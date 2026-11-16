import Nock.NockVMROM.Thm54.OptimizedComputeBaseGates

/-!
# Typed lowering for the normalized 13-base / 58-extension compute row

Source decoder expressions use mixed physical indices `0..70`.  This module lowers them into an
AST that distinguishes thirteen base-field roles from fifty-eight extension-field roles before
coordinate compilation.  Consequently no base role is ever interpreted as an extension-column ID,
and no extension role is passed to `ChipTemplate.col0` with its old physical offset.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeTypedLowering

open Nock
open Nock.Reified
open Module
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open OptimizedComputeGateBasis

noncomputable section

inductive TypedExpr where
  | baseCur : Fin 13 → TypedExpr
  | baseNext : Fin 13 → TypedExpr
  | extCur : Fin 58 → TypedExpr
  | extNext : Fin 58 → TypedExpr
  | challenge : ℕ → TypedExpr
  | publicVal : ℕ → TypedExpr
  | const : ℤ → TypedExpr
  | add : TypedExpr → TypedExpr → TypedExpr
  | sub : TypedExpr → TypedExpr → TypedExpr
  | mul : TypedExpr → TypedExpr → TypedExpr
  | neg : TypedExpr → TypedExpr
  | pow : TypedExpr → ℕ → TypedExpr
deriving DecidableEq

/-- Typed lowering of one normalized mixed-layout expression. -/
def lower : Expr → Option TypedExpr
  | .Var .traceCur i =>
      if h : i < 13 then some (.baseCur ⟨i, h⟩)
      else if h : i < 71 then some (.extCur ⟨i - 13, by omega⟩)
      else none
  | .Var .traceNext i =>
      if h : i < 13 then some (.baseNext ⟨i, h⟩)
      else if h : i < 71 then some (.extNext ⟨i - 13, by omega⟩)
      else none
  | .Var .challenge i => some (.challenge i)
  | .Var .publicVal i => some (.publicVal i)
  | .Const c => some (.const c)
  | .Add x y => return .add (← lower x) (← lower y)
  | .Sub x y => return .sub (← lower x) (← lower y)
  | .Mul x y => return .mul (← lower x) (← lower y)
  | .Neg x => return .neg (← lower x)
  | .Pow x n => return .pow (← lower x) n

/-- Total wrapper used only after a separate `lower = some` proof. -/
def lowerTotal (e : Expr) : TypedExpr :=
  (lower e).getD (.const 0)

structure TypedEnv (F K : Type*) where
  baseTrace : Fin 13 → F
  baseTraceNext : Fin 13 → F
  extTrace : Fin 58 → K
  extTraceNext : Fin 58 → K
  chal : ℕ → K
  pub : ℕ → K

def TypedExpr.eval {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : TypedEnv F K) : TypedExpr → K
  | .baseCur i => algebraMap F K (env.baseTrace i)
  | .baseNext i => algebraMap F K (env.baseTraceNext i)
  | .extCur i => env.extTrace i
  | .extNext i => env.extTraceNext i
  | .challenge i => env.chal i
  | .publicVal i => env.pub i
  | .const c => c
  | .add x y => x.eval env + y.eval env
  | .sub x y => x.eval env - y.eval env
  | .mul x y => x.eval env * y.eval env
  | .neg x => -x.eval env
  | .pow x n => (x.eval env) ^ n

def TypedExpr.degree : TypedExpr → ℕ
  | .baseCur _ | .baseNext _ | .extCur _ | .extNext _ => 1
  | .challenge _ | .publicVal _ | .const _ => 0
  | .add x y | .sub x y => max x.degree y.degree
  | .mul x y => x.degree + y.degree
  | .neg x => x.degree
  | .pow x n => n * x.degree

/-- Range contract for all non-trace typed roles used by the optimized compute template. -/
def TypedSupportFits : TypedExpr → Prop
  | .baseCur _ | .baseNext _ | .extCur _ | .extNext _ | .const _ => True
  | .challenge i => i < 12
  | .publicVal i => i < 42
  | .add x y | .sub x y | .mul x y => TypedSupportFits x ∧ TypedSupportFits y
  | .neg x | .pow x _ => TypedSupportFits x

instance typedSupportFitsDecidable (t : TypedExpr) : Decidable (TypedSupportFits t) := by
  induction t <;> simp only [TypedSupportFits] <;> infer_instance

/-- Reconstitute the old mixed physical environment only for source-semantics comparison. -/
def TypedEnv.toMixedEnv {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : TypedEnv F K) : Env K where
  trace i :=
    if h : i < 13 then algebraMap F K (env.baseTrace ⟨i, h⟩)
    else if h : i < 71 then env.extTrace ⟨i - 13, by omega⟩
    else 0
  traceNext i :=
    if h : i < 13 then algebraMap F K (env.baseTraceNext ⟨i, h⟩)
    else if h : i < 71 then env.extTraceNext ⟨i - 13, by omega⟩
    else 0
  chal := env.chal
  pub := env.pub

theorem lower_eval {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : TypedEnv F K) (e : Expr) (te : TypedExpr)
    (h : lower e = some te) :
    e.eval env.toMixedEnv = te.eval env := by
  induction e generalizing te with
  | Var kind i =>
      cases kind
      · by_cases h13 : i < 13
        · simp [lower, h13] at h
          subst te
          simp [Expr.eval, TypedEnv.toMixedEnv, TypedExpr.eval, h13]
        · by_cases h71 : i < 71
          · simp [lower, h13, h71] at h
            subst te
            simp [Expr.eval, TypedEnv.toMixedEnv, TypedExpr.eval, h13, h71]
          · simp [lower, h13, h71] at h
      · by_cases h13 : i < 13
        · simp [lower, h13] at h
          subst te
          simp [Expr.eval, TypedEnv.toMixedEnv, TypedExpr.eval, h13]
        · by_cases h71 : i < 71
          · simp [lower, h13, h71] at h
            subst te
            simp [Expr.eval, TypedEnv.toMixedEnv, TypedExpr.eval, h13, h71]
          · simp [lower, h13, h71] at h
      · simp [lower] at h
        subst te
        simp [Expr.eval, TypedEnv.toMixedEnv, TypedExpr.eval]
      · simp [lower] at h
        subst te
        simp [Expr.eval, TypedEnv.toMixedEnv, TypedExpr.eval]
  | Const c => simp only [lower, Option.some.injEq] at h; subst te; simp [Expr.eval, TypedExpr.eval]
  | Add x y ihx ihy =>
      cases hx : lower x with
      | none => simp [lower, hx] at h
      | some tx =>
        cases hy : lower y with
        | none => simp [lower, hx, hy] at h
        | some ty =>
          simp [lower, hx, hy] at h
          subst te
          simp [Expr.eval, TypedExpr.eval, ihx tx hx, ihy ty hy]
  | Sub x y ihx ihy =>
      cases hx : lower x with
      | none => simp [lower, hx] at h
      | some tx =>
        cases hy : lower y with
        | none => simp [lower, hx, hy] at h
        | some ty =>
          simp [lower, hx, hy] at h
          subst te
          simp [Expr.eval, TypedExpr.eval, ihx tx hx, ihy ty hy]
  | Mul x y ihx ihy =>
      cases hx : lower x with
      | none => simp [lower, hx] at h
      | some tx =>
        cases hy : lower y with
        | none => simp [lower, hx, hy] at h
        | some ty =>
          simp [lower, hx, hy] at h
          subst te
          simp [Expr.eval, TypedExpr.eval, ihx tx hx, ihy ty hy]
  | Neg x ih =>
      cases hx : lower x with
      | none => simp [lower, hx] at h
      | some tx =>
        simp [lower, hx] at h
        subst te
        simp [Expr.eval, TypedExpr.eval, ih tx hx]
  | Pow x n ih =>
      cases hx : lower x with
      | none => simp [lower, hx] at h
      | some tx =>
        simp [lower, hx] at h
        subst te
        simp [Expr.eval, TypedExpr.eval, ih tx hx]

/-- Physical scalar index used by one typed extension role after coordinate expansion. -/
def extCoordIndex (e : ℕ) (i : Fin 58) (k : Fin e) : ℕ :=
  13 + e * (i : ℕ) + (k : ℕ)

/-- Coordinate compiler for the typed mixed AST. -/
def typedCompile {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) : TypedExpr → Fin e → CoeffExpr F
  | .baseCur i => fun k =>
      .mul (.var .traceCur i) (.const (coord b (1 : K) k))
  | .baseNext i => fun k =>
      .mul (.var .traceNext i) (.const (coord b (1 : K) k))
  | .extCur i => fun k => .var .traceCur (extCoordIndex e i k)
  | .extNext i => fun k => .var .traceNext (extCoordIndex e i k)
  | .challenge i => fun k => .var .challenge (e * i + (k : ℕ))
  | .publicVal i => fun k => .var .publicVal (e * i + (k : ℕ))
  | .const c => fun k => .const ((c : F) * coord b (1 : K) k)
  | .add x y => fun k => .add (typedCompile b x k) (typedCompile b y k)
  | .sub x y => fun k => .sub (typedCompile b x k) (typedCompile b y k)
  | .neg x => fun k => .neg (typedCompile b x k)
  | .mul x y => mulVec b (typedCompile b x) (typedCompile b y)
  | .pow x n => powVec b (typedCompile b x) n

def TypedEnv.toCoeffEnv {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (env : TypedEnv F K) : Env F where
  trace j :=
    if h : j < 13 then env.baseTrace ⟨j, h⟩
    else
      let q := (j - 13) / e
      let r := (j - 13) % e
      if he : 0 < e then
        if hq : q < 58 then coord b (env.extTrace ⟨q, hq⟩) ⟨r, Nat.mod_lt _ he⟩ else 0
      else 0
  traceNext j :=
    if h : j < 13 then env.baseTraceNext ⟨j, h⟩
    else
      let q := (j - 13) / e
      let r := (j - 13) % e
      if he : 0 < e then
        if hq : q < 58 then coord b (env.extTraceNext ⟨q, hq⟩) ⟨r, Nat.mod_lt _ he⟩ else 0
      else 0
  chal j :=
    if he : 0 < e then coord b (env.chal (j / e)) ⟨j % e, Nat.mod_lt _ he⟩ else 0
  pub j :=
    if he : 0 < e then coord b (env.pub (j / e)) ⟨j % e, Nat.mod_lt _ he⟩ else 0

theorem extCoordIndex_lt {e : ℕ} (he : 0 < e) (i : Fin 58) (k : Fin e) :
    extCoordIndex e i k < 13 + 58 * e := by
  simp only [extCoordIndex]
  have hk : e * (i : ℕ) + (k : ℕ) < e * (i : ℕ) + e :=
    Nat.add_lt_add_left k.isLt _
  have hi : e * ((i : ℕ) + 1) ≤ e * 58 :=
    Nat.mul_le_mul_left e (Nat.succ_le_iff.mpr i.isLt)
  calc
    13 + e * (i : ℕ) + (k : ℕ) < 13 + (e * (i : ℕ) + e) := by omega
    _ = 13 + e * ((i : ℕ) + 1) := by ring
    _ ≤ 13 + e * 58 := Nat.add_le_add_left hi 13
    _ = 13 + 58 * e := by ring

theorem toCoeffEnv_trace_ext {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (he : 0 < e) (b : Basis (Fin e) F K) (env : TypedEnv F K)
    (i : Fin 58) (k : Fin e) :
    (env.toCoeffEnv b).trace (extCoordIndex e i k) = coord b (env.extTrace i) k := by
  change (if h : extCoordIndex e i k < 13 then env.baseTrace ⟨_, h⟩ else _) = _
  rw [dif_neg (by simp [extCoordIndex]; omega)]
  rw [dif_pos he]
  letI : NeZero e := ⟨Nat.ne_of_gt he⟩
  have hsub : extCoordIndex e i k - 13 = e * (i : ℕ) + (k : ℕ) := by
    simpa [extCoordIndex, Nat.add_assoc] using
      (Nat.add_sub_cancel_left 13 (e * (i : ℕ) + (k : ℕ)))
  obtain ⟨hdiv0, hmod0⟩ := std_index (e := e) (i : ℕ) k
  have hdiv : (extCoordIndex e i k - 13) / e = (i : ℕ) := by simpa [hsub] using hdiv0
  have hmod : (extCoordIndex e i k - 13) % e = (k : ℕ) := by simpa [hsub] using hmod0
  split
  · congr 2
    · exact Fin.ext hdiv
  · rename_i hq
    exact False.elim (hq (hdiv ▸ i.isLt))

theorem toCoeffEnv_traceNext_ext {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (he : 0 < e) (b : Basis (Fin e) F K) (env : TypedEnv F K)
    (i : Fin 58) (k : Fin e) :
    (env.toCoeffEnv b).traceNext (extCoordIndex e i k) =
      coord b (env.extTraceNext i) k := by
  change (if h : extCoordIndex e i k < 13 then env.baseTraceNext ⟨_, h⟩ else _) = _
  rw [dif_neg (by simp [extCoordIndex]; omega)]
  rw [dif_pos he]
  letI : NeZero e := ⟨Nat.ne_of_gt he⟩
  have hsub : extCoordIndex e i k - 13 = e * (i : ℕ) + (k : ℕ) := by
    simpa [extCoordIndex, Nat.add_assoc] using
      (Nat.add_sub_cancel_left 13 (e * (i : ℕ) + (k : ℕ)))
  obtain ⟨hdiv0, hmod0⟩ := std_index (e := e) (i : ℕ) k
  have hdiv : (extCoordIndex e i k - 13) / e = (i : ℕ) := by simpa [hsub] using hdiv0
  have hmod : (extCoordIndex e i k - 13) % e = (k : ℕ) := by simpa [hsub] using hmod0
  split
  · congr 2
    · exact Fin.ext hdiv
  · rename_i hq
    exact False.elim (hq (hdiv ▸ i.isLt))

theorem toCoeffEnv_chal {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (he : 0 < e) (b : Basis (Fin e) F K) (env : TypedEnv F K)
    (i : ℕ) (k : Fin e) :
    (env.toCoeffEnv b).chal (e * i + (k : ℕ)) = coord b (env.chal i) k := by
  simp [TypedEnv.toCoeffEnv, he, Nat.mul_add_div he, Nat.mul_add_mod,
    Nat.div_eq_of_lt k.isLt, Nat.mod_eq_of_lt k.isLt]

theorem toCoeffEnv_pub {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (he : 0 < e) (b : Basis (Fin e) F K) (env : TypedEnv F K)
    (i : ℕ) (k : Fin e) :
    (env.toCoeffEnv b).pub (e * i + (k : ℕ)) = coord b (env.pub i) k := by
  simp [TypedEnv.toCoeffEnv, he, Nat.mul_add_div he, Nat.mul_add_mod,
    Nat.div_eq_of_lt k.isLt, Nat.mod_eq_of_lt k.isLt]

theorem typedCompile_eval {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] {e : ℕ} (he : 0 < e) (b : Basis (Fin e) F K)
    (env : TypedEnv F K) (t : TypedExpr) (k : Fin e) :
    coord b (t.eval env) k = (typedCompile b t k).eval (env.toCoeffEnv b) := by
  induction t generalizing k with
  | baseCur i =>
      simp only [TypedExpr.eval, typedCompile, CoeffExpr.eval]
      rw [show algebraMap F K (env.baseTrace i) = env.baseTrace i • (1 : K) by
        simp [Algebra.smul_def]]
      rw [coord_smul]
      simp [TypedEnv.toCoeffEnv, i.isLt]
  | baseNext i =>
      simp only [TypedExpr.eval, typedCompile, CoeffExpr.eval]
      rw [show algebraMap F K (env.baseTraceNext i) = env.baseTraceNext i • (1 : K) by
        simp [Algebra.smul_def]]
      rw [coord_smul]
      simp [TypedEnv.toCoeffEnv, i.isLt]
  | extCur i =>
      simp only [TypedExpr.eval, typedCompile, CoeffExpr.eval]
      exact (toCoeffEnv_trace_ext he b env i k).symm
  | extNext i =>
      simp only [TypedExpr.eval, typedCompile, CoeffExpr.eval]
      exact (toCoeffEnv_traceNext_ext he b env i k).symm
  | challenge i =>
      simpa [TypedExpr.eval, typedCompile, CoeffExpr.eval] using
        (toCoeffEnv_chal he b env i k).symm
  | publicVal i =>
      simpa [TypedExpr.eval, typedCompile, CoeffExpr.eval] using
        (toCoeffEnv_pub he b env i k).symm
  | const c => exact coord_intCast b c k
  | add x y ihx ihy =>
      simp only [TypedExpr.eval, typedCompile, CoeffExpr.eval, coord_add, ihx, ihy]
  | sub x y ihx ihy =>
      simp only [TypedExpr.eval, typedCompile, CoeffExpr.eval, coord_sub, ihx, ihy]
  | neg x ih => simp only [TypedExpr.eval, typedCompile, CoeffExpr.eval, coord_neg, ih]
  | mul x y ihx ihy =>
      exact eval_mulVec b _ _ _ (x.eval env) (y.eval env) ihx ihy k
  | pow x n ih => exact eval_powVec b _ _ (x.eval env) ih n k

theorem typedCompile_degree_le {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (t : TypedExpr) (k : Fin e) :
    (typedCompile b t k).degree ≤ t.degree := by
  induction t generalizing k with
  | baseCur i => simp [typedCompile, TypedExpr.degree, CoeffExpr.degree]
  | baseNext i => simp [typedCompile, TypedExpr.degree, CoeffExpr.degree]
  | extCur i => simp [typedCompile, TypedExpr.degree, CoeffExpr.degree]
  | extNext i => simp [typedCompile, TypedExpr.degree, CoeffExpr.degree]
  | challenge i => simp [typedCompile, TypedExpr.degree, CoeffExpr.degree]
  | publicVal i => simp [typedCompile, TypedExpr.degree, CoeffExpr.degree]
  | const c => simp [typedCompile, TypedExpr.degree, CoeffExpr.degree]
  | add x y ihx ihy =>
      simp only [typedCompile, TypedExpr.degree, CoeffExpr.degree]
      exact max_le_max (ihx k) (ihy k)
  | sub x y ihx ihy =>
      simp only [typedCompile, TypedExpr.degree, CoeffExpr.degree]
      exact max_le_max (ihx k) (ihy k)
  | neg x ih => simpa [typedCompile, TypedExpr.degree, CoeffExpr.degree] using ih k
  | mul x y ihx ihy =>
      exact degree_mulVec_le b _ _ x.degree y.degree ihx ihy k
  | pow x n ih => exact degree_powVec_le b _ x.degree ih n k

/-- Every lowered transition gate has only typed `Fin 13` base and `Fin 58` extension roles. -/
def loweredExtTransitionGates : List TypedExpr :=
  extTransitionGates.filterMap lower

@[simp] theorem loweredExtTransitionGates_length :
    loweredExtTransitionGates.length = 21 := by
  set_option maxRecDepth 100000 in
  decide

/-- No transition gate is dropped by typed lowering. -/
theorem lowering_preserves_gate_count :
    loweredExtTransitionGates.length = extTransitionGates.length := by
  rw [loweredExtTransitionGates_length, extTransitionGates_length]

theorem filterMap_length_le {α β : Type*} (f : α → Option β) (xs : List α) :
    (xs.filterMap f).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      cases ha : f a with
      | none =>
          simpa [List.filterMap, ha] using ih.trans (Nat.le_succ _)
      | some b =>
          simpa [List.filterMap, ha] using Nat.succ_le_succ ih

theorem filterMap_supported {α β : Type*} (f : α → Option β) (xs : List α)
    (hlen : (xs.filterMap f).length = xs.length) :
    ∀ x ∈ xs, ∃ y, f x = some y := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      cases ha : f a with
      | none =>
          simp [List.filterMap, ha] at hlen
          have hle := filterMap_length_le f xs
          omega
      | some b =>
          simp only [List.filterMap, ha, Option.toList_some, List.cons_append,
            List.length_cons, add_left_inj] at hlen
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact ⟨b, ha⟩
          · exact ih hlen x hx

theorem extTransitionGates_supported :
    ∀ g ∈ extTransitionGates, ∃ t, lower g = some t :=
  filterMap_supported lower extTransitionGates lowering_preserves_gate_count

theorem filterMap_eval_iff
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : TypedEnv F K) (xs : List Expr)
    (hlen : (xs.filterMap lower).length = xs.length) :
    (∀ t ∈ xs.filterMap lower, t.eval env = 0) ↔
      ∀ g ∈ xs, g.eval env.toMixedEnv = 0 := by
  constructor
  · intro ht g hg
    obtain ⟨t, hlow⟩ := filterMap_supported lower xs hlen g hg
    rw [lower_eval env g t hlow]
    exact ht t (List.mem_filterMap.mpr ⟨g, hg, hlow⟩)
  · intro hg t ht
    obtain ⟨g, hgin, hlow⟩ := List.mem_filterMap.mp ht
    rw [← lower_eval env g t hlow]
    exact hg g hgin

theorem loweredExtTransitionGates_eval_iff
    {F K : Type*} [Field F] [Field K] [Algebra F K] (env : TypedEnv F K) :
    (∀ t ∈ loweredExtTransitionGates, t.eval env = 0) ↔
      ∀ g ∈ extTransitionGates, g.eval env.toMixedEnv = 0 := by
  exact filterMap_eval_iff env extTransitionGates lowering_preserves_gate_count

theorem loweredExtTransitionGates_degree :
    ∀ t ∈ loweredExtTransitionGates, t.degree ≤ 4 := by
  set_option maxRecDepth 100000 in
  decide

theorem loweredExtTransitionGates_support :
    ∀ t ∈ loweredExtTransitionGates, TypedSupportFits t := by
  set_option maxRecDepth 100000 in
  decide

theorem lowerTotal_eq_of_supported (g : Expr) (t : TypedExpr) (h : lower g = some t) :
    lowerTotal g = t := by
  simp [lowerTotal, h]

#print axioms lower_eval
#print axioms extCoordIndex_lt
#print axioms typedCompile_eval
#print axioms typedCompile_degree_le
#print axioms lowering_preserves_gate_count
#print axioms loweredExtTransitionGates_eval_iff

end
end OptimizedComputeTypedLowering
end Nock.NockVMROM.Thm54
