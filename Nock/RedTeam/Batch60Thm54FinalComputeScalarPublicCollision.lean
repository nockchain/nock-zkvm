import Nock.RedTeam.Batch59Thm54FinalComputeCompilerTrace
import Nock.NockVMROM.Thm54.OptimizedComputeGateBasisObstruction

/-!
# Scalar-public final compute correction and challenge-9 boundary

The `13/62`, `199/98` optimized compiler remains an author-authorized correctness delta.  This
artifact does not attribute that optimization to the paper.

This file deliberately introduces a separately named corrected AST,
compiler, gate list, and RAP.  Extension-valued public endpoints `0..1` still coordinate-expand.
The fixed selector publics `20..41` instead use a base-scalar constructor and compile from the same
raw public indices consumed by the base equality gates.

Honest source equations imply folds unconditionally; reverse recovery
requires `FinalComputeCollisionFree`.  A concrete production-family cancellation witnesses that
the premise cannot be erased.  The finite-field cardinality bound remains a separate, explicitly
identified root-count assembly obligation.
-/

namespace Nock.RedTeam.Batch60

set_option maxRecDepth 300000
set_option maxHeartbeats 8000000

open Classical
open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open scoped Polynomial
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasisObstruction
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.StrictExtension

noncomputable section

/-! ## 1. Separately named corrected typed surface -/

/-- Corrected final AST.  Public endpoints are extension values, while selector masks are base
scalars indexed relative to raw public slot 20. -/
inductive CorrectedFinalTypedExpr where
  | baseCur : Fin 13 → CorrectedFinalTypedExpr
  | baseNext : Fin 13 → CorrectedFinalTypedExpr
  | extCur : Fin 62 → CorrectedFinalTypedExpr
  | extNext : Fin 62 → CorrectedFinalTypedExpr
  | challenge : Fin 12 → CorrectedFinalTypedExpr
  | extensionPublic : Fin 2 → CorrectedFinalTypedExpr
  | scalarPublic : Fin 22 → CorrectedFinalTypedExpr
  | const : ℤ → CorrectedFinalTypedExpr
  | add : CorrectedFinalTypedExpr → CorrectedFinalTypedExpr → CorrectedFinalTypedExpr
  | sub : CorrectedFinalTypedExpr → CorrectedFinalTypedExpr → CorrectedFinalTypedExpr
  | mul : CorrectedFinalTypedExpr → CorrectedFinalTypedExpr → CorrectedFinalTypedExpr
  | neg : CorrectedFinalTypedExpr → CorrectedFinalTypedExpr
  | pow : CorrectedFinalTypedExpr → ℕ → CorrectedFinalTypedExpr
deriving DecidableEq

/-- Exact corrected lowering.  No public index outside `0..1 ∪ 20..41` is accepted. -/
def correctedLowerFinal : Expr → Option CorrectedFinalTypedExpr
  | .Var .traceCur i =>
      if h : i < 13 then some (.baseCur ⟨i, h⟩)
      else if h : i < 75 then some (.extCur ⟨i - 13, by omega⟩)
      else none
  | .Var .traceNext i =>
      if h : i < 13 then some (.baseNext ⟨i, h⟩)
      else if h : i < 75 then some (.extNext ⟨i - 13, by omega⟩)
      else none
  | .Var .challenge i =>
      if h : i < 12 then some (.challenge ⟨i, h⟩) else none
  | .Var .publicVal i =>
      if h : i < 2 then some (.extensionPublic ⟨i, h⟩)
      else if h : 20 ≤ i ∧ i < 42 then some (.scalarPublic ⟨i - 20, by omega⟩)
      else none
  | .Const c => some (.const c)
  | .Add x y => return .add (← correctedLowerFinal x) (← correctedLowerFinal y)
  | .Sub x y => return .sub (← correctedLowerFinal x) (← correctedLowerFinal y)
  | .Mul x y => return .mul (← correctedLowerFinal x) (← correctedLowerFinal y)
  | .Neg x => return .neg (← correctedLowerFinal x)
  | .Pow x n => return .pow (← correctedLowerFinal x) n

def correctedLowerFinalTotal (e : Expr) : CorrectedFinalTypedExpr :=
  (correctedLowerFinal e).getD (.const 0)

structure CorrectedFinalTypedEnv (F K : Type*) where
  baseTrace : Fin 13 → F
  baseTraceNext : Fin 13 → F
  extTrace : Fin 62 → K
  extTraceNext : Fin 62 → K
  chal : Fin 12 → K
  extensionPublic : Fin 2 → K
  scalarPublic : Fin 22 → F

def CorrectedFinalTypedExpr.eval {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) : CorrectedFinalTypedExpr → K
  | .baseCur i => algebraMap F K (env.baseTrace i)
  | .baseNext i => algebraMap F K (env.baseTraceNext i)
  | .extCur i => env.extTrace i
  | .extNext i => env.extTraceNext i
  | .challenge i => env.chal i
  | .extensionPublic i => env.extensionPublic i
  | .scalarPublic i => algebraMap F K (env.scalarPublic i)
  | .const c => c
  | .add x y => x.eval env + y.eval env
  | .sub x y => x.eval env - y.eval env
  | .mul x y => x.eval env * y.eval env
  | .neg x => -x.eval env
  | .pow x n => (x.eval env) ^ n

def CorrectedFinalTypedExpr.degree : CorrectedFinalTypedExpr → ℕ
  | .baseCur _ | .baseNext _ | .extCur _ | .extNext _ => 1
  | .challenge _ | .extensionPublic _ | .scalarPublic _ | .const _ => 0
  | .add x y | .sub x y => max x.degree y.degree
  | .mul x y => x.degree + y.degree
  | .neg x => x.degree
  | .pow x n => n * x.degree

def CorrectedFinalTypedEnv.toSourceEnv {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) : Env K where
  trace i :=
    if h : i < 13 then algebraMap F K (env.baseTrace ⟨i, h⟩)
    else if h : i < 75 then env.extTrace ⟨i - 13, by omega⟩
    else 0
  traceNext i :=
    if h : i < 13 then algebraMap F K (env.baseTraceNext ⟨i, h⟩)
    else if h : i < 75 then env.extTraceNext ⟨i - 13, by omega⟩
    else 0
  chal i := if h : i < 12 then env.chal ⟨i, h⟩ else 0
  pub i :=
    if h : i < 2 then env.extensionPublic ⟨i, h⟩
    else if h : 20 ≤ i ∧ i < 42 then algebraMap F K (env.scalarPublic ⟨i - 20, by omega⟩)
    else 0

/-- Source evaluation is preserved by the corrected, typed lowering. -/
theorem correctedLowerFinal_eval {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) (e : Expr) (t : CorrectedFinalTypedExpr)
    (h : correctedLowerFinal e = some t) :
    e.eval env.toSourceEnv = t.eval env := by
  induction e generalizing t with
  | Var kind i =>
      cases kind
      · by_cases h13 : i < 13
        · simp [correctedLowerFinal, h13] at h
          subst t
          simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, CorrectedFinalTypedExpr.eval, h13]
        · by_cases h75 : i < 75
          · simp [correctedLowerFinal, h13, h75] at h
            subst t
            simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, CorrectedFinalTypedExpr.eval,
              h13, h75]
          · simp [correctedLowerFinal, h13, h75] at h
      · by_cases h13 : i < 13
        · simp [correctedLowerFinal, h13] at h
          subst t
          simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, CorrectedFinalTypedExpr.eval, h13]
        · by_cases h75 : i < 75
          · simp [correctedLowerFinal, h13, h75] at h
            subst t
            simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, CorrectedFinalTypedExpr.eval,
              h13, h75]
          · simp [correctedLowerFinal, h13, h75] at h
      · by_cases h12 : i < 12
        · simp [correctedLowerFinal, h12] at h
          subst t
          simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, CorrectedFinalTypedExpr.eval, h12]
        · simp [correctedLowerFinal, h12] at h
      · by_cases h2 : i < 2
        · simp [correctedLowerFinal, h2] at h
          subst t
          have hle : i ≤ 1 := by omega
          simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, CorrectedFinalTypedExpr.eval, hle]
        · by_cases hs : 20 ≤ i ∧ i < 42
          · simp [correctedLowerFinal, h2, hs] at h
            subst t
            have hnle : ¬ i ≤ 1 := by omega
            simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, CorrectedFinalTypedExpr.eval,
              hnle, hs]
          · simp [correctedLowerFinal, h2, hs] at h
  | Const c =>
      simp only [correctedLowerFinal, Option.some.injEq] at h
      subst t
      simp [Expr.eval, CorrectedFinalTypedExpr.eval]
  | Add x y ihx ihy =>
      cases hx : correctedLowerFinal x with
      | none => simp [correctedLowerFinal, hx] at h
      | some tx =>
        cases hy : correctedLowerFinal y with
        | none => simp [correctedLowerFinal, hx, hy] at h
        | some ty =>
          simp [correctedLowerFinal, hx, hy] at h
          subst t
          simp [Expr.eval, CorrectedFinalTypedExpr.eval, ihx tx hx, ihy ty hy]
  | Sub x y ihx ihy =>
      cases hx : correctedLowerFinal x with
      | none => simp [correctedLowerFinal, hx] at h
      | some tx =>
        cases hy : correctedLowerFinal y with
        | none => simp [correctedLowerFinal, hx, hy] at h
        | some ty =>
          simp [correctedLowerFinal, hx, hy] at h
          subst t
          simp [Expr.eval, CorrectedFinalTypedExpr.eval, ihx tx hx, ihy ty hy]
  | Mul x y ihx ihy =>
      cases hx : correctedLowerFinal x with
      | none => simp [correctedLowerFinal, hx] at h
      | some tx =>
        cases hy : correctedLowerFinal y with
        | none => simp [correctedLowerFinal, hx, hy] at h
        | some ty =>
          simp [correctedLowerFinal, hx, hy] at h
          subst t
          simp [Expr.eval, CorrectedFinalTypedExpr.eval, ihx tx hx, ihy ty hy]
  | Neg x ih =>
      cases hx : correctedLowerFinal x with
      | none => simp [correctedLowerFinal, hx] at h
      | some tx =>
        simp [correctedLowerFinal, hx] at h
        subst t
        simp [Expr.eval, CorrectedFinalTypedExpr.eval, ih tx hx]
  | Pow x n ih =>
      cases hx : correctedLowerFinal x with
      | none => simp [correctedLowerFinal, hx] at h
      | some tx =>
        simp [correctedLowerFinal, hx] at h
        subst t
        simp [Expr.eval, CorrectedFinalTypedExpr.eval, ih tx hx]

def correctedFinalExtCoordIndex {e : ℕ} (i : Fin 62) (k : Fin e) : ℕ :=
  13 + e * (i : ℕ) + (k : ℕ)

/-- Coordinate compiler for the corrected final AST.  The scalar-public branch reads raw
`20+i` and embeds that base scalar into `K`; it never strides to `3*(20+i)+k`. -/
def correctedFinalTypedCompile {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) : CorrectedFinalTypedExpr → Fin e → CoeffExpr F
  | .baseCur i => fun k =>
      .mul (.var .traceCur i) (.const (coord b (1 : K) k))
  | .baseNext i => fun k =>
      .mul (.var .traceNext i) (.const (coord b (1 : K) k))
  | .extCur i => fun k => .var .traceCur (correctedFinalExtCoordIndex i k)
  | .extNext i => fun k => .var .traceNext (correctedFinalExtCoordIndex i k)
  | .challenge i => fun k => .var .challenge (e * (i : ℕ) + (k : ℕ))
  | .extensionPublic i => fun k => .var .publicVal (e * (i : ℕ) + (k : ℕ))
  | .scalarPublic i => fun k =>
      .mul (.var .publicVal (20 + (i : ℕ))) (.const (coord b (1 : K) k))
  | .const c => fun k => .const ((c : F) * coord b (1 : K) k)
  | .add x y => fun k =>
      .add (correctedFinalTypedCompile b x k) (correctedFinalTypedCompile b y k)
  | .sub x y => fun k =>
      .sub (correctedFinalTypedCompile b x k) (correctedFinalTypedCompile b y k)
  | .neg x => fun k => .neg (correctedFinalTypedCompile b x k)
  | .mul x y =>
      mulVec b (correctedFinalTypedCompile b x) (correctedFinalTypedCompile b y)
  | .pow x n => powVec b (correctedFinalTypedCompile b x) n

/-- Relation between one corrected typed environment and its physical base-field environment. -/
structure IsCorrectedFinalCoordEnv {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K)
    (env : CorrectedFinalTypedEnv F K) (envF : Env F) : Prop where
  baseTrace : ∀ i : Fin 13, envF.trace i = env.baseTrace i
  baseTraceNext : ∀ i : Fin 13, envF.traceNext i = env.baseTraceNext i
  extTrace : ∀ (i : Fin 62) (k : Fin e),
    envF.trace (correctedFinalExtCoordIndex i k) = coord b (env.extTrace i) k
  extTraceNext : ∀ (i : Fin 62) (k : Fin e),
    envF.traceNext (correctedFinalExtCoordIndex i k) = coord b (env.extTraceNext i) k
  chal : ∀ (i : Fin 12) (k : Fin e),
    envF.chal (e * (i : ℕ) + (k : ℕ)) = coord b (env.chal i) k
  extensionPublic : ∀ (i : Fin 2) (k : Fin e),
    envF.pub (e * (i : ℕ) + (k : ℕ)) = coord b (env.extensionPublic i) k
  scalarPublic : ∀ i : Fin 22, envF.pub (20 + (i : ℕ)) = env.scalarPublic i

/-- Evaluation correctness of the corrected compiler. -/
theorem correctedFinalTypedCompile_eval
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {e : ℕ} (b : Basis (Fin e) F K)
    (env : CorrectedFinalTypedEnv F K) (envF : Env F)
    (henv : IsCorrectedFinalCoordEnv b env envF)
    (t : CorrectedFinalTypedExpr) (k : Fin e) :
    coord b (t.eval env) k = (correctedFinalTypedCompile b t k).eval envF := by
  induction t generalizing k with
  | baseCur i =>
      simp only [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval]
      rw [show algebraMap F K (env.baseTrace i) = env.baseTrace i • (1 : K) by
        simp [Algebra.smul_def], coord_smul, henv.baseTrace]
      simp [smul_eq_mul]
  | baseNext i =>
      simp only [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval]
      rw [show algebraMap F K (env.baseTraceNext i) = env.baseTraceNext i • (1 : K) by
        simp [Algebra.smul_def], coord_smul, henv.baseTraceNext]
      simp [smul_eq_mul]
  | extCur i =>
      simpa [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval] using
        (henv.extTrace i k).symm
  | extNext i =>
      simpa [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval] using
        (henv.extTraceNext i k).symm
  | challenge i =>
      simpa [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval] using
        (henv.chal i k).symm
  | extensionPublic i =>
      simpa [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval] using
        (henv.extensionPublic i k).symm
  | scalarPublic i =>
      simp only [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval]
      rw [show algebraMap F K (env.scalarPublic i) = env.scalarPublic i • (1 : K) by
        simp [Algebra.smul_def], coord_smul, henv.scalarPublic]
      simp [smul_eq_mul]
  | const c => exact coord_intCast b c k
  | add x y ihx ihy =>
      simp only [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval,
        coord_add, ihx, ihy]
  | sub x y ihx ihy =>
      simp only [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval,
        coord_sub, ihx, ihy]
  | neg x ih =>
      simp only [CorrectedFinalTypedExpr.eval, correctedFinalTypedCompile, CoeffExpr.eval,
        coord_neg, ih]
  | mul x y ihx ihy =>
      exact eval_mulVec b envF _ _ (x.eval env) (y.eval env) ihx ihy k
  | pow x n ih =>
      exact eval_powVec b envF _ (x.eval env) ih n k

theorem correctedFinalTypedCompile_reconstruct
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {e : ℕ} (b : Basis (Fin e) F K)
    (env : CorrectedFinalTypedEnv F K) (envF : Env F)
    (henv : IsCorrectedFinalCoordEnv b env envF)
    (t : CorrectedFinalTypedExpr) :
    reconstruct b (fun k => (correctedFinalTypedCompile b t k).eval envF) = t.eval env := by
  rw [← reconstruct_coord b (t.eval env)]
  congr
  funext k
  exact (correctedFinalTypedCompile_eval b env envF henv t k).symm

theorem correctedFinalTypedCompile_degree_le
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (t : CorrectedFinalTypedExpr) (k : Fin e) :
    (correctedFinalTypedCompile b t k).degree ≤ t.degree := by
  induction t generalizing k with
  | baseCur i => simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | baseNext i => simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | extCur i => simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | extNext i => simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | challenge i => simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | extensionPublic i =>
      simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | scalarPublic i =>
      simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | const c => simp [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
  | add x y ihx ihy =>
      simp only [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
      exact max_le_max (ihx k) (ihy k)
  | sub x y ihx ihy =>
      simp only [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree]
      exact max_le_max (ihx k) (ihy k)
  | neg x ih =>
      simpa [correctedFinalTypedCompile, CorrectedFinalTypedExpr.degree, CoeffExpr.degree] using ih k
  | mul x y ihx ihy =>
      exact degree_mulVec_le b _ _ x.degree y.degree ihx ihy k
  | pow x n ih =>
      exact degree_powVec_le b _ x.degree ih n k

/-- Physical support of the corrected cubic compiler. -/
def CorrectedCoeffSupportFits199 {F : Type*} : CoeffExpr F → Prop
  | .const _ => True
  | .var .traceCur i | .var .traceNext i => i < 199
  | .var .challenge i => i < 36
  | .var .publicVal i => i < 6 ∨ (20 ≤ i ∧ i < 42)
  | .add x y | .sub x y | .mul x y =>
      CorrectedCoeffSupportFits199 x ∧ CorrectedCoeffSupportFits199 y
  | .neg x | .pow x _ => CorrectedCoeffSupportFits199 x

theorem corrected_sum_support {F : Type*} [Field F] {ι : Type*}
    (xs : List ι) (f : ι → CoeffExpr F)
    (h : ∀ i ∈ xs, CorrectedCoeffSupportFits199 (f i)) :
    CorrectedCoeffSupportFits199 (CoeffExpr.sumList xs f) := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
      exact ⟨h a (by simp), ih (fun i hi => h i (by simp [hi]))⟩

theorem corrected_mulVec_support
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (u v : Fin 3 → CoeffExpr F)
    (hu : ∀ i, CorrectedCoeffSupportFits199 (u i))
    (hv : ∀ i, CorrectedCoeffSupportFits199 (v i)) :
    ∀ k, CorrectedCoeffSupportFits199 (mulVec b u v k) := by
  intro k
  apply corrected_sum_support
  intro i hi
  apply corrected_sum_support
  intro j hj
  exact ⟨⟨hu i, hv j⟩, trivial⟩

theorem corrected_powVec_support
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (u : Fin 3 → CoeffExpr F)
    (hu : ∀ i, CorrectedCoeffSupportFits199 (u i)) :
    ∀ n k, CorrectedCoeffSupportFits199 (powVec b u n k) := by
  intro n
  induction n with
  | zero => intro k; trivial
  | succ n ih => exact corrected_mulVec_support b (powVec b u n) u ih hu

theorem correctedFinalTypedCompile_support
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (t : CorrectedFinalTypedExpr) (k : Fin 3) :
    CorrectedCoeffSupportFits199 (correctedFinalTypedCompile b t k) := by
  induction t generalizing k with
  | baseCur i =>
      simp [correctedFinalTypedCompile, CorrectedCoeffSupportFits199]
      omega
  | baseNext i =>
      simp [correctedFinalTypedCompile, CorrectedCoeffSupportFits199]
      omega
  | extCur i =>
      simp [correctedFinalTypedCompile, correctedFinalExtCoordIndex, CorrectedCoeffSupportFits199]
      omega
  | extNext i =>
      simp [correctedFinalTypedCompile, correctedFinalExtCoordIndex, CorrectedCoeffSupportFits199]
      omega
  | challenge i =>
      simp [correctedFinalTypedCompile, CorrectedCoeffSupportFits199]
      omega
  | extensionPublic i =>
      simp [correctedFinalTypedCompile, CorrectedCoeffSupportFits199]
      omega
  | scalarPublic i =>
      simp [correctedFinalTypedCompile, CorrectedCoeffSupportFits199]
      omega
  | const c => simp [correctedFinalTypedCompile, CorrectedCoeffSupportFits199]
  | add x y hx hy => exact ⟨hx k, hy k⟩
  | sub x y hx hy => exact ⟨hx k, hy k⟩
  | mul x y hx hy => exact corrected_mulVec_support b _ _ hx hy k
  | neg x hx => exact hx k
  | pow x n hx => exact corrected_powVec_support b _ hx n k

/-! ## 2. -/

def exprPublicIndices : Expr → List ℕ
  | .Var .publicVal i => [i]
  | .Var _ _ | .Const _ => []
  | .Add x y | .Sub x y | .Mul x y => exprPublicIndices x ++ exprPublicIndices y
  | .Neg x | .Pow x _ => exprPublicIndices x

def coeffPublicIndices {F : Type*} : CoeffExpr F → List ℕ
  | .var .publicVal i => [i]
  | .var _ _ | .const _ => []
  | .add x y | .sub x y | .mul x y => coeffPublicIndices x ++ coeffPublicIndices y
  | .neg x | .pow x _ => coeffPublicIndices x

def finalSourceSurface : List Expr :=
  finalExtTransitionGates ++
    [finalMaskedWalkLn1, finalMaskedWalkCount1, finalMaskedWalkAccInit, finalMaskedWalkOut]

theorem final_source_public_indices_exact :
    (finalSourceSurface.flatMap exprPublicIndices).toFinset =
      ({0, 1} : Finset ℕ) ∪ Finset.Icc 20 41 := by
  set_option maxRecDepth 300000 in
  decide

/-- The two base-field selector equality gates consume exactly the scalar-public block
`20..41`. -/
theorem final_base_selector_public_indices_exact :
    ((finalMaskedEndpointEqualityChecks (F := ZMod 73)).flatMap
      coeffPublicIndices).toFinset = Finset.Icc 20 41 := by
  set_option maxRecDepth 300000 in
  decide

/-- After excluding the two genuine extension-valued endpoint publics, the extension source and
the base selector checks consume the identical complete scalar-public block. -/
theorem corrected_extension_and_base_public_indices_identical :
    (finalSourceSurface.flatMap exprPublicIndices).toFinset \ ({0, 1} : Finset ℕ) =
      ((finalMaskedEndpointEqualityChecks (F := ZMod 73)).flatMap
        coeffPublicIndices).toFinset := by
  rw [final_source_public_indices_exact, final_base_selector_public_indices_exact]
  ext i
  simp
  omega

/-- `walkQueueTiling` still lowers. -/
theorem corrected_source_surface_lowers_without_fallback :
    (finalExtTransitionGates.filterMap correctedLowerFinal).length = 78 := by
  set_option maxRecDepth 300000 in
  decide

/-- Every selector public was wrongly
strided.  Across the whole scalar range it reads raw `60..125`, never the intended `20..41`. -/
theorem historical_scalar_public_replay_rejected
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (i : Fin 22) (k : Fin 3) :
    finalTypedCompile b (.publicVal (20 + (i : ℕ))) k =
        .var .publicVal (60 + 3 * (i : ℕ) + (k : ℕ)) ∧
      60 ≤ 60 + 3 * (i : ℕ) + (k : ℕ) ∧
      60 + 3 * (i : ℕ) + (k : ℕ) ≤ 125 ∧
      60 + 3 * (i : ℕ) + (k : ℕ) ≠ 20 + (i : ℕ) := by
  constructor
  · simp [finalTypedCompile]
    omega
  omega

/-- Corrected scalar publics use the exact raw index consumed by
`finalSelectorPublicCheck`; only the basis embedding coefficient depends on `k`. -/
theorem corrected_scalar_public_same_raw_index
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (i : Fin 22) (k : Fin 3) :
    correctedFinalTypedCompile b (.scalarPublic i) k =
      .mul (.var .publicVal (20 + (i : ℕ))) (.const (coord b (1 : K) k)) := by
  rfl

theorem corrected_initial_terminal_selector_ranges
    (st : Nock.ComputeTable.State) :
    correctedLowerFinal (OptimizedComputeTemplate.initialMask st) =
        some (.scalarPublic ⟨Nock.Reified.opCol st, by
          cases st <;> decide⟩) ∧
      correctedLowerFinal (OptimizedComputeTemplate.terminalMask st) =
        some (.scalarPublic ⟨11 + Nock.Reified.opCol st, by
          cases st <;> decide⟩) := by
  cases st <;>
    norm_num [OptimizedComputeTemplate.initialMask, OptimizedComputeTemplate.terminalMask,
      correctedLowerFinal, Nock.Reified.opCol]

/-! ## 3. Corrected final gate list and separately named RAP -/

def correctedFinalLoweredExtTransitionGates : List CorrectedFinalTypedExpr :=
  finalExtTransitionGates.filterMap correctedLowerFinal

def correctedFinalLoweredMaskedEndpointDeg2 : List CorrectedFinalTypedExpr :=
  [finalMaskedWalkInitFold, finalMaskedWalkOut].filterMap correctedLowerFinal

def correctedFinalLoweredMaskedEndpointDeg4 : List CorrectedFinalTypedExpr :=
  [finalMaskedWalkAccInit].filterMap correctedLowerFinal

theorem corrected_lowered_counts :
    correctedFinalLoweredExtTransitionGates.length = 78 ∧
      correctedFinalLoweredMaskedEndpointDeg2.length = 2 ∧
      correctedFinalLoweredMaskedEndpointDeg4.length = 1 := by
  set_option maxRecDepth 300000 in
  decide

theorem corrected_lowered_degrees :
    (∀ t ∈ correctedFinalLoweredExtTransitionGates, t.degree ≤ 4) ∧
      (∀ t ∈ correctedFinalLoweredMaskedEndpointDeg2, t.degree ≤ 2) ∧
      (∀ t ∈ correctedFinalLoweredMaskedEndpointDeg4, t.degree ≤ 4) := by
  set_option maxRecDepth 300000 in
  decide

def correctedCompileList
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (ts : List CorrectedFinalTypedExpr) :
    List (CoeffExpr F) :=
  ts.flatMap fun t => List.ofFn fun k : Fin 3 => correctedFinalTypedCompile b t k

@[simp] theorem correctedCompileList_length
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (ts : List CorrectedFinalTypedExpr) :
    (correctedCompileList b ts).length = ts.length * 3 := by
  simp [correctedCompileList]

theorem correctedCompileList_degree
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (ts : List CorrectedFinalTypedExpr) (d : ℕ)
    (hdeg : ∀ t ∈ ts, t.degree ≤ d) :
    ∀ g ∈ correctedCompileList b ts, g.degree ≤ d := by
  intro g hg
  rw [correctedCompileList] at hg
  obtain ⟨xs, hxs, hg⟩ := List.mem_flatten.mp hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hxs
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
  exact (correctedFinalTypedCompile_degree_le b t k).trans (hdeg t ht)

abbrev CorrectedCoreExtGateId := Fin 78
abbrev CorrectedResidualWitnessId := Fin 3

def correctedFinalExtGate (i : CorrectedCoreExtGateId) : CorrectedFinalTypedExpr :=
  correctedFinalLoweredExtTransitionGates.get ⟨i, by
    rw [corrected_lowered_counts.1]
    exact i.isLt⟩

def correctedFinalResidualSource : CorrectedResidualWitnessId → CorrectedFinalTypedExpr
  | 0 => correctedFinalExtGate 10
  | 1 => correctedFinalExtGate 11
  | 2 => correctedFinalExtGate 20

def correctedFinalCoreExtGateCoord
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (i : CorrectedCoreExtGateId) (k : Fin 3) : CoeffExpr F :=
  if i = 10 then
    .mul notLastCoeff (residualWitnessCoord 0 k)
  else if i = 11 then
    .mul notLastCoeff (residualWitnessCoord 1 k)
  else if i = 20 then
    .mul notLastCoeff (residualWitnessCoord 2 k)
  else if i = 8 ∨ i = 9 then
    .mul notLastCoeff (correctedFinalTypedCompile b (correctedFinalExtGate i) k)
  else
    correctedFinalTypedCompile b (correctedFinalExtGate i) k

def correctedResidualAuxGateCoord
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (j : CorrectedResidualWitnessId) (k : Fin 3) : CoeffExpr F :=
  .sub (residualWitnessCoord j k)
    (correctedFinalTypedCompile b (correctedFinalResidualSource j) k)

def correctedCompileFinalCoreExt
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  (List.ofFn fun i : CorrectedCoreExtGateId =>
    List.ofFn fun k : Fin 3 => correctedFinalCoreExtGateCoord b i k).flatten

def correctedCompileResidualAux
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  (List.ofFn fun j : CorrectedResidualWitnessId =>
    List.ofFn fun k : Fin 3 => correctedResidualAuxGateCoord b j k).flatten

theorem correctedFinalCoreExtGateCoord_degree
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (i : CorrectedCoreExtGateId) (k : Fin 3) :
    (correctedFinalCoreExtGateCoord b i k).degree ≤ 4 := by
  by_cases h10 : i = 10
  · subst i
    simp [correctedFinalCoreExtGateCoord, notLastCoeff, residualWitnessCoord, isLastVar, bv,
      CoeffExpr.degree]
  by_cases h11 : i = 11
  · subst i
    simp [correctedFinalCoreExtGateCoord, notLastCoeff, residualWitnessCoord, isLastVar, bv,
      CoeffExpr.degree]
  by_cases h20 : i = 20
  · subst i
    simp [correctedFinalCoreExtGateCoord, notLastCoeff, residualWitnessCoord, isLastVar, bv,
      CoeffExpr.degree]
  by_cases hsafe : i = 8 ∨ i = 9
  · have htyped :
        (correctedFinalTypedCompile b (correctedFinalExtGate i) k).degree ≤ 3 := by
      rcases hsafe with rfl | rfl <;>
        exact (correctedFinalTypedCompile_degree_le b _ k).trans (by decide)
    simp only [correctedFinalCoreExtGateCoord, h10, h11, h20, hsafe, if_false, if_true,
      CoeffExpr.degree]
    exact Nat.add_le_add (by simp [notLastCoeff, isLastVar, bv, CoeffExpr.degree]) htyped
  · simp only [correctedFinalCoreExtGateCoord, h10, h11, h20, hsafe, if_false]
    exact (correctedFinalTypedCompile_degree_le b (correctedFinalExtGate i) k).trans
      (corrected_lowered_degrees.1 _ (List.get_mem _ _))

theorem correctedResidualAuxGateCoord_degree
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (j : CorrectedResidualWitnessId) (k : Fin 3) :
    (correctedResidualAuxGateCoord b j k).degree ≤ 4 := by
  have hsource : (correctedFinalResidualSource j).degree ≤ 4 := by
    fin_cases j <;> decide
  simp only [correctedResidualAuxGateCoord, CoeffExpr.degree]
  exact max_le (by simp [residualWitnessCoord, CoeffExpr.degree])
    ((correctedFinalTypedCompile_degree_le b (correctedFinalResidualSource j) k).trans hsource)

def correctedFinalComputeAllGates
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (n : ℕ) (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  finalBaseTransitionGates n ++
    correctedCompileFinalCoreExt b ++
    correctedCompileResidualAux b ++
    correctedCompileList b correctedFinalLoweredMaskedEndpointDeg2 ++
    correctedCompileList b correctedFinalLoweredMaskedEndpointDeg4 ++
    finalEndpointEqualityChecks

@[simp] theorem correctedFinalComputeAllGates_length
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (n : ℕ) (b : Basis (Fin 3) F K) :
    (correctedFinalComputeAllGates n b).length = 289 := by
  simp [correctedFinalComputeAllGates, correctedCompileFinalCoreExt,
    correctedCompileResidualAux, corrected_lowered_counts, finalEndpointEqualityChecks]

theorem correctedFinalComputeAllGates_degree
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (n : ℕ) (b : Basis (Fin 3) F K) :
    ∀ g ∈ correctedFinalComputeAllGates n b, g.degree ≤ 4 := by
  intro g hg
  simp only [correctedFinalComputeAllGates, List.mem_append] at hg
  rcases hg with ((((hb | hc) | ha) | h2) | h4) | heq
  · exact (finalBaseTransitionGates_degree n g hb).trans (by decide)
  · rw [correctedCompileFinalCoreExt] at hc
    obtain ⟨xs, hxs, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hc
    exact correctedFinalCoreExtGateCoord_degree b i k
  · rw [correctedCompileResidualAux] at ha
    obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
    exact correctedResidualAuxGateCoord_degree b j k
  · exact (correctedCompileList_degree b correctedFinalLoweredMaskedEndpointDeg2 2
      corrected_lowered_degrees.2.1 g h2).trans (by decide)
  · exact correctedCompileList_degree b correctedFinalLoweredMaskedEndpointDeg4 4
      corrected_lowered_degrees.2.2 g h4
  · exact (finalEndpointEqualityChecks_degree g heq).trans (by decide)

/-- Separately named corrected raw RAP.  Production names are intentionally untouched. -/
def CorrectedFinalComputeRAP
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (H : Finset F) : RAP F where
  e := 3
  k := 2
  wRAP := ![196, 3]
  w := 199
  w_eq := by rw [Fin.sum_univ_two]; norm_num
  h := h
  d := 4
  s := (correctedFinalComputeAllGates n b).length
  ω := orbit.ω
  β := orbit.βcoset
  I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
  C := fun i => coeffToMv chalVal pubVal ((correctedFinalComputeAllGates n b).get i)
  C_vars := fun i => coeffToMv_vars chalVal pubVal _
  C_deg := fun i =>
    (coeffToMv_totalDegree_le chalVal pubVal _).trans
      (correctedFinalComputeAllGates_degree n b _ (List.get_mem _ _))
  H := H
  β_ne_zero := orbit.βcoset_ne_zero
  I_bound := by
    intro q hq
    have hq2 : q.2 = 0 ∨ q.2 = 1 := by
      have h2 := (Finset.mem_product.mp hq).2
      simpa [Finset.mem_insert, Finset.mem_singleton] using h2
    have hge : 2 ≤ 2 ^ h := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) orbit.h_pos
    rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega

def CorrectedFinalFixedPreprocessingRAP
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) : FixedPreprocessingRAP F where
  rap := CorrectedFinalComputeRAP (n := n) b chalVal pubVal orbit (rowNodeSet nodes)
  rounds_pos := by norm_num [CorrectedFinalComputeRAP]
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨11 + (j : ℕ), by
          change 11 + (j : ℕ) < 196
          omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

abbrev CorrectedNamedComputeRAP := @CorrectedFinalFixedPreprocessingRAP

theorem corrected_rap_fingerprint
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    let R := CorrectedFinalComputeRAP (n := n) b chalVal pubVal orbit H
    R.w = 199 ∧ R.s = 289 ∧ R.d = 4 ∧ R.k = 2 ∧ R.e = 3 := by
  exact ⟨rfl, correctedFinalComputeAllGates_length n b, rfl, rfl, rfl⟩

/-! ## 4. -/

def productionCancellationEnv : Env (ZMod 73) where
  trace := fun i => if i = 3 then 1 else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

@[simp] theorem productionCancellationEnv_trace (i : ℕ) :
    productionCancellationEnv.trace i = if i = 3 then 1 else 0 := rfl

@[simp] theorem productionCancellationEnv_traceNext (i : ℕ) :
    productionCancellationEnv.traceNext i = 0 := rfl

@[simp] theorem productionCancellationEnv_chal (i : ℕ) :
    productionCancellationEnv.chal i = 0 := rfl

@[simp] theorem productionCancellationEnv_pub (i : ℕ) :
    productionCancellationEnv.pub i = 0 := rfl

/-
@[simp] theorem productionCancellationEnv_semanticPub_zero
    (role coord : ℕ) :
    (semanticPub.traceCur role coord).eval productionCancellationEnv = 0 := by
  unfold semanticPub
  split <;>
    simp [restoredPub, Nock.Reified.allStates, Nock.Reified.opCol,
      sourcePubAt, restoredAField, restoredBField, restoredIOHostField,
      restoredDenomHostField, overlayANat, overlayBNat,
      productionCancellationEnv, pubFP, decFP, ext0, Expr.eval] <;>
    norm_num [ext0] <;>
    omega
-/

@[simp] theorem productionCancellationEnv_decFP_zero
    (role coord : ℕ) :
    (decFP .traceCur role coord).eval productionCancellationEnv = 0 := by
  simp [decFP, productionCancellationEnv, Expr.eval]
  norm_num [ext0]
  omega

def productionCollisionFamily : List Expr :=
  (formulaExprs.map (fun e => e.subst computeSubst)) ++ [optimizedCombinedGate]

theorem productionCollisionFamily_mem :
    productionCollisionFamily ∈ finalNonIOSourceFamilies17 := by
  simp [productionCollisionFamily, finalNonIOSourceFamilies17, nonIOSourceFamilies17With]

/-- Concrete cancellation in one exact production family: challenge 9 is zero, the first formula
coefficient vanishes, and the corrected selector-relative combined equation is nonzero on the
deliberately malformed selector assignment `op3 = 1`, all others zero. -/
theorem exact_production_family_cancellation :
    FinalCollisionEvent productionCancellationEnv productionCollisionFamily := by
  constructor
  · norm_num [productionCollisionFamily, formulaExprs, fpEqC, consExpr, finalRlcFold,
      finalFoldChallenge, Expr.subst, Expr.eval, computeSubst,
      computeTraceSubst, Nock.Reified.cF, Nock.Reified.cFh, Nock.Reified.cFt,
      Nock.Reified.fpCol, Nock.Reified.tc, pubFP, ext0]
    all_goals
      norm_num [semanticPub, pubFP, productionCancellationEnv, ext0, Expr.eval]
  · refine ⟨optimizedCombinedGate, by simp [productionCollisionFamily], ?_⟩
    norm_num [optimizedCombinedGate, combinedSourceExpr, combinedSelectorExpr,
      Expr.subst, Expr.eval, computeSubst, computeTraceSubst, Nock.Reified.cS,
      Nock.Reified.cE, Nock.Reified.cSf1e, Nock.Reified.cSf2e, Nock.Reified.fpCol,
      Nock.Reified.tc, Nock.Reified.chl, pubFP, decFP, ext0,
      semanticPub, restoredPub, Nock.Reified.allStates, Nock.Reified.opCol,
      sourcePubAt, restoredAField, restoredBField, restoredIOHostField,
      restoredDenomHostField, overlayANat, overlayBNat,
      productionCancellationEnv]

theorem exact_production_collision_event_nonempty :
    FinalComputeCollisionEvent productionCancellationEnv :=
  ⟨productionCollisionFamily, productionCollisionFamily_mem,
    exact_production_family_cancellation⟩

/-- The exact per-family production reverse theorem is false without the collision premise. -/
theorem no_unconditional_production_reverse :
    ¬ (∀ (env : Env (ZMod 73)) (es : List Expr),
      es ∈ finalNonIOSourceFamilies17 →
      (finalRlcFold es).eval env = 0 →
      ∀ e ∈ es, e.eval env = 0) := by
  intro h
  have hall := h productionCancellationEnv productionCollisionFamily
    productionCollisionFamily_mem exact_production_family_cancellation.1
  obtain ⟨e, he, hne⟩ := exact_production_family_cancellation.2
  exact hne (hall e he)

def productionCollisionFreeEnv : Env (ZMod 73) where
  trace := fun _ => 0
  traceNext := fun _ => 0
  chal := fun i => if i = compilerChallengeBase then 2 else 0
  pub := fun _ => 0

@[simp] theorem productionCollisionFreeEnv_trace (i : ℕ) :
    productionCollisionFreeEnv.trace i = 0 := rfl

@[simp] theorem productionCollisionFreeEnv_traceNext (i : ℕ) :
    productionCollisionFreeEnv.traceNext i = 0 := rfl

@[simp] theorem productionCollisionFreeEnv_pub (i : ℕ) :
    productionCollisionFreeEnv.pub i = 0 := rfl

@[simp] theorem productionCollisionFreeEnv_chal9 :
    productionCollisionFreeEnv.chal compilerChallengeBase = 2 := by
  simp [productionCollisionFreeEnv]

@[simp] theorem productionCollisionFreeEnv_chal9_raw :
    productionCollisionFreeEnv.chal 9 = 2 := by
  norm_num [productionCollisionFreeEnv, compilerChallengeBase]

@[simp] theorem productionCollisionFreeEnv_chal1 :
    productionCollisionFreeEnv.chal 1 = 0 := by
  norm_num [productionCollisionFreeEnv, compilerChallengeBase]

@[simp] theorem productionCollisionFreeEnv_semanticPub_zero
    (role coord : ℕ) :
    (semanticPub .traceCur role coord).eval productionCollisionFreeEnv = 0 := by
  unfold semanticPub
  split <;>
    simp [restoredPub, Nock.Reified.allStates, Nock.Reified.opCol,
      productionCollisionFreeEnv, pubFP, Expr.eval]

@[simp] theorem productionCollisionFreeEnv_decFP_zero
    (role coord : ℕ) :
    (decFP .traceCur role coord).eval productionCollisionFreeEnv = 0 := by
  simp [decFP, productionCollisionFreeEnv, Expr.eval]

/-- Updating one list entry preserves a property that held everywhere and holds at the replacement. -/
theorem all_mem_set {α : Type*} (P : α → Prop) (xs : List α) (n : ℕ) (y : α)
    (hxs : ∀ x ∈ xs, P x) (hy : P y) :
    ∀ x ∈ xs.set n y, P x := by
  induction xs generalizing n with
  | nil => simp
  | cons hd tl ih =>
      cases n with
      | zero =>
          intro z hz
          simp only [List.set, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hy
          · exact hxs z (by simp [hz])
      | succ n =>
          intro z hz
          simp only [List.set, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hxs _ (by simp)
          · exact ih n (fun w hw => hxs w (by simp [hw])) z hz

theorem production_zero_env_refolded_sources_zero :
    ∀ e ∈ refoldedPerStateGates, e.eval productionCollisionFreeEnv = 0 := by
  have hmap :
      ∀ e ∈ Nock.Reified.perStateGated.map (fun e => e.subst computeSubst),
        e.eval productionCollisionFreeEnv = 0 := by
    intro e he
    obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp he
    rw [Nock.Reified.perStateGated] at hsrc
    obtain ⟨st, hst, hsrc⟩ := List.mem_flatMap.mp hsrc
    obtain ⟨body, hbody, rfl⟩ := List.mem_map.mp hsrc
    cases st <;>
      norm_num [Nock.Reified.gateBy, Expr.subst, Expr.eval, computeSubst, computeTraceSubst,
        productionCollisionFreeEnv, Nock.Reified.opCol, Nock.Reified.tc]
  rw [refoldedPerStateGates]
  exact all_mem_set (fun e => e.eval productionCollisionFreeEnv = 0)
    ((Nock.Reified.perStateGated.map (fun e => e.subst computeSubst)).set
      177 op3ELeafBoolRefold) 270 op5ELeafBoolRefold
    (all_mem_set (fun e => e.eval productionCollisionFreeEnv = 0)
      (Nock.Reified.perStateGated.map (fun e => e.subst computeSubst))
      177 op3ELeafBoolRefold hmap (by
        simp [op3ELeafBoolRefold, productionCollisionFreeEnv, pubFP, Expr.eval]))
    (by simp [op5ELeafBoolRefold, productionCollisionFreeEnv, pubFP, Expr.eval])

theorem stateBlock_mem_refolded (st : Nock.ComputeTable.State) (e : Expr)
    (he : e ∈ stateBlock st) :
    e ∈ refoldedPerStateGates := by
  cases st <;> simp only [stateBlock] at he
  · exact List.mem_of_mem_take he
  all_goals
    exact List.mem_of_mem_drop (List.mem_of_mem_take he)

theorem stateBlock_zero (st : Nock.ComputeTable.State) :
    ∀ e ∈ stateBlock st, e.eval productionCollisionFreeEnv = 0 := by
  intro e he
  exact production_zero_env_refolded_sources_zero e (stateBlock_mem_refolded st e he)

theorem finalCollisionFree_of_all_zero (es : List Expr)
    (hzero : ∀ e ∈ es, e.eval productionCollisionFreeEnv = 0) :
    FinalCollisionFree productionCollisionFreeEnv es := by
  intro hfold
  exact hzero

set_option linter.unusedSimpArgs false in
theorem productionCollisionFamily_sources_zero :
    ∀ e ∈ productionCollisionFamily, e.eval productionCollisionFreeEnv = 0 := by
  intro e he
  rw [productionCollisionFamily, List.mem_append] at he
  rcases he with he | he
  · obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp he
    simp only [formulaExprs, fpEqC, List.mem_cons, List.not_mem_nil, or_false] at hsrc
    rcases hsrc with (hsrc | hsrc | hsrc)
    all_goals rw [hsrc]
    all_goals
      simp [fpEqC, consExpr, Expr.subst, Expr.eval, computeSubst, computeTraceSubst,
        Nock.Reified.cF, Nock.Reified.cFh, Nock.Reified.cFt, Nock.Reified.cS,
        Nock.Reified.cE, Nock.Reified.cSf1e, Nock.Reified.cSf2e,
        Nock.Reified.fpCol, Nock.Reified.tc, Nock.Reified.chl,
        pubFP, decFP, ext0, semanticPub, restoredPub, Nock.Reified.allStates,
        Nock.Reified.opCol, sourcePubAt, restoredAField, restoredBField,
        restoredIOHostField, restoredDenomHostField, overlayANat, overlayBNat,
        productionCollisionFreeEnv]
  · simp only [List.mem_singleton] at he
    subst e
    simp [optimizedCombinedGate, combinedSourceExpr, combinedSelectorExpr,
      Expr.subst, Expr.eval, computeSubst, computeTraceSubst,
      Nock.Reified.cS, Nock.Reified.cE, Nock.Reified.cSf1e,
      Nock.Reified.cSf2e, Nock.Reified.fpCol, Nock.Reified.tc,
      Nock.Reified.chl, pubFP, decFP, ext0, semanticPub, restoredPub,
      Nock.Reified.allStates, Nock.Reified.opCol, sourcePubAt,
      restoredAField, restoredBField, restoredIOHostField,
      restoredDenomHostField, overlayANat, overlayBNat,
      productionCollisionFreeEnv]
/-
  intro e he
  norm_num [productionCollisionFamily, formulaExprs, fpEqC, consExpr,
    Expr.subst, Expr.eval, computeSubst, computeTraceSubst,
    Nock.Reified.cF, Nock.Reified.cFh, Nock.Reified.cFt, Nock.Reified.cS,
    Nock.Reified.cE, Nock.Reified.cSf1e, Nock.Reified.cSf2e,
    Nock.Reified.fpCol, Nock.Reified.tc, Nock.Reified.chl,
    pubFP, ext0, optimizedCombinedGate, combinedSourceExpr] at he ⊢
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
-/

/-- Collision-freedom is not vacuous: one concrete environment satisfies all seventeen exact
family exclusions. -/
theorem exact_production_collision_free_nonvacuous :
    FinalComputeCollisionFree productionCollisionFreeEnv := by
  intro es hes
  simp only [finalNonIOSourceFamilies17, nonIOSourceFamilies17With, List.mem_cons,
    List.not_mem_nil, or_false] at hes
  rcases hes with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply finalCollisionFree_of_all_zero
    intro e he
    rw [List.mem_append] at he
    rcases he with he | he
    · exact stateBlock_zero .s0 e he
    · exact stateBlock_zero .s1 e he
  · apply finalCollisionFree_of_all_zero
    intro e he
    rw [List.mem_append] at he
    rcases he with he | he
    · exact stateBlock_zero .s2 e he
    · exact stateBlock_zero .s3 e he
  · apply finalCollisionFree_of_all_zero
    intro e he
    rw [List.mem_append] at he
    rcases he with he | he
    · exact stateBlock_zero .s4 e he
    · exact stateBlock_zero .s5 e he
  · simp [FinalCollisionFree, finalRlcFold, Expr.eval]
  · simp [FinalCollisionFree, finalRlcFold, Expr.eval]
  · simp [FinalCollisionFree, finalRlcFold, Expr.eval]
  · intro hfold
    exact productionCollisionFamily_sources_zero
  · simp [FinalCollisionFree, finalRlcFold, Expr.eval]
  · simp [FinalCollisionFree, finalRlcFold, Expr.eval]
  · simp [FinalCollisionFree, finalRlcFold, Expr.eval]
  · simp [FinalCollisionFree, finalRlcFold, Expr.eval]
  · simp [FinalCollisionFree, finalRlcFold, Expr.eval]
  · exact finalCollisionFree_of_all_zero _ (stateBlock_zero .s6)
  · exact finalCollisionFree_of_all_zero _ (stateBlock_zero .s7)
  · exact finalCollisionFree_of_all_zero _ (stateBlock_zero .s8)
  · exact finalCollisionFree_of_all_zero _ (stateBlock_zero .s9)
  · exact finalCollisionFree_of_all_zero _ (stateBlock_zero .cons)

theorem production_complement_is_exact (env : Env (ZMod 73)) :
    ¬ FinalComputeCollisionFree env ↔ FinalComputeCollisionEvent env :=
  not_finalComputeCollisionFree_iff_event env

theorem production_completeness_unconditional (env : Env (ZMod 73))
    (hsource : ∀ e ∈ finalNonIOSourceFamilies17.flatten, e.eval env = 0) :
    ∀ g ∈ finalNonIOTransitionGates, g.eval env = 0 :=
  finalNonIOTransitionGates_complete env hsource

theorem production_soundness_is_conditional (env : Env (ZMod 73))
    (hfree : FinalComputeCollisionFree env)
    (hgates : ∀ g ∈ finalNonIOTransitionGates, g.eval env = 0) :
    ∀ e ∈ finalNonIOSourceFamilies17.flatten, e.eval env = 0 :=
  finalNonIOTransitionGates_sound env hfree hgates

/-! ## 5. Cardinality-bound dependency -/

/-- Exact sum of per-family Horner degrees: `511` source coefficients minus `17` nonempty
families.  This is the numerator of the missing one-row challenge-9 union bound. -/
theorem exact_challenge9_root_budget :
    (finalNonIOSourceFamilies17.map (fun es => es.length - 1)).sum = 494 := by
  set_option maxRecDepth 300000 in
  decide

/-- Existing root-count theorem required by the future bound. -/
theorem existing_rlc_root_count_dependency
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (q : K[X]) (hq : q ≠ 0) :
    (Finset.univ.filter (fun r : K => q.eval r = 0)).card ≤ q.natDegree :=
  NPR.card_eval_zero_le q hq

/-- Vary only challenge 9 while freezing the complete row and every other verifier value. -/
def withFinalFoldChallenge {K : Type*} (baseEnv : Env K) (z : K) : Env K where
  trace := baseEnv.trace
  traceNext := baseEnv.traceNext
  chal := fun i => if i = compilerChallengeBase then z else baseEnv.chal i
  pub := baseEnv.pub

/-- Exact still-missing statement shape.  It is intentionally a proposition, not an inhabitant:
freeze all row data except challenge 9, reify each of the seventeen folds as a univariate
polynomial, prove source independence and nonzero/degree bounds, then union-bound by 494. -/
def FinalChallenge9CardinalityBoundGoal : Prop :=
  ∀ {K : Type*} [Field K] [Fintype K] [DecidableEq K]
      (baseEnv : Env K) (bad : Finset K),
    (∀ z ∈ bad, FinalComputeCollisionEvent (withFinalFoldChallenge baseEnv z)) →
    bad.card ≤ 494

/-! ## 6. -/

abbrev HistoricalNamedComputeRAP :=
  @Nock.NockVMROM.Thm54.OptimizedComputeFinal.NamedComputeRAP

theorem historical_name_compatibility
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) :
    HistoricalNamedComputeRAP hn nodes b chalVal pubVal orbit =
      Nock.NockVMROM.Thm54.OptimizedComputeFinal.NamedComputeRAP
        hn nodes b chalVal pubVal orbit := by
  rfl

theorem corrected_name_compatibility
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) :
    CorrectedNamedComputeRAP hn nodes b chalVal pubVal orbit =
      CorrectedFinalFixedPreprocessingRAP hn nodes b chalVal pubVal orbit := by
  rfl

def strict_package_still_requires_B29
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (P : Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage F K hOrb q Λ) :=
  Nock.RedTeam.Batch59.strict_package_still_requires_B29 P

theorem paper_alias_still_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch59.paper_alias_still_forest

#print axioms correctedLowerFinal_eval
#print axioms correctedFinalTypedCompile_eval
#print axioms correctedFinalTypedCompile_reconstruct
#print axioms correctedFinalTypedCompile_degree_le
#print axioms correctedFinalTypedCompile_support
#print axioms final_source_public_indices_exact
#print axioms final_base_selector_public_indices_exact
#print axioms corrected_extension_and_base_public_indices_identical
#print axioms historical_scalar_public_replay_rejected
#print axioms corrected_scalar_public_same_raw_index
#print axioms correctedFinalComputeAllGates_degree
#print axioms corrected_rap_fingerprint
#print axioms exact_production_family_cancellation
#print axioms exact_production_collision_event_nonempty
#print axioms no_unconditional_production_reverse
#print axioms exact_production_collision_free_nonvacuous
#print axioms production_complement_is_exact
#print axioms production_completeness_unconditional
#print axioms production_soundness_is_conditional
#print axioms exact_challenge9_root_budget
#print axioms existing_rlc_root_count_dependency
#print axioms strict_package_still_requires_B29
#print axioms paper_alias_still_forest

end
end Nock.RedTeam.Batch60
