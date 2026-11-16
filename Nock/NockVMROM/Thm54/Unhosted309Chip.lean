import Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
import Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
import Nock.NockVMROM.Thm54.ComputeWalkLabel
import Nock.NockVMROM.Thm54.OptimizedComputeGateBasis

/-!
# The un-hosted compute chip at width 309

The deployed compute chip (`ProductionNamedComputeRAP`, width `303`) hosts the walk `count` /
`acc` in coordinates `0`/`1` of the state-dependent fingerprint role `overlayANat st`
(`K`-roles `9/10` in `s0`/`s2`, `6/7` in `s1`, `18/19` in `s3`/`s4`, `27/28` otherwise).  Here
the walk gets its own two `𝕂` columns, appended so that no existing physical index moves:

* `W0 = 303..305` (`walkCount`), `W1 = 306..308` (`walkAcc`);
* the seven walk sources that read the hosts as walk values are retargeted onto `W0`/`W1`:
  `aux0` (`walkCountStep`), `aux1` (`walkAccStep`), `ep2₁` (`finalMaskedWalkCount1`),
  `ep2₂` (`finalMaskedWalkOut`), `ep4` (`finalMaskedWalkAccInit`), `core76`
  (`walkQueueNonEmpty`), `core77` (`walkQueueTiling`);
* the host cells stay as **label** reads only (`sourcePubAtR`, unchanged);
* no gate is added: `s = 418`, `d = 4`, `k = 2`, `w = 309`.

The source language is `Expr` with `.Var _ 303` / `.Var _ 306` naming the two new `𝕂` columns
(the `certExt` convention: a `𝕂` column is named by its first physical limb).  The typed
language `WTyped` extends `CorrectedFinalTypedExpr` by those two leaves.
-/

namespace Nock.NockVMROM.Thm54
namespace Unhosted309

set_option maxRecDepth 300000
set_option maxHeartbeats 8000000

open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open OptimizedComputeBaseGates
open OptimizedComputeFinal hiding residualWitnessRole ResidualWitnessId FinalExtensionColumn
open OptimizedComputeFinalTypedLowering
open OptimizedComputeCorrectedFinal
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open scoped Polynomial

noncomputable section

/-! ## 1. The two walk columns -/

/-- First physical limb of the walk-count column `W0`. -/
def walkCountCol : ℕ := 303
/-- First physical limb of the walk-accumulator column `W1`. -/
def walkAccCol : ℕ := 306

/-- Physical limb `k` of walk column `j` (`j = 0` count, `j = 1` acc). -/
def walkLimb (j : Fin 2) (k : Fin 3) : ℕ := 303 + 3 * (j : ℕ) + (k : ℕ)

theorem walkLimb_range (j : Fin 2) (k : Fin 3) : 303 ≤ walkLimb j k ∧ walkLimb j k < 309 := by
  unfold walkLimb; omega

/-! ## 2. The typed language at width 309 -/

/-- `CorrectedFinalTypedExpr` plus the current/next walk columns. -/
inductive WTyped where
  | leaf : CorrectedFinalTypedExpr → WTyped
  | wCur : Fin 2 → WTyped
  | wNext : Fin 2 → WTyped
  | add : WTyped → WTyped → WTyped
  | sub : WTyped → WTyped → WTyped
  | mul : WTyped → WTyped → WTyped
  | neg : WTyped → WTyped
  | pow : WTyped → ℕ → WTyped
deriving DecidableEq

def WTyped.degree : WTyped → ℕ
  | .leaf t => t.degree
  | .wCur _ | .wNext _ => 1
  | .add x y | .sub x y => max x.degree y.degree
  | .mul x y => x.degree + y.degree
  | .neg x => x.degree
  | .pow x n => n * x.degree

/-- The width-309 typed environment: the deployed one plus the two walk columns. -/
structure Env309 (F K : Type*) [Zero F] [Zero K] where
  base : CorrectedFinalTypedEnv F K
  walk : Fin 2 → K
  walkNext : Fin 2 → K

def WTyped.eval {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : Env309 F K) : WTyped → K
  | .leaf t => t.eval env.base
  | .wCur j => env.walk j
  | .wNext j => env.walkNext j
  | .add x y => x.eval env + y.eval env
  | .sub x y => x.eval env - y.eval env
  | .mul x y => x.eval env * y.eval env
  | .neg x => -x.eval env
  | .pow x n => (x.eval env) ^ n

/-- The mixed source environment: the deployed decoder plus `303 ↦ W0`, `306 ↦ W1`. -/
def Env309.toSourceEnv {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : Env309 F K) : Env K where
  trace i := if i = 303 then env.walk 0 else if i = 306 then env.walk 1
    else env.base.toSourceEnv.trace i
  traceNext i := if i = 303 then env.walkNext 0 else if i = 306 then env.walkNext 1
    else env.base.toSourceEnv.traceNext i
  chal := env.base.toSourceEnv.chal
  pub := env.base.toSourceEnv.pub

/-- Lowering at width 309: the two walk columns, else the deployed lowering. -/
def lower309 : Expr → Option WTyped
  | .Var .traceCur i =>
      if i = 303 then some (.wCur 0) else if i = 306 then some (.wCur 1)
      else (correctedLowerFinal (.Var .traceCur i)).map .leaf
  | .Var .traceNext i =>
      if i = 303 then some (.wNext 0) else if i = 306 then some (.wNext 1)
      else (correctedLowerFinal (.Var .traceNext i)).map .leaf
  | .Var .challenge i => (correctedLowerFinal (.Var .challenge i)).map .leaf
  | .Var .publicVal i => (correctedLowerFinal (.Var .publicVal i)).map .leaf
  | .Const c => some (.leaf (.const c))
  | .Add x y => return .add (← lower309 x) (← lower309 y)
  | .Sub x y => return .sub (← lower309 x) (← lower309 y)
  | .Mul x y => return .mul (← lower309 x) (← lower309 y)
  | .Neg x => return .neg (← lower309 x)
  | .Pow x n => return .pow (← lower309 x) n

theorem lower309_eval {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : Env309 F K) : ∀ (e : Expr) (t : WTyped), lower309 e = some t →
      e.eval env.toSourceEnv = t.eval env
  | .Var .traceCur i, t, h => by
      by_cases h3 : i = 303
      · subst h3; simp [lower309] at h; subst t; simp [Expr.eval, Env309.toSourceEnv, WTyped.eval]
      by_cases h6 : i = 306
      · subst h6; simp [lower309] at h; subst t; simp [Expr.eval, Env309.toSourceEnv, WTyped.eval]
      simp only [lower309, h3, h6, if_false] at h
      cases hl : correctedLowerFinal (.Var .traceCur i) with
      | none => simp [hl] at h
      | some t' =>
          simp [hl] at h; subst t
          have := correctedLowerFinal_eval env.base _ _ hl
          simp only [Expr.eval] at this
          simp [Expr.eval, Env309.toSourceEnv, WTyped.eval, h3, h6, this]
  | .Var .traceNext i, t, h => by
      by_cases h3 : i = 303
      · subst h3; simp [lower309] at h; subst t; simp [Expr.eval, Env309.toSourceEnv, WTyped.eval]
      by_cases h6 : i = 306
      · subst h6; simp [lower309] at h; subst t; simp [Expr.eval, Env309.toSourceEnv, WTyped.eval]
      simp only [lower309, h3, h6, if_false] at h
      cases hl : correctedLowerFinal (.Var .traceNext i) with
      | none => simp [hl] at h
      | some t' =>
          simp [hl] at h; subst t
          have := correctedLowerFinal_eval env.base _ _ hl
          simp only [Expr.eval] at this
          simp [Expr.eval, Env309.toSourceEnv, WTyped.eval, h3, h6, this]
  | .Var .challenge i, t, h => by
      simp only [lower309] at h
      cases hl : correctedLowerFinal (.Var .challenge i) with
      | none => simp [hl] at h
      | some t' =>
          simp [hl] at h; subst t
          have := correctedLowerFinal_eval env.base _ _ hl
          simp only [Expr.eval] at this
          simp [Expr.eval, Env309.toSourceEnv, WTyped.eval, this]
  | .Var .publicVal i, t, h => by
      simp only [lower309] at h
      cases hl : correctedLowerFinal (.Var .publicVal i) with
      | none => simp [hl] at h
      | some t' =>
          simp [hl] at h; subst t
          have := correctedLowerFinal_eval env.base _ _ hl
          simp only [Expr.eval] at this
          simp [Expr.eval, Env309.toSourceEnv, WTyped.eval, this]
  | .Const c, t, h => by
      simp only [lower309, Option.some.injEq] at h; subst t
      simp [Expr.eval, WTyped.eval, CorrectedFinalTypedExpr.eval]
  | .Add x y, t, h => by
      cases hx : lower309 x with
      | none => simp [lower309, hx] at h
      | some tx =>
        cases hy : lower309 y with
        | none => simp [lower309, hx, hy] at h
        | some ty =>
          simp [lower309, hx, hy] at h; subst t
          simp [Expr.eval, WTyped.eval, lower309_eval env x tx hx, lower309_eval env y ty hy]
  | .Sub x y, t, h => by
      cases hx : lower309 x with
      | none => simp [lower309, hx] at h
      | some tx =>
        cases hy : lower309 y with
        | none => simp [lower309, hx, hy] at h
        | some ty =>
          simp [lower309, hx, hy] at h; subst t
          simp [Expr.eval, WTyped.eval, lower309_eval env x tx hx, lower309_eval env y ty hy]
  | .Mul x y, t, h => by
      cases hx : lower309 x with
      | none => simp [lower309, hx] at h
      | some tx =>
        cases hy : lower309 y with
        | none => simp [lower309, hx, hy] at h
        | some ty =>
          simp [lower309, hx, hy] at h; subst t
          simp [Expr.eval, WTyped.eval, lower309_eval env x tx hx, lower309_eval env y ty hy]
  | .Neg x, t, h => by
      cases hx : lower309 x with
      | none => simp [lower309, hx] at h
      | some tx =>
          simp [lower309, hx] at h; subst t
          simp [Expr.eval, WTyped.eval, lower309_eval env x tx hx]
  | .Pow x n, t, h => by
      cases hx : lower309 x with
      | none => simp [lower309, hx] at h
      | some tx =>
          simp [lower309, hx] at h; subst t
          simp [Expr.eval, WTyped.eval, lower309_eval env x tx hx]

/-! ## 3. Coordinate compilation at width 309 -/

def compile309 {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) : WTyped → Fin 3 → CoeffExpr F
  | .leaf t => correctedFinalTypedCompile b t
  | .wCur j => fun k => .var .traceCur (walkLimb j k)
  | .wNext j => fun k => .var .traceNext (walkLimb j k)
  | .add x y => fun k => .add (compile309 b x k) (compile309 b y k)
  | .sub x y => fun k => .sub (compile309 b x k) (compile309 b y k)
  | .neg x => fun k => .neg (compile309 b x k)
  | .mul x y => mulVec b (compile309 b x) (compile309 b y)
  | .pow x n => powVec b (compile309 b x) n

/-- The coordinate relation at width 309. -/
structure IsCoordEnv309 {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (env : Env309 F K) (envF : Env F) : Prop where
  base : IsCorrectedFinalCoordEnv b env.base envF
  walk : ∀ j k, envF.trace (walkLimb j k) = coord b (env.walk j) k
  walkNext : ∀ j k, envF.traceNext (walkLimb j k) = coord b (env.walkNext j) k

theorem compile309_eval {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (env : Env309 F K) (envF : Env F) (henv : IsCoordEnv309 b env envF)
    (t : WTyped) (k : Fin 3) :
    coord b (t.eval env) k = (compile309 b t k).eval envF := by
  induction t generalizing k with
  | leaf t => exact correctedFinalTypedCompile_eval b env.base envF henv.base t k
  | wCur j => simp [WTyped.eval, compile309, CoeffExpr.eval, henv.walk]
  | wNext j => simp [WTyped.eval, compile309, CoeffExpr.eval, henv.walkNext]
  | add x y ihx ihy =>
      simp only [WTyped.eval, compile309, CoeffExpr.eval, coord_add, ihx, ihy]
  | sub x y ihx ihy =>
      simp only [WTyped.eval, compile309, CoeffExpr.eval, coord_sub, ihx, ihy]
  | neg x ih =>
      simp only [WTyped.eval, compile309, CoeffExpr.eval, coord_neg, ih]
  | mul x y ihx ihy => exact eval_mulVec b envF _ _ (x.eval env) (y.eval env) ihx ihy k
  | pow x n ih => exact eval_powVec b envF _ (x.eval env) ih n k

theorem compile309_zero_iff {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (env : Env309 F K) (envF : Env F) (henv : IsCoordEnv309 b env envF)
    (t : WTyped) :
    (∀ k, (compile309 b t k).eval envF = 0) ↔ t.eval env = 0 := by
  constructor
  · intro h
    rw [eq_iff_coords_eq b (t.eval env) 0]
    intro k
    rw [coord_zero, compile309_eval b env envF henv]
    exact h k
  · intro h k
    rw [← compile309_eval b env envF henv, h, coord_zero]

theorem compile309_degree_le {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (t : WTyped) (k : Fin 3) :
    (compile309 b t k).degree ≤ t.degree := by
  induction t generalizing k with
  | leaf t => exact correctedFinalTypedCompile_degree_le b t k
  | wCur j => simp [compile309, WTyped.degree, CoeffExpr.degree]
  | wNext j => simp [compile309, WTyped.degree, CoeffExpr.degree]
  | add x y ihx ihy =>
      simp only [compile309, WTyped.degree, CoeffExpr.degree]; exact max_le_max (ihx k) (ihy k)
  | sub x y ihx ihy =>
      simp only [compile309, WTyped.degree, CoeffExpr.degree]; exact max_le_max (ihx k) (ihy k)
  | neg x ih => simpa [compile309, WTyped.degree, CoeffExpr.degree] using ih k
  | mul x y ihx ihy => exact degree_mulVec_le b _ _ x.degree y.degree ihx ihy k
  | pow x n ih => exact degree_powVec_le b _ x.degree ih n k

def compileList309 {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (ts : List WTyped) : List (CoeffExpr F) :=
  ts.flatMap fun t => List.ofFn fun k : Fin 3 => compile309 b t k

@[simp] theorem compileList309_length {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (ts : List WTyped) :
    (compileList309 b ts).length = ts.length * 3 := by simp [compileList309]

theorem compileList309_degree {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (ts : List WTyped) (d : ℕ) (hdeg : ∀ t ∈ ts, t.degree ≤ d) :
    ∀ g ∈ compileList309 b ts, g.degree ≤ d := by
  intro g hg
  rw [compileList309] at hg
  obtain ⟨xs, hxs, hg⟩ := List.mem_flatten.mp hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hxs
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
  exact (compile309_degree_le b t k).trans (hdeg t ht)

theorem compileList309_eval_iff {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (env : Env309 F K) (envF : Env F) (henv : IsCoordEnv309 b env envF)
    (ts : List WTyped) :
    (∀ g ∈ compileList309 b ts, g.eval envF = 0) ↔ ∀ t ∈ ts, t.eval env = 0 := by
  constructor
  · intro h t ht
    apply (compile309_zero_iff b env envF henv t).1
    intro k
    apply h
    rw [compileList309]
    exact List.mem_flatten.mpr
      ⟨List.ofFn (compile309 b t), List.mem_map.mpr ⟨t, ht, rfl⟩, List.mem_ofFn.mpr ⟨k, rfl⟩⟩
  · intro h g hg
    rw [compileList309] at hg
    obtain ⟨xs, hxs, hg⟩ := List.mem_flatten.mp hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact (compile309_zero_iff b env envF henv t).2 (h t ht) k

/-! ## 4. The seven retargeted walk sources (source `Expr` level) -/

/-- Walk transition substitution at width 309: `count`/`acc` (walk indices `1`/`2`) are the
new columns `W0`/`W1` on both rows; `ln` stays the walk line (role `61`), `cur`/`cc`/`cm` stay
in-gate (`ComputeWalkLabel`) — the label reads of the former host cells are unchanged. -/
def finalWalkSubstInGate309 : VarKind → ℕ → Expr
  | .traceCur, 1 => .Var .traceCur walkCountCol
  | .traceCur, 2 => .Var .traceCur walkAccCol
  | .traceNext, 1 => .Var .traceNext walkCountCol
  | .traceNext, 2 => .Var .traceNext walkAccCol
  | k, i => ComputeWalkLabel.finalWalkSubstInGate k i

/-- First-row walk substitution at width 309 (`count`/`acc` are `W0`/`W1`). -/
def finalWalkInitialSubst309 : VarKind → ℕ → Expr
  | .traceCur, 1 => .Var .traceCur walkCountCol
  | .traceCur, 2 => .Var .traceCur walkAccCol
  | k, i => finalWalkInitialSubst k i

/-- Terminal-row walk substitution at width 309. -/
def finalWalkTerminalSubst309 : VarKind → ℕ → Expr
  | .traceCur, 1 => .Var .traceCur walkCountCol
  | .traceCur, 2 => .Var .traceCur walkAccCol
  | k, i => finalWalkTerminalSubst k i

/-- `aux0`'s source: `count(i+1) − count(i)·cm(i+1)` on `W0`. -/
def walkCountStep309 : Expr := Trans.walkCountStep.subst finalWalkSubstInGate309
/-- `aux1`'s source: `ln(i+1)·cur(i+1) + acc(i+1) − acc(i) − count(i)·cc(i+1)` on `W0`/`W1`. -/
def walkAccStep309 : Expr := Trans.walkAccStep.subst finalWalkSubstInGate309

/-- `core76`: `notLast · (walk_inv · (W0 − ln) − 1)`. -/
def walkQueueNonEmpty309 : Expr :=
  .Mul (.Sub (.Const 1) (.Var .traceCur 12))
    (.Sub
      (.Mul (walkInv .traceCur)
        (.Sub (.Var .traceCur walkCountCol) (finalWalkLine .traceCur)))
      (.Const 1))

/-- `core77`: `isLast · (W0 − ln)`. -/
def walkQueueTiling309 : Expr :=
  .Mul (.Var .traceCur 12) (.Sub (.Var .traceCur walkCountCol) (finalWalkLine .traceCur))

/-- `ep2₁`: `isFirst · (W0 − initial_count · cm(1))`. -/
def finalMaskedWalkCount1_309 : Expr :=
  .Mul OptimizedComputeTemplate.fixedIsFirst (Trans.walkCount1.subst finalWalkInitialSubst309)
/-- `ep2₂`: `isLast · W1` (`out_walk = acc(h)`, the paper). -/
def finalMaskedWalkOut309 : Expr :=
  .Mul OptimizedComputeTemplate.fixedIsLast (Trans.walkOut.subst finalWalkTerminalSubst309)
/-- `ep4`: `isFirst² · (ln·cur + W1 − (initial_count·cc + seed))`. -/
def finalMaskedWalkAccInit309 : Expr :=
  .Mul (.Pow OptimizedComputeTemplate.fixedIsFirst 2)
    (Trans.walkAccInit.subst finalWalkInitialSubst309)

/-- The lowering with a default (total on every source below, `lower309_total`). -/
def lowerW (e : Expr) : WTyped := (lower309 e).getD (.leaf (.const 0))
/-- A deployed source, lowered by the deployed lowering and wrapped as a leaf. -/
def lowerLeaf (e : Expr) : WTyped := .leaf ((correctedLowerFinal e).getD (.const 0))

/-- The two retargeted residual sources (`aux0`, `aux1`). -/
def residualSource309 : Fin 2 → WTyped
  | 0 => lowerW walkCountStep309
  | 1 => lowerW walkAccStep309

def queueNonEmpty309 : WTyped := lowerW walkQueueNonEmpty309
def queueTiling309 : WTyped := lowerW walkQueueTiling309

/-- Degree-two endpoints at 309: positions `1`/`2` retargeted, the other four deployed. -/
def endpoint2_309 : List WTyped :=
  [lowerLeaf finalMaskedWalkLn1, lowerW finalMaskedWalkCount1_309, lowerW finalMaskedWalkOut309,
    lowerLeaf finalAccInit, lowerLeaf finalAccTerminal, lowerLeaf finalLnInit]

/-- The degree-four endpoint at 309 (retargeted). -/
def endpoint4_309 : List WTyped := [lowerW finalMaskedWalkAccInit309]

theorem lower309_total :
    (lower309 walkCountStep309).isSome ∧ (lower309 walkAccStep309).isSome ∧
      (lower309 walkQueueNonEmpty309).isSome ∧ (lower309 walkQueueTiling309).isSome ∧
      (lower309 finalMaskedWalkCount1_309).isSome ∧ (lower309 finalMaskedWalkOut309).isSome ∧
      (lower309 finalMaskedWalkAccInit309).isSome := by
  decide

theorem lowerLeaf_total :
    (correctedLowerFinal finalMaskedWalkLn1).isSome ∧ (correctedLowerFinal finalAccInit).isSome ∧
      (correctedLowerFinal finalAccTerminal).isSome ∧ (correctedLowerFinal finalLnInit).isSome := by
  decide

/-- The four untouched degree-two endpoints are exactly the deployed ones. -/
theorem endpoint2_309_untouched :
    correctedEndpoint2.map WTyped.leaf =
      [lowerLeaf finalMaskedWalkLn1, lowerLeaf finalMaskedWalkCount1,
        lowerLeaf finalMaskedWalkOut, lowerLeaf finalAccInit, lowerLeaf finalAccTerminal,
        lowerLeaf finalLnInit] := by
  decide

/-- `walkLnStep` and `walkLn1` read neither `count` nor `acc`: the 309 substitutions leave them
byte-identical (so `core73` and `ep2₀` are not retargeted). -/
theorem walkLn_untouched :
    Trans.walkLnStep.subst finalWalkSubstInGate309 =
        Trans.walkLnStep.subst ComputeWalkLabel.finalWalkSubstInGate ∧
      Trans.walkLn1.subst finalWalkInitialSubst309 = Trans.walkLn1.subst finalWalkInitialSubst := by
  decide

/-! ## 5. The width-309 gate list -/

def correctedCoreCoord309 {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (i : CorrectedCoreExtGateId) (k : Fin 3) : CoeffExpr F :=
  if i = packedQueueNonEmptyId then compile309 b queueNonEmpty309 k
  else if i = packedQueueTilingId then compile309 b queueTiling309 k
  else correctedCoreCoord b i k

/-- The residual index of an aux position `j ≠ 2`. -/
def aux309Idx (j : CorrectedResidualWitnessId) (h : ¬ j = 2) : Fin 2 :=
  ⟨j.val, by have := j.isLt; have : j.val ≠ 2 := fun h' => h (Fin.ext h'); omega⟩

def correctedAuxCoord309 {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (j : CorrectedResidualWitnessId) (k : Fin 3) : CoeffExpr F :=
  if h : j = 2 then correctedAuxCoord b j k
  else .sub (residualWitnessCoord j k) (compile309 b (residualSource309 (aux309Idx j h)) k)

def correctedCore309 {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  (List.ofFn fun i : CorrectedCoreExtGateId =>
    List.ofFn fun k : Fin 3 => correctedCoreCoord309 b i k).flatten

def correctedAux309 {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  (List.ofFn fun j : CorrectedResidualWitnessId =>
    List.ofFn fun k : Fin 3 => correctedAuxCoord309 b j k).flatten

/-- **The 418 gates of the un-hosted chip**, in the deployed order. -/
def allGates309 {F K : Type*} [Field F] [Field K] [Algebra F K]
    (n : ℕ) (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  finalBaseTransitionGates n ++ correctedCore309 b ++ correctedAux309 b ++
    compileList309 b endpoint2_309 ++ compileList309 b endpoint4_309 ++
    finalEndpointEqualityChecks ++ formRCertificateGates (F := F) ++
    correctedCompileList b formRLamPins ++ computeExpGates (F := F)

@[simp] theorem correctedCore309_length {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) : (correctedCore309 b).length = 246 := by
  simp [correctedCore309]

@[simp] theorem correctedAux309_length {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) : (correctedAux309 b).length = 9 := by
  simp [correctedAux309]

theorem endpoint_lengths309 : endpoint2_309.length = 6 ∧ endpoint4_309.length = 1 := ⟨rfl, rfl⟩

/-- **`s = 418`: no gate is added.** -/
@[simp] theorem allGates309_length {F K : Type*} [Field F] [Field K] [Algebra F K]
    (n : ℕ) (b : Basis (Fin 3) F K) : (allGates309 n b).length = 418 := by
  have h := correctedFinalComputeAllGates_length n b
  simp only [correctedFinalComputeAllGates, List.length_append, correctedCompileList_length]
    at h
  simp only [allGates309, List.length_append, compileList309_length, correctedCompileList_length,
    correctedCore309_length, correctedAux309_length]
  have hc : (correctedCore b).length = 246 := by simp [correctedCore]
  have ha : (correctedAux b).length = 9 := by simp [correctedAux]
  have h2 : correctedEndpoint2.length = 6 := corrected_lowered_counts.2.1
  have h4 : correctedEndpoint4.length = 1 := corrected_lowered_counts.2.2
  rw [hc, ha, h2, h4] at h
  simp only [endpoint2_309, endpoint4_309, List.length_cons, List.length_nil]
  omega

/-! ## 6. Degrees of the retargeted sources (measured; each ≤ the deployed one) -/

/-- **New degrees** of the seven retargeted sources: `aux0 2`, `aux1 3`, `ep2₁ 2`, `ep2₂ 2`,
`ep4 4`, `core76 3`, `core77 2`. -/
theorem retargeted_degrees :
    (residualSource309 0).degree = 2 ∧ (residualSource309 1).degree = 3 ∧
      (lowerW finalMaskedWalkCount1_309).degree = 2 ∧
      (lowerW finalMaskedWalkOut309).degree = 2 ∧
      (lowerW finalMaskedWalkAccInit309).degree = 4 ∧
      queueNonEmpty309.degree = 3 ∧ queueTiling309.degree = 2 := by
  decide

/-- **Deployed degrees** of the same seven sources: `aux0 3`, `aux1 4`, `ep2₁ 2`, `ep2₂ 2`,
`ep4 4`, `core76 4`, `core77 3`. -/
theorem deployed_degrees :
    (correctedFinalResidualSource 0).degree = 3 ∧ (correctedFinalResidualSource 1).degree = 4 ∧
      (lowerLeaf finalMaskedWalkCount1).degree = 2 ∧
      (lowerLeaf finalMaskedWalkOut).degree = 2 ∧
      (lowerLeaf finalMaskedWalkAccInit).degree = 4 ∧
      (correctedFinalExtGate packedQueueNonEmptyId).degree = 4 ∧
      (correctedFinalExtGate packedQueueTilingId).degree = 3 := by
  decide

theorem endpoint2_309_degree : ∀ t ∈ endpoint2_309, t.degree ≤ 2 := by decide
theorem endpoint4_309_degree : ∀ t ∈ endpoint4_309, t.degree ≤ 4 := by decide

theorem correctedCoreCoord309_degree {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (i : CorrectedCoreExtGateId) (k : Fin 3) :
    (correctedCoreCoord309 b i k).degree ≤ 4 := by
  unfold correctedCoreCoord309
  split_ifs
  · exact (compile309_degree_le b _ k).trans (by rw [retargeted_degrees.2.2.2.2.2.1]; omega)
  · exact (compile309_degree_le b _ k).trans (by rw [retargeted_degrees.2.2.2.2.2.2]; omega)
  · exact correctedCoreCoord_degree b i k

theorem correctedAuxCoord309_degree {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (j : CorrectedResidualWitnessId) (k : Fin 3) :
    (correctedAuxCoord309 b j k).degree ≤ 4 := by
  unfold correctedAuxCoord309
  split_ifs with h
  · exact correctedAuxCoord_degree b j k
  · have hs : (residualSource309 (aux309Idx j h)).degree ≤ 4 := by
      have hj : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by
        have := j.isLt; have : (j : ℕ) ≠ 2 := fun h' => h (Fin.ext h'); omega
      rcases hj with hj | hj
      · rw [show aux309Idx j h = 0 from Fin.ext hj, retargeted_degrees.1]; omega
      · rw [show aux309Idx j h = 1 from Fin.ext hj, retargeted_degrees.2.1]; omega
    simp only [CoeffExpr.degree]
    exact max_le (by simp [residualWitnessCoord, CoeffExpr.degree])
      ((compile309_degree_le b _ k).trans hs)

theorem allGates309_degree {F K : Type*} [Field F] [Field K] [Algebra F K]
    (n : ℕ) (b : Basis (Fin 3) F K) : ∀ g ∈ allGates309 n b, g.degree ≤ 4 := by
  intro g hg
  simp only [allGates309, List.mem_append] at hg
  rcases hg with (((((((hb | hc) | ha) | h2) | h4) | heq) | hcert) | hlam) | hexp
  · exact (finalBaseTransitionGates_degree n g hb).trans (by decide)
  · rw [correctedCore309] at hc
    obtain ⟨xs, hxs, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hc
    exact correctedCoreCoord309_degree b i k
  · rw [correctedAux309] at ha
    obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
    exact correctedAuxCoord309_degree b j k
  · exact (compileList309_degree b endpoint2_309 2 endpoint2_309_degree g h2).trans (by decide)
  · exact compileList309_degree b endpoint4_309 4 endpoint4_309_degree g h4
  · exact (finalEndpointEqualityChecks_degree g heq).trans (by decide)
  · exact formRCertificateGates_degree g hcert
  · exact correctedCompileList_degree b formRLamPins 4 formRLamPins_degree g hlam
  · exact (computeExpGates_degree g hexp).trans (by decide)

/-! ## 7. The RAP, the fixed-preprocessing chip and the chip at a tuple -/

def CorrectedFinalComputeRAP309
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  { e := 3
    k := 2
    wRAP := ![297, 12]
    w := 309
    w_eq := by simp [Fin.sum_univ_two]
    h := h
    d := 4
    s := (allGates309 n b).length
    ω := orbit.ω
    β := orbit.βcoset
    I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
    C := fun i => coeffToMv chalVal pubVal ((allGates309 n b).get i)
    C_vars := fun _i => coeffToMv_vars chalVal pubVal _
    C_deg := fun _i => (coeffToMv_totalDegree_le chalVal pubVal _).trans
      (allGates309_degree n b _ (List.get_mem _ _))
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
      rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega }

/-- **The un-hosted compute chip** (width `309`), beside `ProductionNamedComputeRAP`. -/
def ProductionNamedComputeRAP309
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) : FixedPreprocessingRAP F where
  rap := CorrectedFinalComputeRAP309 (n := n) b chalVal pubVal orbit (rowNodeSet nodes)
  rounds_pos := by norm_num [CorrectedFinalComputeRAP309]
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨11 + (j : ℕ), by
          have := j.isLt
          change 11 + (j : ℕ) < 297
          omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

theorem rap309_fingerprint
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    let R := CorrectedFinalComputeRAP309 (n := n) b chalVal pubVal orbit H
    R.w = 309 ∧ R.s = 418 ∧ R.d = 4 ∧ R.k = 2 ∧ R.e = 3 :=
  ⟨rfl, allGates309_length n b, rfl, rfl, rfl⟩

/-- The block identity of the repartitioned schedule at width 309 (`108 + 168 + 33`). -/
theorem block_identity309 : 108 + 168 + 33 = 309 ∧ 297 + 12 = 309 := by decide

end
end Unhosted309
end Nock.NockVMROM.Thm54
