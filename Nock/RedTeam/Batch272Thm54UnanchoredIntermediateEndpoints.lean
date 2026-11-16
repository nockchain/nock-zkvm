/-
  Nock/RedTeam/Batch272Thm54UnanchoredIntermediateEndpoints.lean

  Model:
  `Nock/RedTeam/Batch271Thm54AnchoringReview.lean` §E.

  `OptimizedMemoryGateBasis.degreeOneEndpoints` was `[extVar 46, extVar 49]` — pins on the product
  COLUMNS `46`/`49` (honest values `firstMask · ipre`, `lastMask · icur`) bound to nothing.  Consequently:

  * Their replacements: `shiftedTrace_all_but_anchors` (every committed gate but the two anchors
    still vanishes on the shifted trace — the repair is exactly two gates wide),
    **`repaired_chip_rejects_intermediate_shift`** (for ANY accepted trace and ANY `δ ≠ 0` the
    shifted trace is REJECTED at `P.memoryChip`; no hypothesis on the fold, on `2 ≠ 0`, on any
    other column), **`packageM_intermediate_attack_rejected`** at F97 `(packageM hmoreM)` (`δ = 1`: the
    shifted honest trace has `first · ipre = 1` at row `0`, `last · icur = 1` at row `13`, every
    record field / `ver` / terminal / IO accumulator honest — and the chip rejects it), and
    `packageM_honest_accepted` as the control.  The hostile payoff is
    `OptimizedMemoryHostileAccumulator.hostile_intermediate_anchored`.
  * The shift construction (`roleShiftI`, `shiftedTrace`, `shiftedTrace_values`,
    `shiftedTrace_first_ipre`/`last_icur`) and the invariance lemmas for the fifty sources, the
    twenty-one folds, the base gates, the equality checks and the five mixed gates are kept
    verbatim — they are now the measurement that nothing else moved.

  * For ANY package
    `P`, ANY trace `Qm` with `RAP.SatisfiesWithPreprocessing P.memoryChip Qm`, and ANY `δ : 𝕂`,
    the trace with the `intermediate` roles `27` (`ipre`) and `28` (`icur`) moved by the constant
    `δ` at every row was ACCEPTED by the consumed memory chip.  **No fold-collision hypothesis was
    needed** (unlike `Batch271.attackTrace_accepted`): every one of the fifty sources is
    *invariant* under the shift (`sources_invariant`, still here), so the twenty-one fold gates
    are invariant as linear combinations (`foldAt_congr`).
  * **What the shifted trace commits — `shiftedTrace_values` (still here).**  Roles `27`/`28` are
    `+ δ` at every row; every other `𝕂` role (records `19..26`, `ver` `39`, terminal `40`, the IO
    accumulators `43`/`44`, the masks `47`/`48`, the pins `41`/`46`/`49`), every base column
    (`0..5`), every challenge and every public are unchanged.
  * **The paper's `first · ipre` and `last · icur` on the shifted trace —
    `shiftedTrace_first_ipre`, `shiftedTrace_last_icur` (still here):** `ipre_Qm(0) + δ` at the
    first row and `icur_Qm(last) + δ` at the last row.
  * **Paper-gate answer.**  the paper anchors the `intermediate` aggregator in PROSE only
    ("a global terminal constraint check is required to ensure that the final value of
    intermediate is zero, while its initial value is also constrained to be zero as part of
    the memory table RAP … formal specification … provided in Appendix").  The appendix
    (`:2118-2123`) states only the step `(RLC^γ(mem_record(i)) − β)·(intermediate(i) −
    intermediate(i−1)) = op_3(i) − op_2(i)`; `Algorithm:Memspec` (`:2072`, `:2080`) has only the
    per-state step checks; the resource table (`:1487`, "2·e gates of degree 1") prices two
    degree-one `𝕂` endpoint gates without naming them.  No initial/terminal GATE for
    `intermediate` is written anywhere in the paper; the shadow AIR `Nock/AIR.lean::memIpreInitExpr`
    (`ipre(0)`, degree 1) has that shape but the deployed chip committed `46 = 0`, `49 = 0`.
    The repaired gates are degree `2` because `RAP.Satisfies` holds every gate
    at every row, so the endpoint mask is part of the gate.

  The finding was thus the `LK`/`LM`/`LP` shape a fourth time: honest `46 = firstMask · ipre`,
  `49 = lastMask · icur` (`sampledMemoryRoleValue 9`/`12`) made the honest side blind to it.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.RedTeam.Batch271Thm54AnchoringReview
import Mathlib.LinearAlgebra.Lagrange
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch272

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.MemoryPaperFactorization
open Nock.RedTeam.Batch271 (perturb perturb_eval perturb_off projectTrace_perturb colShift
  colShift_role colShift_base colShift_role_zero ShiftedRowF gather_cur gather_next_on
  gather_next_off gather_chal gather_pub rowEnvK_eq_memorySourceEnv)
open Module
open scoped Polynomial

/-! ## A. Read sets, own instrument -/

section ReadSets

/-- All `(kind, index)` leaves of an `Expr`. -/
def leavesE : Expr → List (VarKind × ℕ)
  | .Const _ => []
  | .Var k i => [(k, i)]
  | .Add x y | .Sub x y | .Mul x y => leavesE x ++ leavesE y
  | .Neg x | .Pow x _ => leavesE x

/-- The base-field leaves of a coefficient expression. -/
def leavesC {F : Type*} : CoeffExpr F → List (VarKind × ℕ)
  | .const _ => []
  | .var k i => [(k, i)]
  | .add x y | .sub x y | .mul x y => leavesC x ++ leavesC y
  | .neg x | .pow x _ => leavesC x

/-- The `𝕂`-level leaves of a mixed gate. -/
def leavesM {F : Type*} : MixedExpr F → List (VarKind × ℕ)
  | .Var k i => [(k, i)]
  | .Lift _ => []
  | .Const _ => []
  | .Scale _ u => leavesM u
  | .Add x y | .Sub x y | .Mul x y => leavesM x ++ leavesM y
  | .Neg x | .Pow x _ => leavesM x

/-- The base-field leaves of a mixed gate (inside `Lift`/`Scale`). -/
def leavesMC {F : Type*} : MixedExpr F → List (VarKind × ℕ)
  | .Var _ _ => []
  | .Lift g => leavesC g
  | .Const _ => []
  | .Scale g u => leavesC g ++ leavesMC u
  | .Add x y | .Sub x y | .Mul x y => leavesMC x ++ leavesMC y
  | .Neg x | .Pow x _ => leavesMC x

/-- The four `𝕂` variables of the `intermediate` aggregator: `ipre` (role `27`) and `icur`
(role `28`) at the current and at the next row. -/
def touched : List (VarKind × ℕ) :=
  [(.traceCur, 27), (.traceCur, 28), (.traceNext, 27), (.traceNext, 28)]

def readsTouched (e : Expr) : Bool := (leavesE e).any (fun v => decide (v ∈ touched))
def readsTouchedM {F : Type*} (g : MixedExpr F) : Bool :=
  (leavesM g).any (fun v => decide (v ∈ touched))

/-- Reads trace role `r` (current or next row). -/
def readsRole (r : ℕ) (e : Expr) : Bool :=
  (leavesE e).any (fun v => (v.1 == .traceCur || v.1 == .traceNext) && v.2 == r)
def readsRoleM {F : Type*} (r : ℕ) (g : MixedExpr F) : Bool :=
  (leavesM g).any (fun v => (v.1 == .traceCur || v.1 == .traceNext) && v.2 == r)

/-- The base columns of roles `27`, `28`, `46` under `col = 6 + 3·role + k`.
Role `49`'s old packing `153..155` is now preprocessing (`rootMask` at `153`,
`dequeueMask` at `154`). -/
def shiftedBaseCols : List ℕ := [87, 88, 89, 90, 91, 92, 144, 145, 146]
def readsShiftedColsC {F : Type*} (g : CoeffExpr F) : Bool :=
  (leavesC g).any (fun v => decide (v.2 ∈ shiftedBaseCols))
def readsShiftedColsMC {F : Type*} (g : MixedExpr F) : Bool :=
  (leavesMC g).any (fun v => decide (v.2 ∈ shiftedBaseCols))

private theorem mem_leavesE_iff_support (e : Expr) (v : VarKind × ℕ) :
    v ∈ leavesE e ↔ v ∈ exprVariableSupport e := by
  induction e with
  | Const _ => simp [leavesE, exprVariableSupport]
  | Var _ _ => simp [leavesE, exprVariableSupport]
  | Add x y ihx ihy | Sub x y ihx ihy | Mul x y ihx ihy =>
    simp [leavesE, exprVariableSupport, ihx, ihy]
  | Neg x ih | Pow x _ ih => simp [leavesE, exprVariableSupport, ih]

private theorem readsTouched_iff (e : Expr) :
    readsTouched e = true ↔ ∃ v ∈ exprVariableSupport e, v ∈ touched := by
  simp [readsTouched, List.any_eq_true, decide_eq_true_eq, mem_leavesE_iff_support]

private theorem readsTouched_eq_of_support {e₁ e₂ : Expr}
    (h : exprVariableSupport e₁ = exprVariableSupport e₂) :
    readsTouched e₁ = readsTouched e₂ := by
  have hiff : readsTouched e₁ = true ↔ readsTouched e₂ = true := by
    simp [readsTouched_iff, h]
  cases h₁ : readsTouched e₁ <;> cases h₂ : readsTouched e₂ <;> simp_all [hiff]

private theorem readsRole_iff (r : ℕ) (e : Expr) :
    readsRole r e = true ↔
      ∃ v ∈ exprVariableSupport e,
        (v.1 == VarKind.traceCur || v.1 == VarKind.traceNext) = true ∧ v.2 == r := by
  simp [readsRole, List.any_eq_true, mem_leavesE_iff_support]

private theorem readsRole_eq_of_support (r : ℕ) {e₁ e₂ : Expr}
    (h : exprVariableSupport e₁ = exprVariableSupport e₂) :
    readsRole r e₁ = readsRole r e₂ := by
  have hiff : readsRole r e₁ = true ↔ readsRole r e₂ = true := by
    simp [readsRole_iff, h]
  cases h₁ : readsRole r e₁ <;> cases h₂ : readsRole r e₂ <;> simp_all [hiff]

/-- Index of `mergedGate 23` (`deltaSource`) in `memoryRowSources`: 5 SV + zinv + 23. -/
private theorem memoryRowSources_delta {K : Type} [Field K] :
    (memoryRowSources (K := K))[29]'(by simp [memoryRowSources_length]) =
      deltaSource (K := K) := by
  have h6 : (memSvExprs ++ [zZinvExprM]).length = 6 := by
    simp [memSvExprs, memSvBoolExprs, allMStates]
  have hlt : 6 ≤ 29 := by simp [h6]
  have h23 : 23 < (mergedMemoryCore (K := K)).length := by
    simp [mergedMemoryCore_length]
  unfold memoryRowSources mergedMemoryConstraints
  rw [List.getElem_map, List.getElem_append_right (as := memSvExprs ++ [zZinvExprM])
    (bs := mergedMemoryCore (K := K)) hlt]
  simp [h6, mergedMemoryCore, mergedCoreOrder, deltaSource]

/-- **Exactly two of the fifty sources read `ipre`/`icur` (current or next row): the `Δ`
class and the chain.**  In particular nothing reads `traceNext 28`.  Agrees with
`MemoryPaperFactorization.intermediate_readers` on a second instrument.  Decided at
`ZMod 31`; the generic membership form is `touched_is_delta_or_chain`. -/
theorem transitionSources_touched :
    (transitionSources (K := ZMod 31)).filter readsTouched =
      [deltaSource (K := ZMod 31), memoryChainSource] := by
  set_option maxRecDepth 100000 in decide

/-- **Since the `LU` repair the Expr endpoint buckets are empty** (the two anchors live in
`paperEndpointGates` as mixed `Scale` gates). -/
theorem endpoints_touched :
    (degreeOneEndpoints ++ degreeThreeEndpoints).filter readsTouched = [] := by
  decide

/-- Roles `46`/`49` are read by no source … -/
theorem role46_49_sources :
    (transitionSources (K := ZMod 31)).filter (fun e => readsRole 46 e || readsRole 49 e) = [] := by
  set_option maxRecDepth 100000 in decide

theorem role46_49_endpoints :
    (degreeOneEndpoints ++ degreeThreeEndpoints).filter (fun e => readsRole 46 e || readsRole 49 e)
      = [] := by
  decide

/-- The anchors read the mask mirrors and `ipre`/`icur` at the current row, nothing else. -/
theorem anchors_leaves :
    leavesE intermediateInitGate = [(.traceCur, 47), (.traceCur, 27)] ∧
      leavesE intermediateTerminalGate = [(.traceCur, 48), (.traceCur, 28)] := by
  decide

variable {F K : Type} [Field F] [Field K] [Algebra F K]

private theorem memoryRow_touched_idx {L : Type} [Field L]
    {n : ℕ} (hn : n < (memoryRowSources (K := L)).length)
    (hr : readsTouched ((memoryRowSources (K := L))[n]'hn) = true) : n = 29 := by
  have hn33 : n < 33 := by simpa [memoryRowSources_length] using hn
  have hn31 : n < (memoryRowSources (K := ZMod 31)).length := by
    simpa [memoryRowSources_length] using hn33
  have hsupp := memoryRowSource_support_carrier (K₁ := L) (K₂ := ZMod 31) n hn hn31
  have hr31 : readsTouched ((memoryRowSources (K := ZMod 31))[n]'hn31) = true := by
    rwa [readsTouched_eq_of_support hsupp] at hr
  have hmem :
      (memoryRowSources (K := ZMod 31))[n]'hn31 ∈
        (transitionSources (K := ZMod 31)).filter readsTouched :=
    List.mem_filter.mpr ⟨by
      simp [transitionSources, List.mem_append, List.getElem_mem], hr31⟩
  rw [transitionSources_touched] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hΔ | hch
  · have h29 : 29 < (memoryRowSources (K := ZMod 31)).length := by
      simp [memoryRowSources_length]
    have hnodup : (memoryRowSources (K := ZMod 31)).Nodup := by
      set_option maxRecDepth 100000 in decide
    have heq := hΔ.trans (memoryRowSources_delta (K := ZMod 31)).symm
    exact (List.Nodup.getElem_inj_iff (l := memoryRowSources (K := ZMod 31)) hnodup).mp heq
  · have : memoryChainSource ∉ memoryRowSources (K := ZMod 31) := by
      set_option maxRecDepth 100000 in decide
    exact (this (hch ▸ List.getElem_mem hn31)).elim

private theorem memoryRow_role46_49_false {L : Type} [Field L]
    {n : ℕ} (hn : n < (memoryRowSources (K := L)).length) :
    readsRole 46 ((memoryRowSources (K := L))[n]'hn) = false ∧
      readsRole 49 ((memoryRowSources (K := L))[n]'hn) = false := by
  have hn33 : n < 33 := by simpa [memoryRowSources_length] using hn
  have hn31 : n < (memoryRowSources (K := ZMod 31)).length := by
    simpa [memoryRowSources_length] using hn33
  have hsupp := memoryRowSource_support_carrier (K₁ := L) (K₂ := ZMod 31) n hn hn31
  have hmem :
      (memoryRowSources (K := ZMod 31))[n]'hn31 ∈ transitionSources (K := ZMod 31) := by
    simp [transitionSources, List.mem_append, List.getElem_mem]
  have hr31 : (readsRole 46 ((memoryRowSources (K := ZMod 31))[n]'hn31) ||
      readsRole 49 ((memoryRowSources (K := ZMod 31))[n]'hn31)) = false := by
    have : (memoryRowSources (K := ZMod 31))[n]'hn31 ∉
        (transitionSources (K := ZMod 31)).filter
          (fun e => readsRole 46 e || readsRole 49 e) := by
      simp [role46_49_sources]
    exact Bool.eq_false_iff.mpr fun htrue => this (List.mem_filter.mpr ⟨hmem, htrue⟩)
  refine ⟨?_, ?_⟩
  · simpa [readsRole_eq_of_support 46 hsupp] using
      (Bool.or_eq_false_iff.mp hr31).1
  · simpa [readsRole_eq_of_support 49 hsupp] using
      (Bool.or_eq_false_iff.mp hr31).2

/-- Generic membership form of `transitionSources_touched`. -/
theorem touched_is_delta_or_chain {e : Expr}
    (he : e ∈ transitionSources (K := K)) (hr : readsTouched e = true) :
    e = deltaSource (K := K) ∨ e = memoryChainSource := by
  simp only [transitionSources, List.mem_append, List.mem_singleton] at he
  rcases he with ((((hrs | rfl) | hb) | ht) | hs)
  · obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hrs
    have hn29 := memoryRow_touched_idx hn hr
    subst hn29
    exact Or.inl memoryRowSources_delta
  · exact Or.inr rfl
  · have hnone : ∀ u ∈ walkBoundarySources, readsTouched u = false := by decide
    exact (Bool.false_ne_true ((hnone e hb).symm.trans hr)).elim
  · have hnone : ∀ u ∈ walkTransitionSources, readsTouched u = false := by decide
    exact (Bool.false_ne_true ((hnone e ht).symm.trans hr)).elim
  · have hnone : ∀ u ∈ sampledSources, readsTouched u = false := by decide
    exact (Bool.false_ne_true ((hnone e hs).symm.trans hr)).elim

/-- Of the four mixed gates only the intermediate chain reads `ipre`/`icur`. -/
theorem mixed_touched :
    (deployedMixedGates (F := F)).filter readsTouchedM = [chainMixed] := rfl

theorem role46_49_mixed :
    (deployedMixedGates (F := F)).filter (fun g => readsRoleM 46 g || readsRoleM 49 g) = [] := rfl

/-- **Roles `46`/`49` are dead**: read by no source, no endpoint gate and no mixed gate. -/
theorem role46_49_anywhere :
    (transitionSources (K := K)).filter (fun e => readsRole 46 e || readsRole 49 e) = [] ∧
      (degreeOneEndpoints ++ degreeThreeEndpoints).filter
        (fun e => readsRole 46 e || readsRole 49 e) = [] ∧
      (deployedMixedGates (F := F)).filter (fun g => readsRoleM 46 g || readsRoleM 49 g) = [] := by
  refine ⟨?_, role46_49_endpoints, role46_49_mixed⟩
  rw [List.filter_eq_nil_iff]
  intro e he
  simp only [transitionSources, List.mem_append, List.mem_singleton] at he
  rcases he with ((((hrs | rfl) | hb) | ht) | hs)
  · obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hrs
    have ⟨h46, h49⟩ := memoryRow_role46_49_false hn
    simp [h46, h49]
  · have hfalse : (readsRole 46 memoryChainSource || readsRole 49 memoryChainSource) = false := by
      decide
    exact fun htrue => Bool.false_ne_true (hfalse.symm.trans htrue)
  · have hnone : ∀ u ∈ walkBoundarySources,
        (readsRole 46 u || readsRole 49 u) = false := by decide
    exact fun htrue => Bool.false_ne_true ((hnone e hb).symm.trans htrue)
  · have hnone : ∀ u ∈ walkTransitionSources,
        (readsRole 46 u || readsRole 49 u) = false := by decide
    exact fun htrue => Bool.false_ne_true ((hnone e ht).symm.trans htrue)
  · have hnone : ∀ u ∈ sampledSources,
        (readsRole 46 u || readsRole 49 u) = false := by decide
    exact fun htrue => Bool.false_ne_true ((hnone e hs).symm.trans htrue)

/-- The mixed gates' base-field leaves read base columns `4`/`5` only. -/
theorem mixed_base_blind :
    (deployedMixedGates (F := F)).filter readsShiftedColsMC = [] := rfl

theorem equalityChecks_touched (b : Basis (Fin 3) F K) :
    (mixedEqualityChecks (F := F) b).filter readsTouchedM = [] := rfl

theorem equalityChecks_role46_49 (b : Basis (Fin 3) F K) :
    (mixedEqualityChecks (F := F) b).filter (fun g => readsRoleM 46 g || readsRoleM 49 g) = [] :=
  rfl

theorem equalityChecks_base_blind (b : Basis (Fin 3) F K) :
    (mixedEqualityChecks (F := F) b).filter readsShiftedColsMC = [] := rfl

/-- The eleven base gates read none of the base columns of roles `27`/`28`/`46`/`49`. -/
theorem baseGates_blind (b : Basis (Fin 3) F K) :
    (baseTransitionGates b).filter readsShiftedColsC = [] := rfl

end ReadSets

/-! ## B. Evaluation depends on the leaves only -/

section Congr

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem evalE_congr (env env' : Env K) :
    ∀ e : Expr, (∀ v ∈ leavesE e, envAt env' v.1 v.2 = envAt env v.1 v.2) →
      e.eval env' = e.eval env
  | .Const _, _ => rfl
  | .Var k i, h => by
      have := h (k, i) (by simp [leavesE])
      cases k <;> simpa [envAt, Expr.eval] using this
  | .Add x y, h => by
      simp only [leavesE, List.mem_append] at h
      simp [Expr.eval, evalE_congr env env' x (fun v hv => h v (Or.inl hv)),
        evalE_congr env env' y (fun v hv => h v (Or.inr hv))]
  | .Sub x y, h => by
      simp only [leavesE, List.mem_append] at h
      simp [Expr.eval, evalE_congr env env' x (fun v hv => h v (Or.inl hv)),
        evalE_congr env env' y (fun v hv => h v (Or.inr hv))]
  | .Mul x y, h => by
      simp only [leavesE, List.mem_append] at h
      simp [Expr.eval, evalE_congr env env' x (fun v hv => h v (Or.inl hv)),
        evalE_congr env env' y (fun v hv => h v (Or.inr hv))]
  | .Neg x, h => by
      simp only [leavesE] at h
      simp [Expr.eval, evalE_congr env env' x h]
  | .Pow x n, h => by
      simp only [leavesE] at h
      simp [Expr.eval, evalE_congr env env' x h]

/-- Read a base-field variable off an environment. -/
def envAtF (env : Env F) : VarKind → ℕ → F
  | .traceCur, i => env.trace i
  | .traceNext, i => env.traceNext i
  | .challenge, i => env.chal i
  | .publicVal, i => env.pub i

theorem evalC_congr (env env' : Env F) :
    ∀ g : CoeffExpr F, (∀ v ∈ leavesC g, envAtF env' v.1 v.2 = envAtF env v.1 v.2) →
      g.eval env' = g.eval env
  | .const _, _ => rfl
  | .var k i, h => by
      have := h (k, i) (by simp [leavesC])
      cases k <;> simpa [envAtF, CoeffExpr.eval] using this
  | .add x y, h => by
      simp only [leavesC, List.mem_append] at h
      simp [CoeffExpr.eval, evalC_congr env env' x (fun v hv => h v (Or.inl hv)),
        evalC_congr env env' y (fun v hv => h v (Or.inr hv))]
  | .sub x y, h => by
      simp only [leavesC, List.mem_append] at h
      simp [CoeffExpr.eval, evalC_congr env env' x (fun v hv => h v (Or.inl hv)),
        evalC_congr env env' y (fun v hv => h v (Or.inr hv))]
  | .mul x y, h => by
      simp only [leavesC, List.mem_append] at h
      simp [CoeffExpr.eval, evalC_congr env env' x (fun v hv => h v (Or.inl hv)),
        evalC_congr env env' y (fun v hv => h v (Or.inr hv))]
  | .neg x, h => by
      simp only [leavesC] at h
      simp [CoeffExpr.eval, evalC_congr env env' x h]
  | .pow x n, h => by
      simp only [leavesC] at h
      simp [CoeffExpr.eval, evalC_congr env env' x h]

end Congr

/-! ## C. The uniform shift of `ipre`/`icur`, one row abstractly -/

section Shift

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable (b : Basis (Fin 3) F K) {n : ℕ}

omit [Field F] [Algebra F K] [FiniteDimensional F K] in
/-- The `Δ` class reads current-row variables only. -/
theorem deltaSource_cur_only {L : Type} [Field L] :
    (leavesE (deltaSource (K := L))).all (fun v => v.1 == VarKind.traceCur) = true := by
  have h31 :
      (leavesE (deltaSource (K := ZMod 31))).all (fun v => v.1 == VarKind.traceCur) = true := by
    set_option maxRecDepth 100000 in decide
  have hsupp := memoryRowSource_support_carrier (K₁ := L) (K₂ := ZMod 31) 29
    (by simp [memoryRowSources_length]) (by simp [memoryRowSources_length])
  rw [memoryRowSources_delta (K := L), memoryRowSources_delta (K := ZMod 31)] at hsupp
  simpa [List.all_eq_true, mem_leavesE_iff_support, hsupp] using h31

/-- The role-level shift: `ipre` (role `27`) and `icur` (role `28`) move by the constant `δ`
at every row; nothing else moves. -/
def roleShiftI (δ : K) : ℕ → Fin n → K := fun r _ => if r = 27 ∨ r = 28 then δ else 0

theorem roleShiftI_off (δ : K) (r : ℕ) (hr : r ≠ 27 ∧ r ≠ 28) (i : Fin n) :
    roleShiftI (n := n) δ r i = 0 := by
  simp [roleShiftI, hr.1, hr.2]

theorem roleShiftI_27 (δ : K) (i : Fin n) : roleShiftI (n := n) δ 27 i = δ := by simp [roleShiftI]
theorem roleShiftI_28 (δ : K) (i : Fin n) : roleShiftI (n := n) δ 28 i = δ := by simp [roleShiftI]

omit [FiniteDimensional F K] in
/-- The column image of the shift vanishes off the six base columns `87..92`. -/
theorem colShift_roleShiftI_off (δ : K) (c : ℕ) (hc : ¬ (87 ≤ c ∧ c < 93)) (i : Fin n) :
    colShift b (roleShiftI δ) c i = 0 := by
  simp only [colShift]
  split_ifs with h6
  · rw [roleShiftI_off δ _ (by omega)]; simp [coord]
  · rfl

variable {envF envF' : Env F} {j : Fin n} (δ : K)
  (h : ShiftedRowF envF envF' (colShift b (roleShiftI δ)) j)
include h

theorem cur_r (r : ℕ) :
    (gatherEnv b memoryCol0 envF').trace r =
      (gatherEnv b memoryCol0 envF).trace r + roleShiftI δ r j :=
  gather_cur b _ h r

theorem cur_off (r : ℕ) (hr : r ≠ 27 ∧ r ≠ 28) :
    (gatherEnv b memoryCol0 envF').trace r = (gatherEnv b memoryCol0 envF).trace r := by
  rw [cur_r b δ h r, roleShiftI_off δ r hr, add_zero]

theorem next_on (hj : (j : ℕ) + 1 < n) (r : ℕ) :
    (gatherEnv b memoryCol0 envF').traceNext r =
      (gatherEnv b memoryCol0 envF).traceNext r + roleShiftI δ r ⟨(j : ℕ) + 1, hj⟩ :=
  gather_next_on b _ h hj r

theorem next_off (r : ℕ) (hr : r ≠ 27 ∧ r ≠ 28) :
    (gatherEnv b memoryCol0 envF').traceNext r = (gatherEnv b memoryCol0 envF).traceNext r :=
  gather_next_off b _ h r (fun i => roleShiftI_off δ r hr i)

theorem chal_eq (r : ℕ) :
    (gatherEnv b memoryCol0 envF').chal r = (gatherEnv b memoryCol0 envF).chal r :=
  gather_chal b _ h r

theorem pub_eq (r : ℕ) :
    (gatherEnv b memoryCol0 envF').pub r = (gatherEnv b memoryCol0 envF).pub r :=
  gather_pub b _ h r

omit [FiniteDimensional F K] in
/-- Base-field columns outside `87..92` are unchanged at this row … -/
theorem baseF_cur (c : ℕ) (hc : ¬ (87 ≤ c ∧ c < 93)) : envF'.trace c = envF.trace c := by
  rw [h.cur, colShift_roleShiftI_off b δ c hc, add_zero]

omit [FiniteDimensional F K] in
/-- … and at the next row. -/
theorem baseF_next (c : ℕ) (hc : ¬ (87 ≤ c ∧ c < 93)) : envF'.traceNext c = envF.traceNext c :=
  h.next_off c (fun i => colShift_roleShiftI_off b δ c hc i)

omit [FiniteDimensional F K] in
theorem envAtF_untouched (v : VarKind × ℕ) (hv : v.2 ∉ shiftedBaseCols) :
    envAtF envF' v.1 v.2 = envAtF envF v.1 v.2 := by
  obtain ⟨k, c⟩ := v
  have hc : ¬ (87 ≤ c ∧ c < 93) := by
    intro hc; apply hv; simp only [shiftedBaseCols, List.mem_cons, List.not_mem_nil, or_false]
    omega
  cases k
  · exact baseF_cur b δ h c hc
  · exact baseF_next b δ h c hc
  · exact h.chal c
  · exact h.pub c

theorem envAt_untouched (v : VarKind × ℕ) (hv : v ∉ touched) :
    envAt (gatherEnv b memoryCol0 envF') v.1 v.2 = envAt (gatherEnv b memoryCol0 envF) v.1 v.2 := by
  obtain ⟨k, r⟩ := v
  cases k
  · have hr : r ≠ 27 ∧ r ≠ 28 := by
      constructor <;> rintro rfl <;> apply hv <;> simp [touched]
    exact cur_off b δ h r hr
  · have hr : r ≠ 27 ∧ r ≠ 28 := by
      constructor <;> rintro rfl <;> apply hv <;> simp [touched]
    exact next_off b δ h r hr
  · exact chal_eq b δ h r
  · exact pub_eq b δ h r

/-- A source reading none of the four `intermediate` variables is invariant. -/
theorem eval_blind (e : Expr) (he : readsTouched e = false) :
    e.eval (gatherEnv b memoryCol0 envF') = e.eval (gatherEnv b memoryCol0 envF) := by
  apply evalE_congr
  intro v hv
  apply envAt_untouched b δ h v
  intro hmem
  have : readsTouched e = true := by
    simp only [readsTouched, List.any_eq_true]
    exact ⟨v, hv, by simpa using hmem⟩
  rw [he] at this
  exact Bool.false_ne_true this

/-- **The `Δ intermediate` class is invariant**: it reads `icur − ipre` at the current row. -/
theorem deltaSource_invariant :
    (deltaSource (K := K)).eval (gatherEnv b memoryCol0 envF') =
      (deltaSource (K := K)).eval (gatherEnv b memoryCol0 envF) := by
  rw [← deltaSource_shift (gatherEnv b memoryCol0 envF) δ]
  apply evalE_congr
  rintro ⟨k, i⟩ hv
  have hk : (k == VarKind.traceCur) = true :=
    List.all_eq_true.mp (deltaSource_cur_only (L := K)) (k, i) hv
  have hk' : k = .traceCur := by simpa using hk
  subst hk'
  simp only [envAt, shiftIntermediate]
  rw [cur_r b δ h i]
  simp only [roleShiftI]
  split_ifs <;> simp

/-- **The chain `(1 − last)·(icur(i) − ipre(i+1))` is invariant**: off the last row both
shifted terms cancel; at the last row it is masked. -/
theorem chainSource_invariant (hlast : (j : ℕ) + 1 = n → (gatherEnv b memoryCol0 envF).trace 48 = 1) :
    memoryChainSource.eval (gatherEnv b memoryCol0 envF') =
      memoryChainSource.eval (gatherEnv b memoryCol0 envF) := by
  simp only [memoryChainSource, notLastE, lastE, Trans.icurChainExpr, Reified.tc, Trans.tn,
    Expr.subst, memoryChainSubst, extVar]
  norm_num [Expr.eval]
  rw [cur_off b δ h 48 (by decide)]
  by_cases hj : (j : ℕ) + 1 < n
  · rw [cur_r b δ h 28, next_on b δ h hj 27, roleShiftI_27, roleShiftI_28]; ring
  · have hl : (j : ℕ) + 1 = n := by have := j.isLt; omega
    rw [hlast hl]; simp

/-- **All fifty sources are invariant under the shift.** -/
theorem sources_invariant (hlast : (j : ℕ) + 1 = n → (gatherEnv b memoryCol0 envF).trace 48 = 1) :
    ∀ e ∈ transitionSources (K := K),
      e.eval (gatherEnv b memoryCol0 envF') = e.eval (gatherEnv b memoryCol0 envF) := by
  intro e he
  by_cases hr : readsTouched e = true
  · rcases touched_is_delta_or_chain he hr with rfl | rfl
    · exact deltaSource_invariant b δ h
    · exact chainSource_invariant b δ h hlast
  · exact eval_blind b δ h e (by simpa using hr)

omit h in
/-- A fold gate is a `𝕂`-linear combination of its bucket's sources with powers of challenge
`6`; it is invariant whenever the sources and that challenge are. -/
theorem foldAt_congr (env env' : Env K) (hchal : env'.chal 6 = env.chal 6)
    (hs : ∀ e ∈ extensionFoldSources (K := K), e.eval env' = e.eval env) (q : Fin 21) :
    (foldAt (K := K) q).eval env' = (foldAt (K := K) q).eval env := by
  simp only [foldAt]
  induction sourceIndices (K := K) with
  | nil => simp [Expr.eval]
  | cons i t ih =>
      simp only [List.foldr_cons]
      split_ifs with hq
      · simp only [Expr.eval]
        rw [ih, hs ((extensionFoldSources (K := K)).get i) (List.get_mem _ _)]
        simp only [foldChallenge, Expr.eval, hchal]
      · exact ih

/-- **The twenty-one committed fold gates are invariant** — no fold-collision hypothesis. -/
theorem foldGates_invariant (hlast : (j : ℕ) + 1 = n → (gatherEnv b memoryCol0 envF).trace 48 = 1) :
    ∀ g ∈ extensionTransitionGates (K := K),
      g.eval (gatherEnv b memoryCol0 envF') = g.eval (gatherEnv b memoryCol0 envF) := by
  intro g hg
  obtain ⟨q, -, rfl⟩ := List.mem_ofFn.mp hg
  exact foldAt_congr _ _ (chal_eq b δ h 6)
    (fun e he => sources_invariant b δ h hlast e
      (extensionFoldSources_subset_transitionSources (K := K) e he)) q

theorem forest_endpoints_invariant :
    ∀ g ∈ degreeOneEndpoints ++ degreeThreeEndpoints,
      g.eval (gatherEnv b memoryCol0 envF') = g.eval (gatherEnv b memoryCol0 envF) := by
  intro g hg
  simp [degreeOneEndpoints, degreeThreeEndpoints] at hg

/-- **The two anchors move**: `first · ipre` by `47 · δ` and `last · icur` by `48 · δ`
(the mask mirrors are unchanged by the shift). -/
theorem anchors_shifted :
    intermediateInitGate.eval (gatherEnv b memoryCol0 envF') =
        intermediateInitGate.eval (gatherEnv b memoryCol0 envF) +
          (gatherEnv b memoryCol0 envF).trace 47 * δ ∧
      intermediateTerminalGate.eval (gatherEnv b memoryCol0 envF') =
        intermediateTerminalGate.eval (gatherEnv b memoryCol0 envF) +
          (gatherEnv b memoryCol0 envF).trace 48 * δ := by
  simp only [intermediateInitGate, intermediateTerminalGate, extVar, Expr.eval]
  rw [cur_off b δ h 47 (by decide), cur_off b δ h 48 (by decide), cur_r b δ h 27, cur_r b δ h 28,
    roleShiftI_27, roleShiftI_28]
  constructor <;> ring

omit [FiniteDimensional F K] in
/-- **The eleven base gates are invariant** (they read base columns `0..5` and roles
`40`, `42`, `43`, `44`). -/
theorem baseGates_invariant :
    ∀ g ∈ baseTransitionGates b, g.eval envF' = g.eval envF := by
  intro g hg
  apply evalC_congr
  intro v hv
  apply envAtF_untouched b δ h v
  intro hmem
  have hg' := List.filter_eq_nil_iff.mp (baseGates_blind b) g hg
  apply hg'
  simp only [readsShiftedColsC, List.any_eq_true]
  exact ⟨v, hv, by simpa using hmem⟩

theorem equalityChecks_invariant :
    ∀ g ∈ equalityChecks b, g.eval envF' = g.eval envF := by
  intro g hg
  simp [equalityChecks] at hg

theorem mixed_invariant (hlast5 : (j : ℕ) + 1 = n → envF.trace 5 = 1) :
    ∀ g ∈ foldedMixedTransitionGates (F := F),
      g.eval (gatherEnv b memoryCol0 envF') envF' = g.eval (gatherEnv b memoryCol0 envF) envF := by
  intro g hg
  simp only [foldedMixedTransitionGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [firstMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval]
    rw [cur_off b δ h 47 (by decide), baseF_cur b δ h 4 (by norm_num)]
  · simp only [lastMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval]
    rw [cur_off b δ h 48 (by decide), baseF_cur b δ h 5 (by norm_num)]
  · simp only [chainMixed, MixedExpr.eval, bcur, CoeffExpr.eval]
    rw [baseF_cur b δ h 5 (by norm_num)]
    by_cases hj : (j : ℕ) + 1 < n
    · rw [cur_r b δ h 28, next_on b δ h hj 27, roleShiftI_27, roleShiftI_28]; ring
    · have hl : (j : ℕ) + 1 = n := by have := j.isLt; omega
      rw [hlast5 hl]; simp
  · simp only [accChainMixed, MixedExpr.eval, bcur, CoeffExpr.eval]
    rw [baseF_cur b δ h 5 (by norm_num), cur_off b δ h 44 (by decide), next_off b δ h 43 (by decide)]
  ·
    -- sampled coins — none of `27`/`28`; blind to the shift.
    simp only [denominatorPinMixed, recordRLC, recordRLCExpr, reqIdxRLCTerm, reqIdxCol, bcur,
      CoeffExpr.eval, MixedExpr.eval, MixedExpr.ofExpr_eval, Expr.eval]
    rw [baseF_cur b δ h 181 (by omega)]
    rw [chal_eq b δ h 4, chal_eq b δ h 5, cur_off b δ h 37 (by decide),
      cur_off b δ h 19 (by decide), cur_off b δ h 20 (by decide), cur_off b δ h 21 (by decide),
      cur_off b δ h 22 (by decide), cur_off b δ h 23 (by decide), cur_off b δ h 24 (by decide),
      cur_off b δ h 25 (by decide), cur_off b δ h 26 (by decide),
      cur_off b δ h 57 (by decide)]
  · simp only [dequeueMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval]
    rw [cur_off b δ h 56 (by decide), baseF_cur b δ h 154 (by omega)]

end Shift

/-! ## D. At the consumed chip `P.memoryChip` -/

noncomputable section Deployed

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
theorem colShift_roleShiftI_ge171 (b : Basis (Fin 3) F K) {n : ℕ} (δ : K) (c : ℕ) (hc : 171 ≤ c)
    (i : Fin n) : colShift b (roleShiftI δ) c i = 0 :=
  colShift_roleShiftI_off b δ c (by omega) i

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
/-- The perturbed source row is a `ShiftedRowF` of the original. -/
theorem shiftedRowF_perturb (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (hinj : Function.Injective nodes) (δ : K)
    {w : ℕ} (hw : w = 182) (Q : Fin w → F[X]) (ω : F) (chal pub : ℕ → F) (j : Fin n)
    (hsucc : ∀ (hj : (j : ℕ) + 1 < n), nodes ⟨(j : ℕ) + 1, hj⟩ = nodes j * ω) :
    ShiftedRowF (envOfTrace Q ω (nodes j) chal pub)
      (envOfTrace (perturb nodes (colShift b (roleShiftI δ)) Q) ω (nodes j) chal pub)
      (colShift b (roleShiftI δ)) j where
  cur c := by
    simp only [envOfTrace]
    split_ifs with hc
    · exact perturb_eval nodes hinj _ Q ⟨c, hc⟩ j
    · rw [colShift_roleShiftI_ge171 b δ c (by omega), add_zero]
  next_on hj c := by
    simp only [envOfTrace]
    split_ifs with hc
    · rw [mul_comm, ← hsucc hj]
      exact perturb_eval nodes hinj _ Q ⟨c, hc⟩ ⟨(j : ℕ) + 1, hj⟩
    · rw [colShift_roleShiftI_ge171 b δ c (by omega), add_zero]
  next_off c h0 := by
    simp only [envOfTrace]
    split_ifs with hc
    · rw [perturb_off nodes _ Q ⟨c, hc⟩ h0]
    · rfl
  chal _ := rfl
  pub _ := rfl

variable (δ : K) (Qm : Fin P.memoryChip.rap.w → F[X])

/-- The column shift of the attack at the package's basis. -/
abbrev shiftCols : ℕ → Fin (rows P) → F := colShift P.optimized.basis (roleShiftI δ)

/-- **The shifted trace**: `Qm` with `ipre` and `icur` (roles `27`, `28`) moved by `δ` at
every row, everything else untouched. -/
def shiftedTrace : Fin P.memoryChip.rap.w → F[X] :=
  perturb P.optimized.memoryNodes (shiftCols P δ) Qm

theorem proj_shiftedTrace :
    projOf P (shiftedTrace P δ Qm) =
      perturb P.optimized.memoryNodes (shiftCols P δ) (projOf P Qm) :=
  projectTrace_perturb _ _ _ _ Qm

theorem rowEnvF_shifted (j : Fin (rows P)) :
    rowEnvF P (shiftedTrace P δ Qm) j =
      envOfTrace (perturb P.optimized.memoryNodes (shiftCols P δ) (projOf P Qm))
        P.optimized.orbit.ω (P.optimized.memoryNodes j) P.optimized.memoryChallenge
        P.optimized.memoryPublic := by
  simp only [rowEnvF, proj_shiftedTrace]

theorem shiftedRow (j : Fin (rows P)) :
    ShiftedRowF (rowEnvF P Qm j) (rowEnvF P (shiftedTrace P δ Qm) j) (shiftCols P δ) j := by
  rw [rowEnvF_shifted]
  have hw : (sourceOf P).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit (rowNodeSet P.optimized.memoryNodes)).1
  exact shiftedRowF_perturb P.optimized.basis P.optimized.memoryNodes
    P.optimized.memoryNodes_injective δ hw (projOf P Qm) _ _ _ j
    (fun hj => P.optimized.memoryOrbitAligned j hj)

variable (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
include hsat

/-- At the last row the preprocessing last-mask (base column `5`) is `1`. -/
theorem last5 (j : Fin (rows P)) (hl : (j : ℕ) + 1 = rows P) : (rowEnvF P Qm j).trace 5 = 1 := by
  rw [(masks_at P Qm hsat j).2, if_pos hl]

/-- The live rejection is
`repaired_chip_rejects_intermediate_shift`. -/
theorem shiftedTrace_all_but_anchors (j : Fin (rows P)) :
    (∀ g ∈ baseTransitionGates P.optimized.basis,
        g.eval (rowEnvF P (shiftedTrace P δ Qm) j) = 0) ∧
    (∀ g ∈ equalityChecks P.optimized.basis,
        g.eval (rowEnvF P (shiftedTrace P δ Qm) j) = 0) ∧
    (∀ g ∈ (memorySourceTemplate P.optimized.basis).extTransition ++
        (memorySourceTemplate P.optimized.basis).extDeg1 ++
        (memorySourceTemplate P.optimized.basis).extDeg3,
        g.eval (rowEnvK P (shiftedTrace P δ Qm) j) = 0) := by
  have h := shiftedRow P δ Qm j
  obtain ⟨hbase, heq, _hext, _hmix⟩ := row_parts P Qm hsat j
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rw [baseGates_invariant P.optimized.basis δ h g hg]
    exact hbase g hg
  · intro g hg
    rw [equalityChecks_invariant P.optimized.basis δ h g hg]
    exact heq g hg
  · intro g hg
    simp [memorySourceTemplate, degreeOneEndpoints, degreeThreeEndpoints] at hg

omit hsat in
/-- **What the shifted trace commits**: roles `27`/`28` are `+ δ` at every row; every other
`𝕂` role (records `19..26`, `ver` `39`, terminal `40`, IO accumulators `43`/`44`, masks
`47`/`48`, pins `41`/`46`/`49`), every base column `0..5`, every challenge and public are
unchanged. -/
theorem shiftedTrace_values :
    (∀ j : Fin (rows P), (rowEnvK P (shiftedTrace P δ Qm) j).trace 27 = (rowEnvK P Qm j).trace 27 + δ) ∧
    (∀ j : Fin (rows P), (rowEnvK P (shiftedTrace P δ Qm) j).trace 28 = (rowEnvK P Qm j).trace 28 + δ) ∧
    (∀ (j : Fin (rows P)) (r : ℕ), r ≠ 27 → r ≠ 28 →
      (rowEnvK P (shiftedTrace P δ Qm) j).trace r = (rowEnvK P Qm j).trace r) ∧
    (∀ (j : Fin (rows P)) (c : ℕ), c < 6 →
      (rowEnvF P (shiftedTrace P δ Qm) j).trace c = (rowEnvF P Qm j).trace c) ∧
    (∀ (j : Fin (rows P)) (r : ℕ), (rowEnvK P (shiftedTrace P δ Qm) j).chal r = (rowEnvK P Qm j).chal r) ∧
    (∀ (j : Fin (rows P)) (r : ℕ), (rowEnvK P (shiftedTrace P δ Qm) j).pub r = (rowEnvK P Qm j).pub r) := by
  refine ⟨fun j => ?_, fun j => ?_, fun j r h27 h28 => ?_, fun j c hc => ?_, fun j r => ?_, fun j r => ?_⟩
  · have h := shiftedRow P δ Qm j
    show (gatherEnv P.optimized.basis memoryCol0 _).trace 27 = _
    rw [cur_r P.optimized.basis δ h 27, roleShiftI_27]
  · have h := shiftedRow P δ Qm j
    show (gatherEnv P.optimized.basis memoryCol0 _).trace 28 = _
    rw [cur_r P.optimized.basis δ h 28, roleShiftI_28]
  · have h := shiftedRow P δ Qm j
    show (gatherEnv P.optimized.basis memoryCol0 _).trace r = _
    exact cur_off P.optimized.basis δ h r ⟨h27, h28⟩
  · exact baseF_cur P.optimized.basis δ (shiftedRow P δ Qm j) c (by omega)
  · exact chal_eq P.optimized.basis δ (shiftedRow P δ Qm j) r
  · exact pub_eq P.optimized.basis δ (shiftedRow P δ Qm j) r

omit hsat in
/-- The paper's `first · ipre` on the shifted trace at
any row: the original value plus `first · δ`. -/
theorem shiftedTrace_intermediateInit (j : Fin (rows P)) :
    (OptimizedMemoryGateBasis.intermediateInit (F := F)).eval (rowEnvK P (shiftedTrace P δ Qm) j)
        (rowEnvF P (shiftedTrace P δ Qm) j) =
      (OptimizedMemoryGateBasis.intermediateInit (F := F)).eval (rowEnvK P Qm j) (rowEnvF P Qm j) +
        algebraMap F K ((rowEnvF P Qm j).trace 4) * δ := by
  have h := shiftedRow P δ Qm j
  simp only [OptimizedMemoryGateBasis.intermediateInit, MixedExpr.eval, bcur, CoeffExpr.eval]
  rw [baseF_cur P.optimized.basis δ h 4 (by norm_num)]
  show algebraMap F K _ * (gatherEnv P.optimized.basis memoryCol0 _).trace 27 = _
  rw [cur_r P.optimized.basis δ h 27, roleShiftI_27]
  ring

omit hsat in
/-- The paper's `last · icur` (`intermediateTerminal`) on the shifted trace at any row: the
original value plus `last · δ`. -/
theorem shiftedTrace_intermediateTerminal (j : Fin (rows P)) :
    (OptimizedMemoryGateBasis.intermediateTerminal (F := F)).eval (rowEnvK P (shiftedTrace P δ Qm) j)
        (rowEnvF P (shiftedTrace P δ Qm) j) =
      (OptimizedMemoryGateBasis.intermediateTerminal (F := F)).eval (rowEnvK P Qm j) (rowEnvF P Qm j) +
        algebraMap F K ((rowEnvF P Qm j).trace 5) * δ := by
  have h := shiftedRow P δ Qm j
  simp only [OptimizedMemoryGateBasis.intermediateTerminal, MixedExpr.eval, bcur, CoeffExpr.eval]
  rw [baseF_cur P.optimized.basis δ h 5 (by norm_num)]
  show algebraMap F K _ * (gatherEnv P.optimized.basis memoryCol0 _).trace 28 = _
  rw [cur_r P.optimized.basis δ h 28, roleShiftI_28]
  ring

/-- **At the first row the shifted trace's `first · ipre` is `ipre_Qm(0) + δ`** — and
`ipre_Qm(0) = 0` at any accepted trace since the repair (`hostile_intermediate_anchored`), so it
is `δ`: `shiftedTrace_first_ipre_eq_delta`. -/
theorem shiftedTrace_first_ipre :
    (OptimizedMemoryGateBasis.intermediateInit (F := F)).eval (rowEnvK P (shiftedTrace P δ Qm) (firstRow P))
        (rowEnvF P (shiftedTrace P δ Qm) (firstRow P)) =
      (rowEnvK P Qm (firstRow P)).trace 27 + δ := by
  rw [shiftedTrace_intermediateInit]
  have h4 : (rowEnvF P Qm (firstRow P)).trace 4 = 1 := by
    rw [(masks_at P Qm hsat (firstRow P)).1, if_pos rfl]
  simp only [OptimizedMemoryGateBasis.intermediateInit, MixedExpr.eval, bcur, CoeffExpr.eval, h4, map_one, one_mul]

/-- **At the last row the shifted trace's `last · icur` is `icur_Qm(last) + δ`.** -/
theorem shiftedTrace_last_icur :
    (OptimizedMemoryGateBasis.intermediateTerminal (F := F)).eval (rowEnvK P (shiftedTrace P δ Qm) (lastRow P))
        (rowEnvF P (shiftedTrace P δ Qm) (lastRow P)) =
      (rowEnvK P Qm (lastRow P)).trace 28 + δ := by
  rw [shiftedTrace_intermediateTerminal]
  have h5 : (rowEnvF P Qm (lastRow P)).trace 5 = 1 := by
    rw [(masks_at P Qm hsat (lastRow P)).2, if_pos (by
      exact Nat.sub_add_cancel P.optimized.family.problem.cfg.memRows_pos)]
  simp only [OptimizedMemoryGateBasis.intermediateTerminal, MixedExpr.eval, bcur, CoeffExpr.eval, h5, map_one, one_mul]

theorem shiftedTrace_first_ipre_eq_delta :
    (OptimizedMemoryGateBasis.intermediateInit (F := F)).eval (rowEnvK P (shiftedTrace P δ Qm) (firstRow P))
        (rowEnvF P (shiftedTrace P δ Qm) (firstRow P)) = δ := by
  rw [shiftedTrace_first_ipre P δ Qm hsat, (hostile_intermediate_anchored P Qm hsat).1, zero_add]

theorem shiftedTrace_last_icur_eq_delta :
    (OptimizedMemoryGateBasis.intermediateTerminal (F := F)).eval (rowEnvK P (shiftedTrace P δ Qm) (lastRow P))
        (rowEnvF P (shiftedTrace P δ Qm) (lastRow P)) = δ := by
  rw [shiftedTrace_last_icur P δ Qm hsat, (hostile_intermediate_anchored P Qm hsat).2, zero_add]

/-- The two paper mixed anchors on the shifted trace at row `j`: `first · (ipre + δ)` and
`last · (icur + δ)`. -/
theorem shiftedTrace_anchors (j : Fin (rows P)) :
    (OptimizedMemoryGateBasis.intermediateInit (F := F)).eval (rowEnvK P (shiftedTrace P δ Qm) j)
        (rowEnvF P (shiftedTrace P δ Qm) j) =
      (OptimizedMemoryGateBasis.intermediateInit (F := F)).eval (rowEnvK P Qm j) (rowEnvF P Qm j) +
        algebraMap F K ((rowEnvF P Qm j).trace 4) * δ ∧
    (OptimizedMemoryGateBasis.intermediateTerminal (F := F)).eval (rowEnvK P (shiftedTrace P δ Qm) j)
        (rowEnvF P (shiftedTrace P δ Qm) j) =
      (OptimizedMemoryGateBasis.intermediateTerminal (F := F)).eval (rowEnvK P Qm j) (rowEnvF P Qm j) +
        algebraMap F K ((rowEnvF P Qm j).trace 5) * δ :=
  ⟨shiftedTrace_intermediateInit P δ Qm j, shiftedTrace_intermediateTerminal P δ Qm j⟩

/-- For ANY trace `P.memoryChip` accepts and ANY `δ ≠ 0`, the
shifted trace is rejected: `intermediateInit` at the first row evaluates to `δ ≠ 0`. -/
theorem repaired_chip_rejects_intermediate_shift (hδ : δ ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing P.memoryChip (shiftedTrace P δ Qm) := by
  intro hsat'
  have hI := mixed_at P (shiftedTrace P δ Qm) hsat' (firstRow P) _
    (intermediateInit_mem P.optimized.basis)
  rw [shiftedTrace_first_ipre_eq_delta P δ Qm hsat] at hI
  exact hδ hI

/-- The same at the last row, through `last · icur`. -/
theorem repaired_chip_rejects_intermediate_shift_last (hδ : δ ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing P.memoryChip (shiftedTrace P δ Qm) := by
  intro hsat'
  have hT := mixed_at P (shiftedTrace P δ Qm) hsat' (lastRow P) _
    (intermediateTerminal_mem P.optimized.basis)
  rw [shiftedTrace_last_icur_eq_delta P δ Qm hsat] at hT
  exact hδ hT

omit hsat in
/-- **Generic form of the repair.**  For every accepted trace and every `δ ≠ 0`: the shifted
trace has BOTH paper endpoints equal to `δ ≠ 0` and is REJECTED. -/
theorem shift_both_endpoints_nonzero_rejected
    (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm) (hδ : δ ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing P.memoryChip (shiftedTrace P δ Qm) ∧
      (OptimizedMemoryGateBasis.intermediateInit (F := F)).eval (rowEnvK P (shiftedTrace P δ Qm) (firstRow P))
        (rowEnvF P (shiftedTrace P δ Qm) (firstRow P)) ≠ 0 ∧
      (OptimizedMemoryGateBasis.intermediateTerminal (F := F)).eval (rowEnvK P (shiftedTrace P δ Qm) (lastRow P))
        (rowEnvF P (shiftedTrace P δ Qm) (lastRow P)) ≠ 0 :=
  ⟨repaired_chip_rejects_intermediate_shift P δ Qm hsat hδ,
   by rw [shiftedTrace_first_ipre_eq_delta P δ Qm hsat]; exact hδ,
   by rw [shiftedTrace_last_icur_eq_delta P δ Qm hsat]; exact hδ⟩

end Deployed

/-! ## E. The F97 instantiation at the real package `(packageM hmoreM)` -/

noncomputable section F97

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.MultiRootServedFixture

set_option maxHeartbeats 2000000

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance fintype97 : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance deq97 : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97 : CharP K97cubic 97 := inferInstance
local instance charRing97 : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable {hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution}
include hmoreM

/-- The honest memory trace of the real F97 package `(packageM hmoreM)` (`memRows = 14`). -/
abbrev honestM : Fin (packageM hmoreM).memoryChip.rap.w → F97[X] := canonicalMemoryTrace (packageM hmoreM)

theorem packageM_memRows : rows (packageM hmoreM) = 15 := rfl
theorem packageM_firstRow_val : ((firstRow (packageM hmoreM) : Fin (rows (packageM hmoreM))) : ℕ) = 0 := rfl
theorem packageM_lastRow_val : ((lastRow (packageM hmoreM) : Fin (rows (packageM hmoreM))) : ℕ) = 14 := rfl

theorem rowEnvF_eq_memoryBaseEnv (Qm : Fin (packageM hmoreM).memoryChip.rap.w → F97[X])
    (i : Fin (rows (packageM hmoreM))) :
    rowEnvF (packageM hmoreM) Qm i = (packageM hmoreM).memoryBaseEnv Qm i := by
  unfold rowEnvF projOf OptimizedFullStrictNockVMROMPackage.memoryBaseEnv
    OptimizedFullStrictNockVMROMPackage.memorySourceTrace
  rfl

/-- **Honest `first · ipre = 0` at every row of `(packageM hmoreM)`'s canonical trace.** -/
theorem packageM_honest_intermediateInit (i : Fin (rows (packageM hmoreM))) :
    (OptimizedMemoryGateBasis.intermediateInit (F := F97)).eval (rowEnvK (packageM hmoreM) honestM i) (rowEnvF (packageM hmoreM) honestM i) = 0 := by
  rw [rowEnvK_eq_memorySourceEnv, canonical_memorySourceEnv, rowEnvF_eq_memoryBaseEnv,
    canonical_memoryBaseEnv]
  exact canonical_intermediateInit (packageM hmoreM).optimized.sampled
    (packageM hmoreM).optimized.memoryNodes
    (packageM hmoreM).optimized.memoryNodes_injective (packageM hmoreM).optimized.basis
    (packageM hmoreM).optimized.memoryChallenge (packageM hmoreM).optimized.memoryPublic (packageM hmoreM).optimized.orbit
    i

/-- **Honest `last · icur = 0` at every row of `(packageM hmoreM)`'s canonical trace.** -/
theorem packageM_honest_intermediateTerminal (i : Fin (rows (packageM hmoreM))) :
    (OptimizedMemoryGateBasis.intermediateTerminal (F := F97)).eval (rowEnvK (packageM hmoreM) honestM i) (rowEnvF (packageM hmoreM) honestM i) = 0 := by
  rw [rowEnvK_eq_memorySourceEnv, canonical_memorySourceEnv, rowEnvF_eq_memoryBaseEnv,
    canonical_memoryBaseEnv]
  exact canonical_intermediateTerminal (packageM hmoreM).optimized.sampled
    (packageM hmoreM).optimized.memoryNodes
    (packageM hmoreM).optimized.memoryNodes_injective (packageM hmoreM).optimized.basis
    (packageM hmoreM).optimized.memoryChallenge (packageM hmoreM).optimized.memoryPublic (packageM hmoreM).optimized.orbit
    (packageM hmoreM).optimized.pairedRecordLayout (packageM hmoreM).optimized.sampled.honestVer
    MultiRootServedFixture.execS_cprimeCoherent i

/-- Honest `ipre(0) = 0` and `icur(13) = 0` at `(packageM hmoreM)`. -/
theorem packageM_honest_endpoints :
    (rowEnvK (packageM hmoreM) honestM (firstRow (packageM hmoreM))).trace 27 = 0 ∧
      (rowEnvK (packageM hmoreM) honestM (lastRow (packageM hmoreM))).trace 28 = 0 := by
  have hsat := canonicalMemoryTrace_satisfies (packageM hmoreM) hmoreM
      MultiRootServedFixture.execS_cprimeCoherent
  constructor
  · have h0 := packageM_honest_intermediateInit (firstRow (packageM hmoreM))
    have h4 : (rowEnvF (packageM hmoreM) honestM (firstRow (packageM hmoreM))).trace 4 = 1 := by
      rw [(masks_at (packageM hmoreM) honestM hsat _).1, if_pos rfl]
    simpa [OptimizedMemoryGateBasis.intermediateInit, MixedExpr.eval, bcur, CoeffExpr.eval, h4] using h0
  · have h0 := packageM_honest_intermediateTerminal (lastRow (packageM hmoreM))
    have h5 : (rowEnvF (packageM hmoreM) honestM (lastRow (packageM hmoreM))).trace 5 = 1 := by
      rw [(masks_at (packageM hmoreM) honestM hsat _).2]
      have hlast : ((lastRow (packageM hmoreM) : ℕ) + 1 = rows (packageM hmoreM)) := by
        rw [packageM_lastRow_val, packageM_memRows]
      rw [if_pos hlast]
    simpa [OptimizedMemoryGateBasis.intermediateTerminal, MixedExpr.eval, bcur, CoeffExpr.eval, h5] using h0

/-- **The `LR` §3 witness at a real package, `δ = 1` — REJECTED since the `LU` repair.**  The shifted trace still commits
what it did — the paper's `first · ipre` at row `0` IS `1` and its `last · icur` at row `13` IS
`1` (the honest values are `0`), every other `𝕂` role, base column, challenge and public honest —
and the repaired chip **rejects** it (`repaired_chip_rejects_intermediate_shift`:
`intermediateInitGate` at row `0` reads `1 ≠ 0`). -/
theorem packageM_intermediate_attack_rejected :
    ¬ RAP.SatisfiesWithPreprocessing (packageM hmoreM).memoryChip (shiftedTrace (packageM hmoreM) 1 honestM) ∧
    (OptimizedMemoryGateBasis.intermediateInit (F := F97)).eval
        (rowEnvK (packageM hmoreM) (shiftedTrace (packageM hmoreM) 1 honestM) (firstRow (packageM hmoreM)))
        (rowEnvF (packageM hmoreM) (shiftedTrace (packageM hmoreM) 1 honestM) (firstRow (packageM hmoreM))) = 1 ∧
    (OptimizedMemoryGateBasis.intermediateTerminal (F := F97)).eval
        (rowEnvK (packageM hmoreM) (shiftedTrace (packageM hmoreM) 1 honestM) (lastRow (packageM hmoreM)))
        (rowEnvF (packageM hmoreM) (shiftedTrace (packageM hmoreM) 1 honestM) (lastRow (packageM hmoreM))) = 1 ∧
    (∀ (j : Fin (rows (packageM hmoreM))) (r : ℕ), r ≠ 27 → r ≠ 28 →
      (rowEnvK (packageM hmoreM) (shiftedTrace (packageM hmoreM) 1 honestM) j).trace r =
        (rowEnvK (packageM hmoreM) honestM j).trace r) ∧
    (∀ (j : Fin (rows (packageM hmoreM))) (c : ℕ), c < 6 →
      (rowEnvF (packageM hmoreM) (shiftedTrace (packageM hmoreM) 1 honestM) j).trace c =
        (rowEnvF (packageM hmoreM) honestM j).trace c) := by
  have hsat := canonicalMemoryTrace_satisfies (packageM hmoreM) hmoreM
      MultiRootServedFixture.execS_cprimeCoherent
  obtain ⟨h27, h28⟩ := packageM_honest_endpoints
  refine ⟨repaired_chip_rejects_intermediate_shift (packageM hmoreM) 1 honestM hsat one_ne_zero, ?_, ?_,
    (shiftedTrace_values (packageM hmoreM) 1 honestM).2.2.1, (shiftedTrace_values (packageM hmoreM) 1 honestM).2.2.2.1⟩
  · rw [shiftedTrace_first_ipre (packageM hmoreM) 1 honestM hsat, h27, zero_add]
  · rw [shiftedTrace_last_icur (packageM hmoreM) 1 honestM hsat, h28, zero_add]

/-- The honest trace itself is accepted (non-vacuity of the rejection). -/
theorem packageM_honest_accepted :
    RAP.SatisfiesWithPreprocessing (packageM hmoreM).memoryChip honestM :=
  canonicalMemoryTrace_satisfies (packageM hmoreM) hmoreM
      MultiRootServedFixture.execS_cprimeCoherent

/-- The hostile anchor at `(packageM hmoreM)`, read off acceptance alone (agrees with
`packageM_honest_endpoints`, which went through the canonical construction). -/
theorem packageM_hostile_anchored :
    (rowEnvK (packageM hmoreM) honestM (firstRow (packageM hmoreM))).trace 27 = 0 ∧
      (rowEnvK (packageM hmoreM) honestM (lastRow (packageM hmoreM))).trace 28 = 0 :=
  hostile_intermediate_anchored (packageM hmoreM) honestM (canonicalMemoryTrace_satisfies
      (packageM hmoreM) hmoreM MultiRootServedFixture.execS_cprimeCoherent)

end F97

end Nock.RedTeam.Batch272

#print axioms Nock.RedTeam.Batch272.transitionSources_touched
#print axioms Nock.RedTeam.Batch272.endpoints_touched
#print axioms Nock.RedTeam.Batch272.role46_49_sources
#print axioms Nock.RedTeam.Batch272.role46_49_endpoints
#print axioms Nock.RedTeam.Batch272.mixed_touched
#print axioms Nock.RedTeam.Batch272.baseGates_blind
#print axioms Nock.RedTeam.Batch272.sources_invariant
#print axioms Nock.RedTeam.Batch272.foldGates_invariant
#print axioms Nock.RedTeam.Batch272.role46_49_anywhere
#print axioms Nock.RedTeam.Batch272.shiftedTrace_all_but_anchors
#print axioms Nock.RedTeam.Batch272.shiftedTrace_anchors
#print axioms Nock.RedTeam.Batch272.repaired_chip_rejects_intermediate_shift
#print axioms Nock.RedTeam.Batch272.repaired_chip_rejects_intermediate_shift_last
#print axioms Nock.RedTeam.Batch272.shiftedTrace_values
#print axioms Nock.RedTeam.Batch272.shiftedTrace_first_ipre
#print axioms Nock.RedTeam.Batch272.shiftedTrace_last_icur
#print axioms Nock.RedTeam.Batch272.shift_both_endpoints_nonzero_rejected
#print axioms Nock.RedTeam.Batch272.packageM_honest_endpoints
#print axioms Nock.RedTeam.Batch272.packageM_intermediate_attack_rejected
#print axioms Nock.RedTeam.Batch272.packageM_honest_accepted
#print axioms Nock.RedTeam.Batch272.packageM_hostile_anchored
