import Nock.NockVMROM.Thm54.VclL.Compute.ChipQ7
import Nock.NockVMROM.Thm54.VclL.Compute.RowDecode

/-!
# `V_comp` at the Q7 chip through the PATCHED ROW

.

The Q7 chip no longer constrains roles `54`/`55` (`ln_prev`/`ln`) or reads challenge slots `0`
(`α`) / `9` (`λ`).  `V_comp`'s timestamp clauses read them through the decoder
(`computeTraceSubst 74 = ln_prev · chal 0`, `mr2Field 7` / `mr3Field 7`).  The patched row
`lnPatch env` sets roles `54`/`55` (current and next) and challenges `0`/`9` to `0`, so every
decoded timestamp is `0`:

* With `kept_no_ln` this
  carries every Q7 obligation from the row to the patched row (`VclSourceObligationsQ7.lnPatch`).
* **the deleted per-state recurrences vanish** at the patched row (`deleted_rowLocal_vanish`: core
  `50`, `58`, `65` are `0` there by the syntactic check `zeroAt`, sound by `zeroAt_eval`).
* hence the 72 row-local packed gates hold at the patched row and **`q7_obligations_vcomp`**:
  the patched row is `V_comp` (`VcompAt (lnPatch (gather …))`); at the chip,
  **`computeChipVCLQ7_row_vcomp`** and **`computeChipVCLQ7_lookup_binds_head`**.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open scoped Polynomial
open Polynomial
open Nock Nock.Reified Nock.Framework Nock.Framework.Reify
open Nock.ComputeTable
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeFinal hiding residualWitnessRole ResidualWitnessId
  FinalExtensionColumn
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering hiding finalExtCoordIndex
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead
open Module

set_option maxRecDepth 300000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The patched row -/

section patch
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The timestamp role / coin predicates of the read set. -/
def lnRole (i : Fin 63) : Prop := i.val = 54 ∨ i.val = 55
def lnChal (i : Fin 12) : Prop := i.val = 0 ∨ i.val = 9

instance (i : Fin 63) : Decidable (lnRole i) := by unfold lnRole; infer_instance
instance (i : Fin 12) : Decidable (lnChal i) := by unfold lnChal; infer_instance

/-- **The patched row**: roles `54`/`55` (current and next) and challenges `0` (`α`) / `9` (`λ`)
set to `0`; everything else unchanged. -/
def lnPatch (env : CorrectedFinalTypedEnv F K) : CorrectedFinalTypedEnv F K :=
  { env with
    extTrace := fun i => if lnRole i then 0 else env.extTrace i
    extTraceNext := fun i => if lnRole i then 0 else env.extTraceNext i
    chal := fun i => if lnChal i then 0 else env.chal i }

def lnPatch309 (env : Env309 F K) : Env309 F K := { env with base := lnPatch env.base }

/-- The Prop form of "the instrument finds no timestamp read". -/
def NoLnT (t : CorrectedFinalTypedExpr) : Prop :=
  (∀ r ∈ roles t, r ≠ 54 ∧ r ≠ 55) ∧ ∀ s ∈ chals t, s ≠ 0 ∧ s ≠ 9

def NoLnW (t : WTyped) : Prop :=
  (∀ r ∈ wRoles t, r ≠ 54 ∧ r ≠ 55) ∧ ∀ s ∈ wChals t, s ≠ 0 ∧ s ≠ 9

theorem noLnT_of_touches {t : CorrectedFinalTypedExpr} (h : touchesT t = false) : NoLnT t := by
  simp only [touchesT, Bool.or_eq_false_iff, List.any_eq_false, decide_eq_true_eq] at h
  refine ⟨fun r hr => ?_, fun s hs => ?_⟩
  · have := h.1 r hr; omega
  · have := h.2 s hs; omega

theorem noLnW_of_touches {t : WTyped} (h : touchesW t = false) : NoLnW t := by
  simp only [touchesW, Bool.or_eq_false_iff, List.any_eq_false, decide_eq_true_eq] at h
  refine ⟨fun r hr => ?_, fun s hs => ?_⟩
  · have := h.1 r hr; omega
  · have := h.2 s hs; omega

theorem NoLnT.left {x y : CorrectedFinalTypedExpr} (h : (∀ r ∈ roles x ++ roles y, r ≠ 54 ∧ r ≠ 55) ∧
    ∀ s ∈ chals x ++ chals y, s ≠ 0 ∧ s ≠ 9) : NoLnT x ∧ NoLnT y :=
  ⟨⟨fun r hr => h.1 r (List.mem_append_left _ hr), fun s hs => h.2 s (List.mem_append_left _ hs)⟩,
    ⟨fun r hr => h.1 r (List.mem_append_right _ hr), fun s hs => h.2 s (List.mem_append_right _ hs)⟩⟩

/-- **Read-set congruence (typed)**: a source free of the timestamp read set has the same value at
the patched row. -/
theorem evalT_lnPatch (env : CorrectedFinalTypedEnv F K) :
    ∀ t : CorrectedFinalTypedExpr, NoLnT t → t.eval (lnPatch env) = t.eval env
  | .extCur i, h => by
      have := h.1 i.val (by simp [roles])
      simp only [CorrectedFinalTypedExpr.eval, lnPatch, lnRole]
      rw [if_neg (by omega)]
  | .extNext i, h => by
      have := h.1 i.val (by simp [roles])
      simp only [CorrectedFinalTypedExpr.eval, lnPatch, lnRole]
      rw [if_neg (by omega)]
  | .challenge i, h => by
      have := h.2 i.val (by simp [chals])
      simp only [CorrectedFinalTypedExpr.eval, lnPatch, lnChal]
      rw [if_neg (by omega)]
  | .lamPow _, h => absurd rfl (h.2 9 (by simp [chals])).2
  | .add x y, h => by
      obtain ⟨hx, hy⟩ := NoLnT.left h
      simp only [CorrectedFinalTypedExpr.eval, evalT_lnPatch env x hx, evalT_lnPatch env y hy]
  | .sub x y, h => by
      obtain ⟨hx, hy⟩ := NoLnT.left h
      simp only [CorrectedFinalTypedExpr.eval, evalT_lnPatch env x hx, evalT_lnPatch env y hy]
  | .mul x y, h => by
      obtain ⟨hx, hy⟩ := NoLnT.left h
      simp only [CorrectedFinalTypedExpr.eval, evalT_lnPatch env x hx, evalT_lnPatch env y hy]
  | .neg x, h => by simp only [CorrectedFinalTypedExpr.eval, evalT_lnPatch env x h]
  | .pow x n, h => by simp only [CorrectedFinalTypedExpr.eval, evalT_lnPatch env x h]
  | .baseCur _, _ => rfl
  | .baseNext _, _ => rfl
  | .extensionPublic _, _ => rfl
  | .scalarPublic _, _ => rfl
  | .const _, _ => rfl
  | .certBase _, _ => rfl
  | .certExt _, _ => rfl
  | .expCur, _ => rfl

theorem NoLnW.left {x y : WTyped} (h : (∀ r ∈ wRoles x ++ wRoles y, r ≠ 54 ∧ r ≠ 55) ∧
    ∀ s ∈ wChals x ++ wChals y, s ≠ 0 ∧ s ≠ 9) : NoLnW x ∧ NoLnW y :=
  ⟨⟨fun r hr => h.1 r (List.mem_append_left _ hr), fun s hs => h.2 s (List.mem_append_left _ hs)⟩,
    ⟨fun r hr => h.1 r (List.mem_append_right _ hr), fun s hs => h.2 s (List.mem_append_right _ hs)⟩⟩

/-- **Read-set congruence (width 309)**. -/
theorem evalW_lnPatch (env : Env309 F K) :
    ∀ t : WTyped, NoLnW t → t.eval (lnPatch309 env) = t.eval env
  | .leaf t, h => evalT_lnPatch env.base t h
  | .wCur _, _ => rfl
  | .wNext _, _ => rfl
  | .add x y, h => by
      obtain ⟨hx, hy⟩ := NoLnW.left h
      simp only [WTyped.eval, evalW_lnPatch env x hx, evalW_lnPatch env y hy]
  | .sub x y, h => by
      obtain ⟨hx, hy⟩ := NoLnW.left h
      simp only [WTyped.eval, evalW_lnPatch env x hx, evalW_lnPatch env y hy]
  | .mul x y, h => by
      obtain ⟨hx, hy⟩ := NoLnW.left h
      simp only [WTyped.eval, evalW_lnPatch env x hx, evalW_lnPatch env y hy]
  | .neg x, h => by simp only [WTyped.eval, evalW_lnPatch env x h]
  | .pow x n, h => by simp only [WTyped.eval, evalW_lnPatch env x h]

theorem lnPatch_extTrace_residual (env : CorrectedFinalTypedEnv F K) (j : CorrectedResidualWitnessId) :
    (lnPatch env).extTrace (residualWitnessRole j) = env.extTrace (residualWitnessRole j) := by
  have := j.isLt
  simp only [lnPatch, lnRole, residualWitnessRole]
  rw [if_neg (by omega)]

/-- **The core position values** of every position the instrument clears are unchanged. -/
theorem coreSemValue309_lnPatch (env : Env309 F K) (i : CorrectedCoreExtGateId)
    (h : coreTouches i = false) : coreSemValue309 (lnPatch309 env) i = coreSemValue309 env i := by
  unfold coreTouches at h
  unfold coreSemValue309
  by_cases h1 : i = packedQueueNonEmptyId
  · rw [if_pos h1] at h; rw [if_pos h1, if_pos h1]
    exact evalW_lnPatch env _ (noLnW_of_touches h)
  rw [if_neg h1] at h; rw [if_neg h1, if_neg h1]
  by_cases h2 : i = packedQueueTilingId
  · rw [if_pos h2] at h; rw [if_pos h2, if_pos h2]
    exact evalW_lnPatch env _ (noLnW_of_touches h)
  rw [if_neg h2] at h; rw [if_neg h2, if_neg h2]
  unfold correctedCoreSemanticValue
  by_cases h3 : i = packedWalkCountId
  · rw [if_pos h3, if_pos h3]
    simp only [notLastScalar]
    rw [show (lnPatch309 env).base = lnPatch env.base from rfl, lnPatch_extTrace_residual]
    rfl
  rw [if_neg h3, if_neg h3]; rw [if_neg h3] at h
  by_cases h4 : i = packedWalkAccId
  · rw [if_pos h4, if_pos h4]
    simp only [notLastScalar]
    rw [show (lnPatch309 env).base = lnPatch env.base from rfl, lnPatch_extTrace_residual]
    rfl
  rw [if_neg h4, if_neg h4]; rw [if_neg h4] at h
  by_cases h5 : i = packedChainId
  · rw [if_pos h5, if_pos h5]; rw [if_pos h5] at h
    exact evalT_lnPatch env.base _ (noLnT_of_touches h)
  rw [if_neg h5, if_neg h5]; rw [if_neg h5] at h
  have ht := evalT_lnPatch env.base _ (noLnT_of_touches h)
  by_cases h6 : i = packedLnChainId ∨ i = packedWalkLnId
  · rw [if_pos h6, if_pos h6]
    simp only [notLastScalar]
    exact congrArg _ ht
  · rw [if_neg h6, if_neg h6]
    exact ht

/-- **Positions `74`/`75` MEASURED** (the instrument's `coreTouches` sets them `false` by hand):
their semantic values (`notLast · role 58` / `notLast · role 59`) are unchanged by the patch,
proved from `correctedCoreSemanticValue` without `coreTouches`. -/
theorem walkCountAcc_lnPatch (env : Env309 F K) :
    ∀ i ∈ [packedWalkCountId, packedWalkAccId],
      coreSemValue309 (lnPatch309 env) i = coreSemValue309 env i := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  have hq1 : i ≠ packedQueueNonEmptyId := by rcases hi with rfl | rfl <;> decide
  have hq2 : i ≠ packedQueueTilingId := by rcases hi with rfl | rfl <;> decide
  unfold coreSemValue309 correctedCoreSemanticValue
  rw [if_neg hq1, if_neg hq1, if_neg hq2, if_neg hq2]
  rcases hi with rfl | rfl
  · rw [if_pos rfl, if_pos rfl]
    simp only [notLastScalar]
    rw [show (lnPatch309 env).base = lnPatch env.base from rfl, lnPatch_extTrace_residual]
    rfl
  · rw [if_neg (show packedWalkAccId ≠ packedWalkCountId by decide),
      if_neg (show packedWalkAccId ≠ packedWalkCountId by decide), if_pos rfl, if_pos rfl]
    simp only [notLastScalar]
    rw [show (lnPatch309 env).base = lnPatch env.base from rfl, lnPatch_extTrace_residual]
    rfl

/-- The residual roles those positions read are `58`/`59`, outside `{54, 55}`. -/
theorem residualRoles_measured :
    (residualWitnessRole 0).val = 58 ∧ (residualWitnessRole 1).val = 59 ∧
      packedWalkCountId.val = 74 ∧ packedWalkAccId.val = 75 := ⟨rfl, rfl, rfl, rfl⟩

/-- The aux positions are unchanged. -/
theorem auxSemValue309_lnPatch (env : Env309 F K) (j : CorrectedResidualWitnessId) :
    auxSemValue309 (lnPatch309 env) j = auxSemValue309 env j := by
  unfold auxSemValue309
  split_ifs with h
  · subst h
    exact evalT_lnPatch env.base _ (noLnT_of_touches kept_no_ln.2.2.1)
  · rw [show (lnPatch309 env).base = lnPatch env.base from rfl, lnPatch_extTrace_residual,
      evalW_lnPatch env _ (noLnW_of_touches (kept_no_ln.2.1 _))]

end patch

/-! ## 2. The Q7 source language -/

section obligations
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **The Q7 source obligations** of one row (`VclSourceObligations` minus the deleted gates). -/
structure VclSourceObligationsQ7 (n : ℕ) (env : Env309 F K) (envF : Env F) : Prop where
  base15 : ∀ g ∈ finalBaseTransitionGates n, g.eval envF = 0
  extensionCore : ∀ i ∈ keptCoreIdsQ7, coreSemValue309 env i = 0
  residualAux : ∀ j : CorrectedResidualWitnessId, auxSemValue309 env j = 0
  endpointDegreeTwo : ∀ t ∈ endpoint2Q7, t.eval env = 0
  endpointDegreeFour : ∀ t ∈ endpoint4_309, t.eval env = 0
  selectorEquality2 : ∀ g ∈ finalEndpointEqualityChecks, g.eval envF = 0

/-- Positive control: the VCL obligations restrict to the Q7 ones. -/
theorem VclSourceObligationsQ7.ofVcl {n : ℕ} {env : Env309 F K} {envF : Env F}
    (h : VclSourceObligations n env envF) : VclSourceObligationsQ7 n env envF :=
  ⟨h.base15, fun i hi => h.extensionCore i (keptCoreIdsQ7_sub i hi), h.residualAux,
    fun t ht => h.endpointDegreeTwo t (endpoint2Q7_sub t ht), h.endpointDegreeFour,
    h.selectorEquality2⟩

/-- **The Q7 obligations survive the patch** (`kept_no_ln`). -/
theorem VclSourceObligationsQ7.lnPatch {n : ℕ} {env : Env309 F K} {envF : Env F}
    (h : VclSourceObligationsQ7 n env envF) : VclSourceObligationsQ7 n (lnPatch309 env) envF :=
  ⟨h.base15,
    fun i hi => (coreSemValue309_lnPatch env i (kept_no_ln.1 i hi)).trans (h.extensionCore i hi),
    fun j => (auxSemValue309_lnPatch env j).trans (h.residualAux j),
    fun t ht => (evalW_lnPatch env t (noLnW_of_touches (kept_no_ln.2.2.2.1 t ht))).trans
      (h.endpointDegreeTwo t ht),
    fun t ht => (evalW_lnPatch env t (noLnW_of_touches (kept_no_ln.2.2.2.2 t ht))).trans
      (h.endpointDegreeFour t ht),
    h.selectorEquality2⟩

variable [FiniteDimensional F K]

/-- The kept Q7 gates at a 309-shaped row give the Q7 obligations at its gather. -/
theorem VclSourceObligationsQ7.of_kept (n : ℕ) (b : Basis (Fin 3) F K) (envF : Env F)
    (h : ∀ g ∈ keptGatesQ7 n b, g.eval envF = 0) :
    VclSourceObligationsQ7 n (gather309 b envF) envF := by
  have henv := isCoordEnv309_gather b envF
  simp only [keptGatesQ7, List.forall_mem_append] at h
  obtain ⟨⟨⟨⟨⟨hb, hc⟩, ha⟩, h2⟩, h4⟩, heq⟩ := h
  refine ⟨hb, ?_, (aux309_eval_iff b _ envF henv).1 ha,
    (compileList309_eval_iff b _ envF henv endpoint2Q7).1 h2,
    (compileList309_eval_iff b _ envF henv endpoint4_309).1 h4, heq⟩
  intro i hi
  rw [eq_iff_coords_eq b (coreSemValue309 _ i) 0]
  intro k
  rw [coord_zero' b k, ← coreCoord309_eval b _ envF henv i k]
  apply hc
  simp only [correctedCoreVCLQ7, List.mem_flatten, List.mem_map]
  exact ⟨_, ⟨i, hi, rfl⟩, List.mem_ofFn.mpr ⟨k, rfl⟩⟩

/-- Acceptance of the Q7 gates at a VCL row gives the kept Q7 gates at the pull-back. -/
theorem keptGatesQ7_of_vclGatesQ7 (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) (envV : Env F)
    (h : ∀ g ∈ vclGatesQ7 n b γc ρc, g.eval envV = 0) :
    ∀ g ∈ keptGatesQ7 n b, g.eval (pullEnv envV) = 0 := by
  intro g hg
  have hr := h (reindexE g) (by
    simp only [vclGatesQ7, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨g, hg, rfl⟩)))))
  rwa [eval_reindexE g (pullEnv envV) envV (keptGates309_colsIn n b g (keptGatesQ7_sub n b g hg))
    (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl] at hr

/-- **Acceptance of the Q7 gates at a VCL row gives the Q7 obligations** at the gathered
pull-back. -/
theorem VclSourceObligationsQ7.of_vclGatesQ7 (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ)
    (envV : Env F) (h : ∀ g ∈ vclGatesQ7 n b γc ρc, g.eval envV = 0) :
    VclSourceObligationsQ7 n (gather309 b (pullEnv envV)) (pullEnv envV) :=
  VclSourceObligationsQ7.of_kept n b _ (keptGatesQ7_of_vclGatesQ7 n b γc ρc envV h)

end obligations

/-! ## 3. The deleted recurrences vanish at the patched row -/

section zero
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- A syntactic sufficient condition for "`0` at every patched row". -/
def zeroAt : CorrectedFinalTypedExpr → Bool
  | .extCur i | .extNext i => i.val == 54 || i.val == 55
  | .challenge i => i.val == 0 || i.val == 9
  | .const c => c == 0
  | .add x y | .sub x y => zeroAt x && zeroAt y
  | .mul x y => zeroAt x || zeroAt y
  | .neg x => zeroAt x
  | .pow x n => zeroAt x && 0 < n
  | _ => false

theorem zeroAt_eval (env : CorrectedFinalTypedEnv F K) :
    ∀ t : CorrectedFinalTypedExpr, zeroAt t = true → t.eval (lnPatch env) = 0
  | .extCur i, h => by
      simp only [zeroAt, Bool.or_eq_true, beq_iff_eq] at h
      simp only [CorrectedFinalTypedExpr.eval, lnPatch, lnRole, if_pos h]
  | .extNext i, h => by
      simp only [zeroAt, Bool.or_eq_true, beq_iff_eq] at h
      simp only [CorrectedFinalTypedExpr.eval, lnPatch, lnRole, if_pos h]
  | .challenge i, h => by
      simp only [zeroAt, Bool.or_eq_true, beq_iff_eq] at h
      simp only [CorrectedFinalTypedExpr.eval, lnPatch, lnChal, if_pos h]
  | .const c, h => by
      simp only [zeroAt, beq_iff_eq] at h
      simp [CorrectedFinalTypedExpr.eval, h]
  | .add x y, h => by
      simp only [zeroAt, Bool.and_eq_true] at h
      simp [CorrectedFinalTypedExpr.eval, zeroAt_eval env x h.1, zeroAt_eval env y h.2]
  | .sub x y, h => by
      simp only [zeroAt, Bool.and_eq_true] at h
      simp [CorrectedFinalTypedExpr.eval, zeroAt_eval env x h.1, zeroAt_eval env y h.2]
  | .mul x y, h => by
      simp only [zeroAt, Bool.or_eq_true] at h
      rcases h with h | h
      · simp [CorrectedFinalTypedExpr.eval, zeroAt_eval env x h]
      · simp [CorrectedFinalTypedExpr.eval, zeroAt_eval env y h]
  | .neg x, h => by
      simp only [zeroAt] at h
      simp [CorrectedFinalTypedExpr.eval, zeroAt_eval env x h]
  | .pow x n, h => by
      simp only [zeroAt, Bool.and_eq_true, decide_eq_true_eq] at h
      simp [CorrectedFinalTypedExpr.eval, zeroAt_eval env x h.1, zero_pow (Nat.pos_iff_ne_zero.mp h.2)]

/-- The three per-state `ln` recurrences pass the check (measured). -/
theorem deleted_rowLocal_zeroAt :
    ∀ i ∈ [50, 58, 65], ∀ h : i < 82, zeroAt (correctedFinalExtGate ⟨i, h⟩) = true := by
  decide +kernel

/-- **Core `50`, `58`, `65` vanish at every patched row.** -/
theorem deleted_rowLocal_vanish (env : Env309 F K) (i : CorrectedCoreExtGateId)
    (hi : i.val = 50 ∨ i.val = 58 ∨ i.val = 65) : coreSemValue309 (lnPatch309 env) i = 0 := by
  have hz : zeroAt (correctedFinalExtGate i) = true := by
    have := deleted_rowLocal_zeroAt i.val (by rcases hi with h | h | h <;> simp [h]) i.isLt
    simpa using this
  have hne : ∀ j : CorrectedCoreExtGateId, j.val ≠ i.val → i ≠ j := fun j hj h => hj (by rw [h])
  unfold coreSemValue309 correctedCoreSemanticValue
  have q1 : i ≠ packedQueueNonEmptyId := hne _ (by rcases hi with h | h | h <;> rw [h] <;> decide)
  have q2 : i ≠ packedQueueTilingId := hne _ (by rcases hi with h | h | h <;> rw [h] <;> decide)
  have q3 : i ≠ packedWalkCountId := hne _ (by rcases hi with h | h | h <;> rw [h] <;> decide)
  have q4 : i ≠ packedWalkAccId := hne _ (by rcases hi with h | h | h <;> rw [h] <;> decide)
  have q5 : i ≠ packedChainId := hne _ (by rcases hi with h | h | h <;> rw [h] <;> decide)
  have q6 : ¬ (i = packedLnChainId ∨ i = packedWalkLnId) := by
    rintro (h | h)
    · exact hne _ (by rcases hi with h | h | h <;> rw [h] <;> decide) h
    · exact hne _ (by rcases hi with h | h | h <;> rw [h] <;> decide) h
  simp only [q1, q2, q3, q4, q5, q6, ↓reduceIte]
  exact zeroAt_eval env.base _ hz

end zero

/-! ## 4. `V_comp` at the patched row -/

section vcomp
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The 72 row-local packed gates vanish on a row whose core positions `< 72` vanish (the argument
of `paperPackingRowLocal_eval_zero_vcl`, with the core hypothesis made explicit). -/
theorem paperPackingRowLocal_eval_zero_of_core {env : Env309 F K}
    (hcore : ∀ i : CorrectedCoreExtGateId, (i : ℕ) < 72 → coreSemValue309 env i = 0) :
    ∀ g ∈ OptimizedComputeGateBasis.paperPackingRowLocal, g.eval env.base.toSourceEnv = 0 := by
  intro g hg
  obtain ⟨k, hget⟩ := List.mem_iff_get.mp hg
  have hk : (k : ℕ) < 72 := by
    have := k.isLt
    simpa [OptimizedComputeGateBasis.paperPackingRowLocal_length] using this
  have hc := hcore ⟨k.val, by omega⟩ hk
  have hq1 : (⟨k.val, by omega⟩ : CorrectedCoreExtGateId) ≠ packedQueueNonEmptyId := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have hq2 : (⟨k.val, by omega⟩ : CorrectedCoreExtGateId) ≠ packedQueueTilingId := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have h75 : (⟨k.val, by omega⟩ : CorrectedCoreExtGateId) ≠ packedWalkCountId := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have h76 : (⟨k.val, by omega⟩ : CorrectedCoreExtGateId) ≠ packedWalkAccId := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have h80 : (⟨k.val, by omega⟩ : CorrectedCoreExtGateId) ≠ packedChainId := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have h89 : ¬ ((⟨k.val, by omega⟩ : CorrectedCoreExtGateId) = packedLnChainId ∨
      (⟨k.val, by omega⟩ : CorrectedCoreExtGateId) = packedWalkLnId) := by
    rintro (h | h)
    · have := congrArg Fin.val h; simp at this; omega
    · have := congrArg Fin.val h; simp at this; omega
  have hgate : (correctedFinalExtGate ⟨k.val, by omega⟩).eval env.base = 0 := by
    simp only [coreSemValue309, hq1, hq2, ↓reduceIte] at hc
    have h7 : ¬ ((k : ℕ) = 72 ∨ (k : ℕ) = 73) := by omega
    simpa [correctedCoreSemanticValue, h75, h76, h80, h89, h7] using hc
  have hlen : (k : ℕ) < OptimizedComputeGateBasis.finalExtTransitionGates.length := by simp; omega
  have hsrc := (correctedFinalExtGate_eval_source env.base ⟨k.val, by omega⟩).trans hgate
  have hget' : OptimizedComputeGateBasis.finalExtTransitionGates.get ⟨k.val, hlen⟩ = OptimizedComputeGateBasis.paperPackingRowLocal.get k := by
    have hk' : k.val < OptimizedComputeGateBasis.paperPackingRowLocal.length := k.isLt
    have hdecomp : OptimizedComputeGateBasis.finalExtTransitionGates =
        OptimizedComputeGateBasis.paperPackingRowLocal ++ (OptimizedComputeGateBasis.crossRowSingletons ++
          OptimizedComputeGateBasis.queueWitnessGates ++ OptimizedComputeGateBasis.finalSampledIOTransitionGates) := by
      rw [OptimizedComputeGateBasis.finalExtTransitionGates, OptimizedComputeGateBasis.paperPacking_eq_rowLocal_append]
      simp [List.append_assoc]
    have hq : OptimizedComputeGateBasis.finalExtTransitionGates[k.val]? = OptimizedComputeGateBasis.paperPackingRowLocal[k.val]? := by
      rw [hdecomp]
      exact List.getElem?_append_left hk'
    apply Option.some_inj.mp
    simpa [List.get_eq_getElem] using
      (List.getElem?_eq_getElem hlen).symm.trans (hq.trans (List.getElem?_eq_getElem hk'))
  rw [← hget, ← hget']
  exact hsrc

/-- At the patched row, every core position `< 72` vanishes: the kept ones by the obligations, the
three deleted recurrences by `deleted_rowLocal_vanish`. -/
theorem core_lt72_of_q7 {n : ℕ} {env : Env309 F K} {envF : Env F}
    (h : VclSourceObligationsQ7 n env envF) :
    ∀ i : CorrectedCoreExtGateId, (i : ℕ) < 72 → coreSemValue309 (lnPatch309 env) i = 0 := by
  intro i hi
  by_cases hd : i.val = 50 ∨ i.val = 58 ∨ i.val = 65
  · exact deleted_rowLocal_vanish env i hd
  · have hk : i ∈ keptCoreIdsQ7 := by
      simp only [keptCoreIdsQ7, keptCoreIds, List.mem_filter, List.mem_finRange, true_and,
        formRCoreIds, deletedCoreIds]
      simp; omega
    exact (VclSourceObligationsQ7.lnPatch h).extensionCore i hk

theorem lnPatch_toSourceEnv_trace_base (env : CorrectedFinalTypedEnv F K) (i : ℕ) (hi : i < 13) :
    (lnPatch env).toSourceEnv.trace i = env.toSourceEnv.trace i := by
  rw [source_trace_base _ i hi, source_trace_base _ i hi]; rfl

theorem oneHot_lnPatch (env : CorrectedFinalTypedEnv F K) (st : State)
    (h : OneHotSelector env.toSourceEnv st) : OneHotSelector (lnPatch env).toSourceEnv st := by
  intro s
  rw [lnPatch_toSourceEnv_trace_base env _ (by cases s <;> decide)]
  exact h s

theorem zZinv_lnPatch (env : CorrectedFinalTypedEnv F K) :
    (zZinvExpr.subst computeSubst).eval (lnPatch env).toSourceEnv =
      (zZinvExpr.subst computeSubst).eval env.toSourceEnv := by
  have hs : zZinvExpr.subst computeSubst =
      .Sub (.Mul (.Var .challenge 1) (.Var .challenge 5)) (.Const 1) := rfl
  rw [hs]
  simp [Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, lnPatch, lnChal]

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

/-- **The patched row of a Q7-obligated row is `V_comp`** (every decoded timestamp is `0`). -/
theorem q7_obligations_vcomp (n : ℕ) (b : Basis (Fin 3) F K) (envF : Env F)
    (h : VclSourceObligationsQ7 n (gather309 b envF) envF)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1)
    (hzZ : (zZinvExpr.subst computeSubst).eval
      (gatherCorrectedFinalTypedEnv b envF).toSourceEnv = 0) :
    VcompAt (lnPatch (gatherCorrectedFinalTypedEnv b envF)) := by
  obtain ⟨st, hone⟩ := oneHot_of_base15 n b envF h.base15 hchar
  exact vcompAt_of_rowLocal _ st (oneHot_lnPatch _ st hone)
    ((zZinv_lnPatch _).trans hzZ)
    (paperPackingRowLocal_eval_zero_of_core (env := lnPatch309 (gather309 b envF))
      (core_lt72_of_q7 h))

/-- **At `computeChipVCLQ7`: acceptance ⇒ `V_comp` of the patched row** at every row node. -/
theorem computeChipVCLQ7_row_vcomp {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLQ7 hn nodes b γc ρc chalV pubVal orbit).rap.w → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (computeChipVCLQ7 hn nodes b γc ρc chalV pubVal orbit) P)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1)
    (x : F) (hx : x ∈ rowNodeSet nodes)
    (hzZ : (zZinvExpr.subst computeSubst).eval (gatherCorrectedFinalTypedEnv b
      (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))).toSourceEnv = 0) :
    VcompAt (lnPatch (gatherCorrectedFinalTypedEnv b
      (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))) := by
  have hall := ((computeChipVCLQ7_sat_iff hn nodes b γc ρc chalV pubVal orbit P).1 hP).2 x hx
  exact q7_obligations_vcomp n b _
    (VclSourceObligationsQ7.of_vclGatesQ7 n b γc ρc _ hall) hchar hzZ

/-- **`lookup_binds_head` at the Q7 chip** (patched row): on an accepted row in state
`st ≠ cons`, if the slot-0 record's fingerprints are served as the formula cell `[l r]`, then `l`
is the opcode atom and the row's `f_t` is the formula's axis-3 child. -/
theorem computeChipVCLQ7_lookup_binds_head {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLQ7 hn nodes b γc ρc chalV pubVal orbit).rap.w → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (computeChipVCLQ7 hn nodes b γc ρc chalV pubVal orbit) P)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1)
    (x : F) (hx : x ∈ rowNodeSet nodes)
    (hzZ : (zZinvExpr.subst computeSubst).eval (gatherCorrectedFinalTypedEnv b
      (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))).toSourceEnv = 0)
    (st : State)
    (hone : OneHotSelector (lnPatch (gatherCorrectedFinalTypedEnv b
      (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))).toSourceEnv st)
    (hcons : st ≠ State.cons) (W : ℕ)
    (hz : (decodeInputs (lnPatch (gatherCorrectedFinalTypedEnv b
      (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))))).z ≠ 0)
    (hwin : ∀ k, 0 < k → k < W → (decodeInputs (lnPatch (gatherCorrectedFinalTypedEnv b
      (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))))).z ^ k ≠ 1)
    (hop : st.toNat < ringChar K) {l r : Noun} (hW : l.leaves ≤ W)
    (hl : ∀ a, l = .atom a → a < ringChar K)
    (hsv : ServedFormulaCell (decodeInputs (lnPatch (gatherCorrectedFinalTypedEnv b
        (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))))).z
      (decodePub (lnPatch (gatherCorrectedFinalTypedEnv b
        (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))) st)
      (decodeDec (lnPatch (gatherCorrectedFinalTypedEnv b
        (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))))) l r) :
    l = .atom st.toNat ∧ Noun.slot 3 (.cell l r) = some r ∧
      Nock.GlobalCarryRecognizer.enc (decodeInputs (lnPatch (gatherCorrectedFinalTypedEnv b
        (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))))).z r =
        (decodeDec (lnPatch (gatherCorrectedFinalTypedEnv b
          (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))))).f_t := by
  obtain ⟨st', hone', hV⟩ := computeChipVCLQ7_row_vcomp hn nodes b γc ρc chalV pubVal orbit P hP
    hchar x hx hzZ
  have hst : st' = st := by
    by_contra hne
    have a := hone' st
    have c := hone st
    simp only [if_neg (Ne.symm hne)] at a c
    rw [a] at c
    exact zero_ne_one c
  subst hst
  exact lookup_binds_head_row hV hcons hz W hwin hop hW hl hsv

end vcomp


/-! ## 5. NC: perturbing `chalV 0` / `chalV 9` is silent -/

section nc
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Overwrite the challenge limbs of slots `0` (`0..2`) and `9` (`27..29`). -/
def perturbChal09 (envF : Env F) (u : ℕ → F) : Env F :=
  { envF with chal := fun j => if j < 3 ∨ (27 ≤ j ∧ j < 30) then u j else envF.chal j }

/-- The patched decode does not see the slot-`0`/`9` limbs. -/
theorem lnPatch_gather_perturb (b : Basis (Fin 3) F K) (envF : Env F) (u : ℕ → F) :
    lnPatch (gatherCorrectedFinalTypedEnv b (perturbChal09 envF u)) =
      lnPatch (gatherCorrectedFinalTypedEnv b envF) := by
  simp only [lnPatch, gatherCorrectedFinalTypedEnv, perturbChal09]
  congr 1
  funext i
  by_cases h : lnChal i
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    simp only [lnChal] at h
    apply Finset.sum_congr rfl
    intro k _
    have := i.isLt; have := k.isLt
    have hk : ¬ (3 * (i : ℕ) + (k : ℕ) < 3 ∨ (27 ≤ 3 * (i : ℕ) + (k : ℕ) ∧
        3 * (i : ℕ) + (k : ℕ) < 30)) := by omega
    simp only [hk, if_false]

theorem lnPatch309_gather_perturb (b : Basis (Fin 3) F K) (envF : Env F) (u : ℕ → F) :
    lnPatch309 (gather309 b (perturbChal09 envF u)) = lnPatch309 (gather309 b envF) := by
  simp only [lnPatch309, gather309, lnPatch_gather_perturb]
  rfl

/-- The Q7 obligations are exactly the patched row's. -/
theorem q7_obligations_patch_iff {n : ℕ} {env : Env309 F K} {envF : Env F} :
    VclSourceObligationsQ7 n env envF ↔ VclSourceObligationsQ7 n (lnPatch309 env) envF := by
  refine ⟨VclSourceObligationsQ7.lnPatch, fun h => ⟨h.base15, ?_, ?_, ?_, ?_, h.selectorEquality2⟩⟩
  · exact fun i hi => (coreSemValue309_lnPatch env i (kept_no_ln.1 i hi)).symm.trans
      (h.extensionCore i hi)
  · exact fun j => (auxSemValue309_lnPatch env j).symm.trans (h.residualAux j)
  · exact fun t ht => (evalW_lnPatch env t (noLnW_of_touches (kept_no_ln.2.2.2.1 t ht))).symm.trans
      (h.endpointDegreeTwo t ht)
  · exact fun t ht => (evalW_lnPatch env t (noLnW_of_touches (kept_no_ln.2.2.2.2 t ht))).symm.trans
      (h.endpointDegreeFour t ht)

/-- **NC (silent)**: with the row's `𝔽` gates fixed, the Q7 obligations of a gathered row do not
depend on the challenge limbs of slots `0` (`α`) and `9` (`λ`). -/
theorem q7_obligations_silent_09 (n : ℕ) (b : Basis (Fin 3) F K) (envF : Env F) (u : ℕ → F) :
    VclSourceObligationsQ7 n (gather309 b (perturbChal09 envF u)) envF ↔
      VclSourceObligationsQ7 n (gather309 b envF) envF := by
  rw [q7_obligations_patch_iff, lnPatch309_gather_perturb, ← q7_obligations_patch_iff]

end nc


/-! ## 6. The patched decode agrees with the unpatched decode on what `lookup_binds_head` reads

`lookup_binds_head` reads `decodeInputs.z` (challenge slot 1), `decodeDec` (source columns
`47..64` = extension roles `36..53`), `decodePub.f` (source `14..16` = roles `3..5`) and the base
selectors (`0..10`).  None of them is a patched coordinate (roles 54/55 = source 67/68, challenges
0/9), so the patched and unpatched decodes agree there. -/

section bridge
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Source trace columns other than `67`/`68` (roles 54/55) are unchanged by the patch. -/
theorem lnPatch_source_trace (env : CorrectedFinalTypedEnv F K) (i : ℕ) (h67 : i ≠ 67)
    (h68 : i ≠ 68) : (lnPatch env).toSourceEnv.trace i = env.toSourceEnv.trace i := by
  simp only [CorrectedFinalTypedEnv.toSourceEnv]
  by_cases h13 : i < 13
  · rw [dif_pos h13, dif_pos h13]; rfl
  rw [dif_neg h13, dif_neg h13]
  by_cases h76 : i < 76
  · rw [dif_pos h76, dif_pos h76]
    simp only [lnPatch, lnRole]
    rw [if_neg (by omega)]
  rw [dif_neg h76, dif_neg h76]
  rfl

/-- Source challenges other than slot `0`, slot `9` and the `λ`-power block are unchanged. -/
theorem lnPatch_source_chal (env : CorrectedFinalTypedEnv F K) (i : ℕ) (h0 : i ≠ 0)
    (h9 : i ≠ 9) (hl : ¬ (100 ≤ i ∧ i < 164)) :
    (lnPatch env).toSourceEnv.chal i = env.toSourceEnv.chal i := by
  simp only [CorrectedFinalTypedEnv.toSourceEnv]
  by_cases h12 : i < 12
  · rw [dif_pos h12, dif_pos h12]
    simp only [lnPatch, lnChal]
    rw [if_neg (by omega)]
  · rw [dif_neg h12, dif_neg h12, if_neg hl, if_neg hl]

/-- **Bridge: `decodeInputs.z`** of the patched row is the row's. -/
theorem decodeInputs_z_lnPatch (env : CorrectedFinalTypedEnv F K) :
    (decodeInputs (lnPatch env)).z = (decodeInputs env).z := by
  simp only [decodeInputs, decodeSource, inpOf, Env.ofSubst, computeSubst, Expr.eval]
  exact lnPatch_source_chal env 1 (by decide) (by decide) (by decide)

theorem lnPatch_fpOf_source (env : CorrectedFinalTypedEnv F K) (j : ℕ)
    (hj : 47 ≤ j ∧ j + 2 < 65 ∨ 14 ≤ j ∧ j + 2 < 17) :
    fpOf (decodeSource (lnPatch env)) j = fpOf (decodeSource env) j := by
  have key : ∀ i, 47 ≤ i ∧ i < 65 ∨ 14 ≤ i ∧ i < 17 →
      (decodeSource (lnPatch env)).trace i = (decodeSource env).trace i := by
    intro i hi
    simp only [decodeSource, Env.ofSubst, computeSubst]
    rcases hi with hi | hi
    · have hs : computeTraceSubst .traceCur i =
          decFP .traceCur ((i - 47) / 3) ((i - 47) % 3) := by
        simp only [computeTraceSubst]
        rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      rw [hs]
      simp only [decFP, Expr.eval, ext0]
      exact lnPatch_source_trace env _ (by omega) (by omega)
    · have hs : computeTraceSubst .traceCur i =
          semanticPub .traceCur ((i - 11) / 3) ((i - 11) % 3) := by
        simp only [computeTraceSubst]
        rw [if_neg (by omega), if_pos (by omega)]
      have hr : (i - 11) / 3 = 1 := by omega
      rw [hs, hr]
      simp only [semanticPub, pubFP, ext0]
      rw [if_neg (by decide)]
      exact lnPatch_source_trace env _ (by omega) (by omega)
  simp only [fpOf]
  rw [key j (by omega), key (j + 1) (by omega), key (j + 2) (by omega)]

/-- **Bridge: `decodeDec`** of the patched row is the row's. -/
theorem decodeDec_lnPatch (env : CorrectedFinalTypedEnv F K) :
    decodeDec (lnPatch env) = decodeDec env := by
  simp only [decodeDec, decOf]
  rw [lnPatch_fpOf_source env 47 (by omega), lnPatch_fpOf_source env 50 (by omega),
    lnPatch_fpOf_source env 53 (by omega), lnPatch_fpOf_source env 56 (by omega),
    lnPatch_fpOf_source env 59 (by omega), lnPatch_fpOf_source env 62 (by omega)]

/-- **Bridge: `decodePub.f`** (the formula fingerprint) of the patched row is the row's. -/
theorem decodePub_f_lnPatch (env : CorrectedFinalTypedEnv F K) (st : State) :
    (decodePub (lnPatch env) st).f = (decodePub env st).f := by
  simp only [decodePub, pubOfState]
  exact lnPatch_fpOf_source env 14 (by omega)

/-- The selectors are unchanged (both directions). -/
theorem oneHot_lnPatch_iff (env : CorrectedFinalTypedEnv F K) (st : State) :
    OneHotSelector (lnPatch env).toSourceEnv st ↔ OneHotSelector env.toSourceEnv st := by
  refine ⟨fun h s => ?_, oneHot_lnPatch env st⟩
  rw [← lnPatch_toSourceEnv_trace_base env _ (by cases s <;> decide)]
  exact h s

/-- `ServedFormulaCell` transfers between the patched and the unpatched decode. -/
theorem servedFormulaCell_lnPatch_iff (env : CorrectedFinalTypedEnv F K) (st : State)
    (l r : Noun) :
    ServedFormulaCell (decodeInputs (lnPatch env)).z (decodePub (lnPatch env) st)
        (decodeDec (lnPatch env)) l r ↔
      ServedFormulaCell (decodeInputs env).z (decodePub env st) (decodeDec env) l r := by
  simp only [ServedFormulaCell, decodeInputs_z_lnPatch, decodePub_f_lnPatch, decodeDec_lnPatch]

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

/-- **`lookup_binds_head` at the Q7 chip, stated at the UNPATCHED decode**: every hypothesis and
the conclusion read the row as committed (`decodeInputs.z`, `decodePub.f`, `decodeDec`, the
selectors); the patch is internal to the proof. -/
theorem computeChipVCLQ7_lookup_binds_head_row {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLQ7 hn nodes b γc ρc chalV pubVal orbit).rap.w → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (computeChipVCLQ7 hn nodes b γc ρc chalV pubVal orbit) P)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1)
    (x : F) (hx : x ∈ rowNodeSet nodes)
    (hzZ : (zZinvExpr.subst computeSubst).eval (gatherCorrectedFinalTypedEnv b
      (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))).toSourceEnv = 0)
    (st : State)
    (hone : OneHotSelector (gatherCorrectedFinalTypedEnv b
      (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))).toSourceEnv st)
    (hcons : st ≠ State.cons) (W : ℕ)
    (hz : (decodeInputs (gatherCorrectedFinalTypedEnv b
      (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))).z ≠ 0)
    (hwin : ∀ k, 0 < k → k < W → (decodeInputs (gatherCorrectedFinalTypedEnv b
      (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))).z ^ k ≠ 1)
    (hop : st.toNat < ringChar K) {l r : Noun} (hW : l.leaves ≤ W)
    (hl : ∀ a, l = .atom a → a < ringChar K)
    (hsv : ServedFormulaCell (decodeInputs (gatherCorrectedFinalTypedEnv b
        (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))).z
      (decodePub (gatherCorrectedFinalTypedEnv b
        (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))) st)
      (decodeDec (gatherCorrectedFinalTypedEnv b
        (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))) l r) :
    l = .atom st.toNat ∧ Noun.slot 3 (.cell l r) = some r ∧
      Nock.GlobalCarryRecognizer.enc (decodeInputs (gatherCorrectedFinalTypedEnv b
        (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))).z r =
        (decodeDec (gatherCorrectedFinalTypedEnv b
          (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))).f_t := by
  have := computeChipVCLQ7_lookup_binds_head hn nodes b γc ρc chalV pubVal orbit P hP hchar x hx
    hzZ st ((oneHot_lnPatch_iff _ st).2 hone) hcons W
    (by rw [decodeInputs_z_lnPatch]; exact hz)
    (by rw [decodeInputs_z_lnPatch]; exact hwin) hop hW hl
    ((servedFormulaCell_lnPatch_iff _ st l r).2 hsv)
  rwa [decodeInputs_z_lnPatch, decodeDec_lnPatch] at this

end bridge

end

end VclL.Compute
end Nock.NockVMROM.Thm54
