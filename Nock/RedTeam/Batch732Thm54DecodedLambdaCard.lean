/-
  Nock/RedTeam/Batch732Thm54DecodedLambdaCard.lean

  Receipts, not
  consumers; no production edit.

  * **Width enters only at the figure bridge**: `FormRWidth F` (from §1's `hp64`) gives
    `formRN K ≤ 64` (`formRN_le_of_width`), hence `formRUniformWorkload T ≤ M_T·(3N_T + 130)`.
-/
import Lean
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch732

open scoped Classical Polynomial
open Nock Nock.Reified Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.DecodedLambdaEvent

noncomputable section

section Envs
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [Fintype F] [DecidableEq F]

/-- Every `K`, every env tuple, every `kroots`: no premise. -/
theorem card_every_env_tuple {N M : ℕ} (envsC : Fin N → Env K) (envsK : Fin M → Env K)
    (envsF : Fin M → Env F) (kroots : ℕ) :
    (decodedLambdaEventOfEnvs envsC envsK envsF kroots).card ≤
      Fintype.card K ^ 10 * (M * (3 * N + 67 + (FormRAxisEvent.formRN K - 1))) :=
  decodedLambdaEventOfEnvs_card_le envsC envsK envsF kroots

/-- At chip width. -/
theorem card_every_env_tuple_numeral {N M : ℕ} (hn : FormRAxisEvent.formRN K ≤ 64)
    (envsC : Fin N → Env K) (envsK : Fin M → Env K) (envsF : Fin M → Env F) (kroots : ℕ) :
    (decodedLambdaEventOfEnvs envsC envsK envsF kroots).card ≤
      Fintype.card K ^ 10 * (M * (3 * N + 130)) :=
  decodedLambdaEventOfEnvs_card_le_numeral hn envsC envsK envsF kroots

/-- Σ over the roots of the decomposition counts is at most the row count, every hostile forest. -/
theorem decomp_sum_every_forest {M : ℕ} (envsK : Fin M → Env K) (envsF : Fin M → Env F)
    (kroots : ℕ) :
    ∑ r ∈ Finset.Icc 1 kroots,
      Nock.RedTeam.Batch575.decompCount (decodedMTreeOfEnvs envsK envsF kroots r) ≤ M :=
  sum_decompCount_le envsK envsF kroots

end Envs

section Pkg
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem slot_filled_every_trace :
    ∀ (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]),
      (P.decodedLambdaEventOf Qc Qm).card ≤
        Fintype.card K ^ 10 * ProductionP8Containment.formRUniformWorkload P.strategy :=
  fun Qc Qm => P.decodedLambdaEventOf_card_le Qc Qm

end Pkg

/-- `FormRWidth F` (`of_package`'s premise, `FormRWidth_of_hp64` from §1's `hp64`) gives the width
conjunct at `K` (`ringChar K = ringChar F`). -/
theorem formRN_le_of_width {F K : Type} [Field F] [Field K] [Algebra F K]
    (hw : OptimizedComputeFinalTrace.FormRWidth F) : FormRAxisEvent.formRN K ≤ 64 := by
  have hc : ringChar K = ringChar F := (Algebra.ringChar_eq F K).symm
  have := hw.1
  unfold FormRAxisEvent.formRN
  unfold OptimizedComputeRangeCertificate.formRN at this
  rw [hc]; exact this

/-- At chip width the uniform summand is the numeral `M_T·(3N_T + 130)`. -/
theorem formRUniformWorkload_le_of_width {F K : Type} [Field F] [Field K] [Algebra F K]
    [CharP K (ringChar K)] (T : ProductionP8Containment.ProductionStrategy F K)
    (hn : FormRAxisEvent.formRN K ≤ 64) :
    ProductionP8Containment.formRUniformWorkload T ≤
      (SemanticStrategy.memorySkeletonRows T.skeleton).length *
        (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 130) := by
  unfold ProductionP8Containment.formRUniformWorkload
  exact Nat.mul_le_mul_left _ (by omega)

/-- At `formRN K = 64` it is exactly that numeral. -/
theorem formRUniformWorkload_eq_64 {F K : Type} [Field F] [Field K] [Algebra F K]
    [CharP K (ringChar K)] (T : ProductionP8Containment.ProductionStrategy F K)
    (hn : FormRAxisEvent.formRN K = 64) :
    ProductionP8Containment.formRUniformWorkload T =
      (SemanticStrategy.memorySkeletonRows T.skeleton).length *
        (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 130) := by
  unfold ProductionP8Containment.formRUniformWorkload
  rw [hn]

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let pkg := `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
  let some ci := env.find? (pkg ++ `optimizedFalseAcceptance_card_le_records)
    | throwError "optimizedFalseAcceptance_card_le_records missing"
  let some v := ci.value? (allowOpaque := true) | throwError "no proof term"
  -- Collect the used constants of the proof term and of the proof terms of the two
  -- intermediate theorems (named, so the walk is exact, not a closure).
  let mids : List Name := [pkg ++ `consumedFailureEvent_card_le,
    `Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv_card_le]
  let mut used := v.getUsedConstants
  for m in mids do
    unless used.contains m do throwError m!"the consumed card bound does not reach {m}"
    let some mi := env.find? m | throwError m!"{m} missing"
    let some mv := mi.value? (allowOpaque := true) | throwError m!"{m}: no proof term"
    used := used ++ mv.getUsedConstants
  unless used.contains (pkg ++ `decodedLambdaEventOf_card_le) do
    throwError "the consumed card bound does not use decodedLambdaEventOf_card_le"
  if used.contains `Nock.NockVMROM.Thm54.FormRAxisEvent.formRLambdaEvent_card_le then
    throwError "the consumed card bound still uses formRLambdaEvent_card_le"
  -- the filler is a theorem, not a hypothesis of the consumer
  let some fi := env.find? (pkg ++ `decodedLambdaEventOf_card_le) | throwError "filler missing"
  unless fi matches .thmInfo _ do throwError "filler is not a theorem"
  logInfo "slot_filled_by_theorem: optimizedFalseAcceptance_card_le_records uses the theorem \
    decodedLambdaEventOf_card_le; formRLambdaEvent_card_le is not used"

end Nock.RedTeam.Batch732

#print axioms Nock.RedTeam.Batch732.card_every_env_tuple
#print axioms Nock.RedTeam.Batch732.card_every_env_tuple_numeral
#print axioms Nock.RedTeam.Batch732.decomp_sum_every_forest
#print axioms Nock.RedTeam.Batch732.slot_filled_every_trace
#print axioms Nock.RedTeam.Batch732.formRN_le_of_width
#print axioms Nock.RedTeam.Batch732.formRUniformWorkload_le_of_width
#print axioms Nock.RedTeam.Batch732.formRUniformWorkload_eq_64
#print axioms Nock.NockVMROM.Thm54.DecodedLambdaEvent.decodedLambdaEventOfEnvs_card_le
#print axioms Nock.NockVMROM.Thm54.DecodedLambdaEvent.decodedLambdaEventOfEnvs_card_le_numeral
#print axioms Nock.NockVMROM.Thm54.DecodedLambdaEvent.sum_decompCount_le
#print axioms Nock.NockVMROM.Thm54.DecodedLambdaEvent.decodedSum_le_uniform
#print axioms Nock.NockVMROM.Thm54.DecodedLambdaEvent.decodedRootBad_card_le
#print axioms Nock.NockVMROM.Thm54.DecodedLambdaEvent.natDegree_formRCounts_coeff_le
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.decodedLambdaEventOf_card_le
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.optimizedFalseAcceptance_card_le_records
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
