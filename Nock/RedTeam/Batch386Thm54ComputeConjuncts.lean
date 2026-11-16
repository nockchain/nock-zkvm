/-
  Nock/RedTeam/Batch386Thm54ComputeConjuncts.lean

  **Compute conjuncts after the wrap identity.**

  * `vcomp` — `deployed_row_vcomp_at` transported by `wrap_fixes_vcomp_row`
  * `ln_chain` — family hand-off `ln(i) = ln_prev(i+1)`
  * `computeRows` — `ComputeRowAccepted` = state agreement + `Vcomp`

  **5/21.**  Newly closed: `vcomp`, `ln_chain`,
  `computeRows`.
-/
import Nock.NockVMROM.Thm54.WrapComputeConjuncts
import Nock.RedTeam.Batch377Thm54AcceptedContentOfTraces
import Nock.RedTeam.Batch385Thm54WrapFixesVcomp
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch386

open scoped Polynomial
open Polynomial
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WrapComputeConjuncts
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ExactExecution
open Nock.Framework
open MonolithicRAP

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Step-2 closed compute conjuncts of `AcceptedContent`. -/
structure ClosedComputeConjuncts
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc)) : Prop where
  vcomp :
    ∀ i, ComputeTable.Vcomp
      ((strategyOfTraces P Qc Qm c h).specializedCfg
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).challenges.computeInputs
      (((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computePubAt i)
      (((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeDecAt i)
  ln_chain :
    ∀ i : Fin ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).compRows,
      ∀ hi : (i : ℕ) + 1 <
          ((strategyOfTraces P Qc Qm c h).specializedCfg
              (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).compRows,
        (((strategyOfTraces P Qc Qm c h).specializedExec
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computePubAt i).ln =
          (((strategyOfTraces P Qc Qm c h).specializedExec
              (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computePubAt
            ⟨(i : ℕ) + 1, hi⟩).ln_prev
  computeRows :
    ((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).ComputeRowsAccepted

theorem closedComputeConjuncts_of_accepted
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc)) :
    ClosedComputeConjuncts P Qc Qm c h hz hsat where
  vcomp := specialized_vcomp P Qc Qm c h hz hsat
  ln_chain := specialized_ln_chain P Qc Qm c h hz hsat
  computeRows := specialized_computeRows P Qc Qm c h hz hsat

/-- Names closed at step 2.  Starting 2/21 + these three = **5/21**. -/
def newlyClosed : List String := ["vcomp", "ln_chain", "computeRows"]

theorem newlyClosed_length : newlyClosed.length = 3 := by decide

theorem closed_count_after_step2 : 2 + newlyClosed.length = 5 := by decide

end

end Nock.RedTeam.Batch386

#print axioms Nock.RedTeam.Batch386.closedComputeConjuncts_of_accepted
#print axioms Nock.RedTeam.Batch386.closed_count_after_step2
