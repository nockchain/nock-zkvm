/-
  Nock/RedTeam/Batch374Thm54TraceLabels.lean

  **Row labels off the traces.**

  Receipts for `ExecOfTraces.lblC` / `lblM` / `foC` / `foM` / `clabC` / `clabM`.
  Each mentions `Qc` or `Qm`.  Honest-tree BFS identification is *not* `rfl` — the decoder
  reconstructs fingerprints, not `P.objects.exec` labels.
-/
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfigGoldilocks
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch374

open scoped Polynomial
open Polynomial
open Nock
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- `lblC` mentions `Qc`: the 1-shift of `lblCAt` is `rowEnvAt` at `c`. -/
theorem lblC_mentions_Qc
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    lblC P Qc c (i.val + 1) =
      (computeStateOf (decodeSource (rowEnvAt P c (familyQc P c Qc) i)),
        (decodeInputs (rowEnvAt P c (familyQc P c Qc) i),
          decodePub (rowEnvAt P c (familyQc P c Qc) i)
            (computeStateOf (decodeSource (rowEnvAt P c (familyQc P c Qc) i))),
          decodeDec (rowEnvAt P c (familyQc P c Qc) i))) := by
  rw [lblC_succ]
  rfl

/-- `lblM` mentions `Qm`: pub is `decodeMemPub P Qm`. -/
theorem lblM_mentions_Qm
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (lblM P Qm c (i.val + 1)).2.2 = decodeMemPub P Qm c i := by
  rw [lblM_succ]
  rfl

/-- Positive control: `lblCAt` is the family `rowEnvAt` triple (`rfl`). -/
theorem lblCAt_canonical_eq_typed
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    lblCAt P (canonicalComputeTrace P) P.honestTuple i =
      (computeStateOf (decodeSource
          (rowEnvAt P P.honestTuple
            (familyQc P P.honestTuple (canonicalComputeTrace P)) i)),
        (decodeInputs (rowEnvAt P P.honestTuple
            (familyQc P P.honestTuple (canonicalComputeTrace P)) i),
          decodePub (rowEnvAt P P.honestTuple
              (familyQc P P.honestTuple (canonicalComputeTrace P)) i)
            (computeStateOf (decodeSource
              (rowEnvAt P P.honestTuple
                (familyQc P P.honestTuple (canonicalComputeTrace P)) i))),
          decodeDec (rowEnvAt P P.honestTuple
            (familyQc P P.honestTuple (canonicalComputeTrace P)) i))) :=
  lblCAt_eq_rowEnvAt P (canonicalComputeTrace P) P.honestTuple i

/-- `foC i` is `comp_stateSep.fanout` of the `Qc` label. -/
theorem foC_eq_stateSep
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : ℕ) :
    foC P Qc c i = (comp_stateSep (K := K)).fanout (lblC P Qc c i).1 :=
  rfl

/-- `foM i` is `mem_stateSep.fanout` of the `Qm` label. -/
theorem foM_eq_stateSep
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : ℕ) :
    foM P Qm c i = (mem_stateSep (K := K)).fanout (lblM P Qm c i).1 :=
  rfl

/-- `clabC` is `sfTriple` of the parent `Qc` pub when `j < foC`. -/
theorem clabC_sfTriple
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i j : ℕ)
    (hj : j < foC P Qc c i) :
    ∃ pub dec,
      clabC P Qc c i j =
        some ((lblC P Qc c i).1, ((lblC P Qc c i).2.1, pub, dec)) ∧
        (pub.s, pub.f, pub.e) =
          sfTriple (lblC P Qc c i).2.2.1
            ⟨j, Nat.lt_of_lt_of_le hj
              ((comp_stateSep (K := K)).fanout_le (lblC P Qc c i).1)⟩ := by
  simp [clabC, hj]

end

end Nock.RedTeam.Batch374

#print axioms Nock.RedTeam.Batch374.lblC_mentions_Qc
#print axioms Nock.RedTeam.Batch374.lblM_mentions_Qm
#print axioms Nock.RedTeam.Batch374.lblCAt_canonical_eq_typed
#print axioms Nock.RedTeam.Batch374.foC_eq_stateSep
#print axioms Nock.RedTeam.Batch374.clabC_sfTriple
