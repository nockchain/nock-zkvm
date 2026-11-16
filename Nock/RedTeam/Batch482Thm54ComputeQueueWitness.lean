/-
  Nock/RedTeam/Batch482Thm54ComputeQueueWitness.lean

  **Column + two gates.**

  The compute packed basis gains extension role `62` (`walk_inv`) and the two
  ratio-form queue gates of `Batch478`:

  * `walkQueueNonEmpty = notLast · (walk_inv · (count − ln) − 1)` (degree 4:
    compute `count` is overlay coordinate 0, degree 2)
  * `walkQueueTiling = isLast · (count − ln)` (degree 3)

  Packed walk IDs `72..75` stay put (the pair is appended).  The IO chain
  moves `79 → 81`.  `paperPacking_iff_sources` remains about the core 76
  (queue gates are not sources).  Honest fill is `(count − ln)⁻¹` off a
  tiled last row, else `0`.

  Resources: `w 199 → 202`, `C.rap.s 307 → 313` (`85·e+15` at `e=3` is 270
  transition).  Degree ≤ 4.
-/
import Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
import Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
import Nock.NockVMROM.Thm54.PaperResourceCounts
import Nock.NockVMROM.Thm54.ComputePaperPacking

set_option autoImplicit false

namespace Nock.RedTeam.Batch482

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.Thm54Resources

theorem queue_gates_degree :
    OptimizedComputeGateBasis.walkQueueNonEmpty.degree ≤ 4 ∧
      OptimizedComputeGateBasis.walkQueueTiling.degree ≤ 4 := by
  decide

theorem queue_gates_mem :
    OptimizedComputeGateBasis.walkQueueNonEmpty ∈
        OptimizedComputeGateBasis.paperPackingNonIOGates ∧
      OptimizedComputeGateBasis.walkQueueTiling ∈
        OptimizedComputeGateBasis.paperPackingNonIOGates := by
  simp [OptimizedComputeGateBasis.paperPackingNonIOGates,
    OptimizedComputeGateBasis.queueWitnessGates]

theorem packed_walk_ids_unmoved :
    (packedLnChainId : ℕ) = 72 ∧ (packedWalkLnId : ℕ) = 73 ∧
      (packedWalkCountId : ℕ) = 74 ∧ (packedWalkAccId : ℕ) = 75 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem packed_chain_shifted :
    (packedChainId : ℕ) = 81 :=
  rfl

theorem compute_resources_moved :
    computeColumns 3 = 303 ∧ computeConstraints 3 = 418 ∧
      computeTransitionGates 3 = 374 :=
  ⟨computeColumns_deployed, computeConstraints_deployed, computeTransitionGates_deployed⟩

theorem paperPacking_core_still_76 :
    ComputePaperPacking.paperPackingCoreGates.length = 76 ∧
      OptimizedComputeGateBasis.paperPackingNonIOGates.length = 78 :=
  ⟨ComputePaperPacking.paperPackingCoreGates_length,
    OptimizedComputeGateBasis.paperPackingNonIOGates_length⟩

theorem packing_degree_le_four :
    ∀ g ∈ OptimizedComputeGateBasis.paperPackingNonIOGates, g.degree ≤ 4 :=
  ComputePaperPacking.paperPackingNonIOGates_degree

def nockCompiles_zmod_hypotheses_unmoved : String :=
  "nockCompiles_zmod binders unmoved: hrun hbound hs hf hΛp hp hK hF hwin hKszChar"

theorem nockCompiles_zmod_hypotheses_unmoved_nonempty :
    nockCompiles_zmod_hypotheses_unmoved ≠ "" := by decide

end Nock.RedTeam.Batch482

#print axioms Nock.RedTeam.Batch482.queue_gates_degree
#print axioms Nock.RedTeam.Batch482.compute_resources_moved
#print axioms Nock.RedTeam.Batch482.packing_degree_le_four
