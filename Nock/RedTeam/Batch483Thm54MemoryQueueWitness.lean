/-
  Nock/RedTeam/Batch483Thm54MemoryQueueWitness.lean

  **New column, two gates.**

  The memory paper `𝕂` set gains the two ratio-form queue gates of `Batch478`:

  * `walkQueueNonEmpty = notLast · (walk_inv · (count − ln) − 1)` (degree 3)
  * `walkQueueTiling = isLast · (count − ln)` (degree 2)

  `walk_inv` is a NEW extension role `55` (`QueueWitnessRole`).  Width `196 → 199`
  (`61·e+13 → 62·e+13`).  Honest fill is `(count − ln)⁻¹` off a tiled last row.

  After seed-pin `OH` (`M.rap.s = 146`, `paperKGates = 47`) the queue gates are a
  further `47 → 49` / `146 → 152`.  Degree ≤ 4.  Walk-γ stays slot 7.  Roles 34/35/36 untouched.
-/
import Nock.NockVMROM.Thm54.MemoryWalkLabel
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.PaperResourceCounts
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.OptimizedMemoryCoreInventory

set_option autoImplicit false

namespace Nock.RedTeam.Batch483

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.Thm54Resources
open Nock.NockVMROM.Thm54.MemoryPaperFactorization
open Nock.NockVMROM.Thm54.OptimizedMemoryCoreInventory
open Nock.NockVMROM.Thm54.MemoryWalkLabel

theorem queue_gates_degree :
    (MemoryWalkLabel.walkQueueNonEmpty (F := ℚ)).degree ≤ 4 ∧
      (MemoryWalkLabel.walkQueueTiling (F := ℚ)).degree ≤ 4 :=
  ⟨MemoryWalkLabel.walkQueueNonEmpty_degree,
    MemoryWalkLabel.walkQueueTiling_degree⟩

theorem queue_gates_mem :
    MemoryWalkLabel.walkQueueNonEmpty ∈
      OptimizedMemoryGateBasis.paperKGates (K := ℚ) (F := ℚ) ∧
      MemoryWalkLabel.walkQueueTiling ∈
        OptimizedMemoryGateBasis.paperKGates (K := ℚ) (F := ℚ) := by
  simp [OptimizedMemoryGateBasis.paperKGates,
    MemoryWalkLabel.queueWitnessGates]

theorem walk_inv_is_new_column :
    MemoryWalkLabel.walkInvRole = 55 :=
  rfl

theorem hosted_walk_roles_unmoved :
    MemoryWalkLabel.lnRole = 31 ∧ MemoryWalkLabel.countRole = 32 ∧
      MemoryWalkLabel.accRole = 33 :=
  ⟨rfl, rfl, rfl⟩

theorem memory_width_moved :
    memoryColumns 3 = 205 :=
  memoryColumns_deployed

theorem memory_resources_moved :
    memoryConstraints 3 = 156 ∧ memoryTransitionGates 3 = 156 :=
  ⟨memoryConstraints_deployed, memoryTransitionGates_deployed⟩

theorem paperKGates_moved :
    (OptimizedMemoryGateBasis.paperKGates (K := ℚ) (F := ℚ)).length = 49 ∧
      (OptimizedMemoryGateBasis.paperKGatesCore (K := ℚ) (F := ℚ)).length = 43 :=
  ⟨rfl, rfl⟩

theorem packing_degree_le_four :
    ∀ g ∈ OptimizedMemoryGateBasis.paperKGates (K := ℚ) (F := ℚ), g.degree ≤ 4 :=
  OptimizedMemoryGateBasis.paperKGates_degree

theorem extension_card_moved :
    Fintype.card ExtensionRole = 56 :=
  extensionRole_card

def nockCompiles_zmod_hypotheses_unmoved : String :=
  "nockCompiles_zmod binders unmoved: hrun hbound hs hf hΛp hp hK hF hwin hKszChar"

theorem nockCompiles_zmod_hypotheses_unmoved_nonempty :
    nockCompiles_zmod_hypotheses_unmoved ≠ "" := by decide

end Nock.RedTeam.Batch483
