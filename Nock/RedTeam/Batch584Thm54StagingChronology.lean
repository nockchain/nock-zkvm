/-
  Nock/RedTeam/Batch584Thm54StagingChronology.lean

  Tile equality at 302/204,
  the chronology sentence, and the MEASURED placement of the Form R and `atom` columns.

  Measured now:
  * compute `107 + 132 + 63 = 302`, memory `84 + 48 + 72 = 204` over `deployedChronology`;
-/
import Nock.NockVMROM.Thm54.DeployedStaging
import Nock.NockVMROM.Thm54.CrossRapChronology

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch584

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedStaging

theorem historic_blocks_tile :
    (94 + 6 + 13 : ℕ) = 113 ∧ (36 + 6 + 13 : ℕ) = 55 :=
  CrossRap.blocks_tile_the_chips

theorem live_blocks_tile :
    (108 + 132 + 63 : ℕ) = 303 ∧ (85 + 48 + 72 : ℕ) = 205 :=
  deployed_blocks_tile_the_chips

theorem live_tile_is_the_schedules :
    (303 : ℕ) = ∑ r, deployedComputeSchedule.width r ∧
      (205 : ℕ) = ∑ r, deployedMemorySchedule.width r :=
  ⟨deployedCompute_total_width, deployedMemory_total_width⟩

/-- The measured placement (B3): `(name, chip, first col, last col, round)`. -/
def placement : List (String × String × ℕ × ℕ × ℕ) :=
  [ ("c_j", "compute", 202, 264, 0), ("m_k", "compute", 265, 270, 0),
    ("h", "compute", 271, 271, 0), ("t", "compute", 272, 272, 0),
    ("p", "compute", 273, 273, 0), ("top", "compute", 274, 274, 0),
    ("E_k", "compute", 275, 295, 0),
    ("H", "compute", 296, 298, 2), ("T", "compute", 299, 301, 2),
    ("atom", "memory", 180, 180, 0),
    ("pw", "memory", 15, 17, 2), ("counts", "memory", 18, 20, 2),
    ("T", "memory", 81, 83, 2), ("C'", "memory", 177, 179, 2) ]

/-- Every placement row is the measured map at both ends of its range. -/
theorem placement_measured :
    placement.all (fun r =>
      let rnd := if r.2.1 = "compute" then computeColRound else memoryColRound
      rnd r.2.2.1 == r.2.2.2.2 && rnd r.2.2.2.1 == r.2.2.2.2) = true := by
  decide

theorem chronology_sentence :
    memoryColRound OptimizedMemoryGateBasis.atomCol = 0 ∧ memoryColRound 6 = 1 ∧
      ((deployedChronology.sampledAfter FormRAxisEvent.seedIdx : Fin 3) : ℕ) = 0 ∧
      deployedChronology.sampledAfter FormRAxisEvent.lamIdx =
        deployedChronology.sampledAfter FormRAxisEvent.alphaMIdx :=
  ⟨deployed_chronology_sentence.1, deployed_chronology_sentence.2.1.1,
    deployed_chronology_sentence.2.2.2.2.2.2.1, deployed_chronology_sentence.2.2.2.2.2.2.2⟩

end Nock.RedTeam.Batch584

#print axioms Nock.RedTeam.Batch584.live_blocks_tile
#print axioms Nock.RedTeam.Batch584.placement_measured
#print axioms Nock.RedTeam.Batch584.chronology_sentence
