/-
  Nock/RedTeam/Batch1746Thm54VclLServesCount.lean

  * `vcl_serves_of_count` takes the count exactly as `MF.serves` now receives it
    (`(reqs ++ internal).length < ringChar Kio`); the earlier explicit `k₁ + k₂ < char 𝕂` is retired.
    The instance's `serves` field is the frame's `serves_holds_of_weighted_lookup` (no VCL-specific
    proof needed); `ringChar 𝕂′ = ringChar 𝕂` (`quad_ringChar_eq`).
  * NC kept: `export_count_not_derivable` (the row bounds do not give `3N + P < p`).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.IOField
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1746

open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Chips

#print axioms vcl_serves_of_count
#print axioms quad_ringChar_eq
#print axioms reqCondVCL_any_length
#print axioms serves_holds_of_weighted_lookup
#print axioms export_count_not_derivable

end Nock.RedTeam.Batch1746
