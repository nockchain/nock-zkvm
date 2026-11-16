/-
  Nock/RedTeam/Batch1828Thm54VclLMemResponse.lean

  **`response_sound` of `vclMemFamily`.**
  Production: `VclL/Chips/MemResponseVCL.lean`.

  `vcl_response_sound`: for every accumulator `a` and every committed provider record `r` of
  `vclIoFacts h a`, the four conjuncts of `MemSoundnessFamily.response_sound` hold at
  `R := RV.recordViewVCL` (key in `vclServedKeys`; root / child = `enc (seed χ)` of `vclServedRoot` /
  `vclServed`; `Noun.slot (axis) servedRoot = some served`), from the chip-enforced `GoodM`, the
  request LogUp sums, the joint weighted IO exclusion, the consumer count and the summand exclusion
  only.  Ingredients: `cell_rows_genuine` / `row_dn` (T1), `path_record_genuine` (T3,
  `chain_sound_outside` at `skel := []`), the key-read-set lemmas, `natLift_liftQ`.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.MemResponseVCL
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1828

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

#print axioms natLift_liftQ
#print axioms cell_rows_genuine
#print axioms path_record_genuine
#print axioms valid_records_sound
#print axioms export_records_sound
#print axioms path_records_sound
#print axioms vcl_response_sound

end Nock.RedTeam.Batch1828
