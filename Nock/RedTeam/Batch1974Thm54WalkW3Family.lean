/-
  Nock/RedTeam/Batch1974Thm54WalkW3Family.lean

  **The memory family's IO fields with the walk chip.**

  Module `VclL/Chips/MemFamilyVCLW.lean` (twin of `MemFamilyVCL.lean`):
  * `shapeVW hT hP = shapeVCL hT hP 225 132 Cell.colRoundT colRoundW` (`colRoundW_layout`: the
    round map is `LayoutW`'s `21 / 72 / 39`); `vclChipW` (table `1` = the walk chip at
    `chalsVCL δF χ`, so the walk coins are `frameVCL` slots `0, 1` = `αC, γ`);
  * `vclRespW` (path accumulator = `walkPRecords`, two per row), `vclInternalW` (export internal =
    `walkXInternal`, one per row), round-1 invariance, `vclIoFactsW` (+ `_records`, `_length`),
    `vclInternalW_ne_zero`, `vcl_servesW`.  Same `frameVCL`, same `RV.mVCL = 5 / 11 / 8`.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.MemFamilyVCLW

set_option autoImplicit false

namespace Nock.RedTeam.Batch1974

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

#print axioms walkChipOk_w
#print axioms walkChipOk_sat
#print axioms goodW_of_ok
#print axioms colRoundW_layout
#print axioms wPRec_congr
#print axioms wXInt_congr
#print axioms vclChipW_width
#print axioms vclRespW_round
#print axioms vclInternalW_round
#print axioms vcl_acceptedW
#print axioms vclIoFactsW
#print axioms vclIoFactsW_records
#print axioms vclIoFactsW_length
#print axioms vclInternalW_ne_zero
#print axioms vcl_servesW

end Nock.RedTeam.Batch1974
