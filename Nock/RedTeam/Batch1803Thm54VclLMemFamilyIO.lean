/-
  Nock/RedTeam/Batch1803Thm54VclLMemFamilyIO.lean

  **The memory side's IO fields of `vclMemFamily`.**
  Production: `VclL/Chips/MemFamilyVCL.lean`.

  At `Φ := frameVCL`, `I := ioSpecVCLQuad δ`, `Kio := Quad δ` (`δ = algebraMap F K δF`),
  `S := shapeV hT hP` (`shapeVCL … 225 112 Cell.colRoundT Path.colRoundT`), `m := RV.mVCL`:
  * `chip` / `chip_width`: `vclChip` (table 0 `cellChipOk`, table 1 `pathChipOk`, `okOf V t`,
    `chalsVCL δF χ`, publics `pubsC` / `pubsP`), `vclChip_width`;
  * `respRecords` / `internal`: `vclResp`, `vclInternal` (B0/B1 columns only, no coin, no public);
    `respRecords_round` / `internal_round` at `respRound = 1`: `vclResp_round`, `vclInternal_round`
    (read sets `qLt`, decided by `rfl`);
  * `ioFacts`, `ioFacts_records`, `ioFacts_length` (`D / 2D / P`), `internal_length` (`2D / P / 0`),
    `internal_ne_zero`, `serves`: `vclIoFacts`, `vclIoFacts_records`, `vclIoFacts_length`,
    `vclInternal_length`, `vclInternal_ne_zero`, `vcl_serves`.
  * NC: the read-set instrument rejects a key reading a B2 inverse column or a public slot (such a
    key would make `respRecords_round` false: B2 is sampled after the IO coins).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.MemFamilyVCL
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1803

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

/-- **NC**: a record key reading the B2 role `vProvInv` fails the read-set check. -/
theorem nc_b2_key_rejected {F : Type} [Field F] : qLt 18 129 [(QE.var Cell.vProvInv : QE F)] = false := rfl

/-- **NC**: a record key reading a public slot fails the read-set check. -/
theorem nc_pub_key_rejected {F : Type} [Field F] : qLt 18 129 [(QE.pub 0 : QE F)] = false := rfl

#print axioms vclChip_width
#print axioms vclResp_round
#print axioms vclInternal_round
#print axioms vclIoFacts
#print axioms vclIoFacts_records
#print axioms vclIoFacts_length
#print axioms vclInternal_length
#print axioms vclInternal_ne_zero
#print axioms vcl_serves
#print axioms nc_b2_key_rejected
#print axioms nc_pub_key_rejected

end Nock.RedTeam.Batch1803
