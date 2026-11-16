/-
  Nock/RedTeam/Batch1826Thm54VclLMemBridge.lean

  **The B0 bridge for `response_sound`.**
  Production: `VclL/Chips/MemSoundVCL.lean` §5.

  `rowsOfTr_eq`: the round-0 rows read by the summands and the served nouns (`rowsOfTr`, B0 columns
  only, through `b0Trace`) ARE `(cellTableOf … (chalsVCL δF χ) (pubsC δF ρ y) (QC …)).map (·.b0)`,
  the round-0 rows of the chip's cell table on which `cellTable_accepts_of_lookup` (T1 / T3) runs —
  so `vclSummands_good` and `decodedNoun` speak about the table T1 decodes.  `cellB0Of_congr`,
  `round_cell0`: the read set (`< 129`, all round 0).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.MemSoundVCL
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1826

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

#print axioms rowsOfTr_eq
#print axioms cellB0Of_congr
#print axioms round_cell0

end Nock.RedTeam.Batch1826
