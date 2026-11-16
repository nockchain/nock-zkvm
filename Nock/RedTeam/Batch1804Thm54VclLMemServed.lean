/-
  Nock/RedTeam/Batch1804Thm54VclLMemServed.lean

  **The served-noun fields of `vclMemFamily`.**
  Production: `VclL/Chips/MemSoundVCL.lean`.

  * `servedKeys` / `servedKeys_length`: `vclServedKeys` (the provider keys at the B0 message, read
    through `b0Trace`), `vclServedKeys_length` (`≤ Σ vclRespBound = D + 2D + P`);
  * `servedRoot` / `served`: `vclServedRoot`, `vclServed` (the B0 decode `preZNounOfTable` of the
    cell table's round-0 rows `cellRowsB0`, capped at `2^110`; export side child; path `Noun.slot`);
  * `window` / `windowBound` / `window_le` / `served_leaves_le`: `vclWindow = 2^110`,
    `vclServed_leaves_le` (every B0 message, every key).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.MemSoundVCL
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1804

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

/-- Positive control for the receipt: `Noun.slot 1` serves the root itself (the repair axis). -/
theorem slot_one_serves (n : Nock.Noun) : Nock.Noun.slot 1 n = some n := by simp [Nock.Noun.slot]

#print axioms vclServedKeys_length
#print axioms vclServed_leaves_le
#print axioms validity_axis_one_serves
#print axioms slot_one_serves

end Nock.RedTeam.Batch1804
