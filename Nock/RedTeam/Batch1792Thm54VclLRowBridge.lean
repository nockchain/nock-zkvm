/-
  Nock/RedTeam/Batch1792Thm54VclLRowBridge.lean

  **The row-local half of the VCL-L chip ⇒ row-model
  bridge.**  Production: `Thm54/VclL/Chips/RowBridge.lean`.

  * `cellChip_rowLocal` / `pathChip_rowLocal`: every gate of either chip vanishes at every row node;
  * `next_node` / `traceNext_eq`: under R-LC8's `Checks.memAdjacent` the next-row leaves read row
    `i + 1`;
  * `cellChip_masks` / `pathChip_masks`: the fixed columns are `[i = 0]`, `[i = n − 1]`;
  * `gather_chal_*` / `gather_pub_*`: the gathered `𝕂` coin / public leaves are the supplied ones;
  * `cellChip_serial`: the first row-model consequence — the serial column is `i` at row `i`
    (`Table.SerialOK` in the field).
  Remaining (unconfirmed): `RowOK` (limbs/bits to ℕ, `𝕂′` cons/atom recombination), `ValidityServed`
  and `Chain` edges via the LogUp telescoping, the `vclMemFamily` soundness fields.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.RowBridge
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1792

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

#print axioms cellChip_rowLocal
#print axioms pathChip_rowLocal
#print axioms next_node
#print axioms traceNext_eq
#print axioms cellChip_masks
#print axioms pathChip_masks
#print axioms sum_slotVal
#print axioms gather_chal_cell
#print axioms gather_pub_path
#print axioms cellChip_serial

end Nock.RedTeam.Batch1792
