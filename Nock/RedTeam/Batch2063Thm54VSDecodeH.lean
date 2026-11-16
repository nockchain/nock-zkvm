/-
  Nock/RedTeam/Batch2063Thm54VSDecodeH.lean

  **Decode of a served walk key.**  Additive.
  New module `Thm54/VclL/Handle/DecodeH.lean`: `decode_key` (five base entries equal to `recF r`
  decode through `natOf` and the kind bits to `r`), `exportRec_bounds`, and **`walk_hHX_of_served`**:
  a walk row whose consumed key is among the cell twin's provided keys (`ServeH.keys_served`)
  satisfies `walkH_records_genuine`'s `hHX` at that row, against the cell table read off the
  restricted cell trace.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.DecodeH

namespace Nock.RedTeam.Batch2063

open Nock.NockVMROM.Thm54.VclL.Handle.DecodeH

#print axioms decode_key
#print axioms exportRec_bounds
#print axioms walk_hHX_of_served

end Nock.RedTeam.Batch2063
