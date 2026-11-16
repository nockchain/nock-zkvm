/-
  Nock/RedTeam/Batch2082Thm54VSRowDecode.lean

  **A `computeChipVCLH` row decodes to
  `LocalVS.RowSem`.**  Additive.  New module `Thm54/VclL/Handle/RowDecodeVS.lean`:
  * `hdF` / `rowOf` (handles `(kind = 1, natOf value)`, state from the one-hot index);
  * `activeXRecs` / `activePRecs` (the consumed export / walk records), `XOK` / `POK` (served genuine
    records on a denotation);
  * **`rowSem_of_chip`**: base template gates + `RowSel` + `PrimeFieldElems 𝔽` + `11 < char 𝔽` +
    `XOK`/`POK` on the consumed records ⇒ `RowSem D (char 𝔽) (rowOf eF j₀)`, every state; OP5 "≠"
    only from `neGate` (kind difference or atom-value inverse) on the leaves, with the leaves equal to
    the operands (`z1 = 1`) or read by the walk pair at a common axis (`z1 = 0`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVS

namespace Nock.RedTeam.Batch2082

open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVS

#print axioms xmem
#print axioms pmem
#print axioms pairmem
#print axioms cell3_rec
#print axioms walk_rec
#print axioms rowSem_of_chip

end Nock.RedTeam.Batch2082
