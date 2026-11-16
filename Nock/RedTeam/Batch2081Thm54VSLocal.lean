/-
  Nock/RedTeam/Batch2081Thm54VSLocal.lean

  Additive.  New module `Thm54/VclL/Handle/LocalVS.lean` (pure noun logic over a denotation `D`):
  * `RowVS` / `kids` (= `ChipH.children`) / `RowSem` (L1 decode every row; per-state opcode facts;
    OP5 `Op5Sem`: "=" by handle equality, "≠" by `Differ` or the first-difference walk pair);
  * `defined_step` / `defined_tree` (every subject and result denotes once the root subject does);
  * `local_step` / **`local_all`**: `LocalOK q (skel D ∘ rw)` at every node of a `RowsOK` tree;
    **`holdsF_of_rowsVS`** (through `SVFrameG.holdsF_of_local`);
  * item 6 controls `serials_never_differ`, `differ_controls`, `differ_needs_cell_meaning`;
  * item 8 `state_of_formula`, `rowState_determined`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LocalVS

namespace Nock.RedTeam.Batch2081

open Nock.NockVMROM.Thm54.VclL.Handle.LocalVS

#print axioms defined_step
#print axioms defined_tree
#print axioms local_step
#print axioms local_all
#print axioms holdsF_of_rowsVS
#print axioms serials_never_differ
#print axioms differ_controls
#print axioms differ_needs_cell_meaning
#print axioms state_of_formula
#print axioms rowState_determined

end Nock.RedTeam.Batch2081
