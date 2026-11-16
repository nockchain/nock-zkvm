/-
  Nock/RedTeam/Batch4834Thm54J8ComplL3.lean

  The atom
  table's honest rows at gate level for arbitrary ℕ row data (`atomGates_of_rowOK`, `hbase_of_rows`), the atom
  table satisfied and bound at a good coin by both chip views (`atomOK_of_rows`), row nodes `ω^i` (`powNodes_ok`),
  and `hpair` (`hpair_of_binders`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8AW
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom

namespace Nock.RedTeam.Batch4834

open Nock.NockVMROM.Thm54.VclL.Handle

#check @ComplJ8Atom.RowOK
#print axioms ComplJ8Atom.atomGates_of_rowOK
#print axioms ComplJ8Atom.hbase_of_rows
#print axioms ComplJ8Atom.atomOK_of_rows
#print axioms ComplJ8Atom.AtomTab.rowOK_of_valid
#print axioms ComplJ8Atom.AtomTab.cout_last
#print axioms ComplJ8Atom.AtomTab.rows_ok
#print axioms ComplJ8Atom.powNodes_ok
#print axioms ComplJ8Atom.linkOrder_spec
#print axioms ComplJ8Atom.incChain_inc
#print axioms ComplJ8Atom.incChain_ok
#print axioms ComplJ8Atom.stInv_infoOfP
#print axioms ComplJ8Atom.link_gen
#print axioms ComplJ8Atom.conv_at
#print axioms ComplJ8Atom.valid_gen
#print axioms ComplJ8Atom.s4_row
#print axioms ComplJ8Atom.genHyp_j8
#print axioms ComplJ8Atom.valid_j8
#print axioms ComplJ8Atom.row_info
#print axioms ComplJ8Atom.row_cell
#print axioms ComplJ8Atom.hpair_of_binders
#print axioms ComplJ8AW.awOK_present
#print axioms ComplJ8AW.awOK_absent
#print axioms ComplJ8AW.stA_gen
#print axioms ComplJ8AW.stV_gen
#print axioms ComplJ8AW.atomOK_j8
#print axioms ComplJ8AW.awOK_list

end Nock.RedTeam.Batch4834
