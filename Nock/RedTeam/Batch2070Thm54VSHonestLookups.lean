/-
  Nock/RedTeam/Batch2070Thm54VSHonestLookups.lean

  1. `demandH`: the VS honest demand (handle nouns `s f e sf1 sf2 m` of every row as binds, no export
     reads, the walk reads unchanged).  `handle_cells_mem`: every cell among the twelve handles of every
     honest row (`hn (rowOfSkel _)`) is a row of its closure table; `demandH_one_row`: one row per noun.
     On both toys the table equals the old demand's table (`decide +kernel`).
  2. `accGatesH_honest`: the 18 accumulator gates (cast `ℚ`-template) at a prefix-sum fill with the
     totals as publics; `slotGate_honest`: a slot gate at inverse `A / D` under pole-freeness;
     `export_balance`: the consumed export records of all rows reindex onto the cell table with the
     honest multiplicity (`exportEntries`, `entryRec_eq_expKey`, injective keys).
  3. FINDING (`op3_witness_unhosted`, concrete): `rowOfSkel` leaves the OP3 witness columns at `atom 0`.
  Remaining: the path side of the accumulators and the walk twin's honest records, the 9 compute-walk
  gates over handle labels, the `mixedCompile` lowering, the provider balance on the walk side.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestDemandToys
import Nock.NockVMROM.Thm54.VclL.Handle.HonestLookups

set_option autoImplicit false

namespace Nock.RedTeam.Batch2070

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms handle_cells_mem
#print axioms demandH_one_row
#print axioms toy1_demand_cells
#print axioms toy2_demand_cells
#print axioms accGates_map
#print axioms accGatesH_honest
#print axioms accGatesH_wrong_terminal
#print axioms slotGate_honest
#print axioms slotGate_wrong_inverse
#print axioms sum_reindex
#print axioms exportEntries_cell
#print axioms entryRec_eq_expKey
#print axioms entry_parent_mem
#print axioms export_balance
#print axioms run_rows_sem
#print axioms op3_witness_unhosted

end Nock.RedTeam.Batch2070
