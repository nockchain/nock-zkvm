/-
  Nock/RedTeam/Batch1862Thm54TowerDNodeRec.lean

  **Tower RowFactsQ7, 409-wide table, tower node_records.**
  `towerRowFactsQ7`: `RowFactsQ7` at
  the tower gather from acceptance at `computeChipVCLQ7T` (obl = `towerRowObl`, masks from the
  preprocessing binding).  `tableVCLT hC` (width 409; Im FP columns round 1, inverse/acc Im round 2:
  UNCONFIRMED placement) with `WideTable` instance.  `rowLabel_fst_of_selAt` (any gather),
  `towerSerial_eq_row` (serial column from `TowerRowHolds.serial` + masks), and `towerNodeRecordsQ7`:
  `node_records_Q7G` at `towerGather`/`towerReader`/`tableVCLT` from tower acceptance (hypotheses: coin
  facts `hz`/`hzi`, `hadj`, `hNp`, `hchar`).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerNodeRecQ7
import Nock.NockVMROM.Thm54.VclL.Compute.CompSoundnessVCL

set_option autoImplicit false

namespace Nock.RedTeam.Batch1862
end Nock.RedTeam.Batch1862

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms TowerD.towerRowFactsQ7
#print axioms TowerD.tableVCLT_wide
#print axioms TowerD.rowLabel_fst_of_selAt
#print axioms TowerD.towerSerial_eq_row
#print axioms TowerD.towerNodeRecordsQ7
#print axioms CompSoundnessVCL.compSoundnessVCL
