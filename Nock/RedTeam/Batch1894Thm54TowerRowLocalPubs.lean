/-
  Nock/RedTeam/Batch1894Thm54TowerRowLocalPubs.lean

  **Row-local kept gates read no publics.**
  * `AgreeOff` no longer compares publics; `eval_congr_reads_typed` takes `correctedPublicFreeB t = true`.
  * `rowLocal_kept_publicFree` (`decide +kernel`): every kept core id `i < 72` has a public-free typed
    gate (no `.extensionPublic` / `.scalarPublic` leaf).
  * `towerHolds_rowLocal_nonzeroPub`: sanity check.  At a tower env with some non-zero scalar public, the
    zero-publics env `zeroPub T` satisfies the `pubs` clause (`zeroPub_pub`) and `AgreeOff T (zeroPub T)`
    (`agreeOff_zeroPub`), and the row-local gate holds; the conclusion also records
    `(zeroPub T).scalarPublic ≠ T.scalarPublic`.
  Labelled: this shows the two hypotheses are jointly satisfiable on the publics axis; existence of the honest
  `RowMatch` data itself (C1b) is unconfirmed.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowLocal
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.rowLocal_kept_publicFree
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.eval_congr_reads_typed
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerHolds_rowLocal
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.zeroPub_pub
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.agreeOff_zeroPub
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerHolds_rowLocal_nonzeroPub
