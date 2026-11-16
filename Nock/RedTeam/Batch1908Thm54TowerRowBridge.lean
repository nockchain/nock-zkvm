/-
  Nock/RedTeam/Batch1908Thm54TowerRowBridge.lean

  **Bridge C1c `RowMatchT`/`AgreeOffT` -> C2a `RowMatch`/`AgreeOff`.**
  Both copies are kept.

  * `RowMatchT.toRowMatch`, `AgreeOffT.toAgreeOff`: anonymous constructors.
  * `honest_rowMatch_feeds_rowLocal`: at honest data every row-local kept gate (id < 72) holds in
    the tower field at `towerEnv309` (`honest_rowMatch` feeds `towerHolds_rowLocal`).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowBridge
import Nock.RedTeam.Batch1904Thm54TowerGenMap
import Nock.RedTeam.Batch1894Thm54TowerRowLocalPubs

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.RowMatchT.toRowMatch
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.AgreeOffT.toAgreeOff
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honest_rowMatch_feeds_rowLocal
