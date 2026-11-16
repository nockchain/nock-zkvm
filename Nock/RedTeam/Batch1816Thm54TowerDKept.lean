/-
  Nock/RedTeam/Batch1816Thm54TowerDKept.lean

  **Route (d) phase 2, item 3 — the tower kept-gate list and
  its soundness.**  Production `Thm54/VclL/Compute/TowerKept`:
  `towerKeptGates n b δ` (the Q7 kept groups with the non-linear core Re bodies replaced and the Im
  twins appended, source layout), `towerKeptGates_colsIn` (every body reads only `NoFormR` columns,
  so `reindexE` applies and no column constant moves), `towerKept_sound` (acceptance at the
  pull-back gives `TowerKeptHolds`: every kept typed gate holds in `𝕂′` at `towerEnv309`).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerKept
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1816
end Nock.RedTeam.Batch1816

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerKept_sound
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerKeptGates_colsIn
