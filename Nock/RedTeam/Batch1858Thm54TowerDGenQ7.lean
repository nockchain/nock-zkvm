/-
  Nock/RedTeam/Batch1858Thm54TowerDGenQ7.lean

  **The Q7 decoder chain over `ChipDataG`, in place.**
  `WalkSatQ7` (rows, one-hot, labels, `root_binds`) and `TopoQ7` are
  stated over `ChipDataG` (a `CoordGather`); `CoreQ7` / `NodeRecQ7` / `SummandsQ7` / `CompTreeVCL` consume
  them at `cdOfG V = (cdOf V).toG` (the 3-limb gather, by `rfl`).  The chip-specific acceptance lemmas
  `RowFactsQ7.of_sat` / `of_satS` keep their `ChipData` hypotheses and conclude `RowFactsQ7 D.toG`.
  The regression receipt: `compSoundnessVCL` and the 309-route corollaries keep their axioms.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.CompSoundnessVCL
import Nock.NockVMROM.Thm54.VclL.Compute.TowerGather

set_option autoImplicit false

namespace Nock.RedTeam.Batch1858
end Nock.RedTeam.Batch1858

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms WalkQ7.RowFactsQ7.of_sat
#print axioms WalkQ7.RowFactsQ7.of_satS
#print axioms WalkQ7.vcomp_at
#print axioms WalkQ7.q7_root_binds
#print axioms WalkQ7.frame_rowFacts
#print axioms WalkQ7.frame_root_binds
#print axioms WalkQ7.q7_obligations_vcompG
#print axioms TopoQ7.q7_topology
#print axioms CoreQ7.rowFacts_core_Q7
#print axioms CoreQ7.rowFacts_Q7
#print axioms NodeRecQ7.node_records_Q7
#print axioms CompSoundnessVCL.compSoundnessVCL
#print axioms TowerD.towerRowObl
