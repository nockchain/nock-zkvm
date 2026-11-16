/-
  Nock/RedTeam/Batch1857Thm54TowerDGatherLaws.lean

  **The probe.**  `CoordGather` gains `base_eq` / `baseNext_eq` / `shift`; both instances discharge them;
  `oneHot_of_base15G` (any gather) recovers `oneHot_of_base15` at `ofBasis` (`oneHot_of_base15_viaG`).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerGather
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1857
end Nock.RedTeam.Batch1857

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7.CoordGather.ofBasis
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.towerGather
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7.oneHot_of_base15G
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7.oneHot_of_base15_viaG
