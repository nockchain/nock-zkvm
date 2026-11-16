/-
  Nock/RedTeam/Batch1833Thm54VclLCompTreeVCL.lean

  **The tree is rho-free; `node_records` / `root_binds` at the CF chip.**
  Production `Thm54/VclL/Compute/CompTreeVCL.lean`:
  `pubCF_lt`, `toSourceEnv_envsP_pub` / `treeV_pub_irrel` / `treeV_pubCF` (labels read the environment
  only through `toSourceEnv`, whose `pub` reads limbs `< 9` and `20..41`, never the terminals at `42..47`),
  `treeV_label_root`, `coins_pubCF`, `node_records_CF`, `rowStateOf_toSourceEnv`, `root_binds_CF`.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.CompTreeVCL
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1833

open Nock.NockVMROM.Thm54.VclL.Compute.CompTreeVCL

#print axioms treeV_pub_irrel
#print axioms treeV_pubCF
#print axioms treeV_label_root
#print axioms coins_pubCF
#print axioms node_records_CF
#print axioms root_binds_CF

end Nock.RedTeam.Batch1833
