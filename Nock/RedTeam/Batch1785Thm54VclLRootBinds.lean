/-
  Nock/RedTeam/Batch1785Thm54VclLRootBinds.lean

  **`root_binds` at the VCL layout.**  Production `Thm54/VclL/Compute/RootBindsVCL.lean`: the port of
  `Batch465.deployed_root_label_eq_claim` to the VCL walk on `W0`/`W1`.
  * `root_binds_of_walk` — generic, coin-map free: a `WalkSat` seeded at `RLC^γ(claim label)·α`,
    `out = 0`, first `cur` the RLC of a decoded `Pub`'s label ⇒ `bindFP` of the claim's
    subject / formula / result to `pub.s / f / e`, outside `alphaBadOf (rootDiffP …)` and
    `gammaBadOf`;
  * `vcl_root_cur_eq_claim`, `vcl_root_binds` — the instance through `vcl_walkSat` /
    `vcl_walk_out` (the frame's `root_binds` shape at the first row's one-hot state).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.RootBindsVCL
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1785

open Nock.NockVMROM.Thm54.VclL.Compute.WalkVCL

#print axioms root_binds_of_walk
#print axioms vcl_root_cur_eq_claim
#print axioms vcl_root_binds

end Nock.RedTeam.Batch1785
