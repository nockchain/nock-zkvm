/-
  Nock/RedTeam/Batch1822Thm54VclLTopoQ7.lean

  **The VCL compute topology (walk ⇒ `RVT Fcomp`).**
  Production `Thm54/VclL/Compute/TopoQ7.lean`:
  `okLn_pub_cols` (decided: source `Pub` columns `< 47` read no patched coordinate),
  `lnPatch_pub_sfe` / `labelVec_lnPatch` / `childVecN_lnPatch` (the patched decode agrees on every
  label / child fingerprint), `rvt_of_walk` + `children_length_of_rvt` (chip-free: WalkSat at
  `seed = root·α`, `initial_count = α`, `out = 0`, outside the `α`-root and prefix-`γ` events,
  BFS validity, tiling, per-row state + `Vcomp` ⇒ `RVT Fcomp (reconTree …)`, arity `≤ 3`),
  `lblQ` (patched row labels) and `q7_topology` at the Q7 chip (walk publics, `z ≠ 0`, `z⁻¹` pin,
  `α`-root, prefix-`γ`, `α`-tiling).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TopoQ7
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1822

open Nock.NockVMROM.Thm54.VclL.Compute.TopoQ7

#print axioms okLn_pub_cols
#print axioms lnPatch_pub_sfe
#print axioms labelVec_lnPatch
#print axioms childVecN_lnPatch
#print axioms rvt_of_walk
#print axioms children_length_of_rvt
#print axioms lblQ_row
#print axioms q7_topology

end Nock.RedTeam.Batch1822
