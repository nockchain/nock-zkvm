/-
  Nock/RedTeam/Batch1805Thm54VclLWalkQ7.lean

  **Walk, root_binds and V_comp at the Q7 chip.**
  Production `Thm54/VclL/Compute/WalkSatQ7.lean`:
  * `RowFactsQ7.of_sat`: acceptance at `computeChipVCLQ7` (injective nodes) gives the row facts;
  * `q7_walkSat`, `q7_walk_out`, `q7_bfsValid`, `q7_tiling`, `q7_root_binds`, `vcomp_at`, coin-map
    parametric (coins = slot values `alphaQ`/`gammaQ`/`zQ` of `chalV`, publics `initQ`/`seedQ`);
  * at frameVCL coins (`chalVQ7`, `pubVQ7`): `frame_coins`, `frame_rowFacts`, `frame_vcomp_at`,
    `frame_root_binds` (walk coins chi0/chi1, NPR seed chi2).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.WalkSatQ7
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1805

open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7

#print axioms walk_sources_q7
#print axioms queue_sources_q7
#print axioms RowFactsQ7.of_sat
#print axioms q7_walkSat
#print axioms q7_walk_out
#print axioms q7_bfsValid
#print axioms q7_tiling
#print axioms vcomp_at
#print axioms q7_root_binds
#print axioms frame_coins
#print axioms frame_rowFacts
#print axioms frame_vcomp_at
#print axioms frame_root_binds

end Nock.RedTeam.Batch1805
