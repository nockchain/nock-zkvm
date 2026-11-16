/-
  Nock/RedTeam/Batch1737Thm54VclLWalkRows.lean

  **The walk / queue sources at VCL semantics, row
  level.**

  Production: `Thm54/VclL/Compute/WalkRows.lean`.  The R2 walk / queue twins read the 303-hosted
  walk through Form-R-bearing obligations; at `computeChipVCLD` the walk lives in `W0`/`W1`
  (`208..213`, 309 semantics).
  * `ext_gate_zero_vcl`, `conditional_transition_soundness_vcl` (`DecodedTransitionSourcesVCL`: the
    76 core coin-free sources at 309 semantics — packed table, always-on, `lnChain`, `walkLn`,
    `walkCountStep309`, `walkAccStep309` — and the sampled-IO sources at positions 78, 81; 79/80 are
    the dropped Form R pins), positive control `decoded309_toVCL`;
  * `queue_sources_vcl` (`queueNonEmpty309`, `queueTiling309` on every row);
  * at the chip: `computeChipVCLD_transition_sources`, `computeChipVCLD_queue_sources`,
    `pullEnv_walk` (the pulled walk limbs are VCL `208..213`).
  Not done: the global `WalkSat` assembly at `W0`/`W1` and `BFSValid` / tiling from it.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.WalkRows
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1737

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms mem_keptCoreIds
#print axioms ext_gate_zero_vcl
#print axioms decoded309_toVCL
#print axioms conditional_transition_soundness_vcl
#print axioms queue_sources_vcl
#print axioms computeChipVCLD_transition_sources
#print axioms computeChipVCLD_queue_sources
#print axioms pullEnv_walk

end Nock.RedTeam.Batch1737
