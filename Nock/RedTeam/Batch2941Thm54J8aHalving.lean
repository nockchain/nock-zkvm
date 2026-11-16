/-
  Nock/RedTeam/Batch2941Thm54J8aHalving.lean

  The `s10L` wrap (C-2 FINDING `s10L_halving_wraps_goldilocks`) against the walk's axis certificate:
  * the honest binder `haxis` alone does NOT exclude it (it feeds the honest conjunct only; hostile
    walk axes are bounded by the walk chip's depth certificate `len ≤ 61`, axes `< 2^63`);
  * `s10L_wrap_admitted_by_deployed_cert`: the DEPLOYED certificate admits the walk node (`len = 61`)
    whose record is the child `s10L` row's sibling read at `v − 1`, with `v` the wrapped half —
    parent and child `s10L` gates all hold, `HalvingOK` fails (kernel, Goldilocks);
  * minimal gate change: `len + Σ_{i<5} 2^i bᵢ + 29·b₅ − 60 = 0`, exclusion gate dropped (no column,
    no coin): `depthCert60_range` / `_complete`, `len_le_60_of_cert60`,
    `deployed_admits_61_narrowed_rejects`;
  * under it, `HalvingOK` follows from the child chain row alone: `halvingOK_of_child_s10L(_env)`,
    `halvingOK_of_child_s10T(_env)`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HalvingJ8

namespace Nock.RedTeam.Batch2941

open Nock.NockVMROM.Thm54.VclL.Handle.HalvingJ8

#print axioms s10L_wrap_admitted_by_deployed_cert
#print axioms depthCert60_range
#print axioms depthCert60_complete
#print axioms len_le_60_of_cert60
#print axioms deployed_admits_61_narrowed_rejects
#print axioms halvingOK_of_child_s10L
#print axioms halvingOK_of_child_s10T
#print axioms halvingOK_of_child_s10L_env
#print axioms halvingOK_of_child_s10T_env

end Nock.RedTeam.Batch2941
