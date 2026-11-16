/-
  Nock/RedTeam/Batch2125Thm54VSHonestPin.lean

  Additive;
  nothing existing changed; no handle accumulator, coin or IO summand touched.  `hat_of_run` (`hat` from
  `RunBoundedBy`), `computeChipVCLH_honest_sat_VS_pinned` and `hcomp_pinned` (compute and memory side share
  ONE cell list `H.d.cells = (demandH2 (runRowsH t)).cells`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestPinH

set_option autoImplicit false

namespace Nock.RedTeam.Batch2125

open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

#print axioms atomsLt_of_boundedBy
#print axioms rowOfSkelH_sf_bounded
#print axioms hat_of_run
#print axioms pinned_cells
#print axioms computeChipVCLH_honest_sat_VS_pinned
#print axioms hcomp_pinned

end Nock.RedTeam.Batch2125
