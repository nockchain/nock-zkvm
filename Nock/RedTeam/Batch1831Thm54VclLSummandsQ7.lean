/-
  Nock/RedTeam/Batch1831Thm54VclLSummandsQ7.lean

  **The VCL compute summands, round-local.**
  Production `Thm54/VclL/Compute/SummandsQ7.lean`:
  `coinSummand` (one-coin cylinder, `readsOn` from a read-set hypothesis), `srcB_trace_congr`,
  `rowStateOf_of_oneHot`, `srcV_good` (the RF-free decoders read only `goodSrc` = B0 ∪ B1 columns,
  at any challenge / public maps), the four event sets and their congruences, the five summands
  `sumZero` (z, w 1), `sumTiling` (αC, 2N+2), `sumAlphaRoot` (αC, N, empty off the tiling),
  `sumGammaRoot` (γ, 9), `sumPrefix` (γ, 9N) with `readsOn` compiled, `summandsQ7`,
  `decoders_eq_RF`, `rowFacts_outside_core` / `rowFacts_outside_Q7` (the frame's `rowFactsAt` body
  outside the summands at the frame coin map), `root_binds_outside_core`.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.SummandsQ7
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1831

open Nock.NockVMROM.Thm54.VclL.Compute.SummandsQ7

#print axioms coinSummand
#print axioms coinSummand_mem
#print axioms srcB_trace_congr
#print axioms rowStateOf_of_oneHot
#print axioms srcV_good
#print axioms sets_congr
#print axioms alphaSetE_card
#print axioms tilingSetE_card
#print axioms prefixSetE_card
#print axioms sumTiling
#print axioms sumAlphaRoot
#print axioms sumGammaRoot
#print axioms sumPrefix
#print axioms summandsQ7_weights
#print axioms decoders_eq_RF
#print axioms rowFacts_outside_core
#print axioms rowFacts_outside_Q7
#print axioms root_binds_outside_core

end Nock.RedTeam.Batch1831
