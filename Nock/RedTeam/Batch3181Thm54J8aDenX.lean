/-
  Nock/RedTeam/Batch3181Thm54J8aDenX.lean

  The closed form of the compute `𝕂′` denominators of `computeChipVCLHX`:
  * `denQX_val`: `DX r = compress (γH′, ρH′) (liftRec (keyX m r))` for `r.length ≤ m`;
  * `compress_padK` / `keyX_pad`: zero padding does not move `compress` (service balance at `m = 8`);
  * `consQX_len`: consumed records have length `≤ 5` (`x`, `p`) / `≤ 8` (`s`);
  * `keyX_natKey`: at `ZMod p` the key is the cast of the `ℕ` record of `activeX`;
  * `compute_balanceX_keys`: the compute balances in `compress` form at `coinsCV`;
  * `hden_of_reqs`: `compute_balanceX`'s `hden` from nonzero request denominators (the IO event);
  * `compReqsX_sum`: the compute side of each balance as one request list `compReqsX bl`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8

namespace Nock.RedTeam.Batch3181

open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8

#print axioms keyX_pad
#print axioms compress_padK
#print axioms liftRec_padK
#print axioms denQX_val
#print axioms slotsX_len
#print axioms consQX_len
#print axioms keyX_natKey
#print axioms compute_balanceX_keys
#print axioms hden_of_reqs
#print axioms compReqsX_sum

end Nock.RedTeam.Batch3181
