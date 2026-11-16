/-
  Nock/RedTeam/Batch2062Thm54VSServeH.lean

  Additive.
  New module `Thm54/VclL/Handle/ServeH.lean`: a twin denominator is `FiniteIO.compress ⟨γH, ρH⟩` of
  the lifted key (`denKey_eval`, `walk_den_eq` for 4-entry records padded by `0`); the cell
  providers `(keyH, mh)` sum to `pubs 4`, the walk's consumed keys to `pubs 4`, the walk's handle
  walk records `(recLH/recRH, mL/mR)` to `pubs 5`, every denominator nonzero by the inverse gates;
  `keys_served`: the three-party balance (compute + walk consumers vs cell providers) outside
  `IOFailureEventW` (which contains the pole-hit event, so the pole is priced, not assumed).
  NOT here: the compute consumers' list and sum (slot batching), the decode to `hHX`, the summand.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ServeH

namespace Nock.RedTeam.Batch2062

open Nock.NockVMROM.Thm54.VclL.Handle.ServeH

#print axioms denKey_eval
#print axioms served_of_balance
#print axioms cell_provs_den
#print axioms cell_provs_sum
#print axioms walk_den_eq
#print axioms walk_reqs_den
#print axioms walk_reqs_sum
#print axioms walk_provs_den
#print axioms walk_provs_sum
#print axioms keys_served

end Nock.RedTeam.Batch2062
