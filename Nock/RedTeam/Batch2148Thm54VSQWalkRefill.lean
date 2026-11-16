/-
  Nock/RedTeam/Batch2148Thm54VSQWalkRefill.lean

  New module `RefillWQ`; additive.

  * `denKey_eval4`: a length-4 key's denominator is `compress` of the padded key;
  * `refillW`: columns `0..135` of the `𝕂′` walk twin trace as the SAME polynomials, the three `𝕂` inverses and
    the two inclusive prefix sums interpolated on `136..150`;
  * **`walkChipH_of_HQ`**: `walkChipHQ` acceptance (with preprocessing) at `chalsQ / pubsQ` gives `walkChipH`
    acceptance (with preprocessing) of `refillW` at `chals / pubs`, when the vectors agree on the leaves
    `< 33` / publics `< 4`, the three row denominators are nonzero and `pubs 4 / 5` are the totals.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RefillWQ

namespace Nock.RedTeam.Batch2148

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms RefillWQ.denKey_eval4
#print axioms RefillWQ.refillW_trace_new
#print axioms RefillWQ.refillW_next_new
#print axioms RefillWQ.walkChipH_of_HQ

end Nock.RedTeam.Batch2148
