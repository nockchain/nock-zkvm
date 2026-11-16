/-
  Nock/RedTeam/Batch2142Thm54VSQPathBalance.lean

  New module `PathVSQ`; additive.

  * `denKeyQ_ev'`: `denKeyQ_ev` for keys of length `≤ 5` (walk records `recLH / recRH` have length 4);
  * `wDenQ_eq4`, `walk_provs_denQ`, `walk_provs_sumQ`: the walk twin's weighted path providers sum to
    `(pub₆, pub₇)` at the `𝕂′` coins;
  * **`path_sumQ`**: at every `AcceptsG`-accepted VSQ coin, under `V.Checks` and nonzero compute path
    denominators, `Σ_{compP} compress′(lift r)⁻¹ = Σ_{walkP} w · compress′(lift rec)⁻¹` at `(γH′, ρH′)`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.PathVSQ

namespace Nock.RedTeam.Batch2142

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms PathVSQ.denKeyQ_ev'
#print axioms PathVSQ.wDenQ_eq4
#print axioms PathVSQ.walk_provs_denQ
#print axioms PathVSQ.walk_provs_sumQ
#print axioms PathVSQ.path_sumQ

end Nock.RedTeam.Batch2142
