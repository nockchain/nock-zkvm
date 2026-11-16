/-
  Nock/RedTeam/Batch2141Thm54VSQExportBalance.lean

  **The `𝕂′` export LogUp identity at an accepted VSQ coin** (REPORT-Q2 item 1,
  second half, export side).  New module `BalanceVSQ`; additive.

  * bridges: `coinsCV_VSQ` (compute `𝕂′` coins at `chalVHQ` are `(γH′, ρH′)`), `pubX_VSQ` / `pubP_VSQ`
    (terminals `ρ₃ / ρ₄`), `chalsVSQ_coins` (memory leaves `33/35, 34/36` are `(γH′, ρH′)`),
    `pubsCHQ_term` (`ρ₃ + yH′`), `pubsWHQ_termX` / `_termP` (`yH′`, `ρ₄`);
  * list sums: `cell_provs_denQ` / `cell_provs_sumQ`, `walk_reqs_denQ` / `walk_reqs_sumQ`;
  * **`export_sumQ`**: at every `AcceptsG`-accepted VSQ coin, under `V.Checks` and nonzero compute path
    denominators, `Σ_{compX ++ walkX} compress′(lift r)⁻¹ = Σ_{cell} mh · compress′(lift key)⁻¹` at
    `(γH′, ρH′)` — the `hsum` input of `BalanceQ.logup_descends`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.BalanceVSQ

namespace Nock.RedTeam.Batch2141

open Nock.NockVMROM.Thm54.VclL.Handle

#print axioms BalanceVSQ.coinsCV_VSQ
#print axioms BalanceVSQ.pubX_VSQ
#print axioms BalanceVSQ.pubP_VSQ
#print axioms BalanceVSQ.chalsVSQ_coins
#print axioms BalanceVSQ.pubsCHQ_term
#print axioms BalanceVSQ.pubsWHQ_termX
#print axioms BalanceVSQ.pubsWHQ_termP
#print axioms BalanceVSQ.cell_provs_sumQ
#print axioms BalanceVSQ.walk_reqs_sumQ
#print axioms BalanceVSQ.export_sumQ

end Nock.RedTeam.Batch2141
