/-
  Nock/RedTeam/Batch2088Thm54VSWalkChainSummands.lean

  **The three
  walk-chain exclusions of `rowSem_VS` priced as summands.**  Additive.  New module
  `Thm54/VclL/Handle/WalkChainSumVS.lean`:
  * `dyckVS` (`cellDyckRootSummand` at `frameVS` coins `{2, 3}`, dep `∅`), **`dyck_VS`**;
  * `fpExportIOVS` (the fingerprint-export IO event, accumulator 1, at the IO coins `{4..7}`, dep
    `coinsBelow frameVS 1`, coin-free lists `fpReqs` / `fpProvs`, `fpLists_staged`, `fpLists_at`),
    **`keysExported_VS`** (`walk_keys_exported` at the restricted twins, `reqs = []`, `ρ₁ = 0`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkChainSumVS

namespace Nock.RedTeam.Batch2088

open Nock.NockVMROM.Thm54.VclL.Handle.WalkChainSumVS

#print axioms dyck_VS
#print axioms wOfTrVS_readsOn
#print axioms wOfTrVS_at
#print axioms walkChain_VS
#print axioms fpLists_staged
#print axioms fpLists_at
#print axioms keysExported_VS

end Nock.RedTeam.Batch2088
