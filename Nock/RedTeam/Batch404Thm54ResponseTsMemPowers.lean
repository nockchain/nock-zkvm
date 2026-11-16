/-
  Nock/RedTeam/Batch404Thm54ResponseTsMemPowers.lean

  **`response_ts_mem_powers`.**

  Outside `optimizedFailureEvent`, hostile LIO identifies responses with
  requests.  Request timestamps are
  `ln₀ · α^{S+j+1}` with `ln₀ = 1`.  Reducing mod `orderOf α` (needs `α ≠ 0`)
  puts every response `ts` in `⟨α⟩` below the order — the finder hyp of
  `memExponent` (`Batch399` / case (b)).

  `α ≠ 0` discharges from the priced α-collision event when
  `|hostileRequests| ≥ 2`; otherwise it is an explicit hyp.
-/
import Nock.NockVMROM.Thm54.ResponseTsMemPowers
import Nock.RedTeam.Batch400Thm54MemWrapTransfer

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch404

open Nock.NockVMROM.Thm54.ResponseTsMemPowers

noncomputable abbrev response_ts_mem_powers :=
  @Nock.NockVMROM.Thm54.ResponseTsMemPowers.response_ts_mem_powers

noncomputable abbrev response_ts_mem_powers_of_two :=
  @Nock.NockVMROM.Thm54.ResponseTsMemPowers.response_ts_mem_powers_of_two

noncomputable abbrev MemPower :=
  @Nock.NockVMROM.Thm54.ResponseTsMemPowers.MemPower

theorem hyp_was_remaining :
    "response_ts_mem_powers" ∈ Nock.RedTeam.Batch400.transferRemainingHyps := by
  decide

#check response_ts_mem_powers
#check response_ts_mem_powers_of_two

end Nock.RedTeam.Batch404

#print axioms Nock.NockVMROM.Thm54.ResponseTsMemPowers.response_ts_mem_powers
#print axioms Nock.NockVMROM.Thm54.ResponseTsMemPowers.response_ts_mem_powers_of_two
#print axioms Nock.RedTeam.Batch404.hyp_was_remaining
