/-
  Nock/RedTeam/Batch383Thm54BindsHypsOfSeed.lean

  **`TracesBindsHyps` at the sampled seed.**

  `TracesBindsHyps` stays a named hypothesis (`∀ z, BindsAt`).
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesCore

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch383

open Nock.NockVMROM.Thm54.StrategyOfTracesCore

/-- Named remaining join obligations. -/
def bindsRemaining : List String :=
  ["ComputeJoinSound", "BindsAt_sampled_seed", "TracesBindsHyps"]

theorem bindsRemaining_length : bindsRemaining.length = 3 := by
  decide

#check strategyOfTraces_bindsAtCoin
#check strategyOfTraces

end Nock.RedTeam.Batch383

#print axioms Nock.RedTeam.Batch383.bindsRemaining_length
