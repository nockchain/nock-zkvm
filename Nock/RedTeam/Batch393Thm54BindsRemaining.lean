/-
  Nock/RedTeam/Batch393Thm54BindsRemaining.lean

  **`TracesBindsHyps` stays a hypothesis.**

  Sampled-seed `ComputeJoinSound` / `RecordHalfJoin` not proved.
  `strategyOfTraces` still takes `hbinds`.
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.RedTeam.Batch383Thm54BindsHypsOfSeed

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch393

/-- Re-export: binds hyp is still named, not a theorem. -/
def bindsStillNamed : String := "TracesBindsHyps"

theorem bindsStillNamed_eq : bindsStillNamed = "TracesBindsHyps" := rfl

end Nock.RedTeam.Batch393

#print axioms Nock.RedTeam.Batch393.bindsStillNamed_eq
