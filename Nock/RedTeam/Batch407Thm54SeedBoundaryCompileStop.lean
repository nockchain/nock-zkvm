/-
  Nock/RedTeam/Batch407Thm54SeedBoundaryCompileStop.lean

  The written full-RAP counterexample
  (`Batch407Thm54SeedBoundaryRapAttack.lean`) hangs the elaborator after
  `Batch396` replay: ~3.5 GiB RSS, no olean, `maxHeartbeats 2000000` does
  not fire (kernel/unfold of `package73`, not a `decide`). The twelve
  `memorySubst` pin bodies were moved to `Batch407Bodies` (package-free
  cone) and compile. Leaves compile. The `SatisfiesWithPreprocessing`
  claim at the old chip is therefore **source-only**.

  Finding does **not** downgrade: no rejecting gate of the old chip was
  found.

  Paper re-read at source: the paper.
-/
import Nock.RedTeam.Batch407Thm54SeedBoundaryLeaves
import Nock.RedTeam.Batch407Thm54SeedBoundaryBodies

set_option autoImplicit false

namespace Nock.RedTeam.Batch407Stop

/-- The written RAP attack file does not produce an olean. -/
def fullRapAttackCompiled : Bool := false

theorem fullRapAttackCompiled_is_false : fullRapAttackCompiled = false := rfl

def stopReason : String :=
  "Batch407Thm54SeedBoundaryRapAttack hangs elaborating package73 (3.5GiB, no heartbeat fire); Bodies+Leaves compile; no rejecting gate of the old chip"

theorem stop_is_engineering : fullRapAttackCompiled = false :=
  fullRapAttackCompiled_is_false

end Nock.RedTeam.Batch407Stop
