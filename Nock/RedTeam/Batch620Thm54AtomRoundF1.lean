/-
  Nock/RedTeam/Batch620Thm54AtomRoundF1.lean

  * `Batch601.atom_column_in_round_zero` says the memory RAP has ONE round of width 181 — it
    holds of every source column, the size columns `6..8` included (F1).
  * The measured staging (`DeployedStaging.memoryColRound`) separates them: `atom` (180) is
    round 0, before `z` is sampled; size `6..8` and leaf `12..14` are round 1, after `z`.
  * **Limit, stated:** the separation is a property of the STAGING, not of acceptance:
    `RAP.Satisfies` ignores `k` / `wRAP` (`rap_satisfies_ignores_rounds`), so the chip does not
    enforce it.
-/
import Nock.NockVMROM.Thm54.DeployedStaging
import Nock.RedTeam.Batch601Thm54PreseedAtomMemoryGate

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch620

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedStaging

/-- The measured map separates `atom` from the `z`-bearing columns. -/
theorem atom_separated_from_size :
    memoryColRound OptimizedMemoryGateBasis.atomCol = 0 ∧
      (∀ c ∈ [6, 7, 8, 12, 13, 14], memoryColRound c = 1) ∧
      ((deployedChronology.sampledAfter FormRAxisEvent.seedIdx : Fin 3) : ℕ) = 0 := by
  refine ⟨rfl, ?_, rfl⟩
  decide

/-- Positive control: the single-round reading does NOT separate them (both `< 181`). -/
theorem single_round_does_not_separate :
    OptimizedMemoryGateBasis.atomCol < 181 ∧ (6 : ℕ) < 181 ∧ (14 : ℕ) < 181 := by decide

/-- The staging is not enforced by acceptance. -/
theorem staging_not_enforced {F : Type*} [Field F] [DecidableEq F] (R : Framework.RAP F)
    (k' : ℕ) (w' : Fin k' → ℕ) (hw : R.w = ∑ i, w' i) (P : Fin R.w → Polynomial F) :
    R.Satisfies P ↔ ({R with k := k', wRAP := w', w_eq := hw} : Framework.RAP F).Satisfies P :=
  rap_satisfies_ignores_rounds R k' w' hw P

end Nock.RedTeam.Batch620

#print axioms Nock.RedTeam.Batch620.atom_separated_from_size
#print axioms Nock.RedTeam.Batch620.staging_not_enforced
