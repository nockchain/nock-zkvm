/-
  Nock/RedTeam/Batch622Thm54FormRReviewRepairs.lean

  * **F1 / F4.**  `StagedRAPView` now carries `columnChallenges` and
    `columns_commit_before_sampling` against `deployedChronology` (`usableByColumnOf`), filled from
    the B1 round map for both deployed views.  The contents are not a self-check of B1's table:
    the `atom` column may read no coin, the `z`-bearing size columns exactly `z, a, b, c`, and the
    `λ` helpers `H`, `T` may read `λ` (`b1_challenge_sets`).
  * **F2.**  `DeployedStaging.typedColsC` / `typedSlotsC` are the compile's read set
    (`.pow _ 0` reads nothing; `lamPow` dropped as the `K`-uniform lower bound);
    `computeTypedClass_eq_C`: the classes are unchanged on all 94 deployed typed sources.
  * **F3.**  Class 3 is the legitimate commit-after-coin case: in every class-3 gate the latest
    coin is usable by the latest column (`class3_coin_usable`).  The hazard criterion is on
    events, `ReadsOn (priorCoords …)`, which A4 states.
-/
import Nock.NockVMROM.Thm54.DeployedStaging

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch622

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedStaging

/-- B1's challenge sets at the columns that matter (indices in `landedVec` order: `3` = `z`,
`6, 7, 8` = `a, b, c`, `10` = `λ`). -/
theorem b1_challenge_sets :
    (roundChallenges (memoryRoundFin ⟨180, by decide⟩)).image Fin.val = ∅ ∧
      (roundChallenges (memoryRoundFin ⟨6, by decide⟩)).image Fin.val = {3, 6, 7, 8} ∧
      (roundChallenges (computeRoundFin ⟨202, by decide⟩)).image Fin.val = ∅ ∧
      10 ∈ (roundChallenges (computeRoundFin ⟨296, by decide⟩)).image Fin.val ∧
      10 ∈ (roundChallenges (memoryRoundFin ⟨15, by decide⟩)).image Fin.val := by
  decide

/-- F3: if a gate is class 3 (latest coin round 1, a round-2 column), the coin is usable by the
column under commit-before-sample: `sampledAfter < round`. -/
theorem class3_coin_usable (cols chals : List ℕ) (colRound chalRound : ℕ → ℕ)
    (h : gateReadsLaterColumn colRound chalRound cols chals = true) :
    maxRound chalRound chals < maxRound colRound cols := by
  simpa [gateReadsLaterColumn] using h




end Nock.RedTeam.Batch622

#print axioms Nock.RedTeam.Batch622.b1_challenge_sets
#print axioms Nock.RedTeam.Batch622.class3_coin_usable
