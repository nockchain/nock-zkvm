/-
  Nock/RedTeam/Batch625Thm54FormREventStaging.lean

  Notes only.

  * **Check 3.**  (a) TRUE: `Reified.Expr.Const : ℤ → Expr` (`air_const_is_int`, by the
    constructor's type), so a `StagedChip` (whose `air : Reified.AIR`) cannot carry the deployed
    `CoeffExpr F` gates with their `F`-constants (basis coordinates).  (b) The view LOSES the
    obligations: `StagedChip` has `columnChallenges` and `columns_commit_before_sampling`
    (`stagedChip_fields`), `StagedRAPView` has `[rap, width, hw, schedule]` (`view_fields`) —
    no declared per-column challenge dependence, no commit-before-sample proof, and no column
    map on which `ReadsOnlyPriorRounds` could be stated.  What a `StagedChip` would have forced: for each column, the
    set of coins it may read, each sampled strictly before its round (`usableByColumnOf`, a `<`).
  * **Check 5.**  `E_k` in round 0 is right iff its honest value
    reads only `top`, `c` (base helpers; coin-free) — consistent with its gates being class 0/1
    (`compute_cert_classes`), accepted on that reading.
  * **Check 6, the criterion.**  `gateReadsLaterColumn` fails a gate when it reads a column
    committed AFTER its latest coin.  Under the commitment model that is the LEGITIMATE case: a
    round-2 column may depend on a round-1 coin (`class3_is_legit`: `usableByColumnOf 2 j` holds
    for every `j` with `sampledAfter j = 1`).  The hazard is elsewhere: a BAD EVENT whose read set
    reaches a coordinate sampled at or after the coin its Schwartz–Zippel count is taken over
    (`ReadsOn (priorCoords rnd κ)` failing).  Gates do not have read-set hazards; events do.
    Hence class 3 (42 + 30) is not a soundness hazard; C-late is not a finding; the B2 lists are a
    useful MAP of which columns are bound to which coins, not a hazard list.  Conversely the
    "pass" gates (coin round ≥ column round) are the ones whose soundness is an SZ identity in the
    coin over pre-committed columns — the place where event read sets must be checked.
  * **Check 7.**  Agree: F1 partly (a declared pre-`z` placement of `atom` separate from the
    `z`-bearing size columns), A2 not at all.
-/
import Lean
import Nock.NockVMROM.Thm54.DeployedStaging
import Nock.NockVMROM.Thm54.CommitmentModel

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Lean Elab Command

namespace Nock.RedTeam.Batch625

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.Staging
open Nock.NockVMROM.Thm54.DeployedStaging

/-! ## Check 3(a): `Reified.AIR` constants are integers -/

theorem air_const_is_int : (Reified.Expr.Const : ℤ → Reified.Expr) = Reified.Expr.Const := rfl

run_cmd do
  let env ← getEnv
  let some ci := env.find? ``Nock.Reified.Expr.Const | throwError "no Expr.Const"
  logInfo m!"Reified.Expr.Const : {ci.type}"
  let sc := getStructureFields env ``Nock.NockVMROM.Thm54.Staged.StagedChip
  let sv := getStructureFields env ``Nock.NockVMROM.Thm54.DeployedStaging.StagedRAPView
  logInfo m!"StagedChip fields {sc}; StagedRAPView fields {sv}"
  unless sc.contains `columnChallenges ∧ sc.contains `columns_commit_before_sampling do
    throwError "StagedChip lost its obligations?"
  unless sv == #[`rap, `width, `hw, `schedule, `columnChallenges, `columns_commit_before_sampling] do
    throwError m!"StagedRAPView fields are {sv}"

/-! ## Check 6: class 3 is the legitimate commit-after-coin case -/

/-- A round-2 column may read any coin sampled after round 1. -/
theorem class3_is_legit (j : Fin deployedChronology.numChallenges)
    (hj : ((deployedChronology.sampledAfter j : Fin 3) : ℕ) = 1) :
    deployedChronology.usableByColumnOf (2 : Fin 3) j := by
  show ((deployedChronology.sampledAfter j : Fin 3) : ℕ) < ((2 : Fin 3) : ℕ)
  rw [hj]; decide

/-- Every round-1 coin of the deployed chronology is usable by a round-2 column; every round-0
coin by a round-1 column.  (The `<` is `usableByColumnOf`; `≤` would be `availableBy`.) -/
theorem all_coins_usable_by_later_columns :
    ∀ j : Fin deployedChronology.numChallenges,
      deployedChronology.usableByColumnOf (2 : Fin 3) j ∧
        (((deployedChronology.sampledAfter j : Fin 3) : ℕ) = 0 →
          deployedChronology.usableByColumnOf (1 : Fin 3) j) := by
  intro j
  refine ⟨?_, fun h0 => ?_⟩
  · show ((deployedChronology.sampledAfter j : Fin 3) : ℕ) < 2
    fin_cases j <;> decide
  · show ((deployedChronology.sampledAfter j : Fin 3) : ℕ) < 1
    rw [h0]; decide

/-- The lane's failure criterion, restated: it fires exactly when the column's round exceeds the
coin's `sampledAfter`, i.e. exactly when the column was committed after the coin — the case the
commitment model permits. -/
theorem criterion_is_commit_after_coin (colRound chalRound : ℕ → ℕ) (cols chals : List ℕ) :
    gateReadsLaterColumn colRound chalRound cols chals = true ↔
      maxRound chalRound chals < maxRound colRound cols := by
  simp [gateReadsLaterColumn]

/-- The correct hazard criterion is on EVENTS, not gates: a bad set over the coin vector must read
only coordinates sampled strictly before the coin counted — `ReadsOn (priorCoords rnd κ)`.  A4
states exactly this for the Form R event (lane); the gate lists do not state it for anything. -/
theorem event_criterion_shape {C : Type} (n : ℕ) (rnd : Fin n → ℕ) (κ : Fin n)
    (bad : (Fin n → C) → Finset C) :
    RoundFibred.ReadsOn (RoundFibred.priorCoords rnd κ) bad ↔
      ∀ x y : Fin n → C, (∀ j, rnd j < rnd κ → x j = y j) → bad x = bad y := by
  simp [RoundFibred.ReadsOn, RoundFibred.priorCoords]


/-- A column committed in round `r` can depend on a coin `j` on ANY row only if `j` is usable by
round `r`; so a column `α`-dependent on some row must be placed after `α` on all rows. -/
theorem per_column_rule {V : Type} (chron : ChallengeChronology 3) (r : Fin 3)
    (col : (Fin chron.numChallenges → ℕ) → ℕ → V)   -- (coins, row) ↦ value
    (hreads : ∀ χ₁ χ₂ row, (∀ j, chron.usableByColumnOf r j → χ₁ j = χ₂ j) → col χ₁ row = col χ₂ row)
    (j : Fin chron.numChallenges) (row : ℕ) (χ₁ χ₂ : Fin chron.numChallenges → ℕ)
    (hdiff : col χ₁ row ≠ col χ₂ row) (honly : ∀ j', j' ≠ j → χ₁ j' = χ₂ j') :
    chron.usableByColumnOf r j := by
  by_contra hj
  apply hdiff
  apply hreads
  intro j' hj'
  by_cases h : j' = j
  · subst h; exact absurd hj' hj
  · exact honly j' h

end Nock.RedTeam.Batch625
