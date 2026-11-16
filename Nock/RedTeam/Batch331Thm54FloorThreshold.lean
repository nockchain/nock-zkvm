/-
  Nock/RedTeam/Batch331Thm54FloorThreshold.lean

  **Measured floor `p₀` for `rows < p ∧ Λ < p → seedBudgetVcomp < p³`.**

  Least such `p` is **25**.  Compiled negative at `p₀ − 1 = 24` with
  witness `rows = Λ = 23`; compiled positive from 25 (worst case
  `rows = Λ = 24`, and the ∀ implication).  Floor cannot go below 12.
  `seedBudget` / `sizeWindowRootBound` are not tightened.
-/
import Nock.NockVMROM.Thm54.SizeWindowCounting
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.TraceGen.GenSeedVcomp

set_option autoImplicit false

namespace Nock.RedTeam.Batch331

open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.GoodSeed

/-- The measured threshold: least `p` such that
    `∀ rows Λ, rows < p → Λ < p → seedBudgetVcomp Λ rows < p³`. -/
def p0 : ℕ := 25

theorem b331_p0_eq : p0 = 25 := rfl

/-- Tags need only `11 < p`.  `p₀` sits above that. -/
theorem b331_floor_above_tags : 12 ≤ p0 := by
  decide

/-- Exact triangular count at the negative witness. -/
theorem b331_sizeWindow_23 : sizeWindowRootBound 23 = 276 := by
  unfold sizeWindowRootBound
  decide

/-- **Negative at `p₀ − 1`.**  Worst case allowed by `rows < 24` and
    `Λ < 24` already exceeds `24³` -/
theorem b331_negative_at_p0_pred :
    ¬ (seedBudgetVcomp 23 23 < 24 ^ 3) := by
  unfold seedBudgetVcomp seedBudget
  rw [b331_sizeWindow_23]
  decide

/-- The ∀-implication fails at 24 (same witness). -/
theorem b331_implication_fails_at_24 :
    ¬ (∀ rows Λ, rows < 24 → Λ < 24 → seedBudgetVcomp Λ rows < 24 ^ 3) :=
  fun h => b331_negative_at_p0_pred (h 23 23 (by decide) (by decide))

/-- **Positive from `p₀`.**  Worst case `rows = Λ = 24` sits under `25³`.
    Uses the square majorant of `sizeWindowRootBound`, not a `decide` of
    the triangular sum -/
theorem b331_positive_worst_at_p0 :
    seedBudgetVcomp 24 24 < 25 ^ 3 := by
  have hsq : sizeWindowRootBound 24 ≤ 24 * 24 :=
    sizeWindowRootBound_le_square 24
  unfold seedBudgetVcomp seedBudget
  omega

/-- The implication holds at 25 for every `rows, Λ < 25`. -/
theorem b331_implication_holds_at_p0 {rows Λ : ℕ}
    (hrows : rows < 25) (hΛ : Λ < 25) :
    seedBudgetVcomp Λ rows < 25 ^ 3 :=
  seedBudgetVcomp_lt_pow_of_bounds_twenty_five hrows hΛ (le_rfl : 25 ≤ 25)

/-- The implication holds for every `p ≥ p₀` -/
theorem b331_implication_from_p0 {p rows Λ : ℕ}
    (hp : p0 ≤ p) (hrows : rows < p) (hΛ : Λ < p) :
    seedBudgetVcomp Λ rows < p ^ 3 :=
  seedBudgetVcomp_lt_pow_of_bounds_twenty_five hrows hΛ hp

/-- So `29` is a technique
    floor of that majorant, not of the budget. -/
theorem b331_w9_majorant_fails_at_p0 :
    ¬ (27 * 25 ^ 2 + 22 < 25 ^ 3 + 48 * 25) := by
  decide

/-- It is
    not claimed to be that majorant's least point. -/
theorem b331_w9_majorant_holds_at_29 :
    27 * 29 ^ 2 + 22 < 29 ^ 3 + 48 * 29 :=
  cubic_gap_of_twenty_nine (le_rfl : 29 ≤ 29)

end Nock.RedTeam.Batch331

#print axioms Nock.RedTeam.Batch331.b331_negative_at_p0_pred
#print axioms Nock.RedTeam.Batch331.b331_implication_fails_at_24
#print axioms Nock.RedTeam.Batch331.b331_positive_worst_at_p0
#print axioms Nock.RedTeam.Batch331.b331_implication_holds_at_p0
#print axioms Nock.RedTeam.Batch331.b331_implication_from_p0
#print axioms Nock.RedTeam.Batch331.b331_w9_majorant_fails_at_p0
