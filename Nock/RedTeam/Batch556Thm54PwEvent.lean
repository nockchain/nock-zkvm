/-
  Nock/RedTeam/Batch556Thm54PwEvent.lean

  * **A. The event.**  `bivariate_bad_card_le`: if some
    `Q_{k₀} ≠ 0` then `#{(α, λ) : F = 0} ≤ |𝕂|·(deg Q_{k₀} + E)`.  `forest_zero_iff`: `F ≡ 0` iff
    every `Q_k ≡ 0`.  Own derivation (roots of `Q_{k₀}` in `λ`, then roots in `α` of a nonzero
    polynomial of degree `≤ E` at every other `λ`).
  * **B. Per root.**  Acceptance is `∀ root, F_root = 0`, so the accepting set is inside ANY one
    root's zero set (`accept_subset_root`): the bad set is bounded by one nonzero root
    polynomial, no union over roots.  "Two nonzero root polynomials whose sum is zero while each
    is separately zero" is contradictory by definition (`no_cancelling_roots`).
  * **C. The tuple.**  On `(α, λ) × R` (`R` the other nine coordinates) the event is a cylinder:
    `card = |R|·#{(α,λ)}` (`cylinder_card`), probability `≤ (deg + E)/|𝕂|`
    (`event_probability_le`).
  * **D. Figures.**  `pwAccountingWork N M = M + 3N + 128` majorises `deg Q + E + 1`
    (`deg ≤ 62 + 62 + M`, `E ≤ 3N + 3`, one point for `λ = 0`).  Added in the tree's
    `2·work` convention to the consumed majorant `367·2^{2r} + 144·2^r + 28`
    (`RealProgramSoundness.hostileSizeWork_lt_cardK`), the `122`/`120` figures hold
    (`figures_unmoved_31`, `figures_unmoved_32`); the summand alone is `< 2^{−155}`
    (`new_summand_small`).
  * **E. The existing timestamp event is not consumed but does contain the same-timestamp
    cancellation set** (`same_ts_roots_in_collision_event`).
  * **F. `hbound` does not bound axes**: `evalGRom` serves `[0 ax]` by `Noun.slot ax` for every
    `ax` (`evalGRom_op0_unguarded`), so the completeness condition `axis < 2^63` needs its own
    hypothesis (item 9).
-/
import Nock.RedTeam.Batch554Thm54PwFunctional
import Nock.NockVMROM.Thm54.FormRCore.PwEvent
import Nock.NockVMROM.Thm54.GoldilocksParameters
import Nock.NockVMROM.Thm54.HostileRecordLists
import Nock.NockVMROM.Thm54.TraceGen.GenGuardedRom

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch556

open Nock
open Polynomial

/-! ## A–C. -/

/-! ## D. Figures -/

open Nock.NockVMROM.Thm54.GoldilocksParameters

def pwAccountingWork (N M : ℕ) : ℕ := M + 3 * N + 128

theorem pwAccountingWork_majorises (N M dQ E : ℕ) (hd : dQ ≤ 124 + M) (hE : E ≤ 3 * N + 3) :
    dQ + E + 1 ≤ pwAccountingWork N M := by
  unfold pwAccountingWork; omega

theorem figures_unmoved_31 :
    (367 * 2 ^ 62 + 144 * 2 ^ 31 + 28 + 2 * pwAccountingWork (2 ^ 31) (2 ^ 31)) * 2 ^ 122
      < 2 * cardKGold := by
  norm_num [pwAccountingWork]

theorem figures_unmoved_32 :
    (367 * 2 ^ 64 + 144 * 2 ^ 32 + 28 + 2 * pwAccountingWork (2 ^ 32) (2 ^ 32)) * 2 ^ 120
      < 2 * cardKGold := by
  norm_num [pwAccountingWork]

/-- The new summand alone is below `2^{−155}` at `2^31` rows. -/
theorem new_summand_small :
    (pwAccountingWork (2 ^ 31) (2 ^ 31) : ℚ) / cardKGold < 1 / (2 : ℚ) ^ 155 := by
  rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
  norm_num [pwAccountingWork]

/-! ## E. The existing timestamp event contains the same-timestamp cancellation set -/

section Collision

open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem same_ts_roots_in_collision_event (D e₁ e₂ : ℕ) (h1 : 1 ≤ e₁) (h12 : e₁ < e₂)
    (h2 : e₂ ≤ D) (α : K) (hα : (X ^ e₁ - X ^ e₂ : K[X]).eval α = 0) :
    α ∈ TimestampCollisionEvent D := by
  rw [mem_timestampCollisionEvent]
  refine ⟨e₁, Finset.mem_Icc.mpr ⟨h1, by omega⟩, e₂, Finset.mem_Icc.mpr ⟨by omega, h2⟩, h12, ?_⟩
  simp only [eval_sub, eval_pow, eval_X] at hα
  exact sub_eq_zero.mp hα

end Collision

/-! ## F. `hbound` does not bound axes -/

/-- `RunBoundedBy` is `∃ result, evalGRom q fuel s f = some result`
(`GenNockCompilesCarrier.RunBoundedBy`); the guarded evaluator serves `[0 ax]` by
`Noun.slot ax subj` for EVERY atom `ax`, `2^63` included, so no capstone hypothesis bounds the
axis: the completeness condition `axis < 2^63` is new. -/
theorem evalGRom_op0_unguarded (q fuel : ℕ) (subj : Noun) (ax : ℕ) :
    Nock.NockVMROM.Thm54.TraceGen.evalGRom q (fuel + 1) subj (.cell (.atom 0) (.atom ax))
      = Noun.slot ax subj := by
  simp [Nock.NockVMROM.Thm54.TraceGen.evalGRom]

end Nock.RedTeam.Batch556

#print axioms Nock.RedTeam.Batch556.bivariate_bad_card_le
#print axioms Nock.RedTeam.Batch556.forest_zero_iff
#print axioms Nock.RedTeam.Batch556.accept_card_le_root
#print axioms Nock.RedTeam.Batch556.cylinder_card
#print axioms Nock.RedTeam.Batch556.event_probability_le
#print axioms Nock.RedTeam.Batch556.figures_unmoved_31
#print axioms Nock.RedTeam.Batch556.figures_unmoved_32
#print axioms Nock.RedTeam.Batch556.new_summand_small
#print axioms Nock.RedTeam.Batch556.same_ts_roots_in_collision_event
#print axioms Nock.RedTeam.Batch556.evalGRom_op0_unguarded
