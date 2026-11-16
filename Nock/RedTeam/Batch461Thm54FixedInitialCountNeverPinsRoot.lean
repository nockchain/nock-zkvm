/-
  Nock/RedTeam/Batch461Thm54FixedInitialCountNeverPinsRoot.lean

  **460) — the
  `initial_count` finding in its soundness-relevant shape.**

  Its negative control
  `::walkSat_ic_ne_alpha_does_not_pin_root` exhibits a cheating trace whose `cur 1` is
  `root + (ic − α) · chld` — a trace that DEPENDS on `α`.  In the protocol the base columns
  (`cur`, `chld'`) are committed before `α` is drawn, so an
  `α`-dependent witness only shows a per-coin failure, the kind an `h/|𝕂|` event prices.

  This file compiles the stronger fact the definitions support:

  1. `fixed_initialCount_never_pins_root` — with `initial_count = ic` a fixed non-zero
     constant, there are base columns `cur`, `chld'` chosen BEFORE the coin such that for
     EVERY `α` some extension columns satisfy `WalkSat` with the honest seed `α · root` and
     `out_walk = 0`, while `cur 1 ≠ root`.  The event "the coin catches this trace" is
     empty: no `α`-event of any size prices it.  (Two rows, root with one child: the produced
     index of the child is `ic · α`, the same `α`-power as the seed's `α · root`, so the
     polynomial identity in `α` pins `cur 1 = root + ic · chld'(1,1)`, not `root`.)
  2. `honest_two_node_walkSat_iff` — the HONEST two-node tree (`cur 1 = root`,
     `cur 2 = chld'(1,1) = X ≠ 0`) satisfies `WalkSat ∧ out_walk = 0` for some extension
     columns iff `ic = α` (at `α ≠ 0`).  So the deployed walk accepts the honest tree at
     exactly the one coin `alphaC c.1 = computeWalkAlpha`, and at that coin the cheating
     trace of (1) is accepted too.
  3. After walk-α it is the iff `pub 0 = pub 0' ↔ alphaC = alphaC'`
     (`Batch457::family_initialCount_at` now reads the coin).

  Scope, stated honestly: (1)–(2) are at the paper's `WalkSat`, the
  object `Batch459::deployed_walkSat` shows the deployed walk columns satisfy.  They show
  the WALK GATES do not bind the root at any coin; a full 199-column trace accepted at
  `computeChipAt c` realising (1) is not constructed here (the other gate families are not
  examined).  Nothing consumed is falsified: the capstone's root binding is carried by the
  hypothesis `TracesBindsHyps` (`Batch458::strategyOfTraces_binds_is_hyp`), not derived
  from the chip.
-/
import Nock.Walk
import Nock.RedTeam.Batch457Thm54RootLabelFromChip
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch461

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator

/-! ## A. Fixed `initial_count`: an `α`-independent cheating trace, accepted at every `α` -/

section Abstract
variable {K : Type} [Field K]

/-- The two-row fanout column: root with one child, child a leaf. -/
def fo2 : ℕ → ℕ := fun i => if i = 1 then 1 else 0

/-- **With `initial_count` a fixed non-zero constant `ic`, the walk gates bind the root at
NO coin.**  Base columns `cur`, `chld'` are chosen first (before `α`); for every `α` there are
extension columns `ln, count, acc` with `WalkSat … α (α · root) ic 2 ∧ acc 2 = 0`, and
`cur 1 = root + ic · X ≠ root`.  Compare `Batch457::walkSat_ic_ne_alpha_does_not_pin_root`,
whose `cur 1 = root + (ic − α) · chld` depends on `α`. -/
theorem fixed_initialCount_never_pins_root (ic root X : K) (hic : ic ≠ 0) (hX : X ≠ 0) :
    ∃ (cur : ℕ → K) (chld' : ℕ → ℕ → K),
      (∀ α : K, ∃ (ln count acc : ℕ → K),
        WalkSat cur chld' fo2 ln count acc α (α * root) ic 2 ∧ acc 2 = 0) ∧
      cur 1 ≠ root := by
  refine ⟨fun i => if i = 1 then root + ic * X else 0,
    fun i l => if i = 1 ∧ l = 1 then X else 0, ?_, ?_⟩
  · intro α
    refine ⟨fun i => α ^ i, fun _ => ic * α, fun _ => 0, ?_, rfl⟩
    refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · intro i hi1 hih
      ring
    · simp [fo2]
    · intro i hi1 hih
      have : i = 1 := by omega
      subst this
      simp [fo2]
    · simp only [fo2, Finset.Icc_self, Finset.sum_singleton, pow_one, and_self, if_pos]
      ring
    · intro i hi1 hih
      have : i = 1 := by omega
      subst this
      simp [fo2]
  · intro h
    have h' : root + ic * X = root := by simpa using h
    have : ic * X = 0 := by linear_combination h'
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hic h1
    · exact hX h1

/-- **The honest two-node tree is accepted iff `ic = α`.**  `cur 1 = root`,
`cur 2 = chld'(1,1) = X ≠ 0`, honest seed, `α ≠ 0`: some `ln, count, acc` satisfy
`WalkSat ∧ acc 2 = 0` iff `initial_count = α`.  With `initial_count = computeWalkAlpha`
fixed, the deployed walk accepts the honest tree at exactly one coin. -/
theorem honest_two_node_walkSat_iff (ic root X α : K) (hX : X ≠ 0) (hα : α ≠ 0) :
    (∃ (ln count acc : ℕ → K),
      WalkSat (fun i => if i = 1 then root else X) (fun i l => if i = 1 ∧ l = 1 then X else 0)
        fo2 ln count acc α (α * root) ic 2 ∧ acc 2 = 0) ↔ ic = α := by
  constructor
  · rintro ⟨ln, count, acc, hw, hout⟩
    have hln1 := hw.ln1
    have hln2 := hw.lnInc 1 (le_refl 1) (by norm_num)
    have hinit := hw.accInit
    have hstep := hw.accStep 1 (le_refl 1) (by norm_num)
    simp only [fo2, Finset.Icc_self, Finset.sum_singleton, pow_one, and_self,
      if_pos] at hinit
    simp only [fo2, show (1 : ℕ) + 1 = 2 from rfl, show ¬ ((2 : ℕ) = 1) by norm_num, if_false,
      Finset.Icc_eq_empty_of_lt (show (0 : ℕ) < 1 by norm_num), Finset.sum_empty] at hstep
    rw [hln1] at hinit
    rw [hln2, hln1, hout] at hstep
    -- hinit : α * root + acc 1 = α * ic * X + α * root;  hstep : α * α * X + 0 - acc 1 = 0
    have hacc1 : acc 1 = α * ic * X := by linear_combination hinit
    have hzero : α * X * (α - ic) = 0 := by linear_combination hstep + hacc1
    rcases mul_eq_zero.mp hzero with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hα
      · exact absurd h hX
    · exact (sub_eq_zero.mp h).symm
  · rintro rfl
    -- `α` has been eliminated in favour of `ic`; the honest extension columns at the coin `ic`.
    refine ⟨fun i => ic ^ i, fun _ => ic * ic, fun i => if i = 1 then ic * ic * X else 0, ?_, rfl⟩
    refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · intro i hi1 hih
      ring
    · simp [fo2]
    · intro i hi1 hih
      have : i = 1 := by omega
      subst this
      simp [fo2]
    · simp only [fo2, Finset.Icc_self, Finset.sum_singleton, pow_one, and_self, if_pos]
      ring
    · intro i hi1 hih
      have : i = 1 := by omega
      subst this
      simp only [fo2, show (1 : ℕ) + 1 = 2 from rfl, show ¬ ((2 : ℕ) = 1) by norm_num, if_false,
        if_true, Finset.Icc_eq_empty_of_lt (show (0 : ℕ) < 1 by norm_num), Finset.sum_empty]
      ring

end Abstract

/-! ## B. The chip's `initial_count` is one value at every tuple -/

section Chip

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Extension public `0` of the deployed
compute chip is `alphaC c.1` at every row (`Batch457::family_initialCount_at`, walk-α).
They are equal iff the coins agree. -/
theorem deployed_initialCount_same_at_every_tuple
    (c c' : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (Qc' : Fin (P.computeChipAt c').rap.w → F[X])
    (i : Fin (rows P)) (i' : Fin (rows P)) :
    (rowEnvAt P c Qc i).toSourceEnv.pub 0 = (rowEnvAt P c' Qc' i').toSourceEnv.pub 0 ↔
      alphaC c.1 = alphaC c'.1 := by
  rw [Batch457.family_initialCount_at, Batch457.family_initialCount_at]

end Chip

/-! ## C. Record -/

/-- The failure is structural (every coin), not
a fixed-value premise; and the honest tree is accepted at exactly one coin. -/
def review_reading : List String :=
  ["walk gates with fixed initial_count bind the root at NO coin (alpha-independent witness)",
    "honest two-node tree accepted iff initial_count = alpha",
    "deployed initial_count is one value at every tuple (known before c)"]

theorem review_reading_length : review_reading.length = 3 := by decide

end Nock.RedTeam.Batch461

#print axioms Nock.RedTeam.Batch461.fixed_initialCount_never_pins_root
#print axioms Nock.RedTeam.Batch461.honest_two_node_walkSat_iff
#print axioms Nock.RedTeam.Batch461.deployed_initialCount_same_at_every_tuple
