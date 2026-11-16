/-
  Nock/RedTeam/Batch1811Thm54TowerDInvGenHonest.lean

  **The `inv_gen` obstruction
  at honest values.**

  Here that
  premise is DISCHARGED at the honest NPR values: for the
  two-leaf cell `[x y]` the honest size is `z′²` (`GlobalCarryRecognizer.enc_cons` / `enc_atom`), and
  `z′ − z′²` has Im `b·(1 − 2a)` at `z′ = a + b√δ` — nonzero for every seed with `b ≠ 0`,
  `2a ≠ 1` (all but `|𝕂| + |𝕂|` of the `|𝕂|²` seeds).  Not shown here (phase 2): that the tower generator puts
  exactly these values in roles 15 / slot 1 on its op-3 rows; the row values are hypotheses.
-/
import Nock.RedTeam.Batch1810Thm54TowerDTranslation

set_option autoImplicit false

namespace Nock.RedTeam.Batch1811

open Nock Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.RedTeam.Batch1810

section
variable {K : Type} [Field K] (d : K) [Fact (¬ IsSquare d)]

/-- The honest size of the two-leaf cell `[x y]` is `z′²`. -/
theorem honest_cell_size (z : Quad d) (hz : z ≠ 0) (x y : ℕ) :
    (GlobalCarryRecognizer.enc z (Noun.cell (.atom x) (.atom y))).size = z * z := by
  rw [GlobalCarryRecognizer.enc_cons hz, GlobalCarryRecognizer.enc_atom,
    GlobalCarryRecognizer.enc_atom]
  rfl

/-- **`z′ − size′` is not in `𝕂`** at the honest two-leaf cell, for every seed `z′ = a + b√δ` with
`b ≠ 0` and `2a ≠ 1`. -/
theorem honest_cell_gap_not_base (a b : K) (hb : b ≠ 0) (ha : 2 * a ≠ 1) (x y : ℕ) (c : K) :
    algebraMap K (Quad d) c ≠
      Quad.mk d a b - (GlobalCarryRecognizer.enc (Quad.mk d a b) (Noun.cell (.atom x) (.atom y))).size := by
  have hz : Quad.mk d a b ≠ 0 := fun h => hb ((Quad.mk_eq_zero_iff d a b).mp h).2
  rw [honest_cell_size d _ hz, Quad.mk_mul, Quad.mk_sub, ← Quad.mk_base]
  intro h
  have h2 := ((Quad.mk_eq_mk_iff d _ _ _ _).mp h).2
  apply ha
  have : b * (1 - 2 * a) = 0 := by linear_combination -h2
  have := (mul_eq_zero.mp this).resolve_left hb
  linear_combination -this

end

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **The obstruction, confirmed at honest values.** -/
theorem fpImMap_rejects_honest_op3 (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]
    (eK : Env K) (eF : Env F) (a b : K) (hb : b ≠ 0) (ha : 2 * a ≠ 1) (x y : ℕ)
    (hb3 : eF.trace 3 = 1)
    (hz : (towerEnv δ fpImMap eK eF).chal 1 = Quad.mk _ a b)
    (hs : (towerEnv δ fpImMap eK eF).extTrace 15 =
      (GlobalCarryRecognizer.enc (Quad.mk _ a b) (Noun.cell (.atom x) (.atom y))).size) :
    g34.eval (towerEnv δ fpImMap eK eF) ≠ 0 := by
  set D := (towerEnv δ fpImMap eK eF).chal 1 - (towerEnv δ fpImMap eK eF).extTrace 15 with hD
  have hDb : ∀ c : K, algebraMap K (Quad (algebraMap F K δ)) c ≠ D := by
    intro c; rw [hD, hz, hs]; exact honest_cell_gap_not_base _ a b hb ha x y c
  have h57 : (towerEnv δ fpImMap eK eF).extTrace 57 =
      algebraMap K (Quad (algebraMap F K δ)) (eK.trace 184) := by
    simp [towerEnv, fpImMap, fpImCol_57, imVal, Quad.mk_base]
  have hb' : algebraMap F (Quad (algebraMap F K δ)) ((towerEnv δ fpImMap eK eF).baseTrace 3) = 1 := by
    simp [towerEnv, hb3]
  simp only [g34, CorrectedFinalTypedExpr.eval, ← hD, h57]
  rw [hb', one_mul]
  intro h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact hDb 0 (by rw [map_zero, h])
  · have h1 : algebraMap K (Quad (algebraMap F K δ)) (eK.trace 184) * D = 1 := by
      have : ((1 : ℤ) : Quad (algebraMap F K δ)) = 1 := Int.cast_one
      rw [this] at h; exact sub_eq_zero.mp h
    apply hDb (eK.trace 184)⁻¹
    rw [map_inv₀]
    exact (eq_inv_of_mul_eq_one_right h1).symm

end Nock.RedTeam.Batch1811

#print axioms Nock.RedTeam.Batch1811.honest_cell_size
#print axioms Nock.RedTeam.Batch1811.honest_cell_gap_not_base
#print axioms Nock.RedTeam.Batch1811.fpImMap_rejects_honest_op3
