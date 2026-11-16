import Nock.NockVMROM.Thm54.P8Core.Batch1541Thm54T0Tower
import Nock.NockVMROM.Thm54.GeneratedField

/-!
1. `orbit_dvd_split`: `3·2^(max hC (max hT hP)) ∣ n` gives the three per-height facts `hFC hFT hFP`
   (literally the binders of `honestVCLJ_of_run` / `vcl_completeness_of_run`, with `n = Fintype.card F - 1`).
2. `heightOf rows := max 1 (Nat.clog 2 rows)`: `1 ≤ heightOf rows` and `rows ≤ 2 ^ heightOf rows`
   (the `hC1/hT1/hP1` and `hsize/hsizeT/hsizeP` shapes); `heightOf 0`-style choice `h := 0` fails `1 ≤ h`.
3. `exists_nonsquare_ne_zero` / `chosenδ`: a base non-square at an odd prime, and its lift to a cubic `K`.
-/

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Compute.TowerChosen

/-! ## 1. The `hF` split -/

theorem orbit_dvd_split {n hC hT hP : ℕ} (h : 3 * 2 ^ (max hC (max hT hP)) ∣ n) :
    3 * 2 ^ hC ∣ n ∧ 3 * 2 ^ hT ∣ n ∧ 3 * 2 ^ hP ∣ n := by
  have key : ∀ {a : ℕ}, a ≤ max hC (max hT hP) → 3 * 2 ^ a ∣ n := fun {a} ha =>
    (Nat.mul_dvd_mul_left 3 (Nat.pow_dvd_pow 2 ha)).trans h
  exact ⟨key (le_max_left _ _), key ((le_max_left _ _).trans (le_max_right _ _)),
    key ((le_max_right _ _).trans (le_max_right _ _))⟩

/-! ## 2. The height chooser -/

/-- The chosen orbit height for a table of `rows` rows. -/
def heightOf (rows : ℕ) : ℕ := max 1 (Nat.clog 2 rows)

theorem one_le_heightOf (rows : ℕ) : 1 ≤ heightOf rows := le_max_left _ _

theorem le_two_pow_heightOf (rows : ℕ) : rows ≤ 2 ^ heightOf rows :=
  (Nat.le_pow_clog (by norm_num) rows).trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))

/-- The chooser is tight: the height is `1` or the exact ceiling log. -/
theorem heightOf_le (rows : ℕ) : heightOf rows ≤ max 1 (Nat.clog 2 rows) := le_rfl

/-! ## 3. A base non-square and its cubic lift -/

theorem exists_nonsquare_ne_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ δ : ZMod p, δ ≠ 0 ∧ ¬ IsSquare δ := by
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  exact ⟨a, fun h => ha (h ▸ ⟨0, by simp⟩), ha⟩

/-- The chosen base non-square. -/
noncomputable def chosenδ (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : ZMod p :=
  Classical.choose (exists_nonsquare_ne_zero p hp2)

theorem chosenδ_spec (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    chosenδ p hp2 ≠ 0 ∧ ¬ IsSquare (chosenδ p hp2) :=
  Classical.choose_spec (exists_nonsquare_ne_zero p hp2)

/-- The chosen `δ` stays a non-square in any cubic extension `K` of `ZMod p`. -/
theorem chosenδ_nonsquare_K (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K]
    [Algebra (ZMod p) K] [Fintype K] [CharP K p] (hK3 : Module.finrank (ZMod p) K = 3) :
    ¬ IsSquare (algebraMap (ZMod p) K (chosenδ p hp2)) :=
  T0Tower.nonsquare_lift (F := ZMod p) (K := K)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
    (by rw [ringChar.eq K p]; exact hp2) hK3 _ (chosenδ_spec p hp2).1 (chosenδ_spec p hp2).2

end Nock.NockVMROM.Thm54.VclL.Compute.TowerChosen
