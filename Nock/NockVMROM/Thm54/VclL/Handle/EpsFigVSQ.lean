/-
  Nock/NockVMROM/Thm54/VclL/Handle/EpsFigVSQ.lean

  Additive.

  Every other summand is unchanged.

  * `numHQ`, `boundVCLHQ''_eq` (closed form over `|𝕂|⁴` at `|𝕂′| = |𝕂|²`), `numHQ_corner`;
  * `kWalk_dominant`: the dominant summand is now the `𝕂`-coin compute walk + tiling + walk chain
    `(8N + 2 + 15W)/|𝕂|` (alone it already loses 157 at the `2^31` corner); `hxq_fits`: the moved
    handle export summand alone is below `2^-300`.

  **Scope.** These are statements about the BOUND FUNCTION.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.FiniteIO

noncomputable section

/-- **`boundVCLHQ'' c c' N D W Λ`**: `boundVCLH''` with the two handle IO summands over `𝕂′`
(`c' = |𝕂′|`, four `𝕂`-coins each, so over `c⁴`). -/
def boundVCLHQ'' (c c' N D W Λ : ℕ) : ℚ :=
  ((6 * N : ℕ) : ℚ) / c + ((2 * N + 2 : ℕ) : ℚ) / c + ((15 * W : ℕ) : ℚ) / c +
  ((D * (2 * fuelChip - 1) + 1 + pairCount (D + 3) * (2 * Λ - 1) : ℕ) : ℚ) / c ^ 2 +
  ((ioFailureUnionBound 5 (3 * N + W) D c' + ioFailureUnionBound 5 (2 * N) (2 * W) c' : ℕ) : ℚ) / c ^ 4 +
  ((ioFailureUnionBound 5 (3 + 2 * D) D c' + ioFailureUnionBound 11 W (2 * D) c' : ℕ) : ℚ) / c ^ 4

/-- The numerator over `|𝕂|⁴` (at `|𝕂′| = |𝕂|²`). -/
def numHQ (c N D W Λ : ℕ) : ℕ :=
  c ^ 3 * (8 * N + 2 + 15 * W) +
  c ^ 2 * (D * (2 * fuelChip - 1) + 1 + pairCount (D + 3) * (2 * Λ - 1)) +
  (ioFailureUnionBound 5 (3 * N + W) D (c ^ 2) + ioFailureUnionBound 5 (2 * N) (2 * W) (c ^ 2) +
    ioFailureUnionBound 5 (3 + 2 * D) D (c ^ 2) + ioFailureUnionBound 11 W (2 * D) (c ^ 2))

theorem boundVCLHQ''_eq (c N D W Λ : ℕ) (hc : 0 < c) :
    boundVCLHQ'' c (c ^ 2) N D W Λ = (numHQ c N D W Λ : ℚ) / (c : ℚ) ^ 4 := by
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold boundVCLHQ'' numHQ
  push_cast
  field_simp
  ring

theorem numHQ_corner {c N D W N₀ D₀ W₀ : ℕ} (Λ : ℕ) (hN : N ≤ N₀) (hD : D ≤ D₀) (hW : W ≤ W₀) :
    numHQ c N D W Λ ≤ numHQ c N₀ D₀ W₀ Λ := by
  have h1 := ioFUB_mono 5 (c ^ 2) (a := 3 * N + W) (a' := 3 * N₀ + W₀) (b := D) (b' := D₀) (by omega) hD
  have h2 := ioFUB_mono 5 (c ^ 2) (a := 2 * N) (a' := 2 * N₀) (b := 2 * W) (b' := 2 * W₀) (by omega) (by omega)
  have h3 := ioFUB_mono 5 (c ^ 2) (a := 3 + 2 * D) (a' := 3 + 2 * D₀) (b := D) (b' := D₀) (by omega) hD
  have h4 := ioFUB_mono 11 (c ^ 2) (a := W) (a' := W₀) (b := 2 * D) (b' := 2 * D₀) hW (by omega)
  have h5 : pairCount (D + 3) ≤ pairCount (D₀ + 3) := pairCount_mono (by omega)
  unfold numHQ
  gcongr

/-! ## Figures -/

theorem boundVCLHQ''_lt_of_num {N D W b : ℕ} (h : numHQ cK N D W fuelChip * 2 ^ b < cK ^ 4) :
    boundVCLHQ'' cK (cK ^ 2) N D W fuelChip < 1 / (2 : ℚ) ^ b := by
  rw [boundVCLHQ''_eq _ _ _ _ _ cK_pos]
  have hc : (0 : ℚ) < (cK : ℚ) ^ 4 := by have := cK_pos; positivity
  rw [div_lt_div_iff₀ hc (by positivity), one_mul]
  exact_mod_cast h

theorem not_boundVCLHQ''_le_of_num {N D W b : ℕ} (h : cK ^ 4 < numHQ cK N D W fuelChip * 2 ^ b) :
    ¬ boundVCLHQ'' cK (cK ^ 2) N D W fuelChip ≤ 1 / (2 : ℚ) ^ b := by
  rw [boundVCLHQ''_eq _ _ _ _ _ cK_pos, not_le]
  have hc : (0 : ℚ) < (cK : ℚ) ^ 4 := by have := cK_pos; positivity
  rw [div_lt_div_iff₀ (by positivity) hc, one_mul]
  exact_mod_cast h

/-- Kernel numerals (generic `c` with `c = p³`). -/
theorem numQ_31 (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    numHQ c (2 ^ 31) (2 ^ 31) (2 ^ 31) fuelChip * 2 ^ 156 < c ^ 4 := by
  subst hc; unfold numHQ fuelChip; decide +kernel

theorem numQ_32 (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    numHQ c (2 ^ 32) (2 ^ 32) (2 ^ 32) fuelChip * 2 ^ 155 < c ^ 4 := by
  subst hc; unfold numHQ fuelChip; decide +kernel

theorem numQ_k (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    numHQ c (2 ^ 21) (2 ^ 20) (2 ^ 21) fuelChip * 2 ^ 166 < c ^ 4 := by
  subst hc; unfold numHQ fuelChip; decide +kernel

theorem numQ_31_not (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    c ^ 4 < numHQ c (2 ^ 31) (2 ^ 31) (2 ^ 31) fuelChip * 2 ^ 157 := by
  subst hc; unfold numHQ fuelChip; decide +kernel

theorem numQ_32_not (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    c ^ 4 < numHQ c (2 ^ 32) (2 ^ 32) (2 ^ 32) fuelChip * 2 ^ 156 := by
  subst hc; unfold numHQ fuelChip; decide +kernel

theorem numQ_k_not (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    c ^ 4 < numHQ c (2 ^ 21) (2 ^ 20) (2 ^ 21) fuelChip * 2 ^ 167 := by
  subst hc; unfold numHQ fuelChip; decide +kernel

theorem figVCLHQ''_156 (N D W : ℕ) (hN : N ≤ 2 ^ 31) (hD : D ≤ 2 ^ 31) (hW : W ≤ 2 ^ 31) :
    boundVCLHQ'' cK (cK ^ 2) N D W fuelChip < 1 / (2 : ℚ) ^ 156 :=
  boundVCLHQ''_lt_of_num (lt_of_le_of_lt (Nat.mul_le_mul_right _ (numHQ_corner fuelChip hN hD hW))
    (numQ_31 cK cK_eq))

theorem figVCLHQ''_155_at_32 (N D W : ℕ) (hN : N ≤ 2 ^ 32) (hD : D ≤ 2 ^ 32) (hW : W ≤ 2 ^ 32) :
    boundVCLHQ'' cK (cK ^ 2) N D W fuelChip < 1 / (2 : ℚ) ^ 155 :=
  boundVCLHQ''_lt_of_num (lt_of_le_of_lt (Nat.mul_le_mul_right _ (numHQ_corner fuelChip hN hD hW))
    (numQ_32 cK cK_eq))

theorem figVCLHQ''_166_kernel (N D W : ℕ) (hN : N ≤ 2 ^ 21) (hD : D ≤ 2 ^ 20) (hW : W ≤ 2 ^ 21) :
    boundVCLHQ'' cK (cK ^ 2) N D W fuelChip < 1 / (2 : ℚ) ^ 166 :=
  boundVCLHQ''_lt_of_num (lt_of_le_of_lt (Nat.mul_le_mul_right _ (numHQ_corner fuelChip hN hD hW))
    (numQ_k cK cK_eq))

theorem figVCLHQ''_155 (N D W : ℕ) (hN : N ≤ 2 ^ 31) (hD : D ≤ 2 ^ 31) (hW : W ≤ 2 ^ 31) :
    boundVCLHQ'' cK (cK ^ 2) N D W fuelChip < 1 / (2 : ℚ) ^ 155 :=
  (figVCLHQ''_156 N D W hN hD hW).trans (by norm_num)

theorem figVCLHQ''_154 (N D W : ℕ) (hN : N ≤ 2 ^ 32) (hD : D ≤ 2 ^ 32) (hW : W ≤ 2 ^ 32) :
    boundVCLHQ'' cK (cK ^ 2) N D W fuelChip < 1 / (2 : ℚ) ^ 154 :=
  (figVCLHQ''_155_at_32 N D W hN hD hW).trans (by norm_num)

theorem figVCLHQ''_164 (N D W : ℕ) (hN : N ≤ 2 ^ 21) (hD : D ≤ 2 ^ 20) (hW : W ≤ 2 ^ 21) :
    boundVCLHQ'' cK (cK ^ 2) N D W fuelChip < 1 / (2 : ℚ) ^ 164 :=
  (figVCLHQ''_166_kernel N D W hN hD hW).trans (by norm_num)

/-- Tightness (figures, not floors). -/
theorem figVCLHQ''_not_157 :
    ¬ boundVCLHQ'' cK (cK ^ 2) (2 ^ 31) (2 ^ 31) (2 ^ 31) fuelChip ≤ 1 / (2 : ℚ) ^ 157 :=
  not_boundVCLHQ''_le_of_num (numQ_31_not cK cK_eq)

theorem figVCLHQ''_not_156_at_32 :
    ¬ boundVCLHQ'' cK (cK ^ 2) (2 ^ 32) (2 ^ 32) (2 ^ 32) fuelChip ≤ 1 / (2 : ℚ) ^ 156 :=
  not_boundVCLHQ''_le_of_num (numQ_32_not cK cK_eq)

theorem figVCLHQ''_not_167_kernel :
    ¬ boundVCLHQ'' cK (cK ^ 2) (2 ^ 21) (2 ^ 20) (2 ^ 21) fuelChip ≤ 1 / (2 : ℚ) ^ 167 :=
  not_boundVCLHQ''_le_of_num (numQ_k_not cK cK_eq)

theorem kWalk_dominant (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    c < (8 * 2 ^ 31 + 2 + 15 * 2 ^ 31) * 2 ^ 157 := by
  subst hc; decide +kernel

/-- The moved handle export summand alone is below `2^-300` at the `2^31` corner. -/
theorem hxq_fits (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    ioFailureUnionBound 5 (3 * 2 ^ 31 + 2 ^ 31) (2 ^ 31) (c ^ 2) * 2 ^ 300 < c ^ 4 := by
  subst hc; unfold ioFailureUnionBound; decide +kernel

end

end Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ
