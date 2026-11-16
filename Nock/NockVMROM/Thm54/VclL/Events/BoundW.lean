/-
  Nock/NockVMROM/Thm54/VclL/Events/BoundW.lean

  **`boundVCLW''`, the VCL-L bound with the path
  chip replaced by the paper's walk, and its three figures at VCL-L's budgets.**

  What changes against `boundVCL''` (`Bound.lean`), with `W` = walk rows in place of `P` = path rows:
  * the export accumulator's total is `3N + W + 2D` (one export consume per walk row,
    `vclInternalBoundW 1 = W`), as the path chip's `3N + P + 2D`;
  * the path accumulator's total is `N + 2W` (TWO path records per walk row, `vclRespBoundW 2 = 2W`),
    against the path chip's `N + P`;
  * Widths `5 / 11 / 8` (`RV.mVCL`) and `kc = 3` are unchanged.
-/
import Nock.NockVMROM.Thm54.VclL.Events.Bound

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Events

open Nock.NockVMROM.Thm54.FiniteIO

/-- IO work with the walk: validity `3D + 2`, export `kc·N + W + 2D`, path `N + 2W`. -/
def ioWorkKpW (mv mx mp kc N D W : ℕ) : ℕ :=
  ioFailureUnionBound mv 0 (3 * D + 2) 1 + ioFailureUnionBound mx 0 (kc * N + W + 2 * D) 1 +
    ioFailureUnionBound mp 0 (N + 2 * W) 1

/-- **`boundVCLW''`**: `boundVCL''` with the path rows replaced by walk rows `W` and the walk event
`15W / |𝕂|` added. -/
def boundVCLW'' (c N D W Λ Λc : ℕ) : ℚ :=
  boundGen c N D Λ Λc (ioWorkKpW 5 11 8 3 N D W) + ((15 * W : ℕ) : ℚ) / c

/-- The numerator over `|𝕂|²`. -/
def numGenW (c N D W Λ Λc : ℕ) : ℕ :=
  numGen c N D Λ Λc (ioWorkKpW 5 11 8 3 N D W) + c * (15 * W)

theorem boundVCLW''_eq (c N D W Λ Λc : ℕ) (hc : 0 < c) :
    boundVCLW'' c N D W Λ Λc = (numGenW c N D W Λ Λc : ℚ) / (c : ℚ) ^ 2 := by
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold boundVCLW'' numGenW
  rw [boundGen_eq _ _ _ _ _ _ hc]
  push_cast
  field_simp

theorem ioWorkKpW_mono {mv mx mp kc N D W N' D' W' : ℕ} (hN : N ≤ N') (hD : D ≤ D') (hW : W ≤ W') :
    ioWorkKpW mv mx mp kc N D W ≤ ioWorkKpW mv mx mp kc N' D' W' := by
  unfold ioWorkKpW
  have hk : kc * N ≤ kc * N' := Nat.mul_le_mul_left _ hN
  have := ioFailureUnionBound_mono_tot mv 1 (t := 3 * D + 2) (t' := 3 * D' + 2) (by omega)
  have := ioFailureUnionBound_mono_tot mx 1 (t := kc * N + W + 2 * D) (t' := kc * N' + W' + 2 * D')
    (by omega)
  have := ioFailureUnionBound_mono_tot mp 1 (t := N + 2 * W) (t' := N' + 2 * W') (by omega)
  omega

/-- The monotone corner numerator (twin of `numGen_cornerKpS`). -/
theorem numGenW_corner {N D W Λ Λc N₀ D₀ W₀ : ℕ} (hN : N ≤ N₀) (hD : D ≤ D₀) (hW : W ≤ W₀)
    (hΛ : Λ ≤ Λc) :
    numGenW cK N D W Λ Λc ≤ numGenW cK N₀ D₀ W₀ 0 Λc := by
  have h1 : max Λ Λc = Λc := max_eq_right hΛ
  have h2 : max 0 Λc = Λc := max_eq_right (Nat.zero_le _)
  have hw : numGen cK N D Λ Λc (ioWorkKpW 5 11 8 3 N D W) =
      numGen cK N D 0 Λc (ioWorkKpW 5 11 8 3 N D W) := by
    unfold numGen; rw [h1, h2]
  unfold numGenW
  rw [hw]
  have := numGen_mono (c := cK) (Λ := 0) (Λc := Λc) hN hD (ioWorkKpW_mono (mv := 5) (mx := 11) (mp := 8)
    (kc := 3) hN hD hW)
  have : cK * (15 * W) ≤ cK * (15 * W₀) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem boundVCLW_lt_of_num {N D W Λ Λc b : ℕ} (h : numGenW cK N D W Λ Λc * 2 ^ b < cK ^ 2) :
    boundVCLW'' cK N D W Λ Λc < 1 / (2 : ℚ) ^ b := by
  rw [boundVCLW''_eq _ _ _ _ _ _ cK_pos]
  have hc : (0 : ℚ) < (cK : ℚ) ^ 2 := by have := cK_pos; positivity
  rw [div_lt_div_iff₀ hc (by positivity), one_mul]
  exact_mod_cast h

theorem not_boundVCLW_le_of_num {N D W Λ Λc b : ℕ} (h : cK ^ 2 < numGenW cK N D W Λ Λc * 2 ^ b) :
    ¬ boundVCLW'' cK N D W Λ Λc ≤ 1 / (2 : ℚ) ^ b := by
  rw [boundVCLW''_eq _ _ _ _ _ _ cK_pos, not_le]
  have hc : (0 : ℚ) < (cK : ℚ) ^ 2 := by have := cK_pos; positivity
  rw [div_lt_div_iff₀ (by positivity) hc, one_mul]
  exact_mod_cast h

/-- The corner numerator in closed form (before the kernel evaluation). -/
theorem numGenW_corner_eval (c N D W Λc : ℕ) :
    numGenW c N D W 0 Λc =
      c * computeWork N + memSeedWork N D Λc +
        (1 + Λc * (Λc + 1) / 2 + 10 * N * (2 * Λc - 1) + 3 * N * (2 * Λc - 1) +
          (2 * Λc - 1)) + ioWorkKpW 5 11 8 3 N D W + c * (15 * W) := by
  unfold numGenW
  rw [numGen_corner_eval]

/-- **`figVCLW''_two_pow_31`: 155 bits at `N, D, W ≤ 2^31`.** -/
theorem figVCLW''_two_pow_31 (N D W Λ : ℕ) (hN : N ≤ 2 ^ 31) (hD : D ≤ 2 ^ 31) (hW : W ≤ 2 ^ 31)
    (hΛ : Λ ≤ 2 ^ 110) :
    boundVCLW'' cK N D W Λ (2 ^ 110) < 1 / (2 : ℚ) ^ 155 := by
  apply boundVCLW_lt_of_num
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (numGenW_corner hN hD hW hΛ)) ?_
  rw [numGenW_corner_eval, cK_eq]
  decide +kernel

/-- **`figVCLW''_two_pow_32`: 154 bits at `N, D, W ≤ 2^32`.** -/
theorem figVCLW''_two_pow_32 (N D W Λ : ℕ) (hN : N ≤ 2 ^ 32) (hD : D ≤ 2 ^ 32) (hW : W ≤ 2 ^ 32)
    (hΛ : Λ ≤ 2 ^ 110) :
    boundVCLW'' cK N D W Λ (2 ^ 110) < 1 / (2 : ℚ) ^ 154 := by
  apply boundVCLW_lt_of_num
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (numGenW_corner hN hD hW hΛ)) ?_
  rw [numGenW_corner_eval, cK_eq]
  decide +kernel

/-- **`figVCLW''_kernel`: 164 bits at `N ≤ 2^21`, `D ≤ 2^20`, `W ≤ 2^21`.** -/
theorem figVCLW''_kernel (N D W Λ : ℕ) (hN : N ≤ 2 ^ 21) (hD : D ≤ 2 ^ 20) (hW : W ≤ 2 ^ 21)
    (hΛ : Λ ≤ 2 ^ 110) :
    boundVCLW'' cK N D W Λ (2 ^ 110) < 1 / (2 : ℚ) ^ 164 := by
  apply boundVCLW_lt_of_num
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (numGenW_corner hN hD hW hΛ)) ?_
  rw [numGenW_corner_eval, cK_eq]
  decide +kernel

/-- Tightness (a figure, not a floor): `2^-156` is not reached at the `2^31` corner. -/
theorem figVCLW''_not_156 :
    ¬ boundVCLW'' cK (2 ^ 31) (2 ^ 31) (2 ^ 31) 0 (2 ^ 110) ≤ 1 / (2 : ℚ) ^ 156 := by
  apply not_boundVCLW_le_of_num
  rw [numGenW_corner_eval, cK_eq]
  decide +kernel

/-- Tightness at `2^32`: `2^-155` is not reached. -/
theorem figVCLW''_not_155_at_32 :
    ¬ boundVCLW'' cK (2 ^ 32) (2 ^ 32) (2 ^ 32) 0 (2 ^ 110) ≤ 1 / (2 : ℚ) ^ 155 := by
  apply not_boundVCLW_le_of_num
  rw [numGenW_corner_eval, cK_eq]
  decide +kernel

/-- Tightness at the kernel row: `2^-165` is not reached. -/
theorem figVCLW''_not_165_kernel :
    ¬ boundVCLW'' cK (2 ^ 21) (2 ^ 20) (2 ^ 21) 0 (2 ^ 110) ≤ 1 / (2 : ℚ) ^ 165 := by
  apply not_boundVCLW_le_of_num
  rw [numGenW_corner_eval, cK_eq]
  decide +kernel

theorem figVCLW_double_walk_fails :
    cK ^ 2 < (numGen cK (2 ^ 31) (2 ^ 31) 0 (2 ^ 110) (ioWorkKpW 5 11 8 3 (2 ^ 31) (2 ^ 31) (2 ^ 31)) +
        cK * (30 * 2 ^ 31)) * 2 ^ 155 := by
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

end Nock.NockVMROM.Thm54.VclL.Events
