/-
  Nock/NockVMROM/Thm54/VclL/Events/Bound.lean

  **The VCL-L bound function `boundVCL` and its
  figures.**

  `boundVCL |𝕂| N D P Λ Λ_chip` is the closed form of `epsilonOf (allSummands …)` at the VCL-L
  instance as the generic list is built (`SVFrame.jointSummandsStd`), with `W = max Λ Λ_chip`:
  * over `|𝕂|` (compute side, V4's named hypothesis): topology `24N`, compute walk
    `(N+9) + (2N+2) + 9N`;
  * over `|𝕂|²` (joint, L-C): zero seed `1`, the low-order window `sizeWindowRootBound W`, the NPR
    census `10N(2W − 1)`, the record-pair census `3N(2W − 1)`, the root-result pair `2W − 1`, and
    the three IO summands.

  The figures are exact rationals at `|𝕂| = p³` (Goldilocks), proved by monotonicity in
  `N, D, P` and one kernel evaluation (`decide +kernel`) at the corner; `Λ ≤ 2^110` is absorbed by the window
  (`W = Λ_chip`).
-/
import Nock.NockVMROM.Thm54.P8Core.VclL.Census
import Nock.NockVMROM.Thm54.FiniteFieldIOSoundness
import Nock.Field

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Events

open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.SizeWindowCounting (sizeWindowRootBound)

/-! ## 1. The pieces -/

/-- `ioFailureUnionBound` reads its two record counts only through their sum. -/
theorem ioFailureUnionBound_eq_zero_add (m a b c : ℕ) :
    ioFailureUnionBound m a b c = ioFailureUnionBound m 0 (a + b) c := by
  simp [ioFailureUnionBound]

theorem ioFailureUnionBound_mono_tot (m c : ℕ) {t t' : ℕ} (h : t ≤ t') :
    ioFailureUnionBound m 0 t c ≤ ioFailureUnionBound m 0 t' c := by
  unfold ioFailureUnionBound
  simp only [zero_add]
  gcongr

/-- The compute side's weight over `|𝕂|` (topology `24N`, compute walk `(N+9)+(2N+2)+9N`), the
walk instance's compute summands kept (V4 supplies them as `CF.summands`). -/
def computeWork (N : ℕ) : ℕ := 24 * N + ((N + 9) + (2 * N + 2) + 9 * N)

/-- The memory side's seed weight over `|𝕂|²`: the T2 census and the dyck-root event. -/
def memSeedWork (N D Λc : ℕ) : ℕ :=
  pairCount (D + 3 + 19 * N) * (2 * Λc - 1) + D * (2 * Λc - 1)

/-- The joint list's seed weight over `|𝕂|²` at `W` (`jointSummandsStd`: zero, low-order window,
NPR census `10N`, record census `3N`, root-result). -/
def jointSeedWork (N W : ℕ) : ℕ :=
  1 + sizeWindowRootBound W + 10 * N * (2 * W - 1) + 3 * N * (2 * W - 1) + (2 * W - 1)

/-- The three IO summands at `(IOγ, IOpole)`, export consumers `kc · N + P` (T5: `kc = 2`). -/
def ioWorkVCLk (kc c N D P : ℕ) : ℕ :=
  ioFailureUnionBound 6 0 (3 * D + 2) c + ioFailureUnionBound 10 0 (kc * N + P + D) c +
    ioFailureUnionBound 8 0 (N + P) c

/-- **The numerator over `|𝕂|²`** of a VCL-L-shaped bound with IO work `io`. -/
def numGen (c N D Λ Λc io : ℕ) : ℕ :=
  c * computeWork N + memSeedWork N D Λc + jointSeedWork N (max Λ Λc) + io

/-- The bound with IO work `io`: `computeWork/|𝕂| + (seeds + io)/|𝕂|²`. -/
def boundGen (c N D Λ Λc io : ℕ) : ℚ :=
  (computeWork N : ℚ) / c + ((memSeedWork N D Λc + jointSeedWork N (max Λ Λc) + io : ℕ) : ℚ) / c ^ 2

/-- **`boundVCLk`**: the VCL-L bound at export consumer multiplier `kc`. -/
def boundVCLk (kc c N D P Λ Λc : ℕ) : ℚ := boundGen c N D Λ Λc (ioWorkVCLk kc c N D P)

/-- **`boundVCL |𝕂| N D P Λ Λ_chip`** (T5's `kc = 2`). -/
def boundVCL (c N D P Λ Λc : ℕ) : ℚ := boundVCLk 2 c N D P Λ Λc

/-- The NC `kc = 3` (the live per-row record majorant in place of T5's `2`). -/
def boundVCL_kc3 (c N D P Λ Λc : ℕ) : ℚ := boundVCLk 3 c N D P Λ Λc

theorem boundGen_eq (c N D Λ Λc io : ℕ) (hc : 0 < c) :
    boundGen c N D Λ Λc io = (numGen c N D Λ Λc io : ℚ) / (c : ℚ) ^ 2 := by
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold boundGen numGen
  push_cast
  field_simp
  ring

/-! ## 2. Monotonicity and the window -/

theorem jointSeedWork_window (N Λ Λc : ℕ) (h : Λ ≤ Λc) :
    jointSeedWork N (max Λ Λc) = jointSeedWork N Λc := by
  rw [max_eq_right h]

theorem numGen_mono {c N D Λ Λc io N' D' io' : ℕ} (hN : N ≤ N') (hD : D ≤ D') (hio : io ≤ io') :
    numGen c N D Λ Λc io ≤ numGen c N' D' Λ Λc io' := by
  unfold numGen computeWork memSeedWork jointSeedWork
  have hp : pairCount (D + 3 + 19 * N) ≤ pairCount (D' + 3 + 19 * N') :=
    pairCount_mono (by omega)
  have h1 : pairCount (D + 3 + 19 * N) * (2 * Λc - 1) ≤ pairCount (D' + 3 + 19 * N') * (2 * Λc - 1) :=
    Nat.mul_le_mul_right _ hp
  have h2 : D * (2 * Λc - 1) ≤ D' * (2 * Λc - 1) := Nat.mul_le_mul_right _ hD
  have h3 : 10 * N * (2 * max Λ Λc - 1) ≤ 10 * N' * (2 * max Λ Λc - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : 3 * N * (2 * max Λ Λc - 1) ≤ 3 * N' * (2 * max Λ Λc - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have h5 : c * (24 * N + ((N + 9) + (2 * N + 2) + 9 * N)) ≤
      c * (24 * N' + ((N' + 9) + (2 * N' + 2) + 9 * N')) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem ioWorkVCLk_mono {kc c N D P N' D' P' : ℕ} (hN : N ≤ N') (hD : D ≤ D') (hP : P ≤ P') :
    ioWorkVCLk kc c N D P ≤ ioWorkVCLk kc c N' D' P' := by
  unfold ioWorkVCLk
  have hk : kc * N ≤ kc * N' := Nat.mul_le_mul_left _ hN
  have := ioFailureUnionBound_mono_tot 6 c (t := 3 * D + 2) (t' := 3 * D' + 2) (by omega)
  have := ioFailureUnionBound_mono_tot 10 c (t := kc * N + P + D) (t' := kc * N' + P' + D') (by omega)
  have := ioFailureUnionBound_mono_tot 8 c (t := N + P) (t' := N' + P') (by omega)
  omega

/-- The triangular window in closed form: `2 · Σ_{d ≤ W} d = W(W+1)`. -/
theorem two_mul_sizeWindowRootBound (W : ℕ) : 2 * sizeWindowRootBound W = W * (W + 1) := by
  induction W with
  | zero => simp [sizeWindowRootBound]
  | succ n ih =>
      unfold sizeWindowRootBound at *
      rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
      ring

theorem sizeWindowRootBound_eq (W : ℕ) : sizeWindowRootBound W = W * (W + 1) / 2 := by
  have := two_mul_sizeWindowRootBound W
  omega

/-! ## 3. Figures at Goldilocks (`|𝕂| = p³`) -/

noncomputable abbrev cK : ℕ := Fintype.card Nock.Field.K

theorem cK_eq : cK = 18446744069414584321 ^ 3 := Nock.Field.card_K_value

theorem cK_pos : 0 < cK := by rw [cK_eq]; norm_num

/-- A figure from the numerator: `num · 2^b < |𝕂|²` gives `bound < 2^-b`. -/
theorem boundGen_lt_of_num {N D Λ Λc io b : ℕ}
    (h : numGen cK N D Λ Λc io * 2 ^ b < cK ^ 2) :
    boundGen cK N D Λ Λc io < 1 / (2 : ℚ) ^ b := by
  rw [boundGen_eq _ _ _ _ _ _ cK_pos]
  have hc : (0 : ℚ) < (cK : ℚ) ^ 2 := by have := cK_pos; positivity
  rw [div_lt_div_iff₀ hc (by positivity), one_mul]
  exact_mod_cast h

/-- The converse direction, for negative controls. -/
theorem not_boundGen_le_of_num {N D Λ Λc io b : ℕ}
    (h : cK ^ 2 < numGen cK N D Λ Λc io * 2 ^ b) :
    ¬ boundGen cK N D Λ Λc io ≤ 1 / (2 : ℚ) ^ b := by
  rw [boundGen_eq _ _ _ _ _ _ cK_pos, not_le]
  have hc : (0 : ℚ) < (cK : ℚ) ^ 2 := by have := cK_pos; positivity
  rw [div_lt_div_iff₀ (by positivity) hc, one_mul]
  exact_mod_cast h

/-- The corner numerator: the program window `Λ ≤ Λc` is absorbed (`W = Λc`). -/
theorem numGen_corner {N D P Λ Λc N₀ D₀ P₀ : ℕ} (kc : ℕ) (hN : N ≤ N₀) (hD : D ≤ D₀) (hP : P ≤ P₀)
    (hΛ : Λ ≤ Λc) :
    numGen cK N D Λ Λc (ioWorkVCLk kc cK N D P) ≤
      numGen cK N₀ D₀ 0 Λc (ioWorkVCLk kc cK N₀ D₀ P₀) := by
  have h1 : max Λ Λc = Λc := max_eq_right hΛ
  have h2 : max 0 Λc = Λc := max_eq_right (Nat.zero_le _)
  have hw : numGen cK N D Λ Λc (ioWorkVCLk kc cK N D P) =
      numGen cK N D 0 Λc (ioWorkVCLk kc cK N D P) := by
    unfold numGen; rw [h1, h2]
  rw [hw]
  exact numGen_mono hN hD (ioWorkVCLk_mono hN hD hP)

/-- A corner numerator with the window in closed form (before the kernel evaluation). -/
theorem numGen_corner_eval (c N D Λc io : ℕ) :
    numGen c N D 0 Λc io =
      c * computeWork N + memSeedWork N D Λc +
        (1 + Λc * (Λc + 1) / 2 + 10 * N * (2 * Λc - 1) + 3 * N * (2 * Λc - 1) +
          (2 * Λc - 1)) + io := by
  have h2 : max 0 Λc = Λc := max_eq_right (Nat.zero_le _)
  unfold numGen jointSeedWork
  rw [h2, sizeWindowRootBound_eq]

/-- **`figVCL_two_pow_31`: 122 bits at the row budget `N, D, P ≤ 2^31`** (`Λ ≤ 2^110`,
`Λ_chip = 2^110`).  Design value 122.24. -/
theorem figVCL_two_pow_31 (N D P Λ : ℕ) (hN : N ≤ 2 ^ 31) (hD : D ≤ 2 ^ 31) (hP : P ≤ 2 ^ 31)
    (hΛ : Λ ≤ 2 ^ 110) :
    boundVCL cK N D P Λ (2 ^ 110) < 1 / (2 : ℚ) ^ 122 := by
  apply boundGen_lt_of_num
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (numGen_corner 2 hN hD hP hΛ)) ?_
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- **`figVCL_two_pow_32`: 120 bits at `N, D, P ≤ 2^32`.**  Design value 120.24. -/
theorem figVCL_two_pow_32 (N D P Λ : ℕ) (hN : N ≤ 2 ^ 32) (hD : D ≤ 2 ^ 32) (hP : P ≤ 2 ^ 32)
    (hΛ : Λ ≤ 2 ^ 110) :
    boundVCL cK N D P Λ (2 ^ 110) < 1 / (2 : ℚ) ^ 120 := by
  apply boundGen_lt_of_num
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (numGen_corner 2 hN hD hP hΛ)) ?_
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- **`figVCL_kernel`: 142 bits at the kernel row `N ≤ 2^21`, `D ≤ 2^20`, `P ≤ 2^21`.**
Design value 142.78. -/
theorem figVCL_kernel (N D P Λ : ℕ) (hN : N ≤ 2 ^ 21) (hD : D ≤ 2 ^ 20) (hP : P ≤ 2 ^ 21)
    (hΛ : Λ ≤ 2 ^ 110) :
    boundVCL cK N D P Λ (2 ^ 110) < 1 / (2 : ℚ) ^ 142 := by
  apply boundGen_lt_of_num
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (numGen_corner 2 hN hD hP hΛ)) ?_
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- **`figVCL_bench`: 123 bits at the bench-worst ratios** `100·D ≤ 36·N`, `100·P ≤ 86·N`,
`N ≤ 2^31`.  Design value 123.05. -/
theorem figVCL_bench (N D P Λ : ℕ) (hN : N ≤ 2 ^ 31) (hD : 100 * D ≤ 36 * N)
    (hP : 100 * P ≤ 86 * N) (hΛ : Λ ≤ 2 ^ 110) :
    boundVCL cK N D P Λ (2 ^ 110) < 1 / (2 : ℚ) ^ 123 := by
  apply boundGen_lt_of_num
  have hD' : D ≤ 773094113 := by omega
  have hP' : P ≤ 1846835937 := by omega
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (numGen_corner 2 hN hD' hP' hΛ)) ?_
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- The figures are figures, not floors: `123` is not reached at the budget, `121` not at `2^32`. -/
theorem figVCL_not_123 :
    ¬ boundVCL cK (2 ^ 31) (2 ^ 31) (2 ^ 31) 0 (2 ^ 110) ≤ 1 / (2 : ℚ) ^ 123 := by
  apply not_boundGen_le_of_num
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

theorem figVCL_not_121_at_32 :
    ¬ boundVCL cK (2 ^ 32) (2 ^ 32) (2 ^ 32) 0 (2 ^ 110) ≤ 1 / (2 : ℚ) ^ 121 := by
  apply not_boundGen_le_of_num
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-! ## 4. Negative controls (none touches `serves`) -/

/-- **NC `kc = 3`** (the live record majorant in place of T5's `2N`): 121.78, 122 LOST. -/
theorem figVCL_kc3_fails :
    ¬ boundVCL_kc3 cK (2 ^ 31) (2 ^ 31) (2 ^ 31) 0 (2 ^ 110) ≤ 1 / (2 : ℚ) ^ 122 := by
  apply not_boundGen_le_of_num
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- One tagged accumulator over the sum (width `10`, all `(3D+2) + (2N+P+D) + (N+P)` records). -/
def ioWorkOneAcc (c N D P : ℕ) : ℕ :=
  ioFailureUnionBound 10 0 ((3 * D + 2) + (2 * N + P + D) + (N + P)) c

/-- **NC one accumulator**: 120.83 at this closed form, 122 LOST (three accumulators are
load-bearing). -/
theorem figVCL_oneAcc_fails :
    ¬ boundGen cK (2 ^ 31) (2 ^ 31) 0 (2 ^ 110) (ioWorkOneAcc cK (2 ^ 31) (2 ^ 31) (2 ^ 31)) ≤
      1 / (2 : ℚ) ^ 122 := by
  apply not_boundGen_le_of_num
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- `m_x = 12` (`idL/idR` also in the export key). -/
def ioWorkMx12 (c N D P : ℕ) : ℕ :=
  ioFailureUnionBound 6 0 (3 * D + 2) c + ioFailureUnionBound 12 0 (2 * N + P + D) c +
    ioFailureUnionBound 8 0 (N + P) c

/-- **NC `m_x = 12`**: 122.04 — HOLDS (flagged: a 0.2-bit margin). -/
theorem figVCL_mx12_holds :
    boundGen cK (2 ^ 31) (2 ^ 31) 0 (2 ^ 110) (ioWorkMx12 cK (2 ^ 31) (2 ^ 31) (2 ^ 31)) <
      1 / (2 : ℚ) ^ 122 := by
  apply boundGen_lt_of_num
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- A validity binding per chain in place of `rootIdx` (`k_v = 2D + 2 + P`). -/
def ioWorkKvP (c N D P : ℕ) : ℕ :=
  ioFailureUnionBound 6 0 (3 * D + 2 + P) c + ioFailureUnionBound 10 0 (2 * N + P + D) c +
    ioFailureUnionBound 8 0 (N + P) c

/-- **NC validity per chain**: 122.02 — HOLDS (flagged: the `rootIdx` saving is 0.2 bits). -/
theorem figVCL_kvP_holds :
    boundGen cK (2 ^ 31) (2 ^ 31) 0 (2 ^ 110) (ioWorkKvP cK (2 ^ 31) (2 ^ 31) (2 ^ 31)) <
      1 / (2 : ℚ) ^ 122 := by
  apply boundGen_lt_of_num
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-! ## 5. The repaired bound (R-V3, DESIGN §3): IO coins in 𝕂′, widths `5/10/8`, `kc = 3`

So the repaired bound is `boundGen` with the `1`-form IO work `ioWorkKp`.
The identification with `epsilonOf` at the 11-coin frame (`epsilon_vcll_eq`) waits for R-LC6. -/

/-- `ioFailureUnionBound m 0 t (c²) = c² · ioFailureUnionBound m 0 t 1`. -/
theorem ioFUB_sq (m t c : ℕ) :
    ioFailureUnionBound m 0 t (c ^ 2) = c ^ 2 * ioFailureUnionBound m 0 t 1 := by
  unfold ioFailureUnionBound; ring

/-- IO work at 𝕂′ coins, over `|𝕂|²`: widths `m_v / m_x / m_p`, export multiplier `kc`. -/
def ioWorkKp (mv mx mp kc N D P : ℕ) : ℕ :=
  ioFailureUnionBound mv 0 (3 * D + 2) 1 + ioFailureUnionBound mx 0 (kc * N + P + D) 1 +
    ioFailureUnionBound mp 0 (N + P) 1

/-- **`boundVCL'`**: the repaired VCL-L bound (widths `5/10/8`, `kc = 3`, IO coins in 𝕂′). -/
def boundVCL' (c N D P Λ Λc : ℕ) : ℚ := boundGen c N D Λ Λc (ioWorkKp 5 10 8 3 N D P)

theorem ioWorkKp_mono {mv mx mp kc N D P N' D' P' : ℕ} (hN : N ≤ N') (hD : D ≤ D') (hP : P ≤ P') :
    ioWorkKp mv mx mp kc N D P ≤ ioWorkKp mv mx mp kc N' D' P' := by
  unfold ioWorkKp
  have hk : kc * N ≤ kc * N' := Nat.mul_le_mul_left _ hN
  have := ioFailureUnionBound_mono_tot mv 1 (t := 3 * D + 2) (t' := 3 * D' + 2) (by omega)
  have := ioFailureUnionBound_mono_tot mx 1 (t := kc * N + P + D) (t' := kc * N' + P' + D') (by omega)
  have := ioFailureUnionBound_mono_tot mp 1 (t := N + P) (t' := N' + P') (by omega)
  omega

/-- The monotone corner numerator for the repaired bound (twin of `numGen_corner`). -/
theorem numGen_cornerKp {N D P Λ Λc N₀ D₀ P₀ : ℕ} (mv mx mp kc : ℕ) (hN : N ≤ N₀) (hD : D ≤ D₀)
    (hP : P ≤ P₀) (hΛ : Λ ≤ Λc) :
    numGen cK N D Λ Λc (ioWorkKp mv mx mp kc N D P) ≤
      numGen cK N₀ D₀ 0 Λc (ioWorkKp mv mx mp kc N₀ D₀ P₀) := by
  have h1 : max Λ Λc = Λc := max_eq_right hΛ
  have h2 : max 0 Λc = Λc := max_eq_right (Nat.zero_le _)
  have hw : numGen cK N D Λ Λc (ioWorkKp mv mx mp kc N D P) =
      numGen cK N D 0 Λc (ioWorkKp mv mx mp kc N D P) := by
    unfold numGen; rw [h1, h2]
  rw [hw]
  exact numGen_mono hN hD (ioWorkKp_mono hN hD hP)

/-- **`figVCL'_two_pow_31`: 155 bits at the row budget** (design 155.83). -/
theorem figVCL'_two_pow_31 (N D P Λ : ℕ) (hN : N ≤ 2 ^ 31) (hD : D ≤ 2 ^ 31) (hP : P ≤ 2 ^ 31)
    (hΛ : Λ ≤ 2 ^ 110) :
    boundVCL' cK N D P Λ (2 ^ 110) < 1 / (2 : ℚ) ^ 155 := by
  apply boundGen_lt_of_num
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (numGen_cornerKp 5 10 8 3 hN hD hP hΛ)) ?_
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- **`figVCL'_two_pow_32`: 154 bits** (design 154.83). -/
theorem figVCL'_two_pow_32 (N D P Λ : ℕ) (hN : N ≤ 2 ^ 32) (hD : D ≤ 2 ^ 32) (hP : P ≤ 2 ^ 32)
    (hΛ : Λ ≤ 2 ^ 110) :
    boundVCL' cK N D P Λ (2 ^ 110) < 1 / (2 : ℚ) ^ 154 := by
  apply boundGen_lt_of_num
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (numGen_cornerKp 5 10 8 3 hN hD hP hΛ)) ?_
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- **`figVCL'_kernel`: 164 bits at `N ≤ 2^21`, `D ≤ 2^20`, `P ≤ 2^21`** (design 164.36). -/
theorem figVCL'_kernel (N D P Λ : ℕ) (hN : N ≤ 2 ^ 21) (hD : D ≤ 2 ^ 20) (hP : P ≤ 2 ^ 21)
    (hΛ : Λ ≤ 2 ^ 110) :
    boundVCL' cK N D P Λ (2 ^ 110) < 1 / (2 : ℚ) ^ 164 := by
  apply boundGen_lt_of_num
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (numGen_cornerKp 5 10 8 3 hN hD hP hΛ)) ?_
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- **`figVCL'_bench`: 155 bits at the bench-worst ratios** (design 155.83). -/
theorem figVCL'_bench (N D P Λ : ℕ) (hN : N ≤ 2 ^ 31) (hD : 100 * D ≤ 36 * N)
    (hP : 100 * P ≤ 86 * N) (hΛ : Λ ≤ 2 ^ 110) :
    boundVCL' cK N D P Λ (2 ^ 110) < 1 / (2 : ℚ) ^ 155 := by
  apply boundGen_lt_of_num
  have hD' : D ≤ 773094113 := by omega
  have hP' : P ≤ 1846835937 := by omega
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (numGen_cornerKp 5 10 8 3 hN hD' hP' hΛ)) ?_
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- Tightness (a figure, not a floor): `2^-156` is not reached at the row budget. -/
theorem figVCL'_not_156 :
    ¬ boundVCL' cK (2 ^ 31) (2 ^ 31) (2 ^ 31) 0 (2 ^ 110) ≤ 1 / (2 : ℚ) ^ 156 := by
  apply not_boundGen_le_of_num
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- Width robustness: V2's `9/19/14` entry counts at 𝕂′ coins still keep 155 at `2^31`. -/
theorem figKp_wide_two_pow_31 :
    boundGen cK (2 ^ 31) (2 ^ 31) 0 (2 ^ 110) (ioWorkKp 9 19 14 3 (2 ^ 31) (2 ^ 31) (2 ^ 31)) <
      1 / (2 : ℚ) ^ 155 := by
  apply boundGen_lt_of_num
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- NC (option (I), 𝕂 coins with 𝕂′-keyed `5/10/8`, `kc = 3`): 121.83, 122 LOST. -/
theorem figK_kc3_fails :
    ¬ boundGen cK (2 ^ 31) (2 ^ 31) 0 (2 ^ 110)
        (ioFailureUnionBound 5 0 (3 * 2 ^ 31 + 2) cK +
          ioFailureUnionBound 10 0 (3 * 2 ^ 31 + 2 ^ 31 + 2 ^ 31) cK +
          ioFailureUnionBound 8 0 (2 ^ 31 + 2 ^ 31) cK) ≤ 1 / (2 : ℚ) ^ 122 := by
  apply not_boundGen_le_of_num
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-! The export record is `(fp′ p, fp′ l, fp′ r, idx, side)` (`m_x = 11`) and each cell row provides TWO
export records (sides `0`/`1`), so the export accumulator's provider rows are `2D`
(`ChipRAP.cellXRecords`): export total `kc·N + P + 2D`. -/

/-- IO work at the side slot: export total `kc·N + P + 2D`. -/
def ioWorkKpS (mv mx mp kc N D P : ℕ) : ℕ :=
  ioFailureUnionBound mv 0 (3 * D + 2) 1 + ioFailureUnionBound mx 0 (kc * N + P + 2 * D) 1 +
    ioFailureUnionBound mp 0 (N + P) 1

/-- **`boundVCL''`**: the VCL-L bound at the side slot (widths `5/11/8`, `kc = 3`, IO coins in 𝕂′). -/
def boundVCL'' (c N D P Λ Λc : ℕ) : ℚ := boundGen c N D Λ Λc (ioWorkKpS 5 11 8 3 N D P)

theorem ioWorkKpS_mono {mv mx mp kc N D P N' D' P' : ℕ} (hN : N ≤ N') (hD : D ≤ D') (hP : P ≤ P') :
    ioWorkKpS mv mx mp kc N D P ≤ ioWorkKpS mv mx mp kc N' D' P' := by
  unfold ioWorkKpS
  have hk : kc * N ≤ kc * N' := Nat.mul_le_mul_left _ hN
  have := ioFailureUnionBound_mono_tot mv 1 (t := 3 * D + 2) (t' := 3 * D' + 2) (by omega)
  have := ioFailureUnionBound_mono_tot mx 1 (t := kc * N + P + 2 * D) (t' := kc * N' + P' + 2 * D') (by omega)
  have := ioFailureUnionBound_mono_tot mp 1 (t := N + P) (t' := N' + P') (by omega)
  omega

theorem numGen_cornerKpS {N D P Λ Λc N₀ D₀ P₀ : ℕ} (mv mx mp kc : ℕ) (hN : N ≤ N₀) (hD : D ≤ D₀)
    (hP : P ≤ P₀) (hΛ : Λ ≤ Λc) :
    numGen cK N D Λ Λc (ioWorkKpS mv mx mp kc N D P) ≤
      numGen cK N₀ D₀ 0 Λc (ioWorkKpS mv mx mp kc N₀ D₀ P₀) := by
  have h1 : max Λ Λc = Λc := max_eq_right hΛ
  have h2 : max 0 Λc = Λc := max_eq_right (Nat.zero_le _)
  have hw : numGen cK N D Λ Λc (ioWorkKpS mv mx mp kc N D P) =
      numGen cK N D 0 Λc (ioWorkKpS mv mx mp kc N D P) := by
    unfold numGen; rw [h1, h2]
  rw [hw]
  exact numGen_mono hN hD (ioWorkKpS_mono hN hD hP)

/-- **`figVCL''_two_pow_31`: 155 bits at the row budget, side slot.** -/
theorem figVCL''_two_pow_31 (N D P Λ : ℕ) (hN : N ≤ 2 ^ 31) (hD : D ≤ 2 ^ 31) (hP : P ≤ 2 ^ 31)
    (hΛ : Λ ≤ 2 ^ 110) :
    boundVCL'' cK N D P Λ (2 ^ 110) < 1 / (2 : ℚ) ^ 155 := by
  apply boundGen_lt_of_num
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (numGen_cornerKpS 5 11 8 3 hN hD hP hΛ)) ?_
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- **`figVCL''_two_pow_32`: 154 bits, side slot.** -/
theorem figVCL''_two_pow_32 (N D P Λ : ℕ) (hN : N ≤ 2 ^ 32) (hD : D ≤ 2 ^ 32) (hP : P ≤ 2 ^ 32)
    (hΛ : Λ ≤ 2 ^ 110) :
    boundVCL'' cK N D P Λ (2 ^ 110) < 1 / (2 : ℚ) ^ 154 := by
  apply boundGen_lt_of_num
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (numGen_cornerKpS 5 11 8 3 hN hD hP hΛ)) ?_
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- **`figVCL''_kernel`: 164 bits at `N ≤ 2^21`, `D ≤ 2^20`, `P ≤ 2^21`, side slot.** -/
theorem figVCL''_kernel (N D P Λ : ℕ) (hN : N ≤ 2 ^ 21) (hD : D ≤ 2 ^ 20) (hP : P ≤ 2 ^ 21)
    (hΛ : Λ ≤ 2 ^ 110) :
    boundVCL'' cK N D P Λ (2 ^ 110) < 1 / (2 : ℚ) ^ 164 := by
  apply boundGen_lt_of_num
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (numGen_cornerKpS 5 11 8 3 hN hD hP hΛ)) ?_
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- **`figVCL''_bench`: 155 bits at the bench-worst ratios, side slot.** -/
theorem figVCL''_bench (N D P Λ : ℕ) (hN : N ≤ 2 ^ 31) (hD : 100 * D ≤ 36 * N)
    (hP : 100 * P ≤ 86 * N) (hΛ : Λ ≤ 2 ^ 110) :
    boundVCL'' cK N D P Λ (2 ^ 110) < 1 / (2 : ℚ) ^ 155 := by
  apply boundGen_lt_of_num
  have hD' : D ≤ 773094113 := by omega
  have hP' : P ≤ 1846835937 := by omega
  refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (numGen_cornerKpS 5 11 8 3 hN hD' hP' hΛ)) ?_
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

/-- Tightness at the side slot: `2^-156` is not reached at the row budget. -/
theorem figVCL''_not_156 :
    ¬ boundVCL'' cK (2 ^ 31) (2 ^ 31) (2 ^ 31) 0 (2 ^ 110) ≤ 1 / (2 : ℚ) ^ 156 := by
  apply not_boundGen_le_of_num
  rw [numGen_corner_eval, cK_eq]
  decide +kernel

end Nock.NockVMROM.Thm54.VclL.Events
