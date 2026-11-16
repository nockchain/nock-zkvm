import NockvmE2E.Merkle.E2ENumbers
import NockvmE2E.Merkle.SideMerkle

open BinaryTree OracleComp OracleSpec ProtocolSpec
open Fri.Spec Domain ProximityGap CoreDefinitions NockvmE2E.FriPort NockvmE2E.FriPort.Batched
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.V
open NockvmE2E.Succ.Numbers NockvmE2E.Merkle.E2ENumbers NockvmE2E.Merkle.SideMerkle

/-- `a * 2^n ≤ b ⇒ a / b ≤ (2^n)⁻¹` -/
theorem div_le_inv_pow (a b : ℝ≥0∞) (n : ℕ) (h : a * 2 ^ n ≤ b) (hb0 : b ≠ 0) (hbt : b ≠ ⊤) :
    a / b ≤ (2 ^ n : ℝ≥0∞)⁻¹ := by
  rw [ENNReal.div_le_iff hb0 hbt]
  have h2 : ((2 : ℝ≥0∞) ^ n) ≠ 0 := by positivity
  have h2t : ((2 : ℝ≥0∞) ^ n) ≠ ⊤ := by simp
  calc a = a * 2 ^ n * (2 ^ n : ℝ≥0∞)⁻¹ := by rw [mul_assoc, ENNReal.mul_inv_cancel h2 h2t, mul_one]
    _ ≤ b * (2 ^ n : ℝ≥0∞)⁻¹ := by gcongr
    _ = _ := mul_comm _ _

/-- **collision term**: `(Q_H+V+T)^2/(2|Dg|) ≤ 2^-126` for `Q_H ≤ 2^64`, `V ≤ 2^32`, `T ≤ 2^40`, `|Dg| ≥ p^4` -/
theorem coll_le {Dg : Type} (QH V T : ℕ) (hQH : QH ≤ 2 ^ 64) (hV : V ≤ 2 ^ 32) (hT : T ≤ 2 ^ 40)
    (hDg : goldilocks ^ 4 ≤ Nat.card Dg) :
    ((QH + V + T) ^ 2 : ℝ≥0∞) / (2 * (Nat.card Dg : ℝ≥0∞)) ≤ (2 ^ 126 : ℝ≥0∞)⁻¹ := by
  have h1 : QH + V + T ≤ 2 ^ 65 := by omega
  have h2 : (QH + V + T) ^ 2 ≤ 2 ^ 130 := by
    calc (QH + V + T) ^ 2 ≤ (2 ^ 65) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 2 ^ 130 := by norm_num
  have h3 : 2 ^ 256 ≤ 2 * Nat.card Dg := by
    have : 2 ^ 255 ≤ goldilocks ^ 4 := by unfold goldilocks; norm_num
    omega
  have h4 : (QH + V + T) ^ 2 * 2 ^ 126 ≤ 2 * Nat.card Dg :=
    calc (QH + V + T) ^ 2 * 2 ^ 126 ≤ 2 ^ 130 * 2 ^ 126 := Nat.mul_le_mul_right _ h2
      _ = 2 ^ 256 := by norm_num
      _ ≤ _ := h3
  have hc0 : (Nat.card Dg : ℝ≥0∞) ≠ 0 := by
    have : 0 < Nat.card Dg := lt_of_lt_of_le (by unfold goldilocks; norm_num) hDg
    exact_mod_cast this.ne'
  refine div_le_inv_pow _ _ 126 (by exact_mod_cast h4) (by simpa using hc0) (ENNReal.mul_ne_top (by simp) (ENNReal.natCast_ne_top _))


section FriNum
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
  {n k : ℕ} {ω : SmoothCosetFftDomain n F}

/-- **term (a)**: the batched-FRI error at the J-8 numbers (`l = 170`, `θ = δ = 31/64`, `ε = m 2^n/|F|`, `Q ≤ 2^64`): `≤ 2^-83 + 2^-146`.
Same arithmetic as `E2ENumbers.rapFriEps_le` without the RAP terms. -/
theorem bfriErr_numbers (s : Fin (k + 1) → ℕ+) (hs : ∀ i, s i = 1) (dd : ℕ+)
    (hrate : 64 * (2 ^ (∑ j, (s j).val) * dd.val) ≤ 2 ^ n) (hn : n ≤ 32)
    (hF : goldilocks ^ 3 ≤ Fintype.card F) (m : ℕ) (hm : m + 1 ≤ 2 ^ 12) (Q : ℕ) (hQ : Q ≤ 2 ^ 64) :
    bfriErr (ω := ω) s dd 170 (31 / 64 : ℝ) (31 / 64 : ℝ≥0) ((m * ((2 ^ n : ℝ≥0) / Fintype.card F) : ℝ≥0)) Q ≤
      (2 ^ 83 : ℝ≥0∞)⁻¹ + (2 ^ 146 : ℝ≥0∞)⁻¹ := by
  have hfri := fri_side_le (ω := ω) s hs dd hrate hn hF m hm
  have hfold := sum_foldingError_le (ω := ω) s hs dd hrate hn hF
  have hepsN := eps_le (F := F) m hm hn hF
  have hchal : Finset.univ.sup (fun j => (challengeError (ω := ω) s dd 170 (31 / 64 : ℝ)
      ((31 / 64 : ℝ≥0) : ℝ) j : ℝ≥0∞)) ≤ (((2 ^ 147)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    refine Finset.sup_le fun j _ => ENNReal.coe_le_coe.mpr ?_
    refine (Finset.single_le_sum (f := fun j => challengeError (ω := ω) s dd 170 (31 / 64 : ℝ)
      ((31 / 64 : ℝ≥0) : ℝ) j) (fun _ _ => zero_le) (Finset.mem_univ j)).trans ?_
    rw [sum_challengeError]
    calc _ ≤ (2 ^ 154)⁻¹ + (2 ^ 162)⁻¹ := add_le_add hfold query_le
      _ ≤ (2 ^ 147)⁻¹ := by rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have hmax : (((m * ((2 ^ n : ℝ≥0) / Fintype.card F) : ℝ≥0) : ℝ≥0∞) ⊔
        Finset.univ.sup (fun j => (challengeError (ω := ω) s dd 170 (31 / 64 : ℝ)
          ((31 / 64 : ℝ≥0) : ℝ) j : ℝ≥0∞))) ≤ (((2 ^ 147)⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    sup_le (ENNReal.coe_le_coe.mpr hepsN) hchal
  have hQ' : (Q : ℝ≥0∞) ≤ ((2 ^ 64 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hQ
  have hfri' : ((m * ((2 ^ n : ℝ≥0) / Fintype.card F) : ℝ≥0) : ℝ≥0∞) +
      ((((∑ i, foldingError (ω := ω) s dd (31 / 64 : ℝ) i) +
        Real.toNNReal (1 - min (31 / 64 : ℝ) ((31 / 64 : ℝ≥0) : ℝ)) ^ 170 : ℝ≥0) : ℝ≥0∞)) ≤
      (((2 ^ 146)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_add]; exact ENNReal.coe_le_coe.mpr hfri
  unfold bfriErr
  refine (add_le_add (mul_le_mul' hQ' hmax) hfri').trans ?_
  rw [← ENNReal.coe_mul, enn_inv_pow 146]
  rw [← enn_inv_pow 83, ← enn_inv_pow 146, ← ENNReal.coe_add]
  refine ENNReal.coe_le_coe.mpr ?_
  rw [← NNReal.coe_le_coe]; push_cast; norm_num

end FriNum

/-- **the numbers of `εfix`**: with `Q_FS, Q_H ≤ 2^64`, `V ≤ 2^32`, `T ≤ 2^40`, `k ≤ 61`, `|Dg| ≥ p^4`:
`bfriErr + multiCheckpoint/|Dg| + (Q_H+V+T)^2/(2|Dg|) ≤ 2^-83 + 2^-120` (so `exec_e2e_J8V'' ≤ 2^-82 + 2^-83 + 2^-120`). -/
theorem epsfix_numbers {Dg : Type} (A B : ℝ≥0∞) (hA : A ≤ (2 ^ 83 : ℝ≥0∞)⁻¹ + (2 ^ 146 : ℝ≥0∞)⁻¹)
    (QH V k0 Qfs Pn T : ℕ) (hQH : QH ≤ 2 ^ 64) (hV : V ≤ 2 ^ 32) (hT : T ≤ 2 ^ 40) (hk0 : k0 ≤ 61) (hQfs : Qfs ≤ 2 ^ 64)
    (hDg : goldilocks ^ 4 ≤ Nat.card Dg) :
    A + (MerkleTreeMultiExtractability.multiCheckpointROMErrorNumerator ((k0 * (Qfs + 1)) * Pn) (k0 * (Qfs + 1)) V QH : ℝ≥0∞) *
        (Nat.card Dg : ℝ≥0∞)⁻¹ + ((QH + V + T) ^ 2 : ℝ≥0∞) / (2 * (Nat.card Dg : ℝ≥0∞)) ≤
      (2 ^ 83 : ℝ≥0∞)⁻¹ + (2 ^ 120 : ℝ≥0∞)⁻¹ := by
  have h1 := merkleTerm_le (Dg := Dg) QH V k0 Qfs Pn hQH hV hk0 hQfs hDg
  have h2 := coll_le (Dg := Dg) QH V T hQH hV hT hDg
  refine (add_le_add (add_le_add hA h1) h2).trans ?_
  rw [← enn_inv_pow 83, ← enn_inv_pow 146, ← enn_inv_pow 121, ← enn_inv_pow 126, ← enn_inv_pow 120,
    ← ENNReal.coe_add, ← ENNReal.coe_add, ← ENNReal.coe_add, ← ENNReal.coe_add]
  refine ENNReal.coe_le_coe.mpr ?_
  rw [← NNReal.coe_le_coe]; push_cast; norm_num

end NockvmE2E.Exec.V

#print axioms NockvmE2E.Exec.V.coll_le
#print axioms NockvmE2E.Exec.V.bfriErr_numbers
#print axioms NockvmE2E.Exec.V.epsfix_numbers
