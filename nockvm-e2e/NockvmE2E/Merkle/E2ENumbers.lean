/-
Merkle (B) e2e row 5: the numeric pieces of the e2e bound.
1. `rapFriEps_le`: the RHS of `rap_fri_sound_deep` at `Q ≤ 2^64`, under the parameter hypotheses of
   `Succ.Numbers.rap_fri_sound_deep_numbers`, is `≤ 2^-83 + 2^-144 + 2^-146`.
2. `merkleTerm_le`: the exact multi-checkpoint ROM numerator (`_eq_sup`, NOT the coarse form) over
   `|Dg| ≥ p^4` is `≤ 2^-121`.
3. `e2e_total_le`: the sum is `≤ (2^82)⁻¹`.
-/
import NockvmE2E.Succ.Numbers
import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Potential

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain ProximityGap CoreDefinitions
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

namespace NockvmE2E.Merkle.E2ENumbers

open NockvmE2E.Succ.Numbers

/-! ## 2. The Merkle term -/

open MerkleTreeMultiExtractability in
/-- The exact numerator is independent of the tree sizes: `N ≤ Q_H² + (2·Q_H + K)(Q_H + V)`. -/
theorem numerator_le (nodeBudget K V QH : ℕ) :
    multiCheckpointROMErrorNumerator nodeBudget K V QH ≤ QH ^ 2 + (2 * QH + K) * (QH + V) := by
  rw [multiCheckpointROMErrorNumerator_eq_sup]
  refine Finset.sup_le fun pm hpm => ?_
  have hpm' : pm ≤ QH := Nat.lt_succ_iff.mp (Finset.mem_range.mp hpm)
  have h1 : pm.choose 2 ≤ QH ^ 2 := by
    rw [Nat.choose_two_right]
    calc pm * (pm - 1) / 2 ≤ pm * (pm - 1) := Nat.div_le_self _ _
      _ ≤ QH * QH := Nat.mul_le_mul hpm' (by omega)
      _ = QH ^ 2 := by ring
  have h2 : min nodeBudget (2 * pm + K) ≤ 2 * QH + K :=
    (Nat.min_le_right _ _).trans (by omega)
  exact add_le_add h1 (Nat.mul_le_mul_right _ h2)

open MerkleTreeMultiExtractability in
/-- **(2)** The Merkle term with the exact form: for `Q_H ≤ 2^64`, `V ≤ 2^32`, `K = k0·(Q_FS+1)`,
`k0 ≤ 61`, `Q_FS ≤ 2^64`, `|Dg| ≥ p^4`: `N/|Dg| ≤ 2^-121`. -/
theorem merkleTerm_le {Dg : Type} (QH V k0 Qfs Pn : ℕ) (hQH : QH ≤ 2 ^ 64) (hV : V ≤ 2 ^ 32)
    (hk0 : k0 ≤ 61) (hQfs : Qfs ≤ 2 ^ 64) (hDg : goldilocks ^ 4 ≤ Nat.card Dg) :
    (multiCheckpointROMErrorNumerator ((k0 * (Qfs + 1)) * Pn) (k0 * (Qfs + 1)) V QH : ℝ≥0∞) *
      (Nat.card Dg : ℝ≥0∞)⁻¹ ≤ (2 ^ 121 : ℝ≥0∞)⁻¹ := by
  have hK : k0 * (Qfs + 1) ≤ 61 * (2 ^ 64 + 1) := Nat.mul_le_mul hk0 (by omega)
  have hN : multiCheckpointROMErrorNumerator ((k0 * (Qfs + 1)) * Pn) (k0 * (Qfs + 1)) V QH ≤
      (2 ^ 64) ^ 2 + (2 * 2 ^ 64 + 61 * (2 ^ 64 + 1)) * (2 ^ 64 + 2 ^ 32) :=
    (numerator_le _ _ _ _).trans (by gcongr)
  have hnum : ((2 ^ 64) ^ 2 + (2 * 2 ^ 64 + 61 * (2 ^ 64 + 1)) * (2 ^ 64 + 2 ^ 32)) * 2 ^ 121 ≤
      goldilocks ^ 4 := by unfold goldilocks; norm_num
  set N := multiCheckpointROMErrorNumerator ((k0 * (Qfs + 1)) * Pn) (k0 * (Qfs + 1)) V QH
  have hNc : N * 2 ^ 121 ≤ Nat.card Dg :=
    (Nat.mul_le_mul_right _ hN).trans (hnum.trans hDg)
  have hc0 : (Nat.card Dg : ℝ≥0∞) ≠ 0 := by
    have : 0 < Nat.card Dg := lt_of_lt_of_le (by unfold goldilocks; norm_num) hDg
    exact_mod_cast this.ne'
  have hct : (Nat.card Dg : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h2 : ((2 : ℝ≥0∞) ^ 121) ≠ 0 := by positivity
  have h2t : ((2 : ℝ≥0∞) ^ 121) ≠ ⊤ := by simp
  have hle : (N : ℝ≥0∞) * 2 ^ 121 ≤ Nat.card Dg := by exact_mod_cast hNc
  have h1 : (N : ℝ≥0∞) * 2 ^ 121 * (Nat.card Dg : ℝ≥0∞)⁻¹ ≤ 1 :=
    calc _ ≤ (Nat.card Dg : ℝ≥0∞) * (Nat.card Dg : ℝ≥0∞)⁻¹ := by gcongr
      _ = 1 := ENNReal.mul_inv_cancel hc0 hct
  calc (N : ℝ≥0∞) * (Nat.card Dg : ℝ≥0∞)⁻¹
      = ((N : ℝ≥0∞) * 2 ^ 121 * (Nat.card Dg : ℝ≥0∞)⁻¹) * (2 ^ 121 : ℝ≥0∞)⁻¹ := by
        rw [mul_right_comm, mul_assoc _ ((2 : ℝ≥0∞) ^ 121), ENNReal.mul_inv_cancel h2 h2t, mul_one]
    _ ≤ 1 * (2 ^ 121 : ℝ≥0∞)⁻¹ := by gcongr
    _ = _ := one_mul _

/-! ## 1. The FS term -/

section Rap

open NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort.Batched
open NockvmE2E.Succ.FriDeep

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B F] [Inhabited B]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable [SampleableType F] [Inhabited F]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ F ι (Fin (2 ^ n) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ F ι (Fin (2 ^ n) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ F → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ F → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ω) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ω) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ n) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ω) P A R0 Rest RestV e).Mfin) (nb : ℕ)
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s 170).Challenge j)]

/-- The right-hand side of `rap_fri_sound_deep` (at `l = 170`, `θ = δ = 31/64`, batching error `ε`),
as a function of the query count `Q`. -/
noncomputable def rapFriEps (errOld : ℕ → ℝ≥0∞) (ε : ℝ≥0) (Q : ℕ) : ℝ≥0∞ :=
  Q * (Finset.univ.sup (rapErrors (Rok (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e))
        I0 I Ifin nb (errDeep P errOld)) ⊔
      ((ε : ℝ≥0∞) ⊔ Finset.univ.sup (fun j => (challengeError (ω := ω) s d 170 (31 / 64 : ℝ)
        ((31 / 64 : ℝ≥0) : ℝ) j : ℝ≥0∞)))) +
    (∑ j, rapErrors (Rok (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e))
        I0 I Ifin nb (errDeep P errOld) j +
      ((ε : ℝ≥0∞) +
        (((∑ i, foldingError (ω := ω) s d (31 / 64 : ℝ) i) +
          Real.toNNReal (1 - min (31 / 64 : ℝ) ((31 / 64 : ℝ≥0) : ℝ)) ^ 170 : ℝ≥0) : ℝ≥0∞)))

theorem enn_inv_pow (a : ℕ) : (((2 ^ a)⁻¹ : ℝ≥0) : ℝ≥0∞) = (2 ^ a : ℝ≥0∞)⁻¹ := by
  rw [ENNReal.coe_inv (by positivity), ENNReal.coe_pow, ENNReal.coe_ofNat]

/-- **(1)** The FS term at `Q ≤ 2^64`: `≤ 2^-83 + 2^-144 + 2^-146`. Same parameter hypotheses as
`rap_fri_sound_deep_numbers`. -/
theorem rapFriEps_le (hnb : P.R + 1 < nb)
    (errOld : ℕ → ℝ≥0∞) (hs : ∀ i, s i = 1)
    (hrate : 64 * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ n) (hn : n ≤ 32)
    (hF : goldilocks ^ 3 ≤ Fintype.card F) (hm : m + 1 ≤ 2 ^ 12)
    (hns : P.ns ≤ 2 ^ 20) (hD : P.D.card ≤ 2 ^ 32) (hH : P.H.card ≤ 2 ^ 32) (hnq : P.nq + 1 ≤ 2 ^ 8)
    (herrOld : ∀ r, errOld r ≤ (((2 ^ 150)⁻¹ : ℝ≥0) : ℝ≥0∞)) (hnb30 : nb ≤ 30)
    (Q : ℕ) (hQ : Q ≤ 2 ^ 64) :
    rapFriEps (ω := ω) P A R0 Rest RestV e I0 I Ifin nb s d errOld
        (m * ((2 ^ n : ℝ≥0) / Fintype.card F) : ℝ≥0) Q ≤
      (2 ^ 83 : ℝ≥0∞)⁻¹ + (2 ^ 144 : ℝ≥0∞)⁻¹ + (2 ^ 146 : ℝ≥0∞)⁻¹ := by
  have hB : ∀ r', errDeep P errOld r' ≤ (((2 ^ 149)⁻¹ : ℝ≥0) : ℝ≥0∞) := fun r' => by
    refine (errDeep_le P hF hns hD hH hnq errOld r').trans ?_
    calc errOld r' + (((2 ^ 150)⁻¹ : ℝ≥0) : ℝ≥0∞)
        ≤ (((2 ^ 150)⁻¹ : ℝ≥0) : ℝ≥0∞) + (((2 ^ 150)⁻¹ : ℝ≥0) : ℝ≥0∞) := by gcongr; exact herrOld r'
      _ = (((2 ^ 149)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
        rw [← ENNReal.coe_add]; congr 1; rw [← NNReal.coe_inj]; push_cast; norm_num
  have hsupR := sup_rapErrors_le (Rok (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e))
    I0 I Ifin nb (errDeep P errOld) _ hB
  have hsumR := sum_rapErrors_le (Rok (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e))
    I0 I Ifin nb (errDeep P errOld) _ hB
  have hfri := fri_side_le (ω := ω) s hs d hrate hn hF m hm
  have hfold := sum_foldingError_le (ω := ω) s hs d hrate hn hF
  have hepsN := eps_le (F := F) m hm hn hF
  have hchal : Finset.univ.sup (fun j => (challengeError (ω := ω) s d 170 (31 / 64 : ℝ)
      ((31 / 64 : ℝ≥0) : ℝ) j : ℝ≥0∞)) ≤ (((2 ^ 147)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    refine Finset.sup_le fun j _ => ENNReal.coe_le_coe.mpr ?_
    refine (Finset.single_le_sum (f := fun j => challengeError (ω := ω) s d 170 (31 / 64 : ℝ)
      ((31 / 64 : ℝ≥0) : ℝ) j) (fun _ _ => zero_le) (Finset.mem_univ j)).trans ?_
    rw [sum_challengeError]
    calc _ ≤ (2 ^ 154)⁻¹ + (2 ^ 162)⁻¹ := add_le_add hfold query_le
      _ ≤ (2 ^ 147)⁻¹ := by rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have hmax : Finset.univ.sup (rapErrors (Rok (P.statement R0 Rest)
        (friPlan (ω := ω) P A R0 Rest RestV e)) I0 I Ifin nb (errDeep P errOld)) ⊔
      (((m * ((2 ^ n : ℝ≥0) / Fintype.card F) : ℝ≥0) : ℝ≥0∞) ⊔
        Finset.univ.sup (fun j => (challengeError (ω := ω) s d 170 (31 / 64 : ℝ)
          ((31 / 64 : ℝ≥0) : ℝ) j : ℝ≥0∞))) ≤ (((2 ^ 147)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    refine sup_le (hsupR.trans (ENNReal.coe_le_coe.mpr ?_)) (sup_le (ENNReal.coe_le_coe.mpr hepsN) hchal)
    rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have hQ' : (Q : ℝ≥0∞) ≤ ((2 ^ 64 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hQ
  have hnb' : ((nb + 2 : ℕ) : ℝ≥0∞) ≤ ((32 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast (by omega : nb + 2 ≤ 32)
  have hfri' : ((m * ((2 ^ n : ℝ≥0) / Fintype.card F) : ℝ≥0) : ℝ≥0∞) +
      ((((∑ i, foldingError (ω := ω) s d (31 / 64 : ℝ) i) +
        Real.toNNReal (1 - min (31 / 64 : ℝ) ((31 / 64 : ℝ≥0) : ℝ)) ^ 170 : ℝ≥0) : ℝ≥0∞)) ≤
      (((2 ^ 146)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_add]; exact ENNReal.coe_le_coe.mpr hfri
  unfold rapFriEps
  refine (add_le_add (mul_le_mul' hQ' hmax)
    (add_le_add (hsumR.trans (mul_le_mul' hnb' le_rfl)) hfri')).trans ?_
  rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, enn_inv_pow 146]
  rw [← enn_inv_pow 83, ← enn_inv_pow 144, ← enn_inv_pow 146, ← ENNReal.coe_add, ← ENNReal.coe_add,
    ← ENNReal.coe_add]
  refine ENNReal.coe_le_coe.mpr ?_
  rw [← NNReal.coe_le_coe]; push_cast; norm_num

/-- **(3)** The total: the FS term at `Q_FS ≤ 2^64` plus the Merkle term is `≤ (2^82)⁻¹`. -/
theorem e2e_total_le (hnb : P.R + 1 < nb)
    (errOld : ℕ → ℝ≥0∞) (hs : ∀ i, s i = 1)
    (hrate : 64 * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ n) (hn : n ≤ 32)
    (hF : goldilocks ^ 3 ≤ Fintype.card F) (hm : m + 1 ≤ 2 ^ 12)
    (hns : P.ns ≤ 2 ^ 20) (hD : P.D.card ≤ 2 ^ 32) (hH : P.H.card ≤ 2 ^ 32) (hnq : P.nq + 1 ≤ 2 ^ 8)
    (herrOld : ∀ r, errOld r ≤ (((2 ^ 150)⁻¹ : ℝ≥0) : ℝ≥0∞)) (hnb30 : nb ≤ 30)
    (Qfs : ℕ) (hQfs : Qfs ≤ 2 ^ 64)
    {Dg : Type} (QH V k0 Pn : ℕ) (hQH : QH ≤ 2 ^ 64) (hV : V ≤ 2 ^ 32) (hk0 : k0 ≤ 61)
    (hDg : goldilocks ^ 4 ≤ Nat.card Dg) :
    rapFriEps (ω := ω) P A R0 Rest RestV e I0 I Ifin nb s d errOld
        (m * ((2 ^ n : ℝ≥0) / Fintype.card F) : ℝ≥0) Qfs +
      (MerkleTreeMultiExtractability.multiCheckpointROMErrorNumerator
        ((k0 * (Qfs + 1)) * Pn) (k0 * (Qfs + 1)) V QH : ℝ≥0∞) * (Nat.card Dg : ℝ≥0∞)⁻¹ ≤
      (2 ^ 82 : ℝ≥0∞)⁻¹ := by
  refine (add_le_add
    (rapFriEps_le P A R0 Rest RestV e I0 I Ifin nb s d hnb errOld hs hrate hn hF hm hns hD hH hnq
      herrOld hnb30 Qfs hQfs)
    (merkleTerm_le QH V k0 Qfs Pn hQH hV hk0 hQfs hDg)).trans ?_
  rw [← enn_inv_pow 83, ← enn_inv_pow 144, ← enn_inv_pow 146, ← enn_inv_pow 121, ← enn_inv_pow 82,
    ← ENNReal.coe_add, ← ENNReal.coe_add, ← ENNReal.coe_add]
  refine ENNReal.coe_le_coe.mpr ?_
  rw [← NNReal.coe_le_coe]; push_cast; norm_num

end Rap

end NockvmE2E.Merkle.E2ENumbers
