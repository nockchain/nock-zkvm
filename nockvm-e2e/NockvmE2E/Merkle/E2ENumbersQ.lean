/-
`E2ENumbersQ`: the main-proof numbers term of `Merkle/E2ENumbers.lean` as a function of the Fiat-Shamir query budget Q.
`rapFriEps_le_Q`: `rapFriEps_le`'s bound with the hypothesis `Q ≤ 2^64` dropped: for every Q,
`rapFriEps … Q ≤ Q · 2^-147 + (2^-144 + 2^-146)` (same parameter hypotheses).
-/
import NockvmE2E.Merkle.E2ENumbers

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain ProximityGap CoreDefinitions
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

namespace NockvmE2E.Merkle.E2ENumbers.EpsQ
open NockvmE2E.Merkle.E2ENumbers NockvmE2E.Succ.Numbers

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

theorem rapFriEps_le_Q (hnb : P.R + 1 < nb)
    (errOld : ℕ → ℝ≥0∞) (hs : ∀ i, s i = 1)
    (hrate : 64 * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ n) (hn : n ≤ 32)
    (hF : goldilocks ^ 3 ≤ Fintype.card F) (hm : m + 1 ≤ 2 ^ 12)
    (hns : P.ns ≤ 2 ^ 20) (hD : P.D.card ≤ 2 ^ 32) (hH : P.H.card ≤ 2 ^ 32) (hnq : P.nq + 1 ≤ 2 ^ 8)
    (herrOld : ∀ r, errOld r ≤ (((2 ^ 150)⁻¹ : ℝ≥0) : ℝ≥0∞)) (hnb30 : nb ≤ 30)
    (Q : ℕ) :
    rapFriEps (ω := ω) P A R0 Rest RestV e I0 I Ifin nb s d errOld
        (m * ((2 ^ n : ℝ≥0) / Fintype.card F) : ℝ≥0) Q ≤
      (Q : ℝ≥0∞) * (2 ^ 147 : ℝ≥0∞)⁻¹ + ((2 ^ 144 : ℝ≥0∞)⁻¹ + (2 ^ 146 : ℝ≥0∞)⁻¹) := by
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
  have hnb' : ((nb + 2 : ℕ) : ℝ≥0∞) ≤ ((32 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast (by omega : nb + 2 ≤ 32)
  have hfri' : ((m * ((2 ^ n : ℝ≥0) / Fintype.card F) : ℝ≥0) : ℝ≥0∞) +
      ((((∑ i, foldingError (ω := ω) s d (31 / 64 : ℝ) i) +
        Real.toNNReal (1 - min (31 / 64 : ℝ) ((31 / 64 : ℝ≥0) : ℝ)) ^ 170 : ℝ≥0) : ℝ≥0∞)) ≤
      (((2 ^ 146)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_add]; exact ENNReal.coe_le_coe.mpr hfri
  unfold rapFriEps
  refine add_le_add (mul_le_mul' le_rfl (hmax.trans (le_of_eq (enn_inv_pow 147))))
    (add_le_add (hsumR.trans ?_) (hfri'.trans (le_of_eq (enn_inv_pow 146))))
  rw [← enn_inv_pow 144, ← ENNReal.coe_natCast, ← ENNReal.coe_mul]
  refine ENNReal.coe_le_coe.mpr ?_
  rw [← NNReal.coe_le_coe]; push_cast
  have : ((nb : ℝ) + 2) ≤ 32 := by exact_mod_cast (by omega : nb + 2 ≤ 32)
  nlinarith [show (0:ℝ) ≤ ((2:ℝ) ^ 149)⁻¹ by positivity]

end Rap
end NockvmE2E.Merkle.E2ENumbers.EpsQ

#print axioms NockvmE2E.Merkle.E2ENumbers.EpsQ.rapFriEps_le_Q
