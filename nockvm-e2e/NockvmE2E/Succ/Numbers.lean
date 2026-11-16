/-
concrete security numbers for `rap_fri_sound_deep`.
-/
import NockvmE2E.Succ.FriDeep

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain ProximityGap CoreDefinitions
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

namespace NockvmE2E.Succ.Numbers

/-- The Goldilocks prime `p = 2^64 − 2^32 + 1`. -/
def goldilocks : ℕ := 2 ^ 64 - 2 ^ 32 + 1

theorem two_pow_191_le_goldilocks_cube : 2 ^ 191 ≤ goldilocks ^ 3 := by
  unfold goldilocks; norm_num

/-- `x/|K| ≤ 2^a/2^191` for `x ≤ 2^a`, `|K| ≥ p³`. -/
theorem nn_div_card_le {K : Type} [Fintype K] (hK : goldilocks ^ 3 ≤ Fintype.card K) {x : ℝ≥0} {a : ℕ}
    (hx : x ≤ 2 ^ a) : x / (Fintype.card K : ℝ≥0) ≤ 2 ^ a / 2 ^ 191 := by
  have hc : (2 : ℝ) ^ 191 ≤ Fintype.card K := by
    exact_mod_cast two_pow_191_le_goldilocks_cube.trans hK
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
  have hx' : (x : ℝ) ≤ 2 ^ a := by exact_mod_cast hx
  calc (x : ℝ) / Fintype.card K ≤ 2 ^ a / Fintype.card K := by gcongr
    _ ≤ 2 ^ a / 2 ^ 191 := by gcongr

/-- The same in `ℝ≥0∞`, for a natural numerator. -/
theorem enn_div_card_le {K : Type} [Fintype K] (hK : goldilocks ^ 3 ≤ Fintype.card K) {x a : ℕ}
    (hx : x ≤ 2 ^ a) :
    (x : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞) ≤ (((2 : ℝ≥0) ^ a / 2 ^ 191 : ℝ≥0) : ℝ≥0∞) := by
  have hc : (Fintype.card K : ℝ≥0) ≠ 0 := by
    have := two_pow_191_le_goldilocks_cube.trans hK
    exact_mod_cast (show Fintype.card K ≠ 0 by positivity)
  rw [← ENNReal.coe_natCast x, ← ENNReal.coe_natCast (Fintype.card K), ← ENNReal.coe_div hc,
    ENNReal.coe_le_coe]
  exact nn_div_card_le hK (by exact_mod_cast hx)

/-! ## 1. Reed–Solomon radii at rate `≤ 1/32` -/

/-- At rate `D/|ι| ≤ 1/32`, the relative unique-decoding radius of `RS[α, D]` is at least `31/64`. -/
theorem relUDR_rs_ge {ι F : Type} [Fintype ι] [Field F] [DecidableEq F] (α : ι ↪ F) (D : ℕ)
    [NeZero D] (h : 32 * D ≤ Fintype.card ι) :
    (31 / 64 : ℝ≥0) ≤
      Code.relativeUniqueDecodingRadius (ReedSolomon.code α D : Set (ι → F)) := by
  have hD : D ≤ Fintype.card ι := by omega
  have hc : 0 < Fintype.card ι := by
    have := NeZero.pos D; omega
  unfold Code.relativeUniqueDecodingRadius
  rw [Code.dist_eq_minDist, ReedSolomon.minDist_of_le hD, Nat.cast_add, Nat.cast_one,
    add_tsub_cancel_right]
  have hnat : 62 * Fintype.card ι ≤ 64 * (Fintype.card ι - D) := by omega
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat]
  have hcR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hc
  have hR : (62 : ℝ) * Fintype.card ι ≤ 64 * ((Fintype.card ι - D : ℕ) : ℝ) := by exact_mod_cast hnat
  rw [div_div, le_div_iff₀ (by positivity)]
  linarith


/-! ## 2. FRI folding rounds (arity 2, unique-decoding MCA) -/

section Fold

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}

/-- The rate is constant along the folding schedule: rate `≤ 1/64` at the top gives
`64·deg ≤ |domain|` for the code of every fold round. -/
theorem fold_rate (s : Fin (k + 1) → ℕ+) (d : ℕ+) (i : Fin (k + 1))
    (hrate : 64 * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ n) :
    64 * foldingDegree s d i.succ ≤ 2 ^ (n - foldingPrefix s i.castSucc - (s i).val) := by
  have hle := foldingPrefix_le s i.succ
  rw [foldingPrefix_succ] at hle
  unfold foldingDegree
  rw [foldingPrefix_succ, Nat.sub_sub]
  set S := ∑ j, (s j).val
  set b := foldingPrefix s i.castSucc + (s i).val
  have hSn : S ≤ n := by
    have h1 : 2 ^ S ≤ 2 ^ n := le_trans (by
      have := d.pos; nlinarith [Nat.one_le_two_pow (n := S)]) hrate
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have e1 : 2 ^ (S - b) * 2 ^ b = 2 ^ S := by rw [← pow_add, Nat.sub_add_cancel hle]
  have e2 : 2 ^ (n - b) * 2 ^ b = 2 ^ n := by rw [← pow_add, Nat.sub_add_cancel (hle.trans hSn)]
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.two_pow_pos b)
  calc 64 * (2 ^ (S - b) * d.val) * 2 ^ b = 64 * (2 ^ S * d.val) := by rw [← e1]; ring
    _ ≤ 2 ^ n := hrate
    _ = 2 ^ (n - b) * 2 ^ b := e2.symm

/-- **One FRI folding round, arity 2.** At fold radius `θ = 31/64` (inside the unique-decoding
radius of every round's code at rate `≤ 1/64`), the folding error is the BCIKS20 UD affine-line MCA
error `|domain_i|/|F| ≤ 2^n/|F|` (`rs_mcaError_le_of_le_relUDR`; the degree-1 powers generator is the
affine line). -/
theorem mcaError_powers_le_affineLine {ι : Type} [Fintype ι] [Nonempty ι] (k' : ℕ) (hk : k' = 1)
    (C : ModuleCode ι F F) (θ : ℝ) :
    mcaError (univariatePowersGenerator F k') C θ ≤ mcaError (AffineLineGenerator F) C θ := by
  subst hk; rw [univariatePowersGenerator_one_eq_affineLineGenerator]

theorem foldingError_le (s : Fin (k + 1) → ℕ+) (d : ℕ+) (i : Fin (k + 1)) (hsi : s i = 1)
    (hrate : 64 * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ n) :
    foldingError (ω := ω) s d (31 / 64 : ℝ) i ≤ (2 ^ n : ℝ≥0) / Fintype.card F := by
  have hr := fold_rate s d i hrate
  have hD : NeZero (foldingDegree s d i.succ) := ⟨(foldingDegree_pos s d i.succ).ne'⟩
  unfold foldingError
  have hud := relUDR_rs_ge (F := F)
    ((ω.subdomain (foldingPrefix s i.castSucc)).subdomain (s i).val :
      Fin (2 ^ (n - foldingPrefix s i.castSucc - (s i).val)) ↪ F)
    (foldingDegree s d i.succ) (by rw [Fintype.card_fin]; omega)
  have h := rs_mcaError_le_of_le_relUDR (by norm_num) hud
  rw [show ((31 / 64 : ℝ≥0) : ℝ) = 31 / 64 by norm_num] at h
  refine ((ENNReal.toNNReal_mono ENNReal.coe_ne_top
    ((mcaError_powers_le_affineLine _ (by simp [hsi]) _ _).trans h)).trans_eq
      (ENNReal.toNNReal_coe _)).trans ?_
  rw [Fintype.card_fin]
  gcongr
  exact_mod_cast Nat.pow_le_pow_right (by norm_num) ((Nat.sub_le _ _).trans (Nat.sub_le _ _))

end Fold

/-! ## 3. The batching round (powers generator, as Plonky3; BCIKS20 unique-decoding regime) -/

section Batch

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n : ℕ} {ω : SmoothCosetFftDomain n F}

/-- The rate of `RS[ω, N]` at `64·N ≤ 2^n`. -/
theorem rate_rs_le {N : ℕ} (hrate : 64 * N ≤ 2 ^ n) :
    ((LinearCode.rate (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) N) : ℚ≥0) : ℝ≥0) ≤ 1 / 64 := by
  have hN : N ≤ Fintype.card (Fin (2 ^ n)) := by rw [Fintype.card_fin]; omega
  rw [ReedSolomon.rateOfLinearCode_eq_div hN, Fintype.card_fin]
  rw [← NNReal.coe_le_coe]
  simp only [NNRat.cast_div, NNRat.cast_natCast, NNReal.coe_div, NNReal.coe_natCast, NNRat.cast_pow,
    NNRat.cast_ofNat, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_one, Nat.cast_pow, Nat.cast_ofNat]
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hR : (64 : ℝ) * N ≤ 2 ^ n := by exact_mod_cast hrate
  rw [div_le_iff₀ h2]
  linarith

/-- **The batching error** at `δ = 31/64`, rate `≤ 1/64`: the powers generator of degree `m`
(`m + 1` words) has `caError ≤ m·2^n/|F|` (`caError_powers_le`; `errorBound` in its UD branch). -/
theorem caError_powers_numbers (m : ℕ) {N : ℕ} (hN0 : 0 < N) (hrate : 64 * N ≤ 2 ^ n) :
    caError (univariatePowersGenerator F m)
        (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) N).carrier (31 / 64) (31 / 64) ≤
      ((m * ((2 ^ n : ℝ≥0) / Fintype.card F) : ℝ≥0) : ℝ≥0∞) := by
  have hρ := rate_rs_le (ω := ω) hrate
  have hsq : ReedSolomon.sqrtRate N (ω : Fin (2 ^ n) ↪ F) ≤ 1 / 8 := by
    rw [ReedSolomon.sqrtRate, NNReal.sqrt_le_iff_le_sq]
    refine hρ.trans (le_of_eq ?_); norm_num
  have hδ : (31 / 64 : ℝ≥0) < 1 - ReedSolomon.sqrtRate N (ω : Fin (2 ^ n) ↪ F) := by
    rw [lt_tsub_iff_right]
    calc (31 / 64 : ℝ≥0) + ReedSolomon.sqrtRate N (ω : Fin (2 ^ n) ↪ F)
        ≤ 31 / 64 + 1 / 8 := by gcongr
      _ < 1 := by norm_num
  refine (caError_powers_le m hN0 (by norm_num) hδ).trans ?_
  have hEB : errorBound (31 / 64) N (ω : Fin (2 ^ n) ↪ F) = (2 ^ n : ℝ≥0) / Fintype.card F := by
    have h1 : (63 / 64 : ℝ≥0) ≤ 1 - ((LinearCode.rate
        (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) N) : ℚ≥0) : ℝ≥0) := by
      rw [le_tsub_iff_right (hρ.trans (by rw [← NNReal.coe_le_coe]; norm_num))]
      calc (63 / 64 : ℝ≥0) + _ ≤ 63 / 64 + 1 / 64 := by gcongr
        _ = 1 := by norm_num
    have hmem : (31 / 64 : ℝ≥0) ∈ Set.Icc 0 ((1 - ((LinearCode.rate
        (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) N) : ℚ≥0) : ℝ≥0)) / 2) := by
      refine ⟨by norm_num, le_trans (b := (63 / 64 : ℝ≥0) / 2) ?_ (by gcongr)⟩
      rw [← NNReal.coe_le_coe]; norm_num
    unfold errorBound
    simp only [hmem, ↓reduceIte, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [hEB]

end Batch

/-! ## 4. The FRI-side error, closed form -/

section FriSide

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}

/-- **Query term**: `l = 170` queries at `min θ δ = 31/64`: `(33/64)^170 ≤ 2^-162`. -/
theorem query_le : Real.toNNReal (1 - min (31 / 64 : ℝ) ((31 / 64 : ℝ≥0) : ℝ)) ^ 170 ≤ (2 ^ 162)⁻¹ := by
  rw [← NNReal.coe_le_coe]
  have h : ((31 / 64 : ℝ≥0) : ℝ) = 31 / 64 := by norm_num
  rw [h, min_self, NNReal.coe_pow, Real.coe_toNNReal _ (by norm_num)]
  norm_num

/-- **Folding terms**: `k+1 ≤ 32` arity-2 rounds, each `≤ 2^n/|F| ≤ 2^32/2^191`: `Σ ≤ 2^-154`. -/
theorem sum_foldingError_le (s : Fin (k + 1) → ℕ+) (hs : ∀ i, s i = 1) (d : ℕ+)
    (hrate : 64 * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ n) (hn : n ≤ 32)
    (hF : goldilocks ^ 3 ≤ Fintype.card F) :
    ∑ i, foldingError (ω := ω) s d (31 / 64 : ℝ) i ≤ (2 ^ 154)⁻¹ := by
  have hS : ∑ j, (s j).val = k + 1 := by simp [hs]
  have hk : k + 1 ≤ 32 := by
    have h1 : 2 ^ (k + 1) ≤ 2 ^ 32 := by
      have := d.pos
      have h2 : 2 ^ n ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hn
      rw [hS] at hrate
      nlinarith [Nat.one_le_two_pow (n := k + 1)]
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    omega
  have hround : ∀ i ∈ Finset.univ, foldingError (ω := ω) s d (31 / 64 : ℝ) i ≤ 2 ^ 32 / 2 ^ 191 :=
    fun i _ => (foldingError_le s d i (hs i) hrate).trans
      (nn_div_card_le hF (by exact_mod_cast Nat.pow_le_pow_right (by norm_num) hn))
  refine (Finset.sum_le_card_nsmul _ _ _ hround).trans ?_
  rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← NNReal.coe_le_coe]
  have hk' : ((k + 1 : ℕ) : ℝ) ≤ 32 := by exact_mod_cast hk
  push_cast
  calc ((k : ℝ) + 1) * (2 ^ 32 / 2 ^ 191) ≤ 32 * (2 ^ 32 / 2 ^ 191) := by
        gcongr; exact_mod_cast hk
    _ = (2 ^ 154)⁻¹ := by norm_num

/-- **Batching term**: `m + 1 ≤ 2^12` words: `m·2^n/|F| ≤ 2^-147`. -/
theorem eps_le (m : ℕ) (hm : m + 1 ≤ 2 ^ 12) (hn : n ≤ 32) (hF : goldilocks ^ 3 ≤ Fintype.card F) :
    (m * ((2 ^ n : ℝ≥0) / Fintype.card F) : ℝ≥0) ≤ (2 ^ 147)⁻¹ := by
  have h1 : (2 ^ n : ℝ≥0) / Fintype.card F ≤ 2 ^ 32 / 2 ^ 191 :=
    nn_div_card_le hF (by exact_mod_cast Nat.pow_le_pow_right (by norm_num) hn)
  have hm' : (m : ℝ≥0) ≤ 2 ^ 12 := by exact_mod_cast (by omega : m ≤ 2 ^ 12)
  calc (m : ℝ≥0) * ((2 ^ n : ℝ≥0) / Fintype.card F) ≤ 2 ^ 12 * (2 ^ 32 / 2 ^ 191) := by gcongr
    _ = (2 ^ 147)⁻¹ := by rw [← NNReal.coe_inj]; push_cast; norm_num

/-- **The FRI-side error of `rap_fri_sound_deep` in closed form.** Unique decoding,
arity 2 (`s ≡ 1`), rate `≤ 1/64` (`64·2^{Σs}·d ≤ 2^n`), `n ≤ 32`, `θ = δ = 31/64`, `l = 170`,
batching by the powers generator of degree `m` (`m + 1 ≤ 2^12` words, `ε = m·2^n/|F|`),
`|F| ≥ p³` (Goldilocks cubic extension or larger):
`ε + (Σ foldingError + (1 − min θ δ)^l) ≤ 2^-147 + 2^-154 + 2^-162 ≤ 2^-146`. -/
theorem fri_side_le (s : Fin (k + 1) → ℕ+) (hs : ∀ i, s i = 1) (d : ℕ+)
    (hrate : 64 * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ n) (hn : n ≤ 32)
    (hF : goldilocks ^ 3 ≤ Fintype.card F) (m : ℕ) (hm : m + 1 ≤ 2 ^ 12) :
    (m * ((2 ^ n : ℝ≥0) / Fintype.card F) : ℝ≥0) +
      ((∑ i, foldingError (ω := ω) s d (31 / 64 : ℝ) i) +
        Real.toNNReal (1 - min (31 / 64 : ℝ) ((31 / 64 : ℝ≥0) : ℝ)) ^ 170) ≤ (2 ^ 146)⁻¹ := by
  have h1 := eps_le (F := F) m hm hn hF
  have h2 := sum_foldingError_le (ω := ω) s hs d hrate hn hF
  have h3 := query_le
  calc _ ≤ (2 ^ 147)⁻¹ + ((2 ^ 154)⁻¹ + (2 ^ 162)⁻¹ : ℝ≥0) := by gcongr
    _ ≤ (2 ^ 146)⁻¹ := by rw [← NNReal.coe_le_coe]; push_cast; norm_num

end FriSide

/-! ## 5. The RAP and DEEP terms -/

section Deep

open NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Deep

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} (P : DeepParams Φ K ι β colRound)

/-- `ε_α = (ns − 1)/|K| ≤ 2^-171` for `ns ≤ 2^20` constraints, `|K| ≥ p³`. -/
theorem epsAlpha_le (hK : goldilocks ^ 3 ≤ Fintype.card K) (hns : P.ns ≤ 2 ^ 20) :
    epsAlpha P ≤ (((2 ^ 171)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  refine (enn_div_card_le (a := 20) hK (by omega)).trans (le_of_eq ?_)
  congr 1; rw [← NNReal.coe_inj]; push_cast; norm_num

/-- `ε_ζ = (|D| + (nq+1)|H|)/|K| ≤ 2^-150` for `|D|, |H| ≤ 2^32`, `nq + 1 ≤ 2^8`, `|K| ≥ p³`. -/
theorem epsZeta_le (hK : goldilocks ^ 3 ≤ Fintype.card K) (hD : P.D.card ≤ 2 ^ 32)
    (hH : P.H.card ≤ 2 ^ 32) (hnq : P.nq + 1 ≤ 2 ^ 8) :
    epsZeta P ≤ (((2 ^ 150)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  have h : P.D.card + (P.nq + 1) * P.H.card ≤ 2 ^ 41 := by
    have := Nat.mul_le_mul hnq hH
    norm_num at this ⊢; omega
  refine (enn_div_card_le (a := 41) hK h).trans (le_of_eq ?_)
  congr 1; rw [← NNReal.coe_inj]; push_cast; norm_num

/-- **The RAP+DEEP per-round error**: `errDeep P errOld r ≤ errOld r + 2^-150`
(at most one of `ε_α`, `ε_ζ` is charged on a round; `ε_α ≤ 2^-171 ≤ 2^-150`). -/
theorem errDeep_le (hK : goldilocks ^ 3 ≤ Fintype.card K) (hns : P.ns ≤ 2 ^ 20)
    (hD : P.D.card ≤ 2 ^ 32) (hH : P.H.card ≤ 2 ^ 32) (hnq : P.nq + 1 ≤ 2 ^ 8)
    (errOld : ℕ → ℝ≥0∞) (r : ℕ) :
    errDeep P errOld r ≤ errOld r + (((2 ^ 150)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  have hA : epsAlpha P ≤ (((2 ^ 150)⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    (epsAlpha_le P hK hns).trans (ENNReal.coe_le_coe.mpr (by
      rw [← NNReal.coe_le_coe]; push_cast; norm_num))
  have hZ := epsZeta_le P hK hD hH hnq
  unfold errDeep
  by_cases h1 : P.R = r
  · have h2 : ¬ P.R + 1 = r := by omega
    rw [ite_eq_left h1, ite_eq_right h2, add_zero]; gcongr
  · by_cases h2 : P.R + 1 = r
    · rw [ite_eq_right h1, ite_eq_left h2, add_zero]; gcongr
    · rw [ite_eq_right h1, ite_eq_right h2, add_zero, add_zero]; exact le_self_add

end Deep

section RapErr

open NockvmE2E.Rap

variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] {ι β : Type} {colRound : ι → ℕ}
  (R : RapStatement Φ K ι β colRound)
variable [SampleableType K] [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
  [Inhabited β] [Inhabited K]
  [DecidableEq R.M0] [Finite R.M0] [DecidableEq R.Mfin] [Finite R.Mfin]
  (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound β r))
  (Ifin : OracleInterface R.Mfin) (nb : ℕ)

theorem rapErrors_le (err : ℕ → ℝ≥0∞) (B : ℝ≥0∞) (h : ∀ r, err r ≤ B) (j) :
    rapErrors R I0 I Ifin nb err j ≤ B := by
  unfold rapErrors; split_ifs
  · exact h _
  · exact zero_le

/-- The RAP protocol has `nb + 2` rounds. -/
theorem sum_rapErrors_le (err : ℕ → ℝ≥0∞) (B : ℝ≥0∞) (h : ∀ r, err r ≤ B) :
    ∑ j, rapErrors R I0 I Ifin nb err j ≤ (nb + 2 : ℕ) * B := by
  refine (Finset.sum_le_card_nsmul _ _ _ fun j _ => rapErrors_le R I0 I Ifin nb err B h j).trans
    (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 2
  simp [rounds, rapRounds, colRounds_length]

theorem sup_rapErrors_le (err : ℕ → ℝ≥0∞) (B : ℝ≥0∞) (h : ∀ r, err r ≤ B) :
    Finset.univ.sup (rapErrors R I0 I Ifin nb err) ≤ B :=
  Finset.sup_le fun j _ => rapErrors_le R I0 I Ifin nb err B h j

end RapErr

/-! ## 6. The post-FS figure: ONE theorem -/

section PostFS

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
  (Ifin : OracleInterface (friPlan (ω := ω) P A R0 Rest RestV e).Mfin)
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s 170).Challenge j)]

/-- **The post-Fiat–Shamir figure for `rap_fri_sound_deep`, as ONE theorem.**
Parameters: FRI challenges and RAP coins in `F` with `|F| ≥ p³` (`p` = Goldilocks; e.g. its cubic
extension); unique decoding, arity 2 (`s ≡ 1`), rate `≤ 1/64` (`64·2^{Σs}·d ≤ 2^n`), domain `2^n`,
`n ≤ 32`; `θ = δ = 31/64`; `l = 170` queries; batching by the powers generator of degree `m`
(`m + 1 ≤ 2^12` words, `ε = m·2^n/|F|`); DEEP caps `ns ≤ 2^20`, `nq + 1 ≤ 2^8`, `|D|, |H| ≤ 2^32`;
the OLD RAP's per-round error `errOld r ≤ 2^-150` (an assumption on the RAP instance), `nb ≤ 30`;
`Q ≤ 2^64` fresh random-oracle keys. Then

  `Pr[accepted ∧ ¬Holds] ≤ 2^-82`.

The terms (all proved below): per-challenge max `≤ 2^-147` (batching `2^-147`; RAP+DEEP round
`2^-149`; fold `≤ 2^-154`; query `2^-162`), so `Q·max ≤ 2^-83`; sum `≤ 2^-144` (RAP, `32` rounds)
`+ 2^-146` (FRI side, `fri_side_le`). -/
theorem rap_fri_sound_deep_numbers {nb : ℕ} (hR0 : RapInput R0 nb)
    (hlink : ∀ m0 (tr : DeepTr P) fin χ, Rest m0 tr fin χ →
      (∀ i, ∀ x ∈ P.H, eval x (P.Cp χ (P.restr tr) i) = 0) → R0.Accepts m0 (P.restr tr) fin χ)
    (hnb : P.R + 1 < nb)
    (hRest : ∀ m0 (tr : DeepTr P) fin χ, RestV m0 fin χ →
      SatClaims (deepOI P) tr (deepClaims P A R0 χ fin) → Rest m0 tr fin.1 χ)
    (errOld : ℕ → ℝ≥0∞) (herr0 : ∀ m0 r, roundBound R0 blkOf m0 r ≤ errOld r)
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    -- the concrete parameters
    (hs : ∀ i, s i = 1) (hrate : 64 * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ n) (hn : n ≤ 32)
    (hF : goldilocks ^ 3 ≤ Fintype.card F) (hm : m + 1 ≤ 2 ^ 12)
    (htoPoly : P.toPoly = udDecodeB ω (31 / 64) (friBound s d))
    (hns : P.ns ≤ 2 ^ 20) (hD : P.D.card ≤ 2 ^ 32) (hH : P.H.card ≤ 2 ^ 32) (hnq : P.nq + 1 ≤ 2 ^ 8)
    (herrOld : ∀ r, errOld r ≤ (((2 ^ 150)⁻¹ : ℝ≥0) : ℝ≥0∞)) (hnb30 : nb ≤ 30)
    {Statement GlobalSalt W : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit
      (cRounds (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb
        (ω := ω) (S := F) s d 170))
    (adversary : SingleSaltAdversary Statement GlobalSalt W
      (cRounds (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb
        (ω := ω) (S := F) s d 170))
    (Q : ℕ) (hQ : Q ≤ 2 ^ 64)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (cRounds (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb
          (ω := ω) (S := F) s d 170) guards
        (cAccept (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb s d 170 m
          (univariatePowersGenerator F m)
          (fun _ tr fin χ => deepStmt (ω := ω) P A R0 e tr fin χ) hdom) adversary) ∅)}[
        (∃ x, joint.1.1.1 = some x) ∧ ¬ R0.Holds] ≤ (2 ^ 82 : ℝ≥0∞)⁻¹ := by
  -- the hypotheses of `rap_fri_sound_deep` at these parameters
  have hr : 64 * friBound s d ≤ 2 ^ n := hrate
  have hN1 : 0 < friBound s d := by unfold friBound; positivity
  have hN : friBound s d + 1 ≤ 2 ^ n := by omega
  have hδ : (31 / 64 : ℝ≥0) ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb ω) (friBound s d + 1) : Set (Fin (2 ^ n) → F)) :=
    relUDR_rs_ge _ _ (by rw [Fintype.card_fin]; omega)
  have hε := caError_powers_numbers (ω := ω) m (N := 2 ^ (∑ i, (s i).1) * d)
    (by positivity) hrate
  refine (rap_fri_sound_deep (ω := ω) P A R0 Rest RestV e I0 I Ifin s d 170
    (univariatePowersGenerator F m) hR0 hlink hnb hRest errOld herr0 hdom (31 / 64) (31 / 64) hN hδ
    htoPoly _ hε guards adversary Q queryBound).trans ?_
  -- the terms
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
  refine (add_le_add (mul_le_mul' hQ' hmax)
    (add_le_add (hsumR.trans (mul_le_mul' hnb' le_rfl)) hfri')).trans ?_
  rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_add, ← ENNReal.coe_add,
    show (2 ^ 82 : ℝ≥0∞)⁻¹ = (((2 ^ 82)⁻¹ : ℝ≥0) : ℝ≥0∞) by
      rw [ENNReal.coe_inv (by positivity), ENNReal.coe_pow, ENNReal.coe_ofNat]]
  refine ENNReal.coe_le_coe.mpr ?_
  rw [← NNReal.coe_le_coe]; push_cast; norm_num

end PostFS

end NockvmE2E.Succ.Numbers
