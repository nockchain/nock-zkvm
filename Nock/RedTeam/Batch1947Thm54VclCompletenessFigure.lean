/-
  Nock/RedTeam/Batch1947Thm54VclCompletenessFigure.lean

  **The completeness figure as a theorem.**

  `vcl_completeness_figure` (F = Goldilocks `Fp`): for the honest datum `HC : HonestVCLJ`, with `|𝕂| ≥ p²`
  (`p²` is `|Quad Fp|`; any larger `𝕂` only helps), the total mass
  `epsilonOf (CF.honestBad ++ MF.honestBad) < 2^-65`.
  Parameter mapping (`epsilon_honestBadCF` / `epsilon_bad`):  `N = h = nR = V.N` (rows of the run: `h := V.N` in `badT`,
  `nR = nRows t = V.N` by `HC.hN`), `R = (bfsRows (airReorder t)).length` (rows of the AIR-ordered tree),
  `Λ = 2^110` (`programLeafBound ≤ 2^110`), `nC = V.memRows tC`, `nP = V.memRows tP`.
  Hypotheses `N, R, nC, nP ≤ 2^31`.  Exact `ε = (1 + 3R(2Λ-1) + 5N + 1 + 5nC + 2nP)/|𝕂|² + (N + N²)/|𝕂|`;
  the `N²/|𝕂|` term (the `χ0` order event, `h = N`) dominates: `ε ≈ 2^62/p² > 2^-66`, so **k = 65 is the best
  power-of-two exponent** (`fig_not_66`: the dominant term `2^62/p²` is not below `2^-66`).
  The seed weight is `badSeedsT_card_le` and needs the generator-run facts `hs hf hG` (public subject/formula
  bounded by `q`, the `q`-bounded evaluator agrees); they are hypotheses here.
-/
import Nock.RedTeam.Batch1938Thm54VclCompletenessJoint
import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestBadPole

set_option autoImplicit false

namespace Nock.RedTeam.Batch1947

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.RedTeam.Batch1880 Nock.RedTeam.Batch1882 Nock.RedTeam.Batch1938

/-- The arithmetic of the figure: `X/c² + Y/c < 2^-65` for `c ≥ p²`, `X ≤ 2^145`, `Y ≤ 2^62 + 2^31`. -/
theorem fig_arith (c X Y : ℕ) (hc : Nock.Field.p ^ 2 ≤ c) (hX : X ≤ 2 ^ 145) (hY : Y ≤ 2 ^ 62 + 2 ^ 31) :
    (X : ℚ) / (c : ℚ) ^ 2 + (Y : ℚ) / (c : ℚ) < 1 / (2 : ℚ) ^ 65 := by
  have hp : Nock.Field.p = 18446744069414584321 := Nock.Field.p_eq
  have hc127 : 2 ^ 127 + 2 ^ 97 ≤ c := by
    refine le_trans ?_ hc; rw [hp]; norm_num
  have hcpos : 0 < c := by omega
  have key : (X + Y * c) * 2 ^ 65 < c ^ 2 := by
    have h1 : X * 2 ^ 65 ≤ c * 2 ^ 83 := by
      calc X * 2 ^ 65 ≤ 2 ^ 145 * 2 ^ 65 := Nat.mul_le_mul_right _ hX
        _ = 2 ^ 83 * 2 ^ 127 := by norm_num
        _ ≤ 2 ^ 83 * c := Nat.mul_le_mul_left _ (by omega)
        _ = c * 2 ^ 83 := by ring
    have h2 : Y * c * 2 ^ 65 ≤ (2 ^ 127 + 2 ^ 96) * c := by
      calc Y * c * 2 ^ 65 = (Y * 2 ^ 65) * c := by ring
        _ ≤ ((2 ^ 62 + 2 ^ 31) * 2 ^ 65) * c := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hY)
        _ = (2 ^ 127 + 2 ^ 96) * c := by norm_num
    have h3 : 2 ^ 127 + 2 ^ 96 + 2 ^ 83 < c := by omega
    calc (X + Y * c) * 2 ^ 65 = X * 2 ^ 65 + Y * c * 2 ^ 65 := by ring
      _ ≤ c * 2 ^ 83 + (2 ^ 127 + 2 ^ 96) * c := Nat.add_le_add h1 h2
      _ = c * (2 ^ 127 + 2 ^ 96 + 2 ^ 83) := by ring
      _ < c * c := Nat.mul_lt_mul_of_pos_left h3 hcpos
      _ = c ^ 2 := by ring
  have hq : (0 : ℚ) < (c : ℚ) := by exact_mod_cast hcpos
  have key' : ((X : ℚ) + Y * c) * 2 ^ 65 < (c : ℚ) ^ 2 := by exact_mod_cast key
  have e : (X : ℚ) / (c : ℚ) ^ 2 + (Y : ℚ) / (c : ℚ) = ((X : ℚ) + Y * c) / (c : ℚ) ^ 2 := by
    field_simp
  rw [e, div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- **Negative control (tightness)**: the dominant term `2^62 / p²` (`N = 2^31`, `N²/|𝕂|` at `|𝕂| = p²`) is NOT
below `2^-66`, so `k = 66` cannot be reached by this bound; `fig_arith` (k = 65) is the sharp power of two. -/
theorem fig_not_66 : ¬ ((2 : ℚ) ^ 62 / ((Nock.Field.p : ℕ) : ℚ) ^ 2 < 1 / (2 : ℚ) ^ 66) := by
  rw [Nock.Field.p_eq, not_lt, div_le_div_iff₀ (by norm_num) (by norm_num)]
  norm_num

section Goldilocks
variable {K : Type} [Field K] [Algebra Nock.Field.Fp K] [FiniteDimensional Nock.Field.Fp K] [Fintype K]
  [DecidableEq K] (δF : Nock.Field.Fp) [Fact (¬ IsSquare (algebraMap Nock.Field.Fp K δF))] (hT hP hC : ℕ)

open Classical in
/-- **The completeness figure, compiled.**  `Pr[some honest bad summand fires]`'s bound `ε` is below `2^-65`. -/
theorem vcl_completeness_figure (HC : HonestVCLJ (K := K) δF hT hP hC)
    (hleaf : programLeafBound (airReorder HC.t) ≤ 2 ^ 110)
    (hmemRows : ∀ k, HC.V.memRows k + 1 < ringChar Nock.Field.Fp)
    (haxis : programAxisBound (airReorder HC.t) < 2 ^ 63)
    (hK : Nock.Field.p ^ 2 ≤ Fintype.card K)
    (hN : HC.V.N ≤ 2 ^ 31) (hR : (bfsRows (airReorder HC.t)).length ≤ 2 ^ 31)
    (hnC : HC.V.memRows (tC hT hP) ≤ 2 ^ 31) (hnP : HC.V.memRows (tP hT hP) ≤ 2 ^ 31)
    {q : ℕ} (hqb : 1 < q) (hle : q ≤ ringChar (Quad (algebraMap Nock.Field.Fp K δF)))
    (hs : FieldEmbedding.BoundedBy q HC.V.claim.subject) (hf : FieldEmbedding.BoundedBy q HC.V.claim.formula)
    (hG : FieldEmbedding.evalGBy q HC.fuel HC.V.claim.subject HC.V.claim.formula = some HC.V.claim.result) :
    epsilonOf ((CFv (K := K) δF hT hP hC).honestBad HC.toHonestVCLT ++
      (MFv (K := K) δF hT hP hC).honestBad
        (jointMem δF HC.toHonestVCLT
          (jointMemFacts_of HC (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq
            hleaf hmemRows haxis))) < 1 / (2 : ℚ) ^ 65 := by
  have hconf : TraceConfined (2 ^ 110) (airReorder HC.t) := traceConfined_of_leafBound hleaf
  have hS := badSeedsT_card_le (δ := δF) hqb hle hs hf hG HC.hgen (Λ := 2 ^ 110) Nat.one_le_two_pow hconf
  have hA : epsilonOf ((CFv (K := K) δF hT hP hC).honestBad HC.toHonestVCLT) =
      ((badSeedsT δF HC.t).card : ℚ) / (Fintype.card K : ℚ) ^ 2 +
        ((nRows HC.t * (Fintype.card K * Fintype.card K) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 3 +
        ((HC.V.N * HC.V.N : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 1 +
        5 * ((HC.V.N * (Fintype.card K * Fintype.card K) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 4 :=
    epsilon_honestBadCF δF HC.t _ le_rfl _ le_rfl HC.V.N HC.V.hN HC.V (fun i => stT HC.t i)
  have hB : epsilonOf ((MFv (K := K) δF hT hP hC).honestBad
        (jointMem δF HC.toHonestVCLT
          (jointMemFacts_of HC (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq
            hleaf hmemRows haxis))) =
      (1 + 5 * (HC.V.memRows (tC hT hP) : ℚ) + 2 * (HC.V.memRows (tP hT hP) : ℚ)) /
        (Fintype.card K : ℚ) ^ 2 :=
    epsilon_bad (C := tableVCLT hC) (H := jointMem δF HC.toHonestVCLT
          (jointMemFacts_of HC (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq
            hleaf hmemRows haxis))
  have hcpos : (0 : ℚ) < (Fintype.card K : ℚ) := by
    have : 0 < Fintype.card K := Fintype.card_pos
    exact_mod_cast this
  have hcne : (Fintype.card K : ℚ) ≠ 0 := hcpos.ne'
  rw [show ∀ {Tr : Type} {St : (Coins frameVCL K → Tr) → Prop} (a b : List (BadSummand frameVCL K Tr St)),
      epsilonOf (a ++ b) = epsilonOf a + epsilonOf b from fun a b => by
        unfold epsilonOf; rw [List.map_append, List.sum_append], hA, hB]
  have hNn : HC.V.N = nRows HC.t := HC.hN
  set c : ℕ := Fintype.card K with hcdef
  have hwS : (badSeedsT δF HC.t).card ≤ 2 ^ 144 := by
    refine hS.trans ?_
    unfold seedWeightT
    have h1 : (bfsRows (airReorder HC.t)).length * (3 * (2 * 2 ^ 110 - 1)) ≤ 2 ^ 31 * (3 * (2 * 2 ^ 110)) :=
      Nat.mul_le_mul hR (Nat.mul_le_mul_left _ (by omega))
    have h2 : (2 : ℕ) ^ 31 * (3 * (2 * 2 ^ 110)) + 1 ≤ 2 ^ 144 := by norm_num
    omega
  have e : (((badSeedsT δF HC.t).card : ℚ) / (c : ℚ) ^ 2 +
        ((nRows HC.t * (c * c) : ℕ) : ℚ) / (c : ℚ) ^ 3 + ((HC.V.N * HC.V.N : ℕ) : ℚ) / (c : ℚ) ^ 1 +
        5 * ((HC.V.N * (c * c) : ℕ) : ℚ) / (c : ℚ) ^ 4) +
      (1 + 5 * (HC.V.memRows (tC hT hP) : ℚ) + 2 * (HC.V.memRows (tP hT hP) : ℚ)) / (c : ℚ) ^ 2 =
      (((badSeedsT δF HC.t).card + 5 * HC.V.N + (1 + 5 * HC.V.memRows (tC hT hP) + 2 * HC.V.memRows (tP hT hP)) : ℕ) : ℚ)
          / (c : ℚ) ^ 2 +
        ((HC.V.N + HC.V.N * HC.V.N : ℕ) : ℚ) / (c : ℚ) := by
    rw [← hNn]
    push_cast
    field_simp
    ring
  rw [e]
  exact fig_arith c _ _ hK (by omega) (by
    have : HC.V.N * HC.V.N ≤ 2 ^ 31 * 2 ^ 31 := Nat.mul_le_mul hN hN
    norm_num at this ⊢; omega)

end Goldilocks

end Nock.RedTeam.Batch1947

#print axioms Nock.RedTeam.Batch1947.fig_arith
#print axioms Nock.RedTeam.Batch1947.fig_not_66
#print axioms Nock.RedTeam.Batch1947.vcl_completeness_figure

