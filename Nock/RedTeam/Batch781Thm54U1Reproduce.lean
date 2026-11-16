/-
  Nock/RedTeam/Batch781Thm54U1Reproduce.lean

  * `rowEnv` / `deployed_row_accepts`: a one-row builder for the Form R block (columns `202..295`)
    and the generic per-row acceptance criterion of the 97 deployed base-field gates.
  * `formR_mem_deployed`: the 97 are a sublist of `correctedFinalComputeAllGates`, the list both
    `P.computeChip` and `computeChipAt c` commit (`CorrectedFinalComputeRAP.C`).
  * `row769_accepted`: `p = 769`, shift `63 > n − 1 = 9`, leaf `2^63` — all 97 vanished (the
    `sameproblem-scope` row).

  Gate level only (one row).  Not compiled: a full accepted trace / the capstone.
-/
import Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
import Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
import Nock.Field
import Nock.RedTeam.Batch557Thm54RangeGadget

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Nock.RedTeam.Batch781

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Module

section Generic

variable {F : Type*} [Field F]

/-- One compute row carrying a Form R certificate block: `op₀ = 1`, `f_t.leaf = leaf`,
certificate bits `cb` (column `202 + j` = `c_{j+1}`), shift bits of `m`, `h`/`t` the honest
power helpers of `m`, `P`, `top`, eq-chain helpers `E`. Every other column `0`. -/
noncomputable def rowEnv (leaf : F) (cb : ℕ → Bool) (m : ℕ) (P top : F) (E : ℕ → F) : Env F :=
  ⟨fun i =>
    if i = 0 then 1
    else if i = 136 then leaf
    else if 202 ≤ i ∧ i < 265 then bit01 (cb (i - 202))
    else if 265 ≤ i ∧ i < 271 then bit01 (m.testBit (i - 265))
    else if i = 271 then powBits (2 : F) m 3
    else if i = 272 then powBits (2 : F) m 6
    else if i = 273 then P
    else if i = 274 then top
    else if 275 ≤ i ∧ i < 296 then E (i - 275)
    else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

variable (leaf : F) (cb : ℕ → Bool) (m : ℕ) (P top : F) (E : ℕ → F)

theorem rowEnv_c (j : ℕ) (hj : j < 63) :
    (rowEnv leaf cb m P top E).trace (col0 + j) = bit01 (cb j) := by
  have e : 202 + j - 202 = j := by omega
  simp only [rowEnv, col0, e]
  split_ifs <;> first | rfl | omega

theorem rowEnv_m (k : ℕ) (hk : k < 6) :
    (rowEnv leaf cb m P top E).trace (col0 + 63 + k) = bit01 (m.testBit k) := by
  have e : 202 + 63 + k - 265 = k := by omega
  simp only [rowEnv, col0, e]
  split_ifs <;> first | rfl | omega

theorem rowEnv_h : (rowEnv leaf cb m P top E).trace (col0 + 69) = powBits (2 : F) m 3 := by
  simp [rowEnv, col0]
theorem rowEnv_t : (rowEnv leaf cb m P top E).trace (col0 + 70) = powBits (2 : F) m 6 := by
  simp [rowEnv, col0]
theorem rowEnv_P : (rowEnv leaf cb m P top E).trace (col0 + 71) = P := by
  simp [rowEnv, col0]
theorem rowEnv_top : (rowEnv leaf cb m P top E).trace (col0 + 72) = top := by
  simp [rowEnv, col0]
theorem rowEnv_E (k : ℕ) (hk : k < 21) :
    (rowEnv leaf cb m P top E).trace (col0 + 73 + k) = E k := by
  have e : 202 + 73 + k - 275 = k := by omega
  simp only [rowEnv, col0, e]
  split_ifs <;> first | rfl | omega
theorem rowEnv_op0 : (rowEnv leaf cb m P top E).trace 0 = 1 := by simp [rowEnv]
theorem rowEnv_op9 : (rowEnv leaf cb m P top E).trace 9 = 0 := by simp [rowEnv]
theorem rowEnv_leaf : (rowEnv leaf cb m P top E).trace 136 = leaf := by simp [rowEnv]

/-- Booleanity, and (C2) the pin `c_j = 0` for `j + 1 > n − 1` given `hjunk`. -/
theorem rowEnv_boolean (hjunk : ∀ j, formRN F - 1 < j + 1 → cb j = false) :
    ∀ g ∈ booleanGates (F := F), g.eval (rowEnv leaf cb m P top E) = 0 := by
  intro g hg
  simp only [booleanGates, List.mem_append, List.mem_map, List.mem_range] at hg
  rcases hg with ⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩
  · split_ifs with hjn
    · simp only [colC, bcur, CoeffExpr.eval]
      rw [rowEnv_c leaf cb m P top E j hj, hjunk j hjn]; rfl
    simp only [bbool, colC, bcur, CoeffExpr.eval]
    rw [rowEnv_c leaf cb m P top E j hj]; exact bit01_mul_sub _
  · simp only [bbool, colM, bcur, CoeffExpr.eval]
    rw [rowEnv_m leaf cb m P top E k hk]; exact bit01_mul_sub _

theorem rowEnv_power : ∀ g ∈ powerPins (F := F), g.eval (rowEnv leaf cb m P top E) = 0 := by
  intro g hg
  have hfac (k : ℕ) (hk : k < 6) (x : F) :
      (1 : F) + (rowEnv leaf cb m P top E).trace (202 + 63 + k) * (x - 1) =
        if m.testBit k then x else 1 := by
    have := rowEnv_m leaf cb m P top E k hk
    simp only [col0] at this
    rw [this, bit_switch]
  simp only [powerPins, List.mem_cons, List.not_mem_nil, or_false] at hg
  have hH := rowEnv_h leaf cb m P top E
  have hT := rowEnv_t leaf cb m P top E
  simp only [col0] at hH hT
  rcases hg with rfl | rfl
  · simp only [hPin, factor2, CoeffExpr.eval, colHbase, colM, col0, bcur, hH]
    rw [hfac 0 (by decide), hfac 1 (by decide), hfac 2 (by decide), powBits_three]
    ring
  · simp only [tPin, factor2, CoeffExpr.eval, colHbase, colTbase, colM, col0, bcur, hH, hT]
    rw [hfac 3 (by decide), hfac 4 (by decide), hfac 5 (by decide), powBits_high]
    ring

/-- `lm k` evaluates to the bit-match indicator of `m` against `n − 1`. -/
theorem rowEnv_lm (k : ℕ) (hk : k < 6) :
    (lm (F := F) k).eval (rowEnv leaf cb m P top E) = matchedLm F m k := by
  rw [lm_eval, rowEnv_m leaf cb m P top E k hk]
  unfold matchedLm; split_ifs <;> rfl

theorem rowEnv_pPin (hP : P = matchedP F m) :
    (pPin (F := F)).eval (rowEnv leaf cb m P top E) = 0 := by
  change (rowEnv leaf cb m P top E).trace (col0 + 71) - ((lm (F := F) 5).eval _ *
      (lm (F := F) 4).eval _ * (lm (F := F) 3).eval _) = 0
  rw [rowEnv_P, rowEnv_lm leaf cb m P top E 5 (by decide),
    rowEnv_lm leaf cb m P top E 4 (by decide), rowEnv_lm leaf cb m P top E 3 (by decide), hP]
  simp [matchedP]

/-- **The deployed per-row acceptance criterion, generic.**  If `top ∈ {0, 1}` is the bit-matched
top of `m` (U1), `P` is the bit-matched product, the bits beyond `n − 1` are `0` (C2), the helpers are the `top`-seeded eq-chain of the certificate bits of `a`,
the range gate holds, the comparison holds when `top = 1`, and `leaf = t·csum`, then all 97
deployed base-field Form R gates vanish. -/
theorem deployed_row_accepts (a : ℕ)
    (htop : top = 0 ∨ top = 1) (htopM : top = matchedTop F m) (hP : P = matchedP F m)
    (hjunk : ∀ j, formRN F - 1 < j + 1 → certCBit a j = false)
    (hE : ∀ k, k < 21 → E k = top * certEqRun a (3 * (k + 1)))
    (hR : (rangeGate (F := F)).eval (rowEnv leaf (certCBit a) m P top E) = 0)
    (hlt : top = 1 → certLt (F := F) a 63 = 1)
    (hax : leaf = powBits (2 : F) m 6 * (csum (F := F)).eval (rowEnv leaf (certCBit a) m P top E)) :
    ∀ g ∈ formRCertificateGates (F := F), g.eval (rowEnv leaf (certCBit a) m P top E) = 0 := by
  set env := rowEnv leaf (certCBit a) m P top E with henv
  have hC := rowEnv_c leaf (certCBit a) m P top E
  have hT := rowEnv_top leaf (certCBit a) m P top E
  intro g hg
  simp only [formRCertificateGates, formRPins, formRNamed, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with (((hb | hp) | (rfl | rfl)) | hh) | (rfl | rfl | rfl)
  · exact rowEnv_boolean _ _ _ _ _ _ hjunk g hb
  · exact rowEnv_power _ _ _ _ _ _ g hp
  · exact rowEnv_pPin _ _ _ _ _ _ hP
  · rw [topPin_eval, hT, rowEnv_P, rowEnv_lm _ _ _ _ _ _ 2 (by decide),
      rowEnv_lm _ _ _ _ _ _ 1 (by decide), rowEnv_lm _ _ _ _ _ _ 0 (by decide), hP, htopM]
    unfold matchedTop; ring
  · simp only [helperPins, List.mem_map, List.mem_range] at hh
    obtain ⟨k, hk, rfl⟩ := hh
    rcases htop with h0 | h1
    · refine helperPinAt_eval_of_top0 env (hT.trans h0) (fun t ht => ?_) k hk
      rw [rowEnv_E _ _ _ _ _ _ t ht, hE t ht, h0, zero_mul]
    · refine helperPinAt_eval_of_certRun env a (hT.trans h1) hC (fun t ht => ?_) k hk
      rw [rowEnv_E _ _ _ _ _ _ t ht, hE t ht, h1, one_mul]
  · rcases htop with h0 | h1
    · refine comparisonGate_eval_of_top0 env (hT.trans h0) (fun t ht => ?_)
      rw [rowEnv_E _ _ _ _ _ _ t ht, hE t ht, h0, zero_mul]
    · refine comparisonGate_eval_of_certRun env a (hT.trans h1) hC (fun t ht => ?_) (hlt h1)
      rw [rowEnv_E _ _ _ _ _ _ t ht, hE t ht, h1, one_mul]
  · exact hR
  · refine axisEquation_eval_of_products env ?_ ?_
    · rw [rowEnv_op0, rowEnv_leaf, rowEnv_t, ← hax]; ring
    · rw [rowEnv_op9]; ring

end Generic

/-- The 97 Form R gates are a sublist of the deployed compute gate list that both
`P.computeChip` and the family `computeChipAt c` commit (`CorrectedFinalComputeRAP.C`,
`ProductionNamedComputeRAP := CorrectedFinalFixedPreprocessingRAP`): every accepted row satisfies
them, and they are the only gates reading the shift / top / helper columns `265..295`. -/
theorem formR_mem_deployed {F K : Type*} [Field F] [Field K] [Algebra F K] (n : ℕ)
    (b : Basis (Fin 3) F K) :
    ∀ g ∈ formRCertificateGates (F := F),
      g ∈ OptimizedComputeCorrectedFinal.correctedFinalComputeAllGates n b := by
  intro g hg
  simp only [OptimizedComputeCorrectedFinal.correctedFinalComputeAllGates, List.mem_append]
  exact Or.inl (Or.inl (Or.inr hg))

/-! ## The scope's counterexample, re-derived at PV through the builder (`p = 769`) -/

section At769

instance fact769 : Fact (Nat.Prime 769) := ⟨by norm_num⟩

abbrev F769 := ZMod 769

theorem ringChar_769 : ringChar F769 = 769 := ZMod.ringChar_zmod_n 769
theorem formRN_769 : formRN F769 = 10 := by
  rw [formRN, ringChar_769]; exact Nock.RedTeam.Batch557.size_769
theorem nMinus1Low_769 : nMinus1Low F769 = 9 := by simp [nMinus1Low, formRN_769]

theorem size_two_pow_63 : Nat.size (2 ^ 63) = 64 := Nat.size_pow
theorem certShift_two_pow_63 : certShift (2 ^ 63) = 63 := by
  unfold certShift; rw [size_two_pow_63]
theorem certCBit_two_pow_63 (j : ℕ) : certCBit (2 ^ 63) j = false := by
  unfold certCBit
  rw [certShift_two_pow_63]
  split_ifs with h
  · rw [Nat.testBit_two_pow]; simp; omega
  · rfl

/-- The scope's row: `a = 2^63` (shift `63`, all certificate bits `0`), `top = 1`, leaf `2^63`. -/
noncomputable def row769 : Env F769 :=
  rowEnv ((2 : F769) ^ 63) (certCBit (2 ^ 63)) 63 (matchedP F769 63) 1
    (fun k => 1 * certEqRun (2 ^ 63) (3 * (k + 1)))

theorem msb_lt_769 :
    msbVal (certCBit (2 ^ 63)) < msbVal (fun j => pBit F769 (formRN F769 - 1 - j)) := by
  have hc : ringChar F769 ≠ 0 := by rw [ringChar_769]; norm_num
  have hP := leftoverP_msbVal_of_lt64 (F := F769) hc (by rw [formRN_769]; norm_num)
  have hC := leftoverC_msbVal_of_shift (2 ^ 63) (by positivity)
    (by rw [certShift_two_pow_63])
  rw [certShift_two_pow_63] at hC
  rw [hC, formRN_769]; rw [ringChar_769, formRN_769] at hP
  simp only [Nat.sub_self, zero_mul]
  refine lt_of_lt_of_le ?_ hP; norm_num

theorem row769_accepted : ¬ ∀ g ∈ formRCertificateGates (F := F769), g.eval row769 = 0 := by
  intro h
  have ht := h topPin (by simp [formRCertificateGates, formRPins])
  rw [topPin_eval, row769, rowEnv_top, rowEnv_P,
    rowEnv_lm _ _ _ _ _ _ 2 (by decide), rowEnv_lm _ _ _ _ _ _ 1 (by decide),
    rowEnv_lm _ _ _ _ _ _ 0 (by decide)] at ht
  have h1 : matchedLm F769 63 1 = 0 := by
    simp only [matchedLm, nMinus1Bit, formRN_769]
    rw [if_neg (by decide), show Nat.testBit 63 1 = true by decide]; simp
  rw [h1] at ht; simp at ht

theorem row769_leaf_small : ((2 : F769) ^ 63).val < 2 ^ formRN F769 := by
  rw [formRN_769]; exact lt_trans (ZMod.val_lt _) (by norm_num)

end At769

/-! ## `cert_ambiguous_31` re-opened at the deployed gates (`p = 31`, `n = 5`) -/

section At31

instance fact31 : Fact (Nat.Prime 31) := ⟨by norm_num⟩

abbrev F31 := ZMod 31

theorem ringChar_31 : ringChar F31 = 31 := ZMod.ringChar_zmod_n 31
theorem formRN_31 : formRN F31 = 5 := by
  rw [formRN, ringChar_31]; exact Nock.RedTeam.Batch557.size_31
theorem nMinus1Low_31 : nMinus1Low F31 = 4 := by simp [nMinus1Low, formRN_31]

theorem size_34 : Nat.size 34 = 6 :=
  le_antisymm (Nat.size_le.mpr (by norm_num)) (Nat.lt_size.mpr (by norm_num))
theorem certShift_34 : certShift 34 = 5 := by simp [certShift, size_34]

noncomputable def row31 : Env F31 :=
  rowEnv ((34 : ℕ) : F31) (certCBit 34) 5 (matchedP F31 5) 1
    (fun k => 1 * certEqRun 34 (3 * (k + 1)))

theorem msb_lt_31 :
    msbVal (certCBit 34) < msbVal (fun j => pBit F31 (formRN F31 - 1 - j)) := by
  have hc : ringChar F31 ≠ 0 := by rw [ringChar_31]; norm_num
  have hP := leftoverP_msbVal_of_lt64 (F := F31) hc (by rw [formRN_31]; norm_num)
  have hC := leftoverC_msbVal_of_shift 34 (by norm_num) (by rw [certShift_34]; norm_num)
  rw [certShift_34] at hC
  rw [hC, formRN_31]; rw [ringChar_31, formRN_31] at hP
  refine lt_of_lt_of_le ?_ hP; norm_num

theorem row31_accepted : ¬ ∀ g ∈ formRCertificateGates (F := F31), g.eval row31 = 0 := by
  intro h
  have ht := h topPin (by simp [formRCertificateGates, formRPins])
  rw [topPin_eval, row31, rowEnv_top, rowEnv_P,
    rowEnv_lm _ _ _ _ _ _ 2 (by decide), rowEnv_lm _ _ _ _ _ _ 1 (by decide),
    rowEnv_lm _ _ _ _ _ _ 0 (by decide)] at ht
  have h0 : matchedLm F31 5 0 = 0 := by
    simp [matchedLm, nMinus1Bit, formRN_31]
  rw [h0] at ht; simp at ht

theorem row31_leaf : ((34 : ℕ) : F31) = ((3 : ℕ) : F31) := by decide

end At31

end Nock.RedTeam.Batch781

#print axioms Nock.RedTeam.Batch781.deployed_row_accepts
#print axioms Nock.RedTeam.Batch781.row769_accepted
#print axioms Nock.RedTeam.Batch781.row31_accepted
#print axioms Nock.RedTeam.Batch781.formR_mem_deployed
