/-
  Nock/RedTeam/Batch784Thm54FormRAliasesSurviveU1.lean

  **U1 pre-greenlight, Q2 continued:
  two certificate aliases that the U1 `topPin` does NOT close, compiled at the 97 deployed
  base-field Form R gates AND at the U1 pin.**

  * **A. The comparison gate is misaligned by one bit, at every width — Goldilocks included.**
    Column `202 + j` holds `c_{j+1}` (`colC`, `csumAcc`: weight `2^{−(j+1)}`), i.e. bit `n − 2 − j`
    of a shift-`(n−1)` certificate `a`; `linCol j` / `comparisonTerms` compare it against
    `pBit (n − 1 − j)`.
    - `goldilocks_alias`: at `p = 2^64 − 2^32 + 1` the row with shift `63` and the bits of
      `a = p + 1` passes all 97 deployed gates and the U1 pin, with leaf `1`.  The honest
      certificate of the atom `1` has shift `0`: axis `p + 1` (a 63-step path) is accepted for the
      formula atom `1`.
    - `alias800_at_769`: at `p = 769` the shift-`9` certificate of `a = 800` (leaf `31`) passes
      the deployed gates and U1.  `31`'s honest certificate has shift `4`.
  * **B. Below width 64 the axis equation reads certificate columns the record does not.**
    `csum` sums all 63 columns; `sampledCprime` drops `j + 1 > n − 1` (`lamPowVar` is `0` there)
    and `Padding` stops at `n − 1`.  `junk_alias_at_769`: shift `0`, `c_1..c_9 = 0` (the record
    `(λ^0, λ^9)` of axis `1`, i.e. the honest record of the atom `1`), junk `c_32 = c_47 = 1`;
    `1 + 2^{−32} + 2^{−47} = 2` in `𝔽_769`, so the row's leaf is `2`.  All 97 deployed gates and the
    U1 pin vanish (`top = 0`: the comparison is not consulted).

  Both are gate-level (one row, the committed base gates).  Not compiled: a full accepted trace
  at `computeChipAt c` / the capstone.  No production edit.

  The `topPinU1` replica facts (`row*_u1`) are unchanged: they record that U1 alone did not
  close them.
-/
import Nock.RedTeam.Batch806Thm54FormRRepairSound
import Nock.Field

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch784

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.RedTeam.Batch781
open Nock.RedTeam.Batch782

section Generic

variable {F : Type*} [Field F]

/-- U1 on a builder row whose shift is exactly `n − 1` (low six bits) and `top = 1`. -/
theorem u1_of_eq_nMinus1 (leaf : F) (cb : ℕ → Bool) (E : ℕ → F) :
    (topPinU1 (F := F)).eval
      (rowEnv leaf cb (nMinus1Low F) (matchedP F (nMinus1Low F)) 1 E) = 0 := by
  rw [topPinU1_eval, rowEnv_top, rowEnv_P, rowEnv_lm _ _ _ _ _ _ 2 (by decide),
    rowEnv_lm _ _ _ _ _ _ 1 (by decide), rowEnv_lm _ _ _ _ _ _ 0 (by decide)]
  have := matchedTop_nMinus1 (F := F)
  unfold matchedTop at this
  rw [this]; ring

/-- U1 on a builder row with `top = matchedTop m` (in particular `top = 0` when `m ≠ n − 1`). -/
theorem u1_of_matched (leaf : F) (cb : ℕ → Bool) (m : ℕ) (E : ℕ → F) :
    (topPinU1 (F := F)).eval
      (rowEnv leaf cb m (matchedP F m) (matchedTop F m) E) = 0 := by
  rw [topPinU1_eval, rowEnv_top, rowEnv_P, rowEnv_lm _ _ _ _ _ _ 2 (by decide),
    rowEnv_lm _ _ _ _ _ _ 1 (by decide), rowEnv_lm _ _ _ _ _ _ 0 (by decide)]
  unfold matchedTop; ring

/-- `csum` as a sum. -/
theorem csumAcc_eval_sum (env : Env F) :
    ∀ n, (csumAcc (F := F) n).eval env =
      1 + ∑ j ∈ Finset.range n, env.trace (col0 + j) * twoInv ^ (j + 1) := by
  intro n
  induction n with
  | zero => simp [csumAcc, CoeffExpr.eval]
  | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih]
      simp [csumAcc, CoeffExpr.eval, colC, bcur]

/-- Acceptance of a `top = 0` builder row with ARBITRARY certificate bits: the comparison and the
eq-chain are not consulted. -/
theorem deployed_row_accepts_top0 (leaf : F) (cb : ℕ → Bool) (m : ℕ) (P : F)
    (hP : P = matchedP F m) (htop0 : matchedTop F m = 0)
    (hjunk : ∀ j, formRN F - 1 < j + 1 → cb j = false)
    (hR : (rangeGate (F := F)).eval (rowEnv leaf cb m P 0 (fun _ => 0)) = 0)
    (hax : leaf = powBits (2 : F) m 6 * (csum (F := F)).eval (rowEnv leaf cb m P 0 (fun _ => 0))) :
    ∀ g ∈ formRCertificateGates (F := F), g.eval (rowEnv leaf cb m P 0 (fun _ => 0)) = 0 := by
  set env := rowEnv leaf cb m P 0 (fun _ => 0) with henv
  have hT := rowEnv_top leaf cb m P (0 : F) (fun _ => 0)
  have hE : ∀ t, t < 21 → env.trace (col0 + 73 + t) = 0 := fun t ht => by
    rw [henv, rowEnv_E _ _ _ _ _ _ t ht]
  intro g hg
  simp only [formRCertificateGates, formRPins, formRNamed, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with (((hb | hp) | (rfl | rfl)) | hh) | (rfl | rfl | rfl)
  · exact rowEnv_boolean _ _ _ _ _ _ hjunk g hb
  · exact rowEnv_power _ _ _ _ _ _ g hp
  · exact rowEnv_pPin _ _ _ _ _ _ hP
  · rw [topPin_eval, hT, rowEnv_P, rowEnv_lm _ _ _ _ _ _ 2 (by decide),
      rowEnv_lm _ _ _ _ _ _ 1 (by decide), rowEnv_lm _ _ _ _ _ _ 0 (by decide), hP]
    unfold matchedTop at htop0; rw [htop0]; ring
  · simp only [helperPins, List.mem_map, List.mem_range] at hh
    obtain ⟨k, hk, rfl⟩ := hh
    exact helperPinAt_eval_of_top0 env hT hE k hk
  · exact comparisonGate_eval_of_top0 env hT hE
  · exact hR
  · refine axisEquation_eval_of_products env ?_ ?_
    · rw [rowEnv_op0, rowEnv_leaf, rowEnv_t, ← hax]; ring
    · rw [rowEnv_op9]; ring

end Generic

/-! ## A1. `p = 769`: axis `800` for the leaf `31` (shift `9 = n − 1`) -/

section Alias800

theorem nMinus1Bit_769 (k : ℕ) : nMinus1Bit F769 k = (9 : ℕ).testBit k := by
  simp [nMinus1Bit, formRN_769]

theorem size_800 : Nat.size 800 = 10 :=
  le_antisymm (Nat.size_le.mpr (by norm_num)) (Nat.lt_size.mpr (by norm_num))
theorem certShift_800 : certShift 800 = 9 := by simp [certShift, size_800]

noncomputable def row800 : Env F769 :=
  rowEnv ((800 : ℕ) : F769) (certCBit 800) (nMinus1Low F769) (matchedP F769 (nMinus1Low F769)) 1
    (fun k => 1 * certEqRun 800 (3 * (k + 1)))

theorem msb_lt_800 :
    msbVal (certCBit 800) < msbVal (fun j => pBit F769 (formRN F769 - 1 - j)) := by
  have hc : ringChar F769 ≠ 0 := by rw [ringChar_769]; norm_num
  have hP := leftoverP_msbVal_of_lt64 (F := F769) hc (by rw [formRN_769]; norm_num)
  have hC := leftoverC_msbVal_of_shift 800 (by norm_num) (by rw [certShift_800]; norm_num)
  rw [certShift_800] at hC
  rw [hC, formRN_769]; rw [ringChar_769, formRN_769] at hP
  refine lt_of_lt_of_le ?_ hP; norm_num

theorem row800_accepted : ¬ ∀ g ∈ formRCertificateGates (F := F769), g.eval row800 = 0 := by
  intro h
  have hlt := Nock.RedTeam.Batch806.formR_cert_lt_p (F := F769) row800 800
    (by rw [ringChar_769]; norm_num) (by rw [ringChar_769]; norm_num) (by norm_num) (by norm_num)
    (fun j hj => by rw [row800, rowEnv_c _ _ _ _ _ _ j hj])
    (fun k hk => by rw [row800, rowEnv_m _ _ _ _ _ _ k hk, certShift_800, nMinus1Low_769]) h
  rw [ringChar_769] at hlt
  omega

theorem row800_u1 : (topPinU1 (F := F769)).eval row800 = 0 := u1_of_eq_nMinus1 _ _ _

theorem alias800_at_769 :
    (¬ ∀ g ∈ formRCertificateGates (F := F769), g.eval row800 = 0) ∧
      (topPinU1 (F := F769)).eval row800 = 0 ∧
      ((800 : ℕ) : F769) = ((31 : ℕ) : F769) ∧ 769 ≤ 800 ∧ certShift 31 = 4 := by
  refine ⟨row800_accepted, row800_u1, by decide, by norm_num, ?_⟩
  have : Nat.size 31 = 5 := Nock.RedTeam.Batch557.size_31
  simp [certShift, this]

end Alias800

/-! ## A2. Goldilocks: axis `p + 1` for the leaf `1` -/

section Goldilocks

abbrev GF := Nock.Field.Fp

theorem ringChar_GF : ringChar GF = Nock.Field.p := ZMod.ringChar_zmod_n _
theorem formRN_GF : formRN GF = 64 := by
  rw [formRN, ringChar_GF]; exact Nock.RedTeam.Batch557.size_goldilocks
theorem nMinus1Low_GF : nMinus1Low GF = 63 := by simp [nMinus1Low, formRN_GF]

/-- The aliased certificate value `a = p + 1`. -/
def aG : ℕ := Nock.Field.p + 1

theorem size_aG : Nat.size aG = 64 :=
  le_antisymm (Nat.size_le.mpr (by norm_num [aG, Nock.Field.p]))
    (Nat.lt_size.mpr (by norm_num [aG, Nock.Field.p]))
theorem certShift_aG : certShift aG = 63 := by simp [certShift, size_aG]

noncomputable def rowG : Env GF :=
  rowEnv ((aG : ℕ) : GF) (certCBit aG) (nMinus1Low GF) (matchedP GF (nMinus1Low GF)) 1
    (fun k => 1 * certEqRun aG (3 * (k + 1)))

theorem two_ne_zero_GF : (2 : GF) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : GF) = 0 := by exact_mod_cast h
  have hv : ((2 : ℕ) : GF).val = 2 := ZMod.val_natCast_of_lt (by norm_num [Nock.Field.p])
  rw [h', ZMod.val_zero] at hv
  exact absurd hv (by norm_num)

theorem msb_lt_G :
    msbVal (certCBit aG) < msbVal (fun j => pBit GF (formRN GF - 1 - j)) := by
  rw [leftoverP_msbVal_64 (F := GF) formRN_GF, ringChar_GF,
    leftoverC_msbVal_of_shift aG (by norm_num [aG]) (by rw [certShift_aG]), certShift_aG]
  norm_num [aG, Nock.Field.p]

theorem rowG_accepted : ¬ ∀ g ∈ formRCertificateGates (F := GF), g.eval rowG = 0 := by
  intro h
  have hlt := Nock.RedTeam.Batch806.formR_cert_lt_p (F := GF) rowG aG
    (by rw [ringChar_GF]; norm_num [Nock.Field.p]) (by rw [ringChar_GF]; norm_num [Nock.Field.p])
    (by norm_num [aG]) (by norm_num [aG, Nock.Field.p])
    (fun j hj => by rw [rowG, rowEnv_c _ _ _ _ _ _ j hj])
    (fun k hk => by rw [rowG, rowEnv_m _ _ _ _ _ _ k hk, certShift_aG, nMinus1Low_GF]) h
  rw [ringChar_GF] at hlt
  simp [aG] at hlt

theorem rowG_u1 : (topPinU1 (F := GF)).eval rowG = 0 := u1_of_eq_nMinus1 _ _ _

theorem goldilocks_alias :
    (¬ ∀ g ∈ formRCertificateGates (F := GF), g.eval rowG = 0) ∧
      (topPinU1 (F := GF)).eval rowG = 0 ∧
      ((aG : ℕ) : GF) = 1 ∧ Nock.Field.p < aG ∧ certShift aG = 63 ∧ certShift 1 = 0 := by
  refine ⟨rowG_accepted, rowG_u1, ?_, by simp [aG], certShift_aG, by decide⟩
  simp [aG]

end Goldilocks

/-! ## B. `p = 769`: junk certificate bits beyond `n − 1` (record of axis `1`, leaf `2`) -/

section Junk

/-- Certificate bits `c_32`, `c_47` (columns `31`, `46`); `c_1..c_9` are zero. -/
def junkBits (j : ℕ) : Bool := j = 31 ∨ j = 46

noncomputable def rowJ : Env F769 :=
  rowEnv (2 : F769) junkBits 0 (matchedP F769 0) 0 (fun _ => 0)

theorem twoInv_769 : (twoInv : F769) = 385 := by
  unfold twoInv
  exact inv_eq_of_mul_eq_one_right (by decide)

theorem csum_rowJ : (csum (F := F769)).eval rowJ = 2 := by
  rw [csum, csumAcc_eval_sum, twoInv_769]
  have h : ∀ j ∈ Finset.range 63, rowJ.trace (col0 + j) * (385 : F769) ^ (j + 1) =
      if junkBits j then (385 : F769) ^ (j + 1) else 0 := fun j hj => by
    rw [rowJ, rowEnv_c _ _ _ _ _ _ j (Finset.mem_range.mp hj)]
    cases junkBits j <;> simp
  rw [Finset.sum_congr rfl h]
  decide

theorem rowJ_accepted : ¬ ∀ g ∈ formRCertificateGates (F := F769), g.eval rowJ = 0 := by
  intro h
  have hg := h (colC 31) (by
    simp only [formRCertificateGates, booleanGates, List.mem_append, List.mem_map,
      List.mem_range]
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨31, by norm_num, ?_⟩))))
    rw [if_pos (by rw [formRN_769]; norm_num)])
  simp only [colC, bcur, CoeffExpr.eval] at hg
  rw [rowJ, rowEnv_c _ _ _ _ _ _ 31 (by norm_num)] at hg
  simp [junkBits, bit01] at hg

theorem rowJ_u1 : (topPinU1 (F := F769)).eval rowJ = 0 := by
  have h0 : matchedTop F769 0 = 0 := by
    refine matchedTop_eq_zero_of_ne 0 fun h => ?_
    have := h 0 (by decide)
    rw [nMinus1Bit_769] at this
    exact absurd this (by decide)
  have := u1_of_matched (2 : F769) junkBits 0 (fun _ => 0)
  rwa [h0] at this

theorem junk_alias_at_769 :
    (¬ ∀ g ∈ formRCertificateGates (F := F769), g.eval rowJ = 0) ∧
      (topPinU1 (F := F769)).eval rowJ = 0 ∧
      (∀ j, j < formRN F769 - 1 → junkBits j = false) ∧ rowJ.trace 136 = 2 := by
  refine ⟨rowJ_accepted, rowJ_u1, fun j hj => ?_, rowEnv_leaf _ _ _ _ _ _⟩
  rw [formRN_769] at hj
  simp [junkBits]; omega

end Junk

end Nock.RedTeam.Batch784

#print axioms Nock.RedTeam.Batch784.alias800_at_769
#print axioms Nock.RedTeam.Batch784.goldilocks_alias
#print axioms Nock.RedTeam.Batch784.junk_alias_at_769
