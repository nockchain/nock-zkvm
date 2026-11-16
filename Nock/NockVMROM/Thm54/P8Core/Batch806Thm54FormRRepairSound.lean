/-
  Nock/NockVMROM/Thm54/P8Core/Batch806Thm54FormRRepairSound.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch806Thm54FormRRepairSound`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch806Thm54FormRRepairSound.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch782Thm54U1Sound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Nock.RedTeam.Batch806

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.CoordinateCompiler

section Generic

variable {F : Type*} [Field F]

/-- **`shift_le_formRN_pred` at the production `topPin`.** -/
theorem shift_le_formRN_pred (env : Env F)
    (hb : ∀ k, k < 6 → (bbool (colM (F := F) k)).eval env = 0)
    (hp : (pPin (F := F)).eval env = 0)
    (ht : (topPin (F := F)).eval env = 0)
    (hr : (rangeGate (F := F)).eval env = 0) :
    Nock.RedTeam.Batch782.rowShift env ≤ formRN F - 1 :=
  Nock.RedTeam.Batch782.shift_le_formRN_pred env hb hp ht hr

/-- A zero `lin` factor kills every later eq-chain prefix. -/
theorem certEqRun_zero_of_lin (a i' : ℕ) (h : certLin (F := F) a i' = 0) :
    ∀ n, i' < n → certEqRun (F := F) a n = 0 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      rw [certEqRun]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h' | h'
      · rw [ih h', zero_mul]
      · subst h'; rw [h, mul_zero]

/-- **C1 soundness at the witness level.**  If `p ≤ a` for a shift-`(n−1)` certificate, every
comparison term vanishes: at a position where `p` has `1`, either `a` has `1` (the term is `0`)
or `a` has `0` there, and then the most significant bit where `a > p` differs lies strictly
above it (and below `n − 1`), so the eq-chain is already `0`. -/
theorem certLt_zero_of_ge (a : ℕ) (hchar : ringChar F ≠ 0)
    (hm : certShift a = formRN F - 1) (ha0 : 0 < a) (hge : ringChar F ≤ a) :
    certLt (F := F) a 63 = 0 := by
  rw [certLt_eq_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hsz : certShift a + 1 = Nat.size a := certShift_of_pos a ha0
  have haN : a < 2 ^ formRN F := by
    have := Nat.lt_size_self a
    rw [← hsz, hm] at this
    have hn1 : 1 ≤ formRN F :=
      Nat.one_le_of_lt (Nat.size_pos.mpr (Nat.pos_of_ne_zero hchar))
    rwa [Nat.sub_add_cancel hn1] at this
  by_cases hc : (decide (i + 1 < formRN F) && pBit F (formRN F - 2 - i)) = true
  · have hin : i + 1 < formRN F := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.1
    have hpb : (ringChar F).testBit (formRN F - 2 - i) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.2
    have hcb : certCBit a i = a.testBit (formRN F - 2 - i) := by
      unfold certCBit
      rw [if_pos (by omega), show certShift a - 1 - i = formRN F - 2 - i by omega]
    rw [if_pos hc, hcb]
    cases hci : a.testBit (formRN F - 2 - i)
    · -- `a` has `0` where `p` has `1`: so `p < a` strictly, find the top differing bit.
      have hne : ringChar F ≠ a := by
        intro h; rw [h, hci] at hpb; exact Bool.noConfusion hpb
      have hlt : ringChar F < a := lt_of_le_of_ne hge hne
      obtain ⟨j, hpj, haj, habove⟩ := exists_msb_diff_of_lt hlt
      have hjq : formRN F - 2 - i < j := by
        rcases Nat.lt_or_ge (formRN F - 2 - i) j with h | h
        · exact h
        · exfalso
          rcases Nat.lt_or_eq_of_le h with h' | h'
          · have := habove _ h'
            rw [hpb, hci] at this; exact Bool.noConfusion this
          · rw [h', hci] at haj; exact Bool.noConfusion haj
      have hjn : j < formRN F - 1 := by
        rcases Nat.lt_or_ge j (formRN F - 1) with h | h
        · exact h
        · exfalso
          rcases Nat.lt_or_eq_of_le h with h' | h'
          · have hz : a.testBit j = false :=
              Nat.testBit_lt_two_pow (lt_of_lt_of_le haN (Nat.pow_le_pow_right (by decide)
                (by omega)))
            rw [hz] at haj; exact Bool.noConfusion haj
          · have htop : (ringChar F).testBit (formRN F - 1) = true :=
              testBit_pred_size (n := ringChar F) hchar
            rw [← h', htop] at hpj; exact Bool.noConfusion hpj
      have hlin : certLin (F := F) a (formRN F - 2 - j) = 0 := by
        have hpos : formRN F - 2 - (formRN F - 2 - j) = j := by omega
        have hcj : certCBit a (formRN F - 2 - j) = true := by
          unfold certCBit
          rw [if_pos (by omega), show certShift a - 1 - (formRN F - 2 - j) = j by omega]
          exact haj
        unfold certLin
        rw [hpos, hcj]
        simp [pBit, hpj, bit01]
      rw [certEqRun_zero_of_lin (F := F) a (formRN F - 2 - j) hlin i (by omega), zero_mul]
    · simp [bit01]
  · rw [if_neg hc, mul_zero]

/-- **The repaired comparison is sound:** `certLt a 63 = 1` forces `a < p`. -/
theorem certLt_one_imp_lt (a : ℕ) (hchar : ringChar F ≠ 0)
    (hm : certShift a = formRN F - 1) (ha0 : 0 < a) (hlt : certLt (F := F) a 63 = 1) :
    a < ringChar F := by
  by_contra hge
  rw [certLt_zero_of_ge (F := F) a hchar hm ha0 (Nat.le_of_not_lt hge)] at hlt
  exact zero_ne_one hlt

/-- On a `top = 1` row carrying the bits of `a` and the eq-chain, the comparison gate evaluates to
`certLt a 63 − 1`. -/
theorem comparisonGate_eval_eq (env : Env F) (a : ℕ)
    (hTop : env.trace (col0 + 72) = 1)
    (hC : ∀ j, j < 63 → env.trace (col0 + j) = bit01 (certCBit a j))
    (hE : ∀ k, k < 21 → env.trace (col0 + 73 + k) = certEqRun a (3 * (k + 1))) :
    (comparisonGate (F := F)).eval env = certLt (F := F) a 63 - 1 := by
  simp only [comparisonGate, CoeffExpr.eval, colTop, bcur, hTop]
  congr 1
  let f : ℕ → F := fun i =>
    certEqRun a i * (if (decide (i + 1 < formRN F) && pBit F (formRN F - 2 - i)) = true
      then (1 : F) - bit01 (certCBit a i) else 0)
  have hlist : ∀ n, n ≤ 63 →
      (sumExpr ((List.range n).map fun k =>
          CoeffExpr.mul (bitCoeff (decide (k + 1 < formRN F) && pBit F (formRN F - 2 - k)))
            (termAt (F := F) k))).eval env =
        ∑ i ∈ Finset.range n, f i := by
    intro n hn
    induction n with
    | zero => simp [sumExpr, CoeffExpr.eval]
    | succ n ih =>
        rw [List.range_succ, List.map_append, List.map_singleton, sumExpr_append,
          ih (Nat.le_of_succ_le hn), Finset.sum_range_succ]
        have ht := termAt_eval_of_certRun env a n hTop hC hE (by omega)
        have hb : (bitCoeff (decide (n + 1 < formRN F) && pBit F (formRN F - 2 - n))).eval env =
            if (decide (n + 1 < formRN F) && pBit F (formRN F - 2 - n)) = true
            then (1 : F) else 0 := by
          cases (decide (n + 1 < formRN F) && pBit F (formRN F - 2 - n)) <;>
            simp [bitCoeff, CoeffExpr.eval]
        simp only [sumExpr, CoeffExpr.eval, add_zero]
        rw [hb, ht]
        cases hp : (decide (n + 1 < formRN F) && pBit F (formRN F - 2 - n))
        · simp only [f, hp]
          rw [if_neg (by decide : ¬ false = true), if_neg (by decide : ¬ false = true)]
          simp [zero_mul, mul_zero]
        · simp only [f, hp]
          rw [if_pos trivial, if_pos trivial]
          simp [one_mul]
  rw [comparisonTerms, certLt_eq_sum]
  exact hlist 63 le_rfl

/-- With `top = 1` and the certificate bits of `a`, the 21 helper pins force the eq-chain. -/
theorem helpers_eq_certEqRun (env : Env F) (a : ℕ)
    (hTop : env.trace (col0 + 72) = 1)
    (hC : ∀ j, j < 63 → env.trace (col0 + j) = bit01 (certCBit a j))
    (hH : ∀ k, k < 21 → (helperPinAt (F := F) k).eval env = 0) :
    ∀ k, k < 21 → env.trace (col0 + 73 + k) = certEqRun a (3 * (k + 1)) := by
  intro k
  induction k with
  | zero =>
      intro hk
      have h := hH 0 hk
      simp only [helperPinAt, helperAt, ↓reduceIte, CoeffExpr.eval, colE, colTop, bcur] at h
      rw [linCol_eval_cert env a _ (hC _ (by omega)), linCol_eval_cert env a _ (hC _ (by omega)),
        linCol_eval_cert env a _ (hC _ (by omega)), hTop] at h
      rw [show 3 * (0 + 1) = 0 + 3 by omega, certEqRun_add3]
      simp only [certEqRun, one_mul]
      simpa [sub_eq_zero] using h
  | succ k ih =>
      intro hk
      have h := hH (k + 1) hk
      have hprev := ih (by omega)
      simp only [helperPinAt, helperAt, Nat.add_one_ne_zero, ↓reduceIte, CoeffExpr.eval, colE,
        bcur, Nat.add_sub_cancel] at h
      rw [linCol_eval_cert env a _ (hC _ (by omega)), linCol_eval_cert env a _ (hC _ (by omega)),
        linCol_eval_cert env a _ (hC _ (by omega)), hprev] at h
      rw [show 3 * (k + 1 + 1) = 3 * (k + 1) + 3 by omega, certEqRun_add3]
      have e1 : 3 * (k + 1) + 1 = 3 * (k + 1) + 1 := rfl
      simpa [sub_eq_zero] using h

/-- The six shift columns carry the bits of `m < 64`: the 6-bit shift `rowShift` is `m`. -/
theorem rowShift_eq (env : Env F) (m : ℕ) (hm : m < 64)
    (hM : ∀ k, k < 6 → env.trace (col0 + 63 + k) = bit01 (m.testBit k)) :
    Nock.RedTeam.Batch782.rowShift env = m := by
  have hb : ∀ k, k < 6 → (bbool (colM (F := F) k)).eval env = 0 := fun k hk => by
    simp only [bbool, colM, bcur, CoeffExpr.eval]; rw [hM k hk]; exact bit01_mul_sub _
  obtain ⟨hr64, hR⟩ := Nock.RedTeam.Batch782.shift_cols_of_boolean env hb
  refine eq_of_low6_testBit hr64 hm fun k hk => ?_
  have h := (hR k hk).symm.trans (hM k hk)
  cases h1 : (Nock.RedTeam.Batch782.rowShift env).testBit k <;>
    cases h2 : m.testBit k <;> simp_all [bit01]

end Generic

section Decoded

variable {K : Type} [Field K] {N : ℕ}

/-- **`decodedShift_in_range_of_U1`, at the production `DecodedLambdaEvent.decodedShift` and the
production `topPin`.**  On compute rows satisfying the deployed shift-bit booleanity, `pPin`,
`topPin` and `rangeGate`, every decoded shift (row slots and the C-a constant slots) is
`≤ formRN − 1`.  `2 ≤ formRN` is `hp`'s fragment. -/
theorem decodedShift_in_range_of_U1 (envsC : Fin N → Env K) (hn : 2 ≤ formRN K)
    (hb : ∀ i, ∀ k, k < 6 → (bbool (colM (F := K) k)).eval (envsC i) = 0)
    (hp : ∀ i, (pPin (F := K)).eval (envsC i) = 0)
    (ht : ∀ i, (topPin (F := K)).eval (envsC i) = 0)
    (hr : ∀ i, (rangeGate (F := K)).eval (envsC i) = 0) :
    ∀ e, DecodedLambdaEvent.decodedShift envsC e ≤ formRN K - 1 := by
  intro e
  have hrow : ∀ i, DecodedLambdaEvent.rowShift (envsC i) ≤ formRN K - 1 := fun i =>
    shift_le_formRN_pred (envsC i) (hb i) (hp i) (ht i) (hr i)
  unfold DecodedLambdaEvent.decodedShift
  split
  · rename_i i j _
    unfold DecodedLambdaEvent.slotCert
    split
    · simp only; omega
    · split_ifs
      · exact hrow i
      · simp only; omega
    · split_ifs
      · exact hrow i
      · simp only; omega
  · omega

end Decoded

end Nock.RedTeam.Batch806
