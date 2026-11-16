/-
  Nock/RedTeam/Batch575Thm54FormRMtree.lean

  **Form R accumulators on `MTree K`, parametric `n`.**

  Polynomial convention: `(K[Y])[X]` (`Polynomial (Polynomial K)`).
  * Outer `X` is the timestamp base.
  * Inner `Y` is the accounting base `λ`.
  Why not `MvPolynomial (Fin 2) K`: S1 is `counts = Σ_e X^e · B_e(Y)`; `coeff` extracts
  `B_e`, and `B_e` is `Batch554.bracket` at scale `n−1`.

  Recurrences (form R; form R wins over form (b) at `λ^{n−1}`):
  * halt: `counts = 0`, `pw = 0`.
  * decompose: `counts_P = counts_L + counts_R + (Y−1)(pw_L + pw_R) + pw_R`,
    `pw_P = Y(pw_L + pw_R)`.
  * verify: `+ Y^{n−1}·X^e` on both.
  * read: `counts − T_e·C'_e·X^e`, `pw − Y^{n−1}·T_e·X^e`.

  Uniqueness `readCount e ≤ 1 ∧ verifyCount e ≤ 1` is a legitimate premise.

  **S2 as briefed is a design finding, not a theorem.**  The tree
  `.verify e a (.read e.halt)` with the axis-1 certificate (`m=0`, padding `0`)
  has `counts = 0` and `pw = 0`, unique exponents, `a_e = RelaxisNat = 1`,
  and `vpaths = rpaths = [[]]`, but `¬ Nested e t` and `¬ ReadVerifyNested t`.
  Form R cannot see a verify wrapper sitting on top of a same-exponent read:
  both wrappers have the empty decompose-path, so the algebra is the accepted
  `m = 0` same-node case (`Batch554.same_node_forces_axis_one`).  Compiled as
  `s2_nested_fails`.  The theorem that *does* hold is `formR_counts_zero_iff`:
  `counts = 0` iff every paired `e` has padding and `v = r ++ bitsOf` (no
  `Nested` conjunct).  `pw_root = 0` is not load-bearing (`pw_not_load_bearing`).
-/
import Nock.AxisBatching
import Nock.AxisBridge
import Nock.RedTeam.Batch554Thm54PwFunctional
import Nock.RedTeam.Batch555Thm54PwCertificate
import Nock.RedTeam.Batch556Thm54PwEvent
import Nock.RedTeam.Batch557Thm54RangeGadget
import Nock.NockVMROM.Thm54.FormRCore.Mtree

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch575

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.RedTeam.Batch554
  (vpaths rpaths addrP addrPFrom addrP_append addrP_nil addrP_ne_zero addrP_coeff_length
    bitsOf bitsOf_length Cpoly bracket bracket_zero_iff bracket_zero_prefix
    cross_root_both_nonzero bit sameTsTree honestTree honestTree_paths place)
open Nock.RedTeam.Batch555 (cert cert_zero)
open Polynomial

variable {K : Type*} [Field K]

/-! ## What stays here is S2's failure receipts and the Bridge note. -/

/-- **S2 as briefed FAILS.**  Verify stacked on a same-exponent read, axis-1 certificate. -/
def s2FailTree (e : ℕ) (a : K) : MTree K :=
  .verify e a (.read e .halt)

def axis1 (_e : ℕ) : ℕ := 0
def axis1bits (_e _j : ℕ) : Bool := false

theorem s2Fail_unique (e : ℕ) (a : K) : UniqueExponents (s2FailTree e a) := by
  intro e'
  constructor <;> simp [s2FailTree, readCount, verifyCount] <;> split_ifs <;> simp

theorem s2Fail_paired (e : ℕ) (a : K) : Paired e (s2FailTree e a) := by
  simp [Paired, s2FailTree, readCount, verifyCount]

theorem s2Fail_paths (e : ℕ) (a : K) :
    rpaths e (s2FailTree e a) = [[]] ∧ vpaths e (s2FailTree e a) = [[]] := by
  simp [s2FailTree, rpaths, vpaths]

theorem s2Fail_counts (n e : ℕ) (a : K) :
    formRCounts n axis1 axis1bits (s2FailTree e a) = 0 := by
  have hC : Cpoly (K := K) (n - 1) (axis1bits e) = (X : Polynomial K) ^ (n - 1) := by
    change Cpoly (n - 1) (fun _ => false) = _
    exact Cpoly_false (n - 1)
  simp only [s2FailTree, formRCounts, formRPw, axis1, C'poly, Tpoly, scale, Y]
  rw [hC, pow_zero, one_mul]
  ring

theorem s2Fail_pw (n e : ℕ) (a : K) :
    formRPw n axis1 (s2FailTree e a) = 0 := by
  simp only [s2FailTree, formRPw, axis1, Tpoly, scale, Y, pow_zero, mul_one]
  ring

theorem s2Fail_not_nested (e : ℕ) (a : K) :
    ¬ Nested e (s2FailTree e a) ∧ ¬ AxisBridge.ReadVerifyNested (s2FailTree e a) := by
  constructor
  · intro h
    simp [s2FailTree, Nested, readCount] at h
  · intro h
    simp [s2FailTree, AxisBridge.ReadVerifyNested, verifyCount] at h

theorem s2Fail_relaxis (e : ℕ) (a : K) :
    Relaxis e (s2FailTree e a) = (1 : K) ∧ cert (axis1 e) (axis1bits e) = 1 := by
  constructor
  · simp [s2FailTree, Relaxis, vaddr, vdep]
  · exact cert_zero _

/-- The briefed S2 (`counts = 0 → Nested`) is false at `s2FailTree`. -/
theorem s2_nested_fails (n e : ℕ) (a : K) :
    formRCounts n axis1 axis1bits (s2FailTree e a) = 0
    ∧ UniqueExponents (s2FailTree e a)
    ∧ Paired e (s2FailTree e a)
    ∧ Relaxis e (s2FailTree e a) = (cert (axis1 e) (axis1bits e) : K)
    ∧ ¬ Nested e (s2FailTree e a) :=
  ⟨s2Fail_counts n e a, s2Fail_unique e a, s2Fail_paired e a,
    by
      have ⟨hR, hC⟩ := s2Fail_relaxis e a
      rw [hR, hC, Nat.cast_one],
    (s2Fail_not_nested e a).1⟩

/-- Optional `pw_root = 0` holds on the same failing tree, so it does not restore Nested. -/
theorem s2_nested_fails_with_pw (n e : ℕ) (a : K) :
    formRCounts n axis1 axis1bits (s2FailTree e a) = 0
    ∧ formRPw n axis1 (s2FailTree e a) = 0
    ∧ ¬ Nested e (s2FailTree e a) :=
  ⟨s2Fail_counts n e a, s2Fail_pw n e a, (s2Fail_not_nested e a).1⟩

/-- `pw = 0` is not sufficient for `counts = 0`.  Distinct exponents, swapped certificates:
`pw ≡ 0` and the `e₁` coefficient is `Y^{n−1} ≠ 0`. -/
def sameTs_m (_ : ℕ) : ℕ := 1
def sameTs_c (e₁ : ℕ) : ℕ → ℕ → Bool := fun e _ => decide (e ≠ e₁)

theorem pw_not_load_bearing (n e₁ e₂ : ℕ) (hne : e₁ ≠ e₂) (hn : 2 ≤ n) :
    formRPw n sameTs_m (sameTsTree (K := K) e₁ e₂) = 0
    ∧ (formRCounts n sameTs_m (sameTs_c e₁) (sameTsTree (K := K) e₁ e₂)).coeff e₁ ≠ 0 := by
  have hv : vpaths e₁ (sameTsTree (K := K) e₁ e₂) = [[true]] := by
    simp [sameTsTree, vpaths, hne, Ne.symm hne]
  have hr : rpaths e₁ (sameTsTree (K := K) e₁ e₂) = [[]] := by
    simp [sameTsTree, rpaths, hne, Ne.symm hne]
  constructor
  · simp only [sameTsTree, formRPw, sameTs_m, Tpoly, scale, Y]
    simp [C_mul]
    ring
  · have hbr :
        (formRCounts n sameTs_m (sameTs_c e₁) (sameTsTree (K := K) e₁ e₂)).coeff e₁
          = bracket (K := K) (n - 1) 1 (sameTs_c e₁ e₁) [true] [] := by
      simpa [sameTs_m] using
        paired_bracket (K := K) n sameTs_m (sameTs_c e₁) e₁
          (sameTsTree (K := K) e₁ e₂) [true] [] hv hr
    rw [hbr]
    have htrue : addrP (K := K) [true] = X + 1 := by simp [addrP, addrPFrom, bit]
    have hC : Cpoly (K := K) (n - 1) (sameTs_c e₁ e₁) = (X : Polynomial K) ^ (n - 1) := by
      have hfun : sameTs_c e₁ e₁ = fun _ => false := by
        funext j; simp [sameTs_c]
      rw [hfun]
      exact Cpoly_false (n - 1)
    have heq : bracket (K := K) (n - 1) 1 (sameTs_c e₁ e₁) [true] []
        = (X : Polynomial K) ^ (n - 1) := by
      unfold bracket
      rw [htrue, hC, addrP_nil]
      ring
    rw [heq]
    exact pow_ne_zero _ X_ne_zero

/-! ## S3 — moved verbatim to `Nock/NockVMROM/Thm54/FormRCore/Mtree.lean`, same names:
`decompCount`, `nodeCount`, the degree lemmas, `degY_le`, `formR_event_card`,
`formR_support_le_envelope`, `formR_work_vs_majorant`. -/

/-! ## Bridge (statement only; no proof)

      indP t lmb T        -- Form R `pw`, evaluated at a field `λ = lmb`
      countsP t lmb T C'  -- Form R `counts`, same

  with the same recurrences as `formRPw` / `formRCounts` after
  `Polynomial.map (evalRingHom lmb)`, under `T e = lmb ^ (m e)`,
  `C' e = (C'poly n (c e)).eval lmb`, and
  `pwScale lmb = lmb ^ MemoryTable.pwScaleExp`.

  The recurrence *shape* matches form R
  (`decompose` / `read` / `verify` / `halt`).  Do not reconcile here.

      (formRCounts n mm cc t).map (evalRingHom lmb)
        = AxisBatching.countsP t lmb
            (fun e => lmb ^ mm e)
            (fun e => (C'poly n (cc e)).eval lmb)

  after generalising `pwScaleExp` to `n-1`.
-/


end Nock.RedTeam.Batch575

#print axioms Nock.RedTeam.Batch575.formR_counts_zero_iff
#print axioms Nock.RedTeam.Batch575.s2_nested_fails
#print axioms Nock.RedTeam.Batch575.paired_bracket
#print axioms Nock.RedTeam.Batch575.formR_coeff_cases
