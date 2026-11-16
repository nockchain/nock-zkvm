/-
  Nock/RedTeam/Batch546Thm54LambdaModel.lean

  **Design D-λ (a SAMPLED doubling base `λ` with certified axis bits) on the
  `MTree` model, and the polynomial identity that breaks it.**

  The claimed soundness: per record the root `counts` coefficient is
  `ts·(a_λ − P_{R,V}(λ))·λ^{−d}` and `P_{R,V} = a_λ` AS POLYNOMIALS iff the verify is under the
  read at axis `a`.

  This file compiles the model (`countsL`, the indicator `indP` is unchanged) and REFUTES the
  claim:

  * `read_right_invisible` — the MECHANISM.  A `read_root` wrapper at a RIGHT-child position
    contributes NOTHING to `axis_counts` above it: the decompose rule's `− ind_R` term returns
    exactly the `− ts` the read subtracted (`countsL` of the tree equals `countsL` of the tree
    with the wrapper deleted).  Only its `− ts` in the indicator survives, and the indicator is
    sign-blind.
  * `t1_boundaries` / `t2_boundaries` — concrete forgeries accepted for EVERY `λ ≠ 0`:
    read at the right child of `A`, verify at address `2^{bitlen a} + a` of `A`'s left child,
    certified axis `a ∈ {1, 2}`.  Both boundary polynomials are IDENTICALLY zero in `λ` and `ts`,
    so no Schwartz–Zippel event exists (the acceptance set is all of `K∖{0}`).
  * `read_right_forgery` + `vaddrL_subset_sum` — the FAMILY: for any left subtree holding the
    verify, the root `X^e`-coefficient is `(a_λ − vaddrL)·λ^{−d}` where `vaddrL` is a 0/1
    subset-sum polynomial in `λ` — i.e. a VALID certificate of the integer with those bits — so
    the prover sets the bits to that subset and the coefficient vanishes for every `λ`.
  * `tfull_boundaries` — the two-record tree over the REAL subject `S = cons(cons(u,v), w)`: an
    honest first lookup `(S, w, 3, ts₁)` stacked at the root, and the forged `(w, v, 1, ts₂)`
    served by a read at `w` (S's tail) and a verify at `v` (the head's tail).  Both boundaries are
    identically zero; `slot 1 w = w ≠ v` (`tfull_lookup_false`).
-/
import Nock.AxisBatching
import Nock.AxisBridge
import Nock.Reference

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch546

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Polynomial

variable {K : Type*} [Field K]

/-! ## The D-λ model -/

/-- D-λ `axis_counts` as a polynomial in the timestamp base:
`decompose` divides by the COIN `λ`, `read_root` subtracts `ts`, `verify_child` adds `a_λ·ts` (the record's
`𝕂`-valued certified axis), `halt` is `0`.  The indicator rule is the paper's `indP`. -/
noncomputable def countsL (l : K) : MTree K → K[X]
  | .halt => 0
  | .decompose L R => C l⁻¹ * (countsL l L + countsL l R - indP_bin R)
  | .read e c => countsL l c - X ^ e
  | .verify e a c => countsL l c + C a * X ^ e

/-- At `λ = 2` the model is the paper's `countsP`. -/
theorem countsL_two (t : MTree K) : countsL 2 t = countsP_bin t := by
  induction t with
  | halt => rfl
  | decompose L R ihl ihr => simp [countsL, countsP_bin, ihl, ihr]
  | read e c ih => simp [countsL, countsP_bin, ih]
  | verify e a c ih => simp [countsL, countsP_bin, ih]

theorem constr_countsL_decompose (l : K) (hl : l ≠ 0) (L R : MTree K) :
    C l * countsL l (.decompose L R) = countsL l L + countsL l R - indP_bin R := by
  simp only [countsL]
  rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hl, C_1, one_mul]

noncomputable def axisL (l : K) (n a : ℕ) : K :=
  ∑ i ∈ Finset.range n, ((Nat.testBit a i).toNat : K) * l ^ i

theorem axisL_one (l : K) (n : ℕ) (hn : 1 ≤ n) : axisL l n 1 = 1 := by
  unfold axisL
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    have : Nat.testBit 1 i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by norm_num)
        (Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hi)))
    simp [this]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

theorem axisL_two (l : K) (n : ℕ) (hn : 2 ≤ n) : axisL l n 2 = l := by
  unfold axisL
  have h21 : Nat.testBit 2 1 = true := by decide
  rw [Finset.sum_eq_single 1]
  · simp [h21]
  · intro i _ hi
    rcases Nat.lt_or_ge i 2 with h | h
    · interval_cases i
      · simp
      · exact absurd rfl hi
    · have : Nat.testBit 2 i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by norm_num)
          (Nat.pow_le_pow_right (by norm_num) h))
      simp [this]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

theorem axisL_three (l : K) (n : ℕ) (hn : 2 ≤ n) : axisL l n 3 = l + 1 := by
  unfold axisL
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have h30 : Nat.testBit 3 0 = true := by decide
  have h31 : Nat.testBit 3 1 = true := by decide
  have hhi : ∀ i, Nat.testBit 3 (i + 1 + 1) = false := fun i =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ i + 1 + 1)))
  simp [h30, h31, hhi]

/-! ## The mechanism: a right-child `read_root` is invisible to `axis_counts` -/

/-- **A `read_root` at a RIGHT-child position contributes nothing to `axis_counts` above it.**
The read subtracts `ts` from both accumulators; the parent's decompose rule adds `− ind_R`, and
`ind_R` carries that same `− ts`, so `axis_counts` of the parent is what it would be with the
wrapper DELETED.  This holds for every `λ` — the coin never sees the read. -/
theorem read_right_invisible (l : K) (L c : MTree K) (e : ℕ) :
    countsL l (.decompose L (.read e c)) = countsL l (.decompose L c) := by
  simp only [countsL, indP_bin]; ring

/-- Its indicator, by contrast, keeps the `− ts` (which a verify anywhere can cancel). -/
theorem read_right_indicator (L c : MTree K) (e : ℕ) :
    indP_bin (.decompose L (.read e c)) = indP_bin (.decompose L c) - X ^ e := by
  simp only [indP_bin]; ring

/-- Contrast: at a LEFT-child position the read IS visible (`− λ⁻¹·ts`), which is why the
brief's own crossing is caught by the coin. -/
theorem read_left_visible (l : K) (c R : MTree K) (e : ℕ) :
    countsL l (.decompose (.read e c) R) = countsL l (.decompose c R) - C l⁻¹ * X ^ e := by
  simp only [countsL]; ring

/-- The invisibility persists up a LEFT spine: the read at address `2^k + 1` relative to any
ancestor reached by left steps only. -/
theorem read_right_spine (l : K) (X' c Y : MTree K) (e : ℕ) :
    countsL l (.decompose (.decompose X' (.read e c)) Y)
      = countsL l (.decompose (.decompose X' c) Y) := by
  show C l⁻¹ * (countsL l (.decompose X' (.read e c)) + countsL l Y - indP_bin Y)
      = C l⁻¹ * (countsL l (.decompose X' c) + countsL l Y - indP_bin Y)
  rw [read_right_invisible]

/-! ## Concrete forgeries accepted for every `λ` -/

/-- Witness 1: certified axis `a = 1` (`a_λ = 1`).  Read at the right child of the root,
verify at the LEFT child's right child (address `3 = 2^1 + 1` of the left child). -/
def t1 (e : ℕ) (a : K) : MTree K :=
  .decompose (.decompose .halt (.verify e a .halt)) (.read e .halt)

theorem t1_boundaries (l : K) (e : ℕ) :
    indP_bin (t1 e (axisL l 64 1)) = 0 ∧ countsL l (t1 e (axisL l 64 1)) = 0 := by
  rw [axisL_one l 64 (by norm_num)]
  constructor
  · simp only [t1, indP_bin]; ring
  · simp only [t1, countsL, indP_bin, C_1]; ring

theorem t1_used_once (e : ℕ) (a : K) :
    readCount e (t1 e a) = 1 ∧ verifyCount e (t1 e a) = 1 := by
  constructor <;> simp [t1, readCount, verifyCount]

theorem t1_committed_axis (e : ℕ) (a : K) : vaxis e (t1 e a) = a := by
  simp [t1, vaxis, verifyCount]

/-- The verify is NOT below the read: the read's subtree is a bare `halt`. -/
theorem t1_not_nested (e : ℕ) (a : K) :
    ¬ AxisBridge.ReadVerifyNested (t1 e a) ∧ ¬ Nested e (t1 e a) := by
  constructor
  · intro h
    simp [t1, AxisBridge.ReadVerifyNested, verifyCount] at h
  · intro h
    simp [t1, Nested, readCount, verifyCount] at h

/-- Witness 2: certified axis `a = 2` (`a_λ = λ`).  Read at the right child of the root; verify
at address `6 = 2^2 + 2` of the left child (left child of the right child). -/
def t2 (e : ℕ) (a : K) : MTree K :=
  .decompose (.decompose .halt (.decompose (.verify e a .halt) .halt)) (.read e .halt)

theorem t2_boundaries (l : K) (hl : l ≠ 0) (e : ℕ) :
    indP_bin (t2 e (axisL l 64 2)) = 0 ∧ countsL l (t2 e (axisL l 64 2)) = 0 := by
  rw [axisL_two l 64 (by norm_num)]
  have h : C l⁻¹ * C l = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hl, C_1]
  constructor
  · simp only [t2, indP_bin]; ring
  · simp only [t2, countsL, indP_bin]
    linear_combination (C l⁻¹ * C l⁻¹ * X ^ e) * h

theorem t2_not_nested (e : ℕ) (a : K) :
    ¬ AxisBridge.ReadVerifyNested (t2 e a) := by
  intro h
  simp [t2, AxisBridge.ReadVerifyNested, verifyCount] at h

/-! ## The family: read at the right child, verify anywhere on the left, bits := the path -/

/-- The λ-address accumulated from the current subtree's root down to the `verify_child` with
timestamp `e`: `AxisBatching.vaddr` with the doubling base `2` replaced by `λ`
(`⟶left` scales, `⟶right` scales and adds `λ^{depth}`). -/
noncomputable def vaddrL (l : K) (e : ℕ) : MTree K → K
  | .halt => 0
  | .decompose L R => if verifyCount e L = 1 then vaddrL l e L else vaddrL l e R + l ^ (vdep e R)
  | .read _ c => vaddrL l e c
  | .verify e' _ c => if e' = e then 0 else vaddrL l e c

theorem countsL_coeff_absent (l : K) (e : ℕ) (t : MTree K) :
    readCount e t = 0 → verifyCount e t = 0 → (countsL l t).coeff e = 0 := by
  induction t with
  | halt => intro _ _; simp [countsL]
  | decompose L R ihl ihr =>
      intro hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      simp only [countsL, coeff_C_mul, coeff_add, coeff_sub, indP_coeff]
      rw [ihl (by omega) (by omega), ihr (by omega) (by omega)]
      have h1 : verifyCount e R = 0 := by omega
      have h2 : readCount e R = 0 := by omega
      rw [h1, h2]; simp
  | read e' c ih =>
      intro hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      have he : e' ≠ e := by rintro rfl; simp at hr
      simp only [countsL, coeff_sub, coeff_X_pow, if_neg (fun h : e = e' => he h.symm)]
      rw [ih (by omega) hv]; ring
  | verify e' a c ih =>
      intro hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      have he : e' ≠ e := by rintro rfl; simp at hv
      simp only [countsL, coeff_add, coeff_C_mul, coeff_X_pow, if_neg (fun h : e = e' => he h.symm)]
      rw [ih hr (by omega)]; ring

/-- The pending-region closed form at base `λ` (`AxisBatching.ccoef_pending` with `2 ↦ λ`):
below a record's `read_root`, the `X^e`-coefficient of `counts` is
`(a_λ − vaddrL)·λ^{−depth}`. -/
theorem countsL_coeff_pending (l : K) (hl : l ≠ 0) (e : ℕ) (t : MTree K) :
    readCount e t = 0 → verifyCount e t = 1 →
      (countsL l t).coeff e = (vaxis e t - vaddrL l e t) * l⁻¹ ^ (vdep e t) := by
  induction t with
  | halt => intro _ hv; simp [verifyCount] at hv
  | decompose L R ihl ihr =>
      intro hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      have hrl : readCount e L = 0 := by omega
      have hrr : readCount e R = 0 := by omega
      simp only [countsL, coeff_C_mul, coeff_add, coeff_sub, indP_coeff]
      by_cases hvl : verifyCount e L = 1
      · have hvr : verifyCount e R = 0 := by omega
        rw [ihl hrl hvl, countsL_coeff_absent l e R hrr hvr, hvr, hrr]
        simp only [vaxis, vaddrL, vdep, if_pos hvl]
        rw [pow_succ]; push_cast; ring
      · have hvr : verifyCount e R = 1 := by omega
        rw [countsL_coeff_absent l e L hrl (by omega), ihr hrr hvr, hvr, hrr]
        simp only [vaxis, vaddrL, vdep, if_neg hvl]
        rw [pow_succ]
        have hpow : l ^ (vdep e R) * l⁻¹ ^ (vdep e R) = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ hl, one_pow]
        push_cast
        linear_combination (l⁻¹) * hpow
  | read e' c ih =>
      intro hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      have he : e' ≠ e := by rintro rfl; simp at hr
      simp only [countsL, coeff_sub, coeff_X_pow, if_neg (fun h : e = e' => he h.symm)]
      rw [ih (by omega) hv]
      simp only [vaxis, vaddrL, vdep, sub_zero]
  | verify e' a c ih =>
      intro hr hv
      simp only [readCount] at hr; simp only [verifyCount] at hv
      by_cases he : e' = e
      · have hvc : verifyCount e c = 0 := by rw [if_pos he] at hv; omega
        simp only [countsL, coeff_add, coeff_C_mul, coeff_X_pow, if_pos (he.symm : e = e')]
        rw [countsL_coeff_absent l e c hr hvc]
        simp only [vaxis, vaddrL, vdep, if_pos he]; simp
      · simp only [countsL, coeff_add, coeff_C_mul, coeff_X_pow, if_neg (fun h : e = e' => he h.symm)]
        rw [ih hr (by simpa [he] using hv)]
        simp only [vaxis, vaddrL, vdep, if_neg he, mul_zero, add_zero]

/-- **The forgery family.**  Left subtree `L` holds the verify (and no read of `e`), `c` is free
of `e`, and the read of `e` sits at the RIGHT child: the root's `X^e`-coefficient is `0` in the
indicator and `(a_λ − vaddrL)·λ^{−depth}` in the counts. -/
theorem read_right_forgery (l : K) (hl : l ≠ 0) (e : ℕ) (L c : MTree K)
    (hrL : readCount e L = 0) (hvL : verifyCount e L = 1)
    (hrc : readCount e c = 0) (hvc : verifyCount e c = 0) :
    (indP_bin (.decompose L (.read e c))).coeff e = 0
    ∧ (countsL l (.decompose L (.read e c))).coeff e
        = (vaxis e L - vaddrL l e L) * l⁻¹ ^ (vdep e L + 1) := by
  constructor
  · rw [indP_coeff]
    simp only [verifyCount, readCount, hvL, hrL, hrc, hvc]; push_cast; ring
  · rw [read_right_invisible]
    simp only [countsL, coeff_C_mul, coeff_add, coeff_sub, indP_coeff]
    rw [countsL_coeff_pending l hl e L hrL hvL, countsL_coeff_absent l e c hrc hvc, hrc, hvc]
    rw [pow_succ]; push_cast; ring

/-- `vaddrL` is a 0/1 SUBSET-SUM polynomial in `λ` with exponents below the depth — i.e. it IS
the certificate `Σ_{i∈S} λⁱ` of the integer `Σ_{i∈S} 2ⁱ`, with boolean bits `[i ∈ S]`.  So the
prover who commits those bits has a valid certificate and a vanishing root coefficient for
EVERY `λ`. -/
theorem vaddrL_subset_sum (e : ℕ) (t : MTree K) :
    ∃ S : Finset ℕ, (∀ i ∈ S, i < vdep e t) ∧ ∀ l : K, vaddrL l e t = ∑ i ∈ S, l ^ i := by
  induction t with
  | halt => exact ⟨∅, by simp, fun l => by simp [vaddrL]⟩
  | decompose L R ihl ihr =>
      obtain ⟨SL, hSL, hL⟩ := ihl
      obtain ⟨SR, hSR, hR⟩ := ihr
      by_cases hvl : verifyCount e L = 1
      · refine ⟨SL, ?_, fun l => ?_⟩
        · intro i hi; simp only [vdep, if_pos hvl]; exact Nat.lt_succ_of_lt (hSL i hi)
        · simp only [vaddrL, if_pos hvl]; exact hL l
      · refine ⟨insert (vdep e R) SR, ?_, fun l => ?_⟩
        · intro i hi
          simp only [vdep, if_neg hvl]
          rw [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · exact Nat.lt_succ_self _
          · exact Nat.lt_succ_of_lt (hSR i hi)
        · simp only [vaddrL, if_neg hvl]
          rw [Finset.sum_insert (fun h => Nat.lt_irrefl _ (hSR _ h)), hR l]; ring
  | read e' c ih =>
      obtain ⟨S, hS, h⟩ := ih
      exact ⟨S, fun i hi => by simpa [vdep] using hS i hi, fun l => by simpa [vaddrL] using h l⟩
  | verify e' a c ih =>
      obtain ⟨S, hS, h⟩ := ih
      by_cases he : e' = e
      · exact ⟨∅, by simp, fun l => by simp [vaddrL, he]⟩
      · exact ⟨S, fun i hi => by simpa [vdep, he] using hS i hi,
          fun l => by simpa [vaddrL, he] using h l⟩

/-- The right-child read makes `ReadVerifyNested` fail whenever its own subtree holds no verify. -/
theorem read_right_not_nested (e : ℕ) (L c : MTree K) (hvc : verifyCount e c = 0) :
    ¬ AxisBridge.ReadVerifyNested (.decompose L (.read e c)) := by
  intro h
  simp only [AxisBridge.ReadVerifyNested] at h
  omega

/-! ## The two-record tree over the real subject `S = cons(cons(u,v), w)` -/

/-- Honest lookup `(S, w, 3, ts₁)` (`a_λ = λ + 1`) read at the root, verified at S's tail; forged
lookup `(w, v, 1, ts₂)` (`a_λ = 1`) read at S's tail (stacked under the honest verify), verified
at the head's tail. -/
def tfull (e₁ e₂ : ℕ) (a₁ a₂ : K) : MTree K :=
  .read e₁ (.decompose
    (.decompose .halt (.verify e₂ a₂ .halt))
    (.verify e₁ a₁ (.read e₂ .halt)))

theorem tfull_boundaries (l : K) (hl : l ≠ 0) (e₁ e₂ : ℕ) :
    indP_bin (tfull e₁ e₂ (axisL l 64 3) (axisL l 64 1)) = 0
    ∧ countsL l (tfull e₁ e₂ (axisL l 64 3) (axisL l 64 1)) = 0 := by
  rw [axisL_three l 64 (by norm_num), axisL_one l 64 (by norm_num)]
  have h : C l⁻¹ * C l = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hl, C_1]
  constructor
  · simp only [tfull, indP_bin]; ring
  · simp only [tfull, countsL, indP_bin, C_1, C_add]
    linear_combination (X ^ e₁) * h

theorem tfull_used_once (e₁ e₂ : ℕ) (a₁ a₂ : K) (hne : e₁ ≠ e₂) :
    readCount e₂ (tfull e₁ e₂ a₁ a₂) = 1 ∧ verifyCount e₂ (tfull e₁ e₂ a₁ a₂) = 1
    ∧ readCount e₁ (tfull e₁ e₂ a₁ a₂) = 1 ∧ verifyCount e₁ (tfull e₁ e₂ a₁ a₂) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [tfull, readCount, verifyCount, hne, Ne.symm hne]

/-- The honest record is well-nested, the forged one is not. -/
theorem tfull_nesting (e₁ e₂ : ℕ) (a₁ a₂ : K) (hne : e₁ ≠ e₂) :
    Nested e₁ (tfull e₁ e₂ a₁ a₂) ∧ ¬ Nested e₂ (tfull e₁ e₂ a₁ a₂)
    ∧ ¬ AxisBridge.ReadVerifyNested (tfull e₁ e₂ a₁ a₂) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [tfull, Nested, readCount, verifyCount, Ne.symm hne]
  · intro h
    simp [tfull, Nested, readCount, verifyCount, hne] at h
  · intro h
    simp [tfull, AxisBridge.ReadVerifyNested, verifyCount] at h

/-- The forged claim is `/[1 w] = v`, i.e. `w = v`; false whenever `v ≠ w`.  The read node is
`slot 3 S` (the tail), the verify node is `slot 5 S` (the head's tail); the honest record
`(S, w, 3)` is a true lookup. -/
theorem tfull_lookup_false (u v w : ℕ) (h : v ≠ w) :
    let S := Noun.cell (Noun.cell (Noun.atom u) (Noun.atom v)) (Noun.atom w)
    Noun.slot 3 S = some (Noun.atom w)
    ∧ Noun.slot 5 S = some (Noun.atom v)
    ∧ Noun.slot 1 (Noun.atom w) = some (Noun.atom w)
    ∧ (some (Noun.atom w) : Option Noun) ≠ some (Noun.atom v) := by
  intro S
  refine ⟨by simp [S, Noun.slot], by simp [S, Noun.slot], by simp [Noun.slot], ?_⟩
  intro heq
  simp at heq
  exact h heq.symm


/-- The brief's crossing — read at the LEFT child, verify at the right sibling, `a = 2` — has
`countsL = λ⁻¹·(λ − 2)·X^e`: caught for every `λ ≠ 2`. -/
def tb (e : ℕ) (a : K) : MTree K := .decompose (.read e .halt) (.verify e a .halt)

theorem brief_crossing_caught (l : K) (hl : l ≠ 0) (e : ℕ) :
    countsL l (tb e (axisL l 64 2)) = C (l⁻¹ * (l - 2)) * X ^ e
    ∧ (countsL l (tb e (axisL l 64 2)) = 0 ↔ l = 2) := by
  rw [axisL_two l 64 (by norm_num)]
  have h1 : countsL l (tb e l) = C (l⁻¹ * (l - 2)) * X ^ e := by
    simp only [tb, countsL, indP_bin, C_mul, C_sub]
    rw [show (C (2:K)) = (2:K[X]) from map_ofNat C 2]; ring
  refine ⟨h1, ?_⟩
  rw [h1]
  constructor
  · intro h0
    have hX : (X ^ e : K[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
    have hC : C (l⁻¹ * (l - 2)) = (0 : K[X]) := (mul_eq_zero.mp h0).resolve_right hX
    rw [C_eq_zero, mul_eq_zero] at hC
    rcases hC with hC | hC
    · exact absurd (inv_eq_zero.mp hC) hl
    · exact sub_eq_zero.mp hC
  · rintro rfl; simp

/-- Honest nested placements are exact for every `λ ≠ 0`: the tail lookup (`a = 3`, `a_λ = λ+1`)
and the head lookup (`a = 2`, `a_λ = λ`). -/
theorem honest_axis3_exact (l : K) (hl : l ≠ 0) (e : ℕ) :
    countsL l (.read e (.decompose .halt (.verify e (axisL l 64 3) .halt))) = 0 := by
  rw [axisL_three l 64 (by norm_num)]
  have h : C l⁻¹ * C l = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hl, C_1]
  simp only [countsL, indP_bin, C_add, C_1]
  linear_combination (X ^ e) * h

theorem honest_axis2_exact (l : K) (hl : l ≠ 0) (e : ℕ) :
    countsL l (.read e (.decompose (.verify e (axisL l 64 2) .halt) .halt)) = 0 := by
  rw [axisL_two l 64 (by norm_num)]
  have h : C l⁻¹ * C l = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hl, C_1]
  simp only [countsL, indP_bin]
  linear_combination (X ^ e) * h

end Nock.RedTeam.Batch546

#print axioms Nock.RedTeam.Batch546.read_right_invisible
#print axioms Nock.RedTeam.Batch546.t1_boundaries
#print axioms Nock.RedTeam.Batch546.t2_boundaries
#print axioms Nock.RedTeam.Batch546.read_right_forgery
#print axioms Nock.RedTeam.Batch546.vaddrL_subset_sum
#print axioms Nock.RedTeam.Batch546.tfull_boundaries
#print axioms Nock.RedTeam.Batch546.tfull_lookup_false
#print axioms Nock.RedTeam.Batch546.brief_crossing_caught
