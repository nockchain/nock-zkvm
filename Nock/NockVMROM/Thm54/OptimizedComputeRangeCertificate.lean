/-
  Nock/NockVMROM/Thm54/OptimizedComputeRangeCertificate.lean

  New columns occupy `202.. 301` so the RAP width is `202 + 100 = 302`.
  Gate count `97` base + the two `𝕂` power pins `H`, `T` at `e = 3` coordinates each
  (`OptimizedComputeCorrectedFinal.formRLamPins`), so `C.rap.s = 313 + 97 + 6 = 416`.
  `n := Nat.size p`; the
  Goldilocks instance is `n = 64`.  The range gate is kept (vacuous at
  `n = 2^b`).  Comparison is top-seeded so degree stays `≤ 4`.
  No `nockCompiles_zmod` hypothesis.
-/
import Mathlib.Data.Nat.Size
import Nock.NockVMROM.Thm54.CoordinateCompiler

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeRangeCertificate

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54.CoordinateCompiler

def bcur {F : Type*} (i : ℕ) : CoeffExpr F := .var .traceCur i
def bbool {F : Type*} [Field F] (e : CoeffExpr F) : CoeffExpr F :=
  .mul e (.sub e (.const 1))

variable {F : Type*} [Field F]

/-- Form R bit-length at the deployed Goldilocks chip. -/
def deployedN : ℕ := 64

/-- New-column origin: first unused compute RAP coordinate. -/
def col0 : ℕ := 202

/-- Certificate bits `c_1.. c_{n−1}` at `202.. 264`. -/
def colC (j : ℕ) : CoeffExpr F := bcur (col0 + j)
/-- Shift bits `m_0.. m_{b−1}` at `265.. 270`. -/
def colM (k : ℕ) : CoeffExpr F := bcur (col0 + 63 + k)
/-- Base power helpers `h`, `t`. -/
def colHbase : CoeffExpr F := bcur (col0 + 69)
def colTbase : CoeffExpr F := bcur (col0 + 70)
/-- `p` and `top` of the bit-matched `[m = n−1]` chain. -/
def colP : CoeffExpr F := bcur (col0 + 71)
def colTop : CoeffExpr F := bcur (col0 + 72)
/-- Eq-chain helpers `E_1.. E_21`. -/
def colE (k : ℕ) : CoeffExpr F := bcur (col0 + 73 + k)
/-- 𝕂 helpers `H`, `T` as three-and-three base-field limbs (`296.. 301`). -/
def colHK (k : Fin 3) : CoeffExpr F := bcur (col0 + 94 + (k : ℕ))
def colTK (k : Fin 3) : CoeffExpr F := bcur (col0 + 97 + (k : ℕ))

@[simp] theorem colC_degree (j : ℕ) : (colC (F := F) j).degree = 1 := rfl
@[simp] theorem colM_degree (k : ℕ) : (colM (F := F) k).degree = 1 := rfl
@[simp] theorem colTop_degree : (colTop (F := F)).degree = 1 := rfl
@[simp] theorem colP_degree : (colP (F := F)).degree = 1 := rfl
@[simp] theorem colHbase_degree : (colHbase (F := F)).degree = 1 := rfl
@[simp] theorem colTbase_degree : (colTbase (F := F)).degree = 1 := rfl
@[simp] theorem colE_degree (k : ℕ) : (colE (F := F) k).degree = 1 := rfl

/-- `n := Nat.size (ringChar F)`. Column layout stays the `n = 64` width;
    bit tests and the eq-chain factors read this `n`. -/
noncomputable def formRN (F : Type*) [Field F] : ℕ := Nat.size (ringChar F)

/-- Booleanity of the 63 certificate bits and 6 shift bits. -/
noncomputable def booleanGates : List (CoeffExpr F) :=
  (List.range 63).map (fun j => if formRN F - 1 < j + 1 then colC j else bbool (colC j)) ++
    (List.range 6).map (fun k => bbool (colM k))

theorem booleanGates_degree : ∀ g ∈ booleanGates (F := F), g.degree ≤ 4 := by
  intro g hg
  simp only [booleanGates, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨j, _, rfl⟩ | ⟨k, _, rfl⟩
  · split_ifs <;> simp [bbool, CoeffExpr.degree]
  · simp [bbool, CoeffExpr.degree]

/-- Bit `k` of `n − 1`. -/
noncomputable def nMinus1Bit (F : Type*) [Field F] (k : ℕ) : Bool :=
  (formRN F - 1).testBit k

/-- Low 6 bits of `n − 1`. Dummy-window shift. -/
noncomputable def nMinus1Low (F : Type*) [Field F] : ℕ := (formRN F - 1) % 64

/-- Bit-matched shift bit `lm_k`. -/
noncomputable def lm (k : ℕ) : CoeffExpr F :=
  if nMinus1Bit F k then colM k else .sub (.const 1) (colM k)

/-- Bit-matched `p` pin: `p = Π_{k=3}^{5} lm_k`.  `topPin` (U1) is the bit-matched
    `top = P·lm₂·lm₁·lm₀ = [m = n−1]`. -/
noncomputable def pPin : CoeffExpr F :=
  .sub colP (.mul (.mul (lm 5) (lm 4)) (lm 3))
noncomputable def topPin : CoeffExpr F :=
  .sub colTop (.mul (.mul (.mul colP (lm 2)) (lm 1)) (lm 0))

theorem lm_degree (k : ℕ) : (lm (F := F) k).degree = 1 := by
  unfold lm
  split_ifs <;> simp [CoeffExpr.degree, colM, bcur]

theorem pPin_degree : (pPin (F := F)).degree ≤ 4 := by
  simp [pPin, CoeffExpr.degree, lm_degree]
theorem topPin_degree : (topPin (F := F)).degree ≤ 4 := by
  simp [topPin, CoeffExpr.degree, lm_degree]

theorem topPin_eval (env : Env F) :
    (topPin (F := F)).eval env =
      env.trace (col0 + 72) - env.trace (col0 + 71) * (lm (F := F) 2).eval env *
        (lm (F := F) 1).eval env * (lm (F := F) 0).eval env := by
  simp [topPin, colTop, colP, bcur, CoeffExpr.eval]

/-- Base-field power gadget. -/
def factor2 (k : ℕ) : CoeffExpr F :=
  .add (.const 1) (.mul (colM k) (.sub (.const (2 ^ (2 ^ k) : F)) (.const 1)))
def hPin : CoeffExpr F :=
  .sub colHbase (.mul (.mul (factor2 0) (factor2 1)) (factor2 2))
def tPin : CoeffExpr F :=
  .sub colTbase (.mul (.mul (.mul colHbase (factor2 3)) (factor2 4)) (factor2 5))

theorem factor2_degree (k : ℕ) : (factor2 (F := F) k).degree = 1 := by
  simp [factor2, CoeffExpr.degree]
theorem hPin_degree : (hPin (F := F)).degree ≤ 4 := by
  simp [hPin, factor2, CoeffExpr.degree]
theorem tPin_degree : (tPin (F := F)).degree ≤ 4 := by
  simp [tPin, factor2, CoeffExpr.degree]

/-- Base-field power pins `h`, `t`. -/
def powerPins : List (CoeffExpr F) := [hPin, tPin]

theorem powerPins_degree : ∀ g ∈ powerPins (F := F), g.degree ≤ 4 := by
  intro g hg
  simp only [powerPins, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h
  · rw [h]; exact hPin_degree
  · rw [h]; exact tPin_degree

/-- Bit `i` of the characteristic (`p_i`). -/
noncomputable def pBit (F : Type*) [Field F] (i : ℕ) : Bool := (ringChar F).testBit i

/-- `lin_j`: `c_j` where `p_{n−2−j} = 1`, else `1 − c_j`. -/
noncomputable def linCol (j : ℕ) : CoeffExpr F :=
  if pBit F (formRN F - 2 - j) then colC j else .sub (.const 1) (colC j)

@[simp] theorem linCol_degree (j : ℕ) : (linCol (F := F) j).degree = 1 := by
  unfold linCol
  split_ifs <;> simp [CoeffExpr.degree, colC, bcur]

theorem testBit_pred_size {n : ℕ} (hn : n ≠ 0) : n.testBit (Nat.size n - 1) = true := by
  have hpos : 0 < Nat.size n := (Nat.size_pos).mpr (Nat.pos_of_ne_zero hn)
  have hk : Nat.size n - 1 < Nat.size n := Nat.sub_lt hpos Nat.one_pos
  have hle : 2 ^ (Nat.size n - 1) ≤ n := (Nat.lt_size).mp hk
  have hlt : n < 2 ^ (Nat.size n - 1 + 1) := by
    have : Nat.size n - 1 + 1 = Nat.size n := Nat.sub_add_cancel (Nat.one_le_of_lt hpos)
    rw [this]
    exact Nat.lt_size_self n
  exact Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hle hlt

/-- Eq-chain helper pin, seeded by `top`. Factors are `lin`, not raw `c`. -/
def helperAt (k : ℕ) : CoeffExpr F := if k = 0 then colTop else colE (k - 1)
noncomputable def helperPinAt (k : ℕ) : CoeffExpr F :=
  .sub (colE k)
    (.mul (.mul (.mul (helperAt k) (linCol (3 * k))) (linCol (3 * k + 1)))
      (linCol (3 * k + 2)))

theorem helperAt_degree (k : ℕ) : (helperAt (F := F) k).degree = 1 := by
  unfold helperAt; split_ifs <;> simp
theorem helperPinAt_degree (k : ℕ) : (helperPinAt (F := F) k).degree ≤ 4 := by
  unfold helperPinAt helperAt
  have h1 := linCol_degree (F := F) (3 * k)
  have h2 := linCol_degree (F := F) (3 * k + 1)
  have h3 := linCol_degree (F := F) (3 * k + 2)
  split_ifs <;> simp [CoeffExpr.degree, h1, h2, h3]

noncomputable def helperPins : List (CoeffExpr F) := (List.range 21).map helperPinAt

theorem helperPins_degree : ∀ g ∈ helperPins (F := F), g.degree ≤ 4 := by
  intro g hg
  simp only [helperPins, List.mem_map] at hg
  obtain ⟨k, _, rfl⟩ := hg
  exact helperPinAt_degree k

/-- Goldilocks `p_i` bits. -/
def goldilocksBit (i : ℕ) : Bool := decide (32 ≤ i ∧ i ≤ 63) || decide (i = 0)

def linC (j : ℕ) (b : Bool) : CoeffExpr F :=
  if b then colC j else .sub (.const 1) (colC j)

theorem linC_degree (j : ℕ) (b : Bool) : (linC (F := F) j b).degree = 1 := by
  cases b <;> simp [linC, CoeffExpr.degree]

def foldMul : List (CoeffExpr F) → CoeffExpr F → CoeffExpr F
  | [], E => E
  | l :: ls, E => foldMul ls (.mul E l)

theorem foldMul_degree (ls : List (CoeffExpr F)) (E : CoeffExpr F) (d : ℕ)
    (hE : E.degree = d) (hl : ∀ l ∈ ls, l.degree = 1) :
    (foldMul ls E).degree = d + ls.length := by
  induction ls generalizing E d with
  | nil => simp [foldMul, hE]
  | cons l ls ih =>
      simp only [foldMul, List.length_cons]
      rw [ih (.mul E l) (d + 1) (by simp [CoeffExpr.degree, hE, hl l (by simp)])
        (fun x hx => hl x (by simp [hx]))]
      ring

noncomputable def termAt (k : ℕ) : CoeffExpr F :=
  .mul (foldMul ((List.range (k % 3)).map fun j => linCol (k - (k % 3) + j))
    (helperAt (k / 3)))
    (.sub (.const 1) (colC k))

theorem termAt_degree (k : ℕ) : (termAt (F := F) k).degree ≤ 4 := by
  have hlin : ∀ l ∈ (List.range (k % 3)).map (fun j =>
      linCol (F := F) (k - (k % 3) + j)),
      l.degree = 1 := by
    intro l hl
    simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨j, _, rfl⟩ := hl
    exact linCol_degree _
  have hf := foldMul_degree _ _ 1 (helperAt_degree (k / 3)) hlin
  unfold termAt
  simp only [CoeffExpr.degree, hf, List.length_map, List.length_range, colC_degree]
  have hmod : k % 3 ≤ 2 := Nat.le_of_lt_succ (Nat.mod_lt k (Nat.succ_pos 2))
  omega

def sumExpr : List (CoeffExpr F) → CoeffExpr F
  | [] => .const 0
  | t :: ts => .add t (sumExpr ts)

theorem sumExpr_degree (L : List (CoeffExpr F)) (h : ∀ t ∈ L, t.degree ≤ 4) :
    (sumExpr L).degree ≤ 4 := by
  induction L with
  | nil => simp [sumExpr, CoeffExpr.degree]
  | cons t ts ih =>
      simp only [sumExpr, CoeffExpr.degree]
      exact max_le (h t (by simp)) (ih (fun x hx => h x (by simp [hx])))

/-- Inclusion bit of the comparison sum, as a degree-0 coefficient. -/
noncomputable def bitCoeff (b : Bool) : CoeffExpr F :=
  if b then .const 1 else .const 0

theorem bitCoeff_degree (b : Bool) : (bitCoeff (F := F) b).degree = 0 := by
  cases b <;> simp [bitCoeff, CoeffExpr.degree]

/-- Top-seeded comparison terms over `c_1..c_{63}`.  Index `k` compares bit `n−2−k`
    (**C1**: against `p_{n−2−k}`), and the coefficient is `0` when `k + 1 ≥ n` (no such bit);
    every index is present so the list spine stays `List.range 63`. -/
noncomputable def comparisonTerms : List (CoeffExpr F) :=
  (List.range 63).map fun k =>
    .mul (bitCoeff (decide (k + 1 < formRN F) && pBit F (formRN F - 2 - k))) (termAt k)

theorem comparisonTerms_degree : ∀ t ∈ comparisonTerms (F := F), t.degree ≤ 4 := by
  intro t ht
  simp only [comparisonTerms, List.mem_map] at ht
  obtain ⟨k, _, rfl⟩ := ht
  have ht := termAt_degree (F := F) k
  simp only [CoeffExpr.degree, bitCoeff_degree]
  omega

/-- Top-seeded comparison `Σ terms − top = 0`. -/
noncomputable def comparisonGate : CoeffExpr F := .sub (sumExpr comparisonTerms) colTop

theorem comparisonGate_degree : (comparisonGate (F := F)).degree ≤ 4 := by
  simp only [comparisonGate, CoeffExpr.degree]
  exact max_le (sumExpr_degree _ comparisonTerms_degree) (by simp)

/-- Running product `eqm`.  `eqm_6 = 1`, `eqm_3 = p`, `eqm_0` is not stored
    (`top` is the separate summand).  Degree ≤ 3. -/
noncomputable def eqmAt : ℕ → CoeffExpr F
  | 1 => .mul (.mul colP (lm 2)) (lm 1)
  | 2 => .mul colP (lm 2)
  | 3 => colP
  | 4 => .mul (lm 5) (lm 4)
  | 5 => lm 5
  | 6 => .const 1
  | _ => .const 0

noncomputable def rangeTerm (k : ℕ) : CoeffExpr F :=
  .mul (.mul (eqmAt (k + 1)) (.sub (.const 1) (colM k)))
    (if nMinus1Bit F k then .const 1 else .const 0)

noncomputable def rangeTerms : List (CoeffExpr F) := (List.range 6).map rangeTerm

theorem rangeTerm_degree (k : ℕ) (hk : k < 6) :
    (rangeTerm (F := F) k).degree ≤ 4 := by
  interval_cases k <;>
    simp [rangeTerm, eqmAt, lm, CoeffExpr.degree, colP, colM, bcur] <;>
    split_ifs <;> simp [CoeffExpr.degree, colP, colM, bcur]

theorem rangeTerms_degree : ∀ t ∈ rangeTerms (F := F), t.degree ≤ 4 := by
  intro t ht
  simp only [rangeTerms, List.mem_map, List.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  exact rangeTerm_degree k hk

/-- Range gate `Σ_{k<6} eqm_{k+1}·(1−m_k)·(n−1)_k + top − 1`.
    Kept in the general chip.  At `n = 2^6` and boolean `m` it is the
    boolean telescoping identity, not `top − 1`. -/
noncomputable def rangeGate : CoeffExpr F :=
  .sub (.add (sumExpr rangeTerms) colTop) (.const 1)

theorem rangeGate_degree : (rangeGate (F := F)).degree ≤ 4 := by
  simp only [rangeGate, CoeffExpr.degree]
  exact max_le (max_le (sumExpr_degree _ rangeTerms_degree) (by simp)) (by simp)

/-- Axis equation: `op₀·(f_t.leaf − t·csum) + op₉·(f_th.leaf − t·csum)`. -/
def twoInv : F := (2 : F)⁻¹
def csumAcc : ℕ → CoeffExpr F
  | 0 => .const 1
  | n + 1 => .add (csumAcc n) (.mul (colC n) (.const (twoInv ^ (n + 1))))
def csum : CoeffExpr F := csumAcc 63

theorem csumAcc_degree : ∀ n, (csumAcc (F := F) n).degree ≤ 1 := by
  intro n
  induction n with
  | zero => simp [csumAcc, CoeffExpr.degree]
  | succ n ih =>
      simp only [csumAcc, CoeffExpr.degree]
      exact max_le ih (by simp [CoeffExpr.degree])

theorem csum_degree : (csum (F := F)).degree ≤ 1 := csumAcc_degree 63

/-- Dummy Goldilocks fill (`c = 0`) makes the Horner sum identically `1`. -/
theorem csumAcc_eval_of_zero_c (env : Env F)
    (hC : ∀ j, j < 63 → env.trace (col0 + j) = 0) :
    ∀ n, n ≤ 63 → (csumAcc (F := F) n).eval env = 1 := by
  intro n hn
  induction n with
  | zero => simp [csumAcc, CoeffExpr.eval]
  | succ n ih =>
      simp [csumAcc, CoeffExpr.eval, colC, bcur, hC n (by omega)]
      exact ih (Nat.le_of_succ_le hn)

theorem csum_eval_of_zero_c (env : Env F)
    (hC : ∀ j, j < 63 → env.trace (col0 + j) = 0) :
    (csum (F := F)).eval env = 1 :=
  csumAcc_eval_of_zero_c env hC 63 le_rfl

theorem foldMul_eval_of_zero (ls : List (CoeffExpr F)) (E : CoeffExpr F)
    (env : Env F) (hE : E.eval env = 0) :
    (foldMul ls E).eval env = 0 := by
  induction ls generalizing E with
  | nil => simpa [foldMul]
  | cons l ls ih =>
      exact ih (.mul E l) (by simp [CoeffExpr.eval, hE])

theorem helperAt_eval_of_dummy (env : Env F)
    (hE : ∀ k, k < 21 → env.trace (col0 + 73 + k) = 0)
    (hTop : env.trace (col0 + 72) = 1) (k : ℕ) (hk : k ≤ 21) :
    (helperAt (F := F) k).eval env = if k = 0 then 1 else 0 := by
  unfold helperAt
  split_ifs with h0
  · simpa [colTop, bcur, CoeffExpr.eval] using hTop
  · have hk' : k - 1 < 21 := by omega
    simpa [colE, bcur, CoeffExpr.eval] using hE (k - 1) hk'

theorem goldilocksBit_63 : goldilocksBit 63 = true := by
  simp [goldilocksBit]

theorem sumExpr_eval_zero (ts : List (CoeffExpr F)) (env : Env F)
    (h : ∀ t ∈ ts, t.eval env = 0) :
    (sumExpr ts).eval env = 0 := by
  induction ts with
  | nil => simp [sumExpr, CoeffExpr.eval]
  | cons t ts ih =>
      simp [sumExpr, CoeffExpr.eval, h t (by simp),
        ih (fun x hx => h x (by simp [hx]))]

theorem sumExpr_eval_cons (t : CoeffExpr F) (ts : List (CoeffExpr F)) (env : Env F) :
    (sumExpr (t :: ts)).eval env = t.eval env + (sumExpr ts).eval env := by
  simp [sumExpr, CoeffExpr.eval]

theorem rangeTerm_eval_of_ones (env : Env F)
    (hM : ∀ k, k < 6 → env.trace (col0 + 63 + k) = 1) (k : ℕ) (hk : k < 6) :
    (rangeTerm (F := F) k).eval env = 0 := by
  have hm : env.trace (col0 + 63 + k) = 1 := hM k hk
  simp [rangeTerm, CoeffExpr.eval, colM, bcur, hm]

theorem rangeGate_eval_of_ones (env : Env F)
    (hM : ∀ k, k < 6 → env.trace (col0 + 63 + k) = 1)
    (hTop : env.trace (col0 + 72) = 1) :
    (rangeGate (F := F)).eval env = 0 := by
  simp only [rangeGate, CoeffExpr.eval, colTop, bcur, hTop, sub_eq_zero]
  have hsum : (sumExpr (rangeTerms (F := F))).eval env = 0 := by
    refine sumExpr_eval_zero _ env ?_
    intro t ht
    simp only [rangeTerms, List.mem_map, List.mem_range] at ht
    obtain ⟨k, hk, rfl⟩ := ht
    exact rangeTerm_eval_of_ones env hM k hk
  simpa [hsum]

/-- Binary digits of `r < 2^n` reassemble `r`. -/
theorem sum_testBit_pow (n r : ℕ) (hr : r < 2 ^ n) :
    ∑ i ∈ Finset.range n, (if r.testBit i then 2 ^ i else 0) = r := by
  induction n generalizing r with
  | zero =>
      simp at hr
      simp [hr]
  | succ n ih =>
      rw [Finset.sum_range_succ']
      have hr2 : r / 2 < 2 ^ n := by
        have hmul : r < 2 * 2 ^ n := by simpa [pow_succ, Nat.mul_comm] using hr
        exact Nat.div_lt_of_lt_mul hmul
      have htail := ih (r / 2) hr2
      have hsum :
          ∑ i ∈ Finset.range n, (if r.testBit (i + 1) then 2 ^ (i + 1) else 0) =
            2 * (r / 2 : ℕ) := by
        have hcong :
            ∑ i ∈ Finset.range n, (if r.testBit (i + 1) then 2 ^ (i + 1) else 0) =
              ∑ i ∈ Finset.range n, (2 * if (r / 2).testBit i then 2 ^ i else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Nat.testBit_add_one]
          by_cases hb : (r / 2).testBit i
          · simp [hb, pow_succ, Nat.mul_comm]
          · simp [hb]
        rw [hcong, ← Finset.mul_sum, htail]
      have hbit : (if r.testBit 0 then 1 else 0) = r % 2 := by
        simp only [Nat.testBit_zero]
        cases Nat.mod_two_eq_zero_or_one r with
        | inl h => simp [h]
        | inr h => simp [h]
      rw [pow_zero, hsum, hbit, Nat.div_add_mod]

/-- `m = 63`, `c₀ = 0`, and `cⱼ` the bits of `r < 2^62` give `t · csum = 2^63 + r`. -/
theorem twoPow_csum_low (env : Env F) (r : ℕ) (hr : r < 2 ^ 62)
    (h2 : (2 : F) ≠ 0) (h0 : env.trace col0 = 0)
    (hbit : ∀ j, j < 62 →
      env.trace (col0 + (j + 1)) = if r.testBit (61 - j) then (1 : F) else 0) :
    (2 : F) ^ 63 * (csum (F := F)).eval env = (2 : F) ^ 63 + (r : F) := by
  have htwo (k : ℕ) (hk : k ≤ 63) :
      (2 : F) ^ 63 * twoInv ^ k = (2 : F) ^ (63 - k) := by
    have hkpow : (2 : F) ^ k ≠ 0 := pow_ne_zero k h2
    have hn : (2 : F) ^ 63 = (2 : F) ^ (63 - k) * (2 : F) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    calc (2 : F) ^ 63 * twoInv ^ k
        = (2 : F) ^ 63 * ((2 : F) ^ k)⁻¹ := by rw [twoInv, inv_pow]
      _ = ((2 : F) ^ (63 - k) * (2 : F) ^ k) * ((2 : F) ^ k)⁻¹ := by rw [hn]
      _ = (2 : F) ^ (63 - k) * ((2 : F) ^ k * ((2 : F) ^ k)⁻¹) := by ring
      _ = (2 : F) ^ (63 - k) := by rw [mul_inv_cancel₀ hkpow, mul_one]
  have hacc : ∀ n, n ≤ 63 →
      (2 : F) ^ 63 * (csumAcc (F := F) n).eval env =
        (2 : F) ^ 63 +
          ∑ i ∈ Finset.range (n - 1),
            (if r.testBit (61 - i) then (2 : F) ^ (61 - i) else 0) := by
    intro n hn
    induction n with
    | zero =>
        simp [csumAcc, CoeffExpr.eval]
    | succ n ih =>
        have ihn := ih (Nat.le_of_succ_le hn)
        simp only [csumAcc, CoeffExpr.eval, colC, bcur, Nat.succ_sub_succ_eq_sub]
        by_cases hn0 : n = 0
        · subst n
          simp [h0, htwo 1 (by omega), ihn]
        · have hn62 : n - 1 < 62 := by omega
          have hc := hbit (n - 1) hn62
          have hcol : env.trace (col0 + n) = if r.testBit (62 - n) then (1 : F) else 0 := by
            simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0),
              show 61 - (n - 1) = 62 - n by omega] using hc
          have hadd := htwo (n + 1) (by omega)
          -- 2^63 * (acc + c_n * twoInv^(n+1)) = previous + c_n * 2^(62-n)
          calc (2 : F) ^ 63 *
                ((csumAcc (F := F) n).eval env +
                  env.trace (col0 + n) * twoInv ^ (n + 1))
              = (2 : F) ^ 63 * (csumAcc (F := F) n).eval env +
                  env.trace (col0 + n) * ((2 : F) ^ 63 * twoInv ^ (n + 1)) := by ring
            _ = (2 : F) ^ 63 +
                  ∑ i ∈ Finset.range (n - 1),
                    (if r.testBit (61 - i) then (2 : F) ^ (61 - i) else 0) +
                  env.trace (col0 + n) * (2 : F) ^ (62 - n) := by
                    have hexp : 63 - (n + 1) = 62 - n := by omega
                    rw [ihn, hadd, hexp]
            _ = (2 : F) ^ 63 +
                  ∑ i ∈ Finset.range n,
                    (if r.testBit (61 - i) then (2 : F) ^ (61 - i) else 0) := by
                  have hnpred : n = n - 1 + 1 :=
                    (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)).symm
                  have hsum :
                      ∑ i ∈ Finset.range n,
                          (if r.testBit (61 - i) then (2 : F) ^ (61 - i) else 0) =
                        ∑ i ∈ Finset.range (n - 1),
                            (if r.testBit (61 - i) then (2 : F) ^ (61 - i) else 0) +
                          (if r.testBit (61 - (n - 1)) then (2 : F) ^ (61 - (n - 1)) else 0) := by
                    conv_lhs => rw [hnpred]
                    rw [Finset.sum_range_succ]
                  rw [hsum, hcol]
                  by_cases hb : r.testBit (62 - n)
                  · simp [hb, show 61 - (n - 1) = 62 - n by omega, add_assoc]
                  · simp [hb, show 61 - (n - 1) = 62 - n by omega]
  have h63 := hacc 63 (by omega)
  have hreidx :
      ∑ i ∈ Finset.range 62, (if r.testBit (61 - i) then (2 : F) ^ (61 - i) else 0) =
        ∑ i ∈ Finset.range 62, (if r.testBit i then (2 : F) ^ i else 0) := by
    refine Finset.sum_nbij' (fun i => 61 - i) (fun j => 61 - j) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro i hi
      rfl
  have hcast :
      ∑ i ∈ Finset.range 62, (if r.testBit i then (2 : F) ^ i else 0) = (r : F) := by
    have hnat := sum_testBit_pow 62 r hr
    conv_rhs => rw [← hnat]
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hb : r.testBit i <;> simp [hb, Nat.cast_pow]
  simpa [csum, hreidx, hcast] using h63

/-- Bit `62 - j` of `r`, as a field element. -/
noncomputable def cVal (r j : ℕ) : F :=
  if r.testBit (62 - j) then (1 : F) else 0

/-- `lin_j` of those bits against `p_{n−2−j}` (C1 alignment). -/
noncomputable def linVal (r j : ℕ) : F :=
  if pBit F (formRN F - 2 - j) then cVal r j else (1 : F) - cVal r j

/-- Prefix product of `lin`, seeded by `1` (`top` on an `m = 63` row). -/
noncomputable def eqRun (r : ℕ) : ℕ → F
  | 0 => (1 : F)
  | n + 1 => eqRun r n * linVal r n

/-- Top-seeded comparison accumulator.  `ltRun r 63 = 1` is the gate's `<` bit. -/
noncomputable def ltRun (r : ℕ) : ℕ → F
  | 0 => (0 : F)
  | n + 1 =>
      ltRun r n +
        eqRun r n * (if (decide (n + 1 < formRN F) && pBit F (formRN F - 2 - n)) then (1 : F) - cVal r n else 0)

theorem two_pow_63_cast : ((2 ^ 63 : ℕ) : F) = (2 : F) ^ 63 :=
  Nat.cast_pow (α := F) (m := 2) (n := 63)

/-- `m = 63` and `cⱼ =` bit `62 - j` of `r < 2^63` give `t · csum = 2^63 + r`,
including the `c₀` place. -/
theorem twoPow_csum_bits (env : Env F) (r : ℕ) (hr : r < 2 ^ 63)
    (h2 : (2 : F) ≠ 0)
    (hbit : ∀ j, j < 63 →
      env.trace (col0 + j) = if r.testBit (62 - j) then (1 : F) else 0) :
    (2 : F) ^ 63 * (csum (F := F)).eval env = (2 : F) ^ 63 + (r : F) := by
  have htwo (k : ℕ) (hk : k ≤ 63) :
      (2 : F) ^ 63 * twoInv ^ k = (2 : F) ^ (63 - k) := by
    have hkpow : (2 : F) ^ k ≠ 0 := pow_ne_zero k h2
    have hn : (2 : F) ^ 63 = (2 : F) ^ (63 - k) * (2 : F) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    calc (2 : F) ^ 63 * twoInv ^ k
        = (2 : F) ^ 63 * ((2 : F) ^ k)⁻¹ := by rw [twoInv, inv_pow]
      _ = ((2 : F) ^ (63 - k) * (2 : F) ^ k) * ((2 : F) ^ k)⁻¹ := by rw [hn]
      _ = (2 : F) ^ (63 - k) * ((2 : F) ^ k * ((2 : F) ^ k)⁻¹) := by ring
      _ = (2 : F) ^ (63 - k) := by rw [mul_inv_cancel₀ hkpow, mul_one]
  have hacc : ∀ n, n ≤ 63 →
      (2 : F) ^ 63 * (csumAcc (F := F) n).eval env =
        (2 : F) ^ 63 +
          ∑ i ∈ Finset.range n,
            (if r.testBit (62 - i) then (2 : F) ^ (62 - i) else 0) := by
    intro n hn
    induction n with
    | zero =>
        simp [csumAcc, CoeffExpr.eval]
    | succ n ih =>
        have ihn := ih (Nat.le_of_succ_le hn)
        simp only [csumAcc, CoeffExpr.eval, colC, bcur]
        have hc := hbit n (by omega)
        have hadd := htwo (n + 1) (by omega)
        calc (2 : F) ^ 63 *
              ((csumAcc (F := F) n).eval env +
                env.trace (col0 + n) * twoInv ^ (n + 1))
            = (2 : F) ^ 63 * (csumAcc (F := F) n).eval env +
                env.trace (col0 + n) * ((2 : F) ^ 63 * twoInv ^ (n + 1)) := by ring
          _ = (2 : F) ^ 63 +
                ∑ i ∈ Finset.range n,
                  (if r.testBit (62 - i) then (2 : F) ^ (62 - i) else 0) +
                env.trace (col0 + n) * (2 : F) ^ (62 - n) := by
                  have hexp : 63 - (n + 1) = 62 - n := by omega
                  rw [ihn, hadd, hexp]
          _ = (2 : F) ^ 63 +
                ∑ i ∈ Finset.range (n + 1),
                  (if r.testBit (62 - i) then (2 : F) ^ (62 - i) else 0) := by
                rw [Finset.sum_range_succ]
                rw [hc]
                by_cases hb : r.testBit (62 - n)
                · simp [hb, add_assoc]
                · simp [hb]
  have h63 := hacc 63 (by omega)
  have hreidx :
      ∑ i ∈ Finset.range 63, (if r.testBit (62 - i) then (2 : F) ^ (62 - i) else 0) =
        ∑ i ∈ Finset.range 63, (if r.testBit i then (2 : F) ^ i else 0) := by
    refine Finset.sum_nbij' (fun i => 62 - i) (fun j => 62 - j) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro i hi
      rfl
  have hcast :
      ∑ i ∈ Finset.range 63, (if r.testBit i then (2 : F) ^ i else 0) = (r : F) := by
    have hnat := sum_testBit_pow 63 r hr
    conv_rhs => rw [← hnat]
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hb : r.testBit i <;> simp [hb, Nat.cast_pow]
  simpa [csum, hreidx, hcast] using h63

theorem linCol_eval_cVal (env : Env F) (r j : ℕ)
    (hC : env.trace (col0 + j) = cVal r j) :
    (linCol (F := F) j).eval env = linVal r j := by
  unfold linCol linVal
  split_ifs with hp
  · simpa [colC, bcur, CoeffExpr.eval] using hC
  · have hc : env.trace (col0 + j) = cVal r j := hC
    simp [colC, bcur, CoeffExpr.eval, hc, cVal]

theorem eqRun_add3 (r n : ℕ) :
    eqRun r (n + 3) =
      (((eqRun r n : F) * (linVal r n : F) : F) * (linVal r (n + 1) : F) : F) *
        (linVal r (n + 2) : F) := by
  rw [show n + 3 = n + 2 + 1 by omega, eqRun]
  rw [show n + 2 = n + 1 + 1 by omega, eqRun]
  rw [eqRun]

theorem helperAt_eval_of_run (env : Env F) (r : ℕ)
    (hTop : env.trace (col0 + 72) = 1)
    (hE : ∀ k, k < 21 → env.trace (col0 + 73 + k) = eqRun r (3 * (k + 1)))
    (k : ℕ) (hk : k ≤ 21) :
    (helperAt (F := F) k).eval env = eqRun r (3 * k) := by
  unfold helperAt
  by_cases hk0 : k = 0
  · simp [hk0, eqRun, colTop, bcur, CoeffExpr.eval, hTop]
  · rw [if_neg hk0]
    have hk' : k - 1 < 21 := by omega
    have hE' := hE (k - 1) hk'
    have hidx : 3 * ((k - 1) + 1) = 3 * k := by omega
    simpa [colE, bcur, CoeffExpr.eval, hidx] using hE'

theorem helperPinAt_eval_of_run (env : Env F) (r : ℕ)
    (hTop : env.trace (col0 + 72) = 1)
    (hC : ∀ j, j < 63 → env.trace (col0 + j) = cVal r j)
    (hE : ∀ k, k < 21 → env.trace (col0 + 73 + k) = eqRun r (3 * (k + 1)))
    (k : ℕ) (hk : k < 21) :
    (helperPinAt (F := F) k).eval env = 0 := by
  have hEk : env.trace (col0 + 73 + k) = eqRun r (3 * (k + 1)) := hE k hk
  have hAt : (helperAt (F := F) k).eval env = eqRun r (3 * k) :=
    helperAt_eval_of_run env r hTop hE k (by omega)
  have hlin0 : (linCol (F := F) (3 * k)).eval env = linVal r (3 * k) :=
    linCol_eval_cVal env r (3 * k) (hC _ (by omega))
  have hlin1 : (linCol (F := F) (3 * k + 1)).eval env = linVal r (3 * k + 1) :=
    linCol_eval_cVal env r (3 * k + 1) (hC _ (by omega))
  have hlin2 : (linCol (F := F) (3 * k + 2)).eval env = linVal r (3 * k + 2) :=
    linCol_eval_cVal env r (3 * k + 2) (hC _ (by omega))
  have hprod :
      eqRun r (3 * (k + 1)) =
        (((eqRun r (3 * k) : F) * (linVal r (3 * k) : F) : F) *
            (linVal r (3 * k + 1) : F) : F) *
          (linVal r (3 * k + 2) : F) := by
    rw [show 3 * (k + 1) = 3 * k + 3 by omega]
    exact eqRun_add3 r (3 * k)
  simp only [helperPinAt, CoeffExpr.eval, colE, bcur]
  rw [hEk, hAt, hlin0, hlin1, hlin2, ← hprod, sub_self]

theorem ltRun_eq_sum (r : ℕ) :
    ltRun r 63 =
      ∑ i ∈ Finset.range 63,
        eqRun r i * (if (decide (i + 1 < formRN F) && pBit F (formRN F - 2 - i)) then (1 : F) - cVal r i else 0) := by
  have h : ∀ n, n ≤ 63 →
      ltRun r n =
        ∑ i ∈ Finset.range n,
          eqRun r i * (if (decide (i + 1 < formRN F) && pBit F (formRN F - 2 - i)) then (1 : F) - cVal r i else 0) := by
    intro n hn
    induction n with
    | zero => simp [ltRun]
    | succ n ih =>
        rw [ltRun, ih (Nat.le_of_succ_le hn), Finset.sum_range_succ]
  exact h 63 le_rfl

theorem termAt_eval_of_run (env : Env F) (r k : ℕ)
    (hTop : env.trace (col0 + 72) = 1)
    (hC : ∀ j, j < 63 → env.trace (col0 + j) = cVal r j)
    (hE : ∀ t, t < 21 → env.trace (col0 + 73 + t) = eqRun r (3 * (t + 1)))
    (hk : k < 63) :
    (termAt (F := F) k).eval env = eqRun r k * ((1 : F) - cVal r k) := by
  have hAt : (helperAt (F := F) (k / 3)).eval env = eqRun r (3 * (k / 3)) :=
    helperAt_eval_of_run env r hTop hE (k / 3) (by omega)
  have hc : env.trace (col0 + k) = cVal r k := hC k hk
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · simp only [termAt, h0, List.range_zero, List.map_nil, foldMul, CoeffExpr.eval, colC, bcur]
    rw [hAt, hc]
    rw [show 3 * (k / 3) = k by omega]
  · have hk1 : k - 1 < 63 := by omega
    have hlin : (linCol (F := F) (k - 1)).eval env = linVal r (k - 1) :=
      linCol_eval_cVal env r (k - 1) (hC _ hk1)
    have heq : eqRun r k =
        (eqRun r (3 * (k / 3)) : F) * (linVal r (k - 1) : F) := by
      conv_lhs => rw [show k = 3 * (k / 3) + 1 by omega]
      rw [eqRun, show 3 * (k / 3) = k - 1 by omega]
    have hr1 : List.range (k % 3) = [0] := by
      simp [h1, List.range_succ, List.range_zero, List.nil_append]
    simp only [termAt, hr1, List.map_cons, List.map_nil, foldMul, CoeffExpr.eval, colC, bcur]
    rw [show k - k % 3 + 0 = k - 1 by omega]
    rw [hAt, hlin, hc, ← heq]
  · have hk1 : k - 1 < 63 := by omega
    have hk2 : k - 2 < 63 := by omega
    have hlin1 : (linCol (F := F) (k - 2)).eval env = linVal r (k - 2) :=
      linCol_eval_cVal env r (k - 2) (hC _ hk2)
    have hlin2 : (linCol (F := F) (k - 1)).eval env = linVal r (k - 1) :=
      linCol_eval_cVal env r (k - 1) (hC _ hk1)
    have heq : eqRun r k =
        ((eqRun r (3 * (k / 3)) : F) * (linVal r (k - 2) : F) : F) *
          (linVal r (k - 1) : F) := by
      conv_lhs => rw [show k = 3 * (k / 3) + 1 + 1 by omega]
      rw [eqRun, eqRun, show 3 * (k / 3) = k - 2 by omega, show k - 2 + 1 = k - 1 by omega]
    have hr2 : List.range (k % 3) = [0, 1] := by
      simp [h2, List.range_succ, List.range_zero, List.nil_append]
    simp only [termAt, hr2, List.map_cons, List.map_nil, foldMul, CoeffExpr.eval, colC, bcur]
    rw [show k - k % 3 + 0 = k - 2 by omega, show k - k % 3 + 1 = k - 1 by omega]
    rw [hAt, hlin1, hlin2, hc, ← heq]

theorem sumExpr_append (xs ys : List (CoeffExpr F)) (env : Env F) :
    (sumExpr (xs ++ ys)).eval env = (sumExpr xs).eval env + (sumExpr ys).eval env := by
  induction xs with
  | nil => simp [sumExpr, CoeffExpr.eval]
  | cons x xs ih =>
      simp [sumExpr, CoeffExpr.eval, ih, add_assoc]

theorem comparisonGate_eval_of_run (env : Env F) (r : ℕ)
    (hTop : env.trace (col0 + 72) = 1)
    (hC : ∀ j, j < 63 → env.trace (col0 + j) = cVal r j)
    (hE : ∀ k, k < 21 → env.trace (col0 + 73 + k) = eqRun r (3 * (k + 1)))
    (hlt : ltRun r 63 = (1 : F)) :
    (comparisonGate (F := F)).eval env = 0 := by
  simp only [comparisonGate, CoeffExpr.eval, colTop, bcur, hTop, sub_eq_zero]
  let f : ℕ → F := fun i =>
    eqRun r i * (if (decide (i + 1 < formRN F) && pBit F (formRN F - 2 - i)) then (1 : F) - cVal r i else 0)
  have hlist : ∀ n, n ≤ 63 →
      (sumExpr ((List.range n).map fun k =>
          CoeffExpr.mul (bitCoeff ((decide (k + 1 < formRN F) && pBit F (formRN F - 2 - k)))) (termAt (F := F) k))).eval env =
        ∑ i ∈ Finset.range n, f i := by
    intro n hn
    induction n with
    | zero => simp [sumExpr, CoeffExpr.eval]
    | succ n ih =>
        rw [List.range_succ, List.map_append, List.map_singleton, sumExpr_append,
          ih (Nat.le_of_succ_le hn), Finset.sum_range_succ]
        have ht := termAt_eval_of_run env r n hTop hC hE (by omega)
        have hb : (bitCoeff ((decide (n + 1 < formRN F) && pBit F (formRN F - 2 - n)))).eval env =
            if (decide (n + 1 < formRN F) && pBit F (formRN F - 2 - n)) then (1 : F) else 0 := by
          cases (decide (n + 1 < formRN F) && pBit F (formRN F - 2 - n)) <;> simp [bitCoeff, CoeffExpr.eval]
        simp only [sumExpr, CoeffExpr.eval, add_zero]
        rw [hb, ht]
        cases hp : (decide (n + 1 < formRN F) && pBit F (formRN F - 2 - n))
        · simp only [f, hp]
          rw [if_neg (by decide : ¬ false = true), if_neg (by decide : ¬ false = true)]
          simp [zero_mul, mul_zero]
        · simp only [f, hp]
          rw [if_pos trivial, if_pos trivial]
          simp [one_mul]
  have hterms : (sumExpr (comparisonTerms (F := F))).eval env = ltRun r 63 := by
    rw [comparisonTerms, ltRun_eq_sum]
    exact hlist 63 le_rfl
  rw [hterms]
  exact hlt

/-- Form R axis: `op₀·(f_t.leaf − t·csum) + op₉·(f_th.leaf − t·csum)`.
    Leaves are base columns 136 / 145 (roles 41 / 44, coordinate 0). -/
def ftLeaf : CoeffExpr F := bcur 136
def fthLeaf : CoeffExpr F := bcur 145
def axisEquation : CoeffExpr F :=
  .add
    (.mul (bcur 0) (.sub ftLeaf (.mul colTbase csum)))
    (.mul (bcur 9) (.sub fthLeaf (.mul colTbase csum)))

/-- The axis gate vanishes once `csum = 1` and each opcode product is zero.
    On every state except `s0` / `s9` both opcodes are zero.  On `s0` / `s9`
    the product is the leaf-versus-`t·csum` obligation. -/
theorem axisEquation_eval_of_csum_one (env : Env F)
    (hC : ∀ j, j < 63 → env.trace (col0 + j) = 0)
    (hT : env.trace (col0 + 70) = (2 : F) ^ 63)
    (h0 : env.trace 0 * (env.trace 136 - env.trace (col0 + 70) * 1) = 0)
    (h9 : env.trace 9 * (env.trace 145 - env.trace (col0 + 70) * 1) = 0) :
    (axisEquation (F := F)).eval env = 0 := by
  simp only [axisEquation, ftLeaf, fthLeaf, colTbase, bcur, CoeffExpr.eval,
    csum_eval_of_zero_c env hC, hT, mul_one] at h0 h9 ⊢
  rw [h0, h9]
  ring

/-- On `s9 = 0`, the axis gate is the `s0` opcode product alone. -/
theorem axis_s0_mul_term (env : Env F) (h9z : env.trace 9 = 0) :
    (axisEquation (F := F)).eval env =
      env.trace 0 *
        (env.trace 136 - env.trace (col0 + 70) * (csum (F := F)).eval env) := by
  simp [axisEquation, ftLeaf, fthLeaf, colTbase, bcur, CoeffExpr.eval, h9z, zero_mul, add_zero]

/-- On `s0 = 0`, the axis gate is the `s9` opcode product alone. -/
theorem axis_s9_mul_term (env : Env F) (h0z : env.trace 0 = 0) :
    (axisEquation (F := F)).eval env =
      env.trace 9 *
        (env.trace 145 - env.trace (col0 + 70) * (csum (F := F)).eval env) := by
  simp [axisEquation, ftLeaf, fthLeaf, colTbase, bcur, CoeffExpr.eval, h0z, zero_mul, add_zero]

/-- The axis gate is the sum of the two opcode products. -/
theorem axisEquation_eval_of_products (env : Env F)
    (h0 : env.trace 0 * (env.trace 136 - env.trace (col0 + 70) * (csum (F := F)).eval env) = 0)
    (h9 : env.trace 9 * (env.trace 145 - env.trace (col0 + 70) * (csum (F := F)).eval env) = 0) :
    (axisEquation (F := F)).eval env = 0 := by
  simp only [axisEquation, ftLeaf, fthLeaf, colTbase, bcur, CoeffExpr.eval] at h0 h9 ⊢
  rw [h0, h9]
  ring

theorem axisEquation_degree : (axisEquation (F := F)).degree ≤ 4 := by
  have hc := csum_degree (F := F)
  simp only [axisEquation, ftLeaf, fthLeaf, CoeffExpr.degree, colTbase, bcur]
  have : (csum (F := F)).degree ≤ 1 := hc
  omega

/-- The 97 base-field form-R certificate gates (the two `𝕂` power pins are
    `OptimizedComputeCorrectedFinal.formRLamPins`, `3` coordinates each). -/
noncomputable def formRNamed : List (CoeffExpr F) := [comparisonGate, rangeGate, axisEquation]
noncomputable def formRPins : List (CoeffExpr F) := [pPin, topPin]
noncomputable def formRCertificateGates : List (CoeffExpr F) :=
  booleanGates ++ powerPins ++ formRPins ++ helperPins ++ formRNamed

theorem booleanGates_length : (booleanGates (F := F)).length = 69 := by
  simp [booleanGates]
theorem helperPins_length : (helperPins (F := F)).length = 21 := by
  simp [helperPins]
@[simp] theorem powerPins_length : (powerPins (F := F)).length = 2 := by
  simp [powerPins]
@[simp] theorem formRCertificateGates_length :
    (formRCertificateGates (F := F)).length = 97 := by
  simp [formRCertificateGates, formRPins, formRNamed, booleanGates_length,
    helperPins_length, powerPins_length]

theorem formRNamed_degree : ∀ g ∈ formRNamed (F := F), g.degree ≤ 4 := by
  intro g hg
  simp only [formRNamed, List.mem_cons, List.not_mem_nil, or_false] at hg
  cases hg with
  | inl h => rw [h]; exact comparisonGate_degree
  | inr h =>
      cases h with
      | inl h => rw [h]; exact rangeGate_degree
      | inr h => rw [h]; exact axisEquation_degree

theorem formRPins_degree : ∀ g ∈ formRPins (F := F), g.degree ≤ 4 := by
  intro g hg
  simp only [formRPins, List.mem_cons, List.not_mem_nil, or_false] at hg
  cases hg with
  | inl h => rw [h]; exact pPin_degree
  | inr h => rw [h]; exact topPin_degree

theorem formRCertificateGates_degree :
    ∀ g ∈ formRCertificateGates (F := F), g.degree ≤ 4 := by
  intro g hg
  simp only [formRCertificateGates] at hg
  rcases List.mem_append.mp hg with h | hnamed
  · rcases List.mem_append.mp h with h | hhelp
    · rcases List.mem_append.mp h with h | hpins
      · rcases List.mem_append.mp h with hbool | hpow
        · exact booleanGates_degree g hbool
        · exact powerPins_degree g hpow
      · exact formRPins_degree g hpins
    · exact helperPins_degree g hhelp
  · exact formRNamed_degree g hnamed

/-- Bit `0/1` as a field element. -/
def bit01 (b : Bool) : F := if b then 1 else 0

@[simp] theorem bit01_true : bit01 (F := F) true = 1 := rfl
@[simp] theorem bit01_false : bit01 (F := F) false = 0 := rfl

theorem bit_switch (b : Bool) (x : F) :
    (1 : F) + bit01 b * (x - 1) = if b then x else 1 := by
  cases b <;> simp

theorem bit01_mul_sub (b : Bool) : bit01 (F := F) b * (bit01 b - 1) = 0 := by
  cases b <;> simp

theorem bit01_eq_zero_or_one (b : Bool) :
    bit01 (F := F) b = 0 ∨ bit01 (F := F) b = 1 := by
  cases b <;> simp

theorem bit01_mul_zero_or_one {x y : F}
    (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    x * y = 0 ∨ x * y = 1 := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy]

theorem bit01_prod6_zero_or_one (b0 b1 b2 b3 b4 b5 : Bool) :
    bit01 (F := F) b5 * bit01 b4 * bit01 b3 * bit01 b2 * bit01 b1 * bit01 b0 = 0 ∨
      bit01 (F := F) b5 * bit01 b4 * bit01 b3 * bit01 b2 * bit01 b1 * bit01 b0 = 1 :=
  bit01_mul_zero_or_one
    (bit01_mul_zero_or_one
      (bit01_mul_zero_or_one
        (bit01_mul_zero_or_one
          (bit01_mul_zero_or_one (bit01_eq_zero_or_one b5) (bit01_eq_zero_or_one b4))
          (bit01_eq_zero_or_one b3))
        (bit01_eq_zero_or_one b2))
      (bit01_eq_zero_or_one b1))
    (bit01_eq_zero_or_one b0)

/-- Bit-matched shift value of `m` at bit `k`. -/
noncomputable def matchedLm (F : Type*) [Field F] (m k : ℕ) : F :=
  if nMinus1Bit F k then bit01 (m.testBit k) else 1 - bit01 (m.testBit k)

noncomputable def matchedP (F : Type*) [Field F] (m : ℕ) : F :=
  matchedLm F m 5 * matchedLm F m 4 * matchedLm F m 3

noncomputable def matchedTop (F : Type*) [Field F] (m : ℕ) : F :=
  matchedP F m * matchedLm F m 2 * matchedLm F m 1 * matchedLm F m 0

theorem matchedLm_of_eq (m k : ℕ) (h : m.testBit k = nMinus1Bit F k) :
    matchedLm F m k = 1 := by
  simp [matchedLm, h]
  cases nMinus1Bit F k <;> simp

theorem testBit_mod_64 (m k : ℕ) (hk : k < 6) :
    (m % 64).testBit k = m.testBit k := by
  have hpow : (64 : ℕ) = 2 ^ 6 := by decide
  rw [hpow, Nat.testBit_mod_two_pow]
  simp [hk]

theorem nMinus1Low_testBit (k : ℕ) (hk : k < 6) :
    (nMinus1Low F).testBit k = nMinus1Bit F k := by
  unfold nMinus1Low nMinus1Bit
  exact testBit_mod_64 (formRN F - 1) k hk

/-- Horner exponent in leftover `T`/`H`.  On `m < 64` (leftover-narrow and
    leftover-wide `a < 2^64`) this is the live shift `m`, so `T = 2^m`.
    Wider leftovers keep the 6-bit match window. -/
noncomputable def leftoverHornerExp (F : Type*) [Field F] (m : ℕ) : ℕ :=
  if m < 64 then m
  else if nMinus1Low F ≤ m % 64 then nMinus1Low F else m

/-- `p`/`top` match: on `m < 64` only when `N = m` (Horner agrees with
    bit-matched `[m = n−1]`); wider leftovers use `N ≤ m % 64`. -/
noncomputable def leftoverMatch (F : Type*) [Field F] (m : ℕ) : Prop :=
  if m < 64 then nMinus1Low F = m else nMinus1Low F ≤ m % 64

noncomputable instance leftoverMatch.decidable (m : ℕ) :
    Decidable (leftoverMatch (F := F) m) := by
  unfold leftoverMatch
  infer_instance

theorem leftoverHornerExp_of_lt {m : ℕ} (hm : m < 64) :
    leftoverHornerExp (F := F) m = m := if_pos hm

/-- A wide Horner exponent is the raw shift, so its low 6 bits sit strictly
below `n−1` (the `N ≤ m % 64` arm returns `N` itself, which is `< 64`). -/
theorem leftoverHornerExp_wide_mod_lt {m : ℕ}
    (h : 64 ≤ leftoverHornerExp (F := F) m) :
    leftoverHornerExp (F := F) m % 64 < nMinus1Low F := by
  by_cases hm : m < 64
  · have he : leftoverHornerExp (F := F) m = m := leftoverHornerExp_of_lt (F := F) hm
    omega
  · by_cases hle : nMinus1Low F ≤ m % 64
    · have he : leftoverHornerExp (F := F) m = nMinus1Low F := by
        simp [leftoverHornerExp, hm, hle]
      have hN : nMinus1Low F < 64 := Nat.mod_lt _ (by decide)
      omega
    · have he : leftoverHornerExp (F := F) m = m := by
        simp [leftoverHornerExp, hm, hle]
      rw [he]
      exact Nat.lt_of_not_ge hle

/-- Exponent written into the 6 shift bits, `H` and `T`.
    Leftover-narrow (`m < 64`) writes the live Horner exponent so
    `T = 2^m` reconstructs the limb.  Wider leftovers still snap to
    `n−1` when the 6-bit window is strictly below `n−1`. -/
noncomputable def rangeShiftExp (F : Type*) [Field F] (m : ℕ) : ℕ :=
  let e := leftoverHornerExp F m
  if m < 64 then e
  else if e % 64 < nMinus1Low F then nMinus1Low F else e

theorem rangeShiftExp_of_lt64 {m : ℕ} (hm : m < 64) :
    rangeShiftExp (F := F) m = leftoverHornerExp (F := F) m := by
  simp [rangeShiftExp, hm]

theorem rangeShiftExp_of_mod_lt {m : ℕ}
    (h : leftoverHornerExp (F := F) m % 64 < nMinus1Low F) :
    rangeShiftExp (F := F) m =
      if m < 64 then leftoverHornerExp (F := F) m else nMinus1Low F := by
  simp [rangeShiftExp, h]

theorem rangeShiftExp_eq_horner_of_mod_ge {m : ℕ}
    (h : ¬ leftoverHornerExp (F := F) m % 64 < nMinus1Low F) :
    rangeShiftExp (F := F) m = leftoverHornerExp (F := F) m := by
  simp [rangeShiftExp, h]

theorem rangeShiftExp_lt_64 (m : ℕ) : rangeShiftExp (F := F) m < 64 := by
  by_cases hm : m < 64
  · rw [rangeShiftExp_of_lt64 (F := F) hm, leftoverHornerExp_of_lt (F := F) hm]
    exact hm
  · by_cases h : leftoverHornerExp (F := F) m % 64 < nMinus1Low F
    · rw [rangeShiftExp_of_mod_lt (F := F) h, if_neg hm]
      exact Nat.mod_lt _ (by decide)
    · rw [rangeShiftExp_eq_horner_of_mod_ge (F := F) h]
      by_contra hge
      exact h (leftoverHornerExp_wide_mod_lt (F := F) (Nat.le_of_not_lt hge))

theorem leftoverMatch_of_lt {m : ℕ} (hm : m < 64) :
    leftoverMatch (F := F) m ↔ nMinus1Low F = m := by
  simp [leftoverMatch, hm]

/-- Leftover-match at `n ≤ 64` is the full window `m = n−1`. -/
theorem leftoverMatch_eq_nMinus1_of_le64 (hchar : ringChar F ≠ 0) {m : ℕ}
    (hm : leftoverMatch (F := F) m) (hm64 : m < 64)
    (hle : formRN F ≤ 64) :
    m = formRN F - 1 := by
  have hN : nMinus1Low F = m := (leftoverMatch_of_lt (F := F) hm64).mp hm
  have hn1 : 1 ≤ formRN F :=
    Nat.one_le_of_lt (Nat.size_pos.mpr (Nat.pos_of_ne_zero hchar))
  have hmod : nMinus1Low F = formRN F - 1 :=
    Nat.mod_eq_of_lt (by omega)
  exact hN.symm.trans hmod

/-- `leftoverMatch` is the Horner-window equality `leftoverHornerExp = N`. -/
theorem leftoverMatch_iff_horner (m : ℕ) :
    leftoverMatch (F := F) m ↔
      leftoverHornerExp (F := F) m = nMinus1Low F := by
  by_cases hm : m < 64
  · rw [leftoverMatch_of_lt (F := F) hm, leftoverHornerExp_of_lt (F := F) hm]
    exact eq_comm
  · have hN : nMinus1Low F < 64 := Nat.mod_lt _ (by decide)
    have hmge : 64 ≤ m := Nat.le_of_not_lt hm
    constructor
    · intro hwin
      have : nMinus1Low F ≤ m % 64 := by
        simpa [leftoverMatch, hm] using hwin
      simp [leftoverHornerExp, hm, this]
    · intro heq
      by_cases hle : nMinus1Low F ≤ m % 64
      · simpa [leftoverMatch, hm] using hle
      · have hexp : leftoverHornerExp (F := F) m = m := by
          simp [leftoverHornerExp, hm, hle]
        have : m = nMinus1Low F := hexp.symm.trans heq
        omega

theorem rangeShiftExp_of_match {m : ℕ} (h : leftoverMatch (F := F) m) :
    rangeShiftExp (F := F) m = nMinus1Low F := by
  have he : leftoverHornerExp (F := F) m = nMinus1Low F :=
    (leftoverMatch_iff_horner (F := F) m).mp h
  have hmod : leftoverHornerExp (F := F) m % 64 = nMinus1Low F := by
    rw [he]
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
  have hnot : ¬ leftoverHornerExp (F := F) m % 64 < nMinus1Low F := by
    rw [hmod]
    exact Nat.lt_irrefl _
  rw [rangeShiftExp_eq_horner_of_mod_ge (F := F) hnot, he]

theorem rangeShiftExp_testBit_nMinus1_of_mod_lt {m k : ℕ}
    (hm : ¬ m < 64)
    (h : leftoverHornerExp (F := F) m % 64 < nMinus1Low F) (hk : k < 6) :
    (rangeShiftExp (F := F) m).testBit k = nMinus1Bit F k := by
  rw [rangeShiftExp_of_mod_lt (F := F) h, if_neg hm, nMinus1Low_testBit (F := F) k hk]

theorem rangeShiftExp_testBit_nMinus1_of_match {m k : ℕ}
    (h : leftoverMatch (F := F) m) (hk : k < 6) :
    (rangeShiftExp (F := F) m).testBit k = nMinus1Bit F k := by
  rw [rangeShiftExp_of_match (F := F) h, nMinus1Low_testBit (F := F) k hk]

/-- Unmatched leftover: either the 6-bit Horner window is strictly below `N`,
    or `N < leftoverHornerExp` (leftover-narrow `m < 64`, or leftover-wide
    `leftoverHornerExp ≥ 64`).  Do not claim `m % 64 < N` on the second side. -/
theorem leftoverMatch_neg_range_cmp {m : ℕ}
    (hne : ¬ leftoverMatch (F := F) m) :
    leftoverHornerExp (F := F) m % 64 < nMinus1Low F ∨
      nMinus1Low F < leftoverHornerExp (F := F) m := by
  have hne' : leftoverHornerExp (F := F) m ≠ nMinus1Low F :=
    mt (leftoverMatch_iff_horner (F := F) m).mpr hne
  by_cases hm64e : leftoverHornerExp (F := F) m < 64
  · have hexp : leftoverHornerExp (F := F) m % 64 =
        leftoverHornerExp (F := F) m := Nat.mod_eq_of_lt hm64e
    rcases Nat.lt_or_gt_of_ne hne' with hlt | hgt
    · exact Or.inl (hexp.symm ▸ hlt)
    · exact Or.inr hgt
  · -- leftover-wide unmatched: `leftoverHornerExp ≥ 64 > N`.
    have hNlt : nMinus1Low F < 64 := Nat.mod_lt _ (by decide)
    have hmge : 64 ≤ leftoverHornerExp (F := F) m :=
      Nat.le_of_not_lt hm64e
    exact Or.inr (hNlt.trans_le hmge)

/-- Unmatched leftover with `N < leftoverHornerExp < 64`.
    Bit-matched `top` of `n−1` is `1` (`rangeGate_eval_of_gt_top1`). -/
noncomputable def leftoverGtTop (F : Type*) [Field F] (m : ℕ) : Prop :=
  leftoverHornerExp (F := F) m < 64 ∧
    nMinus1Low F < leftoverHornerExp (F := F) m

noncomputable instance leftoverGtTop.decidable (m : ℕ) :
    Decidable (leftoverGtTop (F := F) m) := by
  unfold leftoverGtTop
  infer_instance

/-- Bit-matched `top`: `1` on leftover-match, leftover-gt, and leftover-wide
    dummy snap; `0` on leftover-narrow unmatched (`m < 64`) so
    `rangeGate_eval_of_lt` applies. -/
noncomputable def leftoverBitMatchedTop (F : Type*) [Field F] (m : ℕ) : F :=
  if leftoverMatch (F := F) m then 1
  else if leftoverGtTop (F := F) m then 1
  else if m < 64 then 0
  else 1

/-- Helpers run on leftover-match / leftover-gt / leftover-wide (`top = 1`).
    Leftover-narrow unmatched writes `0` so comparison is `of_top0`. -/
noncomputable def leftoverHelperMask (F : Type*) [Field F] (m : ℕ) : F :=
  if leftoverMatch (F := F) m then 1
  else if leftoverGtTop (F := F) m then 1
  else if m < 64 then 0
  else 1

theorem matchedLm_nMinus1 (k : ℕ) (hk : k < 6) :
    matchedLm F (nMinus1Low F) k = 1 :=
  matchedLm_of_eq (nMinus1Low F) k (nMinus1Low_testBit (F := F) k hk)

theorem matchedP_nMinus1 : matchedP F (nMinus1Low F) = 1 := by
  simp [matchedP, matchedLm_nMinus1 (F := F) 5 (by decide),
    matchedLm_nMinus1 (F := F) 4 (by decide),
    matchedLm_nMinus1 (F := F) 3 (by decide)]

theorem matchedP_rangeShiftExp_of_mod_lt {m : ℕ}
    (hm : ¬ m < 64)
    (h : leftoverHornerExp (F := F) m % 64 < nMinus1Low F) :
    matchedP F (rangeShiftExp (F := F) m) = 1 := by
  rw [rangeShiftExp_of_mod_lt (F := F) h, if_neg hm, matchedP_nMinus1]

theorem matchedP_rangeShiftExp_of_match {m : ℕ}
    (h : leftoverMatch (F := F) m) :
    matchedP F (rangeShiftExp (F := F) m) = 1 := by
  rw [rangeShiftExp_of_match (F := F) h, matchedP_nMinus1]

theorem matchedTop_nMinus1 : matchedTop F (nMinus1Low F) = 1 := by
  simp [matchedTop, matchedP_nMinus1 (F := F),
    matchedLm_nMinus1 (F := F) 2 (by decide),
    matchedLm_nMinus1 (F := F) 1 (by decide),
    matchedLm_nMinus1 (F := F) 0 (by decide)]

theorem leftoverGtTop_top {m : ℕ} (_h : leftoverGtTop (F := F) m) :
    matchedTop F (nMinus1Low F) = 1 :=
  matchedTop_nMinus1 (F := F)

theorem leftoverBitMatchedTop_of_match {m : ℕ}
    (heq : leftoverMatch (F := F) m) :
    leftoverBitMatchedTop (F := F) m = 1 := by
  simp [leftoverBitMatchedTop, heq]

theorem leftoverBitMatchedTop_nMinus1 :
    leftoverBitMatchedTop (F := F) (nMinus1Low F) = 1 := by
  have h : leftoverMatch (F := F) (nMinus1Low F) := by
    have hm : nMinus1Low F < 64 := Nat.mod_lt _ (by decide)
    exact (leftoverMatch_of_lt (F := F) hm).mpr rfl
  exact leftoverBitMatchedTop_of_match (F := F) h

theorem leftoverBitMatchedTop_of_gt {m : ℕ}
    (hne : ¬ leftoverMatch (F := F) m) (hgt : leftoverGtTop (F := F) m) :
    leftoverBitMatchedTop (F := F) m = 1 := by
  simp [leftoverBitMatchedTop, hne, hgt]

theorem leftoverBitMatchedTop_of_lt {m : ℕ}
    (hne : ¬ leftoverMatch (F := F) m) (hgt : ¬ leftoverGtTop (F := F) m)
    (hm : m < 64) :
    leftoverBitMatchedTop (F := F) m = 0 := by
  simp [leftoverBitMatchedTop, hne, hgt, hm]

theorem leftoverBitMatchedTop_of_wide {m : ℕ}
    (hne : ¬ leftoverMatch (F := F) m) (hgt : ¬ leftoverGtTop (F := F) m)
    (hm : ¬ m < 64) :
    leftoverBitMatchedTop (F := F) m = 1 := by
  simp [leftoverBitMatchedTop, hne, hgt, hm]

theorem leftoverHelperMask_of_match {m : ℕ}
    (heq : leftoverMatch (F := F) m) :
    leftoverHelperMask (F := F) m = 1 := by
  simp [leftoverHelperMask, heq]

theorem leftoverGtTop_not_match {m : ℕ} (h : leftoverGtTop (F := F) m) :
    ¬ leftoverMatch (F := F) m := by
  intro hm
  have he : leftoverHornerExp (F := F) m = nMinus1Low F :=
    (leftoverMatch_iff_horner (F := F) m).mp hm
  have : nMinus1Low F < leftoverHornerExp (F := F) m := h.2
  exact (he ▸ this).false

theorem leftoverHelperMask_of_gt {m : ℕ}
    (hgt : leftoverGtTop (F := F) m) :
    leftoverHelperMask (F := F) m = 1 := by
  simp [leftoverHelperMask, leftoverGtTop_not_match (F := F) hgt, hgt]

theorem leftoverHelperMask_of_off {m : ℕ}
    (hne : ¬ leftoverMatch (F := F) m) (hgt : ¬ leftoverGtTop (F := F) m)
    (hm : m < 64) :
    leftoverHelperMask (F := F) m = 0 := by
  simp [leftoverHelperMask, hne, hgt, hm]

theorem leftoverHelperMask_of_wide {m : ℕ}
    (hne : ¬ leftoverMatch (F := F) m) (hgt : ¬ leftoverGtTop (F := F) m)
    (hm : ¬ m < 64) :
    leftoverHelperMask (F := F) m = 1 := by
  simp [leftoverHelperMask, hne, hgt, hm]

theorem matchedLm_of_allBits (m k : ℕ)
    (h : nMinus1Bit F k = true) :
    matchedLm F m k = bit01 (m.testBit k) := by
  simp [matchedLm, h]

theorem matchedP_of_allBits (m : ℕ)
    (h : ∀ k, k < 6 → nMinus1Bit F k = true) :
    matchedP F m =
      bit01 (m.testBit 5) * bit01 (m.testBit 4) * bit01 (m.testBit 3) := by
  simp [matchedP, matchedLm_of_allBits m 5 (h 5 (by decide)),
    matchedLm_of_allBits m 4 (h 4 (by decide)),
    matchedLm_of_allBits m 3 (h 3 (by decide))]

theorem matchedTop_of_allBits (m : ℕ)
    (h : ∀ k, k < 6 → nMinus1Bit F k = true) :
    matchedTop F m =
      bit01 (m.testBit 5) * bit01 (m.testBit 4) * bit01 (m.testBit 3) *
        bit01 (m.testBit 2) * bit01 (m.testBit 1) * bit01 (m.testBit 0) := by
  simp [matchedTop, matchedP_of_allBits m h,
    matchedLm_of_allBits m 2 (h 2 (by decide)),
    matchedLm_of_allBits m 1 (h 1 (by decide)),
    matchedLm_of_allBits m 0 (h 0 (by decide))]

theorem matchedLm_eq_one_iff (m k : ℕ) :
    matchedLm F m k = 1 ↔ m.testBit k = nMinus1Bit F k := by
  unfold matchedLm
  cases hn : nMinus1Bit F k <;> cases hm : m.testBit k <;> simp [hn, hm]

theorem matchedP_eq_one_of_eq (m : ℕ)
    (h : ∀ k, k < 6 → m.testBit k = nMinus1Bit F k) :
    matchedP F m = 1 := by
  simp [matchedP,
    matchedLm_of_eq m 5 (h 5 (by decide)),
    matchedLm_of_eq m 4 (h 4 (by decide)),
    matchedLm_of_eq m 3 (h 3 (by decide))]

theorem matchedTop_eq_one_of_eq (m : ℕ)
    (h : ∀ k, k < 6 → m.testBit k = nMinus1Bit F k) :
    matchedTop F m = 1 := by
  simp [matchedTop, matchedP,
    matchedLm_of_eq m 5 (h 5 (by decide)),
    matchedLm_of_eq m 4 (h 4 (by decide)),
    matchedLm_of_eq m 3 (h 3 (by decide)),
    matchedLm_of_eq m 2 (h 2 (by decide)),
    matchedLm_of_eq m 1 (h 1 (by decide)),
    matchedLm_of_eq m 0 (h 0 (by decide))]

theorem matchedLm_zero_or_one (m k : ℕ) :
    matchedLm F m k = 0 ∨ matchedLm F m k = 1 := by
  unfold matchedLm
  cases nMinus1Bit F k <;> cases m.testBit k <;> simp

theorem matchedTop_eq_zero_of_ne (m : ℕ)
    (h : ¬ ∀ k, k < 6 → m.testBit k = nMinus1Bit F k) :
    matchedTop F m = 0 := by
  have ⟨k, hk, hne⟩ : ∃ k, k < 6 ∧ m.testBit k ≠ nMinus1Bit F k := by
    simpa [not_forall] using h
  have hz : matchedLm F m k = 0 := by
    have : ¬ matchedLm F m k = 1 := fun h1 =>
      hne ((matchedLm_eq_one_iff (F := F) m k).mp h1)
    rcases matchedLm_zero_or_one (F := F) m k with h0 | h1
    · exact h0
    · exact (this h1).elim
  have hmul0 {x y : F} (hx : x = 0 ∨ x = 1) (hy : y = 0) : x * y = 0 := by
    rcases hx with hx | hx <;> simp [hx, hy]
  have h01 := fun j => matchedLm_zero_or_one (F := F) m j
  interval_cases k <;> simp [matchedTop, matchedP, hz]

theorem lm_eval (env : Env F) (k : ℕ) :
    (lm (F := F) k).eval env =
      if nMinus1Bit F k then env.trace (col0 + 63 + k)
      else 1 - env.trace (col0 + 63 + k) := by
  simp [lm, colM, bcur, CoeffExpr.eval]
  split_ifs <;> rfl

/-- Dummy-window range: `m` bits are `n−1`, so `top = 1` and every range
    term vanishes.  Parametric in `n`; does not assume Goldilocks `64`. -/
theorem rangeGate_eval_of_eq_nMinus1 (env : Env F)
    (hM : ∀ k, k < 6 → env.trace (col0 + 63 + k) = bit01 (nMinus1Bit F k))
    (hP : env.trace (col0 + 71) = 1)
    (hTop : env.trace (col0 + 72) = 1) :
    (rangeGate (F := F)).eval env = 0 := by
  have hterm (k : ℕ) (hk : k < 6) : (rangeTerm (F := F) k).eval env = 0 := by
    have hm : env.trace (col0 + 63 + k) = bit01 (nMinus1Bit F k) := hM k hk
    by_cases hn : nMinus1Bit F k
    · have hb : env.trace (col0 + 63 + k) = 1 := by simp [hm, hn]
      simp [rangeTerm, CoeffExpr.eval, colM, bcur, hb, hn]
    · simp [rangeTerm, CoeffExpr.eval, colM, bcur, hn]
  have hsum : (sumExpr (rangeTerms (F := F))).eval env = 0 := by
    refine sumExpr_eval_zero _ env ?_
    intro t ht
    simp only [rangeTerms, List.mem_map, List.mem_range] at ht
    obtain ⟨k, hk, rfl⟩ := ht
    exact hterm k hk
  simp [rangeGate, CoeffExpr.eval, colTop, bcur, hTop, hsum]

/-- At `n = 64` the six low bits of `n − 1 = 63` are set. -/
theorem nMinus1Bit_of_formRN64 (h : formRN F = 64) :
    ∀ k, k < 6 → nMinus1Bit F k = true := by
  intro k hk
  have h63 : (63 : ℕ).testBit k = true := by
    have hbit : (2 ^ 6 - 1).testBit k = decide (k < 6) :=
      Nat.testBit_two_pow_sub_one (n := 6) k
    have hdec : decide (k < 6) = true := decide_eq_true hk
    have hpow : (2 : ℕ) ^ 6 - 1 = 63 := by decide
    rw [hpow] at hbit
    exact hbit.trans hdec
  unfold nMinus1Bit
  have h63' : formRN F - 1 = 63 := by rw [h]
  simpa [h63'] using h63

/-- Shift of the natural certificate of a positive integer: `Nat.size a - 1`. -/
def certShift (a : ℕ) : ℕ := Nat.size a - 1

/-- Lower bits of `a`, MSB first.  Index `j ≥ certShift a` is zero. -/
def certCBit (a j : ℕ) : Bool :=
  if j < certShift a then a.testBit (certShift a - 1 - j) else false

/-- Live leftover `C[0] = 1` forces a positive certificate. -/
theorem certCBit_zero_true_pos {a : ℕ} (h : certCBit a 0 = true) : 0 < a := by
  by_contra ha0
  have ha : a = 0 := Nat.eq_zero_of_not_pos ha0
  have hz : certCBit a 0 = false := by
    simp [certCBit, certShift, ha, Nat.size_zero]
  exact Bool.false_ne_true (hz.symm.trans h)

noncomputable def certLin (a j : ℕ) : F :=
  if pBit F (formRN F - 2 - j) then bit01 (certCBit a j) else (1 : F) - bit01 (certCBit a j)

/-- Prefix product of leftover `lin`, seeded by `1` (`top` on an `m = n−1` row). -/
noncomputable def certEqRun (a : ℕ) : ℕ → F
  | 0 => (1 : F)
  | n + 1 => certEqRun a n * certLin a n

/-- Top-seeded leftover comparison accumulator. -/
noncomputable def certLt (a : ℕ) : ℕ → F
  | 0 => (0 : F)
  | n + 1 =>
      certLt a n +
        certEqRun a n * (if (decide (n + 1 < formRN F) && pBit F (formRN F - 2 - n)) = true
          then (1 : F) - bit01 (certCBit a n) else 0)

theorem linCol_eval_cert (env : Env F) (a j : ℕ)
    (hC : env.trace (col0 + j) = bit01 (certCBit a j)) :
    (linCol (F := F) j).eval env = certLin a j := by
  unfold linCol certLin
  split_ifs with hp
  · simpa [colC, bcur, CoeffExpr.eval] using hC
  · have hc : env.trace (col0 + j) = bit01 (certCBit a j) := hC
    simp [colC, bcur, CoeffExpr.eval, hc]

theorem certEqRun_add3 (a n : ℕ) :
    certEqRun a (n + 3) =
      (((certEqRun a n : F) * (certLin a n : F) : F) * (certLin a (n + 1) : F) : F) *
        (certLin a (n + 2) : F) := by
  rw [show n + 3 = n + 2 + 1 by omega, certEqRun]
  rw [show n + 2 = n + 1 + 1 by omega, certEqRun]
  rw [certEqRun]

theorem helperAt_eval_of_certRun (env : Env F) (a : ℕ)
    (hTop : env.trace (col0 + 72) = 1)
    (hE : ∀ k, k < 21 → env.trace (col0 + 73 + k) = certEqRun a (3 * (k + 1)))
    (k : ℕ) (hk : k ≤ 21) :
    (helperAt (F := F) k).eval env = certEqRun a (3 * k) := by
  unfold helperAt
  by_cases hk0 : k = 0
  · simp [hk0, certEqRun, colTop, bcur, CoeffExpr.eval, hTop]
  · rw [if_neg hk0]
    have hk' : k - 1 < 21 := by omega
    have hE' := hE (k - 1) hk'
    have hidx : 3 * ((k - 1) + 1) = 3 * k := by omega
    simpa [colE, bcur, CoeffExpr.eval, hidx] using hE'

theorem helperPinAt_eval_of_certRun (env : Env F) (a : ℕ)
    (hTop : env.trace (col0 + 72) = 1)
    (hC : ∀ j, j < 63 → env.trace (col0 + j) = bit01 (certCBit a j))
    (hE : ∀ k, k < 21 → env.trace (col0 + 73 + k) = certEqRun a (3 * (k + 1)))
    (k : ℕ) (hk : k < 21) :
    (helperPinAt (F := F) k).eval env = 0 := by
  have hEk : env.trace (col0 + 73 + k) = certEqRun a (3 * (k + 1)) := hE k hk
  have hAt : (helperAt (F := F) k).eval env = certEqRun a (3 * k) :=
    helperAt_eval_of_certRun env a hTop hE k (by omega)
  have hlin0 : (linCol (F := F) (3 * k)).eval env = certLin a (3 * k) :=
    linCol_eval_cert env a (3 * k) (hC _ (by omega))
  have hlin1 : (linCol (F := F) (3 * k + 1)).eval env = certLin a (3 * k + 1) :=
    linCol_eval_cert env a (3 * k + 1) (hC _ (by omega))
  have hlin2 : (linCol (F := F) (3 * k + 2)).eval env = certLin a (3 * k + 2) :=
    linCol_eval_cert env a (3 * k + 2) (hC _ (by omega))
  have hprod :
      certEqRun a (3 * (k + 1)) =
        (((certEqRun a (3 * k) : F) * (certLin a (3 * k) : F) : F) *
            (certLin a (3 * k + 1) : F) : F) *
          (certLin a (3 * k + 2) : F) := by
    rw [show 3 * (k + 1) = 3 * k + 3 by omega]
    exact certEqRun_add3 a (3 * k)
  simp only [helperPinAt, CoeffExpr.eval, colE, bcur]
  rw [hEk, hAt, hlin0, hlin1, hlin2, ← hprod, sub_self]

theorem termAt_eval_of_certRun (env : Env F) (a k : ℕ)
    (hTop : env.trace (col0 + 72) = 1)
    (hC : ∀ j, j < 63 → env.trace (col0 + j) = bit01 (certCBit a j))
    (hE : ∀ t, t < 21 → env.trace (col0 + 73 + t) = certEqRun a (3 * (t + 1)))
    (hk : k < 63) :
    (termAt (F := F) k).eval env = certEqRun a k * ((1 : F) - bit01 (certCBit a k)) := by
  have hAt : (helperAt (F := F) (k / 3)).eval env = certEqRun a (3 * (k / 3)) :=
    helperAt_eval_of_certRun env a hTop hE (k / 3) (by omega)
  have hc : env.trace (col0 + k) = bit01 (certCBit a k) := hC k hk
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · simp only [termAt, h0, List.range_zero, List.map_nil, foldMul, CoeffExpr.eval, colC, bcur]
    have hdiv : 3 * (k / 3) = k := by omega
    rw [hAt, hc, hdiv]
  · have hlin0 : (linCol (F := F) (k - 1)).eval env = certLin a (k - 1) :=
      linCol_eval_cert env a (k - 1) (hC _ (by omega))
    have heq : certEqRun a k =
        (certEqRun a (3 * (k / 3)) : F) * (certLin a (k - 1) : F) := by
      conv_lhs => rw [show k = 3 * (k / 3) + 1 by omega]
      rw [certEqRun, show 3 * (k / 3) = k - 1 by omega]
    have hr1 : List.range (k % 3) = [0] := by
      simp [h1, List.range_succ, List.range_zero]
    simp only [termAt, hr1, List.map_cons, List.map_nil, foldMul, CoeffExpr.eval, colC, bcur]
    rw [show k - k % 3 + 0 = k - 1 by omega]
    rw [hAt, hlin0, hc, ← heq]
  · have hlin0 : (linCol (F := F) (k - 2)).eval env = certLin a (k - 2) :=
      linCol_eval_cert env a (k - 2) (hC _ (by omega))
    have hlin1 : (linCol (F := F) (k - 1)).eval env = certLin a (k - 1) :=
      linCol_eval_cert env a (k - 1) (hC _ (by omega))
    have heq : certEqRun a k =
        ((certEqRun a (3 * (k / 3)) : F) * (certLin a (k - 2) : F) : F) *
          (certLin a (k - 1) : F) := by
      conv_lhs => rw [show k = 3 * (k / 3) + 1 + 1 by omega]
      rw [certEqRun, certEqRun, show 3 * (k / 3) = k - 2 by omega,
        show k - 2 + 1 = k - 1 by omega]
    have hr2 : List.range (k % 3) = [0, 1] := by
      simp [h2, List.range_succ, List.range_zero, List.nil_append]
    simp only [termAt, hr2, List.map_cons, List.map_nil, foldMul, CoeffExpr.eval, colC, bcur]
    rw [show k - k % 3 + 0 = k - 2 by omega, show k - k % 3 + 1 = k - 1 by omega]
    rw [hAt, hlin0, hlin1, hc, ← heq]

theorem certLt_eq_sum (a : ℕ) :
    certLt a 63 =
      ∑ i ∈ Finset.range 63,
        certEqRun a i * (if (decide (i + 1 < formRN F) && pBit F (formRN F - 2 - i)) then (1 : F) - bit01 (certCBit a i) else 0) := by
  have h : ∀ n, n ≤ 63 →
      certLt a n =
        ∑ i ∈ Finset.range n,
          certEqRun a i * (if (decide (i + 1 < formRN F) && pBit F (formRN F - 2 - i)) then (1 : F) - bit01 (certCBit a i) else 0) := by
    intro n hn
    induction n with
    | zero => simp [certLt]
    | succ n ih =>
        rw [certLt, ih (Nat.le_of_succ_le hn), Finset.sum_range_succ]
  exact h 63 le_rfl

theorem comparisonGate_eval_of_certRun (env : Env F) (a : ℕ)
    (hTop : env.trace (col0 + 72) = 1)
    (hC : ∀ j, j < 63 → env.trace (col0 + j) = bit01 (certCBit a j))
    (hE : ∀ k, k < 21 → env.trace (col0 + 73 + k) = certEqRun a (3 * (k + 1)))
    (hlt : certLt a 63 = (1 : F)) :
    (comparisonGate (F := F)).eval env = 0 := by
  simp only [comparisonGate, CoeffExpr.eval, colTop, bcur, hTop, sub_eq_zero]
  let f : ℕ → F := fun i =>
    certEqRun a i * (if (decide (i + 1 < formRN F) && pBit F (formRN F - 2 - i)) then (1 : F) - bit01 (certCBit a i) else 0)
  have hlist : ∀ n, n ≤ 63 →
      (sumExpr ((List.range n).map fun k =>
          CoeffExpr.mul (bitCoeff ((decide (k + 1 < formRN F) && pBit F (formRN F - 2 - k)))) (termAt (F := F) k))).eval env =
        ∑ i ∈ Finset.range n, f i := by
    intro n hn
    induction n with
    | zero => simp [sumExpr, CoeffExpr.eval]
    | succ n ih =>
        rw [List.range_succ, List.map_append, List.map_singleton, sumExpr_append,
          ih (Nat.le_of_succ_le hn), Finset.sum_range_succ]
        have ht := termAt_eval_of_certRun env a n hTop hC hE (by omega)
        have hb : (bitCoeff ((decide (n + 1 < formRN F) && pBit F (formRN F - 2 - n)))).eval env =
            if (decide (n + 1 < formRN F) && pBit F (formRN F - 2 - n)) then (1 : F) else 0 := by
          cases (decide (n + 1 < formRN F) && pBit F (formRN F - 2 - n)) <;> simp [bitCoeff, CoeffExpr.eval]
        simp only [sumExpr, CoeffExpr.eval, add_zero]
        rw [hb, ht]
        cases hp : (decide (n + 1 < formRN F) && pBit F (formRN F - 2 - n))
        · simp only [f, hp]
          rw [if_neg (by decide : ¬ false = true), if_neg (by decide : ¬ false = true)]
          simp [zero_mul, mul_zero]
        · simp only [f, hp]
          rw [if_pos trivial, if_pos trivial]
          simp [one_mul]
  have hterms : (sumExpr (comparisonTerms (F := F))).eval env = certLt a 63 := by
    rw [comparisonTerms, certLt_eq_sum]
    exact hlist 63 le_rfl
  rw [hterms]
  exact hlt

theorem testBit_false_of_lt_64 {n i : ℕ} (hn : n < 64) (hi : ¬ i < 6) :
    n.testBit i = false := by
  have hge : 6 ≤ i := Nat.le_of_not_lt hi
  have hpow : n < 2 ^ i :=
    calc n < 64 := hn
      _ = 2 ^ 6 := by decide
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hge
  have hz : n / 2 ^ i = 0 := Nat.div_eq_of_lt hpow
  have hshift : n >>> i = 0 := by
    rw [Nat.shiftRight_eq_div_pow, hz]
  simp [Nat.testBit, hshift]

theorem eq_of_low6_testBit {m N : ℕ} (hm : m < 64) (hN : N < 64)
    (h : ∀ k, k < 6 → m.testBit k = N.testBit k) : m = N := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · exact h i hi
  · rw [testBit_false_of_lt_64 hm hi, testBit_false_of_lt_64 hN hi]

theorem certShift_of_pos (a : ℕ) (ha : 0 < a) : certShift a + 1 = Nat.size a := by
  have hpos : 0 < Nat.size a := Nat.size_pos.mpr ha
  simp [certShift, Nat.sub_add_cancel (Nat.one_le_of_lt hpos)]

theorem certShift_lt_63 (a : ℕ) (ha0 : 0 < a) (ha : a < 2 ^ 63) : certShift a < 63 := by
  have hsz : Nat.size a ≤ 63 := Nat.size_le.mpr ha
  have hpos : 1 ≤ Nat.size a := Nat.one_le_of_lt (Nat.size_pos.mpr ha0)
  simp only [certShift]
  omega

/-- `certShift a < n` as soon as `a < 2^n`, including `a = 0` (`n > 0`). -/
theorem certShift_lt_of_lt (a n : ℕ) (hn : 0 < n) (ha : a < 2 ^ n) :
    certShift a < n := by
  have hsz : Nat.size a ≤ n := Nat.size_le.mpr ha
  simp only [certShift]
  omega

theorem certShift_le_63_of_lt_64 (a : ℕ) (ha : a < 2 ^ 64) : certShift a ≤ 63 := by
  have hsz : Nat.size a ≤ 64 := Nat.size_le.mpr ha
  simp only [certShift]
  omega

theorem certShift_topBit (a : ℕ) (ha : 0 < a) : a.testBit (certShift a) = true := by
  simpa [certShift] using testBit_pred_size (n := a) (Nat.ne_of_gt ha)

/-- `2^n ≤ a < 2^{n+1}` sets bit `n`. -/
theorem testBit_of_mem_pow_window (a n : ℕ) (hlo : 2 ^ n ≤ a) (hhi : a < 2 ^ (n + 1)) :
    a.testBit n = true := by
  have hsz : Nat.size a = n + 1 := by
    have hle : Nat.size a ≤ n + 1 := Nat.size_le.mpr hhi
    have hgt : n < Nat.size a := (Nat.lt_size).mpr hlo
    omega
  have hpos : 0 < a := lt_of_lt_of_le (Nat.two_pow_pos n) hlo
  have : a.testBit (Nat.size a - 1) = true :=
    testBit_pred_size (n := a) (Nat.ne_of_gt hpos)
  simpa [hsz] using this

/-- Low bits of `a` agree with `a - 2^n` when `2^n ≤ a`. -/
theorem testBit_sub_pow (a n i : ℕ) (hle : 2 ^ n ≤ a) (hi : i < n) :
    a.testBit i = (a - 2 ^ n).testBit i := by
  have hadd : a = (a - 2 ^ n) + 2 ^ n := (Nat.sub_add_cancel hle).symm
  conv_lhs => rw [hadd, Nat.add_comm]
  rw [Nat.testBit_two_pow_add_gt hi]

/-- `a = 2^m +` its lower bits, `m = certShift a`. -/
theorem nat_eq_certBits (a : ℕ) (ha : 0 < a) :
    a = 2 ^ certShift a +
      ∑ i ∈ Finset.range (certShift a), (if a.testBit i then 2 ^ i else 0) := by
  have hlt : a < 2 ^ (certShift a + 1) := by
    simpa [certShift_of_pos a ha] using Nat.lt_size_self a
  have hsum := sum_testBit_pow (certShift a + 1) a hlt
  rw [Finset.sum_range_succ, certShift_topBit a ha] at hsum
  simpa [add_comm] using hsum.symm

/-- Product of `x^{2^i}` over the set bits of `m` below `n`. -/
def powBits (x : F) (m n : ℕ) : F :=
  (Finset.range n).prod fun i => if m.testBit i then x ^ 2 ^ i else 1

theorem testBit_succ_div (n i : ℕ) : n.testBit (i + 1) = (n / 2).testBit i :=
  Nat.testBit_add_one n i

theorem prod_bitPow_eq_pow (x : F) (n m : ℕ) (hm : m < 2 ^ n) :
    powBits x m n = x ^ m := by
  induction n generalizing m x with
  | zero =>
      simp only [pow_zero, Nat.lt_one_iff] at hm
      simp [powBits, hm]
  | succ n ih =>
      rw [powBits, Finset.prod_range_succ']
      have hdiv : m / 2 < 2 ^ n := by
        have hmul : m < 2 * 2 ^ n := by simpa [pow_succ, Nat.mul_comm] using hm
        exact Nat.div_lt_of_lt_mul hmul
      have htail :
          (Finset.range n).prod (fun i => if m.testBit (i + 1) then x ^ 2 ^ (i + 1) else (1 : F)) =
            powBits (x ^ 2) (m / 2) n := by
        rw [powBits]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [testBit_succ_div]
        by_cases hb : (m / 2).testBit i
        · have hexp : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ, Nat.mul_comm]
          simp [hb, hexp, pow_mul]
        · simp [hb]
      rw [htail, ih (x ^ 2) (m / 2) hdiv, ← pow_mul, Nat.mul_comm]
      rcases Nat.mod_two_eq_zero_or_one m with hmod | hmod
      · have hb0 : m.testBit 0 = false := by simp [Nat.testBit_zero, hmod]
        simp [hb0]
        rw [show m / 2 * 2 = m by omega]
      · have hb0 : m.testBit 0 = true := by simp [Nat.testBit_zero, hmod]
        simp only [hb0, ite_true, pow_zero, pow_one]
        rw [← pow_succ]
        rw [show m / 2 * 2 + 1 = m by omega]

theorem powBits_six_eq (x : F) (m : ℕ) (hm : m < 64) : powBits x m 6 = x ^ m := by
  have : m < 2 ^ 6 := by simpa using hm
  exact prod_bitPow_eq_pow x 6 m this

theorem powBits_three (x : F) (m : ℕ) :
    powBits x m 3 =
      (if m.testBit 0 then x ^ 2 ^ 0 else 1) *
      (if m.testBit 1 then x ^ 2 ^ 1 else 1) *
      (if m.testBit 2 then x ^ 2 ^ 2 else 1) := by
  simp [powBits, Finset.prod_range_succ]

theorem powBits_high (x : F) (m : ℕ) :
    powBits x m 6 = powBits x m 3 *
      (if m.testBit 3 then x ^ 2 ^ 3 else 1) *
      (if m.testBit 4 then x ^ 2 ^ 4 else 1) *
      (if m.testBit 5 then x ^ 2 ^ 5 else 1) := by
  simp [powBits, Finset.prod_range_succ]

theorem bit_prod_zero_of_shift_lt (a : ℕ) (hm : certShift a < 63) :
    bit01 (F := F) ((certShift a).testBit 5) * bit01 ((certShift a).testBit 4) *
        bit01 ((certShift a).testBit 3) * bit01 ((certShift a).testBit 2) *
        bit01 ((certShift a).testBit 1) * bit01 ((certShift a).testBit 0) = 0 := by
  have hm64 : certShift a < 64 := by omega
  by_contra hne
  have hbit : ∀ k, k < 6 → (certShift a).testBit k = true := by
    intro k hk
    by_contra hf
    have hz : bit01 (F := F) ((certShift a).testBit k) = 0 := by
      cases ht : (certShift a).testBit k
      · rfl
      · exact absurd ht hf
    interval_cases k
    · simp only [hz, mul_zero] at hne; exact hne trivial
    · simp only [hz, mul_zero, zero_mul] at hne; exact hne trivial
    · simp only [hz, mul_zero, zero_mul] at hne; exact hne trivial
    · simp only [hz, mul_zero, zero_mul] at hne; exact hne trivial
    · simp only [hz, mul_zero, zero_mul] at hne; exact hne trivial
    · simp only [hz, zero_mul] at hne; exact hne trivial
  have hsum := sum_testBit_pow 6 (certShift a) hm64
  have h63 : ∑ i ∈ Finset.range 6, (if (certShift a).testBit i then 2 ^ i else 0) = 63 := by
    simp [Finset.sum_range_succ, hbit 0 (by decide), hbit 1 (by decide), hbit 2 (by decide),
      hbit 3 (by decide), hbit 4 (by decide), hbit 5 (by decide)]
  rw [h63] at hsum
  omega

theorem bit_prod_zero_of_lt63 (a : ℕ) (ha0 : 0 < a) (ha : a < 2 ^ 63) :
    bit01 (F := F) ((certShift a).testBit 5) * bit01 ((certShift a).testBit 4) *
        bit01 ((certShift a).testBit 3) * bit01 ((certShift a).testBit 2) *
        bit01 ((certShift a).testBit 1) * bit01 ((certShift a).testBit 0) = 0 := by
  have hm : certShift a < 63 := certShift_lt_63 a ha0 ha
  exact bit_prod_zero_of_shift_lt (F := F) a hm

/-- Helpers vanish and `top = 0`, so every comparison term is zero. -/
theorem termAt_eval_of_top0 (env : Env F)
    (hTop : env.trace (col0 + 72) = 0)
    (hE : ∀ k, k < 21 → env.trace (col0 + 73 + k) = 0)
    (k : ℕ) (hk : k ≤ 63) : (termAt (F := F) k).eval env = 0 := by
  have hhead : (helperAt (F := F) (k / 3)).eval env = 0 := by
    by_cases hz : k / 3 = 0
    · simp [helperAt, hz, colTop, bcur, CoeffExpr.eval, hTop]
    · have hlt : k / 3 - 1 < 21 := by omega
      simp [helperAt, hz, colE, bcur, CoeffExpr.eval, hE _ hlt]
  unfold termAt
  simp only [CoeffExpr.eval]
  rw [foldMul_eval_of_zero _ _ env hhead]
  simp

theorem helperPinAt_eval_of_top0 (env : Env F)
    (hTop : env.trace (col0 + 72) = 0)
    (hE : ∀ k, k < 21 → env.trace (col0 + 73 + k) = 0)
    (k : ℕ) (hk : k < 21) : (helperPinAt (F := F) k).eval env = 0 := by
  have hEk : env.trace (col0 + 73 + k) = 0 := hE k hk
  simp only [helperPinAt, CoeffExpr.eval, colE, bcur, hEk, sub_eq_zero]
  by_cases hk0 : k = 0
  · subst k
    simp [helperAt, colTop, bcur, CoeffExpr.eval, hTop]
  · have hprev : env.trace (col0 + 73 + (k - 1)) = 0 := hE (k - 1) (by omega)
    simp [helperAt, hk0, colE, bcur, CoeffExpr.eval, hprev]

theorem comparisonGate_eval_of_top0 (env : Env F)
    (hTop : env.trace (col0 + 72) = 0)
    (hE : ∀ k, k < 21 → env.trace (col0 + 73 + k) = 0) :
    (comparisonGate (F := F)).eval env = 0 := by
  simp only [comparisonGate, CoeffExpr.eval, colTop, bcur, hTop, sub_eq_zero]
  refine sumExpr_eval_zero _ env ?_
  intro t ht
  simp only [comparisonTerms, List.mem_map, List.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  have hk' := termAt_eval_of_top0 env hTop hE k (by omega)
  simp [CoeffExpr.eval, hk']

/-- All six low bits of `n − 1` are set, so the range sum is the boolean telescope. -/
theorem rangeGate_eval_of_allBits (env : Env F)
    (hbits : ∀ k, k < 6 → nMinus1Bit F k = true)
    (b0 b1 b2 b3 b4 b5 : F)
    (h0 : env.trace (col0 + 63) = b0) (h1 : env.trace (col0 + 64) = b1)
    (h2 : env.trace (col0 + 65) = b2) (h3 : env.trace (col0 + 66) = b3)
    (h4 : env.trace (col0 + 67) = b4) (h5 : env.trace (col0 + 68) = b5)
    (hP : env.trace (col0 + 71) = b5 * b4 * b3)
    (hTop : env.trace (col0 + 72) = b5 * b4 * b3 * b2 * b1 * b0) :
    (rangeGate (F := F)).eval env = 0 := by
  have hterm (k : ℕ) (hk : k < 6) (e b : F)
      (he : (eqmAt (F := F) (k + 1)).eval env = e)
      (hb : env.trace (col0 + 63 + k) = b) :
      (rangeTerm (F := F) k).eval env = e * (1 - b) := by
    simp [rangeTerm, CoeffExpr.eval, colM, bcur, hb, he, hbits k hk]
  have hl (k : ℕ) (hk : k < 6) : (lm (F := F) k).eval env = env.trace (col0 + 63 + k) := by
    simp [lm, hbits k hk, colM, bcur, CoeffExpr.eval]
  have he1 : (eqmAt (F := F) 1).eval env = b5 * b4 * b3 * b2 * b1 := by
    simp [eqmAt, CoeffExpr.eval, colP, bcur, hP, hl 2 (by decide), hl 1 (by decide), h2, h1]
  have he2 : (eqmAt (F := F) 2).eval env = b5 * b4 * b3 * b2 := by
    simp [eqmAt, CoeffExpr.eval, colP, bcur, hP, hl 2 (by decide), h2]
  have he3 : (eqmAt (F := F) 3).eval env = b5 * b4 * b3 := by
    simp [eqmAt, CoeffExpr.eval, colP, bcur, hP]
  have he4 : (eqmAt (F := F) 4).eval env = b5 * b4 := by
    simp [eqmAt, CoeffExpr.eval, hl 5 (by decide), hl 4 (by decide), h5, h4]
  have he5 : (eqmAt (F := F) 5).eval env = b5 := by
    simp [eqmAt, CoeffExpr.eval, hl 5 (by decide), h5]
  have he6 : (eqmAt (F := F) 6).eval env = 1 := by
    simp [eqmAt, CoeffExpr.eval]
  have ht0 := hterm 0 (by decide) _ _ he1 h0
  have ht1 := hterm 1 (by decide) _ _ he2 h1
  have ht2 := hterm 2 (by decide) _ _ he3 h2
  have ht3 := hterm 3 (by decide) _ _ he4 h3
  have ht4 := hterm 4 (by decide) _ _ he5 h4
  have ht5 := hterm 5 (by decide) _ _ he6 h5
  have hlist : rangeTerms (F := F) =
      [rangeTerm 0, rangeTerm 1, rangeTerm 2, rangeTerm 3, rangeTerm 4, rangeTerm 5] := by
    simp [rangeTerms, List.range_succ, List.range_zero]
  simp only [rangeGate, CoeffExpr.eval, colTop, bcur, hTop, sub_eq_zero, hlist, sumExpr]
  rw [ht0, ht1, ht2, ht3, ht4, ht5]
  ring

theorem pow_csum_cert (env : Env F) (a : ℕ) (ha0 : 0 < a) (ha : a < 2 ^ 63)
    (h2 : (2 : F) ≠ 0)
    (hC : ∀ j, j < 63 →
      env.trace (col0 + j) = if certCBit a j then (1 : F) else 0) :
    (2 : F) ^ certShift a * (csum (F := F)).eval env = (a : F) := by
  set m := certShift a with hm
  have hm63 : m < 63 := by simpa [hm] using certShift_lt_63 a ha0 ha
  have htwo (k : ℕ) (hk : k ≤ m) :
      (2 : F) ^ m * twoInv ^ k = (2 : F) ^ (m - k) := by
    have hkpow : (2 : F) ^ k ≠ 0 := pow_ne_zero k h2
    have hn : (2 : F) ^ m = (2 : F) ^ (m - k) * (2 : F) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    calc (2 : F) ^ m * twoInv ^ k
        = (2 : F) ^ m * ((2 : F) ^ k)⁻¹ := by rw [twoInv, inv_pow]
      _ = ((2 : F) ^ (m - k) * (2 : F) ^ k) * ((2 : F) ^ k)⁻¹ := by rw [hn]
      _ = (2 : F) ^ (m - k) * ((2 : F) ^ k * ((2 : F) ^ k)⁻¹) := by ring
      _ = (2 : F) ^ (m - k) := by rw [mul_inv_cancel₀ hkpow, mul_one]
  have hacc : ∀ n, n ≤ 63 →
      (2 : F) ^ m * (csumAcc (F := F) n).eval env =
        (2 : F) ^ m +
          ∑ i ∈ Finset.range (min n m),
            (if a.testBit (m - 1 - i) then (2 : F) ^ (m - 1 - i) else 0) := by
    intro n hn
    induction n with
    | zero => simp [csumAcc, CoeffExpr.eval]
    | succ n ih =>
        have ihn := ih (Nat.le_of_succ_le hn)
        simp only [csumAcc, CoeffExpr.eval, colC, bcur]
        have hc := hC n (by omega)
        by_cases hnm : n < m
        · have hbit : certCBit a n = a.testBit (m - 1 - n) := by
            have hlt : n < certShift a := by simpa [hm] using hnm
            simp [certCBit, hlt, hm]
          rw [hc, hbit]
          have hadd := htwo (n + 1) (by omega)
          have hexp : m - (n + 1) = m - 1 - n := by omega
          calc (2 : F) ^ m *
                ((csumAcc (F := F) n).eval env +
                  (if a.testBit (m - 1 - n) then (1 : F) else 0) * twoInv ^ (n + 1))
              = (2 : F) ^ m * (csumAcc (F := F) n).eval env +
                  (if a.testBit (m - 1 - n) then (1 : F) else 0) *
                    ((2 : F) ^ m * twoInv ^ (n + 1)) := by ring
            _ = (2 : F) ^ m +
                  ∑ i ∈ Finset.range (min n m),
                    (if a.testBit (m - 1 - i) then (2 : F) ^ (m - 1 - i) else 0) +
                  (if a.testBit (m - 1 - n) then (2 : F) ^ (m - 1 - n) else 0) := by
                    rw [ihn, hadd, hexp]
                    by_cases hb : a.testBit (m - 1 - n) <;> simp [hb]
            _ = (2 : F) ^ m +
                  ∑ i ∈ Finset.range (min (n + 1) m),
                    (if a.testBit (m - 1 - i) then (2 : F) ^ (m - 1 - i) else 0) := by
                  have hmin : min n m = n := min_eq_left (Nat.le_of_lt hnm)
                  have hmin' : min (n + 1) m = n + 1 := min_eq_left hnm
                  rw [hmin, hmin', Finset.sum_range_succ]
                  ring
        · have hge : m ≤ n := by omega
          have hc0 : certCBit a n = false := by
            have hge' : ¬ n < certShift a := by simpa [hm] using hnm
            simp [certCBit, hge']
          rw [hc, hc0]
          have hmin : min n m = m := min_eq_right hge
          have hmin' : min (n + 1) m = m := min_eq_right (Nat.le_trans hge (Nat.le_succ n))
          simp [ihn, hmin, hmin']
  have h63 := hacc 63 (by omega)
  have hmin : min 63 m = m := min_eq_right (Nat.le_of_lt hm63)
  rw [hmin] at h63
  have hreidx :
      ∑ i ∈ Finset.range m, (if a.testBit (m - 1 - i) then (2 : F) ^ (m - 1 - i) else 0) =
        ∑ i ∈ Finset.range m, (if a.testBit i then (2 : F) ^ i else 0) := by
    refine Finset.sum_nbij' (fun i => m - 1 - i) (fun j => m - 1 - j) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro i hi
      rfl
  have hcast :
      (2 : F) ^ m + ∑ i ∈ Finset.range m, (if a.testBit i then (2 : F) ^ i else 0) = (a : F) := by
    have hnat := nat_eq_certBits a ha0
    rw [← hm] at hnat
    conv_rhs => rw [hnat]
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_sum]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    by_cases hb : a.testBit i <;> simp [hb, Nat.cast_pow]
  simpa [csum, hreidx, hcast] using h63

/-- MSB-first 63-bit value of a bit stream. -/
def msbVal (b : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range 63, if b i then 2 ^ (62 - i) else 0

theorem sum_range_pow_two (n : ℕ) :
    ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      omega

theorem msbVal_split (b : ℕ → Bool) (k : ℕ) (hk : k < 63) :
    msbVal b =
      ∑ i ∈ Finset.range k, (if b i then 2 ^ (62 - i) else 0) +
        (if b k then 2 ^ (62 - k) else 0) +
        ∑ i ∈ Finset.Ico (k + 1) 63, (if b i then 2 ^ (62 - i) else 0) := by
  have hunion : Finset.range 63 = Finset.range (k + 1) ∪ Finset.Ico (k + 1) 63 := by
    ext x
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range (k + 1)) (Finset.Ico (k + 1) 63) := by
    refine Finset.disjoint_left.2 ?_
    intro x hx hx'
    simp only [Finset.mem_range, Finset.mem_Ico] at hx hx'
    omega
  unfold msbVal
  rw [hunion, Finset.sum_union hdisj, Finset.sum_range_succ]

theorem msbVal_prefix_eq (bC bP : ℕ → Bool) (k : ℕ)
    (h : ∀ i < k, bC i = bP i) :
    ∑ i ∈ Finset.range k, (if bC i then 2 ^ (62 - i) else 0) =
      ∑ i ∈ Finset.range k, (if bP i then 2 ^ (62 - i) else 0) := by
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < k := Finset.mem_range.mp hi
  rw [h i hi']

theorem msbVal_tail_lt (b : ℕ → Bool) (k : ℕ) (hk : k < 63) :
    ∑ i ∈ Finset.Ico (k + 1) 63, (if b i then 2 ^ (62 - i) else 0) < 2 ^ (62 - k) := by
  have hle :
      ∑ i ∈ Finset.Ico (k + 1) 63, (if b i then 2 ^ (62 - i) else 0) ≤
        ∑ i ∈ Finset.Ico (k + 1) 63, 2 ^ (62 - i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs <;> simp
  have hgeom :
      ∑ i ∈ Finset.Ico (k + 1) 63, 2 ^ (62 - i) = 2 ^ (62 - k) - 1 := by
    have hbij :
        (∑ i ∈ Finset.Ico (k + 1) 63, (2 : ℕ) ^ (62 - i)) =
          ∑ t ∈ Finset.range (62 - k), (2 : ℕ) ^ t := by
      refine Finset.sum_nbij' (fun i => 62 - i) (fun t => 62 - t) ?_ ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_Ico] at hi
        simp only [Finset.mem_range]
        omega
      · intro t ht
        simp only [Finset.mem_range] at ht
        simp only [Finset.mem_Ico]
        omega
      · intro i hi
        simp only [Finset.mem_Ico] at hi
        omega
      · intro t ht
        simp only [Finset.mem_range] at ht
        omega
      · intro _ _; rfl
    rw [hbij, sum_range_pow_two]
  have hpos : 1 ≤ 2 ^ (62 - k) := Nat.one_le_pow _ 2 (by decide)
  omega

theorem msbVal_gt_of_first_gt (bC bP : ℕ → Bool) (k : ℕ) (hk : k < 63)
    (hpref : ∀ i < k, bC i = bP i)
    (hC : bC k = true) (hP : bP k = false) :
    msbVal bP < msbVal bC := by
  rw [msbVal_split bC k hk, msbVal_split bP k hk]
  simp [hC, hP]
  have hpre := msbVal_prefix_eq bC bP k hpref
  have htailP := msbVal_tail_lt bP k hk
  omega

theorem exists_first_msb_lt (bC bP : ℕ → Bool)
    (hlt : msbVal bC < msbVal bP) :
    ∃ k < 63, bC k = false ∧ bP k = true ∧ ∀ i < k, bC i = bP i := by
  have hne : (Finset.filter (fun i => bC i ≠ bP i) (Finset.range 63)).Nonempty := by
    by_contra h
    have hempty := Finset.not_nonempty_iff_eq_empty.mp h
    have heq : msbVal bC = msbVal bP := by
      unfold msbVal
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i < 63 := Finset.mem_range.mp hi
      have : bC i = bP i := by
        by_contra hne
        have : i ∈ Finset.filter (fun i => bC i ≠ bP i) (Finset.range 63) :=
          Finset.mem_filter.mpr ⟨hi, hne⟩
        simp [hempty] at this
      rw [this]
    omega
  set S := Finset.filter (fun i => bC i ≠ bP i) (Finset.range 63)
  let k := S.min' hne
  have hkmem := S.min'_mem hne
  have hk : k < 63 := Finset.mem_range.mp (Finset.mem_filter.mp hkmem).1
  have hdiff : bC k ≠ bP k := (Finset.mem_filter.mp hkmem).2
  have hpref : ∀ i < k, bC i = bP i := by
    intro i hi
    by_contra hne'
    have hiS : i ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_trans hi hk), hne'⟩
    exact Nat.lt_le_asymm hi (S.min'_le i hiS)
  refine ⟨k, hk, ?_⟩
  cases hCb : bC k <;> cases hPb : bP k
  · exact (hdiff (by simp [hCb, hPb])).elim
  · exact ⟨rfl, rfl, hpref⟩
  · have := msbVal_gt_of_first_gt bC bP k hk hpref hCb hPb
    exact (Nat.lt_asymm hlt this).elim
  · exact (hdiff (by simp [hCb, hPb])).elim

theorem certLin_one_of_match (a j : ℕ)
    (h : certCBit a j = pBit F (formRN F - 2 - j)) :
    certLin (F := F) a j = 1 := by
  unfold certLin
  cases hp : pBit F (formRN F - 2 - j) <;> simp [h, hp]

theorem certLin_zero_of_ltBit (a j : ℕ)
    (hC : certCBit a j = false) (hP : pBit F (formRN F - 2 - j) = true) :
    certLin (F := F) a j = 0 := by
  unfold certLin
  simp [hC, hP]

theorem certEqRun_one_of_prefix (a n : ℕ)
    (h : ∀ i < n, certCBit a i = pBit F (formRN F - 2 - i)) :
    certEqRun (F := F) a n = 1 := by
  induction n with
  | zero => simp [certEqRun]
  | succ n ih =>
      rw [certEqRun, ih (fun i hi => h i (lt_trans hi (Nat.lt_succ_self _))),
        certLin_one_of_match a n (h n (Nat.lt_succ_self _)), mul_one]

theorem certLt_zero_of_prefix (a n : ℕ)
    (h : ∀ i < n, certCBit a i = pBit F (formRN F - 2 - i)) :
    certLt (F := F) a n = 0 := by
  induction n with
  | zero => simp [certLt]
  | succ n ih =>
      rw [certLt, ih (fun i hi => h i (lt_trans hi (Nat.lt_succ_self _)))]
      have hbit := h n (Nat.lt_succ_self _)
      by_cases hp : pBit F (formRN F - 2 - n) = true
      · simp [hp, hbit]
      · simp [hp]

theorem certLt_one_of_first_lt (a k : ℕ) (hk : k < 63)
    (hpref : ∀ i < k, certCBit a i = pBit F (formRN F - 2 - i))
    (hC : certCBit a k = false) (hP : pBit F (formRN F - 2 - k) = true)
    (hn : k + 1 < formRN F) :
    certLt (F := F) a 63 = 1 := by
  have hrun : certEqRun (F := F) a k = 1 := certEqRun_one_of_prefix a k hpref
  have hzero : certLt (F := F) a k = 0 := certLt_zero_of_prefix a k hpref
  have hstep : certLt (F := F) a (k + 1) = 1 := by
    rw [certLt, hzero, hrun]
    simp [hP, hC, hn]
  have hkill : ∀ t, certEqRun (F := F) a (k + 1 + t) = 0 := by
    intro t
    induction t with
    | zero =>
        rw [Nat.add_zero, certEqRun, hrun, certLin_zero_of_ltBit a k hC hP, mul_zero]
    | succ t ih =>
        rw [show k + 1 + (t + 1) = (k + 1 + t) + 1 by omega, certEqRun, ih, zero_mul]
  have hkill' : ∀ n, k + 1 ≤ n → certEqRun (F := F) a n = 0 := by
    intro n hn
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hn
    simpa [ht] using hkill t
  have hrest : ∀ n, k + 1 ≤ n → n ≤ 63 → certLt (F := F) a n = 1 := by
    intro n hn hn63
    induction n, hn using Nat.le_induction with
    | base => exact hstep
    | succ n hn ih =>
        have ihn := ih (Nat.le_of_succ_le hn63)
        rw [certLt, ihn, hkill' n (by omega)]
        simp
  exact hrest 63 (by omega) le_rfl

theorem leftoverC_msbVal (a : ℕ) (hchar : ringChar F ≠ 0)
    (hle : formRN F ≤ 64) (hm : certShift a = formRN F - 1) (ha0 : 0 < a) :
    msbVal (certCBit a) = (a - 2 ^ (formRN F - 1)) * 2 ^ (64 - formRN F) := by
  set n := formRN F
  have hn1 : 1 ≤ n := Nat.one_le_of_lt (Nat.size_pos.mpr (Nat.pos_of_ne_zero hchar))
  have hm63 : n - 1 ≤ 63 := by omega
  have hsum :
      msbVal (certCBit a) =
        ∑ j ∈ Finset.range (n - 1), (if a.testBit (n - 2 - j) then 2 ^ (62 - j) else 0) := by
    unfold msbVal
    have hsplit : Finset.range 63 = Finset.range (n - 1) ∪ Finset.Ico (n - 1) 63 := by
      ext x
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      omega
    have hdisj : Disjoint (Finset.range (n - 1)) (Finset.Ico (n - 1) 63) := by
      refine Finset.disjoint_left.2 ?_
      intro x hx hx'
      simp only [Finset.mem_range, Finset.mem_Ico] at hx hx'
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have htail :
        ∑ j ∈ Finset.Ico (n - 1) 63, (if certCBit a j then 2 ^ (62 - j) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have : ¬ j < n - 1 := by
        simp only [Finset.mem_Ico] at hj
        omega
      simp [certCBit, hm, this]
    have hhead :
        ∑ j ∈ Finset.range (n - 1), (if certCBit a j then 2 ^ (62 - j) else 0) =
          ∑ j ∈ Finset.range (n - 1), (if a.testBit (n - 2 - j) then 2 ^ (62 - j) else 0) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < n - 1 := Finset.mem_range.mp hj
      have hcb : certCBit a j = a.testBit (n - 2 - j) := by
        simp [certCBit, hm, hj', show n - 1 - 1 - j = n - 2 - j by omega]
      rw [hcb]
    rw [hhead, htail, add_zero]
  have hreidx :
      ∑ j ∈ Finset.range (n - 1), (if a.testBit (n - 2 - j) then 2 ^ (62 - j) else 0) =
        ∑ i ∈ Finset.range (n - 1), (if a.testBit i then 2 ^ (64 - n + i) else 0) := by
    refine Finset.sum_nbij' (fun j => n - 2 - j) (fun i => n - 2 - i) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      have : 62 - j = 64 - n + (n - 2 - j) := by omega
      simp [this]
  have hnat := nat_eq_certBits a ha0
  have hwin : a = 2 ^ (n - 1) +
      ∑ i ∈ Finset.range (n - 1), (if a.testBit i then 2 ^ i else 0) := by
    simpa [hm] using hnat
  have hpow :
      ∑ i ∈ Finset.range (n - 1), (if a.testBit i then 2 ^ (64 - n + i) else 0) =
        (a - 2 ^ (n - 1)) * 2 ^ (64 - n) := by
    have : ∑ i ∈ Finset.range (n - 1), (if a.testBit i then 2 ^ (64 - n + i) else 0) =
        2 ^ (64 - n) * ∑ i ∈ Finset.range (n - 1), (if a.testBit i then 2 ^ i else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hb
      · rw [Nat.pow_add, Nat.mul_comm]
      · simp
    have hsum : ∑ i ∈ Finset.range (n - 1), (if a.testBit i then 2 ^ i else 0) =
        a - 2 ^ (n - 1) := by
      have hle : 2 ^ (n - 1) ≤ a := by
        have : n - 1 < Nat.size a := by
          have := certShift_of_pos a ha0
          omega
        exact (Nat.lt_size).mp this
      omega
    rw [this, hsum]
    ring
  rw [hsum, hreidx, hpow]

theorem leftoverP_msbVal_of_lt64 (hchar : ringChar F ≠ 0)
    (hle : formRN F ≤ 63) :
    ringChar F * 2 ^ (63 - formRN F) ≤
      msbVal (fun j => pBit F (formRN F - 1 - j)) := by
  set n := formRN F
  have hn1 : 1 ≤ n := Nat.one_le_of_lt (Nat.size_pos.mpr (Nat.pos_of_ne_zero hchar))
  have hn : n ≤ 63 := hle
  have hhead :
      ∑ j ∈ Finset.range n, (if pBit F (n - 1 - j) then 2 ^ (62 - j) else 0) =
        ringChar F * 2 ^ (63 - n) := by
    have hreidx :
        ∑ j ∈ Finset.range n, (if (ringChar F).testBit (n - 1 - j) then 2 ^ (62 - j) else 0) =
          ∑ k ∈ Finset.range n, (if (ringChar F).testBit k then 2 ^ (63 - n + k) else 0) := by
      refine Finset.sum_nbij' (fun j => n - 1 - j) (fun k => n - 1 - k) ?_ ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_range] at hj ⊢
        omega
      · intro k hk
        simp only [Finset.mem_range] at hk ⊢
        omega
      · intro j hj
        simp only [Finset.mem_range] at hj
        omega
      · intro k hk
        simp only [Finset.mem_range] at hk
        omega
      · intro j hj
        simp only [Finset.mem_range] at hj
        have : 62 - j = 63 - n + (n - 1 - j) := by omega
        simp [pBit, this]
    have hpow :
        ∑ k ∈ Finset.range n, (if (ringChar F).testBit k then 2 ^ (63 - n + k) else 0) =
          2 ^ (63 - n) * ∑ k ∈ Finset.range n, (if (ringChar F).testBit k then 2 ^ k else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> simp [Nat.pow_add, Nat.mul_comm]
    have hsum : ∑ k ∈ Finset.range n, (if (ringChar F).testBit k then 2 ^ k else 0) =
        ringChar F := by
      have hlt : ringChar F < 2 ^ n := Nat.lt_size_self (ringChar F)
      exact sum_testBit_pow n (ringChar F) hlt
    have hcomb : ∑ j ∈ Finset.range n, (if pBit F (n - 1 - j) then 2 ^ (62 - j) else 0) =
        ringChar F * 2 ^ (63 - n) := by
      unfold pBit
      exact hreidx.trans (by rw [hpow, hsum, Nat.mul_comm])
    exact hcomb
  unfold msbVal
  have hsplit : Finset.range 63 = Finset.range n ∪ Finset.Ico n 63 := by
    ext x
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range n) (Finset.Ico n 63) := by
    refine Finset.disjoint_left.2 ?_
    intro x hx hx'
    simp only [Finset.mem_range, Finset.mem_Ico] at hx hx'
    omega
  rw [hsplit, Finset.sum_union hdisj, hhead]
  exact Nat.le_add_right _ _

theorem leftoverP_msbVal_64 (h : formRN F = 64) :
    msbVal (fun j => pBit F (formRN F - 1 - j)) = ringChar F / 2 := by
  have hlt : ringChar F < 2 ^ 64 := by
    have := Nat.lt_size_self (ringChar F)
    rwa [show Nat.size (ringChar F) = 64 from h] at this
  have hhalf : ringChar F / 2 < 2 ^ 63 := by omega
  have hsum := sum_testBit_pow 63 (ringChar F / 2) hhalf
  have hbits : ∑ i ∈ Finset.range 63,
      (if (ringChar F / 2).testBit i then 2 ^ i else 0) =
        ∑ i ∈ Finset.range 63,
          (if (ringChar F).testBit (i + 1) then 2 ^ i else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← testBit_succ_div]
  have hreidx :
      msbVal (fun j => pBit F (formRN F - 1 - j)) =
        ∑ i ∈ Finset.range 63, (if (ringChar F).testBit (i + 1) then 2 ^ i else 0) := by
    unfold msbVal
    refine Finset.sum_nbij' (fun j => 62 - j) (fun i => 62 - i) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      have : formRN F - 1 - j = (62 - j) + 1 := by rw [h]; omega
      simp [pBit, this]
  rw [hreidx, ← hbits, hsum]

private theorem two_pow_64_sub_one_not_prime : ¬ Nat.Prime ((2 : ℕ) ^ 64 - 1) := by
  have hpow : ∀ k, (2 : ℕ) ^ (2 * k) % 3 = 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add, Nat.mul_mod, ih]
        decide
  have hmod : ((2 : ℕ) ^ 64 - 1) % 3 = 0 := by
    have h64 : (2 : ℕ) ^ 64 % 3 = 1 := hpow 32
    have := Nat.div_add_mod ((2 : ℕ) ^ 64) 3
    omega
  have hdiv : 3 ∣ (2 : ℕ) ^ 64 - 1 := Nat.dvd_of_mod_eq_zero hmod
  intro hp
  rcases Nat.Prime.eq_one_or_self_of_dvd hp 3 hdiv with h3 | h3
  · cases h3
  · have : 3 < (2 : ℕ) ^ 64 - 1 := by decide
    omega

/-- Leftover `m = n−1`, `n ≤ 64`, `a ≤ p`: the 63-bit MSB stream is lex `<`. -/
theorem leftover_msb_lt_of_window (a : ℕ) (hchar : ringChar F ≠ 0)
    (hle : formRN F ≤ 64) (hm : certShift a = formRN F - 1)
    (ha0 : 0 < a) (hap : a ≤ ringChar F) :
    msbVal (certCBit a) <
      msbVal (fun j => pBit F (formRN F - 1 - j)) := by
  set n := formRN F
  have hn1 : 1 ≤ n := Nat.one_le_of_lt (Nat.size_pos.mpr (Nat.pos_of_ne_zero hchar))
  have hpow2 : 2 * 2 ^ (n - 1) = 2 ^ n :=
    ((pow_succ' (2 : ℕ) (n - 1)).symm).trans
      (congrArg (fun t => (2 : ℕ) ^ t) (Nat.sub_add_cancel hn1))
  have hszA : certShift a + 1 = Nat.size a := certShift_of_pos a ha0
  have hlo : 2 ^ (n - 1) ≤ a := by
    have : n - 1 < Nat.size a := by
      rw [← hszA, hm]
      omega
    exact (Nat.lt_size).mp this
  have hCval := leftoverC_msbVal (F := F) a hchar hle hm ha0
  have hlt : msbVal (certCBit a) < msbVal (fun j => pBit F (n - 1 - j)) := by
    by_cases hn64 : n = 64
    · have hP := leftoverP_msbVal_64 (F := F) hn64
      have hC : msbVal (certCBit a) = a - 2 ^ 63 := by
        simpa [n, hn64] using hCval
      have hp64 : ringChar F < 2 ^ 64 := by
        have := Nat.lt_size_self (ringChar F)
        rwa [show Nat.size (ringChar F) = 64 from hn64] at this
      have hplo : 2 ^ 63 ≤ ringChar F := by
        have hszp : Nat.size (ringChar F) = 64 := by
          simpa [n, formRN] using hn64
        have : 63 < Nat.size (ringChar F) := by
          rw [hszp]
          exact Nat.lt_succ_self 63
        exact (Nat.lt_size).mp this
      have hprime : Nat.Prime (ringChar F) :=
        (CharP.char_is_prime_or_zero (R := F) (ringChar F)).resolve_right hchar
      have hodd : ringChar F % 2 = 1 := by
        rcases Nat.Prime.eq_two_or_odd hprime with h2 | hodd
        · have h2sz : Nat.size (2 : ℕ) = 2 := by decide
          have : n = 2 := by simp [n, formRN, h2, h2sz]
          omega
        · exact hodd
      have hpow64 : (2 : ℕ) ^ 64 = 2 * 2 ^ 63 := (pow_succ' (2 : ℕ) 63).symm
      have hp2 : (2 : ℕ) ^ 64 ≤ 2 * ringChar F := by
        rw [hpow64]
        exact Nat.mul_le_mul_left 2 hplo
      have hsub : 2 * ringChar F - (2 : ℕ) ^ 64 = 2 * (ringChar F - 2 ^ 63) := by
        rw [hpow64, Nat.mul_sub_left_distrib]
      have hgap : 2 * (ringChar F - 2 ^ 63) < ringChar F := by
        rw [← hsub]
        exact Nat.sub_lt_right_of_lt_add hp2 (by
          rw [two_mul]
          exact Nat.add_lt_add_left hp64 _)
      have hhalf : 2 * (ringChar F / 2) = ringChar F - 1 := by
        have := Nat.div_add_mod (ringChar F) 2
        omega
      have hle_half : ringChar F - 2 ^ 63 ≤ ringChar F / 2 := by
        have : 2 * (ringChar F - 2 ^ 63) ≤ 2 * (ringChar F / 2) := by
          have : 2 * (ringChar F - 2 ^ 63) ≤ ringChar F - 1 :=
            Nat.le_sub_one_of_lt hgap
          omega
        exact Nat.le_of_mul_le_mul_left this (by decide : 0 < 2)
      have hne_half : ringChar F - 2 ^ 63 ≠ ringChar F / 2 := by
        intro heq
        have : 2 * (ringChar F - 2 ^ 63) = 2 * (ringChar F / 2) :=
          congrArg (fun x => 2 * x) heq
        rw [← hsub, hhalf] at this
        have : ringChar F = (2 : ℕ) ^ 64 - 1 := by
          have : 1 ≤ (2 : ℕ) ^ 64 := Nat.one_le_pow 64 2 (by decide)
          omega
        exact two_pow_64_sub_one_not_prime (by simpa [this] using hprime)
      have : a - 2 ^ 63 < ringChar F / 2 :=
        lt_of_le_of_lt (Nat.sub_le_sub_right hap _)
          (lt_of_le_of_ne hle_half hne_half)
      rw [hC, hP]
      exact this
    · have hle' : n ≤ 63 := by omega
      have hP := leftoverP_msbVal_of_lt64 (F := F) hchar hle'
      have hC : msbVal (certCBit a) = (a - 2 ^ (n - 1)) * 2 ^ (64 - n) := hCval
      have hpn : ringChar F < 2 ^ n := Nat.lt_size_self (ringChar F)
      have hplo : 2 ^ (n - 1) ≤ ringChar F := by
        have : n - 1 < Nat.size (ringChar F) := by
          change n - 1 < n
          omega
        exact (Nat.lt_size).mp this
      have hp2 : 2 ^ n ≤ 2 * ringChar F := by
        rw [← hpow2]
        exact Nat.mul_le_mul_left 2 hplo
      have h2 : 2 * (a - 2 ^ (n - 1)) < ringChar F := by
        have heq : 2 * (a - 2 ^ (n - 1)) = 2 * a - 2 ^ n := by
          rw [Nat.mul_sub_left_distrib, hpow2]
        have hgap : 2 * ringChar F - 2 ^ n < ringChar F :=
          Nat.sub_lt_right_of_lt_add hp2 (by
            rw [two_mul]
            exact Nat.add_lt_add_left hpn _)
        have : 2 * a - 2 ^ n ≤ 2 * ringChar F - 2 ^ n :=
          Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hap) _
        rw [heq]
        exact lt_of_le_of_lt this hgap
      have hscale : (a - 2 ^ (n - 1)) * 2 ^ (64 - n) =
          2 * (a - 2 ^ (n - 1)) * 2 ^ (63 - n) := by
        have : 64 - n = (63 - n) + 1 := by omega
        rw [this, pow_succ']
        ac_rfl
      have : (a - 2 ^ (n - 1)) * 2 ^ (64 - n) < ringChar F * 2 ^ (63 - n) := by
        rw [hscale]
        exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)
      rw [hC]
      exact lt_of_lt_of_le this hP
  exact hlt

theorem nat_lt_of_testBit {n m k : ℕ}
    (hn : n.testBit k = false) (hm : m.testBit k = true)
    (h : ∀ j, k < j → n.testBit j = m.testBit j) : n < m := by
  have hhi : n / 2 ^ (k + 1) = m / 2 ^ (k + 1) := by
    apply Nat.eq_of_testBit_eq
    intro i
    have := h (k + 1 + i) (by omega)
    have hn' : n.testBit (k + 1 + i) = (n / 2 ^ (k + 1)).testBit i := by
      rw [Nat.testBit_div_two_pow, Nat.add_comm]
    have hm' : m.testBit (k + 1 + i) = (m / 2 ^ (k + 1)).testBit i := by
      rw [Nat.testBit_div_two_pow, Nat.add_comm]
    rw [← hn', ← hm', this]
  have hnmod : n % 2 ^ (k + 1) < 2 ^ k := by
    have hbit : (n % 2 ^ (k + 1)).testBit k = false := by
      rw [Nat.testBit_mod_two_pow]
      simp [show k < k + 1 by omega, hn]
    have hlt : n % 2 ^ (k + 1) < 2 ^ (k + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
    by_contra hge
    have hle : 2 ^ k ≤ n % 2 ^ (k + 1) := Nat.le_of_not_gt hge
    have : (n % 2 ^ (k + 1)).testBit k = true :=
      Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hle (by omega)
    simp [hbit] at this
  have hmmod : 2 ^ k ≤ m % 2 ^ (k + 1) := by
    have hbit : (m % 2 ^ (k + 1)).testBit k = true := by
      rw [Nat.testBit_mod_two_pow]
      simp [show k < k + 1 by omega, hm]
    by_contra hle
    have hlt' : m % 2 ^ (k + 1) < 2 ^ k := Nat.not_le.mp hle
    have hz : (m % 2 ^ (k + 1)) / 2 ^ k = 0 := Nat.div_eq_of_lt hlt'
    have : (m % 2 ^ (k + 1)).testBit k = false := by
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hz]
    simp [hbit] at this
  have hn' : n = 2 ^ (k + 1) * (n / 2 ^ (k + 1)) + n % 2 ^ (k + 1) :=
    (Nat.div_add_mod n (2 ^ (k + 1))).symm
  have hm' : m = 2 ^ (k + 1) * (m / 2 ^ (k + 1)) + m % 2 ^ (k + 1) :=
    (Nat.div_add_mod m (2 ^ (k + 1))).symm
  rw [hn', hm', hhi]
  omega

/-- The most significant differing bit of `a < b`: `a` has `0`, `b` has `1`, above agree. -/
theorem exists_msb_diff_of_lt {a b : ℕ} (h : a < b) :
    ∃ i, a.testBit i = false ∧ b.testBit i = true ∧
      ∀ j, i < j → a.testBit j = b.testBit j := by
  classical
  have hbnd : ∀ i, a.testBit i ≠ b.testBit i → i ≤ Nat.size b := by
    intro i hi
    by_contra hlt
    have hb : b < 2 ^ i := lt_of_lt_of_le (Nat.lt_size_self b)
      (Nat.pow_le_pow_right (by decide) (by omega))
    exact hi ((Nat.testBit_lt_two_pow (lt_trans h hb)).trans (Nat.testBit_lt_two_pow hb).symm)
  have hex : ∃ i, a.testBit i ≠ b.testBit i := by
    by_contra hall
    exact (Nat.ne_of_lt h) (Nat.eq_of_testBit_eq fun i => by
      by_contra hne
      exact hall ⟨i, hne⟩)
  obtain ⟨i0, hi0⟩ := hex
  let i := Nat.findGreatest (fun i => a.testBit i ≠ b.testBit i) (Nat.size b)
  have hi : a.testBit i ≠ b.testBit i :=
    Nat.findGreatest_spec (P := fun i => a.testBit i ≠ b.testBit i) (hbnd i0 hi0) hi0
  have habove : ∀ j, i < j → a.testBit j = b.testBit j := by
    intro j hj
    by_contra hne
    exact Nat.findGreatest_is_greatest (P := fun i => a.testBit i ≠ b.testBit i) hj
      (hbnd j hne) hne
  cases ha : a.testBit i <;> cases hb : b.testBit i
  · exact (hi (by rw [ha, hb])).elim
  · exact ⟨i, ha, hb, habove⟩
  · exfalso
    have : b < a := nat_lt_of_testBit hb ha (fun j hj => (habove j hj).symm)
    omega
  · exact (hi (by rw [ha, hb])).elim

/-- **C1 honest completeness.**  A shift-`(n−1)` certificate of `0 < a < p` passes the
    realigned comparison (`certLt = 1`): the most significant bit where `a` and `p` differ lies
    below `n − 1` (both have bit `n − 1` set), `a` has `0` and `p` has `1` there, and every bit
    above agrees.  Before C1 the comparison tested `a − 2^{n−1} < ⌊p/2⌋` (`a ≤ p` sufficed);
    the realigned test is `a < p`. -/
theorem certLt_one_of_window (a : ℕ) (hchar : ringChar F ≠ 0)
    (hle : formRN F ≤ 64) (hm : certShift a = formRN F - 1)
    (ha0 : 0 < a) (hap : a < ringChar F) :
    certLt (F := F) a 63 = 1 := by
  obtain ⟨i, hia, hip, habove⟩ := exists_msb_diff_of_lt hap
  have hpN : ringChar F < 2 ^ formRN F := Nat.lt_size_self _
  have hiN : i < formRN F := by
    by_contra h
    have hz : (ringChar F).testBit i = false :=
      Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hpN (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt h)))
    rw [hz] at hip
    exact Bool.false_ne_true hip
  have htop : a.testBit (formRN F - 1) = true := by
    rw [← hm]; exact certShift_topBit a ha0
  have hi1 : i < formRN F - 1 := by
    rcases Nat.lt_or_ge i (formRN F - 1) with h | h
    · exact h
    · have : i = formRN F - 1 := by omega
      rw [this, htop] at hia
      exact Bool.noConfusion hia
  refine certLt_one_of_first_lt (F := F) a (formRN F - 2 - i) (by omega) ?_ ?_ ?_ (by omega)
  · intro j hj
    have hjs : j < certShift a := by omega
    have hpos : certShift a - 1 - j = formRN F - 2 - j := by omega
    simp only [certCBit, if_pos hjs, hpos, pBit]
    exact habove _ (by omega)
  · have hks : formRN F - 2 - i < certShift a := by omega
    have hpos : certShift a - 1 - (formRN F - 2 - i) = i := by omega
    simp only [certCBit, if_pos hks, hpos, hia]
  · have hpos : formRN F - 2 - (formRN F - 2 - i) = i := by omega
    simp only [pBit, hpos, hip]

theorem exists_first_lt_bit (m N : ℕ) (hm : m < 64) (hN : N < 64) (hlt : m < N) :
    ∃ k < 6, m.testBit k = false ∧ N.testBit k = true ∧
      ∀ j, k < j → j < 6 → m.testBit j = N.testBit j := by
  have hne : (Finset.filter (fun i => m.testBit i ≠ N.testBit i) (Finset.range 6)).Nonempty := by
    by_contra h
    have hempty := Finset.not_nonempty_iff_eq_empty.mp h
    have heq : m = N :=
      eq_of_low6_testBit hm hN fun k hk => by
        by_contra hne
        have : k ∈ Finset.filter (fun i => m.testBit i ≠ N.testBit i) (Finset.range 6) :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hne⟩
        simp [hempty] at this
    omega
  set S := Finset.filter (fun i => m.testBit i ≠ N.testBit i) (Finset.range 6)
  let k := S.max' hne
  have hkmem := S.max'_mem hne
  have hk : k < 6 := Finset.mem_range.mp (Finset.mem_filter.mp hkmem).1
  have hdiff : m.testBit k ≠ N.testBit k := (Finset.mem_filter.mp hkmem).2
  have hhigh : ∀ j, k < j → j < 6 → m.testBit j = N.testBit j := by
    intro j hj hj6
    by_contra hne'
    have hjS : j ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj6, hne'⟩
    exact Nat.lt_le_asymm hj (S.le_max' j hjS)
  refine ⟨k, hk, ?_⟩
  cases hmb : m.testBit k <;> cases hNb : N.testBit k
  · exact (hdiff (by simp [hmb, hNb])).elim
  · exact ⟨rfl, rfl, hhigh⟩
  · have hlt' : N < m :=
      nat_lt_of_testBit hNb hmb fun j hj => by
        by_cases hj6 : j < 6
        · exact (hhigh j hj hj6).symm
        · rw [testBit_false_of_lt_64 hN hj6, testBit_false_of_lt_64 hm hj6]
    exact (Nat.lt_asymm hlt hlt').elim
  · exact (hdiff (by simp [hmb, hNb])).elim

theorem eqmAt_eval_one_of_high (env : Env F) (m k : ℕ) (hk : k < 6)
    (hM : ∀ j, j < 6 → env.trace (col0 + 63 + j) = bit01 (m.testBit j))
    (hP : env.trace (col0 + 71) = matchedP (F := F) m)
    (hhigh : ∀ j, k < j → j < 6 → m.testBit j = nMinus1Bit F j) :
    (eqmAt (F := F) (k + 1)).eval env = 1 := by
  have hlm (j : ℕ) (hj : j < 6) (heq : m.testBit j = nMinus1Bit F j) :
      (lm (F := F) j).eval env = 1 := by
    rw [lm_eval, hM j hj]
    cases hn : nMinus1Bit F j <;> simp [heq, hn]
  have hp_of (hk3 : k < 3) : env.trace (col0 + 71) = 1 := by
    have : matchedP (F := F) m = 1 := by
      simp [matchedP,
        matchedLm_of_eq m 5 (hhigh 5 (by omega) (by decide)),
        matchedLm_of_eq m 4 (hhigh 4 (by omega) (by decide)),
        matchedLm_of_eq m 3 (hhigh 3 (by omega) (by decide))]
    simpa [this] using hP
  interval_cases k
  · have hp := hp_of (by decide)
    simp [eqmAt, CoeffExpr.eval, colP, bcur, hp,
      hlm 2 (by decide) (hhigh 2 (by decide) (by decide)),
      hlm 1 (by decide) (hhigh 1 (by decide) (by decide))]
  · have hp := hp_of (by decide)
    simp [eqmAt, CoeffExpr.eval, colP, bcur, hp,
      hlm 2 (by decide) (hhigh 2 (by decide) (by decide))]
  · have hp := hp_of (by decide)
    simp [eqmAt, CoeffExpr.eval, colP, bcur, hp]
  · simp [eqmAt, CoeffExpr.eval,
      hlm 5 (by decide) (hhigh 5 (by decide) (by decide)),
      hlm 4 (by decide) (hhigh 4 (by decide) (by decide))]
  · simp [eqmAt, CoeffExpr.eval,
      hlm 5 (by decide) (hhigh 5 (by decide) (by decide))]
  · simp [eqmAt, CoeffExpr.eval]

theorem lm_eval_zero_of_ltBit (env : Env F) (m k : ℕ) (hk : k < 6)
    (hM : env.trace (col0 + 63 + k) = bit01 (m.testBit k))
    (hC : m.testBit k = false) (hP : nMinus1Bit F k = true) :
    (lm (F := F) k).eval env = 0 := by
  rw [lm_eval, hM, hP, hC]
  simp

theorem rangeTerm_eval_of_first_lt (env : Env F) (m k j : ℕ)
    (hk : k < 6) (hj : j < 6)
    (hM : ∀ t, t < 6 → env.trace (col0 + 63 + t) = bit01 (m.testBit t))
    (hPcol : env.trace (col0 + 71) = matchedP (F := F) m)
    (hhigh : ∀ t, k < t → t < 6 → m.testBit t = nMinus1Bit F t)
    (hCk : m.testBit k = false) (hPk : nMinus1Bit F k = true) :
    (rangeTerm (F := F) j).eval env = if j = k then (1 : F) else 0 := by
  have heq1 := eqmAt_eval_one_of_high env m k hk hM hPcol hhigh
  by_cases hjk : j = k
  · subst j
    simp only [rangeTerm, CoeffExpr.eval, colM, bcur]
    rw [heq1, hM k hk, hCk, hPk]
    simp [bit01, CoeffExpr.eval]
  · have hterm : (rangeTerm (F := F) j).eval env = 0 := by
      by_cases hjk' : k < j
      · have hmatch : m.testBit j = nMinus1Bit F j := hhigh j hjk' hj
        simp only [rangeTerm, CoeffExpr.eval, colM, bcur]
        cases hn : nMinus1Bit F j
        · simp [CoeffExpr.eval]
        · have hm1 : env.trace (col0 + 63 + j) = 1 := by
            simp [hM j hj, hmatch, hn, bit01]
          simp [hm1, CoeffExpr.eval]
      · have hjle : j < k := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hjk') hjk
        have hlm0 : (lm (F := F) k).eval env = 0 :=
          lm_eval_zero_of_ltBit env m k hk (hM k hk) hCk hPk
        have hP0 : 3 ≤ k → matchedP (F := F) m = 0 := by
          intro hk3
          have hz : matchedLm (F := F) m k = 0 := by
            unfold matchedLm
            simp [hCk, hPk]
          interval_cases k <;> first
            | exact (Nat.not_succ_le_zero _ hk3).elim
            | simp [matchedP, hz]
        have heq0 : (eqmAt (F := F) (j + 1)).eval env = 0 := by
          interval_cases k
          · exact (Nat.not_lt_zero j hjle).elim
          · have hj0 : j = 0 := by omega
            subst j
            simp [eqmAt, CoeffExpr.eval, hlm0]
          · have hj01 : j = 0 ∨ j = 1 := by omega
            rcases hj01 with rfl | rfl
            · simp [eqmAt, CoeffExpr.eval, hlm0]
            · simp [eqmAt, CoeffExpr.eval, hlm0]
          · have hp0 : env.trace (col0 + 71) = 0 := by
              simpa [hP0 (by decide)] using hPcol
            interval_cases j <;> simp [eqmAt, CoeffExpr.eval, colP, bcur, hp0, hlm0]
          · have hp0 : env.trace (col0 + 71) = 0 := by
              simpa [hP0 (by decide)] using hPcol
            interval_cases j <;> simp [eqmAt, CoeffExpr.eval, colP, bcur, hp0, hlm0]
          · have hp0 : env.trace (col0 + 71) = 0 := by
              simpa [hP0 (by decide)] using hPcol
            interval_cases j <;> simp [eqmAt, CoeffExpr.eval, colP, bcur, hp0, hlm0]
        simp [rangeTerm, CoeffExpr.eval, heq0]
    simp [hjk, hterm]

/-- Bit-matched leftover-narrow range: `m < n−1` in the 6-bit window.
    Needs `top = 0`.  Do not apply at bit-matched `top = 1`. -/
theorem rangeGate_eval_of_lt (env : Env F) (m : ℕ)
    (hm : m < 64) (hN : nMinus1Low F < 64) (hlt : m < nMinus1Low F)
    (hM : ∀ k, k < 6 → env.trace (col0 + 63 + k) = bit01 (m.testBit k))
    (hP : env.trace (col0 + 71) = matchedP (F := F) m)
    (hTop : env.trace (col0 + 72) = 0) :
    (rangeGate (F := F)).eval env = 0 := by
  obtain ⟨k, hk, hCk, hNk, hhigh⟩ :=
    exists_first_lt_bit m (nMinus1Low F) hm hN hlt
  have hPk : nMinus1Bit F k = true := by
    simpa [nMinus1Bit, nMinus1Low_testBit (F := F) k hk] using hNk
  have hhigh' : ∀ t, k < t → t < 6 → m.testBit t = nMinus1Bit F t := by
    intro t ht ht6
    rw [hhigh t ht ht6, nMinus1Low_testBit (F := F) t ht6]
  have hterm := fun j hj =>
    rangeTerm_eval_of_first_lt env m k j hk hj hM hP hhigh' hCk hPk
  have hlist : rangeTerms (F := F) =
      [rangeTerm 0, rangeTerm 1, rangeTerm 2, rangeTerm 3, rangeTerm 4, rangeTerm 5] := by
    simp [rangeTerms, List.range_succ, List.range_zero]
  simp only [rangeGate, CoeffExpr.eval, colTop, bcur, hTop, sub_eq_zero, hlist, sumExpr]
  have ht0 := hterm 0 (by decide)
  have ht1 := hterm 1 (by decide)
  have ht2 := hterm 2 (by decide)
  have ht3 := hterm 3 (by decide)
  have ht4 := hterm 4 (by decide)
  have ht5 := hterm 5 (by decide)
  interval_cases k <;> simp [ht0, ht1, ht2, ht3, ht4, ht5]

theorem lm_eval_zero_of_gtBit (env : Env F) (m k : ℕ) (hk : k < 6)
    (hM : env.trace (col0 + 63 + k) = bit01 (m.testBit k))
    (hC : m.testBit k = true) (hP : nMinus1Bit F k = false) :
    (lm (F := F) k).eval env = 0 := by
  rw [lm_eval, hM, hP, hC]
  simp

/-- First high mismatch `m = 1`, `N = 0`: every range term vanishes. -/
theorem rangeTerm_eval_of_first_gt (env : Env F) (m k j : ℕ)
    (hk : k < 6) (hj : j < 6)
    (hM : ∀ t, t < 6 → env.trace (col0 + 63 + t) = bit01 (m.testBit t))
    (hPcol : env.trace (col0 + 71) = matchedP (F := F) m)
    (hhigh : ∀ t, k < t → t < 6 → m.testBit t = nMinus1Bit F t)
    (hCk : m.testBit k = true) (hPk : nMinus1Bit F k = false) :
    (rangeTerm (F := F) j).eval env = 0 := by
  have heq1 := eqmAt_eval_one_of_high env m k hk hM hPcol hhigh
  by_cases hjk : j = k
  · subst j
    simp only [rangeTerm, CoeffExpr.eval, colM, bcur]
    rw [heq1, hM k hk, hCk, hPk]
    simp [bit01, CoeffExpr.eval]
  · by_cases hjk' : k < j
    · have hmatch : m.testBit j = nMinus1Bit F j := hhigh j hjk' hj
      simp only [rangeTerm, CoeffExpr.eval, colM, bcur]
      cases hn : nMinus1Bit F j
      · simp [CoeffExpr.eval]
      · have hm1 : env.trace (col0 + 63 + j) = 1 := by
          simp [hM j hj, hmatch, hn, bit01]
        simp [hm1, CoeffExpr.eval]
    · have hjle : j < k := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hjk') hjk
      have hlm0 : (lm (F := F) k).eval env = 0 :=
        lm_eval_zero_of_gtBit env m k hk (hM k hk) hCk hPk
      have hP0 : 3 ≤ k → matchedP (F := F) m = 0 := by
        intro hk3
        have hz : matchedLm (F := F) m k = 0 := by
          unfold matchedLm
          simp [hCk, hPk]
        interval_cases k <;> first
          | exact (Nat.not_succ_le_zero _ hk3).elim
          | simp [matchedP, hz]
      have heq0 : (eqmAt (F := F) (j + 1)).eval env = 0 := by
        interval_cases k
        · exact (Nat.not_lt_zero j hjle).elim
        · have hj0 : j = 0 := by omega
          subst j
          simp [eqmAt, CoeffExpr.eval, hlm0]
        · have hj01 : j = 0 ∨ j = 1 := by omega
          rcases hj01 with rfl | rfl
          · simp [eqmAt, CoeffExpr.eval, hlm0]
          · simp [eqmAt, CoeffExpr.eval, hlm0]
        · have hp0 : env.trace (col0 + 71) = 0 := by
            simpa [hP0 (by decide)] using hPcol
          interval_cases j <;> simp [eqmAt, CoeffExpr.eval, colP, bcur, hp0, hlm0]
        · have hp0 : env.trace (col0 + 71) = 0 := by
            simpa [hP0 (by decide)] using hPcol
          interval_cases j <;> simp [eqmAt, CoeffExpr.eval, colP, bcur, hp0, hlm0]
        · have hp0 : env.trace (col0 + 71) = 0 := by
            simpa [hP0 (by decide)] using hPcol
          interval_cases j <;> simp [eqmAt, CoeffExpr.eval, colP, bcur, hp0, hlm0]
      simp [rangeTerm, CoeffExpr.eval, heq0]

/-- Leftover-narrow `N < m` with bit-matched `top` of `n−1` (`top = 1`).
    Do not claim `m % 64 < N`.  `Σ = 0`, so `range = 1 − 1`. -/
theorem rangeGate_eval_of_gt_top1 (env : Env F) (m : ℕ)
    (hm : m < 64) (hN : nMinus1Low F < 64) (hgt : nMinus1Low F < m)
    (hM : ∀ k, k < 6 → env.trace (col0 + 63 + k) = bit01 (m.testBit k))
    (hP : env.trace (col0 + 71) = matchedP (F := F) m)
    (hTop : env.trace (col0 + 72) = 1) :
    (rangeGate (F := F)).eval env = 0 := by
  obtain ⟨k, hk, hNk, hCk, hhigh⟩ :=
    exists_first_lt_bit (nMinus1Low F) m hN hm hgt
  have hPk : nMinus1Bit F k = false := by
    simpa [nMinus1Bit, nMinus1Low_testBit (F := F) k hk] using hNk
  have hhigh' : ∀ t, k < t → t < 6 → m.testBit t = nMinus1Bit F t := by
    intro t ht ht6
    rw [← hhigh t ht ht6, nMinus1Low_testBit (F := F) t ht6]
  have hterm := fun j hj =>
    rangeTerm_eval_of_first_gt env m k j hk hj hM hP hhigh' hCk hPk
  have hlist : rangeTerms (F := F) =
      [rangeTerm 0, rangeTerm 1, rangeTerm 2, rangeTerm 3, rangeTerm 4, rangeTerm 5] := by
    simp [rangeTerms, List.range_succ, List.range_zero]
  simp only [rangeGate, CoeffExpr.eval, colTop, bcur, hTop, sub_eq_zero, hlist, sumExpr]
  have ht0 := hterm 0 (by decide)
  have ht1 := hterm 1 (by decide)
  have ht2 := hterm 2 (by decide)
  have ht3 := hterm 3 (by decide)
  have ht4 := hterm 4 (by decide)
  have ht5 := hterm 5 (by decide)
  simp [ht0, ht1, ht2, ht3, ht4, ht5]

/-- Bit-matched `top = 1` makes the range gate `Σ rangeTerms = 0`.
    `rangeShiftExp` writes `n−1` when the Horner window is strictly below
    `N`, so each term vanishes (`rangeGate_eval_of_eq_nMinus1`).  Above `N`
    every term already vanishes (`rangeGate_eval_of_gt_top1`).  Do not read
    the below-`N` sum as `1`. -/
theorem rangeGate_eval_of_rangeShift (env : Env F) (m : ℕ)
    (hM : ∀ k, k < 6 →
      env.trace (col0 + 63 + k) = bit01 ((rangeShiftExp (F := F) m).testBit k))
    (hP : env.trace (col0 + 71) = matchedP (F := F) (rangeShiftExp (F := F) m))
    (hTop : env.trace (col0 + 72) = 1)
    (hnarrow : ¬ (m < 64 ∧ leftoverHornerExp (F := F) m % 64 < nMinus1Low F)) :
    (rangeGate (F := F)).eval env = 0 := by
  have hN64 : nMinus1Low F < 64 := Nat.mod_lt _ (by decide)
  have hse : rangeShiftExp (F := F) m < 64 := rangeShiftExp_lt_64 (F := F) m
  by_cases hsnap : leftoverHornerExp (F := F) m % 64 < nMinus1Low F
  · have hm : ¬ m < 64 := fun hm => hnarrow ⟨hm, hsnap⟩
    have heq : rangeShiftExp (F := F) m = nMinus1Low F := by
      rw [rangeShiftExp_of_mod_lt (F := F) hsnap, if_neg hm]
    have hM' : ∀ k, k < 6 →
        env.trace (col0 + 63 + k) = bit01 (nMinus1Bit F k) := by
      intro k hk
      rw [hM k hk, heq, nMinus1Low_testBit (F := F) k hk]
    have hP1 : env.trace (col0 + 71) = 1 := by
      rw [hP, heq, matchedP_nMinus1]
    exact rangeGate_eval_of_eq_nMinus1 env hM' hP1 hTop
  · have heq : rangeShiftExp (F := F) m = leftoverHornerExp (F := F) m :=
      rangeShiftExp_eq_horner_of_mod_ge (F := F) hsnap
    have he64 : leftoverHornerExp (F := F) m < 64 := by
      rw [← heq]; exact hse
    have hmod : leftoverHornerExp (F := F) m % 64 = leftoverHornerExp (F := F) m :=
      Nat.mod_eq_of_lt he64
    have hge : nMinus1Low F ≤ leftoverHornerExp (F := F) m := by
      have hnot : ¬ leftoverHornerExp (F := F) m % 64 < nMinus1Low F := hsnap
      rw [hmod] at hnot
      exact Nat.le_of_not_lt hnot
    have hM' : ∀ k, k < 6 →
        env.trace (col0 + 63 + k) =
          bit01 ((leftoverHornerExp (F := F) m).testBit k) := by
      intro k hk
      rw [hM k hk, heq]
    have hP' : env.trace (col0 + 71) =
        matchedP (F := F) (leftoverHornerExp (F := F) m) := by
      rw [hP, heq]
    by_cases heqN : leftoverHornerExp (F := F) m = nMinus1Low F
    · have hM'' : ∀ k, k < 6 →
          env.trace (col0 + 63 + k) = bit01 (nMinus1Bit F k) := by
        intro k hk
        rw [hM' k hk, heqN, nMinus1Low_testBit (F := F) k hk]
      have hP1 : env.trace (col0 + 71) = 1 := by
        rw [hP', heqN, matchedP_nMinus1]
      exact rangeGate_eval_of_eq_nMinus1 env hM'' hP1 hTop
    · have hgt : nMinus1Low F < leftoverHornerExp (F := F) m :=
        lt_of_le_of_ne hge (Ne.symm heqN)
      exact rangeGate_eval_of_gt_top1 env (leftoverHornerExp (F := F) m)
        he64 hN64 hgt hM' hP' hTop

/-- Leftover C-stream as an integer, any shift `m ≤ 63`. -/
theorem leftoverC_msbVal_of_shift (a : ℕ) (ha0 : 0 < a)
    (hm63 : certShift a ≤ 63) :
    msbVal (certCBit a) =
      (a - 2 ^ certShift a) * 2 ^ (63 - certShift a) := by
  set m := certShift a
  have hsum :
      msbVal (certCBit a) =
        ∑ j ∈ Finset.range m, (if a.testBit (m - 1 - j) then 2 ^ (62 - j) else 0) := by
    unfold msbVal
    have hsplit : Finset.range 63 = Finset.range m ∪ Finset.Ico m 63 := by
      ext x
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      omega
    have hdisj : Disjoint (Finset.range m) (Finset.Ico m 63) := by
      refine Finset.disjoint_left.2 ?_
      intro x hx hx'
      simp only [Finset.mem_range, Finset.mem_Ico] at hx hx'
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have htail :
        ∑ j ∈ Finset.Ico m 63, (if certCBit a j then 2 ^ (62 - j) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have : ¬ j < certShift a := by
        simp only [Finset.mem_Ico] at hj
        omega
      simp [certCBit, this]
    have hhead :
        ∑ j ∈ Finset.range m, (if certCBit a j then 2 ^ (62 - j) else 0) =
          ∑ j ∈ Finset.range m, (if a.testBit (m - 1 - j) then 2 ^ (62 - j) else 0) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < certShift a := by
        simpa using Finset.mem_range.mp hj
      have hcb : certCBit a j = a.testBit (m - 1 - j) := by
        simp [certCBit, hj']
        have : certShift a - 1 - j = m - 1 - j := by omega
        simp [this]
      rw [hcb]
    rw [hhead, htail, add_zero]
  have hreidx :
      ∑ j ∈ Finset.range m, (if a.testBit (m - 1 - j) then 2 ^ (62 - j) else 0) =
        ∑ i ∈ Finset.range m, (if a.testBit i then 2 ^ (63 - m + i) else 0) := by
    refine Finset.sum_nbij' (fun j => m - 1 - j) (fun i => m - 1 - i) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      have : 62 - j = 63 - m + (m - 1 - j) := by omega
      simp [this]
  have hnat := nat_eq_certBits a ha0
  have hpow :
      ∑ i ∈ Finset.range m, (if a.testBit i then 2 ^ (63 - m + i) else 0) =
        (a - 2 ^ m) * 2 ^ (63 - m) := by
    have : ∑ i ∈ Finset.range m, (if a.testBit i then 2 ^ (63 - m + i) else 0) =
        2 ^ (63 - m) * ∑ i ∈ Finset.range m, (if a.testBit i then 2 ^ i else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hb
      · rw [Nat.pow_add, Nat.mul_comm]
      · simp
    have hsum' : ∑ i ∈ Finset.range m, (if a.testBit i then 2 ^ i else 0) =
        a - 2 ^ m := by
      have hle : 2 ^ m ≤ a := by
        have : m < Nat.size a := by
          have := certShift_of_pos a ha0
          omega
        exact (Nat.lt_size).mp this
      have hnat' : a = 2 ^ m +
          ∑ i ∈ Finset.range m, (if a.testBit i then 2 ^ i else 0) := by
        simpa [show certShift a = m from rfl] using nat_eq_certBits a ha0
      omega
    rw [this, hsum']
    ring
  rw [hsum, hreidx, hpow]

/-- Top 63 bits of `p` when `n > 63`: `p` bits `n−1` down to `n−63`. -/
theorem leftoverP_msbVal_gt (hchar : ringChar F ≠ 0)
    (hgt : 63 < formRN F) :
    msbVal (fun j => pBit F (formRN F - 1 - j)) =
      ringChar F / 2 ^ (formRN F - 63) := by
  set n := formRN F
  have hn1 : 1 ≤ n := Nat.one_le_of_lt (Nat.size_pos.mpr (Nat.pos_of_ne_zero hchar))
  have hlt : ringChar F < 2 ^ n := Nat.lt_size_self (ringChar F)
  have hdiv : ringChar F / 2 ^ (n - 63) < 2 ^ 63 := by
    have : ringChar F < 2 ^ n := hlt
    have hpow : 2 ^ n = 2 ^ 63 * 2 ^ (n - 63) := by
      rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt hgt)]
    have : ringChar F / 2 ^ (n - 63) < 2 ^ 63 :=
      Nat.div_lt_of_lt_mul (by
        rw [Nat.mul_comm, ← hpow]
        exact this)
    exact this
  have hsum := sum_testBit_pow 63 (ringChar F / 2 ^ (n - 63)) hdiv
  have hbits : ∑ i ∈ Finset.range 63,
      (if (ringChar F / 2 ^ (n - 63)).testBit i then 2 ^ i else 0) =
        ∑ i ∈ Finset.range 63,
          (if (ringChar F).testBit (i + (n - 63)) then 2 ^ i else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.testBit_div_two_pow]
  have hreidx :
      msbVal (fun j => pBit F (n - 1 - j)) =
        ∑ i ∈ Finset.range 63, (if (ringChar F).testBit (i + (n - 63)) then 2 ^ i else 0) := by
    unfold msbVal
    refine Finset.sum_nbij' (fun j => 62 - j) (fun i => 62 - i) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      have : n - 1 - j = (62 - j) + (n - 63) := by omega
      simp [pBit, this]
  rw [hreidx, ← hbits, hsum]

/-- Bit `k < w` of `r + 2^w` is bit `k` of `r`. -/
theorem testBit_add_two_pow_of_lt (r w k : ℕ) (hk : k < w) :
    (r + 2 ^ w).testBit k = r.testBit k := by
  have hdv : 2 ^ (k + 1) ∣ 2 ^ w := Nat.pow_dvd_pow _ (Nat.succ_le_of_lt hk)
  have hmod : (r + 2 ^ w) % 2 ^ (k + 1) = r % 2 ^ (k + 1) := by
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdv, Nat.add_zero, Nat.mod_mod]
  have hk' : k < k + 1 := Nat.lt_succ_self k
  have hL : (r + 2 ^ w).testBit k = ((r + 2 ^ w) % 2 ^ (k + 1)).testBit k := by
    rw [Nat.testBit_mod_two_pow]
    simp [hk']
  have hR : r.testBit k = (r % 2 ^ (k + 1)).testBit k := by
    rw [Nat.testBit_mod_two_pow]
    simp [hk']
  rw [hL, hR, hmod]

/-- Top 63 leftover C-bits when `m = n−1` and `n > 64`:
    `a` bits `n−2` down to `n−64`, i.e. `(a − 2^{n−1}) / 2^{n−64}`. -/
theorem leftoverC_msbVal_gt (a : ℕ) (hchar : ringChar F ≠ 0)
    (hgt : 64 < formRN F) (hm : certShift a = formRN F - 1) (ha0 : 0 < a) :
    msbVal (certCBit a) =
      (a - 2 ^ (formRN F - 1)) / 2 ^ (formRN F - 64) := by
  set n := formRN F
  have hn1 : 1 ≤ n := Nat.one_le_of_lt (Nat.size_pos.mpr (Nat.pos_of_ne_zero hchar))
  have hsz : Nat.size a = n := by
    have := certShift_of_pos a ha0
    omega
  have hlo : 2 ^ (n - 1) ≤ a :=
    (Nat.lt_size).mp (by rw [hsz]; omega)
  have hhi : a < 2 ^ n := Nat.size_le.mp (by rw [hsz])
  have hpow63 : 2 ^ (n - 1) = 2 ^ 63 * 2 ^ (n - 64) := by
    have : n - 1 = 63 + (n - 64) := by omega
    rw [this, pow_add]
  have h2 : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := by rw [Nat.sub_add_cancel hn1]
      _ = 2 ^ (n - 1) * 2 := pow_succ _ _
      _ = 2 ^ (n - 1) + 2 ^ (n - 1) := mul_two _
  have hlow : (a - 2 ^ (n - 1)) / 2 ^ (n - 64) < 2 ^ 63 := by
    have : a - 2 ^ (n - 1) < 2 ^ (n - 1) :=
      Nat.sub_lt_left_of_lt_add hlo (hhi.trans_eq h2)
    exact Nat.div_lt_of_lt_mul (by
      rw [Nat.mul_comm, ← hpow63]
      exact this)
  have hsum := sum_testBit_pow 63 ((a - 2 ^ (n - 1)) / 2 ^ (n - 64)) hlow
  have hreidx :
      msbVal (certCBit a) =
        ∑ i ∈ Finset.range 63,
          (if a.testBit (i + (n - 64)) then 2 ^ i else 0) := by
    unfold msbVal
    refine Finset.sum_nbij' (fun j => 62 - j) (fun i => 62 - i) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      have hj' : j < certShift a := by
        rw [hm]
        omega
      have hcb : certCBit a j = a.testBit (n - 2 - j) := by
        unfold certCBit
        rw [if_pos hj', hm]
        exact congrArg a.testBit (by omega)
      have : n - 2 - j = (62 - j) + (n - 64) := by omega
      simp [hcb, this]
  have hbits :
      ∑ i ∈ Finset.range 63,
          (if a.testBit (i + (n - 64)) then 2 ^ i else 0) =
        ∑ i ∈ Finset.range 63,
          (if ((a - 2 ^ (n - 1)) / 2 ^ (n - 64)).testBit i then 2 ^ i else 0) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hk : i + (n - 64) < n - 1 := by
      simp only [Finset.mem_range] at hi
      omega
    have htb : (a - 2 ^ (n - 1)).testBit (i + (n - 64)) =
        a.testBit (i + (n - 64)) := by
      have h := testBit_add_two_pow_of_lt (a - 2 ^ (n - 1)) (n - 1)
        (i + (n - 64)) hk
      have ha_outer :
          a.testBit (i + (n - 64)) =
            ((a - 2 ^ (n - 1)) + 2 ^ (n - 1)).testBit (i + (n - 64)) :=
        congrArg (fun t => t.testBit (i + (n - 64)))
          (Nat.sub_add_cancel hlo).symm
      exact h.symm.trans ha_outer.symm
    rw [Nat.testBit_div_two_pow, htb]
  rw [hreidx, hbits, hsum]

/-- Decidable leftover-stream test: 63-bit `C < P`.  False on Mersenne `C = P`. -/
noncomputable def leftoverMsbLt (a : ℕ) : Bool :=
  decide (msbVal (certCBit a) <
    msbVal (fun j => pBit F (formRN F - 1 - j)))

theorem leftoverMsbLt_iff (a : ℕ) :
    leftoverMsbLt (F := F) a = true ↔
      msbVal (certCBit a) <
        msbVal (fun j => pBit F (formRN F - 1 - j)) := by
  simp [leftoverMsbLt]

/-- Live leftover `C` when leftover writes the real limb (`T = 2^m`).
    Leftover-narrow always has live `T`, so `C` reconstructs the atom
    even when the leftover MSB stream is not lex-below `P`.  Dummy `T`
    still zeros `C`.  Do not `rfl` `certLt = 1` or `2^m = L`. -/
noncomputable def leftoverUseC (a : ℕ) : Bool :=
  decide (rangeShiftExp (F := F) (certShift a) = certShift a)

theorem leftoverUseC_of_msb (a : ℕ)
    (_h : leftoverMsbLt (F := F) a = true)
    (hlive : rangeShiftExp (F := F) (certShift a) = certShift a) :
    leftoverUseC (F := F) a = true := by
  simp [leftoverUseC, hlive]

theorem leftoverUseC_of_live (a : ℕ)
    (_h : leftoverMsbLt (F := F) a = true)
    (hlive : rangeShiftExp (F := F) (certShift a) = certShift a) :
    leftoverUseC (F := F) a = true :=
  leftoverUseC_of_msb (F := F) a _h hlive

/-- Live `T` alone fills leftover `C` (leftover-narrow axis). -/
theorem leftoverUseC_of_hlive (a : ℕ)
    (hlive : rangeShiftExp (F := F) (certShift a) = certShift a) :
    leftoverUseC (F := F) a = true := by
  simp [leftoverUseC, hlive]

theorem leftoverUseC_of_narrow (a : ℕ)
    (_h : leftoverMsbLt (F := F) a = true)
    (hlive : rangeShiftExp (F := F) (certShift a) = certShift a) :
    leftoverUseC (F := F) a = true :=
  leftoverUseC_of_hlive (F := F) a hlive

theorem leftoverUseC_live_of_use (a : ℕ)
    (h : leftoverUseC (F := F) a = true) :
    rangeShiftExp (F := F) (certShift a) = certShift a := by
  simpa [leftoverUseC] using h

theorem leftoverUseC_not_of_not_live (a : ℕ)
    (hlive : rangeShiftExp (F := F) (certShift a) ≠ certShift a) :
    leftoverUseC (F := F) a ≠ true := by
  intro h
  exact hlive (leftoverUseC_live_of_use (F := F) a h)

/-- Dummy `T` (not live) zeros leftover `C`.  `¬leftoverMsbLt` no longer
    forces this: leftover-narrow live `C` still reconstructs the atom. -/
theorem leftoverUseC_zero_msb (a : ℕ)
    (h : leftoverUseC (F := F) a ≠ true) :
    rangeShiftExp (F := F) (certShift a) ≠ certShift a := by
  intro hl
  exact h (leftoverUseC_of_hlive (F := F) a hl)

/-- Window Nats below `p` inject through the field. -/
theorem leftover_nat_cast_inj {a b : ℕ} (_hchar : ringChar F ≠ 0)
    (ha : a < ringChar F) (hb : b < ringChar F)
    (he : (a : F) = (b : F)) : a = b := by
  haveI : CharP F (ringChar F) := inferInstance
  have hmod : a % ringChar F = b % ringChar F :=
    (CharP.natCast_eq_natCast (R := F) (p := ringChar F)).mp he
  have ha' : a % ringChar F = a := Nat.mod_eq_of_lt ha
  have hb' : b % ringChar F = b := Nat.mod_eq_of_lt hb
  exact ha'.symm.trans (hmod.trans hb')

/-- Distinct window Nats stay distinct in `F` when both sit below `p`. -/
theorem leftover_cast_ne_two_pow (a e : ℕ) (hchar : ringChar F ≠ 0)
    (ha : a < ringChar F) (he : 2 ^ e < ringChar F) (hne : a ≠ 2 ^ e) :
    (a : F) ≠ (2 : F) ^ e := by
  intro h
  apply hne
  apply leftover_nat_cast_inj (F := F) hchar ha he
  simpa [Nat.cast_pow] using h

/-- Zero leftover `C` is lex-below `P` (`p_{n−1} = 1`). -/
theorem leftoverMsbLt_of_zero (hchar : ringChar F ≠ 0) :
    leftoverMsbLt (F := F) 0 = true := by
  rw [leftoverMsbLt_iff]
  have hC : msbVal (certCBit 0) = 0 := by
    unfold msbVal
    refine Finset.sum_eq_zero fun j _ => ?_
    have : certCBit 0 j = false := by
      simp [certCBit, certShift, Nat.size_zero]
    simp [this]
  have hP0 : pBit F (formRN F - 1 - 0) = true := by
    simpa [pBit, formRN, Nat.sub_zero] using testBit_pred_size (n := ringChar F) hchar
  have hP : 0 < msbVal (fun j => pBit F (formRN F - 1 - j)) := by
    rw [msbVal_split (fun j => pBit F (formRN F - 1 - j)) 0 (by decide)]
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, hP0, ↓reduceIte]
    exact Nat.lt_add_right _ (Nat.two_pow_pos 62)
  omega

/-- `p`'s MSB is 1, so the leftover `P` stream is at least `2^62`. -/
theorem leftoverP_ge_two_pow_62 (hchar : ringChar F ≠ 0) :
    2 ^ 62 ≤ msbVal (fun j => pBit F (formRN F - 1 - j)) := by
  have hP0 : pBit F (formRN F - 1 - 0) = true := by
    simpa [pBit, formRN, Nat.sub_zero] using testBit_pred_size (n := ringChar F) hchar
  rw [msbVal_split (fun j => pBit F (formRN F - 1 - j)) 0 (by decide)]
  simp only [Finset.range_zero, Finset.sum_empty, zero_add]
  rw [if_pos hP0]
  exact Nat.le_add_right _ _

/-- Zero leftover MSB (`C[0] = 0`) is lex-below `P`. -/
theorem leftoverMsbLt_of_cbit0 (a : ℕ) (hchar : ringChar F ≠ 0)
    (h0 : certCBit a 0 = false) :
    leftoverMsbLt (F := F) a = true := by
  rw [leftoverMsbLt_iff]
  have hC : msbVal (certCBit a) < 2 ^ 62 := by
    have hsplit := msbVal_split (certCBit a) 0 (by decide)
    have hmid : (if certCBit a 0 then (2 : ℕ) ^ 62 else 0) = 0 := by
      rw [h0]
      exact if_neg (by decide : ¬ false = true)
    rw [hsplit, Finset.range_zero, Finset.sum_empty, zero_add, hmid, zero_add]
    exact msbVal_tail_lt (certCBit a) 0 (by decide)
  exact hC.trans_le (leftoverP_ge_two_pow_62 (F := F) hchar)

/-- Live leftover `T = 2^m` at `n ≤ 64` is the full window `m = n−1`
    when the Horner window is not leftover-narrow unmatched. -/
theorem leftoverMatch_of_live_le64 (a : ℕ) (hchar : ringChar F ≠ 0)
    (hle : formRN F ≤ 64) (hltN : a < 2 ^ formRN F)
    (hlive : rangeShiftExp (F := F) (certShift a) = certShift a)
    (hgeWin : ¬ leftoverHornerExp (F := F) (certShift a) % 64 < nMinus1Low F) :
    leftoverMatch (F := F) (certShift a) := by
  set m := certShift a
  have hn0 : 0 < formRN F := Nat.size_pos.mpr (Nat.pos_of_ne_zero hchar)
  have hm_lt : m < formRN F := certShift_lt_of_lt a (formRN F) hn0 hltN
  have hm64 : m < 64 := lt_of_lt_of_le hm_lt hle
  have hN : nMinus1Low F = formRN F - 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hexp : leftoverHornerExp (F := F) m = m := leftoverHornerExp_of_lt hm64
  have hmod : leftoverHornerExp (F := F) m % 64 = m := by
    rw [hexp, Nat.mod_eq_of_lt hm64]
  have hge : nMinus1Low F ≤ m :=
    Nat.le_of_not_lt (by simpa [hmod] using hgeWin)
  have heq : nMinus1Low F = m := by
    rw [hN]
    omega
  exact (leftoverMatch_of_lt (F := F) hm64).mpr heq

/-- Window leftover `m = n−1` at `n ≤ 64` is lex-below `P`. -/
theorem leftoverMsbLt_of_window (a : ℕ) (hchar : ringChar F ≠ 0)
    (hle : formRN F ≤ 64) (hm : certShift a = formRN F - 1)
    (ha0 : 0 < a) (hap : a ≤ ringChar F) :
    leftoverMsbLt (F := F) a = true :=
  (leftoverMsbLt_iff (F := F) a).mpr
    (leftover_msb_lt_of_window (F := F) a hchar hle hm ha0 hap)

/-- Live `T = 2^m` at `n ≤ 64` with Horner window `≥ n−1` is leftover-match,
    so `C < P`.  Leftover-narrow unmatched (`m < n−1`) does not use this. -/
theorem leftoverMsbLt_of_narrow_live (a : ℕ) (hchar : ringChar F ≠ 0)
    (hlt : a < 2 ^ 63) (ha0 : 0 < a) (hap : a ≤ ringChar F)
    (hltN : a < 2 ^ formRN F)
    (hle : formRN F ≤ 64)
    (hlive : rangeShiftExp (F := F) (certShift a) = certShift a)
    (hgeWin : ¬ leftoverHornerExp (F := F) (certShift a) % 64 < nMinus1Low F) :
    leftoverMsbLt (F := F) a = true := by
  have hwin := leftoverMatch_of_live_le64 (F := F) a hchar hle hltN hlive hgeWin
  have hm62 : certShift a < 63 := by
    have hsz : Nat.size a ≤ 63 := (Nat.size_le).mpr hlt
    have := certShift_of_pos a ha0
    omega
  have hm64 : certShift a < 64 := lt_trans hm62 (by decide)
  have hmN : certShift a = formRN F - 1 :=
    leftoverMatch_eq_nMinus1_of_le64 (F := F) hchar hwin hm64 hle
  have hn1_lt : formRN F - 1 < 63 := hmN ▸ hm62
  by_cases hn64 : formRN F = 64
  · exact (lt_irrefl (63 : ℕ) (by simpa [hn64] using hn1_lt)).elim
  · have hn63 : formRN F ≤ 63 := Nat.le_of_lt_succ
      (lt_of_le_of_ne hle hn64)
    exact leftoverMsbLt_of_window (F := F) a hchar (le_trans hn63 (by decide)) hmN ha0 hap

/-- Leftover-narrow `C` as an integer sits strictly below `2^63`. -/
theorem leftoverC_msbVal_lt_two_pow_63 (a : ℕ) (ha0 : 0 < a) (_hlt : a < 2 ^ 63)
    (hm63 : certShift a ≤ 63) :
    msbVal (certCBit a) < 2 ^ 63 := by
  rw [leftoverC_msbVal_of_shift a ha0 hm63]
  set m := certShift a
  have hsz : Nat.size a = m + 1 := by
    have := certShift_of_pos a ha0
    omega
  have hlt : a < 2 ^ (m + 1) := by
    simpa [hsz] using Nat.lt_size_self a
  have hlo : 2 ^ m ≤ a := by
    have : m < Nat.size a := by rw [hsz]; exact Nat.lt_succ_self m
    exact (Nat.lt_size).mp this
  have hsub : a - 2 ^ m < 2 ^ m := by omega
  calc (a - 2 ^ m) * 2 ^ (63 - m) < 2 ^ m * 2 ^ (63 - m) :=
      Nat.mul_lt_mul_of_pos_right hsub (Nat.pow_pos (by decide : 0 < 2))
    _ = 2 ^ 63 := by
      rw [Nat.mul_comm, ← Nat.pow_add, show 63 - m + m = 63 by omega]

/-- Live leftover-narrow with `C[0] = 1` still has `C < P` at `n ≤ 64`. -/
theorem leftoverMsbLt_of_cbit1_live (a : ℕ) (hchar : ringChar F ≠ 0)
    (_hC1 : certCBit a 0 = true) (hlt : a < 2 ^ 63) (ha0 : 0 < a)
    (hap : a ≤ ringChar F) (hltN : a < 2 ^ formRN F)
    (hle : formRN F ≤ 64)
    (hlive : rangeShiftExp (F := F) (certShift a) = certShift a)
    (hgeWin : ¬ leftoverHornerExp (F := F) (certShift a) % 64 < nMinus1Low F) :
    leftoverMsbLt (F := F) a = true :=
  leftoverMsbLt_of_narrow_live (F := F) a hchar hlt ha0 hap hltN hle hlive hgeWin

/-- `n > 64`, leftover `m = n−1`, `a < p`: the 63-bit streams are lex `<`
    whenever the floor comparison `(a − 2^{n−1}) / 2^{n−64} < p / 2^{n−63}`
    holds.  Mersenne `a = p` is `C = P` and is excluded by `a < p` plus this
    floor test; do not claim `certLt = 1` there. -/
theorem leftover_msb_lt_of_window_gt (a : ℕ) (hchar : ringChar F ≠ 0)
    (hgt : 64 < formRN F) (hm : certShift a = formRN F - 1)
    (ha0 : 0 < a) (hlt : a < ringChar F)
    (hdiv : (a - 2 ^ (formRN F - 1)) / 2 ^ (formRN F - 64) <
      ringChar F / 2 ^ (formRN F - 63)) :
    msbVal (certCBit a) <
      msbVal (fun j => pBit F (formRN F - 1 - j)) := by
  rw [leftoverC_msbVal_gt (F := F) a hchar hgt hm ha0,
    leftoverP_msbVal_gt (F := F) hchar (lt_trans (by decide : 63 < 64) hgt)]
  exact hdiv

/-- Every positive `n` sits at or above its top `Nat.size` bit. -/
theorem nat_ge_two_pow_pred_size (n : ℕ) (hn : n ≠ 0) :
    2 ^ (Nat.size n - 1) ≤ n := by
  have hpos : 0 < Nat.size n := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
  have hk : Nat.size n - 1 < Nat.size n := Nat.sub_lt hpos Nat.one_pos
  exact (Nat.lt_size).mp hk

/-- `Nat.size p > 2` from the deployed bit-length hypothesis. -/
theorem ringChar_size_gt_two (hn : 2 < formRN F) : 2 < Nat.size (ringChar F) := by
  simpa [formRN] using hn

/-- Characteristic `p > 2` once `Nat.size p > 2` (deployed `n = 64`). -/
theorem ringChar_gt_two (hchar : ringChar F ≠ 0)
    (hsz : 2 < Nat.size (ringChar F)) : 2 < ringChar F := by
  have hprime := (CharP.char_is_prime_or_zero (R := F) (ringChar F)).resolve_right hchar
  have hone := Nat.Prime.one_lt hprime
  have hne2 : ringChar F ≠ 2 := by
    intro h
    rw [h] at hsz
    have htwo : Nat.size (2 : ℕ) = 2 := by decide
    exact (Nat.lt_irrefl 2).elim (htwo ▸ hsz)
  exact Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hone) (Ne.symm hne2)

theorem ringChar_gt_two_formRN (hchar : ringChar F ≠ 0) (hn : 2 < formRN F) :
    2 < ringChar F :=
  ringChar_gt_two hchar (ringChar_size_gt_two hn)

theorem ringChar_gt_two_of_ne2 (hchar : ringChar F ≠ 0) (h2 : 2 ≠ ringChar F) :
    2 < ringChar F := by
  have hprime := (CharP.char_is_prime_or_zero (R := F) (ringChar F)).resolve_right hchar
  exact Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hprime.one_lt) h2

theorem ringChar_gt_two_of_two_ne_zero (hchar : ringChar F ≠ 0) (h2F : (2 : F) ≠ 0) :
    2 < ringChar F :=
  ringChar_gt_two_of_ne2 hchar (by
    intro heq
    exact h2F (by
      have hz : (ringChar F : F) = 0 := CharP.cast_eq_zero (R := F) (ringChar F)
      have hcast : (2 : F) = (ringChar F : F) := congrArg Nat.cast heq
      exact hcast.trans hz))

theorem ringChar_gt_two_of_formRN63 (hchar : ringChar F ≠ 0) (hn : 63 < formRN F) :
    2 < ringChar F :=
  ringChar_gt_two_formRN hchar (Nat.lt_trans (by decide : (2 : ℕ) < 63) hn)

/-- Below the top `Nat.size` bit, `2^m` sits strictly below `p`. -/
theorem two_pow_lt_ringChar (hchar : ringChar F ≠ 0) {m : ℕ}
    (hm : m < Nat.size (ringChar F) - 1) : 2 ^ m < ringChar F :=
  lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide : 1 < 2) hm)
    (nat_ge_two_pow_pred_size (ringChar F) hchar)

theorem two_pow_lt_ringChar_of_lt63 (hchar : ringChar F ≠ 0) (hn : 63 < formRN F) {m : ℕ}
    (hm : m < 63) : 2 ^ m < ringChar F := by
  have hbound : m < formRN F - 1 := by
    have := hn
    omega
  exact two_pow_lt_ringChar hchar (by simpa [formRN] using hbound)

/-- The top power-of-two window sits strictly below `p`. -/
theorem two_pow_pred_size_lt_ringChar (hchar : ringChar F ≠ 0) (hgt2 : 2 < ringChar F) :
    2 ^ (Nat.size (ringChar F) - 1) < ringChar F := by
  set k := Nat.size (ringChar F) - 1
  have hge := nat_ge_two_pow_pred_size (ringChar F) hchar
  refine lt_of_le_of_ne hge ?_
  intro heq
  have hprime : Nat.Prime (ringChar F) :=
    (CharP.char_is_prime_or_zero (R := F) (ringChar F)).resolve_right hchar
  have hodd : ringChar F % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd hprime with h2 | hodd
    · exfalso
      exact (not_le.mpr hgt2) (le_of_eq h2)
    · exact hodd
  have hodd' : (2 ^ k) % 2 = 1 := by simpa [k, heq] using hodd
  have hkpos : 0 < k := by
    by_cases hk0 : k = 0
    · exfalso
      have hone : ringChar F = 1 := by
        rw [hk0, pow_zero] at heq
        exact heq.symm
      rw [hone] at hprime
      exact Nat.not_prime_one hprime
    · exact Nat.pos_of_ne_zero hk0
  have heven : 2 ^ k % 2 = 0 := by
    rcases k with (_ | k')
    · exact (Nat.lt_irrefl 0 hkpos).elim
    · have hmul : (2 * 2 ^ k') % 2 = 0 := by
        rw [Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod]
      simpa [pow_succ] using hmul
  rw [hodd'] at heven
  exact Nat.one_ne_zero heven

/-- `64 ≤ formRN` implies the bit-length exceeds `63`. -/
theorem formRN63_of_ge64 (h : 64 ≤ formRN F) : 63 < formRN F := by omega

/-- Dummy-window exponent sits below `formRN`. -/
theorem nMinus1Low_lt_formRN (hchar : ringChar F ≠ 0) : nMinus1Low F < formRN F := by
  unfold nMinus1Low formRN
  have hpos : 0 < ringChar F := Nat.pos_of_ne_zero hchar
  have hszpos : 0 < Nat.size (ringChar F) := by
    have hge : 1 ≤ Nat.size (ringChar F) := Nat.size_pos.mpr hpos
    exact Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hge
  have hsub : Nat.size (ringChar F) - 1 < Nat.size (ringChar F) :=
    Nat.sub_lt hszpos (by decide : (0 : ℕ) < 1)
  by_cases h64 : 64 ≤ Nat.size (ringChar F)
  · exact lt_of_le_of_lt (Nat.mod_le _ _) hsub
  · have hlt : Nat.size (ringChar F) < 64 := Nat.lt_of_not_ge h64
    have hmod : (Nat.size (ringChar F) - 1) % 64 = Nat.size (ringChar F) - 1 := by
      apply Nat.mod_eq_of_lt
      exact Nat.lt_trans hsub hlt
    simpa [hmod] using hsub

/-- `nMinus1Low` sits at most at `formRN − 1`. -/
theorem nMinus1Low_le_pred_formRN : nMinus1Low F ≤ formRN F - 1 := by
  unfold nMinus1Low formRN
  exact Nat.le_trans (Nat.mod_le _ _) (Nat.le_refl _)

/-- Dummy `T = 2^63` forces the deployed bit-length past `63`. -/
theorem formRN63_of_nMinus1Low_eq_63 (h : nMinus1Low F = 63) : 63 < formRN F := by
  by_contra hnot
  have hle : formRN F ≤ 63 := Nat.le_of_not_gt hnot
  have hmod : nMinus1Low F ≤ formRN F - 1 := nMinus1Low_le_pred_formRN
  rw [h] at hmod
  omega

/-- When `63 < formRN`, the `2^63` window sits strictly below `p`. -/
theorem two_pow_63_lt_ringChar (hchar : ringChar F ≠ 0) (hn : 63 < formRN F) :
    2 ^ 63 < ringChar F := by
  by_cases h64 : formRN F = 64
  · have hgt2 := ringChar_gt_two_of_formRN63 hchar (h64 ▸ hn)
    have hsz : Nat.size (ringChar F) = 64 := by simpa [formRN] using h64
    rw [show (2 ^ 63 : ℕ) = 2 ^ (Nat.size (ringChar F) - 1) from by rw [hsz]]
    exact two_pow_pred_size_lt_ringChar hchar hgt2
  · have hbound : 63 < Nat.size (ringChar F) - 1 := by
      change 63 < formRN F - 1
      omega
    exact two_pow_lt_ringChar hchar hbound

/-- Characteristic two is incompatible with `(2 : F) ≠ 0`. -/
theorem ringChar_ne_two_of_two_ne_zero (h2 : (2 : F) ≠ 0) : ringChar F ≠ 2 := by
  intro h
  apply h2
  calc (2 : F) = (ringChar F : F) := by
        rw [show (ringChar F : ℕ) = 2 from h]
        norm_cast
    _ = 0 := CharP.cast_eq_zero (R := F) (p := ringChar F)

/-- Strictly above characteristic two once `ringChar ≠ 2` and `2 < formRN`. -/
theorem ringChar_gt_two_of_ne_two (hchar : ringChar F ≠ 0) (_hne : ringChar F ≠ 2)
    (hfn : 2 < formRN F) : 2 < ringChar F :=
  ringChar_gt_two_formRN hchar hfn

/-- `2^{n−1 mod 64}` sits below the characteristic. -/
theorem two_pow_nMinus1Low_lt_ringChar (hchar : ringChar F ≠ 0) (hgt2 : 2 < ringChar F) :
    2 ^ nMinus1Low F < ringChar F := by
  by_cases hle64 : 64 ≤ formRN F
  · have hn63 := formRN63_of_ge64 hle64
    by_cases hN63 : nMinus1Low F = 63
    · rw [hN63]
      exact two_pow_63_lt_ringChar hchar hn63
    · have hN62 : nMinus1Low F ≤ 62 := by
        have hN64 : nMinus1Low F < 64 := by
          unfold nMinus1Low
          exact Nat.mod_lt _ (by decide)
        omega
      exact lt_trans (Nat.pow_lt_pow_right (by decide : (1 : ℕ) < 2)
          (Nat.lt_of_le_of_lt hN62 (by decide : (62 : ℕ) < 63)))
        (two_pow_63_lt_ringChar hchar hn63)
  · have hform : formRN F < 64 := Nat.lt_of_not_ge hle64
    have hpos : 0 < ringChar F := Nat.pos_of_ne_zero hchar
    have hszpos : 0 < Nat.size (ringChar F) := by
      have hge : 1 ≤ Nat.size (ringChar F) := Nat.size_pos.mpr hpos
      exact Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hge
    have hmod : nMinus1Low F = formRN F - 1 := by
      unfold nMinus1Low formRN
      rw [Nat.mod_eq_of_lt (Nat.lt_trans (Nat.sub_lt hszpos (by decide)) hform)]
    rw [hmod]
    change 2 ^ (Nat.size (ringChar F) - 1) < ringChar F
    exact two_pow_pred_size_lt_ringChar hchar hgt2

/-- `certCBit (2^m) 0` is always false: only bit `m` is set. -/
theorem certCBit_zero_pow (m : ℕ) : certCBit (2 ^ m) 0 = false := by
  by_cases hm : m = 0
  · subst hm
    simp [certCBit, certShift]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hsz : Nat.size (2 ^ m) = m + 1 := Nat.size_pow
    have hshift : certShift (2 ^ m) = m := by
      simp [certShift, hsz, Nat.succ_sub_one]
    have hbit : (2 ^ m).testBit (m - 1) = false := by
      rw [Nat.testBit_two_pow]
      exact decide_eq_false (by
        intro h
        have := Nat.sub_add_cancel (Nat.one_le_of_lt hmpos)
        omega)
    unfold certCBit
    rw [if_pos (by rw [hshift]; exact hmpos)]
    simp [hshift, hbit]

/-- Live `C[0] = 1` excludes `a = 2^m`. -/
theorem certCBit_pow_ne (a : ℕ) (hC1 : certCBit a 0 = true) {m : ℕ} (hm : m = certShift a) :
    a ≠ 2 ^ m := by
  intro heq
  rw [heq] at hC1
  rw [certCBit_zero_pow m] at hC1
  exact Bool.false_ne_true hC1

/-- Zeroed leftover `C`: `T · csum = 2^e` from `T = 2^e` and `csum = 1`. -/
theorem axis_match_gate_eq (env : Env F) (e : ℕ)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0) :
    env.trace (col0 + 70) * (csum (F := F)).eval env = (2 : F) ^ e := by
  rw [hT, csum_eval_of_zero_c env hCz, mul_one]

/-- Zeroed leftover `C` at trace `272`: `T · csum = 2^e`. -/
theorem axis_match272 (env : Env F) (e : ℕ)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0) :
    env.trace 272 * (csum (F := F)).eval env = (2 : F) ^ e := by
  convert axis_match_gate_eq env e hT hCz using 1
  simp [col0]

/-- `trace 272` and `col0 + 70` agree on the axis match product. -/
theorem axis_match272_csum_eq (env : Env F) :
    env.trace 272 * (csum (F := F)).eval env =
      env.trace (col0 + 70) * (csum (F := F)).eval env := by
  simp [col0]

/-- Relocate a `trace 272` axis match to `col0 + 70`. -/
theorem axis_hmatch272_to_col0 (env : Env F) (L : F)
    (hmatch272 : env.trace 272 * (csum (F := F)).eval env = L) :
    env.trace (col0 + 70) * (csum (F := F)).eval env = L := by
  rw [← axis_match272_csum_eq, hmatch272]

/-- Zeroed leftover `C` with `T = 2^e` and `T · csum = L` forces `(a : F) = ↑(2^e)`. -/
theorem axis_zero_c_pow_ne (env : Env F) (a : ℕ) (L : F) (e : ℕ)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (haL : (a : F) = L)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0)
    (hmatch : env.trace (col0 + 70) * (csum (F := F)).eval env = L) :
    (a : F) = ((2 ^ e : ℕ) : F) := by
  calc (a : F) = L := haL
    _ = env.trace (col0 + 70) * (csum (F := F)).eval env := hmatch.symm
    _ = (2 : F) ^ e := axis_match_gate_eq env e hT hCz
    _ = ((2 ^ e : ℕ) : F) := (Nat.cast_pow (α := F) (m := 2) (n := e)).symm

/-- Zeroed leftover `C` with live `T = 2^m`: `T · csum = L` when `(a : F) = (2 : F) ^ e`. -/
theorem axis_hmatch_of_zero_c_eq (env : Env F) (a : ℕ) (L : F) (e : ℕ)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (haL : (a : F) = L)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0)
    (heq : (a : F) = (2 : F) ^ e) :
    env.trace (col0 + 70) * (csum (F := F)).eval env = L := by
  have hcsum := csum_eval_of_zero_c env hCz
  calc
    env.trace (col0 + 70) * (csum (F := F)).eval env
        = env.trace (col0 + 70) * 1 := by rw [hcsum]
    _ = (2 : F) ^ e := by rw [mul_one, hT]
    _ = L := by rw [← haL, heq]

/-- Zeroed leftover `C` with `T · csum = L` contradicts `a ≠ 2^e`. -/
theorem axis_zero_c_excluded (env : Env F) (a : ℕ) (L : F) (e : ℕ)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (haL : (a : F) = L)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0)
    (hchar : ringChar F ≠ 0) (ha : a < ringChar F) (he : 2 ^ e < ringChar F)
    (hmatch : env.trace (col0 + 70) * (csum (F := F)).eval env = L)
    (hne : a ≠ 2 ^ e) : False := by
  apply hne
  exact leftover_nat_cast_inj (F := F) hchar ha he
    (axis_zero_c_pow_ne env a L e hT haL hCz hmatch)

/-- `(a : F) = (2 : F) ^ e` from `a = 2^e` without `rfl` on field powers. -/
theorem cast_eq_pow (a e : ℕ) (hmEq : a = 2 ^ e) : (a : F) = (2 : F) ^ e :=
  hmEq ▸ Nat.cast_pow (α := F) (m := 2) (n := e)

/-- Field equality of powers of two determines the exponents below `p`. -/
theorem two_pow_field_inj (hchar : ringChar F ≠ 0) {m n : ℕ}
    (hm : 2 ^ m < ringChar F) (hn : 2 ^ n < ringChar F)
    (heq : (2 : F) ^ m = (2 : F) ^ n) : m = n := by
  have hcast : ((2 ^ m : ℕ) : F) = ((2 ^ n : ℕ) : F) := by
    calc ((2 ^ m : ℕ) : F) = (2 : F) ^ m := Nat.cast_pow (α := F) (m := 2) (n := m)
      _ = (2 : F) ^ n := heq
      _ = ((2 ^ n : ℕ) : F) := (Nat.cast_pow (α := F) (m := 2) (n := n)).symm
  have hmod : (2 ^ m) % ringChar F = (2 ^ n) % ringChar F :=
    (CharP.natCast_eq_natCast (R := F) (p := ringChar F)).1 hcast
  have hnat : 2 ^ m = 2 ^ n := by
    rw [← Nat.mod_eq_of_lt hm, ← Nat.mod_eq_of_lt hn, hmod]
  exact (Nat.pow_right_injective (by decide : 1 < 2)) hnat

/-- Zeroed leftover `C` with `csum = 1` needs `L = T`; excluded below `p`. -/
theorem axis_pow_match_forbidden (env : Env F) (a : ℕ) (L : F) (e : ℕ)
    (_hnous : ¬ leftoverUseC (F := F) a = true)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (haL : (a : F) = L)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0)
    (hchar : ringChar F ≠ 0) (ha : a < ringChar F) (he : 2 ^ e < ringChar F)
    (hne : a ≠ 2 ^ e)
    (hmatch : env.trace (col0 + 70) * (csum (F := F)).eval env = L) : False := by
  apply hne
  exact leftover_nat_cast_inj (F := F) hchar ha he (by
    calc (a : F) = L := haL
      _ = env.trace (col0 + 70) * (csum (F := F)).eval env := hmatch.symm
      _ = (2 : F) ^ e := axis_match_gate_eq env e hT hCz
      _ = ((2 ^ e : ℕ) : F) := (Nat.cast_pow (α := F) (m := 2) (n := e)).symm)

/-- Zeroed leftover `C` with `L = (2 : F) ^ e` gives the axis `272`-match. -/
theorem axis_hmatch272_of_zero_c_le (env : Env F) (L : F) (e : ℕ)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0)
    (hLe : L = (2 : F) ^ e) :
    env.trace 272 * (csum (F := F)).eval env = L :=
  Eq.trans (axis_match272 env e hT hCz) (Eq.symm hLe)

/-- `L ≠ (2 : F) ^ e` but `T · csum = L` contradicts `T · csum = (2 : F) ^ e`. -/
theorem axis_hmatch272_zero_c_contra (env : Env F) (L : F) (e : ℕ)
    (h272 : env.trace 272 * (csum (F := F)).eval env = (2 : F) ^ e)
    (hLne : L ≠ (2 : F) ^ e)
    (htl : env.trace 272 * (csum (F := F)).eval env = L) : False :=
  hLne (Eq.trans (Eq.symm htl) h272)

/-- Close axis `272`-match from `axis_match272` when `L ≠ (2 : F) ^ e`. -/
theorem axis_hmatch272_zero_c_close (env : Env F) (L : F) (e : ℕ)
    (h272 : env.trace 272 * (csum (F := F)).eval env = (2 : F) ^ e)
    (hLne : L ≠ (2 : F) ^ e)
    (hmatch : env.trace 272 * (csum (F := F)).eval env = L) :
    env.trace 272 * (csum (F := F)).eval env = L :=
  False.elim (axis_hmatch272_zero_c_contra env L e h272 hLne hmatch)

/-- `x − y = 0` contradicts `x ≠ y`. -/
theorem eq_sub_zero_false_of_ne {x y : F} (hne : x ≠ y) (h : x - y = 0) : False :=
  hne (eq_of_sub_eq_zero h)

/-- Exfalso close for `x − y = 0` incompatible with `x ≠ y`. -/
theorem eq_sub_zero_of_ne {x y : F} (hne : x ≠ y) (h : x - y = 0) : x - y = 0 :=
  False.elim (eq_sub_zero_false_of_ne hne h)

/-- `x * y = 0` contradicts `x * y ≠ 0`. -/
theorem eq_mul_zero_false_of_ne {x y : F} (hne : x * y ≠ 0) (h : x * y = 0) : False :=
  hne h

/-- Exfalso close for `x * y = 0` incompatible with `x * y ≠ 0`. -/
theorem eq_mul_zero_of_ne {x y : F} (hne : x * y ≠ 0) (h : x * y = 0) : x * y = 0 :=
  False.elim (eq_mul_zero_false_of_ne hne h)

/-- powNe axis sub-goal: `L − 2^e = 0` from `L ≠ 2^e` via exfalso. -/
theorem axis_powNe_sub_zero {L : F} {e : ℕ} (hLne : L ≠ (2 : F) ^ e)
    (hsub : L - (2 : F) ^ e = 0) : L - (2 : F) ^ e = 0 :=
  eq_sub_zero_of_ne hLne hsub

/-- Dummy hexlow factor: `x · y = 0` from `x · y ≠ 0` via exfalso. -/
theorem axis_hexlow_mul_zero_exfalso {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hprod : x * y = 0) : x * y = 0 :=
  eq_mul_zero_of_ne (mul_ne_zero hx hy) hprod

/-- Close `L − 2^e = 0` under `L ≠ 2^e` by exfalso on the sub-goal. -/
theorem axis_powNe_sub_zero_close {L : F} {e : ℕ} (hLne : L ≠ (2 : F) ^ e)
    (hsub : L - (2 : F) ^ e = 0) : L - (2 : F) ^ e = 0 :=
  False.elim (eq_sub_zero_false_of_ne hLne hsub)

/-- Close a hexlow factor product under nonzero factors by exfalso. -/
theorem axis_hexlow_mul_zero_close {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hprod : x * y = 0) : x * y = 0 :=
  False.elim (eq_mul_zero_false_of_ne (mul_ne_zero hx hy) hprod)

/-- `x = 0` contradicts `x ≠ 0`. -/
theorem eq_zero_false_of_ne {x : F} (hne : x ≠ 0) (h : x = 0) : False :=
  hne h

/-- Exfalso close for `x = 0` incompatible with `x ≠ 0`. -/
theorem eq_zero_of_ne {x : F} (hne : x ≠ 0) (h : x = 0) : x = 0 :=
  False.elim (eq_zero_false_of_ne hne h)

/-- Contradiction for `axis_hmatch272_of_zero_c_ne`. -/
theorem axis_hmatch272_zero_c_ne_contra (env : Env F) (a : ℕ) (L : F) (e : ℕ)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (haL : (a : F) = L)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0)
    (hchar : ringChar F ≠ 0) (ha : a < ringChar F) (he : 2 ^ e < ringChar F)
    (hne : a ≠ 2 ^ e)
    (hmatch : env.trace 272 * (csum (F := F)).eval env = L) : False := by
  have h272 := axis_match272 env e hT hCz
  by_cases hLe : L = (2 : F) ^ e
  · apply hne
    have hcast : (a : F) = ((2 ^ e : ℕ) : F) :=
      calc (a : F) = L := haL
        _ = (2 : F) ^ e := hLe
        _ = ((2 ^ e : ℕ) : F) := (Nat.cast_pow (α := F) (m := 2) (n := e)).symm
    exact leftover_nat_cast_inj (F := F) hchar ha he hcast
  · apply hLe
    exact Eq.trans (Eq.symm hmatch) h272

/-- Zeroed leftover `C` with `a ≠ 2^e`: axis match contradicts below `p`. -/
theorem axis_hmatch272_of_zero_c_ne (env : Env F) (a : ℕ) (L : F) (e : ℕ)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (haL : (a : F) = L)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0)
    (hchar : ringChar F ≠ 0) (ha : a < ringChar F) (he : 2 ^ e < ringChar F)
    (hne : a ≠ 2 ^ e)
    (hmatch : env.trace 272 * (csum (F := F)).eval env = L) :
    env.trace 272 * (csum (F := F)).eval env = L :=
  (axis_hmatch272_zero_c_ne_contra env a L e hT haL hCz hchar ha he hne hmatch).elim

/-- Zeroed leftover `C` with live `T = 2^e`: axis `272`-match when `(a : F) = (2 : F) ^ e`. -/
theorem axis_hmatch272_zero_c (env : Env F) (a : ℕ) (L : F) (e : ℕ)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (haL : (a : F) = L)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0)
    (heq : (a : F) = (2 : F) ^ e) :
    env.trace 272 * (csum (F := F)).eval env = L := by
  have h272 := axis_match272 env e hT hCz
  exact Eq.trans h272 (Eq.symm (by rw [← haL, heq]))

/-- Zeroed leftover `C` with `a ≠ 2^e` contradicts any axis `272`-match below `p`. -/
theorem axis_hmatch272_zero_c_ne' (env : Env F) (a : ℕ) (L : F) (e : ℕ)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (haL : (a : F) = L)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0)
    (hchar : ringChar F ≠ 0) (ha : a < ringChar F) (he : 2 ^ e < ringChar F)
    (hne : a ≠ 2 ^ e)
    (hmatch : env.trace 272 * (csum (F := F)).eval env = L) : False :=
  axis_zero_c_excluded env a L e hT haL hCz hchar ha he hmatch hne

/-- From a live axis `272`-match, `L = (2 : F) ^ e`. -/
theorem axis272_l_eq_pow_of_hmatch (env : Env F) (L : F) (e : ℕ)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0)
    (hmatch272 : env.trace 272 * (csum (F := F)).eval env = L) :
    L = (2 : F) ^ e :=
  Eq.trans (Eq.symm hmatch272) (axis_match272 env e hT hCz)

/-- Zeroed leftover `C` with `a ≠ 2^e`: axis `272`-match from an explicit gate match. -/
theorem axis272Match_of_zero_c_ne (env : Env F) (a : ℕ) (L : F) (e : ℕ)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (haL : (a : F) = L)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0)
    (hchar : ringChar F ≠ 0) (ha : a < ringChar F) (he : 2 ^ e < ringChar F)
    (hne : a ≠ 2 ^ e)
    (hmatch : env.trace 272 * (csum (F := F)).eval env = L) :
    env.trace 272 * (csum (F := F)).eval env = L := by
  classical
  rcases eq_or_ne a (2 ^ e) with heq | hneq
  · exact axis_hmatch272_zero_c env a L e hT haL hCz (cast_eq_pow a e heq)
  · exact (hneq (leftover_nat_cast_inj hchar ha he
      (axis_zero_c_pow_ne env a L e hT haL hCz
        (axis_hmatch272_to_col0 env L hmatch)))).elim

/-- Close axis `272`-match when `L ≠ (2 : F) ^ e` but the match is assumed. -/
theorem axis_hmatch272_close_hLe_false (env : Env F) (L : F) (e : ℕ)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0)
    (hLe : L ≠ (2 : F) ^ e)
    (hmatch272 : env.trace 272 * (csum (F := F)).eval env = L) :
    env.trace 272 * (csum (F := F)).eval env = L :=
  False.elim (hLe (Eq.trans (Eq.symm hmatch272) (axis_match272 env e hT hCz)))

/-- `L ≠ (2 : F) ^ e` with a live axis `272`-match contradicts `T · csum = (2 : F) ^ e`. -/
theorem axis_hmatch272_close_of_cast_ne_contra (env : Env F) (a : ℕ) (L : F) (e : ℕ)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (haL : (a : F) = L)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0)
    (hchar : ringChar F ≠ 0) (ha : a < ringChar F) (he : 2 ^ e < ringChar F)
    (hne : a ≠ 2 ^ e) (hLne : L ≠ (2 : F) ^ e) (hnePow : (a : F) ≠ (2 : F) ^ e)
    (hmatch : env.trace 272 * (csum (F := F)).eval env = L) : False := by
  apply hLne
  by_cases hp : (a : F) = (2 : F) ^ e
  · exact False.elim (hnePow hp)
  · exact Eq.trans (Eq.symm hmatch) (axis_match272 env e hT hCz)

/-- Close axis `272`-match on the `L ≠ (2 : F) ^ e` branch from cast mismatch. -/
theorem axis_hmatch272_close_of_cast_ne (env : Env F) (a : ℕ) (L : F) (e : ℕ)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (haL : (a : F) = L)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0)
    (hchar : ringChar F ≠ 0) (ha : a < ringChar F) (he : 2 ^ e < ringChar F)
    (hne : a ≠ 2 ^ e) (hLne : L ≠ (2 : F) ^ e) (hnePow : (a : F) ≠ (2 : F) ^ e)
    (hmatch272 : env.trace 272 * (csum (F := F)).eval env = L) :
    env.trace 272 * (csum (F := F)).eval env = L := by
  exact axis_hmatch272_close_hLe_false env L e hT hCz hLne hmatch272

/-- Close axis `272`-match when `a = ringChar F` (no strict `a < ringChar` input). -/
theorem axis_hmatch272_close_of_cast_eq_mod (env : Env F) (a : ℕ) (L : F) (e : ℕ)
    (hT : env.trace (col0 + 70) = (2 : F) ^ e)
    (haL : (a : F) = L)
    (hCz : ∀ j, j < 63 → env.trace (col0 + j) = 0)
    (hchar : ringChar F ≠ 0) (hapChar : a = ringChar F) (he : 2 ^ e < ringChar F)
    (hne : a ≠ 2 ^ e) (hLne : L ≠ (2 : F) ^ e) (hnePow : (a : F) ≠ (2 : F) ^ e)
    (hmatch272 : env.trace 272 * (csum (F := F)).eval env = L) :
    env.trace 272 * (csum (F := F)).eval env = L := by
  exact axis_hmatch272_close_hLe_false env L e hT hCz hLne hmatch272

/-- At `formRN = 63`, the dummy shift is `62`. -/
theorem nMinus1Low_eq_62_of_formRN63 (h63 : formRN F = 63) : nMinus1Low F = 62 := by
  unfold nMinus1Low
  rw [h63]

/-- `N ≤ 62`, `N ≠ 63`, and `63 < formRN`: field powers of two differ at `2^63`. -/
theorem two_pow_field_ne_pow63_of_le62 (hchar : ringChar F ≠ 0) {N : ℕ}
    (hN62 : N ≤ 62) (hfn : 63 < formRN F) (hN63 : N ≠ 63) :
    (2 : F) ^ N ≠ (2 : F) ^ 63 := fun heq =>
  hN63 <|
    two_pow_field_inj hchar
      (lt_trans (Nat.pow_lt_pow_right (by decide : (1 : ℕ) < 2)
        (Nat.lt_succ_of_le hN62)) (two_pow_63_lt_ringChar hchar hfn))
      (two_pow_63_lt_ringChar hchar hfn) heq

/-- At `formRN = 63`, dummy `N = nMinus1Low = 62` stays below `2^63`. -/
theorem two_pow_field_ne_pow63_at_formRN63 (h2 : (2 : F) ≠ 0) (h63 : formRN F = 63)
    {N : ℕ} (hN : N = nMinus1Low F) :
    (2 : F) ^ N ≠ (2 : F) ^ 63 := by
  rw [hN, nMinus1Low_eq_62_of_formRN63 h63]
  intro heq
  have htwo : (2 : F) = (1 : F) + 1 := by norm_num
  have h21 : (2 : F) ≠ 1 := fun h => by
    have h11 : (1 : F) + 1 = (1 : F) := by rw [← htwo, h]
    have hone : (1 : F) = 0 := by
      calc (1 : F)
          = (1 : F) + 0 := (add_zero _).symm
        _ = (1 : F) + ((1 : F) + -(1 : F)) := by rw [add_neg_cancel]
        _ = ((1 : F) + (1 : F)) + -(1 : F) := by rw [add_assoc]
        _ = (1 : F) + -(1 : F) := by rw [h11]
        _ = 0 := add_neg_cancel (1 : F)
    exact h2 (by rw [h, hone])
  have hpow62 : (2 : F) ^ 62 ≠ 0 := pow_ne_zero 62 h2
  have hone : (2 : F) - 1 ≠ 0 := fun h => h21 (sub_eq_zero.mp h)
  have hmul : (2 : F) * (2 : F) ^ 62 = (2 : F) ^ 63 := by
    rw [mul_comm, ← pow_succ (2 : F) 62]
  have hz : (2 : F) ^ 62 * ((2 : F) - 1) = 0 := by
    have hstep : (2 : F) ^ 62 * 2 = (2 : F) ^ 63 := by rw [mul_comm, hmul]
    rw [mul_sub, mul_one, hstep, heq, sub_self]
  exact hpow62 ((mul_eq_zero.mp hz).resolve_right hone)

end OptimizedComputeRangeCertificate
end Nock.NockVMROM.Thm54
