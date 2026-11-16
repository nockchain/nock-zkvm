/-
  Nock/RedTeam/Batch550Thm54TopBitModel.lean

  **Design (i) "certified top bit" on the `MTree` model: the ASCENDING rule computes
  the BIT-REVERSED address, so the memory chip verifies `/[rev(a) R]` when the compute chip asks
  for `/[a R]`.**

  The brief claims the
  ascending rule "computes at every node `counts_X = Σ w·P^X_leaf(λ)`" with `P` the ROOT-ADDRESS
  polynomial (`λ^depth` + path bits, LSB = the edge into the node).

  It does not.  Going up one edge `e` maps a leaf's polynomial `A ↦ λ·A + e`, so the edge OUT OF
  THE ANCESTOR lands at `λ⁰` and the edge INTO THE LEAF at `λ^{depth−1}`: the ascending functional
  is the bit-REVERSED path polynomial (`ascending_is_reversed`, `embed_countsA`).  The compute
  side's `a_λ = Σ bᵢλⁱ` is the STANDARD one (`:1288-1291`: `2·axis + bit`, the newest edge is the
  LSB), so:

  * `honest_five_rejected` — the honest lookup `/[5 S]` (read at the root, verify at left-then-
    right, `T = λ²`, `a_λ = λ² + 1`) has root polynomial `(λ − 1)·ts ≠ 0`: REJECTED for every
    `λ ≠ 1`.  Completeness fails on every non-palindromic axis.
  * `forged_six_for_five` — the same record served by a verify at `/[6 S]` (right-then-left) has
    root polynomial `0` IDENTICALLY in `λ`: ACCEPTED for every `λ`, every `T`.  `/[5 S] ≠ /[6 S]`
    (`slot_five_ne_six`).  This is a forgery with NO event.
  * `root_read_reversed` — the family: under a root read the design checks `a_λ = revAddr(path)`,
    `T` cancels, and the only accepted verify for a certified `a` sits at the bit-reversal of `a`.
  * Item E — the FOREST-level check `Σ_roots counts + E = 0` (which replaced the per-root
    `rootMask·counts = 0`) accepts a read in one root and the verify in ANOTHER root
    (`cross_root_forgery`): the root-relative identity cannot see which root a node is in.

  Variant (i') (one-hot activation) has the same memory side and the same `E`, so every theorem
  here applies to it verbatim (`T`, `a_λ` are opaque record values in this file).
-/
import Nock.RedTeam.Batch546Thm54LambdaModel

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch550

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.RedTeam.Batch546 (axisL)
open Polynomial

variable {K : Type*} [Field K]

/-! ## Design (i) on `MTree`

The record's `𝕂` fields are keyed by the timestamp exponent: `T e` is the certified top-bit
power of record `e`, and the verify node's stored field is read as that record's `a_λ`.  Timestamps are
`X^e` (`X = α`, `:1413`). -/

/-- `axis_indicator` under design (i): `verify_child` adds `ts`, the `read_root` wrapper subtracts
`T·ts`, `decompose` sums (`ind_P = ind_L + ind_R`). -/
noncomputable def indA (T : ℕ → K) : MTree K → K[X]
  | .halt => 0
  | .decompose L R => indA T L + indA T R
  | .read e c => indA T c - C (T e) * X ^ e
  | .verify e _ c => indA T c + X ^ e

/-- `axis_counts` under design (i): the ASCENDING rule
`counts_P = λ·(counts_L + counts_R) + ind_R`; `verify_child` adds `ts`; the `read_root` wrapper
subtracts `T·ts`. -/
noncomputable def countsA (l : K) (T : ℕ → K) : MTree K → K[X]
  | .halt => 0
  | .decompose L R => C l * (countsA l T L + countsA l T R) + indA T R
  | .read e c => countsA l T c - C (T e) * X ^ e
  | .verify e _ c => countsA l T c + X ^ e

/-- The compute-side accumulator `E = Σ_records ts·(T − a_λ)`, collected here at the verify node
that carries the record's `a_λ`. -/
noncomputable def Eacc (T : ℕ → K) : MTree K → K[X]
  | .halt => 0
  | .decompose L R => Eacc T L + Eacc T R
  | .read _ c => Eacc T c
  | .verify e a c => Eacc T c + C (T e - a) * X ^ e

/-- The root identity of design (i) for one tree: `counts_root + E = 0`. -/
noncomputable def rootPoly (l : K) (T : ℕ → K) (t : MTree K) : K[X] :=
  countsA l T t + Eacc T t

/-! ## Item C — what the ascending rule computes -/

/-- Place a subtree at the end of a top-down path (`false` = left, `true` = right), with `halt`
siblings.  By linearity of every rule this is the general case for one leaf. -/
def embed : List Bool → MTree K → MTree K
  | [], t => t
  | false :: p, t => .decompose (embed p t) .halt
  | true :: p, t => .decompose .halt (embed p t)

/-- The polynomial the ascending rule attaches to a top-down path: `A(e :: p) = λ·A(p) + e`,
`A([]) = 1`.  The edge OUT OF THE ANCESTOR (`p.head`) sits at `λ⁰`; the edge INTO THE LEAF at
`λ^{depth−1}`.  This is the bit-REVERSAL of the paper's address. -/
def revAddr (l : K) : List Bool → K
  | [] => 1
  | e :: p => l * revAddr l p + (if e then 1 else 0)

/-- The paper's address polynomial of a top-down path (`:1288-1291`, `axis ↦ 2·axis + bit` with
`2 ↦ λ`): the edge INTO THE LEAF is the LSB.  It is `revAddr` of the reversed path. -/
def stdAddr (l : K) (p : List Bool) : K := revAddr l p.reverse

theorem indA_embed (T : ℕ → K) (p : List Bool) (t : MTree K) :
    indA T (embed p t) = indA T t := by
  induction p with
  | nil => rfl
  | cons e p ih => cases e <;> simp [embed, indA, ih]

/-- **The ascending functional, exactly, for every weight sign.**  A leaf with `(counts, ind) =
(c, w)` at the end of path `p` contributes `λ^{|p|}·c + (revAddr p − λ^{|p|})·w` at the top —
i.e. `w·revAddr p` when `c = w` (a verify: `w = ts`; a read wrapper: `w = −T·ts`). -/
theorem countsA_embed (l : K) (T : ℕ → K) (p : List Bool) (t : MTree K) :
    countsA l T (embed p t)
      = C (l ^ p.length) * countsA l T t + C (revAddr l p - l ^ p.length) * indA T t := by
  induction p with
  | nil => simp [embed, revAddr]
  | cons e p ih =>
      cases e
      · simp only [embed, countsA, indA, ih, revAddr, List.length_cons]
        simp only [Bool.false_eq_true, if_false, add_zero, C_mul, C_sub, C_pow, pow_succ]
        ring
      · simp only [embed, countsA, ih, revAddr, List.length_cons, indA_embed]
        simp only [if_true, C_mul, C_sub, C_add, C_pow, C_1, pow_succ]
        ring

/-- The ascending rule is the reversed address, not the paper's: at path `[left, right]`
(`/[5]`) it yields `λ² + λ` (= the bits of `6`), while the address polynomial is `λ² + 1`. -/
theorem ascending_is_reversed (l : K) :
    revAddr l [false, true] = l ^ 2 + l ∧ stdAddr l [false, true] = l ^ 2 + 1 := by
  constructor <;> simp [revAddr, stdAddr] <;> ring

/-! ## The root-read family: `T` cancels and the check is `a_λ = revAddr(path)` -/

theorem Eacc_embed (T : ℕ → K) (e : ℕ) (a : K) (p : List Bool) :
    Eacc T (embed p (.verify e a .halt)) = C (T e - a) * X ^ e := by
  induction p with
  | nil => simp [embed, Eacc]
  | cons b p ih => cases b <;> simp [embed, Eacc, ih]

/-- Under a `read_root` at the root of a tree, one record verified at the end of path `p` has
root polynomial `(revAddr p − a_λ)·ts`, for EVERY `T`. -/
theorem root_read_reversed (l : K) (T : ℕ → K) (e : ℕ) (a : K) (p : List Bool) :
    rootPoly l T (.read e (embed p (.verify e a .halt)))
      = C (revAddr l p - a) * X ^ e := by
  simp only [rootPoly, countsA, Eacc, Eacc_embed, countsA_embed, indA]
  simp only [C_sub, C_pow]
  ring

theorem axisL_five (l : K) (n : ℕ) (hn : 3 ≤ n) : axisL l n 5 = l ^ 2 + 1 := by
  unfold axisL
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  have h0 : Nat.testBit 5 0 = true := by decide
  have h1 : Nat.testBit 5 1 = false := by decide
  have h2 : Nat.testBit 5 2 = true := by decide
  have hhi : ∀ i, Nat.testBit 5 (i + 1 + 1 + 1) = false := fun i =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ i + 1 + 1 + 1)))
  simp [h0, h1, h2, hhi]

theorem axisL_six (l : K) (n : ℕ) (hn : 3 ≤ n) : axisL l n 6 = l ^ 2 + l := by
  unfold axisL
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  have h0 : Nat.testBit 6 0 = false := by decide
  have h1 : Nat.testBit 6 1 = true := by decide
  have h2 : Nat.testBit 6 2 = true := by decide
  have hhi : ∀ i, Nat.testBit 6 (i + 1 + 1 + 1) = false := fun i =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ i + 1 + 1 + 1)))
  simp [h0, h1, h2, hhi]

/-- **Completeness break.**  The honest lookup `/[5 S]`: `read_root` at the root, `verify_child`
at the left child's right child, certificate `a = 5` (`T = λ²`, `a_λ = λ² + 1`).  Root polynomial
`(λ − 1)·ts`: rejected for every `λ ≠ 1`. -/
theorem honest_five_rejected (l : K) (e : ℕ) :
    rootPoly l (fun _ => l ^ 2) (.read e (embed [false, true] (.verify e (axisL l 63 5) .halt)))
      = C (l - 1) * X ^ e
    ∧ (l ≠ 1 →
        rootPoly l (fun _ => l ^ 2)
          (.read e (embed [false, true] (.verify e (axisL l 63 5) .halt))) ≠ 0) := by
  rw [root_read_reversed, axisL_five l 63 (by norm_num)]
  have h : revAddr l [false, true] - (l ^ 2 + 1) = l - 1 := by simp [revAddr]; ring
  refine ⟨by rw [h], fun hl h0 => ?_⟩
  rw [h] at h0
  have hX : (X ^ e : K[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hC : C (l - 1) = (0 : K[X]) := (mul_eq_zero.mp h0).resolve_right hX
  exact hl (sub_eq_zero.mp (C_eq_zero.mp hC))

/-- **Soundness break, no event.**  The same record (`a = 5`, `T = λ²`, `a_λ = λ² + 1`) served
by a `verify_child` at the RIGHT child's LEFT child — `/[6 S]` — has root polynomial `0` for
every `λ`.  The memory chip verifies the bit-reversal of the certified axis. -/
theorem forged_six_for_five (l : K) (e : ℕ) :
    rootPoly l (fun _ => l ^ 2)
      (.read e (embed [true, false] (.verify e (axisL l 63 5) .halt))) = 0 := by
  rw [root_read_reversed, axisL_five l 63 (by norm_num)]
  have h : revAddr l [true, false] - (l ^ 2 + 1) = 0 := by simp [revAddr]; ring
  rw [h, C_0, zero_mul]

/-- The mirror: certificate `a = 6` is accepted exactly at `/[5 S]`. -/
theorem forged_five_for_six (l : K) (e : ℕ) :
    rootPoly l (fun _ => l ^ 2)
      (.read e (embed [false, true] (.verify e (axisL l 63 6) .halt))) = 0 := by
  rw [root_read_reversed, axisL_six l 63 (by norm_num)]
  have h : revAddr l [false, true] - (l ^ 2 + l) = 0 := by simp [revAddr]; ring
  rw [h, C_0, zero_mul]

/-- `/[5 S] = v ≠ x = /[6 S]` on `S = [[u v] [x y]]`: the accepted claim is false. -/
theorem slot_five_ne_six (u v x y : ℕ) (h : v ≠ x) :
    let S := Noun.cell (Noun.cell (Noun.atom u) (Noun.atom v))
      (Noun.cell (Noun.atom x) (Noun.atom y))
    Noun.slot 5 S = some (Noun.atom v) ∧ Noun.slot 6 S = some (Noun.atom x)
      ∧ Noun.slot 5 S ≠ Noun.slot 6 S := by
  intro S
  refine ⟨by simp [S, Noun.slot], by simp [S, Noun.slot], ?_⟩
  simp [S, Noun.slot]
  exact h

/-- The general shape of the break: for a root read the accepted verify position is the
bit-reversal of the certified path, and honest completeness holds only on palindromes.  For
`p = [false, true]` versus its reverse: both facts in one statement. -/
theorem reversal_family (l : K) (T : ℕ → K) (e : ℕ) (p : List Bool) :
    rootPoly l T (.read e (embed p.reverse (.verify e (stdAddr l p) .halt))) = 0
    ∧ rootPoly l T (.read e (embed p (.verify e (stdAddr l p) .halt)))
        = C (revAddr l p - revAddr l p.reverse) * X ^ e := by
  constructor
  · rw [root_read_reversed]; simp [stdAddr]
  · rw [root_read_reversed]; rfl

/-! ## Item A — the traces that broke D-λ are rejected by (i) as stated -/

theorem t1_rejected (l : K) (e : ℕ) :
    rootPoly l (fun _ => 1) (Batch546.t1 e (axisL l 63 1)) = C (l ^ 2 - 1) * X ^ e := by
  rw [Batch546.axisL_one l 63 (by norm_num)]
  simp only [rootPoly, Batch546.t1, countsA, indA, Eacc, C_sub, C_pow, C_1]
  ring

/-- `Batch546.t2` (`a = 2`, `T = λ`, verify at `/[6]` of the left child): root polynomial
`λ²(λ − 1)·ts`. -/
theorem t2_rejected (l : K) (e : ℕ) :
    rootPoly l (fun _ => l) (Batch546.t2 e (axisL l 63 2)) = C (l ^ 2 * (l - 1)) * X ^ e := by
  rw [Batch546.axisL_two l 63 (by norm_num)]
  simp only [rootPoly, Batch546.t2, countsA, indA, Eacc, C_sub, C_pow, C_mul, C_1]
  ring

/-- `Batch546.tfull` (honest `(S, w, 3, ts₁)` stacked at the root, forged `(w, v, 1, ts₂)` read
at the tail and verified at the head's tail): root polynomial `(λ² − 1)·ts₂`. -/
theorem tfull_rejected (l : K) (e₁ e₂ : ℕ) (hne : e₁ ≠ e₂) :
    rootPoly l (fun e => if e = e₁ then l else 1)
      (Batch546.tfull e₁ e₂ (axisL l 63 3) (axisL l 63 1)) = C (l ^ 2 - 1) * X ^ e₂ := by
  rw [Batch546.axisL_three l 63 (by norm_num), Batch546.axisL_one l 63 (by norm_num)]
  simp only [rootPoly, Batch546.tfull, countsA, indA, Eacc, if_true, if_neg (Ne.symm hne),
    C_sub, C_pow, C_add, C_1]
  ring

/-- These polynomials are nonzero: `t1`/`tfull` are rejected for `λ ∉ {1, −1}`, `t2` for
`λ ∉ {0, 1}`. -/
theorem old_forgeries_rejected (l : K) (e : ℕ) (hl1 : l ≠ 1) (hl2 : l ≠ -1) (hl0 : l ≠ 0) :
    rootPoly l (fun _ => 1) (Batch546.t1 e (axisL l 63 1)) ≠ 0
    ∧ rootPoly l (fun _ => l) (Batch546.t2 e (axisL l 63 2)) ≠ 0 := by
  have hX : (X ^ e : K[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have h2 : l ^ 2 - 1 ≠ 0 := by
    intro h
    have : (l - 1) * (l + 1) = 0 := by ring_nf; ring_nf at h; linear_combination h
    rcases mul_eq_zero.mp this with h | h
    · exact hl1 (sub_eq_zero.mp h)
    · exact hl2 (eq_neg_of_add_eq_zero_left h)
  constructor
  · rw [t1_rejected]
    exact mul_ne_zero (by rwa [Ne, C_eq_zero]) hX
  · rw [t2_rejected]
    refine mul_ne_zero ?_ hX
    rw [Ne, C_eq_zero]
    exact mul_ne_zero (pow_ne_zero _ hl0) (sub_ne_zero.mpr hl1)

/-! ## Item E — the forest-level check accepts a read in one root and its verify in another -/

/-- Design (i) replaces the per-root `rootMask·counts = 0` by ONE forest sum
`Σ_roots counts_root = −E_pub`. -/
noncomputable def forestPoly (l : K) (T : ℕ → K) (F : List (MTree K)) : K[X] :=
  (F.map (rootPoly l T)).sum

/-- **Cross-root forgery.**  Root 1 is a bare `read_root` wrapper over the subject `S₁`; root 2
holds the `verify_child` at the end of path `p` of a DIFFERENT subject `S₂`.  With the
certificate's `a_λ` set to `revAddr p` (i.e. the bits of the reversed path — a valid boolean
certificate) the forest polynomial is `0` for every `λ` and every `T`: the claim
`/[a S₁] = (node of S₂)` is accepted.  The root-relative identity has no root name in it. -/
theorem cross_root_forgery (l : K) (T : ℕ → K) (e : ℕ) (p : List Bool) (S₁ : MTree K) :
    (∀ e', readCount e' S₁ = 0) → (∀ e', verifyCount e' S₁ = 0) →
    forestPoly l T [.read e S₁, embed p (.verify e (revAddr l p) .halt)] = 0 := by
  intro hr hv
  have hcS : countsA l T S₁ = 0 ∧ indA T S₁ = 0 ∧ Eacc T S₁ = 0 := by
    induction S₁ with
    | halt => simp [countsA, indA, Eacc]
    | decompose L R ihl ihr =>
        have hrl : ∀ e', readCount e' L = 0 := fun e' => by
          have := hr e'; simp only [readCount] at this; omega
        have hrr : ∀ e', readCount e' R = 0 := fun e' => by
          have := hr e'; simp only [readCount] at this; omega
        have hvl : ∀ e', verifyCount e' L = 0 := fun e' => by
          have := hv e'; simp only [verifyCount] at this; omega
        have hvr : ∀ e', verifyCount e' R = 0 := fun e' => by
          have := hv e'; simp only [verifyCount] at this; omega
        obtain ⟨h1, h2, h3⟩ := ihl hrl hvl
        obtain ⟨h4, h5, h6⟩ := ihr hrr hvr
        simp [countsA, indA, Eacc, h1, h2, h3, h4, h5, h6]
    | read e' c _ => have := hr e'; simp [readCount] at this
    | verify e' _ c _ => have := hv e'; simp [verifyCount] at this
  obtain ⟨h1, h2, h3⟩ := hcS
  simp only [forestPoly, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    rootPoly, countsA, Eacc, h1, h3, Eacc_embed, countsA_embed, indA, zero_sub]
  simp only [C_sub, C_pow]
  ring

/-- The two roots are disjoint trees: the read of `e` is in root 1 only and the verify of `e` in
root 2 only. -/
theorem cross_root_split (e : ℕ) (p : List Bool) (a : K) (S₁ : MTree K)
    (hr : ∀ e', readCount e' S₁ = 0) (hv : ∀ e', verifyCount e' S₁ = 0) :
    readCount e (.read e S₁) = 1 ∧ verifyCount e (.read e S₁) = 0
    ∧ readCount e (embed p (.verify e a .halt)) = 0
    ∧ verifyCount e (embed p (.verify e a .halt)) = 1 := by
  refine ⟨by simp [readCount, hr], by simp [verifyCount, hv], ?_, ?_⟩
  · induction p with
    | nil => simp [embed, readCount]
    | cons b p ih => cases b <;> simp [embed, readCount, ih]
  · induction p with
    | nil => simp [embed, verifyCount]
    | cons b p ih => cases b <;> simp [embed, verifyCount, ih]

end Nock.RedTeam.Batch550

#print axioms Nock.RedTeam.Batch550.countsA_embed
#print axioms Nock.RedTeam.Batch550.honest_five_rejected
#print axioms Nock.RedTeam.Batch550.forged_six_for_five
#print axioms Nock.RedTeam.Batch550.slot_five_ne_six
#print axioms Nock.RedTeam.Batch550.tfull_rejected
#print axioms Nock.RedTeam.Batch550.old_forgeries_rejected
#print axioms Nock.RedTeam.Batch550.cross_root_forgery
