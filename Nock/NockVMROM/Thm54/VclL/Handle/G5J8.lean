/-
  Nock/NockVMROM/Thm54/VclL/Handle/G5J8.lean

  **The real g5 shape — the atom table's leaf coordinate at
  `y` of a denoted row is `leafVal y (val l)`, hence `AtomLeaves (encZY z y)` at the exported rows.**

  The atom table is a cell table over limbs whose structure coin is `y` (`AtomChipHQ.atomTable_accepts`: T1 at
  `y`).  A row denoting the limb list `l` (`AtomChipHQ.Denotes`: the right comb `[l₀ [l₁ … [l_{k−1} l_k]]]`) has, at
  `y`, the fingerprint of that comb, whose LEAF coordinate is the limb polynomial at `y`; the bivariate encoder
  `encZY` reads an atom `v` at `leafVal y v` (A-1: the limb polynomial of `limbs v` for a big atom).  They agree:

  * §1 `horner y l = Σ lᵢ yⁱ`; **`aeval_limbPoly`** (`aeval y (limbPoly l) = horner y l`);
    **`horner_limbs_val`** (bounded limbs: trailing zero limbs do not change `horner`, so
    `horner y (limbs (val l)) = horner y l` with NO canonicity premise); **`leafVal_val`**
    (`p ≤ val l` ⇒ `leafVal y (val l) = horner y l`).
  * §2 `combL l` (the right comb `Denotes` describes); **`comb_leaf`**: under any encoder with inline limbs
    (`E (atom a) = atomFP y a`) and `cons` at `y`, `(E (combL l)).leaf = horner y l`.
  * §3 **`leaf_eq_leafVal`** (the two together) and **`atomLeaves_of_rows`**: an export list whose keys are
    `(⟨z, 0, (E_y (combL l)).leaf⟩, 0, 0, idx)` with `l` bounded, `p ≤ val l` (g4, exported rows) and
    `ext idx = atom (val l)` (`extA` restricted to exported rows) is `AtomLeaves (encZY z y)` — `atomLeaves_of_g5`
    at `ext = extA`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.G5J8

open Nock Nock.Atoms Polynomial
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY atomLeaves_of_g5)

noncomputable section

/-! ## 1. The limb polynomial at `y` -/

section Horner
variable {K : Type} [Field K]

/-- `Σ lᵢ yⁱ` in Horner form. -/
def horner (y : K) : List ℕ → K
  | [] => 0
  | a :: l => (a : K) + y * horner y l

variable [Algebra Fp K]

theorem aeval_limbPoly (y : K) (l : List ℕ) : aeval y (limbPoly l) = horner y l := by
  induction l with
  | nil => simp [limbPoly, natPoly, horner]
  | cons a l ih =>
    rw [horner, ← ih]
    simp [limbPoly, natPoly, Polynomial.map_add, Polynomial.map_mul]

/-- **Trailing zero limbs do not move `horner`**: for bounded limbs, `horner y (limbs (val l)) = horner y l`. -/
theorem horner_limbs_val (y : K) {l : List ℕ} (hl : ∀ a ∈ l, a < B) : horner y (limbs (val l)) = horner y l := by
  induction l with
  | nil => simp [limbs, horner]
  | cons a l ih =>
    have ih' := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have ha : a < B := hl a (List.mem_cons_self ..)
    rw [val_cons]
    by_cases h0 : a = 0 ∧ val l = 0
    · obtain ⟨rfl, hv⟩ := h0
      rw [hv] at ih'
      simp only [limbs, Nat.digits_zero, horner, Nat.cast_zero, zero_add] at ih' ⊢
      rw [hv, Nat.mul_zero, Nat.digits_zero, horner, ← ih']
      simp
    · have hxy : a ≠ 0 ∨ val l ≠ 0 := by
        by_contra hc; push Not at hc; exact h0 hc
      rw [limbs, Nat.digits_add B one_lt_B a (val l) ha hxy, horner, horner]
      rw [← ih']; rfl

variable [Fintype K] [DecidableEq K]

/-- **`leafVal` of a big value is the limb polynomial at `y`** of any bounded limb list of that value. -/
theorem leafVal_val (y : K) {l : List ℕ} (hl : ∀ a ∈ l, a < B) (hbig : p ≤ val l) :
    leafVal y (val l) = horner y l := by
  unfold leafVal L
  rw [if_neg (by omega), aeval_limbPoly, horner_limbs_val y hl]

end Horner

/-! ## 2. The comb's leaf coordinate -/

/-- **The right comb of a limb list** (`[l₀ [l₁ … [l_{k−1} l_k]]]`, as `AtomChipHQ.Denotes`). -/
def combL : List ℕ → Noun
  | [] => .atom 0
  | [a] => .atom a
  | a :: b :: l => .cell (.atom a) (combL (b :: l))

section Comb
variable {K : Type} [Field K]

/-- **The comb's leaf coordinate at `y`** under an encoder with inline limbs and `cons` at `y`. -/
theorem comb_leaf (E : Noun → FP K) (y : K) (hc : ∀ u v, E (.cell u v) = FP.cons y (E u) (E v)) :
    ∀ (l : List ℕ), l ≠ [] → (∀ a ∈ l, E (.atom a) = FP.atomFP y (a : K)) → (E (combL l)).leaf = horner y l
  | [], h, _ => absurd rfl h
  | [a], _, hE => by rw [combL, hE a (by simp)]; simp [horner]
  | a :: b :: l, _, hE => by
    rw [combL, hc, hE a (by simp)]
    have ih := comb_leaf E y hc (b :: l) (by simp) fun x hx => hE x (List.mem_cons_of_mem _ hx)
    simp only [FP.cons, FP.atomFP_leaf, FP.atomFP_size, ih, horner]

end Comb

/-! ## 3. The g5 shape at `extA` -/

section G5
variable {K : Type} [Field K] [Algebra Fp K] [Fintype K] [DecidableEq K]

/-- **The atom leaf coordinate at `y` of a denoted (big) row is `leafVal y (val l)`.** -/
theorem leaf_eq_leafVal (E : Noun → FP K) (y : K) (hc : ∀ u v, E (.cell u v) = FP.cons y (E u) (E v))
    {l : List ℕ} (hne : l ≠ []) (hE : ∀ a ∈ l, E (.atom a) = FP.atomFP y (a : K)) (hl : ∀ a ∈ l, a < B)
    (hbig : p ≤ val l) : (E (combL l)).leaf = leafVal y (val l) := by
  rw [comb_leaf E y hc l hne hE, leafVal_val y hl hbig]

/-- **`AtomLeaves (encZY z y)` from the atom table's export keys**: every key is `(⟨z, 0, (E_y (combL l)).leaf⟩, 0, 0,
idx)` for the limb list `l = lim idx` of its row (inline limbs `< B`, `p ≤ val l`: g4 on exported rows) and
`ext idx = atom (val l)` (`extA` on exported rows). -/
theorem atomLeaves_of_rows (z y : K) (E : Noun → FP K) (hc : ∀ u v, E (.cell u v) = FP.cons y (E u) (E v))
    {vp : List (VKey K)} {ext : ℕ → Option Noun} (lim : ℕ → List ℕ)
    (h : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.1 = FP.atomFP z (E (combL (lim k.2.2.2))).leaf ∧
      lim k.2.2.2 ≠ [] ∧ (∀ a ∈ lim k.2.2.2, E (.atom a) = FP.atomFP y (a : K)) ∧ (∀ a ∈ lim k.2.2.2, a < B) ∧
      p ≤ val (lim k.2.2.2) ∧ ext k.2.2.2 = some (.atom (val (lim k.2.2.2)))) :
    AtomLeaves (encZY z y) vp ext := by
  refine atomLeaves_of_g5 z y fun k hk => ?_
  obtain ⟨h1, h2, h3, hne, hE, hl, hbig, hx⟩ := h k hk
  exact ⟨h1, h2, _, hx, by rw [h3, leaf_eq_leafVal E y hc hne hE hl hbig]⟩

end G5

end

end Nock.NockVMROM.Thm54.VclL.Handle.G5J8
