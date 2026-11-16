/-
  Nock/Atoms/Limbs.lean

  **The canonical limb encoding of big atoms.**

  An atom
  `n` is SMALL iff `n < p` (Goldilocks, `Nock.Field.p`) and BIG iff `n ≥ p`; a big atom is the
  canonical little-endian base-`B = 2^32` limb list: every limb `< B`, top limb `≠ 0`.

  * `B`, `limbs n := Nat.digits B n`, `val l := Nat.ofDigits B l`, `Canonical l`.
  * Round trip `val_limbs`, `limbs_canonical`, `limbs_val` (a canonical list is the limbs of its
    value) and `canonical_unique` (uniqueness of the canonical representation).
  * Boundary: `limbs_p : limbs p = [1, B − 1]`, `limbs_p_sub_one : limbs (p − 1) = [0, B − 1]`;
    `two_le_length_of_big` (a big atom has at least two limbs); `big_iff` (the Goldilocks form of
    the boundary gate (iv): for a canonical `l`, `p ≤ val l ↔ 3 ≤ len ∨ (len = 2 ∧ l₁ = B − 1 ∧
    1 ≤ l₀)`).
-/
import Mathlib.Data.Nat.Digits.Lemmas
import Nock.Field

set_option autoImplicit false

namespace Nock.Atoms

/-- The limb base `B = 2^32`. -/
def B : ℕ := 2 ^ 32

theorem B_eq : B = 4294967296 := by norm_num [B]

theorem one_lt_B : 1 < B := by norm_num [B]

/-- The Goldilocks prime, `p = 2^64 − 2^32 + 1` (`Nock.Field.p`). -/
abbrev p : ℕ := Nock.Field.p

theorem p_eq_limbs : p = 1 + B * (B - 1) := by norm_num [B, Nock.Field.p]

theorem two_B_lt_p : 2 * B < p := by norm_num [B, Nock.Field.p]

/-- The value of a little-endian limb list: `Σ lᵢ Bⁱ`. -/
def val (l : List ℕ) : ℕ := Nat.ofDigits B l

@[simp] theorem val_nil : val [] = 0 := by simp [val]

@[simp] theorem val_cons (a : ℕ) (l : List ℕ) : val (a :: l) = a + B * val l := by
  simp [val, Nat.ofDigits_cons]

/-- The canonical limb list of `n` (little-endian base `B`, no leading zero limb; `[]` for `0`). -/
def limbs (n : ℕ) : List ℕ := Nat.digits B n

/-- Canonical limb lists: every limb `< B`, last (top) limb `≠ 0`. -/
def Canonical (l : List ℕ) : Prop :=
  (∀ a ∈ l, a < B) ∧ ∀ h : l ≠ [], l.getLast h ≠ 0

theorem val_limbs (n : ℕ) : val (limbs n) = n := Nat.ofDigits_digits B n

theorem limbs_canonical (n : ℕ) : Canonical (limbs n) :=
  ⟨fun _ h => Nat.digits_lt_base one_lt_B h, fun _ => Nat.getLast_digit_ne_zero B
    (by intro h0; subst h0; simp_all [limbs])⟩

/-- A canonical list is the limb list of its value. -/
theorem limbs_val {l : List ℕ} (h : Canonical l) : limbs (val l) = l :=
  Nat.digits_ofDigits B one_lt_B l h.1 h.2

/-- **Uniqueness of the canonical representation.** -/
theorem canonical_unique {l l' : List ℕ} (h : Canonical l) (h' : Canonical l')
    (hv : val l = val l') : l = l' := by
  rw [← limbs_val h, ← limbs_val h', hv]

theorem canonical_iff_eq_limbs {l : List ℕ} : Canonical l ↔ l = limbs (val l) :=
  ⟨fun h => (limbs_val h).symm, fun h => h ▸ limbs_canonical _⟩

/-! ## The small / big boundary -/

/-- `n` is big iff `p ≤ n`. -/
def IsBig (n : ℕ) : Prop := p ≤ n

theorem canonical_one_top : Canonical [1, B - 1] := by
  refine ⟨?_, fun _ => ?_⟩
  · intro a ha; simp at ha; rcases ha with rfl | rfl <;> norm_num [B]
  · simp [B]

/-- `p = [1, B − 1]` as limbs. -/
theorem limbs_p : limbs p = [1, B - 1] := by
  have : val [1, B - 1] = p := by simp [p_eq_limbs]
  rw [← this, limbs_val canonical_one_top]

/-- `p − 1 = [0, B − 1]` as limbs (the one small value whose successor is big). -/
theorem limbs_p_sub_one : limbs (p - 1) = [0, B - 1] := by
  have hc : Canonical [0, B - 1] := by
    refine ⟨?_, fun _ => ?_⟩
    · intro a ha; simp at ha; rcases ha with rfl | rfl <;> norm_num [B]
    · simp [B]
  have : val [0, B - 1] = p - 1 := by simp [p_eq_limbs]
  rw [← this, limbs_val hc]

/-- Lists of length `≤ 1` with limbs `< B` have value `< B`. -/
theorem val_lt_B_of_length_le_one {l : List ℕ} (hl : ∀ a ∈ l, a < B) (h : l.length ≤ 1) :
    val l < B := by
  match l, h with
  | [], _ => simp [B]
  | [a], _ => simpa using hl a (by simp)

/-- **A big atom has at least two limbs.** -/
theorem two_le_length_of_big {n : ℕ} (h : IsBig n) : 2 ≤ (limbs n).length := by
  by_contra hlt
  have := val_lt_B_of_length_le_one (limbs_canonical n).1 (by omega)
  rw [val_limbs] at this
  have : B < p := by norm_num [B, Nock.Field.p]
  unfold IsBig at h
  omega

/-- A canonical list of length `≥ 3` has value `≥ B²`. -/
theorem B_sq_le_val {l : List ℕ} (h : Canonical l) (hl : 3 ≤ l.length) : B * B ≤ val l := by
  have hv := limbs_val h
  have hlen : (Nat.digits B (val l)).length = Nat.log B (val l) + 1 :=
    Nat.length_digits B (val l) one_lt_B (by
      intro h0; rw [h0] at hv; simp [limbs] at hv; subst hv; simp at hl)
  rw [limbs] at hv
  rw [hv] at hlen
  have : 2 ≤ Nat.log B (val l) := by omega
  have := Nat.pow_le_of_le_log (b := B) (by
      intro h0; rw [h0] at hlen; simp at hlen; omega) this
  simpa [pow_two] using this

/-- **The Goldilocks boundary gate (iv)** (SPEC-SEMANTICS S2.2): for a canonical `l`,
`p ≤ val l ↔ 3 ≤ len ∨ (len = 2 ∧ l₁ = B − 1 ∧ 1 ≤ l₀)`. -/
theorem big_iff {l : List ℕ} (h : Canonical l) :
    IsBig (val l) ↔ 3 ≤ l.length ∨ ∃ a b, l = [a, b] ∧ b = B - 1 ∧ 1 ≤ a := by
  unfold IsBig
  have hB : B = 4294967296 := B_eq
  have hp : p = 1 + B * (B - 1) := p_eq_limbs
  constructor
  · intro hbig
    by_cases h3 : 3 ≤ l.length
    · exact Or.inl h3
    · right
      match l, h3 with
      | [], _ => simp at hbig; rw [hp, hB] at hbig; omega
      | [a], _ =>
        have := h.1 a (by simp)
        simp at hbig; rw [hp, hB] at hbig; rw [hB] at this; omega
      | [a, b], _ =>
        have ha := h.1 a (by simp)
        have hb := h.1 b (by simp)
        simp at hbig
        rw [hp] at hbig
        rw [hB] at ha hb hbig ⊢
        refine ⟨a, b, rfl, ?_, ?_⟩ <;> omega
      | _ :: _ :: _ :: _, h3 => simp at h3
  · rintro (h3 | ⟨a, b, rfl, hb, ha⟩)
    · have := B_sq_le_val h h3
      rw [hp]
      have : B * (B - 1) < B * B := by rw [hB]; norm_num
      omega
    · simp; rw [hp, hb]; omega

end Nock.Atoms
