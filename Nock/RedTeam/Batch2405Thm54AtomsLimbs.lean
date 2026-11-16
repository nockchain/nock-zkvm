/-
  Nock/RedTeam/Batch2405Thm54AtomsLimbs.lean

  Exact statements by `example`, and their axioms.

  * `limbs n = Nat.digits (2^32) n`, `val l = Nat.ofDigits (2^32) l`; round trip and uniqueness of the
    canonical representation; `limbs p = [1, B−1]`, `limbs (p−1) = [0, B−1]`; a big atom has ≥ 2
    limbs; the Goldilocks boundary gate `big_iff`.
-/
import Nock.Atoms.Limbs

set_option autoImplicit false

namespace Nock.RedTeam.Batch2405

open Nock.Atoms

example : B = 2 ^ 32 := rfl
example : p = 2 ^ 64 - 2 ^ 32 + 1 := rfl
example (n : ℕ) : limbs n = Nat.digits (2 ^ 32) n := rfl
example (l : List ℕ) : val l = Nat.ofDigits (2 ^ 32) l := rfl
example (l : List ℕ) : Canonical l ↔ (∀ a ∈ l, a < B) ∧ ∀ h : l ≠ [], l.getLast h ≠ 0 := Iff.rfl
example (n : ℕ) : val (limbs n) = n := val_limbs n
example (n : ℕ) : Canonical (limbs n) := limbs_canonical n
example {l : List ℕ} (h : Canonical l) : limbs (val l) = l := limbs_val h
example {l l' : List ℕ} (h : Canonical l) (h' : Canonical l') (hv : val l = val l') : l = l' :=
  canonical_unique h h' hv
example : limbs p = [1, B - 1] := limbs_p
example : limbs (p - 1) = [0, B - 1] := limbs_p_sub_one
example {n : ℕ} (h : p ≤ n) : 2 ≤ (limbs n).length := two_le_length_of_big h
example {l : List ℕ} (h : Canonical l) :
    p ≤ val l ↔ 3 ≤ l.length ∨ ∃ a b, l = [a, b] ∧ b = B - 1 ∧ 1 ≤ a := big_iff h

/-- Negative control for `big_iff`: `[0, B−1]` (= `p − 1`) is canonical, has two limbs and top limb
`B − 1`, and is NOT big — the `1 ≤ l₀` clause is load-bearing. -/
theorem nc_p_sub_one_small : Canonical [0, B - 1] ∧ ¬ p ≤ val [0, B - 1] := by
  refine ⟨?_, ?_⟩
  · rw [← limbs_p_sub_one]; exact limbs_canonical _
  · simp [B, Nock.Field.p]

end Nock.RedTeam.Batch2405

#print axioms Nock.Atoms.val_limbs
#print axioms Nock.Atoms.limbs_canonical
#print axioms Nock.Atoms.limbs_val
#print axioms Nock.Atoms.canonical_unique
#print axioms Nock.Atoms.limbs_p
#print axioms Nock.Atoms.limbs_p_sub_one
#print axioms Nock.Atoms.two_le_length_of_big
#print axioms Nock.Atoms.big_iff
#print axioms Nock.RedTeam.Batch2405.nc_p_sub_one_small
