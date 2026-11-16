/-
  Nock/RedTeam/Batch2406Thm54AtomsCarry.lean

  * `Carry cin l l′` per position: `l′ᵢ + B·c_outᵢ = lᵢ + c_inᵢ`, `l′ᵢ < B`, `c ∈ {0,1}`, `c_inᵢ₊₁ =
    c_outᵢ`; `nil1` = overflow appends top limb `1`.  Value `val l′ = val l + cin`; tail sharing;
    canonicity preserved; carries and result determined; completeness; the crossing `p−1 ↦ p`.
  * Negative controls: dropping the `l′ᵢ < B` side condition admits a WRONG result list of the right
    value that is not canonical (`nc_no_range`), and an unbounded carry `c_out = 2` breaks
    determinism of the carries (`nc_carry_two`).
-/
import Nock.Atoms.Carry

set_option autoImplicit false

namespace Nock.RedTeam.Batch2406

open Nock.Atoms

example {cin : ℕ} {l l' : List ℕ} (h : Carry cin l l') : val l' = val l + cin := carry_val h
example {l l' : List ℕ} (h : Carry 1 l l') : val l' = val l + 1 := inc_val h
example {l l' : List ℕ} (hl : ∀ a ∈ l, a < B) (h : Carry 0 l l') : l' = l := carry_zero_eq hl h
example {cin a a' : ℕ} {l : List ℕ} (hl : ∀ x ∈ l, x < B) (hcin : cin ≤ 1) (ha' : a' < B)
    (he : a' = a + cin) : Carry cin (a :: l) (a' :: l) := Carry.stop hl hcin ha' he
example {cin cout a a' : ℕ} (ha' : a' < B) (he : a' + B * cout = a + cin) :
    cout = (a + cin) / B ∧ a' = (a + cin) % B := carry_cout ha' he
example {cin : ℕ} {l l₁ l₂ : List ℕ} (h₁ : Carry cin l l₁) (h₂ : Carry cin l l₂) : l₁ = l₂ :=
  carry_det h₁ h₂
example {cin : ℕ} {l l' : List ℕ} (h : Carry cin l l') (hc : Canonical l) : Canonical l' :=
  carry_canonical h hc
example {cin : ℕ} (hcin : cin ≤ 1) {l : List ℕ} (hl : ∀ a ∈ l, a < B) : ∃ l', Carry cin l l' :=
  carry_exists hcin hl
example {l l' : List ℕ} (hc : Canonical l) (h : Carry 1 l l') : l' = limbs (val l + 1) :=
  inc_eq_limbs hc h
example : Carry 1 (limbs (p - 1)) (limbs p) := crossing
example (k : ℕ) : Carry 1 (List.replicate k (B - 1)) (List.replicate k 0 ++ [1]) := carry_all_top k

/-- **NC 1 (range side condition).** Without `l′ᵢ < B`, the per-position equation with carries
in `{0,1}` admits `[B−1] ↦ [B]` (no carry out), of the right value but NOT canonical. -/
theorem nc_no_range :
    (B - 1) + 1 = B + B * 0 ∧ val [B] = val [B - 1] + 1 ∧ ¬ Canonical [B] ∧ ¬ Carry 1 [B - 1] [B] := by
  refine ⟨by norm_num [B], by norm_num [B], fun h => absurd (h.1 B (by simp)) (lt_irrefl _), ?_⟩
  intro h
  cases h with
  | cons _ _ hlt _ _ => exact lt_irrefl _ hlt

/-- **NC 2 (boolean carries).** -/
theorem nc_carry_two : (2 * B - 1) + 1 = 0 + B * 2 ∧ (2 * B - 1) + 1 = B + B * 1 := by
  norm_num [B]

end Nock.RedTeam.Batch2406

#print axioms Nock.Atoms.carry_val
#print axioms Nock.Atoms.inc_val
#print axioms Nock.Atoms.carry_zero_eq
#print axioms Nock.Atoms.Carry.stop
#print axioms Nock.Atoms.carry_cout
#print axioms Nock.Atoms.carry_det
#print axioms Nock.Atoms.carry_canonical
#print axioms Nock.Atoms.carry_exists
#print axioms Nock.Atoms.inc_eq_limbs
#print axioms Nock.Atoms.inc_big
#print axioms Nock.Atoms.crossing
#print axioms Nock.Atoms.carry_all_top
#print axioms Nock.RedTeam.Batch2406.nc_no_range
#print axioms Nock.RedTeam.Batch2406.nc_carry_two
