import Mathlib

/-! Shows that the clock recurrence `clk(i+1) = ω · clk(i)` pins the clock column only up to a scalar multiple, including at the wrap row. -/

namespace Attack

variable {K : Type*} [Field K]

/-- The only in-AIR way to pin a clock column is the (row-uniform, wrap-consistent) recurrence
    `clk(i+1) = ω · clk(i)`.  Every scalar multiple of the honest clock satisfies it, including
    cyclically at the wrap.  So the recurrence pins `clk` only up to the scalar `c`. -/
theorem clock_recurrence_scalar_free (ω c : K) (n : ℕ) (hω : ω ^ n = 1) :
    (∀ k, (fun j => c * ω ^ j) (k + 1) = ω * (fun j => c * ω ^ j) k)
      ∧ (fun j => c * ω ^ j) n = (fun j => c * ω ^ j) 0 := by
  refine ⟨fun k => by ring, ?_⟩
  simp [hω]

/-- Consequence: for the wrap selector `clk − s` the row at which the `.transition` gate is
    switched off is `c⁻¹ · s`, i.e. the prover picks it by picking `c`. -/
theorem skip_row_is_prover_chosen (ω s : K) (c : K) (hc : c ≠ 0) (k : ℕ)
    (hk : c * ω ^ k = s) : ω ^ k = c⁻¹ * s := by
  rw [← hk]
  field_simp

end Attack
