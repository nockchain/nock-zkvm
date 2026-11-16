/-
  Nock/RedTeam/Batch547Thm54LambdaDeterminacy.lean

  **Item A (determinacy) and the `λ = 0` degeneracy of D-λ.**

  The brief's item A: with halt leaves `(0,0)` and the four rules, every node's accumulators are a
  FUNCTION of the read/verify placements (no split freedom).  TRUE for every `λ ≠ 0`
  (`rulesL_unique`): any pair of functions satisfying the four D-λ equations on all subtrees IS
  `(indP, countsL λ)`.
-/
import Nock.RedTeam.Batch546Thm54LambdaModel

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch547

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.RedTeam.Batch546
open Polynomial

variable {K : Type*} [Field K]

structure RulesL (l : K) (ind cnt : MTree K → K[X]) : Prop where
  halt_ind : ind .halt = 0
  halt_cnt : cnt .halt = 0
  dec_ind : ∀ L R, ind (.decompose L R) = ind L + ind R
  dec_cnt : ∀ L R, C l * cnt (.decompose L R) = cnt L + cnt R - ind R
  read_ind : ∀ e c, ind (.read e c) = ind c - X ^ e
  read_cnt : ∀ e c, cnt (.read e c) = cnt c - X ^ e
  ver_ind : ∀ e a c, ind (.verify e a c) = ind c + X ^ e
  ver_cnt : ∀ e a c, cnt (.verify e a c) = cnt c + C a * X ^ e

/-- The model satisfies its own rules (for `λ ≠ 0`). -/
theorem rulesL_model (l : K) (hl : l ≠ 0) : RulesL l indP_bin (countsL l) where
  halt_ind := rfl
  halt_cnt := rfl
  dec_ind := fun _ _ => rfl
  dec_cnt := fun L R => constr_countsL_decompose l hl L R
  read_ind := fun _ _ => rfl
  read_cnt := fun _ _ => rfl
  ver_ind := fun _ _ _ => rfl
  ver_cnt := fun _ _ _ => rfl

/-- **Item A — determinacy.**  For `λ ≠ 0` the four rules determine every node's accumulators
from the placements alone: any valuation is the model. -/
theorem rulesL_unique (l : K) (hl : l ≠ 0) (ind cnt : MTree K → K[X])
    (h : RulesL l ind cnt) (t : MTree K) :
    ind t = indP_bin t ∧ cnt t = countsL l t := by
  induction t with
  | halt => exact ⟨h.halt_ind, h.halt_cnt⟩
  | decompose L R ihl ihr =>
      refine ⟨?_, ?_⟩
      · rw [h.dec_ind, ihl.1, ihr.1]; rfl
      · have hd := h.dec_cnt L R
        rw [ihl.2, ihr.2, ihr.1] at hd
        have hc : C l⁻¹ * C l = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hl, C_1]
        calc cnt (.decompose L R)
            = C l⁻¹ * (C l * cnt (.decompose L R)) := by rw [← mul_assoc, hc, one_mul]
          _ = countsL l (.decompose L R) := by rw [hd]; rfl
  | read e c ih =>
      exact ⟨by rw [h.read_ind, ih.1]; rfl, by rw [h.read_cnt, ih.2]; rfl⟩
  | verify e a c ih =>
      exact ⟨by rw [h.ver_ind, ih.1]; rfl, by rw [h.ver_cnt, ih.2]; rfl⟩

/-- At `λ = 0` the decompose gate `λ·counts_P = counts_L + counts_R − ind_R` does not mention
`counts_P`: at `decompose halt halt` EVERY value of the parent's `counts` satisfies it. -/
theorem lambda_zero_local_freedom (v : K[X]) :
    C (0 : K) * v = (0 : K[X]) + 0 - 0 := by simp

end Nock.RedTeam.Batch547

#print axioms Nock.RedTeam.Batch547.rulesL_unique
#print axioms Nock.RedTeam.Batch547.lambda_zero_local_freedom
