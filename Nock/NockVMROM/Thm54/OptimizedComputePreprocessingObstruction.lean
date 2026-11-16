import Nock.NockVMROM.Thm54.OptimizedComputeAllRowsObstruction
import Nock.Framework.FixedPreprocessingRAP

/-!
# Fixed-preprocessing obstruction at the current `Framework.RAP` interface

The proposed endpoint-mask repair needs two trace columns to be verifier-fixed Lagrange selectors:
`isFirst = 1` only at the first row and `isLast = 1` only at the last row.  Merely putting those
columns in the preprocessing round does not express that property in the current
`Framework.RAP.Satisfies`: satisfaction receives one unrestricted polynomial vector and does not
carry a fixed preprocessing trace or a commitment-opening equality to one.

This file compiles that interface boundary on a two-row RAP whose only two columns are declared in
its preprocessing round.  Both the exact first/last masks and the all-zero wrong masks satisfy the
same RAP.  It also proves that scalar `publicVal` binding cannot repair the issue: one scalar cannot
equal the first-mask column at both row values `1` and `0`.

This is an implementation obstruction, not a verdict about the paper construction.  The proposed
masking delta can proceed after either:

* adding a local satisfaction interface carrying a fixed preprocessing polynomial vector and
  changing the consumed biconditional/strict-package side to that interface; or

Neither mechanism currently exists in `Framework.RAP`, and changing only the 13-column codec cannot
make raw `RAP.Satisfies` reject a wrong preprocessing mask.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputePreprocessingObstruction

open Nock.Framework
open scoped Polynomial

noncomputable section

abbrev F73 := ZMod 73

/-- A minimal RAP with two columns, both in its sole preprocessing round, and one zero
constraint. -/
def preprocessingOnlyRAP : RAP F73 where
  e := 1
  k := 1
  wRAP := ![2]
  w := 2
  w_eq := by simp
  h := 1
  d := 0
  s := 1
  ω := 1
  β := 1
  I := ∅
  C := fun _ => 0
  C_vars := by simp
  C_deg := by simp
  H := {0, 1}
  β_ne_zero := by norm_num
  I_bound := by simp

/-- Correct two-row Lagrange masks on nodes `0,1`: `1-X` selects the first row and `X` the last. -/
def exactMaskTrace : Fin 2 → F73[X]
  | 0 => 1 - Polynomial.X
  | 1 => Polynomial.X

/-- Malformed preprocessing assignment with neither endpoint selected. -/
def wrongMaskTrace : Fin 2 → F73[X] := fun _ => 0

def ExactTwoRowMasks (P : Fin 2 → F73[X]) : Prop :=
  (P 0).eval 0 = 1 ∧ (P 0).eval 1 = 0 ∧
    (P 1).eval 0 = 0 ∧ (P 1).eval 1 = 1

theorem exactMaskTrace_exact : ExactTwoRowMasks exactMaskTrace := by
  norm_num [ExactTwoRowMasks, exactMaskTrace]

theorem wrongMaskTrace_not_exact : ¬ ExactTwoRowMasks wrongMaskTrace := by
  simp [ExactTwoRowMasks, wrongMaskTrace]

/-- Declaring the columns as preprocessing metadata does not constrain their polynomial values. -/
theorem exactMaskTrace_satisfies :
    preprocessingOnlyRAP.Satisfies exactMaskTrace := by
  simp [RAP.Satisfies, RAP.compose, preprocessingOnlyRAP]
  all_goals (constructor <;> (first | simp | (erw [(MvPolynomial.aeval _).map_zero]; simp)))

/-- The same raw satisfaction predicate accepts malformed all-zero endpoint masks. -/
theorem wrongMaskTrace_satisfies :
    preprocessingOnlyRAP.Satisfies wrongMaskTrace := by
  simp [RAP.Satisfies, RAP.compose, preprocessingOnlyRAP]
  all_goals (constructor <;> (first | simp | (erw [(MvPolynomial.aeval _).map_zero]; simp)))


theorem preprocessing_metadata_does_not_bind_masks :
    preprocessingOnlyRAP.Satisfies exactMaskTrace ∧
      preprocessingOnlyRAP.Satisfies wrongMaskTrace ∧
      ExactTwoRowMasks exactMaskTrace ∧
      ¬ ExactTwoRowMasks wrongMaskTrace :=
  ⟨exactMaskTrace_satisfies, wrongMaskTrace_satisfies,
    exactMaskTrace_exact, wrongMaskTrace_not_exact⟩

/-- What a pair of scalar public values could express through ordinary pointwise equality gates. -/
def ScalarPublicMaskBinding
    (P : Fin 2 → F73[X]) (firstClaim lastClaim : F73) : Prop :=
  ∀ x ∈ ({0, 1} : Finset F73),
    (P 0).eval x = firstClaim ∧ (P 1).eval x = lastClaim

/-- Scalar public values are constant across `H`, so they cannot bind the nonconstant exact
first/last mask columns. -/
theorem exactMasks_have_no_scalar_public_binding :
    ¬ ∃ firstClaim lastClaim : F73,
      ScalarPublicMaskBinding exactMaskTrace firstClaim lastClaim := by
  rintro ⟨firstClaim, lastClaim, h⟩
  have h0 := (h 0 (by simp)).1
  have h1 := (h 1 (by simp)).1
  norm_num [exactMaskTrace] at h0 h1
  have : (1 : F73) = 0 := h0.trans h1.symm
  exact one_ne_zero this

/-! ## Production fixed-preprocessing closure

The local production
interface binds exactly the two columns in round zero by polynomial equality. -/

theorem preprocessingOnlyRAP_rounds_pos : 0 < preprocessingOnlyRAP.k := by
  norm_num [preprocessingOnlyRAP]

def fixedPreprocessingOnlyRAP : FixedPreprocessingRAP F73 where
  rap := preprocessingOnlyRAP
  rounds_pos := preprocessingOnlyRAP_rounds_pos
  fixedCount := 2
  preprocessingIndex := Function.Embedding.refl (Fin 2)
  preprocessing := exactMaskTrace

theorem preprocessingOnly_designated_range :
    fixedPreprocessingOnlyRAP.rap.k = 1 ∧
      fixedPreprocessingOnlyRAP.rap.wRAP
        (fixedPreprocessingOnlyRAP.rap.firstRound fixedPreprocessingOnlyRAP.rounds_pos) = 2 ∧
      (∀ j, (fixedPreprocessingOnlyRAP.preprocessingColumn j : Fin 2) = j) := by
  refine ⟨rfl, rfl, ?_⟩
  intro j
  apply Fin.ext
  rfl

/-- The exact masks make the strengthened local interface non-vacuous. -/
theorem exactMaskTrace_satisfiesWithPreprocessing :
    RAP.SatisfiesWithPreprocessing fixedPreprocessingOnlyRAP exactMaskTrace := by
  refine RAP.satisfiesWithPreprocessing_of_raw_of_binds
    fixedPreprocessingOnlyRAP exactMaskTrace_satisfies ?_
  intro j
  rw [preprocessingOnly_designated_range.2.2 j]
  fin_cases j <;> rfl

/-- The first fixed preprocessing polynomial is genuinely nonzero. -/
theorem fixedPreprocessingOnlyRAP_first :
    fixedPreprocessingOnlyRAP.preprocessing (0 : Fin 2) =
      (1 - Polynomial.X : F73[X]) := by
  rfl


theorem wrongMaskTrace_rejected_by_fixed_preprocessing :
    preprocessingOnlyRAP.Satisfies wrongMaskTrace ∧
      ¬ RAP.SatisfiesWithPreprocessing fixedPreprocessingOnlyRAP wrongMaskTrace := by
  refine ⟨wrongMaskTrace_satisfies, ?_⟩
  intro h
  have hbind := h.2 (0 : Fin 2)
  rw [preprocessingOnly_designated_range.2.2 (0 : Fin 2)] at hbind
  rw [fixedPreprocessingOnlyRAP_first] at hbind
  simpa [wrongMaskTrace] using congrArg (fun p : F73[X] => p.eval 0) hbind

#print axioms exactMaskTrace_exact
#print axioms wrongMaskTrace_not_exact
#print axioms exactMaskTrace_satisfies
#print axioms wrongMaskTrace_satisfies
#print axioms preprocessing_metadata_does_not_bind_masks
#print axioms exactMasks_have_no_scalar_public_binding
#print axioms preprocessingOnly_designated_range
#print axioms exactMaskTrace_satisfiesWithPreprocessing
#print axioms wrongMaskTrace_rejected_by_fixed_preprocessing

end
end OptimizedComputePreprocessingObstruction
end Nock.NockVMROM.Thm54
