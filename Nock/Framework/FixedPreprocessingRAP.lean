import Nock.Framework.Core

/-!
# Local fixed-preprocessing RAP interface

`Def:RAP` makes the first interaction-round block the verifier's preprocessing columns.  This module adds a local wrapper for consumers which
also need the first-round polynomial block bound to verifier-fixed preprocessing polynomials.

Only the prefix belonging to round zero is fixed.  Later interaction rounds remain unrestricted.
The binding is polynomial equality, rather than equality merely on the active evaluation domain.
-/

namespace Nock.Framework

open scoped Polynomial

noncomputable section

variable {F : Type*} [CommRing F]

/-- Round zero, available whenever the RAP has at least one interaction round. -/
def RAP.firstRound (R : RAP F) (hk : 0 < R.k) : Fin R.k :=
  ⟨0, hk⟩

/-- The first-round width is bounded by the total width. -/
theorem RAP.firstRoundWidth_le_width (R : RAP F) (hk : 0 < R.k) :
    R.wRAP (R.firstRound hk) ≤ R.w := by
  rw [R.w_eq]
  exact Finset.single_le_sum
    (fun i _ => Nat.zero_le (R.wRAP i))
    (Finset.mem_univ (R.firstRound hk))

/-- Inclusion of the designated preprocessing prefix into the complete trace-column range. -/
def RAP.preprocessingColumn (R : RAP F) (hk : 0 < R.k) :
    Fin (R.wRAP (R.firstRound hk)) ↪ Fin R.w where
  toFun j := ⟨j, j.isLt.trans_le (R.firstRoundWidth_le_width hk)⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin R.w => x.val) hij

/-- A RAP together with verifier-fixed polynomial columns selected from its designated first round.

The remaining columns, including every column in rounds `1, …, k-1`, are not fixed by this
wrapper. -/
structure FixedPreprocessingRAP (F : Type*) [CommRing F] where
  rap : RAP F
  /-- `Def:RAP` has a designated first round. -/
  rounds_pos : 0 < rap.k
  /-- Number of verifier-fixed preprocessing columns. -/
  fixedCount : ℕ
  /-- Distinct designated locations inside the round-zero prefix. -/
  preprocessingIndex :
    Fin fixedCount ↪ Fin (rap.wRAP (rap.firstRound rounds_pos))
  /-- Verifier-fixed preprocessing polynomials at those designated locations. -/
  preprocessing : Fin fixedCount → F[X]

namespace FixedPreprocessingRAP

/-- The designated round-zero column inclusion of a fixed-preprocessing RAP. -/
def preprocessingColumn (R : FixedPreprocessingRAP F) :
    Fin R.fixedCount ↪ Fin R.rap.w where
  toFun j := R.rap.preprocessingColumn R.rounds_pos (R.preprocessingIndex j)
  inj' := by
    intro i j hij
    apply R.preprocessingIndex.injective
    apply (R.rap.preprocessingColumn R.rounds_pos).injective
    exact hij

/-- Every designated fixed column lies in the round-zero prefix. -/
theorem preprocessingColumn_lt_roundWidth (R : FixedPreprocessingRAP F)
    (j : Fin R.fixedCount) :
    (R.preprocessingColumn j : ℕ) <
      R.rap.wRAP (R.rap.firstRound R.rounds_pos) :=
  (R.preprocessingIndex j).isLt

/-- Polynomial-level binding of the candidate trace's designated preprocessing prefix. -/
def BindsPreprocessing (R : FixedPreprocessingRAP F)
    (P : Fin R.rap.w → F[X]) : Prop :=
  ∀ j, P (R.preprocessingColumn j) = R.preprocessing j

end FixedPreprocessingRAP

namespace RAP

/-- Local satisfaction interface for a RAP with verifier-fixed preprocessing. -/
def SatisfiesWithPreprocessing (R : FixedPreprocessingRAP F)
    (P : Fin R.rap.w → F[X]) : Prop :=
  R.rap.Satisfies P ∧ R.BindsPreprocessing P

/-- Projection to the unchanged raw satisfaction predicate. -/
theorem satisfiesWithPreprocessing_raw (R : FixedPreprocessingRAP F)
    {P : Fin R.rap.w → F[X]} (h : RAP.SatisfiesWithPreprocessing R P) :
    R.rap.Satisfies P :=
  h.1

/-- The fixed-preprocessing component is available independently of raw satisfaction. -/
theorem satisfiesWithPreprocessing_binds (R : FixedPreprocessingRAP F)
    {P : Fin R.rap.w → F[X]} (h : RAP.SatisfiesWithPreprocessing R P) :
    R.BindsPreprocessing P :=
  h.2

/-- Constructor/non-vacuity principle: every raw satisfying trace carrying the fixed prefix
satisfies the strengthened interface. -/
theorem satisfiesWithPreprocessing_of_raw_of_binds (R : FixedPreprocessingRAP F)
    {P : Fin R.rap.w → F[X]} (hraw : R.rap.Satisfies P)
    (hfixed : R.BindsPreprocessing P) :
    RAP.SatisfiesWithPreprocessing R P :=
  ⟨hraw, hfixed⟩

/-- Satisfaction is extensional in the complete polynomial assignment. -/
theorem satisfiesWithPreprocessing_ext (R : FixedPreprocessingRAP F)
    {P Q : Fin R.rap.w → F[X]} (hPQ : ∀ i, P i = Q i) :
    RAP.SatisfiesWithPreprocessing R P ↔ RAP.SatisfiesWithPreprocessing R Q := by
  have hfun : P = Q := funext hPQ
  subst Q
  rfl

/-- Any wrong polynomial in a designated first-round column is rejected, even when the raw
constraints happen to accept the candidate trace. -/
theorem not_satisfiesWithPreprocessing_of_wrong (R : FixedPreprocessingRAP F)
    (P : Fin R.rap.w → F[X])
    (j : Fin R.fixedCount)
    (hwrong : P (R.preprocessingColumn j) ≠ R.preprocessing j) :
    ¬ RAP.SatisfiesWithPreprocessing R P := by
  intro h
  exact hwrong (h.2 j)

end RAP

end

end Nock.Framework

#print axioms Nock.Framework.RAP.firstRoundWidth_le_width
#print axioms Nock.Framework.RAP.satisfiesWithPreprocessing_raw
#print axioms Nock.Framework.RAP.satisfiesWithPreprocessing_ext
#print axioms Nock.Framework.RAP.not_satisfiesWithPreprocessing_of_wrong
