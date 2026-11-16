import Nock.NockVMROM.Thm54.RAPPadding
import Nock.NockVMROM.Thm54.StrictPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!

The paper's semantic cores and connective assembly are at the paper, with generic IO at
the paper, walk/forest at the paper, appendix constraints at
the paper, and proof assembly at the paper.

It does not construct the optimized semantic cores, discharge
`B29SemanticTemplate`, close R6, or change the paper alias. -/

namespace Nock.RedTeam.Batch48

open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.RAPPadding
open Nock.NockVMROM.Thm54.StrictPackage
open scoped Polynomial

noncomputable section

/-! ## 1. All appended columns are semantically unread -/

/-- Build a padded trace from an arbitrary source trace and arbitrary values for every appended
column. -/
def paddedTrace {F : Type*} [CommRing F] (R : RAP F) (extra : Fin R.k → ℕ)
    (source : Fin R.w → F[X]) (appended : Fin (extraWidth extra) → F[X]) :
    Fin (R.w + extraWidth extra) → F[X] :=
  Fin.addCases source appended

/-- Projection ignores every appended column, not merely one selected witness. -/
theorem projectTrace_paddedTrace {F : Type*} [CommRing F] (R : RAP F)
    (extra : Fin R.k → ℕ) (source : Fin R.w → F[X])
    (appended : Fin (extraWidth extra) → F[X]) :
    projectTrace R extra (paddedTrace R extra source appended) = source := by
  funext i
  simp [projectTrace, paddedTrace, columnInclusion] <;> exact Fin.addCases_left i

/-- Varying all appended trace columns arbitrarily leaves both projection and satisfaction
unchanged. -/
theorem all_appended_columns_unread {F : Type*} [CommRing F] (R : RAP F)
    (extra : Fin R.k → ℕ) (n : ℕ) (source : Fin R.w → F[X])
    (A B : Fin (extraWidth extra) → F[X]) :
    projectTrace R extra (paddedTrace R extra source A) =
        projectTrace R extra (paddedTrace R extra source B) ∧
      ((pad R extra n).Satisfies (paddedTrace R extra source A) ↔
        (pad R extra n).Satisfies (paddedTrace R extra source B)) := by
  have hA := projectTrace_paddedTrace R extra source A
  have hB := projectTrace_paddedTrace R extra source B
  constructor
  · rw [hA, hB]
  · rw [satisfies_iff, satisfies_iff, hA, hB]

/-! ## 2. Appended constraints are literal zero polynomials -/

/-- Every appended constraint body is definitionally the zero multivariate polynomial. -/
theorem appended_constraint_literal_zero {F : Type*} [CommRing F] (R : RAP F)
    (extra : Fin R.k → ℕ) (n : ℕ) (i : Fin n) :
    (pad R extra n).C (Fin.natAdd R.s i) = 0 := by
  simp [pad]

/-- Literal-zero appended constraints mention no variables. -/
theorem appended_constraint_vars_empty {F : Type*} [CommRing F] (R : RAP F)
    (extra : Fin R.k → ℕ) (n : ℕ) (i : Fin n) :
    ((pad R extra n).C (Fin.natAdd R.s i)).vars = ∅ := by
  rw [appended_constraint_literal_zero]
  simp

/-- Literal-zero appended constraints have total degree zero. -/
theorem appended_constraint_degree_zero {F : Type*} [CommRing F] (R : RAP F)
    (extra : Fin R.k → ℕ) (n : ℕ) (i : Fin n) :
    ((pad R extra n).C (Fin.natAdd R.s i)).totalDegree = 0 := by
  rw [appended_constraint_literal_zero]
  simp

/-- Literal-zero appended constraints compose to zero for every trace. -/
theorem appended_constraint_compose_zero {F : Type*} [CommRing F] (R : RAP F)
    (extra : Fin R.k → ℕ) (n : ℕ)
    (P : Fin (R.w + extraWidth extra) → F[X]) (i : Fin n) :
    (pad R extra n).compose P (Fin.natAdd R.s i) = 0 :=
  compose_right R extra n P i

/-! ## 3. Original columns, variables, and constraints are injectively preserved -/

theorem column_inclusion_injective {F : Type*} [CommRing F] (R : RAP F)
    (extra : Fin R.k → ℕ) :
    Function.Injective (columnInclusion R extra) :=
  (columnInclusion R extra).injective

theorem variable_inclusion_injective {F : Type*} [CommRing F] (R : RAP F)
    (extra : Fin R.k → ℕ) :
    Function.Injective (variableInclusion R extra) := by
  intro a b h
  have hfst :
      (variableInclusion R extra a).1 = (variableInclusion R extra b).1 :=
    congrArg (fun q => q.1) h
  have hsnd :
      (variableInclusion R extra a).2 = (variableInclusion R extra b).2 :=
    congrArg (fun q => q.2) h
  apply Prod.ext
  · exact (columnInclusion R extra).injective hfst
  · simpa [variableInclusion] using hsnd

theorem constraint_inclusion_injective {F : Type*} [CommRing F] (R : RAP F)
    (n : ℕ) :
    Function.Injective (Fin.castAdd n : Fin R.s → Fin (R.s + n)) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun q : Fin (R.s + n) => q.val) h

/-- The padded variable-index set is exactly the image of the source set. -/
theorem source_index_set_exact_image {F : Type*} [CommRing F] (R : RAP F)
    (extra : Fin R.k → ℕ) (n : ℕ) :
    (pad R extra n).I = R.I.image (variableInclusion R extra) :=
  rfl

/-- No source symbolic variable is truncated from the padded RAP's index set. -/
theorem source_variables_not_truncated {F : Type*} [CommRing F] (R : RAP F)
    (extra : Fin R.k → ℕ) (n : ℕ) (q : Fin R.w × ℕ) (hq : q ∈ R.I) :
    variableInclusion R extra q ∈ (pad R extra n).I := by
  rw [source_index_set_exact_image]
  exact Finset.mem_image.mpr ⟨q, hq, rfl⟩

/-- No original column collides with any appended column. -/
theorem original_appended_columns_disjoint {F : Type*} [CommRing F] (R : RAP F)
    (extra : Fin R.k → ℕ) (i : Fin R.w) (j : Fin (extraWidth extra)) :
    columnInclusion R extra i ≠ Fin.natAdd R.w j := by
  intro h
  have hv := congrArg Fin.val h
  simp [columnInclusion] at hv
  have h1 : (columnInclusion R extra i).val < R.w := i.isLt
  have h2 : (Fin.natAdd R.w j).val = R.w + j.val := rfl
  have h3 := congrArg Fin.val h
  omega

/-- Original and appended constraint indices cannot collide. -/
theorem original_appended_constraints_disjoint {F : Type*} [CommRing F] (R : RAP F)
    (n : ℕ) (i : Fin R.s) (j : Fin n) :
    (Fin.castAdd n i : Fin (R.s + n)) ≠ Fin.natAdd R.s j := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv
  omega

/-- Every source constraint body is exactly its rename along the injective variable inclusion. -/
theorem original_constraint_is_renamed {F : Type*} [CommRing F] (R : RAP F)
    (extra : Fin R.k → ℕ) (n : ℕ) (i : Fin R.s) :
    (pad R extra n).C (Fin.castAdd n i) =
      MvPolynomial.rename (variableInclusion R extra) (R.C i) := by
  simp [pad]

/-- Renamed source evaluation is exactly source evaluation on the projected trace. -/
theorem renamed_evaluation_matches_source {F : Type*} [CommRing F] (R : RAP F)
    (extra : Fin R.k → ℕ) (n : ℕ)
    (P : Fin (R.w + extraWidth extra) → F[X]) (i : Fin R.s) :
    (pad R extra n).compose P (Fin.castAdd n i) =
      R.compose (projectTrace R extra P) i :=
  compose_left R extra n P i

/-! ## 4. Two concrete RAPs test `k = 1` and `k = 2` -/

def sourceRAP1 : RAP ℚ where
  e := 3
  k := 1
  wRAP := fun _ => 1
  w := 1
  w_eq := by simp
  h := 0
  d := 1
  s := 1
  ω := 1
  β := 1
  I := {(0, 0)}
  C := fun _ => MvPolynomial.X (0, 0)
  C_vars := by intro i; simp
  C_deg := by intro i; simp
  H := {1}
  β_ne_zero := by norm_num
  I_bound := by
    intro q hq
    simp only [Finset.mem_singleton] at hq
    subst q
    norm_num

def sourceRAP2 : RAP ℚ where
  e := 3
  k := 2
  wRAP := fun _ => 1
  w := 2
  w_eq := by
    simp
  h := 0
  d := 1
  s := 1
  ω := 1
  β := 1
  I := {(0, 0)}
  C := fun _ => MvPolynomial.X (0, 0)
  C_vars := by intro i; simp
  C_deg := by intro i; simp
  H := {1}
  β_ne_zero := by norm_num
  I_bound := by
    intro q hq
    simp only [Finset.mem_singleton] at hq
    subst q
    norm_num

theorem sourceRAP1_k_positive : 0 < sourceRAP1.k := by
  norm_num [sourceRAP1]

theorem sourceRAP2_k_positive : 0 < sourceRAP2.k := by
  norm_num [sourceRAP2]

abbrev sourceRAP1_round0 : Fin sourceRAP1.k :=
  ⟨0, sourceRAP1_k_positive⟩

abbrev sourceRAP2_round0 : Fin sourceRAP2.k :=
  ⟨0, sourceRAP2_k_positive⟩

abbrev sourceRAP2_round1 : Fin sourceRAP2.k :=
  ⟨1, by norm_num [sourceRAP2]⟩

abbrev sourceRAP1_constraint0 : Fin sourceRAP1.s :=
  ⟨0, by norm_num [sourceRAP1]⟩

abbrev sourceRAP1_column0 : Fin sourceRAP1.w :=
  ⟨0, by norm_num [sourceRAP1]⟩

/-- `firstRoundExtra` cannot be called without evidence that a valid first round exists. -/
abbrev first_round_requires_positive := @firstRoundExtra

/-- For `k = 1`, the only valid round receives all residual columns. -/
theorem first_round_k1_exact :
    firstRoundExtra sourceRAP1 sourceRAP1_k_positive 12 sourceRAP1_round0 = 12 ∧
      extraWidth (firstRoundExtra sourceRAP1 sourceRAP1_k_positive 12) = 12 := by
  norm_num [firstRoundExtra, extraWidth, sourceRAP1]

/-- For `k = 2`, round zero receives all residual columns and round one receives none. -/
theorem first_round_k2_exact :
    firstRoundExtra sourceRAP2 sourceRAP2_k_positive 25 sourceRAP2_round0 = 25 ∧
      firstRoundExtra sourceRAP2 sourceRAP2_k_positive 25 sourceRAP2_round1 = 0 ∧
      extraWidth (firstRoundExtra sourceRAP2 sourceRAP2_k_positive 25) = 25 := by
  norm_num [firstRoundExtra, extraWidth, sourceRAP2, Fin.sum_univ_two]

/-- Every padded per-round width is exactly source width plus that round's requested extra, and the
declared total exactly sums those entries. -/
theorem per_round_width_accounting {F : Type*} [CommRing F] (R : RAP F)
    (extra : Fin R.k → ℕ) (n : ℕ) :
    (∀ i, (pad R extra n).wRAP i = R.wRAP i + extra i) ∧
      (pad R extra n).w = ∑ i, (pad R extra n).wRAP i := by
  constructor
  · intro i
    rfl
  · exact (pad R extra n).w_eq

/-- Concrete two-round compute placement: all twelve cubic compute residual columns are in round
zero, none in round one, and the total rises by exactly twelve. -/
theorem compute_k2_round_accounting :
    (padComputeCore sourceRAP2 sourceRAP2_k_positive 3).wRAP sourceRAP2_round0 =
        sourceRAP2.wRAP sourceRAP2_round0 + 12 ∧
      (padComputeCore sourceRAP2 sourceRAP2_k_positive 3).wRAP sourceRAP2_round1 =
        sourceRAP2.wRAP sourceRAP2_round1 ∧
      (padComputeCore sourceRAP2 sourceRAP2_k_positive 3).w = sourceRAP2.w + 12 := by
  constructor
  · change sourceRAP2.wRAP sourceRAP2_round0 +
      firstRoundExtra sourceRAP2 sourceRAP2_k_positive 12 sourceRAP2_round0 =
        sourceRAP2.wRAP sourceRAP2_round0 + 12
    norm_num [firstRoundExtra, sourceRAP2]
  · constructor
    · change sourceRAP2.wRAP sourceRAP2_round1 +
        firstRoundExtra sourceRAP2 sourceRAP2_k_positive 12 sourceRAP2_round1 =
          sourceRAP2.wRAP sourceRAP2_round1
      norm_num [firstRoundExtra, sourceRAP2]
    · norm_num [padComputeCore, pad, firstRoundExtra, computeResidualColumns, extraWidth,
        sourceRAP2, Fin.sum_univ_two]

/-- Concrete one-round memory placement: all twenty-three cubic memory residual columns are in its
only valid round. -/
theorem memory_k1_round_accounting :
    (padMemoryCore sourceRAP1 sourceRAP1_k_positive 3).wRAP sourceRAP1_round0 =
        sourceRAP1.wRAP sourceRAP1_round0 + 23 ∧
      (padMemoryCore sourceRAP1 sourceRAP1_k_positive 3).w = sourceRAP1.w + 23 := by
  constructor
  · change sourceRAP1.wRAP sourceRAP1_round0 +
      firstRoundExtra sourceRAP1 sourceRAP1_k_positive 23 sourceRAP1_round0 =
        sourceRAP1.wRAP sourceRAP1_round0 + 23
    norm_num [firstRoundExtra, sourceRAP1]
  · norm_num [padMemoryCore, pad, firstRoundExtra, memoryResidualColumns, extraWidth, sourceRAP1]

/-! ## 5. Independent AO arithmetic and cubic fingerprints -/

/-- Independent symbolic derivation; no production arithmetic theorem is invoked. -/
theorem independent_AO_symbolic (e : ℕ) :
    (58 * e + 13) + 4 * e = 62 * e + 13 ∧
      (55 * e + 6) + (6 * e + 7) = 61 * e + 13 ∧
      (21 * e + 13) + (3 * e + 2) = 24 * e + 15 ∧
      (21 * e + 14) + (3 * e + 2) = 24 * e + 16 := by
  omega

/-- Independent cubic arithmetic, including the exact residual addends. -/
theorem independent_e3_fingerprints :
    187 + 12 = 199 ∧ 76 + 11 = 87 ∧
      171 + 25 = 196 ∧ 77 + 11 = 88 := by
  norm_num

/-- One-short and one-extra residual choices are rejected in every cubic bucket. -/
theorem reject_one_short_or_extra_residuals :
    187 + 11 ≠ 199 ∧ 187 + 13 ≠ 199 ∧
      76 + 10 ≠ 87 ∧ 76 + 12 ≠ 87 ∧
      171 + 24 ≠ 196 ∧ 171 + 26 ≠ 196 ∧
      77 + 10 ≠ 88 ∧ 77 + 12 ≠ 88 := by
  norm_num

/-- Re-derive the compute `187/76 → 199/87` result by unfolding the constructor, without invoking
the production fingerprint or arithmetic theorems. -/
theorem independent_padComputeCore_e3 (R : RAP ℚ) (hk : 0 < R.k)
    (hw : R.w = 187) (hs : R.s = 76) :
    (padComputeCore R hk 3).w = 199 ∧ (padComputeCore R hk 3).s = 87 := by
  constructor
  · simp [padComputeCore, pad, firstRoundExtra, extraWidth, computeResidualColumns, hw]
  · simp [padComputeCore, pad, residualTransitionGates, hs]

/-- Independent memory `171/77 → 194/88` constructor check (`residual = 23`). -/
theorem independent_padMemoryCore_e3 (R : RAP ℚ) (hk : 0 < R.k)
    (hw : R.w = 171) (hs : R.s = 77) :
    (padMemoryCore R hk 3).w = 194 ∧ (padMemoryCore R hk 3).s = 88 := by
  constructor
  · simp [padMemoryCore, pad, firstRoundExtra, extraWidth, memoryResidualColumns, hw]
  · simp [padMemoryCore, pad, residualTransitionGates, hs]

/-! ## 6. Metadata, validity, and exact constraint-count preservation -/

theorem pad_preserves_metadata_and_validity {F : Type*} [CommRing F] (R : RAP F)
    (extra : Fin R.k → ℕ) (n : ℕ) :
    (pad R extra n).e = R.e ∧
      (pad R extra n).k = R.k ∧
      (pad R extra n).h = R.h ∧
      (pad R extra n).d = R.d ∧
      (pad R extra n).ω = R.ω ∧
      (pad R extra n).β = R.β ∧
      (pad R extra n).H = R.H ∧
      (pad R extra n).β ≠ 0 ∧
      (∀ q ∈ (pad R extra n).I, q.2 < 2 ^ (pad R extra n).h) ∧
      (pad R extra n).s = R.s + n := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (pad R extra n).β_ne_zero,
    (pad R extra n).I_bound, rfl⟩

theorem cubic_constraint_count_exact (R : RAP ℚ) (hk : 0 < R.k) :
    (padComputeCore R hk 3).s = R.s + 11 ∧
      (padMemoryCore R hk 3).s = R.s + 11 := by
  simp [padComputeCore, padMemoryCore, pad, residualTransitionGates]

/-! ## 7. Non-vacuity and rejection preservation with a real nonzero constraint -/

def zeroTrace1 : Fin sourceRAP1.w → ℚ[X] := fun _ => 0
def oneTrace1 : Fin sourceRAP1.w → ℚ[X] := fun _ => 1
def extraOne : Fin sourceRAP1.k → ℕ := fun _ => 2

theorem source_constraint_is_nonzero :
    sourceRAP1.C sourceRAP1_constraint0 ≠ 0 := by
  change MvPolynomial.X (R := ℚ) (0, 0) ≠ 0
  exact MvPolynomial.X_ne_zero _

theorem renamed_source_constraint_is_nonzero :
    (pad sourceRAP1 extraOne 2).C (Fin.castAdd 2 sourceRAP1_constraint0) ≠ 0 := by
  rw [original_constraint_is_renamed]
  change MvPolynomial.rename (variableInclusion sourceRAP1 extraOne)
    (MvPolynomial.X (sourceRAP1_column0, 0) :
      MvPolynomial (Fin sourceRAP1.w × ℕ) ℚ) ≠ 0
  rw [MvPolynomial.rename_X]
  exact MvPolynomial.X_ne_zero (R := ℚ) _

theorem source_zero_trace_satisfies : sourceRAP1.Satisfies zeroTrace1 := by
  intro i x hx
  change Polynomial.eval x
    ((MvPolynomial.aeval
      (fun q : Fin sourceRAP1.w × ℕ =>
        (zeroTrace1 q.1).comp
          (Polynomial.C (sourceRAP1.ω ^ q.2) * Polynomial.X)))
      (MvPolynomial.X (sourceRAP1_column0, 0) :
        MvPolynomial (Fin sourceRAP1.w × ℕ) ℚ)) = 0
  rw [MvPolynomial.aeval_X]
  simp [zeroTrace1]

theorem source_one_trace_rejects : ¬ sourceRAP1.Satisfies oneTrace1 := by
  intro h
  have bad := h sourceRAP1_constraint0 1 (by simp [sourceRAP1])
  change Polynomial.eval 1
    ((MvPolynomial.aeval
      (fun q : Fin sourceRAP1.w × ℕ =>
        (oneTrace1 q.1).comp
          (Polynomial.C (sourceRAP1.ω ^ q.2) * Polynomial.X)))
      (MvPolynomial.X (sourceRAP1_column0, 0) :
        MvPolynomial (Fin sourceRAP1.w × ℕ) ℚ)) = 0 at bad
  rw [MvPolynomial.aeval_X] at bad
  norm_num [oneTrace1] at bad

def paddedZeroTrace1 (tail : Fin (extraWidth extraOne) → ℚ[X]) :
    Fin (sourceRAP1.w + extraWidth extraOne) → ℚ[X] :=
  paddedTrace sourceRAP1 extraOne zeroTrace1 tail

def paddedOneTrace1 (tail : Fin (extraWidth extraOne) → ℚ[X]) :
    Fin (sourceRAP1.w + extraWidth extraOne) → ℚ[X] :=
  paddedTrace sourceRAP1 extraOne oneTrace1 tail

/-- Both directions of `satisfies_iff` fire for every choice of the two appended columns. -/
theorem padded_zero_trace_satisfies (tail : Fin (extraWidth extraOne) → ℚ[X]) :
    (pad sourceRAP1 extraOne 2).Satisfies (paddedZeroTrace1 tail) := by
  rw [satisfies_iff]
  change sourceRAP1.Satisfies
    (projectTrace sourceRAP1 extraOne (paddedTrace sourceRAP1 extraOne zeroTrace1 tail))
  rw [projectTrace_paddedTrace]
  exact source_zero_trace_satisfies

/-- Padding cannot turn the concrete bad source trace into a good trace, regardless of all
appended values. -/
theorem padded_bad_trace_stays_bad (tail : Fin (extraWidth extraOne) → ℚ[X]) :
    ¬ (pad sourceRAP1 extraOne 2).Satisfies (paddedOneTrace1 tail) := by
  intro h
  apply source_one_trace_rejects
  have hp := (satisfies_iff sourceRAP1 extraOne 2 (paddedOneTrace1 tail)).mp h
  change sourceRAP1.Satisfies
    (projectTrace sourceRAP1 extraOne (paddedTrace sourceRAP1 extraOne oneTrace1 tail)) at hp
  rw [projectTrace_paddedTrace] at hp
  exact hp

/-- Concrete non-vacuity and discrimination are witnessed simultaneously by one nonzero source
gate, one satisfying trace, one rejecting trace, and arbitrary appended columns. -/
theorem padding_nonvacuous_and_discriminating :
    sourceRAP1.C sourceRAP1_constraint0 ≠ 0 ∧
      sourceRAP1.Satisfies zeroTrace1 ∧
      ¬ sourceRAP1.Satisfies oneTrace1 ∧
      (∀ tail, (pad sourceRAP1 extraOne 2).Satisfies (paddedZeroTrace1 tail)) ∧
      (∀ tail, ¬ (pad sourceRAP1 extraOne 2).Satisfies (paddedOneTrace1 tail)) :=
  ⟨source_constraint_is_nonzero, source_zero_trace_satisfies, source_one_trace_rejects,
    padded_zero_trace_satisfies, padded_bad_trace_stays_bad⟩

/-- The concrete nonzero renamed gate obeys `compose_left`, so it is neither dropped nor replaced
by a zero gate. -/
theorem concrete_nonzero_compose_left
    (P : Fin (sourceRAP1.w + extraWidth extraOne) → ℚ[X]) :
    (pad sourceRAP1 extraOne 2).compose P (Fin.castAdd 2 sourceRAP1_constraint0) =
      sourceRAP1.compose (projectTrace sourceRAP1 extraOne P) sourceRAP1_constraint0 :=
  compose_left sourceRAP1 extraOne 2 P sourceRAP1_constraint0

/-! ## 8. Scope guards: padding is not R6 closure -/

/-- The constructor's exact type requires an already-built source RAP; it does not produce an
optimized semantic core from Nock execution semantics. -/
abbrev padding_requires_source_RAP := @padComputeCore

/-- The strict package still carries the Batch-29 compute semantic-template residual. -/
def strict_package_still_requires_compute_B29
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    Nock.RedTeam.Batch29.B29SemanticTemplate
      (K := K) (MonolithicRAP.compTemplate F) P.compLanguage :=
  P.compSemanticTemplate

/-- The strict package still carries the Batch-29 memory semantic-template residual. -/
def strict_package_still_requires_memory_B29
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    Nock.RedTeam.Batch29.B29SemanticTemplate
      (K := K) (MonolithicRAP.memTemplate F) P.memLanguage :=
  P.memSemanticTemplate

/-- The consumed strict theorem remains conditional on a supplied strict package. -/
noncomputable def strict_capstone_remains_conditional
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    StrictThm54Statement P :=
  strictNockVMROM_of_package P

/-- Padding does not repoint the paper theorem alias. -/
theorem paper_alias_remains_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  rfl

end
end Nock.RedTeam.Batch48

#print axioms Nock.RedTeam.Batch48.all_appended_columns_unread
#print axioms Nock.RedTeam.Batch48.appended_constraint_literal_zero
#print axioms Nock.RedTeam.Batch48.appended_constraint_vars_empty
#print axioms Nock.RedTeam.Batch48.appended_constraint_degree_zero
#print axioms Nock.RedTeam.Batch48.appended_constraint_compose_zero
#print axioms Nock.RedTeam.Batch48.variable_inclusion_injective
#print axioms Nock.RedTeam.Batch48.constraint_inclusion_injective
#print axioms Nock.RedTeam.Batch48.source_variables_not_truncated
#print axioms Nock.RedTeam.Batch48.original_appended_columns_disjoint
#print axioms Nock.RedTeam.Batch48.renamed_evaluation_matches_source
#print axioms Nock.RedTeam.Batch48.first_round_k1_exact
#print axioms Nock.RedTeam.Batch48.first_round_k2_exact
#print axioms Nock.RedTeam.Batch48.independent_AO_symbolic
#print axioms Nock.RedTeam.Batch48.independent_e3_fingerprints
#print axioms Nock.RedTeam.Batch48.reject_one_short_or_extra_residuals
#print axioms Nock.RedTeam.Batch48.independent_padComputeCore_e3
#print axioms Nock.RedTeam.Batch48.independent_padMemoryCore_e3
#print axioms Nock.RedTeam.Batch48.pad_preserves_metadata_and_validity
#print axioms Nock.RedTeam.Batch48.renamed_source_constraint_is_nonzero
#print axioms Nock.RedTeam.Batch48.padding_nonvacuous_and_discriminating
#print axioms Nock.RedTeam.Batch48.concrete_nonzero_compose_left
#print axioms Nock.RedTeam.Batch48.strict_package_still_requires_compute_B29
#print axioms Nock.RedTeam.Batch48.strict_package_still_requires_memory_B29
#print axioms Nock.RedTeam.Batch48.strict_capstone_remains_conditional
#print axioms Nock.RedTeam.Batch48.paper_alias_remains_forest
