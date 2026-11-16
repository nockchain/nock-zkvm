import Nock.NockVMROM.Thm54.OptimizedComputeCoreInventory
import Nock.NockVMROM.Thm54.StrictPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!

`Def:RAP` says that `.s` is the total number of constraint polynomials
. The compute capstone separately lists `24e+15` transition constraints,
`2e + e` endpoint constraints, and two equalities; the memory capstone
lists `24e+16`, `2e + 2e`, and four.

The authorized correctness delta remains exactly `4e` / `6e+5` columns and `3e+2` literal-zero
transition constraints.  This file does not construct either optimized semantic core, discharge
`B29SemanticTemplate`, close R6, or change the paper alias.
-/

namespace Nock.RedTeam.Batch49

open Module
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.RAPPadding
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.StrictPackage
open scoped Polynomial

noncomputable section

/-! ## 1. Independent symbolic and cubic reconstruction

These proofs unfold the relevant formulas directly.  They do not call any production arithmetic,
fingerprint, or equality theorem.
-/

theorem independent_symbolic_totals (e : ℕ) :
    (21 * e + 13) + (2 * e + e + 2) = 24 * e + 15 ∧
      ((21 * e + 13) + (2 * e + e + 2)) + (3 * e + 2) = 27 * e + 17 ∧
      (21 * e + 13) + (3 * e + 2) = 24 * e + 15 ∧
      (21 * e + 14) + (2 * e + 2 * e + 4) = 25 * e + 18 ∧
      ((21 * e + 14) + (2 * e + 2 * e + 4)) + (3 * e + 2) =
        28 * e + 20 ∧
      (21 * e + 14) + (3 * e + 2) = 24 * e + 16 := by
  omega

theorem independent_cubic_totals :
    76 + 11 = 87 ∧
      87 + 11 = 98 ∧
      76 + 11 = 87 ∧
      77 + 16 = 93 ∧
      93 + 11 = 104 ∧
      77 + 11 = 88 := by
  norm_num

theorem independent_unfolded_production_formulas (e : ℕ) :
    computeCoreTotalConstraints e = 24 * e + 15 ∧
      computeFinalTotalConstraints e = 27 * e + 17 ∧
      memoryCoreTotalConstraints e = 25 * e + 18 ∧
      memoryFinalTotalConstraints e = 28 * e + 20 := by
  simp [computeCoreTotalConstraints, computeCoreTransitionGates,
    computeCoreEndpointEqualityConstraints, computeFinalTotalConstraints,
    memoryCoreTotalConstraints, memoryCoreTransitionGates,
    memoryCoreEndpointEqualityConstraints, memoryFinalTotalConstraints]
  omega

theorem independent_unfolded_cubic_formulas :
    computeCoreTransitionGates 3 = 76 ∧
      computeCoreEndpointEqualityConstraints 3 = 11 ∧
      computeCoreTotalConstraints 3 = 87 ∧
      residualTransitionGates 3 = 11 ∧
      computeFinalTotalConstraints 3 = 98 ∧
      memoryCoreTransitionGates 3 = 77 ∧
      memoryCoreEndpointEqualityConstraints 3 = 16 ∧
      memoryCoreTotalConstraints 3 = 93 ∧
      memoryFinalTotalConstraints 3 = 104 := by
  norm_num [computeCoreTransitionGates, computeCoreEndpointEqualityConstraints,
    computeCoreTotalConstraints, residualTransitionGates, computeFinalTotalConstraints,
    memoryCoreTransitionGates, memoryCoreEndpointEqualityConstraints,
    memoryCoreTotalConstraints, memoryFinalTotalConstraints]

/-! ## 2. Equality with the consumed monolithic RAP values -/

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem padded_compute_matches_consumed {e h : ℕ}
    (R : RAP F) (hk : 0 < R.k)
    (he : R.e = e) (hw : R.w = 58 * e + 13) (hs : R.s = 24 * e + 15)
    (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F e h) (H : Finset F) :
    (padComputeCore R hk e).e = e ∧
      (padComputeCore R hk e).w = 62 * e + 13 ∧
      (padComputeCore R hk e).w =
        (RAP_NockCompIO b chalVal pubVal orbit H).w ∧
      (padComputeCore R hk e).s =
        (RAP_NockCompIO b chalVal pubVal orbit H).s := by
  refine ⟨he, ?_, ?_, ?_⟩
  · change R.w +
      extraWidth (firstRoundExtra R hk (computeResidualColumns e)) = 62 * e + 13
    rw [extraWidth_firstRoundExtra, hw]
    simp [computeResidualColumns]
    omega
  · rw [RAP_NockCompIO_width]
    change R.w +
      extraWidth (firstRoundExtra R hk (computeResidualColumns e)) = 62 * e + 13
    rw [extraWidth_firstRoundExtra, hw]
    simp [computeResidualColumns]
    omega
  · rw [RAP_NockCompIO_s]
    change R.s + residualTransitionGates e =
      (24 * e + 15) + 2 * e + e + 2
    rw [hs]
    simp [residualTransitionGates]
    omega

theorem padded_memory_matches_consumed {e h : ℕ}
    (R : RAP F) (hk : 0 < R.k)
    (he : R.e = e) (hw : R.w = 55 * e + 6) (hs : R.s = 25 * e + 18)
    (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F e h) (H : Finset F) :
    (padMemoryCore R hk e).e = e ∧
      (padMemoryCore R hk e).w = 61 * e + 11 ∧
      (RAP_NockMemIO b chalVal pubVal orbit H).w = 61 * e + 13 ∧
      (padMemoryCore R hk e).s =
        (RAP_NockMemIO b chalVal pubVal orbit H).s := by
  refine ⟨he, ?_, RAP_NockMemIO_width b chalVal pubVal orbit H, ?_⟩
  · change R.w +
      extraWidth (firstRoundExtra R hk (memoryResidualColumns e)) = 61 * e + 11
    rw [extraWidth_firstRoundExtra, hw]
    simp [memoryResidualColumns]
    omega
  · rw [RAP_NockMemIO_s]
    change R.s + residualTransitionGates e =
      (24 * e + 16) + 2 * e + 2 * e + 4
    rw [hs]
    simp [residualTransitionGates]
    omega

/-! ## 3. Transition-only `.s` regressions are rejected -/

theorem reject_obsolete_cubic_source_and_final_s
    (Rc Rm : RAP F) (hkc : 0 < Rc.k) (hkm : 0 < Rm.k)
    (hcs : Rc.s = 87) (hms : Rm.s = 93) :
    Rc.s ≠ 76 ∧
      Rm.s ≠ 77 ∧
      (padComputeCore Rc hkc 3).s ≠ 87 ∧
      (padMemoryCore Rm hkm 3).s ≠ 88 := by
  constructor
  · omega
  · constructor
    · omega
    · constructor
      · change Rc.s + residualTransitionGates 3 ≠ 87
        simp [hcs, residualTransitionGates]
      · change Rm.s + residualTransitionGates 3 ≠ 88
        simp [hms, residualTransitionGates]

/-! ## 4. Exact appended partition and literal-zero structure -/

theorem appended_count_is_exact (e : ℕ) :
    residualTransitionGates e = 3 * e + 2 := rfl

theorem padded_constraint_count_exact (R : RAP F) (hk : 0 < R.k) (e : ℕ) :
    (padComputeCore R hk e).s = R.s + (3 * e + 2) ∧
      (padMemoryCore R hk e).s = R.s + (3 * e + 2) := by
  simp [padComputeCore, padMemoryCore, pad, residualTransitionGates]

theorem appended_constraint_literal_zero (R : RAP F) (extra : Fin R.k → ℕ)
    (n : ℕ) (i : Fin n) :
    (pad R extra n).C (Fin.natAdd R.s i) = 0 := by
  simp [pad]

theorem appended_constraint_vars_empty (R : RAP F) (extra : Fin R.k → ℕ)
    (n : ℕ) (i : Fin n) :
    ((pad R extra n).C (Fin.natAdd R.s i)).vars = ∅ := by
  rw [appended_constraint_literal_zero]
  simp

theorem appended_constraint_degree_zero (R : RAP F) (extra : Fin R.k → ℕ)
    (n : ℕ) (i : Fin n) :
    ((pad R extra n).C (Fin.natAdd R.s i)).totalDegree = 0 := by
  rw [appended_constraint_literal_zero]
  simp

theorem appended_constraint_compose_zero (R : RAP F) (extra : Fin R.k → ℕ)
    (n : ℕ) (P : Fin (R.w + extraWidth extra) → F[X]) (i : Fin n) :
    (pad R extra n).compose P (Fin.natAdd R.s i) = 0 := by
  simp [RAP.compose, pad]

theorem source_constraint_retained (R : RAP F) (extra : Fin R.k → ℕ)
    (n : ℕ) (i : Fin R.s) :
    (pad R extra n).C (Fin.castAdd n i) =
      MvPolynomial.rename (variableInclusion R extra) (R.C i) := by
  simp [pad]

theorem source_constraint_indices_injective (R : RAP F) (n : ℕ) :
    Function.Injective (Fin.castAdd n : Fin R.s → Fin (R.s + n)) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun q : Fin (R.s + n) => q.val) hij

theorem source_and_appended_indices_disjoint (R : RAP F) (n : ℕ)
    (i : Fin R.s) (j : Fin n) :
    (Fin.castAdd n i : Fin (R.s + n)) ≠ Fin.natAdd R.s j := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv
  omega

theorem every_padded_constraint_has_exact_side (R : RAP F) (n : ℕ)
    (j : Fin (R.s + n)) :
    (∃ i : Fin R.s, j = Fin.castAdd n i) ∨
      (∃ i : Fin n, j = Fin.natAdd R.s i) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

theorem compute_endpoint_bucket_retained_once
    (R : RAP F) (hk : 0 < R.k) (e : ℕ)
    (hs : R.s = computeCoreTotalConstraints e) :
    R.s = computeCoreTransitionGates e + computeCoreEndpointEqualityConstraints e ∧
      (padComputeCore R hk e).s =
        computeCoreTransitionGates e + computeCoreEndpointEqualityConstraints e +
          residualTransitionGates e := by
  constructor
  · simpa [computeCoreTotalConstraints] using hs
  · change R.s + residualTransitionGates e = _
    rw [hs]
    rfl

theorem memory_endpoint_bucket_retained_once
    (R : RAP F) (hk : 0 < R.k) (e : ℕ)
    (hs : R.s = memoryCoreTotalConstraints e) :
    R.s = memoryCoreTransitionGates e + memoryCoreEndpointEqualityConstraints e ∧
      (padMemoryCore R hk e).s =
        memoryCoreTransitionGates e + memoryCoreEndpointEqualityConstraints e +
          residualTransitionGates e := by
  constructor
  · simpa [memoryCoreTotalConstraints] using hs
  · change R.s + residualTransitionGates e = _
    rw [hs]
    rfl

/-! ## 5. Semantic iff, real non-vacuity, and bad-trace preservation -/

def witnessRAP : RAP ℚ where
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

theorem witnessRAP_k_positive : 0 < witnessRAP.k := by
  norm_num [witnessRAP]

abbrev witnessConstraint : Fin witnessRAP.s :=
  ⟨0, by norm_num [witnessRAP]⟩

abbrev witnessColumn : Fin witnessRAP.w :=
  ⟨0, by norm_num [witnessRAP]⟩

def zeroTrace : Fin witnessRAP.w → ℚ[X] := fun _ => 0
def badTrace : Fin witnessRAP.w → ℚ[X] := fun _ => 1

def computeExtra : Fin witnessRAP.k → ℕ :=
  firstRoundExtra witnessRAP witnessRAP_k_positive (computeResidualColumns 3)

def paddedTrace (source : Fin witnessRAP.w → ℚ[X])
    (tail : Fin (extraWidth computeExtra) → ℚ[X]) :
    Fin (witnessRAP.w + extraWidth computeExtra) → ℚ[X] :=
  Fin.addCases source tail

theorem project_paddedTrace (source : Fin witnessRAP.w → ℚ[X])
    (tail : Fin (extraWidth computeExtra) → ℚ[X]) :
    projectTrace witnessRAP computeExtra (paddedTrace source tail) = source := by
  funext i
  simp [projectTrace, paddedTrace, columnInclusion] <;> exact Fin.addCases_left i

theorem witness_constraint_nonzero :
    witnessRAP.C witnessConstraint ≠ 0 := by
  change MvPolynomial.X (R := ℚ) (0, 0) ≠ 0
  exact MvPolynomial.X_ne_zero _

theorem zeroTrace_satisfies : witnessRAP.Satisfies zeroTrace := by
  intro i x hx
  change Polynomial.eval x
    ((MvPolynomial.aeval
      (fun q : Fin witnessRAP.w × ℕ =>
        (zeroTrace q.1).comp
          (Polynomial.C (witnessRAP.ω ^ q.2) * Polynomial.X)))
      (MvPolynomial.X (witnessColumn, 0) :
        MvPolynomial (Fin witnessRAP.w × ℕ) ℚ)) = 0
  rw [MvPolynomial.aeval_X]
  simp [zeroTrace]

theorem badTrace_rejects : ¬ witnessRAP.Satisfies badTrace := by
  intro h
  have bad := h witnessConstraint 1 (by simp [witnessRAP])
  change Polynomial.eval 1
    ((MvPolynomial.aeval
      (fun q : Fin witnessRAP.w × ℕ =>
        (badTrace q.1).comp
          (Polynomial.C (witnessRAP.ω ^ q.2) * Polynomial.X)))
      (MvPolynomial.X (witnessColumn, 0) :
        MvPolynomial (Fin witnessRAP.w × ℕ) ℚ)) = 0 at bad
  rw [MvPolynomial.aeval_X] at bad
  norm_num [badTrace] at bad

theorem repaired_compute_satisfies_iff
    (P : Fin (padComputeCore witnessRAP witnessRAP_k_positive 3).w → ℚ[X]) :
    (padComputeCore witnessRAP witnessRAP_k_positive 3).Satisfies P ↔
      witnessRAP.Satisfies (projectTrace witnessRAP computeExtra P) := by
  exact padComputeCore_satisfies_iff witnessRAP witnessRAP_k_positive 3 P

theorem repaired_memory_satisfies_iff
    (P : Fin (padMemoryCore witnessRAP witnessRAP_k_positive 3).w → ℚ[X]) :
    (padMemoryCore witnessRAP witnessRAP_k_positive 3).Satisfies P ↔
      witnessRAP.Satisfies
        (projectTrace witnessRAP
          (firstRoundExtra witnessRAP witnessRAP_k_positive (memoryResidualColumns 3)) P) := by
  exact padMemoryCore_satisfies_iff witnessRAP witnessRAP_k_positive 3 P

theorem padded_good_trace_satisfies
    (tail : Fin (extraWidth computeExtra) → ℚ[X]) :
    (padComputeCore witnessRAP witnessRAP_k_positive 3).Satisfies
      (paddedTrace zeroTrace tail) := by
  erw [repaired_compute_satisfies_iff]
  erw [project_paddedTrace]
  exact zeroTrace_satisfies

theorem padded_bad_trace_stays_bad
    (tail : Fin (extraWidth computeExtra) → ℚ[X]) :
    ¬ (padComputeCore witnessRAP witnessRAP_k_positive 3).Satisfies
      (paddedTrace badTrace tail) := by
  intro h
  apply badTrace_rejects
  have hp := (repaired_compute_satisfies_iff (paddedTrace badTrace tail)).mp h
  rw [project_paddedTrace] at hp
  exact hp

theorem padding_nonvacuous_and_discriminating :
    witnessRAP.C witnessConstraint ≠ 0 ∧
      witnessRAP.Satisfies zeroTrace ∧
      ¬ witnessRAP.Satisfies badTrace ∧
      (∀ tail, (padComputeCore witnessRAP witnessRAP_k_positive 3).Satisfies
        (paddedTrace zeroTrace tail)) ∧
      (∀ tail, ¬ (padComputeCore witnessRAP witnessRAP_k_positive 3).Satisfies
        (paddedTrace badTrace tail)) :=
  ⟨witness_constraint_nonzero, zeroTrace_satisfies, badTrace_rejects,
    padded_good_trace_satisfies, padded_bad_trace_stays_bad⟩

/-! ## 6. Metadata, width, and per-round preservation -/

theorem pad_preserves_all_metadata (R : RAP F) (extra : Fin R.k → ℕ) (n : ℕ) :
    (pad R extra n).e = R.e ∧
      (pad R extra n).k = R.k ∧
      (pad R extra n).h = R.h ∧
      (pad R extra n).d = R.d ∧
      (pad R extra n).ω = R.ω ∧
      (pad R extra n).β = R.β ∧
      (pad R extra n).H = R.H ∧
      (pad R extra n).β ≠ 0 ∧
      (∀ q ∈ (pad R extra n).I, q.2 < 2 ^ (pad R extra n).h) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (pad R extra n).β_ne_zero,
    (pad R extra n).I_bound⟩

theorem per_round_and_total_width_preserved
    (R : RAP F) (extra : Fin R.k → ℕ) (n : ℕ) :
    (∀ i, (pad R extra n).wRAP i = R.wRAP i + extra i) ∧
      (pad R extra n).w = R.w + extraWidth extra ∧
      (pad R extra n).w = ∑ i, (pad R extra n).wRAP i := by
  exact ⟨fun _ => rfl, rfl, (pad R extra n).w_eq⟩

theorem first_round_residuals_and_widths_exact :
    extraWidth computeExtra = 12 ∧
      (padComputeCore witnessRAP witnessRAP_k_positive 3).w = 13 ∧
      (padComputeCore witnessRAP witnessRAP_k_positive 3).w =
        ∑ i, (padComputeCore witnessRAP witnessRAP_k_positive 3).wRAP i := by
  constructor
  · simp [computeExtra, computeResidualColumns]
  · constructor
    · norm_num [padComputeCore, pad, computeExtra, firstRoundExtra,
        computeResidualColumns, extraWidth, witnessRAP]
    · exact (padComputeCore witnessRAP witnessRAP_k_positive 3).w_eq

/-! ## 7. Scope guards -/

abbrev padding_still_requires_source_RAP := @padComputeCore

def strict_package_still_requires_compute_B29
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    Nock.RedTeam.Batch29.B29SemanticTemplate
      (K := K) (MonolithicRAP.compTemplate F) P.compLanguage :=
  P.compSemanticTemplate

def strict_package_still_requires_memory_B29
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    Nock.RedTeam.Batch29.B29SemanticTemplate
      (K := K) (MonolithicRAP.memTemplate F) P.memLanguage :=
  P.memSemanticTemplate

noncomputable def strict_capstone_remains_conditional
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) :
    StrictThm54Statement P :=
  strictNockVMROM_of_package P

theorem paper_alias_remains_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  rfl

end
end Nock.RedTeam.Batch49

#print axioms Nock.RedTeam.Batch49.independent_symbolic_totals
#print axioms Nock.RedTeam.Batch49.independent_unfolded_production_formulas
#print axioms Nock.RedTeam.Batch49.padded_compute_matches_consumed
#print axioms Nock.RedTeam.Batch49.padded_memory_matches_consumed
#print axioms Nock.RedTeam.Batch49.reject_obsolete_cubic_source_and_final_s
#print axioms Nock.RedTeam.Batch49.appended_constraint_literal_zero
#print axioms Nock.RedTeam.Batch49.appended_constraint_vars_empty
#print axioms Nock.RedTeam.Batch49.appended_constraint_degree_zero
#print axioms Nock.RedTeam.Batch49.appended_constraint_compose_zero
#print axioms Nock.RedTeam.Batch49.every_padded_constraint_has_exact_side
#print axioms Nock.RedTeam.Batch49.compute_endpoint_bucket_retained_once
#print axioms Nock.RedTeam.Batch49.memory_endpoint_bucket_retained_once
#print axioms Nock.RedTeam.Batch49.repaired_compute_satisfies_iff
#print axioms Nock.RedTeam.Batch49.repaired_memory_satisfies_iff
#print axioms Nock.RedTeam.Batch49.padding_nonvacuous_and_discriminating
#print axioms Nock.RedTeam.Batch49.pad_preserves_all_metadata
#print axioms Nock.RedTeam.Batch49.per_round_and_total_width_preserved
#print axioms Nock.RedTeam.Batch49.strict_package_still_requires_compute_B29
#print axioms Nock.RedTeam.Batch49.strict_package_still_requires_memory_B29
#print axioms Nock.RedTeam.Batch49.strict_capstone_remains_conditional
#print axioms Nock.RedTeam.Batch49.paper_alias_remains_forest
