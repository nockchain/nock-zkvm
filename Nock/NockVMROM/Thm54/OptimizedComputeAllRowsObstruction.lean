import Nock.NockVMROM.Thm54.OptimizedComputeTemplate

/-!
# Obstruction to the current optimized compute all-row connective

`WalkSat` applies its initial equations only at row `1`, its transition equations only on
`1 ≤ i < h`, and its terminal closure only at row `h`.  The current
`compOptimizedCoreRAP`, by contrast, places transition, initial, terminal, and endpoint-equality
constraints in one list and `Framework.RAP.Satisfies` evaluates every member of that list at every
point of the one shared domain `H`.

The two facts are not equivalent for a multi-row walk.  The concrete two-row walk below satisfies
`WalkSat`, has terminal accumulator zero, and has `ln 2 ≠ α`, so imposing the initial line equation
on every active row rejects a valid segmented walk.  The second theorem records, directly against
the constructed 187/87 core, that current satisfaction does impose every compiled gate at every
active point.

This is an implementation obstruction for the current monolithic template, not a verdict about the
paper construction.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeAllRowsObstruction

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

open Nock
open Nock.Framework
open Nock.Reified
open Module
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeTypedLowering
open scoped Polynomial

noncomputable section

abbrev F73 := ZMod 73

def twoRowLn (i : ℕ) : F73 := 2 ^ i
def zeroColumn (_ : ℕ) : F73 := 0
def zeroChildren (_ _ : ℕ) : F73 := 0
def zeroFanout (_ : ℕ) : ℕ := 0

/-- The segmented walk language does not repeat its first-row line constraint at row two. -/
theorem twoRowWalkSat :
    Walk.WalkSat zeroColumn zeroChildren zeroFanout
      twoRowLn zeroColumn zeroColumn 2 0 0 2 := by
  constructor
  · norm_num
  · norm_num [twoRowLn]
  · intro i hi hlt
    interval_cases i
    norm_num [twoRowLn]
  · simp [zeroColumn, zeroFanout]
  · intro i hi hlt
    interval_cases i
    simp [zeroColumn, zeroFanout]
  · simp [zeroColumn, zeroChildren, zeroFanout]
  · intro i hi hlt
    interval_cases i
    simp [zeroColumn, zeroChildren, zeroFanout]

def AllRowInitialLine {K : Type*} (ln : ℕ → K) (α : K) (n : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n → ln i = α

/-- A valid two-row walk has `ln 2 = α²`, not a second copy of the row-one equation `ln = α`. -/
theorem twoRowWalk_not_allRowInitialLine :
    ¬ AllRowInitialLine twoRowLn (2 : F73) 2 := by
  intro h
  have h2 := h 2 (by omega) (by omega)
  norm_num [twoRowLn] at h2
  have hne : (4 : F73) ≠ 2 := by decide
  exact hne h2

/-- Compiled semantic counterexample to replacing segmented endpoint domains by one all-gate
domain: the exact walk and terminal closure hold, but the initial equation does not hold at every
active row. -/
theorem segmentedWalk_not_globalEndpoints :
    Walk.WalkSat zeroColumn zeroChildren zeroFanout
        twoRowLn zeroColumn zeroColumn 2 0 0 2 ∧
      zeroColumn 2 = 0 ∧
      ¬ AllRowInitialLine twoRowLn (2 : F73) 2 :=
  ⟨twoRowWalkSat, rfl, twoRowWalk_not_allRowInitialLine⟩

/-- Mixed physical environment exposing only the line column and the walk challenge.  This is the
part of a decoded optimized row read by `optimizedWalkLn1`. -/
def twoRowEndpointEnv (i : ℕ) : Env F73 where
  trace j := if j = 68 then twoRowLn i else 0
  traceNext _ := 0
  chal j := if j = 0 then 2 else 0
  pub _ := 0

/-- The current optimized endpoint source is exactly the first-row equation, and it is nonzero on
row two of the valid segmented walk. -/
theorem optimizedWalkLn1_nonzero_on_valid_second_row :
    optimizedWalkLn1.eval (twoRowEndpointEnv 2) ≠ 0 := by
  norm_num [optimizedWalkLn1, Trans.walkLn1, Expr.subst, walkInitialSubst,
    Reified.tc, Reified.chl, OptimizedComputeSubstitution.lnCur,
    OptimizedComputeSubstitution.ext0, twoRowEndpointEnv, twoRowLn, Expr.eval]
  decide

/-- Hence the repaired source conjunction cannot be imposed uniformly on both rows while remaining
equivalent to the segmented two-row walk language. -/
theorem no_global_optimizedWalkLn1_for_twoRowWalk :
    ¬ ∀ i, 1 ≤ i → i ≤ 2 →
      optimizedWalkLn1.eval (twoRowEndpointEnv i) = 0 := by
  intro h
  exact optimizedWalkLn1_nonzero_on_valid_second_row (h 2 (by omega) (by omega))

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- `Framework.RAP.Satisfies` has one shared constraint domain: every constraint is enforced at
every point of `R.H`.  There is no constraint-specific boundary or transition domain in this
interface. -/
theorem satisfies_enforces_each_constraint_on_whole_H
    (R : RAP F) (P : Fin R.w → F[X]) (hsat : R.Satisfies P) :
    ∀ i : Fin R.s, ∀ x ∈ R.H, (R.compose P i).eval x = 0 :=
  hsat

/-- The current optimized core is an instance of that shared-domain interface. -/
theorem coreSatisfies_enforces_each_constraint_on_whole_H
    [FiniteDimensional F K] {h : ℕ}
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictExtension.StrictOrbitDomain F 3 h) (H : Finset F) :
    let R := compOptimizedCoreRAP b chalVal pubVal orbit H
    ∀ (P : Fin R.w → F[X]), R.Satisfies P →
      ∀ i : Fin R.s, ∀ x ∈ H, (R.compose P i).eval x = 0 := by
  dsimp only
  intro P hsat
  exact satisfies_enforces_each_constraint_on_whole_H _ P hsat

/-- The gate list used by that core includes every coordinate of both degree-one endpoint gates.
Combined with `coreSatisfies_enforces_each_constraint_on_whole_H`, these are therefore global
constraints on `H`, not first/terminal-row constraints. -/
theorem endpointDeg1_coordinates_mem_currentCore
    (b : Basis (Fin 3) F K) :
    ∀ t ∈ loweredEndpointDeg1, ∀ k : Fin 3,
      typedCompile b t k ∈ compOptimizedAllGates b := by
  intro t ht k
  have hm : typedCompile b t k ∈ compileTypedList b loweredEndpointDeg1 := by
    simp only [compileTypedList, List.mem_flatMap, List.mem_ofFn]
    exact ⟨t, ht, k, rfl⟩
  simp only [compOptimizedAllGates, List.mem_append]
  exact Or.inl (Or.inl (Or.inr hm))

/-! ## Degree obstruction for a literal fixed-column transition mask

`FixedPreprocessingRAP` binds slot 12 as a polynomial, but the wrapped `Framework.RAP` still sees
that slot as an ordinary trace variable when checking `MvPolynomial.totalDegree`.  Consequently a
literal multiplication by `1-isLast` raises trace degree by one.  This is harmless for the linear
line transition, but it takes the genuine optimized walk-count, walk-accumulator, and sampled-IO
folds from degree four to degree five. -/

def notLastTraceMask : Expr :=
  .Sub (.Const 1) (.Var .traceCur 12)

def lastMaskedTransition (e : Expr) : Expr :=
  .Mul notLastTraceMask e

theorem literal_fixed_last_mask_degree_census :
    (lastMaskedTransition
        (Trans.lnChainExpr.subst OptimizedComputeSubstitution.computeSubst)).degree = 2 ∧
      (lastMaskedTransition
        (Trans.walkCountStep.subst OptimizedComputeSubstitution.walkSubst)).degree = 5 ∧
      (lastMaskedTransition
        (Trans.walkAccStep.subst OptimizedComputeSubstitution.walkSubst)).degree = 5 ∧
      (lastMaskedTransition
        OptimizedComputeFiniteIOGates.optimizedFoldedProgStep3).degree = 5 := by
  decide

/-- Therefore the direct fixed-column masking requested by the shared all-row domain cannot inhabit
the current degree-four `Framework.RAP`; fixed polynomial binding alone does not make preprocessing
variables degree-zero coefficients in `RAP.C`. -/
theorem literal_fixed_last_mask_exceeds_degree_four :
    ¬ (lastMaskedTransition
        (Trans.walkCountStep.subst OptimizedComputeSubstitution.walkSubst)).degree ≤ 4 ∧
      ¬ (lastMaskedTransition
        (Trans.walkAccStep.subst OptimizedComputeSubstitution.walkSubst)).degree ≤ 4 ∧
      ¬ (lastMaskedTransition
        OptimizedComputeFiniteIOGates.optimizedFoldedProgStep3).degree ≤ 4 := by
  decide

#print axioms twoRowWalkSat
#print axioms twoRowWalk_not_allRowInitialLine
#print axioms segmentedWalk_not_globalEndpoints
#print axioms optimizedWalkLn1_nonzero_on_valid_second_row
#print axioms no_global_optimizedWalkLn1_for_twoRowWalk
#print axioms satisfies_enforces_each_constraint_on_whole_H
#print axioms coreSatisfies_enforces_each_constraint_on_whole_H
#print axioms endpointDeg1_coordinates_mem_currentCore
#print axioms literal_fixed_last_mask_degree_census
#print axioms literal_fixed_last_mask_exceeds_degree_four

end
end OptimizedComputeAllRowsObstruction
end Nock.NockVMROM.Thm54
