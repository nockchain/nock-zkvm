import Nock.NockVMROM.Thm54.OptimizedComputeCoreInventory
import Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
import Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
import Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
import Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal

/-!
# Obstruction to the direct optimized compute gate-basis assembly

The optimized compute inventory reserves twenty extension transition gates for the table/walk
block and one for sampled program IO.  The inactive-safe sampled-IO repair, however, is an exact
four-gate production block: three semantic denominator pins and the degree-four accumulator fold.
This file records the resulting count obstruction and a concrete semantic reason that the three
pins cannot simply be discarded.

This is an implementation obstruction, not a verdict about the paper construction.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeGateBasisObstruction

open Nock
open Nock.Reified
open Module
open OptimizedComputeCoreInventory
open OptimizedComputeFiniteIOGates
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeFinalTypedLowering
open OptimizedComputeCorrectedFinal
open OptimizedComputeFinal
open OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.CoordinateCompiler

theorem reviewed_sampledIO_gate_count :
    optimizedSampledIOTransitionGates.length = 4 :=
  optimizedSampledIOTransitionGates_length

/-- The optimized source inventory allocates exactly one extension transition to program IO. -/
theorem allocated_sampledIO_gate_count :
    Fintype.card ProgramIOExtensionTransition = 1 := by
  rfl

theorem reviewed_sampledIO_ne_allocated_count :
    optimizedSampledIOTransitionGates.length ≠
      Fintype.card ProgramIOExtensionTransition := by
  rw [reviewed_sampledIO_gate_count, allocated_sampledIO_gate_count]
  decide

theorem direct_reviewed_extension_count
    (tableWalk : List Expr)
    (htableWalk :
      tableWalk.length = Fintype.card TableWalkExtensionTransition) :
    (tableWalk ++ optimizedSampledIOTransitionGates).length = 24 := by
  rw [List.length_append, htableWalk, reviewed_sampledIO_gate_count]
  rfl

theorem direct_reviewed_extension_count_impossible
    (tableWalk : List Expr)
    (htableWalk :
      tableWalk.length = Fintype.card TableWalkExtensionTransition) :
    (tableWalk ++ optimizedSampledIOTransitionGates).length ≠
      Fintype.card ExtensionTransition := by
  rw [direct_reviewed_extension_count tableWalk htableWalk,
    extensionTransition_card]
  decide

theorem repaired_extension_allocation :
    nonIOTransitionGates.length + optimizedSampledIOTransitionGates.length =
      Fintype.card ExtensionTransition := by
  rw [nonIOTransitionGates_length, optimizedSampledIOTransitionGates_length,
    extensionTransition_card]

/-- The repaired list itself realizes the exact extension-transition cardinality. -/
theorem repaired_extension_gate_count :
    extTransitionGates.length = Fintype.card ExtensionTransition := by
  rw [extTransitionGates_length, extensionTransition_card]

theorem accumulator_fold_alone_accepts_cancellation :
    optimizedFoldedProgStep3.eval cancellationRegressionEnv = 0 := by
  apply (optimizedFoldedProgStep3_eval cancellationRegressionEnv).2
  norm_num [FoldedProgStep3, OptimizedComputeSubstitution.sampledIOSubst,
    OptimizedComputeSubstitution.sampledActive,
    OptimizedComputeSubstitution.sampledDenomWitness,
    OptimizedComputeSubstitution.overlayCoord, Nock.Reified.allStates,
    OptimizedComputeSubstitution.overlayANat,
    OptimizedComputeSubstitution.overlayBNat,
    OptimizedComputeSubstitution.pubFP, OptimizedComputeSubstitution.ext0,
    Nock.Reified.opCol, cancellationRegressionEnv, Expr.eval]

/-- The single degree-four accumulator fold is not semantically equivalent to the repaired
four-gate block: it accepts the concrete cancellation assignment rejected by a denominator pin. -/
theorem accumulator_fold_alone_not_exact :
    ¬ (optimizedFoldedProgStep3.eval cancellationRegressionEnv = 0 ↔
      ∀ g ∈ optimizedSampledIOTransitionGates,
        g.eval cancellationRegressionEnv = 0) := by
  intro hiff
  have hall := hiff.mp accumulator_fold_alone_accepts_cancellation
  obtain ⟨g, hg, hbad⟩ := cancellation_regression_rejected
  exact hbad (hall g hg)

/-- It is specifically an exact-cardinality/exact-semantics conflict. -/
theorem reviewed_sampledIO_degree_four :
    ∀ g ∈ optimizedSampledIOTransitionGates, g.degree ≤ 4 :=
  optimizedSampledIOTransitionGates_degree

/-! ## Final-compiler reverse-direction obstruction -/

/-- The production family fold has the same unavoidable cancellation behavior at its disjoint
compiler challenge.  Moving the challenge namespace repairs aliasing, but cannot make a
many-to-one RLC injective on arbitrary trace residual vectors. -/
def finalCancellationEnv : Env ℚ where
  trace := fun _ => 0
  traceNext := fun _ => 0
  chal := fun i => if i = compilerChallengeBase then 1 else 0
  pub := fun _ => 0

theorem final_rlcFold_cancellation_counterexample :
    (finalRlcFold [.Const 1, .Const (-1)]).eval finalCancellationEnv = 0 ∧
      ¬ (∀ e ∈ ([.Const 1, .Const (-1)] : List Expr),
        e.eval finalCancellationEnv = 0) := by
  constructor
  · norm_num [finalRlcFold, finalFoldChallenge, finalCancellationEnv,
      compilerChallengeBase, Expr.eval]
  · simp [Expr.eval]

/-- Consequently there is no unconditional decoder theorem from one production RLC equation to
the full source family.  Any arbitrary-trace reverse theorem must either assume the explicit
`CollisionFree` event or return a semantic-or-collision disjunction. -/
theorem no_unconditional_final_rlc_decoder :
    ¬ (∀ (env : Env ℚ) (es : List Expr),
      (finalRlcFold es).eval env = 0 ↔ ∀ e ∈ es, e.eval env = 0) := by
  intro h
  exact final_rlcFold_cancellation_counterexample.2
    ((h finalCancellationEnv [.Const 1, .Const (-1)]).1
      final_rlcFold_cancellation_counterexample.1)

/-- Endpoint selector leaves are currently lowered as extension-valued publics.  Thus selector
index 20 is read at cubic raw coordinates `60..62`, whereas the scalar equality gate reads raw
index 20.  This is a same-object public-valuation obstruction, independent of the RLC issue. -/
theorem endpoint_selector_public_index_mismatch
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (k : Fin 3) :
    finalTypedCompile b (.publicVal 20) k =
        .var .publicVal (60 + (k : ℕ)) ∧
      60 + (k : ℕ) ≠ 20 := by
  constructor
  · rfl
  · omega


/-- The initial walk endpoint gate is itself an RLC at compiler challenge 11.  Vanishing of this
gate plus challenge-9 collision freedom does not recover the count equation when challenge 11 is
zero. -/
theorem endpoint_init_fold_requires_challenge11_exclusion
    {K : Type*} [Field K] (env : Env K)
    (hchal : env.chal (compilerChallengeBase + 2) = 0)
    (hln : finalMaskedWalkLn1.eval env = 0)
    (hcount : finalMaskedWalkCount1.eval env ≠ 0) :
    finalMaskedWalkInitFold.eval env = 0 ∧
      ¬ (finalMaskedWalkLn1.eval env = 0 ∧ finalMaskedWalkCount1.eval env = 0) := by
  constructor
  · simp [finalMaskedWalkInitFold, Expr.eval, hchal, hln]
  · exact fun h => hcount h.2

def selectorPublicCancellationEnv : Env ℚ where
  trace i := if i = 0 ∨ i = 11 then 1 else 0
  traceNext := fun _ => 0
  chal i := if i = finalScalarChallengeBase then 1 else 0
  pub i := if i = 22 then 1 else 0

/-- The corrected scalar-public equality surface still compresses eleven equalities with scalar
challenge 36.  At challenge one, opposite errors in slots 20 and 22 cancel while both individual
equalities are false. -/
theorem selector_public_rlc_requires_challenge36_exclusion :
    (CoeffExpr.mul isFirstVar (finalSelectorPublicCheck .traceCur 20)).eval
        selectorPublicCancellationEnv = 0 ∧
      selectorPublicCancellationEnv.trace 0 ≠ selectorPublicCancellationEnv.pub 20 ∧
      selectorPublicCancellationEnv.trace 2 ≠ selectorPublicCancellationEnv.pub 22 := by
  norm_num [selectorPublicCancellationEnv, finalSelectorPublicCheck, CoeffExpr.sumList,
    CoeffExpr.eval, isFirstVar, bv, finalScalarChallengeBase, List.range, List.range.loop]

/-- The honest replacement must additionally exclude the challenge-11 endpoint
fold and challenge-36 selector-public RLC events. -/
def CorrectedFinalAdditionalCollisionPremises {F K : Type*} [Field F] [Field K]
    (envF : Env F) (envK : Env K) : Prop :=
  ((finalMaskedWalkInitFold.eval envK = 0) →
    finalMaskedWalkLn1.eval envK = 0 ∧ finalMaskedWalkCount1.eval envK = 0) ∧
  ((CoeffExpr.mul isFirstVar (finalSelectorPublicCheck .traceCur 20)).eval envF = 0 →
    ∀ i < 11, envF.trace i = envF.pub (20 + i)) ∧
  ((CoeffExpr.mul isLastVar (finalSelectorPublicCheck .traceCur 31)).eval envF = 0 →
    ∀ i < 11, envF.trace i = envF.pub (31 + i))

#print axioms reviewed_sampledIO_ne_allocated_count
#print axioms direct_reviewed_extension_count_impossible
#print axioms repaired_extension_allocation
#print axioms repaired_extension_gate_count
#print axioms accumulator_fold_alone_not_exact
#print axioms reviewed_sampledIO_degree_four
#print axioms final_rlcFold_cancellation_counterexample
#print axioms no_unconditional_final_rlc_decoder
#print axioms endpoint_selector_public_index_mismatch
#print axioms endpoint_init_fold_requires_challenge11_exclusion
#print axioms selector_public_rlc_requires_challenge36_exclusion

end OptimizedComputeGateBasisObstruction
end Nock.NockVMROM.Thm54
