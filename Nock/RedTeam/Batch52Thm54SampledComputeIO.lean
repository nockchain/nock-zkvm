import Nock.RedTeam.Batch51Thm54OptimizedComputeOverlayIO
import Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace
import Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates

/-!
# Sampled compute-IO slice

Paper frame:
-/

namespace Nock.RedTeam.Batch52

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeSampledIO
open Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-- The sampled records, symbolic comparison assignment, shared-IO result, and finite witness are
all projections of one assignment indexed by the same `R.problem.cfg/exec`. -/
theorem same_object_threading (A : SampledIOSameExecutionAssignment R p) :
    A.sampled.records.requests = R.problem.exec.derivedRequestIO ∧
      A.sampled.records.responses = R.problem.exec.derivedResponseIO ∧
      SharedIOSat R p ∧
      FiniteIO.FiniteIOAccepts A.sampled.records A.sampled.coins A.sampled.witness :=
  ⟨A.requests_eq, A.responses_eq, A.sharedIOSat, A.sampled.accepts⟩

/-- The three exclusions have their exact, distinct argument positions: pole/gamma, gamma, and
pole/gamma. -/
theorem three_bad_events_exact (A : SampledIOSameExecutionAssignment R p) :
    A.sampled.coins.pole ∉
        FiniteIO.IOPoleHitEvent A.sampled.records A.sampled.coins.gamma ∧
      A.sampled.coins.gamma ∉
        FiniteIO.IORLCCollisionEvent A.sampled.records ∧
      A.sampled.coins.pole ∉
        FiniteIO.IOLogDerivEvent A.sampled.records A.sampled.coins.gamma :=
  A.three_events_good

/-- Concrete wrong-coin replay is rejected, so post-challenge columns are not coin-independent. -/
theorem wrong_coin_substitution_rejected :
    ¬ FiniteIO.FiniteIOAccepts
      Batch26.honestRecords Batch26.shiftedCoins
      (Batch26.honestWitness.transport (c₂ := Batch26.shiftedCoins)) :=
  Batch26.b26_chronology_violation_rejected

/-- Co-residence exposes exact capacity, every active-row recurrence, every inverse pin, and the
terminal equality without an appended record-indexed phase. -/
theorem co_residence_full_shape
    (A : SampledIOSameExecutionAssignment R p)
    (hcap : R.problem.cfg.compRows ≤ 2 ^ R.problem.cfg.orbit.h) :
    NoAppendedComputeIOPhase A :=
  noAppendedComputeIOPhase A hcap

/-- The generic malformed inverse, step, and terminal controls are independently available. -/
theorem malformed_controls
    (coins : FiniteIO.IOCoins K) (v : Fin 9 → K) (bad acc accNext contribution terminal : K)
    (hden : FiniteIO.compress coins v ≠ 0)
    (hinv : bad ≠ requestInv coins v)
    (hstep : accNext ≠ acc + contribution)
    (hterm : acc ≠ terminal) :
    FiniteIO.compress coins v * bad ≠ 1 ∧
      accNext - acc - contribution ≠ 0 ∧ terminal - acc ≠ 0 :=
  ⟨wrong_inverse_rejected coins v bad hden hinv,
    wrong_step_rejected acc accNext contribution hstep,
    wrong_terminal_rejected acc terminal hterm⟩

theorem overlay_cardinality_and_width :
    Fintype.card (OptimizedComputeOverlay.OverlayValues K) = Fintype.card K ^ 6 ∧
      Fintype.card OptimizedComputeCodec.ExtensionColumn = 58 :=
  ⟨Batch51.overlay_cardinality, OptimizedComputeOverlay.extensionColumn_card⟩

/-- Concrete `F73 ⊂ K73cubic` non-vacuity reaches the accepted row roundtrip. -/
noncomputable def concrete_cubic_nonvacuity :=
  OptimizedComputeSampledTrace.Concrete.honest_row_roundtrip

/-- Independent expansion receipt: under the three required nonzero-denominator premises, the
degree-four fold is iff the three inverse pins and accumulator step. -/
theorem folded_gate_exact
    (acc accNext d0 d1 d2 a0 a1 a2 : K)
    (hd0 : d0 ≠ 0) (hd1 : d1 ≠ 0) (hd2 : d2 ≠ 0) :
    FoldedProgStep3 acc accNext d0 d1 d2 a0 a1 a2 ↔
      ∃ inv0 inv1 inv2 : K,
        d0 * inv0 = 1 ∧ d1 * inv1 = 1 ∧ d2 * inv2 = 1 ∧
        accNext = acc + a0 * inv0 + a1 * inv1 + a2 * inv2 :=
  foldedProgStep3_iff_inverse_witnesses acc accNext d0 d1 d2 a0 a1 a2 hd0 hd1 hd2

theorem folded_gate_degree_and_layout :
    foldedProgStep3.degree = 4 ∧
      foldedProgStep3 =
        .Sub
          (.Mul (.Mul (.Mul (.Sub (Nock.Reified.Trans.tn 0) (Nock.Reified.tc 0))
            (Nock.Reified.tc 1)) (Nock.Reified.tc 2)) (Nock.Reified.tc 3))
          (.Add
            (.Add
              (.Mul (.Mul (Nock.Reified.tc 4) (Nock.Reified.tc 2)) (Nock.Reified.tc 3))
              (.Mul (.Mul (Nock.Reified.tc 5) (Nock.Reified.tc 1)) (Nock.Reified.tc 3)))
            (.Mul (.Mul (Nock.Reified.tc 6) (Nock.Reified.tc 1)) (Nock.Reified.tc 2))) :=
  ⟨foldedProgStep3_degree, rfl⟩

/-- The nonzero premises are load-bearing: with zero denominators the fold may vanish while an
inverse constituent fails. -/
theorem zero_denominator_counterexample :
    FoldedProgStep3 (K := Batch26.F7) 0 1 0 0 0 1 0 0 ∧
      ¬ ∃ inv0 : Batch26.F7, (0 : Batch26.F7) * inv0 = 1 := by
  constructor
  · norm_num [FoldedProgStep3]
  · simp

theorem scope_guard :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Batch51.paper_alias_is_still_forest

end
end Nock.RedTeam.Batch52

#print axioms Nock.RedTeam.Batch52.same_object_threading
#print axioms Nock.RedTeam.Batch52.three_bad_events_exact
#print axioms Nock.RedTeam.Batch52.wrong_coin_substitution_rejected
#print axioms Nock.RedTeam.Batch52.co_residence_full_shape
#print axioms Nock.RedTeam.Batch52.malformed_controls
#print axioms Nock.RedTeam.Batch52.overlay_cardinality_and_width
#print axioms Nock.RedTeam.Batch52.concrete_cubic_nonvacuity
#print axioms Nock.RedTeam.Batch52.folded_gate_exact
#print axioms Nock.RedTeam.Batch52.folded_gate_degree_and_layout
#print axioms Nock.RedTeam.Batch52.zero_denominator_counterexample
#print axioms Nock.RedTeam.Batch52.scope_guard
