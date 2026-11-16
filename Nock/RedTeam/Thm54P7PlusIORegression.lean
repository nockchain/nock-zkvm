import Nock.NockVMROM.Thm54.PlusIOSegmentedRAP
import Nock.RedTeam.Thm54P3Nonvacuity

/-!
# Exact `+IO` regression on the committed balanced execution

The
repository does not currently export concrete injective finite-coordinate encoders for the full
compute and memory node-label types.  Consequently this file does not invent such encoders and
does not claim a closed concrete `PlusIOSegmentedFamily`.

`familyOfRemainingNodeEncoders` states the exact remaining constructor hypotheses: two widths,
two encoders, and their injectivity proofs.
-/

open scoped Classical

namespace Nock.RedTeam.Thm54P7PlusIORegression

open Nock Nock.NockVMROM.Thm54
open Nock.RedTeam.Thm54P3Nonvacuity

noncomputable section

abbrev K17 := Nock.RedTeam.Thm54P2Nonvacuity.K17

def problem : ExactCanonicalRAPProblem K17 K17 :=
  ExactCanonicalRAPProblem.ofChained production_chained

theorem problem_cfg_exec :
    problem.cfg = cfg ∧ problem.exec = exec :=
  ⟨rfl, rfl⟩

theorem production_p4_same_execution :
    ExactCanonicalRAPSameExecutionCertificate problem :=
  production_chained.exactCanonicalRAP_sameExecution

/-- The uniqueness strengthening required for `LIO`; this is deliberately additional to the
plain chained witness. -/
def semanticWitness : SemanticIOWitness cfg exec where
  toSemanticIOPreimage := semanticPreimage
  semanticRequests_nodup := by simp [semanticPreimage]

/-- The exact derived lists satisfy the strong IO endpoint through the semantic witness, not
through plain `ChainedSemanticExactLanguage`. -/
theorem production_LIO :
    IO.LIO cfg.Ksz exec.derivedRequestIO exec.derivedResponseIO :=
  (semanticWitness.strongExactLanguage_of_semanticExactLanguage
    production_semantic_exact).2.2

/-- Exact remaining constructor hypotheses for this committed witness.

No capacity, endpoint, configuration, execution, table, or semantic-IO hypothesis remains:
only concrete injective coordinate encoders for the two full node-label types are parameters. -/
def familyOfRemainingNodeEncoders
    (compNodeWidth : ℕ)
    (compNodeEncode :
      (ComputeTable.State × ComputeTable.DTcomp K17) → Fin compNodeWidth → K17)
    (compNodeEncode_injective : ∀ a b, compNodeEncode a = compNodeEncode b →
      ComputeTable.computeLabelOf a = ComputeTable.computeLabelOf b)
    (memNodeWidth : ℕ)
    (memNodeEncode :
      (MemoryTable.MState × MemoryTable.DTmem K17) → Fin memNodeWidth → K17)
    (memNodeEncode_injective : ∀ a b, memNodeEncode a = memNodeEncode b →
      MemoryTable.memoryLabelOf a = MemoryTable.memoryLabelOf b) :
    PlusIOSegmentedFamily K17 K17 where
  problem := problem
  computeWalkAlpha := problem.cfg.challenges.α
  memoryWalkAlpha := problem.cfg.challenges.α
  walkGamma := problem.cfg.challenges.γ
  compNodeWidth := compNodeWidth
  compNodeEncode := compNodeEncode
  compNodeEncode_labelOf := compNodeEncode_injective
  memNodeWidth := memNodeWidth
  memNodeEncode := memNodeEncode
  memNodeEncode_labelOf := memNodeEncode_injective
  requests := 0
  responses := 0
  outMem := 0
  progIO_capacity := by
    change exec.derivedRequestIO.length + 1 ≤ 2 ^ cfg.orbit.h
    rw [derived_request_singleton]
    norm_num [cfg, orbit8]
  memIO_capacity := by
    change exec.derivedResponseIO.length + 1 ≤ 2 ^ cfg.orbit.h
    rw [derived_response_singleton]
    norm_num [cfg, orbit8]

/-- Once the two honest node encoders are supplied, `SemanticIOWitness` constructs one shared IO
assignment over the actual derived lists and chooses its public endpoint values. -/
theorem production_io_assignment_exists
    (compNodeWidth : ℕ)
    (compNodeEncode :
      (ComputeTable.State × ComputeTable.DTcomp K17) → Fin compNodeWidth → K17)
    (compNodeEncode_injective : ∀ a b, compNodeEncode a = compNodeEncode b →
      ComputeTable.computeLabelOf a = ComputeTable.computeLabelOf b)
    (memNodeWidth : ℕ)
    (memNodeEncode :
      (MemoryTable.MState × MemoryTable.DTmem K17) → Fin memNodeWidth → K17)
    (memNodeEncode_injective : ∀ a b, memNodeEncode a = memNodeEncode b →
      MemoryTable.memoryLabelOf a = MemoryTable.memoryLabelOf b) :
    ∃ requests responses outMem : IOField K17,
      Nonempty (ExactDerivedIOAssignment
        ((familyOfRemainingNodeEncoders
          compNodeWidth compNodeEncode compNodeEncode_injective
          memNodeWidth memNodeEncode memNodeEncode_injective).withIOEndpoints
            requests responses outMem) 17) := by
  apply
    ExactDerivedIOAssignment.exists_with_public_endpoints_of_semanticIOWitness
      (familyOfRemainingNodeEncoders
        compNodeWidth compNodeEncode compNodeEncode_injective
        memNodeWidth memNodeEncode memNodeEncode_injective)
  · change cfg.Ksz < 17
    norm_num [cfg]
  · exact semanticWitness
  · exact production_semantic_exact

end

end Nock.RedTeam.Thm54P7PlusIORegression

#print axioms Nock.RedTeam.Thm54P7PlusIORegression.problem_cfg_exec
#print axioms Nock.RedTeam.Thm54P7PlusIORegression.production_p4_same_execution
#print axioms Nock.RedTeam.Thm54P7PlusIORegression.production_LIO
#print axioms Nock.RedTeam.Thm54P7PlusIORegression.familyOfRemainingNodeEncoders
#print axioms Nock.RedTeam.Thm54P7PlusIORegression.production_io_assignment_exists
