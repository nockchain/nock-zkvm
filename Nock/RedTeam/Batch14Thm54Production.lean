import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.ProductionAsymptotic
import Nock.NockVMROM.Thm54.CompleteProductionCost
import Nock.NockVMROM.Thm54.ProductionRawVerifier
import Nock.NockVMROM.Thm54.RawTopologyAIR
import Nock.NockVMROM.Thm54.TemplateComputeWalkCounting
import Nock.NockVMROM.Thm54.TemplateMemoryWalkCounting
import Nock.NockVMROM.Thm54.ProductionTopologyCost
import Nock.NockVMROM.Thm54.TemplateAxisCounting
import Nock.NockVMROM.Thm54.TemplateAxisStructure
import Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
import Nock.PaperNamesForestControl

/-!
# Scoped production Theorem 5.4 packet

This packet assembles the independently compiled raw-scope, production-asymptotic, and complete
cost receipts.  Its scope is the topology-enabled, verifier-generated, eight-family segmented
production predicate.  It does not repoint the paper alias and does not claim the strict
`199/196`, `e = 3` monolithic G10 object or an authenticated succinct topology trace.
-/

namespace Nock.RedTeam

open scoped Classical
open Nock Nock.Framework Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAsymptotic
open Nock.NockVMROM.Thm54.CompleteProductionCost
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.SizeWindowCounting

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable [charRing : CharP K (ringChar K)]

/-! ## Production containment and asymptotic capstones -/

/-- Direct receipt for the accepted-outside-the-five-event-union containment theorem. -/
noncomputable def b14_containment_capstone :=
  @ProductionP8Containment.accepted_outside_failureUnion

/-- Direct receipt for the exact five-event union cardinality theorem. -/
noncomputable def b14_cardinality_capstone :=
  @ProductionP8Containment.failureUnion_card_le

/-- Direct receipt for the fixed-field production false-acceptance probability theorem. -/
noncomputable def b14_probability_capstone :=
  @ProductionP8Containment.production_jointProbability_falseAcceptance_le

/-- Direct receipt for the varying-prime pointwise production theorem. -/
noncomputable def b14_pointwise_capstone :=
  @ProductionAsymptotic.production_pointwiseP8Bound

/-- Direct receipt for conditional family asymptotic soundness from componentwise polynomial
growth and the explicit semantic, operational, and capacity hypotheses. -/
@[reducible] noncomputable def b14_asymptotic_capstone :=
  @ProductionAsymptotic.production_hasExactAsymptoticSoundness

/-- The numerator/cardinality ratio itself tends to zero under the same polynomial-growth data. -/
noncomputable def b14_workload_tendsto_zero_capstone :=
  @ProductionAsymptotic.production_workload_div_card_tendsto_zero

/-! ## Data-only raw chronology and the sole semantic binding source -/

/-- Positive exact-shape declaration for the complete raw timestamp object.  Its two projections
are `claim` and `afterSeed`; there is no `semanticConsistency` or `BindsAt` projection on this
data-only type. -/
theorem b14_raw_timestamp_exact_shape
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K)) :
    V.raw.timestamp =
      { claim := V.raw.timestamp.claim
        afterSeed := V.raw.timestamp.afterSeed } :=
  ProductionP8Containment.productionRawTimestamp_exact_shape V

/-- Positive exact-shape declaration for the seed carrier.  It exposes only the config template,
execution template, and sampled-seed equation. -/
theorem b14_raw_seed_carrier_exact_shape
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (z : K) (hz : z ≠ 0) :
    V.raw.timestamp.afterSeed ⟨z, hz⟩ =
      { configTemplate := (V.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate
        executionTemplate := (V.raw.timestamp.afterSeed ⟨z, hz⟩).executionTemplate
        sampledSeed := (V.raw.timestamp.afterSeed ⟨z, hz⟩).sampledSeed } :=
  ProductionP8Containment.productionRawSeedCarrier_exact_shape V z hz

omit [Fintype K] [DecidableEq K] in
/- `BareSemanticSupport.binds` is the explicit and sole production-side source of `BindsAt`.
The raw verifier path contributes only the specialized config and execution appearing below. -/
theorem b14_semantic_binding_from_bare_support
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (S : ProductionP8Containment.BareSemanticSupport F K V)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    SemanticStrategy.BindsAt z (ProductionP8Containment.ProductionStrategy.ofBare S).skeleton
      (specializedProblem (ProductionP8Containment.ProductionStrategy.ofBare S).verifier.raw.timestamp
        z hz α lmb).cfg
      (specializedProblem (ProductionP8Containment.ProductionStrategy.ofBare S).verifier.raw.timestamp
        z hz α lmb).exec :=
  S.binds z hz α lmb

/-- Once its one skeleton is fixed, bare semantic support has no proof-carrying data fields that
can distinguish IO assignments, table witnesses, walk responses, or acceptance proofs. -/
theorem b14_bare_semantic_support_exact_scope
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (A B : ProductionP8Containment.BareSemanticSupport F K V)
    (h : A.skeleton = B.skeleton) :
    A = B :=
  ProductionP8Containment.bareSemanticSupport_no_proof_carrying_fields V A B h

/-! ## Exact production failure union -/

/-- Membership expands to exactly five events: zero seed, the fixed combined NPR census,
verifier-generated topology collision, checker-guarded template-axis failure, and the exact
low-order size-window seed event. -/
theorem b14_failureUnion_mem_exactly_five
    (T : ProductionP8Containment.ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (ω : JointCoins K) (lmb : K) :
    ω ∈ ProductionP8Containment.FailureUnion T C lmb ↔
      ω ∈ zeroSeedFailureEvent ∨
      ω ∈ collisionFailureEvent C.census ∨
      ω ∈ specializedTopologyFailureEvent T.verifier.raw lmb ∨
      ω ∈ ProductionP8Containment.guardedAxisFailureEvent T lmb ∨
      ω ∈ SizeWindowFailure T.skeleton := by
  simp only [ProductionP8Containment.FailureUnion, Finset.mem_union]
  tauto

/-- The regenerated compute-walk event is exactly zero and is not a fifth production event. -/
theorem b14_regenerated_compute_event_zero
    (T : TemplateRawJointSoundness.Strategy F K (ringChar K)) (lmb : K) :
    (TemplateRawJointSoundness.specializedComputeWalkFailureEvent T lmb).card = 0 :=
  regenerated_compute_walk_event_zero T lmb

/-- The regenerated memory-walk event is exactly zero once topology has its own event. -/
theorem b14_regenerated_memory_event_zero
    (T : TemplateRawJointSoundness.Strategy F K (ringChar K)) (lmb : K)
    (hchar : NodeEncoding.StateTagChar K)
    (hlam : ∀ z (hz : z ≠ 0) alphaM i,
      ((TemplateRawJointSoundness.specializedProblem T.timestamp z hz alphaM lmb).exec.memoryPubAt i).lambda = (TemplateRawJointSoundness.specializedProblem T.timestamp z hz alphaM lmb).cfg.challenges.lam) :
    (TemplateMemoryWalkCounting.countingData T lmb hchar hlam).failureEvent.card = 0 :=
  regenerated_memory_walk_event_zero T lmb hchar hlam

/-! ## Topology quarantine and rejection regressions -/

omit [Fintype K] [DecidableEq K] charRing in
/- The generic deep topology AIR still accepts arbitrary all-zero polynomial traces.  This is the
quarantine receipt, not a production-acceptance theorem. -/
theorem b14_allZero_generic_topology_quarantined
    (R : RawPlusIOSegmentedFamily F K) :
    (∀ kind, (computeTopologyGenericRAP R kind).Satisfies
      (RawTopologyAIR.computeAllZeroArbitraryTrace (K := K))) ∧
    (∀ kind, (memoryTopologyGenericRAP R kind).Satisfies
      (RawTopologyAIR.memoryAllZeroArbitraryTrace (K := K))) :=
  allZero_generic_satisfies R

omit [Fintype K] [DecidableEq K] charRing in
/- Positive production-surface declaration: production topology checks are evaluated only on
the two verifier-generated traces formed from the committed payload arrays. -/
theorem b14_production_topology_uses_generated_traces
    {R : RawPlusIOSegmentedFamily F K}
    (M : ProductionRawVerifier.Message R (ringChar K)) :
    M.VerifierGeneratedSegmentedTopologyChecks ↔
      (∀ kind, (computeTopologyGenericRAP R kind).Satisfies
        (computeTopologyTrace R M.topology.compute)) ∧
      (∀ kind, (memoryTopologyGenericRAP R kind).Satisfies
        (memoryTopologyTrace R M.topology.memory)) :=
  Iff.rfl

noncomputable def b14_wrong_compute_fanout_rejected :=
  @Nock.NockVMROM.Thm54.wrongComputeFanout_rejected

noncomputable def b14_wrong_memory_fanout_rejected :=
  @Nock.NockVMROM.Thm54.wrongMemoryFanout_rejected

noncomputable def b14_extra_or_missing_compute_child_rejected :=
  @Nock.NockVMROM.Thm54.extraOrMissingComputeChild_rejected

noncomputable def b14_extra_or_missing_memory_child_rejected :=
  @Nock.NockVMROM.Thm54.extraOrMissingMemoryChild_rejected

noncomputable def b14_mutated_compute_payload_rejected :=
  @Nock.NockVMROM.Thm54.mutatedComputeChildPayload_rejected

noncomputable def b14_mutated_memory_payload_rejected :=
  @Nock.NockVMROM.Thm54.mutatedMemoryChildPayload_rejected

/-- Existing malformed-axis rejection receipts. -/
noncomputable def b14_crossing_axis_rejected :=
  @ProductionAxisStructureVerifier.crossing_rejected_by_new_ancestry_check

noncomputable def b14_duplicate_read_axis_rejected :=
  @ProductionAxisStructureVerifier.duplicate_read_exponent_rejected

noncomputable def b14_mismatched_root_partition_rejected :=
  @ProductionAxisStructureVerifier.mismatched_root_partition_rejected

/-! ## Complete acceptance and cost -/

theorem b14_complete_acceptance_expansion
    (T : CompleteProductionCost.FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    T.Accepts ω lmb ↔
      CompleteProductionCost.CompleteProductionAcceptanceExpansion T ω lmb hz :=
  CompleteProductionCost.final_accepts_iff_complete_expansion T ω lmb hz

theorem b14_complete_cost_receipt
    (T : CompleteProductionCost.FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (rootBound gateBound ioBound : ℕ) :
    CompleteProductionCost.CompleteProductionCostCertificate
      T ω lmb hz rootBound gateBound ioBound
      (CompleteProductionCost.completeProductionCostAt T ω lmb hz rootBound gateBound ioBound) :=
  CompleteProductionCost.completeProductionCost_certificate
    T ω lmb hz rootBound gateBound ioBound

/-- Exact numerical scope guard: production is `188/79`, `e = 1`, while strict paper G10 is
`199/196`, `e = 3`; the two fingerprints differ. -/
theorem b14_production_fingerprint_ne_strict_g10
    (T : CompleteProductionCost.FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (rootBound gateBound ioBound : ℕ) :
    CompleteProductionCost.completeProductionAIRFingerprint
        (CompleteProductionCost.completeProductionCostAt
          T ω lmb hz rootBound gateBound ioBound) = (188, 79, 1) ∧
      CompleteProductionCost.strictPaperG10Fingerprint = (199, 196, 3) ∧
      CompleteProductionCost.completeProductionAIRFingerprint
          (CompleteProductionCost.completeProductionCostAt
            T ω lmb hz rootBound gateBound ioBound) ≠
        CompleteProductionCost.strictPaperG10Fingerprint := by
  refine ⟨rfl, ?_, CompleteProductionCost.completeProductionCost_ne_strictPaperG10
    T ω lmb hz rootBound gateBound ioBound⟩
  simp only [CompleteProductionCost.strictPaperG10Fingerprint]
  rw [Nock.NockVMROM.paperParamCost_IO_thm54.1,
    Nock.NockVMROM.paperParamCost_IO_thm54.2.1]

/-! ## Paper alias scope -/

noncomputable def b14_paper_alias_remains_forest :=
  @«Thm:NockVMROM:forest-control»

end

#print axioms b14_containment_capstone
#print axioms b14_cardinality_capstone
#print axioms b14_probability_capstone
#print axioms b14_pointwise_capstone
#print axioms b14_asymptotic_capstone
#print axioms b14_workload_tendsto_zero_capstone
#print axioms b14_raw_timestamp_exact_shape
#print axioms b14_raw_seed_carrier_exact_shape
#print axioms b14_semantic_binding_from_bare_support
#print axioms b14_bare_semantic_support_exact_scope
#print axioms b14_failureUnion_mem_exactly_five
#print axioms b14_regenerated_compute_event_zero
#print axioms b14_regenerated_memory_event_zero
#print axioms b14_allZero_generic_topology_quarantined
#print axioms b14_production_topology_uses_generated_traces
#print axioms b14_wrong_compute_fanout_rejected
#print axioms b14_wrong_memory_fanout_rejected
#print axioms b14_extra_or_missing_compute_child_rejected
#print axioms b14_extra_or_missing_memory_child_rejected
#print axioms b14_mutated_compute_payload_rejected
#print axioms b14_mutated_memory_payload_rejected
#print axioms b14_crossing_axis_rejected
#print axioms b14_duplicate_read_axis_rejected
#print axioms b14_mismatched_root_partition_rejected
#print axioms b14_complete_acceptance_expansion
#print axioms b14_complete_cost_receipt
#print axioms b14_production_fingerprint_ne_strict_g10
#print axioms b14_paper_alias_remains_forest

end Nock.RedTeam
