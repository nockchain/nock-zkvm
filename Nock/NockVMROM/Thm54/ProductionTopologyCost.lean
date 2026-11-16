import Nock.NockVMROM.Thm54.ExactCost
import Nock.NockVMROM.Thm54.ProductionRawVerifier
import Nock.NockVMROM.Thm54.TemplateComputeWalkCounting
import Nock.NockVMROM.Thm54.TemplateMemoryWalkCounting

/-!
# Exact cost of the production topology verifier

The two additional components are the verifier-generated compute and memory topology AIRs used by
`ProductionRawVerifier`.  IO remains visible inside the unchanged six-family record, while topology
is recorded in two new, separate fields.

This is not a succinct-verifier claim.  The verifier constructs and inspects the topology rows
deterministically.  The natural work receipts below count all generated field cells and all
authoritative child-slot reads, and bound that work by a fixed constant times
`compRows * 3 + memRows * 2`.
-/

namespace Nock.NockVMROM.Thm54

open Classical
open Nock Framework Framework.Reify Framework.Thm54
open Nock.Reified

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {p : ℕ} [CharP K p]

/-- Reuse the exact-cost component format for one verifier-generated topology AIR. -/
def topologyComponentCost (air : AIR) : ComponentCost where
  localWidth := air.numTraceCols
  constraints := air.constraints.length
  degree4Gates := air.constraints.countP (fun c => c.degree == 4)
  airMaxDegree := air.maxDegree
  histogram := degreeHistogram air

/-- Production cost data: the old six-family record is preserved literally and the two topology
families are added as separate components. -/
structure ReifiedProductionCost where
  sixFamily : ReifiedFinalCost
  computeTopology : ComponentCost
  memoryTopology : ComponentCost
  /-- Aggregate disjoint accounting, not the width of one monolithic RAP. -/
  computeWidthWithTopology : ℕ
  /-- Aggregate disjoint accounting, not the width of one monolithic RAP. -/
  memoryWidthWithTopology : ℕ
  sixFamilyConstraints : ℕ
  topologyConstraints : ℕ
  totalConstraints : ℕ
  familyCount : ℕ
  segmentKindsPerFamily : ℕ
  acceptanceEvaluations : ℕ
deriving DecidableEq, Repr

private abbrev sixFamilyCost : ReifiedFinalCost := finalSegmentedCost (K := K)
private abbrev computeTopoAIR : AIR := RawTopologyAIR.computeAIR
private abbrev memoryTopoAIR : AIR := RawTopologyAIR.memoryAIR

/-- Exact production data computed from the existing six-family record and the two literal
topology AIR objects. -/
def productionTopologyCost : ReifiedProductionCost where
  sixFamily := sixFamilyCost (K := K)
  computeTopology := topologyComponentCost computeTopoAIR
  memoryTopology := topologyComponentCost memoryTopoAIR
  computeWidthWithTopology :=
    sixFamilyCost (K := K).computeDisjointWidth + computeTopoAIR.numTraceCols
  memoryWidthWithTopology :=
    sixFamilyCost (K := K).memoryDisjointWidth + memoryTopoAIR.numTraceCols
  sixFamilyConstraints :=
    sixFamilyCost (K := K).computeTable.constraints +
      sixFamilyCost (K := K).computeWalk.constraints +
      sixFamilyCost (K := K).computeIO.constraints +
      sixFamilyCost (K := K).memoryTable.constraints +
      sixFamilyCost (K := K).memoryWalk.constraints +
      sixFamilyCost (K := K).memoryIO.constraints
  topologyConstraints :=
    computeTopoAIR.constraints.length + memoryTopoAIR.constraints.length
  totalConstraints :=
    sixFamilyCost (K := K).computeTable.constraints +
      sixFamilyCost (K := K).computeWalk.constraints +
      sixFamilyCost (K := K).computeIO.constraints +
      sixFamilyCost (K := K).memoryTable.constraints +
      sixFamilyCost (K := K).memoryWalk.constraints +
      sixFamilyCost (K := K).memoryIO.constraints +
      computeTopoAIR.constraints.length + memoryTopoAIR.constraints.length
  familyCount := 8
  segmentKindsPerFamily := 4
  acceptanceEvaluations := 8 * 4

/-- Mechanical interface and degree census of both topology AIRs. -/
theorem topology_air_exact_census :
    productionTopologyCost (K := K).computeTopology.localWidth = 86 ∧
      productionTopologyCost (K := K).memoryTopology.localWidth = 34 ∧
      computeTopoAIR.numChallenges = 1 ∧
      memoryTopoAIR.numChallenges = 1 ∧
      computeTopoAIR.numPublic = 0 ∧
      memoryTopoAIR.numPublic = 0 ∧
      productionTopologyCost (K := K).computeTopology.constraints = 34 ∧
      productionTopologyCost (K := K).memoryTopology.constraints = 15 ∧
      productionTopologyCost (K := K).computeTopology.airMaxDegree = 2 ∧
      productionTopologyCost (K := K).memoryTopology.airMaxDegree = 2 ∧
      productionTopologyCost (K := K).computeTopology.degree4Gates = 0 ∧
      productionTopologyCost (K := K).memoryTopology.degree4Gates = 0 := by
  simp only [productionTopologyCost, sixFamilyCost, finalSegmentedCost,
    topologyComponentCost, computeTopoAIR, memoryTopoAIR]
  decide

/-- Exact topology degree histograms in `(0,1,2,3,4,≥5)` order. -/
theorem topology_degree_histograms :
    productionTopologyCost (K := K).computeTopology.histogram = ⟨0, 1, 33, 0, 0, 0⟩ ∧
      productionTopologyCost (K := K).memoryTopology.histogram = ⟨0, 1, 14, 0, 0, 0⟩ := by
  simp only [productionTopologyCost, sixFamilyCost, finalSegmentedCost,
    topologyComponentCost, computeTopoAIR, memoryTopoAIR]
  decide

/-- Per-kind topology constraint census.  Only row segments contain constraints. -/
theorem topology_constraints_by_kind :
    (kindSeg computeTopoAIR .row).constraints.length = 34 ∧
      (kindSeg computeTopoAIR .boundary).constraints.length = 0 ∧
      (kindSeg computeTopoAIR .transition).constraints.length = 0 ∧
      (kindSeg computeTopoAIR .terminal).constraints.length = 0 ∧
      (kindSeg memoryTopoAIR .row).constraints.length = 15 ∧
      (kindSeg memoryTopoAIR .boundary).constraints.length = 0 ∧
      (kindSeg memoryTopoAIR .transition).constraints.length = 0 ∧
      (kindSeg memoryTopoAIR .terminal).constraints.length = 0 := by
  simp only [productionTopologyCost, sixFamilyCost, finalSegmentedCost,
    topologyComponentCost, computeTopoAIR, memoryTopoAIR]
  decide

/-- Per-kind topology maximum degrees. -/
theorem topology_max_degree_by_kind :
    (kindSeg computeTopoAIR .row).maxDegree = 2 ∧
      (kindSeg computeTopoAIR .boundary).maxDegree = 0 ∧
      (kindSeg computeTopoAIR .transition).maxDegree = 0 ∧
      (kindSeg computeTopoAIR .terminal).maxDegree = 0 ∧
      (kindSeg memoryTopoAIR .row).maxDegree = 2 ∧
      (kindSeg memoryTopoAIR .boundary).maxDegree = 0 ∧
      (kindSeg memoryTopoAIR .transition).maxDegree = 0 ∧
      (kindSeg memoryTopoAIR .terminal).maxDegree = 0 := by
  simp only [productionTopologyCost, sixFamilyCost, finalSegmentedCost,
    topologyComponentCost, computeTopoAIR, memoryTopoAIR]
  decide

/-- Every topology segment uses the same authoritative per-kind domain as its corresponding
compute or memory family. -/
theorem topology_segment_domains (R : RawPlusIOSegmentedFamily F K)
    (kind : ConstraintKind) :
    (computeTopologyGenericRAP R kind).H = R.cfg.computeDomain kind ∧
      (memoryTopologyGenericRAP R kind).H = R.cfg.memoryDomain kind := by
  exact ⟨rfl, rfl⟩

/-- Exact additive delta from six families to the topology-enabled eight-family verifier.  IO is
not folded into topology: its existing `2`/`3`-column components remain separately visible. -/
theorem production_cost_exact_delta :
    productionTopologyCost (K := K).sixFamily.computeIO.localWidth = 2 ∧
      productionTopologyCost (K := K).sixFamily.memoryIO.localWidth = 3 ∧
      productionTopologyCost (K := K).computeTopology.localWidth = 86 ∧
      productionTopologyCost (K := K).memoryTopology.localWidth = 34 ∧
      productionTopologyCost (K := K).computeWidthWithTopology = 188 ∧
      productionTopologyCost (K := K).memoryWidthWithTopology = 79 ∧
      productionTopologyCost (K := K).sixFamilyConstraints = 627 ∧
      productionTopologyCost (K := K).topologyConstraints = 49 ∧
      productionTopologyCost (K := K).totalConstraints = 676 ∧
      productionTopologyCost (K := K).familyCount = 8 ∧
      productionTopologyCost (K := K).segmentKindsPerFamily = 4 ∧
      productionTopologyCost (K := K).acceptanceEvaluations = 32 := by
  have hio := finalSegmentedCost_localWidths (K := K)
  have hsum := finalSegmentedCost_constraintTotal (K := K)
  simp only [productionTopologyCost, sixFamilyCost, hio, hsum,
    topologyComponentCost, computeTopoAIR, memoryTopoAIR]
  decide

/-- The same delta in difference form: `+86/+34` columns (`+120` aggregate), `+49`
constraints, `+2` families, and `+8` kind-segmented evaluations. -/
theorem production_cost_difference_form :
    productionTopologyCost (K := K).computeWidthWithTopology -
        productionTopologyCost (K := K).sixFamily.computeDisjointWidth = 86 ∧
      productionTopologyCost (K := K).memoryWidthWithTopology -
        productionTopologyCost (K := K).sixFamily.memoryDisjointWidth = 34 ∧
      (productionTopologyCost (K := K).computeWidthWithTopology +
          productionTopologyCost (K := K).memoryWidthWithTopology) -
        (productionTopologyCost (K := K).sixFamily.computeDisjointWidth +
          productionTopologyCost (K := K).sixFamily.memoryDisjointWidth) = 120 ∧
      productionTopologyCost (K := K).totalConstraints -
        productionTopologyCost (K := K).sixFamilyConstraints = 49 ∧
      productionTopologyCost (K := K).familyCount - 6 = 2 ∧
      productionTopologyCost (K := K).acceptanceEvaluations - 24 = 8 := by
  have hio := finalSegmentedCost_localWidths (K := K)
  have hsum := finalSegmentedCost_constraintTotal (K := K)
  simp only [productionTopologyCost, sixFamilyCost, hio, hsum,
    topologyComponentCost, computeTopoAIR, memoryTopoAIR]
  decide

/-- The old verifier had six families and therefore 24 kind-segmented evaluations; production has
eight families and 32.  The exact acceptance-evaluation delta is eight. -/
theorem production_acceptance_evaluation_delta :
    6 * 4 = 24 ∧ 8 * 4 = 32 ∧ 32 - 24 = 8 := by
  simp only [productionTopologyCost, sixFamilyCost, finalSegmentedCost,
    topologyComponentCost, computeTopoAIR, memoryTopoAIR]
  decide

/-- The cost census is tied to the production verifier's own eight-family count, not merely to an
unrelated arithmetic literal. -/
theorem production_acceptance_evaluations_certified :
    productionTopologyCost (K := K).acceptanceEvaluations = 32 ∧
      8 * 4 = 32 := by
  exact ⟨by
    simp only [productionTopologyCost],
    ProductionRawVerifier.Message.segmented_evaluation_count⟩

/-- Dependent certificate joining the unchanged exact six-family certificate to the two
verifier-generated topology families.  `ofLegacy S` is the data-only production family consumed
by `ProductionRawVerifier`. -/
structure ProductionTopologyCostCertificate
    (S : PlusIOSegmentedFamily F K) (c : ReifiedProductionCost) : Prop where
  six_family : ExactCostCertificate S c.sixFamily
  compute_topology :
    c.computeTopology = topologyComponentCost computeTopoAIR
  memory_topology :
    c.memoryTopology = topologyComponentCost memoryTopoAIR
  compute_width : ∀ kind,
    c.computeTopology.localWidth =
      (computeTopologyGenericRAP (RawPlusIOSegmentedFamily.ofLegacy S) kind).w
  memory_width : ∀ kind,
    c.memoryTopology.localWidth =
      (memoryTopologyGenericRAP (RawPlusIOSegmentedFamily.ofLegacy S) kind).w
  compute_domain : ∀ kind,
    (computeTopologyGenericRAP (RawPlusIOSegmentedFamily.ofLegacy S) kind).H =
      S.problem.cfg.computeDomain kind
  memory_domain : ∀ kind,
    (memoryTopologyGenericRAP (RawPlusIOSegmentedFamily.ofLegacy S) kind).H =
      S.problem.cfg.memoryDomain kind
  total_widths :
    c.computeWidthWithTopology =
        c.sixFamily.computeDisjointWidth + c.computeTopology.localWidth ∧
      c.memoryWidthWithTopology =
        c.sixFamily.memoryDisjointWidth + c.memoryTopology.localWidth
  constraint_total :
    c.totalConstraints = c.sixFamilyConstraints + c.topologyConstraints
  evaluation_total :
    c.acceptanceEvaluations = c.familyCount * c.segmentKindsPerFamily

/-- The literal production record has the full dependent certificate. -/
theorem productionTopologyCost_certificate (S : PlusIOSegmentedFamily F K) :
    ProductionTopologyCostCertificate S (productionTopologyCost (K := K)) := by
  refine
    { six_family := finalSegmentedCost_certificate S
      compute_topology := rfl
      memory_topology := rfl
      compute_width := ?_
      memory_width := ?_
      compute_domain := ?_
      memory_domain := ?_
      total_widths := ⟨rfl, rfl⟩
      constraint_total := by simp only [productionTopologyCost]; omega
      evaluation_total := by simp only [productionTopologyCost] }
  · intro kind
    rfl
  · intro kind
    rfl
  · intro kind
    rfl
  · intro kind
    rfl

/-- The aggregate disjoint production
accounting is neither the old `102/44` six-family accounting nor numerically equal to the paper's
strict `199/196` monolithic object.  This comparison does not identify the layouts.  In particular
topology is not assigned zero cost. -/
theorem production_cost_discrimination :
    productionTopologyCost (K := K).computeWidthWithTopology ≠
        sixFamilyCost (K := K).computeDisjointWidth ∧
      productionTopologyCost (K := K).memoryWidthWithTopology ≠
        sixFamilyCost (K := K).memoryDisjointWidth ∧
      productionTopologyCost (K := K).computeWidthWithTopology ≠ 199 ∧
      productionTopologyCost (K := K).memoryWidthWithTopology ≠ 196 ∧
      productionTopologyCost (K := K).computeTopology.localWidth ≠ 0 ∧
      productionTopologyCost (K := K).memoryTopology.localWidth ≠ 0 := by
  simp only [productionTopologyCost, sixFamilyCost, finalSegmentedCost,
    topologyComponentCost, computeTopoAIR, memoryTopoAIR]
  decide

theorem production_cost_ne_paper_strict :
    productionTopologyCost (K := K).computeWidthWithTopology ≠
        Nock.NockVMROM.paperParamCost.compIOCols.eval 3 ∧
      productionTopologyCost (K := K).memoryWidthWithTopology ≠
        Nock.NockVMROM.paperParamCost.memIOCols.eval 3 := by
  rw [Nock.NockVMROM.paperParamCost_IO_thm54.1,
    Nock.NockVMROM.paperParamCost_IO_thm54.2.1]
  exact ⟨production_cost_discrimination.2.2.1,
    production_cost_discrimination.2.2.2.1⟩

/-! ## Honest deterministic verifier work -/

/-- Fixed maximum fanouts inspected by the production topology verifier. -/
def topologyComputeFanout : ℕ := 3
def topologyMemoryFanout : ℕ := 2

/-- One unit per parent/slot authoritative lookup. -/
def topologyVerifierSlotInspections
    (R : RawPlusIOSegmentedFamily F K) : ℕ :=
  R.cfg.compRows * topologyComputeFanout +
    R.cfg.memRows * topologyMemoryFanout

/-- Natural deterministic work proxy: every generated topology field cell plus every authoritative
parent/slot lookup.  This deliberately does not model constant-query succinct verification. -/
def topologyVerifierNaturalOperations
    (R : RawPlusIOSegmentedFamily F K) : ℕ :=
  topologyVerifierGeneratedFieldCells R + topologyVerifierSlotInspections R

/-- Exact operation expansion and a concrete linear upper bound.  Thus, for the fixed topology
schemas, construction/inspection is `O(compRows*fanoutComp + memRows*fanoutMem)`, with constant
`30`; it is not constant-query work. -/
theorem topology_verifier_natural_operation_bound
    (R : RawPlusIOSegmentedFamily F K) :
    topologyVerifierNaturalOperations R =
        (R.cfg.compRows * 86 + R.cfg.memRows * 34) +
          (R.cfg.compRows * 3 + R.cfg.memRows * 2) ∧
      topologyVerifierNaturalOperations R ≤
        30 * (R.cfg.compRows * topologyComputeFanout +
          R.cfg.memRows * topologyMemoryFanout) := by
  constructor
  · rfl
  · simp only [topologyVerifierNaturalOperations, topologyVerifierGeneratedFieldCells,
      topologyVerifierSlotInspections, topologyComputeFanout, topologyMemoryFanout,
      RawTopologyAIR.computeTraceWidth, RawTopologyAIR.memoryTraceWidth]
    omega

/-! ## Bad-event workload -/

/-- Exact topology `gamma` workload, normalized to one coefficient per parent row. -/
theorem topology_gamma_workload_exact
    (R : RawPlusIOSegmentedFamily F K) :
    topologyWorkload R = 24 * R.cfg.compRows + 8 * R.cfg.memRows := by
  simp [topologyWorkload]
  omega

/-- Recounting rule for the topology-enabled architecture.  Regenerated compute- and memory-walk
events contribute zero; only the separately counted topology `gamma` event contributes here. -/
def productionTopologyBadEventWorkload
    (R : RawPlusIOSegmentedFamily F K) : ℕ :=
  topologyWorkload R + 0 + 0

theorem production_topology_bad_event_workload_exact
    (R : RawPlusIOSegmentedFamily F K) :
    productionTopologyBadEventWorkload R =
      24 * R.cfg.compRows + 8 * R.cfg.memRows := by
  rw [productionTopologyBadEventWorkload, add_zero, add_zero,
    topology_gamma_workload_exact]

/-- The concrete regenerated compute event is empty, so it must not be added a second time. -/
theorem regenerated_compute_walk_event_zero
    [Fintype K] [DecidableEq K]
    (T : TemplateRawJointSoundness.Strategy F K p) (lmb : K) :
    (TemplateRawJointSoundness.specializedComputeWalkFailureEvent T lmb).card = 0 :=
  TemplateRawJointSoundness.specializedComputeWalkFailureEvent_card_eq_zero T lmb

/-- The concrete regenerated memory event has zero cardinality once topology collisions remain in
their own event, so it also must not be added a second time. -/
theorem regenerated_memory_walk_event_zero
    [Fintype K] [DecidableEq K]
    (T : TemplateRawJointSoundness.Strategy F K p) (lmb : K)
    (hchar : NodeEncoding.StateTagChar K)
    (hlam : ∀ z (hz : z ≠ 0) alphaM i,
      ((TemplateRawJointSoundness.specializedProblem T.timestamp z hz alphaM lmb).exec.memoryPubAt i).lambda = (TemplateRawJointSoundness.specializedProblem T.timestamp z hz alphaM lmb).cfg.challenges.lam) :
    (TemplateMemoryWalkCounting.countingData T lmb hchar hlam).failureEvent.card = 0 := by
  have h := TemplateMemoryWalkCounting.countingFailureEvent_card_le T lmb hchar hlam
  simpa using h

end
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.topology_air_exact_census
#print axioms Nock.NockVMROM.Thm54.topology_degree_histograms
#print axioms Nock.NockVMROM.Thm54.topology_constraints_by_kind
#print axioms Nock.NockVMROM.Thm54.topology_max_degree_by_kind
#print axioms Nock.NockVMROM.Thm54.topology_segment_domains
#print axioms Nock.NockVMROM.Thm54.production_cost_exact_delta
#print axioms Nock.NockVMROM.Thm54.production_cost_difference_form
#print axioms Nock.NockVMROM.Thm54.production_acceptance_evaluations_certified
#print axioms Nock.NockVMROM.Thm54.productionTopologyCost_certificate
#print axioms Nock.NockVMROM.Thm54.production_cost_discrimination
#print axioms Nock.NockVMROM.Thm54.production_cost_ne_paper_strict
#print axioms Nock.NockVMROM.Thm54.topology_verifier_natural_operation_bound
#print axioms Nock.NockVMROM.Thm54.topology_gamma_workload_exact
#print axioms Nock.NockVMROM.Thm54.production_topology_bad_event_workload_exact
#print axioms Nock.NockVMROM.Thm54.regenerated_compute_walk_event_zero
#print axioms Nock.NockVMROM.Thm54.regenerated_memory_walk_event_zero
