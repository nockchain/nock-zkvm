import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.ProductionTopologyCost

/-!
# Complete cost certificate for final production acceptance

`productionTopologyCost` is the exact census of the eight segmented AIR families.  It is not the
cost of the whole final predicate: `ProductionStrategy.Accepts` additionally reconstructs the two
IO traces, evaluates the raw verifier gates, runs the deterministic axis-structure checker, and
checks one template-axis polynomial boundary per memory root.

This module keeps those categories disjoint.  The topology and axis-structure work use the
existing mechanically proved linear formulas.  The exact number of verifier-reconstructed IO rows
is the sum of the request and response `records + 1` domains, but there is no field-operation
semantics for constructing one such row.  The number of root-polynomial evaluations is exactly
`kMem`.  No constant is invented for
any of those categories.

In particular, `676` and `32` below mean only AIR constraints and kind-segmented RAP evaluations.
They are never asserted to be the total number of checks performed by final acceptance.
-/

namespace Nock.NockVMROM.Thm54.CompleteProductionCost

open scoped Classical
open Nock Framework Framework.Reify Framework.Thm54
open Nock.Reified
open ProductionP8Containment
open ProductionAxisStructureVerifier
open TemplateAxisCounting
open SemanticTimestampStrategy
open Nock.AxisBatching.MTree

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable [charRing : CharP K (ringChar K)]

abbrev FinalProductionStrategy :=
  ProductionP8Containment.ProductionStrategy F K

/-! ## Exact final-acceptance expansion -/

/-- The eight AIR-backed families at one accepted seed specialization. -/
def EightSegmentedChecksAt
    (T : FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) : Prop :=
  (T.verifier.messageAt ω lmb hz).EightRAPSatisfy

/-- Raw deterministic gates, including phase/seed bindings, row alignment, canonical encoder
bindings, the three public-claim bindings, and the IO side conditions.  These are outside
`EightRAPSatisfy`; no AIR-column count is assigned to them here. -/
def LegacyAndPublicGateChecksAt
    (T : FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) : Prop :=
  (T.verifier.messageAt ω lmb hz).raw.VerifierGates T.verifier.raw.claim ω

def AxisStructureChecksAt
    (T : FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) : Prop :=
  structuralChecksAt T.verifier (nprSeed ω) hz (alphaM ω) = true

/-- Every final non-AIR acceptance condition, kept separate from the eight segmented families. -/
def NonAIRAcceptanceChecksAt
    (T : FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) : Prop :=
  LegacyAndPublicGateChecksAt T ω lmb hz ∧
    AxisStructureChecksAt T ω lmb hz ∧
    T.RootAxisBoundaryAt (nprSeed ω) hz (alphaM ω)

/-- The exact nonzero-seed expansion of final production acceptance. -/
def CompleteProductionAcceptanceExpansion
    (T : FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) : Prop :=
  LegacyAndPublicGateChecksAt T ω lmb hz ∧
    EightSegmentedChecksAt T ω lmb hz ∧
    AxisStructureChecksAt T ω lmb hz ∧
    T.RootAxisBoundaryAt (nprSeed ω) hz (alphaM ω)

/-- Direct connection to the definition of the final, proof-carrying production strategy's
acceptance predicate. -/
theorem final_accepts_iff_complete_expansion
    (T : FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    T.Accepts ω lmb ↔ CompleteProductionAcceptanceExpansion T ω lmb hz := by
  rw [ProductionP8Containment.ProductionStrategy.accepts_iff T ω lmb hz]
  rw [ProductionAxisStructureVerifier.accepts_iff T.verifier ω lmb hz]
  simp only [ProductionRawVerifier.Message.VerifierChecks,
    CompleteProductionAcceptanceExpansion, LegacyAndPublicGateChecksAt,
    EightSegmentedChecksAt, AxisStructureChecksAt]
  tauto

/-- Equivalent accounting split: exactly eight AIR families, plus every non-AIR acceptance check. -/
theorem final_accepts_iff_segmented_and_nonAIR
    (T : FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    T.Accepts ω lmb ↔
      EightSegmentedChecksAt T ω lmb hz ∧ NonAIRAcceptanceChecksAt T ω lmb hz := by
  rw [final_accepts_iff_complete_expansion T ω lmb hz]
  simp only [CompleteProductionAcceptanceExpansion, NonAIRAcceptanceChecksAt]
  tauto

/-- Each
quantifier ranges over the four constructors of `ConstraintKind`. -/
theorem eightSegmentedChecksAt_iff_eight_families
    (T : FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    EightSegmentedChecksAt T ω lmb hz ↔
      (∀ kind, ((T.verifier.familyAt ω lmb hz).computeTableRAP kind).Satisfies
        (T.verifier.messageAt ω lmb hz).raw.computeTableTrace) ∧
      (∀ kind, ((T.verifier.familyAt ω lmb hz).memoryTableRAP kind).Satisfies
        (T.verifier.messageAt ω lmb hz).raw.memoryTableTrace) ∧
      (∀ kind, ((T.verifier.familyAt ω lmb hz).computeWalkRAP kind).Satisfies
        (T.verifier.messageAt ω lmb hz).raw.computeWalkTrace) ∧
      (∀ kind, ((T.verifier.familyAt ω lmb hz).memoryWalkRAP kind).Satisfies
        (T.verifier.messageAt ω lmb hz).raw.memoryWalkTrace) ∧
      (∀ kind, ((T.verifier.familyAt ω lmb hz).computeIORAP kind).Satisfies
        (T.verifier.messageAt ω lmb hz).raw.computeIOTrace) ∧
      (∀ kind, ((T.verifier.familyAt ω lmb hz).memoryIORAP kind).Satisfies
        (T.verifier.messageAt ω lmb hz).raw.memoryIOTrace) ∧
      (∀ kind, (computeTopologyGenericRAP
          (T.verifier.familyAt ω lmb hz) kind).Satisfies
        (computeTopologyTrace (T.verifier.familyAt ω lmb hz)
          (T.verifier.messageAt ω lmb hz).topology.compute)) ∧
      (∀ kind, (memoryTopologyGenericRAP
          (T.verifier.familyAt ω lmb hz) kind).Satisfies
        (memoryTopologyTrace (T.verifier.familyAt ω lmb hz)
          (T.verifier.messageAt ω lmb hz).topology.memory)) := by
  simp only [EightSegmentedChecksAt,
    ProductionRawVerifier.Message.EightRAPSatisfy,
    RawMessage.SixRAPSatisfy,
    ProductionRawVerifier.Message.VerifierGeneratedSegmentedTopologyChecks]
  tauto

/-! ## Cost data with explicit residual budgets -/

/-- Exact number of rows reconstructed by the verifier for the request and response IO traces.
Each trace contains one initial accumulator row in addition to its derived records. -/
def verifierReconstructedIOTraceRowCount
    (T : FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) : ℕ :=
  let R := T.verifier.familyAt ω lmb hz
  (R.exec.derivedRequestIO.length + 1) +
    (R.exec.derivedResponseIO.length + 1)

omit [Fintype K] [DecidableEq K] in
/-- Definitional receipt spelling the exact two verifier-reconstructed IO row domains. -/
theorem verifierReconstructedIOTraceRowCount_exact
    (T : FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    verifierReconstructedIOTraceRowCount T ω lmb hz =
      ((T.verifier.familyAt ω lmb hz).exec.derivedRequestIO.length + 1) +
        ((T.verifier.familyAt ω lmb hz).exec.derivedResponseIO.length + 1) := by
  rfl

/-- Exactly one `Polynomial.eval` boundary obligation is checked for each committed memory root. -/
def rootAxisBoundaryEvaluationCount
    (T : FinalProductionStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) : ℕ :=
  (T.verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate.kMem

/-- Definitional spelling of all root-polynomial evaluations counted above. -/
theorem rootAxisBoundaryAt_iff_all_root_evaluations
    (T : FinalProductionStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) (α : K) :
    T.RootAxisBoundaryAt z hz α ↔
      ∀ i : Fin (rootAxisBoundaryEvaluationCount T z hz),
        (countsP_bin
          (templateAxisTree
            (templateMemoryTreeAt (committedTemplate T.verifier z hz) i))).eval α = 0 := by
  rfl

/-- Mechanically exact cardinality of the finite root-evaluation domain. -/
theorem rootAxisBoundaryEvaluationCount_exact
    (T : FinalProductionStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) :
    Fintype.card (Fin (rootAxisBoundaryEvaluationCount T z hz)) =
      rootAxisBoundaryEvaluationCount T z hz := by
  simp

/-- Existing proved topology linear-operation upper bound, exposed as data. -/
def topologyLinearOperationBound
    (R : RawPlusIOSegmentedFamily F K) : ℕ :=
  30 * (R.cfg.compRows * topologyComputeFanout +
    R.cfg.memRows * topologyMemoryFanout)

/-- Existing proved axis-structure linear-operation upper bound, exposed as data. -/
def axisStructureLinearOperationBound
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) : ℕ :=
  2 * (T.memRows + totalTemplateReadVerifyOccurrences E)

/-- Complete accounting record.  Topology and axis work have exact/linear formulas.
`verifierReconstructedIORows` is an exact row count, but
`ioTraceConstructionOperationBound` is caller-supplied because there is no per-row
field-operation semantics.  `rootAxisPolynomialOperationBound` explicitly budgets polynomial
evaluation, while `legacyPublicGateOperationBound` explicitly budgets heterogeneous raw/public
gates, including `Nodup` and `Ksz` scans. -/
structure CompleteProductionCostData where
  segmentedAIR : ReifiedProductionCost
  topologyNaturalOperations : ℕ
  topologyOperationBound : ℕ
  axisStructureNaturalOperations : ℕ
  axisStructureOperationBound : ℕ
  verifierReconstructedIORows : ℕ
  ioTraceConstructionOperationBound : ℕ
  rootAxisPolynomialEvaluations : ℕ
  rootAxisPolynomialOperationBound : ℕ
  legacyPublicGateOperationBound : ℕ
  completeDeterministicOperationBound : ℕ
deriving DecidableEq, Repr

/-- Cost data at one nonzero-seed specialization.  The three unknown operation bounds remain
visible parameters and are included in the complete deterministic upper bound.  Argument order is
the stable `(rootBound, gateBound, ioBound)` order. -/
def completeProductionCostAt
    (T : FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (rootAxisPolynomialOperationBound legacyPublicGateOperationBound
      ioTraceConstructionOperationBound : ℕ) :
    CompleteProductionCostData :=
  let R := T.verifier.familyAt ω lmb hz
  let E := committedTemplate T.verifier (nprSeed ω) hz
  { segmentedAIR := productionTopologyCost (K := K)
    topologyNaturalOperations := topologyVerifierNaturalOperations R
    topologyOperationBound := topologyLinearOperationBound R
    axisStructureNaturalOperations := axisStructureVerifierNaturalOperations E
    axisStructureOperationBound := axisStructureLinearOperationBound E
    verifierReconstructedIORows :=
      verifierReconstructedIOTraceRowCount T ω lmb hz
    ioTraceConstructionOperationBound := ioTraceConstructionOperationBound
    rootAxisPolynomialEvaluations :=
      rootAxisBoundaryEvaluationCount T (nprSeed ω) hz
    rootAxisPolynomialOperationBound := rootAxisPolynomialOperationBound
    legacyPublicGateOperationBound := legacyPublicGateOperationBound
    completeDeterministicOperationBound :=
      topologyLinearOperationBound R +
        axisStructureLinearOperationBound E +
        rootAxisPolynomialOperationBound +
        legacyPublicGateOperationBound +
        ioTraceConstructionOperationBound }

/-- The final certificate simultaneously identifies acceptance and certifies each exact or bounded
cost category.  The hypotheses needed to interpret the three explicit residual budgets are supplied
only when deriving an end-to-end operation inequality below. -/
structure CompleteProductionCostCertificate
    (T : FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (rootBound gateBound ioBound : ℕ) (c : CompleteProductionCostData) : Prop where
  acceptance :
    T.Accepts ω lmb ↔ CompleteProductionAcceptanceExpansion T ω lmb hz
  segmented_air :
    c.segmentedAIR = productionTopologyCost (K := K)
  topology_exact :
    c.topologyNaturalOperations =
      topologyVerifierNaturalOperations (T.verifier.familyAt ω lmb hz)
  topology_formula :
    c.topologyNaturalOperations =
      ((T.verifier.familyAt ω lmb hz).cfg.compRows * 86 +
          (T.verifier.familyAt ω lmb hz).cfg.memRows * 34) +
        ((T.verifier.familyAt ω lmb hz).cfg.compRows * 3 +
          (T.verifier.familyAt ω lmb hz).cfg.memRows * 2)
  topology_bounded :
    c.topologyNaturalOperations ≤ c.topologyOperationBound
  axis_structure_exact :
    c.axisStructureNaturalOperations =
      axisStructureVerifierNaturalOperations
        (committedTemplate T.verifier (nprSeed ω) hz)
  axis_structure_formula :
    c.axisStructureNaturalOperations =
      (T.verifier.raw.timestamp.afterSeed
          ⟨nprSeed ω, hz⟩).configTemplate.memRows +
        totalTemplateReadVerifyOccurrences
          (committedTemplate T.verifier (nprSeed ω) hz)
  axis_structure_bounded :
    c.axisStructureNaturalOperations ≤ c.axisStructureOperationBound
  io_rows_exact :
    c.verifierReconstructedIORows =
      verifierReconstructedIOTraceRowCount T ω lmb hz
  io_rows_formula :
    c.verifierReconstructedIORows =
      ((T.verifier.familyAt ω lmb hz).exec.derivedRequestIO.length + 1) +
        ((T.verifier.familyAt ω lmb hz).exec.derivedResponseIO.length + 1)
  io_budget_explicit :
    c.ioTraceConstructionOperationBound = ioBound
  root_evaluations_exact :
    c.rootAxisPolynomialEvaluations =
      rootAxisBoundaryEvaluationCount T (nprSeed ω) hz
  root_budget_explicit :
    c.rootAxisPolynomialOperationBound = rootBound
  gate_budget_explicit :
    c.legacyPublicGateOperationBound = gateBound
  complete_bound_exact :
    c.completeDeterministicOperationBound =
      c.topologyOperationBound + c.axisStructureOperationBound +
        rootBound + gateBound + ioBound

/-- The literal complete record has the complete certificate for every explicit triple of residual
budgets. -/
theorem completeProductionCost_certificate
    (T : FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (rootBound gateBound ioBound : ℕ) :
    CompleteProductionCostCertificate T ω lmb hz rootBound gateBound ioBound
      (completeProductionCostAt T ω lmb hz rootBound gateBound ioBound) := by
  refine
    { acceptance := final_accepts_iff_complete_expansion T ω lmb hz
      segmented_air := rfl
      topology_exact := rfl
      topology_formula := (topology_verifier_natural_operation_bound
        (T.verifier.familyAt ω lmb hz)).1
      topology_bounded := ?_
      axis_structure_exact := rfl
      axis_structure_formula := (axis_structure_verifier_natural_operation_bound
        (committedTemplate T.verifier (nprSeed ω) hz)).1
      axis_structure_bounded := ?_
      io_rows_exact := rfl
      io_rows_formula := verifierReconstructedIOTraceRowCount_exact T ω lmb hz
      io_budget_explicit := rfl
      root_evaluations_exact := rfl
      root_budget_explicit := rfl
      gate_budget_explicit := rfl
      complete_bound_exact := by
        simp [completeProductionCostAt] }
  · exact (topology_verifier_natural_operation_bound
      (T.verifier.familyAt ω lmb hz)).2
  · exact (axis_structure_verifier_natural_operation_bound
      (committedTemplate T.verifier (nprSeed ω) hz)).2

/-- AIR-only exact quantities.  The theorem name and statement deliberately do not call `676` or
`32` the cost of final acceptance. -/
theorem completeProductionCost_segmentedAIR_exact
    (T : FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (rootBound gateBound ioBound : ℕ) :
    let c := completeProductionCostAt T ω lmb hz rootBound gateBound ioBound
    c.segmentedAIR.computeWidthWithTopology = 188 ∧
      c.segmentedAIR.memoryWidthWithTopology = 79 ∧
      c.segmentedAIR.sixFamilyConstraints = 627 ∧
      c.segmentedAIR.topologyConstraints = 49 ∧
      c.segmentedAIR.totalConstraints = 676 ∧
      c.segmentedAIR.familyCount = 8 ∧
      c.segmentedAIR.segmentKindsPerFamily = 4 ∧
      c.segmentedAIR.acceptanceEvaluations = 32 := by
  simpa [completeProductionCostAt] using
    production_cost_exact_delta (K := K).2.2.2.2

/-- Conditional end-to-end operation bound.  The exact topology and axis costs are proved below
their existing linear formulas.  IO trace construction, polynomial evaluation, and heterogeneous
raw/public gate work must each be bounded by its own explicit parameter. -/
theorem completeProductionCost_deterministic_operations_le
    (T : FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (rootBound gateBound ioBound rootActual gateActual ioActual : ℕ)
    (hroot : rootActual ≤ rootBound)
    (hgate : gateActual ≤ gateBound)
    (hio : ioActual ≤ ioBound) :
    let c := completeProductionCostAt T ω lmb hz rootBound gateBound ioBound
    c.topologyNaturalOperations + c.axisStructureNaturalOperations +
        rootActual + gateActual + ioActual ≤
      c.completeDeterministicOperationBound := by
  dsimp [completeProductionCostAt]
  have htop := (topology_verifier_natural_operation_bound
    (T.verifier.familyAt ω lmb hz)).2
  have haxis := (axis_structure_verifier_natural_operation_bound
    (committedTemplate T.verifier (nprSeed ω) hz)).2
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add htop haxis) hroot) hgate) hio

/-! ## Strict-paper regression -/

/-- Minimal numerical fingerprint sufficient to prevent confusing this segmented, deterministic
production checker with the paper's strict `199/196`, `e = 3` G10 package. -/
def completeProductionAIRFingerprint (c : CompleteProductionCostData) :
    ℕ × ℕ × ℕ :=
  (c.segmentedAIR.computeWidthWithTopology,
    c.segmentedAIR.memoryWidthWithTopology,
    c.segmentedAIR.sixFamily.eDeg)

def strictPaperG10Fingerprint : ℕ × ℕ × ℕ :=
  (Nock.NockVMROM.paperParamCost.compIOCols.eval 3,
    Nock.NockVMROM.paperParamCost.memIOCols.eval 3, 3)

/-- Regression: completing the deterministic cost accounting does not turn the production object
into the strict-paper package. -/
theorem completeProductionCost_ne_strictPaperG10
    (T : FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (rootBound gateBound ioBound : ℕ) :
    completeProductionAIRFingerprint
        (completeProductionCostAt T ω lmb hz rootBound gateBound ioBound) ≠
      strictPaperG10Fingerprint := by
  intro h
  have hw := congrArg Prod.fst h
  exact production_cost_ne_paper_strict (K := K).1 (by
    simpa [completeProductionAIRFingerprint, completeProductionCostAt,
      strictPaperG10Fingerprint] using hw)

end

end Nock.NockVMROM.Thm54.CompleteProductionCost

#print axioms Nock.NockVMROM.Thm54.CompleteProductionCost.final_accepts_iff_complete_expansion
#print axioms Nock.NockVMROM.Thm54.CompleteProductionCost.final_accepts_iff_segmented_and_nonAIR
#print axioms Nock.NockVMROM.Thm54.CompleteProductionCost.eightSegmentedChecksAt_iff_eight_families
#print axioms Nock.NockVMROM.Thm54.CompleteProductionCost.verifierReconstructedIOTraceRowCount_exact
#print axioms Nock.NockVMROM.Thm54.CompleteProductionCost.rootAxisBoundaryAt_iff_all_root_evaluations
#print axioms Nock.NockVMROM.Thm54.CompleteProductionCost.completeProductionCost_certificate
#print axioms Nock.NockVMROM.Thm54.CompleteProductionCost.completeProductionCost_segmentedAIR_exact
#print axioms Nock.NockVMROM.Thm54.CompleteProductionCost.completeProductionCost_deterministic_operations_le
#print axioms Nock.NockVMROM.Thm54.CompleteProductionCost.completeProductionCost_ne_strictPaperG10
