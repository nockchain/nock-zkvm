import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.HardenedTopologyAIR
import Nock.NockVMROM.Thm54.RawSemanticAssembly

/-!
# Correctness and exact residual boundary for the buildable topology

This module keeps output correctness separate from `BuildableTopology` and
`BuildableChips.Inputs`.  It derives the verifier-generated topology AIR, child-array binding,
exact traversal shape, and hardened state-selector facts from the canonical output.

The same module records the exact Milestone-4 stop boundary on the consumed exact memory trees.
`BuildableNockExecution` contains the paper's accepted `Vmem` rows, noun realization, aggregate
forest walk, and global semantic IO relation, but it does not contain the per-root ancestry /
partition check or the identically-zero per-root `axis_counts` polynomial.  The final theorems
below state, on `exactAxisTree E.cfg E.exec root` itself, why those facts are required before the
primitive `MemoryChipAssignment` can be upgraded to `MemoryProductionAssignment`.
-/

namespace Nock.NockVMROM.Thm54
namespace BuildableTopologyCorrectness

open scoped Classical Polynomial
open Nock Nock.Walk Nock.Framework Nock.Reified
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open RawSemanticAssembly
open HardenedTopologyAIR
open BuildableChips
open OptimizedComputeFinalTrace
open OptimizedMemorySameExecution
open TemplateAxisCounting

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## Canonical topology data and verifier-generated AIR -/

/-- The topology arrays in the universal builder are exactly the authoritative BFS child
payloads.  No topology proposition is stored in either input record. -/
theorem builtArrays_eq_honest
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (buildTopology E I).topologyArrays =
      honestTopologyArrays (buildTopology E I).rawFamily := by
  rfl

/-- The raw topology binding residual is a theorem of the exact arity-3/2 traversals, rather than
an input to the builder. -/
theorem rawTopologyBinding
    (E : BuildableNockExecution F K) (I : Inputs E) :
    RawTopologyBindingResidual (buildTopology E I).rawFamily := by
  constructor
  · simpa [BuildableTopology.rawFamily, BuildableRawFamily.toRawPlusIOSegmentedFamily,
      RawPlusIOSegmentedFamily.computeWalkRows] using
      (computeBinding_of_exactTopology E.traversal.1)
  · simpa [BuildableTopology.rawFamily, BuildableRawFamily.toRawPlusIOSegmentedFamily,
      RawPlusIOSegmentedFamily.memoryWalkRows] using
      (memoryBinding_of_exactTopology E.traversal.2)

/-- The canonical child arrays satisfy both verifier-generated topology RAPs.  This uses the
actual topology traces exported by `buildTopology`, never an arbitrary all-zero trace. -/
theorem verifierGeneratedTopologySatisfies
    (E : BuildableNockExecution F K) (I : Inputs E) :
    VerifierGeneratedTopologyRAPSatisfyOfCommittedArrays
      (buildTopology E I).rawFamily (buildTopology E I).topologyArrays := by
  rw [builtArrays_eq_honest]
  exact honestVerifierGeneratedTopologyRAP_complete
    (buildTopology E I).rawFamily E.traversal

/-- Exact row-level fanout, deterministic lookup, and active child-RLC obligations of the two
topology AIRs. -/
theorem topologyFieldChecks
    (E : BuildableNockExecution F K) (I : Inputs E) :
    ComputeTopologyFieldChecks (buildTopology E I).rawFamily
        (buildTopology E I).topologyArrays.compute ∧
      MemoryTopologyFieldChecks (buildTopology E I).rawFamily
        (buildTopology E I).topologyArrays.memory :=
  (verifierGeneratedTopologyRAP_iff_fieldChecksOfCommittedArrays
    (buildTopology E I).rawFamily (buildTopology E I).topologyArrays).1
      (verifierGeneratedTopologySatisfies E I)

/-- The verifier-generated AIR therefore yields the production compressed topology check, with
the bounded state-tag interpretation supplied by the backend input. -/
theorem topologyCompressed
    (E : BuildableNockExecution F K) (I : Inputs E) :
    TopologyCompressedCheck (buildTopology E I).rawFamily
      (buildTopology E I).rawFamily.walkGamma :=
  topologyCompressedCheck_of_verifierGeneratedRAPOfCommittedArrays
    I.stateTagChar (buildTopology E I).rawFamily
    (buildTopology E I).topologyArrays
    (verifierGeneratedTopologySatisfies E I)

/-! ## Hardened state selectors -/

/-- A verifier-generated one-hot selector row whose selected state is an actual finite index. -/
def selectorEnv (n : ℕ) (selected : Fin n) : Env K where
  trace j := if j = selected then 1 else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

omit [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
private theorem selector_sum (n : ℕ) (selected : Fin n) :
    ((List.range n).map fun j =>
      (selectorEnv (K := K) n selected).trace j).sum = 1 := by
  simp only [selectorEnv]
  calc
    ((List.range n).map fun j => if j = (selected : ℕ) then (1 : K) else 0).sum =
        ∑ j : Fin n, if (j : ℕ) = (selected : ℕ) then (1 : K) else 0 := by
      symm
      exact Fin.sum_univ_eq_sum_range
        (fun j => if j = (selected : ℕ) then (1 : K) else 0) n
    _ = 1 := by
      have hset :
          ({j : Fin n | (j : ℕ) = (selected : ℕ)} : Finset (Fin n)) = {selected} := by
        ext j
        simp [Fin.ext_iff]
      simp [hset]

/- Every verifier-generated one-hot row satisfies booleanity and the paper's sum-to-one
hardening. -/
omit [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
theorem selectorEnv_satisfies
    (n : ℕ) (selected : Fin n) :
    RowSat (hardenedSelectorAIR n) (selectorEnv (K := K) n selected) := by
  intro c hc
  simp only [hardenedSelectorAIR, hardenedSelectorConstraints, List.mem_append,
    List.mem_map, List.mem_singleton] at hc
  rcases hc with ⟨j, _hj, rfl⟩ | rfl
  · by_cases h : j = selected
    · simp [selectorBoolExpr, stVar, selectorEnv, h, Expr.eval]
    · simp [selectorBoolExpr, stVar, selectorEnv, h, Expr.eval]
  · simp [sumToOneExpr, sumSelectorsExpr_eval, selector_sum, Expr.eval]

/-- Hardened compute selectors are generated from the actual committed row state. -/
theorem computeSelectorsHardened
    (E : BuildableNockExecution F K) (I : Inputs E) :
    ∀ i : Fin E.cfg.compRows,
      RowSat (hardenedSelectorAIR 11)
        (selectorEnv (K := K) 11
          (OptimizedComputeCodec.stateIndex
            (computeTopologyNodeAt (buildTopology E I).rawFamily i).label.1)) := by
  intro i
  exact selectorEnv_satisfies 11 _

/-- Hardened memory selectors are generated from the actual committed row state. -/
theorem memorySelectorsHardened
    (E : BuildableNockExecution F K) (I : Inputs E) :
    ∀ i : Fin E.cfg.memRows,
      RowSat (hardenedSelectorAIR 4)
        (selectorEnv (K := K) 4
          (OptimizedMemoryCodec.stateIndex
            (memoryTopologyNodeAt (buildTopology E I).rawFamily i).label.1)) := by
  intro i
  exact selectorEnv_satisfies 4 _

/- The quarantined all-zero selector assignment is rejected on both nonempty selector sets. -/
omit [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
theorem allZeroTopologySelectorsRejected :
    (∀ env : Env K, (∀ j, env.trace j = 0) →
      ¬ RowSat (hardenedSelectorAIR 11) env) ∧
    (∀ env : Env K, (∀ j, env.trace j = 0) →
      ¬ RowSat (hardenedSelectorAIR 4) env) :=
  ⟨fun env hz => hardenedSelector_rejects_allZero 11 env hz,
    fun env hz => hardenedSelector_rejects_allZero 4 env hz⟩

/-- Separate correctness proposition for the canonical output.  It contains only conclusions
proved above; no field is added to `BuildableTopology`, `Inputs`, or `BuildableNockExecution`. -/
structure BuiltTopologyAIRCorrectness
    (E : BuildableNockExecution F K) (I : Inputs E) : Prop where
  raw_binding : RawTopologyBindingResidual (buildTopology E I).rawFamily
  arrays_canonical :
    (buildTopology E I).topologyArrays =
      honestTopologyArrays (buildTopology E I).rawFamily
  verifier_generated :
    VerifierGeneratedTopologyRAPSatisfyOfCommittedArrays
      (buildTopology E I).rawFamily (buildTopology E I).topologyArrays
  field_checks :
    ComputeTopologyFieldChecks (buildTopology E I).rawFamily
        (buildTopology E I).topologyArrays.compute ∧
      MemoryTopologyFieldChecks (buildTopology E I).rawFamily
        (buildTopology E I).topologyArrays.memory
  compressed :
    TopologyCompressedCheck (buildTopology E I).rawFamily
      (buildTopology E I).rawFamily.walkGamma
  compute_selectors : ∀ i : Fin E.cfg.compRows,
    RowSat (hardenedSelectorAIR 11)
      (selectorEnv (K := K) 11
        (OptimizedComputeCodec.stateIndex
          (computeTopologyNodeAt (buildTopology E I).rawFamily i).label.1))
  memory_selectors : ∀ i : Fin E.cfg.memRows,
    RowSat (hardenedSelectorAIR 4)
      (selectorEnv (K := K) 4
        (OptimizedMemoryCodec.stateIndex
          (memoryTopologyNodeAt (buildTopology E I).rawFamily i).label.1))

/-- Canonical topology correctness is derived solely from `E` and `I`. -/
theorem builtTopologyAIRCorrectness
    (E : BuildableNockExecution F K) (I : Inputs E) :
    BuiltTopologyAIRCorrectness E I where
  raw_binding := rawTopologyBinding E I
  arrays_canonical := builtArrays_eq_honest E I
  verifier_generated := verifierGeneratedTopologySatisfies E I
  field_checks := topologyFieldChecks E I
  compressed := topologyCompressed E I
  compute_selectors := computeSelectorsHardened E I
  memory_selectors := memorySelectorsHardened E I

/-! ## Output identity and substitution rejection -/

/-- Correctness of an arbitrary data value requires it to be the actual canonical output and then
uses the separately proved canonical correctness theorem. -/
structure BuildableTopologyCorrect (E : BuildableNockExecution F K) (I : Inputs E)
    (T : BuildableTopology E) : Prop where
  output_eq : T = buildTopology E I
  topology : BuiltTopologyAIRCorrectness E I

theorem buildTopology_correct
    (E : BuildableNockExecution F K) (I : Inputs E) :
    BuildableTopologyCorrect E I (buildTopology E I) :=
  ⟨rfl, builtTopologyAIRCorrectness E I⟩

/-- Replacing the raw family, child arrays, chips, domains, roots, or challenges changes the
correctness proposition unless the complete output remains equal to the canonical constructor. -/
theorem substitutedOutput_rejected
    (E : BuildableNockExecution F K) (I : Inputs E) (T : BuildableTopology E)
    (hne : T ≠ buildTopology E I) :
    ¬ BuildableTopologyCorrect E I T := by
  intro h
  exact hne h.output_eq

/-- In particular, replaying otherwise satisfying chip traces against perturbed raw-family
metadata is rejected by the correctness proposition. -/
theorem rawFamilySubstitution_rejected
    (E : BuildableNockExecution F K) (I : Inputs E) (T : BuildableTopology E)
    (hraw : T.raw ≠ buildRawFamily E I) :
    ¬ BuildableTopologyCorrect E I T := by
  apply substitutedOutput_rejected E I T
  intro h
  apply hraw
  exact congrArg BuildableTopology.raw h

/-! ## Exact consumed-tree axis boundary -/

theorem memoryProduction_requires_exact_ancestry
    (E : BuildableNockExecution F K) (I : Inputs E)
    (P : MemoryProductionAssignment (sampledAssignment E I) E.execA) :
    ∀ root : Fin E.cfg.kMem,
      ReadVerifyNested (exactAxisTree E.cfg E.execA root) :=
  P.axisStructural.ancestry

/-- A failed ancestry check on an actual canonical root rules out the requested upgrade from the
primitive chip assignment.  This is stated on `exactAxisTree E.cfg E.execA root`, not on an
independent `MTree` shadow. -/
theorem no_memoryProduction_of_exact_ancestry_failure
    (E : BuildableNockExecution F K) (I : Inputs E)
    (root : Fin E.cfg.kMem)
    (hbad : ¬ ReadVerifyNested (exactAxisTree E.cfg E.execA root)) :
    ¬ MemoryProductionAssignment (sampledAssignment E I) E.execA := by
  intro P
  exact hbad (memoryProduction_requires_exact_ancestry E I P root)

/-- Every production memory assignment also necessarily contains the identically-zero
root-indexed `axis_counts` polynomial, not merely its evaluation at one challenge. -/
theorem memoryProduction_requires_rootPolynomial
    (E : BuildableNockExecution F K) (I : Inputs E)
    (P : MemoryProductionAssignment (sampledAssignment E I) E.execA) :
    ∀ root : Fin E.cfg.kMem,
      countsP_bin (exactAxisTree E.cfg E.execA root) = 0 :=
  P.axisRootPolynomial

/-- A nonzero root polynomial on an actual canonical root independently rules out the production
assignment required by Milestone 4. -/
theorem no_memoryProduction_of_exact_rootPolynomial_failure
    (E : BuildableNockExecution F K) (I : Inputs E)
    (root : Fin E.cfg.kMem)
    (hbad : countsP_bin (exactAxisTree E.cfg E.execA root) ≠ 0) :
    ¬ MemoryProductionAssignment (sampledAssignment E I) E.execA := by
  intro P
  exact hbad (memoryProduction_requires_rootPolynomial E I P root)

/-- The primitive assignment constructed in Milestone 3 remains available independently of both
missing production conclusions. -/
theorem primitiveMemoryAssignment_still_constructed
    (E : BuildableNockExecution F K) (I : Inputs E) :
    MemoryChipAssignment (sampledAssignment E I) :=
  memoryChipAssignment E I

end
end BuildableTopologyCorrectness
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.BuildableTopologyCorrectness.rawTopologyBinding
#print axioms Nock.NockVMROM.Thm54.BuildableTopologyCorrectness.verifierGeneratedTopologySatisfies
#print axioms Nock.NockVMROM.Thm54.BuildableTopologyCorrectness.topologyCompressed
#print axioms Nock.NockVMROM.Thm54.BuildableTopologyCorrectness.computeSelectorsHardened
#print axioms Nock.NockVMROM.Thm54.BuildableTopologyCorrectness.memorySelectorsHardened
#print axioms Nock.NockVMROM.Thm54.BuildableTopologyCorrectness.allZeroTopologySelectorsRejected
#print axioms Nock.NockVMROM.Thm54.BuildableTopologyCorrectness.buildTopology_correct
#print axioms Nock.NockVMROM.Thm54.BuildableTopologyCorrectness.substitutedOutput_rejected
#print axioms Nock.NockVMROM.Thm54.BuildableTopologyCorrectness.rawFamilySubstitution_rejected
#print axioms
  Nock.NockVMROM.Thm54.BuildableTopologyCorrectness.no_memoryProduction_of_exact_ancestry_failure
#print axioms
  Nock.NockVMROM.Thm54.BuildableTopologyCorrectness.no_memoryProduction_of_exact_rootPolynomial_failure
