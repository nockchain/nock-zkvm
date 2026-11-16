import Nock.NockVMROM.Thm54.BuildableTopology
import Nock.RedTeam.Batch69Thm54RepairedP8TraceThreading
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Universal-constructor Milestones 0--1

Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

These receipts test non-vacuity, exhaustive record shape, write-free state
coverage, dependent cfg/exec threading, exact concrete satisfaction indices, and the intended
data-only boundary.
-/

namespace Nock.RedTeam.Batch70

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Framework Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.BuildableConcrete

noncomputable section

local instance prime73 : Fact (Nat.Prime 73) := ⟨by norm_num⟩

/-! ## Exhaustive staged-input shape -/

/-- Exhaustive eta receipt for the universal-constructor input.  No RAP, package, optimized
topology binding, coordinate pin, satisfaction, acceptance, axis conclusion, target, or soundness
field is available to reconstruct in this record.  The cumulative language separately retains the
required semantic arity-3/2 traversal predicates, exposed below. -/
theorem buildable_execution_eta
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (E : BuildableNockExecution F K) :
    E =
      { q := E.q
        q_gt_one := E.q_gt_one
        Λ := E.Λ
        cfg := E.cfg
        execA := E.execA
        exec := E.exec
        exec_encode := E.exec_encode
        semanticData := E.semanticData
        memoryTrace := E.memoryTrace
        requestNodup := E.requestNodup
        recordCountBalance := E.recordCountBalance
        q_le_ringChar := E.q_le_ringChar
        two_ne_zero := E.two_ne_zero
        Ksz_lt_ringChar := E.Ksz_lt_ringChar
        programIOCapacity := E.programIOCapacity
        memoryIOCapacity := E.memoryIOCapacity } := by
  cases E
  rfl

/-- The cumulative language field itself contains exactly traversal/chaining plus noun
realization; it is not a hidden optimized-package or acceptance result. -/
theorem noun_realized_language_eta
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {q : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (L : NounRealizedTraversableChainedSemanticExactLanguage q cfg exec) :
    L =
      { traversable := L.traversable
        nounRealization := L.nounRealization } := by
  cases L
  rfl

/-- The traversability layer is exactly one chained semantic proof and the two fixed arity
topology predicates on the same execution. -/
theorem traversable_language_eta
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (L : TraversableChainedSemanticExactLanguage cfg exec) :
    L =
      { chained := L.chained
        compute_topology := L.compute_topology
        memory_topology := L.memory_topology } := by
  cases L
  rfl

/-- `RecordCountBalanced` hides no record permutation, topology, or acceptance output: it is
definitionally only equality of the verify/read wrapper counts. -/
theorem record_count_balance_exact_shape
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    RowLayout.RecordCountBalanced exec ↔
      RowLayout.memoryStateCount exec .verify_child =
        RowLayout.memoryStateCount exec .read_root :=
  Iff.rfl

/-- Both capacity fields are the literal execution-derived list-length inequalities. -/
theorem io_capacities_exact_shape
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (E : BuildableNockExecution F K) :
    (E.exec.derivedRequestIO.length + 1 ≤ 2 ^ E.cfg.orbit.h) ∧
      (E.exec.derivedResponseIO.length + 1 ≤ 2 ^ E.cfg.orbit.h) :=
  ⟨E.programIOCapacity, E.memoryIOCapacity⟩

/-! ## Authority-prose baseline guards -/

/-- The two currently enforced generic RAP validity facts are genuine structure fields. -/
theorem rap_beta_and_index_bounds
    {F : Type} [Field F] (R : RAP F) :
    R.β ≠ 0 ∧ ∀ q ∈ R.I, q.2 < 2 ^ R.h :=
  ⟨R.β_ne_zero, R.I_bound⟩

@[reducible] noncomputable def direct_s1_cite :=
  @Nock.NockVMROM.nock_uniqueMES

/-- The consumed one-hot realization contains exactly the five paper clauses. -/
theorem one_hot_five_clause_eta
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (H : OneHotRealization cfg exec) :
    H =
      { condition1 := H.condition1
        condition2 := H.condition2
        condition3 := H.condition3
        condition4 := H.condition4
        condition5 := H.condition5 } := by
  cases H
  rfl

/-- The traversal predicates are definitionally the exact arity-3 compute and arity-2 memory
products, not unconstrained topology fields. -/
theorem exact_traversal_arity_shapes
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    ComputeExactTopology exec =
        Walk.RVTWithArity (ComputeTable.Fcomp (K := K)) exec.computeTree ∧
      MemoryExactTopology exec =
        (∀ t ∈ exec.memoryForest,
          Walk.RVTWithArity (MemoryTable.Fmem (K := K)) t) :=
  ⟨rfl, rfl⟩

/-! ## Write-free drift and complete state coverage -/

/-- Exact constructor census for the compute state type. -/
def allComputeStates : List ComputeTable.State :=
  [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .cons]

theorem all_compute_states_exact :
    allComputeStates.Nodup ∧ ∀ s : ComputeTable.State, s ∈ allComputeStates := by
  constructor
  · decide
  · intro s
    cases s <;> decide

/-- Every constructor, including `cons`, satisfies the write-free numeric test. -/
theorem every_compute_state_is_write_free :
    ∀ s : ComputeTable.State, s.toNat < 10 := by
  intro s
  cases s <;> decide

theorem cons_is_present_and_not_opcode10 :
    ComputeTable.State.cons.toNat = 0 ∧
      ComputeTable.State.cons.toNat < 10 ∧
      NodeEncoding.computeStateTag .cons = 11 ∧
      ComputeTable.State.cons ≠ .s0 := by
  decide

/-- All four memory states remain present; write-freedom is a compute-opcode restriction, not a
memory-state deletion. -/
theorem all_memory_states_exact :
    ([MemoryTable.MState.decompose, .halt, .read_root, .verify_child] : List MemoryTable.MState).Nodup ∧
      ∀ s : MemoryTable.MState,
        s ∈ [MemoryTable.MState.decompose, .halt, .read_root, .verify_child] := by
  constructor
  · decide
  · intro s
    cases s <;> decide

/-! ## Exhaustive staged-output shape and dependent object threading -/

/-- Exhaustive eta receipt for the data-only topology output.  In particular there is no
correctness, satisfaction, acceptance, axis, target, or soundness field. -/
theorem buildable_topology_eta
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {E : BuildableNockExecution F K} (T : BuildableTopology E) :
    T =
      { raw := T.raw
        hOrb := T.hOrb
        basis := T.basis
        orbit := T.orbit
        computeNodes := T.computeNodes
        memoryNodes := T.memoryNodes
        computeChallenge := T.computeChallenge
        computePublic := T.computePublic
        memoryChallenge := T.memoryChallenge
        memoryPublic := T.memoryPublic
        computeChipData := T.computeChipData
        memoryChipData := T.memoryChipData
        computeChildPayload := T.computeChildPayload
        memoryChildPayload := T.memoryChildPayload } := by
  cases T
  rfl

/-- Any attempted replacement of the raw family's problem must equal the input's complete
dependent cfg/exec pair. -/
theorem raw_family_problem_substitution_requires_input
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {E : BuildableNockExecution F K} (T : BuildableTopology E)
    (Q : RawProblem F K) (h : T.rawFamily.problem = Q) :
    Q = ⟨E.cfg, E.exec⟩ :=
  h.symm.trans T.rawFamily_problem

/-- Whole-problem equality exposes cfg equality and dependent execution equality. -/
theorem raw_family_problem_substitution_forces_cfg_exec
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {E : BuildableNockExecution F K} (T : BuildableTopology E)
    (Q : RawProblem F K) (h : T.rawFamily.problem = Q) :
    Q.cfg = E.cfg ∧ HEq Q.exec E.exec := by
  have hQ := raw_family_problem_substitution_requires_input T Q h
  cases hQ
  exact ⟨rfl, HEq.rfl⟩

/-- Satisfaction is one proposition over exactly one supplied topology and one trace pair; there
are no independently quantified chips or traces in either conclusion. -/
theorem trace_satisfaction_exact_shape
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {E : BuildableNockExecution F K} (T : BuildableTopology E)
    (Q : BuildableTopologyTraces T) :
    BuildableTraceSatisfaction T Q ↔
      RAP.SatisfiesWithPreprocessing (BuildableTopology.computeChip T) Q.compute ∧
      RAP.SatisfiesWithPreprocessing (BuildableTopology.memoryChip T) Q.memory := by
  constructor
  · intro h
    exact ⟨h.compute, h.memory⟩
  · rintro ⟨hc, hm⟩
    exact ⟨hc, hm⟩

/-- The two missing constructors are genuinely function types, not fields or assumptions. -/
theorem missing_constructor_types_are_functions
    (F K : Type) [Field F] [Field K] [Algebra F K] :
    BuildableTopologyConstructor F K =
        ((E : BuildableNockExecution F K) → BuildableTopology E) ∧
      (∀ build : BuildableTopologyConstructor F K,
        BuildableTopologyTraceConstructor build =
          ((E : BuildableNockExecution F K) → BuildableTopologyTraces (build E))) :=
  ⟨rfl, fun _ => rfl⟩

/-! ## Concrete F73 non-vacuity and exact indices -/

/-- Substantive projections from the minimal concrete input: positive rows, write-freedom,
semantic timestamps, all five one-hot clauses, exact arity-3/2 traversal, request uniqueness,
record balance, both capacities, and the exact `M+2L` budget. -/
theorem concrete_execution_substantive_nonvacuity :
    concreteExecution.q = 73 ∧
      1 < concreteExecution.q ∧
      0 < concreteExecution.cfg.compRows ∧
      0 < concreteExecution.cfg.memRows ∧
      WriteFreeExactExecution concreteExecution.exec ∧
      Nonempty (SemanticIOPreimage concreteExecution.cfg concreteExecution.exec) ∧
      OneHotRealization concreteExecution.cfg concreteExecution.exec ∧
      ComputeExactTopology concreteExecution.exec ∧
      MemoryExactTopology concreteExecution.exec ∧
      concreteExecution.exec.derivedRequestIO.Nodup ∧
      RowLayout.RecordCountBalanced concreteExecution.exec ∧
      concreteExecution.exec.derivedRequestIO.length + 1 ≤
        2 ^ concreteExecution.cfg.orbit.h ∧
      concreteExecution.exec.derivedResponseIO.length + 1 ≤
        2 ^ concreteExecution.cfg.orbit.h ∧
      concreteExecution.cfg.memRows =
        RowLayout.memoryM concreteExecution.exec +
          2 * RowLayout.memoryL concreteExecution.exec := by
  exact
    ⟨rfl, concreteExecution.q_gt_one,
      concreteExecution.computeRows_pos, concreteExecution.memoryRows_pos,
      concreteExecution.writeFree, concreteExecution.timestampBounds,
      concreteExecution.oneHot, concreteExecution.traversal.1,
      concreteExecution.traversal.2, concreteExecution.requestNodup,
      concreteExecution.recordCountBalance, concreteExecution.programIOCapacity,
      concreteExecution.memoryIOCapacity,
      concreteExecution.memoryRows_eq_M_add_two_mul_L⟩

/-- All output stages and the separate correctness proposition are inhabited together, and the
raw family is definitionally tied to the same concrete input problem.
`hmore` is the remaining Relaxis join at form R (`kMem = 2` dummy halt). -/
theorem concrete_all_stages_nonvacuous
    (hbasis : OptimizedComputeFinalTrace.FormRBasis ConcreteStrictPackage.basis73)
    (hmore : ∀ i : Fin ConcreteStrictPackage.honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < ConcreteStrictPackage.honestLegacyFamily.problem.cfg.kMem →
        (ConcreteStrictPackage.honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (ConcreteStrictPackage.honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0) :
    Nonempty
        (BuildableNockExecution
          ConcreteStrictPackage.F73 ConcreteStrictPackage.K73cubic) ∧
      Nonempty (BuildableTopology concreteExecution) ∧
      Nonempty (BuildableTopologyTraces concreteTopology) ∧
      BuildableTraceSatisfaction concreteTopology concreteTraces ∧
      (BuildableTopology.rawFamily concreteTopology).problem =
        ⟨concreteExecution.cfg, concreteExecution.exec⟩ :=
  ⟨⟨concreteExecution⟩, ⟨concreteTopology⟩, ⟨concreteTraces⟩,
    concreteTraceSatisfaction hbasis hmore, concreteTopology.rawFamily_problem⟩

/-- The concrete satisfaction proof projects the exact concrete topology and concrete traces. -/
theorem concrete_satisfaction_projects_exact_objects
    (hbasis : OptimizedComputeFinalTrace.FormRBasis ConcreteStrictPackage.basis73)
    (hmore : ∀ i : Fin ConcreteStrictPackage.honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < ConcreteStrictPackage.honestLegacyFamily.problem.cfg.kMem →
        (ConcreteStrictPackage.honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (ConcreteStrictPackage.honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0) :
    RAP.SatisfiesWithPreprocessing
        (BuildableTopology.computeChip concreteTopology) concreteTraces.compute ∧
      RAP.SatisfiesWithPreprocessing
        (BuildableTopology.memoryChip concreteTopology) concreteTraces.memory :=
  ⟨(concreteTraceSatisfaction hbasis hmore).compute, (concreteTraceSatisfaction hbasis hmore).memory⟩

/-! ## Intended data-only boundary -/

/-- A deliberately altered raw-family datum on the same indexed execution. -/
def perturbedRawFamily : BuildableRawFamily concreteExecution :=
  { concreteRawFamily with
    computeWalkAlpha := concreteRawFamily.computeWalkAlpha + 1 }

theorem perturbed_raw_family_is_distinct :
    perturbedRawFamily ≠ concreteRawFamily := by
  intro h
  have ha := congrArg
    (fun R : BuildableRawFamily concreteExecution => R.computeWalkAlpha) h
  simp [perturbedRawFamily] at ha

/-- Changing arbitrary raw-family data leaves the dependent problem index fixed. -/
def perturbedTopology : BuildableTopology concreteExecution :=
  { concreteTopology with raw := perturbedRawFamily }

theorem perturbed_topology_problem_still_fixed :
    (BuildableTopology.rawFamily perturbedTopology).problem =
      ⟨concreteExecution.cfg, concreteExecution.exec⟩ :=
  perturbedTopology.rawFamily_problem

/-- The optimized trace type depends on the chip fields, not on arbitrary raw-family metadata. -/
def perturbedTraces : BuildableTopologyTraces perturbedTopology where
  compute := concreteTraces.compute
  memory := concreteTraces.memory

/-- The same chip traces remain satisfying after changing an unrelated raw-family datum.  This is
the compiled negative control showing that `BuildableTraceSatisfaction` is only chip-trace
satisfaction; it is not topology/payload correctness, which later milestones must derive. -/
theorem trace_satisfaction_does_not_bind_raw_family
    (hbasis : OptimizedComputeFinalTrace.FormRBasis ConcreteStrictPackage.basis73)
    (hmore : ∀ i : Fin ConcreteStrictPackage.honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < ConcreteStrictPackage.honestLegacyFamily.problem.cfg.kMem →
        (ConcreteStrictPackage.honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (ConcreteStrictPackage.honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0) :
    BuildableTraceSatisfaction perturbedTopology perturbedTraces := by
  constructor
  · simpa [perturbedTopology, perturbedTraces, BuildableTopology.computeChip] using
      (concreteTraceSatisfaction hbasis hmore).compute
  · simpa [perturbedTopology, perturbedTraces, BuildableTopology.memoryChip] using
      (concreteTraceSatisfaction hbasis hmore).memory

/-! ## Release and documentation guards -/

theorem release_aliases_unchanged :
    @«Thm:NockVMROM» =
        @Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch69.repaired_alias_and_forest_control

#print axioms Nock.NockVMROM.Thm54.writeFreeExactExecution
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.writeFree
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.computeRows_pos
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.memoryRows_pos
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.timestampBounds
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.chained
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.oneHot
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.traversal
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.memoryRows_eq_M_add_two_mul_L
#print axioms Nock.NockVMROM.Thm54.BuildableTopology.rawFamily_problem
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteLanguage
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteExecution
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteTopology
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteTraces
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteTraceSatisfaction
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concrete_nonvacuous
#print axioms buildable_execution_eta
#print axioms record_count_balance_exact_shape
#print axioms rap_beta_and_index_bounds
#print axioms direct_s1_cite
#print axioms one_hot_five_clause_eta
#print axioms exact_traversal_arity_shapes
#print axioms every_compute_state_is_write_free
#print axioms cons_is_present_and_not_opcode10
#print axioms buildable_topology_eta
#print axioms raw_family_problem_substitution_forces_cfg_exec
#print axioms trace_satisfaction_exact_shape
#print axioms concrete_execution_substantive_nonvacuity
#print axioms concrete_all_stages_nonvacuous
#print axioms perturbed_raw_family_is_distinct
#print axioms trace_satisfaction_does_not_bind_raw_family
#print axioms release_aliases_unchanged

end
end Nock.RedTeam.Batch70
