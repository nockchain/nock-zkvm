import Nock.NockVMROM.Thm54.BuildableAxisWitness

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# buildable semantic input and reverse axis witness

Paper frame:
the paper, with exact batching at
the paper.

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

It does not inhabit the generic localization
bridge or repoint the paper alias. -/

namespace Nock.RedTeam.Batch73

open scoped Classical Polynomial
open Polynomial
open Nock Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildableTopologyCorrectness
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedMemorySameExecution
open Nock.NockVMROM.Thm54.TemplateAxisCounting

noncomputable section

/-! ## A. Exhaustive semantic input shape -/

/-- The strengthened universal input contains exactly semantic/pre-compilation data. -/
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

/-- `ExactExecutionSemanticData` has only the prior cumulative language, genuine row acceptance,
and semantic data on the authoritative `exec.computeRowAt`; it has no axis polynomial, production
assignment, optimized acceptance, target, or capstone theorem field. -/
theorem exact_semantic_data_eta
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (D : ExactExecutionSemanticData q Λ cfg exec) :
    D =
      { language := D.language
        rowAccepted := D.rowAccepted
        rows := D.rows } := by
  cases D
  rfl

/-- Served lookups occur only inside `needs`; no batching boundary or
theorem conclusion is hidden in a row certificate. -/
theorem compute_row_semantic_data_eta
    {K : Type} [Field K] {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (D : ComputeRowSemanticData q Λ row) :
    D =
      { root := D.root
        tails := D.tails
        branchTails := D.branchTails
        calls := D.calls
        windows := D.windows
        axisGates := D.axisGates
        tails_count := D.tails_count
        branchTails_count := D.branchTails_count
        calls_count := D.calls_count
        windows_count := D.windows_count
        axisGates_count := D.axisGates_count
        realizedNouns := D.realizedNouns
        subject_mem := D.subject_mem
        formula_mem := D.formula_mem
        result_mem := D.result_mem
        bounded := D.bounded
        comparisons := D.comparisons
        comparison_faithful := D.comparison_faithful
        comparison_leaves := D.comparison_leaves
        comparison_roles := D.comparison_roles
        axisGate_listed := D.axisGate_listed
        axisGate_tail_mem := D.axisGate_tail_mem
        needs := D.needs } := by
  cases D
  rfl

/-- A served lookup carries one exact record, nouns, a Nat axis, record realization, and genuine
global-carry slot service—no batching conclusion. -/
theorem served_lookup_eta
    {K : Type} [Field K] {z : K} (S : ServedNounLookup z) :
    S =
      { record := S.record
        root := S.root
        axis := S.axis
        child := S.child
        realization := S.realization
        served := S.served } := by
  cases S
  rfl

/-- The compatibility language accessor is definitionally the semantic bundle's language. -/
theorem language_is_pinned_to_semantic_data
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (E : BuildableNockExecution F K) :
    E.language = E.semanticData.language :=
  rfl

/-- Any proposed substitute for the accessor must equal the exact language stored in
`semanticData`; the dependent cfg/exec indices cannot be changed independently. -/
theorem language_substitution_requires_identity
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (E : BuildableNockExecution F K)
    (L : NounRealizedTraversableChainedSemanticExactLanguage E.q E.cfg E.exec)
    (h : E.language = L) :
    L = E.semanticData.language := by
  exact h.symm

/-! ## B. Reverse theorem statement and load-bearing controls -/

abbrev K5 := ZMod 5

local instance prime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private theorem two_ne_zero_K5 : (2 : K5) ≠ 0 := by decide

/-- A genuine nontrivial left-child lookup: root axis `1` doubles to axis `2`. -/
def leftAxisTree : MTree K5 :=
  .read 7 (.decompose (.verify 7 2 .halt) .halt)

/-- Independent application of the new reverse theorem on a nontrivial tree. -/
theorem left_axis_reverse_theorem :
    countsP_bin leftAxisTree = 0 := by
  apply countsP_zero_of_exactMemoryAxisValidity two_ne_zero_K5
  · simp [leftAxisTree, readExps]
  · simp [leftAxisTree, verifyExps]
  · intro e
    simp [leftAxisTree, readExps, verifyExps]
  · intro e he
    have heq : e = 7 := by simpa [leftAxisTree, readExps] using he
    subst e
    simp [leftAxisTree, Nested, readCount, verifyCount]
  · intro e he
    have heq : e = 7 := by simpa [leftAxisTree, readExps] using he
    subst e
    norm_num [leftAxisTree, vaxis, Relaxis, vaddr, vdep, readCount, verifyCount]

/-- A genuine nontrivial right-child lookup: doubling plus the right bit gives axis `3`. -/
def rightAxisTree : MTree K5 :=
  .read 9 (.decompose .halt (.verify 9 3 .halt))

/-- Independent right-branch application of the reverse theorem. -/
theorem right_axis_reverse_theorem :
    countsP_bin rightAxisTree = 0 := by
  apply countsP_zero_of_exactMemoryAxisValidity two_ne_zero_K5
  · simp [rightAxisTree, readExps]
  · simp [rightAxisTree, verifyExps]
  · intro e
    simp [rightAxisTree, readExps, verifyExps]
  · intro e he
    have heq : e = 9 := by simpa [rightAxisTree, readExps] using he
    subst e
    simp [rightAxisTree, Nested, readCount, verifyCount]
  · intro e he
    have heq : e = 9 := by simpa [rightAxisTree, readExps] using he
    subst e
    norm_num [rightAxisTree, vaxis, Relaxis, vaddr, vdep, readCount, verifyCount]

/-- The concrete recurrences have the paper's signs, halving, and left/right convention. -/
theorem left_right_recurrence_receipt :
    vaxis 7 leftAxisTree = 2 ∧
      Relaxis 7 leftAxisTree = 2 ∧
      countsP_bin leftAxisTree = 0 ∧
      vaxis 9 rightAxisTree = 3 ∧
      Relaxis 9 rightAxisTree = 3 ∧
      countsP_bin rightAxisTree = 0 := by
  refine ⟨by norm_num [leftAxisTree, vaxis, verifyCount],
    by norm_num [leftAxisTree, Relaxis, vaddr, vdep, readCount, verifyCount],
    left_axis_reverse_theorem,
    by norm_num [rightAxisTree, vaxis, verifyCount],
    by norm_num [rightAxisTree, Relaxis, vaddr, vdep, readCount, verifyCount],
    right_axis_reverse_theorem⟩

/-- Dropping exact read/verify support equality is invalid even with uniqueness, nesting, and
semantic validity for every read exponent.  The unmatched verify contributes `X`. -/
def supportMismatchTree : MTree K5 :=
  .read 0 (.verify 0 1 (.verify 1 1 .halt))

theorem support_equality_is_load_bearing :
    (readExps supportMismatchTree).Nodup ∧
      (verifyExps supportMismatchTree).Nodup ∧
      (∀ e, e ∈ readExps supportMismatchTree → Nested e supportMismatchTree) ∧
      (∀ e, e ∈ readExps supportMismatchTree →
        vaxis e supportMismatchTree = Relaxis e supportMismatchTree) ∧
      (¬ ∀ e, e ∈ readExps supportMismatchTree ↔ e ∈ verifyExps supportMismatchTree) ∧
      countsP_bin supportMismatchTree ≠ 0 := by
  refine ⟨by simp [supportMismatchTree, readExps],
    by simp [supportMismatchTree, verifyExps], ?_, ?_, ?_, ?_⟩
  · intro e he
    have heq : e = 0 := by simpa [supportMismatchTree, readExps] using he
    subst e
    simp [supportMismatchTree, Nested, readCount]
  · intro e he
    have heq : e = 0 := by simpa [supportMismatchTree, readExps] using he
    subst e
    norm_num [supportMismatchTree, vaxis, Relaxis, vaddr, vdep, readCount, verifyCount]
  · intro h
    have := (h 1).2
    simp [supportMismatchTree, readExps, verifyExps] at this
  · intro h
    have hc := congrArg (fun P : K5[X] => P.coeff 1) h
    norm_num [supportMismatchTree, countsP_bin, indP_bin] at hc

/-- Semantic axis validity is independently load-bearing. -/
def wrongAxisTree : MTree K5 :=
  .read 0 (.verify 0 2 .halt)

theorem semantic_axis_validity_is_load_bearing :
    (readExps wrongAxisTree).Nodup ∧
      (verifyExps wrongAxisTree).Nodup ∧
      (∀ e, e ∈ readExps wrongAxisTree ↔ e ∈ verifyExps wrongAxisTree) ∧
      (∀ e, e ∈ readExps wrongAxisTree → Nested e wrongAxisTree) ∧
      (¬ ∀ e, e ∈ readExps wrongAxisTree →
        vaxis e wrongAxisTree = Relaxis e wrongAxisTree) ∧
      countsP_bin wrongAxisTree ≠ 0 := by
  refine ⟨by simp [wrongAxisTree, readExps],
    by simp [wrongAxisTree, verifyExps], ?_, ?_, ?_, ?_⟩
  · intro e
    simp [wrongAxisTree, readExps, verifyExps]
  · intro e he
    have heq : e = 0 := by simpa [wrongAxisTree, readExps] using he
    subst e
    simp [wrongAxisTree, Nested, readCount]
  · intro h
    have hh := h 0 (by simp [wrongAxisTree, readExps])
    norm_num [wrongAxisTree, vaxis, Relaxis, vaddr, vdep, readCount, verifyCount] at hh
    exact (show (2 : K5) ≠ 1 by decide) hh
  · intro h
    have hc := congrArg (fun P : K5[X] => P.coeff 0) h
    norm_num [wrongAxisTree, countsP_bin, indP_bin] at hc

/-- Nesting is load-bearing independently of support, uniqueness, and the selected exponent's
semantic axis equality. -/
def crossingTree : MTree K5 :=
  .decompose (.read 0 .halt) (.verify 0 1 .halt)

theorem nesting_is_load_bearing :
    (readExps crossingTree).Nodup ∧
      (verifyExps crossingTree).Nodup ∧
      (∀ e, e ∈ readExps crossingTree ↔ e ∈ verifyExps crossingTree) ∧
      (∀ e, e ∈ readExps crossingTree →
        vaxis e crossingTree = Relaxis e crossingTree) ∧
      (¬ ∀ e, e ∈ readExps crossingTree → Nested e crossingTree) ∧
      countsP_bin crossingTree ≠ 0 := by
  refine ⟨by simp [crossingTree, readExps],
    by simp [crossingTree, verifyExps], ?_, ?_, ?_, ?_⟩
  · intro e
    simp [crossingTree, readExps, verifyExps]
  · intro e he
    have heq : e = 0 := by simpa [crossingTree, readExps] using he
    subst e
    norm_num [crossingTree, vaxis, Relaxis, vaddr, vdep, readCount, verifyCount]
  · intro h
    have hh := h 0 (by simp [crossingTree, readExps])
    simp [crossingTree, Nested, readCount, verifyCount] at hh
  · intro h
    have hc := congrArg (fun P : K5[X] => P.coeff 0) h
    norm_num [crossingTree, countsP_bin, indP_bin] at hc
    exact (show (2 : K5) ≠ 0 by decide) hc

/-- Timestamp uniqueness is load-bearing: duplicate exponent pairs can hide the wrong second
axis while `vaxis`/`Relaxis` select the honest first pair. -/
def duplicateExponentTree : MTree K5 :=
  .decompose
    (.read 0 (.verify 0 1 .halt))
    (.read 0 (.verify 0 2 .halt))

theorem timestamp_nodup_is_load_bearing :
    (¬ (readExps duplicateExponentTree).Nodup) ∧
      (¬ (verifyExps duplicateExponentTree).Nodup) ∧
      (∀ e, e ∈ readExps duplicateExponentTree ↔ e ∈ verifyExps duplicateExponentTree) ∧
      (∀ e, e ∈ readExps duplicateExponentTree → Nested e duplicateExponentTree) ∧
      (∀ e, e ∈ readExps duplicateExponentTree →
        vaxis e duplicateExponentTree = Relaxis e duplicateExponentTree) ∧
      countsP_bin duplicateExponentTree ≠ 0 := by
  refine ⟨by simp [duplicateExponentTree, readExps],
    by simp [duplicateExponentTree, verifyExps], ?_, ?_, ?_, ?_⟩
  · intro e
    simp [duplicateExponentTree, readExps, verifyExps]
  · intro e he
    have heq : e = 0 := by simpa [duplicateExponentTree, readExps] using he
    subst e
    simp [duplicateExponentTree, Nested, readCount, verifyCount]
  · intro e he
    have heq : e = 0 := by simpa [duplicateExponentTree, readExps] using he
    subst e
    norm_num [duplicateExponentTree, vaxis, Relaxis, vaddr, vdep, readCount, verifyCount]
  · intro h
    have hc := congrArg (fun P : K5[X] => P.coeff 0) h
    norm_num [duplicateExponentTree, countsP_bin, indP_bin] at hc
    exact (show (2 : K5) ≠ 0 by decide) hc

/-- One sampled zero does not imply the polynomial identity. -/
def sampledOnlyTree : MTree K5 :=
  .read 1 (.verify 1 2 .halt)

theorem sampled_evaluation_is_not_polynomial_identity :
    (countsP_bin sampledOnlyTree).eval 0 = 0 ∧ countsP_bin sampledOnlyTree ≠ 0 := by
  constructor
  · norm_num [sampledOnlyTree, countsP_bin, indP_bin]
  · intro h
    have hc := congrArg (fun P : K5[X] => P.coeff 1) h
    norm_num [sampledOnlyTree, countsP_bin, indP_bin] at hc

/-! ## C. Concrete same-object witness, dependencies, and honest scope -/

open ConcreteStrictPackage
open BuildableConcrete
open BuildableChips.Concrete
open BuildableAxisWitness.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := ConcreteStrictPackage.concrete_char73
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- The production carrier itself has exactly primitive obligations, structural ancestry/support
data, and the root-polynomial identity on the same sampled assignment. -/
theorem memory_production_eta
    (P : MemoryProductionAssignment (sampledAssignment concreteExecution inputs73)
      concreteExecution.execA) :
    P =
      { obligations := P.obligations
        exec_encode := P.exec_encode
        axisStructural := P.axisStructural
        axisRootPolynomial := P.axisRootPolynomial
        axisRootIndicator := P.axisRootIndicator
        rootPubZero := P.rootPubZero } := by
  cases P
  rfl

/-- Semantic data, finite sampled IO, structural/root-polynomial witnesses, and the final
production assignment are all indexed by the identical concrete cfg/exec. -/
theorem concrete_same_object_threading
    (hmore : BuildableAxisWitness.LaterSeedZeros concreteExecution) :
    concreteExecution.language = concreteExecution.semanticData.language ∧
      (sampledAssignment concreteExecution inputs73).sampled.records.requests =
        concreteExecution.exec.derivedRequestIO ∧
      (sampledAssignment concreteExecution inputs73).sampled.records.responses =
        concreteExecution.exec.derivedResponseIO ∧
      (exactFamilyCompletion concreteExecution inputs73).family.problem.cfg =
        concreteExecution.cfg ∧
      HEq (exactFamilyCompletion concreteExecution inputs73).family.problem.exec
        concreteExecution.exec ∧
      ExactAxisStructuralRefinement concreteExecution.cfg concreteExecution.execA ∧
      (∀ root : Fin concreteExecution.cfg.kMem,
        countsP_bin (exactAxisTree concreteExecution.cfg concreteExecution.execA root) = 0) ∧
      Nonempty
        (MemoryProductionAssignment (sampledAssignment concreteExecution inputs73)
          concreteExecution.execA) := by
  refine ⟨rfl, rfl, rfl, rfl, HEq.rfl, ?_, ?_, ⟨memoryProduction hmore⟩⟩
  · exact (memoryProduction hmore).axisStructural
  · exact (memoryProduction hmore).axisRootPolynomial

/-- Whole dependent-problem substitution forces both cfg and execution identity. -/
theorem mismatched_execution_substitution_forces_identity
    (Q : ExactCanonicalRAPProblem F73 K73cubic)
    (hQ : (exactFamilyCompletion concreteExecution inputs73).family.problem = Q) :
    Q.cfg = concreteExecution.cfg ∧ HEq Q.exec concreteExecution.exec := by
  cases hQ
  exact ⟨rfl, HEq.rfl⟩

/-- The imported structural and root-polynomial witnesses pre-exist in the concrete memory module.
They are sufficient independently of the downstream `BuildableAxisWitness.memoryProduction`
definition and of the new reverse theorem. -/
theorem concrete_axis_dependencies_preexist :
    ExactAxisStructuralRefinement
        honestLegacyFamily.problem.cfg OptimizedMemorySameExecution.Concrete.honestExecA ∧
      ∀ root : Fin honestLegacyFamily.problem.cfg.kMem,
        countsP_bin (exactAxisTree honestLegacyFamily.problem.cfg
          OptimizedMemorySameExecution.Concrete.honestExecA root) = 0 :=
  ⟨OptimizedMemorySameExecution.Concrete.honest_axisStructural,
    OptimizedMemorySameExecution.Concrete.honest_axisRootPolynomial⟩

/-- The F73 compute fixture is a singleton terminal OP1 row, while its memory fixture has genuine
nonterminal `read_root`/`decompose` rows and an actual `verify_child` event. -/
theorem concrete_fixture_exact_scope :
    concreteExecution.cfg.compRows = 1 ∧
      ((ConcreteStrictPackage.exec honestSeed honestAlpha).computePubAt
        ⟨0, by norm_num [ConcreteStrictPackage.cfg]⟩).state = .s1 ∧
      ((ConcreteStrictPackage.exec honestSeed honestAlpha).memoryPubAt
        ⟨1, by norm_num [ConcreteStrictPackage.cfg]⟩).st = .read_root ∧
      ((ConcreteStrictPackage.exec honestSeed honestAlpha).memoryPubAt
        ⟨2, by norm_num [ConcreteStrictPackage.cfg]⟩).st = .decompose ∧
      ((ConcreteStrictPackage.exec honestSeed honestAlpha).memoryPubAt
        ⟨4, by norm_num [ConcreteStrictPackage.cfg]⟩).st = .verify_child := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rw [ConcreteStrictPackage.computePubAt_zero]
    rfl
  · rw [ConcreteStrictPackage.memoryPubAt_one]
    rfl
  · rw [ConcreteStrictPackage.memoryPubAt_two]
    rfl
  · rw [ConcreteStrictPackage.memoryPubAt_four]
    rfl

/-- The exact concrete root has an actually used timestamp and exports its axis consequence. -/
theorem concrete_used_axis_nonvacuous
    (hmore : BuildableAxisWitness.LaterSeedZeros concreteExecution) :
    ∃ (root : Fin concreteExecution.cfg.kMem) (e : ℕ),
      e ∈ readExps (exactAxisTree concreteExecution.cfg concreteExecution.execA root) ∧
      e ∈ verifyExps (exactAxisTree concreteExecution.cfg concreteExecution.execA root) ∧
      vaxis e (exactAxisTree concreteExecution.cfg concreteExecution.execA root) =
        Relaxis e (exactAxisTree concreteExecution.cfg concreteExecution.execA root) := by
  let root : Fin concreteExecution.cfg.kMem := ⟨1, by
    norm_num [concreteExecution, ConcreteStrictPackage.cfg]⟩
  let e := timestampExp
    (ConcreteStrictPackage.cfg honestSeed honestAlpha).challenges.α
    (ConcreteStrictPackage.readPub honestSeed honestAlpha).mem.ts
  refine ⟨root, e, ?_, ?_, axis_eq_relaxis_of_used hmore root e ?_ ?_⟩
  all_goals
    simp [root, e, concreteExecution, exactAxisTree, ExactExecution.memoryTreeAt,
      ConcreteStrictPackage.execA, ConcreteStrictPackage.readTreeA,
      ConcreteStrictPackage.decomposeTreeA, ConcreteStrictPackage.verifyTreeA,
      ConcreteStrictPackage.readRowA, ConcreteStrictPackage.verifyRowA,
      ConcreteStrictPackage.readPubA, ConcreteStrictPackage.verifyPubA,
      ConcreteStrictPackage.rowRecord,
      ConcreteStrictPackage.exec, ConcreteStrictPackage.readTree,
      ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
      ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
      ConcreteStrictPackage.readRow, ConcreteStrictPackage.decomposeRow,
      ConcreteStrictPackage.headRow, ConcreteStrictPackage.verifyRow,
      ConcreteStrictPackage.tailRow, AxisBridge.ofNTree, AxisBridge.MemWalk.toMTree,
      ConcreteStrictPackage.readPub, ConcreteStrictPackage.verifyPub,
      ConcreteStrictPackage.requestRecord, timestampExpAt, readExps, verifyExps]
  all_goals
    (erw [List.getElem_cons_succ]
     simp [root, e, concreteExecution, exactAxisTree, ExactExecution.memoryTreeAt,
      ConcreteStrictPackage.execA, ConcreteStrictPackage.readTreeA,
      ConcreteStrictPackage.decomposeTreeA, ConcreteStrictPackage.verifyTreeA,
      ConcreteStrictPackage.readRowA, ConcreteStrictPackage.verifyRowA,
      ConcreteStrictPackage.readPubA, ConcreteStrictPackage.verifyPubA,
      ConcreteStrictPackage.rowRecord,
      ConcreteStrictPackage.exec, ConcreteStrictPackage.readTree,
      ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
      ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
      ConcreteStrictPackage.readRow, ConcreteStrictPackage.decomposeRow,
      ConcreteStrictPackage.headRow, ConcreteStrictPackage.verifyRow,
      ConcreteStrictPackage.tailRow, AxisBridge.ofNTree, AxisBridge.MemWalk.toMTree,
      ConcreteStrictPackage.readPub, ConcreteStrictPackage.verifyPub,
      ConcreteStrictPackage.requestRecord, timestampExpAt, readExps, verifyExps])

/-! ## D. Generic M4 remains a function target, not a theorem supplied by this patch -/

/-- Exact still-open generic target.  This declaration only names the function type; it does not
provide an inhabitant. -/
def GenericMemoryProductionConstructor : Prop :=
  ∀ {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)],
    ∀ (E : BuildableNockExecution F K) (I : Inputs E),
      Nonempty (MemoryProductionAssignment (sampledAssignment E I) E.execA)

theorem generic_m4_target_exact_shape :
    GenericMemoryProductionConstructor =
      (∀ {F K : Type} [Field F] [Field K] [Algebra F K]
        [FiniteDimensional F K] [Fintype K] [DecidableEq K]
        [CharP K (ringChar K)],
        ∀ (E : BuildableNockExecution F K) (I : Inputs E),
          Nonempty (MemoryProductionAssignment (sampledAssignment E I) E.execA)) :=
  rfl

/-- What the patch supplies generically is only the consumed-tree necessity direction. -/
theorem generic_stop_boundary_exact_shape
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E)
    (P : MemoryProductionAssignment (sampledAssignment E I) E.execA) :
    (∀ root : Fin E.cfg.kMem,
      ReadVerifyNested (exactAxisTree E.cfg E.execA root)) ∧
    (∀ root : Fin E.cfg.kMem,
      countsP_bin (exactAxisTree E.cfg E.execA root) = 0) :=
  ⟨memoryProduction_requires_exact_ancestry E I P,
    memoryProduction_requires_rootPolynomial E I P⟩

#print axioms Nock.AxisBridge.countsP_zero_of_exactMemoryAxisValidity
#print axioms Nock.AxisBridge.countsP_zero_of_exactMemoryAxisValidity_single
#print axioms Nock.NockVMROM.Thm54.BuildableAxisWitness.rootPolynomial_of_exactMemoryAxisValidity
#print axioms Nock.NockVMROM.Thm54.BuildableNockExecution.language
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteSemanticData
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteExecution
#print axioms Nock.NockVMROM.Thm54.OptimizedMemorySameExecution.Concrete.honest_axisStructural
#print axioms Nock.NockVMROM.Thm54.OptimizedMemorySameExecution.Concrete.honest_axisRootPolynomial
#print axioms Nock.NockVMROM.Thm54.BuildableAxisWitness.Concrete.memoryProduction
#print axioms Nock.NockVMROM.Thm54.BuildableAxisWitness.Concrete.memoryProduction_nonvacuous
#print axioms Nock.NockVMROM.Thm54.BuildableAxisWitness.Concrete.axis_eq_relaxis_of_used
#print axioms buildable_execution_eta
#print axioms exact_semantic_data_eta
#print axioms compute_row_semantic_data_eta
#print axioms left_axis_reverse_theorem
#print axioms right_axis_reverse_theorem
#print axioms left_right_recurrence_receipt
#print axioms support_equality_is_load_bearing
#print axioms semantic_axis_validity_is_load_bearing
#print axioms nesting_is_load_bearing
#print axioms timestamp_nodup_is_load_bearing
#print axioms sampled_evaluation_is_not_polynomial_identity
#print axioms concrete_same_object_threading
#print axioms mismatched_execution_substitution_forces_identity
#print axioms concrete_axis_dependencies_preexist
#print axioms concrete_fixture_exact_scope
#print axioms concrete_used_axis_nonvacuous
#print axioms generic_m4_target_exact_shape
#print axioms generic_stop_boundary_exact_shape

end
end Nock.RedTeam.Batch73
