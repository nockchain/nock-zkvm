import Nock.NockVMROM.Thm54.GenericHonestData
import Nock.RedTeam.Batch96Thm54GenericHonestCommitment
import Nock.RedTeam.Batch101Thm54MemoryAssembly
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

NMR axis carry is not re-litigated (`Def:NMR` 1328, per-node carry 1301).

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  `nounSizeBound` is the execution leaf window `E.Λ`.
`recordEquations` is the reconstructed `memRecSkelOf` identity on the inverse-BFS
compute skeleton, not a new smuggled table and not a `CensusRecordPremises`
field.  The five remaining extras are paper-named, eta-exactly-five, and copied
from `C` rather than inhabited from `E` alone.  `dataOfCensus` still takes `C`.
No `∀ E, Data E`.  Accounting remains `11+1+2`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch102

open scoped Classical
open Nock Nock.Framework Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## A. Derived fields come from `E` and the reconstructed skeleton -/

/-- The reconstructed compute-skeleton rows are exactly `computeSkeletonOf` of
the execution's semantic rows.  Record equations are therefore identities of
that constructor, not a separately supplied table -/
theorem reconstructed_rows_are_computeSkeletonOf
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      ∃ i : Fin E.cfg.compRows,
        s = computeSkeletonOf (E.semanticData.rows i)
          (publicRowNoun_of_execution E i) := by
  intro s hs
  rw [computeSkeletonRows_of_assembly E P M] at hs
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
  rw [List.mem_range'] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  simp only [Nat.one_mul]
  have hidx : k < E.cfg.compRows := by
    rw [← E.exec.compute_bfs_length]
    exact hk
  refine ⟨⟨k, hidx⟩, ?_⟩
  have hlbl : computeLabelAt E P (1 + k) = computeNodeAt E P ⟨k, hidx⟩ := by
    have : (1 + k) - 1 = k := Nat.add_sub_cancel_left 1 k
    simpa [this] using computeLabelAt_of_index E P (i := 1 + k)
      (by simpa [this] using hidx)
  rw [hlbl, computeNodeAt, computeNodeOf]

/-- OP0 `mr2` of `computeSkeletonOf` is the paper copy
`(subject, evaluation)`, by `memRecSkelOf`, and the skeleton
`SkeletonRecordEquations` obligation holds -/
theorem computeSkeletonOf_s0_record_is_memRecSkelOf
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (h : row.1 = .s0)
    (hi : (1 : ℕ) < Nock.Framework.recordCount row.1) :
    ServedLookupBridge.SkeletonRecordEquations (computeSkeletonOf data pubR) ∧
      (computeSkeletonOf data pubR).subject = data.root.subject ∧
      (computeSkeletonOf data pubR).evaluation = data.root.result ∧
      memRecSkelOf data pubR ⟨1, by omega⟩ hi =
        { root := data.root.subject, child := data.root.result
          axis := atomVal data.root.tail } :=
  ⟨computeSkeletonOf_recordEquations data pubR, rfl, rfl,
    memRecSkelOf_mr2_s0 data pubR h hi⟩

/-- OP9 `mr3` of `computeSkeletonOf` is the paper copy
`(sf1.result, sf2.formula)`, by `memRecSkelOf` -/
theorem computeSkeletonOf_s9_record_is_memRecSkelOf
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (h : row.1 = .s9)
    (hi : (2 : ℕ) < Nock.Framework.recordCount row.1) :
    ServedLookupBridge.SkeletonRecordEquations (computeSkeletonOf data pubR) ∧
      memRecSkelOf data pubR ⟨2, by omega⟩ hi =
        { root := subformulaNounOf data pubR ⟨0, by omega⟩
            (by simp [ComputeTable.fanoutComp, h]) .result
          child := subformulaNounOf data pubR ⟨1, by omega⟩
            (by simp [ComputeTable.fanoutComp, h]) .formula
          axis := atomVal (decompNoun data .f_th) } :=
  ⟨computeSkeletonOf_recordEquations data pubR, memRecSkelOf_mr3_s9 data pubR h hi⟩

/-- Assembled record equations do not take a census premise.  They are a
theorem of `E`, `P`, and `M` only -/
theorem recordEquations_of_assembly_independent_of_census
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      ServedLookupBridge.SkeletonRecordEquations s :=
  recordEquations_of_assembly E P M

/-- `censusAssemblyOf` pins the leaf-window numeral to `E.Λ`, not to a field of
`C` -/
theorem censusAssemblyOf_nounSizeBound_is_E_Lambda
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).nounSizeBound = E.Λ :=
  censusAssemblyOf_nounSizeBound E P M C

/-- The assembled record-equation proof is the reconstructed-skeleton identity,
not a `CensusRecordPremises` projection -/
theorem censusAssemblyOf_recordEquations_are_assembly
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).recordEquations =
      recordEquations_of_assembly E P M :=
  censusAssemblyOf_recordEquations E P M C

/-- `dataOfCensus` inherits both derived fields from `E` / the reconstructed
skeleton -/
theorem dataOfCensus_derived_fields_are_from_E
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOfCensus E P M C hln).nounSizeBound = E.Λ ∧
      (dataOfCensus E P M C hln).recordEquations =
        recordEquations_of_assembly E P M ∧
      (dataOfCensus E P M C hln).Λ = E.Λ :=
  dataOfCensus_derived_fields E P M C hln

/-- The older seven-field API still copies a free numeral.  Derivation is the
`censusAssemblyOf` / `dataOfCensus` path, not `dataOf` itself. -/
theorem dataOf_still_copies_free_nounSizeBound
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryAssemblyPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) M.memoryNodes)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOf E P M C hln).nounSizeBound = C.nounSizeBound :=
  rfl

/-! ## B. Five extras are paper-named, eta-exactly-five, and copied from `C` -/

/-- Exhaustive eta receipt: remaining census extras are exactly five fields,
with neither `nounSizeBound` nor `recordEquations` among them, and no `True`
padding -/
theorem censusRecordPremises_eta_exactly_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl

/-- `censusAssemblyOf` copies the five extras from `C`; it does not inhabit
them from `E` alone -/
theorem censusAssemblyOf_copies_five_extras
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).slotSemantics = C.slotSemantics ∧
      (censusAssemblyOf E P M C).census = C.census ∧
      (censusAssemblyOf E P M C).sizeWindowBound = C.sizeWindowBound ∧
      (censusAssemblyOf E P M C).skeletonBounded = C.skeletonBounded ∧
      (censusAssemblyOf E P M C).combinedBounded = C.combinedBounded :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Slot semantics is the two Nock `/` facts of opcode 0 and opcode 9, not a
committed-line pointer -/
theorem slotSemantics_expands_to_noun_slot
    (s : ServedLookupBridge.RowSkeleton)
    (h : ServedLookupBridge.SkeletonSlotSemantics s) :
    (s.state = .s0 →
      Noun.slot (P8Census.skeletonMemoryAxis s 1) s.subject =
        some s.evaluation) ∧
      (s.state = .s9 →
        Noun.slot (P8Census.skeletonMemoryAxis s 2)
          (P8Census.skeletonSubformula s 0 .result) =
            some (P8Census.skeletonSubformula s 1 .formula)) :=
  ⟨h.s0_slot, h.s9_slot⟩

/-- Any inhabitant of the remaining slot extra must reproduce those `/` facts. -/
theorem any_slotSemantics_reproduces_noun_slot
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M)
    {s : ComputeRowSkeleton}
    (hs : s ∈ computeSkeletonRows
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M))) :
    (s.state = .s0 →
      Noun.slot (P8Census.skeletonMemoryAxis s 1) s.subject =
        some s.evaluation) ∧
      (s.state = .s9 →
        Noun.slot (P8Census.skeletonMemoryAxis s 2)
          (P8Census.skeletonSubformula s 0 .result) =
            some (P8Census.skeletonSubformula s 1 .formula)) :=
  slotSemantics_expands_to_noun_slot s (C.slotSemantics s hs)

/-- The OP0/OP9 axis consumed by `/` is the Nat stored in the skeleton memory
record, not a table-row index -/
theorem slot_axis_is_skeleton_memory_record_nat
    (s : ComputeRowSkeleton) (h : s.state = .s0) :
    P8Census.skeletonMemoryAxis s 1 =
      (s.memoryRecord (1 : Fin 3)
        (by simp [h, Nock.Framework.recordCount])).axis := by
  simp [P8Census.skeletonMemoryAxis, h, Nock.Framework.recordCount]

/-- `needs.served` supplies only the paper length for OP0/OP9.  That length is
not an identification of the served witness with the reconstructed skeleton's
subject, axis, and evaluation -/
theorem needs_served_is_length_not_skeleton_identification
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) :
    data.needs.served.length = requiredServedLookups row.1 ∧
      requiredServedLookups .s0 = 1 ∧
      requiredServedLookups .s9 = 1 ∧
      requiredServedLookups .s1 = 0 :=
  ⟨data.needs.served_count, rfl, rfl, rfl⟩

/-- Slot semantics is equivalent to the recognizer `ServedLookup` of the same
nouns, still not a `Vcomp` fingerprint equation -/
theorem slotSemantics_iff_served_lookup
    (s : ServedLookupBridge.RowSkeleton) :
    ServedLookupBridge.SkeletonSlotSemantics s ↔
      ((s.state = .s0 →
          GlobalCarryAxis.ServedLookup
            (GlobalCarryRecognizer.ofNoun s.subject 1)
            (P8Census.skeletonMemoryAxis s 1) s.evaluation) ∧
        (s.state = .s9 →
          GlobalCarryAxis.ServedLookup
            (GlobalCarryRecognizer.ofNoun
              (P8Census.skeletonSubformula s 0 .result) 1)
            (P8Census.skeletonMemoryAxis s 2)
            (P8Census.skeletonSubformula s 1 .formula))) :=
  ServedLookupBridge.skeletonSlotSemantics_iff_served s

/-- SepSeed uniqueness is not demanded -/
theorem census_expands_to_leaf_bounds_not_sepSeed
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (∀ pair ∈ BoundSemanticTrace.skeletonPairs K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      pair.1.leaves ≤ E.Λ ∧ pair.2.leaves ≤ E.Λ) ∧
      (∀ pair ∈ EdgeComparisonCensus.edgePairs
          (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).computeTree,
        pair.1.leaves ≤ E.Λ ∧ pair.2.leaves ≤ E.Λ) :=
  ⟨C.census.p8.leaves_bounded, C.census.edges.leaves_bounded⟩

/-- Size-window extra is a leaf bound on the OP3/OP4/OP6 window nouns, not
`True` -/
theorem sizeWindowBound_expands_to_leaf_bound
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    ∀ n ∈ SizeWindowCounting.skeletonSizeWindowNouns
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      n.leaves ≤ E.Λ :=
  C.sizeWindowBound

/-- `realizedNouns.bounded` covers the root subject/formula/result triple. -/
theorem realizedNouns_cover_subject_formula_result
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) :
    data.root.subject ∈ data.realizedNouns ∧
      data.root.formula ∈ data.realizedNouns ∧
      data.root.result ∈ data.realizedNouns ∧
      (∀ n ∈ data.realizedNouns, FieldEmbedding.BoundedBy q n) :=
  ⟨data.subject_mem, data.formula_mem, data.result_mem, data.bounded⟩

/-- Skeleton boundedness additionally requires every decomposition, subformula,
memory-record noun, memory-row noun, and memory-tree node.  The root triple
does not supply it -/
theorem skeletonBounded_expands_beyond_root_triple
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    let S := skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)
    (computeSkeletonRows S).Forall (ComputeRowSkeleton.BoundedBy E.q) ∧
      (memorySkeletonRows S).Forall (MemoryRowSkeleton.BoundedBy E.q) ∧
      (∀ tree ∈ S.memoryForest, ∀ node, InTree tree node →
        node.label.BoundedBy E.q) :=
  ⟨C.skeletonBounded.computeRows, C.skeletonBounded.memoryRows,
    C.skeletonBounded.memoryTrees⟩

/-- Combined boundedness is `q`-boundedness of every local and edge census pair,
not SepSeed uniqueness -/
theorem combinedBounded_expands_to_pair_atom_bounds
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    ∀ pair ∈ EdgeComparisonCensus.combinedSkeletonPairs K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      FieldEmbedding.BoundedBy E.q pair.1 ∧
        FieldEmbedding.BoundedBy E.q pair.2 :=
  C.combinedBounded

/-! ## C. `Data` still needs named `C` -/

/-- Residual plus memory plus the two derived census fields still do not
produce `Data`: `dataOfCensus` retains the five-field argument and projects
every extra -/
theorem dataOfCensus_still_requires_and_projects_five_extras
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    let D := dataOfCensus E P M C hln
    (∀ s ∈ computeSkeletonRows D.skeleton,
        ServedLookupBridge.SkeletonSlotSemantics s) ∧
      EdgeComparisonCensus.CombinedSkeletonCensus K D.skeleton D.Λ ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy D.skeleton D.Λ ∧
      D.skeleton.BoundedBy E.q ∧
      ProductionP8Containment.CombinedBoundedBy K E.q D.skeleton := by
  dsimp [dataOfCensus, dataOfRecord, dataOf, censusAssemblyOf, Data.skeleton]
  exact ⟨C.slotSemantics, C.census, C.sizeWindowBound, C.skeletonBounded,
    C.combinedBounded⟩

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

theorem memoryRecordPremises_eta_still_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } := by
  cases M
  rfl

/-- Any hypothetical universal `Data` constructor would still manufacture the
named characteristic equality.  This is a consequence, not a claim that the
function space is empty. -/
theorem any_universal_data_constructor_still_forces_q_pin
    (g : ∀ E : BuildableNockExecution F K, Data E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  fun E => (g E).q_eq_ringChar

/-! ## D. Concrete non-vacuity of the two derived fields; F73 does not fire OP0/OP9 -/

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.BuildableConcrete
open Nock.RedTeam.Batch96.ConcretePremises
open Nock.RedTeam.Batch101

/-- The two derived fields are inhabited on the real F73 execution without
manufacturing `CensusRecordPremises`.  That execution is OP1, so the OP0/OP9
antecedents of record equations are false here; the generic `memRecSkelOf`
identities above are the live-branch evidence -/
theorem concrete_derived_fields_nonvacuous_without_census :
    concreteExecution.Λ = 2 ∧
      (∀ s ∈ computeSkeletonRows
          (skeletonOfNodes
            (computeNodesOf concreteExecution f73_residualPremises)
            (memoryNodesOf concreteExecution concreteMemoryRecordPremises)),
        ServedLookupBridge.SkeletonRecordEquations s) :=
  ⟨rfl, recordEquations_of_assembly concreteExecution f73_residualPremises
    concreteMemoryRecordPremises⟩

/-- The F73 compute row is OP1, so `SkeletonSlotSemantics` / live record
equations are implication-vacuous on that fixture.  This is not rounded up to
a generic inhabitant of the five extras. -/
theorem f73_compute_row_is_op1 :
    (concreteExecution.exec.computeRowAt
      ⟨0, concreteExecution.cfg.compRows_pos⟩).1 = .s1 := by
  change
    ((ConcreteStrictPackage.exec honestSeed honestAlpha).computeRowAt
      ⟨0, by
        simpa [concreteExecution, ConcreteStrictPackage.cfg] using
          concreteExecution.cfg.compRows_pos⟩).1 = .s1
  rw [ConcreteStrictPackage.exec] at *
  simp [ExactExecution.computeRowAt, ExactExecution.computeRows,
    Nock.Walk.bfsForest, ConcreteStrictPackage.computeRow,
    ConcreteStrictPackage.cfg]

/-! ## E. -/

inductive ReviewedField102
  | structural
  | optimized_chips
  | shared_io
  | perfect_completeness
  | containment
  | walk_bounds
  | p8_fixed_field_soundness
  | p8_fixed_field_bits
  | acceptance_to_target
  | complete_false_acceptance_bound
  | complete_false_acceptance_bits
  | exact_resources
  | row_budgets
  | shared_forest_axis
deriving DecidableEq

def substantiveFields102 : List ReviewedField102 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields102 : List ReviewedField102 := [.structural]

def residualFields102 : List ReviewedField102 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

theorem independent_exact_eleven_one_two_accounting :
    substantiveFields102.length = 11 ∧
      typeSummaryFields102.length = 1 ∧
      residualFields102 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields102.length = 2 ∧
      (substantiveFields102 ++ typeSummaryFields102 ++ residualFields102).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  ⟨optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth, rfl⟩

#print axioms reconstructed_rows_are_computeSkeletonOf
#print axioms computeSkeletonOf_s0_record_is_memRecSkelOf
#print axioms computeSkeletonOf_s9_record_is_memRecSkelOf
#print axioms recordEquations_of_assembly_independent_of_census
#print axioms censusAssemblyOf_nounSizeBound_is_E_Lambda
#print axioms censusAssemblyOf_recordEquations_are_assembly
#print axioms dataOfCensus_derived_fields_are_from_E
#print axioms dataOf_still_copies_free_nounSizeBound
#print axioms censusRecordPremises_eta_exactly_five
#print axioms censusAssemblyOf_copies_five_extras
#print axioms slotSemantics_expands_to_noun_slot
#print axioms any_slotSemantics_reproduces_noun_slot
#print axioms slot_axis_is_skeleton_memory_record_nat
#print axioms needs_served_is_length_not_skeleton_identification
#print axioms slotSemantics_iff_served_lookup
#print axioms census_expands_to_leaf_bounds_not_sepSeed
#print axioms sizeWindowBound_expands_to_leaf_bound
#print axioms realizedNouns_cover_subject_formula_result
#print axioms skeletonBounded_expands_beyond_root_triple
#print axioms combinedBounded_expands_to_pair_atom_bounds
#print axioms dataOfCensus_still_requires_and_projects_five_extras
#print axioms residualPremises_eta_still_four
#print axioms memoryRecordPremises_eta_still_two
#print axioms any_universal_data_constructor_still_forces_q_pin
#print axioms concrete_derived_fields_nonvacuous_without_census
#print axioms f73_compute_row_is_op1
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeSkeletonOf_recordEquations
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.recordEquations_of_assembly
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.censusAssemblyOf
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.dataOfCensus
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch102
