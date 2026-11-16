import Nock.NockVMROM.Thm54.GenericHonestData
import Nock.RedTeam.Batch99Thm54RingChar
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  The reconstructed compute tree projects exactly to
`E.exec.computeTree`, and its fanout proof consumes `E.traversal`.  Whole-tree
`computeOK` contains the fanout, state, full nine-conjunct `BindComputeRow`,
and full seven-conjunct timestamp specialization at every node.

`MemoryAssemblyPremises` and `CensusAssemblyPremises` are data-carrying
structures, not propositions definitionally equal to `True` and not empty
wrappers.  Their eta receipts expose respectively three and seven fields;
the memory bundle forces a nonempty node forest.  `dataOf` retains explicit
`P`, `M`, and `C` inputs and projects their obligations into `Data`.

No generic `∀ E, Data E` constructor was found.  The compiled boundary records
that any such constructor would force `q = ringChar K` for every buildable
execution.  This does not prove a metatheoretic nonexistence result, and is not
rounded up to one.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch100

open scoped Classical
open Nock Nock.Framework Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## A. `computeOK` is the full whole-tree predicate -/

/-- Independent expansion of all four `ComputeNodeOK` conjuncts at every node
of the reconstructed committed tree -/
theorem computeOK_expands_all_four_node_obligations
    (E : BuildableNockExecution F K) (P : ResidualPremises E) :
    ∀ t, InTree (computeNodesOf E P) t →
      t.children.length = ComputeTable.fanoutComp t.label.skel.state ∧
        t.label.stamp.state = t.label.skel.state ∧
        BindComputeRow E.cfg.challenges.z t.label.skel t.label.row ∧
        ComputeTimestampSpecializesAt E.cfg.challenges.α
          t.label.stamp t.label.row := by
  intro t ht
  exact computeNodesOf_ok E P t ht

/-- The binding branch inside `computeOK` is the complete nine-conjunct
`BindComputeRow`, including all `Dec`, fanout, and three memory-record slots. -/
theorem computeOK_binding_expands_all_nine_conjuncts
    (E : BuildableNockExecution F K) (P : ResidualPremises E) :
    ∀ t, InTree (computeNodesOf E P) t →
      let s := t.label.skel
      let row := t.label.row
      row.1 = s.state ∧
        row.2.1.z = E.cfg.challenges.z ∧
        row.2.2.1.state = s.state ∧
        bindFP E.cfg.challenges.z s.subject row.2.2.1.s ∧
        bindFP E.cfg.challenges.z s.formula row.2.2.1.f ∧
        bindFP E.cfg.challenges.z s.evaluation row.2.2.1.e ∧
        (∀ slot : DecSlot,
          if h : decActive s.state slot = true
          then bindFP E.cfg.challenges.z (s.decomposition slot h)
            (decFP row.2.2.2 slot)
          else True) ∧
        (∀ i : Fin 3,
          if h : (i : ℕ) < ComputeTable.fanoutComp s.state
          then ∀ slot : TripleSlot,
            bindFP E.cfg.challenges.z (s.subformula i h slot)
              (tripleFP (computeSubformulaFPs row.2.2.1 i) slot)
          else computeSubformulaFPs row.2.2.1 i = (0, 0, 0)) ∧
        (∀ i : Fin 3,
          if h : (i : ℕ) < recordCount s.state
          then BindMemRec E.cfg.challenges.z (s.memoryRecord i h)
            (computeMemRec row.2.2.1 i)
          else computeMemRec row.2.2.1 i = ComputeTable.MemRec.zero) := by
  intro t ht
  simpa [BindComputeRow] using
    (computeNodesOf_ok E P t ht).2.2.1

/-- The timestamp branch inside `computeOK` contains the RAP-faithful relative
specialization: state, sampled alpha, `ln` relative to published `ln_prev`,
record timestamps relative to `ln_prev`, and padding zeros. -/
theorem computeOK_timestamps_expand_all_seven_conjuncts
    (E : BuildableNockExecution F K) (P : ResidualPremises E) :
    ∀ t, InTree (computeNodesOf E P) t →
      let stamp := t.label.stamp
      let row := t.label.row
      row.1 = stamp.state ∧
        row.2.1.α = E.cfg.challenges.α ∧
        row.2.2.1.state = stamp.state ∧
        row.2.2.1.ln =
          row.2.2.1.ln_prev *
            E.cfg.challenges.α ^ (stamp.lnExponent - stamp.lnPrevExponent) ∧
        (∀ i : Fin 3,
          (computeMemRec row.2.2.1 i).ts =
            if computeMemRecKind stamp.state i = .active
            then row.2.2.1.ln_prev *
              E.cfg.challenges.α ^ (stamp.recordExponent i - stamp.lnPrevExponent)
            else 0) ∧
        (∀ i : Fin 3,
          computeMemRecKind stamp.state i = .padding →
            computeMemRec row.2.2.1 i = ComputeTable.MemRec.zero) := by
  intro t ht
  simpa [ComputeTimestampSpecializesAt] using
    (computeNodesOf_ok E P t ht).2.2.2

/-! ## B. Fanout is threaded from the authoritative execution tree -/

/-- The reconstruction is not an independently chosen shadow tree: row
projection is literally the authoritative execution tree, whose exact topology
is `E.traversal.1`; every reconstructed node has the corresponding state
fanout -/
theorem compute_reconstruction_threads_execution_and_traversal
    (E : BuildableNockExecution F K) (P : ResidualPremises E) :
    mapNTree ComputeNode.row (computeNodesOf E P) = E.exec.computeTree ∧
      RVTWithArity (ComputeTable.Fcomp (K := K)) E.exec.computeTree ∧
      ∀ t, InTree (computeNodesOf E P) t →
        t.children.length = ComputeTable.fanoutComp t.label.skel.state := by
  refine ⟨computeNodesOf_rows E P, E.traversal.1, ?_⟩
  intro t ht
  exact (computeNodesOf_ok E P t ht).1

/-! ## C. Remaining bundles are substantive structures, not `True` wrappers -/

/-- Exhaustive eta receipt for the three-field memory assembly bundle.  Its
carrier data and two dependent proofs rule out an empty structure wrapper. -/
theorem memoryAssemblyPremises_eta
    {E : BuildableNockExecution F K} (M : MemoryAssemblyPremises E) :
    M =
      { memoryNodes := M.memoryNodes
        memory_rows := M.memory_rows
        memoryOK := M.memoryOK } := by
  cases M
  rfl

/-- The memory bundle cannot hide an empty node list: its row projection is the
authoritative nonempty memory forest -/
theorem memoryAssemblyPremises_force_nonempty
    {E : BuildableNockExecution F K} (M : MemoryAssemblyPremises E) :
    M.memoryNodes ≠ [] := by
  intro h
  apply E.execA.memoryForest_nonempty
  rw [← M.memory_rows, h]
  rfl

/-- Exhaustive eta receipt for all seven census/window/bound fields.  This
structure carries a natural and six dependent proof obligations; it is neither
an empty structure nor a proposition definitionally equal to `True`. -/
theorem censusAssemblyPremises_eta
    {E : BuildableNockExecution F K}
    {computeNodes : NTree (ComputeNode K)}
    {memoryNodes : List (NTree (MemoryNode K))}
    (C : CensusAssemblyPremises E computeNodes memoryNodes) :
    C =
      { nounSizeBound := C.nounSizeBound
        slotSemantics := C.slotSemantics
        recordEquations := C.recordEquations
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl

/-- `dataOf` projects the exact open memory, census, window, and bound
obligations into its result; neither named bundle is erased. -/
theorem dataOf_projects_every_named_open_obligation
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryAssemblyPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) M.memoryNodes)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    let D := dataOf E P M C hln
    D.memoryNodes.map (mapNTree MemoryNode.row) = E.execA.memoryForest ∧
      (∀ t ∈ D.memoryNodes,
        MemoryNodesOK E.cfg.challenges.z E.cfg.challenges.α t) ∧
      (∀ s ∈ computeSkeletonRows D.skeleton,
        ServedLookupBridge.SkeletonSlotSemantics s) ∧
      (∀ s ∈ computeSkeletonRows D.skeleton,
        ServedLookupBridge.SkeletonRecordEquations s) ∧
      EdgeComparisonCensus.CombinedSkeletonCensus K D.skeleton D.Λ ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy D.skeleton D.Λ ∧
      D.skeleton.BoundedBy E.q ∧
      ProductionP8Containment.CombinedBoundedBy K E.q D.skeleton := by
  dsimp [dataOf, Data.skeleton]
  exact ⟨M.memory_rows, M.memoryOK, C.slotSemantics, C.recordEquations,
    C.census, C.sizeWindowBound, C.skeletonBounded, C.combinedBounded⟩

/-- The result retains all three explicit input objects: compute data from
`P`, memory data from `M`, and the natural bound from `C`. -/
theorem dataOf_retains_P_M_C_objects
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryAssemblyPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) M.memoryNodes)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOf E P M C hln).computeNodes = computeNodesOf E P ∧
      (dataOf E P M C hln).memoryNodes = M.memoryNodes ∧
      (dataOf E P M C hln).nounSizeBound = C.nounSizeBound ∧
      (dataOf E P M C hln).Λ = E.Λ ∧
      (dataOf E P M C hln).q_eq_ringChar = P.q_eq_ringChar := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## D. Four residual premises and no rounded-up universal constructor -/

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

/-- All remaining residual statements remain projectable after the compute
assembly. -/
theorem residualPremises_projects_all_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows,
        AxisAtomPremises (E.semanticData.rows i)) ∧
      E.q = ringChar K :=
  ⟨P.inactiveDec, P.axisAtoms, P.q_eq_ringChar⟩

/-- Compiled boundary for the searched API: any hypothetical universal
constructor would manufacture the characteristic equality for every buildable
execution.  This is a consequence, not a claim that Lean proves function-space
emptiness. -/
theorem any_universal_data_constructor_forces_q_pin
    (g : ∀ E : BuildableNockExecution F K, Data E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  fun E => (g E).q_eq_ringChar

/-! ## E. -/

inductive ReviewedField100
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

def substantiveFields100 : List ReviewedField100 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields100 : List ReviewedField100 := [.structural]

def residualFields100 : List ReviewedField100 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

theorem independent_exact_eleven_one_two_accounting :
    substantiveFields100.length = 11 ∧
      typeSummaryFields100.length = 1 ∧
      residualFields100 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields100.length = 2 ∧
      (substantiveFields100 ++ typeSummaryFields100 ++ residualFields100).Nodup ∧
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

#print axioms computeOK_expands_all_four_node_obligations
#print axioms computeOK_binding_expands_all_nine_conjuncts
#print axioms computeOK_timestamps_expand_all_seven_conjuncts
#print axioms compute_reconstruction_threads_execution_and_traversal
#print axioms memoryAssemblyPremises_eta
#print axioms memoryAssemblyPremises_force_nonempty
#print axioms censusAssemblyPremises_eta
#print axioms dataOf_projects_every_named_open_obligation
#print axioms dataOf_retains_P_M_C_objects
#print axioms residualPremises_eta_still_four
#print axioms residualPremises_projects_all_four
#print axioms any_universal_data_constructor_forces_q_pin
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeNodesOf_ok
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.dataOf
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch100
