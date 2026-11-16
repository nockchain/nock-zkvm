import Nock.NockVMROM.Thm54
import Nock.NockVMROM.Thm54.Walk37.PaperNames
import Nock.RedTeam.Batch91Thm54CompleteFalseAcceptance
import Nock.RedTeam.Batch128Thm54GenericHonestPackage
import Nock.RedTeam.Batch154Thm54NamedExtras
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Independent spec-redteam of CI / CH

Construction
files were not edited in this pass. Capstone untouched. No C5 as a
`BuildableNockExecution` field. No C2 field. No BFS edits.

Paper frame (re-read at source):
slot operator the paper; NMR `1328`; served-memory coverage
`1398-1431`; OP9 arm fetch `1736-1738`.

Consumed capstone:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`
(`«Thm:NockVMROM»`).

Five axes:
1. Vacuity — named extra over `computeNodesOf` at a real OP9 row, not an
   empty type. Negatives: Op6 `named_slotSemantics` is the state gate
   (no `.s0` / `.s9`); served-join subject is literal `Op9Skeleton.parentRow`
.
2. Weakening — prefer-call is a selector, not uniqueness; `enc_collision`
   still true; slot identification is `Noun.slot`, not `needs.served` length.
4. Axiom leak — `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.RedTeam.Batch157

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.CensusExtraClosure
open Nock.NockVMROM.Thm54.P8Census
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.SlotSemanticsOp9
open Nock.NockVMROM.Thm54.TraceGen
  (op9CoreNoun op9Arm op9_slot)
open Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3
  (Op9Execution parentRowData seedZ alphaA exec cfg)
open Nock.NockVMROM.Thm54.TraceGen.Op9Skeleton (parentRow)
open Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3 (Op6Execution)
open Nock.RedTeam.Batch91

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

-- Form R leftover first-row `counts = 0` (live is `chainOneBitWeight`).
variable (hfirst :
  ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
    ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0)
variable (hfirst6 :
  ((TraceGen.Op6ConfigK3.exec TraceGen.Op6ConfigK3.seedZ TraceGen.Op6ConfigK3.alphaA).memoryPubAt
      ⟨0, by norm_num [TraceGen.Op6ConfigK3.cfg]⟩).pt.counts = 0 ∧
    ((TraceGen.Op6ConfigK3.exec TraceGen.Op6ConfigK3.seedZ TraceGen.Op6ConfigK3.alphaA).memoryPubAt
      ⟨0, by norm_num [TraceGen.Op6ConfigK3.cfg]⟩).pt.indicator = 0)


/-! ## Axis 5. Layer pins (no C5 field; census still five) -/

/-- `BuildableNockExecution` eta has no `ExactExecutionLocalCertificates`
and no C2 `FPRealizedWithin` field -/
theorem execution_eta_lacks_C5
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
        memoryIOCapacity := E.memoryIOCapacity } :=
  E.eta_with_memoryTrace

theorem censusRecordPremises_eta_five
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

theorem residualPremises_eta_three
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

theorem memoryRecordPremises_eta_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } := by
  cases M
  rfl

theorem eleven_one_two : 11 + 1 + 2 = 14 :=
  GenericHonestPackage.residual_pair_still_eleven_one_two

theorem eleven_one_two_is_batch91 :
    reviewedSubstantiveFields.length = 11 ∧
      reviewedTypeSummaryFields.length = 1 ∧
      reviewedResidualFields.length = 2 :=
  ⟨Batch91.exact_eleven_one_two_partition.1,
    Batch91.exact_eleven_one_two_partition.2.1,
    Batch91.exact_eleven_one_two_partition.2.2.2.1⟩

/-! ## Axis 2 / CH. Prefer-call is a selector, not uniqueness -/

/-- CH: reconstruction subformula slots are `subformulaNounOf`. -/
theorem computeSkeletonOf_subformula_is_prefer_call
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) :
    (computeSkeletonOf data pubR).subformula =
      fun i hi slot => subformulaNounOf data pubR i hi slot :=
  rfl

/-- CH: the selector is an if-then on a windowed `CallRealization`, else
`subformulaNoun`. Not a uniqueness theorem. -/
theorem subformulaNounOf_is_selector
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1)
    (slot : TripleSlot) :
    subformulaNounOf data pubR i hi slot =
      if hlen : (i : ℕ) < data.calls.length then
        if hw : FieldEmbedding.BoundedBy q
            (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot) ∧
              (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot).leaves ≤ Λ ∧
                GlobalCarryRecognizer.enc row.2.1.z
                  (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot) =
                  tripleFP (computeSubformulaFPs row.2.2.1 i) slot then
          callSlotNoun (data.calls.get ⟨i, hlen⟩) slot
        else
          subformulaNoun Λ pubR i hi slot
      else
        subformulaNoun Λ pubR i hi slot :=
  rfl

/-- Windowed call nouns are selected, not uniquely forced. -/
theorem prefer_call_selects_the_call_noun
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1)
    (slot : TripleSlot)
    (hlen : (i : ℕ) < data.calls.length)
    (hw : FieldEmbedding.BoundedBy q (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot) ∧
      (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot).leaves ≤ Λ ∧
        GlobalCarryRecognizer.enc row.2.1.z
          (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot) =
          tripleFP (computeSubformulaFPs row.2.2.1 i) slot) :
    subformulaNounOf data pubR i hi slot =
      callSlotNoun (data.calls.get ⟨i, hlen⟩) slot :=
  subformulaNounOf_leaves_of_call data pubR i hi slot hlen hw

/-- Uniqueness of realizing nouns still takes `SepSeed`. Prefer-call does
not delete that hypothesis -/
def uniqueness_still_needs_SepSeed :=
  @uniqueness_requires_SepSeed

/-- `enc` still collides across the window: `chooseNoun` is unpinned. -/
def enc_collision_still_true :=
  Batch154.Op6.enc_collision_blocks_named_window

/-- Slot identification is `Noun.slot`, not `needs.served` length. -/
theorem op9_arm_fetch_is_noun_slot :
    Noun.slot 2 op9CoreNoun = some op9Arm :=
  op9_slot

theorem skeletonSlotSemantics_s9_is_noun_slot
    {s : ComputeRowSkeleton} (h : SkeletonSlotSemantics s)
    (hs9 : s.state = .s9) :
    Noun.slot (skeletonMemoryAxis s 2)
      (skeletonSubformula s 0 .result) =
        some (skeletonSubformula s 1 .formula) :=
  h.s9_slot hs9

/-! ## Axis 1. Vacuity: named extra at a real OP9 reconstruction -/

theorem op9_compRows : (Op9Execution hfirst).cfg.compRows = 3 := rfl

theorem op9_Lambda : (Op9Execution hfirst).Λ = 7 := rfl

theorem op9_fin_val (i : Fin (Op9Execution hfirst).cfg.compRows) :
    (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 := by
  have hi : (i : ℕ) < 3 := by
    have hrows := op9_compRows hfirst
    have := i.isLt
    omega
  omega

private theorem op9_one : (1 : ℕ) < (Op9Execution hfirst).cfg.compRows := by
  rw [op9_compRows hfirst]; omega

private theorem op9_two : (2 : ℕ) < (Op9Execution hfirst).cfg.compRows := by
  rw [op9_compRows hfirst]; omega

/-- S0: `(P, M)` inhabited, so the named type is not `∀` over empty. -/
theorem residual_inhabited : Nonempty (ResidualPremises (Op9Execution hfirst)) :=
  ⟨(residualPremises hfirst)⟩

theorem memory_inhabited : Nonempty (MemoryRecordPremises (Op9Execution hfirst)) :=
  ⟨(memoryRecordPremises hfirst)⟩

/-- Parent compute row is `.s9` -/
theorem parent_is_s9_independent :
    ((Op9Execution hfirst).exec.computeRowAt ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).1 =
      ComputeTable.State.s9 :=
  parent_is_s9 hfirst

theorem lookup_state_gate_fails_independent :
    ¬ ∀ i : Fin (Op9Execution hfirst).cfg.compRows,
      ((Op9Execution hfirst).exec.computeRowAt i).1 ≠ ComputeTable.State.s0 ∧
        ((Op9Execution hfirst).exec.computeRowAt i).1 ≠ ComputeTable.State.s9 :=
  lookup_state_gate_fails hfirst

/-- Named extra type: reconstruction rows, not a free skeleton. -/
def namedSlotSemanticsType (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E) : Prop :=
  ∀ s ∈ computeSkeletonRows
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
    SkeletonSlotSemantics s

theorem named_extra_is_census_slotSemantics_field
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    namedSlotSemanticsType E P M :=
  C.slotSemantics

/-- Reconstruction subformula of the parent is `subformulaNounOf`. -/
theorem reconstructed_parent_subformula_is_prefer_call
    (P : ResidualPremises (Op9Execution hfirst))
    (i : Fin 3)
    (hi : (i : ℕ) < ComputeTable.fanoutComp
      ((Op9Execution hfirst).exec.computeRowAt ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).1)
    (slot : TripleSlot) :
    (computeNodeAt (Op9Execution hfirst) P
        ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel.subformula i hi slot =
      subformulaNounOf
        ((Op9Execution hfirst).semanticData.rows ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩)
        (publicRowNoun_of_execution (Op9Execution hfirst)
          ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩)
        i hi slot :=
  rfl

/-- CH instance at this row: prefer-call pins sf0 result to `op9CoreNoun`. -/
theorem reconstructed_sf0_is_op9CoreNoun
    (P : ResidualPremises (Op9Execution hfirst)) :
    skeletonSubformula
        (computeNodeAt (Op9Execution hfirst) P ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel
        0 .result = op9CoreNoun :=
  reconstructed_sf0_result hfirst P

theorem reconstructed_sf1_is_op9Arm
    (P : ResidualPremises (Op9Execution hfirst)) :
    skeletonSubformula
        (computeNodeAt (Op9Execution hfirst) P ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel
        1 .formula = op9Arm :=
  reconstructed_sf1_formula hfirst P

theorem reconstructed_mr3_is_two
    (P : ResidualPremises (Op9Execution hfirst)) :
    skeletonMemoryAxis
        (computeNodeAt (Op9Execution hfirst) P ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel
        2 = 2 :=
  reconstructed_mr3_axis hfirst P

/-- Independently assembled parent `s9_slot`: pins then `op9_slot`.
This is the load-bearing OP9 half, not the state gate. -/
theorem reconstructed_parent_s9_slot
    (P : ResidualPremises (Op9Execution hfirst)) :
    Noun.slot
        (skeletonMemoryAxis
          (computeNodeAt (Op9Execution hfirst) P ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel
          2)
        (skeletonSubformula
          (computeNodeAt (Op9Execution hfirst) P ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel
          0 .result) =
      some
        (skeletonSubformula
          (computeNodeAt (Op9Execution hfirst) P ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel
          1 .formula) := by
  rw [reconstructed_sf0_is_op9CoreNoun, reconstructed_sf1_is_op9Arm,
    reconstructed_mr3_is_two]
  exact op9_slot

/-- Named `CensusRecordPremises.slotSemantics` at this reconstruction,
assembled independently from `reconstructed_rows_are_nodes`, the parent
pins, and vacuous `.s1` children. Not `exact named_slotSemantics`. -/
theorem named_slotSemantics_independent
    (P : ResidualPremises (Op9Execution hfirst)) (M : MemoryRecordPremises (Op9Execution hfirst)) :
    namedSlotSemanticsType (Op9Execution hfirst) P M := by
  intro s hs
  obtain ⟨i, rfl⟩ := reconstructed_rows_are_nodes (Op9Execution hfirst) P M hs
  rcases op9_fin_val hfirst i with h0 | h1 | h2
  · have : i = ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩ := Fin.ext h0
    subst this
    refine
      { s0_slot := fun hs0 => by
          have hst := reconstructed_parent_state hfirst P
          exact absurd (hs0.symm.trans hst) (by decide)
        s9_slot := fun _ => reconstructed_parent_s9_slot hfirst P }
  · have : i = ⟨1, op9_one hfirst⟩ := Fin.ext h1
    subst this
    refine
      { s0_slot := fun hs0 => by
          have hst := reconstructed_child1_state hfirst P
          exact absurd (hs0.symm.trans hst) (by decide)
        s9_slot := fun hs9 => by
          have hst := reconstructed_child1_state hfirst P
          exact absurd (hs9.symm.trans hst) (by decide) }
  · have : i = ⟨2, op9_two hfirst⟩ := Fin.ext h2
    subst this
    refine
      { s0_slot := fun hs0 => by
          have hst := reconstructed_child2_state hfirst P
          exact absurd (hs0.symm.trans hst) (by decide)
        s9_slot := fun hs9 => by
          have hst := reconstructed_child2_state hfirst P
          exact absurd (hs9.symm.trans hst) (by decide) }

theorem named_extra_inhabited :
    namedSlotSemanticsType (Op9Execution hfirst) (residualPremises hfirst) (memoryRecordPremises hfirst) :=
  named_slotSemantics_independent hfirst (residualPremises hfirst) (memoryRecordPremises hfirst)

/-! ## Axis 1 negatives: Op6 state gate; served join is literal parentRow -/

/-- No `.s9` row -/
def op6_named_slotSemantics_is_state_gate :=
  @Batch154.Op6.named_slotSemantics_is_state_gate

/-- Op6 parent is `.s6`, not `.s9`. The Op6 extra is a different extra. -/
theorem op6_parent_is_s6 :
    ((Op6Execution hfirst6).exec.computeRowAt ⟨0, (Op6Execution hfirst6).cfg.compRows_pos⟩).1 =
      ComputeTable.State.s6 :=
  Batch154.Op6.parent_is_s6 hfirst6

theorem op6_parent_ne_s9 :
    ((Op6Execution hfirst6).exec.computeRowAt ⟨0, (Op6Execution hfirst6).cfg.compRows_pos⟩).1 ≠
      ComputeTable.State.s9 := by
  intro hs9
  exact absurd ((op6_parent_is_s6 hfirst6).symm.trans hs9) (by decide)

/-- Gate is load-bearing: OP0 failure still compiled. -/
theorem lookup_gate_is_load_bearing :
    ¬ SkeletonSlotSemantics CensusExtraClosure.s0SlotFailRow :=
  CensusExtraClosure.s0SlotFailRow_slotSemantics_fails

/-- Served-join conclusion : `SkeletonSlotSemantics` of the
**literal** `Op9Skeleton.parentRow`. Not `computeNodesOf`. -/
theorem served_join_subject_is_literal_parentRow :
    parentRow = Nock.NockVMROM.Thm54.TraceGen.Op9Skeleton.parentRow :=
  rfl

theorem served_join_inhabits_literal_parentRow :
    SkeletonSlotSemantics parentRow :=
  Batch154.Op9.parent_skeletonSlotSemantics_from_service_served

/-- Literal parentRow sf0 is a match, not `subformulaNounOf`. -/
theorem literal_parent_sf0_is_match :
    skeletonSubformula parentRow 0 .result = op9CoreNoun :=
  Batch154.Op9.parent_sf0_result

/-- Two different propositions: reconstructed `∀` extra vs one-row
literal join -/
theorem reconstruction_extra_and_literal_join_are_distinct_types
    (P : ResidualPremises (Op9Execution hfirst)) (M : MemoryRecordPremises (Op9Execution hfirst)) :
    namedSlotSemanticsType (Op9Execution hfirst) P M ∧
      SkeletonSlotSemantics parentRow :=
  ⟨named_slotSemantics_independent hfirst P M,
    served_join_inhabits_literal_parentRow⟩

/-- `dataOf` always commits reconstructed nodes -/
theorem dataOf_commits_reconstructed
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryAssemblyPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) M.memoryNodes)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOf E P M C hln).computeNodes = computeNodesOf E P :=
  rfl

/-- Literal-node `Data` at this fixture is the constructor tree, not
`computeNodesOf`. -/
theorem data_computeNodes_is_literal_constructor :
    (TraceGen.Op9ConfigK3.data hfirst).computeNodes =
      TraceGen.Op9ConfigK3.op9ComputeTree :=
  rfl

/-- OP0 reconstruction extra is not claimed: the OP0 gate witness still fails. -/
theorem op0_half_not_claimed :
    ¬ SkeletonSlotSemantics CensusExtraClosure.s0SlotFailRow ∧
      CensusExtraClosure.s0SlotFailRow.state = ComputeTable.State.s0 :=
  ⟨lookup_gate_is_load_bearing, rfl⟩

/-- Production named extra, cited as the CI object under attack. -/
def production_named_slotSemantics :=
  @SlotSemanticsOp9.named_slotSemantics

theorem tick_not_licensed :
    named_slotSemantics_independent hfirst (residualPremises hfirst) (memoryRecordPremises hfirst) =
      named_slotSemantics_independent hfirst (residualPremises hfirst) (memoryRecordPremises hfirst) ∧
        ¬ False :=
  ⟨rfl, not_false⟩

/-! ## Axis 5 continued. -/

variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]
variable [Fintype F] [DecidableEq F]

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  Batch128.consumed_capstone_and_alias_remain_frozen_batch128 P hax hbasis hwidth

end

#print axioms execution_eta_lacks_C5
#print axioms censusRecordPremises_eta_five
#print axioms residualPremises_eta_three
#print axioms memoryRecordPremises_eta_two
#print axioms eleven_one_two
#print axioms eleven_one_two_is_batch91
#print axioms computeSkeletonOf_subformula_is_prefer_call
#print axioms subformulaNounOf_is_selector
#print axioms prefer_call_selects_the_call_noun
#print axioms uniqueness_still_needs_SepSeed
#print axioms enc_collision_still_true
#print axioms op9_arm_fetch_is_noun_slot
#print axioms skeletonSlotSemantics_s9_is_noun_slot
#print axioms residual_inhabited
#print axioms memory_inhabited
#print axioms parent_is_s9_independent
#print axioms lookup_state_gate_fails_independent
#print axioms named_extra_is_census_slotSemantics_field
#print axioms reconstructed_parent_subformula_is_prefer_call
#print axioms reconstructed_sf0_is_op9CoreNoun
#print axioms reconstructed_sf1_is_op9Arm
#print axioms reconstructed_mr3_is_two
#print axioms reconstructed_parent_s9_slot
#print axioms named_slotSemantics_independent
#print axioms named_extra_inhabited
#print axioms op6_named_slotSemantics_is_state_gate
#print axioms op6_parent_is_s6
#print axioms op6_parent_ne_s9
#print axioms lookup_gate_is_load_bearing
#print axioms served_join_subject_is_literal_parentRow
#print axioms served_join_inhabits_literal_parentRow
#print axioms literal_parent_sf0_is_match
#print axioms reconstruction_extra_and_literal_join_are_distinct_types
#print axioms dataOf_commits_reconstructed
#print axioms data_computeNodes_is_literal_constructor
#print axioms op0_half_not_claimed
#print axioms production_named_slotSemantics
#print axioms tick_not_licensed
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms optimizedFullStrictNockVMROM_of_package

end Nock.RedTeam.Batch157
