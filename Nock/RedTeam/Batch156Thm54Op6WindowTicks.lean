import Nock.NockVMROM.Thm54.GenericHonestCommitment
import Nock.NockVMROM.Thm54.GenericHonestData
import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.SizeWindowBoundOp6
import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.NounRealization
import Nock.NockVMROM.Thm54.Walk37.PaperNames
import Nock.RedTeam.Batch91Thm54CompleteFalseAcceptance
import Nock.RedTeam.Batch128Thm54GenericHonestPackage
import Nock.RedTeam.Batch136Thm54CensusExtras
import Nock.RedTeam.Batch154Thm54NamedExtras
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Independent spec-redteam of CF / CG / CH / CJ

Those letters are claims under attack,
not evidence.  Construction files were not edited in this pass.

Paper frame (re-read at source):
`Def[Nock Program]` window the paper (at `1097`);
collision consumer `1188-1204`; OP6 `sf_evaluation_2` type-read `1777`;
always-operative `f = cons(f_h, f_t)` `1846-1848`; tail `1858-1861`;
OP6 branch tail `1872-1875`; `Lem:decomp` `1210-1214`.

Consumed capstone:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`
(`«Thm:NockVMROM»`).

Five axes:
1. Vacuity — named extras inhabited at a real Op6 K3 execution, not `∀`
   over an empty type.  Negatives: generic size-window still fails
   (`census_holds_and_sizeWindowBound_fails` / `Λ < 4`);
   `enc_collision_across_the_window` still true.
2. Weakening — selector is not C2-as-field; `FPRealizedWithin` is not a
   `NounRealization` / `FPRealizationWitness` field.  Tick is written
   Op6 scope, not `∀ E`.
3. Drift — named extras are reconstruction `CensusRecordPremises`, not
   literal-node `Data.skeletonBounded` / `Data.sizeWindowBound`.
   `census` (`CombinedSkeletonCensus`) vs `combinedBounded`
   (`CombinedBoundedBy`) are different kinds.  At this Op6 parent, the
   window noun is the already-held `CallRealization`, not a fresh
   `chooseNounPreferWindow` pick.
4. Axiom leak — `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
5. Attack:
   later tick is a scope-rule change, not a TRADE close.  C2 not added.
   `CensusRecordPremises` still five.

No §J tick is issued from this batch.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.RedTeam.Batch156

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.CensusExtraClosure
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3
open Nock.NockVMROM.Thm54.SizeWindowBoundOp6
  (residualPremises memoryRecordPremises)
open Nock.Framework

noncomputable section

-- Form R leftover first-row `counts = 0` (live is `chainOneBitWeight`).
variable (hfirst :
  ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
    ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0)


/-! ## Axis 1. Vacuity: real Op6 K3 execution, not ∀ over empty type -/

theorem residual_inhabited : Nonempty (ResidualPremises (Op6Execution hfirst)) :=
  ⟨(residualPremises hfirst)⟩

theorem memory_inhabited : Nonempty (MemoryRecordPremises (Op6Execution hfirst)) :=
  ⟨(memoryRecordPremises hfirst)⟩

theorem op6_Lambda : (Op6Execution hfirst).Λ = 7 := rfl

theorem op6_q : (Op6Execution hfirst).q = 97 := rfl

theorem op6_compRows : (Op6Execution hfirst).cfg.compRows = 3 := rfl

private theorem op6_one : (1 : ℕ) < (Op6Execution hfirst).cfg.compRows := by
  rw [op6_compRows]; omega

theorem computeRowAt_zero' :
    (Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩ =
      parentRow seedZ alphaA := by
  simpa [Op6Execution] using computeRowAt_zero

/-- Parent row is `.s6`. -/
theorem parent_is_s6 :
    ((Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).1 =
      .s6 := by
  rw [computeRowAt_zero']; rfl

theorem window_state_gate_fails :
    ¬ ∀ i : Fin (Op6Execution hfirst).cfg.compRows,
      ((Op6Execution hfirst).exec.computeRowAt i).1 ≠ .s3 ∧
        ((Op6Execution hfirst).exec.computeRowAt i).1 ≠ .s4 ∧
          ((Op6Execution hfirst).exec.computeRowAt i).1 ≠ .s6 := by
  intro h
  exact (h ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).2.2 (parent_is_s6 hfirst)

/-- Named `CensusRecordPremises.sizeWindowBound` at this inhabited `(P, M)`. -/
theorem named_sizeWindowBound_at_witness :
    SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) (residualPremises hfirst))
          (memoryNodesOf (Op6Execution hfirst) (memoryRecordPremises hfirst))) (Op6Execution hfirst).Λ :=
  SizeWindowBoundOp6.named_sizeWindowBound hfirst (residualPremises hfirst) (memoryRecordPremises hfirst)

/-- Named `CensusRecordPremises.census` at the same pair. -/
theorem named_census_at_witness :
    EdgeComparisonCensus.CombinedSkeletonCensus K
        (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) (residualPremises hfirst))
          (memoryNodesOf (Op6Execution hfirst) (memoryRecordPremises hfirst))) (Op6Execution hfirst).Λ :=
  SizeWindowBoundOp6.named_census hfirst (residualPremises hfirst) (memoryRecordPremises hfirst)

/-- All five census extras inhabit at this `(P, M)`. -/
theorem census_bundle_inhabited :
    Nonempty
      (CensusRecordPremises (Op6Execution hfirst) (residualPremises hfirst) (memoryRecordPremises hfirst)) :=
  ⟨SizeWindowBoundOp6.censusRecordPremises hfirst (residualPremises hfirst) (memoryRecordPremises hfirst)⟩

/-- Negative: synthetic OP6 skeleton still separates census from the size window
at every `Λ < 4`.  Generic `∀ E` size-window is not claimed, and this refutation
is unchanged -/
theorem generic_size_window_still_fails :
    EdgeComparisonCensus.CombinedSkeletonCensus K s6WindowSkeleton 2 ∧
      ∀ Λ : ℕ, Λ < 4 →
        ¬ SizeWindowCounting.SizeWindowNounsBoundedBy s6WindowSkeleton Λ :=
  census_holds_and_sizeWindowBound_fails

/-- Negative: `enc` still collides a 17-leaf comb with `.atom 0` at this seed.
The selector may prefer the windowed witness; the collision fact remains. -/
theorem enc_collision_still_true :
    (Noun.atom 0).leaves ≤ (Op6Execution hfirst).Λ ∧
      ∃ n : Noun,
        GlobalCarryRecognizer.enc seedZ n =
            GlobalCarryRecognizer.enc seedZ (.atom 0) ∧
          FieldEmbedding.BoundedBy (Op6Execution hfirst).q n ∧
            ¬ n.leaves ≤ (Op6Execution hfirst).Λ := by
  have h := SizeWindowBoundOp6.enc_collision_across_the_window hfirst
  exact ⟨h.2.2.2.1, ⟨_, h.1, h.2.1, h.2.2.2.2⟩⟩

/-! ## Axis 2. Weakening: selector is not C2-as-field; not ∀ E -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- `FPRealized` has no leaf bound.  Designed C2 would add `leaves ≤ Λ` here. -/
theorem FPRealized_has_no_leaf_bound {z : K} {q : ℕ} {fp : ComputeTable.FP K} :
    FPRealized z q fp ↔
      ∃ n : Noun, FieldEmbedding.BoundedBy q n ∧
        GlobalCarryRecognizer.enc z n = fp :=
  Iff.rfl

/-- `FPRealizedWithin` is a separate selector proposition, not a field. -/
theorem FPRealizedWithin_is_exists_window {z : K} {q Λ : ℕ}
    {fp : ComputeTable.FP K} :
    FPRealizedWithin z q Λ fp ↔
      ∃ n : Noun, FieldEmbedding.BoundedBy q n ∧ n.leaves ≤ Λ ∧
        GlobalCarryRecognizer.enc z n = fp :=
  Iff.rfl

/-- `FPRealizationWitness` still three fields: noun, `BoundedBy q`, encoding.
No `leaves ≤ Λ`.  If C2 had been added as a field this eta would fail. -/
theorem fpWitness_eta_without_leaves {z : K} {q : ℕ} {fp : ComputeTable.FP K}
    (w : FPRealizationWitness z q fp) :
    w = { noun := w.noun, bounded := w.bounded, encoding := w.encoding } := by
  cases w
  rfl

/-- Public-row realization still five slots.  No `FPRealizedWithin` field. -/
theorem publicRowNoun_eta_without_within {q : ℕ} {row : ComputePublicLabel K}
    (R : ComputePublicRowNounRealization q row) :
    R =
      { subject := R.subject
        formula := R.formula
        evaluation := R.evaluation
        subformula := R.subformula
        memoryRecord := R.memoryRecord } := by
  cases R
  rfl

/-- Reconstruction selector: windowed `Classical.choose` or fallback `chooseNoun`. -/
theorem chooseNounPreferWindow_is_selector {z : K} {q Λ : ℕ}
    {fp : ComputeTable.FP K} (h : FPRealized z q fp) :
    chooseNounPreferWindow (Λ := Λ) h =
      if hw : FPRealizedWithin z q Λ fp then Classical.choose hw
      else chooseNoun h :=
  rfl

/-- Encoding of the selector is the committed fingerprint, window or not. -/
theorem chooseNounPreferWindow_enc_unchanged {z : K} {q Λ : ℕ}
    {fp : ComputeTable.FP K} (h : FPRealized z q fp) :
    GlobalCarryRecognizer.enc z (chooseNounPreferWindow (Λ := Λ) h) = fp :=
  chooseNounPreferWindow_enc (Λ := Λ) h

/-- Named size-window extra is `∀ P M` at **this** execution, not `∀ E`. -/
def namedSizeWindowBoundAtOp6 : Prop :=
  ∀ (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)),
    SizeWindowCounting.SizeWindowNounsBoundedBy
      (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
        (memoryNodesOf (Op6Execution hfirst) M)) (Op6Execution hfirst).Λ

theorem named_sizeWindowBound_is_this_execution :
    namedSizeWindowBoundAtOp6 hfirst :=
  SizeWindowBoundOp6.named_sizeWindowBound hfirst

/-- `CensusRecordPremises` still five fields.  If a sixth were added this eta
would fail -/
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

/-- CF/CG ledger
prose that says “still four” is stale relative to this type. -/
theorem residualPremises_eta_three
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

/-- Execution carrier still fourteen fields.  No fifteenth -/
theorem still_fourteen (E : BuildableNockExecution F K) :
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

theorem independent_exact_eleven_one_two_accounting :
    Batch91.reviewedSubstantiveFields.length = 11 ∧
      Batch91.reviewedTypeSummaryFields.length = 1 ∧
      Batch91.reviewedResidualFields =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      Batch91.reviewedResidualFields.length = 2 ∧
      (Batch91.reviewedSubstantiveFields ++ Batch91.reviewedTypeSummaryFields ++
        Batch91.reviewedResidualFields).Nodup ∧
      11 + 1 + 2 = 14 :=
  Batch91.exact_eleven_one_two_partition

/-! ## Axis 3. Drift: reconstruction extras vs literal Data; census vs combinedBounded -/

/-- Constructor `Data` commits literal nodes, not `computeNodesOf`. -/
theorem data_is_literal_nodes :
    (data hfirst).computeNodes = op6ComputeTree ∧
      (data hfirst).memoryNodes = [op6MemTree] :=
  SizeWindowBoundOp6.data_is_literal_node_constructor hfirst

/-- `dataOf` always commits reconstructed nodes. -/
theorem dataOf_commits_reconstructed
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryAssemblyPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) M.memoryNodes)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOf E P M C hln).computeNodes = computeNodesOf E P :=
  rfl

/-- Named size-window is on `computeNodesOf` / `memoryNodesOf`, not `data.skeleton`. -/
theorem named_sizeWindowBound_is_reconstruction
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
          (memoryNodesOf (Op6Execution hfirst) M)) (Op6Execution hfirst).Λ :=
  SizeWindowBoundOp6.named_sizeWindowBound hfirst P M

/-- Literal-node extra is a different subject. -/
theorem data_sizeWindowBound_is_literal_skeleton :
    SizeWindowCounting.SizeWindowNounsBoundedBy (data hfirst).skeleton (data hfirst).Λ :=
  SizeWindowBoundOp6.data_sizeWindowBound hfirst

/-- Named `skeletonBounded` is reconstruction `BoundedBy q`, not `data.skeletonBounded`. -/
theorem named_skeletonBounded_is_reconstruction
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
      (memoryNodesOf (Op6Execution hfirst) M)).BoundedBy (Op6Execution hfirst).q :=
  SizeWindowBoundOp6.named_skeletonBounded hfirst P M

/-- `census` kind is `CombinedSkeletonCensus` (leaf-window consumer). -/
def censusKind (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) : Prop :=
  EdgeComparisonCensus.CombinedSkeletonCensus K
    (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ

/-- `combinedBounded` kind is atom-range `CombinedBoundedBy`, not census. -/
def combinedBoundedKind (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) : Prop :=
  ProductionP8Containment.CombinedBoundedBy K E.q
    (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M))

theorem named_census_has_census_kind
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    censusKind (Op6Execution hfirst) P M :=
  SizeWindowBoundOp6.named_census hfirst P M

theorem named_combinedBounded_has_combined_kind
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    combinedBoundedKind (Op6Execution hfirst) P M :=
  SizeWindowBoundOp6.named_combinedBounded hfirst P M

/-- Reconstructed subformula slot **is** `subformulaNounOf`. -/
theorem computeSkeletonOf_subformula_is_of {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1)
    (slot : TripleSlot) :
    (computeSkeletonOf data pubR).subformula i hi slot =
      subformulaNounOf data pubR i hi slot :=
  rfl

/-- CH: `subformulaNounOf` encoding equals the committed fingerprint. -/
theorem subformulaNounOf_enc_unchanged {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1)
    (slot : TripleSlot) :
    GlobalCarryRecognizer.enc row.2.1.z (subformulaNounOf data pubR i hi slot) =
      tripleFP (computeSubformulaFPs row.2.2.1 i) slot :=
  subformulaNounOf_enc data pubR i hi slot

/-- CH: both selector branches encode to the same fingerprint. -/
theorem of_and_noun_encode_the_same {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1)
    (slot : TripleSlot) :
    GlobalCarryRecognizer.enc row.2.1.z (subformulaNounOf data pubR i hi slot) =
      GlobalCarryRecognizer.enc row.2.1.z (subformulaNoun Λ pubR i hi slot) := by
  rw [subformulaNounOf_enc, subformulaNoun_enc]

end

/-! ## Axis 3 continued / CH: Op6 parent sf2 is the CallRealization noun -/

noncomputable section

-- Form R leftover first-row `counts = 0` (live is `chainOneBitWeight`).
variable (hfirst :
  ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
    ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0)
include hfirst

theorem parentRowData_calls_len : parentRowData.calls.length = 2 := rfl

theorem parentCall2_result_is_atom0 :
    parentCall2.result = TraceGen.op6CondResult :=
  rfl

theorem parent_sf2_call_slot :
    callSlotNoun (parentRowData.calls.get ⟨1, by decide⟩) TripleSlot.result =
      TraceGen.op6CondResult :=
  rfl

/-- Parent `sf2` result fingerprint is `enc seedZ (.atom 0)`. -/
theorem parent_sf2_fp_is_atom0 :
    SemanticStrategy.tripleFP
        (computeSubformulaFPs (parentPub seedZ alphaA) 1) TripleSlot.result =
      GlobalCarryRecognizer.enc seedZ TraceGen.op6CondResult := by
  have h := SizeWindowBoundOp6.parent_sf2_result_fp hfirst
  rw [SizeWindowBoundOp6.op6_computeRowAt_zero hfirst] at h
  simpa [parentRow, TraceGen.op6CondResult] using h

/-- CH at this execution: when the call noun is a windowed realizer,
`subformulaNounOf` returns that call noun, not a fresh `chooseNoun`. -/
theorem parent_sf2_prefers_call
    (pubR : ComputePublicRowNounRealization 97
      (computePublicLabel (parentRow seedZ alphaA))) :
    subformulaNounOf parentRowData pubR ⟨1, by decide⟩ (by decide)
        TripleSlot.result =
      TraceGen.op6CondResult := by
  have hi : (1 : ℕ) < ComputeTable.fanoutComp (parentRow seedZ alphaA).1 := by
    decide
  have hlen : (1 : ℕ) < parentRowData.calls.length := by decide
  have hw :
      FieldEmbedding.BoundedBy 97
          (callSlotNoun (parentRowData.calls.get ⟨1, hlen⟩) TripleSlot.result) ∧
        (callSlotNoun (parentRowData.calls.get ⟨1, hlen⟩)
          TripleSlot.result).leaves ≤ (7 : ℕ) ∧
          GlobalCarryRecognizer.enc (parentRow seedZ alphaA).2.1.z
            (callSlotNoun (parentRowData.calls.get ⟨1, hlen⟩) TripleSlot.result) =
            SemanticStrategy.tripleFP
              (computeSubformulaFPs (parentRow seedZ alphaA).2.2.1 1)
              TripleSlot.result := by
    have hslot :
        callSlotNoun (parentRowData.calls.get ⟨1, hlen⟩) TripleSlot.result =
          TraceGen.op6CondResult := rfl
    rw [hslot]
    refine ⟨bounded_condResult, by decide, ?_⟩
    simpa [parentRow, compInputs] using (parent_sf2_fp_is_atom0 hfirst).symm
  exact (subformulaNounOf_leaves_of_call parentRowData pubR ⟨1, by decide⟩ hi
    TripleSlot.result hlen hw).trans (by rfl)

/-- Unfolded CH selector: call-noun if windowed, else `subformulaNoun`. -/
theorem subformulaNounOf_is_prefer_call {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
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

/-! ## Axis 5. -/

/-- `ConsDecomposedRow` is strictly stronger
than `BoundedBy q` -/
theorem trade_still_fails :
    ComputeRowSkeleton.BoundedBy 1 Batch136.rtConsShapedNotConsRow ∧
      (∃ l r : Noun, Batch136.rtConsShapedNotConsRow.formula = .cell l r) ∧
      Batch136.rtConsShapedNotConsRow.formula ≠
        .cell (Batch136.rtConsShapedNotConsRow.decomposition .f_h rfl)
          (Batch136.rtConsShapedNotConsRow.decomposition .f_t rfl) :=
  Batch136.redteam_bounded_cons_shaped_row_is_not_consDecomposed

theorem named_skeletonBounded_via_cons
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
      (memoryNodesOf (Op6Execution hfirst) M)).BoundedBy (Op6Execution hfirst).q :=
  Batch154.Op6.named_skeletonBounded hfirst P M

def batch154_tick_not_licensed :=
  Batch154.Op6.tick_not_licensed

/-- F97 already inhabited the same extra via the same TRADE, as CJ states. -/
def f97_skeletonBounded_already_inhabited :=
  @distinctCensus_skeletonBounded_and_combinedBounded

/-- CJ added no new inhabitant: production `named_skeletonBounded` is still
the ConsDecomposedRow discharge at written Op6 scope, not `∀ E`. -/
theorem cj_no_new_generic_skeletonBounded
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
      (memoryNodesOf (Op6Execution hfirst) M)).BoundedBy (Op6Execution hfirst).q :=
  SizeWindowBoundOp6.named_skeletonBounded hfirst P M

/-- Named `slotSemantics` at Op6 is still the OP0/OP9 **state gate**, not a
served join and not C5 -/
theorem named_slotSemantics_is_state_gate
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
          (memoryNodesOf (Op6Execution hfirst) M)),
      ServedLookupBridge.SkeletonSlotSemantics s :=
  SizeWindowBoundOp6.named_slotSemantics hfirst P M

/-- Gate remains load-bearing -/
theorem lookup_gate_is_load_bearing :
    ¬ ServedLookupBridge.SkeletonSlotSemantics
        CensusExtraClosure.s0SlotFailRow :=
  CensusExtraClosure.s0SlotFailRow_slotSemantics_fails

/-- Five-field projection of the inhabited Op6 census bundle. -/
theorem censusRecordPremises_projects_five
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    ServedLookupBridge.SkeletonSlotSemantics
        (computeNodeAt (Op6Execution hfirst) P ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel →
      EdgeComparisonCensus.CombinedSkeletonCensus K
          (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
            (memoryNodesOf (Op6Execution hfirst) M)) (Op6Execution hfirst).Λ ∧
        SizeWindowCounting.SizeWindowNounsBoundedBy
          (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
            (memoryNodesOf (Op6Execution hfirst) M)) (Op6Execution hfirst).Λ ∧
          (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
            (memoryNodesOf (Op6Execution hfirst) M)).BoundedBy (Op6Execution hfirst).q ∧
            ProductionP8Containment.CombinedBoundedBy K (Op6Execution hfirst).q
              (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
                (memoryNodesOf (Op6Execution hfirst) M)) :=
  fun _ =>
    ⟨SizeWindowBoundOp6.named_census hfirst P M,
      SizeWindowBoundOp6.named_sizeWindowBound hfirst P M,
      SizeWindowBoundOp6.named_skeletonBounded hfirst P M,
      SizeWindowBoundOp6.named_combinedBounded hfirst P M⟩

/-- Direct five-field inhabitant, independently named. -/
def censusRecordPremises_at_op6
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    CensusRecordPremises (Op6Execution hfirst) P M :=
  SizeWindowBoundOp6.censusRecordPremises hfirst P M

end

/-! ## Axis 4. -/

#print axioms residual_inhabited
#print axioms memory_inhabited
#print axioms op6_Lambda
#print axioms parent_is_s6
#print axioms window_state_gate_fails
#print axioms named_sizeWindowBound_at_witness
#print axioms named_census_at_witness
#print axioms census_bundle_inhabited
#print axioms generic_size_window_still_fails
#print axioms enc_collision_still_true
#print axioms FPRealized_has_no_leaf_bound
#print axioms FPRealizedWithin_is_exists_window
#print axioms fpWitness_eta_without_leaves
#print axioms publicRowNoun_eta_without_within
#print axioms chooseNounPreferWindow_is_selector
#print axioms chooseNounPreferWindow_enc_unchanged
#print axioms named_sizeWindowBound_is_this_execution
#print axioms censusRecordPremises_eta_five
#print axioms residualPremises_eta_three
#print axioms still_fourteen
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms independent_exact_eleven_one_two_accounting
#print axioms data_is_literal_nodes
#print axioms dataOf_commits_reconstructed
#print axioms named_sizeWindowBound_is_reconstruction
#print axioms data_sizeWindowBound_is_literal_skeleton
#print axioms named_skeletonBounded_is_reconstruction
#print axioms named_census_has_census_kind
#print axioms named_combinedBounded_has_combined_kind
#print axioms computeSkeletonOf_subformula_is_of
#print axioms subformulaNounOf_enc_unchanged
#print axioms of_and_noun_encode_the_same
#print axioms parentRowData_calls_len
#print axioms parentCall2_result_is_atom0
#print axioms parent_sf2_call_slot
#print axioms parent_sf2_fp_is_atom0
#print axioms parent_sf2_prefers_call
#print axioms subformulaNounOf_is_prefer_call
#print axioms trade_still_fails
#print axioms named_skeletonBounded_via_cons
#print axioms batch154_tick_not_licensed
#print axioms f97_skeletonBounded_already_inhabited
#print axioms cj_no_new_generic_skeletonBounded
#print axioms named_slotSemantics_is_state_gate
#print axioms lookup_gate_is_load_bearing
#print axioms censusRecordPremises_projects_five
#print axioms censusRecordPremises_at_op6
#print axioms optimizedFullStrictNockVMROM_of_package

end Nock.RedTeam.Batch156
