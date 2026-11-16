import Nock.NockVMROM.Thm54.AxisAtomsOp9
import Nock.NockVMROM.Thm54.Op9Statement
import Nock.NockVMROM.Thm54.SemanticIntermediatePreimage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
import Nock.RedTeam.Batch91Thm54CompleteFalseAcceptance
import Nock.RedTeam.Batch128Thm54GenericHonestPackage
import Nock.RedTeam.Batch130Thm54GenericHonestPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Independent spec-redteam of CK (designed C5 at Op9; named `axisAtoms`)

Construction files were not edited in this pass.  Paper
`V_comp` OP0/OP9 axis lines and NMR were re-read at source.

Paper frame (re-read at source):
OP0 formula-tail as NMR address.  OP9 `ln = ln_prev · z³`
is `1737`; `mem_axis_3 = formula_tail_head` is `1738`.  NMR address space
`A := axis_root(child) ∈ F`.  Appendix `.leaf` cells:
OP0 `1866` (gate `1864`), OP9 `1881` (gate `1879`).

Consumed capstone:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`
(`«Thm:NockVMROM»`).

Five axes:
1. Vacuity — C5 is a `Type` inhabitant (`ExactExecutionLocalCertificates`)
   on execution-layer `Op9Execution.semanticData`, not a `Prop`-only shadow.
   Negative: generic `E` still needs the `axisAtoms` extra; C5 is not a
   field of `E`.
Tick is written-scope Op9; `axisAtoms` remains
   a `ResidualPremises` field.  Compiled distinction: C1-style license is
   an implication *from* the designed object; `named_axisAtoms` has no C5
   binder and is the fixture-free residual projection.
3. Drift — `LocalOpcodeCertificate.s9` is on row data, not the reconstructed
   skeleton; `castRowData` transports parent/child certificates;
   `residualPremises_kinds` is the three-tuple after `firstLine` left.
4. Axiom leak — `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
5. Wrong layer — not a fifteenth field; not statement-layer
   `op9ParentCertificate_nonempty`; not `∀ E`; `11+1+2` unchanged.

No tick.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch158

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.TraceGen
  (op9AxisAtom)
open Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3
open Nock.Framework

noncomputable section

-- Form R leftover first-row `counts = 0` (live is `chainOneBitWeight`).
variable (hfirst :
  ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
    ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0)


private theorem one_lt_op9 : (1 : ℕ) < (Op9Execution hfirst).cfg.compRows := by
  change 1 < 3
  decide

private theorem two_lt_op9 : (2 : ℕ) < (Op9Execution hfirst).cfg.compRows := by
  change 2 < 3
  decide

/-! ## Axis 1. Vacuity: C5 is a real Type on execution-layer row data -/

/-- C5 is a `Type`, not a `Prop`.  `AxisAtomPremises` is a `Prop`. -/
def c5_is_Type : Type :=
  ExactExecutionLocalCertificates (Op9Execution hfirst).semanticData

def extra_is_Prop : Prop :=
  ∀ i : Fin (Op9Execution hfirst).cfg.compRows,
    AxisAtomPremises ((Op9Execution hfirst).semanticData.rows i)

/-- Designed C5 inhabitant: parent `.s9` + two `.s1` certificates on
    `(Op9Execution hfirst).semanticData`.  Not `Nonempty`-only -/
def c5_inhabitant : c5_is_Type hfirst :=
  AxisAtomsOp9.localCertificates hfirst

theorem c5_nonempty :
    Nonempty (ExactExecutionLocalCertificates (Op9Execution hfirst).semanticData) :=
  AxisAtomsOp9.localCertificates_nonempty hfirst

/-- Parent certificate is on execution-layer `parentRowData`, not a
    reconstructed `ComputeRowSkeleton` -/
def parent_certificate_on_row_data : LocalOpcodeCertificate 97 7 parentRowData :=
  AxisAtomsOp9.parentCertificate

theorem parent_row_is_s9 : (parentRow seedZ alphaA).1 = .s9 := rfl

theorem child1_row_is_s1 : (child1Row seedZ alphaA).1 = .s1 := rfl

theorem child2_row_is_s1 : (child2Row seedZ alphaA).1 = .s1 := rfl

theorem op9_compRows : (Op9Execution hfirst).cfg.compRows = 3 := rfl

/-- Each canonical compute row carries a `LocalOpcodeCertificate` (Type). -/
theorem c5_row_zero_inhabited :
    Nonempty (LocalOpcodeCertificate 97 7
      ((Op9Execution hfirst).semanticData.rows ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩)) :=
  ⟨(AxisAtomsOp9.localCertificates hfirst).rows ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩⟩

theorem c5_row_one_inhabited :
    Nonempty (LocalOpcodeCertificate 97 7
      ((Op9Execution hfirst).semanticData.rows ⟨1, one_lt_op9 hfirst⟩)) :=
  ⟨(AxisAtomsOp9.localCertificates hfirst).rows ⟨1, one_lt_op9 hfirst⟩⟩

theorem c5_row_two_inhabited :
    Nonempty (LocalOpcodeCertificate 97 7
      ((Op9Execution hfirst).semanticData.rows ⟨2, two_lt_op9 hfirst⟩)) :=
  ⟨(AxisAtomsOp9.localCertificates hfirst).rows ⟨2, two_lt_op9 hfirst⟩⟩

/-- Axis atom at this fixture is `2`.  Paper OP9 `mem_axis_3 = formula_tail_head`, not the `ln` check at `1737`. -/
theorem op9AxisAtom_is_atom_two : op9AxisAtom = .atom 2 := rfl

/-- Noun-shape extra at the parent row data: `decompNoun.f_th` is an atom.
    This is `AxisAtomPremises`, not `ComparisonListed` -/
theorem parent_f_th_is_atom_two :
    decompNoun parentRowData .f_th = .atom 2 :=
  SlotSemanticsOp9.parent_decomp_f_th.trans op9AxisAtom_is_atom_two

/-- C5's s9 axis field is `ComparisonListed` (census membership), not
    `AxisAtomPremises` (noun constructor equality) -/
theorem parent_axis_is_comparison_listed :
    ComparisonListed parentRowData .axisAtom op9AxisAtom (.atom 2) := by
  simp [ComparisonListed, parentRowData, parentComparisons, op9AxisAtom]

theorem axisAtomPremises_expands
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) :
    AxisAtomPremises data =
      ((row.1 = .s0 → ∃ k, data.root.tail = Noun.atom k) ∧
        (row.1 = .s9 → ∃ k, decompNoun data .f_th = Noun.atom k)) :=
  rfl

theorem comparisonListed_is_membership
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (role : ComparisonRole) (left right : Noun) :
    ComparisonListed data role left right =
      ({ role := role, left := left, right := right } ∈ data.comparisons) :=
  rfl

/-! ## Axis 1 negative: generic `E` still needs the extra; C5 not a field -/

variable {F' K' : Type} [Field F'] [Field K'] [Algebra F' K']
variable [FiniteDimensional F' K'] [Fintype K'] [DecidableEq K']
variable [CharP K' (ringChar K')]
variable [Fintype F'] [DecidableEq F']

theorem execution_eta_lacks_c5 (E : BuildableNockExecution F' K') :
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

/-- `bindComputeRow_of_axisAtoms` still takes `AxisAtomPremises`, not C5. -/
def bindComputeRow_still_takes_axisAtoms :=
  @bindComputeRow_of_axisAtoms

/-- `dataOf` still consumes `P.axisAtoms`.  Not recovered from `Data`. -/
theorem dataOf_still_consumes_axisAtoms
    (E : BuildableNockExecution F' K') (P : ResidualPremises E)
    (M : MemoryAssemblyPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) M.memoryNodes)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOf E P M C hln).q_eq_ringChar = P.q_eq_ringChar ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) :=
  Batch130.dataOf_consumes_axisAtoms_independent E P M C hln

theorem data_has_q_eq_but_not_axisAtoms
    {E : BuildableNockExecution F' K'} (D : Data E) :
    E.q = ringChar K' :=
  Batch130.data_carries_q_eq_only_independent D

/-- `Vcomp` OP9 puts `f_th.leaf` in `mr3.axis` — a field element, not noun shape. -/
def vcomp_s9_axis_is_field_element :=
  @Batch130.vcomp_s9_mr3_axis_is_field_element

/-! ## Extra from C5 vs residual projection -/

/-- Three-field eta: `axisAtoms` remains a `ResidualPremises` field.
    If it had left the structure this would not compile -/
theorem residualPremises_eta_three
    {E : BuildableNockExecution F' K'} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

theorem residualPremises_still_projects_axisAtoms
    {E : BuildableNockExecution F' K'} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K' :=
  residualPremises_still_three P

/-- No C5 binder. -/
def fixture_free_extra : extra_is_Prop hfirst :=
  (SlotSemanticsOp9.residualPremises hfirst).axisAtoms

/-- CK's named extra: same type, still no C5 binder -/
def named_extra : extra_is_Prop hfirst :=
  AxisAtomsOp9.named_axisAtoms hfirst

/-- Source identity: `named_axisAtoms` is the residual projection.
    (Any two proofs of this `Prop` are equal by proof irrelevance; the
    type-level pin is that neither binder mentions C5. Contrast C1 below.) -/
theorem named_axisAtoms_is_residual_projection :
    AxisAtomsOp9.named_axisAtoms hfirst = (SlotSemanticsOp9.residualPremises hfirst).axisAtoms :=
  rfl

/-- C1 license shape, independently compiled: the named extra is an
    implication *from* the designed object -/
def c1_license_takes_designed_object :=
  @pairedRecordLayout_of_intermediatePreimage

/-- CK named extra has no C5 argument -/
def named_axisAtoms_has_no_c5_binder :=
  @AxisAtomsOp9.named_axisAtoms

def c5_has_certificate_type :=
  @AxisAtomsOp9.localCertificates

/-! ## Axis 3. Drift: skeleton vs certificate; `castRowData`; kinds 3-tuple -/

/-- Semantic parent row is `castRowData` of `parentRowData` along
    `computeRowAt_zero` -/
theorem rows_zero_is_castRowData :
    (Op9Execution hfirst).semanticData.rows ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩ =
      castRowData computeRowAt_zero parentRowData :=
  SlotSemanticsOp9.rows_zero hfirst

theorem rows_one_is_castRowData :
    (Op9Execution hfirst).semanticData.rows ⟨1, one_lt_op9 hfirst⟩ =
      castRowData computeRowAt_one child1RowData :=
  SlotSemanticsOp9.rows_one hfirst

theorem rows_two_is_castRowData :
    (Op9Execution hfirst).semanticData.rows ⟨2, two_lt_op9 hfirst⟩ =
      castRowData computeRowAt_two child2RowData :=
  SlotSemanticsOp9.rows_two hfirst

/-- `castRowData` preserves `decompNoun` -/
theorem castRowData_preserves_f_th :
    decompNoun
        (castRowData computeRowAt_zero parentRowData) .f_th =
      decompNoun parentRowData .f_th :=
  SlotSemanticsOp9.castRowData_decompNoun computeRowAt_zero parentRowData .f_th

/-- Reconstructed skeleton state is `.s9` at the parent; the certificate
    lives on `ComputeRowSemanticData`, not on that skeleton. -/
theorem reconstructed_parent_state_is_s9 :
    ((computeNodeAt (Op9Execution hfirst) (SlotSemanticsOp9.residualPremises hfirst)
        ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩).skel).state = .s9 :=
  SlotSemanticsOp9.reconstructed_parent_state hfirst (SlotSemanticsOp9.residualPremises hfirst)

theorem computeSkeletonOf_parent_is_s9
    (pubR : ComputePublicRowNounRealization 97
      (computePublicLabel (parentRow seedZ alphaA))) :
    (computeSkeletonOf parentRowData pubR).state = .s9 :=
  rfl

/-- Paper `1737` is the OP9 line-number check `ln = ln_prev · α³` at this
    honest row (`ln_prev = 1`).  Distinct from `AxisAtomPremises`. -/
theorem parent_ln_is_alpha_cubed :
    (parentRow seedZ alphaA).2.2.1.ln = alphaA ^ 3 ∧
      (parentRow seedZ alphaA).2.2.1.ln_prev = 1 :=
  ⟨rfl, rfl⟩

/-- Classification tuple is three kinds after `firstLine` left; `axisAtoms`
    is the `paperProtocol` slot -/
theorem residualPremises_kinds_is_three :
    (PremiseKind.leanEncoding, PremiseKind.paperProtocol, PremiseKind.leanEncoding) =
      (.leanEncoding, .paperProtocol, .leanEncoding) :=
  residualPremises_kinds

/-! ## Axis 5. Wrong layer: not a fifteenth field; not statement-layer; not `∀ E` -/

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen
    (P : OptimizedFullStrictNockVMROMPackage F' K' 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F') :
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

/-- Statement-layer `op9ParentCertificate_nonempty` is `Nonempty` of a
    certificate on `op9ParentRowData` over `K97cubic`, not C5 on
    `(Op9Execution hfirst).semanticData` over `K3` -/
theorem statement_layer_parent_cert :
    Nonempty (LocalOpcodeCertificate 97 7 Op9Statement.op9ParentRowData) :=
  Op9Statement.op9ParentCertificate_nonempty

def execution_layer_c5 :=
  @AxisAtomsOp9.localCertificates

/-- `packageOf` still takes `Data E` and `Inputs E`.  Not `∀ E, Data E`. -/
def packageOf_still_takes_data_and_inputs :=
  @packageOf

theorem packageOf_fibre_still_takes_forest_order
    {E : BuildableNockExecution F' K'} (D : Data E)
    (hgt : 11 < ringChar K') (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K' ∧ E.cfg.memRows < ringChar K')
    (hgenF : GeneratedField.ClaimGenerated K' D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F')
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    ∀ a g : K',
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts (honestCoin E a g)
        E.cfg.challenges.lam :=
  Batch130.packageOf_fibre_accepts_still_takes_window_batch130
    D hgt I hprl hmore hord hordM hrows hgenF hF horder

/-- `CensusRecordPremises` still five fields. -/
theorem censusRecordPremises_eta_five
    {E : BuildableNockExecution F' K'} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl

/-- `MemoryRecordPremises` still two fields. -/
theorem memoryRecordPremises_eta_two
    {E : BuildableNockExecution F' K'} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } := by
  cases M
  rfl

end

/-! ## Axis 4. -/

#print axioms c5_nonempty
#print axioms parent_row_is_s9
#print axioms child1_row_is_s1
#print axioms child2_row_is_s1
#print axioms op9_compRows
#print axioms c5_row_zero_inhabited
#print axioms c5_row_one_inhabited
#print axioms c5_row_two_inhabited
#print axioms op9AxisAtom_is_atom_two
#print axioms parent_f_th_is_atom_two
#print axioms parent_axis_is_comparison_listed
#print axioms axisAtomPremises_expands
#print axioms comparisonListed_is_membership
#print axioms execution_eta_lacks_c5
#print axioms bindComputeRow_still_takes_axisAtoms
#print axioms dataOf_still_consumes_axisAtoms
#print axioms data_has_q_eq_but_not_axisAtoms
#print axioms vcomp_s9_axis_is_field_element
#print axioms residualPremises_eta_three
#print axioms residualPremises_still_projects_axisAtoms
#print axioms fixture_free_extra
#print axioms named_extra
#print axioms named_axisAtoms_is_residual_projection
#print axioms c1_license_takes_designed_object
#print axioms named_axisAtoms_has_no_c5_binder
#print axioms c5_has_certificate_type
#print axioms rows_zero_is_castRowData
#print axioms rows_one_is_castRowData
#print axioms rows_two_is_castRowData
#print axioms castRowData_preserves_f_th
#print axioms reconstructed_parent_state_is_s9
#print axioms computeSkeletonOf_parent_is_s9
#print axioms parent_ln_is_alpha_cubed
#print axioms residualPremises_kinds_is_three
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms independent_exact_eleven_one_two_accounting
#print axioms statement_layer_parent_cert
#print axioms execution_layer_c5
#print axioms packageOf_still_takes_data_and_inputs
#print axioms packageOf_fibre_still_takes_forest_order
#print axioms censusRecordPremises_eta_five
#print axioms memoryRecordPremises_eta_two
#print axioms optimizedFullStrictNockVMROM_of_package
#print axioms AxisAtomsOp9.localCertificates
#print axioms AxisAtomsOp9.named_axisAtoms
#print axioms AxisAtomsOp9.parentCertificate

end Nock.RedTeam.Batch158
