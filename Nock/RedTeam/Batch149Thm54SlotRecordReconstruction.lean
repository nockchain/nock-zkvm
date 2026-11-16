import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.DistinctCensusExecution
import Nock.NockVMROM.Thm54.GenericHonestCommitment
import Nock.NockVMROM.Thm54.GenericHonestData
import Nock.NockVMROM.Thm54.NounRealization
import Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Reconstruction-route `slotSemantics` / `recordEquations`

Construction files were not edited.  The two proposed fields below are
**shadows**.  Neither is added to `ComputeRowSemanticData` or `CensusRecordPremises`.

Paper frame (re-read at source):
* slot operator `\(n_2,n_1)`; base `\(1,n_1)=n_1` (`1290`);
  child-axis (`1292-1294`).  `Def:NMR` address space (`1328`) is **not** re-litigated.
* Algorithm `NockCompute` OP0 `mem_record₂`:
  `mem_root₂ = input_subject`, `mem_child₂ = evaluation`.

Consumed capstone: `optimizedFullStrictNockVMROM_of_package`.  Nothing here inhabits a
named extra as a new field, ticks `slotSemantics` / `census` / `skeletonBounded`, or
restarts designed `C2` / fingerprint `C4` / `C5`.

1. **`recordEquations` as a carrier field is a rename (C6 family).**
   `RecordEquationsField` is `Iff.rfl` with `SkeletonRecordEquations` on
   `computeSkeletonOf`.  That predicate already holds by construction
   (`computeSkeletonOf_recordEquations`, `recordEquations_of_assembly`).
   `censusAssemblyOf_recordEquations` copies the derived proof, `rfl`.
   It is **not** among the five `CensusRecordPremises` fields.

2. **Designed OP0 identification is the record equation.**
   `DesignedOP0RecordId` is `Iff.rfl` with `SkeletonRecordEquations.s0_record`.
   On reconstructed rows the public triple are labels (`rfl`), and OP0 `mr2`
   nouns are those labels (`memRecSkelOf`).  Identification is therefore
   already the assembled record equation, not a new reconstruction object.

3. **Identification does not entail `slotSemantics`.**
   `s0SlotFailRow` has record equations (hence designed OP0 identification)
   and the paper axis-1 base case, and fails `/[2, atom 0]`
   (`slotSemantics_does_not_follow_from_records_or_axis_one`).
   Adding identification as a field would not discharge the named extra.
   The residual remains the slot fact itself; `C5` stays DEPRIORITIZED
.  **Do not tick `slotSemantics`.**

4. **Live-fixture non-vacuity, reconstruction not hand-built `skelD`.**
   At F97 `distinctCensusExecution`, `recordEquations_of_assembly` inhabits
   the derived record equations, and `distinctCensus_slotSemantics` inhabits
   `SkeletonSlotSemantics` because the fixture has no `.s0`/`.s9` rows.
   The opcode gate remains load-bearing: the extra is **not** closed generically.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch149

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.ServedLookupBridge

noncomputable section

open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## Shadows of the proposed fields — not added to production -/

/-- Proposed reconstruction-route field: record equations on the reconstructed skeleton.
Shadow only.  Production `CensusAssemblyPremises.recordEquations` is already derived. -/
def RecordEquationsField {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) : Prop :=
  SkeletonRecordEquations (computeSkeletonOf data pubR)

/-- Proposed reconstruction-route field: slot facts on the reconstructed skeleton.
Shadow only.  Production `CensusRecordPremises.slotSemantics` stays a named extra. -/
def SlotSemanticsField {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) : Prop :=
  SkeletonSlotSemantics (computeSkeletonOf data pubR)

/-- Designed OP0 identification: `mem_record₂` nouns equal subject/evaluation.
This is `SkeletonRecordEquations.s0_record` on the nose.  Shadow only. -/
def DesignedOP0RecordId (s : ComputeRowSkeleton) : Prop :=
  ∀ h : s.state = .s0,
    let mr := s.memoryRecord (1 : Fin 3) (by simp [h, Nock.Framework.recordCount])
    mr.root = s.subject ∧ mr.child = s.evaluation

/-! ## Equivalence: record field is already derived -/

/-- The proposed record field is definitionally `SkeletonRecordEquations` on the reconstruction. -/
theorem b149_record_field_iff {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) :
    RecordEquationsField data pubR ↔
      SkeletonRecordEquations (computeSkeletonOf data pubR) :=
  Iff.rfl

/-- Every reconstructed row already inhabits the proposed record field, by construction. -/
theorem b149_record_field_already {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) :
    RecordEquationsField data pubR :=
  computeSkeletonOf_recordEquations data pubR

/-- Whole-execution reconstruction already inhabits record equations. -/
theorem b149_record_equations_of_assembly (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      SkeletonRecordEquations s :=
  recordEquations_of_assembly E P M

/-- `censusAssemblyOf` copies the derived proof, not a `CensusRecordPremises` field. -/
theorem b149_censusAssemblyOf_recordEquations
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).recordEquations =
      recordEquations_of_assembly E P M :=
  censusAssemblyOf_recordEquations E P M C

/-! ## Equivalence: designed OP0 identification is the record equation -/

/-- Designed OP0 identification is definitionally `SkeletonRecordEquations.s0_record`. -/
theorem b149_designed_c3_iff_s0_record (s : ComputeRowSkeleton) :
    DesignedOP0RecordId s ↔
      ∀ h : s.state = .s0,
        let mr := s.memoryRecord (1 : Fin 3) (by simp [h, Nock.Framework.recordCount])
        mr.root = s.subject ∧ mr.child = s.evaluation :=
  Iff.rfl

/-- Record equations supply designed OP0 identification. -/
theorem b149_designed_c3_of_records (s : ComputeRowSkeleton)
    (h : SkeletonRecordEquations s) : DesignedOP0RecordId s :=
  h.s0_record

/-- Reconstructed public triple are execution labels, `rfl`. -/
theorem b149_reconstruction_public_triple_are_labels {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) :
    (computeSkeletonOf data pubR).subject = data.root.subject ∧
      (computeSkeletonOf data pubR).formula = data.root.formula ∧
        (computeSkeletonOf data pubR).evaluation = data.root.result :=
  ⟨rfl, rfl, rfl⟩

/-- On a reconstructed row, designed OP0 identification holds by construction. -/
theorem b149_designed_c3_on_reconstruction {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) :
    DesignedOP0RecordId (computeSkeletonOf data pubR) :=
  (computeSkeletonOf_recordEquations data pubR).s0_record

/-! ## Discriminator: records / identification do not entail slotSemantics -/

/-- Assembled-style record equations hold, paper `\(1,n)=n` holds, named extra fails. -/
theorem b149_slot_does_not_follow_from_records_or_axis_one :
    SkeletonRecordEquations GenericHonestData.s0SlotFailRow ∧
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun GenericHonestData.s0SlotFailRow.subject 1) 1
        GenericHonestData.s0SlotFailRow.subject ∧
      ¬ SkeletonSlotSemantics GenericHonestData.s0SlotFailRow :=
  GenericHonestData.slotSemantics_does_not_follow_from_records_or_axis_one

/-- Designed OP0 identification on that row, and the named extra still fails. -/
theorem b149_designed_c3_does_not_entail_slot :
    DesignedOP0RecordId GenericHonestData.s0SlotFailRow ∧
      ¬ SkeletonSlotSemantics GenericHonestData.s0SlotFailRow :=
  ⟨b149_designed_c3_of_records _ GenericHonestData.s0SlotFailRow_recordEquations,
    GenericHonestData.slotSemantics_fails_of_atom_subject_axis_two⟩

/-- The proposed slot field is not a consequence of the proposed record field. -/
theorem b149_slot_field_not_from_records :
    ∃ s : ComputeRowSkeleton,
      SkeletonRecordEquations s ∧ ¬ SkeletonSlotSemantics s :=
  ⟨GenericHonestData.s0SlotFailRow, GenericHonestData.s0SlotFailRow_recordEquations,
    GenericHonestData.slotSemantics_fails_of_atom_subject_axis_two⟩

/-- `censusAssemblyOf` still copies `slotSemantics` from the named extra. -/
theorem b149_censusAssemblyOf_copies_slotSemantics
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).slotSemantics = C.slotSemantics :=
  censusAssemblyOf_copies_slotSemantics E P M C

/-! ## Live fixture (F97 reconstruction, not `skelD`) -/

section LiveFixture

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.CensusExtraClosure

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)

/-- Record equations already hold on the F97 reconstruction, for every `(P, M)`. -/
theorem b149_recordEquations_at_f97
    (P : ResidualPremises (distinctCensusExecution hfirstD))
    (M : MemoryRecordPremises (distinctCensusExecution hfirstD)) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)),
      SkeletonRecordEquations s :=
  recordEquations_of_assembly (distinctCensusExecution hfirstD) P M

/-- `slotSemantics` holds at F97 because the fixture has no lookup states.
This is **fixture-level and state-gated**, not a generic discharge. -/
theorem b149_slotSemantics_at_f97
    (P : ResidualPremises (distinctCensusExecution hfirstD))
    (M : MemoryRecordPremises (distinctCensusExecution hfirstD)) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (distinctCensusExecution hfirstD) P)
          (memoryNodesOf (distinctCensusExecution hfirstD) M)),
      SkeletonSlotSemantics s :=
  CensusExtraClosure.distinctCensus_slotSemantics hfirstD P M

end LiveFixture

/-! ## Accounting: nothing moved -/

/-- `ComputeRowSemanticData` still has no slot or record field. -/
theorem b149_computeRowSemanticData_still_no_slot_or_record_field {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (d : ComputeRowSemanticData q Λ row) :
    d =
      { root := d.root
        tails := d.tails
        branchTails := d.branchTails
        calls := d.calls
        windows := d.windows
        axisGates := d.axisGates
        tails_count := d.tails_count
        branchTails_count := d.branchTails_count
        calls_count := d.calls_count
        windows_count := d.windows_count
        axisGates_count := d.axisGates_count
        realizedNouns := d.realizedNouns
        subject_mem := d.subject_mem
        formula_mem := d.formula_mem
        result_mem := d.result_mem
        bounded := d.bounded
        comparisons := d.comparisons
        comparison_faithful := d.comparison_faithful
        comparison_leaves := d.comparison_leaves
        comparison_roles := d.comparison_roles
        axisGate_listed := d.axisGate_listed
        axisGate_tail_mem := d.axisGate_tail_mem
        needs := d.needs } := by
  cases d
  rfl

/-- Accounting: `CensusRecordPremises` is still five named fields; `recordEquations` is not among them. -/
theorem b149_censusRecordPremises_still_five {E : BuildableNockExecution F K}
    {P : ResidualPremises E} {M : MemoryRecordPremises E}
    (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl

theorem b149_eleven_one_two : 11 + 1 + 2 = 14 := rfl

#print axioms RecordEquationsField
#print axioms SlotSemanticsField
#print axioms DesignedOP0RecordId
#print axioms b149_record_field_iff
#print axioms b149_record_field_already
#print axioms b149_record_equations_of_assembly
#print axioms b149_censusAssemblyOf_recordEquations
#print axioms b149_designed_c3_iff_s0_record
#print axioms b149_designed_c3_of_records
#print axioms b149_reconstruction_public_triple_are_labels
#print axioms b149_designed_c3_on_reconstruction
#print axioms b149_slot_does_not_follow_from_records_or_axis_one
#print axioms b149_designed_c3_does_not_entail_slot
#print axioms b149_slot_field_not_from_records
#print axioms b149_censusAssemblyOf_copies_slotSemantics
#print axioms b149_recordEquations_at_f97
#print axioms b149_slotSemantics_at_f97
#print axioms b149_computeRowSemanticData_still_no_slot_or_record_field
#print axioms b149_censusRecordPremises_still_five
#print axioms b149_eleven_one_two

end

end Nock.RedTeam.Batch149
