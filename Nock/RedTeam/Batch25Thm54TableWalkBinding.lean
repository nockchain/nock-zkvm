/-
  Nock/RedTeam/Batch25Thm54TableWalkBinding.lean

  Four things are checked, all as compiled artifacts rather than prose:

  1. **Non-vacuity of the recognizer-completeness bridge.**  A concrete `ℚ`-seeded `.s0` row and a
     concrete `.s9` row on which `RecognizerCompleteness.servedLookup_of_slot` genuinely fires, and
     on which the two `ServedLookup` obligations of
     `StrictOperationalEvidence.StrictRowOperationalEvidence` therefore hold.  Without such a witness,
     `ServedLookupBridge.strict_s0_served_of_slot` could be true for an unsatisfiable premise.

  2. **The Packet-A coverage gap.**  `RawSemanticAssembly.scannedRowRecordRealization_of_bindComputeRow`
     (A2's Step 4) had no compiled `.s0` witness: `recordCount.s0 = 2` and `fanoutComp.s0 = 0`, so
     the `.s0` branch is the one that exercises "live `mr2`, zero subformulas".  `b25_s0_step4_record`
     builds a real `SemanticStrategy.BindComputeRow` and a real
     `BoundSemanticTrace.SkeletonOperationalCore` on that row and shows the `s0_record` field fires
     at the **production** record `pub.mr2`.

  3. **`hfo` / `hFcommit` discharge regressions**, plus the wrong-fanout rejection: the fanout column
     is the authoritative `comp_stateSep` bank (no second selector bank), and disagreement with it
     refutes the topology binding residual outright.

  4. **A partial receipt for B6** — exactly which half of `RawSemanticAssembly.ExecTreeShapeMatchesAt`
     prover-committed topology supplies and which half it does not.
-/

import Nock.NockVMROM.Thm54.ServedLookupBridge
import Nock.NockVMROM.Thm54.SharedTableWalkRow

namespace Nock.RedTeam.Batch25

open Classical
open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.RecognizerCompleteness
open Nock.NockVMROM.Thm54.ServedLookupBridge

noncomputable section

/-! ## 1. A concrete recognizer-completeness witness -/

/-- Sample NPR seed. -/
def zq : ℚ := 2

theorem zq_ne_zero : zq ≠ 0 := by norm_num [zq]

/-- The `.s0` row's subject: a genuine cell, so axis `2` is a real lookup. -/
def subj0 : Noun := .cell (.atom 7) (.atom 9)

/-- The value served at axis `2` of `subj0`. -/
def eval0 : Noun := .atom 7

theorem slot_two_subj0 : Noun.slot 2 subj0 = some eval0 :=
  GlobalCarryRecognizer.local_cons_head subj0 eval0 (.atom 9) rfl

/-- **The bridge fires.**  A concrete served lookup produced by recognizer completeness — the
premise of `ServedLookupBridge.strict_s0_served_of_slot` is inhabited. -/
theorem b25_servedLookup_of_slot_fires :
    GlobalCarryAxis.ServedLookup (GlobalCarryRecognizer.ofNoun subj0 1) 2 eval0 :=
  servedLookup_of_slot slot_two_subj0

/-- The two directions really are inverse on this witness. -/
theorem b25_servedLookup_iff_roundtrip :
    Noun.slot 2 subj0 = some eval0 := by
  exact (servedLookup_iff_slot 2 subj0 eval0).1 b25_servedLookup_of_slot_fires

/-! ## 2. A real `.s0` compute row: Step-4 record branch and the served field -/

def mr1Skel : SemanticStrategy.MemRecSkeleton := ⟨.atom 0, .atom 0, 1⟩
def mr2Skel : SemanticStrategy.MemRecSkeleton := ⟨subj0, eval0, 2⟩

/-- `OP_0` formula `[0 2]`. -/
def form0 : Noun := .cell (.atom 0) (.atom 2)

/-- A genuine `.s0` pre-seed compute row: `recordCount.s0 = 2` (so `mr1`/`mr2` are live and `mr3` is
padding) and `fanoutComp.s0 = 0` (so all three subformula triples are padding). -/
def s0Skel : SemanticStrategy.ComputeRowSkeleton where
  state := .s0
  subject := subj0
  formula := form0
  evaluation := eval0
  decomposition := fun slot _ =>
    match slot with
    | .f_h => .atom 0
    | .f_t => .atom 2
    | _ => .atom 0
  subformula := fun i hi _ => absurd hi (by simp [ComputeTable.fanoutComp])
  memoryRecord := fun i _ => if (i : ℕ) = 1 then mr2Skel else mr1Skel

theorem s0Skel_state : s0Skel.state = .s0 := rfl

theorem s0Skel_axis : P8Census.skeletonMemoryAxis s0Skel 1 = 2 := rfl

/-- The `.s0` row's Nock slot semantics — the one honest premise of Packet B, discharged here on a
concrete row. -/
theorem s0Skel_slotSemantics : SkeletonSlotSemantics s0Skel where
  s0_slot := fun _ => by rw [s0Skel_axis]; exact slot_two_subj0
  s9_slot := fun h => absurd h (by simp [s0Skel_state])

/-- **`strict_s0_served` holds on a real `.s0` row.** -/
theorem b25_strict_s0_served :
    GlobalCarryAxis.ServedLookup
      (GlobalCarryRecognizer.ofNoun s0Skel.subject 1)
      (P8Census.skeletonMemoryAxis s0Skel 1) s0Skel.evaluation :=
  strict_s0_served_of_slot s0Skel_slotSemantics rfl

/-! ### The production row bound to that skeleton -/

def s0Inputs : ComputeTable.Inputs ℚ := ⟨0, zq, 0, 0, 0⟩

def s0Pub : ComputeTable.Pub ℚ where
  state := .s0
  s := GlobalCarryRecognizer.enc zq subj0
  f := GlobalCarryRecognizer.enc zq form0
  e := GlobalCarryRecognizer.enc zq eval0
  sf1_s := 0
  sf1_f := 0
  sf1_e := 0
  sf2_s := 0
  sf2_f := 0
  sf2_e := 0
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 0
  ln := 0
  mr1 := ⟨GlobalCarryRecognizer.enc zq (.atom 0), GlobalCarryRecognizer.enc zq (.atom 0),
    ((1 : ℕ) : ℚ), 0⟩
  mr2 := ⟨GlobalCarryRecognizer.enc zq subj0, GlobalCarryRecognizer.enc zq eval0,
    ((2 : ℕ) : ℚ), 0⟩
  mr3 := ComputeTable.MemRec.zero

def s0Dec : ComputeTable.Dec ℚ where
  f_h := GlobalCarryRecognizer.enc zq (.atom 0)
  f_t := GlobalCarryRecognizer.enc zq (.atom 2)
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

def s0RowData : ComputeTable.State × ComputeTable.DTcomp ℚ := (.s0, s0Inputs, s0Pub, s0Dec)

/-- The concrete production row really is bound to the concrete skeleton at seed `zq`. -/
theorem b25_bindComputeRow : SemanticStrategy.BindComputeRow zq s0Skel s0RowData := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;> simp [SemanticStrategy.decActive, SemanticStrategy.hasTailDecomposition,
      SemanticStrategy.decFP, SemanticStrategy.bindFP, s0Skel, s0RowData, s0Dec]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp s0Skel.state) := by
      simp [s0Skel, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
    · rfl

/-- A real `BoundSemanticTrace.SkeletonOperationalCore` on the `.s0` row.  Its served
field is produced by Packet B's recognizer completeness, not assumed. -/
theorem b25_s0_operationalCore :
    BoundSemanticTrace.SkeletonOperationalCore s0Skel :=
  skeletonOperationalCore_of_parts
    { s0_record := fun _ => ⟨rfl, rfl⟩
      s9_record := fun h => absurd h (by simp [s0Skel_state]) }
    s0Skel_slotSemantics

/-- **Packet-A coverage gap closed.**  A2's Step-4 record branch (`ScannedRowRecordRealization`)
compiles on a real `.s0` row with `recordCount = 2`, `fanoutComp = 0`, and its `s0_record` field
fires at the **production** record `computeMemRec s0Pub 1 = s0Pub.mr2`. -/
theorem b25_s0_step4_record :
    OpcodeSemantics.RealizesMemRec zq (computeMemRec s0Pub (1 : Fin 3))
      s0Skel.subject s0Skel.evaluation (P8Census.skeletonMemoryAxis s0Skel 1) :=
  (RawSemanticAssembly.scannedRowRecordRealization_of_bindComputeRow
    b25_s0_operationalCore b25_bindComputeRow).s0_record rfl

/-- The whole scanned-row strict contract on the `.s0` row: production records, both served
lookups, and modular OP4 — with no served lookup assumed anywhere. -/
theorem b25_s0_strictScannedRowEvidence (p : ℕ) :
    StrictScannedRowEvidence p zq s0Skel s0RowData :=
  strictScannedRowEvidence_of_bindComputeRow
    { s0_record := fun _ => ⟨rfl, rfl⟩
      s9_record := fun h => absurd h (by simp [s0Skel_state]) }
    s0Skel_slotSemantics
    (fun h => absurd h (by simp [s0Skel_state]))
    b25_bindComputeRow

/-! ## A real `.s9` row for `strict_s9_served` -/

def core9 : Noun := .cell (.atom 5) (.atom 6)
def arm9 : Noun := .atom 6

/-- A genuine `.s9` pre-seed compute row: `fanoutComp.s9 = 2` and `recordCount.s9 = 3`, so
`sf1`/`sf2` and `mr1`/`mr2`/`mr3` are all live. -/
def s9Skel : SemanticStrategy.ComputeRowSkeleton where
  state := .s9
  subject := .atom 0
  formula := .cell (.atom 9) (.cell (.atom 3) (.atom 1))
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun i _ slot =>
    if (i : ℕ) = 0 then
      match slot with
      | .result => core9
      | _ => .atom 0
    else
      match slot with
      | .formula => arm9
      | _ => .atom 0
  memoryRecord := fun i _ =>
    if (i : ℕ) = 2 then ⟨core9, arm9, 3⟩ else ⟨.atom 0, .atom 0, 1⟩

theorem s9Skel_state : s9Skel.state = .s9 := rfl

theorem s9Skel_axis : P8Census.skeletonMemoryAxis s9Skel 2 = 3 := rfl

theorem s9Skel_core : P8Census.skeletonSubformula s9Skel 0 .result = core9 := rfl

theorem s9Skel_arm : P8Census.skeletonSubformula s9Skel 1 .formula = arm9 := rfl

theorem s9Skel_slotSemantics : SkeletonSlotSemantics s9Skel where
  s0_slot := fun h => absurd h (by simp [s9Skel_state])
  s9_slot := fun _ => by
    rw [s9Skel_axis, s9Skel_core, s9Skel_arm]
    exact GlobalCarryRecognizer.local_cons_tail core9 (.atom 5) arm9 rfl

/-- **`strict_s9_served` holds on a real `.s9` row.** -/
theorem b25_strict_s9_served :
    GlobalCarryAxis.ServedLookup
      (GlobalCarryRecognizer.ofNoun
        (P8Census.skeletonSubformula s9Skel 0 .result) 1)
      (P8Census.skeletonMemoryAxis s9Skel 2)
      (P8Census.skeletonSubformula s9Skel 1 .formula) :=
  strict_s9_served_of_slot s9Skel_slotSemantics rfl

/-- Both served obligations of the strict row contract are met on a genuine row, so
`StrictRowOperationalEvidence` is inhabited without assuming a served lookup. -/
theorem b25_strictRowOperationalEvidence_nonvacuous (p : ℕ) :
    StrictOperationalEvidence.StrictRowOperationalEvidence p zq s0Skel :=
  strictRowOperationalEvidence_of_slots
    { s0_record := fun _ => ⟨rfl, rfl⟩
      s9_record := fun h => absurd h (by simp [s0Skel_state]) }
    s0Skel_slotSemantics
    (fun h => absurd h (by simp [s0Skel_state]))

/-! ## 3. `hfo` / `hFcommit` discharge and the selector-bank regressions -/

section Walk

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Discharge regression: `hfo` in exactly the shape `Walk.Walk_IOP_final_prob` consumes, with the
authoritative `comp_stateSep` bank on the right-hand side. -/
theorem b25_hfo_compute_discharged (R : RawPlusIOSegmentedFamily F K)
    (hbind : RawTopologyBindingResidual R) :
    ∀ i, 1 ≤ i → i ≤ R.cfg.compRows →
      foCol R.computeWalkRows i =
        (ComputeTable.comp_stateSep (K := K)).fanout
          (SharedTableWalkRow.computeRowLabel R i).1 :=
  SharedTableWalkRow.hfo_compute R hbind

/-- Memory analogue, against `mem_stateSep`. -/
theorem b25_hfo_memory_discharged (R : RawPlusIOSegmentedFamily F K)
    (hbind : RawTopologyBindingResidual R) :
    ∀ i, 1 ≤ i → i ≤ R.cfg.memRows →
      foCol R.memoryWalkRows i =
        (MemoryTable.mem_stateSep (K := K)).fanout
          (SharedTableWalkRow.memoryRowLabel R i).1 :=
  SharedTableWalkRow.hfo_memory R hbind

/-- Discharge regression: `hFcommit` in exactly the shape `Walk.Walk_IOP_final_prob` consumes. -/
theorem b25_hFcommit_compute_discharged (R : RawPlusIOSegmentedFamily F K)
    (hrows : R.exec.ComputeRowsAccepted) (hbind : RawTopologyBindingResidual R) :
    ∀ i, 1 ≤ i → i ≤ R.cfg.compRows →
      ComputeTable.Fcomp (SharedTableWalkRow.computeRowLabel R i)
        (fun j : Fin 3 =>
          if (j : ℕ) < foCol R.computeWalkRows i then
            some (SharedTableWalkRow.computeChildLabel R i ((j : ℕ) + 1)) else none) :=
  SharedTableWalkRow.hFcommit_compute R hrows hbind

/-- Memory analogue. -/
theorem b25_hFcommit_memory_discharged (R : RawPlusIOSegmentedFamily F K)
    (hrows : R.exec.MemoryRowsAccepted) (hbind : RawTopologyBindingResidual R) :
    ∀ i, 1 ≤ i → i ≤ R.cfg.memRows →
      MemoryTable.Fmem (SharedTableWalkRow.memoryRowLabel R i)
        (fun j : Fin 2 =>
          if (j : ℕ) < foCol R.memoryWalkRows i then
            some (SharedTableWalkRow.memoryChildLabel R i ((j : ℕ) + 1)) else none) :=
  SharedTableWalkRow.hFcommit_memory R hrows hbind

/-- **Wrong-fanout rejection.**  A row whose committed child count disagrees with the authoritative
`comp_stateSep` bank refutes the topology binding residual, hence (by
`exactTopology_iff_rawTopologyBindingResidual_of_rowsAccepted`) cannot come from an accepted exact
topology.  There is no second, prover-controlled selector bank to disagree with: the fanout is a
total function of the committed state, so an all-zero or duplicated selector cannot be expressed. -/
theorem b25_wrong_fanout_rejected (R : RawPlusIOSegmentedFamily F K)
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ R.cfg.compRows)
    (hne : foCol R.computeWalkRows i ≠
      (ComputeTable.comp_stateSep (K := K)).fanout
        (SharedTableWalkRow.computeRowLabel R i).1) :
    ¬ RawTopologyBindingResidual R :=
  SharedTableWalkRow.wrong_fanout_no_binding R h1 h2 hne

/-- **Duplicated-selector regression.**  Committing a child payload different from the authoritative
BFS child row is rejected deterministically, independently of the `gamma` RLC collision event
(`RawTopologyAIR.mutatedComputeChildPayload_rejected`). -/
theorem b25_mutated_child_payload_rejected (R : RawPlusIOSegmentedFamily F K)
    (A : RawTopologyArrays R) (i : Fin R.cfg.compRows) (slot : Fin 3)
    (hi : (slot : ℕ) < ComputeTable.fanoutComp (computeTopologyNodeAt R i).label.1)
    (hne : A.compute.childPayload i slot ≠ computeLookupPayload R i slot) :
    ¬ VerifierGeneratedTopologyRAPSatisfyOfCommittedArrays R A :=
  mutatedComputeChildPayload_rejected R A i slot hi hne

/-- **`s0` is a walk leaf.**  The OP0 slice cannot commit any child at all. -/
theorem b25_s0_slice_has_no_children (R : RawPlusIOSegmentedFamily F K)
    (hbind : RawTopologyBindingResidual R)
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ R.cfg.compRows)
    (hs0 : (SharedTableWalkRow.computeRowLabel R i).1 = .s0) :
    foCol R.computeWalkRows i = 0 ∧ (SharedTableWalkRow.computeNodeAtIdx R i).children = [] :=
  SharedTableWalkRow.s0_is_leaf R hbind h1 h2 hs0

/-! ## 4. B6 partial receipt: what prover-committed topology does and does not supply

`RawSemanticAssembly.ExecTreeShapeMatchesAt C exec` is a relation between the **committed skeleton
tree** and the **execution tree**.  Prover-committed topology (the binding residual, which acceptance
supplies) constrains only the execution side: every execution node's child count is
`fanoutComp` of that node's own committed state.  It says nothing about the skeleton tree's arity and
nothing about the ordered skeleton-to-execution pairing, which is the remaining content of
`ComputeShapeMatch`.  `b25_exec_side_arity_of_binding` compiles the half that IS supplied. -/

/-- The execution-side half of the shape datum, from the topology binding residual. -/
theorem b25_exec_side_arity_of_binding (R : RawPlusIOSegmentedFamily F K)
    (hbind : RawTopologyBindingResidual R) :
    ∀ t ∈ bfsForest [R.exec.computeTree],
      ComputeTable.fanoutComp t.label.1 = t.children.length :=
  fun t ht => (hbind.1 t ht).1

/-- Memory-side analogue of the supplied half. -/
theorem b25_memory_exec_side_arity_of_binding (R : RawPlusIOSegmentedFamily F K)
    (hbind : RawTopologyBindingResidual R) :
    ∀ t ∈ bfsForest R.exec.memoryForest,
      MemoryTable.fanoutMem t.label.1 = t.children.length :=
  fun t ht => (hbind.2 t ht).1

/-- **The residual, named.**  What `ExecTreeShapeMatchesAt` still needs beyond the execution-side
arity is the ordered skeleton-to-execution pairing.  This definition is the exact statement that is
NOT proved by Packet B; it is recorded so the gap cannot be silently absorbed. -/
def B6ComputeShapeResidual (C : StrictCommitment.SkeletonCommitment)
    (R : RawPlusIOSegmentedFamily F K) : Prop :=
  RawSemanticAssembly.ComputeShapeMatch C.skeleton.computeTree R.exec.computeTree

/-- Memory half of the same residual. -/
def B6MemoryShapeResidual (C : StrictCommitment.SkeletonCommitment)
    (R : RawPlusIOSegmentedFamily F K) : Prop :=
  List.Forall₂ RawSemanticAssembly.MemoryShapeMatch
    C.skeleton.memoryForest R.exec.memoryForest

/-- The two named residuals are exactly `ExecTreeShapeMatchesAt`: nothing has been dropped or
relabelled. -/
theorem b25_B6_residual_is_shape_datum (C : StrictCommitment.SkeletonCommitment)
    (R : RawPlusIOSegmentedFamily F K) :
    (B6ComputeShapeResidual C R ∧ B6MemoryShapeResidual C R) ↔
      RawSemanticAssembly.ExecTreeShapeMatchesAt C R.exec :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.compute, h.memory⟩⟩

end Walk

end

end Nock.RedTeam.Batch25

#print axioms Nock.RedTeam.Batch25.b25_servedLookup_of_slot_fires
#print axioms Nock.RedTeam.Batch25.b25_servedLookup_iff_roundtrip
#print axioms Nock.RedTeam.Batch25.s0Skel_slotSemantics
#print axioms Nock.RedTeam.Batch25.b25_strict_s0_served
#print axioms Nock.RedTeam.Batch25.b25_bindComputeRow
#print axioms Nock.RedTeam.Batch25.b25_s0_operationalCore
#print axioms Nock.RedTeam.Batch25.b25_s0_step4_record
#print axioms Nock.RedTeam.Batch25.b25_s0_strictScannedRowEvidence
#print axioms Nock.RedTeam.Batch25.s9Skel_slotSemantics
#print axioms Nock.RedTeam.Batch25.b25_strict_s9_served
#print axioms Nock.RedTeam.Batch25.b25_strictRowOperationalEvidence_nonvacuous
#print axioms Nock.RedTeam.Batch25.b25_hfo_compute_discharged
#print axioms Nock.RedTeam.Batch25.b25_hfo_memory_discharged
#print axioms Nock.RedTeam.Batch25.b25_hFcommit_compute_discharged
#print axioms Nock.RedTeam.Batch25.b25_hFcommit_memory_discharged
#print axioms Nock.RedTeam.Batch25.b25_wrong_fanout_rejected
#print axioms Nock.RedTeam.Batch25.b25_mutated_child_payload_rejected
#print axioms Nock.RedTeam.Batch25.b25_s0_slice_has_no_children
#print axioms Nock.RedTeam.Batch25.b25_exec_side_arity_of_binding
#print axioms Nock.RedTeam.Batch25.b25_memory_exec_side_arity_of_binding
#print axioms Nock.RedTeam.Batch25.b25_B6_residual_is_shape_datum
