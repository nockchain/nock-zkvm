/-
  Nock/NockVMROM/Thm54/TraceGen/GenCensus.lean

  Generator-side census extras on BFS compute skeletons, as the *existing*
  `SkeletonSlotSemantics` / `SkeletonRecordEquations` predicates.  Not new carrier fields
.

  Eleven opcode cases (OP0–OP9 + cons).  Off `.s0`/`.s9` both extras are
  vacuous.  On `.s0`/`.s9`, `recordEquations` is the `genSkelOp0`/`genSkelOp9`
  memory-record identity; `slotSemantics` is the paper slot fact
  `Noun.slot axis root = some child`, carried as an honest Nock hyp.

  Memory: `memoryAssemblyOf` inhabits `MemoryAssemblyPremises` from
  `MemoryRecordPremises`.  The two named extras are `axisNat`
  (`BindMemRec.axis = (skel.axis : K)`, `Def:NMR` the paper) and
  `timestampClosed`, which BFS mem-join restamp preserves on the stamp.

  This module does not edit `Gen.lean`.
-/
import Nock.NockVMROM.Thm54.TraceGen.BFSAssign
import Nock.NockVMROM.Thm54.ServedLookupBridge
import Nock.NockVMROM.Thm54.GenericHonestData
import Nock.Reference

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.GenericHonestData

variable {K : Type} [Field K]

/-! ## Vacuous extras off OP0/OP9 -/

theorem slotSemantics_of_ne_lookup (s : ComputeRowSkeleton)
    (h0 : s.state ≠ ComputeTable.State.s0)
    (h9 : s.state ≠ ComputeTable.State.s9) :
    SkeletonSlotSemantics s where
  s0_slot h := (h0 h).elim
  s9_slot h := (h9 h).elim

theorem recordEquations_of_ne_lookup (s : ComputeRowSkeleton)
    (h0 : s.state ≠ ComputeTable.State.s0)
    (h9 : s.state ≠ ComputeTable.State.s9) :
    SkeletonRecordEquations s where
  s0_record h := (h0 h).elim
  s9_record h := (h9 h).elim

/-! ## Nine non-lookup `genSkel*` cases -/

theorem genSkelOp1_slotSemantics (subject formula result head : Noun) :
    SkeletonSlotSemantics (genSkelOp1 subject formula result head) :=
  slotSemantics_of_ne_lookup _ (by simp [genSkelOp1]) (by simp [genSkelOp1])

theorem genSkelOp1_recordEquations (subject formula result head : Noun) :
    SkeletonRecordEquations (genSkelOp1 subject formula result head) :=
  recordEquations_of_ne_lookup _ (by simp [genSkelOp1]) (by simp [genSkelOp1])

theorem genSkelOp2_slotSemantics
    (subject formula head fTail fTh fTt sf1 sf2 result : Noun) :
    SkeletonSlotSemantics
      (genSkelOp2 subject formula head fTail fTh fTt sf1 sf2 result) :=
  slotSemantics_of_ne_lookup _ (by simp [genSkelOp2]) (by simp [genSkelOp2])

theorem genSkelOp2_recordEquations
    (subject formula head fTail fTh fTt sf1 sf2 result : Noun) :
    SkeletonRecordEquations
      (genSkelOp2 subject formula head fTail fTh fTt sf1 sf2 result) :=
  recordEquations_of_ne_lookup _ (by simp [genSkelOp2]) (by simp [genSkelOp2])

theorem genSkelOp3_slotSemantics
    (subject formula head tail callSubject callFormula callResult result : Noun) :
    SkeletonSlotSemantics
      (genSkelOp3 subject formula head tail callSubject callFormula callResult
        result) :=
  slotSemantics_of_ne_lookup _ (by simp [genSkelOp3]) (by simp [genSkelOp3])

theorem genSkelOp3_recordEquations
    (subject formula head tail callSubject callFormula callResult result : Noun) :
    SkeletonRecordEquations
      (genSkelOp3 subject formula head tail callSubject callFormula callResult
        result) :=
  recordEquations_of_ne_lookup _ (by simp [genSkelOp3]) (by simp [genSkelOp3])

theorem genSkelOp4_slotSemantics
    (subject formula head tail callSubject callFormula callResult result : Noun) :
    SkeletonSlotSemantics
      (genSkelOp4 subject formula head tail callSubject callFormula callResult
        result) :=
  slotSemantics_of_ne_lookup _ (by simp [genSkelOp4]) (by simp [genSkelOp4])

theorem genSkelOp4_recordEquations
    (subject formula head tail callSubject callFormula callResult result : Noun) :
    SkeletonRecordEquations
      (genSkelOp4 subject formula head tail callSubject callFormula callResult
        result) :=
  recordEquations_of_ne_lookup _ (by simp [genSkelOp4]) (by simp [genSkelOp4])

theorem genSkelOp5_slotSemantics
    (subject formula head fTail fTh fTt sf1 sf2 result : Noun) :
    SkeletonSlotSemantics
      (genSkelOp5 subject formula head fTail fTh fTt sf1 sf2 result) :=
  slotSemantics_of_ne_lookup _ (by simp [genSkelOp5]) (by simp [genSkelOp5])

theorem genSkelOp5_recordEquations
    (subject formula head fTail fTh fTt sf1 sf2 result : Noun) :
    SkeletonRecordEquations
      (genSkelOp5 subject formula head fTail fTh fTt sf1 sf2 result) :=
  recordEquations_of_ne_lookup _ (by simp [genSkelOp5]) (by simp [genSkelOp5])

theorem genSkelOp6_slotSemantics
    (subject formula head fTail fTh fTt fTth fTtt cond taken result : Noun) :
    SkeletonSlotSemantics
      (genSkelOp6 subject formula head fTail fTh fTt fTth fTtt cond taken
        result) :=
  slotSemantics_of_ne_lookup _ (by simp [genSkelOp6]) (by simp [genSkelOp6])

theorem genSkelOp6_recordEquations
    (subject formula head fTail fTh fTt fTth fTtt cond taken result : Noun) :
    SkeletonRecordEquations
      (genSkelOp6 subject formula head fTail fTh fTt fTth fTtt cond taken
        result) :=
  recordEquations_of_ne_lookup _ (by simp [genSkelOp6]) (by simp [genSkelOp6])

theorem genSkelOp7_slotSemantics
    (subject formula head fTail fTh fTt sb result : Noun) :
    SkeletonSlotSemantics
      (genSkelOp7 subject formula head fTail fTh fTt sb result) :=
  slotSemantics_of_ne_lookup _ (by simp [genSkelOp7]) (by simp [genSkelOp7])

theorem genSkelOp7_recordEquations
    (subject formula head fTail fTh fTt sb result : Noun) :
    SkeletonRecordEquations
      (genSkelOp7 subject formula head fTail fTh fTt sb result) :=
  recordEquations_of_ne_lookup _ (by simp [genSkelOp7]) (by simp [genSkelOp7])

theorem genSkelOp8_slotSemantics
    (subject formula head fTail fTh fTt sb result : Noun) :
    SkeletonSlotSemantics
      (genSkelOp8 subject formula head fTail fTh fTt sb result) :=
  slotSemantics_of_ne_lookup _ (by simp [genSkelOp8]) (by simp [genSkelOp8])

theorem genSkelOp8_recordEquations
    (subject formula head fTail fTh fTt sb result : Noun) :
    SkeletonRecordEquations
      (genSkelOp8 subject formula head fTail fTh fTt sb result) :=
  recordEquations_of_ne_lookup _ (by simp [genSkelOp8]) (by simp [genSkelOp8])

theorem genSkelCons_slotSemantics
    (subject leftF rightF leftR rightR : Noun) :
    SkeletonSlotSemantics (genSkelCons subject leftF rightF leftR rightR) :=
  slotSemantics_of_ne_lookup _ (by simp [genSkelCons]) (by simp [genSkelCons])

theorem genSkelCons_recordEquations
    (subject leftF rightF leftR rightR : Noun) :
    SkeletonRecordEquations (genSkelCons subject leftF rightF leftR rightR) :=
  recordEquations_of_ne_lookup _ (by simp [genSkelCons]) (by simp [genSkelCons])

/-! ## OP0 record identity and slot -/

theorem genSkelOp0_memoryAxis (subject formula head tail result : Noun)
    (axis : ℕ) :
    P8Census.skeletonMemoryAxis
      (genSkelOp0 subject formula head tail result axis) 1 = axis := by
  simp [P8Census.skeletonMemoryAxis, genSkelOp0, Nock.Framework.recordCount]

theorem genSkelOp0_recordEquations (subject formula head tail result : Noun)
    (axis : ℕ) :
    SkeletonRecordEquations
      (genSkelOp0 subject formula head tail result axis) where
  s0_record h := by
    simp [genSkelOp0]
  s9_record h := by
    simp [genSkelOp0] at h

theorem genSkelOp0_slotSemantics (subject formula head tail result : Noun)
    (axis : ℕ) (hslot : Noun.slot axis subject = some result) :
    SkeletonSlotSemantics
      (genSkelOp0 subject formula head tail result axis) where
  s0_slot _ := by
    rw [genSkelOp0_memoryAxis]
    exact hslot
  s9_slot h := by
    simp [genSkelOp0] at h

/-! ## OP9 record identity and slot -/

theorem genSkelOp9_memoryAxis
    (subject formula head fTail fTh fTt core arm result : Noun) (axis : ℕ) :
    P8Census.skeletonMemoryAxis
      (genSkelOp9 subject formula head fTail fTh fTt core arm result axis) 2 =
        axis := by
  simp [P8Census.skeletonMemoryAxis, genSkelOp9, Nock.Framework.recordCount]

theorem genSkelOp9_recordEquations
    (subject formula head fTail fTh fTt core arm result : Noun) (axis : ℕ) :
    SkeletonRecordEquations
      (genSkelOp9 subject formula head fTail fTh fTt core arm result axis) where
  s0_record h := by
    simp [genSkelOp9] at h
  s9_record h := by
    simp [genSkelOp9, P8Census.skeletonSubformula, ComputeTable.fanoutComp]

theorem genSkelOp9_slotSemantics
    (subject formula head fTail fTh fTt core arm result : Noun) (axis : ℕ)
    (hslot : Noun.slot axis core = some arm) :
    SkeletonSlotSemantics
      (genSkelOp9 subject formula head fTail fTh fTt core arm result axis) where
  s0_slot h := by
    simp [genSkelOp9] at h
  s9_slot _ := by
    rw [genSkelOp9_memoryAxis]
    simp [genSkelOp9, P8Census.skeletonSubformula, ComputeTable.fanoutComp]
    exact hslot

/-! ## Tree-wide via BFS rows -/

theorem genCompute_slotSemantics (t : NTree (GenComputeRow K))
    (h : ∀ g ∈ bfsRows t, SkeletonSlotSemantics g.skel) :
    ∀ s ∈ computeSkeletonRows (genComputeSemanticSkeleton t),
      SkeletonSlotSemantics s := by
  intro s hs
  rw [computeSkeletonRows_genCompute] at hs
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hs
  exact h n.label (List.mem_map.mpr ⟨n, hn, rfl⟩)

theorem genCompute_recordEquations (t : NTree (GenComputeRow K))
    (h : ∀ g ∈ bfsRows t, SkeletonRecordEquations g.skel) :
    ∀ s ∈ computeSkeletonRows (genComputeSemanticSkeleton t),
      SkeletonRecordEquations s := by
  intro s hs
  rw [computeSkeletonRows_genCompute] at hs
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hs
  exact h n.label (List.mem_map.mpr ⟨n, hn, rfl⟩)

/-- **The `bfsAssign` transport, for any predicate on skeletons.**

`bfsAssign` rewrites exponents and nothing else — `bfsLabelAt_skel` — so any property that reads
only `.skel` survives it. -/
theorem bfsAssign_computeSkeletonRows_of_bfsRows
    (P : ComputeRowSkeleton → Prop)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (h : ∀ g ∈ bfsRows t, P g.skel) :
    ∀ s ∈ computeSkeletonRows (genSemanticSkeleton (bfsAssign t) mf), P s := by
  intro s hs
  rw [computeSkeletonRows_genSemantic, computeSkeletonRows_genCompute] at hs
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hs
  have hlabels := bfsAssign_bfsForest_labels t
  have hmem : n.label ∈ (bfsForest [bfsAssign t]).map NTree.label :=
    List.mem_map.mpr ⟨n, hn, rfl⟩
  rw [hlabels] at hmem
  obtain ⟨i, hi, hlab⟩ := List.mem_map.mp hmem
  have hi' := lt_bfsRows_of_mem_range' hi
  have hskel : n.label.skel = (bfsRows t)[i - 1].skel := by
    rw [← hlab, bfsLabelAt_skel t i hi']
  rw [hskel]
  exact h _ (List.getElem_mem _)

theorem bfsAssign_computeSkeletonRows_slotSemantics
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (h : ∀ g ∈ bfsRows t, SkeletonSlotSemantics g.skel) :
    ∀ s ∈ computeSkeletonRows (genSemanticSkeleton (bfsAssign t) mf),
      SkeletonSlotSemantics s :=
  bfsAssign_computeSkeletonRows_of_bfsRows _ t mf h

theorem bfsAssign_computeSkeletonRows_recordEquations
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (h : ∀ g ∈ bfsRows t, SkeletonRecordEquations g.skel) :
    ∀ s ∈ computeSkeletonRows (genSemanticSkeleton (bfsAssign t) mf),
      SkeletonRecordEquations s :=
  bfsAssign_computeSkeletonRows_of_bfsRows _ t mf h

/-! ## Memory NMR extras feed `memoryAssemblyOf` -/

theorem bindMemory_axisNat {z : K} {s : MemoryRowSkeleton}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (hbind : BindMemoryRowA z s row)
    (hact : memoryMemRecKind s.state = .active) :
    ∃ n : ℕ, row.2.2.mem.axis = (n : K) := by
  have hrec : BindMemRec z (s.memoryRecord hact) row.2.2.mem := by
    simpa [BindMemoryRowA, hact] using hbind.2.2.2.2.2.1
  exact ⟨(s.memoryRecord hact).axis, hrec.2.2⟩

/-- Live memory-record timestamp is some `α^e`. -/
theorem timestampSpecializes_closed {α : K}
    {stamp : MemoryTimestampRow}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (htime : MemoryTimestampSpecializesAt α stamp row)
    (hact : memoryMemRecKind stamp.state = .active) :
    MemoryTimestampClosedAt α row.2.2.mem.ts := by
  refine ⟨stamp.recordExponent, ?_⟩
  have hts := htime.2.2.1
  simpa [hact] using hts

/-- The production inhabitant of `MemoryAssemblyPremises` from the two named
    NMR extras.  BFS-generated memory that supplies `axisNat`/`timestampClosed`
    (via `bindMemory_axisNat` / `timestampSpecializes_closed` on each live row)
    is consumed here without a second assembly -/
noncomputable def memoryAssemblyOfBFS {F : Type} [Field F] [Algebra F K]
    (E : BuildableNockExecution F K) (M : MemoryRecordPremises E) :
    MemoryAssemblyPremises E :=
  memoryAssemblyOf E M

theorem memoryAssemblyOfBFS_eq {F : Type} [Field F] [Algebra F K]
    (E : BuildableNockExecution F K) (M : MemoryRecordPremises E) :
    memoryAssemblyOfBFS E M = memoryAssemblyOf E M :=
  rfl

/-! ## Non-vacuity -/

theorem slot_two_cell (l r : Noun) :
    Noun.slot 2 (Noun.cell l r) = some l := by
  simp [Noun.slot]

theorem genSkelOp1_census_nonvacuous :
    SkeletonSlotSemantics (genSkelOp1 (.atom 0) (.atom 1) (.atom 0) (.atom 1)) ∧
      SkeletonRecordEquations
        (genSkelOp1 (.atom 0) (.atom 1) (.atom 0) (.atom 1)) :=
  ⟨genSkelOp1_slotSemantics _ _ _ _, genSkelOp1_recordEquations _ _ _ _⟩

theorem genSkelOp0_census_nonvacuous :
    let subject := Noun.cell (.atom 3) (.atom 4)
    SkeletonSlotSemantics (genSkelOp0 subject (.atom 0) (.atom 0) (.atom 0)
        (.atom 3) 2) ∧
      SkeletonRecordEquations (genSkelOp0 subject (.atom 0) (.atom 0) (.atom 0)
        (.atom 3) 2) :=
  ⟨genSkelOp0_slotSemantics _ _ _ _ _ _ (slot_two_cell _ _),
    genSkelOp0_recordEquations _ _ _ _ _ _⟩

theorem genSkelOp9_census_nonvacuous :
    let core := Noun.cell (.atom 1) (.atom 7)
    SkeletonSlotSemantics (genSkelOp9 (.atom 0) (.atom 9) (.atom 9) (.atom 0)
        (.atom 2) (.atom 0) core (.atom 1) (.atom 7) 2) ∧
      SkeletonRecordEquations (genSkelOp9 (.atom 0) (.atom 9) (.atom 9) (.atom 0)
        (.atom 2) (.atom 0) core (.atom 1) (.atom 7) 2) :=
  ⟨genSkelOp9_slotSemantics _ _ _ _ _ _ _ _ _ _ (slot_two_cell _ _),
    genSkelOp9_recordEquations _ _ _ _ _ _ _ _ _ _⟩

theorem genSkelCons_census_nonvacuous :
    SkeletonSlotSemantics (genSkelCons (.atom 0) (.atom 1) (.atom 2)
        (.atom 3) (.atom 4)) ∧
      SkeletonRecordEquations (genSkelCons (.atom 0) (.atom 1) (.atom 2)
        (.atom 3) (.atom 4)) :=
  ⟨genSkelCons_slotSemantics _ _ _ _ _, genSkelCons_recordEquations _ _ _ _ _⟩

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp0_slotSemantics
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp0_recordEquations
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp9_slotSemantics
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp9_recordEquations
#print axioms Nock.NockVMROM.Thm54.TraceGen.bfsAssign_computeSkeletonRows_of_bfsRows
#print axioms Nock.NockVMROM.Thm54.TraceGen.bfsAssign_computeSkeletonRows_slotSemantics
#print axioms Nock.NockVMROM.Thm54.TraceGen.bfsAssign_computeSkeletonRows_recordEquations
#print axioms Nock.NockVMROM.Thm54.TraceGen.bindMemory_axisNat
#print axioms Nock.NockVMROM.Thm54.TraceGen.timestampSpecializes_closed
#print axioms Nock.NockVMROM.Thm54.TraceGen.memoryAssemblyOfBFS
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp0_census_nonvacuous
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp9_census_nonvacuous
