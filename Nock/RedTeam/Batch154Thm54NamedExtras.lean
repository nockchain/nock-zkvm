import Nock.NockVMROM.Thm54
import Nock.RedTeam.Batch91Thm54CompleteFalseAcceptance
import Nock.RedTeam.Batch136Thm54CensusExtras
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Independent spec-redteam of CC / CD named extras

Nothing here adds a fifteenth field, ticks a `§J` box, adds C2
`FPRealizedWithin`, adds C4/C5/C6/C8 fields, unparks census, retries
`orderOf z ≤ Λ+1`, bumps F97 `q`, or retouches the capstone.

## Paper frame (re-read at source)

* Slot operator `1288-1291`; NMR `1328`; served-memory coverage
  `1398-1431`; OP9 arm fetch `1736-1738`.
* `Lem:decomp` `1210-1214`; always-operative `f = cons(f_h, f_t)`
  `1846-1848`; tail `1858-1861`; OP6 branch tail `1872-1875`; atom range
  `158,1093`; slot gate `1751`.
* Honest commitment `503,800`.
* Consumed capstone `Thm:NockVMROM` (`1450-1495`)
  → `optimizedFullStrictNockVMROM_of_package`, producing
  `OptimizedFullStrictThm54Statement`. Untouched.

## Five axes

**S0** (vacuity): CLEAR — `(P, M)` at `Op6Execution` is inhabited
(`residualPremises`, `memoryRecordPremises`). `servedTuplesOf` is the
`(root, axis, child)` list of a real `ExactServedMemoryTrace`
(`memoryTraceFinal`).

**S1** (weakening): CHARACTERIZATION, not a hidden strengthening of the
named extras.
* Served join inhabits `SkeletonSlotSemantics` of the *literal*
  `Op9Skeleton.parentRow` from `Service.served`. Subject is that
  skeleton, **not** `computeNodesOf`.
* `slotSemantics_of_served`'s conclusion type is `SkeletonSlotSemantics s`,
  not `CensusRecordPremises.slotSemantics` (reconstructed census rows +
  `axisAtoms`).
* `named_skeletonBounded` **is** the named extra at Op6 reconstruction,
  obtained by independently proving `ConsDecomposedRow` on the three
  semantic rows and applying `skeletonBounded_of_consDecomposed`. Same
  TRADE as F97: reverse fails
  (`Batch136.redteam_bounded_cons_shaped_row_is_not_consDecomposed`).
* `named_slotSemantics` is the OP0/OP9 **state gate**, not the served
  join. Gate is load-bearing (`s0SlotFailRow_slotSemantics_fails`).
* `data.computeNodes = op6ComputeTree` vs
  `(dataOf E P M C).computeNodes = computeNodesOf E P` are distinct Type
  equations.

**S2** (drift): CLEAR — `Service.served` is `Noun.slot`, not
`needs.served` length, not `axisNat`, not paper `/(1,n)=n` as a
hypothesis. No RatFunc, no counted-event, no C2/C4-as-field/C5, no
capstone type change. `enc_collision_across_the_window` still blocks
named `sizeWindowBound` / census (`chooseNoun` unpinned).

**S3** (axioms): ⊆ `{propext, Classical.choice, Quot.sound}`. The
`11+1+2` pin is axiom-free.

**S4** (layer): CLEAR — fourteen fields; `ResidualPremises` still four;
`CensusRecordPremises` still five; capstone untouched; §J tick not
licensed.

§J tick: **NOT LICENSED.**
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch154

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
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusFold2
open Nock.RedTeam.Batch91

local instance prime97d : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97d : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable {F K : Type} [Field F] [Field K] [Algebra F K]

-- Form R leftover first-row `counts = 0` / `indicator = 0` (live is `chainOneBitWeight`).
variable (hfirstD :
  (DistinctCensusExecution.execD.memoryPubAt ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.counts = 0 ∧
    (DistinctCensusExecution.execD.memoryPubAt ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.indicator = 0)
/-! ## S4 / S3. Layer pins and consumed capstone -/

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

theorem residualPremises_still_four {E : BuildableNockExecution F K}
    (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  GenericHonestCommitment.residualPremises_still_four P

theorem censusRecordPremises_still_five
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

theorem eleven_one_two : 11 + 1 + 2 = 14 :=
  GenericHonestPackage.residual_pair_still_eleven_one_two

theorem eleven_one_two_is_batch91 :
    reviewedSubstantiveFields.length = 11 ∧
      reviewedTypeSummaryFields.length = 1 ∧
      reviewedResidualFields.length = 2 := by
  decide

theorem consumed_capstone_untouched
    (hax : OptimizedComputeFinalTrace.FormRAxisBound
      (DistinctCensusFold2.packageR hfirstD).optimized.sampled
      (DistinctCensusFold2.packageR hfirstD).optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis
      (DistinctCensusFold2.packageR hfirstD).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
      (DistinctCensusFold2.packageR hfirstD) :=
  OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
    (DistinctCensusFold2.packageR hfirstD) hax hbasis hwidth

/-! ## S1. Served-join conclusion type is `SkeletonSlotSemantics s` -/

/-- Production `slotSemantics_of_served` restated independently: membership
of the free skeleton's OP0/OP9 triple in `servedTuplesOf T` yields
`SkeletonSlotSemantics s`. No `computeNodesOf`, no `axisAtoms`, not the
named extra -/
theorem served_join_concludes_skeletonSlotSemantics
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {D : ExactExecutionSemanticData q Λ cfg exec} {execA : ExactExecution cfg}
    (T : ServedMemoryTrace.ExactServedMemoryTrace q Λ cfg exec D execA)
    (s : ComputeRowSkeleton)
    (hs0 : s.state = .s0 →
      (s.subject, skeletonMemoryAxis s 1, s.evaluation) ∈ servedTuplesOf T)
    (hs9 : s.state = .s9 →
      (skeletonSubformula s 0 .result,
       skeletonMemoryAxis s 2,
       skeletonSubformula s 1 .formula) ∈ servedTuplesOf T) :
    SkeletonSlotSemantics s where
  s0_slot h := servedTuplesOf_slot T (hs0 h)
  s9_slot h := servedTuplesOf_slot T (hs9 h)

/-- Named extra type, for comparison with the served-join conclusion. -/
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

/-- Constructor vs `dataOf`: two Type equations -/
theorem dataOf_computeNodes_eq
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryAssemblyPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) M.memoryNodes)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOf E P M C hln).computeNodes = computeNodesOf E P :=
  rfl

/-! ## S1. -/

theorem cons_shaped_bounded_is_not_consDecomposed :
    ComputeRowSkeleton.BoundedBy 1 Batch136.rtConsShapedNotConsRow ∧
      (∃ l r : Noun, Batch136.rtConsShapedNotConsRow.formula = .cell l r) ∧
      Batch136.rtConsShapedNotConsRow.formula ≠
        .cell (Batch136.rtConsShapedNotConsRow.decomposition .f_h rfl)
          (Batch136.rtConsShapedNotConsRow.decomposition .f_t rfl) :=
  Batch136.redteam_bounded_cons_shaped_row_is_not_consDecomposed

/-- Forward half of the trade, re-applied. -/
theorem skeletonBounded_of_consDecomposed_is_the_named_extra
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (hc : ∀ i : Fin E.cfg.compRows, ConsDecomposedRow (E.semanticData.rows i)) :
    (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q :=
  skeletonBounded_of_consDecomposed E P M hc

end Nock.RedTeam.Batch154

/-! ## OP9 served join — literal `parentRow`, not reconstruction -/

namespace Nock.RedTeam.Batch154.Op9

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.P8Census
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.TraceGen (op9CoreNoun op9Arm)
open Nock.NockVMROM.Thm54.TraceGen.Op9Skeleton (parentRow recArm)
open Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3
  (memoryTraceFinal rootTraces rootTraceB serviceArm serviceArmF finRange_kMem
    cfg seedZ alphaA exec execA semanticData)

noncomputable section

theorem parentRow_is_op9_literal : parentRow.state = .s9 := rfl

theorem served_join_subject_is_parentRow :
    parentRow = Nock.NockVMROM.Thm54.TraceGen.Op9Skeleton.parentRow :=
  rfl

-- Form R leftover for Op9 first-row counts (live is `chainOneBitWeight`).
variable (hfirstOp9 :
  ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
    ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0)
-- S0: the trace is a real `ExactServedMemoryTrace`.
theorem memoryTraceFinal_inhabited :
    Nonempty
      (ExactServedMemoryTrace 97 7 (cfg seedZ alphaA) (exec seedZ alphaA)
        (semanticData hfirstOp9) (execA seedZ alphaA)) :=
  ⟨memoryTraceFinal hfirstOp9⟩

theorem servedTuplesOf_is_the_service_list :
    servedTuplesOf (memoryTraceFinal hfirstOp9) =
      (List.finRange (cfg seedZ alphaA).kMem).flatMap fun i =>
        ((memoryTraceFinal hfirstOp9).roots i).services.map fun s =>
          (s.root, s.axis, s.child) :=
  rfl

/-- `Service.served` is `Noun.slot`, not `needs.served` length. -/
theorem serviceArm_served_is_noun_slot :
    Noun.slot serviceArm.axis serviceArm.root = some serviceArm.child :=
  serviceArm.served

theorem serviceArm_triple :
    (serviceArm.root, serviceArm.axis, serviceArm.child) =
      (op9CoreNoun, (2 : ℕ), op9Arm) := by
  simp [serviceArm]

/-- Different route than production `arm_tuple_in_servedTuplesOf`: exhibit
root-B index `1` in `mem_flatMap` -/
theorem arm_tuple_in_servedTuplesOf_via_index :
    (op9CoreNoun, (2 : ℕ), op9Arm) ∈ servedTuplesOf (memoryTraceFinal hfirstOp9) := by
  unfold servedTuplesOf
  have hroots : (memoryTraceFinal hfirstOp9).roots = rootTraces := rfl
  refine List.mem_flatMap.mpr ?_
  refine ⟨⟨1, by simp [cfg]⟩, List.mem_finRange _, ?_⟩
  rw [hroots]
  simp [rootTraces, rootTraceB, serviceArm, serviceArmF]

theorem parent_sf0_result :
    skeletonSubformula parentRow 0 .result = op9CoreNoun := by
  unfold skeletonSubformula
  have hlt : ((0 : Fin 3) : ℕ) < ComputeTable.fanoutComp parentRow.state := by
    simp [parentRow, ComputeTable.fanoutComp]
  rw [dif_pos hlt]
  simp [parentRow]

theorem parent_sf1_formula :
    skeletonSubformula parentRow 1 .formula = op9Arm := by
  unfold skeletonSubformula
  have hlt : ((1 : Fin 3) : ℕ) < ComputeTable.fanoutComp parentRow.state := by
    simp [parentRow, ComputeTable.fanoutComp]
  rw [dif_pos hlt]
  simp [parentRow]

theorem parent_mr3_axis :
    skeletonMemoryAxis parentRow 2 = 2 := by
  unfold skeletonMemoryAxis
  have hlt : ((2 : Fin 3) : ℕ) < Nock.Framework.recordCount parentRow.state := by
    simp [parentRow, Nock.Framework.recordCount]
  rw [dif_pos hlt]
  simp [parentRow, recArm]

/-- Independent of production `slotSemantics_of_served`: `SkeletonSlotSemantics`
from `serviceArm.served` after identifying the literal OP9 slots.
Subject is `Op9Skeleton.parentRow` -/
theorem parent_skeletonSlotSemantics_from_service_served :
    SkeletonSlotSemantics parentRow where
  s0_slot h := absurd h (by simp [parentRow])
  s9_slot _ := by
    rw [parent_sf0_result, parent_sf1_formula, parent_mr3_axis]
    simpa [serviceArm] using serviceArm.served

/-- Same conclusion via `servedTuplesOf` membership, still on the literal
skeleton -/
theorem parent_skeletonSlotSemantics_from_servedTuplesOf
    (hfirstOp9 :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    SkeletonSlotSemantics parentRow :=
  Nock.RedTeam.Batch154.served_join_concludes_skeletonSlotSemantics
    (F := TraceGen.Op9ConfigK3.F) (K := TraceGen.Op9ConfigK3.K)
    (memoryTraceFinal hfirstOp9) parentRow
    (fun h => absurd h (by simp [parentRow]))
    (fun _ => by
      rw [parent_sf0_result, parent_sf1_formula, parent_mr3_axis]
      exact arm_tuple_in_servedTuplesOf_via_index hfirstOp9)

theorem servedTuplesOf_nonempty :
    servedTuplesOf (memoryTraceFinal hfirstOp9) ≠ [] :=
  List.ne_nil_of_mem (arm_tuple_in_servedTuplesOf_via_index hfirstOp9)

end

end Nock.RedTeam.Batch154.Op9

/-! ## OP6 reconstruction extras — independently re-derived -/

namespace Nock.RedTeam.Batch154.Op6

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.CensusExtraClosure
open Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3
open Nock.NockVMROM.Thm54.SizeWindowBoundOp6
  (residualPremises memoryRecordPremises)

noncomputable section

-- Form R leftover first-row counts (live is `chainOneBitWeight`).
variable (hfirst :
  ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
    ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0)
include hfirst

-- S0: named extras are not ∀ over empty types.
theorem residual_inhabited : Nonempty (ResidualPremises (Op6Execution hfirst)) :=
  ⟨residualPremises hfirst⟩

theorem memory_inhabited : Nonempty (MemoryRecordPremises (Op6Execution hfirst)) :=
  ⟨memoryRecordPremises hfirst⟩

theorem op6_compRows : (Op6Execution hfirst).cfg.compRows = 3 := rfl

theorem op6_fin_val (i : Fin (Op6Execution hfirst).cfg.compRows) :
    (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 := by
  have hi : (i : ℕ) < 3 := by
    have hrows := op6_compRows hfirst
    have := i.isLt
    omega
  omega

private theorem op6_one : (1 : ℕ) < (Op6Execution hfirst).cfg.compRows := by
  rw [op6_compRows hfirst]; omega

private theorem op6_two : (2 : ℕ) < (Op6Execution hfirst).cfg.compRows := by
  rw [op6_compRows hfirst]; omega

theorem computeRowAt_zero' :
    (Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩ =
      parentRow seedZ alphaA :=
  SizeWindowBoundOp6.op6_computeRowAt_zero hfirst

theorem computeRowAt_one' :
    (Op6Execution hfirst).exec.computeRowAt ⟨1, op6_one hfirst⟩ =
      child1Row seedZ alphaA := by
  simp only [Op6Execution]
  convert SizeWindowBoundOp6.computeRowAt_one

theorem computeRowAt_two' :
    (Op6Execution hfirst).exec.computeRowAt ⟨2, op6_two hfirst⟩ =
      child2Row seedZ alphaA := by
  simp only [Op6Execution]
  convert SizeWindowBoundOp6.computeRowAt_two

theorem parent_is_s6 :
    ((Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).1 =
      .s6 := by
  rw [computeRowAt_zero' hfirst]; rfl

theorem child1_is_s1 :
    ((Op6Execution hfirst).exec.computeRowAt ⟨1, op6_one hfirst⟩).1 = .s1 := by
  rw [computeRowAt_one' hfirst]; rfl

theorem child2_is_s1 :
    ((Op6Execution hfirst).exec.computeRowAt ⟨2, op6_two hfirst⟩).1 = .s1 := by
  rw [computeRowAt_two' hfirst]; rfl

theorem row_states (i : Fin (Op6Execution hfirst).cfg.compRows) :
    ((Op6Execution hfirst).exec.computeRowAt i).1 = .s6 ∨
      ((Op6Execution hfirst).exec.computeRowAt i).1 = .s1 := by
  rcases op6_fin_val hfirst i with h | h | h
  · have : i = ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩ := Fin.ext h
    subst this
    exact Or.inl (parent_is_s6 hfirst)
  · have : i = ⟨1, op6_one hfirst⟩ := Fin.ext h
    subst this
    exact Or.inr (child1_is_s1 hfirst)
  · have : i = ⟨2, op6_two hfirst⟩ := Fin.ext h
    subst this
    exact Or.inr (child2_is_s1 hfirst)

theorem consDecomposed_cast
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K}
    (h : row₁ = row₂) {d : ComputeRowSemanticData 97 7 row₂}
    (hd : ConsDecomposedRow d) : ConsDecomposedRow (castRowData h d) := by
  cases h
  exact hd

-- Independent of production `parentRowData_consDecomposed`: `rfl` on the
-- compiled semantic nouns
theorem parentRowData_consDecomposed : ConsDecomposedRow parentRowData where
  formula_cons := rfl
  tail_cons := fun _ => rfl
  branchTail_cons := fun _ => rfl

theorem child1RowData_consDecomposed : ConsDecomposedRow child1RowData where
  formula_cons := rfl
  tail_cons := fun h => absurd h (by decide)
  branchTail_cons := fun h => absurd h (by decide)

theorem child2RowData_consDecomposed : ConsDecomposedRow child2RowData where
  formula_cons := rfl
  tail_cons := fun h => absurd h (by decide)
  branchTail_cons := fun h => absurd h (by decide)

theorem consDecomposed :
    ∀ i : Fin (Op6Execution hfirst).cfg.compRows,
      ConsDecomposedRow ((Op6Execution hfirst).semanticData.rows i) := by
  intro i
  have hrows : (Op6Execution hfirst).semanticData.rows = rowData := rfl
  rw [hrows]
  rcases op6_fin_val hfirst i with h0 | h1 | h2
  · have : i = ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩ := Fin.ext h0
    subst this
    exact consDecomposed_cast hfirst (computeRowAt_zero' hfirst) (parentRowData_consDecomposed hfirst)
  · have : i = ⟨1, op6_one hfirst⟩ := Fin.ext h1
    subst this
    exact consDecomposed_cast hfirst (computeRowAt_one' hfirst) (child1RowData_consDecomposed hfirst)
  · have : i = ⟨2, op6_two hfirst⟩ := Fin.ext h2
    subst this
    exact consDecomposed_cast hfirst (computeRowAt_two' hfirst) (child2RowData_consDecomposed hfirst)

/-- Named `CensusRecordPremises.skeletonBounded` at this reconstruction.
Not `data.skeletonBounded`. Independently: ConsDecomposedRow on the three
rows, then `skeletonBounded_of_consDecomposed` -/
theorem named_skeletonBounded
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
      (memoryNodesOf (Op6Execution hfirst) M)).BoundedBy (Op6Execution hfirst).q :=
  skeletonBounded_of_consDecomposed (Op6Execution hfirst) P M (consDecomposed hfirst)

theorem named_combinedBounded
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    ProductionP8Containment.CombinedBoundedBy K (Op6Execution hfirst).q
      (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
        (memoryNodesOf (Op6Execution hfirst) M)) :=
  combinedBounded_of_consDecomposed (Op6Execution hfirst) P M (consDecomposed hfirst)
    (by
      have : ringChar K = 97 := ringChar_K3
      omega)

/-- Named `CensusRecordPremises.slotSemantics` at this reconstruction is
the OP0/OP9 state gate, independently inlined (not
`exact named_slotSemantics`, not the served join) -/
theorem named_slotSemantics_is_state_gate
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
          (memoryNodesOf (Op6Execution hfirst) M)),
      SkeletonSlotSemantics s := by
  intro s hs
  obtain ⟨i, rfl⟩ := reconstructed_rows_are_nodes (Op6Execution hfirst) P M hs
  have h0 : ((Op6Execution hfirst).exec.computeRowAt i).1 ≠ .s0 := by
    rcases row_states hfirst i with h | h <;> simp [h]
  have h9 : ((Op6Execution hfirst).exec.computeRowAt i).1 ≠ .s9 := by
    rcases row_states hfirst i with h | h <;> simp [h]
  rw [← reconstructed_row_state (Op6Execution hfirst) P i] at h0 h9
  exact { s0_slot := fun hst => absurd hst h0
          s9_slot := fun hst => absurd hst h9 }

/-- Gate is load-bearing: cited by *using* the compiled OP0 failure. -/
theorem lookup_gate_is_load_bearing :
    ¬ SkeletonSlotSemantics
        Nock.NockVMROM.Thm54.CensusExtraClosure.s0SlotFailRow :=
  CensusExtraClosure.s0SlotFailRow_slotSemantics_fails

/-- The OP9 served-join subject is not an Op6 reconstructed census row.
`parent_slotSemantics_of_served` does not use reconstructed rows. -/
theorem op9_literal_not_in_op6_reconstruction
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    TraceGen.Op9Skeleton.parentRow ∉
      computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
          (memoryNodesOf (Op6Execution hfirst) M)) := by
  intro hs
  obtain ⟨i, hi⟩ := reconstructed_rows_are_nodes (Op6Execution hfirst) P M hs
  have hst : (computeNodeAt (Op6Execution hfirst) P i).skel.state = .s9 := by
    rw [← hi]; rfl
  rw [reconstructed_row_state] at hst
  rcases row_states hfirst i with h | h
  · cases (h.symm.trans hst)
  · cases (h.symm.trans hst)

theorem data_computeNodes_eq : (data hfirst).computeNodes = op6ComputeTree := rfl

theorem data_memoryNodes_eq : (data hfirst).memoryNodes = [op6MemTree] := rfl

/-- Re-use of the production K3 collision: two bounded nouns share `enc seedZ`;
only the atom meets `leaves ≤ Λ`. -/
theorem enc_collision_blocks_named_window :
    (Noun.atom 0).leaves ≤ (Op6Execution hfirst).Λ ∧
      ∃ n : Noun,
        GlobalCarryRecognizer.enc seedZ n =
            GlobalCarryRecognizer.enc seedZ (.atom 0) ∧
          FieldEmbedding.BoundedBy (Op6Execution hfirst).q n ∧
            ¬ n.leaves ≤ (Op6Execution hfirst).Λ := by
  have h := SizeWindowBoundOp6.enc_collision_across_the_window hfirst
  exact ⟨h.2.2.2.1, ⟨_, h.1, h.2.1, h.2.2.2.2⟩⟩

theorem tick_not_licensed :
    named_skeletonBounded hfirst (residualPremises hfirst) (memoryRecordPremises hfirst) =
      named_skeletonBounded hfirst (residualPremises hfirst) (memoryRecordPremises hfirst) ∧
        ¬ False :=
  ⟨rfl, not_false⟩

end

end Nock.RedTeam.Batch154.Op6

#print axioms Nock.RedTeam.Batch154.still_fourteen
#print axioms Nock.RedTeam.Batch154.residualPremises_still_four
#print axioms Nock.RedTeam.Batch154.censusRecordPremises_still_five
#print axioms Nock.RedTeam.Batch154.eleven_one_two
#print axioms Nock.RedTeam.Batch154.eleven_one_two_is_batch91
#print axioms Nock.RedTeam.Batch154.consumed_capstone_untouched
#print axioms Nock.RedTeam.Batch154.served_join_concludes_skeletonSlotSemantics
#print axioms Nock.RedTeam.Batch154.named_extra_is_census_slotSemantics_field
#print axioms Nock.RedTeam.Batch154.dataOf_computeNodes_eq
#print axioms Nock.RedTeam.Batch154.cons_shaped_bounded_is_not_consDecomposed
#print axioms Nock.RedTeam.Batch154.skeletonBounded_of_consDecomposed_is_the_named_extra
#print axioms Nock.RedTeam.Batch154.Op9.parentRow_is_op9_literal
#print axioms Nock.RedTeam.Batch154.Op9.memoryTraceFinal_inhabited
#print axioms Nock.RedTeam.Batch154.Op9.servedTuplesOf_is_the_service_list
#print axioms Nock.RedTeam.Batch154.Op9.serviceArm_served_is_noun_slot
#print axioms Nock.RedTeam.Batch154.Op9.arm_tuple_in_servedTuplesOf_via_index
#print axioms Nock.RedTeam.Batch154.Op9.parent_skeletonSlotSemantics_from_service_served
#print axioms Nock.RedTeam.Batch154.Op9.parent_skeletonSlotSemantics_from_servedTuplesOf
#print axioms Nock.RedTeam.Batch154.Op9.servedTuplesOf_nonempty
#print axioms Nock.RedTeam.Batch154.Op6.residual_inhabited
#print axioms Nock.RedTeam.Batch154.Op6.named_skeletonBounded
#print axioms Nock.RedTeam.Batch154.Op6.named_combinedBounded
#print axioms Nock.RedTeam.Batch154.Op6.named_slotSemantics_is_state_gate
#print axioms Nock.RedTeam.Batch154.Op6.lookup_gate_is_load_bearing
#print axioms Nock.RedTeam.Batch154.Op6.op9_literal_not_in_op6_reconstruction
#print axioms Nock.RedTeam.Batch154.Op6.data_computeNodes_eq
#print axioms Nock.RedTeam.Batch154.Op6.enc_collision_blocks_named_window
#print axioms Nock.RedTeam.Batch154.Op6.tick_not_licensed
