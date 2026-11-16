/-
  Nock/NockVMROM/Thm54/SizeWindowBoundOp6.lean

  `sizeWindowBound` at a real OP6 execution, scope stated before any edit.

  Scope (in force for this module; nothing wider is claimed).
  * Execution: `(Op6Execution hfirst)`, the already-compiled `BuildableNockExecution` over
    `K3` for `*[0 [6 [[1 0] [[1 5] [1 6]]]]] = 5`.
    Parent compute row is `.s6`. `Λ = 7`.
  * Honest-noun extra: `HonestCommitment.Data.sizeWindowBound` on the literal-node
    skeleton `skeletonOfNodes (data hfirst).computeNodes (data hfirst).memoryNodes`. Already compiled
    in `Op6DataK3`; re-stated so the gated-opcode inhabitant is named.
  * Named extra: `CensusRecordPremises.sizeWindowBound`, i.e.
    `SizeWindowNounsBoundedBy (skeletonOfNodes (computeNodesOf E P)
    (memoryNodesOf E M)) E.Λ`. Reduced here to the leaves of one reconstructed
    subformula (`sf2_e` of the `.s6` parent). That slot is `subformulaNoun` /
    `Classical.choose` of `FPRealized` (`CensusExtraClosure` §G.1). The honest
    condition-result is `.atom 0` (`op6CondResult`). Closing the named extra from
    the recorded facts about `chooseNoun` is the declined C2 non-carrier route
    (`Batch137.redteam_c2_noncarrier_route_blocked`).
  * Inhabitation: `ResidualPremises` and `MemoryRecordPremises` at this execution
    are compiled, so the named type is not a `∀` over an empty type.
    * Not done at module open: named reconstruction extra is discharged below
    by preferring a windowed `chooseNoun` when one exists (`FPRealizedWithin` as
    a *selector*, not a `NounRealization` field). Named `census` is inhabited at
    the same written scope via `RowLeafWindow` + `RowCellIdentities`. No
    `orderOf z ≤ Λ+1`; no fifteenth execution field; capstone untouched;
    `Gen.lean` / `BFSAssign.lean` not touched.

  Also in this leaf (not a size-window tick; scopes written at the decls):
  * Item 2 fixture: `SlotSemanticsServedOp9` instantiates
    `ServedLookupBridge.slotSemantics_of_served` at `Op9ConfigK3.memoryTraceFinal`
    and the literal `Op9Skeleton.parentRow` (`.s9`). Not the named reconstruction
    extra; `axisAtoms` stays parked. §J.2 `slotSemantics` is now ticked at the
    reconstructed `Op9Execution` in `SlotSemanticsOp9.lean`.
  * Item 3: `data_is_literal_node_constructor` vs `dataOf_commits_reconstructed`.

  Paper: window the paper (at `1097`); consumer `1188-1204` (`1198`);
  OP6 type-read of `sf_evaluation_2` at `1777`, prose `1710,1714`.
-/
import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.TraceGen.Op6DataK3
import Nock.NockVMROM.Thm54.TraceGen.Op9LanguageK3
import Nock.NockVMROM.Thm54.TraceGen.Op9SkeletonK3
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.GroupTheory.OrderOfElement

namespace Nock.NockVMROM.Thm54.SizeWindowBoundOp6

open scoped Classical
open Nock Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3
open Nock.NockVMROM.Thm54.CensusExtraClosure

noncomputable section

variable (hfirst :
  ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
    ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0)

omit hfirst in private theorem zero_lt_comp : (0 : ℕ) < (cfg seedZ alphaA).compRows := by decide
omit hfirst in private theorem one_lt_comp : (1 : ℕ) < (cfg seedZ alphaA).compRows := by decide
omit hfirst in private theorem two_lt_comp : (2 : ℕ) < (cfg seedZ alphaA).compRows := by decide

/-! ## The execution contains an OP6 row -/

theorem computeRowAt_zero :
    (exec seedZ alphaA).computeRowAt ⟨0, zero_lt_comp⟩ = parentRow seedZ alphaA := by
  simp [ExactExecution.computeRowAt, computeRows_eq]

theorem computeRowAt_one :
    (exec seedZ alphaA).computeRowAt ⟨1, one_lt_comp⟩ = child1Row seedZ alphaA := by
  simp [ExactExecution.computeRowAt, computeRows_eq]

theorem computeRowAt_two :
    (exec seedZ alphaA).computeRowAt ⟨2, two_lt_comp⟩ = child2Row seedZ alphaA := by
  simp [ExactExecution.computeRowAt, computeRows_eq]

theorem op6_computeRowAt_zero :
    (Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩ =
      parentRow seedZ alphaA := by
  exact computeRowAt_zero

/-- Parent row is `.s6`. This is the load-bearing witness that the state gate
does not apply -/
theorem parent_is_s6 :
    ((Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).1 = .s6 := by
  rw [op6_computeRowAt_zero]; rfl

theorem window_state_gate_fails :
    ¬ ∀ i : Fin (Op6Execution hfirst).cfg.compRows,
      ((Op6Execution hfirst).exec.computeRowAt i).1 ≠ .s3 ∧
        ((Op6Execution hfirst).exec.computeRowAt i).1 ≠ .s4 ∧
          ((Op6Execution hfirst).exec.computeRowAt i).1 ≠ .s6 := by
  intro h
  exact (h ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).2.2 (parent_is_s6 hfirst)

/-! ## Honest-noun extra on the literal-node commitment -/

/-- Already compiled as `(data hfirst).sizeWindowBound`. The window noun is the 1-leaf
condition result `op6CondResult =.atom 0`. This is `SizeWindowNounsBoundedBy` on
`Data`'s skeleton, not on `computeNodesOf E P` -/
theorem data_sizeWindowBound :
    SizeWindowCounting.SizeWindowNounsBoundedBy (data hfirst).skeleton (data hfirst).Λ :=
  (data hfirst).sizeWindowBound

theorem data_Lambda_eq : (data hfirst).Λ = (Op6Execution hfirst).Λ := rfl

private theorem op6_one : (1 : ℕ) < (Op6Execution hfirst).cfg.compRows := by
  change (1 : ℕ) < (cfg seedZ alphaA).compRows
  exact one_lt_comp

private theorem op6_two : (2 : ℕ) < (Op6Execution hfirst).cfg.compRows := by
  change (2 : ℕ) < (cfg seedZ alphaA).compRows
  exact two_lt_comp

theorem condResult_leaves_le_Lambda :
    Noun.leaves (.atom 0) ≤ (Op6Execution hfirst).Λ := by
  change Noun.leaves (.atom 0) ≤ 7
  decide

theorem parentCall2_is_the_window_noun :
    parentCall2.result = .atom 0 := by
  change TraceGen.op6CondResult = .atom 0
  rfl

/-! ## `ResidualPremises` / `MemoryRecordPremises` at this execution -/

private theorem fin_val_le_two (i : Fin (Op6Execution hfirst).cfg.compRows) :
    (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 := by
  have hrows : (Op6Execution hfirst).cfg.compRows = 3 := rfl
  have hi : (i : ℕ) < 3 := by
    rw [← hrows]
    exact i.isLt
  omega

theorem row_states (i : Fin (Op6Execution hfirst).cfg.compRows) :
    ((Op6Execution hfirst).exec.computeRowAt i).1 = .s6 ∨
      ((Op6Execution hfirst).exec.computeRowAt i).1 = .s1 := by
  rcases fin_val_le_two hfirst i with h | h | h
  · have : i = ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩ := Fin.ext h
    subst this
    exact Or.inl (parent_is_s6 hfirst)
  · have : i = ⟨1, one_lt_comp⟩ := Fin.ext h
    subst this
    refine Or.inr ?_
    have hs : ((exec seedZ alphaA).computeRowAt ⟨1, one_lt_comp⟩).1 = .s1 := by
      rw [computeRowAt_one]; rfl
    exact hs
  · have : i = ⟨2, two_lt_comp⟩ := Fin.ext h
    subst this
    refine Or.inr ?_
    have hs : ((exec seedZ alphaA).computeRowAt ⟨2, two_lt_comp⟩).1 = .s1 := by
      rw [computeRowAt_two]; rfl
    exact hs

def residualPremises : ResidualPremises (Op6Execution hfirst) where
  inactiveDec := trivial
  axisAtoms := by
    intro i
    refine ⟨?_, ?_⟩ <;> intro h <;>
      rcases row_states hfirst i with hs | hs <;> rw [hs] at h <;>
        exact absurd h (by decide)
  q_eq_ringChar := by
    change (97 : ℕ) = ringChar TraceGen.Op6ConfigK3.K
    exact ringChar_K3.symm

theorem timestampClosed :
    ∀ i : Fin (Op6Execution hfirst).cfg.memRows,
      memoryMemRecKind ((Op6Execution hfirst).exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt (Op6Execution hfirst).cfg.challenges.α
          ((Op6Execution hfirst).exec.memoryRowAt i).2.2.mem.ts := by
  intro i hact
  have hmem : (Op6Execution hfirst).exec.memoryRowAt i ∈ (exec seedZ alphaA).memoryRows := by
    exact ExactExecution.memoryRowAt_mem (exec seedZ alphaA) i
  rw [TraceGen.Op6ConfigK3.memoryRows_eq] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h
  · rw [h]; exact ⟨1, by simp [Op6Execution, lblOf, pReadF, readPub, recF, cfg]⟩
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h]; exact ⟨1, by simp [Op6Execution, lblOf, pVerifyF, verifyPub, recF, cfg]⟩
  · rw [h]; exact ⟨2, by simp [Op6Execution, lblOf, pReadT, readPub, recT, cfg]⟩
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h]; exact ⟨2, by simp [Op6Execution, lblOf, pVerifyT, verifyPub, recT, cfg]⟩
  · rw [h]; exact ⟨3, by simp [Op6Execution, lblOf, pReadP, readPub, recP, cfg]⟩
  · rw [h]; exact ⟨5, by simp [Op6Execution, lblOf, pReadC2, readPub, recC2, cfg]⟩
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h]; exact ⟨3, by simp [Op6Execution, lblOf, pVerifyP, verifyPub, recP, cfg]⟩
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h]; exact ⟨5, by simp [Op6Execution, lblOf, pVerifyC2, verifyPub, recC2, cfg]⟩
  · rw [h]; exact ⟨4, by simp [Op6Execution, lblOf, pReadC1, readPub, recC1, cfg]⟩
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h] at hact; exact absurd hact (by decide)
  · rw [h]; exact ⟨4, by simp [Op6Execution, lblOf, pVerifyC1, verifyPub, recC1, cfg]⟩
  · rw [h] at hact; exact absurd hact (by decide)

def memoryRecordPremises : MemoryRecordPremises (Op6Execution hfirst) :=
  memoryRecordPremises_of_timestampClosed (Op6Execution hfirst) (timestampClosed hfirst) honestVer

/-! ## Named extra reduces to one reconstructed subformula -/

theorem reconstructed_parent_state (P : ResidualPremises (Op6Execution hfirst)) :
    ((computeNodeAt (Op6Execution hfirst) P ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel).state = .s6 := by
  rw [reconstructed_row_state, parent_is_s6]

theorem reconstructed_child1_state (P : ResidualPremises (Op6Execution hfirst)) :
    ((computeNodeAt (Op6Execution hfirst) P ⟨1, one_lt_comp⟩).skel).state = .s1 := by
  rw [reconstructed_row_state]
  have hs : ((exec seedZ alphaA).computeRowAt ⟨1, one_lt_comp⟩).1 = .s1 := by
    rw [computeRowAt_one]; rfl
  exact hs

theorem reconstructed_child2_state (P : ResidualPremises (Op6Execution hfirst)) :
    ((computeNodeAt (Op6Execution hfirst) P ⟨2, two_lt_comp⟩).skel).state = .s1 := by
  rw [reconstructed_row_state]
  have hs : ((exec seedZ alphaA).computeRowAt ⟨2, two_lt_comp⟩).1 = .s1 := by
    rw [computeRowAt_two]; rfl
  exact hs

private theorem parent_skel_mem
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    (computeNodeAt (Op6Execution hfirst) P ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel ∈
      computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
          (memoryNodesOf (Op6Execution hfirst) M)) := by
  rw [computeSkeletonRows_of_assembly (Op6Execution hfirst) P M]
  refine List.mem_map.mpr ⟨1, ?mem, ?eq⟩
  · have hlen : (bfsForest [(Op6Execution hfirst).exec.computeTree]).length =
        (Op6Execution hfirst).cfg.compRows := (Op6Execution hfirst).exec.compute_bfs_length
    rw [hlen, List.mem_range']
    refine ⟨0, (Op6Execution hfirst).cfg.compRows_pos, ?_⟩
    simp
  · exact congrArg ComputeNode.skel
      (computeLabelAt_of_index (Op6Execution hfirst) P (i := 1) (Op6Execution hfirst).cfg.compRows_pos)

/-- The named `CensusRecordPremises.sizeWindowBound` extra at this OP6 execution
is the leaf bound on the reconstructed parent `sf2` result — `subformulaNoun`, a
`Classical.choose` witness of `FPRealized` -/
theorem named_sizeWindowBound_iff_sf2_result
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
          (memoryNodesOf (Op6Execution hfirst) M)) (Op6Execution hfirst).Λ ↔
      (P8Census.skeletonSubformula
          (computeNodeAt (Op6Execution hfirst) P ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel
          ⟨1, by decide⟩ .result).leaves ≤ (Op6Execution hfirst).Λ := by
  constructor
  · intro h
    exact h _ (by
      rw [SizeWindowCounting.skeletonSizeWindowNouns, List.mem_flatMap]
      refine ⟨_, parent_skel_mem hfirst P M, ?_⟩
      simp [SizeWindowCounting.requiredSizeWindowNouns, reconstructed_parent_state hfirst])
  · intro hleaf n hn
    rw [SizeWindowCounting.skeletonSizeWindowNouns, List.mem_flatMap] at hn
    obtain ⟨s, hs, hns⟩ := hn
    obtain ⟨i, rfl⟩ := reconstructed_rows_are_nodes (Op6Execution hfirst) P M hs
    rcases fin_val_le_two hfirst i with h | h | h
    · have : i = ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩ := Fin.ext h
      subst this
      have hreq :
          SizeWindowCounting.requiredSizeWindowNouns
              (computeNodeAt (Op6Execution hfirst) P ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel =
            [P8Census.skeletonSubformula
              (computeNodeAt (Op6Execution hfirst) P ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel
              ⟨1, by decide⟩ .result] := by
        simp [SizeWindowCounting.requiredSizeWindowNouns, reconstructed_parent_state hfirst,
          P8Census.skeletonSubformula]
      simp [hreq] at hns
      rwa [hns]
    · have : i = ⟨1, one_lt_comp⟩ := Fin.ext h
      subst this
      have hempty : SizeWindowCounting.requiredSizeWindowNouns
          (computeNodeAt (Op6Execution hfirst) P ⟨1, one_lt_comp⟩).skel = [] := by
        simp [SizeWindowCounting.requiredSizeWindowNouns, reconstructed_child1_state]
      simp [hempty] at hns
    · have : i = ⟨2, two_lt_comp⟩ := Fin.ext h
      subst this
      have hempty : SizeWindowCounting.requiredSizeWindowNouns
          (computeNodeAt (Op6Execution hfirst) P ⟨2, two_lt_comp⟩).skel = [] := by
        simp [SizeWindowCounting.requiredSizeWindowNouns, reconstructed_child2_state]
      simp [hempty] at hns

/-- The reconstructed OP6 window noun encodes to the honest condition result.
That does not pin its leaf count: `chooseNoun` is characterised only up to `enc`
and `BoundedBy q` (`reconstructed_subformulaNoun_properties`) -/
theorem reconstructed_sf2_encodes_condResult (P : ResidualPremises (Op6Execution hfirst)) :
    GlobalCarryRecognizer.enc seedZ
        ((computeNodeAt (Op6Execution hfirst) P ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel.subformula
          ⟨1, by decide⟩
          (by
            change (1 : ℕ) < ComputeTable.fanoutComp
              ((computeNodeAt (Op6Execution hfirst) P ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel).state
            rw [reconstructed_parent_state hfirst P]
            decide)
          .result) =
      GlobalCarryRecognizer.enc seedZ (.atom 0) := by
  simp only [computeNodeAt, computeNodeOf, computeSkeletonOf]
  have hi : (1 : ℕ) < ComputeTable.fanoutComp
      ((Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).1 := by
    rw [op6_computeRowAt_zero]
    decide
  have henc := subformulaNounOf_enc
    ((Op6Execution hfirst).semanticData.rows ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩)
    (publicRowNoun_of_execution (Op6Execution hfirst) ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩)
    ⟨1, by decide⟩ hi TripleSlot.result
  have hz : ((Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).2.1.z =
      seedZ := by
    rw [same_z (Op6Execution hfirst) ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩]
    rfl
  rw [hz] at henc
  simpa [op6_computeRowAt_zero, SemanticStrategy.tripleFP, computeSubformulaFPs,
    ComputeTable.sfTriple, parentRow, parentPub, fp, TraceGen.op6CondResult] using henc

theorem condResult_bounded :
    FieldEmbedding.BoundedBy (Op6Execution hfirst).q (.atom 0) := by
  change FieldEmbedding.BoundedBy (97 : ℕ) (.atom 0)
  decide

/-- The parent `sf2` result fingerprint is `enc seedZ (.atom 0)`. -/
theorem parent_sf2_result_fp :
    SemanticStrategy.tripleFP
        (computeSubformulaFPs
          ((Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).2.2.1
          1)
        TripleSlot.result =
      GlobalCarryRecognizer.enc seedZ (.atom 0) := by
  rw [op6_computeRowAt_zero]
  simp [SemanticStrategy.tripleFP, computeSubformulaFPs, ComputeTable.sfTriple,
    parentRow, parentPub, fp, TraceGen.op6CondResult]

/-- Atom `0` is a `NockProgram^Λ` realizer of the window fingerprint.
Not designed C2 as a `NounRealization` field -/
theorem sf2_fp_realized_within :
    FPRealizedWithin seedZ (Op6Execution hfirst).q (Op6Execution hfirst).Λ
      (SemanticStrategy.tripleFP
        (computeSubformulaFPs
          ((Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).2.2.1
          1)
        TripleSlot.result) :=
  ⟨.atom 0, condResult_bounded hfirst, condResult_leaves_le_Lambda hfirst, (parent_sf2_result_fp hfirst).symm⟩

/-- Reconstruction selector picks a windowed witness, so the named extra's
leaf bound holds -/
theorem reconstructed_sf2_leaves (P : ResidualPremises (Op6Execution hfirst)) :
    (P8Census.skeletonSubformula
        (computeNodeAt (Op6Execution hfirst) P ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel
        ⟨1, by decide⟩ .result).leaves ≤ (Op6Execution hfirst).Λ := by
  have hi : (1 : ℕ) < ComputeTable.fanoutComp
      ((Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).1 := by
    rw [op6_computeRowAt_zero]
    decide
  have hz :
      ((Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).2.1.z =
        seedZ := by
    rw [same_z (Op6Execution hfirst) ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩]
    rfl
  have hlt : (1 : ℕ) < ComputeTable.fanoutComp
      (computeNodeAt (Op6Execution hfirst) P ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel.state := by
    rw [reconstructed_parent_state hfirst P]
    decide
  unfold P8Census.skeletonSubformula
  rw [dif_pos hlt]
  simp [computeNodeAt, computeNodeOf, computeSkeletonOf]
  have hw :
      FPRealizedWithin
        ((Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).2.1.z
        (Op6Execution hfirst).q (Op6Execution hfirst).Λ
        (SemanticStrategy.tripleFP
          (computeSubformulaFPs
            ((Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).2.2.1
            1)
          TripleSlot.result) := by
    rw [hz]
    exact (sf2_fp_realized_within hfirst)
  exact subformulaNounOf_leaves_of_within
    ((Op6Execution hfirst).semanticData.rows ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩)
    (publicRowNoun_of_execution (Op6Execution hfirst) ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩)
    ⟨1, by decide⟩ hi TripleSlot.result hw

/-- Instantiating the named extra at the compiled `(P, M)` pair: it is the leaf
bound on that one reconstructed subformula. The selector prefers a windowed
witness when one exists (`sf2_fp_realized_within`). -/
theorem named_extra_at_witness :
    SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) (residualPremises hfirst))
          (memoryNodesOf (Op6Execution hfirst) (memoryRecordPremises hfirst))) (Op6Execution hfirst).Λ ↔
      (P8Census.skeletonSubformula
          (computeNodeAt (Op6Execution hfirst) (residualPremises hfirst)
            ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel
          ⟨1, by decide⟩ .result).leaves ≤ (Op6Execution hfirst).Λ :=
  named_sizeWindowBound_iff_sf2_result hfirst (residualPremises hfirst) (memoryRecordPremises hfirst)

/-- Named `CensusRecordPremises.sizeWindowBound` at this OP6 reconstruction.
Written scope: `(Op6Execution hfirst)` over `K3`, parent `.s6`, `Λ = 7`. This is the
J.00 gated-state inhabitant -/
theorem named_sizeWindowBound
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
          (memoryNodesOf (Op6Execution hfirst) M)) (Op6Execution hfirst).Λ :=
  (named_sizeWindowBound_iff_sf2_result hfirst P M).mpr (reconstructed_sf2_leaves hfirst P)

/-! ## The recorded `enc` fact does not pin leaves

Instantiated at this execution's `seedZ`
(`orderOf = 16`): the 17-leaf left comb and `.atom 0` share a fingerprint, both
`BoundedBy 97`, and only the atom meets `leaves ≤ Λ`. The reconstructed window noun is a
`chooseNoun` of that fingerprint, so `reconstructed_sf2_encodes_condResult` does not
discharge `named_extra_at_witness`. -/

/-- The left comb with `k + 1` leaves, every leaf the atom `0`. -/
private def leftComb : ℕ → Noun
  | 0 => .atom 0
  | k + 1 => .cell (leftComb k) (.atom 0)

private theorem leftComb_leaves (k : ℕ) : (leftComb k).leaves = k + 1 := by
  induction k with
  | zero => simp [leftComb, Noun.leaves]
  | succ k ih => simp [leftComb, Noun.leaves, ih]

private theorem leftComb_bounded {q : ℕ} (hq : 0 < q) (k : ℕ) :
    FieldEmbedding.BoundedBy q (leftComb k) := by
  induction k with
  | zero => simpa [leftComb] using hq
  | succ k ih => exact ⟨ih, hq⟩

private theorem enc_leftComb {F : Type*} [Field F] {z : F} (hz : z ≠ 0) (k : ℕ) :
    GlobalCarryRecognizer.enc z (leftComb k) =
      ⟨z ^ (k + 1), z ^ k * ∑ i ∈ Finset.range k, z ^ i, 0⟩ := by
  have hatom : GlobalCarryRecognizer.enc z (Noun.atom 0) = ⟨z, 0, 0⟩ := by
    refine ComputeTable.FP.ext ?_ ?_ ?_
    · simp [GlobalCarryRecognizer.enc, Noun.leaves]
    · simp [GlobalCarryRecognizer.enc, NPR.dyckBits, Noun.dyckWord, Noun.shape,
        Nock.BTree.encode, NPR.listPoly, NPR.cpoly]
    · simp [GlobalCarryRecognizer.enc, NPR.leafF, Noun.leafList, NPR.listPoly, NPR.cpoly]
  induction k with
  | zero => simpa [leftComb] using hatom
  | succ k ih =>
      rw [show leftComb (k + 1) = .cell (leftComb k) (.atom 0) from rfl,
        GlobalCarryRecognizer.enc_cons hz, ih, hatom]
      refine ComputeTable.FP.ext ?_ ?_ ?_
      · simp [ComputeTable.FP.cons, pow_succ]
      · simp only [ComputeTable.FP.cons, Finset.sum_range_succ]
        field_simp
        ring
      · simp [ComputeTable.FP.cons]

private theorem enc_leftComb_collision {F : Type*} [Field F] {z : F} (hord : 2 ≤ orderOf z) :
    GlobalCarryRecognizer.enc z (leftComb (orderOf z)) =
      GlobalCarryRecognizer.enc z (.atom 0) := by
  have hpow : z ^ orderOf z = 1 := pow_orderOf_eq_one z
  have hz : z ≠ 0 := (orderOf_pos_iff.mp (by omega)).isUnit.ne_zero
  have hne1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have hsum : ∑ i ∈ Finset.range (orderOf z), z ^ i = 0 := by
    have hmul : (∑ i ∈ Finset.range (orderOf z), z ^ i) * (z - 1) = 0 := by
      rw [geom_sum_mul, hpow, sub_self]
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne1
  have hatom : GlobalCarryRecognizer.enc z (Noun.atom 0) = ⟨z, 0, 0⟩ := by
    simpa [leftComb] using enc_leftComb (z := z) hz 0
  rw [enc_leftComb hz, hatom]
  refine ComputeTable.FP.ext ?_ ?_ ?_
  · simp [pow_succ, hpow]
  · simp [hsum]
  · rfl

/-- At this OP6 seed the honest window fingerprint is also realized by a 17-leaf comb.
`chooseNoun` may return either; `enc` does not force `leaves ≤ Λ` -/
theorem enc_collision_across_the_window :
    GlobalCarryRecognizer.enc seedZ (leftComb 16) =
        GlobalCarryRecognizer.enc seedZ (.atom 0) ∧
      FieldEmbedding.BoundedBy (Op6Execution hfirst).q (leftComb 16) ∧
        FieldEmbedding.BoundedBy (Op6Execution hfirst).q (Noun.atom 0) ∧
          (Noun.atom 0).leaves ≤ (Op6Execution hfirst).Λ ∧
            ¬ (leftComb 16).leaves ≤ (Op6Execution hfirst).Λ := by
  have hord : orderOf seedZ = 16 := seedZ_order
  have hq : 0 < (Op6Execution hfirst).q := by
    change 0 < (97 : ℕ)
    omega
  have hcoll := enc_leftComb_collision (z := seedZ) (by rw [hord]; omega)
  rw [hord] at hcoll
  refine ⟨hcoll, leftComb_bounded hq 16, ?_, ?_, ?_⟩
  · simpa using hq
  · change (Noun.atom 0).leaves ≤ (7 : ℕ)
    simp [Noun.leaves]
  · rw [leftComb_leaves]
    change ¬ (16 + 1) ≤ (7 : ℕ)
    omega

/-- The cubic OP6 honest `Data` is the literal-node constructor (`op6ComputeTree` /
`[op6MemTree]`), not `dataOf` on reconstructed `(P, M, C)`. `dataOf` commits
`computeNodesOf` (`GenericHonestData.dataOf`). Two honest-commitment stories;
this fixture uses the constructor -/
theorem data_is_literal_node_constructor :
    (data hfirst).computeNodes = op6ComputeTree ∧
      (data hfirst).memoryNodes = [op6MemTree] :=
  ⟨rfl, rfl⟩

/-- `dataOf` always commits the reconstructed compute tree, never the literal
generator/fixture nodes -/
theorem dataOf_commits_reconstructed
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryAssemblyPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) M.memoryNodes)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOf E P M C hln).computeNodes = computeNodesOf E P :=
  rfl

/-! ## Named `skeletonBounded` on the reconstruction

Written scope: `(Op6Execution hfirst)` over `K3`. The paper `cons` constraints hold on the
already-compiled semantic rows (`ConsDecomposedRow`), so
`skeletonBounded_of_consDecomposed` inhabits the named extra on
`computeNodesOf` / `memoryNodesOf`. This is not `(data hfirst).skeletonBounded` (literal
nodes). Same trade as F97: `ConsDecomposedRow` is strictly stronger than the
atom-range conclusion. `census` and named `sizeWindowBound` stay blocked on
`chooseNoun` leaves. §J.2 not ticked. -/

theorem consDecomposed_cast
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K}
    (h : row₁ = row₂) {d : SemanticTrace.ComputeRowSemanticData 97 7 row₂}
    (hd : ConsDecomposedRow d) : ConsDecomposedRow (castRowData h d) := by
  cases h
  exact hd

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
  rcases fin_val_le_two hfirst i with h0 | h1 | h2
  · have : i = ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩ := Fin.ext h0
    subst this
    exact consDecomposed_cast
      (Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.computeRowAt_zero)
      parentRowData_consDecomposed
  · have : i = ⟨1, one_lt_comp⟩ := Fin.ext h1
    subst this
    exact consDecomposed_cast
      (Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.computeRowAt_one)
      child1RowData_consDecomposed
  · have : i = ⟨2, two_lt_comp⟩ := Fin.ext h2
    subst this
    exact consDecomposed_cast
      (Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.computeRowAt_two)
      child2RowData_consDecomposed

/-- Named `CensusRecordPremises.skeletonBounded` at this OP6 reconstruction. -/
theorem named_skeletonBounded
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
      (memoryNodesOf (Op6Execution hfirst) M)).BoundedBy (Op6Execution hfirst).q :=
  skeletonBounded_of_consDecomposed (Op6Execution hfirst) P M (consDecomposed hfirst)

/-- Derived `combinedBounded` at the same reconstruction. -/
theorem named_combinedBounded
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    ProductionP8Containment.CombinedBoundedBy K (Op6Execution hfirst).q
      (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
        (memoryNodesOf (Op6Execution hfirst) M)) :=
  combinedBounded_of_consDecomposed (Op6Execution hfirst) P M (consDecomposed hfirst)
    (by
      have : ringChar K = 97 := ringChar_K3
      omega)

/-! ## Named `census` at this reconstruction

`census_of_leafWindow_on_reconstruction` needs `1 ≤ Λ`, `RowCellIdentities` on
every reconstructed compute row, and `RowLeafWindow`. Cell identities are
free from `ConsDecomposedRow` (no `.s8` / `.cons`). The leaf window is the
honest public triples plus windowed `chooseNoun` of every active subformula
fingerprint. Not designed C2 as a `NounRealization` field. -/

theorem one_le_Lambda : 1 ≤ (Op6Execution hfirst).Λ := by
  change 1 ≤ 7
  decide

theorem no_s8 (i : Fin (Op6Execution hfirst).cfg.compRows) :
    ((Op6Execution hfirst).exec.computeRowAt i).1 ≠ .s8 := by
  rcases row_states hfirst i with h | h <;> rw [h] <;> decide

theorem no_cons (i : Fin (Op6Execution hfirst).cfg.compRows) :
    ((Op6Execution hfirst).exec.computeRowAt i).1 ≠ .cons := by
  rcases row_states hfirst i with h | h <;> rw [h] <;> decide

theorem named_rowCellIdentities
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
          (memoryNodesOf (Op6Execution hfirst) M)),
      RowCellIdentities s :=
  rowCellIdentities_on_reconstruction (Op6Execution hfirst) P M (consDecomposed hfirst)
    (no_s8 hfirst) (no_cons hfirst)

theorem castRowData_root_subject
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K}
    (h : row₁ = row₂) (d : SemanticTrace.ComputeRowSemanticData 97 7 row₂) :
    (castRowData h d).root.subject = d.root.subject := by
  cases h
  rfl

theorem castRowData_root_formula
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K}
    (h : row₁ = row₂) (d : SemanticTrace.ComputeRowSemanticData 97 7 row₂) :
    (castRowData h d).root.formula = d.root.formula := by
  cases h
  rfl

theorem castRowData_root_result
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K}
    (h : row₁ = row₂) (d : SemanticTrace.ComputeRowSemanticData 97 7 row₂) :
    (castRowData h d).root.result = d.root.result := by
  cases h
  rfl

theorem rows_zero :
    (Op6Execution hfirst).semanticData.rows ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩ =
      castRowData
        Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.computeRowAt_zero
        parentRowData :=
  rfl

theorem rows_one :
    (Op6Execution hfirst).semanticData.rows ⟨1, one_lt_comp⟩ =
      castRowData
        Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.computeRowAt_one
        child1RowData :=
  rfl

theorem rows_two :
    (Op6Execution hfirst).semanticData.rows ⟨2, two_lt_comp⟩ =
      castRowData
        Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.computeRowAt_two
        child2RowData :=
  rfl

theorem reconstructed_parent_roots (P : ResidualPremises (Op6Execution hfirst)) :
    (computeNodeAt (Op6Execution hfirst) P ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel.subject =
      TraceGen.op6Subject ∧
    (computeNodeAt (Op6Execution hfirst) P ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel.formula =
      TraceGen.op6ParentFormula ∧
    (computeNodeAt (Op6Execution hfirst) P ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel.evaluation =
      TraceGen.op6Result := by
  simp only [computeNodeAt, computeNodeOf, computeSkeletonOf]
  rw [rows_zero, castRowData_root_subject, castRowData_root_formula,
    castRowData_root_result]
  exact ⟨rfl, rfl, rfl⟩

theorem reconstructed_child1_roots (P : ResidualPremises (Op6Execution hfirst)) :
    (computeNodeAt (Op6Execution hfirst) P ⟨1, one_lt_comp⟩).skel.subject =
      TraceGen.op6Subject ∧
    (computeNodeAt (Op6Execution hfirst) P ⟨1, one_lt_comp⟩).skel.formula =
      TraceGen.op6BranchC ∧
    (computeNodeAt (Op6Execution hfirst) P ⟨1, one_lt_comp⟩).skel.evaluation =
      TraceGen.op6Result := by
  simp only [computeNodeAt, computeNodeOf, computeSkeletonOf]
  rw [rows_one, castRowData_root_subject, castRowData_root_formula,
    castRowData_root_result]
  exact ⟨rfl, rfl, rfl⟩

theorem reconstructed_child2_roots (P : ResidualPremises (Op6Execution hfirst)) :
    (computeNodeAt (Op6Execution hfirst) P ⟨2, two_lt_comp⟩).skel.subject =
      TraceGen.op6Subject ∧
    (computeNodeAt (Op6Execution hfirst) P ⟨2, two_lt_comp⟩).skel.formula =
      TraceGen.op6CondFormula ∧
    (computeNodeAt (Op6Execution hfirst) P ⟨2, two_lt_comp⟩).skel.evaluation =
      TraceGen.op6CondResult := by
  simp only [computeNodeAt, computeNodeOf, computeSkeletonOf]
  rw [rows_two, castRowData_root_subject, castRowData_root_formula,
    castRowData_root_result]
  exact ⟨rfl, rfl, rfl⟩

theorem op6_public_nouns_leaves :
    TraceGen.op6Subject.leaves ≤ (Op6Execution hfirst).Λ ∧
      TraceGen.op6ParentFormula.leaves ≤ (Op6Execution hfirst).Λ ∧
        TraceGen.op6Result.leaves ≤ (Op6Execution hfirst).Λ ∧
          TraceGen.op6BranchC.leaves ≤ (Op6Execution hfirst).Λ ∧
            TraceGen.op6CondFormula.leaves ≤ (Op6Execution hfirst).Λ ∧
              TraceGen.op6CondResult.leaves ≤ (Op6Execution hfirst).Λ := by
  change
    TraceGen.op6Subject.leaves ≤ 7 ∧
      TraceGen.op6ParentFormula.leaves ≤ 7 ∧
        TraceGen.op6Result.leaves ≤ 7 ∧
          TraceGen.op6BranchC.leaves ≤ 7 ∧
            TraceGen.op6CondFormula.leaves ≤ 7 ∧
              TraceGen.op6CondResult.leaves ≤ 7
  decide

/-- Honest nouns of the two live parent subformula triples (`sf1` taken, `sf2` condition). -/
def parentHonestNoun (i : Fin 3) (slot : TripleSlot) : Noun :=
  if (i : ℕ) = 0 then
    match slot with
    | .subject => TraceGen.op6Subject
    | .formula => TraceGen.op6BranchC
    | .result => TraceGen.op6Result
  else
    match slot with
    | .subject => TraceGen.op6Subject
    | .formula => TraceGen.op6CondFormula
    | .result => TraceGen.op6CondResult

theorem parentHonestNoun_bounded (i : Fin 3) (slot : TripleSlot) :
    FieldEmbedding.BoundedBy (Op6Execution hfirst).q (parentHonestNoun i slot) := by
  unfold parentHonestNoun
  split_ifs
  · cases slot
    · exact bounded_subject
    · exact bounded_branchC
    · exact bounded_result
  · cases slot
    · exact bounded_subject
    · exact bounded_condFormula
    · exact bounded_condResult

theorem parentHonestNoun_leaves (i : Fin 3) (slot : TripleSlot) :
    (parentHonestNoun i slot).leaves ≤ (Op6Execution hfirst).Λ := by
  change (parentHonestNoun i slot).leaves ≤ 7
  unfold parentHonestNoun
  split_ifs <;> cases slot <;> decide

theorem parent_subformula_fp (i : Fin 3) (hi : (i : ℕ) < 2) (slot : TripleSlot) :
    SemanticStrategy.tripleFP
        (computeSubformulaFPs (parentPub seedZ alphaA) i) slot =
      GlobalCarryRecognizer.enc seedZ (parentHonestNoun i slot) := by
  have h01 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
  rcases h01 with h0 | h1
  · have : i = ⟨0, by decide⟩ := Fin.ext h0
    subst this
    cases slot <;> simp [parentHonestNoun, SemanticStrategy.tripleFP,
      computeSubformulaFPs, ComputeTable.sfTriple, parentPub, fp]
  · have : i = ⟨1, by decide⟩ := Fin.ext h1
    subst this
    cases slot <;> simp [parentHonestNoun, SemanticStrategy.tripleFP,
      computeSubformulaFPs, ComputeTable.sfTriple, parentPub, fp]

theorem parent_subformula_fp_realized (i : Fin 3)
    (hi : (i : ℕ) < ComputeTable.fanoutComp .s6) (slot : TripleSlot) :
    FPRealizedWithin seedZ (Op6Execution hfirst).q (Op6Execution hfirst).Λ
      (SemanticStrategy.tripleFP
        (computeSubformulaFPs (parentPub seedZ alphaA) i) slot) :=
  ⟨parentHonestNoun i slot, parentHonestNoun_bounded hfirst i slot,
    parentHonestNoun_leaves hfirst i slot,
    (parent_subformula_fp i (by simpa [ComputeTable.fanoutComp] using hi) slot).symm⟩

theorem reconstructed_parent_subformula_leaves (P : ResidualPremises (Op6Execution hfirst))
    (i : Fin 3) (slot : TripleSlot) :
    (P8Census.skeletonSubformula
        (computeNodeAt (Op6Execution hfirst) P ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel
        i slot).leaves ≤ (Op6Execution hfirst).Λ := by
  by_cases hi : (i : ℕ) < ComputeTable.fanoutComp
      (computeNodeAt (Op6Execution hfirst) P ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel.state
  · have hirow : (i : ℕ) < ComputeTable.fanoutComp
        ((Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).1 := by
      rw [reconstructed_row_state (Op6Execution hfirst) P] at hi
      exact hi
    have hz :
        ((Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).2.1.z =
          seedZ := by
      rw [same_z (Op6Execution hfirst) ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩]
      rfl
    unfold P8Census.skeletonSubformula
    rw [dif_pos hi]
    simp [computeNodeAt, computeNodeOf, computeSkeletonOf]
    have hw :
        FPRealizedWithin
          ((Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).2.1.z
          (Op6Execution hfirst).q (Op6Execution hfirst).Λ
          (SemanticStrategy.tripleFP
            (computeSubformulaFPs
              ((Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).2.2.1
              i)
            slot) := by
      rw [hz, op6_computeRowAt_zero]
      have hfan : ComputeTable.fanoutComp .s6 =
          ComputeTable.fanoutComp
            ((Op6Execution hfirst).exec.computeRowAt ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).1 := by
        rw [op6_computeRowAt_zero]
        rfl
      have hi' : (i : ℕ) < ComputeTable.fanoutComp .s6 := by
        rw [hfan]
        exact hirow
      simpa [parentRow, parentPub] using parent_subformula_fp_realized hfirst i hi' slot
    exact subformulaNounOf_leaves_of_within
      ((Op6Execution hfirst).semanticData.rows ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩)
      (publicRowNoun_of_execution (Op6Execution hfirst) ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩)
      i hirow slot hw
  · unfold P8Census.skeletonSubformula
    rw [dif_neg hi]
    simp [Noun.leaves]
    exact one_le_Lambda hfirst

theorem reconstructed_parent_rowLeafWindow (P : ResidualPremises (Op6Execution hfirst)) :
    RowLeafWindow (Op6Execution hfirst).Λ
      (computeNodeAt (Op6Execution hfirst) P ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩).skel := by
  have hroot := reconstructed_parent_roots hfirst P
  have hleaves := op6_public_nouns_leaves hfirst
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hroot.1]; exact hleaves.1
  · rw [hroot.2.1]; exact hleaves.2.1
  · rw [hroot.2.2]; exact hleaves.2.2.1
  · intro i slot
    exact reconstructed_parent_subformula_leaves hfirst P i slot

theorem reconstructed_child1_rowLeafWindow (P : ResidualPremises (Op6Execution hfirst)) :
    RowLeafWindow (Op6Execution hfirst).Λ
      (computeNodeAt (Op6Execution hfirst) P ⟨1, one_lt_comp⟩).skel := by
  have hroot := reconstructed_child1_roots hfirst P
  have hleaves := op6_public_nouns_leaves hfirst
  refine rowLeafWindow_of_fanout_zero (one_le_Lambda hfirst) ?_ ?_ ?_ ?_
  · rw [reconstructed_child1_state hfirst P]; decide
  · rw [hroot.1]; exact hleaves.1
  · rw [hroot.2.1]; exact hleaves.2.2.2.1
  · rw [hroot.2.2]; exact hleaves.2.2.1

theorem reconstructed_child2_rowLeafWindow (P : ResidualPremises (Op6Execution hfirst)) :
    RowLeafWindow (Op6Execution hfirst).Λ
      (computeNodeAt (Op6Execution hfirst) P ⟨2, two_lt_comp⟩).skel := by
  have hroot := reconstructed_child2_roots hfirst P
  have hleaves := op6_public_nouns_leaves hfirst
  refine rowLeafWindow_of_fanout_zero (one_le_Lambda hfirst) ?_ ?_ ?_ ?_
  · rw [reconstructed_child2_state hfirst P]; decide
  · rw [hroot.1]; exact hleaves.1
  · rw [hroot.2.1]; exact hleaves.2.2.2.2.1
  · rw [hroot.2.2]; exact hleaves.2.2.2.2.2

theorem named_rowLeafWindow
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
          (memoryNodesOf (Op6Execution hfirst) M)),
      RowLeafWindow (Op6Execution hfirst).Λ s := by
  intro s hs
  obtain ⟨i, rfl⟩ := reconstructed_rows_are_nodes (Op6Execution hfirst) P M hs
  rcases fin_val_le_two hfirst i with h | h | h
  · have : i = ⟨0, (Op6Execution hfirst).cfg.compRows_pos⟩ := Fin.ext h
    subst this
    exact reconstructed_parent_rowLeafWindow hfirst P
  · have : i = ⟨1, one_lt_comp⟩ := Fin.ext h
    subst this
    exact reconstructed_child1_rowLeafWindow hfirst P
  · have : i = ⟨2, two_lt_comp⟩ := Fin.ext h
    subst this
    exact reconstructed_child2_rowLeafWindow hfirst P

/-- Named `CensusRecordPremises.census` at this OP6 reconstruction.
Written scope: `(Op6Execution hfirst)` over `K3`, `Λ = 7`. -/
theorem named_census
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    EdgeComparisonCensus.CombinedSkeletonCensus K
      (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
        (memoryNodesOf (Op6Execution hfirst) M)) (Op6Execution hfirst).Λ :=
  census_of_leafWindow_on_reconstruction (Op6Execution hfirst) P M (one_le_Lambda hfirst)
    (named_rowCellIdentities hfirst P M) (named_rowLeafWindow hfirst P M)

/-- Named `CensusRecordPremises.slotSemantics` is free here by the OP0/OP9
state gate (no lookup rows). Not a generic close; the gate is load-bearing
(`s0SlotFailRow_slotSemantics_fails`) -/
theorem named_slotSemantics
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf (Op6Execution hfirst) P)
          (memoryNodesOf (Op6Execution hfirst) M)),
      ServedLookupBridge.SkeletonSlotSemantics s :=
  slotSemantics_of_no_lookup_states (Op6Execution hfirst) P M fun i => by
    rcases row_states hfirst i with h | h <;> simp [h]

/-- The whole five-field census bundle at this OP6 reconstruction. -/
def censusRecordPremises
    (P : ResidualPremises (Op6Execution hfirst)) (M : MemoryRecordPremises (Op6Execution hfirst)) :
    CensusRecordPremises (Op6Execution hfirst) P M where
  slotSemantics := named_slotSemantics hfirst P M
  census := named_census hfirst P M
  sizeWindowBound := named_sizeWindowBound hfirst P M
  skeletonBounded := named_skeletonBounded hfirst P M
  combinedBounded := named_combinedBounded hfirst P M

end

end Nock.NockVMROM.Thm54.SizeWindowBoundOp6

#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.parent_is_s6
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.window_state_gate_fails
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.data_sizeWindowBound
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.residualPremises
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.memoryRecordPremises
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.named_sizeWindowBound_iff_sf2_result
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.reconstructed_sf2_encodes_condResult
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.named_extra_at_witness
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.sf2_fp_realized_within
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.reconstructed_sf2_leaves
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.named_sizeWindowBound
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.enc_collision_across_the_window
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.data_is_literal_node_constructor
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.dataOf_commits_reconstructed
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.parentRowData_consDecomposed
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.consDecomposed
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.named_skeletonBounded
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.named_combinedBounded
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.named_census
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.named_rowLeafWindow
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.named_rowCellIdentities
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.named_slotSemantics
#print axioms Nock.NockVMROM.Thm54.SizeWindowBoundOp6.censusRecordPremises

/-
  Item 2 fixture — written scope.
  * Execution: already-compiled OP9 K3 `ExactServedMemoryTrace`
    (`Op9ConfigK3.memoryTraceFinal`) for
    `*[[[1 7] [1 9]] [9 2 [1 [[1 7] [1 9]]]]] = 7`.
  * Skeleton: literal `Op9Skeleton.parentRow` (state `.s9`), not
    `computeNodesOf` / reconstructed census rows. OP9 `axisAtoms` is parked
    Tier 3, so this is not `CensusRecordPremises.slotSemantics`.
  * Join: the arm-fetch triple is `serviceArm` in root B of that trace
    (`servedTuplesOf`), then `slotSemantics_of_served`. Not `needs.served`
    length, not `axisNat`, not paper `/(1,n)=n` as a hypothesis.
  * Not done at the time of this leaf: C2; C5; no field. The reconstruction
    extra is `SlotSemanticsOp9.named_slotSemantics`.
-/
namespace Nock.NockVMROM.Thm54.SlotSemanticsServedOp9

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.P8Census
open Nock.NockVMROM.Thm54.TraceGen (op9CoreNoun op9Arm)
open Nock.NockVMROM.Thm54.TraceGen.Op9Skeleton (parentRow)
open Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3
  (memoryTraceFinal rootTraces rootTraceB serviceArm serviceArmF finRange_kMem
    cfg seedZ alphaA exec)

noncomputable section

variable (hfirst :
  ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
    ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0)

theorem parent_is_s9 : parentRow.state = .s9 := rfl

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
  simp [parentRow, Nock.NockVMROM.Thm54.TraceGen.Op9Skeleton.recArm]

/-- The `.s9` slot triple is exactly the root-B arm-fetch service. -/
theorem parent_s9_triple_eq_serviceArm :
    (skeletonSubformula parentRow 0 .result,
      skeletonMemoryAxis parentRow 2,
      skeletonSubformula parentRow 1 .formula) =
      (serviceArm.root, serviceArm.axis, serviceArm.child) := by
  rw [parent_sf0_result, parent_sf1_formula, parent_mr3_axis]
  simp [serviceArm]

/-- `serviceArm` is among `servedTuplesOf (memoryTraceFinal hfirst)`. -/
theorem arm_tuple_in_servedTuplesOf :
    (op9CoreNoun, (2 : ℕ), op9Arm) ∈ servedTuplesOf (memoryTraceFinal hfirst) := by
  unfold servedTuplesOf
  rw [show (memoryTraceFinal hfirst).roots = rootTraces from rfl, finRange_kMem]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
  refine Or.inr ?_
  simp [rootTraces, rootTraceB, serviceArm, serviceArmF]

/-- Identifying the literal OP9 parent slots with the compiled served-memory
arm fetch. This is not `CensusRecordPremises.slotSemantics` on reconstructed
`computeNodesOf` -/
theorem parent_slotSemantics_of_served
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    SkeletonSlotSemantics parentRow :=
  slotSemantics_of_served (memoryTraceFinal hfirst) parentRow
    (fun h => absurd h (by simp [parentRow]))
    (fun _ => by
      rw [parent_sf0_result, parent_sf1_formula, parent_mr3_axis]
      exact arm_tuple_in_servedTuplesOf hfirst)

end

end Nock.NockVMROM.Thm54.SlotSemanticsServedOp9

#print axioms Nock.NockVMROM.Thm54.SlotSemanticsServedOp9.parent_is_s9
#print axioms Nock.NockVMROM.Thm54.SlotSemanticsServedOp9.arm_tuple_in_servedTuplesOf
#print axioms Nock.NockVMROM.Thm54.SlotSemanticsServedOp9.parent_slotSemantics_of_served
