import Nock.NockVMROM.Thm54.ServedForestCommitment
import Nock.NockVMROM.Thm54.ServedForestParams
import Nock.NockVMROM.Thm54.Op3Statement
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# `ServedForestOp3` — the OP₃ instantiation of the generic honest-commitment module (stage 8)

The memory-side root `A` (whose skeleton carries `encS op3ParentFormulaS`) is discharged
**generically** by the served-forest module — the earlier `Op3Gen`/`Op3Statement` scope notes that
predicted a ~3300-line memory clone predate that generic lift; the only genuinely OP₃-specific work
is the compute parent-row seed binding / timestamp / semantic bridge / noun realization and the six
skeleton obligations, all ported here from their `MultiRootHonestCommitment` counterparts with the
`wut` gate output `op3ParentResultS =.atom 1` in place of OP₄'s increment.
-/

namespace Nock.NockVMROM.Thm54.ServedForestModule

open scoped Classical
open Nock Nock.Noun Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open SemanticStrategy SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.ServedForest
open Nock.NockVMROM.Thm54.Op3Statement
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance op3_factPrime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance op3_fintypeK97 : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance op3_decEqK97 : DecidableEq K97cubic := Classical.decEq K97cubic
local instance op3_charP97 : CharP K97cubic 97 := inferInstance
local instance op3_charPringChar : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-! ## A. The OP₃ semantic parent record and its bridge -/

/-- The OP₃ parent semantic (nmr) record: the parent formula opened over `[3 [0 2]]`. -/
def op3SemParentRec : (nmrMEF F97 K97cubic).Rec :=
  (3,
    (((encS op3ParentFormulaS).size, (encS op3ParentFormulaS).dyck, (encS op3ParentFormulaS).leaf),
     ((encS formulaS).size, (encS formulaS).dyck, (encS formulaS).leaf)),
    1)

private theorem op3_algebraMap_three :
    algebraMap F97 K97cubic (3 : F97) = (3 : K97cubic) := by
  simpa using (map_natCast (algebraMap F97 K97cubic) 3)

theorem op3SemParentRec_bridge :
    bridge F97 K97cubic cfgS.challenges.α cfgS.challenges.lam op3SemParentRec
      = NockVM.encRecFormR (parentRecordG op3Params) MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees]
  rw [show memRecOfNMR F97 K97cubic
      ((nmrEncoding F97 K97cubic cfgS.challenges.α).encode op3SemParentRec)
        = parentRecordG op3Params by
    ext <;> norm_num [memRecOfNMR, nmrEncoding, op3SemParentRec, cfgS, parentRecordG,
      op3Params, op3ParentFormulaS, fixtureAlpha, op3_algebraMap_three]]
  -- `cfgS.challenges.lam = formRDefault` (fixture value) by unfolding
  rfl

/-! ## B. The OP₃ compute parent-row `Fcomp` (shared `parentOutS`) and active request -/

/-- `parentOutS` and `op3ParentOutS` are pointwise equal, so the OP₃ parent row is an accepted
nonterminal `Fcomp` row against the *shared* fanout. -/
theorem op3ParentRowFcomp :
    ComputeTable.Fcomp (op3ParentPubS.state, (servedInputs, op3ParentPubS, op3ParentDecS))
      parentOutS := by
  have h : parentOutS = op3ParentOutS := by funext i; fin_cases i <;> rfl
  rw [h]; exact op3ParentRowS_accepts

theorem op3ParentActiveReq :
    NockVM.activeRequestRecords op3ParentPubS = [parentRecordG op3Params] := by
  simp [NockVM.activeRequestRecords, op3ParentPubS, parentRecordG, op3Params, op3ParentRecordS,
    op3ParentFormulaS]

/-! ## C. `op3Exec` — `op3Params` bundled with the concrete compute parent-row seam -/

/-- Bounded-noun realization of the OP₃ parent public row. -/
theorem op3ParentRow_nounRealization :
    ComputePublicRowNounRealization 97
      (computePublicLabel (op3ParentPubS.state, (servedInputs, op3ParentPubS, op3ParentDecS))) where
  subject := fpActiveS bounded_subjectS
  formula := fpActiveS op3Params.hformulaBounded
  evaluation := fpActiveS op3Params.hresultBounded
  subformula := by
    intro i
    fin_cases i
    · exact ⟨fpActiveS bounded_subjectS, fpActiveS bounded_formulaS, fpActiveS bounded_resultS⟩
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i
    fin_cases i
    · exact parentRecordG_active op3Params
    · exact rfl
    · exact rfl

/-- **The OP₃ served-forest execution.** -/
def op3Exec : ServedForestExec where
  toServedForestParams := op3Params
  parentPub := op3ParentPubS
  parentDec := op3ParentDecS
  parentAccepts := op3ParentS_accepts
  parentWf := op3ParentS_wf
  parentActiveReq := op3ParentActiveReq
  parentLineHandoff := op3_compute_line_handoffS
  parentLineOrigin := rfl
  parentRowData := op3ParentRowData
  parentRowServed := rfl
  parentRowNoun := op3ParentRow_nounRealization
  semParentRec := op3SemParentRec
  semParentTs := rfl
  semParentBridge := op3SemParentRec_bridge
  parentRowFcomp := op3ParentRowFcomp
  parentFanout := rfl

/-! ## D. The committed OP₃ skeleton's compute rows -/

theorem computeSkeletonRowsMG_op3 :
    computeSkeletonRows (skelMG op3Exec) = [parentSkeletonRowG op3Exec, servedSkeletonRow] := by
  norm_num [computeSkeletonRows, skelMG, skeletonOfNodes, computeNodesMG, mapNTree,
    parentNodeG, servedNode, bfsForest, NTree.size, totalSize]

/-! ## E. The two OP₃ parent-compute-seam proofs (seed bind + timestamp specialization) -/

theorem bind_parentRowG_op3 :
    BindComputeRow servedSeed (parentSkeletonRowG op3Exec) (parentRowG op3Exec) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP,
        parentSkeletonRowG, parentRowG, op3Exec, op3Params, op3ParentPubS, op3ParentDecS,
        op3ParentHeadS, encS]
  · intro i
    fin_cases i
    · rw [dif_pos (by simp [parentSkeletonRowG, op3Exec, op3ParentPubS, ComputeTable.fanoutComp])]
      intro slot
      cases slot <;> rfl
    · rw [dif_neg (by simp [parentSkeletonRowG, op3Exec, op3ParentPubS, ComputeTable.fanoutComp])]
      rfl
    · rw [dif_neg (by simp [parentSkeletonRowG, op3Exec, op3ParentPubS, ComputeTable.fanoutComp])]
      rfl
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, by norm_num [parentSkeletonRowG, parentRecordSkeletonG, parentRowG,
        op3Exec, op3Params, op3ParentPubS, op3ParentRecordS, op3ParentFormulaS, computeMemRec]⟩
    · rfl
    · rfl

theorem stamp_parentRowG_op3 :
    ComputeTimestampSpecializesAt cfgS.challenges.α (parentStampG op3Exec) (parentRowG op3Exec) := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show op3ParentPubS.ln_prev = cfgS.challenges.α ^ 0
    rw [pow_zero]; rfl
  · show op3ParentPubS.ln = cfgS.challenges.α ^ 1
    rw [pow_one]; rfl
  · intro i
    fin_cases i
    · show op3ParentPubS.mr1.ts = _
      rw [if_pos (by rfl)]
      show op3ParentRecordS.ts = cfgS.challenges.α ^ 1
      rw [pow_one]; rfl
    · show op3ParentPubS.mr2.ts = _
      rw [if_neg (by decide)]; rfl
    · show op3ParentPubS.mr3.ts = _
      rw [if_neg (by decide)]; rfl
  · intro i hi
    fin_cases i
    · exact absurd hi
        (by simp [parentStampG, op3Exec, op3ParentPubS, computeMemRecKind,
          Nock.Framework.recordCount])
    · rfl
    · rfl

/-! ## F. The six skeleton-only obligations at OP₃ -/

theorem op3_slotSem :
    ∀ s ∈ computeSkeletonRows (skelMG op3Exec),
      ServedLookupBridge.SkeletonSlotSemantics s := by
  intro s hs
  rw [computeSkeletonRowsMG_op3] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact
      { s0_slot := fun h => absurd h (by simp [parentSkeletonRowG, op3Exec, op3ParentPubS])
        s9_slot := fun h => absurd h (by simp [parentSkeletonRowG, op3Exec, op3ParentPubS]) }
  · refine
      { s0_slot := fun _ => ?_
        s9_slot := fun h => absurd h (by simp [servedSkeletonRow]) }
    show Noun.slot (P8Census.skeletonMemoryAxis servedSkeletonRow 1) subjectS = some resultS
    rw [show P8Census.skeletonMemoryAxis servedSkeletonRow 1 = 2 from rfl]
    exact slot_subjectS

theorem op3_recordEq :
    ∀ s ∈ computeSkeletonRows (skelMG op3Exec),
      ServedLookupBridge.SkeletonRecordEquations s := by
  intro s hs
  rw [computeSkeletonRowsMG_op3] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact
      { s0_record := fun h => absurd h (by simp [parentSkeletonRowG, op3Exec, op3ParentPubS])
        s9_record := fun h => absurd h (by simp [parentSkeletonRowG, op3Exec, op3ParentPubS]) }
  · exact
      { s0_record := fun _ => ⟨rfl, rfl⟩
        s9_record := fun h => absurd h (by simp [servedSkeletonRow]) }

theorem op3_sizeWindowB :
    SizeWindowCounting.SizeWindowNounsBoundedBy (skelMG op3Exec) 3 := by
  intro n hn
  rw [SizeWindowCounting.skeletonSizeWindowNouns, computeSkeletonRowsMG_op3] at hn
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hn
  have hp : SizeWindowCounting.requiredSizeWindowNouns (parentSkeletonRowG op3Exec) = [resultS] :=
    rfl
  have hs : SizeWindowCounting.requiredSizeWindowNouns servedSkeletonRow = [] := rfl
  rw [hp, hs] at hn
  simp only [List.mem_singleton, List.not_mem_nil, or_false] at hn
  subst hn
  decide

theorem parentSkeletonRowG_op3_bounded : (parentSkeletonRowG op3Exec).BoundedBy 97 := by
  refine ⟨by simp [parentSkeletonRowG, op3Exec, subjectS, FieldEmbedding.BoundedBy], ?_, ?_,
    ?_, ?_, ?_⟩
  · show FieldEmbedding.BoundedBy 97 op3ParentFormulaS
    exact op3Params.hformulaBounded
  · show FieldEmbedding.BoundedBy 97 op3ParentResultS
    exact op3Params.hresultBounded
  · intro slot h
    cases slot <;>
      simp [parentSkeletonRowG, op3Exec, op3Params, op3ParentHeadS, formulaS, headS, tailS,
        FieldEmbedding.BoundedBy]
  · intro i h slot
    cases slot <;>
      simp [parentSkeletonRowG, op3Exec, op3Params, subjectS, formulaS, headS, tailS, resultS,
        FieldEmbedding.BoundedBy]
  · intro i h
    exact ⟨by simp [parentSkeletonRowG, op3Exec, op3Params, parentRecordSkeletonG,
        op3ParentFormulaS, op3ParentHeadS, formulaS, headS, tailS, FieldEmbedding.BoundedBy],
      by simp [parentSkeletonRowG, op3Exec, op3Params, parentRecordSkeletonG, formulaS, headS,
        tailS, FieldEmbedding.BoundedBy]⟩

theorem memorySkeletonRowsMG_op3 :
    memorySkeletonRows (skelMG op3Exec) =
      [dummyHaltSkel, aReadOuterSkelG op3Params, bReadSkel, aDecomposeOuterSkelG op3Params,
        bDecomposeSkel, aHeadHaltSkelG op3Params, aReadInnerSkel, bVerifySkel, bTailHaltSkel,
        aVerifyOuterSkelG op3Params, bResultHaltSkel, aDecomposeInnerSkel, aInnerHeadHaltSkel,
        aVerifyInnerSkel, aTailHaltSkel] := by
  norm_num [memorySkeletonRows, skelMG, skeletonOfNodes, memoryNodesMG, mapNTree,
    dummyHaltNodeTree, rootANodeTreeG, aDecomposeOuterNodeTreeG, aHeadHaltNodeTreeG,
    aReadInnerNodeTreeG, aVerifyOuterNodeTreeG, aDecomposeInnerNodeTree, aInnerHeadHaltNodeTree,
    aVerifyInnerNodeTree, aTailHaltNodeTree, rootBNodeTree, bDecomposeNodeTree,
    bVerifyNodeTree, bResultHaltNodeTree, bTailHaltNodeTree, memNode,
    bfsForest, NTree.size, totalSize, op3Exec]

theorem op3_memorySkeletonRowsBounded :
    ∀ s ∈ memorySkeletonRows (skelMG op3Exec), s.BoundedBy 97 := by
  intro s hs
  rw [memorySkeletonRowsMG_op3] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by simp [dummyHaltSkel, FieldEmbedding.BoundedBy],
      fun i h => by simp [dummyHaltSkel, MemoryTable.fanoutMem] at h,
      fun h => by simp [dummyHaltSkel, memoryMemRecKind] at h⟩
  · exact ⟨by simp [aReadOuterSkelG, op3Params, op3ParentFormulaS, op3ParentHeadS, formulaS,
      headS, tailS, FieldEmbedding.BoundedBy],
      fun i h => by simp [aReadOuterSkelG, op3Params, op3ParentFormulaS, op3ParentHeadS, formulaS,
        headS, tailS, FieldEmbedding.BoundedBy],
      fun h => ⟨by simp [aReadOuterSkelG, op3Params, parentRecordSkeletonG, op3ParentFormulaS,
          op3ParentHeadS, formulaS, headS, tailS, FieldEmbedding.BoundedBy],
        by simp [aReadOuterSkelG, op3Params, parentRecordSkeletonG, formulaS, headS, tailS,
          FieldEmbedding.BoundedBy]⟩⟩
  · exact ⟨by simp [bReadSkel, subjectS, FieldEmbedding.BoundedBy],
      fun i h => by simp [bReadSkel, subjectS, FieldEmbedding.BoundedBy],
      fun h => ⟨by simp [bReadSkel, servedRecordSkeleton, subjectS, FieldEmbedding.BoundedBy],
        by simp [bReadSkel, servedRecordSkeleton, resultS, FieldEmbedding.BoundedBy]⟩⟩
  · refine ⟨by simp [aDecomposeOuterSkelG, op3Params, op3ParentFormulaS, op3ParentHeadS, formulaS,
      headS, tailS, FieldEmbedding.BoundedBy], ?_, fun h => nomatch h⟩
    intro i h
    fin_cases i <;>
      simp [aDecomposeOuterSkelG, op3Params, op3ParentHeadS, formulaS, headS, tailS,
        FieldEmbedding.BoundedBy]
  · refine ⟨by simp [bDecomposeSkel, subjectS, FieldEmbedding.BoundedBy], ?_,
      fun h => nomatch h⟩
    intro i h
    fin_cases i <;>
      simp [bDecomposeSkel, resultS, bTailNoun, FieldEmbedding.BoundedBy]
  · exact ⟨by simp [aHeadHaltSkelG, op3Params, op3ParentHeadS, FieldEmbedding.BoundedBy],
      (fun i h => nomatch h), fun h => nomatch h⟩
  · exact ⟨by simp [aReadInnerSkel, formulaS, headS, tailS, FieldEmbedding.BoundedBy],
      fun i h => by simp [aReadInnerSkel, formulaS, headS, tailS, FieldEmbedding.BoundedBy],
      fun h => ⟨by simp [aReadInnerSkel, innerRecordSkeleton, formulaS, headS, tailS,
          FieldEmbedding.BoundedBy],
        by simp [aReadInnerSkel, innerRecordSkeleton, tailS, FieldEmbedding.BoundedBy]⟩⟩
  · exact ⟨by simp [bVerifySkel, resultS, FieldEmbedding.BoundedBy],
      fun i h => by simp [bVerifySkel, resultS, FieldEmbedding.BoundedBy],
      fun h => ⟨by simp [bVerifySkel, servedRecordSkeleton, subjectS, FieldEmbedding.BoundedBy],
        by simp [bVerifySkel, servedRecordSkeleton, resultS, FieldEmbedding.BoundedBy]⟩⟩
  · exact ⟨by simp [bTailHaltSkel, bTailNoun, FieldEmbedding.BoundedBy],
      (fun i h => nomatch h), fun h => nomatch h⟩
  · exact ⟨by simp [aVerifyOuterSkelG, formulaS, headS, tailS, FieldEmbedding.BoundedBy],
      fun i h => by simp [aVerifyOuterSkelG, formulaS, headS, tailS, FieldEmbedding.BoundedBy],
      fun h => ⟨by simp [aVerifyOuterSkelG, op3Params, parentRecordSkeletonG, op3ParentFormulaS,
          op3ParentHeadS, formulaS, headS, tailS, FieldEmbedding.BoundedBy],
        by simp [aVerifyOuterSkelG, parentRecordSkeletonG, formulaS, headS, tailS,
          FieldEmbedding.BoundedBy]⟩⟩
  · exact ⟨by simp [bResultHaltSkel, resultS, FieldEmbedding.BoundedBy],
      (fun i h => nomatch h), fun h => nomatch h⟩
  · refine ⟨by simp [aDecomposeInnerSkel, formulaS, headS, tailS, FieldEmbedding.BoundedBy],
      ?_, fun h => nomatch h⟩
    intro i h
    fin_cases i <;>
      simp [aDecomposeInnerSkel, headS, tailS, FieldEmbedding.BoundedBy]
  · exact ⟨by simp [aInnerHeadHaltSkel, headS, FieldEmbedding.BoundedBy],
      (fun i h => nomatch h), fun h => nomatch h⟩
  · exact ⟨by simp [aVerifyInnerSkel, tailS, FieldEmbedding.BoundedBy],
      fun i h => by simp [aVerifyInnerSkel, tailS, FieldEmbedding.BoundedBy],
      fun h => ⟨by simp [aVerifyInnerSkel, innerRecordSkeleton, formulaS, headS, tailS,
          FieldEmbedding.BoundedBy],
        by simp [aVerifyInnerSkel, innerRecordSkeleton, tailS, FieldEmbedding.BoundedBy]⟩⟩
  · exact ⟨by simp [aTailHaltSkel, tailS, FieldEmbedding.BoundedBy],
      (fun i h => nomatch h), fun h => nomatch h⟩

theorem op3_skelBounded : (skelMG op3Exec).BoundedBy 97 := by
  refine { computeRows := ?_, memoryRows := ?_, memoryTrees := ?_ }
  · rw [computeSkeletonRowsMG_op3]
    exact ⟨parentSkeletonRowG_op3_bounded, servedSkeletonRow_bounded⟩
  · rw [List.forall_iff_forall_mem]
    exact op3_memorySkeletonRowsBounded
  · intro tree htree node hnode
    have hm : node ∈ bfsForest (skelMG op3Exec).memoryForest :=
      (mem_bfsForest (skelMG op3Exec).memoryForest node).2 ⟨tree, htree, hnode⟩
    have hlbl : node.label ∈ memorySkeletonRows (skelMG op3Exec) :=
      List.mem_map_of_mem hm
    exact op3_memorySkeletonRowsBounded _ hlbl

theorem skeletonComparisonCensusMG_op3 :
    P8Census.skeletonComparisonCensus (K := K97cubic) (skelMG op3Exec) =
      P8Census.skeletonComparisons (K := K97cubic) (parentSkeletonRowG op3Exec) ++
        P8Census.skeletonComparisons (K := K97cubic) servedSkeletonRow := by
  rw [P8Census.skeletonComparisonCensus, computeSkeletonRowsMG_op3]
  simp

theorem op3ParentResultS_leaves : op3ParentResultS.leaves ≤ 3 := by
  rw [op3ParentResultS_atom]; decide

theorem op3ParentResultS_bounded : FieldEmbedding.BoundedBy 97 op3ParentResultS := by
  rw [op3ParentResultS_atom]; simp [FieldEmbedding.BoundedBy]

def op3_censusC : EdgeComparisonCensus.CombinedSkeletonCensus K97cubic (skelMG op3Exec) 3 where
  p8 :=
    { leaves_bounded := by
        intro pair hp
        rw [BoundSemanticTrace.skeletonPairs, skeletonComparisonCensusMG_op3] at hp
        simp [P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
          P8Census.skeletonSubformula, P8Census.skeletonMemoryAxis,
          SemanticTrace.ComparisonUse.pair, skelMG, skeletonOfNodes, computeNodesMG,
          mapNTree, parentNodeG, parentSkeletonRowG, op3Exec, op3Params, op3ParentPubS,
          servedSkeletonRow, SemanticSkeleton.publicClaim, decActive, hasTailDecomposition,
          servedRecordSkeleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [subjectS, op3ParentFormulaS, op3ParentResultS_atom, op3ParentHeadS, formulaS, headS,
            tailS, resultS, ComputeTable.fanoutComp, Nock.Framework.recordCount,
            Noun.wut, Noun.leaves] }
  edges :=
    { leaves_bounded := by
        intro pair hp
        rw [EdgeComparisonCensus.edgePairs] at hp
        simp [skelMG, skeletonOfNodes, computeNodesMG, mapNTree, parentNodeG, op3Exec, op3Params,
          op3ParentPubS, servedNode,
          bfsForest, NTree.size, totalSize, EdgeComparisonCensus.rowEdgePairs,
          EdgeComparisonCensus.edgeTriple, NTree.childOpt,
          P8Census.skeletonSubformula, parentSkeletonRowG, servedSkeletonRow,
          ComputeTable.fanoutComp] at hp
        rcases hp with rfl | rfl | rfl <;>
          simp [subjectS, formulaS, headS, tailS, resultS, Noun.leaves] }

theorem op3_combinedB :
    ProductionP8Containment.CombinedBoundedBy K97cubic 97 (skelMG op3Exec) := by
  intro pair hp
  rw [EdgeComparisonCensus.combinedSkeletonPairs, List.mem_append] at hp
  rcases hp with hp | hp
  · rw [BoundSemanticTrace.skeletonPairs, skeletonComparisonCensusMG_op3] at hp
    simp [P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
      P8Census.skeletonSubformula, P8Census.skeletonMemoryAxis,
      SemanticTrace.ComparisonUse.pair, skelMG, skeletonOfNodes, computeNodesMG,
      mapNTree, parentNodeG, parentSkeletonRowG, op3Exec, op3Params, op3ParentPubS,
      servedSkeletonRow, SemanticSkeleton.publicClaim, decActive, hasTailDecomposition,
      servedRecordSkeleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [subjectS, op3ParentFormulaS, op3ParentResultS_atom, op3ParentHeadS, formulaS, headS,
        tailS, resultS, ComputeTable.fanoutComp, Nock.Framework.recordCount,
        op3ParentResultS_bounded, Noun.wut, FieldEmbedding.BoundedBy]
  · rw [EdgeComparisonCensus.edgePairs] at hp
    simp [skelMG, skeletonOfNodes, computeNodesMG, mapNTree, parentNodeG, op3Exec, op3Params,
      op3ParentPubS, servedNode,
      bfsForest, NTree.size, totalSize, EdgeComparisonCensus.rowEdgePairs,
      EdgeComparisonCensus.edgeTriple, NTree.childOpt,
      P8Census.skeletonSubformula, parentSkeletonRowG, servedSkeletonRow,
      ComputeTable.fanoutComp] at hp
    rcases hp with rfl | rfl | rfl <;>
      simp [subjectS, formulaS, headS, tailS, resultS, FieldEmbedding.BoundedBy]


theorem op3s_leafIs : GeneratedField.LeafIs (K := K97cubic) 2 (.cell (.atom 7) (.atom 9)) (.cell (.atom 3) (.cell (.atom 0) (.atom 2))) 3 := by
  gen_simp

theorem op3s_evalIsSome : (FieldEmbedding.evalGBy (ringChar K97cubic) 2 (.cell (.atom 7) (.atom 9)) (.cell (.atom 3) (.cell (.atom 0) (.atom 2)))).isSome := by
  have h97 := MultiRootServedFixture.ringChar_K97
  simp [h97, FieldEmbedding.evalGBy, FieldEmbedding.lusGBy, Noun.slot]

/-- Program-level `generated` at any window `Λ ≥ 3`. -/
theorem op3s_program_generated (Λ : ℕ) (hΛ : 3 ≤ Λ) :
    ∃ (gfuel : ℕ) (G : Nock.Walk.NTree (TraceGen.GenComputeRow K97cubic)) (R : Noun) (fuel : ℕ)
      (r : Noun),
      TraceGen.genComputeSkeleton (K := K97cubic) gfuel (.cell (.atom 7) (.atom 9)) (.cell (.atom 3) (.cell (.atom 0) (.atom 2))) = .ok (G, R) ∧
        FieldEmbedding.evalGBy (ringChar K97cubic) fuel (.cell (.atom 7) (.atom 9)) (.cell (.atom 3) (.cell (.atom 0) (.atom 2))) = some r ∧
        TraceGen.programLeafBound (TraceGen.airReorder G) ≤ Λ :=
  GeneratedField.generated_of _ _ _ _ 2 2 (GeneratedField.le_of_leafIs op3s_leafIs hΛ)
    op3s_evalIsSome

/-- Negative control: zero margin (`Λ = 2` is refuted). -/
theorem op3s_leaf_margin_zero :
    ¬ ∃ (G : Nock.Walk.NTree (TraceGen.GenComputeRow K97cubic)) (R : Noun),
      TraceGen.genComputeSkeleton (K := K97cubic) 2 (.cell (.atom 7) (.atom 9)) (.cell (.atom 3) (.cell (.atom 0) (.atom 2))) = .ok (G, R) ∧
        TraceGen.programLeafBound (TraceGen.airReorder G) ≤ 2 := by
  rintro ⟨G, R, hx, hle⟩
  have h := op3s_leafIs
  unfold GeneratedField.LeafIs at h
  rw [hx] at h
  simp only at h
  omega

theorem op3_skel_claim :
    (skelMG op3Exec).publicClaim.subject = (.cell (.atom 7) (.atom 9)) ∧ (skelMG op3Exec).publicClaim.formula = (.cell (.atom 3) (.cell (.atom 0) (.atom 2))) := by
  show (skelMG op3Exec).computeTree.label.subject = (.cell (.atom 7) (.atom 9)) ∧
    (skelMG op3Exec).computeTree.label.formula = (.cell (.atom 3) (.cell (.atom 0) (.atom 2)))
  simp [skelMG, skeletonOfNodes, mapNTree_label]
  all_goals (try refine ⟨?_, ?_⟩)
  all_goals first | rfl | decide

theorem op3_generatedC : GeneratedField.ClaimGenerated K97cubic (skelMG op3Exec).publicClaim 3 :=
  GeneratedField.claimGenerated_of_eq op3_skel_claim.1 op3_skel_claim.2
    (op3s_program_generated 3 le_rfl)

/-! ## G. `op3Commit` and the released OP₃ statement -/

/-- **The OP₃ honest commitment.** -/
def op3Commit : ServedForestCommit where
  toServedForestExec := op3Exec
  parentComputeBind := bind_parentRowG_op3
  parentComputeStamp := stamp_parentRowG_op3
  slotSem := op3_slotSem
  recordEq := op3_recordEq
  censusC := op3_censusC
  sizeWindowB := op3_sizeWindowB
  skelBounded := op3_skelBounded
  combinedB := op3_combinedB
  pairedRecordLayout := pairedRecordLayoutSG _
  honestVer := honestVerSG _
  generatedC := op3_generatedC

/-- **The released fourteen-conjunct Theorem-5.4 statement over the generic OP₃ package.** -/
theorem op3Statement
    (hmoreMG : BuildableAxisWitness.LaterSeedZeros
      (servedForestModule op3Commit.toServedForestExec))
    (hax : FormRAxisBound (packageMG op3Commit hmoreMG).optimized.sampled
      (packageMG op3Commit hmoreMG).optimized.basis)
    (hbasis : FormRBasis (packageMG op3Commit hmoreMG).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageMG op3Commit hmoreMG) :=
  statementMG op3Commit hmoreMG hax hbasis hwidth

theorem op3Statement_nonvacuous
    (hmoreMG : BuildableAxisWitness.LaterSeedZeros
      (servedForestModule op3Commit.toServedForestExec))
    (hax : FormRAxisBound (packageMG op3Commit hmoreMG).optimized.sampled
      (packageMG op3Commit hmoreMG).optimized.basis)
    (hbasis : FormRBasis (packageMG op3Commit hmoreMG).optimized.basis)
    (hwidth : FormRWidth F97) :
    Nonempty
      (OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageMG op3Commit hmoreMG)) :=
  ⟨op3Statement hmoreMG hax hbasis hwidth⟩

end

end Nock.NockVMROM.Thm54.ServedForestModule

#print axioms Nock.NockVMROM.Thm54.ServedForestModule.op3Exec
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.op3Commit
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.op3Statement
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.op3Statement_nonvacuous
