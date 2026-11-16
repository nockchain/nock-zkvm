/-
  Nock/NockVMROM/Thm54/TraceGen/Op9LanguageK3.lean

  Stage 4d of the OP9 Layer-2 CORE, over `K3`: semantic IO preimage,
  chained/traversable language, noun realization, and the assembled
  `ExactExecutionSemanticData 97 7` for the fan-out-2 invoke program

      `*[0 [9 [2 [1 [[1 7] [1 9]]]]]] = 7`

  Five committed records: parent formula@3 (`α¹`), parent tail@2 (`α²`),
  arm-fetch core@2 (`α³`), child1 coreFormula@3 (`α⁴`), child2 arm@3 (`α⁵`).
-/
import Nock.NockVMROM.Thm54.TraceGen.Op9RowWebK3
import Nock.NockVMROM.Thm54.TraceGen.Op9MemoryTraceK3
import Nock.NockVMROM.Thm54.Language
import Nock.NockVMROM.Thm54.NounRealization
import Mathlib.Tactic.IntervalCases

namespace Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3

open Nock Nock.Walk Nock.NockVM Nock.MemoryTable Nock.ComputeTable
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

/-! ## A. Semantic IO preimage -/

def semOf (axis : F) (root child : Noun) (exp : ℕ) : (nmrMEF F K).Rec :=
  (axis,
    ((((fp seedZ root).size, (fp seedZ root).dyck, (fp seedZ root).leaf),
      ((fp seedZ child).size, (fp seedZ child).dyck, (fp seedZ child).leaf)),
    exp))

def semF : (nmrMEF F K).Rec := semOf 3 op9ParentFormula op9ParentTail 1
def semT : (nmrMEF F K).Rec := semOf 2 op9ParentTail op9AxisAtom 2
def semArm : (nmrMEF F K).Rec := semOf 2 op9CoreNoun op9Arm 3
def semCoreF : (nmrMEF F K).Rec := semOf 3 op9CoreFormula op9CoreNoun 4
def semArmF : (nmrMEF F K).Rec := semOf 3 op9Arm op9Result 5

theorem semF_preimage :
    memRecOfNMR F K ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semF) =
      recF seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semF, semOf, cfg, recF, seedZ, alphaA, map_ofNat]

theorem semT_preimage :
    memRecOfNMR F K ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semT) =
      recT seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semT, semOf, cfg, recT, seedZ, alphaA, map_ofNat,
    pow_two]

theorem semArm_preimage :
    memRecOfNMR F K ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semArm) =
      recArm seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semArm, semOf, cfg, recArm, seedZ, alphaA, map_ofNat,
    pow_succ]

theorem semCoreF_preimage :
    memRecOfNMR F K ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semCoreF) =
      recCoreF seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semCoreF, semOf, cfg, recCoreF, seedZ, alphaA,
    map_ofNat, pow_succ]

theorem semArmF_preimage :
    memRecOfNMR F K ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semArmF) =
      recArmF seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semArmF, semOf, cfg, recArmF, seedZ, alphaA,
    map_ofNat, pow_succ]

theorem semF_bridge :
    bridge F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semF =
      NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees, semF_preimage]
  rfl
theorem semT_bridge :
    bridge F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semT =
      NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees, semT_preimage]
  rfl
theorem semArm_bridge :
    bridge F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semArm =
      NockVM.encRecFormR (recArm seedZ alphaA) MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees, semArm_preimage]
  rfl
theorem semCoreF_bridge :
    bridge F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semCoreF =
      NockVM.encRecFormR (recCoreF seedZ alphaA) MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees, semCoreF_preimage]
  rfl
theorem semArmF_bridge :
    bridge F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semArmF =
      NockVM.encRecFormR (recArmF seedZ alphaA) MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees, semArmF_preimage]
  rfl

theorem semResp_nodup : [semF, semT, semArm, semCoreF, semArmF].Nodup := by
  simp [semF, semT, semArm, semCoreF, semArmF, semOf]

/-- `4` has multiplicative order `24` in `ZMod 97`. -/
theorem alphaA_order_base : orderOf (4 : F) = 24 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

/-- `α = 4 = φ 4` keeps multiplicative order `24` in `K3`. -/
theorem alphaA_order : orderOf alphaA = 24 := by
  have h := orderOf_injective φ.toMonoidHom φ_injective (4 : F)
  rw [alphaA_order_base] at h
  rw [alphaA_eq_image]; simpa using h

def semanticPreimage :
    SemanticIOPreimage (cfg seedZ alphaA) (exec seedZ alphaA) where
  timestampBound := 6
  timestampBound_le_order := by
    change 6 ≤ orderOf alphaA
    rw [alphaA_order]; norm_num
  semanticRequests := [semF, semT, semArm, semCoreF, semArmF]
  semanticResponses := [semF, semArm, semT, semArmF, semCoreF]
  requestTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [semF, semT, semArm, semCoreF, semArmF, semOf]
  responseTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [semF, semT, semArm, semCoreF, semArmF, semOf]
  semantic_lmio := by
    refine ⟨by norm_num [IO.InRange, cfg],
      [semF, semT, semArm, semCoreF, semArmF], le_refl _, semResp_nodup, ?_, ?_⟩
    · tauto
    · exact List.Perm.cons _ (List.Perm.trans (List.Perm.swap _ _ _)
        (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _))))
  requestTimestamp_determines := by
    intro x hx y hy h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (simp [semF, semT, semArm, semCoreF, semArmF, semOf] at h)
  requests_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
      List.map_cons, List.map_nil,
      semF_bridge, semT_bridge, semArm_bridge, semCoreF_bridge, semArmF_bridge,
      derived_requests]
  responses_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
      List.map_cons, List.map_nil,
      semF_bridge, semArm_bridge, semT_bridge, semArmF_bridge, semCoreF_bridge,
      derived_responses]

theorem semanticExactLanguage :
    SemanticExactLanguage (cfg seedZ alphaA) (exec seedZ alphaA) :=
  ⟨computeRowsAccepted, memoryRowsAccepted, ⟨semanticPreimage⟩⟩

/-! ## B. Chained boundaries and traversable topology -/

/-- Every executed memory row carries the package `λ = formRDefault` (row encode). -/
theorem exec_lambda_package :
    ∀ i, ((exec seedZ alphaA).memoryPubAt i).lambda? = some MemoryTable.formRDefault := by
  intro i
  fin_cases i
  · rw [memoryPubAt_0]; simp only [pReadF, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_1]; simp only [pReadArm, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_2]; simp only [pDecPF, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_3]; simp only [pDecCN_B, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_4]; simp only [pHalt9, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_5]; simp only [pVerifyF, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_6]; simp only [pVerifyArm, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_7]; simp only [pDecCT_B, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_8]; simp only [pReadT, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_9]; simp only [pReadArmF, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_10]; simp only [pHaltH1_B2, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_11]; simp only [pHaltA9_B, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_12]; simp only [pDecPT, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_13]; simp only [pDecArmB, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_14]; simp only [pVerifyT, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_15]; simp only [pReadCoreF, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_16]; simp only [pHaltH1_B1, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_17]; simp only [pVerifyArmF, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_18]; simp only [pHaltA2, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_19]; simp only [pDecCF, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_20]; simp only [pHaltA7_B, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_21]; simp only [pHaltH1a, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_22]; simp only [pVerifyCoreF, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_23]; simp only [pDecCN, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_24]; simp only [pDecArmA, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_25]; simp only [pDecCTA, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_26]; simp only [pHaltH1b, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_27]; simp only [pHaltA7, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_28]; simp only [pHaltH1c, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_29]; simp only [pHaltA9, readPub, decPub, verifyPub, haltPub]

theorem chained
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    ChainedSemanticExactLanguage (cfg seedZ alphaA) (exec seedZ alphaA) where
  semantic := semanticExactLanguage
  z_ne_zero := seedZ_ne_zero
  compute_wf := compute_wf_all
  memory_wf := memory_wf_all
  compute_chain := compute_chain
  memory_chain := memory_chain
  memory_first_counts := hfirst.1
  memory_first_indicator := hfirst.2
  memory_first_ipre := by rw [memoryPubAt_0]; rfl
  memory_last_icur := by
    have hlast :
        (cfg seedZ alphaA).orbit.lastIndex (cfg seedZ alphaA).memRows
          (cfg seedZ alphaA).memRows_pos = ⟨29, by norm_num [cfg]⟩ := rfl
    rw [hlast, memoryPubAt_29]; rfl

  memory_same_lambda := ExactExecution.memory_same_lambda_of_const _ (some MemoryTable.formRDefault)
    exec_lambda_package

theorem traversable
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    TraversableChainedSemanticExactLanguage (cfg seedZ alphaA) (exec seedZ alphaA) where
  chained := chained hfirst
  compute_topology := compute_topology
  memory_topology := memory_topology

/-! ## C. Bounded noun realization -/

theorem bounded_subject : FieldEmbedding.BoundedBy 97 op9Subject := by
  simp [op9Subject, FieldEmbedding.BoundedBy]
theorem bounded_head : FieldEmbedding.BoundedBy 97 op9Head := by
  simp [op9Head, FieldEmbedding.BoundedBy]
theorem bounded_axisAtom : FieldEmbedding.BoundedBy 97 op9AxisAtom := by
  simp [op9AxisAtom, FieldEmbedding.BoundedBy]
theorem bounded_result : FieldEmbedding.BoundedBy 97 op9Result := by
  simp [op9Result, FieldEmbedding.BoundedBy]
theorem bounded_op1Head : FieldEmbedding.BoundedBy 97 op1Head := by
  simp [op1Head, FieldEmbedding.BoundedBy]
theorem bounded_coreNoun : FieldEmbedding.BoundedBy 97 op9CoreNoun := by
  simp [op9CoreNoun, FieldEmbedding.BoundedBy]
theorem bounded_arm : FieldEmbedding.BoundedBy 97 op9Arm := by
  simp [op9Arm, FieldEmbedding.BoundedBy]
theorem bounded_coreFormula : FieldEmbedding.BoundedBy 97 op9CoreFormula := by
  simp [op9CoreFormula, op9CoreNoun, FieldEmbedding.BoundedBy]
theorem bounded_parentTail : FieldEmbedding.BoundedBy 97 op9ParentTail := by
  simp [op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun, FieldEmbedding.BoundedBy]
theorem bounded_formula : FieldEmbedding.BoundedBy 97 op9ParentFormula := by
  simp [op9ParentFormula, op9ParentTail, op9AxisAtom, op9CoreFormula, op9CoreNoun,
    FieldEmbedding.BoundedBy]
theorem bounded_coreTail : FieldEmbedding.BoundedBy 97 op9CoreTail := by
  simp [op9CoreTail, FieldEmbedding.BoundedBy]

theorem fpRealized {n : Noun} (hb : FieldEmbedding.BoundedBy 97 n) :
    FPRealized seedZ 97 (fp seedZ n) :=
  ⟨n, hb, rfl⟩

theorem fpActive {n : Noun} (hb : FieldEmbedding.BoundedBy 97 n) :
    FPSlotRealized seedZ 97 .active (fp seedZ n) :=
  ⟨fpRealized hb, FPRealized.ne_zero seedZ_ne_zero (fpRealized hb)⟩

theorem alphaA_ne_zero : alphaA ≠ 0 := by rw [alphaA]; decide

theorem recF_ne_zero : recF seedZ alphaA ≠ MemRec.zero := fun h =>
  alphaA_ne_zero (by simpa [recF, MemRec.zero] using congrArg MemRec.ts h)
theorem recT_ne_zero : recT seedZ alphaA ≠ MemRec.zero := fun h =>
  (pow_ne_zero 2 alphaA_ne_zero) (by simpa [recT, MemRec.zero] using congrArg MemRec.ts h)
theorem recArm_ne_zero : recArm seedZ alphaA ≠ MemRec.zero := fun h =>
  (pow_ne_zero 3 alphaA_ne_zero) (by simpa [recArm, MemRec.zero] using congrArg MemRec.ts h)
theorem recCoreF_ne_zero : recCoreF seedZ alphaA ≠ MemRec.zero := fun h =>
  (pow_ne_zero 4 alphaA_ne_zero)
    (by simpa [recCoreF, MemRec.zero] using congrArg MemRec.ts h)
theorem recArmF_ne_zero : recArmF seedZ alphaA ≠ MemRec.zero := fun h =>
  (pow_ne_zero 5 alphaA_ne_zero)
    (by simpa [recArmF, MemRec.zero] using congrArg MemRec.ts h)

theorem recF_active : MemRecSlotRealized seedZ 97 .active (recF seedZ alphaA) :=
  ⟨recF_ne_zero, fpActive bounded_formula, fpActive bounded_parentTail⟩
theorem recT_active : MemRecSlotRealized seedZ 97 .active (recT seedZ alphaA) :=
  ⟨recT_ne_zero, fpActive bounded_parentTail, fpActive bounded_axisAtom⟩
theorem recArm_active : MemRecSlotRealized seedZ 97 .active (recArm seedZ alphaA) :=
  ⟨recArm_ne_zero, fpActive bounded_coreNoun, fpActive bounded_arm⟩
theorem recCoreF_active : MemRecSlotRealized seedZ 97 .active (recCoreF seedZ alphaA) :=
  ⟨recCoreF_ne_zero, fpActive bounded_coreFormula, fpActive bounded_coreNoun⟩
theorem recArmF_active : MemRecSlotRealized seedZ 97 .active (recArmF seedZ alphaA) :=
  ⟨recArmF_ne_zero, fpActive bounded_arm, fpActive bounded_result⟩

/-! ### Per-row compute public realizations -/

theorem parentRow_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel (parentRow seedZ alphaA)) where
  subject := fpActive bounded_subject
  formula := fpActive bounded_formula
  evaluation := fpActive bounded_result
  subformula := by
    intro i; fin_cases i
    · exact ⟨fpActive bounded_subject, fpActive bounded_coreFormula,
        fpActive bounded_coreNoun⟩
    · exact ⟨fpActive bounded_coreNoun, fpActive bounded_arm, fpActive bounded_result⟩
    · exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recF_active
    · exact recT_active
    · exact recArm_active

theorem child1Row_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel (child1Row seedZ alphaA)) where
  subject := fpActive bounded_subject
  formula := fpActive bounded_coreFormula
  evaluation := fpActive bounded_coreNoun
  subformula := by intro i; fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recCoreF_active
    · rfl
    · rfl

theorem child2Row_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel (child2Row seedZ alphaA)) where
  subject := fpActive bounded_coreNoun
  formula := fpActive bounded_arm
  evaluation := fpActive bounded_result
  subformula := by intro i; fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recArmF_active
    · rfl
    · rfl

theorem computeTreeNounRealization :
    ComputePublicTreeNounRealization 97 (exec seedZ alphaA).computePublicTree := by
  have h : (bfsForest [(exec seedZ alphaA).computePublicTree]).map NTree.label =
      [computePublicLabel (parentRow seedZ alphaA),
        computePublicLabel (child1Row seedZ alphaA),
        computePublicLabel (child2Row seedZ alphaA)] := by
    rw [ExactExecution.computePublicTree_bfs, ExactExecution.computePublicRows, computeRows_eq]
    rfl
  unfold ComputePublicTreeNounRealization ComputePublicRowsNounRealization
  rw [h]
  refine List.forall_iff_forall_mem.mpr ?_
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl
  · exact parentRow_nounRealization
  · exact child1Row_nounRealization
  · exact child2Row_nounRealization

/-! ### Memory row public realizations -/

theorem memSingleChildRealization (pub : MemoryTable.Pub K)
    (hst : MemoryTable.fanoutMem pub.st = 1)
    (hpt : FPSlotRealized seedZ 97 .active pub.pt.noun)
    (hlc : FPSlotRealized seedZ 97 .active pub.lc.noun)
    (hrc : pub.rc = MemoryTable.Cell.zero)
    (hkind : memoryMemRecKind pub.st = .active)
    (hmem : MemRecSlotRealized seedZ 97 .active pub.mem) :
    MemoryPublicRowNounRealization 97 (lblOf seedZ pub) where
  parent := hpt
  child := by
    intro i; fin_cases i
    · show MemoryCellSlotRealized seedZ 97 (memoryChildKind pub.st 0) pub.lc
      rw [memoryChildKind, hst]; simpa [MemoryCellSlotRealized] using hlc
    · show MemoryCellSlotRealized seedZ 97 (memoryChildKind pub.st 1) pub.rc
      rw [memoryChildKind, hst]; simpa [MemoryCellSlotRealized] using hrc
  memoryRecord := by
    show MemRecSlotRealized seedZ 97 (memoryMemRecKind pub.st) pub.mem
    rw [hkind]; exact hmem

theorem memDecomposeRealization (pub : MemoryTable.Pub K)
    (hpt : FPSlotRealized seedZ 97 .active pub.pt.noun)
    (hlc : FPSlotRealized seedZ 97 .active pub.lc.noun)
    (hrc : FPSlotRealized seedZ 97 .active pub.rc.noun)
    (hmem : pub.mem = MemRec.zero) :
    MemoryPublicRowNounRealization 97
      (MemoryTable.MState.decompose, (memInputs seedZ, pub)) where
  parent := hpt
  child := by
    intro i; fin_cases i
    · exact hlc
    · exact hrc
  memoryRecord := hmem

theorem memHaltRealization (pub : MemoryTable.Pub K)
    (hpt : FPSlotRealized seedZ 97 .active pub.pt.noun)
    (hlc : pub.lc = MemoryTable.Cell.zero)
    (hrc : pub.rc = MemoryTable.Cell.zero)
    (hmem : pub.mem = MemRec.zero) :
    MemoryPublicRowNounRealization 97
      (MemoryTable.MState.halt, (memInputs seedZ, pub)) where
  parent := hpt
  child := by
    intro i; fin_cases i
    · exact hlc
    · exact hrc
  memoryRecord := hmem

theorem memoryForestNounRealization :
    MemoryPublicForestNounRealization 97 (exec seedZ alphaA).memoryForest := by
  unfold MemoryPublicForestNounRealization MemoryPublicRowsNounRealization
  rw [show (bfsForest (exec seedZ alphaA).memoryForest).map NTree.label =
      (exec seedZ alphaA).memoryRows from rfl, memoryRows_eq]
  refine List.forall_iff_forall_mem.mpr ?_
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- Row 0: pReadF (read_root, pt=formula, lc=formula, rec=recF)
  · exact memSingleChildRealization _ rfl
      (fpActive bounded_formula) (fpActive bounded_formula) rfl rfl (recF_active.formRRow _)
  -- Row 1: pReadArm (read_root, pt=coreNoun, lc=coreNoun, rec=recArm)
  · exact memSingleChildRealization _ rfl
      (fpActive bounded_coreNoun) (fpActive bounded_coreNoun) rfl rfl (recArm_active.formRRow _)
  -- Row 2: pDecPF (decompose, pt=formula, lc=head, rc=parentTail)
  · exact memDecomposeRealization _
      (fpActive bounded_formula) (fpActive bounded_head) (fpActive bounded_parentTail) rfl
  -- Row 3: pDecCN_B (decompose, pt=coreNoun, lc=arm, rc=coreTail)
  · exact memDecomposeRealization _
      (fpActive bounded_coreNoun) (fpActive bounded_arm) (fpActive bounded_coreTail) rfl
  -- Row 4: pHalt9 (halt, pt=head/atom 9)
  · exact memHaltRealization _ (fpActive bounded_head) rfl rfl rfl
  -- Row 5: pVerifyF (verify_child, pt=parentTail, lc=parentTail, rec=recF)
  · exact memSingleChildRealization _ rfl
      (fpActive bounded_parentTail) (fpActive bounded_parentTail) rfl rfl (recF_active.formRRow _)
  -- Row 6: pVerifyArm (verify_child, pt=arm, lc=arm, rec=recArm)
  · exact memSingleChildRealization _ rfl
      (fpActive bounded_arm) (fpActive bounded_arm) rfl rfl (recArm_active.formRRow _)
  -- Row 7: pDecCT_B (decompose, pt=coreTail, lc=op1Head, rc=head)
  · exact memDecomposeRealization _
      (fpActive bounded_coreTail) (fpActive bounded_op1Head) (fpActive bounded_head) rfl
  -- Row 8: pReadT (read_root, pt=parentTail, lc=parentTail, rec=recT)
  · exact memSingleChildRealization _ rfl
      (fpActive bounded_parentTail) (fpActive bounded_parentTail) rfl rfl (recT_active.formRRow _)
  -- Row 9: pReadArmF (read_root, pt=arm, lc=arm, rec=recArmF)
  · exact memSingleChildRealization _ rfl
      (fpActive bounded_arm) (fpActive bounded_arm) rfl rfl (recArmF_active.formRRow _)
  -- Row 10: pHaltH1_B2 (halt, pt=op1Head/atom 1)
  · exact memHaltRealization _ (fpActive bounded_op1Head) rfl rfl rfl
  -- Row 11: pHaltA9_B (halt, pt=head/atom 9)
  · exact memHaltRealization _ (fpActive bounded_head) rfl rfl rfl
  -- Row 12: pDecPT (decompose, pt=parentTail, lc=axisAtom, rc=coreFormula)
  · exact memDecomposeRealization _
      (fpActive bounded_parentTail) (fpActive bounded_axisAtom) (fpActive bounded_coreFormula) rfl
  -- Row 13: pDecArmB (decompose, pt=arm, lc=op1Head, rc=result)
  · exact memDecomposeRealization _
      (fpActive bounded_arm) (fpActive bounded_op1Head) (fpActive bounded_result) rfl
  -- Row 14: pVerifyT (verify_child, pt=axisAtom, lc=axisAtom, rec=recT)
  · exact memSingleChildRealization _ rfl
      (fpActive bounded_axisAtom) (fpActive bounded_axisAtom) rfl rfl (recT_active.formRRow _)
  -- Row 15: pReadCoreF (read_root, pt=coreFormula, lc=coreFormula, rec=recCoreF)
  · exact memSingleChildRealization _ rfl
      (fpActive bounded_coreFormula) (fpActive bounded_coreFormula) rfl rfl
          (recCoreF_active.formRRow _)
  -- Row 16: pHaltH1_B1 (halt, pt=op1Head/atom 1)
  · exact memHaltRealization _ (fpActive bounded_op1Head) rfl rfl rfl
  -- Row 17: pVerifyArmF (verify_child, pt=result, lc=result, rec=recArmF)
  · exact memSingleChildRealization _ rfl
      (fpActive bounded_result) (fpActive bounded_result) rfl rfl (recArmF_active.formRRow _)
  -- Row 18: pHaltA2 (halt, pt=axisAtom/atom 2)
  · exact memHaltRealization _ (fpActive bounded_axisAtom) rfl rfl rfl
  -- Row 19: pDecCF (decompose, pt=coreFormula, lc=op1Head, rc=coreNoun)
  · exact memDecomposeRealization _
      (fpActive bounded_coreFormula) (fpActive bounded_op1Head) (fpActive bounded_coreNoun) rfl
  -- Row 20: pHaltA7_B (halt, pt=result/atom 7)
  · exact memHaltRealization _ (fpActive bounded_result) rfl rfl rfl
  -- Row 21: pHaltH1a (halt, pt=op1Head/atom 1)
  · exact memHaltRealization _ (fpActive bounded_op1Head) rfl rfl rfl
  -- Row 22: pVerifyCoreF (verify_child, pt=coreNoun, lc=coreNoun, rec=recCoreF)
  · exact memSingleChildRealization _ rfl
      (fpActive bounded_coreNoun) (fpActive bounded_coreNoun) rfl rfl (recCoreF_active.formRRow _)
  -- Row 23: pDecCN (decompose, pt=coreNoun, lc=arm, rc=coreTail)
  · exact memDecomposeRealization _
      (fpActive bounded_coreNoun) (fpActive bounded_arm) (fpActive bounded_coreTail) rfl
  -- Row 24: pDecArmA (decompose, pt=arm, lc=op1Head, rc=result)
  · exact memDecomposeRealization _
      (fpActive bounded_arm) (fpActive bounded_op1Head) (fpActive bounded_result) rfl
  -- Row 25: pDecCTA (decompose, pt=coreTail, lc=op1Head, rc=head)
  · exact memDecomposeRealization _
      (fpActive bounded_coreTail) (fpActive bounded_op1Head) (fpActive bounded_head) rfl
  -- Row 26: pHaltH1b (halt, pt=op1Head/atom 1)
  · exact memHaltRealization _ (fpActive bounded_op1Head) rfl rfl rfl
  -- Row 27: pHaltA7 (halt, pt=result/atom 7)
  · exact memHaltRealization _ (fpActive bounded_result) rfl rfl rfl
  -- Row 28: pHaltH1c (halt, pt=op1Head/atom 1)
  · exact memHaltRealization _ (fpActive bounded_op1Head) rfl rfl rfl
  -- Row 29: pHaltA9 (halt, pt=head/atom 9)
  · exact memHaltRealization _ (fpActive bounded_head) rfl rfl rfl

/-! ### Memory leaf atoms -/

theorem leafAtomHalt (k : ℕ) (hk : k < 97) (acc : K) :
    MemoryLeafAtomsRealized 97 (mLeaf seedZ (haltPub seedZ k acc)) :=
  ⟨k, hk, by
    show ((k : ℕ) : K) = (fp seedZ (Noun.atom k)).leaf
    simp [fp, GlobalCarryRecognizer.enc_atom]⟩

theorem leafAtoms_rootTreeA : MemoryLeafAtomsRealized 97 (rootTreeA seedZ alphaA) :=
  ⟨leafAtomHalt 9 (by norm_num) _,
   ⟨leafAtomHalt 2 (by norm_num) _,
    ⟨leafAtomHalt 1 (by norm_num) _,
     ⟨⟨leafAtomHalt 1 (by norm_num) _, leafAtomHalt 7 (by norm_num) _⟩,
      ⟨leafAtomHalt 1 (by norm_num) _, leafAtomHalt 9 (by norm_num) _⟩⟩⟩⟩⟩

theorem leafAtoms_rootTreeB : MemoryLeafAtomsRealized 97 (rootTreeB seedZ alphaA) :=
  ⟨⟨leafAtomHalt 1 (by norm_num) _, leafAtomHalt 7 (by norm_num) _⟩,
   ⟨leafAtomHalt 1 (by norm_num) _, leafAtomHalt 9 (by norm_num) _⟩⟩

theorem nounRealization :
    ExactExecutionNounRealization 97 (cfg seedZ alphaA) (exec seedZ alphaA) where
  computeTree := computeTreeNounRealization
  memoryForest := memoryForestNounRealization
  memoryLeaves := by
    intro tree htree
    simp only [exec, List.mem_cons, List.not_mem_nil, or_false] at htree
    rcases htree with rfl | rfl
    · exact leafAtoms_rootTreeA
    · exact leafAtoms_rootTreeB

/-! ## D. The cumulative language bundle and assembled semantic data -/

theorem language
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    NounRealizedTraversableChainedSemanticExactLanguage 97 (cfg seedZ alphaA)
      (exec seedZ alphaA) where
  traversable := traversable hfirst
  nounRealization := nounRealization

def semanticData
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    SemanticTrace.ExactExecutionSemanticData 97 7 (cfg seedZ alphaA) (exec seedZ alphaA) where
  language := language hfirst
  rowAccepted := fun i => ExactExecution.computeRowAt_accepted computeRowsAccepted i
  rows := rowData

/-! ## E. Served memory trace (parametrized definition from Op9MemoryTraceK3) -/

def memoryTraceFinal
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    ExactServedMemoryTrace 97 7 (cfg seedZ alphaA) (exec seedZ alphaA) (semanticData hfirst)
      (execA seedZ alphaA) :=
  memoryTrace (semanticData hfirst) rfl

end

end Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.semanticPreimage
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.language
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.semanticData
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.memoryTraceFinal
