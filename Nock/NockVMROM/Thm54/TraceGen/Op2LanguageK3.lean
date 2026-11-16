/-
  Nock/NockVMROM/Thm54/TraceGen/Op2LanguageK3.lean

  Stage 3 of the OP2 Layer-2 CORE, over `K3`: the cumulative
  `NounRealizedTraversableChainedSemanticExactLanguage` bundle and the assembled
  `ExactExecutionSemanticData 97 7` for the fan-out-3 eval program

      `*[0 [2 [1 [0 1]] [1 [1 5]]]] = 5`

  Five committed records: parent formula@3 (`α¹`), parent formula-tail@2 (`α²`, the
  axis-2 NMR descent), and three
  child formula@3 records (`α³,α⁴,α⁵`).  Semantic axes live in `F = ZMod 97` and
  embed into `K3` by `algebraMap` (`bridge F K` / `memRecOfNMR F K`).  The compute
  request order is `(F,T,B,C,S)` and the memory `read_root` response order is
  `(F,T,C,B,S)` — a permutation of the same five unique records.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op2MemoryWebK3
import Nock.NockVMROM.Thm54.TraceGen.Op2SemanticDataK3
import Nock.NockVMROM.Thm54.Language
import Nock.NockVMROM.Thm54.NounRealization
import Nock.NockVMROM.Thm54.SemanticTrace
import Mathlib.Tactic.IntervalCases

namespace Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

open Nock Nock.Walk Nock.NockVM Nock.MemoryTable Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

/-! ## Canonical derived IO of the slice -/

/-- The four compute rows emit five records: parent `.s2` contributes `mr1,mr2`, each
`.s1` child contributes `mr1`. -/
theorem derived_requests :
    (exec seedZ alphaA).derivedRequestIO =
      [NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault,
      NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault,
        NockVM.encRecFormR (recB seedZ alphaA) MemoryTable.formRDefault,
        NockVM.encRecFormR (recC seedZ alphaA) MemoryTable.formRDefault,
        NockVM.encRecFormR (recS seedZ alphaA) MemoryTable.formRDefault] := by
  rw [ExactExecution.derivedRequestIO_eq_computeRows, computeRows_eq]
  simp [NockVM.activeRequestRecords, parentRow, child1Row, child2Row, child3Row,
    parentPub, child1Pub, child2Pub, child3Pub, op1PubOf]

/-- The five `read_root` rows serve the same five records in BFS order
`(F, T, C, B, S)`. -/
theorem derived_responses :
    (exec seedZ alphaA).derivedResponseIO =
      [NockVM.encRecFormR (recF seedZ alphaA) MemoryTable.formRDefault,
      NockVM.encRecFormR (recT seedZ alphaA) MemoryTable.formRDefault,
        NockVM.encRecFormR (recC seedZ alphaA) MemoryTable.formRDefault,
        NockVM.encRecFormR (recB seedZ alphaA) MemoryTable.formRDefault,
        NockVM.encRecFormR (recS seedZ alphaA) MemoryTable.formRDefault] := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, memoryRows_eq]
  simp [lblOf, MemoryTable.Pub.cprime, parentDec, parentPub, parentRow, pReadF, pDecF, pHalt2,
    pVerifyF, pReadT, pDecT, pVerifyT, pReadC, pReadB, pDecC, pDecB, pHaltC1, pVerifyC, pHaltB1,
    pVerifyB, pReadS, pDecSf1, pDecS, pHalt0, pHalt1s, pHaltS1, pVerifyS, pHalt5, readPub, decPub,
    haltPub, verifyPub]

/-! ## H. Semantic IO preimage

Each semantic record is `(axis : F, (rootFP, childFP), exp)` with the axis embedded by
`algebraMap F K`.  The axis-2 formula-tail record is `semT`. -/

def semOf (axis : F) (root child : Noun) (exp : ℕ) : (nmrMEF F K).Rec :=
  (axis,
    ((((fp seedZ root).size, (fp seedZ root).dyck, (fp seedZ root).leaf),
      ((fp seedZ child).size, (fp seedZ child).dyck, (fp seedZ child).leaf)),
    exp))

/-- Parent formula-open `[2 [b c]] @3`, timestamp `α¹`. -/
def semF : (nmrMEF F K).Rec := semOf 3 op2ParentFormula op2ParentTail 1
/-- Parent formula-tail `[b c] @2` (axis-2 descent), timestamp `α²`. -/
def semT : (nmrMEF F K).Rec := semOf 2 op2ParentTail op2ChildFormula1 2
/-- Child-one `[1 [0 1]] @3`, timestamp `α³`. -/
def semB : (nmrMEF F K).Rec := semOf 3 op2ChildFormula1 op2Sf1 3
/-- Child-two `[1 [1 5]] @3`, timestamp `α⁴`. -/
def semC : (nmrMEF F K).Rec := semOf 3 op2ChildFormula2 op2Sf2 4
/-- Child-three `[1 5] @3`, timestamp `α⁵`. -/
def semS : (nmrMEF F K).Rec := semOf 3 op2Sf2 op2Result 5

theorem semF_preimage :
    memRecOfNMR F K
        ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semF) =
      recF seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semF, semOf, cfg, recF, seedZ, alphaA, map_ofNat]

theorem semT_preimage :
    memRecOfNMR F K
        ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semT) =
      recT seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semT, semOf, cfg, recT, seedZ, alphaA, map_ofNat,
    pow_two]

theorem semB_preimage :
    memRecOfNMR F K
        ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semB) =
      recB seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semB, semOf, cfg, recB, seedZ, alphaA, map_ofNat,
    pow_succ]

theorem semC_preimage :
    memRecOfNMR F K
        ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semC) =
      recC seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semC, semOf, cfg, recC, seedZ, alphaA, map_ofNat,
    pow_succ]

theorem semS_preimage :
    memRecOfNMR F K
        ((nmrEncoding F K (cfg seedZ alphaA).challenges.α).encode semS) =
      recS seedZ alphaA := by
  ext <;> simp [memRecOfNMR, nmrEncoding, semS, semOf, cfg, recS, seedZ, alphaA, map_ofNat,
    pow_succ]

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
theorem semB_bridge :
    bridge F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semB =
      NockVM.encRecFormR (recB seedZ alphaA) MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees, semB_preimage]
  rfl
theorem semC_bridge :
    bridge F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semC =
      NockVM.encRecFormR (recC seedZ alphaA) MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees, semC_preimage]
  rfl
theorem semS_bridge :
    bridge F K (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semS =
      NockVM.encRecFormR (recS seedZ alphaA) MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees, semS_preimage]
  rfl

theorem semResp_nodup : [semF, semT, semC, semB, semS].Nodup := by
  simp [semF, semT, semC, semB, semS, semOf]

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

/-- The five-record semantic IO preimage.  Request order `(F,T,B,C,S)` matches compute
emission; response order `(F,T,C,B,S)` matches memory BFS `read_root`s. -/
def semanticPreimage :
    SemanticIOPreimage (cfg seedZ alphaA) (exec seedZ alphaA) where
  timestampBound := 6
  timestampBound_le_order := by
    change 6 ≤ orderOf alphaA
    rw [alphaA_order]; norm_num
  semanticRequests := [semF, semT, semB, semC, semS]
  semanticResponses := [semF, semT, semC, semB, semS]
  requestTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [semF, semT, semB, semC, semS, semOf]
  responseTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [semF, semT, semC, semB, semS, semOf]
  semantic_lmio := by
    refine ⟨by norm_num [IO.InRange, cfg], [semF, semT, semC, semB, semS], by simp,
      semResp_nodup, ?_, List.Perm.refl _⟩
    intro x
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    have key : ∀ p q r s t : Prop, (p ∨ q ∨ r ∨ s ∨ t) ↔ (p ∨ q ∨ s ∨ r ∨ t) := by
      intro p q r s t; tauto
    exact key _ _ _ _ _
  requestTimestamp_determines := by
    intro x hx y hy h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl <;>
      first | (simp [semF, semT, semB, semC, semS, semOf] at h; done) | rfl
  requests_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
      List.map_cons, List.map_nil, semF_bridge, semT_bridge, semB_bridge, semC_bridge,
      semS_bridge, derived_requests]
  responses_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
      List.map_cons, List.map_nil, semF_bridge, semT_bridge, semC_bridge, semB_bridge,
      semS_bridge, derived_responses]

theorem semanticExactLanguage :
    SemanticExactLanguage (cfg seedZ alphaA) (exec seedZ alphaA) :=
  ⟨computeRowsAccepted, memoryRowsAccepted, ⟨semanticPreimage⟩⟩

/-! ## Chained boundaries and traversable topology -/

/-- Form R leftover remaining on the first `read_root`. Dummy-wired. -/
theorem exec_lambda_package :
    ∀ i, ((exec seedZ alphaA).memoryPubAt i).lambda? = some MemoryTable.formRDefault := by
  intro i
  fin_cases i
  · rw [memoryPubAt_0]; simp only [pReadF, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_1]; simp only [pDecF, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_2]; simp only [pHalt2, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_3]; simp only [pVerifyF, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_4]; simp only [pReadT, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_5]; simp only [pDecT, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_6]; simp only [pVerifyT, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_7]; simp only [pReadC, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_8]; simp only [pReadB, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_9]; simp only [pDecC, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_10]; simp only [pDecB, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_11]; simp only [pHaltC1, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_12]; simp only [pVerifyC, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_13]; simp only [pHaltB1, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_14]; simp only [pVerifyB, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_15]; simp only [pReadS, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_16]; simp only [pDecSf1, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_17]; simp only [pDecS, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_18]; simp only [pHalt0, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_19]; simp only [pHalt1s, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_20]; simp only [pHaltS1, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_21]; simp only [pVerifyS, readPub, decPub, verifyPub, haltPub]
  · rw [memoryPubAt_22]; simp only [pHalt5, readPub, decPub, verifyPub, haltPub]

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
          (cfg seedZ alphaA).memRows_pos = ⟨22, by norm_num [cfg]⟩ := rfl
    rw [hlast, memoryPubAt_22]; rfl

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

/-! ## J. Bounded noun realization -/

theorem fpRealized {n : Noun} (hb : FieldEmbedding.BoundedBy 97 n) :
    FPRealized seedZ 97 (fp seedZ n) :=
  ⟨n, hb, rfl⟩

theorem fpActive {n : Noun} (hb : FieldEmbedding.BoundedBy 97 n) :
    FPSlotRealized seedZ 97 .active (fp seedZ n) :=
  ⟨fpRealized hb, FPRealized.ne_zero seedZ_ne_zero (fpRealized hb)⟩

theorem alphaA_ne_zero : alphaA ≠ 0 := by rw [alphaA]; decide

theorem recF_ne_zero : recF seedZ alphaA ≠ MemRec.zero := fun h =>
  alphaA_ne_zero (by
    simpa [recF, MemRec.zero] using congrArg MemRec.ts h)
theorem recT_ne_zero : recT seedZ alphaA ≠ MemRec.zero := fun h =>
  (pow_ne_zero 2 alphaA_ne_zero) (by
    simpa [recT, MemRec.zero] using congrArg MemRec.ts h)
theorem recB_ne_zero : recB seedZ alphaA ≠ MemRec.zero := fun h =>
  (pow_ne_zero 3 alphaA_ne_zero) (by
    simpa [recB, MemRec.zero] using congrArg MemRec.ts h)
theorem recC_ne_zero : recC seedZ alphaA ≠ MemRec.zero := fun h =>
  (pow_ne_zero 4 alphaA_ne_zero) (by
    simpa [recC, MemRec.zero] using congrArg MemRec.ts h)
theorem recS_ne_zero : recS seedZ alphaA ≠ MemRec.zero := fun h =>
  (pow_ne_zero 5 alphaA_ne_zero) (by
    simpa [recS, MemRec.zero] using congrArg MemRec.ts h)

theorem recF_active : MemRecSlotRealized seedZ 97 .active (recF seedZ alphaA) :=
  ⟨recF_ne_zero, fpActive bounded_formula, fpActive bounded_tail⟩
theorem recT_active : MemRecSlotRealized seedZ 97 .active (recT seedZ alphaA) :=
  ⟨recT_ne_zero, fpActive bounded_tail, fpActive bounded_child1⟩
theorem recB_active : MemRecSlotRealized seedZ 97 .active (recB seedZ alphaA) :=
  ⟨recB_ne_zero, fpActive bounded_child1, fpActive bounded_sf1⟩
theorem recC_active : MemRecSlotRealized seedZ 97 .active (recC seedZ alphaA) :=
  ⟨recC_ne_zero, fpActive bounded_child2, fpActive bounded_sf2⟩
theorem recS_active : MemRecSlotRealized seedZ 97 .active (recS seedZ alphaA) :=
  ⟨recS_ne_zero, fpActive bounded_sf2, fpActive bounded_result⟩

/-! ### Per-row public compute realizations -/

theorem parentRow_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel (parentRow seedZ alphaA)) where
  subject := fpActive bounded_subject
  formula := fpActive bounded_formula
  evaluation := fpActive bounded_result
  subformula := by
    intro i; fin_cases i
    · exact ⟨fpActive bounded_subject, fpActive bounded_child1, fpActive bounded_sf1⟩
    · exact ⟨fpActive bounded_subject, fpActive bounded_child2, fpActive bounded_sf2⟩
    · exact ⟨fpActive bounded_sf1, fpActive bounded_sf2, fpActive bounded_result⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recF_active
    · exact recT_active
    · rfl

theorem child1Row_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel (child1Row seedZ alphaA)) where
  subject := fpActive bounded_subject
  formula := fpActive bounded_child1
  evaluation := fpActive bounded_sf1
  subformula := by intro i; fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recB_active
    · rfl
    · rfl

theorem child2Row_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel (child2Row seedZ alphaA)) where
  subject := fpActive bounded_subject
  formula := fpActive bounded_child2
  evaluation := fpActive bounded_sf2
  subformula := by intro i; fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recC_active
    · rfl
    · rfl

theorem child3Row_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel (child3Row seedZ alphaA)) where
  subject := fpActive bounded_sf1
  formula := fpActive bounded_sf2
  evaluation := fpActive bounded_result
  subformula := by intro i; fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recS_active
    · rfl
    · rfl

theorem computeTreeNounRealization :
    ComputePublicTreeNounRealization 97 (exec seedZ alphaA).computePublicTree := by
  have h : (bfsForest [(exec seedZ alphaA).computePublicTree]).map NTree.label =
      [computePublicLabel (parentRow seedZ alphaA),
        computePublicLabel (child1Row seedZ alphaA),
        computePublicLabel (child2Row seedZ alphaA),
        computePublicLabel (child3Row seedZ alphaA)] := by
    rw [ExactExecution.computePublicTree_bfs, ExactExecution.computePublicRows,
      computeRows_eq]
    rfl
  unfold ComputePublicTreeNounRealization ComputePublicRowsNounRealization
  rw [h]
  refine List.forall_iff_forall_mem.mpr ?_
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl
  · exact parentRow_nounRealization
  · exact child1Row_nounRealization
  · exact child2Row_nounRealization
  · exact child3Row_nounRealization

/-! ### Per-row public memory realizations -/

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

theorem pReadF_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pReadF seedZ alphaA)) :=
  memSingleChildRealization _ rfl (fpActive bounded_formula) (fpActive bounded_formula)
    rfl rfl (recF_active.formRRow _)
theorem pReadT_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pReadT seedZ alphaA)) :=
  memSingleChildRealization _ rfl (fpActive bounded_tail) (fpActive bounded_tail)
    rfl rfl (recT_active.formRRow _)
theorem pReadC_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pReadC seedZ alphaA)) :=
  memSingleChildRealization _ rfl (fpActive bounded_child2) (fpActive bounded_child2)
    rfl rfl (recC_active.formRRow _)
theorem pReadB_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pReadB seedZ alphaA)) :=
  memSingleChildRealization _ rfl (fpActive bounded_child1) (fpActive bounded_child1)
    rfl rfl (recB_active.formRRow _)
theorem pReadS_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pReadS seedZ alphaA)) :=
  memSingleChildRealization _ rfl (fpActive bounded_sf2) (fpActive bounded_sf2)
    rfl rfl (recS_active.formRRow _)
theorem pVerifyF_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pVerifyF seedZ alphaA)) :=
  memSingleChildRealization _ rfl (fpActive bounded_tail) (fpActive bounded_tail)
    rfl rfl (recF_active.formRRow _)
theorem pVerifyT_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pVerifyT seedZ alphaA)) :=
  memSingleChildRealization _ rfl (fpActive bounded_child1) (fpActive bounded_child1)
    rfl rfl (recT_active.formRRow _)
theorem pVerifyC_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pVerifyC seedZ alphaA)) :=
  memSingleChildRealization _ rfl (fpActive bounded_sf2) (fpActive bounded_sf2)
    rfl rfl (recC_active.formRRow _)
theorem pVerifyB_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pVerifyB seedZ alphaA)) :=
  memSingleChildRealization _ rfl (fpActive bounded_sf1) (fpActive bounded_sf1)
    rfl rfl (recB_active.formRRow _)
theorem pVerifyS_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pVerifyS seedZ alphaA)) :=
  memSingleChildRealization _ rfl (fpActive bounded_result) (fpActive bounded_result)
    rfl rfl (recS_active.formRRow _)
theorem pDecF_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pDecF seedZ alphaA)) :=
  memDecomposeRealization _ (fpActive bounded_formula) (fpActive bounded_op2Head)
    (fpActive bounded_tail) rfl
theorem pDecT_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pDecT seedZ alphaA)) :=
  memDecomposeRealization _ (fpActive bounded_tail) (fpActive bounded_child1)
    (fpActive bounded_child2) rfl
theorem pDecC_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pDecC seedZ alphaA)) :=
  memDecomposeRealization _ (fpActive bounded_child2) (fpActive bounded_op1Head)
    (fpActive bounded_sf2) rfl
theorem pDecB_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pDecB seedZ alphaA)) :=
  memDecomposeRealization _ (fpActive bounded_child1) (fpActive bounded_op1Head)
    (fpActive bounded_sf1) rfl
theorem pDecS_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pDecS seedZ alphaA)) :=
  memDecomposeRealization _ (fpActive bounded_sf2) (fpActive bounded_op1Head)
    (fpActive bounded_result) rfl
theorem pDecSf1_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pDecSf1 seedZ alphaA)) :=
  memDecomposeRealization _ (fpActive bounded_sf1) (fpActive (bounded_atom 0 (by norm_num)))
    (fpActive (bounded_atom 1 (by norm_num))) rfl
theorem pHalt2_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pHalt2 seedZ alphaA)) :=
  memHaltRealization _ (fpActive bounded_op2Head) rfl rfl rfl
theorem pHaltC1_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pHaltC1 seedZ alphaA)) :=
  memHaltRealization _ (fpActive bounded_op1Head) rfl rfl rfl
theorem pHaltB1_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pHaltB1 seedZ alphaA)) :=
  memHaltRealization _ (fpActive bounded_op1Head) rfl rfl rfl
theorem pHalt0_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pHalt0 seedZ alphaA)) :=
  memHaltRealization _ (fpActive (bounded_atom 0 (by norm_num))) rfl rfl rfl
theorem pHalt1s_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pHalt1s seedZ alphaA)) :=
  memHaltRealization _ (fpActive (bounded_atom 1 (by norm_num))) rfl rfl rfl
theorem pHaltS1_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pHaltS1 seedZ alphaA)) :=
  memHaltRealization _ (fpActive bounded_op1Head) rfl rfl rfl
theorem pHalt5_realization :
    MemoryPublicRowNounRealization 97 (lblOf seedZ (pHalt5 seedZ)) :=
  memHaltRealization _ (fpActive bounded_result) rfl rfl rfl

theorem memoryForestNounRealization :
    MemoryPublicForestNounRealization 97 (exec seedZ alphaA).memoryForest := by
  unfold MemoryPublicForestNounRealization MemoryPublicRowsNounRealization
  rw [show (bfsForest (exec seedZ alphaA).memoryForest).map NTree.label =
      (exec seedZ alphaA).memoryRows from rfl, memoryRows_eq]
  refine List.forall_iff_forall_mem.mpr ?_
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pReadF_realization
  · exact pDecF_realization
  · exact pHalt2_realization
  · exact pVerifyF_realization
  · exact pReadT_realization
  · exact pDecT_realization
  · exact pVerifyT_realization
  · exact pReadC_realization
  · exact pReadB_realization
  · exact pDecC_realization
  · exact pDecB_realization
  · exact pHaltC1_realization
  · exact pVerifyC_realization
  · exact pHaltB1_realization
  · exact pVerifyB_realization
  · exact pReadS_realization
  · exact pDecSf1_realization
  · exact pDecS_realization
  · exact pHalt0_realization
  · exact pHalt1s_realization
  · exact pHaltS1_realization
  · exact pVerifyS_realization
  · exact pHalt5_realization

/-! ### Leaf-atom existence on the reconstruction forest -/

theorem leafAtomHalt (k : ℕ) (hk : k < 97) (acc : K) :
    MemoryLeafAtomsRealized 97 (mLeaf seedZ (haltPub seedZ k acc)) :=
  ⟨k, hk, by
    show ((k : ℕ) : K) = (fp seedZ (Noun.atom k)).leaf
    simp [fp, GlobalCarryRecognizer.enc_atom]⟩

theorem leafAtoms_tHalt5 : MemoryLeafAtomsRealized 97 (tHalt5 seedZ) :=
  leafAtomHalt 5 (by norm_num) 0
theorem leafAtoms_tHaltS1 : MemoryLeafAtomsRealized 97 (tHaltS1 seedZ alphaA) :=
  leafAtomHalt 1 (by norm_num) (qS seedZ alphaA)
theorem leafAtoms_tHalt0 : MemoryLeafAtomsRealized 97 (tHalt0 seedZ alphaA) :=
  leafAtomHalt 0 (by norm_num) (qS seedZ alphaA)
theorem leafAtoms_tHalt1s : MemoryLeafAtomsRealized 97 (tHalt1s seedZ alphaA) :=
  leafAtomHalt 1 (by norm_num) (qS seedZ alphaA)
theorem leafAtoms_tHaltB1 : MemoryLeafAtomsRealized 97 (tHaltB1 seedZ alphaA) :=
  leafAtomHalt 1 (by norm_num) (qB seedZ alphaA)
theorem leafAtoms_tHaltC1 : MemoryLeafAtomsRealized 97 (tHaltC1 seedZ alphaA) :=
  leafAtomHalt 1 (by norm_num) (qC seedZ alphaA + qB seedZ alphaA)
theorem leafAtoms_tHalt2 : MemoryLeafAtomsRealized 97 (tHalt2 seedZ alphaA) :=
  leafAtomHalt 2 (by norm_num) (qF seedZ alphaA)

theorem leafAtoms_tVerifyS : MemoryLeafAtomsRealized 97 (tVerifyS seedZ alphaA) :=
  leafAtoms_tHalt5
theorem leafAtoms_tDecS : MemoryLeafAtomsRealized 97 (tDecS seedZ alphaA) :=
  ⟨leafAtoms_tHaltS1, leafAtoms_tVerifyS⟩
theorem leafAtoms_tReadS : MemoryLeafAtomsRealized 97 (tReadS seedZ alphaA) :=
  leafAtoms_tDecS
theorem leafAtoms_tDecSf1 : MemoryLeafAtomsRealized 97 (tDecSf1 seedZ alphaA) :=
  ⟨leafAtoms_tHalt0, leafAtoms_tHalt1s⟩
theorem leafAtoms_tVerifyB : MemoryLeafAtomsRealized 97 (tVerifyB seedZ alphaA) :=
  leafAtoms_tDecSf1
theorem leafAtoms_tDecB : MemoryLeafAtomsRealized 97 (tDecB seedZ alphaA) :=
  ⟨leafAtoms_tHaltB1, leafAtoms_tVerifyB⟩
theorem leafAtoms_tReadB : MemoryLeafAtomsRealized 97 (tReadB seedZ alphaA) :=
  leafAtoms_tDecB
theorem leafAtoms_tVerifyC : MemoryLeafAtomsRealized 97 (tVerifyC seedZ alphaA) :=
  leafAtoms_tReadS
theorem leafAtoms_tDecC : MemoryLeafAtomsRealized 97 (tDecC seedZ alphaA) :=
  ⟨leafAtoms_tHaltC1, leafAtoms_tVerifyC⟩
theorem leafAtoms_tReadC : MemoryLeafAtomsRealized 97 (tReadC seedZ alphaA) :=
  leafAtoms_tDecC
theorem leafAtoms_tVerifyT : MemoryLeafAtomsRealized 97 (tVerifyT seedZ alphaA) :=
  leafAtoms_tReadB
theorem leafAtoms_tDecT : MemoryLeafAtomsRealized 97 (tDecT seedZ alphaA) :=
  ⟨leafAtoms_tVerifyT, leafAtoms_tReadC⟩
theorem leafAtoms_tReadT : MemoryLeafAtomsRealized 97 (tReadT seedZ alphaA) :=
  leafAtoms_tDecT
theorem leafAtoms_tVerifyF : MemoryLeafAtomsRealized 97 (tVerifyF seedZ alphaA) :=
  leafAtoms_tReadT
theorem leafAtoms_tDecF : MemoryLeafAtomsRealized 97 (tDecF seedZ alphaA) :=
  ⟨leafAtoms_tHalt2, leafAtoms_tVerifyF⟩
theorem leafAtoms_rootTree : MemoryLeafAtomsRealized 97 (rootTree seedZ alphaA) :=
  leafAtoms_tDecF

theorem nounRealization :
    ExactExecutionNounRealization 97 (cfg seedZ alphaA) (exec seedZ alphaA) where
  computeTree := computeTreeNounRealization
  memoryForest := memoryForestNounRealization
  memoryLeaves := by
    intro tree htree
    simp only [exec, List.mem_cons, List.not_mem_nil, or_false] at htree
    subst htree
    exact leafAtoms_rootTree

/-! ## The cumulative language bundle and assembled semantic data -/

theorem language
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    NounRealizedTraversableChainedSemanticExactLanguage 97 (cfg seedZ alphaA)
      (exec seedZ alphaA) where
  traversable := traversable hfirst
  nounRealization := nounRealization

/-- The exact per-row semantic data of the OP2/K3 slice. -/
def semanticData
    (hfirst :
      ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
        ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0) :
    SemanticTrace.ExactExecutionSemanticData 97 7 (cfg seedZ alphaA) (exec seedZ alphaA) where
  language := language hfirst
  rowAccepted := fun i => ExactExecution.computeRowAt_accepted computeRowsAccepted i
  rows := rowData

end

end Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.semanticPreimage
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.language
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.semanticData
