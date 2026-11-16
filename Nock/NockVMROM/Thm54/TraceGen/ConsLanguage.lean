/-
  Nock/NockVMROM/Thm54/TraceGen/ConsLanguage.lean

  The cumulative
  `NounRealizedTraversableChainedSemanticExactLanguage` bundle and the assembled
  `SemanticTrace.ExactExecutionSemanticData 97 4` for the BRANCHING slice
  `*[0 [[1 5] [1 6]]] = [5 6]` over `K = ZMod 97`, seed `z = 8`, `α = 4`.

  This sits above the acceptance webs (`ConsRowWeb`, `ConsMemoryWeb`) and the row-level bundle
  (`ConsSemanticData`), mirroring `Op1Language`/`DistinctCensusExecution` at the three-request,
  thirteen-memory-row branching size:

  * `derived_requests`/`derived_responses`   the three committed records `recCons/recL/recR`;
  * `semCons`/`semL`/`semR`, their bridges, and `semanticPreimage`  (the multiplicity-preserving
    `nmrMEF` preimage of the derived IO, three distinct timestamps `α, α², α³`);
  * `computePubAt`/`memoryPubAt` BFS-indexing lemmas + `compute_wf`/`memory_wf`/`compute_chain`/
    `memory_chain`  (`chained`);
  * `traversable`  (reusing the web-side `compute_topology`/`memory_topology`);
  * `nounRealization`  (bounded noun realization of every public row and every leaf atom);
  * `language`  and the assembled `semanticData`.

  Faithfulness of the semantic records is diagonal: `F = K = ZMod 97`, so the axis embeds by the
  identity and every bridge is `d2_record_bridge_agrees` on a self-preimage.
-/
import Nock.NockVMROM.Thm54.TraceGen.ConsRowWeb
import Nock.NockVMROM.Thm54.TraceGen.ConsMemoryWeb
import Nock.NockVMROM.Thm54.Language
import Nock.NockVMROM.Thm54.NounRealization

namespace Nock.NockVMROM.Thm54.TraceGen.ConsConfig

open Nock Nock.Walk Nock.NockVM Nock.MemoryTable Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton

noncomputable section

/-! ## Canonical derived IO of the slice -/

/-- The three compute rows emit the three committed records in BFS order. -/
theorem derived_requests :
    exec.derivedRequestIO = [encRecFormR recCons formRDefault, encRecFormR recL formRDefault,
      encRecFormR recR formRDefault] := by
  rw [ExactExecution.derivedRequestIO_eq_computeRows, computeRows_eq]
  simp [NockVM.activeRequestRecords, consRow, op1LRow, op1RRow, consPub, op1LPub, op1RPub,
    op1PubOf]

/-- The three `read_root` rows serve the same three records in BFS order. -/
theorem derived_responses :
    exec.derivedResponseIO = [encRecFormR recCons formRDefault, encRecFormR recL formRDefault,
      encRecFormR recR formRDefault] := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, memoryRows_eq]
  simp [lblOf, pDummyHalt, pReadF, pDecF, pReadL, pReadR, pDecL,
    pVerifyF, pHaltL1, pVerifyL, pDecR, pHaltL5, pHaltR1, pVerifyR, pHaltR6,
    readPub, decPub, haltPub, verifyPub, MemoryTable.Pub.cprime]

/-! ## H. Semantic IO preimage

Each semantic record `(axis 3, (rootFP, childFP), exp)` realizes its committed record over the
identity axis embedding (`F = K`).  The three exponents are the distinct `1, 2, 3`. -/

/-- The `.cons` root's semantic record `([[1 5] [1 6]], [1 6], axis 3, ts α^1)`. -/
def semCons : (nmrMEF F F).Rec :=
  (3,
    (((enc formulaNoun).size, (enc formulaNoun).dyck, (enc formulaNoun).leaf),
     ((enc rightFormula).size, (enc rightFormula).dyck, (enc rightFormula).leaf)),
    1)

/-- The left `OP_1` child's semantic record `([1 5], 5, axis 3, ts α^2)`. -/
def semL : (nmrMEF F F).Rec :=
  (3,
    (((enc leftFormula).size, (enc leftFormula).dyck, (enc leftFormula).leaf),
     ((enc leftResult).size, (enc leftResult).dyck, (enc leftResult).leaf)),
    2)

/-- The right `OP_1` child's semantic record `([1 6], 6, axis 3, ts α^3)`. -/
def semR : (nmrMEF F F).Rec :=
  (3,
    (((enc rightFormula).size, (enc rightFormula).dyck, (enc rightFormula).leaf),
     ((enc rightResult).size, (enc rightResult).dyck, (enc rightResult).leaf)),
    3)

theorem semCons_bridge :
    bridge F F cfg.challenges.α cfg.challenges.lam semCons = encRecFormR recCons formRDefault := by
  rw [← d2_record_bridge_agrees]
  rw [show memRecOfNMR F F
      ((nmrEncoding F F cfg.challenges.α).encode semCons) = recCons by
    ext <;> simp [memRecOfNMR, nmrEncoding, semCons, cfg, recCons, seedZ, alphaA, enc]]
  rfl

theorem semL_bridge :
    bridge F F cfg.challenges.α cfg.challenges.lam semL = encRecFormR recL formRDefault := by
  rw [← d2_record_bridge_agrees]
  rw [show memRecOfNMR F F
      ((nmrEncoding F F cfg.challenges.α).encode semL) = recL by
    ext <;> simp [memRecOfNMR, nmrEncoding, semL, cfg, recL, seedZ, alphaA, enc, pow_two]]
  rfl

theorem semR_bridge :
    bridge F F cfg.challenges.α cfg.challenges.lam semR = encRecFormR recR formRDefault := by
  rw [← d2_record_bridge_agrees]
  rw [show memRecOfNMR F F
      ((nmrEncoding F F cfg.challenges.α).encode semR) = recR by
    ext <;> simp [memRecOfNMR, nmrEncoding, semR, cfg, recR, seedZ, alphaA, enc, pow_succ]]
  rfl

theorem semRecs_nodup : [semCons, semL, semR].Nodup := by
  have h12 : semCons ≠ semL := by
    intro h
    have := congrArg (fun r : (nmrMEF F F).Rec => r.2.2) h
    norm_num [semCons, semL] at this
  have h13 : semCons ≠ semR := by
    intro h
    have := congrArg (fun r : (nmrMEF F F).Rec => r.2.2) h
    norm_num [semCons, semR] at this
  have h23 : semL ≠ semR := by
    intro h
    have := congrArg (fun r : (nmrMEF F F).Rec => r.2.2) h
    norm_num [semL, semR] at this
  simp [h12, h13, h23]

/-- `α = 4` has multiplicative order `24` in `ZMod 97`, bounding the semantic timestamp window. -/
theorem alphaA_order : orderOf (alphaA : F) = 24 := by
  rw [show (alphaA : F) = (4 : F) from rfl, orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

/-- The semantic IO preimage: three requests, three responses, bridging to the derived IO. -/
def semanticPreimage : SemanticIOPreimage cfg exec where
  timestampBound := 4
  timestampBound_le_order := by
    change (4 : ℕ) ≤ orderOf (alphaA : F)
    rw [alphaA_order]; norm_num
  semanticRequests := [semCons, semL, semR]
  semanticResponses := [semCons, semL, semR]
  requestTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> norm_num [semCons, semL, semR]
  responseTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> norm_num [semCons, semL, semR]
  semantic_lmio := by
    refine ⟨by norm_num [IO.InRange, cfg], [semCons, semL, semR],
      le_refl _, semRecs_nodup, fun x => Iff.rfl, List.Perm.refl _⟩
  requestTimestamp_determines := by
    intro x hx y hy h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | rfl | (norm_num [semCons, semL, semR] at h)
  requests_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_singleton,
      semCons_bridge, semL_bridge, semR_bridge, derived_requests]
  responses_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_singleton,
      semCons_bridge, semL_bridge, semR_bridge, derived_responses]

theorem semantic_exact
    (hReadF : Vmem memInputs pReadF) (hDecF : Vmem memInputs pDecF)
    (hReadL : Vmem memInputs pReadL) (hReadR : Vmem memInputs pReadR)
    (hDecL : Vmem memInputs pDecL) (hVerifyF : Vmem memInputs pVerifyF)
    (hVerifyL : Vmem memInputs pVerifyL) (hDecR : Vmem memInputs pDecR)
    (hVerifyR : Vmem memInputs pVerifyR) :
    SemanticExactLanguage cfg exec :=
  ⟨computeRowsAccepted,
    memoryRowsAccepted hReadF hDecF hReadL hReadR hDecL hVerifyF hVerifyL hDecR hVerifyR,
    ⟨semanticPreimage⟩⟩

/-! ## Compute indexing, genericity, and line-accumulator chaining -/

theorem computePubAt_zero : exec.computePubAt ⟨0, by norm_num [cfg]⟩ = consPub := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt, computeRows_eq, cfg, consRow]
theorem computePubAt_one : exec.computePubAt ⟨1, by norm_num [cfg]⟩ = op1LPub := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt, computeRows_eq, cfg, op1LRow]
theorem computePubAt_two : exec.computePubAt ⟨2, by norm_num [cfg]⟩ = op1RPub := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt, computeRows_eq, cfg, op1RRow]

theorem compute_wf_all :
    ∀ i, ComputeTable.WF cfg.challenges.computeInputs (exec.computePubAt i) := by
  intro i
  fin_cases i
  · rw [computePubAt_zero]; exact cons_wf
  · rw [computePubAt_one]; exact op1L_wf
  · rw [computePubAt_two]; exact op1R_wf

theorem compute_chain :
    ∀ i : Fin cfg.compRows, ∀ _ : (i : ℕ) + 1 < cfg.compRows,
      (exec.computePubAt i).ln =
        (exec.computePubAt ⟨(i : ℕ) + 1, by omega⟩).ln_prev := by
  intro i hi
  fin_cases i
  · rw [computePubAt_zero, computePubAt_one]
    simp [consPub, op1LPub, op1PubOf]
  · rw [computePubAt_one, computePubAt_two]
    simp [op1LPub, op1RPub, op1PubOf, pow_two]
  · simp [cfg] at hi

/-! ## Memory indexing, genericity, and LogUp chaining -/

theorem memoryPubAt_0 : exec.memoryPubAt ⟨0, by norm_num [cfg]⟩ = pDummyHalt := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_1 : exec.memoryPubAt ⟨1, by norm_num [cfg]⟩ = pReadF := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_2 : exec.memoryPubAt ⟨2, by norm_num [cfg]⟩ = pDecF := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_3 : exec.memoryPubAt ⟨3, by norm_num [cfg]⟩ = pReadL := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_4 : exec.memoryPubAt ⟨4, by norm_num [cfg]⟩ = pReadR := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_5 : exec.memoryPubAt ⟨5, by norm_num [cfg]⟩ = pDecL := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_6 : exec.memoryPubAt ⟨6, by norm_num [cfg]⟩ = pVerifyF := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_7 : exec.memoryPubAt ⟨7, by norm_num [cfg]⟩ = pHaltL1 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_8 : exec.memoryPubAt ⟨8, by norm_num [cfg]⟩ = pVerifyL := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_9 : exec.memoryPubAt ⟨9, by norm_num [cfg]⟩ = pDecR := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_10 : exec.memoryPubAt ⟨10, by norm_num [cfg]⟩ = pHaltL5 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_11 : exec.memoryPubAt ⟨11, by norm_num [cfg]⟩ = pHaltR1 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_12 : exec.memoryPubAt ⟨12, by norm_num [cfg]⟩ = pVerifyR := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_13 : exec.memoryPubAt ⟨13, by norm_num [cfg]⟩ = pHaltR6 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]

theorem memory_wf_all :
    ∀ i, MemoryTable.WF cfg.challenges.memoryInputs (exec.memoryPubAt i) := by
  intro i
  fin_cases i
  · rw [memoryPubAt_0]; exact ⟨fun h => by simp [pDummyHalt, haltPub] at h⟩
  · rw [memoryPubAt_1]; exact pReadF_wf
  · rw [memoryPubAt_2]; exact ⟨fun h => by simp [pDecF, decPub] at h⟩
  · rw [memoryPubAt_3]; exact pReadL_wf
  · rw [memoryPubAt_4]; exact pReadR_wf
  · rw [memoryPubAt_5]; exact ⟨fun h => by simp [pDecL, decPub] at h⟩
  · rw [memoryPubAt_6]; exact pVerifyF_wf
  · rw [memoryPubAt_7]; exact ⟨fun h => by simp [pHaltL1, haltPub] at h⟩
  · rw [memoryPubAt_8]; exact pVerifyL_wf
  · rw [memoryPubAt_9]; exact ⟨fun h => by simp [pDecR, decPub] at h⟩
  · rw [memoryPubAt_10]; exact ⟨fun h => by simp [pHaltL5, haltPub] at h⟩
  · rw [memoryPubAt_11]; exact ⟨fun h => by simp [pHaltR1, haltPub] at h⟩
  · rw [memoryPubAt_12]; exact pVerifyR_wf
  · rw [memoryPubAt_13]; exact ⟨fun h => by simp [pHaltR6, haltPub] at h⟩

theorem memory_chain :
    ∀ i : Fin cfg.memRows, ∀ _ : (i : ℕ) + 1 < cfg.memRows,
      (exec.memoryPubAt i).icur =
        (exec.memoryPubAt ⟨(i : ℕ) + 1, by omega⟩).ipre := by
  intro i hi
  fin_cases i
  · rw [memoryPubAt_0, memoryPubAt_1]; rfl
  · rw [memoryPubAt_1, memoryPubAt_2]; rfl
  · rw [memoryPubAt_2, memoryPubAt_3]; rfl
  · rw [memoryPubAt_3, memoryPubAt_4]; rfl
  · rw [memoryPubAt_4, memoryPubAt_5]; rfl
  · rw [memoryPubAt_5, memoryPubAt_6]; rfl
  · rw [memoryPubAt_6, memoryPubAt_7]; rfl
  · rw [memoryPubAt_7, memoryPubAt_8]; rfl
  · rw [memoryPubAt_8, memoryPubAt_9]; rfl
  · rw [memoryPubAt_9, memoryPubAt_10]; rfl
  · rw [memoryPubAt_10, memoryPubAt_11]; rfl
  · rw [memoryPubAt_11, memoryPubAt_12]; rfl
  · rw [memoryPubAt_12, memoryPubAt_13]; rfl
  · simp [cfg] at hi

theorem chained
    (hReadF : Vmem memInputs pReadF) (hDecF : Vmem memInputs pDecF)
    (hReadL : Vmem memInputs pReadL) (hReadR : Vmem memInputs pReadR)
    (hDecL : Vmem memInputs pDecL) (hVerifyF : Vmem memInputs pVerifyF)
    (hVerifyL : Vmem memInputs pVerifyL) (hDecR : Vmem memInputs pDecR)
    (hVerifyR : Vmem memInputs pVerifyR) :
    ChainedSemanticExactLanguage cfg exec where
  semantic := semantic_exact hReadF hDecF hReadL hReadR hDecL hVerifyF hVerifyL hDecR hVerifyR
  z_ne_zero := seedZ_ne_zero
  compute_wf := compute_wf_all
  memory_wf := memory_wf_all
  compute_chain := compute_chain
  memory_chain := memory_chain
  memory_first_counts := by rw [memoryPubAt_0]; rfl
  memory_first_indicator := by rw [memoryPubAt_0]; rfl
  memory_first_ipre := by rw [memoryPubAt_0]; rfl
  memory_last_icur := by
    have hlast :
        cfg.orbit.lastIndex cfg.memRows cfg.memRows_pos = ⟨13, by norm_num [cfg]⟩ := rfl
    rw [hlast, memoryPubAt_13]; rfl

  memory_same_lambda := ExactExecution.memory_same_lambda_of_const _ (some formRDefault) (by
    intro i
    fin_cases i
    · rw [memoryPubAt_0]; rfl
    · rw [memoryPubAt_1]; rfl
    · rw [memoryPubAt_2]; rfl
    · rw [memoryPubAt_3]; rfl
    · rw [memoryPubAt_4]; rfl
    · rw [memoryPubAt_5]; rfl
    · rw [memoryPubAt_6]; rfl
    · rw [memoryPubAt_7]; rfl
    · rw [memoryPubAt_8]; rfl
    · rw [memoryPubAt_9]; rfl
    · rw [memoryPubAt_10]; rfl
    · rw [memoryPubAt_11]; rfl
    · rw [memoryPubAt_12]; rfl
    · rw [memoryPubAt_13]; rfl)

theorem traversable
    (hReadF : Vmem memInputs pReadF) (hDecF : Vmem memInputs pDecF)
    (hReadL : Vmem memInputs pReadL) (hReadR : Vmem memInputs pReadR)
    (hDecL : Vmem memInputs pDecL) (hVerifyF : Vmem memInputs pVerifyF)
    (hVerifyL : Vmem memInputs pVerifyL) (hDecR : Vmem memInputs pDecR)
    (hVerifyR : Vmem memInputs pVerifyR) :
    TraversableChainedSemanticExactLanguage cfg exec where
  chained := chained hReadF hDecF hReadL hReadR hDecL hVerifyF hVerifyL hDecR hVerifyR
  compute_topology := compute_topology
  memory_topology :=
    memory_topology hReadF hDecF hReadL hReadR hDecL hVerifyF hVerifyL hDecR hVerifyR

/-! ## J. Bounded noun realization -/

theorem fpRealized {n : Noun} (hb : FieldEmbedding.BoundedBy 97 n) :
    FPRealized seedZ 97 (enc n) :=
  ⟨n, hb, rfl⟩

theorem fpActive {n : Noun} (hb : FieldEmbedding.BoundedBy 97 n) :
    FPSlotRealized seedZ 97 .active (enc n) :=
  ⟨fpRealized hb, FPRealized.ne_zero seedZ_ne_zero (fpRealized hb)⟩

theorem alphaA_ne_zero : (alphaA : F) ≠ 0 := by decide

theorem recCons_ne_zero : recCons ≠ ComputeTable.MemRec.zero := fun h =>
  alphaA_ne_zero (by
    simpa [recCons, ComputeTable.MemRec.zero] using congrArg ComputeTable.MemRec.ts h)
theorem recL_ne_zero : recL ≠ ComputeTable.MemRec.zero := fun h =>
  (pow_ne_zero 2 alphaA_ne_zero) (by
    simpa [recL, ComputeTable.MemRec.zero] using congrArg ComputeTable.MemRec.ts h)
theorem recR_ne_zero : recR ≠ ComputeTable.MemRec.zero := fun h =>
  (pow_ne_zero 3 alphaA_ne_zero) (by
    simpa [recR, ComputeTable.MemRec.zero] using congrArg ComputeTable.MemRec.ts h)

theorem recCons_active : MemRecSlotRealized seedZ 97 .active recCons :=
  ⟨recCons_ne_zero, fpActive bounded_formulaNoun, fpActive bounded_rightFormula⟩
theorem recL_active : MemRecSlotRealized seedZ 97 .active recL :=
  ⟨recL_ne_zero, fpActive bounded_leftFormula, fpActive bounded_leftResult⟩
theorem recR_active : MemRecSlotRealized seedZ 97 .active recR :=
  ⟨recR_ne_zero, fpActive bounded_rightFormula, fpActive bounded_rightResult⟩

/-! ### Per-row public compute realizations -/

theorem consRow_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel consRow) where
  subject := fpActive bounded_subjectNoun
  formula := fpActive bounded_formulaNoun
  evaluation := fpActive bounded_resultNoun
  subformula := by
    intro i; fin_cases i
    · exact ⟨fpActive bounded_subjectNoun, fpActive bounded_leftFormula,
        fpActive bounded_leftResult⟩
    · exact ⟨fpActive bounded_subjectNoun, fpActive bounded_rightFormula,
        fpActive bounded_rightResult⟩
    · exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recCons_active
    · exact rfl
    · exact rfl

theorem op1LRow_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel op1LRow) where
  subject := fpActive bounded_subjectNoun
  formula := fpActive bounded_leftFormula
  evaluation := fpActive bounded_leftResult
  subformula := by intro i; fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recL_active
    · exact rfl
    · exact rfl

theorem op1RRow_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel op1RRow) where
  subject := fpActive bounded_subjectNoun
  formula := fpActive bounded_rightFormula
  evaluation := fpActive bounded_rightResult
  subformula := by intro i; fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recR_active
    · exact rfl
    · exact rfl

theorem computeTreeNounRealization :
    ComputePublicTreeNounRealization 97 exec.computePublicTree := by
  have h : (bfsForest [exec.computePublicTree]).map NTree.label
      = [computePublicLabel consRow, computePublicLabel op1LRow,
        computePublicLabel op1RRow] := by
    rw [ExactExecution.computePublicTree_bfs, ExactExecution.computePublicRows, computeRows_eq]
    rfl
  unfold ComputePublicTreeNounRealization ComputePublicRowsNounRealization
  rw [h]
  refine List.forall_iff_forall_mem.mpr ?_
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl
  · exact consRow_nounRealization
  · exact op1LRow_nounRealization
  · exact op1RRow_nounRealization

/-! ### Per-row public memory realizations -/

theorem memSingleChildRealization (pub : MemoryTable.Pub F)
    (hst : MemoryTable.fanoutMem pub.st = 1)
    (hpt : FPSlotRealized seedZ 97 .active pub.pt.noun)
    (hlc : FPSlotRealized seedZ 97 .active pub.lc.noun)
    (hrc : pub.rc = MemoryTable.Cell.zero)
    (hkind : memoryMemRecKind pub.st = .active)
    (hmem : MemRecSlotRealized seedZ 97 .active pub.mem) :
    MemoryPublicRowNounRealization 97 (lblOf pub) where
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

theorem memDecomposeRealization (pub : MemoryTable.Pub F)
    (hpt : FPSlotRealized seedZ 97 .active pub.pt.noun)
    (hlc : FPSlotRealized seedZ 97 .active pub.lc.noun)
    (hrc : FPSlotRealized seedZ 97 .active pub.rc.noun)
    (hmem : pub.mem = ComputeTable.MemRec.zero) :
    MemoryPublicRowNounRealization 97 (MemoryTable.MState.decompose, (memInputs, pub)) where
  parent := hpt
  child := by
    intro i; fin_cases i
    · exact hlc
    · exact hrc
  memoryRecord := hmem

theorem memHaltRealization (pub : MemoryTable.Pub F)
    (hpt : FPSlotRealized seedZ 97 .active pub.pt.noun)
    (hlc : pub.lc = MemoryTable.Cell.zero)
    (hrc : pub.rc = MemoryTable.Cell.zero)
    (hmem : pub.mem = ComputeTable.MemRec.zero) :
    MemoryPublicRowNounRealization 97 (MemoryTable.MState.halt, (memInputs, pub)) where
  parent := hpt
  child := by
    intro i; fin_cases i
    · exact hlc
    · exact hrc
  memoryRecord := hmem

theorem pReadF_realization : MemoryPublicRowNounRealization 97 (lblOf pReadF) :=
  memSingleChildRealization pReadF rfl (fpActive bounded_formulaNoun)
    (fpActive bounded_formulaNoun) rfl rfl (recCons_active.formRRow _)
theorem pReadL_realization : MemoryPublicRowNounRealization 97 (lblOf pReadL) :=
  memSingleChildRealization pReadL rfl (fpActive bounded_leftFormula)
    (fpActive bounded_leftFormula) rfl rfl (recL_active.formRRow _)
theorem pReadR_realization : MemoryPublicRowNounRealization 97 (lblOf pReadR) :=
  memSingleChildRealization pReadR rfl (fpActive bounded_rightFormula)
    (fpActive bounded_rightFormula) rfl rfl (recR_active.formRRow _)
theorem pVerifyF_realization : MemoryPublicRowNounRealization 97 (lblOf pVerifyF) :=
  memSingleChildRealization pVerifyF rfl (fpActive bounded_rightFormula)
    (fpActive bounded_rightFormula) rfl rfl (recCons_active.formRRow _)
theorem pVerifyL_realization : MemoryPublicRowNounRealization 97 (lblOf pVerifyL) :=
  memSingleChildRealization pVerifyL rfl (fpActive bounded_leftResult)
    (fpActive bounded_leftResult) rfl rfl (recL_active.formRRow _)
theorem pVerifyR_realization : MemoryPublicRowNounRealization 97 (lblOf pVerifyR) :=
  memSingleChildRealization pVerifyR rfl (fpActive bounded_rightResult)
    (fpActive bounded_rightResult) rfl rfl (recR_active.formRRow _)
theorem pDecF_realization : MemoryPublicRowNounRealization 97 (lblOf pDecF) :=
  memDecomposeRealization pDecF (fpActive bounded_formulaNoun)
    (fpActive bounded_leftFormula) (fpActive bounded_rightFormula) rfl
theorem pDecL_realization : MemoryPublicRowNounRealization 97 (lblOf pDecL) :=
  memDecomposeRealization pDecL (fpActive bounded_leftFormula)
    (fpActive bounded_op1Head) (fpActive bounded_leftResult) rfl
theorem pDecR_realization : MemoryPublicRowNounRealization 97 (lblOf pDecR) :=
  memDecomposeRealization pDecR (fpActive bounded_rightFormula)
    (fpActive bounded_op1Head) (fpActive bounded_rightResult) rfl
theorem pDummyHalt_realization : MemoryPublicRowNounRealization 97 (lblOf pDummyHalt) :=
  memHaltRealization pDummyHalt (fpActive (bounded_atom 0 (by norm_num))) rfl rfl rfl
theorem pHaltL1_realization : MemoryPublicRowNounRealization 97 (lblOf pHaltL1) :=
  memHaltRealization pHaltL1 (fpActive (bounded_atom 1 (by norm_num))) rfl rfl rfl
theorem pHaltL5_realization : MemoryPublicRowNounRealization 97 (lblOf pHaltL5) :=
  memHaltRealization pHaltL5 (fpActive (bounded_atom 5 (by norm_num))) rfl rfl rfl
theorem pHaltR1_realization : MemoryPublicRowNounRealization 97 (lblOf pHaltR1) :=
  memHaltRealization pHaltR1 (fpActive (bounded_atom 1 (by norm_num))) rfl rfl rfl
theorem pHaltR6_realization : MemoryPublicRowNounRealization 97 (lblOf pHaltR6) :=
  memHaltRealization pHaltR6 (fpActive (bounded_atom 6 (by norm_num))) rfl rfl rfl

theorem memoryForestNounRealization :
    MemoryPublicForestNounRealization 97 exec.memoryForest := by
  unfold MemoryPublicForestNounRealization MemoryPublicRowsNounRealization
  rw [show (bfsForest exec.memoryForest).map NTree.label = exec.memoryRows from rfl,
    memoryRows_eq]
  refine List.forall_iff_forall_mem.mpr ?_
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pDummyHalt_realization
  · exact pReadF_realization
  · exact pDecF_realization
  · exact pReadL_realization
  · exact pReadR_realization
  · exact pDecL_realization
  · exact pVerifyF_realization
  · exact pHaltL1_realization
  · exact pVerifyL_realization
  · exact pDecR_realization
  · exact pHaltL5_realization
  · exact pHaltR1_realization
  · exact pVerifyR_realization
  · exact pHaltR6_realization

/-! ### Leaf-atom existence on the served forest -/

theorem leafAtomHalt (k : ℕ) (hk : k < 97) (acc : F) :
    MemoryLeafAtomsRealized 97 (mLeaf (haltPub k acc)) :=
  ⟨k, hk, by
    show ((k : ℕ) : F) = (enc (Noun.atom k)).leaf
    simp [enc, GlobalCarryRecognizer.enc_atom]⟩

theorem leafAtoms_tDummyHalt : MemoryLeafAtomsRealized 97 tDummyHalt :=
  leafAtomHalt 0 (by norm_num) 0
theorem leafAtoms_tHaltL1 : MemoryLeafAtomsRealized 97 tHaltL1 :=
  leafAtomHalt 1 (by norm_num) (qL + qR)
theorem leafAtoms_tHaltL5 : MemoryLeafAtomsRealized 97 tHaltL5 :=
  leafAtomHalt 5 (by norm_num) qR
theorem leafAtoms_tHaltR1 : MemoryLeafAtomsRealized 97 tHaltR1 :=
  leafAtomHalt 1 (by norm_num) qR
theorem leafAtoms_tHaltR6 : MemoryLeafAtomsRealized 97 tHaltR6 :=
  leafAtomHalt 6 (by norm_num) 0
theorem leafAtoms_tVerifyL : MemoryLeafAtomsRealized 97 tVerifyL := leafAtoms_tHaltL5
theorem leafAtoms_tDecL : MemoryLeafAtomsRealized 97 tDecL :=
  ⟨leafAtoms_tHaltL1, leafAtoms_tVerifyL⟩
theorem leafAtoms_tReadL : MemoryLeafAtomsRealized 97 tReadL := leafAtoms_tDecL
theorem leafAtoms_tVerifyR : MemoryLeafAtomsRealized 97 tVerifyR := leafAtoms_tHaltR6
theorem leafAtoms_tDecR : MemoryLeafAtomsRealized 97 tDecR :=
  ⟨leafAtoms_tHaltR1, leafAtoms_tVerifyR⟩
theorem leafAtoms_tVerifyF : MemoryLeafAtomsRealized 97 tVerifyF := leafAtoms_tDecR
theorem leafAtoms_tReadR : MemoryLeafAtomsRealized 97 tReadR := leafAtoms_tVerifyF
theorem leafAtoms_tDecF : MemoryLeafAtomsRealized 97 tDecF :=
  ⟨leafAtoms_tReadL, leafAtoms_tReadR⟩
theorem leafAtoms_rootTree : MemoryLeafAtomsRealized 97 rootTree := leafAtoms_tDecF

theorem nounRealization : ExactExecutionNounRealization 97 cfg exec where
  computeTree := computeTreeNounRealization
  memoryForest := memoryForestNounRealization
  memoryLeaves := by
    intro tree htree
    simp only [exec, List.mem_cons, List.not_mem_nil, or_false] at htree
    rcases htree with rfl | rfl
    · exact leafAtoms_tDummyHalt
    · exact leafAtoms_rootTree

/-! ## The cumulative language bundle and the assembled semantic data -/

theorem language
    (hReadF : Vmem memInputs pReadF) (hDecF : Vmem memInputs pDecF)
    (hReadL : Vmem memInputs pReadL) (hReadR : Vmem memInputs pReadR)
    (hDecL : Vmem memInputs pDecL) (hVerifyF : Vmem memInputs pVerifyF)
    (hVerifyL : Vmem memInputs pVerifyL) (hDecR : Vmem memInputs pDecR)
    (hVerifyR : Vmem memInputs pVerifyR) :
    NounRealizedTraversableChainedSemanticExactLanguage 97 cfg exec where
  traversable := traversable hReadF hDecF hReadL hReadR hDecL hVerifyF hVerifyL hDecR hVerifyR
  nounRealization := nounRealization

/-- The exact per-row semantic data of the branching cons slice. -/
def semanticData
    (hReadF : Vmem memInputs pReadF) (hDecF : Vmem memInputs pDecF)
    (hReadL : Vmem memInputs pReadL) (hReadR : Vmem memInputs pReadR)
    (hDecL : Vmem memInputs pDecL) (hVerifyF : Vmem memInputs pVerifyF)
    (hVerifyL : Vmem memInputs pVerifyL) (hDecR : Vmem memInputs pDecR)
    (hVerifyR : Vmem memInputs pVerifyR) :
    SemanticTrace.ExactExecutionSemanticData 97 4 cfg exec where
  language := language hReadF hDecF hReadL hReadR hDecL hVerifyF hVerifyL hDecR hVerifyR
  rowAccepted := fun i => ExactExecution.computeRowAt_accepted computeRowsAccepted i
  rows := rowData

end

end Nock.NockVMROM.Thm54.TraceGen.ConsConfig

#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.semanticPreimage
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.language
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.semanticData
