/-
  Nock/NockVMROM/Thm54/TraceGen/Op1Language.lean

  The cumulative
  `NounRealizedTraversableChainedSemanticExactLanguage` bundle for the OP1 slice
  `*[0 [1 5]] = 5` over `K = ZMod 97`, `Λ = 3`, seed `z = 8`, `α = 4`.

  It mirrors `DistinctCensusExecution.lean` (the F97 fixture) and the K73cubic sibling
  `ConcreteStrictPackage.lean` at the minimal OP1 size (1 compute row, 5 memory rows), but stays
  generic over `ZMod 97` — no cubic base-change, no `noncomputable`/`Classical` fixture
  constructors.  It consumes the row-level web of `Op1RowWeb.lean` and produces:

  * `semanticPreimage`/`semanticExactLanguage`  (the single committed record `([1 5], 5, 3, α)`);
  * `chained`   (well-formedness + LogUp chaining boundaries);
  * `traversable`  (arity-3/2 exact topology);
  * `nounRealization`  (bounded noun realization of every public row and every leaf atom);
  * `language`  — the full bundle the semantic-data field consumes.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op1RowWeb
import Nock.NockVMROM.Thm54.Language
import Nock.NockVMROM.Thm54.NounRealization

namespace Nock.NockVMROM.Thm54.TraceGen.Op1Config

open Nock Nock.Walk Nock.NockVM Nock.MemoryTable Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton

/-! ## Canonical derived IO of the slice -/

/-- The execution emits exactly one request: the encoded single committed record. -/
theorem derived_request_singleton :
    (exec seedZ alphaA).derivedRequestIO =
      [encRecFormR (requestRecord seedZ alphaA) formRDefault] := by
  simp [ExactExecution.derivedRequestIO, rawRequests_eq]

/-- The `read_root` row serves exactly one response: the same encoded record. -/
theorem derived_response_singleton :
    (exec seedZ alphaA).derivedResponseIO =
      [encRecFormR (requestRecord seedZ alphaA) formRDefault] := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, memoryRows_eq]
  simp [dummyHaltRow, readRow, decomposeRow, headRow, verifyRow, tailRow, dummyHaltPub, readPub,
    decomposePub, headPub, verifyPub, tailPub, Pub.cprime, rowRecord, rowCprime]

/-! ## H. Semantic IO preimage

The single semantic record is `([1 5], 5, axis 3, ts α^1)`; over `ZMod 97` the semantic axis
`F` and the table field `K` coincide, so `bridge F F` embeds the axis `3` by the identity. -/

/-- The unique semantic `nmrMEF` record realizing `requestRecord = ([1 5], 5, 3, α)`.  Its
timestamp exponent is `1`, so `nmrEncoding … α` realizes `α ^ 1 = α`. -/
noncomputable def semanticRecord : (nmrMEF F F).Rec :=
  (3,
    ((((fp seedZ formulaNoun).size,
        (fp seedZ formulaNoun).dyck,
        (fp seedZ formulaNoun).leaf),
      ((fp seedZ resultNoun).size,
        (fp seedZ resultNoun).dyck,
        (fp seedZ resultNoun).leaf)),
    1))

/-- Decoding `semanticRecord` at the honest challenge is the honest committed record. -/
theorem semantic_preimage_record :
    memRecOfNMR F F
        ((nmrEncoding F F (cfg seedZ alphaA).challenges.α).encode semanticRecord) =
      requestRecord seedZ alphaA := by
  ext <;>
    simp [memRecOfNMR, nmrEncoding, semanticRecord, cfg, requestRecord, seedZ, alphaA]

/-- The single-record bridge equation. -/
theorem semantic_bridge_eq :
    bridge F F (cfg seedZ alphaA).challenges.α (cfg seedZ alphaA).challenges.lam semanticRecord =
      encRecFormR (requestRecord seedZ alphaA) formRDefault := by
  rw [← d2_record_bridge_agrees, semantic_preimage_record]
  rfl

/-- `α = 4` has multiplicative order `24` in `ZMod 97` — bounds the semantic timestamp window. -/
theorem alphaA_order : orderOf alphaA = 24 := by
  rw [show alphaA = (4 : F) from rfl, orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

/-- The semantic IO preimage: one request, one response, bridging to the derived IO. -/
noncomputable def semanticPreimage :
    SemanticIOPreimage (cfg seedZ alphaA) (exec seedZ alphaA) where
  timestampBound := 2
  timestampBound_le_order := by
    change 2 ≤ orderOf alphaA
    rw [alphaA_order]; norm_num
  semanticRequests := [semanticRecord]
  semanticResponses := [semanticRecord]
  requestTimestampBound := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    norm_num [semanticRecord]
  responseTimestampBound := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    norm_num [semanticRecord]
  semantic_lmio := by
    refine ⟨by norm_num [IO.InRange, cfg], [semanticRecord], le_refl _, by simp,
      fun x => Iff.rfl, List.Perm.refl _⟩
  requestTimestamp_determines := by
    intro x hx y hy _
    simp only [List.mem_singleton] at hx hy
    rw [hx, hy]
  requests_bridge := by
    rw [bridgeRecords, List.map_singleton, semantic_bridge_eq, derived_request_singleton]
  responses_bridge := by
    rw [bridgeRecords, List.map_singleton, semantic_bridge_eq, derived_response_singleton]

/-- The exact semantic language: rows accepted plus the bridging preimage. -/
theorem semanticExactLanguage
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    SemanticExactLanguage (cfg seedZ alphaA) (exec seedZ alphaA) :=
  ⟨computeRowsAccepted, memoryRowsAccepted hread hdec hver, ⟨semanticPreimage⟩⟩

/-! ## Chained boundaries (well-formedness + LogUp chaining) -/

theorem chained
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    ChainedSemanticExactLanguage (cfg seedZ alphaA) (exec seedZ alphaA) where
  semantic := semanticExactLanguage hread hdec hver
  z_ne_zero := seedZ_ne_zero
  compute_wf := compute_wf_all
  memory_wf := memory_wf_all
  compute_chain := compute_chain
  memory_chain := memory_chain
  memory_first_counts := by rw [memoryPubAt_zero]; rfl
  memory_first_indicator := by rw [memoryPubAt_zero]; rfl
  memory_first_ipre := by rw [memoryPubAt_zero]; rfl
  memory_last_icur := by
    have hlast :
        (cfg seedZ alphaA).orbit.lastIndex (cfg seedZ alphaA).memRows
          (cfg seedZ alphaA).memRows_pos = ⟨5, by norm_num [cfg]⟩ := rfl
    rw [hlast, memoryPubAt_five]; rfl
  memory_same_lambda := ExactExecution.memory_same_lambda_of_const _ (some formRDefault) (by
    intro i
    fin_cases i
    · rw [memoryPubAt_zero]; rfl
    · rw [memoryPubAt_one]; rfl
    · rw [memoryPubAt_two]; rfl
    · rw [memoryPubAt_three]; rfl
    · rw [memoryPubAt_four]; rfl
    · rw [memoryPubAt_five]; rfl)

/-! ## Traversable topology (arity 3/2) -/

theorem traversable
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    TraversableChainedSemanticExactLanguage (cfg seedZ alphaA) (exec seedZ alphaA) where
  chained := chained hread hdec hver
  compute_topology := compute_topology
  memory_topology := memory_topology hread hdec hver

/-! ## J. Bounded noun realization -/

theorem fpRealized {n : Noun} (hb : FieldEmbedding.BoundedBy 97 n) :
    FPRealized seedZ 97 (fp seedZ n) :=
  ⟨n, hb, rfl⟩

theorem fpActive {n : Noun} (hb : FieldEmbedding.BoundedBy 97 n) :
    FPSlotRealized seedZ 97 .active (fp seedZ n) :=
  ⟨fpRealized hb, FPRealized.ne_zero seedZ_ne_zero (fpRealized hb)⟩

theorem bounded_atom (k : ℕ) (hk : k < 97) : FieldEmbedding.BoundedBy 97 (.atom k) := by
  simp [FieldEmbedding.BoundedBy]; exact hk

theorem bounded_subjectNoun : FieldEmbedding.BoundedBy 97 subjectNoun := bounded_atom 0 (by norm_num)
theorem bounded_headNoun : FieldEmbedding.BoundedBy 97 headNoun := bounded_atom 1 (by norm_num)
theorem bounded_resultNoun : FieldEmbedding.BoundedBy 97 resultNoun := bounded_atom 5 (by norm_num)
theorem bounded_formulaNoun : FieldEmbedding.BoundedBy 97 formulaNoun :=
  ⟨bounded_headNoun, bounded_resultNoun⟩

/-- The single committed record is an active pair of realized noun fingerprints. -/
theorem request_active :
    MemRecSlotRealized seedZ 97 .active (requestRecord seedZ alphaA) :=
  ⟨by
    intro h
    have hd := congrArg (fun r : MemRec F => r.ts) h
    simp only [requestRecord, MemRec.zero] at hd
    exact absurd hd (by decide),
   fpActive bounded_formulaNoun, fpActive bounded_resultNoun⟩

/-! ### Per-row public realizations -/

theorem computeRow_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel (computeRow seedZ alphaA)) where
  subject := fpActive bounded_subjectNoun
  formula := fpActive bounded_formulaNoun
  evaluation := fpActive bounded_resultNoun
  subformula := by intro i; fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact request_active
    · exact rfl
    · exact rfl

theorem computeTreeNounRealization :
    ComputePublicTreeNounRealization 97 (exec seedZ alphaA).computePublicTree := by
  have h : (bfsForest [(exec seedZ alphaA).computePublicTree]).map NTree.label
      = [computePublicLabel (computeRow seedZ alphaA)] := by
    rw [ExactExecution.computePublicTree_bfs, ExactExecution.computePublicRows,
      computeRows_eq]
    rfl
  unfold ComputePublicTreeNounRealization ComputePublicRowsNounRealization
  rw [h]
  refine List.forall_iff_forall_mem.mpr ?_
  intro row hrow
  simp only [List.mem_singleton] at hrow
  subst hrow
  exact computeRow_nounRealization

/-- A single-child memory row (`read_root`/`verify_child`): active parent, active live child,
zero right pad, active live record. -/
theorem memSingleChildRealization (pub : MemoryTable.Pub F)
    (hst : MemoryTable.fanoutMem pub.st = 1)
    (hpt : FPSlotRealized seedZ 97 .active pub.pt.noun)
    (hlc : FPSlotRealized seedZ 97 .active pub.lc.noun)
    (hrc : pub.rc = MemoryTable.Cell.zero)
    (hkind : memoryMemRecKind pub.st = .active)
    (hmem : MemRecSlotRealized seedZ 97 .active pub.mem) :
    MemoryPublicRowNounRealization 97 (pub.st, (memoryInputs seedZ, pub)) where
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

/-- A decompose row: active parent, two active live children, zero (padding) record. -/
theorem memDecomposeRealization (pub : MemoryTable.Pub F)
    (hpt : FPSlotRealized seedZ 97 .active pub.pt.noun)
    (hlc : FPSlotRealized seedZ 97 .active pub.lc.noun)
    (hrc : FPSlotRealized seedZ 97 .active pub.rc.noun)
    (hmem : pub.mem = ComputeTable.MemRec.zero) :
    MemoryPublicRowNounRealization 97 (MemoryTable.MState.decompose, (memoryInputs seedZ, pub)) where
  parent := hpt
  child := by
    intro i; fin_cases i
    · exact hlc
    · exact hrc
  memoryRecord := hmem

/-- A halt leaf row: active parent, zero children, zero record. -/
theorem memHaltRealization (pub : MemoryTable.Pub F)
    (hpt : FPSlotRealized seedZ 97 .active pub.pt.noun)
    (hlc : pub.lc = MemoryTable.Cell.zero)
    (hrc : pub.rc = MemoryTable.Cell.zero)
    (hmem : pub.mem = ComputeTable.MemRec.zero) :
    MemoryPublicRowNounRealization 97 (MemoryTable.MState.halt, (memoryInputs seedZ, pub)) where
  parent := hpt
  child := by
    intro i; fin_cases i
    · exact hlc
    · exact hrc
  memoryRecord := hmem

theorem dummyHaltRow_realization :
    MemoryPublicRowNounRealization 97 (dummyHaltRow seedZ) :=
  memHaltRealization (dummyHaltPub seedZ) (fpActive (bounded_atom 0 (by norm_num))) rfl rfl rfl

theorem readRow_realization :
    MemoryPublicRowNounRealization 97 (readRow seedZ alphaA) :=
  memSingleChildRealization (readPub seedZ alphaA) rfl (fpActive bounded_formulaNoun)
    (fpActive bounded_formulaNoun) rfl rfl (request_active.formRRow _)

theorem decomposeRow_realization :
    MemoryPublicRowNounRealization 97 (decomposeRow seedZ alphaA) :=
  memDecomposeRealization (decomposePub seedZ alphaA) (fpActive bounded_formulaNoun)
    (fpActive bounded_headNoun) (fpActive bounded_resultNoun) rfl

theorem headRow_realization :
    MemoryPublicRowNounRealization 97 (headRow seedZ) :=
  memHaltRealization (headPub seedZ) (fpActive bounded_headNoun) rfl rfl rfl

theorem verifyRow_realization :
    MemoryPublicRowNounRealization 97 (verifyRow seedZ alphaA) :=
  memSingleChildRealization (verifyPub seedZ alphaA) rfl (fpActive bounded_resultNoun)
    (fpActive bounded_resultNoun) rfl rfl (request_active.formRRow _)

theorem tailRow_realization :
    MemoryPublicRowNounRealization 97 (tailRow seedZ) :=
  memHaltRealization (tailPub seedZ) (fpActive bounded_resultNoun) rfl rfl rfl

theorem memoryForestNounRealization :
    MemoryPublicForestNounRealization 97 (exec seedZ alphaA).memoryForest := by
  have h : (bfsForest (exec seedZ alphaA).memoryForest).map NTree.label
      = (exec seedZ alphaA).memoryRows := rfl
  unfold MemoryPublicForestNounRealization MemoryPublicRowsNounRealization
  rw [h, memoryRows_eq]
  refine List.forall_iff_forall_mem.mpr ?_
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl
  · exact dummyHaltRow_realization
  · exact readRow_realization
  · exact decomposeRow_realization
  · exact headRow_realization
  · exact verifyRow_realization
  · exact tailRow_realization

/-! ### Leaf-atom existence on the served forest -/

theorem leafAtoms_dummyHaltTree : MemoryLeafAtomsRealized 97 (dummyHaltTree seedZ) :=
  ⟨0, by norm_num, by
    show ((0 : ℕ) : F) = (fp seedZ (.atom 0)).leaf
    simp [fp, dummyHaltCell, dummyHaltPub, GlobalCarryRecognizer.enc_atom]⟩

theorem leafAtoms_tailTree : MemoryLeafAtomsRealized 97 (tailTree seedZ) :=
  ⟨5, by norm_num, by
    show ((5 : ℕ) : F) = (fp seedZ resultNoun).leaf
    simp [fp, resultNoun, GlobalCarryRecognizer.enc_atom]⟩

theorem leafAtoms_verifyTree : MemoryLeafAtomsRealized 97 (verifyTree seedZ alphaA) :=
  leafAtoms_tailTree

theorem leafAtoms_headTree : MemoryLeafAtomsRealized 97 (headTree seedZ) :=
  ⟨1, by norm_num, by
    show ((1 : ℕ) : F) = (fp seedZ headNoun).leaf
    simp [fp, headNoun, GlobalCarryRecognizer.enc_atom]⟩

theorem leafAtoms_decomposeTree : MemoryLeafAtomsRealized 97 (decomposeTree seedZ alphaA) :=
  ⟨leafAtoms_headTree, leafAtoms_verifyTree⟩

theorem leafAtoms_readTree : MemoryLeafAtomsRealized 97 (readTree seedZ alphaA) :=
  leafAtoms_decomposeTree

theorem nounRealization :
    ExactExecutionNounRealization 97 (cfg seedZ alphaA) (exec seedZ alphaA) where
  computeTree := computeTreeNounRealization
  memoryForest := memoryForestNounRealization
  memoryLeaves := by
    intro tree htree
    simp only [exec, List.mem_cons, List.not_mem_nil, or_false] at htree
    rcases htree with rfl | rfl
    · exact leafAtoms_dummyHaltTree
    · exact leafAtoms_readTree

/-! ## The cumulative language bundle -/

theorem language
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    NounRealizedTraversableChainedSemanticExactLanguage 97 (cfg seedZ alphaA)
      (exec seedZ alphaA) where
  traversable := traversable hread hdec hver
  nounRealization := nounRealization

end Nock.NockVMROM.Thm54.TraceGen.Op1Config
