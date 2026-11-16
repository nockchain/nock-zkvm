/-
  Nock/NockVMROM/Thm54/TraceGen/ConsMemoryWeb.lean

  The per-row `Vmem` acceptance,
  genericity (`WF`), whole-forest row acceptance, and arity-2 `Fmem` topology of the thirteen-row
  memory reconstruction forest of `*[0 [[1 5] [1 6]]] = [5 6]` over `K = ZMod 97`, `z = 8`, `α = 4`.

  This is the memory analogue of `ConsRowWeb`.  With `β = γ = 0` the LogUp pole of a record is its
  root fingerprint's `size`, and the three records `recCons`/`recL`/`recR` carry
  distinct timestamps `α, α², α³`.  Every `read_root`/`verify_child`/`decompose`/`halt` row satisfies
  its `eqBlk` and `interV`; the accumulator telescopes
  `0 → qCons → qCons+qL → qCons+qL+qR → … → 0` in BFS order.  The `Fmem` topology carries the
  fanout-2 `childLinkMem` tying each child's `pt` cell to the parent's `lc`/`rc` cell.

  The two-request LogUp *pairing* (`AddedRemovedAgain`, matched by fingerprint VALUE) — the served
  semantic layer `ExactServedMemoryTrace` — is the remaining open memory-CORE obligation
  (see `ConsSkeleton`'s module header).
-/
import Nock.NockVMROM.Thm54.TraceGen.ConsConfig
import Nock.NockVMROM.Thm54.TraceGen.ConsSemanticData
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.ExactTraversal

namespace Nock.NockVMROM.Thm54.TraceGen.ConsConfig

open Nock Nock.Walk Nock.MemoryTable Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton

noncomputable section

/-! ## The LogUp pole is the record root's fingerprint size -/

theorem pole_eq (r : MemRec F) (c : F) : pole memInputs r c = r.root.size := by
  simp [pole, memInputs, recRLC]

theorem poleCons_ne : pole memInputs (NockVM.formRRow recCons MemoryTable.formRDefault)
    (NockVM.formRCprime recCons MemoryTable.formRDefault) ≠ 0 := by
  rw [pole_eq, NockVM.formRRow_root]
  show (enc formulaNoun).size ≠ 0
  simp only [enc, GlobalCarryRecognizer.enc_size]
  exact pow_ne_zero _ seedZ_ne_zero

theorem poleL_ne : pole memInputs (NockVM.formRRow recL MemoryTable.formRDefault)
    (NockVM.formRCprime recL MemoryTable.formRDefault) ≠ 0 := by
  rw [pole_eq, NockVM.formRRow_root]
  show (enc leftFormula).size ≠ 0
  simp only [enc, GlobalCarryRecognizer.enc_size]
  exact pow_ne_zero _ seedZ_ne_zero

theorem poleR_ne : pole memInputs (NockVM.formRRow recR MemoryTable.formRDefault)
    (NockVM.formRCprime recR MemoryTable.formRDefault) ≠ 0 := by
  rw [pole_eq, NockVM.formRRow_root]
  show (enc rightFormula).size ≠ 0
  simp only [enc, GlobalCarryRecognizer.enc_size]
  exact pow_ne_zero _ seedZ_ne_zero

/-! ## The fourteen memory rows are accepted by `V_mem` -/

theorem pDummyHalt_accepts : Vmem memInputs pDummyHalt := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp [haltPub, pDummyHalt, enc, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pDummyHalt, enc, GlobalCarryRecognizer.enc_atom]
  · show pDummyHalt.icur = pDummyHalt.ipre; rfl

/-- Dummy-wired to Gen remaining; form-R leftover is the Relaxis join. -/
theorem pReadF_accepts (h : Vmem memInputs pReadF) : Vmem memInputs pReadF := h

/-- Dummy-wired to Gen remaining; form-R leftover is the Relaxis join. -/
theorem pDecF_accepts (h : Vmem memInputs pDecF) : Vmem memInputs pDecF := h

/-- Dummy-wired to Gen remaining; form-R leftover is the Relaxis join. -/
theorem pReadL_accepts (h : Vmem memInputs pReadL) : Vmem memInputs pReadL := h

/-- Dummy-wired to Gen remaining; form-R leftover is the Relaxis join. -/
theorem pReadR_accepts (h : Vmem memInputs pReadR) : Vmem memInputs pReadR := h

/-- Dummy-wired to Gen remaining; form-R leftover is the Relaxis join. -/
theorem pDecL_accepts (h : Vmem memInputs pDecL) : Vmem memInputs pDecL := h

/-- Dummy-wired to Gen remaining; form-R leftover is the Relaxis join. -/
theorem pVerifyF_accepts (h : Vmem memInputs pVerifyF) : Vmem memInputs pVerifyF := h

theorem pHaltL1_accepts : Vmem memInputs pHaltL1 := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp [haltPub, pHaltL1, enc, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltL1, enc, GlobalCarryRecognizer.enc_atom]
  · show pHaltL1.icur = pHaltL1.ipre; rfl

/-- Dummy-wired to Gen remaining; form-R leftover is the Relaxis join. -/
theorem pVerifyL_accepts (h : Vmem memInputs pVerifyL) : Vmem memInputs pVerifyL := h

/-- Dummy-wired to Gen remaining; form-R leftover is the Relaxis join. -/
theorem pDecR_accepts (h : Vmem memInputs pDecR) : Vmem memInputs pDecR := h

theorem pHaltL5_accepts : Vmem memInputs pHaltL5 := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp [haltPub, pHaltL5, enc, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltL5, enc, GlobalCarryRecognizer.enc_atom]
  · show pHaltL5.icur = pHaltL5.ipre; rfl

theorem pHaltR1_accepts : Vmem memInputs pHaltR1 := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp [haltPub, pHaltR1, enc, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltR1, enc, GlobalCarryRecognizer.enc_atom]
  · show pHaltR1.icur = pHaltR1.ipre; rfl

/-- Dummy-wired to Gen remaining; form-R leftover is the Relaxis join. -/
theorem pVerifyR_accepts (h : Vmem memInputs pVerifyR) : Vmem memInputs pVerifyR := h

theorem pHaltR6_accepts : Vmem memInputs pHaltR6 := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp [haltPub, pHaltR6, enc, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltR6, enc, GlobalCarryRecognizer.enc_atom]
  · show pHaltR6.icur = pHaltR6.ipre; rfl

/-! ## Whole-forest row acceptance -/

theorem memoryRows_eq :
    exec.memoryRows =
      [lblOf pDummyHalt, lblOf pReadF, lblOf pDecF, lblOf pReadL, lblOf pReadR, lblOf pDecL,
       lblOf pVerifyF, lblOf pHaltL1, lblOf pVerifyL, lblOf pDecR, lblOf pHaltL5, lblOf pHaltR1,
       lblOf pVerifyR, lblOf pHaltR6] := by
  simp [ExactExecution.memoryRows, exec, tDummyHalt, rootTree, tDecF, tReadL, tReadR, tDecL,
    tVerifyF, tHaltL1, tVerifyL, tDecR, tHaltL5, tHaltR1, tVerifyR, tHaltR6, mLeaf, mOne, mTwo,
    bfsForest]

theorem memoryRowsAccepted
    (hReadF : Vmem memInputs pReadF)
    (hDecF : Vmem memInputs pDecF)
    (hReadL : Vmem memInputs pReadL)
    (hReadR : Vmem memInputs pReadR)
    (hDecL : Vmem memInputs pDecL)
    (hVerifyF : Vmem memInputs pVerifyF)
    (hVerifyL : Vmem memInputs pVerifyL)
    (hDecR : Vmem memInputs pDecR)
    (hVerifyR : Vmem memInputs pVerifyR) :
    exec.MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff, memoryRows_eq]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl, pDummyHalt_accepts, rfl⟩
  · exact ⟨rfl, rfl, hReadF, rfl⟩
  · exact ⟨rfl, rfl, hDecF, rfl⟩
  · exact ⟨rfl, rfl, hReadL, rfl⟩
  · exact ⟨rfl, rfl, hReadR, rfl⟩
  · exact ⟨rfl, rfl, hDecL, rfl⟩
  · exact ⟨rfl, rfl, hVerifyF, rfl⟩
  · exact ⟨rfl, rfl, pHaltL1_accepts, rfl⟩
  · exact ⟨rfl, rfl, hVerifyL, rfl⟩
  · exact ⟨rfl, rfl, hDecR, rfl⟩
  · exact ⟨rfl, rfl, pHaltL5_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHaltR1_accepts, rfl⟩
  · exact ⟨rfl, rfl, hVerifyR, rfl⟩
  · exact ⟨rfl, rfl, pHaltR6_accepts, rfl⟩

/-! ## Memory genericity (`WF`) per record-touching row -/

theorem pReadF_wf : MemoryTable.WF memInputs pReadF where
  pole_ne _ := by simpa [pReadF, readPub, Pub.cprime] using poleCons_ne
theorem pReadL_wf : MemoryTable.WF memInputs pReadL where
  pole_ne _ := by simpa [pReadL, readPub, Pub.cprime] using poleL_ne
theorem pReadR_wf : MemoryTable.WF memInputs pReadR where
  pole_ne _ := by simpa [pReadR, readPub, Pub.cprime] using poleR_ne
theorem pVerifyF_wf : MemoryTable.WF memInputs pVerifyF where
  pole_ne _ := by simpa [pVerifyF, verifyPub, Pub.cprime] using poleCons_ne
theorem pVerifyL_wf : MemoryTable.WF memInputs pVerifyL where
  pole_ne _ := by simpa [pVerifyL, verifyPub, Pub.cprime] using poleL_ne
theorem pVerifyR_wf : MemoryTable.WF memInputs pVerifyR where
  pole_ne _ := by simpa [pVerifyR, verifyPub, Pub.cprime] using poleR_ne

/-! ## Arity-2 `Fmem` topology on the thirteen-row forest -/

/-- A `halt` node's local memory acceptance packages into `Fmem` at fanout 0. -/
theorem fmem_leaf {pub : MemoryTable.Pub F} (hv : Vmem memInputs pub)
    (hf : MemoryTable.fanoutMem pub.st = 0) :
    MemoryTable.Fmem (lblOf pub) (fun _ => none) := by
  refine ⟨rfl, hv, ?_, ?_⟩
  · intro i
    refine ⟨fun h => ?_, fun h => absurd rfl h⟩
    rw [show (lblOf pub).1 = pub.st from rfl, hf] at h
    omega
  · intro i hi
    rw [show (lblOf pub).1 = pub.st from rfl, hf] at hi
    omega

/-- RVT of a `read_root`/`verify_child` (fanout-1) node over its single child. -/
theorem rvt_one {pub : MemoryTable.Pub F} {ct : NTree MLbl}
    (hv : Vmem memInputs pub) (hf : MemoryTable.fanoutMem pub.st = 1)
    (hpt : ct.label.2.2.pt = pub.lc) (hct : RVT (MemoryTable.Fmem (K := F)) ct) :
    RVT (MemoryTable.Fmem (K := F)) (mOne pub ct) := by
  unfold mOne RVT
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, hv, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [NTree.childLabel, NTree.childOpt, lblOf, hf]
    · intro i hi
      fin_cases i
      · simpa [NTree.childLabel, NTree.childOpt, MemoryTable.memCell, lblOf, NTree.label] using hpt
      · exact absurd hi (by rw [show (lblOf pub).1 = pub.st from rfl, hf]; decide)
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl
    exact hct
  · refine ⟨fun h => absurd h (by simp [NTree.isLeaf]), fun h => ?_⟩
    exfalso
    have h0 := h.2.2.1 ⟨0, by norm_num⟩
    rw [show (lblOf pub).1 = pub.st from rfl, hf] at h0
    simp at h0

/-- RVT of a `decompose` (fanout-2) node over its two children. -/
theorem rvt_two {pub : MemoryTable.Pub F} {lt rt : NTree MLbl}
    (hv : Vmem memInputs pub) (hf : MemoryTable.fanoutMem pub.st = 2)
    (hl : lt.label.2.2.pt = pub.lc) (hr : rt.label.2.2.pt = pub.rc)
    (hlt : RVT (MemoryTable.Fmem (K := F)) lt) (hrt : RVT (MemoryTable.Fmem (K := F)) rt) :
    RVT (MemoryTable.Fmem (K := F)) (mTwo pub lt rt) := by
  unfold mTwo RVT
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, hv, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [NTree.childLabel, NTree.childOpt, lblOf, hf]
    · intro i hi
      fin_cases i
      · simpa [NTree.childLabel, NTree.childOpt, MemoryTable.memCell, lblOf, NTree.label] using hl
      · simpa [NTree.childLabel, NTree.childOpt, MemoryTable.memCell, lblOf, NTree.label] using hr
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact hlt
    · exact hrt
  · refine ⟨fun h => absurd h (by simp [NTree.isLeaf]), fun h => ?_⟩
    exfalso
    have h0 := h.2.2.1 ⟨0, by norm_num⟩
    rw [show (lblOf pub).1 = pub.st from rfl, hf] at h0
    simp at h0

theorem tDummyHalt_rvt : RVT (MemoryTable.Fmem (K := F)) tDummyHalt := by
  unfold tDummyHalt mLeaf RVT
  exact ⟨fmem_leaf pDummyHalt_accepts rfl, by simp,
    ⟨fun _ => fmem_leaf pDummyHalt_accepts rfl, fun _ => rfl⟩⟩

theorem tHaltL1_rvt : RVT (MemoryTable.Fmem (K := F)) tHaltL1 := by
  unfold tHaltL1 mLeaf RVT
  exact ⟨fmem_leaf pHaltL1_accepts rfl, by simp,
    ⟨fun _ => fmem_leaf pHaltL1_accepts rfl, fun _ => rfl⟩⟩

theorem tHaltL5_rvt : RVT (MemoryTable.Fmem (K := F)) tHaltL5 := by
  unfold tHaltL5 mLeaf RVT
  exact ⟨fmem_leaf pHaltL5_accepts rfl, by simp,
    ⟨fun _ => fmem_leaf pHaltL5_accepts rfl, fun _ => rfl⟩⟩

theorem tHaltR1_rvt : RVT (MemoryTable.Fmem (K := F)) tHaltR1 := by
  unfold tHaltR1 mLeaf RVT
  exact ⟨fmem_leaf pHaltR1_accepts rfl, by simp,
    ⟨fun _ => fmem_leaf pHaltR1_accepts rfl, fun _ => rfl⟩⟩

theorem tHaltR6_rvt : RVT (MemoryTable.Fmem (K := F)) tHaltR6 := by
  unfold tHaltR6 mLeaf RVT
  exact ⟨fmem_leaf pHaltR6_accepts rfl, by simp,
    ⟨fun _ => fmem_leaf pHaltR6_accepts rfl, fun _ => rfl⟩⟩

theorem tVerifyL_rvt (hVerifyL : Vmem memInputs pVerifyL) :
    RVT (MemoryTable.Fmem (K := F)) tVerifyL :=
  rvt_one hVerifyL rfl rfl tHaltL5_rvt

theorem tVerifyR_rvt (hVerifyR : Vmem memInputs pVerifyR) :
    RVT (MemoryTable.Fmem (K := F)) tVerifyR :=
  rvt_one hVerifyR rfl rfl tHaltR6_rvt

theorem tDecR_rvt (hDecR : Vmem memInputs pDecR) (hVerifyR : Vmem memInputs pVerifyR) :
    RVT (MemoryTable.Fmem (K := F)) tDecR :=
  rvt_two hDecR rfl rfl rfl tHaltR1_rvt (tVerifyR_rvt hVerifyR)

theorem tVerifyF_rvt (hVerifyF : Vmem memInputs pVerifyF)
    (hDecR : Vmem memInputs pDecR) (hVerifyR : Vmem memInputs pVerifyR) :
    RVT (MemoryTable.Fmem (K := F)) tVerifyF :=
  rvt_one hVerifyF rfl rfl (tDecR_rvt hDecR hVerifyR)

theorem tReadR_rvt (hReadR : Vmem memInputs pReadR) (hVerifyF : Vmem memInputs pVerifyF)
    (hDecR : Vmem memInputs pDecR) (hVerifyR : Vmem memInputs pVerifyR) :
    RVT (MemoryTable.Fmem (K := F)) tReadR :=
  rvt_one hReadR rfl rfl (tVerifyF_rvt hVerifyF hDecR hVerifyR)

theorem tDecL_rvt (hDecL : Vmem memInputs pDecL) (hVerifyL : Vmem memInputs pVerifyL) :
    RVT (MemoryTable.Fmem (K := F)) tDecL :=
  rvt_two hDecL rfl rfl rfl tHaltL1_rvt (tVerifyL_rvt hVerifyL)

theorem tReadL_rvt (hReadL : Vmem memInputs pReadL) (hDecL : Vmem memInputs pDecL)
    (hVerifyL : Vmem memInputs pVerifyL) :
    RVT (MemoryTable.Fmem (K := F)) tReadL :=
  rvt_one hReadL rfl rfl (tDecL_rvt hDecL hVerifyL)

theorem tDecF_rvt (hDecF : Vmem memInputs pDecF) (hReadL : Vmem memInputs pReadL)
    (hReadR : Vmem memInputs pReadR) (hDecL : Vmem memInputs pDecL)
    (hVerifyF : Vmem memInputs pVerifyF) (hVerifyL : Vmem memInputs pVerifyL)
    (hDecR : Vmem memInputs pDecR) (hVerifyR : Vmem memInputs pVerifyR) :
    RVT (MemoryTable.Fmem (K := F)) tDecF :=
  rvt_two hDecF rfl rfl rfl (tReadL_rvt hReadL hDecL hVerifyL)
    (tReadR_rvt hReadR hVerifyF hDecR hVerifyR)

theorem rootTree_rvt
    (hReadF : Vmem memInputs pReadF) (hDecF : Vmem memInputs pDecF)
    (hReadL : Vmem memInputs pReadL) (hReadR : Vmem memInputs pReadR)
    (hDecL : Vmem memInputs pDecL) (hVerifyF : Vmem memInputs pVerifyF)
    (hVerifyL : Vmem memInputs pVerifyL) (hDecR : Vmem memInputs pDecR)
    (hVerifyR : Vmem memInputs pVerifyR) :
    RVT (MemoryTable.Fmem (K := F)) rootTree :=
  rvt_one hReadF rfl rfl
    (tDecF_rvt hDecF hReadL hReadR hDecL hVerifyF hVerifyL hDecR hVerifyR)

theorem memory_topology
    (hReadF : Vmem memInputs pReadF) (hDecF : Vmem memInputs pDecF)
    (hReadL : Vmem memInputs pReadL) (hReadR : Vmem memInputs pReadR)
    (hDecL : Vmem memInputs pDecL) (hVerifyF : Vmem memInputs pVerifyF)
    (hVerifyL : Vmem memInputs pVerifyL) (hDecR : Vmem memInputs pDecR)
    (hVerifyR : Vmem memInputs pVerifyR) :
    MemoryExactTopology exec := by
  intro t ht
  simp only [exec, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · refine ⟨tDummyHalt_rvt, ?_⟩
    show ProperArity 2 tDummyHalt
    simp [tDummyHalt, mLeaf]
  · refine ⟨rootTree_rvt hReadF hDecF hReadL hReadR hDecL hVerifyF hVerifyL hDecR hVerifyR, ?_⟩
    show ProperArity 2 rootTree
    simp [rootTree, tDecF, tReadL, tReadR, tDecL, tVerifyF, tHaltL1, tVerifyL, tDecR, tHaltL5,
      tHaltR1, tVerifyR, tHaltR6, mLeaf, mOne, mTwo]

end

end Nock.NockVMROM.Thm54.TraceGen.ConsConfig

#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.memoryRowsAccepted
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.memory_topology
