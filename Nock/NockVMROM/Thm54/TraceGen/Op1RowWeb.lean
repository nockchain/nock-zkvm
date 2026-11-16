/-
  Nock/NockVMROM/Thm54/TraceGen/Op1RowWeb.lean

  The per-row acceptance,
  genericity, BFS re-indexing, chained-boundary, and arity-3/2 topology web of the OP1 slice
  `*[0 [1 5]] = 5` over `K = ZMod 97`, `Λ = 3`, seed `z = 8`, `α = 4`.

  This mirrors `DistinctCensusExecution.lean` (the F97 fixture) and the K73cubic sibling
  `ConcreteStrictPackage.lean` at the minimal OP1 size (1 compute row, 5 memory rows), but stays
  generic over `ZMod 97` — no cubic base-change, no `noncomputable`/`Classical` fixture
  constructors.  It is the foundation the language bundle (`Op1Language.lean`) consumes.

  The single committed record is `requestRecord = ([1 5], 5, axis 3, ts α)`; its LogUp pole is
  `(fp z [1 5]).size = z² = 64`, so the honest `intermediate` reciprocal is `reqPoleInv = 64⁻¹`.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op1Config
import Nock.NockVMROM.Thm54.TraceGen.Op1BuildableParts
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.ExactTraversal

namespace Nock.NockVMROM.Thm54.TraceGen.Op1Config

open Nock Nock.Walk Nock.MemoryTable Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton

/-! ## The LogUp pole of the single committed record -/

/-- With `β = γ = 0` the pole of the request record is its root's fingerprint size
`(fp z [1 5]).size = z²`. -/
theorem pole_req (z α : F) :
    pole (memoryInputs z) (requestRecord z α) 1 = (fp z formulaNoun).size := by
  unfold pole memoryInputs
  simp only [recRLC, zero_mul, mul_zero, add_zero, zero_pow, sub_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true]
  rfl

/-- The request record's root size is `z ^ 2 ≠ 0` (`[1 5]` has two leaves), so the pole is
nonzero and the LogUp genericity `WF` holds. -/
theorem pole_req_ne (z : F) (hz : z ≠ 0) (α : F) :
    pole (memoryInputs z) (requestRecord z α) 1 ≠ 0 := by
  rw [pole_req]
  show z ^ formulaNoun.leaves ≠ 0
  exact pow_ne_zero _ hz

/-- The executed (row-level) record has the same pole: with `β = γ = 0` the pole reads only the
root fingerprint, which the Form R encode keeps. -/
theorem pole_row_eq (z α : F) :
    pole (memoryInputs z) (rowRecord z α) (rowCprime z α) =
      pole (memoryInputs z) (requestRecord z α) 1 := by
  simp [pole, recRLC, memoryInputs, rowRecord, NockVM.formRRow]

theorem pole_row_ne (z : F) (hz : z ≠ 0) (α : F) :
    pole (memoryInputs z) (rowRecord z α) (rowCprime z α) ≠ 0 := by
  rw [pole_row_eq]; exact pole_req_ne z hz α

/-- `reqPoleInv z = pole⁻¹` — the honest field reciprocal read `+` at `read_root`, `−` at
`verify_child`. -/
theorem reqPoleInv_eq (z α : F) :
    reqPoleInv z = (pole (memoryInputs z) (requestRecord z α) 1)⁻¹ := by
  rw [pole_req, reqPoleInv]

/-! ## The single `OP_1` compute row -/

/-- The OP1 slice's compute row is accepted by the algorithmic compute verifier. -/
theorem compute_accepts :
    Vcomp (computeInputs seedZ alphaA) (computePub seedZ alphaA) (computeDec seedZ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero headNoun resultNoun
  · ext <;> norm_num [computePub, requestRecord, computeDec, computeInputs, seedZ, alphaA]
  · simp [SVhead, headAtom, computePub, computeDec, computeInputs, fp,
      headNoun, GlobalCarryRecognizer.enc_atom, State.toNat, seedZ, alphaA]
  · norm_num [memBlk, computePub, computeInputs, MemRec.zero, seedZ, alphaA]
  · simp [evalV, sfz1, sfz2, sfz3, computePub, computeDec]

/-- Compute genericity (nonzero sizes, RLC nondegeneracy) on the `OP_1` row. -/
theorem compute_wf :
    ComputeTable.WF (computeInputs seedZ alphaA) (computePub seedZ alphaA) where
  rlc5 := by simp [computePub]
  size8 := by simp [computePub]
  size11 := by simp [computePub]

/-! ## The five memory rows are accepted by `V_mem` -/

theorem dummy_accepts : Vmem (memoryInputs seedZ) (dummyHaltPub seedZ) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · show (fp seedZ (.atom 0)).size = seedZ
    simp [fp, dummyHaltCell, dummyHaltPub, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]
  · show (fp seedZ (.atom 0)).dyck = 0
    simp [fp, dummyHaltCell, dummyHaltPub, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]

/-- Dummy-wired to Gen remaining; form-R leftover is the Relaxis join. -/
theorem read_accepts
    (h : Vmem (memoryInputs seedZ) (readPub seedZ alphaA)) :
    Vmem (memoryInputs seedZ) (readPub seedZ alphaA) :=
  h

/-- Dummy-wired to Gen remaining; form-R leftover is the Relaxis join. -/
theorem decompose_accepts
    (h : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA)) :
    Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA) :=
  h

theorem head_accepts : Vmem (memoryInputs seedZ) (headPub seedZ) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · show (fp seedZ headNoun).size = seedZ
    simp [fp, headNoun, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]
  · show (fp seedZ headNoun).dyck = 0
    simp [fp, headNoun, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]

/-- Dummy-wired to Gen remaining; form-R leftover is the Relaxis join. -/
theorem verify_accepts
    (h : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA) :=
  h

theorem tail_accepts : Vmem (memoryInputs seedZ) (tailPub seedZ) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · show (fp seedZ resultNoun).size = seedZ
    simp [fp, resultNoun, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]
  · show (fp seedZ resultNoun).dyck = 0
    simp [fp, resultNoun, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]

/-! ## Memory genericity (`WF`) per row -/

theorem dummy_wf : MemoryTable.WF (memoryInputs seedZ) (dummyHaltPub seedZ) where
  pole_ne h := by simp [dummyHaltPub] at h

theorem read_wf : MemoryTable.WF (memoryInputs seedZ) (readPub seedZ alphaA) where
  pole_ne _ := by
    simpa [readPub, Pub.cprime] using pole_row_ne seedZ seedZ_ne_zero alphaA

theorem decompose_wf : MemoryTable.WF (memoryInputs seedZ) (decomposePub seedZ alphaA) where
  pole_ne h := by simp [decomposePub] at h

theorem head_wf : MemoryTable.WF (memoryInputs seedZ) (headPub seedZ) where
  pole_ne h := by simp [headPub] at h

theorem verify_wf : MemoryTable.WF (memoryInputs seedZ) (verifyPub seedZ alphaA) where
  pole_ne _ := by
    simpa [verifyPub, Pub.cprime] using pole_row_ne seedZ seedZ_ne_zero alphaA

theorem tail_wf : MemoryTable.WF (memoryInputs seedZ) (tailPub seedZ) where
  pole_ne h := by simp [tailPub] at h

/-! ## Whole-trace row acceptance -/

theorem computeRowsAccepted : (exec seedZ alphaA).ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff, computeRows_eq]
  intro row hrow
  simp only [List.mem_singleton] at hrow
  subst row
  exact ⟨rfl, rfl, compute_accepts⟩

theorem memoryRowsAccepted
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    (exec seedZ alphaA).MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff, memoryRows_eq]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl, dummy_accepts, rfl⟩
  · exact ⟨rfl, rfl, hread, rfl⟩
  · exact ⟨rfl, rfl, hdec, rfl⟩
  · exact ⟨rfl, rfl, head_accepts, rfl⟩
  · exact ⟨rfl, rfl, hver, rfl⟩
  · exact ⟨rfl, rfl, tail_accepts, rfl⟩

/-! ## BFS re-indexing of the canonical rows -/

theorem computePubAt_zero :
    (exec seedZ alphaA).computePubAt ⟨0, by norm_num [cfg]⟩ = computePub seedZ alphaA := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt, computeRows_eq, cfg,
    computeRow]

theorem computeDecAt_zero :
    (exec seedZ alphaA).computeDecAt ⟨0, by norm_num [cfg]⟩ = computeDec seedZ := by
  norm_num [ExactExecution.computeDecAt, ExactExecution.computeRowAt, computeRows_eq, cfg,
    computeRow]

theorem memoryPubAt_zero :
    (exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩ = dummyHaltPub seedZ := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg,
    dummyHaltRow]

theorem memoryPubAt_one :
    (exec seedZ alphaA).memoryPubAt ⟨1, by norm_num [cfg]⟩ = readPub seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, readRow]

theorem memoryPubAt_two :
    (exec seedZ alphaA).memoryPubAt ⟨2, by norm_num [cfg]⟩ = decomposePub seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg,
    decomposeRow]

theorem memoryPubAt_three :
    (exec seedZ alphaA).memoryPubAt ⟨3, by norm_num [cfg]⟩ = headPub seedZ := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, headRow]

theorem memoryPubAt_four :
    (exec seedZ alphaA).memoryPubAt ⟨4, by norm_num [cfg]⟩ = verifyPub seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg,
    verifyRow]

theorem memoryPubAt_five :
    (exec seedZ alphaA).memoryPubAt ⟨5, by norm_num [cfg]⟩ = tailPub seedZ := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, tailRow]

/-! ## Genericity and chained boundaries on the canonical rows -/

theorem compute_wf_all :
    ∀ i, ComputeTable.WF (cfg seedZ alphaA).challenges.computeInputs
      ((exec seedZ alphaA).computePubAt i) := by
  intro i
  fin_cases i
  rw [computePubAt_zero]
  exact compute_wf

theorem memory_wf_all :
    ∀ i, MemoryTable.WF (cfg seedZ alphaA).challenges.memoryInputs
      ((exec seedZ alphaA).memoryPubAt i) := by
  intro i
  fin_cases i
  · rw [memoryPubAt_zero]; exact dummy_wf
  · rw [memoryPubAt_one]; exact read_wf
  · rw [memoryPubAt_two]; exact decompose_wf
  · rw [memoryPubAt_three]; exact head_wf
  · rw [memoryPubAt_four]; exact verify_wf
  · rw [memoryPubAt_five]; exact tail_wf

theorem compute_chain :
    ∀ i : Fin (cfg seedZ alphaA).compRows, ∀ _ : (i : ℕ) + 1 < (cfg seedZ alphaA).compRows,
      ((exec seedZ alphaA).computePubAt i).ln =
        ((exec seedZ alphaA).computePubAt ⟨(i : ℕ) + 1, by omega⟩).ln_prev := by
  intro i hi
  fin_cases i
  norm_num [cfg] at hi

theorem memory_chain :
    ∀ i : Fin (cfg seedZ alphaA).memRows, ∀ _ : (i : ℕ) + 1 < (cfg seedZ alphaA).memRows,
      ((exec seedZ alphaA).memoryPubAt i).icur =
        ((exec seedZ alphaA).memoryPubAt ⟨(i : ℕ) + 1, by omega⟩).ipre := by
  intro i hi
  fin_cases i
  · rw [memoryPubAt_zero, memoryPubAt_one]; rfl
  · rw [memoryPubAt_one, memoryPubAt_two]; rfl
  · rw [memoryPubAt_two, memoryPubAt_three]; rfl
  · rw [memoryPubAt_three, memoryPubAt_four]; rfl
  · rw [memoryPubAt_four, memoryPubAt_five]; rfl
  · norm_num [cfg] at hi

/-! ## Arity-3/2 topology on the compute tree and the single memory root -/

/-- A `read_root`/`verify_child` node's local memory acceptance packages into `Fmem` at fanout 1. -/
theorem fmem_leaf {pub : MemoryTable.Pub F} (hv : Vmem (memoryInputs seedZ) pub)
    (hf : MemoryTable.fanoutMem pub.st = 0) :
    MemoryTable.Fmem (pub.st, (memoryInputs seedZ, pub)) (fun _ => none) := by
  refine ⟨rfl, hv, ?_, ?_⟩
  · intro i
    refine ⟨fun h => ?_, fun h => absurd rfl h⟩
    rw [show (pub.st, (memoryInputs seedZ, pub)).1 = pub.st from rfl, hf] at h
    omega
  · intro i hi
    rw [show (pub.st, (memoryInputs seedZ, pub)).1 = pub.st from rfl, hf] at hi
    omega

theorem dummyHaltTree_rvt : RVT (MemoryTable.Fmem (K := F)) (dummyHaltTree seedZ) := by
  unfold dummyHaltTree dummyHaltRow RVT
  exact ⟨fmem_leaf dummy_accepts rfl, by simp,
    ⟨fun _ => fmem_leaf dummy_accepts rfl, fun _ => rfl⟩⟩

theorem tailTree_rvt : RVT (MemoryTable.Fmem (K := F)) (tailTree seedZ) := by
  unfold tailTree tailRow RVT
  exact ⟨fmem_leaf tail_accepts rfl, by simp, ⟨fun _ => fmem_leaf tail_accepts rfl, fun _ => rfl⟩⟩

theorem headTree_rvt : RVT (MemoryTable.Fmem (K := F)) (headTree seedZ) := by
  unfold headTree headRow RVT
  exact ⟨fmem_leaf head_accepts rfl, by simp, ⟨fun _ => fmem_leaf head_accepts rfl, fun _ => rfl⟩⟩

theorem verifyTree_rvt
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    RVT (MemoryTable.Fmem (K := F)) (verifyTree seedZ alphaA) := by
  unfold verifyTree verifyRow RVT
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, hver, ?_, ?_⟩
    · intro i
      fin_cases i <;>
        simp [MemoryTable.fanoutMem, verifyPub, NTree.childLabel, NTree.childOpt, tailTree]
    · intro i hi
      fin_cases i
      · simp [NTree.childLabel, NTree.childOpt, MemoryTable.memCell, tailTree, tailRow,
          verifyPub, tailPub, tailCell, verifyCell]
      · simp [MemoryTable.fanoutMem] at hi
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact tailTree_rvt
  · refine ⟨fun h => absurd h (by simp [NTree.isLeaf]), fun h => ?_⟩
    exfalso
    have h0 := h.2.2.1 ⟨0, by norm_num⟩
    simp [MemoryTable.fanoutMem, verifyPub] at h0

theorem decomposeTree_rvt
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    RVT (MemoryTable.Fmem (K := F)) (decomposeTree seedZ alphaA) := by
  unfold decomposeTree decomposeRow RVT
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, hdec, ?_, ?_⟩
    · intro i
      fin_cases i <;>
        simp [MemoryTable.fanoutMem, decomposePub, NTree.childLabel, NTree.childOpt,
          headTree, verifyTree]
    · intro i hi
      fin_cases i
      · simp [NTree.childLabel, NTree.childOpt, MemoryTable.memCell, headTree, headRow,
          decomposePub, headPub, headCell, decomposeCell]
      · simp [NTree.childLabel, NTree.childOpt, MemoryTable.memCell, verifyTree, verifyRow,
          decomposePub, verifyPub, verifyCell, decomposeCell]
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact headTree_rvt
    · exact verifyTree_rvt hver
  · refine ⟨fun h => absurd h (by simp [NTree.isLeaf]), fun h => ?_⟩
    exfalso
    have h0 := h.2.2.1 ⟨0, by norm_num⟩
    simp [MemoryTable.fanoutMem, decomposePub] at h0

theorem readTree_rvt
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    RVT (MemoryTable.Fmem (K := F)) (readTree seedZ alphaA) := by
  unfold readTree readRow RVT
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, hread, ?_, ?_⟩
    · intro i
      fin_cases i <;>
        simp [MemoryTable.fanoutMem, readPub, NTree.childLabel, NTree.childOpt, decomposeTree]
    · intro i hi
      fin_cases i
      · simp [NTree.childLabel, NTree.childOpt, MemoryTable.memCell, decomposeTree,
          decomposeRow, readPub, decomposePub, decomposeCell, seedCell]
      · simp [MemoryTable.fanoutMem, readPub] at hi
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact decomposeTree_rvt hdec hver
  · refine ⟨fun h => absurd h (by simp [NTree.isLeaf]), fun h => ?_⟩
    exfalso
    have h0 := h.2.2.1 ⟨0, by norm_num⟩
    simp [MemoryTable.fanoutMem, readPub] at h0

/-- The single `OP_1` compute row is a proper arity-3 `RVT` leaf. -/
theorem computeRow_fcomp :
    ComputeTable.Fcomp (computeRow seedZ alphaA) (fun _ => none) := by
  refine ⟨rfl, compute_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [computeRow, ComputeTable.fanoutComp]
  · intro i hi; simp [computeRow, ComputeTable.fanoutComp] at hi

theorem compute_topology : ComputeExactTopology (exec seedZ alphaA) := by
  refine ⟨?_, ?_⟩
  · show RVT (ComputeTable.Fcomp (K := F)) (exec seedZ alphaA).computeTree
    show RVT (ComputeTable.Fcomp (K := F)) (.node (computeRow seedZ alphaA) [])
    unfold RVT
    refine ⟨?_, by simp, ?_⟩
    · rw [show (fun i : Fin 3 => (NTree.node (computeRow seedZ alphaA) []).childLabel i)
          = (fun _ => none) by funext i; fin_cases i <;> rfl]
      exact computeRow_fcomp
    · exact ⟨fun _ => computeRow_fcomp, fun _ => rfl⟩
  · show ProperArity 3 (exec seedZ alphaA).computeTree
    simp [exec]

theorem memory_topology
    (hread : Vmem (memoryInputs seedZ) (readPub seedZ alphaA))
    (hdec : Vmem (memoryInputs seedZ) (decomposePub seedZ alphaA))
    (hver : Vmem (memoryInputs seedZ) (verifyPub seedZ alphaA)) :
    MemoryExactTopology (exec seedZ alphaA) := by
  intro t ht
  simp only [exec, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · refine ⟨dummyHaltTree_rvt, ?_⟩
    show ProperArity 2 (dummyHaltTree seedZ)
    simp [dummyHaltTree]
  · refine ⟨readTree_rvt hread hdec hver, ?_⟩
    show ProperArity 2 (readTree seedZ alphaA)
    simp [readTree, decomposeTree, headTree, verifyTree, tailTree]

end Nock.NockVMROM.Thm54.TraceGen.Op1Config
