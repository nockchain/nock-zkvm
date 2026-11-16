import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.RedTeam.Thm54P2Nonvacuity
import Nock.NockVMROM.Thm54.SemanticTimestampStrategy

/-!
The tempting forest

`read_root → decompose → (halt, halt)` and `verify_child → halt`

The accepted construction below keeps two roots and six rows, but puts
the matching `verify_child` in the right branch of the first tree and uses a balanced halt as the
second root.  Its aggregate BFS order is

`read_root, halt, decompose, halt, verify_child, halt`

and its LogUp accumulator is `0 → 1 → 1 → 1 → 1 → 0 → 0`.

The obstruction above was measured on the pre-Form R rows (`λ = 1`, `C' = 1`).
-/

open scoped Classical

namespace Nock.RedTeam.Thm54P3Nonvacuity

noncomputable section

open Nock Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.Framework.Thm54
open Nock.RedTeam.Thm54P2Nonvacuity

/-! ## Field and eight-point orbit -/

theorem characteristic_gt_eleven :
    ∀ n : ℕ, n ≤ 11 → (n : K17) = 1 → n = 1 :=
  char_valid_17

theorem omega2_order : orderOf (2 : K17) = 8 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

def orbit8 : OrbitDomain K17 where
  h := 3
  ω := 2
  βcoset := 1
  βcoset_ne_zero := by norm_num
  order_ω := by simpa using omega2_order

/-! ## Balanced memory rows -/

/-- The decompose child carries
    `(pw, counts) = (128, 192)`, so the parent is `(0, 0)` in `K17`. -/
def seedReadCell : Cell K17 := ⟨rootFP, 128 - 16 * 2 * 4, 192 - 2 * 24 * 4⟩

/-- Decompose of halt `(0,0)` and verify `(64,64)` at `λ = 2`: `pw = λ(0+64) = 128`,
    `counts = 0+64+(λ-1)·64 + 64 = 192`. -/
def liftedDecompCell : Cell K17 := ⟨rootFP, 128, 192⟩

/-- A verify of timestamp `4` over a zero child carries `(pw, counts) = (64, 64)`
    (`eqBlk` adds `λ^{n−1}·ts = 16·4` to both). -/
def verifyCell : Cell K17 := ⟨tailFP, 16 * 4, 16 * 4⟩

noncomputable def pRead : MemoryTable.Pub K17 where
  st := .read_root
  pt := seedReadCell
  lc := liftedDecompCell
  rc := Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := rowRecord
  cprime? := some rowC
  lambda? := some formRDefault
  ipre := 0
  icur := 1

noncomputable def pDummy : MemoryTable.Pub K17 where
  st := .halt
  pt := headCell
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some formRDefault
  ipre := 0
  icur := 0

noncomputable def pDecomp : MemoryTable.Pub K17 where
  st := .decompose
  pt := liftedDecompCell
  lc := headCell
  rc := verifyCell
  lcSt := .halt
  rcSt := .verify_child
  mem := MemRec.zero
  lambda? := some formRDefault
  ipre := 1
  icur := 1

noncomputable def pHead : MemoryTable.Pub K17 where
  st := .halt
  pt := headCell
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some formRDefault
  ipre := 1
  icur := 1

noncomputable def pVerify : MemoryTable.Pub K17 where
  st := .verify_child
  pt := verifyCell
  lc := tailCell
  rc := Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := rowRecord
  cprime? := some rowC
  lambda? := some formRDefault
  ipre := 1
  icur := 0

noncomputable def pTail : MemoryTable.Pub K17 where
  st := .halt
  pt := tailCell
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some formRDefault
  ipre := 0
  icur := 0

theorem verify_pole : pole mInp pVerify.mem rowC = 1 := by
  simpa [pVerify] using read_pole

theorem verify_pole_ne : pole mInp pVerify.mem rowC ≠ 0 := by
  rw [verify_pole]
  norm_num

theorem read_accepts_p3 : Vmem mInp pRead := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp only [eqBlk, pRead, seedReadCell, liftedDecompCell, rowRecord, Pub.lambda,
      Pub.cprime, pwScaleExp_K17, Option.getD_some, rowC, formRDefault]
    norm_num
  · simp [interV, pRead, Pub.cprime]
    simpa [pole] using read_pole

theorem dummy_accepts : Vmem mInp pDummy := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp [eqBlk, pDummy, Thm54P2Nonvacuity.headCell, headFP, mInp,
      Cell.zero, MemRec.zero, FP.atomFP, Pub.lambda, Pub.cprime]
  · rfl

theorem decomp_accepts_p3 : Vmem mInp pDecomp := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_, rfl⟩
    · simp [pDecomp, liftedDecompCell, Thm54P2Nonvacuity.headCell, verifyCell, Pub.lambda,
        formRDefault]
      norm_num
    · simp [pDecomp, liftedDecompCell, Thm54P2Nonvacuity.headCell, verifyCell, Pub.lambda,
        formRDefault]
      norm_num
  · rfl

theorem head_accepts : Vmem mInp pHead := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp [eqBlk, pHead, Thm54P2Nonvacuity.headCell, headFP, mInp,
      Cell.zero, MemRec.zero, FP.atomFP, Pub.lambda, Pub.cprime]
  · rfl

theorem verify_accepts : Vmem mInp pVerify := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp only [eqBlk, pVerify, verifyCell, tailCell, rowRecord, Pub.lambda,
      pwScaleExp_K17, Option.getD_some, formRDefault]
    norm_num
  · simp [interV, pVerify, Pub.cprime]
    simpa [pVerify, pole] using verify_pole

theorem tail_accepts : Vmem mInp pTail := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp [eqBlk, pTail, tailCell, tailFP, mInp, Cell.zero, MemRec.zero, FP.atomFP,
      Pub.lambda, Pub.cprime]
  · rfl

theorem read_wf_p3 : MemoryTable.WF mInp pRead where
  pole_ne _ := by simpa [pRead, Pub.cprime] using read_pole_ne

theorem dummy_wf : MemoryTable.WF mInp pDummy where
  pole_ne h := by simp [pDummy] at h

theorem decomp_wf_p3 : MemoryTable.WF mInp pDecomp where
  pole_ne h := by simp [pDecomp] at h

theorem head_wf : MemoryTable.WF mInp pHead where
  pole_ne h := by simp [pHead] at h

theorem verify_wf : MemoryTable.WF mInp pVerify where
  pole_ne _ := by simpa [pVerify, Pub.cprime] using verify_pole_ne

theorem tail_wf : MemoryTable.WF mInp pTail where
  pole_ne h := by simp [pTail] at h

theorem compute_rap_row : ∃ ex, RAPcomp cInp cPub cDec ex :=
  (equiv_compute cInp cPub cDec compute_wf).mpr compute_accepts

theorem read_rap_row : ∃ g, RAPmem mInp pRead g :=
  (equiv_mem mInp pRead read_wf_p3).mpr read_accepts_p3

theorem dummy_rap_row : ∃ g, RAPmem mInp pDummy g :=
  (equiv_mem mInp pDummy dummy_wf).mpr dummy_accepts

theorem decomp_rap_row : ∃ g, RAPmem mInp pDecomp g :=
  (equiv_mem mInp pDecomp decomp_wf_p3).mpr decomp_accepts_p3

theorem head_rap_row : ∃ g, RAPmem mInp pHead g :=
  (equiv_mem mInp pHead head_wf).mpr head_accepts

theorem verify_rap_row : ∃ g, RAPmem mInp pVerify g :=
  (equiv_mem mInp pVerify verify_wf).mpr verify_accepts

theorem tail_rap_row : ∃ g, RAPmem mInp pTail g :=
  (equiv_mem mInp pTail tail_wf).mpr tail_accepts

/-! ## Two accepted memory trees -/

def readLabelP3 : MState × MemoryTable.DTmem K17 :=
  (.read_root, (mInp, pRead))

def dummyLabel : MState × MemoryTable.DTmem K17 :=
  (.halt, (mInp, pDummy))

def decompLabelP3 : MState × MemoryTable.DTmem K17 :=
  (.decompose, (mInp, pDecomp))

def headLabelP3 : MState × MemoryTable.DTmem K17 :=
  (.halt, (mInp, pHead))

def verifyLabel : MState × MemoryTable.DTmem K17 :=
  (.verify_child, (mInp, pVerify))

def tailLabelP3 : MState × MemoryTable.DTmem K17 :=
  (.halt, (mInp, pTail))

def tailTreeP3 : NTree (MState × MemoryTable.DTmem K17) :=
  .node tailLabelP3 []

def verifyTree : NTree (MState × MemoryTable.DTmem K17) :=
  .node verifyLabel [tailTreeP3]

def headTreeP3 : NTree (MState × MemoryTable.DTmem K17) :=
  .node headLabelP3 []

def decompTreeP3 : NTree (MState × MemoryTable.DTmem K17) :=
  .node decompLabelP3 [headTreeP3, verifyTree]

def readTreeP3 : NTree (MState × MemoryTable.DTmem K17) :=
  .node readLabelP3 [decompTreeP3]

def dummyTree : NTree (MState × MemoryTable.DTmem K17) :=
  .node dummyLabel []

theorem dummyLabel_accepts :
    MemoryTable.Fmem dummyLabel (fun _ => none) := by
  refine ⟨rfl, dummy_accepts, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [dummyLabel, MemoryTable.fanoutMem]
  · intro i hi
    simp [dummyLabel, MemoryTable.fanoutMem] at hi

theorem headLabel_accepts_p3 :
    MemoryTable.Fmem headLabelP3 (fun _ => none) := by
  refine ⟨rfl, head_accepts, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [headLabelP3, MemoryTable.fanoutMem]
  · intro i hi
    simp [headLabelP3, MemoryTable.fanoutMem] at hi

theorem tailLabel_accepts_p3 :
    MemoryTable.Fmem tailLabelP3 (fun _ => none) := by
  refine ⟨rfl, tail_accepts, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [tailLabelP3, MemoryTable.fanoutMem]
  · intro i hi
    simp [tailLabelP3, MemoryTable.fanoutMem] at hi

def verifyOut : Fin 2 → Option (MState × MemoryTable.DTmem K17)
  | 0 => some tailLabelP3
  | 1 => none

theorem verifyLabel_accepts :
    MemoryTable.Fmem verifyLabel verifyOut := by
  refine ⟨rfl, verify_accepts, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [verifyLabel, verifyOut, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i
    · simp [verifyOut, MemoryTable.memCell, verifyLabel, tailLabelP3,
        pVerify, pTail, tailCell]
    · simp [verifyLabel, MemoryTable.fanoutMem] at hi

def decompOutP3 : Fin 2 → Option (MState × MemoryTable.DTmem K17)
  | 0 => some headLabelP3
  | 1 => some verifyLabel

theorem decompLabel_accepts_p3 :
    MemoryTable.Fmem decompLabelP3 decompOutP3 := by
  refine ⟨rfl, decomp_accepts_p3, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [decompLabelP3, decompOutP3, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i <;>
      simp [decompOutP3, MemoryTable.memCell, decompLabelP3, headLabelP3,
        verifyLabel, pDecomp, pHead, pVerify, Thm54P2Nonvacuity.headCell, verifyCell]

def readOutP3 : Fin 2 → Option (MState × MemoryTable.DTmem K17)
  | 0 => some decompLabelP3
  | 1 => none

theorem readLabel_accepts_p3 :
    MemoryTable.Fmem readLabelP3 readOutP3 := by
  refine ⟨rfl, read_accepts_p3, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [readLabelP3, readOutP3, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i
    · simp [readOutP3, MemoryTable.memCell, readLabelP3, decompLabelP3,
        pRead, pDecomp, liftedDecompCell]
    · simp [readLabelP3, MemoryTable.fanoutMem] at hi

theorem tailTree_rvt_p3 : RVT (MemoryTable.Fmem (K := K17)) tailTreeP3 :=
  rvt_leaf tailLabel_accepts_p3

theorem verifyTree_rvt : RVT (MemoryTable.Fmem (K := K17)) verifyTree := by
  unfold verifyTree RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 2 => (NTree.node verifyLabel [tailTreeP3]).childLabel i) =
        verifyOut by
      funext i
      fin_cases i <;> rfl]
    exact verifyLabel_accepts
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact tailTree_rvt_p3
  · simp [NTree.isLeaf, MemoryTable.Fmem, verifyLabel, MemoryTable.fanoutMem]

theorem headTree_rvt_p3 : RVT (MemoryTable.Fmem (K := K17)) headTreeP3 :=
  rvt_leaf headLabel_accepts_p3

theorem decompTree_rvt_p3 : RVT (MemoryTable.Fmem (K := K17)) decompTreeP3 := by
  unfold decompTreeP3 RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show
      (fun i : Fin 2 => (NTree.node decompLabelP3 [headTreeP3, verifyTree]).childLabel i) =
        decompOutP3 by
      funext i
      fin_cases i <;> rfl]
    exact decompLabel_accepts_p3
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact headTree_rvt_p3
    · exact verifyTree_rvt
  · simp [NTree.isLeaf, MemoryTable.Fmem, decompLabelP3, MemoryTable.fanoutMem]

theorem readTree_rvt_p3 : RVT (MemoryTable.Fmem (K := K17)) readTreeP3 := by
  unfold readTreeP3 RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show
      (fun i : Fin 2 => (NTree.node readLabelP3 [decompTreeP3]).childLabel i) =
        readOutP3 by
      funext i
      fin_cases i <;> rfl]
    exact readLabel_accepts_p3
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact decompTree_rvt_p3
  · simp [NTree.isLeaf, MemoryTable.Fmem, readLabelP3, MemoryTable.fanoutMem]

theorem dummyTree_rvt : RVT (MemoryTable.Fmem (K := K17)) dummyTree :=
  rvt_leaf dummyLabel_accepts

/-! ## Exact carrier and canonical BFS rows -/

def cfg : ExactConfig K17 K17 where
  challenges :=
    { a := 0, b := 0, c := 0, α := 4, z := 1, β := 0, γ := 0,
      lam := formRDefault }
  Ksz := 4
  kMem := 2
  orbit := orbit8
  orbit_h_pos := by norm_num [orbit8]
  compRows := 1
  memRows := 6
  compRows_pos := by norm_num
  memRows_pos := by norm_num
  compRows_le := by norm_num [orbit8]
  memRows_le := by norm_num [orbit8]
  eDeg := 1
  eDeg_eq_one := rfl
  compNodes := fun i => orbit8.orbitPoint i
  compNodes_spec := by intro i; rfl
  memNodes := fun i => orbit8.orbitPoint i
  memNodes_spec := by intro i; rfl

theorem challenge_alignment :
    cfg.challenges.computeInputs = cInp ∧ cfg.challenges.memoryInputs = mInp :=
  ⟨rfl, rfl⟩

def exec : ExactExecution cfg where
  computeTree := computeTree
  memoryForest := [dummyTree, readTreeP3]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTree, bfsForest, NTree.size, totalSize, cfg]
  memory_bfs_length := by
    norm_num [readTreeP3, dummyTree, decompTreeP3, headTreeP3, verifyTree, tailTreeP3,
      bfsForest, NTree.size, totalSize, cfg]

/-! `execA` stores the a-bearing `sharedRecord` (axis `3`) on the `read_root`/`verify_child` rows; the
executed `exec` is its Form R row encode (`exec_eq_encodeMem`).  Inactive rows are shared. -/

theorem formRRow_shared : formRRow sharedRecord formRDefault = rowRecord := by
  have hax : nockAxisOf sharedRecord.axis = 3 := nockAxisOf_three
  simp only [formRRow, hax, formRT_shared]
  rfl

theorem formRCprime_shared : formRCprime sharedRecord formRDefault = rowC := by
  have hax : nockAxisOf sharedRecord.axis = 3 := nockAxisOf_three
  simp only [formRCprime, hax, formRC_shared]

noncomputable def pReadA : MemoryTable.Pub K17 :=
  { pRead with mem := sharedRecord, cprime? := none, lambda? := none }

noncomputable def pVerifyA : MemoryTable.Pub K17 :=
  { pVerify with mem := sharedRecord, cprime? := none, lambda? := none }

def readLabelP3A : MState × MemoryTable.DTmem K17 := (.read_root, (mInp, pReadA))
def verifyLabelA : MState × MemoryTable.DTmem K17 := (.verify_child, (mInp, pVerifyA))
def verifyTreeA : NTree (MState × MemoryTable.DTmem K17) := .node verifyLabelA [tailTreeP3]
def decompTreeP3A : NTree (MState × MemoryTable.DTmem K17) :=
  .node decompLabelP3 [headTreeP3, verifyTreeA]
def readTreeP3A : NTree (MState × MemoryTable.DTmem K17) := .node readLabelP3A [decompTreeP3A]

def execA : ExactExecution cfg where
  computeTree := computeTree
  memoryForest := [dummyTree, readTreeP3A]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTree, bfsForest, NTree.size, totalSize, cfg]
  memory_bfs_length := by
    norm_num [readTreeP3A, dummyTree, decompTreeP3A, headTreeP3, verifyTreeA, tailTreeP3,
      bfsForest, NTree.size, totalSize, cfg]

theorem exec_eq_encodeMem : exec = execA.encodeMem := by
  apply ExactExecution.ext
  · rfl
  · simp [ExactExecution.encodeMem, exec, execA, Nock.NockVMROM.Thm54.mapNTree, cfg,
      SemanticTimestampStrategy.MemoryRowTemplate.encodeRow, memoryMemRecKind,
      dummyTree, readTreeP3, decompTreeP3, headTreeP3, verifyTree, tailTreeP3,
      readTreeP3A, decompTreeP3A, verifyTreeA, dummyLabel, readLabelP3, decompLabelP3,
      headLabelP3, verifyLabel, tailLabelP3, readLabelP3A, verifyLabelA, pReadA, pVerifyA,
      pRead, pVerify, pDummy, pDecomp, pHead, pTail, formRRow_shared, formRCprime_shared]

theorem execution_rows :
    exec.computeRows = [cLabel] ∧
      exec.memoryRows =
        [dummyLabel, readLabelP3, decompLabelP3, headLabelP3, verifyLabel, tailLabelP3] := by
  constructor <;>
    norm_num [ExactExecution.computeRows, ExactExecution.memoryRows, exec, computeTree,
      dummyTree, readTreeP3, decompTreeP3, headTreeP3, verifyTree, tailTreeP3,
      bfsForest, NTree.size, totalSize]

theorem computePubAt_eq (i : Fin cfg.compRows) :
    exec.computePubAt i = cPub := by
  fin_cases i
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt,
    execution_rows.1, cfg, cLabel]

theorem memoryPubAt_zero :
    exec.memoryPubAt ⟨0, by norm_num [cfg]⟩ = pDummy := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
    execution_rows.2, cfg, dummyLabel]

theorem memoryPubAt_one :
    exec.memoryPubAt ⟨1, by norm_num [cfg]⟩ = pRead := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
    execution_rows.2, cfg, readLabelP3]

theorem memoryPubAt_two :
    exec.memoryPubAt ⟨2, by norm_num [cfg]⟩ = pDecomp := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
    execution_rows.2, cfg, decompLabelP3]

theorem memoryPubAt_three :
    exec.memoryPubAt ⟨3, by norm_num [cfg]⟩ = pHead := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
    execution_rows.2, cfg, headLabelP3]

theorem memoryPubAt_four :
    exec.memoryPubAt ⟨4, by norm_num [cfg]⟩ = pVerify := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
    execution_rows.2, cfg, verifyLabel]

theorem memoryPubAt_five :
    exec.memoryPubAt ⟨5, by norm_num [cfg]⟩ = pTail := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
    execution_rows.2, cfg, tailLabelP3]

theorem verify_emits_no_external_response :
    MemoryTable.responseRecords pVerify = [] := by
  exact MemoryTable.responseRecords_eq_nil_of_verify_child pVerify rfl rfl

theorem pRead_ver : pRead.ver = true := rfl
theorem pDummy_ver : pDummy.ver = false := rfl
theorem pDecomp_ver : pDecomp.ver = false := rfl
theorem pHead_ver : pHead.ver = false := rfl
theorem pVerify_ver : pVerify.ver = false := rfl
theorem pTail_ver : pTail.ver = false := rfl

set_option maxHeartbeats 400000 in
theorem derived_request_singleton :
    exec.derivedRequestIO = [encRecC rowRecord rowC] := by
  rw [ExactExecution.derivedRequestIO_eq_computeRows, execution_rows.1]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change (NockVM.activeRequestRecords cPub).map
      (fun r => encRecFormR r cfg.challenges.lam) = [encRecC rowRecord rowC]
  rw [raw_requests_singleton, List.map_singleton]
  exact congrArg (fun v => [v]) formR_shared

set_option maxHeartbeats 400000 in
theorem derived_response_singleton :
    exec.derivedResponseIO = [encRecC rowRecord rowC] := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, execution_rows.2]
  simp [readLabelP3, dummyLabel, decompLabelP3, headLabelP3, verifyLabel, tailLabelP3,
    pRead_ver, pDummy_ver, pDecomp_ver, pHead_ver, pVerify_ver, pTail_ver,
    Pub.cprime, encRecC, pRead]

theorem memory_state_sequence :
    exec.memoryRows.map Prod.fst =
      [.halt, .read_root, .decompose, .halt, .verify_child, .halt] := by
  rw [execution_rows.2]
  rfl


theorem semantic_exponent_one :
    semanticRecord.2.2 = 1 :=
  semanticRecord_timestamp

theorem shared_timestamp_is_alpha_one :
    sharedRecord.ts = cfg.challenges.α ^ semanticRecord.2.2 := by
  norm_num [sharedRecord, cfg, semanticRecord]

def semanticPreimage : SemanticIOPreimage cfg exec where
  timestampBound := 2
  timestampBound_le_order := by norm_num [cfg, omega4_order]
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
    rw [IO.LmIO_iff]
    exact ⟨by norm_num [IO.InRange, cfg], by simp, by simp, by simp⟩
  requestTimestamp_determines := by
    intro x hx y hy _
    simp only [List.mem_singleton] at hx hy
    rw [hx, hy]
  requests_bridge := by
    rw [bridgeRecords, List.map_singleton,
      show cfg.challenges.α = Thm54P2Nonvacuity.cfg.challenges.α by rfl,
      show cfg.challenges.lam = Thm54P2Nonvacuity.cfg.challenges.lam by rfl,
      semantic_bridge_eq, derived_request_singleton]
  responses_bridge := by
    rw [bridgeRecords, List.map_singleton,
      show cfg.challenges.α = Thm54P2Nonvacuity.cfg.challenges.α by rfl,
      show cfg.challenges.lam = Thm54P2Nonvacuity.cfg.challenges.lam by rfl,
      semantic_bridge_eq, derived_response_singleton]

theorem production_compute_rows_accepted : exec.ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff, execution_rows.1]
  intro row hrow
  simp only [List.mem_singleton] at hrow
  subst row
  exact ⟨rfl, rfl, compute_accepts⟩

theorem production_memory_rows_accepted : exec.MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff, execution_rows.2]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl, dummy_accepts, rfl⟩
  · exact ⟨rfl, rfl, read_accepts_p3, rfl⟩
  · exact ⟨rfl, rfl, decomp_accepts_p3, rfl⟩
  · exact ⟨rfl, rfl, head_accepts, rfl⟩
  · exact ⟨rfl, rfl, verify_accepts, rfl⟩
  · exact ⟨rfl, rfl, tail_accepts, rfl⟩

theorem production_semantic_exact :
    SemanticExactLanguage cfg exec :=
  ⟨production_compute_rows_accepted, production_memory_rows_accepted, ⟨semanticPreimage⟩⟩


theorem production_chained :
    ChainedSemanticExactLanguage cfg exec where
  semantic := production_semantic_exact
  z_ne_zero := by norm_num [cfg]
  compute_wf := by
    intro i
    rw [computePubAt_eq, challenge_alignment.1]
    exact compute_wf
  memory_wf := by
    intro i
    fin_cases i
    · rw [memoryPubAt_zero, challenge_alignment.2]
      exact dummy_wf
    · rw [memoryPubAt_one, challenge_alignment.2]
      exact read_wf_p3
    · rw [memoryPubAt_two, challenge_alignment.2]
      exact decomp_wf_p3
    · rw [memoryPubAt_three, challenge_alignment.2]
      exact head_wf
    · rw [memoryPubAt_four, challenge_alignment.2]
      exact verify_wf
    · rw [memoryPubAt_five, challenge_alignment.2]
      exact tail_wf
  compute_chain := by
    intro i hi
    fin_cases i
    norm_num [cfg] at hi
  memory_chain := by
    intro i hi
    fin_cases i
    · rw [memoryPubAt_zero, memoryPubAt_one]
      rfl
    · rw [memoryPubAt_one, memoryPubAt_two]
      rfl
    · rw [memoryPubAt_two, memoryPubAt_three]
      rfl
    · rw [memoryPubAt_three, memoryPubAt_four]
      rfl
    · rw [memoryPubAt_four, memoryPubAt_five]
      rfl
    · norm_num [cfg] at hi
  memory_first_counts := by
    rw [memoryPubAt_zero]
    rfl
  memory_first_indicator := by
    rw [memoryPubAt_zero]
    rfl
  memory_first_ipre := by
    rw [memoryPubAt_zero]
    rfl
  memory_last_icur := by
    have hlast :
        cfg.orbit.lastIndex cfg.memRows cfg.memRows_pos = ⟨5, by norm_num [cfg]⟩ := by
      rfl
    rw [hlast, memoryPubAt_five]
    rfl

  memory_same_lambda := ExactExecution.memory_same_lambda_of_const _ (some formRDefault) (by
    intro i
    fin_cases i
    · rw [memoryPubAt_zero]; rfl
    · rw [memoryPubAt_one]; rfl
    · rw [memoryPubAt_two]; rfl
    · rw [memoryPubAt_three]; rfl
    · rw [memoryPubAt_four]; rfl
    · rw [memoryPubAt_five]; rfl)

def acceptedExecution : ChainedAcceptedExecution cfg :=
  ⟨exec, production_chained⟩

theorem compute_exact_segmented_rap :
    ComputeExecutionSegmentedRAPSatisfies cfg exec :=
  production_chained.computeSegmentedRAP

theorem memory_exact_segmented_rap :
    MemoryExecutionSegmentedRAPSatisfies cfg exec :=
  production_chained.memorySegmentedRAP

theorem both_exact_segmented_rap_families :
    ComputeExecutionSegmentedRAPSatisfies cfg exec ∧
      MemoryExecutionSegmentedRAPSatisfies cfg exec :=
  production_chained.segmentedRAP

theorem accumulator_values :
    (pRead.ipre, pRead.icur, pDummy.icur, pDecomp.icur, pHead.icur,
      pVerify.icur, pTail.icur) = (0, 1, 0, 1, 1, 0, 0) := by
  rfl

#print axioms characteristic_gt_eleven
#print axioms omega2_order
#print axioms read_accepts_p3
#print axioms verify_accepts
#print axioms verify_pole_ne
#print axioms readTree_rvt_p3
#print axioms dummyTree_rvt
#print axioms execution_rows
#print axioms derived_request_singleton
#print axioms derived_response_singleton
#print axioms semantic_exponent_one
#print axioms shared_timestamp_is_alpha_one
#print axioms semanticPreimage
#print axioms production_semantic_exact
#print axioms production_chained
#print axioms acceptedExecution
#print axioms compute_exact_segmented_rap
#print axioms memory_exact_segmented_rap
#print axioms both_exact_segmented_rap_families

end

end Nock.RedTeam.Thm54P3Nonvacuity
