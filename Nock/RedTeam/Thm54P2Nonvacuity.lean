import Nock.NockVMROM.Thm54.Language
import Nock.NockVM
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
This promoted fixture builds one accepted compute leaf and a four-row accepted memory tree
`read_root → decompose → (halt, halt)`.  The compute row emits one nonzero memory request; the
`read_root` row serves that exact record.  The authoritative extractors therefore both return the
same singleton encoded record.
-/

open scoped Classical

namespace Nock.RedTeam.Thm54P2Nonvacuity

noncomputable section

open Nock Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.Framework.Thm54

abbrev K17 := ZMod 17

instance prime17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-! ## Field and orbit -/

theorem char_valid_17 :
    ∀ n : ℕ, n ≤ 11 → (n : K17) = 1 → n = 1 := by
  intro n hn h
  change (n : ZMod 17) = ((1 : ℕ) : ZMod 17) at h
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [Nat.mod_eq_of_lt (by omega)] at h
  norm_num at h
  exact h

theorem omega4_order : orderOf (4 : K17) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

def orbit17 : OrbitDomain K17 where
  h := 2
  ω := 4
  βcoset := 1
  βcoset_ne_zero := by norm_num
  order_ω := by simpa using omega4_order

/-! ## Shared compute request -/

def headFP : FP K17 := FP.atomFP 1 1
def tailFP : FP K17 := FP.atomFP 1 2
noncomputable def rootFP : FP K17 := FP.cons 1 headFP tailFP

def sharedRecord : MemRec K17 where
  root := rootFP
  child := tailFP
  axis := 3
  ts := 4

/-- The row-level memory record (`BindMemRow`): `axis = T = λ^m` at `λ = formRDefault = 2`,
`m = Nat.size 3 − 1 = 1`. -/
def rowRecord : MemRec K17 where
  root := rootFP
  child := tailFP
  axis := 2
  ts := 4

/-- `C' = Cpoly(λ)` at `λ = 2`, `n − 1 = pwScaleExp K17 = 4`, bits of `3` MSB-first: `2^4 + 2^3`. -/
def rowC : K17 := 24

theorem pwScaleExp_K17 : pwScaleExp K17 = 4 := by
  rw [pwScaleExp_zmod]; decide

theorem nockAxisOf_three : nockAxisOf (3 : K17) = 3 := by
  have h := nockAxisOf_natCast (K := K17) (a := 3) (by rw [ZMod.ringChar_zmod_n]; norm_num)
  simpa using h

theorem formRT_shared : formRT (formRDefault : K17) 3 = 2 := by
  simp [formRT, formRDefault, formRCertShift_three]

theorem formRC_shared : formRC (formRDefault : K17) 3 = rowC := by
  rw [formRDefault, formRC_two_eq, pwScaleExp_K17]
  rw [show certSum 3 4 = 8 by decide]
  norm_num [rowC]

/-- The single Form R encode of the a-bearing compute record is the row-level memory record. -/
theorem formR_shared : encRecFormR sharedRecord formRDefault = encRecC rowRecord rowC := by
  have hax : nockAxisOf sharedRecord.axis = 3 := nockAxisOf_three
  unfold encRecFormR
  simp only [hax, formRT_shared, formRC_shared]
  rfl

theorem rootFP_value : rootFP = ⟨1, 1, 3⟩ := by
  ext <;> norm_num [rootFP, headFP, tailFP, FP.cons, FP.atomFP]

theorem sharedRecord_ne_zero : sharedRecord ≠ (MemRec.zero : MemRec K17) := by
  intro h
  have hd := congrArg (fun r : MemRec K17 => r.root.dyck) h
  norm_num [sharedRecord, MemRec.zero, rootFP_value] at hd

def cInp : ComputeTable.Inputs K17 where
  α := 4
  z := 1
  a := 0
  b := 0
  c := 0

noncomputable def cDec : ComputeTable.Dec K17 where
  f_h := headFP
  f_t := tailFP
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

noncomputable def cPub : ComputeTable.Pub K17 where
  state := .s1
  s := 0
  f := rootFP
  e := tailFP
  sf1_s := 0
  sf1_f := 0
  sf1_e := 0
  sf2_s := 0
  sf2_f := 0
  sf2_e := 0
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 1
  ln := 4
  mr1 := sharedRecord
  mr2 := MemRec.zero
  mr3 := MemRec.zero

theorem cPub_state : cPub.state = State.s1 := rfl

theorem compute_accepts : Vcomp cInp cPub cDec := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · ext <;> norm_num [cPub, sharedRecord, cInp, cDec]
  · simp [SVhead, headAtom, cPub, cDec, cInp, headFP, State.toNat]
  · norm_num [memBlk, cPub, cInp, MemRec.zero]
  · simp [evalV, sfz1, sfz2, sfz3, cPub, cDec]

theorem compute_wf : ComputeTable.WF cInp cPub where
  rlc5 := by simp [cPub]
  size8 := by simp [cPub]
  size11 := by simp [cPub]

theorem compute_RAP_accepts : ∃ ex, RAPcomp cInp cPub cDec ex :=
  (equiv_compute cInp cPub cDec compute_wf).mpr compute_accepts

theorem raw_requests_singleton :
    NockVM.activeRequestRecords cPub = [sharedRecord] := by
  simp [NockVM.activeRequestRecords, cPub]

/-! ## Accepted memory tree -/

def mInp : MemoryTable.Inputs K17 where
  z := 1
  β := 0
  γ := 0

def readCell : Cell K17 := ⟨rootFP, -(16 * 2 * 4), -(2 * 24 * 4)⟩
def decompCell : Cell K17 := ⟨rootFP, 0, 0⟩
def headCell : Cell K17 := ⟨headFP, 0, 0⟩
def tailCell : Cell K17 := ⟨tailFP, 0, 0⟩

noncomputable def readPub : MemoryTable.Pub K17 where
  st := .read_root
  pt := readCell
  lc := decompCell
  rc := Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := rowRecord
  cprime? := some rowC
  ipre := 0
  icur := 1

noncomputable def decompPub : MemoryTable.Pub K17 where
  st := .decompose
  pt := decompCell
  lc := headCell
  rc := tailCell
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  ipre := 0
  icur := 0

noncomputable def headHaltPub : MemoryTable.Pub K17 where
  st := .halt
  pt := headCell
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  ipre := 0
  icur := 0

noncomputable def tailHaltPub : MemoryTable.Pub K17 where
  st := .halt
  pt := tailCell
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  ipre := 0
  icur := 0

theorem read_state : readPub.st = MState.read_root := rfl
theorem decomp_state : decompPub.st = MState.decompose := rfl
theorem head_halt_state : headHaltPub.st = MState.halt := rfl
theorem tail_halt_state : tailHaltPub.st = MState.halt := rfl

theorem read_pole : pole mInp rowRecord rowC = 1 := by
  norm_num [pole, recRLC, mInp, rowRecord, rootFP_value]

theorem read_pole_ne : pole mInp rowRecord rowC ≠ 0 := by
  rw [read_pole]
  norm_num

theorem read_accepts : Vmem mInp readPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp only [eqBlk, readPub, readCell, decompCell, rowRecord, Pub.lambda, Pub.cprime,
      pwScaleExp_K17, Option.getD_some, Option.getD_none, rowC]
    norm_num
  · simp [interV, readPub, Pub.cprime]
    simpa [pole] using read_pole

theorem decomp_accepts : Vmem mInp decompPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_, rfl⟩
    · norm_num [decompPub, decompCell, headCell, tailCell]
    · norm_num [decompPub, decompCell, headCell, tailCell]
  · rfl

theorem head_halt_accepts : Vmem mInp headHaltPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · norm_num [eqBlk, headHaltPub, headCell, headFP, mInp, Cell.zero, MemRec.zero, FP.atomFP]
  · rfl

theorem tail_halt_accepts : Vmem mInp tailHaltPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · norm_num [eqBlk, tailHaltPub, tailCell, tailFP, mInp, Cell.zero, MemRec.zero, FP.atomFP]
  · rfl

theorem read_wf : MemoryTable.WF mInp readPub where
  pole_ne _ := by simpa [readPub, Pub.cprime] using read_pole_ne

theorem read_RAP_accepts : ∃ g, RAPmem mInp readPub g :=
  (equiv_mem mInp readPub read_wf).mpr read_accepts

theorem raw_responses_singleton :
    MemoryTable.responseRecords readPub = [rowRecord] := rfl

/-! ## Actual RVT carriers and exact configuration -/

def cLabel : State × ComputeTable.DTcomp K17 :=
  (.s1, (cInp, cPub, cDec))

def readLabel : MState × MemoryTable.DTmem K17 :=
  (.read_root, (mInp, readPub))

def decompLabel : MState × MemoryTable.DTmem K17 :=
  (.decompose, (mInp, decompPub))

def headHaltLabel : MState × MemoryTable.DTmem K17 :=
  (.halt, (mInp, headHaltPub))

def tailHaltLabel : MState × MemoryTable.DTmem K17 :=
  (.halt, (mInp, tailHaltPub))

def computeTree : NTree (State × ComputeTable.DTcomp K17) :=
  .node cLabel []

def headTree : NTree (MState × MemoryTable.DTmem K17) :=
  .node headHaltLabel []

def tailTree : NTree (MState × MemoryTable.DTmem K17) :=
  .node tailHaltLabel []

def decompTree : NTree (MState × MemoryTable.DTmem K17) :=
  .node decompLabel [headTree, tailTree]

def memoryTree : NTree (MState × MemoryTable.DTmem K17) :=
  .node readLabel [decompTree]

theorem computeLabel_accepts :
    ComputeTable.Fcomp cLabel (fun _ => none) := by
  refine ⟨rfl, compute_accepts, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp [cLabel, ComputeTable.fanoutComp]
  · intro i hi
    simp [cLabel, ComputeTable.fanoutComp] at hi

theorem computeTree_rvt : RVT (ComputeTable.Fcomp (K := K17)) computeTree := by
  unfold computeTree RVT
  exact ⟨computeLabel_accepts, by simp, ⟨fun _ => computeLabel_accepts, fun _ => rfl⟩⟩

theorem rvt_leaf {LT : Type*} {n : ℕ}
    {F : LT → (Fin n → Option LT) → Prop} {lbl : LT}
    (h : F lbl (fun _ => none)) : RVT F (.node lbl []) := by
  unfold RVT
  exact ⟨h, by simp, ⟨fun _ => h, fun _ => rfl⟩⟩

theorem headLabel_accepts :
    MemoryTable.Fmem headHaltLabel (fun _ => none) := by
  refine ⟨rfl, head_halt_accepts, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [headHaltLabel, MemoryTable.fanoutMem]
  · intro i hi
    simp [headHaltLabel, MemoryTable.fanoutMem] at hi

theorem tailLabel_accepts :
    MemoryTable.Fmem tailHaltLabel (fun _ => none) := by
  refine ⟨rfl, tail_halt_accepts, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [tailHaltLabel, MemoryTable.fanoutMem]
  · intro i hi
    simp [tailHaltLabel, MemoryTable.fanoutMem] at hi

def decompOut : Fin 2 → Option (MState × MemoryTable.DTmem K17)
  | 0 => some headHaltLabel
  | 1 => some tailHaltLabel

theorem decompLabel_accepts :
    MemoryTable.Fmem decompLabel decompOut := by
  refine ⟨rfl, decomp_accepts, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [decompLabel, decompOut, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i <;>
      simp [decompOut, MemoryTable.memCell, decompLabel,
        headHaltLabel, tailHaltLabel, decompPub, headHaltPub, tailHaltPub,
        headCell, tailCell]

def readOut : Fin 2 → Option (MState × MemoryTable.DTmem K17)
  | 0 => some decompLabel
  | 1 => none

theorem readLabel_accepts :
    MemoryTable.Fmem readLabel readOut := by
  refine ⟨rfl, read_accepts, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [readLabel, readOut, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i
    · simp [readOut, MemoryTable.memCell, readLabel,
        decompLabel, readPub, decompPub, decompCell]
    · simp [readLabel, MemoryTable.fanoutMem] at hi

theorem headTree_rvt : RVT (MemoryTable.Fmem (K := K17)) headTree := by
  exact rvt_leaf headLabel_accepts

theorem tailTree_rvt : RVT (MemoryTable.Fmem (K := K17)) tailTree := by
  exact rvt_leaf tailLabel_accepts

theorem decompTree_rvt : RVT (MemoryTable.Fmem (K := K17)) decompTree := by
  unfold decompTree RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 2 => (NTree.node decompLabel [headTree, tailTree]).childLabel i) =
        decompOut by
      funext i
      fin_cases i <;> rfl]
    exact decompLabel_accepts
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact headTree_rvt
    · exact tailTree_rvt
  · simp [NTree.isLeaf, MemoryTable.Fmem, decompLabel, MemoryTable.fanoutMem]

theorem memoryTree_rvt : RVT (MemoryTable.Fmem (K := K17)) memoryTree := by
  unfold memoryTree RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 2 => (NTree.node readLabel [decompTree]).childLabel i) =
        readOut by
      funext i
      fin_cases i <;> rfl]
    exact readLabel_accepts
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact decompTree_rvt
  · simp [NTree.isLeaf, MemoryTable.Fmem, readLabel, MemoryTable.fanoutMem]

def cfg : ExactConfig K17 K17 where
  challenges :=
    { a := 0, b := 0, c := 0, α := 4, z := 1, β := 0, γ := 0,
      lam := formRDefault }
  Ksz := 4
  kMem := 1
  orbit := orbit17
  orbit_h_pos := by norm_num [orbit17]
  compRows := 1
  memRows := 4
  compRows_pos := by norm_num
  memRows_pos := by norm_num
  compRows_le := by norm_num [orbit17]
  memRows_le := by norm_num [orbit17]
  eDeg := 1
  eDeg_eq_one := rfl
  compNodes := fun i => orbit17.orbitPoint i
  compNodes_spec := by intro i; rfl
  memNodes := fun i => orbit17.orbitPoint i
  memNodes_spec := by intro i; rfl

theorem challenge_alignment :
    cfg.challenges.computeInputs = cInp ∧ cfg.challenges.memoryInputs = mInp :=
  ⟨rfl, rfl⟩

def exec : ExactExecution cfg where
  computeTree := computeTree
  memoryForest := [memoryTree]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTree, bfsForest, NTree.size, totalSize, cfg]
  memory_bfs_length := by
    norm_num [memoryTree, decompTree, headTree, tailTree, bfsForest, NTree.size, totalSize, cfg]

theorem execution_rows :
    exec.computeRows = [cLabel] ∧
      exec.memoryRows = [readLabel, decompLabel, headHaltLabel, tailHaltLabel] := by
  constructor <;>
    norm_num [ExactExecution.computeRows, ExactExecution.memoryRows, exec, computeTree,
      memoryTree, decompTree, headTree, tailTree, bfsForest, NTree.size, totalSize]

/-! ## Authoritative row extractors -/

def compTrace : ℕ → State × ComputeTable.DTcomp K17 := fun _ => cLabel

def memTrace : ℕ → MState × MemoryTable.DTmem K17
  | 1 => readLabel
  | 2 => decompLabel
  | 3 => headHaltLabel
  | 4 => tailHaltLabel
  | _ => tailHaltLabel

theorem compTrace_matches_bfs :
    (List.range' 1 cfg.compRows).map compTrace = exec.computeRows := by
  rw [execution_rows.1]
  rfl

theorem memTrace_matches_bfs :
    (List.range' 1 cfg.memRows).map memTrace = exec.memoryRows := by
  rw [execution_rows.2]
  rfl

theorem extracted_requests :
    reqRecs compTrace cfg.compRows formRDefault = [encRecC rowRecord rowC] := by
  rw [reqRecs_eq_computeRows]
  simp [compTrace, cLabel, cfg, cPub, NockVM.activeRequestRecords, formR_shared]

theorem readPub_ver : readPub.ver = true := rfl
theorem decompPub_ver : decompPub.ver = false := rfl
theorem headHaltPub_ver : headHaltPub.ver = false := rfl
theorem tailHaltPub_ver : tailHaltPub.ver = false := rfl

theorem extracted_responses :
    respRecs memTrace cfg.memRows = [encRecC rowRecord rowC] := by
  have hr : List.range 4 = [0, 1, 2, 3] := by decide
  unfold respRecs
  simp only [memTrace, cfg]
  rw [hr]
  simp [readLabel, decompLabel, headHaltLabel, tailHaltLabel, readPub_ver,
    decompPub_ver, headHaltPub_ver, tailHaltPub_ver, Pub.cprime, encRecC,
    List.flatMap, List.map, readPub]

theorem extracted_equal :
    reqRecs compTrace cfg.compRows formRDefault = respRecs memTrace cfg.memRows := by
  rw [extracted_requests, extracted_responses]

theorem encoded_value :
    encRecC rowRecord rowC = ![1, 1, 3, 1, 0, 2, 2, 4, 24] := by
  funext i
  fin_cases i <;> norm_num [encRecC, rowRecord, rowC, rootFP_value, tailFP, FP.atomFP]

theorem request_nodup : (reqRecs compTrace cfg.compRows formRDefault).Nodup := by
  rw [extracted_requests]
  simp

theorem response_nodup : (respRecs memTrace cfg.memRows).Nodup := by
  rw [extracted_responses]
  simp

theorem requests_inRange :
    IO.InRange cfg.Ksz (reqRecs compTrace cfg.compRows formRDefault).length := by
  rw [extracted_requests]
  norm_num [IO.InRange, cfg]

theorem responses_inRange :
    IO.InRange cfg.Ksz (respRecs memTrace cfg.memRows).length := by
  rw [extracted_responses]
  norm_num [IO.InRange, cfg]

theorem Ksz_lt_char : cfg.Ksz < 17 := by norm_num [cfg]

theorem accepted_LmIO :
    IO.LmIO cfg.Ksz (reqRecs compTrace cfg.compRows formRDefault) (respRecs memTrace cfg.memRows) := by
  rw [extracted_requests, extracted_responses, IO.LmIO_iff]
  exact ⟨by norm_num [IO.InRange, cfg], by norm_num, by simp, by simp⟩

theorem accepted_LIO :
    IO.LIO cfg.Ksz (reqRecs compTrace cfg.compRows formRDefault) (respRecs memTrace cfg.memRows) := by
  rw [extracted_requests, extracted_responses]
  exact ⟨by norm_num [IO.InRange, cfg], by simp, List.Perm.refl _⟩

/-! ## Semantic preimage and bridge equality -/

def semanticRecord : (nmrMEF K17 K17).Rec :=
  (3,
    (((rootFP.size, rootFP.dyck, rootFP.leaf),
      (tailFP.size, tailFP.dyck, tailFP.leaf)),
    1))

/-- The semantic timestamp is the actual first memory-access exponent. -/
theorem semanticRecord_timestamp :
    semanticRecord.2.2 = 1 :=
  rfl

/-- The field timestamp is exactly the first power of the configured timestamp generator. -/
theorem sharedRecord_timestamp :
    sharedRecord.ts = cfg.challenges.α ^ semanticRecord.2.2 := by
  norm_num [sharedRecord, cfg, semanticRecord]

theorem semantic_preimage :
    memRecOfNMR K17 K17 ((nmrEncoding K17 K17 cfg.challenges.α).encode semanticRecord) =
      sharedRecord := by
  ext <;> norm_num [memRecOfNMR, nmrEncoding, semanticRecord, cfg, sharedRecord]

theorem semantic_bridge_eq :
    bridge K17 K17 cfg.challenges.α cfg.challenges.lam semanticRecord = encRecC rowRecord rowC := by
  rw [← d2_record_bridge_agrees]
  rw [semantic_preimage]
  exact formR_shared

theorem extracted_semantic_bridge :
    reqRecs compTrace cfg.compRows formRDefault =
        [bridge K17 K17 cfg.challenges.α cfg.challenges.lam semanticRecord] ∧
      respRecs memTrace cfg.memRows =
        [bridge K17 K17 cfg.challenges.α cfg.challenges.lam semanticRecord] := by
  constructor
  · rw [extracted_requests, semantic_bridge_eq]
  · rw [extracted_responses, semantic_bridge_eq]


set_option maxHeartbeats 400000 in
theorem derivedRequestIO_singleton :
    exec.derivedRequestIO = [encRecC rowRecord rowC] := by
  rw [ExactExecution.derivedRequestIO_eq_computeRows, execution_rows.1]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change (NockVM.activeRequestRecords cPub).map
      (fun r => encRecFormR r formRDefault) = [encRecC rowRecord rowC]
  rw [raw_requests_singleton, List.map_singleton, formR_shared]

set_option maxHeartbeats 400000 in
theorem derivedResponseIO_singleton :
    exec.derivedResponseIO = [encRecC rowRecord rowC] := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, execution_rows.2]
  have hr : List.range 4 = [0, 1, 2, 3] := by decide
  simp [readLabel, decompLabel, headHaltLabel, tailHaltLabel, readPub_ver,
    decompPub_ver, headHaltPub_ver, tailHaltPub_ver, Pub.cprime, encRecC, readPub]

theorem production_compute_rows_accepted : exec.ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff, execution_rows.1]
  simp [ExactExecution.ComputeRowAccepted, cLabel, challenge_alignment, compute_accepts,
    cPub_state]

theorem production_memory_rows_accepted : exec.MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff, execution_rows.2]
  simp [ExactExecution.MemoryRowAccepted, readLabel, decompLabel, headHaltLabel,
    tailHaltLabel, challenge_alignment, read_accepts, decomp_accepts,
    head_halt_accepts, tail_halt_accepts, read_state, decomp_state,
    head_halt_state, tail_halt_state]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem production_exactLanguage : ExactLanguage cfg exec :=
  ⟨production_compute_rows_accepted, production_memory_rows_accepted, by
    rw [derivedRequestIO_singleton, derivedResponseIO_singleton]
    simpa [extracted_requests, extracted_responses] using accepted_LmIO⟩

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
    rw [bridgeRecords, List.map_singleton, semantic_bridge_eq, derivedRequestIO_singleton]
  responses_bridge := by
    rw [bridgeRecords, List.map_singleton, semantic_bridge_eq, derivedResponseIO_singleton]

def semanticWitness : SemanticIOWitness cfg exec where
  toSemanticIOPreimage := semanticPreimage
  semanticRequests_nodup := by simp [semanticPreimage]

theorem production_semanticExactLanguage : SemanticExactLanguage cfg exec :=
  ⟨production_compute_rows_accepted, production_memory_rows_accepted, ⟨semanticPreimage⟩⟩

theorem production_semantic_implies_exactLanguage : ExactLanguage cfg exec :=
  production_semanticExactLanguage.toExactLanguage

theorem production_strongExactLanguage : StrongExactLanguage cfg exec :=
  semanticWitness.strongExactLanguage_of_semanticExactLanguage production_semanticExactLanguage

/-! ## Multiplicity regression for the final semantic language -/

/-- A second configuration with two accepted compute rows and the same one-row response set.
It exercises the base language's intended duplicate-request semantics. -/
def cfgDup : ExactConfig K17 K17 where
  challenges := cfg.challenges
  Ksz := 4
  kMem := 1
  orbit := orbit17
  orbit_h_pos := by norm_num [orbit17]
  compRows := 2
  memRows := 4
  compRows_pos := by norm_num
  memRows_pos := by norm_num
  compRows_le := by norm_num [orbit17]
  memRows_le := by norm_num [orbit17]
  eDeg := 1
  eDeg_eq_one := rfl
  compNodes := fun i => orbit17.orbitPoint i
  compNodes_spec := by intro i; rfl
  memNodes := fun i => orbit17.orbitPoint i
  memNodes_spec := by intro i; rfl

def computeTreeDup : NTree (State × ComputeTable.DTcomp K17) :=
  .node cLabel [.node cLabel []]

def execDup : ExactExecution cfgDup where
  computeTree := computeTreeDup
  memoryForest := [memoryTree]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTreeDup, bfsForest, NTree.size, totalSize, cfgDup]
  memory_bfs_length := by
    norm_num [memoryTree, decompTree, headTree, tailTree, bfsForest, NTree.size,
      totalSize, cfgDup]

theorem executionDup_rows :
    execDup.computeRows = [cLabel, cLabel] ∧
      execDup.memoryRows = [readLabel, decompLabel, headHaltLabel, tailHaltLabel] := by
  constructor <;>
    norm_num [ExactExecution.computeRows, ExactExecution.memoryRows, execDup, computeTreeDup,
      memoryTree, decompTree, headTree, tailTree, bfsForest, NTree.size, totalSize]

set_option maxHeartbeats 400000 in
theorem derivedRequestIO_duplicate :
    execDup.derivedRequestIO = [encRecC rowRecord rowC, encRecC rowRecord rowC] := by
  rw [ExactExecution.derivedRequestIO_eq_computeRows, executionDup_rows.1]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append]
  change (NockVM.activeRequestRecords cPub).map (fun r => encRecFormR r formRDefault) ++
      (NockVM.activeRequestRecords cPub).map (fun r => encRecFormR r formRDefault) =
    [encRecC rowRecord rowC, encRecC rowRecord rowC]
  rw [raw_requests_singleton, List.map_singleton, formR_shared]
  rfl

set_option maxHeartbeats 400000 in
theorem derivedResponseIO_duplicate :
    execDup.derivedResponseIO = [encRecC rowRecord rowC] := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, executionDup_rows.2]
  have hr : List.range 4 = [0, 1, 2, 3] := by decide
  simp [readLabel, decompLabel, headHaltLabel, tailHaltLabel, readPub_ver,
    decompPub_ver, headHaltPub_ver, tailHaltPub_ver, Pub.cprime, encRecC, readPub]

theorem productionDup_compute_rows_accepted : execDup.ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff, executionDup_rows.1]
  intro row hrow
  have : row = cLabel := by simpa using hrow
  subst row
  exact ⟨rfl, rfl, compute_accepts⟩

theorem productionDup_memory_rows_accepted : execDup.MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff, executionDup_rows.2]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl, read_accepts, rfl⟩
  · exact ⟨rfl, rfl, decomp_accepts, rfl⟩
  · exact ⟨rfl, rfl, head_halt_accepts, rfl⟩
  · exact ⟨rfl, rfl, tail_halt_accepts, rfl⟩

def semanticPreimageDup : SemanticIOPreimage cfgDup execDup where
  timestampBound := 2
  timestampBound_le_order := by norm_num [cfgDup, cfg, omega4_order]
  semanticRequests := [semanticRecord, semanticRecord]
  semanticResponses := [semanticRecord]
  requestTimestampBound := by
    intro r hr
    have : r = semanticRecord := by simpa using hr
    subst r
    norm_num [semanticRecord]
  responseTimestampBound := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    norm_num [semanticRecord]
  semantic_lmio := by
    rw [IO.LmIO_iff]
    exact ⟨by norm_num [IO.InRange, cfgDup], by simp, by simp, by simp⟩
  requestTimestamp_determines := by
    intro x hx y hy _
    have hx' : x = semanticRecord := by simpa using hx
    have hy' : y = semanticRecord := by simpa using hy
    rw [hx', hy']
  requests_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_singleton,
      show cfgDup.challenges.α = cfg.challenges.α by rfl,
      show cfgDup.challenges.lam = cfg.challenges.lam by rfl, semantic_bridge_eq,
      derivedRequestIO_duplicate]
  responses_bridge := by
    rw [bridgeRecords, List.map_singleton,
      show cfgDup.challenges.α = cfg.challenges.α by rfl,
      show cfgDup.challenges.lam = cfg.challenges.lam by rfl, semantic_bridge_eq,
      derivedResponseIO_duplicate]

/-- The final semantic base language admits the intended duplicate-request execution. -/
theorem productionDup_semanticExactLanguage :
    SemanticExactLanguage cfgDup execDup :=
  ⟨productionDup_compute_rows_accepted, productionDup_memory_rows_accepted,
    ⟨semanticPreimageDup⟩⟩

/-- The same execution is not in the uniqueness-strengthened language. -/
theorem productionDup_not_strongExactLanguage :
    ¬ StrongExactLanguage cfgDup execDup := by
  intro h
  have hlen := h.2.2.2.2.length_eq
  rw [derivedRequestIO_duplicate, derivedResponseIO_duplicate] at hlen
  norm_num at hlen

#print axioms char_valid_17
#print axioms omega4_order
#print axioms compute_accepts
#print axioms compute_RAP_accepts
#print axioms read_accepts
#print axioms read_pole_ne
#print axioms read_RAP_accepts
#print axioms computeTree_rvt
#print axioms memoryTree_rvt
#print axioms challenge_alignment
#print axioms execution_rows
#print axioms extracted_requests
#print axioms extracted_responses
#print axioms accepted_LmIO
#print axioms accepted_LIO
#print axioms semanticRecord_timestamp
#print axioms sharedRecord_timestamp
#print axioms semantic_preimage
#print axioms extracted_semantic_bridge
#print axioms production_exactLanguage
#print axioms semanticPreimage
#print axioms production_semanticExactLanguage
#print axioms production_semantic_implies_exactLanguage
#print axioms production_strongExactLanguage
#print axioms semanticWitness
#print axioms productionDup_semanticExactLanguage
#print axioms productionDup_not_strongExactLanguage

end
end Nock.RedTeam.Thm54P2Nonvacuity
