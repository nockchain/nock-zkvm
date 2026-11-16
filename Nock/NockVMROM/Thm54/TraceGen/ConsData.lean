/-
  Nock/NockVMROM/Thm54/TraceGen/ConsData.lean

  The assembled
  `ConsExecution : BuildableNockExecution (ZMod 97) (ZMod 97)` — all fourteen fields — and the
  directly-built literal-node commitment `HonestCommitment.Data ConsExecution` for the BRANCHING
  slice `*[0 [[1 5] [1 6]]] = [5 6]` over `K = ZMod 97`, `Λ = 4`, seed `z = 8`, `α = 4`.

  `ConsExecution` bundles the two semantic-CORE fields (`semanticData` from `ConsLanguage.lean`,
  `memoryTrace` — the `ExactServedMemoryTrace` assembled here from `ConsMemoryTrace`'s `rootTraces`)
  with the seven non-semantic fields (request-uniqueness, `M + 2L` record balance, finite-field
  range/nondegeneracy, and the two orbit IO-capacity bounds), all discharged directly on `cfg`/`exec`.

  The commitment supplies `computeNodes`/`memoryNodes` as literal node trees (NEVER via `dataOf`):
  the three-row compute tree (`.cons` autocons root over two `OP_1` children) and the thirteen-row
  memory reconstruction.  Their `skeletonOfNodes` is definitionally `ConsSkeleton.semanticSkeleton`,
  so the six census-closure obligations already discharged there (`slotSemantics`, `recordEquations`,
  `census`, `sizeWindowBound`, `skeletonBounded`, `combinedBounded`) are reused by `▸`-transport.
-/
import Nock.NockVMROM.Thm54.TraceGen.ConsLanguage
import Nock.NockVMROM.Thm54.TraceGen.ConsMemoryTrace
import Nock.NockVMROM.Thm54.BelowDefs.HonestCommitment
import Nock.NockVMROM.Thm54.ConcreteStrictPackage

namespace Nock.NockVMROM.Thm54.TraceGen.ConsConfig

open Nock Nock.Walk Nock.NockVM Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
  (ComputeTimestampSpecializesAt MemoryTimestampSpecializesAt)

noncomputable section

/-! ## A. The seven non-semantic `BuildableNockExecution` fields -/

/-- Records with distinct timestamps have distinct Form R encodings (slot `7` is `ts`). -/
theorem encRec_ne_of_ts_ne {r s : ComputeTable.MemRec F} (h : r.ts ≠ s.ts) :
    NockVM.encRecFormR r formRDefault ≠ NockVM.encRecFormR s formRDefault := by
  intro he
  exact h (by have hc := congrFun he (7 : Fin 9); change r.ts = s.ts at hc; exact hc)

/-- `requestNodup`: the three execution-derived requests are unique. -/
theorem requestNodup : exec.derivedRequestIO.Nodup := by
  rw [derived_requests]
  have h12 : NockVM.encRecFormR recCons formRDefault ≠ NockVM.encRecFormR recL formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recCons, ts_recL]; exact alpha_pow_ne_12)
  have h13 : NockVM.encRecFormR recCons formRDefault ≠ NockVM.encRecFormR recR formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recCons, ts_recR]; exact alpha_pow_ne_13)
  have h23 : NockVM.encRecFormR recL formRDefault ≠ NockVM.encRecFormR recR formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_recL, ts_recR]; exact alpha_pow_ne_23)
  simp [h12, h13, h23]

/-- Three `read_root` rows and three `verify_child` rows. -/
theorem memoryStateCounts :
    RowLayout.memoryStateCount exec .read_root = 3 ∧
      RowLayout.memoryStateCount exec .verify_child = 3 := by
  constructor <;>
    simp [RowLayout.memoryStateCount, RowLayout.fibreCount, memoryRows_eq,
      lblOf, pDummyHalt, pReadF, pDecF, pReadL, pReadR, pDecL, pVerifyF, pHaltL1, pVerifyL, pDecR,
      pHaltL5, pHaltR1, pVerifyR, pHaltR6, readPub, decPub, haltPub, verifyPub]

/-- `recordCountBalance`: one `verify_child` wrapper per `read_root` wrapper. -/
theorem recordCountBalance : RowLayout.RecordCountBalanced exec := by
  rw [RowLayout.RecordCountBalanced, memoryStateCounts.1, memoryStateCounts.2]

/-- `q_le_ringChar`: the Nat atom bound `q = 97` embeds without wraparound in `ZMod 97`. -/
theorem q_le_ringChar : (97 : ℕ) ≤ ringChar (ZMod 97) := by rw [ZMod.ringChar_zmod_n]

/-- `two_ne_zero`: the binary Nock-axis recurrence is nondegenerate over `ZMod 97`. -/
theorem two_ne_zero : (2 : ZMod 97) ≠ 0 := by decide

/-- `Ksz_lt_ringChar`: the IO count bound `Ksz = 4` is below the field characteristic. -/
theorem Ksz_lt_ringChar : cfg.Ksz < ringChar (ZMod 97) := by
  rw [ZMod.ringChar_zmod_n]; norm_num [cfg]

/-- `programIOCapacity`: the three requests' active prefix fits the `h = 4` orbit. -/
theorem programIOCapacity : exec.derivedRequestIO.length + 1 ≤ 2 ^ cfg.orbit.h := by
  rw [derived_requests]; norm_num [cfg, executionOrbit]

/-- `memoryIOCapacity`: the three responses' active prefix fits the `h = 4` orbit. -/
theorem memoryIOCapacity : exec.derivedResponseIO.length + 1 ≤ 2 ^ cfg.orbit.h := by
  rw [derived_responses]; norm_num [cfg, executionOrbit]

/-! ## B. The served memory trace

Every `.cons`/`OP_1` row of this slice has an empty `needs.served`, so `semanticCoverage` is
vacuous.  The remaining fields are `ConsMemoryTrace`'s aggregate timestamp facts. -/

/-- The census tuple of a served lookup, robust to `castRowData` transport. -/
def lookupTuple {z : F} (l : ServedNounLookup z) :
    ComputeTable.MemRec F × Noun × ℕ × Noun :=
  (l.record, l.root, l.axis, l.child)

theorem castRowData_servedTuples
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp F}
    (h : row₁ = row₂) (d : ComputeRowSemanticData 97 4 row₂) :
    (castRowData h d).needs.served.map lookupTuple = d.needs.served.map lookupTuple := by
  subst h; rfl

theorem rowData_zero_servedTuples :
    (rowData ⟨0, by norm_num [cfg]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAt_zero consRowData).trans rfl
theorem rowData_one_servedTuples :
    (rowData ⟨1, by norm_num [cfg]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAt_one op1LRowData).trans rfl
theorem rowData_two_servedTuples :
    (rowData ⟨2, by norm_num [cfg]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAt_two op1RRowData).trans rfl

/-- The cons slice's exact served memory trace. -/
def memoryTrace
    (hReadF : Vmem memInputs pReadF) (hDecF : Vmem memInputs pDecF)
    (hReadL : Vmem memInputs pReadL) (hReadR : Vmem memInputs pReadR)
    (hDecL : Vmem memInputs pDecL) (hVerifyF : Vmem memInputs pVerifyF)
    (hVerifyL : Vmem memInputs pVerifyL) (hDecR : Vmem memInputs pDecR)
    (hVerifyR : Vmem memInputs pVerifyR) :
    ExactServedMemoryTrace 97 4 cfg exec
      (semanticData hReadF hDecF hReadL hReadR hDecL hVerifyF hVerifyL hDecR hVerifyR) execA where
  roots := rootTraces
  timestampPowersNodup := forestTimestampPowers_nodup
  forestIndexRange := forestIndexRange
  semanticCoverage := by
    intro row lookup hlookup
    have hmem : lookupTuple lookup ∈ (rowData row).needs.served.map lookupTuple :=
      List.mem_map_of_mem hlookup
    fin_cases row
    · rw [rowData_zero_servedTuples] at hmem; simp at hmem
    · rw [rowData_one_servedTuples] at hmem; simp at hmem
    · rw [rowData_two_servedTuples] at hmem; simp at hmem

/-! ## C. The assembled buildable execution -/

/-- The cons slice's complete `BuildableNockExecution` — all fourteen fields explicitly named. -/
def ConsExecution
    (hReadF : Vmem memInputs pReadF) (hDecF : Vmem memInputs pDecF)
    (hReadL : Vmem memInputs pReadL) (hReadR : Vmem memInputs pReadR)
    (hDecL : Vmem memInputs pDecL) (hVerifyF : Vmem memInputs pVerifyF)
    (hVerifyL : Vmem memInputs pVerifyL) (hDecR : Vmem memInputs pDecR)
    (hVerifyR : Vmem memInputs pVerifyR) :
    BuildableNockExecution F F where
  q := 97
  q_gt_one := by norm_num
  Λ := 4
  cfg := cfg
  execA := execA
  exec := exec
  exec_encode := exec_encode
  semanticData := semanticData hReadF hDecF hReadL hReadR hDecL hVerifyF hVerifyL hDecR hVerifyR
  memoryTrace := memoryTrace hReadF hDecF hReadL hReadR hDecL hVerifyF hVerifyL hDecR hVerifyR
  requestNodup := requestNodup
  recordCountBalance := recordCountBalance
  q_le_ringChar := q_le_ringChar
  two_ne_zero := two_ne_zero
  Ksz_lt_ringChar := Ksz_lt_ringChar
  programIOCapacity := programIOCapacity
  memoryIOCapacity := memoryIOCapacity

/-! ## D. Row-skeleton bindings of the concrete rows -/

theorem bind_consRow : BindComputeRow seedZ ConsSkeleton.consRow consRow := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP,
        ConsSkeleton.consRow, consRow, consDec, enc]
  · intro i
    fin_cases i
    · rw [dif_pos (by decide)]
      intro slot
      cases slot <;>
        simp [ConsSkeleton.consRow, computeSubformulaFPs, ComputeTable.sfTriple, consRow,
          consPub, tripleFP, bindFP, enc]
    · rw [dif_pos (by decide)]
      intro slot
      cases slot <;>
        simp [ConsSkeleton.consRow, computeSubformulaFPs, ComputeTable.sfTriple, consRow,
          consPub, tripleFP, bindFP, enc]
    · rw [dif_neg (by decide)]
      simp [computeSubformulaFPs, ComputeTable.sfTriple, consRow, consPub]
  · intro i
    fin_cases i
    · rw [dif_pos (by decide)]
      exact ⟨rfl, rfl, rfl⟩
    · rw [dif_neg (by decide)]
      simp [computeMemRec, consRow, consPub, MemRec.zero]
    · rw [dif_neg (by decide)]
      simp [computeMemRec, consRow, consPub, MemRec.zero]

theorem bind_op1LRow : BindComputeRow seedZ ConsSkeleton.op1LRow op1LRow := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP,
        ConsSkeleton.op1LRow, op1LRow, op1DecOf, enc]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp ConsSkeleton.op1LRow.state) := by
      simp [ConsSkeleton.op1LRow, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, op1LRow, op1LPub, op1PubOf]
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, rfl⟩
    · rfl
    · rfl

theorem bind_op1RRow : BindComputeRow seedZ ConsSkeleton.op1RRow op1RRow := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP,
        ConsSkeleton.op1RRow, op1RRow, op1DecOf, enc]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp ConsSkeleton.op1RRow.state) := by
      simp [ConsSkeleton.op1RRow, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, op1RRow, op1RPub, op1PubOf]
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, rfl⟩
    · rfl
    · rfl

/-! ### Memory-row bindings -/

theorem bind_readFRow : BindMemoryRowA seedZ ConsSkeleton.readFRow (lblOf pReadFA) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [ConsSkeleton.readFRow, MemoryTable.fanoutMem, memoryChildCell, lblOf, pReadFA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decFRow : BindMemoryRowA seedZ ConsSkeleton.decFRow (lblOf pDecFA) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_readLRow : BindMemoryRowA seedZ ConsSkeleton.readLRow (lblOf pReadLA) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [ConsSkeleton.readLRow, MemoryTable.fanoutMem, memoryChildCell, lblOf, pReadLA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_readRRow : BindMemoryRowA seedZ ConsSkeleton.readRRow (lblOf pReadRA) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [ConsSkeleton.readRRow, MemoryTable.fanoutMem, memoryChildCell, lblOf, pReadRA, readPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decLRow : BindMemoryRowA seedZ ConsSkeleton.decLRow (lblOf pDecLA) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyFRow : BindMemoryRowA seedZ ConsSkeleton.verifyFRow (lblOf pVerifyFA) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [ConsSkeleton.verifyFRow, MemoryTable.fanoutMem, memoryChildCell, lblOf, pVerifyFA,
        verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_dummyHaltRow : BindMemoryRowA seedZ ConsSkeleton.dummyHaltRow (lblOf pDummyHaltA) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [ConsSkeleton.dummyHaltRow, lblOf, pDummyHaltA, haltPub, bindFP, enc,
      GlobalCarryRecognizer.enc_atom]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem ConsSkeleton.dummyHaltRow.state) := by
      simp [ConsSkeleton.dummyHaltRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_haltL1Row : BindMemoryRowA seedZ ConsSkeleton.haltL1Row (lblOf pHaltL1A) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [ConsSkeleton.haltL1Row, lblOf, pHaltL1A, haltPub, bindFP, enc, ConsSkeleton.op1Head,
      GlobalCarryRecognizer.enc_atom]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem ConsSkeleton.haltL1Row.state) := by
      simp [ConsSkeleton.haltL1Row, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyLRow : BindMemoryRowA seedZ ConsSkeleton.verifyLRow (lblOf pVerifyLA) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [ConsSkeleton.verifyLRow, MemoryTable.fanoutMem, memoryChildCell, lblOf, pVerifyLA,
        verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_decRRow : BindMemoryRowA seedZ ConsSkeleton.decRRow (lblOf pDecRA) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_haltL5Row : BindMemoryRowA seedZ ConsSkeleton.haltL5Row (lblOf pHaltL5A) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [ConsSkeleton.haltL5Row, lblOf, pHaltL5A, haltPub, bindFP, enc, ConsSkeleton.leftResult,
      GlobalCarryRecognizer.enc_atom]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem ConsSkeleton.haltL5Row.state) := by
      simp [ConsSkeleton.haltL5Row, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_haltR1Row : BindMemoryRowA seedZ ConsSkeleton.haltR1Row (lblOf pHaltR1A) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [ConsSkeleton.haltR1Row, lblOf, pHaltR1A, haltPub, bindFP, enc, ConsSkeleton.op1Head,
      GlobalCarryRecognizer.enc_atom]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem ConsSkeleton.haltR1Row.state) := by
      simp [ConsSkeleton.haltR1Row, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyRRow : BindMemoryRowA seedZ ConsSkeleton.verifyRRow (lblOf pVerifyRA) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [ConsSkeleton.verifyRRow, MemoryTable.fanoutMem, memoryChildCell, lblOf, pVerifyRA,
        verifyPub]
  · exact ⟨rfl, rfl, rfl⟩

theorem bind_haltR6Row : BindMemoryRowA seedZ ConsSkeleton.haltR6Row (lblOf pHaltR6A) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp [ConsSkeleton.haltR6Row, lblOf, pHaltR6A, haltPub, bindFP, enc, ConsSkeleton.rightResult,
      GlobalCarryRecognizer.enc_atom]
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem ConsSkeleton.haltR6Row.state) := by
      simp [ConsSkeleton.haltR6Row, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

/-! ## E. The literal committed node trees -/

def consComputeNode : ComputeNode F where
  skel := ConsSkeleton.consRow
  stamp := { state := .cons, lnPrevExponent := 0, lnExponent := 1, recordExponent := fun _ => 1 }
  row := consRow

def op1LComputeNode : ComputeNode F where
  skel := ConsSkeleton.op1LRow
  stamp := { state := .s1, lnPrevExponent := 1, lnExponent := 2, recordExponent := fun _ => 2 }
  row := op1LRow

def op1RComputeNode : ComputeNode F where
  skel := ConsSkeleton.op1RRow
  stamp := { state := .s1, lnPrevExponent := 2, lnExponent := 3, recordExponent := fun _ => 3 }
  row := op1RRow

def consComputeTree : NTree (ComputeNode F) :=
  .node consComputeNode [.node op1LComputeNode [], .node op1RComputeNode []]

def dummyHaltNode : MemoryNode F where
  skel := ConsSkeleton.dummyHaltRow
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf pDummyHaltA
def readFNode : MemoryNode F where
  skel := ConsSkeleton.readFRow
  stamp := { state := .read_root, recordExponent := 1 }
  row := lblOf pReadFA
def decFNode : MemoryNode F where
  skel := ConsSkeleton.decFRow
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf pDecFA
def readLNode : MemoryNode F where
  skel := ConsSkeleton.readLRow
  stamp := { state := .read_root, recordExponent := 2 }
  row := lblOf pReadLA
def readRNode : MemoryNode F where
  skel := ConsSkeleton.readRRow
  stamp := { state := .read_root, recordExponent := 3 }
  row := lblOf pReadRA
def decLNode : MemoryNode F where
  skel := ConsSkeleton.decLRow
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf pDecLA
def verifyFNode : MemoryNode F where
  skel := ConsSkeleton.verifyFRow
  stamp := { state := .verify_child, recordExponent := 1 }
  row := lblOf pVerifyFA
def haltL1Node : MemoryNode F where
  skel := ConsSkeleton.haltL1Row
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf pHaltL1A
def verifyLNode : MemoryNode F where
  skel := ConsSkeleton.verifyLRow
  stamp := { state := .verify_child, recordExponent := 2 }
  row := lblOf pVerifyLA
def decRNode : MemoryNode F where
  skel := ConsSkeleton.decRRow
  stamp := { state := .decompose, recordExponent := 0 }
  row := lblOf pDecRA
def haltL5Node : MemoryNode F where
  skel := ConsSkeleton.haltL5Row
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf pHaltL5A
def haltR1Node : MemoryNode F where
  skel := ConsSkeleton.haltR1Row
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf pHaltR1A
def verifyRNode : MemoryNode F where
  skel := ConsSkeleton.verifyRRow
  stamp := { state := .verify_child, recordExponent := 3 }
  row := lblOf pVerifyRA
def haltR6Node : MemoryNode F where
  skel := ConsSkeleton.haltR6Row
  stamp := { state := .halt, recordExponent := 0 }
  row := lblOf pHaltR6A

def dummyHaltMemTree : NTree (MemoryNode F) := .node dummyHaltNode []

/-- The committed memory node tree, matching `ConsConfig.rootTree`'s topology. -/
def consMemTree : NTree (MemoryNode F) :=
  .node readFNode
    [.node decFNode
      [.node readLNode
        [.node decLNode [.node haltL1Node [], .node verifyLNode [.node haltL5Node []]]],
       .node readRNode
        [.node verifyFNode
          [.node decRNode [.node haltR1Node [], .node verifyRNode [.node haltR6Node []]]]]]]

/-! ## F. Timestamp specialization of each concrete row -/

theorem cons_compute_specializes :
    ComputeTimestampSpecializesAt alphaA consComputeNode.stamp consRow := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show (consPub).ln_prev = alphaA ^ 0; simp [consPub]
  · show (consPub).ln = alphaA ^ 1; simp [consPub, pow_one]
  · intro i
    fin_cases i <;>
      simp [consComputeNode, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        consRow, consPub, recCons, MemRec.zero, pow_one]
  · intro i hi
    fin_cases i <;>
      simp_all [consComputeNode, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        consRow, consPub, MemRec.zero]

theorem op1L_compute_specializes :
    ComputeTimestampSpecializesAt alphaA op1LComputeNode.stamp op1LRow := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show (op1LPub).ln_prev = alphaA ^ 1; simp [op1LPub, op1PubOf, pow_one]
  · show (op1LPub).ln = alphaA ^ 2; simp [op1LPub, op1PubOf, pow_two]
  · intro i
    fin_cases i <;>
      simp [op1LComputeNode, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        op1LRow, op1LPub, op1PubOf, recL, MemRec.zero]
  · intro i hi
    fin_cases i <;>
      simp_all [op1LComputeNode, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        op1LRow, op1LPub, op1PubOf, MemRec.zero]

theorem op1R_compute_specializes :
    ComputeTimestampSpecializesAt alphaA op1RComputeNode.stamp op1RRow := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show (op1RPub).ln_prev = alphaA ^ 2; simp [op1RPub, op1PubOf, pow_two]
  · show (op1RPub).ln = alphaA ^ 3; simp [op1RPub, op1PubOf, pow_succ, pow_two]
  · intro i
    fin_cases i <;>
      simp [op1RComputeNode, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        op1RRow, op1RPub, op1PubOf, recR, MemRec.zero]
  · intro i hi
    fin_cases i <;>
      simp_all [op1RComputeNode, computeMemRec, computeMemRecKind, Nock.Framework.recordCount,
        op1RRow, op1RPub, op1PubOf, MemRec.zero]

theorem readF_specializes :
    MemoryTimestampSpecializesAt alphaA readFNode.stamp (lblOf pReadFA) :=
  ⟨rfl, rfl, by simp [readFNode, memoryMemRecKind, lblOf, pReadFA, readPub, recCons, pow_one],
    by simp [readFNode, memoryMemRecKind]⟩
theorem decF_specializes :
    MemoryTimestampSpecializesAt alphaA decFNode.stamp (lblOf pDecFA) :=
  ⟨rfl, rfl, by simp [decFNode, memoryMemRecKind, lblOf, pDecFA, decPub, MemRec.zero],
    by simp [decFNode, memoryMemRecKind, lblOf, pDecFA, decPub, MemRec.zero]⟩
theorem readL_specializes :
    MemoryTimestampSpecializesAt alphaA readLNode.stamp (lblOf pReadLA) :=
  ⟨rfl, rfl, by simp [readLNode, memoryMemRecKind, lblOf, pReadLA, readPub, recL],
    by simp [readLNode, memoryMemRecKind]⟩
theorem readR_specializes :
    MemoryTimestampSpecializesAt alphaA readRNode.stamp (lblOf pReadRA) :=
  ⟨rfl, rfl, by simp [readRNode, memoryMemRecKind, lblOf, pReadRA, readPub, recR],
    by simp [readRNode, memoryMemRecKind]⟩
theorem decL_specializes :
    MemoryTimestampSpecializesAt alphaA decLNode.stamp (lblOf pDecLA) :=
  ⟨rfl, rfl, by simp [decLNode, memoryMemRecKind, lblOf, pDecLA, decPub, MemRec.zero],
    by simp [decLNode, memoryMemRecKind, lblOf, pDecLA, decPub, MemRec.zero]⟩
theorem verifyF_specializes :
    MemoryTimestampSpecializesAt alphaA verifyFNode.stamp (lblOf pVerifyFA) :=
  ⟨rfl, rfl, by simp [verifyFNode, memoryMemRecKind, lblOf, pVerifyFA, verifyPub, recCons, pow_one],
    by simp [verifyFNode, memoryMemRecKind]⟩
theorem dummyHalt_specializes :
    MemoryTimestampSpecializesAt alphaA dummyHaltNode.stamp (lblOf pDummyHaltA) :=
  ⟨rfl, rfl, by simp [dummyHaltNode, memoryMemRecKind, lblOf, pDummyHaltA, haltPub, MemRec.zero],
    by simp [dummyHaltNode, memoryMemRecKind, lblOf, pDummyHaltA, haltPub, MemRec.zero]⟩
theorem haltL1_specializes :
    MemoryTimestampSpecializesAt alphaA haltL1Node.stamp (lblOf pHaltL1A) :=
  ⟨rfl, rfl, by simp [haltL1Node, memoryMemRecKind, lblOf, pHaltL1A, haltPub, MemRec.zero],
    by simp [haltL1Node, memoryMemRecKind, lblOf, pHaltL1A, haltPub, MemRec.zero]⟩
theorem verifyL_specializes :
    MemoryTimestampSpecializesAt alphaA verifyLNode.stamp (lblOf pVerifyLA) :=
  ⟨rfl, rfl, by simp [verifyLNode, memoryMemRecKind, lblOf, pVerifyLA, verifyPub, recL],
    by simp [verifyLNode, memoryMemRecKind]⟩
theorem decR_specializes :
    MemoryTimestampSpecializesAt alphaA decRNode.stamp (lblOf pDecRA) :=
  ⟨rfl, rfl, by simp [decRNode, memoryMemRecKind, lblOf, pDecRA, decPub, MemRec.zero],
    by simp [decRNode, memoryMemRecKind, lblOf, pDecRA, decPub, MemRec.zero]⟩
theorem haltL5_specializes :
    MemoryTimestampSpecializesAt alphaA haltL5Node.stamp (lblOf pHaltL5A) :=
  ⟨rfl, rfl, by simp [haltL5Node, memoryMemRecKind, lblOf, pHaltL5A, haltPub, MemRec.zero],
    by simp [haltL5Node, memoryMemRecKind, lblOf, pHaltL5A, haltPub, MemRec.zero]⟩
theorem haltR1_specializes :
    MemoryTimestampSpecializesAt alphaA haltR1Node.stamp (lblOf pHaltR1A) :=
  ⟨rfl, rfl, by simp [haltR1Node, memoryMemRecKind, lblOf, pHaltR1A, haltPub, MemRec.zero],
    by simp [haltR1Node, memoryMemRecKind, lblOf, pHaltR1A, haltPub, MemRec.zero]⟩
theorem verifyR_specializes :
    MemoryTimestampSpecializesAt alphaA verifyRNode.stamp (lblOf pVerifyRA) :=
  ⟨rfl, rfl, by simp [verifyRNode, memoryMemRecKind, lblOf, pVerifyRA, verifyPub, recR],
    by simp [verifyRNode, memoryMemRecKind]⟩
theorem haltR6_specializes :
    MemoryTimestampSpecializesAt alphaA haltR6Node.stamp (lblOf pHaltR6A) :=
  ⟨rfl, rfl, by simp [haltR6Node, memoryMemRecKind, lblOf, pHaltR6A, haltPub, MemRec.zero],
    by simp [haltR6Node, memoryMemRecKind, lblOf, pHaltR6A, haltPub, MemRec.zero]⟩

/-! ## G. Local node validity -/

theorem consComputeTree_OK :
    ComputeNodesOK seedZ alphaA consComputeTree := by
  refine ComputeNodesOK.mk' ⟨?_, rfl, bind_consRow, cons_compute_specializes⟩ ?_
  · simp [consComputeNode, ConsSkeleton.consRow, ComputeTable.fanoutComp]
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ComputeNodesOK.mk' ⟨by simp [op1LComputeNode, ConsSkeleton.op1LRow,
        ComputeTable.fanoutComp], rfl, bind_op1LRow, op1L_compute_specializes⟩ (by simp)
    · exact ComputeNodesOK.mk' ⟨by simp [op1RComputeNode, ConsSkeleton.op1RRow,
        ComputeTable.fanoutComp], rfl, bind_op1RRow, op1R_compute_specializes⟩ (by simp)

theorem dummyHaltMemTree_OK :
    MemoryNodesOK seedZ alphaA dummyHaltMemTree :=
  MemoryNodesOK.mk' ⟨rfl, rfl, bind_dummyHaltRow, dummyHalt_specializes⟩ (by simp)

theorem consMemTree_OK :
    MemoryNodesOK seedZ alphaA consMemTree := by
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readFRow, readF_specializes⟩ ?_
  intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decFRow, decF_specializes⟩ ?_
  intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · -- left branch: readL
    refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readLRow, readL_specializes⟩ ?_
    intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he
    refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decLRow, decL_specializes⟩ ?_
    intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltL1Row, haltL1_specializes⟩ (by simp)
    · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyLRow, verifyL_specializes⟩ ?_
      intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; subst hg
      exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltL5Row, haltL5_specializes⟩ (by simp)
  · -- right branch: readR
    refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_readRRow, readR_specializes⟩ ?_
    intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he
    refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyFRow, verifyF_specializes⟩ ?_
    intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf; subst hf
    refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_decRRow, decR_specializes⟩ ?_
    intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltR1Row, haltR1_specializes⟩ (by simp)
    · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_verifyRRow, verifyR_specializes⟩ ?_
      intro h hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh; subst hh
      exact MemoryNodesOK.mk' ⟨rfl, rfl, bind_haltR6Row, haltR6_specializes⟩ (by simp)

/-! ## H. The committed skeleton is exactly `ConsSkeleton.semanticSkeleton` -/

theorem skeletonOfNodes_eq :
    skeletonOfNodes consComputeTree [dummyHaltMemTree, consMemTree] =
      ConsSkeleton.semanticSkeleton := by
  simp [skeletonOfNodes, consComputeTree, dummyHaltMemTree, consMemTree, mapNTree,
    ConsSkeleton.semanticSkeleton, ConsSkeleton.computeTree, consComputeNode,
    op1LComputeNode, op1RComputeNode, dummyHaltNode,
    readFNode, decFNode, readLNode, readRNode, decLNode, verifyFNode, haltL1Node, verifyLNode,
    decRNode, haltL5Node, haltR1Node, verifyRNode, haltR6Node,
    ConsSkeleton.dummyHaltTree, ConsSkeleton.readFTree, ConsSkeleton.decFTree,
    ConsSkeleton.readLTree, ConsSkeleton.decLTree,
    ConsSkeleton.haltL1Tree, ConsSkeleton.verifyLTree, ConsSkeleton.haltL5Tree,
    ConsSkeleton.readRTree, ConsSkeleton.verifyFTree, ConsSkeleton.decRTree,
    ConsSkeleton.haltR1Tree, ConsSkeleton.verifyRTree, ConsSkeleton.haltR6Tree]

/-- The committed compute tree projects to `exec.computeTree`. -/
theorem cons_compute_rows :
    mapNTree ComputeNode.row consComputeTree = exec.computeTree := by
  simp [consComputeTree, consComputeNode, op1LComputeNode, op1RComputeNode, mapNTree, exec,
    computeTree]

/-- The committed memory forest projects to `exec.memoryForest`. -/
theorem cons_memory_rows :
    [dummyHaltMemTree, consMemTree].map (mapNTree MemoryNode.row) = execA.memoryForest := by
  simp [dummyHaltMemTree, dummyHaltNode, consMemTree, readFNode, decFNode, readLNode, readRNode,
    decLNode, verifyFNode, haltL1Node, verifyLNode, decRNode, haltL5Node, haltR1Node,
    verifyRNode, haltR6Node, mapNTree, exec, execA, tDummyHaltA, rootTreeA, tDecFA, tReadLA,
        tReadRA,
    tDecLA, tVerifyFA, tHaltL1A, tVerifyLA, tDecRA, tHaltL5A, tHaltR1A, tVerifyRA, tHaltR6A,
    mLeaf, mOne, mTwo]

/-! ## I. The honest commitment -/

/-- The directly-built honest commitment of the branching cons slice: the literal three-node
compute tree and thirteen-node memory tree, with all six census obligations transported from
`ConsSkeleton`. -/
def ConsData
    (hReadF : Vmem memInputs pReadF) (hDecF : Vmem memInputs pDecF)
    (hReadL : Vmem memInputs pReadL) (hReadR : Vmem memInputs pReadR)
    (hDecL : Vmem memInputs pDecL) (hVerifyF : Vmem memInputs pVerifyF)
    (hVerifyL : Vmem memInputs pVerifyL) (hDecR : Vmem memInputs pDecR)
    (hVerifyR : Vmem memInputs pVerifyR) :
    Data (ConsExecution hReadF hDecF hReadL hReadR hDecL hVerifyF hVerifyL hDecR hVerifyR) where
  computeNodes := consComputeTree
  memoryNodes := [dummyHaltMemTree, consMemTree]
  compute_rows := cons_compute_rows
  memory_rows := cons_memory_rows
  computeOK := consComputeTree_OK
  memoryOK := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact dummyHaltMemTree_OK
    · exact consMemTree_OK
  root_line_exponent := rfl
  root_line_origin := rfl
  nounSizeBound := 7
  Λ := 4
  slotSemantics := skeletonOfNodes_eq ▸ ConsSkeleton.slotSemantics
  recordEquations := skeletonOfNodes_eq ▸ ConsSkeleton.recordEquations
  census := skeletonOfNodes_eq ▸ ConsSkeleton.census
  sizeWindowBound := skeletonOfNodes_eq ▸ ConsSkeleton.sizeWindowBound
  q_eq_ringChar := by show (97 : ℕ) = ringChar F; rw [ZMod.ringChar_zmod_n]
  skeletonBounded := skeletonOfNodes_eq ▸ ConsSkeleton.skeletonBounded
  combinedBounded := skeletonOfNodes_eq ▸ ConsSkeleton.combinedBounded

/-- The committed skeleton this commitment derives is exactly the cons committed skeleton. -/
theorem ConsData_skeleton
    (hReadF : Vmem memInputs pReadF) (hDecF : Vmem memInputs pDecF)
    (hReadL : Vmem memInputs pReadL) (hReadR : Vmem memInputs pReadR)
    (hDecL : Vmem memInputs pDecL) (hVerifyF : Vmem memInputs pVerifyF)
    (hVerifyL : Vmem memInputs pVerifyL) (hDecR : Vmem memInputs pDecR)
    (hVerifyR : Vmem memInputs pVerifyR) :
    (ConsData hReadF hDecF hReadL hReadR hDecL hVerifyF hVerifyL hDecR hVerifyR).skeleton =
      ConsSkeleton.semanticSkeleton :=
  skeletonOfNodes_eq

end

end Nock.NockVMROM.Thm54.TraceGen.ConsConfig

#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.ConsExecution
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.memoryTrace
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.ConsData
