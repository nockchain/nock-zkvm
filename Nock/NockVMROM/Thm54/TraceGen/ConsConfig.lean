/-
  Nock/NockVMROM/Thm54/TraceGen/ConsConfig.lean

  The concrete `ExactConfig` and `ExactExecution` carriers of
  the fresh BRANCHING ROM program `*[0 [[1 5] [1 6]]] = [5 6]`, over `F = K = ZMod 97`.

  These are the two structural halves of the eventual `BuildableNockExecution (ZMod 97) (ZMod 97)`
  that carry no soundness/semantic obligation: `ExactConfig` is the shared challenge/orbit/domain
  data, and `ExactExecution` is the authoritative forest-first carrier — the
  three-row compute tree and
  the fourteen-row memory reconstruction of its three committed requests, in BFS order — whose only proof obligations are the tree BFS lengths.

  NEW vs OP1: the fourteen-row forest exceeds OP1's `2³ = 8` capacity, so the execution orbit needs
  exponent `h = 4` (capacity `2⁴ = 16`).  `8` has EXACT multiplicative order `16` in `ZMod 97`
  (`8⁸ = -1`), driving that orbit.  Constants (plan): seed `z = 8`, timestamp challenge `α = 4`,
  `a = b = c = 0`, memory challenges `β = γ = 0`, `compRows = 3`, `memRows = 14`, `kMem = 2`,
  `eDeg = 1`, `Ksz = 4`.  Form R at fixture `λ = 1` leaves the served read-root nonzero, so a
  halt seed row is prepended (`kMem = 2`) and `ChainedSemanticExactLanguage` still sees a zero
  first row.

  The three committed records carry the distinct timestamps `α, α², α³` (the compute line-number
  recurrence `ln(i) = ln(i-1)·α` over the three BFS compute rows), so the LogUp accumulator
  telescopes to zero over the forest, matched by fingerprint VALUE (memoryless, positionless).
  `ExactExecution` imposes no acceptance condition on these columns; their per-row AIR acceptance and
  the served two-request LogUp are the still-open `ExactExecutionSemanticData`/`ExactServedMemoryTrace`
  (see `ConsSkeleton`'s module header).
-/
import Nock.NockVMROM.Thm54.Execution
import Nock.GlobalCarryRecognizer
import Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.ConsConfig

open Nock Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton

/-- `ZMod 97` is a field. -/
instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- The slice base and table field coincide (`eDeg = 1`). -/
abbrev F : Type := ZMod 97

/-! ## The execution orbit -/

/-- `8` has exact multiplicative order sixteen in `ZMod 97` (`8⁸ = -1`), so it drives the
fourteen-row execution orbit of exponent `h = 4`. -/
theorem omega8_order : orderOf (8 : ZMod 97) = 16 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

/-- The fourteen-row exact execution orbit. -/
def executionOrbit : OrbitDomain F where
  h := 4
  ω := 8
  βcoset := 1
  βcoset_ne_zero := by norm_num
  order_ω := by simpa using omega8_order

/-! ## Constants and the seed-`z` encoder -/

/-- The concrete honest seed of the slice. -/
def seedZ : F := 8
/-- The timestamp challenge of the slice. -/
def alphaA : F := 4

theorem seedZ_ne_zero : seedZ ≠ 0 := by decide

/-- The seed-`z` fingerprint of a committed noun. -/
noncomputable def enc (n : Noun) : FP F := GlobalCarryRecognizer.enc seedZ n

noncomputable section

/-! ## The three committed memory records with distinct timestamps `α, α², α³` -/

/-- The `.cons` root's live record: opening the formula at axis `3`, timestamp `α`. -/
def recCons : MemRec F := ⟨enc formulaNoun, enc rightFormula, 3, alphaA⟩
/-- The left `OP_1` child's live record: opening `[1 5]` at axis `3`, timestamp `α²`. -/
def recL : MemRec F := ⟨enc leftFormula, enc leftResult, 3, alphaA ^ 2⟩
/-- The right `OP_1` child's live record: opening `[1 6]` at axis `3`, timestamp `α³`. -/
def recR : MemRec F := ⟨enc rightFormula, enc rightResult, 3, alphaA ^ 3⟩

/-! ## Table inputs -/

def compInputs : ComputeTable.Inputs F where
  α := alphaA
  z := seedZ
  a := 0
  b := 0
  c := 0

def memInputs : MemoryTable.Inputs F := ⟨seedZ, 0, 0⟩

/-! ## The three compute rows -/

/-- The `.cons` autocons compute row's decomposition: head `[1 5]`, tail `[1 6]`. -/
def consDec : ComputeTable.Dec F where
  f_h := enc leftFormula
  f_t := enc rightFormula
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

/-- The `.cons` autocons compute row: two subformula branches, one committed
record `recCons`, line-number `1 → α`. -/
def consPub : ComputeTable.Pub F where
  state := .cons
  s := enc subjectNoun
  f := enc formulaNoun
  e := enc resultNoun
  sf1_s := enc subjectNoun
  sf1_f := enc leftFormula
  sf1_e := enc leftResult
  sf2_s := enc subjectNoun
  sf2_f := enc rightFormula
  sf2_e := enc rightResult
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 1
  ln := alphaA
  mr1 := recCons
  mr2 := MemRec.zero
  mr3 := MemRec.zero

def consRow : ComputeTable.State × ComputeTable.DTcomp F := (.cons, (compInputs, consPub, consDec))

/-- Generic `OP_1` decomposition: head `1`, tail its constant result. -/
def op1DecOf (result : Noun) : ComputeTable.Dec F where
  f_h := enc op1Head
  f_t := enc result
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

/-- Generic `OP_1` public row, line-number `lnPrev → lnPrev·α`. -/
def op1PubOf (formula result : Noun) (lnPrev : F) (rec : MemRec F) : ComputeTable.Pub F where
  state := .s1
  s := enc subjectNoun
  f := enc formula
  e := enc result
  sf1_s := 0
  sf1_f := 0
  sf1_e := 0
  sf2_s := 0
  sf2_f := 0
  sf2_e := 0
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := lnPrev
  ln := lnPrev * alphaA
  mr1 := rec
  mr2 := MemRec.zero
  mr3 := MemRec.zero

def op1LPub : ComputeTable.Pub F := op1PubOf leftFormula leftResult alphaA recL
def op1RPub : ComputeTable.Pub F := op1PubOf rightFormula rightResult (alphaA ^ 2) recR

def op1LRow : ComputeTable.State × ComputeTable.DTcomp F := (.s1, (compInputs, op1LPub, op1DecOf leftResult))
def op1RRow : ComputeTable.State × ComputeTable.DTcomp F := (.s1, (compInputs, op1RPub, op1DecOf rightResult))

/-- The branching compute tree: `.cons` root over its two `OP_1` children (BFS: root, left, right). -/
def computeTree : NTree (ComputeTable.State × ComputeTable.DTcomp F) :=
  .node consRow [.node op1LRow [], .node op1RRow []]

/-! ## Generic memory-row shapes -/

abbrev MLbl := MemoryTable.MState × MemoryTable.DTmem F

def lblOf (pub : MemoryTable.Pub F) : MLbl := (pub.st, (memInputs, pub))

def haltPub (k : ℕ) (acc : F) : MemoryTable.Pub F where
  st := .halt
  pt := ⟨enc (.atom k), 0, 0⟩
  lc := MemoryTable.Cell.zero
  rc := MemoryTable.Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := acc
  icur := acc

def decPub (pt lc rc : MemoryTable.Cell F) (lcSt rcSt : MemoryTable.MState) (acc : F) :
    MemoryTable.Pub F where
  st := .decompose
  pt := pt
  lc := lc
  rc := rc
  lcSt := lcSt
  rcSt := rcSt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := acc
  icur := acc

def readPub (pt lc : MemoryTable.Cell F) (rec : MemRec F) (ipre icur : F) : MemoryTable.Pub F where
  st := .read_root
  pt := pt
  lc := lc
  rc := MemoryTable.Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := NockVM.formRRow rec MemoryTable.formRDefault
  cprime? := some (NockVM.formRCprime rec MemoryTable.formRDefault)
  lambda? := some MemoryTable.formRDefault
  ipre := ipre
  icur := icur

def verifyPub (pt lc : MemoryTable.Cell F) (rec : MemRec F) (ipre icur : F) : MemoryTable.Pub F where
  st := .verify_child
  pt := pt
  lc := lc
  rc := MemoryTable.Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := NockVM.formRRow rec MemoryTable.formRDefault
  cprime? := some (NockVM.formRCprime rec MemoryTable.formRDefault)
  lambda? := some MemoryTable.formRDefault
  ipre := ipre
  icur := icur

/-- The a-bearing `read_root` row. -/
@[simp] def readPubA (pt lc : MemoryTable.Cell F) (rec : MemRec F) (ipre icur : F) : MemoryTable.Pub
    F :=
  { readPub pt lc rec ipre icur with mem := rec, cprime? := none, lambda? := none }

/-- The a-bearing `verify_child` row; its row encode is `verifyPub`. -/
@[simp] def verifyPubA (pt lc : MemoryTable.Cell F) (rec : MemRec F) (ipre icur : F) :
    MemoryTable.Pub F :=
  { verifyPub pt lc rec ipre icur with mem := rec, cprime? := none, lambda? := none }

/-- The a-bearing (generator) `halt` row: no package `λ` written (`Gen.lean` emits none). -/
@[simp] def haltPubA (k : ℕ) (acc : F) : MemoryTable.Pub F := { haltPub k acc with lambda? := none }

/-- The a-bearing (generator) `decompose` row. -/
@[simp] def decPubA (pt lc rc : MemoryTable.Cell F) (lcSt rcSt : MemoryTable.MState) (acc : F) :
    MemoryTable.Pub F :=
  { decPub pt lc rc lcSt rcSt acc with lambda? := none }

/-! ## The three LogUp reciprocals -/

/-- With `β = γ = 0` the pole of a record is its root's fingerprint size.  Memory rows are
row-level (`BindMemRow`): they store `(T, C')` of the a-bearing record. -/
def qCons : F := (pole memInputs (NockVM.formRRow recCons MemoryTable.formRDefault)
    (NockVM.formRCprime recCons MemoryTable.formRDefault))⁻¹
def qL : F := (pole memInputs (NockVM.formRRow recL MemoryTable.formRDefault)
    (NockVM.formRCprime recL MemoryTable.formRDefault))⁻¹
def qR : F := (pole memInputs (NockVM.formRRow recR MemoryTable.formRDefault)
    (NockVM.formRCprime recR MemoryTable.formRDefault))⁻¹

/-! ## The thirteen memory-forest cells

Indicator/counts follow form R at fixture `λ = 1`, `C' = 1`
(`MemoryTable.eqBlk`): verify adds `ts` to both, read subtracts `axis·ts`
from both, decompose is `I_L+I_R` / `C_L+C_R+I_R`.  Derived bottom-up.
The read root is therefore not `(0,0)`; a halt seed row is prepended so
`ChainedSemanticExactLanguage` still sees a zero first row. -/

def cHaltL1 : MemoryTable.Cell F := ⟨enc op1Head, 0, 0⟩
def cHaltL5 : MemoryTable.Cell F := ⟨enc leftResult, 0, 0⟩
def cHaltR1 : MemoryTable.Cell F := ⟨enc op1Head, 0, 0⟩
def cHaltR6 : MemoryTable.Cell F := ⟨enc rightResult, 0, 0⟩
def cVerifyL : MemoryTable.Cell F := ⟨enc leftResult, alphaA ^ 2, 3 * alphaA ^ 2⟩
def cDecL : MemoryTable.Cell F := ⟨enc leftFormula, alphaA ^ 2, alphaA ^ 2⟩
def cReadL : MemoryTable.Cell F := ⟨enc leftFormula, 0, 0⟩
def cVerifyR : MemoryTable.Cell F := ⟨enc rightResult, alphaA ^ 3, 3 * alphaA ^ 3⟩
def cDecR : MemoryTable.Cell F := ⟨enc rightFormula, alphaA ^ 3, alphaA ^ 3⟩
def cVerifyF : MemoryTable.Cell F :=
  ⟨enc rightFormula, alphaA ^ 3 + alphaA, alphaA ^ 3 + 3 * alphaA⟩
def cReadR : MemoryTable.Cell F := ⟨enc rightFormula, alphaA, 3 * alphaA⟩
def cDecF : MemoryTable.Cell F := ⟨enc formulaNoun, alphaA, alphaA⟩
def cReadF : MemoryTable.Cell F := ⟨enc formulaNoun, 0, 0⟩

/-! ## The fourteen memory rows (halt seed + thirteen-row reconstruction) -/

def pDummyHalt : MemoryTable.Pub F := haltPub 0 0
def pReadF : MemoryTable.Pub F := readPub cReadF cDecF recCons 0 qCons
def pDecF : MemoryTable.Pub F := decPub cDecF cReadL cReadR .read_root .read_root qCons
def pReadL : MemoryTable.Pub F := readPub cReadL cDecL recL qCons (qCons + qL)
def pReadR : MemoryTable.Pub F := readPub cReadR cVerifyF recR (qCons + qL) (qCons + qL + qR)
def pDecL : MemoryTable.Pub F := decPub cDecL cHaltL1 cVerifyL .halt .verify_child (qCons + qL + qR)
def pVerifyF : MemoryTable.Pub F := verifyPub cVerifyF cDecR recCons (qCons + qL + qR) (qL + qR)
def pHaltL1 : MemoryTable.Pub F := haltPub 1 (qL + qR)
def pVerifyL : MemoryTable.Pub F := verifyPub cVerifyL cHaltL5 recL (qL + qR) qR
def pDecR : MemoryTable.Pub F := decPub cDecR cHaltR1 cVerifyR .halt .verify_child qR
def pHaltL5 : MemoryTable.Pub F := haltPub 5 qR
def pHaltR1 : MemoryTable.Pub F := haltPub 1 qR
def pVerifyR : MemoryTable.Pub F := verifyPub cVerifyR cHaltR6 recR qR 0
def pHaltR6 : MemoryTable.Pub F := haltPub 6 0

/-! The a-bearing view of the fourteen rows (same cells; records `(…, 3, ts)`; no `λ` written),
i.e. what the generator emits (`ConsGenMem`). -/

@[simp] def pDummyHaltA : MemoryTable.Pub F := haltPubA 0 0
@[simp] def pReadFA : MemoryTable.Pub F := readPubA cReadF cDecF recCons 0 qCons
@[simp] def pDecFA : MemoryTable.Pub F := decPubA cDecF cReadL cReadR .read_root .read_root qCons
@[simp] def pReadLA : MemoryTable.Pub F := readPubA cReadL cDecL recL qCons (qCons + qL)
@[simp] def pReadRA : MemoryTable.Pub F := readPubA cReadR cVerifyF recR (qCons + qL) (qCons + qL
    + qR)
@[simp] def pDecLA : MemoryTable.Pub F :=
  decPubA cDecL cHaltL1 cVerifyL .halt .verify_child (qCons + qL + qR)
@[simp] def pVerifyFA : MemoryTable.Pub F := verifyPubA cVerifyF cDecR recCons (qCons + qL + qR) (qL
    + qR)
@[simp] def pHaltL1A : MemoryTable.Pub F := haltPubA 1 (qL + qR)
@[simp] def pVerifyLA : MemoryTable.Pub F := verifyPubA cVerifyL cHaltL5 recL (qL + qR) qR
@[simp] def pDecRA : MemoryTable.Pub F := decPubA cDecR cHaltR1 cVerifyR .halt .verify_child qR
@[simp] def pHaltL5A : MemoryTable.Pub F := haltPubA 5 qR
@[simp] def pHaltR1A : MemoryTable.Pub F := haltPubA 1 qR
@[simp] def pVerifyRA : MemoryTable.Pub F := verifyPubA cVerifyR cHaltR6 recR qR 0
@[simp] def pHaltR6A : MemoryTable.Pub F := haltPubA 6 0

/-! ## The single serviced root -/

def mLeaf (pub : MemoryTable.Pub F) : NTree MLbl := .node (lblOf pub) []
def mOne (pub : MemoryTable.Pub F) (c : NTree MLbl) : NTree MLbl := .node (lblOf pub) [c]
def mTwo (pub : MemoryTable.Pub F) (l r : NTree MLbl) : NTree MLbl := .node (lblOf pub) [l, r]

def tDummyHalt : NTree MLbl := mLeaf pDummyHalt
def tHaltL1 : NTree MLbl := mLeaf pHaltL1
def tHaltL5 : NTree MLbl := mLeaf pHaltL5
def tVerifyL : NTree MLbl := mOne pVerifyL tHaltL5
def tDecL : NTree MLbl := mTwo pDecL tHaltL1 tVerifyL
def tReadL : NTree MLbl := mOne pReadL tDecL
def tHaltR1 : NTree MLbl := mLeaf pHaltR1
def tHaltR6 : NTree MLbl := mLeaf pHaltR6
def tVerifyR : NTree MLbl := mOne pVerifyR tHaltR6
def tDecR : NTree MLbl := mTwo pDecR tHaltR1 tVerifyR
def tVerifyF : NTree MLbl := mOne pVerifyF tDecR
def tReadR : NTree MLbl := mOne pReadR tVerifyF
def tDecF : NTree MLbl := mTwo pDecF tReadL tReadR
def rootTree : NTree MLbl := mOne pReadF tDecF

/-! The a-bearing served tree. -/

def tDummyHaltA : NTree MLbl := mLeaf pDummyHaltA
def tHaltL1A : NTree MLbl := mLeaf pHaltL1A
def tHaltL5A : NTree MLbl := mLeaf pHaltL5A
def tVerifyLA : NTree MLbl := mOne pVerifyLA tHaltL5A
def tDecLA : NTree MLbl := mTwo pDecLA tHaltL1A tVerifyLA
def tReadLA : NTree MLbl := mOne pReadLA tDecLA
def tHaltR1A : NTree MLbl := mLeaf pHaltR1A
def tHaltR6A : NTree MLbl := mLeaf pHaltR6A
def tVerifyRA : NTree MLbl := mOne pVerifyRA tHaltR6A
def tDecRA : NTree MLbl := mTwo pDecRA tHaltR1A tVerifyRA
def tVerifyFA : NTree MLbl := mOne pVerifyFA tDecRA
def tReadRA : NTree MLbl := mOne pReadRA tVerifyFA
def tDecFA : NTree MLbl := mTwo pDecFA tReadLA tReadRA
def rootTreeA : NTree MLbl := mOne pReadFA tDecFA

/-! ## The concrete configuration and execution -/

/-- The cons slice's shared configuration. -/
def cfg : ExactConfig F F where
  challenges := { a := 0, b := 0, c := 0, α := alphaA, z := seedZ, β := 0, γ := 0, lam := MemoryTable.formRDefault }
  Ksz := 4
  kMem := 2
  orbit := executionOrbit
  orbit_h_pos := by norm_num [executionOrbit]
  compRows := 3
  memRows := 14
  compRows_pos := by norm_num
  memRows_pos := by norm_num
  compRows_le := by norm_num [executionOrbit]
  memRows_le := by norm_num [executionOrbit]
  eDeg := 1
  eDeg_eq_one := rfl
  compNodes := fun i => executionOrbit.orbitPoint i
  compNodes_spec := by intro i; rfl
  memNodes := fun i => executionOrbit.orbitPoint i
  memNodes_spec := by intro i; rfl

/-- The fixture's configured `λ` is `formRDefault`. -/
@[simp] theorem cfg_lam : cfg.challenges.lam = MemoryTable.formRDefault := rfl

/-- The cons slice's authoritative forest-first execution: the three-row compute tree and the
fourteen-row memory reconstruction of its three requests (halt seed + served tree). -/
def exec : ExactExecution cfg where
  computeTree := computeTree
  memoryForest := [tDummyHalt, rootTree]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTree, bfsForest, NTree.size, totalSize, cfg]
  memory_bfs_length := by
    norm_num [tDummyHalt, rootTree, tDecF, tReadL, tReadR, tDecL, tVerifyF, tHaltL1, tVerifyL,
      tDecR, tHaltL5, tHaltR1, tVerifyR, tHaltR6, mOne, mTwo, mLeaf, bfsForest, NTree.size,
      totalSize, cfg]

/-- The a-bearing view of `exec`: same compute tree, memory records holding the
address. -/
def execA : ExactExecution cfg where
  computeTree := computeTree
  memoryForest := [tDummyHaltA, rootTreeA]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTree, bfsForest, NTree.size, totalSize, cfg]
  memory_bfs_length := by
    norm_num [tDummyHaltA, rootTreeA, tDecFA, tReadLA, tReadRA, tDecLA, tVerifyFA, tHaltL1A,
      tVerifyLA, tDecRA, tHaltL5A, tHaltR1A, tVerifyRA, tHaltR6A, mOne, mTwo, mLeaf, bfsForest,
      NTree.size, totalSize, cfg]

end

/-- The compute carrier is exactly three rows, the memory carrier exactly fourteen. -/
theorem exec_row_counts :
    exec.computeRows.length = 3 ∧ exec.memoryRows.length = 14 :=
  ⟨exec.computeRows_length, exec.memoryRows_length⟩

end Nock.NockVMROM.Thm54.TraceGen.ConsConfig

#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.exec
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.omega8_order
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.exec_row_counts
