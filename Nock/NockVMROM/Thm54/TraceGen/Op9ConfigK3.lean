/-
  Nock/NockVMROM/Thm54/TraceGen/Op9ConfigK3.lean

  The `ExactConfig (ZMod 97) K3` and `ExactExecution` carriers for the fan-out-2
  invoke program

      `*[0 [9 [2 [1 [[1 7] [1 9]]]]]] = 7`

  over base `F = ZMod 97` and the computable cubic table field `K = K3`.

  Compute tree (BFS: root, then two `OP_1` children):

      s9 root  (subject 0, formula [9 [2 [1 [[1 7][1 9]]]]], eval 7)
     /       \
  child1:s1  child2:s1
  core-eval  arm-eval
  (sub=0,    (sub=[[1 7][1 9]],
   f=[1 [[1 7][1 9]]],  f=[1 7],
   eval=[[1 7][1 9]])   eval=7)

  Memory forest: TWO roots (`kMem = 2`):
  * Root A (at parent formula): serves F (formula@3), T (tail@2), CoreF (coreFormula@3)
  * Root B (at computed core): serves Arm (core@2), ArmF (arm@3)
  Total: 5 served records with timestamps α,…,α⁵.
  Total memory rows: 30 (Root A = 19, Root B = 11).
-/
import Nock.NockVMROM.Thm54.Execution
import Nock.GlobalCarryRecognizer
import Nock.NockVMROM.Thm54.TraceGen.Op9Gen
import Nock.NockVMROM.Thm54.TraceGen.CubicField97
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3

open Nock Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.CubicField97

abbrev F : Type := ZMod 97
abbrev K : Type := CubicField97.K3
noncomputable abbrev φ : F →+* K := algebraMap F K
theorem φ_injective : Function.Injective φ := RingHom.injective φ

/-! ## The execution orbit over `K3` (`h = 5`, capacity `32`) -/

theorem omega19_order_base : orderOf (19 : F) = 32 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

theorem omega19_order : orderOf (φ (19 : F)) = 32 := by
  have h := orderOf_injective φ.toMonoidHom φ_injective (19 : F)
  rw [omega19_order_base] at h
  simpa using h

noncomputable def executionOrbit : OrbitDomain K where
  h := 5
  ω := φ (19 : F)
  βcoset := 1
  βcoset_ne_zero := one_ne_zero
  order_ω := by simpa using omega19_order

/-! ## Seed-dependent field rows -/

noncomputable section

noncomputable def fp (z : K) (n : Noun) : FP K := GlobalCarryRecognizer.enc z n

def op1Head : Noun := .atom 1
def op9Head : Noun := .atom 9

/-! ## The five committed memory records -/

def recF (z α : K) : MemRec K := ⟨fp z op9ParentFormula, fp z op9ParentTail, 3, α⟩
def recT (z α : K) : MemRec K := ⟨fp z op9ParentTail, fp z op9AxisAtom, 2, α ^ 2⟩
def recArm (z α : K) : MemRec K := ⟨fp z op9CoreNoun, fp z op9Arm, 2, α ^ 3⟩
def recCoreF (z α : K) : MemRec K := ⟨fp z op9CoreFormula, fp z op9CoreNoun, 3, α ^ 4⟩
def recArmF (z α : K) : MemRec K := ⟨fp z op9Arm, fp z op9Result, 3, α ^ 5⟩

/-! ## Table inputs -/

def compInputs (z α : K) : ComputeTable.Inputs K where
  α := α
  z := z
  a := 0
  b := 0
  c := 1

def memInputs (z : K) : MemoryTable.Inputs K := ⟨z, 0, 0⟩

/-! ## The three compute rows (`.s9` root + two `.s1` children) -/

def parentDec (z : K) : ComputeTable.Dec K where
  f_h := fp z op9Head
  f_t := fp z op9ParentTail
  f_th := fp z op9AxisAtom
  f_tt := fp z op9CoreFormula
  f_tth := 0
  f_ttt := 0

def parentPub (z α : K) : ComputeTable.Pub K where
  state := .s9
  s := fp z op9Subject
  f := fp z op9ParentFormula
  e := fp z op9Result
  sf1_s := fp z op9Subject
  sf1_f := fp z op9CoreFormula
  sf1_e := fp z op9CoreNoun
  sf2_s := fp z op9CoreNoun
  sf2_f := fp z op9Arm
  sf2_e := fp z op9Result
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 1
  ln := α ^ 3
  mr1 := recF z α
  mr2 := recT z α
  mr3 := recArm z α

def parentRow (z α : K) : ComputeTable.State × ComputeTable.DTcomp K :=
  (.s9, (compInputs z α, parentPub z α, parentDec z))

def op1DecOf (z : K) (result : Noun) : ComputeTable.Dec K where
  f_h := fp z op1Head
  f_t := fp z result
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

def op1PubOf (z α : K) (subject formula result : Noun) (lnPrev : K) (rec : MemRec K) :
    ComputeTable.Pub K where
  state := .s1
  s := fp z subject
  f := fp z formula
  e := fp z result
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
  ln := lnPrev * α
  mr1 := rec
  mr2 := MemRec.zero
  mr3 := MemRec.zero

def child1Pub (z α : K) : ComputeTable.Pub K :=
  op1PubOf z α op9Subject op9CoreFormula op9CoreNoun (α ^ 3) (recCoreF z α)
def child2Pub (z α : K) : ComputeTable.Pub K :=
  op1PubOf z α op9CoreNoun op9Arm op9Result (α ^ 4) (recArmF z α)

def child1Row (z α : K) : ComputeTable.State × ComputeTable.DTcomp K :=
  (.s1, (compInputs z α, child1Pub z α, op1DecOf z op9CoreNoun))
def child2Row (z α : K) : ComputeTable.State × ComputeTable.DTcomp K :=
  (.s1, (compInputs z α, child2Pub z α, op1DecOf z op9Result))

def computeTree (z α : K) : NTree (ComputeTable.State × ComputeTable.DTcomp K) :=
  .node (parentRow z α) [.node (child1Row z α) [], .node (child2Row z α) []]

/-! ## Memory-row shapes -/

abbrev MLbl := MemoryTable.MState × MemoryTable.DTmem K

def lblOf (z : K) (pub : MemoryTable.Pub K) : MLbl := (pub.st, (memInputs z, pub))

def haltPub (z : K) (k : ℕ) (acc : K) : MemoryTable.Pub K where
  st := .halt
  pt := ⟨fp z (.atom k), 0, 0⟩
  lc := MemoryTable.Cell.zero
  rc := MemoryTable.Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := acc
  icur := acc

def decPub (_z : K) (pt lc rc : MemoryTable.Cell K) (lcSt rcSt : MemoryTable.MState)
    (acc : K) : MemoryTable.Pub K where
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

def readPub (_z : K) (pt lc : MemoryTable.Cell K) (rec : MemRec K) (ipre icur : K) :
    MemoryTable.Pub K where
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

def verifyPub (_z : K) (pt lc : MemoryTable.Cell K) (rec : MemRec K) (ipre icur : K) :
    MemoryTable.Pub K where
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

@[simp] def readPubA (z : K) (pt lc : MemoryTable.Cell K) (rec : MemRec K) (ipre icur : K) :
    MemoryTable.Pub K :=
  { readPub z pt lc rec ipre icur with mem := rec, cprime? := none }

/-- The a-bearing `verify_child` row; its row encode is `verifyPub`. -/
@[simp] def verifyPubA (z : K) (pt lc : MemoryTable.Cell K) (rec : MemRec K) (ipre icur : K) :
    MemoryTable.Pub K :=
  { verifyPub z pt lc rec ipre icur with mem := rec, cprime? := none }

/-! ## Memory-forest cells

Each noun in the tree has up to three cell forms depending on state:
* Read cell: indicator = 0, counts = 0 (read nodes just pass through)
* Decompose cell: indicator = Σ(child indicators), counts per the recursion
* Verify cell: indicator = ts, counts = axis * ts
* Halt cells: always indicator = 0, counts = 0

Computed bottom-up from halts (all zero) through the tree.
Timestamps: recF=α, recT=α², recArm=α³, recCoreF=α⁴, recArmF=α⁵. -/

-- Form R row-level cells at the package `λ = formRDefault`: `verify_child` adds `λ^{n−1}·ts` to both
-- columns; `read_root` subtracts `λ^{n−1}·T·ts` / `T·C'·ts` with `(T, C')` of the record's Nock
-- axis; `decompose` is `λ(I_L+I_R)` / `C_L+C_R+(λ−1)(I_L+I_R)+I_R`.
@[simp] def cellVerify (noun : ComputeTable.FP K) (lc : MemoryTable.Cell K) (ts : K) :
    MemoryTable.Cell K :=
  ⟨noun, lc.indicator + MemoryTable.formRDefault ^ MemoryTable.pwScaleExp K * ts,
    lc.counts + MemoryTable.formRDefault ^ MemoryTable.pwScaleExp K * ts⟩
@[simp] def cellDec (noun : ComputeTable.FP K) (lc rc : MemoryTable.Cell K) :
    MemoryTable.Cell K :=
  ⟨noun, MemoryTable.formRDefault * (lc.indicator + rc.indicator),
    lc.counts + rc.counts + (MemoryTable.formRDefault - 1) * (lc.indicator + rc.indicator)
      + rc.indicator⟩
@[simp] def cellRead (noun : ComputeTable.FP K) (lc : MemoryTable.Cell K) (axis ts : K) :
    MemoryTable.Cell K :=
  ⟨noun, lc.indicator - MemoryTable.formRDefault ^ MemoryTable.pwScaleExp K *
      MemoryTable.formRT MemoryTable.formRDefault (MemoryTable.nockAxisOf axis) * ts,
    lc.counts - MemoryTable.formRT MemoryTable.formRDefault (MemoryTable.nockAxisOf axis) *
      MemoryTable.formRC MemoryTable.formRDefault (MemoryTable.nockAxisOf axis) * ts⟩

-- Halt-level cells (indicator = 0, counts = 0)
def cHead9 (z : K) : MemoryTable.Cell K := ⟨fp z op9Head, 0, 0⟩
def cHead1 (z : K) : MemoryTable.Cell K := ⟨fp z op1Head, 0, 0⟩
def cAxisAtom (z : K) : MemoryTable.Cell K := ⟨fp z op9AxisAtom, 0, 0⟩
def cResult (z : K) : MemoryTable.Cell K := ⟨fp z op9Result, 0, 0⟩

def cDecArmA (z : K) : MemoryTable.Cell K := cellDec (fp z op9Arm) (cHead1 z) (cResult z)
def cDecCTA (z : K) : MemoryTable.Cell K := cellDec (fp z op9CoreTail) (cHead1 z) (cHead9 z)
def cDecCN (z : K) : MemoryTable.Cell K := cellDec (fp z op9CoreNoun) (cDecArmA z) (cDecCTA z)
def cDecCT_B (z : K) : MemoryTable.Cell K := ⟨fp z op9CoreTail, 0, 0⟩

def cVerifyArmF (z α : K) : MemoryTable.Cell K := cellVerify (fp z op9Result) (cResult z) (α ^ 5)
def cDecArmB (z α : K) : MemoryTable.Cell K := cellDec (fp z op9Arm) (cHead1 z) (cVerifyArmF z α)
def cReadArmF (z α : K) : MemoryTable.Cell K := cellRead (fp z op9Arm) (cDecArmB z α) 3 (α ^ 5)

def cVerifyArm (z α : K) : MemoryTable.Cell K := cellVerify (fp z op9Arm) (cReadArmF z α) (α ^ 3)
def cDecCN_B (z α : K) : MemoryTable.Cell K := cellDec (fp z op9CoreNoun) (cVerifyArm z α) (cDecCT_B z)
def cReadArm (z α : K) : MemoryTable.Cell K := cellRead (fp z op9CoreNoun) (cDecCN_B z α) 2 (α ^ 3)

def cVerifyCoreF (z α : K) : MemoryTable.Cell K := cellVerify (fp z op9CoreNoun) (cDecCN z) (α ^ 4)
def cDecCF (z α : K) : MemoryTable.Cell K := cellDec (fp z op9CoreFormula) (cHead1 z) (cVerifyCoreF z α)
def cReadCoreF (z α : K) : MemoryTable.Cell K := cellRead (fp z op9CoreFormula) (cDecCF z α) 3 (α ^ 4)

def cVerifyT (z α : K) : MemoryTable.Cell K := cellVerify (fp z op9AxisAtom) (cAxisAtom z) (α ^ 2)
def cDecPT (z α : K) : MemoryTable.Cell K := cellDec (fp z op9ParentTail) (cVerifyT z α) (cReadCoreF z α)
def cReadT (z α : K) : MemoryTable.Cell K := cellRead (fp z op9ParentTail) (cDecPT z α) 2 (α ^ 2)

def cVerifyF (z α : K) : MemoryTable.Cell K := cellVerify (fp z op9ParentTail) (cReadT z α) α
def cDecPF (z α : K) : MemoryTable.Cell K := cellDec (fp z op9ParentFormula) (cHead9 z) (cVerifyF z α)
def cReadF (z α : K) : MemoryTable.Cell K := cellRead (fp z op9ParentFormula) (cDecPF z α) 3 α

/-! ## LogUp reciprocals -/

def qF (z α : K) : K := (pole (memInputs z) (recF z α) 1)⁻¹
def qT (z α : K) : K := (pole (memInputs z) (recT z α) 1)⁻¹
def qArm (z α : K) : K := (pole (memInputs z) (recArm z α) 1)⁻¹
def qCoreF (z α : K) : K := (pole (memInputs z) (recCoreF z α) 1)⁻¹
def qArmF (z α : K) : K := (pole (memInputs z) (recArmF z α) 1)⁻¹

/-! ## Root A: formula decomposition (19 nodes: 3 read, 3 verify, 6 decompose, 7 halt)

Subject: op9ParentFormula = cell (atom 9) (cell (atom 2) (cell (atom 1) (cell (cell (atom 1) (atom 7)) (cell (atom 1) (atom 9)))))
Services: F (formula@3), T (tail@2), CoreF (coreFormula@3)

BFS order (interleaved with Root B) determines the LogUp accumulator telescoping:
  readF(+qF), readArm(+qArm), decPF, decCN_B, halt9, verifyF(-qF), verifyArm(-qArm),
  decCT_B, readT(+qT), readArmF(+qArmF), haltH1_B2, haltA9_B, decPT, decArmB,
  verifyT(-qT), readCoreF(+qCoreF), haltH1_B1, verifyArmF(-qArmF), haltA2, decCF,
  haltA7_B, haltH1a, verifyCoreF(-qCoreF), decCN, decArmA, decCTA, haltH1b, haltA7,
  haltH1c, haltA9 -/

def pReadF (z α : K) : MemoryTable.Pub K :=
  readPub z (cReadF z α) (cDecPF z α) (recF z α) 0 (qF z α)
def pDecPF (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecPF z α) (cHead9 z) (cVerifyF z α) .halt .verify_child
    (qF z α + qArm z α)
def pHalt9 (z α : K) : MemoryTable.Pub K := haltPub z 9 (qF z α + qArm z α)
def pVerifyF (z α : K) : MemoryTable.Pub K :=
  verifyPub z (cVerifyF z α) (cReadT z α) (recF z α) (qF z α + qArm z α) (qArm z α)
def pReadT (z α : K) : MemoryTable.Pub K :=
  readPub z (cReadT z α) (cDecPT z α) (recT z α) 0 (qT z α)
def pDecPT (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecPT z α) (cVerifyT z α) (cReadCoreF z α) .verify_child .read_root
    (qT z α + qArmF z α)
def pVerifyT (z α : K) : MemoryTable.Pub K :=
  verifyPub z (cVerifyT z α) (cAxisAtom z) (recT z α) (qT z α + qArmF z α) (qArmF z α)
def pHaltA2 (z α : K) : MemoryTable.Pub K := haltPub z 2 (qCoreF z α)
def pReadCoreF (z α : K) : MemoryTable.Pub K :=
  readPub z (cReadCoreF z α) (cDecCF z α) (recCoreF z α) (qArmF z α) (qArmF z α + qCoreF z α)
def pDecCF (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecCF z α) (cHead1 z) (cVerifyCoreF z α) .halt .verify_child (qCoreF z α)
def pHaltH1a (z α : K) : MemoryTable.Pub K := haltPub z 1 (qCoreF z α)
def pVerifyCoreF (z α : K) : MemoryTable.Pub K :=
  verifyPub z (cVerifyCoreF z α) (cDecCN z) (recCoreF z α) (qCoreF z α) 0
def pDecCN (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecCN z) (cDecArmA z) (cDecCTA z) .decompose .decompose 0
@[simp] def pDecArmA (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecArmA z) (cHead1 z) (cResult z) .halt .halt 0
def pHaltH1b (z α : K) : MemoryTable.Pub K := haltPub z 1 0
def pHaltA7 (z α : K) : MemoryTable.Pub K := haltPub z 7 0
@[simp] def pDecCTA (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecCTA z) (cHead1 z) (cHead9 z) .halt .halt 0
def pHaltH1c (z α : K) : MemoryTable.Pub K := haltPub z 1 0
def pHaltA9 (z α : K) : MemoryTable.Pub K := haltPub z 9 0

/-! ## Root B: arm-fetch descent (11 nodes: 2 read, 2 verify, 3 decompose, 4 halt)

Subject: op9CoreNoun = cell (cell (atom 1) (atom 7)) (cell (atom 1) (atom 9))
Services: Arm (core@2), ArmF (arm@3) -/

def pReadArm (z α : K) : MemoryTable.Pub K :=
  readPub z (cReadArm z α) (cDecCN_B z α) (recArm z α) (qF z α) (qF z α + qArm z α)
def pDecCN_B (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecCN_B z α) (cVerifyArm z α) (cDecCT_B z) .verify_child .decompose
    (qF z α + qArm z α)
def pVerifyArm (z α : K) : MemoryTable.Pub K :=
  verifyPub z (cVerifyArm z α) (cReadArmF z α) (recArm z α) (qArm z α) 0
def pReadArmF (z α : K) : MemoryTable.Pub K :=
  readPub z (cReadArmF z α) (cDecArmB z α) (recArmF z α) (qT z α) (qT z α + qArmF z α)
def pDecArmB (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecArmB z α) (cHead1 z) (cVerifyArmF z α) .halt .verify_child
    (qT z α + qArmF z α)
def pHaltH1_B1 (z α : K) : MemoryTable.Pub K := haltPub z 1 (qArmF z α + qCoreF z α)
def pVerifyArmF (z α : K) : MemoryTable.Pub K :=
  verifyPub z (cVerifyArmF z α) (cResult z) (recArmF z α) (qArmF z α + qCoreF z α)
    (qCoreF z α)
def pHaltA7_B (z α : K) : MemoryTable.Pub K := haltPub z 7 (qCoreF z α)
def pDecCT_B (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecCT_B z) (cHead1 z) (cHead9 z) .halt .halt 0
def pHaltH1_B2 (z α : K) : MemoryTable.Pub K := haltPub z 1 (qT z α + qArmF z α)
def pHaltA9_B (z α : K) : MemoryTable.Pub K := haltPub z 9 (qT z α + qArmF z α)

/-! The a-bearing view of the active rows (same cells; record `(…, a, ts)`). -/

@[simp] def pReadFA (z α : K) : MemoryTable.Pub K :=
  readPubA z (cReadF z α) (cDecPF z α) (recF z α) 0 (qF z α)
@[simp] def pVerifyFA (z α : K) : MemoryTable.Pub K :=
  verifyPubA z (cVerifyF z α) (cReadT z α) (recF z α) (qF z α + qArm z α) (qArm z α)
@[simp] def pReadTA (z α : K) : MemoryTable.Pub K :=
  readPubA z (cReadT z α) (cDecPT z α) (recT z α) 0 (qT z α)
@[simp] def pVerifyTA (z α : K) : MemoryTable.Pub K :=
  verifyPubA z (cVerifyT z α) (cAxisAtom z) (recT z α) (qT z α + qArmF z α) (qArmF z α)
@[simp] def pReadCoreFA (z α : K) : MemoryTable.Pub K :=
  readPubA z (cReadCoreF z α) (cDecCF z α) (recCoreF z α) (qArmF z α) (qArmF z α + qCoreF z α)
@[simp] def pVerifyCoreFA (z α : K) : MemoryTable.Pub K :=
  verifyPubA z (cVerifyCoreF z α) (cDecCN z) (recCoreF z α) (qCoreF z α) 0
@[simp] def pReadArmA (z α : K) : MemoryTable.Pub K :=
  readPubA z (cReadArm z α) (cDecCN_B z α) (recArm z α) (qF z α) (qF z α + qArm z α)
@[simp] def pVerifyArmA (z α : K) : MemoryTable.Pub K :=
  verifyPubA z (cVerifyArm z α) (cReadArmF z α) (recArm z α) (qArm z α) 0
@[simp] def pReadArmFA (z α : K) : MemoryTable.Pub K :=
  readPubA z (cReadArmF z α) (cDecArmB z α) (recArmF z α) (qT z α) (qT z α + qArmF z α)
@[simp] def pVerifyArmFA (z α : K) : MemoryTable.Pub K :=
  verifyPubA z (cVerifyArmF z α) (cResult z) (recArmF z α) (qArmF z α + qCoreF z α)
    (qCoreF z α)

/-! ## Memory NTree assembly helpers -/

def mLeaf (z : K) (pub : MemoryTable.Pub K) : NTree MLbl :=
  .node (lblOf z pub) []
def mOne (z : K) (pub : MemoryTable.Pub K) (child : NTree MLbl) : NTree MLbl :=
  .node (lblOf z pub) [child]
def mTwo (z : K) (pub : MemoryTable.Pub K) (l r : NTree MLbl) : NTree MLbl :=
  .node (lblOf z pub) [l, r]

/-! ## Root A: 19-node formula tree -/

def rootTreeA (z α : K) : NTree MLbl :=
  mOne z (pReadF z α)
    (mTwo z (pDecPF z α)
      (mLeaf z (pHalt9 z α))
      (mOne z (pVerifyF z α)
        (mOne z (pReadT z α)
          (mTwo z (pDecPT z α)
            (mOne z (pVerifyT z α)
              (mLeaf z (pHaltA2 z α)))
            (mOne z (pReadCoreF z α)
              (mTwo z (pDecCF z α)
                (mLeaf z (pHaltH1a z α))
                (mOne z (pVerifyCoreF z α)
                  (mTwo z (pDecCN z α)
                    (mTwo z (pDecArmA z α)
                      (mLeaf z (pHaltH1b z α))
                      (mLeaf z (pHaltA7 z α)))
                    (mTwo z (pDecCTA z α)
                      (mLeaf z (pHaltH1c z α))
                      (mLeaf z (pHaltA9 z α)))))))))))

/-- The a-bearing view of `rootTreeA`. -/
def rootTreeAView (z α : K) : NTree MLbl :=
  mOne z (pReadFA z α)
    (mTwo z (pDecPF z α)
      (mLeaf z (pHalt9 z α))
      (mOne z (pVerifyFA z α)
        (mOne z (pReadTA z α)
          (mTwo z (pDecPT z α)
            (mOne z (pVerifyTA z α)
              (mLeaf z (pHaltA2 z α)))
            (mOne z (pReadCoreFA z α)
              (mTwo z (pDecCF z α)
                (mLeaf z (pHaltH1a z α))
                (mOne z (pVerifyCoreFA z α)
                  (mTwo z (pDecCN z α)
                    (mTwo z (pDecArmA z α)
                      (mLeaf z (pHaltH1b z α))
                      (mLeaf z (pHaltA7 z α)))
                    (mTwo z (pDecCTA z α)
                      (mLeaf z (pHaltH1c z α))
                      (mLeaf z (pHaltA9 z α)))))))))))

/-! ## Root B: 11-node arm-fetch tree -/

def rootTreeB (z α : K) : NTree MLbl :=
  mOne z (pReadArm z α)
    (mTwo z (pDecCN_B z α)
      (mOne z (pVerifyArm z α)
        (mOne z (pReadArmF z α)
          (mTwo z (pDecArmB z α)
            (mLeaf z (pHaltH1_B1 z α))
            (mOne z (pVerifyArmF z α)
              (mLeaf z (pHaltA7_B z α))))))
      (mTwo z (pDecCT_B z α)
        (mLeaf z (pHaltH1_B2 z α))
        (mLeaf z (pHaltA9_B z α))))

/-- The a-bearing view of `rootTreeB`. -/
def rootTreeBView (z α : K) : NTree MLbl :=
  mOne z (pReadArmA z α)
    (mTwo z (pDecCN_B z α)
      (mOne z (pVerifyArmA z α)
        (mOne z (pReadArmFA z α)
          (mTwo z (pDecArmB z α)
            (mLeaf z (pHaltH1_B1 z α))
            (mOne z (pVerifyArmFA z α)
              (mLeaf z (pHaltA7_B z α))))))
      (mTwo z (pDecCT_B z α)
        (mLeaf z (pHaltH1_B2 z α))
        (mLeaf z (pHaltA9_B z α))))

/-! ## The concrete configuration and execution -/

def cfg (z α : K) : ExactConfig F K where
  challenges := { a := 0, b := 0, c := 1, α := α, z := z, β := 0, γ := 0, lam := MemoryTable.formRDefault }
  Ksz := 8
  kMem := 2
  orbit := executionOrbit
  orbit_h_pos := by norm_num [executionOrbit]
  compRows := 3
  memRows := 30
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
@[simp] theorem cfg_lam (z α : K) : (cfg z α).challenges.lam = MemoryTable.formRDefault := rfl

def exec (z α : K) : ExactExecution (cfg z α) where
  computeTree := computeTree z α
  memoryForest := [rootTreeA z α, rootTreeB z α]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTree, bfsForest, NTree.size, totalSize, cfg]
  memory_bfs_length := by
    norm_num [rootTreeA, rootTreeB, mOne, mTwo, mLeaf, bfsForest, NTree.size, totalSize, cfg,
      pReadF, pDecPF, pHalt9, pVerifyF, pReadT, pDecPT, pVerifyT, pHaltA2,
      pReadCoreF, pDecCF, pHaltH1a, pVerifyCoreF, pDecCN, pDecArmA, pHaltH1b, pHaltA7,
      pDecCTA, pHaltH1c, pHaltA9,
      pReadArm, pDecCN_B, pVerifyArm, pReadArmF, pDecArmB, pHaltH1_B1, pVerifyArmF,
      pHaltA7_B, pDecCT_B, pHaltH1_B2, pHaltA9_B]

/-- The a-bearing view of `exec`: same compute tree, memory records holding the address.  The
served memory trace and all axis accounting live here; `exec` is its row encode. -/
def execA (z α : K) : ExactExecution (cfg z α) where
  computeTree := computeTree z α
  memoryForest := [rootTreeAView z α, rootTreeBView z α]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTree, bfsForest, NTree.size, totalSize, cfg]
  memory_bfs_length := by
    norm_num [rootTreeAView, rootTreeBView, mOne, mTwo, mLeaf, bfsForest, NTree.size, totalSize,
      cfg,
      pReadFA, pDecPF, pHalt9, pVerifyFA, pReadTA, pDecPT, pVerifyTA, pHaltA2,
      pReadCoreFA, pDecCF, pHaltH1a, pVerifyCoreFA, pDecCN, pDecArmA, pHaltH1b, pHaltA7,
      pDecCTA, pHaltH1c, pHaltA9,
      pReadArmA, pDecCN_B, pVerifyArmA, pReadArmFA, pDecArmB, pHaltH1_B1, pVerifyArmFA,
      pHaltA7_B, pDecCT_B, pHaltH1_B2, pHaltA9_B]

end

def seedZ : K := 8
def alphaA : K := 4

theorem seedZ_eq_image : seedZ = φ (8 : F) := by rw [seedZ]; simp [map_ofNat]
theorem alphaA_eq_image : alphaA = φ (4 : F) := by rw [alphaA]; simp [map_ofNat]

theorem seedZ_ne_zero : seedZ ≠ 0 := by rw [seedZ]; decide

end Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.cfg
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.exec
