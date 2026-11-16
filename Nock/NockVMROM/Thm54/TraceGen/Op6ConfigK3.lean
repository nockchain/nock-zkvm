/-
  Nock/NockVMROM/Thm54/TraceGen/Op6ConfigK3.lean

  The `ExactConfig (ZMod 97) K3` and `ExactExecution` carriers for the fan-out-2
  branch (if) program

      `*[0 [6 [[1 0] [[1 5] [1 6]]]]] = 5`

  over base `F = ZMod 97` and the computable cubic table field `K = K3`.

  Compute tree (BFS: root, then two `OP_1` children, with shared-subject threading):

      s6 root  (subject 0, formula [6 [[1 0] [[1 5] [1 6]]]], eval 5)
     /       \
  child1:s1  child2:s1
  taken       cond
  (sub=0,    (sub=0,
   f=[1 5],   f=[1 0],
   eval=5)    eval=0)
  Parent sf1 = taken branch (child1), sf2 = condition (child2) per evalV.s6

  Memory forest: 23-row single-root tree for 5 records (parent: formula-open@3,
  formula-tail@2, branch-pair@2; child1: branchC@3, child2: condFormula@3).
  Cell children that are NOT record roots (condFormula via recT, branchD via recP)
  are decomposed to their atoms.
-/
import Nock.NockVMROM.Thm54.Execution
import Nock.GlobalCarryRecognizer
import Nock.NockVMROM.Thm54.TraceGen.Op6Gen
import Nock.NockVMROM.Thm54.TraceGen.CubicField97
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3

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
def op6Head : Noun := .atom 6

/-! ## The five committed memory records (3 parent + 2 children) -/

def recF (z α : K) : MemRec K := ⟨fp z op6ParentFormula, fp z op6ParentTail, 3, α⟩
def recT (z α : K) : MemRec K := ⟨fp z op6ParentTail, fp z op6CondFormula, 2, α ^ 2⟩
def recP (z α : K) : MemRec K := ⟨fp z op6BranchPair, fp z op6BranchC, 2, α ^ 3⟩
def recC1 (z α : K) : MemRec K := ⟨fp z op6BranchC, fp z op6Result, 3, α ^ 4⟩
def recC2 (z α : K) : MemRec K := ⟨fp z op6CondFormula, fp z op6CondResult, 3, α ^ 5⟩

/-! ## Table inputs -/

def compInputs (z α : K) : ComputeTable.Inputs K where
  α := α
  z := z
  a := 0
  b := 0
  c := 1

def memInputs (z : K) : MemoryTable.Inputs K := ⟨z, 0, 0⟩

/-! ## The three compute rows (`.s6` root + two `.s1` children) -/

def parentDec (z : K) : ComputeTable.Dec K where
  f_h := fp z op6Head
  f_t := fp z op6ParentTail
  f_th := fp z op6CondFormula
  f_tt := fp z op6BranchPair
  f_tth := fp z op6BranchC
  f_ttt := fp z op6BranchD

def parentPub (z α : K) : ComputeTable.Pub K where
  state := .s6
  s := fp z op6Subject
  f := fp z op6ParentFormula
  e := fp z op6Result
  sf1_s := fp z op6Subject
  sf1_f := fp z op6BranchC
  sf1_e := fp z op6Result
  sf2_s := fp z op6Subject
  sf2_f := fp z op6CondFormula
  sf2_e := fp z op6CondResult
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 1
  ln := α ^ 3
  mr1 := recF z α
  mr2 := recT z α
  mr3 := recP z α

def parentRow (z α : K) : ComputeTable.State × ComputeTable.DTcomp K :=
  (.s6, (compInputs z α, parentPub z α, parentDec z))

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
  op1PubOf z α op6Subject op6BranchC op6Result (α ^ 3) (recC1 z α)
def child2Pub (z α : K) : ComputeTable.Pub K :=
  op1PubOf z α op6Subject op6CondFormula op6CondResult (α ^ 4) (recC2 z α)

def child1Row (z α : K) : ComputeTable.State × ComputeTable.DTcomp K :=
  (.s1, (compInputs z α, child1Pub z α, op1DecOf z op6Result))
def child2Row (z α : K) : ComputeTable.State × ComputeTable.DTcomp K :=
  (.s1, (compInputs z α, child2Pub z α, op1DecOf z op6CondResult))

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

/-! ## The five LogUp reciprocals -/

def qF (z α : K) : K := (pole (memInputs z) (recF z α) 1)⁻¹
def qT (z α : K) : K := (pole (memInputs z) (recT z α) 1)⁻¹
def qP (z α : K) : K := (pole (memInputs z) (recP z α) 1)⁻¹
def qC1 (z α : K) : K := (pole (memInputs z) (recC1 z α) 1)⁻¹
def qC2 (z α : K) : K := (pole (memInputs z) (recC2 z α) 1)⁻¹

/-! ## The 23 memory-forest cells (form R) -/

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

def cHalt6 (z : K) : MemoryTable.Cell K := ⟨fp z (.atom 6), 0, 0⟩
def cHalt1_c2 (_z : K) : MemoryTable.Cell K := ⟨fp _z (.atom 1), 0, 0⟩
def cHalt0 (z : K) : MemoryTable.Cell K := ⟨fp z (.atom 0), 0, 0⟩
def cHalt1_c1 (_z : K) : MemoryTable.Cell K := ⟨fp _z (.atom 1), 0, 0⟩
def cHalt5 (z : K) : MemoryTable.Cell K := ⟨fp z (.atom 5), 0, 0⟩
def cHalt1_d (_z : K) : MemoryTable.Cell K := ⟨fp _z (.atom 1), 0, 0⟩
def cHalt6_d (z : K) : MemoryTable.Cell K := ⟨fp z (.atom 6), 0, 0⟩

def cVerifyC2 (z α : K) : MemoryTable.Cell K := cellVerify (fp z op6CondResult) (cHalt0 z) (α ^ 5)
def cDecC2 (z α : K) : MemoryTable.Cell K := cellDec (fp z op6CondFormula) (cHalt1_c2 z) (cVerifyC2 z α)
def cReadC2 (z α : K) : MemoryTable.Cell K := cellRead (fp z op6CondFormula) (cDecC2 z α) 3 (α ^ 5)

def cVerifyC1 (z α : K) : MemoryTable.Cell K := cellVerify (fp z op6Result) (cHalt5 z) (α ^ 4)
def cDecC1 (z α : K) : MemoryTable.Cell K := cellDec (fp z op6BranchC) (cHalt1_c1 z) (cVerifyC1 z α)
def cReadC1 (z α : K) : MemoryTable.Cell K := cellRead (fp z op6BranchC) (cDecC1 z α) 3 (α ^ 4)

def cDecBranchD (z α : K) : MemoryTable.Cell K :=
  cellDec (fp z op6BranchD) (cHalt1_d z) (cHalt6_d z)

def cVerifyP (z α : K) : MemoryTable.Cell K := cellVerify (fp z op6BranchC) (cReadC1 z α) (α ^ 3)
def cDecP (z α : K) : MemoryTable.Cell K := cellDec (fp z op6BranchPair) (cVerifyP z α) (cDecBranchD z α)
def cReadP (z α : K) : MemoryTable.Cell K := cellRead (fp z op6BranchPair) (cDecP z α) 2 (α ^ 3)

def cVerifyT (z α : K) : MemoryTable.Cell K := cellVerify (fp z op6CondFormula) (cReadC2 z α) (α ^ 2)
def cDecT (z α : K) : MemoryTable.Cell K := cellDec (fp z op6ParentTail) (cVerifyT z α) (cReadP z α)
def cReadT (z α : K) : MemoryTable.Cell K := cellRead (fp z op6ParentTail) (cDecT z α) 2 (α ^ 2)

def cVerifyF (z α : K) : MemoryTable.Cell K := cellVerify (fp z op6ParentTail) (cReadT z α) α
def cDecF (z α : K) : MemoryTable.Cell K := cellDec (fp z op6ParentFormula) (cHalt6 z) (cVerifyF z α)
def cReadF (z α : K) : MemoryTable.Cell K := cellRead (fp z op6ParentFormula) (cDecF z α) 3 α

/-! ## The 23 memory rows -/

def pReadF (z α : K) : MemoryTable.Pub K :=
  readPub z (cReadF z α) (cDecF z α) (recF z α) 0 (qF z α)
def pDecF (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecF z α) (cHalt6 z) (cVerifyF z α) .halt .verify_child (qF z α)
def pHalt6 (z α : K) : MemoryTable.Pub K := haltPub z 6 (qF z α)
def pVerifyF (z α : K) : MemoryTable.Pub K :=
  verifyPub z (cVerifyF z α) (cReadT z α) (recF z α) (qF z α) 0

def pReadT (z α : K) : MemoryTable.Pub K :=
  readPub z (cReadT z α) (cDecT z α) (recT z α) 0 (qT z α)
def pDecT (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecT z α) (cVerifyT z α) (cReadP z α) .verify_child .read_root (qT z α)
def pVerifyT (z α : K) : MemoryTable.Pub K :=
  verifyPub z (cVerifyT z α) (cReadC2 z α) (recT z α) (qT z α) 0

def pReadC2 (z α : K) : MemoryTable.Pub K :=
  readPub z (cReadC2 z α) (cDecC2 z α) (recC2 z α) (qP z α) (qP z α + qC2 z α)
def pDecC2 (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecC2 z α) (cHalt1_c2 z) (cVerifyC2 z α) .halt .verify_child (qP z α + qC2 z α)
def pHalt1_c2 (z α : K) : MemoryTable.Pub K := haltPub z 1 (qC2 z α)
def pVerifyC2 (z α : K) : MemoryTable.Pub K :=
  verifyPub z (cVerifyC2 z α) (cHalt0 z) (recC2 z α) (qC2 z α) 0
def pHalt0 (z α : K) : MemoryTable.Pub K := haltPub z 0 (qC1 z α)

def pReadP (z α : K) : MemoryTable.Pub K :=
  readPub z (cReadP z α) (cDecP z α) (recP z α) 0 (qP z α)
def pDecP (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecP z α) (cVerifyP z α) (cDecBranchD z α) .verify_child .decompose (qP z α + qC2 z α)
def pVerifyP (z α : K) : MemoryTable.Pub K :=
  verifyPub z (cVerifyP z α) (cReadC1 z α) (recP z α) (qP z α + qC2 z α) (qC2 z α)

def pReadC1 (z α : K) : MemoryTable.Pub K :=
  readPub z (cReadC1 z α) (cDecC1 z α) (recC1 z α) 0 (qC1 z α)
def pDecC1 (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecC1 z α) (cHalt1_c1 z) (cVerifyC1 z α) .halt .verify_child (qC1 z α)
def pHalt1_c1 (z α : K) : MemoryTable.Pub K := haltPub z 1 (qC1 z α)
def pVerifyC1 (z α : K) : MemoryTable.Pub K :=
  verifyPub z (cVerifyC1 z α) (cHalt5 z) (recC1 z α) (qC1 z α) 0
def pHalt5 (z _α : K) : MemoryTable.Pub K := haltPub z 5 0

/-! The a-bearing view of the active rows (same cells; record `(…, a, ts)`). -/

@[simp] def pReadFA (z α : K) : MemoryTable.Pub K :=
  readPubA z (cReadF z α) (cDecF z α) (recF z α) 0 (qF z α)
@[simp] def pVerifyFA (z α : K) : MemoryTable.Pub K :=
  verifyPubA z (cVerifyF z α) (cReadT z α) (recF z α) (qF z α) 0
@[simp] def pReadTA (z α : K) : MemoryTable.Pub K :=
  readPubA z (cReadT z α) (cDecT z α) (recT z α) 0 (qT z α)
@[simp] def pVerifyTA (z α : K) : MemoryTable.Pub K :=
  verifyPubA z (cVerifyT z α) (cReadC2 z α) (recT z α) (qT z α) 0
@[simp] def pReadC2A (z α : K) : MemoryTable.Pub K :=
  readPubA z (cReadC2 z α) (cDecC2 z α) (recC2 z α) (qP z α) (qP z α + qC2 z α)
@[simp] def pVerifyC2A (z α : K) : MemoryTable.Pub K :=
  verifyPubA z (cVerifyC2 z α) (cHalt0 z) (recC2 z α) (qC2 z α) 0
@[simp] def pReadPA (z α : K) : MemoryTable.Pub K :=
  readPubA z (cReadP z α) (cDecP z α) (recP z α) 0 (qP z α)
@[simp] def pVerifyPA (z α : K) : MemoryTable.Pub K :=
  verifyPubA z (cVerifyP z α) (cReadC1 z α) (recP z α) (qP z α + qC2 z α) (qC2 z α)
@[simp] def pReadC1A (z α : K) : MemoryTable.Pub K :=
  readPubA z (cReadC1 z α) (cDecC1 z α) (recC1 z α) 0 (qC1 z α)
@[simp] def pVerifyC1A (z α : K) : MemoryTable.Pub K :=
  verifyPubA z (cVerifyC1 z α) (cHalt5 z) (recC1 z α) (qC1 z α) 0

def pDecBranchD (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecBranchD z α) (cHalt1_d z) (cHalt6_d z) .halt .halt (qC2 z α)
def pHalt1_d (z α : K) : MemoryTable.Pub K := haltPub z 1 (qC1 z α)
def pHalt6_d (z α : K) : MemoryTable.Pub K := haltPub z 6 (qC1 z α)

/-! ## The memory forest tree -/

def mLeaf (z : K) (pub : MemoryTable.Pub K) : NTree MLbl := .node (lblOf z pub) []
def mOne (z : K) (pub : MemoryTable.Pub K) (c : NTree MLbl) : NTree MLbl :=
  .node (lblOf z pub) [c]
def mTwo (z : K) (pub : MemoryTable.Pub K) (l r : NTree MLbl) : NTree MLbl :=
  .node (lblOf z pub) [l, r]

def tHalt6 (z α : K) : NTree MLbl := mLeaf z (pHalt6 z α)

def tHalt5 (z α : K) : NTree MLbl := mLeaf z (pHalt5 z α)
def tHalt0 (z α : K) : NTree MLbl := mLeaf z (pHalt0 z α)
def tVerifyC2 (z α : K) : NTree MLbl := mOne z (pVerifyC2 z α) (tHalt0 z α)
def tHalt1_c2 (z α : K) : NTree MLbl := mLeaf z (pHalt1_c2 z α)
def tDecC2 (z α : K) : NTree MLbl := mTwo z (pDecC2 z α) (tHalt1_c2 z α) (tVerifyC2 z α)
def tReadC2 (z α : K) : NTree MLbl := mOne z (pReadC2 z α) (tDecC2 z α)
def tVerifyT (z α : K) : NTree MLbl := mOne z (pVerifyT z α) (tReadC2 z α)

def tVerifyC1 (z α : K) : NTree MLbl := mOne z (pVerifyC1 z α) (tHalt5 z α)
def tHalt1_c1 (z α : K) : NTree MLbl := mLeaf z (pHalt1_c1 z α)
def tDecC1 (z α : K) : NTree MLbl := mTwo z (pDecC1 z α) (tHalt1_c1 z α) (tVerifyC1 z α)
def tReadC1 (z α : K) : NTree MLbl := mOne z (pReadC1 z α) (tDecC1 z α)
def tVerifyP (z α : K) : NTree MLbl := mOne z (pVerifyP z α) (tReadC1 z α)

def tHalt6_d (z α : K) : NTree MLbl := mLeaf z (pHalt6_d z α)
def tHalt1_d (z α : K) : NTree MLbl := mLeaf z (pHalt1_d z α)
def tDecBranchD (z α : K) : NTree MLbl :=
  mTwo z (pDecBranchD z α) (tHalt1_d z α) (tHalt6_d z α)

def tDecP (z α : K) : NTree MLbl :=
  mTwo z (pDecP z α) (tVerifyP z α) (tDecBranchD z α)
def tReadP (z α : K) : NTree MLbl :=
  mOne z (pReadP z α) (tDecP z α)

def tDecT (z α : K) : NTree MLbl :=
  mTwo z (pDecT z α) (tVerifyT z α) (tReadP z α)
def tReadT (z α : K) : NTree MLbl :=
  mOne z (pReadT z α) (tDecT z α)

def tVerifyF (z α : K) : NTree MLbl :=
  mOne z (pVerifyF z α) (tReadT z α)
def tDecF (z α : K) : NTree MLbl :=
  mTwo z (pDecF z α) (tHalt6 z α) (tVerifyF z α)
def rootTree (z α : K) : NTree MLbl :=
  mOne z (pReadF z α) (tDecF z α)

/-! The a-bearing served tree (padding rows shared). -/

def tVerifyC2A (z α : K) : NTree MLbl := mOne z (pVerifyC2A z α) (tHalt0 z α)
def tDecC2A (z α : K) : NTree MLbl := mTwo z (pDecC2 z α) (tHalt1_c2 z α) (tVerifyC2A z α)
def tReadC2A (z α : K) : NTree MLbl := mOne z (pReadC2A z α) (tDecC2A z α)
def tVerifyTA (z α : K) : NTree MLbl := mOne z (pVerifyTA z α) (tReadC2A z α)
def tVerifyC1A (z α : K) : NTree MLbl := mOne z (pVerifyC1A z α) (tHalt5 z α)
def tDecC1A (z α : K) : NTree MLbl := mTwo z (pDecC1 z α) (tHalt1_c1 z α) (tVerifyC1A z α)
def tReadC1A (z α : K) : NTree MLbl := mOne z (pReadC1A z α) (tDecC1A z α)
def tVerifyPA (z α : K) : NTree MLbl := mOne z (pVerifyPA z α) (tReadC1A z α)
def tDecPA (z α : K) : NTree MLbl := mTwo z (pDecP z α) (tVerifyPA z α) (tDecBranchD z α)
def tReadPA (z α : K) : NTree MLbl := mOne z (pReadPA z α) (tDecPA z α)
def tDecTA (z α : K) : NTree MLbl := mTwo z (pDecT z α) (tVerifyTA z α) (tReadPA z α)
def tReadTA (z α : K) : NTree MLbl := mOne z (pReadTA z α) (tDecTA z α)
def tVerifyFA (z α : K) : NTree MLbl := mOne z (pVerifyFA z α) (tReadTA z α)
def tDecFA (z α : K) : NTree MLbl := mTwo z (pDecF z α) (tHalt6 z α) (tVerifyFA z α)
def rootTreeA (z α : K) : NTree MLbl := mOne z (pReadFA z α) (tDecFA z α)

/-! ## The concrete configuration and execution -/

def cfg (z α : K) : ExactConfig F K where
  challenges := { a := 0, b := 0, c := 1, α := α, z := z, β := 0, γ := 0, lam := MemoryTable.formRDefault }
  Ksz := 8
  kMem := 1
  orbit := executionOrbit
  orbit_h_pos := by norm_num [executionOrbit]
  compRows := 3
  memRows := 23
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
  memoryForest := [rootTree z α]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTree, bfsForest, NTree.size, totalSize, cfg]
  memory_bfs_length := by
    norm_num [rootTree, tDecF, tHalt6, tVerifyF, tReadT, tDecT, tVerifyT, tHalt5,
      tReadP, tDecP, tVerifyP, tReadC1, tDecC1, tHalt1_c1, tVerifyC1,
      tReadC2, tDecC2, tHalt1_c2, tVerifyC2, tHalt0,
      tDecBranchD, tHalt1_d, tHalt6_d,
      mOne, mTwo, mLeaf, bfsForest, NTree.size, totalSize, cfg]

/-- The a-bearing view of `exec`: same compute tree, memory records holding the address.  The
served memory trace and all axis accounting live here; `exec` is its row encode. -/
def execA (z α : K) : ExactExecution (cfg z α) where
  computeTree := computeTree z α
  memoryForest := [rootTreeA z α]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTree, bfsForest, NTree.size, totalSize, cfg]
  memory_bfs_length := by
    norm_num [rootTreeA, tDecFA, tHalt6, tVerifyFA, tReadTA, tDecTA, tVerifyTA, tHalt5,
      tReadPA, tDecPA, tVerifyPA, tReadC1A, tDecC1A, tHalt1_c1, tVerifyC1A,
      tReadC2A, tDecC2A, tHalt1_c2, tVerifyC2A, tHalt0,
      tDecBranchD, tHalt1_d, tHalt6_d,
      mOne, mTwo, mLeaf, bfsForest, NTree.size, totalSize, cfg]

end

def seedZ : K := 8
def alphaA : K := 4

theorem seedZ_eq_image : seedZ = φ (8 : F) := by rw [seedZ]; simp [map_ofNat]
theorem alphaA_eq_image : alphaA = φ (4 : F) := by rw [alphaA]; simp [map_ofNat]

theorem seedZ_ne_zero : seedZ ≠ 0 := by rw [seedZ]; decide

theorem exec_row_counts :
    (exec seedZ alphaA).computeRows.length = 3 ∧
      (exec seedZ alphaA).memoryRows.length = 23 :=
  ⟨(exec seedZ alphaA).computeRows_length, (exec seedZ alphaA).memoryRows_length⟩

end Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.exec
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.omega19_order
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op6ConfigK3.exec_row_counts
