/-
  Nock/NockVMROM/Thm54/TraceGen/Op8ConfigK3.lean

  The `ExactConfig (ZMod 97) K3` and `ExactExecution` carriers for the fan-out-2
  push program

      `*[0 [8 [[1 3] [1 5]]]] = 5`

  over base `F = ZMod 97` and the computable cubic table field `K = K3`.

  Compute tree (BFS: root, then two `OP_1` children, with autocons subject threading):

      s8 root  (subject 0, formula [8 [1 3] [1 5]], eval 5)
     /       \
  child1:s1  child2:s1
  helper     consumer
  (sub=0,    (sub=[3 0], AUTOCONS pushed subject [sb a],
   f=[1 3],   f=[1 5], eval=5)
   eval=3)
  Parent sf1 = consumer (child2), sf2 = helper (child1) per evalV.s8
-/
import Nock.NockVMROM.Thm54.Execution
import Nock.GlobalCarryRecognizer
import Nock.NockVMROM.Thm54.TraceGen.Op8Gen
import Nock.NockVMROM.Thm54.TraceGen.CubicField97
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.Op8ConfigK3

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
def op8Head : Noun := .atom 8

/-! ## The four committed memory records -/

def recF (z α : K) : MemRec K := ⟨fp z op8ParentFormula, fp z op8ParentTail, 3, α⟩
def recT (z α : K) : MemRec K := ⟨fp z op8ParentTail, fp z op8ChildFormulaB, 2, α ^ 2⟩
def recB (z α : K) : MemRec K := ⟨fp z op8ChildFormulaB, fp z op8Sb, 3, α ^ 4⟩
def recC (z α : K) : MemRec K := ⟨fp z op8ChildFormulaC, fp z op8Result, 3, α ^ 3⟩

/-! ## Table inputs -/

def compInputs (z α : K) : ComputeTable.Inputs K where
  α := α
  z := z
  a := 0
  b := 0
  c := 1

def memInputs (z : K) : MemoryTable.Inputs K := ⟨z, 0, 0⟩

/-! ## The three compute rows (`.s8` root + two `.s1` children) -/

def parentDec (z : K) : ComputeTable.Dec K where
  f_h := fp z op8Head
  f_t := fp z op8ParentTail
  f_th := fp z op8ChildFormulaB
  f_tt := fp z op8ChildFormulaC
  f_tth := 0
  f_ttt := 0

def parentPub (z α : K) : ComputeTable.Pub K where
  state := .s8
  s := fp z op8Subject
  f := fp z op8ParentFormula
  e := fp z op8Result
  sf1_s := fp z op8PushedSubject
  sf1_f := fp z op8ChildFormulaC
  sf1_e := fp z op8Result
  sf2_s := fp z op8Subject
  sf2_f := fp z op8ChildFormulaB
  sf2_e := fp z op8Sb
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 1
  ln := α ^ 2
  mr1 := recF z α
  mr2 := recT z α
  mr3 := MemRec.zero

def parentRow (z α : K) : ComputeTable.State × ComputeTable.DTcomp K :=
  (.s8, (compInputs z α, parentPub z α, parentDec z))

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
  op1PubOf z α op8Subject op8ChildFormulaB op8Sb (α ^ 3) (recB z α)
def child2Pub (z α : K) : ComputeTable.Pub K :=
  op1PubOf z α op8PushedSubject op8ChildFormulaC op8Result (α ^ 2) (recC z α)

def child1Row (z α : K) : ComputeTable.State × ComputeTable.DTcomp K :=
  (.s1, (compInputs z α, child1Pub z α, op1DecOf z op8Sb))
def child2Row (z α : K) : ComputeTable.State × ComputeTable.DTcomp K :=
  (.s1, (compInputs z α, child2Pub z α, op1DecOf z op8Result))

def computeTree (z α : K) : NTree (ComputeTable.State × ComputeTable.DTcomp K) :=
  .node (parentRow z α) [.node (child2Row z α) [], .node (child1Row z α) []]

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

/-! ## The four LogUp reciprocals -/

def qF (z α : K) : K := (pole (memInputs z) (recF z α) 1)⁻¹
def qT (z α : K) : K := (pole (memInputs z) (recT z α) 1)⁻¹
def qB (z α : K) : K := (pole (memInputs z) (recB z α) 1)⁻¹
def qC (z α : K) : K := (pole (memInputs z) (recC z α) 1)⁻¹

/-! ## The seventeen memory-forest cells (form R) -/

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

def cHalt3 (z : K) : MemoryTable.Cell K := ⟨fp z op8Sb, 0, 0⟩
def cVerifyB (z α : K) : MemoryTable.Cell K := cellVerify (fp z op8Sb) (cHalt3 z) (α ^ 4)
def cHaltB1 (z : K) : MemoryTable.Cell K := ⟨fp z op1Head, 0, 0⟩
def cDecB (z α : K) : MemoryTable.Cell K := cellDec (fp z op8ChildFormulaB) (cHaltB1 z) (cVerifyB z α)
def cReadB (z α : K) : MemoryTable.Cell K := cellRead (fp z op8ChildFormulaB) (cDecB z α) 3 (α ^ 4)

def cHalt5 (z : K) : MemoryTable.Cell K := ⟨fp z op8Result, 0, 0⟩
def cVerifyC (z α : K) : MemoryTable.Cell K := cellVerify (fp z op8Result) (cHalt5 z) (α ^ 3)
def cHaltC1 (z : K) : MemoryTable.Cell K := ⟨fp z op1Head, 0, 0⟩
def cDecC (z α : K) : MemoryTable.Cell K := cellDec (fp z op8ChildFormulaC) (cHaltC1 z) (cVerifyC z α)
def cReadC (z α : K) : MemoryTable.Cell K := cellRead (fp z op8ChildFormulaC) (cDecC z α) 3 (α ^ 3)

def cVerifyT (z α : K) : MemoryTable.Cell K := cellVerify (fp z op8ChildFormulaB) (cReadB z α) (α ^ 2)
def cDecT (z α : K) : MemoryTable.Cell K := cellDec (fp z op8ParentTail) (cVerifyT z α) (cReadC z α)
def cReadT (z α : K) : MemoryTable.Cell K := cellRead (fp z op8ParentTail) (cDecT z α) 2 (α ^ 2)

def cHalt8 (z : K) : MemoryTable.Cell K := ⟨fp z (.atom 8), 0, 0⟩
def cVerifyF (z α : K) : MemoryTable.Cell K := cellVerify (fp z op8ParentTail) (cReadT z α) α
def cDecF (z α : K) : MemoryTable.Cell K := cellDec (fp z op8ParentFormula) (cHalt8 z) (cVerifyF z α)
def cReadF (z α : K) : MemoryTable.Cell K := cellRead (fp z op8ParentFormula) (cDecF z α) 3 α

/-! ## The seventeen memory rows -/

def pReadF (z α : K) : MemoryTable.Pub K :=
  readPub z (cReadF z α) (cDecF z α) (recF z α) 0 (qF z α)
def pDecF (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecF z α) (cHalt8 z) (cVerifyF z α) .halt .verify_child (qF z α)
def pHalt8 (z α : K) : MemoryTable.Pub K := haltPub z 8 (qF z α)
def pVerifyF (z α : K) : MemoryTable.Pub K :=
  verifyPub z (cVerifyF z α) (cReadT z α) (recF z α) (qF z α) 0
def pReadT (z α : K) : MemoryTable.Pub K :=
  readPub z (cReadT z α) (cDecT z α) (recT z α) 0 (qT z α)
def pDecT (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecT z α) (cVerifyT z α) (cReadC z α) .verify_child .read_root (qT z α)
def pVerifyT (z α : K) : MemoryTable.Pub K :=
  verifyPub z (cVerifyT z α) (cReadB z α) (recT z α) (qT z α) 0
def pReadC (z α : K) : MemoryTable.Pub K :=
  readPub z (cReadC z α) (cDecC z α) (recC z α) 0 (qC z α)
def pReadB (z α : K) : MemoryTable.Pub K :=
  readPub z (cReadB z α) (cDecB z α) (recB z α) (qC z α) (qC z α + qB z α)
def pDecC (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecC z α) (cHaltC1 z) (cVerifyC z α) .halt .verify_child (qC z α + qB z α)
def pDecB (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecB z α) (cHaltB1 z) (cVerifyB z α) .halt .verify_child (qC z α + qB z α)
def pHaltC1 (z α : K) : MemoryTable.Pub K := haltPub z 1 (qC z α + qB z α)
def pVerifyC (z α : K) : MemoryTable.Pub K :=
  verifyPub z (cVerifyC z α) (cHalt5 z) (recC z α) (qC z α + qB z α) (qB z α)
def pHaltB1 (z α : K) : MemoryTable.Pub K := haltPub z 1 (qB z α)
def pVerifyB (z α : K) : MemoryTable.Pub K :=
  verifyPub z (cVerifyB z α) (cHalt3 z) (recB z α) (qB z α) 0
def pHalt5 (z _α : K) : MemoryTable.Pub K := haltPub z 5 0
def pHalt3 (z _α : K) : MemoryTable.Pub K := haltPub z 3 0

/-! The a-bearing view of the active rows (same cells; record `(…, a, ts)`). -/

@[simp] def pReadFA (z α : K) : MemoryTable.Pub K :=
  readPubA z (cReadF z α) (cDecF z α) (recF z α) 0 (qF z α)
@[simp] def pVerifyFA (z α : K) : MemoryTable.Pub K :=
  verifyPubA z (cVerifyF z α) (cReadT z α) (recF z α) (qF z α) 0
@[simp] def pReadTA (z α : K) : MemoryTable.Pub K :=
  readPubA z (cReadT z α) (cDecT z α) (recT z α) 0 (qT z α)
@[simp] def pVerifyTA (z α : K) : MemoryTable.Pub K :=
  verifyPubA z (cVerifyT z α) (cReadB z α) (recT z α) (qT z α) 0
@[simp] def pReadCA (z α : K) : MemoryTable.Pub K :=
  readPubA z (cReadC z α) (cDecC z α) (recC z α) 0 (qC z α)
@[simp] def pReadBA (z α : K) : MemoryTable.Pub K :=
  readPubA z (cReadB z α) (cDecB z α) (recB z α) (qC z α) (qC z α + qB z α)
@[simp] def pVerifyCA (z α : K) : MemoryTable.Pub K :=
  verifyPubA z (cVerifyC z α) (cHalt5 z) (recC z α) (qC z α + qB z α) (qB z α)
@[simp] def pVerifyBA (z α : K) : MemoryTable.Pub K :=
  verifyPubA z (cVerifyB z α) (cHalt3 z) (recB z α) (qB z α) 0

/-! ## The memory forest tree -/

def mLeaf (z : K) (pub : MemoryTable.Pub K) : NTree MLbl := .node (lblOf z pub) []
def mOne (z : K) (pub : MemoryTable.Pub K) (c : NTree MLbl) : NTree MLbl :=
  .node (lblOf z pub) [c]
def mTwo (z : K) (pub : MemoryTable.Pub K) (l r : NTree MLbl) : NTree MLbl :=
  .node (lblOf z pub) [l, r]

def tHalt3 (z α : K) : NTree MLbl := mLeaf z (pHalt3 z α)
def tVerifyB (z α : K) : NTree MLbl := mOne z (pVerifyB z α) (tHalt3 z α)
def tHaltB1 (z α : K) : NTree MLbl := mLeaf z (pHaltB1 z α)
def tDecB (z α : K) : NTree MLbl := mTwo z (pDecB z α) (tHaltB1 z α) (tVerifyB z α)
def tReadB (z α : K) : NTree MLbl := mOne z (pReadB z α) (tDecB z α)
def tVerifyT (z α : K) : NTree MLbl := mOne z (pVerifyT z α) (tReadB z α)
def tHalt5 (z α : K) : NTree MLbl := mLeaf z (pHalt5 z α)
def tVerifyC (z α : K) : NTree MLbl := mOne z (pVerifyC z α) (tHalt5 z α)
def tHaltC1 (z α : K) : NTree MLbl := mLeaf z (pHaltC1 z α)
def tDecC (z α : K) : NTree MLbl := mTwo z (pDecC z α) (tHaltC1 z α) (tVerifyC z α)
def tReadC (z α : K) : NTree MLbl := mOne z (pReadC z α) (tDecC z α)
def tDecT (z α : K) : NTree MLbl := mTwo z (pDecT z α) (tVerifyT z α) (tReadC z α)
def tReadT (z α : K) : NTree MLbl := mOne z (pReadT z α) (tDecT z α)
def tVerifyF (z α : K) : NTree MLbl := mOne z (pVerifyF z α) (tReadT z α)
def tHalt8 (z α : K) : NTree MLbl := mLeaf z (pHalt8 z α)
def tDecF (z α : K) : NTree MLbl := mTwo z (pDecF z α) (tHalt8 z α) (tVerifyF z α)
def rootTree (z α : K) : NTree MLbl := mOne z (pReadF z α) (tDecF z α)

/-! The a-bearing served tree (padding rows shared). -/

def tVerifyBA (z α : K) : NTree MLbl := mOne z (pVerifyBA z α) (tHalt3 z α)
def tDecBA (z α : K) : NTree MLbl := mTwo z (pDecB z α) (tHaltB1 z α) (tVerifyBA z α)
def tReadBA (z α : K) : NTree MLbl := mOne z (pReadBA z α) (tDecBA z α)
def tVerifyTA (z α : K) : NTree MLbl := mOne z (pVerifyTA z α) (tReadBA z α)
def tVerifyCA (z α : K) : NTree MLbl := mOne z (pVerifyCA z α) (tHalt5 z α)
def tDecCA (z α : K) : NTree MLbl := mTwo z (pDecC z α) (tHaltC1 z α) (tVerifyCA z α)
def tReadCA (z α : K) : NTree MLbl := mOne z (pReadCA z α) (tDecCA z α)
def tDecTA (z α : K) : NTree MLbl := mTwo z (pDecT z α) (tVerifyTA z α) (tReadCA z α)
def tReadTA (z α : K) : NTree MLbl := mOne z (pReadTA z α) (tDecTA z α)
def tVerifyFA (z α : K) : NTree MLbl := mOne z (pVerifyFA z α) (tReadTA z α)
def tDecFA (z α : K) : NTree MLbl := mTwo z (pDecF z α) (tHalt8 z α) (tVerifyFA z α)
def rootTreeA (z α : K) : NTree MLbl := mOne z (pReadFA z α) (tDecFA z α)

/-! ## The concrete configuration and execution -/

def cfg (z α : K) : ExactConfig F K where
  challenges := { a := 0, b := 0, c := 1, α := α, z := z, β := 0, γ := 0, lam := MemoryTable.formRDefault }
  Ksz := 8
  kMem := 1
  orbit := executionOrbit
  orbit_h_pos := by norm_num [executionOrbit]
  compRows := 3
  memRows := 17
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
    norm_num [rootTree, tDecF, tHalt8, tVerifyF, tReadT, tDecT, tVerifyT, tReadC,
      tReadB, tDecC, tDecB, tHaltC1, tVerifyC, tHaltB1, tVerifyB, tHalt5, tHalt3,
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
    norm_num [rootTreeA, tDecFA, tHalt8, tVerifyFA, tReadTA, tDecTA, tVerifyTA, tReadCA,
      tReadBA, tDecCA, tDecBA, tHaltC1, tVerifyCA, tHaltB1, tVerifyBA, tHalt5, tHalt3,
      mOne, mTwo, mLeaf, bfsForest, NTree.size, totalSize, cfg]

end

def seedZ : K := 8
def alphaA : K := 4

theorem seedZ_eq_image : seedZ = φ (8 : F) := by rw [seedZ]; simp [map_ofNat]
theorem alphaA_eq_image : alphaA = φ (4 : F) := by rw [alphaA]; simp [map_ofNat]

theorem seedZ_ne_zero : seedZ ≠ 0 := by rw [seedZ]; decide

theorem exec_row_counts :
    (exec seedZ alphaA).computeRows.length = 3 ∧
      (exec seedZ alphaA).memoryRows.length = 17 :=
  ⟨(exec seedZ alphaA).computeRows_length, (exec seedZ alphaA).memoryRows_length⟩

end Nock.NockVMROM.Thm54.TraceGen.Op8ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op8ConfigK3.exec
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op8ConfigK3.omega19_order
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op8ConfigK3.exec_row_counts
