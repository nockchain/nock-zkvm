/-
  Nock/NockVMROM/Thm54/TraceGen/Op2ConfigK3.lean

  Stage 3 of the OP2 Layer-2 CORE: the `ExactConfig (ZMod 97) K3` and `ExactExecution` carriers
  for the fan-out-3 eval program

      `*[0 [2 [1 [0 1]] [1 [1 5]]]] = 5`

  over base `F = ZMod 97` and the computable cubic table field `K = K3` (`finrank F K = 3`).

  Compute tree (BFS: root, then three `OP_1` children):

      s2 root  (subject 0, formula [2 [b c]], eval 5)
     /    |    \
  sf1:s1  sf2:s1  sf3:s1

  Memory forest: a *single* root (`kMem = 1`) reconstructing the five committed records
  (parent `mr1` formula@3, parent `mr2` formula-tail@2, and the three child formula@3
  records) as one interleaved `read_root`/`verify_child` tree.  The axis-2 (left) descent
  on the formula tail is the OP2-specific memory shape.  There is no Layer-1 committed served-memory fixture; this is the
  reconstruction, not a served lookup (`requiredServedLookups.s2 = 0`).

  The seed `z = 8` and timestamp challenge `α = 4` are the base-field images used by the
  OP1/K3 slice.  Five live timestamps `α,…,α⁵` need 23 memory rows, so the execution orbit
  uses exponent `h = 5` (capacity `2⁵ = 32`) driven by `φ 19` (`19` has order `32` in
  `ZMod 97`)
-/
import Nock.NockVMROM.Thm54.Execution
import Nock.GlobalCarryRecognizer
import Nock.NockVMROM.Thm54.TraceGen.Op2Gen
import Nock.NockVMROM.Thm54.TraceGen.CubicField97
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

open Nock Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.CubicField97

/-- The base (semantic) field. -/
abbrev F : Type := ZMod 97

/-- The table/RAP field: the computable cubic extension with `finrank F K3 = 3`. -/
abbrev K : Type := CubicField97.K3

/-- The injective algebra map `ZMod 97 →+* K3`. -/
noncomputable abbrev φ : F →+* K := algebraMap F K

theorem φ_injective : Function.Injective φ := RingHom.injective φ

/-! ## The execution orbit over `K3` (`h = 5`, capacity `32`) -/

/-- `19` has multiplicative order thirty-two in `ZMod 97`. -/
theorem omega19_order_base : orderOf (19 : F) = 32 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

/-- The image `φ 19` keeps multiplicative order thirty-two in `K3`. -/
theorem omega19_order : orderOf (φ (19 : F)) = 32 := by
  have h := orderOf_injective φ.toMonoidHom φ_injective (19 : F)
  rw [omega19_order_base] at h
  simpa using h

/-- The twenty-three-row exact execution orbit over `K3`. -/
noncomputable def executionOrbit : OrbitDomain K where
  h := 5
  ω := φ (19 : F)
  βcoset := 1
  βcoset_ne_zero := one_ne_zero
  order_ω := by simpa using omega19_order

/-! ## Seed-dependent field rows (parametrized by `z α : K3`) -/

noncomputable section

/-- The seed-`z` fingerprint of a committed noun, over `K3`. -/
noncomputable def fp (z : K) (n : Noun) : FP K := GlobalCarryRecognizer.enc z n

/-- Shared `OP_1` formula head `1`. -/
def op1Head : Noun := .atom 1
/-- The `OP_2` formula head `2`. -/
def op2Head : Noun := .atom 2

/-! ## The five committed memory records

Timestamps follow the generator's `stampOfAcc` schedule (`Op2Gen.computeNodesOp2`):
parent records at `α, α²`; children at `α³, α⁴, α⁵`. -/

/-- Parent `mr1`: formula-open `[2 [b c]] @3`. -/
def recF (z α : K) : MemRec K := ⟨fp z op2ParentFormula, fp z op2ParentTail, 3, α⟩
/-- Parent `mr2`: formula-tail `[b c] @2` — the axis-2 descent. -/
def recT (z α : K) : MemRec K := ⟨fp z op2ParentTail, fp z op2ChildFormula1, 2, α ^ 2⟩
/-- Child-one `OP_1` record: `[1 [0 1]] @3 → [0 1]`. -/
def recB (z α : K) : MemRec K := ⟨fp z op2ChildFormula1, fp z op2Sf1, 3, α ^ 3⟩
/-- Child-two `OP_1` record: `[1 [1 5]] @3 → [1 5]`. -/
def recC (z α : K) : MemRec K := ⟨fp z op2ChildFormula2, fp z op2Sf2, 3, α ^ 4⟩
/-- Child-three `OP_1` record: `[1 5] @3 → 5` (computed-subject child). -/
def recS (z α : K) : MemRec K := ⟨fp z op2Sf2, fp z op2Result, 3, α ^ 5⟩

/-! ## Table inputs -/

def compInputs (z α : K) : ComputeTable.Inputs K where
  α := α
  z := z
  a := 0
  b := 0
  c := 0

def memInputs (z : K) : MemoryTable.Inputs K := ⟨z, 0, 0⟩

/-! ## The four compute rows -/

/-- The `.s2` parent decomposition: head `2`, tail `[b c]`, `f_th ↦ b`, `f_tt ↦ c`. -/
def parentDec (z : K) : ComputeTable.Dec K where
  f_h := fp z op2Head
  f_t := fp z op2ParentTail
  f_th := fp z op2ChildFormula1
  f_tt := fp z op2ChildFormula2
  f_tth := 0
  f_ttt := 0

/-- The `.s2` parent public row: three live subformula
slots, two committed records, line-number `1 → α²`. -/
def parentPub (z α : K) : ComputeTable.Pub K where
  state := .s2
  s := fp z op2Subject
  f := fp z op2ParentFormula
  e := fp z op2Result
  sf1_s := fp z op2Subject
  sf1_f := fp z op2ChildFormula1
  sf1_e := fp z op2Sf1
  sf2_s := fp z op2Subject
  sf2_f := fp z op2ChildFormula2
  sf2_e := fp z op2Sf2
  sf3_s := fp z op2Sf1
  sf3_f := fp z op2Sf2
  sf3_e := fp z op2Result
  ln_prev := 1
  ln := α ^ 2
  mr1 := recF z α
  mr2 := recT z α
  mr3 := MemRec.zero

def parentRow (z α : K) : ComputeTable.State × ComputeTable.DTcomp K :=
  (.s2, (compInputs z α, parentPub z α, parentDec z))

/-- Generic `OP_1` decomposition: head `1`, tail its constant result. -/
def op1DecOf (z : K) (result : Noun) : ComputeTable.Dec K where
  f_h := fp z op1Head
  f_t := fp z result
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

/-- Generic `OP_1` public row, line-number `lnPrev → lnPrev·α`. -/
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
  op1PubOf z α op2Subject op2ChildFormula1 op2Sf1 (α ^ 2) (recB z α)
def child2Pub (z α : K) : ComputeTable.Pub K :=
  op1PubOf z α op2Subject op2ChildFormula2 op2Sf2 (α ^ 3) (recC z α)
def child3Pub (z α : K) : ComputeTable.Pub K :=
  op1PubOf z α op2Sf1 op2Sf2 op2Result (α ^ 4) (recS z α)

def child1Row (z α : K) : ComputeTable.State × ComputeTable.DTcomp K :=
  (.s1, (compInputs z α, child1Pub z α, op1DecOf z op2Sf1))
def child2Row (z α : K) : ComputeTable.State × ComputeTable.DTcomp K :=
  (.s1, (compInputs z α, child2Pub z α, op1DecOf z op2Sf2))
def child3Row (z α : K) : ComputeTable.State × ComputeTable.DTcomp K :=
  (.s1, (compInputs z α, child3Pub z α, op1DecOf z op2Result))

/-- The fan-out-3 compute tree: `.s2` root over its three `OP_1` children
(BFS: parent, child1, child2, child3). -/
def computeTree (z α : K) : NTree (ComputeTable.State × ComputeTable.DTcomp K) :=
  .node (parentRow z α)
    [.node (child1Row z α) [], .node (child2Row z α) [], .node (child3Row z α) []]

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

/-! ## The five LogUp reciprocals

With `β = γ = 0` the pole of a record is its root's fingerprint size. -/

def qF (z α : K) : K := (pole (memInputs z) (recF z α) 1)⁻¹
def qT (z α : K) : K := (pole (memInputs z) (recT z α) 1)⁻¹
def qB (z α : K) : K := (pole (memInputs z) (recB z α) 1)⁻¹
def qC (z α : K) : K := (pole (memInputs z) (recC z α) 1)⁻¹
def qS (z α : K) : K := (pole (memInputs z) (recS z α) 1)⁻¹

/-! ## The twenty-three memory-forest cells

Form R rows at `λ = formRDefault = 2` (row-level `(T, C')`): remaining is the record axis
(`mem.axis` is `T`).
Verify `+ ts`, decompose `cnt += rc.ind`, read `− axis · ts`. Bottom-up so every
`eqBlk` conjunct holds. -/

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

-- child-three OP1 subtree `[1 5] @3 → 5` (ts = α⁵)
def cHalt5 (z : K) : MemoryTable.Cell K := ⟨fp z op2Result, 0, 0⟩
def cVerifyS (z α : K) : MemoryTable.Cell K := cellVerify (fp z op2Result) (cHalt5 z) (α ^ 5)
def cHaltS1 (z : K) : MemoryTable.Cell K := ⟨fp z op1Head, 0, 0⟩
def cDecS (z α : K) : MemoryTable.Cell K := cellDec (fp z op2Sf2) (cHaltS1 z) (cVerifyS z α)
def cReadS (z α : K) : MemoryTable.Cell K := cellRead (fp z op2Sf2) (cDecS z α) 3 (α ^ 5)

-- child-two `[1 [1 5]] @3 → [1 5]` wrapping the child-three subtree (ts = α⁴)
def cVerifyC (z α : K) : MemoryTable.Cell K :=
  cellVerify (fp z op2Sf2) (cReadS z α) (α ^ 4)
def cHaltC1 (z : K) : MemoryTable.Cell K := ⟨fp z op1Head, 0, 0⟩
def cDecC (z α : K) : MemoryTable.Cell K :=
  cellDec (fp z op2ChildFormula2) (cHaltC1 z) (cVerifyC z α)
def cReadC (z α : K) : MemoryTable.Cell K :=
  cellRead (fp z op2ChildFormula2) (cDecC z α) 3 (α ^ 4)

-- `[0 1]` decompose after verifying child-one (no extra record)
def cHalt0 (z : K) : MemoryTable.Cell K := ⟨fp z (.atom 0), 0, 0⟩
def cHalt1s (z : K) : MemoryTable.Cell K := ⟨fp z (.atom 1), 0, 0⟩
def cDecSf1 (z : K) : MemoryTable.Cell K := cellDec (fp z op2Sf1) (cHalt0 z) (cHalt1s z)

-- child-one `[1 [0 1]] @3 → [0 1]` (ts = α³)
def cVerifyB (z α : K) : MemoryTable.Cell K := cellVerify (fp z op2Sf1) (cDecSf1 z) (α ^ 3)
def cHaltB1 (z : K) : MemoryTable.Cell K := ⟨fp z op1Head, 0, 0⟩
def cDecB (z α : K) : MemoryTable.Cell K := cellDec (fp z op2ChildFormula1) (cHaltB1 z) (cVerifyB z α)
def cReadB (z α : K) : MemoryTable.Cell K := cellRead (fp z op2ChildFormula1) (cDecB z α) 3 (α ^ 3)

-- formula-tail `[b c] @2` (axis-2 left descent, ts = α²)
def cVerifyT (z α : K) : MemoryTable.Cell K :=
  cellVerify (fp z op2ChildFormula1) (cReadB z α) (α ^ 2)
def cDecT (z α : K) : MemoryTable.Cell K :=
  cellDec (fp z op2ParentTail) (cVerifyT z α) (cReadC z α)
def cReadT (z α : K) : MemoryTable.Cell K :=
  cellRead (fp z op2ParentTail) (cDecT z α) 2 (α ^ 2)

-- formula `[2 [b c]] @3` (ts = α)
def cVerifyF (z α : K) : MemoryTable.Cell K :=
  cellVerify (fp z op2ParentTail) (cReadT z α) α
def cHalt2 (z : K) : MemoryTable.Cell K := ⟨fp z (.atom 2), 0, 0⟩
def cDecF (z α : K) : MemoryTable.Cell K :=
  cellDec (fp z op2ParentFormula) (cHalt2 z) (cVerifyF z α)
def cReadF (z α : K) : MemoryTable.Cell K :=
  cellRead (fp z op2ParentFormula) (cDecF z α) 3 α

/-! ## The twenty-three memory rows, with BFS-chained LogUp accumulators

BFS order (the `memory_chain` order):
`readF, decF, halt2, verifyF, readT, decT, verifyT, readC, readB, decC, decB,
haltC1, verifyC, haltB1, verifyB, readS, decSf1, decS, halt0, halt1s, haltS1,
verifyS, halt5`. -/

def pReadF (z α : K) : MemoryTable.Pub K :=
  readPub z (cReadF z α) (cDecF z α) (recF z α) 0 (qF z α)
def pDecF (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecF z α) (cHalt2 z) (cVerifyF z α) .halt .verify_child (qF z α)
def pHalt2 (z α : K) : MemoryTable.Pub K := haltPub z 2 (qF z α)
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
  verifyPub z (cVerifyC z α) (cReadS z α) (recC z α) (qC z α + qB z α) (qB z α)
def pHaltB1 (z α : K) : MemoryTable.Pub K := haltPub z 1 (qB z α)
def pVerifyB (z α : K) : MemoryTable.Pub K :=
  verifyPub z (cVerifyB z α) (cDecSf1 z) (recB z α) (qB z α) 0
def pReadS (z α : K) : MemoryTable.Pub K :=
  readPub z (cReadS z α) (cDecS z α) (recS z α) 0 (qS z α)
def pDecSf1 (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecSf1 z) (cHalt0 z) (cHalt1s z) .halt .halt (qS z α)
def pDecS (z α : K) : MemoryTable.Pub K :=
  decPub z (cDecS z α) (cHaltS1 z) (cVerifyS z α) .halt .verify_child (qS z α)
def pHalt0 (z α : K) : MemoryTable.Pub K := haltPub z 0 (qS z α)
def pHalt1s (z α : K) : MemoryTable.Pub K := haltPub z 1 (qS z α)
def pHaltS1 (z α : K) : MemoryTable.Pub K := haltPub z 1 (qS z α)
def pVerifyS (z α : K) : MemoryTable.Pub K :=
  verifyPub z (cVerifyS z α) (cHalt5 z) (recS z α) (qS z α) 0
def pHalt5 (z : K) : MemoryTable.Pub K := haltPub z 5 0

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
  verifyPubA z (cVerifyC z α) (cReadS z α) (recC z α) (qC z α + qB z α) (qB z α)
@[simp] def pVerifyBA (z α : K) : MemoryTable.Pub K :=
  verifyPubA z (cVerifyB z α) (cDecSf1 z) (recB z α) (qB z α) 0
@[simp] def pReadSA (z α : K) : MemoryTable.Pub K :=
  readPubA z (cReadS z α) (cDecS z α) (recS z α) 0 (qS z α)
@[simp] def pVerifySA (z α : K) : MemoryTable.Pub K :=
  verifyPubA z (cVerifyS z α) (cHalt5 z) (recS z α) (qS z α) 0

/-! ## The single serviced root -/

def mLeaf (z : K) (pub : MemoryTable.Pub K) : NTree MLbl := .node (lblOf z pub) []
def mOne (z : K) (pub : MemoryTable.Pub K) (c : NTree MLbl) : NTree MLbl :=
  .node (lblOf z pub) [c]
def mTwo (z : K) (pub : MemoryTable.Pub K) (l r : NTree MLbl) : NTree MLbl :=
  .node (lblOf z pub) [l, r]

def tHalt5 (z : K) : NTree MLbl := mLeaf z (pHalt5 z)
def tVerifyS (z α : K) : NTree MLbl := mOne z (pVerifyS z α) (tHalt5 z)
def tHaltS1 (z α : K) : NTree MLbl := mLeaf z (pHaltS1 z α)
def tDecS (z α : K) : NTree MLbl := mTwo z (pDecS z α) (tHaltS1 z α) (tVerifyS z α)
def tReadS (z α : K) : NTree MLbl := mOne z (pReadS z α) (tDecS z α)
def tHalt0 (z α : K) : NTree MLbl := mLeaf z (pHalt0 z α)
def tHalt1s (z α : K) : NTree MLbl := mLeaf z (pHalt1s z α)
def tDecSf1 (z α : K) : NTree MLbl := mTwo z (pDecSf1 z α) (tHalt0 z α) (tHalt1s z α)
def tVerifyB (z α : K) : NTree MLbl := mOne z (pVerifyB z α) (tDecSf1 z α)
def tHaltB1 (z α : K) : NTree MLbl := mLeaf z (pHaltB1 z α)
def tDecB (z α : K) : NTree MLbl := mTwo z (pDecB z α) (tHaltB1 z α) (tVerifyB z α)
def tReadB (z α : K) : NTree MLbl := mOne z (pReadB z α) (tDecB z α)
def tVerifyC (z α : K) : NTree MLbl := mOne z (pVerifyC z α) (tReadS z α)
def tHaltC1 (z α : K) : NTree MLbl := mLeaf z (pHaltC1 z α)
def tDecC (z α : K) : NTree MLbl := mTwo z (pDecC z α) (tHaltC1 z α) (tVerifyC z α)
def tReadC (z α : K) : NTree MLbl := mOne z (pReadC z α) (tDecC z α)
def tVerifyT (z α : K) : NTree MLbl := mOne z (pVerifyT z α) (tReadB z α)
def tDecT (z α : K) : NTree MLbl := mTwo z (pDecT z α) (tVerifyT z α) (tReadC z α)
def tReadT (z α : K) : NTree MLbl := mOne z (pReadT z α) (tDecT z α)
def tVerifyF (z α : K) : NTree MLbl := mOne z (pVerifyF z α) (tReadT z α)
def tHalt2 (z α : K) : NTree MLbl := mLeaf z (pHalt2 z α)
def tDecF (z α : K) : NTree MLbl := mTwo z (pDecF z α) (tHalt2 z α) (tVerifyF z α)
def rootTree (z α : K) : NTree MLbl := mOne z (pReadF z α) (tDecF z α)

/-! The a-bearing served tree (padding rows shared). -/

def tVerifySA (z α : K) : NTree MLbl := mOne z (pVerifySA z α) (tHalt5 z)
def tDecSA (z α : K) : NTree MLbl := mTwo z (pDecS z α) (tHaltS1 z α) (tVerifySA z α)
def tReadSA (z α : K) : NTree MLbl := mOne z (pReadSA z α) (tDecSA z α)
def tVerifyBA (z α : K) : NTree MLbl := mOne z (pVerifyBA z α) (tDecSf1 z α)
def tDecBA (z α : K) : NTree MLbl := mTwo z (pDecB z α) (tHaltB1 z α) (tVerifyBA z α)
def tReadBA (z α : K) : NTree MLbl := mOne z (pReadBA z α) (tDecBA z α)
def tVerifyCA (z α : K) : NTree MLbl := mOne z (pVerifyCA z α) (tReadSA z α)
def tDecCA (z α : K) : NTree MLbl := mTwo z (pDecC z α) (tHaltC1 z α) (tVerifyCA z α)
def tReadCA (z α : K) : NTree MLbl := mOne z (pReadCA z α) (tDecCA z α)
def tVerifyTA (z α : K) : NTree MLbl := mOne z (pVerifyTA z α) (tReadBA z α)
def tDecTA (z α : K) : NTree MLbl := mTwo z (pDecT z α) (tVerifyTA z α) (tReadCA z α)
def tReadTA (z α : K) : NTree MLbl := mOne z (pReadTA z α) (tDecTA z α)
def tVerifyFA (z α : K) : NTree MLbl := mOne z (pVerifyFA z α) (tReadTA z α)
def tDecFA (z α : K) : NTree MLbl := mTwo z (pDecF z α) (tHalt2 z α) (tVerifyFA z α)
def rootTreeA (z α : K) : NTree MLbl := mOne z (pReadFA z α) (tDecFA z α)

/-! ## The concrete configuration and execution -/

/-- The OP2/K3 slice's shared configuration. -/
def cfg (z α : K) : ExactConfig F K where
  challenges := { a := 0, b := 0, c := 0, α := α, z := z, β := 0, γ := 0, lam := MemoryTable.formRDefault }
  Ksz := 8
  kMem := 1
  orbit := executionOrbit
  orbit_h_pos := by norm_num [executionOrbit]
  compRows := 4
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

/-- The OP2/K3 slice's authoritative forest-first execution: the four-row compute tree
and the twenty-three-row single-root memory reconstruction of its five requests. -/
def exec (z α : K) : ExactExecution (cfg z α) where
  computeTree := computeTree z α
  memoryForest := [rootTree z α]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTree, bfsForest, NTree.size, totalSize, cfg]
  memory_bfs_length := by
    norm_num [rootTree, tDecF, tHalt2, tVerifyF, tReadT, tDecT, tVerifyT, tReadC,
      tReadB, tDecC, tDecB, tHaltC1, tVerifyC, tHaltB1, tVerifyB, tReadS, tDecSf1,
      tDecS, tHalt0, tHalt1s, tHaltS1, tVerifyS, tHalt5, mOne, mTwo, mLeaf,
      bfsForest, NTree.size, totalSize, cfg]

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
    norm_num [rootTreeA, tDecFA, tHalt2, tVerifyFA, tReadTA, tDecTA, tVerifyTA, tReadCA,
      tReadBA, tDecCA, tDecBA, tHaltC1, tVerifyCA, tHaltB1, tVerifyBA, tReadSA, tDecSf1,
      tDecSA, tHalt0, tHalt1s, tHaltS1, tVerifySA, tHalt5, mOne, mTwo, mLeaf,
      bfsForest, NTree.size, totalSize, cfg]

end

/-- The concrete honest seed `z = 8` (`= φ 8`). -/
def seedZ : K := 8
/-- The concrete honest timestamp challenge `α = 4` (`= φ 4`). -/
def alphaA : K := 4

theorem seedZ_eq_image : seedZ = φ (8 : F) := by rw [seedZ]; simp [map_ofNat]
theorem alphaA_eq_image : alphaA = φ (4 : F) := by rw [alphaA]; simp [map_ofNat]

theorem seedZ_ne_zero : seedZ ≠ 0 := by rw [seedZ]; decide

/-- The compute carrier is exactly four rows, the memory carrier exactly twenty-three. -/
theorem exec_row_counts :
    (exec seedZ alphaA).computeRows.length = 4 ∧
      (exec seedZ alphaA).memoryRows.length = 23 :=
  ⟨(exec seedZ alphaA).computeRows_length, (exec seedZ alphaA).memoryRows_length⟩

end Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.exec
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.omega19_order
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.exec_row_counts
