import Nock.NockVMROM.Thm54.EqualityOperandCensus
import Nock.NockVMROM.Thm54.MultiRootServedFixture
import Nock.NockVMROM.Thm54.TraceGen.RowEncode

/-!
# A whole execution over the distinct-pair `OP_5` census

`EqualityOperandCensus` builds the first comparison census in the tree with a
genuinely distinct noun pair: the honest Nock evaluation `*[0 [5 [1 [7 9]] [1 [8 10]]]] = 1`
compares the two *different* operands `[7 9]` and `[8 10]` at the `equalityOperand` role
.  It stops at the census, because no `BuildableNockExecution` exists over that
skeleton: the three rows commit four memory records (`op5Skeleton_record_budget`) and the module's
`memoryForest` is empty.

This module supplies the whole execution.  The compute side is the same three rows -- an `OP_5`
parent with two constant `OP_1` children -- now carrying their
real memory records; the memory side is a **single serviced root** on the noun `op5Formula`, whose
twenty-one rows service all four committed records through four nested `read_root`/`verify_child`
pairs.

**The seed is `8`, not the released fixture's `-1`.**  `servedSeed_is_the_collision_seed` compiles
that `-1` is exactly this census's unique bad seed, so it cannot be reused;
`op5Census_good_seed_of_order_sixteen` supplies `8`.  At `8` the two operands are separated
(`operands_not_sepSeed_iff`), which is what makes the row's `equalityOperand` comparison a
`PairFaithful` statement about two genuinely different nouns rather than a vacuous diagonal.  The
same choice is what makes `ComputeTable.WF.rlc5` -- the paper's OP_5 random-linear-combination
non-degeneracy (the paper; **cite corrected** -- was `1712,1716`, and `1716` is
the *opcodes-8-and-11* paragraph, which bears on `WF.size8`/`WF.size11` and not on `rlc5`.  Unlike
the `WF` docstring in `Nock/ComputeTable.lean`, which covers all three fields and so cites `1716`
correctly, this sentence is about `rlc5` alone, so `1716` was propagated rather than checked.  `1712`
is the OP_5 paragraph and `1991` is EC.5.5 itself) -- satisfiable: it needs
`a·Δsize + b·Δdyck + c·Δleaf ≠ 0` on the two *unequal* operand fingerprints, and with
`(a,b,c) = (0,0,1)` that is exactly `-(1 + z) ≠ 0`.  The released fixtures all take `(a,b,c) = 0`
and have no `OP_5` row, so this is the first execution in the tree at which the gate has content.
-/

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.DistinctCensusExecution

open scoped Classical
open Nock Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.EqualityOperandCensus

noncomputable section

local instance prime97d : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97d : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-! ## A. The sampled seed and timestamp challenge -/


/-- The sampled NPR seed.  `-1` is the census's unique collision seed
(`servedSeed_is_the_collision_seed`), so the fixture moves to `8`, which
`op5Census_good_seed_of_order_sixteen` compiles to be good and of multiplicative order `16`. -/
def seedD : K97cubic := 8

theorem seedD_ne_neg_one : seedD ≠ -1 := eight_ne_neg_one_K97

theorem seedD_ne : seedD ≠ 0 := by
  intro hk
  have hk' : (8 : K97cubic) = 0 := hk
  have hbase : (8 : F97) ≠ 0 := by decide
  apply hbase
  apply (algebraMap F97 K97cubic).injective
  simpa only [map_ofNat, map_zero] using hk'

theorem one_lt_orderOf_seedD : 1 < orderOf seedD := by
  rw [show seedD = (8 : K97cubic) from rfl, omega8_order]
  norm_num

/-- The seed-`8` encoder. -/
def encD (n : Noun) : ComputeTable.FP K97cubic := GlobalCarryRecognizer.enc seedD n


/-- The sampled timestamp challenge, reused from the released fixture: order `24`, so the four
committed record exponents `1..4` give four distinct timestamps. -/
def alphaD : K97cubic := fixtureAlpha

theorem alphaD_order : orderOf alphaD = 24 := fixtureAlpha_order

/-! ## B. The three compute rows

The nouns are `EqualityOperandCensus`'s: `op5Formula = [5 [[1 [7 9]] [1 [8 10]]]]`,
`op5Tail = [[1 [7 9]] [1 [8 10]]]`, `leftFormula = [1 [7 9]]`, `rightFormula = [1 [8 10]]`,
`operandLeft = [7 9]`, `operandRight = [8 10]`, subject `0`, evaluation `1`. -/

def op5Head : Noun := .atom 5
def op1Head : Noun := .atom 1

theorem op5Formula_cons : op5Formula = .cell op5Head op5Tail := rfl
theorem op5Tail_cons : op5Tail = .cell leftFormula rightFormula := rfl
theorem leftFormula_cons : leftFormula = .cell op1Head operandLeft := rfl
theorem rightFormula_cons : rightFormula = .cell op1Head operandRight := rfl
theorem operandLeft_cons : operandLeft = .cell (.atom 7) (.atom 9) := rfl
theorem operandRight_cons : operandRight = .cell (.atom 8) (.atom 10) := rfl

/-! ### The four committed memory records -/


/-- The `OP_5` row's `mr1`: the always-operative formula opening.

*Cite repair.*  This cite read the paper alone until it was repaired.  `1850` is the block's
introductory sentence and does support *always-operative*; the record itself
(`((input_formula, formula_tail), 3, timestamp₁)`) is **`1852`** and `ln(i-1) · α = timestamp₁` is
**`1854`** — which is what `recT`'s sibling `1856-1862` already pointed at for `mem_record₂`. -/
def recF : ComputeTable.MemRec K97cubic := ⟨encD op5Formula, encD op5Tail, 3, alphaD⟩


/-- The `OP_5` row's `mr2`: the tail opening at axis `2`. -/
def recT : ComputeTable.MemRec K97cubic := ⟨encD op5Tail, encD leftFormula, 2, alphaD ^ 2⟩

/-- The left `OP_1` row's `mr1`. -/
def recL : ComputeTable.MemRec K97cubic := ⟨encD leftFormula, encD operandLeft, 3, alphaD ^ 3⟩

/-- The right `OP_1` row's `mr1`. -/
def recR : ComputeTable.MemRec K97cubic := ⟨encD rightFormula, encD operandRight, 3, alphaD ^ 4⟩

/-! ### Table inputs.  `c = 1` is what makes the `OP_5` RLC gate non-degenerate. -/

def compInputs : ComputeTable.Inputs K97cubic where
  α := alphaD
  z := seedD
  a := 0
  b := 0
  c := 1

def memInputs : MemoryTable.Inputs K97cubic := ⟨seedD, 0, 0⟩

/-! ### The two operands really are different, at this seed -/

theorem operands_sepSeed :
    GlobalCarryRecognizer.SepSeed seedD operandLeft operandRight := by
  by_contra h
  exact seedD_ne_neg_one ((operands_not_sepSeed_iff seedD).mp h)

theorem operands_encD_ne : encD operandLeft ≠ encD operandRight := by
  intro h
  exact seedD_ne_neg_one
    ((operands_fn_eq_iff seedD).mp
      (GlobalCarryRecognizer.enc_eq_imp_fn_eq seedD operandLeft operandRight h))

theorem bounded_operandLeft : FieldEmbedding.BoundedBy 97 operandLeft := by
  simp [operandLeft, FieldEmbedding.BoundedBy]

theorem bounded_operandRight : FieldEmbedding.BoundedBy 97 operandRight := by
  simp [operandRight, FieldEmbedding.BoundedBy]

/-- **The substantive comparison of the whole fixture.**  The `OP_5` row's `equalityOperand`
census entry is a `PairFaithful` claim about two genuinely *unequal* nouns
. -/
theorem operands_pairFaithful :
    OpcodeSemantics.PairFaithful seedD 97 operandLeft operandRight where
  separates := operands_sepSeed
  left_bounded := bounded_operandLeft
  right_bounded := bounded_operandRight

/-! ### Boundedness of every committed noun -/

theorem bounded_op5Subject : FieldEmbedding.BoundedBy 97 op5Subject := by
  simp [op5Subject]
theorem bounded_op5Result : FieldEmbedding.BoundedBy 97 op5Result := by
  simp [op5Result]
theorem bounded_op5Head : FieldEmbedding.BoundedBy 97 op5Head := by simp [op5Head]
theorem bounded_op1Head : FieldEmbedding.BoundedBy 97 op1Head := by simp [op1Head]
theorem bounded_leftFormula : FieldEmbedding.BoundedBy 97 leftFormula := by
  simp [leftFormula, operandLeft, FieldEmbedding.BoundedBy]
theorem bounded_rightFormula : FieldEmbedding.BoundedBy 97 rightFormula := by
  simp [rightFormula, operandRight, FieldEmbedding.BoundedBy]
theorem bounded_op5Tail : FieldEmbedding.BoundedBy 97 op5Tail := by
  simp [op5Tail, leftFormula, rightFormula, operandLeft, operandRight,
    FieldEmbedding.BoundedBy]
theorem bounded_op5Formula : FieldEmbedding.BoundedBy 97 op5Formula := by
  simp [op5Formula, op5Tail, leftFormula, rightFormula, operandLeft, operandRight,
    FieldEmbedding.BoundedBy]

/-! ### The `OP_5` row -/

def op5Dec : ComputeTable.Dec K97cubic where
  f_h := encD op5Head
  f_t := encD op5Tail
  f_th := encD leftFormula
  f_tt := encD rightFormula
  f_tth := 0
  f_ttt := 0

def op5PubD : ComputeTable.Pub K97cubic where
  state := .s5
  s := encD op5Subject
  f := encD op5Formula
  e := encD op5Result
  sf1_s := encD op5Subject
  sf1_f := encD leftFormula
  sf1_e := encD operandLeft
  sf2_s := encD op5Subject
  sf2_f := encD rightFormula
  sf2_e := encD operandRight
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 1
  ln := alphaD ^ 2
  mr1 := recF
  mr2 := recT
  mr3 := MemRec.zero

def op5RowD : ComputeTable.State × ComputeTable.DTcomp K97cubic :=
  (.s5, (compInputs, op5PubD, op5Dec))

theorem op5_accepts : Vcomp compInputs op5PubD op5Dec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedD_ne op5Head op5Tail
  · ext <;> norm_num [op5PubD, recF, op5Dec, compInputs, encD]
  · simp [SVhead, headAtom, op5PubD, op5Dec, compInputs, encD, op5Head,
      GlobalCarryRecognizer.enc_atom, State.toNat]
  · refine ⟨?_, ?_, rfl, ?_⟩
    · ext <;> norm_num [op5PubD, recT, op5Dec, compInputs, encD]
    · exact (GlobalCarryRecognizer.enc_cons seedD_ne leftFormula rightFormula).symm
    · norm_num [op5PubD, compInputs]
  · refine ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
    · simp [op5PubD, compInputs, encD, op5Result,
        GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]
    · simp [op5PubD, encD, op5Result,
        GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]
    · rw [show op5PubD.e.leaf = 1 by
        simp [op5PubD, encD, op5Result, GlobalCarryRecognizer.enc_atom,
          ComputeTable.FP.atomFP]]
      rw [ComputeTable.FP.eqOp, if_neg]
      exact operands_encD_ne

theorem op5_wf : ComputeTable.WF compInputs op5PubD where
  rlc5 := by
    intro _ _
    show compInputs.a * (op5PubD.sf1_e.size - op5PubD.sf2_e.size)
      + compInputs.b * (op5PubD.sf1_e.dyck - op5PubD.sf2_e.dyck)
      + compInputs.c * (op5PubD.sf1_e.leaf - op5PubD.sf2_e.leaf) ≠ 0
    rw [show compInputs.a = 0 from rfl, show compInputs.b = 0 from rfl,
      show compInputs.c = 1 from rfl]
    rw [show op5PubD.sf1_e.leaf = 7 + 9 * seedD by
        simpa [op5PubD, encD] using leafPoly_eval_left seedD,
      show op5PubD.sf2_e.leaf = 8 + 10 * seedD by
        simpa [op5PubD, encD] using leafPoly_eval_right seedD]
    intro h
    apply seedD_ne_neg_one
    linear_combination -h
  size8 := by simp [op5PubD]
  size11 := by simp [op5PubD]

/-! ### The two `OP_1` rows -/

def op1DecOf (result : Noun) : ComputeTable.Dec K97cubic where
  f_h := encD op1Head
  f_t := encD result
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

def op1PubOf (formula result : Noun) (lnPrev : K97cubic)
    (rec : ComputeTable.MemRec K97cubic) : ComputeTable.Pub K97cubic where
  state := .s1
  s := encD op5Subject
  f := encD formula
  e := encD result
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
  ln := lnPrev * alphaD
  mr1 := rec
  mr2 := MemRec.zero
  mr3 := MemRec.zero

def op1LPub : ComputeTable.Pub K97cubic :=
  op1PubOf leftFormula operandLeft (alphaD ^ 2) recL

def op1RPub : ComputeTable.Pub K97cubic :=
  op1PubOf rightFormula operandRight (alphaD ^ 3) recR

def op1LRow : ComputeTable.State × ComputeTable.DTcomp K97cubic :=
  (.s1, (compInputs, op1LPub, op1DecOf operandLeft))

def op1RRow : ComputeTable.State × ComputeTable.DTcomp K97cubic :=
  (.s1, (compInputs, op1RPub, op1DecOf operandRight))

theorem op1L_accepts : Vcomp compInputs op1LPub (op1DecOf operandLeft) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedD_ne op1Head operandLeft
  · ext <;> norm_num [op1LPub, op1PubOf, recL, op1DecOf, compInputs, encD]
    ring
  · simp [SVhead, headAtom, op1LPub, op1PubOf, op1DecOf, compInputs, encD, op1Head,
      GlobalCarryRecognizer.enc_atom, State.toNat]
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

theorem op1R_accepts : Vcomp compInputs op1RPub (op1DecOf operandRight) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedD_ne op1Head operandRight
  · ext <;> norm_num [op1RPub, op1PubOf, recR, op1DecOf, compInputs, encD]
    ring
  · simp [SVhead, headAtom, op1RPub, op1PubOf, op1DecOf, compInputs, encD, op1Head,
      GlobalCarryRecognizer.enc_atom, State.toNat]
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

theorem op1L_wf : ComputeTable.WF compInputs op1LPub where
  rlc5 := by intro h; simp [op1LPub, op1PubOf] at h
  size8 := by intro h; simp [op1LPub, op1PubOf] at h
  size11 := by intro h; simp [op1LPub, op1PubOf] at h

theorem op1R_wf : ComputeTable.WF compInputs op1RPub where
  rlc5 := by intro h; simp [op1RPub, op1PubOf] at h
  size8 := by intro h; simp [op1RPub, op1PubOf] at h
  size11 := by intro h; simp [op1RPub, op1PubOf] at h

/-! ### The three-row compute tree -/

def op5Out : Fin 3 → Option (ComputeTable.State × ComputeTable.DTcomp K97cubic)
  | 0 => some op1LRow
  | 1 => some op1RRow
  | 2 => none

theorem op5Row_accepts : ComputeTable.Fcomp op5RowD op5Out := by
  refine ⟨rfl, op5_accepts, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [op5RowD, op5Out, ComputeTable.fanoutComp]
  · intro i hi
    fin_cases i
    · simp [op5Out, ComputeTable.sfTriple, op5RowD, op1LRow, op5PubD, op1LPub, op1PubOf]
    · simp [op5Out, ComputeTable.sfTriple, op5RowD, op1RRow, op5PubD, op1RPub, op1PubOf]
    · simp [op5RowD, ComputeTable.fanoutComp] at hi

theorem op1LRow_accepts : ComputeTable.Fcomp op1LRow (fun _ => none) := by
  refine ⟨rfl, op1L_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [op1LRow, ComputeTable.fanoutComp]
  · intro i hi; simp [op1LRow, ComputeTable.fanoutComp] at hi

theorem op1RRow_accepts : ComputeTable.Fcomp op1RRow (fun _ => none) := by
  refine ⟨rfl, op1R_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [op1RRow, ComputeTable.fanoutComp]
  · intro i hi; simp [op1RRow, ComputeTable.fanoutComp] at hi

def computeTreeD : NTree (ComputeTable.State × ComputeTable.DTcomp K97cubic) :=
  .node op5RowD [.node op1LRow [], .node op1RRow []]

theorem computeTreeD_rvt : RVT (ComputeTable.Fcomp (K := K97cubic)) computeTreeD := by
  unfold computeTreeD RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 3 =>
        (NTree.node op5RowD [.node op1LRow [], .node op1RRow []]).childLabel i) = op5Out by
      funext i; fin_cases i <;> rfl]
    exact op5Row_accepts
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · unfold RVT
      exact ⟨op1LRow_accepts, by simp, ⟨fun _ => op1LRow_accepts, fun _ => rfl⟩⟩
    · unfold RVT
      exact ⟨op1RRow_accepts, by simp, ⟨fun _ => op1RRow_accepts, fun _ => rfl⟩⟩
  · simp [NTree.isLeaf, ComputeTable.Fcomp, op5RowD, ComputeTable.fanoutComp]
    intro _ _ h
    exact absurd (h 0) (by simp)

/-! ## C. Generic memory-row shapes

The forest below has twenty-one rows, so the three row shapes and their `Vmem`/`WF`/`RVT`
obligations are discharged once, generically, rather than twenty-one times
. -/

abbrev MLbl := MemoryTable.MState × MemoryTable.DTmem K97cubic

def lblOf (pub : MemoryTable.Pub K97cubic) : MLbl := (pub.st, (memInputs, pub))


/-- Both LogUp challenges are zero, so the pole of a record is its root's fingerprint size. -/
theorem pole_eq_root_size (r : ComputeTable.MemRec K97cubic) :
    pole memInputs r 1 = r.root.size := by
  simp [pole, recRLC, memInputs]

theorem pole_ne_of_root (n : Noun) (r : ComputeTable.MemRec K97cubic)
    (h : r.root = encD n) : pole memInputs r 1 ≠ 0 := by
  rw [pole_eq_root_size, h]
  exact pow_ne_zero _ seedD_ne

/-! ### Form R row encode at the package `λ = formRDefault = 2`

Executed `read_root`/`verify_child` rows store `(T, C')` of their a-bearing record
(`NockVM.formRRow`/`formRCprime`); the a-bearing record (axis `a`) lives on the `…A` view. -/

/-- `λ^{n−1}` at the package `λ`. -/
def scaleD : K97cubic := MemoryTable.formRDefault ^ MemoryTable.pwScaleExp K97cubic

/-- Row-level `T` of an a-bearing record. -/
def TD (r : ComputeTable.MemRec K97cubic) : K97cubic :=
  MemoryTable.formRT MemoryTable.formRDefault (MemoryTable.nockAxisOf r.axis)

/-- Row-level `C'` of an a-bearing record. -/
def CD (r : ComputeTable.MemRec K97cubic) : K97cubic :=
  MemoryTable.formRC MemoryTable.formRDefault (MemoryTable.nockAxisOf r.axis)

/-- With `β = γ = 0` the pole reads only the root, which the row encode keeps. -/
theorem pole_row_eq (r : ComputeTable.MemRec K97cubic) :
    pole memInputs (NockVM.formRRow r MemoryTable.formRDefault)
        (NockVM.formRCprime r MemoryTable.formRDefault) = pole memInputs r 1 := by
  simp [pole, recRLC, memInputs, NockVM.formRRow]

/-! ### `halt` rows -/

def haltPub (k : ℕ) (acc : K97cubic) : MemoryTable.Pub K97cubic where
  st := .halt
  pt := ⟨encD (.atom k), 0, 0⟩
  lc := MemoryTable.Cell.zero
  rc := MemoryTable.Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := ComputeTable.MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := acc
  icur := acc

theorem haltPub_accepts (k : ℕ) (acc : K97cubic) : Vmem memInputs (haltPub k acc) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, encD, memInputs, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]
  · simp [haltPub, encD, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]

theorem haltPub_wf (k : ℕ) (acc : K97cubic) : MemoryTable.WF memInputs (haltPub k acc) where
  pole_ne h := by simp [haltPub] at h

/-! ### `decompose` rows -/

def decPub (pt lc rc : MemoryTable.Cell K97cubic) (lcSt rcSt : MemoryTable.MState)
    (acc : K97cubic) : MemoryTable.Pub K97cubic where
  st := .decompose
  pt := pt
  lc := lc
  rc := rc
  lcSt := lcSt
  rcSt := rcSt
  mem := ComputeTable.MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := acc
  icur := acc

theorem decPub_accepts {pt lc rc : MemoryTable.Cell K97cubic}
    {lcSt rcSt : MemoryTable.MState} {acc : K97cubic}
    (hn : pt.noun = ComputeTable.FP.cons seedD lc.noun rc.noun)
    (hi : pt.indicator = 2 * (lc.indicator + rc.indicator))
    (hc : pt.counts =
      lc.counts + rc.counts + (lc.indicator + rc.indicator) + rc.indicator) :
    Vmem memInputs (decPub pt lc rc lcSt rcSt acc) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨hn, ?_, ?_, rfl⟩, rfl⟩
  · simpa [decPub, Pub.lambda, MemoryTable.formRDefault] using hi
  · simp only [decPub, Pub.lambda, Option.getD_some, MemoryTable.formRDefault]
    rw [hc]; ring

theorem decPub_wf (pt lc rc : MemoryTable.Cell K97cubic) (lcSt rcSt : MemoryTable.MState)
    (acc : K97cubic) : MemoryTable.WF memInputs (decPub pt lc rc lcSt rcSt acc) where
  pole_ne h := by simp [decPub] at h

/-! ### `read_root` rows -/

def readPub (pt lc : MemoryTable.Cell K97cubic) (rec : ComputeTable.MemRec K97cubic)
    (ipre icur : K97cubic) : MemoryTable.Pub K97cubic where
  st := .read_root
  pt := pt
  lc := lc
  rc := MemoryTable.Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := NockVM.formRRow rec MemoryTable.formRDefault
  ipre := ipre
  icur := icur
  cprime? := some (NockVM.formRCprime rec MemoryTable.formRDefault)
  lambda? := some MemoryTable.formRDefault

theorem readPub_accepts {pt lc : MemoryTable.Cell K97cubic}
    {rec : ComputeTable.MemRec K97cubic} {ipre icur : K97cubic}
    (hn : pt.noun = lc.noun)
    (hi : pt.indicator = lc.indicator - scaleD * TD rec * rec.ts)
    (hc : pt.counts = lc.counts - TD rec * CD rec * rec.ts)
    (hroot : rec.root = pt.noun)
    (hacc : icur - ipre = (pole memInputs rec 1)⁻¹) :
    Vmem memInputs (readPub pt lc rec ipre icur) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨hn, rfl, ?_, ?_, hroot, rfl⟩, ?_⟩
  · simpa [readPub, Pub.lambda, scaleD, TD, NockVM.formRRow] using hi
  · simpa [readPub, Pub.cprime, TD, CD, NockVM.formRRow, NockVM.formRCprime] using hc
  · simpa [interV, readPub, Pub.cprime, pole_row_eq] using hacc

theorem readPub_wf (pt lc : MemoryTable.Cell K97cubic)
    (rec : ComputeTable.MemRec K97cubic) (ipre icur : K97cubic)
    (h : pole memInputs rec 1 ≠ 0) :
    MemoryTable.WF memInputs (readPub pt lc rec ipre icur) where
  pole_ne _ := by simpa [readPub, Pub.cprime, pole_row_eq] using h

/-! ### `verify_child` rows -/

def verifyPub (pt lc : MemoryTable.Cell K97cubic) (rec : ComputeTable.MemRec K97cubic)
    (ipre icur : K97cubic) : MemoryTable.Pub K97cubic where
  st := .verify_child
  pt := pt
  lc := lc
  rc := MemoryTable.Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := NockVM.formRRow rec MemoryTable.formRDefault
  ipre := ipre
  icur := icur
  cprime? := some (NockVM.formRCprime rec MemoryTable.formRDefault)
  lambda? := some MemoryTable.formRDefault

theorem verifyPub_accepts {pt lc : MemoryTable.Cell K97cubic}
    {rec : ComputeTable.MemRec K97cubic} {ipre icur : K97cubic}
    (hn : pt.noun = lc.noun)
    (hi : pt.indicator = lc.indicator + scaleD * rec.ts)
    (hc : pt.counts = lc.counts + scaleD * rec.ts)
    (hchild : rec.child = pt.noun)
    (hacc : ipre - icur = (pole memInputs rec 1)⁻¹) :
    Vmem memInputs (verifyPub pt lc rec ipre icur) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨hn, rfl, ?_, ?_, hchild, rfl⟩, ?_⟩
  · simpa [verifyPub, Pub.lambda, scaleD, NockVM.formRRow] using hi
  · simpa [verifyPub, Pub.lambda, scaleD, NockVM.formRRow] using hc
  · simpa [interV, verifyPub, Pub.cprime, pole_row_eq] using hacc

theorem verifyPub_wf (pt lc : MemoryTable.Cell K97cubic)
    (rec : ComputeTable.MemRec K97cubic) (ipre icur : K97cubic)
    (h : pole memInputs rec 1 ≠ 0) :
    MemoryTable.WF memInputs (verifyPub pt lc rec ipre icur) where
  pole_ne _ := by simpa [verifyPub, Pub.cprime, pole_row_eq] using h

/-- The a-bearing `read_root` row; its row encode is `readPub`. -/
@[simp] def readPubA (pt lc : MemoryTable.Cell K97cubic) (rec : ComputeTable.MemRec K97cubic)
    (ipre icur : K97cubic) : MemoryTable.Pub K97cubic :=
  { readPub pt lc rec ipre icur with mem := rec, cprime? := none }

/-- The a-bearing `verify_child` row; its row encode is `verifyPub`. -/
@[simp] def verifyPubA (pt lc : MemoryTable.Cell K97cubic) (rec : ComputeTable.MemRec K97cubic)
    (ipre icur : K97cubic) : MemoryTable.Pub K97cubic :=
  { verifyPub pt lc rec ipre icur with mem := rec, cprime? := none }

/-! ### Generic tree shapes and their `RVT` obligations -/

def mLeaf (pub : MemoryTable.Pub K97cubic) : NTree MLbl := .node (lblOf pub) []
def mOne (pub : MemoryTable.Pub K97cubic) (c : NTree MLbl) : NTree MLbl :=
  .node (lblOf pub) [c]
def mTwo (pub : MemoryTable.Pub K97cubic) (l r : NTree MLbl) : NTree MLbl :=
  .node (lblOf pub) [l, r]

theorem fmem_leaf {pub : MemoryTable.Pub K97cubic} (hv : Vmem memInputs pub)
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

theorem rvt_mLeaf {pub : MemoryTable.Pub K97cubic} (hv : Vmem memInputs pub)
    (hf : MemoryTable.fanoutMem pub.st = 0) :
    RVT (MemoryTable.Fmem (K := K97cubic)) (mLeaf pub) := by
  have hF := fmem_leaf hv hf
  unfold mLeaf RVT
  exact ⟨hF, by simp, ⟨fun _ => hF, fun _ => rfl⟩⟩

theorem rvt_mOne {pub : MemoryTable.Pub K97cubic} {c : NTree MLbl}
    (hv : Vmem memInputs pub) (hf : MemoryTable.fanoutMem pub.st = 1)
    (hpt : c.label.2.2.pt = pub.lc)
    (hc : RVT (MemoryTable.Fmem (K := K97cubic)) c) :
    RVT (MemoryTable.Fmem (K := K97cubic)) (mOne pub c) := by
  have hst : (lblOf pub).1 = pub.st := rfl
  have hF : MemoryTable.Fmem (lblOf pub)
      (fun i : Fin 2 => (mOne pub c).childLabel i) := by
    refine ⟨rfl, hv, ?_, ?_⟩
    · intro i
      fin_cases i
      · simp [hst, hf, mOne, NTree.childLabel, NTree.childOpt]
      · simp [hst, hf, mOne, NTree.childLabel, NTree.childOpt]
    · intro i hi
      fin_cases i
      · simpa [mOne, NTree.childLabel, NTree.childOpt, MemoryTable.memCell, lblOf]
          using hpt
      · rw [hst, hf] at hi
        simp at hi
  unfold mOne RVT
  refine ⟨hF, ?_, ?_⟩
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact hc
  · refine ⟨fun h => absurd h (by simp [NTree.isLeaf]), fun h => ?_⟩
    exfalso
    have h0 := h.2.2.1 ⟨0, by norm_num⟩
    rw [hst, hf] at h0
    simp at h0

theorem rvt_mTwo {pub : MemoryTable.Pub K97cubic} {l r : NTree MLbl}
    (hv : Vmem memInputs pub) (hf : MemoryTable.fanoutMem pub.st = 2)
    (hl : l.label.2.2.pt = pub.lc) (hr : r.label.2.2.pt = pub.rc)
    (hcl : RVT (MemoryTable.Fmem (K := K97cubic)) l)
    (hcr : RVT (MemoryTable.Fmem (K := K97cubic)) r) :
    RVT (MemoryTable.Fmem (K := K97cubic)) (mTwo pub l r) := by
  have hst : (lblOf pub).1 = pub.st := rfl
  have hF : MemoryTable.Fmem (lblOf pub)
      (fun i : Fin 2 => (mTwo pub l r).childLabel i) := by
    refine ⟨rfl, hv, ?_, ?_⟩
    · intro i
      fin_cases i <;>
        simp [hst, hf, mTwo, NTree.childLabel, NTree.childOpt]
    · intro i hi
      fin_cases i
      · simpa [mTwo, NTree.childLabel, NTree.childOpt, MemoryTable.memCell, lblOf] using hl
      · simpa [mTwo, NTree.childLabel, NTree.childOpt, MemoryTable.memCell, lblOf] using hr
  unfold mTwo RVT
  refine ⟨hF, ?_, ?_⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact hcl
    · exact hcr
  · refine ⟨fun h => absurd h (by simp [NTree.isLeaf]), fun h => ?_⟩
    exfalso
    have h0 := h.2.2.1 ⟨0, by norm_num⟩
    rw [hst, hf] at h0
    simp at h0

/-! ## D. The single serviced root

Twenty-one rows on the noun `op5Formula`, servicing all four committed records through four
nested `read_root`/`verify_child` pairs.  The four service timestamps are
`α, α², α³, α⁴`; the `indicator`/`counts` columns are the paper's own
`+timestamp` / `+axis·timestamp` bookkeeping. -/

/-- The four LogUp reciprocals.  Naming them keeps the whole `intermediate` accumulator symbolic,
so its twenty-one-row chain is a ring identity rather than modular arithmetic
. -/
def qF : K97cubic := (pole memInputs recF 1)⁻¹
def qT : K97cubic := (pole memInputs recT 1)⁻¹
def qL : K97cubic := (pole memInputs recL 1)⁻¹
def qR : K97cubic := (pole memInputs recR 1)⁻¹

theorem pole_recF_ne : pole memInputs recF 1 ≠ 0 := pole_ne_of_root op5Formula recF rfl
theorem pole_recT_ne : pole memInputs recT 1 ≠ 0 := pole_ne_of_root op5Tail recT rfl
theorem pole_recL_ne : pole memInputs recL 1 ≠ 0 := pole_ne_of_root leftFormula recL rfl
theorem pole_recR_ne : pole memInputs recR 1 ≠ 0 := pole_ne_of_root rightFormula recR rfl

/-! ### The twenty label cells -/

-- Form R row-level cells at `λ = 2` (`MemoryTable.eqBlk`): `verify_child`
-- adds `λ^{n−1}·ts` to both; `read_root` subtracts `λ^{n−1}·T·ts` / `T·C'·ts`; `decompose` is
-- `λ(I_L+I_R)` / `C_L+C_R+(λ−1)(I_L+I_R)+I_R`.  Each cell is written from its children.
def cH5 : MemoryTable.Cell K97cubic := ⟨encD op5Head, 0, 0⟩
def cA1 : MemoryTable.Cell K97cubic := ⟨encD op1Head, 0, 0⟩
def cA7 : MemoryTable.Cell K97cubic := ⟨encD (.atom 7), 0, 0⟩
def cA9 : MemoryTable.Cell K97cubic := ⟨encD (.atom 9), 0, 0⟩
def cA8 : MemoryTable.Cell K97cubic := ⟨encD (.atom 8), 0, 0⟩
def cA10 : MemoryTable.Cell K97cubic := ⟨encD (.atom 10), 0, 0⟩
def cOLd : MemoryTable.Cell K97cubic :=
  ⟨encD operandLeft, 2 * (cA7.indicator + cA9.indicator),
    cA7.counts + cA9.counts + (cA7.indicator + cA9.indicator) + cA9.indicator⟩
def cOL0 : MemoryTable.Cell K97cubic :=
  ⟨encD operandLeft, cOLd.indicator + scaleD * recL.ts, cOLd.counts + scaleD * recL.ts⟩
def cLd : MemoryTable.Cell K97cubic :=
  ⟨encD leftFormula, 2 * (cA1.indicator + cOL0.indicator),
    cA1.counts + cOL0.counts + (cA1.indicator + cOL0.indicator) + cOL0.indicator⟩
def cLv : MemoryTable.Cell K97cubic :=
  ⟨encD leftFormula, cLd.indicator + scaleD * recT.ts, cLd.counts + scaleD * recT.ts⟩
def cL0 : MemoryTable.Cell K97cubic :=
  ⟨encD leftFormula, cLv.indicator - scaleD * TD recL * recL.ts,
    cLv.counts - TD recL * CD recL * recL.ts⟩
def cORd : MemoryTable.Cell K97cubic :=
  ⟨encD operandRight, 2 * (cA8.indicator + cA10.indicator),
    cA8.counts + cA10.counts + (cA8.indicator + cA10.indicator) + cA10.indicator⟩
def cOR0 : MemoryTable.Cell K97cubic :=
  ⟨encD operandRight, cORd.indicator + scaleD * recR.ts, cORd.counts + scaleD * recR.ts⟩
def cRd : MemoryTable.Cell K97cubic :=
  ⟨encD rightFormula, 2 * (cA1.indicator + cOR0.indicator),
    cA1.counts + cOR0.counts + (cA1.indicator + cOR0.indicator) + cOR0.indicator⟩
def cR0 : MemoryTable.Cell K97cubic :=
  ⟨encD rightFormula, cRd.indicator - scaleD * TD recR * recR.ts,
    cRd.counts - TD recR * CD recR * recR.ts⟩
def cTd : MemoryTable.Cell K97cubic :=
  ⟨encD op5Tail, 2 * (cL0.indicator + cR0.indicator),
    cL0.counts + cR0.counts + (cL0.indicator + cR0.indicator) + cR0.indicator⟩
def cTv : MemoryTable.Cell K97cubic :=
  ⟨encD op5Tail, cTd.indicator + scaleD * recF.ts, cTd.counts + scaleD * recF.ts⟩
def cT0 : MemoryTable.Cell K97cubic :=
  ⟨encD op5Tail, cTv.indicator - scaleD * TD recT * recT.ts,
    cTv.counts - TD recT * CD recT * recT.ts⟩
def cFd : MemoryTable.Cell K97cubic :=
  ⟨encD op5Formula, 2 * (cH5.indicator + cT0.indicator),
    cH5.counts + cT0.counts + (cH5.indicator + cT0.indicator) + cT0.indicator⟩
def cF0 : MemoryTable.Cell K97cubic :=
  ⟨encD op5Formula, cFd.indicator - scaleD * TD recF * recF.ts,
    cFd.counts - TD recF * CD recF * recF.ts⟩

/-! ### The twenty-one rows -/

def pN1 : MemoryTable.Pub K97cubic := readPub cF0 cFd recF 0 qF
def pN2 : MemoryTable.Pub K97cubic := decPub cFd cH5 cT0 .halt .read_root qF
def pN3 : MemoryTable.Pub K97cubic := haltPub 5 qF
def pN4 : MemoryTable.Pub K97cubic := readPub cT0 cTv recT qF (qF + qT)
def pN5 : MemoryTable.Pub K97cubic := verifyPub cTv cTd recF (qF + qT) qT
def pN6 : MemoryTable.Pub K97cubic := decPub cTd cL0 cR0 .read_root .read_root qT
def pN7 : MemoryTable.Pub K97cubic := readPub cL0 cLv recL qT (qT + qL)
def pN8 : MemoryTable.Pub K97cubic := verifyPub cLv cLd recT (qT + qL + qR) (qL + qR)
def pN9 : MemoryTable.Pub K97cubic := decPub cLd cA1 cOL0 .halt .verify_child (qL + qR)
def pN10 : MemoryTable.Pub K97cubic := haltPub 1 qL
def pN11 : MemoryTable.Pub K97cubic := verifyPub cOL0 cOLd recL qL 0
def pN12 : MemoryTable.Pub K97cubic := decPub cOLd cA7 cA9 .halt .halt 0
def pN13 : MemoryTable.Pub K97cubic := haltPub 7 0
def pN14 : MemoryTable.Pub K97cubic := haltPub 9 0
def pN15 : MemoryTable.Pub K97cubic := readPub cR0 cRd recR (qT + qL) (qT + qL + qR)
def pN16 : MemoryTable.Pub K97cubic := decPub cRd cA1 cOR0 .halt .verify_child (qL + qR)
def pN17 : MemoryTable.Pub K97cubic := haltPub 1 (qL + qR)
def pN18 : MemoryTable.Pub K97cubic := verifyPub cOR0 cORd recR (qL + qR) qL
def pN19 : MemoryTable.Pub K97cubic := decPub cORd cA8 cA10 .halt .halt 0
def pN20 : MemoryTable.Pub K97cubic := haltPub 8 0
def pN21 : MemoryTable.Pub K97cubic := haltPub 10 0

/-! The a-bearing view of the eight active rows (same cells; record `(…, a, ts)`). -/

@[simp] def pN1A : MemoryTable.Pub K97cubic := readPubA cF0 cFd recF 0 qF
@[simp] def pN4A : MemoryTable.Pub K97cubic := readPubA cT0 cTv recT qF (qF + qT)
@[simp] def pN5A : MemoryTable.Pub K97cubic := verifyPubA cTv cTd recF (qF + qT) qT
@[simp] def pN7A : MemoryTable.Pub K97cubic := readPubA cL0 cLv recL qT (qT + qL)
@[simp] def pN8A : MemoryTable.Pub K97cubic := verifyPubA cLv cLd recT (qT + qL + qR) (qL + qR)
@[simp] def pN11A : MemoryTable.Pub K97cubic := verifyPubA cOL0 cOLd recL qL 0
@[simp] def pN15A : MemoryTable.Pub K97cubic := readPubA cR0 cRd recR (qT + qL) (qT + qL + qR)
@[simp] def pN18A : MemoryTable.Pub K97cubic := verifyPubA cOR0 cORd recR (qL + qR) qL

/-! ### `Vmem` acceptance of all twenty-one rows

Every cell is written from its children, so each row's `eqBlk` cell identities hold by
definition (`rfl`). -/

theorem pN1_accepts : Vmem memInputs pN1 :=
  readPub_accepts rfl rfl rfl rfl
    (by rw [show (pole memInputs recF 1)⁻¹ = qF from rfl, sub_zero])

theorem pN2_accepts : Vmem memInputs pN2 :=
  decPub_accepts (GlobalCarryRecognizer.enc_cons seedD_ne op5Head op5Tail) rfl rfl

theorem pN3_accepts : Vmem memInputs pN3 := haltPub_accepts 5 qF

theorem pN4_accepts : Vmem memInputs pN4 :=
  readPub_accepts rfl rfl rfl rfl
    (by rw [show (pole memInputs recT 1)⁻¹ = qT from rfl] <;> first | ring | skip)

theorem pN5_accepts : Vmem memInputs pN5 :=
  verifyPub_accepts rfl rfl rfl rfl
    (by rw [show (pole memInputs recF 1)⁻¹ = qF from rfl] <;> first | ring | skip)

theorem pN6_accepts : Vmem memInputs pN6 :=
  decPub_accepts (GlobalCarryRecognizer.enc_cons seedD_ne leftFormula rightFormula) rfl rfl

theorem pN7_accepts : Vmem memInputs pN7 :=
  readPub_accepts rfl rfl rfl rfl
    (by rw [show (pole memInputs recL 1)⁻¹ = qL from rfl] <;> first | ring | skip)

theorem pN8_accepts : Vmem memInputs pN8 :=
  verifyPub_accepts rfl rfl rfl rfl
    (by rw [show (pole memInputs recT 1)⁻¹ = qT from rfl] <;> first | ring | skip)

theorem pN9_accepts : Vmem memInputs pN9 :=
  decPub_accepts (GlobalCarryRecognizer.enc_cons seedD_ne op1Head operandLeft) rfl rfl

theorem pN10_accepts : Vmem memInputs pN10 := haltPub_accepts 1 qL

theorem pN11_accepts : Vmem memInputs pN11 :=
  verifyPub_accepts rfl rfl rfl rfl
    (by rw [show (pole memInputs recL 1)⁻¹ = qL from rfl] <;> first | ring | skip)

theorem pN12_accepts : Vmem memInputs pN12 :=
  decPub_accepts (GlobalCarryRecognizer.enc_cons seedD_ne (.atom 7) (.atom 9)) rfl rfl

theorem pN13_accepts : Vmem memInputs pN13 := haltPub_accepts 7 0
theorem pN14_accepts : Vmem memInputs pN14 := haltPub_accepts 9 0

theorem pN15_accepts : Vmem memInputs pN15 :=
  readPub_accepts rfl rfl rfl rfl
    (by rw [show (pole memInputs recR 1)⁻¹ = qR from rfl] <;> first | ring | skip)

theorem pN16_accepts : Vmem memInputs pN16 :=
  decPub_accepts (GlobalCarryRecognizer.enc_cons seedD_ne op1Head operandRight) rfl rfl

theorem pN17_accepts : Vmem memInputs pN17 := haltPub_accepts 1 (qL + qR)

theorem pN18_accepts : Vmem memInputs pN18 :=
  verifyPub_accepts rfl rfl rfl rfl
    (by rw [show (pole memInputs recR 1)⁻¹ = qR from rfl] <;> first | ring | skip)

theorem pN19_accepts : Vmem memInputs pN19 :=
  decPub_accepts (GlobalCarryRecognizer.enc_cons seedD_ne (.atom 8) (.atom 10)) rfl rfl

theorem pN20_accepts : Vmem memInputs pN20 := haltPub_accepts 8 0
theorem pN21_accepts : Vmem memInputs pN21 := haltPub_accepts 10 0

/-! ### Memory-table well-formedness -/

theorem pN1_wf : MemoryTable.WF memInputs pN1 := readPub_wf _ _ _ _ _ pole_recF_ne
theorem pN2_wf : MemoryTable.WF memInputs pN2 := decPub_wf _ _ _ _ _ _
theorem pN3_wf : MemoryTable.WF memInputs pN3 := haltPub_wf 5 qF
theorem pN4_wf : MemoryTable.WF memInputs pN4 := readPub_wf _ _ _ _ _ pole_recT_ne
theorem pN5_wf : MemoryTable.WF memInputs pN5 := verifyPub_wf _ _ _ _ _ pole_recF_ne
theorem pN6_wf : MemoryTable.WF memInputs pN6 := decPub_wf _ _ _ _ _ _
theorem pN7_wf : MemoryTable.WF memInputs pN7 := readPub_wf _ _ _ _ _ pole_recL_ne
theorem pN8_wf : MemoryTable.WF memInputs pN8 := verifyPub_wf _ _ _ _ _ pole_recT_ne
theorem pN9_wf : MemoryTable.WF memInputs pN9 := decPub_wf _ _ _ _ _ _
theorem pN10_wf : MemoryTable.WF memInputs pN10 := haltPub_wf 1 qL
theorem pN11_wf : MemoryTable.WF memInputs pN11 := verifyPub_wf _ _ _ _ _ pole_recL_ne
theorem pN12_wf : MemoryTable.WF memInputs pN12 := decPub_wf _ _ _ _ _ _
theorem pN13_wf : MemoryTable.WF memInputs pN13 := haltPub_wf 7 0
theorem pN14_wf : MemoryTable.WF memInputs pN14 := haltPub_wf 9 0
theorem pN15_wf : MemoryTable.WF memInputs pN15 := readPub_wf _ _ _ _ _ pole_recR_ne
theorem pN16_wf : MemoryTable.WF memInputs pN16 := decPub_wf _ _ _ _ _ _
theorem pN17_wf : MemoryTable.WF memInputs pN17 := haltPub_wf 1 (qL + qR)
theorem pN18_wf : MemoryTable.WF memInputs pN18 := verifyPub_wf _ _ _ _ _ pole_recR_ne
theorem pN19_wf : MemoryTable.WF memInputs pN19 := decPub_wf _ _ _ _ _ _
theorem pN20_wf : MemoryTable.WF memInputs pN20 := haltPub_wf 8 0
theorem pN21_wf : MemoryTable.WF memInputs pN21 := haltPub_wf 10 0

/-! ### The tree -/

def tN14 : NTree MLbl := mLeaf pN14
def tN13 : NTree MLbl := mLeaf pN13
def tN12 : NTree MLbl := mTwo pN12 tN13 tN14
def tN11 : NTree MLbl := mOne pN11 tN12
def tN10 : NTree MLbl := mLeaf pN10
def tN9 : NTree MLbl := mTwo pN9 tN10 tN11
def tN8 : NTree MLbl := mOne pN8 tN9
def tN7 : NTree MLbl := mOne pN7 tN8
def tN21 : NTree MLbl := mLeaf pN21
def tN20 : NTree MLbl := mLeaf pN20
def tN19 : NTree MLbl := mTwo pN19 tN20 tN21
def tN18 : NTree MLbl := mOne pN18 tN19
def tN17 : NTree MLbl := mLeaf pN17
def tN16 : NTree MLbl := mTwo pN16 tN17 tN18
def tN15 : NTree MLbl := mOne pN15 tN16
def tN6 : NTree MLbl := mTwo pN6 tN7 tN15
def tN5 : NTree MLbl := mOne pN5 tN6
def tN4 : NTree MLbl := mOne pN4 tN5
def tN3 : NTree MLbl := mLeaf pN3
def tN2 : NTree MLbl := mTwo pN2 tN3 tN4

/-- The one serviced root, on the noun `op5Formula`. -/
def rootTreeD : NTree MLbl := mOne pN1 tN2

/-! The a-bearing served tree; padding rows shared. -/

def tN11A : NTree MLbl := mOne pN11A tN12
def tN9A : NTree MLbl := mTwo pN9 tN10 tN11A
def tN8A : NTree MLbl := mOne pN8A tN9A
def tN7A : NTree MLbl := mOne pN7A tN8A
def tN18A : NTree MLbl := mOne pN18A tN19
def tN16A : NTree MLbl := mTwo pN16 tN17 tN18A
def tN15A : NTree MLbl := mOne pN15A tN16A
def tN6A : NTree MLbl := mTwo pN6 tN7A tN15A
def tN5A : NTree MLbl := mOne pN5A tN6A
def tN4A : NTree MLbl := mOne pN4A tN5A
def tN2A : NTree MLbl := mTwo pN2 tN3 tN4A
def rootTreeDA : NTree MLbl := mOne pN1A tN2A

theorem tN14_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN14 :=
  rvt_mLeaf pN14_accepts rfl
theorem tN13_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN13 :=
  rvt_mLeaf pN13_accepts rfl
theorem tN12_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN12 :=
  rvt_mTwo pN12_accepts rfl rfl rfl tN13_rvt tN14_rvt
theorem tN11_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN11 :=
  rvt_mOne pN11_accepts rfl rfl tN12_rvt
theorem tN10_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN10 :=
  rvt_mLeaf pN10_accepts rfl
theorem tN9_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN9 :=
  rvt_mTwo pN9_accepts rfl rfl rfl tN10_rvt tN11_rvt
theorem tN8_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN8 :=
  rvt_mOne pN8_accepts rfl rfl tN9_rvt
theorem tN7_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN7 :=
  rvt_mOne pN7_accepts rfl rfl tN8_rvt
theorem tN21_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN21 :=
  rvt_mLeaf pN21_accepts rfl
theorem tN20_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN20 :=
  rvt_mLeaf pN20_accepts rfl
theorem tN19_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN19 :=
  rvt_mTwo pN19_accepts rfl rfl rfl tN20_rvt tN21_rvt
theorem tN18_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN18 :=
  rvt_mOne pN18_accepts rfl rfl tN19_rvt
theorem tN17_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN17 :=
  rvt_mLeaf pN17_accepts rfl
theorem tN16_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN16 :=
  rvt_mTwo pN16_accepts rfl rfl rfl tN17_rvt tN18_rvt
theorem tN15_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN15 :=
  rvt_mOne pN15_accepts rfl rfl tN16_rvt
theorem tN6_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN6 :=
  rvt_mTwo pN6_accepts rfl rfl rfl tN7_rvt tN15_rvt
theorem tN5_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN5 :=
  rvt_mOne pN5_accepts rfl rfl tN6_rvt
theorem tN4_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN4 :=
  rvt_mOne pN4_accepts rfl rfl tN5_rvt
theorem tN3_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN3 :=
  rvt_mLeaf pN3_accepts rfl
theorem tN2_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) tN2 :=
  rvt_mTwo pN2_accepts rfl rfl rfl tN3_rvt tN4_rvt

theorem rootTreeD_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) rootTreeD :=
  rvt_mOne pN1_accepts rfl rfl tN2_rvt

/-! ## E. The exact configuration and execution

The twenty-one-row forest does not fit the released `h = 4` orbit (`2^4 = 16`).  `19` is an
element of order `32` in `F97`, hence in `K97cubic`, giving capacity `2^5 = 32`
.  The NPR seed stays `8`. -/

theorem omega19_order : orderOf (19 : K97cubic) = 32 := by
  have hbase : orderOf (19 : F97) = 32 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hpos
    interval_cases m <;> decide
  have hcast : (19 : K97cubic) = algebraMap F97 K97cubic (19 : F97) :=
    (map_natCast (algebraMap F97 K97cubic) 19).symm
  rw [hcast]
  change orderOf ((algebraMap F97 K97cubic).toMonoidHom (19 : F97)) = 32
  exact (orderOf_injective (algebraMap F97 K97cubic).toMonoidHom
    (algebraMap F97 K97cubic).injective (19 : F97)).trans hbase

def orbitD : Nock.Framework.Thm54.OrbitDomain K97cubic where
  h := 5
  ω := 19
  βcoset := 1
  βcoset_ne_zero := by norm_num
  order_ω := by simpa using omega19_order


/-- Three compute rows, twenty-one memory rows, one serviced root.  The equality-RLC
coefficient `c = 1` is the one that makes the `OP_5` gate non-degenerate. -/
def cfgD : ExactConfig F97 K97cubic where
  challenges :=
    { a := 0
      b := 0
      c := 1
      lam := MemoryTable.formRDefault
      α := alphaD
      z := seedD
      β := 0
      γ := 0 }
  Ksz := 4
  kMem := 1
  orbit := orbitD
  orbit_h_pos := by norm_num [orbitD]
  compRows := 3
  memRows := 21
  compRows_pos := by norm_num
  memRows_pos := by norm_num
  compRows_le := by norm_num [orbitD]
  memRows_le := by norm_num [orbitD]
  eDeg := 1
  eDeg_eq_one := rfl
  compNodes := fun i => orbitD.orbitPoint i
  compNodes_spec := by intro i; rfl
  memNodes := fun i => orbitD.orbitPoint i
  memNodes_spec := by intro i; rfl

/-- The fixture's configured `λ` is `formRDefault`. -/
@[simp] theorem cfgD_lam : cfgD.challenges.lam = MemoryTable.formRDefault := rfl

theorem challenge_alignmentD :
    cfgD.challenges.computeInputs = compInputs ∧
      cfgD.challenges.memoryInputs = memInputs :=
  ⟨rfl, rfl⟩

theorem seedD_cfg : cfgD.challenges.z = seedD := rfl

def execD : ExactExecution cfgD where
  computeTree := computeTreeD
  memoryForest := [rootTreeD]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTreeD, bfsForest, NTree.size, totalSize, cfgD]
  memory_bfs_length := by
    norm_num [rootTreeD, tN2, tN3, tN4, tN5, tN6, tN7, tN8, tN9, tN10, tN11, tN12, tN13,
      tN14, tN15, tN16, tN17, tN18, tN19, tN20, tN21, bfsForest, NTree.size, totalSize, cfgD,
      mOne, mTwo, mLeaf]

/-- The a-bearing view of `execD`: same compute tree; the served memory trace and all axis
accounting live here, and `execD` is its row encode (`execD_encode`). -/
def execDA : ExactExecution cfgD where
  computeTree := computeTreeD
  memoryForest := [rootTreeDA]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTreeD, bfsForest, NTree.size, totalSize, cfgD]
  memory_bfs_length := by
    norm_num [rootTreeDA, tN2A, tN3, tN4A, tN5A, tN6A, tN7A, tN8A, tN9A, tN10, tN11A, tN12,
      tN13, tN14, tN15A, tN16A, tN17, tN18A, tN19, tN20, tN21, bfsForest, NTree.size,
      totalSize, cfgD, mOne, mTwo, mLeaf]

/-- `execD` is the Form R row encode of `execDA` (`BuildableNockExecution.exec_encode`). -/
theorem execD_encode : execD = execDA.encodeMem :=
  TraceGen.RowEncode.eq_encodeMem_of rfl (by
    simp [execD, execDA, mapNTree, rootTreeD, rootTreeDA, tN2, tN2A, tN3, tN4, tN4A, tN5,
      tN5A, tN6, tN6A, tN7, tN7A, tN8, tN8A, tN9, tN9A, tN10, tN11, tN11A, tN12, tN13, tN14,
      tN15, tN15A, tN16, tN16A, tN17, tN18, tN18A, tN19, tN20, tN21, mOne, mTwo, mLeaf, lblOf,
      pN1, pN1A, pN2, pN3, pN4, pN4A, pN5, pN5A, pN6, pN7, pN7A, pN8, pN8A, pN9, pN10, pN11,
      pN11A, pN12, pN13, pN14, pN15, pN15A, pN16, pN17, pN18, pN18A, pN19, pN20, pN21,
      readPub, readPubA, verifyPub, verifyPubA, haltPub, decPub])

/-- BFS labels of the one serviced root.  The four `read_root` rows
appear at indices `0, 3, 6, 7`. -/
def memoryLabelsD : List MLbl :=
  [lblOf pN1, lblOf pN2, lblOf pN3, lblOf pN4, lblOf pN5, lblOf pN6,
    lblOf pN7, lblOf pN15, lblOf pN8, lblOf pN16, lblOf pN9, lblOf pN17,
    lblOf pN18, lblOf pN10, lblOf pN11, lblOf pN19, lblOf pN12, lblOf pN20,
    lblOf pN21, lblOf pN13, lblOf pN14]

set_option maxRecDepth 400000 in
theorem execution_rowsD :
    execD.computeRows = [op5RowD, op1LRow, op1RRow] ∧
      execD.memoryRows = memoryLabelsD := by
  constructor
  · norm_num [ExactExecution.computeRows, execD, computeTreeD, bfsForest, NTree.size,
      totalSize]
  · norm_num [ExactExecution.memoryRows, execD, memoryLabelsD, rootTreeD, tN2, tN3, tN4,
      tN5, tN6, tN7, tN8, tN9, tN10, tN11, tN12, tN13, tN14, tN15, tN16, tN17, tN18, tN19,
      tN20, tN21, bfsForest, NTree.size, totalSize, mOne, mTwo, mLeaf, lblOf]

/-! ## F. Derived IO: four requests, four responses, same order -/

theorem derived_requestsD :
    execD.derivedRequestIO =
      [encRecFormR recF formRDefault, encRecFormR recT formRDefault,
        encRecFormR recL formRDefault, encRecFormR recR formRDefault] := by
  rw [ExactExecution.derivedRequestIO_eq_computeRows, execution_rowsD.1]
  simp [NockVM.activeRequestRecords, op5RowD, op1LRow, op1RRow, op5PubD, op1LPub, op1RPub,
    op1PubOf]

theorem derived_responsesD :
    execD.derivedResponseIO =
      [encRecFormR recF formRDefault, encRecFormR recT formRDefault,
        encRecFormR recL formRDefault, encRecFormR recR formRDefault] := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, execution_rowsD.2]
  simp [memoryLabelsD, MemoryTable.responseRecords, lblOf, pN1, pN2, pN3, pN4, pN5, pN6,
    pN7, pN15, pN8, pN16, pN9, pN17, pN18, pN10, pN11, pN19, pN12, pN20, pN21, pN13, pN14,
    readPub, decPub, haltPub, verifyPub, Pub.cprime]

theorem encRec_ne_of_ts_ne {r s : ComputeTable.MemRec K97cubic} (h : r.ts ≠ s.ts) :
    encRec r ≠ encRec s := by
  intro he
  apply h
  have hc := congrFun he (7 : Fin 9)
  change r.ts = s.ts at hc
  exact hc

theorem encRecC_ne_of_ts_ne {r s : ComputeTable.MemRec K97cubic} {c : K97cubic}
    (h : r.ts ≠ s.ts) : encRecC r c ≠ encRecC s c := by
  intro he
  apply h
  have hc := congrFun he (7 : Fin 9)
  change r.ts = s.ts at hc
  exact hc

theorem encRecFormR_ne_of_ts_ne {r s : ComputeTable.MemRec K97cubic}
    (h : r.ts ≠ s.ts) : encRecFormR r formRDefault ≠ encRecFormR s formRDefault := by
  intro he
  apply h
  have hc := congrFun he (7 : Fin 9)
  change r.ts = s.ts at hc
  exact hc

private theorem natCast_ne_K97 {m n : ℕ} (hm : m < 97) (hn : n < 97) (hmn : m ≠ n) :
    (m : K97cubic) ≠ (n : K97cubic) := by
  letI : CharP K97cubic 97 := char97d
  intro h
  exact hmn (CharP.natCast_injOn_Iio K97cubic 97 (by simpa using hm) (by simpa using hn) h)

theorem ts_recF : recF.ts = alphaD ^ 1 := by simp [recF, alphaD]
theorem ts_recT : recT.ts = alphaD ^ 2 := rfl
theorem ts_recL : recL.ts = alphaD ^ 3 := rfl
theorem ts_recR : recR.ts = alphaD ^ 4 := rfl

theorem fixtureAlpha_pow_ne {m n : ℕ} (hm : m < 24) (hn : n < 24) (hmn : m ≠ n) :
    fixtureAlpha ^ m ≠ fixtureAlpha ^ n := by
  intro h
  have hord : orderOf fixtureAlpha = 24 := fixtureAlpha_order
  have : m = n :=
    pow_injOn_Iio_orderOf (x := fixtureAlpha)
      (Set.mem_Iio.mpr (by simpa [hord] using hm))
      (Set.mem_Iio.mpr (by simpa [hord] using hn)) h
  exact hmn this

theorem requestsD_nodup : execD.derivedRequestIO.Nodup := by
  rw [derived_requestsD]
  have h12 : encRecFormR recF formRDefault ≠ encRecFormR recT formRDefault :=
    encRecFormR_ne_of_ts_ne (by
      rw [ts_recF, ts_recT]
      simpa [alphaD] using
        fixtureAlpha_pow_ne (m := 1) (n := 2) (by norm_num) (by norm_num) (by norm_num))
  have h13 : encRecFormR recF formRDefault ≠ encRecFormR recL formRDefault :=
    encRecFormR_ne_of_ts_ne (by
      rw [ts_recF, ts_recL]
      simpa [alphaD] using
        fixtureAlpha_pow_ne (m := 1) (n := 3) (by norm_num) (by norm_num) (by norm_num))
  have h14 : encRecFormR recF formRDefault ≠ encRecFormR recR formRDefault :=
    encRecFormR_ne_of_ts_ne (by
      rw [ts_recF, ts_recR]
      simpa [alphaD] using
        fixtureAlpha_pow_ne (m := 1) (n := 4) (by norm_num) (by norm_num) (by norm_num))
  have h23 : encRecFormR recT formRDefault ≠ encRecFormR recL formRDefault :=
    encRecFormR_ne_of_ts_ne (by
      rw [ts_recT, ts_recL]
      simpa [alphaD] using
        fixtureAlpha_pow_ne (m := 2) (n := 3) (by norm_num) (by norm_num) (by norm_num))
  have h24 : encRecFormR recT formRDefault ≠ encRecFormR recR formRDefault :=
    encRecFormR_ne_of_ts_ne (by
      rw [ts_recT, ts_recR]
      simpa [alphaD] using
        fixtureAlpha_pow_ne (m := 2) (n := 4) (by norm_num) (by norm_num) (by norm_num))
  have h34 : encRecFormR recL formRDefault ≠ encRecFormR recR formRDefault :=
    encRecFormR_ne_of_ts_ne (by
      rw [ts_recL, ts_recR]
      simpa [alphaD] using
        fixtureAlpha_pow_ne (m := 3) (n := 4) (by norm_num) (by norm_num) (by norm_num))
  simp [h12, h13, h14, h23, h24, h34]

theorem responsesD_nodup : execD.derivedResponseIO.Nodup := by
  rw [derived_responsesD]
  simpa [derived_requestsD] using requestsD_nodup

/-! ## G. Row acceptance, genericity, and the chained boundaries -/

theorem compute_rows_acceptedD : execD.ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff, execution_rowsD.1]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl
  · exact ⟨rfl, rfl, op5_accepts⟩
  · exact ⟨rfl, rfl, op1L_accepts⟩
  · exact ⟨rfl, rfl, op1R_accepts⟩

theorem memory_rows_acceptedD : execD.MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff, execution_rowsD.2]
  intro row hrow
  simp only [memoryLabelsD, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl, pN1_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN2_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN3_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN4_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN5_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN6_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN7_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN15_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN8_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN16_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN9_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN17_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN18_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN10_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN11_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN19_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN12_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN20_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN21_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN13_accepts, rfl⟩
  · exact ⟨rfl, rfl, pN14_accepts, rfl⟩

theorem computePubAtD_zero : execD.computePubAt ⟨0, by norm_num [cfgD]⟩ = op5PubD := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt,
    execution_rowsD.1, cfgD, op5RowD]
theorem computePubAtD_one : execD.computePubAt ⟨1, by norm_num [cfgD]⟩ = op1LPub := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt,
    execution_rowsD.1, cfgD, op1LRow]
theorem computePubAtD_two : execD.computePubAt ⟨2, by norm_num [cfgD]⟩ = op1RPub := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt,
    execution_rowsD.1, cfgD, op1RRow]

theorem compute_wf_allD :
    ∀ i, ComputeTable.WF cfgD.challenges.computeInputs (execD.computePubAt i) := by
  rw [challenge_alignmentD.1]
  intro i
  fin_cases i
  · rw [computePubAtD_zero]; exact op5_wf
  · rw [computePubAtD_one]; exact op1L_wf
  · rw [computePubAtD_two]; exact op1R_wf

theorem compute_chainD :
    ∀ i : Fin cfgD.compRows, ∀ _ : (i : ℕ) + 1 < cfgD.compRows,
      (execD.computePubAt i).ln =
        (execD.computePubAt ⟨(i : ℕ) + 1, by omega⟩).ln_prev := by
  intro i hi
  fin_cases i
  · rw [computePubAtD_zero, computePubAtD_one]
    simp [op5PubD, op1LPub, op1PubOf]
  · rw [computePubAtD_one, computePubAtD_two]
    simp [op1LPub, op1RPub, op1PubOf]; ring
  · simp [cfgD] at hi

theorem memoryPubAtD_0 : execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩ = pN1 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_1 : execD.memoryPubAt ⟨1, by norm_num [cfgD]⟩ = pN2 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_2 : execD.memoryPubAt ⟨2, by norm_num [cfgD]⟩ = pN3 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_3 : execD.memoryPubAt ⟨3, by norm_num [cfgD]⟩ = pN4 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_4 : execD.memoryPubAt ⟨4, by norm_num [cfgD]⟩ = pN5 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_5 : execD.memoryPubAt ⟨5, by norm_num [cfgD]⟩ = pN6 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_6 : execD.memoryPubAt ⟨6, by norm_num [cfgD]⟩ = pN7 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_7 : execD.memoryPubAt ⟨7, by norm_num [cfgD]⟩ = pN15 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_8 : execD.memoryPubAt ⟨8, by norm_num [cfgD]⟩ = pN8 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_9 : execD.memoryPubAt ⟨9, by norm_num [cfgD]⟩ = pN16 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_10 : execD.memoryPubAt ⟨10, by norm_num [cfgD]⟩ = pN9 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_11 : execD.memoryPubAt ⟨11, by norm_num [cfgD]⟩ = pN17 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_12 : execD.memoryPubAt ⟨12, by norm_num [cfgD]⟩ = pN18 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_13 : execD.memoryPubAt ⟨13, by norm_num [cfgD]⟩ = pN10 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_14 : execD.memoryPubAt ⟨14, by norm_num [cfgD]⟩ = pN11 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_15 : execD.memoryPubAt ⟨15, by norm_num [cfgD]⟩ = pN19 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_16 : execD.memoryPubAt ⟨16, by norm_num [cfgD]⟩ = pN12 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_17 : execD.memoryPubAt ⟨17, by norm_num [cfgD]⟩ = pN20 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_18 : execD.memoryPubAt ⟨18, by norm_num [cfgD]⟩ = pN21 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_19 : execD.memoryPubAt ⟨19, by norm_num [cfgD]⟩ = pN13 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]
theorem memoryPubAtD_20 : execD.memoryPubAt ⟨20, by norm_num [cfgD]⟩ = pN14 := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsD.2,
    cfgD, memoryLabelsD, lblOf]

/-- Every census memory row carries the package `λ = formRDefault` (the row encode writes it). -/
theorem execD_lambda_unset :
    ∀ i, (execD.memoryPubAt i).lambda? = some formRDefault := by
  intro i
  fin_cases i
  · rw [memoryPubAtD_0]; rfl
  · rw [memoryPubAtD_1]; rfl
  · rw [memoryPubAtD_2]; rfl
  · rw [memoryPubAtD_3]; rfl
  · rw [memoryPubAtD_4]; rfl
  · rw [memoryPubAtD_5]; rfl
  · rw [memoryPubAtD_6]; rfl
  · rw [memoryPubAtD_7]; rfl
  · rw [memoryPubAtD_8]; rfl
  · rw [memoryPubAtD_9]; rfl
  · rw [memoryPubAtD_10]; rfl
  · rw [memoryPubAtD_11]; rfl
  · rw [memoryPubAtD_12]; rfl
  · rw [memoryPubAtD_13]; rfl
  · rw [memoryPubAtD_14]; rfl
  · rw [memoryPubAtD_15]; rfl
  · rw [memoryPubAtD_16]; rfl
  · rw [memoryPubAtD_17]; rfl
  · rw [memoryPubAtD_18]; rfl
  · rw [memoryPubAtD_19]; rfl
  · rw [memoryPubAtD_20]; rfl

/-- Halt and decompose rows carry `MemRec.zero`; read/verify rows make the inactive-state
hypotheses unsatisfiable. W4 stage 2: the all-row pole-hit half of `interFailurePairs`. -/
theorem inactive_mem_zeroD (i : Fin cfgD.memRows)
    (hnr : (execD.memoryPubAt i).st ≠ .read_root)
    (hnv : (execD.memoryPubAt i).st ≠ .verify_child) :
    (execD.memoryPubAt i).mem = ComputeTable.MemRec.zero := by
  fin_cases i <;>
    simp [memoryPubAtD_0, memoryPubAtD_1, memoryPubAtD_2, memoryPubAtD_3,
      memoryPubAtD_4, memoryPubAtD_5, memoryPubAtD_6, memoryPubAtD_7,
      memoryPubAtD_8, memoryPubAtD_9, memoryPubAtD_10, memoryPubAtD_11,
      memoryPubAtD_12, memoryPubAtD_13, memoryPubAtD_14, memoryPubAtD_15,
      memoryPubAtD_16, memoryPubAtD_17, memoryPubAtD_18, memoryPubAtD_19,
      memoryPubAtD_20, pN1, pN2, pN3, pN4, pN5, pN6, pN7, pN8, pN9, pN10,
      pN11, pN12, pN13, pN14, pN15, pN16, pN17, pN18, pN19, pN20, pN21,
      haltPub, decPub, readPub, verifyPub] at hnr hnv ⊢

/-- Inactive (`halt`/`decompose`) rows carry the default `C' = 1` (`cprime? = none`). -/
theorem inactive_cprime_oneD (i : Fin cfgD.memRows)
    (hnr : (execD.memoryPubAt i).st ≠ .read_root)
    (hnv : (execD.memoryPubAt i).st ≠ .verify_child) :
    (execD.memoryPubAt i).cprime = 1 := by
  fin_cases i <;>
    simp [memoryPubAtD_0, memoryPubAtD_1, memoryPubAtD_2, memoryPubAtD_3,
      memoryPubAtD_4, memoryPubAtD_5, memoryPubAtD_6, memoryPubAtD_7,
      memoryPubAtD_8, memoryPubAtD_9, memoryPubAtD_10, memoryPubAtD_11,
      memoryPubAtD_12, memoryPubAtD_13, memoryPubAtD_14, memoryPubAtD_15,
      memoryPubAtD_16, memoryPubAtD_17, memoryPubAtD_18, memoryPubAtD_19,
      memoryPubAtD_20, pN1, pN2, pN3, pN4, pN5, pN6, pN7, pN8, pN9, pN10,
      pN11, pN12, pN13, pN14, pN15, pN16, pN17, pN18, pN19, pN20, pN21,
      haltPub, decPub, readPub, verifyPub, MemoryTable.Pub.cprime] at hnr hnv ⊢

theorem memory_wf_allD :
    ∀ i, MemoryTable.WF cfgD.challenges.memoryInputs (execD.memoryPubAt i) := by
  rw [challenge_alignmentD.2]
  intro i
  fin_cases i
  · rw [memoryPubAtD_0]; exact pN1_wf
  · rw [memoryPubAtD_1]; exact pN2_wf
  · rw [memoryPubAtD_2]; exact pN3_wf
  · rw [memoryPubAtD_3]; exact pN4_wf
  · rw [memoryPubAtD_4]; exact pN5_wf
  · rw [memoryPubAtD_5]; exact pN6_wf
  · rw [memoryPubAtD_6]; exact pN7_wf
  · rw [memoryPubAtD_7]; exact pN15_wf
  · rw [memoryPubAtD_8]; exact pN8_wf
  · rw [memoryPubAtD_9]; exact pN16_wf
  · rw [memoryPubAtD_10]; exact pN9_wf
  · rw [memoryPubAtD_11]; exact pN17_wf
  · rw [memoryPubAtD_12]; exact pN18_wf
  · rw [memoryPubAtD_13]; exact pN10_wf
  · rw [memoryPubAtD_14]; exact pN11_wf
  · rw [memoryPubAtD_15]; exact pN19_wf
  · rw [memoryPubAtD_16]; exact pN12_wf
  · rw [memoryPubAtD_17]; exact pN20_wf
  · rw [memoryPubAtD_18]; exact pN21_wf
  · rw [memoryPubAtD_19]; exact pN13_wf
  · rw [memoryPubAtD_20]; exact pN14_wf


theorem memory_chainD :
    ∀ i : Fin cfgD.memRows, ∀ _ : (i : ℕ) + 1 < cfgD.memRows,
      (execD.memoryPubAt i).icur =
        (execD.memoryPubAt ⟨(i : ℕ) + 1, by omega⟩).ipre := by
  intro i hi
  fin_cases i
  · rw [memoryPubAtD_0, memoryPubAtD_1]; rfl
  · rw [memoryPubAtD_1, memoryPubAtD_2]; rfl
  · rw [memoryPubAtD_2, memoryPubAtD_3]; rfl
  · rw [memoryPubAtD_3, memoryPubAtD_4]; rfl
  · rw [memoryPubAtD_4, memoryPubAtD_5]; rfl
  · rw [memoryPubAtD_5, memoryPubAtD_6]; rfl
  · rw [memoryPubAtD_6, memoryPubAtD_7]; rfl
  · rw [memoryPubAtD_7, memoryPubAtD_8]; rfl
  · rw [memoryPubAtD_8, memoryPubAtD_9]; rfl
  · rw [memoryPubAtD_9, memoryPubAtD_10]; rfl
  · rw [memoryPubAtD_10, memoryPubAtD_11]; rfl
  · rw [memoryPubAtD_11, memoryPubAtD_12]; rfl
  · rw [memoryPubAtD_12, memoryPubAtD_13]; rfl
  · rw [memoryPubAtD_13, memoryPubAtD_14]; rfl
  · rw [memoryPubAtD_14, memoryPubAtD_15]; rfl
  · rw [memoryPubAtD_15, memoryPubAtD_16]; rfl
  · rw [memoryPubAtD_16, memoryPubAtD_17]; rfl
  · rw [memoryPubAtD_17, memoryPubAtD_18]; rfl
  · rw [memoryPubAtD_18, memoryPubAtD_19]; rfl
  · rw [memoryPubAtD_19, memoryPubAtD_20]; rfl
  · simp [cfgD] at hi

/-! ## H. Semantic IO preimage -/

def semF : (nmrMEF F97 K97cubic).Rec :=
  (3,
    (((encD op5Formula).size, (encD op5Formula).dyck, (encD op5Formula).leaf),
     ((encD op5Tail).size, (encD op5Tail).dyck, (encD op5Tail).leaf)),
    1)

def semT : (nmrMEF F97 K97cubic).Rec :=
  (2,
    (((encD op5Tail).size, (encD op5Tail).dyck, (encD op5Tail).leaf),
     ((encD leftFormula).size, (encD leftFormula).dyck, (encD leftFormula).leaf)),
    2)

def semL : (nmrMEF F97 K97cubic).Rec :=
  (3,
    (((encD leftFormula).size, (encD leftFormula).dyck, (encD leftFormula).leaf),
     ((encD operandLeft).size, (encD operandLeft).dyck, (encD operandLeft).leaf)),
    3)

def semR : (nmrMEF F97 K97cubic).Rec :=
  (3,
    (((encD rightFormula).size, (encD rightFormula).dyck, (encD rightFormula).leaf),
     ((encD operandRight).size, (encD operandRight).dyck, (encD operandRight).leaf)),
    4)

private theorem algebraMap_three :
    algebraMap F97 K97cubic (3 : F97) = (3 : K97cubic) := by
  simpa using (map_natCast (algebraMap F97 K97cubic) 3)

private theorem algebraMap_two :
    algebraMap F97 K97cubic (2 : F97) = (2 : K97cubic) := by
  simpa using (map_natCast (algebraMap F97 K97cubic) 2)

theorem semF_bridge :
    bridge F97 K97cubic cfgD.challenges.α cfgD.challenges.lam semF = encRecFormR recF formRDefault := by
  rw [← d2_record_bridge_agrees]
  rw [show memRecOfNMR F97 K97cubic
      ((nmrEncoding F97 K97cubic cfgD.challenges.α).encode semF) = recF by
    ext <;> norm_num [memRecOfNMR, nmrEncoding, semF, cfgD, recF, alphaD, fixtureAlpha,
      algebraMap_three]]
  rfl

theorem semT_bridge :
    bridge F97 K97cubic cfgD.challenges.α cfgD.challenges.lam semT = encRecFormR recT formRDefault := by
  rw [← d2_record_bridge_agrees]
  rw [show memRecOfNMR F97 K97cubic
      ((nmrEncoding F97 K97cubic cfgD.challenges.α).encode semT) = recT by
    ext <;> norm_num [memRecOfNMR, nmrEncoding, semT, cfgD, recT, alphaD, fixtureAlpha,
      algebraMap_two]]
  rfl

theorem semL_bridge :
    bridge F97 K97cubic cfgD.challenges.α cfgD.challenges.lam semL = encRecFormR recL formRDefault := by
  rw [← d2_record_bridge_agrees]
  rw [show memRecOfNMR F97 K97cubic
      ((nmrEncoding F97 K97cubic cfgD.challenges.α).encode semL) = recL by
    ext <;> norm_num [memRecOfNMR, nmrEncoding, semL, cfgD, recL, alphaD, fixtureAlpha,
      algebraMap_three]]
  rfl

theorem semR_bridge :
    bridge F97 K97cubic cfgD.challenges.α cfgD.challenges.lam semR = encRecFormR recR formRDefault := by
  rw [← d2_record_bridge_agrees]
  rw [show memRecOfNMR F97 K97cubic
      ((nmrEncoding F97 K97cubic cfgD.challenges.α).encode semR) = recR by
    ext <;> norm_num [memRecOfNMR, nmrEncoding, semR, cfgD, recR, alphaD, fixtureAlpha,
      algebraMap_three]]
  rfl

theorem semRecs_nodup : [semF, semT, semL, semR].Nodup := by
  have h12 : semF ≠ semT := by
    intro h
    have := congrArg (fun r : (nmrMEF F97 K97cubic).Rec => r.2.2) h
    norm_num [semF, semT] at this
  have h13 : semF ≠ semL := by
    intro h
    have := congrArg (fun r : (nmrMEF F97 K97cubic).Rec => r.2.2) h
    norm_num [semF, semL] at this
  have h14 : semF ≠ semR := by
    intro h
    have := congrArg (fun r : (nmrMEF F97 K97cubic).Rec => r.2.2) h
    norm_num [semF, semR] at this
  have h23 : semT ≠ semL := by
    intro h
    have := congrArg (fun r : (nmrMEF F97 K97cubic).Rec => r.2.2) h
    norm_num [semT, semL] at this
  have h24 : semT ≠ semR := by
    intro h
    have := congrArg (fun r : (nmrMEF F97 K97cubic).Rec => r.2.2) h
    norm_num [semT, semR] at this
  have h34 : semL ≠ semR := by
    intro h
    have := congrArg (fun r : (nmrMEF F97 K97cubic).Rec => r.2.2) h
    norm_num [semL, semR] at this
  simp [h12, h13, h14, h23, h24, h34]


def semanticPreimageD : SemanticIOPreimage cfgD execD where
  timestampBound := 5
  timestampBound_le_order := by
    change 5 ≤ orderOf fixtureAlpha
    rw [fixtureAlpha_order]
    norm_num
  semanticRequests := [semF, semT, semL, semR]
  semanticResponses := [semF, semT, semL, semR]
  requestTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> norm_num [semF, semT, semL, semR]
  responseTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> norm_num [semF, semT, semL, semR]
  semantic_lmio := by
    refine ⟨by norm_num [IO.InRange, cfgD], [semF, semT, semL, semR],
      le_refl _, semRecs_nodup, fun x => Iff.rfl, List.Perm.refl _⟩
  requestTimestamp_determines := by
    intro x hx y hy h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first | with_reducible rfl | (norm_num [semF, semT, semL, semR] at h)
  requests_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_cons, List.map_singleton,
      semF_bridge, semT_bridge, semL_bridge, semR_bridge, derived_requestsD]
  responses_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_cons, List.map_singleton,
      semF_bridge, semT_bridge, semL_bridge, semR_bridge, derived_responsesD]

theorem semantic_exactD : SemanticExactLanguage cfgD execD :=
  ⟨compute_rows_acceptedD, memory_rows_acceptedD, ⟨semanticPreimageD⟩⟩

theorem chainedD
    (hfirstD :
      (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
        (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0) :
    ChainedSemanticExactLanguage cfgD execD where
  semantic := semantic_exactD
  z_ne_zero := seedD_ne
  compute_wf := compute_wf_allD
  memory_wf := memory_wf_allD
  compute_chain := compute_chainD
  memory_chain := memory_chainD
  memory_first_counts := hfirstD.1
  memory_first_indicator := hfirstD.2
  memory_first_ipre := by rw [memoryPubAtD_0]; rfl
  memory_last_icur := by
    have hlast :
        cfgD.orbit.lastIndex cfgD.memRows cfgD.memRows_pos =
          ⟨20, by norm_num [cfgD]⟩ := rfl
    rw [hlast, memoryPubAtD_20]
    rfl
  memory_same_lambda :=
    ExactExecution.memory_same_lambda_of_const _ (some formRDefault) execD_lambda_unset

/-! ## I. Exact arity-3/2 topology -/

theorem compute_topologyD : ComputeExactTopology execD := by
  refine ⟨computeTreeD_rvt, ?_⟩
  show ProperArity 3 computeTreeD
  simp [computeTreeD]

theorem memory_topologyD : MemoryExactTopology execD := by
  intro t ht
  simp only [execD, List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht
  refine ⟨rootTreeD_rvt, ?_⟩
  simp [rootTreeD, tN2, tN3, tN4, tN5, tN6, tN7, tN8, tN9, tN10, tN11, tN12, tN13, tN14,
    tN15, tN16, tN17, tN18, tN19, tN20, tN21, mOne, mTwo, mLeaf]

theorem traversableD
    (hfirstD :
      (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
        (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0) :
    TraversableChainedSemanticExactLanguage cfgD execD where
  chained := chainedD hfirstD
  compute_topology := compute_topologyD
  memory_topology := memory_topologyD

/-! ## J. Bounded noun realization -/

theorem fpRealizedD {n : Noun} (hb : FieldEmbedding.BoundedBy 97 n) :
    FPRealized seedD 97 (encD n) :=
  ⟨n, hb, rfl⟩

theorem fpActiveD {n : Noun} (hb : FieldEmbedding.BoundedBy 97 n) :
    FPSlotRealized seedD 97 .active (encD n) :=
  ⟨fpRealizedD hb, FPRealized.ne_zero seedD_ne (fpRealizedD hb)⟩

theorem alphaD_ne : (alphaD : K97cubic) ≠ 0 := by
  simpa [alphaD, fixtureAlpha] using
    natCast_ne_K97 (m := 4) (n := 0) (by norm_num) (by norm_num) (by norm_num)

theorem recF_ne_zero : recF ≠ ComputeTable.MemRec.zero := by
  intro h
  exact alphaD_ne (by simpa [recF, ComputeTable.MemRec.zero] using congrArg MemRec.ts h)
theorem recT_ne_zero : recT ≠ ComputeTable.MemRec.zero := by
  intro h
  exact (pow_ne_zero 2 alphaD_ne)
    (by simpa [recT, ComputeTable.MemRec.zero] using congrArg MemRec.ts h)
theorem recL_ne_zero : recL ≠ ComputeTable.MemRec.zero := by
  intro h
  exact (pow_ne_zero 3 alphaD_ne)
    (by simpa [recL, ComputeTable.MemRec.zero] using congrArg MemRec.ts h)
theorem recR_ne_zero : recR ≠ ComputeTable.MemRec.zero := by
  intro h
  exact (pow_ne_zero 4 alphaD_ne)
    (by simpa [recR, ComputeTable.MemRec.zero] using congrArg MemRec.ts h)

/-- The four row-level records are pairwise distinct and nonzero: their timestamps are
`α, α², α³, α⁴` (`0` on padding). -/
theorem rowRecs_distinct :
    let F := NockVM.formRRow recF formRDefault
    let T := NockVM.formRRow recT formRDefault
    let L := NockVM.formRRow recL formRDefault
    let R := NockVM.formRRow recR formRDefault
    F ≠ T ∧ F ≠ L ∧ F ≠ R ∧ T ≠ L ∧ T ≠ R ∧ L ≠ R ∧
      ComputeTable.MemRec.zero ≠ F ∧ ComputeTable.MemRec.zero ≠ T ∧
      ComputeTable.MemRec.zero ≠ L ∧ ComputeTable.MemRec.zero ≠ R := by
  intro F T L R
  have hts : ∀ {a b : ComputeTable.MemRec K97cubic}, a.ts ≠ b.ts →
      NockVM.formRRow a formRDefault ≠ NockVM.formRRow b formRDefault :=
    fun h he => h (by simpa [NockVM.formRRow] using congrArg ComputeTable.MemRec.ts he)
  have hz : ∀ {a : ComputeTable.MemRec K97cubic}, a.ts ≠ 0 →
      ComputeTable.MemRec.zero ≠ NockVM.formRRow a formRDefault :=
    fun h he => h (by simpa [NockVM.formRRow, ComputeTable.MemRec.zero] using
      (congrArg ComputeTable.MemRec.ts he).symm)
  have hp : ∀ {m n : ℕ}, m < 24 → n < 24 → m ≠ n → alphaD ^ m ≠ alphaD ^ n :=
    fun hm hn hmn => by simpa [alphaD] using fixtureAlpha_pow_ne hm hn hmn
  refine ⟨hts ?_, hts ?_, hts ?_, hts ?_, hts ?_, hts ?_, hz ?_, hz ?_, hz ?_, hz ?_⟩
  · rw [ts_recF, ts_recT]; exact hp (by norm_num) (by norm_num) (by norm_num)
  · rw [ts_recF, ts_recL]; exact hp (by norm_num) (by norm_num) (by norm_num)
  · rw [ts_recF, ts_recR]; exact hp (by norm_num) (by norm_num) (by norm_num)
  · rw [ts_recT, ts_recL]; exact hp (by norm_num) (by norm_num) (by norm_num)
  · rw [ts_recT, ts_recR]; exact hp (by norm_num) (by norm_num) (by norm_num)
  · rw [ts_recL, ts_recR]; exact hp (by norm_num) (by norm_num) (by norm_num)
  · rw [ts_recF]; exact pow_ne_zero _ alphaD_ne
  · rw [ts_recT]; exact pow_ne_zero _ alphaD_ne
  · rw [ts_recL]; exact pow_ne_zero _ alphaD_ne
  · rw [ts_recR]; exact pow_ne_zero _ alphaD_ne

/-- Row-level `C'` is a function of the stored record on `execD`: the eight active rows store `formRRow r λ` beside
`formRCprime r λ`, padding rows `MemRec.zero` beside the default `1`, and distinct active
records have distinct timestamps. -/
theorem execD_cprimeCoherent : execD.CprimeCoherent := by
  obtain ⟨hFT, hFL, hFR, hTL, hTR, hLR, hzF, hzT, hzL, hzR⟩ := rowRecs_distinct
  refine ExactExecution.cprimeCoherent_of_fun
    (fun m => if m = NockVM.formRRow recF formRDefault then CD recF
      else if m = NockVM.formRRow recT formRDefault then CD recT
      else if m = NockVM.formRRow recL formRDefault then CD recL
      else if m = NockVM.formRRow recR formRDefault then CD recR else 1) ?_
  intro row hmem
  rw [execution_rowsD.2] at hmem
  simp only [memoryLabelsD, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [lblOf, pN1, pN2, pN3, pN4, pN5, pN6, pN7, pN15, pN8, pN16, pN9, pN17, pN18, pN10,
      pN11, pN19, pN12, pN20, pN21, pN13, pN14,
      readPub, decPub, haltPub, verifyPub, MemoryTable.Pub.cprime, NockVM.formRCprime, CD,
      hFT, hFL, hFR, hTL, hTR, hLR, hzF, hzT, hzL, hzR, Ne.symm hFT, Ne.symm hFL,
      Ne.symm hFR, Ne.symm hTL, Ne.symm hTR, Ne.symm hLR]

theorem recF_active : MemRecSlotRealized seedD 97 .active recF :=
  ⟨recF_ne_zero, fpActiveD bounded_op5Formula, fpActiveD bounded_op5Tail⟩
theorem recT_active : MemRecSlotRealized seedD 97 .active recT :=
  ⟨recT_ne_zero, fpActiveD bounded_op5Tail, fpActiveD bounded_leftFormula⟩
theorem recL_active : MemRecSlotRealized seedD 97 .active recL :=
  ⟨recL_ne_zero, fpActiveD bounded_leftFormula, fpActiveD bounded_operandLeft⟩
theorem recR_active : MemRecSlotRealized seedD 97 .active recR :=
  ⟨recR_ne_zero, fpActiveD bounded_rightFormula, fpActiveD bounded_operandRight⟩

theorem pairFaithful_self (n : Noun) (h : FieldEmbedding.BoundedBy 97 n) :
    OpcodeSemantics.PairFaithful seedD 97 n n where
  separates := fun hne => absurd rfl hne
  left_bounded := h
  right_bounded := h

theorem op5Row_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel op5RowD) where
  subject := fpActiveD bounded_op5Subject
  formula := fpActiveD bounded_op5Formula
  evaluation := fpActiveD bounded_op5Result
  subformula := by
    intro i; fin_cases i
    · exact ⟨fpActiveD bounded_op5Subject, fpActiveD bounded_leftFormula,
        fpActiveD bounded_operandLeft⟩
    · exact ⟨fpActiveD bounded_op5Subject, fpActiveD bounded_rightFormula,
        fpActiveD bounded_operandRight⟩
    · exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recF_active
    · exact recT_active
    · exact rfl

theorem op1L_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel op1LRow) where
  subject := fpActiveD bounded_op5Subject
  formula := fpActiveD bounded_leftFormula
  evaluation := fpActiveD bounded_operandLeft
  subformula := by intro i; fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recL_active
    · exact rfl
    · exact rfl

theorem op1R_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel op1RRow) where
  subject := fpActiveD bounded_op5Subject
  formula := fpActiveD bounded_rightFormula
  evaluation := fpActiveD bounded_operandRight
  subformula := by intro i; fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i; fin_cases i
    · exact recR_active
    · exact rfl
    · exact rfl

theorem computeTreeNounRealizationD :
    ComputePublicTreeNounRealization 97 execD.computePublicTree := by
  have h : (bfsForest [execD.computePublicTree]).map NTree.label
      = [computePublicLabel op5RowD, computePublicLabel op1LRow,
        computePublicLabel op1RRow] := by
    rw [ExactExecution.computePublicTree_bfs, ExactExecution.computePublicRows,
      execution_rowsD.1]
    rfl
  unfold ComputePublicTreeNounRealization ComputePublicRowsNounRealization
  rw [h]
  refine List.forall_iff_forall_mem.mpr ?_
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl
  · exact op5Row_nounRealization
  · exact op1L_nounRealization
  · exact op1R_nounRealization

theorem memSingleChildRealization (pub : MemoryTable.Pub K97cubic)
    (hst : MemoryTable.fanoutMem pub.st = 1)
    (hpt : FPSlotRealized seedD 97 .active pub.pt.noun)
    (hlc : FPSlotRealized seedD 97 .active pub.lc.noun)
    (hrc : pub.rc = MemoryTable.Cell.zero)
    (hkind : memoryMemRecKind pub.st = .active)
    (hmem : MemRecSlotRealized seedD 97 .active pub.mem) :
    MemoryPublicRowNounRealization 97 (lblOf pub) where
  parent := hpt
  child := by
    intro i; fin_cases i
    · show MemoryCellSlotRealized seedD 97 (memoryChildKind pub.st 0) pub.lc
      rw [memoryChildKind, hst]; simpa [MemoryCellSlotRealized] using hlc
    · show MemoryCellSlotRealized seedD 97 (memoryChildKind pub.st 1) pub.rc
      rw [memoryChildKind, hst]; simpa [MemoryCellSlotRealized] using hrc
  memoryRecord := by
    show MemRecSlotRealized seedD 97 (memoryMemRecKind pub.st) pub.mem
    rw [hkind]; exact hmem

theorem memDecomposeRealization (pub : MemoryTable.Pub K97cubic)
    (hpt : FPSlotRealized seedD 97 .active pub.pt.noun)
    (hlc : FPSlotRealized seedD 97 .active pub.lc.noun)
    (hrc : FPSlotRealized seedD 97 .active pub.rc.noun)
    (hmem : pub.mem = ComputeTable.MemRec.zero) :
    MemoryPublicRowNounRealization 97 (.decompose, (memInputs, pub)) where
  parent := hpt
  child := by
    intro i
    fin_cases i
    · exact hlc
    · exact hrc
  memoryRecord := hmem

theorem memHaltRealization (pub : MemoryTable.Pub K97cubic)
    (hpt : FPSlotRealized seedD 97 .active pub.pt.noun)
    (hlc : pub.lc = MemoryTable.Cell.zero)
    (hrc : pub.rc = MemoryTable.Cell.zero)
    (hmem : pub.mem = ComputeTable.MemRec.zero) :
    MemoryPublicRowNounRealization 97 (.halt, (memInputs, pub)) where
  parent := hpt
  child := by
    intro i
    fin_cases i
    · exact hlc
    · exact hrc
  memoryRecord := hmem

theorem bounded_atom (k : ℕ) (hk : k < 97) :
    FieldEmbedding.BoundedBy 97 (.atom k) := by
  simp [FieldEmbedding.BoundedBy]; exact hk

theorem pN1_realization : MemoryPublicRowNounRealization 97 (lblOf pN1) :=
  memSingleChildRealization pN1 rfl (fpActiveD bounded_op5Formula)
    (fpActiveD bounded_op5Formula) rfl rfl (recF_active.formRRow _)
theorem pN4_realization : MemoryPublicRowNounRealization 97 (lblOf pN4) :=
  memSingleChildRealization pN4 rfl (fpActiveD bounded_op5Tail)
    (fpActiveD bounded_op5Tail) rfl rfl (recT_active.formRRow _)
theorem pN5_realization : MemoryPublicRowNounRealization 97 (lblOf pN5) :=
  memSingleChildRealization pN5 rfl (fpActiveD bounded_op5Tail)
    (fpActiveD bounded_op5Tail) rfl rfl (recF_active.formRRow _)
theorem pN7_realization : MemoryPublicRowNounRealization 97 (lblOf pN7) :=
  memSingleChildRealization pN7 rfl (fpActiveD bounded_leftFormula)
    (fpActiveD bounded_leftFormula) rfl rfl (recL_active.formRRow _)
theorem pN8_realization : MemoryPublicRowNounRealization 97 (lblOf pN8) :=
  memSingleChildRealization pN8 rfl (fpActiveD bounded_leftFormula)
    (fpActiveD bounded_leftFormula) rfl rfl (recT_active.formRRow _)
theorem pN11_realization : MemoryPublicRowNounRealization 97 (lblOf pN11) :=
  memSingleChildRealization pN11 rfl (fpActiveD bounded_operandLeft)
    (fpActiveD bounded_operandLeft) rfl rfl (recL_active.formRRow _)
theorem pN15_realization : MemoryPublicRowNounRealization 97 (lblOf pN15) :=
  memSingleChildRealization pN15 rfl (fpActiveD bounded_rightFormula)
    (fpActiveD bounded_rightFormula) rfl rfl (recR_active.formRRow _)
theorem pN18_realization : MemoryPublicRowNounRealization 97 (lblOf pN18) :=
  memSingleChildRealization pN18 rfl (fpActiveD bounded_operandRight)
    (fpActiveD bounded_operandRight) rfl rfl (recR_active.formRRow _)
theorem pN2_realization : MemoryPublicRowNounRealization 97 (lblOf pN2) :=
  memDecomposeRealization pN2 (fpActiveD bounded_op5Formula)
    (fpActiveD bounded_op5Head) (fpActiveD bounded_op5Tail) rfl
theorem pN6_realization : MemoryPublicRowNounRealization 97 (lblOf pN6) :=
  memDecomposeRealization pN6 (fpActiveD bounded_op5Tail)
    (fpActiveD bounded_leftFormula) (fpActiveD bounded_rightFormula) rfl
theorem pN9_realization : MemoryPublicRowNounRealization 97 (lblOf pN9) :=
  memDecomposeRealization pN9 (fpActiveD bounded_leftFormula)
    (fpActiveD bounded_op1Head) (fpActiveD bounded_operandLeft) rfl
theorem pN12_realization : MemoryPublicRowNounRealization 97 (lblOf pN12) :=
  memDecomposeRealization pN12 (fpActiveD bounded_operandLeft)
    (fpActiveD (bounded_atom 7 (by norm_num)))
    (fpActiveD (bounded_atom 9 (by norm_num))) rfl
theorem pN16_realization : MemoryPublicRowNounRealization 97 (lblOf pN16) :=
  memDecomposeRealization pN16 (fpActiveD bounded_rightFormula)
    (fpActiveD bounded_op1Head) (fpActiveD bounded_operandRight) rfl
theorem pN19_realization : MemoryPublicRowNounRealization 97 (lblOf pN19) :=
  memDecomposeRealization pN19 (fpActiveD bounded_operandRight)
    (fpActiveD (bounded_atom 8 (by norm_num)))
    (fpActiveD (bounded_atom 10 (by norm_num))) rfl
theorem pN3_realization : MemoryPublicRowNounRealization 97 (lblOf pN3) :=
  memHaltRealization pN3 (fpActiveD bounded_op5Head) rfl rfl rfl
theorem pN10_realization : MemoryPublicRowNounRealization 97 (lblOf pN10) :=
  memHaltRealization pN10 (fpActiveD bounded_op1Head) rfl rfl rfl
theorem pN13_realization : MemoryPublicRowNounRealization 97 (lblOf pN13) :=
  memHaltRealization pN13 (fpActiveD (bounded_atom 7 (by norm_num))) rfl rfl rfl
theorem pN14_realization : MemoryPublicRowNounRealization 97 (lblOf pN14) :=
  memHaltRealization pN14 (fpActiveD (bounded_atom 9 (by norm_num))) rfl rfl rfl
theorem pN17_realization : MemoryPublicRowNounRealization 97 (lblOf pN17) :=
  memHaltRealization pN17 (fpActiveD bounded_op1Head) rfl rfl rfl
theorem pN20_realization : MemoryPublicRowNounRealization 97 (lblOf pN20) :=
  memHaltRealization pN20 (fpActiveD (bounded_atom 8 (by norm_num))) rfl rfl rfl
theorem pN21_realization : MemoryPublicRowNounRealization 97 (lblOf pN21) :=
  memHaltRealization pN21 (fpActiveD (bounded_atom 10 (by norm_num))) rfl rfl rfl

theorem memoryForestNounRealizationD :
    MemoryPublicForestNounRealization 97 execD.memoryForest := by
  unfold MemoryPublicForestNounRealization MemoryPublicRowsNounRealization
  rw [show (bfsForest execD.memoryForest).map NTree.label = execD.memoryRows from rfl,
    execution_rowsD.2]
  refine List.forall_iff_forall_mem.mpr ?_
  intro row hrow
  simp only [memoryLabelsD, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pN1_realization
  · exact pN2_realization
  · exact pN3_realization
  · exact pN4_realization
  · exact pN5_realization
  · exact pN6_realization
  · exact pN7_realization
  · exact pN15_realization
  · exact pN8_realization
  · exact pN16_realization
  · exact pN9_realization
  · exact pN17_realization
  · exact pN18_realization
  · exact pN10_realization
  · exact pN11_realization
  · exact pN19_realization
  · exact pN12_realization
  · exact pN20_realization
  · exact pN21_realization
  · exact pN13_realization
  · exact pN14_realization

theorem leafAtomD (k : ℕ) (hk : k < 97) (pub : MemoryTable.Pub K97cubic)
    (h : pub.pt.noun = encD (.atom k)) :
    MemoryLeafAtomsRealized 97 (NTree.node (.halt, (memInputs, pub)) []) :=
  ⟨k, hk, by rw [h]; simp [encD, GlobalCarryRecognizer.enc_atom]⟩

theorem leafAtoms_tN14 : MemoryLeafAtomsRealized 97 tN14 :=
  leafAtomD 9 (by norm_num) pN14 rfl
theorem leafAtoms_tN13 : MemoryLeafAtomsRealized 97 tN13 :=
  leafAtomD 7 (by norm_num) pN13 rfl
theorem leafAtoms_tN12 : MemoryLeafAtomsRealized 97 tN12 :=
  ⟨leafAtoms_tN13, leafAtoms_tN14⟩
theorem leafAtoms_tN11 : MemoryLeafAtomsRealized 97 tN11 := leafAtoms_tN12
theorem leafAtoms_tN10 : MemoryLeafAtomsRealized 97 tN10 :=
  leafAtomD 1 (by norm_num) pN10 rfl
theorem leafAtoms_tN9 : MemoryLeafAtomsRealized 97 tN9 :=
  ⟨leafAtoms_tN10, leafAtoms_tN11⟩
theorem leafAtoms_tN8 : MemoryLeafAtomsRealized 97 tN8 := leafAtoms_tN9
theorem leafAtoms_tN7 : MemoryLeafAtomsRealized 97 tN7 := leafAtoms_tN8
theorem leafAtoms_tN21 : MemoryLeafAtomsRealized 97 tN21 :=
  leafAtomD 10 (by norm_num) pN21 rfl
theorem leafAtoms_tN20 : MemoryLeafAtomsRealized 97 tN20 :=
  leafAtomD 8 (by norm_num) pN20 rfl
theorem leafAtoms_tN19 : MemoryLeafAtomsRealized 97 tN19 :=
  ⟨leafAtoms_tN20, leafAtoms_tN21⟩
theorem leafAtoms_tN18 : MemoryLeafAtomsRealized 97 tN18 := leafAtoms_tN19
theorem leafAtoms_tN17 : MemoryLeafAtomsRealized 97 tN17 :=
  leafAtomD 1 (by norm_num) pN17 rfl
theorem leafAtoms_tN16 : MemoryLeafAtomsRealized 97 tN16 :=
  ⟨leafAtoms_tN17, leafAtoms_tN18⟩
theorem leafAtoms_tN15 : MemoryLeafAtomsRealized 97 tN15 := leafAtoms_tN16
theorem leafAtoms_tN6 : MemoryLeafAtomsRealized 97 tN6 :=
  ⟨leafAtoms_tN7, leafAtoms_tN15⟩
theorem leafAtoms_tN5 : MemoryLeafAtomsRealized 97 tN5 := leafAtoms_tN6
theorem leafAtoms_tN4 : MemoryLeafAtomsRealized 97 tN4 := leafAtoms_tN5
theorem leafAtoms_tN3 : MemoryLeafAtomsRealized 97 tN3 :=
  leafAtomD 5 (by norm_num) pN3 rfl
theorem leafAtoms_tN2 : MemoryLeafAtomsRealized 97 tN2 :=
  ⟨leafAtoms_tN3, leafAtoms_tN4⟩
theorem leafAtoms_rootTreeD : MemoryLeafAtomsRealized 97 rootTreeD :=
  leafAtoms_tN2

theorem nounRealizationD : ExactExecutionNounRealization 97 cfgD execD where
  computeTree := computeTreeNounRealizationD
  memoryForest := memoryForestNounRealizationD
  memoryLeaves := by
    intro tree htree
    simp only [execD, List.mem_cons, List.not_mem_nil, or_false] at htree
    subst htree
    exact leafAtoms_rootTreeD

theorem languageD
    (hfirstD :
      (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
        (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0) :
    NounRealizedTraversableChainedSemanticExactLanguage 97 cfgD execD where
  traversable := traversableD hfirstD
  nounRealization := nounRealizationD

/-! ## K. Exact row-level semantic data

`Λ = 7` is `op5Formula.leaves`, matching `op5Census`.  The `OP_5` row's
`equalityOperand` comparison is the genuinely distinct pair `([7 9], [8 10])`. -/

def op5Root : OpcodeSemantics.RootRealization compInputs op5PubD op5Dec where
  subject := op5Subject
  formula := op5Formula
  result := op5Result
  head := op5Head
  tail := op5Tail
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def op5TailReal : OpcodeSemantics.TailRealization seedD op5Dec where
  head := leftFormula
  tail := rightFormula
  head_realizes := rfl
  tail_realizes := rfl

def op5CallL :
    OpcodeSemantics.CallRealization seedD op5PubD.sf1_s op5PubD.sf1_f op5PubD.sf1_e where
  subject := op5Subject
  formula := leftFormula
  result := operandLeft
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

def op5CallR :
    OpcodeSemantics.CallRealization seedD op5PubD.sf2_s op5PubD.sf2_f op5PubD.sf2_e where
  subject := op5Subject
  formula := rightFormula
  result := operandRight
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl

def op5Comparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op5Head, right := .atom 5 },
    { role := .formulaCons, left := op5Formula, right := .cell op5Head op5Tail },
    { role := .tailCons, left := op5Tail, right := .cell leftFormula rightFormula },
    { role := .recursiveSubject, left := op5Subject, right := op5Subject },
    { role := .recursiveFormula, left := leftFormula, right := leftFormula },
    { role := .recursiveSubject, left := op5Subject, right := op5Subject },
    { role := .recursiveFormula, left := rightFormula, right := rightFormula },
    { role := .equalityOperand, left := operandLeft, right := operandRight },
    { role := .producedResult, left := op5Result,
      right := Noun.tis operandLeft operandRight } ]

def op5RowData : ComputeRowSemanticData 97 7 op5RowD where
  root := op5Root
  tails := [op5TailReal]
  branchTails := []
  calls :=
    [ { subjectFP := op5PubD.sf1_s, formulaFP := op5PubD.sf1_f,
        resultFP := op5PubD.sf1_e, realization := op5CallL },
      { subjectFP := op5PubD.sf2_s, formulaFP := op5PubD.sf2_f,
        resultFP := op5PubD.sf2_e, realization := op5CallR } ]
  windows := []
  axisGates := []
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [op5Subject, op5Formula, op5Result]
  subject_mem := by simp [op5Root]
  formula_mem := by simp [op5Root]
  result_mem := by simp [op5Root]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · exact bounded_op5Subject
    · exact bounded_op5Formula
    · exact bounded_op5Result
  comparisons := op5Comparisons
  comparison_faithful := by
    intro c hc
    simp only [op5Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_op5Head
    · rw [← op5Formula_cons]; exact pairFaithful_self _ bounded_op5Formula
    · rw [← op5Tail_cons]; exact pairFaithful_self _ bounded_op5Tail
    · exact pairFaithful_self _ bounded_op5Subject
    · exact pairFaithful_self _ bounded_leftFormula
    · exact pairFaithful_self _ bounded_op5Subject
    · exact pairFaithful_self _ bounded_rightFormula
    · exact operands_pairFaithful
    · rw [op5Result_is_tis]; exact pairFaithful_self _ bounded_op5Result
  comparison_leaves := by
    intro c hc
    simp only [op5Comparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h | h <;> subst h
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

/-- **The census entry that is not a self-comparison**. -/
theorem op5RowData_has_distinct_equalityOperand :
    { role := .equalityOperand, left := operandLeft, right := operandRight } ∈
      op5RowData.comparisons ∧ operandLeft ≠ operandRight :=
  ⟨by simp [op5RowData, op5Comparisons], operands_ne⟩

def op1LRoot :
    OpcodeSemantics.RootRealization compInputs op1LPub (op1DecOf operandLeft) where
  subject := op5Subject
  formula := leftFormula
  result := operandLeft
  head := op1Head
  tail := operandLeft
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def op1LComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op1Head, right := .atom 1 },
    { role := .formulaCons, left := leftFormula, right := .cell op1Head operandLeft },
    { role := .producedResult, left := operandLeft, right := operandLeft } ]

def op1LRowData : ComputeRowSemanticData 97 7 op1LRow where
  root := op1LRoot
  tails := []
  branchTails := []
  calls := []
  windows := []
  axisGates := []
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [op5Subject, leftFormula, operandLeft]
  subject_mem := by simp [op1LRoot]
  formula_mem := by simp [op1LRoot]
  result_mem := by simp [op1LRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · exact bounded_op5Subject
    · exact bounded_leftFormula
    · exact bounded_operandLeft
  comparisons := op1LComparisons
  comparison_faithful := by
    intro c hc
    simp only [op1LComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_op1Head
    · rw [← leftFormula_cons]; exact pairFaithful_self _ bounded_leftFormula
    · exact pairFaithful_self _ bounded_operandLeft
  comparison_leaves := by
    intro c hc
    simp only [op1LComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h <;> exact ⟨by decide, by decide⟩
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

def op1RRoot :
    OpcodeSemantics.RootRealization compInputs op1RPub (op1DecOf operandRight) where
  subject := op5Subject
  formula := rightFormula
  result := operandRight
  head := op1Head
  tail := operandRight
  subject_realizes := rfl
  formula_realizes := rfl
  result_realizes := rfl
  head_realizes := rfl
  tail_realizes := rfl

def op1RComparisons : List ComparisonUse :=
  [ { role := .opcodeHead, left := op1Head, right := .atom 1 },
    { role := .formulaCons, left := rightFormula, right := .cell op1Head operandRight },
    { role := .producedResult, left := operandRight, right := operandRight } ]

def op1RRowData : ComputeRowSemanticData 97 7 op1RRow where
  root := op1RRoot
  tails := []
  branchTails := []
  calls := []
  windows := []
  axisGates := []
  tails_count := rfl
  branchTails_count := rfl
  calls_count := rfl
  windows_count := rfl
  axisGates_count := rfl
  realizedNouns := [op5Subject, rightFormula, operandRight]
  subject_mem := by simp [op1RRoot]
  formula_mem := by simp [op1RRoot]
  result_mem := by simp [op1RRoot]
  bounded := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h <;> subst h
    · exact bounded_op5Subject
    · exact bounded_rightFormula
    · exact bounded_operandRight
  comparisons := op1RComparisons
  comparison_faithful := by
    intro c hc
    simp only [op1RComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h
    · exact pairFaithful_self _ bounded_op1Head
    · rw [← rightFormula_cons]; exact pairFaithful_self _ bounded_rightFormula
    · exact pairFaithful_self _ bounded_operandRight
  comparison_leaves := by
    intro c hc
    simp only [op1RComparisons, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h <;> subst h <;> exact ⟨by decide, by decide⟩
  comparison_roles := rfl
  axisGate_listed := by intro gate hgate; simp at hgate
  axisGate_tail_mem := by intro gate hgate; simp at hgate
  needs :=
    { served := []
      served_count := rfl }

theorem computeRowAtD_zero :
    execD.computeRowAt ⟨0, by norm_num [cfgD]⟩ = op5RowD := by
  norm_num [ExactExecution.computeRowAt, execution_rowsD.1, cfgD]
theorem computeRowAtD_one :
    execD.computeRowAt ⟨1, by norm_num [cfgD]⟩ = op1LRow := by
  norm_num [ExactExecution.computeRowAt, execution_rowsD.1, cfgD]
theorem computeRowAtD_two :
    execD.computeRowAt ⟨2, by norm_num [cfgD]⟩ = op1RRow := by
  norm_num [ExactExecution.computeRowAt, execution_rowsD.1, cfgD]

def castRowData {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K97cubic}
    (h : row₁ = row₂) (d : ComputeRowSemanticData 97 7 row₂) :
    ComputeRowSemanticData 97 7 row₁ :=
  h.symm ▸ d

def rowDataD : ∀ i : Fin cfgD.compRows,
    ComputeRowSemanticData 97 7 (execD.computeRowAt i)
  | ⟨0, _⟩ => castRowData computeRowAtD_zero op5RowData
  | ⟨1, _⟩ => castRowData computeRowAtD_one op1LRowData
  | ⟨2, _⟩ => castRowData computeRowAtD_two op1RRowData
  | ⟨n + 3, h⟩ =>
      absurd (show n + 3 < 3 from by simpa [cfgD] using h) (by omega)

def semanticDataD
    (hfirstD :
      (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
        (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0) :
    ExactExecutionSemanticData 97 7 cfgD execD where
  language := languageD hfirstD
  rowAccepted := fun i => ExactExecution.computeRowAt_accepted compute_rows_acceptedD i
  rows := rowDataD

def lookupTuple {z : K97cubic} (l : ServedNounLookup z) :
    ComputeTable.MemRec K97cubic × Noun × ℕ × Noun :=
  (l.record, l.root, l.axis, l.child)

theorem castRowData_servedTuples
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K97cubic}
    (h : row₁ = row₂) (d : ComputeRowSemanticData 97 7 row₂) :
    (castRowData h d).needs.served.map lookupTuple = d.needs.served.map lookupTuple := by
  subst h
  rfl

theorem rowDataD_zero_servedTuples :
    (rowDataD ⟨0, by norm_num [cfgD]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAtD_zero op5RowData).trans rfl
theorem rowDataD_one_servedTuples :
    (rowDataD ⟨1, by norm_num [cfgD]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAtD_one op1LRowData).trans rfl
theorem rowDataD_two_servedTuples :
    (rowDataD ⟨2, by norm_num [cfgD]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAtD_two op1RRowData).trans rfl

/-! ## L. The exact axis tree and four services

OP_5/OP_1 have `requiredServedLookups = 0`, so `semanticCoverage` is vacuous.  The four
records are still real services on the one 21-row axis tree. -/

open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM.Thm54.ServedMemoryTrace

theorem ts_closed_recF : TimestampClosedAt cfgD.challenges.α recF.ts :=
  ⟨1, by simp [recF, cfgD, alphaD]⟩
theorem ts_closed_recT : TimestampClosedAt cfgD.challenges.α recT.ts :=
  ⟨2, rfl⟩
theorem ts_closed_recL : TimestampClosedAt cfgD.challenges.α recL.ts :=
  ⟨3, rfl⟩
theorem ts_closed_recR : TimestampClosedAt cfgD.challenges.α recR.ts :=
  ⟨4, rfl⟩

def expF : ℕ := timestampExp cfgD.challenges.α recF.ts
def expT : ℕ := timestampExp cfgD.challenges.α recT.ts
def expL : ℕ := timestampExp cfgD.challenges.α recL.ts
def expR : ℕ := timestampExp cfgD.challenges.α recR.ts

theorem ts_eq_recF : recF.ts = cfgD.challenges.α ^ expF := timestampExp_spec ts_closed_recF
theorem ts_eq_recT : recT.ts = cfgD.challenges.α ^ expT := timestampExp_spec ts_closed_recT
theorem ts_eq_recL : recL.ts = cfgD.challenges.α ^ expL := timestampExp_spec ts_closed_recL
theorem ts_eq_recR : recR.ts = cfgD.challenges.α ^ expR := timestampExp_spec ts_closed_recR

theorem expF_ne_expT : expF ≠ expT := by
  intro h
  have heq : recF.ts = recT.ts := by rw [ts_eq_recF, ts_eq_recT, h]
  rw [ts_recF, ts_recT] at heq
  exact fixtureAlpha_pow_ne (m := 1) (n := 2) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [alphaD] using heq)
theorem expF_ne_expL : expF ≠ expL := by
  intro h
  have heq : recF.ts = recL.ts := by rw [ts_eq_recF, ts_eq_recL, h]
  rw [ts_recF, ts_recL] at heq
  exact fixtureAlpha_pow_ne (m := 1) (n := 3) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [alphaD] using heq)
theorem expF_ne_expR : expF ≠ expR := by
  intro h
  have heq : recF.ts = recR.ts := by rw [ts_eq_recF, ts_eq_recR, h]
  rw [ts_recF, ts_recR] at heq
  exact fixtureAlpha_pow_ne (m := 1) (n := 4) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [alphaD] using heq)
theorem expT_ne_expF : expT ≠ expF := fun h => expF_ne_expT h.symm
theorem expT_ne_expL : expT ≠ expL := by
  intro h
  have heq : recT.ts = recL.ts := by rw [ts_eq_recT, ts_eq_recL, h]
  rw [ts_recT, ts_recL] at heq
  exact fixtureAlpha_pow_ne (m := 2) (n := 3) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [alphaD] using heq)
theorem expT_ne_expR : expT ≠ expR := by
  intro h
  have heq : recT.ts = recR.ts := by rw [ts_eq_recT, ts_eq_recR, h]
  rw [ts_recT, ts_recR] at heq
  exact fixtureAlpha_pow_ne (m := 2) (n := 4) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [alphaD] using heq)
theorem expL_ne_expF : expL ≠ expF := fun h => expF_ne_expL h.symm
theorem expL_ne_expT : expL ≠ expT := fun h => expT_ne_expL h.symm
theorem expL_ne_expR : expL ≠ expR := by
  intro h
  have heq : recL.ts = recR.ts := by rw [ts_eq_recL, ts_eq_recR, h]
  rw [ts_recL, ts_recR] at heq
  exact fixtureAlpha_pow_ne (m := 3) (n := 4) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [alphaD] using heq)
theorem expR_ne_expF : expR ≠ expF := fun h => expF_ne_expR h.symm
theorem expR_ne_expT : expR ≠ expT := fun h => expT_ne_expR h.symm
theorem expR_ne_expL : expR ≠ expL := fun h => expL_ne_expR h.symm

theorem memoryTreeAtD_zero : execDA.memoryTreeAt ⟨0, by norm_num [cfgD]⟩ = rootTreeDA := rfl


theorem axisPath_three : axisPath 3 = [true] := by
  rw [axisPath_of_two_le (by norm_num)]
  norm_num [axisPath_of_lt_two]
theorem axisPath_two : axisPath 2 = [false] := by
  rw [axisPath_of_two_le (by norm_num)]
  norm_num [axisPath_of_lt_two]

set_option maxRecDepth 400000 in
theorem axisTreeD :
    exactAxisTree cfgD execDA ⟨0, by norm_num [cfgD]⟩ =
      MTree.read expF
        (MTree.decompose MTree.halt
          (MTree.read expT
            (MTree.verify expF 3
              (MTree.decompose
                (MTree.read expL
                  (MTree.verify expT 2
                    (MTree.decompose MTree.halt
                      (MTree.verify expL 3 (MTree.decompose MTree.halt MTree.halt)))))
                (MTree.read expR
                  (MTree.decompose MTree.halt
                    (MTree.verify expR 3 (MTree.decompose MTree.halt MTree.halt)))))))) := by
  rw [exactAxisTree, memoryTreeAtD_zero]
  simp [rootTreeDA, tN2A, tN3, tN4A, tN5A, tN6A, tN7A, tN8A, tN9A, tN10, tN11A, tN12, tN13, tN14,
    tN15A, tN16A, tN17, tN18A, tN19, tN20, tN21, mOne, mTwo, mLeaf, lblOf,
    Nock.AxisBridge.ofNTree, Nock.AxisBridge.MemWalk.toMTree, timestampExpAt,
    expF, expT, expL, expR, pN1A, pN2, pN3, pN4A, pN5A, pN6, pN7A, pN8A, pN9, pN10, pN11A,
    pN12, pN13, pN14, pN15A, pN16, pN17, pN18A, pN19, pN20, pN21,
    readPub, readPubA, decPub, haltPub, verifyPub, verifyPubA, recF, recT, recL, recR]

theorem rawRequestsD :
    execDA.rawRequests = [recF, recT, recL, recR] := by
  rw [ExactExecution.rawRequests_eq_computeRows,
    show execDA.computeRows = execD.computeRows from rfl, execution_rowsD.1]
  simp [NockVM.activeRequestRecords, op5RowD, op1LRow, op1RRow, op5PubD, op1LPub, op1RPub,
    op1PubOf]

def serviceF : Service cfgD execDA where
  exponent := expF
  record := recF
  root := op5Formula
  child := op5Tail
  axis := 3
  request_mem := by rw [rawRequestsD]; simp
  timestamp := ts_eq_recF
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recF] }
  served := by simp [op5Formula, op5Tail, Noun.slot]

def serviceT : Service cfgD execDA where
  exponent := expT
  record := recT
  root := op5Tail
  child := leftFormula
  axis := 2
  request_mem := by rw [rawRequestsD]; simp
  timestamp := ts_eq_recT
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recT] }
  served := by simp [op5Tail, leftFormula, Noun.slot]

def serviceL : Service cfgD execDA where
  exponent := expL
  record := recL
  root := leftFormula
  child := operandLeft
  axis := 3
  request_mem := by rw [rawRequestsD]; simp
  timestamp := ts_eq_recL
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recL] }
  served := by simp [leftFormula, operandLeft, Noun.slot]

def serviceR : Service cfgD execDA where
  exponent := expR
  record := recR
  root := rightFormula
  child := operandRight
  axis := 3
  request_mem := by rw [rawRequestsD]; simp
  timestamp := ts_eq_recR
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recR] }
  served := by simp [rightFormula, operandRight, Noun.slot]

theorem rootResponseRecordsD :
    rootResponseRecords execDA ⟨0, by norm_num [cfgD]⟩ =
      [recF, recT, recL, recR] := by
  simp [rootResponseRecords, memoryTreeAtD_zero, rootTreeDA, tN2A, tN3, tN4A, tN5A, tN6A, tN7A,
    tN8A, tN9A, tN10, tN11A, tN12, tN13, tN14, tN15A, tN16A, tN17, tN18A, tN19, tN20, tN21,
    bfsForest, MemoryTable.responseRecords, lblOf, mOne, mTwo, mLeaf,
    pN1A, pN2, pN3, pN4A, pN5A, pN6, pN7A, pN8A, pN9, pN10, pN11A, pN12, pN13, pN14, pN15A,
    pN16, pN17, pN18A, pN19, pN20, pN21, readPub, readPubA, decPub, haltPub, verifyPub, verifyPubA]

def rootTraceD : RootTrace cfgD execDA ⟨0, by norm_num [cfgD]⟩ where
  subject := op5Formula
  services := [serviceF, serviceT, serviceL, serviceR]
  recordPartition := by rw [rootResponseRecordsD]; rfl
  readPartition := by rw [axisTreeD]; simp [serviceF, serviceT, serviceL, serviceR, readExps]
  verifyPartition := by
    rw [axisTreeD]; simp [serviceF, serviceT, serviceL, serviceR, verifyExps]
  traversal := by
    rw [axisTreeD]
    refine ServiceWalk.read serviceF (by simp) rfl rfl ?_ ?_
    · rw [show serviceF.axis = 3 from rfl, axisPath_three]
      refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
      refine VerifyRoute.read_other expT_ne_expF ?_
      exact VerifyRoute.here rfl rfl
        (by
          simp [readCount]
          repeat constructor
          all_goals
            first | exact expL_ne_expF | exact expR_ne_expF)
        (by
          simp [verifyCount]
          repeat constructor
          all_goals
            first | exact expT_ne_expF | exact expL_ne_expF | exact expR_ne_expF)
    · refine ServiceWalk.decompose ServiceWalk.halt ?_
      refine ServiceWalk.read serviceT (by simp) rfl rfl ?_ ?_
      · rw [show serviceT.axis = 2 from rfl, axisPath_two]
        refine VerifyRoute.verify_other expF_ne_expT ?_
        refine VerifyRoute.left ?_ (by simp [readCount]; exact expR_ne_expT)
          (by simp [verifyCount]; exact expR_ne_expT)
        refine VerifyRoute.read_other expL_ne_expT ?_
        exact VerifyRoute.here rfl rfl (by simp [readCount]) (by
          simp [verifyCount]
          exact expL_ne_expT)
      · exact ServiceWalk.verify
          (ServiceWalk.decompose
            (ServiceWalk.read serviceL (by simp) rfl rfl
              (by
                rw [show serviceL.axis = 3 from rfl, axisPath_three]
                refine VerifyRoute.verify_other expT_ne_expL ?_
                refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
                exact VerifyRoute.here rfl rfl (by simp [readCount]) (by simp [verifyCount]))
              (ServiceWalk.verify
                (ServiceWalk.decompose ServiceWalk.halt
                  (ServiceWalk.verify
                    (ServiceWalk.decompose ServiceWalk.halt ServiceWalk.halt)))))
            (ServiceWalk.read serviceR (by simp) rfl rfl
              (by
                rw [show serviceR.axis = 3 from rfl, axisPath_three]
                refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
                exact VerifyRoute.here rfl rfl (by simp [readCount]) (by simp [verifyCount]))
              (ServiceWalk.decompose ServiceWalk.halt
                (ServiceWalk.verify
                  (ServiceWalk.decompose ServiceWalk.halt ServiceWalk.halt)))))

def rootTracesD : ∀ i : Fin cfgD.kMem, RootTrace cfgD execDA i
  | ⟨0, _⟩ => rootTraceD
  | ⟨n + 1, h⟩ =>
      absurd (show n + 1 < 1 from by simpa [cfgD] using h) (by omega)

theorem rootTracesD_zero : rootTracesD ⟨0, by norm_num [cfgD]⟩ = rootTraceD := rfl

theorem finRange_kMemD :
    List.finRange cfgD.kMem = [⟨0, by norm_num [cfgD]⟩] := rfl

theorem forestTimestampPowersD :
    (List.finRange cfgD.kMem).flatMap (fun i => (rootTracesD i).timestampPowers) =
      [alphaD, alphaD ^ 2, alphaD ^ 3, alphaD ^ 4] := by
  rw [finRange_kMemD]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, rootTracesD_zero]
  simp only [RootTrace.timestampPowers, RootTrace.exponents, rootTraceD,
    List.map_cons, List.map_nil]
  rw [show (serviceF.exponent : ℕ) = expF from rfl,
    show (serviceT.exponent : ℕ) = expT from rfl,
    show (serviceL.exponent : ℕ) = expL from rfl,
    show (serviceR.exponent : ℕ) = expR from rfl,
    ← ts_eq_recF, ← ts_eq_recT, ← ts_eq_recL, ← ts_eq_recR,
    ts_recF, ts_recT, ts_recL, ts_recR]
  simp [alphaD, pow_one]

theorem forestTimestampPowers_nodupD :
    ((List.finRange cfgD.kMem).flatMap
      (fun i => (rootTracesD i).timestampPowers)).Nodup := by
  rw [forestTimestampPowersD]
  have h12 : alphaD ≠ alphaD ^ 2 := by
    simpa [alphaD, pow_one] using
      fixtureAlpha_pow_ne (m := 1) (n := 2) (by norm_num) (by norm_num) (by norm_num)
  have h13 : alphaD ≠ alphaD ^ 3 := by
    simpa [alphaD, pow_one] using
      fixtureAlpha_pow_ne (m := 1) (n := 3) (by norm_num) (by norm_num) (by norm_num)
  have h14 : alphaD ≠ alphaD ^ 4 := by
    simpa [alphaD, pow_one] using
      fixtureAlpha_pow_ne (m := 1) (n := 4) (by norm_num) (by norm_num) (by norm_num)
  have h23 : alphaD ^ 2 ≠ alphaD ^ 3 := by
    simpa [alphaD] using
      fixtureAlpha_pow_ne (m := 2) (n := 3) (by norm_num) (by norm_num) (by norm_num)
  have h24 : alphaD ^ 2 ≠ alphaD ^ 4 := by
    simpa [alphaD] using
      fixtureAlpha_pow_ne (m := 2) (n := 4) (by norm_num) (by norm_num) (by norm_num)
  have h34 : alphaD ^ 3 ≠ alphaD ^ 4 := by
    simpa [alphaD] using
      fixtureAlpha_pow_ne (m := 3) (n := 4) (by norm_num) (by norm_num) (by norm_num)
  simp [h12, h13, h14, h23, h24, h34]

def servedMemoryTraceD
    (hfirstD :
      (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
        (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0) :
    ExactServedMemoryTrace 97 7 cfgD execD (semanticDataD hfirstD) execDA where
  roots := rootTracesD
  timestampPowersNodup := forestTimestampPowers_nodupD
  forestIndexRange := by
    rw [forestTimestampPowersD]
    norm_num [IO.InRange, cfgD]
  semanticCoverage := by
    intro row lookup hlookup
    have hl : lookup ∈ (rowDataD row).needs.served := hlookup
    have hmem : lookupTuple lookup ∈ (rowDataD row).needs.served.map lookupTuple :=
      List.mem_map_of_mem hl
    fin_cases row
    · rw [rowDataD_zero_servedTuples] at hmem; simp at hmem
    · rw [rowDataD_one_servedTuples] at hmem; simp at hmem
    · rw [rowDataD_two_servedTuples] at hmem; simp at hmem

/-! ## M. The buildable execution

All fourteen fields named explicitly.  `recordCountBalance` is four `read_root` against four
`verify_child`.  Capacities sit under the `h = 5` orbit (`2^5 = 32`). -/

theorem ringChar_K97 : ringChar K97cubic = 97 :=
  MultiRootServedFixture.ringChar_K97

theorem memoryStateCountsD :
    RowLayout.memoryStateCount execD .read_root = 4 ∧
      RowLayout.memoryStateCount execD .verify_child = 4 ∧
      RowLayout.memoryStateCount execD .decompose = 6 ∧
      RowLayout.memoryStateCount execD .halt = 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [RowLayout.memoryStateCount, RowLayout.fibreCount, execution_rowsD.2,
      memoryLabelsD, lblOf, pN1, pN2, pN3, pN4, pN5, pN6, pN7, pN8, pN9, pN10, pN11,
      pN12, pN13, pN14, pN15, pN16, pN17, pN18, pN19, pN20, pN21,
      readPub, decPub, haltPub, verifyPub]


theorem recordCountBalanceD : RowLayout.RecordCountBalanced execD := by
  rw [RowLayout.RecordCountBalanced, memoryStateCountsD.1, memoryStateCountsD.2.1]

def distinctCensusExecution
    (hfirstD :
      (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
        (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0) :
    BuildableNockExecution F97 K97cubic where
  q := 97
  q_gt_one := by norm_num
  Λ := 7
  cfg := cfgD
  execA := execDA
  exec := execD
  exec_encode := execD_encode
  semanticData := semanticDataD hfirstD
  memoryTrace := servedMemoryTraceD hfirstD
  requestNodup := requestsD_nodup
  recordCountBalance := recordCountBalanceD
  q_le_ringChar := by rw [ringChar_K97]
  two_ne_zero := NonterminalServedRow.two_ne_zero_K97
  Ksz_lt_ringChar := by rw [ringChar_K97]; norm_num [cfgD]
  programIOCapacity := by
    rw [derived_requestsD]
    norm_num [cfgD, orbitD]
  memoryIOCapacity := by
    rw [derived_responsesD]
    norm_num [cfgD, orbitD]

end

end Nock.NockVMROM.Thm54.DistinctCensusExecution

#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.computeTreeD_rvt
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.rootTreeD_rvt
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.cfgD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.execD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.execution_rowsD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.derived_requestsD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.derived_responsesD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.requestsD_nodup
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.compute_rows_acceptedD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.memory_rows_acceptedD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.compute_wf_allD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.memory_wf_allD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.compute_chainD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.memory_chainD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.semanticPreimageD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.chainedD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.compute_topologyD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.memory_topologyD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.traversableD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.languageD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.nounRealizationD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.op5RowData
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.op5RowData_has_distinct_equalityOperand
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.op1LRowData
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.op1RRowData
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.semanticDataD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.op5RowData_has_distinct_equalityOperand
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.axisTreeD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.rootTraceD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.servedMemoryTraceD
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.distinctCensusExecution
#print axioms Nock.NockVMROM.Thm54.DistinctCensusExecution.recordCountBalanceD
