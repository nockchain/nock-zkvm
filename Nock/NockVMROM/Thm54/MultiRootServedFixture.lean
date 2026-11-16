import Nock.NockVMROM.Thm54.NonterminalServedRow
import Nock.NockVMROM.Thm54.TraceGen.RowEncode
import Nock.NockVMROM.Thm54.BuildablePackage

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# A two-serviced-root nonterminal fixture at a repaired seed

This module builds the multi-root memory fixture that the nonterminal `OP_0` row data of
`NonterminalServedRow` was missing.  Everything lives at the repaired seed
`NonterminalServedRow.servedSeed = -1` over the same cubic field `K97cubic`, so
`OpcodeSemantics.SizeWindow` exists for every atom and the compute-side row data of that module is
reused verbatim.

**The compute side** is `NonterminalServedRow.computeTreeS`: an `OP_4` parent whose
single recursive call is the genuine `OP_0` served row.  Its three emitted requests
 are

* `parentRecordS` — the `OP_4` row's `mr1`, root `parentFormulaS`, axis `3`, timestamp `α`;
* `servedFormulaRecord` — the `OP_0` row's `mr1`, root `formulaS`, axis `3`, timestamp `α²`;
* `servedRecord` — the `OP_0` row's `mr2`, the actual slot lookup, root `subjectS`, axis `2`,
  timestamp `α³`.

**The memory side** is a fourteen-row forest with **two serviced roots**:

* root `A` is rooted at the noun `parentFormulaS` and serves `parentRecordS` and
  `servedFormulaRecord` through nested `read_root`/`verify_child` pairs (nine rows);
* root `B` is rooted at the noun `subjectS` and serves `servedRecord` on a genuine **left**
  descent, `axisPath 2 = [false]` (five rows).

Both roots carry records, so the aggregate `intermediate` accumulator of the paper genuinely
interleaves the two roots in the BFS order

`A.read, B.read, A.decompose, B.decompose, A.halt, A.read, B.verify, B.halt, A.verify, B.halt,`
`A.decompose, A.halt, A.verify, A.halt`

and its value sequence is `0, -1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0`, closing at zero
.  This is the first fixture in which `timestampPowersNodup` is a genuinely
**cross-root** condition.
-/

namespace Nock.NockVMROM.Thm54.MultiRootServedFixture

open scoped Classical
open Nock Nock.Noun Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97m : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97m : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-! ## A. Seed, field constants and the served nouns -/


/-- The right-hand halt noun of root `B`; `subjectS = [7 9]` so `axis 2` is a real left descent. -/
def bTailNoun : Noun := .atom 9

theorem subjectS_cons : subjectS = .cell resultS bTailNoun := rfl

theorem parentFormulaS_cons : parentFormulaS = .cell parentHeadS formulaS := rfl

theorem formulaS_cons : formulaS = .cell headS tailS := rfl

/-- Memory-table RAP inputs at the repaired seed.  Both LogUp challenges are zero, as in the
existing F97 fixture, so the pole is the record's root size. -/
def memInputsS : MemoryTable.Inputs K97cubic := ⟨servedSeed, 0, 0⟩

theorem memInputsS_z : memInputsS.z = servedSeed := rfl

/-! ## B. LogUp poles of the three served records -/

theorem pole_parentRecordS : pole memInputsS parentRecordS 1 = -1 := by
  norm_num [pole, recRLC, memInputsS, parentRecordS, encS, parentFormulaS, parentHeadS,
    formulaS, headS, tailS, servedSeed, GlobalCarryRecognizer.enc_size, Noun.leaves]

theorem pole_servedFormulaRecord : pole memInputsS servedFormulaRecord 1 = 1 := by
  norm_num [pole, recRLC, memInputsS, servedFormulaRecord, encS, formulaS, headS, tailS,
    servedSeed, GlobalCarryRecognizer.enc_size, Noun.leaves]

theorem pole_servedRecord : pole memInputsS servedRecord 1 = 1 := by
  norm_num [pole, recRLC, memInputsS, servedRecord, encS, subjectS, resultS,
    servedSeed, GlobalCarryRecognizer.enc_size, Noun.leaves]

theorem pole_parentRecordS_ne : pole memInputsS parentRecordS 1 ≠ 0 := by
  rw [pole_parentRecordS]
  exact neg_ne_zero.mpr one_ne_zero

theorem pole_servedFormulaRecord_ne : pole memInputsS servedFormulaRecord 1 ≠ 0 := by
  rw [pole_servedFormulaRecord]; norm_num

theorem pole_servedRecord_ne : pole memInputsS servedRecord 1 ≠ 0 := by
  rw [pole_servedRecord]; norm_num

/-! ## C. Timestamps -/

theorem ts_parentRecordS : parentRecordS.ts = 4 := by
  norm_num [parentRecordS, fixtureAlpha]

theorem ts_servedFormulaRecord : servedFormulaRecord.ts = 16 := by
  norm_num [servedFormulaRecord, fixtureAlpha]

theorem ts_servedRecord : servedRecord.ts = 64 := by
  norm_num [servedRecord, fixtureAlpha]

/-! ## D. Root `A`: the nine-row nested-service tree on `parentFormulaS` -/

-- Form R row-level cells at `λ = formRDefault` (`OptimizedStrictNonterminalConcrete.rowVerifyCell`

def aTailCell : Cell K97cubic := ⟨encS tailS, 0, 0⟩
def aInnerVerifyCell : Cell K97cubic := rowVerifyCell (encS tailS) aTailCell servedFormulaRecord.ts
def aInnerHeadCell : Cell K97cubic := ⟨encS headS, 0, 0⟩
def aInnerLiftCell : Cell K97cubic := rowDecCell (encS formulaS) aInnerHeadCell aInnerVerifyCell
def aOuterVerifyCell : Cell K97cubic :=
  rowVerifyCell (encS formulaS) aInnerLiftCell parentRecordS.ts
def aInnerRootCell : Cell K97cubic :=
  rowReadCell (encS formulaS) aOuterVerifyCell servedFormulaRecord
def aHeadCell : Cell K97cubic := ⟨encS parentHeadS, 0, 0⟩
def aLiftCell : Cell K97cubic := rowDecCell (encS parentFormulaS) aHeadCell aInnerRootCell
def aRootCell : Cell K97cubic := rowReadCell (encS parentFormulaS) aLiftCell parentRecordS

def aReadOuterPub : MemoryTable.Pub K97cubic where
  st := .read_root
  pt := aRootCell
  lc := aLiftCell
  rc := Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := NockVM.formRRow parentRecordS MemoryTable.formRDefault
  cprime? := some (NockVM.formRCprime parentRecordS MemoryTable.formRDefault)
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := -1

def aDecomposeOuterPub : MemoryTable.Pub K97cubic where
  st := .decompose
  pt := aLiftCell
  lc := aHeadCell
  rc := aInnerRootCell
  lcSt := .halt
  rcSt := .read_root
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

def aHeadHaltPub : MemoryTable.Pub K97cubic where
  st := .halt
  pt := aHeadCell
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

def aReadInnerPub : MemoryTable.Pub K97cubic where
  st := .read_root
  pt := aInnerRootCell
  lc := aOuterVerifyCell
  rc := Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := NockVM.formRRow servedFormulaRecord MemoryTable.formRDefault
  cprime? := some (NockVM.formRCprime servedFormulaRecord MemoryTable.formRDefault)
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 1

def aVerifyOuterPub : MemoryTable.Pub K97cubic where
  st := .verify_child
  pt := aOuterVerifyCell
  lc := aInnerLiftCell
  rc := Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := NockVM.formRRow parentRecordS MemoryTable.formRDefault
  cprime? := some (NockVM.formRCprime parentRecordS MemoryTable.formRDefault)
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 1

def aDecomposeInnerPub : MemoryTable.Pub K97cubic where
  st := .decompose
  pt := aInnerLiftCell
  lc := aInnerHeadCell
  rc := aInnerVerifyCell
  lcSt := .halt
  rcSt := .verify_child
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 1

def aInnerHeadHaltPub : MemoryTable.Pub K97cubic where
  st := .halt
  pt := aInnerHeadCell
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 1

def aVerifyInnerPub : MemoryTable.Pub K97cubic where
  st := .verify_child
  pt := aInnerVerifyCell
  lc := aTailCell
  rc := Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := NockVM.formRRow servedFormulaRecord MemoryTable.formRDefault
  cprime? := some (NockVM.formRCprime servedFormulaRecord MemoryTable.formRDefault)
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 0

def aTailHaltPub : MemoryTable.Pub K97cubic where
  st := .halt
  pt := aTailCell
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

/-! ## E. Root `B`: the five-row left-descent tree on `subjectS` -/

def bResultHaltCell : Cell K97cubic := ⟨encS resultS, 0, 0⟩
def bTailHaltCell : Cell K97cubic := ⟨encS bTailNoun, 0, 0⟩
def bVerifyCell : Cell K97cubic := rowVerifyCell (encS resultS) bResultHaltCell servedRecord.ts
def bLiftCell : Cell K97cubic := rowDecCell (encS subjectS) bVerifyCell bTailHaltCell
def bRootCell : Cell K97cubic := rowReadCell (encS subjectS) bLiftCell servedRecord

def bReadPub : MemoryTable.Pub K97cubic where
  st := .read_root
  pt := bRootCell
  lc := bLiftCell
  rc := Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := NockVM.formRRow servedRecord MemoryTable.formRDefault
  cprime? := some (NockVM.formRCprime servedRecord MemoryTable.formRDefault)
  lambda? := some MemoryTable.formRDefault
  ipre := -1
  icur := 0

def bDecomposePub : MemoryTable.Pub K97cubic where
  st := .decompose
  pt := bLiftCell
  lc := bVerifyCell
  rc := bTailHaltCell
  lcSt := .verify_child
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

def bVerifyPub : MemoryTable.Pub K97cubic where
  st := .verify_child
  pt := bVerifyCell
  lc := bResultHaltCell
  rc := Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := NockVM.formRRow servedRecord MemoryTable.formRDefault
  cprime? := some (NockVM.formRCprime servedRecord MemoryTable.formRDefault)
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 0

def bResultHaltPub : MemoryTable.Pub K97cubic where
  st := .halt
  pt := bResultHaltCell
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 1

def bTailHaltPub : MemoryTable.Pub K97cubic where
  st := .halt
  pt := bTailHaltCell
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

/-! The a-bearing view of the six active rows; their Form R row encode is the
executed row. -/

@[simp] def aReadOuterPubA : MemoryTable.Pub K97cubic :=
  { aReadOuterPub with mem := parentRecordS, cprime? := none }
@[simp] def aReadInnerPubA : MemoryTable.Pub K97cubic :=
  { aReadInnerPub with mem := servedFormulaRecord, cprime? := none }
@[simp] def aVerifyOuterPubA : MemoryTable.Pub K97cubic :=
  { aVerifyOuterPub with mem := parentRecordS, cprime? := none }
@[simp] def aVerifyInnerPubA : MemoryTable.Pub K97cubic :=
  { aVerifyInnerPub with mem := servedFormulaRecord, cprime? := none }
@[simp] def bReadPubA : MemoryTable.Pub K97cubic :=
  { bReadPub with mem := servedRecord, cprime? := none }
@[simp] def bVerifyPubA : MemoryTable.Pub K97cubic :=
  { bVerifyPub with mem := servedRecord, cprime? := none }

/-- With `β = γ = 0` the pole reads only the root, which the Form R row encode keeps. -/
@[simp] theorem pole_rowS (r : ComputeTable.MemRec K97cubic) :
    pole memInputsS (NockVM.formRRow r MemoryTable.formRDefault)
      (NockVM.formRCprime r MemoryTable.formRDefault) = pole memInputsS r 1 := by
  simp [pole, recRLC, memInputsS, NockVM.formRRow]

/-! ## F. `Vmem` acceptance of all fourteen rows -/

theorem aReadOuter_accepts : Vmem memInputsS aReadOuterPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp only [eqBlk, aReadOuterPub]
    repeat' constructor
  · change aReadOuterPub.icur - aReadOuterPub.ipre =
      (pole memInputsS aReadOuterPub.mem aReadOuterPub.cprime)⁻¹
    rw [show aReadOuterPub.mem = NockVM.formRRow parentRecordS MemoryTable.formRDefault from rfl,
      show aReadOuterPub.cprime =
        NockVM.formRCprime parentRecordS MemoryTable.formRDefault from rfl, pole_rowS,
      pole_parentRecordS, inv_neg_one]
    simp [aReadOuterPub]

theorem aDecomposeOuter_accepts : Vmem memInputsS aDecomposeOuterPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, rfl⟩
    · show aLiftCell.noun = FP.cons servedSeed aHeadCell.noun aInnerRootCell.noun
      rw [show aLiftCell.noun = encS parentFormulaS from rfl,
        show aHeadCell.noun = encS parentHeadS from rfl,
        show aInnerRootCell.noun = encS formulaS from rfl, parentFormulaS_cons]
      exact GlobalCarryRecognizer.enc_cons servedSeed_ne parentHeadS formulaS
    · rfl
    · rfl
  · rfl

theorem aHeadHalt_accepts : Vmem memInputsS aHeadHaltPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simp [aHeadHaltPub, aHeadCell, encS, parentHeadS, memInputsS,
        GlobalCarryRecognizer.enc_atom]
    · simp [aHeadHaltPub, aHeadCell, encS, parentHeadS, GlobalCarryRecognizer.enc_atom]
  · rfl

theorem aReadInner_accepts : Vmem memInputsS aReadInnerPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp only [eqBlk, aReadInnerPub]
    repeat' constructor
  · change aReadInnerPub.icur - aReadInnerPub.ipre =
      (pole memInputsS aReadInnerPub.mem aReadInnerPub.cprime)⁻¹
    rw [show aReadInnerPub.mem =
      NockVM.formRRow servedFormulaRecord MemoryTable.formRDefault from rfl,
      show aReadInnerPub.cprime =
        NockVM.formRCprime servedFormulaRecord MemoryTable.formRDefault from rfl, pole_rowS,
      pole_servedFormulaRecord, inv_one]
    simp [aReadInnerPub]

theorem aVerifyOuter_accepts : Vmem memInputsS aVerifyOuterPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp only [eqBlk, aVerifyOuterPub]
    repeat' constructor
  · change aVerifyOuterPub.ipre - aVerifyOuterPub.icur =
      (pole memInputsS aVerifyOuterPub.mem aVerifyOuterPub.cprime)⁻¹
    rw [show aVerifyOuterPub.mem = NockVM.formRRow parentRecordS MemoryTable.formRDefault from rfl,
      show aVerifyOuterPub.cprime =
        NockVM.formRCprime parentRecordS MemoryTable.formRDefault from rfl, pole_rowS,
      pole_parentRecordS, inv_neg_one]
    simp [aVerifyOuterPub]

theorem aDecomposeInner_accepts : Vmem memInputsS aDecomposeInnerPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, rfl⟩
    · show aInnerLiftCell.noun = FP.cons servedSeed aInnerHeadCell.noun aInnerVerifyCell.noun
      rw [show aInnerLiftCell.noun = encS formulaS from rfl,
        show aInnerHeadCell.noun = encS headS from rfl,
        show aInnerVerifyCell.noun = encS tailS from rfl, formulaS_cons]
      exact GlobalCarryRecognizer.enc_cons servedSeed_ne headS tailS
    · rfl
    · rfl
  · rfl

theorem aInnerHeadHalt_accepts : Vmem memInputsS aInnerHeadHaltPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simp [aInnerHeadHaltPub, aInnerHeadCell, encS, headS, memInputsS,
        GlobalCarryRecognizer.enc_atom]
    · simp [aInnerHeadHaltPub, aInnerHeadCell, encS, headS, GlobalCarryRecognizer.enc_atom]
  · rfl

theorem aVerifyInner_accepts : Vmem memInputsS aVerifyInnerPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp only [eqBlk, aVerifyInnerPub]
    repeat' constructor
  · change aVerifyInnerPub.ipre - aVerifyInnerPub.icur =
      (pole memInputsS aVerifyInnerPub.mem aVerifyInnerPub.cprime)⁻¹
    rw [show aVerifyInnerPub.mem =
      NockVM.formRRow servedFormulaRecord MemoryTable.formRDefault from rfl,
      show aVerifyInnerPub.cprime =
        NockVM.formRCprime servedFormulaRecord MemoryTable.formRDefault from rfl, pole_rowS,
      pole_servedFormulaRecord, inv_one]
    simp [aVerifyInnerPub]

theorem aTailHalt_accepts : Vmem memInputsS aTailHaltPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simp [aTailHaltPub, aTailCell, encS, tailS, memInputsS, GlobalCarryRecognizer.enc_atom]
    · simp [aTailHaltPub, aTailCell, encS, tailS, GlobalCarryRecognizer.enc_atom]
  · rfl

theorem bRead_accepts : Vmem memInputsS bReadPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp only [eqBlk, bReadPub]
    repeat' constructor
  · change bReadPub.icur - bReadPub.ipre =
      (pole memInputsS bReadPub.mem bReadPub.cprime)⁻¹
    rw [show bReadPub.mem = NockVM.formRRow servedRecord MemoryTable.formRDefault from rfl,
      show bReadPub.cprime =
        NockVM.formRCprime servedRecord MemoryTable.formRDefault from rfl, pole_rowS,
      pole_servedRecord, inv_one]
    simp [bReadPub]

theorem bDecompose_accepts : Vmem memInputsS bDecomposePub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, rfl⟩
    · show bLiftCell.noun = FP.cons servedSeed bVerifyCell.noun bTailHaltCell.noun
      rw [show bLiftCell.noun = encS subjectS from rfl,
        show bVerifyCell.noun = encS resultS from rfl,
        show bTailHaltCell.noun = encS bTailNoun from rfl, subjectS_cons]
      exact GlobalCarryRecognizer.enc_cons servedSeed_ne resultS bTailNoun
    · rfl
    · rfl
  · rfl

theorem bVerify_accepts : Vmem memInputsS bVerifyPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp only [eqBlk, bVerifyPub]
    repeat' constructor
  · change bVerifyPub.ipre - bVerifyPub.icur =
      (pole memInputsS bVerifyPub.mem bVerifyPub.cprime)⁻¹
    rw [show bVerifyPub.mem = NockVM.formRRow servedRecord MemoryTable.formRDefault from rfl,
      show bVerifyPub.cprime =
        NockVM.formRCprime servedRecord MemoryTable.formRDefault from rfl, pole_rowS,
      pole_servedRecord, inv_one]
    simp [bVerifyPub]

theorem bResultHalt_accepts : Vmem memInputsS bResultHaltPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simp [bResultHaltPub, bResultHaltCell, encS, resultS, memInputsS,
        GlobalCarryRecognizer.enc_atom]
    · simp [bResultHaltPub, bResultHaltCell, encS, resultS, GlobalCarryRecognizer.enc_atom]
  · rfl

theorem bTailHalt_accepts : Vmem memInputsS bTailHaltPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simp [bTailHaltPub, bTailHaltCell, encS, bTailNoun, memInputsS,
        GlobalCarryRecognizer.enc_atom]
    · simp [bTailHaltPub, bTailHaltCell, encS, bTailNoun, GlobalCarryRecognizer.enc_atom]
  · rfl

/-! ## G. Memory-table well-formedness -/

theorem aReadOuter_wf : MemoryTable.WF memInputsS aReadOuterPub where
  pole_ne _ := by
    show pole memInputsS aReadOuterPub.mem aReadOuterPub.cprime ≠ 0
    simpa [aReadOuterPub, Pub.cprime] using pole_parentRecordS_ne

theorem aDecomposeOuter_wf : MemoryTable.WF memInputsS aDecomposeOuterPub where
  pole_ne h := by simp [aDecomposeOuterPub] at h

theorem aHeadHalt_wf : MemoryTable.WF memInputsS aHeadHaltPub where
  pole_ne h := by simp [aHeadHaltPub] at h

theorem aReadInner_wf : MemoryTable.WF memInputsS aReadInnerPub where
  pole_ne _ := by
    show pole memInputsS aReadInnerPub.mem aReadInnerPub.cprime ≠ 0
    simpa [aReadInnerPub, Pub.cprime] using pole_servedFormulaRecord_ne

theorem aVerifyOuter_wf : MemoryTable.WF memInputsS aVerifyOuterPub where
  pole_ne _ := by
    show pole memInputsS aVerifyOuterPub.mem aVerifyOuterPub.cprime ≠ 0
    simpa [aVerifyOuterPub, Pub.cprime] using pole_parentRecordS_ne

theorem aDecomposeInner_wf : MemoryTable.WF memInputsS aDecomposeInnerPub where
  pole_ne h := by simp [aDecomposeInnerPub] at h

theorem aInnerHeadHalt_wf : MemoryTable.WF memInputsS aInnerHeadHaltPub where
  pole_ne h := by simp [aInnerHeadHaltPub] at h

theorem aVerifyInner_wf : MemoryTable.WF memInputsS aVerifyInnerPub where
  pole_ne _ := by
    show pole memInputsS aVerifyInnerPub.mem aVerifyInnerPub.cprime ≠ 0
    simpa [aVerifyInnerPub, Pub.cprime] using pole_servedFormulaRecord_ne

theorem aTailHalt_wf : MemoryTable.WF memInputsS aTailHaltPub where
  pole_ne h := by simp [aTailHaltPub] at h

theorem bRead_wf : MemoryTable.WF memInputsS bReadPub where
  pole_ne _ := by
    show pole memInputsS bReadPub.mem bReadPub.cprime ≠ 0
    simpa [bReadPub, Pub.cprime] using pole_servedRecord_ne

theorem bDecompose_wf : MemoryTable.WF memInputsS bDecomposePub where
  pole_ne h := by simp [bDecomposePub] at h

theorem bVerify_wf : MemoryTable.WF memInputsS bVerifyPub where
  pole_ne _ := by
    show pole memInputsS bVerifyPub.mem bVerifyPub.cprime ≠ 0
    simpa [bVerifyPub, Pub.cprime] using pole_servedRecord_ne

theorem bResultHalt_wf : MemoryTable.WF memInputsS bResultHaltPub where
  pole_ne h := by simp [bResultHaltPub] at h

theorem bTailHalt_wf : MemoryTable.WF memInputsS bTailHaltPub where
  pole_ne h := by simp [bTailHaltPub] at h

/-! ## H. The two accepted memory trees -/

def memLabelS (st : MState) (pub : MemoryTable.Pub K97cubic) :
    MState × MemoryTable.DTmem K97cubic :=
  (st, (memInputsS, pub))

abbrev aReadOuterLabel := memLabelS .read_root aReadOuterPub
abbrev aDecomposeOuterLabel := memLabelS .decompose aDecomposeOuterPub
abbrev aHeadHaltLabel := memLabelS .halt aHeadHaltPub
abbrev aReadInnerLabel := memLabelS .read_root aReadInnerPub
abbrev aVerifyOuterLabel := memLabelS .verify_child aVerifyOuterPub
abbrev aDecomposeInnerLabel := memLabelS .decompose aDecomposeInnerPub
abbrev aInnerHeadHaltLabel := memLabelS .halt aInnerHeadHaltPub
abbrev aVerifyInnerLabel := memLabelS .verify_child aVerifyInnerPub
abbrev aTailHaltLabel := memLabelS .halt aTailHaltPub
abbrev bReadLabel := memLabelS .read_root bReadPub
abbrev bDecomposeLabel := memLabelS .decompose bDecomposePub
abbrev bVerifyLabel := memLabelS .verify_child bVerifyPub
abbrev bResultHaltLabel := memLabelS .halt bResultHaltPub
abbrev bTailHaltLabel := memLabelS .halt bTailHaltPub

def dummyHaltCellS : Cell K97cubic := ⟨encS (.atom 0), 0, 0⟩

def dummyHaltPubS : MemoryTable.Pub K97cubic where
  st := .halt
  pt := dummyHaltCellS
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

abbrev dummyHaltLabelS := memLabelS .halt dummyHaltPubS

theorem dummyHaltS_accepts : Vmem memInputsS dummyHaltPubS := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · norm_num [eqBlk, dummyHaltPubS, dummyHaltCellS, memInputsS, encS,
      GlobalCarryRecognizer.enc_atom, Cell.zero, MemRec.zero]
  · rfl

theorem dummyHaltS_wf : MemoryTable.WF memInputsS dummyHaltPubS where
  pole_ne h := by simp [dummyHaltPubS] at h

def dummyHaltTreeS : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node dummyHaltLabelS []

def aTailHaltTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aTailHaltLabel []
def aVerifyInnerTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aVerifyInnerLabel [aTailHaltTree]
def aInnerHeadHaltTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aInnerHeadHaltLabel []
def aDecomposeInnerTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aDecomposeInnerLabel [aInnerHeadHaltTree, aVerifyInnerTree]
def aVerifyOuterTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aVerifyOuterLabel [aDecomposeInnerTree]
def aReadInnerTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aReadInnerLabel [aVerifyOuterTree]
def aHeadHaltTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aHeadHaltLabel []
def aDecomposeOuterTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aDecomposeOuterLabel [aHeadHaltTree, aReadInnerTree]
/-- Serviced root `A`, on the noun `parentFormulaS`. -/
def rootATree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aReadOuterLabel [aDecomposeOuterTree]

def bResultHaltTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node bResultHaltLabel []
def bVerifyTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node bVerifyLabel [bResultHaltTree]
def bTailHaltTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node bTailHaltLabel []
def bDecomposeTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node bDecomposeLabel [bVerifyTree, bTailHaltTree]
/-- Serviced root `B`, on the noun `subjectS`; its service is a left descent. -/
def rootBTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node bReadLabel [bDecomposeTree]

/-! The a-bearing view of the served forest. -/

abbrev aReadOuterLabelA := memLabelS .read_root aReadOuterPubA
abbrev aReadInnerLabelA := memLabelS .read_root aReadInnerPubA
abbrev aVerifyOuterLabelA := memLabelS .verify_child aVerifyOuterPubA
abbrev aVerifyInnerLabelA := memLabelS .verify_child aVerifyInnerPubA
abbrev bReadLabelA := memLabelS .read_root bReadPubA
abbrev bVerifyLabelA := memLabelS .verify_child bVerifyPubA

def aVerifyInnerTreeA : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aVerifyInnerLabelA [aTailHaltTree]
def aDecomposeInnerTreeA : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aDecomposeInnerLabel [aInnerHeadHaltTree, aVerifyInnerTreeA]
def aVerifyOuterTreeA : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aVerifyOuterLabelA [aDecomposeInnerTreeA]
def aReadInnerTreeA : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aReadInnerLabelA [aVerifyOuterTreeA]
def aDecomposeOuterTreeA : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aDecomposeOuterLabel [aHeadHaltTree, aReadInnerTreeA]
def rootATreeA : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aReadOuterLabelA [aDecomposeOuterTreeA]
def bVerifyTreeA : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node bVerifyLabelA [bResultHaltTree]
def bDecomposeTreeA : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node bDecomposeLabel [bVerifyTreeA, bTailHaltTree]
def rootBTreeA : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node bReadLabelA [bDecomposeTreeA]

theorem dummyHaltLabel_accepts : MemoryTable.Fmem dummyHaltLabelS (fun _ => none) := by
  refine ⟨rfl, dummyHaltS_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, dummyHaltPubS, MemoryTable.fanoutMem]
  · intro i hi; simp [memLabelS, dummyHaltPubS, MemoryTable.fanoutMem] at hi

theorem aHeadHaltLabel_accepts : MemoryTable.Fmem aHeadHaltLabel (fun _ => none) := by
  refine ⟨rfl, aHeadHalt_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, MemoryTable.fanoutMem]
  · intro i hi; simp [memLabelS, MemoryTable.fanoutMem] at hi

theorem aInnerHeadHaltLabel_accepts :
    MemoryTable.Fmem aInnerHeadHaltLabel (fun _ => none) := by
  refine ⟨rfl, aInnerHeadHalt_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, MemoryTable.fanoutMem]
  · intro i hi; simp [memLabelS, MemoryTable.fanoutMem] at hi

theorem aTailHaltLabel_accepts : MemoryTable.Fmem aTailHaltLabel (fun _ => none) := by
  refine ⟨rfl, aTailHalt_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, MemoryTable.fanoutMem]
  · intro i hi; simp [memLabelS, MemoryTable.fanoutMem] at hi

theorem bResultHaltLabel_accepts : MemoryTable.Fmem bResultHaltLabel (fun _ => none) := by
  refine ⟨rfl, bResultHalt_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, MemoryTable.fanoutMem]
  · intro i hi; simp [memLabelS, MemoryTable.fanoutMem] at hi

theorem bTailHaltLabel_accepts : MemoryTable.Fmem bTailHaltLabel (fun _ => none) := by
  refine ⟨rfl, bTailHalt_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, MemoryTable.fanoutMem]
  · intro i hi; simp [memLabelS, MemoryTable.fanoutMem] at hi

def aVerifyInnerOut : Fin 2 → Option (MState × MemoryTable.DTmem K97cubic)
  | 0 => some aTailHaltLabel
  | 1 => none

theorem aVerifyInnerLabel_accepts :
    MemoryTable.Fmem aVerifyInnerLabel aVerifyInnerOut := by
  refine ⟨rfl, aVerifyInner_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, aVerifyInnerOut, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i
    · simp [aVerifyInnerOut, MemoryTable.memCell, memLabelS, aVerifyInnerPub, aTailHaltPub]
    · simp [memLabelS, MemoryTable.fanoutMem] at hi

def aDecomposeInnerOut : Fin 2 → Option (MState × MemoryTable.DTmem K97cubic)
  | 0 => some aInnerHeadHaltLabel
  | 1 => some aVerifyInnerLabel

theorem aDecomposeInnerLabel_accepts :
    MemoryTable.Fmem aDecomposeInnerLabel aDecomposeInnerOut := by
  refine ⟨rfl, aDecomposeInner_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, aDecomposeInnerOut, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i <;>
      simp [aDecomposeInnerOut, MemoryTable.memCell, memLabelS, aDecomposeInnerPub,
        aInnerHeadHaltPub, aVerifyInnerPub]

def aVerifyOuterOut : Fin 2 → Option (MState × MemoryTable.DTmem K97cubic)
  | 0 => some aDecomposeInnerLabel
  | 1 => none

theorem aVerifyOuterLabel_accepts :
    MemoryTable.Fmem aVerifyOuterLabel aVerifyOuterOut := by
  refine ⟨rfl, aVerifyOuter_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, aVerifyOuterOut, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i
    · simp [aVerifyOuterOut, MemoryTable.memCell, memLabelS, aVerifyOuterPub, aDecomposeInnerPub]
    · simp [memLabelS, MemoryTable.fanoutMem] at hi

def aReadInnerOut : Fin 2 → Option (MState × MemoryTable.DTmem K97cubic)
  | 0 => some aVerifyOuterLabel
  | 1 => none

theorem aReadInnerLabel_accepts :
    MemoryTable.Fmem aReadInnerLabel aReadInnerOut := by
  refine ⟨rfl, aReadInner_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, aReadInnerOut, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i
    · simp [aReadInnerOut, MemoryTable.memCell, memLabelS, aReadInnerPub, aVerifyOuterPub]
    · simp [memLabelS, MemoryTable.fanoutMem] at hi

def aDecomposeOuterOut : Fin 2 → Option (MState × MemoryTable.DTmem K97cubic)
  | 0 => some aHeadHaltLabel
  | 1 => some aReadInnerLabel

theorem aDecomposeOuterLabel_accepts :
    MemoryTable.Fmem aDecomposeOuterLabel aDecomposeOuterOut := by
  refine ⟨rfl, aDecomposeOuter_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, aDecomposeOuterOut, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i <;>
      simp [aDecomposeOuterOut, MemoryTable.memCell, memLabelS, aDecomposeOuterPub,
        aHeadHaltPub, aReadInnerPub]

def aReadOuterOut : Fin 2 → Option (MState × MemoryTable.DTmem K97cubic)
  | 0 => some aDecomposeOuterLabel
  | 1 => none

theorem aReadOuterLabel_accepts :
    MemoryTable.Fmem aReadOuterLabel aReadOuterOut := by
  refine ⟨rfl, aReadOuter_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, aReadOuterOut, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i
    · simp [aReadOuterOut, MemoryTable.memCell, memLabelS, aReadOuterPub, aDecomposeOuterPub]
    · simp [memLabelS, MemoryTable.fanoutMem] at hi

def bVerifyOut : Fin 2 → Option (MState × MemoryTable.DTmem K97cubic)
  | 0 => some bResultHaltLabel
  | 1 => none

theorem bVerifyLabel_accepts : MemoryTable.Fmem bVerifyLabel bVerifyOut := by
  refine ⟨rfl, bVerify_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, bVerifyOut, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i
    · simp [bVerifyOut, MemoryTable.memCell, memLabelS, bVerifyPub, bResultHaltPub]
    · simp [memLabelS, MemoryTable.fanoutMem] at hi

def bDecomposeOut : Fin 2 → Option (MState × MemoryTable.DTmem K97cubic)
  | 0 => some bVerifyLabel
  | 1 => some bTailHaltLabel

theorem bDecomposeLabel_accepts : MemoryTable.Fmem bDecomposeLabel bDecomposeOut := by
  refine ⟨rfl, bDecompose_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, bDecomposeOut, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i <;>
      simp [bDecomposeOut, MemoryTable.memCell, memLabelS, bDecomposePub, bVerifyPub, bTailHaltPub]

def bReadOut : Fin 2 → Option (MState × MemoryTable.DTmem K97cubic)
  | 0 => some bDecomposeLabel
  | 1 => none

theorem bReadLabel_accepts : MemoryTable.Fmem bReadLabel bReadOut := by
  refine ⟨rfl, bRead_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, bReadOut, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i
    · simp [bReadOut, MemoryTable.memCell, memLabelS, bReadPub, bDecomposePub]
    · simp [memLabelS, MemoryTable.fanoutMem] at hi

theorem dummyHaltTreeS_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) dummyHaltTreeS := by
  unfold RVT
  exact ⟨dummyHaltLabel_accepts, by simp, ⟨fun _ => dummyHaltLabel_accepts, fun _ => rfl⟩⟩

theorem aTailHaltTree_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) aTailHaltTree := by
  unfold RVT
  exact ⟨aTailHaltLabel_accepts, by simp, ⟨fun _ => aTailHaltLabel_accepts, fun _ => rfl⟩⟩

theorem aInnerHeadHaltTree_rvt :
    RVT (MemoryTable.Fmem (K := K97cubic)) aInnerHeadHaltTree := by
  unfold RVT
  exact ⟨aInnerHeadHaltLabel_accepts, by simp,
    ⟨fun _ => aInnerHeadHaltLabel_accepts, fun _ => rfl⟩⟩

theorem bResultHaltTree_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) bResultHaltTree := by
  unfold RVT
  exact ⟨bResultHaltLabel_accepts, by simp, ⟨fun _ => bResultHaltLabel_accepts, fun _ => rfl⟩⟩

theorem bTailHaltTree_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) bTailHaltTree := by
  unfold RVT
  exact ⟨bTailHaltLabel_accepts, by simp, ⟨fun _ => bTailHaltLabel_accepts, fun _ => rfl⟩⟩

theorem aVerifyInnerTree_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) aVerifyInnerTree := by
  unfold aVerifyInnerTree RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 2 => (NTree.node aVerifyInnerLabel [aTailHaltTree]).childLabel i) =
        aVerifyInnerOut by funext i; fin_cases i <;> rfl]
    exact aVerifyInnerLabel_accepts
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact aTailHaltTree_rvt
  · simp [NTree.isLeaf, MemoryTable.Fmem, memLabelS, MemoryTable.fanoutMem]

theorem aDecomposeInnerTree_rvt :
    RVT (MemoryTable.Fmem (K := K97cubic)) aDecomposeInnerTree := by
  unfold aDecomposeInnerTree RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 2 =>
        (NTree.node aDecomposeInnerLabel [aInnerHeadHaltTree, aVerifyInnerTree]).childLabel i) =
        aDecomposeInnerOut by funext i; fin_cases i <;> rfl]
    exact aDecomposeInnerLabel_accepts
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact aInnerHeadHaltTree_rvt
    · exact aVerifyInnerTree_rvt
  · simp [NTree.isLeaf, MemoryTable.Fmem, memLabelS, MemoryTable.fanoutMem]

theorem aVerifyOuterTree_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) aVerifyOuterTree := by
  unfold aVerifyOuterTree RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 2 =>
        (NTree.node aVerifyOuterLabel [aDecomposeInnerTree]).childLabel i) =
        aVerifyOuterOut by funext i; fin_cases i <;> rfl]
    exact aVerifyOuterLabel_accepts
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact aDecomposeInnerTree_rvt
  · simp [NTree.isLeaf, MemoryTable.Fmem, memLabelS, MemoryTable.fanoutMem]

theorem aReadInnerTree_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) aReadInnerTree := by
  unfold aReadInnerTree RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 2 =>
        (NTree.node aReadInnerLabel [aVerifyOuterTree]).childLabel i) =
        aReadInnerOut by funext i; fin_cases i <;> rfl]
    exact aReadInnerLabel_accepts
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact aVerifyOuterTree_rvt
  · simp [NTree.isLeaf, MemoryTable.Fmem, memLabelS, MemoryTable.fanoutMem]

theorem aHeadHaltTree_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) aHeadHaltTree := by
  unfold RVT
  exact ⟨aHeadHaltLabel_accepts, by simp, ⟨fun _ => aHeadHaltLabel_accepts, fun _ => rfl⟩⟩

theorem aDecomposeOuterTree_rvt :
    RVT (MemoryTable.Fmem (K := K97cubic)) aDecomposeOuterTree := by
  unfold aDecomposeOuterTree RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 2 =>
        (NTree.node aDecomposeOuterLabel [aHeadHaltTree, aReadInnerTree]).childLabel i) =
        aDecomposeOuterOut by funext i; fin_cases i <;> rfl]
    exact aDecomposeOuterLabel_accepts
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact aHeadHaltTree_rvt
    · exact aReadInnerTree_rvt
  · simp [NTree.isLeaf, MemoryTable.Fmem, memLabelS, MemoryTable.fanoutMem]

theorem rootATree_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) rootATree := by
  unfold rootATree RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 2 =>
        (NTree.node aReadOuterLabel [aDecomposeOuterTree]).childLabel i) =
        aReadOuterOut by funext i; fin_cases i <;> rfl]
    exact aReadOuterLabel_accepts
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact aDecomposeOuterTree_rvt
  · simp [NTree.isLeaf, MemoryTable.Fmem, memLabelS, MemoryTable.fanoutMem]

theorem bVerifyTree_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) bVerifyTree := by
  unfold bVerifyTree RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 2 => (NTree.node bVerifyLabel [bResultHaltTree]).childLabel i) =
        bVerifyOut by funext i; fin_cases i <;> rfl]
    exact bVerifyLabel_accepts
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact bResultHaltTree_rvt
  · simp [NTree.isLeaf, MemoryTable.Fmem, memLabelS, MemoryTable.fanoutMem]

theorem bDecomposeTree_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) bDecomposeTree := by
  unfold bDecomposeTree RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 2 =>
        (NTree.node bDecomposeLabel [bVerifyTree, bTailHaltTree]).childLabel i) =
        bDecomposeOut by funext i; fin_cases i <;> rfl]
    exact bDecomposeLabel_accepts
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact bVerifyTree_rvt
    · exact bTailHaltTree_rvt
  · simp [NTree.isLeaf, MemoryTable.Fmem, memLabelS, MemoryTable.fanoutMem]

theorem rootBTree_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) rootBTree := by
  unfold rootBTree RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 2 => (NTree.node bReadLabel [bDecomposeTree]).childLabel i) =
        bReadOut by funext i; fin_cases i <;> rfl]
    exact bReadLabel_accepts
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact bDecomposeTree_rvt
  · simp [NTree.isLeaf, MemoryTable.Fmem, memLabelS, MemoryTable.fanoutMem]

/-! ## I. The exact configuration and execution -/

/-- Fifteen memory rows: dummy halt plus two serviced roots; two nonterminal compute rows. -/
def cfgS : ExactConfig F97 K97cubic where
  challenges :=
    { a := 0
      b := 0
      c := 0
      lam := MemoryTable.formRDefault
      α := fixtureAlpha
      z := servedSeed
      β := 0
      γ := 0 }
  Ksz := 4
  kMem := 3
  orbit := executionOrbit97
  orbit_h_pos := by norm_num [executionOrbit97]
  compRows := 2
  memRows := 15
  compRows_pos := by norm_num
  memRows_pos := by norm_num
  compRows_le := by norm_num [executionOrbit97]
  memRows_le := by norm_num [executionOrbit97]
  eDeg := 1
  eDeg_eq_one := rfl
  compNodes := fun i => executionOrbit97.orbitPoint i
  compNodes_spec := by intro i; rfl
  memNodes := fun i => executionOrbit97.orbitPoint i
  memNodes_spec := by intro i; rfl

/-- The fixture's configured `λ` is `formRDefault`. -/
@[simp] theorem cfgS_lam : cfgS.challenges.lam = MemoryTable.formRDefault := rfl

theorem challenge_alignmentS :
    cfgS.challenges.computeInputs = servedInputs ∧
      cfgS.challenges.memoryInputs = memInputsS :=
  ⟨rfl, rfl⟩

def execS : ExactExecution cfgS where
  computeTree := computeTreeS
  memoryForest := [dummyHaltTreeS, rootATree, rootBTree]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTreeS, bfsForest, NTree.size, totalSize, cfgS]
  memory_bfs_length := by
    norm_num [dummyHaltTreeS, rootATree, aDecomposeOuterTree, aHeadHaltTree, aReadInnerTree,
      aVerifyOuterTree, aDecomposeInnerTree, aInnerHeadHaltTree, aVerifyInnerTree,
      aTailHaltTree, rootBTree, bDecomposeTree, bVerifyTree, bResultHaltTree, bTailHaltTree,
      bfsForest, NTree.size, totalSize, cfgS]

/-- The a-bearing view of `execS`: the served memory trace and axis accounting live here; `execS`
is its Form R row encode. -/
def execSA : ExactExecution cfgS where
  computeTree := computeTreeS
  memoryForest := [dummyHaltTreeS, rootATreeA, rootBTreeA]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTreeS, bfsForest, NTree.size, totalSize, cfgS]
  memory_bfs_length := by
    norm_num [dummyHaltTreeS, rootATreeA, aDecomposeOuterTreeA, aHeadHaltTree, aReadInnerTreeA,
      aVerifyOuterTreeA, aDecomposeInnerTreeA, aInnerHeadHaltTree, aVerifyInnerTreeA,
      aTailHaltTree, rootBTreeA, bDecomposeTreeA, bVerifyTreeA, bResultHaltTree, bTailHaltTree,
      bfsForest, NTree.size, totalSize, cfgS]

/-- The aggregate BFS row order genuinely interleaves the two serviced roots. -/
theorem execution_rowsS :
    execS.computeRows = [parentRowS, servedRow] ∧
      execS.memoryRows =
        [dummyHaltLabelS, aReadOuterLabel, bReadLabel, aDecomposeOuterLabel, bDecomposeLabel,
          aHeadHaltLabel, aReadInnerLabel, bVerifyLabel, bTailHaltLabel,
          aVerifyOuterLabel, bResultHaltLabel, aDecomposeInnerLabel, aInnerHeadHaltLabel,
          aVerifyInnerLabel, aTailHaltLabel] := by
  constructor <;>
    norm_num [ExactExecution.computeRows, ExactExecution.memoryRows, execS, computeTreeS,
      dummyHaltTreeS, rootATree, aDecomposeOuterTree, aHeadHaltTree, aReadInnerTree, aVerifyOuterTree,
      aDecomposeInnerTree, aInnerHeadHaltTree, aVerifyInnerTree, aTailHaltTree,
      rootBTree, bDecomposeTree, bVerifyTree, bResultHaltTree, bTailHaltTree,
      bfsForest, NTree.size, totalSize]

/-- `execS` is the Form R row encode of `execSA` (`BuildableNockExecution.exec_encode`). -/
theorem execS_encode : execS = execSA.encodeMem :=
  TraceGen.RowEncode.eq_encodeMem_of rfl (by
    simp [execS, execSA, mapNTree, dummyHaltTreeS, rootATree, rootATreeA, aDecomposeOuterTree,
      aDecomposeOuterTreeA, aHeadHaltTree, aReadInnerTree, aReadInnerTreeA, aVerifyOuterTree,
      aVerifyOuterTreeA, aDecomposeInnerTree, aDecomposeInnerTreeA, aInnerHeadHaltTree,
      aVerifyInnerTree, aVerifyInnerTreeA, aTailHaltTree, rootBTree, rootBTreeA, bDecomposeTree,
      bDecomposeTreeA, bVerifyTree, bVerifyTreeA, bResultHaltTree, bTailHaltTree, memLabelS,
      dummyHaltPubS, aReadOuterPub, bReadPub, aDecomposeOuterPub, bDecomposePub, aHeadHaltPub,
      aReadInnerPub, bVerifyPub, bTailHaltPub, aVerifyOuterPub, bResultHaltPub,
      aDecomposeInnerPub, aInnerHeadHaltPub, aVerifyInnerPub, aTailHaltPub])

/-! ## J. Derived IO: three requests, three responses, genuinely permuted -/


/-- The `OP_4` row emits one request and the `OP_0` row emits two, the second being the actual
slot lookup. -/
theorem derived_requestsS :
    execS.derivedRequestIO =
      [NockVM.encRecFormR parentRecordS MemoryTable.formRDefault,
          NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault,
        NockVM.encRecFormR servedRecord MemoryTable.formRDefault] := by
  rw [ExactExecution.derivedRequestIO_eq_computeRows, execution_rowsS.1]
  simp [NockVM.activeRequestRecords, parentRowS, servedRow, parentPubS, servedPub]


/-- The three `read_root` rows of the two serviced roots emit the same three records in a
*different* order: root `B`'s service is second in the aggregate BFS traversal while it is third in
the compute request list.  The matching is therefore genuinely positionless. -/
theorem derived_responsesS :
    execS.derivedResponseIO =
      [NockVM.encRecFormR parentRecordS MemoryTable.formRDefault,
          NockVM.encRecFormR servedRecord MemoryTable.formRDefault,
        NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault] := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, execution_rowsS.2]
  rfl

theorem encRec_ne_of_ts_ne {r s : ComputeTable.MemRec K97cubic} (h : r.ts ≠ s.ts) :
    NockVM.encRecFormR r MemoryTable.formRDefault ≠ NockVM.encRecFormR s MemoryTable.formRDefault
        := by
  intro he
  apply h
  have hc := congrFun he (7 : Fin 9)
  change r.ts = s.ts at hc
  exact hc

private theorem natCast_ne_K97 {m n : ℕ} (hm : m < 97) (hn : n < 97) (hmn : m ≠ n) :
    (m : K97cubic) ≠ (n : K97cubic) := by
  letI : CharP K97cubic 97 := char97m
  intro h
  exact hmn (CharP.natCast_injOn_Iio K97cubic 97 (by simpa using hm) (by simpa using hn) h)

theorem ts_4_ne_16 : (4 : K97cubic) ≠ 16 := by
  have h := natCast_ne_K97 (m := 4) (n := 16) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

theorem ts_4_ne_64 : (4 : K97cubic) ≠ 64 := by
  have h := natCast_ne_K97 (m := 4) (n := 64) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

theorem ts_16_ne_64 : (16 : K97cubic) ≠ 64 := by
  have h := natCast_ne_K97 (m := 16) (n := 64) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

theorem requestsS_nodup : execS.derivedRequestIO.Nodup := by
  rw [derived_requestsS]
  have h12 : NockVM.encRecFormR parentRecordS MemoryTable.formRDefault
      ≠ NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_parentRecordS, ts_servedFormulaRecord]; exact ts_4_ne_16)
  have h13 : NockVM.encRecFormR parentRecordS MemoryTable.formRDefault
      ≠ NockVM.encRecFormR servedRecord MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_parentRecordS, ts_servedRecord]; exact ts_4_ne_64)
  have h23 : NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault
      ≠ NockVM.encRecFormR servedRecord MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_servedFormulaRecord, ts_servedRecord]; exact ts_16_ne_64)
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩⟩
  · simp [h12, h13]
  · simpa using h23

theorem responsesS_nodup : execS.derivedResponseIO.Nodup := by
  rw [derived_responsesS]
  have h12 : NockVM.encRecFormR parentRecordS MemoryTable.formRDefault
      ≠ NockVM.encRecFormR servedRecord MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_parentRecordS, ts_servedRecord]; exact ts_4_ne_64)
  have h13 : NockVM.encRecFormR parentRecordS MemoryTable.formRDefault
      ≠ NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault :=
    encRec_ne_of_ts_ne (by rw [ts_parentRecordS, ts_servedFormulaRecord]; exact ts_4_ne_16)
  have h23 : NockVM.encRecFormR servedRecord MemoryTable.formRDefault ≠ NockVM.encRecFormR
      servedFormulaRecord MemoryTable.formRDefault :=
    fun h => (encRec_ne_of_ts_ne
      (r := servedFormulaRecord) (s := servedRecord)
      (by rw [ts_servedFormulaRecord, ts_servedRecord]; exact ts_16_ne_64)) h.symm
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩⟩
  · simp [h12, h13]
  · simpa using h23

/-! ## K. Row acceptance, genericity, and the chained boundaries -/

theorem compute_rows_acceptedS : execS.ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff, execution_rowsS.1]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl
  · exact ⟨rfl, rfl, parentS_accepts⟩
  · exact ⟨rfl, rfl, served_accepts⟩

theorem memory_rows_acceptedS : execS.MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff, execution_rowsS.2]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl, dummyHaltS_accepts, rfl⟩
  · exact ⟨rfl, rfl, aReadOuter_accepts, rfl⟩
  · exact ⟨rfl, rfl, bRead_accepts, rfl⟩
  · exact ⟨rfl, rfl, aDecomposeOuter_accepts, rfl⟩
  · exact ⟨rfl, rfl, bDecompose_accepts, rfl⟩
  · exact ⟨rfl, rfl, aHeadHalt_accepts, rfl⟩
  · exact ⟨rfl, rfl, aReadInner_accepts, rfl⟩
  · exact ⟨rfl, rfl, bVerify_accepts, rfl⟩
  · exact ⟨rfl, rfl, bTailHalt_accepts, rfl⟩
  · exact ⟨rfl, rfl, aVerifyOuter_accepts, rfl⟩
  · exact ⟨rfl, rfl, bResultHalt_accepts, rfl⟩
  · exact ⟨rfl, rfl, aDecomposeInner_accepts, rfl⟩
  · exact ⟨rfl, rfl, aInnerHeadHalt_accepts, rfl⟩
  · exact ⟨rfl, rfl, aVerifyInner_accepts, rfl⟩
  · exact ⟨rfl, rfl, aTailHalt_accepts, rfl⟩

theorem computePubAtS_zero : execS.computePubAt ⟨0, by norm_num [cfgS]⟩ = parentPubS := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt,
    execution_rowsS.1, cfgS, parentRowS]

theorem computePubAtS_one : execS.computePubAt ⟨1, by norm_num [cfgS]⟩ = servedPub := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt,
    execution_rowsS.1, cfgS, servedRow]

theorem compute_wf_allS :
    ∀ i, ComputeTable.WF cfgS.challenges.computeInputs (execS.computePubAt i) := by
  rw [challenge_alignmentS.1]
  intro i
  fin_cases i
  · rw [computePubAtS_zero]; exact parentS_wf
  · rw [computePubAtS_one]; exact served_wf

theorem memoryPubAtS_0 : execS.memoryPubAt ⟨0, by norm_num [cfgS]⟩ = dummyHaltPubS := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsS.2,
    cfgS, memLabelS]

theorem memoryPubAtS_1 : execS.memoryPubAt ⟨1, by norm_num [cfgS]⟩ = aReadOuterPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsS.2,
    cfgS, memLabelS]

theorem memoryPubAtS_2 : execS.memoryPubAt ⟨2, by norm_num [cfgS]⟩ = bReadPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsS.2,
    cfgS, memLabelS]

theorem memoryPubAtS_3 : execS.memoryPubAt ⟨3, by norm_num [cfgS]⟩ = aDecomposeOuterPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsS.2,
    cfgS, memLabelS]

theorem memoryPubAtS_4 : execS.memoryPubAt ⟨4, by norm_num [cfgS]⟩ = bDecomposePub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsS.2,
    cfgS, memLabelS]

theorem memoryPubAtS_5 : execS.memoryPubAt ⟨5, by norm_num [cfgS]⟩ = aHeadHaltPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsS.2,
    cfgS, memLabelS]

theorem memoryPubAtS_6 : execS.memoryPubAt ⟨6, by norm_num [cfgS]⟩ = aReadInnerPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsS.2,
    cfgS, memLabelS]

theorem memoryPubAtS_7 : execS.memoryPubAt ⟨7, by norm_num [cfgS]⟩ = bVerifyPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsS.2,
    cfgS, memLabelS]

theorem memoryPubAtS_8 : execS.memoryPubAt ⟨8, by norm_num [cfgS]⟩ = bTailHaltPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsS.2,
    cfgS, memLabelS]

theorem memoryPubAtS_9 : execS.memoryPubAt ⟨9, by norm_num [cfgS]⟩ = aVerifyOuterPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsS.2,
    cfgS, memLabelS]

theorem memoryPubAtS_10 : execS.memoryPubAt ⟨10, by norm_num [cfgS]⟩ = bResultHaltPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsS.2,
    cfgS, memLabelS]

theorem memoryPubAtS_11 : execS.memoryPubAt ⟨11, by norm_num [cfgS]⟩ = aDecomposeInnerPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsS.2,
    cfgS, memLabelS]

theorem memoryPubAtS_12 : execS.memoryPubAt ⟨12, by norm_num [cfgS]⟩ = aInnerHeadHaltPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsS.2,
    cfgS, memLabelS]

theorem memoryPubAtS_13 : execS.memoryPubAt ⟨13, by norm_num [cfgS]⟩ = aVerifyInnerPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsS.2,
    cfgS, memLabelS]

theorem memoryPubAtS_14 : execS.memoryPubAt ⟨14, by norm_num [cfgS]⟩ = aTailHaltPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rowsS.2,
    cfgS, memLabelS]

/-- Every fixture memory row carries the package `λ = formRDefault` (row encode). -/
theorem execS_lambda_unset :
    ∀ i, (execS.memoryPubAt i).lambda? = some MemoryTable.formRDefault := by
  intro i
  fin_cases i
  · rw [memoryPubAtS_0]; rfl
  · rw [memoryPubAtS_1]; rfl
  · rw [memoryPubAtS_2]; rfl
  · rw [memoryPubAtS_3]; rfl
  · rw [memoryPubAtS_4]; rfl
  · rw [memoryPubAtS_5]; rfl
  · rw [memoryPubAtS_6]; rfl
  · rw [memoryPubAtS_7]; rfl
  · rw [memoryPubAtS_8]; rfl
  · rw [memoryPubAtS_9]; rfl
  · rw [memoryPubAtS_10]; rfl
  · rw [memoryPubAtS_11]; rfl
  · rw [memoryPubAtS_12]; rfl
  · rw [memoryPubAtS_13]; rfl
  · rw [memoryPubAtS_14]; rfl

/-- Halt and decompose rows carry `MemRec.zero`; read/verify rows make the inactive-state
hypotheses unsatisfiable. W4 stage 2: the all-row pole-hit half of `interFailurePairs`. -/
theorem inactive_mem_zeroS (i : Fin cfgS.memRows)
    (hnr : (execS.memoryPubAt i).st ≠ .read_root)
    (hnv : (execS.memoryPubAt i).st ≠ .verify_child) :
    (execS.memoryPubAt i).mem = ComputeTable.MemRec.zero := by
  fin_cases i <;>
    simp [memoryPubAtS_0, memoryPubAtS_1, memoryPubAtS_2, memoryPubAtS_3,
      memoryPubAtS_4, memoryPubAtS_5, memoryPubAtS_6, memoryPubAtS_7,
      memoryPubAtS_8, memoryPubAtS_9, memoryPubAtS_10, memoryPubAtS_11,
      memoryPubAtS_12, memoryPubAtS_13, memoryPubAtS_14, dummyHaltPubS,
      aReadOuterPub, bReadPub,
      aDecomposeOuterPub, bDecomposePub, aHeadHaltPub, aReadInnerPub,
      bVerifyPub, bTailHaltPub, aVerifyOuterPub, bResultHaltPub,
      aDecomposeInnerPub, aInnerHeadHaltPub, aVerifyInnerPub, aTailHaltPub] at hnr hnv ⊢

/-- Inactive (`halt`/`decompose`) rows carry the default `C' = 1` (`cprime? = none`). -/
theorem inactive_cprime_oneS (i : Fin cfgS.memRows)
    (hnr : (execS.memoryPubAt i).st ≠ .read_root)
    (hnv : (execS.memoryPubAt i).st ≠ .verify_child) :
    (execS.memoryPubAt i).cprime = 1 := by
  fin_cases i <;>
    simp [memoryPubAtS_0, memoryPubAtS_1, memoryPubAtS_2, memoryPubAtS_3,
      memoryPubAtS_4, memoryPubAtS_5, memoryPubAtS_6, memoryPubAtS_7,
      memoryPubAtS_8, memoryPubAtS_9, memoryPubAtS_10, memoryPubAtS_11,
      memoryPubAtS_12, memoryPubAtS_13, memoryPubAtS_14, dummyHaltPubS,
      aReadOuterPub, bReadPub,
      aDecomposeOuterPub, bDecomposePub, aHeadHaltPub, aReadInnerPub,
      bVerifyPub, bTailHaltPub, aVerifyOuterPub, bResultHaltPub,
      aDecomposeInnerPub, aInnerHeadHaltPub, aVerifyInnerPub, aTailHaltPub,
          MemoryTable.Pub.cprime] at hnr hnv ⊢

theorem memory_wf_allS :
    ∀ i, MemoryTable.WF cfgS.challenges.memoryInputs (execS.memoryPubAt i) := by
  rw [challenge_alignmentS.2]
  intro i
  fin_cases i
  · rw [memoryPubAtS_0]; exact dummyHaltS_wf
  · rw [memoryPubAtS_1]; exact aReadOuter_wf
  · rw [memoryPubAtS_2]; exact bRead_wf
  · rw [memoryPubAtS_3]; exact aDecomposeOuter_wf
  · rw [memoryPubAtS_4]; exact bDecompose_wf
  · rw [memoryPubAtS_5]; exact aHeadHalt_wf
  · rw [memoryPubAtS_6]; exact aReadInner_wf
  · rw [memoryPubAtS_7]; exact bVerify_wf
  · rw [memoryPubAtS_8]; exact bTailHalt_wf
  · rw [memoryPubAtS_9]; exact aVerifyOuter_wf
  · rw [memoryPubAtS_10]; exact bResultHalt_wf
  · rw [memoryPubAtS_11]; exact aDecomposeInner_wf
  · rw [memoryPubAtS_12]; exact aInnerHeadHalt_wf
  · rw [memoryPubAtS_13]; exact aVerifyInner_wf
  · rw [memoryPubAtS_14]; exact aTailHalt_wf

theorem compute_chainS :
    ∀ i : Fin cfgS.compRows, ∀ _ : (i : ℕ) + 1 < cfgS.compRows,
      (execS.computePubAt i).ln =
        (execS.computePubAt ⟨(i : ℕ) + 1, by omega⟩).ln_prev := by
  intro i hi
  fin_cases i
  · rw [computePubAtS_zero, computePubAtS_one]
    exact compute_line_handoffS
  · simp [cfgS] at hi


/-- The one global `intermediate` accumulator threads through both serviced roots. -/
theorem memory_chainS :
    ∀ i : Fin cfgS.memRows, ∀ _ : (i : ℕ) + 1 < cfgS.memRows,
      (execS.memoryPubAt i).icur =
        (execS.memoryPubAt ⟨(i : ℕ) + 1, by omega⟩).ipre := by
  intro i hi
  fin_cases i
  · rw [memoryPubAtS_0, memoryPubAtS_1]; rfl
  · rw [memoryPubAtS_1, memoryPubAtS_2]; rfl
  · rw [memoryPubAtS_2, memoryPubAtS_3]; rfl
  · rw [memoryPubAtS_3, memoryPubAtS_4]; rfl
  · rw [memoryPubAtS_4, memoryPubAtS_5]; rfl
  · rw [memoryPubAtS_5, memoryPubAtS_6]; rfl
  · rw [memoryPubAtS_6, memoryPubAtS_7]; rfl
  · rw [memoryPubAtS_7, memoryPubAtS_8]; rfl
  · rw [memoryPubAtS_8, memoryPubAtS_9]; rfl
  · rw [memoryPubAtS_9, memoryPubAtS_10]; rfl
  · rw [memoryPubAtS_10, memoryPubAtS_11]; rfl
  · rw [memoryPubAtS_11, memoryPubAtS_12]; rfl
  · rw [memoryPubAtS_12, memoryPubAtS_13]; rfl
  · rw [memoryPubAtS_13, memoryPubAtS_14]; rfl
  · simp [cfgS] at hi

/-- The accumulator's fifteen-row value sequence over both roots, starting at the dummy halt
and closing at zero. -/
theorem accumulator_valuesS :
    (dummyHaltPubS.ipre, dummyHaltPubS.icur, aReadOuterPub.icur, bReadPub.icur,
      aDecomposeOuterPub.icur, bDecomposePub.icur, aHeadHaltPub.icur, aReadInnerPub.icur,
      bVerifyPub.icur, bTailHaltPub.icur, aVerifyOuterPub.icur, bResultHaltPub.icur,
      aDecomposeInnerPub.icur, aInnerHeadHaltPub.icur, aVerifyInnerPub.icur,
      aTailHaltPub.icur) =
      ((0 : K97cubic), 0, -1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0) :=
  rfl

/-! ## L. Bounded nouns and realized fingerprints -/

theorem bounded_headS : FieldEmbedding.BoundedBy 97 headS := by simp [headS]
theorem bounded_tailS : FieldEmbedding.BoundedBy 97 tailS := by simp [tailS]
theorem bounded_resultS : FieldEmbedding.BoundedBy 97 resultS := by simp [resultS]
theorem bounded_bTailNoun : FieldEmbedding.BoundedBy 97 bTailNoun := by simp [bTailNoun]
theorem bounded_parentHeadS : FieldEmbedding.BoundedBy 97 parentHeadS := by simp [parentHeadS]
theorem bounded_parentResultS : FieldEmbedding.BoundedBy 97 parentResultS := by
  simp [parentResultS]
theorem bounded_formulaS : FieldEmbedding.BoundedBy 97 formulaS := by
  simp [formulaS, headS, tailS, FieldEmbedding.BoundedBy]
theorem bounded_subjectS : FieldEmbedding.BoundedBy 97 subjectS := by
  simp [subjectS, FieldEmbedding.BoundedBy]
theorem bounded_parentFormulaS : FieldEmbedding.BoundedBy 97 parentFormulaS := by
  simp [parentFormulaS, parentHeadS, formulaS, headS, tailS, FieldEmbedding.BoundedBy]

theorem fpRealizedS {n : Noun} (hb : FieldEmbedding.BoundedBy 97 n) :
    FPRealized servedSeed 97 (encS n) :=
  ⟨n, hb, rfl⟩

theorem fpActiveS {n : Noun} (hb : FieldEmbedding.BoundedBy 97 n) :
    FPSlotRealized servedSeed 97 .active (encS n) :=
  ⟨fpRealizedS hb, FPRealized.ne_zero servedSeed_ne (fpRealizedS hb)⟩

theorem ts_ne_zero_4 : (4 : K97cubic) ≠ 0 := by
  have h := natCast_ne_K97 (m := 4) (n := 0) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

theorem ts_ne_zero_16 : (16 : K97cubic) ≠ 0 := by
  have h := natCast_ne_K97 (m := 16) (n := 0) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

theorem ts_ne_zero_64 : (64 : K97cubic) ≠ 0 := by
  have h := natCast_ne_K97 (m := 64) (n := 0) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

/-- Row-level `C'` is a function of the stored record on `execS`: the three active records have distinct timestamps
(`4, 16, 64`) and padding rows store `MemRec.zero` beside the default `1`. -/
theorem execS_cprimeCoherent : execS.CprimeCoherent := by
  have hts : ∀ {a b : ComputeTable.MemRec K97cubic}, a.ts ≠ b.ts →
      NockVM.formRRow a MemoryTable.formRDefault ≠ NockVM.formRRow b MemoryTable.formRDefault :=
    fun h he => h (by have := congrArg ComputeTable.MemRec.ts he; exact this)
  have hz : ∀ {a : ComputeTable.MemRec K97cubic}, a.ts ≠ 0 →
      ComputeTable.MemRec.zero ≠ NockVM.formRRow a MemoryTable.formRDefault :=
    fun h he => h (by have := congrArg ComputeTable.MemRec.ts he; exact this.symm)
  have tPF : parentRecordS.ts ≠ servedFormulaRecord.ts := by
    rw [ts_parentRecordS, ts_servedFormulaRecord]; exact ts_4_ne_16
  have tPS : parentRecordS.ts ≠ servedRecord.ts := by
    rw [ts_parentRecordS, ts_servedRecord]; exact ts_4_ne_64
  have tFS : servedFormulaRecord.ts ≠ servedRecord.ts := by
    rw [ts_servedFormulaRecord, ts_servedRecord]; exact ts_16_ne_64
  have tP : parentRecordS.ts ≠ 0 := by rw [ts_parentRecordS]; exact ts_ne_zero_4
  have tF : servedFormulaRecord.ts ≠ 0 := by rw [ts_servedFormulaRecord]; exact ts_ne_zero_16
  have tS : servedRecord.ts ≠ 0 := by rw [ts_servedRecord]; exact ts_ne_zero_64
  have hPF := hts tPF
  have hPS := hts tPS
  have hFS := hts tFS
  have hzP := hz tP
  have hzF := hz tF
  have hzS := hz tS
  refine ExactExecution.cprimeCoherent_of_fun
    (fun m => if m = NockVM.formRRow parentRecordS MemoryTable.formRDefault then
        NockVM.formRCprime parentRecordS MemoryTable.formRDefault
      else if m = NockVM.formRRow servedFormulaRecord MemoryTable.formRDefault then
        NockVM.formRCprime servedFormulaRecord MemoryTable.formRDefault
      else if m = NockVM.formRRow servedRecord MemoryTable.formRDefault then
        NockVM.formRCprime servedRecord MemoryTable.formRDefault
      else 1) ?_
  intro row hmem
  rw [execution_rowsS.2] at hmem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals
    simp [memLabelS, dummyHaltLabelS, aReadOuterLabel, bReadLabel, aDecomposeOuterLabel,
        bDecomposeLabel, aHeadHaltLabel, aReadInnerLabel, bVerifyLabel, bTailHaltLabel,
        aVerifyOuterLabel, bResultHaltLabel, aDecomposeInnerLabel, aInnerHeadHaltLabel,
        aVerifyInnerLabel, aTailHaltLabel, dummyHaltPubS, aReadOuterPub, bReadPub,
        aDecomposeOuterPub, bDecomposePub, aHeadHaltPub, aReadInnerPub, bVerifyPub, bTailHaltPub,
        aVerifyOuterPub, bResultHaltPub, aDecomposeInnerPub, aInnerHeadHaltPub, aVerifyInnerPub,
        aTailHaltPub, MemoryTable.Pub.cprime, hPF, hPS, hFS, hzP, hzF, hzS,
      Ne.symm hPF, Ne.symm hPS, Ne.symm hFS]

theorem parentRecordS_ne_zero : parentRecordS ≠ ComputeTable.MemRec.zero := by
  intro h
  have hts := congrArg ComputeTable.MemRec.ts h
  rw [ts_parentRecordS] at hts
  exact ts_ne_zero_4 (by simpa [ComputeTable.MemRec.zero] using hts)

theorem servedFormulaRecord_ne_zero : servedFormulaRecord ≠ ComputeTable.MemRec.zero := by
  intro h
  have hts := congrArg ComputeTable.MemRec.ts h
  rw [ts_servedFormulaRecord] at hts
  exact ts_ne_zero_16 (by simpa [ComputeTable.MemRec.zero] using hts)

theorem servedRecord_ne_zero : servedRecord ≠ ComputeTable.MemRec.zero := by
  intro h
  have hts := congrArg ComputeTable.MemRec.ts h
  rw [ts_servedRecord] at hts
  exact ts_ne_zero_64 (by simpa [ComputeTable.MemRec.zero] using hts)

theorem parentRecordS_active : MemRecSlotRealized servedSeed 97 .active parentRecordS :=
  ⟨parentRecordS_ne_zero, fpActiveS bounded_parentFormulaS, fpActiveS bounded_formulaS⟩

theorem servedFormulaRecord_active :
    MemRecSlotRealized servedSeed 97 .active servedFormulaRecord :=
  ⟨servedFormulaRecord_ne_zero, fpActiveS bounded_formulaS, fpActiveS bounded_tailS⟩

theorem servedRecord_active : MemRecSlotRealized servedSeed 97 .active servedRecord :=
  ⟨servedRecord_ne_zero, fpActiveS bounded_subjectS, fpActiveS bounded_resultS⟩

/-! ## M. Semantic IO preimage -/

def semParentRec : (nmrMEF F97 K97cubic).Rec :=
  (3,
    (((encS parentFormulaS).size, (encS parentFormulaS).dyck, (encS parentFormulaS).leaf),
     ((encS formulaS).size, (encS formulaS).dyck, (encS formulaS).leaf)),
    1)

def semInnerRec : (nmrMEF F97 K97cubic).Rec :=
  (3,
    (((encS formulaS).size, (encS formulaS).dyck, (encS formulaS).leaf),
     ((encS tailS).size, (encS tailS).dyck, (encS tailS).leaf)),
    2)

def semServedRec : (nmrMEF F97 K97cubic).Rec :=
  (2,
    (((encS subjectS).size, (encS subjectS).dyck, (encS subjectS).leaf),
     ((encS resultS).size, (encS resultS).dyck, (encS resultS).leaf)),
    3)

private theorem algebraMap_three :
    algebraMap F97 K97cubic (3 : F97) = (3 : K97cubic) := by
  simpa using (map_natCast (algebraMap F97 K97cubic) 3)

private theorem algebraMap_two :
    algebraMap F97 K97cubic (2 : F97) = (2 : K97cubic) := by
  simpa using (map_natCast (algebraMap F97 K97cubic) 2)

theorem semParentRec_bridge :
    bridge F97 K97cubic cfgS.challenges.α cfgS.challenges.lam semParentRec =
      NockVM.encRecFormR parentRecordS MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees]
  rw [show memRecOfNMR F97 K97cubic
      ((nmrEncoding F97 K97cubic cfgS.challenges.α).encode semParentRec) = parentRecordS by
    ext <;> norm_num [memRecOfNMR, nmrEncoding, semParentRec, cfgS, parentRecordS,
      fixtureAlpha, algebraMap_three]]
  rfl

theorem semInnerRec_bridge :
    bridge F97 K97cubic cfgS.challenges.α cfgS.challenges.lam semInnerRec =
      NockVM.encRecFormR servedFormulaRecord MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees]
  rw [show memRecOfNMR F97 K97cubic
      ((nmrEncoding F97 K97cubic cfgS.challenges.α).encode semInnerRec) =
        servedFormulaRecord by
    ext <;> norm_num [memRecOfNMR, nmrEncoding, semInnerRec, cfgS, servedFormulaRecord,
      fixtureAlpha, algebraMap_three]]
  rfl

theorem semServedRec_bridge :
    bridge F97 K97cubic cfgS.challenges.α cfgS.challenges.lam semServedRec =
      NockVM.encRecFormR servedRecord MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees]
  rw [show memRecOfNMR F97 K97cubic
      ((nmrEncoding F97 K97cubic cfgS.challenges.α).encode semServedRec) = servedRecord by
    ext <;> norm_num [memRecOfNMR, nmrEncoding, semServedRec, cfgS, servedRecord,
      fixtureAlpha, algebraMap_two]]
  rfl

theorem semRecs_nodup : [semParentRec, semInnerRec, semServedRec].Nodup := by
  have h12 : semParentRec ≠ semInnerRec := by
    intro h
    have := congrArg (fun r : (nmrMEF F97 K97cubic).Rec => r.2.2) h
    norm_num [semParentRec, semInnerRec] at this
  have h13 : semParentRec ≠ semServedRec := by
    intro h
    have := congrArg (fun r : (nmrMEF F97 K97cubic).Rec => r.2.2) h
    norm_num [semParentRec, semServedRec] at this
  have h23 : semInnerRec ≠ semServedRec := by
    intro h
    have := congrArg (fun r : (nmrMEF F97 K97cubic).Rec => r.2.2) h
    norm_num [semInnerRec, semServedRec] at this
  simp [h12, h13, h23]


/-- The semantic preimage of the whole execution's IO.  Its response list is the genuine
**permutation** of the request list produced by the interleaved two-root BFS traversal. -/
def semanticPreimageS : SemanticIOPreimage cfgS execS where
  timestampBound := 4
  timestampBound_le_order := by
    change 4 ≤ orderOf fixtureAlpha
    rw [fixtureAlpha_order]
    norm_num
  semanticRequests := [semParentRec, semInnerRec, semServedRec]
  semanticResponses := [semParentRec, semServedRec, semInnerRec]
  requestTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> norm_num [semParentRec, semInnerRec, semServedRec]
  responseTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> norm_num [semParentRec, semInnerRec, semServedRec]
  semantic_lmio := by
    refine ⟨by norm_num [IO.InRange, cfgS], [semParentRec, semInnerRec, semServedRec],
      le_refl _, semRecs_nodup, fun x => Iff.rfl, ?_⟩
    exact List.Perm.cons semParentRec (List.Perm.swap semInnerRec semServedRec [])
  requestTimestamp_determines := by
    intro x hx y hy h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | rfl | (norm_num [semParentRec, semInnerRec, semServedRec] at h)
  requests_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_singleton,
      semParentRec_bridge, semInnerRec_bridge, semServedRec_bridge, derived_requestsS]
  responses_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_cons, List.map_singleton,
      semParentRec_bridge, semServedRec_bridge, semInnerRec_bridge, derived_responsesS]

theorem semantic_exactS : SemanticExactLanguage cfgS execS :=
  ⟨compute_rows_acceptedS, memory_rows_acceptedS, ⟨semanticPreimageS⟩⟩

/-! ## N. The chained exact language -/

theorem chainedS : ChainedSemanticExactLanguage cfgS execS where
  semantic := semantic_exactS
  z_ne_zero := servedSeed_ne
  compute_wf := compute_wf_allS
  memory_wf := memory_wf_allS
  compute_chain := compute_chainS
  memory_chain := memory_chainS
  memory_first_counts := by rw [memoryPubAtS_0]; rfl
  memory_first_indicator := by rw [memoryPubAtS_0]; rfl
  memory_first_ipre := by rw [memoryPubAtS_0]; rfl
  memory_last_icur := by
    have hlast :
        cfgS.orbit.lastIndex cfgS.memRows cfgS.memRows_pos =
          ⟨14, by norm_num [cfgS]⟩ := rfl
    rw [hlast, memoryPubAtS_14]
    rfl
  memory_same_lambda :=
    ExactExecution.memory_same_lambda_of_const _ (some MemoryTable.formRDefault) execS_lambda_unset

/-! ## O. Exact arity-3/2 topology -/

theorem compute_topologyS : ComputeExactTopology execS := by
  refine ⟨computeTreeS_rvt, ?_⟩
  show ProperArity 3 computeTreeS
  simp [computeTreeS]

theorem memory_topologyS : MemoryExactTopology execS := by
  intro t ht
  simp only [execS, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨dummyHaltTreeS_rvt, ?_⟩
    simp [dummyHaltTreeS]
  · refine ⟨rootATree_rvt, ?_⟩
    simp [rootATree, aDecomposeOuterTree, aHeadHaltTree, aReadInnerTree, aVerifyOuterTree,
      aDecomposeInnerTree, aInnerHeadHaltTree, aVerifyInnerTree, aTailHaltTree]
  · refine ⟨rootBTree_rvt, ?_⟩
    simp [rootBTree, bDecomposeTree, bVerifyTree, bResultHaltTree, bTailHaltTree]

theorem traversableS : TraversableChainedSemanticExactLanguage cfgS execS where
  chained := chainedS
  compute_topology := compute_topologyS
  memory_topology := memory_topologyS

/-! ## P. Bounded noun realization of every public row -/

theorem parentRow_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel parentRowS) where
  subject := fpActiveS bounded_subjectS
  formula := fpActiveS bounded_parentFormulaS
  evaluation := fpActiveS bounded_parentResultS
  subformula := by
    intro i
    fin_cases i
    · exact ⟨fpActiveS bounded_subjectS, fpActiveS bounded_formulaS, fpActiveS bounded_resultS⟩
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i
    fin_cases i
    · exact parentRecordS_active
    · exact rfl
    · exact rfl

theorem servedRow_nounRealization :
    ComputePublicRowNounRealization 97 (computePublicLabel servedRow) where
  subject := fpActiveS bounded_subjectS
  formula := fpActiveS bounded_formulaS
  evaluation := fpActiveS bounded_resultS
  subformula := by
    intro i
    fin_cases i
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  memoryRecord := by
    intro i
    fin_cases i
    · exact servedFormulaRecord_active
    · exact servedRecord_active
    · exact rfl

theorem computeTreeNounRealizationS :
    ComputePublicTreeNounRealization 97 execS.computePublicTree := by
  have h : (bfsForest [execS.computePublicTree]).map NTree.label
      = [computePublicLabel parentRowS, computePublicLabel servedRow] := by
    rw [ExactExecution.computePublicTree_bfs, ExactExecution.computePublicRows,
      execution_rowsS.1]
    rfl
  unfold ComputePublicTreeNounRealization ComputePublicRowsNounRealization
  rw [h]
  refine List.forall_iff_forall_mem.mpr ?_
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl
  · exact parentRow_nounRealization
  · exact servedRow_nounRealization

/-- Read/verify rows carry one active child cell, a null right cell, and a live record. -/
theorem memSingleChildRealization {st : MState} (pub : MemoryTable.Pub K97cubic)
    (hst : MemoryTable.fanoutMem st = 1)
    (hpt : FPSlotRealized servedSeed 97 .active pub.pt.noun)
    (hlc : FPSlotRealized servedSeed 97 .active pub.lc.noun)
    (hrc : pub.rc = MemoryTable.Cell.zero)
    (hkind : memoryMemRecKind st = .active)
    (hmem : MemRecSlotRealized servedSeed 97 .active pub.mem) :
    MemoryPublicRowNounRealization 97 (memLabelS st pub) where
  parent := hpt
  child := by
    intro i
    fin_cases i
    · show MemoryCellSlotRealized servedSeed 97 (memoryChildKind st 0) pub.lc
      rw [memoryChildKind, hst]
      simpa [MemoryCellSlotRealized] using hlc
    · show MemoryCellSlotRealized servedSeed 97 (memoryChildKind st 1) pub.rc
      rw [memoryChildKind, hst]
      simpa [MemoryCellSlotRealized] using hrc
  memoryRecord := by
    show MemRecSlotRealized servedSeed 97 (memoryMemRecKind st) pub.mem
    rw [hkind]
    exact hmem

/-- `decompose` rows carry two active child cells and no live record. -/
theorem memDecomposeRealization (pub : MemoryTable.Pub K97cubic)
    (hpt : FPSlotRealized servedSeed 97 .active pub.pt.noun)
    (hlc : FPSlotRealized servedSeed 97 .active pub.lc.noun)
    (hrc : FPSlotRealized servedSeed 97 .active pub.rc.noun)
    (hmem : pub.mem = ComputeTable.MemRec.zero) :
    MemoryPublicRowNounRealization 97 (memLabelS .decompose pub) where
  parent := hpt
  child := by
    intro i
    fin_cases i
    · exact hlc
    · exact hrc
  memoryRecord := hmem

/-- `halt` rows carry two null child cells and no live record. -/
theorem memHaltRealization (pub : MemoryTable.Pub K97cubic)
    (hpt : FPSlotRealized servedSeed 97 .active pub.pt.noun)
    (hlc : pub.lc = MemoryTable.Cell.zero)
    (hrc : pub.rc = MemoryTable.Cell.zero)
    (hmem : pub.mem = ComputeTable.MemRec.zero) :
    MemoryPublicRowNounRealization 97 (memLabelS .halt pub) where
  parent := hpt
  child := by
    intro i
    fin_cases i
    · exact hlc
    · exact hrc
  memoryRecord := hmem

theorem dummyHalt_realization : MemoryPublicRowNounRealization 97 dummyHaltLabelS :=
  memHaltRealization dummyHaltPubS (fpActiveS (by simp [FieldEmbedding.BoundedBy])) rfl rfl rfl

theorem aReadOuter_realization : MemoryPublicRowNounRealization 97 aReadOuterLabel :=
  memSingleChildRealization aReadOuterPub rfl
    (fpActiveS bounded_parentFormulaS) (fpActiveS bounded_parentFormulaS) rfl rfl
    (parentRecordS_active.formRRow _)

theorem bRead_realization : MemoryPublicRowNounRealization 97 bReadLabel :=
  memSingleChildRealization bReadPub rfl
    (fpActiveS bounded_subjectS) (fpActiveS bounded_subjectS) rfl rfl (servedRecord_active.formRRow
        _)

theorem aDecomposeOuter_realization :
    MemoryPublicRowNounRealization 97 aDecomposeOuterLabel :=
  memDecomposeRealization aDecomposeOuterPub (fpActiveS bounded_parentFormulaS)
    (fpActiveS bounded_parentHeadS) (fpActiveS bounded_formulaS) rfl

theorem bDecompose_realization : MemoryPublicRowNounRealization 97 bDecomposeLabel :=
  memDecomposeRealization bDecomposePub (fpActiveS bounded_subjectS)
    (fpActiveS bounded_resultS) (fpActiveS bounded_bTailNoun) rfl

theorem aHeadHalt_realization : MemoryPublicRowNounRealization 97 aHeadHaltLabel :=
  memHaltRealization aHeadHaltPub (fpActiveS bounded_parentHeadS) rfl rfl rfl

theorem aReadInner_realization : MemoryPublicRowNounRealization 97 aReadInnerLabel :=
  memSingleChildRealization aReadInnerPub rfl
    (fpActiveS bounded_formulaS) (fpActiveS bounded_formulaS) rfl rfl
    (servedFormulaRecord_active.formRRow _)

theorem bVerify_realization : MemoryPublicRowNounRealization 97 bVerifyLabel :=
  memSingleChildRealization bVerifyPub rfl
    (fpActiveS bounded_resultS) (fpActiveS bounded_resultS) rfl rfl (servedRecord_active.formRRow _)

theorem bTailHalt_realization : MemoryPublicRowNounRealization 97 bTailHaltLabel :=
  memHaltRealization bTailHaltPub (fpActiveS bounded_bTailNoun) rfl rfl rfl

theorem aVerifyOuter_realization : MemoryPublicRowNounRealization 97 aVerifyOuterLabel :=
  memSingleChildRealization aVerifyOuterPub rfl
    (fpActiveS bounded_formulaS) (fpActiveS bounded_formulaS) rfl rfl (parentRecordS_active.formRRow
        _)

theorem bResultHalt_realization : MemoryPublicRowNounRealization 97 bResultHaltLabel :=
  memHaltRealization bResultHaltPub (fpActiveS bounded_resultS) rfl rfl rfl

theorem aDecomposeInner_realization :
    MemoryPublicRowNounRealization 97 aDecomposeInnerLabel :=
  memDecomposeRealization aDecomposeInnerPub (fpActiveS bounded_formulaS)
    (fpActiveS bounded_headS) (fpActiveS bounded_tailS) rfl

theorem aInnerHeadHalt_realization :
    MemoryPublicRowNounRealization 97 aInnerHeadHaltLabel :=
  memHaltRealization aInnerHeadHaltPub (fpActiveS bounded_headS) rfl rfl rfl

theorem aVerifyInner_realization : MemoryPublicRowNounRealization 97 aVerifyInnerLabel :=
  memSingleChildRealization aVerifyInnerPub rfl
    (fpActiveS bounded_tailS) (fpActiveS bounded_tailS) rfl rfl (servedFormulaRecord_active.formRRow
        _)

theorem aTailHalt_realization : MemoryPublicRowNounRealization 97 aTailHaltLabel :=
  memHaltRealization aTailHaltPub (fpActiveS bounded_tailS) rfl rfl rfl

theorem memoryForestNounRealizationS :
    MemoryPublicForestNounRealization 97 execS.memoryForest := by
  unfold MemoryPublicForestNounRealization MemoryPublicRowsNounRealization
  rw [show (bfsForest execS.memoryForest).map NTree.label = execS.memoryRows from rfl,
    execution_rowsS.2]
  refine List.forall_iff_forall_mem.mpr ?_
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact dummyHalt_realization
  · exact aReadOuter_realization
  · exact bRead_realization
  · exact aDecomposeOuter_realization
  · exact bDecompose_realization
  · exact aHeadHalt_realization
  · exact aReadInner_realization
  · exact bVerify_realization
  · exact bTailHalt_realization
  · exact aVerifyOuter_realization
  · exact bResultHalt_realization
  · exact aDecomposeInner_realization
  · exact aInnerHeadHalt_realization
  · exact aVerifyInner_realization
  · exact aTailHalt_realization

theorem leafAtomS (k : ℕ) (hk : k < 97) (pub : MemoryTable.Pub K97cubic)
    (h : pub.pt.noun = encS (.atom k)) :
    MemoryLeafAtomsRealized 97 (NTree.node (memLabelS .halt pub) []) :=
  ⟨k, hk, by rw [h]; simp [encS, GlobalCarryRecognizer.enc_atom]⟩

theorem leafAtoms_dummyHaltTreeS : MemoryLeafAtomsRealized 97 dummyHaltTreeS :=
  leafAtomS 0 (by norm_num) dummyHaltPubS rfl

theorem leafAtoms_aTailHaltTree : MemoryLeafAtomsRealized 97 aTailHaltTree :=
  leafAtomS 2 (by norm_num) aTailHaltPub rfl

theorem leafAtoms_aInnerHeadHaltTree : MemoryLeafAtomsRealized 97 aInnerHeadHaltTree :=
  leafAtomS 0 (by norm_num) aInnerHeadHaltPub rfl

theorem leafAtoms_aHeadHaltTree : MemoryLeafAtomsRealized 97 aHeadHaltTree :=
  leafAtomS 4 (by norm_num) aHeadHaltPub rfl

theorem leafAtoms_bResultHaltTree : MemoryLeafAtomsRealized 97 bResultHaltTree :=
  leafAtomS 7 (by norm_num) bResultHaltPub rfl

theorem leafAtoms_bTailHaltTree : MemoryLeafAtomsRealized 97 bTailHaltTree :=
  leafAtomS 9 (by norm_num) bTailHaltPub rfl

theorem leafAtoms_aVerifyInnerTree : MemoryLeafAtomsRealized 97 aVerifyInnerTree :=
  leafAtoms_aTailHaltTree

theorem leafAtoms_aDecomposeInnerTree : MemoryLeafAtomsRealized 97 aDecomposeInnerTree :=
  ⟨leafAtoms_aInnerHeadHaltTree, leafAtoms_aVerifyInnerTree⟩

theorem leafAtoms_aVerifyOuterTree : MemoryLeafAtomsRealized 97 aVerifyOuterTree :=
  leafAtoms_aDecomposeInnerTree

theorem leafAtoms_aReadInnerTree : MemoryLeafAtomsRealized 97 aReadInnerTree :=
  leafAtoms_aVerifyOuterTree

theorem leafAtoms_aDecomposeOuterTree : MemoryLeafAtomsRealized 97 aDecomposeOuterTree :=
  ⟨leafAtoms_aHeadHaltTree, leafAtoms_aReadInnerTree⟩

theorem leafAtoms_rootATree : MemoryLeafAtomsRealized 97 rootATree :=
  leafAtoms_aDecomposeOuterTree

theorem leafAtoms_bVerifyTree : MemoryLeafAtomsRealized 97 bVerifyTree :=
  leafAtoms_bResultHaltTree

theorem leafAtoms_bDecomposeTree : MemoryLeafAtomsRealized 97 bDecomposeTree :=
  ⟨leafAtoms_bVerifyTree, leafAtoms_bTailHaltTree⟩

theorem leafAtoms_rootBTree : MemoryLeafAtomsRealized 97 rootBTree :=
  leafAtoms_bDecomposeTree

theorem nounRealizationS : ExactExecutionNounRealization 97 cfgS execS where
  computeTree := computeTreeNounRealizationS
  memoryForest := memoryForestNounRealizationS
  memoryLeaves := by
    intro tree htree
    simp only [execS, List.mem_cons, List.not_mem_nil, or_false] at htree
    rcases htree with rfl | rfl | rfl
    · exact leafAtoms_dummyHaltTreeS
    · exact leafAtoms_rootATree
    · exact leafAtoms_rootBTree

theorem languageS :
    NounRealizedTraversableChainedSemanticExactLanguage 97 cfgS execS where
  traversable := traversableS
  nounRealization := nounRealizationS

/-! ## Q. Exact row-level semantic data on both compute rows -/

theorem computeRowAtS_zero :
    execS.computeRowAt ⟨0, by norm_num [cfgS]⟩ = parentRowS := by
  norm_num [ExactExecution.computeRowAt, execution_rowsS.1, cfgS]

theorem computeRowAtS_one :
    execS.computeRowAt ⟨1, by norm_num [cfgS]⟩ = servedRow := by
  norm_num [ExactExecution.computeRowAt, execution_rowsS.1, cfgS]

/-- Transport of row-level semantic data along an equality of rows. -/
def castRowData {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K97cubic}
    (h : row₁ = row₂) (d : SemanticTrace.ComputeRowSemanticData 97 3 row₂) :
    SemanticTrace.ComputeRowSemanticData 97 3 row₁ :=
  h.symm ▸ d

/-- The seed-independent content of a served slot lookup: its record, root, axis and child. -/
def lookupTuple {z : K97cubic} (l : SemanticTrace.ServedNounLookup z) :
    ComputeTable.MemRec K97cubic × Noun × ℕ × Noun :=
  (l.record, l.root, l.axis, l.child)

theorem castRowData_servedTuples
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K97cubic}
    (h : row₁ = row₂) (d : SemanticTrace.ComputeRowSemanticData 97 3 row₂) :
    (castRowData h d).needs.served.map lookupTuple = d.needs.served.map lookupTuple := by
  subst h
  rfl

/-- Both compute rows' semantic data, on the authoritative indexed rows. -/
def rowDataS : ∀ i : Fin cfgS.compRows,
    SemanticTrace.ComputeRowSemanticData 97 3 (execS.computeRowAt i)
  | ⟨0, _⟩ => castRowData computeRowAtS_zero parentRowData
  | ⟨1, _⟩ => castRowData computeRowAtS_one servedRowData
  | ⟨n + 2, h⟩ =>
      absurd (show n + 2 < 2 from by simpa [cfgS] using h) (by omega)

/-- The nonterminal `OP_4` row needs no slot lookup (`requiredServedLookups .s4 = 0`). -/
theorem rowDataS_zero_servedTuples :
    (rowDataS ⟨0, by norm_num [cfgS]⟩).needs.served.map lookupTuple = [] :=
  (castRowData_servedTuples computeRowAtS_zero parentRowData).trans rfl

/-- **The nonterminal `OP_0` row's actual slot lookup**, exposed seed-independently
. -/
theorem rowDataS_one_servedTuples :
    (rowDataS ⟨1, by norm_num [cfgS]⟩).needs.served.map lookupTuple =
      [(servedRecord, subjectS, 2, resultS)] :=
  (castRowData_servedTuples computeRowAtS_one servedRowData).trans rfl

/-- The exact semantic CORE of the whole execution.  Row `0` is the nonterminal `OP_4` parent and
row `1` is the genuine `OP_0` served row, whose `needs.served` list has one entry. -/
def semanticDataS : SemanticTrace.ExactExecutionSemanticData 97 3 cfgS execS where
  language := languageS
  rowAccepted := fun i => ExactExecution.computeRowAt_accepted compute_rows_acceptedS i
  rows := rowDataS

/-! ## R. The exact axis trees of the two serviced roots -/

theorem ts_closed_parent : TimestampClosedAt cfgS.challenges.α parentRecordS.ts :=
  ⟨1, by simp [parentRecordS, cfgS]⟩

theorem ts_closed_inner : TimestampClosedAt cfgS.challenges.α servedFormulaRecord.ts :=
  ⟨2, rfl⟩

theorem ts_closed_served : TimestampClosedAt cfgS.challenges.α servedRecord.ts :=
  ⟨3, rfl⟩

def expParent : ℕ := timestampExp cfgS.challenges.α parentRecordS.ts
def expInner : ℕ := timestampExp cfgS.challenges.α servedFormulaRecord.ts
def expServed : ℕ := timestampExp cfgS.challenges.α servedRecord.ts

theorem ts_eq_parent : parentRecordS.ts = cfgS.challenges.α ^ expParent :=
  timestampExp_spec ts_closed_parent

theorem ts_eq_inner : servedFormulaRecord.ts = cfgS.challenges.α ^ expInner :=
  timestampExp_spec ts_closed_inner

theorem ts_eq_served : servedRecord.ts = cfgS.challenges.α ^ expServed :=
  timestampExp_spec ts_closed_served

theorem expParent_ne_expInner : expParent ≠ expInner := by
  intro h
  have heq : parentRecordS.ts = servedFormulaRecord.ts := by
    rw [ts_eq_parent, ts_eq_inner, h]
  rw [ts_parentRecordS, ts_servedFormulaRecord] at heq
  exact ts_4_ne_16 heq

theorem expInner_ne_expParent : expInner ≠ expParent :=
  fun h => expParent_ne_expInner h.symm

theorem expParent_ne_expServed : expParent ≠ expServed := by
  intro h
  have heq : parentRecordS.ts = servedRecord.ts := by
    rw [ts_eq_parent, ts_eq_served, h]
  rw [ts_parentRecordS, ts_servedRecord] at heq
  exact ts_4_ne_64 heq

theorem expInner_ne_expServed : expInner ≠ expServed := by
  intro h
  have heq : servedFormulaRecord.ts = servedRecord.ts := by
    rw [ts_eq_inner, ts_eq_served, h]
  rw [ts_servedFormulaRecord, ts_servedRecord] at heq
  exact ts_16_ne_64 heq

theorem memoryTreeAtS_zero : execSA.memoryTreeAt ⟨0, by norm_num [cfgS]⟩ = dummyHaltTreeS := rfl

theorem memoryTreeAtS_one : execSA.memoryTreeAt ⟨1, by norm_num [cfgS]⟩ = rootATreeA := rfl

theorem memoryTreeAtS_two : execSA.memoryTreeAt ⟨2, by norm_num [cfgS]⟩ = rootBTreeA := rfl


theorem axisPath_three : ServedMemoryTrace.axisPath 3 = [true] := by
  rw [ServedMemoryTrace.axisPath_of_two_le (by norm_num)]
  norm_num [ServedMemoryTrace.axisPath_of_lt_two]


theorem axisPath_two : ServedMemoryTrace.axisPath 2 = [false] := by
  rw [ServedMemoryTrace.axisPath_of_two_le (by norm_num)]
  norm_num [ServedMemoryTrace.axisPath_of_lt_two]

set_option maxRecDepth 400000 in
theorem axisTreeDummyS :
    exactAxisTree cfgS execSA ⟨0, by norm_num [cfgS]⟩ = MTree.halt := by
  rw [exactAxisTree, memoryTreeAtS_zero]
  simp [dummyHaltTreeS, Nock.AxisBridge.ofNTree, Nock.AxisBridge.MemWalk.toMTree,
    memLabelS, dummyHaltPubS]

set_option maxRecDepth 400000 in
/-- Root `A`'s exact axis tree: nested `read_root`/`verify_child` pairs on the two timestamps. -/
theorem axisTreeAS :
    exactAxisTree cfgS execSA ⟨1, by norm_num [cfgS]⟩ =
      MTree.read expParent
        (MTree.decompose MTree.halt
          (MTree.read expInner
            (MTree.verify expParent 3
              (MTree.decompose MTree.halt
                (MTree.verify expInner 3 MTree.halt))))) := by
  rw [exactAxisTree, memoryTreeAtS_one]
  simp [rootATreeA, aDecomposeOuterTreeA, aHeadHaltTree, aReadInnerTreeA, aVerifyOuterTreeA,
    aDecomposeInnerTreeA, aInnerHeadHaltTree, aVerifyInnerTreeA, aTailHaltTree,
    Nock.AxisBridge.ofNTree, Nock.AxisBridge.MemWalk.toMTree, memLabelS, timestampExpAt,
    expParent, expInner, aReadOuterPubA, aReadOuterPub, aReadInnerPubA, aReadInnerPub,
    aVerifyOuterPubA, aVerifyOuterPub, aVerifyInnerPubA, aVerifyInnerPub,
    parentRecordS, servedFormulaRecord]

set_option maxRecDepth 400000 in
/-- Root `B`'s exact axis tree: a single service reached by a genuine **left** descent. -/
theorem axisTreeBS :
    exactAxisTree cfgS execSA ⟨2, by norm_num [cfgS]⟩ =
      MTree.read expServed
        (MTree.decompose (MTree.verify expServed 2 MTree.halt) MTree.halt) := by
  rw [exactAxisTree, memoryTreeAtS_two]
  simp [rootBTreeA, bDecomposeTreeA, bVerifyTreeA, bResultHaltTree, bTailHaltTree,
    Nock.AxisBridge.ofNTree, Nock.AxisBridge.MemWalk.toMTree, memLabelS, timestampExpAt,
    expServed, bReadPubA, bReadPub, bVerifyPubA, bVerifyPub, servedRecord]

/-! ## S. The three compute-side services -/

theorem rawRequestsS :
    execSA.rawRequests = [parentRecordS, servedFormulaRecord, servedRecord] := by
  rw [ExactExecution.rawRequests_eq_computeRows, show execSA.computeRows =
    execS.computeRows from rfl,
    execution_rowsS.1]
  simp [NockVM.activeRequestRecords, parentRowS, servedRow, parentPubS, servedPub]

def serviceA1 : ServedMemoryTrace.Service cfgS execSA where
  exponent := expParent
  record := parentRecordS
  root := parentFormulaS
  child := formulaS
  axis := 3
  request_mem := by rw [rawRequestsS]; simp
  timestamp := ts_eq_parent
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [parentRecordS] }
  served := by simp [parentFormulaS, Noun.slot]

def serviceA2 : ServedMemoryTrace.Service cfgS execSA where
  exponent := expInner
  record := servedFormulaRecord
  root := formulaS
  child := tailS
  axis := 3
  request_mem := by rw [rawRequestsS]; simp
  timestamp := ts_eq_inner
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [servedFormulaRecord] }
  served := by simp [formulaS, Noun.slot]

def serviceB : ServedMemoryTrace.Service cfgS execSA where
  exponent := expServed
  record := servedRecord
  root := subjectS
  child := resultS
  axis := 2
  request_mem := by rw [rawRequestsS]; simp
  timestamp := ts_eq_served
  realization := servedRecord_realizes
  served := slot_subjectS

/-! ## T. The two root traces -/

theorem rootResponseRecordsDummy :
    ServedMemoryTrace.rootResponseRecords execSA ⟨0, by norm_num [cfgS]⟩ = [] := by
  simp [ServedMemoryTrace.rootResponseRecords, memoryTreeAtS_zero, dummyHaltTreeS,
    bfsForest, MemoryTable.responseRecords, memLabelS, dummyHaltPubS]

theorem rootResponseRecordsA :
    ServedMemoryTrace.rootResponseRecords execSA ⟨1, by norm_num [cfgS]⟩ =
      [parentRecordS, servedFormulaRecord] := by
  simp [ServedMemoryTrace.rootResponseRecords, memoryTreeAtS_one, rootATreeA,
    aDecomposeOuterTreeA, aHeadHaltTree, aReadInnerTreeA, aVerifyOuterTreeA,
    aDecomposeInnerTreeA, aInnerHeadHaltTree, aVerifyInnerTreeA, aTailHaltTree,
    bfsForest, MemoryTable.responseRecords, memLabelS, aReadOuterPubA, aReadOuterPub,
    aDecomposeOuterPub,
        aHeadHaltPub, aReadInnerPubA, aReadInnerPub, aVerifyOuterPubA, aVerifyOuterPub,
        aDecomposeInnerPub, aInnerHeadHaltPub,
            aVerifyInnerPubA, aVerifyInnerPub, aTailHaltPub]

theorem rootResponseRecordsB :
    ServedMemoryTrace.rootResponseRecords execSA ⟨2, by norm_num [cfgS]⟩ = [servedRecord] := by
  simp [ServedMemoryTrace.rootResponseRecords, memoryTreeAtS_two, rootBTreeA,
    bDecomposeTreeA, bVerifyTreeA, bResultHaltTree, bTailHaltTree,
    bfsForest, MemoryTable.responseRecords, memLabelS, bReadPubA, bReadPub, bDecomposePub,
    bVerifyPubA, bVerifyPub,
        bResultHaltPub, bTailHaltPub]

def rootTraceDummy :
    ServedMemoryTrace.RootTrace cfgS execSA ⟨0, by norm_num [cfgS]⟩ where
  subject := .atom 0
  services := []
  recordPartition := by rw [rootResponseRecordsDummy]; rfl
  readPartition := by rw [axisTreeDummyS]; simp [readExps]
  verifyPartition := by rw [axisTreeDummyS]; simp [verifyExps]
  traversal := by
    rw [axisTreeDummyS]
    exact ServedMemoryTrace.ServiceWalk.halt

/-- Root `A`'s exact service partition: two nested services, walked from the noun
`parentFormulaS`. -/
def rootTraceA :
    ServedMemoryTrace.RootTrace cfgS execSA ⟨1, by norm_num [cfgS]⟩ where
  subject := parentFormulaS
  services := [serviceA1, serviceA2]
  recordPartition := by rw [rootResponseRecordsA]; rfl
  readPartition := by rw [axisTreeAS]; simp [serviceA1, serviceA2, readExps]
  verifyPartition := by rw [axisTreeAS]; simp [serviceA1, serviceA2, verifyExps]
  traversal := by
    rw [axisTreeAS]
    refine ServedMemoryTrace.ServiceWalk.read serviceA1 (by simp) rfl rfl ?_ ?_
    · rw [show serviceA1.axis = 3 from rfl, axisPath_three]
      refine ServedMemoryTrace.VerifyRoute.right (by simp [readCount])
        (by simp [verifyCount]) ?_
      refine ServedMemoryTrace.VerifyRoute.read_other expInner_ne_expParent ?_
      exact ServedMemoryTrace.VerifyRoute.here rfl rfl (by simp [readCount])
        (by simp [verifyCount, expInner_ne_expParent])
    · refine ServedMemoryTrace.ServiceWalk.decompose ServedMemoryTrace.ServiceWalk.halt ?_
      refine ServedMemoryTrace.ServiceWalk.read serviceA2 (by simp) rfl rfl ?_ ?_
      · rw [show serviceA2.axis = 3 from rfl, axisPath_three]
        refine ServedMemoryTrace.VerifyRoute.verify_other expParent_ne_expInner ?_
        refine ServedMemoryTrace.VerifyRoute.right (by simp [readCount])
          (by simp [verifyCount]) ?_
        exact ServedMemoryTrace.VerifyRoute.here rfl rfl (by simp [readCount])
          (by simp [verifyCount])
      · exact ServedMemoryTrace.ServiceWalk.verify
          (ServedMemoryTrace.ServiceWalk.decompose ServedMemoryTrace.ServiceWalk.halt
            (ServedMemoryTrace.ServiceWalk.verify ServedMemoryTrace.ServiceWalk.halt))

/-- Root `B`'s exact service partition: one service on a left descent, walked from the noun
`subjectS`. -/
def rootTraceB :
    ServedMemoryTrace.RootTrace cfgS execSA ⟨2, by norm_num [cfgS]⟩ where
  subject := subjectS
  services := [serviceB]
  recordPartition := by rw [rootResponseRecordsB]; rfl
  readPartition := by rw [axisTreeBS]; simp [serviceB, readExps]
  verifyPartition := by rw [axisTreeBS]; simp [serviceB, verifyExps]
  traversal := by
    rw [axisTreeBS]
    refine ServedMemoryTrace.ServiceWalk.read serviceB (by simp) rfl rfl ?_ ?_
    · rw [show serviceB.axis = 2 from rfl, axisPath_two]
      refine ServedMemoryTrace.VerifyRoute.left ?_ (by simp [readCount])
        (by simp [verifyCount])
      exact ServedMemoryTrace.VerifyRoute.here rfl rfl (by simp [readCount])
        (by simp [verifyCount])
    · exact ServedMemoryTrace.ServiceWalk.decompose
        (ServedMemoryTrace.ServiceWalk.verify ServedMemoryTrace.ServiceWalk.halt)
        ServedMemoryTrace.ServiceWalk.halt

def rootTracesS : ∀ i : Fin cfgS.kMem, ServedMemoryTrace.RootTrace cfgS execSA i
  | ⟨0, _⟩ => rootTraceDummy
  | ⟨1, _⟩ => rootTraceA
  | ⟨2, _⟩ => rootTraceB
  | ⟨n + 3, h⟩ =>
      absurd (show n + 3 < 3 from by simpa [cfgS] using h) (by omega)

theorem rootTracesS_zero : rootTracesS ⟨0, by norm_num [cfgS]⟩ = rootTraceDummy := rfl

theorem rootTracesS_one : rootTracesS ⟨1, by norm_num [cfgS]⟩ = rootTraceA := rfl

theorem rootTracesS_two : rootTracesS ⟨2, by norm_num [cfgS]⟩ = rootTraceB := rfl

/-! ## U. The aggregate `intermediate` multiset across BOTH roots -/

theorem finRange_kMemS :
    List.finRange cfgS.kMem =
      [⟨0, by norm_num [cfgS]⟩, ⟨1, by norm_num [cfgS]⟩, ⟨2, by norm_num [cfgS]⟩] := rfl

/-- The whole forest's service timestamp multiset spans both serviced roots. -/
theorem forestTimestampPowersS :
    (List.finRange cfgS.kMem).flatMap
        (fun i => (rootTracesS i).timestampPowers) = [(4 : K97cubic), 16, 64] := by
  rw [finRange_kMemS]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    rootTracesS_zero, rootTracesS_one, rootTracesS_two]
  simp only [ServedMemoryTrace.RootTrace.timestampPowers,
    ServedMemoryTrace.RootTrace.exponents, rootTraceDummy, rootTraceA, rootTraceB,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rw [show (serviceA1.exponent : ℕ) = expParent from rfl,
    show (serviceA2.exponent : ℕ) = expInner from rfl,
    show (serviceB.exponent : ℕ) = expServed from rfl,
    ← ts_eq_parent, ← ts_eq_inner, ← ts_eq_served,
    ts_parentRecordS, ts_servedFormulaRecord, ts_servedRecord]


theorem forestTimestampPowers_nodupS :
    ((List.finRange cfgS.kMem).flatMap
      (fun i => (rootTracesS i).timestampPowers)).Nodup := by
  rw [forestTimestampPowersS]
  have h1 : (4 : K97cubic) ≠ 16 := ts_4_ne_16
  have h2 : (4 : K97cubic) ≠ 64 := ts_4_ne_64
  have h3 : (16 : K97cubic) ≠ 64 := ts_16_ne_64
  simp [h1, h2, h3]

/-- **The nonterminal OP0 `semanticCoverage` witness at the level of a whole execution.**  Row `1`
of the compute tree is the genuine `OP_0` row; its one served lookup is covered by root `B`'s
service. -/
def servedMemoryTraceS :
    ServedMemoryTrace.ExactServedMemoryTrace 97 3 cfgS execS semanticDataS execSA where
  roots := rootTracesS
  timestampPowersNodup := forestTimestampPowers_nodupS
  forestIndexRange := by
    rw [forestTimestampPowersS]
    norm_num [IO.InRange, cfgS]
  semanticCoverage := by
    intro row lookup hlookup
    have hl : lookup ∈ (rowDataS row).needs.served := hlookup
    rcases row with ⟨v, hv⟩
    match v, hv with
    | 0, hv =>
        exfalso
        have hmem : lookupTuple lookup ∈
            (rowDataS ⟨0, hv⟩).needs.served.map lookupTuple :=
          List.mem_map_of_mem hl
        rw [rowDataS_zero_servedTuples] at hmem
        simp at hmem
    | 1, hv =>
        have hmem : lookupTuple lookup ∈
            (rowDataS ⟨1, hv⟩).needs.served.map lookupTuple :=
          List.mem_map_of_mem hl
        rw [rowDataS_one_servedTuples] at hmem
        simp only [List.mem_singleton] at hmem
        have htuple : (lookup.record, lookup.root, lookup.axis, lookup.child) =
            (servedRecord, subjectS, 2, resultS) := hmem
        refine ⟨⟨2, by norm_num [cfgS]⟩, serviceB, ?_, ?_, ?_, ?_, ?_⟩
        · rw [rootTracesS_two]
          simp [rootTraceB]
        · have hc := congrArg Prod.fst htuple
          simpa [serviceB] using hc.symm
        · have hc := congrArg (fun p => p.2.1) htuple
          simpa [serviceB] using hc.symm
        · have hc := congrArg (fun p => p.2.2.2) htuple
          simpa [serviceB] using hc.symm
        · have hc := congrArg (fun p => p.2.2.1) htuple
          simpa [serviceB] using hc.symm
    | (n + 2), hv =>
        exact absurd (show n + 2 < 2 from by simpa [cfgS] using hv) (by omega)

/-! ## V. The buildable execution: all fourteen fields named explicitly -/

theorem ringChar_K97 : ringChar K97cubic = 97 := by
  rw [← Algebra.ringChar_eq F97 K97cubic, ZMod.ringChar_zmod_n]

theorem memoryStateCountsS :
    RowLayout.memoryStateCount execS .read_root = 3 ∧
      RowLayout.memoryStateCount execS .verify_child = 3 ∧
      RowLayout.memoryStateCount execS .decompose = 3 ∧
      RowLayout.memoryStateCount execS .halt = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [RowLayout.memoryStateCount, RowLayout.fibreCount, execution_rowsS.2, memLabelS,
      dummyHaltPubS, aReadOuterPub, bReadPub, aDecomposeOuterPub, bDecomposePub, aHeadHaltPub,
      aReadInnerPub, bVerifyPub, bTailHaltPub, aVerifyOuterPub, bResultHaltPub,
      aDecomposeInnerPub, aInnerHeadHaltPub, aVerifyInnerPub, aTailHaltPub]

theorem addedRecordListS :
    RowLayout.addedRecordList execS =
      [NockVM.formRRow parentRecordS MemoryTable.formRDefault,
          NockVM.formRRow servedRecord MemoryTable.formRDefault,
        NockVM.formRRow servedFormulaRecord MemoryTable.formRDefault] := by
  rw [RowLayout.addedRecordList, execution_rowsS.2]
  simp [memLabelS, dummyHaltPubS, aReadOuterPub, bReadPub, aDecomposeOuterPub,
    bDecomposePub, aHeadHaltPub, aReadInnerPub, bVerifyPub, bTailHaltPub, aVerifyOuterPub,
    bResultHaltPub, aDecomposeInnerPub, aInnerHeadHaltPub, aVerifyInnerPub, aTailHaltPub]

theorem consumedRecordListS :
    RowLayout.consumedRecordList execS =
      [NockVM.formRRow servedRecord MemoryTable.formRDefault,
          NockVM.formRRow parentRecordS MemoryTable.formRDefault,
        NockVM.formRRow servedFormulaRecord MemoryTable.formRDefault] := by
  rw [RowLayout.consumedRecordList, execution_rowsS.2]
  simp [RowLayout.consumedRecords, memLabelS, dummyHaltPubS, aReadOuterPub, bReadPub, aDecomposeOuterPub,
    bDecomposePub, aHeadHaltPub, aReadInnerPub, bVerifyPub, bTailHaltPub, aVerifyOuterPub,
    bResultHaltPub, aDecomposeInnerPub, aInnerHeadHaltPub, aVerifyInnerPub, aTailHaltPub]


theorem pairedRecordLayoutS : RowLayout.PairedRecordLayout execS := by
  rw [RowLayout.PairedRecordLayout, addedRecordListS, consumedRecordListS]
  exact (List.Perm.swap (NockVM.formRRow servedRecord MemoryTable.formRDefault)
    (NockVM.formRRow parentRecordS MemoryTable.formRDefault)
    [NockVM.formRRow servedFormulaRecord MemoryTable.formRDefault]).symm

/-- Honest `ver = (st = read_root)` on the multi-root fixture (structure default). -/
theorem honestVerS :
    ∀ row ∈ execS.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  intro row hrow
  -- Fixture pubs omit `ver`, so the structure default `decide (st = read_root)` applies.
  simp [execution_rowsS.2, memLabelS, dummyHaltLabelS, aReadOuterLabel, bReadLabel, aDecomposeOuterLabel,
    bDecomposeLabel, aHeadHaltLabel, aReadInnerLabel, bVerifyLabel, bTailHaltLabel,
    aVerifyOuterLabel, bResultHaltLabel, aDecomposeInnerLabel, aInnerHeadHaltLabel,
    aVerifyInnerLabel, aTailHaltLabel, dummyHaltPubS, aReadOuterPub, aDecomposeOuterPub, aHeadHaltPub,
    aReadInnerPub, aVerifyOuterPub, aDecomposeInnerPub, aInnerHeadHaltPub, aVerifyInnerPub,
    aTailHaltPub, bReadPub, bDecomposePub, bVerifyPub, bResultHaltPub, bTailHaltPub] at hrow
  rcases hrow with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (subst h; rfl)



theorem recordCountBalanceS : RowLayout.RecordCountBalanced execS := by
  rw [RowLayout.RecordCountBalanced, memoryStateCountsS.1, memoryStateCountsS.2.1]


theorem memoryBudgetS :
    RowLayout.memoryM execS = 9 ∧ RowLayout.memoryL execS = 3 ∧
      cfgS.memRows = RowLayout.memoryM execS + 2 * RowLayout.memoryL execS := by
  refine ⟨?_, ?_, ?_⟩
  · rw [RowLayout.memoryM, memoryStateCountsS.2.2.1, memoryStateCountsS.2.2.2]
  · exact memoryStateCountsS.1
  · rw [RowLayout.memoryM, RowLayout.memoryL, memoryStateCountsS.2.2.1,
      memoryStateCountsS.2.2.2, memoryStateCountsS.1]
    norm_num [cfgS]

/-- **The multi-root buildable execution.**  All fourteen input fields are named explicitly; in
particular `memoryTrace` is the two-serviced-root `ExactServedMemoryTrace` above and `two_ne_zero`
is supplied, neither having a default. -/
def multiRootExecution : BuildableNockExecution F97 K97cubic where
  q := 97
  q_gt_one := by norm_num
  Λ := 3
  cfg := cfgS
  execA := execSA
  exec := execS
  exec_encode := execS_encode
  semanticData := semanticDataS
  memoryTrace := servedMemoryTraceS
  requestNodup := requestsS_nodup
  recordCountBalance := recordCountBalanceS
  q_le_ringChar := by rw [ringChar_K97]
  two_ne_zero := two_ne_zero_K97
  Ksz_lt_ringChar := by rw [ringChar_K97]; norm_num [cfgS]
  programIOCapacity := by
    rw [derived_requestsS]
    norm_num [cfgS, executionOrbit97]
  memoryIOCapacity := by
    rw [derived_responsesS]
    norm_num [cfgS, executionOrbit97]

/-- Honest `ver` on the buildable multi-root execution. -/
theorem honestVerM :
    ∀ row ∈ multiRootExecution.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) :=
  honestVerS

/-! ## W. Pre-compilation backend inputs for the generic constructors -/

open Module StrictExtension BuildableChips
open OptimizedMemorySameExecution OptimizedStrictFullPackage

/-- Strict RAP orbit of exact order `3 · 2^4 = 48`, the height the fourteen-row `M + 2L` prefix
needs. -/
def strictOrbitM : StrictOrbitDomain F97 3 4 where
  ω := Classical.choose (exists_zmod_generator_of_dvd_sub_one 97 48 (by norm_num))
  βcoset := 1
  e_pos := by norm_num
  h_pos := by norm_num
  order_ω := by
    simpa using Classical.choose_spec
      (exists_zmod_generator_of_dvd_sub_one 97 48 (by norm_num))
  βcoset_ne_zero := one_ne_zero

def sampledRecordsM : FiniteIO.PreChallengeRecords K97cubic 9 :=
  executionRecords multiRootExecution

theorem sampledRecordsM_lengths :
    sampledRecordsM.requests.length = 3 ∧ sampledRecordsM.responses.length = 3 := by
  constructor
  · change execS.derivedRequestIO.length = 3
    rw [derived_requestsS]; rfl
  · change execS.derivedResponseIO.length = 3
    rw [derived_responsesS]; rfl

theorem cardK97cubic : Fintype.card K97cubic = 97 ^ 3 := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 97 3 (by norm_num)

theorem ioFailureBoundM :
    (FiniteIO.IOFailureEvent sampledRecordsM).card <
      Fintype.card (K97cubic × K97cubic) := by
  refine lt_of_le_of_lt (FiniteIO.IOFailureEvent_card_le sampledRecordsM) ?_
  rw [sampledRecordsM_lengths.1, sampledRecordsM_lengths.2]
  simp only [FiniteIO.ioFailureUnionBound, Fintype.card_prod]
  rw [cardK97cubic]
  norm_num

theorem goodIOCoinsM_exists :
    ∃ coins : FiniteIO.IOCoins K97cubic,
      (coins.gamma, coins.pole) ∉ FiniteIO.IOFailureEvent (sampledRecordsM) ∧
      (coins.gamma, coins.pole) ∉ FiniteIO.IOFailureEvent (BuildableChips.executionRecords10 (multiRootExecution)) :=
  RecordCarrier.exists_io_coins_ext _ (sampledRecordsM)
    (sampledRecordsM_lengths).1.le (sampledRecordsM_lengths).2.le
    (by
      rw [RecordCarrier.honestIOBound_eq, Fintype.card_prod, cardK97cubic]
      norm_num)

def ioCoinsM : FiniteIO.IOCoins K97cubic := Classical.choose goodIOCoinsM_exists

theorem ioCoinsM_good :
    (ioCoinsM.gamma, ioCoinsM.pole) ∉ FiniteIO.IOFailureEvent sampledRecordsM :=
  (Classical.choose_spec (goodIOCoinsM_exists)).1

theorem ioCoinsM_good10 :
    (ioCoinsM.gamma, ioCoinsM.pole) ∉
      FiniteIO.IOFailureEvent (BuildableChips.executionRecords10 (multiRootExecution)) :=
  (Classical.choose_spec (goodIOCoinsM_exists)).2

theorem inputsM_interCard :
    2 * ((executionInterRecords multiRootExecution).requests.length +
      (executionInterRecords multiRootExecution).responses.length) + 1 < Fintype.card K97cubic :=
  executionInterRecords_card_lt_of_memRows_eq multiRootExecution
    (show multiRootExecution.cfg.memRows = 15 from rfl)
    cardK97cubic
    (by norm_num)


def inputsM : Inputs multiRootExecution where
  stateTagChar := stateTagChar97
  computeWalkAlpha := 2
  memoryWalkAlpha := 3
  walkGamma := 5
  hOrb := 4
  basis := basis97
  orbit := strictOrbitM
  activeDomains :=
    { computeCapacity := by norm_num [multiRootExecution, cfgS]
      memoryCapacity := by
        rw [show RowLayout.memoryM multiRootExecution.exec = 9 from memoryBudgetS.1,
          show RowLayout.memoryL multiRootExecution.exec = 3 from memoryBudgetS.2.1]
        norm_num }
  ioCoins := ioCoinsM
  ioPoleHitGood := by
    intro h
    apply ioCoinsM_good
    unfold FiniteIO.IOFailureEvent
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    exact Or.inr (Or.inl h)
  ioGammaGood := by
    intro h
    apply ioCoinsM_good
    unfold FiniteIO.IOFailureEvent
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    exact Or.inl h
  ioLogDerivGood := by
    intro h
    apply ioCoinsM_good
    unfold FiniteIO.IOFailureEvent
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    exact Or.inr (Or.inr h)
  computeChallenges := default
  memoryScalarChallenge := fun j => (j : F97) + 1
  memoryExtensionFold :=
    interPoleOfE multiRootExecution ioCoinsM.gamma inputsM_interCard
  interPoleHitGood :=
    interPoleOfE_good multiRootExecution ioCoinsM.gamma inputsM_interCard
  honestVer := honestVerM
  ioGood10 := ioCoinsM_good10
  interPoleHitGood10 :=
    interPoleOfE_good10 (multiRootExecution) ioCoinsM.gamma inputsM_interCard

theorem inputsM_challenges : inputsM.computeChallenges = default := rfl

/-! ## X. The generic constructors, run on the multi-root fixture -/

/-- Milestone 1: the sampled same-execution assignment. -/
def sampledAssignmentM :
    SampledIOSameExecutionAssignment
      (exactFamilyCompletion multiRootExecution inputsM).family (ringChar K97cubic) :=
  sampledAssignment multiRootExecution inputsM

/-- Milestone 3: the optimized topology payload, both chips and both coordinate layouts. -/
def topologyM : BuildableTopology multiRootExecution :=
  buildTopology multiRootExecution inputsM

/-- Milestone 3: the canonical polynomial traces of both chips. -/
def tracesM : BuildableTopologyTraces topologyM :=
  buildTraces multiRootExecution inputsM

/-- F97's first compute row (`parentPubS`) has `ln_prev = 1` — the origin the W6.1 stage-2A gate
`finalLnInit` pins. -/
theorem lineOriginM :
    (multiRootExecution.exec.computePubAt ⟨0, multiRootExecution.cfg.compRows_pos⟩).ln_prev = 1 := by
  change (execS.computePubAt ⟨0, cfgS.compRows_pos⟩).ln_prev = 1
  rw [computePubAtS_zero]
  rfl

/-- Milestone 3: both traces satisfy their chips with the pinned preprocessing. -/
theorem walkOrderM :
    2 ≤ multiRootExecution.cfg.compRows →
      multiRootExecution.cfg.compRows ≤ orderOf inputsM.computeWalkAlpha := fun _ => by
  have hα : inputsM.computeWalkAlpha = (2 : K97cubic) := rfl
  have hrows : multiRootExecution.cfg.compRows = 2 := rfl
  rw [hα, omega2_order, hrows]
  norm_num

theorem walkOrderMem :
    2 ≤ multiRootExecution.cfg.memRows →
      multiRootExecution.cfg.memRows ≤ orderOf inputsM.memoryWalkAlpha := fun _ => by
  have hα : inputsM.memoryWalkAlpha = (3 : K97cubic) := rfl
  have hrows : multiRootExecution.cfg.memRows = 15 := rfl
  rw [hα, omega3_order, hrows]
  norm_num

/-- H1.5b Part 2a `rowsBound` of this fixture: `3·2 < 97` and `15 < 97`. -/
theorem rowsBoundM :
    3 * multiRootExecution.cfg.compRows < ringChar K97cubic ∧
      multiRootExecution.cfg.memRows < ringChar K97cubic := by
  rw [ringChar_K97]
  have h1 : multiRootExecution.cfg.compRows = 2 := rfl
  have h2 : multiRootExecution.cfg.memRows = 15 := rfl
  rw [h1, h2]
  norm_num

theorem traceSatisfactionM
    (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)
    (hax : FormRAxisBound sampledAssignmentM inputsM.basis)
    (hbasis : FormRBasis inputsM.basis)
    (hwidth : FormRWidth F97)
    (hhalt : MemoryHaltLeavesHonest.HaltRowsBase (F := F97) multiRootExecution.exec) :
    BuildableTraceSatisfaction topologyM tracesM :=
  buildTraceSatisfaction multiRootExecution inputsM lineOriginM pairedRecordLayoutS hmoreM walkOrderM walkOrderMem
    execS_cprimeCoherent hax hbasis hwidth hhalt

/-- **Milestone 4 on a multi-root fixture.**  The full sampled `MemoryProductionAssignment`,
whose axis-side fields come from the two-serviced-root `ExactServedMemoryTrace` above
. -/
def memoryProductionM (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution) :
    MemoryProductionAssignment sampledAssignmentM execSA :=
  BuildableAxisWitness.buildableMemoryProductionAssignment multiRootExecution inputsM hmoreM

/-- Pinned optimized resources and active-row budgets of the multi-root fixture
(`Thm:comp_38`/`Thm:mem_38`). -/
theorem resourcesM :
    topologyM.computeChip.rap.w = 303 ∧ topologyM.computeChip.rap.s = 418 ∧
      topologyM.memoryChip.rap.w = 205 ∧ topologyM.memoryChip.rap.s = 156 ∧
      topologyM.computeDomain.card = 2 ∧ topologyM.memoryDomain.card = 15 := by
  refine ⟨(chip_resources multiRootExecution inputsM).1,
    (chip_resources multiRootExecution inputsM).2.1,
    (chip_resources multiRootExecution inputsM).2.2.1,
    (chip_resources multiRootExecution inputsM).2.2.2, ?_, ?_⟩
  · show (buildTopology multiRootExecution inputsM).computeDomain.card = 2
    rw [(raw_row_cards multiRootExecution inputsM).1]
    rfl
  · show (buildTopology multiRootExecution inputsM).memoryDomain.card = 15
    rw [(raw_row_cards multiRootExecution inputsM).2,
      show RowLayout.memoryM multiRootExecution.exec = 9 from memoryBudgetS.1,
      show RowLayout.memoryL multiRootExecution.exec = 3 from memoryBudgetS.2.1]


theorem sameExecutionM (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution) :
    topologyM.rawFamily.problem = ⟨cfgS, execS⟩ ∧
      (exactFamilyCompletion multiRootExecution inputsM).family.problem.cfg = cfgS ∧
      (exactFamilyCompletion multiRootExecution inputsM).family.problem.exec = execS ∧
      (memoryProductionM hmoreM).axisStructural = servedMemoryTraceS.axisStructural :=
  ⟨topology_problem_same_execution multiRootExecution inputsM, rfl, rfl, rfl⟩

/-- The axis conclusion the multi-root production assignment exports, on both serviced roots. -/
theorem axis_eq_relaxis_of_usedM
    (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)
    (root : Fin cfgS.kMem) (e : ℕ)
    (hread : e ∈ readExps (exactAxisTree cfgS execSA root))
    (hverify : e ∈ verifyExps (exactAxisTree cfgS execSA root)) :
    vaxis e (exactAxisTree cfgS execSA root) =
      Relaxis e (exactAxisTree cfgS execSA root) :=
  MemoryProductionAssignment.axis_eq_relaxis_of_used two_ne_zero_K97 (memoryProductionM hmoreM)
    root e hread hverify

/-! ## Y. The Milestone-5 boundary for this fixture, stated honestly

`buildFullPackage` and `universalOptimizedFullStrictThm54` are *conditional* on a
`BuildablePackage.CommitmentResidual`, the committed P8 template/skeleton layer of
the paper. What compiles is the implication: for **every** residual over this
fixture, the released fourteen-field statement holds of the constructed package. -/
theorem universalStatement_of_residualM
    (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)
    (R : BuildablePackage.CommitmentResidual multiRootExecution)
    (hgenF : GeneratedField.ClaimGenerated K97cubic R.verifier.raw.claim R.Λ)
    (hax : FormRAxisBound
      (BuildablePackage.buildFullPackage multiRootExecution inputsM R inputsM_challenges
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM).optimized.sampled
      (BuildablePackage.buildFullPackage multiRootExecution inputsM R inputsM_challenges
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM).optimized.basis)
    (hbasis : FormRBasis
      (BuildablePackage.buildFullPackage multiRootExecution inputsM R inputsM_challenges
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedFullStrictThm54Statement
      (BuildablePackage.buildFullPackage multiRootExecution inputsM R inputsM_challenges
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM) :=
  BuildablePackage.universalOptimizedFullStrictThm54 multiRootExecution inputsM R
    inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
    hgenF (by prime_field_elems) hax hbasis hwidth

/-! ## Z. -/

/-- **Deferred item 1, closed: a nonterminal OP0 `semanticCoverage` inhabitant at the level of a
whole execution.**  The compute tree is a nonterminal `OP_4` root whose single successor is the
`OP_0` row; that row's `requiredServedLookups` is `1`, its actual served
lookup is the slot `(subjectS, axis 2) ↦ resultS`, and the whole-execution `semanticCoverage` field
of `servedMemoryTraceS` covers it with an actual forest service. -/
theorem deferred_nonterminal_semanticCoverage_closed :
    execS.computeRows = [parentRowS, servedRow] ∧
      ComputeTable.fanoutComp parentRowS.1 = 1 ∧
      parentOutS 0 = some servedRow ∧
      SemanticTrace.requiredServedLookups servedRow.1 = 1 ∧
      (rowDataS ⟨1, by norm_num [cfgS]⟩).needs.served.map lookupTuple =
        [(servedRecord, subjectS, 2, resultS)] ∧
      (∃ (i : Fin cfgS.kMem) (s : ServedMemoryTrace.Service cfgS execSA),
        s ∈ (servedMemoryTraceS.roots i).services ∧ s.record = servedRecord ∧
          s.root = subjectS ∧ s.child = resultS ∧ s.axis = 2) := by
  refine ⟨execution_rowsS.1, rfl, rfl, rfl, rowDataS_one_servedTuples,
    ⟨⟨2, by norm_num [cfgS]⟩, serviceB, ?_, rfl, rfl, rfl, rfl⟩⟩
  change serviceB ∈ (rootTracesS ⟨2, _⟩).services
  rw [rootTracesS_two]
  simp [rootTraceB]

/-- **Deferred item 2, closed: a two-serviced-root fixture exercising the cross-root global
timestamp premise.**  Both supplied roots emit records, the aggregate `intermediate` multiset is
the union of the two roots' service timestamps, its `Nodup` is genuinely cross-root, and the one
global `L_mIO` matching of the paper is discharged on it. -/
theorem deferred_two_serviced_roots_closed :
    cfgS.kMem = 3 ∧
      ServedMemoryTrace.rootResponseRecords execSA ⟨0, by norm_num [cfgS]⟩ = [] ∧
      ServedMemoryTrace.rootResponseRecords execSA ⟨1, by norm_num [cfgS]⟩ =
        [parentRecordS, servedFormulaRecord] ∧
      ServedMemoryTrace.rootResponseRecords execSA ⟨2, by norm_num [cfgS]⟩ = [servedRecord] ∧
      (List.finRange cfgS.kMem).flatMap
          (fun i => (rootTracesS i).timestampPowers) = [(4 : K97cubic), 16, 64] ∧
      ((List.finRange cfgS.kMem).flatMap
        (fun i => (rootTracesS i).timestampPowers)).Nodup ∧
      IO.LmIO cfgS.Ksz (forestReadTimestamps cfgS execSA)
        (forestVerifyTimestamps cfgS execSA) :=
  ⟨rfl, rootResponseRecordsDummy, rootResponseRecordsA, rootResponseRecordsB, forestTimestampPowersS,
    forestTimestampPowers_nodupS, servedMemoryTraceS.intermediateMatching⟩


theorem both_roots_serviced :
    (rootTracesS ⟨1, by norm_num [cfgS]⟩).services ≠ [] ∧
      (rootTracesS ⟨2, by norm_num [cfgS]⟩).services ≠ [] := by
  refine ⟨?_, ?_⟩
  · rw [rootTracesS_one]; simp [rootTraceA]
  · rw [rootTracesS_two]; simp [rootTraceB]

/-- **Deferred item 3, closed: a full sampled `MemoryProductionAssignment` on a multi-root
execution.**  Its primitive table/walk/IO obligations are the Milestone-3 sampled ones and its two
axis-side fields come from the two-serviced-root `ExactServedMemoryTrace`
. -/
theorem deferred_full_sampled_memoryProduction_closed
    (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution) :
    Nonempty (MemoryProductionAssignment sampledAssignmentM execSA) ∧
      (memoryProductionM hmoreM).obligations =
        (memoryChipAssignment multiRootExecution inputsM).obligations ∧
      (memoryProductionM hmoreM).axisStructural = servedMemoryTraceS.axisStructural ∧
      (∀ i : Fin cfgS.kMem, countsP_bin (exactAxisTree cfgS execSA i) = 0) :=
  ⟨⟨memoryProductionM hmoreM⟩, rfl, rfl, (memoryProductionM hmoreM).axisRootPolynomial⟩

/-- The fixture is at a repaired seed, so the F97 obstruction of `NonterminalServedRow` does not
apply to it: `servedSeed` has multiplicative order `2 > 1`, hence every atom has a bounded power
window. -/
theorem fixture_seed_is_repaired :
    cfgS.challenges.z = servedSeed ∧ 1 < orderOf servedSeed ∧
      cfgS.challenges.z ≠ fixtureSeed :=
  ⟨rfl, one_lt_orderOf_servedSeed, by
    rw [show cfgS.challenges.z = servedSeed from rfl, fixtureSeed_eq_one]
    exact neg_one_ne_one_K97⟩

end

end Nock.NockVMROM.Thm54.MultiRootServedFixture

#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.pole_parentRecordS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.pole_servedFormulaRecord
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.pole_servedRecord
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.aReadOuter_accepts
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.aDecomposeOuter_accepts
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.aReadInner_accepts
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.aVerifyOuter_accepts
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.aVerifyInner_accepts
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.bRead_accepts
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.bDecompose_accepts
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.bVerify_accepts
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.rootATree_rvt
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.rootBTree_rvt
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.execution_rowsS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.derived_requestsS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.derived_responsesS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.requestsS_nodup
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.responsesS_nodup
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.compute_rows_acceptedS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.memory_rows_acceptedS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.memory_chainS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.accumulator_valuesS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.semanticPreimageS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.chainedS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.compute_topologyS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.memory_topologyS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.traversableS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.nounRealizationS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.languageS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.rowDataS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.rowDataS_one_servedTuples
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.semanticDataS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.axisTreeAS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.axisTreeBS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.serviceA1
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.serviceA2
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.serviceB
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.rootTraceA
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.rootTraceB
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.forestTimestampPowersS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.forestTimestampPowers_nodupS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.servedMemoryTraceS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.recordCountBalanceS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.memoryBudgetS
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.multiRootExecution
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.inputsM
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.sampledAssignmentM
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.topologyM
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.tracesM
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.traceSatisfactionM
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.memoryProductionM
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.resourcesM
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.sameExecutionM
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.axis_eq_relaxis_of_usedM
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.universalStatement_of_residualM
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.deferred_nonterminal_semanticCoverage_closed
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.deferred_two_serviced_roots_closed
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.both_roots_serviced
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.deferred_full_sampled_memoryProduction_closed
#print axioms Nock.NockVMROM.Thm54.MultiRootServedFixture.fixture_seed_is_repaired
