import Nock.NockVMROM.Thm54.HonestCommitment
import Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# The honest commitment of the two-serviced-root nonterminal fixture

Until
now the only inhabitant of `Data` was over the terminal single-row F73 fixture.

This module inhabits `Data multiRootExecution`: the committed skeleton, the committed Nat timestamp
exponents, and the honest-seed bindings of the **two-compute-row, fourteen-memory-row,
two-serviced-root** exact execution of `MultiRootServedFixture`.

Two obligations are genuinely non-vacuous here for the first time.  The committed `OP_0` row has
`state =.s0`, so `SkeletonSlotSemantics.s0_slot` is a real Nock slot fact —
`Noun.slot 2 subjectS = some resultS` — and `SkeletonRecordEquations.s0_record`
really identifies the committed `mr2` root/child with the row's subject and evaluation.  At F73 both were discharged by `absurd` on the row state.
-/

namespace Nock.NockVMROM.Thm54.MultiRootHonestCommitment

open scoped Classical
open Nock Nock.Noun Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open SemanticStrategy SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance prime97h : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97h : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-! ## A. The committed memory-record skeletons -/

/-- The `OP_4` parent's one emitted record: root `parentFormulaS`, child `formulaS`, axis `3`. -/
def parentRecordSkeleton : MemRecSkeleton where
  root := parentFormulaS
  child := formulaS
  axis := 3

/-- The `OP_0` row's `mr1`: root `formulaS`, child `tailS`, axis `3`. -/
def innerRecordSkeleton : MemRecSkeleton where
  root := formulaS
  child := tailS
  axis := 3

/-- **The `OP_0` row's `mr2`, the actual slot lookup**. -/
def servedRecordSkeleton : MemRecSkeleton where
  root := subjectS
  child := resultS
  axis := 2

/-! ## B. The two committed compute-row skeletons -/

/-- The nonterminal `OP_4` parent skeleton. -/
def parentSkeletonRow : ComputeRowSkeleton where
  state := .s4
  subject := subjectS
  formula := parentFormulaS
  evaluation := parentResultS
  decomposition := fun slot _ =>
    match slot with
    | .f_h => parentHeadS
    | .f_t => formulaS
    | _ => .atom 0
  subformula := fun _ _ slot =>
    match slot with
    | .subject => subjectS
    | .formula => formulaS
    | .result => resultS
  memoryRecord := fun _ _ => parentRecordSkeleton

/-- The served `OP_0` skeleton. -/
def servedSkeletonRow : ComputeRowSkeleton where
  state := .s0
  subject := subjectS
  formula := formulaS
  evaluation := resultS
  decomposition := fun slot _ =>
    match slot with
    | .f_h => headS
    | .f_t => tailS
    | _ => .atom 0
  subformula := fun i hi _ => absurd hi (by simp [ComputeTable.fanoutComp])
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then innerRecordSkeleton else servedRecordSkeleton

/-! ## C. The fourteen committed memory-row skeletons -/

def aReadOuterSkel : MemoryRowSkeleton where
  state := .read_root
  parent := parentFormulaS
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => parentFormulaS
  memoryRecord := fun _ => parentRecordSkeleton

def aDecomposeOuterSkel : MemoryRowSkeleton where
  state := .decompose
  parent := parentFormulaS
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then parentHeadS else formulaS
  memoryRecord := fun h => nomatch h

def dummyHaltSkel : MemoryRowSkeleton where
  state := .halt
  parent := .atom 0
  haltAtom := fun _ => 0
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

def aHeadHaltSkel : MemoryRowSkeleton where
  state := .halt
  parent := parentHeadS
  haltAtom := fun _ => 4
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

def aReadInnerSkel : MemoryRowSkeleton where
  state := .read_root
  parent := formulaS
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => formulaS
  memoryRecord := fun _ => innerRecordSkeleton

def aVerifyOuterSkel : MemoryRowSkeleton where
  state := .verify_child
  parent := formulaS
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => formulaS
  memoryRecord := fun _ => parentRecordSkeleton

def aDecomposeInnerSkel : MemoryRowSkeleton where
  state := .decompose
  parent := formulaS
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then headS else tailS
  memoryRecord := fun h => nomatch h

def aInnerHeadHaltSkel : MemoryRowSkeleton where
  state := .halt
  parent := headS
  haltAtom := fun _ => 0
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

def aVerifyInnerSkel : MemoryRowSkeleton where
  state := .verify_child
  parent := tailS
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => tailS
  memoryRecord := fun _ => innerRecordSkeleton

def aTailHaltSkel : MemoryRowSkeleton where
  state := .halt
  parent := tailS
  haltAtom := fun _ => 2
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

def bReadSkel : MemoryRowSkeleton where
  state := .read_root
  parent := subjectS
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => subjectS
  memoryRecord := fun _ => servedRecordSkeleton

def bDecomposeSkel : MemoryRowSkeleton where
  state := .decompose
  parent := subjectS
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then resultS else bTailNoun
  memoryRecord := fun h => nomatch h

def bVerifySkel : MemoryRowSkeleton where
  state := .verify_child
  parent := resultS
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => resultS
  memoryRecord := fun _ => servedRecordSkeleton

def bResultHaltSkel : MemoryRowSkeleton where
  state := .halt
  parent := resultS
  haltAtom := fun _ => 7
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

def bTailHaltSkel : MemoryRowSkeleton where
  state := .halt
  parent := bTailNoun
  haltAtom := fun _ => 9
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

/-! ## D. The committed Nat timestamp exponents -/

def parentStamp : ComputeTimestampRow where
  state := .s4
  lnPrevExponent := 0
  lnExponent := 1
  recordExponent := fun _ => 1

def servedStamp : ComputeTimestampRow where
  state := .s0
  lnPrevExponent := 1
  lnExponent := 3
  recordExponent := fun i => if (i : ℕ) = 0 then 2 else 3

def memStamp (st : MState) (e : ℕ) : MemoryTimestampRow where
  state := st
  recordExponent := e

/-! ## E. Honest-seed bindings of the two compute rows -/

theorem bind_parentRow :
    BindComputeRow servedSeed parentSkeletonRow parentRowS := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP,
        parentSkeletonRow, parentRowS, parentDecS, encS]
  · intro i
    fin_cases i
    · rw [dif_pos (by simp [parentSkeletonRow, ComputeTable.fanoutComp])]
      intro slot
      cases slot <;> rfl
    · rw [dif_neg (by simp [parentSkeletonRow, ComputeTable.fanoutComp])]
      rfl
    · rw [dif_neg (by simp [parentSkeletonRow, ComputeTable.fanoutComp])]
      rfl
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, by norm_num [parentSkeletonRow, parentRecordSkeleton, parentRowS,
        parentPubS, parentRecordS, computeMemRec]⟩
    · rfl
    · rfl

theorem bind_servedRow :
    BindComputeRow servedSeed servedSkeletonRow servedRow := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP,
        servedSkeletonRow, servedRow, servedDec, encS]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp servedSkeletonRow.state) := by
      simp [servedSkeletonRow, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, servedRow, servedPub]
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, by norm_num [servedSkeletonRow, innerRecordSkeleton, servedRow,
        servedPub, servedFormulaRecord, computeMemRec]⟩
    · exact ⟨rfl, rfl, by norm_num [servedSkeletonRow, servedRecordSkeleton, servedRow,
        servedPub, servedRecord, computeMemRec]⟩
    · rfl

/-! ## F. Honest-seed bindings of the fourteen memory rows -/

theorem bind_dummyHalt :
    BindMemoryRowA servedSeed dummyHaltSkel dummyHaltLabelS := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem dummyHaltSkel.state) := by
      simp [dummyHaltSkel, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_aReadOuter :
    BindMemoryRowA servedSeed aReadOuterSkel aReadOuterLabelA := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [aReadOuterSkel, MemoryTable.fanoutMem, memoryChildCell, memLabelS, aReadOuterPubA,
    aReadOuterPub]
  · exact ⟨rfl, rfl, by norm_num [aReadOuterSkel, parentRecordSkeleton, memLabelS,
      aReadOuterPubA, aReadOuterPub, parentRecordS]⟩

theorem bind_aDecomposeOuter :
    BindMemoryRowA servedSeed aDecomposeOuterSkel aDecomposeOuterLabel := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_aHeadHalt :
    BindMemoryRowA servedSeed aHeadHaltSkel aHeadHaltLabel := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem aHeadHaltSkel.state) := by
      simp [aHeadHaltSkel, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_aReadInner :
    BindMemoryRowA servedSeed aReadInnerSkel aReadInnerLabelA := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [aReadInnerSkel, MemoryTable.fanoutMem, memoryChildCell, memLabelS, aReadInnerPubA,
    aReadInnerPub]
  · exact ⟨rfl, rfl, by norm_num [aReadInnerSkel, innerRecordSkeleton, memLabelS,
      aReadInnerPubA, aReadInnerPub, servedFormulaRecord]⟩

theorem bind_aVerifyOuter :
    BindMemoryRowA servedSeed aVerifyOuterSkel aVerifyOuterLabelA := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [aVerifyOuterSkel, MemoryTable.fanoutMem, memoryChildCell, memLabelS, aVerifyOuterPubA,
    aVerifyOuterPub]
  · exact ⟨rfl, rfl, by norm_num [aVerifyOuterSkel, parentRecordSkeleton, memLabelS,
      aVerifyOuterPubA, aVerifyOuterPub, parentRecordS]⟩

theorem bind_aDecomposeInner :
    BindMemoryRowA servedSeed aDecomposeInnerSkel aDecomposeInnerLabel := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_aInnerHeadHalt :
    BindMemoryRowA servedSeed aInnerHeadHaltSkel aInnerHeadHaltLabel := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem aInnerHeadHaltSkel.state) := by
      simp [aInnerHeadHaltSkel, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_aVerifyInner :
    BindMemoryRowA servedSeed aVerifyInnerSkel aVerifyInnerLabelA := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [aVerifyInnerSkel, MemoryTable.fanoutMem, memoryChildCell, memLabelS, aVerifyInnerPubA,
    aVerifyInnerPub]
  · exact ⟨rfl, rfl, by norm_num [aVerifyInnerSkel, innerRecordSkeleton, memLabelS,
      aVerifyInnerPubA, aVerifyInnerPub, servedFormulaRecord]⟩

theorem bind_aTailHalt :
    BindMemoryRowA servedSeed aTailHaltSkel aTailHaltLabel := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem aTailHaltSkel.state) := by
      simp [aTailHaltSkel, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_bRead :
    BindMemoryRowA servedSeed bReadSkel bReadLabelA := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [bReadSkel, MemoryTable.fanoutMem, memoryChildCell, memLabelS, bReadPubA, bReadPub]
  · exact ⟨rfl, rfl, by norm_num [bReadSkel, servedRecordSkeleton, memLabelS,
      bReadPubA, bReadPub, servedRecord]⟩

theorem bind_bDecompose :
    BindMemoryRowA servedSeed bDecomposeSkel bDecomposeLabel := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_bVerify :
    BindMemoryRowA servedSeed bVerifySkel bVerifyLabelA := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [bVerifySkel, MemoryTable.fanoutMem, memoryChildCell, memLabelS, bVerifyPubA, bVerifyPub]
  · exact ⟨rfl, rfl, by norm_num [bVerifySkel, servedRecordSkeleton, memLabelS,
      bVerifyPubA, bVerifyPub, servedRecord]⟩

theorem bind_bResultHalt :
    BindMemoryRowA servedSeed bResultHaltSkel bResultHaltLabel := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem bResultHaltSkel.state) := by
      simp [bResultHaltSkel, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_bTailHalt :
    BindMemoryRowA servedSeed bTailHaltSkel bTailHaltLabel := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem bTailHaltSkel.state) := by
      simp [bTailHaltSkel, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

/-! ## G. The committed exponents specialize to the fixture's own timestamp columns -/

theorem stamp_parentRow :
    ComputeTimestampSpecializesAt cfgS.challenges.α parentStamp parentRowS := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show parentPubS.ln_prev = cfgS.challenges.α ^ 0
    rw [pow_zero]; rfl
  · show parentPubS.ln = cfgS.challenges.α ^ 1
    rw [pow_one]; rfl
  · intro i
    fin_cases i
    · show parentPubS.mr1.ts = _
      rw [if_pos (by rfl)]
      show parentRecordS.ts = cfgS.challenges.α ^ 1
      rw [pow_one]; rfl
    · show parentPubS.mr2.ts = _
      rw [if_neg (by decide)]; rfl
    · show parentPubS.mr3.ts = _
      rw [if_neg (by decide)]; rfl
  · intro i hi
    fin_cases i
    · exact absurd hi
        (by simp [parentStamp, computeMemRecKind, Nock.Framework.recordCount])
    · rfl
    · rfl

theorem stamp_servedRow :
    ComputeTimestampSpecializesAt cfgS.challenges.α servedStamp servedRow := by
  refine ComputeTimestampSpecializesAt.of_absolute rfl rfl rfl ?_ ?_ ?_ ?_
    (by decide) (fun i => by fin_cases i <;> decide)
  · show servedPub.ln_prev = cfgS.challenges.α ^ 1
    rw [pow_one]; rfl
  · show servedPub.ln = cfgS.challenges.α ^ 3
    rfl
  · intro i
    fin_cases i
    · show servedPub.mr1.ts = _
      rw [if_pos (by rfl)]
      rfl
    · show servedPub.mr2.ts = _
      rw [if_pos (by rfl)]
      rfl
    · show servedPub.mr3.ts = _
      rw [if_neg (by decide)]; rfl
  · intro i hi
    fin_cases i
    · exact absurd hi
        (by simp [servedStamp, computeMemRecKind, Nock.Framework.recordCount])
    · exact absurd hi
        (by simp [servedStamp, computeMemRecKind, Nock.Framework.recordCount])
    · rfl

/-- Memory rows whose state carries no live record: the exponent is arbitrary and the record is
the exact production zero. -/
theorem stamp_padding {st : MState} (hst : memoryMemRecKind st = .padding)
    (pub : MemoryTable.Pub K97cubic) (hpub : pub.st = st)
    (hmem : pub.mem = ComputeTable.MemRec.zero) (e : ℕ) :
    MemoryTimestampSpecializesAt cfgS.challenges.α (memStamp st e) (memLabelS st pub) := by
  have hne : ¬ (memoryMemRecKind (memStamp st e).state = FPSlotKind.active) := by
    show ¬ (memoryMemRecKind st = FPSlotKind.active)
    rw [hst]; simp
  refine ⟨rfl, hpub, ?_, ?_⟩
  · show pub.mem.ts = _
    rw [if_neg hne, hmem]; rfl
  · intro _; exact hmem

theorem stamp_aReadOuter :
    MemoryTimestampSpecializesAt cfgS.challenges.α (memStamp .read_root 1) aReadOuterLabelA := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show aReadOuterPubA.mem.ts = _
    rw [if_pos (by rfl)]
    show parentRecordS.ts = cfgS.challenges.α ^ 1
    rw [pow_one]; rfl
  · intro h; exact absurd h (by decide)

theorem stamp_aReadInner :
    MemoryTimestampSpecializesAt cfgS.challenges.α (memStamp .read_root 2) aReadInnerLabelA := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show aReadInnerPubA.mem.ts = _
    rw [if_pos (by rfl)]
    rfl
  · intro h; exact absurd h (by decide)

theorem stamp_aVerifyOuter :
    MemoryTimestampSpecializesAt cfgS.challenges.α (memStamp .verify_child 1)
      aVerifyOuterLabelA := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show aVerifyOuterPubA.mem.ts = _
    rw [if_pos (by rfl)]
    show parentRecordS.ts = cfgS.challenges.α ^ 1
    rw [pow_one]; rfl
  · intro h; exact absurd h (by decide)

theorem stamp_aVerifyInner :
    MemoryTimestampSpecializesAt cfgS.challenges.α (memStamp .verify_child 2)
      aVerifyInnerLabelA := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show aVerifyInnerPubA.mem.ts = _
    rw [if_pos (by rfl)]
    rfl
  · intro h; exact absurd h (by decide)

theorem stamp_bRead :
    MemoryTimestampSpecializesAt cfgS.challenges.α (memStamp .read_root 3) bReadLabelA := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show bReadPubA.mem.ts = _
    rw [if_pos (by rfl)]
    rfl
  · intro h; exact absurd h (by decide)

theorem stamp_bVerify :
    MemoryTimestampSpecializesAt cfgS.challenges.α (memStamp .verify_child 3)
      bVerifyLabelA := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show bVerifyPubA.mem.ts = _
    rw [if_pos (by rfl)]
    rfl
  · intro h; exact absurd h (by decide)

/-! ## H. The committed node trees -/

def parentNode : ComputeNode K97cubic where
  skel := parentSkeletonRow
  stamp := parentStamp
  row := parentRowS

def servedNode : ComputeNode K97cubic where
  skel := servedSkeletonRow
  stamp := servedStamp
  row := servedRow

/-- The committed compute node tree: an `OP_4` parent with its single `OP_0` recursive call. -/
def computeNodesM : NTree (ComputeNode K97cubic) :=
  .node parentNode [.node servedNode []]

def memNode (skel : MemoryRowSkeleton) (e : ℕ) (pub : MemoryTable.Pub K97cubic) :
    MemoryNode K97cubic where
  skel := skel
  stamp := memStamp skel.state e
  row := memLabelS skel.state pub

def aTailHaltNodeTree : NTree (MemoryNode K97cubic) :=
  .node (memNode aTailHaltSkel 0 aTailHaltPub) []
def aVerifyInnerNodeTree : NTree (MemoryNode K97cubic) :=
  .node (memNode aVerifyInnerSkel 2 aVerifyInnerPubA) [aTailHaltNodeTree]
def dummyHaltNodeTree : NTree (MemoryNode K97cubic) :=
  .node (memNode dummyHaltSkel 0 dummyHaltPubS) []

def aInnerHeadHaltNodeTree : NTree (MemoryNode K97cubic) :=
  .node (memNode aInnerHeadHaltSkel 0 aInnerHeadHaltPub) []
def aDecomposeInnerNodeTree : NTree (MemoryNode K97cubic) :=
  .node (memNode aDecomposeInnerSkel 0 aDecomposeInnerPub)
    [aInnerHeadHaltNodeTree, aVerifyInnerNodeTree]
def aVerifyOuterNodeTree : NTree (MemoryNode K97cubic) :=
  .node (memNode aVerifyOuterSkel 1 aVerifyOuterPubA) [aDecomposeInnerNodeTree]
def aReadInnerNodeTree : NTree (MemoryNode K97cubic) :=
  .node (memNode aReadInnerSkel 2 aReadInnerPubA) [aVerifyOuterNodeTree]
def aHeadHaltNodeTree : NTree (MemoryNode K97cubic) :=
  .node (memNode aHeadHaltSkel 0 aHeadHaltPub) []
def aDecomposeOuterNodeTree : NTree (MemoryNode K97cubic) :=
  .node (memNode aDecomposeOuterSkel 0 aDecomposeOuterPub)
    [aHeadHaltNodeTree, aReadInnerNodeTree]
/-- Committed serviced root `A`. -/
def rootANodeTree : NTree (MemoryNode K97cubic) :=
  .node (memNode aReadOuterSkel 1 aReadOuterPubA) [aDecomposeOuterNodeTree]

def bResultHaltNodeTree : NTree (MemoryNode K97cubic) :=
  .node (memNode bResultHaltSkel 0 bResultHaltPub) []
def bVerifyNodeTree : NTree (MemoryNode K97cubic) :=
  .node (memNode bVerifySkel 3 bVerifyPubA) [bResultHaltNodeTree]
def bTailHaltNodeTree : NTree (MemoryNode K97cubic) :=
  .node (memNode bTailHaltSkel 0 bTailHaltPub) []
def bDecomposeNodeTree : NTree (MemoryNode K97cubic) :=
  .node (memNode bDecomposeSkel 0 bDecomposePub) [bVerifyNodeTree, bTailHaltNodeTree]
/-- Committed serviced root `B`. -/
def rootBNodeTree : NTree (MemoryNode K97cubic) :=
  .node (memNode bReadSkel 3 bReadPubA) [bDecomposeNodeTree]

def memoryNodesM : List (NTree (MemoryNode K97cubic)) :=
  [dummyHaltNodeTree, rootANodeTree, rootBNodeTree]

/-! ## I. Local validity of every committed node at the honest sample -/

theorem computeNodesM_OK :
    ComputeNodesOK cfgS.challenges.z cfgS.challenges.α computeNodesM := by
  refine ComputeNodesOK.mk' ⟨rfl, rfl, bind_parentRow, stamp_parentRow⟩ ?_
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact ComputeNodesOK.mk' ⟨rfl, rfl, bind_servedRow, stamp_servedRow⟩ (by simp)

theorem dummyHaltNodeTree_OK :
    MemoryNodesOK cfgS.challenges.z cfgS.challenges.α dummyHaltNodeTree := by
  exact MemoryNodesOK.mk'
    ⟨rfl, rfl, bind_dummyHalt,
      stamp_padding (st := .halt) rfl dummyHaltPubS rfl rfl 0⟩ (by simp)

theorem rootANodeTree_OK :
    MemoryNodesOK cfgS.challenges.z cfgS.challenges.α rootANodeTree := by
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_aReadOuter, stamp_aReadOuter⟩ ?_
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  refine MemoryNodesOK.mk'
    ⟨rfl, rfl, bind_aDecomposeOuter, stamp_padding (st := .decompose) rfl aDecomposeOuterPub rfl rfl 0⟩ ?_
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact MemoryNodesOK.mk'
      ⟨rfl, rfl, bind_aHeadHalt,
        stamp_padding (st := .halt) rfl aHeadHaltPub rfl rfl 0⟩ (by simp)
  · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_aReadInner, stamp_aReadInner⟩ ?_
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_aVerifyOuter, stamp_aVerifyOuter⟩ ?_
    intro f hf
    simp only [List.mem_singleton] at hf
    subst hf
    refine MemoryNodesOK.mk'
      ⟨rfl, rfl, bind_aDecomposeInner,
        stamp_padding (st := .decompose) rfl aDecomposeInnerPub rfl rfl 0⟩ ?_
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact MemoryNodesOK.mk'
        ⟨rfl, rfl, bind_aInnerHeadHalt,
          stamp_padding (st := .halt) rfl aInnerHeadHaltPub rfl rfl 0⟩ (by simp)
    · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_aVerifyInner, stamp_aVerifyInner⟩ ?_
      intro k hk
      simp only [List.mem_singleton] at hk
      subst hk
      exact MemoryNodesOK.mk'
        ⟨rfl, rfl, bind_aTailHalt,
          stamp_padding (st := .halt) rfl aTailHaltPub rfl rfl 0⟩ (by simp)

theorem rootBNodeTree_OK :
    MemoryNodesOK cfgS.challenges.z cfgS.challenges.α rootBNodeTree := by
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_bRead, stamp_bRead⟩ ?_
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  refine MemoryNodesOK.mk'
    ⟨rfl, rfl, bind_bDecompose,
      stamp_padding (st := .decompose) rfl bDecomposePub rfl rfl 0⟩ ?_
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_bVerify, stamp_bVerify⟩ ?_
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact MemoryNodesOK.mk'
      ⟨rfl, rfl, bind_bResultHalt,
        stamp_padding (st := .halt) rfl bResultHaltPub rfl rfl 0⟩ (by simp)
  · exact MemoryNodesOK.mk'
      ⟨rfl, rfl, bind_bTailHalt,
        stamp_padding (st := .halt) rfl bTailHaltPub rfl rfl 0⟩ (by simp)

/-! ## J. The committed skeleton and its canonical BFS rows -/

/-- The committed semantic skeleton of the two-serviced-root fixture. -/
def skelM : SemanticSkeleton := skeletonOfNodes computeNodesM memoryNodesM

theorem computeSkeletonRowsM :
    computeSkeletonRows skelM = [parentSkeletonRow, servedSkeletonRow] := by
  norm_num [computeSkeletonRows, skelM, skeletonOfNodes, computeNodesM, mapNTree,
    parentNode, servedNode, bfsForest, NTree.size, totalSize]

theorem memorySkeletonRowsM :
    memorySkeletonRows skelM =
      [dummyHaltSkel, aReadOuterSkel, bReadSkel, aDecomposeOuterSkel, bDecomposeSkel,
        aHeadHaltSkel, aReadInnerSkel, bVerifySkel, bTailHaltSkel,
        aVerifyOuterSkel, bResultHaltSkel, aDecomposeInnerSkel, aInnerHeadHaltSkel,
        aVerifyInnerSkel, aTailHaltSkel] := by
  norm_num [memorySkeletonRows, skelM, skeletonOfNodes, memoryNodesM, mapNTree,
    dummyHaltNodeTree, rootANodeTree, aDecomposeOuterNodeTree, aHeadHaltNodeTree, aReadInnerNodeTree,
    aVerifyOuterNodeTree, aDecomposeInnerNodeTree, aInnerHeadHaltNodeTree,
    aVerifyInnerNodeTree, aTailHaltNodeTree, rootBNodeTree, bDecomposeNodeTree,
    bVerifyNodeTree, bResultHaltNodeTree, bTailHaltNodeTree, memNode,
    bfsForest, NTree.size, totalSize]

/-! ## K. The six skeleton-only semantic obligations -/

/-- **The `OP_0` slot fact is genuine here**: the committed `mr2` axis is `2` and
`/(2, subjectS) = resultS`.  At F73 this obligation was vacuous. -/
theorem slotSemanticsM :
    ∀ s ∈ computeSkeletonRows skelM, ServedLookupBridge.SkeletonSlotSemantics s := by
  intro s hs
  rw [computeSkeletonRowsM] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact
      { s0_slot := fun h => absurd h (by simp [parentSkeletonRow])
        s9_slot := fun h => absurd h (by simp [parentSkeletonRow]) }
  · refine
      { s0_slot := fun _ => ?_
        s9_slot := fun h => absurd h (by simp [servedSkeletonRow]) }
    show Noun.slot (P8Census.skeletonMemoryAxis servedSkeletonRow 1) subjectS = some resultS
    rw [show P8Census.skeletonMemoryAxis servedSkeletonRow 1 = 2 from rfl]
    exact slot_subjectS

/-- **The `OP_0` record equations are genuine here**. -/
theorem recordEquationsM :
    ∀ s ∈ computeSkeletonRows skelM, ServedLookupBridge.SkeletonRecordEquations s := by
  intro s hs
  rw [computeSkeletonRowsM] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact
      { s0_record := fun h => absurd h (by simp [parentSkeletonRow])
        s9_record := fun h => absurd h (by simp [parentSkeletonRow]) }
  · exact
      { s0_record := fun _ => ⟨rfl, rfl⟩
        s9_record := fun h => absurd h (by simp [servedSkeletonRow]) }

theorem incMod_resultS_leaves :
    (OpcodeSemantics.incMod (ringChar K97cubic) resultS).leaves = 1 := by
  rw [incMod_resultS]
  rfl

theorem sizeWindowBoundM :
    SizeWindowCounting.SizeWindowNounsBoundedBy skelM 3 := by
  intro n hn
  rw [SizeWindowCounting.skeletonSizeWindowNouns, computeSkeletonRowsM] at hn
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hn
  have hp : SizeWindowCounting.requiredSizeWindowNouns parentSkeletonRow = [resultS] := rfl
  have hs : SizeWindowCounting.requiredSizeWindowNouns servedSkeletonRow = [] := rfl
  rw [hp, hs] at hn
  simp only [List.mem_singleton, List.not_mem_nil, or_false] at hn
  subst hn
  decide

theorem parentSkeletonRow_bounded : parentSkeletonRow.BoundedBy 97 := by
  refine ⟨by simp [parentSkeletonRow, subjectS, resultS, FieldEmbedding.BoundedBy], ?_, ?_,
    ?_, ?_, ?_⟩
  · simp [parentSkeletonRow, parentFormulaS, parentHeadS, formulaS, headS, tailS,
      FieldEmbedding.BoundedBy]
  · simp [parentSkeletonRow, parentResultS, FieldEmbedding.BoundedBy]
  · intro slot h
    cases slot <;>
      simp [parentSkeletonRow, parentHeadS, formulaS, headS, tailS, FieldEmbedding.BoundedBy]
  · intro i h slot
    cases slot <;>
      simp [parentSkeletonRow, subjectS, formulaS, headS, tailS, resultS,
        FieldEmbedding.BoundedBy]
  · intro i h
    exact ⟨by simp [parentSkeletonRow, parentRecordSkeleton, parentFormulaS, parentHeadS,
        formulaS, headS, tailS, FieldEmbedding.BoundedBy],
      by simp [parentSkeletonRow, parentRecordSkeleton, formulaS, headS, tailS,
        FieldEmbedding.BoundedBy]⟩

theorem servedSkeletonRow_bounded : servedSkeletonRow.BoundedBy 97 := by
  refine ⟨by simp [servedSkeletonRow, subjectS, resultS, FieldEmbedding.BoundedBy], ?_, ?_,
    ?_, ?_, ?_⟩
  · simp [servedSkeletonRow, formulaS, headS, tailS, FieldEmbedding.BoundedBy]
  · simp [servedSkeletonRow, resultS, FieldEmbedding.BoundedBy]
  · intro slot h
    cases slot <;>
      simp [servedSkeletonRow, headS, tailS, FieldEmbedding.BoundedBy]
  · intro i h
    simp [servedSkeletonRow, ComputeTable.fanoutComp] at h
  · intro i h
    fin_cases i <;> refine ⟨?_, ?_⟩ <;>
      simp [servedSkeletonRow, innerRecordSkeleton, servedRecordSkeleton,
        formulaS, headS, tailS, subjectS, resultS, FieldEmbedding.BoundedBy]

theorem memorySkeletonRowsM_bounded :
    ∀ s ∈ memorySkeletonRows skelM, s.BoundedBy 97 := by
  intro s hs
  rw [memorySkeletonRowsM] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by simp [dummyHaltSkel, FieldEmbedding.BoundedBy],
      (fun i h => nomatch h), fun h => nomatch h⟩
  · exact ⟨by simp [aReadOuterSkel, parentFormulaS, parentHeadS, formulaS, headS, tailS,
      FieldEmbedding.BoundedBy],
      fun i h => by simp [aReadOuterSkel, parentFormulaS, parentHeadS, formulaS, headS, tailS,
        FieldEmbedding.BoundedBy],
      fun h => ⟨by simp [aReadOuterSkel, parentRecordSkeleton, parentFormulaS, parentHeadS,
          formulaS, headS, tailS, FieldEmbedding.BoundedBy],
        by simp [aReadOuterSkel, parentRecordSkeleton, formulaS, headS, tailS,
          FieldEmbedding.BoundedBy]⟩⟩
  · exact ⟨by simp [bReadSkel, subjectS, FieldEmbedding.BoundedBy],
      fun i h => by simp [bReadSkel, subjectS, FieldEmbedding.BoundedBy],
      fun h => ⟨by simp [bReadSkel, servedRecordSkeleton, subjectS, FieldEmbedding.BoundedBy],
        by simp [bReadSkel, servedRecordSkeleton, resultS, FieldEmbedding.BoundedBy]⟩⟩
  · refine ⟨by simp [aDecomposeOuterSkel, parentFormulaS, parentHeadS, formulaS, headS, tailS,
      FieldEmbedding.BoundedBy], ?_, fun h => nomatch h⟩
    intro i h
    fin_cases i <;>
      simp [aDecomposeOuterSkel, parentHeadS, formulaS, headS, tailS,
        FieldEmbedding.BoundedBy]
  · refine ⟨by simp [bDecomposeSkel, subjectS, FieldEmbedding.BoundedBy], ?_,
      fun h => nomatch h⟩
    intro i h
    fin_cases i <;>
      simp [bDecomposeSkel, resultS, bTailNoun, FieldEmbedding.BoundedBy]
  · exact ⟨by simp [aHeadHaltSkel, parentHeadS, FieldEmbedding.BoundedBy],
      (fun i h => nomatch h), fun h => nomatch h⟩
  · exact ⟨by simp [aReadInnerSkel, formulaS, headS, tailS, FieldEmbedding.BoundedBy],
      fun i h => by simp [aReadInnerSkel, formulaS, headS, tailS, FieldEmbedding.BoundedBy],
      fun h => ⟨by simp [aReadInnerSkel, innerRecordSkeleton, formulaS, headS, tailS,
          FieldEmbedding.BoundedBy],
        by simp [aReadInnerSkel, innerRecordSkeleton, tailS, FieldEmbedding.BoundedBy]⟩⟩
  · exact ⟨by simp [bVerifySkel, resultS, FieldEmbedding.BoundedBy],
      fun i h => by simp [bVerifySkel, resultS, FieldEmbedding.BoundedBy],
      fun h => ⟨by simp [bVerifySkel, servedRecordSkeleton, subjectS, FieldEmbedding.BoundedBy],
        by simp [bVerifySkel, servedRecordSkeleton, resultS, FieldEmbedding.BoundedBy]⟩⟩
  · exact ⟨by simp [bTailHaltSkel, bTailNoun, FieldEmbedding.BoundedBy],
      (fun i h => nomatch h), fun h => nomatch h⟩
  · exact ⟨by simp [aVerifyOuterSkel, formulaS, headS, tailS, FieldEmbedding.BoundedBy],
      fun i h => by simp [aVerifyOuterSkel, formulaS, headS, tailS, FieldEmbedding.BoundedBy],
      fun h => ⟨by simp [aVerifyOuterSkel, parentRecordSkeleton, parentFormulaS, parentHeadS,
          formulaS, headS, tailS, FieldEmbedding.BoundedBy],
        by simp [aVerifyOuterSkel, parentRecordSkeleton, formulaS, headS, tailS,
          FieldEmbedding.BoundedBy]⟩⟩
  · exact ⟨by simp [bResultHaltSkel, resultS, FieldEmbedding.BoundedBy],
      (fun i h => nomatch h), fun h => nomatch h⟩
  · refine ⟨by simp [aDecomposeInnerSkel, formulaS, headS, tailS, FieldEmbedding.BoundedBy],
      ?_, fun h => nomatch h⟩
    intro i h
    fin_cases i <;>
      simp [aDecomposeInnerSkel, headS, tailS, FieldEmbedding.BoundedBy]
  · exact ⟨by simp [aInnerHeadHaltSkel, headS, FieldEmbedding.BoundedBy],
      (fun i h => nomatch h), fun h => nomatch h⟩
  · exact ⟨by simp [aVerifyInnerSkel, tailS, FieldEmbedding.BoundedBy],
      fun i h => by simp [aVerifyInnerSkel, tailS, FieldEmbedding.BoundedBy],
      fun h => ⟨by simp [aVerifyInnerSkel, innerRecordSkeleton, formulaS, headS, tailS,
          FieldEmbedding.BoundedBy],
        by simp [aVerifyInnerSkel, innerRecordSkeleton, tailS, FieldEmbedding.BoundedBy]⟩⟩
  · exact ⟨by simp [aTailHaltSkel, tailS, FieldEmbedding.BoundedBy],
      (fun i h => nomatch h), fun h => nomatch h⟩

theorem skeletonBoundedM : skelM.BoundedBy 97 := by
  refine { computeRows := ?_, memoryRows := ?_, memoryTrees := ?_ }
  · rw [computeSkeletonRowsM]
    exact ⟨parentSkeletonRow_bounded, servedSkeletonRow_bounded⟩
  · rw [List.forall_iff_forall_mem]
    exact memorySkeletonRowsM_bounded
  · intro tree htree node hnode
    have hm : node ∈ bfsForest skelM.memoryForest :=
      (mem_bfsForest skelM.memoryForest node).2 ⟨tree, htree, hnode⟩
    have hlbl : node.label ∈ memorySkeletonRows skelM :=
      List.mem_map_of_mem hm
    exact memorySkeletonRowsM_bounded _ hlbl

/-! ## L. The pre-seed comparison census -/

theorem skeletonComparisonCensusM :
    P8Census.skeletonComparisonCensus (K := K97cubic) skelM =
      P8Census.skeletonComparisons (K := K97cubic) parentSkeletonRow ++
        P8Census.skeletonComparisons (K := K97cubic) servedSkeletonRow := by
  rw [P8Census.skeletonComparisonCensus, computeSkeletonRowsM]
  simp

theorem incMod_atom7_leaves :
    (OpcodeSemantics.incMod (ringChar K97cubic) (Noun.atom 7)).leaves ≤ 3 := by
  have h : OpcodeSemantics.incMod (ringChar K97cubic) (Noun.atom 7) = parentResultS :=
    incMod_resultS
  rw [h]
  decide

def censusM : EdgeComparisonCensus.CombinedSkeletonCensus K97cubic skelM 3 where
  p8 :=
    { leaves_bounded := by
        intro pair hp
        rw [BoundSemanticTrace.skeletonPairs, skeletonComparisonCensusM] at hp
        simp [P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
          P8Census.skeletonSubformula, P8Census.skeletonMemoryAxis,
          SemanticTrace.ComparisonUse.pair, skelM, skeletonOfNodes, computeNodesM,
          mapNTree, parentNode, parentSkeletonRow, servedSkeletonRow,
          SemanticSkeleton.publicClaim, decActive, hasTailDecomposition,
          servedRecordSkeleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [subjectS, parentFormulaS, parentResultS, parentHeadS, formulaS, headS,
            tailS, resultS, ComputeTable.fanoutComp, Nock.Framework.recordCount,
            incMod_atom7_leaves, Noun.leaves] }
  edges :=
    { leaves_bounded := by
        intro pair hp
        rw [EdgeComparisonCensus.edgePairs] at hp
        simp [skelM, skeletonOfNodes, computeNodesM, mapNTree, parentNode, servedNode,
          bfsForest, NTree.size, totalSize, EdgeComparisonCensus.rowEdgePairs,
          EdgeComparisonCensus.edgeTriple, NTree.childOpt,
          P8Census.skeletonSubformula, parentSkeletonRow, servedSkeletonRow,
          ComputeTable.fanoutComp] at hp
        rcases hp with rfl | rfl | rfl <;>
          simp [subjectS, formulaS, headS, tailS, resultS, Noun.leaves] }

theorem incMod_atom7_bounded :
    FieldEmbedding.BoundedBy 97 (OpcodeSemantics.incMod (ringChar K97cubic) (Noun.atom 7)) := by
  have h : OpcodeSemantics.incMod (ringChar K97cubic) (Noun.atom 7) = parentResultS :=
    incMod_resultS
  rw [h]
  simp [parentResultS, FieldEmbedding.BoundedBy]

theorem combinedBoundedM :
    ProductionP8Containment.CombinedBoundedBy K97cubic 97 skelM := by
  intro pair hp
  rw [EdgeComparisonCensus.combinedSkeletonPairs, List.mem_append] at hp
  rcases hp with hp | hp
  · rw [BoundSemanticTrace.skeletonPairs, skeletonComparisonCensusM] at hp
    simp [P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
      P8Census.skeletonSubformula, P8Census.skeletonMemoryAxis,
      SemanticTrace.ComparisonUse.pair, skelM, skeletonOfNodes, computeNodesM,
      mapNTree, parentNode, parentSkeletonRow, servedSkeletonRow,
      SemanticSkeleton.publicClaim, decActive, hasTailDecomposition,
      servedRecordSkeleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [subjectS, parentFormulaS, parentResultS, parentHeadS, formulaS, headS,
        tailS, resultS, ComputeTable.fanoutComp, Nock.Framework.recordCount,
        incMod_atom7_bounded, FieldEmbedding.BoundedBy]
  · rw [EdgeComparisonCensus.edgePairs] at hp
    simp [skelM, skeletonOfNodes, computeNodesM, mapNTree, parentNode, servedNode,
      bfsForest, NTree.size, totalSize, EdgeComparisonCensus.rowEdgePairs,
      EdgeComparisonCensus.edgeTriple, NTree.childOpt,
      P8Census.skeletonSubformula, parentSkeletonRow, servedSkeletonRow,
      ComputeTable.fanoutComp] at hp
    rcases hp with rfl | rfl | rfl <;>
      simp [subjectS, formulaS, headS, tailS, resultS, FieldEmbedding.BoundedBy]

/-! ## M. The honest commitment of the two-serviced-root fixture -/

/-- **`HonestCommitment.Data` at a semantically distinct, nonterminal execution.**  The committed
node trees are the fourteen memory rows in two serviced roots and the two nonterminal compute rows;
their honest-seed bindings are at `(z, α) = (servedSeed, 4)`. -/
def dataM : HonestCommitment.Data multiRootExecution where
  computeNodes := computeNodesM
  memoryNodes := memoryNodesM
  compute_rows := by
    show mapNTree ComputeNode.row computeNodesM = computeTreeS
    simp [computeNodesM, parentNode, servedNode, mapNTree, computeTreeS]
  memory_rows := by
    show memoryNodesM.map (mapNTree MemoryNode.row) = [dummyHaltTreeS, rootATreeA, rootBTreeA]
    simp [memoryNodesM, dummyHaltNodeTree, rootANodeTree, aDecomposeOuterNodeTree, aHeadHaltNodeTree,
      aReadInnerNodeTree, aVerifyOuterNodeTree, aDecomposeInnerNodeTree,
      aInnerHeadHaltNodeTree, aVerifyInnerNodeTree, aTailHaltNodeTree,
      rootBNodeTree, bDecomposeNodeTree, bVerifyNodeTree, bResultHaltNodeTree,
      bTailHaltNodeTree, memNode, mapNTree, dummyHaltTreeS, dummyHaltPubS, dummyHaltLabelS,
      rootATreeA, aDecomposeOuterTreeA,
      aHeadHaltTree, aReadInnerTreeA, aVerifyOuterTreeA, aDecomposeInnerTreeA,
      aInnerHeadHaltTree, aVerifyInnerTreeA, aTailHaltTree, rootBTreeA,
      bDecomposeTreeA, bVerifyTreeA, bResultHaltTree, bTailHaltTree]
    exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, rfl⟩
  computeOK := computeNodesM_OK
  memoryOK := by
    intro t ht
    simp only [memoryNodesM, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact dummyHaltNodeTree_OK
    · exact rootANodeTree_OK
    · exact rootBNodeTree_OK
  root_line_exponent := rfl
  root_line_origin := rfl
  nounSizeBound := 3
  Λ := 3
  slotSemantics := slotSemanticsM
  recordEquations := recordEquationsM
  census := censusM
  sizeWindowBound := sizeWindowBoundM
  q_eq_ringChar := ringChar_K97.symm
  skeletonBounded := skeletonBoundedM
  combinedBounded := combinedBoundedM

theorem dataM_skeleton : dataM.skeleton = skelM := by rfl

/-- The committed skeleton really is the two-row / fourteen-row shape, and the served `OP_0` row
is committed with its `mr2` axis `2` slot lookup. -/
theorem dataM_shape :
    computeSkeletonRows dataM.skeleton = [parentSkeletonRow, servedSkeletonRow] ∧
      (memorySkeletonRows dataM.skeleton).length = 15 ∧
      servedSkeletonRow.state = ComputeTable.State.s0 ∧
      P8Census.skeletonMemoryAxis servedSkeletonRow 1 = 2 ∧
      Noun.slot (P8Census.skeletonMemoryAxis servedSkeletonRow 1)
        servedSkeletonRow.subject = some servedSkeletonRow.evaluation := by
  refine ⟨computeSkeletonRowsM, ?_, rfl, rfl, ?_⟩
  · rw [dataM_skeleton, memorySkeletonRowsM]; rfl
  · rw [show P8Census.skeletonMemoryAxis servedSkeletonRow 1 = 2 from rfl]
    exact slot_subjectS

/-! ## N. The committed residual, the constructed package, and the released statement -/

/-- Its
committed template is generated by the `HonestCommitment` renderer at every sampled seed, and the
post-challenge arrays are the all-zero later-round message: they inhabit the constructor and claim
**no** acceptance. -/
def residualM : BuildablePackage.CommitmentResidual multiRootExecution :=
  HonestCommitment.commitmentResidualOfZero dataM

theorem residualM_nonvacuous :
    Nonempty (BuildablePackage.CommitmentResidual multiRootExecution) :=
  ⟨residualM⟩


theorem mr_leafIs : GeneratedField.LeafIs (K := K97cubic) 2 (.cell (.atom 7) (.atom 9)) (.cell (.atom 4) (.cell (.atom 0) (.atom 2))) 3 := by
  gen_simp

theorem mr_evalIsSome : (FieldEmbedding.evalGBy (ringChar K97cubic) 2 (.cell (.atom 7) (.atom 9)) (.cell (.atom 4) (.cell (.atom 0) (.atom 2)))).isSome := by
  have h97 := MultiRootServedFixture.ringChar_K97
  simp [h97, FieldEmbedding.evalGBy, FieldEmbedding.lusGBy, Noun.slot]

/-- Program-level `generated` at any window `Λ ≥ 3`. -/
theorem mr_program_generated (Λ : ℕ) (hΛ : 3 ≤ Λ) :
    ∃ (gfuel : ℕ) (G : Nock.Walk.NTree (TraceGen.GenComputeRow K97cubic)) (R : Noun) (fuel : ℕ)
      (r : Noun),
      TraceGen.genComputeSkeleton (K := K97cubic) gfuel (.cell (.atom 7) (.atom 9)) (.cell (.atom 4) (.cell (.atom 0) (.atom 2))) = .ok (G, R) ∧
        FieldEmbedding.evalGBy (ringChar K97cubic) fuel (.cell (.atom 7) (.atom 9)) (.cell (.atom 4) (.cell (.atom 0) (.atom 2))) = some r ∧
        TraceGen.programLeafBound (TraceGen.airReorder G) ≤ Λ :=
  GeneratedField.generated_of _ _ _ _ 2 2 (GeneratedField.le_of_leafIs mr_leafIs hΛ)
    mr_evalIsSome

/-- Negative control: zero margin (`Λ = 2` is refuted). -/
theorem mr_leaf_margin_zero :
    ¬ ∃ (G : Nock.Walk.NTree (TraceGen.GenComputeRow K97cubic)) (R : Noun),
      TraceGen.genComputeSkeleton (K := K97cubic) 2 (.cell (.atom 7) (.atom 9)) (.cell (.atom 4) (.cell (.atom 0) (.atom 2))) = .ok (G, R) ∧
        TraceGen.programLeafBound (TraceGen.airReorder G) ≤ 2 := by
  rintro ⟨G, R, hx, hle⟩
  have h := mr_leafIs
  unfold GeneratedField.LeafIs at h
  rw [hx] at h
  simp only at h
  omega

theorem residualM_claim :
    (residualM).verifier.raw.claim.subject = (.cell (.atom 7) (.atom 9)) ∧
      (residualM).verifier.raw.claim.formula = (.cell (.atom 4) (.cell (.atom 0) (.atom 2))) := by
  show (dataM).skeleton.computeTree.label.subject = (.cell (.atom 7) (.atom 9)) ∧
    (dataM).skeleton.computeTree.label.formula = (.cell (.atom 4) (.cell (.atom 0) (.atom 2)))
  simp [HonestCommitment.Data.skeleton, HonestCommitment.skeletonOfNodes, mapNTree_label]
  all_goals (try refine ⟨?_, ?_⟩)
  all_goals first | rfl | decide

/-- `generated` at `residualM` (window `3`). -/
theorem residualM_generated :
    GeneratedField.ClaimGenerated K97cubic (residualM).verifier.raw.claim (residualM).Λ :=
  GeneratedField.claimGenerated_of_eq (residualM_claim).1 (residualM_claim).2
    (mr_program_generated _ (le_of_eq rfl))

theorem residualOf_claim
    (A : ∀ (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic),
      TemplateRawJointSoundness.AlphaMCommitment (p := ringChar K97cubic)
        dataM.timestampStrategy z hz α lmb)
    (W : ∀ (ω : JointCoins K97cubic) (_lmb : K97cubic), nprSeed ω ≠ 0 → RawWalkArrays K97cubic) :
    (HonestCommitment.commitmentResidualOf dataM A W).verifier.raw.claim.subject = (.cell (.atom 7) (.atom 9)) ∧
      (HonestCommitment.commitmentResidualOf dataM A W).verifier.raw.claim.formula = (.cell (.atom 4) (.cell (.atom 0) (.atom 2))) :=
  residualM_claim

/-- `generated` at `commitmentResidualOf dataM A W` (the arrays do not touch the claim). -/
theorem residualOf_generated
    (A : ∀ (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic),
      TemplateRawJointSoundness.AlphaMCommitment (p := ringChar K97cubic)
        dataM.timestampStrategy z hz α lmb)
    (W : ∀ (ω : JointCoins K97cubic) (_lmb : K97cubic), nprSeed ω ≠ 0 → RawWalkArrays K97cubic) :
    GeneratedField.ClaimGenerated K97cubic
      (HonestCommitment.commitmentResidualOf dataM A W).verifier.raw.claim
      (HonestCommitment.commitmentResidualOf dataM A W).Λ :=
  residualM_generated

/-- `primeField` at `F97 = ZMod 97`. -/
theorem f97_primeField : GeneratedField.PrimeFieldElems F97 := by
  haveI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  exact GeneratedField.primeFieldElems_zmod 97

/-- The constructed package over the two-serviced-root nonterminal execution. -/
def packageM (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution) :
    OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F97 K97cubic 4 :=
  BuildablePackage.buildFullPackage multiRootExecution inputsM residualM inputsM_challenges
    pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM residualM_generated f97_primeField

/-- **The released fourteen-conjunct Theorem-5.4 statement over a semantically distinct,
nonterminal, two-serviced-root execution.**  The consumed capstone
`optimizedFullStrictNockVMROM_of_package` is unchanged. -/
theorem statementM
    (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)
    (hax : FormRAxisBound (packageM hmoreM).optimized.sampled (packageM hmoreM).optimized.basis)
    (hbasis : FormRBasis (packageM hmoreM).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageM hmoreM) :=
  BuildablePackage.universalOptimizedFullStrictThm54 multiRootExecution inputsM residualM
    inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
    residualM_generated f97_primeField hax hbasis hwidth

theorem statementM_nonvacuous
    (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)
    (hax : FormRAxisBound (packageM hmoreM).optimized.sampled (packageM hmoreM).optimized.basis)
    (hbasis : FormRBasis (packageM hmoreM).optimized.basis)
    (hwidth : FormRWidth F97) :
    Nonempty (OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageM hmoreM)) :=
  ⟨statementM hmoreM hax hbasis hwidth⟩

theorem regressionM
    (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)
    (hax : FormRAxisBound (packageM hmoreM).optimized.sampled (packageM hmoreM).optimized.basis)
    (hbasis : FormRBasis (packageM hmoreM).optimized.basis)
    (hwidth : FormRWidth F97) :
    (packageM hmoreM).objects.cfg = cfgS ∧
      (packageM hmoreM).objects.exec = execS ∧
      (packageM hmoreM).computeChip.rap.w = 303 ∧ (packageM hmoreM).computeChip.rap.s = 418 ∧
      (packageM hmoreM).memoryChip.rap.w = 205 ∧ (packageM hmoreM).memoryChip.rap.s = 156 ∧
      (packageM hmoreM).computeChip.rap.H.card = 2 ∧
      (∀ (ω : JointCoins K97cubic) (lmb : K97cubic), (packageM hmoreM).strategy.Accepts ω lmb →
        ω ∉ ProductionP8Containment.FailureUnion (packageM hmoreM).strategy residualM.census lmb →
        ProductionP8Containment.GenuineTargetAt (packageM hmoreM).strategy 97 3 ω lmb) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (BuildablePackage.constructed_resources multiRootExecution inputsM residualM
      inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualM_generated f97_primeField).1
  · exact (BuildablePackage.constructed_resources multiRootExecution inputsM residualM
      inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualM_generated f97_primeField).2.1
  · exact (BuildablePackage.constructed_resources multiRootExecution inputsM residualM
      inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualM_generated f97_primeField).2.2.1
  · exact (BuildablePackage.constructed_resources multiRootExecution inputsM residualM
      inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualM_generated f97_primeField).2.2.2
  · exact (BuildablePackage.constructed_row_budgets multiRootExecution inputsM residualM
      inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualM_generated f97_primeField).1
  · exact BuildablePackage.universalContainment multiRootExecution inputsM residualM
      inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      residualM_generated f97_primeField hax hbasis hwidth

/-! ## O. The post-challenge arrays, stated without flattery

`residualM` is instantiated with `HonestCommitment.commitmentResidualOfZero`, i.e. with the
**all-zero** later-round message.  The two theorems below
say precisely that, and no more. -/

/-- Compiled receipt of the weakness: the later-round arrays of `residualM` really are the all-zero
post-`alphaM` commitment and the all-zero walk arrays. -/
theorem residualM_arrays_are_zero :
    residualM =
      HonestCommitment.commitmentResidualOf dataM
        (fun z hz α lmb => HonestCommitment.zeroAlphaM dataM.timestampStrategy z hz α lmb)
        (fun _ _ _ => HonestCommitment.zeroWalk) :=
  rfl

/-- **The arrays are the only remaining freedom.**  For *every* choice of post-challenge table/IO
and walk arrays over this committed data the released fourteen-conjunct statement holds of the
constructed package, so an honest accepting choice would make the containment conjunct informative
without touching anything else in the construction. -/
theorem statementM_of_arrays
    (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)
    (A : ∀ (z : K97cubic) (hz : z ≠ 0) (α lmb : K97cubic),
      TemplateRawJointSoundness.AlphaMCommitment (p := ringChar K97cubic)
        dataM.timestampStrategy z hz α lmb)
    (W : ∀ (ω : JointCoins K97cubic) (_lmb : K97cubic), nprSeed ω ≠ 0 → RawWalkArrays K97cubic)
    (hax : FormRAxisBound
      (BuildablePackage.buildFullPackage multiRootExecution inputsM
        (HonestCommitment.commitmentResidualOf dataM A W) inputsM_challenges
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      (residualOf_generated A W) f97_primeField).optimized.sampled
      (BuildablePackage.buildFullPackage multiRootExecution inputsM
        (HonestCommitment.commitmentResidualOf dataM A W) inputsM_challenges
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      (residualOf_generated A W) f97_primeField).optimized.basis)
    (hbasis : FormRBasis
      (BuildablePackage.buildFullPackage multiRootExecution inputsM
        (HonestCommitment.commitmentResidualOf dataM A W) inputsM_challenges
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      (residualOf_generated A W) f97_primeField).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
      (BuildablePackage.buildFullPackage multiRootExecution inputsM
        (HonestCommitment.commitmentResidualOf dataM A W) inputsM_challenges
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
        (residualOf_generated A W) f97_primeField) :=
  BuildablePackage.universalOptimizedFullStrictThm54 multiRootExecution inputsM
    (HonestCommitment.commitmentResidualOf dataM A W) inputsM_challenges
    pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
    (residualOf_generated A W) f97_primeField hax hbasis hwidth

/-- The two inhabitants of `CommitmentResidual` are over **semantically distinct** executions: this
one has two nonterminal compute rows and fourteen memory rows in two serviced roots, the F73 one has
a single terminal `OP_1` row and five memory rows in one root. -/
theorem residualM_distinct_from_f73 :
    multiRootExecution.cfg.compRows = 2 ∧ multiRootExecution.cfg.memRows = 15 ∧
      multiRootExecution.cfg.kMem = 3 ∧
      SemanticTrace.requiredServedLookups
        (execS.computeRowAt ⟨1, by norm_num [cfgS]⟩).1 = 1 :=
  ⟨rfl, rfl, rfl, by rw [computeRowAtS_one]; rfl⟩

end

end Nock.NockVMROM.Thm54.MultiRootHonestCommitment

#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.bind_parentRow
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.bind_servedRow
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.stamp_parentRow
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.stamp_servedRow
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.stamp_padding
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.computeNodesM_OK
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.rootANodeTree_OK
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.rootBNodeTree_OK
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.computeSkeletonRowsM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.memorySkeletonRowsM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.slotSemanticsM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.recordEquationsM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.sizeWindowBoundM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.skeletonBoundedM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.censusM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.combinedBoundedM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.dataM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.dataM_skeleton
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.dataM_shape
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.residualM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.residualM_nonvacuous
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.packageM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.statementM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.statementM_nonvacuous
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.regressionM
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.residualM_arrays_are_zero
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.statementM_of_arrays
#print axioms Nock.NockVMROM.Thm54.MultiRootHonestCommitment.residualM_distinct_from_f73
