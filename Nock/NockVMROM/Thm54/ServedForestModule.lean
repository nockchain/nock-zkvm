import Nock.NockVMROM.Thm54.ServedForestParams

/-!
# `ServedForestModule` — the generic root-`A` parent seam of the served-memory forest

Root `A` is the only part of the fourteen-row forest that reads the parent head/formula
(`encS parentFormulaS`, `encS parentHeadS`); root `B` and the inner shared-child rows are
opcode-invariant and are reused verbatim from `MultiRootServedFixture`.

## What lands here (all additive, kernel-clean)

Generic over `P : ServedForestParams`:

* the three parent-rooted cells `aRootCellG`/`aLiftCellG`/`aHeadCellG` and the parent memory record
  `parentRecordG`;
* the head-independent **pole** (`pole_parentRecordG = -1`, from `parentFormula_leaves P = 3` and the
  `γ = 0` collapse of `recRLC`) and **timestamp** (`ts_parentRecordG = 4`);
* the three parent-touching `Vmem` acceptances — `aReadOuter_acceptsG` (the two `rfl`s close for any
  noun; timestamp + pole are opcode-invariant), `aDecomposeOuter_acceptsG` (the sole noun step is
  `enc_cons`, gated only on `servedSeed ≠ 0`), and `aHeadHalt_acceptsG` (`enc_atom`, generic in the
  atom).

## Regression evidence (both instantiations discharge)

`op4Params` reproduces the concrete `MultiRootServedFixture` objects **definitionally** (the
`_eq_op4` lemmas are `rfl`), so `op0Statement` is untouched and axiom-safe; `op3Params` discharges
the *same generic proofs* with no new obligation — the direct proof-level confirmation of the
report's (A)/(B) classification for the parent seam.

## Scope note

This lands the generic **parent seam** (the crux (B) surface). It does not yet re-express the full
`multiRootExecution`/`dataM` chain as an instantiation (the remaining §7 mechanical port of the
opcode-invariant (A) blocks).
-/

namespace Nock.NockVMROM.Thm54.ServedForestModule

open scoped Classical
open Nock Nock.Noun Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.ServedForest

noncomputable section

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (P : ServedForestParams)

/-! ## A. The three parent-rooted cells and the parent memory record (generic) -/

/-- Generic root-`A` head cell, rooted at the parent head. -/
def aHeadCellG : Cell K97cubic := ⟨encS P.parentHead, 0, 0⟩

def aLiftCellG : Cell K97cubic := rowDecCell (encS P.parentFormula) (aHeadCellG P) aInnerRootCell

/-- Generic parent memory record: root the parent formula, child the shared `formulaS`, axis `3`,
timestamp `α`. -/
def parentRecordG : MemRec K97cubic where
  root := encS P.parentFormula
  child := encS formulaS
  axis := 3
  ts := fixtureAlpha

def aRootCellG : Cell K97cubic := rowReadCell (encS P.parentFormula) (aLiftCellG P)
    (parentRecordG P)

/-! ## B. Head-independent pole and timestamp -/

theorem ts_parentRecordG : (parentRecordG P).ts = 4 := by
  norm_num [parentRecordG, fixtureAlpha]

/-- **The pole is head-independent.** With `γ = β = 0` the record RLC collapses to the root size
`servedSeed ^ parentFormula.leaves`, and `parentFormula.leaves = 3` for any head atom, so the pole is
`(-1) ^ 3 = -1`. -/
theorem pole_parentRecordG : pole memInputsS (parentRecordG P) 1 = -1 := by
  have hl := parentFormula_leaves P
  simp only [pole, recRLC, memInputsS, parentRecordG, encS,
    GlobalCarryRecognizer.enc_size, hl]
  norm_num [servedSeed]

theorem pole_parentRecordG_ne : pole memInputsS (parentRecordG P) 1 ≠ 0 := by
  rw [pole_parentRecordG]
  exact neg_ne_zero.mpr one_ne_zero

/-! ## C. The three parent-rooted memory pubs (generic) -/

def aReadOuterPubG : MemoryTable.Pub K97cubic where
  st := .read_root
  pt := aRootCellG P
  lc := aLiftCellG P
  rc := Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := NockVM.formRRow (parentRecordG P) MemoryTable.formRDefault
  cprime? := some (NockVM.formRCprime (parentRecordG P) MemoryTable.formRDefault)
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := -1

def aDecomposeOuterPubG : MemoryTable.Pub K97cubic where
  st := .decompose
  pt := aLiftCellG P
  lc := aHeadCellG P
  rc := aInnerRootCell
  lcSt := .halt
  rcSt := .read_root
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

def aHeadHaltPubG : MemoryTable.Pub K97cubic where
  st := .halt
  pt := aHeadCellG P
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

/-! ## D. The three parent-touching `Vmem` acceptances (generic) -/

/-- **(A)/(B):** the two opening `rfl`s compare `pt.noun`/`lc.noun` (both `encS parentFormula`) and
close for *any* noun; the remainder is the opcode-invariant timestamp (`ts = 4`) and pole
(`= -1`). -/
theorem aReadOuter_acceptsG : Vmem memInputsS (aReadOuterPubG P) := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp only [eqBlk, aReadOuterPubG, aRootCellG]
    repeat' constructor
  · change (aReadOuterPubG P).icur - (aReadOuterPubG P).ipre
        = (pole memInputsS (aReadOuterPubG P).mem (aReadOuterPubG P).cprime)⁻¹
    rw [show (aReadOuterPubG P).mem =
        NockVM.formRRow (parentRecordG P) MemoryTable.formRDefault from rfl,
      show (aReadOuterPubG P).cprime =
        NockVM.formRCprime (parentRecordG P) MemoryTable.formRDefault from rfl, pole_rowS,
      pole_parentRecordG, inv_neg_one]
    simp [aReadOuterPubG]

/-- **(B), gated on `servedSeed ≠ 0`:** the sole noun step is the `enc_cons` homomorphism at the
parent formula's cons shape (`P.hcons`), generic in the head atom. -/
theorem aDecomposeOuter_acceptsG : Vmem memInputsS (aDecomposeOuterPubG P) := by
  refine ⟨MemoryTable.verBool_holds _, ?_, rfl⟩
  refine ⟨?_, ?_, ?_, rfl⟩
  · show (aLiftCellG P).noun
        = FP.cons servedSeed (aHeadCellG P).noun aInnerRootCell.noun
    rw [show (aLiftCellG P).noun = encS P.parentFormula from rfl,
      show (aHeadCellG P).noun = encS P.parentHead from rfl,
      show aInnerRootCell.noun = encS formulaS from rfl, P.hcons]
    exact GlobalCarryRecognizer.enc_cons servedSeed_ne P.parentHead formulaS
  · rfl
  · rfl

/-- **(B):** closes via `enc_atom` for any parent head atom (`P.hhead`). -/
theorem aHeadHalt_acceptsG : Vmem memInputsS (aHeadHaltPubG P) := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simp [aHeadHaltPubG, aHeadCellG, encS, P.hhead, memInputsS,
        GlobalCarryRecognizer.enc_atom]
    · simp [aHeadHaltPubG, aHeadCellG, encS, P.hhead, GlobalCarryRecognizer.enc_atom]
  · rfl

/-! ## D'. The generic root-`A` outer-verify row.

The outer verify row lives over the **shared** cells `aOuterVerifyCell`/`aInnerLiftCell`; its only
parent-touching content is the memory record `mem = parentRecordG`, whose timestamp (`= 4`) and pole
(`= -1`) are head-independent. -/

def aVerifyOuterPubG : MemoryTable.Pub K97cubic where
  st := .verify_child
  pt := aOuterVerifyCell
  lc := aInnerLiftCell
  rc := Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := NockVM.formRRow (parentRecordG P) MemoryTable.formRDefault
  cprime? := some (NockVM.formRCprime (parentRecordG P) MemoryTable.formRDefault)
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 1

/-- **(A):** shared cells; the record `mem` contributes only its head-independent timestamp and
pole. -/
theorem aVerifyOuter_acceptsG : Vmem memInputsS (aVerifyOuterPubG P) := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp only [eqBlk, aVerifyOuterPubG]
    repeat' constructor
  · change (aVerifyOuterPubG P).ipre - (aVerifyOuterPubG P).icur
        = (pole memInputsS (aVerifyOuterPubG P).mem (aVerifyOuterPubG P).cprime)⁻¹
    rw [show (aVerifyOuterPubG P).mem =
        NockVM.formRRow (parentRecordG P) MemoryTable.formRDefault from rfl,
      show (aVerifyOuterPubG P).cprime =
        NockVM.formRCprime (parentRecordG P) MemoryTable.formRDefault from rfl, pole_rowS,
      pole_parentRecordG, inv_neg_one]
    simp [aVerifyOuterPubG]

/-! ## G. Generic memory-table well-formedness of the four parent-touching rows -/

theorem aReadOuter_wfG : MemoryTable.WF memInputsS (aReadOuterPubG P) where
  pole_ne := by
    intro
    show pole memInputsS (aReadOuterPubG P).mem (aReadOuterPubG P).cprime ≠ 0
    simpa [aReadOuterPubG, Pub.cprime] using pole_parentRecordG_ne P

theorem aDecomposeOuter_wfG : MemoryTable.WF memInputsS (aDecomposeOuterPubG P) where
  pole_ne h := by simp [aDecomposeOuterPubG] at h

theorem aHeadHalt_wfG : MemoryTable.WF memInputsS (aHeadHaltPubG P) where
  pole_ne h := by simp [aHeadHaltPubG] at h

theorem aVerifyOuter_wfG : MemoryTable.WF memInputsS (aVerifyOuterPubG P) where
  pole_ne := by
    intro
    show pole memInputsS (aVerifyOuterPubG P).mem (aVerifyOuterPubG P).cprime ≠ 0
    simpa [aVerifyOuterPubG, Pub.cprime] using pole_parentRecordG_ne P

/-! ## H. Generic root-`A` memory trees + `RVT` (plan §(i), structural).

The parent-rooted labels/trees are generic; the shared inner rows (`aReadInner`,
`aDecomposeInner`, …) and their `RVT`s are reused verbatim from `MultiRootServedFixture`. -/

abbrev aReadOuterLabelG := memLabelS .read_root (aReadOuterPubG P)
abbrev aDecomposeOuterLabelG := memLabelS .decompose (aDecomposeOuterPubG P)
abbrev aHeadHaltLabelG := memLabelS .halt (aHeadHaltPubG P)
abbrev aVerifyOuterLabelG := memLabelS .verify_child (aVerifyOuterPubG P)

theorem aHeadHaltLabelG_accepts : MemoryTable.Fmem (aHeadHaltLabelG P) (fun _ => none) := by
  refine ⟨rfl, aHeadHalt_acceptsG P, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, MemoryTable.fanoutMem]
  · intro i hi; simp [memLabelS, MemoryTable.fanoutMem] at hi

/-- The outer-verify child is the **shared** inner-decompose subtree, so its child-out is the shared
`aVerifyOuterOut`. -/
theorem aVerifyOuterLabelG_accepts :
    MemoryTable.Fmem (aVerifyOuterLabelG P) aVerifyOuterOut := by
  refine ⟨rfl, aVerifyOuter_acceptsG P, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, aVerifyOuterOut, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i
    · simp [aVerifyOuterOut, MemoryTable.memCell, memLabelS, aVerifyOuterPubG, aInnerLiftCell,
        aDecomposeInnerPub]
    · simp [memLabelS, MemoryTable.fanoutMem] at hi

def aDecomposeOuterOutG : Fin 2 → Option (MState × MemoryTable.DTmem K97cubic)
  | 0 => some (aHeadHaltLabelG P)
  | 1 => some aReadInnerLabel

theorem aDecomposeOuterLabelG_accepts :
    MemoryTable.Fmem (aDecomposeOuterLabelG P) (aDecomposeOuterOutG P) := by
  refine ⟨rfl, aDecomposeOuter_acceptsG P, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, aDecomposeOuterOutG, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i <;>
      simp [aDecomposeOuterOutG, MemoryTable.memCell, memLabelS, aDecomposeOuterPubG,
        aHeadHaltPubG, aHeadCellG, aInnerRootCell, aReadInnerPub]

def aReadInnerOutG : Fin 2 → Option (MState × MemoryTable.DTmem K97cubic)
  | 0 => some (aVerifyOuterLabelG P)
  | 1 => none

/-- The inner-read label is **shared**, but its accepted child is the generic outer-verify row, so
its child-out threads the generic label. -/
theorem aReadInnerLabelG_accepts :
    MemoryTable.Fmem aReadInnerLabel (aReadInnerOutG P) := by
  refine ⟨rfl, aReadInner_accepts, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, aReadInnerOutG, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i
    · simp [aReadInnerOutG, MemoryTable.memCell, memLabelS, aReadInnerPub, aVerifyOuterPubG,
        aOuterVerifyCell]
    · simp [memLabelS, MemoryTable.fanoutMem] at hi

def aReadOuterOutG : Fin 2 → Option (MState × MemoryTable.DTmem K97cubic)
  | 0 => some (aDecomposeOuterLabelG P)
  | 1 => none

theorem aReadOuterLabelG_accepts :
    MemoryTable.Fmem (aReadOuterLabelG P) (aReadOuterOutG P) := by
  refine ⟨rfl, aReadOuter_acceptsG P, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [memLabelS, aReadOuterOutG, MemoryTable.fanoutMem]
  · intro i hi
    fin_cases i
    · simp [aReadOuterOutG, MemoryTable.memCell, memLabelS, aReadOuterPubG, aLiftCellG,
        aDecomposeOuterPubG]
    · simp [memLabelS, MemoryTable.fanoutMem] at hi

def aHeadHaltTreeG : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node (aHeadHaltLabelG P) []
def aVerifyOuterTreeG : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node (aVerifyOuterLabelG P) [aDecomposeInnerTree]
def aReadInnerTreeG : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node aReadInnerLabel [aVerifyOuterTreeG P]
def aDecomposeOuterTreeG : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node (aDecomposeOuterLabelG P) [aHeadHaltTreeG P, aReadInnerTreeG P]
/-- Serviced root `A`, generic over the parent formula. -/
def rootATreeG : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node (aReadOuterLabelG P) [aDecomposeOuterTreeG P]

theorem aHeadHaltTreeG_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) (aHeadHaltTreeG P) := by
  unfold RVT
  exact ⟨aHeadHaltLabelG_accepts P, by simp,
    ⟨fun _ => aHeadHaltLabelG_accepts P, fun _ => rfl⟩⟩

theorem aVerifyOuterTreeG_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) (aVerifyOuterTreeG P) := by
  unfold aVerifyOuterTreeG RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 2 =>
        (NTree.node (aVerifyOuterLabelG P) [aDecomposeInnerTree]).childLabel i) =
        aVerifyOuterOut by funext i; fin_cases i <;> rfl]
    exact aVerifyOuterLabelG_accepts P
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact aDecomposeInnerTree_rvt
  · simp [NTree.isLeaf, MemoryTable.Fmem, memLabelS, MemoryTable.fanoutMem]

theorem aReadInnerTreeG_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) (aReadInnerTreeG P) := by
  unfold aReadInnerTreeG RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 2 =>
        (NTree.node aReadInnerLabel [aVerifyOuterTreeG P]).childLabel i) =
        aReadInnerOutG P by funext i; fin_cases i <;> rfl]
    exact aReadInnerLabelG_accepts P
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact aVerifyOuterTreeG_rvt P
  · simp [NTree.isLeaf, MemoryTable.Fmem, memLabelS, MemoryTable.fanoutMem]

theorem aDecomposeOuterTreeG_rvt :
    RVT (MemoryTable.Fmem (K := K97cubic)) (aDecomposeOuterTreeG P) := by
  unfold aDecomposeOuterTreeG RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 2 =>
        (NTree.node (aDecomposeOuterLabelG P)
          [aHeadHaltTreeG P, aReadInnerTreeG P]).childLabel i) =
        aDecomposeOuterOutG P by funext i; fin_cases i <;> rfl]
    exact aDecomposeOuterLabelG_accepts P
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact aHeadHaltTreeG_rvt P
    · exact aReadInnerTreeG_rvt P
  · simp [NTree.isLeaf, MemoryTable.Fmem, memLabelS, MemoryTable.fanoutMem]

theorem rootATreeG_rvt : RVT (MemoryTable.Fmem (K := K97cubic)) (rootATreeG P) := by
  unfold rootATreeG RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 2 =>
        (NTree.node (aReadOuterLabelG P) [aDecomposeOuterTreeG P]).childLabel i) =
        aReadOuterOutG P by funext i; fin_cases i <;> rfl]
    exact aReadOuterLabelG_accepts P
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact aDecomposeOuterTreeG_rvt P
  · simp [NTree.isLeaf, MemoryTable.Fmem, memLabelS, MemoryTable.fanoutMem]

/-! ## L. Generic parent record: non-zero and active (plan §(iii)).

The shared fingerprint helpers `fpRealizedS`/`fpActiveS` and the boundedness of the shared child
nouns are opcode-invariant and reused verbatim from `MultiRootServedFixture`. The parent-touching
boundedness facts come from the interface fields `P.hheadBounded`/`P.hformulaBounded`/
`P.hresultBounded`. -/

theorem parentRecordG_ne_zero : parentRecordG P ≠ ComputeTable.MemRec.zero := by
  intro h
  have hts := congrArg ComputeTable.MemRec.ts h
  rw [ts_parentRecordG] at hts
  exact ts_ne_zero_4 (by simpa [ComputeTable.MemRec.zero] using hts)

theorem parentRecordG_active : MemRecSlotRealized servedSeed 97 .active (parentRecordG P) :=
  ⟨parentRecordG_ne_zero P, fpActiveS P.hformulaBounded, fpActiveS bounded_formulaS⟩

/-! ## P. Generic bounded-noun realization of the four parent-touching public rows (plan §(iii)).

The kind-specific helpers `memSingleChildRealization`/`memDecomposeRealization`/
`memHaltRealization`/`leafAtomS` are opcode-invariant and reused verbatim. -/

theorem aReadOuter_realizationG : MemoryPublicRowNounRealization 97 (aReadOuterLabelG P) :=
  memSingleChildRealization (aReadOuterPubG P) rfl
    (fpActiveS P.hformulaBounded) (fpActiveS P.hformulaBounded) rfl rfl
    ((parentRecordG_active P).formRRow _)

theorem aDecomposeOuter_realizationG :
    MemoryPublicRowNounRealization 97 (aDecomposeOuterLabelG P) :=
  memDecomposeRealization (aDecomposeOuterPubG P) (fpActiveS P.hformulaBounded)
    (fpActiveS P.hheadBounded) (fpActiveS bounded_formulaS) rfl

theorem aHeadHalt_realizationG : MemoryPublicRowNounRealization 97 (aHeadHaltLabelG P) :=
  memHaltRealization (aHeadHaltPubG P) (fpActiveS P.hheadBounded) rfl rfl rfl

theorem aVerifyOuter_realizationG :
    MemoryPublicRowNounRealization 97 (aVerifyOuterLabelG P) :=
  memSingleChildRealization (aVerifyOuterPubG P) rfl
    (fpActiveS bounded_formulaS) (fpActiveS bounded_formulaS) rfl rfl
    ((parentRecordG_active P).formRRow _)

/-! ## P'. Generic leaf-atom realization of the root-`A` subtrees.

The shared inner subtrees keep their concrete leaf-atom realizations; only the parent head-halt
leaf carries the opcode atom `P.headAtom` (`P.hhead`, `P.hheadlt`). -/

theorem leafAtoms_aHeadHaltTreeG : MemoryLeafAtomsRealized 97 (aHeadHaltTreeG P) :=
  leafAtomS P.headAtom P.hheadlt (aHeadHaltPubG P)
    (by rw [show (aHeadHaltPubG P).pt.noun = encS P.parentHead from rfl, P.hhead])

theorem leafAtoms_aVerifyOuterTreeG : MemoryLeafAtomsRealized 97 (aVerifyOuterTreeG P) :=
  leafAtoms_aDecomposeInnerTree

theorem leafAtoms_aReadInnerTreeG : MemoryLeafAtomsRealized 97 (aReadInnerTreeG P) :=
  leafAtoms_aVerifyOuterTreeG P

theorem leafAtoms_aDecomposeOuterTreeG : MemoryLeafAtomsRealized 97 (aDecomposeOuterTreeG P) :=
  ⟨leafAtoms_aHeadHaltTreeG P, leafAtoms_aReadInnerTreeG P⟩

theorem leafAtoms_rootATreeG : MemoryLeafAtomsRealized 97 (rootATreeG P) :=
  leafAtoms_aDecomposeOuterTreeG P

end

/-! ## E. Regression evidence — `op4Params` reproduces the concrete objects definitionally -/

/-- The generic parent record at `op4Params` is *definitionally* the concrete `parentRecordS`. -/
theorem parentRecordG_eq_op4 : parentRecordG op4Params = parentRecordS := rfl

theorem aRootCellG_eq_op4 : aRootCellG op4Params = aRootCell := rfl
theorem aLiftCellG_eq_op4 : aLiftCellG op4Params = aLiftCell := rfl
theorem aHeadCellG_eq_op4 : aHeadCellG op4Params = aHeadCell := rfl
theorem aReadOuterPubG_eq_op4 : aReadOuterPubG op4Params = aReadOuterPub := rfl
theorem aDecomposeOuterPubG_eq_op4 : aDecomposeOuterPubG op4Params = aDecomposeOuterPub := rfl
theorem aHeadHaltPubG_eq_op4 : aHeadHaltPubG op4Params = aHeadHaltPub := rfl
theorem aVerifyOuterPubG_eq_op4 : aVerifyOuterPubG op4Params = aVerifyOuterPub := rfl

/-- The whole generic root-`A` tree at `op4Params` is *definitionally* the concrete `rootATree`. -/
theorem rootATreeG_eq_op4 : rootATreeG op4Params = rootATree := rfl
theorem aDecomposeOuterTreeG_eq_op4 : aDecomposeOuterTreeG op4Params = aDecomposeOuterTree := rfl
theorem aHeadHaltTreeG_eq_op4 : aHeadHaltTreeG op4Params = aHeadHaltTree := rfl
theorem aVerifyOuterTreeG_eq_op4 : aVerifyOuterTreeG op4Params = aVerifyOuterTree := rfl
theorem aReadInnerTreeG_eq_op4 : aReadInnerTreeG op4Params = aReadInnerTree := rfl

/-! ## F. Both opcodes discharge the same generic acceptances -/

theorem aReadOuter_accepts_op4 : Vmem memInputsS (aReadOuterPubG op4Params) :=
  aReadOuter_acceptsG op4Params
theorem aReadOuter_accepts_op3 : Vmem memInputsS (aReadOuterPubG op3Params) :=
  aReadOuter_acceptsG op3Params

theorem aDecomposeOuter_accepts_op4 : Vmem memInputsS (aDecomposeOuterPubG op4Params) :=
  aDecomposeOuter_acceptsG op4Params
theorem aDecomposeOuter_accepts_op3 : Vmem memInputsS (aDecomposeOuterPubG op3Params) :=
  aDecomposeOuter_acceptsG op3Params

theorem aHeadHalt_accepts_op4 : Vmem memInputsS (aHeadHaltPubG op4Params) :=
  aHeadHalt_acceptsG op4Params
theorem aHeadHalt_accepts_op3 : Vmem memInputsS (aHeadHaltPubG op3Params) :=
  aHeadHalt_acceptsG op3Params

theorem aVerifyOuter_accepts_op4 : Vmem memInputsS (aVerifyOuterPubG op4Params) :=
  aVerifyOuter_acceptsG op4Params
theorem aVerifyOuter_accepts_op3 : Vmem memInputsS (aVerifyOuterPubG op3Params) :=
  aVerifyOuter_acceptsG op3Params

/-! ## G'. Both opcodes discharge the whole generic root-`A` tree `RVT`. -/

theorem rootATree_rvt_op4 : RVT (MemoryTable.Fmem (K := K97cubic)) (rootATreeG op4Params) :=
  rootATreeG_rvt op4Params
theorem rootATree_rvt_op3 : RVT (MemoryTable.Fmem (K := K97cubic)) (rootATreeG op3Params) :=
  rootATreeG_rvt op3Params

/-! ## H'. Regression + both-opcode discharge for the generic root-`A` realization. -/

theorem parentRecordG_active_eq_op4 : parentRecordG_active op4Params = parentRecordS_active := rfl
theorem aReadOuter_realizationG_eq_op4 :
    aReadOuter_realizationG op4Params = aReadOuter_realization := rfl
theorem aVerifyOuter_realizationG_eq_op4 :
    aVerifyOuter_realizationG op4Params = aVerifyOuter_realization := rfl
theorem leafAtoms_rootATreeG_eq_op4 : leafAtoms_rootATreeG op4Params = leafAtoms_rootATree := rfl

theorem aReadOuter_realization_op3 :
    MemoryPublicRowNounRealization 97 (aReadOuterLabelG op3Params) :=
  aReadOuter_realizationG op3Params
theorem aDecomposeOuter_realization_op3 :
    MemoryPublicRowNounRealization 97 (aDecomposeOuterLabelG op3Params) :=
  aDecomposeOuter_realizationG op3Params
theorem aHeadHalt_realization_op3 :
    MemoryPublicRowNounRealization 97 (aHeadHaltLabelG op3Params) :=
  aHeadHalt_realizationG op3Params
theorem aVerifyOuter_realization_op3 :
    MemoryPublicRowNounRealization 97 (aVerifyOuterLabelG op3Params) :=
  aVerifyOuter_realizationG op3Params
theorem leafAtoms_rootATree_op3 : MemoryLeafAtomsRealized 97 (rootATreeG op3Params) :=
  leafAtoms_rootATreeG op3Params

end Nock.NockVMROM.Thm54.ServedForestModule

#print axioms Nock.NockVMROM.Thm54.ServedForestModule.pole_parentRecordG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.aReadOuter_acceptsG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.aDecomposeOuter_acceptsG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.aHeadHalt_acceptsG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.parentRecordG_eq_op4
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.aReadOuter_accepts_op3
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.aVerifyOuter_acceptsG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.rootATreeG_rvt
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.rootATreeG_eq_op4
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.rootATree_rvt_op3
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.parentRecordG_active
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.aReadOuter_realizationG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.leafAtoms_rootATreeG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.leafAtoms_rootATreeG_eq_op4
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.leafAtoms_rootATree_op3
