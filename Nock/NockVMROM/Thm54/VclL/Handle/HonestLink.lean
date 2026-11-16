/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestLink.lean

  1. `honestJ_cellRows_eq`: the cell rows of the honest memory datum built from the compiler run's
     `HonestVCLJ` (`jointMem`, the datum `honestVCLJ_of_run` feeds) ARE `cellRows0 … (demT HJ.t).cells`
     (by `rfl`: `jointMem.d = demT HJ.t`, `HonestVCL.cellRows` unfolds to `cellRows0 … d.cells`).
  2. Hash-consing carried from `tableB0` to `cellRows0`, beyond the `idx` field: on a nodup row list
     under `n < ringChar F` the rows are pairwise distinct, equal nouns have equal rows, and the child
     serial columns `idL / idR` of a row are equal iff the child cells are equal (children of closed
     row lists are rows).  So handle equality (`kind`, `serial`) of the chip decides noun equality
     on the honest table.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HashCons
import Nock.NockVMROM.Thm54.VclL.Compute.TowerJointHonest
import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestRun

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Walk Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.StrictExtension

noncomputable section

/-! ## 1. The honest run's cell data is `cellRows0 … cells` -/

section Link
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))]
  {hT hP hC : ℕ}

/-- The memory datum built from the run's `HonestVCLJ` has the run's demand. -/
theorem jointMem_d (HJ : HonestVCLJ (K := K) δF hT hP hC)
    (hf : JointMemFacts δF hT hP hC HJ.toHonestVCLT) :
    (jointMem δF HJ.toHonestVCLT hf).d = demT HJ.t := rfl

/-- **Carry-over 1.**  The generated cell rows of the honest memory datum of the run are
`cellRows0 … (demT HJ.t).cells`, with the run's multiplicity lists. -/
theorem honestJ_cellRows_eq (HJ : HonestVCLJ (K := K) δF hT hP hC)
    (hf : JointMemFacts δF hT hP hC HJ.toHonestVCLT) (z : Quad (algebraMap F K δF)) :
    (jointMem δF HJ.toHonestVCLT hf).cellRows z =
      cellRows0 δF z (demT HJ.t).cells (vcsOf (demT HJ.t).cells [])
        (xs0P (demT HJ.t).cells (demT HJ.t).preads (demT HJ.t).reads)
        (xs1P (demT HJ.t).cells (demT HJ.t).preads (demT HJ.t).reads) := rfl

/-- The tree of `honestVCLJ_of_run` is the run's tree, so the demand above is the run's. -/
theorem honestVCLJ_of_run_t {fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar F) fuel subject formula)
    (Ksz : ℕ) (αs : Quad (algebraMap F K δF)) (hK3 : Module.finrank F K = 3)
    (hp : 25 ≤ ringChar F)
    (hC1 : 1 ≤ hC) (hT1 : 1 ≤ hT) (hP1 : 1 ≤ hP)
    (hFC : 3 * 2 ^ hC ∣ Fintype.card F - 1) (hFT : 3 * 2 ^ hT ∣ Fintype.card F - 1)
    (hFP : 3 * 2 ^ hP ∣ Fintype.card F - 1)
    (hsize : nRows (runTree (K := K) δF hrun hbound) ≤ 2 ^ hC)
    (hrowsC : 3 * nRows (runTree (K := K) δF hrun hbound) < ringChar K)
    (hsizeT : cellLen (K := K) δF (runTree (K := K) δF hrun hbound) ≤ 2 ^ hT)
    (hsizeP : pathLen (K := K) δF (runTree (K := K) δF hrun hbound) ≤ 2 ^ hP) :
    (honestVCLJ_of_run (K := K) δF hT hP hC hrun hbound Ksz αs hK3 hp hC1 hT1 hP1 hFC hFT hFP hsize hrowsC
        hsizeT hsizeP).t = runTree (K := K) δF hrun hbound := rfl

end Link

/-! ## 2. Hash-consing at `cellRows0`, beyond the `idx` field -/

section HashConsRows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] {δF : F}
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- Naturals below the characteristic are cast-injective. -/
theorem cast_inj_of_lt {a b : ℕ} (ha : a < ringChar F) (hb : b < ringChar F)
    (h : (a : F) = (b : F)) : a = b := by
  haveI := ringChar.charP F
  exact Nat.ModEq.eq_of_lt_of_lt ((CharP.natCast_eq_natCast F (ringChar F)).mp h) ha hb

/-- **Rows are pairwise distinct**: on a nodup row list with `n < ringChar F`, `cellRows0 j =
cellRows0 k` forces `j = k` (the `idx` column is the closure position). -/
theorem cellRows0_inj (z : Quad (algebraMap F K δF)) (cells vcs xs0 xs1 : List Noun)
    (hnd : cells.Nodup) (hn : cells.length < ringChar F) {j k : ℕ} (hj : j < cells.length)
    (hk : k < cells.length)
    (h : cellRows0 δF z cells vcs xs0 xs1 j = cellRows0 δF z cells vcs xs0 xs1 k) : j = k := by
  have h1 := congrArg CellVals.idx h
  rw [cellRows0_idx z cells vcs xs0 xs1 hnd hj, cellRows0_idx z cells vcs xs0 xs1 hnd hk] at h1
  exact cast_inj_of_lt (hj.trans hn) (hk.trans hn) h1

/-- **Equal nouns have equal rows, and distinct positions hold distinct nouns** (one row per
noun at `cellRows0`). -/
theorem cellRows0_noun_iff (z : Quad (algebraMap F K δF)) (cells vcs xs0 xs1 : List Noun)
    (hnd : cells.Nodup) (hn : cells.length < ringChar F) {j k : ℕ} (hj : j < cells.length)
    (hk : k < cells.length) :
    cells[j] = cells[k] ↔ cellRows0 δF z cells vcs xs0 xs1 j = cellRows0 δF z cells vcs xs0 xs1 k := by
  constructor
  · intro h
    have : j = k := (List.Nodup.getElem_inj_iff hnd).mp h
    subst this; rfl
  · intro h
    have := cellRows0_inj z cells vcs xs0 xs1 hnd hn hj hk h
    subst this; rfl

/-- The row of a closure noun is the row at its closure position. -/
theorem cellRows0_of_mem (z : Quad (algebraMap F K δF)) (cells vcs xs0 xs1 : List Noun)
    {n : Noun} (hn : n ∈ cells) :
    cellRows0 δF z cells vcs xs0 xs1 (cells.idxOf n) = cellRow0 δF z cells vcs xs0 xs1 n := by
  have hi : cells.idxOf n < cells.length := List.idxOf_lt_length_iff.mpr hn
  rw [cellRows0_getElem z cells vcs xs0 xs1 hi, List.getElem_idxOf hi]

/-- **The child serial columns decide child equality**: for two rows of a list closed under cell
children, with cell left children, `idL` agrees iff the left children are equal. -/
theorem cellRow0_idL_iff (z : Quad (algebraMap F K δF)) (cells vcs xs0 xs1 : List Noun)
    (hn : cells.length < ringChar F)
    (hclosed : ∀ n ∈ cells, ∀ c ∈ childCells n, c ∈ cells)
    {a b : Noun} (ha : a ∈ cells) (hb : b ∈ cells)
    (hha : (hdN a).isCell = true) (hhb : (hdN b).isCell = true) :
    (cellRow0 δF z cells vcs xs0 xs1 a).idL = (cellRow0 δF z cells vcs xs0 xs1 b).idL ↔
      hdN a = hdN b := by
  have hcell : ∀ n ∈ cells, (hdN n).isCell = true → hdN n ∈ cells := by
    intro n hn' hh
    refine hclosed n hn' _ ?_
    cases n with
    | atom _ => simp [hdN, Noun.isCell] at hh
    | cell x y =>
      cases hx : x with
      | atom _ => simp [hdN, hx, Noun.isCell] at hh
      | cell u v => simp [childCells, selfCell, hdN, hx]
  have h1 := hcell a ha hha
  have h2 := hcell b hb hhb
  have i1 := List.idxOf_lt_length_iff.mpr h1
  have i2 := List.idxOf_lt_length_iff.mpr h2
  simp only [cellRow0, hha, hhb, if_true]
  constructor
  · intro h
    have := cast_inj_of_lt (i1.trans hn) (i2.trans hn) h
    have e1 := List.getElem_idxOf i1
    have e2 := List.getElem_idxOf i2
    simp only [this] at e1
    exact e1.symm.trans e2
  · intro h; rw [h]

end HashConsRows

end

end Nock.NockVMROM.Thm54.VclL.Handle
