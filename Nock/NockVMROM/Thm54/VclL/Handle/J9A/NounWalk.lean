/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/NounWalk.lean

  `walkAOK_row` has no
  `nA`: the record's root `rv = natOf (e.trace ridx)` is a row of the accepted table `tb`
  (`denH_true_lt`), so `rv < tb.length`; `tb.length = nA` is tied at the LINK (`HokJ9G.lean:340`).

  * `walkAOK_row_lt`: `∀ j < n, natOf (ridx of row j) < tb.length` (the premises of `walkAOK_row` that this needs).
  * `walkAOK_row9`: `walkAOK_row` and `walkAOK_row_lt` in one statement (`WalkAOK … ∧ rv < tb.length`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.J9A.NounWalk

open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8 (walkAOK_row)

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW
open Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8 (recNat bitF zq_val zq_axis natKey_walk childHOfK)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8 (extA extA_of_denotes)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (ProvP)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (natKey padK)
open Nock.ComputeTable (FP)
open Nock.Atoms (val)
open Module
open scoped Polynomial

noncomputable section

section Row
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (kroots : ℕ) (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipHQK δ kroots b hn nodes orbit chals pubs).rap.w → (ZMod p)[X])

open scoped Classical in
theorem walkAOK_row_lt
    (hsat : (walkChipHQK δ kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipHQK δ kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar (ZMod p))
    (hq : 2 ^ 63 < ringChar (ZMod p))
    (hz : Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3) ≠ 0)
    {tb : List (CellRow (ringChar (ZMod p)) (Quad (algebraMap (ZMod p) K δ)))}
    {vl : List (VKey (Quad (algebraMap (ZMod p) K δ)))}
    (htab : TableAccepts (Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3)) tb vl)
    (hT2 : Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3) ∉ tableBadSeeds fuelChip (tb.map (·.b0)) [])
    (hdy : Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3) ∉ cellDyckRootSeeds fuelChip (tb.map (·.b0)))
    (hX : KeysExported tb (walkDataOf δ kroots b hn nodes orbit chals pubs
      (restrictWalkK δ kroots b hn nodes orbit chals pubs Q)).X)
    (hHX : ∀ j < n, ∃ c ∈ tb,
      (natOf ((walkEnvFA δ kroots b hn nodes orbit chals pubs Q j).trace WChip.idx),
        childHOf (walkEnvFA δ kroots b hn nodes orbit chals pubs Q j) false,
        childHOf (walkEnvFA δ kroots b hn nodes orbit chals pubs Q j) true) = exportRec c.b0)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (walkDataOf δ kroots b hn nodes orbit chals pubs
        (restrictWalkK δ kroots b hn nodes orbit chals pubs Q)))
    (htb : tb.length ≤ ringChar (ZMod p)) :
    ∀ j < n, natOf ((walkEnvFA δ kroots b hn nodes orbit chals pubs Q j).trace WChip.ridx) < tb.length := by
  have hF := GeneratedField.primeFieldElems_zmod p
  intro j hj
  have hbb : ∃ bb : Bool, True := ⟨true, trivial⟩
  obtain ⟨bb, -⟩ := hbb
  have : NeZero (ringChar (ZMod p)) := ⟨(Fact.out : (ringChar (ZMod p)).Prime).ne_zero⟩
  obtain ⟨ri, rt, nn, h1, h2, h3, h4⟩ := atomWalk_records_genuine δ kroots b hn nodes orbit chals pubs Q hsat
    hbind hinj hadj hF hk hkn hkp hq hz htab hT2 hdy hX hHX hout (j + 1) (by omega) (by omega) bb
  simp only [Nat.add_sub_cancel] at h3
  set eA := walkEnvFA δ kroots b hn nodes orbit chals pubs Q j
  have hr : (walkEnvF b hn nodes orbit chals pubs (restrictWalkK δ kroots b hn nodes orbit chals pubs Q) j).trace
      WChip.ridx = eA.trace WChip.ridx :=
    (walkEnvFA_trace δ kroots b hn nodes orbit chals pubs Q j (by decide)).symm
  have hpre : (walkEnvF b hn nodes orbit chals pubs (restrictWalkK δ kroots b hn nodes orbit chals pubs Q) j).trace
      WChip.pre = eA.trace WChip.pre :=
    (walkEnvFA_trace δ kroots b hn nodes orbit chals pubs Q j (by decide)).symm
  have h1' : zq (eA.trace WChip.ridx) = (ri : ZMod (ringChar (ZMod p))) := by rw [← hr]; exact h1
  have hri_lt : ri < ringChar (ZMod p) := lt_of_lt_of_le (denH_true_lt h2) (by simpa using htb)
  have hri : natOf (eA.trace WChip.ridx) = ri := by
    have := congrArg ZMod.val h1'
    rw [zq_val hF, ZMod.val_natCast, Nat.mod_eq_of_lt hri_lt] at this
    exact this
  have := denH_true_lt h2
  rw [hri]; simpa using this

open scoped Classical in
theorem walkAOK_row9
    (hsat : (walkChipHQK δ kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipHQK δ kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar (ZMod p))
    (hq : 2 ^ 63 < ringChar (ZMod p))
    (hz : Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3) ≠ 0)
    {tb : List (CellRow (ringChar (ZMod p)) (Quad (algebraMap (ZMod p) K δ)))}
    {vl : List (VKey (Quad (algebraMap (ZMod p) K δ)))}
    (htab : TableAccepts (Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3)) tb vl)
    (hT2 : Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3) ∉ tableBadSeeds fuelChip (tb.map (·.b0)) [])
    (hdy : Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3) ∉ cellDyckRootSeeds fuelChip (tb.map (·.b0)))
    (hX : KeysExported tb (walkDataOf δ kroots b hn nodes orbit chals pubs
      (restrictWalkK δ kroots b hn nodes orbit chals pubs Q)).X)
    (hHX : ∀ j < n, ∃ c ∈ tb,
      (natOf ((walkEnvFA δ kroots b hn nodes orbit chals pubs Q j).trace WChip.idx),
        childHOf (walkEnvFA δ kroots b hn nodes orbit chals pubs Q j) false,
        childHOf (walkEnvFA δ kroots b hn nodes orbit chals pubs Q j) true) = exportRec c.b0)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (walkDataOf δ kroots b hn nodes orbit chals pubs
        (restrictWalkK δ kroots b hn nodes orbit chals pubs Q)))
    (hs : SerialOK (tb.map (·.b0))) (htb : tb.length ≤ ringChar (ZMod p)) {rA : ℕ → ARow}
    (hag : ∀ c ∈ tb.map (·.b0), AgreeRow c (rA c.idx))
    {q' : ℕ} (tC : List (CellRowB0 q')) :
    ∀ j < n, ∀ bb : Bool,
      WalkAOK (denK tC (extA rA)) combN (recNat (walkEnvFA δ kroots b hn nodes orbit chals pubs Q j) bb) ∧
        natOf ((walkEnvFA δ kroots b hn nodes orbit chals pubs Q j).trace WChip.ridx) < tb.length := by
  intro j hj bb
  exact ⟨walkAOK_row δ kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hk hkn hkp hq hz htab hT2 hdy hX hHX hout
      hs htb hag tC j hj bb, walkAOK_row_lt δ kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hk hkn hkp hq hz
      htab hT2 hdy hX hHX hout htb j hj⟩

end Row

end

end Nock.NockVMROM.Thm54.VclL.Handle.J9A.NounWalk

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.J9A.NounWalk.walkAOK_row_lt
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.J9A.NounWalk.walkAOK_row9
