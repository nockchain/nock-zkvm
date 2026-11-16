/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHWalkPubs.lean

* `lastK6_scan`: `lastK6 (scanK6 l) = (scanK6 l).getD (l.length - 1) 0`.
  * `toQ_last_sum`: the last inclusive prefix sum is the full sum.
  * `toQ_xT / toQ_pT / toQ_hxT / toQ_hpT`: the four exec terminals map to `wxT / wpT / whX / whP`.
  * `walkGenRowsB_pubs`: `K3.toK ((walkGenRowsB …).2 j) = pubsWOf … j`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkGlue

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkPubs

open Nock Nock.Walk Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalk
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkRow
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)

theorem lastK6_scan (l : List K6) : Gen.lastK6 (Gen.scanK6 l) = (Gen.scanK6 l).getD (l.length - 1) 0 := by
  have hlen : (Gen.scanK6 l).length = l.length := by simp [scanK6_eq]
  unfold Gen.lastK6
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hlen]
  simp [List.getD_eq_getElem?_getD]

section Main
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))] [Fact (ringChar (ZMod P)).Prime]
  [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- The last inclusive prefix sum is the full sum. -/
theorem toQ_last_sum (l : List K6) (N : ℕ) (hl : l.length = N)
    (F : ℕ → Quad (algebraMap (ZMod P) KC deltaF))
    (hN : ∀ j < N, K6.toQ ((Gen.scanK6 l).getD j 0) = ∑ k ∈ Finset.range (j + 1), F k) :
    K6.toQ (Gen.lastK6 (Gen.scanK6 l)) = ∑ k ∈ Finset.range N, F k := by
  by_cases h0 : N = 0
  · subst h0
    have : l = [] := List.length_eq_zero_iff.mp hl
    subst this
    have h1 : K6.toQ (Gen.lastK6 (Gen.scanK6 [])) = 0 := by
      simp [Gen.lastK6, scanK6_eq, K6.toQ_zero]
    rw [h1, Finset.sum_range_zero]
  · rw [lastK6_scan, hl]
    have := hN (N - 1) (by omega)
    rw [show N - 1 + 1 = N by omega] at this
    exact this

theorem walkGenRowsB_pubs_def (k : Co) (y : K6) (α γ : K3) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ)
    (cert : ℕ → ℕ → ℕ) (cs : List Noun) (ws : List WRow) (kr : ℕ) (j : ℕ) :
    (walkGenRowsB k y α γ H rI cert cs ws kr).2 j =
      (let ds := dsL k y H rI cs ws
       let xT := Gen.lastK6 (Gen.scanK6 (ds.map (·.xInv)))
       let pT := Gen.lastK6 (Gen.scanK6 (ds.map pTermD))
       let hxT := Gen.lastK6 (Gen.scanK6 (ds.map (·.hXi)))
       let hpT := Gen.lastK6 (Gen.scanK6 (ds.map hPTermD))
       if j = 0 then xT.re else if j = 1 then xT.im else if j = 2 then pT.re else if j = 3 then pT.im
       else if j = 4 then hxT.re else if j = 5 then hxT.im else if j = 6 then hpT.re
       else if j = 7 then hpT.im else 0) := by
  unfold walkGenRowsB dsL
  rfl

variable (χe : CoinsE) (D : ComplJ8Data.J8Data P Rg fuel s f r)
  (hcs : ∀ c ∈ D.cells, c.isCell = true)
  (hwcell : ∀ u ∈ walkRows D.cells D.reads, u.label.node ∈ D.cells)
  (hwroot : ∀ u ∈ walkRows D.cells D.reads, u.label.root ∈ D.cells ∨ u.label.root.isCell = false)
include hcs hwcell hwroot

theorem dsL_len : (dsL (coOf χe) (yE χe) D.H (idxN D.cells) D.cells
    ((walkRows D.cells D.reads).map wrowOf)).length = (walkRows D.cells D.reads).length := by
  simp [dsL]

theorem toQ_xT :
    K6.toQ (Gen.lastK6 (Gen.scanK6 ((dsL (coOf χe) (yE χe) D.H (idxN D.cells) D.cells
      ((walkRows D.cells D.reads).map wrowOf)).map (·.xInv)))) = ComplJ8Of.wxT deltaF D (toχ χe) := by
  refine (toQ_last_sum _ (walkRows D.cells D.reads).length
    (by rw [List.length_map, dsL_len χe D hcs hwcell hwroot])
    (fun k => K6.toQ (dW χe D.H D.cells D.reads k).xInv) ?_).trans ?_
  · intro j hj
    exact scan_sum χe D hcs hwcell hwroot (fun d => d.xInv) j hj
  · unfold ComplJ8Of.wxT
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < (walkRows D.cells D.reads).length := Finset.mem_range.mp hk
    exact toQ_xInv χe D.H D.cells D.reads k hcs _ _ (hnodeK D hcs hwcell hwroot k hk')

theorem toQ_pT :
    K6.toQ (Gen.lastK6 (Gen.scanK6 ((dsL (coOf χe) (yE χe) D.H (idxN D.cells) D.cells
      ((walkRows D.cells D.reads).map wrowOf)).map pTermD))) = ComplJ8Of.wpT deltaF D (toχ χe) := by
  refine (toQ_last_sum _ (walkRows D.cells D.reads).length
    (by rw [List.length_map, dsL_len χe D hcs hwcell hwroot])
    (fun k => K6.toQ (pTermD (dW χe D.H D.cells D.reads k))) ?_).trans ?_
  · intro j hj
    exact scan_sum χe D hcs hwcell hwroot pTermD j hj
  · unfold ComplJ8Of.wpT
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < (walkRows D.cells D.reads).length := Finset.mem_range.mp hk
    unfold pTermD
    rw [K6.toQ_add, K6.toQ_mul, K6.toQ_mul, FillMem.toQ_lq, FillMem.toQ_lq,
      toQ_pInvL χe D.H D.cells D.reads k hcs _ _ (hrootK D hcs hwcell hwroot k hk'),
      toQ_pInvR χe D.H D.cells D.reads k hcs _ _ (hrootK D hcs hwcell hwroot k hk')]
    rfl

theorem toQ_hxT {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (walkRows D.cells D.reads).length)) :
    K6.toQ (Gen.lastK6 (Gen.scanK6 ((dsL (coOf χe) (yE χe) D.H (idxN D.cells) D.cells
      ((walkRows D.cells D.reads).map wrowOf)).map (·.hXi)))) =
      ComplJ8Of.whX deltaF powerBasis3 D o (toχ χe) := by
  refine (toQ_last_sum _ (walkRows D.cells D.reads).length
    (by rw [List.length_map, dsL_len χe D hcs hwcell hwroot])
    (fun k => K6.toQ (dW χe D.H D.cells D.reads k).hXi) ?_).trans ?_
  · intro j hj
    exact scan_sum χe D hcs hwcell hwroot (fun d => d.hXi) j hj
  · unfold ComplJ8Of.whX
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < (walkRows D.cells D.reads).length := Finset.mem_range.mp hk
    rw [toQ_hXi χe D.H D.cells D.reads k hcs (hnodeK D hcs hwcell hwroot k hk')]
    simp only [ComplJ8Of.wdN, WalkTraceHQ.dN, dif_pos hk']
    rw [(ComplJ8Of.walk_dRow_split deltaF powerBasis3 D o hinj (toχ χe) _ ⟨k, hk'⟩).1]
    rfl

theorem toQ_hpT {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (walkRows D.cells D.reads).length)) :
    K6.toQ (Gen.lastK6 (Gen.scanK6 ((dsL (coOf χe) (yE χe) D.H (idxN D.cells) D.cells
      ((walkRows D.cells D.reads).map wrowOf)).map hPTermD))) =
      ComplJ8Of.whP deltaF powerBasis3 D o (toχ χe) := by
  refine (toQ_last_sum _ (walkRows D.cells D.reads).length
    (by rw [List.length_map, dsL_len χe D hcs hwcell hwroot])
    (fun k => K6.toQ (hPTermD (dW χe D.H D.cells D.reads k))) ?_).trans ?_
  · intro j hj
    exact scan_sum χe D hcs hwcell hwroot hPTermD j hj
  · unfold ComplJ8Of.whP
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < (walkRows D.cells D.reads).length := Finset.mem_range.mp hk
    have mL := cN_mL χe D hcs hwcell hwroot k hk'
    have mR := cN_mR χe D hcs hwcell hwroot k hk'
    unfold hPTermD
    rw [K6.toQ_add, K6.toQ_mul, K6.toQ_mul, FillMem.toQ_lq, FillMem.toQ_lq,
      toQ_hPLi χe D.H D.cells D.reads k hcs (hrootK D hcs hwcell hwroot k hk'),
      toQ_hPRi χe D.H D.cells D.reads k hcs (hrootK D hcs hwcell hwroot k hk')]
    simp only [ComplJ8Of.wdN, WalkTraceHQ.dN, dif_pos hk', mL, mR]
    rw [(ComplJ8Of.walk_dRow_split deltaF powerBasis3 D o hinj (toχ χe) _ ⟨k, hk'⟩).2.1,
      (ComplJ8Of.walk_dRow_split deltaF powerBasis3 D o hinj (toχ χe) _ ⟨k, hk'⟩).2.2]
    rfl

/-- **The exec walk table's publics are the honest J-8 walk's.** -/
theorem walkGenRowsB_pubs {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (walkRows D.cells D.reads).length)) (j : ℕ) :
    K3.toK ((Nock.V1J8.Gen.walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) D.H
        (Nock.V1J8.Gen.idxN D.cells) HonestK8.certB8 D.cells ((walkRows D.cells D.reads).map wrowOf)
        (krW D.cells D.reads)).2 j) =
      ComplJ8Of.pubsWOf deltaF powerBasis3 D o (toχ χe) j := by
  have hx := toQ_xT χe D hcs hwcell hwroot
  have hp := toQ_pT χe D hcs hwcell hwroot
  have hhx := toQ_hxT χe D hcs hwcell hwroot o hinj
  have hhp := toQ_hpT χe D hcs hwcell hwroot o hinj
  rw [walkGenRowsB_pubs_def]
  dsimp only
  generalize Gen.lastK6 (Gen.scanK6 ((dsL (coOf χe) (yE χe) D.H (idxN D.cells) D.cells
      ((walkRows D.cells D.reads).map wrowOf)).map (·.xInv))) = xT at hx ⊢
  generalize Gen.lastK6 (Gen.scanK6 ((dsL (coOf χe) (yE χe) D.H (idxN D.cells) D.cells
      ((walkRows D.cells D.reads).map wrowOf)).map pTermD)) = pT at hp ⊢
  generalize Gen.lastK6 (Gen.scanK6 ((dsL (coOf χe) (yE χe) D.H (idxN D.cells) D.cells
      ((walkRows D.cells D.reads).map wrowOf)).map (·.hXi))) = hxT at hhx ⊢
  generalize Gen.lastK6 (Gen.scanK6 ((dsL (coOf χe) (yE χe) D.H (idxN D.cells) D.cells
      ((walkRows D.cells D.reads).map wrowOf)).map hPTermD)) = hpT at hhp ⊢
  simp only [ComplJ8Of.pubsWOf, ComplJ8Of.pubsW0, ComplJ8Of.pub2]
  by_cases j0 : j = 0
  · subst j0; simp only [reduceIte, Nat.reduceLT, Nat.reduceMod]; rw [← hx, re_toQ]
  by_cases j1 : j = 1
  · subst j1; simp only [reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceEqDiff, Nat.one_ne_zero]
    rw [← hx, im_toQ]
  by_cases j2 : j = 2
  · subst j2; simp only [reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceEqDiff]; rw [← hp, re_toQ]
  by_cases j3 : j = 3
  · subst j3; simp only [reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceEqDiff]; rw [← hp, im_toQ]
  by_cases j4 : j = 4
  · subst j4; simp only [reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceEqDiff]; rw [← hhx, re_toQ]
  by_cases j5 : j = 5
  · subst j5; simp only [reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceEqDiff]; rw [← hhx, im_toQ]
  by_cases j6 : j = 6
  · subst j6; simp only [reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceEqDiff]; rw [← hhp, re_toQ]
  by_cases j7 : j = 7
  · subst j7; simp only [reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceEqDiff]; rw [← hhp, im_toQ]
  have h8 : 8 ≤ j := by omega
  rw [if_neg j0, if_neg j1, if_neg j2, if_neg j3, if_neg j4, if_neg j5, if_neg j6, if_neg j7,
    if_neg (by omega : ¬ j < 4), if_neg (by omega : ¬ j < 6), if_neg (by omega : ¬ j < 8)]
  exact K3.toK_zero

end Main

#print axioms lastK6_scan
#print axioms toQ_last_sum
#print axioms toQ_xT
#print axioms toQ_pT
#print axioms toQ_hxT
#print axioms toQ_hpT
#print axioms walkGenRowsB_pubs

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkPubs
