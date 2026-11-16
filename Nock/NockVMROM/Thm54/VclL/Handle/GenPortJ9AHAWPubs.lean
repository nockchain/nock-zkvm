/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAWPubs.lean

* `lastK6_scan`, `toQ_last_sum`: the last inclusive prefix sum is the full sum.
  * `toQ_xT / toQ_pT / toQ_hxT / toQ_hpT`: the four exec terminals map to `vxT9 / vpT9 / vhX9 / vhP9`.
  * `walkGenRowsBE_pubs`: `K3.toK ((awE χe D).2 j) = pubsVOf9 … j`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module Polynomial
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRowH
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW
open Nock.V1J8.Gen (P WRow WalkD walkDBE pTermD hPTermD scanK6 lastK6 walkGenRowsBE)

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWPubs

theorem lastK6_scan (l : List K6) :
    Nock.V1J8.Gen.lastK6 (Nock.V1J8.Gen.scanK6 l) = (Nock.V1J8.Gen.scanK6 l).getD (l.length - 1) 0 := by
  have hlen : (Nock.V1J8.Gen.scanK6 l).length = l.length := by
    simp [GenPortJ9AHCell.scanK6_eq']
  unfold Nock.V1J8.Gen.lastK6
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hlen]
  simp [List.getD_eq_getElem?_getD]

section Main
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))] [Fact (ringChar (ZMod P)).Prime]
  [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- The last inclusive prefix sum is the full sum. -/
theorem toQ_last_sum (l : List K6) (N : ℕ) (hl : l.length = N)
    (F : ℕ → Quad (algebraMap (ZMod P) KC deltaF))
    (hN : ∀ j < N, K6.toQ ((Nock.V1J8.Gen.scanK6 l).getD j 0) = ∑ k ∈ Finset.range (j + 1), F k) :
    K6.toQ (Nock.V1J8.Gen.lastK6 (Nock.V1J8.Gen.scanK6 l)) = ∑ k ∈ Finset.range N, F k := by
  by_cases h0 : N = 0
  · subst h0
    have : l = [] := List.length_eq_zero_iff.mp hl
    subst this
    have h1 : K6.toQ (Nock.V1J8.Gen.lastK6 (Nock.V1J8.Gen.scanK6 [])) = 0 := by
      simp [Nock.V1J8.Gen.lastK6, GenPortJ9AHCell.scanK6_eq', K6.toQ_zero]
    rw [h1, Finset.sum_range_zero]
  · rw [lastK6_scan, hl]
    have := hN (N - 1) (by omega)
    rw [show N - 1 + 1 = N by omega] at this
    exact this

theorem walkGenRowsBE_pubs_def (ptr : Noun → ℕ) (k : Co) (y : K6) (α γ : K3) (H : Noun → ℕ × ℕ)
    (rI : Noun → ℕ) (cert : ℕ → ℕ → ℕ) (cs : List Noun) (ws : List WRow) (kr : ℕ) (j : ℕ) :
    (walkGenRowsBE ptr k y α γ H rI cert cs ws kr).2 j =
      (let ds := dsL ptr k y H rI cs ws
       let xT := Nock.V1J8.Gen.lastK6 (Nock.V1J8.Gen.scanK6 (ds.map (·.xInv)))
       let pT := Nock.V1J8.Gen.lastK6 (Nock.V1J8.Gen.scanK6 (ds.map pTermD))
       let hxT := Nock.V1J8.Gen.lastK6 (Nock.V1J8.Gen.scanK6 (ds.map (·.hXi)))
       let hpT := Nock.V1J8.Gen.lastK6 (Nock.V1J8.Gen.scanK6 (ds.map hPTermD))
       if j = 0 then xT.re else if j = 1 then xT.im else if j = 2 then pT.re else if j = 3 then pT.im
       else if j = 4 then hxT.re else if j = 5 then hxT.im else if j = 6 then hpT.re
       else if j = 7 then hpT.im else 0) := by
  unfold walkGenRowsBE dsL
  rfl

variable (χe : CoinsE) (D : J8Data P Rg fuel s f r)
  (hwA : ∀ u ∈ walkRows D.acs D.preads, u.label.node ∈ D.acs)
  (hsm : ∀ y ∈ D.acs, GenPortJ9AHAtomRow.Small y)
  (hcl : ∀ y ∈ D.acs, y.isCell = true) (hne : D.preads ≠ [])
include hwA hsm hcl hne

theorem toQ_xT :
    K6.toQ (lastK6 (scanK6 ((dsE χe D).map (·.xInv)))) = vxT9 deltaF D (toχ χe) := by
  refine (toQ_last_sum _ (walkRows D.acs D.preads).length
    (by rw [List.length_map, dsE_length χe D])
    (fun k => K6.toQ (dW χe D k).xInv) ?_).trans ?_
  · intro j hj
    exact scan_sum χe D hwA hsm hcl hne (fun d => d.xInv) j hj
  · unfold vxT9
    rw [nVOf_eq D hne]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < (walkRows D.acs D.preads).length := Finset.mem_range.mp hk
    rw [vR9_eq, vRow9_eq]
    exact toQ_xInv χe D _ k hwA hsm (wTrie_mem D.acs D.preads hk') hcl (α0 χe) (γ0 χe) rfl

theorem toQ_pT :
    K6.toQ (lastK6 (scanK6 ((dsE χe D).map pTermD))) = vpT9 deltaF D (toχ χe) := by
  refine (toQ_last_sum _ (walkRows D.acs D.preads).length
    (by rw [List.length_map, dsE_length χe D])
    (fun k => K6.toQ (pTermD (dW χe D k))) ?_).trans ?_
  · intro j hj
    exact scan_sum χe D hwA hsm hcl hne pTermD j hj
  · unfold vpT9
    rw [nVOf_eq D hne]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < (walkRows D.acs D.preads).length := Finset.mem_range.mp hk
    rw [vR9_eq, vRow9_eq]
    unfold pTermD
    rw [K6.toQ_add, K6.toQ_mul, K6.toQ_mul, FillMem.toQ_lq, FillMem.toQ_lq,
      toQ_pInvL χe D _ k hwA hsm (wTrie_mem D.acs D.preads hk') (α0 χe) (γ0 χe) rfl,
      toQ_pInvR χe D _ k hwA hsm (wTrie_mem D.acs D.preads hk') (α0 χe) (γ0 χe) rfl, dW_w χe D k]
    rfl

omit hwA hsm hcl in
theorem vdN9_eq_dRow {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (l : List (Nock.NockVMROM.Thm54.CoordinateCompiler.CoeffExpr (ZMod P))) (k : ℕ)
    (hkV : k < nVOf D) :
    vdN9 deltaF powerBasis3 D o (toχ χe) l k =
      WalkTraceHQ.dRow deltaF (krW D.acs D.preads) powerBasis3 (nV_pos D) (powN o _) o
        (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) (pubsV09 deltaF D (toχ χe)) l
        (vCol9 deltaF powerBasis3 D (toχ χe)) (kLV9 D) (vLV9 D) (kRV9 D) (vRV9 D) ⟨k, hkV⟩ := by
  simp only [vdN9, WalkTraceHQ.dN, dif_pos hkV, krVOf_eq D hne]

theorem toQ_hxT {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (powN o (nVOf D))) :
    K6.toQ (lastK6 (scanK6 ((dsE χe D).map (·.hXi)))) = vhX9 deltaF powerBasis3 D o (toχ χe) := by
  refine (toQ_last_sum _ (walkRows D.acs D.preads).length
    (by rw [List.length_map, dsE_length χe D])
    (fun k => K6.toQ (dW χe D k).hXi) ?_).trans ?_
  · intro j hj
    exact scan_sum χe D hwA hsm hcl hne (fun d => d.hXi) j hj
  · unfold vhX9
    refine Finset.sum_congr (by rw [nVOf_eq D hne]) fun k hk => ?_
    have hkV : k < nVOf D := Finset.mem_range.mp hk
    rw [hXi_eq χe D hwA hsm hcl hne o hinj k hkV, vdN9_eq_dRow χe D hne o _ k hkV]
    simp only [rolesH, WalkTraceHQ.rolesF]
    rw [(aw_dRow_split9 deltaF powerBasis3 D o hinj (toχ χe) (pubsVOf9 deltaF powerBasis3 D o (toχ χe))
        ⟨k, hkV⟩).1,
      (aw_dRow_split9 deltaF powerBasis3 D o hinj (toχ χe) (pubsV09 deltaF D (toχ χe)) ⟨k, hkV⟩).1]

theorem toQ_hpT {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (powN o (nVOf D))) :
    K6.toQ (lastK6 (scanK6 ((dsE χe D).map hPTermD))) = vhP9 deltaF powerBasis3 D o (toχ χe) := by
  refine (toQ_last_sum _ (walkRows D.acs D.preads).length
    (by rw [List.length_map, dsE_length χe D])
    (fun k => K6.toQ (hPTermD (dW χe D k))) ?_).trans ?_
  · intro j hj
    exact scan_sum χe D hwA hsm hcl hne hPTermD j hj
  · unfold vhP9
    refine Finset.sum_congr (by rw [nVOf_eq D hne]) fun k hk => ?_
    have hkV : k < nVOf D := Finset.mem_range.mp hk
    have mL := cN_mL χe D hwA hsm hcl k hkV
    have mR := cN_mR χe D hwA hsm hcl k hkV
    unfold hPTermD
    rw [K6.toQ_add, K6.toQ_mul, K6.toQ_mul, FillMem.toQ_lq, FillMem.toQ_lq,
      hPLi_eq χe D hwA hsm hcl hne o hinj k hkV, hPRi_eq χe D hwA hsm hcl hne o hinj k hkV]
    rw [vdN9_eq_dRow χe D hne o WalkHC.recLH k hkV, vdN9_eq_dRow χe D hne o WalkHC.recRH k hkV, mL, mR]
    simp only [rolesH, WalkTraceHQ.rolesF]
    have s1 := fun pubs => aw_dRow_split9 deltaF powerBasis3 D o hinj (toχ χe) pubs ⟨k, hkV⟩
    rw [(s1 (pubsVOf9 deltaF powerBasis3 D o (toχ χe))).2.1, (s1 (pubsVOf9 deltaF powerBasis3 D o (toχ χe))).2.2,
      (s1 (pubsV09 deltaF D (toχ χe))).2.1, (s1 (pubsV09 deltaF D (toχ χe))).2.2, dW_w χe D k]
    rfl

/-- **The exec atom-walk table's publics are the honest J-9 atom walk's.** -/
theorem walkGenRowsBE_pubs {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (powN o (nVOf D))) (j : ℕ) :
    K3.toK ((awE χe D).2 j) = pubsVOf9 deltaF powerBasis3 D o (toχ χe) j := by
  have hx := toQ_xT χe D hwA hsm hcl hne
  have hp := toQ_pT χe D hwA hsm hcl hne
  have hhx := toQ_hxT χe D hwA hsm hcl hne o hinj
  have hhp := toQ_hpT χe D hwA hsm hcl hne o hinj
  unfold awE
  rw [walkGenRowsBE_pubs_def]
  dsimp only
  generalize lastK6 (scanK6 ((dsE χe D).map (·.xInv))) = xT at hx ⊢
  generalize lastK6 (scanK6 ((dsE χe D).map pTermD)) = pT at hp ⊢
  generalize lastK6 (scanK6 ((dsE χe D).map (·.hXi))) = hxT at hhx ⊢
  generalize lastK6 (scanK6 ((dsE χe D).map hPTermD)) = hpT at hhp ⊢
  simp only [pubsVOf9, pubsV09, ComplJ8Of.pub2, if_neg hne]
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
#print axioms walkGenRowsBE_pubs

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWPubs
