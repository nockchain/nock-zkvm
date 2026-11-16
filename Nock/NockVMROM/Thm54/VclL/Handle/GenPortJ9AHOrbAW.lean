/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHOrbAW.lean

* `aw_interp_at` : `genJ9AX_aw_interp` at a generic chip `q = reorb I.V O'` (injective nodes);
  * `aw_ok_at`     : `genJ9AX_aw_ok` at the same generic chip `q`;
  * `aw_pubs_B`    : the exec atom-walk publics are `BRun9A`'s `pubsV` (`genJ9AX_aw_pubs_orb`);
  * `aw_at`        : `hVk` at `mkPbA (withOrb I o) hv'`, `I'.toMsg`, `I'.toTr`, coin `toχ I'.χ`.
  Never compares `mkPbA` with `B.Pb`.  The honest side is used only through `B.Good`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRunOK
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipCast
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfMem

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module Polynomial
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRun
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRunOK
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.V1J8.Gen
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkOrd (krW_regroup)
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbAW

section Run
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hnc : Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t) = [])
  (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
  (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
include hnc hax9 hwalkA

local notation "DA" => j9aDataOf P Rg Rt hgen
local notation "DR" => regV (j9aDataOf P Rg Rt hgen)

/-- **Interpolant at a re-oriented chip** `q = reorb I.V O'`, any injective nodes. -/
theorem aw_interp_at (χe : CoinsE) (hne : (DA).preads ≠ []) (q : ChipIn) (O' : Orb)
    (hq : q = reorb (recJ9AX s f χe t r).V O')
    (ho : OrbOK q) (hinj : Function.Injective (nodesOf q)) (j : ℕ) (hj : j < 166) :
    interpOf q j =
      ComplJ9BBalF.trVOf9 deltaF powerBasis3 (DR) (mkOrbit q ho) (toχ χe) ⟨j, hj⟩ := by
  have hqn : q.n = (recJ9AX s f χe t r).V.n := by subst hq; rfl
  have hqc : ∀ (c : ℕ) (i : Fin q.n),
      q.cols c i = (recJ9AX s f χe t r).V.cols c (Fin.cast hqn i) := by
    subst hq; intro c i; rfl
  have hn : q.n = nVOf (DR) := hqn.trans (genJ9AX_aw_n' Rt hgen hnc hax9 hwalkA χe)
  have hinj' := hinj_powN q ho _ hn hinj
  unfold interpOf
  rw [GenPortJ9AHCell.interp_cast hn]
  have hnodes : nodesOf q ∘ Fin.cast hn.symm = powN (mkOrbit q ho) (nVOf (DR)) := by
    rw [GenPortJ9AHAtomRow.nodesOf_powN q ho]
    rfl
  rw [hnodes]
  unfold trVOf9 WalkTraceHQ.walkTraceHQ honestQ
  refine congrArg (Lagrange.interpolate Finset.univ (powN (mkOrbit q ho) (nVOf (DR)))) ?_
  funext i'
  have key := genJ9AX_aw_cols Rt hgen hnc hax9 hwalkA χe hne (mkOrbit q ho) hinj'
    (Fin.cast hqn (Fin.cast hn.symm i')) j hj
  refine (hqc _ _).trans ?_
  exact key

/-- **`AWChipOK` at a re-oriented chip** `q = reorb I.V O'` (present or absent). -/
theorem aw_ok_at (χe : CoinsE) (q : ChipIn) (O' : Orb)
    (hq : q = reorb (recJ9AX s f χe t r).V O')
    (ho : OrbOK q) (hinj : Function.Injective (nodesOf q))
    (hnV : 0 < q.n) (h31 : Rows31 (DA))
    (hgV : ∀ e ∈ famAWV9 deltaF (DA) (K := KC), toχ χe ∉ e.ev)
    (hgH : ∀ e ∈ famAWH9 deltaF (DA) (K := KC), toχ χe ∉ e.ev) :
    AcceptsJ8V.AWChipOK deltaF powerBasis3 (recJ9AX s f χe t r).krootsV hnV
      (nodesOf q) (mkOrbit q ho)
      (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
      (fun j => K3.toK ((recJ9AX s f χe t r).M.pubsV j))
      (fun j => interpOf q (j : ℕ)) := by
  by_cases h0 : (DA).preads = []
  · have hk : (recJ9AX s f χe t r).krootsV = 0 := by
      rw [genJ9AX_aw_krootsV Rt hgen hnc hax9 hwalkA χe]
      unfold krVOf
      rw [if_pos h0]
    have hz : ∀ j, K3.toK ((recJ9AX s f χe t r).M.pubsV j) = 0 := fun j => by
      rw [pubsV_absent Rt hgen hnc hax9 hwalkA χe h0]
      exact K3.toK_zero
    exact Or.inr ⟨hk, hz _, hz _, hz _, hz _, hz _, hz _⟩
  · have hqn : q.n = (recJ9AX s f χe t r).V.n := by subst hq; rfl
    have hall := hall_DA Rt hgen hnc hax9 hwalkA
    have hne' : (DR).preads ≠ [] := fun e => h0 (regroup_eq_nil_iff.mp e)
    have hn : q.n = nVOf (DR) := hqn.trans (genJ9AX_aw_n' Rt hgen hnc hax9 hwalkA χe)
    have hk : (recJ9AX s f χe t r).krootsV = krVOf (DR) :=
      (genJ9AX_aw_krootsV Rt hgen hnc hax9 hwalkA χe).trans (krVOf_regV (DA) hall).symm
    have hinj' := hinj_powN q ho _ hn hinj
    have hadj' : ∀ (i : Fin (nVOf (DR))) (hi : (i : ℕ) + 1 < nVOf (DR)),
        powN (mkOrbit q ho) (nVOf (DR)) ⟨(i : ℕ) + 1, hi⟩ =
          powN (mkOrbit q ho) (nVOf (DR)) i * (mkOrbit q ho).ω :=
      fun i hi => pow_succ _ _
    have h31' : ∀ x ∈ sizesJ8 (DR), x ≤ 2 ^ 31 := by
      rw [sizesJ8_regV (DA) hall]
      exact h31
    have hp63 : 2 ^ 63 < P := by
      show 2 ^ 63 < Nock.Field.p
      norm_num [Nock.Field.p]
    have hperm := walkRows_regV_perm (DA) hall
    have hgV' : ∀ e ∈ famAWV9 deltaF (DR) (K := KC), toχ χe ∉ e.ev :=
      GenPortJ9AHAWFam.famAWV9_good_of_perm deltaF (DA) (DR) rfl regroup_eq_nil_iff hperm _ hgV
    have hgH' : ∀ e ∈ famAWH9 deltaF (DR) (K := KC), toχ χe ∉ e.ev :=
      GenPortJ9AHAWFam.famAWH9_good_of_perm deltaF (DA) (DR) rfl rfl regroup_eq_nil_iff hperm _ hgH
    have H := GenPortJ9AHMemSat2.awOK_D9o deltaF powerBasis3 (DR) (mkOrbit q ho) hp63 h31'
      (walkDepthOK_regV (DA) (hwalk_DA Rt hgen hnc hax9 hwalkA)) (ComplJ9ADataRec.acsA_pos Rt hgen)
      hinj' hadj' (toχ χe) hgV' hgH'
    have hT : trVOf9 deltaF powerBasis3 (DR) (mkOrbit q ho) (toχ χe) =
        fun j : Fin 166 => interpOf q (j : ℕ) :=
      funext fun j => (aw_interp_at Rt hgen hnc hax9 hwalkA χe h0 q O' hq ho hinj j j.2).symm
    have hpb : (fun j => K3.toK ((recJ9AX s f χe t r).M.pubsV j)) =
        pubsVOf9 deltaF powerBasis3 (DR) (mkOrbit q ho) (toχ χe) :=
      funext fun j => genJ9AX_aw_pubs_DR Rt hgen hnc hax9 hwalkA χe h0 _ hinj' j
    refine awOK_cast (kr := (recJ9AX s f χe t r).krootsV) (kr' := krVOf (DR)) deltaF powerBasis3 hk hn hnV
      (nV_pos (DR)) (nodesOf q) (powN (mkOrbit q ho) (nVOf (DR))) ?_
      (mkOrbit q ho) (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) hpb
      (T := trVOf9 deltaF powerBasis3 (DR) (mkOrbit q ho) (toχ χe))
      (T' := fun j : Fin 166 => interpOf q (j : ℕ)) hT H
    intro i
    rw [GenPortJ9AHAtomRow.nodesOf_powN q ho]
    rfl

/-- **The exec atom-walk publics are the honest record's** `((BRun9A …).M (toχ χe)).pubsV` (`rfl`-shaped). -/
theorem aw_pubs_B (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (DA)) (χe : CoinsE) (j : ℕ) :
    K3.toK ((recJ9AX s f χe t r).M.pubsV j) =
      ((ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).M (toχ χe)).pubsV j :=
  (genJ9AX_aw_pubs_orb Rt hgen hnc hax9 hwalkA χe (ComplJ9ARun.hF_run Rt hgen hpG h31A) j).trans rfl

/-- **`hVk` of `AcceptsJ9A` at `withOrb I o`.** -/
theorem aw_at (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (DA))
    (χe : CoinsE) (o : OrbJ9A) (ho : OrbAdm (recJ9AX s f χe t r) o)
    (hv' : ValidJ9A (withOrb (recJ9AX s f χe t r) o))
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    AcceptsJ8V.AWChipOK deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').krootsV
      (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').hnV
      (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nodesV
      (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').orbitV
      (ChalsAZJ8.chalsAJ8Z deltaF (toχ (withOrb (recJ9AX s f χe t r) o).χ))
      (withOrb (recJ9AX s f χe t r) o).toMsg.pubsV
      (AcceptsJ8.qV deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').toPubJ8
        (withOrb (recJ9AX s f χe t r) o).toTr.toJ8
        (ChalsAZJ8.chalsAJ8Z deltaF (toχ (withOrb (recJ9AX s f χe t r) o).χ))
        (withOrb (recJ9AX s f χe t r) o).toMsg.pubsV) := by
  have hgV : ∀ e ∈ famAWV9 deltaF (DA) (K := KC), toχ χe ∉ e.ev := fun e he =>
    ComplJ9AOfMem.goodJA deltaF powerBasis3 Rt hgen hpG h31A hχ (famAWV9 deltaF (DA) (K := KC))
      (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])) e he
  have hgH : ∀ e ∈ famAWH9 deltaF (DA) (K := KC), toχ χe ∉ e.ev := fun e he =>
    ComplJ9AOfMem.goodJA deltaF powerBasis3 Rt hgen hpG h31A hχ (famAWH9 deltaF (DA) (K := KC))
      (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])) e he
  have h31 : Rows31 (DA) := ComplJ9ARun.h31_run Rt hgen h31A
  have hoV : OrbOK (reorb (recJ9AX s f χe t r).V o.V) := hv'.oV
  have hinj : Function.Injective (nodesOf (reorb (recJ9AX s f χe t r).V o.V)) :=
    (nodes_ok _ hoV ho.V.2).1
  exact aw_ok_at Rt hgen hnc hax9 hwalkA χe (reorb (recJ9AX s f χe t r).V o.V) o.V rfl hoV hinj
    hv'.nV h31 hgV hgH

end Run

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbAW

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbAW in
#print axioms aw_interp_at
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbAW in
#print axioms aw_ok_at
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbAW in
#print axioms aw_pubs_B
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbAW in
#print axioms aw_at
