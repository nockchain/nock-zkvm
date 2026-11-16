/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAWRunOK.lean

With `DA := j9aDataOf P Rg Rt hgen` and `DR := regV DA`, at the exec chip `I.V := (recJ9AX s f χe t r).V`:
  * `awOK_cast` (generic, `subst` only): transport of `AWChipOK` along `kr`, `n`, nodes, publics, trace;
  * `hinj_powN`: injective nodes of `I.V` give injective `powN o m` for `m = I.V.n`;
  * **`genJ9AX_aw_cols`** (present): `I.V.cols c i` is the honest column at `DR`;
  * `genJ9AX_aw_pubs_DR`: the publics at `DR`;
  * **`genJ9AX_aw_interp`** (present): `interpOf I.V j = trVOf9 … DR (mkOrbit I.V ho) (toχ χe) ⟨j, hj⟩`;
  * **`genJ9AX_aw_ok`** (both cases): `AWChipOK` of the exec chip at its own orbit.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWFam
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMemSat2
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCell
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRow

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
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.V1J8.Gen
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkOrd (krW_regroup)
open Nock.V1J9A Nock.V1J9A.GenJ9AX

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRunOK

/-! ## 1. Generic transport (`subst` only) -/

section Generic
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **`AWChipOK` transported** along `kr = kr'`, `n = m` (nodes related by `Fin.cast`), publics and trace
equalities. -/
theorem awOK_cast {kr kr' : ℕ} (ek : kr = kr') {n m : ℕ} (e : n = m) (hn : 0 < n) (hm : 0 < m)
    (ν : Fin n → ZMod p) (μ : Fin m → ZMod p) (hνμ : ∀ i : Fin n, ν i = μ (Fin.cast e i)) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (chals : ℕ → K) {pubs pubs' : ℕ → K} (hpb : pubs = pubs')
    {T T' : Fin 166 → (ZMod p)[X]} (hT : T = T')
    (H : AcceptsJ8V.AWChipOK δ b kr' hm μ o chals pubs'
      (fun j => T (Fin.cast (CellTwinK.walkChipHQK_width δ kr' b hm μ o chals pubs') j))) :
    AcceptsJ8V.AWChipOK δ b kr hn ν o chals pubs
      (fun j => T' (Fin.cast (CellTwinK.walkChipHQK_width δ kr b hn ν o chals pubs) j)) := by
  subst ek
  subst e
  obtain rfl : ν = μ := funext hνμ
  subst hpb
  subst hT
  exact H

end Generic

/-- Injective nodes of a chip give injective `powN` at any size `m = q.n`. -/
theorem hinj_powN (q : ChipIn) (ho : OrbOK q) (m : ℕ) (e : q.n = m)
    (hinj : Function.Injective (nodesOf q)) :
    Function.Injective (ComplJ8Of.powN (mkOrbit q ho) m) := by
  intro a b hab
  have h1 : nodesOf q (Fin.cast e.symm a) = nodesOf q (Fin.cast e.symm b) := by
    rw [GenPortJ9AHAtomRow.nodesOf_powN q ho]
    exact hab
  have h2 := hinj h1
  have h3 : ((Fin.cast e.symm a : Fin q.n) : ℕ) = ((Fin.cast e.symm b : Fin q.n) : ℕ) := congrArg Fin.val h2
  exact Fin.ext h3

theorem chipOf_cols (tbl : Array (Array (ZMod P))) (q : ChipIn) (hq : q = chipOf tbl) (c : ℕ) (i : Fin q.n) :
    q.cols c i = (tbl.getD i #[]).getD c 0 := by
  subst hq
  rfl

/-! ## 2. The atom walk at the run -/

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

/-- **Columns (present)**: the exec atom-walk column `c < 166` at row `i` is the honest column at `DR`. -/
theorem genJ9AX_aw_cols (χe : CoinsE) (hne : (DA).preads ≠ []) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (powN o (nVOf (DR))))
    (i : Fin (recJ9AX s f χe t r).V.n) (c : ℕ) (hc : c < 166) :
    (recJ9AX s f χe t r).V.cols c i =
      fullCol (nV_pos (DR))
        (WalkTraceHQ.colHQ deltaF (krVOf (DR)) powerBasis3 (vCol9 deltaF powerBasis3 (DR) (toχ χe))
          (kLV9 (DR)) (vLV9 (DR)) (kRV9 (DR)) (vRV9 (DR))
          (WalkTraceHQ.rolesF deltaF (krVOf (DR)) powerBasis3 (nV_pos (DR)) (powN o (nVOf (DR))) o
            (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) (pubsVOf9 deltaF powerBasis3 (DR) o (toχ χe))
            (vCol9 deltaF powerBasis3 (DR) (toχ χe)) (kLV9 (DR)) (vLV9 (DR)) (kRV9 (DR)) (vRV9 (DR)))) c
        (Fin.cast (genJ9AX_aw_n' Rt hgen hnc hax9 hwalkA χe) i) := by
  have hne' : (DR).preads ≠ [] := fun e => hne (regroup_eq_nil_iff.mp e)
  have key := GenPortJ9AHAW.walkGenRowsBE_cols χe (DR) (hwA_DR Rt hgen hnc hax9 hwalkA)
    (hsm_DR Rt hgen hnc hax9 hwalkA) (hcl_DR Rt hgen hnc hax9 hwalkA) hne' o hinj
    (Fin.cast (genJ9AX_aw_n' Rt hgen hnc hax9 hwalkA χe) i) c hc
  refine Eq.trans ?_ key
  have e1 : (recJ9AX s f χe t r).V.cols c i =
      (((vRPJ s f χe (RnOf t r)).1.getD (i : ℕ) #[]).getD c 0) := by
    exact chipOf_cols _ _ rfl c i
  refine e1.trans ?_
  rw [vRPJ_eq_awE Rt hgen hnc hax9 hwalkA χe hne]
  rfl

/-- **The publics at `DR`** (present), at any orbit with injective nodes. -/
theorem genJ9AX_aw_pubs_DR (χe : CoinsE) (hne : (DA).preads ≠ []) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (powN o (nVOf (DR)))) (j : ℕ) :
    K3.toK ((recJ9AX s f χe t r).M.pubsV j) = pubsVOf9 deltaF powerBasis3 (DR) o (toχ χe) j := by
  have hne' : (DR).preads ≠ [] := fun e => hne (regroup_eq_nil_iff.mp e)
  rw [recX_M_pubsV, vRPJ_eq_awE Rt hgen hnc hax9 hwalkA χe hne]
  exact GenPortJ9AHAWPubs.walkGenRowsBE_pubs χe (DR) (hwA_DR Rt hgen hnc hax9 hwalkA)
    (hsm_DR Rt hgen hnc hax9 hwalkA) (hcl_DR Rt hgen hnc hax9 hwalkA) hne' o hinj j

/-- **Interpolant (present)**: the exec column interpolants are the honest `trVOf9` at `DR`. -/
theorem genJ9AX_aw_interp (χe : CoinsE) (hne : (DA).preads ≠ [])
    (ho : OrbOK (recJ9AX s f χe t r).V) (hinj : Function.Injective (nodesOf (recJ9AX s f χe t r).V))
    (j : ℕ) (hj : j < 166) :
    interpOf (recJ9AX s f χe t r).V j =
      ComplJ9BBalF.trVOf9 deltaF powerBasis3 (DR) (mkOrbit (recJ9AX s f χe t r).V ho) (toχ χe) ⟨j, hj⟩ := by
  have hn := genJ9AX_aw_n' Rt hgen hnc hax9 hwalkA χe
  have hinj' := hinj_powN _ ho _ hn hinj
  unfold interpOf
  rw [GenPortJ9AHCell.interp_cast hn]
  have hnodes : nodesOf (recJ9AX s f χe t r).V ∘ Fin.cast hn.symm =
      powN (mkOrbit (recJ9AX s f χe t r).V ho) (nVOf (DR)) := by
    rw [GenPortJ9AHAtomRow.nodesOf_powN _ ho]
    rfl
  rw [hnodes]
  unfold trVOf9 WalkTraceHQ.walkTraceHQ honestQ
  refine congrArg (Lagrange.interpolate Finset.univ (powN (mkOrbit (recJ9AX s f χe t r).V ho) (nVOf (DR)))) ?_
  funext i'
  exact genJ9AX_aw_cols Rt hgen hnc hax9 hwalkA χe hne (mkOrbit (recJ9AX s f χe t r).V ho) hinj'
    (Fin.cast hn.symm i') j hj

/-- **`AWChipOK` of the exec atom walk** at its own orbit (present or absent). -/
theorem genJ9AX_aw_ok (χe : CoinsE) (ho : OrbOK (recJ9AX s f χe t r).V)
    (hinj : Function.Injective (nodesOf (recJ9AX s f χe t r).V))
    (hnV : 0 < (recJ9AX s f χe t r).V.n) (h31 : Rows31 (DA))
    (hgV : ∀ e ∈ famAWV9 deltaF (DA) (K := KC), toχ χe ∉ e.ev)
    (hgH : ∀ e ∈ famAWH9 deltaF (DA) (K := KC), toχ χe ∉ e.ev) :
    AcceptsJ8V.AWChipOK deltaF powerBasis3 (recJ9AX s f χe t r).krootsV hnV
      (nodesOf (recJ9AX s f χe t r).V) (mkOrbit (recJ9AX s f χe t r).V ho)
      (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
      (fun j => K3.toK ((recJ9AX s f χe t r).M.pubsV j))
      (fun j => interpOf (recJ9AX s f χe t r).V (j : ℕ)) := by
  by_cases h0 : (DA).preads = []
  · have hk : (recJ9AX s f χe t r).krootsV = 0 := by
      rw [genJ9AX_aw_krootsV Rt hgen hnc hax9 hwalkA χe]
      unfold krVOf
      rw [if_pos h0]
    have hz : ∀ j, K3.toK ((recJ9AX s f χe t r).M.pubsV j) = 0 := fun j => by
      rw [pubsV_absent Rt hgen hnc hax9 hwalkA χe h0]
      exact K3.toK_zero
    exact Or.inr ⟨hk, hz _, hz _, hz _, hz _, hz _, hz _⟩
  · have hall := hall_DA Rt hgen hnc hax9 hwalkA
    have hne' : (DR).preads ≠ [] := fun e => h0 (regroup_eq_nil_iff.mp e)
    have hn := genJ9AX_aw_n' Rt hgen hnc hax9 hwalkA χe
    have hk : (recJ9AX s f χe t r).krootsV = krVOf (DR) :=
      (genJ9AX_aw_krootsV Rt hgen hnc hax9 hwalkA χe).trans (krVOf_regV (DA) hall).symm
    have hinj' := hinj_powN _ ho _ hn hinj
    have hadj' : ∀ (i : Fin (nVOf (DR))) (hi : (i : ℕ) + 1 < nVOf (DR)),
        powN (mkOrbit (recJ9AX s f χe t r).V ho) (nVOf (DR)) ⟨(i : ℕ) + 1, hi⟩ =
          powN (mkOrbit (recJ9AX s f χe t r).V ho) (nVOf (DR)) i * (mkOrbit (recJ9AX s f χe t r).V ho).ω :=
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
    have H := GenPortJ9AHMemSat2.awOK_D9o deltaF powerBasis3 (DR) (mkOrbit (recJ9AX s f χe t r).V ho) hp63 h31'
      (walkDepthOK_regV (DA) (hwalk_DA Rt hgen hnc hax9 hwalkA)) (ComplJ9ADataRec.acsA_pos Rt hgen)
      hinj' hadj' (toχ χe) hgV' hgH'
    have hT : trVOf9 deltaF powerBasis3 (DR) (mkOrbit (recJ9AX s f χe t r).V ho) (toχ χe) =
        fun j : Fin 166 => interpOf (recJ9AX s f χe t r).V (j : ℕ) :=
      funext fun j => (genJ9AX_aw_interp Rt hgen hnc hax9 hwalkA χe h0 ho hinj j j.2).symm
    have hpb : (fun j => K3.toK ((recJ9AX s f χe t r).M.pubsV j)) =
        pubsVOf9 deltaF powerBasis3 (DR) (mkOrbit (recJ9AX s f χe t r).V ho) (toχ χe) :=
      funext fun j => genJ9AX_aw_pubs_DR Rt hgen hnc hax9 hwalkA χe h0 _ hinj' j
    refine awOK_cast (kr := (recJ9AX s f χe t r).krootsV) (kr' := krVOf (DR)) deltaF powerBasis3 hk hn hnV
      (nV_pos (DR)) (nodesOf (recJ9AX s f χe t r).V) (powN (mkOrbit (recJ9AX s f χe t r).V ho) (nVOf (DR))) ?_
      (mkOrbit (recJ9AX s f χe t r).V ho) (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) hpb
      (T := trVOf9 deltaF powerBasis3 (DR) (mkOrbit (recJ9AX s f χe t r).V ho) (toχ χe))
      (T' := fun j : Fin 166 => interpOf (recJ9AX s f χe t r).V (j : ℕ)) hT H
    intro i
    rw [GenPortJ9AHAtomRow.nodesOf_powN _ ho]
    rfl

end Run

#print axioms awOK_cast
#print axioms hinj_powN
#print axioms genJ9AX_aw_cols
#print axioms genJ9AX_aw_pubs_DR
#print axioms genJ9AX_aw_interp
#print axioms genJ9AX_aw_ok

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRunOK
