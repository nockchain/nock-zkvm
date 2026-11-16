/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAWE.lean

  **G1E-P4: the atom-walk chip over an abstract record `I : InJ9A`** (additive; no `hnc`).
  Twins of `GenPortJ9AHAWRun` (:205-298), `GenPortJ9AHAWRunOK` §2 and `GenPortJ9AHOrbAW`, with
  `recJ9AX s f χe t r` replaced by `I` and the `hnc` record lemmas replaced by the link hypotheses
  `hVon`, `hVoff`, `hkrV` (RHS of `vRPK_eq_awEJ`, `vRPK_absent`, `size_krootsV`).
  The DA-only helpers come from `GenPortJ9AHMsgJ` (`hallV_DAJ`, `hwA_DRJ`, `hcl_DRJ`, `hsm_DRJ`, `hwalkV_DAJ`).
  Extra hypothesis: `awE_at` takes `hχI : I.χ = χe`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRunOK
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWPubs
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWPub
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWOrd
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWFam
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRow
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCell
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsgJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfMem
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalFA

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option quotPrecheck false

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
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRunOK (awOK_cast hinj_powN chipOf_cols)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.V1J8.Gen
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkOrd (krW_regroup)
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE

section Run
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
  (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
include hax9 hwalkA

local notation "DA" => j9aDataOf P Rg Rt hgen
local notation "DR" => regV (j9aDataOf P Rg Rt hgen)
local notation "VonT[" χe "," I "]" =>
  ((j9aDataOf P Rg Rt hgen).preads ≠ [] →
    (I : InJ9A).V = chipOf (GenPortJ9AHAW.awE χe (regV (j9aDataOf P Rg Rt hgen))).1 ∧
      (I).M.pubsV = (GenPortJ9AHAW.awE χe (regV (j9aDataOf P Rg Rt hgen))).2)
local notation "VoffT[" I "]" =>
  ((j9aDataOf P Rg Rt hgen).preads = [] →
    (I : InJ9A).V = chipOf #[Array.replicate 166 0] ∧ (I).M.pubsV = fun _ => 0)
local notation "KrT[" I "]" => ((I : InJ9A).krootsV = ComplJ8Of.krVOf (j9aDataOf P Rg Rt hgen))

/-- **`awE_n'`**: the atom-walk chip has `nVOf DR` rows. -/
theorem awE_n' (χe : CoinsE) (I : InJ9A) (hVon : VonT[χe, I]) (hVoff : VoffT[I]) :
    I.V.n = nVOf (DR) := by
  by_cases h : (DA).preads = []
  · rw [(hVoff h).1]
    have h' : (DR).preads = [] := regroup_eq_nil_iff.mpr h
    unfold nVOf
    rw [if_pos h']
    rfl
  · have h' : (DR).preads ≠ [] := fun e => h (regroup_eq_nil_iff.mp e)
    rw [(hVon h).1]
    exact GenPortJ9AHAW.walkGenRowsBE_size χe (DR) h'

/-- **`awE_n`**: `nVOf DA` rows. -/
theorem awE_n (χe : CoinsE) (I : InJ9A) (hVon : VonT[χe, I]) (hVoff : VoffT[I]) :
    I.V.n = nVOf (DA) :=
  (awE_n' Rt hgen hax9 hwalkA χe I hVon hVoff).trans
    (nVOf_regV (DA) (GenPortJ9AHMsgJ.hallV_DAJ Rt hgen))

/-- **`awE_krootsV`**: the root count is `krVOf DA`. -/
theorem awE_krootsV (I : InJ9A) (hkrV : KrT[I]) : I.krootsV = krVOf (DA) := hkrV

/-- **`awE_pubs`**. -/
theorem awE_pubs (χe : CoinsE) (I : InJ9A) (hVon : VonT[χe, I]) (hVoff : VoffT[I])
    {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (powN o (nVOf (DA)))) (j : ℕ) :
    K3.toK (I.M.pubsV j) = pubsVOf9 deltaF powerBasis3 (DA) o (toχ χe) j := by
  by_cases h0 : (DA).preads = []
  · rw [(hVoff h0).2]
    show K3.toK 0 = _
    unfold pubsVOf9
    rw [if_pos h0, K3.toK_zero]
  · have h' : (DR).preads ≠ [] := fun e => h0 (regroup_eq_nil_iff.mp e)
    have hall := GenPortJ9AHMsgJ.hallV_DAJ Rt hgen
    have hinj' : Function.Injective (powN o (nVOf (DR))) := by
      rw [nVOf_regV (DA) hall]
      exact hinj
    rw [(hVon h0).2]
    rw [GenPortJ9AHAWPubs.walkGenRowsBE_pubs χe (DR) (GenPortJ9AHMsgJ.hwA_DRJ Rt hgen)
      (GenPortJ9AHMsgJ.hsm_DRJ Rt hgen) (GenPortJ9AHMsgJ.hcl_DRJ Rt hgen) h' o hinj' j]
    exact GenPortJ9AHAWPub.pubsVOf9_perm deltaF powerBasis3 (D := DA) (D' := DR) rfl rfl
      (regroup_eq_nil_iff) (walkRows_regV_perm (DA) hall) o o hinj hinj' (toχ χe) ▸ rfl

/-- **`awE_pubs_orb`**. -/
theorem awE_pubs_orb (χe : CoinsE) (I : InJ9A) (hVon : VonT[χe, I]) (hVoff : VoffT[I])
    (hF : DvdOK (DA)) (j : ℕ) :
    K3.toK (I.M.pubsV j) = pubsVOf9 deltaF powerBasis3 (DA) (orbJ8 (DA) hF) (toχ χe) j := by
  have hmem : nVOf (DA) ∈ sizesJ8 (DA) := by simp [sizesJ8]
  have hinj : Function.Injective (powN (orbJ8 (DA) hF) (nVOf (DA))) :=
    (powN_ok _ (le_two_pow_ht _ hmem)).1
  exact awE_pubs Rt hgen hax9 hwalkA χe I hVon hVoff (orbJ8 (DA) hF) hinj j

/-- **`awE_pubs_avOf9`**. -/
theorem awE_pubs_avOf9 (χe : CoinsE) (I : InJ9A) (hVon : VonT[χe, I]) (hVoff : VoffT[I])
    (hF : DvdOK (DA)) (AV : AVPart P KC) (j : ℕ) :
    K3.toK (I.M.pubsV j) = (avOf9 deltaF powerBasis3 (DA) hF AV).pubsV (toχ χe) j :=
  awE_pubs_orb Rt hgen hax9 hwalkA χe I hVon hVoff hF j

/-- **`awE_cols`** (present). -/
theorem awE_cols (χe : CoinsE) (I : InJ9A) (hVon : VonT[χe, I]) (hVoff : VoffT[I])
    (hne : (DA).preads ≠ []) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (powN o (nVOf (DR))))
    (i : Fin I.V.n) (c : ℕ) (hc : c < 166) :
    I.V.cols c i =
      fullCol (nV_pos (DR))
        (WalkTraceHQ.colHQ deltaF (krVOf (DR)) powerBasis3 (vCol9 deltaF powerBasis3 (DR) (toχ χe))
          (kLV9 (DR)) (vLV9 (DR)) (kRV9 (DR)) (vRV9 (DR))
          (WalkTraceHQ.rolesF deltaF (krVOf (DR)) powerBasis3 (nV_pos (DR)) (powN o (nVOf (DR))) o
            (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) (pubsVOf9 deltaF powerBasis3 (DR) o (toχ χe))
            (vCol9 deltaF powerBasis3 (DR) (toχ χe)) (kLV9 (DR)) (vLV9 (DR)) (kRV9 (DR)) (vRV9 (DR)))) c
        (Fin.cast (awE_n' Rt hgen hax9 hwalkA χe I hVon hVoff) i) := by
  have hne' : (DR).preads ≠ [] := fun e => hne (regroup_eq_nil_iff.mp e)
  have key := GenPortJ9AHAW.walkGenRowsBE_cols χe (DR) (GenPortJ9AHMsgJ.hwA_DRJ Rt hgen)
    (GenPortJ9AHMsgJ.hsm_DRJ Rt hgen) (GenPortJ9AHMsgJ.hcl_DRJ Rt hgen) hne' o hinj
    (Fin.cast (awE_n' Rt hgen hax9 hwalkA χe I hVon hVoff) i) c hc
  refine Eq.trans ?_ key
  have e1 : I.V.cols c i = (((GenPortJ9AHAW.awE χe (DR)).1.getD (i : ℕ) #[]).getD c 0) :=
    chipOf_cols _ _ (hVon hne).1 c i
  exact e1

/-- **`awE_pubs_DR`**. -/
theorem awE_pubs_DR (χe : CoinsE) (I : InJ9A) (hVon : VonT[χe, I])
    (hne : (DA).preads ≠ []) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (powN o (nVOf (DR)))) (j : ℕ) :
    K3.toK (I.M.pubsV j) = pubsVOf9 deltaF powerBasis3 (DR) o (toχ χe) j := by
  have hne' : (DR).preads ≠ [] := fun e => hne (regroup_eq_nil_iff.mp e)
  rw [(hVon hne).2]
  exact GenPortJ9AHAWPubs.walkGenRowsBE_pubs χe (DR) (GenPortJ9AHMsgJ.hwA_DRJ Rt hgen)
    (GenPortJ9AHMsgJ.hsm_DRJ Rt hgen) (GenPortJ9AHMsgJ.hcl_DRJ Rt hgen) hne' o hinj j

/-- **`awE_interp`** (present). -/
theorem awE_interp (χe : CoinsE) (I : InJ9A) (hVon : VonT[χe, I]) (hVoff : VoffT[I])
    (hne : (DA).preads ≠ [])
    (ho : OrbOK I.V) (hinj : Function.Injective (nodesOf I.V))
    (j : ℕ) (hj : j < 166) :
    interpOf I.V j =
      ComplJ9BBalF.trVOf9 deltaF powerBasis3 (DR) (mkOrbit I.V ho) (toχ χe) ⟨j, hj⟩ := by
  have hn := awE_n' Rt hgen hax9 hwalkA χe I hVon hVoff
  have hinj' := hinj_powN _ ho _ hn hinj
  unfold interpOf
  rw [GenPortJ9AHCell.interp_cast hn]
  have hnodes : nodesOf I.V ∘ Fin.cast hn.symm = powN (mkOrbit I.V ho) (nVOf (DR)) := by
    rw [GenPortJ9AHAtomRow.nodesOf_powN _ ho]
    rfl
  rw [hnodes]
  unfold trVOf9 WalkTraceHQ.walkTraceHQ honestQ
  refine congrArg (Lagrange.interpolate Finset.univ (powN (mkOrbit I.V ho) (nVOf (DR)))) ?_
  funext i'
  exact awE_cols Rt hgen hax9 hwalkA χe I hVon hVoff hne (mkOrbit I.V ho) hinj'
    (Fin.cast hn.symm i') j hj

/-- **`awE_ok`**: `AWChipOK` of the chip at its own orbit (present or absent). -/
theorem awE_ok (χe : CoinsE) (I : InJ9A) (hVon : VonT[χe, I]) (hVoff : VoffT[I]) (hkrV : KrT[I])
    (ho : OrbOK I.V) (hinj : Function.Injective (nodesOf I.V))
    (hnV : 0 < I.V.n) (h31 : Rows31 (DA))
    (hgV : ∀ e ∈ famAWV9 deltaF (DA) (K := KC), toχ χe ∉ e.ev)
    (hgH : ∀ e ∈ famAWH9 deltaF (DA) (K := KC), toχ χe ∉ e.ev) :
    AcceptsJ8V.AWChipOK deltaF powerBasis3 I.krootsV hnV
      (nodesOf I.V) (mkOrbit I.V ho)
      (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
      (fun j => K3.toK (I.M.pubsV j))
      (fun j => interpOf I.V (j : ℕ)) := by
  by_cases h0 : (DA).preads = []
  · have hk : I.krootsV = 0 := by
      rw [awE_krootsV Rt hgen hax9 hwalkA I hkrV]
      unfold krVOf
      rw [if_pos h0]
    have hz : ∀ j, K3.toK (I.M.pubsV j) = 0 := fun j => by
      rw [(hVoff h0).2]
      exact K3.toK_zero
    exact Or.inr ⟨hk, hz _, hz _, hz _, hz _, hz _, hz _⟩
  · have hall := GenPortJ9AHMsgJ.hallV_DAJ Rt hgen
    have hne' : (DR).preads ≠ [] := fun e => h0 (regroup_eq_nil_iff.mp e)
    have hn := awE_n' Rt hgen hax9 hwalkA χe I hVon hVoff
    have hk : I.krootsV = krVOf (DR) :=
      (awE_krootsV Rt hgen hax9 hwalkA I hkrV).trans (krVOf_regV (DA) hall).symm
    have hinj' := hinj_powN _ ho _ hn hinj
    have hadj' : ∀ (i : Fin (nVOf (DR))) (hi : (i : ℕ) + 1 < nVOf (DR)),
        powN (mkOrbit I.V ho) (nVOf (DR)) ⟨(i : ℕ) + 1, hi⟩ =
          powN (mkOrbit I.V ho) (nVOf (DR)) i * (mkOrbit I.V ho).ω :=
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
    have H := GenPortJ9AHMemSat2.awOK_D9o deltaF powerBasis3 (DR) (mkOrbit I.V ho) hp63 h31'
      (walkDepthOK_regV (DA) (GenPortJ9AHMsgJ.hwalkV_DAJ Rt hgen hax9 hwalkA))
      (ComplJ9ADataRec.acsA_pos Rt hgen) hinj' hadj' (toχ χe) hgV' hgH'
    have hT : trVOf9 deltaF powerBasis3 (DR) (mkOrbit I.V ho) (toχ χe) =
        fun j : Fin 166 => interpOf I.V (j : ℕ) :=
      funext fun j => (awE_interp Rt hgen hax9 hwalkA χe I hVon hVoff h0 ho hinj j j.2).symm
    have hpb : (fun j => K3.toK (I.M.pubsV j)) =
        pubsVOf9 deltaF powerBasis3 (DR) (mkOrbit I.V ho) (toχ χe) :=
      funext fun j => awE_pubs_DR Rt hgen hax9 hwalkA χe I hVon h0 _ hinj' j
    refine awOK_cast (kr := I.krootsV) (kr' := krVOf (DR)) deltaF powerBasis3 hk hn hnV
      (nV_pos (DR)) (nodesOf I.V) (powN (mkOrbit I.V ho) (nVOf (DR))) ?_
      (mkOrbit I.V ho) (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) hpb
      (T := trVOf9 deltaF powerBasis3 (DR) (mkOrbit I.V ho) (toχ χe))
      (T' := fun j : Fin 166 => interpOf I.V (j : ℕ)) hT H
    intro i
    rw [GenPortJ9AHAtomRow.nodesOf_powN _ ho]
    rfl

/-- **`awE_interp_at`**: interpolant at a re-oriented chip `q = reorb I.V O'`. -/
theorem awE_interp_at (χe : CoinsE) (I : InJ9A) (hVon : VonT[χe, I]) (hVoff : VoffT[I])
    (hne : (DA).preads ≠ []) (q : ChipIn) (O' : Orb)
    (hq : q = reorb I.V O')
    (ho : OrbOK q) (hinj : Function.Injective (nodesOf q)) (j : ℕ) (hj : j < 166) :
    interpOf q j =
      ComplJ9BBalF.trVOf9 deltaF powerBasis3 (DR) (mkOrbit q ho) (toχ χe) ⟨j, hj⟩ := by
  have hqn : q.n = I.V.n := by subst hq; rfl
  have hqc : ∀ (c : ℕ) (i : Fin q.n), q.cols c i = I.V.cols c (Fin.cast hqn i) := by
    subst hq; intro c i; rfl
  have hn : q.n = nVOf (DR) := hqn.trans (awE_n' Rt hgen hax9 hwalkA χe I hVon hVoff)
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
  have key := awE_cols Rt hgen hax9 hwalkA χe I hVon hVoff hne (mkOrbit q ho) hinj'
    (Fin.cast hqn (Fin.cast hn.symm i')) j hj
  refine (hqc _ _).trans ?_
  exact key

/-- **`awE_ok_at`**: `AWChipOK` at a re-oriented chip `q = reorb I.V O'`. -/
theorem awE_ok_at (χe : CoinsE) (I : InJ9A) (hVon : VonT[χe, I]) (hVoff : VoffT[I]) (hkrV : KrT[I])
    (q : ChipIn) (O' : Orb)
    (hq : q = reorb I.V O')
    (ho : OrbOK q) (hinj : Function.Injective (nodesOf q))
    (hnV : 0 < q.n) (h31 : Rows31 (DA))
    (hgV : ∀ e ∈ famAWV9 deltaF (DA) (K := KC), toχ χe ∉ e.ev)
    (hgH : ∀ e ∈ famAWH9 deltaF (DA) (K := KC), toχ χe ∉ e.ev) :
    AcceptsJ8V.AWChipOK deltaF powerBasis3 I.krootsV hnV
      (nodesOf q) (mkOrbit q ho)
      (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
      (fun j => K3.toK (I.M.pubsV j))
      (fun j => interpOf q (j : ℕ)) := by
  by_cases h0 : (DA).preads = []
  · have hk : I.krootsV = 0 := by
      rw [awE_krootsV Rt hgen hax9 hwalkA I hkrV]
      unfold krVOf
      rw [if_pos h0]
    have hz : ∀ j, K3.toK (I.M.pubsV j) = 0 := fun j => by
      rw [(hVoff h0).2]
      exact K3.toK_zero
    exact Or.inr ⟨hk, hz _, hz _, hz _, hz _, hz _, hz _⟩
  · have hqn : q.n = I.V.n := by subst hq; rfl
    have hall := GenPortJ9AHMsgJ.hallV_DAJ Rt hgen
    have hne' : (DR).preads ≠ [] := fun e => h0 (regroup_eq_nil_iff.mp e)
    have hn : q.n = nVOf (DR) := hqn.trans (awE_n' Rt hgen hax9 hwalkA χe I hVon hVoff)
    have hk : I.krootsV = krVOf (DR) :=
      (awE_krootsV Rt hgen hax9 hwalkA I hkrV).trans (krVOf_regV (DA) hall).symm
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
      (walkDepthOK_regV (DA) (GenPortJ9AHMsgJ.hwalkV_DAJ Rt hgen hax9 hwalkA))
      (ComplJ9ADataRec.acsA_pos Rt hgen) hinj' hadj' (toχ χe) hgV' hgH'
    have hT : trVOf9 deltaF powerBasis3 (DR) (mkOrbit q ho) (toχ χe) =
        fun j : Fin 166 => interpOf q (j : ℕ) :=
      funext fun j => (awE_interp_at Rt hgen hax9 hwalkA χe I hVon hVoff h0 q O' hq ho hinj j j.2).symm
    have hpb : (fun j => K3.toK (I.M.pubsV j)) =
        pubsVOf9 deltaF powerBasis3 (DR) (mkOrbit q ho) (toχ χe) :=
      funext fun j => awE_pubs_DR Rt hgen hax9 hwalkA χe I hVon h0 _ hinj' j
    refine awOK_cast (kr := I.krootsV) (kr' := krVOf (DR)) deltaF powerBasis3 hk hn hnV
      (nV_pos (DR)) (nodesOf q) (powN (mkOrbit q ho) (nVOf (DR))) ?_
      (mkOrbit q ho) (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) hpb
      (T := trVOf9 deltaF powerBasis3 (DR) (mkOrbit q ho) (toχ χe))
      (T' := fun j : Fin 166 => interpOf q (j : ℕ)) hT H
    intro i
    rw [GenPortJ9AHAtomRow.nodesOf_powN q ho]
    rfl

/-- **`awE_at`**: `hVk` of `AcceptsJ9A` at `withOrb I o` (conclusion = `OrbAW.aw_at`'s, at `I`).
Extra link hypothesis: `hχI : I.χ = χe`. -/
theorem awE_at (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (DA))
    (χe : CoinsE) (I : InJ9A) (hχI : I.χ = χe) (hVon : VonT[χe, I]) (hVoff : VoffT[I]) (hkrV : KrT[I])
    (o : OrbJ9A) (ho : OrbAdm I o)
    (hv' : ValidJ9A (withOrb I o))
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    AcceptsJ8V.AWChipOK deltaF powerBasis3 (mkPbA (withOrb I o) hv').krootsV
      (mkPbA (withOrb I o) hv').hnV
      (mkPbA (withOrb I o) hv').nodesV
      (mkPbA (withOrb I o) hv').orbitV
      (ChalsAZJ8.chalsAJ8Z deltaF (toχ (withOrb I o).χ))
      (withOrb I o).toMsg.pubsV
      (AcceptsJ8.qV deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8
        (ChalsAZJ8.chalsAJ8Z deltaF (toχ (withOrb I o).χ))
        (withOrb I o).toMsg.pubsV) := by
  have hgV : ∀ e ∈ famAWV9 deltaF (DA) (K := KC), toχ χe ∉ e.ev := fun e he =>
    ComplJ9AOfMem.goodJA deltaF powerBasis3 Rt hgen hpG h31A hχ (famAWV9 deltaF (DA) (K := KC))
      (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])) e he
  have hgH : ∀ e ∈ famAWH9 deltaF (DA) (K := KC), toχ χe ∉ e.ev := fun e he =>
    ComplJ9AOfMem.goodJA deltaF powerBasis3 Rt hgen hpG h31A hχ (famAWH9 deltaF (DA) (K := KC))
      (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9])) e he
  have h31 : Rows31 (DA) := ComplJ9ARun.h31_run Rt hgen h31A
  have hoV : OrbOK (reorb I.V o.V) := hv'.oV
  have hinj : Function.Injective (nodesOf (reorb I.V o.V)) :=
    (nodes_ok _ hoV ho.V.2).1
  have key := awE_ok_at Rt hgen hax9 hwalkA χe I hVon hVoff hkrV (reorb I.V o.V) o.V rfl hoV hinj
    hv'.nV h31 hgV hgH
  subst hχI
  exact key

end Run

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE in
#print axioms awE_n'
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE in
#print axioms awE_n
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE in
#print axioms awE_krootsV
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE in
#print axioms awE_pubs
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE in
#print axioms awE_pubs_orb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE in
#print axioms awE_pubs_avOf9
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE in
#print axioms awE_cols
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE in
#print axioms awE_pubs_DR
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE in
#print axioms awE_interp
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE in
#print axioms awE_ok
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE in
#print axioms awE_interp_at
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE in
#print axioms awE_ok_at
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWE in
#print axioms awE_at
