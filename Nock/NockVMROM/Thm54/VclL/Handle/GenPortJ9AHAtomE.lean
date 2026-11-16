/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAtomE.lean

  **The atom chip over an abstract record `I : InJ9A`** (no `hnc`). Twins of `GenPortJ9AHAtomRun` (:110-202) and `GenPortJ9AHOrbAtom.atom_interp_at` / `atom_at`, with the record
  facts replaced by the two hypotheses `hAc : I.A = chipOf (atomGenE …).1`, `hpA : I.M.pubsA = (atomGenE …).2`
  (RHS verbatim from `GenPortJ9AHMsgJ.aRPK_eqJ`). -/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbAtom
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtom
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomCols1
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomCols2
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMemSat2
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipCast
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ATables
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfMem

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomCols2
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtom
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf acsA_pos)
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (qA)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L (qAL)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomE

section Run
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [instFR : Fact (ringChar (ZMod P)).Prime] [instAR : Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DA" => ComplJ9ADataRec.j9aDataOf P Rg Rt hgen
local notation "DD" => ComplJ8Data.j8DataOf P Rg Rt hgen

theorem atomE_n (χe : CoinsE) (I : InJ9A)
    (hAc : I.A = chipOf (atomGenE (ComplJ8Data.ptrP P (DA).acs (DA).rows) χe (DA).acs (DA).info (DA).mb (DA).mxA (DA).mhA).1) :
    I.A.n = (DA).acs.length := by
  rw [hAc]
  exact atomGenE_size (ComplJ8Data.ptrP P (DA).acs (DA).rows) χe (DA).acs (DA).info (DA).mb (DA).mxA (DA).mhA

noncomputable abbrev colAF (hA : 0 < (DA).acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h) (χe : CoinsE) :
    ℕ → Fin (DA).acs.length → ZMod P :=
  GenPortJ9AHAtomRun.colAF Rt hgen hA o χe

theorem atomE_cols (χe : CoinsE) (I : InJ9A)
    (hAc : I.A = chipOf (atomGenE (ComplJ8Data.ptrP P (DA).acs (DA).rows) χe (DA).acs (DA).info (DA).mb (DA).mxA (DA).mhA).1)
    (hN : (DD).rows.size ≤ 2 ^ 31) (hA : 0 < (DA).acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (DA).acs.length))
    (i : Fin I.A.n) (c : ℕ) (hc : c < 349) :
    I.A.cols c i = colAF Rt hgen hA o χe c (Fin.cast (atomE_n Rt hgen χe I hAc) i) := by
  have hacs : (DA).acs = ComplJ8Data.acsP P (DA).bigs (DA).dupP := rfl
  have hinfo : (DA).info = ComplJ8Data.infoOfP P (DA).acs (DA).rows := rfl
  have hg : ComplJ8Atom.GenHyp (DA).bigs (DA).dupP (DA).rows (DA).mb := ComplJ9ATables.genHyp_mbXA Rg Rt hgen hN
  have key := atomGenE_cols (DA) hacs hinfo hg χe hA o hinj (Fin.cast (atomE_n Rt hgen χe I hAc) i) c hc
  refine Eq.trans ?_ key
  exact GenPortJ9AHAtomRun.chipOf_cols _ _ hAc c i

theorem atomE_pubs (χe : CoinsE) (I : InJ9A)
    (hAc : I.A = chipOf (atomGenE (ComplJ8Data.ptrP P (DA).acs (DA).rows) χe (DA).acs (DA).info (DA).mb (DA).mxA (DA).mhA).1)
    (hpA : I.M.pubsA = (atomGenE (ComplJ8Data.ptrP P (DA).acs (DA).rows) χe (DA).acs (DA).info (DA).mb (DA).mxA (DA).mhA).2)
    (hN : (DD).rows.size ≤ 2 ^ 31) (hA : 0 < (DA).acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (DA).acs.length)) (j : ℕ) :
    K3.toK (I.M.pubsA j) = ComplJ8Of.pubsAOf deltaF powerBasis3 (DA) hA o (toχ χe) j := by
  have hacs : (DA).acs = ComplJ8Data.acsP P (DA).bigs (DA).dupP := rfl
  have hinfo : (DA).info = ComplJ8Data.infoOfP P (DA).acs (DA).rows := rfl
  have hg : ComplJ8Atom.GenHyp (DA).bigs (DA).dupP (DA).rows (DA).mb := ComplJ9ATables.genHyp_mbXA Rg Rt hgen hN
  rw [hpA]
  exact atomGenE_pubs (DA) hacs hinfo hg χe hA o hinj j

theorem atomE_interp (χe : CoinsE) (I : InJ9A)
    (hAc : I.A = chipOf (atomGenE (ComplJ8Data.ptrP P (DA).acs (DA).rows) χe (DA).acs (DA).info (DA).mb (DA).mxA (DA).mhA).1)
    (hN : (DD).rows.size ≤ 2 ^ 31) (hA : 0 < (DA).acs.length)
    (q : ChipIn) (hqn : q.n = I.A.n)
    (hqc : ∀ c i, q.cols c i = I.A.cols c (Fin.cast hqn i))
    (ho : OrbOK q) (hinj : Function.Injective (nodesOf q)) (j : ℕ) (hj : j < 349) :
    interpOf q j = ComplJ8Of.trAOf deltaF powerBasis3 (DA) hA (mkOrbit q ho) (toχ χe) ⟨j, hj⟩ := by
  have e : q.n = (DA).acs.length := hqn.trans (atomE_n Rt hgen χe I hAc)
  have hinj' : Function.Injective (ComplJ8Of.powN (mkOrbit q ho) (DA).acs.length) := by
    intro a b hab
    have h1 : nodesOf q (Fin.cast e.symm a) = nodesOf q (Fin.cast e.symm b) := by
      rw [nodesOf_powN q ho]
      exact hab
    have h2 := hinj h1
    have h3 : ((Fin.cast e.symm a : Fin q.n) : ℕ) = ((Fin.cast e.symm b : Fin q.n) : ℕ) := congrArg Fin.val h2
    exact Fin.ext h3
  obtain ⟨gG, hgG⟩ : ∃ g : Fin (DA).acs.length → ZMod P, g = colAF Rt hgen hA (mkOrbit q ho) χe j :=
    ⟨_, rfl⟩
  have hcols : ∀ i : Fin q.n, q.cols j i = gG (Fin.cast e i) := by
    intro i
    rw [hqc, hgG]
    exact atomE_cols Rt hgen χe I hAc hN hA (mkOrbit q ho) hinj' (Fin.cast hqn i) j hj
  have hn : nodesOf q = fun i : Fin q.n => ComplJ8Of.powN (mkOrbit q ho) (DA).acs.length (Fin.cast e i) :=
    funext fun i => (congrFun (nodesOf_powN q ho) i).trans rfl
  show Lagrange.interpolate Finset.univ (nodesOf q) (fun i => q.cols j i) = _
  rw [hn, show (fun i => q.cols j i) = fun i : Fin q.n => gG (Fin.cast e i) from funext hcols]
  refine (interp_cast e (ComplJ8Of.powN (mkOrbit q ho) (DA).acs.length) gG).trans ?_
  subst hgG
  rfl

include hgen

theorem atomE_interp_at (χe : CoinsE) (I : InJ9A)
    (hAc : I.A = chipOf (atomGenE (ComplJ8Data.ptrP P (DA).acs (DA).rows) χe (DA).acs (DA).info (DA).mb (DA).mxA (DA).mhA).1)
    (hN : (ComplJ8Data.j8DataOf P Rg Rt hgen).rows.size ≤ 2 ^ 31)
    (hA : 0 < (j9aDataOf P Rg Rt hgen).acs.length)
    (O' : Orb) (q : ChipIn) (hq : q = reorb I.A O')
    (ho : OrbOK q) (hinj : Function.Injective (nodesOf q)) (j : ℕ) (hj : j < 349) :
    interpOf q j = ComplJ8Of.trAOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hA (mkOrbit q ho) (toχ χe)
      ⟨j, hj⟩ := by
  subst hq
  exact atomE_interp Rt hgen χe I hAc hN hA (reorb I.A O') rfl (fun _ _ => rfl) ho hinj j hj

/-- **`(hsatA ∧ hbindA) ∧ (hsatL ∧ hbindL)` of `AcceptsJ9A` at `withOrb I o`.** -/
theorem atomE_at (hpG : P = Nock.Atoms.p)
    (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (χe : CoinsE) (I : InJ9A)
    (hAc : I.A = chipOf (atomGenE (ComplJ8Data.ptrP P (DA).acs (DA).rows) χe (DA).acs (DA).info (DA).mb (DA).mxA (DA).mhA).1)
    (hpA : I.M.pubsA = (atomGenE (ComplJ8Data.ptrP P (DA).acs (DA).rows) χe (DA).acs (DA).info (DA).mb (DA).mxA (DA).mhA).2)
    (o : OrbJ9A) (ho : OrbAdm I o)
    (hv' : ValidJ9A (withOrb I o))
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    ((AtomChipHQ.atomChipHQ deltaF powerBasis3 (mkPbA (withOrb I o) hv').hnA
        (mkPbA (withOrb I o) hv').nodesA (mkPbA (withOrb I o) hv').orbitA
        (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) (withOrb I o).toMsg.pubsA).rap.Satisfies
      (qA deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
        (withOrb I o).toMsg.pubsA) ∧
    (AtomChipHQ.atomChipHQ deltaF powerBasis3 (mkPbA (withOrb I o) hv').hnA
        (mkPbA (withOrb I o) hv').nodesA (mkPbA (withOrb I o) hv').orbitA
        (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) (withOrb I o).toMsg.pubsA).BindsPreprocessing
      (qA deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
        (withOrb I o).toMsg.pubsA)) ∧
    ((AtomChipHQL.atomChipHQL deltaF powerBasis3 (mkPbA (withOrb I o) hv').hnA
        (mkPbA (withOrb I o) hv').nodesA (mkPbA (withOrb I o) hv').orbitA
        (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) (withOrb I o).toMsg.pubsA).rap.Satisfies
      (qAL deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
        (withOrb I o).toMsg.pubsA) ∧
    (AtomChipHQL.atomChipHQL deltaF powerBasis3 (mkPbA (withOrb I o) hv').hnA
        (mkPbA (withOrb I o) hv').nodesA (mkPbA (withOrb I o) hv').orbitA
        (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) (withOrb I o).toMsg.pubsA).BindsPreprocessing
      (qAL deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
        (withOrb I o).toMsg.pubsA)) := by
  have hn := atomE_n Rt hgen χe I hAc
  have hA : 0 < (j9aDataOf P Rg Rt hgen).acs.length := acsA_pos Rt hgen
  have hN := GenPortJ9AHOrbAtom.rows_leP Rt hgen h31A
  have hoA : OrbOK (reorb I.A o.A) := hv'.oA
  have hinj0 : Function.Injective (nodesOf (reorb I.A o.A)) :=
    GenPortJ9AHOrb.nodesOf_inj _ hoA ho.A.2
  have hnodes : nodesOf (reorb I.A o.A) =
      ComplJ8Of.powN (mkOrbit (reorb I.A o.A) hoA) I.A.n :=
    GenPortJ9AHOrbA.nodesOf_powN _ hoA
  have hpow : ComplJ8Of.powN (mkOrbit (reorb I.A o.A) hoA)
        (j9aDataOf P Rg Rt hgen).acs.length =
      nodesOf (reorb I.A o.A) ∘ Fin.cast hn.symm := by
    rw [hnodes]; rfl
  have hinjN : Function.Injective (ComplJ8Of.powN (mkOrbit (reorb I.A o.A) hoA)
      (j9aDataOf P Rg Rt hgen).acs.length) := by
    rw [hpow]; exact hinj0.comp (Fin.cast_injective _)
  have hadjN : ∀ (i : Fin (j9aDataOf P Rg Rt hgen).acs.length)
      (hi : (i : ℕ) + 1 < (j9aDataOf P Rg Rt hgen).acs.length),
      ComplJ8Of.powN (mkOrbit (reorb I.A o.A) hoA)
          (j9aDataOf P Rg Rt hgen).acs.length ⟨(i : ℕ) + 1, hi⟩ =
        ComplJ8Of.powN (mkOrbit (reorb I.A o.A) hoA)
          (j9aDataOf P Rg Rt hgen).acs.length i * (mkOrbit (reorb I.A o.A) hoA).ω :=
    fun i hi => pow_succ _ _
  -- the J-8 orbit
  have hF := ComplJ9ARun.hF_run Rt hgen hpG h31A
  have hmem : (j9aDataOf P Rg Rt hgen).acs.length ∈ ComplJ8Of.sizesJ8 (j9aDataOf P Rg Rt hgen) := by
    simp [ComplJ8Of.sizesJ8]
  have hinjJ : Function.Injective (ComplJ8Of.powN (ComplJ8Of.orbJ8 (j9aDataOf P Rg Rt hgen) hF)
      (j9aDataOf P Rg Rt hgen).acs.length) :=
    (ComplJ8Of.powN_ok _ (ComplJ8Of.le_two_pow_ht _ hmem)).1
  -- coin events
  have hin := ComplJ9AOfMem.goodJA deltaF powerBasis3 Rt hgen hpG h31A hχ
  have gZ : ∀ e ∈ ComplJ8OfAtom.famAZ (K := KC), toχ χe ∉ e.ev :=
    hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9]))
  have gV : ∀ e ∈ ComplJ8OfAtom.famAV deltaF (j9aDataOf P Rg Rt hgen) (K := KC), toχ χe ∉ e.ev :=
    hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9]))
  have gH0 : ∀ e ∈ ComplJ8OfAtom.famAH deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hA
      (ComplJ8Of.orbJ8 (j9aDataOf P Rg Rt hgen) hF) (K := KC), toχ χe ∉ e.ev :=
    hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9]))
  have gMB0 : ∀ e ∈ ComplJ8OfAtom.famMB deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hA
      (ComplJ8Of.orbJ8 (j9aDataOf P Rg Rt hgen) hF) (K := KC), toχ χe ∉ e.ev :=
    hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9]))
  have gC0 : ∀ e ∈ ComplJ8OfAtom.famC deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hA
      (ComplJ8Of.orbJ8 (j9aDataOf P Rg Rt hgen) hF) (K := KC), toχ χe ∉ e.ev :=
    hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9]))
  have gMI0 : ∀ e ∈ ComplJ8OfAtom.famMI deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hA
      (ComplJ8Of.orbJ8 (j9aDataOf P Rg Rt hgen) hF) (K := KC), toχ χe ∉ e.ev :=
    hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9]))
  have gH := (GenPortJ9AHGood.famAH_ev_orb deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hA
    (ComplJ8Of.orbJ8 (j9aDataOf P Rg Rt hgen) hF) _ hinjJ hinjN (toχ χe)).mp gH0
  have gMB := (GenPortJ9AHGood.famMB_ev_orb deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hA
    (ComplJ8Of.orbJ8 (j9aDataOf P Rg Rt hgen) hF) _ hinjJ hinjN (toχ χe)).mp gMB0
  have gC := (GenPortJ9AHGood.famC_ev_orb deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hA
    (ComplJ8Of.orbJ8 (j9aDataOf P Rg Rt hgen) hF) _ hinjJ hinjN (toχ χe)).mp gC0
  have gMI := (GenPortJ9AHGood.famMI_ev_orb deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hA
    (ComplJ8Of.orbJ8 (j9aDataOf P Rg Rt hgen) hF) _ hinjJ hinjN (toχ χe)).mp gMI0
  have H :=GenPortJ9AHMemSat2.atomOK_runAo deltaF powerBasis3 Rt hgen hpG
    (mkOrbit (reorb I.A o.A) hoA) hA (ComplJ9ARun.h31_run Rt hgen h31A) hinjN hadjN
    (toχ χe) gZ gV gH gMB gC gMI
  obtain ⟨H1, H2, H3, H4⟩ := H
  -- publics
  have hpubs : (withOrb I o).toMsg.pubsA =
      ComplJ8Of.pubsAOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hA
        (mkOrbit (reorb I.A o.A) hoA) (toχ χe) :=
    funext fun j => atomE_pubs Rt hgen χe I hAc hpA hN hA _ hinjN j
  -- trace
  have hT : ∀ j : Fin 349, interpOf (reorb I.A o.A) j =
      ComplJ8Of.trAOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hA
        (mkOrbit (reorb I.A o.A) hoA) (toχ χe) j :=
    fun j => atomE_interp_at Rt hgen χe I hAc hN hA o.A _ rfl hoA hinj0 j j.2
  have hνμ : ∀ i : Fin (reorb I.A o.A).n,
      nodesOf (reorb I.A o.A) i =
        ComplJ8Of.powN (mkOrbit (reorb I.A o.A) hoA)
          (j9aDataOf P Rg Rt hgen).acs.length (Fin.cast hn i) :=
    fun i => congrFun hnodes i
  generalize (withOrb I o).toMsg.pubsA = pubs at hpubs ⊢
  subst hpubs
  have hT' : ∀ j : Fin 349, (withOrb I o).toTr.toJ8.A j =
      ComplJ8Of.trAOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hA
        (mkOrbit (reorb I.A o.A) hoA) (toχ χe) j :=
    fun j => hT j
  rw [GenPortJ9AHOrbAtom.qA_eq_cast _ _ _ _ _ hT', GenPortJ9AHOrbAtom.qAL_eq_cast _ _ _ _ _ hT']
  exact ⟨GenPortJ9AHChipCast.atomOK_reidx deltaF powerBasis3 hn hv'.nA hA _ _ hνμ _ _ _ _ ⟨H1, H2⟩,
    GenPortJ9AHChipCast.atomLOK_reidx deltaF powerBasis3 hn hv'.nA hA _ _ hνμ _ _ _ _ ⟨H3, H4⟩⟩


end Run

#print axioms atomE_n
#print axioms atomE_cols
#print axioms atomE_pubs
#print axioms atomE_interp
#print axioms atomE_interp_at
#print axioms atomE_at

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomE
