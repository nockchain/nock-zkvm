/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHAtomE.lean

  **Honest link, file 3: the atom chip over an abstract record `I : InJ9A` at the J-9 AL data `DL`.**
  Twin of `GenPortJ9AHAtomE` (`j9aDataOf` replaced by `j9alDataOf`).  Only `mb` differs from DA
  among the atom generator's inputs (`info`, `acs`, `mxA`, `mhA`, `rows` are DA's by `rfl`); the bumped `mb` meets
  `GenHyp` by `ComplJ9ALTables.genHyp_mbL`.  `hAc`/`hpA` are the RHS of the DL twin of `aRPK_eqJ`, verbatim.
  Table fact: `GenPortJ9ALHMemSat.atomOK_runLo`; coin hypothesis `B8L.Good` as in `GenPortJ9ALHCellE`.
-/
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

import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHMemSat

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
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (qA)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L (qAL)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAtomE

section Run
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [instFR : Fact (ringChar (ZMod P)).Prime] [instAR : Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × Nock.Jet.Prim.PrimOp))
  {fuel : ℕ} {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DL" => ComplJ9ALData.j9alDataOf P Rg Rt prims hgen
local notation "DA" => ComplJ9ADataRec.j9aDataOf P Rg Rt hgen
local notation "DD" => ComplJ8Data.j8DataOf P Rg Rt hgen

theorem atomE_nL (χe : CoinsE) (I : InJ9A)
    (hAc : I.A = chipOf (atomGenE (ComplJ8Data.ptrP P (DL).acs (DL).rows) χe (DL).acs (DL).info (DL).mb (DL).mxA (DL).mhA).1) :
    I.A.n = (DL).acs.length := by
  rw [hAc]
  exact atomGenE_size (ComplJ8Data.ptrP P (DL).acs (DL).rows) χe (DL).acs (DL).info (DL).mb (DL).mxA (DL).mhA

noncomputable abbrev colAFL (hA : 0 < (DL).acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h) (χe : CoinsE) :
    ℕ → Fin (DL).acs.length → ZMod P :=
  fun c i => fullCol hA (HonestA8.colA deltaF powerBasis3 hA (ComplJ8Of.powN o _) o
    (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
    (ComplJ8Of.pubsAOf deltaF powerBasis3 (DL) hA o (toχ χe))
    (ComplJ8Of.colAH deltaF powerBasis3 (DL) hA o (toχ χe) (ComplJ8Of.pubsAOf deltaF powerBasis3 (DL) hA o (toχ χe)))
    (ComplJ8Of.newBA (DL))) c i

theorem atomE_colsL (χe : CoinsE) (I : InJ9A)
    (hAc : I.A = chipOf (atomGenE (ComplJ8Data.ptrP P (DL).acs (DL).rows) χe (DL).acs (DL).info (DL).mb (DL).mxA (DL).mhA).1)
    (hN : (DD).rows.size ≤ 2 ^ 31) (hA : 0 < (DL).acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (DL).acs.length))
    (i : Fin I.A.n) (c : ℕ) (hc : c < 349) :
    I.A.cols c i = colAFL Rt prims hgen hA o χe c (Fin.cast (atomE_nL Rt prims hgen χe I hAc) i) := by
  have hacs : (DL).acs = ComplJ8Data.acsP P (DL).bigs (DL).dupP := rfl
  have hinfo : (DL).info = ComplJ8Data.infoOfP P (DL).acs (DL).rows := rfl
  have hg : ComplJ8Atom.GenHyp (DL).bigs (DL).dupP (DL).rows (DL).mb := ComplJ9ALTables.genHyp_mbL Rg Rt prims hgen hN
  have key := atomGenE_cols (DL) hacs hinfo hg χe hA o hinj (Fin.cast (atomE_nL Rt prims hgen χe I hAc) i) c hc
  refine Eq.trans ?_ key
  exact GenPortJ9AHAtomRun.chipOf_cols _ _ hAc c i

theorem atomE_pubsL (χe : CoinsE) (I : InJ9A)
    (hAc : I.A = chipOf (atomGenE (ComplJ8Data.ptrP P (DL).acs (DL).rows) χe (DL).acs (DL).info (DL).mb (DL).mxA (DL).mhA).1)
    (hpA : I.M.pubsA = (atomGenE (ComplJ8Data.ptrP P (DL).acs (DL).rows) χe (DL).acs (DL).info (DL).mb (DL).mxA (DL).mhA).2)
    (hN : (DD).rows.size ≤ 2 ^ 31) (hA : 0 < (DL).acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (DL).acs.length)) (j : ℕ) :
    K3.toK (I.M.pubsA j) = ComplJ8Of.pubsAOf deltaF powerBasis3 (DL) hA o (toχ χe) j := by
  have hacs : (DL).acs = ComplJ8Data.acsP P (DL).bigs (DL).dupP := rfl
  have hinfo : (DL).info = ComplJ8Data.infoOfP P (DL).acs (DL).rows := rfl
  have hg : ComplJ8Atom.GenHyp (DL).bigs (DL).dupP (DL).rows (DL).mb := ComplJ9ALTables.genHyp_mbL Rg Rt prims hgen hN
  rw [hpA]
  exact atomGenE_pubs (DL) hacs hinfo hg χe hA o hinj j

theorem atomE_interpL (χe : CoinsE) (I : InJ9A)
    (hAc : I.A = chipOf (atomGenE (ComplJ8Data.ptrP P (DL).acs (DL).rows) χe (DL).acs (DL).info (DL).mb (DL).mxA (DL).mhA).1)
    (hN : (DD).rows.size ≤ 2 ^ 31) (hA : 0 < (DL).acs.length)
    (q : ChipIn) (hqn : q.n = I.A.n)
    (hqc : ∀ c i, q.cols c i = I.A.cols c (Fin.cast hqn i))
    (ho : OrbOK q) (hinj : Function.Injective (nodesOf q)) (j : ℕ) (hj : j < 349) :
    interpOf q j = ComplJ8Of.trAOf deltaF powerBasis3 (DL) hA (mkOrbit q ho) (toχ χe) ⟨j, hj⟩ := by
  have e : q.n = (DL).acs.length := hqn.trans (atomE_nL Rt prims hgen χe I hAc)
  have hinj' : Function.Injective (ComplJ8Of.powN (mkOrbit q ho) (DL).acs.length) := by
    intro a b hab
    have h1 : nodesOf q (Fin.cast e.symm a) = nodesOf q (Fin.cast e.symm b) := by
      rw [nodesOf_powN q ho]
      exact hab
    have h2 := hinj h1
    have h3 : ((Fin.cast e.symm a : Fin q.n) : ℕ) = ((Fin.cast e.symm b : Fin q.n) : ℕ) := congrArg Fin.val h2
    exact Fin.ext h3
  obtain ⟨gG, hgG⟩ : ∃ g : Fin (DL).acs.length → ZMod P, g = colAFL Rt prims hgen hA (mkOrbit q ho) χe j :=
    ⟨_, rfl⟩
  have hcols : ∀ i : Fin q.n, q.cols j i = gG (Fin.cast e i) := by
    intro i
    rw [hqc, hgG]
    exact atomE_colsL Rt prims hgen χe I hAc hN hA (mkOrbit q ho) hinj' (Fin.cast hqn i) j hj
  have hn : nodesOf q = fun i : Fin q.n => ComplJ8Of.powN (mkOrbit q ho) (DL).acs.length (Fin.cast e i) :=
    funext fun i => (congrFun (nodesOf_powN q ho) i).trans rfl
  show Lagrange.interpolate Finset.univ (nodesOf q) (fun i => q.cols j i) = _
  rw [hn, show (fun i => q.cols j i) = fun i : Fin q.n => gG (Fin.cast e i) from funext hcols]
  refine (interp_cast e (ComplJ8Of.powN (mkOrbit q ho) (DL).acs.length) gG).trans ?_
  subst hgG
  rfl

include hgen

theorem atomE_interp_atL (χe : CoinsE) (I : InJ9A)
    (hAc : I.A = chipOf (atomGenE (ComplJ8Data.ptrP P (DL).acs (DL).rows) χe (DL).acs (DL).info (DL).mb (DL).mxA (DL).mhA).1)
    (hN : (ComplJ8Data.j8DataOf P Rg Rt hgen).rows.size ≤ 2 ^ 31)
    (hA : 0 < (DL).acs.length)
    (O' : Orb) (q : ChipIn) (hq : q = reorb I.A O')
    (ho : OrbOK q) (hinj : Function.Injective (nodesOf q)) (j : ℕ) (hj : j < 349) :
    interpOf q j = ComplJ8Of.trAOf deltaF powerBasis3 (DL) hA (mkOrbit q ho) (toχ χe)
      ⟨j, hj⟩ := by
  subst hq
  exact atomE_interpL Rt prims hgen χe I hAc hN hA (reorb I.A O') rfl (fun _ _ => rfl) ho hinj j hj

/-- **`(hsatA ∧ hbindA) ∧ (hsatL ∧ hbindL)` of `AcceptsJ9A` at `withOrb I o`.** -/
theorem atomE_atL (hpG : P = Nock.Atoms.p)
    (h31A : ComplJ9ARun.Rows31A (DA))
    (χe : CoinsE) (I : InJ9A)
    (hAc : I.A = chipOf (atomGenE (ComplJ8Data.ptrP P (DL).acs (DL).rows) χe (DL).acs (DL).info (DL).mb (DL).mxA (DL).mhA).1)
    (hpA : I.M.pubsA = (atomGenE (ComplJ8Data.ptrP P (DL).acs (DL).rows) χe (DL).acs (DL).info (DL).mb (DL).mxA (DL).mhA).2)
    (o : OrbJ9A) (ho : OrbAdm I o)
    (hv' : ValidJ9A (withOrb I o))
    (hχ : (ComplJ9ALRun.B8L deltaF powerBasis3 Rt hgen prims hpG
      (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).Good (toχ χe)) :
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
  have hn := atomE_nL Rt prims hgen χe I hAc
  have hA : 0 < (DL).acs.length := ComplJ9ALData.acsL_pos Rt prims hgen
  have h31 := ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A
  have hN := ComplJ9ALTables.rows_leL Rt prims hgen (ComplJ9ARun.rows31_of_A h31)
  have hoA : OrbOK (reorb I.A o.A) := hv'.oA
  have hinj0 : Function.Injective (nodesOf (reorb I.A o.A)) :=
    GenPortJ9AHOrb.nodesOf_inj _ hoA ho.A.2
  have hnodes : nodesOf (reorb I.A o.A) =
      ComplJ8Of.powN (mkOrbit (reorb I.A o.A) hoA) I.A.n :=
    GenPortJ9AHOrbA.nodesOf_powN _ hoA
  have hpow : ComplJ8Of.powN (mkOrbit (reorb I.A o.A) hoA)
        (DL).acs.length =
      nodesOf (reorb I.A o.A) ∘ Fin.cast hn.symm := by
    rw [hnodes]; rfl
  have hinjN : Function.Injective (ComplJ8Of.powN (mkOrbit (reorb I.A o.A) hoA)
      (DL).acs.length) := by
    rw [hpow]; exact hinj0.comp (Fin.cast_injective _)
  have hadjN : ∀ (i : Fin (DL).acs.length)
      (hi : (i : ℕ) + 1 < (DL).acs.length),
      ComplJ8Of.powN (mkOrbit (reorb I.A o.A) hoA)
          (DL).acs.length ⟨(i : ℕ) + 1, hi⟩ =
        ComplJ8Of.powN (mkOrbit (reorb I.A o.A) hoA)
          (DL).acs.length i * (mkOrbit (reorb I.A o.A) hoA).ω :=
    fun i hi => pow_succ _ _
  -- the J-8 orbit
  have hF := ComplJ9ALRun.hFL Rt hgen prims hpG h31
  have hmem : (DL).acs.length ∈ ComplJ8Of.sizesJ8 (DL) := by
    simp [ComplJ8Of.sizesJ8]
  have hinjJ : Function.Injective (ComplJ8Of.powN (ComplJ8Of.orbJ8 (DL) hF)
      (DL).acs.length) :=
    (ComplJ8Of.powN_ok _ (ComplJ8Of.le_two_pow_ht _ hmem)).1
  -- coin events
  have hin := GenPortJ9ALHMemSat.hin_B8L deltaF powerBasis3 Rt prims hgen hpG h31 (toχ χe) hχ
  have gZ : ∀ e ∈ ComplJ8OfAtom.famAZ (K := KC), toχ χe ∉ e.ev :=
    hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9]))
  have gV : ∀ e ∈ ComplJ8OfAtom.famAV deltaF (DL) (K := KC), toχ χe ∉ e.ev :=
    hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9]))
  have gH0 : ∀ e ∈ ComplJ8OfAtom.famAH deltaF powerBasis3 (DL) hA
      (ComplJ8Of.orbJ8 (DL) hF) (K := KC), toχ χe ∉ e.ev :=
    hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9]))
  have gMB0 : ∀ e ∈ ComplJ8OfAtom.famMB deltaF powerBasis3 (DL) hA
      (ComplJ8Of.orbJ8 (DL) hF) (K := KC), toχ χe ∉ e.ev :=
    hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9]))
  have gC0 : ∀ e ∈ ComplJ8OfAtom.famC deltaF powerBasis3 (DL) hA
      (ComplJ8Of.orbJ8 (DL) hF) (K := KC), toχ χe ∉ e.ev :=
    hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9]))
  have gMI0 : ∀ e ∈ ComplJ8OfAtom.famMI deltaF powerBasis3 (DL) hA
      (ComplJ8Of.orbJ8 (DL) hF) (K := KC), toχ χe ∉ e.ev :=
    hin _ (List.mem_append_right _ (by simp [ComplJ9BOf.famsA9]))
  have gH := (GenPortJ9AHGood.famAH_ev_orb deltaF powerBasis3 (DL) hA
    (ComplJ8Of.orbJ8 (DL) hF) _ hinjJ hinjN (toχ χe)).mp gH0
  have gMB := (GenPortJ9AHGood.famMB_ev_orb deltaF powerBasis3 (DL) hA
    (ComplJ8Of.orbJ8 (DL) hF) _ hinjJ hinjN (toχ χe)).mp gMB0
  have gC := (GenPortJ9AHGood.famC_ev_orb deltaF powerBasis3 (DL) hA
    (ComplJ8Of.orbJ8 (DL) hF) _ hinjJ hinjN (toχ χe)).mp gC0
  have gMI := (GenPortJ9AHGood.famMI_ev_orb deltaF powerBasis3 (DL) hA
    (ComplJ8Of.orbJ8 (DL) hF) _ hinjJ hinjN (toχ χe)).mp gMI0
  have H :=GenPortJ9ALHMemSat.atomOK_runLo deltaF powerBasis3 Rt prims hgen hpG
    (mkOrbit (reorb I.A o.A) hoA) hA (ComplJ9ARun.rows31_of_A h31) hinjN hadjN
    (toχ χe) gZ gV gH gMB gC gMI
  obtain ⟨H1, H2, H3, H4⟩ := H
  -- publics
  have hpubs : (withOrb I o).toMsg.pubsA =
      ComplJ8Of.pubsAOf deltaF powerBasis3 (DL) hA
        (mkOrbit (reorb I.A o.A) hoA) (toχ χe) :=
    funext fun j => atomE_pubsL Rt prims hgen χe I hAc hpA hN hA _ hinjN j
  -- trace
  have hT : ∀ j : Fin 349, interpOf (reorb I.A o.A) j =
      ComplJ8Of.trAOf deltaF powerBasis3 (DL) hA
        (mkOrbit (reorb I.A o.A) hoA) (toχ χe) j :=
    fun j => atomE_interp_atL Rt prims hgen χe I hAc hN hA o.A _ rfl hoA hinj0 j j.2
  have hνμ : ∀ i : Fin (reorb I.A o.A).n,
      nodesOf (reorb I.A o.A) i =
        ComplJ8Of.powN (mkOrbit (reorb I.A o.A) hoA)
          (DL).acs.length (Fin.cast hn i) :=
    fun i => congrFun hnodes i
  generalize (withOrb I o).toMsg.pubsA = pubs at hpubs ⊢
  subst hpubs
  have hT' : ∀ j : Fin 349, (withOrb I o).toTr.toJ8.A j =
      ComplJ8Of.trAOf deltaF powerBasis3 (DL) hA
        (mkOrbit (reorb I.A o.A) hoA) (toχ χe) j :=
    fun j => hT j
  rw [GenPortJ9AHOrbAtom.qA_eq_cast _ _ _ _ _ hT', GenPortJ9AHOrbAtom.qAL_eq_cast _ _ _ _ _ hT']
  exact ⟨GenPortJ9AHChipCast.atomOK_reidx deltaF powerBasis3 hn hv'.nA hA _ _ hνμ _ _ _ _ ⟨H1, H2⟩,
    GenPortJ9AHChipCast.atomLOK_reidx deltaF powerBasis3 hn hv'.nA hA _ _ hνμ _ _ _ _ ⟨H3, H4⟩⟩


end Run

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAtomE
