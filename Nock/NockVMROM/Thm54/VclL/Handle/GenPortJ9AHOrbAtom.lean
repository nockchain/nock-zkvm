/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHOrbAtom.lean

* `rows_leP`        : `(j8DataOf …).rows.size ≤ 2 ^ 31` from `Rows31A DA` (the `hN` of `genJ9AX_atom_interp`);
  * `atom_interp_at`  : `genJ9AX_atom_interp` at `q = reorb I.A O'`;
  * `atom_at`         : `(hsatA ∧ hbindA) ∧ (hsatL ∧ hbindL)` at `mkPbA (withOrb I o) hv'`, `I.toMsg`/`toTr`,
                        coin `toχ χe` (D1b `atomOK_runAo` at the orbit of `reorb I.A o.A`, D2 `*_ev_orb`, F1b casts).
  Never compares `mkPbA` with `B.Pb`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipCast
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMemSat2
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfMem

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbAtom

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf acsA_pos)
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (qA)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L (qAL)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA

section Run
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- Variable-level view lemma: `qA` is the cast of any `T` agreeing with `tr.A` (cheap to instantiate). -/
theorem qA_eq_cast (Pb : Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8.PubJ8 P)
    (tr : Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8.TrJ8 (ZMod P)) (chals pubs : ℕ → KC)
    (T : Fin 349 → Polynomial (ZMod P)) (h : ∀ j : Fin 349, tr.A j = T j) :
    qA deltaF powerBasis3 Pb tr chals pubs =
      fun j => T (Fin.cast (AtomChipHQ.atomChipHQ_width deltaF powerBasis3 Pb.hnA Pb.nodesA Pb.orbitA chals pubs) j) :=
  funext fun j => h _

/-- Variable-level view lemma for the variant chip. -/
theorem qAL_eq_cast (Pb : Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8.PubJ8 P)
    (tr : Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8.TrJ8 (ZMod P)) (chals pubs : ℕ → KC)
    (T : Fin 349 → Polynomial (ZMod P)) (h : ∀ j : Fin 349, tr.A j = T j) :
    qAL deltaF powerBasis3 Pb tr chals pubs =
      fun j => T (Fin.cast (AtomChipHQL.atomChipHQL_width deltaF powerBasis3 Pb.hnA Pb.nodesA Pb.orbitA chals pubs) j) :=
  funext fun j => h _

/-- **The `hN` binder of `genJ9AX_atom_interp`**: the J-8 rows fit in `2^31`, from `Rows31A DA`. -/
theorem rows_leP (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen)) :
    (ComplJ8Data.j8DataOf P Rg Rt hgen).rows.size ≤ 2 ^ 31 :=
  ComplJ9ATables.rows_leA Rg Rt hgen (ComplJ9ARun.h31_run Rt hgen h31A)

include hgen

/-- `genJ9AX_atom_interp` at `q = reorb I.A O'` (any orbit with injective nodes). -/
theorem atom_interp_at (hnc : callsOf (ComplJ8Data.rowsOfT t) = []) (χe : CoinsE)
    (hN : (ComplJ8Data.j8DataOf P Rg Rt hgen).rows.size ≤ 2 ^ 31)
    (hA : 0 < (j9aDataOf P Rg Rt hgen).acs.length)
    (O' : Orb) (q : ChipIn) (hq : q = reorb (recJ9AX s f χe t r).A O')
    (ho : OrbOK q) (hinj : Function.Injective (nodesOf q)) (j : ℕ) (hj : j < 349) :
    interpOf q j = ComplJ8Of.trAOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hA (mkOrbit q ho) (toχ χe)
      ⟨j, hj⟩ := by
  subst hq
  exact GenPortJ9AHAtomRun.genJ9AX_atom_interp Rt hgen hnc χe hN hA (reorb (recJ9AX s f χe t r).A O') rfl (fun _ _ => rfl) ho hinj j hj

/-- **`(hsatA ∧ hbindA) ∧ (hsatL ∧ hbindL)` of `AcceptsJ9A` at `withOrb I o`.** -/
theorem atom_at (hnc : callsOf (ComplJ8Data.rowsOfT t) = []) (hpG : P = Nock.Atoms.p)
    (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (χe : CoinsE) (o : OrbJ9A) (ho : OrbAdm (recJ9AX s f χe t r) o)
    (hv' : ValidJ9A (withOrb (recJ9AX s f χe t r) o))
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    ((AtomChipHQ.atomChipHQ deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').hnA
        (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nodesA (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').orbitA
        (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) (withOrb (recJ9AX s f χe t r) o).toMsg.pubsA).rap.Satisfies
      (qA deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').toPubJ8
        (withOrb (recJ9AX s f χe t r) o).toTr.toJ8 (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
        (withOrb (recJ9AX s f χe t r) o).toMsg.pubsA) ∧
    (AtomChipHQ.atomChipHQ deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').hnA
        (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nodesA (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').orbitA
        (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) (withOrb (recJ9AX s f χe t r) o).toMsg.pubsA).BindsPreprocessing
      (qA deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').toPubJ8
        (withOrb (recJ9AX s f χe t r) o).toTr.toJ8 (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
        (withOrb (recJ9AX s f χe t r) o).toMsg.pubsA)) ∧
    ((AtomChipHQL.atomChipHQL deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').hnA
        (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nodesA (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').orbitA
        (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) (withOrb (recJ9AX s f χe t r) o).toMsg.pubsA).rap.Satisfies
      (qAL deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').toPubJ8
        (withOrb (recJ9AX s f χe t r) o).toTr.toJ8 (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
        (withOrb (recJ9AX s f χe t r) o).toMsg.pubsA) ∧
    (AtomChipHQL.atomChipHQL deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').hnA
        (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nodesA (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').orbitA
        (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) (withOrb (recJ9AX s f χe t r) o).toMsg.pubsA).BindsPreprocessing
      (qAL deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').toPubJ8
        (withOrb (recJ9AX s f χe t r) o).toTr.toJ8 (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
        (withOrb (recJ9AX s f χe t r) o).toMsg.pubsA)) := by
  have hn := GenPortJ9AHAtomRun.genJ9AX_atom_n Rt hgen hnc χe
  have hA : 0 < (j9aDataOf P Rg Rt hgen).acs.length := acsA_pos Rt hgen
  have hN := rows_leP Rt hgen h31A
  have hoA : OrbOK (reorb (recJ9AX s f χe t r).A o.A) := hv'.oA
  have hinj0 : Function.Injective (nodesOf (reorb (recJ9AX s f χe t r).A o.A)) :=
    GenPortJ9AHOrb.nodesOf_inj _ hoA ho.A.2
  have hnodes : nodesOf (reorb (recJ9AX s f χe t r).A o.A) =
      ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).A o.A) hoA) (recJ9AX s f χe t r).A.n :=
    GenPortJ9AHOrbA.nodesOf_powN _ hoA
  have hpow : ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).A o.A) hoA)
        (j9aDataOf P Rg Rt hgen).acs.length =
      nodesOf (reorb (recJ9AX s f χe t r).A o.A) ∘ Fin.cast hn.symm := by
    rw [hnodes]; rfl
  have hinjN : Function.Injective (ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).A o.A) hoA)
      (j9aDataOf P Rg Rt hgen).acs.length) := by
    rw [hpow]; exact hinj0.comp (Fin.cast_injective _)
  have hadjN : ∀ (i : Fin (j9aDataOf P Rg Rt hgen).acs.length)
      (hi : (i : ℕ) + 1 < (j9aDataOf P Rg Rt hgen).acs.length),
      ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).A o.A) hoA)
          (j9aDataOf P Rg Rt hgen).acs.length ⟨(i : ℕ) + 1, hi⟩ =
        ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).A o.A) hoA)
          (j9aDataOf P Rg Rt hgen).acs.length i * (mkOrbit (reorb (recJ9AX s f χe t r).A o.A) hoA).ω :=
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
    (mkOrbit (reorb (recJ9AX s f χe t r).A o.A) hoA) hA (ComplJ9ARun.h31_run Rt hgen h31A) hinjN hadjN
    (toχ χe) gZ gV gH gMB gC gMI
  obtain ⟨H1, H2, H3, H4⟩ := H
  -- publics
  have hpubs : (withOrb (recJ9AX s f χe t r) o).toMsg.pubsA =
      ComplJ8Of.pubsAOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hA
        (mkOrbit (reorb (recJ9AX s f χe t r).A o.A) hoA) (toχ χe) :=
    funext fun j => GenPortJ9AHAtomRun.genJ9AX_atom_pubs Rt hgen hnc χe hN hA _ hinjN j
  -- trace
  have hT : ∀ j : Fin 349, interpOf (reorb (recJ9AX s f χe t r).A o.A) j =
      ComplJ8Of.trAOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hA
        (mkOrbit (reorb (recJ9AX s f χe t r).A o.A) hoA) (toχ χe) j :=
    fun j => atom_interp_at Rt hgen hnc χe hN hA o.A _ rfl hoA hinj0 j j.2
  have hνμ : ∀ i : Fin (reorb (recJ9AX s f χe t r).A o.A).n,
      nodesOf (reorb (recJ9AX s f χe t r).A o.A) i =
        ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).A o.A) hoA)
          (j9aDataOf P Rg Rt hgen).acs.length (Fin.cast hn i) :=
    fun i => congrFun hnodes i
  generalize (withOrb (recJ9AX s f χe t r) o).toMsg.pubsA = pubs at hpubs ⊢
  subst hpubs
  have hT' : ∀ j : Fin 349, (withOrb (recJ9AX s f χe t r) o).toTr.toJ8.A j =
      ComplJ8Of.trAOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) hA
        (mkOrbit (reorb (recJ9AX s f χe t r).A o.A) hoA) (toχ χe) j :=
    fun j => hT j
  rw [qA_eq_cast _ _ _ _ _ hT', qAL_eq_cast _ _ _ _ _ hT']
  exact ⟨GenPortJ9AHChipCast.atomOK_reidx deltaF powerBasis3 hn hv'.nA hA _ _ hνμ _ _ _ _ ⟨H1, H2⟩,
    GenPortJ9AHChipCast.atomLOK_reidx deltaF powerBasis3 hn hv'.nA hA _ _ hνμ _ _ _ _ ⟨H3, H4⟩⟩

end Run

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbAtom

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbAtom in
#print axioms qA_eq_cast
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbAtom in
#print axioms qAL_eq_cast
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbAtom in
#print axioms rows_leP
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbAtom in
#print axioms atom_interp_at
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbAtom in
#print axioms atom_at
