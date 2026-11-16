/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHXASE.lean

  **The compute, axis and split chips over an abstract record `I : InJ9A`.**
  No `hnc`: the field-shape equations `hX hm hρ hρS` (compute), `hAX hpX haxOn hszAX` (axis),
  `hSPon hSPoff hspOn hszSP hszA` (split) replace the record lemmas. `hJk` is not here. -/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbXAS
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsg

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHXASE

noncomputable section

/-! ## 1. Compute chip -/

section Sat

open Nock Nock.Noun Nock.Walk Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 toVSQ)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (genX9T)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOfComp
open Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff Nock.V1J9A.GenJ9AX Nock.V1J9A.GenCompX9
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A (qX9)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCoin
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbJ9A OrbAdm reorb withOrb)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbXAS
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (W9 N9 N9_def idOfA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 rowsOfT9 genX9T)
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD (lnClosed cntClosed)
open Nock.NockVMROM.Thm54.VclL.HonestSatX9 (accW9)
open Nock.NockVMROM.Thm54.VclL.HonestTraceX9 (polyX9)

variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- `toTr_C_at` at an abstract record: from the compute-chip shape `hX`. -/
theorem toTrE_C_at (χe : CoinsE) (I : InJ9A)
    (hX : I.X = chipOf (compGenX9 ⟨s, f, r⟩ (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
      (idOfA (p := P) Rt hgen) (W9 t) χe).rows)
    (ν : Fin I.X.n → ZMod P) (d : Fin 137) :
    Lagrange.interpolate Finset.univ ν (fun i => I.X.cols d i) =
      polyX9 powerBasis3 deltaF (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd (idOfA (p := P) Rt hgen)
        (W9 t) (Example.chalE χe) (pubFinal9 ⟨s, f, r⟩ (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
          (idOfA (p := P) Rt hgen) (W9 t) χe)
        (lnClosed (K3.toK (χe ⟨13, by decide⟩)))
        (cntClosed (Walk.foCol (W9 t)) (K3.toK (χe ⟨13, by decide⟩)) (K3.toK (χe ⟨13, by decide⟩)))
        (accW9 (fun u => K3.toK (nodeV9E (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
          (idOfA (p := P) Rt hgen) (χe ⟨14, by decide⟩) u)) (W9 t) (K3.toK (χe ⟨13, by decide⟩)))
        ν 137 d :=
  interp_aux_at ⟨s, f, r⟩ (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd (idOfA (p := P) Rt hgen)
    t χe d _ _ _ rfl rfl rfl I.X hX ν

/-- **`hsatX` at `withOrb I o`** over an abstract record. -/
theorem hsatXE_at
    (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (χe : CoinsE) (I : InJ9A) (hc : I.c = ⟨s, f, r⟩) (hχI : I.χ = χe)
    (hX : I.X = chipOf (compGenX9 ⟨s, f, r⟩ (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
      (idOfA (p := P) Rt hgen) (W9 t) χe).rows)
    (hm : I.toMsg.m = ((BRun9A deltaF powerBasis3 Rt hgen hpG h31A).M (toχ χe)).m) (hρ : I.toMsg.ρ = ((BRun9A deltaF powerBasis3 Rt hgen hpG h31A).M (toχ χe)).ρ)
    (hρS : I.toMsg.ρS = ((BRun9A deltaF powerBasis3 Rt hgen hpG h31A).M (toχ χe)).ρS)
    (o : OrbJ9A) (ho : OrbAdm I o) (hv' : ValidJ9A (withOrb I o))
    (hχ : (BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX9 (mkPbA (withOrb I o) hv').hn
        (mkPbA (withOrb I o) hv').nodes powerBasis3 deltaF
        (chalVJ8 powerBasis3 (toχ (withOrb I o).χ))
        (ClaimJ9.pubVJ9 deltaF powerBasis3 (withOrb I o).c
          (withOrb I o).toMsg.m (withOrb I o).toMsg.ρ
          (withOrb I o).toMsg.ρS (toχ (withOrb I o).χ))
        (mkPbA (withOrb I o) hv').orbit)
      (qX9 deltaF powerBasis3 (mkPbA (withOrb I o) hv') (withOrb I o).toTr
        (chalVJ8 powerBasis3 (toχ (withOrb I o).χ))
        (ClaimJ9.pubVJ9 deltaF powerBasis3 (withOrb I o).c
          (withOrb I o).toMsg.m (withOrb I o).toMsg.ρ
          (withOrb I o).toMsg.ρS (toχ (withOrb I o).χ))) := by
  have hXn : I.X.n = N9 t := by
    rw [hX, Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp.chipOf_n,
      Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp.compGenX9_size, N9_def]
  obtain ⟨⟨hinj, hadj⟩, -⟩ := Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA.nodes_withOrb ho hv'
  have key := GenPortJ9AHCompSat.hsatXA_at (p := P) deltaF powerBasis3 Rt hgen hpG h31A hax9 hop5 (toχ χe) hχ
    (mkPbA (withOrb I o) hv').hn hXn (mkPbA (withOrb I o) hv').nodes hinj
    (mkPbA (withOrb I o) hv').orbit hadj
  subst hχI
  have hpub : ClaimJ9.pubVJ9 deltaF powerBasis3 (withOrb I o).c
      (withOrb I o).toMsg.m (withOrb I o).toMsg.ρ
      (withOrb I o).toMsg.ρS (toχ (withOrb I o).χ) =
      pubCA deltaF powerBasis3 Rt hgen (toχ I.χ) := by
    unfold pubCA
    show ClaimJ9.pubVJ9 deltaF powerBasis3 I.c I.toMsg.m I.toMsg.ρ I.toMsg.ρS (toχ I.χ) = _
    rw [hc, hm, hρ, hρS]
    rfl
  have hq : qX9 deltaF powerBasis3 (mkPbA (withOrb I o) hv')
        (withOrb I o).toTr
        (chalVJ8 powerBasis3 (toχ (withOrb I o).χ))
        (pubCA deltaF powerBasis3 Rt hgen (toχ I.χ)) =
      trCA deltaF powerBasis3 Rt hgen (toχ I.χ) (mkPbA (withOrb I o) hv').nodes := by
    funext d
    refine Eq.trans (toTrE_C_at Rt hgen I.χ I hX (mkPbA (withOrb I o) hv').nodes d) ?_
    have hp : pubFinal9 ⟨s, f, r⟩ (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
        (idOfA (p := P) Rt hgen) (W9 t) I.χ = pubCA deltaF powerBasis3 Rt hgen (toχ I.χ) :=
      pubFinal9_eq_pubCA Rt hgen I.χ
    rw [trCA_def, hchi_toχ, hp]
    have hα := αC0_toχ I.χ
    have hγ := γC0_toχ I.χ
    have hnode : ∀ γ0 : K3, K3.toK γ0 = γA powerBasis3 (toχ I.χ) →
        nodeVA powerBasis3 Rt hgen (toχ I.χ) =
        fun u => K3.toK (nodeV9E (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
          (idOfA (p := P) Rt hgen) γ0 u) := fun γ0 hg =>
      funext fun u => by
        rw [nodeV9E_eq]
        show ComplJ9AReadsAt.nodeV9 (F := ZMod P) _ _ _ (γA powerBasis3 (toχ I.χ)) u = _
        rw [hg]
    rw [show αA powerBasis3 (toχ I.χ) = _ from hα, hnode _ hγ.symm]
    rfl
  rw [hpub, hq]
  exact key

end Sat

/-! ## 2. Axis chip -/

section AxisRun

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen Nock.V1J9A
open Nock.V1J9A.CheckJ9AIff Nock.V1J9A.CheckJ9A Nock.V1J9A.GenJ9AX
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AXChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
  (BRun9A famAXA famSPA good_fam axOnA spOnA nSOf nSOf_eq nSOf_pos Rows31A nXA_pos nXA_eq csA)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj (RnOf rows9J recX_AX recX_SP recX_pubsX recX_pubsS
  sRPJ_of_spOn sRPJ_of_not_spOn)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbJ9A OrbAdm reorb withOrb)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbXAS

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **`hAXk` at `withOrb I o`** over an abstract record. -/
theorem hAXkE_at (hpG : P = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf P Rg Rt hgen))
    (χe : CoinsE) (I : InJ9A) (hχI : I.χ = χe)
    (hAX : I.AX = chipOf (GenAxE.axGenOf χe (j9aDataOf P Rg Rt hgen).acs.length (j9aDataOf P Rg Rt hgen).H
      (ComplJ9AGen.rowsOfT9 t) (axOnA t)).1)
    (hpX : I.pubsX = (GenAxE.axGenOf χe (j9aDataOf P Rg Rt hgen).acs.length (j9aDataOf P Rg Rt hgen).H
      (ComplJ9AGen.rowsOfT9 t) (axOnA t)).2)
    (haxOn : I.axOn = axOnA t) (hszAX : I.AX.n = (BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Pb.nX)
    (o : OrbJ9A) (ho : OrbAdm I o) (hv' : ValidJ9A (withOrb I o))
    (hχ : (BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    AXChipOK deltaF powerBasis3 (mkPbA (withOrb I o) hv').axOn
      (mkPbA (withOrb I o) hv').hnX (mkPbA (withOrb I o) hv').nodesX
      (mkPbA (withOrb I o) hv').orbitX
      (VerJ8.chalsMJ8 deltaF (toχ (withOrb I o).χ))
      (withOrb I o).toMsg.pubsX
      (fun j => (withOrb I o).toTr.X
        (Fin.cast (AxisChipJ9.width_eq deltaF powerBasis3 hv'.nAX (nodesOf (withOrb I o).AX)
          (mkOrbit (withOrb I o).AX hv'.oAX)
          (VerJ8.chalsMJ8 deltaF (toχ (withOrb I o).χ))
          (withOrb I o).toMsg.pubsX) j)) := by
  have hsz : I.AX.n ≤ 2 ^ 31 :=
    hszAX.le.trans (h31A _ (ComplJ9AOfStatic.mem_nX Rt hgen))
  refine axOK_I' (withOrb I o) hv' o.AX χe (j9aDataOf P Rg Rt hgen).acs.length
    (j9aDataOf P Rg Rt hgen).H (ComplJ9AGen.rowsOfT9 t) (axOnA t) ?_ ?_ haxOn hχI ho.AX.2 ?_ ?_ ?_
  · show reorb I.AX o.AX = _
    rw [hAX]
  · show I.pubsX = _
    exact hpX
  · intro _
    exact GenPortJ9AHMsg.le_tbl _ _ hAX hsz
  · intro _
    exact ComplJ9AChainsRun.axChains9_OK (p0 := P) (j9aDataOf P Rg Rt hgen).acs.length (j9aDataOf P Rg Rt hgen).H
      hgen hpG (fun a c => (ComplJ8CompRun.hH_run (p := P) Rt hgen).cell a c)
  · intro h hn0 hn e he
    rw [famAX_irrel hn0 (nXA_pos (p := P) Rt hgen) _ hn (nXA_eq (p := P) Rt hgen h)] at he
    exact good_fam deltaF powerBasis3 Rt hgen hpG h31A hχ (famAXA deltaF Rt hgen)
      (List.mem_append_right _ List.mem_cons_self) e (by simp only [famAXA, dif_pos h]; exact he)

end AxisRun

/-! ## 3. Split chip -/

section SplitRun

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen Nock.V1J9A
open Nock.V1J9A.CheckJ9AIff Nock.V1J9A.CheckJ9A Nock.V1J9A.GenJ9AX
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (SPChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
  (BRun9A famSPA good_fam axOnA spOnA nSOf nSOf_eq nSOf_pos Rows31A)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj (RnOf rows9J spOnJ recX_SP recX_pubsS
  sRPJ_of_spOn sRPJ_of_not_spOn)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbJ9A OrbAdm reorb withOrb)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbXAS

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **`hSPk` at `withOrb I o`** over an abstract record. -/
theorem hSPkE_at (hpG : P = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf P Rg Rt hgen))
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (χe : CoinsE) (I : InJ9A) (hχI : I.χ = χe)
    (hSPon : spOnA P t = true →
      I.SP = chipOf (GenSpE.spGenE χe (j9aDataOf P Rg Rt hgen).acs.length (GenSpE.vSE (ComplJ9AGen.rowsOfT9 t))
        (GenSpE.mSE (ComplJ9AGen.rowsOfT9 t) (GenSpE.vSE (ComplJ9AGen.rowsOfT9 t)))).1 ∧
      I.pubsS = (GenSpE.spGenE χe (j9aDataOf P Rg Rt hgen).acs.length (GenSpE.vSE (ComplJ9AGen.rowsOfT9 t))
        (GenSpE.mSE (ComplJ9AGen.rowsOfT9 t) (GenSpE.vSE (ComplJ9AGen.rowsOfT9 t)))).2)
    (hSPoff : ¬ spOnA P t = true → I.pubsS = fun _ => (0 : K3))
    (hspOn : I.spOn = spOnA P t) (hszSP : I.SP.n = (BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Pb.nS) (hszA : I.A.n = (BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Pb.nA)
    (o : OrbJ9A) (ho : OrbAdm I o) (hv' : ValidJ9A (withOrb I o))
    (hχ : (BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    SPChipOK deltaF powerBasis3 (mkPbA (withOrb I o) hv').nA
      (mkPbA (withOrb I o) hv').spOn (mkPbA (withOrb I o) hv').hnS
      (mkPbA (withOrb I o) hv').nodesS (mkPbA (withOrb I o) hv').orbitS
      (VerJ8.chalsMJ8 deltaF (toχ (withOrb I o).χ))
      (withOrb I o).toMsg.pubsS
      (fun j => (withOrb I o).toTr.S
        (Fin.cast (SplitChipJ9.width_eq deltaF (mkPbA (withOrb I o) hv').nA powerBasis3
          (mkPbA (withOrb I o) hv').hnS (mkPbA (withOrb I o) hv').nodesS
          (mkPbA (withOrb I o) hv').orbitS
          (VerJ8.chalsMJ8 deltaF (toχ (withOrb I o).χ))
          (withOrb I o).toMsg.pubsS) j)) := by
  by_cases h : spOnA P t = true
  · obtain ⟨hSP, hP⟩ := hSPon h
    have hn : I.SP.n = nSOf P t := hszSP.trans (rfl : (BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Pb.nS = nSOf P t)
    have hvl : I.SP.n = (GenSpE.vSE (ComplJ9AGen.rowsOfT9 t)).length :=
      hn.trans (nSOf_eq h)
    have hsz : I.SP.n ≤ 2 ^ 31 :=
      hszSP.le.trans (h31A _ (ComplJ9AOfStatic.mem_nS Rt hgen))
    have hP63 : 2 ^ 63 < P := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
    have hnp : I.SP.n < P := by
      have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
      omega
    have hp32 : 2 ^ 32 < P := by
      have : (2 : ℕ) ^ 32 < 2 ^ 63 := by norm_num
      omega
    refine spChipOK_I' (withOrb I o) hv' o.SP χe (j9aDataOf P Rg Rt hgen).acs.length
      (GenSpE.vSE (ComplJ9AGen.rowsOfT9 t))
      (GenSpE.mSE (ComplJ9AGen.rowsOfT9 t) (GenSpE.vSE (ComplJ9AGen.rowsOfT9 t))) ?_ ?_ (hspOn.trans h) ?_ hχI
      ho.SP.2 hnp hp32 ?_ ?_
    · show reorb I.SP o.SP = _
      rw [hSP]
    · show I.pubsS = _
      exact hP
    · exact hszA.trans (rfl : (BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Pb.nA = (j9aDataOf P Rg Rt hgen).acs.length)
    · intro i
      have hi : (i : ℕ) < (GenSpE.vSE (ComplJ9AGen.rowsOfT9 t)).length := by
        have := i.2
        change (i : ℕ) < I.SP.n at this
        omega
      show 2 ^ 32 ≤ (ComplJ9AChainsRun.splitVals9 P (ComplJ9AGen.rowsOfT9 t)).getD i 0 ∧
        (ComplJ9AChainsRun.splitVals9 P (ComplJ9AGen.rowsOfT9 t)).getD i 0 < 2 ^ 64
      have hi' : (i : ℕ) < (ComplJ9AChainsRun.splitVals9 P (ComplJ9AGen.rowsOfT9 t)).length := hi
      rw [List.getD_eq_getElem _ _ hi']
      exact ComplJ9AChainsRun.splitVals9_range hgen hpG hax9 _ (List.getElem_mem hi')
    · intro e he
      exact good_fam deltaF powerBasis3 Rt hgen hpG h31A hχ (famSPA deltaF Rt hgen)
        (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)) e
        (famSP_cast _ (fun k => (GenSpE.vSE (ComplJ9AGen.rowsOfT9 t)).getD k 0) hn e he)
  · have hz : ∀ j, K3.toK ((withOrb I o).pubsS j) = 0 := by
      intro j
      show K3.toK (I.pubsS j) = 0
      rw [hSPoff h]
      exact K3.toK_zero
    exact Or.inr ⟨hspOn.trans (Bool.eq_false_iff.mpr h), hz _, hz _⟩

end SplitRun

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHXASE

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHXASE
#print axioms toTrE_C_at
#print axioms hsatXE_at
#print axioms hAXkE_at
#print axioms hSPkE_at
end Axioms
