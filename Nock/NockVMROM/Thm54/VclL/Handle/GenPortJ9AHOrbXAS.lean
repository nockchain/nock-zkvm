/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHOrbXAS.lean

  Imports `AcceptsJ9A`.

  * `interp_chipOf_compGenX9_at`, `interp_aux_at`, `toTr_C_at`: A1 with the nodes generalized;
  * `hsatX_at`   : the compute conjunct (`hsatX`) at `mkPbA (withOrb I o) hv'`, `I.toMsg`, `toχ`;
  * `hJk_at`     : the absent J chip;
  * `axChipOK_exec'`, `axChipOK_absent'`, `axOK_I'`, `hAXk_at` : the axis chip at the orbit `reorb (chipOf T) O`;
  * `interpOf_spChip'`, `spChipOK_exec'`, `spChipOK_exec_absent'`, `spChipOK_I'`, `hSPk_at`: the split chip likewise.

  Seam note (E2b): the AX / SP part is in a section WITHOUT the `[Algebra Nock.Atoms.Fp …]` binder, exactly like
  B1a/B1b and `ComplJ9AChipsOK` (global instance); `hsatX_at` / `hJk_at` are in the binder section like
  A2 / C5-with-binder.  F1h converts where they meet.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCompSat
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMsg
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAx
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHSp

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbXAS

noncomputable section

/-! ## 1. A1 at arbitrary nodes -/

section Comp

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 rowsOfT9 genX9T)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (W9 N9 N9_def idOfA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.V1J9A.GenCompX9
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD (lnClosed cntClosed)
open Nock.NockVMROM.Thm54.VclL.HonestSatX9 (accW9)
open Nock.NockVMROM.Thm54.VclL.HonestTraceX9 (polyX9)
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.GenJ9AX

/-- A1 `interpOf_chipOf_compGenX9` at arbitrary nodes `ν`. -/
theorem interp_chipOf_compGenX9_at
    [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
    (c : P8PublicClaim) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (χe : CoinsE)
    (ν : Fin (chipOf (compGenX9 c H pd idOf W χe).rows).n → ZMod P) (d : Fin 137) :
    Lagrange.interpolate Finset.univ ν (fun i => (chipOf (compGenX9 c H pd idOf W χe).rows).cols d i) =
      polyX9 powerBasis3 deltaF H pd idOf W (Example.chalE χe) (pubFinal9 c H pd idOf W χe)
        (lnClosed (K3.toK (χe ⟨13, by decide⟩)))
        (cntClosed (Walk.foCol W) (K3.toK (χe ⟨13, by decide⟩)) (K3.toK (χe ⟨13, by decide⟩)))
        (accW9 (fun u => K3.toK (nodeV9E H pd idOf (χe ⟨14, by decide⟩) u)) W (K3.toK (χe ⟨13, by decide⟩)))
        ν 137 d := by
  unfold polyX9
  congr 1
  funext i
  have hi : (i : ℕ) < W.length := by
    have h : (i : ℕ) < (chipOf (compGenX9 c H pd idOf W χe).rows).n := i.2
    exact lt_of_lt_of_eq h
      ((Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp.chipOf_n _).trans
        (Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp.compGenX9_size c H pd idOf W χe))
  exact compGenX9_eq_closed c H pd idOf W χe hi d.2

theorem interp_aux_at [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
    (c : P8PublicClaim) (DH : Noun → ℕ × ℕ) (Dpd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idA : ℕ → ℕ)
    (t' : NTree SkelX) (χe : CoinsE)
    (d : Fin 137) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (hH : H = DH) (hpd : pd = Dpd) (hid : idOf = idA) (X : ChipIn) (hI : X =
      chipOf (compGenX9 c H pd idOf (W9 t') χe).rows) (ν : Fin X.n → ZMod P) :
    Lagrange.interpolate Finset.univ ν (fun i => X.cols d i) =
      polyX9 powerBasis3 deltaF DH Dpd idA (W9 t') (Example.chalE χe)
        (pubFinal9 c DH Dpd idA (W9 t') χe)
        (lnClosed (K3.toK (χe ⟨13, by decide⟩)))
        (cntClosed (Walk.foCol (W9 t')) (K3.toK (χe ⟨13, by decide⟩)) (K3.toK (χe ⟨13, by decide⟩)))
        (accW9 (fun u => K3.toK (nodeV9E DH Dpd idA (χe ⟨14, by decide⟩) u)) (W9 t')
          (K3.toK (χe ⟨13, by decide⟩)))
        ν 137 d := by
  subst hH hpd hid hI
  exact interp_chipOf_compGenX9_at _ _ _ _ _ χe ν d

/-- **A1 at arbitrary nodes**: the exec compute columns, interpolated at any nodes `ν`, are the honest `polyX9`. -/
theorem toTr_C_at [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
    {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
    (hnc : callsOf (ComplJ8Data.rowsOfT t) = []) (χe : CoinsE)
    (ν : Fin (recJ9AX s f χe t r).X.n → ZMod P) (d : Fin 137) :
    Lagrange.interpolate Finset.univ ν (fun i => (recJ9AX s f χe t r).X.cols d i) =
      polyX9 powerBasis3 deltaF (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd (idOfA (p := P) Rt hgen)
        (W9 t) (Example.chalE χe) (pubFinal9 ⟨s, f, r⟩ (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
          (idOfA (p := P) Rt hgen) (W9 t) χe)
        (lnClosed (K3.toK (χe ⟨13, by decide⟩)))
        (cntClosed (Walk.foCol (W9 t)) (K3.toK (χe ⟨13, by decide⟩)) (K3.toK (χe ⟨13, by decide⟩)))
        (accW9 (fun u => K3.toK (nodeV9E (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
          (idOfA (p := P) Rt hgen) (χe ⟨14, by decide⟩) u)) (W9 t) (K3.toK (χe ⟨13, by decide⟩)))
        ν 137 d := by
  obtain ⟨hH, hpd, hid⟩ := Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp.recJ9AX_hdp Rt hgen hnc
  exact interp_aux_at ⟨s, f, r⟩ (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd (idOfA (p := P) Rt hgen)
    t χe d _ _ _ hH hpd hid _ (Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp.recJ9AX_X s f χe t r) ν

end Comp

/-! ## 2. `hsatX` at `withOrb I o` -/

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

variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **`hsatX` of `AcceptsJ9A` at `withOrb I o`** (`Pb := mkPbA I' hv'`, `M := I'.toMsg`, `tr := I'.toTr`,
`χ := toχ I'.χ`, `c := I'.c`, `I' := withOrb (recJ9AX s f χe t r) o`). -/
theorem hsatX_at
    (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hnc : callsOf (ComplJ8Data.rowsOfT t) = [])
    (χe : CoinsE) (o : OrbJ9A) (ho : OrbAdm (recJ9AX s f χe t r) o)
    (hv' : ValidJ9A (withOrb (recJ9AX s f χe t r) o))
    (hχ : (BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX9 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').hn
        (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nodes powerBasis3 deltaF
        (chalVJ8 powerBasis3 (toχ (withOrb (recJ9AX s f χe t r) o).χ))
        (ClaimJ9.pubVJ9 deltaF powerBasis3 (withOrb (recJ9AX s f χe t r) o).c
          (withOrb (recJ9AX s f χe t r) o).toMsg.m (withOrb (recJ9AX s f χe t r) o).toMsg.ρ
          (withOrb (recJ9AX s f χe t r) o).toMsg.ρS (toχ (withOrb (recJ9AX s f χe t r) o).χ))
        (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').orbit)
      (qX9 deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv') (withOrb (recJ9AX s f χe t r) o).toTr
        (chalVJ8 powerBasis3 (toχ (withOrb (recJ9AX s f χe t r) o).χ))
        (ClaimJ9.pubVJ9 deltaF powerBasis3 (withOrb (recJ9AX s f χe t r) o).c
          (withOrb (recJ9AX s f χe t r) o).toMsg.m (withOrb (recJ9AX s f χe t r) o).toMsg.ρ
          (withOrb (recJ9AX s f χe t r) o).toMsg.ρS (toχ (withOrb (recJ9AX s f χe t r) o).χ))) := by
  have hX := recJ9AX_X_n s f χe t r
  obtain ⟨⟨hinj, hadj⟩, -⟩ := Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA.nodes_withOrb ho hv'
  have key := GenPortJ9AHCompSat.hsatXA_at (p := P) deltaF powerBasis3 Rt hgen hpG h31A hax9 hop5 (toχ χe) hχ
    (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').hn hX (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nodes hinj
    (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').orbit hadj
  have hpub : ClaimJ9.pubVJ9 deltaF powerBasis3 (withOrb (recJ9AX s f χe t r) o).c
      (withOrb (recJ9AX s f χe t r) o).toMsg.m (withOrb (recJ9AX s f χe t r) o).toMsg.ρ
      (withOrb (recJ9AX s f χe t r) o).toMsg.ρS (toχ (withOrb (recJ9AX s f χe t r) o).χ) =
      pubCA deltaF powerBasis3 Rt hgen (toχ χe) := by
    have e1 := GenPortJ9AHMsg.msg_m Rt hgen hnc hpG h31A χe
    have e2 := GenPortJ9AHMsg.msg_ρ Rt hgen hnc hpG h31A χe
    have e3 := GenPortJ9AHMsg.msg_ρS Rt hgen hnc hpG h31A χe
    unfold pubCA
    show ClaimJ9.pubVJ9 deltaF powerBasis3 (recJ9AX s f χe t r).c (recJ9AX s f χe t r).toMsg.m
      (recJ9AX s f χe t r).toMsg.ρ (recJ9AX s f χe t r).toMsg.ρS (toχ (recJ9AX s f χe t r).χ) = _
    rw [e1, e2, e3]
    rfl
  have hq : qX9 deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv')
        (withOrb (recJ9AX s f χe t r) o).toTr
        (chalVJ8 powerBasis3 (toχ (withOrb (recJ9AX s f χe t r) o).χ))
        (pubCA deltaF powerBasis3 Rt hgen (toχ χe)) =
      trCA deltaF powerBasis3 Rt hgen (toχ χe) (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nodes := by
    funext d
    refine Eq.trans (toTr_C_at Rt hgen hnc χe (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nodes d) ?_
    have hp : pubFinal9 ⟨s, f, r⟩ (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
        (idOfA (p := P) Rt hgen) (W9 t) χe = pubCA deltaF powerBasis3 Rt hgen (toχ χe) :=
      pubFinal9_eq_pubCA Rt hgen χe
    rw [trCA_def, hchi_toχ, hp]
    have hα := αC0_toχ χe
    have hγ := γC0_toχ χe
    have hnode : ∀ γ0 : K3, K3.toK γ0 = γA powerBasis3 (toχ χe) →
        nodeVA powerBasis3 Rt hgen (toχ χe) =
        fun u => K3.toK (nodeV9E (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
          (idOfA (p := P) Rt hgen) γ0 u) := fun γ0 hg =>
      funext fun u => by
        rw [nodeV9E_eq]
        show ComplJ9AReadsAt.nodeV9 (F := ZMod P) _ _ _ (γA powerBasis3 (toχ χe)) u = _
        rw [hg]
    rw [show αA powerBasis3 (toχ χe) = _ from hα, hnode _ hγ.symm]
    rfl
  rw [hpub, hq]
  exact key

end Sat

/-! ## 3. `hJk` at `withOrb I o` -/

section JChip

open Nock Nock.Field Nock.TraceGenExe Nock.Edit Nock.Edit.GenX Nock.Walk Nock.V1J8 Nock.V1J8.Gen Nock.V1J8.Exe
open Nock.V1J8.Check Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff Nock.V1J9A.GenJ9AX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbJ9A OrbAdm reorb withOrb)

/-- **`hJk` at `withOrb I o`**: the absent J chip (C5 `recJ9AX_jchip` pattern). -/
theorem hJk_at (s f : Noun) (χe : CoinsE) (t : NTree SkelX) (r : Noun) (o : OrbJ9A)
    (hv' : ValidJ9A (withOrb (recJ9AX s f χe t r) o)) :
    JGenJ8.JChipOK deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nodesJ
      (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').orbitJ
      (chalsJJ8 (toχ (withOrb (recJ9AX s f χe t r) o).χ))
      (withOrb (recJ9AX s f χe t r) o).toMsg.pubsJ (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').lay
      (qJ deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').toPubJ8
        (withOrb (recJ9AX s f χe t r) o).toTr.toJ8
        (chalsJJ8 (toχ (withOrb (recJ9AX s f χe t r) o).χ))
        (withOrb (recJ9AX s f χe t r) o).toMsg.pubsJ) :=
  Or.inr ⟨rfl, Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJ.recJ9AX_toMsg_pubsJ s f χe t r _,
    Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJ.recJ9AX_toMsg_pubsJ s f χe t r _,
    Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJ.recJ9AX_toMsg_pubsJ s f χe t r _,
    Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJ.recJ9AX_toMsg_pubsJ s f χe t r _⟩

end JChip

/-! ## 4. The axis chip at `reorb (chipOf T) O` (no `Algebra Fp` binder: as B1a) -/

section Axis

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen Nock.V1J9A
open Nock.V1J9A.CheckJ9AIff Nock.V1J9A.CheckJ9A
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AXChipOK)
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Polynomial
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisRows (ChainSpec)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH (polyAx colAx)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbJ9A OrbAdm reorb withOrb)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAx (chipOf_axGenE_n fullCol_colAx)

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-- B1a `axChipOK_exec` at `q = reorb (chipOf T) O` (`hnq` explicit; `hs` kept for `q.n < p`). -/
theorem axChipOK_exec' (χe : CoinsE) (cs : List (ChainSpec (ZMod p))) (hcs : ∀ c ∈ cs, c.OK)
    (q : ChipIn) (O : Orb) (hqc : q = reorb (chipOf (GenAxE.axGenE χe cs).1) O) (ho : OrbOK q) (hn0 : 0 < q.n)
    (hn : q.n = (ComplJ9AAxisRows.tableRows cs).length) (hs : (GenAxE.axGenE χe cs).1.size ≤ 2 ^ 31)
    (hnq : q.n ≤ 3 * 2 ^ q.h)
    (hg : ∀ e ∈ ComplJ9AChipsOK.famAX deltaF hn0 cs hn (K := KC), toχ χe ∉ e.ev)
    (chals pubs : ℕ → KC) (hch : chals = VerJ8.chalsMJ8 deltaF (toχ χe))
    (hpub : pubs = fun j => K3.toK (GenAxE.pubsXE χe (ComplJ9AAxisRows.tableRows cs) j))
    (P : Fin (AxisChipJ9.axisChipJ9 deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) chals pubs).rap.w → (ZMod p)[X])
    (hP : ∀ j, P j = interpOf q (j : ℕ)) :
    AXChipOK deltaF powerBasis3 true hn0 (nodesOf q) (mkOrbit q ho) chals pubs P := by
  have hinj : Function.Injective (nodesOf q) := nodesOf_inj q ho hnq
  have hadj : ∀ (i : Fin q.n) (hi : (i : ℕ) + 1 < q.n),
      nodesOf q ⟨(i : ℕ) + 1, hi⟩ = nodesOf q i * (mkOrbit q ho).ω := by
    intro i hi
    rw [nodesOf_adj q i hi, mul_comm]; rfl
  have hnp : q.n < p := by
    have e : q.n = (GenAxE.axGenE χe cs).1.size := by rw [hqc]; rfl
    have h2 : (2 : ℕ) ^ 31 < p := by norm_num [Nock.Field.p]
    omega
  have hpubs : pubs = ComplJ9AChipsOK.pubsXOf deltaF hn0 cs hn (toχ χe) :=
    hpub.trans (funext fun j => pubsXE_eq χe cs hn0 hn j)
  have hcolq : ∀ (c : ℕ) (i : Fin q.n), c < 52 → q.cols c i =
      colAx deltaF powerBasis3 chals hn0
        (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn) c i := by
    intro c i hc
    subst hch
    subst hqc
    exact axGenE_cols χe cs (n := (chipOf (GenAxE.axGenE χe cs).1).n) hn0 hn i c hc
  have hint : ∀ j : Fin (AxisChipJ9.axisChipJ9 deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) chals pubs).rap.w,
      interpOf q (j : ℕ) = polyAx deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) chals pubs
        (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn) j := by
    intro j
    have hj : (j : ℕ) < 52 := j.2
    unfold polyAx Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.honestQ interpOf
    congr 1
    funext i
    rw [fullCol_colAx χe (ComplJ9AAxisRows.tableRows cs) hn0 hn chals j hj i]
    exact hcolq j i hj
  have hPe : P = polyAx deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) chals pubs
      (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn) := funext fun j => (hP j).trans (hint j)
  rw [hPe]
  subst hch
  subst hpubs
  exact ComplJ9AChipsOK.axChipOK_honest deltaF powerBasis3 hn0 cs hn hcs (nodesOf q) (mkOrbit q ho) hinj hadj hnp
    (toχ χe) hg

/-- The absent axis chip (copy of B1a `axChipOK_absent`). -/
theorem axChipOK_absent' (q : ChipIn) (ho : OrbOK q) (hn0 : 0 < q.n) (chals pubs : ℕ → KC)
    (hpub : ∀ j, pubs j = 0)
    (P : Fin (AxisChipJ9.axisChipJ9 deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) chals pubs).rap.w → (ZMod p)[X]) :
    AXChipOK deltaF powerBasis3 false hn0 (nodesOf q) (mkOrbit q ho) chals pubs P :=
  Or.inr ⟨rfl, hpub _, hpub _, hpub _, hpub _⟩

/-- B1a `axOK_I` at an input record `I'` whose axis chip is `reorb (chipOf T) O`. -/
theorem axOK_I' (I : InJ9A) (hv : ValidJ9A I) (O : Orb) (χe : CoinsE) (nA : ℕ) (H : Noun → ℕ × ℕ)
    (rows9 : Array ComplJ9AGen.LX9) (on : Bool)
    (hAX : I.AX = reorb (chipOf (GenAxE.axGenOf χe nA H rows9 on).1) O)
    (hpub : I.pubsX = (GenAxE.axGenOf χe nA H rows9 on).2) (hon : I.axOn = on) (hχ : I.χ = χe)
    (hnq : I.AX.n ≤ 3 * 2 ^ I.AX.h)
    (hs : on = true → (GenAxE.axGenOf χe nA H rows9 on).1.size ≤ 2 ^ 31)
    (hcs : on = true → ∀ c ∈ ComplJ9AChainsRun.axChains9 p nA H rows9, c.OK)
    (hg : on = true → ∀ (hn0 : 0 < I.AX.n)
      (hn : I.AX.n = (ComplJ9AAxisRows.tableRows (ComplJ9AChainsRun.axChains9 p nA H rows9)).length),
      ∀ e ∈ ComplJ9AChipsOK.famAX deltaF hn0 (ComplJ9AChainsRun.axChains9 p nA H rows9) hn (K := KC),
        toχ χe ∉ e.ev) :
    AXChipOK deltaF powerBasis3 (mkPbA I hv).axOn (mkPbA I hv).hnX (mkPbA I hv).nodesX (mkPbA I hv).orbitX
      (VerJ8.chalsMJ8 deltaF (toχ I.χ)) I.toMsg.pubsX
      (fun j => I.toTr.X (Fin.cast (AxisChipJ9.width_eq deltaF powerBasis3 hv.nAX (nodesOf I.AX)
        (mkOrbit I.AX hv.oAX) (VerJ8.chalsMJ8 deltaF (toχ I.χ)) I.toMsg.pubsX) j)) := by
  have hch : VerJ8.chalsMJ8 deltaF (toχ I.χ) = VerJ8.chalsMJ8 deltaF (toχ χe) := by rw [hχ]
  show AXChipOK deltaF powerBasis3 I.axOn hv.nAX (nodesOf I.AX) (mkOrbit I.AX hv.oAX)
      (VerJ8.chalsMJ8 deltaF (toχ I.χ)) (fun i => K3.toK (I.pubsX i)) _
  rw [hon]
  cases hon' : on
  · have hz : ∀ j, K3.toK (I.pubsX j) = 0 := by
      intro j
      rw [hpub]
      simp [GenAxE.axGenOf, hon', GenAxE.zeroChip, K3.toK_zero]
    exact axChipOK_absent' I.AX hv.oAX hv.nAX _ _ hz _
  · rw [hon'] at hAX hpub hs hcs hg
    have hs' : (GenAxE.axGenE χe (ComplJ9AChainsRun.axChains9 p nA H rows9)).1.size ≤ 2 ^ 31 := by
      simpa [GenAxE.axGenOf] using hs rfl
    simp only [GenAxE.axGenOf, if_true] at hAX hpub
    have hn : I.AX.n = (ComplJ9AAxisRows.tableRows (ComplJ9AChainsRun.axChains9 p nA H rows9)).length := by
      rw [hAX]; exact chipOf_axGenE_n _ _
    exact axChipOK_exec' χe _ (hcs rfl) I.AX O hAX hv.oAX hv.nAX hn hs' hnq (hg rfl hv.nAX hn) _ _ hch
      (by funext j; rw [hpub]; rfl) _ (fun j => rfl)

/-- `famAX` does not depend on the row-count variable beyond the proofs `0 < n`, `n = rows`. -/
theorem famAX_irrel {n m : ℕ} (hn0 : 0 < n) (hm0 : 0 < m) (cs : List (ChainSpec (ZMod p)))
    (hn : n = (ComplJ9AAxisRows.tableRows cs).length) (hm : m = (ComplJ9AAxisRows.tableRows cs).length) :
    ComplJ9AChipsOK.famAX deltaF hn0 cs hn (K := KC) = ComplJ9AChipsOK.famAX deltaF hm0 cs hm (K := KC) := by
  subst hn
  subst hm
  rfl

end Axis

/-! ## 5. The axis chip of `recJ9AX` at `withOrb I o` (global instance, as `ComplJ9AOf.axOK_A`) -/

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

/-- **`hAXk` of `AcceptsJ9A` at `withOrb I o`.** -/
theorem hAXk_at (hpG : P = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf P Rg Rt hgen))
    (hnc : callsOf (ComplJ8Data.rowsOfT t) = []) (χe : CoinsE) (o : OrbJ9A)
    (ho : OrbAdm (recJ9AX s f χe t r) o)
    (hv' : ValidJ9A (withOrb (recJ9AX s f χe t r) o))
    (hχ : (BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    AXChipOK deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').axOn
      (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').hnX (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nodesX
      (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').orbitX
      (VerJ8.chalsMJ8 deltaF (toχ (withOrb (recJ9AX s f χe t r) o).χ))
      (withOrb (recJ9AX s f χe t r) o).toMsg.pubsX
      (fun j => (withOrb (recJ9AX s f χe t r) o).toTr.X
        (Fin.cast (AxisChipJ9.width_eq deltaF powerBasis3 hv'.nAX (nodesOf (withOrb (recJ9AX s f χe t r) o).AX)
          (mkOrbit (withOrb (recJ9AX s f χe t r) o).AX hv'.oAX)
          (VerJ8.chalsMJ8 deltaF (toχ (withOrb (recJ9AX s f χe t r) o).χ))
          (withOrb (recJ9AX s f χe t r) o).toMsg.pubsX) j)) := by
  have hsz : (recJ9AX s f χe t r).AX.n ≤ 2 ^ 31 :=
    (GenPortJ9AHMsg.size_AX Rt hgen hnc hpG h31A χe).le.trans
      (h31A _ (ComplJ9AOfStatic.mem_nX Rt hgen))
  refine axOK_I' (withOrb (recJ9AX s f χe t r) o) hv' o.AX χe (j9aDataOf P Rg Rt hgen).acs.length
    (j9aDataOf P Rg Rt hgen).H (ComplJ9AGen.rowsOfT9 t) (axOnA t) ?_ ?_ rfl rfl ho.AX.2 ?_ ?_ ?_
  · show reorb (recJ9AX s f χe t r).AX o.AX = _
    rw [recX_AX, GenPortJ9AHMsg.xRPJ_eq Rt hgen hnc χe]
  · show (recJ9AX s f χe t r).pubsX = _
    rw [recX_pubsX, GenPortJ9AHMsg.xRPJ_eq Rt hgen hnc χe]
  · intro _
    have := GenPortJ9AHMsg.le_tbl _ _ (recX_AX s f χe t r) hsz
    rwa [GenPortJ9AHMsg.xRPJ_eq Rt hgen hnc χe] at this
  · intro _
    exact ComplJ9AChainsRun.axChains9_OK (p0 := P) (j9aDataOf P Rg Rt hgen).acs.length (j9aDataOf P Rg Rt hgen).H
      hgen hpG (fun a c => (ComplJ8CompRun.hH_run (p := P) Rt hgen).cell a c)
  · intro h hn0 hn e he
    rw [famAX_irrel hn0 (nXA_pos (p := P) Rt hgen) _ hn (nXA_eq (p := P) Rt hgen h)] at he
    exact good_fam deltaF powerBasis3 Rt hgen hpG h31A hχ (famAXA deltaF Rt hgen)
      (List.mem_append_right _ List.mem_cons_self) e (by simp only [famAXA, dif_pos h]; exact he)

end AxisRun

/-! ## 6. The split chip at `reorb (chipOf T) O` -/

section Split

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen Nock.V1J9A
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (SPChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb
open Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH (polyS polySC)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbJ9A OrbAdm reorb withOrb)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHSp (spGenE_size)

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-- B1b `interpOf_spChip` at `q = reorb (chipOf T) O`. -/
theorem interpOf_spChip' (χe : CoinsE) (nA : ℕ) (vS mS : List ℕ) (q : ChipIn) (O : Orb)
    (hq : q = reorb (chipOf (GenSpE.spGenE χe nA vS mS).1) O) (w : ℕ) (hw : w ≤ 90) (c : Fin w) :
    interpOf q c =
      polyS deltaF nA powerBasis3 (VerJ8.chalsMJ8 deltaF (toχ χe))
        (fun i : Fin q.n => vS.getD i 0) (fun i : Fin q.n => mS.getD i 0) (nodesOf q) w c := by
  subst hq
  have hn : (chipOf (GenSpE.spGenE χe nA vS mS).1).n = vS.length := spGenE_size χe nA vS mS
  unfold interpOf polyS
  congr 1
  funext i
  have := spGenE_cols χe nA vS mS (n := (chipOf (GenSpE.spGenE χe nA vS mS).1).n) hn i c (by omega)
  exact this

/-- B1b `spChipOK_exec` at `q = reorb (chipOf T) O`. -/
theorem spChipOK_exec' (χe : CoinsE) (nA : ℕ) (vS mS : List ℕ) (q : ChipIn) (O : Orb)
    (hq : q = reorb (chipOf (GenSpE.spGenE χe nA vS mS).1) O) (ho : OrbOK q) (hn0 : 0 < q.n)
    (hnq : q.n ≤ 3 * 2 ^ q.h) (hnp : q.n < p) (hp : 2 ^ 32 < p)
    (hv : ∀ i : Fin q.n, 2 ^ 32 ≤ vS.getD i 0 ∧ vS.getD i 0 < 2 ^ 64)
    (hχ : ∀ e ∈ ComplJ9AChipsOK.famSP deltaF nA (fun i : Fin q.n => vS.getD i 0) (K := KC),
      toχ χe ∉ e.ev) :
    SPChipOK deltaF powerBasis3 nA true hn0 (nodesOf q) (mkOrbit q ho)
      (VerJ8.chalsMJ8 deltaF (toχ χe)) (fun j => K3.toK ((GenSpE.spGenE χe nA vS mS).2 j))
      (fun j => interpOf q j) := by
  have hn : q.n = vS.length := by rw [hq]; exact spGenE_size χe nA vS mS
  have hpub : (fun j => K3.toK ((GenSpE.spGenE χe nA vS mS).2 j)) =
      ComplJ9AChipsOK.pubsSOf deltaF nA (fun i : Fin q.n => vS.getD i 0)
        (fun i : Fin q.n => mS.getD i 0) (toχ χe) := by
    funext j
    exact pubsSE_eq χe nA vS mS hn hn0 j
  have hinj := nodesOf_inj q ho hnq
  have hadj : ∀ (i : Fin q.n) (hi : (i : ℕ) + 1 < q.n),
      nodesOf q ⟨(i : ℕ) + 1, hi⟩ = nodesOf q i * (mkOrbit q ho).ω := by
    intro i hi
    rw [nodesOf_adj q i hi]
    exact mul_comm _ _
  have key := ComplJ9AChipsOK.spChipOK_honest deltaF powerBasis3 nA (fun i : Fin q.n => vS.getD i 0)
    (fun i : Fin q.n => mS.getD i 0) hn0 (nodesOf q) (mkOrbit q ho) hp hv hinj hadj hnp (toχ χe) hχ
  have hQ : (fun j : Fin (SplitChipJ9.splitChipJ9 deltaF nA powerBasis3 hn0 (nodesOf q) (mkOrbit q ho)
      (VerJ8.chalsMJ8 deltaF (toχ χe)) (ComplJ9AChipsOK.pubsSOf deltaF nA (fun i : Fin q.n => vS.getD i 0)
        (fun i : Fin q.n => mS.getD i 0) (toχ χe))).rap.w => interpOf q j) =
      polySC deltaF nA powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) (VerJ8.chalsMJ8 deltaF (toχ χe))
        (ComplJ9AChipsOK.pubsSOf deltaF nA (fun i : Fin q.n => vS.getD i 0)
          (fun i : Fin q.n => mS.getD i 0) (toχ χe)) (fun i : Fin q.n => vS.getD i 0)
        (fun i : Fin q.n => mS.getD i 0) := by
    funext c
    exact interpOf_spChip' χe nA vS mS q O hq _ (Nat.le_of_eq rfl) c
  rw [hpub, hQ]
  exact key

/-- The absent split chip (copy of B1b `spChipOK_exec_absent`). -/
theorem spChipOK_exec_absent' (nA : ℕ) (q : ChipIn) (ho : OrbOK q) (hn0 : 0 < q.n) (chals : ℕ → KC)
    (QS : Fin (SplitChipJ9.splitChipJ9 deltaF nA powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) chals
      (fun j => K3.toK ((fun _ => (0 : K3)) j))).rap.w → Polynomial (ZMod p)) :
    SPChipOK deltaF powerBasis3 nA false hn0 (nodesOf q) (mkOrbit q ho) chals
      (fun j => K3.toK ((fun _ => (0 : K3)) j)) QS :=
  Or.inr ⟨rfl, K3.toK_zero, K3.toK_zero⟩

/-- B1b `spChipOK_I` at an input record `I` whose split chip is `reorb (chipOf T) O`. -/
theorem spChipOK_I' (I : InJ9A) (hv : ValidJ9A I) (O : Orb) (χe : CoinsE) (nA : ℕ) (vS mS : List ℕ)
    (hSP : I.SP = reorb (chipOf (GenSpE.spGenE χe nA vS mS).1) O)
    (hP : I.pubsS = (GenSpE.spGenE χe nA vS mS).2)
    (hon : I.spOn = true) (hA : I.A.n = nA) (hχ' : I.χ = χe)
    (hnq : I.SP.n ≤ 3 * 2 ^ I.SP.h) (hnp : I.SP.n < p) (hp : 2 ^ 32 < p)
    (hvv : ∀ i : Fin I.SP.n, 2 ^ 32 ≤ vS.getD i 0 ∧ vS.getD i 0 < 2 ^ 64)
    (hχ : ∀ e ∈ ComplJ9AChipsOK.famSP deltaF nA (fun i : Fin I.SP.n => vS.getD i 0) (K := KC),
      toχ χe ∉ e.ev) :
    SPChipOK deltaF powerBasis3 (mkPbA I hv).nA (mkPbA I hv).spOn (mkPbA I hv).hnS (mkPbA I hv).nodesS
      (mkPbA I hv).orbitS (VerJ8.chalsMJ8 deltaF (toχ I.χ)) (fun j => K3.toK (I.pubsS j))
      (fun j => interpOf I.SP j) := by
  have h := spChipOK_exec' χe nA vS mS I.SP O hSP hv.oSP hv.nSP hnq hnp hp hvv hχ
  subst hχ'
  have e1 : (mkPbA I hv).nA = nA := hA
  rw [hP]
  rw [e1]
  have e2 : (mkPbA I hv).spOn = true := hon
  rw [e2]
  exact h

/-- `famSP` along a cast of the row count. -/
theorem famSP_cast (nA : ℕ) (g : ℕ → ℕ) {n m : ℕ} (h : n = m)
    (e : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad.BadSpec KC)
    (he : e ∈ ComplJ9AChipsOK.famSP deltaF nA (fun i : Fin n => g i) (K := KC)) :
    e ∈ ComplJ9AChipsOK.famSP deltaF nA (fun i : Fin m => g i) (K := KC) := by
  subst h; exact he

end Split

/-! ## 7. The split chip of `recJ9AX` at `withOrb I o` -/

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

/-- **`hSPk` of `AcceptsJ9A` at `withOrb I o`** (present via `spChipOK_exec'`, absent by zero publics). -/
theorem hSPk_at (hpG : P = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf P Rg Rt hgen))
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t)
    (hnc : callsOf (ComplJ8Data.rowsOfT t) = []) (χe : CoinsE) (o : OrbJ9A)
    (ho : OrbAdm (recJ9AX s f χe t r) o)
    (hv' : ValidJ9A (withOrb (recJ9AX s f χe t r) o))
    (hχ : (BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    SPChipOK deltaF powerBasis3 (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nA
      (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').spOn (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').hnS
      (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nodesS (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').orbitS
      (VerJ8.chalsMJ8 deltaF (toχ (withOrb (recJ9AX s f χe t r) o).χ))
      (withOrb (recJ9AX s f χe t r) o).toMsg.pubsS
      (fun j => (withOrb (recJ9AX s f χe t r) o).toTr.S
        (Fin.cast (SplitChipJ9.width_eq deltaF (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nA powerBasis3
          (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').hnS (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').nodesS
          (mkPbA (withOrb (recJ9AX s f χe t r) o) hv').orbitS
          (VerJ8.chalsMJ8 deltaF (toχ (withOrb (recJ9AX s f χe t r) o).χ))
          (withOrb (recJ9AX s f χe t r) o).toMsg.pubsS) j)) := by
  by_cases h : spOnA P t = true
  · have hn : (recJ9AX s f χe t r).SP.n = nSOf P t :=
      (GenPortJ9AHMsg.size_SP Rt hgen hnc hpG h31A χe).trans (GenPortJ9AHMsg.Pb_nS Rt hgen hnc hpG h31A)
    have hvl : (recJ9AX s f χe t r).SP.n = (GenSpE.vSE (rows9J s f χe (RnOf t r))).length :=
      hn.trans (nSOf_eq h)
    have hsz : (recJ9AX s f χe t r).SP.n ≤ 2 ^ 31 :=
      (GenPortJ9AHMsg.size_SP Rt hgen hnc hpG h31A χe).le.trans
        (h31A _ (ComplJ9AOfStatic.mem_nS Rt hgen))
    have hP63 : 2 ^ 63 < P := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
    have hnp : (recJ9AX s f χe t r).SP.n < P := by
      have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
      omega
    have hp32 : 2 ^ 32 < P := by
      have : (2 : ℕ) ^ 32 < 2 ^ 63 := by norm_num
      omega
    refine spChipOK_I' (withOrb (recJ9AX s f χe t r) o) hv' o.SP χe (j9aDataOf P Rg Rt hgen).acs.length
      (GenSpE.vSE (rows9J s f χe (RnOf t r)))
      (GenSpE.mSE (rows9J s f χe (RnOf t r)) (GenSpE.vSE (rows9J s f χe (RnOf t r)))) ?_ ?_ h ?_ rfl
      ho.SP.2 hnp hp32 ?_ ?_
    · show reorb (recJ9AX s f χe t r).SP o.SP = _
      rw [recX_SP, sRPJ_of_spOn s f χe (RnOf t r) h, GenPortJ9AHCellRun.acs_eq Rt hgen hnc χe]
    · show (recJ9AX s f χe t r).pubsS = _
      rw [recX_pubsS, sRPJ_of_spOn s f χe (RnOf t r) h, GenPortJ9AHCellRun.acs_eq Rt hgen hnc χe]
    · exact (GenPortJ9AHMsg.size_A Rt hgen hnc hpG h31A χe).trans (GenPortJ9AHMsg.Pb_nA Rt hgen hnc hpG h31A)
    · intro i
      have hi : (i : ℕ) < (GenSpE.vSE (rows9J s f χe (RnOf t r))).length := by
        have := i.2
        change (i : ℕ) < (recJ9AX s f χe t r).SP.n at this
        omega
      show 2 ^ 32 ≤ (ComplJ9AChainsRun.splitVals9 P (ComplJ9AGen.rowsOfT9 t)).getD i 0 ∧
        (ComplJ9AChainsRun.splitVals9 P (ComplJ9AGen.rowsOfT9 t)).getD i 0 < 2 ^ 64
      have hi' : (i : ℕ) < (ComplJ9AChainsRun.splitVals9 P (ComplJ9AGen.rowsOfT9 t)).length := hi
      rw [List.getD_eq_getElem _ _ hi']
      exact ComplJ9AChainsRun.splitVals9_range hgen hpG hax9 _ (List.getElem_mem hi')
    · intro e he
      exact good_fam deltaF powerBasis3 Rt hgen hpG h31A hχ (famSPA deltaF Rt hgen)
        (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)) e
        (famSP_cast _ (fun k => (GenSpE.vSE (rows9J s f χe (RnOf t r))).getD k 0) hn e he)
  · have h' : spOnJ s f χe (RnOf t r) = false := Bool.eq_false_iff.mpr h
    have hz : ∀ j, K3.toK ((withOrb (recJ9AX s f χe t r) o).pubsS j) = 0 := by
      intro j
      show K3.toK ((recJ9AX s f χe t r).pubsS j) = 0
      rw [recX_pubsS, sRPJ_of_not_spOn s f χe (RnOf t r) h']
      exact K3.toK_zero
    exact Or.inr ⟨h', hz _, hz _⟩

end SplitRun

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbXAS

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbXAS
#print axioms interp_chipOf_compGenX9_at
#print axioms interp_aux_at
#print axioms toTr_C_at
#print axioms hsatX_at
#print axioms hJk_at
#print axioms axChipOK_exec'
#print axioms axChipOK_absent'
#print axioms axOK_I'
#print axioms hAXk_at
#print axioms interpOf_spChip'
#print axioms spChipOK_exec'
#print axioms spChipOK_exec_absent'
#print axioms spChipOK_I'
#print axioms famSP_cast
#print axioms hSPk_at
end Axioms
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbXAS.famAX_irrel
