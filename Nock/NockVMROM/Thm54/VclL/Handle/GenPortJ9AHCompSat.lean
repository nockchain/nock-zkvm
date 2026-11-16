/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHCompSat.lean

* `hsatXA_at`: a copy of `ComplJ9AOfComp.hsatXA` with the honest orbit `powN oA (N9 t)` replaced by arbitrary
    `nodes` / `orbit` (`hinj`, `hadj` as hypotheses; `n = N9 t`).  Every other hypothesis is unchanged.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfComp

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCompSat

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

noncomputable section

section Run
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9 (rowAt9 fl1 llW)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX (HdlOK hk hv)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (chalAlphaW chalGammaW pubIC pubSeed pubOut pubRhoX pubRhoP)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DA" => j9aDataOf p Rg Rt hgen

variable (hpG : p = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))

include hpG h31A in
/-- **`hsatXA` at an arbitrary orbit.**  Same binders as `ComplJ9AOfComp.hsatXA`; the honest orbit `powN oA (N9 t)`
is replaced by arbitrary `nodes` / `orbit` (`hinj`, `hadj`), with `n = N9 t`. -/
theorem hsatXA_at (hax9 : ComplJ9ABinders.ProgAxOK9A p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (χ : Coins frameJ8 K) (hχ : (BRun9A δ b Rt hgen hpG h31A).Good χ)
    {hh n : ℕ} (hn : 0 < n) (hnN : n = N9 t) (nodes : Fin n → ZMod p) (hinj : Function.Injective nodes)
    (orbit : StrictOrbitDomain (ZMod p) 3 hh)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX9 hn nodes b δ (chalVJ8 b χ) (pubCA δ b Rt hgen χ) orbit)
      (trCA δ b Rt hgen χ nodes) := by
  rw [trCA_def]
  have hN : N9 t = (bfsForest [genX9T t]).length := N9_def t
  have hρ := hρA δ b Rt hgen χ
  exact HonestSatX9.computeChipVCLHX9_honest_sat δ (DA).H (DA).pd (idOfA (p := p) Rt hgen) (genX9T t) (nodeVA b Rt hgen χ)
    (αA b χ) (γA b χ) (hordA δ b Rt hgen hpG h31A hχ) hn (hnN.trans hN)
    nodes hinj b (chalVJ8 b χ) (pubCA δ b Rt hgen χ) orbit
    (fun i hi => (hadj i hi).trans (mul_comm _ _)) rfl rfl
    (ClaimJ9.pubVJ9_IC δ b _ _ _ _ χ) (hpSA δ b Rt hgen χ) (ClaimJ9.pubVJ9_out δ b _ _ _ _ χ)
    (ComplJ9ABase.hbase9 hpG hgen hax9 hop5 (DA).H (DA).pd (DA).acs.length (hHA (p := p) Rt hgen)
      (hpairA Rt hgen hpG hop5) (hnN.trans hN) (pubCA δ b Rt hgen χ) (hpubA δ b Rt hgen χ))
    (ComplJ9AReadsAt.readsAt9_honest_zmod (DA).H (DA).pd (DA).acs.length (hHA' (p := p) Rt hgen) (p62_of hpG) (p64_of hpG)
      hgen (αA b χ) (γA b χ))
    (by rw [← hnN] at hρ; simpa [hnN] using hρ) (by rw [hnN]; exact hnbA δ b Rt hgen hpG h31A hχ)

end Run

/-! ## At the exec record -/

section Exec
open Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff Nock.V1J9A.GenJ9AX Nock.V1J9A.GenCompX9
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A (qX9)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCoin
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll

variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **A2 at the exec record.**  The compute-chip conjunct of `AcceptsJ9A` (`hsatX`) for `I = recJ9AX s f χe t r` at
`mkPbA I hv`: same chip and trace as `AcceptsJ9A.hsatX`, with the public vector written as the honest twin publics
`pubCA` at `toχ χe` (`= pubFinal9`, G2 `pubFinal9_eq_pubCA`; `AcceptsJ9A` writes it `pubVJ9 … I.toMsg …`, equal by
`Check9.pubVJ9_eq` + `compGenX9_rho/_rhoS`, which A1/G2 left to the assembly).  The `qX9` agreement is
`recJ9AX_toTr_C`-driven and proved inside. -/
theorem recJ9AX_hsatX
    (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hnc : callsOf (ComplJ8Data.rowsOfT t) = [])
    (χe : CoinsE)
    (hχ : (BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe))
    (hv : ValidJ9A (recJ9AX s f χe t r))
    (hn3 : (recJ9AX s f χe t r).X.n ≤ 3 * 2 ^ (recJ9AX s f χe t r).X.h) :
    RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX9 (mkPbA (recJ9AX s f χe t r) hv).hn (mkPbA (recJ9AX s f χe t r) hv).nodes powerBasis3 deltaF
        (chalVJ8 powerBasis3 (toχ χe)) (pubCA deltaF powerBasis3 Rt hgen (toχ χe))
        (mkPbA (recJ9AX s f χe t r) hv).orbit)
      (qX9 deltaF powerBasis3 (mkPbA (recJ9AX s f χe t r) hv) (recJ9AX s f χe t r).toTr
        (chalVJ8 powerBasis3 (toχ χe)) (pubCA deltaF powerBasis3 Rt hgen (toχ χe))) := by
  have hX := recJ9AX_X_n s f χe t r
  have hinj : Function.Injective (nodesOf (recJ9AX s f χe t r).X) :=
    nodesOf_inj _ hv.oX hn3
  have hadj : ∀ (i : Fin (recJ9AX s f χe t r).X.n) (hi : (i : ℕ) + 1 < (recJ9AX s f χe t r).X.n),
      nodesOf (recJ9AX s f χe t r).X ⟨(i : ℕ) + 1, hi⟩ =
        nodesOf (recJ9AX s f χe t r).X i * (mkPbA (recJ9AX s f χe t r) hv).orbit.ω :=
    fun i hi => (nodesOf_adj _ i hi).trans (mul_comm _ _)
  have key := hsatXA_at (p := P) deltaF powerBasis3 Rt hgen hpG h31A hax9 hop5 (toχ χe) hχ
    (mkPbA (recJ9AX s f χe t r) hv).hn hX (nodesOf (recJ9AX s f χe t r).X) hinj
    (mkPbA (recJ9AX s f χe t r) hv).orbit hadj
  have hq : qX9 deltaF powerBasis3 (mkPbA (recJ9AX s f χe t r) hv) (recJ9AX s f χe t r).toTr
        (chalVJ8 powerBasis3 (toχ χe)) (pubCA deltaF powerBasis3 Rt hgen (toχ χe)) =
      trCA deltaF powerBasis3 Rt hgen (toχ χe) (nodesOf (recJ9AX s f χe t r).X) := by
    funext d
    show (recJ9AX s f χe t r).toTr.C _ = _
    have hp : pubFinal9 ⟨s, f, r⟩ (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
        (idOfA (p := P) Rt hgen) (W9 t) χe = pubCA deltaF powerBasis3 Rt hgen (toχ χe) :=
      pubFinal9_eq_pubCA Rt hgen χe
    rw [trCA_def, recJ9AX_toTr_C Rt hgen hnc χe d, hchi_toχ, hp]
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
  rw [hq]
  exact key

end Exec

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCompSat

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCompSat.hsatXA_at
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCompSat.recJ9AX_hsatX
