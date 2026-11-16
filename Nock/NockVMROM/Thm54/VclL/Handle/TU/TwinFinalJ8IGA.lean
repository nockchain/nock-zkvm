/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/TwinFinalJ8IGA.lean

 Extraction twin of `FinalJ8IGA.acceptsJ8_holdsN_EIGA` (the assembly with the atom walk absent). The hypotheses
 and the proof text are those of the source theorem; only the last step differs: it calls
 `TwinRowSemIJ8.acceptsJ8_holdsN_computeI_ex`, so the conclusion also carries the compute walk's row accumulator
 `RowsAccXI`, its forest goal, and the row tree with its `RowsOKX` and `GenuineNX` facts (`TreeFacts`), next to
 `HoldsN`. The corollary `acceptsJ8_holdsN_EIGA_of_ex` re-derives the form that hides the intermediate objects.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8E
import Nock.NockVMROM.Thm54.VclL.Handle.RowSemIJ8
import Nock.NockVMROM.Thm54.VclL.Handle.JetProvIJ8
import Nock.NockVMROM.Thm54.VclL.Handle.JGenJ8
import Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinRowSemIJ8
import Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8IGA

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinFinalJ8IGA

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 toVSQ)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf compReqsX)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 pad8_entry7 pad8_sum atomIncProvs provP_append)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX DenOKX)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB provK Accepted)
open Nock.Jet.RapJetJ8 (jRd jProv jCons rowsJ coinsJ accepted_of_sat jet_tagged_sum)
open Nock.Jet.FibreJ8 (effP)
open Nock.Jet.PinJ8 (pinKey pinCons)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8 (axOK_x axOK_s)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemIJ8 (acceptsJ8_holdsN_computeI RowsAccXI)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinRowSemIJ8 (acceptsJ8_holdsN_computeI_ex TreeFacts)
open Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8E (withS provP_filter)

noncomputable section

/-! ## 2. The assembly -/

section Final
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`acceptsJ8_holdsN_EIGA`, with the intermediate objects exposed**: the assembly with NO atom walk. As `FinalJ8IG.acceptsJ8_holdsN_EIG`, with the `s`
providers `jProv ++ pad8 atomIncProvs` (`hprovS`), the atom walk's `s` publics `0` in `hGS` (`hV0`), and no `hAW`. -/
theorem acceptsJ8_holdsN_EIGA_ex [CharP K p] [CharP 𝕂′ p]
    (χ : Coins frameJ8 K) (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′)
    -- the compute trace
    {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
    {P : Fin (computeChipVCLHX hn nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit).rap.w → (ZMod p)[X]}
    {α γ seed : K}
    (C : XCtx hn nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P α γ seed) (hp : 2 ^ 63 + 1 < p)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    -- the cell table
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hchC : ∀ j, 33 ≤ j → j ≤ 36 → chalsC j = chalsMJ8 δ χ j)
    -- the J-8 walk
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hF : GeneratedField.PrimeFieldElems (ZMod p)) (hp64 : 64 ≤ ringChar (ZMod p))
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    (hchW : ∀ j, 33 ≤ j → j ≤ 36 → chalsW j = chalsMJ8 δ χ j)
    -- the J chip and its public registry
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.w → (ZMod p)[X])
    (hJk : JGenJ8.JChipOK δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    {Rt : ℕ → Nock.Jet.Autogen.Tpl} {regs ids : List ℕ} {idx : ℕ → ℕ}
    -- the atom table
    {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA)
    (chalsA pubsA : ℕ → K)
    (QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (hsatA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbindA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinjA : Function.Injective nodesA)
    (hadjA : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hchA : ∀ j, 33 ≤ j → j ≤ 36 → chalsA j = chalsMJ8 δ χ j)
    -- the atom walk ABSENT: its two `s` publics are `0`
    (pubsV : ℕ → K) (hV0 : pubsV WalkHQ.pubPQ = 0 ∧ pubsV (WalkHQ.pubPQ + 1) = 0)
    -- the wiring (the pins are `s` consumes)
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++
      jRd b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hprovP : provs .p = ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW)
    (hextP : ext .p = [])
    (hprovS : provs .s = jProv b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ ++
      pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA))
    (hextS : ext .s = pinCons (p := p) (K := K) regs idx ++ jCons b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    -- the verifier's public equations (the `s` one carries the pins' sum)
    (hGx : ρ 3 + (Quad.mk _ (pubsW WalkHQ.pubXQ) (pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (pubsJ 2) (pubsJ 3)) =
      Quad.mk _ (pubsC CellHQ.pubHQ) (pubsC (CellHQ.pubHQ + 1)))
    (hGp : ρ 4 = Quad.mk _ (pubsW WalkHQ.pubPQ) (pubsW (WalkHQ.pubPQ + 1)))
    (hGS : ρS + ((pinCons (p := p) (K := K) regs idx).map fun r =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (pubsJ 0) (pubsJ 1) =
      Quad.mk _ (pubsA AtomChipHQ.pubMI) (pubsA (AtomChipHQ.pubMI + 1)) +
        Quad.mk _ (pubsV WalkHQ.pubPQ) (pubsV (WalkHQ.pubPQ + 1)))
    -- the IO events and counts at the compute coins: `x`, `p` as before, `s` at the effective providers
    (hout : ∀ bl, bl ≠ .s → ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (houtS : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) ext .s) (effP (liftP (provs .s))))
    (hcount : ∀ bl, (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) ext bl).length < p)
    -- the denotation
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {comb : ℕ → Noun}
    (hRg : Rg.Faithful) (hD : DenOKX p D)
    -- the x and p provider obligations
    (hX : ProvP (p := p) (K := K) (RecOKA D Rg comb) .x (cellProvsW b nodesC orbitC chalsC pubsC QC))
    (hP : ProvP (p := p) (K := K) (RecOKA D Rg comb) .p (ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW))
    (hPax : ProvP (p := p) (K := K) AxOK .p (ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW))
    -- the J chip's public checks and registry
    (hlay : List.ofFn lay = layoutJ8 Rt regs ids)
    (hsmall : ∀ q ∈ layoutJ8 Rt regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 Rt regs ids).filterMap tvKey).Nodup)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p)
    (hRegP : Accepted Rt regs ids (rowsJ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ) →
      (∀ id ∈ regs, ∃ r' ∈ rowsJ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ,
        pinKey (F := ZMod p) id (idx id) ∈ provK r') →
      ∀ r ∈ rowsJ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ, r.pre.kd = .reg →
        D (r.w.kN.val, r.w.vN.val) = some (Nock.Jet.Autogen.compile p (Rt r.pre.id)))
    -- the inc heads
    (hI : ProvP (p := p) (K := K) (RecOKI D Rg comb) .s (pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA)))
    -- the compute walk, its events and the root binding
    (hseed : seed = Walk.rlc γ (encT (K := K)
      (rowW (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0)
        (stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0))).trip) * α)
    (hα : α ∉ tileSet (foOf (rowsWX (fun r => envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r)
      (fun r => stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r)))) n)
    (hw : (α, γ) ∉ cwEvent (K := K)
      (rowsWX (fun r => envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r)
        (fun r => stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r))) n)
    (hreal : (stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0)).isChain = false)
    (x : P8PublicClaim)
    (hs : D (hdV (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0) xS) = some x.subject)
    (hf : D (hdV (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0) xF) = some x.formula)
    (he : D (hdV (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0) xE) = some x.result) :
    RowsAccXI n (fun r => (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P) r) (fun r => stX ((envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P) r)) D Rg comb ∧
    ForestReconGoal (stVS K) (lblOf (rowsWX (fun r => (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P) r) (fun r => stX ((envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P) r)))) 1 n ∧
    TreeFacts K n (fun r => (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P) r) (fun r => stX ((envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P) r)) D Rg ∧ Nock.Jet.HoldsN x := by
  have B := AcceptJ8.bctx_of_xctx C
  have hp3 : 3 < p := by omega
  have hcv := coinsCV_J8 δ b χ
  have hcJ : coinsJ δ (chalsJJ8 χ) = coinsCV b δ (chalVJ8 b χ) := (coinsJ_J8 δ χ).trans hcv.symm
  have hcA := (BalSJ8.acoins_of_agree χ chalsA hchA).trans hcv.symm
  -- the other service providers
  obtain ⟨provO, hpO⟩ : ∃ l, l = pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA) := ⟨_, rfl⟩
  have hO7 : ∀ q ∈ provO, q.1 ⟨7, by norm_num⟩ = 0 := by
    intro q hq'
    rw [hpO] at hq'
    exact pad8_entry7 _ q hq'
  -- the `s` balance with the pins
  have hS : ρS + (List.map (α := Fin 8 → K) (fun r => (compress (coinsCV b δ (chalVJ8 b χ))
        (liftRec (L := 𝕂′) r))⁻¹) (ext .s)).sum =
      (List.map (α := (Fin 8 → K) × K) (fun q => algebraMap K 𝕂′ q.2 *
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) q.1))⁻¹) (provs .s)).sum := by
    have h3 := JGenJ8.jet_tagged_sumG hJk
    have hI' := ServiceJ8.atomIncProvs_sum δ b hnA nodesA orbitA chalsA pubsA QA hsatA hbindA hinjA hadjA
    rw [hcJ] at h3
    rw [hcA] at hI'
    have hGS0 := hGS
    rw [hV0.1, hV0.2, Quad.mk_zero', add_zero] at hGS0
    rw [hprovS, hextS, List.map_append, List.map_append, List.sum_append, List.sum_append, pad8_sum, h3, hI']
    linear_combination hGS0
  have hbal : BalJ8 (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pubVJ8 δ b c m ρ ρS χ) provs ext :=
    JGenJ8.balJ8_frameJ8G χ c m ρ ρS hnC nodesC orbitC chalsC pubsC QC hsatC hbindC hinjC hadjC hchC
      kroots hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW hchW
      nodesJ orbitJ pubsJ lay PJ hJk hprovX hextX hprovP hextP _ _ rfl rfl hGx hGp hS
  rw [← hpO] at hprovS
  -- denominators of the compute consumes
  have hne : ∀ bl, ∀ r ∈ compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalVJ8 b χ)
      (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) bl,
      compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r) ≠ 0 := by
    intro bl r hr
    cases bl with
    | s => exact TeleC.den_ne_of_out _ _ _ _ houtS _ (List.mem_map_of_mem (List.mem_append_left _ hr))
    | x =>
      exact TeleC.den_ne_of_out _ _ _ _ (hout .x (by intro h; cases h)) _
        (List.mem_map_of_mem (List.mem_append_left _ hr))
    | p =>
      exact TeleC.den_ne_of_out _ _ _ _ (hout .p (by intro h; cases h)) _
        (List.mem_map_of_mem (List.mem_append_left _ hr))
  have hc := DenXJ8.compReqsX_sum B hne .s
  change _ = ServedJ8.rhoX (b := b) (δ := δ) (pubVal := pubVJ8 δ b c m ρ ρS χ) .s at hc
  rw [rhoX_s_J8] at hc
  -- the compute's `s` consumes as `Fin 8` keys
  obtain ⟨cS, hcS⟩ : ∃ l : List (Fin 8 → K), l = compReqsX (K := K) (hn := hn) (nodes := nodes)
      (chalV := chalVJ8 b χ) (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) .s := ⟨_, rfl⟩
  have hc8 : (cS.map fun r => (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum = ρS := by
    rw [hcS]; exact hc
  -- the J share: `hG`, the event at the effective providers, the count
  have hG : Quad.mk _ (pubsJ 0) (pubsJ 1) +
      ((cS ++ pinCons (p := p) (K := K) regs idx).map fun r =>
          (compress (coinsJ δ (chalsJJ8 χ)) (liftRec (L := 𝕂′) r))⁻¹).sum =
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ (chalsJJ8 χ)) (liftRec (L := 𝕂′) q.1))⁻¹).sum := by
    have h3 := JGenJ8.jet_tagged_sumG hJk
    rw [hcJ] at h3 ⊢
    have hS' := hS
    rw [hprovS, hextS, List.map_append, List.map_append, List.sum_append, List.sum_append, h3] at hS'
    rw [List.map_append, List.sum_append]
    linear_combination hS' + hc8
  have houtJ : ((coinsJ δ (chalsJJ8 χ)).gamma, (coinsJ δ (chalsJJ8 χ)).pole) ∉
      IOFailureEventW (((cS ++ pinCons (p := p) (K := K) regs idx) ++
          jCons b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ).map (liftRec (L := 𝕂′)))
        (effP (Nock.Jet.SubJ8.liftS (δ := δ) (jProv b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ ++ provO))) := by
    rw [hcJ, List.append_assoc]
    have h : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
        IOFailureEventW (List.map (α := Fin 8 → K) (liftRec (L := 𝕂′)) (List.append (α := Fin 8 → K) cS (ext .s)))
          (effP (liftP (m := 8) (provs .s))) := by
      rw [hcS]; exact houtS
    rw [hextS, hprovS] at h
    exact h
  have hcountJ : ((cS ++ pinCons (p := p) (K := K) regs idx) ++
        jCons b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ).length < p := by
    have h : (List.map (α := Fin 8 → K) (liftRec (L := 𝕂′)) (List.append (α := Fin 8 → K) cS (ext .s))).length < p := by
      rw [hcS]; exact hcount .s
    rw [hextS, List.length_map] at h
    rw [List.append_assoc]
    exact h
  -- the effective provider family
  set provsE := withS provs (Nock.Jet.SubJ8.jProvE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
      (chals := chalsJJ8 χ) (pubs := pubsJ) (lay := lay) (P := PJ) provO ++
    Nock.Jet.SubJ8.provOE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
      (chals := chalsJJ8 χ) (pubs := pubsJ) (lay := lay) (P := PJ) provO) with hprovsE
  have hbalE : BalJ8 (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pubVJ8 δ b c m ρ ρS χ) provsE ext := by
    intro bl
    cases bl with
    | x => exact hbal .x
    | p => exact hbal .p
    | s =>
      have he := Nock.Jet.SubJ8.balance_effE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
        (chals := chalsJJ8 χ) (pubs := pubsJ) (lay := lay) (P := PJ) provO
        (fun k => (compress (coinsCV b δ (chalVJ8 b χ)) k)⁻¹)
      simp only [Nock.Jet.SubJ8.liftS, List.map_map, Function.comp_def] at he
      have h0 : _ + (List.map (α := Fin 8 → K) (fun r => (compress (coinsCV b δ (chalVJ8 b χ))
          (liftRec (L := 𝕂′) r))⁻¹) (ext .s)).sum =
          (List.map (α := (Fin 8 → K) × K) (fun q => algebraMap K 𝕂′ q.2 *
            (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) q.1))⁻¹) (provs .s)).sum := hbal .s
      rw [hprovS, he] at h0
      exact h0
  have houtE : ∀ bl, ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) ext bl) (liftP (provsE bl)) := by
    intro bl
    cases bl with
    | x => exact hout .x (by intro h; cases h)
    | p => exact hout .p (by intro h; cases h)
    | s =>
      have hl := Nock.Jet.SubJ8.liftS_effE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
        (chals := chalsJJ8 χ) (pubs := pubsJ) (lay := lay) (P := PJ) provO
      have hl' : liftP (p := p) (K := K) (δ := δ) (provsE .s) = effP (liftP (p := p) (K := K) (δ := δ) (provs .s)) := by
        rw [hprovS]; exact hl
      rw [hl']
      exact houtS
  -- the providers
  have hXp : ∀ limbA : ℕ → ℕ → HX, ProvOK (p := p) (K := K) D Rg limbA .x (provsE .x) := fun limbA => by
    show ProvOK (p := p) (K := K) D Rg limbA .x (provs .x)
    rw [hprovX]; exact provOK_of_provPA (by decide) hX
  have hJ : ∀ limbA : ℕ → ℕ → HX, ProvP (p := p) (K := K) (fun r => PreI D r → RecOK D Rg limbA r) .s
      (Nock.Jet.SubJ8.jProvE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
        (chals := chalsJJ8 χ) (pubs := pubsJ) (lay := lay) (P := PJ) provO) := fun limbA =>
    by
    rcases hJk with ⟨hsatJ, hbindJ, hinjJ, hnJ, hadjJ⟩ | ⟨h0, -⟩
    · -- J present: J-3b `Accepted`, the served pins, `hReg`
      have hbalJ := Nock.Jet.SubJ8.bal_of_serviceE hp3 hsatJ hbindJ hinjJ hnJ hadjJ _ provO hO7 hG houtJ hcountJ
      have hAcc := accepted_of_sat hsatJ hbindJ hinjJ hlay hsmall huniq hbalJ
      have hpinS := Nock.Jet.SubJ8.pin_servedE hp3 hsatJ hbindJ hinjJ hnJ hadjJ _ provO hO7 hG houtJ hcountJ
        (regs := regs) (idx := idx) (List.subset_append_right _ _)
      have hReg := hRegP hAcc hpinS
      exact JetProvIJ8.jetProvOKI hp3 hAcc hD hTpl
        (BalXJ8.hRd_of_balX B hbalE houtE hcount _ hextX (hXp limbA)) hReg provO
    · -- J absent: no J service provider
      rw [JGenJ8.jProvE_nil h0]
      intro q hq
      cases hq
  have hO : ProvP (p := p) (K := K) (RecOKI D Rg comb) .s provO := by
    rw [hpO]; exact hI
  have hprovE : ∀ bl, ProvP (p := p) (K := K) (RecOKI D Rg comb) bl (provsE bl) := by
    intro bl
    cases bl with
    | x => show ProvP _ _ (provs .x); rw [hprovX]; exact provPI_of_provPA hX
    | p => show ProvP _ _ (provs .p); rw [hprovP]; exact provPI_of_provPA hP
    | s => exact provP_append.mpr ⟨provPI_of_forall hJ, provP_filter _ hO⟩
  have haxP : ∀ bl, ProvP (p := p) (K := K) AxOK bl (provsE bl) := by
    intro bl
    cases bl with
    | x => intro q _ l _ _ _; exact axOK_x l
    | p => show ProvP _ _ (provs .p); rw [hprovP]; exact hPax
    | s => intro q _ l _ _ _; exact axOK_s l
  exact acceptsJ8_holdsN_computeI_ex C hp hRg hD hseed hα hw hbalE houtE hcount hprovE haxP hreal x hs hf he

/-- **`acceptsJ8_holdsN_EIGA_ex` with the axis bound exported** : also every active record of every
compute row meets `AxOK` (`servedP_of_balancesJ8` at `haxP`). Same hypotheses as `acceptsJ8_holdsN_EIGA_ex`.

**`acceptsJ8_holdsN_EIGA`, with the intermediate objects exposed**: the assembly with NO atom walk. As `FinalJ8IG.acceptsJ8_holdsN_EIG`, with the `s`
providers `jProv ++ pad8 atomIncProvs` (`hprovS`), the atom walk's `s` publics `0` in `hGS` (`hV0`), and no `hAW`. -/
theorem acceptsJ8_holdsN_EIGA_exA [CharP K p] [CharP 𝕂′ p]
    (χ : Coins frameJ8 K) (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′)
    -- the compute trace
    {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
    {P : Fin (computeChipVCLHX hn nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit).rap.w → (ZMod p)[X]}
    {α γ seed : K}
    (C : XCtx hn nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P α γ seed) (hp : 2 ^ 63 + 1 < p)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    -- the cell table
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hchC : ∀ j, 33 ≤ j → j ≤ 36 → chalsC j = chalsMJ8 δ χ j)
    -- the J-8 walk
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hF : GeneratedField.PrimeFieldElems (ZMod p)) (hp64 : 64 ≤ ringChar (ZMod p))
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    (hchW : ∀ j, 33 ≤ j → j ≤ 36 → chalsW j = chalsMJ8 δ χ j)
    -- the J chip and its public registry
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.w → (ZMod p)[X])
    (hJk : JGenJ8.JChipOK δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    {Rt : ℕ → Nock.Jet.Autogen.Tpl} {regs ids : List ℕ} {idx : ℕ → ℕ}
    -- the atom table
    {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA)
    (chalsA pubsA : ℕ → K)
    (QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (hsatA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbindA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinjA : Function.Injective nodesA)
    (hadjA : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hchA : ∀ j, 33 ≤ j → j ≤ 36 → chalsA j = chalsMJ8 δ χ j)
    -- the atom walk ABSENT: its two `s` publics are `0`
    (pubsV : ℕ → K) (hV0 : pubsV WalkHQ.pubPQ = 0 ∧ pubsV (WalkHQ.pubPQ + 1) = 0)
    -- the wiring (the pins are `s` consumes)
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++
      jRd b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hprovP : provs .p = ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW)
    (hextP : ext .p = [])
    (hprovS : provs .s = jProv b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ ++
      pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA))
    (hextS : ext .s = pinCons (p := p) (K := K) regs idx ++ jCons b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    -- the verifier's public equations (the `s` one carries the pins' sum)
    (hGx : ρ 3 + (Quad.mk _ (pubsW WalkHQ.pubXQ) (pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (pubsJ 2) (pubsJ 3)) =
      Quad.mk _ (pubsC CellHQ.pubHQ) (pubsC (CellHQ.pubHQ + 1)))
    (hGp : ρ 4 = Quad.mk _ (pubsW WalkHQ.pubPQ) (pubsW (WalkHQ.pubPQ + 1)))
    (hGS : ρS + ((pinCons (p := p) (K := K) regs idx).map fun r =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (pubsJ 0) (pubsJ 1) =
      Quad.mk _ (pubsA AtomChipHQ.pubMI) (pubsA (AtomChipHQ.pubMI + 1)) +
        Quad.mk _ (pubsV WalkHQ.pubPQ) (pubsV (WalkHQ.pubPQ + 1)))
    -- the IO events and counts at the compute coins: `x`, `p` as before, `s` at the effective providers
    (hout : ∀ bl, bl ≠ .s → ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (houtS : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) ext .s) (effP (liftP (provs .s))))
    (hcount : ∀ bl, (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) ext bl).length < p)
    -- the denotation
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {comb : ℕ → Noun}
    (hRg : Rg.Faithful) (hD : DenOKX p D)
    -- the x and p provider obligations
    (hX : ProvP (p := p) (K := K) (RecOKA D Rg comb) .x (cellProvsW b nodesC orbitC chalsC pubsC QC))
    (hP : ProvP (p := p) (K := K) (RecOKA D Rg comb) .p (ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW))
    (hPax : ProvP (p := p) (K := K) AxOK .p (ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW))
    -- the J chip's public checks and registry
    (hlay : List.ofFn lay = layoutJ8 Rt regs ids)
    (hsmall : ∀ q ∈ layoutJ8 Rt regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 Rt regs ids).filterMap tvKey).Nodup)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p)
    (hRegP : Accepted Rt regs ids (rowsJ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ) →
      (∀ id ∈ regs, ∃ r' ∈ rowsJ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ,
        pinKey (F := ZMod p) id (idx id) ∈ provK r') →
      ∀ r ∈ rowsJ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ, r.pre.kd = .reg →
        D (r.w.kN.val, r.w.vN.val) = some (Nock.Jet.Autogen.compile p (Rt r.pre.id)))
    -- the inc heads
    (hI : ProvP (p := p) (K := K) (RecOKI D Rg comb) .s (pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA)))
    -- the compute walk, its events and the root binding
    (hseed : seed = Walk.rlc γ (encT (K := K)
      (rowW (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0)
        (stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0))).trip) * α)
    (hα : α ∉ tileSet (foOf (rowsWX (fun r => envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r)
      (fun r => stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r)))) n)
    (hw : (α, γ) ∉ cwEvent (K := K)
      (rowsWX (fun r => envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r)
        (fun r => stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r))) n)
    (hreal : (stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0)).isChain = false)
    (x : P8PublicClaim)
    (hs : D (hdV (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0) xS) = some x.subject)
    (hf : D (hdV (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0) xF) = some x.formula)
    (he : D (hdV (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0) xE) = some x.result) :
    RowsAccXI n (fun r => (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P) r) (fun r => stX ((envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P) r)) D Rg comb ∧
    ForestReconGoal (stVS K) (lblOf (rowsWX (fun r => (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P) r) (fun r => stX ((envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P) r)))) 1 n ∧
    TreeFacts K n (fun r => (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P) r) (fun r => stX ((envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P) r)) D Rg ∧ Nock.Jet.HoldsN x ∧
    (∀ r < n, ∀ y ∈ RowSemChipX.activeX ((envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P) r), AxOK y) := by
  have B := AcceptJ8.bctx_of_xctx C
  have hp3 : 3 < p := by omega
  have hcv := coinsCV_J8 δ b χ
  have hcJ : coinsJ δ (chalsJJ8 χ) = coinsCV b δ (chalVJ8 b χ) := (coinsJ_J8 δ χ).trans hcv.symm
  have hcA := (BalSJ8.acoins_of_agree χ chalsA hchA).trans hcv.symm
  -- the other service providers
  obtain ⟨provO, hpO⟩ : ∃ l, l = pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA) := ⟨_, rfl⟩
  have hO7 : ∀ q ∈ provO, q.1 ⟨7, by norm_num⟩ = 0 := by
    intro q hq'
    rw [hpO] at hq'
    exact pad8_entry7 _ q hq'
  -- the `s` balance with the pins
  have hS : ρS + (List.map (α := Fin 8 → K) (fun r => (compress (coinsCV b δ (chalVJ8 b χ))
        (liftRec (L := 𝕂′) r))⁻¹) (ext .s)).sum =
      (List.map (α := (Fin 8 → K) × K) (fun q => algebraMap K 𝕂′ q.2 *
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) q.1))⁻¹) (provs .s)).sum := by
    have h3 := JGenJ8.jet_tagged_sumG hJk
    have hI' := ServiceJ8.atomIncProvs_sum δ b hnA nodesA orbitA chalsA pubsA QA hsatA hbindA hinjA hadjA
    rw [hcJ] at h3
    rw [hcA] at hI'
    have hGS0 := hGS
    rw [hV0.1, hV0.2, Quad.mk_zero', add_zero] at hGS0
    rw [hprovS, hextS, List.map_append, List.map_append, List.sum_append, List.sum_append, pad8_sum, h3, hI']
    linear_combination hGS0
  have hbal : BalJ8 (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pubVJ8 δ b c m ρ ρS χ) provs ext :=
    JGenJ8.balJ8_frameJ8G χ c m ρ ρS hnC nodesC orbitC chalsC pubsC QC hsatC hbindC hinjC hadjC hchC
      kroots hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW hchW
      nodesJ orbitJ pubsJ lay PJ hJk hprovX hextX hprovP hextP _ _ rfl rfl hGx hGp hS
  rw [← hpO] at hprovS
  -- denominators of the compute consumes
  have hne : ∀ bl, ∀ r ∈ compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalVJ8 b χ)
      (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) bl,
      compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r) ≠ 0 := by
    intro bl r hr
    cases bl with
    | s => exact TeleC.den_ne_of_out _ _ _ _ houtS _ (List.mem_map_of_mem (List.mem_append_left _ hr))
    | x =>
      exact TeleC.den_ne_of_out _ _ _ _ (hout .x (by intro h; cases h)) _
        (List.mem_map_of_mem (List.mem_append_left _ hr))
    | p =>
      exact TeleC.den_ne_of_out _ _ _ _ (hout .p (by intro h; cases h)) _
        (List.mem_map_of_mem (List.mem_append_left _ hr))
  have hc := DenXJ8.compReqsX_sum B hne .s
  change _ = ServedJ8.rhoX (b := b) (δ := δ) (pubVal := pubVJ8 δ b c m ρ ρS χ) .s at hc
  rw [rhoX_s_J8] at hc
  -- the compute's `s` consumes as `Fin 8` keys
  obtain ⟨cS, hcS⟩ : ∃ l : List (Fin 8 → K), l = compReqsX (K := K) (hn := hn) (nodes := nodes)
      (chalV := chalVJ8 b χ) (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) .s := ⟨_, rfl⟩
  have hc8 : (cS.map fun r => (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum = ρS := by
    rw [hcS]; exact hc
  -- the J share: `hG`, the event at the effective providers, the count
  have hG : Quad.mk _ (pubsJ 0) (pubsJ 1) +
      ((cS ++ pinCons (p := p) (K := K) regs idx).map fun r =>
          (compress (coinsJ δ (chalsJJ8 χ)) (liftRec (L := 𝕂′) r))⁻¹).sum =
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ (chalsJJ8 χ)) (liftRec (L := 𝕂′) q.1))⁻¹).sum := by
    have h3 := JGenJ8.jet_tagged_sumG hJk
    rw [hcJ] at h3 ⊢
    have hS' := hS
    rw [hprovS, hextS, List.map_append, List.map_append, List.sum_append, List.sum_append, h3] at hS'
    rw [List.map_append, List.sum_append]
    linear_combination hS' + hc8
  have houtJ : ((coinsJ δ (chalsJJ8 χ)).gamma, (coinsJ δ (chalsJJ8 χ)).pole) ∉
      IOFailureEventW (((cS ++ pinCons (p := p) (K := K) regs idx) ++
          jCons b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ).map (liftRec (L := 𝕂′)))
        (effP (Nock.Jet.SubJ8.liftS (δ := δ) (jProv b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ ++ provO))) := by
    rw [hcJ, List.append_assoc]
    have h : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
        IOFailureEventW (List.map (α := Fin 8 → K) (liftRec (L := 𝕂′)) (List.append (α := Fin 8 → K) cS (ext .s)))
          (effP (liftP (m := 8) (provs .s))) := by
      rw [hcS]; exact houtS
    rw [hextS, hprovS] at h
    exact h
  have hcountJ : ((cS ++ pinCons (p := p) (K := K) regs idx) ++
        jCons b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ).length < p := by
    have h : (List.map (α := Fin 8 → K) (liftRec (L := 𝕂′)) (List.append (α := Fin 8 → K) cS (ext .s))).length < p := by
      rw [hcS]; exact hcount .s
    rw [hextS, List.length_map] at h
    rw [List.append_assoc]
    exact h
  -- the effective provider family
  set provsE := withS provs (Nock.Jet.SubJ8.jProvE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
      (chals := chalsJJ8 χ) (pubs := pubsJ) (lay := lay) (P := PJ) provO ++
    Nock.Jet.SubJ8.provOE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
      (chals := chalsJJ8 χ) (pubs := pubsJ) (lay := lay) (P := PJ) provO) with hprovsE
  have hbalE : BalJ8 (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pubVJ8 δ b c m ρ ρS χ) provsE ext := by
    intro bl
    cases bl with
    | x => exact hbal .x
    | p => exact hbal .p
    | s =>
      have he := Nock.Jet.SubJ8.balance_effE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
        (chals := chalsJJ8 χ) (pubs := pubsJ) (lay := lay) (P := PJ) provO
        (fun k => (compress (coinsCV b δ (chalVJ8 b χ)) k)⁻¹)
      simp only [Nock.Jet.SubJ8.liftS, List.map_map, Function.comp_def] at he
      have h0 : _ + (List.map (α := Fin 8 → K) (fun r => (compress (coinsCV b δ (chalVJ8 b χ))
          (liftRec (L := 𝕂′) r))⁻¹) (ext .s)).sum =
          (List.map (α := (Fin 8 → K) × K) (fun q => algebraMap K 𝕂′ q.2 *
            (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) q.1))⁻¹) (provs .s)).sum := hbal .s
      rw [hprovS, he] at h0
      exact h0
  have houtE : ∀ bl, ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) ext bl) (liftP (provsE bl)) := by
    intro bl
    cases bl with
    | x => exact hout .x (by intro h; cases h)
    | p => exact hout .p (by intro h; cases h)
    | s =>
      have hl := Nock.Jet.SubJ8.liftS_effE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
        (chals := chalsJJ8 χ) (pubs := pubsJ) (lay := lay) (P := PJ) provO
      have hl' : liftP (p := p) (K := K) (δ := δ) (provsE .s) = effP (liftP (p := p) (K := K) (δ := δ) (provs .s)) := by
        rw [hprovS]; exact hl
      rw [hl']
      exact houtS
  -- the providers
  have hXp : ∀ limbA : ℕ → ℕ → HX, ProvOK (p := p) (K := K) D Rg limbA .x (provsE .x) := fun limbA => by
    show ProvOK (p := p) (K := K) D Rg limbA .x (provs .x)
    rw [hprovX]; exact provOK_of_provPA (by decide) hX
  have hJ : ∀ limbA : ℕ → ℕ → HX, ProvP (p := p) (K := K) (fun r => PreI D r → RecOK D Rg limbA r) .s
      (Nock.Jet.SubJ8.jProvE (δ := δ) (b := b) (nodes := nodesJ) (orbit := orbitJ)
        (chals := chalsJJ8 χ) (pubs := pubsJ) (lay := lay) (P := PJ) provO) := fun limbA =>
    by
    rcases hJk with ⟨hsatJ, hbindJ, hinjJ, hnJ, hadjJ⟩ | ⟨h0, -⟩
    · -- J present: J-3b `Accepted`, the served pins, `hReg`
      have hbalJ := Nock.Jet.SubJ8.bal_of_serviceE hp3 hsatJ hbindJ hinjJ hnJ hadjJ _ provO hO7 hG houtJ hcountJ
      have hAcc := accepted_of_sat hsatJ hbindJ hinjJ hlay hsmall huniq hbalJ
      have hpinS := Nock.Jet.SubJ8.pin_servedE hp3 hsatJ hbindJ hinjJ hnJ hadjJ _ provO hO7 hG houtJ hcountJ
        (regs := regs) (idx := idx) (List.subset_append_right _ _)
      have hReg := hRegP hAcc hpinS
      exact JetProvIJ8.jetProvOKI hp3 hAcc hD hTpl
        (BalXJ8.hRd_of_balX B hbalE houtE hcount _ hextX (hXp limbA)) hReg provO
    · -- J absent: no J service provider
      rw [JGenJ8.jProvE_nil h0]
      intro q hq
      cases hq
  have hO : ProvP (p := p) (K := K) (RecOKI D Rg comb) .s provO := by
    rw [hpO]; exact hI
  have hprovE : ∀ bl, ProvP (p := p) (K := K) (RecOKI D Rg comb) bl (provsE bl) := by
    intro bl
    cases bl with
    | x => show ProvP _ _ (provs .x); rw [hprovX]; exact provPI_of_provPA hX
    | p => show ProvP _ _ (provs .p); rw [hprovP]; exact provPI_of_provPA hP
    | s => exact provP_append.mpr ⟨provPI_of_forall hJ, provP_filter _ hO⟩
  have haxP : ∀ bl, ProvP (p := p) (K := K) AxOK bl (provsE bl) := by
    intro bl
    cases bl with
    | x => intro q _ l _ _ _; exact axOK_x l
    | p => show ProvP _ _ (provs .p); rw [hprovP]; exact hPax
    | s => intro q _ l _ _ _; exact axOK_s l
  have H := acceptsJ8_holdsN_computeI_ex C hp hRg hD hseed hα hw hbalE houtE hcount hprovE haxP hreal x hs hf he
  exact ⟨H.1, H.2.1, H.2.2.1, H.2.2.2, ServedJ8.servedP_of_balancesJ8 B (by omega) hbalE houtE hcount haxP⟩

/-- Sanity: the twin implies `acceptsJ8_holdsN_EIGA`. -/
theorem acceptsJ8_holdsN_EIGA_of_ex [CharP K p] [CharP 𝕂′ p]
    (χ : Coins frameJ8 K) (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′)
    -- the compute trace
    {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
    {P : Fin (computeChipVCLHX hn nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit).rap.w → (ZMod p)[X]}
    {α γ seed : K}
    (C : XCtx hn nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P α γ seed) (hp : 2 ^ 63 + 1 < p)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    -- the cell table
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hchC : ∀ j, 33 ≤ j → j ≤ 36 → chalsC j = chalsMJ8 δ χ j)
    -- the J-8 walk
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hF : GeneratedField.PrimeFieldElems (ZMod p)) (hp64 : 64 ≤ ringChar (ZMod p))
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    (hchW : ∀ j, 33 ≤ j → j ≤ 36 → chalsW j = chalsMJ8 δ χ j)
    -- the J chip and its public registry
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.w → (ZMod p)[X])
    (hJk : JGenJ8.JChipOK δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    {Rt : ℕ → Nock.Jet.Autogen.Tpl} {regs ids : List ℕ} {idx : ℕ → ℕ}
    -- the atom table
    {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA)
    (chalsA pubsA : ℕ → K)
    (QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (hsatA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbindA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinjA : Function.Injective nodesA)
    (hadjA : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hchA : ∀ j, 33 ≤ j → j ≤ 36 → chalsA j = chalsMJ8 δ χ j)
    -- the atom walk ABSENT: its two `s` publics are `0`
    (pubsV : ℕ → K) (hV0 : pubsV WalkHQ.pubPQ = 0 ∧ pubsV (WalkHQ.pubPQ + 1) = 0)
    -- the wiring (the pins are `s` consumes)
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++
      jRd b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hprovP : provs .p = ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW)
    (hextP : ext .p = [])
    (hprovS : provs .s = jProv b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ ++
      pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA))
    (hextS : ext .s = pinCons (p := p) (K := K) regs idx ++ jCons b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    -- the verifier's public equations (the `s` one carries the pins' sum)
    (hGx : ρ 3 + (Quad.mk _ (pubsW WalkHQ.pubXQ) (pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (pubsJ 2) (pubsJ 3)) =
      Quad.mk _ (pubsC CellHQ.pubHQ) (pubsC (CellHQ.pubHQ + 1)))
    (hGp : ρ 4 = Quad.mk _ (pubsW WalkHQ.pubPQ) (pubsW (WalkHQ.pubPQ + 1)))
    (hGS : ρS + ((pinCons (p := p) (K := K) regs idx).map fun r =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (pubsJ 0) (pubsJ 1) =
      Quad.mk _ (pubsA AtomChipHQ.pubMI) (pubsA (AtomChipHQ.pubMI + 1)) +
        Quad.mk _ (pubsV WalkHQ.pubPQ) (pubsV (WalkHQ.pubPQ + 1)))
    -- the IO events and counts at the compute coins: `x`, `p` as before, `s` at the effective providers
    (hout : ∀ bl, bl ≠ .s → ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (houtS : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) ext .s) (effP (liftP (provs .s))))
    (hcount : ∀ bl, (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) ext bl).length < p)
    -- the denotation
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {comb : ℕ → Noun}
    (hRg : Rg.Faithful) (hD : DenOKX p D)
    -- the x and p provider obligations
    (hX : ProvP (p := p) (K := K) (RecOKA D Rg comb) .x (cellProvsW b nodesC orbitC chalsC pubsC QC))
    (hP : ProvP (p := p) (K := K) (RecOKA D Rg comb) .p (ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW))
    (hPax : ProvP (p := p) (K := K) AxOK .p (ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW))
    -- the J chip's public checks and registry
    (hlay : List.ofFn lay = layoutJ8 Rt regs ids)
    (hsmall : ∀ q ∈ layoutJ8 Rt regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 Rt regs ids).filterMap tvKey).Nodup)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p)
    (hRegP : Accepted Rt regs ids (rowsJ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ) →
      (∀ id ∈ regs, ∃ r' ∈ rowsJ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ,
        pinKey (F := ZMod p) id (idx id) ∈ provK r') →
      ∀ r ∈ rowsJ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ, r.pre.kd = .reg →
        D (r.w.kN.val, r.w.vN.val) = some (Nock.Jet.Autogen.compile p (Rt r.pre.id)))
    -- the inc heads
    (hI : ProvP (p := p) (K := K) (RecOKI D Rg comb) .s (pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA)))
    -- the compute walk, its events and the root binding
    (hseed : seed = Walk.rlc γ (encT (K := K)
      (rowW (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0)
        (stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0))).trip) * α)
    (hα : α ∉ tileSet (foOf (rowsWX (fun r => envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r)
      (fun r => stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r)))) n)
    (hw : (α, γ) ∉ cwEvent (K := K)
      (rowsWX (fun r => envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r)
        (fun r => stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r))) n)
    (hreal : (stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0)).isChain = false)
    (x : P8PublicClaim)
    (hs : D (hdV (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0) xS) = some x.subject)
    (hf : D (hdV (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0) xF) = some x.formula)
    (he : D (hdV (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0) xE) = some x.result) :
    Nock.Jet.HoldsN x :=
  (acceptsJ8_holdsN_EIGA_ex χ c m ρ ρS C hp hnC nodesC orbitC chalsC pubsC QC hsatC hbindC hinjC hadjC hchC kroots hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW hchW nodesJ orbitJ pubsJ lay PJ hJk hnA nodesA orbitA chalsA pubsA QA hsatA hbindA hinjA hadjA hchA pubsV hV0 hprovX hextX hprovP hextP hprovS hextS hGx hGp hGS hout houtS hcount hRg hD hX hP hPax hlay hsmall huniq hTpl hRegP hI hseed hα hw hreal x hs hf he).2.2.2

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinFinalJ8IGA

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinFinalJ8IGA.acceptsJ8_holdsN_EIGA_ex
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinFinalJ8IGA.acceptsJ8_holdsN_EIGA_exA
