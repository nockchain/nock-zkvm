/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/TwinLinkJ8A.lean

 Extraction twins of `LinkJ8A.hsoundJ8ZUA` and `LinkJ8A.hsoundJ8XUA` (the J-8 soundness chain with the atom walk
 absent). The hypotheses and the proof text are those of the source theorems; only the last step differs: it calls
 `TwinHokLJ8GA.acceptsJ8_holdsN_finalLGA_ex`, so the conclusion also carries the compute walk's row accumulator
 `RowsAccXI` at the row environments `envX` (cell-table denotation `denJ8`, comb `combN`) and its forest goal, next
 to `HoldsN`. `hsoundJ8XUA_ex` also returns the claim-cell decode `hcell`. The corollaries
 `hsoundJ8ZUA_of_ex` and `hsoundJ8XUA_of_ex` re-derive the source theorems.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A
import Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinHokLJ8GA

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinLinkJ8A

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Reads)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8 (AWSeedsOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.FibreJ8 (effP)
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.CorJ8F (denJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree chalsOK_J8 chalsAJ8_ok)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY encZY_cell inlineAtoms_encZY)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC outside40C outside_sumJ8_D)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 wchain_out v0 v1)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8 (OutJ8 outJ8_of_outside chalsMJ8_z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayLe realize40 realizeJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3
open Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8 (valReader)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (rowsMJ8 rowsB0 crA)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (censusList2)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z atomTZ)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_of_ne chalsAJ8Z_ok chalsAJ8Z_agree)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R4 (RR4 LL4 hHXV_ofZ)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ)
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun claimH isCellN)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crA crM crW crC staged_eq below_of_mem shV)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (mbXs claimCells claimRecsJ8 pinRecsJ8 rkC MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_zAt)
open Nock.NockVMROM.Thm54.VclL.Handle.RealVJ8
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R4
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R5
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (xS xF xE)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (envCJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP (toMsgJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 St40 sum40 fpx_out v4 v5 v6 v7)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (extY_below shV_round)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemIJ8 (RowsAccXI)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combN)

noncomputable section

section SoundZ
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

/-- `hsoundJ8ZUA`, with the compute walk's row accumulator `RowsAccXI` at the row environments `envX`, the cell-table
denotation `denJ8` and the comb `combN`, and its forest goal, next to `HoldsN`. Same hypotheses as the source theorem. -/
theorem hsoundJ8ZUA_ex [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hacc : AcceptsJ8ZA δ b Pb Rg c χ M tr)
    (hsatL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
      (qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA))
    (hbindL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
      (qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA))
    (hout : ∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ)
    {rA : ℕ → ARow} (hl : LinkJ8ZUA δ b Pb c χ M tr R L rA) :
    Nock.Jet.HoldsN c ∧
    RowsAccXI Pb.n (fun r => envX δ b Pb c χ M tr r) (fun r => stX (envX δ b Pb c χ M tr r))
      (denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA) Rg combN ∧
    ForestReconGoal (stVS K) (lblOf (rowsWX (fun r => envX δ b Pb c χ M tr r)
      (fun r => stX (envX δ b Pb c χ M tr r)))) 1 Pb.n := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp : 2 ^ 63 + 1 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; omega
  have hF' := GeneratedField.primeFieldElems_zmod p
  have O := outJ8_of_outside R L b hout
  have hz2 : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) := by
    rw [(chalsMJ8_z (δ := δ) χ).1, (chalsMJ8_z (δ := δ) χ).2]
  have hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0 := by
    rw [hz2]; exact O.z_ne
  -- (b) the IO events, read at the trace's lists
  have houtC : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.D.valReqs tr χ) (R.D.valProvs tr χ) := O.valid hl.budV.1 hl.budV.2
  rw [hl.rdV.1, hl.rdV.2] at houtC
  have hx : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (R.D.cxReqs tr χ) (R.D.cxProvs tr χ) := O.hout_x hl.budX.1 hl.budX.2
  rw [hl.rdX.1, hl.rdX.2] at hx
  have hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (L.pReqs tr (toVSQ χ)) (L.pProvs tr (toVSQ χ)) := O.hout_p hl.budP.1 hl.budP.2
  rw [hl.rdP.1, hl.rdP.2] at hpp
  have hs : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (R.D.svReqs tr χ) (R.D.svProvs tr χ) := O.hout_s hl.budS.1 hl.budS.2
  rw [hl.rdS.1, hl.rdS.2] at hs
  have hW := wchain_out L (outside40C R L hout)
  rw [hl.rdWW, ← (coinW_J8 δ χ).1, ← (coinW_J8 δ χ).2] at hW
  have hw0 : (limbVal b (chalVJ8 b χ) chalAlphaW, limbVal b (chalVJ8 b χ) chalGammaW) ∉
      cwEvent (K := K) (L.cRows tr) (L.cH tr) := O.hw rfl rfl
  rw [hl.rdWC.1, hl.rdWC.2] at hw0
  have hα0 : limbVal b (chalVJ8 b χ) chalAlphaW ∉ tileSet (K := K) (foOf (L.cRows tr)) (L.cH tr) := O.hα rfl
  rw [hl.rdWC.1, hl.rdWC.2] at hα0
  -- (b) `EncInj2` at the cell table
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hbindC
  have htabC := TwoProviderQ.cellTable_accepts2 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hF' hq'
    hzC hsatC0 hbindC0 hacc.hinjC hacc.hadjC hacc.hnpC _ _ (chalsOK_J8 (δ := δ) χ) M.reqsC M.xsC hacc.hsumC houtC
    hacc.hxneC hl.hcountC M.vp hacc.hxC hacc.hvp0
  rw [hz2] at htabC
  have hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (encJ8 δ χ) :=
    inlineAtoms_encZY (by rw [hrc]; exact hpG) _ _
  have hEinj := EncInjJ8.encInj2_of_outside (withLiftC R L).D
    (outside_sumJ8_D (withLiftC R L) hout .bivariateCensus (by decide) (by decide) (by decide)) hq' O.z_ne hE
    htabC hl.hvp hl.hext hqM hk hl.hprs
  -- (c) the compute context
  have XC : XCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ))
      (limbVal b (chalVJ8 b χ) chalAlphaW) (limbVal b (chalVJ8 b χ) chalGammaW)
      (limbVal b (pubVJ8 δ b c M.m M.ρ M.ρS χ) pubSeed) :=
    ⟨by omega, hacc.hsatX, hacc.hinjX, hacc.hadjX, rfl, rfl, pubVJ8_IC δ b c M.m M.ρ M.ρS χ, rfl,
      pubVJ8_out δ b c M.m M.ρ M.ρS χ⟩
  obtain ⟨hA, hF, -, hH⟩ := TwinHokLJ8GA.acceptsJ8_holdsN_finalLGA_ex (χ := χ) (c := c) (m := M.m) (ρ := M.ρ) (ρS := M.ρS) (C := XC) (hp := hp)
    (provs := provsJ8A δ b Pb χ M tr) (ext := extJ8 δ b Pb c χ M tr)
    (hnC := Pb.hnC) (nodesC := Pb.nodesC) (orbitC := Pb.orbitC) (chalsC := chalsMJ8 δ χ) (pubsC := M.pubsC)
    (QC := qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) (hsatC := hacc.hsatC) (hbindC := hacc.hbindC)
    (hinjC := hacc.hinjC) (hadjC := hacc.hadjC) (hchC := fun _ _ _ => rfl)
    (kroots := Pb.kroots) (hnW := Pb.hnW) (nodesW := Pb.nodesW) (orbitW := Pb.orbitW) (chalsW := chalsMJ8 δ χ)
    (pubsW := M.pubsW) (QW := qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) (hsatW := hacc.hsatW) (hbindW := hacc.hbindW)
    (hF := hF') (hp64 := by rw [hrc]; omega) (hinjW := hacc.hinjW) (hadjW := hacc.hadjW)
    (hchW := fun _ _ _ => rfl)
    (nodesJ := Pb.nodesJ) (orbitJ := Pb.orbitJ) (pubsJ := M.pubsJ) (lay := Pb.lay)
    (PJ := qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ) (hJk := hacc.hJk)
    (Rt := Pb.Rt) (regs := Pb.regs) (ids := Pb.ids) (idx := Pb.idx) (rk := Pb.rk)
    (hnA := Pb.hnA) (nodesA := Pb.nodesA) (orbitA := Pb.orbitA) (chalsA := chalsAJ8Z δ χ) (pubsA := M.pubsA)
    (QA := qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) (QL := qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
    (hQA := (qAL_toHQ δ b Pb tr _ _).symm) (hsatL := hsatL) (hbindL := hbindL)
    (hinjA := hacc.hinjA) (hadjA := hacc.hadjA) (hchA := fun j h1 h2 => chalsAJ8Z_agree δ χ j h1 h2)
    (pubsV := M.pubsV) (hV0 := hacc.hV0)
    (hprovX := rfl) (hextX := rfl) (hprovP := rfl) (hextP := rfl) (hprovS := rfl) (hextS := rfl)
    (hGx := hacc.hGx) (hGp := hacc.hGp) (hGS := hacc.hGS)
    (hout := fun bl hbl => by cases bl with | x => exact hx | p => exact hpp | s => exact absurd rfl hbl)
    (houtS := hs) (hcount := hl.hcount)
    (hnpC := hacc.hnpC) (hzC := hzC) (γV := _) (ρV := _) (hokC := chalsOK_J8 (δ := δ) χ)
    (reqsC := M.reqsC) (xsC := M.xsC) (hsumC := hacc.hsumC) (houtC := houtC) (hxneC := hacc.hxneC)
    (hcountC := hl.hcountC) (vp := M.vp) (hxC := hacc.hxC) (hvp0 := hacc.hvp0)
    (E := encJ8 δ χ) (hconsE := fun a b' => by rw [hz2]; rfl) (hE := by rw [hz2]; exact hE)
    (rA := rA) (hvp := hl.hvp) (hEinj := hEinj)
    (hkW := hacc.hkW) (hknW := hacc.hknW) (hkpW := hacc.hkpW) (hXW := hl.hXW) (hHXW := hl.hHXW) (houtW := hW)
    (hRg := hRg) (hlay := hacc.hlay) (hsmall := hacc.hsmall) (huniq := hacc.huniq) (hTpl := hacc.hTpl)
    (hnd := hacc.hnd) (hidx := hacc.hidx) (hrk := hacc.hrk) (hlt := hacc.hlt) (hpinC := hacc.hpinC)
    (hinjE := hl.hinjE)
    (hRA := hl.hRA) (hsA := hl.hsA) (hidxA := hl.hidxA) (hpG := hpG) (hrn := hl.hrn) (hB := hl.hB)
    (hwRA := hl.hwRA) (wreqs := M.wreqs) (hbalA := hacc.hbalA) (houtA := hl.houtA)
    (hcountA := hl.hcountA) (hnpA := hacc.hnpA) (hzA := by rw [chalsAJ8Z_of_ne δ χ (by omega) (by omega), chalsAJ8Z_of_ne δ χ (by omega) (by omega)]; exact O.atom_hz) (hservedA := hl.hservedA)
    (hseed := hl.hseed) (hα := hα0) (hw := hw0) (hreal := hl.hreal) (x := c) (hs := hl.hs) (hf := hl.hf)
    (he := hl.he)
  exact ⟨hH, hA, hF⟩

/-- **`hsoundJ8ZUA_ex` with the axis bound exported** : also `AxOK` at every active record of every
compute row.

`hsoundJ8ZUA`, with the compute walk's row accumulator `RowsAccXI` at the row environments `envX`, the cell-table
denotation `denJ8` and the comb `combN`, and its forest goal, next to `HoldsN`. Same hypotheses as the source theorem. -/
theorem hsoundJ8ZUA_exA [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hacc : AcceptsJ8ZA δ b Pb Rg c χ M tr)
    (hsatL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
      (qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA))
    (hbindL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
      (qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA))
    (hout : ∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ)
    {rA : ℕ → ARow} (hl : LinkJ8ZUA δ b Pb c χ M tr R L rA) :
    Nock.Jet.HoldsN c ∧
    RowsAccXI Pb.n (fun r => envX δ b Pb c χ M tr r) (fun r => stX (envX δ b Pb c χ M tr r))
      (denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA) Rg combN ∧
    ForestReconGoal (stVS K) (lblOf (rowsWX (fun r => envX δ b Pb c χ M tr r)
      (fun r => stX (envX δ b Pb c χ M tr r)))) 1 Pb.n ∧
    (∀ r < Pb.n, ∀ y ∈ RowSemChipX.activeX (envX δ b Pb c χ M tr r), AxOK y) := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp : 2 ^ 63 + 1 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; omega
  have hF' := GeneratedField.primeFieldElems_zmod p
  have O := outJ8_of_outside R L b hout
  have hz2 : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) := by
    rw [(chalsMJ8_z (δ := δ) χ).1, (chalsMJ8_z (δ := δ) χ).2]
  have hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0 := by
    rw [hz2]; exact O.z_ne
  -- (b) the IO events, read at the trace's lists
  have houtC : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.D.valReqs tr χ) (R.D.valProvs tr χ) := O.valid hl.budV.1 hl.budV.2
  rw [hl.rdV.1, hl.rdV.2] at houtC
  have hx : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (R.D.cxReqs tr χ) (R.D.cxProvs tr χ) := O.hout_x hl.budX.1 hl.budX.2
  rw [hl.rdX.1, hl.rdX.2] at hx
  have hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (L.pReqs tr (toVSQ χ)) (L.pProvs tr (toVSQ χ)) := O.hout_p hl.budP.1 hl.budP.2
  rw [hl.rdP.1, hl.rdP.2] at hpp
  have hs : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (R.D.svReqs tr χ) (R.D.svProvs tr χ) := O.hout_s hl.budS.1 hl.budS.2
  rw [hl.rdS.1, hl.rdS.2] at hs
  have hW := wchain_out L (outside40C R L hout)
  rw [hl.rdWW, ← (coinW_J8 δ χ).1, ← (coinW_J8 δ χ).2] at hW
  have hw0 : (limbVal b (chalVJ8 b χ) chalAlphaW, limbVal b (chalVJ8 b χ) chalGammaW) ∉
      cwEvent (K := K) (L.cRows tr) (L.cH tr) := O.hw rfl rfl
  rw [hl.rdWC.1, hl.rdWC.2] at hw0
  have hα0 : limbVal b (chalVJ8 b χ) chalAlphaW ∉ tileSet (K := K) (foOf (L.cRows tr)) (L.cH tr) := O.hα rfl
  rw [hl.rdWC.1, hl.rdWC.2] at hα0
  -- (b) `EncInj2` at the cell table
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hbindC
  have htabC := TwoProviderQ.cellTable_accepts2 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hF' hq'
    hzC hsatC0 hbindC0 hacc.hinjC hacc.hadjC hacc.hnpC _ _ (chalsOK_J8 (δ := δ) χ) M.reqsC M.xsC hacc.hsumC houtC
    hacc.hxneC hl.hcountC M.vp hacc.hxC hacc.hvp0
  rw [hz2] at htabC
  have hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (encJ8 δ χ) :=
    inlineAtoms_encZY (by rw [hrc]; exact hpG) _ _
  have hEinj := EncInjJ8.encInj2_of_outside (withLiftC R L).D
    (outside_sumJ8_D (withLiftC R L) hout .bivariateCensus (by decide) (by decide) (by decide)) hq' O.z_ne hE
    htabC hl.hvp hl.hext hqM hk hl.hprs
  -- (c) the compute context
  have XC : XCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ))
      (limbVal b (chalVJ8 b χ) chalAlphaW) (limbVal b (chalVJ8 b χ) chalGammaW)
      (limbVal b (pubVJ8 δ b c M.m M.ρ M.ρS χ) pubSeed) :=
    ⟨by omega, hacc.hsatX, hacc.hinjX, hacc.hadjX, rfl, rfl, pubVJ8_IC δ b c M.m M.ρ M.ρS χ, rfl,
      pubVJ8_out δ b c M.m M.ρ M.ρS χ⟩
  obtain ⟨hA, hF, -, hH, hAx⟩ := TwinHokLJ8GA.acceptsJ8_holdsN_finalLGA_exA (χ := χ) (c := c) (m := M.m) (ρ := M.ρ) (ρS := M.ρS) (C := XC) (hp := hp)
    (provs := provsJ8A δ b Pb χ M tr) (ext := extJ8 δ b Pb c χ M tr)
    (hnC := Pb.hnC) (nodesC := Pb.nodesC) (orbitC := Pb.orbitC) (chalsC := chalsMJ8 δ χ) (pubsC := M.pubsC)
    (QC := qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) (hsatC := hacc.hsatC) (hbindC := hacc.hbindC)
    (hinjC := hacc.hinjC) (hadjC := hacc.hadjC) (hchC := fun _ _ _ => rfl)
    (kroots := Pb.kroots) (hnW := Pb.hnW) (nodesW := Pb.nodesW) (orbitW := Pb.orbitW) (chalsW := chalsMJ8 δ χ)
    (pubsW := M.pubsW) (QW := qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) (hsatW := hacc.hsatW) (hbindW := hacc.hbindW)
    (hF := hF') (hp64 := by rw [hrc]; omega) (hinjW := hacc.hinjW) (hadjW := hacc.hadjW)
    (hchW := fun _ _ _ => rfl)
    (nodesJ := Pb.nodesJ) (orbitJ := Pb.orbitJ) (pubsJ := M.pubsJ) (lay := Pb.lay)
    (PJ := qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ) (hJk := hacc.hJk)
    (Rt := Pb.Rt) (regs := Pb.regs) (ids := Pb.ids) (idx := Pb.idx) (rk := Pb.rk)
    (hnA := Pb.hnA) (nodesA := Pb.nodesA) (orbitA := Pb.orbitA) (chalsA := chalsAJ8Z δ χ) (pubsA := M.pubsA)
    (QA := qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) (QL := qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
    (hQA := (qAL_toHQ δ b Pb tr _ _).symm) (hsatL := hsatL) (hbindL := hbindL)
    (hinjA := hacc.hinjA) (hadjA := hacc.hadjA) (hchA := fun j h1 h2 => chalsAJ8Z_agree δ χ j h1 h2)
    (pubsV := M.pubsV) (hV0 := hacc.hV0)
    (hprovX := rfl) (hextX := rfl) (hprovP := rfl) (hextP := rfl) (hprovS := rfl) (hextS := rfl)
    (hGx := hacc.hGx) (hGp := hacc.hGp) (hGS := hacc.hGS)
    (hout := fun bl hbl => by cases bl with | x => exact hx | p => exact hpp | s => exact absurd rfl hbl)
    (houtS := hs) (hcount := hl.hcount)
    (hnpC := hacc.hnpC) (hzC := hzC) (γV := _) (ρV := _) (hokC := chalsOK_J8 (δ := δ) χ)
    (reqsC := M.reqsC) (xsC := M.xsC) (hsumC := hacc.hsumC) (houtC := houtC) (hxneC := hacc.hxneC)
    (hcountC := hl.hcountC) (vp := M.vp) (hxC := hacc.hxC) (hvp0 := hacc.hvp0)
    (E := encJ8 δ χ) (hconsE := fun a b' => by rw [hz2]; rfl) (hE := by rw [hz2]; exact hE)
    (rA := rA) (hvp := hl.hvp) (hEinj := hEinj)
    (hkW := hacc.hkW) (hknW := hacc.hknW) (hkpW := hacc.hkpW) (hXW := hl.hXW) (hHXW := hl.hHXW) (houtW := hW)
    (hRg := hRg) (hlay := hacc.hlay) (hsmall := hacc.hsmall) (huniq := hacc.huniq) (hTpl := hacc.hTpl)
    (hnd := hacc.hnd) (hidx := hacc.hidx) (hrk := hacc.hrk) (hlt := hacc.hlt) (hpinC := hacc.hpinC)
    (hinjE := hl.hinjE)
    (hRA := hl.hRA) (hsA := hl.hsA) (hidxA := hl.hidxA) (hpG := hpG) (hrn := hl.hrn) (hB := hl.hB)
    (hwRA := hl.hwRA) (wreqs := M.wreqs) (hbalA := hacc.hbalA) (houtA := hl.houtA)
    (hcountA := hl.hcountA) (hnpA := hacc.hnpA) (hzA := by rw [chalsAJ8Z_of_ne δ χ (by omega) (by omega), chalsAJ8Z_of_ne δ χ (by omega) (by omega)]; exact O.atom_hz) (hservedA := hl.hservedA)
    (hseed := hl.hseed) (hα := hα0) (hw := hw0) (hreal := hl.hreal) (x := c) (hs := hl.hs) (hf := hl.hf)
    (he := hl.he)
  exact ⟨hH, hA, hF, hAx⟩

/-- `hsoundJ8ZUA` from its twin. -/
theorem hsoundJ8ZUA_of_ex [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hacc : AcceptsJ8ZA δ b Pb Rg c χ M tr)
    (hsatL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
      (qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA))
    (hbindL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
      (qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA))
    (hout : ∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ)
    {rA : ℕ → ARow} (hl : LinkJ8ZUA δ b Pb c χ M tr R L rA) :
    Nock.Jet.HoldsN c :=
  (hsoundJ8ZUA_ex δ b Pb hRg c χ M tr R L hpG hqM hk hacc hsatL hbindL hout hl).1

end SoundZ

section SoundX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

/-- `hsoundJ8XUA`, with the row accumulator `RowsAccXI` and the forest goal at the row environments of `toMsgJ8ZA`, and
the claim-cell decode `hcell`: every cell claim noun is the denotation of its handle's cell record. Same hypotheses
as the source theorem. -/
theorem hsoundJ8XUA_ex [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    {r0 : RowsJ8} {g0 : ℕ} (hacc3 : AcceptsJ8V.AcceptsJ8V δ b Pb Rg c χ M tr r0 g0) (h0 : Pb.krootsV = 0)
    (hout : ∀ s ∈ AtomFpxJ8.allJ8X (AtomFpxJ8.withFpxV δ b (withLiftC R L) Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV
      Pb.nodesA Pb.orbitA), ¬ s.mem tr χ)
    {rA : ℕ → ARow} (hl : LinkJ8XUA δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr R L rA) :
    Nock.Jet.HoldsN c ∧
    RowsAccXI Pb.n (fun r => envX δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr r)
      (fun r => stX (envX δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr r))
      (denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA) Rg combN ∧
    ForestReconGoal (stVS K) (lblOf (rowsWX (fun r => envX δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr r)
      (fun r => stX (envX δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr r)))) 1 Pb.n ∧
    (∀ k : Fin 3, isCellN (claimNoun c k) = true →
      denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
        (1, (M.m k).1) = some (claimNoun c k)) := by
  have hacc' := hacc3
  have hacc := acceptsJ8ZA_of_V hacc' h0
  replace hout := AtomFpxJ8.outsideC_of_outsideX _ hout
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp : 2 ^ 63 + 1 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; omega
  have hF' := GeneratedField.primeFieldElems_zmod p
  have O := outJ8_of_outside R L b hout
  have hz2 : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) := by
    rw [(chalsMJ8_z (δ := δ) χ).1, (chalsMJ8_z (δ := δ) χ).2]
  have hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0 := by
    rw [hz2]; exact O.z_ne
  have houtC : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.D.valReqs tr χ) (R.D.valProvs tr χ) := O.valid hl.budV.1 hl.budV.2
  rw [hl.rdV.1, hl.rdV.2] at houtC
  have hcountC := hcountC_of' δ b Pb c χ M tr hacc'.hlenC
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hbindC
  have htabC := TwoProviderQ.cellTable_accepts2 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hF' hq'
    hzC hsatC0 hbindC0 hacc.hinjC hacc.hadjC hacc.hnpC _ _ (chalsOK_J8 (δ := δ) χ) _ _ hacc.hsumC houtC
    hacc.hxneC hcountC _ hacc.hxC hacc.hvp0
  rw [hz2] at htabC
  have hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (encJ8 δ χ) :=
    inlineAtoms_encZY (by rw [hrc]; exact hpG) _ _
  -- the census at the registered and claim cell nouns (Q2)
  have hG := LinkQ2J8.hinjE_of_outside (withLiftC R L) hout hq' O.z_ne hE htabC hl.hvp hl.hext hqM hk
    (G := censusG Pb c)
    (fun x hx => ⟨(hacc'.hcen x hx).1, fun v hv => hqM v (by rw [hrc]; exact (hacc'.hcen x hx).2 v hv)⟩) hl.hprsG
  have hinjE : ∀ id ∈ Pb.regs, ∀ d ∈ decodedNouns2 ((cellT δ b Pb χ (toMsgJ8ZA δ b Pb c χ M tr) tr).map (·.b0))
      (extB p rA), encJ8 δ χ (Nock.Jet.Autogen.compile p (Pb.Rt id)) = encJ8 δ χ d →
        Nock.Jet.Autogen.compile p (Pb.Rt id) = d :=
    fun id hid d hd he => hG _ (List.mem_append_left _ (List.mem_map_of_mem hid)) d hd he
  -- the claim's cell records are served
  have hvpr : ∀ k ∈ (toMsgJ8ZA δ b Pb c χ M tr).vp,
      k.2.1 < ringChar (ZMod p) ∧ k.2.2.1 < ringChar (ZMod p) ∧ k.2.2.2 < ringChar (ZMod p) := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := hacc.hvp0 k hk
    exact ⟨by omega, by omega, h3⟩
  have hcell : ∀ k : Fin 3, isCellN (claimNoun c k) = true →
      denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
        (1, (M.m k).1) = some (claimNoun c k) := by
    intro k hkc
    have hprov := Nock.Jet.PinJ8.regClaims_provided δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) hF' hsatC0 hbindC0 hacc.hinjC hacc.hadjC _ _ (chalsOK_J8 (δ := δ) χ)
      _ _ hacc.hsumC houtC hacc.hxneC hcountC _ hacc.hxC hvpr (regs := [0])
      (Ef := fun _ => encJ8 δ χ (claimNoun c k)) (rk := fun _ => rkC (claimNoun c k)) (idx := fun _ => (M.m k).1)
      (fun _ _ => List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkc⟩, rfl⟩))
      (fun _ _ => by
        have h62 : (rkC (claimNoun c k)).2 < 2 ^ 62 := Nat.mod_lt _ (by positivity)
        rw [hrc]
        exact ⟨hacc'.hclR k hkc, by omega, hacc'.hclI k hkc⟩) 0 (List.mem_singleton_self 0)
    rcases hprov with hc | hv
    · exact claimK_genuine_cell hq' (fun a b' => rfl) hE htabC hl.hvp
        (fun d hd he => hG _ (List.mem_append_right _ (List.mem_map_of_mem
          (List.mem_filter.mpr ⟨List.mem_finRange k, hkc⟩))) d hd he) hc
    · exfalso
      obtain ⟨h1, h2, -⟩ := hl.hvp _ hv
      exact rkC_ne hkc (Prod.ext h1 h2)
  have hden : ∀ k : Fin 3, denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
      (hdV (envX δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr 0) (![xS, xF, xE] k)) = some (claimNoun c k) := by
    intro k
    rw [AcceptsJ8ZLA.row0_hdZ δ b Pb Rg c χ _ tr (by omega) hacc k]
    exact den_claim _ _ c M.m k (hacc'.hclA k) (hacc'.hclI k) (hcell k)
  have hreal : (stX (envX δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr 0)).isChain = false :=
    AcceptsJ8ZLA.hrealJ8Z δ b Pb Rg c χ _ tr (by omega) hacc hacc'.hcellF
  obtain ⟨hH, hA, hF⟩ := hsoundJ8ZUA_ex δ b Pb hRg c χ (toMsgJ8ZA δ b Pb c χ M tr) tr R L hpG hqM hk hacc hacc3.hsatL hacc3.hbindL hout
    { rdX := hl.rdX, budX := hl.budX, rdP := hl.rdP, budP := hl.budP, rdS := hl.rdS, budS := hl.budS, hcount := hl.hcount, rdV := hl.rdV, budV := hl.budV, rdWC := hl.rdWC, rdWW := hl.rdWW, hext := hl.hext, hprs := hl.hprs, hvp := hl.hvp, hXW := hl.hXW, hHXW := hl.hHXW, hRA := hl.hRA, hsA := hl.hsA, hidxA := hl.hidxA, hrn := hl.hrn, hB := hl.hB, hwRA := hl.hwRA, houtA := hl.houtA, hservedA := hl.hservedA, 
      hcountC := hcountC, hcountA := hcountA_ofZA δ b Pb c χ M tr hacc'.hlenA, hinjE := hinjE,
      hseed := AcceptsJ8ZLA.hseedJ8Z δ b Pb Rg c χ _ tr (by omega) hacc, hreal := hreal,
      hs := hden 0, hf := hden 1, he := hden 2 }
  exact ⟨hH, hA, hF, hcell⟩

/-- **`hsoundJ8XUA_ex` with the axis bound and the cell table exported** : also `AxOK` at every
active record of every compute row, and the two-provider acceptance of the cell table with its encoder and
external leaves (the inputs of `row_genuine2`).

`hsoundJ8XUA`, with the row accumulator `RowsAccXI` and the forest goal at the row environments of `toMsgJ8ZA`, and
the claim-cell decode `hcell`: every cell claim noun is the denotation of its handle's cell record. Same hypotheses
as the source theorem. -/
theorem hsoundJ8XUA_exA [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    {r0 : RowsJ8} {g0 : ℕ} (hacc3 : AcceptsJ8V.AcceptsJ8V δ b Pb Rg c χ M tr r0 g0) (h0 : Pb.krootsV = 0)
    (hout : ∀ s ∈ AtomFpxJ8.allJ8X (AtomFpxJ8.withFpxV δ b (withLiftC R L) Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV
      Pb.nodesA Pb.orbitA), ¬ s.mem tr χ)
    {rA : ℕ → ARow} (hl : LinkJ8XUA δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr R L rA) :
    Nock.Jet.HoldsN c ∧
    RowsAccXI Pb.n (fun r => envX δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr r)
      (fun r => stX (envX δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr r))
      (denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA) Rg combN ∧
    ForestReconGoal (stVS K) (lblOf (rowsWX (fun r => envX δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr r)
      (fun r => stX (envX δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr r)))) 1 Pb.n ∧
    (∀ k : Fin 3, isCellN (claimNoun c k) = true →
      denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
        (1, (M.m k).1) = some (claimNoun c k)) ∧
    (∀ k : Fin 3, denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
      (hdV (envX δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr 0) (![xS, xF, xE] k)) = some (claimNoun c k)) ∧
    (∀ r < Pb.n, ∀ y ∈ RowSemChipX.activeX (envX δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr r), AxOK y) ∧
    ∃ (z : 𝕂′) (E : Noun → FP 𝕂′) (vp : List (VKey 𝕂′)), (∀ a b', E (.cell a b') = FP.cons z (E a) (E b')) ∧
      InlineAtoms (ringChar (ZMod p)) z E ∧
      TableAccepts2 z (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
          (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))) vp ∧
      AtomLeaves E vp (extB p rA) := by
  have hacc' := hacc3
  have hacc := acceptsJ8ZA_of_V hacc' h0
  replace hout := AtomFpxJ8.outsideC_of_outsideX _ hout
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp : 2 ^ 63 + 1 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; omega
  have hF' := GeneratedField.primeFieldElems_zmod p
  have O := outJ8_of_outside R L b hout
  have hz2 : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) := by
    rw [(chalsMJ8_z (δ := δ) χ).1, (chalsMJ8_z (δ := δ) χ).2]
  have hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0 := by
    rw [hz2]; exact O.z_ne
  have houtC : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.D.valReqs tr χ) (R.D.valProvs tr χ) := O.valid hl.budV.1 hl.budV.2
  rw [hl.rdV.1, hl.rdV.2] at houtC
  have hcountC := hcountC_of' δ b Pb c χ M tr hacc'.hlenC
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hbindC
  have htabC := TwoProviderQ.cellTable_accepts2 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hF' hq'
    hzC hsatC0 hbindC0 hacc.hinjC hacc.hadjC hacc.hnpC _ _ (chalsOK_J8 (δ := δ) χ) _ _ hacc.hsumC houtC
    hacc.hxneC hcountC _ hacc.hxC hacc.hvp0
  rw [hz2] at htabC
  have hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (encJ8 δ χ) :=
    inlineAtoms_encZY (by rw [hrc]; exact hpG) _ _
  -- the census at the registered and claim cell nouns (Q2)
  have hG := LinkQ2J8.hinjE_of_outside (withLiftC R L) hout hq' O.z_ne hE htabC hl.hvp hl.hext hqM hk
    (G := censusG Pb c)
    (fun x hx => ⟨(hacc'.hcen x hx).1, fun v hv => hqM v (by rw [hrc]; exact (hacc'.hcen x hx).2 v hv)⟩) hl.hprsG
  have hinjE : ∀ id ∈ Pb.regs, ∀ d ∈ decodedNouns2 ((cellT δ b Pb χ (toMsgJ8ZA δ b Pb c χ M tr) tr).map (·.b0))
      (extB p rA), encJ8 δ χ (Nock.Jet.Autogen.compile p (Pb.Rt id)) = encJ8 δ χ d →
        Nock.Jet.Autogen.compile p (Pb.Rt id) = d :=
    fun id hid d hd he => hG _ (List.mem_append_left _ (List.mem_map_of_mem hid)) d hd he
  -- the claim's cell records are served
  have hvpr : ∀ k ∈ (toMsgJ8ZA δ b Pb c χ M tr).vp,
      k.2.1 < ringChar (ZMod p) ∧ k.2.2.1 < ringChar (ZMod p) ∧ k.2.2.2 < ringChar (ZMod p) := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := hacc.hvp0 k hk
    exact ⟨by omega, by omega, h3⟩
  have hcell : ∀ k : Fin 3, isCellN (claimNoun c k) = true →
      denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
        (1, (M.m k).1) = some (claimNoun c k) := by
    intro k hkc
    have hprov := Nock.Jet.PinJ8.regClaims_provided δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) hF' hsatC0 hbindC0 hacc.hinjC hacc.hadjC _ _ (chalsOK_J8 (δ := δ) χ)
      _ _ hacc.hsumC houtC hacc.hxneC hcountC _ hacc.hxC hvpr (regs := [0])
      (Ef := fun _ => encJ8 δ χ (claimNoun c k)) (rk := fun _ => rkC (claimNoun c k)) (idx := fun _ => (M.m k).1)
      (fun _ _ => List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkc⟩, rfl⟩))
      (fun _ _ => by
        have h62 : (rkC (claimNoun c k)).2 < 2 ^ 62 := Nat.mod_lt _ (by positivity)
        rw [hrc]
        exact ⟨hacc'.hclR k hkc, by omega, hacc'.hclI k hkc⟩) 0 (List.mem_singleton_self 0)
    rcases hprov with hc | hv
    · exact claimK_genuine_cell hq' (fun a b' => rfl) hE htabC hl.hvp
        (fun d hd he => hG _ (List.mem_append_right _ (List.mem_map_of_mem
          (List.mem_filter.mpr ⟨List.mem_finRange k, hkc⟩))) d hd he) hc
    · exfalso
      obtain ⟨h1, h2, -⟩ := hl.hvp _ hv
      exact rkC_ne hkc (Prod.ext h1 h2)
  have hden : ∀ k : Fin 3, denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
      (hdV (envX δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr 0) (![xS, xF, xE] k)) = some (claimNoun c k) := by
    intro k
    rw [AcceptsJ8ZLA.row0_hdZ δ b Pb Rg c χ _ tr (by omega) hacc k]
    exact den_claim _ _ c M.m k (hacc'.hclA k) (hacc'.hclI k) (hcell k)
  have hreal : (stX (envX δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr 0)).isChain = false :=
    AcceptsJ8ZLA.hrealJ8Z δ b Pb Rg c χ _ tr (by omega) hacc hacc'.hcellF
  obtain ⟨hH, hA, hF, hAx⟩ := hsoundJ8ZUA_exA δ b Pb hRg c χ (toMsgJ8ZA δ b Pb c χ M tr) tr R L hpG hqM hk hacc hacc3.hsatL hacc3.hbindL hout
    { rdX := hl.rdX, budX := hl.budX, rdP := hl.rdP, budP := hl.budP, rdS := hl.rdS, budS := hl.budS, hcount := hl.hcount, rdV := hl.rdV, budV := hl.budV, rdWC := hl.rdWC, rdWW := hl.rdWW, hext := hl.hext, hprs := hl.hprs, hvp := hl.hvp, hXW := hl.hXW, hHXW := hl.hHXW, hRA := hl.hRA, hsA := hl.hsA, hidxA := hl.hidxA, hrn := hl.hrn, hB := hl.hB, hwRA := hl.hwRA, houtA := hl.houtA, hservedA := hl.hservedA, 
      hcountC := hcountC, hcountA := hcountA_ofZA δ b Pb c χ M tr hacc'.hlenA, hinjE := hinjE,
      hseed := AcceptsJ8ZLA.hseedJ8Z δ b Pb Rg c χ _ tr (by omega) hacc, hreal := hreal,
      hs := hden 0, hf := hden 1, he := hden 2 }
  exact ⟨hH, hA, hF, hcell, hden, hAx, _, _, _, fun a b' => rfl, hE, htabC, hl.hvp⟩

/-- `hsoundJ8XUA` from its twin. -/
theorem hsoundJ8XUA_of_ex [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    {r0 : RowsJ8} {g0 : ℕ} (hacc3 : AcceptsJ8V.AcceptsJ8V δ b Pb Rg c χ M tr r0 g0) (h0 : Pb.krootsV = 0)
    (hout : ∀ s ∈ AtomFpxJ8.allJ8X (AtomFpxJ8.withFpxV δ b (withLiftC R L) Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV
      Pb.nodesA Pb.orbitA), ¬ s.mem tr χ)
    {rA : ℕ → ARow} (hl : LinkJ8XUA δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr R L rA) :
    Nock.Jet.HoldsN c :=
  (hsoundJ8XUA_ex δ b Pb hRg c χ M tr R L hpG hqM hk hacc3 h0 hout hl).1


end SoundX

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinLinkJ8A

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinLinkJ8A.hsoundJ8ZUA_ex
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinLinkJ8A.hsoundJ8ZUA_of_ex
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinLinkJ8A.hsoundJ8XUA_ex
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinLinkJ8A.hsoundJ8XUA_of_ex
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinLinkJ8A.hsoundJ8ZUA_exA
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinLinkJ8A.hsoundJ8XUA_exA
