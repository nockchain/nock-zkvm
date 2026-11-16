/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/LinkV1J9A.lean

* `row0_pub9` (any public vector), `trace0_toJ8` (row 0 of the twin reads the J-8 projection `tr.toJ8` at the old
    columns, through `permX9`), `row0_hdA`, `claimRow0_eqA`, `claimRecsT9_eqA`, `rdV9_viewA`, `hcountC9A`.
  No `maxRecDepth`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9G
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.RapWalkX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.LinkV1J9A

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
open Nock Nock.Reified Nock.Framework Module Polynomial
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
open Nock Nock.Reified Nock.Framework Module Polynomial
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

open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9Z
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9ZL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9ZG
open Nock.NockVMROM.Thm54.VclL.Handle.RealJ9
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9ZL (envX9)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AcceptsJ9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (computeChipVCLHX9 eq_of_base9 permX9)

noncomputable section

/-! ## 1. Row 0 of the twin: the claim publics -/

section Gen
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chalV pv : ℕ → ZMod p}
  {P : Fin (computeChipVCLHX9 hn nodes b δ chalV pv orbit).rap.w → (ZMod p)[X]}

theorem eqg9 {env : Env (ZMod p)} (hB : ChipHX9.BaseHoldsX9 env) {g : EqG ℚ} (hg : g ∈ ChipHX9.eqGatesX9)
    (hσ : evalQX g.σ env = 1) : env.trace g.x = evalQX g.y.expr env := by
  have := eq_of_base9 hB hg
  simp only [EqG.gate, evalQX, cc, hσ, one_mul] at this
  exact sub_eq_zero.mp this

/-- **Row 0's claim handles are the publics `0..5`** on the twin, for ANY public vector (`row0_pub`'s proof). -/
theorem row0_pub9 {α γ seed : K} (XC : RapWalkX9.XCtx hn nodes b δ chalV pv orbit P α γ seed) :
    (CompReqsX9.envsN9 hn nodes orbit chalV pv P 0).trace xS.k = pv 0 ∧
    (CompReqsX9.envsN9 hn nodes orbit chalV pv P 0).trace xS.v = pv 1 ∧
    (CompReqsX9.envsN9 hn nodes orbit chalV pv P 0).trace xF.k = pv 2 ∧
    (CompReqsX9.envsN9 hn nodes orbit chalV pv P 0).trace xF.v = pv 3 ∧
    (CompReqsX9.envsN9 hn nodes orbit chalV pv P 0).trace xE.k = pv 4 ∧
    (CompReqsX9.envsN9 hn nodes orbit chalV pv P 0).trace xE.v = pv 5 := by
  have hB := RapWalkX9.baseE9 XC hn
  have hF : (CompReqsX9.envsN9 hn nodes orbit chalV pv P 0).trace firstX = 1 := by
    have := RapWalkX9.firstE9 XC hn
    simpa using this
  have key : ∀ (x y : ℕ), (⟨cc firstX, x, .pub y⟩ : EqG ℚ) ∈ (claimEq (F := ℚ)) →
      (CompReqsX9.envsN9 hn nodes orbit chalV pv P 0).trace x = pv y := by
    intro x y hg
    have hg9 : (⟨cc firstX, x, .pub y⟩ : EqG ℚ) ∈ ChipHX9.eqGatesX9 :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hg)))
    have h := eqg9 hB hg9 (by simpa [evalQX, cc] using hF)
    simpa [Opnd.expr, evalQX, RapWalkX9.pubE9 XC 0] using h
  exact ⟨key _ _ (by simp [claimEq, hpub]), key _ _ (by simp [claimEq, hpub]),
    key _ _ (by simp [claimEq, hpub]), key _ _ (by simp [claimEq, hpub]),
    key _ _ (by simp [claimEq, hpub]), key _ _ (by simp [claimEq, hpub])⟩

end Gen

section Val
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ9A} {g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (xS xF xE)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (envCJ8)

/-- The twin compute environments of a J-9 A trace at `pubVJ9`. -/
abbrev envA (Pb : PubJ9A p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ9A' p K δ) (tr : TrJ9A (ZMod p))
    (i : ℕ) : Env (ZMod p) :=
  CompReqsX9.envsN9 Pb.hn Pb.nodes Pb.orbit (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)
    (qX9 δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) i

/-- **Row 0 of the twin reads the J-8 projection** at every old column `j < 123` (`permX9 j` in RAP order). -/
theorem trace0_toJ8 (Pb : PubJ9A p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ9A' p K δ)
    (tr : TrJ9A (ZMod p)) (j : ℕ) (hj : j < 123) :
    (envA δ b Pb c χ M tr 0).trace j = (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.toJ8.C 0).trace j := by
  have hw : permX9 j < 137 := ChipHX9.permX9_lt (by simp only [ChipHX9.widthHX9]; omega)
  have hw' : permX9 j <
      (computeChipVCLHX9 Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit).rap.w := hw
  simp only [envA, CompReqsX9.envsN9, ChipHX9.Env.viaPerm, TeleC.envsN, dif_pos Pb.hn, TeleC.rEF, envCJ8,
    Framework.Reify.envOfTrace, dif_pos hw', dif_pos hj]
  all_goals rfl

/-- The twin compute context at `pubVJ9`. -/
theorem xctxJ9A (Pb : PubJ9A p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ9A' p K δ)
    (tr : TrJ9A (ZMod p)) (hp : 20 < p)
    (hsatX : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 Pb.hn Pb.nodes b δ (chalVJ8 b χ)
      (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit) (qX9 δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)))
    (hinjX : Function.Injective Pb.nodes)
    (hadjX : ∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω) :
    RapWalkX9.XCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX9 δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ))
      (limbVal b (chalVJ8 b χ) chalAlphaW) (limbVal b (chalVJ8 b χ) chalGammaW)
      (limbVal b (pubVJ9 δ b c M.m M.ρ M.ρS χ) pubSeed) :=
  ⟨hp, hsatX, hinjX, hadjX, rfl, rfl, pubVJ9_IC δ b c M.m M.ρ M.ρS χ, rfl, pubVJ9_out δ b c M.m M.ρ M.ρS χ⟩

/-- **Row 0's claim handles of the twin** (`row0_hd9`'s proof). -/
theorem row0_hdA {Pb : PubJ9A p} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ9A' p K δ}
    {tr : TrJ9A (ZMod p)} {α γ seed : K}
    (XC : RapWalkX9.XCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX9 δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) α γ seed) :
    ∀ k : Fin 3, hdV (envA δ b Pb c χ M tr 0) (![xS, xF, xE] k) =
      ((((claimHJ9 p c M.m k).1 : ℕ) : ZMod p).val, (((claimHJ9 p c M.m k).2 : ℕ) : ZMod p).val) := by
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := row0_pub9 XC
  have L := fun j (hj : j < 6) => pubVJ9_label δ b c M.m M.ρ M.ρS χ j hj
  intro k
  fin_cases k
  · simp [hdV]; rw [p0, p1, L 0 (by norm_num), L 1 (by norm_num)]; simp [labelJ9]
  · simp [hdV]; rw [p2, p3, L 2 (by norm_num), L 3 (by norm_num)]; simp [labelJ9]
  · simp [hdV]; rw [p4, p5, L 4 (by norm_num), L 5 (by norm_num)]; simp [labelJ9]

/-- **V1 `claimRow0_eqA`**: the claim serials off row 0 of an accepted J-9 A trace. -/
theorem claimRow0_eqA (Pb : PubJ9A p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ9A' p K δ) (tr : TrJ9A (ZMod p)) (hp : 20 < p) (hacc : AcceptsJ9A δ b Pb Rg c χ M tr r g)
    (k : Fin 3) : claimRow0 Pb.toPubJ8 tr.toJ8 k = (((claimHJ9 p c M.m k).2 : ℕ) : ZMod p) := by
  have XC := xctxJ9A δ b Pb c χ M tr hp hacc.hsatX hacc.hinjX hacc.hadjX
  have hd := row0_hdA (tr := tr) δ b XC k
  have h2 := congrArg Prod.snd hd
  simp only [hdV] at h2
  have hv := ZMod.val_injective p h2
  have hk : (![xS, xF, xE] k).v < 123 := by fin_cases k <;> decide
  unfold claimRow0
  rw [← trace0_toJ8 δ b Pb c χ M tr _ hk]
  exact hv

/-- **V1 `claimRecsT9_eqA`**: the readout's J-9 claim records are the verifier's on an accepted J-9 A trace. -/
theorem claimRecsT9_eqA (Pb : PubJ9A p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ9A' p K δ) (tr : TrJ9A (ZMod p)) (hp : 20 < p) (hacc : AcceptsJ9A δ b Pb Rg c χ M tr r g) :
    claimRecsT9 δ Pb.toPubJ8 c χ tr.toJ8 = claimRecsJ9 δ χ c M.m := by
  have hs : ∀ k, (isCellN (claimNoun c k) = true ∨ isBigN p (claimNoun c k) = true) →
      claimRow0 Pb.toPubJ8 tr.toJ8 k = (((M.m k).1 : ℕ) : ZMod p) := fun k hk => by
    rw [claimRow0_eqA δ b Pb Rg c χ M tr hp hacc k, claimHJ9_snd hk]
  unfold claimRecsT9 claimRecsJ9 claimRecsT claimRecsJ8 claimBigRecs
  congr 1
  · refine List.map_congr_left fun k hk => ?_
    have hc : isCellN (claimNoun c k) = true := (List.mem_filter.mp hk).2
    have := hs k (Or.inl hc)
    unfold claimRow0 at this
    rw [this]
  · refine List.map_congr_left fun k hk => ?_
    have hc : isBigN p (claimNoun c k) = true := (List.mem_filter.mp hk).2
    rw [hs k (Or.inr hc)]

/-- **V1 `rdV9_viewA`**: the #2 readout IS `LinkJ8X''.rdV`'s pair at `toMsgJ9Z` of the projections. -/
theorem rdV9_viewA (Pb : PubJ9A p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ9A' p K δ) (tr : TrJ9A (ZMod p)) (hp : 20 < p) (hacc : AcceptsJ9A δ b Pb Rg c χ M tr r g) :
    valReqsJ9 δ b Pb.toPubJ8 c tr.toJ8 χ = (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).reqsC ++
      cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC
        (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
          (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC
          (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC)) ∧
    valProvsJ8 δ b Pb.toPubJ8 tr.toJ8 χ = SVFrame.liftWts (cellVRecords δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
      (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
        (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC
        (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC))) ++
      (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).xsC := by
  have hw : 183 ≤ (cellChip δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.w := by
    rw [cell_w]; norm_num
  refine ⟨?_, ?_⟩
  · show (claimRecsT9 δ Pb.toPubJ8 c χ tr.toJ8 ++ pinRecsJ8 δ Pb.toPubJ8 χ) ++ _ =
      (claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb.toPubJ8 χ) ++ _
    rw [claimRecsT9_eqA δ b Pb Rg c χ M tr hp hacc, cVInt_chip]
    refine congrArg ((claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb.toPubJ8 χ) ++ ·) ?_
    exact cVInt_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ (by norm_num) hw fun j hj => congrArg tr.M (Fin.ext rfl)
  · show liftWts _ ++ mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) (fun _ => 0) tr.A =
      liftWts _ ++ mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
        (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)
    rw [cVRec_chip]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · exact congrArg liftWts
        (cVRec_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ (by norm_num) hw fun j hj => congrArg tr.M (Fin.ext rfl))
    · exact mbXs_congr δ b Pb.nodesA Pb.orbitA _ _ _ _ _ _ (by norm_num)
        (by rw [AtomChipHQ.atomChipHQ_width]; norm_num) (fun j hj => rfl) rfl rfl

/-- **V1 `hcountC9A`**: `hcountC` at the J-9 A message (`hcountC9G` at the projections; no acceptance needed). -/
theorem hcountC9A (Pb : PubJ9A p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ9A' p K δ)
    (tr : TrJ9A (ZMod p)) (hlen : 3 + Pb.regs.length + 2 * Pb.nC < p) :
    ((toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).reqsC ++ cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC
      (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
        (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC
        (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC))).length < p :=
  hcountC9G δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8 hlen

end Val

end

end Nock.NockVMROM.Thm54.VclL.Handle.LinkV1J9A

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.LinkV1J9A
#print axioms row0_pub9
#print axioms trace0_toJ8
#print axioms claimRow0_eqA
#print axioms claimRecsT9_eqA
#print axioms rdV9_viewA
#print axioms hcountC9A
end Axioms

