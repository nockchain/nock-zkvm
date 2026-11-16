/-
  **The accepted-trace layer of `AcceptsJ9V` with the atom walk present.**
  `AcceptsJ9ZG` is `AcceptsJ8G.AcceptsJ8ZG` with `hsatX` at `pubVJ9`; `acceptsJ9ZG_of_V` derives it from `AcceptsJ9V`
  at `1 ≤ krootsV`.  The module also gives the `AcceptsJ9ZG` versions of the J-8 helpers (`AcceptsJ8ZBG` budgets,
  `AcceptsJ8ZWG` the compute-row link `rdWC`, `AcceptsJ8ZHG` the walk-read link `hHXW`, `AcceptsJ8ZXG` the
  atom-walk export, `LinkJ8NV.hXW_of_ioG` / `hHXV_ofZG`); the `hsatX` reads at `pubVJ9` go through `AcceptsJ9ZL`
  (`compReqs9_eq`, `envX9_trace`, `stX_of_trace`, `rhoX_pubVJ9`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9ZG
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

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G (AcceptsJ8ZG)

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8 bitFix bitFix_off)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayJ8 LayLe realize40 wdWJ8 cRowsJ8 envCJ8 stOfEnv
  stOfIdx stOfIdx_stIdx rowW_congr shV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX (stIdx)
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8 (stX stX_spec baseX_of_sat)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8 (rowW rowsWX)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8


open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G (AcceptsJ8ZG)

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec liftRec_inj)
open Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW restrictHQKWCell cellB0Of_hqkw
  cellChipHQKW_width)
open Nock.NockVMROM.Thm54.VclL.Handle.ProvXJ8 (exportRecK_lt)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8 bitFix bitFix_off)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8 (childHOfK)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal computeChipVCLHX nStates)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf compReqsX compReqsX_sum)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (BalJ8 reqsJ8 liftP den_prov_ne_of_out)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.Jet.FibreJ8 (effP)
open Nock.ComputeTable (FP)

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1H
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8


open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G (AcceptsJ8ZG)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZX (vxReqsAtZ vxProvsAtZ)

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.WalkVCL (KeysExported)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (restrictWalkK walkChipHQK_restrict_sat walkChipHQK_restrict_bind)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (restrictAtomCell atomChipHQ_restrict_cell_sat
  atomChipHQ_restrict_bind)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_ok)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 shV)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (c4 c5 c6 c7)

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R2V
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8


open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G (AcceptsJ8ZG)

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf compReqsX)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crC crM crW crJ crA staged_eq)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8)
open Nock.Jet.ChipJ8 (jetChipJ8)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.FibreJ8 (effP)

open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8


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

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)

open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9Z
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9ZL

noncomputable section

section Accept
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`AcceptsJ8ZG`**: `AcceptsJ8Z.AcceptsJ8Z` with the J chip present or absent (`JGenJ8.JChipOK`). -/
structure AcceptsJ9ZG (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) : Prop where
  -- compute
  hsatX : RAP.SatisfiesWithPreprocessing (computeChipVCLHX Pb.hn Pb.nodes b δ (chalVJ8 b χ)
    (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit) (qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ))
  hinjX : Function.Injective Pb.nodes
  hadjX : ∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω
  -- the cell table
  hsatC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.Satisfies
    (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)
  hbindC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).BindsPreprocessing
    (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)
  hinjC : Function.Injective Pb.nodesC
  hadjC : ∀ (i : Fin Pb.nC) (hi : (i : ℕ) + 1 < Pb.nC), Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesC i * Pb.orbitC.ω
  hnpC : Pb.nC < ringChar (ZMod p)
  -- the J-8 walk
  hsatW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).rap.Satisfies
    (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)
  hbindW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).BindsPreprocessing
    (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)
  hinjW : Function.Injective Pb.nodesW
  hadjW : ∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW), Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω
  hkW : 1 ≤ Pb.kroots
  hknW : Pb.kroots ≤ Pb.nW
  hkpW : Pb.kroots + Pb.nW < ringChar (ZMod p)
  hJk : JGenJ8.JChipOK δ b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)
  -- the atom table
  hsatA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
    (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  hbindA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
    (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  hinjA : Function.Injective Pb.nodesA
  hadjA : ∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω
  hnpA : Pb.nA < p
  -- the atom walk
  hsatV : (walkChipHQK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV).rap.Satisfies
    (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV)
  hbindV : (walkChipHQK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV).BindsPreprocessing
    (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV)
  hinjV : Function.Injective Pb.nodesV
  hadjV : ∀ (i : Fin Pb.nV) (hi : (i : ℕ) + 1 < Pb.nV), Pb.nodesV ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesV i * Pb.orbitV.ω
  hkV : 1 ≤ Pb.krootsV
  hknV : Pb.krootsV ≤ Pb.nV
  hkpV : Pb.krootsV + Pb.nV < ringChar (ZMod p)
  -- the public balance equations
  hGx : M.ρ 3 + (Quad.mk _ (M.pubsW WalkHQ.pubXQ) (M.pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (M.pubsJ 2) (M.pubsJ 3)) =
    Quad.mk _ (M.pubsC CellHQ.pubHQ) (M.pubsC (CellHQ.pubHQ + 1))
  hGp : M.ρ 4 = Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1))
  hGS : M.ρS + ((pinCons (p := p) (K := K) Pb.regs Pb.idx).map fun r =>
      (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (M.pubsJ 0) (M.pubsJ 1) =
    Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1))
  hsumC : (M.reqsC.map fun r => (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
    Quad.mk _ (M.pubsC 0) (M.pubsC 1) + (M.xsC.map fun x => x.2 * (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x.1)⁻¹).sum
  hxneC : ∀ x ∈ M.xsC, FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x.1 ≠ 0
  hbalA : Quad.mk _ (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
    Quad.mk _ (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
      ((M.wreqs.map (liftRec (K := K) (L := 𝕂′))).map fun r =>
        (compress (AtomServedQ.acoins δ (chalsAJ8Z δ χ)) r)⁻¹).sum
  -- the cell validity's external keys
  hxC : ∀ x ∈ M.xsC, ∃ k ∈ M.vp, x.1 = ClaimVS.claimVec δ k.1 (k.2.2.2 : ZMod p) (k.2.1 : ZMod p) (k.2.2.1 : ZMod p)
  hvp0 : ∀ k ∈ M.vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar (ZMod p)
  -- the J chip's public checks and the registry pin
  hlay : List.ofFn Pb.lay = layoutJ8 Pb.Rt Pb.regs Pb.ids
  hsmall : ∀ q ∈ layoutJ8 Pb.Rt Pb.regs Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p
  huniq : ((layoutJ8 Pb.Rt Pb.regs Pb.ids).filterMap tvKey).Nodup
  hTpl : ∀ i ∈ Pb.regs, Rg i = some ⟨(Pb.Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Pb.Rt i)⟩ ∧
    axPosB (Pb.Rt i) = true ∧ (Pb.Rt i).WellTyped p
  hnd : Pb.regs.Nodup
  hidx : ∀ id ∈ Pb.regs, Pb.idx id < p
  hrk : ∀ id ∈ Pb.regs, Pb.rk id ≠ (0, 0)
  hlt : ∀ id ∈ Pb.regs, (Pb.rk id).1 < ringChar (ZMod p) ∧ (Pb.rk id).2 < ringChar (ZMod p) ∧
    Pb.idx id < ringChar (ZMod p)
  hpinC : ∀ id ∈ Pb.regs, ClaimVS.claimVec δ
    (encZY (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))
      (Nock.Jet.Autogen.compile p (Pb.Rt id))) (Pb.idx id : ZMod p)
    ((Pb.rk id).1 : ZMod p) ((Pb.rk id).2 : ZMod p) ∈ M.reqsC

variable {δ b}

/-- **`AcceptsJ9V` at `1 ≤ krootsV` ⇒ `AcceptsJ9ZG` at `toMsgJ9Z`.** -/
theorem acceptsJ9ZG_of_V {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsJ9V.AcceptsJ9V δ b Pb Rg c χ M tr r g) (hpos : 1 ≤ Pb.krootsV) :
    AcceptsJ9ZG δ b Pb Rg c χ (toMsgJ9Z δ b Pb c χ M tr) tr :=
  have hV := AcceptsJ8V.aw_present_of_pos δ b h.hVk hpos
  {
  hsatX := h.hsatX
  hinjX := h.hinjX
  hadjX := h.hadjX
  hsatC := h.hsatC
  hbindC := h.hbindC
  hinjC := h.hinjC
  hadjC := h.hadjC
  hnpC := h.hnpC
  hsatW := h.hsatW
  hbindW := h.hbindW
  hinjW := h.hinjW
  hadjW := h.hadjW
  hkW := h.hkW
  hknW := h.hknW
  hkpW := h.hkpW
  hJk := h.hJk
  hsatA := h.hsatA
  hbindA := h.hbindA
  hinjA := h.hinjA
  hadjA := h.hadjA
  hnpA := h.hnpA
  hsatV := hV.1
  hbindV := hV.2.1
  hinjV := hV.2.2.1
  hadjV := hV.2.2.2.1
  hkV := hV.2.2.2.2.1
  hknV := hV.2.2.2.2.2.1
  hkpV := hV.2.2.2.2.2.2
  hGx := h.hGx
  hGp := h.hGp
  hGS := h.hGS
  hlay := h.hlay
  hsmall := h.hsmall
  huniq := h.huniq
  hTpl := h.hTpl
  hnd := h.hnd
  hidx := h.hidx
  hrk := h.hrk
  hlt := h.hlt
  hsumC := by
    show _ = _ + ((mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _).map _).sum
    rw [mbXs_sum δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ h.hsatA h.hbindA h.hinjA h.hadjA _ _
      (chalsAJ8Z_ok δ χ)]
    exact h.hsumC'
  hxneC := mbXs_den δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ h.hsatA _ _ (chalsAJ8Z_ok δ χ)
  hbalA := by
    show _ = _ + (((ServeH.walkXReqs b Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV _).map _).map _).sum
    rw [List.map_map]
    refine h.hbalA'.trans ?_
    congr 1
    exact (WalkTeleJ8.walkHQK_reqs_sumQ δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV _
      hV.1 hV.2.1 hV.2.2.1 hV.2.2.2.1).symm
  hxC := mbXs_claimVec δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _
  hvp0 := fun k hk => by
    obtain ⟨h1, h2, h3⟩ := mbVp_small δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ k hk
    exact ⟨h1, h2, by rw [ZMod.ringChar_zmod_n]; exact h3⟩
  hpinC := fun id hid => List.mem_append_right _ (List.mem_map.mpr ⟨id, hid, rfl⟩) }

end Accept

section BudgetsG9
open Nock.Jet.ChipJ8 (entsX ents0T ents1T ents2T ents3)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

variable {Rg : Nock.Jet.Registry} {r : RowsJ8} {g : ℕ}

theorem compLenZG9 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZG δ b Pb Rg c χ M tr) (hp : 17 < p) (bl : Bal) :
    (compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
        (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) bl).length ≤ ReadIOJ8.capB bl * Pb.n :=
  (AcceptsJ9ZL.compReqs9_eq δ b Pb c χ M tr bl) ▸
    ReadIOJ8.compReqsX_length_le hacc.hsatX (by rw [ZMod.ringChar_zmod_n]; exact hp) bl

/-- **`budX`** at `realIO`. -/
theorem budX_ofZG9 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZG δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g) :
    (reqsOf δ b Pb c χ M tr .x).length ≤ 3 * r.N + r.W + r.rd ∧
      (liftP (δ := δ) (provsJ8 δ b Pb χ M tr .x)).length ≤ r.D := by
  refine ⟨?_, ?_⟩
  · rw [reqsOf_length]
    have h1 := compLenZG9 δ b Pb c χ M tr hacc hp .x
    have h2 : (extJ8 δ b Pb c χ M tr .x).length = Pb.nW + jCount entsX Pb.lay := by
      simp only [extJ8, byBal]
      erw [List.length_append, walkXReqs_length, jRd_length]
    simp only [ReadIOJ8.capB] at h1
    have := hB.x1
    omega
  · simp only [liftP, List.length_map]
    show (cellProvsW b Pb.nodesC Pb.orbitC _ _ _).length ≤ r.D
    simp only [cellProvsW, List.length_map, List.length_finRange]
    exact hB.x2

/-- **`budP`** at `real40`. -/
theorem budP_ofZG9 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZG δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g) :
    (reqsOf δ b Pb c χ M tr .p).length ≤ 2 * r.N ∧
      (liftP (δ := δ) (provsJ8 δ b Pb χ M tr .p)).length ≤ 2 * r.W := by
  refine ⟨?_, ?_⟩
  · rw [reqsOf_length]
    have h1 := compLenZG9 δ b Pb c χ M tr hacc hp .p
    have h2 : (extJ8 δ b Pb c χ M tr .p).length = 0 := rfl
    simp only [ReadIOJ8.capB] at h1
    have := hB.p1
    omega
  · simp only [liftP, List.length_map]
    show (ServeH.walkPProvs b Pb.nodesW Pb.orbitW _ _ _).length ≤ 2 * r.W
    rw [walkPProvs_length]; have := hB.p2; omega

theorem atomIncProvs_length_leZ {F K' : Type} [Field F] [Field K'] [Algebra F K'] [DecidableEq F]
    (b' : Basis (Fin 3) F K') {h n w : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (chals pubs : ℕ → K') (Q : Fin w → F[X]) : (atomIncProvs b' nodes orbit chals pubs Q).length ≤ n := by
  unfold atomIncProvs
  exact (AcceptsJ8P.length_flatMap_ite_le _ _ _).trans (by simp)

/-- **`budS`** at `realIO`. -/
theorem budS_ofZG9 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZG δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g) :
    (reqsOf δ b Pb c χ M tr .s).length ≤ r.N + 2 * r.J + g ∧
      (effP (liftP (δ := δ) (provsJ8 δ b Pb χ M tr .s))).length ≤ r.calls + r.heads + r.blocks + r.J := by
  refine ⟨?_, ?_⟩
  · rw [reqsOf_length]
    have h1 := compLenZG9 δ b Pb c χ M tr hacc hp .s
    have h2 : (extJ8 δ b Pb c χ M tr .s).length =
        Pb.regs.length + (jCount ents0T Pb.lay + jCount ents1T Pb.lay) := by
      simp only [extJ8, byBal]
      erw [List.length_append, jCons_length]
      erw [List.length_map]
    simp only [ReadIOJ8.capB] at h1
    have := hB.s1
    omega
  · refine (List.length_filter_le _ _).trans ?_
    simp only [liftP, List.length_map]
    show (_ ++ (pad8 _ ++ pad8 _)).length ≤ _
    simp only [List.length_append, pad8, List.length_map, jProv_length, walkPProvs_length]
    have := atomIncProvs_length_leZ b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA)
    have := hB.s2
    omega

/-- **`hcount`** from the budgets and the frame's caps below `p`. -/
theorem hcount_ofZG9 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZG δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g)
    (hcap : 3 * r.N + r.W + r.rd < p ∧ 2 * r.N < p ∧ r.N + 2 * r.J + g < p) :
    ∀ bl, (reqsOf δ b Pb c χ M tr bl).length < p := by
  intro bl
  cases bl
  · exact lt_of_le_of_lt (budX_ofZG9 δ b Pb c χ M tr hacc hp hB).1 hcap.1
  · exact lt_of_le_of_lt (budP_ofZG9 δ b Pb c χ M tr hacc hp hB).1 hcap.2.1
  · exact lt_of_le_of_lt (budS_ofZG9 δ b Pb c χ M tr hacc hp hB).1 hcap.2.2

end BudgetsG9

section TwinsG
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {Rg : Nock.Jet.Registry}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
/-- **`LinkJ8.rdWC`** at `L := realize40 L0 (layPb Pb …) hL`: on a trace whose compute chip is accepted
(`AcceptsJ8.hsatX`), over `17 < p`, the compute rows `cRowsJ8` (coin-free environments, `stOfEnv`) are
`rowsWX` of the `frameJ8` environments `envX` and their one-hot states `stX`, and `cH = n`. -/
theorem rdWC_realize40ZG9 (Pb : PubJ8 p) (skel : List Noun) (hs : skel.length ≤ 3)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hL : LayLe (layPb Pb skel hs) r) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZG δ b Pb Rg c χ M tr) (hp : 17 < p) :
    (realize40 δ b L0 (layPb Pb skel hs) hL).cRows tr =
        rowsWX (fun i => envX δ b Pb c χ M tr i) (fun i => stX (envX δ b Pb c χ M tr i)) ∧
      (realize40 δ b L0 (layPb Pb skel hs) hL).cH tr = Pb.n := by
  refine ⟨?_, rfl⟩
  show cRowsJ8 Pb.hn Pb.nodes Pb.orbit tr = _
  funext i
  show rowW (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C (i - 1)) (stOfEnv (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C (i - 1))) =
    rowW (envX δ b Pb c χ M tr (i - 1)) (stX (envX δ b Pb c χ M tr (i - 1)))
  generalize i - 1 = k
  have htr : (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C k).trace = (envX9 δ b Pb c χ M tr k).trace := by
    simp only [envCJ8, envX9, TeleC.envsN]
    split_ifs <;> rfl
  have htr' : (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C k).trace = (envX δ b Pb c χ M tr k).trace :=
    htr.trans (envX9_trace δ b Pb c χ M tr k)
  have hB : BaseHoldsX (envX9 δ b Pb c χ M tr k) := by
    simp only [envX9, TeleC.envsN]
    split_ifs
    · exact baseX_of_sat Pb.hn Pb.nodes b δ _ _ Pb.orbit _ hacc.hsatX _ (mem_rowNodeSet _ _)
    · exact baseX_of_sat Pb.hn Pb.nodes b δ _ _ Pb.orbit _ hacc.hsatX _ (mem_rowNodeSet _ _)
  have hc : nStates < ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n]; exact hp
  have hoh := stX_spec hB hc
  have hoh' : OneHotAt (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C k) (stIdx (stX (envX9 δ b Pb c χ M tr k))) :=
    fun j hj => by rw [congrFun htr j]; exact hoh j hj
  rw [stOfEnv_of_oneHot hoh', stX_of_trace (envX9_trace δ b Pb c χ M tr k),
    TraceJ8.rowW_congr (fun j _ => congrFun htr' j)]

/-- **`LinkJ8.rdWC`, compute and walk fields** (`cRows`, `cH`, `wdW`), at `L := realize40 L0 (layPb Pb …) hL`. -/
theorem linkJ8_L2ZG9 (Pb : PubJ8 p) (skel : List Noun) (hs : skel.length ≤ 3)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hL : LayLe (layPb Pb skel hs) r) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZG δ b Pb Rg c χ M tr) (hp : 17 < p) :
    ((realize40 δ b L0 (layPb Pb skel hs) hL).cRows tr =
        rowsWX (fun i => envX δ b Pb c χ M tr i) (fun i => stX (envX δ b Pb c χ M tr i)) ∧
      (realize40 δ b L0 (layPb Pb skel hs) hL).cH tr = Pb.n) ∧
    (realize40 δ b L0 (layPb Pb skel hs) hL).wdW tr (toVSQ χ) =
      walkDataOf δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW))) :=
  ⟨rdWC_realize40ZG9 δ b Pb skel hs L0 hL c χ M tr hacc hp, rdWW_realize40 δ b Pb skel hs L0 hL χ M tr⟩


/-- **Every J-8 walk read is a cell-table provided key** on an accepted trace, outside the compute's handle IO
events at the real lists (`s` at the effective providers), with the `x` count `< p`. -/
theorem walkX_servedZG9 [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZG δ b Pb Rg c χ M tr)
    (hp : 64 ≤ p)
    (hx : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .x) (liftP (provsJ8 δ b Pb χ M tr .x)))
    (hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .p) (liftP (provsJ8 δ b Pb χ M tr .p)))
    (hs : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .s) (effP (liftP (provsJ8 δ b Pb χ M tr .s))))
    (hcx : (reqsOf δ b Pb c χ M tr .x).length < p) :
    ∀ j : Fin Pb.nW, ServeH.keyVec5 (K := K) WalkHC.xKeyH
        (wEF b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) j) ∈
      (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)).map
        Prod.fst := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hF := GeneratedField.primeFieldElems_zmod p
  have B : TeleCQX.BCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) :=
    ⟨by rw [hrc]; show 17 < p; omega, hacc.hsatX, hacc.hinjX, hacc.hadjX⟩
  have hcv := VerJ8.coinsCV_J8 δ b χ
  have hG := (VerJ8.goodCJ8_iff (δ := δ) (b := b) c M.m M.ρ M.ρS χ M.pubsC M.pubsW M.pubsJ M.ρS 0).2
    ⟨hacc.hGx, hacc.hGp, add_zero _⟩
  have he := JGenJ8.extX_sumQG δ b (coinsCV b δ (chalVJ8 b χ)) Pb.kroots Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ)
    M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) hacc.hsatW hacc.hbindW hF (by rw [hrc]; exact hp)
    hacc.hinjW hacc.hadjW ((VerJ8.mcoins_J8 δ χ).trans hcv.symm)
    Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)
    hacc.hJk ((VerJ8.coinsJX_J8 δ χ).trans hcv.symm)
  have hpr := BalXJ8.provsX_sumQ δ b (coinsCV b δ (chalVJ8 b χ)) Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) hacc.hsatC hacc.hbindC hacc.hinjC hacc.hadjC
    ((VerJ8.mcoins_J8 δ χ).trans hcv.symm)
  have hbx : ServedJ8.rhoX (b := b) (δ := δ) (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) .x +
      ((extJ8 δ b Pb c χ M tr .x).map fun r => (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum =
      ((provsJ8 δ b Pb χ M tr .x).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) q.1))⁻¹).sum := by
    show _ + ((ServeH.walkXReqs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) ++
      Nock.Jet.RapJetJ8.jRd b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)).map
        _).sum = ((cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)).map
          _).sum
    convert hG .x using 2 <;> first | exact he | exact hpr
  have hne : ∀ bl, ∀ r ∈ compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
      (pubVal := pubVJ9 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
      (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) bl,
      compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r) ≠ 0 := by
    intro bl r hr
    rw [AcceptsJ9ZL.compReqs9_eq δ b Pb c χ M tr bl] at hr
    cases bl with
    | s => exact TeleC.den_ne_of_out _ _ _ _ hs _ (List.mem_map_of_mem (List.mem_append_left _ hr))
    | x => exact TeleC.den_ne_of_out _ _ _ _ hx _ (List.mem_map_of_mem (List.mem_append_left _ hr))
    | p => exact TeleC.den_ne_of_out _ _ _ _ hpp _ (List.mem_map_of_mem (List.mem_append_left _ hr))
  have hserved : ∀ r ∈ reqsOf δ b Pb c χ M tr .x, r ∈ (liftP (provsJ8 δ b Pb χ M tr .x)).map Prod.fst := by
    refine ServeH.served_of_balance (p := p) _ _ _ _ (TeleC.den_ne_of_out _ _ _ _ hx)
      (den_prov_ne_of_out _ _ _ _ hx) ?_ hcx hx
    have h1 := compReqsX_sum B hne .x
    rw [AcceptsJ9ZL.compReqs9_eq δ b Pb c χ M tr .x] at h1
    change _ = ServedJ8.rhoX (K := K) (b := b) (δ := δ) (pubVal := pubVJ9 δ b c M.m M.ρ M.ρS χ) .x at h1
    rw [rhoX_pubVJ9 δ b c M.m M.ρ M.ρS χ .x] at h1
    have h2 := hbx
    unfold reqsOf reqsJ8 liftP
    rw [List.map_map, List.map_append, List.sum_append, List.map_map]
    simp only [Function.comp_def] at h1 ⊢
    rw [h1]
    exact h2
  intro j
  have hc : ServeH.keyVec5 (K := K) WalkHC.xKeyH
      (wEF b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) j) ∈
      extJ8 δ b Pb c χ M tr .x :=
    List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange j))
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (hserved _ (List.mem_map_of_mem (List.mem_append_right _ hc)))
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨q0, hq0, liftRec_inj hqe⟩

/-- **`LinkJ8.hHXW`** on an accepted trace outside the compute's handle IO events at the real lists. -/
theorem hHXW_of_acceptsZG9 [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZG δ b Pb Rg c χ M tr)
    (hp : 64 ≤ p)
    (hx : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .x) (liftP (provsJ8 δ b Pb χ M tr .x)))
    (hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .p) (liftP (provsJ8 δ b Pb χ M tr .p)))
    (hs : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .s) (effP (liftP (provsJ8 δ b Pb χ M tr .s))))
    (hcx : (reqsOf δ b Pb c χ M tr .x).length < p) :
    ∀ j < Pb.nW, ∃ c' ∈ cellT δ b Pb χ M tr,
      (natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j).trace WChip.idx),
        WalkKJ8.childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) false,
        WalkKJ8.childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) true) = exportRecK c'.b0 :=
  hHXW_of_served δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC Pb.kroots Pb.hnW Pb.nodesW Pb.orbitW
    (chalsMJ8 δ χ) M.pubsW (by omega) _ hacc.hsatC _
    (walkX_servedZG9 δ b Pb c χ M tr hacc hp hx hpp hs hcx)


end TwinsG

section XVG9
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`LinkJ8.hXV` from the export lookup**: on an `AcceptsJ8` trace, with the terminal check
`pubsA(2,3) = pubsV(0,1)` and the validity pair outside the IO failure event of the atom walk's keys against the
atom table's export records, every key the atom walk consumes is a row of the decoded atom table. -/
theorem hXV_of_ioZG9 [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZG δ b Pb Rg c χ M tr)
    (hAV : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA 2) (M.pubsA 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV 0) (M.pubsV 1))
    (hout : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (vxReqsAtZ δ b Pb χ M tr) (liftWts (vxProvsAtZ δ b Pb χ M tr))) :
    KeysExported (atomTZ δ b Pb χ M tr)
      (walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
        (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
          (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV))).X := by
  have hsatC := atomChipHQ_restrict_cell_sat δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ hacc.hsatA
  have hbindC := atomChipHQ_restrict_bind δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ hacc.hbindA
  have hsatP := walkChipHQK_restrict_sat δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV _
    hacc.hsatV
  have hbindP := walkChipHQK_restrict_bind δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV _
    hacc.hbindV
  have hcnt : (vxReqsAtZ δ b Pb χ M tr).length < p := by
    rw [vxReqsAtZ, walkXInternal_length]
    have h := hacc.hkpV
    rw [ZMod.ringChar_zmod_n] at h
    omega
  exact walk_keys_exported δ Pb.krootsV b Pb.hnA Pb.nodesA Pb.orbitA Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ)
    M.pubsA M.pubsV _ _ hsatC hbindC hacc.hinjA hacc.hadjA hsatP hbindP hacc.hinjV hacc.hadjV _ _
    (chalsAJ8Z_ok δ χ) 0 (by rw [zero_add]; exact hAV) (p := p) [] (by simp) (by simp)
    (fun hc => hout (mem_IOFailureEventW_iff.mpr (Or.inl hc)))
    (fun hc => hout (mem_IOFailureEventW_iff.mpr (Or.inr (Or.inr hc)))) hcnt

/-- The walk's consumed export keys `vxReqsJ8` equal `vxReqsAtZ …`, read from the walk chip's columns. -/
theorem vxReqsJ8_viewZG9 (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    vxReqsJ8 δ b Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV tr = vxReqsAtZ δ b Pb χ M tr :=
  wXInt_congr δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV _ _ _ _ _ _ (by norm_num) (by rw [walk_w]; norm_num)
    fun j hj => congrArg tr.V (Fin.ext rfl)

/-- The atom table's export records `vxProvsJ8` equal the weights `liftWts (vxProvsAtZ …)` read from the cell chip's columns. -/
theorem vxProvsJ8_viewZG9 (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    vxProvsJ8 δ b Pb.nodesA Pb.orbitA tr = liftWts (vxProvsAtZ δ b Pb χ M tr) := by
  have hw : 183 ≤ (cellChip δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.w := by
    rw [cell_w]; norm_num
  have e := cXRec_congr δ b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) (restrictQ 129 205 shA tr.A)
    (restrictAtomCell δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA))
    (chalsAJ8Z δ χ) M.pubsA (by norm_num) hw fun j hj => congrArg tr.A (Fin.ext rfl)
  rw [vxProvsJ8, e]
  rfl

variable {r : RowsJ8} {P g : ℕ}

/-- Acceptance at `AcceptsJ9ZG` and a coin outside every summand of `allJ8X X` give the `X`-side readout hypotheses, given the stated request and provider equalities. -/
theorem hXV_of_outsideXZG9 [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZG δ b Pb Rg c χ M tr)
    (X : DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (hX : ∀ s ∈ allJ8X X, ¬ s.mem tr χ)
    (hrq : X.vxReqs tr χ = vxReqsJ8 δ b Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV tr)
    (hpv : X.vxProvs tr χ = vxProvsJ8 δ b Pb.nodesA Pb.orbitA tr)
    (hbV : Pb.nV ≤ r.AW) (hbA : Pb.nA ≤ r.A)
    (hAV : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA 2) (M.pubsA 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV 0) (M.pubsV 1)) :
    KeysExported (atomTZ δ b Pb χ M tr)
      (walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
        (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
          (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV))).X := by
  have h1 : (X.vxReqs tr χ).length ≤ r.AW := by
    rw [hrq, vxReqsJ8_length]; exact hbV
  have h2 : (X.vxProvs tr χ).length ≤ 2 * r.A := by
    rw [hpv]; exact (vxProvsJ8_length δ b Pb.nodesA Pb.orbitA tr).trans (by omega)
  have hout := afx_out_of_outsideX X hX h1 h2
  rw [hrq, hpv, vxReqsJ8_viewZG9 δ b Pb χ M tr, vxProvsJ8_viewZG9 δ b Pb χ M tr] at hout
  exact hXV_of_ioZG9 δ b Pb c χ M tr hacc hAV hout

/-- **`LinkJ8.hXV` at the real readout** `withFpxV R …` (the readout equations are `rfl`). -/
theorem hXV_withFpxVZG9 [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZG δ b Pb Rg c χ M tr)
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (hX : ∀ s ∈ allJ8X (withFpxV δ b R Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA), ¬ s.mem tr χ)
    (hbV : Pb.nV ≤ r.AW) (hbA : Pb.nA ≤ r.A)
    (hAV : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA 2) (M.pubsA 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV 0) (M.pubsV 1)) :
    KeysExported (atomTZ δ b Pb χ M tr)
      (walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
        (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
          (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV))).X :=
  hXV_of_outsideXZG9 δ b Pb c χ M tr hacc _ hX rfl rfl hbV hbA hAV


end XVG9

section FxRG9
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))] {r : RowsJ8}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 St40 sum40 fpx_out v4 v5 v6 v7)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (extY_below shV_round)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z)


/-- **`LinkJ8.hXW` from the fingerprint-export lookup** (the class of `LinkJ8R2V.hXV_of_io`): on an `AcceptsJ8Z`
trace, with `pubsC(2,3) = pubsW(0,1)` and the validity pair outside the IO failure event of the J-8 walk's keys
(at the `bitFix` view) against the cell table's export records, every key the J-8 walk consumes is a decoded cell
row. -/
theorem hXW_of_ioG9 [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZG δ b Pb Rg c χ M tr) (hp : 64 ≤ p)
    (hWC : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 2) (M.pubsC 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsW 0) (M.pubsW 1))
    (hout : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr) (fxProvsJ8 δ b Pb.nodesC Pb.orbitC tr)) :
    WalkVCL.KeysExported (cellT δ b Pb χ M tr)
      (walkDataOf δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (AtomWalkAW.restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)))).X := by
  have hF := GeneratedField.primeFieldElems_zmod p
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp64 : 64 ≤ ringChar (ZMod p) := by rw [hrc]; exact hp
  have hsatC := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _
    hacc.hsatC
  have hbindC := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _
    hacc.hbindC
  have hsatP := AtomWalkAW.walkChipHQK_restrict_sat δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _
    (WalkJ8.walkChipJ8_bitFix_sat δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _ hF hp64 hacc.hsatW)
  have hbindP := AtomWalkAW.walkChipHQK_restrict_bind δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ)
    M.pubsW _ (WalkJ8.walkChipJ8_bitFix_bind δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _
      hacc.hbindW)
  have hrq : walkXInternal δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (AtomWalkAW.restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW))) = fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr :=
    wXInt_bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW _ _ _ _ tr.W
  have hpv : liftWts (cellXRecords δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))) = fxProvsJ8 δ b Pb.nodesC Pb.orbitC tr := by
    have hw : 183 ≤ (cellChip δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.w := by
      rw [cell_w]; norm_num
    rw [cXRec_chip]
    exact congrArg liftWts
      (cXRec_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ hw (by norm_num) fun j hj => congrArg tr.M (Fin.ext rfl))
  rw [← hrq, ← hpv] at hout
  have hcnt : (walkXInternal δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (AtomWalkAW.restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)))).length < p := by
    rw [walkXInternal_length]
    have h := hacc.hkpW
    rw [hrc] at h
    omega
  exact walk_keys_exported δ Pb.kroots b Pb.hnC Pb.nodesC Pb.orbitC Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ)
    M.pubsC M.pubsW _ _ hsatC hbindC hacc.hinjC hacc.hadjC hsatP hbindP hacc.hinjW hacc.hadjW _ _
    (ProbJ8.chalsOK_J8 δ χ) 0 (by rw [zero_add]; exact hWC) (p := p) [] (by simp) (by simp)
    (fun hc => hout (mem_IOFailureEventW_iff.mpr (Or.inl hc)))
    (fun hc => hout (mem_IOFailureEventW_iff.mpr (Or.inr (Or.inr hc)))) (by simpa using hcnt)

end FxRG9

section HXVG9
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`LinkJ8.hHXV`, derived**: on an `AcceptsJ8Z` trace whose `wreqs` are the atom walk's reads, outside the atom
export event (`houtA`) with the count `< p`, every atom-walk row's read names a decoded atom-table row. -/
theorem hHXV_ofZG9 [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZG δ b Pb Rg c χ M tr)
    (hwr : M.wreqs = ServeH.walkXReqs b Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
      (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV))
    (houtA : ((AtomServedQ.acoins δ (chalsAJ8Z δ χ)).gamma, (AtomServedQ.acoins δ (chalsAJ8Z δ χ)).pole) ∉
      IOFailureEventW ((AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
          (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) ++ M.wreqs).map (BalanceQ.liftRec (K := K) (L := 𝕂′)))
        (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
          (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA))))
    (hcountA : (AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
      (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) ++ M.wreqs).length < p) :
    ∀ j < Pb.nV, ∃ c' ∈ atomTZ δ b Pb χ M tr,
      (natOf ((AtomWalkAW.walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
          (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV) j).trace WChip.idx),
        childHOf (AtomWalkAW.walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
          (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV) j) false,
        childHOf (AtomWalkAW.walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
          (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV) j) true) = exportRec c'.b0 := by
  have hF := GeneratedField.primeFieldElems_zmod p
  have hs := AtomServedQ.atom_consume_served δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ hacc.hsatA
    hacc.hbindA hacc.hinjA hacc.hadjA M.wreqs hacc.hbalA houtA hcountA
  intro j hj
  have hm := hs _ (List.mem_append_right _ (by rw [hwr]; exact List.mem_map_of_mem (List.mem_finRange ⟨j, hj⟩)))
  obtain ⟨c', hc', he⟩ := HxvJ8.atom_hHX_of_served δ b Pb.hnA Pb.nodesA Pb.orbitA Pb.krootsV Pb.hnV Pb.nodesV
    Pb.orbitV (chalsAJ8Z δ χ) M.pubsA M.pubsV _ _ hF hacc.hsatA ⟨j, hj⟩ hm
  refine ⟨c', hc', ?_⟩
  rw [show j = ((⟨j, hj⟩ : Fin Pb.nV) : ℕ) from rfl, AtomWalkProvJ8.walkEnvFA_eq_wEF]
  exact he

end HXVG9

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9ZG
