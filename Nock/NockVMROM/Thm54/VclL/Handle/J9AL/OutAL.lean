/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/OutAL.lean

  **The #1 (40th-class) exclusions outside the J-9 AL list.**
  The J-9 AL datum `RR49AL.XAL X` keeps `X`'s #1 summands along `TrJ9AL.toTrJ9A`.  At a
  J-9 A datum whose #1–#10 part is `withLiftCA R L C` (as `Out40J9A.XA9` and `ProbJ9A.XA9Z` are, by `rfl`):
  * `outside40AL`: outside `allJ8C (XAL …).C` at `tr`, outside every summand of `sum40A L C` at `tr.toTrJ9A`
    (the twin of `Lift40J9A.outside40CA`);
  * `zeroAL`, `hpAL`: the `z ≠ 0` and the `.p` handle-path IO exclusions (`Out40J9A.zero_outA` / `hp_outA`);
  * `walkAL`: S8's `hα` / `hw` at the twin rows (the twin of `CompWalkJ9A.walkA`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.RR49AL
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.SoundJ9A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.OutAL

noncomputable section

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

open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9Z
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9ZL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9ZG
open Nock.NockVMROM.Thm54.VclL.Handle.RealJ9
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9G
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AcceptsJ9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (computeChipVCLHX9)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J9A (CW9 withLiftCA outside40CA)
open Nock.NockVMROM.Thm54.VclL.Handle.Out40J9A (OutJ9A outJ9A_of_outside cw9A)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkV1J9A
open Nock.NockVMROM.Thm54.VclL.Handle.ShareJ9A (svA nSA pSA pWA)
open Nock.NockVMROM.Thm54.VclL.Handle.HbalJ9A (extAC provsAC)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combN)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (RecOK9)
open Nock.J9A.NounAx (valId)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (DataJ8X allJ8X)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J9A (sum40A cw9_out tile9_out)
open Nock.NockVMROM.Thm54.VclL.Handle.Out40J9A (cRows9 cRows9_eq zero_outA hp_outA)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9 Nock.NockVMROM.Thm54.VclL.Handle.TeleX9
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeX9 Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeX9

section Out
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ9AL} {P g₀ : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **Outside the J-9 AL list, outside the J-9 A #1 summands at `tr.toTrJ9A`.** -/
theorem outside40AL (X0 : DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A
      (RR49A.rowsB r.toRowsJ9A) P g₀)
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A
      (RR49A.rowsB r.toRowsJ9A) P g₀)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A (RR49A.rowsB r.toRowsJ9A))
    (C : CW9 (K := K) (TrJ9A (ZMod p)) StJ9A (RR49A.rowsB r.toRowsJ9A))
    (Pb : PubJ9AL p) (c : P8PublicClaim) (g : ℕ) {tr : TrJ9AL (ZMod p)} {χ : Coins frameJ8 K}
    (h : ∀ s ∈ allJ8C (RR49AL.XAL δ b { X0 with C := withLiftCA R L C } Pb c g).C, ¬ s.mem tr χ) :
    ∀ s ∈ sum40A L C, ¬ s.mem tr.toTrJ9A (toVSQ χ) := by
  intro s hs hm
  have h1 := ListJ8C.outside_sumJ8C _ h .fortieth
  exact h1 _ (List.mem_map.mpr ⟨s, hs, rfl⟩) ((mem_liftJ8 _ _ _ _ _).mpr hm)

/-- `z ≠ 0` outside the J-9 AL list. -/
theorem zeroAL (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A
      (RR49A.rowsB r.toRowsJ9A))
    (C : CW9 (K := K) (TrJ9A (ZMod p)) StJ9A (RR49A.rowsB r.toRowsJ9A)) {tr : TrJ9AL (ZMod p)}
    {χ : Coins frameJ8 K} (h40 : ∀ s ∈ sum40A L C, ¬ s.mem tr.toTrJ9A (toVSQ χ)) :
    Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) ≠ 0 := by
  have := zero_outA L C h40
  exact this

/-- The `.p` handle-path IO exclusion outside the J-9 AL list, at the compute coins. -/
theorem hpAL (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A
      (RR49A.rowsB r.toRowsJ9A))
    (C : CW9 (K := K) (TrJ9A (ZMod p)) StJ9A (RR49A.rowsB r.toRowsJ9A)) {tr : TrJ9AL (ZMod p)}
    {χ : Coins frameJ8 K} (h40 : ∀ s ∈ sum40A L C, ¬ s.mem tr.toTrJ9A (toVSQ χ))
    (h1 : (L.pReqs tr.toTrJ9A (toVSQ χ)).length ≤ 2 * (RR49A.rowsB r.toRowsJ9A).N)
    (h2 : (L.pProvs tr.toTrJ9A (toVSQ χ)).length ≤ 2 * (RR49A.rowsB r.toRowsJ9A).W) :
    ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (L.pReqs tr.toTrJ9A (toVSQ χ)) (L.pProvs tr.toTrJ9A (toVSQ χ)) := by
  rw [coinsCV_J8 δ b χ]
  exact hp_outA L C h40 h1 h2

/-- **S8's `hα`, `hw`** outside the J-9 AL list (the twin of `CompWalkJ9A.walkA`). -/
theorem walkAL {Pb : PubJ9AL p} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ9AL' p K δ}
    {tr : TrJ9AL (ZMod p)} (hN : Pb.n ≤ (RR49A.rowsB r.toRowsJ9A).N)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A
      (RR49A.rowsB r.toRowsJ9A))
    (h40 : ∀ s ∈ sum40A L (Out40J9A.cw9A (K := K) Pb.toPubJ9A hN), ¬ s.mem tr.toTrJ9A (toVSQ χ)) :
    limbVal b (chalVJ8 b χ) chalAlphaW ∉ tileSet (foOf9 (rowsWX9
      (fun r => LinkV1J9A.envA δ b Pb.toPubJ9A c χ M.toMsgJ9A' tr.toTrJ9A r)
      (fun r => stX9 (LinkV1J9A.envA δ b Pb.toPubJ9A c χ M.toMsgJ9A' tr.toTrJ9A r)))) Pb.n ∧
    (limbVal b (chalVJ8 b χ) chalAlphaW, limbVal b (chalVJ8 b χ) chalGammaW) ∉
      cwEvent9 (K := K) (rowsWX9 (fun r => LinkV1J9A.envA δ b Pb.toPubJ9A c χ M.toMsgJ9A' tr.toTrJ9A r)
        (fun r => stX9 (LinkV1J9A.envA δ b Pb.toPubJ9A c χ M.toMsgJ9A' tr.toTrJ9A r))) Pb.n := by
  have e : rowsWX9 (fun r => LinkV1J9A.envA δ b Pb.toPubJ9A c χ M.toMsgJ9A' tr.toTrJ9A r)
      (fun r => stX9 (LinkV1J9A.envA δ b Pb.toPubJ9A c χ M.toMsgJ9A' tr.toTrJ9A r)) =
      cRows9 Pb.toPubJ9A tr.toTrJ9A :=
    cRows9_eq Pb.toPubJ9A tr.toTrJ9A (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)
  rw [e, Lift40J8.limb_alphaW_J8, Lift40J8.limb_gammaW_J8]
  have h1 := tile9_out L _ h40
  have h2 := cw9_out L _ h40
  exact ⟨h1, h2⟩

end Out

end

end Nock.NockVMROM.Thm54.VclL.Handle.OutAL
