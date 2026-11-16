/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/SoundJ9AL.lean

  **`soundAL_core`, the ONE call to
  `FinalLGGAL.acceptsJ9AL_holdsN_finalLGG` from `AcceptsJ9AL`.** The J-9 AL twin of
  `J9A/SoundJ9A.soundA_core`.
  * Outside the J-9 AL list `RR49AL.allJ9AL` (the datum `XAL` over any J-9 A datum `X0` whose #1–#10 part is
    `withLiftCA (realIOA R8 …) (LL4A …) (cw9A …)`, plus `arithSZ`), for any J-8 datum `R8` whose #3 / #10 readouts
    are the real ones (#10 with the primitive nouns `censusP`), with the atom-walk handle reads and share of
    `soundA_core` verbatim, an `AcceptsJ9AL`-accepted trace satisfies `HoldsN c`.
  * #2 is `XAL`'s own `valReqsAL` (no `hRV`); #5 / #6 are `XAL`'s `reqsAL` / `provsAL` (`IOAL.ioAL`).
  * The service step `hsvc` of `finalLGG` is discharged inside: the axis share (`SvcShareAL.axShareAL_svc`) with the
    ALU share `AluSvcAL.aluShare` (ALU present) or the empty share (ALU absent).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.FinalLGGAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.OutAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.IOAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.CountAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.LinkAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.HelpAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.SvcShareAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AtomRowAL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.SoundJ9AL

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
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J9A (sum40A)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL (AcceptsJ9AL)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (BalJ8 ProvP liftP rhoX)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (RecOK9I)
open Nock.NockVMROM.Thm54.VclL.Handle.DenJ9A (denJ9A)
open Nock.NockVMROM.Thm54.VclL.Handle.SoundJ9A (fpx_outA wchain_outA)

section AluShare
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The ALU share of the service step** at one J-9 A denotation `denJ9A tC p rA V` (`rA` the atom table's reader):
ALU present, `AluSvcAL.aluShare` (the `preg` / `hdr` provides) with its served consumes (`hsv`, from the J share),
the tags of the other provides, the export reads `Cell3` (`AluSvcAL.cell3_of_x`, from the `.x` block served) and
the per-call semantics `AluSvcAL.hsemAL`; ALU absent, `aluPL = []`.
`hsemAL` carries the two `AluSZOps` workarounds: the consumed arithmetic event is `RR49AL.arithAL` (`harith`, gap (i)), and
the ALU context's reader is the padded `AtomWalkAL.rStar rA nA`, moved back to `rA` inside `hsemAL` (gap (ii)). -/
theorem aluShareAL (hpG : p = Nock.Atoms.p) {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry}
    {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {r : RowsJ9AL} {g : ℕ}
    (hacc : AcceptsJ9AL δ b Pb Rg c χ M tr r g) (harith : ¬ (RR49AL.arithAL δ b r Pb).mem tr χ)
    (hy : Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 2) (chalsAJ8Z δ χ 3) ≠ 0)
    (hserved : ValidityServed (cellTableOf δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
      (AtomChipHQ.restrictAtomCell δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
        (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA))))
    (hRA : ∀ k : Fin Pb.nA, AtomChipHQ.Reads (AtomServedQ.aEF b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
      (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA) k) (rAT (K := K) b Pb.toPubJ8 tr.toJ8 k))
    (hsU : ∀ k : Fin Pb.nA, ReaderR3bJ8.SmallU (rAT (K := K) b Pb.toPubJ8 tr.toJ8 k))
    (hidxA : ∀ k : Fin Pb.nA, (rAT (K := K) b Pb.toPubJ8 tr.toJ8 k).idx = k)
    (hBA : AtomChipHQ.LimbsBounded (rAT (K := K) b Pb.toPubJ8 tr.toJ8))
    (hwRA : ∀ j, (rAT (K := K) b Pb.toPubJ8 tr.toJ8 j).wR ≤ 1)
    (hTout : ∀ j, Pb.nA ≤ j → (rAT (K := K) b Pb.toPubJ8 tr.toJ8 j).wR = 0 →
      (rAT (K := K) b Pb.toPubJ8 tr.toJ8 j).aR ≠ 0)
    (hden2 : ∀ j l, AtomChipHQ.Denotes (rAT (K := K) b Pb.toPubJ8 tr.toJ8) j l → p ≤ Nock.Atoms.val l → j < Pb.nA)
    (hvpL : ∀ (e : FP 𝕂′) (v : ℕ), ClaimVS.claimVec δ e (v : ZMod p) 0 0 ∈ RR49AL.aluFpL δ b Pb tr χ → v < p →
      (e, 0, 0, v) ∈ AcceptsJ8P.mbVp δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
        (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA))
    {q : ℕ} (tC : List (CellRowB0 q)) (V : ℕ → Option ℕ)
    (hpin : ∀ q' ∈ Pb.prims, denJ9A tC p (rAT (K := K) b Pb.toPubJ8 tr.toJ8) V (1, Pb.idxP q'.1) =
      some (Nock.Jet.Prim.primC q'.2))
    {JP pI pW pX pS : List ((Fin 8 → K) × K)}
    (hsv : ∀ c' ∈ RR49AL.aluSL δ b Pb tr ++ AcceptsJ9AL.pinRgP (p := p) (K := K) Pb,
      c' ∈ (JP ++ (pI ++ pW ++ (pX ++ RR49AL.aluPL δ b Pb tr) ++ pS)).map Prod.fst)
    (hJ7 : ∀ q' ∈ JP, ∃ k < 6, q'.1 ⟨7, by norm_num⟩ = algebraMap (ZMod p) K ((k : ℕ) : ZMod p))
    (hI7 : ∀ q' ∈ pI, q'.1 ⟨7, by norm_num⟩ = 0) (hW7 : ∀ q' ∈ pW, q'.1 ⟨7, by norm_num⟩ = 0)
    (hX7 : ∀ q' ∈ pX, q'.1 ⟨7, by norm_num⟩ = algebraMap (ZMod p) K ((5 : ℕ) : ZMod p))
    (hS7 : ∀ q' ∈ pS, q'.1 ⟨7, by norm_num⟩ = 0)
    {provsX : List ((Fin (mOf .x) → K) × K)} {extX : List (Fin (mOf .x) → K)}
    (hsvX : ∀ c' ∈ extX, c' ∈ provsX.map Prod.fst)
    (hXp : ProvP (p := p) (K := K) (RecOK9I (denJ9A tC p (rAT (K := K) b Pb.toPubJ8 tr.toJ8) V) V Rg combN) .x
      provsX)
    (hextX : ∀ c' ∈ RR49AL.aluXL δ b Pb tr, c' ∈ extX) :
    ProvP (p := p) (K := K) (RecOK9I (denJ9A tC p (rAT (K := K) b Pb.toPubJ8 tr.toJ8) V) V Rg combN) .s
      (RR49AL.aluPL δ b Pb tr) := by
  rcases hacc.hALk with ⟨hon, hsatL, hbindL, hinjL, hadjL, -, hpre⟩ | ⟨hoff, -⟩
  · subst hpG
    have eS : RR49AL.aluSL δ b Pb tr = aluRegReqsOf δ b Pb tr := by rw [RR49AL.aluSL, if_pos hon]
    rw [eS] at hsv
    have hsem := AluSvcAL.hsemAL hsatL hbindL hinjL hadjL hpre r hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA
        hacc.hnpA hy hserved hRA hsU hidxA hBA (fun k => hwRA k) hTout
        (AtomRowAL.hin_rAT δ b Pb tr χ M.pubsA hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA hacc.hnpA hserved)
        hden2 (AtomRowAL.rowRead_rAT b r Pb tr hacc.hbudV.2.2.1) (AtomRowAL.atomAL_len r Pb tr hacc.hbudV.2.2.1)
        (fun e v hm hv => hvpL e v (by rw [RR49AL.aluFpL, if_pos hon]; exact hm) hv) hacc.hlenL.2.1 harith tC V
    exact AluSvcAL.aluShare δ b hon hsatL hbindL hpre hacc.hndP hacc.hlenL.2.2 hacc.hPrim hpin
      (SvcShareAL.h7OAL δ b hJ7 hI7 hW7 hX7 hS7) (SvcShareAL.hservAL δ b hon hsv)
      (fun i hH => AluSvcAL.cell3_of_x δ b hsvX hXp i
        (hextX _ (by rw [RR49AL.aluXL, if_pos hon]; exact AluSvcAL.keyX_mem δ b i hH)))
      hsem
  · have e : RR49AL.aluPL δ b Pb tr = [] := by simp [RR49AL.aluPL, hoff]
    rw [e]
    intro q hq
    cases hq

end AluShare

section Core
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (xS xF xE)

/-- **The J-9 AL soundness core** (see the module header). -/
theorem soundAL_core [CharP K p] [CharP 𝕂′ p] {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {r : RowsJ9AL} {g P : ℕ}
    (hacc : AcceptsJ9AL δ b Pb Rg c χ M tr r g)
    (X0 : DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A (RR49A.rowsB r.toRowsJ9A) P
      (g + r.N + r.AX))
    (R8 : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 (RR49A.rowsB r.toRowsJ9A) P
      (g + r.N + r.AX))
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 (RR49A.rowsB r.toRowsJ9A))
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (LinkJ8Q1.layPb Pb.toPubJ8 skel hs) (RR49A.rowsB r.toRowsJ9A))
    (hN : Pb.n ≤ (RR49A.rowsB r.toRowsJ9A).N)
    (hout : ∀ s ∈ RR49AL.allJ9AL δ b
        { X0 with
          C := withLiftCA (RR49A.realIOA δ b R8 Pb.axOn Pb.spOn Pb.toPubJ9A)
            (RR49A.LL4A δ b L0 Pb.toPubJ9A skel hs hL Pb.axOn Pb.spOn) (Out40J9A.cw9A (K := K) Pb.toPubJ9A hN) }
        Pb c g, ¬ s.mem tr χ)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ (RR49A.rowsB r.toRowsJ9A).maxlen)
    (hk : 2 * fuelChip ≤ (RR49A.rowsB r.toRowsJ9A).leaves) (hmax : Pb.nA + 2 ≤ (RR49A.rowsB r.toRowsJ9A).maxlen)
    (hA3 : 3 + 2 * (RR49A.rowsB r.toRowsJ9A).A < p)
    (hcap : 3 * (RR49AL.rowsBL r).N + (RR49AL.rowsBL r).W + (RR49AL.rowsBL r).rd < p ∧ 2 * (RR49AL.rowsBL r).N < p ∧
      (RR49AL.rowsBL r).N + 2 * (RR49AL.rowsBL r).J + RR49AL.gL r g < p)
    -- the J-8 datum's #3 / #10 readouts (#10 WITH the primitive nouns `censusP`)
    (hRAV : R8.D.avReqs tr.toJ8 χ = RealAJ8.avReqsJ8 δ b Pb.toPubJ8 tr.toJ8 ∧
      R8.D.avProvs tr.toJ8 χ = RealAJ8.avProvsJ8 δ b Pb.toPubJ8 tr.toJ8)
    (hRprs : R8.D.prs tr.toJ8 = EncInjJ8.censusPairs (EncInjJ8.censusList2
      (TraceJ8.rowsMJ8 Pb.nodesC Pb.orbitC tr.toJ8) (extT8 b Pb.toPubJ8 tr.toJ8) ++
        ((censusG Pb.toPubJ8 c ++ claimX b Pb.toPubJ8 c tr.toJ8) ++ AcceptsJ9AL.censusP Pb)))
    -- the atom-walk handle reads and the atom-walk share (`soundA_core`'s, verbatim)
    (wreqs : List (Fin 5 → K))
    (hbalW : Quad.mk _ (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk _ (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
        ((wreqs.map (liftRec (K := K) (L := 𝕂′))).map fun r =>
          (compress (AtomServedQ.acoins δ (chalsAJ8Z δ χ)) r)⁻¹).sum)
    (houtA : ((AtomServedQ.acoins δ (chalsAJ8Z δ χ)).gamma, (AtomServedQ.acoins δ (chalsAJ8Z δ χ)).pole) ∉
      IOFailureEventW ((AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
          (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA) ++ wreqs).map (liftRec (K := K) (L := 𝕂′)))
        (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
          (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA))))
    (hcountA : (AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
      (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA) ++ wreqs).length < p)
    (hWsh : (∀ k : Fin Pb.nA, AtomChipHQ.Reads (AtomServedQ.aEF b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
        (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA) k) (rAT (K := K) b Pb.toPubJ8 tr.toJ8 k)) →
      (∀ k : Fin Pb.nA, ReaderR3bJ8.SmallU (rAT (K := K) b Pb.toPubJ8 tr.toJ8 k)) →
      (∀ k : Fin Pb.nA, (rAT (K := K) b Pb.toPubJ8 tr.toJ8 k).idx = k) →
      (∀ k, Pb.nA ≤ k → (rAT (K := K) b Pb.toPubJ8 tr.toJ8 k).inc = 0) →
      AtomChipHQ.LimbsBounded (rAT (K := K) b Pb.toPubJ8 tr.toJ8) →
      (∀ j, (rAT (K := K) b Pb.toPubJ8 tr.toJ8 j).wR ≤ 1) →
      ValidityServed (cellTableOf δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
        (AtomChipHQ.restrictAtomCell δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
          (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA))) →
      ∀ (sv : ℕ → Option ℕ) (D : HX → Option Noun) (Rg' : Nock.Jet.Registry),
      ProvP (p := p) (K := K) (RecOK9 D (valId Pb.nA (rAT (K := K) b Pb.toPubJ8 tr.toJ8) sv) Rg' combN) .s
        (pWA Pb.krootsV (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
          (qV δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsV)))) :
    Nock.Jet.HoldsN c := by
  set M' := toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8 with hM'
  set rA := rAT (K := K) b Pb.toPubJ8 tr.toJ8 with hrA
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp : 2 ^ 63 + 1 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hq : 2 ^ 63 < p := by omega
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; omega
  have hp20 : 20 < p := by omega
  have hp64 : 64 ≤ p := by omega
  have hp32 : 2 ^ 32 < p := by omega
  have hBp : Nock.Atoms.B < p := by rw [hpG]; norm_num [Nock.Atoms.B, Nock.Atoms.p, Nock.Field.p]
  have hF' := GeneratedField.primeFieldElems_zmod p
  -- (0) outside the J-9 AL list: outside `XAL`'s list (`hoC`), outside `arithSZ` (`harith`), outside #1 (`h40`)
  obtain ⟨hX, harith⟩ := RR49AL.outside_allJ9AL δ b _ Pb c g hout
  have hoC := AtomFpxJ8.outsideC_of_outsideX _ hX
  have h40 := OutAL.outside40AL δ b X0 (RR49A.realIOA δ b R8 Pb.axOn Pb.spOn Pb.toPubJ9A)
    (RR49A.LL4A δ b L0 Pb.toPubJ9A skel hs hL Pb.axOn Pb.spOn) (Out40J9A.cw9A (K := K) Pb.toPubJ9A hN) Pb c g hoC
  have hzne : Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) ≠ 0 := OutAL.zeroAL δ _ _ h40
  have hB := hacc.hbud
  have hz2 : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) := by
    rw [(chalsMJ8_z (δ := δ) χ).1, (chalsMJ8_z (δ := δ) χ).2]
  have hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0 := by
    rw [hz2]; exact hzne
  -- the ALU counts (`CountAL`)
  have hSL : (RR49AL.aluSL δ b Pb tr).length + 2 * Pb.prims.length ≤ 2 * Pb.nL := by
    subst hpG; exact CountAL.aluSL_pins_le δ b hacc.hALk
  have hpL : (RR49AL.aluPL δ b Pb tr).length ≤ 2 * Pb.nL := by
    subst hpG; exact CountAL.aluPL_le δ b hacc.hALk
  have hFpL : (RR49AL.aluFpL δ b Pb tr χ).length ≤ Pb.nL := by
    subst hpG; exact CountAL.aluFpL_le δ b χ
  have hAw : ∀ q ∈ RR49AL.aluPL δ b Pb tr, ∃ c' : Fin (mOf .s), 4 ≤ (c' : ℕ) ∧ q.1 c' ≠ 0 := by
    subst hpG; exact SvcShareAL.aluPL_hAw δ b
  have htagL : ∀ q ∈ RR49AL.aluPL δ b Pb tr,
      q.1 ⟨7, by norm_num⟩ = algebraMap (ZMod p) K ((7 : ℕ) : ZMod p) ∨
        q.1 ⟨7, by norm_num⟩ = algebraMap (ZMod p) K ((6 : ℕ) : ZMod p) ∨
        q.1 ⟨7, by norm_num⟩ = algebraMap (ZMod p) K ((3 : ℕ) : ZMod p) := by
    subst hpG; exact SvcShareAL.aluPL_tag δ b
  -- (a) the cell validity table (#2) at `XAL`'s `valReqsAL`
  have rV := LinkAL.rdV_viewAL δ b Pb Rg c χ M tr hp20 hacc
  have lV := RealJ9.valJ9_length δ b Pb.toPubJ8 c tr.toJ8 χ
  have hlenV : (RR49AL.valReqsAL δ b Pb c tr χ).length ≤
      3 + Pb.regs.length + 2 * Pb.nC + Pb.prims.length + Pb.nL := by
    have h := lV.1
    have hP : (AcceptsJ9AL.pinRecsP δ Pb χ).length = Pb.prims.length := by simp [AcceptsJ9AL.pinRecsP]
    simp only [RR49AL.valReqsAL, RealJ9.valReqsJ9, List.length_append] at h hFpL ⊢
    omega
  have hrdV := RR49AL.rdV_AL δ b (X := { X0 with
    C := withLiftCA (RR49A.realIOA δ b R8 Pb.axOn Pb.spOn Pb.toPubJ9A)
      (RR49A.LL4A δ b L0 Pb.toPubJ9A skel hs hL Pb.axOn Pb.spOn) (Out40J9A.cw9A (K := K) Pb.toPubJ9A hN) }) Pb c g tr χ
  have houtC := ListJ8C.valid_out_of_outsideC _ hoC
      (by
        rw [hrdV.1]
        show (RR49AL.valReqsAL δ b Pb c tr χ).length ≤ 3 + 2 * r.D + (g + r.N + r.AX + 3 * r.AL)
        have := hacc.hbudV.1; have := hB.x2; have := hacc.hlenL.2.1
        omega)
      (by
        rw [hrdV.2]
        show (RealVJ8.valProvsJ8 δ b Pb.toPubJ8 tr.toJ8 χ).length ≤ r.D + r.mb
        have := hacc.hbudV.2.1; have := hB.x2; have := lV.2
        omega)
  rw [hrdV.1, hrdV.2, rV.1, rV.2] at houtC
  have hcountC := LinkAL.hcountCAL δ b Pb c χ M tr hacc.hlenCP
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
    _ hacc.hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
    _ hacc.hbindC
  have hsumC := LinkAL.hsumCAL δ b hpG hacc
  have hxneC : ∀ x ∈ M'.xsC, FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x.1 ≠ 0 :=
    mbXs_den δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ hacc.hsatA _ _ (chalsAJ8Z_ok δ χ)
  have hxC : ∀ x ∈ M'.xsC, ∃ k ∈ M'.vp,
      x.1 = ClaimVS.claimVec δ k.1 (k.2.2.2 : ZMod p) (k.2.1 : ZMod p)
        (k.2.2.1 : ZMod p) :=
    mbXs_claimVec δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _
  have hvp0 : ∀ k ∈ M'.vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar (ZMod p) := fun k hk => by
    obtain ⟨h1, h2, h3⟩ := mbVp_small δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ k hk
    exact ⟨h1, h2, by rw [hrc]; exact h3⟩
  have htabC := TwoProviderQ.cellTable_accepts2 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC _ hF' hq'
    hzC hsatC0 hbindC0 hacc.hinjC hacc.hadjC hacc.hnpC _ _ (chalsOK_J8 (δ := δ) χ) _ _ hsumC houtC
    hxneC hcountC _ hxC hvp0
  rw [hz2] at htabC
  have hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3))
      (encJ8 δ χ) :=
    inlineAtoms_encZY (by rw [hrc]; exact hpG) _ _
  -- (b) the atom table's reader `rAT`
  have hEr := rAT_eq δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA
  have hRA : ∀ k : Fin Pb.nA, AtomChipHQ.Reads (AtomServedQ.aEF b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
      (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA) k) (rA k) := by
    rw [hrA, ← hEr]; exact LinkQ2J8.hRA_valReader _
  have hwRA : ∀ j, (rA j).wR ≤ 1 := by
    rw [hrA, ← hEr]; exact LinkQ2J8.hwRA_valReader _ (LinkQ2J8.atom_wR_bool hacc.hsatA)
  have hidxA : ∀ k : Fin Pb.nA, (rA k).idx = k := by
    rw [hrA, ← hEr]; exact ReaderR3bJ8.hidxA_valReader hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA hacc.hnpA
  have hBA : AtomChipHQ.LimbsBounded rA := by
    rw [hrA, ← hEr]; exact ReaderR3bJ8.hB_valReader hp32.le hacc.hsatA
  have hwout : ∀ k, Pb.nA ≤ k → (rA k).wR = 0 := by
    rw [hrA, ← hEr]; exact LinkQ2J8.wR_valReader_out _
  have hTout : ∀ j, Pb.nA ≤ j → (rA j).wR = 0 → (rA j).aR ≠ 0 := by
    rw [hrA, ← hEr]; exact LinkQ2J8.aR_valReader_out _
  have hrn : ∀ k, Pb.nA ≤ k → (rA k).inc = 0 := by
    rw [hrA, ← hEr]; exact LinkQ2J8.hrn_valReader _
  have hden2 : ∀ j l, AtomChipHQ.Denotes rA j l → p ≤ Nock.Atoms.val l → j < Pb.nA := by
    rw [hrA, ← hEr]; exact DenJ9A.hden2_valReader _ hBp
  -- (c) #3: the atom table is served (`XAL`'s #3 at `tr` is `R8`'s at `tr.toJ8`)
  have rAV := RealAJ8.rdAV_view δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA
  have hserved := ServedAJ8.hservedA_of_outside _ hoC
    hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA (chalsAJ8Z_ok δ χ) hacc.hvalA0
    ⟨hRAV.1.trans rAV.1, hRAV.2.trans rAV.2⟩
    ⟨by
      show (R8.D.avReqs tr.toJ8 χ).length ≤ _
      rw [hRAV.1]
      exact (RealAJ8.avReqsJ8_length δ b Pb.toPubJ8 tr.toJ8).trans
        (by have := hacc.hbudV.2.2.1; show _ ≤ 3 + 2 * r.A; omega),
     by
      show (R8.D.avProvs tr.toJ8 χ).length ≤ _
      rw [hRAV.2]
      exact (RealAJ8.avProvsJ8_length δ b Pb.toPubJ8 tr.toJ8).le.trans hacc.hbudV.2.2.1⟩ hA3
  -- (d) S1: `SmallU` at the reader, from the export consume of the #4 balance
  have hcs := AtomServedQ.consumeServedQ_of_balance δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _
    hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA wreqs hbalW houtA hcountA
  have hsU : ∀ k : Fin Pb.nA, ReaderR3bJ8.SmallU (rA k) := by
    rw [hrA, ← hEr]
    exact ReaderR3bJ8.smallU_valReader hq (by have := hacc.hnAS; omega) hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA
      hserved hcs
  have hy : Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 2) (chalsAJ8Z δ χ 3) ≠ 0 := by
    rw [chalsAJ8Z_of_ne δ χ (by omega) (by omega), chalsAJ8Z_of_ne δ χ (by omega) (by omega)]
    exact ListJ8C.atom_hz_of_outsideC _ hoC
  have hvp := AtomLeavesUJ8.hvp_of_mbU χ hq hpG hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA hacc.hnpA hy
    hserved hRA hsU hidxA hBA (fun k => hwRA k) hTout
  have hext := LinkQ2J8.hext_of_rows (q := p) hBA hwout hmax
  -- (e) the census (#10) over `(censusG ++ claimX) ++ censusP`
  obtain ⟨hXbig, hXext, hXsrc⟩ := LinkAL.claimX_factsAL δ b hp20 hacc
  set X := claimX (K := K) b Pb.toPubJ8 c tr.toJ8 with hX
  have hprsX : ∀ pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2
      ((cellT δ b Pb.toPubJ8 χ M' tr.toJ8).map (·.b0)) (extB p rA) ++
        ((censusG Pb.toPubJ8 c ++ X) ++ AcceptsJ9AL.censusP Pb)),
      pr ∈ (RR49AL.XAL δ b { X0 with
        C := withLiftCA (RR49A.realIOA δ b R8 Pb.axOn Pb.spOn Pb.toPubJ9A)
          (RR49A.LL4A δ b L0 Pb.toPubJ9A skel hs hL Pb.axOn Pb.spOn) (Out40J9A.cw9A (K := K) Pb.toPubJ9A hN) }
        Pb c g).C.D.prs tr := by
    intro pr hpr
    show pr ∈ R8.D.prs tr.toJ8
    rw [hRprs, rowsMJ8_eq_cellT δ b Pb.toPubJ8 χ M' tr.toJ8]
    exact hpr
  have hXatom : ∀ x ∈ X, ∃ v, x = .atom v ∧ lenL v ≤ (RR49A.rowsB r.toRowsJ9A).maxlen := by
    intro x hx
    rcases hXsrc x hx with ⟨k, hkb, rfl⟩ | ⟨j, hj⟩
    · have h := hacc.hcen' _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkb⟩, rfl⟩)))
      cases hn : claimNoun c k with
      | atom v =>
        rw [hn] at h
        exact ⟨v, rfl, (h.2 v (by simp [Noun.leafList])).trans hmax⟩
      | cell a b' => rw [hn] at hkb; simp [isBigN] at hkb
    · exact hext j x hj
  have hcenG : ∀ x ∈ (censusG Pb.toPubJ8 c ++ X) ++ AcceptsJ9AL.censusP Pb,
      x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ (RR49A.rowsB r.toRowsJ9A).maxlen := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · have h := hacc.hcen' x (List.mem_append_left _ (List.mem_append_left _ hx))
        exact ⟨h.1, fun v hv => (h.2 v hv).trans hmax⟩
      · obtain ⟨v, rfl, hv⟩ := hXatom x hx
        refine ⟨by simp [Noun.leaves, fuelChip], fun w hw => ?_⟩
        simp only [Noun.leafList, List.mem_singleton] at hw
        exact hw ▸ hv
    · have h := hacc.hcen' x (List.mem_append_right _ hx)
      exact ⟨h.1, fun v hv => (h.2 v hv).trans hmax⟩
  have hG := LinkQ2J8.hinjE_of_outside _ hoC hq' hzne hE htabC hvp hext hqM hk
    (G := (censusG Pb.toPubJ8 c ++ X) ++ AcceptsJ9AL.censusP Pb) hcenG hprsX
  have hinjE : ∀ id ∈ Pb.regs, ∀ d ∈ decodedNouns2 ((cellT δ b Pb.toPubJ8 χ M' tr.toJ8).map (·.b0))
      (extB p rA),
      encJ8 δ χ (Nock.Jet.Autogen.compile p (Pb.Rt id)) = encJ8 δ χ d →
        Nock.Jet.Autogen.compile p (Pb.Rt id) = d :=
    fun id hid d hd he => hG _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map_of_mem hid)))) d hd he
  have hinjP : ∀ q ∈ Pb.prims, ∀ d ∈ decodedNouns2 ((cellT δ b Pb.toPubJ8 χ M' tr.toJ8).map (·.b0))
      (extB p rA),
      encJ8 δ χ (Nock.Jet.Prim.primC q.2) = encJ8 δ χ d → Nock.Jet.Prim.primC q.2 = d :=
    fun q hq d hd he => hG _ (List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩)) d hd he
  have hM1 : 1 ≤ (RR49A.rowsB r.toRowsJ9A).maxlen :=
    (Nock.Atoms.one_le_lenL 0).trans (hqM 0 (by rw [hrc]; omega))
  have hinjX : ∀ a ∈ X, ∀ b' ∈ X, encJ8 δ χ a = encJ8 δ χ b' → a = b' := by
    refine EncInjJ8.encZY_inj_of_sep hzne (prs := (RR49AL.XAL δ b { X0 with
        C := withLiftCA (RR49A.realIOA δ b R8 Pb.axOn Pb.spOn Pb.toPubJ9A)
          (RR49A.LL4A δ b L0 Pb.toPubJ9A skel hs hL Pb.axOn Pb.spOn) (Out40J9A.cw9A (K := K) Pb.toPubJ9A hN) }
        Pb c g).C.D.prs tr)
      (k := (RR49A.rowsB r.toRowsJ9A).leaves) (M := (RR49A.rowsB r.toRowsJ9A).maxlen) (Λ := fuelChip)
      (fun pr hpr => hprsX pr (censusPairs_append_mem_right (censusPairs_append_mem
        (censusPairs_append_mem_right hpr))))
      (fun _pr hpr hlen hne hkk hm1 hm2 => ListJ8C.biv_out_of_outsideC _ hoC hpr hlen hne hkk hm1 hm2)
      (fun n hn => ?_) hk hM1 (fun n hn => ?_)
    · obtain ⟨v, rfl, -⟩ := hXatom n hn
      simp [Noun.leaves, fuelChip]
    · obtain ⟨v, rfl, hv⟩ := hXatom n hn
      intro x hx
      simp only [Noun.leafList, List.mem_singleton] at hx
      exact hx ▸ hv
  have hvpr : ∀ k ∈ M'.vp, k.2.1 < ringChar (ZMod p) ∧ k.2.2.1 < ringChar (ZMod p) ∧
      k.2.2.2 < ringChar (ZMod p) := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := hvp0 k hk
    exact ⟨by omega, by omega, h3⟩
  -- (f) the claim's cell records are served
  have hcell : ∀ k : Fin 3, isCellN (claimNoun c k) = true →
      denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
        (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M'.pubsC) rA (1, (M.m k).1) = some (claimNoun c k) := by
    intro k hkc
    have hprov := Nock.Jet.PinJ8.regClaims_provided δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
        (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M'.pubsC)) hF' hsatC0 hbindC0 hacc.hinjC hacc.hadjC _ _
      (chalsOK_J8 (δ := δ) χ) _ _ hsumC houtC hxneC hcountC _ hxC hvpr (regs := [0])
      (Ef := fun _ => encJ8 δ χ (claimNoun c k)) (rk := fun _ => rkC (claimNoun c k)) (idx := fun _ => (M.m k).1)
      (fun _ _ => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkc⟩, rfl⟩))))
      (fun _ _ => by
        have h62 : (rkC (claimNoun c k)).2 < 2 ^ 62 := Nat.mod_lt _ (by positivity)
        rw [hrc]
        exact ⟨hacc.hclR k hkc, by omega, hacc.hclI k (Or.inl hkc)⟩) 0 (List.mem_singleton_self 0)
    rcases hprov with hc | hv
    · exact claimK_genuine_cell hq' (fun a b' => rfl) hE htabC hvp
        (fun d hd he => hG _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_finRange k, hkc⟩))))) d hd he) hc
    · exfalso
      obtain ⟨h1, h2, -⟩ := hvp _ hv
      exact rkC_ne hkc (Prod.ext h1 h2)
  -- (g) the big case
  have hbig : ∀ k : Fin 3, isBigN p (claimNoun c k) = true →
      denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
        (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M'.pubsC) rA (2, (M.m k).1) = some (claimNoun c k) := by
    intro k hkb
    have hI := hacc.hclI k (Or.inr hkb)
    have hprov := Nock.Jet.PinJ8.regClaims_provided δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
        (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M'.pubsC)) hF' hsatC0 hbindC0 hacc.hinjC hacc.hadjC _ _
      (chalsOK_J8 (δ := δ) χ) _ _ hsumC houtC hxneC hcountC _ hxC hvpr (regs := [0])
      (Ef := fun _ => encJ8 δ χ (claimNoun c k)) (rk := fun _ => (0, 0)) (idx := fun _ => (M.m k).1)
      (fun _ _ => by
        show _ ∈ ((claimRecsJ8 δ χ c M.m ++ claimBigRecs δ χ c M.m) ++ pinRecsJ8 δ Pb.toPubJ8 χ) ++
          (AcceptsJ9AL.pinRecsP δ Pb χ ++ RR49AL.aluFpL δ b Pb tr χ)
        simp only [Nat.cast_zero]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkb⟩, rfl⟩))))
      (fun _ _ => by rw [hrc]; exact ⟨by omega, by omega, hI⟩) 0 (List.mem_singleton_self 0)
    rcases hprov with ⟨c', hc', heq⟩ | hv
    · exfalso
      simp only [Prod.mk.injEq] at heq
      exact cell_key_rank_pos hq' htabC.rows hc' ⟨heq.2.1.symm, heq.2.2.1.symm⟩
    · obtain ⟨-, -, v, hext', hEv⟩ := hvp _ hv
      have hn := hinjX _ (hXbig k hkb) _ (hXext k hkb _ hext') hEv
      show denK _ (extB p rA) (2, (M.m k).1) = _
      simp only [denK]
      rw [hext', ← hn]
  -- (h) the compute side
  have XC := xctxJ9A δ b Pb.toPubJ9A c χ M.toMsgJ9A' tr.toTrJ9A hp20 hacc.hsatX hacc.hinjX hacc.hadjX
  have hden : ∀ k : Fin 3, denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
      (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M'.pubsC) rA
      (hdV (envA δ b Pb.toPubJ9A c χ M.toMsgJ9A' tr.toTrJ9A 0) (![xS, xF, xE] k)) = some (claimNoun c k) := by
    intro k
    have : Fact (1 < p) := ⟨by omega⟩
    rw [row0_hdA δ b XC k]
    show denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
      (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M'.pubsC) rA
      ((((claimKH p (claimNoun c k) (M.m k).1).1 : ℕ) : ZMod p).val,
        (((claimKH p (claimNoun c k) (M.m k).1).2 : ℕ) : ZMod p).val) = some (claimNoun c k)
    cases hx : claimNoun c k with
    | atom v =>
      by_cases hv : p ≤ v
      · have hkb : isBigN p (claimNoun c k) = true := by rw [hx]; simp [isBigN, hv]
        have hI := hacc.hclI k (Or.inr hkb)
        simp only [claimKH, if_pos hv, ZMod.val_natCast, Nat.mod_eq_of_lt hI,
          Nat.mod_eq_of_lt (show 2 < p by omega)]
        rw [← hx]; exact hbig k hkb
      · simp only [claimKH, if_neg hv, ZMod.val_natCast, Nat.zero_mod, Nat.mod_eq_of_lt (Nat.lt_of_not_le hv)]
        rfl
    | cell a b' =>
      have hkc : isCellN (claimNoun c k) = true := by rw [hx]; rfl
      have hI := hacc.hclI k (Or.inl hkc)
      simp only [claimKH, ZMod.val_natCast, Nat.mod_eq_of_lt hI, Nat.mod_eq_of_lt (show 1 < p by omega)]
      rw [← hx]; exact hcell k hkc
  -- (i) the compute IO events (`IOAL.ioAL`), the compute walk (`OutAL.walkAL`), `hbal` (`HbalJ9AL.hbalAL`)
  have hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (RR49AL.reqsAL δ b Pb tr .p) (liftP (RR49AL.provsAL δ b Pb tr .p)) :=
    OutAL.hpAL δ b (RR49A.LL4A δ b L0 Pb.toPubJ9A skel hs hL Pb.axOn Pb.spOn)
      (Out40J9A.cw9A (K := K) Pb.toPubJ9A hN) h40
      (by
        show (RR49AL.reqsAL δ b Pb tr .p).length ≤ 2 * (RR49AL.rowsBL r).N
        exact IOAL.reqsAL_p_le δ b hp20 hB _ _ hacc.hsatX)
      (by
        show (liftP (δ := δ) (RR49AL.provsAL δ b Pb tr .p)).length ≤ 2 * (RR49AL.rowsBL r).W
        exact IOAL.provsAL_p_le δ b hB)
  obtain ⟨hioX, hioS, hioC⟩ := IOAL.ioAL δ b _ (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩) hoC hpp hacc hp20 hcap
    hSL hpL
  obtain ⟨hα9, hw9⟩ := OutAL.walkAL δ b (c := c) (M := M) hN
    (RR49A.LL4A δ b L0 Pb.toPubJ9A skel hs hL Pb.axOn Pb.spOn) h40
  have hbal := HbalJ9AL.hbalAL δ b hacc (by rw [hrc]; exact hp64) hpG
  -- (j) the J-8 walk: #1.4, #1.5 at `LL4A`, `hXW`, `hHXW`
  have hfx := fpx_outA _ (Out40J9A.cw9A (K := K) Pb.toPubJ9A hN) h40
    (by show (RealVJ8.fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr.toJ8).length ≤
          (RR49A.rowsB r.toRowsJ9A).W
        rw [RealVJ8.fxReqsJ8, walkXInternal_length]; exact hL.W)
    (by show (RealVJ8.fxProvsJ8 δ b Pb.nodesC Pb.orbitC tr.toJ8).length ≤ 2 * (RR49A.rowsB r.toRowsJ9A).D
        rw [RealVJ8.fxProvsJ8, liftWts_length]
        exact (cXRec_length δ b _ _ _ _ _).trans (by have := hB.x2; show _ ≤ 2 * r.D; omega))
  have hXW := NCJ9A.hXW_of_ioNC δ b Pb.toPubJ8 χ M' tr.toJ8 hacc.hsatC hacc.hbindC hacc.hinjC hacc.hadjC
    hacc.hsatW hacc.hbindW hacc.hinjW hacc.hadjW hacc.hkpW hp64
    (by show Quad.mk _ (M.pubsC 2) (M.pubsC 3) = Quad.mk _ (M.pubsW 0) (M.pubsW 1)
        rw [hacc.hfxC.1, hacc.hfxC.2]) hfx
  have hW := wchain_outA _ (Out40J9A.cw9A (K := K) Pb.toPubJ9A hN) h40
  have hWW := LinkJ8Q1.rdWW_realize40 δ b Pb.toPubJ8 skel hs L0 hL χ M' tr.toJ8
  have hWW' : (RR49A.LL4A δ b L0 Pb.toPubJ9A skel hs hL Pb.axOn Pb.spOn).wdW tr.toTrJ9A (toVSQ χ) = _ := hWW
  rw [hWW', ← (coinW_J8 δ χ).1, ← (coinW_J8 δ χ).2] at hW
  have hne : ∀ bl, ∀ x ∈ CompReqsX9.compReqsX9 (K := K) Pb.hn Pb.nodes Pb.orbit (chalVJ8 b χ)
      (pubVJ9 δ b c M.m M.ρ M.ρS χ)
      (qX9 δ b Pb.toPubJ9A tr.toTrJ9A (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) bl,
      compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := Quad (algebraMap (ZMod p) K δ)) x) ≠ 0 := by
    intro bl x hx
    have hm := List.mem_map_of_mem (f := liftRec (L := Quad (algebraMap (ZMod p) K δ)))
      (List.mem_append_left (HbalJ9AL.extACL δ b Pb χ M tr bl) hx)
    cases bl with
    | x => exact TeleC.den_ne_of_out _ _ _ _ (hioX .x (by decide)) _ hm
    | p => exact TeleC.den_ne_of_out _ _ _ _ (hioX .p (by decide)) _ hm
    | s => exact TeleC.den_ne_of_out _ _ _ _ hioS _ hm
  have hHXW := HelpAL.hHXW9AL (HoldsX9.bctx9_of_xctx XC) hbal hne (hioX .x (by decide)) (hioC .x) (by omega)
    Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC) hacc.hsatC
    Pb.kroots Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW)
    Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ)
    (RR49AL.aluXL δ b Pb tr) rfl rfl
  have hEinj := EncInjJ8.encInj2_of_outside _
    (ListJ8C.outside_sumJ8_D _ hoC .bivariateCensus (by decide) (by decide) (by decide)) hq' hzne hE
    htabC hvp hext hqM hk (fun pr hpr => hprsX pr (censusPairs_append_mem hpr))
  -- (k) the cell-side primitive pins (`AcceptsJ9AL.hReg_of_pinP`): the cell at `(1, idxP id)` is `primC op`
  have hpinD : ∀ q ∈ Pb.prims, denK ((cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
          (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC))).map (·.b0)) (extB p rA) (1, Pb.idxP q.1) =
        some (Nock.Jet.Prim.primC q.2) :=
    AcceptsJ9AL.hReg_of_pinP δ b hq hacc hzC _ _ (chalsOK_J8 (δ := δ) χ) _ _ hsumC houtC hxneC hcountC _ hxC hvp0
      (fun x hx => List.mem_append_right _ (List.mem_append_left _ hx)) (encJ8 δ χ)
      (fun a b' => by rw [hz2]; rfl) (by rw [hz2]; exact hE) (fun _ _ => rfl) hvp hinjP
  -- (l) the ALU validity reads are external atom keys (`CtxBuildAL.rank0_vp`)
  have hvpL : ∀ (e : FP (Quad (algebraMap (ZMod p) K δ))) (v : ℕ),
      ClaimVS.claimVec δ e (v : ZMod p) 0 0 ∈ RR49AL.aluFpL δ b Pb tr χ → v < p → (e, 0, 0, v) ∈ M'.vp :=
    fun e v hm hv => CtxBuildAL.rank0_vp δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC _ hF' hsatC0 hbindC0
      hacc.hinjC hacc.hadjC _ _ (chalsOK_J8 (δ := δ) χ) _ _ hsumC houtC hxneC hcountC M'.vp hxC hvpr hq'
      htabC.rows (List.mem_append_right _ (List.mem_append_right _ hm)) (by rw [hrc]; exact hv)
  -- (m) the J share of the service balance: every consume of `cS ++ pinCons ++ eA` is a J or other provide
  obtain ⟨provO, hpO⟩ : ∃ l : List ((Fin 8 → K) × K), l =
      pad8 (atomIncProvs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
          (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)) ++
        pWA Pb.krootsV (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
          (qV δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsV)) ++
        ((if Pb.axOn then AxisChipJ9.axTagProvs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
          (qAX δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsX) else []) ++ RR49AL.aluPL δ b Pb tr) ++
        pSA Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS
          (qSP δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsS) := ⟨_, rfl⟩
  obtain ⟨eA, heA⟩ : ∃ l : List (Fin 8 → K), l = RR49AL.pinsP Pb ++
      (if Pb.axOn then AxisChipJ9.axLimbReqs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
        (qAX δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsX) else []) ++ RR49AL.aluSL δ b Pb tr := ⟨_, rfl⟩
  obtain ⟨cS, hcS⟩ : ∃ l : List (Fin 8 → K), l = CompReqsX9.compReqsX9 (K := K) Pb.hn Pb.nodes Pb.orbit (chalVJ8 b χ)
      (pubVJ9 δ b c M.m M.ρ M.ρS χ) (qX9 δ b Pb.toPubJ9A tr.toTrJ9A (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) .s :=
    ⟨_, rfl⟩
  have hcJ : Nock.Jet.RapJetJ8.coinsJ δ (chalsJJ8 χ) = coinsCV b δ (chalVJ8 b χ) :=
    (coinsJ_J8 δ χ).trans (coinsCV_J8 δ b χ).symm
  have hextS : HbalJ9AL.extACL δ b Pb χ M tr .s = pinCons (p := p) (K := K) Pb.regs Pb.idx ++ eA ++
      jCons b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ) := by
    rw [heA]; rfl
  have hprovS : HbalJ9AL.provsACL δ b Pb χ M tr .s =
      jProv b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ) ++
        provO := by
    rw [hpO]; rfl
  have hJserv : ∀ c' ∈ cS ++ pinCons (p := p) (K := K) Pb.regs Pb.idx ++ eA,
      c' ∈ (jProv b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay
        (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ) ++ provO).map Prod.fst := by
    refine HelpAL.served_JALG hacc.hJk _ _ ?_ ?_ ?_
    · have h3 := JGenJ8.jet_tagged_sumG hacc.hJk
      have hc8 : (cS.map fun r => (compress (coinsCV b δ (chalVJ8 b χ))
          (liftRec (L := Quad (algebraMap (ZMod p) K δ)) r))⁻¹).sum =
          rhoX (b := b) (δ := δ) (pubVal := pubVJ9 δ b c M.m M.ρ M.ρS χ) .s := by
        rw [hcS]; exact TeleX9.compReqsX9_sum (HoldsX9.bctx9_of_xctx XC) hne .s
      have hS' : rhoX (b := b) (δ := δ) (pubVal := pubVJ9 δ b c M.m M.ρ M.ρS χ) .s +
          (List.map (α := Fin 8 → K) (fun r => (compress (coinsCV b δ (chalVJ8 b χ))
            (liftRec (L := Quad (algebraMap (ZMod p) K δ)) r))⁻¹)
            (pinCons (p := p) (K := K) Pb.regs Pb.idx ++ eA ++
              jCons b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay
                (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ))).sum =
          (List.map (α := (Fin 8 → K) × K) (fun q => algebraMap K (Quad (algebraMap (ZMod p) K δ)) q.2 *
            (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := Quad (algebraMap (ZMod p) K δ)) q.1))⁻¹)
            (jProv b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay
              (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ) ++ provO)).sum := by
        have h := hbal .s
        rw [hextS, hprovS] at h
        exact h
      rw [hcJ] at h3 ⊢
      rw [List.map_append, List.map_append, List.map_append, List.sum_append, List.sum_append,
        List.sum_append] at hS'
      rw [List.map_append, List.map_append, List.sum_append, List.sum_append]
      linear_combination hS' - h3 + hc8
    · rw [hcJ]
      have h2 : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
          IOFailureEventW ((cS ++ (pinCons (p := p) (K := K) Pb.regs Pb.idx ++ eA ++
              jCons b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay
                (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ))).map
            (liftRec (L := Quad (algebraMap (ZMod p) K δ))))
            (effP (liftP (m := 8) (jProv b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay
              (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ) ++ provO))) := by
        rw [hcS, heA, hpO]; exact hioS
      simp only [List.append_assoc] at h2 ⊢
      exact h2
    · have h : ((cS ++ (pinCons (p := p) (K := K) Pb.regs Pb.idx ++ eA ++
              jCons b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay
                (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ))).map
            (liftRec (L := Quad (algebraMap (ZMod p) K δ)))).length < p := by
        rw [hcS, heA]; exact hioC .s
      simp only [List.length_map, List.length_append] at h ⊢
      omega
  -- (n) the ALU share of the service step at the J-9 A denotation `D = denJ9A tC p rA V`
  have hsvE : ∀ c' ∈ eA, c' ∈ (jProv b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay
      (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ) ++ provO).map Prod.fst :=
    fun c' h => hJserv c' (List.mem_append_right _ h)
  rw [hpO] at hsvE
  have hJ7 : ∀ q ∈ jProv b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay
      (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ),
      ∃ k < 6, q.1 ⟨7, by norm_num⟩ = algebraMap (ZMod p) K ((k : ℕ) : ZMod p) := by
    intro q hq
    rcases ServeAL.jProv_tag q hq with h | h | h
    · exact ⟨1, by norm_num, h⟩
    · exact ⟨2, by norm_num, h⟩
    · exact ⟨3, by norm_num, h⟩
  have hX7 : ∀ q ∈ (if Pb.axOn then AxisChipJ9.axTagProvs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
      (qAX δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsX) else []),
      q.1 ⟨7, by norm_num⟩ = algebraMap (ZMod p) K ((5 : ℕ) : ZMod p) := by
    intro q hq
    split_ifs at hq
    · exact FinalJ9AX9.axTag_entry7 b _ _ _ _ _ q hq
    · cases hq
  have hAsh := fun (hsvX : ∀ c' ∈ HbalJ9AL.extACL δ b Pb χ M tr .x,
      c' ∈ (HbalJ9AL.provsACL δ b Pb χ M tr .x).map Prod.fst) hXp =>
    aluShareAL δ b hpG hacc harith hy hserved hRA hsU hidxA hBA hwRA hTout hden2 (fun e v hm hv => hvpL e v hm hv)
      ((cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
          (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC))).map (·.b0))
      (valId Pb.nA rA (svA Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS
        (qSP δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsS)))
      (fun q hq => by rw [DenJ9A.denJ9A_ne3 _ _ _ _ (by simp)]; exact hpinD q hq)
      (fun c' h => hsvE c' (by
        rw [heA]
        rcases List.mem_append.mp h with h | h
        · exact List.mem_append_right _ h
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))
      hJ7 (ServiceJ8.pad8_entry7 _) ShareJ9A.awShare_h7 hX7 ShareJ9A.spShare_h7 hsvX hXp
      (fun c' h => by
        show c' ∈ (_ ++ RR49AL.aluXL δ b Pb tr) ++ _
        exact List.mem_append_left _ (List.mem_append_right _ h))
  -- (o) the tags of the axis + ALU provides and the ALU provides' weight entries
  have h7X : ∀ q ∈ (if Pb.axOn then AxisChipJ9.axTagProvs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
      (qAX δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsX) else []) ++ RR49AL.aluPL δ b Pb tr,
      SubJ9A.NotJ7 (p := p) q.1 := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ShareJ9A.axShare_h7 hpG hacc.hAXk q hq
    · rcases htagL q hq with h | h | h
      · exact SubJ9A.notJ7_of_tag (t := 7) (by omega) (by norm_num) (by norm_num) (by omega) h
      · exact SubJ9A.notJ7_of_tag (t := 6) (by omega) (by norm_num) (by norm_num) (by omega) h
      · exact SubJ9A.notJ7_of_tag (t := 3) (by omega) (by norm_num) (by norm_num) (by omega) h
  -- (p) THE call
  exact FinalLGGAL.acceptsJ9AL_holdsN_finalLGG (δ := δ) (b := b) (χ := χ)
    (pv := pubVJ9 δ b c M.m M.ρ M.ρS χ) (C := XC) (hpG := hpG)
    (provs := HbalJ9AL.provsACL δ b Pb χ M tr) (ext := HbalJ9AL.extACL δ b Pb χ M tr) (hbal := hbal)
    (hnC := Pb.hnC) (nodesC := Pb.nodesC) (orbitC := Pb.orbitC) (chalsC := chalsMJ8 δ χ) (pubsC := M.pubsC)
    (QC := qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC) (hsatC := hacc.hsatC) (hbindC := hacc.hbindC)
    (hinjC := hacc.hinjC) (hadjC := hacc.hadjC)
    (kroots := Pb.kroots) (hnW := Pb.hnW) (nodesW := Pb.nodesW) (orbitW := Pb.orbitW) (chalsW := chalsMJ8 δ χ)
    (pubsW := M.pubsW) (QW := qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW) (hsatW := hacc.hsatW)
    (hbindW := hacc.hbindW) (hinjW := hacc.hinjW) (hadjW := hacc.hadjW)
    (nodesJ := Pb.nodesJ) (orbitJ := Pb.orbitJ) (pubsJ := M.pubsJ) (lay := Pb.lay)
    (PJ := qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ) (hJk := hacc.hJk)
    (Rt := Pb.Rt) (regs := Pb.regs) (ids := Pb.ids) (idx := Pb.idx) (rk := Pb.rk)
    (hnA := Pb.hnA) (nodesA := Pb.nodesA) (orbitA := Pb.orbitA) (chalsA := chalsAJ8Z δ χ) (pubsA := M.pubsA)
    (QA := qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA) (QL := qAL δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)
    (hQA := (qAL_toHQ δ b Pb.toPubJ8 tr.toJ8 _ _).symm) (hsatL := hacc.hsatL) (hbindL := hacc.hbindL)
    (hinjA := hacc.hinjA) (hadjA := hacc.hadjA)
    (hout := hioX) (houtS := hioS) (hcount := hioC)
    (hnpC := hacc.hnpC) (hzC := hzC) (γV := _) (ρV := _) (hokC := chalsOK_J8 (δ := δ) χ)
    (reqsC := _) (xsC := M'.xsC) (hsumC := hsumC) (houtC := houtC) (hxneC := hxneC)
    (hcountC := hcountC) (vp := M'.vp) (hxC := hxC) (hvp0 := hvp0)
    (E := encJ8 δ χ) (hconsE := fun a b' => by rw [hz2]; rfl) (hE := by rw [hz2]; exact hE)
    (rA := rA) (hvp := hvp) (hEinj := hEinj)
    (hkW := hacc.hkW) (hknW := hacc.hknW) (hkpW := hacc.hkpW) (hXW := hXW) (hHXW := hHXW) (houtW := hW)
    (hRg := hRg) (hlay := hacc.hlay) (hsmall := hacc.hsmall) (huniq := hacc.huniq) (hTpl := hacc.hTpl)
    (hnd := hacc.hnd) (hidx := hacc.hidx) (hrk := hacc.hrk) (hlt := hacc.hlt)
    (hpinC := fun id hid => List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨id, hid, rfl⟩)))
    (hinjE := hinjE)
    (hRA := hRA) (hsA := hsU) (hidxA := hidxA) (hrn := hrn) (hB := hBA) (hwRA := hwRA)
    (wreqs := wreqs) (hbalA := hbalW) (houtA := houtA) (hcountA := hcountA) (hnpA := hacc.hnpA) (hzA := hy)
    (hservedA := hserved) (hden2 := hden2) (hTout := hTout)
    (sv := svA Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS
      (qSP δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsS))
    (nS := nSA Pb.spOn (nS := Pb.nS))
    (hsv0 := ShareJ9A.spShare_ne0 hp32 hacc.hSPk) (hsvn := ShareJ9A.spShare_lt)
    (hnAS := ShareJ9A.spShare_nAS hq hacc.hnAS)
    (pW := pWA Pb.krootsV (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
      (qV δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsV)))
    (pX := (if Pb.axOn then AxisChipJ9.axTagProvs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
      (qAX δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsX) else []) ++ RR49AL.aluPL δ b Pb tr)
    (pS := pSA Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS
      (qSP δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsS))
    (h7W := ShareJ9A.awShare_h7) (h7X := h7X) (h7S := ShareJ9A.spShare_h7)
    (hS := ShareJ9A.spShare_prov hp32 (by have := hacc.hnAS; omega) hacc.hSPk rA)
    (hsvc := fun hD hsvX hXp hPp hI pJ hJ hsvS hsvP =>
      SvcShareAL.axShareAL_svc hpG hacc.hAXk
        (fun D Rg' => hWsh hRA hsU hidxA hrn hBA hwRA hserved (svA Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS
          (chalsMJ8 δ χ) M.pubsS (qSP δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsS)) D Rg')
        (ShareJ9A.spShare_prov hp32 (by have := hacc.hnAS; omega) hacc.hSPk rA)
        (fun c' hc' => by
          rw [hextS, heA]
          exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _
            (List.mem_append_right _ hc'))))
        (fun c' hc' => hc') hD hPp hI (hAsh hsvX hXp) hAw hJ hsvS hsvP)
    (eA := RR49AL.pinsP Pb ++ (if Pb.axOn then AxisChipJ9.axLimbReqs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
      (qAX δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsX) else []) ++ RR49AL.aluSL δ b Pb tr)
    (wX := ServeH.walkXReqs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW) ++ RR49AL.aluXL δ b Pb tr)
    (hprovX := rfl) (hextX := rfl) (hprovP := rfl) (hprovS := rfl) (hextS := rfl)
    (hseed := CompWalkJ9A.hseedA δ b XC) (hα := hα9) (hw := hw9)
    (hreal := CompWalkJ9A.hrealA δ b XC hacc.hcellF (by omega)) (x := c)
    (hs := hden 0) (hf := hden 1) (he := hden 2)
    (fun D Rg' => hWsh hRA hsU hidxA hrn hBA hwRA hserved (svA Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS
      (chalsMJ8 δ χ) M.pubsS (qSP δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsS)) D Rg')

end Core

end

end Nock.NockVMROM.Thm54.VclL.Handle.SoundJ9AL
