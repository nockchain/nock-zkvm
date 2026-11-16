/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ProbJ9AL.lean

  **THE J-9 AL bound.** The J-9 AL twin of
  `J9A/ProbJ9A.lean` (the bound at a present / absent atom walk, `probJ9AL_present` / `probJ9AL_absent`, and the final bound `probJ9AL_final`).
  * `soundAL_present` (`1 ≤ krootsV`) and `soundAL_absent` (`krootsV = 0`): `SoundJ9AL.soundAL_core` at the real data
    `CensusAL.XA9P` / `XA9ZP` (#10 over `censusG ++ claimX ++ censusP`, `withCensusP`), the atom-walk premises as in
    `ProbJ9A.soundA_present` / `soundA_absent` (read through `XAL`, definitionally `X`'s at `tr.toTrJ9A`).
  * **`probJ9AL_present`**, **`probJ9AL_absent`** (`RR49AL.probJ9AL_lt_155` at `XA9P` / `XA9ZP`, id parameter
    `g + N + AX`), **`probJ9AL_final`** (case on `krootsV`), **`probJ9AL_final_clean`**.
  * Binders of `probJ9AL_final_clean` = `ProbJ9A.probJ9A_final_clean`'s with `AcceptsJ9A → AcceptsJ9AL` (and the
    J-9 AL types `PubJ9AL`, `MsgJ9AL'`, `TrJ9AL`/`StJ9AL`, `RowsJ9AL`), the census budget `hreg9` replaced by
    **`hreg9P : (censusG ++ censusP).length + 6 ≤ 2^31`** (the primitive nouns ride on #10's
    budget; strictly stronger than `hreg9`, `CensusAL.hreg9_of`), plus **`hAL : r.AL ≤ 2^31`**.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.SoundJ9AL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.CensusAL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ProbJ9AL

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


open Nock.NockVMROM.Thm54.VclL.Handle.SoundJ9A (soundA_core)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (DataJ8X allJ8X)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZX (vxReqsAtZ vxProvsAtZ)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL (AcceptsJ9AL censusP)
open Nock.NockVMROM.Thm54.VclL.Handle.SoundJ9AL (soundAL_core)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ9A (hA3A)

section Corner
variable {p : ℕ} [Fact p.Prime]

/-- `soundAL_core`'s capacity premise at the J-9 AL rows (`rowsBL`, `gL`), below the census corner. -/
theorem hcapAL {r : RowsJ9AL} {g : ℕ} (hr : RowsLe r.toRowsJ8 EncInjJ8.cornerC) (hAX : r.AX ≤ 2 ^ 31)
    (hAL : r.AL ≤ 2 ^ 31) (hg : g ≤ 2 ^ 31) (hpG : p = Nock.Atoms.p) :
    3 * (RR49AL.rowsBL r).N + (RR49AL.rowsBL r).W + (RR49AL.rowsBL r).rd < p ∧ 2 * (RR49AL.rowsBL r).N < p ∧
      (RR49AL.rowsBL r).N + 2 * (RR49AL.rowsBL r).J + RR49AL.gL r g < p := by
  obtain ⟨hN, -, hW, -, -, -, hJ, -, -, -, -, -, hrd, -, -⟩ := hr
  simp only [EncInjJ8.cornerC, corner31] at hN hW hJ hrd
  subst hpG
  simp only [Nock.Atoms.p, Nock.Field.p]
  exact ⟨by show 3 * r.N + r.W + (r.rd + r.AL) < _; omega, by show 2 * r.N < _; omega,
    by show r.N + 2 * r.J + (g + r.N + r.AX + 3 * r.AL) < _; omega⟩

end Corner

section Wrap
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **S9 at an ABSENT atom walk** (`krootsV = 0`, `wreqs = []`), J-9 AL. -/
theorem soundAL_absent [CharP K p] [CharP 𝕂′ p] {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {r : RowsJ9AL} {g P : ℕ}
    (hacc : AcceptsJ9AL δ b Pb Rg c χ M tr r g) (h0 : Pb.krootsV = 0)
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8
      (RR49A.rowsB r.toRowsJ9A) P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 (RR49A.rowsB r.toRowsJ9A))
    (skel : List Noun) (hs : skel.length ≤ 3)
    (hL : LayLe (LinkJ8Q1.layPb Pb.toPubJ8 skel hs) (RR49A.rowsB r.toRowsJ9A))
    (hP : P = 2 ^ 66) (hnM : (LinkJ8Q1.layPb Pb.toPubJ8 skel hs).nM ≤ 2 ^ 31)
    (hreg9P : (AcceptsJ8P.censusG Pb.toPubJ8 c ++ censusP Pb).length + 6 ≤ 2 ^ 31)
    (hN : Pb.n ≤ (RR49A.rowsB r.toRowsJ9A).N)
    (hout : ∀ s ∈ RR49AL.allJ9AL δ b (CensusAL.XA9ZP δ b (g := g + r.N + r.AX) R0 L0 Pb c skel hs hL hP hnM hreg9P hN)
      Pb c g, ¬ s.mem tr χ)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ (RR49A.rowsB r.toRowsJ9A).maxlen)
    (hk : 2 * fuelChip ≤ (RR49A.rowsB r.toRowsJ9A).leaves) (hmax : Pb.nA + 2 ≤ (RR49A.rowsB r.toRowsJ9A).maxlen)
    (hA3 : 3 + 2 * (RR49A.rowsB r.toRowsJ9A).A < p)
    (hcap : 3 * (RR49AL.rowsBL r).N + (RR49AL.rowsBL r).W + (RR49AL.rowsBL r).rd < p ∧ 2 * (RR49AL.rowsBL r).N < p ∧
      (RR49AL.rowsBL r).N + 2 * (RR49AL.rowsBL r).J + RR49AL.gL r g < p) :
    Nock.Jet.HoldsN c := by
  have hoC := AtomFpxJ8.outsideC_of_outsideX _ (RR49AL.outside_allJ9AL δ b _ Pb c g hout).1
  have hbalW : Quad.mk _ (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk _ (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
        ((([] : List (Fin 5 → K)).map (liftRec (K := K) (L := 𝕂′))).map fun r =>
          (compress (AtomServedQ.acoins δ (chalsAJ8Z δ χ)) r)⁻¹).sum := by
    rcases hacc.hVk with ⟨-, -, -, -, h1, -⟩ | ⟨-, -, -, hx1, hx2, -, -⟩
    · omega
    · rw [hacc.hbalA', hx1, hx2, Quad.mk_zero']
      simp
  have rAX := rdAX_A δ b (g := g + r.N + r.AX) R0 Pb.toPubJ8 c skel hs hL hP hnM
    (hreg_of9 (CensusAL.hreg9_of hreg9P)) χ tr.toJ8 (chalsAJ8Z δ χ) M.pubsA
  have hac : AtomServedQ.acoins δ (chalsAJ8Z δ χ) = AtomServedQ.acoins δ (ProbJ8.chalsAJ8 δ χ) := by
    simp only [AtomServedQ.acoins, chalsAJ8Z_of_ne δ χ (show (33 : ℕ) ≠ 37 by decide) (by decide),
      chalsAJ8Z_of_ne δ χ (show (34 : ℕ) ≠ 37 by decide) (by decide),
      chalsAJ8Z_of_ne δ χ (show (35 : ℕ) ≠ 37 by decide) (by decide),
      chalsAJ8Z_of_ne δ χ (show (36 : ℕ) ≠ 37 by decide) (by decide)]
  have houtA : ((AtomServedQ.acoins δ (chalsAJ8Z δ χ)).gamma, (AtomServedQ.acoins δ (chalsAJ8Z δ χ)).pole) ∉
      IOFailureEventW ((AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
          (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA) ++ []).map (liftRec (K := K) (L := 𝕂′)))
        (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
          (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA))) := by
    rw [hac, List.append_nil]
    refine LinkQ2J8.houtA_of_outside _ hoC _ _ rAX.1 rAX.2 ?_ ?_
    · refine le_trans (le_of_eq (congrArg List.length rAX.1.symm)) ?_
      have h1 := axReqsJ8A_length δ b Pb.toPubJ8 tr.toJ8
      have := hacc.hbudV.2.2.1
      show (axReqsJ8A δ b Pb.toPubJ8 tr.toJ8).length ≤ r.A + r.inc + r.AW
      omega
    · refine le_trans (le_of_eq (congrArg List.length rAX.2.symm)) ?_
      show (RealAJ8.axProvsJ8 δ b Pb.toPubJ8 tr.toJ8).length ≤ r.A
      rw [RealAJ8.axProvsJ8_length]; exact hacc.hbudV.2.2.1
  have hcountA : (AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
      (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA) ++ []).length < p :=
    hcountA_ofZA δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8 hacc.hlenA
  exact soundAL_core δ b hRg hacc
    (RR49A.XA δ b (g := g + r.N + r.AX) R0 L0 Pb.toPubJ9A c skel hs hL hP hnM (CensusAL.hreg9_of hreg9P)
      Pb.axOn Pb.spOn)
    (CensusAL.withCensusP δ b (LinkJ9A.RR4A9 δ b (g := g + r.N + r.AX) R0 Pb.toPubJ8 c skel hs hL hP hnM
      (CensusAL.hreg9_of hreg9P)) Pb.toPubJ8 c (censusP Pb) hP hnM hreg9P)
    L0 skel hs hL hN hout hpG hqM hk hmax hA3 hcap ⟨rfl, rfl⟩ rfl [] hbalW houtA hcountA
    (fun _ _ _ _ _ _ _ => ShareJ9A.awShare_prov (fun h1 => absurd h1 (by omega)))

/-- **S9 at a PRESENT atom walk** (`1 ≤ krootsV`, `wreqs` = the atom walk's reads), J-9 AL. -/
theorem soundAL_present [CharP K p] [CharP 𝕂′ p] {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {r : RowsJ9AL} {g P : ℕ}
    (hacc : AcceptsJ9AL δ b Pb Rg c χ M tr r g) (hpos : 1 ≤ Pb.krootsV)
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8
      (RR49A.rowsB r.toRowsJ9A) P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 (RR49A.rowsB r.toRowsJ9A))
    (skel : List Noun) (hs : skel.length ≤ 3)
    (hL : LayLe (LinkJ8Q1.layPb Pb.toPubJ8 skel hs) (RR49A.rowsB r.toRowsJ9A))
    (hP : P = 2 ^ 66) (hnM : (LinkJ8Q1.layPb Pb.toPubJ8 skel hs).nM ≤ 2 ^ 31)
    (hreg9P : (AcceptsJ8P.censusG Pb.toPubJ8 c ++ censusP Pb).length + 6 ≤ 2 ^ 31)
    (hN : Pb.n ≤ (RR49A.rowsB r.toRowsJ9A).N)
    (hout : ∀ s ∈ RR49AL.allJ9AL δ b (CensusAL.XA9P δ b (g := g + r.N + r.AX) R0 L0 Pb c skel hs hL hP hnM hreg9P hN)
      Pb c g, ¬ s.mem tr χ)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ (RR49A.rowsB r.toRowsJ9A).maxlen)
    (hk : 2 * fuelChip ≤ (RR49A.rowsB r.toRowsJ9A).leaves) (hmax : Pb.nA + 2 ≤ (RR49A.rowsB r.toRowsJ9A).maxlen)
    (hA3 : 3 + 2 * (RR49A.rowsB r.toRowsJ9A).A < p) (hΛ : fuelChip ≤ (RR49A.rowsB r.toRowsJ9A).Λ)
    (hcap : 3 * (RR49AL.rowsBL r).N + (RR49AL.rowsBL r).W + (RR49AL.rowsBL r).rd < p ∧ 2 * (RR49AL.rowsBL r).N < p ∧
      (RR49AL.rowsBL r).N + 2 * (RR49AL.rowsBL r).J + RR49AL.gL r g < p) :
    Nock.Jet.HoldsN c := by
  have hoX := (RR49AL.outside_allJ9AL δ b _ Pb c g hout).1
  have hoC := AtomFpxJ8.outsideC_of_outsideX _ hoX
  have hV := AcceptsJ8V.aw_present_of_pos δ b hacc.hVk hpos
  set M' := toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8 with hM'
  set wr := ServeH.walkXReqs b Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
    (qV δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsV) with hwr
  have hbalW : Quad.mk _ (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk _ (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
        ((wr.map (liftRec (K := K) (L := 𝕂′))).map fun r =>
          (compress (AtomServedQ.acoins δ (chalsAJ8Z δ χ)) r)⁻¹).sum := by
    rw [List.map_map]
    refine hacc.hbalA'.trans ?_
    congr 1
    exact (WalkTeleJ8.walkHQK_reqs_sumQ δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV _
      hV.1 hV.2.1 hV.2.2.1 hV.2.2.2.1).symm
  have rAX := RealAJ8.rdAX_view δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA (chalsAJ8Z δ χ) M.pubsV
  have hac : AtomServedQ.acoins δ (chalsAJ8Z δ χ) = AtomServedQ.acoins δ (ProbJ8.chalsAJ8 δ χ) := by
    simp only [AtomServedQ.acoins, chalsAJ8Z_of_ne δ χ (show (33 : ℕ) ≠ 37 by decide) (by decide),
      chalsAJ8Z_of_ne δ χ (show (34 : ℕ) ≠ 37 by decide) (by decide),
      chalsAJ8Z_of_ne δ χ (show (35 : ℕ) ≠ 37 by decide) (by decide),
      chalsAJ8Z_of_ne δ χ (show (36 : ℕ) ≠ 37 by decide) (by decide)]
  have houtA : ((AtomServedQ.acoins δ (chalsAJ8Z δ χ)).gamma, (AtomServedQ.acoins δ (chalsAJ8Z δ χ)).pole) ∉
      IOFailureEventW ((AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
          (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA) ++ wr).map (liftRec (K := K) (L := 𝕂′)))
        (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
          (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA))) := by
    rw [hac]
    refine LinkQ2J8.houtA_of_outside _ hoC _ _ rAX.1 rAX.2 ?_ ?_
    · refine le_trans (le_of_eq (congrArg List.length rAX.1.symm)) ?_
      have := RealAJ8.axReqsJ8_length δ b Pb.toPubJ8 tr.toJ8
      have := hacc.hbudV.2.2.1; have := hacc.hbudV.2.2.2.1
      show (RealAJ8.axReqsJ8 δ b Pb.toPubJ8 tr.toJ8).length ≤ r.A + r.inc + r.AW
      omega
    · refine le_trans (le_of_eq (congrArg List.length rAX.2.symm)) ?_
      show (RealAJ8.axProvsJ8 δ b Pb.toPubJ8 tr.toJ8).length ≤ r.A
      rw [RealAJ8.axProvsJ8_length]; exact hacc.hbudV.2.2.1
  have hcountA : (AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
      (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA) ++ wr).length < p :=
    hcountA_ofZ'' δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8 hacc.hlenA
  -- the atom walk's PRESENT premises
  have hzA : Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 2) (chalsAJ8Z δ χ 3) ≠ 0 := by
    rw [chalsAJ8Z_of_ne δ χ (by omega) (by omega), chalsAJ8Z_of_ne δ χ (by omega) (by omega)]
    exact ListJ8C.atom_hz_of_outsideC _ hoC
  have hseedsV := NCVJ9A.hseedsV_gen δ b _ Pb.toPubJ8 χ M' tr.toJ8 hoC
    (AcceptsJ8ZS.rowsAJ8_eq_atomTZ δ b Pb.toPubJ8 χ M' tr.toJ8) hΛ
  have hvx := AtomFpxJ8.afx_out_of_outsideX _ hoX
    (by
      show (AtomFpxJ8.vxReqsJ8 δ b Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV tr.toJ8).length ≤ r.AW
      rw [AtomFpxJ8.vxReqsJ8_length]; exact hacc.hbudV.2.2.2.1)
    (by
      show (AtomFpxJ8.vxProvsJ8 δ b Pb.nodesA Pb.orbitA tr.toJ8).length ≤ 2 * r.A
      exact (AtomFpxJ8.vxProvsJ8_length δ b Pb.nodesA Pb.orbitA tr.toJ8).trans
        (by have := hacc.hbudV.2.2.1; omega))
  have hvx' : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (vxReqsAtZ δ b Pb.toPubJ8 χ M' tr.toJ8) (liftWts (vxProvsAtZ δ b Pb.toPubJ8 χ M' tr.toJ8)) := by
    rw [← vxReqsJ8_viewZG9 δ b Pb.toPubJ8 χ M' tr.toJ8, ← vxProvsJ8_viewZG9 δ b Pb.toPubJ8 χ M' tr.toJ8]
    exact hvx
  have hXV := NCVJ9A.hXV_of_ioNC δ b Pb.toPubJ8 χ M' tr.toJ8 hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA
    hV.1 hV.2.1 hV.2.2.1 hV.2.2.2.1 hV.2.2.2.2.2.2
    (by show Quad.mk _ (M.pubsA 2) (M.pubsA 3) = Quad.mk _ (M.pubsV 0) (M.pubsV 1)
        rw [hacc.hfxA.1, hacc.hfxA.2]) hvx'
  have hHXV := NCJ9A.hHXV_ofNC δ b Pb.toPubJ8 χ M' tr.toJ8 hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA hbalW rfl
    houtA hcountA
  have houtV : (chalsAJ8Z δ χ 0, chalsAJ8Z δ χ 1) ∉ WalkVCL.walkEvent (algebraMap (ZMod p) K δ)
      (walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
        (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
          (qV δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsV))) := by
    have h1 : (EncZYJ8.chalsVJ8 δ χ 0, EncZYJ8.chalsVJ8 δ χ 1) ∉ WalkVCL.walkEvent (algebraMap (ZMod p) K δ)
        ((CensusAL.XA9P δ b (g := g + r.N + r.AX) R0 L0 Pb c skel hs hL hP hnM hreg9P hN).C.wdC tr.toTrJ9A χ) :=
      ListJ8C.houtV_of_outsideC (RR49AL.XAL δ b
        (CensusAL.XA9P δ b (g := g + r.N + r.AX) R0 L0 Pb c skel hs hL hP hnM hreg9P hN) Pb c g).C hoC
    have h2 : (EncZYJ8.chalsVJ8 δ χ 0, EncZYJ8.chalsVJ8 δ χ 1) ∉ WalkVCL.walkEvent (algebraMap (ZMod p) K δ)
        ((LinkJ9G.RR49 δ b (g := g + r.N + r.AX) R0 Pb.toPubJ8 c skel hs hL hP hnM
          (CensusAL.hreg9_of hreg9P)).wdC tr.toJ8 χ) := h1
    rw [(chalsAJ8Z_01 δ χ).1, (chalsAJ8Z_01 δ χ).2, ← wdV_view δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsV]
    exact h2
  exact soundAL_core δ b hRg hacc
    (RR49A.XA δ b (g := g + r.N + r.AX) R0 L0 Pb.toPubJ9A c skel hs hL hP hnM (CensusAL.hreg9_of hreg9P)
      Pb.axOn Pb.spOn)
    (CensusAL.withCensusP δ b (LinkJ9G.RR49 δ b (g := g + r.N + r.AX) R0 Pb.toPubJ8 c skel hs hL hP hnM
      (CensusAL.hreg9_of hreg9P)) Pb.toPubJ8 c (censusP Pb) hP hnM hreg9P)
    L0 skel hs hL hN hout hpG hqM hk hmax hA3 hcap ⟨rfl, rfl⟩ rfl wr hbalW houtA hcountA
    (fun hRA hsA hidxA hrn hB hwRA hserv => ShareJ9A.awShare_prov (fun _ =>
      HokJ9AG9.walkShareV9 hpG Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
        (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA) hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA
        hRA hsA hidxA hrn hB hwRA hacc.hnpA hzA hserv Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
        (qV δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsV) hV.1 hV.2.1 hV.2.2.1 hV.2.2.2.1 ⟨rfl, rfl⟩
        hV.2.2.2.2.1 hV.2.2.2.2.2.1 hV.2.2.2.2.2.2 hseedsV hXV hHXV houtV))

end Wrap

section Final
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ9AL} {g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Classical in
/-- **The J-9 AL bound at a PRESENT atom walk** (`1 ≤ krootsV`). -/
theorem probJ9AL_present [CharP K p] [CharP 𝕂′ p] (Pb : PubJ9AL p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r.toRowsJ8 EncInjJ8.cornerC) (hAX : r.AX ≤ 2 ^ 31) (hSP : r.SP ≤ 2 ^ 31) (hAL : r.AL ≤ 2 ^ 31)
    (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9P : (censusG Pb.toPubJ8 c ++ censusP Pb).length + 6 ≤ 2 ^ 31)
    (hpos : 1 ≤ Pb.krootsV) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ9AL' p K δ, AcceptsJ9AL δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 := by
  have hΛ : fuelChip ≤ (RR49A.rowsB r.toRowsJ9A).Λ := by
    show fuelChip ≤ r.Λ
    rw [hr.2.2.2.1]; exact le_refl _
  exact RR49AL.probJ9AL_lt_155 δ b
    (CensusAL.XA9P δ b (g := g + r.N + r.AX)
      (R0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (P := 2 ^ 66))
      (L0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ)) Pb c [] (by simp)
      (LinkJ8NV.layLe_ofG (r := RR49A.rowsB r.toRowsJ9A) Pb.toPubJ8 hLC hLM hLW hLA hLV) rfl hnM hreg9P hLC)
    Pb c g Q hQ _ _
    (fun χ hacc hout => by
      obtain ⟨M, hM⟩ := hacc
      exact soundAL_present δ b hRg hM hpos _ _ [] (by simp) _ rfl hnM hreg9P hLC hout hpG hqM hk hmax
        (hA3A (r := r.toRowsJ9A) hr hpG) hΛ (hcapAL hr hAX hAL hg hpG))
    hcK hr hAX hSP hAL (le_refl _) hg

open Classical in
/-- **The J-9 AL bound at an ABSENT atom walk** (`krootsV = 0`). -/
theorem probJ9AL_absent [CharP K p] [CharP 𝕂′ p] (Pb : PubJ9AL p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r.toRowsJ8 EncInjJ8.cornerC) (hAX : r.AX ≤ 2 ^ 31) (hSP : r.SP ≤ 2 ^ 31) (hAL : r.AL ≤ 2 ^ 31)
    (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9P : (censusG Pb.toPubJ8 c ++ censusP Pb).length + 6 ≤ 2 ^ 31)
    (h0 : Pb.krootsV = 0) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ9AL' p K δ, AcceptsJ9AL δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  RR49AL.probJ9AL_lt_155 δ b
    (CensusAL.XA9ZP δ b (g := g + r.N + r.AX)
      (R0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (P := 2 ^ 66))
      (L0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ)) Pb c [] (by simp)
      (LinkJ8NV.layLe_ofG (r := RR49A.rowsB r.toRowsJ9A) Pb.toPubJ8 hLC hLM hLW hLA hLV) rfl hnM hreg9P hLC)
    Pb c g Q hQ _ _
    (fun χ hacc hout => by
      obtain ⟨M, hM⟩ := hacc
      exact soundAL_absent δ b hRg hM h0 _ _ [] (by simp) _ rfl hnM hreg9P hLC hout hpG hqM hk hmax
        (hA3A (r := r.toRowsJ9A) hr hpG) (hcapAL hr hAX hAL hg hpG))
    hcK hr hAX hSP hAL (le_refl _) hg

open Classical in
/-- **THE J-9 AL BOUND**: `Pr_χ[(∃ M, AcceptsJ9AL … (Q χ) r g) ∧ ¬ HoldsN c] < 2^-155`, the atom walk present
or absent (rows `rowsBL r`, id parameter `gL r g`, at the J-9 AL census corner). -/
theorem probJ9AL_final [CharP K p] [CharP 𝕂′ p] (Pb : PubJ9AL p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r.toRowsJ8 EncInjJ8.cornerC) (hAX : r.AX ≤ 2 ^ 31) (hSP : r.SP ≤ 2 ^ 31) (hAL : r.AL ≤ 2 ^ 31)
    (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9P : (censusG Pb.toPubJ8 c ++ censusP Pb).length + 6 ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ9AL' p K δ, AcceptsJ9AL δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 := by
  rcases Nat.eq_zero_or_pos Pb.krootsV with h0 | hpos
  · exact probJ9AL_absent δ b Pb hRg c Q hQ hpG hcK hr hAX hSP hAL hqM hk hmax hg hLC hLM hLW hLA hLV hnM hreg9P h0
  · exact probJ9AL_present δ b Pb hRg c Q hQ hpG hcK hr hAX hSP hAL hqM hk hmax hg hLC hLM hLW hLA hLV hnM hreg9P
      hpos

end Final

section Clean
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ9AL} {g : ℕ}

open Classical in
/-- **`probJ9AL_final_clean`: J-9 AL soundness, with the characteristic binders derived.**
For a faithful jet registry `Rg`, a public claim `c` that does not hold (`¬ HoldsN c`), any staged trace family `Q`
(`StJ9AL`), the Goldilocks prime `p`, a challenge field with `|K| = cK`, and every table (including the ALU table,
`AL`) of at most `2^31` rows within the public sizes `Pb`, the fraction of verifier coins `χ` for which some
message `M` makes `AcceptsJ9AL` accept is `< 1 / 2^155`.  The instances `[Fact (ringChar (ZMod p)).Prime]` and
`[Algebra (ZMod (ringChar (ZMod p))) K]` are built from `ringChar (ZMod p) = p`, so they are not hypotheses. -/
theorem probJ9AL_final_clean [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r.toRowsJ8 EncInjJ8.cornerC) (hAX : r.AX ≤ 2 ^ 31) (hSP : r.SP ≤ 2 ^ 31) (hAL : r.AL ≤ 2 ^ 31)
    (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9P : (censusG Pb.toPubJ8 c ++ censusP Pb).length + 6 ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ9AL' p K δ, AcceptsJ9AL δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  haveI : Fact (ringChar (ZMod p)).Prime := ⟨by rw [hrc]; exact Fact.out⟩
  haveI : Algebra (ZMod (ringChar (ZMod p))) K := @Eq.rec ℕ p (fun q _ => Algebra (ZMod q) K) ‹Algebra (ZMod p) K› _ hrc.symm
  exact probJ9AL_final δ b Pb hRg c Q hQ hpG hcK hr hAX hSP hAL hqM hk hmax hg hLC hLM hLW hLA hLV hnM hreg9P

end Clean

end

end Nock.NockVMROM.Thm54.VclL.Handle.ProbJ9AL
