/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/SoundJ9A.lean

* `fpx_outA`, `wchain_outA`: #1.5 / #1.4 at the J-9 A list `sum40A`.
  * `claimX_factsA`: the census facts of the claim extension (`LinkJ9G.claimX_factsG` at the twin, `claimRow0_eqA`).
  The cell / J / registry /
    atom-table / reader block is `LinkJ9G.linkXUG9_of_R5` (l. 371-481) and `hsoundJ9XUG` (l. 546-668) over the
    `AcceptsJ9A` fields; the compute items are `CompWalkJ9A` / `IOJ9A` / `HbalJ9A`; the shares are `ShareJ9A`'s. -/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.CompWalkJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.NCJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ServedXJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.DenJ9A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.SoundJ9A

noncomputable section

section Out
open Nock Nock.Reified Nock.Framework Nock.Edit Module Polynomial
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J9A
open Nock.NockVMROM.Thm54.VclL.Events
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {δ : K} [Fact (¬ IsSquare δ)] {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8}

/-- #1.5 (the fingerprint export) outside the J-9 A list. -/
theorem fpx_outA (L : Data40J8 (q := q) δ Tr St r) (C : CW9 (K := K) Tr St r) {tr : Tr} {ψ : Coins frameVSQ K}
    (h : ∀ s ∈ sum40A L C, ¬ s.mem tr ψ) (h1 : (L.fxReqs tr ψ).length ≤ r.W)
    (h2 : (L.fxProvs tr ψ).length ≤ 2 * r.D) :
    (Quad.mk δ (ψ v4) (ψ v6), Quad.mk δ (ψ v5) (ψ v7)) ∉ IOFailureEventW (L.fxReqs tr ψ) (L.fxProvs tr ψ) := by
  have := h (fpxL L) (by simp [sum40A])
  rw [fpxL, mem_ioSummandF, evIO_of_guard h1 h2] at this
  exact this

/-- #1.4 (the J-8 walk chain) outside the J-9 A list. -/
theorem wchain_outA (L : Data40J8 (q := q) δ Tr St r) (C : CW9 (K := K) Tr St r) {tr : Tr} {ψ : Coins frameVSQ K}
    (h : ∀ s ∈ sum40A L C, ¬ s.mem tr ψ) : (ψ v0, ψ v1) ∉ WalkVCL.walkEvent δ (L.wdW tr ψ) := by
  have := h (wchainL L) (by simp [sum40A])
  erw [wchainL, mem_specSummandF] at this; exact this

end Out

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

section ClaimXA
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **The claim extension's census facts at the twin** (`LinkJ9G.claimX_factsG` with `claimRow0_eqA`). -/
theorem claimX_factsA {Pb : PubJ9A p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9A' p K δ} {tr : TrJ9A (ZMod p)} {r : RowsJ9A} {g : ℕ} (hp : 20 < p)
    (hacc : AcceptsJ9A δ b Pb Rg c χ M tr r g) :
    (∀ k, isBigN p (claimNoun c k) = true → claimNoun c k ∈ claimX (K := K) b Pb.toPubJ8 c tr.toJ8) ∧
    (∀ k, isBigN p (claimNoun c k) = true → ∀ m, extB p (rAT (K := K) b Pb.toPubJ8 tr.toJ8) (M.m k).1 = some m →
      m ∈ claimX (K := K) b Pb.toPubJ8 c tr.toJ8) ∧
    (∀ x ∈ claimX (K := K) b Pb.toPubJ8 c tr.toJ8, (∃ k, isBigN p (claimNoun c k) = true ∧ x = claimNoun c k) ∨
      ∃ j, extB p (rAT (K := K) b Pb.toPubJ8 tr.toJ8) j = some x) := by
  refine ⟨fun k hkb => List.mem_append_left _ (List.mem_map.mpr
    ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkb⟩, rfl⟩), fun k hkb m hm => ?_, fun x hx => ?_⟩
  · have hI := hacc.hclI k (Or.inr hkb)
    have hr := claimRow0_eqA δ b Pb Rg c χ M tr hp hacc k
    rw [claimHJ9_snd (Or.inr hkb)] at hr
    have hv : (claimRow0 Pb.toPubJ8 tr.toJ8 k).val = (M.m k).1 := by
      rw [hr]; show (((M.m k).1 : ℕ) : ZMod p).val = _; rw [ZMod.val_natCast, Nat.mod_eq_of_lt hI]
    refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkb⟩, ?_⟩)
    show extB p (rAT (K := K) b Pb.toPubJ8 tr.toJ8) (claimRow0 Pb.toPubJ8 tr.toJ8 k).val = some m
    rw [hv]; exact hm
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      exact Or.inl ⟨k, (List.mem_filter.mp hk).2, rfl⟩
    · obtain ⟨k, -, hk⟩ := List.mem_filterMap.mp hx
      exact Or.inr ⟨_, hk⟩

end ClaimXA

section Core
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (xS xF xE)

/-- **S9 core** (see the module header). -/
theorem soundA_core [CharP K p] [CharP 𝕂′ p] {Pb : PubJ9A p} {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ9A' p K δ} {tr : TrJ9A (ZMod p)} {r : RowsJ9A} {g P : ℕ}
    (hacc : AcceptsJ9A δ b Pb Rg c χ M tr r g)
    (R8 : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 (RR49A.rowsB r) P
      (g + r.N + r.AX))
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 (RR49A.rowsB r))
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (LinkJ8Q1.layPb Pb.toPubJ8 skel hs) (RR49A.rowsB r))
    (hN : Pb.n ≤ (RR49A.rowsB r).N)
    (hout : ∀ s ∈ allJ8C (withLiftCA (RR49A.realIOA δ b R8 Pb.axOn Pb.spOn Pb)
      (RR49A.LL4A δ b L0 Pb skel hs hL Pb.axOn Pb.spOn) (cw9A (K := K) Pb hN)), ¬ s.mem tr χ)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ (RR49A.rowsB r).maxlen)
    (hk : 2 * fuelChip ≤ (RR49A.rowsB r).leaves) (hmax : Pb.nA + 2 ≤ (RR49A.rowsB r).maxlen)
    (hA3 : 3 + 2 * (RR49A.rowsB r).A < p)
    (hcap : 3 * (RR49A.rowsB r).N + (RR49A.rowsB r).W + (RR49A.rowsB r).rd < p ∧
      2 * (RR49A.rowsB r).N < p ∧ (RR49A.rowsB r).N + 2 * (RR49A.rowsB r).J + (g + r.N + r.AX) < p)

    (hRV : R8.D.valReqs tr.toJ8 χ = valReqsJ9 δ b Pb.toPubJ8 c tr.toJ8 χ ∧
      R8.D.valProvs tr.toJ8 χ = valProvsJ8 δ b Pb.toPubJ8 tr.toJ8 χ)
    (hRAV : R8.D.avReqs tr.toJ8 χ = RealAJ8.avReqsJ8 δ b Pb.toPubJ8 tr.toJ8 ∧
      R8.D.avProvs tr.toJ8 χ = RealAJ8.avProvsJ8 δ b Pb.toPubJ8 tr.toJ8)
    (hRprs : R8.D.prs tr.toJ8 = EncInjJ8.censusPairs (EncInjJ8.censusList2
      (TraceJ8.rowsMJ8 Pb.nodesC Pb.orbitC tr.toJ8) (extT8 b Pb.toPubJ8 tr.toJ8) ++
        (censusG Pb.toPubJ8 c ++ claimX b Pb.toPubJ8 c tr.toJ8)))
    -- the atom-walk handle reads and the atom-walk share
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
  have O := outJ9A_of_outside _ _ _ b hout
  have h40 := outside40CA _ _ _ hout
  have hB := hacc.hbud
  have hz2 : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) := by
    rw [(chalsMJ8_z (δ := δ) χ).1, (chalsMJ8_z (δ := δ) χ).2]
  have hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0 := by
    rw [hz2]; exact O.z_ne
  -- (a) the cell validity table (#2) at the J-9 claim records
  have rV := rdV9_viewA δ b Pb Rg c χ M tr hp20 hacc
  have lV := RealJ9.valJ9_length δ b Pb.toPubJ8 c tr.toJ8 χ
  have eV1 : (withLiftCA (RR49A.realIOA δ b R8 Pb.axOn Pb.spOn Pb)
      (RR49A.LL4A δ b L0 Pb skel hs hL Pb.axOn Pb.spOn) (cw9A (K := K) Pb hN)).D.valReqs tr χ =
      valReqsJ9 δ b Pb.toPubJ8 c tr.toJ8 χ := hRV.1
  have eV2 : (withLiftCA (RR49A.realIOA δ b R8 Pb.axOn Pb.spOn Pb)
      (RR49A.LL4A δ b L0 Pb skel hs hL Pb.axOn Pb.spOn) (cw9A (K := K) Pb hN)).D.valProvs tr χ =
      valProvsJ8 δ b Pb.toPubJ8 tr.toJ8 χ := hRV.2
  have houtC := O.valid (by
      rw [eV1]; have := hacc.hbudV.1; have := hB.x2; have := lV.1
      show _ ≤ 3 + 2 * r.D + (g + r.N + r.AX); omega)
    (by rw [eV2]; have := hacc.hbudV.2.1; have := hB.x2; have := lV.2; show _ ≤ r.D + r.mb; omega)
  rw [eV1, eV2, rV.1, rV.2] at houtC
  have hcountC := hcountC9A δ b Pb c χ M tr hacc.hlenC
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
    _ hacc.hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
    _ hacc.hbindC
  have hsumC : (M'.reqsC.map fun r => (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
      Quad.mk _ (M'.pubsC 0) (M'.pubsC 1) + (M'.xsC.map fun x => x.2 * (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x.1)⁻¹).sum := by
    show _ = _ + ((mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _).map _).sum
    rw [mbXs_sum δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ hacc.hsatA hacc.hbindA hacc.hinjA
      hacc.hadjA _ _ (chalsAJ8Z_ok δ χ)]
    exact hacc.hsumC'
  have hxneC : ∀ x ∈ M'.xsC, FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x.1 ≠ 0 :=
    mbXs_den δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ hacc.hsatA _ _ (chalsAJ8Z_ok δ χ)
  have hxC : ∀ x ∈ M'.xsC, ∃ k ∈ M'.vp,
      x.1 = ClaimVS.claimVec δ k.1 (k.2.2.2 : ZMod p) (k.2.1 : ZMod p) (k.2.2.1 : ZMod p) :=
    mbXs_claimVec δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _
  have hvp0 : ∀ k ∈ M'.vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar (ZMod p) := fun k hk => by
    obtain ⟨h1, h2, h3⟩ := mbVp_small δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ k hk
    exact ⟨h1, h2, by rw [hrc]; exact h3⟩
  have htabC := TwoProviderQ.cellTable_accepts2 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC _ hF' hq'
    hzC hsatC0 hbindC0 hacc.hinjC hacc.hadjC hacc.hnpC _ _ (chalsOK_J8 (δ := δ) χ) _ _ hsumC houtC
    hxneC hcountC _ hxC hvp0
  rw [hz2] at htabC
  have hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (encJ8 δ χ) :=
    inlineAtoms_encZY (by rw [hrc]; exact hpG) _ _
  -- (b) the atom table's reader `rAT` (LinkJ9G l. 373-387)
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
  -- (c) #3: the atom table is served
  have rAV := RealAJ8.rdAV_view δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA
  have hserved := ServedAJ8.hservedA_of_outside _ hout
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
    exact O.atom_hz
  have hvp := AtomLeavesUJ8.hvp_of_mbU χ hq hpG hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA hacc.hnpA hy
    hserved hRA hsU hidxA hBA (fun k => hwRA k) hTout
  have hext := LinkQ2J8.hext_of_rows (q := p) hBA hwout hmax
  -- (e) the census over `censusG ++ claimX`
  obtain ⟨hXbig, hXext, hXsrc⟩ := claimX_factsA δ b hp20 hacc
  set X := claimX (K := K) b Pb.toPubJ8 c tr.toJ8 with hX
  have hprsX : ∀ pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2
      ((cellT δ b Pb.toPubJ8 χ M' tr.toJ8).map (·.b0)) (extB p rA) ++ (censusG Pb.toPubJ8 c ++ X)),
      pr ∈ (withLiftCA (RR49A.realIOA δ b R8 Pb.axOn Pb.spOn Pb)
        (RR49A.LL4A δ b L0 Pb skel hs hL Pb.axOn Pb.spOn) (cw9A (K := K) Pb hN)).D.prs tr := by
    intro pr hpr
    show pr ∈ R8.D.prs tr.toJ8
    rw [hRprs, rowsMJ8_eq_cellT δ b Pb.toPubJ8 χ M' tr.toJ8]
    exact hpr
  have hXatom : ∀ x ∈ X, ∃ v, x = .atom v ∧ lenL v ≤ (RR49A.rowsB r).maxlen := by
    intro x hx
    rcases hXsrc x hx with ⟨k, hkb, rfl⟩ | ⟨j, hj⟩
    · have h := hacc.hcen' _ (List.mem_append_right _
        (List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkb⟩, rfl⟩))
      cases hn : claimNoun c k with
      | atom v =>
        rw [hn] at h
        exact ⟨v, rfl, (h.2 v (by simp [Noun.leafList])).trans hmax⟩
      | cell a b' => rw [hn] at hkb; simp [isBigN] at hkb
    · exact hext j x hj
  have hcenG : ∀ x ∈ censusG Pb.toPubJ8 c ++ X,
      x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ (RR49A.rowsB r).maxlen := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have h := hacc.hcen' x (List.mem_append_left _ hx)
      exact ⟨h.1, fun v hv => (h.2 v hv).trans hmax⟩
    · obtain ⟨v, rfl, hv⟩ := hXatom x hx
      refine ⟨by simp [Noun.leaves, fuelChip], fun w hw => ?_⟩
      simp only [Noun.leafList, List.mem_singleton] at hw
      exact hw ▸ hv
  have hG := LinkQ2J8.hinjE_of_outside _ hout hq' O.z_ne hE htabC hvp hext hqM hk
    (G := censusG Pb.toPubJ8 c ++ X) hcenG hprsX
  have hinjE : ∀ id ∈ Pb.regs, ∀ d ∈ decodedNouns2 ((cellT δ b Pb.toPubJ8 χ M' tr.toJ8).map (·.b0)) (extB p rA),
      encJ8 δ χ (Nock.Jet.Autogen.compile p (Pb.Rt id)) = encJ8 δ χ d → Nock.Jet.Autogen.compile p (Pb.Rt id) = d :=
    fun id hid d hd he => hG _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hid))) d hd he
  have hM1 : 1 ≤ (RR49A.rowsB r).maxlen := (Nock.Atoms.one_le_lenL 0).trans (hqM 0 (by rw [hrc]; omega))
  have hinjX : ∀ a ∈ X, ∀ b' ∈ X, encJ8 δ χ a = encJ8 δ χ b' → a = b' := by
    refine EncInjJ8.encZY_inj_of_sep O.z_ne (prs := (withLiftCA (RR49A.realIOA δ b R8 Pb.axOn Pb.spOn Pb)
        (RR49A.LL4A δ b L0 Pb skel hs hL Pb.axOn Pb.spOn) (cw9A (K := K) Pb hN)).D.prs tr)
      (k := (RR49A.rowsB r).leaves) (M := (RR49A.rowsB r).maxlen) (Λ := fuelChip)
      (fun pr hpr => hprsX pr (censusPairs_append_mem_right (censusPairs_append_mem_right hpr)))
      (fun _pr hpr hlen hne hkk hm1 hm2 => ListJ8C.biv_out_of_outsideC _ hout hpr hlen hne hkk hm1 hm2)
      (fun n hn => ?_) hk hM1 (fun n hn => ?_)
    · obtain ⟨v, rfl, -⟩ := hXatom n hn
      simp [Noun.leaves, fuelChip]
    · obtain ⟨v, rfl, hv⟩ := hXatom n hn
      intro x hx
      simp only [Noun.leafList, List.mem_singleton] at hx
      exact hx ▸ hv
  have hvpr : ∀ k ∈ M'.vp, k.2.1 < ringChar (ZMod p) ∧ k.2.2.1 < ringChar (ZMod p) ∧ k.2.2.2 < ringChar (ZMod p) := by
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
      (fun _ _ => List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkc⟩, rfl⟩)))
      (fun _ _ => by
        have h62 : (rkC (claimNoun c k)).2 < 2 ^ 62 := Nat.mod_lt _ (by positivity)
        rw [hrc]
        exact ⟨hacc.hclR k hkc, by omega, hacc.hclI k (Or.inl hkc)⟩) 0 (List.mem_singleton_self 0)
    rcases hprov with hc | hv
    · exact claimK_genuine_cell hq' (fun a b' => rfl) hE htabC hvp
        (fun d hd he => hG _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem
          (List.mem_filter.mpr ⟨List.mem_finRange k, hkc⟩)))) d hd he) hc
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
        show _ ∈ (claimRecsJ8 δ χ c M.m ++ claimBigRecs δ χ c M.m) ++ pinRecsJ8 δ Pb.toPubJ8 χ
        simp only [Nat.cast_zero]
        exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkb⟩, rfl⟩)))
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
  have XC := xctxJ9A δ b Pb c χ M tr hp20 hacc.hsatX hacc.hinjX hacc.hadjX
  have hden : ∀ k : Fin 3, denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
      (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M'.pubsC) rA
      (hdV (envA δ b Pb c χ M tr 0) (![xS, xF, xE] k)) = some (claimNoun c k) := by
    intro k
    haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
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
  -- (i) the compute IO events (`ioA`), the compute walk (`walkA`), `hbal` (`hbalA`)
  obtain ⟨hioX, hioS, hioC⟩ := IOJ9A.ioA δ b (RR49A.realIOA δ b R8 Pb.axOn Pb.spOn Pb)
    (RR49A.LL4A δ b L0 Pb skel hs hL Pb.axOn Pb.spOn) (cw9A (K := K) Pb hN)
    (RR49A.rdX_A δ b R8 Pb.axOn Pb.spOn Pb tr χ) (RR49A.rdS_A δ b R8 Pb.axOn Pb.spOn Pb tr χ)
    (RR49A.rdP_A δ b (LinkJ8R4.LL4 δ b L0 Pb.toPubJ8 skel hs hL) Pb.axOn Pb.spOn Pb tr χ) hout hacc hp20 hcap
  obtain ⟨hα9, hw9⟩ := CompWalkJ9A.walkA δ b (c := c) (M := M) (RR49A.realIOA δ b R8 Pb.axOn Pb.spOn Pb)
    (RR49A.LL4A δ b L0 Pb skel hs hL Pb.axOn Pb.spOn) hN hout
  have hbal := HbalJ9A.hbalA δ b hacc (by rw [hrc]; exact hp64)
  -- (j) the J-8 walk: #1.4, #1.5 at `LL4A`, `hXW`, `hHXW`
  have hfx := fpx_outA _ (cw9A (K := K) Pb hN) h40
    (by show (RealVJ8.fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr.toJ8).length ≤ (RR49A.rowsB r).W
        rw [RealVJ8.fxReqsJ8, walkXInternal_length]; exact hL.W)
    (by show (RealVJ8.fxProvsJ8 δ b Pb.nodesC Pb.orbitC tr.toJ8).length ≤ 2 * (RR49A.rowsB r).D
        rw [RealVJ8.fxProvsJ8, liftWts_length]
        exact (cXRec_length δ b _ _ _ _ _).trans (by have := hB.x2; show _ ≤ 2 * r.D; omega))
  have hXW := NCJ9A.hXW_of_ioNC δ b Pb.toPubJ8 χ M' tr.toJ8 hacc.hsatC hacc.hbindC hacc.hinjC hacc.hadjC
    hacc.hsatW hacc.hbindW hacc.hinjW hacc.hadjW hacc.hkpW hp64
    (by show Quad.mk _ (M.pubsC 2) (M.pubsC 3) = Quad.mk _ (M.pubsW 0) (M.pubsW 1)
        rw [hacc.hfxC.1, hacc.hfxC.2]) hfx
  have hW := wchain_outA _ (cw9A (K := K) Pb hN) h40
  rw [show (RR49A.LL4A δ b L0 Pb skel hs hL Pb.axOn Pb.spOn).wdW tr (toVSQ χ) = _ from
    LinkJ8Q1.rdWW_realize40 δ b Pb.toPubJ8 skel hs L0 hL χ M' tr.toJ8, ← (coinW_J8 δ χ).1, ← (coinW_J8 δ χ).2] at hW
  have hne : ∀ bl, ∀ x ∈ CompReqsX9.compReqsX9 (K := K) Pb.hn Pb.nodes Pb.orbit (chalVJ8 b χ)
      (pubVJ9 δ b c M.m M.ρ M.ρS χ) (qX9 δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) bl,
      compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x) ≠ 0 := by
    intro bl x hx
    have hm := List.mem_map_of_mem (f := liftRec (L := 𝕂′)) (List.mem_append_left (extAC δ b Pb χ M tr bl) hx)
    cases bl with
    | x => exact TeleC.den_ne_of_out _ _ _ _ (hioX .x (by decide)) _ hm
    | p => exact TeleC.den_ne_of_out _ _ _ _ (hioX .p (by decide)) _ hm
    | s => exact TeleC.den_ne_of_out _ _ _ _ hioS _ hm
  have hHXW := ServedXJ9A.hHXW9 (HoldsX9.bctx9_of_xctx XC) hbal hne (hioX .x (by decide)) (hioC .x) (by omega)
    Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC) hacc.hsatC
    Pb.kroots Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW)
    Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ) rfl rfl
  have hEinj := EncInjJ8.encInj2_of_outside _
    (outside_sumJ8_D _ hout .bivariateCensus (by decide) (by decide) (by decide)) hq' O.z_ne hE
    htabC hvp hext hqM hk (fun pr hpr => hprsX pr (censusPairs_append_mem hpr))
  -- (k) THE call
  exact HokJ9AG9.acceptsJ9A_holdsN_finalLGG (δ := δ) (b := b) (χ := χ)
    (pv := pubVJ9 δ b c M.m M.ρ M.ρS χ) (C := XC) (hpG := hpG)
    (provs := provsAC δ b Pb χ M tr) (ext := extAC δ b Pb χ M tr) (hbal := hbal)
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
    (reqsC := M'.reqsC) (xsC := M'.xsC) (hsumC := hsumC) (houtC := houtC) (hxneC := hxneC)
    (hcountC := hcountC) (vp := M'.vp) (hxC := hxC) (hvp0 := hvp0)
    (E := encJ8 δ χ) (hconsE := fun a b' => by rw [hz2]; rfl) (hE := by rw [hz2]; exact hE)
    (rA := rA) (hvp := hvp) (hEinj := hEinj)
    (hkW := hacc.hkW) (hknW := hacc.hknW) (hkpW := hacc.hkpW) (hXW := hXW) (hHXW := hHXW) (houtW := hW)
    (hRg := hRg) (hlay := hacc.hlay) (hsmall := hacc.hsmall) (huniq := hacc.huniq) (hTpl := hacc.hTpl)
    (hnd := hacc.hnd) (hidx := hacc.hidx) (hrk := hacc.hrk) (hlt := hacc.hlt)
    (hpinC := fun id hid => List.mem_append_right _ (List.mem_map.mpr ⟨id, hid, rfl⟩))
    (hinjE := hinjE)
    (hRA := hRA) (hsA := hsU) (hidxA := hidxA) (hrn := hrn) (hB := hBA) (hwRA := hwRA)
    (wreqs := wreqs) (hbalA := hbalW) (houtA := houtA) (hcountA := hcountA) (hnpA := hacc.hnpA) (hzA := hy)
    (hservedA := hserved) (hden2 := hden2) (hTout := hTout)
    (sv := svA Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS (qSP δ b Pb tr (chalsMJ8 δ χ) M.pubsS))
    (nS := nSA Pb.spOn (nS := Pb.nS))
    (hsv0 := ShareJ9A.spShare_ne0 hp32 hacc.hSPk) (hsvn := ShareJ9A.spShare_lt)
    (hnAS := ShareJ9A.spShare_nAS hq hacc.hnAS)
    (pW := pWA Pb.krootsV (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
      (qV δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsV)))
    (pX := if Pb.axOn then AxisChipJ9.axTagProvs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
      (qAX δ b Pb tr (chalsMJ8 δ χ) M.pubsX) else [])
    (pS := pSA Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS (qSP δ b Pb tr (chalsMJ8 δ χ) M.pubsS))
    (h7W := ShareJ9A.awShare_h7) (h7X := ShareJ9A.axShare_h7 hpG hacc.hAXk) (h7S := ShareJ9A.spShare_h7)
    (hS := ShareJ9A.spShare_prov hp32 (by have := hacc.hnAS; omega) hacc.hSPk rA)
    (hsvc := ShareJ9A.axShare_svc hpG hacc.hAXk (fun D Rg' => hWsh hRA hsU hidxA hrn hBA hwRA hserved (svA Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS (qSP δ b Pb tr (chalsMJ8 δ χ) M.pubsS)) D Rg')
      (ShareJ9A.spShare_prov hp32 (by have := hacc.hnAS; omega) hacc.hSPk rA)
      (fun c' hc' => by
        show c' ∈ _ ++ _ ++ _
        exact List.mem_append_left _ (List.mem_append_right _ hc'))
      (fun c' hc' => hc'))
    (eA := if Pb.axOn then AxisChipJ9.axLimbReqs b Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
      (qAX δ b Pb tr (chalsMJ8 δ χ) M.pubsX) else [])
    (hprovX := rfl) (hextX := rfl) (hprovP := rfl) (hprovS := rfl) (hextS := rfl)
    (hseed := CompWalkJ9A.hseedA δ b XC) (hα := hα9) (hw := hw9)
    (hreal := CompWalkJ9A.hrealA δ b XC hacc.hcellF (by omega)) (x := c)
    (hs := hden 0) (hf := hden 1) (he := hden 2)
    (fun D Rg' => hWsh hRA hsU hidxA hrn hBA hwRA hserved (svA Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS (qSP δ b Pb tr (chalsMJ8 δ χ) M.pubsS)) D Rg')

end Core

end

end Nock.NockVMROM.Thm54.VclL.Handle.SoundJ9A

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.SoundJ9A
#print axioms fpx_outA
#print axioms wchain_outA
#print axioms claimX_factsA
#print axioms soundA_core
end Axioms
