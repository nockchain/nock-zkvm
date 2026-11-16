/-
  Nock/NockVMROM/Thm54/VclL/Handle/LinkJ9G.lean

  **Soundness of `AcceptsJ9V` with the atom walk PRESENT, and THE J-9 (B) bound.**
  The atom-walk-present counterpart of `LinkJ9A`, parallel to `LinkJ8NV`: `claimRecsT9_eqG`, `rdV9_viewG`, `RR49 := RealJ9.withJ9 RR4`, `linkXUG9_of_R5`
  (reusing `AcceptsJ8L.LinkJ8XU`), `hsoundJ9XUG` (the big case as in `LinkJ9A`; the compute assembly
  `HokJ9G` at `pubVJ9`), `probJ9_present`, and
  * **`probJ9B_final`**: `Pr_χ[(∃ M, AcceptsJ9V … (Q χ) r g) ∧ ¬ HoldsN c] < 2^-155` at EVERY layout, at
    `LinkJ8A.probJ8V_final`'s binders with `hreg` read as `|censusG Pb c| + 6 ≤ 2^31` (the claim extension joins the
    census; `P = 2^66`);
  * **`probJ9B_final_clean`**: the same without the two derived instance binders (`CleanJ8`'s wrapper).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9ZG
import Nock.NockVMROM.Thm54.VclL.Handle.HokJ9G

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9G
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

noncomputable section

section Val
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (xS xF xE)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (envCJ8)

/-- **The claim serials off row 0** at `pubVJ9`. -/
theorem claimRow0_eqG (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p) (hacc : AcceptsJ9ZG δ b Pb Rg c χ M tr) (k : Fin 3) :
    claimRow0 Pb tr k = (((claimHJ9 p c M.m k).2 : ℕ) : ZMod p) := by
  have XC := xctxJ9 δ b Pb c χ M tr hp hacc.hsatX hacc.hinjX hacc.hadjX
  have hd := row0_hd9 (tr := tr) XC k
  have h2 := congrArg Prod.snd hd
  simp only [hdV] at h2
  have hv := ZMod.val_injective p h2
  unfold claimRow0
  rw [row0_envC9 δ b Pb c χ M tr]
  exact hv

/-- **The readout's J-9 claim records are the verifier's** on an accepted trace. -/
theorem claimRecsT9_eqG (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p)
    (hacc : AcceptsJ9ZG δ b Pb Rg c χ (toMsgJ9Z δ b Pb c χ M tr) tr) :
    claimRecsT9 δ Pb c χ tr = claimRecsJ9 δ χ c M.m := by
  have hs : ∀ k, (isCellN (claimNoun c k) = true ∨ isBigN p (claimNoun c k) = true) →
      claimRow0 Pb tr k = (((M.m k).1 : ℕ) : ZMod p) := fun k hk => by
    rw [claimRow0_eqG δ b Pb Rg c χ _ tr hp hacc k, claimHJ9_snd hk]; rfl
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

/-- **The readout at an accepted trace**: the readout IS `LinkJ8X''.rdV`'s pair at `toMsgJ9Z`. -/
theorem rdV9_viewG (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p)
    (hacc : AcceptsJ9ZG δ b Pb Rg c χ (toMsgJ9Z δ b Pb c χ M tr) tr) :
    valReqsJ9 δ b Pb c tr χ = (toMsgJ9Z δ b Pb c χ M tr).reqsC ++
      cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb c χ M tr).pubsC
        (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb c χ M tr).pubsC
          (qM δ b Pb tr (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb c χ M tr).pubsC)) ∧
    valProvsJ8 δ b Pb tr χ = SVFrame.liftWts (cellVRecords δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
      (toMsgJ9Z δ b Pb c χ M tr).pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb c χ M tr).pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb c χ M tr).pubsC))) ++ (toMsgJ9Z δ b Pb c χ M tr).xsC := by
  have hw : 183 ≤ (cellChip δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.w := by
    rw [cell_w]; norm_num
  refine ⟨?_, ?_⟩
  · show (claimRecsT9 δ Pb c χ tr ++ pinRecsJ8 δ Pb χ) ++ _ = (claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb χ) ++ _
    rw [claimRecsT9_eqG δ b Pb Rg c χ M tr hp hacc, cVInt_chip]
    refine congrArg ((claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb χ) ++ ·) ?_
    exact cVInt_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ (by norm_num) hw fun j hj => congrArg tr.M (Fin.ext rfl)
  · show liftWts _ ++ mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) (fun _ => 0) tr.A =
      liftWts _ ++ mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
    rw [cVRec_chip]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · exact congrArg liftWts
        (cVRec_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ (by norm_num) hw fun j hj => congrArg tr.M (Fin.ext rfl))
    · exact mbXs_congr δ b Pb.nodesA Pb.orbitA _ _ _ _ _ _ (by norm_num)
        (by rw [AtomChipHQ.atomChipHQ_width]; norm_num) (fun j hj => rfl) rfl rfl

/-- **`hcountC` at the J-9 message** (the claim records stay `≤ 3`). -/
theorem hcountC9G (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ)
    (tr : TrJ8 (ZMod p)) (hlen : 3 + Pb.regs.length + 2 * Pb.nC < p) :
    ((toMsgJ9Z δ b Pb c χ M tr).reqsC ++ cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
      (toMsgJ9Z δ b Pb c χ M tr).pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb c χ M tr).pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb c χ M tr).pubsC))).length < p := by
  have h1 := claimRecsJ9_length δ χ c M.m
  have h2 : (cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb c χ M tr).pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb c χ M tr).pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb c χ M tr).pubsC))).length ≤ 2 * Pb.nC := by
    unfold cellVInternal
    refine (AcceptsJ8P.length_flatMap_le _ _ 2 fun i => ?_).trans (by simp)
    rw [List.length_append]
    split_ifs <;> simp
  show ((claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb χ) ++ _).length < p
  rw [List.length_append, List.length_append, pinRecsJ8, List.length_map]
  omega

end Val

section Link
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (xS xF xE)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (envCJ8)

/-- **The J-9 present real data**: `RR4` with the J-9 claim lists (`RealJ9.withJ9`). -/
abbrev RR49 (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (Pb : PubJ8 p) (c : P8PublicClaim) (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg9 : (censusG Pb c).length + 6 ≤ 2 ^ 31) :
    DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g :=
  withJ9 δ b (RR4 δ b (g := g) R0 Pb c skel hs hL hP hnM (hreg_of9 hreg9)) Pb c hP hnM hreg9

/-- **`LinkJ8XU` at the R4 real data from `AcceptsJ8'''` alone**: every field derived — `linkX_of_R4` with
`hsA` derived (`SmallU` at the reader, `smallU_valReader`, from `nA ≤ 2^62`, `hservedA` and the export
consume `ConsumeServedQ` of the `houtA` balance), `hvp` through the `SmallU` twin `hvp_of_mbU`, and no `hok` (derived
downstream at the variant chip). -/
theorem linkXUG9_of_R5 [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg9 : (censusG Pb c).length + 6 ≤ 2 ^ 31)
    (hpG : p = Nock.Atoms.p) (hr : RowsLe r EncInjJ8.cornerC) (hg : g ≤ 2 ^ 31) (hmax : Pb.nA + 2 ≤ r.maxlen)
    (hacc3 : AcceptsJ9V.AcceptsJ9V δ b Pb Rg c χ M tr r g) (hpos : 1 ≤ Pb.krootsV)
    (hout : ∀ s ∈ AtomFpxJ8.allJ8X (AtomFpxJ8.withFpxV δ b
      (withLiftC (RR49 δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg9) (LL4 δ b L0 Pb skel hs hL))
      Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA), ¬ s.mem tr χ)
 :
    LinkJ8XU δ b Pb c χ (toMsgJ9Z δ b Pb c χ M tr) tr (RR49 δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg9)
      (LL4 δ b L0 Pb skel hs hL) (rAT b Pb tr) := by
  have hacc' := hacc3
  have hacc := acceptsJ9ZG_of_V hacc' hpos
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp17 : 17 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hp64 : 64 ≤ p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hp32 : 2 ^ 32 ≤ p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hq : 2 ^ 63 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hcap := RepriceJ8.hcap_corner32 hr hg hpG
  have hB := hacc'.hbud
  have hΛ : fuelChip ≤ r.Λ := by rw [hr.2.2.2.1]; exact le_refl _
  have hoC := AtomFpxJ8.outsideC_of_outsideX _ hout
  set M' := toMsgJ9Z δ b Pb c χ M tr with hM'
  -- L1: the handle balances
  have rX := rdX_realIO δ b (realizeG δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM (LinkJ9A.hreg_of9 hreg9)) Pb c χ M' tr
  have rS := rdS_realIO δ b (realizeG δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM (LinkJ9A.hreg_of9 hreg9)) Pb c χ M' tr
  have rP := rdP_real40 δ b (realize40 δ b L0 (layPb Pb skel hs) hL) Pb c χ M' tr
  have bX := budX_ofZG9 δ b Pb c χ M' tr hacc hp17 hB
  have bP := budP_ofZG9 δ b Pb c χ M' tr hacc hp17 hB
  have bS := budS_ofZG9 δ b Pb c χ M' tr hacc hp17 hB
  have L2 := linkJ8_L2ZG9 δ b Pb skel hs L0 hL c χ M' tr hacc hp17
  have hx := ListJ8C.hout_x_of_outsideC _ b hoC _ _ rX.1 rX.2 bX.1 bX.2
  have hpp := ListJ8C.hout_p_of_outside40C _ _ b hoC _ _ rP.1 rP.2 bP.1 bP.2
  have hss := ListJ8C.hout_s_of_outsideC _ b hoC _ _ rS.1 rS.2 bS.1 bS.2
  have hcnt := hcount_ofZG9 δ b Pb c χ M' tr hacc hp17 hB hcap
  -- the readout
  have rV := rdV9_viewG δ b Pb Rg c χ M tr hp17 hacc
  have lV := RealJ9.valJ9_length δ b Pb c tr χ
  -- the reader at chalsAJ8Z
  have hE := rAT_eq δ b Pb tr (chalsAJ8Z δ χ) M.pubsA
  have hRA : ∀ k : Fin Pb.nA, AtomChipHQ.Reads (AtomServedQ.aEF b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
      (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) k) (rAT b Pb tr k) := by
    rw [← hE]; exact LinkQ2J8.hRA_valReader _
  have hwRA : ∀ j, (rAT (K := K) b Pb tr j).wR ≤ 1 := by
    rw [← hE]; exact LinkQ2J8.hwRA_valReader _ (LinkQ2J8.atom_wR_bool hacc.hsatA)
  have hidxA : ∀ k : Fin Pb.nA, (rAT (K := K) b Pb tr k).idx = k := by
    rw [← hE]; exact ReaderR3bJ8.hidxA_valReader hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA hacc.hnpA
  have hBA : AtomChipHQ.LimbsBounded (rAT (K := K) b Pb tr) := by
    rw [← hE]; exact ReaderR3bJ8.hB_valReader hp32 hacc.hsatA
  have hwout : ∀ k, Pb.nA ≤ k → (rAT (K := K) b Pb tr k).wR = 0 := by
    rw [← hE]; exact LinkQ2J8.wR_valReader_out _
  have hTout : ∀ j, Pb.nA ≤ j → (rAT (K := K) b Pb tr j).wR = 0 → (rAT (K := K) b Pb tr j).aR ≠ 0 := by
    rw [← hE]; exact LinkQ2J8.aR_valReader_out _
  -- hservedA
  have hA3 : 3 + 2 * r.A < p := by
    have := hr.2.2.2.2.1; simp only [EncInjJ8.cornerC, corner31] at this
    rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]; omega
  have rAV := RealAJ8.rdAV_view δ b Pb tr (chalsAJ8Z δ χ) M.pubsA
  have hserved := ServedAJ8.hservedA_of_outside
    (withLiftC (RR49 δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg9) (LL4 δ b L0 Pb skel hs hL)) hoC
    hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA (chalsAJ8Z_ok δ χ) hacc'.hvalA0 rAV
    ⟨(RealAJ8.avReqsJ8_length δ b Pb tr).trans (by have := hacc'.hbudV.2.2.1; omega),
      (RealAJ8.avProvsJ8_length δ b Pb tr).le.trans hacc'.hbudV.2.2.1⟩ hA3
  -- houtA
  have rAX := RealAJ8.rdAX_view δ b Pb tr (chalsAJ8Z δ χ) M.pubsA (chalsAJ8Z δ χ) M.pubsV
  have hac : AtomServedQ.acoins δ (chalsAJ8Z δ χ) = AtomServedQ.acoins δ (ProbJ8.chalsAJ8 δ χ) := by
    simp only [AtomServedQ.acoins, chalsAJ8Z_of_ne δ χ (show (33 : ℕ) ≠ 37 by decide) (by decide),
      chalsAJ8Z_of_ne δ χ (show (34 : ℕ) ≠ 37 by decide) (by decide),
      chalsAJ8Z_of_ne δ χ (show (35 : ℕ) ≠ 37 by decide) (by decide),
      chalsAJ8Z_of_ne δ χ (show (36 : ℕ) ≠ 37 by decide) (by decide)]
  have houtA : ((AtomServedQ.acoins δ (chalsAJ8Z δ χ)).gamma, (AtomServedQ.acoins δ (chalsAJ8Z δ χ)).pole) ∉
      IOFailureEventW ((AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M'.pubsA
          (qA δ b Pb tr (chalsAJ8Z δ χ) M'.pubsA) ++ M'.wreqs).map (BalanceQ.liftRec (K := K) (L := 𝕂′)))
        (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M'.pubsA
          (qA δ b Pb tr (chalsAJ8Z δ χ) M'.pubsA))) := by
    rw [hac]
    refine LinkQ2J8.houtA_of_outside
      (withLiftC (RR49 δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg9) (LL4 δ b L0 Pb skel hs hL)) hoC _ _
      rAX.1 rAX.2 ?_ ?_
    · refine le_trans (le_of_eq (congrArg List.length rAX.1.symm)) ?_
      have := RealAJ8.axReqsJ8_length δ b Pb tr
      have := hacc'.hbudV.2.2.1; have := hacc'.hbudV.2.2.2
      omega
    · refine le_trans (le_of_eq (congrArg List.length rAX.2.symm)) ?_
      rw [RealAJ8.axProvsJ8_length]; exact hacc'.hbudV.2.2.1
  have hcountA := hcountA_ofZ'' δ b Pb c χ M tr hacc'.hlenA
  -- hXW
  have hfx := Lift40J8.fpx_out (LL4 δ b L0 Pb skel hs hL) (ListJ8C.outside40C _ _ hoC)
    (by show (RealVJ8.fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr).length ≤ r.W
        rw [RealVJ8.fxReqsJ8, walkXInternal_length]; exact hL.W)
    (by show (RealVJ8.fxProvsJ8 δ b Pb.nodesC Pb.orbitC tr).length ≤ 2 * r.D
        rw [RealVJ8.fxProvsJ8, liftWts_length]
        exact (cXRec_length δ b _ _ _ _ _).trans (by have := hB.x2; omega))
  have hXW := hXW_of_ioG9 δ b Pb c χ M' tr hacc hp64
    (by show Quad.mk _ (M.pubsC 2) (M.pubsC 3) = Quad.mk _ (M.pubsW 0) (M.pubsW 1)
        rw [hacc'.hfxC.1, hacc'.hfxC.2]) hfx
  -- the census
  have hG : ∀ pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2 ((cellT δ b Pb χ M' tr).map (·.b0))
      (AtomBigJ8.extB p (rAT b Pb tr)) ++ censusG Pb c),
      pr ∈ (RR49 δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg9).D.prs tr := by
    intro pr hpr
    show pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2 (TraceJ8.rowsMJ8 Pb.nodesC Pb.orbitC tr) (extT8 b Pb tr) ++
      (censusG Pb c ++ RealJ9.claimX b Pb c tr))
    rw [rowsMJ8_eq_cellT δ b Pb χ M' tr, ← List.append_assoc]
    exact censusPairs_append_mem hpr
  have hext := LinkQ2J8.hext_of_rows (q := p) hBA hwout hmax
  have hy : Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 2) (chalsAJ8Z δ χ 3) ≠ 0 := by
    rw [chalsAJ8Z_of_ne δ χ (by omega) (by omega), chalsAJ8Z_of_ne δ χ (by omega) (by omega)]
    exact (outJ8_of_outside _ _ b hoC).atom_hz
  -- S1: `SmallU` at the reader from the export consume of the `houtA` balance
  have hcs := AtomServedQ.consumeServedQ_of_balance δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M'.pubsA _
    hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA M'.wreqs hacc.hbalA houtA hcountA
  have hsU : ∀ k : Fin Pb.nA, SmallU (rAT (K := K) b Pb tr k) := by
    rw [← hE]
    exact ReaderR3bJ8.smallU_valReader hq hacc'.hnA62 hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA hserved hcs
  have hvp := AtomLeavesUJ8.hvp_of_mbU χ hq hpG hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA hacc.hnpA hy
    hserved hRA hsU hidxA hBA (fun k => hwRA k) hTout
  exact
    { rdX := rX
      budX := ⟨(congrArg List.length rX.1).le.trans bX.1, (congrArg List.length rX.2).le.trans bX.2⟩
      rdP := rP
      budP := ⟨(congrArg List.length rP.1).le.trans bP.1, (congrArg List.length rP.2).le.trans bP.2⟩
      rdS := rS
      budS := ⟨(congrArg List.length rS.1).le.trans bS.1, (congrArg List.length rS.2).le.trans bS.2⟩
      hcount := hcnt
      rdV := rV
      budV := ⟨lV.1.trans (by have := hacc'.hbudV.1; have := hB.x2; omega),
        lV.2.trans (by have := hacc'.hbudV.2.1; have := hB.x2; omega)⟩
      rdWC := L2.1
      rdWW := L2.2
      hext := hext
      hprs := fun pr hpr => hG pr (censusPairs_append_mem hpr)
      hvp := hvp
      hXW := hXW
      hHXW := hHXW_of_acceptsZG9 δ b Pb c χ M' tr hacc hp64 hx hpp hss (hcnt .x)
      hRA := hRA
      hsA := hsU
      hidxA := hidxA
      hrn := by rw [← hE]; exact LinkQ2J8.hrn_valReader _
      hB := hBA
      hwRA := hwRA
      houtA := houtA
      hservedA := hserved
      hseedsV := AcceptsJ8ZS.hseedsV_of_outsideZ δ b _ Pb χ M' tr hoC
        (AcceptsJ8ZS.rowsAJ8_eq_atomTZ δ b Pb χ M' tr) hΛ
      hHXV := hHXV_ofZG9 δ b Pb c χ M' tr hacc rfl houtA hcountA
      hprsG := hG }

/-! ## 3. THE FINAL theorem -/

end Link

section Sound
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (xS xF xE)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (envCJ8)

/-- **`hsoundJ9XUG`**: an `AcceptsJ9V`-accepted trace at a PRESENT atom walk, outside the J-8 events at the data
`R`, under `LinkJ8XUA` at `toMsgJ9ZA` and the census readout over the claim extension `X` (the claim's big atoms
and the atom-table nouns at their serials), satisfies `HoldsN c`. -/
theorem hsoundJ9XUG [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hmax : Pb.nA + 2 ≤ r.maxlen)
    {r0 : RowsJ8} {g0 : ℕ} (hacc3 : AcceptsJ9V.AcceptsJ9V δ b Pb Rg c χ M tr r0 g0) (hpos : 1 ≤ Pb.krootsV)
    (hout : ∀ s ∈ AtomFpxJ8.allJ8X (AtomFpxJ8.withFpxV δ b (withLiftC R L) Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV
      Pb.nodesA Pb.orbitA), ¬ s.mem tr χ)
    (hbV : Pb.nV ≤ r.AW) (hbA : Pb.nA ≤ r.A)
    (hWV : R.wdC tr χ = walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
      (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV)))
    {rA : ℕ → ARow} (hl : LinkJ8XU δ b Pb c χ (toMsgJ9Z δ b Pb c χ M tr) tr R L rA)
    (X : List Noun)
    (hprsX : ∀ pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2
        ((cellT δ b Pb χ (toMsgJ9Z δ b Pb c χ M tr) tr).map (·.b0)) (extB p rA) ++ (censusG Pb c ++ X)),
      pr ∈ R.D.prs tr)
    (hXbig : ∀ k, isBigN p (claimNoun c k) = true → claimNoun c k ∈ X)
    (hXext : ∀ k, isBigN p (claimNoun c k) = true → ∀ m, extB p rA (M.m k).1 = some m → m ∈ X)
    (hXsrc : ∀ x ∈ X, (∃ k, isBigN p (claimNoun c k) = true ∧ x = claimNoun c k) ∨ ∃ j, extB p rA j = some x) :
    Nock.Jet.HoldsN c := by
  have hacc' := hacc3
  have hacc := acceptsJ9ZG_of_V hacc' hpos
  have hAV : Quad.mk (algebraMap (ZMod p) K δ) ((toMsgJ9Z δ b Pb c χ M tr).pubsA 2)
      ((toMsgJ9Z δ b Pb c χ M tr).pubsA 3) =
      Quad.mk (algebraMap (ZMod p) K δ) ((toMsgJ9Z δ b Pb c χ M tr).pubsV 0) ((toMsgJ9Z δ b Pb c χ M tr).pubsV 1) := by
    show Quad.mk _ (M.pubsA 2) (M.pubsA 3) = Quad.mk _ (M.pubsV 0) (M.pubsV 1)
    rw [hacc'.hfxA.1, hacc'.hfxA.2]
  have hXV := hXV_withFpxVZG9 δ b Pb c χ (toMsgJ9Z δ b Pb c χ M tr) tr hacc (withLiftC R L) hout hbV hbA hAV
  replace hout := AtomFpxJ8.outsideC_of_outsideX _ hout
  set M' := toMsgJ9Z δ b Pb c χ M tr with hM'
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
  -- (a) the cell validity table at the J-9 claim records
  have houtC : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.D.valReqs tr χ) (R.D.valProvs tr χ) := O.valid hl.budV.1 hl.budV.2
  rw [hl.rdV.1, hl.rdV.2] at houtC
  have hcountC := hcountC9G δ b Pb c χ M tr hacc'.hlenC
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
    _ hacc.hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
    _ hacc.hbindC
  have htabC := TwoProviderQ.cellTable_accepts2 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC _ hF' hq'
    hzC hsatC0 hbindC0 hacc.hinjC hacc.hadjC hacc.hnpC _ _ (chalsOK_J8 (δ := δ) χ) _ _ hacc.hsumC houtC
    hacc.hxneC hcountC _ hacc.hxC hacc.hvp0
  rw [hz2] at htabC
  have hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (encJ8 δ χ) :=
    inlineAtoms_encZY (by rw [hrc]; exact hpG) _ _
  have hXatom : ∀ x ∈ X, ∃ v, x = .atom v ∧ lenL v ≤ r.maxlen := by
    intro x hx
    rcases hXsrc x hx with ⟨k, hkb, rfl⟩ | ⟨j, hj⟩
    · have h := hacc'.hcen' _ (List.mem_append_right _
        (List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkb⟩, rfl⟩))
      cases hn : claimNoun c k with
      | atom v =>
        rw [hn] at h
        exact ⟨v, rfl, (h.2 v (by simp [Noun.leafList])).trans hmax⟩
      | cell a b' => rw [hn] at hkb; simp [isBigN] at hkb
    · exact hl.hext j x hj
  have hcenG : ∀ x ∈ censusG Pb c ++ X, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ r.maxlen := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have h := hacc'.hcen' x (List.mem_append_left _ hx)
      exact ⟨h.1, fun v hv => (h.2 v hv).trans hmax⟩
    · obtain ⟨v, rfl, hv⟩ := hXatom x hx
      refine ⟨by simp [Noun.leaves, fuelChip], fun w hw => ?_⟩
      simp only [Noun.leafList, List.mem_singleton] at hw
      exact hw ▸ hv
  have hG := LinkQ2J8.hinjE_of_outside (withLiftC R L) hout hq' O.z_ne hE htabC hl.hvp hl.hext hqM hk
    (G := censusG Pb c ++ X) hcenG hprsX
  have hinjE : ∀ id ∈ Pb.regs, ∀ d ∈ decodedNouns2 ((cellT δ b Pb χ M' tr).map (·.b0)) (extB p rA),
      encJ8 δ χ (Nock.Jet.Autogen.compile p (Pb.Rt id)) = encJ8 δ χ d → Nock.Jet.Autogen.compile p (Pb.Rt id) = d :=
    fun id hid d hd he => hG _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hid))) d hd he
  have hM1 : 1 ≤ r.maxlen := (Nock.Atoms.one_le_lenL 0).trans (hqM 0 (by rw [hrc]; omega))
  have hinjX := hinjX_of_outside δ (withLiftC R L) hout O.z_ne hk hM1 hprsX hXatom
  have hvpr : ∀ k ∈ M'.vp, k.2.1 < ringChar (ZMod p) ∧ k.2.2.1 < ringChar (ZMod p) ∧ k.2.2.2 < ringChar (ZMod p) := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := hacc.hvp0 k hk
    exact ⟨by omega, by omega, h3⟩
  -- (c) the claim's cell records are served (as at J-8)
  have hcell : ∀ k : Fin 3, isCellN (claimNoun c k) = true →
      denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M'.pubsC) rA
        (1, (M.m k).1) = some (claimNoun c k) := by
    intro k hkc
    have hprov := Nock.Jet.PinJ8.regClaims_provided δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M'.pubsC)) hF' hsatC0 hbindC0 hacc.hinjC hacc.hadjC _ _ (chalsOK_J8 (δ := δ) χ)
      _ _ hacc.hsumC houtC hacc.hxneC hcountC _ hacc.hxC hvpr (regs := [0])
      (Ef := fun _ => encJ8 δ χ (claimNoun c k)) (rk := fun _ => rkC (claimNoun c k)) (idx := fun _ => (M.m k).1)
      (fun _ _ => List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkc⟩, rfl⟩)))
      (fun _ _ => by
        have h62 : (rkC (claimNoun c k)).2 < 2 ^ 62 := Nat.mod_lt _ (by positivity)
        rw [hrc]
        exact ⟨hacc'.hclR k hkc, by omega, hacc'.hclI k (Or.inl hkc)⟩) 0 (List.mem_singleton_self 0)
    rcases hprov with hc | hv
    · exact claimK_genuine_cell hq' (fun a b' => rfl) hE htabC hl.hvp
        (fun d hd he => hG _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem
          (List.mem_filter.mpr ⟨List.mem_finRange k, hkc⟩)))) d hd he) hc
    · exfalso
      obtain ⟨h1, h2, -⟩ := hl.hvp _ hv
      exact rkC_ne hkc (Prod.ext h1 h2)
  -- (d) **the big case**: a big claim leaf's record is an `mb` row's export, and the census pins its atom
  have hbig : ∀ k : Fin 3, isBigN p (claimNoun c k) = true →
      denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M'.pubsC) rA
        (2, (M.m k).1) = some (claimNoun c k) := by
    intro k hkb
    have hI := hacc'.hclI k (Or.inr hkb)
    have hprov := Nock.Jet.PinJ8.regClaims_provided δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M'.pubsC)) hF' hsatC0 hbindC0 hacc.hinjC hacc.hadjC _ _ (chalsOK_J8 (δ := δ) χ)
      _ _ hacc.hsumC houtC hacc.hxneC hcountC _ hacc.hxC hvpr (regs := [0])
      (Ef := fun _ => encJ8 δ χ (claimNoun c k)) (rk := fun _ => (0, 0)) (idx := fun _ => (M.m k).1)
      (fun _ _ => by
        show _ ∈ (claimRecsJ8 δ χ c M.m ++ claimBigRecs δ χ c M.m) ++ pinRecsJ8 δ Pb χ
        simp only [Nat.cast_zero]
        exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkb⟩, rfl⟩)))
      (fun _ _ => by rw [hrc]; exact ⟨by omega, by omega, hI⟩) 0 (List.mem_singleton_self 0)
    rcases hprov with ⟨c', hc', heq⟩ | hv
    · -- a cell row never has rank `(0, 0)`
      exfalso
      simp only [Prod.mk.injEq] at heq
      exact cell_key_rank_pos hq' htabC.rows hc' ⟨heq.2.1.symm, heq.2.2.1.symm⟩
    · obtain ⟨-, -, v, hext, hEv⟩ := hl.hvp _ hv
      have hn := hinjX _ (hXbig k hkb) _ (hXext k hkb _ hext) hEv
      show denK _ (extB p rA) (2, (M.m k).1) = _
      simp only [denK]
      rw [hext, ← hn]
  -- (e) the compute side at `pubVJ9`
  have XC := xctxJ9 δ b Pb c χ M' tr (by omega) hacc.hsatX hacc.hinjX hacc.hadjX
  have hden : ∀ k : Fin 3, denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
      (qM δ b Pb tr (chalsMJ8 δ χ) M'.pubsC) rA
      (hdV (envX9 δ b Pb c χ M' tr 0) (![xS, xF, xE] k)) = some (claimNoun c k) := by
    intro k
    haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
    rw [row0_hd9 XC k]
    show denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M'.pubsC) rA
      ((((claimKH p (claimNoun c k) (M.m k).1).1 : ℕ) : ZMod p).val,
        (((claimKH p (claimNoun c k) (M.m k).1).2 : ℕ) : ZMod p).val) = some (claimNoun c k)
    cases hx : claimNoun c k with
    | atom v =>
      by_cases hv : p ≤ v
      · have hkb : isBigN p (claimNoun c k) = true := by rw [hx]; simp [isBigN, hv]
        have hI := hacc'.hclI k (Or.inr hkb)
        simp only [claimKH, if_pos hv, ZMod.val_natCast, Nat.mod_eq_of_lt hI,
          Nat.mod_eq_of_lt (show 2 < p by omega)]
        rw [← hx]; exact hbig k hkb
      · simp only [claimKH, if_neg hv, ZMod.val_natCast, Nat.zero_mod, Nat.mod_eq_of_lt (Nat.lt_of_not_le hv)]
        rfl
    | cell a b' =>
      have hkc : isCellN (claimNoun c k) = true := by rw [hx]; rfl
      have hI := hacc'.hclI k (Or.inl hkc)
      simp only [claimKH, ZMod.val_natCast, Nat.mod_eq_of_lt hI, Nat.mod_eq_of_lt (show 1 < p by omega)]
      rw [← hx]; exact hcell k hkc
  -- (f) the compute IO events (`x`, `p`, `s`), the walk events
  have hx : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (R.D.cxReqs tr χ) (R.D.cxProvs tr χ) := O.hout_x hl.budX.1 hl.budX.2
  rw [hl.rdX.1, hl.rdX.2] at hx
  have hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (L.pReqs tr (toVSQ χ)) (L.pProvs tr (toVSQ χ)) := O.hout_p hl.budP.1 hl.budP.2
  rw [hl.rdP.1, hl.rdP.2] at hpp
  have hs : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (R.D.svReqs tr χ) (R.D.svProvs tr χ) := O.hout_s hl.budS.1 hl.budS.2
  rw [hl.rdS.1, hl.rdS.2] at hs
  have hV : (chalsAJ8Z δ χ 0, chalsAJ8Z δ χ 1) ∉ WalkVCL.walkEvent (algebraMap (ZMod p) K δ) (R.wdC tr χ) :=
    by rw [(chalsAJ8Z_01 δ χ).1, (chalsAJ8Z_01 δ χ).2]; exact O.houtV
  rw [hWV] at hV
  have hW := wchain_out L (outside40C R L hout)
  rw [hl.rdWW, ← (coinW_J8 δ χ).1, ← (coinW_J8 δ χ).2] at hW
  have hw0 : (limbVal b (chalVJ8 b χ) chalAlphaW, limbVal b (chalVJ8 b χ) chalGammaW) ∉
      cwEvent (K := K) (L.cRows tr) (L.cH tr) := O.hw rfl rfl
  rw [hl.rdWC.1, hl.rdWC.2] at hw0
  have hα0 : limbVal b (chalVJ8 b χ) chalAlphaW ∉ tileSet (K := K) (foOf (L.cRows tr)) (L.cH tr) := O.hα rfl
  rw [hl.rdWC.1, hl.rdWC.2] at hα0
  have hw9 := hw0
  rw [← rowsWX_envX9 δ b Pb c χ M' tr] at hw9
  have hα9 := hα0
  rw [← rowsWX_envX9 δ b Pb c χ M' tr] at hα9
  have hEinj := EncInjJ8.encInj2_of_outside (withLiftC R L).D
    (outside_sumJ8_D (withLiftC R L) hout .bivariateCensus (by decide) (by decide) (by decide)) hq' O.z_ne hE
    htabC hl.hvp hl.hext hqM hk hl.hprs
  exact HokJ9G.acceptsJ9_holdsN_finalLG (χ := χ) (c := c) (m := M'.m) (ρ := M'.ρ) (ρS := M'.ρS)
    (pv := pubVJ9 δ b c M'.m M'.ρ M'.ρS χ) (hpv := pubVJ9_hi δ b c M'.m M'.ρ M'.ρS χ) (C := XC) (hp := hp)
    (provs := provsJ8 δ b Pb χ M' tr) (ext := extJ8 δ b Pb c χ M' tr)
    (hnC := Pb.hnC) (nodesC := Pb.nodesC) (orbitC := Pb.orbitC) (chalsC := chalsMJ8 δ χ) (pubsC := M'.pubsC)
    (QC := qM δ b Pb tr (chalsMJ8 δ χ) M'.pubsC) (hsatC := hacc.hsatC) (hbindC := hacc.hbindC)
    (hinjC := hacc.hinjC) (hadjC := hacc.hadjC) (hchC := fun _ _ _ => rfl)
    (kroots := Pb.kroots) (hnW := Pb.hnW) (nodesW := Pb.nodesW) (orbitW := Pb.orbitW) (chalsW := chalsMJ8 δ χ)
    (pubsW := M'.pubsW) (QW := qW δ b Pb tr (chalsMJ8 δ χ) M'.pubsW) (hsatW := hacc.hsatW) (hbindW := hacc.hbindW)
    (hF := hF') (hp64 := by rw [hrc]; omega) (hinjW := hacc.hinjW) (hadjW := hacc.hadjW)
    (hchW := fun _ _ _ => rfl)
    (nodesJ := Pb.nodesJ) (orbitJ := Pb.orbitJ) (pubsJ := M'.pubsJ) (lay := Pb.lay)
    (PJ := qJ δ b Pb tr (chalsJJ8 χ) M'.pubsJ) (hJk := hacc.hJk)
    (Rt := Pb.Rt) (regs := Pb.regs) (ids := Pb.ids) (idx := Pb.idx) (rk := Pb.rk)
    (hnA := Pb.hnA) (nodesA := Pb.nodesA) (orbitA := Pb.orbitA) (chalsA := chalsAJ8Z δ χ) (pubsA := M'.pubsA)
    (QA := qA δ b Pb tr (chalsAJ8Z δ χ) M'.pubsA) (QL := qAL δ b Pb tr (chalsAJ8Z δ χ) M'.pubsA)
    (hQA := (qAL_toHQ δ b Pb tr _ _).symm) (hsatL := hacc3.hsatL) (hbindL := hacc3.hbindL)
    (hinjA := hacc.hinjA) (hadjA := hacc.hadjA) (hchA := fun j h1 h2 => chalsAJ8Z_agree δ χ j h1 h2)
    (krootsV := Pb.krootsV) (hnV := Pb.hnV) (nodesV := Pb.nodesV) (orbitV := Pb.orbitV) (chalsV := chalsAJ8Z δ χ)
    (pubsV := M'.pubsV) (QV := qV δ b Pb tr (chalsAJ8Z δ χ) M'.pubsV) (hsatV := hacc.hsatV) (hbindV := hacc.hbindV)
    (hinjV := hacc.hinjV) (hadjV := hacc.hadjV) (hchV := fun j h1 h2 => chalsAJ8Z_agree δ χ j h1 h2)
    (hprovX := rfl) (hextX := rfl) (hprovP := rfl) (hextP := rfl) (hprovS := provsJ8_sZ δ b Pb χ M' tr) (hextS := rfl)
    (hGx := hacc.hGx) (hGp := hacc.hGp) (hGS := hacc.hGS)
    (hout := fun bl hbl => by
      cases bl with
      | x => rw [reqs9_eq δ b Pb c χ M' tr]; exact hx
      | p => rw [reqs9_eq δ b Pb c χ M' tr]; exact hpp
      | s => exact absurd rfl hbl)
    (houtS := by rw [reqs9_eq δ b Pb c χ M' tr]; exact hs)
    (hcount := fun bl => by rw [reqs9_eq δ b Pb c χ M' tr]; exact hl.hcount bl)
    (hnpC := hacc.hnpC) (hzC := hzC) (γV := _) (ρV := _) (hokC := chalsOK_J8 (δ := δ) χ)
    (reqsC := M'.reqsC) (xsC := M'.xsC) (hsumC := hacc.hsumC) (houtC := houtC) (hxneC := hacc.hxneC)
    (hcountC := hcountC) (vp := M'.vp) (hxC := hacc.hxC) (hvp0 := hacc.hvp0)
    (E := encJ8 δ χ) (hconsE := fun a b' => by rw [hz2]; rfl) (hE := by rw [hz2]; exact hE)
    (rA := rA) (hvp := hl.hvp) (hEinj := hEinj)
    (hkW := hacc.hkW) (hknW := hacc.hknW) (hkpW := hacc.hkpW) (hXW := hl.hXW) (hHXW := hl.hHXW) (houtW := hW)
    (hRg := hRg) (hlay := hacc.hlay) (hsmall := hacc.hsmall) (huniq := hacc.huniq) (hTpl := hacc.hTpl)
    (hnd := hacc.hnd) (hidx := hacc.hidx) (hrk := hacc.hrk) (hlt := hacc.hlt) (hpinC := hacc.hpinC)
    (hinjE := hinjE)
    (hRA := hl.hRA) (hsA := hl.hsA) (hidxA := hl.hidxA) (hpG := hpG) (hrn := hl.hrn) (hB := hl.hB)
    (hwRA := hl.hwRA) (wreqs := M'.wreqs) (hbalA := hacc.hbalA) (houtA := hl.houtA)
    (hcountA := hcountA_ofZ'' δ b Pb c χ M tr hacc'.hlenA) (hnpA := hacc.hnpA) (hzA := by rw [chalsAJ8Z_of_ne δ χ (by omega) (by omega), chalsAJ8Z_of_ne δ χ (by omega) (by omega)]; exact O.atom_hz) (hservedA := hl.hservedA)
    (hyV := ⟨rfl, rfl⟩) (hkV := hacc.hkV) (hknV := hacc.hknV) (hkpV := hacc.hkpV) (hseedsV := hl.hseedsV)
    (hXV := hXV) (hHXV := hl.hHXV) (houtV := hV)
    (hseed := hseedJ9 XC) (hα := hα9) (hw := hw9) (hreal := hrealJ9 XC hacc'.hcellF) (x := c) (hs := hden 0)
    (hf := hden 1) (he := hden 2)

end Sound

section Final
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (xS xF xE)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (envCJ8)

/-- **The claim extension at the real data** (`X := claimX`, `rA := rAT`): the four census facts `hsoundJ9XUA`
reads, from `AcceptsJ9V` at an absent layout. -/
theorem claimX_factsG (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (hp17 : 17 < p) {r0 : RowsJ8} {g0 : ℕ}
    (hacc3 : AcceptsJ9V.AcceptsJ9V δ b Pb Rg c χ M tr r0 g0) (hpos : 1 ≤ Pb.krootsV) :
    (∀ k, isBigN p (claimNoun c k) = true → claimNoun c k ∈ claimX (K := K) b Pb c tr) ∧
    (∀ k, isBigN p (claimNoun c k) = true → ∀ m, extB p (rAT (K := K) b Pb tr) (M.m k).1 = some m →
      m ∈ claimX (K := K) b Pb c tr) ∧
    (∀ x ∈ claimX (K := K) b Pb c tr, (∃ k, isBigN p (claimNoun c k) = true ∧ x = claimNoun c k) ∨
      ∃ j, extB p (rAT (K := K) b Pb tr) j = some x) := by
  have hacc := acceptsJ9ZG_of_V hacc3 hpos
  refine ⟨fun k hkb => List.mem_append_left _ (List.mem_map.mpr
    ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkb⟩, rfl⟩), fun k hkb m hm => ?_, fun x hx => ?_⟩
  · have hI := hacc3.hclI k (Or.inr hkb)
    have hr := claimRow0_eqG δ b Pb Rg c χ _ tr hp17 hacc k
    rw [claimHJ9_snd (Or.inr hkb)] at hr
    have hv : (claimRow0 Pb tr k).val = (M.m k).1 := by
      rw [hr]; show (((M.m k).1 : ℕ) : ZMod p).val = _; rw [ZMod.val_natCast, Nat.mod_eq_of_lt hI]
    refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkb⟩, ?_⟩)
    show extB p (rAT (K := K) b Pb tr) (claimRow0 Pb tr k).val = some m
    rw [hv]; exact hm
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      exact Or.inl ⟨k, (List.mem_filter.mp hk).2, rfl⟩
    · obtain ⟨k, -, hk⟩ := List.mem_filterMap.mp hx
      exact Or.inr ⟨_, hk⟩


open Classical in
/-- **The J-9 bound at a PRESENT atom walk** (`1 ≤ krootsV`), through `RepriceJ8.probJ8X_lt_155_census32` at the
J-9 data `withFpxV (withLiftC RR49 LL4)`. -/
theorem probJ9_present [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r EncInjJ8.cornerC) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9 : (censusG Pb c).length + 6 ≤ 2 ^ 31) (hpos : 1 ≤ Pb.krootsV) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsJ9V.AcceptsJ9V δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  RepriceJ8.probJ8X_lt_155_census32
    (AtomFpxJ8.withFpxV δ b
      (withLiftC (RR49 δ b (g := g + r.N) (R0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (P := 2 ^ 66))
          Pb c [] (by simp) (LinkJ8NV.layLe_ofG Pb hLC hLM hLW hLA hLV) rfl hnM hreg9)
        (LL4 δ b (L0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ)) Pb [] (by simp)
          (LinkJ8NV.layLe_ofG Pb hLC hLM hLW hLA hLV)))
      Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA) Q hQ _ _
    (fun χ hacc hout => by
      obtain ⟨M, hM⟩ := hacc
      have hp17 : 17 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
      obtain ⟨hXbig, hXext, hXsrc⟩ := claimX_factsG δ b Pb c χ M (Q χ) hp17 hM hpos
      refine hsoundJ9XUG δ b Pb hRg c χ M (Q χ) _ _ hpG hqM hk hmax hM hpos hout hM.hbudV.2.2.2 hM.hbudV.2.2.1
        (wdV_view δ b Pb (Q χ) _ _)
        (linkXUG9_of_R5 δ b Pb c χ M (Q χ) _ _ [] (by simp) (LinkJ8NV.layLe_ofG Pb hLC hLM hLW hLA hLV) rfl hnM
          hreg9 hpG hr hg hmax hM hpos hout) (claimX b Pb c (Q χ)) ?_ hXbig hXext hXsrc
      intro pr hpr
      show pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2 (TraceJ8.rowsMJ8 Pb.nodesC Pb.orbitC (Q χ))
        (extT8 b Pb (Q χ)) ++ (censusG Pb c ++ claimX b Pb c (Q χ)))
      rw [rowsMJ8_eq_cellT δ b Pb χ (toMsgJ9Z δ b Pb c χ M (Q χ)) (Q χ)]
      exact hpr)
    hcK hr (le_refl _) (RepriceJ8.g32_of_corner hr hg)

open Classical in
/-- **THE J-9 (B) BOUND: `AcceptsJ9V`, the atom walk present OR absent.**  At `LinkJ8A.probJ8V_final`'s binders
(`hreg` read as `|censusG Pb c| + 6 ≤ 2^31`): `Pr_χ[(∃ M, AcceptsJ9V … (Q χ) r g) ∧ ¬ HoldsN c] < 2^-155`. -/
theorem probJ9B_final [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r EncInjJ8.cornerC) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9 : (censusG Pb c).length + 6 ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsJ9V.AcceptsJ9V δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 := by
  rcases Nat.eq_zero_or_pos Pb.krootsV with h0 | hpos
  · exact LinkJ9A.probJ9_absent δ b Pb hRg c Q hQ hpG hcK hr hqM hk hmax hg hLC hLM hLW hLA hLV hnM hreg9 h0
  · exact probJ9_present δ b Pb hRg c Q hQ hpG hcK hr hqM hk hmax hg hLC hLM hLW hLA hLV hnM hreg9 hpos

end Final

section Clean
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {g : ℕ}

open Classical in
/-- **`probJ9B_final_clean`**: `probJ9B_final` without the derived binders `[Fact (ringChar (ZMod p)).Prime]` and
`[Algebra (ZMod (ringChar (ZMod p))) K]` (built from `ringChar (ZMod p) = p`, as `CleanJ8.probJ8V_final_clean`). -/
theorem probJ9B_final_clean [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ8 p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r EncInjJ8.cornerC) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9 : (censusG Pb c).length + 6 ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsJ9V.AcceptsJ9V δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  haveI : Fact (ringChar (ZMod p)).Prime := ⟨by rw [hrc]; exact Fact.out⟩
  haveI : Algebra (ZMod (ringChar (ZMod p))) K := @Eq.rec ℕ p (fun q _ => Algebra (ZMod q) K) ‹Algebra (ZMod p) K› _ hrc.symm
  exact probJ9B_final δ b Pb hRg c Q hQ hpG hcK hr hqM hk hmax hg hLC hLM hLW hLA hLV hnM hreg9

end Clean

end

end Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9G
