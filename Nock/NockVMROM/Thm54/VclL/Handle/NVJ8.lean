/-
  Nock/NockVMROM/Thm54/VclL/Handle/NVJ8.lean

  **A compiled completeness obstruction of `AcceptsJ8'''`.**

  * **`regs_or_ids_of_acceptsL`**: every inhabitant of `AcceptsJ8'''` has a NON-EMPTY J layout,
    `Pb.regs ≠ [] ∨ Pb.ids ≠ []`.  The conjuncts that force it are `AcceptsJ8''.hnJ : 0 < Pb.nJ` and
    `AcceptsJ8''.hlay : List.ofFn Pb.lay = layoutJ8 Pb.Rt Pb.regs Pb.ids`, since `layoutJ8 R [] [] = []`
    (`layoutJ8_nil`).
  * **`no_acceptsL_empty_registry`**: with the EMPTY registry (`Pb.regs = []`) and no jet call (`Pb.ids = []`, the
    layout of every jet-free run), nothing is accepted: no coin, message, trace, rows or budget.  So the NV brief's
    first instance (`*[[0 0] [0 1]] = [0 0]`, no jets, empty registry) has NO inhabitant.  This is a completeness
    bug of the predicate for empty-registry deployments; the unsatisfiable conjunct is `hnJ` (given `hlay`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.NVJ8

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

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L

/-- The J layout of an empty registry with no jet call is empty. -/
theorem layoutJ8_nil (R : ℕ → Nock.Jet.Autogen.Tpl) : layoutJ8 R [] [] = [] := by
  simp [Nock.Jet.ChipJ8.layoutJ8, Nock.Jet.ChipJ8.blocks]

section Accept
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **Every inhabitant of `AcceptsJ8'''` has a non-empty J layout** (`hnJ` + `hlay`). -/
theorem regs_or_ids_of_acceptsL {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim}
    {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsJ8''' δ b Pb Rg c χ M tr r g) : Pb.regs ≠ [] ∨ Pb.ids ≠ [] := by
  by_contra hne
  rw [not_or, not_not, not_not] at hne
  have hl := h.toPP.hlay
  rw [hne.1, hne.2, layoutJ8_nil] at hl
  have hlen := congrArg List.length hl
  rw [List.length_ofFn, List.length_nil] at hlen
  exact absurd h.toPP.hnJ (by omega)

/-- **No inhabitant at the empty registry with a jet-free layout**: `Pb.regs = []` and `Pb.ids = []` ⇒ for every
claim, rows and budget there is no coin, message and trace with `AcceptsJ8'''`.  The unsatisfiable conjunct is
`hnJ : 0 < Pb.nJ` (forced to `nJ = 0` by `hlay`). -/
theorem no_acceptsL_empty_registry {Pb : PubJ8 p} (hreg : Pb.regs = []) (hids : Pb.ids = [])
    (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (r : RowsJ8) (g : ℕ) :
    ¬ ∃ (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)), AcceptsJ8''' δ b Pb Rg c χ M tr r g := by
  rintro ⟨χ, M, tr, h⟩
  rcases regs_or_ids_of_acceptsL δ b h with h1 | h1
  · exact h1 hreg
  · exact h1 hids

end Accept

end Nock.NockVMROM.Thm54.VclL.Handle.NVJ8
