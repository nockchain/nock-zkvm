/-
  Nock/NockVMROM/Thm54/VclL/Handle/NonVacuousJ8.lean

  **`probJ8V_nonvacuous`.**  The J-8 bound `LinkJ8A.probJ8V_final` is about
  `Pr[(∃ M, AcceptsJ8V …) ∧ ¬HoldsN c]`; it is not vacuous: the predicate `AcceptsJ8V` is inhabited (`InhabJ8Main.inhabitant_goldilocks`) by a TRUE claim, at a layout with the J chip absent, no registers, and the
  atom walk absent (`krootsV = 0`).  That layout takes the ABSENT branch of `probJ8V_final`
  (`rcases Nat.eq_zero_or_pos Pb.krootsV`, first case, `probJ8V_absent`), not the present one (`¬ 0 < krootsV`).
  Not claimed: a staged trace map `StJ8` through the honest traces (the inhabitant is at one coin).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Main
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.NonVacuousJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **`probJ8V_final` is not vacuous**: at Goldilocks, `AcceptsJ8V` is inhabited for the true claim `c0`, at a
layout with `krootsV = 0` (so `probJ8V_final` takes its ABSENT branch, `probJ8V_absent`, and not the present one). -/
theorem probJ8V_nonvacuous (hpG : p = Nock.Atoms.p) (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    ∃ (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (r : RowsJ8) (g : ℕ),
      AcceptsJ8V δ b Pb R0 c0 χ M tr r g ∧ Pb.krootsV = 0 ∧ ¬ 0 < Pb.krootsV ∧ Pb.nJ = 0 ∧ Pb.regs = [] ∧
        Nock.Jet.HoldsN c0 := by
  obtain ⟨Pb, χ, M, tr, r, g, hacc, hk, hJ, hreg, hH⟩ := InhabJ8Main.inhabitant_goldilocks (K := K) δ b hpG Rt
  exact ⟨Pb, χ, M, tr, r, g, hacc, hk, by omega, hJ, hreg, hH⟩

end Nock.NockVMROM.Thm54.VclL.Handle.NonVacuousJ8
