/-
  Nock/NockVMROM/Thm54/VclL/Handle/CleanJ8.lean

  `probJ8V_final_clean` / `probJ8V_nonvacuous_clean`: the J-8 bound
  and its non-vacuity WITHOUT the duplicate binders `[Fact (ringChar (ZMod p)).Prime]` and
  `[Algebra (ZMod (ringChar (ZMod p))) K]`.  They are derived from `[Fact p.Prime]`, `[Algebra (ZMod p) K]` via
  `ringChar (ZMod p) = p` (`ZMod.ringChar_zmod_n`): the twin Fact is `ringChar_zmod_n ▸ Fact.out`, and the twin
  algebra is the transport of the given one along that equation.  Thin wrappers; statements otherwise identical.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.NonVacuousJ8

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8

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
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {g : ℕ}

open Classical in
theorem probJ8V_final_clean [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r EncInjJ8.cornerC) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsJ8V.AcceptsJ8V δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  haveI : Fact (ringChar (ZMod p)).Prime := ⟨by rw [hrc]; exact Fact.out⟩
  haveI : Algebra (ZMod (ringChar (ZMod p))) K := @Eq.rec ℕ p (fun q _ => Algebra (ZMod q) K) ‹Algebra (ZMod p) K› _ hrc.symm
  exact LinkJ8A.probJ8V_final δ b Pb hRg c Q hQ hpG hcK hr hqM hk hmax hg hLC hLM hLW hLA hLV hnM hreg

theorem probJ8V_nonvacuous_clean (hpG : p = Nock.Atoms.p) (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    ∃ (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (r : RowsJ8) (g : ℕ),
      AcceptsJ8V.AcceptsJ8V δ b Pb R0 c0 χ M tr r g ∧ Pb.krootsV = 0 ∧ ¬ 0 < Pb.krootsV ∧ Pb.nJ = 0 ∧
        Pb.regs = [] ∧ Nock.Jet.HoldsN c0 := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  haveI : Fact (ringChar (ZMod p)).Prime := ⟨by rw [hrc]; exact Fact.out⟩
  haveI : Algebra (ZMod (ringChar (ZMod p))) K := @Eq.rec ℕ p (fun q _ => Algebra (ZMod q) K) ‹Algebra (ZMod p) K› _ hrc.symm
  exact NonVacuousJ8.probJ8V_nonvacuous (K := K) δ b hpG Rt

end Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8
