/-
  Nock/NockVMROM/Thm54/VclL/Handle/EpsFigVS2.lean

  New module beside `EpsFigVS.standaloneVS_122`, same statement shape and
  proof: `N, D, W ≤ 2^32` gives `< 2^-120` (`figVCLH''_two_pow_32`); `N ≤ 2^21`, `D ≤ 2^20`, `W ≤ 2^21` gives
  `< 2^-142` (`figVCLH''_kernel`).  Additive.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS2

open Nock Nock.Walk Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Module
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVS
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVS Nock.NockVMROM.Thm54.VclL.Handle.ServedVS
open Nock.NockVMROM.Thm54.VclL.Handle.ServedPVS Nock.NockVMROM.Thm54.VclL.Handle.WalkGenVS
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS Nock.NockVMROM.Thm54.VclL.Handle.CensusVS
open Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVS Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVS
open Nock.NockVMROM.Thm54.VclL.Handle.WalkChainSumVS Nock.NockVMROM.Thm54.VclL.Handle.CWalkChipVS
open Nock.NockVMROM.Thm54.VclL.Handle.SoundVS
open Nock.NockVMROM.Thm54.FiniteIO
open scoped Polynomial

open Nock.NockVMROM.Thm54.VclL.Handle.EpsVS Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.SVGenuineF (HoldsF)

noncomputable section

open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS

section Figs
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)


open Classical in
/-- **120 bits end to end at VS** (`N, D, W ≤ 2^32`). -/
theorem standaloneVS_120 (hp : 2 ^ 63 < ringChar F) :
    letI : Fact (ringChar F).Prime := ⟨prime_of_big hp⟩
    letI : Algebra (ZMod (ringChar F)) K := zmodAlg
    ∀ (V : VerifierData F K hC (shapeVS hT hP))
      (_ : V.Checks (fun a => (compCoreVS δF hT hP hC (sumCVS hT hP hC)).reqBound V a +
        (memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC)).internalBound V a)
        (ringChar (Quad (algebraMap F K δF))))
      (msg : MessagesG (compCoreVS δF hT hP hC (sumCVS hT hP hC))
        (memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC)))
      (_ : TracesStaged frameVS (tableVS hC) (shapeVS hT hP) msg.traces)
      (_ : Fintype.card K = cK)
      (_ : V.N ≤ 2 ^ 32) (_ : V.memRows (tCS hT hP) ≤ 2 ^ 32) (_ : V.memRows (tWS hT hP) ≤ 2 ^ 32)
      (_ : leafBoundF (ringChar F) V.N V.claim ≤ 2 ^ 110),
    ((Finset.univ.filter fun χ : Coins frameVS K => AcceptsG V msg χ ∧ ¬ HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVS K) < 1 / (2 : ℚ) ^ 120 := by
  intro V hV msg hst hcK hN hD hW hΛ
  refine lt_of_le_of_lt (standaloneVS_soundness_le δF hT hP kr hC hp V hV msg hst) ?_
  rw [hcK, quad_card, hcK, claimFuel_eq_fuelChip _ _ V.hN _ hΛ]
  exact figVCLH''_two_pow_32 _ _ _ hN hD hW

open Classical in
/-- **142 bits end to end at VS** (`N ≤ 2^21`, `D ≤ 2^20`, `W ≤ 2^21`). -/
theorem standaloneVS_142 (hp : 2 ^ 63 < ringChar F) :
    letI : Fact (ringChar F).Prime := ⟨prime_of_big hp⟩
    letI : Algebra (ZMod (ringChar F)) K := zmodAlg
    ∀ (V : VerifierData F K hC (shapeVS hT hP))
      (_ : V.Checks (fun a => (compCoreVS δF hT hP hC (sumCVS hT hP hC)).reqBound V a +
        (memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC)).internalBound V a)
        (ringChar (Quad (algebraMap F K δF))))
      (msg : MessagesG (compCoreVS δF hT hP hC (sumCVS hT hP hC))
        (memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC)))
      (_ : TracesStaged frameVS (tableVS hC) (shapeVS hT hP) msg.traces)
      (_ : Fintype.card K = cK)
      (_ : V.N ≤ 2 ^ 21) (_ : V.memRows (tCS hT hP) ≤ 2 ^ 20) (_ : V.memRows (tWS hT hP) ≤ 2 ^ 21)
      (_ : leafBoundF (ringChar F) V.N V.claim ≤ 2 ^ 110),
    ((Finset.univ.filter fun χ : Coins frameVS K => AcceptsG V msg χ ∧ ¬ HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVS K) < 1 / (2 : ℚ) ^ 142 := by
  intro V hV msg hst hcK hN hD hW hΛ
  refine lt_of_le_of_lt (standaloneVS_soundness_le δF hT hP kr hC hp V hV msg hst) ?_
  rw [hcK, quad_card, hcK, claimFuel_eq_fuelChip _ _ V.hN _ hΛ]
  exact figVCLH''_kernel _ _ _ hN hD hW

end Figs

end

end Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS2
