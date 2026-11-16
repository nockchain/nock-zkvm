import Nock.NockVMROM.Thm54.VclL.Compute.TowerJointHonestW
import Nock.NockVMROM.Thm54.VclL.Chips.StandaloneVCLW

/-!
* `ringCharFactW F` / `algZModW F K`: the two instance arguments the walk family carries
  (`[Fact (ringChar F).Prime]`, `[Algebra (ZMod (ringChar F)) K]`), DERIVED from `[Field F] [Fintype F]`
  and `[Algebra F K]` (no package field, no binder).  `Algebra (ZMod n) K` is a subsingleton, and at
  `F = ZMod p` this is the same `ZMod.algebra` as `Batch1996.algRC` (up to the `CharP` proof).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.StandaloneW

noncomputable section

section Inst
variable (F K : Type) [Field F] [Fintype F] [Field K] [Algebra F K]

/-- `ringChar F` is prime (`F` a finite field). -/
theorem ringCharFactW : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩

/-- `K` has characteristic `ringChar F`. -/
theorem charP_ringCharW : CharP K (ringChar F) := by
  rw [Algebra.ringChar_eq F K]; exact ringChar.charP K

/-- The walk family's `ZMod (ringChar F)`-algebra on `K` (Mathlib's `ZMod.algebra`). -/
abbrev algZModW : Algebra (ZMod (ringChar F)) K :=
  haveI := charP_ringCharW F K
  ZMod.algebra K (ringChar F)

end Inst

section Complete
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (hT hP hC : ℕ)

open Classical in
theorem vcl_completenessW5' (HJ : HonestVCLJW (K := K) δF hT hP hC)
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hleaf : programLeafBound (airReorder HJ.t) ≤ 2 ^ 110)
    (hmemRows : ∀ k, HJ.V.memRows k + 1 < ringChar F)
    (haxis : programAxisBound (airReorder HJ.t) < 2 ^ 63)
    (hkp : krT δF HJ.t + HJ.V.memRows (tWW hT hP) < ringChar F) :
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        ∃ s ∈ (CFvW (K := K) δF hT hP hC).honestBad HJ.toHonestVCLT ++
            (MFvW (K := K) δF hT hP hC (krT δF HJ.t)).honestBad
              (jointMemW HJ hF hq hleaf hmemRows haxis hkp),
          s.mem ((CFvW (K := K) δF hT hP hC).honestQ HJ.toHonestVCLT χ,
            (MFvW (K := K) δF hT hP hC (krT δF HJ.t)).honestQ
              (jointMemW HJ hF hq hleaf hmemRows haxis hkp) χ) χ).card : ℚ) /
        Fintype.card (Coins frameVCL K) ≤
      epsilonOf ((CFvW (K := K) δF hT hP hC).honestBad HJ.toHonestVCLT ++
        (MFvW (K := K) δF hT hP hC (krT δF HJ.t)).honestBad
          (jointMemW HJ hF hq hleaf hmemRows haxis hkp)) :=
  (vcl_standaloneW δF hT hP hC (krT δF HJ.t)).completeness
    HJ.toHonestVCLT (jointMemW HJ hF hq hleaf hmemRows haxis hkp)
    (jointMemW_honestV δF HJ hF hq hleaf hmemRows haxis hkp)
    (jointMemW_honestReq δF HJ hF hq hleaf hmemRows haxis hkp)

end Complete

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
