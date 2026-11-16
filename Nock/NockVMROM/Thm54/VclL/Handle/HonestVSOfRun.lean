/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestVSOfRun.lean

  Additive.

  `hVS_of_run`: `honestVCLW_of_demandH2` over the run's rows with `hleafH` from `hleafH_of_run`
  (`programLeafBound ≤ B`, `2B ≤ 2^110`) and `haxisH` from `haxisH_of_run` (`programAxisBound < 2^63` and the
  OP5 depth binder `programOp5DepthOK`), so `hd` is `rfl`.  `honest_accepted_VS_of_run`: at that datum, for
  every coin outside the priced honest bad event (`HonestGoodVS`, probability `≤ epsCVS`), the honest messages
  are accepted at `frameVS`; `hat` from `hat_of_run`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestNonVacVS
import Nock.NockVMROM.Thm54.VclL.Handle.HonestLeafH
import Nock.NockVMROM.Thm54.VclL.Handle.HonestAxisH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.TraceGen
open Module

noncomputable section

section OfRun
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC : ℕ}

/-- **The honest VS memory datum of a run** (cell list `demandH2` of the run's rows). -/
def hVS_of_run {fuel : ℕ} {subject formula result : Noun} {t : NTree (GenComputeRow Kg)}
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (V : VerifierData F K hC (shapeVW hT hP))
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hmnodes : ∀ (k : Fin (shapeVW hT hP).k) (i : Fin (V.memRows k)), V.memNodes k i = (V.orbitM k).ω ^ (i : ℕ))
    (hsizeM : ∀ k : Fin (shapeVW hT hP).k, V.memRows k ≤ 2 ^ ((shapeVW hT hP).table k).height)
    (hC0 : V.memRows (tCW hT hP) = (demandH2 (runRowsH t)).cells.length)
    (hW0 : V.memRows (tWW hT hP) = (walkRows (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads).length)
    {B : ℕ} (hB : programLeafBound (airReorder t) ≤ B) (hB2 : 2 * B ≤ 2 ^ 110)
    (haxis : Compute.programAxisBound (airReorder t) < 2 ^ 63) (hop5 : programOp5DepthOK t)
    (hmemC : (demandH2 (runRowsH t)).cells.length + 1 < ringChar F)
    (hmemW : krW (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads +
      (walkRows (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads).length < ringChar F) :
    HonestVCLW (K := K) δF hT hP hC (krW (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads) :=
  honestVCLW_of_demandH2 (runRowsH t) V hF hq hmnodes hsizeM hC0 hW0 (hleafH_of_run hrun hB hB2)
    (haxisH_of_run hrun haxis hop5) hmemC hmemW

/-- **Completeness at VS from the run.** -/
theorem honest_accepted_VS_of_run
    {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
    {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}
    {fuel : ℕ} {subject formula result : Noun} {t : NTree (GenComputeRow Kg)}
    (hev : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar F) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar F) subject) (hf : FieldEmbedding.BoundedBy (ringChar F) formula)
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (V : VerifierData F K hC (shapeVW hT hP))
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hmnodes : ∀ (k : Fin (shapeVW hT hP).k) (i : Fin (V.memRows k)), V.memNodes k i = (V.orbitM k).ω ^ (i : ℕ))
    (hsizeM : ∀ k : Fin (shapeVW hT hP).k, V.memRows k ≤ 2 ^ ((shapeVW hT hP).table k).height)
    (hC0 : V.memRows (tCW hT hP) = (demandH2 (runRowsH t)).cells.length)
    (hW0 : V.memRows (tWW hT hP) = (walkRows (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads).length)
    {B : ℕ} (hB : programLeafBound (airReorder t) ≤ B) (hB2 : 2 * B ≤ 2 ^ 110)
    (haxis : Compute.programAxisBound (airReorder t) < 2 ^ 63) (hop5 : programOp5DepthOK t)
    (hmemC : (demandH2 (runRowsH t)).cells.length + 1 < ringChar F)
    (hmemW : krW (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads +
      (walkRows (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads).length < ringChar F)
    (x : ClaimMsgVS) (hm : HonestClaimMsgFull (demandH2 (runRowsH t)).cells V.claim x)
    (hN : V.N = (bfsForest [airReorder t]).length)
    (hinj : Function.Injective V.computeNodes) (hadj : (vsOf V).AdjacentC)
    (hroot : (rowAtW (bfsForest [airReorder t]) 1).s = V.claim.subject ∧
      (rowAtW (bfsForest [airReorder t]) 1).f = V.claim.formula ∧
      (rowAtW (bfsForest [airReorder t]) 1).e = V.claim.result)
    (hbs : ∀ b ∈ (claimBinds V.claim).flatMap selfCell, b ∈ (demandH2 (runRowsH t)).cells)
    (hslot : ∀ r ∈ pathReads (demandH2 (runRowsH t)).preads, (Noun.slot r.2 r.1).isSome)
    (χ : Coins frameVS K)
    (hχ : HonestGoodVS (hVS_of_run (δF := δF) hrun V hF hq hmnodes hsizeM hC0 hW0 hB hB2 haxis hop5 hmemC hmemW)
      t x χ) :
    AcceptsG (vsOf V) (msgVS (sumC := sumC) (sumM := sumM)
      (hVS_of_run (δF := δF) hrun V hF hq hmnodes hsizeM hC0 hW0 hB hB2 haxis hop5 hmemC hmemW) t x) χ :=
  honest_accepted_VS_whp (hVS_of_run (δF := δF) hrun V hF hq hmnodes hsizeM hC0 hW0 hB hB2 haxis hop5 hmemC hmemW)
    t x hrun rfl hm hN hinj hadj hroot hbs hslot
    (hat_of_run (by have := hq; omega) hev hbound hs hf hrun) χ hχ

end OfRun

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
