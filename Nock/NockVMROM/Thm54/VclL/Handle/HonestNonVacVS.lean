/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestNonVacVS.lean

  Additive.

  `exists_good_coin`: when `epsCVS < 1` some coin lies outside every honest bad event; with `epsCVS_lt`
  (`|𝕂| ≥ 2^189`, rows `≤ 2^31`), `exists_accepted_VS`: some coin `χ` at which the honest run's messages
  `msgVS` are accepted at `frameVS` (`AcceptsG`), at the soundness cores `sumCVS` / `sumMVS` of `hsoundVS`.
  This discharges `hsoundVS`'s `AcceptsG` premise at a real honest message under the run hypotheses.
  NOT done here (UNCONFIRMED, open): `hV : (vsOf H.V).Checks …` and `hout` (the coin also outside the
  soundness summands; needs the staging of `msgVS`'s traces and `epsilonOf (allSummandsG …) + epsCVS < 1`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestEpsVS
import Nock.NockVMROM.Thm54.VclL.Handle.SoundVS

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.TraceGen
open Module
open scoped Polynomial

noncomputable section

section NonVac
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ} (H : HonestVCLW (K := K) δF hT hP hC kr) (t : NTree (GenComputeRow Kg)) (x : ClaimMsgVS)

open Classical in
/-- **A good coin exists** whenever the completeness error is below one. -/
theorem exists_good_coin (hN : (vsOf H.V).N = (bfsForest [airReorder t]).length) (h1 : epsCVS H t < 1) :
    ∃ χ : Coins frameVS K, HonestGoodVS H t x χ := by
  by_contra hne
  push Not at hne
  have hall : (Finset.univ.filter fun χ : Coins frameVS K => ¬ HonestGoodVS H t x χ) = Finset.univ := by
    ext χ; simp [hne χ]
  have h := vsCompleteness H t x hN
  rw [hall, Finset.card_univ] at h
  have hpos : (0 : ℚ) < Fintype.card (Coins frameVS K) := by exact_mod_cast Fintype.card_pos
  rw [div_self hpos.ne'] at h
  linarith

/-- **An accepting coin for the honest VS run** (at `hsoundVS`'s cores): under the run hypotheses of
`honest_accepted_VS_whp`, `|𝕂| ≥ 2^189` and rows `≤ 2^31`, some `χ` has `AcceptsG (vsOf H.V) (msgVS …) χ`. -/
theorem exists_accepted_VS
    {fuel : ℕ} {subject formula : Noun} {result : Noun}
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (hd : H.d = demandH2 (bfsRows (airReorder t)))
    (hm : HonestClaimMsgFull H.d.cells H.V.claim x)
    (hN : (vsOf H.V).N = (bfsForest [airReorder t]).length)
    (hinj : Function.Injective (vsOf H.V).computeNodes) (hadj : (vsOf H.V).AdjacentC)
    (hroot : (rowAtW (bfsForest [airReorder t]) 1).s = H.V.claim.subject ∧
      (rowAtW (bfsForest [airReorder t]) 1).f = H.V.claim.formula ∧
      (rowAtW (bfsForest [airReorder t]) 1).e = H.V.claim.result)
    (hbs : ∀ b ∈ (claimBinds H.V.claim).flatMap selfCell, b ∈ H.d.cells)
    (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome)
    (hat : ∀ g ∈ bfsRows (airReorder t),
      AtomsLt (ringChar F) (rowOfSkelH g.skel).sf1 ∧ AtomsLt (ringChar F) (rowOfSkelH g.skel).sf2)
    (hK : 2 ^ 189 ≤ Fintype.card K) (hnC : H.V.memRows (tCW hT hP) ≤ 2 ^ 31)
    (hnW : H.V.memRows (tWW hT hP) ≤ 2 ^ 31) (hNt : (bfsForest [airReorder t]).length ≤ 2 ^ 31) :
    ∃ χ : Coins frameVS K, AcceptsG (vsOf H.V)
      (msgVS (sumC := SoundVS.sumCVS (F := F) (K := K) hT hP hC)
        (sumM := SoundVS.sumMVS (F := F) (K := K) δF hT hP kr hC) H t x) χ := by
  have h1 : epsCVS H t < 1 :=
    lt_of_lt_of_le (epsCVS_lt H t hK hnC hnW hNt) (by norm_num)
  obtain ⟨χ, hχ⟩ := exists_good_coin H t x hN h1
  exact ⟨χ, honest_accepted_VS_whp H t x hrun hd hm hN hinj hadj hroot hbs hslot hat χ hχ⟩

end NonVac

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
