/-
  Nock/NockVMROM/Thm54/VclL/Handle/SoundVSQ.lean

  Additive.

  * **`hsoundVSQ`**: `V.Checks → AcceptsG V msg χ → outside every VSQ summand → HoldsF (ringChar K) V.claim`.
    Proof: choose `(γ, ρ)` by `exists_pair_poleFreeQ`; the re-fill `msgK` is VS-accepted at `chiK χ γ ρ`
    (`acceptsK`); the eight pulled-back summands transfer by `mem_pullS` + `CongrVSQ` (the re-fill agrees
    with the projection off the handle blocks, `tracesK_off`); the two VS handle summands are outside by the
    choice (`evX_congr` / `evP_congr`); then `hsoundVS` at `toVSV V`.  No hypothesis beyond `hsoundVS`'s.
  * **`standaloneVSQ_sound`** (`standaloneG_of_sound`), `standaloneVSQ_sound'` (instance arguments discharged
    from `2^63 < p`), **`standaloneVSQ_soundness_le`** (`≤ boundVCLHQ''`), and the figures
    **`standaloneVSQ_155 / _154 / _164`** at the VS figures' row bounds.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptVSQ
import Nock.NockVMROM.Thm54.VclL.Handle.PullVSQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.SoundVSQ

open Nock Nock.Framework Module
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ChoiceQ Nock.NockVMROM.Thm54.VclL.Handle.SummandsHQ
open Nock.NockVMROM.Thm54.VclL.Handle.DescentVSQ Nock.NockVMROM.Thm54.VclL.Handle.AcceptVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.CongrVSQ Nock.NockVMROM.Thm54.VclL.Handle.PullVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.SoundVS Nock.NockVMROM.Thm54.VclL.Handle.EpsVS
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS Nock.NockVMROM.Thm54.VclL.Handle.CensusVS
open Nock.NockVMROM.Thm54.VclL.Handle.WalkChainSumVS Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS
open Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.SVGenuineF (HoldsF)

noncomputable section

section VSQ
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)

attribute [local instance] ClaimDenVS.quadCharF

section Sound
variable [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]

/-- **`hsound` at the 17-coin frame**: an accepted VSQ trace outside every VSQ summand proves the claim.
Same hypotheses as `hsoundVS` (at the VSQ cores and frame). -/
theorem hsoundVSQ (V : VerifierData F K hC (shapeVSQ hT hP))
    (hV : V.Checks (fun a => (compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC)).reqBound V a +
      (memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)).internalBound V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC))
      (memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)))
    (χ : Coins frameVSQ K) (h : AcceptsG V msg χ)
    (hout : ∀ s ∈ allSummandsG (CC := compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC))
        (MC := memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)) V msg.msg0C msg.msg0M (jointVSQ δF hT hP hC),
      ¬ s.mem (msg.traces χ) χ) :
    HoldsF (ringChar K) V.claim := by
  set V' := toVSV hT hP hC V
  have hin : ∀ s, s ∈ allSummandsG (CC := compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC))
      (MC := memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)) V msg.msg0C msg.msg0M (jointVSQ δF hT hP hC) →
      ¬ s.mem (msg.traces χ) χ := hout
  have hL : allSummandsG (CC := compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC))
        (MC := memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)) V msg.msg0C msg.msg0M (jointVSQ δF hT hP hC) =
      [pullS hT hP hC (cwalkVS hT hP hC V'), pullS hT hP hC (ctileVS hT hP hC V'),
        pullS hT hP hC (dyckVS δF hT hP hC V'), pullS hT hP hC (walkChainVS δF hT hP kr hC V'),
        pullS hT hP hC (fpExportIOVS δF hT hP kr hC V'), pullS hT hP hC (zeroVS δF hT hP hC),
        pullS hT hP hC (censusVS δF hT hP hC V'), pullS hT hP hC (valSummand δF hT hP hC V' msg.msg0C),
        ioSummandHXQ δF hT hP hC V, ioSummandHPQ δF hT hP hC V] := rfl
  rw [hL] at hin
  have hCW := hin (pullS hT hP hC (cwalkVS hT hP hC V')) (by simp)
  have hCT := hin (pullS hT hP hC (ctileVS hT hP hC V')) (by simp)
  have hDy := hin (pullS hT hP hC (dyckVS δF hT hP hC V')) (by simp)
  have hWC := hin (pullS hT hP hC (walkChainVS δF hT hP kr hC V')) (by simp)
  have hFP := hin (pullS hT hP hC (fpExportIOVS δF hT hP kr hC V')) (by simp)
  have h0 := hin (pullS hT hP hC (zeroVS δF hT hP hC)) (by simp)
  have hc := hin (pullS hT hP hC (censusVS δF hT hP hC V')) (by simp)
  have hval := hin (pullS hT hP hC (valSummand δF hT hP hC V' msg.msg0C)) (by simp)
  have hXq := hin (ioSummandHXQ δF hT hP hC V) (by simp)
  have hPq := hin (ioSummandHPQ δF hT hP hC V) (by simp)
  -- the pole-free `𝕂` pair and the re-fill
  obtain ⟨γ, ρ, hX, hP', d1, d2, d3, d4⟩ := exists_pair_poleFreeQ δF hT hP kr hC V hV msg χ h
  have hacc := acceptsK (sumCV := sumCVS hT hP hC) (sumMV := sumMVS δF hT hP kr hC) δF V msg χ γ ρ hV h hXq hPq
    d1 d2 d3 d4
  have hoff := tracesK_off (sumCV := sumCVS hT hP hC) (sumMV := sumMVS δF hT hP kr hC) δF V msg χ γ ρ
  have hV' := toVSV_checks hT hP hC V hV
  refine hsoundVS δF hT hP kr hC V' hV' _ (chiK χ γ ρ) hacc ?_
  intro s hs
  have hL' : allSummandsG (CC := compCoreVS δF hT hP hC (sumCVS hT hP hC))
        (MC := memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC)) V'
        (msgK (sumCV := sumCVS hT hP hC) (sumMV := sumMVS δF hT hP kr hC) δF V msg χ γ ρ).msg0C
        (msgK (sumCV := sumCVS hT hP hC) (sumMV := sumMVS δF hT hP kr hC) δF V msg χ γ ρ).msg0M
        (jointVS δF hT hP hC) =
      [cwalkVS hT hP hC V', ctileVS hT hP hC V', dyckVS δF hT hP hC V', walkChainVS δF hT hP kr hC V',
        fpExportIOVS δF hT hP kr hC V', zeroVS δF hT hP hC, censusVS δF hT hP hC V',
        valSummand δF hT hP hC V' msg.msg0C, ioSummandHX hT hP hC V', ioSummandHP hT hP hC V'] := rfl
  rw [hL'] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  have pull := fun (s0 : BadSummand frameVS K (TrVS F hT hP hC)
      (TracesStaged frameVS (tableVS hC) (shapeVS hT hP))) (hs0 : ¬ (pullS hT hP hC s0).mem (msg.traces χ) χ) =>
    fun hm : s0.mem (projQ hT hP hC (msg.traces χ)) (toVS χ) => hs0 ((mem_pullS hT hP hC s0 _ _).mpr hm)
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun hm => pull _ hCW ((cwalk_congr V' hoff).mp hm)
  · exact fun hm => pull _ hCT ((ctile_congr V' hoff).mp hm)
  · exact fun hm => pull _ hDy ((dyck_congr δF V' hoff).mp hm)
  · exact fun hm => pull _ hWC ((walkChain_congr δF kr V' hoff).mp hm)
  · exact fun hm => pull _ hFP ((fp_congr δF kr V' hoff).mp hm)
  · exact fun hm => pull _ h0 ((zero_congr δF hoff).mp hm)
  · exact fun hm => pull _ hc ((census_congr δF V' hoff).mp hm)
  · exact fun hm => pull _ hval ((val_congr δF V' _ hoff).mp hm)
  · rw [mem_ioSummandHX, chiK_gam, chiK_rho, evX_congr V' hoff]; exact hX
  · rw [mem_ioSummandHP, chiK_gam, chiK_rho, evP_congr V' hoff]; exact hP'

/-- **`StandaloneG` at the 17-coin VSQ instance**, through its soundness half. -/
theorem standaloneVSQ_sound :
    StandaloneG (compCoreVSQ δF hT hP hC (sumCVSQ (F := F) (K := K) hT hP hC))
      (memCoreVSQ δF hT hP kr hC (sumMVSQ (F := F) (K := K) δF hT hP kr hC))
      (jointVSQ (F := F) (K := K) δF hT hP hC) :=
  standaloneG_of_sound (CC := compCoreVSQ δF hT hP hC (sumCVSQ (F := F) (K := K) hT hP hC))
    (MC := memCoreVSQ δF hT hP kr hC (sumMVSQ (F := F) (K := K) δF hT hP kr hC)) (jointVSQ (F := F) (K := K) δF hT hP hC)
    (fun V hV msg χ h hout => hsoundVSQ δF hT hP kr hC V hV msg χ h hout)

end Sound

/-- `standaloneVSQ_sound` with the two instance arguments discharged (as `standaloneVS_sound'`). -/
theorem standaloneVSQ_sound' (hp : 2 ^ 63 < ringChar F) :
    letI : Fact (ringChar F).Prime := ⟨prime_of_big hp⟩
    letI : Algebra (ZMod (ringChar F)) K := zmodAlg
    StandaloneG (compCoreVSQ δF hT hP hC (sumCVSQ (F := F) (K := K) hT hP hC))
      (memCoreVSQ δF hT hP kr hC (sumMVSQ (F := F) (K := K) δF hT hP kr hC))
      (jointVSQ (F := F) (K := K) δF hT hP hC) := by
  letI : Fact (ringChar F).Prime := ⟨prime_of_big hp⟩
  letI : Algebra (ZMod (ringChar F)) K := zmodAlg
  exact standaloneVSQ_sound δF hT hP kr hC

open Classical in
/-- **Soundness at VSQ with its `ε`**: the false-acceptance probability is `≤ boundVCLHQ''`. -/
theorem standaloneVSQ_soundness_le (hp : 2 ^ 63 < ringChar F) :
    letI : Fact (ringChar F).Prime := ⟨prime_of_big hp⟩
    letI : Algebra (ZMod (ringChar F)) K := zmodAlg
    ∀ (V : VerifierData F K hC (shapeVSQ hT hP))
      (_ : V.Checks (fun a => (compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC)).reqBound V a +
        (memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)).internalBound V a)
        (ringChar (Quad (algebraMap F K δF))))
      (msg : MessagesG (compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC))
        (memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)))
      (_ : TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP) msg.traces),
    ((Finset.univ.filter fun χ : Coins frameVSQ K => AcceptsG V msg χ ∧ ¬ HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVSQ K) ≤
      boundVCLHQ'' (Fintype.card K) (Fintype.card (Quad (algebraMap F K δF))) V.N
        (V.memRows (tCQ hT hP)) (V.memRows (tWQ hT hP)) (claimFuel V.claim) := by
  letI : Fact (ringChar F).Prime := ⟨prime_of_big hp⟩
  letI : Algebra (ZMod (ringChar F)) K := zmodAlg
  intro V hV msg hst
  exact ((standaloneVSQ_sound' δF hT hP kr hC hp).soundness V hV msg hst).trans
    (epsilonVSQ_eq δF hT hP kr hC V msg).le

open Classical in
/-- **155 bits end to end at VSQ** (`N, D, W ≤ 2^31`, `|𝕂| = p³`, claim leaves `≤ 2^110`). -/
theorem standaloneVSQ_155 (hp : 2 ^ 63 < ringChar F) :
    letI : Fact (ringChar F).Prime := ⟨prime_of_big hp⟩
    letI : Algebra (ZMod (ringChar F)) K := zmodAlg
    ∀ (V : VerifierData F K hC (shapeVSQ hT hP))
      (_ : V.Checks (fun a => (compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC)).reqBound V a +
        (memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)).internalBound V a)
        (ringChar (Quad (algebraMap F K δF))))
      (msg : MessagesG (compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC))
        (memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)))
      (_ : TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP) msg.traces)
      (_ : Fintype.card K = cK)
      (_ : V.N ≤ 2 ^ 31) (_ : V.memRows (tCQ hT hP) ≤ 2 ^ 31) (_ : V.memRows (tWQ hT hP) ≤ 2 ^ 31)
      (_ : leafBoundF (ringChar F) V.N V.claim ≤ 2 ^ 110),
    ((Finset.univ.filter fun χ : Coins frameVSQ K => AcceptsG V msg χ ∧ ¬ HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVSQ K) < 1 / (2 : ℚ) ^ 155 := by
  intro V hV msg hst hcK hN hD hW hΛ
  refine lt_of_le_of_lt (standaloneVSQ_soundness_le δF hT hP kr hC hp V hV msg hst) ?_
  rw [hcK, quad_card, hcK, claimFuel_eq_fuelChip _ _ V.hN _ hΛ]
  exact figVCLHQ''_155 _ _ _ hN hD hW

open Classical in
/-- **154 bits at VSQ** (`N, D, W ≤ 2^32`). -/
theorem standaloneVSQ_154 (hp : 2 ^ 63 < ringChar F) :
    letI : Fact (ringChar F).Prime := ⟨prime_of_big hp⟩
    letI : Algebra (ZMod (ringChar F)) K := zmodAlg
    ∀ (V : VerifierData F K hC (shapeVSQ hT hP))
      (_ : V.Checks (fun a => (compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC)).reqBound V a +
        (memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)).internalBound V a)
        (ringChar (Quad (algebraMap F K δF))))
      (msg : MessagesG (compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC))
        (memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)))
      (_ : TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP) msg.traces)
      (_ : Fintype.card K = cK)
      (_ : V.N ≤ 2 ^ 32) (_ : V.memRows (tCQ hT hP) ≤ 2 ^ 32) (_ : V.memRows (tWQ hT hP) ≤ 2 ^ 32)
      (_ : leafBoundF (ringChar F) V.N V.claim ≤ 2 ^ 110),
    ((Finset.univ.filter fun χ : Coins frameVSQ K => AcceptsG V msg χ ∧ ¬ HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVSQ K) < 1 / (2 : ℚ) ^ 154 := by
  intro V hV msg hst hcK hN hD hW hΛ
  refine lt_of_le_of_lt (standaloneVSQ_soundness_le δF hT hP kr hC hp V hV msg hst) ?_
  rw [hcK, quad_card, hcK, claimFuel_eq_fuelChip _ _ V.hN _ hΛ]
  exact figVCLHQ''_154 _ _ _ hN hD hW

open Classical in
/-- **164 bits at VSQ** (`N ≤ 2^21`, `D ≤ 2^20`, `W ≤ 2^21`). -/
theorem standaloneVSQ_164 (hp : 2 ^ 63 < ringChar F) :
    letI : Fact (ringChar F).Prime := ⟨prime_of_big hp⟩
    letI : Algebra (ZMod (ringChar F)) K := zmodAlg
    ∀ (V : VerifierData F K hC (shapeVSQ hT hP))
      (_ : V.Checks (fun a => (compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC)).reqBound V a +
        (memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)).internalBound V a)
        (ringChar (Quad (algebraMap F K δF))))
      (msg : MessagesG (compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC))
        (memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)))
      (_ : TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP) msg.traces)
      (_ : Fintype.card K = cK)
      (_ : V.N ≤ 2 ^ 21) (_ : V.memRows (tCQ hT hP) ≤ 2 ^ 20) (_ : V.memRows (tWQ hT hP) ≤ 2 ^ 21)
      (_ : leafBoundF (ringChar F) V.N V.claim ≤ 2 ^ 110),
    ((Finset.univ.filter fun χ : Coins frameVSQ K => AcceptsG V msg χ ∧ ¬ HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVSQ K) < 1 / (2 : ℚ) ^ 164 := by
  intro V hV msg hst hcK hN hD hW hΛ
  refine lt_of_le_of_lt (standaloneVSQ_soundness_le δF hT hP kr hC hp V hV msg hst) ?_
  rw [hcK, quad_card, hcK, claimFuel_eq_fuelChip _ _ V.hN _ hΛ]
  exact figVCLHQ''_164 _ _ _ hN hD hW

end VSQ

end

end Nock.NockVMROM.Thm54.VclL.Handle.SoundVSQ
