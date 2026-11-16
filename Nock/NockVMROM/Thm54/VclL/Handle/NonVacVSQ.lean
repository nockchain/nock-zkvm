/-
  Nock/NockVMROM/Thm54/VclL/Handle/NonVacVSQ.lean

  Additive: a NEW module.

  * `exists_outside_two`: two events of probabilities `≤ a`, `≤ b` with `a + b < 1` miss some point;
  * **`hout_prob_le`**: along the staged honest message (`msgVSQ_staged`), the coins at which some VSQ soundness
    summand fires have probability `≤ boundVCLHQ''` (`union_prob_le` over `allSummandsG` + `epsilonVSQ_eq`);
  * `exists_good_outside`: when `epsCVSQ + boundVCLHQ'' < 1`, some coin is outside every honest bad event AND
    outside every soundness summand;
  * `claimFuel_of_run`: the claim's fuel is `fuelChip` at the verifier from the run (`hB`, `hB2`, the root row);
  * **`hsoundVSQ_premises_nonempty`**: under run facts, field facts (`|𝕂| = p³`) and `hop5`, there exist a
    verifier datum `V`, a staged message `msg` and a coin `χ` with `hV`, `AcceptsG V msg χ` and `hout` — every
    premise of `hsoundVSQ` at once.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.StagedVSQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Handle.PullVSQ Nock.NockVMROM.Thm54.VclL.Handle.SoundVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Two small events miss a point -/

theorem exists_outside_two {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] (A B : Finset α) (a b : ℚ)
    (hA : (A.card : ℚ) / Fintype.card α ≤ a) (hB : (B.card : ℚ) / Fintype.card α ≤ b) (h : a + b < 1) :
    ∃ x, x ∉ A ∧ x ∉ B := by
  by_contra hne
  push Not at hne
  have hU : (Finset.univ : Finset α) ⊆ A ∪ B := fun x _ => by
    by_cases hx : x ∈ A
    · exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_right _ (hne x hx)
  have hc : (Fintype.card α : ℚ) ≤ A.card + B.card := by
    have := (Finset.card_le_card hU).trans (Finset.card_union_le A B)
    rw [Finset.card_univ] at this
    exact_mod_cast this
  have hpos : (0 : ℚ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have : (1 : ℚ) ≤ A.card / Fintype.card α + B.card / Fintype.card α := by
    rw [← add_div, le_div_iff₀ hpos, one_mul]; exact hc
  linarith

/-! ## 2. `hout` along the staged honest message -/

section Hout
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ}

open Classical in
/-- **`hout` along any staged message**: Pr_χ[some VSQ soundness summand fires] `≤ boundVCLHQ''`. -/
theorem hout_prob_le (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC)) (memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)))
    (hst : TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP) msg.traces) :
    ((unionEvent (allSummandsG (CC := compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC))
        (MC := memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)) V msg.msg0C msg.msg0M (jointVSQ δF hT hP hC))
        msg.traces).card : ℚ) / Fintype.card (Coins frameVSQ K) ≤
      boundVCLHQ'' (Fintype.card K) (Fintype.card (Quad (algebraMap F K δF))) V.N
        (V.memRows (tCQ hT hP)) (V.memRows (tWQ hT hP)) (claimFuel V.claim) :=
  (union_prob_le _ msg.traces hst).trans (epsilonVSQ_eq δF hT hP kr hC V msg).le

variable (H : HonestVCLW (K := K) δF hT hP hC kr) (t : NTree (GenComputeRow Kg)) (x : ClaimMsgVS)

open Classical in
/-- **A coin outside every honest bad event and every soundness summand**, when `ε_c + ε_s < 1`. -/
theorem exists_good_outside (hN : (vsqOf H.V).N = (bfsForest [airReorder t]).length)
    (V : VerifierData F K hC (shapeVSQ hT hP))
    (h1 : epsCVSQ H t + boundVCLHQ'' (Fintype.card K) (Fintype.card (Quad (algebraMap F K δF))) V.N
        (V.memRows (tCQ hT hP)) (V.memRows (tWQ hT hP)) (claimFuel V.claim) < 1) :
    ∃ χ : Coins frameVSQ K, HonestGoodVSQ H t x χ ∧
      ∀ s ∈ allSummandsG (CC := compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC))
          (MC := memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)) V
          (msgVSQ (sumC := sumCVSQ hT hP hC) (sumM := sumMVSQ δF hT hP kr hC) H t x).msg0C
          (msgVSQ (sumC := sumCVSQ hT hP hC) (sumM := sumMVSQ δF hT hP kr hC) H t x).msg0M (jointVSQ δF hT hP hC),
        ¬ s.mem ((msgVSQ (sumC := sumCVSQ hT hP hC) (sumM := sumMVSQ δF hT hP kr hC) H t x).traces χ) χ := by
  set msg := msgVSQ (sumC := sumCVSQ hT hP hC) (sumM := sumMVSQ δF hT hP kr hC) H t x
  obtain ⟨χ, hA, hB⟩ := exists_outside_two
    (Finset.univ.filter fun χ : Coins frameVSQ K => ¬ HonestGoodVSQ H t x χ)
    (unionEvent (allSummandsG (CC := compCoreVSQ δF hT hP hC (sumCVSQ hT hP hC))
        (MC := memCoreVSQ δF hT hP kr hC (sumMVSQ δF hT hP kr hC)) V msg.msg0C msg.msg0M (jointVSQ δF hT hP hC))
        msg.traces) _ _ (vsqCompleteness H t x hN) (hout_prob_le V msg (msgVSQ_staged H t x)) h1
  refine ⟨χ, ?_, fun s hs hm => hB ?_⟩
  · simpa using hA
  · simp only [unionEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨s, hs, hm⟩

end Hout

/-! ## 3. The claim's fuel at the verifier from the run -/

section Fuel
variable {Kg : Type} [Field Kg] {fuel : ℕ} {subject formula result : Noun} {t : NTree (GenComputeRow Kg)}

/-- **At the run's claim, `claimFuel = fuelChip`**: the claim's nouns are the root row's, whose leaves are
`≤ programLeafBound ≤ B ≤ 2^109`. -/
theorem claimFuel_of_run (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    {B : ℕ} (hB : programLeafBound (airReorder t) ≤ B) (hB2 : 2 * B ≤ 2 ^ 110) :
    claimFuel ⟨subject, formula, result⟩ = fuelChip := by
  have hr := foldl_sup_le_of_le (bfsRows (airReorder t)) rowNounsBound hB t.label root_mem_rows
  obtain ⟨g1, g2, g3⟩ := genComputeSkeleton_root_sfe hrun
  have h' : rowNounsBound t.label ≤ B := hr
  unfold rowNounsBound at h'
  rw [g1, g2, g3] at h'
  have hf : fuelChip = 2 ^ 110 := rfl
  unfold claimFuel
  simp only [max_le_iff, sup_le_iff] at h' ⊢
  refine le_antisymm (max_le le_rfl ?_) (le_max_left _ _)
  refine max_le ?_ (max_le ?_ ?_) <;> [skip; skip; skip] <;> rw [hf] <;> omega

end Fuel

/-! ## 4. Every premise of `hsoundVSQ`, inhabited -/

section NonVac
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {fuel : ℕ} {subject formula result : Noun} {t : NTree (GenComputeRow Kg)}

attribute [local instance] ClaimDenVS.quadCharF

/-- **`hsoundVSQ_premises_nonempty`: every premise of `hsoundVSQ` holds at once, at the honest run.**
There are a verifier datum `V` (`vsqOf (vsVerifierOfRun …)`), a message `msg` (`msgVSQ` at `hVSQ_of_run`, staged)
and a coin `χ` with `V.claim = ⟨subject, formula, result⟩`, `hV : V.Checks …`, `AcceptsG V msg χ` and `hout` (no VSQ soundness summand fires).
Hypotheses: run facts (`hev hrun hbound hs hf hB hB2 haxis hnC hnW hN`), field facts (`hK3 hFd hF hq hcK`, the
instances) and the OP5 binder `hop5`. -/
theorem hsoundVSQ_premises_nonempty
    (hev : Nock.evalN fuel subject formula = some result)
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (hK3 : Module.finrank F K = 3)
    (hFd : 3 * 2 ^ (max (hCq t) (max (hTq t) (hPq t))) ∣ Fintype.card F - 1)
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    {B : ℕ} (hB : programLeafBound (airReorder t) ≤ B) (hB2 : 2 * B ≤ 2 ^ 110)
    (haxis : Compute.programAxisBound (airReorder t) < 2 ^ 63) (hop5 : programOp5DepthOK t)
    (hnC : nCr t ≤ 2 ^ 31) (hnW : nWr t ≤ 2 ^ 31) (hN : nNr t ≤ 2 ^ 31)
    (hbound : RunBoundedBy (ringChar F) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar F) subject) (hf : FieldEmbedding.BoundedBy (ringChar F) formula)
    (hcK : Fintype.card K = VclL.Events.cK) :
    ∃ (V : VerifierData F K (hCq t) (shapeVSQ (hTq t) (hPq t)))
      (msg : MessagesG (compCoreVSQ δF (hTq t) (hPq t) (hCq t) (sumCVSQ (hTq t) (hPq t) (hCq t)))
        (memCoreVSQ δF (hTq t) (hPq t) (krW (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads) (hCq t)
          (sumMVSQ δF (hTq t) (hPq t) (krW (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads) (hCq t))))
      (χ : Coins frameVSQ K),
      V.claim = ⟨subject, formula, result⟩ ∧
      V.Checks (fun a => (compCoreVSQ δF (hTq t) (hPq t) (hCq t) (sumCVSQ (hTq t) (hPq t) (hCq t))).reqBound V a +
          (memCoreVSQ δF (hTq t) (hPq t) (krW (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads) (hCq t)
            (sumMVSQ δF (hTq t) (hPq t) (krW (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads)
              (hCq t))).internalBound V a)
        (ringChar (Quad (algebraMap F K δF))) ∧
      TracesStaged frameVSQ (tableVSQ (hCq t)) (shapeVSQ (hTq t) (hPq t)) msg.traces ∧
      AcceptsG V msg χ ∧
      ∀ s ∈ allSummandsG (CC := compCoreVSQ δF (hTq t) (hPq t) (hCq t) (sumCVSQ (hTq t) (hPq t) (hCq t)))
          (MC := memCoreVSQ δF (hTq t) (hPq t) (krW (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads)
            (hCq t) (sumMVSQ δF (hTq t) (hPq t) (krW (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads)
              (hCq t)))
          V msg.msg0C msg.msg0M (jointVSQ δF (hTq t) (hPq t) (hCq t)),
        ¬ s.mem (msg.traces χ) χ := by
  set H := hVSQ_of_run (δF := δF) hev hrun hK3 hFd hF hq hB hB2 haxis hop5 hnC hnW
  set V := vsqOf (vsVerifierOfRun hev hrun hK3 hFd)
  have hNt : (vsqOf H.V).N = (bfsForest [airReorder t]).length := rfl
  have hεc : epsCVSQ H t < 1 / 2 ^ 126 := by
    refine vsqCompleteness_figure H t hcK ?_ ?_ hN
    · exact (vsV_hC0 hev hrun hK3 hFd).le.trans hnC
    · exact (vsV_hW0 hev hrun hK3 hFd).le.trans hnW
  have hεs : boundVCLHQ'' (Fintype.card K) (Fintype.card (Quad (algebraMap F K δF))) V.N
      (V.memRows (tCQ (hTq t) (hPq t))) (V.memRows (tWQ (hTq t) (hPq t))) (claimFuel V.claim) < 1 / 2 ^ 155 := by
    rw [quad_card, hcK, show V.claim = ⟨subject, formula, result⟩ from rfl, claimFuel_of_run hrun hB hB2]
    exact figVCLHQ''_155 _ _ _ hN ((vsV_hC0 hev hrun hK3 hFd).le.trans hnC)
      ((vsV_hW0 hev hrun hK3 hFd).le.trans hnW)
  have h1 : epsCVSQ H t + boundVCLHQ'' (Fintype.card K) (Fintype.card (Quad (algebraMap F K δF))) V.N
      (V.memRows (tCQ (hTq t) (hPq t))) (V.memRows (tWQ (hTq t) (hPq t))) (claimFuel V.claim) < 1 := by
    have : (1 : ℚ) / 2 ^ 126 + 1 / 2 ^ 155 < 1 := by norm_num
    linarith
  obtain ⟨χ, hgood, hout⟩ := exists_good_outside H t (xOfRun (t := t) (subject := subject) (formula := formula)
    (result := result)) hNt V h1
  exact ⟨V, _, χ, rfl, vsqV_checks hev hrun hK3 hFd hF hq hnC hnW hbound hs hf hN _ _ _, msgVSQ_staged H t _,
    honest_accepted_VSQ_of_run_chosen hev hrun hK3 hFd hF hq hB hB2 haxis hop5 hnC hnW hbound hs hf χ hgood, hout⟩

end NonVac

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
