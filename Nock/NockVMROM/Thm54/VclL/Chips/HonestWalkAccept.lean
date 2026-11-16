/-
  Nock/NockVMROM/Thm54/VclL/Chips/HonestWalkAccept.lean

  **The `ok`-gated walk chip accepts the honest
  walk trace** (twin of `HonestMemBridge.pathChipOk_sat_of_rows` + `HonestMemAccept.pathOk_sat`).

  * `walkChipOk_sat_of_rows`: row-local gates + the three preprocessed masks give acceptance;
  * `honestWalkQ_two`: the honest column `2` IS the preprocessed root mask `rootRowMaskW nodes kr`;
  * **`walkOk_sat`**: given `WalkBaseFacts`, `WalkKFacts` (at `α = χ₀`, `γ = χ₁`) and
    `WalkMixedFacts` (at the IO coins `γ′, ρ′`) on every row, the `ok`-gated walk chip accepts the
    interpolated honest trace.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestWalkCol
import Nock.NockVMROM.Thm54.VclL.Chips.MemFamilyVCLW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Module
open scoped Polynomial

noncomputable section

section Bridge
attribute [local irreducible] WChip.baseGates WChip.mixedGates

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kr : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- **Walk chip acceptance from row-local gates** (`ok = true`). -/
theorem walkChipOk_sat_of_rows
    (Q : Fin (walkChipOk δF kr b hn nodes orbit chals pubs true).rap.w → F[X])
    (hm0 : Q ⟨0, by rw [walkChipOk_w]; omega⟩ = firstRowMask nodes)
    (hm1 : Q ⟨1, by rw [walkChipOk_w]; omega⟩ = lastRowMask hn nodes)
    (hm2 : Q ⟨2, by rw [walkChipOk_w]; omega⟩ = rootRowMaskW nodes kr)
    (hbase : ∀ i : Fin n, ∀ g ∈ WChip.baseGates (F := F) kr,
      g.eval (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 21 chals) (slotVal b 21 pubs)) = 0)
    (hmixed : ∀ i : Fin n, ∀ g ∈ WChip.mixedGates δF kr,
      g.eval (gatherEnv b ((walkTemplate δF kr).col0 3)
          (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 21 chals) (slotVal b 21 pubs)))
        (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 21 chals) (slotVal b 21 pubs)) = 0) :
    RAP.SatisfiesWithPreprocessing (walkChipOk δF kr b hn nodes orbit chals pubs true) Q := by
  refine ⟨?_, ?_⟩
  · refine (expandChip_satisfies_iff_language (walkTemplateOk δF kr true) b _ _ orbit (rowNodeSet nodes) Q).mpr
      fun x hx => ?_
    obtain ⟨i, rfl⟩ : ∃ i, nodes i = x := by
      classical
      unfold rowNodeSet at hx
      simpa using hx
    refine ⟨?_, by simp [walkTemplateOk, walkTemplate], ?_, ?_⟩
    · intro g hg
      simp only [walkTemplateOk, okGates, if_true, List.append_nil] at hg
      exact hbase i g hg
    · simp [walkTemplateOk, walkTemplate]
    · intro g hg
      exact hmixed i g hg
  · intro j
    fin_cases j
    · exact hm0
    · exact hm1
    · exact hm2

end Bridge

section Accept
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kr : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- The honest column `2` is the preprocessed root mask. -/
theorem honestWalkQ_two (vals : Fin n → WalkVals F K (Quad (algebraMap F K δF))) :
    honestQ hn nodes (walkCol δF b kr vals) 132 ⟨2, by norm_num⟩ = rootRowMaskW nodes kr := by
  simp only [honestQ, rootRowMaskW]
  congr 1

/-- **The `31` mixed gates of the walk chip vanish at the honest environment of row `i`.** -/
theorem walk_mixed_gates_hold (vals : Fin n → WalkVals F K (Quad (algebraMap F K δF)))
    (hF : GeneratedField.PrimeFieldElems F) (ω : F) (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11)
    (hb : ∀ i, WalkBaseFacts kr vals i) (hk : ∀ i, WalkKFacts δF kr vals (chals 0) (chals 1) i)
    (hf : ∀ i, WalkMixedFacts δF kr pubs vals γ ρ i) (i : Fin n) :
    ∀ g ∈ WChip.mixedGates δF kr,
      g.eval (walkEKh δF b kr hn nodes ω chals pubs vals i) (walkEFh δF b kr hn nodes ω chals pubs vals i) = 0 := by
  intro g hg
  rcases List.mem_append.mp hg with hw | hq
  · exact walk_kgates_hold δF b kr hn nodes ω chals pubs vals hF hinj hadj i hb (hk i) g hw
  · obtain ⟨e, he, hge⟩ := List.mem_flatMap.mp hq
    have h := walk_qEqs_hold δF b kr hn nodes ω chals pubs vals hinj hadj i γ ρ hok (hf i) e he
    simp only [QE.ev, Quad.mk_eq_zero_iff] at h
    simp only [QE.gates, List.mem_cons, List.not_mem_nil, or_false] at hge
    rcases hge with rfl | rfl
    · exact h.1
    · exact h.2

/-- **The `ok`-gated walk chip accepts the honest trace** of `vals`. -/
theorem walkOk_sat (vals : Fin n → WalkVals F K (Quad (algebraMap F K δF)))
    (hF : GeneratedField.PrimeFieldElems F) (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11)
    (hb : ∀ i, WalkBaseFacts kr vals i) (hk : ∀ i, WalkKFacts δF kr vals (chals 0) (chals 1) i)
    (hf : ∀ i, WalkMixedFacts δF kr pubs vals γ ρ i) :
    RAP.SatisfiesWithPreprocessing (walkChipOk δF kr b hn nodes orbit chals pubs true)
      (fun j => honestQ hn nodes (walkCol δF b kr vals) 132
        (Fin.cast (walkChipOk_w δF kr b hn nodes orbit chals pubs true) j)) := by
  have hw := walkChipOk_w δF kr b hn nodes orbit chals pubs true
  refine walkChipOk_sat_of_rows δF kr b hn nodes orbit chals pubs _ ?_ ?_ ?_ ?_ ?_
  · exact honestQ_zero hn nodes _ (by norm_num)
  · exact honestQ_one hn nodes _ (by norm_num)
  · exact honestWalkQ_two δF kr b hn nodes vals
  · intro i g hg
    rw [envOfTrace_castW hw]
    exact walk_base_gates_hold δF b kr hn nodes orbit.ω chals pubs vals hinj hadj i (hb i) g hg
  · intro i g hg
    have e := envOfTrace_castW hw (honestWalkQ δF b kr hn nodes vals) orbit.ω (nodes i)
      (slotVal b 21 chals) (slotVal b 21 pubs)
    simp only [e]
    exact walk_mixed_gates_hold δF kr b hn nodes chals pubs vals hF orbit.ω hinj hadj γ ρ hok hb hk hf i g hg

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
