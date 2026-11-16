import Nock.NockVMROM.Thm54.VclL.Compute.TowerLookup
import Nock.NockVMROM.Thm54.DeployedChipFamily

/-!
# Route (d), TWD-4 item (a) : the completeness direction of the tower kept list

`towerKept_sound`
 gave `towerKeptGates` accepted `⇒ TowerKeptHolds`; here the converse, so
`towerKeptGates` accepted `⇔ TowerKeptHolds` at the gathered environment (`towerKept_iff`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

section Complete
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **Item (a): the tower kept list is complete.**  Every kept typed gate holding in `𝕂′` at the
gathered environment gives every gate of `towerKeptGates` at `eF`. -/
theorem towerKept_complete (b : Basis (Fin 3) F K) (n e : ℕ) (he : e = MemoryTable.pwScaleExp K)
    (eF : Env F) (H : TowerKeptHolds n δ (gatherEnv b eF) eF) :
    ∀ g ∈ towerKeptGates n e b δ, g.eval eF = 0 := by
  have hc := isCoordEnv_gather b eF
  have wcomp : ∀ g : WTyped, qLinearW towerM g = true →
      g.eval (towerEnv309 δ towerM (gatherEnv b eF) eF) = 0 →
      (∀ k, (compile309 b g k).eval eF = 0) ∧
        (hasImW towerM g = true → ∀ k, (wIm b δ e g k).eval eF = 0) := fun g hl hg =>
    (gateW_iff b δ e he hc g hl).mpr hg
  intro g hg
  simp only [towerKeptGates, List.mem_append] at hg
  rcases hg with ((((((((hb | hr) | hi) | ha) | hai) | h2) | h2i) | h4) | h4i) | heq
  · exact H.base g hb
  · simp only [towerCoreRe, List.mem_flatMap, List.mem_ofFn] at hr
    obtain ⟨i, hi, ⟨k, rfl⟩⟩ := hr
    have ht := H.core i hi
    by_cases hs : specialCore i = true
    · have := (specialGate_iff b δ e he hc i hs).mpr (by
        simpa [coreTarget, hs, towerHolds] using ht)
      exact this.1 k
    · have hs' : specialCore i = false := by simpa using hs
      have := (coreGate_iff b δ towerM e he hc i hs').mpr (by
        simpa [coreTarget, hs', towerHolds, WTyped.eval, towerEnv309] using ht)
      exact this.1 k
  · simp only [towerCoreIm, List.mem_flatMap, List.mem_ofFn] at hi
    obtain ⟨i, hi, ⟨k, rfl⟩⟩ := hi
    have hik : i ∈ keptCoreIdsQ7 ∧ (decide (i = packedWalkAccId) || (!specialCore i && hasIm towerM (correctedFinalExtGate i))) = true := by
      simpa [coreImIds, List.mem_filter] using hi
    have ht := H.core i hik.1
    by_cases hs : specialCore i = true
    · have h75 : i = packedWalkAccId := by
        have := hik.2
        simp [hs] at this
        exact this
      have := (specialGate_iff b δ e he hc i hs).mpr (by
        simpa [coreTarget, hs, towerHolds] using ht)
      exact this.2 h75 k
    · have hs' : specialCore i = false := by simpa using hs
      have hI : hasIm towerM (correctedFinalExtGate i) = true := by
        have := hik.2
        simpa [hs', show i ≠ packedWalkAccId from by
          intro hh; subst hh; simp [specialCore] at hs'] using this
      have := (coreGate_iff b δ towerM e he hc i hs').mpr (by
        simpa [coreTarget, hs', towerHolds, WTyped.eval, towerEnv309] using ht)
      exact this.2 hI k
  · simp only [correctedAux309, List.mem_flatten, List.mem_ofFn] at ha
    obtain ⟨_, ⟨j, rfl⟩, hk⟩ := ha
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hk
    have hg : auxTarget j ∈ (List.finRange 3).map auxTarget :=
      List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
    have := wcomp _ (towerWGates_qLinear _ (by simp [towerWGates, hg])) (H.aux j)
    rw [auxRe_eq]
    exact this.1 k
  · simp only [wImList, List.mem_flatMap, List.mem_filter, List.mem_ofFn] at hai
    obtain ⟨t, ⟨ht, hI⟩, ⟨k, rfl⟩⟩ := hai
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp ht
    have hg : auxTarget j ∈ (List.finRange 3).map auxTarget :=
      List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
    exact (wcomp _ (towerWGates_qLinear _ (by simp [towerWGates, hg])) (H.aux j)).2 hI k
  · simp only [compileList309, List.mem_flatMap, List.mem_ofFn] at h2
    obtain ⟨t, ht, ⟨k, rfl⟩⟩ := h2
    exact (wcomp t (towerWGates_qLinear _ (by
      simp only [towerWGates, List.mem_append]; exact Or.inl (Or.inr (endpoint2Q7_sub t ht))))
      (H.ep2 t ht)).1 k
  · simp only [wImList, List.mem_flatMap, List.mem_filter, List.mem_ofFn] at h2i
    obtain ⟨t, ⟨ht, hI⟩, ⟨k, rfl⟩⟩ := h2i
    exact (wcomp t (towerWGates_qLinear _ (by
      simp only [towerWGates, List.mem_append]; exact Or.inl (Or.inr (endpoint2Q7_sub t ht))))
      (H.ep2 t ht)).2 hI k
  · simp only [compileList309, List.mem_flatMap, List.mem_ofFn] at h4
    obtain ⟨t, ht, ⟨k, rfl⟩⟩ := h4
    exact (wcomp t (towerWGates_qLinear _ (by
      simp only [towerWGates, List.mem_append]; exact Or.inr ht)) (H.ep4 t ht)).1 k
  · simp only [wImList, List.mem_flatMap, List.mem_filter, List.mem_ofFn] at h4i
    obtain ⟨t, ⟨ht, hI⟩, ⟨k, rfl⟩⟩ := h4i
    exact (wcomp t (towerWGates_qLinear _ (by
      simp only [towerWGates, List.mem_append]; exact Or.inr ht)) (H.ep4 t ht)).2 hI k
  · exact H.eq g heq

/-- **`towerKeptGates` accepted at `eF` iff the kept typed gates hold in `𝕂′`.** -/
theorem towerKept_iff (b : Basis (Fin 3) F K) (n e : ℕ) (he : e = MemoryTable.pwScaleExp K)
    (eF : Env F) :
    (∀ g ∈ towerKeptGates n e b δ, g.eval eF = 0) ↔ TowerKeptHolds n δ (gatherEnv b eF) eF :=
  ⟨towerKept_sound δ b n e he eF, towerKept_complete δ b n e he eF⟩

end Complete

/-! ## The three measured items of TWD-3 (appended columns, publics, rounds) -/

section Measured
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP

/-- **Im columns `394.. 408`** (inverse / accumulator Im triples): every Im role column of
`fullImMap` (ext roles and walk roles) lies in `232.. 393`, so the five appended triples
`394, 397, 400, 403, 406` are disjoint from them and from the width-`232` chip. -/
theorem appendedCols_fresh :
    (∀ r : Fin 63, ∀ c, fullImMap.ext r = some c → 232 ≤ c ∧ c + 3 ≤ 394) ∧
    (∀ j : Fin 2, ∀ c, fullImMap.walk j = some c → 232 ≤ c ∧ c + 3 ≤ 394) := by
  constructor <;> decide +kernel

/-- **ρ′ Im publics `51.. 56`** (CORRECTED from TWD-3's `49.. 54`, which overlapped the walk-seed
Im public triple `48.. 50`): disjoint from the gate-read publics `0..8`, `20..41`, the accumulator
terminals `42..47` and the seed Im triple. -/
theorem rhoIm_pubs_fresh :
    fullImMap.extPub 1 = some 48 ∧ fullImMap.extPub 0 = none ∧ fullImMap.extPub 2 = none ∧
    (∀ j, 51 ≤ j → j < 57 → j ∉ DeployedChipFamily.computePublicReadSet ∧ ¬ (42 ≤ j ∧ j < 51)) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro j h1 h2
  refine ⟨?_, by omega⟩
  simp only [DeployedChipFamily.computePublicReadSet, List.mem_append, List.mem_range, List.mem_map]
  rintro (h | ⟨a, ha, rfl⟩) <;> omega

/-- The gate semantics
(`computeChipVCLQ7T_sat_iff`) does not read `wRAP`; the placement is forced by "no existing column
constant moves". -/
theorem vclRAPQ7T_wRAP
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n e : ℕ} (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (vclRAPQ7T (n := n) (e := e) b δ chalV pubVal orbit H).wRAP = ![208, 202] ∧
      208 + 202 = vclWidthT ∧ 232 ≤ 394 ∧ 394 + 15 + 1 = vclWidthT := ⟨rfl, rfl, by norm_num, rfl⟩

end Measured

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
