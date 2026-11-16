import Nock.NockVMROM.Thm54.VclL.Compute.TowerGates
import Nock.NockVMROM.Thm54.VclL.Compute.ChipQ7S

/-!
# Route (d), phase 2 : the tower kept-gate list and its soundness (item 3)

`towerKeptGates n e b δ` is `keptGatesQ7 n b` with (i) the Re body of every non-`qLinear` core gate
REPLACED by `(toQ g).1` (`coreRe`), (ii) the Im twins APPENDED (`coreIm` on `coreImIds`, `wIm` on the
Im-carrying aux / endpoint gates).  All bodies are in the SOURCE layout (so `reindexE` applies, no
column constant moves).  `towerKept_sound`: acceptance of the list at the pull-back gives every kept
typed gate in `𝕂′` at `towerEnv309` (`TowerKeptHolds`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

section Lists
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Re bodies of the kept core. -/
def towerCoreRe (b : Basis (Fin 3) F K) (δ : F) (n : ℕ) : List (CoeffExpr F) :=
  keptCoreIdsQ7.flatMap fun i => List.ofFn fun k : Fin 3 => coreRe b δ n towerM i k

/-- Im twins of the kept core. -/
def towerCoreIm (b : Basis (Fin 3) F K) (δ : F) (n : ℕ) : List (CoeffExpr F) :=
  (coreImIds towerM).flatMap fun i => List.ofFn fun k : Fin 3 => coreIm b δ n towerM i k

/-- Im twins of a list of walk-language gates (only those carrying an Im half). -/
def wImList (b : Basis (Fin 3) F K) (δ : F) (n : ℕ) (ts : List WTyped) : List (CoeffExpr F) :=
  (ts.filter (hasImW towerM)).flatMap fun g => List.ofFn fun k : Fin 3 => wIm b δ n g k

/-- **The tower kept gates** (source layout). -/
def towerKeptGates (n e : ℕ) (b : Basis (Fin 3) F K) (δ : F) : List (CoeffExpr F) :=
  finalBaseTransitionGates n ++ towerCoreRe b δ e ++ towerCoreIm b δ e ++ correctedAux309 b ++
    wImList b δ e ((List.finRange 3).map auxTarget) ++ compileList309 b endpoint2Q7 ++
    wImList b δ e endpoint2Q7 ++ compileList309 b endpoint4_309 ++ wImList b δ e endpoint4_309 ++
    finalEndpointEqualityChecks

/-- The typed / walk target of kept core id `i`. -/
def coreTarget (i : CorrectedCoreExtGateId) : WTyped :=
  if specialCore i then specialTarget i else .leaf (correctedFinalExtGate i)

end Lists

section ColsIn'
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem towerM_walk_noFormR_cols : ∀ j c, towerM.walk j = some c → ∀ k : Fin 3, NoFormR (c + k) :=
  towerM_noFormR.2

theorem wIm_colsIn (b : Basis (Fin 3) F K) (δ : F) (n : ℕ) (g : WTyped) (hg : wNoCert g = true)
    (k : Fin 3) : ColsIn NoFormR (wIm b δ n g k) :=
  colsIn_mixedCompile b _ (toQW_colsOk δ towerM n towerM_noFormR.1 towerM_noFormR.2 g hg).2 k

theorem coreIm_colsIn (b : Basis (Fin 3) F K) (δ : F) (n : ℕ) (i : CorrectedCoreExtGateId)
    (hi : i ∈ keptCoreIdsQ7) (k : Fin 3) : ColsIn NoFormR (coreIm b δ n towerM i k) := by
  unfold coreIm
  split_ifs with h75
  · refine colsIn_mul ?_ (colsIn_var _ _ (Or.inr ?_))
    · exact colsIn_sub (colsIn_const _) (colsIn_var _ _ (Or.inl (by omega)))
    · have := towerM_ext_ge 59 _ towerM_ext59
      omega
  · exact colsIn_mixedCompile b _
      (toQ_colsOk δ towerM n towerM_noFormR.1 _ (ext_gates_noCert i (keptCoreIdsQ7_sub i hi))).2 k

theorem coreRe_colsIn (b : Basis (Fin 3) F K) (δ : F) (n : ℕ) (i : CorrectedCoreExtGateId)
    (hi : i ∈ keptCoreIdsQ7) (k : Fin 3) : ColsIn NoFormR (coreRe b δ n towerM i k) := by
  unfold coreRe
  split_ifs with hc
  · have hmem : correctedCoreCoord309 b i k ∈ correctedCoreVCLQ7 b := by
      simp only [correctedCoreVCLQ7, List.mem_flatten, List.mem_map]
      exact ⟨_, ⟨i, hi, rfl⟩, List.mem_ofFn.mpr ⟨k, rfl⟩⟩
    exact correctedCoreVCL_colsIn b _ (correctedCoreVCLQ7_sub b _ hmem)
  · exact colsIn_mixedCompile b _
      (toQ_colsOk δ towerM n towerM_noFormR.1 _ (ext_gates_noCert i (keptCoreIdsQ7_sub i hi))).1 k

theorem wImList_colsIn (b : Basis (Fin 3) F K) (δ : F) (n : ℕ) (ts : List WTyped)
    (h : ∀ t ∈ ts, wNoCert t = true) : ∀ g ∈ wImList b δ n ts, ColsIn NoFormR g := by
  intro g hg
  simp only [wImList, List.mem_flatMap, List.mem_filter, List.mem_ofFn] at hg
  obtain ⟨t, ⟨ht, _⟩, ⟨k, rfl⟩⟩ := hg
  exact wIm_colsIn b δ n t (h t ht) k

theorem towerW_noCert : ∀ g ∈ towerWGates, wNoCert g = true := by decide +kernel

theorem auxTarget_noCert : ∀ g ∈ (List.finRange 3).map auxTarget, wNoCert g = true := by
  intro g hg
  apply towerW_noCert
  simp only [towerWGates, List.mem_append]
  exact Or.inl (Or.inl hg)

theorem endpoint2_noCert_tower : ∀ g ∈ endpoint2Q7, wNoCert g = true := fun g hg =>
  endpoint2_noCert g (endpoint2Q7_sub g hg)

/-- **Every tower kept gate reads only `NoFormR` columns** (so `reindexE` applies). -/
theorem towerKeptGates_colsIn (n e : ℕ) (b : Basis (Fin 3) F K) (δ : F) :
    ∀ g ∈ towerKeptGates n e b δ, ColsIn NoFormR g := by
  intro g hg
  simp only [towerKeptGates, List.mem_append] at hg
  rcases hg with ((((((((hb | hr) | hi) | ha) | hai) | h2) | h2i) | h4) | h4i) | heq
  · exact finalBaseTransitionGates_colsIn n g hb
  · simp only [towerCoreRe, List.mem_flatMap, List.mem_ofFn] at hr
    obtain ⟨i, hi, ⟨k, rfl⟩⟩ := hr
    exact coreRe_colsIn b δ e i hi k
  · simp only [towerCoreIm, List.mem_flatMap, List.mem_ofFn] at hi
    obtain ⟨i, hi, ⟨k, rfl⟩⟩ := hi
    exact coreIm_colsIn b δ e i (List.mem_filter.mp hi).1 k
  · exact correctedAux309_colsIn b g ha
  · exact wImList_colsIn b δ e _ auxTarget_noCert g hai
  · exact compileList309_colsIn b _ endpoint2_noCert_tower g h2
  · exact wImList_colsIn b δ e _ endpoint2_noCert_tower g h2i
  · exact compileList309_colsIn b _ endpoint4_noCert g h4
  · exact wImList_colsIn b δ e _ endpoint4_noCert g h4i
  · exact finalEndpointEqualityChecks_colsIn g heq

end ColsIn'

/-! ## Soundness -/

section Sound
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- A walk-language gate holds in `𝕂′` at the tower environment. -/
def towerHolds (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (eK : Env K) (eF : Env F) (g : WTyped) : Prop :=
  g.eval (towerEnv309 δ towerM eK eF) = 0

/-- Every kept typed gate holds in `𝕂′` (the typed semantic content of the tower kept list). -/
structure TowerKeptHolds (n : ℕ) (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (eK : Env K) (eF : Env F) : Prop where
  base : ∀ g ∈ finalBaseTransitionGates n, g.eval eF = 0
  core : ∀ i ∈ keptCoreIdsQ7, towerHolds δ eK eF (coreTarget i)
  aux : ∀ j, towerHolds δ eK eF (auxTarget j)
  ep2 : ∀ g ∈ endpoint2Q7, towerHolds δ eK eF g
  ep4 : ∀ g ∈ endpoint4_309, towerHolds δ eK eF g
  eq : ∀ g ∈ finalEndpointEqualityChecks, g.eval eF = 0

theorem mem_compileList309 (b : Basis (Fin 3) F K) {ts : List WTyped} {g : WTyped}
    (hg : g ∈ ts) (k : Fin 3) : compile309 b g k ∈ compileList309 b ts := by
  simp only [compileList309, List.mem_flatMap, List.mem_ofFn]
  exact ⟨g, hg, k, rfl⟩

theorem mem_wImList (b : Basis (Fin 3) F K) (δ : F) (n : ℕ) {ts : List WTyped} {g : WTyped}
    (hg : g ∈ ts) (hi : hasImW towerM g = true) (k : Fin 3) :
    wIm b δ n g k ∈ wImList b δ n ts := by
  simp only [wImList, List.mem_flatMap, List.mem_filter, List.mem_ofFn]
  exact ⟨g, ⟨hg, hi⟩, k, rfl⟩

variable (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **Item 3: the tower kept list is sound.**  Acceptance of `towerKeptGates` at (the pull-back)
`eF` gives every kept typed gate in `𝕂′` at `towerEnv309` over the gathered `𝕂` window. -/
theorem towerKept_sound (b : Basis (Fin 3) F K) (n e : ℕ) (he : e = MemoryTable.pwScaleExp K)
    (eF : Env F) (h : ∀ g ∈ towerKeptGates n e b δ, g.eval eF = 0) :
    TowerKeptHolds n δ (gatherEnv b eF) eF := by
  have hc := isCoordEnv_gather b eF
  have wsound : ∀ g : WTyped, qLinearW towerM g = true →
      (∀ k, (compile309 b g k).eval eF = 0) →
      (hasImW towerM g = true → ∀ k, (wIm b δ e g k).eval eF = 0) →
      g.eval (towerEnv309 δ towerM (gatherEnv b eF) eF) = 0 := fun g hl hre him =>
    (gateW_iff b δ e he hc g hl).mp ⟨hre, him⟩
  have m0 : ∀ g, g ∈ finalBaseTransitionGates n → g ∈ towerKeptGates n e b δ := by
    intro g hg
    simp only [towerKeptGates, List.mem_append]
    tauto
  have m1 : ∀ g, g ∈ towerCoreRe b δ e → g ∈ towerKeptGates n e b δ := by
    intro g hg
    simp only [towerKeptGates, List.mem_append]
    tauto
  have m2 : ∀ g, g ∈ towerCoreIm b δ e → g ∈ towerKeptGates n e b δ := by
    intro g hg
    simp only [towerKeptGates, List.mem_append]
    tauto
  have m3 : ∀ g, g ∈ correctedAux309 b → g ∈ towerKeptGates n e b δ := by
    intro g hg
    simp only [towerKeptGates, List.mem_append]
    tauto
  have m4 : ∀ g, g ∈ wImList b δ e ((List.finRange 3).map auxTarget) → g ∈ towerKeptGates n e b δ := by
    intro g hg
    simp only [towerKeptGates, List.mem_append]
    tauto
  have m5 : ∀ g, g ∈ compileList309 b endpoint2Q7 → g ∈ towerKeptGates n e b δ := by
    intro g hg
    simp only [towerKeptGates, List.mem_append]
    tauto
  have m6 : ∀ g, g ∈ wImList b δ e endpoint2Q7 → g ∈ towerKeptGates n e b δ := by
    intro g hg
    simp only [towerKeptGates, List.mem_append]
    tauto
  have m7 : ∀ g, g ∈ compileList309 b endpoint4_309 → g ∈ towerKeptGates n e b δ := by
    intro g hg
    simp only [towerKeptGates, List.mem_append]
    tauto
  have m8 : ∀ g, g ∈ wImList b δ e endpoint4_309 → g ∈ towerKeptGates n e b δ := by
    intro g hg
    simp only [towerKeptGates, List.mem_append]
    tauto
  have m9 : ∀ g, g ∈ finalEndpointEqualityChecks → g ∈ towerKeptGates n e b δ := by
    intro g hg
    simp only [towerKeptGates, List.mem_append]
    tauto
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg; exact h g (m0 g hg)
  · intro i hi
    have hre : ∀ k, (coreRe b δ e towerM i k).eval eF = 0 := fun k =>
      h _ (m1 _ (by
        simp only [towerCoreRe, List.mem_flatMap, List.mem_ofFn]
        exact ⟨i, hi, k, rfl⟩))
    have him : i ∈ coreImIds towerM → ∀ k, (coreIm b δ e towerM i k).eval eF = 0 := fun hm k =>
      h _ (m2 _ (by
        simp only [towerCoreIm, List.mem_flatMap, List.mem_ofFn]
        exact ⟨i, hm, k, rfl⟩))
    by_cases hs : specialCore i = true
    · have := (specialGate_iff b δ e he hc i hs).mp ⟨hre, fun h75 k => him (by
        simp only [coreImIds, List.mem_filter]
        exact ⟨hi, by simp [h75]⟩) k⟩
      simpa [coreTarget, hs, towerHolds] using this
    · have hs' : specialCore i = false := by simpa using hs
      have := (coreGate_iff b δ towerM e he hc i hs').mp ⟨hre, fun hI => him (by
        simp only [coreImIds, List.mem_filter]
        exact ⟨hi, by simp [hs', hI]⟩)⟩
      simpa [coreTarget, hs', towerHolds, WTyped.eval, towerEnv309] using this
  · intro j
    have hg : auxTarget j ∈ (List.finRange 3).map auxTarget :=
      List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
    refine wsound _ (towerWGates_qLinear _ (by simp [towerWGates, hg])) (fun k => ?_)
      (fun hI k => ?_)
    · rw [← auxRe_eq]
      exact h _ (m3 _ (by
        simp only [correctedAux309, List.mem_flatten, List.mem_ofFn]
        exact ⟨_, ⟨j, rfl⟩, List.mem_ofFn.mpr ⟨k, rfl⟩⟩))
    · exact h _ (m4 _ (mem_wImList b δ e hg hI k))
  · intro g hg
    refine wsound g (towerWGates_qLinear _ (by
      simp only [towerWGates, List.mem_append]; exact Or.inl (Or.inr (endpoint2Q7_sub g hg))))
      (fun k => h _ (m5 _ (mem_compileList309 b hg k)))
      (fun hI k => h _ (m6 _ (mem_wImList b δ e hg hI k)))
  · intro g hg
    refine wsound g (towerWGates_qLinear _ (by
      simp only [towerWGates, List.mem_append]; exact Or.inr hg))
      (fun k => h _ (m7 _ (mem_compileList309 b hg k)))
      (fun hI k => h _ (m8 _ (mem_wImList b δ e hg hI k)))
  · intro g hg; exact h g (m9 g hg)

end Sound

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
