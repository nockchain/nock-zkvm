/-
  Nock/V1J8/MemJAW.lean

  **The J chip and the atom walk, executably (S5).**

  * `checkJ8chip_iff`: `SatisfiesWithPreprocessing (jetChipJ8 …) P ↔ checkJchip T = true` (present case; the 18
    verifier-fixed columns `prepJ lay` = `jetPre lay j`, `j < 18`).
  * `checkAW_iff`: `SatisfiesWithPreprocessing (walkChipHQK … krootsV …) P ↔ checkAW kr T = true` (present case;
    masks `isFirst`, `isLast`, `isRoot`).
  * **The dispatch** (present or absent, verbatim `JGenJ8.JChipOK` / `AcceptsJ8V.AWChipOK`):
    `checkJOK_iff : JChipOK … ↔ checkJOK T = true`, `checkAWOK_iff : AWChipOK … ↔ checkAWOK kr T = true`.  The
    node conditions (injective, `ω`-adjacent), the root-count range and the absent-case zero publics are checked
    (`nodupB`, `adjB`, `zero3`), not assumed.
-/
import Nock.V1J8.MemX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.V1J8.MemX

open Nock Nock.Reified Nock.Framework Nock.TraceGenExe Nock.Field Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (slotVal)
open Nock.Jet.ChipJ8 (jetChipJ8 jetTemplateJ8T jetTemplateJ8T_baseCols jetPre PRow)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK walkTemplateHQK walkTemplateHQK_baseCols)
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.V1J8.CompX (zero3)

/-! ## 1. Node conditions, executably -/

/-- Injective nodes. -/
def nodupB {n : ℕ} (T : TabM n) : Bool := decide (List.ofFn T.nodes).Nodup

/-- `ω`-adjacent nodes (`node (i+1) = node i · ω`). -/
def adjB {n : ℕ} (T : TabM n) : Bool :=
  (List.finRange n).all fun i => if h : (i : ℕ) + 1 < n then decide (T.nodes ⟨i + 1, h⟩ = T.nodes i * T.ω) else true

theorem nodupB_iff {n : ℕ} (T : TabM n) : nodupB T = true ↔ Function.Injective T.nodes := by
  simp [nodupB, List.nodup_ofFn]

theorem adjB_iff {n : ℕ} (T : TabM n) :
    adjB T = true ↔ ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), T.nodes ⟨(i : ℕ) + 1, hi⟩ = T.nodes i * T.ω := by
  simp only [adjB, List.all_eq_true, List.mem_finRange, true_implies]
  constructor
  · intro h i hi
    have := h i
    rw [dif_pos hi] at this
    exact of_decide_eq_true this
  · intro h i
    split
    · exact decide_eq_true (h i ‹_›)
    · rfl

theorem adj_core {n : ℕ} (T : TabM n) {ω : ZMod p} (hω : ω = T.ω)
    (ha : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), T.nodes ⟨(i : ℕ) + 1, hi⟩ = T.nodes i * ω) :
    ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n, T.nodes ⟨i + 1, h⟩ = T.ω * T.nodes i := by
  intro i h; rw [ha i h, hω, mul_comm]

/-! ## 2. The J chip -/

/-- The J chip's 18 verifier-fixed columns from the public layout. -/
def prepJ {n : ℕ} (lay : Fin n → PRow) : List (ℕ × (Fin n → ZMod p)) :=
  (List.finRange 18).map fun j => ((j : ℕ), fun i => jetPre (F := ZMod p) lay (j : ℕ) i)

/-- **The executable J-chip check** (present case). -/
def checkJchip {n : ℕ} (T : TabM n) : Bool := checkM (jetTemplateJ8T deltaF) T

/-- **`checkJ8chip_iff`: the J chip, finitely (present case).** -/
theorem checkJ8chip_iff {n h : ℕ} (T : TabM n) (orbit : StrictOrbitDomain (ZMod p) 3 h) (lay : Fin n → PRow)
    (P : Fin (jetChipJ8 deltaF powerBasis3 T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i)) lay).rap.w → (ZMod p)[X])
    (hinj : Function.Injective T.nodes)
    (hadj : ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n, T.nodes ⟨i + 1, h⟩ = T.ω * T.nodes i)
    (hω : orbit.ω = T.ω) (hprep : T.prep = prepJ lay)
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ T.nodes (fun i => T.cols j i)) :
    RAP.SatisfiesWithPreprocessing (jetChipJ8 deltaF powerBasis3 T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i)) lay) P ↔ checkJchip T = true := by
  refine chipM_iff (jetTemplateJ8T deltaF) T _ P hinj hadj rfl hω rfl ?_ ?_ hP
  · rw [jetTemplateJ8T_baseCols]
    exact expandChip_C _ _ _ _ _ _
  · rw [hprep]
    unfold prepJ
    rw [List.map_map, List.ofFn_eq_map]
    rfl

/-- **The J chip, present or absent, executably.** -/
def checkJOK {n : ℕ} (T : TabM n) : Bool :=
  (checkJchip T && nodupB T && decide (0 < n) && adjB T) ||
  (decide (n = 0) && zero3 (T.pubs 0) && zero3 (T.pubs 1) && zero3 (T.pubs 2) && zero3 (T.pubs 3))

/-- **`checkJOK_iff`: `JChipOK` (present or absent) is exactly `checkJOK`.** -/
theorem checkJOK_iff {n h : ℕ} (T : TabM n) (orbit : StrictOrbitDomain (ZMod p) 3 h) (lay : Fin n → PRow)
    (P : Fin (jetChipJ8 deltaF powerBasis3 T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i)) lay).rap.w → (ZMod p)[X])
    (hω : orbit.ω = T.ω) (hprep : T.prep = prepJ lay)
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ T.nodes (fun i => T.cols j i)) :
    JGenJ8.JChipOK deltaF powerBasis3 T.nodes orbit (fun i => K3.toK (T.chals i)) (fun i => K3.toK (T.pubs i))
      lay P ↔ checkJOK T = true := by
  have ha : (∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), T.nodes ⟨(i : ℕ) + 1, hi⟩ = T.nodes i * orbit.ω) ↔
      adjB T = true := by rw [adjB_iff, hω]
  unfold JGenJ8.JChipOK checkJOK
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, nodupB_iff, zero3_iff_toK]
  constructor
  · rintro (⟨hs, hb, hi, hn, hadj⟩ | ⟨h0, p0, p1, p2, p3⟩)
    · exact Or.inl ⟨⟨⟨(checkJ8chip_iff T orbit lay P hi (adj_core T hω hadj) hω hprep hP).mp ⟨hs, hb⟩, hi⟩, hn⟩,
        ha.mp hadj⟩
    · exact Or.inr ⟨⟨⟨⟨h0, p0⟩, p1⟩, p2⟩, p3⟩
  · rintro (⟨⟨⟨hc, hi⟩, hn⟩, hadj⟩ | ⟨⟨⟨⟨h0, p0⟩, p1⟩, p2⟩, p3⟩)
    · have hadj' := ha.mpr hadj
      obtain ⟨hs, hb⟩ := (checkJ8chip_iff T orbit lay P hi (adj_core T hω hadj') hω hprep hP).mpr hc
      exact Or.inl ⟨hs, hb, hi, hn, hadj'⟩
    · exact Or.inr ⟨h0, p0, p1, p2, p3⟩

/-! ## 3. The atom walk -/

/-- **The executable atom-walk check** (present case; `kr` = `krootsV`). -/
def checkAW (kr : ℕ) {n : ℕ} (T : TabM n) : Bool := checkM (walkTemplateHQK deltaF kr) T

/-- **`checkAW_iff`: the atom walk chip `walkChipHQK`, finitely (present case).** -/
theorem checkAW_iff (kr : ℕ) {n h : ℕ} (T : TabM n) (hn : 0 < n) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (P : Fin (walkChipHQK deltaF kr powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i))).rap.w → (ZMod p)[X])
    (hinj : Function.Injective T.nodes)
    (hadj : ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n, T.nodes ⟨i + 1, h⟩ = T.ω * T.nodes i)
    (hω : orbit.ω = T.ω) (hprep : T.prep = prep3 n kr)
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ T.nodes (fun i => T.cols j i)) :
    RAP.SatisfiesWithPreprocessing (walkChipHQK deltaF kr powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i))) P ↔ checkAW kr T = true := by
  refine chipM_iff (walkTemplateHQK deltaF kr) T _ P hinj hadj rfl hω rfl ?_ ?_ hP
  · rw [walkTemplateHQK_baseCols]
    exact expandChip_C _ _ _ _ _ _
  · rw [hprep]
    simp only [List.ofFn_succ, List.ofFn_zero, walkChipHQK, FixedPreprocessingRAP.preprocessingColumn,
      RAP.preprocessingColumn, prep3, List.map_cons, List.map_nil]
    refine congrArg₂ _ (Prod.ext rfl ?_) (congrArg₂ _ (Prod.ext rfl ?_) (congrArg₂ _ (Prod.ext rfl ?_) rfl))
    · exact firstMask_interp _
    · exact lastMask_interp hn _
    · rfl

/-- **The atom walk, present or absent, executably.** -/
def checkAWOK (kr : ℕ) {n : ℕ} (T : TabM n) : Bool :=
  (checkAW kr T && nodupB T && adjB T && decide (1 ≤ kr) && decide (kr ≤ n) && decide (kr + n < p)) ||
  (decide (kr = 0) && zero3 (T.pubs 0) && zero3 (T.pubs 1) && zero3 (T.pubs WalkHQ.pubXQ) &&
    zero3 (T.pubs (WalkHQ.pubXQ + 1)) && zero3 (T.pubs WalkHQ.pubPQ) && zero3 (T.pubs (WalkHQ.pubPQ + 1)))

/-- **`checkAWOK_iff`: `AWChipOK` (present or absent) is exactly `checkAWOK`.** -/
theorem checkAWOK_iff (kr : ℕ) {n h : ℕ} (T : TabM n) (hn : 0 < n) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (P : Fin (walkChipHQK deltaF kr powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i))).rap.w → (ZMod p)[X])
    (hω : orbit.ω = T.ω) (hprep : T.prep = prep3 n kr)
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ T.nodes (fun i => T.cols j i)) :
    AcceptsJ8V.AWChipOK deltaF powerBasis3 kr hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i)) P ↔ checkAWOK kr T = true := by
  have ha : (∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), T.nodes ⟨(i : ℕ) + 1, hi⟩ = T.nodes i * orbit.ω) ↔
      adjB T = true := by rw [adjB_iff, hω]
  have hr : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  unfold AcceptsJ8V.AWChipOK checkAWOK
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, nodupB_iff, zero3_iff_toK, hr]
  constructor
  · rintro (⟨hs, hb, hi, hadj, h1, h2, h3⟩ | ⟨h0, p0, p1, p2, p3, p4, p5⟩)
    · exact Or.inl ⟨⟨⟨⟨⟨(checkAW_iff kr T hn orbit P hi (adj_core T hω hadj) hω hprep hP).mp ⟨hs, hb⟩, hi⟩,
        ha.mp hadj⟩, h1⟩, h2⟩, h3⟩
    · exact Or.inr ⟨⟨⟨⟨⟨⟨h0, p0⟩, p1⟩, p2⟩, p3⟩, p4⟩, p5⟩
  · rintro (⟨⟨⟨⟨⟨hc, hi⟩, hadj⟩, h1⟩, h2⟩, h3⟩ | ⟨⟨⟨⟨⟨⟨h0, p0⟩, p1⟩, p2⟩, p3⟩, p4⟩, p5⟩)
    · have hadj' := ha.mpr hadj
      obtain ⟨hs, hb⟩ := (checkAW_iff kr T hn orbit P hi (adj_core T hω hadj') hω hprep hP).mpr hc
      exact Or.inl ⟨hs, hb, hi, hadj', h1, h2, h3⟩
    · exact Or.inr ⟨h0, p0, p1, p2, p3, p4, p5⟩

end Nock.V1J8.MemX

#print axioms Nock.V1J8.MemX.checkJ8chip_iff
#print axioms Nock.V1J8.MemX.checkJOK_iff
#print axioms Nock.V1J8.MemX.checkAW_iff
#print axioms Nock.V1J8.MemX.checkAWOK_iff
