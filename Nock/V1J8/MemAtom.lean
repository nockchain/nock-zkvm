/-
  Nock/V1J8/MemAtom.lean

  **`checkAtomHQL_iff` and `checkAtomHQ_iff`, the executable checks of the
  J-8 atom chips `atomChipHQL` (width `349`) and `atomChipHQ` at their source gates (S4).**  Fixed columns `isFirst`, `isLast` at `0`, `1`.
-/
import Nock.V1J8.MemX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.V1J8.MemX

open Nock Nock.Reified Nock.Framework Nock.TraceGenExe Nock.Field Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (slotVal)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL atomTemplateHQL atomTemplateHQL_baseCols)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (atomChipHQ atomTemplateHQ atomTemplateHQ_baseCols)
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)

/-- **The executable atom-HQL check.** -/
def checkAtomHQL {n : ℕ} (T : TabM n) : Bool := checkM (atomTemplateHQL deltaF) T

/-- **The executable atom-HQ check.** -/
def checkAtomHQ {n : ℕ} (T : TabM n) : Bool := checkM (atomTemplateHQ deltaF) T

/-- **`checkAtomHQL_iff`: the J-8 atom chip with `gL`, finitely.** -/
theorem checkAtomHQL_iff {n h : ℕ} (T : TabM n) (hn : 0 < n) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (P : Fin (atomChipHQL deltaF powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i))).rap.w → (ZMod p)[X])
    (hinj : Function.Injective T.nodes)
    (hadj : ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n, T.nodes ⟨i + 1, h⟩ = T.ω * T.nodes i)
    (hω : orbit.ω = T.ω) (hprep : T.prep = prep2 n)
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ T.nodes (fun i => T.cols j i)) :
    RAP.SatisfiesWithPreprocessing (atomChipHQL deltaF powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i))) P ↔ checkAtomHQL T = true := by
  refine chipM_iff (atomTemplateHQL deltaF) T _ P hinj hadj rfl hω rfl ?_ ?_ hP
  · rw [atomTemplateHQL_baseCols]
    exact expandChip_C _ _ _ _ _ _
  · rw [hprep]
    simp only [List.ofFn_succ, List.ofFn_zero, atomChipHQL, FixedPreprocessingRAP.preprocessingColumn,
      RAP.preprocessingColumn, prep2, List.map_cons, List.map_nil]
    refine congrArg₂ _ (Prod.ext rfl ?_) (congrArg₂ _ (Prod.ext rfl ?_) rfl)
    · exact firstMask_interp _
    · exact lastMask_interp hn _

/-- **`checkAtomHQ_iff`: the J-8 atom chip (`hsatA` / `hbindA`), finitely.** -/
theorem checkAtomHQ_iff {n h : ℕ} (T : TabM n) (hn : 0 < n) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (P : Fin (atomChipHQ deltaF powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i))).rap.w → (ZMod p)[X])
    (hinj : Function.Injective T.nodes)
    (hadj : ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n, T.nodes ⟨i + 1, h⟩ = T.ω * T.nodes i)
    (hω : orbit.ω = T.ω) (hprep : T.prep = prep2 n)
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ T.nodes (fun i => T.cols j i)) :
    RAP.SatisfiesWithPreprocessing (atomChipHQ deltaF powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i))) P ↔ checkAtomHQ T = true := by
  refine chipM_iff (atomTemplateHQ deltaF) T _ P hinj hadj rfl hω rfl ?_ ?_ hP
  · rw [atomTemplateHQ_baseCols]
    exact expandChip_C _ _ _ _ _ _
  · rw [hprep]
    simp only [List.ofFn_succ, List.ofFn_zero, atomChipHQ, FixedPreprocessingRAP.preprocessingColumn,
      RAP.preprocessingColumn, prep2, List.map_cons, List.map_nil]
    refine congrArg₂ _ (Prod.ext rfl ?_) (congrArg₂ _ (Prod.ext rfl ?_) rfl)
    · exact firstMask_interp _
    · exact lastMask_interp hn _

end Nock.V1J8.MemX

#print axioms Nock.V1J8.MemX.checkAtomHQL_iff
#print axioms Nock.V1J8.MemX.checkAtomHQ_iff
