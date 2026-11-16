/-
  Nock/V1J8/MemWalkJ8.lean

  **`checkWalkJ8_iff`, the executable check of the J-8 walk chip
  `walkChipJ8` (width `166`) at its source gates (S4).**

  `checkWalkJ8 kr T = checkM (walkTemplateJ8 deltaF kr) T` (`MemX`); fixed columns `isFirst`, `isLast`, `isRoot`
  (`i < kroots`) at `0`, `1`, `2`.
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
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8 walkTemplateJ8 walkTemplateJ8_baseCols)
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)

/-- **The executable walk-J8 check** (`kr` = the root count `kroots`). -/
def checkWalkJ8 (kr : ℕ) {n : ℕ} (T : TabM n) : Bool := checkM (walkTemplateJ8 deltaF kr) T

/-- **`checkWalkJ8_iff`: the J-8 walk chip, finitely.** -/
theorem checkWalkJ8_iff (kr : ℕ) {n h : ℕ} (T : TabM n) (hn : 0 < n) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (P : Fin (walkChipJ8 deltaF kr powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i))).rap.w → (ZMod p)[X])
    (hinj : Function.Injective T.nodes)
    (hadj : ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n, T.nodes ⟨i + 1, h⟩ = T.ω * T.nodes i)
    (hω : orbit.ω = T.ω) (hprep : T.prep = prep3 n kr)
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ T.nodes (fun i => T.cols j i)) :
    RAP.SatisfiesWithPreprocessing (walkChipJ8 deltaF kr powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i))) P ↔ checkWalkJ8 kr T = true := by
  refine chipM_iff (walkTemplateJ8 deltaF kr) T _ P hinj hadj rfl hω rfl ?_ ?_ hP
  · rw [walkTemplateJ8_baseCols]
    exact expandChip_C _ _ _ _ _ _
  · rw [hprep]
    simp only [List.ofFn_succ, List.ofFn_zero, walkChipJ8, FixedPreprocessingRAP.preprocessingColumn,
      RAP.preprocessingColumn, prep3, List.map_cons, List.map_nil]
    refine congrArg₂ _ (Prod.ext rfl ?_) (congrArg₂ _ (Prod.ext rfl ?_) (congrArg₂ _ (Prod.ext rfl ?_) rfl))
    · exact firstMask_interp _
    · exact lastMask_interp hn _
    · rfl

end Nock.V1J8.MemX

#print axioms Nock.V1J8.MemX.checkWalkJ8_iff
