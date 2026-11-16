/-
  Nock/V1J8/MemCellKW.lean

  **`checkCellKW_iff`, the executable check of the J-8 cell chip
  `cellChipHQKW` (width `242`) at its source gates (S4).**

  `checkCellKW T = checkM (cellTemplateHQKW deltaF) T` (`MemX`); the chip at the power basis, `δ = 7`, the table's
  nodes / coins / publics (`K3`, mapped by `K3.toK`), is satisfied with its two masks by the row interpolants iff
  `checkCellKW T = true` (`T.prep` = the masks `isFirst`, `isLast` at columns `0`, `1`).
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
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellTemplateHQKW cellTemplateHQKW_baseCols)
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)

/-- **The executable cell-KW check.** -/
def checkCellKW {n : ℕ} (T : TabM n) : Bool := checkM (cellTemplateHQKW deltaF) T

/-- **`checkCellKW_iff`: the J-8 cell chip, finitely.** -/
theorem checkCellKW_iff {n h : ℕ} (T : TabM n) (hn : 0 < n) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (P : Fin (cellChipHQKW deltaF powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i))).rap.w → (ZMod p)[X])
    (hinj : Function.Injective T.nodes)
    (hadj : ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n, T.nodes ⟨i + 1, h⟩ = T.ω * T.nodes i)
    (hω : orbit.ω = T.ω) (hprep : T.prep = prep2 n)
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ T.nodes (fun i => T.cols j i)) :
    RAP.SatisfiesWithPreprocessing (cellChipHQKW deltaF powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i))) P ↔ checkCellKW T = true := by
  refine chipM_iff (cellTemplateHQKW deltaF) T _ P hinj hadj rfl hω rfl ?_ ?_ hP
  · rw [cellTemplateHQKW_baseCols]
    exact expandChip_C _ _ _ _ _ _
  · rw [hprep]
    simp only [List.ofFn_succ, List.ofFn_zero, cellChipHQKW, FixedPreprocessingRAP.preprocessingColumn,
      RAP.preprocessingColumn, prep2, List.map_cons, List.map_nil]
    refine congrArg₂ _ (Prod.ext rfl ?_) (congrArg₂ _ (Prod.ext rfl ?_) rfl)
    · exact firstMask_interp _
    · exact lastMask_interp hn _

end Nock.V1J8.MemX

#print axioms Nock.V1J8.MemX.chipM_iff
#print axioms Nock.V1J8.MemX.checkCellKW_iff
