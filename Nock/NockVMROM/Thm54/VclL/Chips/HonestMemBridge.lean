/-
  Nock/NockVMROM/Thm54/VclL/Chips/HonestMemBridge.lean

  **Chip acceptance FROM row-local gate equations**
  (the converse of `RowBridge.cellChip_rowLocal` / `pathChip_rowLocal`).

  `cellChipOk_sat_of_rows` / `pathChipOk_sat_of_rows`: a trace `Q` whose two preprocessing columns are
  the endpoint masks and whose every row-`i` environment (`Reify.envOfTrace Q ω (nodes i) …`) satisfies
  the chip's base gates and mixed gates is accepted by the `ok = true` chip.  This is the interface
  the honest construction targets: it reduces `honest_accepted` to per-row gate equations at the
  environments of the interpolated honest columns (`HonestMemQ`).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.ChipV
import Nock.NockVMROM.Thm54.VclL.Chips.RowBridge

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
open Module
open scoped Polynomial

noncomputable section

section Bridge
attribute [local irreducible] Cell.baseGates Path.baseGates Cell.mixedGates Path.mixedGates

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- **Cell chip acceptance from row-local gates** (`ok = true`). -/
theorem cellChipOk_sat_of_rows
    (Q : Fin (cellChipOk δF b hn nodes orbit chals pubs true).rap.w → F[X])
    (hm0 : Q ⟨0, by rw [cellChipOk_w]; omega⟩ = firstRowMask nodes)
    (hm1 : Q ⟨1, by rw [cellChipOk_w]; omega⟩ = lastRowMask hn nodes)
    (hbase : ∀ i : Fin n, ∀ g ∈ Cell.baseGates (F := F),
      g.eval (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 129 chals) (slotVal b 129 pubs)) = 0)
    (hmixed : ∀ i : Fin n, ∀ g ∈ Cell.mixedGates δF,
      g.eval (gatherEnv b ((cellTemplate δF).col0 3)
          (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 129 chals) (slotVal b 129 pubs)))
        (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 129 chals) (slotVal b 129 pubs)) = 0) :
    RAP.SatisfiesWithPreprocessing (cellChipOk δF b hn nodes orbit chals pubs true) Q := by
  refine ⟨?_, ?_⟩
  · refine (expandChip_satisfies_iff_language (cellTemplateOk δF true) b _ _ orbit (rowNodeSet nodes) Q).mpr
      fun x hx => ?_
    obtain ⟨i, rfl⟩ : ∃ i, nodes i = x := by
      classical
      unfold rowNodeSet at hx
      simpa using hx
    refine ⟨?_, by simp [cellTemplateOk, cellTemplate], ?_, ?_⟩
    · intro g hg
      simp only [cellTemplateOk, okGates, if_true, List.append_nil] at hg
      exact hbase i g hg
    · simp [cellTemplateOk, cellTemplate]
    · intro g hg
      exact hmixed i g hg
  · intro j
    fin_cases j
    · exact hm0
    · exact hm1

/-- **Path chip acceptance from row-local gates** (`ok = true`). -/
theorem pathChipOk_sat_of_rows
    (Q : Fin (pathChipOk δF b hn nodes orbit chals pubs true).rap.w → F[X])
    (hm0 : Q ⟨0, by rw [pathChipOk_w]; omega⟩ = firstRowMask nodes)
    (hm1 : Q ⟨1, by rw [pathChipOk_w]; omega⟩ = lastRowMask hn nodes)
    (hbase : ∀ i : Fin n, ∀ g ∈ Path.baseGates (F := F),
      g.eval (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 16 chals) (slotVal b 16 pubs)) = 0)
    (hmixed : ∀ i : Fin n, ∀ g ∈ Path.mixedGates δF,
      g.eval (gatherEnv b ((pathTemplate δF).col0 3)
          (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 16 chals) (slotVal b 16 pubs)))
        (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 16 chals) (slotVal b 16 pubs)) = 0) :
    RAP.SatisfiesWithPreprocessing (pathChipOk δF b hn nodes orbit chals pubs true) Q := by
  refine ⟨?_, ?_⟩
  · refine (expandChip_satisfies_iff_language (pathTemplateOk δF true) b _ _ orbit (rowNodeSet nodes) Q).mpr
      fun x hx => ?_
    obtain ⟨i, rfl⟩ : ∃ i, nodes i = x := by
      classical
      unfold rowNodeSet at hx
      simpa using hx
    refine ⟨?_, by simp [pathTemplateOk, pathTemplate], ?_, ?_⟩
    · intro g hg
      simp only [pathTemplateOk, okGates, if_true, List.append_nil] at hg
      exact hbase i g hg
    · simp [pathTemplateOk, pathTemplate]
    · intro g hg
      exact hmixed i g hg
  · intro j
    fin_cases j
    · exact hm0
    · exact hm1

end Bridge

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
