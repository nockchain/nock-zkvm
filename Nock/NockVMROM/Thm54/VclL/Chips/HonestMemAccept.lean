/-
  Nock/NockVMROM/Thm54/VclL/Chips/HonestMemAccept.lean

  **The `ok`-gated chips accept the honest trace.**

  `cellOk_sat` / `pathOk_sat`: the cell / path chip at `ok = true` accepts the interpolated honest trace
  `honestQ … (cellCol …)` / `honestQ … (pathCol …)` (at the chip's own width index, through `Fin.cast`) given
  the row facts (`CellBaseFacts` + `CellMixedFacts`, `PathBaseFacts` + `PathMixedFacts` at every row), the
  adjacency / injectivity of the nodes and the challenge relation `ChalsOK`.  Glues
  `cellChipOk_sat_of_rows`  with `cell_base_gates_hold` / `cell_mixed_gates_hold` (1846/1847) and
  the path twins (1848).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemFill
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemBridge
import Nock.NockVMROM.Thm54.VclL.Chips.ChipV

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
open Module
open scoped Polynomial

noncomputable section

theorem envOfTrace_castW {F : Type} [Field F] {w w' : ℕ} (hw : w' = w) (P : Fin w → F[X]) (ω x : F)
    (c p : ℕ → F) :
    Reify.envOfTrace (fun j : Fin w' => P (Fin.cast hw j)) ω x c p = Reify.envOfTrace P ω x c p := by
  subst hw; rfl

section Accept
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- **The `ok`-gated cell chip accepts the honest trace** of `vals`. -/
theorem cellOk_sat (vals : Fin n → CellVals F (Quad (algebraMap F K δF)))
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ z : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11)
    (hz : Quad.mk _ (chals 2) (chals 3) = z)
    (hb : ∀ i, CellBaseFacts vals i) (hf : ∀ i, CellMixedFacts δF pubs γ ρ z vals i) :
    RAP.SatisfiesWithPreprocessing (cellChipOk δF b hn nodes orbit chals pubs true)
      (fun j => honestQ hn nodes (cellCol δF b vals) 225
        (Fin.cast (cellChipOk_w δF b hn nodes orbit chals pubs true) j)) := by
  have hw := cellChipOk_w δF b hn nodes orbit chals pubs true
  refine cellChipOk_sat_of_rows δF b hn nodes orbit chals pubs _ ?_ ?_ ?_ ?_
  · exact honestQ_zero hn nodes _ (by norm_num)
  · exact honestQ_one hn nodes _ (by norm_num)
  · intro i g hg
    rw [envOfTrace_castW hw]
    exact cell_base_gates_hold δF b hn nodes orbit.ω _ _ vals hinj hadj i (hb i) g hg
  · intro i g hg
    have e := envOfTrace_castW hw (honestCellQ δF b hn nodes vals) orbit.ω (nodes i)
      (slotVal b 129 chals) (slotVal b 129 pubs)
    simp only [e]
    exact cell_mixed_gates_hold δF b hn nodes orbit.ω chals pubs vals hinj hadj i (hb i) γ ρ z hok hz
      (hf i) g hg

/-- **The `ok`-gated path chip accepts the honest trace** of `vals`. -/
theorem pathOk_sat (vals : Fin n → PathVals F (Quad (algebraMap F K δF)))
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11)
    (hb : ∀ i, PathBaseFacts vals i) (hf : ∀ i, PathMixedFacts δF pubs γ ρ vals i) :
    RAP.SatisfiesWithPreprocessing (pathChipOk δF b hn nodes orbit chals pubs true)
      (fun j => honestQ hn nodes (pathCol δF b vals) 112
        (Fin.cast (pathChipOk_w δF b hn nodes orbit chals pubs true) j)) := by
  have hw := pathChipOk_w δF b hn nodes orbit chals pubs true
  refine pathChipOk_sat_of_rows δF b hn nodes orbit chals pubs _ ?_ ?_ ?_ ?_
  · exact honestQ_zero hn nodes _ (by norm_num)
  · exact honestQ_one hn nodes _ (by norm_num)
  · intro i g hg
    rw [envOfTrace_castW hw]
    exact path_base_gates_hold δF b hn nodes orbit.ω _ _ vals hinj hadj i (hb i) g hg
  · intro i g hg
    have e := envOfTrace_castW hw (honestPathQ δF b hn nodes vals) orbit.ω (nodes i)
      (slotVal b 16 chals) (slotVal b 16 pubs)
    simp only [e]
    exact path_mixed_gates_hold δF b hn nodes orbit.ω chals pubs vals hinj hadj i (hb i) γ ρ hok
      (hf i) g hg

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
