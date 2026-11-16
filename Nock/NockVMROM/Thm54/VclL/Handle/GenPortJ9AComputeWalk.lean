/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AComputeWalk.lean

-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ACompute

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeWalk

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (invPermX9 colX9)
open Nock.V1J9A.GenCompX9

/-- **Walk columns = `trX9`**: if the walk functions `ln cnt acc` of `trX9` are the `K3.toK` of the executable walk
values `walkVals9` at BFS rows `j + 1`, then every walk twin column of row `j` agrees (the inverse column
`(cnt - ln)⁻¹` is then forced by `hinv`). -/
theorem compTable9_eq_trX9_walk
    [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
    (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (pub : ℕ → ZMod P) (χe : CoinsE) (chalV pubVal : ℕ → ZMod P) (ln cnt acc : ℕ → KC)
    (hln : ∀ j < W.length, ln (j + 1) =
      K3.toK ((walkVals9 H pd idOf W (χe ⟨13, by decide⟩) (χe ⟨14, by decide⟩)).getD j (0, 0, 0, 0)).1)
    (hcnt : ∀ j < W.length, cnt (j + 1) =
      K3.toK ((walkVals9 H pd idOf W (χe ⟨13, by decide⟩) (χe ⟨14, by decide⟩)).getD j (0, 0, 0, 0)).2.1)
    (hacc : ∀ j < W.length, acc (j + 1) =
      K3.toK ((walkVals9 H pd idOf W (χe ⟨13, by decide⟩) (χe ⟨14, by decide⟩)).getD j (0, 0, 0, 0)).2.2.1)
    (hinv : ∀ j < W.length,
      ((walkVals9 H pd idOf W (χe ⟨13, by decide⟩) (χe ⟨14, by decide⟩)).getD j (0, 0, 0, 0)).2.2.2 =
        (((walkVals9 H pd idOf W (χe ⟨13, by decide⟩) (χe ⟨14, by decide⟩)).getD j (0, 0, 0, 0)).2.1 -
          ((walkVals9 H pd idOf W (χe ⟨13, by decide⟩) (χe ⟨14, by decide⟩)).getD j (0, 0, 0, 0)).1)⁻¹)
    {j : ℕ} (hj : j < W.length) {d : ℕ} (hd : d < 137)
    (hr : 111 ≤ invPermX9 d ∧ invPermX9 d < 123) :
    ((compTable9 H pd idOf W pub χe).getD j #[]).getD d 0 =
      Nock.NockVMROM.Thm54.VclL.HonestTraceX9.trX9 powerBasis3 deltaF H pd idOf W chalV pubVal ln cnt acc j
        (invPermX9 d) := by
  rw [GenPortJ9ACompute.compTable9_getD H pd idOf W pub χe hj hd]
  set c := invPermX9 d with hc
  obtain ⟨h1, h2⟩ := hr
  unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX9.trX9
  rw [if_neg (by omega), if_neg (by omega), if_pos h2]
  simp only [compColD9, if_neg (show ¬ (c < 69 ∨ 123 ≤ c) by omega), if_neg (show ¬ c < 93 by omega),
    if_neg (show ¬ c < 111 by omega)]
  unfold Nock.NockVMROM.Thm54.VclL.HonestTraceX.cNA
  rw [dif_pos (show (c - 111) % 3 < 3 by omega)]
  have hw : (c - 111) / 3 = 0 ∨ (c - 111) / 3 = 1 ∨ (c - 111) / 3 = 2 ∨ (c - 111) / 3 = 3 := by omega
  rcases hw with hw | hw | hw | hw <;> rw [hw]
  · simp only [Nock.NockVMROM.Thm54.VclL.HonestTraceX.walkV, hln j hj, if_true]
    exact (coord_K _ _ (by omega)).symm
  · simp only [Nock.NockVMROM.Thm54.VclL.HonestTraceX.walkV, hcnt j hj]
    simp only [show (1 : ℕ) ≠ 0 by decide, if_false, if_true]
    exact (coord_K _ _ (by omega)).symm
  · simp only [Nock.NockVMROM.Thm54.VclL.HonestTraceX.walkV, hacc j hj]
    simp only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, if_false, if_true]
    exact (coord_K _ _ (by omega)).symm
  · simp only [Nock.NockVMROM.Thm54.VclL.HonestTraceX.walkV, hcnt j hj, hln j hj]
    simp only [show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, if_false]
    rw [hinv j hj, ← K3.toK_sub, ← K3.toK_inv]
    exact (coord_K _ _ (by omega)).symm

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeWalk

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeWalk.compTable9_eq_trX9_walk
