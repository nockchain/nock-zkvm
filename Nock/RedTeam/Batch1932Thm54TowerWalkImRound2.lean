/-
  Nock/RedTeam/Batch1932Thm54TowerWalkImRound2.lean

  **The walk-accumulator Im columns `388.. 393` of `tableVCLT`
  move from round 1 to round 2.**

  `tableVCLT.colRound` (and its rfl twin
  `TowerHonestBadPole.rnd`) now put them in round 2.  Proofs adjusted (bounds only, no summand
  weakened): `tableVCLT_colRound_im` (`c < 388`), `towerM_ext_round` (`c + 2 < 483`, decide +kernel),
  `ColOkT` (`c < 388`; `entryOkT` record checks re-decided), `entryR1` record checks re-decided.
  Every soundness consumer rebuilds unchanged (`#print axioms` below).

  Compiled here:
  * `col_round_two`, `rnd_two`: `388.. 393` are round 2 of `tableVCLT` and of the pole twin `rnd`.
  * `all_coins_before_two`: every `frameVCL` coin (`χ₀.. χ₁₀`) is sampled after round `≤ 1 < 2`.
  * `staged_of_rest`: **`honest_staged`'s precondition at `388.. 393`** — a family staged on every other
    column is staged, whatever its values at `388.. 393` read (any of `χ₀.. χ₁₀`).
  * `staged_overlay`: overwriting columns `388.. 393` of a staged family by ANY coin function
    (e.g. the honest `coord (Im (acc χ))`) keeps it staged.
  * NC `nc_placement`: the family whose column `391` is `χ₀` is staged at the new placement and NOT at
    the old one (`Batch1931.oldColRound`); `old_placement_forces_im_zero` re-exports
    `Batch1931.staged_forces_im_zero` (old placement ⇒ honest staged family forces `Im = 0`).
-/
import Nock.RedTeam.Batch1931Thm54TowerStagedStop
import Nock.RedTeam.Batch1882Thm54VclStandaloneNoHrow
import Nock.RedTeam.Batch1927Thm54TowerHonestBad
import Nock.RedTeam.Batch1744Thm54VclLIOFieldQuad
import Nock.RedTeam.Batch1881Thm54TowerRowFactsAt

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Nock.RedTeam.Batch1932

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Compute Module Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame

/-- **The walk-accumulator Im columns `388.. 393` are round `2` of the tower table.** -/
theorem col_round_two (hC c : ℕ) (h1 : 388 ≤ c) (h2 : c < 394) (hw : c < (tableVCLT hC).width) :
    (tableVCLT hC).colRound ⟨c, hw⟩ = 2 := by
  show (if c < 232 then colRoundVCLE c else if c < 388 then 1 else if c = z1Col then 1 else 2) = 2
  rw [if_neg (by omega), if_neg (by omega), if_neg (by simp only [z1Col]; omega)]

/-- The pole summands' twin schedule `rnd` agrees. -/
theorem rnd_two (c : ℕ) (h1 : 388 ≤ c) (h2 : c < 394) : rnd c = 2 := by
  simp only [rnd]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by simp only [z1Col]; omega)]

/-- The FP / role-56/57 Im block `232.. 387` stays round `1`. -/
theorem col_round_one_rest (hC c : ℕ) (h1 : 232 ≤ c) (h2 : c < 388) (hw : c < (tableVCLT hC).width) :
    (tableVCLT hC).colRound ⟨c, hw⟩ = 1 :=
  tableVCLT_colRound_im hC c h1 h2 hw

/-- Every `frameVCL` coin is sampled before round 2. -/
theorem all_coins_before_two : ∀ i : Fin frameVCL.n, frameVCL.sampledAfter i < 2 := by decide

/-- **`honest_staged`'s precondition at `388.. 393`.**  A family that is staged on every column outside
`388.. 393` is staged: at `388.. 393` (round 2) the staging hypothesis fixes ALL eleven coins, so the
family may read any of `χ₀.. χ₁₀` there. -/
theorem staged_of_rest {K β : Type} (hC : ℕ) (Q : Coins frameVCL K → Fin (tableVCLT hC).width → β)
    (hrest : ∀ j : Fin (tableVCLT hC).width, ¬ (388 ≤ j.1 ∧ j.1 < 394) → ∀ χ χ' : Coins frameVCL K,
      (∀ i : Fin frameVCL.n, frameVCL.sampledAfter i < (tableVCLT hC).colRound j → χ i = χ' i) →
        Q χ j = Q χ' j) :
    StagedCols frameVCL (tableVCLT hC).colRound Q := by
  intro j χ χ' h
  by_cases hj : 388 ≤ j.1 ∧ j.1 < 394
  · have : χ = χ' := funext fun i => h i (by
      rw [show j = ⟨j.1, j.isLt⟩ from rfl, col_round_two hC j.1 hj.1 hj.2 j.isLt]
      exact all_coins_before_two i)
    rw [this]
  · exact hrest j hj χ χ' h

/-- **Overlaying `388.. 393` keeps stagedness**: replace those six columns of a staged family by any
coin function `g` (the honest `coord (Im (acc χ))` / role-59 values read `χ₀, χ₁`). -/
theorem staged_overlay {K β : Type} (hC : ℕ) (Q : Coins frameVCL K → Fin (tableVCLT hC).width → β)
    (hQ : StagedCols frameVCL (tableVCLT hC).colRound Q)
    (g : Coins frameVCL K → Fin (tableVCLT hC).width → β) :
    StagedCols frameVCL (tableVCLT hC).colRound
      (fun χ j => if 388 ≤ j.1 ∧ j.1 < 394 then g χ j else Q χ j) := by
  refine staged_of_rest hC _ fun j hj χ χ' h => ?_
  simp only [if_neg hj]
  exact hQ j χ χ' h

/-- The test family: column `391` holds the walk coin `χ₀`, every other column `0`. -/
def walkCoinFam {K : Type} [Zero K] (hC : ℕ) : Coins frameVCL K → Fin (tableVCLT hC).width → K :=
  fun χ j => if j.1 = 391 then χ ⟨0, by decide⟩ else 0

/-- **NC (placement discriminates).**  A column `391` reading the walk coin `χ₀` is staged at the new
placement and NOT at the old one (`Batch1931.oldColRound`, `388.. 393` in round 1). -/
theorem nc_placement {K : Type} [Field K] (hC : ℕ) :
    StagedCols frameVCL (tableVCLT hC).colRound (walkCoinFam (K := K) hC) ∧
      ¬ StagedCols frameVCL (Batch1931.oldColRound hC) (walkCoinFam (K := K) hC) := by
  refine ⟨staged_of_rest hC _ fun j hj χ χ' _ => ?_, fun hS => ?_⟩
  · have : j.1 ≠ 391 := fun e => hj ⟨by omega, by omega⟩
    simp [walkCoinFam, this]
  · have hw : 391 < (tableVCLT hC).width := by rw [tableVCLT_width]; norm_num
    have := hS ⟨391, hw⟩ (fun _ => 0) (Function.update (fun _ => 0) ⟨0, by decide⟩ 1) (fun i hi => by
      rw [Batch1931.col_round_one hC 391 (by norm_num) (by norm_num) hw] at hi
      have hi0 : i ≠ ⟨0, by decide⟩ := by
        rintro rfl; exact absurd hi (by decide)
      simp [Function.update_of_ne hi0])
    simp [walkCoinFam] at this

alias old_placement_forces_im_zero := Batch1931.staged_forces_im_zero

end Nock.RedTeam.Batch1932

open Nock.RedTeam.Batch1932 in
section
#print axioms col_round_two
#print axioms rnd_two
#print axioms col_round_one_rest
#print axioms all_coins_before_two
#print axioms staged_of_rest
#print axioms staged_overlay
#print axioms nc_placement
#print axioms old_placement_forces_im_zero
end

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.compSoundnessVCLT
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.rowFactsAt_compSoundnessVCLT
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.formulaRecT_ok
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.formulaRec_R1
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.imFP_costaged
#print axioms Nock.RedTeam.Batch1880.vcl_standalone_soundness
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_soundness'
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_155'
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_154'
#print axioms Nock.RedTeam.Batch1882.vcl_standalone_164'
