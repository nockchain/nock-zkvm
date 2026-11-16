/-
  Nock/RedTeam/Batch1927Thm54TowerHonestBad.lean

  **The honest bad-event summands of the VCL compute family.**
  Items (a) SeedGood, (b) rlc5, (c) `χ0` order, (d) poles.

  Total weight: `ε = wS/|𝕂|² + wR/|𝕂|³ + h²/|𝕂| + 5·N·|𝕂|²/|𝕂|⁴` (`epsilon_honestBadCF`).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestBadPole
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda
import Nock.NockVMROM.Thm54.TraceGen.GenGoodSeedExists

set_option autoImplicit false

namespace Nock.RedTeam.Batch1927

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

/-- NC (the `χ0`-order event discriminates): in `ZMod 7`, `2` has order `3 < 4` so it is bad for `h = 4`,
while `3` (order `6`) is not. -/
theorem nc_ordBad_discriminates :
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    (2 : ZMod 7) ∈ ordBad (K := ZMod 7) 4 ∧ (3 : ZMod 7) ∉ ordBad (K := ZMod 7) 4 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  classical
  constructor
  · simp only [ordBad, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr ⟨3, by norm_num, by norm_num, by decide⟩
  · simp only [ordBad, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_exists]
    refine ⟨by decide, ?_⟩
    rintro d ⟨h0, h4, h⟩
    interval_cases d <;> revert h <;> decide

#print axioms badSeedsT_card_le
#print axioms seedGood_of_not_mem
#print axioms mixedKernel_card_le
#print axioms rlc5Bad_card_le
#print axioms rlc5Holds_renderNode_alpha
#print axioms rlc5_of_not_mem
#print axioms ordBad_card_le
#print axioms hord_of_not_mem
#print axioms sumSeedGoodT_mem
#print axioms sumRlc5T_mem
#print axioms sumOrdT_mem
#print axioms poleSummandTr_ne
#print axioms epsilon_honestBadCF
#print axioms honestBadCF_decode
#print axioms nc_ordBad_discriminates

end Nock.RedTeam.Batch1927
