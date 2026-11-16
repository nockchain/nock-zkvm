/-
  Nock/RedTeam/Batch1964Thm54VclCompletenessChosen.lean

  **The three MM0 orphan lemmas discharged at the capstone.**

  `Ksz`/`αs` are fixed to `0`.
-/
import Nock.RedTeam.Batch1955Thm54VclCompletenessOfRun
import Nock.NockVMROM.Thm54.VclL.Compute.TowerChosen

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1964

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Compute.TowerChosen
open Nock.RedTeam.Batch1880 Nock.RedTeam.Batch1882 Nock.RedTeam.Batch1938 Nock.RedTeam.Batch1947
open Nock.RedTeam.Batch1955

noncomputable section

section Chosen
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] [CharP K p]

theorem hq_ne_two (hq : 2 ^ 63 < p) : p ≠ 2 := by
  have : 2 ≤ 2 ^ 63 := by norm_num
  omega

/-- The chosen base non-square (needs only `2^63 < p`). -/
def δq (hq : 2 ^ 63 < p) : ZMod p := chosenδ p (hq_ne_two hq)

theorem δq_nonsquare (hq : 2 ^ 63 < p) (hK3 : Module.finrank (ZMod p) K = 3) :
    ¬ IsSquare (algebraMap (ZMod p) K (δq hq)) :=
  chosenδ_nonsquare_K p (hq_ne_two hq) hK3

theorem ringChar_zmod (p : ℕ) [Fact p.Prime] : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p

theorem ringChar_K : ringChar K = p := ringChar.eq K p

section Heights
variable (δF : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δF))] {fuel : ℕ} {subject formula result : Noun}
  (hrun : Nock.evalN fuel subject formula = some result)
  (hbound : RunBoundedBy (ringChar (ZMod p)) fuel subject formula)

/-- Chosen compute / cell / path orbit heights from the run. -/
def hCr : ℕ := heightOf (nRows (runTree (K := K) δF hrun hbound))
def hTr : ℕ := heightOf (cellLen (K := K) δF (runTree (K := K) δF hrun hbound))
def hPr : ℕ := heightOf (pathLen (K := K) δF (runTree (K := K) δF hrun hbound))

theorem hF_split (hF : 3 * 2 ^ (max (hCr (K := K) δF hrun hbound)
      (max (hTr (K := K) δF hrun hbound) (hPr (K := K) δF hrun hbound))) ∣ p - 1) :
    3 * 2 ^ hCr (K := K) δF hrun hbound ∣ Fintype.card (ZMod p) - 1 ∧
    3 * 2 ^ hTr (K := K) δF hrun hbound ∣ Fintype.card (ZMod p) - 1 ∧
    3 * 2 ^ hPr (K := K) δF hrun hbound ∣ Fintype.card (ZMod p) - 1 := by
  rw [ZMod.card]; exact orbit_dvd_split hF

end Heights
end Chosen

section Capstone
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] [CharP K p]

open Classical in
/-- **`vcl_completeness_of_run` with the three MM0 orphans discharged.**  Hypotheses: exactly the PROPOSED
binder list (run, bound, `finrank = 3`, `2^63 < p`, `hF`, `hrowsC`, `hmemC`, `hmemP`, `hleaf`, `haxis`).
The base non-square `δ`, its `Fact`, the three orbit heights, `hFC/hFT/hFP`, `hC1/hT1/hP1` and
`hsize/hsizeT/hsizeP` are all produced inside. -/
theorem vcl_completeness_of_run_chosen {fuel : ℕ} {subject formula result : Noun}
    (hq : 2 ^ 63 < p) (hK3 : Module.finrank (ZMod p) K = 3)
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy p fuel subject formula) :
    haveI : Fact (¬ IsSquare (algebraMap (ZMod p) K (δq hq))) := ⟨δq_nonsquare hq hK3⟩
    have hb : RunBoundedBy (ringChar (ZMod p)) fuel subject formula := by rw [ringChar_zmod]; exact hbound
    ∀ (hF : 3 * 2 ^ (max (hCr (K := K) (δq hq) hrun hb)
        (max (hTr (K := K) (δq hq) hrun hb) (hPr (K := K) (δq hq) hrun hb))) ∣ p - 1)
      (hrowsC : 3 * nRows (runTree (K := K) (δq hq) hrun hb) < p)
      (hmemC : cellLen (K := K) (δq hq) (runTree (K := K) (δq hq) hrun hb) + 1 < p)
      (hmemP : pathLen (K := K) (δq hq) (runTree (K := K) (δq hq) hrun hb) + 1 < p)
      (hleaf : programLeafBound (airReorder (runTree (K := K) (δq hq) hrun hb)) ≤ 2 ^ 110)
      (haxis : programAxisBound (airReorder (runTree (K := K) (δq hq) hrun hb)) < 2 ^ 63),
    let hC := hCr (K := K) (δq hq) hrun hb
    let hT := hTr (K := K) (δq hq) hrun hb
    let hP := hPr (K := K) (δq hq) hrun hb
    let HC := honestVCLJ_of_run (K := K) (δq hq) hT hP hC hrun hb 0 0 hK3
      (by rw [ringChar_zmod]; have : 2 ≤ 2 ^ 63 := by norm_num
          omega)
      (one_le_heightOf _) (one_le_heightOf _) (one_le_heightOf _)
      (hF_split (K := K) (δq hq) hrun hb hF).1 (hF_split (K := K) (δq hq) hrun hb hF).2.1
      (hF_split (K := K) (δq hq) hrun hb hF).2.2
      (le_two_pow_heightOf _) (by rw [ringChar_K]; exact hrowsC)
      (le_two_pow_heightOf _) (le_two_pow_heightOf _)
    let hmemRows := memRows_of_run (K := K) (δq hq) hT hP hC hrun hb 0 hK3
      (one_le_heightOf _) (one_le_heightOf _) (one_le_heightOf _)
      (hF_split (K := K) (δq hq) hrun hb hF).1 (hF_split (K := K) (δq hq) hrun hb hF).2.1
      (hF_split (K := K) (δq hq) hrun hb hF).2.2
      (by rw [ringChar_zmod]; exact hmemC) (by rw [ringChar_zmod]; exact hmemP)
    HC.V.claim = ⟨subject, formula, result⟩ ∧ HC.t = runTree (K := K) (δq hq) hrun hb ∧
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        ∃ s ∈ (CFv (K := K) (δq hq) hT hP hC).honestBad HC.toHonestVCLT ++
            (MFv (K := K) (δq hq) hT hP hC).honestBad
              (jointMem (δq hq) HC.toHonestVCLT (jointMemFacts_of HC
                (GeneratedField.primeFieldElems_zmod p) (by rw [ringChar_zmod]; exact hq)
                hleaf hmemRows haxis)),
          s.mem ((CFv (K := K) (δq hq) hT hP hC).honestQ HC.toHonestVCLT χ,
            (MFv (K := K) (δq hq) hT hP hC).honestQ
              (jointMem (δq hq) HC.toHonestVCLT (jointMemFacts_of HC
                (GeneratedField.primeFieldElems_zmod p) (by rw [ringChar_zmod]; exact hq)
                hleaf hmemRows haxis)) χ) χ).card : ℚ) /
        Fintype.card (Coins frameVCL K) ≤
      epsilonOf ((CFv (K := K) (δq hq) hT hP hC).honestBad HC.toHonestVCLT ++
        (MFv (K := K) (δq hq) hT hP hC).honestBad
          (jointMem (δq hq) HC.toHonestVCLT (jointMemFacts_of HC
            (GeneratedField.primeFieldElems_zmod p) (by rw [ringChar_zmod]; exact hq)
            hleaf hmemRows haxis))) := by
  intro _ hF hrowsC hmemC hmemP hleaf haxis hC hT hP HC hmemRows
  haveI : Fact (¬ IsSquare (algebraMap (ZMod p) K (δq hq))) := ⟨δq_nonsquare hq hK3⟩
  have hF' := GeneratedField.primeFieldElems_zmod p
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [ringChar_zmod]; exact hq
  refine ⟨rfl, rfl, ?_⟩
  convert vcl_completeness' (δq hq) hT hP hC HC hF' hq' hleaf hmemRows haxis using 3
  congr 1
  ext χ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end Capstone

/-! ## Negative control: the chooser at `h := 0` fails `hC1`, and is tight below -/

/-- NC: the choice `h := 0` violates `1 ≤ h` (the `hC1/hT1/hP1` shape) although it would satisfy
`rows ≤ 2^h` for `rows = 1`; so `max 1 _` is needed, `clog` alone is not enough. -/
theorem chooser_zero_fails : ¬ (1 ≤ Nat.clog 2 1) ∧ ¬ (1 ≤ (0 : ℕ)) ∧ 1 ≤ heightOf 1 := by
  refine ⟨by decide, by decide, one_le_heightOf 1⟩

/-- NC: the chooser is tight (`rows = 5` needs height `3`; height `2` fails `rows ≤ 2^h`). -/
theorem chooser_tight : heightOf 5 = 3 ∧ ¬ (5 ≤ 2 ^ 2) := by
  refine ⟨by decide, by decide⟩

/-- NC (base non-square): at `p = 7`, `δ = 1` is a square, so the nonsquare premise discriminates. -/
theorem delta_one_square_mod7 : IsSquare (1 : ZMod 7) := ⟨1, by decide⟩

theorem delta_three_nonsquare_mod7 : ¬ IsSquare (3 : ZMod 7) := by decide

/-- NC (`hF` split): `3·2^2 ∣ 12` but `3·2^3 ∤ 12`; the split at heights `(2,1,1)` is exactly `3·2^2 ∣ 12`. -/
theorem hF_split_nc : (3 * 2 ^ (max 2 (max 1 1)) ∣ 12) ∧ ¬ (3 * 2 ^ 3 ∣ 12) := by decide

end

end Nock.RedTeam.Batch1964

#print axioms Nock.RedTeam.Batch1964.vcl_completeness_of_run_chosen
#print axioms Nock.RedTeam.Batch1964.hF_split
#print axioms Nock.RedTeam.Batch1964.chooser_zero_fails
#print axioms Nock.RedTeam.Batch1964.chooser_tight
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerChosen.orbit_dvd_split
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerChosen.le_two_pow_heightOf
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerChosen.chosenδ_nonsquare_K
