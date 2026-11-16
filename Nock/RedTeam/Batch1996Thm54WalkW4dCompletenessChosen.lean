/-
  Nock/RedTeam/Batch1996Thm54WalkW4dCompletenessChosen.lean

  **The walk family's completeness twin at the capstone binders**
  (twin of `Batch1964.vcl_completeness_of_run_chosen`).

  The two instances
  the walk family needs at `F = ZMod p` are DERIVED (no binder): `Fact (ringChar (ZMod p)).Prime` from
  `Fact p.Prime`, and `Algebra (ZMod (ringChar (ZMod p))) K` is `ZMod.algebra` from `CharP K p`.
-/
import Nock.RedTeam.Batch1995Thm54WalkW4dCompletenessOfRun
import Nock.RedTeam.Batch1964Thm54VclCompletenessChosen

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1996

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Compute.TowerChosen
open Nock.RedTeam.Batch1964 Nock.RedTeam.Batch1995

noncomputable section

section Inst
variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p]

/-- `ringChar (ZMod p)` is prime. -/
theorem fact_ringChar_zmod : Fact (ringChar (ZMod p)).Prime := ⟨by rw [ringChar_zmod]; exact Fact.out⟩

/-- `K` has characteristic `ringChar (ZMod p)`. -/
theorem charP_ringChar_zmod : CharP K (ringChar (ZMod p)) := by rw [ringChar_zmod]; infer_instance

/-- The walk family's `ZMod (ringChar F)`-algebra at `F = ZMod p` (Mathlib's `ZMod.algebra`). -/
abbrev algRC : Algebra (ZMod (ringChar (ZMod p))) K :=
  haveI := charP_ringChar_zmod p K
  ZMod.algebra K (ringChar (ZMod p))

end Inst

section Capstone
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] [CharP K p]

open Classical in
/-- **The walk family's completeness at the capstone binders.**  Hypotheses: exactly
`hq hK3 hrun hbound hF hrowsC hmemC hmemW hleaf haxis`. -/
theorem vcl_completenessW_of_run_chosen {fuel : ℕ} {subject formula result : Noun}
    (hq : 2 ^ 63 < p) (hK3 : Module.finrank (ZMod p) K = 3)
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy p fuel subject formula) :
    haveI : Fact (¬ IsSquare (algebraMap (ZMod p) K (δq hq))) := ⟨δq_nonsquare hq hK3⟩
    haveI : Fact (ringChar (ZMod p)).Prime := fact_ringChar_zmod p
    letI : Algebra (ZMod (ringChar (ZMod p))) K := algRC p K
    have hb : RunBoundedBy (ringChar (ZMod p)) fuel subject formula := by rw [ringChar_zmod]; exact hbound
    ∀ (hF : 3 * 2 ^ (max (hCr (K := K) (δq hq) hrun hb)
        (max (hTr (K := K) (δq hq) hrun hb) (hPr (K := K) (δq hq) hrun hb))) ∣ p - 1)
      (hrowsC : 3 * nRows (runTree (K := K) (δq hq) hrun hb) < p)
      (hmemC : cellLen (K := K) (δq hq) (runTree (K := K) (δq hq) hrun hb) + 1 < p)
      (hmemW : krW (demT (runTree (K := K) (δq hq) hrun hb)).cells (demT (runTree (K := K) (δq hq) hrun hb)).preads +
        (walkRows (demT (runTree (K := K) (δq hq) hrun hb)).cells
          (demT (runTree (K := K) (δq hq) hrun hb)).preads).length < p)
      (hleaf : programLeafBound (airReorder (runTree (K := K) (δq hq) hrun hb)) ≤ 2 ^ 110)
      (haxis : programAxisBound (airReorder (runTree (K := K) (δq hq) hrun hb)) < 2 ^ 63),
    let hC := hCr (K := K) (δq hq) hrun hb
    let hT := hTr (K := K) (δq hq) hrun hb
    let hP := hPr (K := K) (δq hq) hrun hb
    let HJ := honestVCLJW_of_run (K := K) (δq hq) hT hP hC hrun hb 0 0 hK3
      (by rw [ringChar_zmod]; have : 2 ≤ 2 ^ 63 := by norm_num
          omega)
      (one_le_heightOf _) (one_le_heightOf _) (one_le_heightOf _)
      (hF_split (K := K) (δq hq) hrun hb hF).1 (hF_split (K := K) (δq hq) hrun hb hF).2.1
      (hF_split (K := K) (δq hq) hrun hb hF).2.2
      (le_two_pow_heightOf _) (by rw [ringChar_K]; exact hrowsC)
      (le_two_pow_heightOf _) (le_two_pow_heightOf _)
    let hmemRows := memRowsW_of_run (K := K) (δq hq) hT hP hC hrun hb 0 hK3
      (one_le_heightOf _) (one_le_heightOf _) (one_le_heightOf _)
      (hF_split (K := K) (δq hq) hrun hb hF).1 (hF_split (K := K) (δq hq) hrun hb hF).2.1
      (hF_split (K := K) (δq hq) hrun hb hF).2.2
      (by rw [ringChar_zmod]; exact hmemC) (by rw [ringChar_zmod]; exact hmemW)
    let hkp := kpW_of_run (K := K) (δq hq) hT hP hC hrun hb 0 hK3
      (one_le_heightOf _) (one_le_heightOf _) (one_le_heightOf _)
      (hF_split (K := K) (δq hq) hrun hb hF).1 (hF_split (K := K) (δq hq) hrun hb hF).2.1
      (hF_split (K := K) (δq hq) hrun hb hF).2.2 (by rw [ringChar_zmod]; exact hmemW)
    let hF' := GeneratedField.primeFieldElems_zmod p
    let hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [ringChar_zmod]; exact hq
    HJ.V.claim = ⟨subject, formula, result⟩ ∧ HJ.t = runTree (K := K) (δq hq) hrun hb ∧
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        ∃ s ∈ (CFvW4 (K := K) (δq hq) hT hP hC).honestBad HJ.toHonestVCLT ++
            (MFvW4 (K := K) (δq hq) hT hP hC (krT (δq hq) HJ.t)).honestBad
              (jointMemW HJ hF' hq' hleaf hmemRows haxis hkp),
          s.mem ((CFvW4 (K := K) (δq hq) hT hP hC).honestQ HJ.toHonestVCLT χ,
            (MFvW4 (K := K) (δq hq) hT hP hC (krT (δq hq) HJ.t)).honestQ
              (jointMemW HJ hF' hq' hleaf hmemRows haxis hkp) χ) χ).card : ℚ) /
        Fintype.card (Coins frameVCL K) ≤
      epsilonOf ((CFvW4 (K := K) (δq hq) hT hP hC).honestBad HJ.toHonestVCLT ++
        (MFvW4 (K := K) (δq hq) hT hP hC (krT (δq hq) HJ.t)).honestBad
          (jointMemW HJ hF' hq' hleaf hmemRows haxis hkp)) := by
  intro hb hF hrowsC hmemC hmemW hleaf haxis hC hT hP HJ hmemRows hkp hF' hq'
  haveI : Fact (¬ IsSquare (algebraMap (ZMod p) K (δq hq))) := ⟨δq_nonsquare hq hK3⟩
  haveI : Fact (ringChar (ZMod p)).Prime := fact_ringChar_zmod p
  letI : Algebra (ZMod (ringChar (ZMod p))) K := algRC p K
  exact ⟨rfl, rfl, vcl_completenessW' (δq hq) hT hP hC HJ hF' hq' hleaf hmemRows haxis hkp⟩

end Capstone

end

end Nock.RedTeam.Batch1996

#print axioms Nock.RedTeam.Batch1996.vcl_completenessW_of_run_chosen
#print axioms Nock.RedTeam.Batch1996.fact_ringChar_zmod
#print axioms Nock.RedTeam.Batch1996.charP_ringChar_zmod
