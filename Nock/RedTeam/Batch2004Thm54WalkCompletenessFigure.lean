/-
  Nock/RedTeam/Batch2004Thm54WalkCompletenessFigure.lean

  **The walk twin of the completeness figure.**  Twin of `Batch1947.vcl_completeness_figure` / `Batch1955.vcl_completeness_figure_of_run`.

  The signed §1 v6 text says the joint honest completeness total stays `< 2^-65` with walk rows in place of path
  rows.  The compute side `CFvW` is the unchanged tower compute family (`epsilon_honestBadCF`, same seed weight);
  the honest memory error is `(1 + 5·nC + 3·nW)/|𝕂|²` (`Batch1993.honestBad_epsilon`).  With `nC, nW ≤ 2^31` the
  numerator is `≤ 2^144 + 5·2^31 + 1 + 8·2^31 ≤ 2^145`, so `Batch1947.fig_arith` applies verbatim.
  `vcl_completenessW_figure`: `epsilonOf (CFvW.honestBad ++ MFvW.honestBad) < 2^-65` at Goldilocks, `|𝕂| ≥ p²`.
  The two instance binders `[Fact (ringChar Fp).Prime] [Algebra (ZMod (ringChar Fp)) K]` are the walk family's
  (derived in `Batch1996` as `fact_ringChar_zmod` / `algRC`).
-/
import Nock.RedTeam.Batch1955Thm54VclCompletenessOfRun
import Nock.RedTeam.Batch1993Thm54WalkW4cFamily
import Nock.RedTeam.Batch1996Thm54WalkW4dCompletenessChosen
import Nock.NockVMROM.Thm54.VclL.Compute.TowerPackageW

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch2004

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.VclL.StandaloneW
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.RedTeam.Batch1880 Nock.RedTeam.Batch1882 Nock.RedTeam.Batch1938 Nock.RedTeam.Batch1947
open Nock.RedTeam.Batch1955 Nock.RedTeam.Batch1964 Nock.RedTeam.Batch1996

noncomputable section

section Goldilocks
variable {K : Type} [Field K] [Algebra Nock.Field.Fp K] [FiniteDimensional Nock.Field.Fp K] [Fintype K]
  [DecidableEq K] (δF : Nock.Field.Fp) [Fact (¬ IsSquare (algebraMap Nock.Field.Fp K δF))]
  [Fact (ringChar Nock.Field.Fp).Prime] [Algebra (ZMod (ringChar Nock.Field.Fp)) K] (hT hP hC : ℕ)

open Classical in
/-- **The walk completeness figure, compiled.**  `Pr[some honest bad summand fires]`'s bound `ε` is below `2^-65`
at the walk pair `CFvW / MFvW`.  Hypotheses: those of `vcl_completeness_figure` with the memory-size premise
`hnP` (path rows) replaced by `hnW : memRows tWW ≤ 2^31` (walk rows), and `hkp` (the `hmemW` content). -/
theorem vcl_completenessW_figure (HJ : HonestVCLJW (K := K) δF hT hP hC)
    (hleaf : programLeafBound (airReorder HJ.t) ≤ 2 ^ 110)
    (hmemRows : ∀ k, HJ.V.memRows k + 1 < ringChar Nock.Field.Fp)
    (haxis : programAxisBound (airReorder HJ.t) < 2 ^ 63)
    (hkp : krT δF HJ.t + HJ.V.memRows (tWW hT hP) < ringChar Nock.Field.Fp)
    (hK : Nock.Field.p ^ 2 ≤ Fintype.card K)
    (hN : HJ.V.N ≤ 2 ^ 31) (hR : (bfsRows (airReorder HJ.t)).length ≤ 2 ^ 31)
    (hnC : HJ.V.memRows (tCW hT hP) ≤ 2 ^ 31) (hnW : HJ.V.memRows (tWW hT hP) ≤ 2 ^ 31)
    {q : ℕ} (hqb : 1 < q) (hle : q ≤ ringChar (Quad (algebraMap Nock.Field.Fp K δF)))
    (hs : FieldEmbedding.BoundedBy q HJ.V.claim.subject) (hf : FieldEmbedding.BoundedBy q HJ.V.claim.formula)
    (hG : FieldEmbedding.evalGBy q HJ.fuel HJ.V.claim.subject HJ.V.claim.formula = some HJ.V.claim.result) :
    epsilonOf ((CFvW (K := K) δF hT hP hC).honestBad HJ.toHonestVCLT ++
      (MFvW (K := K) δF hT hP hC (krT δF HJ.t)).honestBad
        (jointMemW HJ (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq
          hleaf hmemRows haxis hkp)) < 1 / (2 : ℚ) ^ 65 := by
  have hconf : TraceConfined (2 ^ 110) (airReorder HJ.t) := traceConfined_of_leafBound hleaf
  have hS := badSeedsT_card_le (δ := δF) hqb hle hs hf hG HJ.hgen (Λ := 2 ^ 110) Nat.one_le_two_pow hconf
  have hA : epsilonOf ((CFvW (K := K) δF hT hP hC).honestBad HJ.toHonestVCLT) =
      ((badSeedsT δF HJ.t).card : ℚ) / (Fintype.card K : ℚ) ^ 2 +
        ((nRows HJ.t * (Fintype.card K * Fintype.card K) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 3 +
        ((HJ.V.N * HJ.V.N : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 1 +
        5 * ((HJ.V.N * (Fintype.card K * Fintype.card K) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 4 :=
    epsilon_honestBadCF δF HJ.t _ le_rfl _ le_rfl HJ.V.N HJ.V.hN HJ.V (fun i => stT HJ.t i)
  have hB : epsilonOf ((MFvW (K := K) δF hT hP hC (krT δF HJ.t)).honestBad
        (jointMemW HJ (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq
          hleaf hmemRows haxis hkp)) =
      (1 + 5 * (HJ.V.memRows (tCW hT hP) : ℚ) + 3 * (HJ.V.memRows (tWW hT hP) : ℚ)) /
        (Fintype.card K : ℚ) ^ 2 :=
    Nock.RedTeam.Batch1993.honestBad_epsilon δF hT hP (krT δF HJ.t)
      (jointMemW HJ (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq
          hleaf hmemRows haxis hkp)
  have hcpos : (0 : ℚ) < (Fintype.card K : ℚ) := by
    have : 0 < Fintype.card K := Fintype.card_pos
    exact_mod_cast this
  have hcne : (Fintype.card K : ℚ) ≠ 0 := hcpos.ne'
  rw [show ∀ {Tr : Type} {St : (Coins frameVCL K → Tr) → Prop} (a b : List (BadSummand frameVCL K Tr St)),
      epsilonOf (a ++ b) = epsilonOf a + epsilonOf b from fun a b => by
        unfold epsilonOf; rw [List.map_append, List.sum_append], hA, hB]
  have hNn : HJ.V.N = nRows HJ.t := HJ.hN
  set c : ℕ := Fintype.card K with hcdef
  have hwS : (badSeedsT δF HJ.t).card ≤ 2 ^ 144 := by
    refine hS.trans ?_
    unfold seedWeightT
    have h1 : (bfsRows (airReorder HJ.t)).length * (3 * (2 * 2 ^ 110 - 1)) ≤ 2 ^ 31 * (3 * (2 * 2 ^ 110)) :=
      Nat.mul_le_mul hR (Nat.mul_le_mul_left _ (by omega))
    have h2 : (2 : ℕ) ^ 31 * (3 * (2 * 2 ^ 110)) + 1 ≤ 2 ^ 144 := by norm_num
    omega
  have e : (((badSeedsT δF HJ.t).card : ℚ) / (c : ℚ) ^ 2 +
        ((nRows HJ.t * (c * c) : ℕ) : ℚ) / (c : ℚ) ^ 3 + ((HJ.V.N * HJ.V.N : ℕ) : ℚ) / (c : ℚ) ^ 1 +
        5 * ((HJ.V.N * (c * c) : ℕ) : ℚ) / (c : ℚ) ^ 4) +
      (1 + 5 * (HJ.V.memRows (tCW hT hP) : ℚ) + 3 * (HJ.V.memRows (tWW hT hP) : ℚ)) / (c : ℚ) ^ 2 =
      (((badSeedsT δF HJ.t).card + 5 * HJ.V.N + (1 + 5 * HJ.V.memRows (tCW hT hP) + 3 * HJ.V.memRows (tWW hT hP)) : ℕ) : ℚ)
          / (c : ℚ) ^ 2 +
        ((HJ.V.N + HJ.V.N * HJ.V.N : ℕ) : ℚ) / (c : ℚ) := by
    rw [← hNn]
    push_cast
    field_simp
    ring
  rw [e]
  exact fig_arith c _ _ hK (by omega) (by
    have : HJ.V.N * HJ.V.N ≤ 2 ^ 31 * 2 ^ 31 := Nat.mul_le_mul hN hN
    norm_num at this ⊢; omega)

open Classical in
/-- **The walk completeness figure at the compiler-built verifier** (`< 2^-65`): `vcl_completenessW_figure` with
`HJ := honestVCLJW_of_run …` from `hrun`/`hbound`.  Premises: those of `vcl_completeness_figure_of_run` with
`hmemP`/`hnP` (path) replaced by `hmemW` (`krW + |walkRows| < p`, as `Batch1996`) / `hnW` (`|walkRows| ≤ 2^31`). -/
theorem vcl_completenessW_figure_of_run {fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar Nock.Field.Fp) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar Nock.Field.Fp) subject)
    (hf : FieldEmbedding.BoundedBy (ringChar Nock.Field.Fp) formula)
    (Ksz : ℕ) (αs : Quad (algebraMap Nock.Field.Fp K δF))
    (hK3 : Module.finrank Nock.Field.Fp K = 3) (hK : Nock.Field.p ^ 2 ≤ Fintype.card K)
    (hC1 : 1 ≤ hC) (hT1 : 1 ≤ hT) (hP1 : 1 ≤ hP) (hC32 : hC ≤ 32) (hT32 : hT ≤ 32) (hP32 : hP ≤ 32)
    (hsize : nRows (runTree (K := K) δF hrun hbound) ≤ 2 ^ hC)
    (hrowsC : 3 * nRows (runTree (K := K) δF hrun hbound) < ringChar K)
    (hsizeT : cellLen (K := K) δF (runTree (K := K) δF hrun hbound) ≤ 2 ^ hT)
    (hsizeP : pathLen (K := K) δF (runTree (K := K) δF hrun hbound) ≤ 2 ^ hP)
    (hleaf : programLeafBound (airReorder (runTree (K := K) δF hrun hbound)) ≤ 2 ^ 110)
    (hmemC : cellLen (K := K) δF (runTree (K := K) δF hrun hbound) + 1 < ringChar Nock.Field.Fp)
    (hmemW : krW (demT (runTree (K := K) δF hrun hbound)).cells (demT (runTree (K := K) δF hrun hbound)).preads +
      (walkRows (demT (runTree (K := K) δF hrun hbound)).cells
        (demT (runTree (K := K) δF hrun hbound)).preads).length < ringChar Nock.Field.Fp)
    (haxis : programAxisBound (airReorder (runTree (K := K) δF hrun hbound)) < 2 ^ 63)
    (hN : nRows (runTree (K := K) δF hrun hbound) ≤ 2 ^ 31)
    (hR : (bfsRows (airReorder (runTree (K := K) δF hrun hbound))).length ≤ 2 ^ 31)
    (hnC : cellLen (K := K) δF (runTree (K := K) δF hrun hbound) ≤ 2 ^ 31)
    (hnW : (walkRows (demT (runTree (K := K) δF hrun hbound)).cells
        (demT (runTree (K := K) δF hrun hbound)).preads).length ≤ 2 ^ 31) :
    let HJ := honestVCLJW_of_run δF hT hP hC hrun hbound Ksz αs hK3 goldilocks_hp hC1 hT1 hP1
      (goldilocks_orbit_dvd hC32) (goldilocks_orbit_dvd hT32) (goldilocks_orbit_dvd hP32)
      hsize hrowsC hsizeT hsizeP
    let hmemRows := memRowsW_of_run δF hT hP hC hrun hbound Ksz hK3 hC1 hT1 hP1
      (goldilocks_orbit_dvd hC32) (goldilocks_orbit_dvd hT32) (goldilocks_orbit_dvd hP32) hmemC hmemW
    let hkp := kpW_of_run δF hT hP hC hrun hbound Ksz hK3 hC1 hT1 hP1
      (goldilocks_orbit_dvd hC32) (goldilocks_orbit_dvd hT32) (goldilocks_orbit_dvd hP32) hmemW
    epsilonOf ((CFvW (K := K) δF hT hP hC).honestBad HJ.toHonestVCLT ++
      (MFvW (K := K) δF hT hP hC (krT δF HJ.t)).honestBad
        (jointMemW HJ (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq
          hleaf hmemRows haxis hkp)) < 1 / (2 : ℚ) ^ 65 := by
  intro HJ hmemRows hkp
  have hgrom := evalGRom_of_runBounded hrun hbound
  exact vcl_completenessW_figure δF hT hP hC HJ hleaf hmemRows haxis hkp hK hN hR
    (by rw [HJ.hC0]; exact hnC) (by rw [HJ.hW0]; exact hnW)
    (q := ringChar Nock.Field.Fp) (by have := goldilocks_hq; omega) (ringChar_quad_fp δF).ge
    hs hf (evalGRom_le_evalGBy hgrom)

end Goldilocks

end

end Nock.RedTeam.Batch2004

#print axioms Nock.RedTeam.Batch2004.vcl_completenessW_figure
#print axioms Nock.RedTeam.Batch2004.vcl_completenessW_figure_of_run
