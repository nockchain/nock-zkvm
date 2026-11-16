/-
  Nock/RedTeam/Batch1955Thm54VclCompletenessOfRun.lean

* `vcl_completeness_of_run`: `Batch1938.vcl_completeness'` with `HC := honestVCLJ_of_run …` built from
    `hrun : evalN fuel subject formula = some result` and `hbound : RunBoundedBy (ringChar F) …` (the binders
    `nockCompiles_zmod` already has), through `romTree` / `romTree_spec` exactly as `nockCompiles_zmod` does.
  * `vcl_completeness_figure_of_run` (F = Goldilocks): `Batch1947.vcl_completeness_figure` at the same `HC`;
    the run facts `hqb hle hG` are DISCHARGED (`q := ringChar F`, `hG` by `evalGRom_le_evalGBy`), the orbit
    orders by `hC/hT/hP ≤ 32`, `hp` by `goldilocks_hq`.
  The honest path table is
    `pathTableP` (old chains plus ONE `m = 0` padding chain when the demand has no deep read), so
    `pathLen ≥ 1` always (`pathLen_pos`). The old negative control `honestVCLJ_empty_at_quote` (no `HonestVCLJ`
    at `*[0 [1 0]]`) is replaced by `pathTable_T0_empty` / `pathLen_T0` (unpadded table empty, padded table has
    exactly one row). -/
import Nock.RedTeam.Batch1947Thm54VclCompletenessFigure
import Nock.RedTeam.Batch1259Thm54HonestNonVacuityConcrete
import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestRun

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1955

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.RedTeam.Batch1880 Nock.RedTeam.Batch1882 Nock.RedTeam.Batch1938 Nock.RedTeam.Batch1947

noncomputable section

section Generic
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (hT hP hC : ℕ)

open Classical in
/-- **Completeness at the compiler-built verifier.**  `vcl_completeness'` with `HC` produced from the run.
Named premises (all public): field `hF hq hK3 hp`, orbit orders `hC1 hT1 hP1 hFC hFT hFP`, sizes
`hsize hrowsC hsizeT hsizeP hmemC hmemP hleaf haxis`;
.  Data: `Ksz`, `αs`. -/
theorem vcl_completeness_of_run {fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar F) fuel subject formula)
    (Ksz : ℕ) (αs : Quad (algebraMap F K δF))
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hK3 : Module.finrank F K = 3) (hp : 25 ≤ ringChar F)
    (hC1 : 1 ≤ hC) (hT1 : 1 ≤ hT) (hP1 : 1 ≤ hP)
    (hFC : 3 * 2 ^ hC ∣ Fintype.card F - 1) (hFT : 3 * 2 ^ hT ∣ Fintype.card F - 1)
    (hFP : 3 * 2 ^ hP ∣ Fintype.card F - 1)
    (hsize : nRows (runTree (K := K) δF hrun hbound) ≤ 2 ^ hC)
    (hrowsC : 3 * nRows (runTree (K := K) δF hrun hbound) < ringChar K)
    (hsizeT : cellLen (K := K) δF (runTree (K := K) δF hrun hbound) ≤ 2 ^ hT)
    (hsizeP : pathLen (K := K) δF (runTree (K := K) δF hrun hbound) ≤ 2 ^ hP)
    (hleaf : programLeafBound (airReorder (runTree (K := K) δF hrun hbound)) ≤ 2 ^ 110)
    (hmemC : cellLen (K := K) δF (runTree (K := K) δF hrun hbound) + 1 < ringChar F)
    (hmemP : pathLen (K := K) δF (runTree (K := K) δF hrun hbound) + 1 < ringChar F)
    (haxis : programAxisBound (airReorder (runTree (K := K) δF hrun hbound)) < 2 ^ 63) :
    let HC := honestVCLJ_of_run δF hT hP hC hrun hbound Ksz αs hK3 hp hC1 hT1 hP1 hFC hFT hFP
      hsize hrowsC hsizeT hsizeP
    let hmemRows := memRows_of_run δF hT hP hC hrun hbound Ksz hK3 hC1 hT1 hP1 hFC hFT hFP hmemC hmemP
    HC.V.claim = ⟨subject, formula, result⟩ ∧ HC.t = runTree (K := K) δF hrun hbound ∧
    ((Finset.univ.filter fun χ : Coins frameVCL K =>
        ∃ s ∈ (CFv (K := K) δF hT hP hC).honestBad HC.toHonestVCLT ++
            (MFv (K := K) δF hT hP hC).honestBad
              (jointMem δF HC.toHonestVCLT (jointMemFacts_of HC hF hq hleaf hmemRows haxis)),
          s.mem ((CFv (K := K) δF hT hP hC).honestQ HC.toHonestVCLT χ,
            (MFv (K := K) δF hT hP hC).honestQ
              (jointMem δF HC.toHonestVCLT (jointMemFacts_of HC hF hq hleaf hmemRows haxis)) χ) χ).card : ℚ) /
        Fintype.card (Coins frameVCL K) ≤
      epsilonOf ((CFv (K := K) δF hT hP hC).honestBad HC.toHonestVCLT ++
        (MFv (K := K) δF hT hP hC).honestBad
          (jointMem δF HC.toHonestVCLT (jointMemFacts_of HC hF hq hleaf hmemRows haxis))) :=
  by
  intro HC hmemRows
  exact ⟨rfl, rfl, vcl_completeness' δF hT hP hC HC hF hq hleaf hmemRows haxis⟩

/-- Every `HonestVCLJ` has a non-empty path table (`VerifierData.hM`; now automatic: `pathLen_pos`). -/
theorem honestVCLJ_pathLen_pos (HC : HonestVCLJ (K := K) δF hT hP hC) : 0 < pathLen (K := K) δF HC.t := by
  have h := HC.V.hM (tP hT hP)
  rw [HC.hP0] at h
  exact h

end Generic

/-! ## The negative control: the quote program `*[0 [1 0]]` has an empty path table -/

section NC
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (hT hP hC : ℕ)

/-- The compiler's tree for `*[0 [1 0]]` (fuel `1`) is `Batch1259.T0`. -/
theorem runTree_quote :
    romTree (K := Quad (algebraMap F K δF)) Batch1259.evalRom0 = Batch1259.T0 :=
  Batch1259.romTree0 _

theorem rowPathKeys_s1 {L : Type} [Field L] (g : GenComputeRow L) (hg : g.skel.state = .s1) :
    rowPathKeys g = [] := by
  unfold rowPathKeys rowKeysAt
  rw [hg]
  have : ((List.finRange 3).filter fun j => decide (slotAcc ComputeTable.State.s1 j = some AccVCL.path)) = [] := by
    decide
  rw [this]
  rfl

theorem demT_preads_T0 : (demT (δ := δF) (Batch1259.T0 (K := Quad (algebraMap F K δF)))).preads = [] := by
  have hn : nRows (δ := δF) (Batch1259.T0 (K := Quad (algebraMap F K δF))) = 1 := by
    simp [nRows, Batch1259.air0, Batch1259.bfs_leaf]
  have hrows : genRowsT (δ := δF) (Batch1259.T0 (K := Quad (algebraMap F K δF))) =
      [bfsLabelAt (airReorder Batch1259.T0) 1] := by
    simp [genRowsT, hn]
  have hst : (bfsLabelAt (airReorder (Batch1259.T0 (K := Quad (algebraMap F K δF)))) 1).skel.state = .s1 := by
    rw [bfsLabelAt_one_skel, airReorder_label]; rfl
  simp only [demT, demandOfRowsD, hrows, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact rowPathKeys_s1 _ hst

/-- **NC (unpadded)**: the old (unpadded) path table of the quote program `*[0 [1 0]]` is EMPTY. -/
theorem pathTable_T0_empty :
    (pathTable δF (0 : Quad (algebraMap F K δF)) (demT (δ := δF) (Batch1259.T0 (K := Quad (algebraMap F K δF)))).cells
      (demT (δ := δF) (Batch1259.T0 (K := Quad (algebraMap F K δF)))).preads).length = 0 := by
  simp only [demT_preads_T0, pathTable, pathReads, List.filter_nil, List.dedup_nil, List.flatMap_nil,
    List.length_nil]

/-- **Padded**: the honest (padded) path table of the same program has exactly ONE row (the `m = 0`
padding chain). -/
theorem pathLen_T0 : pathLen (K := K) δF Batch1259.T0 = 1 := by
  have h := pathTable_T0_empty (K := K) δF
  unfold pathLen pathTableP
  rw [List.length_append, h, chainRows_length, padSteps_of_eq _ _ (by rw [demT_preads_T0]; rfl)]
  rfl

end NC

/-! ## Goldilocks: the figure at the compiler-built verifier -/

section Goldilocks
variable {K : Type} [Field K] [Algebra Nock.Field.Fp K] [FiniteDimensional Nock.Field.Fp K] [Fintype K]
  [DecidableEq K] (δF : Nock.Field.Fp) [Fact (¬ IsSquare (algebraMap Nock.Field.Fp K δF))] (hT hP hC : ℕ)

/-- `3·2^h ∣ p − 1` at Goldilocks for `h ≤ 32` (`p − 1 = 3·2^32·1431655765`). -/
theorem goldilocks_orbit_dvd {h : ℕ} (hh : h ≤ 32) : 3 * 2 ^ h ∣ Fintype.card Nock.Field.Fp - 1 := by
  have hc : Fintype.card Nock.Field.Fp - 1 = 3 * 2 ^ 32 * 1431655765 := by
    rw [show Fintype.card Nock.Field.Fp = Nock.Field.p from ZMod.card _, Nock.Field.p_eq]
    norm_num
  rw [hc]
  exact (Nat.mul_dvd_mul_left 3 (Nat.pow_dvd_pow 2 hh)).trans (Nat.dvd_mul_right _ _)

theorem goldilocks_hp : 25 ≤ ringChar Nock.Field.Fp := by
  have := goldilocks_hq; omega

theorem ringChar_quad_fp :
    ringChar (Quad (algebraMap Nock.Field.Fp K δF)) = ringChar Nock.Field.Fp := by
  rw [ringChar_quad, ← Algebra.ringChar_eq Nock.Field.Fp K]

/-- **The completeness figure at the compiler-built verifier** (`< 2^-65`).  The run facts of
`vcl_completeness_figure` (`hqb hle hG`) are discharged from `hrun`/`hbound`; the orbit orders from
`hC, hT, hP ∈ [1, 32]`.  Remaining premises: `hs hf` (claim nouns over `𝔽`), `hK` (`p² ≤ |𝕂|`), `hK3`, the
size bounds. -/
theorem vcl_completeness_figure_of_run {fuel : ℕ} {subject formula result : Noun}
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
    (hmemP : pathLen (K := K) δF (runTree (K := K) δF hrun hbound) + 1 < ringChar Nock.Field.Fp)
    (haxis : programAxisBound (airReorder (runTree (K := K) δF hrun hbound)) < 2 ^ 63)
    (hN : nRows (runTree (K := K) δF hrun hbound) ≤ 2 ^ 31)
    (hR : (bfsRows (airReorder (runTree (K := K) δF hrun hbound))).length ≤ 2 ^ 31)
    (hnC : cellLen (K := K) δF (runTree (K := K) δF hrun hbound) ≤ 2 ^ 31)
    (hnP : pathLen (K := K) δF (runTree (K := K) δF hrun hbound) ≤ 2 ^ 31) :
    let HC := honestVCLJ_of_run δF hT hP hC hrun hbound Ksz αs hK3 goldilocks_hp hC1 hT1 hP1
      (goldilocks_orbit_dvd hC32) (goldilocks_orbit_dvd hT32) (goldilocks_orbit_dvd hP32)
      hsize hrowsC hsizeT hsizeP
    let hmemRows := memRows_of_run δF hT hP hC hrun hbound Ksz hK3 hC1 hT1 hP1
      (goldilocks_orbit_dvd hC32) (goldilocks_orbit_dvd hT32) (goldilocks_orbit_dvd hP32) hmemC hmemP
    epsilonOf ((CFv (K := K) δF hT hP hC).honestBad HC.toHonestVCLT ++
      (MFv (K := K) δF hT hP hC).honestBad
        (jointMem δF HC.toHonestVCLT
          (jointMemFacts_of HC (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq
            hleaf hmemRows haxis))) < 1 / (2 : ℚ) ^ 65 := by
  intro HC hmemRows
  have hgrom := evalGRom_of_runBounded hrun hbound
  exact vcl_completeness_figure δF hT hP hC HC hleaf hmemRows haxis hK hN hR hnC hnP
    (q := ringChar Nock.Field.Fp) (by have := goldilocks_hq; omega) (ringChar_quad_fp δF).ge
    hs hf (evalGRom_le_evalGBy hgrom)

end Goldilocks

end

end Nock.RedTeam.Batch1955

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.honestVCLJ_of_run
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.demT_cells_pos
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.exists_orderOf_eq_of_dvd
#print axioms Nock.RedTeam.Batch1955.vcl_completeness_of_run
#print axioms Nock.RedTeam.Batch1955.honestVCLJ_pathLen_pos
#print axioms Nock.RedTeam.Batch1955.pathLen_T0
#print axioms Nock.RedTeam.Batch1955.pathTable_T0_empty
#print axioms Nock.RedTeam.Batch1955.demT_preads_T0
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.pathLen_pos
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.pathTableP_good
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.HonestVCL.req_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.path_pTotalP
#print axioms Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.path_yTotalP
#print axioms Nock.RedTeam.Batch1955.goldilocks_orbit_dvd
#print axioms Nock.RedTeam.Batch1955.vcl_completeness_figure_of_run
