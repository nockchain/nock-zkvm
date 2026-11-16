/-
  Nock/RedTeam/Batch1956Thm54VclCompletenessToy.lean

  **One concrete, fully discharged instance of
  `vcl_completeness_of_run` / `vcl_completeness_figure_of_run` (PG38 addenda run-3 N1, run-4).**

  Measured at the run: `nRows = 1`, demand binds `[0, [1 0]]`, one export read `([1 0], 3)`, NO path read
  (`preads = []`), `cellLen = 1`, `pathLen = 1` (the `m = 0` pad, PAD),
  leaf bound `2`, axis bound `0`, `|bfsRows| = 1`.

  `vcl_completeness_toy` has NO hypotheses: every premise of `vcl_completeness_of_run` (`hrun hbound hF hq
  hK3 hp hC1 hT1 hP1 hFC hFT hFP hsize hrowsC hsizeT hsizeP hleaf hmemC hmemP haxis`; Batch1962: `hax1` is gone) and the extra
  premises of `vcl_completeness_figure_of_run` (`hs hf hK hC32 hT32 hP32 hN hR hnC hnP`) are closed lemmas
  below.
-/
import Nock.RedTeam.Batch1955Thm54VclCompletenessOfRun
import Nock.RedTeam.Batch1560PrimalityCerts

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1956

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.RedTeam.Batch1259 (subj0 form0 T0)
open Nock.RedTeam.Batch1880 Nock.RedTeam.Batch1882 Nock.RedTeam.Batch1938 Nock.RedTeam.Batch1947
open Nock.RedTeam.Batch1955

noncomputable section

/-! ## 1. The quote run's demand (generic in the field) -/

section Generic
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

theorem nRows_T0 : nRows (δ := δF) (T0 (K := Quad (algebraMap F K δF))) = 1 := by
  simp [nRows, Batch1259.air0, Batch1259.bfs_leaf]

/-- **The demand of `*[0 [1 0]]`**: binds subject and formula, ONE export read `([1 0], 3)` (the quoted
constant), NO path read. -/
theorem demT_T0 : demT (δ := δF) (T0 (K := Quad (algebraMap F K δF))) =
    ⟨[subj0, form0], [(form0, 3)], []⟩ := by
  have hrows : genRowsT (δ := δF) (T0 (K := Quad (algebraMap F K δF))) =
      [bfsLabelAt (airReorder T0) 1] := by
    simp [genRowsT, nRows_T0]
  have hst : (bfsLabelAt (airReorder (T0 (K := Quad (algebraMap F K δF)))) 1).skel =
      (T0 (K := Quad (algebraMap F K δF))).label.skel := by
    rw [bfsLabelAt_one_skel, airReorder_label]
  have hs1 : (bfsLabelAt (airReorder (T0 (K := Quad (algebraMap F K δF)))) 1).skel.state = .s1 := by
    rw [hst]; rfl
  have hreq : (bfsLabelAt (airReorder (T0 (K := Quad (algebraMap F K δF)))) 1).requests =
      [⟨form0, .atom 0, 3, 0⟩] := by
    rw [Batch1259.air0]
    simp [bfsLabelAt, Batch1259.bfsRows0, skelNode]
  simp only [demT, demandOfRowsD, hrows, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [rowPathKeys_s1 _ hs1]
  simp only [rowExportKeys, rowKeysAt, hs1, rowSlotKeys, hreq]
  simp only [rowBinds, hst]
  have : ((List.finRange 3).filter fun j => decide (slotAcc ComputeTable.State.s1 j = some AccVCL.export)) =
      [0] := by
    decide
  rw [this]
  rfl

theorem cellLen_T0 : cellLen (K := K) δF T0 = 1 := by
  simp [cellLen, demT_T0, Demand.cells, Demand.roots, closureOf, cellsOf]

theorem axis_T0 : programAxisBound (airReorder (T0 (K := K))) = 0 := by
  rw [Batch1259.air0, programAxisBound, Batch1259.bfsRows0]
  simp [honestAx, skelNode, genSkelOp1]

theorem bfsRows_len_T0 : (bfsRows (airReorder (T0 (K := K)))).length = 1 := by
  rw [Batch1259.air0, Batch1259.bfsRows0]; rfl

end Generic

/-! ## 2. The concrete configuration: Goldilocks, `K = GaloisField p 3`, `δ = 7` -/

local notation "Fp" => Nock.Field.Fp
local notation "Kc" => Nock.Field.K

instance instFactSevenNS : Fact (¬ IsSquare (algebraMap Fp Kc 7)) :=
  ⟨by rw [map_ofNat]; exact Batch1560.seven_not_square_K⟩

abbrev δ7 : Fp := 7

theorem hK3_toy : Module.finrank Fp Kc = 3 := GaloisField.finrank Nock.Field.p (by norm_num)

theorem ringChar_Kc : ringChar Kc = ringChar Fp := (Algebra.ringChar_eq Fp Kc).symm

theorem hrun_toy : Nock.evalN 1 subj0 form0 = some (.atom 0) := Batch1259.hrun0

theorem hbound_toy : RunBoundedBy (ringChar Fp) 1 subj0 form0 := ⟨.atom 0, by simp [evalGRom]⟩

/-- The compiler's tree at the toy run is `T0`. -/
theorem runTree_toy : runTree (K := Kc) δ7 hrun_toy hbound_toy = T0 := Batch1259.romTree0 _

theorem hs_toy : FieldEmbedding.BoundedBy (ringChar Fp) subj0 := by
  have := goldilocks_hq; simp [FieldEmbedding.BoundedBy]; omega

theorem hf_toy : FieldEmbedding.BoundedBy (ringChar Fp) form0 := by
  have := goldilocks_hq; simp [FieldEmbedding.BoundedBy]; omega

theorem hK_toy : Nock.Field.p ^ 2 ≤ Fintype.card Kc := by
  rw [Nock.Field.card_K]; exact Nat.pow_le_pow_right (by rw [Nock.Field.p_eq]; norm_num) (by norm_num)

theorem h1_32 : (1 : ℕ) ≤ 32 := by norm_num

theorem hsize_toy : nRows (runTree (K := Kc) δ7 hrun_toy hbound_toy) ≤ 2 ^ 1 := by
  rw [runTree_toy, nRows_T0]; norm_num

theorem hrowsC_toy : 3 * nRows (runTree (K := Kc) δ7 hrun_toy hbound_toy) < ringChar Kc := by
  rw [runTree_toy, nRows_T0, ringChar_Kc]; have := goldilocks_hq; omega

theorem hsizeT_toy : cellLen (K := Kc) δ7 (runTree (K := Kc) δ7 hrun_toy hbound_toy) ≤ 2 ^ 1 := by
  rw [runTree_toy, cellLen_T0]; norm_num

theorem hsizeP_toy : pathLen (K := Kc) δ7 (runTree (K := Kc) δ7 hrun_toy hbound_toy) ≤ 2 ^ 1 := by
  rw [runTree_toy, pathLen_T0]; norm_num

theorem hleaf_toy : programLeafBound (airReorder (runTree (K := Kc) δ7 hrun_toy hbound_toy)) ≤ 2 ^ 110 := by
  rw [runTree_toy, Batch1259.leaf0]; norm_num

theorem hmemC_toy : cellLen (K := Kc) δ7 (runTree (K := Kc) δ7 hrun_toy hbound_toy) + 1 < ringChar Fp := by
  rw [runTree_toy, cellLen_T0]; have := goldilocks_hq; omega

theorem hmemP_toy : pathLen (K := Kc) δ7 (runTree (K := Kc) δ7 hrun_toy hbound_toy) + 1 < ringChar Fp := by
  rw [runTree_toy, pathLen_T0]; have := goldilocks_hq; omega

theorem haxis_toy : programAxisBound (airReorder (runTree (K := Kc) δ7 hrun_toy hbound_toy)) < 2 ^ 63 := by
  rw [runTree_toy, axis_T0]; norm_num

theorem hN_toy : nRows (runTree (K := Kc) δ7 hrun_toy hbound_toy) ≤ 2 ^ 31 := by
  rw [runTree_toy, nRows_T0]; norm_num

theorem hR_toy : (bfsRows (airReorder (runTree (K := Kc) δ7 hrun_toy hbound_toy))).length ≤ 2 ^ 31 := by
  rw [runTree_toy, bfsRows_len_T0]; norm_num

theorem hnC_toy : cellLen (K := Kc) δ7 (runTree (K := Kc) δ7 hrun_toy hbound_toy) ≤ 2 ^ 31 := by
  rw [runTree_toy, cellLen_T0]; norm_num

theorem hnP_toy : pathLen (K := Kc) δ7 (runTree (K := Kc) δ7 hrun_toy hbound_toy) ≤ 2 ^ 31 := by
  rw [runTree_toy, pathLen_T0]; norm_num

/-! ## 3. The headline: completeness at the toy run, no hypotheses -/

/-- The honest joint datum of the toy run (exactly the `HC` of `vcl_completeness_figure_of_run`). -/
def HCtoy : HonestVCLJ (K := Kc) δ7 1 1 1 :=
  honestVCLJ_of_run δ7 1 1 1 hrun_toy hbound_toy 0 0 hK3_toy goldilocks_hp le_rfl le_rfl le_rfl
    (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32)
    hsize_toy hrowsC_toy hsizeT_toy hsizeP_toy

theorem hmemRows_toy : ∀ k, (HCtoy).V.memRows k + 1 < ringChar Fp :=
  memRows_of_run δ7 1 1 1 hrun_toy hbound_toy 0 hK3_toy le_rfl le_rfl le_rfl
    (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) hmemC_toy hmemP_toy

open Classical in
/-- **`vcl_completeness_of_run` at one concrete program, NO hypotheses** (PG38 run-3 N1 / run-4):
the quote `*[0 [1 0]]` over Goldilocks, `K = GaloisField p 3`, `δ = 7`, `hC = hT = hP = 1`.  The honest
datum is the compiler's (`claim = ⟨0, [1 0], 0⟩`, `t = T0`), the honest rejection probability is at most
`epsilonOf` of the honest-bad events (`vcl_completeness_of_run`), and that `epsilonOf` is `< 2^-65`
(`vcl_completeness_figure_of_run`) at the same datum. -/
theorem vcl_completeness_toy :
    HCtoy.V.claim = ⟨subj0, form0, .atom 0⟩ ∧ HCtoy.t = T0 ∧
    ((Finset.univ.filter fun χ : Coins frameVCL Kc =>
        ∃ s ∈ (CFv (K := Kc) δ7 1 1 1).honestBad HCtoy.toHonestVCLT ++
            (MFv (K := Kc) δ7 1 1 1).honestBad
              (jointMem δ7 HCtoy.toHonestVCLT (jointMemFacts_of HCtoy
                (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hleaf_toy hmemRows_toy haxis_toy)),
          s.mem ((CFv (K := Kc) δ7 1 1 1).honestQ HCtoy.toHonestVCLT χ,
            (MFv (K := Kc) δ7 1 1 1).honestQ
              (jointMem δ7 HCtoy.toHonestVCLT (jointMemFacts_of HCtoy
                (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hleaf_toy hmemRows_toy
                haxis_toy)) χ) χ).card : ℚ) /
        Fintype.card (Coins frameVCL Kc) ≤
      epsilonOf ((CFv (K := Kc) δ7 1 1 1).honestBad HCtoy.toHonestVCLT ++
        (MFv (K := Kc) δ7 1 1 1).honestBad
          (jointMem δ7 HCtoy.toHonestVCLT (jointMemFacts_of HCtoy
            (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hleaf_toy hmemRows_toy haxis_toy))) ∧
    epsilonOf ((CFv (K := Kc) δ7 1 1 1).honestBad HCtoy.toHonestVCLT ++
        (MFv (K := Kc) δ7 1 1 1).honestBad
          (jointMem δ7 HCtoy.toHonestVCLT (jointMemFacts_of HCtoy
            (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hleaf_toy hmemRows_toy haxis_toy)))
      < 1 / (2 : ℚ) ^ 65 := by
  have h1 := vcl_completeness_of_run (K := Kc) δ7 1 1 1 hrun_toy hbound_toy 0 0
    (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hK3_toy goldilocks_hp le_rfl le_rfl le_rfl
    (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32)
    hsize_toy hrowsC_toy hsizeT_toy hsizeP_toy hleaf_toy hmemC_toy hmemP_toy haxis_toy
  have h2 := vcl_completeness_figure_of_run (K := Kc) δ7 1 1 1 hrun_toy hbound_toy hs_toy hf_toy 0 0
    hK3_toy hK_toy le_rfl le_rfl le_rfl h1_32 h1_32 h1_32
    hsize_toy hrowsC_toy hsizeT_toy hsizeP_toy hleaf_toy hmemC_toy hmemP_toy haxis_toy
    hN_toy hR_toy hnC_toy hnP_toy
  exact ⟨h1.1, h1.2.1.trans runTree_toy, h1.2.2, h2⟩

/-! ## 4. Negative controls -/

theorem nc_hq_zmod73 : ¬ (2 ^ 63 < ringChar (ZMod 73)) := by
  rw [ZMod.ringChar_zmod_n]; norm_num

/-- Still a true statement about demands: a demand with an axis-1 path read violated the
old premise `∀ r ∈ preads, r.2 ≠ 1`. -/
theorem nc_hax1_axis1 : ¬ (∀ r ∈ (⟨[], [], [(subj0, 1)]⟩ : Demand).preads, r.2 ≠ 1) := by
  simp

end

end Nock.RedTeam.Batch1956

#print axioms Nock.RedTeam.Batch1956.vcl_completeness_toy
#print axioms Nock.RedTeam.Batch1956.demT_T0
#print axioms Nock.RedTeam.Batch1956.cellLen_T0
#print axioms Nock.RedTeam.Batch1956.axis_T0
#print axioms Nock.RedTeam.Batch1956.runTree_toy
#print axioms Nock.RedTeam.Batch1956.hbound_toy
#print axioms Nock.RedTeam.Batch1956.nc_hq_zmod73
#print axioms Nock.RedTeam.Batch1956.nc_hax1_axis1
