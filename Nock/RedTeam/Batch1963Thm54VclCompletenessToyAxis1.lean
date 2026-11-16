/-
  Nock/RedTeam/Batch1963Thm54VclCompletenessToyAxis1.lean

  **A SECOND concrete, hypothesis-free instance of
  `vcl_completeness_of_run` / `vcl_completeness_figure_of_run`, at a program that EXECUTES AXIS 1.**

  Program: `*[0 [0 1]]` — subject `0`, formula `[0 1]` (OP0 at axis `1`: `Noun.slot 1 n = some n`), fuel `1`,
  result `0`.  One `s0` row with `honestAx = 1`: its requests are the formula-open `([0 1], 3)` (export) and the
  slot read `(0, 1)` (path kind).  The honest `z1` is `1` there, the path term is `0`, and the memory
  side drops the read (`isPathAx 1 = false`), so the padded path table has the single `m = 0` pad row.

  `vcl_completeness_toy_axis1` has NO hypotheses.  `axis_A = 1`: the program's axis bound is exactly `1` (the row really is an axis-1 row).
-/
import Nock.RedTeam.Batch1962Thm54Z1bHonestAxis1

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1963

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.RedTeam.Batch1880 Nock.RedTeam.Batch1882 Nock.RedTeam.Batch1938 Nock.RedTeam.Batch1947
open Nock.RedTeam.Batch1955

noncomputable section

abbrev subjA : Noun := .atom 0
abbrev formA : Noun := .cell (.atom 0) (.atom 1)

/-- The generator's tree at `*[0 [0 1]]`: one `s0` row, requests `([0 1], 3)` and `(0, 1)`. -/
abbrev TA {K : Type} [Field K] : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp0 subjA formA (.atom 0) (.atom 1) (.atom 0) 1)
    [⟨formA, .atom 1, 3, 0⟩, ⟨subjA, .atom 0, 1, 0⟩]) []

section Generic
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

theorem genA : genComputeSkeleton (K := Quad (algebraMap F K δF)) 1 subjA formA = .ok (TA, .atom 0) := by
  simp [genComputeSkeleton, Noun.slot]

theorem evalRomA : evalRom 1 subjA formA = some (.atom 0) := by simp [evalRom, Noun.slot]

theorem romTreeA (h : evalRom 1 subjA formA = some (.atom 0)) :
    romTree (K := Quad (algebraMap F K δF)) h = TA := by
  have hs := romTree_spec (K := Quad (algebraMap F K δF)) h
  rw [genA δF] at hs
  injection hs with hs
  exact (Prod.mk.inj hs).1.symm

theorem airA : airReorder (TA (K := Quad (algebraMap F K δF))) = TA := by
  simp [airReorder, skelNode, genSkelOp0, airNeedsSwap]

theorem bfsA : bfsRows (TA (K := Quad (algebraMap F K δF))) =
    [skelNode (genSkelOp0 subjA formA (.atom 0) (.atom 1) (.atom 0) 1) [⟨formA, .atom 1, 3, 0⟩, ⟨subjA, .atom 0, 1, 0⟩]] := by
  simp [bfsRows, Batch1259.bfs_leaf]

theorem nRows_A : nRows (δ := δF) (TA (K := Quad (algebraMap F K δF))) = 1 := by
  simp [nRows, airA, Batch1259.bfs_leaf]

/-- **The demand of `*[0 [0 1]]`**: binds subject and formula, ONE export read `([0 1], 3)`, ONE path-kind read
`(0, 1)` — at axis `1`. -/
theorem demT_A : demT (δ := δF) (TA (K := Quad (algebraMap F K δF))) =
    ⟨[subjA, formA], [(formA, 3)], [(subjA, 1)]⟩ := by
  have hrows : genRowsT (δ := δF) (TA (K := Quad (algebraMap F K δF))) =
      [bfsLabelAt (airReorder TA) 1] := by
    simp [genRowsT, nRows_A]
  have hst : (bfsLabelAt (airReorder (TA (K := Quad (algebraMap F K δF)))) 1).skel =
      (TA (K := Quad (algebraMap F K δF))).label.skel := by
    rw [bfsLabelAt_one_skel, airReorder_label]
  have hs0 : (bfsLabelAt (airReorder (TA (K := Quad (algebraMap F K δF)))) 1).skel.state = .s0 := by
    rw [hst]; rfl
  have hreq : (bfsLabelAt (airReorder (TA (K := Quad (algebraMap F K δF)))) 1).requests =
      [⟨formA, .atom 1, 3, 0⟩, ⟨subjA, .atom 0, 1, 0⟩] := by
    rw [airA δF]
    simp [bfsLabelAt, bfsA, skelNode]
  simp only [demT, demandOfRowsD, hrows, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp only [rowExportKeys, rowPathKeys, rowKeysAt, hs0, rowSlotKeys, hreq]
  simp only [rowBinds, hst]
  have e1 : ((List.finRange 3).filter fun j => decide (slotAcc ComputeTable.State.s0 j = some AccVCL.export)) =
      [0] := by decide
  have e2 : ((List.finRange 3).filter fun j => decide (slotAcc ComputeTable.State.s0 j = some AccVCL.path)) =
      [1] := by decide
  rw [e1, e2]
  rfl

theorem cellLen_A : cellLen (K := K) δF (TA (K := Quad (algebraMap F K δF))) = 1 := by
  simp [cellLen, demT_A, Demand.cells, Demand.roots, closureOf, cellsOf]

/-- The program's axis bound is exactly `1`: the single row is an axis-1 row. -/
theorem axis_A : programAxisBound (airReorder (TA (K := Quad (algebraMap F K δF)))) = 1 := by
  rw [airA δF, programAxisBound, bfsA δF]
  simp [honestAx, skelNode, genSkelOp0]

theorem leaf_A : programLeafBound (airReorder (TA (K := Quad (algebraMap F K δF)))) ≤ 2 ^ 110 := by
  rw [airA δF, programLeafBound, bfsA δF]
  simp [rowNounsBound, skelNode, genSkelOp0, Noun.leaves]

theorem bfsRows_len_A : (bfsRows (airReorder (TA (K := Quad (algebraMap F K δF))))).length = 1 := by
  rw [airA δF, bfsA δF]; rfl

theorem pathTable_A_empty :
    (pathTable δF (0 : Quad (algebraMap F K δF)) (demT (δ := δF) (TA (K := Quad (algebraMap F K δF)))).cells
      (demT (δ := δF) (TA (K := Quad (algebraMap F K δF)))).preads).length = 0 := by
  have h1 : isPathAx 1 = false := by decide
  simp only [demT_A, pathTable, pathReads, List.filter_cons, h1, List.filter_nil, List.dedup_nil,
    List.flatMap_nil, List.length_nil]
  simp

/-- Padded: the axis-1 read is not a path read, so the padded path table is the single `m = 0` pad row. -/
theorem pathLen_A : pathLen (K := K) δF (TA (K := Quad (algebraMap F K δF))) = 1 := by
  have h := pathTable_A_empty (K := K) δF
  unfold pathLen pathTableP
  rw [List.length_append, h, chainRows_length, padSteps_of_eq _ _ (by
    have h1 : isPathAx 1 = false := by decide
    simp [demT_A, pathReads, h1])]
  rfl

end Generic

/-! ## Goldilocks, `K = GaloisField p 3`, `δ = 7` -/

local notation "Fp" => Nock.Field.Fp
local notation "Kc" => Nock.Field.K

open Nock.RedTeam.Batch1956 (instFactSevenNS δ7 hK3_toy ringChar_Kc hK_toy h1_32)

theorem hrun_A : Nock.evalN 1 subjA formA = some (.atom 0) := by simp [Nock.evalN, Noun.slot]

theorem hbound_A : RunBoundedBy (ringChar Fp) 1 subjA formA := ⟨.atom 0, by simp [evalGRom, Noun.slot]⟩

theorem runTree_A : runTree (K := Kc) δ7 hrun_A hbound_A = TA := romTreeA δ7 _

theorem hs_A : FieldEmbedding.BoundedBy (ringChar Fp) subjA := by
  have := goldilocks_hq; simp [FieldEmbedding.BoundedBy]; omega

theorem hf_A : FieldEmbedding.BoundedBy (ringChar Fp) formA := by
  have := goldilocks_hq; simp [FieldEmbedding.BoundedBy]; omega

theorem hsize_A : nRows (runTree (K := Kc) δ7 hrun_A hbound_A) ≤ 2 ^ 1 := by
  rw [runTree_A, nRows_A]; norm_num

theorem hrowsC_A : 3 * nRows (runTree (K := Kc) δ7 hrun_A hbound_A) < ringChar Kc := by
  rw [runTree_A, nRows_A, ringChar_Kc]; have := goldilocks_hq; omega

theorem hsizeT_A : cellLen (K := Kc) δ7 (runTree (K := Kc) δ7 hrun_A hbound_A) ≤ 2 ^ 1 := by
  rw [runTree_A, cellLen_A]; norm_num

theorem hsizeP_A : pathLen (K := Kc) δ7 (runTree (K := Kc) δ7 hrun_A hbound_A) ≤ 2 ^ 1 := by
  rw [runTree_A, pathLen_A]; norm_num

theorem hleaf_A : programLeafBound (airReorder (runTree (K := Kc) δ7 hrun_A hbound_A)) ≤ 2 ^ 110 := by
  rw [runTree_A]; exact leaf_A δ7

theorem hmemC_A : cellLen (K := Kc) δ7 (runTree (K := Kc) δ7 hrun_A hbound_A) + 1 < ringChar Fp := by
  rw [runTree_A, cellLen_A]; have := goldilocks_hq; omega

theorem hmemP_A : pathLen (K := Kc) δ7 (runTree (K := Kc) δ7 hrun_A hbound_A) + 1 < ringChar Fp := by
  rw [runTree_A, pathLen_A]; have := goldilocks_hq; omega

theorem haxis_A : programAxisBound (airReorder (runTree (K := Kc) δ7 hrun_A hbound_A)) < 2 ^ 63 := by
  rw [runTree_A, axis_A]; norm_num

theorem hN_A : nRows (runTree (K := Kc) δ7 hrun_A hbound_A) ≤ 2 ^ 31 := by
  rw [runTree_A, nRows_A]; norm_num

theorem hR_A : (bfsRows (airReorder (runTree (K := Kc) δ7 hrun_A hbound_A))).length ≤ 2 ^ 31 := by
  rw [runTree_A, bfsRows_len_A]; norm_num

theorem hnC_A : cellLen (K := Kc) δ7 (runTree (K := Kc) δ7 hrun_A hbound_A) ≤ 2 ^ 31 := by
  rw [runTree_A, cellLen_A]; norm_num

theorem hnP_A : pathLen (K := Kc) δ7 (runTree (K := Kc) δ7 hrun_A hbound_A) ≤ 2 ^ 31 := by
  rw [runTree_A, pathLen_A]; norm_num

/-- The honest joint datum of the axis-1 run. -/
def HCA : HonestVCLJ (K := Kc) δ7 1 1 1 :=
  honestVCLJ_of_run δ7 1 1 1 hrun_A hbound_A 0 0 hK3_toy goldilocks_hp le_rfl le_rfl le_rfl
    (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32)
    hsize_A hrowsC_A hsizeT_A hsizeP_A

theorem hmemRows_A : ∀ k, (HCA).V.memRows k + 1 < ringChar Fp :=
  memRows_of_run δ7 1 1 1 hrun_A hbound_A 0 hK3_toy le_rfl le_rfl le_rfl
    (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) hmemC_A hmemP_A

open Classical in
/-- **`vcl_completeness_of_run` at an AXIS-1 program, NO hypotheses**: `*[0 [0 1]]` over Goldilocks,
`K = GaloisField p 3`, `δ = 7`, `hC = hT = hP = 1`.  The honest datum is the compiler's
(`claim = ⟨0, [0 1], 0⟩`, `t = TA`), the honest rejection probability is at most `epsilonOf` of the honest-bad
events, and that `epsilonOf` is `< 2^-65`.  The honest trace fills `z1 = 1` on the single (axis-1) row. -/
theorem vcl_completeness_toy_axis1 :
    HCA.V.claim = ⟨subjA, formA, .atom 0⟩ ∧ HCA.t = TA ∧
    ((Finset.univ.filter fun χ : Coins frameVCL Kc =>
        ∃ s ∈ (CFv (K := Kc) δ7 1 1 1).honestBad HCA.toHonestVCLT ++
            (MFv (K := Kc) δ7 1 1 1).honestBad
              (jointMem δ7 HCA.toHonestVCLT (jointMemFacts_of HCA
                (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hleaf_A hmemRows_A haxis_A)),
          s.mem ((CFv (K := Kc) δ7 1 1 1).honestQ HCA.toHonestVCLT χ,
            (MFv (K := Kc) δ7 1 1 1).honestQ
              (jointMem δ7 HCA.toHonestVCLT (jointMemFacts_of HCA
                (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hleaf_A hmemRows_A
                haxis_A)) χ) χ).card : ℚ) /
        Fintype.card (Coins frameVCL Kc) ≤
      epsilonOf ((CFv (K := Kc) δ7 1 1 1).honestBad HCA.toHonestVCLT ++
        (MFv (K := Kc) δ7 1 1 1).honestBad
          (jointMem δ7 HCA.toHonestVCLT (jointMemFacts_of HCA
            (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hleaf_A hmemRows_A haxis_A))) ∧
    epsilonOf ((CFv (K := Kc) δ7 1 1 1).honestBad HCA.toHonestVCLT ++
        (MFv (K := Kc) δ7 1 1 1).honestBad
          (jointMem δ7 HCA.toHonestVCLT (jointMemFacts_of HCA
            (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hleaf_A hmemRows_A haxis_A)))
      < 1 / (2 : ℚ) ^ 65 := by
  have h1 := vcl_completeness_of_run (K := Kc) δ7 1 1 1 hrun_A hbound_A 0 0
    (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hK3_toy goldilocks_hp le_rfl le_rfl le_rfl
    (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32) (goldilocks_orbit_dvd h1_32)
    hsize_A hrowsC_A hsizeT_A hsizeP_A hleaf_A hmemC_A hmemP_A haxis_A
  have h2 := vcl_completeness_figure_of_run (K := Kc) δ7 1 1 1 hrun_A hbound_A hs_A hf_A 0 0
    hK3_toy hK_toy le_rfl le_rfl le_rfl h1_32 h1_32 h1_32
    hsize_A hrowsC_A hsizeT_A hsizeP_A hleaf_A hmemC_A hmemP_A haxis_A
    hN_A hR_A hnC_A hnP_A
  exact ⟨h1.1, h1.2.1.trans runTree_A, h1.2.2, h2⟩

/-! ## Negative control -/

/-- **NC (discriminating)**: the deleted premise `hax1` (`∀ r ∈ preads, r.2 ≠ 1`) FAILS at this program: its
demand has the axis-1 read `(0, 1)`. -/
theorem nc_old_hax1_fails_axis1_program :
    ¬ (∀ r ∈ (demT (runTree (K := Kc) δ7 hrun_A hbound_A)).preads, r.2 ≠ 1) := by
  rw [runTree_A, demT_A]; simp

end

end Nock.RedTeam.Batch1963

#print axioms Nock.RedTeam.Batch1963.vcl_completeness_toy_axis1
#print axioms Nock.RedTeam.Batch1963.demT_A
#print axioms Nock.RedTeam.Batch1963.cellLen_A
#print axioms Nock.RedTeam.Batch1963.pathLen_A
#print axioms Nock.RedTeam.Batch1963.axis_A
#print axioms Nock.RedTeam.Batch1963.runTree_A
#print axioms Nock.RedTeam.Batch1963.hbound_A
#print axioms Nock.RedTeam.Batch1963.nc_old_hax1_fails_axis1_program
