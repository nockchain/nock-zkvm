import Nock.NockVMROM.Thm54.VclL.Compute.TowerJointSizes
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier

/-!
# `HonestVCLJ` built from a compiler run

PG38 VERDICT A4 / §4: `HC : HonestVCLJ` was an orphan hypothesis (no compiled term built it).  Here it is
PRODUCED from the run `nockCompiles_zmod` already has (`hrun : evalN fuel subject formula = some result`,
`hbound : RunBoundedBy (ringChar F) fuel subject formula`), exactly as `nockCompiles_zmod` builds its tree:
`t := romTree (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))`, `hgen := romTree_spec`.

The verifier datum `vOfRun` is the run's: claim `⟨subject, formula, result⟩`, `N = nRows t`, compute nodes
`ω^i`, memory rows = the generator's table lengths (cells / path table), memory nodes `ω_k^i`, orbits from
`3·2^h ∣ |F| − 1` (`strictOrbitOf`), basis from `finrank F K = 3`.  `Ksz` and `αs` are data (unread by the
VCL honest side).

Premises of `honestVCLJ_of_run` (all public: functions of the claim and the field):
* field: `hK3 : finrank F K = 3`, `hp : 25 ≤ ringChar F`, orbit orders `hFC / hFT / hFP` with `1 ≤ h`;
* sizes: `hsize : nRows t ≤ 2^hC`, `hrowsC : 3·nRows t < ringChar K`, `hsizeT / hsizeP` (table lengths `≤ 2^h`);
*  `hpath` is GONE: the honest path table is `pathTableP` (the old chains plus an `m = 0`
  padding chain when the demand has no deep read), so `pathLen ≥ 1` always (`pathLen_pos`).
*  `hax1` is GONE: axis-1 reads are served by the chip's `z1` column (honest `z1 = [axis = 1]`).
The cell table is non-empty from the run (`demT_cells_pos`: the claim formula is a cell).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.StrictExtension

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. Orbits from the field order -/

section Orbit
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A divisor of `|F| − 1` is the exact order of an element of `F` (the unit group is cyclic). -/
theorem exists_orderOf_eq_of_dvd (m : ℕ) (hm : m ∣ Fintype.card F - 1) : ∃ ω : F, orderOf ω = m := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hcard : Nat.card Fˣ = Fintype.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  rw [hcard] at hg
  have hne : orderOf g ≠ 0 := by
    rw [hg]
    have : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  have hdvd : m ∣ orderOf g := by rw [hg]; exact hm
  refine ⟨((g ^ (orderOf g / m) : Fˣ) : F), ?_⟩
  rw [orderOf_units]
  exact orderOf_pow_orderOf_div hne hdvd

/-- **The strict orbit of height `h`** from `3·2^h ∣ |F| − 1`, coset `β = 1`. -/
def strictOrbitOf (h : ℕ) (h1 : 1 ≤ h) (hd : 3 * 2 ^ h ∣ Fintype.card F - 1) : StrictOrbitDomain F 3 h where
  ω := (exists_orderOf_eq_of_dvd _ hd).choose
  βcoset := 1
  e_pos := by norm_num
  h_pos := h1
  order_ω := (exists_orderOf_eq_of_dvd _ hd).choose_spec
  βcoset_ne_zero := one_ne_zero

end Orbit

/-! ## 2. The run's tree and its non-empty tables -/

section RunTree
variable {K : Type} [Field K]

theorem nRows_pos' (t : NTree (GenComputeRow K)) : 0 < (bfsForest [airReorder t]).length :=
  List.length_pos_of_mem ((mem_bfsForest _ _).mpr ⟨_, List.mem_singleton_self _, InTree.here _⟩)

/-- The first BFS label is the root's (up to the stamp). -/
theorem bfsLabelAt_one_skel (t : NTree (GenComputeRow K)) : (bfsLabelAt t 1).skel = t.label.skel := by
  unfold bfsLabelAt
  have : (bfsRows t)[0]? = some t.label := by
    unfold bfsRows
    rw [bfsForest_cons_eq _ (List.cons_ne_nil _ _)]
    rfl
  simp only [Nat.sub_self, this]

/-- A formula the reference interpreter evaluates is a cell. -/
theorem formula_cell_of_evalN {fuel : ℕ} {S Fm R : Noun} (h : Nock.evalN fuel S Fm = some R) :
    ∃ a b, Fm = .cell a b := by
  cases Fm with
  | atom k => cases fuel <;> simp [Nock.evalN] at h
  | cell a b => exact ⟨a, b, rfl⟩

end RunTree

section Demand
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

theorem nRows_pos (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) : 0 < nRows t := nRows_pos' t

/-- **The cell table of the run is non-empty**: the root row binds the claim formula, a cell. -/
theorem demT_cells_pos {fuel : ℕ} {S Fm R : Noun}
    {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))}
    (h : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel S Fm = .ok (t, R))
    (hFm : ∃ a b, Fm = .cell a b) : 0 < (demT t).cells.length := by
  obtain ⟨a, b, rfl⟩ := hFm
  apply List.length_pos_of_mem (a := Noun.cell a b)
  have hroot : (bfsLabelAt (airReorder t) 1).skel.formula = .cell a b := by
    rw [bfsLabelAt_one_skel, airReorder_label]
    exact (genComputeSkeleton_root_sfe h).2.1
  have hmem : bfsLabelAt (airReorder t) 1 ∈ genRowsT t := by
    unfold genRowsT
    refine List.mem_map.mpr ⟨1, List.mem_range'.mpr ⟨0, nRows_pos δ t, by simp⟩, rfl⟩
  have hbind : Noun.cell a b ∈ (demT t).binds := by
    simp only [demT, demandOfRowsD, List.mem_flatMap]
    exact ⟨_, hmem, by simp [rowBinds, hroot]⟩
  simp only [Demand.cells, closureOf, List.mem_dedup, List.mem_flatMap]
  refine ⟨Noun.cell a b, ?_, ?_⟩
  · simp only [Demand.roots, List.mem_append]; exact Or.inl (Or.inl hbind)
  · simp [cellsOf]

end Demand

/-! ## 3. The verifier datum and `HonestVCLJ` from the run -/

section Build
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (hT hP hC : ℕ)

/-- **The compiler's tree** at the run (as in `nockCompiles_zmod`). -/
def runTree {fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar F) fuel subject formula) :
    NTree (GenComputeRow (Quad (algebraMap F K δF))) :=
  romTree (K := Quad (algebraMap F K δF)) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))

/-- The cell-table length of a tree's demand. -/
def cellLen (t : NTree (GenComputeRow (Quad (algebraMap F K δF)))) : ℕ := (demT t).cells.length

/-- The path-table length of a tree's demand. -/
def pathLen (t : NTree (GenComputeRow (Quad (algebraMap F K δF)))) : ℕ :=
  (pathTableP δF (0 : Quad (algebraMap F K δF)) (demT t).cells (demT t).preads).length

/-- **The padded path table is never empty** : with no deep read the padding chain has one row;
with a deep read its chain has `|axisBits| ≥ 1` rows (the slot is defined, `demT_slot_of_gen`). -/
theorem pathLen_pos {fuel : ℕ} {S Fm R : Noun}
    {t : NTree (GenComputeRow (Quad (algebraMap F K δF)))}
    (hgen : genComputeSkeleton (K := Quad (algebraMap F K δF)) fuel S Fm = .ok (t, R)) :
    0 < pathLen (K := K) δF t := by
  unfold pathLen pathTableP
  rw [List.length_append]
  by_cases hp : pathReads (demT t).preads = []
  · rw [chainRows_length, padSteps_of_eq _ _ hp]; simp
  · obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hp
    obtain ⟨ha, hne, child, hw⟩ := deep_facts hr (demT_slot_of_gen δF hgen r hr)
    have hlen : (pathSteps r.1 (axisBits r.2)).length = (axisBits r.2).length := by
      simpa using congrArg List.length (pathSteps_sides r.1 _ (by rw [hw]; rfl))
    have hpos : 0 < (pathSteps r.1 (axisBits r.2)).length := by
      rw [hlen]; exact List.length_pos_of_ne_nil hne
    have hmem : chainRow δF (0 : Quad (algebraMap F K δF)) (demT t).cells r.1 ((demT t).preads.count r)
        (pathSteps r.1 (axisBits r.2)) 0 ∈
        pathTable δF (0 : Quad (algebraMap F K δF)) (demT t).cells (demT t).preads := by
      unfold pathTable
      refine List.mem_flatMap.mpr ⟨r, hr, ?_⟩
      unfold chainRows
      exact List.mem_map.mpr ⟨0, List.mem_range.mpr hpos, rfl⟩
    have := List.length_pos_of_mem hmem
    omega

theorem shapeV_height (k : Fin (ChipRAP.shapeV hT hP).k) :
    ((ChipRAP.shapeV hT hP).table k).height = if (k : ℕ) = 0 then hT else hP := by
  show (if (k : ℕ) = 0 then _ else _ : TableSpec).height = _
  split_ifs <;> rfl

/-- The memory orbits, per table. -/
def orbitMOf (hT1 : 1 ≤ hT) (hP1 : 1 ≤ hP)
    (hFT : 3 * 2 ^ hT ∣ Fintype.card F - 1) (hFP : 3 * 2 ^ hP ∣ Fintype.card F - 1)
    (k : Fin (ChipRAP.shapeV hT hP).k) : StrictOrbitDomain F 3 ((ChipRAP.shapeV hT hP).table k).height :=
  strictOrbitOf _ (by rw [shapeV_height]; split_ifs <;> assumption)
    (by rw [shapeV_height]; split_ifs <;> assumption)

/-- **The verifier datum of the run.** -/
def vOfRun {fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar F) fuel subject formula)
    (Ksz : ℕ) (hK3 : Module.finrank F K = 3)
    (hC1 : 1 ≤ hC) (hT1 : 1 ≤ hT) (hP1 : 1 ≤ hP)
    (hFC : 3 * 2 ^ hC ∣ Fintype.card F - 1) (hFT : 3 * 2 ^ hT ∣ Fintype.card F - 1)
    (hFP : 3 * 2 ^ hP ∣ Fintype.card F - 1)
    :
    VerifierData F K hC (ChipRAP.shapeV hT hP) where
  claim := ⟨subject, formula, result⟩
  N := nRows (runTree (K := K) δF hrun hbound)
  hN := nRows_pos δF _
  Ksz := Ksz
  basis := Module.finBasisOfFinrankEq F K hK3
  orbitC := strictOrbitOf hC hC1 hFC
  computeNodes i := (strictOrbitOf hC hC1 hFC).ω ^ (i : ℕ)
  memRows k := if (k : ℕ) = 0 then cellLen (K := K) δF (runTree (K := K) δF hrun hbound) else pathLen (K := K) δF (runTree (K := K) δF hrun hbound)
  hM k := by
    split_ifs
    · exact demT_cells_pos δF (romTree_spec _) (formula_cell_of_evalN hrun)
    · exact pathLen_pos δF (romTree_spec _)
  orbitM := orbitMOf hT hP hT1 hP1 hFT hFP
  memNodes k i := (orbitMOf hT hP hT1 hP1 hFT hFP k).ω ^ (i : ℕ)

/-- **`HonestVCLJ` from the compiler run** (PG38 A4). -/
def honestVCLJ_of_run {fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar F) fuel subject formula)
    (Ksz : ℕ) (αs : Quad (algebraMap F K δF)) (hK3 : Module.finrank F K = 3)
    (hp : 25 ≤ ringChar F)
    (hC1 : 1 ≤ hC) (hT1 : 1 ≤ hT) (hP1 : 1 ≤ hP)
    (hFC : 3 * 2 ^ hC ∣ Fintype.card F - 1) (hFT : 3 * 2 ^ hT ∣ Fintype.card F - 1)
    (hFP : 3 * 2 ^ hP ∣ Fintype.card F - 1)
    (hsize : nRows (runTree (K := K) δF hrun hbound) ≤ 2 ^ hC)
    (hrowsC : 3 * nRows (runTree (K := K) δF hrun hbound) < ringChar K)
    (hsizeT : cellLen (K := K) δF (runTree (K := K) δF hrun hbound) ≤ 2 ^ hT)
    (hsizeP : pathLen (K := K) δF (runTree (K := K) δF hrun hbound) ≤ 2 ^ hP) :
    HonestVCLJ (K := K) δF hT hP hC where
  V := vOfRun δF hT hP hC hrun hbound Ksz hK3 hC1 hT1 hP1 hFC hFT hFP
  fuel := fuel
  t := runTree δF hrun hbound
  hgen := romTree_spec _
  αs := αs
  hN := rfl
  hnodes _ := rfl
  hsize := hsize
  hp := hp
  hrowsC := hrowsC
  hC0 := by simp [vOfRun, tC, cellLen]
  hP0 := by simp [vOfRun, tP, pathLen]
  hmnodes _ _ := rfl
  hsizeM k := by
    show (if (k : ℕ) = 0 then _ else _) ≤ 2 ^ ((ChipRAP.shapeV hT hP).table k).height
    rw [shapeV_height]
    split_ifs
    · exact hsizeT
    · exact hsizeP

/-- `hmemRows` of `vcl_completeness'` from the two table premises. -/
theorem memRows_of_run {fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar F) fuel subject formula)
    (Ksz : ℕ) (hK3 : Module.finrank F K = 3)
    (hC1 : 1 ≤ hC) (hT1 : 1 ≤ hT) (hP1 : 1 ≤ hP)
    (hFC : 3 * 2 ^ hC ∣ Fintype.card F - 1) (hFT : 3 * 2 ^ hT ∣ Fintype.card F - 1)
    (hFP : 3 * 2 ^ hP ∣ Fintype.card F - 1)
    (hmemC : cellLen (K := K) δF (runTree (K := K) δF hrun hbound) + 1 < ringChar F)
    (hmemP : pathLen (K := K) δF (runTree (K := K) δF hrun hbound) + 1 < ringChar F) :
    ∀ k, (vOfRun (K := K) δF hT hP hC hrun hbound Ksz hK3 hC1 hT1 hP1 hFC hFT hFP).memRows k + 1
      < ringChar F := by
  intro k
  show (if (k : ℕ) = 0 then _ else _) + 1 < _
  split_ifs
  · exact hmemC
  · exact hmemP

end Build

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
