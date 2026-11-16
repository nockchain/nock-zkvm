import Nock.NockVMROM.Thm54.VclL.Compute.TowerJointHonest
import Nock.NockVMROM.Thm54.VclL.Compute.TowerJointReqFacts

/-!
# `JointMemFacts` discharged

`HonestVCLJ extends HonestVCLT` adds the memory-shape definitional fields (`hC0`, `hP0`, `memNodes = ω^i`) and
the public size check `hsizeM` (`V.Checks.hcapM`).  `hadj` / `hinj` are derived.  `hrank` is derived from the
public size condition `hleaf` (`programLeafBound ≤ 2^110`), `h62` from `haxis` (`programAxisBound < 2^63`)
(stated over EVERY read of the demand, `demT_depth_le`).  `hrows` is the public size condition `hmemRows`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

noncomputable section

section Sizes
variable {K : Type} [Field K]

/-- Request facts at every BFS row of the AIR-ordered tree of an accepted run. -/
theorem rowReq {fuel : ℕ} {S Fm : Noun} {t : NTree (GenComputeRow K)} {r : Noun}
    (h : genComputeSkeleton (K := K) fuel S Fm = .ok (t, r))
    {g : GenComputeRow K} (hg : g ∈ bfsRows (airReorder t)) :
    ∀ req ∈ g.requests, (req.axis ≤ 3 ∨ req.axis = honestAx g.skel) ∧
      ∃ v, InTree (airReorder t) v ∧ req.root.leaves ≤ rowNounsBound v.label := by
  unfold bfsRows at hg
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ u).mp hu
  simp only [List.mem_singleton] at hc
  subst hc
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label t u hin
  intro req hreq
  obtain ⟨h1, v, hv, h3⟩ := (VclL.Compute.gen_reqFacts h).2 u0 hu0 req (by rw [← hl]; exact hreq)
  refine ⟨by rw [hl]; exact h1, ?_⟩
  obtain ⟨v', hv', hl'⟩ := labelsFrom_of_airReorder t v hv
  exact ⟨v', hv', by rw [← hl']; exact h3⟩

theorem rowBound_le {t : NTree (GenComputeRow K)} {B : ℕ} (hB : programLeafBound t ≤ B)
    {v : NTree (GenComputeRow K)} (hv : InTree t v) : rowNounsBound v.label ≤ B := by
  refine foldl_sup_le_of_le (bfsRows t) rowNounsBound hB v.label ?_
  exact List.mem_map.mpr ⟨v, (mem_bfsForest [t] v).mpr ⟨t, List.mem_singleton_self t, hv⟩, rfl⟩

theorem bfsRows_mem_of_inTree {t : NTree (GenComputeRow K)} {v : NTree (GenComputeRow K)}
    (hv : InTree t v) : v.label ∈ bfsRows t :=
  List.mem_map.mpr ⟨v, (mem_bfsForest [t] v).mpr ⟨t, List.mem_singleton_self t, hv⟩, rfl⟩


end Sizes

section Demand
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

theorem genRowsT_mem (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) {g : GenComputeRow (Quad (algebraMap F K δ))}
    (hg : g ∈ genRowsT t) :
    ∃ g0 ∈ bfsRows (airReorder t), g.requests = g0.requests ∧ g.skel = g0.skel := by
  simp only [genRowsT, List.mem_map] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  have hi' := lt_bfsRows_of_mem_range' (t := airReorder t) hi
  exact ⟨_, List.getElem_mem hi', bfsLabelAt_requests _ i hi', bfsLabelAt_skel _ i hi'⟩

/-- **The root leaves of the demand** are bounded by the window `B ≥ programLeafBound`. -/
theorem demT_roots_leaves {fuel : ℕ} {S Fm R : Noun}
    {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))}
    (h : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel S Fm = .ok (t, R))
    {B : ℕ} (hB : programLeafBound (airReorder t) ≤ B) :
    ∀ n ∈ (demT t).roots, n.leaves ≤ B := by
  intro n hn
  simp only [Demand.roots, List.mem_append, List.mem_map] at hn
  rcases hn with (hn | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩
  · simp only [demT, demandOfRowsD, List.mem_flatMap] at hn
    obtain ⟨g, hg, hn⟩ := hn
    obtain ⟨g0, hg0, -, hs⟩ := genRowsT_mem δ t hg
    have hb := foldl_sup_le_of_le (bfsRows (airReorder t)) rowNounsBound hB g0 hg0
    simp only [rowBinds, hs, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl
    · exact (leaves_le_rowB_subject g0).trans hb
    · exact (leaves_le_rowB_formula g0).trans hb
  all_goals
    obtain ⟨g, hg, hr⟩ := demT_key_mem (t := t) (by first | exact Or.inl hr | exact Or.inr hr)
    obtain ⟨g0, hg0, hq, -⟩ := genRowsT_mem δ t hg
    simp only [rowSlotKeys, hq, List.mem_map] at hr
    obtain ⟨req, hreq, rfl⟩ := hr
    obtain ⟨-, v, hv, h3⟩ := rowReq h hg0 req hreq
    exact h3.trans (rowBound_le hB hv)

theorem internal_le_of_mem_cellsOf : ∀ (root n : Noun), n ∈ cellsOf root → n.internal ≤ root.internal
  | .atom _, n, h => by simp [cellsOf] at h
  | .cell a b, n, h => by
    simp only [cellsOf, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact le_refl _
    · have := internal_le_of_mem_cellsOf a n h
      simp only [Noun.internal]; omega
    · have := internal_le_of_mem_cellsOf b n h
      simp only [Noun.internal]; omega

/-- **`hrank` from the public size condition `hleaf`.** -/
theorem demT_rank_lt {fuel : ℕ} {S Fm R : Noun}
    {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))}
    (h : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel S Fm = .ok (t, R))
    (hleaf : programLeafBound (airReorder t) ≤ 2 ^ 110) :
    ∀ n ∈ (demT t).cells, rankOf n < 2 ^ 110 := by
  intro n hn
  simp only [Demand.cells, closureOf, List.mem_dedup, List.mem_flatMap] at hn
  obtain ⟨root, hroot, hn⟩ := hn
  have hl := demT_roots_leaves δ h hleaf root hroot
  have h1 := internal_le_of_mem_cellsOf root n hn
  have h2 := (Noun.pbt_size root).2
  show n.internal < 2 ^ 110
  have : 0 < 2 ^ 110 := by positivity
  omega

/-- **`h62` over every read of the demand (export and path kinds, SHD-A), from the public size condition `haxis`.** -/
theorem demT_depth_le {fuel : ℕ} {S Fm R : Noun}
    {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))}
    (h : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel S Fm = .ok (t, R))
    (haxis : programAxisBound (airReorder t) < 2 ^ 63) :
    ∀ r, (r ∈ (demT t).reads ∨ r ∈ (demT t).preads) → depthOf r.2 ≤ 62 := by
  intro r hr
  obtain ⟨g, hg, hr⟩ := demT_key_mem (t := t) hr
  obtain ⟨g0, hg0, hq, -⟩ := genRowsT_mem δ t hg
  simp only [rowSlotKeys, hq, List.mem_map] at hr
  obtain ⟨req, hreq, rfl⟩ := hr
  obtain ⟨hax, -⟩ := rowReq h hg0 req hreq
  refine depthOf_le_of_lt_pow 62 _ ?_
  rcases hax with h3 | h3
  · exact lt_of_le_of_lt h3 (by norm_num)
  · rw [h3]
    exact lt_of_le_of_lt (rowAx_le_programAxisBound (airReorder t) g0 hg0) haxis

end Demand

section Joint2
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (hT hP hC : ℕ)

/-- **The honest datum of the joint compute-memory run**: `HonestVCLT` at the memory shape `shapeV hT hP`,
with the memory-side fields that are definitional for the honest verifier datum:
`hC0` / `hP0` (the memory heights are the generator's table lengths), `hmnodes` (the memory nodes are the
orbit points `ω^i`, as `hnodes` for compute) and `hsizeM` (public size check `V.Checks.hcapM`:
`memRows ≤ 2^height`, as `hsize` for compute). -/
structure HonestVCLJ extends HonestVCLT F K δF hC (ChipRAP.shapeV hT hP) where
  hC0 : V.memRows (tC hT hP) = (demT t).cells.length
  hP0 : V.memRows (tP hT hP) =
    (pathTableP δF (0 : Quad (algebraMap F K δF)) (demT t).cells (demT t).preads).length
  hmnodes : ∀ (k : Fin (ChipRAP.shapeV hT hP).k) (i : Fin (V.memRows k)), V.memNodes k i = (V.orbitM k).ω ^ (i : ℕ)
  /-- Public size check (`VerifierData.Checks.hcapM`). -/
  hsizeM : ∀ k : Fin (ChipRAP.shapeV hT hP).k, V.memRows k ≤ 2 ^ ((ChipRAP.shapeV hT hP).table k).height

variable {δF hT hP hC}

theorem HonestVCLJ.hadj (HJ : HonestVCLJ (K := K) δF hT hP hC) (k : Fin (ChipRAP.shapeV hT hP).k) :
    HJ.V.AdjacentM k := by
  intro i hi
  rw [HJ.hmnodes k ⟨(i : ℕ) + 1, hi⟩, HJ.hmnodes k i]
  exact pow_succ _ _

theorem HonestVCLJ.hinj (HJ : HonestVCLJ (K := K) δF hT hP hC) (k : Fin (ChipRAP.shapeV hT hP).k) :
    Function.Injective (HJ.V.memNodes k) := by
  intro a b hab
  rw [HJ.hmnodes k a, HJ.hmnodes k b] at hab
  have hord : orderOf (HJ.V.orbitM k).ω = 3 * 2 ^ ((ChipRAP.shapeV hT hP).table k).height :=
    (HJ.V.orbitM k).order_ω
  have hle := HJ.hsizeM k
  apply Fin.ext
  refine pow_injOn_Iio_orderOf ?_ ?_ hab
  · show (a : ℕ) < orderOf _
    rw [hord]; have := a.isLt; omega
  · show (b : ℕ) < orderOf _
    rw [hord]; have := b.isLt; omega

/-- **`JointMemFacts` from the field parameters and the three public size conditions.**
* `hF`, `hq`: field parameters (`PrimeFieldElems F`, `2^63 < char F`);
* `hleaf`: public size condition, `programLeafBound (airReorder t) ≤ 2^110` (`→ hrank`);
* `hmemRows`: public size condition, `memRows + 1 < char F` (`= hrows`);
* `haxis`: public size condition, `programAxisBound (airReorder t) < 2^63` (`→ h62`). -/
theorem jointMemFacts_of (HJ : HonestVCLJ (K := K) δF hT hP hC)
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hleaf : programLeafBound (airReorder HJ.t) ≤ 2 ^ 110)
    (hmemRows : ∀ k, HJ.V.memRows k + 1 < ringChar F)
    (haxis : programAxisBound (airReorder HJ.t) < 2 ^ 63) :
    JointMemFacts δF hT hP hC HJ.toHonestVCLT where
  hF := hF
  hq := hq
  hrows := hmemRows
  hadj := HJ.hadj
  hinj := HJ.hinj
  hrank := demT_rank_lt δF HJ.hgen hleaf
  h62 := fun r hr => by
    have : r ∈ (demT HJ.t).reads ∨ r ∈ (demT HJ.t).preads := by
      unfold pathReads at hr
      exact Or.inr (List.mem_filter.mp (List.mem_dedup.mp hr)).1
    exact demT_depth_le δF HJ.hgen haxis r this
  hC0 := HJ.hC0
  hP0 := HJ.hP0

end Joint2

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
