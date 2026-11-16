/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestSizeH.lean

  Additive; no handle
  accumulator, coin or IO summand is touched.

  * `hrank` from `hleafH` (every handle noun has `≤ 2^110` leaves; the subject / formula / evaluation handles
    are bounded by `programLeafBound`, `handleNouns_sfe_leaves`; the child-result and hosted-slot handles
    are the named residual condition);
  * `h62` from `haxisH` (every consumed entry's axis is `< 2^63`);
  * `hrows` / `hkp` from the two table-length conditions `hmemC`, `hmemW` (as `memRowsW_of_run`, `kpW_of_run`).
  `honestVCLW_of_demandH2` assembles the datum (with `hadj`, `hinj` from `hmnodes`, `hsizeM` as in
  `HonestVCLJW.hadj / hinj`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestPinH
import Nock.NockVMROM.Thm54.VclL.Compute.TowerJointSizes

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD Nock.NockVMROM.Thm54.VclL.Compute
open Module

noncomputable section

section Sizes
variable {Kg : Type} [Field Kg]

/-- **`hrank` for `demandH2`.** -/
theorem demandH2_rank_lt (rows : List (GenComputeRow Kg))
    (hleafH : ∀ n ∈ rows.flatMap handleNouns, n.leaves ≤ 2 ^ 110) :
    ∀ n ∈ (demandH2 rows).cells, rankOf n < 2 ^ 110 := by
  intro n hn
  simp only [Demand.cells, closureOf, List.mem_dedup, List.mem_flatMap] at hn
  obtain ⟨root, hroot, hn⟩ := hn
  have hl : root.leaves ≤ 2 ^ 110 := by
    simp only [Demand.roots, demandH2, List.map_nil, List.append_nil, List.mem_append, List.mem_map] at hroot
    rcases hroot with hr | ⟨r, hr, rfl⟩
    · exact hleafH root hr
    · exact hleafH _ (walkReads_root_mem rows r hr)
  have h1 := internal_le_of_mem_cellsOf root n hn
  have h2 := (Noun.pbt_size root).2
  show n.internal < 2 ^ 110
  have : 0 < 2 ^ 110 := by positivity
  omega

/-- The subject / formula / evaluation handles of a row are bounded by `programLeafBound`. -/
theorem handleNouns_sfe_leaves (t : NTree (GenComputeRow Kg)) {B : ℕ} (hB : programLeafBound (airReorder t) ≤ B)
    {g : GenComputeRow Kg} (hg : g ∈ bfsRows (airReorder t)) :
    (rowOfSkel g.skel).s.leaves ≤ B ∧ (rowOfSkel g.skel).f.leaves ≤ B ∧ (rowOfSkel g.skel).e.leaves ≤ B := by
  have hb := foldl_sup_le_of_le (bfsRows (airReorder t)) rowNounsBound hB g hg
  have h1 : (rowOfSkel g.skel).s = g.skel.subject := by unfold rowOfSkel; split <;> rfl
  have h2 : (rowOfSkel g.skel).f = g.skel.formula := rowOfSkel_f _
  have h3 : (rowOfSkel g.skel).e = g.skel.evaluation := by unfold rowOfSkel; split <;> rfl
  rw [h1, h2, h3]
  refine ⟨(leaves_le_rowB_subject g).trans hb, (leaves_le_rowB_formula g).trans hb, ?_⟩
  exact (by unfold rowNounsBound; exact le_sup_right : g.skel.evaluation.leaves ≤ rowNounsBound g).trans hb

/-- **`h62` for `demandH2`**: every path read has `≤ 62` edges when every consumed axis is `< 2^63`. -/
theorem demandH2_depth_le (rows : List (GenComputeRow Kg))
    (haxisH : ∀ x ∈ consEntriesAll rows, x.2.1 < 2 ^ 63) :
    ∀ r ∈ pathReads (demandH2 rows).preads, depthOf r.2 ≤ 62 := by
  intro r hr
  unfold pathReads at hr
  have hr' := (List.mem_filter.mp (List.mem_dedup.mp hr)).1
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr'
  exact depthOf_le_of_lt_pow 62 _ (haxisH x hx)

end Sizes

section Datum
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC : ℕ}

/-- `hrows` from the two table-length conditions. -/
theorem hrows_of_lengths (V : VerifierData F K hC (shapeVW hT hP)) (d : Demand)
    (hC0 : V.memRows (tCW hT hP) = d.cells.length)
    (hW0 : V.memRows (tWW hT hP) = (walkRows d.cells d.preads).length)
    (hmemC : d.cells.length + 1 < ringChar F)
    (hmemW : (walkRows d.cells d.preads).length + 1 < ringChar F) :
    ∀ t, V.memRows t + 1 < ringChar F := by
  intro t
  obtain ⟨i, hi⟩ := t
  have hk : (shapeVW hT hP).k = 2 := rfl
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · exact (congrArg (· + 1) hC0).trans_lt hmemC
  · exact (congrArg (· + 1) hW0).trans_lt hmemW

/-- `hadj` from the memory nodes `ω^i`. -/
theorem memAdj_of (V : VerifierData F K hC (shapeVW hT hP))
    (hmnodes : ∀ (k : Fin (shapeVW hT hP).k) (i : Fin (V.memRows k)), V.memNodes k i = (V.orbitM k).ω ^ (i : ℕ))
    (k : Fin (shapeVW hT hP).k) : V.AdjacentM k := by
  intro i hi
  rw [hmnodes k ⟨(i : ℕ) + 1, hi⟩, hmnodes k i]
  exact pow_succ _ _

/-- `hinj` from the memory nodes `ω^i` and the height check. -/
theorem memInj_of (V : VerifierData F K hC (shapeVW hT hP))
    (hmnodes : ∀ (k : Fin (shapeVW hT hP).k) (i : Fin (V.memRows k)), V.memNodes k i = (V.orbitM k).ω ^ (i : ℕ))
    (hsizeM : ∀ k : Fin (shapeVW hT hP).k, V.memRows k ≤ 2 ^ ((shapeVW hT hP).table k).height)
    (k : Fin (shapeVW hT hP).k) : Function.Injective (V.memNodes k) := by
  intro a b hab
  rw [hmnodes k a, hmnodes k b] at hab
  have hord : orderOf (V.orbitM k).ω = 3 * 2 ^ ((shapeVW hT hP).table k).height :=
    (V.orbitM k).order_ω
  have hle := hsizeM k
  apply Fin.ext
  refine pow_injOn_Iio_orderOf ?_ ?_ hab
  · show (a : ℕ) < orderOf _
    rw [hord]; have := a.isLt; omega
  · show (b : ℕ) < orderOf _
    rw [hord]; have := b.isLt; omega

/-- **The honest walk memory datum over `demandH2 rows`**, with every size field derived from the public
size conditions (`hleafH`, `haxisH`, `hmemC`, `hmemW`) and the memory shape facts. -/
def honestVCLW_of_demandH2 (rows : List (GenComputeRow Kg))
    (V : VerifierData F K hC (shapeVW hT hP))
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hmnodes : ∀ (k : Fin (shapeVW hT hP).k) (i : Fin (V.memRows k)), V.memNodes k i = (V.orbitM k).ω ^ (i : ℕ))
    (hsizeM : ∀ k : Fin (shapeVW hT hP).k, V.memRows k ≤ 2 ^ ((shapeVW hT hP).table k).height)
    (hC0 : V.memRows (tCW hT hP) = (demandH2 rows).cells.length)
    (hW0 : V.memRows (tWW hT hP) = (walkRows (demandH2 rows).cells (demandH2 rows).preads).length)
    (hleafH : ∀ n ∈ rows.flatMap handleNouns, n.leaves ≤ 2 ^ 110)
    (haxisH : ∀ x ∈ consEntriesAll rows, x.2.1 < 2 ^ 63)
    (hmemC : (demandH2 rows).cells.length + 1 < ringChar F)
    (hmemW : krW (demandH2 rows).cells (demandH2 rows).preads +
      (walkRows (demandH2 rows).cells (demandH2 rows).preads).length < ringChar F) :
    HonestVCLW (K := K) δF hT hP hC (krW (demandH2 rows).cells (demandH2 rows).preads) where
  V := V
  d := demandH2 rows
  hF := hF
  hq := hq
  hrows := hrows_of_lengths V _ hC0 hW0 hmemC
    (by have := one_le_krW (demandH2 rows).cells (demandH2 rows).preads; omega)
  hadj := memAdj_of V hmnodes
  hinj := memInj_of V hmnodes hsizeM
  hrank := demandH2_rank_lt rows hleafH
  h62 := demandH2_depth_le rows haxisH
  hC0 := hC0
  hW0 := hW0
  hkr := rfl
  hkp := by rw [hW0]; exact hmemW

end Datum

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
