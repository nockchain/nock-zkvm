/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestMh2.lean

  Additive.

  The cell twin's public is `Re ρ₃ + yH = Σ_j mh_j / den_j` (`pubsCH`), where `yH` is the walk twin's
  export-consume total (one consume per walk row, `xKeyH`).

  * `consumedH2` / `walkConsH2`: the compute side's consumed export records and the walk rows' consumed
    export keys, both over `(demandH2 rows).cells`;
  * `mhH2 rows n`: the count of `expKey cells n` in their concatenation;
  * `export_total_link2`: for any weight `f`, the consumed total (compute + walk) is the `mhH2`-weighted
    provided total over the cell list (`sum_reindex`; `expKey` is injective on the cells);
  * `run_rows_pks`: the path-key shape `PKS` of every BFS row of a run (to use `handle_cells_memH2`);
  * positive control `toy1_mhH_ne_mhH2`: at the toy `*[0 [1 0]]` the formula cell has `mhH = 1` and
    `mhH2 = 2`: the walk row matters (kernel `decide`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestMh
import Nock.NockVMROM.Thm54.VclL.Handle.HonestDemand2
import Nock.NockVMROM.Thm54.VclL.Handle.HonestToys

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.SemanticStrategy ComputeTable

noncomputable section

section Pks
variable {K : Type} [Field K]

/-- **The path-key shape of every BFS row of a run** (`inTree_pathKeys` through `airReorder`). -/
theorem run_rows_pks {fuel : ℕ} {subject formula result : Noun} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ g ∈ bfsRows (airReorder t), PKS g := by
  intro g hg
  unfold bfsRows at hg
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ u).mp hu
  simp only [List.mem_singleton] at hc
  subst hc
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label t u hin
  rw [hl]
  exact inTree_pathKeys h u0 hu0

end Pks

section Mh2
variable {K F : Type} [Field K] [Field F]

/-- **The compute side's consumed export records over `demandH2`'s cell list.** -/
def consumedH2 (rows : List (GenComputeRow K)) : List (F × (F × F) × (F × F)) :=
  rows.flatMap fun g => (exportEntries (rowOfSkelH g.skel)).map (entryRec (demandH2 rows).cells)

/-- **The walk rows' consumed export keys** (one per walk row, at its node). -/
def walkConsH2 (rows : List (GenComputeRow K)) : List (F × (F × F) × (F × F)) :=
  (walkRows (demandH2 rows).cells (demandH2 rows).preads).map fun w =>
    expKey (demandH2 rows).cells w.label.node

/-- **The honest handle multiplicity of the cell twin over `demandH2`**: compute consumers plus walk-row
consumers of the export key of `n`. -/
def mhH2 [DecidableEq F] (rows : List (GenComputeRow K)) (n : Noun) : ℕ :=
  (consumedH2 (F := F) rows ++ walkConsH2 rows).count (expKey (demandH2 rows).cells n)

theorem mhH2_eq [DecidableEq F] (rows : List (GenComputeRow K)) (n : Noun) :
    mhH2 (F := F) rows n = (consumedH2 (F := F) rows).count (expKey (demandH2 rows).cells n) +
      (walkConsH2 (F := F) rows).count (expKey (demandH2 rows).cells n) := by
  unfold mhH2; exact List.count_append ..

/-- **The export total link over `demandH2`, with the walk consumers.** -/
theorem export_total_link2 {M : Type} [AddCommMonoid M] [DecidableEq F]
    (rows : List (GenComputeRow K))
    (hsem : ∀ g ∈ rows, (rowOfSkel g.skel).Sem) (hpk : ∀ g ∈ rows, PKS g)
    (hlen : (demandH2 rows).cells.length < ringChar F)
    (hwn : ∀ w ∈ walkRows (demandH2 rows).cells (demandH2 rows).preads,
      w.label.node ∈ (demandH2 rows).cells)
    (f : F × (F × F) × (F × F) → M) :
    ((consumedH2 (F := F) rows).map f).sum + ((walkConsH2 (F := F) rows).map f).sum =
      ((demandH2 rows).cells.map fun n =>
        (mhH2 (F := F) rows n) • f (expKey (demandH2 rows).cells n)).sum := by
  rw [← List.sum_append, ← List.map_append]
  refine sum_reindex (demandH2 rows).cells (closureOf_nodup _) (expKey (demandH2 rows).cells) ?_ f _ ?_
  · intro a ha b hb h
    have h1 := congrArg Prod.fst h
    simp only [expKey] at h1
    have hia := List.idxOf_lt_length_iff.mpr ha
    have hib := List.idxOf_lt_length_iff.mpr hb
    exact (honest_handle_eq_iff (demandH2 rows) ha hb).mp
      (cast_inj_of_lt (hia.trans hlen) (hib.trans hlen) h1)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [consumedH2, List.mem_flatMap, List.mem_map] at hx
      obtain ⟨g, hg, e, he, rfl⟩ := hx
      have he' : e ∈ exportEntries (rowOfSkel g.skel) := by rw [← exportEntries_H]; exact he
      have hcell := exportEntries_cell _ (hsem g hg) e he'
      refine ⟨e.1, handle_cells_memH2 rows hpk hg e.1 (entry_parent_mem _ e he)
        (by rw [hcell]; rfl), ?_⟩
      exact (entryRec_eq_expKey _ _ (hsem g hg) e he').symm
    · simp only [walkConsH2, List.mem_map] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨w.label.node, hwn w hw, rfl⟩

/-- `export_total_link2` at the LogUp weight `1 / recDen`. -/
theorem export_total_link2_inv {L : Type} [Field L] [Algebra F L] [DecidableEq F]
    (rows : List (GenComputeRow K))
    (hsem : ∀ g ∈ rows, (rowOfSkel g.skel).Sem) (hpk : ∀ g ∈ rows, PKS g)
    (hlen : (demandH2 rows).cells.length < ringChar F)
    (hwn : ∀ w ∈ walkRows (demandH2 rows).cells (demandH2 rows).preads,
      w.label.node ∈ (demandH2 rows).cells) (ρ γ : L) :
    ((consumedH2 (F := F) rows).map fun k => (recDen ρ γ k)⁻¹).sum +
        ((walkConsH2 (F := F) rows).map fun k => (recDen ρ γ k)⁻¹).sum =
      ((demandH2 rows).cells.map fun n =>
        (mhH2 (F := F) rows n : L) * (recDen ρ γ (expKey (F := F) (demandH2 rows).cells n))⁻¹).sum := by
  rw [export_total_link2 rows hsem hpk hlen hwn (fun k => (recDen ρ γ k)⁻¹)]
  simp [nsmul_eq_mul]

end Mh2

/-! ## Positive control: the walk term matters -/

section Toy

/-- The formula cell of the toy `*[0 [1 0]]`. -/
abbrev toy1F : Noun := .cell (.atom 1) (.atom 0)

/-- **Positive control** (kernel `decide`): at `*[0 [1 0]]` the formula cell is the one row of the cell
table; the compute side consumes its export key once (`mhH = 1`), and the one (dummy) walk row consumes it
again (`mhH2 = 2`).  So `mhH ≠ mhH2`: the walk consumers are not optional. -/
theorem toy1_cells_mhH :
    (demandH2 [toy1Row]).cells = [toy1F] ∧ (demandH2 [toy1Row]).preads = [] ∧
    mhH (F := Z67) [toy1Row] toy1F = 1 ∧
    (consumedH2 (F := Z67) [toy1Row]).count (expKey (demandH2 [toy1Row]).cells toy1F) = 1 := by
  decide +kernel

/-- The toy's walk: no path read, so the one dummy trie at the first cell. -/
theorem toy1_walkRows :
    walkRows (demandH2 [toy1Row]).cells (demandH2 [toy1Row]).preads = [trie toy1F toy1F [] []] := by
  rw [toy1_cells_mhH.1, toy1_cells_mhH.2.1]
  have ht : (trie toy1F toy1F [] []).children = [] := by
    simp [toy1F, trie, cont, contT, sideTails]
  simp only [walkRows, walkForest, walkRoots, pathKind, List.filter_nil, List.map_nil, List.dedup_nil,
    if_true, List.headD_cons]
  rw [bfsForest_cons_eq _ (by simp)]
  simp [ht, bfsForest_nil]

/-- **Positive control**: at `*[0 [1 0]]` the formula cell is the one row of the cell table; the compute
side consumes its export key once (`mhH = 1`), and the one (dummy) walk row consumes it again
(`mhH2 = 2`).  So `mhH ≠ mhH2`: the walk consumers are not optional. -/
theorem toy1_mhH_ne_mhH2 :
    mhH (F := Z67) [toy1Row] toy1F = 1 ∧ mhH2 (F := Z67) [toy1Row] toy1F = 2 := by
  refine ⟨toy1_cells_mhH.2.2.1, ?_⟩
  rw [mhH2_eq, toy1_cells_mhH.2.2.2]
  have hw : walkConsH2 (F := Z67) [toy1Row] = [expKey (demandH2 [toy1Row]).cells toy1F] := by
    unfold walkConsH2
    rw [toy1_walkRows]
    simp [(trie_label toy1F toy1F [] []).1]
  rw [hw]; simp

end Toy

end

end Nock.NockVMROM.Thm54.VclL.Handle
