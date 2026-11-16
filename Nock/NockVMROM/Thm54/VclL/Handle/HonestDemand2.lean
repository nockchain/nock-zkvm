/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestDemand2.lean

  Additive: a NEW worker `demandH2` beside `demandH` (no `Gen.lean` edit, no existing module edited).

  * `demandH2 rows` = `demandH rows` with the walk reads `walkReadsH rows` (OP0/OP9 reads plus the OP5
    first-difference pair reads) in place of `rows.flatMap rowPathKeys`.
  * `demandH2_cells_mem_iff` / `demandH2_cells_perm`: the cells are unchanged AS A SET (membership, and
    `List.Perm` since both are duplicate-free).  Exact LIST equality is NOT claimed (the root order feeds
    `dedup`; serials are positions, so a literal swap would renumber): UNCONFIRMED and probably false.
  * `demandH2_balance`: `compute_walk_balance` for the walk built from `demandH2`'s `preads`.
  * `pathKind_rowPathKeys_eq`: the OP0 / OP9 part of `walkReadsH` equals `rowPathKeys` up to the
    `pathKind` filter (axis 1 reads, which are `z1` local and carry no path row, are in `rowPathKeys`
    but not in `walkReadsH`).  Literal equality is false for that reason.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.PathKeyShape
import Nock.NockVMROM.Thm54.VclL.Handle.PathConsH
import Nock.NockVMROM.Thm54.VclL.Handle.HonestRowsH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.SemanticStrategy

noncomputable section

section D2
variable {K : Type} [Field K]

/-- **The VS demand with the OP5 pair reads**: the binds of `demandH`, the walk reads of
`walkReadsH` (OP0, OP9 and the OP5 first-difference pair). -/
def demandH2 (rows : List (GenComputeRow K)) : Demand :=
  ⟨rows.flatMap handleNouns, [], walkReadsH rows⟩

/-- The OP0 / OP9 entries of an effective row. -/
def pathEntries (r : RowN) : List PEnt :=
  (if r.op = 0 ∧ r.ft ≠ .atom 1 then [(r.s, atomVal r.ft, r.e)] else []) ++
  (if r.op = 9 ∧ r.fth ≠ .atom 1 then [(r.sf1, atomVal r.fth, r.m)] else [])

/-- The OP5 pair entries of an effective row. -/
def pairEntries (r : RowN) : List PEnt :=
  if r.op = 5 ∧ r.e = .atom 1 ∧ (fdN r.sf1 r.sf2).1 ≠ [] then
    [(r.sf1, atomVal r.m, r.ftth), (r.sf2, atomVal r.m, r.fttt)] else []

theorem consEntries_split (r : RowN) : consEntries r = pathEntries r ++ pairEntries r := rfl

theorem hn_op (r : RowN) : (hn r).op = r.op := by unfold hn; split_ifs <;> rfl
theorem hn_s (r : RowN) : (hn r).s = r.s := by unfold hn; split_ifs <;> rfl
theorem hn_sf1 (r : RowN) : (hn r).sf1 = r.sf1 := by unfold hn; split_ifs <;> rfl
theorem hn_sf2 (r : RowN) : (hn r).sf2 = r.sf2 := by unfold hn; split_ifs <;> rfl
theorem rH_s (sk : ComputeRowSkeleton) : (rowOfSkelH sk).s = (rowOfSkel sk).s := by
  unfold rowOfSkelH; by_cases h : (rowOfSkel sk).op = 3 <;> simp [h]
theorem rH_sf1 (sk : ComputeRowSkeleton) : (rowOfSkelH sk).sf1 = (rowOfSkel sk).sf1 := by
  unfold rowOfSkelH; by_cases h : (rowOfSkel sk).op = 3 <;> simp [h]
theorem rH_sf2 (sk : ComputeRowSkeleton) : (rowOfSkelH sk).sf2 = (rowOfSkel sk).sf2 := by
  unfold rowOfSkelH; by_cases h : (rowOfSkel sk).op = 3 <;> simp [h]

/-- Roots of the consumed entries of an honest row are among its `s / sf1 / sf2`. -/
theorem consEntries_root_mem (sk : ComputeRowSkeleton) :
    ∀ x ∈ consEntries (hn (rowOfSkelH sk)),
      x.1 = (rowOfSkel sk).s ∨ x.1 = (rowOfSkel sk).sf1 ∨ x.1 = (rowOfSkel sk).sf2 := by
  intro x hx
  have hs' : (hn (rowOfSkelH sk)).s = (rowOfSkel sk).s := by rw [hn_s, rH_s]
  have h1' : (hn (rowOfSkelH sk)).sf1 = (rowOfSkel sk).sf1 := by rw [hn_sf1, rH_sf1]
  have h2' : (hn (rowOfSkelH sk)).sf2 = (rowOfSkel sk).sf2 := by rw [hn_sf2, rH_sf2]
  generalize hn (rowOfSkelH sk) = r at *
  unfold consEntries at hx
  simp only [List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · split at hx
    · simp at hx; subst hx; exact Or.inl hs'
    · simp at hx
  · split at hx
    · simp at hx; subst hx; exact Or.inr (Or.inl h1')
    · simp at hx
  · split at hx
    · simp at hx; rcases hx with rfl | rfl
      · exact Or.inr (Or.inl h1')
      · exact Or.inr (Or.inr h2')
    · simp at hx

theorem handleNouns_s (g : GenComputeRow K) : (rowOfSkel g.skel).s ∈ handleNouns g := by simp [handleNouns]
theorem handleNouns_sf1 (g : GenComputeRow K) : (rowOfSkel g.skel).sf1 ∈ handleNouns g := by simp [handleNouns]
theorem handleNouns_sf2 (g : GenComputeRow K) : (rowOfSkel g.skel).sf2 ∈ handleNouns g := by simp [handleNouns]

/-- The new walk reads' roots are handle nouns. -/
theorem walkReads_root_mem (rows : List (GenComputeRow K)) :
    ∀ r ∈ walkReadsH rows, r.1 ∈ rows.flatMap handleNouns := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  obtain ⟨g, hg, hxg⟩ := List.mem_flatMap.mp hx
  refine List.mem_flatMap.mpr ⟨g, hg, ?_⟩
  rcases consEntries_root_mem g.skel x hxg with h | h | h
  · rw [h]; exact handleNouns_s g
  · rw [h]; exact handleNouns_sf1 g
  · rw [h]; exact handleNouns_sf2 g

/-- The old walk reads' roots are handle nouns, for rows of the right shape. -/
theorem pathKeys_root_mem (rows : List (GenComputeRow K)) (hpk : ∀ g ∈ rows, PKS g) :
    ∀ r ∈ rows.flatMap rowPathKeys, r.1 ∈ rows.flatMap handleNouns := by
  intro r hr
  obtain ⟨g, hg, hrg⟩ := List.mem_flatMap.mp hr
  refine List.mem_flatMap.mpr ⟨g, hg, ?_⟩
  have := hpk g hg
  unfold PKS at this
  rw [this] at hrg
  unfold pkOf at hrg
  simp only [List.mem_append] at hrg
  rcases hrg with h | h
  · split at h
    · simp at h; subst h; exact handleNouns_s g
    · simp at h
  · split at h
    · simp at h; subst h; exact handleNouns_sf1 g
    · simp at h

/-- **The cells are unchanged** (as a set). -/
theorem demandH2_cells_mem_iff (rows : List (GenComputeRow K)) (hpk : ∀ g ∈ rows, PKS g) (c : Noun) :
    c ∈ (demandH2 rows).cells ↔ c ∈ (demandH rows).cells := by
  have key : ∀ (ps : List (Noun × ℕ)), (∀ r ∈ ps, r.1 ∈ rows.flatMap handleNouns) →
      (c ∈ (⟨rows.flatMap handleNouns, [], ps⟩ : Demand).cells ↔
        c ∈ closureOf (rows.flatMap handleNouns)) := by
    intro ps hps
    unfold Demand.cells Demand.roots
    simp only [mem_closureOf, List.mem_append, List.map_nil, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨n, hn, hc⟩
      rcases hn with hn | hn
      · exact ⟨n, hn, hc⟩
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hn
        exact ⟨_, hps r hr, hc⟩
    · rintro ⟨n, hn, hc⟩
      exact ⟨n, Or.inl hn, hc⟩
  unfold demandH2 demandH
  rw [key _ (walkReads_root_mem rows), key _ (pathKeys_root_mem rows hpk)]

theorem demandH2_cells_perm (rows : List (GenComputeRow K)) (hpk : ∀ g ∈ rows, PKS g) :
    (demandH2 rows).cells.Perm (demandH rows).cells :=
  (List.perm_ext_iff_of_nodup (closureOf_nodup _) (closureOf_nodup _)).mpr
    (demandH2_cells_mem_iff rows hpk)

/-- One row per noun (hash-consing) survives. -/
theorem demandH2_one_row (rows : List (GenComputeRow K)) :
    ∀ n ∈ (demandH2 rows).cells, (demandH2 rows).cells.count n = 1 :=
  honest_one_row_per_noun _

/-- The handle cells of every row are rows of the new demand's table. -/
theorem handle_cells_memH2 (rows : List (GenComputeRow K)) (hpk : ∀ g ∈ rows, PKS g)
    {g : GenComputeRow K} (hg : g ∈ rows) :
    ∀ n ∈ rowHandleNouns (hn (rowOfSkelH g.skel)), n.isCell = true → n ∈ (demandH2 rows).cells :=
  fun n hn hc => (demandH2_cells_mem_iff rows hpk n).mpr (handle_cells_memH rows hg n hn hc)

/-- **The walk balance for the walk built from `demandH2`'s reads and cells.** -/
theorem demandH2_balance {F : Type} [Field F] {M : Type} [AddCommMonoid M]
    (W : F × F × (F × F) → M) (rows : List (GenComputeRow K))
    (hsem : ∀ g ∈ rows, (rowOfSkel g.skel).Sem) :
    (((consEntriesAll rows).map fun x => W (entRecP (demandH2 rows).cells x))).sum =
      (((walkRows (demandH2 rows).cells (demandH2 rows).preads).map fun t =>
        provH W (demandH2 rows).cells t.label)).sum :=
  compute_walk_balance W (demandH2 rows).cells rows hsem

/-! ## The OP0 / OP9 part equals `rowPathKeys` up to `pathKind` -/

theorem isPathAx_iff (a : ℕ) : isPathAx a = true ↔ 2 ≤ a := by
  by_cases h : 2 ≤ a
  · simp only [isPathAx, decide_eq_true_eq, h, iff_true]
    rw [show depthOf a = (axisBits a).length from rfl, axisBits_of_two_le h]
    simp
  · simp only [isPathAx, h, iff_false]
    rw [show depthOf a = (axisBits a).length from rfl, axisBits_of_lt_two (by omega)]
    simp

/-- Per row: the path-kind part of `rowPathKeys` is the OP0 / OP9 part of the consumed entries. -/
theorem pathKind_rowPathKeys_row (g : GenComputeRow K) (hpk : PKS g) (hs : (rowOfSkel g.skel).Sem) :
    pathKind (rowPathKeys g) =
      (pathEntries (hn (rowOfSkelH g.skel))).map fun x => (x.1, x.2.1) := by
  unfold PKS at hpk
  rw [hpk]
  have hop : ∀ o, (rowOfSkel g.skel).op = o → o ≠ 3 → o ≠ 5 → hn (rowOfSkelH g.skel) = rowOfSkel g.skel := by
    intro o ho h3 h5
    have e1 : rowOfSkelH g.skel = rowOfSkel g.skel := rowOfSkelH_of_ne _ (by omega)
    rw [e1]; exact hn_of_ne _ (by omega)
  have hopR : (hn (rowOfSkelH g.skel)).op = (rowOfSkel g.skel).op := by
    rw [hn_op, rowOfSkelH_op]
  generalize hr : rowOfSkel g.skel = r at *
  unfold pkOf pathKind pathEntries
  by_cases h0 : r.op = 0
  · have he := hop 0 h0 (by omega) (by omega)
    rw [he]
    have hsem := hs
    simp only [RowN.Sem, h0] at hsem
    obtain ⟨-, -, ax, hft, hsl⟩ := hsem
    have hne0 : ax ≠ 0 := fun h => by rw [h, slot_zero_none] at hsl; cases hsl
    have h9 : ¬ r.op = 9 := by omega
    simp only [h0, h9, if_true, if_false, List.append_nil, hft, atomVal]
    by_cases h1 : ax = 1
    · simp [h1, isPathAx, depthOf, axisBits_of_lt_two]
    · have : isPathAx ax = true := (isPathAx_iff ax).mpr (by omega)
      simp [this, h1]
  · by_cases h9 : r.op = 9
    · have he := hop 9 h9 (by omega) (by omega)
      rw [he]
      have hsem := hs
      simp only [RowN.Sem, h9] at hsem
      obtain ⟨-, -, -, -, ax, hft, hsl⟩ := hsem
      have hne0 : ax ≠ 0 := fun h => by rw [h, slot_zero_none] at hsl; cases hsl
      simp only [h0, h9, if_true, if_false, List.nil_append, hft, atomVal]
      by_cases h1 : ax = 1
      · simp [h1, isPathAx, depthOf, axisBits_of_lt_two]
      · have : isPathAx ax = true := (isPathAx_iff ax).mpr (by omega)
        simp [this, h1]
    · simp [h0, h9, hopR, pathKind]

/-- **The OP0 / OP9 part of the new walk reads is `rowPathKeys`, up to `pathKind`**, over a list of rows. -/
theorem pathKind_rowPathKeys_eq (rows : List (GenComputeRow K)) (hpk : ∀ g ∈ rows, PKS g)
    (hsem : ∀ g ∈ rows, (rowOfSkel g.skel).Sem) :
    pathKind (rows.flatMap rowPathKeys) =
      (rows.flatMap fun g => pathEntries (hn (rowOfSkelH g.skel))).map fun x => (x.1, x.2.1) := by
  induction rows with
  | nil => simp [pathKind]
  | cons g rs ih =>
    have h1 := pathKind_rowPathKeys_row g (hpk g (by simp)) (hsem g (by simp))
    have h2 := ih (fun g' hg' => hpk g' (by simp [hg'])) (fun g' hg' => hsem g' (by simp [hg']))
    simp only [List.flatMap_cons, pathKind, List.filter_append, List.map_append] at h1 h2 ⊢
    rw [h1, h2]

/-- The walk reads split into the OP0 / OP9 part and the OP5 pair part, row by row. -/
theorem walkReadsH_split (rows : List (GenComputeRow K)) :
    walkReadsH rows =
      (rows.flatMap fun g => (pathEntries (hn (rowOfSkelH g.skel)) ++
        pairEntries (hn (rowOfSkelH g.skel)))).map fun x => (x.1, x.2.1) := rfl

end D2

end

end Nock.NockVMROM.Thm54.VclL.Handle
