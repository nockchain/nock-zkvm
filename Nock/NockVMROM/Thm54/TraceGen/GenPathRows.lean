/-
  Nock/NockVMROM/Thm54/TraceGen/GenPathRows.lean

  * `axisBits` / `axisFold_axisBits` / `slot_eq_chainWalk` — an axis as its side bits;
  * `pathSteps` / `edgesOf` — the edge chain from a root along an axis (`Edge` of V0's Chain.lean:
    the consumed cell `(p, l, r)`, its serial `cellIdx`, the side);
    `chainEnd_edgesOf`, `chainAcc_edgesOf` (the ℕ fold of the sides is the axis; in `ZMod q` the
    path chip's accumulator is its cast), `edgesOf_sides`;
  * `certBits` — the 6 certificate bits of `62 − k` (`k ≤ 62`; `cert_sound`);
  * `PathRow`, `pathRowOf`, `PathRowOK`: one row per DISTINCT deep `(root, axis)` read, with the
    multiplicity `m` = number of compute consumers;
    `genPathRows_record_is_slot` (the model's `honest_record_is_slot`: the row's record
    `(root fp, child fp, acc, rootIdx)` is the slot read), `genPathRows_ok`;
  * `Demand`, `demandOfRows`, `lookupKeys` — the compute side's lookups (`lookupsVCL`, ≤ 2 per row)
    as functions of the skeleton rows (consumed by V4);
  * `exportConsumers` and the glue theorems: the generated cell table's export multiset balances
    the path edges plus the shallow compute lookups (`genPathRows_export_balanced`), and the whole
    VCL-L generator output is accepted (`genVclL_accepts`).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMemTable

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL

open Nock
open Nock.ComputeTable (FP)

/-! ## 1. An axis as its side bits -/

/-- Fuel-structural core of `axisBits` (kernel-reducible, so fixtures are `decide`). -/
def axisBitsAux : ℕ → ℕ → List Bool
  | 0, _ => []
  | f + 1, a => if 2 ≤ a then axisBitsAux f (a / 2) ++ [decide (a % 2 = 1)] else []

theorem axisBitsAux_fuel : ∀ (a f g : ℕ), a ≤ f → a ≤ g → axisBitsAux f a = axisBitsAux g a := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro f g hf hg
    by_cases h2 : 2 ≤ a
    · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      simp only [axisBitsAux, h2, if_true]
      rw [ih (a / 2) (by omega) f' g' (by omega) (by omega)]
    · cases f <;> cases g <;> simp [axisBitsAux, h2]

/-- The side bits (root first) of an axis `a ≥ 1`: `a`'s binary digits after the leading one. -/
def axisBits (a : ℕ) : List Bool := axisBitsAux a a

theorem axisBits_of_lt_two {a : ℕ} (h : a < 2) : axisBits a = [] := by
  cases a with
  | zero => rfl
  | succ a => simp [axisBits, axisBitsAux, show ¬ 2 ≤ a + 1 by omega]

theorem axisBits_of_two_le {a : ℕ} (h : 2 ≤ a) :
    axisBits a = axisBits (a / 2) ++ [decide (a % 2 = 1)] := by
  obtain ⟨f, rfl⟩ : ∃ f, a = f + 1 := ⟨a - 1, by omega⟩
  simp only [axisBits, axisBitsAux, h, if_true]
  rw [axisBitsAux_fuel ((f + 1) / 2) f ((f + 1) / 2) (by omega) (by omega)]

/-- **The fold of an axis's bits is the axis** (`a ≥ 1`). -/
theorem axisFold_axisBits : ∀ (a : ℕ), 1 ≤ a → axisFold (axisBits a) = a := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha
    by_cases h2 : 2 ≤ a
    · rw [axisBits_of_two_le h2, axisFold_append, ih (a / 2) (by omega) (by omega)]
      by_cases hm : a % 2 = 1 <;> simp [hm] <;> omega
    · rw [axisBits_of_lt_two (by omega)]
      have : a = 1 := by omega
      subst this; simp [axisFold]

/-- The generator's axis is `Noun.slot`: reading `a` is walking `axisBits a`. -/
theorem slot_eq_chainWalk (a : ℕ) (ha : 1 ≤ a) (root : Noun) :
    Noun.slot a root = chainWalk root (axisBits a) := by
  rw [← chain_slot, axisFold_axisBits a ha]

/-- Path depth: the number of edges of the chain. -/
abbrev depthOf (a : ℕ) : ℕ := (axisBits a).length

/-! ## 2. The edge chain -/

/-- The `(cell, side)` steps of the walk from `root` along `bits` (stops at an atom). -/
def pathSteps : Noun → List Bool → List (Noun × Bool)
  | _, [] => []
  | .cell l r, b :: bs => (.cell l r, b) :: pathSteps (if b then r else l) bs
  | .atom _, _ :: _ => []

theorem mem_pathSteps_cellsOf : ∀ (n : Noun) (bits : List Bool) {p : Noun} {b : Bool},
    (p, b) ∈ pathSteps n bits → p ∈ cellsOf n
  | _, [], p, b, h => by simp [pathSteps] at h
  | .cell l r, c :: bs, p, b, h => by
    simp only [pathSteps, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, -⟩ | h
    · exact mem_cellsOf_self
    · have := mem_pathSteps_cellsOf (if c then r else l) bs h
      simp only [cellsOf, List.mem_cons, List.mem_append]
      right
      cases c
      · exact Or.inl this
      · exact Or.inr this
  | .atom _, _ :: _, p, b, h => by simp [pathSteps] at h

theorem pathSteps_isCell : ∀ (n : Noun) (bits : List Bool) {p : Noun} {b : Bool},
    (p, b) ∈ pathSteps n bits → p.isCell = true := by
  intro n bits p b h
  exact isCell_of_mem_cellsOf (mem_pathSteps_cellsOf n bits h)

/-- **The sides of the chain are the bits** whenever the walk completes. -/
theorem pathSteps_sides : ∀ (n : Noun) (bits : List Bool), (chainWalk n bits).isSome →
    (pathSteps n bits).map Prod.snd = bits
  | _, [], _ => rfl
  | .cell l r, b :: bs, h => by
    simp only [pathSteps, List.map_cons, chainWalk] at h ⊢
    rw [pathSteps_sides _ bs h]
  | .atom _, _ :: _, h => by simp [chainWalk] at h

section Edges
variable {q : ℕ} {Kfp : Type} [Field Kfp]

/-- **The path chip's edge rows** for a read `(root, bits)`: each consumes the cell it leaves
(`(fn p, fn l, fn r)` and its serial `cellIdx`), carrying the side bit. -/
noncomputable def edgesOf (z : Kfp) (cells : List Noun) (root : Noun) (bits : List Bool) :
    List (Edge Kfp) :=
  (pathSteps root bits).map fun pb =>
    ⟨GlobalCarryRecognizer.enc z pb.1, GlobalCarryRecognizer.enc z (hdN pb.1),
      GlobalCarryRecognizer.enc z (tlN pb.1), pb.2, cells.idxOf pb.1⟩

theorem edgesOf_sides (z : Kfp) (cells : List Noun) (root : Noun) (bits : List Bool)
    (h : (chainWalk root bits).isSome) : (edgesOf z cells root bits).map Edge.side = bits := by
  have e : (edgesOf z cells root bits).map Edge.side = (pathSteps root bits).map Prod.snd := by
    simp only [edgesOf, List.map_map]; rfl
  rw [e]
  exact pathSteps_sides root bits h

/-- **`chainAcc_edgesOf`** (the ℕ fold): the fold of an axis's edge sides is the axis; in `ZMod q`
the path chip's accumulator is its cast. -/
theorem chainAcc_edgesOf (z : Kfp) (cells : List Noun) (root : Noun) (a : ℕ) (ha : 1 ≤ a)
    (h : (chainWalk root (axisBits a)).isSome) :
    axisFold ((edgesOf z cells root (axisBits a)).map Edge.side) = a ∧
    chainAccF q ((edgesOf z cells root (axisBits a)).map Edge.side) = (a : ZMod q) := by
  rw [edgesOf_sides z cells root _ h]
  exact ⟨axisFold_axisBits a ha, by rw [chainAccF_eq, axisFold_axisBits a ha]⟩

variable [DecidableEq Kfp]

/-- **The chain links**: starting at `fn root`, the edges end at the fingerprint of the noun the
walk reaches. -/
theorem chainEnd_edgesOf (z : Kfp) (cells : List Noun) :
    ∀ (root : Noun) (bits : List Bool) (n : Noun), chainWalk root bits = some n →
      chainEnd (GlobalCarryRecognizer.enc z root) (edgesOf z cells root bits) =
        some (GlobalCarryRecognizer.enc z n)
  | root, [], n, h => by
    simp only [chainWalk, Option.some.injEq] at h
    subst h; simp [edgesOf, pathSteps, chainEnd]
  | .cell l r, b :: bs, n, h => by
    simp only [chainWalk] at h
    have ih := chainEnd_edgesOf z cells (if b then r else l) bs n h
    simp only [edgesOf, pathSteps, List.map_cons, chainEnd, hdN, tlN] at ih ⊢
    simp only [if_true]
    cases b <;> simpa [childOf] using ih
  | .atom _, _ :: _, n, h => by simp [chainWalk] at h

end Edges

/-! ## 3. The certificate bits -/

/-- The six certificate bits of `62 − k` (little-endian): `k ≤ 62` iff they exist. -/
def certBits (k : ℕ) : Fin 6 → Bool := fun i => (62 - k).testBit i

/-- The value the six bits spell. -/
def certVal (b : Fin 6 → Bool) : ℕ := ∑ i : Fin 6, if b i then 2 ^ (i : ℕ) else 0

/-- **The certificate is sound**: a chain of `k ≤ 62` edges has bits spelling `62 − k`. -/
theorem cert_sound : ∀ k : Fin 63, certVal (certBits k) + (k : ℕ) = 62 := by decide

/-! ## 4. Path rows -/

/-- **A path-chip row** (one per distinct deep read): the root serial (B0), the record
`(root fp, child fp, acc)`, the edge chain, the length `len` with its 6 certificate bits, and the
multiplicity `m` (the number of compute consumers). -/
structure PathRow (Kfp : Type) where
  rootIdx : ℕ
  rootFP : FP Kfp
  childFP : FP Kfp
  acc : ℕ
  edges : List (Edge Kfp)
  len : ℕ
  bits : Fin 6 → Bool
  m : ℕ

section Rows
variable {q : ℕ} {Kfp : Type} [Field Kfp]

/-- The deep reads: depth `≥ 2` (the path chip's reads; depth `1` is an export lookup). -/
def isDeep (a : ℕ) : Bool := decide (2 ≤ depthOf a)

/-- The distinct deep reads, in first-occurrence order of the dedup. -/
def deepReads (reads : List (Noun × ℕ)) : List (Noun × ℕ) :=
  (reads.filter fun r => isDeep r.2).dedup

/-- **The honest path row** of a read `(root, axis)` with multiplicity `reads.count`. -/
noncomputable def pathRowOf (z : Kfp) (cells : List Noun) (reads : List (Noun × ℕ))
    (r : Noun × ℕ) : PathRow Kfp :=
  let bits := axisBits r.2
  let es := edgesOf z cells r.1 bits
  { rootIdx := cells.idxOf r.1
    rootFP := GlobalCarryRecognizer.enc z r.1
    childFP := match chainWalk r.1 bits with
      | some n => GlobalCarryRecognizer.enc z n
      | none => 0
    acc := axisFold (es.map Edge.side)
    edges := es
    len := bits.length
    bits := certBits bits.length
    m := reads.count r }

/-- **SHD-A: the path-kind axes** (depth `≥ 1`: axes `2`, `3` and deeper; axis `1` has depth `0` and
is NOT a path read, `shd_axis1_first`).  A one-row chain at depth `1` consumes the export and provides
`pReq (root, a)`. -/
def isPathAx (a : ℕ) : Bool := decide (1 ≤ depthOf a)

/-- **SHD-A: the distinct path-kind reads** (dedup, first-occurrence order). -/
def pathReads (l : List (Noun × ℕ)) : List (Noun × ℕ) :=
  (l.filter fun r => isPathAx r.2).dedup

/-- **The path rows**: one per distinct deep `(root, axis)` read. -/
noncomputable def genPathRows (z : Kfp) (cells : List Noun) (reads : List (Noun × ℕ)) :
    List (PathRow Kfp) :=
  (deepReads reads).map (pathRowOf z cells reads)

variable [DecidableEq Kfp]

/-- **The path-row gates**: chain linkage from the root's fingerprint to the child's, the
accumulator is the fold of the sides, the length is the number of edges and `≤ 62` with its 6
certificate bits, the first edge consumes the root's serial. -/
structure PathRowOK (r : PathRow Kfp) : Prop where
  link : chainEnd r.rootFP r.edges = some r.childFP
  acc : r.acc = axisFold (r.edges.map Edge.side)
  len_eq : r.len = r.edges.length
  len_le : r.len ≤ 62
  cert : certVal r.bits + r.len = 62
  first : ∀ e ∈ r.edges.head?, e.cellIdx = r.rootIdx
  nonempty : r.edges ≠ []

/-- **`genPathRows_record_is_slot`** (the model's `honest_record_is_slot`): when the read is
defined (`slot a root = some child`), the generated row's record is the slot read — its child
fingerprint is `fn child`, its accumulator is the axis `a` (as ℕ, and its cast in `ZMod q`), and
the chain links from `fn root`. -/
theorem genPathRows_record_is_slot (z : Kfp) (cells : List Noun) (reads : List (Noun × ℕ))
    (root child : Noun) (a : ℕ) (ha : 1 ≤ a) (hslot : Noun.slot a root = some child) :
    let r := pathRowOf z cells reads (root, a)
    r.childFP = GlobalCarryRecognizer.enc z child ∧ r.acc = a ∧
    chainAccF q (r.edges.map Edge.side) = (a : ZMod q) ∧
    chainEnd r.rootFP r.edges = some r.childFP ∧ r.rootFP = GlobalCarryRecognizer.enc z root := by
  intro r
  have hw : chainWalk root (axisBits a) = some child := by
    rw [← slot_eq_chainWalk a ha]; exact hslot
  have hs : (chainWalk root (axisBits a)).isSome := by rw [hw]; rfl
  obtain ⟨h1, h2⟩ := chainAcc_edgesOf (q := q) z cells root a ha hs
  have hc : r.childFP = GlobalCarryRecognizer.enc z child := by
    simp only [r, pathRowOf]; rw [hw]
  refine ⟨hc, h1, h2, ?_, rfl⟩
  rw [hc]
  exact chainEnd_edgesOf z cells root _ child hw

/-- **The honest path row passes its gates** when the read is defined, deep and at most 62 edges
(`hax63`'s role). -/
theorem genPathRows_ok (z : Kfp) (cells : List Noun) (reads : List (Noun × ℕ))
    (root child : Noun) (a : ℕ) (hdeep : isDeep a = true) (h62 : depthOf a ≤ 62)
    (hslot : Noun.slot a root = some child) (hroot : root ∈ cells) :
    PathRowOK (pathRowOf z cells reads (root, a)) := by
  have ha : 1 ≤ a := by
    by_contra h
    have : a = 0 := by omega
    subst this
    simp [isDeep, depthOf, axisBits, axisBitsAux] at hdeep
  have hw : chainWalk root (axisBits a) = some child := by
    rw [← slot_eq_chainWalk a ha]; exact hslot
  have hs : (chainWalk root (axisBits a)).isSome := by rw [hw]; rfl
  obtain ⟨hl, -, -, hlink, -⟩ := genPathRows_record_is_slot (q := 0) z cells reads root child a ha hslot
  have hsides := edgesOf_sides z cells root _ hs
  have hlen : (edgesOf z cells root (axisBits a)).length = (axisBits a).length := by
    have := congrArg List.length hsides
    simpa using this
  have h2 : 2 ≤ (axisBits a).length := by simpa [isDeep, depthOf] using hdeep
  refine ⟨hlink, rfl, ?_, h62, ?_, ?_, ?_⟩
  · simpa [pathRowOf] using hlen.symm
  · have h62' : (axisBits a).length ≤ 62 := h62
    have := cert_sound ⟨(axisBits a).length, Nat.lt_succ_of_le h62'⟩
    simpa [pathRowOf] using this
  · intro e he
    simp only [pathRowOf, edgesOf] at he ⊢
    obtain ⟨b, bs, hb⟩ : ∃ b bs, axisBits a = b :: bs := by
      cases h : axisBits a with
      | nil => rw [h] at h2; simp at h2
      | cons b bs => exact ⟨b, bs, rfl⟩
    rw [hb] at he
    cases root with
    | atom v => simp [chainWalk, hb] at hw
    | cell l r =>
      simp [pathSteps] at he ⊢
      subst he
      rfl
  · intro hnil
    simp only [pathRowOf] at hnil
    have := congrArg List.length hnil
    simp only [hlen, List.length_nil] at this
    omega

end Rows


/-! ## 5. The demand: what the compute side binds and reads -/

/-- **The compute side's demand on the memory**: the root bindings (subject and formula of each
compute row, with multiplicity) and the lookups `(root, axis)` (the non-inline records, with
multiplicity; `lookupsVCL`). -/
structure Demand where
  binds : List Noun
  /-- the export-kind reads (slot accumulator `.export`; depth `1`) -/
  reads : List (Noun × ℕ)
  /-- SHD-A: the path-kind reads (slot accumulator `.path`; `isPathAx`) -/
  preads : List (Noun × ℕ)

/-- Every noun the table must contain a row for: the bound nouns and the read roots. -/
def Demand.roots (d : Demand) : List Noun := d.binds ++ d.reads.map Prod.fst ++ d.preads.map Prod.fst

/-- **The hash-consed cell table's rows**: one per distinct cell of every subject, every quoted
constant, every formula and every read root. -/
def Demand.cells (d : Demand) : List Noun := closureOf d.roots

/-- Depth-1 reads: an export lookup of the root cell (one lookup, no chain). -/
def shallowReads (reads : List (Noun × ℕ)) : List (Noun × ℕ) :=
  reads.filter fun r => decide (depthOf r.2 = 1)

/-- The parents of the edges of all distinct deep chains (one consumption per edge row). -/
def edgeParents (preads : List (Noun × ℕ)) : List Noun :=
  (pathReads preads).flatMap fun r => (pathSteps r.1 (axisBits r.2)).map Prod.fst

/-- The cells the compute side looks up at depth 1 (one per occurrence). -/
def shallowLookups (reads : List (Noun × ℕ)) : List Noun :=
  (shallowReads reads).flatMap fun r => selfCell r.1

/-- **The export consumers**: path-edge parents plus compute cell lookups.  `mx` of a row is the
number of times its noun occurs here. -/
def exportConsumers (preads reads : List (Noun × ℕ)) : List Noun :=
  edgeParents preads ++ shallowLookups reads

section Glue
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Algebra (ZMod q) Kfp]

theorem read_root_mem (d : Demand) {r : Noun × ℕ} (hr : r ∈ d.reads) : r.1 ∈ d.roots := by
  simp only [Demand.roots, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨r, hr, rfl⟩)

theorem pread_root_mem (d : Demand) {r : Noun × ℕ} (hr : r ∈ d.preads) : r.1 ∈ d.roots := by
  simp only [Demand.roots, List.mem_append, List.mem_map]
  exact Or.inr ⟨r, hr, rfl⟩

theorem exportConsumers_subset (d : Demand) :
    ∀ c ∈ exportConsumers d.preads d.reads, c ∈ d.cells := by
  intro c hc
  simp only [exportConsumers, List.mem_append] at hc
  rcases hc with hc | hc
  · simp only [edgeParents, pathReads, List.mem_flatMap, List.mem_map, List.mem_dedup,
      List.mem_filter] at hc
    obtain ⟨r, ⟨hr, -⟩, ⟨pb, hpb, rfl⟩⟩ := hc
    exact mem_closureOf.mpr ⟨r.1, pread_root_mem d hr, mem_pathSteps_cellsOf _ _ hpb⟩
  · simp only [shallowLookups, shallowReads, List.mem_flatMap, List.mem_filter] at hc
    obtain ⟨r, ⟨hr, -⟩, hc⟩ := hc
    exact selfCell_subset_closureOf (b := r.1) (read_root_mem d hr) hc

theorem binds_subset (d : Demand) : ∀ b ∈ d.binds.flatMap selfCell, b ∈ d.cells := by
  intro c hc
  simp only [List.mem_flatMap] at hc
  obtain ⟨b, hb, hc⟩ := hc
  exact selfCell_subset_closureOf (b := b) (by simp [Demand.roots, hb]) hc

/-- **The path rows' edges and the compute cell lookups are exactly the export consumers**: the
generated cell table's export multiset balances them (the `mx` completeness content). -/
theorem genPathRows_export_balanced (z : Kfp) (d : Demand) (vcs : List Noun) :
    ExportBalanced (tableRows (q := q) z d.cells vcs (exportConsumers d.preads d.reads))
      ((pathReads d.preads).flatMap fun r => edgesOf z d.cells r.1 (axisBits r.2))
      ((shallowLookups d.reads).map (xkeyOf z d.cells)) := by
  have hnd := closureOf_nodup d.roots
  have hcell : ∀ n ∈ d.cells, n.isCell = true := fun n hn => closureOf_isCell hn
  refine genMemTable_export_balanced z d.cells vcs _ hnd hcell (exportConsumers_subset d) _ _ ?_
  simp only [exportConsumers, edgeParents, List.map_append, List.map_flatMap, List.map_map,
    List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro r _
  simp [edgesOf, xkeyOf, Function.comp_def]

theorem bind_cell_mem_cells (d : Demand) {b : Noun} (hb : b ∈ d.binds) (hc : b.isCell = true) :
    b ∈ d.cells := by
  cases b with
  | atom _ => simp [Noun.isCell] at hc
  | cell x y => exact mem_closureOf.mpr ⟨_, by simp [Demand.roots, hb], mem_cellsOf_self⟩

theorem pread_cell_mem_cells (d : Demand) {r : Noun × ℕ} (hr : r ∈ d.preads) (hc : r.1.isCell = true) :
    r.1 ∈ d.cells := by
  cases h : r.1 with
  | atom _ => rw [h] at hc; simp [Noun.isCell] at hc
  | cell x y => exact mem_closureOf.mpr ⟨_, pread_root_mem d hr, h ▸ mem_cellsOf_self⟩

theorem read_cell_mem_cells (d : Demand) {r : Noun × ℕ} (hr : r ∈ d.reads) (hc : r.1.isCell = true) :
    r.1 ∈ d.cells := by
  cases h : r.1 with
  | atom _ => rw [h] at hc; simp [Noun.isCell] at hc
  | cell x y => exact mem_closureOf.mpr ⟨_, read_root_mem d hr, h ▸ mem_cellsOf_self⟩

/-- **The whole VCL-L generator output is accepted** (the table side): serial gate, every row
gate, the validity balance against the root bindings, at any field with `Algebra (ZMod q)`, any
nonzero seed, from the demand's hash-consed closure — given only that every root's atoms are `< q`
and its rank is `< 2^110`. -/
theorem genVclL_accepts [NeZero q] {z : Kfp} (hz : z ≠ 0) (d : Demand)
    (hrank : ∀ r ∈ d.roots, rankOf r < 2 ^ 110) (hatoms : ∀ r ∈ d.roots, AtomsLt q r) :
    TableAccepts z
      (tableRows (q := q) z d.cells (vcsOf d.cells d.binds) (exportConsumers d.preads d.reads))
      ((d.binds.flatMap selfCell).map (vkeyOf z d.cells)) ∧
    ExportBalanced (tableRows (q := q) z d.cells (vcsOf d.cells d.binds) (exportConsumers d.preads d.reads))
      ((pathReads d.preads).flatMap fun r => edgesOf z d.cells r.1 (axisBits r.2))
      ((shallowLookups d.reads).map (xkeyOf z d.cells)) := by
  obtain ⟨hnd, hcell, hclosed, hrk, hat⟩ := closureOf_hyps (q := q) d.roots hrank hatoms
  exact ⟨genMemTable_accepts hz d.cells d.binds _ hnd hcell hclosed (binds_subset d) hrk hat,
    genPathRows_export_balanced z d _⟩

/-- Decode at the certified fuel for every generated cell. -/
theorem genVclL_decode [NeZero q] (d : Demand)
    (hrank : ∀ r ∈ d.roots, rankOf r < 2 ^ 110) (hatoms : ∀ r ∈ d.roots, AtomsLt q r)
    (vcs xcs : List Noun) {n : Noun} (hn : n ∈ d.cells) :
    preZNounOfTable (tableB0 q d.cells vcs xcs) (d.cells.idxOf n) = some n := by
  obtain ⟨-, hcell, hclosed, hrk, hat⟩ := closureOf_hyps (q := q) d.roots hrank hatoms
  exact genMemTable_preZNounOfTable d.cells vcs xcs hcell hclosed hat n hn (hrk n hn)

end Glue


/-! ## 6. The compute side's lookup columns, from the skeleton -/

section Skeleton
open Nock.NockVMROM.Thm54.TraceGen
open Nock.Walk
variable {K : Type} [Field K]

/-- The nouns a compute row binds to the table (validity root bindings): subject and formula. -/
def rowBinds (g : GenComputeRow K) : List Noun := [g.skel.subject, g.skel.formula]

/-- At most two per row (`rowLookups_le_two`). -/
def rowLookups (g : GenComputeRow K) : List (Noun × ℕ) :=
  (g.requests.drop (inlineRecords g.skel.state)).map fun r => (r.root, r.axis)

/-- The compute tree's rows (breadth-first, as the walk commits them). -/
def skelRows (ct : NTree (GenComputeRow K)) : List (GenComputeRow K) :=
  (bfsForest [ct]).map NTree.label

/-- **The VCL-L demand of a list of compute rows.** -/
def demandOfRows (rows : List (GenComputeRow K)) : Demand :=
  ⟨rows.flatMap rowBinds, rows.flatMap rowLookups,
    (rows.flatMap rowLookups).filter fun r => isDeep r.2⟩

theorem rowLookups_length (g : GenComputeRow K)
    (hlen : g.requests.length = Nock.Framework.recordCount g.skel.state) :
    (rowLookups g).length = lookupsVCL g.skel.state := by
  simp [rowLookups, lookupsVCL, hlen]

/-- **At most two lookups per compute row** (T5 at the generator's rows). -/
theorem rowLookups_le_two (g : GenComputeRow K)
    (hlen : g.requests.length = Nock.Framework.recordCount g.skel.state) :
    (rowLookups g).length ≤ 2 := by
  rw [rowLookups_length g hlen]; exact lookupsVCL_le_two _

/-- The reads of a demand number at most `2·N`. -/
theorem demandOfRows_reads_le (rows : List (GenComputeRow K))
    (hlen : ∀ g ∈ rows, g.requests.length = Nock.Framework.recordCount g.skel.state) :
    (demandOfRows rows).reads.length ≤ 2 * rows.length := by
  simp only [demandOfRows, List.length_flatMap]
  induction rows with
  | nil => simp
  | cons g rs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := rowLookups_le_two g (hlen g (by simp))
    have h2 := ih (fun g' hg' => hlen g' (by simp [hg']))
    omega

/-- The binds number exactly `2·N`. -/
theorem demandOfRows_binds_length (rows : List (GenComputeRow K)) :
    (demandOfRows rows).binds.length = 2 * rows.length := by
  simp only [demandOfRows, List.length_flatMap, rowBinds]
  induction rows with
  | nil => simp
  | cons g rs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_cons, List.length_nil] at ih ⊢; omega

/-- **The generator's rows carry exactly `recordCount` requests** (so `lookupsVCL` is the lookup
count at the generator's rows, no hypothesis): every node of every tree `genComputeSkeleton`
emits.  Proof by fuel induction over the 12 emission arms. -/
theorem genComputeSkeleton_requests_length (fuel : ℕ) :
    ∀ (s f : Noun) (ct : NTree (GenComputeRow K)) (res : Noun),
      genComputeSkeleton fuel s f = .ok (ct, res) →
      ∀ t, InTree ct t → t.label.requests.length = Nock.Framework.recordCount t.label.skel.state := by
  induction fuel with
  | zero => intro s f ct res h; simp [genComputeSkeleton] at h
  | succ n ih =>
    intro s f ct res h t ht
    unfold genComputeSkeleton at h
    repeat' (split at h)
    all_goals first
      | (exfalso; simp at h; done)
      | skip
    all_goals
      (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       cases ht with
       | here => simp [skelNode, Nock.Framework.recordCount, genSkelOp0, genSkelOp1, genSkelOp2, genSkelOp3, genSkelOp4, genSkelOp5, genSkelOp6, genSkelOp7, genSkelOp8, genSkelOp9, genSkelCons]
       | sub hs hst =>
         simp only [NTree.children_node, List.mem_cons, List.not_mem_nil, or_false] at hs <;>
         first
           | exact hs.elim
           | (subst hs; exact ih _ _ _ _ (by assumption) _ hst)
           | (rcases hs with rfl | rfl <;> exact ih _ _ _ _ (by assumption) _ hst)
           | (rcases hs with rfl | rfl | rfl <;> exact ih _ _ _ _ (by assumption) _ hst))

/-- Every row of the generator's compute tree. -/
theorem skelRows_requests_length (fuel : ℕ) (subj f res : Noun) (ct : NTree (GenComputeRow K))
    (h : genComputeSkeleton fuel subj f = .ok (ct, res)) :
    ∀ g ∈ skelRows ct, g.requests.length = Nock.Framework.recordCount g.skel.state := by
  intro g hg
  simp only [skelRows, List.mem_map] at hg
  obtain ⟨t, ht, rfl⟩ := hg
  obtain ⟨c, hc, hct⟩ := (mem_bfsForest _ _).mp ht
  have : c = ct := by simpa using hc
  subst this
  exact genComputeSkeleton_requests_length fuel subj f c res h t hct

/-- **The demand of the generator's compute tree**, with the `≤ 2N` read majorant. -/
theorem demandOfGen_reads_le (fuel : ℕ) (subj f res : Noun) (ct : NTree (GenComputeRow K))
    (h : genComputeSkeleton fuel subj f = .ok (ct, res)) :
    (demandOfRows (skelRows ct)).reads.length ≤ 2 * (skelRows ct).length :=
  demandOfRows_reads_le _ (skelRows_requests_length fuel subj f res ct h)

end Skeleton

end Nock.NockVMROM.Thm54.VclL
