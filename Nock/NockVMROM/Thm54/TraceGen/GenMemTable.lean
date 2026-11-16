/-
  Nock/NockVMROM/Thm54/TraceGen/GenMemTable.lean

  * `cellsOf`, `closureOf` — the hash-consed closure: one entry per DISTINCT cell subterm of a root
    list (spec-level `List.dedup`; the order is the list's, any order is sound under the rank);
  * `rowB0` / `tableB0` — the round-0 columns: serial `idx = idxOf`, child serials, weights, atoms,
    the exact rank `mu = Noun.internal` (cells below) as two limbs with carry, `mv`, `mx` (the
    consumer counts handed in as lists of nouns);
  * `tableRows` — the B1 fill: `fn` (= `GlobalCarryRecognizer.enc z`) of each row's noun and children;
  * lemmas (all at ANY field `Kfp` with `Algebra (ZMod q) Kfp`, `z ≠ 0`):
    `genMemTable_serial` (`idx i = i`), `genMemTable_rank_limbs` (the limb hypotheses of
    `mu_limbs_exact` hold; `rowOK`), `genMemTable_rowOK`, `genMemTable_decode` (`decodeB0` at a
    row's serial is the row's noun), `genMemTable_mv_eq_consumers`, `genMemTable_mx_eq_consumers`,
    `genMemTable_validity_balanced`, `genMemTable_export_balanced` (the completeness content: the
    provided multisets equal the consumed ones), `genMemTable_accepts` (`TableAccepts`).
-/
import Nock.NockVMROM.Thm54.P8Core.VclL.Consumers

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL

open Nock
open Nock.ComputeTable (FP)

/-! ## 1. The hash-consed closure -/

/-- Every cell subterm of a noun (with repeats), the noun itself first. -/
def cellsOf : Noun → List Noun
  | .atom _ => []
  | .cell a b => .cell a b :: (cellsOf a ++ cellsOf b)

/-- **The hash-consed closure** of a root list: one entry per DISTINCT cell subterm. -/
def closureOf (ns : List Noun) : List Noun := (ns.flatMap cellsOf).dedup

/-- A cell as a singleton list, an atom as the empty list. -/
def selfCell : Noun → List Noun
  | .atom _ => []
  | .cell x y => [.cell x y]

/-- The cell children of a noun (atoms carry no row). -/
def childCells : Noun → List Noun
  | .atom _ => []
  | .cell a b => selfCell a ++ selfCell b

/-- Head and tail of a cell (an atom is returned unchanged). -/
def hdN : Noun → Noun
  | .cell a _ => a
  | n => n

def tlN : Noun → Noun
  | .cell _ b => b
  | n => n

theorem mem_cellsOf_self {a b : Noun} : Noun.cell a b ∈ cellsOf (.cell a b) := by
  simp [cellsOf]

theorem mem_cellsOf_trans {n : Noun} : ∀ {c d : Noun}, c ∈ cellsOf n → d ∈ cellsOf c → d ∈ cellsOf n := by
  induction n with
  | atom _ => intro c d h; simp [cellsOf] at h
  | cell a b iha ihb =>
    intro c d hc hd
    simp only [cellsOf, List.mem_cons, List.mem_append] at hc ⊢
    rcases hc with rfl | hc | hc
    · simpa only [cellsOf, List.mem_cons, List.mem_append] using hd
    · exact Or.inr (Or.inl (iha hc hd))
    · exact Or.inr (Or.inr (ihb hc hd))

theorem isCell_of_mem_cellsOf {n c : Noun} (h : c ∈ cellsOf n) : c.isCell = true := by
  induction n with
  | atom _ => simp [cellsOf] at h
  | cell a b iha ihb =>
    simp only [cellsOf, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · rfl
    · exact iha h
    · exact ihb h

theorem selfCell_mem_cellsOf {a c : Noun} (hc : c ∈ selfCell a) : c ∈ cellsOf a := by
  cases a with
  | atom _ => simp [selfCell] at hc
  | cell x y => simp [selfCell] at hc; subst hc; exact mem_cellsOf_self

theorem selfCell_isCell {a c : Noun} (hc : c ∈ selfCell a) : c.isCell = true := by
  cases a with
  | atom _ => simp [selfCell] at hc
  | cell x y => simp [selfCell] at hc; subst hc; rfl

theorem childCells_mem_cellsOf {n c : Noun} (h : c ∈ childCells n) : c ∈ cellsOf n := by
  cases n with
  | atom _ => simp [childCells] at h
  | cell a b =>
    simp only [childCells, List.mem_append] at h
    simp only [cellsOf, List.mem_cons, List.mem_append]
    rcases h with h | h
    · exact Or.inr (Or.inl (selfCell_mem_cellsOf h))
    · exact Or.inr (Or.inr (selfCell_mem_cellsOf h))

theorem childCells_isCell {n c : Noun} (h : c ∈ childCells n) : c.isCell = true := by
  cases n with
  | atom _ => simp [childCells] at h
  | cell a b =>
    simp only [childCells, List.mem_append] at h
    rcases h with h | h
    · exact selfCell_isCell h
    · exact selfCell_isCell h

theorem mem_closureOf {ns : List Noun} {c : Noun} :
    c ∈ closureOf ns ↔ ∃ n ∈ ns, c ∈ cellsOf n := by
  simp [closureOf, List.mem_dedup, List.mem_flatMap]

/-- **The closure is closed under cell children** (a row's children have rows). -/
theorem closureOf_closed {ns : List Noun} {n c : Noun} (hn : n ∈ closureOf ns)
    (hc : c ∈ childCells n) : c ∈ closureOf ns := by
  rw [mem_closureOf] at hn ⊢
  obtain ⟨m, hm, hnm⟩ := hn
  exact ⟨m, hm, mem_cellsOf_trans hnm (childCells_mem_cellsOf hc)⟩

theorem closureOf_isCell {ns : List Noun} {n : Noun} (hn : n ∈ closureOf ns) : n.isCell = true := by
  rw [mem_closureOf] at hn
  obtain ⟨m, -, h⟩ := hn
  exact isCell_of_mem_cellsOf h

theorem closureOf_nodup (ns : List Noun) : (closureOf ns).Nodup := List.nodup_dedup _

/-! ## 2. The round-0 rows -/

section Rows
variable (q : ℕ)

/-- The rank `μ` of a noun: the number of cells below it, with multiplicity (`λ − 1`). -/
abbrev rankOf (n : Noun) : ℕ := n.internal

/-- The B0 row of a noun (meaningful for a cell; an atom gets the all-zero row).  `cells` is the
closure (serials = positions), `vcs` the validity consumers (child references and root bindings, as
nouns), `xcs` the export consumers (path-edge parents and compute cell lookups, as nouns);
`mv n = vcs.count n`, `mx n = xcs.count n`. -/
def rowB0 (cells vcs xcs : List Noun) (n : Noun) : CellRowB0 q :=
  match n with
  | .atom _ => ⟨0, 0, 0, false, false, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | .cell a b =>
    { idx := cells.idxOf n
      idL := if a.isCell then cells.idxOf a else 0
      idR := if b.isCell then cells.idxOf b else 0
      wL := a.isCell
      wR := b.isCell
      aL := match a with | .atom v => (v : ZMod q) | _ => 0
      aR := match b with | .atom v => (v : ZMod q) | _ => 0
      lo := rankOf n % 2 ^ 62
      hi := rankOf n / 2 ^ 62
      loL := rankOf a % 2 ^ 62
      hiL := rankOf a / 2 ^ 62
      loR := rankOf b % 2 ^ 62
      hiR := rankOf b / 2 ^ 62
      carry := (rankOf a % 2 ^ 62 + rankOf b % 2 ^ 62 + 1) / 2 ^ 62
      mv := vcs.count n
      mx := xcs.count n }

/-- **The B0 table**: one row per closure cell, in closure order (serial = position). -/
def tableB0 (cells vcs xcs : List Noun) : List (CellRowB0 q) :=
  cells.map (rowB0 q cells vcs xcs)

variable {q}
variable {Kfp : Type*} [Field Kfp] [Algebra (ZMod q) Kfp]

/-- **The B1 fill** at the seed `z`: `fn` of the row's noun and of its two children. -/
noncomputable def tableRows (z : Kfp) (cells vcs xcs : List Noun) : List (CellRow q Kfp) :=
  cells.map fun n =>
    { b0 := rowB0 q cells vcs xcs n
      p := GlobalCarryRecognizer.enc z n
      l := GlobalCarryRecognizer.enc z (hdN n)
      r := GlobalCarryRecognizer.enc z (tlN n) }

theorem tableRows_b0 (z : Kfp) (cells vcs xcs : List Noun) :
    (tableRows (q := q) z cells vcs xcs).map (·.b0) = tableB0 q cells vcs xcs := by
  simp [tableRows, tableB0, Function.comp_def]

end Rows

/-! ## 3. Serials, decode -/

section Serial
variable {q : ℕ}

theorem genMemTable_serial (cells vcs xcs : List Noun) (hnd : cells.Nodup)
    (hcell : ∀ n ∈ cells, n.isCell = true) :
    SerialOK (tableB0 q cells vcs xcs) := by
  unfold SerialOK tableB0
  rw [List.map_map, List.length_map]
  apply List.ext_getElem
  · rw [List.length_map, List.length_range]
  · intro i h1 h2
    have hi : i < cells.length := by simpa using h1
    simp only [List.getElem_map, Function.comp_apply, List.getElem_range]
    have hc := hcell _ (List.getElem_mem hi)
    generalize hn : cells[i] = n at hc
    cases n with
    | atom _ => simp [Noun.isCell] at hc
    | cell a b =>
      simp only [rowB0]
      rw [← hn]
      exact hnd.idxOf_getElem i hi

theorem tableB0_getElem? (cells vcs xcs : List Noun) {n : Noun} (hn : n ∈ cells) :
    (tableB0 q cells vcs xcs)[cells.idxOf n]? = some (rowB0 q cells vcs xcs n) := by
  have hlt : cells.idxOf n < cells.length := List.idxOf_lt_length_iff.mpr hn
  simp [tableB0, List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem_idxOf]

theorem natCast_val (v : ℕ) (hv : v < q) : ((v : ZMod q)).val = v := ZMod.val_cast_of_lt hv

/-- Atoms of a noun are below `q` (the cells' atom children are `ZMod q` values). -/
def AtomsLt (q : ℕ) (n : Noun) : Prop := ∀ k ∈ n.leafList, k < q

theorem AtomsLt.left {a b : Noun} (h : AtomsLt q (.cell a b)) : AtomsLt q a := fun k hk =>
  h k (by simp [Noun.leafList, hk])

theorem AtomsLt.right {a b : Noun} (h : AtomsLt q (.cell a b)) : AtomsLt q b := fun k hk =>
  h k (by simp [Noun.leafList, hk])

/-- **The decode is the identity at a row's serial**: with enough fuel (`μ < f`), `decodeB0` of the
generated B0 table at the serial of a closure cell is that cell.  Atoms are read back through
`ZMod q` (`AtomsLt`). -/
theorem genMemTable_decode (cells vcs xcs : List Noun)
    (hcell : ∀ n ∈ cells, n.isCell = true)
    (hclosed : ∀ n ∈ cells, ∀ c ∈ childCells n, c ∈ cells)
    (hatoms : ∀ n ∈ cells, AtomsLt q n) :
    ∀ (n : Noun), n ∈ cells → ∀ f, rankOf n < f →
      decodeB0 (tableB0 q cells vcs xcs) f (cells.idxOf n) = some n := by
  intro n
  induction n with
  | atom v => intro h; have := hcell _ h; simp [Noun.isCell] at this
  | cell a b iha ihb =>
    intro hn f hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [Noun.internal] at hf; omega⟩
    have hmu : rankOf (.cell a b) = rankOf a + rankOf b + 1 := by
      simp only [rankOf, Noun.internal]; omega
    have hat := hatoms _ hn
    rw [decodeB0_succ, tableB0_getElem? cells vcs xcs hn]
    simp only [Option.bind_some]
    have hL : childL (tableB0 q cells vcs xcs) g (rowB0 q cells vcs xcs (.cell a b)) = some a := by
      cases a with
      | atom v =>
        simp only [childL, rowB0, Noun.isCell, Bool.false_eq_true, if_false]
        rw [natCast_val v (hat.left v (by simp [Noun.leafList]))]
      | cell x y =>
        simp only [childL, rowB0, Noun.isCell, if_true]
        refine iha ?_ g ?_
        · exact hclosed _ hn _ (by simp [childCells, selfCell])
        · omega
    have hR : childR (tableB0 q cells vcs xcs) g (rowB0 q cells vcs xcs (.cell a b)) = some b := by
      cases b with
      | atom v =>
        simp only [childR, rowB0, Noun.isCell, Bool.false_eq_true, if_false]
        rw [natCast_val v (hat.right v (by simp [Noun.leafList]))]
      | cell x y =>
        simp only [childR, rowB0, Noun.isCell, if_true]
        refine ihb ?_ g ?_
        · exact hclosed _ hn _ (by simp [childCells, selfCell])
        · omega
    rw [hL]; simp only [Option.bind_some]; rw [hR]; rfl

/-- At the certified fuel `2^110` (`preZNounOfTable`), given the rank bound. -/
theorem genMemTable_preZNounOfTable (cells vcs xcs : List Noun)
    (hcell : ∀ n ∈ cells, n.isCell = true)
    (hclosed : ∀ n ∈ cells, ∀ c ∈ childCells n, c ∈ cells)
    (hatoms : ∀ n ∈ cells, AtomsLt q n) (n : Noun) (hn : n ∈ cells)
    (hrank : rankOf n < 2 ^ 110) :
    preZNounOfTable (tableB0 q cells vcs xcs) (cells.idxOf n) = some n :=
  genMemTable_decode cells vcs xcs hcell hclosed hatoms n hn _ hrank

end Serial


/-! ## 4. Multiset balance engine -/

section Balance

theorem expand_map_fst {α β : Type*} (f : α → β) (l : List (α × ℕ)) :
    expand (l.map fun kc => (f kc.1, kc.2)) = (expand l).map f := by
  induction l with
  | nil => simp [expand]
  | cons kc l ih =>
    simp only [expand, List.map_cons, List.flatMap_cons, List.map_append, List.map_replicate] at ih ⊢
    rw [ih]

theorem expand_map_one {α : Type*} (l : List α) : expand (l.map (·, 1)) = l := by
  induction l with
  | nil => simp [expand]
  | cons a l ih =>
    simp only [expand, List.map_cons, List.flatMap_cons, List.replicate_one, List.singleton_append] at ih ⊢
    rw [ih]

theorem expand_map_one_f {α β : Type*} (f : α → β) (l : List α) :
    expand (l.map fun a => (f a, 1)) = l.map f := by
  induction l with
  | nil => simp [expand]
  | cons a l ih =>
    simp only [expand, List.map_cons, List.flatMap_cons, List.replicate_one, List.singleton_append] at ih ⊢
    rw [ih]

theorem expand_append {α : Type*} (l₁ l₂ : List (α × ℕ)) :
    expand (l₁ ++ l₂) = expand l₁ ++ expand l₂ := by
  simp [expand, List.flatMap_append]

theorem sum_ite_eq {α : Type*} [DecidableEq α] (cells : List α) (hnd : cells.Nodup) (a : α)
    (g : α → ℕ) : (cells.map fun c => if c = a then g c else 0).sum = if a ∈ cells then g a else 0 := by
  induction cells with
  | nil => simp
  | cons c cs ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons, List.mem_cons]
    rw [ih hnd.2]
    by_cases hca : c = a
    · subst hca; simp [hnd.1]
    · by_cases hac : a ∈ cs <;> simp [hca, hac, Ne.symm hca]

/-- **The multiset a consumer list names is the expansion of the per-cell counts** (the
completeness content of `mv` / `mx`): every consumed noun is a row, so the counts account for all
of it. -/
theorem perm_expand_count (cells cs : List Noun) (hnd : cells.Nodup) (hsub : ∀ c ∈ cs, c ∈ cells) :
    cs.Perm (expand (cells.map fun c => (c, cs.count c))) := by
  rw [List.perm_iff_count]
  intro a
  simp only [expand, List.count_flatMap, List.map_map, Function.comp_def, List.count_replicate]
  have : (cells.map fun c => if (c == a) = true then cs.count c else 0) =
      (cells.map fun c => if c = a then cs.count c else 0) := by
    apply List.map_congr_left; intro c _; simp
  rw [this, sum_ite_eq cells hnd a (fun c => cs.count c)]
  by_cases ha : a ∈ cells
  · simp [ha]
  · have : cs.count a = 0 := List.count_eq_zero.mpr fun h => ha (hsub a h)
    simp [ha, this]

end Balance


/-! ## 5. The row gates hold -/

section Gates
variable {q : ℕ} {Kfp : Type*} [Field Kfp] [Algebra (ZMod q) Kfp]

theorem limb_split (M a b : ℕ) (hM : 0 < M) :
    (a + b + 1) % M + ((a % M + b % M + 1) / M) * M = a % M + b % M + 1 ∧
    (a + b + 1) / M = a / M + b / M + (a % M + b % M + 1) / M := by
  have ha := Nat.div_add_mod a M
  have hb := Nat.div_add_mod b M
  have hsum : a + b + 1 = M * (a / M + b / M) + (a % M + b % M + 1) := by
    rw [Nat.mul_add]; omega
  rw [hsum, Nat.mul_add_mod, Nat.mul_add_div hM]
  have ht := Nat.div_add_mod (a % M + b % M + 1) M
  constructor
  · have hc : ((a % M + b % M + 1) / M) * M = M * ((a % M + b % M + 1) / M) := Nat.mul_comm _ _
    omega
  · omega

theorem rank_cell (a b : Noun) : rankOf (.cell a b) = rankOf a + rankOf b + 1 := by
  simp only [rankOf, Noun.internal]; omega

theorem rank_lt_cell_left (a b : Noun) : rankOf a < rankOf (.cell a b) := by
  rw [rank_cell]; omega

theorem rank_lt_cell_right (a b : Noun) : rankOf b < rankOf (.cell a b) := by
  rw [rank_cell]; omega

/-- **`genMemTable_rank_limbs`**: the generated row's limbs satisfy exactly the hypotheses of
`mu_limbs_exact` (ranges, carry, the two limb equations over `ℕ`), and hence the rank is exact:
`mu = muL + muR + 1`, `mu = internal`. -/
theorem genMemTable_rank_limbs (cells vcs xcs : List Noun) (a b : Noun)
    (hlt : rankOf (.cell a b) < 2 ^ 110) :
    let c := rowB0 q cells vcs xcs (.cell a b)
    c.lo < 2 ^ 62 ∧ c.loL < 2 ^ 62 ∧ c.loR < 2 ^ 62 ∧
    c.hi < 2 ^ 48 ∧ c.hiL < 2 ^ 48 ∧ c.hiR < 2 ^ 48 ∧ c.carry ≤ 1 ∧
    c.lo + c.carry * 2 ^ 62 = c.loL + c.loR + 1 ∧ c.hi = c.hiL + c.hiR + c.carry ∧
    c.mu = rankOf (.cell a b) ∧ c.muL = rankOf a ∧ c.muR = rankOf b := by
  intro c
  have hM : (0 : ℕ) < 2 ^ 62 := by positivity
  obtain ⟨h1, h2⟩ := limb_split (2 ^ 62) (rankOf a) (rankOf b) hM
  have hr := rank_cell a b
  have hla := rank_lt_cell_left a b
  have hlb := rank_lt_cell_right a b
  have e110 : (2 : ℕ) ^ 110 = 2 ^ 62 * 2 ^ 48 := by norm_num
  have ha2 := Nat.mod_lt (rankOf a) hM
  have hb2 := Nat.mod_lt (rankOf b) hM
  have hn2 := Nat.mod_lt (rankOf (.cell a b)) hM
  have hhi : ∀ r : ℕ, r < 2 ^ 110 → r / 2 ^ 62 < 2 ^ 48 := fun r hr => by
    rw [Nat.div_lt_iff_lt_mul hM]; rw [e110] at hr; omega
  have hcar : (rankOf a % 2 ^ 62 + rankOf b % 2 ^ 62 + 1) / 2 ^ 62 ≤ 1 := by
    have : (rankOf a % 2 ^ 62 + rankOf b % 2 ^ 62 + 1) / 2 ^ 62 < 2 := by
      rw [Nat.div_lt_iff_lt_mul hM]; omega
    omega
  have hmu : c.mu = rankOf (.cell a b) := by
    simp only [c, rowB0, CellRowB0.mu]; exact Nat.div_add_mod' _ _
  refine ⟨hn2, ha2, hb2, hhi _ hlt, hhi _ (by omega), hhi _ (by omega), hcar, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [c, rowB0]; rw [hr]; exact h1
  · simp only [c, rowB0]; rw [hr]; exact h2
  · exact hmu
  · simp only [c, rowB0, CellRowB0.muL]; exact Nat.div_add_mod' _ _
  · simp only [c, rowB0, CellRowB0.muR]; exact Nat.div_add_mod' _ _


theorem limb_gates_of_nat (c : CellRowB0 q)
    (e1 : c.lo + c.carry * 2 ^ 62 = c.loL + c.loR + 1) (e2 : c.hi = c.hiL + c.hiR + c.carry) :
    ((c.lo : ZMod q) + (c.carry : ZMod q) * 2 ^ 62 = (c.loL : ZMod q) + (c.loR : ZMod q) + 1) ∧
    ((c.hi : ZMod q) = (c.hiL : ZMod q) + (c.hiR : ZMod q) + (c.carry : ZMod q)) := by
  constructor
  · have := congrArg (Nat.cast : ℕ → ZMod q) e1
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] at this
    exact this
  · have := congrArg (Nat.cast : ℕ → ZMod q) e2
    rw [Nat.cast_add, Nat.cast_add] at this
    exact this

/-- **Every generated row satisfies the row gates** at a nonzero seed: the cons gate is `FP.cons`
(`enc_cons`), the limb ranges, the carry, the two limb equations in `ZMod q`, and the atom gates. -/
theorem genMemTable_rowOK [NeZero q] {z : Kfp} (hz : z ≠ 0) (cells vcs xcs : List Noun)
    (hrank : ∀ n ∈ cells, rankOf n < 2 ^ 110) (hatoms : ∀ n ∈ cells, AtomsLt q n)
    (hcell : ∀ n ∈ cells, n.isCell = true) {n : Noun} (hn : n ∈ cells) :
    RowOK z (⟨rowB0 q cells vcs xcs n, GlobalCarryRecognizer.enc z n,
      GlobalCarryRecognizer.enc z (hdN n), GlobalCarryRecognizer.enc z (tlN n)⟩ : CellRow q Kfp) := by
  have hc := hcell _ hn
  cases n with
  | atom _ => simp [Noun.isCell] at hc
  | cell a b =>
    obtain ⟨hlo, hloL, hloR, hhi, hhiL, hhiR, hcar, e1, e2, -, -, -⟩ :=
      genMemTable_rank_limbs (q := q) cells vcs xcs a b (hrank _ hn)
    have hat := hatoms _ hn
    refine ⟨GlobalCarryRecognizer.enc_cons hz a b, hlo, hloL, hloR, hhi, hhiL, hhiR, hcar, ?_, ?_, ?_, ?_⟩
    · exact (limb_gates_of_nat _ e1 e2).1
    · exact (limb_gates_of_nat _ e1 e2).2
    · intro hw
      cases a with
      | cell x y => simp [rowB0, Noun.isCell] at hw
      | atom v =>
        refine ⟨?_, by simp [rowB0, rankOf, Noun.internal], by simp [rowB0, rankOf, Noun.internal]⟩
        simp only [rowB0, hdN]
        rw [atom_enc, natCast_val v (hat.left v (by simp [Noun.leafList]))]
    · intro hw
      cases b with
      | cell x y => simp [rowB0, Noun.isCell] at hw
      | atom v =>
        refine ⟨?_, by simp [rowB0, rankOf, Noun.internal], by simp [rowB0, rankOf, Noun.internal]⟩
        simp only [rowB0, tlN]
        rw [atom_enc, natCast_val v (hat.right v (by simp [Noun.leafList]))]

theorem genMemTable_rows_ok [NeZero q] {z : Kfp} (hz : z ≠ 0) (cells vcs xcs : List Noun)
    (hrank : ∀ n ∈ cells, rankOf n < 2 ^ 110) (hatoms : ∀ n ∈ cells, AtomsLt q n)
    (hcell : ∀ n ∈ cells, n.isCell = true) :
    ∀ c ∈ tableRows (q := q) z cells vcs xcs, RowOK z c := by
  intro c hc
  simp only [tableRows, List.mem_map] at hc
  obtain ⟨n, hn, rfl⟩ := hc
  exact genMemTable_rowOK hz cells vcs xcs hrank hatoms hcell hn

end Gates

/-! ## 6. The three balances -/

section Balanced
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Algebra (ZMod q) Kfp]

/-- The validity key of a cell: `(fn, hi, lo, idx)`. -/
noncomputable def vkeyOf (z : Kfp) (cells : List Noun) (n : Noun) : VKey Kfp :=
  (GlobalCarryRecognizer.enc z n, rankOf n / 2 ^ 62, rankOf n % 2 ^ 62, cells.idxOf n)

/-- The export key of a cell: `(fn, fn_L, fn_R, idx)` (option R, `m_x = 10`). -/
noncomputable def xkeyOf (z : Kfp) (cells : List Noun) (n : Noun) : XKey Kfp :=
  (GlobalCarryRecognizer.enc z n, GlobalCarryRecognizer.enc z (hdN n),
    GlobalCarryRecognizer.enc z (tlN n), cells.idxOf n)

/-- **The validity consumers**: every cell child of every row (in-degree) plus the root bindings
(subject and formula of every compute row; atoms carry no row). -/
def vcsOf (cells binds : List Noun) : List Noun :=
  cells.flatMap childCells ++ binds.flatMap selfCell

theorem expand_flatMap {α β : Type*} (f : α → List (β × ℕ)) (l : List α) :
    expand (l.flatMap f) = l.flatMap fun a => expand (f a) := by
  induction l with
  | nil => simp [expand]
  | cons a l ih => simp [List.flatMap_cons, expand_append, ih]

theorem vProv_rows (z : Kfp) (cells vcs xcs : List Noun) (hcell : ∀ n ∈ cells, n.isCell = true) :
    vProv (tableRows (q := q) z cells vcs xcs) = cells.map fun n => (vkeyOf z cells n, vcs.count n) := by
  simp only [vProv, tableRows, List.map_map]
  apply List.map_congr_left
  intro n hn
  have := hcell n hn
  cases n with
  | atom _ => simp [Noun.isCell] at this
  | cell a b => rfl

theorem expand_vCons_row (z : Kfp) (cells vcs xcs : List Noun) {n : Noun} (hc : n.isCell = true) :
    expand (vCons [(⟨rowB0 q cells vcs xcs n, GlobalCarryRecognizer.enc z n,
      GlobalCarryRecognizer.enc z (hdN n), GlobalCarryRecognizer.enc z (tlN n)⟩ : CellRow q Kfp)]) =
    (childCells n).map (vkeyOf z cells) := by
  cases n with
  | atom _ => simp [Noun.isCell] at hc
  | cell a b =>
    cases a <;> cases b <;>
      simp [vCons, expand, vkeyOf, rowB0, childCells, selfCell, hdN, tlN, Noun.isCell]

theorem expand_vCons (z : Kfp) (cells vcs xcs : List Noun) (hcell : ∀ n ∈ cells, n.isCell = true) :
    expand (vCons (tableRows (q := q) z cells vcs xcs)) =
    (cells.flatMap childCells).map (vkeyOf z cells) := by
  unfold vCons tableRows
  rw [List.flatMap_map, expand_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro n hn
  have := expand_vCons_row (q := q) z cells vcs xcs (hcell n hn)
  simpa [vCons] using this

/-- **`genMemTable_mv_eq_consumers`**: a row's `mv` is its in-degree (the child references to it
among the closure's rows) plus its root bindings. -/
theorem genMemTable_mv_eq_consumers (cells binds xcs : List Noun) {n : Noun} (hc : n.isCell = true) :
    (rowB0 q cells (vcsOf cells binds) xcs n).mv =
      (cells.flatMap childCells).count n + (binds.flatMap selfCell).count n := by
  cases n with
  | atom _ => simp [Noun.isCell] at hc
  | cell a b => simp [rowB0, vcsOf, List.count_append]

/-- **`genMemTable_mx_eq_consumers`**: a row's `mx` is the number of its export consumptions
(path-chip edge rows with this parent, plus compute cell lookups of it). -/
theorem genMemTable_mx_eq_consumers (cells vcs xcs : List Noun) {n : Noun} (hc : n.isCell = true) :
    (rowB0 q cells vcs xcs n).mx = xcs.count n := by
  cases n with
  | atom _ => simp [Noun.isCell] at hc
  | cell a b => rfl

/-- **The validity balance** (`ValidityBalanced`): the table's validity multiset equals its own
child consumptions plus the root bindings.  Needs: a nodup closure of cells, closed under children,
containing the bound cells. -/
theorem genMemTable_validity_balanced (z : Kfp) (cells binds xcs : List Noun)
    (hnd : cells.Nodup) (hcell : ∀ n ∈ cells, n.isCell = true)
    (hclosed : ∀ n ∈ cells, ∀ c ∈ childCells n, c ∈ cells)
    (hbind : ∀ b ∈ binds.flatMap selfCell, b ∈ cells) :
    ValidityBalanced (tableRows (q := q) z cells (vcsOf cells binds) xcs)
      ((binds.flatMap selfCell).map (vkeyOf z cells)) := by
  unfold ValidityBalanced
  have hsub : ∀ c ∈ vcsOf cells binds, c ∈ cells := by
    intro c hc
    simp only [vcsOf, List.mem_append, List.mem_flatMap] at hc
    rcases hc with ⟨n, hn, hcn⟩ | h
    · exact hclosed n hn c hcn
    · exact hbind c (List.mem_flatMap.mpr h)
  have hperm := perm_expand_count cells (vcsOf cells binds) hnd hsub
  rw [vProv_rows z cells _ xcs hcell, expand_append, expand_vCons z cells _ xcs hcell, expand_map_one,
    ← List.map_append]
  have h1 : (cells.map fun n => (vkeyOf z cells n, (vcsOf cells binds).count n)) =
      (cells.map fun n => (n, (vcsOf cells binds).count n)).map fun kc => (vkeyOf z cells kc.1, kc.2) := by
    simp [List.map_map, Function.comp_def]
  rw [h1, expand_map_fst]
  exact (hperm.symm.map (vkeyOf z cells))

theorem xProv_rows (z : Kfp) (cells vcs xcs : List Noun) (hcell : ∀ n ∈ cells, n.isCell = true) :
    xProv (tableRows (q := q) z cells vcs xcs) = cells.map fun n => (xkeyOf z cells n, xcs.count n) := by
  simp only [xProv, tableRows, List.map_map]
  apply List.map_congr_left
  intro n hn
  have := hcell n hn
  cases n with
  | atom _ => simp [Noun.isCell] at this
  | cell a b => rfl

/-- **`genMemTable_mx_eq_consumers` / the export balance**: the table's export multiset equals the
path chip's edge consumptions plus the compute cell lookups, whenever those two lists are exactly
the export consumers `xcs` (`mx n = xcs.count n`). -/
theorem genMemTable_export_balanced (z : Kfp) (cells vcs xcs : List Noun)
    (hnd : cells.Nodup) (hcell : ∀ n ∈ cells, n.isCell = true) (hsub : ∀ c ∈ xcs, c ∈ cells)
    (edges : List (Edge Kfp)) (cl : List (XKey Kfp))
    (hx : edges.map (fun e => (e.p, e.l, e.r, e.cellIdx)) ++ cl = xcs.map (xkeyOf z cells)) :
    ExportBalanced (tableRows (q := q) z cells vcs xcs) edges cl := by
  unfold ExportBalanced
  have hperm := perm_expand_count cells xcs hnd hsub
  rw [xProv_rows z cells vcs xcs hcell, expand_append, expand_map_one_f, expand_map_one, hx]
  have h1 : (cells.map fun n => (xkeyOf z cells n, xcs.count n)) =
      (cells.map fun n => (n, xcs.count n)).map fun kc => (xkeyOf z cells kc.1, kc.2) := by
    simp [List.map_map, Function.comp_def]
  rw [h1, expand_map_fst]
  exact (hperm.symm.map (xkeyOf z cells))

/-- **An accepted table** (the parts T1 reads): serial gate, every row gate, validity balance —
for the generated table, from a nodup closed closure. -/
theorem genMemTable_accepts [NeZero q] {z : Kfp} (hz : z ≠ 0) (cells binds xcs : List Noun)
    (hnd : cells.Nodup) (hcell : ∀ n ∈ cells, n.isCell = true)
    (hclosed : ∀ n ∈ cells, ∀ c ∈ childCells n, c ∈ cells)
    (hbind : ∀ b ∈ binds.flatMap selfCell, b ∈ cells)
    (hrank : ∀ n ∈ cells, rankOf n < 2 ^ 110) (hatoms : ∀ n ∈ cells, AtomsLt q n) :
    TableAccepts z (tableRows (q := q) z cells (vcsOf cells binds) xcs)
      ((binds.flatMap selfCell).map (vkeyOf z cells)) where
  serial := by
    rw [tableRows_b0]; exact genMemTable_serial cells _ _ hnd hcell
  rows := genMemTable_rows_ok hz cells _ xcs hrank hatoms hcell
  served := (genMemTable_validity_balanced z cells binds xcs hnd hcell hclosed hbind).served

end Balanced


/-! ## 7. The closure meets the hypotheses -/

section Closure
variable {q : ℕ}

theorem rank_le_of_mem_cellsOf {n c : Noun} (h : c ∈ cellsOf n) : rankOf c ≤ rankOf n := by
  induction n with
  | atom _ => simp [cellsOf] at h
  | cell a b iha ihb =>
    simp only [cellsOf, List.mem_cons, List.mem_append] at h
    rw [rank_cell]
    rcases h with rfl | h | h
    · rw [rank_cell]
    · have := iha h; omega
    · have := ihb h; omega

theorem atomsLt_of_mem_cellsOf {n c : Noun} (h : c ∈ cellsOf n) (hn : AtomsLt q n) :
    AtomsLt q c := by
  induction n with
  | atom _ => simp [cellsOf] at h
  | cell a b iha ihb =>
    simp only [cellsOf, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact hn
    · exact iha h hn.left
    · exact ihb h hn.right

/-- **The generated closure meets every table hypothesis**, from per-root hypotheses: nodup, all
cells, closed under children, ranks `< 2^110`, atoms `< q`. -/
theorem closureOf_hyps (roots : List Noun) (hrank : ∀ r ∈ roots, rankOf r < 2 ^ 110)
    (hatoms : ∀ r ∈ roots, AtomsLt q r) :
    (closureOf roots).Nodup ∧ (∀ n ∈ closureOf roots, n.isCell = true) ∧
    (∀ n ∈ closureOf roots, ∀ c ∈ childCells n, c ∈ closureOf roots) ∧
    (∀ n ∈ closureOf roots, rankOf n < 2 ^ 110) ∧ (∀ n ∈ closureOf roots, AtomsLt q n) := by
  refine ⟨closureOf_nodup roots, fun n hn => closureOf_isCell hn,
    fun n hn c hc => closureOf_closed hn hc, ?_, ?_⟩
  · intro n hn
    obtain ⟨r, hr, hnr⟩ := mem_closureOf.mp hn
    exact lt_of_le_of_lt (rank_le_of_mem_cellsOf hnr) (hrank r hr)
  · intro n hn
    obtain ⟨r, hr, hnr⟩ := mem_closureOf.mp hn
    exact atomsLt_of_mem_cellsOf hnr (hatoms r hr)

theorem selfCell_subset_closureOf {roots : List Noun} {b c : Noun} (hb : b ∈ roots)
    (hc : c ∈ selfCell b) : c ∈ closureOf roots :=
  mem_closureOf.mpr ⟨b, hb, selfCell_mem_cellsOf hc⟩

theorem cell_mem_closureOf {roots : List Noun} {b : Noun} (hb : b ∈ roots) {x y : Noun}
    (h : b = .cell x y) : b ∈ closureOf roots :=
  mem_closureOf.mpr ⟨b, hb, h ▸ mem_cellsOf_self⟩

end Closure

end Nock.NockVMROM.Thm54.VclL
