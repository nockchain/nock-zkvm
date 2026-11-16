/-
  Nock/NockVMROM/Thm54/VclL/Chips/Prelim.lean

  **The interface-independent preliminaries of
  `vclMemFamily`.**

  * `quad_ringChar` — `ringChar 𝕂′ = ringChar 𝕂` (`ExtraPremises.char_eq` at `Kfp = Quad δ`);
  * `decodeB0_boundedBy`, `preZNounOfTable_getD_boundedBy` — every B0-decoded noun is over `𝔽`
    (`ExtraPremises.served_bounded`: the served roots are `decodeB0` values, atoms `ZMod q`-`val`s);
  * `decode_exists` — on an accepted table every row's serial decodes (at any fuel above its rank) to
    a cell with `μ + 1` leaves, at ANY seed, including `z = 0` (no `hz`: the fingerprint half of
    `decode_sound` is dropped);
  * `zero_mem_cellDyckRootSeeds`, `seed_ne_zero_of_not_mem_dyck` — the dyck polynomial of every cell
    has zero constant term (its Dyck word starts with `0`, `Dyck.lean::encode`), so `z = 0` lies in
    the dyck-root event as soon as the table has a row: outside V0's dyck summand the seed is nonzero,
    with no summand of its own.
-/
import Nock.NockVMROM.Thm54.P8Core.VclL.DyckRoot
import Nock.NockVMROM.Thm54.P8Core.Batch1541Thm54T0Tower

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Chips

open Nock Polynomial
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.T0Tower

/-! ## 1. `char_eq` at the tower -/

/-- **`ringChar 𝕂′ = ringChar 𝕂`** (`𝕂′ = 𝕂[X]/(X² − δ)` is a `𝕂`-algebra field). -/
theorem quad_ringChar {K : Type} [Field K] (δ : K) [Fact (¬ IsSquare δ)] :
    ringChar (Quad δ) = ringChar K :=
  (Algebra.ringChar_eq K (Quad δ)).symm

/-! ## 2. `served_bounded`: B0-decoded nouns are over `𝔽` -/

theorem boundedBy_of_leafList {q : ℕ} : ∀ n : Noun, (∀ k ∈ n.leafList, k < q) →
    FieldEmbedding.BoundedBy q n
  | .atom a, h => by simpa [Noun.leafList] using h
  | .cell l r, h => by
    simp only [Noun.leafList, List.mem_append] at h
    exact ⟨boundedBy_of_leafList l fun k hk => h k (Or.inl hk),
      boundedBy_of_leafList r fun k hk => h k (Or.inr hk)⟩

/-- **Every B0-decoded noun is over `𝔽`** (`decodeB0_leafList_lt`). -/
theorem decodeB0_boundedBy {q : ℕ} [NeZero q] (t : List (CellRowB0 q)) {f i : ℕ} {n : Noun}
    (h : decodeB0 t f i = some n) : FieldEmbedding.BoundedBy q n :=
  boundedBy_of_leafList n (decodeB0_leafList_lt t f i n h)

/-- The served-root shape `(preZNounOfTable t i).getD (atom 0)` is over `𝔽` (for `0 < q`). -/
theorem preZNounOfTable_getD_boundedBy {q : ℕ} [NeZero q] (t : List (CellRowB0 q)) (i : ℕ) :
    FieldEmbedding.BoundedBy q ((preZNounOfTable t i).getD (.atom 0)) := by
  cases h : preZNounOfTable t i with
  | none => exact (Nat.pos_of_ne_zero (NeZero.ne q) : 0 < q)
  | some n => exact decodeB0_boundedBy t h

/-! ## 3. Decode existence at any seed -/

section Exists
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Algebra (ZMod q) Kfp]

/-- **Decode existence without `hz`**: the round-0 half of `decode_sound`. -/
theorem decode_exists [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp}
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl) :
    ∀ n, ∀ c ∈ t, c.b0.mu = n → ∀ fuel, n < fuel →
      ∃ L R, decodeB0 (t.map (·.b0)) fuel c.b0.idx = some (.cell L R) ∧
        (Noun.cell L R).leaves = n + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hc hn fuel hf
  obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  have hok := h.rows c hc
  have hrank := rowOK_mu hq hok
  have hleft : ∃ a, childL (t.map (·.b0)) fuel c.b0 = some a ∧ a.leaves = c.b0.muL + 1 := by
    cases hw : c.b0.wL with
    | false =>
      obtain ⟨-, hlo, hhi⟩ := hok.atomL hw
      exact ⟨.atom c.b0.aL.val, by simp [childL, hw], by
        simp [Noun.leaves, CellRowB0.muL, hlo, hhi]⟩
    | true =>
      obtain ⟨c', hc', -, hhiL, hloL, hidL⟩ := consumed_left h.served hc hw
      have hmu : c'.b0.mu = c.b0.muL := by simp [CellRowB0.mu, CellRowB0.muL, hhiL, hloL]
      have hval : c'.b0.mu < n := by rw [hmu, ← hn, hrank]; omega
      obtain ⟨L, R, hd, hlv⟩ := ih _ hval c' hc' rfl fuel (by omega)
      exact ⟨.cell L R, by simp [childL, hw, hidL, hd], by rw [hlv, hmu]⟩
  have hright : ∃ b, childR (t.map (·.b0)) fuel c.b0 = some b ∧ b.leaves = c.b0.muR + 1 := by
    cases hw : c.b0.wR with
    | false =>
      obtain ⟨-, hlo, hhi⟩ := hok.atomR hw
      exact ⟨.atom c.b0.aR.val, by simp [childR, hw], by
        simp [Noun.leaves, CellRowB0.muR, hlo, hhi]⟩
    | true =>
      obtain ⟨c', hc', -, hhiR, hloR, hidR⟩ := consumed_right h.served hc hw
      have hmu : c'.b0.mu = c.b0.muR := by simp [CellRowB0.mu, CellRowB0.muR, hhiR, hloR]
      have hval : c'.b0.mu < n := by rw [hmu, ← hn, hrank]; omega
      obtain ⟨L, R, hd, hlv⟩ := ih _ hval c' hc' rfl fuel (by omega)
      exact ⟨.cell L R, by simp [childR, hw, hidR, hd], by rw [hlv, hmu]⟩
  obtain ⟨a, hda, hla⟩ := hleft
  obtain ⟨b, hdb, hlb⟩ := hright
  have hmem : c.b0 ∈ t.map (·.b0) := List.mem_map_of_mem hc
  refine ⟨a, b, ?_, ?_⟩
  · rw [decodeB0_succ, serial_lookup h.serial hmem, Option.bind_some, hda, Option.bind_some, hdb,
      Option.bind_some]
  · simp only [Noun.leaves] at hla hlb ⊢; rw [hla, hlb, ← hn, hrank]; ring

/-- A row of an accepted table decodes, at the certified fuel, to a decoded cell of the table. -/
theorem row_decoded_cell [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp}
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl)
    {c : CellRow q Kfp} (hc : c ∈ t) :
    ∃ L R, Noun.cell L R ∈ decodedNouns (t.map (·.b0)) ∧ (Noun.cell L R).leaves ≤ fuelChip := by
  have hlt := rowOK_mu_lt (h.rows c hc)
  obtain ⟨L, R, hd, hlv⟩ := decode_exists hq h _ c hc rfl fuelChip hlt
  exact ⟨L, R, mem_decodedNouns_of hd, by omega⟩

end Exists

/-! ## 4. `z = 0` is a dyck root of every cell -/

section Zero
variable {Kfp : Type} [Field Kfp]

/-- **The dyck polynomial of a cell vanishes at `0`** (its Dyck word starts with `0`). -/
theorem dyck_cell_eval_zero (L R : Noun) :
    (NPR.listPoly (NPR.dyckBits (K := Kfp) (.cell L R))).eval 0 = 0 := by
  have : NPR.dyckBits (K := Kfp) (.cell L R) =
      (0 : Kfp) :: NPR.dyckBits (K := Kfp) L ++ ((1 : Kfp) :: NPR.dyckBits (K := Kfp) R) := by
    simp [NPR.dyckBits, Noun.dyckWord, Noun.shape, Nock.BTree.encode]
  rw [this, List.cons_append, NPR.listPoly_cons]
  simp

variable {q : ℕ} [Fintype Kfp] [DecidableEq Kfp] [Algebra (ZMod q) Kfp]

/-- **`0` is in the dyck-root event of every nonempty accepted table.** -/
theorem zero_mem_cellDyckRootSeeds [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp}
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl)
    {c : CellRow q Kfp} (hc : c ∈ t) :
    (0 : Kfp) ∈ cellDyckRootSeeds fuelChip (t.map (·.b0)) := by
  obtain ⟨L, R, hmem, hle⟩ := row_decoded_cell hq h hc
  exact mem_cellDyckRootSeeds hmem rfl hle (dyck_cell_eval_zero L R)

/-- **Outside the dyck-root event the seed is nonzero** (on a table with a row). -/
theorem seed_ne_zero_of_not_mem_dyck [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp}
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl)
    {c : CellRow q Kfp} (hc : c ∈ t) (hgood : z ∉ cellDyckRootSeeds fuelChip (t.map (·.b0))) :
    z ≠ 0 := by
  rintro rfl
  exact hgood (zero_mem_cellDyckRootSeeds hq h hc)

end Zero

end Nock.NockVMROM.Thm54.VclL.Chips
