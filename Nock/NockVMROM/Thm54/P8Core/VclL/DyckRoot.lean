/-
  Nock/NockVMROM/Thm54/P8Core/VclL/DyckRoot.lean

An atom's fingerprint has dyck component `0` (`enc_atom`, the paper's `(z, 0, ·)`); a cell's
  dyck polynomial `F_w = listPoly (dyckBits n)` is NONZERO (its Dyck word `0 w_L 1 w_R` carries a
  `1`, `Noun.dyckWord`) of natDegree `≤ 2λ − 3 ≤ 2Λ − 1`.  So `enc z atom = enc z cell` forces
  `F_w(cell)(z) = 0`, and the event "some decoded cell's `F_w` vanishes at the seed" has at most
  `D · (2Λ − 1)` seeds — linear in `D`, independent of the atom values.

  * `dyck_cell_ne_zero`, `dyck_natDegree_le`, `enc_atom_dyck`, `dyck_root_of_atom_collision` (1);
  * `cellDyckRootSeeds`, `cellDyckRootSeeds_card_le` (2, field-generic);
  * `towerSeedSummand` (any B0-const bad seed set over `𝕂′` as a `BadSummand` on two coins),
    `cellDyckRootSummand`, `vclCellDyckRootSummand` at `frameVCL` coins `2, 3` (2, 3);
-/
import Nock.NockVMROM.Thm54.P8Core.VclL.Chain

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL

open Nock Polynomial
open Nock.ComputeTable (FP)

/-! ## 1. Non-vacuity -/

section Dyck
variable {Kfp : Type} [Field Kfp]

theorem listPoly_replicate_zero : ∀ n : ℕ, NPR.listPoly (List.replicate n (0 : Kfp)) = 0
  | 0 => by simp
  | n + 1 => by rw [List.replicate_succ, NPR.listPoly_cons, listPoly_replicate_zero n]; simp

/-- **A cell's dyck polynomial is nonzero.** -/
theorem dyck_cell_ne_zero (L R : Noun) :
    NPR.listPoly (NPR.dyckBits (K := Kfp) (.cell L R)) ≠ 0 := by
  set l := NPR.dyckBits (K := Kfp) (.cell L R)
  have hone : (1 : Kfp) ∈ l := by
    simp only [l, NPR.dyckBits, Noun.dyckWord, Noun.shape, Nock.BTree.encode, List.map_cons,
      List.map_append, List.mem_cons, List.mem_append]
    simp
  have hne : l ≠ List.replicate l.length 0 := by
    intro h
    rw [h] at hone
    exact one_ne_zero (List.eq_of_mem_replicate hone)
  have := NPR.listPoly_sub_ne_zero (by simp) hne
  rwa [listPoly_replicate_zero, sub_zero] at this

/-- The dyck polynomial of a noun with `≤ Λ` leaves has natDegree `≤ 2Λ − 1`. -/
theorem dyck_natDegree_le {Λ : ℕ} (n : Noun) (h : n.leaves ≤ Λ) :
    (NPR.listPoly (NPR.dyckBits (K := Kfp) n)).natDegree ≤ 2 * Λ - 1 := by
  refine (NPR.listPoly_natDegree_le _).trans ?_
  have := NPR.dyckBits_length (K := Kfp) n
  omega

theorem enc_atom_dyck (z : Kfp) (k : ℕ) : (GlobalCarryRecognizer.enc z (.atom k)).dyck = 0 := by
  rw [GlobalCarryRecognizer.enc_atom]; rfl

/-- **An atom/noun fingerprint collision is a dyck root of the noun.** -/
theorem dyck_root_of_atom_collision (z : Kfp) (k : ℕ) (n : Noun)
    (h : GlobalCarryRecognizer.enc z (.atom k) = GlobalCarryRecognizer.enc z n) :
    (NPR.listPoly (NPR.dyckBits (K := Kfp) n)).eval z = 0 := by
  have := congrArg FP.dyck h
  rw [enc_atom_dyck, GlobalCarryRecognizer.enc_dyck] at this
  exact this.symm

end Dyck

/-! ## 2. The event and its card -/

section Event
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Fintype Kfp] [DecidableEq Kfp]
open scoped Classical

/-- The dyck roots of one noun, guarded: a cell with `≤ Λ` leaves. -/
noncomputable def dyckRoots (Λ : ℕ) (n : Noun) : Finset Kfp :=
  Finset.univ.filter fun z =>
    n.leaves ≤ Λ ∧ (∃ L R, n = .cell L R) ∧ (NPR.listPoly (NPR.dyckBits (K := Kfp) n)).eval z = 0

theorem dyckRoots_card_le (Λ : ℕ) (n : Noun) : (dyckRoots (Kfp := Kfp) Λ n).card ≤ 2 * Λ - 1 := by
  by_cases hg : n.leaves ≤ Λ ∧ ∃ L R, n = .cell L R
  · obtain ⟨hl, L, R, rfl⟩ := hg
    have hsub : dyckRoots (Kfp := Kfp) Λ (.cell L R) ⊆
        Finset.univ.filter fun z => (NPR.listPoly (NPR.dyckBits (K := Kfp) (.cell L R))).eval z = 0 := by
      intro z hz
      simp only [dyckRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hz.2.2
    exact (Finset.card_le_card hsub).trans ((NPR.card_eval_zero_le _ (dyck_cell_ne_zero L R)).trans
      (dyck_natDegree_le _ hl))
  · have : dyckRoots (Kfp := Kfp) Λ n = ∅ := by
      ext z; simp only [dyckRoots, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false]
      exact fun h => hg ⟨h.1, h.2.1⟩
    rw [this]; simp

/-- **`cellDyckRootSeeds`**: some decoded cell (serial `< |t|`, `≤ Λ` leaves) has `F_w(seed) = 0`. -/
noncomputable def cellDyckRootSeeds (Λ : ℕ) (t : List (CellRowB0 q)) : Finset Kfp :=
  (Finset.range t.length).biUnion fun i =>
    match preZNounOfTable t i with
    | some n => dyckRoots Λ n
    | none => ∅

/-- **Card `≤ D · (2Λ − 1)`**, `D = |t|`, no premise. -/
theorem cellDyckRootSeeds_card_le (Λ : ℕ) (t : List (CellRowB0 q)) :
    (cellDyckRootSeeds (Kfp := Kfp) Λ t).card ≤ t.length * (2 * Λ - 1) := by
  unfold cellDyckRootSeeds
  refine (Finset.card_biUnion_le_card_mul _ _ (2 * Λ - 1) ?_).trans (by simp)
  intro i _
  split
  · exact dyckRoots_card_le Λ _
  · simp

theorem mem_cellDyckRootSeeds {Λ : ℕ} {t : List (CellRowB0 q)} {z : Kfp} {n L R : Noun}
    (hn : n ∈ decodedNouns t) (hcell : n = .cell L R) (hl : n.leaves ≤ Λ)
    (h0 : (NPR.listPoly (NPR.dyckBits (K := Kfp) n)).eval z = 0) :
    z ∈ cellDyckRootSeeds Λ t := by
  obtain ⟨i, hi, hd⟩ := mem_decodedNouns.mp hn
  unfold cellDyckRootSeeds
  rw [Finset.mem_biUnion]
  refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
  rw [hd]
  simp only [dyckRoots, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hl, ⟨L, R, hcell⟩, h0⟩

end Event

/-! ## 3. As a summand over the tower seed -/

section Summand
open SVFrame T0Tower
open scoped Classical

variable {q : ℕ} {K : Type} [Field K] [Fintype K] [DecidableEq K] (δ : K) [Fact (¬ IsSquare δ)]

/-- **Any coin-free bad seed set over `𝕂′` as a summand** on two coins `i, j` (seed
`Quad.mk δ (χ i) (χ j)`), weight `W`, `dep = ∅` along any strategy along which `bad ∘ Q` is
constant. -/
noncomputable def towerSeedSummand (Φ : CoinFrame) (i j : Fin Φ.n)
    {Tr : Type} (Staged : (Coins Φ K → Tr) → Prop) (bad : Tr → Finset (Quad δ)) (W : ℕ)
    (hW : ∀ tr, (bad tr).card ≤ W)
    (hconst : ∀ Q, Staged Q → ∀ χ χ', bad (Q χ) = bad (Q χ')) :
    BadSummand Φ K Tr Staged where
  coins := {i, j}
  dep := ∅
  disj := Finset.disjoint_empty_right _
  badSet tr _ := Finset.univ.filter fun f => pairSeed δ i j f ∈ bad tr
  weight := W
  card_le tr _ := by
    refine le_trans ?_ (hW tr)
    refine Finset.card_le_card_of_injOn (pairSeed δ i j) ?_ ?_
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf
      exact hf
    · intro f _ f' _ h
      exact pairSeed_injective δ i j h
  readsOn Q hQ χ χ' _ := by
    show (Finset.univ.filter fun f => pairSeed δ i j f ∈ bad (Q χ)) =
      Finset.univ.filter fun f => pairSeed δ i j f ∈ bad (Q χ')
    rw [hconst Q hQ χ χ']

theorem towerSeedSummand_mem_iff (Φ : CoinFrame) (i j : Fin Φ.n)
    {Tr : Type} (Staged : (Coins Φ K → Tr) → Prop) (bad : Tr → Finset (Quad δ)) (W : ℕ) (hW hconst)
    (tr : Tr) (χ : Coins Φ K) :
    (towerSeedSummand δ Φ i j Staged bad W hW hconst).mem tr χ ↔ Quad.mk δ (χ i) (χ j) ∈ bad tr := by
  show (fun k : ({i, j} : Finset (Fin Φ.n)) => χ k) ∈ Finset.univ.filter (fun f => pairSeed δ i j f ∈ bad tr) ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **The dyck-root summand**: weight `D · (2Λ − 1)` over `|𝕂|²`, B0-const under the census's
`hconst` (the table rows are coin-independent). -/
noncomputable def cellDyckRootSummand (Φ : CoinFrame) (i j : Fin Φ.n)
    {Tr : Type} (Staged : (Coins Φ K → Tr) → Prop)
    (rowsOf : Tr → List (CellRowB0 q)) (D Λ : ℕ) (hD : ∀ tr, (rowsOf tr).length ≤ D)
    (hconst : ∀ Q, Staged Q → ∀ χ χ', rowsOf (Q χ) = rowsOf (Q χ')) :
    BadSummand Φ K Tr Staged :=
  towerSeedSummand δ Φ i j Staged (fun tr => cellDyckRootSeeds (Kfp := Quad δ) Λ (rowsOf tr))
    (D * (2 * Λ - 1))
    (fun tr => (cellDyckRootSeeds_card_le Λ _).trans (Nat.mul_le_mul_right _ (hD tr)))
    (fun Q hQ χ χ' => by simp only [hconst Q hQ χ χ'])

/-- At `frameVCL` coins `2, 3`, `Λ_chip = 2^110`. -/
noncomputable def vclCellDyckRootSummand {Tr : Type} (Staged : (Coins frameVCL K → Tr) → Prop)
    (rowsOf : Tr → List (CellRowB0 q)) (D : ℕ) (hD : ∀ tr, (rowsOf tr).length ≤ D)
    (hconst : ∀ Q, Staged Q → ∀ χ χ', rowsOf (Q χ) = rowsOf (Q χ')) :
    BadSummand frameVCL K Tr Staged :=
  cellDyckRootSummand δ frameVCL ⟨2, by decide⟩ ⟨3, by decide⟩ Staged rowsOf D fuelChip hD hconst

theorem vclCellDyckRootSummand_shape {Tr : Type} (Staged : (Coins frameVCL K → Tr) → Prop)
    (rowsOf : Tr → List (CellRowB0 q)) (D : ℕ) (hD hconst) :
    (vclCellDyckRootSummand δ Staged rowsOf D hD hconst).coins.card = 2 ∧
    (vclCellDyckRootSummand δ Staged rowsOf D hD hconst).dep = ∅ ∧
    (vclCellDyckRootSummand δ Staged rowsOf D hD hconst).weight = D * (2 * 2 ^ 110 - 1) :=
  ⟨Finset.card_pair (by decide), rfl, rfl⟩

theorem vclCellDyckRootSummand_mem_iff {Tr : Type} (Staged : (Coins frameVCL K → Tr) → Prop)
    (rowsOf : Tr → List (CellRowB0 q)) (D : ℕ) (hD hconst) (tr : Tr) (χ : Coins frameVCL K) :
    (vclCellDyckRootSummand δ Staged rowsOf D hD hconst).mem tr χ ↔
      Quad.mk δ (χ ⟨2, by decide⟩) (χ ⟨3, by decide⟩) ∈
        cellDyckRootSeeds (Kfp := Quad δ) fuelChip (rowsOf tr) := by
  unfold vclCellDyckRootSummand cellDyckRootSummand
  exact towerSeedSummand_mem_iff δ _ _ _ _ _ _ _ _ tr χ

end Summand

/-! ## 4. -/

section Use
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Fintype Kfp] [DecidableEq Kfp] [Algebra (ZMod q) Kfp]

/-- Outside the dyck-root event, no atom child collides with a decoded cell. -/
theorem hatom_of_not_mem_dyck [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0)
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl)
    (hgood : z ∉ cellDyckRootSeeds fuelChip (t.map (·.b0))) :
    ∀ a ∈ AtomChildren t, ∀ b ∈ decodedNouns (t.map (·.b0)),
      GlobalCarryRecognizer.enc z a ≠ GlobalCarryRecognizer.enc z b := by
  intro a ha b hb henc
  obtain ⟨c, -, hc⟩ := ha
  obtain ⟨k, rfl⟩ : ∃ k, a = .atom k := by
    rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨_, rfl⟩
  obtain ⟨i, -, hd⟩ := mem_decodedNouns.mp hb
  obtain ⟨L, R, hLR⟩ := decodeB0_isCell _ _ _ _ hd
  exact hgood (mem_cellDyckRootSeeds hb hLR (decoded_window hq hz h hb).1
    (dyck_root_of_atom_collision z k b henc))


theorem chain_sound_outside [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0)
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl)
    (skel : List Noun) (hT2 : z ∉ tableBadSeeds fuelChip (t.map (·.b0)) skel)
    (hdy : z ∉ cellDyckRootSeeds fuelChip (t.map (·.b0)))
    {rootIdx : ℕ} {root : Noun} (hroot : preZNounOfTable (t.map (·.b0)) rootIdx = some root)
    (es : List (Edge Kfp)) (hexp : ∀ e ∈ es, EdgeExported t e) {ch : FP Kfp}
    (hend : chainEnd (GlobalCarryRecognizer.enc z root) es = some ch) :
    ∃ n, GlobalCarryRecognizer.enc z n = ch ∧
      Noun.slot (axisFold (es.map Edge.side)) root = some n :=
  chain_sound_of_census hq hz h skel hT2 (hatom_of_not_mem_dyck hq hz h hdy) hroot es hexp hend

end Use

end Nock.NockVMROM.Thm54.VclL
