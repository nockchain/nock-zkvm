/-
  Nock/NockVMROM/Thm54/P8Core/VclL/Census.lean

`S := {preZNounOfTable t i | i < |t|} ++ skel` (the B0-decoded table nouns, then the compute
  skeleton nouns); the census prices EVERY unordered pair of `S` at distinct positions
  (`allPairs`), not the pregreen's `D` pairs.  The bad seeds are `PreSeedCensus.pairBadSeeds` (guarded at
  `Λ`, field-generic, `NPR.collision_card_le_tight`):
  card `≤ k(k−1)/2 · (2Λ − 1)` with `k = |S| ≤ D + Ksk`, NO premise on the traces beyond the two
  length majorants (rule 8(b)).

  * `allPairs`, `allPairs_length_mul_two`, `mem_allPairs_of_ne`, `pairCount`;
  * `decodedNouns`, `censusNouns`, `tableBadSeeds`, `tableBadSeeds_card_le`;

  * `tableCensusSummand` — the census as a `SVFrame.BadSummand` over two coins `(z₁, z₂)` of any
    frame, the seed `Quad.mk δ z₁ z₂ ∈ 𝕂′ = 𝕂(√δ)` (T0), `dep = ∅` (B0-const: the bad set is a
    function of the round-0 table and skeleton only), weight `pairCount (D + Ksk) · (2Λ − 1)`;
    `vclCensusSummand` at `frameVCL` coins `2, 3`, `Λ = 2^110`, `Ksk = 3 + 19N`.
-/
import Nock.NockVMROM.Thm54.P8Core.VclL.Table
import Nock.NockVMROM.Thm54.PreZCensusCore
import Nock.NockVMROM.Thm54.P8Core.SVFrame.MemSoundnessFamily
import Nock.NockVMROM.Thm54.P8Core.Batch1541Thm54T0Tower

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL

open Nock
open Nock.ComputeTable (FP)

/-! ## 1. All pairs at distinct positions -/

/-- The unordered pairs of a list at distinct positions. -/
def allPairs : List Noun → List (Noun × Noun)
  | [] => []
  | a :: l => l.map (a, ·) ++ allPairs l

theorem allPairs_length_mul_two : ∀ l : List Noun,
    (allPairs l).length * 2 = l.length * (l.length - 1)
  | [] => rfl
  | a :: l => by
    simp only [allPairs, List.length_append, List.length_map, List.length_cons]
    rw [Nat.add_mul, allPairs_length_mul_two l]
    cases l.length with
    | zero => simp
    | succ m => simp only [Nat.add_sub_cancel]; ring

/-- `k(k−1)/2`. -/
def pairCount (k : ℕ) : ℕ := k * (k - 1) / 2

theorem allPairs_length (l : List Noun) : (allPairs l).length = pairCount l.length := by
  unfold pairCount; rw [← allPairs_length_mul_two]; simp

theorem pairCount_mono {a b : ℕ} (h : a ≤ b) : pairCount a ≤ pairCount b :=
  Nat.div_le_div_right (Nat.mul_le_mul h (Nat.sub_le_sub_right h 1))

theorem pairCount_le_sq_div_two (k : ℕ) : pairCount k ≤ k ^ 2 / 2 :=
  Nat.div_le_div_right (by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))

theorem mem_allPairs_of_ne : ∀ (l : List Noun) {a b : Noun}, a ∈ l → b ∈ l → a ≠ b →
    (a, b) ∈ allPairs l ∨ (b, a) ∈ allPairs l
  | [], _, _, ha, _, _ => absurd ha (List.not_mem_nil)
  | x :: l, a, b, ha, hb, hne => by
    simp only [allPairs, List.mem_append, List.mem_map, Prod.mk.injEq]
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hne
      · exact Or.inl (Or.inl ⟨b, hb', rfl, rfl⟩)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr (Or.inl ⟨a, ha', rfl, rfl⟩)
      · rcases mem_allPairs_of_ne l ha' hb' hne with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

/-! ## 2. The decoded set and its bad seeds -/

section Census
variable {q : ℕ}

/-- The B0-decoded nouns of a round-0 table, one per serial `< |t|`. -/
def decodedNouns (t : List (CellRowB0 q)) : List Noun :=
  (List.range t.length).filterMap (preZNounOfTable t)

theorem decodedNouns_length_le (t : List (CellRowB0 q)) : (decodedNouns t).length ≤ t.length := by
  unfold decodedNouns
  exact (List.length_filterMap_le _ _).trans (by simp)

theorem mem_decodedNouns {t : List (CellRowB0 q)} {n : Noun} :
    n ∈ decodedNouns t ↔ ∃ i < t.length, preZNounOfTable t i = some n := by
  simp [decodedNouns, List.mem_filterMap, List.mem_range]

/-- The census noun list: decoded table nouns, then the skeleton nouns. -/
def censusNouns (t : List (CellRowB0 q)) (skel : List Noun) : List Noun := decodedNouns t ++ skel

theorem censusNouns_length_le (t : List (CellRowB0 q)) (skel : List Noun) :
    (censusNouns t skel).length ≤ t.length + skel.length := by
  unfold censusNouns; rw [List.length_append]
  exact Nat.add_le_add_right (decodedNouns_length_le t) _

variable {Kfp : Type} [Field Kfp] [Fintype Kfp] [DecidableEq Kfp]

/-- **The table all-pairs bad seeds**: some guarded pair of the census nouns is field-distinct and
fingerprint-equal at `z`. -/
noncomputable def tableBadSeeds (Λ : ℕ) (t : List (CellRowB0 q)) (skel : List Noun) : Finset Kfp :=
  PreSeedCensus.pairBadSeeds (K := Kfp) Λ (allPairs (censusNouns t skel))

/-- **T2, card**: `≤ k(k−1)/2 · (2Λ − 1)`, `k = |t| + |skel|`, no premise. -/
theorem tableBadSeeds_card_le (Λ : ℕ) (t : List (CellRowB0 q)) (skel : List Noun) :
    (tableBadSeeds (Kfp := Kfp) Λ t skel).card ≤
      pairCount (t.length + skel.length) * (2 * Λ - 1) := by
  refine (PreSeedCensus.pairBadSeeds_card_le Λ _).trans (Nat.mul_le_mul_right _ ?_)
  rw [allPairs_length]
  exact pairCount_mono (censusNouns_length_le t skel)

/-- A noun at a serial of an accepted table is the noun T1 decodes for the row AT that serial. -/
theorem decoded_window [Algebra (ZMod q) Kfp] [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp}
    (hz : z ≠ 0) {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl)
    {n : Noun} (hn : n ∈ decodedNouns (t.map (·.b0))) :
    n.leaves ≤ fuelChip ∧ ∀ k ∈ n.leafList, k < q := by
  obtain ⟨i, hi, hd⟩ := mem_decodedNouns.mp hn
  rw [List.length_map] at hi
  have hc : t[i] ∈ t := List.getElem_mem hi
  have hidx : t[i].b0.idx = i := by
    have h1 := congrArg (fun l => l[i]?) h.serial
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some] at h1
    rw [List.getElem?_range (by simpa using hi)] at h1
    exact Option.some.inj h1
  obtain ⟨n', hd', -, -, hle, hlt⟩ := preZNounOfTable_sound hq hz h _ hc
  rw [hidx, hd, Option.some.injEq] at hd'
  subst hd'
  exact ⟨hle, hlt⟩


theorem decodedNouns_inj_of_not_mem [Algebra (ZMod q) Kfp] [Fact q.Prime] (hq : 2 ^ 63 < q)
    {z : Kfp} (hz : z ≠ 0) {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)}
    (h : TableAccepts z t vl) (skel : List Noun)
    (hgood : z ∉ tableBadSeeds fuelChip (t.map (·.b0)) skel) :
    ∀ a ∈ decodedNouns (t.map (·.b0)), ∀ b ∈ decodedNouns (t.map (·.b0)),
      GlobalCarryRecognizer.enc z a = GlobalCarryRecognizer.enc z b → a = b := by
  intro a ha b hb henc
  haveI : CharP Kfp q := charP_of_injective_algebraMap (algebraMap (ZMod q) Kfp).injective q
  have hchar : ringChar Kfp = q := ringChar.eq Kfp q
  obtain ⟨hla, hqa⟩ := decoded_window hq hz h ha
  obtain ⟨hlb, hqb⟩ := decoded_window hq hz h hb
  by_contra hne
  have hma : a ∈ censusNouns (t.map (·.b0)) skel := List.mem_append_left _ ha
  have hmb : b ∈ censusNouns (t.map (·.b0)) skel := List.mem_append_left _ hb
  have hfield : (NPR.leafF (K := Kfp) a, NPR.dyckBits (K := Kfp) a)
      = (NPR.leafF (K := Kfp) b, NPR.dyckBits (K := Kfp) b) := by
    rcases mem_allPairs_of_ne _ hma hmb hne with hp | hp
    · exact PreSeedCensus.fieldNoun_eq_of_not_mem_pairBadSeeds hgood hp hla hlb henc
    · exact (PreSeedCensus.fieldNoun_eq_of_not_mem_pairBadSeeds hgood hp hlb hla henc.symm).symm
  exact hne (PreSeedCensus.noun_eq_of_fieldNoun_eq (K := Kfp)
    (fun k hk => hchar ▸ hqa k hk) (fun k hk => hchar ▸ hqb k hk) hfield)

end Census

/-! ## 3. The census as a `BadSummand` over the tower seed `(z₁, z₂)` -/

section Summand
open SVFrame T0Tower
open scoped Classical

variable {q : ℕ} {K : Type} [Field K] [Fintype K] [DecidableEq K] (δ : K) [Fact (¬ IsSquare δ)]

/-- The tower seed of a pair-coin assignment. -/
noncomputable def pairSeed {n : ℕ} (i j : Fin n) (f : ({i, j} : Finset (Fin n)) → K) : Quad δ :=
  Quad.mk δ (f ⟨i, by simp⟩) (f ⟨j, by simp⟩)

theorem pairSeed_injective {n : ℕ} (i j : Fin n) : Function.Injective (pairSeed δ (K := K) i j) := by
  intro f f' h
  obtain ⟨h1, h2⟩ := (Quad.mk_eq_mk_iff δ _ _ _ _).mp h
  funext x
  obtain ⟨x, hx⟩ := x
  rcases Finset.mem_insert.mp hx with rfl | hx'
  · exact h1
  · rw [Finset.mem_singleton] at hx'; subst hx'; exact h2

/-- The census bad set on the pair coins: the tower seed is a table bad seed. -/
noncomputable def censusBadSet {n : ℕ} (i j : Fin n) (Λ : ℕ) (rows : List (CellRowB0 q))
    (skel : List Noun) : Finset (({i, j} : Finset (Fin n)) → K) :=
  Finset.univ.filter fun f => pairSeed δ i j f ∈ tableBadSeeds (Kfp := Quad δ) Λ rows skel

theorem censusBadSet_card_le {n : ℕ} (i j : Fin n) (Λ : ℕ) (rows : List (CellRowB0 q))
    (skel : List Noun) :
    (censusBadSet δ i j Λ rows skel).card ≤ pairCount (rows.length + skel.length) * (2 * Λ - 1) := by
  refine le_trans ?_ (tableBadSeeds_card_le (Kfp := Quad δ) Λ rows skel)
  refine Finset.card_le_card_of_injOn (pairSeed δ i j) ?_ ?_
  · intro f hf
    simp only [censusBadSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf
    exact hf
  · intro f _ f' _ h
    exact pairSeed_injective δ i j h

/-- **T2 as a summand**: the table all-pairs census over two coins `i ≠ j` of any frame, priced
`pairCount (D + Ksk) · (2Λ − 1)` over `|𝕂|²`, reading no coin (`dep = ∅`) along any strategy whose
round-0 table and skeleton are coin-independent (`hconst`, the B0 staging). -/
noncomputable def tableCensusSummand (Φ : CoinFrame) (i j : Fin Φ.n)
    {Tr : Type} (Staged : (Coins Φ K → Tr) → Prop)
    (rowsOf : Tr → List (CellRowB0 q)) (skelOf : Tr → List Noun) (D Ksk Λ : ℕ)
    (hD : ∀ tr, (rowsOf tr).length ≤ D) (hsk : ∀ tr, (skelOf tr).length ≤ Ksk)
    (hconst : ∀ Q, Staged Q → ∀ χ χ', rowsOf (Q χ) = rowsOf (Q χ') ∧ skelOf (Q χ) = skelOf (Q χ')) :
    BadSummand Φ K Tr Staged where
  coins := {i, j}
  dep := ∅
  disj := Finset.disjoint_empty_right _
  badSet tr _ := censusBadSet δ i j Λ (rowsOf tr) (skelOf tr)
  weight := pairCount (D + Ksk) * (2 * Λ - 1)
  card_le tr _ := (censusBadSet_card_le δ i j Λ _ _).trans
    (Nat.mul_le_mul_right _ (pairCount_mono (Nat.add_le_add (hD tr) (hsk tr))))
  readsOn Q hQ χ χ' _ := by
    obtain ⟨h1, h2⟩ := hconst Q hQ χ χ'
    show censusBadSet δ i j Λ (rowsOf (Q χ)) (skelOf (Q χ)) =
      censusBadSet δ i j Λ (rowsOf (Q χ')) (skelOf (Q χ'))
    rw [h1, h2]

theorem tableCensusSummand_coins_card (Φ : CoinFrame) (i j : Fin Φ.n) (hij : i ≠ j)
    {Tr : Type} (Staged : (Coins Φ K → Tr) → Prop)
    (rowsOf : Tr → List (CellRowB0 q)) (skelOf : Tr → List Noun) (D Ksk Λ : ℕ) (hD hsk hconst) :
    (tableCensusSummand δ Φ i j Staged rowsOf skelOf D Ksk Λ hD hsk hconst).coins.card = 2 :=
  Finset.card_pair hij


theorem tableCensusSummand_weight_le (Φ : CoinFrame) (i j : Fin Φ.n)
    {Tr : Type} (Staged : (Coins Φ K → Tr) → Prop)
    (rowsOf : Tr → List (CellRowB0 q)) (skelOf : Tr → List Noun) (D Ksk Λ : ℕ) (hD hsk hconst) :
    (tableCensusSummand δ Φ i j Staged rowsOf skelOf D Ksk Λ hD hsk hconst).weight ≤
      ((D + Ksk) ^ 2 / 2) * (2 * Λ - 1) :=
  Nat.mul_le_mul_right _ (pairCount_le_sq_div_two _)

/-- Membership in the summand's event is membership of the tower seed in the table bad seeds. -/
theorem tableCensusSummand_mem_iff (Φ : CoinFrame) (i j : Fin Φ.n)
    {Tr : Type} (Staged : (Coins Φ K → Tr) → Prop)
    (rowsOf : Tr → List (CellRowB0 q)) (skelOf : Tr → List Noun) (D Ksk Λ : ℕ) (hD hsk hconst)
    (tr : Tr) (χ : Coins Φ K) :
    (tableCensusSummand δ Φ i j Staged rowsOf skelOf D Ksk Λ hD hsk hconst).mem tr χ ↔
      Quad.mk δ (χ i) (χ j) ∈ tableBadSeeds (Kfp := Quad δ) Λ (rowsOf tr) (skelOf tr) := by
  show (fun k : ({i, j} : Finset (Fin Φ.n)) => χ k) ∈ censusBadSet δ i j Λ (rowsOf tr) (skelOf tr) ↔ _
  unfold censusBadSet
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **`vclCensusSummand`**: T2 at `frameVCL` (`z₁, z₂` = coins `2, 3`), `Λ_chip = 2^110`, the
skeleton majorant `3 + 19N`. -/
noncomputable def vclCensusSummand {Tr : Type} (Staged : (Coins frameVCL K → Tr) → Prop)
    (rowsOf : Tr → List (CellRowB0 q)) (skelOf : Tr → List Noun) (D N : ℕ)
    (hD : ∀ tr, (rowsOf tr).length ≤ D) (hsk : ∀ tr, (skelOf tr).length ≤ 3 + 19 * N)
    (hconst : ∀ Q, Staged Q → ∀ χ χ', rowsOf (Q χ) = rowsOf (Q χ') ∧ skelOf (Q χ) = skelOf (Q χ')) :
    BadSummand frameVCL K Tr Staged :=
  tableCensusSummand δ frameVCL ⟨2, by decide⟩ ⟨3, by decide⟩ Staged rowsOf skelOf D (3 + 19 * N)
    fuelChip hD hsk hconst

theorem vclCensusSummand_shape {Tr : Type} (Staged : (Coins frameVCL K → Tr) → Prop)
    (rowsOf : Tr → List (CellRowB0 q)) (skelOf : Tr → List Noun) (D N : ℕ) (hD hsk hconst) :
    (vclCensusSummand δ Staged rowsOf skelOf D N hD hsk hconst).coins.card = 2 ∧
    (vclCensusSummand δ Staged rowsOf skelOf D N hD hsk hconst).dep = ∅ ∧
    (vclCensusSummand δ Staged rowsOf skelOf D N hD hsk hconst).weight ≤
      ((D + 3 + 19 * N) ^ 2 / 2) * (2 * 2 ^ 110 - 1) := by
  refine ⟨tableCensusSummand_coins_card δ _ _ _ (by decide) _ _ _ _ _ _ _ _ _, rfl, ?_⟩
  have := tableCensusSummand_weight_le δ frameVCL ⟨2, by decide⟩ ⟨3, by decide⟩ Staged rowsOf skelOf
    D (3 + 19 * N) fuelChip hD hsk hconst
  simpa [vclCensusSummand, fuelChip, Nat.add_assoc] using this

end Summand

end Nock.NockVMROM.Thm54.VclL
