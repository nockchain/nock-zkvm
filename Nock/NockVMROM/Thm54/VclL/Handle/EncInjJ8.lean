/-
  Nock/NockVMROM/Thm54/VclL/Handle/EncInjJ8.lean

  `WalkKJ8.EncInj2 E t ext` (injectivity of the encoder on the decoded cells of the two-provider table and
  its atom children, `InS2`) is the named hypothesis of `chain_sound2` / `walkJ8_records_genuineK`.

  * §1 the census noun list **`censusList2 rows ext`** = `decodedNouns2 rows ext ++ kidAtomList rows ext`
    (round-0 data: the cell table's B0 rows and the atom table's denotation `ext`); `inS2_mem` (`InS2 ⊆` it),
    `censusList2_length_le` (`≤ 3·|rows|`).
  * §1 the readout **`censusPairs S`**: for every unordered pair `(a, b)` of `allPairs S`, TWO pairs —
    the leaf lists `(a.leafList, b.leafList)` and the Dyck words as `0/1` atom lists, right-padded with `0`
    to a common length (`dyckPad`).  `censusPairs_length : = 2 · pairCount |S|`.
  * §2 the coordinates of `encZY`: **`encZY_leaf`** (`leaf = leafSum y z leafList`, `size = z^leaves`),
    **`encZY_dyck`** (at `z ≠ 0`, `dyck = leafSum y z (dyckPad …)` for any padding).
  * §3 the padding is faithful: `dyckWord_eq_of_pad` (equal padded words ⇒ equal Dyck words, via
    `#true = #false` in a Dyck encoding).
  * §4 **`encZY_inj_of_sep`** — the core: at `z ≠ 0`, if every admissible census pair of `S` separates at
    `(z, y)` (`leafSum` differs) and `S`'s nouns have `≤ Λ` leaves with `2Λ ≤ k`, atoms `≤ M` limbs, then
    `encZY z y` is injective on `S` (Dyck pair ⇒ same shape; leaf pair ⇒ same leaves;
    `Noun.noun_dyck_leaf_injective`).
  * §5 the table: `decoded2_leaves_le` (decoded nouns have `≤ fuelChip` leaves, `decodeTree_sound`),
    `decodeTree2_atoms` (their atoms are inline `< q` or atoms of `ext`), **`encInj2_of_sep`**.

  * §6 `encInj2_of_outside`: the same, with the separation read off the census sum of `DataJ8`.
  * §7 the figure at the census corner `cornerC`.  The Dyck pairs have length `2λ − 2`, so the readout
    needs `r.leaves ≥ 2·fuelChip` (the corner `corner31` has `leaves = fuelChip`), and it has
    `2·pairCount(3D) < 2^66` pairs (`corner31` has `P ≤ 2^31`).  The bound `< 2^-155` holds at
    `leaves ≤ 2·fuelChip`, `P ≤ 2^66` (`numJ8_census`, by `decide +kernel`; `figJ8_155_census`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8
import Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8
open Nock.ComputeTable (FP)
open Nock.Atoms (leafVal leafVal_small leafSum lenL)

noncomputable section

/-! ## 1. The census nouns and the census-pair readout -/

section Readout
variable {q : ℕ}

/-- The atom children of the B0 rows, one per side: an inline atom `(aS s).val`, or the external atom
`ext (idS s)` of a weighted rank-`(0, 0)` child. -/
def kidOf (ext : ℕ → Option Noun) (c : CellRowB0 q) (s : Side) : Option Noun :=
  if c.wS s = false then some (.atom (c.aS s).val)
  else if c.hiS s = 0 ∧ c.loS s = 0 then ext (c.idS s) else none

def kidAtomList (t : List (CellRowB0 q)) (ext : ℕ → Option Noun) : List Noun :=
  t.flatMap fun c => [Side.L, Side.R].filterMap (kidOf ext c)

theorem kidAtomList_length_le (t : List (CellRowB0 q)) (ext : ℕ → Option Noun) :
    (kidAtomList t ext).length ≤ 2 * t.length := by
  induction t with
  | nil => simp [kidAtomList]
  | cons c t ih =>
    simp only [kidAtomList, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have : ([Side.L, Side.R].filterMap (kidOf ext c)).length ≤ 2 :=
      (List.length_filterMap_le _ _).trans (by simp)
    omega

/-- **The census noun list** (round-0 data): the decoded cells, then the atom children. -/
def censusList2 (t : List (CellRowB0 q)) (ext : ℕ → Option Noun) : List Noun :=
  decodedNouns2 t ext ++ kidAtomList t ext

theorem decodedNouns2_length_le (t : List (CellRowB0 q)) (ext : ℕ → Option Noun) :
    (decodedNouns2 t ext).length ≤ t.length := by
  unfold decodedNouns2
  exact (List.length_filterMap_le _ _).trans (by simp)

theorem censusList2_length_le (t : List (CellRowB0 q)) (ext : ℕ → Option Noun) :
    (censusList2 t ext).length ≤ 3 * t.length := by
  unfold censusList2
  rw [List.length_append]
  have := decodedNouns2_length_le t ext
  have := kidAtomList_length_le t ext
  omega

variable {Kfp : Type} [Field Kfp] [Fintype Kfp] [DecidableEq Kfp] [Algebra (ZMod q) Kfp]

/-- `InS2` is membership in the census noun list. -/
theorem inS2_mem {t : List (CellRow q Kfp)} {ext : ℕ → Option Noun} {n : Noun} (h : InS2 t ext n) :
    n ∈ censusList2 (t.map (·.b0)) ext := by
  rcases h with h | ⟨c, hc, s, h⟩
  · exact List.mem_append_left _ h
  · refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨c.b0, List.mem_map_of_mem hc, ?_⟩)
    refine List.mem_filterMap.mpr ⟨s, by cases s <;> simp, ?_⟩
    rcases h with ⟨hw, rfl⟩ | ⟨hw, hhi, hlo, hx⟩
    · simp [kidOf, hw]
    · simp [kidOf, hw, hhi, hlo, hx]

end Readout

/-- A Dyck word as `0/1` atoms, right-padded with `0` (`false`) to length `m`. -/
def dyckPad (m : ℕ) (n : Noun) : List ℕ :=
  (n.dyckWord ++ List.replicate (m - n.dyckWord.length) false).map fun b => if b then 1 else 0

/-- The two census pairs of a noun pair: leaf lists, and the Dyck words padded to a common length. -/
def censusPairOf (a b : Noun) : List (List ℕ × List ℕ) :=
  [(a.leafList, b.leafList),
    (dyckPad (max a.dyckWord.length b.dyckWord.length) a, dyckPad (max a.dyckWord.length b.dyckWord.length) b)]

def censusPairs (S : List Noun) : List (List ℕ × List ℕ) :=
  (allPairs S).flatMap fun pr => censusPairOf pr.1 pr.2

theorem censusPairs_length (S : List Noun) : (censusPairs S).length = 2 * pairCount S.length := by
  unfold censusPairs
  rw [← allPairs_length]
  induction allPairs S with
  | nil => simp
  | cons pr l ih => simp [censusPairOf, ih]; ring

theorem censusPairOf_sub {S : List Noun} {a b : Noun} (h : (a, b) ∈ allPairs S) :
    ∀ pr ∈ censusPairOf a b, pr ∈ censusPairs S :=
  fun pr hpr => List.mem_flatMap.mpr ⟨(a, b), h, hpr⟩

/-! ## 2. The coordinates of `encZY` -/

section Coords
variable {Kfp : Type} [Field Kfp] [Algebra Nock.Atoms.Fp Kfp] [Fintype Kfp] [DecidableEq Kfp]

theorem leafSum_append (y z : Kfp) (l₁ l₂ : List ℕ) :
    leafSum y z (l₁ ++ l₂) = leafSum y z l₁ + z ^ l₁.length * leafSum y z l₂ := by
  induction l₁ with
  | nil => simp [leafSum]
  | cons n l ih => simp only [List.cons_append, leafSum, ih, List.length_cons, pow_succ]; ring

/-- **The leaf and size coordinates**: `leaf = Σ leafVal y nᵢ · zⁱ`, `size = z^λ` (every `z`). -/
theorem encZY_leaf (z y : Kfp) (n : Noun) :
    (encZY z y n).leaf = leafSum y z n.leafList ∧ (encZY z y n).size = z ^ n.leaves := by
  induction n with
  | atom k => simp [encZY, leafSum, Noun.leafList, Noun.leaves]
  | cell a b iha ihb =>
    refine ⟨?_, ?_⟩
    · simp only [encZY_cell, FP.cons, Noun.leafList, leafSum_append, iha.1, iha.2, ihb.1,
        Noun.leafList_length]
    · simp only [encZY_cell, FP.cons, iha.2, ihb.2, Noun.leaves, pow_add]

/-- The size and Dyck coordinates of `encZY` are `enc z`'s (they never read the leaves). -/
theorem encZY_size_dyck {z : Kfp} (hz : z ≠ 0) (y : Kfp) (n : Noun) :
    (encZY z y n).size = (GlobalCarryRecognizer.enc z n).size ∧
      (encZY z y n).dyck = (GlobalCarryRecognizer.enc z n).dyck := by
  induction n with
  | atom k => simp [encZY, GlobalCarryRecognizer.enc_atom]
  | cell a b iha ihb =>
    rw [encZY_cell, GlobalCarryRecognizer.enc_cons hz]
    simp only [FP.cons, iha.1, iha.2, ihb.1, ihb.2, and_self]

theorem leafVal_bit (y : Kfp) (b : Bool) :
    leafVal y (if b then 1 else 0) = if b then (1 : Kfp) else 0 := by
  have h1 : (1 : ℕ) < Nock.Atoms.p := by norm_num [Nock.Atoms.p, Nock.Field.p]
  have h0 : (0 : ℕ) < Nock.Atoms.p := by norm_num [Nock.Atoms.p, Nock.Field.p]
  cases b
  · simp [leafVal_small y h0]
  · simp [leafVal_small y h1]

theorem leafSum_bits (y z : Kfp) (w : List Bool) :
    leafSum y z (w.map fun b => if b then 1 else 0) =
      (NPR.listPoly (w.map fun b => if b then (1 : Kfp) else 0)).eval z := by
  induction w with
  | nil => simp [leafSum]
  | cons b w ih =>
    simp only [List.map_cons, leafSum, ih, NPR.listPoly_cons, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, leafVal_bit]

theorem leafSum_replicate_zero (y z : Kfp) (k : ℕ) :
    leafSum y z ((List.replicate k false).map fun b => if b then 1 else 0) = 0 := by
  rw [leafSum_bits]
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.map_cons, NPR.listPoly_cons, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, ih, Bool.false_eq_true, if_false, Polynomial.eval_C]
    ring

/-- **The Dyck coordinate** (`z ≠ 0`): `dyck = leafSum y z (dyckPad m n)` for every padding `m`. -/
theorem encZY_dyck {z : Kfp} (hz : z ≠ 0) (y : Kfp) (m : ℕ) (n : Noun) :
    (encZY z y n).dyck = leafSum y z (dyckPad m n) := by
  rw [(encZY_size_dyck hz y n).2, GlobalCarryRecognizer.enc_dyck, dyckPad, List.map_append, leafSum_append,
    leafSum_replicate_zero, mul_zero, add_zero, leafSum_bits]
  rfl

end Coords

/-! ## 3. The padding is faithful -/

theorem count_true_add_false : ∀ w : List Bool, w.count true + w.count false = w.length
  | [] => rfl
  | b :: w => by
    have := count_true_add_false w
    cases b <;> simp [List.count_cons] <;> omega

theorem encode_count (t : Nock.BTree) : (Nock.BTree.encode t).count true = (Nock.BTree.encode t).count false := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
    simp only [Nock.BTree.encode, List.count_cons, List.count_append]
    simp
    omega

theorem dyckWord_len_count (n : Noun) : n.dyckWord.length = 2 * n.dyckWord.count true := by
  have h1 := count_true_add_false n.dyckWord
  have h2 := encode_count n.shape
  simp only [Noun.dyckWord] at h1 ⊢
  omega

theorem bit_injective : Function.Injective fun b : Bool => if b then (1 : ℕ) else 0 := by
  intro a b h; cases a <;> cases b <;> simp_all

/-- Equal padded Dyck words are equal Dyck words. -/
theorem dyckWord_eq_of_pad {m : ℕ} {a b : Noun} (h : dyckPad m a = dyckPad m b) : a.dyckWord = b.dyckWord := by
  unfold dyckPad at h
  have h' := (List.map_injective_iff.mpr bit_injective) h
  have hc := congrArg (List.count true) h'
  simp only [List.count_append, List.count_replicate] at hc
  simp at hc
  have hl : a.dyckWord.length = b.dyckWord.length := by
    rw [dyckWord_len_count a, dyckWord_len_count b, hc]
  exact List.append_inj_left h' hl

/-! ## 4. The core: separation of every census pair ⇒ `encZY` injective on the list -/

section Core
variable {Kfp : Type} [Field Kfp] [Algebra Nock.Atoms.Fp Kfp] [Fintype Kfp] [DecidableEq Kfp]

theorem lenL_bit (b : Bool) : lenL (if b then 1 else 0) = 1 := by
  have h1 : (1 : ℕ) < Nock.Atoms.p := by norm_num [Nock.Atoms.p, Nock.Field.p]
  have h0 : (0 : ℕ) < Nock.Atoms.p := by norm_num [Nock.Atoms.p, Nock.Field.p]
  cases b <;> simp [lenL, h0, h1]

def SepAt (y z : Kfp) (prs : List (List ℕ × List ℕ)) (k M : ℕ) : Prop :=
  ∀ pr ∈ prs, pr.1.length = pr.2.length → pr.1 ≠ pr.2 → pr.1.length ≤ k →
    (∀ a ∈ pr.1, lenL a ≤ M) → (∀ a ∈ pr.2, lenL a ≤ M) → leafSum y z pr.1 ≠ leafSum y z pr.2

/-- **One noun pair**: if both of its census pairs separate, equal `encZY` means equal nouns. -/
theorem pair_inj {z y : Kfp} (hz : z ≠ 0) {prs : List (List ℕ × List ℕ)} {k M Λ : ℕ}
    (hsep : SepAt y z prs k M) {a b : Noun} (hab : ∀ pr ∈ censusPairOf a b, pr ∈ prs)
    (ha : a.leaves ≤ Λ) (hb : b.leaves ≤ Λ) (hk : 2 * Λ ≤ k) (hM1 : 1 ≤ M)
    (haM : ∀ x ∈ a.leafList, lenL x ≤ M) (hbM : ∀ x ∈ b.leafList, lenL x ≤ M)
    (he : encZY z y a = encZY z y b) : a = b := by
  set m := max a.dyckWord.length b.dyckWord.length
  -- the Dyck pair
  have hdy : a.dyckWord = b.dyckWord := by
    by_contra hne
    have hpne : dyckPad m a ≠ dyckPad m b := fun h => hne (dyckWord_eq_of_pad h)
    have hlen : (dyckPad m a).length = (dyckPad m b).length := by
      simp only [dyckPad, List.length_map, List.length_append, List.length_replicate, m]; omega
    have hla := a.dyckWord_length
    have hlb := b.dyckWord_length
    have hlk : (dyckPad m a).length ≤ k := by
      simp only [dyckPad, List.length_map, List.length_append, List.length_replicate, m]; omega
    have hbits : ∀ n : Noun, ∀ x ∈ dyckPad m n, lenL x ≤ M := by
      intro n x hx
      simp only [dyckPad, List.mem_map] at hx
      obtain ⟨b', -, rfl⟩ := hx
      rw [lenL_bit]; exact hM1
    apply hsep (dyckPad m a, dyckPad m b) (hab _ (by simp [censusPairOf, m])) hlen hpne hlk (hbits a) (hbits b)
    rw [← encZY_dyck hz y m a, ← encZY_dyck hz y m b, he]
  -- same shape, hence same leaf count
  have hsh : a.shape = b.shape := Nock.BTree.encode_injective hdy
  have hlv : a.leaves = b.leaves := by
    have h1 := a.dyckWord_length
    have h2 := b.dyckWord_length
    rw [hdy] at h1; omega
  -- the leaf pair
  have hll : a.leafList = b.leafList := by
    by_contra hne
    have hl1 : a.leafList.length = b.leafList.length := by simp [hlv]
    have hl2 : a.leafList.length ≤ k := by simp; omega
    apply hsep (a.leafList, b.leafList) (hab _ (by simp [censusPairOf])) hl1 hne hl2 haM hbM
    rw [← (encZY_leaf z y a).1, ← (encZY_leaf z y b).1, he]
  exact Noun.noun_dyck_leaf_injective (Prod.ext hdy hll)

/-- **The core**: at `z ≠ 0`, if every admissible census pair of `S` separates at `(z, y)`, every noun of
`S` has `≤ Λ` leaves (`2Λ ≤ k`) and atoms of `≤ M` limbs, then `encZY z y` is injective on `S`. -/
theorem encZY_inj_of_sep {z y : Kfp} (hz : z ≠ 0) {S : List Noun} {prs : List (List ℕ × List ℕ)}
    {k M Λ : ℕ} (hsub : ∀ pr ∈ censusPairs S, pr ∈ prs) (hsep : SepAt y z prs k M)
    (hΛ : ∀ n ∈ S, n.leaves ≤ Λ) (hk : 2 * Λ ≤ k) (hM1 : 1 ≤ M)
    (hM : ∀ n ∈ S, ∀ x ∈ n.leafList, lenL x ≤ M) :
    ∀ a ∈ S, ∀ b ∈ S, encZY z y a = encZY z y b → a = b := by
  intro a ha b hb he
  by_contra hne
  rcases mem_allPairs_of_ne S ha hb hne with hp | hp
  · exact hne (pair_inj hz hsep (fun pr h => hsub _ (censusPairOf_sub hp pr h)) (hΛ a ha) (hΛ b hb) hk hM1
      (hM a ha) (hM b hb) he)
  · exact hne (pair_inj hz hsep (fun pr h => hsub _ (censusPairOf_sub hp pr h)) (hΛ b hb) (hΛ a ha) hk hM1
      (hM b hb) (hM a ha) he.symm).symm

end Core

/-! ## 5. The two-provider table -/

section Table
variable {q : ℕ}

/-- The child of a row under `leaf2`: an inline atom, an `ext` value, or a decoded serial. -/
theorem childT_leaf2 (t : List (CellRowB0 q)) (ext : ℕ → Option Noun) (f : ℕ) (c : CellRowB0 q) (s : Side)
    {n : Noun} (h : VclL.childT t (leaf2 q ext) f c s = some n) :
    n = .atom (c.aS s).val ∨ (∃ j, ext j = some n) ∨ decodeTree t (leaf2 q ext) f (c.idS s) = some n := by
  unfold VclL.childT leaf2 at h
  split_ifs at h with hw h0
  · exact Or.inr (Or.inl ⟨_, h⟩)
  · exact Or.inr (Or.inr h)
  · exact Or.inl (Option.some.inj h).symm

/-- The atoms of a decoded noun are inline atoms (`< q`) or atoms of an `ext` value. -/
theorem decodeTree2_atoms [NeZero q] (t : List (CellRowB0 q)) (ext : ℕ → Option Noun) :
    ∀ f i n, decodeTree t (leaf2 q ext) f i = some n →
      ∀ x ∈ n.leafList, x < q ∨ ∃ j m, ext j = some m ∧ x ∈ m.leafList
  | 0, _, _, h => by simp [decodeTree] at h
  | f + 1, i, n, h => by
    rw [decodeTree_succ] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨c, -, a, ha, b, hb, hn⟩ := h
    cases hn
    have side : ∀ s, ∀ m, VclL.childT t (leaf2 q ext) f c s = some m →
        ∀ x ∈ m.leafList, x < q ∨ ∃ j m', ext j = some m' ∧ x ∈ m'.leafList := by
      intro s m hm x hx
      rcases childT_leaf2 t ext f c s hm with rfl | ⟨j, hj⟩ | hd
      · simp only [Noun.leafList, List.mem_singleton] at hx
        exact Or.inl (hx ▸ ZMod.val_lt _)
      · exact Or.inr ⟨j, m, hj, hx⟩
      · exact decodeTree2_atoms t ext f _ m hd x hx
    intro x hx
    simp only [Noun.leafList, List.mem_append] at hx
    rcases hx with hx | hx
    · exact side .L a ha x hx
    · exact side .R b hb x hx

variable {Kfp : Type} [Field Kfp] [Fintype Kfp] [DecidableEq Kfp] [Algebra (ZMod q) Kfp] [Fact q.Prime]

/-- Decoded nouns of an accepted two-provider table have `≤ fuelChip` leaves (`decodeTree_sound`). -/
theorem decoded2_leaves_le (hq : 2 ^ 63 < q) {z : Kfp} {E : Noun → FP Kfp}
    (hcons : ∀ a b, E (.cell a b) = FP.cons z (E a) (E b)) (hE : InlineAtoms q z E)
    {t : List (CellRow q Kfp)} {vp : List (VKey Kfp)} {ext : ℕ → Option Noun}
    (h : TableAccepts2 z t vp) (hvp : AtomLeaves E vp ext) {n : Noun}
    (hn : n ∈ decodedNouns2 (t.map (·.b0)) ext) : n.leaves ≤ fuelChip := by
  unfold decodedNouns2 at hn
  obtain ⟨i, hi, hd⟩ := List.mem_filterMap.mp hn
  rw [List.mem_range, List.length_map] at hi
  have hc : t[i] ∈ t := List.getElem_mem hi
  have hidx : t[i].b0.idx = i := by
    have h1 := congrArg (fun l => l[i]?) h.serial
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some] at h1
    rw [List.getElem?_range (by simpa using hi)] at h1
    exact Option.some.inj h1
  have hT := treeOK_leaf2 hq hE h hvp
  have hlt := rowOK_mu_lt (h.rows _ hc)
  obtain ⟨L, R, hdec, -, -, -, -, -, hlv⟩ := decodeTree_sound hq hcons hT _ t[i] hc rfl fuelChip hlt
  unfold preZNounOfTable2 at hd
  rw [hidx, hd, Option.some.injEq] at hdec
  rw [hdec, hlv]
  exact hlt

/-- **`EncInj2 (encZY z y)` from the census separation** (the table form of §4). -/
theorem encInj2_of_sep [Algebra Nock.Atoms.Fp Kfp] (hq : 2 ^ 63 < q) {z y : Kfp} (hz : z ≠ 0)
    (hE : InlineAtoms q z (encZY z y)) {t : List (CellRow q Kfp)} {vp : List (VKey Kfp)}
    {ext : ℕ → Option Noun} (h : TableAccepts2 z t vp) (hvp : AtomLeaves (encZY z y) vp ext)
    {k M : ℕ} (hext : ∀ j m, ext j = some m → ∃ v, m = .atom v ∧ lenL v ≤ M)
    (hqM : ∀ x < q, lenL x ≤ M) (hk : 2 * fuelChip ≤ k) {prs : List (List ℕ × List ℕ)}
    (hsub : ∀ pr ∈ censusPairs (censusList2 (t.map (·.b0)) ext), pr ∈ prs) (hsep : SepAt y z prs k M) :
    EncInj2 (encZY z y) t ext := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hM1 : 1 ≤ M := (Nock.Atoms.one_le_lenL 0).trans (hqM 0 (by have := (Fact.out : q.Prime).pos; omega))
  have hextM : ∀ j m, ext j = some m → ∀ x ∈ m.leafList, lenL x ≤ M := by
    intro j m hj x hx
    obtain ⟨v, rfl, hv⟩ := hext j m hj
    simp only [Noun.leafList, List.mem_singleton] at hx
    exact hx ▸ hv
  have hS : ∀ n ∈ censusList2 (t.map (·.b0)) ext,
      n.leaves ≤ fuelChip ∧ ∀ x ∈ n.leafList, lenL x ≤ M := by
    intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · refine ⟨decoded2_leaves_le hq (encZY_cell z y) hE h hvp hn, ?_⟩
      obtain ⟨i, -, hd⟩ := List.mem_filterMap.mp hn
      intro x hx
      rcases decodeTree2_atoms _ ext _ _ _ hd x hx with hx | ⟨j, m, hj, hxm⟩
      · exact hqM x hx
      · exact hextM j m hj x hxm
    · obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp hn
      obtain ⟨s, -, hs⟩ := List.mem_filterMap.mp hc
      unfold kidOf at hs
      split_ifs at hs with hw h0
      · cases hs
        refine ⟨by simp [Noun.leaves, fuelChip], ?_⟩
        intro x hx
        simp only [Noun.leafList, List.mem_singleton] at hx
        exact hx ▸ hqM _ (ZMod.val_lt _)
      · obtain ⟨v, rfl, hv⟩ := hext _ n hs
        refine ⟨by simp [Noun.leaves, fuelChip], ?_⟩
        intro x hx
        simp only [Noun.leafList, List.mem_singleton] at hx
        exact hx ▸ hv
  have hinj := encZY_inj_of_sep hz hsub hsep (fun n hn => (hS n hn).1) hk hM1 (fun n hn => (hS n hn).2)
  intro a ha b hb he
  exact hinj a (inS2_mem ha) b (inS2_mem hb) he

end Table

/-! ## 6. `EncInj2` outside the census-sum event -/

section Outside
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`EncInj2 (encZY z y)` outside the bivariate census event**: if no census sum `s` of `sumJ8 R.bivariateCensus`
holds at `(tr, χ)`, then `encZY` at the coin point `z = (χ c2, χ c3)`, `y = (χ cY1, χ cY2)` is injective on the decoded
cells and atom children of the table.  Inputs: the accepted two-provider table, atom-root external keys, `ext` atoms
of `≤ maxlen` limbs, inline atoms of `≤ maxlen` limbs, `2·fuelChip ≤ r.leaves`, and the census pairs contained in
`R.prs tr`. -/
theorem encInj2_of_outside (R : DataJ8 (q := q) (algebraMap (ZMod p) K δ) Tr St r P) {tr : Tr}
    {χ : Coins frameJ8 K} (h : ∀ s ∈ sumJ8 R .bivariateCensus, ¬ s.mem tr χ)
    {qc : ℕ} [Fact qc.Prime] [Algebra (ZMod qc) 𝕂′] (hq : 2 ^ 63 < qc)
    (hz : Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) ≠ 0)
    (hE : InlineAtoms qc (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3))
      (encZY (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))))
    {t : List (CellRow qc 𝕂′)} {vp : List (VKey 𝕂′)} {ext : ℕ → Option Noun}
    (htab : TableAccepts2 (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) t vp)
    (hvp : AtomLeaves (encZY (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3))
      (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))) vp ext)
    (hext : ∀ j m, ext j = some m → ∃ v, m = .atom v ∧ lenL v ≤ r.maxlen)
    (hqM : ∀ x < qc, lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hprs : ∀ pr ∈ censusPairs (censusList2 (t.map (·.b0)) ext), pr ∈ R.prs tr) :
    EncInj2 (encZY (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3))
      (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))) t ext :=
  encInj2_of_sep hq hz hE htab hvp hext hqM hk hprs
    (fun _pr hpr hlen hne hkk hM1 hM2 => biv_out_of_outside R h hpr hlen hne hkk hM1 hM2)

end Outside

/-! ## 7. The figure at the census corner -/

/-- **The census corner**: `corner31` with `leaves = 2·fuelChip` (the Dyck pairs). -/
def cornerC : RowsJ8 := { corner31 with leaves := 2 * fuelChip }

theorem numJ8_census (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    numJ8 c cornerC (2 ^ 66) * 2 ^ 155 < c ^ 4 := by
  subst hc; unfold numJ8 numHQ cornerC corner31 fuelChip pairCount ioFailureUnionBound; decide +kernel

/-- **`< 2^-155` at the census readout's parameters**: every row count `≤ 2^31`, `leaves ≤ 2·fuelChip`,
`P ≤ 2^66` census pairs (`2·pairCount(3·2^31) < 2^66`). -/
theorem figJ8_155_census (r : RowsJ8) (P : ℕ) (h : RowsLe r cornerC) (hP : P ≤ 2 ^ 66) :
    boundJ8P cK (cK ^ 2) r P < 1 / (2 : ℚ) ^ 155 :=
  boundJ8P_lt_of_num (lt_of_le_of_lt (Nat.mul_le_mul_right _ (numJ8_corner h hP)) (numJ8_census cK cK_eq))

/-- The census readout's pair count at `≤ 2^31` cell rows fits `2^66`. -/
theorem censusPairs_length_le {q : ℕ} (t : List (CellRowB0 q)) (ext : ℕ → Option Noun) (ht : t.length ≤ 2 ^ 31) :
    (censusPairs (censusList2 t ext)).length ≤ 2 ^ 66 := by
  rw [censusPairs_length]
  have h1 := censusList2_length_le t ext
  have h2 : pairCount (censusList2 t ext).length ≤ pairCount (3 * 2 ^ 31) := pairCount_mono (by omega)
  have h3 : pairCount (3 * 2 ^ 31) ≤ 2 ^ 65 := by unfold pairCount; norm_num
  omega

end

end Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8
