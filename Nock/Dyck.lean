/-
  Nock/Dyck.lean

  Dyck words and their bijection with proper binary trees.

  The paper defines the Dyck language by the context-free grammar
      L_dk = { w ∈ {0,1}* | w = ε  or  ∃ w₁,w₂ ∈ L_dk. w = 0 w₁ 1 w₂ },
  and `Lem:optimal_dyck` asserts the structural equivalence
      L_dk ≡ L_full_BT              (Dyck words ↔ proper binary trees)
      L^{2λ}_dk ≡ L^{2λ+1}_full_BT  (length-graded version)
  and the cardinality `|L^{2λ}_dk| = C_λ` (the λ-th Catalan number).

  This file formalizes the **structure**: the Dyck language as an inductive predicate on
  `List Bool` (mirroring the grammar with `0 = false`, `1 = true`), the proper-binary-tree
  *shape* `BTree` (the paper's `L_full_BT`, data-free — the paper separates a noun `(t,dt)`
  into a Dyck word `t` and a leaf array `dt`,, the encoding
  `BTree → List Bool`, and the bijection

      `encode` is injective and its image is exactly the Dyck language

  i.e. `BTree ≃ { w // Dyck w }`, which is `L_dk ≡ L_full_BT` verbatim.  The length-graded
  correspondence `L^{2λ}_dk ≡ L^{2λ+1}_full_BT` is `dyck_length_graded`.

  CATALAN CARDINALITY:  `|L^{2λ}_dk| = C_λ`, the λ-th Catalan number, is now
  proved (§ "Catalan cardinality" at the end) via a bijection `BTree ≃ Mathlib.BinaryTree Unit`
  and Mathlib's `BinaryTree.treesOfNumNodesEq_card_eq_catalan`.
-/

import Nock.Tree
import Mathlib.Combinatorics.Enumerative.Catalan.Tree

namespace Nock

/-! ### The Dyck language -/

--(`L_dk = { w | w = ε ∨ ∃ w₁ w₂ ∈ L_dk. w = 0 w₁ 1 w₂ }`, with 0=false,1=true)
/-- The **Dyck language** as an inductive predicate on bit strings (`0 = false` = "open",
    `1 = true` = "close").  `eps` is `w = ε`; `cat` is `w = 0 w₁ 1 w₂` for `w₁,w₂ ∈ L_dk`. -/
inductive Dyck : List Bool → Prop
  | eps : Dyck []
  | cat {w₁ w₂ : List Bool} : Dyck w₁ → Dyck w₂ → Dyck (false :: w₁ ++ true :: w₂)

/-! ### Proper binary tree shapes = `L_full_BT`data-free) -/

--(`L_full_BT`: proper/full binary trees — here the data-free *shape*)
/-- A proper binary tree **shape**: the paper's `L_full_BT`, i.e. a `Noun`
    with the leaf data erased.  Every node has zero (`leaf`) or two (`node`) children. -/
inductive BTree where
  | leaf : BTree
  | node : BTree → BTree → BTree
deriving Repr, DecidableEq, Inhabited

namespace BTree

/-- Total node count of a shape (matches `Noun.size`). -/
def size : BTree → Nat
  | .leaf     => 1
  | .node l r => 1 + l.size + r.size

/-- The Dyck encoding of a proper binary tree: `leaf ↦ ε`,
    `node l r ↦ 0 · encode l · 1 · encode r`. -/
def encode : BTree → List Bool
  | .leaf     => []
  | .node l r => false :: encode l ++ true :: encode r

/-- A Dyck word encoding a tree has length `size − 1` (each internal node contributes the
    pair `0…1`).  Stated additively to avoid truncated subtraction. -/
theorem encode_length_add_one (t : BTree) : (encode t).length + 1 = t.size := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
      simp only [encode, size, List.length_cons, List.length_append]
      omega

/-! ### `encode` lands in the Dyck language, and is onto it -/

--(⇐ direction of `L_dk ≡ L_full_BT`: every tree's encoding is Dyck)
/-- Every tree encodes to a Dyck word. -/
theorem dyck_encode (t : BTree) : Dyck (encode t) := by
  induction t with
  | leaf => exact Dyck.eps
  | node l r ihl ihr => exact Dyck.cat ihl ihr

--(⇒ direction of `L_dk ≡ L_full_BT`: every Dyck word is some tree's encoding)
/-- Every Dyck word is the encoding of some tree (surjectivity of `encode` onto `L_dk`). -/
theorem exists_encode_of_dyck {w : List Bool} (h : Dyck w) : ∃ t : BTree, encode t = w := by
  induction h with
  | eps => exact ⟨.leaf, rfl⟩
  | @cat w₁ w₂ _ _ ih₁ ih₂ =>
      obtain ⟨t₁, ht₁⟩ := ih₁
      obtain ⟨t₂, ht₂⟩ := ih₂
      exact ⟨.node t₁ t₂, by simp only [encode, ht₁, ht₂]⟩

/-! ### A greedy parser, to pin down injectivity of `encode`

    `decode fuel w` parses exactly one tree off the front of `w`, returning the tree and the
    unconsumed suffix.  A leading `0` (`false`) starts a `node`; anything else (a leading `1`
    or the empty word) is a `leaf` consuming nothing.  This is the algorithmic inverse of
    `encode`; `decode_encode` proves the round-trip, which yields injectivity. -/
def decode : Nat → List Bool → Option (BTree × List Bool)
  | 0,         _                => none
  | fuel + 1, (false :: rest) =>
      match decode fuel rest with
      | some (l, true :: rest₁) =>
          match decode fuel rest₁ with
          | some (r, rest₂) => some (.node l r, rest₂)
          | none            => none
      | _ => none
  | _ + 1,     rest            => some (.leaf, rest)   -- leading `1`, or `[]`

end BTree
end Nock

namespace Nock
namespace BTree

/-! ### Round-trip: `decode` inverts `encode`, hence `encode` is injective -/

/-- The greedy parser recovers the encoded tree and returns the untouched suffix, provided
    the fuel covers the tree's size and the suffix is not "open"-led (which is exactly the
    invariant maintained by the recursion: a left subtree is followed by its closing `1`, a
    right subtree by the parent's suffix). -/
theorem decode_encode :
    ∀ (t : BTree) (fuel : Nat) (rest : List Bool),
      t.size ≤ fuel → (rest = [] ∨ rest.head? = some true) →
      decode fuel (encode t ++ rest) = some (t, rest) := by
  intro t
  induction t with
  | leaf =>
      intro fuel rest _ hrest
      cases fuel with
      | zero => simp [size] at *
      | succ f =>
          simp only [encode, List.nil_append]
          rcases hrest with h | h
          · subst h; rfl
          · cases rest with
            | nil => rfl
            | cons b rs =>
                simp only [List.head?_cons, Option.some.injEq] at h
                subst h; rfl
  | node l r ihl ihr =>
      intro fuel rest hsize hrest
      cases fuel with
      | zero => simp [size] at hsize
      | succ f =>
          -- fuel = f+1, f ≥ size l + size r ≥ size l, size r
          simp only [size] at hsize
          have hfl : l.size ≤ f := by omega
          have hfr : r.size ≤ f := by omega
          -- left subtree: continuation starts with `true`
          have hL := ihl f (true :: (encode r ++ rest)) hfl (Or.inr rfl)
          -- right subtree: continuation is the (open-free) `rest`
          have hR := ihr f rest hfr hrest
          simp only [encode, List.cons_append, List.append_assoc, decode, hL, hR]

/-- `encode` is injective: distinct shapes have distinct Dyck words. -/
theorem encode_injective {t₁ t₂ : BTree} (h : encode t₁ = encode t₂) : t₁ = t₂ := by
  have hlen : t₁.size = t₂.size := by
    have e₁ := encode_length_add_one t₁
    have e₂ := encode_length_add_one t₂
    rw [h] at e₁; omega
  have d₁ : decode t₁.size (encode t₁ ++ []) = some (t₁, []) :=
    decode_encode t₁ t₁.size [] (Nat.le_refl _) (Or.inl rfl)
  have d₂ : decode t₁.size (encode t₂ ++ []) = some (t₂, []) :=
    decode_encode t₂ t₁.size [] (by omega) (Or.inl rfl)
  rw [h] at d₁
  have := d₁.symm.trans d₂
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this.1

/-! ### `Lem:optimal_dyck` — the structural bijection -/

--(`L_dk ≡ L_full_BT`: the image of `encode` is exactly the Dyck language)
/-- **`L_dk ≡ L_full_BT`.**  A bit string is a Dyck word iff it is the
    encoding of some proper binary tree.  Together with `encode_injective`, this says
    `encode: BTree → { w // Dyck w }` is a bijection. -/
theorem dyck_iff_encode {w : List Bool} : Dyck w ↔ ∃ t : BTree, encode t = w :=
  ⟨exists_encode_of_dyck, fun ⟨t, ht⟩ => ht ▸ dyck_encode t⟩

--(`L^{2λ}_dk ≡ L^{2λ+1}_full_BT`: the length-graded bijection)
/-- **`L^{2λ}_dk ≡ L^{2λ+1}_full_BT`.**  Under the bijection, a Dyck word of
    length `2λ` corresponds exactly to a proper binary tree of size `2λ + 1`.  (The `encode`
    length identity `|encode t| + 1 = size t` graded at `2λ`.) -/
theorem dyck_length_graded {w : List Bool} (t : BTree) (ht : encode t = w) (lam : Nat) :
    w.length = 2 * lam ↔ t.size = 2 * lam + 1 := by
  have := encode_length_add_one t
  rw [ht] at this
  omega

end BTree

/-! ### Connection to `Noun`: a noun is a shape (`BTree`) plus leaf data -/

namespace Noun

--(a noun `n = (t, dt)` = a Dyck word/tree shape `t` + leaf array `dt`)
/-- The **shape** of a noun: erase the leaf data, leaving a proper binary tree (`L_full_BT`).
    The paper's noun `(t, dt)` pairs this shape (encoded as the Dyck word `t`) with the leaf
    array `dt`; the Dyck bijection above governs the `t` component. -/
def shape : Noun → Nock.BTree
  | .atom _   => .leaf
  | .cell l r => .node l.shape r.shape

/-- The shape preserves leaf and node counts (`Noun.size = BTree.size ∘ shape`). -/
theorem shape_size (n : Noun) : n.shape.size = n.size := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp only [shape, Nock.BTree.size, size]; omega

/-- The Dyck word of a noun: the encoding of its shape.  By `Lem:pbt_size` a
    noun with `λ` leaves has size `2λ − 1`, so its Dyck word has length `2λ − 2 = 2(λ−1)`,
    matching the paper's `L^{2(λ−1)}_dk` component of a noun. -/
def dyckWord (n : Noun) : List Bool := n.shape.encode

/-- A noun's Dyck word has length `2·leaves − 2 = 2(λ−1)`. -/
theorem dyckWord_length (n : Noun) : n.dyckWord.length + 2 = 2 * n.leaves := by
  have h1 := Nock.BTree.encode_length_add_one n.shape
  have h2 := shape_size n
  have h3 := size_add_one n
  simp only [dyckWord]
  omega

end Noun

/-! ### Catalan cardinality `|L^{2λ}_dk| = C_λ`

    The paper's `Lem:optimal_dyck` closes with the counting claim
        `|L^{2λ}_dk| = C_λ`,   the λ-th Catalan number.
    By the length-graded bijection `dyck_length_graded`, `L^{2λ}_dk` is in bijection with the
    proper binary trees of size `2λ+1` (`BTree` with `size = 2λ+1`).  Mathlib counts binary
    trees by their number of *internal* nodes: `BinaryTree.treesOfNumNodesEq λ` is the finset of
    `BinaryTree Unit` with `numNodes = λ`, and `treesOfNumNodesEq_card_eq_catalan` gives its
    cardinality as `catalan λ`.  We bridge via the shape isomorphism `BTree ≃ BinaryTree Unit`
    (a `BTree` leaf ↦ `nil`, a `BTree` node ↦ a `BinaryTree` node), under which
    `size = 2·numNodes + 1`, so `size = 2λ+1 ⟺ numNodes = λ`. -/

namespace BTree

/-- The shape isomorphism to Mathlib's `BinaryTree`: a proper-binary-tree `leaf` is Mathlib's
    empty leaf `nil`; a `node` is a Mathlib `node` carrying the unit value. -/
def toBin : BTree → BinaryTree Unit
  | .leaf     => .nil
  | .node l r => .node () (toBin l) (toBin r)

/-- Inverse of `toBin`. -/
def ofBin : BinaryTree Unit → BTree
  | .nil        => .leaf
  | .node _ l r => .node (ofBin l) (ofBin r)

@[simp] theorem ofBin_toBin (t : BTree) : ofBin (toBin t) = t := by
  induction t <;> simp_all [toBin, ofBin]

@[simp] theorem toBin_ofBin (t : BinaryTree Unit) : toBin (ofBin t) = t := by
  induction t <;> simp_all [toBin, ofBin]

/-- `BTree ≃ BinaryTree Unit` — the data-free proper-binary-tree shape is exactly Mathlib's
    `BinaryTree Unit` (`L_full_BT` as a Fintype-graded object). -/
def equivBin : BTree ≃ BinaryTree Unit :=
  ⟨toBin, ofBin, ofBin_toBin, toBin_ofBin⟩

/-- Under the shape isomorphism, `BTree.size` is `2·numNodes + 1`: a proper binary tree with
    `λ` internal (Mathlib) nodes has `2λ+1` total nodes (`Lem:pbt_size`,. -/
theorem size_eq (t : BTree) : t.size = 2 * (toBin t).numNodes + 1 := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
      simp only [size, toBin, BinaryTree.numNodes, ihl, ihr]
      omega

/-- **`|L^{2λ}_dk|` as a finset.**  The Dyck words of length `2λ`, obtained
    as the image of Mathlib's `treesOfNumNodesEq λ` under `encode ∘ ofBin`. -/
noncomputable def dyckWordsOfLen (lam : ℕ) : Finset (List Bool) :=
  (BinaryTree.treesOfNumNodesEq lam).map
    ⟨fun t => encode (ofBin t), fun a b h => by
      have := encode_injective h
      have := congrArg toBin this
      simpa using this⟩

/-- A word lies in `dyckWordsOfLen λ` iff it is a Dyck word of length `2λ` — i.e. this finset is
    exactly the paper's `L^{2λ}_dk`. -/
theorem mem_dyckWordsOfLen {lam : ℕ} {w : List Bool} :
    w ∈ dyckWordsOfLen lam ↔ Dyck w ∧ w.length = 2 * lam := by
  simp only [dyckWordsOfLen, Finset.mem_map, Function.Embedding.coeFn_mk,
    BinaryTree.mem_treesOfNumNodesEq]
  constructor
  · rintro ⟨t, ht, rfl⟩
    show Dyck (encode (ofBin t)) ∧ (encode (ofBin t)).length = 2 * lam
    refine ⟨dyck_encode _, ?_⟩
    have hlen := encode_length_add_one (ofBin t)
    have hsz := size_eq (ofBin t)
    rw [toBin_ofBin, ht] at hsz
    omega
  · rintro ⟨hd, hlen⟩
    obtain ⟨s, hs⟩ := exists_encode_of_dyck hd
    refine ⟨toBin s, ?_, ?_⟩
    · have hlen' := encode_length_add_one s
      have hsz := size_eq s
      rw [hs, hlen] at hlen'
      omega
    · show encode (ofBin (toBin s)) = w
      rw [ofBin_toBin, hs]

/-- **`|L^{2λ}_dk| = C_λ`.**  The number of Dyck words of length `2λ` is the
    λ-th Catalan number.  This is the counting claim of `Lem:optimal_dyck`. -/
theorem dyckWordsOfLen_card (lam : ℕ) : (dyckWordsOfLen lam).card = catalan lam := by
  rw [dyckWordsOfLen, Finset.card_map, BinaryTree.treesOfNumNodesEq_card_eq_catalan]

/-- `dyckWordsOfLen λ` is, as a set, exactly `L^{2λ}_dk = { w ∈ L_dk | |w| = 2λ }`
.  Combined with `dyckWordsOfLen_card`, this is `|L^{2λ}_dk| = C_λ` verbatim. -/
theorem coe_dyckWordsOfLen (lam : ℕ) :
    ↑(dyckWordsOfLen lam) = {w : List Bool | Dyck w ∧ w.length = 2 * lam} := by
  ext w; simp only [Finset.mem_coe, Set.mem_setOf_eq, mem_dyckWordsOfLen]

end BTree
end Nock
