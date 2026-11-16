/-
  Nock/Tree.lean

  The fundamental data object: a *noun*.

  Paper correspondence:
    - §2.2 "Recursive Tree Representations": a noun is a proper binary tree whose
      leaves carry data.  The paper models the data at the leaves as field elements
      (`DT(F)`); here, for the *semantics* layer, leaves are natural numbers, exactly
      matching standard (Urbit) Nock atoms.
    - Def "noun": `n = (t, dt)`, a Dyck word `t` plus a leaf array `dt`.
      Here the isomorphic *inductive* presentation is primary; the Dyck-word
      encoding lives in `Nock/Dyck.lean`.
-/

namespace Nock

/-- A Nock noun: an `atom` (a natural number) or a `cell` (an ordered pair of nouns).
    This is a *proper binary tree* with `Nat`-labelled leaves. -/
inductive Noun where
  | atom : Nat → Noun
  | cell : Noun → Noun → Noun
deriving Repr, DecidableEq, Inhabited

namespace Noun

/-- `?` in Nock terms: is this noun a cell? -/
def isCell : Noun → Bool
  | .cell _ _ => true
  | .atom _   => false

def isAtom (n : Noun) : Bool := !n.isCell

/-- Number of leaves — the paper's `λ`. -/
def leaves : Noun → Nat
  | .atom _   => 1
  | .cell l r => l.leaves + r.leaves

/-- Total node count.  For a proper binary tree this equals `2 * leaves - 1` — proved below (`pbt_size`). -/
def size : Noun → Nat
  | .atom _   => 1
  | .cell l r => 1 + l.size + r.size

/-- Number of *internal* nodes (cells) — the paper's `λ - 1`. -/
def internal : Noun → Nat
  | .atom _   => 0
  | .cell l r => 1 + l.internal + r.internal

/-! ### `Lem:pbt_size` -/

/-- The additive form of `Lem:pbt_size`: a proper binary tree has `size = 2·leaves − 1`,
    stated over `Nat` without truncated subtraction as `size + 1 = 2·leaves`. -/
theorem size_add_one (n : Noun) : n.size + 1 = 2 * n.leaves := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp only [size, leaves]; omega

/-- **Lemma (proper binary tree size).**  A proper binary tree with
    `2λ − 1` nodes has `λ` leaf nodes and `λ − 1` internal nodes.  Concretely: for every
    noun, `size = 2·leaves − 1` and `internal = leaves − 1`; equivalently, if `size = 2λ−1`
    then `leaves = λ` and `internal = λ−1`. -/
theorem pbt_size (n : Noun) :
    n.size = 2 * n.leaves - 1 ∧ n.internal = n.leaves - 1 := by
  have hs : n.size + 1 = 2 * n.leaves := size_add_one n
  refine ⟨by omega, ?_⟩
  induction n with
  | atom k => rfl
  | cell l r ihl ihr =>
      have hl := size_add_one l
      have hr := size_add_one r
      simp only [internal, leaves]; omega

/-- `Lem:pbt_size`, in the paper's exact phrasing: if a noun has `2λ − 1` nodes (with
    `λ ≥ 1`), it has `λ − 1` internal and `λ` leaf nodes. -/
theorem pbt_size_of_size {n : Noun} {lam : Nat} (hlam : 1 ≤ lam)
    (h : n.size = 2 * lam - 1) : n.leaves = lam ∧ n.internal = lam - 1 := by
  have hs : n.size + 1 = 2 * n.leaves := size_add_one n
  have hi : n.internal = n.leaves - 1 := (pbt_size n).2
  refine ⟨by omega, by omega⟩

/-- Every node of a proper binary tree is a leaf or an internal node:
    `size = leaves + internal`. -/
theorem size_eq_leaves_add_internal (n : Noun) : n.size = n.leaves + n.internal := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp only [size, leaves, internal]; omega

end Noun

/-! ### `S`-Expressions `L_S_Exp` — scope note

    The paper first introduces the general `S`-expression language
    \[
      \mathcal{L}_{\mathsf{S\_Exp}} = \{ s \in \mathcal{S} \mid
        \mathsf{type}(s) = \mathsf{atom} \;\cup\;
        (\mathsf{left}(s) \in \mathcal{L}_{\mathsf{S\_Exp}} \cap
         \mathsf{right}(s) \in \mathcal{L}_{\mathsf{S\_Exp}}) \}
    \], an atom-or-pair recursion.  Crucially the paper then observes that this language admits **circular** `S`-expressions: the two
    elements of a pair may reference each other, so `L_S_Exp` in full generality is a
    directed *graph* with cycles, not a tree.  To keep the base variable efficient the
    paper *deliberately restricts* the variable "to a binary tree so as not to support
    this feature", i.e. to a proper binary tree = `Noun` above.

    Scope: the circular `L_S_Exp` object is **not** modelled.
    The *acyclic* fragment of `L_S_Exp` — an
    atom, or a pair of acyclic `S`-expressions — coincides definitionally with the proper
    binary tree `Noun` (`atom`/`cell`).  Thus the
    S-expression is represented, in its intended restricted form, by `Noun`; the circular
    generality is out of scope, as in the paper. -/

/-! ### Proper `n`-ary trees `L_full_T,n` — def + "not used here" note

    The paper extends the proper-binary-tree representation to proper `n`-ary trees purely "for completeness", stating explicitly that "we do not make use
    of this generalization here".  The only new functional is
    `child_i : T^n → T^n`, mapping an `n`-ary tree to its child at index `i`, generalizing
    `left`/`right`.  A proper (full) `n`-ary tree `L_full_T,n`
    is one whose every node has either zero children (a leaf, `size = 1`) or exactly `n`
    children, each itself a proper `n`-ary tree with the children disjoint. -/

/-- A proper (full) **`k`-ary tree**: every node has either zero children (`leaf`) or
    exactly `k` children (`node`, indexed by `Fin k`).  This is the paper's `L_full_T,n` with `n = k`; "properness" (0 or `k` children, children disjoint) is
    enforced by construction.  NOT USED in the rest of the development;
    provided for completeness.  The `k = 2` instance is the binary shape `BTree`
    (`Nock/Dyck.lean`), with `childi 0 = left`, `childi 1 = right`. -/
inductive NAryTree (k : Nat) where
  | leaf : NAryTree k
  | node : (Fin k → NAryTree k) → NAryTree k

namespace NAryTree

/-- The paper's `child_i` functional: the `i`-th child of a `k`-ary tree,
    or `none` at a leaf (which has no children).  Generalizes `left`/`right`. -/
def childi {k : Nat} (i : Fin k) : NAryTree k → Option (NAryTree k)
  | .leaf   => none
  | .node f => some (f i)

end NAryTree

/-! ### `k`-ary axis labeling `kAxis` — def + binary instance

    The Nock addressing scheme labels each node by its "axis" via a BFS-style recurrence.  For a general `k`-ary tree the paper gives
    \[
      \mathsf{axis}_{n_1}(n_i) = \mathsf{axis}_i \iff
        \forall j \in [k],\;
        \mathsf{axis}_{n_1}(\mathsf{child}_j(n_i)) = k \cdot \mathsf{axis}_i + (j-1).
    \]
    The paper then "restrict[s] the analysis to the case where `k = 2`",
    which is the binary axis carried by `AxisDescent` (`descA`, children `2·a` and `2·a+1`). -/

/-- The **general `k`-ary axis recurrence**: if a node has axis `a`,
    its `j`-th child (`j ∈ {1,…,k}`) has axis `k·a + (j−1)`.  The binary `descA`/slot axis
    of `Nock/AxisDescent.lean` is the `k = 2` instance. -/
def kAxis (k a j : Nat) : Nat := k * a + (j - 1)

/-- The binary (`k = 2`) instance of `kAxis`: the left child (`j = 1`) of a node with axis
    `a` has axis `2·a`, matching `descA`'s `2·k` branch. -/
theorem kAxis_two_left (a : Nat) : kAxis 2 a 1 = 2 * a := by
  simp [kAxis]

/-- The binary (`k = 2`) instance of `kAxis`: the right child (`j = 2`) of a node with axis
    `a` has axis `2·a + 1`, matching `descA`'s `2·k + 1` branch. -/
theorem kAxis_two_right (a : Nat) : kAxis 2 a 2 = 2 * a + 1 := by
  simp [kAxis]

end Nock
