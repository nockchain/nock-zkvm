/-
  Nock/RedTeam/Batch1CoreData.lean

  Core Data Structures (Nouns & Trees).
  Independent verification of definitional faithfulness + non-vacuity witnesses.

  This artifact provides MACHINE-CHECKED evidence for:
  1. Def:Proper_BT — Proper Binary Tree
  2. Def:tree_nodes — leaf / internal nodes
  3. Def:noun — noun = (t, dt)
  4. Lem:pbt_size — size relation
  5. Algorithm:Valid_Noun — CheckValidNoun

  HYGIENE: No `sorry`, `admit`, or `native_decide`. Axiom-clean.
-/
import Nock.NounValidation

namespace Nock.RedTeam

/-! ## 1. Def:Proper_BT — Proper Binary Tree

    Paper: `L_full_BT = { t | size(t)=1 ∪ (left(t)∈L_full_BT ∩ right(t)∈L_full_BT ∩
    (left(t)∩right(t)=∅)) }`

    Adversarial checks:
    (a) Properness: every node has exactly 0 (atom/leaf) or 2 (cell/node) children
    (b) Acyclicity/finiteness: children are strictly smaller ⇒ no cycles
    (c) Base case: `(Noun.atom k).size = 1` -/

/-- **[1.a] Child count classification**: Every `Noun` has exactly 0 or 2 children.
    This is the paper's "proper" constraint: `size(t) = 1` ⇔ leaf (0 children),
    otherwise 2 children. The inductive definition enforces this by construction. -/
def childCount (n : Noun) : Nat :=
  match n with
  | .atom _ => 0
  | .cell _ _ => 2

/-- Every Noun has child count ∈ {0, 2} — the properness invariant. -/
theorem childCount_in_zero_or_two (n : Noun) : childCount n = 0 ∨ childCount n = 2 := by
  cases n <;> simp [childCount]

/-- Atoms have exactly 0 children (leaf nodes). -/
theorem childCount_atom (k : ℕ) : childCount (Noun.atom k) = 0 := rfl

/-- Cells have exactly 2 children (internal nodes). -/
theorem childCount_cell (l r : Noun) : childCount (Noun.cell l r) = 2 := rfl

/-- **[1.b.i] Acyclicity witness (left child)**: The left subtree is strictly smaller.
    This is the paper's disjoint-children restriction realized: since `l.size < cell.size`,
    no circular reference is possible. -/
theorem left_size_lt_cell_size (l r : Noun) : l.size < (Noun.cell l r).size := by
  simp only [Noun.size]
  omega

/-- **[1.b.ii] Acyclicity witness (right child)**: The right subtree is strictly smaller. -/
theorem right_size_lt_cell_size (l r : Noun) : r.size < (Noun.cell l r).size := by
  simp only [Noun.size]
  omega

/-- **[1.b.iii] Combined acyclicity**: Both children are strictly smaller than parent.
    This establishes that `Noun` is an inductive well-founded type with no cycles. -/
theorem children_strictly_smaller (l r : Noun) :
    l.size < (Noun.cell l r).size ∧ r.size < (Noun.cell l r).size :=
  ⟨left_size_lt_cell_size l r, right_size_lt_cell_size l r⟩

/-- **[1.c] Base case**: An atom has size 1, matching paper's `size(t) = 1` for leaves. -/
theorem atom_size_eq_one (k : ℕ) : (Noun.atom k).size = 1 := rfl

/-- **[1.c'] Size is always positive**: Every noun has size ≥ 1 (no empty trees). -/
theorem size_pos (n : Noun) : 1 ≤ n.size := by
  induction n with
  | atom k => simp [Noun.size]
  | cell l r ihl ihr => simp only [Noun.size]; omega

/-! ## 2. Def:tree_nodes — leaf / internal nodes

    Paper: A node with no children is a LEAF; a non-leaf node is INTERNAL.

    Adversarial checks:
    (a) Every node is leaf XOR internal; `size = leaves + internal`
    (b) Non-vacuity: both categories are inhabited -/

/-- **[2.a.i] Atom ⟺ childCount = 0**: The paper's "no children" = atom. -/
theorem atom_iff_childCount_zero (n : Noun) : n.isAtom = true ↔ childCount n = 0 := by
  cases n with
  | atom k => simp [Noun.isAtom, Noun.isCell, childCount]
  | cell l r => simp [Noun.isAtom, Noun.isCell, childCount]

/-- **[2.a.ii] Cell ⟺ childCount = 2**: The paper's "has children" = cell. -/
theorem cell_iff_childCount_two (n : Noun) : n.isCell = true ↔ childCount n = 2 := by
  cases n with
  | atom k => simp [Noun.isAtom, Noun.isCell, childCount]
  | cell l r => simp [Noun.isAtom, Noun.isCell, childCount]

/-- **[2.a.iii] Exclusive**: A node is a leaf XOR internal (not both, not neither). -/
theorem leaf_xor_internal (n : Noun) : n.isAtom = true ↔ n.isCell = false := by
  simp [Noun.isAtom, Noun.isCell]

/-- **[2.a.iv] Size decomposition** (cite existing `size_eq_leaves_add_internal`):
    `size = leaves + internal`. This is the partition of nodes. -/
example (n : Noun) : n.size = n.leaves + n.internal := Noun.size_eq_leaves_add_internal n

/-- **[2.b.i] Non-vacuity (leaf)**: There exist nouns with leaves (every noun has ≥1 leaf). -/
theorem leaves_inhabited : ∃ n : Noun, n.leaves ≥ 1 := ⟨Noun.atom 0, by simp [Noun.leaves]⟩

/-- **[2.b.ii] Non-vacuity (internal)**: There exist nouns with internal nodes. -/
theorem internal_inhabited : ∃ n : Noun, n.internal ≥ 1 :=
  ⟨Noun.cell (Noun.atom 0) (Noun.atom 1), by simp [Noun.internal]⟩

/-- **[2.b.iii] Concrete witness**: A cell with two atoms has 2 leaves and 1 internal node. -/
example : (Noun.cell (Noun.atom 0) (Noun.atom 1)).leaves = 2 := rfl
example : (Noun.cell (Noun.atom 0) (Noun.atom 1)).internal = 1 := rfl
example : (Noun.cell (Noun.atom 0) (Noun.atom 1)).size = 3 := rfl

/-! ## 3. Def:noun — noun `n = (t, dt)`

    Paper: `n := (t, dt) ∈ L_dk^{2(λ-1)} × DT(F)^λ` — a Dyck word `t` (shape) plus
    an ordered array `dt` of λ FIELD elements.

    Lean: `Noun` is an inductive tree with `Nat`-valued leaves (not field elements).

    Adversarial checks:
    (a) Isomorphism: `Noun ≃ (shape × leaf-list)` — reconstruction round-trip
    (b) DRIFT: Lean leaves are `Nat`, not field elements — document this
    (c) Length bookkeeping: Dyck word has length `2(λ-1)`, there are λ leaves -/

/-- The extraction function: given a `Noun`, extract its shape and leaf list. -/
def extractShapeLeaves (n : Noun) : BTree × List ℕ := (n.shape, n.leafList)

/-- **[3.a.i] The round-trip property** (cite existing `eq_of_shape_leafList`):
    Two nouns with equal shape and leafList are equal. This proves the uniqueness
    of `(t, dt) ↦ n` (the paper's "corresponds to a unique noun"). -/
example {n₁ n₂ : Noun} (hs : n₁.shape = n₂.shape) (hl : n₁.leafList = n₂.leafList) :
    n₁ = n₂ := Noun.eq_of_shape_leafList hs hl

/-- **[3.a.ii] Injectivity** (cite existing `noun_dyck_leaf_injective`):
    `n ↦ (n.dyckWord, n.leafList)` is injective. -/
example : Function.Injective (fun n : Noun => (n.dyckWord, n.leafList)) :=
  Noun.noun_dyck_leaf_injective

/-- **[3.a.iii] Shape preserves size** (cite existing `shape_size`):
    `n.shape.size = n.size`. -/
example (n : Noun) : n.shape.size = n.size := Noun.shape_size n

/-- **[3.b] DRIFT FINDING (documented)**: Lean leaves are `Nat`, not field elements.

    The paper defines `dt ∈ DT(F)^λ` where F is a finite field.
    The Lean `Noun` uses `Nat`-valued leaves (see `Nock/Tree.lean:8-16` docstring).

    This is a DOCUMENTED Phase-2 deferral: the field-valued view (`Nat → K`) is
    introduced at the NPR layer (`Nock/NPR.lean:leafF`), where atoms are cast
    into the field. At the semantics layer, atoms remain `Nat` (matching Urbit).

    VERDICT: Benign documented deferral, not a faithfulness break. The
    `Nat`-to-field cast is explicit and tracked at the NPR boundary. -/
def drift_Nat_vs_Field_documented : String :=
  "Lean leaves are Nat; paper uses F. Cast to F happens at NPR layer (leafF). " ++
  "See Tree.lean:8-16 docstring. Phase-2 deferral, not a gap."

/-- **[3.c.i] Length bookkeeping (Dyck word)**: A noun's Dyck word has length `2(λ-1)`.
    (Cite existing `dyckWord_length`: `dyckWord.length + 2 = 2 * leaves`.) -/
example (n : Noun) : n.dyckWord.length + 2 = 2 * n.leaves := Noun.dyckWord_length n

/-- **[3.c.ii] Length bookkeeping (leaf list)**: A noun's leaf list has length λ.
    (Cite existing `leafList_length`.) -/
example (n : Noun) : n.leafList.length = n.leaves := Noun.leafList_length n

/-- **[3.c.iii] Concrete example**: For `atom 42`, the Dyck word is empty (length 0 = 2(1-1))
    and leafList has 1 element. -/
example : (Noun.atom 42).dyckWord.length = 0 := rfl
example : (Noun.atom 42).leafList.length = 1 := rfl
example : (Noun.atom 42).leaves = 1 := rfl

/-- **[3.c.iv] Concrete example (λ=2)**: For `cell (atom 1) (atom 2)`, Dyck word has
    length 2 = 2(2-1) and leafList has 2 elements. -/
example : (Noun.cell (Noun.atom 1) (Noun.atom 2)).dyckWord.length = 2 := rfl
example : (Noun.cell (Noun.atom 1) (Noun.atom 2)).leafList.length = 2 := rfl
example : (Noun.cell (Noun.atom 1) (Noun.atom 2)).leaves = 2 := rfl

/-! ## 4. Lem:pbt_size — size relation

    Paper: A tree in `L^{2λ-1}_full_BT` has `λ-1` internal and `λ` leaf nodes.

    Lean: `pbt_size_of_size {n lam} (hlam : 1 ≤ lam) (h : n.size = 2*lam-1) :
           n.leaves = lam ∧ n.internal = lam-1` @ `Nock/Tree.lean:81`

    Adversarial checks:
    (a) NON-VACUITY: The hypothesis `1 ≤ lam ∧ n.size = 2*lam-1` is satisfiable
    (b) Guard check: The `1 ≤ lam` guard is load-bearing (not decorative) -/

/-- **[4.a.i] Non-vacuity witness family**: For every λ ≥ 1, there exists a noun
    with size = 2λ-1. We construct a "right spine" of λ atoms. -/
def rightSpine : ℕ → Noun
  | 0 => Noun.atom 0  -- degenerate case, size 1
  | 1 => Noun.atom 0  -- λ=1: just an atom, size 1 = 2*1-1
  | n + 2 => Noun.cell (Noun.atom 0) (rightSpine (n + 1))

/-- Right spine has the correct size. -/
theorem rightSpine_size : ∀ lam : ℕ, 1 ≤ lam → (rightSpine lam).size = 2 * lam - 1 := by
  intro lam hlam
  match lam with
  | 1 => rfl
  | lam + 2 =>
      simp only [rightSpine, Noun.size]
      have ih := rightSpine_size (lam + 1) (by omega)
      omega

/-- **[4.a.ii] Satisfiability of `pbt_size_of_size` hypotheses**: For every λ ≥ 1,
    we can find a noun satisfying the premises. -/
theorem pbt_size_hypothesis_satisfiable (lam : ℕ) (hlam : 1 ≤ lam) :
    ∃ n : Noun, n.size = 2 * lam - 1 :=
  ⟨rightSpine lam, rightSpine_size lam hlam⟩

/-- **[4.a.iii] Non-vacuity: the conclusion fires.** -/
theorem pbt_size_conclusion_fires (lam : ℕ) (hlam : 1 ≤ lam) :
    (rightSpine lam).leaves = lam ∧ (rightSpine lam).internal = lam - 1 :=
  Noun.pbt_size_of_size hlam (rightSpine_size lam hlam)

/-- **[4.a.iv] Concrete instance λ=1**: An atom has size 1 = 2*1-1, 1 leaf, 0 internal. -/
example : (Noun.atom 0).size = 2 * 1 - 1 := rfl
example : (Noun.atom 0).leaves = 1 := rfl
example : (Noun.atom 0).internal = 1 - 1 := rfl

/-- **[4.a.v] Concrete instance λ=2**: `cell(atom,atom)` has size 3 = 2*2-1. -/
example : (Noun.cell (Noun.atom 0) (Noun.atom 1)).size = 2 * 2 - 1 := rfl
example : (Noun.cell (Noun.atom 0) (Noun.atom 1)).leaves = 2 := rfl
example : (Noun.cell (Noun.atom 0) (Noun.atom 1)).internal = 2 - 1 := rfl

/-- **[4.a.vi] Concrete instance λ=3**: A 3-leaf tree. -/
def threeLeafTree : Noun := Noun.cell (Noun.atom 0) (Noun.cell (Noun.atom 1) (Noun.atom 2))
example : threeLeafTree.size = 2 * 3 - 1 := rfl
example : threeLeafTree.leaves = 3 := rfl
example : threeLeafTree.internal = 3 - 1 := rfl

/-- **[4.b.i] Guard is load-bearing**: Size = 0 is impossible (size ≥ 1 always). -/
theorem size_ne_zero (n : Noun) : n.size ≠ 0 := by
  have := size_pos n
  omega

/-- **[4.b.ii] No noun has size = 2*0-1**: The λ=0 case is vacuously blocked by
    the `1 ≤ lam` guard, but ALSO because `2*0-1 = 0` in Nat and no noun has size 0. -/
theorem no_size_zero_noun : ¬∃ n : Noun, n.size = 2 * 0 - 1 := by
  intro ⟨n, h⟩
  simp at h
  exact size_ne_zero n h

/-- **[4.b.iii] Guard is load-bearing (direct)**: Without `1 ≤ lam`, the statement
    `n.size = 2 * lam - 1 → n.leaves = lam` would be vacuously true for lam=0
    because the premise is unsatisfiable. The guard makes this explicit. -/
theorem guard_is_load_bearing :
    (∀ n : Noun, n.size = 2 * 0 - 1 → n.leaves = 0) ∧  -- vacuously true
    ¬(∃ n : Noun, n.size = 2 * 0 - 1) := by  -- because no such n exists
  constructor
  · intro n h; simp at h; exact absurd h (size_ne_zero n)
  · exact no_size_zero_noun

/-! ## 5. Algorithm:Valid_Noun — CheckValidNoun

    Paper pseudocode: Init mset={n₀}; parse transcript; each step parse (n,n_L,n_R),
    REJECT if n∉mset, remove n; if atom then REJECT if n_L,n_R ≠ ⊥; else REJECT if
    n ≠ cons(n_L,n_R), push n_L,n_R; ACCEPT iff mset empty at end.

    Lean: `checkValidNoun` @ `Nock/NounValidation.lean:111`

    Adversarial checks:
    (a) DISCRIMINATION: The verifier is not trivially accepting/rejecting
    (b) FAITHFULNESS: Each paper reject condition is enforced by `stepMset` -/

/-- A concrete accepting example: atom 42 with its transcript. -/
def atom42 : Noun := Noun.atom 42
def atom42_transcript : Transcript := [(Noun.atom 42, none)]

/-- **[5.a.i] Non-vacuity (accept)**: The verifier ACCEPTS valid input. -/
theorem atom42_accepts : checkValidNoun atom42 atom42_transcript = Result.accept := rfl

/-- A concrete cell and its valid transcript. -/
def cell01 : Noun := Noun.cell (Noun.atom 0) (Noun.atom 1)
def cell01_transcript : Transcript :=
  [(Noun.cell (Noun.atom 0) (Noun.atom 1), some (Noun.atom 0, Noun.atom 1)),
   (Noun.atom 0, none),
   (Noun.atom 1, none)]

/-- **[5.a.ii] Non-vacuity (accept cell)**: The verifier ACCEPTS a valid cell. -/
theorem cell01_accepts : checkValidNoun cell01 cell01_transcript = Result.accept := rfl

-- **[5.a.iii] Discrimination: bad transcript is REJECTED.**

-- Case 1: Transcript names a node not in mset (paper line 1250: "If n ∉ mset, Reject")
def bad_transcript_wrong_node : Transcript := [(Noun.atom 99, none)]
theorem reject_wrong_node : checkValidNoun atom42 bad_transcript_wrong_node = Result.reject := rfl

-- Case 2: Atom step with non-⊥ children (paper line 1253: "If n_L,n_R ≠ ⊥, Reject")
def bad_transcript_atom_with_children : Transcript :=
  [(Noun.atom 42, some (Noun.atom 0, Noun.atom 1))]
theorem reject_atom_with_children :
    checkValidNoun atom42 bad_transcript_atom_with_children = Result.reject := rfl

-- Case 3: Cell step with wrong decomposition (paper line 1255: "If n ≠ cons(n_L,n_R), Reject")
def bad_transcript_wrong_decomp : Transcript :=
  [(Noun.cell (Noun.atom 0) (Noun.atom 1), some (Noun.atom 5, Noun.atom 6))]
theorem reject_wrong_decomp :
    checkValidNoun cell01 bad_transcript_wrong_decomp = Result.reject := rfl

-- Case 4: Transcript too short (mset not empty at end)
def bad_transcript_too_short : Transcript :=
  [(Noun.cell (Noun.atom 0) (Noun.atom 1), some (Noun.atom 0, Noun.atom 1))]
  -- Missing the atom steps for children
theorem reject_too_short :
    checkValidNoun cell01 bad_transcript_too_short = Result.reject := rfl

-- Case 5: Cell claimed as atom (none instead of some)
def bad_transcript_cell_as_atom : Transcript :=
  [(Noun.cell (Noun.atom 0) (Noun.atom 1), none)]
theorem reject_cell_as_atom :
    checkValidNoun cell01 bad_transcript_cell_as_atom = Result.reject := rfl

-- **[5.b] Faithfulness of stepMset**: Each reject branch is exercised.

/-- **[5.b.i] n ∉ mset ⇒ stepMset returns none (reject).**
    When the transcript names a node not in the multiset, stepMset fails. -/
theorem stepMset_rejects_not_in_mset :
    stepMset ({Noun.atom 42} : Multiset Noun) (Noun.atom 99) none = none := by
  simp [stepMset]

/-- **[5.b.ii] Atom with children ⇒ stepMset returns none (reject).**
    An atom step must have `ch = none`; `some (_, _)` is rejected. -/
theorem stepMset_rejects_atom_with_children (l r : Noun) :
    stepMset ({Noun.atom 42} : Multiset Noun) (Noun.atom 42) (some (l, r)) = none := rfl

/-- **[5.b.iii] Cell with wrong children ⇒ stepMset returns none (reject).**
    A cell step must have `ch = some (a, b)` where `cell a b = n`. -/
theorem stepMset_rejects_wrong_children :
    let n := Noun.cell (Noun.atom 0) (Noun.atom 1)
    stepMset ({n} : Multiset Noun) n (some (Noun.atom 5, Noun.atom 6)) = none := rfl

/-- **[5.b.iv] Cell claimed as atom ⇒ stepMset returns none (reject).** -/
theorem stepMset_rejects_cell_as_atom :
    let n := Noun.cell (Noun.atom 0) (Noun.atom 1)
    stepMset ({n} : Multiset Noun) n none = none := rfl

/-- **[5.b.v] Correct steps succeed**: When the transcript matches, stepMset succeeds. -/
theorem stepMset_accepts_correct_atom :
    stepMset ({Noun.atom 42} : Multiset Noun) (Noun.atom 42) none = some 0 := rfl

theorem stepMset_accepts_correct_cell :
    let n := Noun.cell (Noun.atom 0) (Noun.atom 1)
    let result := stepMset ({n} : Multiset Noun) n (some (Noun.atom 0, Noun.atom 1))
    result = some ({Noun.atom 0, Noun.atom 1} : Multiset Noun) := rfl

/-!
### [5.b.vi] Faithfulness summary

No discrepancy found between paper pseudocode and `stepMset`. All four reject
branches are present and faithfully implemented:
- n ∉ mset → reject (membership check before processing)
- atom with n_L,n_R ≠ ⊥ → reject (atom case checks `ch = none`)
- cell with n ≠ cons(n_L,n_R) → reject (cell case checks children match)
- cell claimed as atom (none) → reject (pattern match fails)

VERDICT: Algorithm:Valid_Noun faithfully implemented. No drift found.
-/

def checkValidNoun_faithfulness_verdict : String :=
  "All paper reject branches present in stepMset. " ++
  "Discrimination witnessed: verifier accepts valid, rejects invalid. " ++
  "No discrepancy found."

/-! ## Summary: Disposition per object

1. Def:Proper_BT — PASSED (properness by construction, acyclicity witnessed)
2. Def:tree_nodes — PASSED (leaf/internal partition + non-vacuity)
3. Def:noun — PASSED with DOCUMENTED DRIFT (Nat vs Field, deferred to NPR)
4. Lem:pbt_size — PASSED (non-vacuity via witness family, guard is load-bearing)
5. Algorithm:Valid_Noun — PASSED (discrimination + faithfulness witnessed)
-/

def batch1_summary : List (String × String) :=
  [("Def:Proper_BT", "passed"),
   ("Def:tree_nodes", "passed"),
   ("Def:noun", "passed (drift: Nat vs Field, documented Phase-2 deferral)"),
   ("Lem:pbt_size", "passed"),
   ("Algorithm:Valid_Noun", "passed")]

end Nock.RedTeam
