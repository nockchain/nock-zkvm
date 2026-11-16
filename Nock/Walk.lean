/-
  Nock/Walk.lean

  The generic compilation engine of paper §3.2: the recursively
  verifiable stateful `n`-ary tree `L_RVT^{F,n}`, the sufficient state/data-separation
  conditions, the `RAP_walk` construction, the main theorem `Thm:Walk_IOP`, and the
  forest corollary `Corr:forest`.

  ──────────────────────────────────────────────────────────────────────────────────────
  MODELING OVERVIEW
  ──────────────────────────────────────────────────────────────────────────────────────

  * `Def:RVT`.  A stateful labeled proper `n`-ary tree is the inductive
    type `NTree LT n` with labels in `LT = S × DT` and a child map `Fin n → Option (…)`
    (`none = ⊥`).  Being an element of `L_SLT^n` is structural, so the type
    *is* the SLT language.  The recursively-verifiable predicate `RVT F`
    is the recursive membership over the algebraically-constrainable labeling language
    `L(F,n)`, modeled as a relation `F : LT → (Fin n → Option LT) → Prop`.

  * `Def:state_data_separation`.  Bundled as `StateSep`:
      - `Sleaf`      : the leaf-state predicate `S_leaf ⊆ S`;
      - `solely`     : `s ∈ S_leaf ⟺ node is a leaf`  (solely state-traversable);
      - `fanout`     : `S → ℕ` with `fanout(s) ∈ [n]` on non-leaf states and `fanout=0`
                       on leaf states, together with the
                       state-defined dynamic labeling property.

  * `RAP_walk`.  The columns are functions `ℕ → …` (row-indexed, paper's
    1-indexing i = 1..h).  Column set:
      `current_node` (via `rlc`), `children` (n of them, via `rlc`), one-hot `st`,
      line `ln`, `count`, accumulator `acc_walk`, plus `T_F`/`F`-constraints abstracted as
      the labeling relation.  `RLC^γ(v) = Σ γ^{c} v(c)` is `rlc`.  The one-hot column `st`
      is captured by `OneHot st jrow` (⟹ the paper's two booleanity constraints, proved as
      `oneHot_booleanity`), which collapses `Σ_j st(i,j)·g(j) = g(jrow i)` (`sum_oneHot`);
      because `fanout` of a leaf state is `0`, the paper's restriction of the accumulation
      sum to `s_j ∈ S∖S_leaf` is automatic, so we carry the accumulation in the collapsed
      per-row form `∑_{l=1}^{fanout(jrow i)}` (see `WalkSat`).

  * `Thm:Walk_IOP` & PROOF.  Following the paper:
      - `nodeListP k`  = `∑_{i=1}^k RLC^γ(current(i))·X^i`,
      - `nodeQueueP k` = the BFS-queue polynomial with the paper's closed form,
      and we prove sorry-free:
        `ln_closed`      `ln(k)=α^k`
        `count_closed`   `count(k)=α^{1+Σfanout}`
        `nodeQueue_deg`  `deg(node_queue_k)=1+Σfanout`
        `nodeQueue_succ` the paper's queue recurrence
        `acc_closed`     `acc_walk(k)=−node_list_k(α)+node_queue_k(α)`
        `walk_completeness` / `out_walk = 0 ⟺ node_list(α)=node_queue_h(α)`
        `walk_soundness_card` Schwartz–Zippel bound `≤ h/|K|`.
      The single combinatorial bridge the paper calls "self-evident" — that the polynomial
      identity `node_list = node_queue_h` together with the `F`-constraints yields an actual
      `L_RVT^{F,n}` tree — is `reconTree_ReconGoal` (deterministic inverse-BFS
      reconstruction + RVT lift), composed into the literal soundness statements
      `Walk_IOP_final_card` / `Walk_IOP_final_prob`.

  * `Corr:forest`.  Identical gates; only `seed`/`initial_count` change.
    The arithmetic core takes `seed` and `initial_count` as parameters, so the forest
    accepting-identity `forest_walk` and `forest_completeness` carry over verbatim; rows =
    total nodes in aggregate.  The forest *soundness* Schwartz–Zippel ingredient is proved
    (`forest_soundness_card`/`_prob`, `≤h/|K|` at the polynomial-inequality level, the forest
    analogue of `walk_soundness_card`), and the *fully composed* forest soundness is
    proved too (see §`ForestComposeRVT` below): `reconForest_ForestReconGoal` lifts it
    through `ForestReconGoal`/`StateSep` — the literal `∃ (sltᵢ)_{i=1}^{kroots} ∈ ∏ L_RVT`
    reconstruction statement, via the multi-root inverse-BFS reconstruction
    `firstCF`/`buildTF`/`reconForest` — and `Walk_IOP_forest_final_card`/`_prob` are the
    literal soundness statements (`≤ h/|K| + ε_RLC`), the multi-root analogues of
    `Walk_IOP_final_card`/`_prob`.  `Nock/PaperNames.lean` aliases `«Corr:forest»` to
    `Walk_IOP_forest_final_prob`.  No strength is lost at one root:
    `ForestReconGoal_one` and `Walk_IOP_final_card_of_forest` recover the single-tree
    statements as the `kroots = 1` case.  Everything named here is sorry-free.

    SCOPE, at the chip layer (`Nock/NockVM.lean`), which is a *separate* claim from the
    above: the integrated capstone `NockVM.V_NockVMROM_forest` DOES discharge the memory
    conjunct at `kroots ≥ 1` through `walkBadForest`/`Walk_IOP_forest_final_prob`, so
    subject-mutating programs are covered — indeed
    `Thm:mem_38`'s own proof applies `Corr:forest`, not `Thm:Walk_IOP`, to `L_mem`.
    What is single-root is (i) the *un-linked bundle* corollary `NockVM.NockVMROM`, whose memory conjunct is instantiated at
    `hSfm : Sf fom hm + 1 = hm`, and (ii) the compute walk in both capstones, which is
    single-root by design (one initial subject-formula pair).
-/
import Nock.Field
import Nock.SetEq
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.BigOperators.Intervals

open Polynomial BigOperators
open scoped Classical

namespace Nock
namespace Walk

/-! ## §3.2 `Def:RVT` — recursively verifiable stateful `n`-ary trees -/

/-- A stateful labeled proper `n`-ary tree with label space `LT`, modeled
    as a rose tree: a node carries a label and the *ordered list of its non-`⊥` children*.
    The paper's `Fin n → Option (NTree)` child map is recovered by `childOpt`
    (`none = ⊥`, entries beyond the list are `⊥`); arity `n` is a bound on `children.length`
    imposed by membership, not by the type.  `L_SLT^n` is exactly the set of
    such trees, so the type models the SLT language directly. -/
inductive NTree (LT : Type*) where
  | node (label : LT) (children : List (NTree LT))
deriving Inhabited

namespace NTree
variable {LT : Type*}

/-- The label of a node. -/
def label : NTree LT → LT
  | node l _ => l

/-- The ordered list of (non-`⊥`) children. -/
def children : NTree LT → List (NTree LT)
  | node _ c => c

@[simp] theorem label_node (l : LT) (c : List (NTree LT)) : (node l c).label = l := rfl
@[simp] theorem children_node (l : LT) (c : List (NTree LT)) : (node l c).children = c := rfl

/-- A node is a *leaf* iff it has no children. -/
def isLeaf (t : NTree LT) : Prop := t.children = []

/-- The `i`-th child as `Option` (`none = ⊥` for `i` past the last non-`⊥` child).  This is
    the paper's child map `Fin n → Option (NTree)` restricted along `Fin n ↪ ℕ`. -/
def childOpt (t : NTree LT) (i : ℕ) : Option (NTree LT) := t.children[i]?

/-- `child_label(i, t)`: the label of the `i`-th child, or `⊥`. -/
def childLabel (t : NTree LT) (i : ℕ) : Option LT := (t.childOpt i).map label

/-- Total node count `total_nodes(t)`. -/
def size : NTree LT → ℕ
  | node _ c => 1 + (c.map size).sum

end NTree

/-- **`Def:RVT`.**  A recursively-verifiable stateful labeled `n`-ary tree
    over the algebraically-constrainable labeling language `L(F,n)`, where
    `F : LT → (Fin n → Option LT) → Prop` recognizes `((l, child_labels) ∈ L(F,n))`
    (with the convention that leaf outputs are all `⊥`).  The child-label vector
    `Fin n → Option LT` is `fun i => t.childLabel i` restricted to `Fin n`.  The three
    clauses of the paper:
      (1) `(l, child_label(·,rvt)) ∈ L(F,n)`;
      (2) every non-`⊥` child is itself in `L_RVT^{F,n}`;
      (3) `size = 1  ⟺  (l, {⊥}^n) ∈ L(F,n)`  (leaf iff the label verifies with no
          children). -/
def RVT {LT : Type*} {n : ℕ} (F : LT → (Fin n → Option LT) → Prop) :
    NTree LT → Prop
  | t@(NTree.node l ch) =>
      F l (fun i => t.childLabel i)
        ∧ (∀ s ∈ ch, RVT F s)
        ∧ (t.isLeaf ↔ F l (fun _ => none))
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹s ∈ ch›
  omega

/-! ## `Def:state_data_separation` -/

/-- **`Def:state_data_separation`.**  Sufficient conditions on `L(F,n)`.
    The label space is `S × DT`; `st` extracts the state.  Bundles:
      * `Sleaf`  — the leaf-state subset `S_leaf ⊆ S`;
      * `solely` — *solely state-traversable*: for every `rvt`, `state ∈ S_leaf ⟺ leaf`;
      * `fanout` — `fanout(s) ∈ [n]` for non-leaf `s`, `fanout(s)=0` for leaf `s`, and `dynamic`: whenever `(x,x_out) ∈ L(F,n)`
                   with `x=(s,d)`, exactly the first `fanout(s)` outputs are non-`⊥`
                   (*state-defined dynamic labeling*). -/
structure StateSep {S DT : Type*} {n : ℕ}
    (F : (S × DT) → (Fin n → Option (S × DT)) → Prop) where
  /-- The leaf-state subset `S_leaf ⊆ S`. -/
  Sleaf : S → Prop
  /-- `fanout(s)`: the number of non-`⊥` children of a state-`s` node. -/
  fanout : S → ℕ
  /-- `fanout(s) ∈ [n]` on non-leaf states. -/
  fanout_le : ∀ s, fanout s ≤ n
  /-- Leaf states have `fanout = 0`. -/
  fanout_leaf : ∀ s, Sleaf s → fanout s = 0
  /-- **Solely state-traversable**: the state decides leaf-ness. -/
  solely : ∀ t : NTree (S × DT), RVT F t →
    (Sleaf (NTree.label t).1 ↔ t.isLeaf)
  /-- **State-defined dynamic labeling**: an accepted statement `(x,x_out)`
      with `x=(s,d)` has exactly the first `fanout(s)` outputs non-`⊥`. -/
  dynamic : ∀ (s : S) (d : DT) (xout : Fin n → Option (S × DT)), F (s, d) xout →
    (∀ i : Fin n, ((i : ℕ) < fanout s ↔ xout i ≠ none))

/-! ## `RAP_walk` — the arithmetized walk

  We work over a field `K` (the extension field of the paper).  Columns are row-indexed
  by `ℕ` following the paper's 1-indexing (`i = 1..h`).  `node_size` is the width of a node
  in `𝔽`, `numStates = |S|`, `n` the arity. -/

section Core

variable {K : Type*} [Field K]
variable {numStates n node_size : ℕ}

/-- **`RLC^γ`.**  `RLC^γ(v) = Σ_{c} γ^{c} · v(c)`, the random linear
    combination of a node vector `v ∈ 𝔽^{node_size}` at challenge `γ ∈ K`. -/
def rlc (γ : K) (v : Fin node_size → K) : K := ∑ c : Fin node_size, γ ^ (c : ℕ) * v c

/-- **One-hot state column**: `st(i,j) = 1` iff `j` is the active state
    `jrow i` of row `i`, else `0`.  This is the canonical solution of the paper's two
    booleanity constraints (`Σ_j st(i,j)=1` and `Σ_j st(i,j)(1−st(i,j))=0`), which it
    entails (`oneHot_booleanity`). -/
def OneHot (st : ℕ → Fin numStates → K) (jrow : ℕ → Fin numStates) : Prop :=
  ∀ i j, st i j = if j = jrow i then 1 else 0

/-- **State booleanity, forward.**  A one-hot column satisfies the paper's
    two booleanity constraints for every row `i`:
    `Σ_j st(i,j) = 1` and `Σ_j st(i,j)·(1 − st(i,j)) = 0`. -/
theorem oneHot_booleanity {st : ℕ → Fin numStates → K} {jrow : ℕ → Fin numStates}
    (h : OneHot st jrow) (i : ℕ) :
    (∑ j, st i j) = 1 ∧ (∑ j, st i j * (1 - st i j)) = 0 := by
  constructor
  · simp only [h i]
    rw [Finset.sum_ite_eq' Finset.univ (jrow i) (fun _ => (1 : K))]
    simp
  · apply Finset.sum_eq_zero
    intro j _
    rw [h i j]
    by_cases hj : j = jrow i <;> simp [hj]

/-- **One-hot collapse.**  `Σ_j st(i,j)·g(j) = g(jrow i)`: the one-hot
    column selects the active state's summand.  This turns the paper's
    `Σ_{s_j∈S} st(i,j)·(…)` into the per-row `(…)` evaluated at the active state. -/
theorem sum_oneHot {st : ℕ → Fin numStates → K} {jrow : ℕ → Fin numStates}
    (h : OneHot st jrow) (i : ℕ) (g : Fin numStates → K) :
    (∑ j, st i j * g j) = g (jrow i) := by
  simp only [h i, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (jrow i) g]
  simp

/-! ### The `RAP_walk` satisfaction predicate

  Given fanout `fo : ℕ → ℕ` (`fo i = fanout(jrow i)`) and the RLC-reduced columns
  `cur i = RLC^γ(current(i))`, `chld i l = RLC^γ(children(i,l))` (l = 1..fanout), the
  paper's initial inputs & constraints.  `fanout(leaf)=0` makes the
  restriction of the accumulation sum to non-leaf states automatic, so the sums run
  `l = 1..fo i`. -/

/-- Partial fanout sum `Σ_{i=1}^k fanout(j(i))`. -/
def Sf (fo : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 k, fo i

/-- **`RAP_walk` initial inputs & constraints** in RLC-reduced,
    collapsed one-hot form.  Row range is `1..h`. -/
structure WalkSat (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (ln count acc : ℕ → K) (α seed initial_count : K) (h : ℕ) : Prop where
  /-- `h ≥ 1`: at least the root row. -/
  hpos : 1 ≤ h
  /-- **Initial line constraint:** `ln(1) = α`. -/
  ln1 : ln 1 = α
  /-- **Line-number increment:** `ln(i+1) = α·ln(i)`. -/
  lnInc : ∀ i, 1 ≤ i → i < h → ln (i + 1) = α * ln i
  /-- **Initial count:** `count(1) = initial_count·α^{fanout(j(1))}`. -/
  count1 : count 1 = initial_count * α ^ (fo 1)
  /-- **Count increment:** `count(i+1) = count(i)·α^{fanout(j(i+1))}`. -/
  countInc : ∀ i, 1 ≤ i → i < h → count (i + 1) = count i * α ^ (fo (i + 1))
  /-- **Initial accumulator constraint.** -/
  accInit : ln 1 * cur 1 + acc 1
      = (∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * initial_count * chld' 1 l) + seed
  /-- **Line-indexed multiset accumulation step.** -/
  accStep : ∀ i, 1 ≤ i → i < h →
      ln (i + 1) * cur (i + 1) + acc (i + 1) - acc i
        = ∑ l ∈ Finset.Icc 1 (fo (i + 1)), α ^ l * count i * chld' (i + 1) l

variable {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {ln count acc : ℕ → K}
variable {α seed initial_count : K} {h : ℕ}

/-! ### The `node_list` and `node_queue` polynomials -/

/-- **`node_list_k(X)`:** `Σ_{i=1}^k RLC^γ(current(i))·X^i`. -/
noncomputable def nodeListP (cur : ℕ → K) (k : ℕ) : K[X] :=
  ∑ i ∈ Finset.Icc 1 k, C (cur i) * X ^ i

/-- The `i`-th accumulation contribution to the queue:
    `Σ_{l=1}^{fanout(j(i))} RLC^γ(children(i,l))·X^{1+l+Σ_{m=1}^{i-1}fanout(j(m))}`. -/
noncomputable def queueTerm (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (i : ℕ) : K[X] :=
  ∑ l ∈ Finset.Icc 1 (fo i), C (chld' i l) * X ^ (1 + l + Sf fo (i - 1))

/-- **`node_queue_k(X)`, closed form.**  `RLC^γ(current(1))·X` plus the
    accumulation contributions of rows `1..k`.  We take the closed form as the definition
    and prove it satisfies the paper's recurrence (`nodeQueue_succ`) and degree formula
    (`nodeQueue_deg`). -/
noncomputable def nodeQueueP (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (k : ℕ) : K[X] :=
  C (cur 1) * X + ∑ i ∈ Finset.Icc 1 k, queueTerm chld' fo i

/-! ### Fanout partial-sum arithmetic -/

@[simp] theorem Sf_zero (fo : ℕ → ℕ) : Sf fo 0 = 0 := by simp [Sf]

theorem Sf_succ (fo : ℕ → ℕ) (k : ℕ) : Sf fo (k + 1) = Sf fo k + fo (k + 1) := by
  unfold Sf; rw [Finset.sum_Icc_succ_top (by omega)]

theorem Sf_one (fo : ℕ → ℕ) : Sf fo 1 = fo 1 := by
  have := Sf_succ fo 0; simpa using this

theorem Sf_pred_succ (fo : ℕ → ℕ) {i : ℕ} (hi : 1 ≤ i) :
    Sf fo i = Sf fo (i - 1) + fo i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  have hj : 1 + j - 1 = j := by omega
  rw [hj, Nat.add_comm 1 j, Sf_succ]

theorem Sf_mono (fo : ℕ → ℕ) {i k : ℕ} (h : i ≤ k) : Sf fo i ≤ Sf fo k := by
  unfold Sf
  exact Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_right h)

/-! ### `node_list` / `node_queue` recurrences, evaluations, and degrees -/

theorem nodeListP_succ (cur : ℕ → K) (k : ℕ) :
    nodeListP cur (k + 1) = nodeListP cur k + C (cur (k + 1)) * X ^ (k + 1) := by
  unfold nodeListP; rw [Finset.sum_Icc_succ_top (by omega)]

theorem queueTerm_eval (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (i : ℕ) (α : K) :
    (queueTerm chld' fo i).eval α
      = ∑ l ∈ Finset.Icc 1 (fo i), chld' i l * α ^ (1 + l + Sf fo (i - 1)) := by
  unfold queueTerm
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [eval_mul, eval_C, eval_pow, eval_X]

theorem nodeQueueP_succ (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (k : ℕ) :
    nodeQueueP cur chld' fo (k + 1)
      = nodeQueueP cur chld' fo k + queueTerm chld' fo (k + 1) := by
  unfold nodeQueueP; rw [Finset.sum_Icc_succ_top (by omega)]; ring

theorem nodeListP_eval (cur : ℕ → K) (k : ℕ) (α : K) :
    (nodeListP cur k).eval α = ∑ i ∈ Finset.Icc 1 k, cur i * α ^ i := by
  unfold nodeListP
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [eval_mul, eval_C, eval_pow, eval_X]

/-- **`node_list` degree bound:** `deg(node_list_k) ≤ k`. -/
theorem nodeListP_natDegree_le (cur : ℕ → K) (k : ℕ) : (nodeListP cur k).natDegree ≤ k := by
  unfold nodeListP
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  refine le_trans (natDegree_C_mul_le _ _) ?_
  rw [natDegree_X_pow]
  exact (Finset.mem_Icc.mp hi).2

/-- **`node_queue` degree bound:** `deg(node_queue_k) ≤ 1 + Σ_{i≤k}fanout`.
    The paper states equality; equality additionally needs the leading child-RLC not to
    vanish, so the rigorous statement is the upper bound (which is what soundness uses). -/
theorem nodeQueueP_natDegree_le (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (k : ℕ) :
    (nodeQueueP cur chld' fo k).natDegree ≤ 1 + Sf fo k := by
  unfold nodeQueueP
  refine le_trans (natDegree_add_le _ _) ?_
  rw [max_le_iff]
  refine ⟨?_, ?_⟩
  · refine le_trans (natDegree_C_mul_le _ _) ?_
    rw [natDegree_X]; omega
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    unfold queueTerm
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro l hl
    refine le_trans (natDegree_C_mul_le _ _) ?_
    rw [natDegree_X_pow]
    have hik := (Finset.mem_Icc.mp hi)
    have hlk := (Finset.mem_Icc.mp hl)
    have hsi : Sf fo (i - 1) + fo i = Sf fo i := (Sf_pred_succ fo hik.1).symm
    calc 1 + l + Sf fo (i - 1) ≤ 1 + fo i + Sf fo (i - 1) := by omega
      _ = 1 + Sf fo i := by omega
      _ ≤ 1 + Sf fo k := by have := Sf_mono fo hik.2; omega

section Telescope

variable {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {ln count acc : ℕ → K}
variable {α seed initial_count : K} {h : ℕ}

/-- **`ln(k) = α^k`.** -/
theorem ln_closed (hw : WalkSat cur chld' fo ln count acc α seed initial_count h) :
    ∀ k, 1 ≤ k → k ≤ h → ln k = α ^ k := by
  intro k
  induction k with
  | zero => intro h1 _; omega
  | succ m ih =>
    intro _ hle
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simpa using hw.ln1
    · rw [hw.lnInc m hm (by omega), ih hm (by omega)]; ring

/-- **`count(k) = initial_count·α^{Σ_{i≤k}fanout}`.** -/
theorem count_closed (hw : WalkSat cur chld' fo ln count acc α seed initial_count h) :
    ∀ k, 1 ≤ k → k ≤ h → count k = initial_count * α ^ (Sf fo k) := by
  intro k
  induction k with
  | zero => intro h1 _; omega
  | succ m ih =>
    intro _ hle
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; rw [hw.count1, Sf_one]
    · rw [hw.countInc m hm (by omega), ih hm (by omega), Sf_succ, pow_add]; ring

/-- Per-row child contribution `childSum(i) = Σ_{l=1}^{fanout(j(i))} RLC(children(i,l))·
    α^{l+Σ_{m≤i-1}fanout}`. -/
def childSum (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (α : K) (i : ℕ) : K :=
  ∑ l ∈ Finset.Icc 1 (fo i), chld' i l * α ^ (l + Sf fo (i - 1))

/-- **General telescoping identity.**  Summing `accInit` and the accumulation steps with `ln(k)=α^k`, `count(k)=initial_count·α^{Σfanout}` yields, for
    `1 ≤ k ≤ h`,
    `acc(k) = seed − node_list_k(α) + initial_count·Σ_{i≤k} childSum(i)`.
    This is the paper before substituting the concrete `(seed,initial_count)`;
    the concrete recognizer values are substituted in `acc_closed`. -/
theorem acc_telescope (hw : WalkSat cur chld' fo ln count acc α seed initial_count h) :
    ∀ k, 1 ≤ k → k ≤ h →
      acc k = seed - (nodeListP cur k).eval α
        + initial_count * ∑ i ∈ Finset.Icc 1 k, childSum chld' fo α i := by
  intro k
  induction k with
  | zero => intro h1 _; omega
  | succ m ih =>
    intro _ hle
    rcases Nat.eq_zero_or_pos m with hm | hm
    · -- base case k = 1
      subst hm
      have hstep := hw.accInit
      rw [hw.ln1] at hstep
      -- childSum 1 = ∑ chld' 1 l * α^l  (since Sf fo 0 = 0)
      have hcs1 : childSum chld' fo α 1 = ∑ l ∈ Finset.Icc 1 (fo 1), chld' 1 l * α ^ l := by
        unfold childSum; simp
      -- the accInit RHS child sum, rearranged
      have hrhs : (∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * initial_count * chld' 1 l)
          = initial_count * childSum chld' fo α 1 := by
        rw [hcs1, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_); ring
      rw [hrhs] at hstep
      have hnl : (nodeListP cur 1).eval α = cur 1 * α := by
        rw [nodeListP_eval]; simp
      have hqcs : (∑ i ∈ Finset.Icc 1 1, childSum chld' fo α i) = childSum chld' fo α 1 := by
        simp
      rw [hnl, hqcs]
      -- from α * cur 1 + acc 1 = initial_count * childSum 1 + seed
      linear_combination hstep
    · -- step case k = m+1, m ≥ 1
      have hstep := hw.accStep m hm (by omega)
      rw [ln_closed hw (m + 1) (by omega) (by omega),
          count_closed hw m hm (by omega)] at hstep
      -- RHS = initial_count * childSum (m+1)
      have hcs : (∑ l ∈ Finset.Icc 1 (fo (m + 1)),
                    α ^ l * (initial_count * α ^ Sf fo m) * chld' (m + 1) l)
          = initial_count * childSum chld' fo α (m + 1) := by
        unfold childSum
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        have : (m + 1) - 1 = m := by omega
        rw [this, pow_add]; ring
      rw [hcs] at hstep
      have ihm := ih hm (by omega)
      rw [nodeListP_succ, eval_add, eval_mul, eval_C, eval_pow, eval_X]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
      -- acc (m+1) = acc m - α^(m+1) cur(m+1) + initial_count childSum(m+1)
      have hacc : acc (m + 1)
          = acc m - α ^ (m + 1) * cur (m + 1) + initial_count * childSum chld' fo α (m + 1) := by
        linear_combination hstep
      rw [hacc, ihm]
      ring

end Telescope

end Core

/-! ### `node_queue` evaluation and the recognizer closed form -/

variable {K : Type*} [Field K]

theorem nodeQueueP_eval (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (k : ℕ) (α : K) :
    (nodeQueueP cur chld' fo k).eval α
      = cur 1 * α
        + ∑ i ∈ Finset.Icc 1 k, ∑ l ∈ Finset.Icc 1 (fo i),
            chld' i l * α ^ (1 + l + Sf fo (i - 1)) := by
  unfold nodeQueueP
  rw [eval_add, eval_mul, eval_C, eval_X, eval_finsetSum]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact queueTerm_eval chld' fo i α

section Recognizer

variable {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {ln count acc : ℕ → K}
variable {α seed initial_count : K} {h : ℕ}

/-- **`acc_walk(k) = −node_list_k(α) + node_queue_k(α)`.**  The recognizer
    setting substitutes `seed = RLC^γ(current(1))·α` and `initial_count = α`
    into the general telescoping identity `acc_telescope`. -/
theorem acc_closed (hw : WalkSat cur chld' fo ln count acc α seed initial_count h)
    (hseed : seed = cur 1 * α) (hic : initial_count = α) :
    ∀ k, 1 ≤ k → k ≤ h →
      acc k = -(nodeListP cur k).eval α + (nodeQueueP cur chld' fo k).eval α := by
  intro k hk1 hkh
  rw [acc_telescope hw k hk1 hkh, nodeQueueP_eval, hseed, hic]
  have key : α * ∑ i ∈ Finset.Icc 1 k, childSum chld' fo α i
      = ∑ i ∈ Finset.Icc 1 k, ∑ l ∈ Finset.Icc 1 (fo i),
          chld' i l * α ^ (1 + l + Sf fo (i - 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold childSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [pow_add, pow_one]
    ring
  rw [key]; ring

/-- **`out_walk = 0 ⟺ node_list(α) = node_queue_h(α)`.**  With the terminal
    constraint `out_walk = acc_walk(h)`. -/
theorem walk_out_zero_iff (hw : WalkSat cur chld' fo ln count acc α seed initial_count h)
    (hseed : seed = cur 1 * α) (hic : initial_count = α) :
    acc h = 0 ↔ (nodeListP cur h).eval α = (nodeQueueP cur chld' fo h).eval α := by
  rw [acc_closed hw hseed hic h hw.hpos (le_refl h)]
  constructor
  · intro heq; linear_combination -heq
  · intro heq; rw [heq]; ring

/-- **Perfect completeness.**  If the walk columns form a full breadth-first
    traversal — i.e. the arithmetized identity `node_list = node_queue_h` —
    then `out_walk = acc_walk(h) = 0`. -/
theorem walk_completeness (hw : WalkSat cur chld' fo ln count acc α seed initial_count h)
    (hseed : seed = cur 1 * α) (hic : initial_count = α)
    (hbft : nodeListP cur h = nodeQueueP cur chld' fo h) :
    acc h = 0 := by
  rw [walk_out_zero_iff hw hseed hic, hbft]

end Recognizer

/-! ### Schwartz–Zippel soundness -/

section Soundness

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Univariate Schwartz–Zippel / root counting: a nonzero polynomial of `natDegree d`
    vanishes at at most `d` points of `K`. -/
theorem card_roots_le (q : K[X]) (hq : q ≠ 0) :
    (Finset.univ.filter (fun r : K => q.eval r = 0)).card ≤ q.natDegree := by
  have hset : (Finset.univ.filter (fun r : K => q.eval r = 0)) = q.roots.toFinset := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_toFinset,
      mem_roots hq, IsRoot.def]
  rw [hset]
  calc q.roots.toFinset.card ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := card_roots' q

/-- **Soundness error `≤ h/|K|`, cardinality form.**  If the walk does *not*
    encode a full BFT (the polynomials `node_list_h` and `node_queue_h` differ) but its
    fanout structure is that of an `h`-node tree (`Σfanout + 1 ≤ h` — every non-root node is
    exactly one child), then at most `h` challenges `α ∈ K` make `node_list_h(α) =
    node_queue_h(α)` — equivalently (via `walk_out_zero_iff`), at most `h` challenges accept
    a cheating table with `out_walk = 0`.  A degree-`≤ h` polynomial identity checked at a
    random `α` fails for a wrong table with probability `≤ h/|K|`. -/
theorem walk_soundness_card {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {h : ℕ}
    (hne : nodeListP cur h ≠ nodeQueueP cur chld' fo h) (hdeg : Sf fo h + 1 ≤ h) :
    (Finset.univ.filter
        (fun r : K => (nodeListP cur h).eval r = (nodeQueueP cur chld' fo h).eval r)).card ≤ h := by
  have hPne : (nodeListP cur h - nodeQueueP cur chld' fo h) ≠ 0 := sub_ne_zero.mpr hne
  have hset : (Finset.univ.filter
        (fun r : K => (nodeListP cur h).eval r = (nodeQueueP cur chld' fo h).eval r))
      = Finset.univ.filter
        (fun r : K => (nodeListP cur h - nodeQueueP cur chld' fo h).eval r = 0) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_sub, sub_eq_zero]
  rw [hset]
  refine le_trans (card_roots_le _ hPne) ?_
  refine le_trans (natDegree_sub_le _ _) ?_
  rw [max_le_iff]
  exact ⟨nodeListP_natDegree_le cur h,
    le_trans (nodeQueueP_natDegree_le cur chld' fo h) (by omega)⟩

/-- **Soundness error `≤ h/|K|`, probability form.**  The counting-measure
    probability that a random `α ∈ K` accepts a non-BFT table is `≤ h/|K|`. -/
theorem walk_soundness_prob {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {h : ℕ}
    (hne : nodeListP cur h ≠ nodeQueueP cur chld' fo h) (hdeg : Sf fo h + 1 ≤ h) :
    ((Finset.univ.filter
        (fun r : K => (nodeListP cur h).eval r = (nodeQueueP cur chld' fo h).eval r)).card : ℚ)
        / (Fintype.card K)
      ≤ (h : ℚ) / (Fintype.card K) := by
  have hpos : (0 : ℚ) < Fintype.card K := by
    haveI : Nonempty K := ⟨0⟩
    exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff_of_pos_right hpos]
  exact_mod_cast walk_soundness_card hne hdeg

end Soundness

/-! ## `Thm:Walk_IOP`: the packaged theorem -/

section WalkIOP

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {ln count acc : ℕ → K}
variable {α seed initial_count : K} {h : ℕ}

/-- The arithmetized "full breadth-first traversal" condition: the paper
    proves that `{current_node}_{i=1}^h` is a full BFT iff `node_list = node_queue_h` as
    polynomials.  We take this identity as the arithmetized BFT predicate. -/
def IsFullBFT (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (h : ℕ) : Prop :=
  nodeListP cur h = nodeQueueP cur chld' fo h

/-- **`Thm:Walk_IOP`, arithmetized form — sorry-free.**  For the recognizer
    settings `seed = RLC^γ(slt)·α`, `initial_count = α`:

    * **Perfect completeness:** if the table is a full BFT (`IsFullBFT`), then
      `out_walk = acc_walk(h) = 0`.

    * **Soundness error `≤ h/|K|`:** if the table is *not* a full BFT but has the fanout
      structure of an `h`-node tree, at most `h` of the `|K|` challenges `α` accept it with
      `out_walk = 0` (probability `≤ h/|K|`).

    Following the paper's proof: `ln_closed`, `count_closed`,
    `acc_closed` reduce `out_walk = 0` to the polynomial identity `node_list = node_queue_h`
    (`walk_out_zero_iff`), whose failure is caught by Schwartz–Zippel (`walk_soundness_card`).
    The reduction of genuine `L_RVT^{F,n}` membership to `IsFullBFT ∧ F`-constraints — the
    paper's "self-evident" step — is `reconTree_ReconGoal`; `Walk_IOP_final_card` /
    `Walk_IOP_final_prob` are the literal statements that compose it in. -/
theorem Walk_IOP (hw : WalkSat cur chld' fo ln count acc α seed initial_count h)
    (hseed : seed = cur 1 * α) (hic : initial_count = α) :
    (IsFullBFT cur chld' fo h → acc h = 0)
    ∧ (¬ IsFullBFT cur chld' fo h → Sf fo h + 1 ≤ h →
        (Finset.univ.filter (fun r : K =>
          (nodeListP cur h).eval r = (nodeQueueP cur chld' fo h).eval r)).card ≤ h) := by
  refine ⟨fun hbft => walk_completeness hw hseed hic hbft, fun hnb hdeg => ?_⟩
  exact walk_soundness_card hnb hdeg

end WalkIOP

/-! ## `Corr:forest`: verifiable walks over multiple trees

  "Immediate from locality": the gates are identical; only the initial inputs
  change to `seed = Σ_{i=1}^k RLC^γ(slt_i)·α^i` and `initial_count = α^k`.  The arithmetic
  core `acc_telescope` takes `seed`/`initial_count` as parameters, so the same identity
  `acc(h) = seed − node_list_h(α) + initial_count·Σ childSum` holds verbatim, and the total
  number of rows `h` is the total nodes in aggregate. -/

section Forest

variable {K : Type*} [Field K]
variable {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {ln count acc : ℕ → K}
variable {α seed initial_count : K} {h : ℕ}

/-- The forest "accepting" polynomial: `node_list_h(X)` versus the seeded, `initial_count`-
    weighted queue expansion `seed + initial_count·Σ childSum` (evaluated at `α` = `X`).  For
    a single tree with `(seed,initial_count) = (RLC(slt)·α, α)` this reduces to
    `node_list = node_queue_h` (`Walk_IOP`); the forest sets
    `(seed,initial_count) = (Σ RLC(slt_i)·α^i, α^k)`. -/
def ForestAccepts (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (α seed initial_count : K)
    (h : ℕ) : Prop :=
  (nodeListP cur h).eval α = seed + initial_count * ∑ i ∈ Finset.Icc 1 h, childSum chld' fo α i

/-- **`Corr:forest`, arithmetized — sorry-free.**  With the forest initial
    inputs (`seed = Σ RLC^γ(slt_i)·α^i`, `initial_count = α^k` — supplied as `hw`'s
    parameters), the same accumulation gates give `out_walk = acc_walk(h) = 0` iff the
    forest accepting identity holds.  Perfect completeness and the identical soundness gate
    follow from the general telescoping identity `acc_telescope`, exactly as in `Walk_IOP`
    ("immediate from locality"). -/
theorem forest_walk (hw : WalkSat cur chld' fo ln count acc α seed initial_count h) :
    acc h = 0 ↔ ForestAccepts cur chld' fo α seed initial_count h := by
  rw [acc_telescope hw h hw.hpos (le_refl h)]
  unfold ForestAccepts
  constructor
  · intro heq; linear_combination -heq
  · intro heq; rw [heq]; ring

/-- **Forest perfect completeness.**  If the forest accepting identity holds
    (the columns are a full BFT of the `k` trees in aggregate), `out_walk = 0`. -/
theorem forest_completeness (hw : WalkSat cur chld' fo ln count acc α seed initial_count h)
    (hacc : ForestAccepts cur chld' fo α seed initial_count h) :
    acc h = 0 := (forest_walk hw).mpr hacc

end Forest


/-! ## §3.2 The combinatorial bridge — `Walk_IOP` over genuine `L_RVT` membership

  The arithmetic core (`acc_closed`, `walk_out_zero_iff`,
  `walk_completeness`, `walk_soundness_card`) works at the arithmetized-BFT level.  This section
  closes the combinatorial bridge the paper calls "self-evident", giving
  `Thm:Walk_IOP` in its full form:

    `slt ∈ L_RVT^{F,n} ⟺ ∃ T_walk satisfying RAP_walk with out_walk = 0`, soundness `≤ h/|K|`.

  1. **BFS flatten** (`bfsForest`, `bfsForest_flatMap_comm`, `walk_tail_eq`): the level-order
     traversal `W = bfsForest [root]` satisfies the queue fixpoint `W = root :: W.flatMap
     children` — the paper's "given list = queue" characterization.

  2. **Queue identity → BFT** (`bfs_isFullBFT`): the walk columns `curCol/chldCol/foCol`
     derived from `W` satisfy the arithmetized identity `node_list = node_queue_h` (`IsFullBFT`).
     Mechanized by reindexing both polynomials through the flattening of step 1
     (`lpoly`, `nodeListP_eq_lpoly`, `nodeQueueP_eq`, `queueSum_eq`).

  3. **Push `RVT` through the `F`-constraints** (`RVT_iff_forall_InTree`, `RVT_iff_walk_Fcon`):
     the BFS rows are exactly the tree nodes (`mem_bfsForest`), and `RVT F root` is exactly
     "every node/row satisfies its `F`-constraint".  `StateSep` is used to match leaf rows to
     `S_leaf` (`walk_leaf_iff_Sleaf`, via `solely`/`fanout_leaf`) and to align the arithmetized
     `fanout(j(i))` with the real child count (`walk_childLabel_iff_fanout`, via `dynamic`).

  Composed with the arithmetic core: `walk_completeness_RVT` (perfect completeness),
  `walk_soundness_card` (soundness `≤ h/|K|`), packaged as `Walk_IOP_RVT`.  Also: forest
  soundness (`forest_soundness_card`/`_prob`, `Corr:forest`) and the one-hot seam
  (`paperWalkSat_collapse`: the paper's un-collapsed constraints ⟹ `WalkSat`).

  Everything below is **sorry-free**.
-/
variable {LT : Type*}

/-- Total size of a forest (list of trees). -/
def totalSize (l : List (NTree LT)) : ℕ := (l.map NTree.size).sum

@[simp] theorem totalSize_nil : totalSize ([] : List (NTree LT)) = 0 := rfl

theorem totalSize_cons (t : NTree LT) (l : List (NTree LT)) :
    totalSize (t :: l) = t.size + totalSize l := rfl

theorem totalSize_append (l₁ l₂ : List (NTree LT)) :
    totalSize (l₁ ++ l₂) = totalSize l₁ + totalSize l₂ := by
  unfold totalSize; rw [List.map_append, List.sum_append]

/-- The multiset of children of a forest, flattened left-to-right. -/
theorem totalSize_flatMap_children (l : List (NTree LT)) :
    totalSize (l.flatMap NTree.children) + l.length = totalSize l := by
  induction l with
  | nil => simp
  | cons t rest ih =>
    rw [List.flatMap_cons, totalSize_append, totalSize_cons, List.length_cons]
    -- totalSize t.children + totalSize (rest.flatMap children) + (rest.length+1) = t.size + totalSize rest
    have hts : t.size = 1 + totalSize t.children := by
      cases t with
      | node l c => simp [NTree.size, totalSize]
    omega

/-- Level-order BFS of a forest: output the current level, then recurse on the next level
    (the concatenation of all children). -/
def bfsForest (l : List (NTree LT)) : List (NTree LT) :=
  match l with
  | [] => []
  | (t :: rest) => (t :: rest) ++ bfsForest ((t :: rest).flatMap NTree.children)
termination_by totalSize l
decreasing_by
  have h := totalSize_flatMap_children (t :: rest)
  simp only [List.length_cons] at h
  omega

theorem bfsForest_nil : bfsForest ([] : List (NTree LT)) = [] := by
  rw [bfsForest]

theorem bfsForest_cons_eq (l : List (NTree LT)) (hl : l ≠ []) :
    bfsForest l = l ++ bfsForest (l.flatMap NTree.children) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons t rest => rw [bfsForest]

/-- **BFS commutes with `flatMap children`.**  The children of the BFS list, flattened, are
    the BFS list of the children level.  Proved by ordinary `Nat.rec` on a **size budget** `n`
    bounding `totalSize l`, not by well-founded recursion on `totalSize` itself. -/
theorem bfsForest_flatMap_comm_aux (n : ℕ) :
    ∀ l : List (NTree LT), totalSize l ≤ n →
      (bfsForest l).flatMap NTree.children = bfsForest (l.flatMap NTree.children) := by
  induction n with
  | zero =>
    intro l hn
    have : l = [] := by
      cases l with
      | nil => rfl
      | cons t rest =>
        exfalso
        have : 1 ≤ t.size := by cases t with | node _ _ => simp [NTree.size]
        rw [totalSize_cons] at hn; omega
    subst this; simp [bfsForest_nil]
  | succ m ih =>
    intro l hn
    by_cases hne : l = []
    · subst hne; simp [bfsForest_nil]
    · have hstep := bfsForest_cons_eq l hne
      rw [hstep, List.flatMap_append]
      by_cases hc : l.flatMap NTree.children = []
      · rw [hc]; simp only [List.flatMap_nil, List.append_nil, bfsForest_nil]
      · have hle : totalSize (l.flatMap NTree.children) ≤ m := by
          have h := totalSize_flatMap_children l
          have hlen : 0 < l.length := List.length_pos_of_ne_nil hne
          omega
        rw [ih (l.flatMap NTree.children) hle,
          bfsForest_cons_eq (l.flatMap NTree.children) hc]

theorem bfsForest_flatMap_comm (l : List (NTree LT)) :
    (bfsForest l).flatMap NTree.children = bfsForest (l.flatMap NTree.children) :=
  bfsForest_flatMap_comm_aux (totalSize l) l le_rfl

/-- **The BFS flattening identity.**  For a nonempty forest, the BFS list equals the forest
    prepended to the flattened children of its own BFS list. -/
theorem bfsForest_eq_append_flatMap (l : List (NTree LT)) (hl : l ≠ []) :
    bfsForest l = l ++ (bfsForest l).flatMap NTree.children := by
  rw [bfsForest_flatMap_comm]; exact bfsForest_cons_eq l hl

/-- The BFS walk of a single tree: `[root]`-seeded BFS.  Its tail is the flattened children
    of the whole walk (`W = root :: W.flatMap children`). -/
theorem walk_tail_eq (root : NTree LT) :
    bfsForest [root] = root :: (bfsForest [root]).flatMap NTree.children := by
  have h := bfsForest_eq_append_flatMap [root] (by simp)
  simpa using h

/-! ### Value-list polynomials (`lpoly`) -/

section Lpoly
variable {K : Type*} [Field K]

/-- `lpoly e [a₀, a₁, …] = C a₀·Xᵉ + C a₁·Xᵉ⁺¹ + …`: place a list of coefficients at
    consecutive exponents starting at `e`. -/
noncomputable def lpoly (e : ℕ) : List K → K[X]
  | [] => 0
  | (a :: rest) => C a * X ^ e + lpoly (e + 1) rest

@[simp] theorem lpoly_nil (e : ℕ) : lpoly e ([] : List K) = 0 := rfl

theorem lpoly_cons (e : ℕ) (a : K) (rest : List K) :
    lpoly e (a :: rest) = C a * X ^ e + lpoly (e + 1) rest := rfl

theorem lpoly_append (e : ℕ) (l₁ l₂ : List K) :
    lpoly e (l₁ ++ l₂) = lpoly e l₁ + lpoly (e + l₁.length) l₂ := by
  induction l₁ generalizing e with
  | nil => simp
  | cons a rest ih =>
    rw [List.cons_append, lpoly_cons, lpoly_cons, ih (e + 1), List.length_cons]
    have he : e + 1 + rest.length = e + (rest.length + 1) := by omega
    rw [he]; ring

/-- `lpoly` as an explicit `Finset.range` sum. -/
theorem lpoly_eq_sum (e : ℕ) (cs : List K) :
    lpoly e cs = ∑ i ∈ Finset.range cs.length, C (cs.getD i 0) * X ^ (e + i) := by
  induction cs generalizing e with
  | nil => simp
  | cons a rest ih =>
    rw [lpoly_cons, ih (e + 1), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    have hs : (∑ i ∈ Finset.range rest.length, C (rest.getD i 0) * X ^ (e + 1 + i))
        = ∑ i ∈ Finset.range rest.length, C (rest.getD i 0) * (X : K[X]) ^ (e + (i + 1)) := by
      apply Finset.sum_congr rfl; intro i _; congr 2; omega
    rw [hs]; ring

end Lpoly

/-! ### BFS length -/

theorem bfsForest_length_aux (n : ℕ) :
    ∀ l : List (NTree LT), totalSize l ≤ n → (bfsForest l).length = totalSize l := by
  induction n with
  | zero =>
    intro l hn
    have : l = [] := by
      cases l with
      | nil => rfl
      | cons t rest =>
        exfalso
        have : 1 ≤ t.size := by cases t with | node _ _ => simp [NTree.size]
        rw [totalSize_cons] at hn; omega
    subst this; simp [bfsForest_nil]
  | succ m ih =>
    intro l hn
    by_cases hne : l = []
    · subst hne; simp [bfsForest_nil]
    · rw [bfsForest_cons_eq l hne, List.length_append]
      have hle : totalSize (l.flatMap NTree.children) ≤ m := by
        have h := totalSize_flatMap_children l
        have hlen : 0 < l.length := List.length_pos_of_ne_nil hne
        omega
      rw [ih (l.flatMap NTree.children) hle]
      have h := totalSize_flatMap_children l
      omega

theorem bfsForest_length (l : List (NTree LT)) : (bfsForest l).length = totalSize l :=
  bfsForest_length_aux (totalSize l) l le_rfl

/-! ### Tree-derived walk columns -/

section Columns
variable {K : Type*} [Field K]
variable (nodeVal : NTree LT → K)

/-- `current_node` column reduced by an RLC valuation `nodeVal` (1-indexed): `cur i` is the
    value of the `i`-th walk node, `0` past the end. -/
def curCol (W : List (NTree LT)) : ℕ → K :=
  fun i => ((W[i - 1]?).map nodeVal).getD 0

/-- `fanout` column: number of children of the `i`-th walk node. -/
def foCol (W : List (NTree LT)) : ℕ → ℕ :=
  fun i => ((W[i - 1]?).map (fun t => t.children.length)).getD 0

/-- `children` column: value of the `l`-th child of the `i`-th walk node. -/
def chldCol (W : List (NTree LT)) : ℕ → ℕ → K :=
  fun i l => (((W[i - 1]?).bind (fun t => t.children[l - 1]?)).map nodeVal).getD 0

variable {nodeVal}

theorem sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ l ∈ Finset.Icc 1 n, f l = ∑ i ∈ Finset.range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

theorem curCol_succ (W : List (NTree LT)) (j : ℕ) :
    curCol nodeVal W (j + 1) = (W.map nodeVal).getD j 0 := by
  unfold curCol
  rw [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_map]

/-- `Sf (foCol W)` equals the length of the flattened children of the walk prefix. -/
theorem Sf_foCol (W : List (NTree LT)) (k : ℕ) :
    Sf (foCol W) k = ((W.take k).flatMap NTree.children).length := by
  induction k with
  | zero => simp [Sf]
  | succ m ih =>
    rw [Sf_succ, ih, List.take_add_one, List.flatMap_append, List.length_append]
    congr 1
    unfold foCol
    rw [Nat.add_sub_cancel]
    cases W[m]? with
    | none => simp
    | some t => simp

/-- The queue accumulation contribution of row `k+1` is the `lpoly` of that node's children
    placed after the `Sf`-many already-queued children. -/
theorem queueTerm_eq_lpoly (W : List (NTree LT)) (k : ℕ) :
    queueTerm (chldCol nodeVal W) (foCol W) (k + 1)
      = lpoly (2 + Sf (foCol W) k)
          (((W[k]?.map NTree.children).getD []).map nodeVal) := by
  set blk := (W[k]?.map NTree.children).getD [] with hblk
  have hfo : foCol W (k + 1) = blk.length := by
    unfold foCol
    rw [Nat.add_sub_cancel, hblk]
    cases W[k]? <;> simp
  unfold queueTerm
  rw [hfo, Nat.add_sub_cancel, lpoly_eq_sum, List.length_map,
    sum_Icc_one_eq_range]
  apply Finset.sum_congr rfl
  intro i _
  have hchld : chldCol nodeVal W (k + 1) (i + 1) = (blk.map nodeVal).getD i 0 := by
    unfold chldCol
    rw [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_map, hblk,
      Nat.add_sub_cancel]
    cases W[k]? with
    | none => rfl
    | some t => rfl
  rw [hchld]
  congr 2
  omega

/-- **`node_list` as a value-list polynomial.** -/
theorem nodeListP_eq_lpoly (W : List (NTree LT)) :
    nodeListP (curCol nodeVal W) W.length = lpoly 1 (W.map nodeVal) := by
  unfold nodeListP
  rw [sum_Icc_one_eq_range, lpoly_eq_sum, List.length_map]
  apply Finset.sum_congr rfl
  intro i _
  rw [curCol_succ]
  congr 2
  omega

/-- The queue accumulation over the first `k` rows is the `lpoly` of the flattened children
    of the walk prefix. -/
theorem queueSum_eq (W : List (NTree LT)) (k : ℕ) :
    ∑ i ∈ Finset.Icc 1 k, queueTerm (chldCol nodeVal W) (foCol W) i
      = lpoly 2 (((W.take k).flatMap NTree.children).map nodeVal) := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ m + 1), ih, queueTerm_eq_lpoly,
      List.take_add_one, List.flatMap_append, List.map_append, lpoly_append, List.length_map]
    have hB : (W[m]?.map NTree.children).getD [] = (W[m]?).toList.flatMap NTree.children := by
      cases W[m]? <;> simp
    rw [hB, Sf_foCol W m]

/-- **`node_queue` as `RLC(root)·X` plus a value-list polynomial of the flattened children.** -/
theorem nodeQueueP_eq (W : List (NTree LT)) :
    nodeQueueP (curCol nodeVal W) (chldCol nodeVal W) (foCol W) W.length
      = C (curCol nodeVal W 1) * X + lpoly 2 ((W.flatMap NTree.children).map nodeVal) := by
  unfold nodeQueueP
  rw [queueSum_eq, List.take_length]

/-- **BRIDGE COMPLETENESS (crux).**  The walk columns derived from a genuine BFS of a tree
    satisfy the arithmetized full-BFT identity `node_list = node_queue_h`.  This is the
    paper's "self-evident" queue lemma, mechanized: the BFS list `W` satisfies
    `W = root :: W.flatMap children` (`walk_tail_eq`), so peeling the root from `node_list`
    leaves exactly the flattened-children polynomial that `node_queue` accumulates. -/
theorem bfs_isFullBFT (root : NTree LT) :
    nodeListP (curCol nodeVal (bfsForest [root])) (bfsForest [root]).length
      = nodeQueueP (curCol nodeVal (bfsForest [root]))
          (chldCol nodeVal (bfsForest [root])) (foCol (bfsForest [root]))
          (bfsForest [root]).length := by
  set W := bfsForest [root] with hWdef
  rw [nodeListP_eq_lpoly, nodeQueueP_eq]
  have hW : W = root :: W.flatMap NTree.children := by rw [hWdef]; exact walk_tail_eq root
  have hcur1 : curCol nodeVal W 1 = nodeVal root := by
    unfold curCol; rw [hW]; simp
  rw [hcur1]
  conv_lhs => rw [hW]
  rw [List.map_cons, lpoly_cons, pow_one]

end Columns

/-! ### Existence of a satisfying `RAP_walk` table for any columns -/

section Witness
variable {K : Type*} [Field K]

/-- **Table constructibility.**  For *any* node/children/fanout columns, verifier challenge
    `α` and initial inputs `(seed, initial_count)`, the prover can build line/count/accumulator
    columns satisfying every `RAP_walk` gate.  The line and count columns take their closed
    forms `α^k`, `initial_count·α^{Σfanout}`; the accumulator is built by the telescoping
    closed form, which satisfies the initial and accumulation constraints by direct algebra
    (the reverse of `acc_telescope`). -/
theorem walkSat_exists (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (α seed initial_count : K) {h : ℕ} (hh : 1 ≤ h) :
    ∃ ln count acc : ℕ → K,
      WalkSat cur chld' fo ln count acc α seed initial_count h := by
  refine ⟨fun k => α ^ k, fun k => initial_count * α ^ (Sf fo k),
    fun k => seed - (nodeListP cur k).eval α
      + initial_count * ∑ i ∈ Finset.Icc 1 k, childSum chld' fo α i, ?_⟩
  refine
    { hpos := hh
      ln1 := by simp
      lnInc := fun i _ _ => by rw [pow_succ]; ring
      count1 := by rw [Sf_one]
      countInc := fun i _ _ => by rw [Sf_succ, pow_add]; ring
      accInit := ?_
      accStep := ?_ }
  · -- accInit
    have hnl : (nodeListP cur 1).eval α = cur 1 * α := by rw [nodeListP_eval]; simp
    have hkey : initial_count * (∑ j ∈ Finset.Icc 1 1, childSum chld' fo α j)
        = ∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * initial_count * chld' 1 l := by
      rw [Finset.Icc_self, Finset.sum_singleton]
      unfold childSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [show (1 : ℕ) - 1 = 0 from rfl, Sf_zero, Nat.add_zero]
      ring
    rw [hnl]
    linear_combination hkey
  · -- accStep
    intro i _ _
    have hnl : (nodeListP cur (i + 1)).eval α
        = (nodeListP cur i).eval α + cur (i + 1) * α ^ (i + 1) := by
      rw [nodeListP_succ, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    have hcssum : (∑ j ∈ Finset.Icc 1 (i + 1), childSum chld' fo α j)
        = (∑ j ∈ Finset.Icc 1 i, childSum chld' fo α j) + childSum chld' fo α (i + 1) := by
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ i + 1)]
    have hkey : initial_count * childSum chld' fo α (i + 1)
        = ∑ l ∈ Finset.Icc 1 (fo (i + 1)),
            α ^ l * (initial_count * α ^ Sf fo i) * chld' (i + 1) l := by
      unfold childSum
      rw [Nat.add_sub_cancel, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [pow_add]; ring
    rw [hnl, hcssum]
    linear_combination hkey

end Witness

/-! ### Structural bridge: BFS rows are exactly the tree nodes; F-per-row ⟺ RVT -/

/-- `InTree c t`: node `t` occurs somewhere in tree `c` (`c` itself, or inside a subtree). -/
inductive InTree : NTree LT → NTree LT → Prop
  | here (c : NTree LT) : InTree c c
  | sub {c s t : NTree LT} (hs : s ∈ c.children) (h : InTree s t) : InTree c t

/-- **BFS rows are exactly the tree nodes.**  `t` appears in the BFS list of a forest iff it
    occurs in one of the trees. -/
theorem mem_bfsForest_aux (n : ℕ) :
    ∀ (cs : List (NTree LT)) (t : NTree LT), totalSize cs ≤ n →
      (t ∈ bfsForest cs ↔ ∃ c ∈ cs, InTree c t) := by
  induction n with
  | zero =>
    intro cs t hn
    have : cs = [] := by
      cases cs with
      | nil => rfl
      | cons c rest =>
        exfalso
        have : 1 ≤ c.size := by cases c with | node _ _ => simp [NTree.size]
        rw [totalSize_cons] at hn; omega
    subst this; simp [bfsForest_nil]
  | succ m ih =>
    intro cs t hn
    by_cases hne : cs = []
    · subst hne; simp [bfsForest_nil]
    · rw [bfsForest_cons_eq cs hne, List.mem_append]
      have hle : totalSize (cs.flatMap NTree.children) ≤ m := by
        have h := totalSize_flatMap_children cs
        have hlen : 0 < cs.length := List.length_pos_of_ne_nil hne
        omega
      rw [ih (cs.flatMap NTree.children) t hle]
      constructor
      · rintro (hmem | ⟨c, hc, hct⟩)
        · exact ⟨t, hmem, InTree.here t⟩
        · rw [List.mem_flatMap] at hc
          obtain ⟨c', hc', hcc'⟩ := hc
          exact ⟨c', hc', InTree.sub hcc' hct⟩
      · rintro ⟨c, hc, hct⟩
        cases hct with
        | here => exact Or.inl hc
        | sub hs hst =>
          refine Or.inr ⟨_, ?_, hst⟩
          rw [List.mem_flatMap]; exact ⟨c, hc, hs⟩

theorem mem_bfsForest (cs : List (NTree LT)) (t : NTree LT) :
    t ∈ bfsForest cs ↔ ∃ c ∈ cs, InTree c t :=
  mem_bfsForest_aux (totalSize cs) cs t le_rfl

/-! ### BFS splits over `++`, and BFS vs. DFS pre-order

  Two enumeration facts about `bfsForest` that the arithmetic development above never needed
  but the trace generator does.  `bfsForest` is the level-order flatten the walk RAP commits to, so every *timestamp*
  the generator hands out is indexed by BFS position.  The memory forest, by contrast, is built
  by a DFS pre-order recursion (`genMemForestFromTree`: this node's records, then each child's
  subtree in turn).  Nothing here is about the field or the RAP — these are statements about
  `NTree` enumeration order, and they are the bridge between the two orders.

  Both are permutations, not equalities: BFS and DFS visit the same nodes in different orders,
  and `Nodup`/length/membership — all that the timestamp-uniqueness argument needs — transfer across a permutation. -/

/-- A forest of total size zero is empty (every `NTree` has `size ≥ 1`). -/
theorem eq_nil_of_totalSize_eq_zero {l : List (NTree LT)} (h : totalSize l = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons t rest =>
    exfalso
    have ht : 1 ≤ t.size := by cases t with | node _ _ => simp [NTree.size]
    rw [totalSize_cons] at h; omega

private theorem perm_append_left_comm {α : Type*} (b c d : List α) :
    (b ++ (c ++ d)).Perm (c ++ (b ++ d)) := by
  have h : List.Perm ((b ++ c) ++ d) ((c ++ b) ++ d) :=
    List.Perm.append_right d List.perm_append_comm
  simpa only [List.append_assoc] using h

private theorem perm_append_shuffle {α : Type*} (a b c d : List α) :
    ((a ++ b) ++ (c ++ d)).Perm ((a ++ c) ++ (b ++ d)) := by
  simp only [List.append_assoc]
  exact List.Perm.append_left a (perm_append_left_comm b c d)

/-- **BFS distributes over `++` up to permutation.**  It is *not* an equality: `bfsForest`
    interleaves the two forests level by level, whereas the right-hand side runs one forest to
    exhaustion first.  Proved by ordinary `Nat.rec` on a **size budget** `n` bounding
    `totalSize l₁ + totalSize l₂` — not by well-founded recursion on `totalSize` itself — exactly
    like `bfsForest_flatMap_comm_aux`.  `bfsForest_append_perm` then instantiates the budget at
    `totalSize l₁ + totalSize l₂` with `le_rfl`. -/
theorem bfsForest_append_perm_aux (n : ℕ) :
    ∀ l₁ l₂ : List (NTree LT), totalSize l₁ + totalSize l₂ ≤ n →
      (bfsForest (l₁ ++ l₂)).Perm (bfsForest l₁ ++ bfsForest l₂) := by
  induction n with
  | zero =>
    intro l₁ l₂ hn
    have h1 : l₁ = [] := eq_nil_of_totalSize_eq_zero (by omega)
    have h2 : l₂ = [] := eq_nil_of_totalSize_eq_zero (by omega)
    subst h1; subst h2; simp [bfsForest_nil]
  | succ m ih =>
    intro l₁ l₂ hn
    rcases eq_or_ne l₁ [] with rfl | h1
    · simp [bfsForest_nil]
    rcases eq_or_ne l₂ [] with rfl | h2
    · simp [bfsForest_nil]
    have hne : l₁ ++ l₂ ≠ [] := by simp [h1]
    have hc1 := totalSize_flatMap_children l₁
    have hc2 := totalSize_flatMap_children l₂
    have hp1 : 0 < l₁.length := List.length_pos_of_ne_nil h1
    have hp2 : 0 < l₂.length := List.length_pos_of_ne_nil h2
    have hle : totalSize (l₁.flatMap NTree.children)
        + totalSize (l₂.flatMap NTree.children) ≤ m := by omega
    rw [bfsForest_cons_eq _ hne, bfsForest_cons_eq _ h1, bfsForest_cons_eq _ h2,
      List.flatMap_append]
    refine ((ih _ _ hle).append_left (l₁ ++ l₂)).trans ?_
    exact perm_append_shuffle l₁ l₂ _ _

/-- **`bfsForest (l₁ ++ l₂) ~ bfsForest l₁ ++ bfsForest l₂`.** -/
theorem bfsForest_append_perm (l₁ l₂ : List (NTree LT)) :
    (bfsForest (l₁ ++ l₂)).Perm (bfsForest l₁ ++ bfsForest l₂) :=
  bfsForest_append_perm_aux (totalSize l₁ + totalSize l₂) l₁ l₂ le_rfl

/-- **BFS of a forest is, up to permutation, the per-tree BFS lists concatenated.**  The
    immediate consequence of `bfsForest_append_perm`, and the form a per-tree induction wants. -/
theorem bfsForest_perm_flatMap (l : List (NTree LT)) :
    (bfsForest l).Perm (l.flatMap fun t => bfsForest [t]) := by
  induction l with
  | nil => simp [bfsForest_nil]
  | cons t rest ih =>
    have h : t :: rest = [t] ++ rest := rfl
    rw [h, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact (bfsForest_append_perm [t] rest).trans (ih.append_left _)

mutual
/-- **DFS pre-order flatten of a forest**, mutually with `dfsTree`.  The recursion shape is
    deliberately the one `genMemForestFromTree`/`genMemForestFromList` use — this node first,
    then each child subtree left to right — so that a generator recursion can be re-expressed as
    a `flatMap` over `dfsTree`. -/
def dfsForest {LT : Type*} : List (NTree LT) → List (NTree LT)
  | [] => []
  | t :: ts => dfsTree t ++ dfsForest ts

/-- **DFS pre-order flatten of a tree**: the root, then its children's forests. -/
def dfsTree {LT : Type*} : NTree LT → List (NTree LT)
  | .node l cs => NTree.node l cs :: dfsForest cs
end

@[simp] theorem dfsForest_nil : dfsForest ([] : List (NTree LT)) = [] := rfl

@[simp] theorem dfsForest_cons (t : NTree LT) (ts : List (NTree LT)) :
    dfsForest (t :: ts) = dfsTree t ++ dfsForest ts := rfl

theorem dfsTree_eq (t : NTree LT) : dfsTree t = t :: dfsForest t.children := by
  cases t; rfl

/-- Unlike BFS, DFS pre-order splits over `++` as an **equality**, not merely up to permutation
    (contrast `bfsForest_append_perm`).  It is still *proved*, by structural induction on `l₁` —
    the equation is not definitional: `dfsForest` recurses on its argument list, so
    `dfsForest (l₁ ++ l₂)` and `dfsForest l₁ ++ dfsForest l₂` are only equal after `|l₁|`
    unfoldings plus associativity. -/
theorem dfsForest_append (l₁ l₂ : List (NTree LT)) :
    dfsForest (l₁ ++ l₂) = dfsForest l₁ ++ dfsForest l₂ := by
  induction l₁ with
  | nil => simp
  | cons t ts ih => simp [dfsForest_cons, ih, List.append_assoc]

/-- The DFS analogue of `bfsForest_eq_append_flatMap`, up to permutation: the roots come first,
    then (some order of) the whole next level's DFS. -/
theorem dfsForest_perm_append_flatMap_children (l : List (NTree LT)) :
    (dfsForest l).Perm (l ++ dfsForest (l.flatMap NTree.children)) := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    rw [dfsForest_cons, dfsTree_eq, List.flatMap_cons, dfsForest_append,
      List.cons_append, List.cons_append]
    refine List.Perm.cons t ?_
    refine (List.Perm.append_left _ ih).trans ?_
    exact perm_append_left_comm _ _ _

theorem bfsForest_perm_dfsForest_aux (n : ℕ) :
    ∀ l : List (NTree LT), totalSize l ≤ n → (bfsForest l).Perm (dfsForest l) := by
  induction n with
  | zero =>
    intro l hn
    have hl : l = [] := eq_nil_of_totalSize_eq_zero (by omega)
    subst hl
    simp [bfsForest_nil]
  | succ m ih =>
    intro l hn
    rcases eq_or_ne l [] with rfl | hne
    · simp [bfsForest_nil]
    have hc := totalSize_flatMap_children l
    have hp : 0 < l.length := List.length_pos_of_ne_nil hne
    have hle : totalSize (l.flatMap NTree.children) ≤ m := by omega
    rw [bfsForest_cons_eq l hne]
    exact ((ih _ hle).append_left l).trans (dfsForest_perm_append_flatMap_children l).symm

/-- **BFS and DFS enumerate the same nodes.**  The level-order flatten the walk RAP commits to
    and the pre-order flatten the generator builds with are permutations of one another.  This
    is the missing bridge for any property that is proved in one order and consumed in the
    other — `Nodup` of the timestamp exponents in particular. -/
theorem bfsForest_perm_dfsForest (l : List (NTree LT)) :
    (bfsForest l).Perm (dfsForest l) :=
  bfsForest_perm_dfsForest_aux (totalSize l) l le_rfl

/-- The single-tree form. -/
theorem dfsTree_perm_bfsForest (t : NTree LT) :
    (dfsTree t).Perm (bfsForest [t]) := by
  have h := bfsForest_perm_dfsForest [t]
  simpa [dfsForest_cons, dfsForest_nil] using h.symm

/-- DFS visits every node exactly once (`bfsForest_length` transported). -/
theorem dfsForest_length (l : List (NTree LT)) : (dfsForest l).length = totalSize l := by
  rw [← (bfsForest_perm_dfsForest l).length_eq, bfsForest_length]

/-- DFS rows are exactly the tree nodes (`mem_bfsForest` transported). -/
theorem mem_dfsForest (cs : List (NTree LT)) (t : NTree LT) :
    t ∈ dfsForest cs ↔ ∃ c ∈ cs, InTree c t := by
  rw [← (bfsForest_perm_dfsForest cs).mem_iff, mem_bfsForest]


/-! ### `ProperArity` — membership in `L_SLT^n` (the arity bound `RVT` alone omits)

  The paper's recursively-verifiable-tree language is `L_RVT^{F,n} ⊆ L_SLT^n`: the trees are
  genuine `n`-ary stateful labeled trees.  `Walk.RVT F` constrains only the child
  slots `0..n-1` (via `childLabel : Fin n → …`) and clause (2) recurses into ALL children, but it
  does NOT bound the child count — a node with a `(>n)`-th child that is itself a valid `RVT F`
  subtree still satisfies `RVT F`.  Hence `{t // RVT F t}` is STRICTLY larger than `L_RVT^{F,n}`.
  `ProperArity n` supplies the missing `L_SLT^n` bound; the faithful language is
  `{t // RVT F t ∧ ProperArity n t}` (see `fanout_eq_children_length_of_properArity`). -/

/-- **`ProperArity n t` — `t ∈ L_SLT^n`.**  Every node of `t` has at most `n`
    children, i.e. `t` is a genuine `n`-ary stateful labeled tree. -/
def ProperArity (n : ℕ) (t : NTree LT) : Prop :=
  ∀ s, InTree t s → s.children.length ≤ n

/-- The root of a `ProperArity` tree respects the arity bound. -/
theorem ProperArity.root {n : ℕ} {t : NTree LT} (h : ProperArity n t) :
    t.children.length ≤ n :=
  h t (InTree.here t)

/-- `ProperArity` is inherited by every child subtree. -/
theorem ProperArity.ofChild {n : ℕ} {t s : NTree LT} (h : ProperArity n t)
    (hs : s ∈ t.children) : ProperArity n s :=
  fun u hu => h u (InTree.sub hs hu)

section FBridge
variable {S DT : Type*} {n : ℕ} (F : (S × DT) → (Fin n → Option (S × DT)) → Prop)

/-- The per-row `F`-constraint on a node: its
    label verifies against its child labels, and it is a leaf iff its label verifies with no
    children. -/
def Fcon (t : NTree (S × DT)) : Prop :=
  F (NTree.label t) (fun i => t.childLabel i) ∧ (t.isLeaf ↔ F (NTree.label t) (fun _ => none))

/-- **`RVT` is exactly "every node satisfies its `F`-constraint".**  Structural unfolding of
    `Def:RVT`: the per-row `F`-constraints of `RAP_walk` (checked at every node/row) are
    equivalent to recursive-verifiable-tree membership. -/
theorem RVT_iff_forall_InTree (root : NTree (S × DT)) :
    RVT F root ↔ ∀ t, InTree root t → Fcon F t := by
  match root with
  | NTree.node l ch =>
    have ih : ∀ s ∈ ch, (RVT F s ↔ ∀ t, InTree s t → Fcon F t) :=
      fun s hs => RVT_iff_forall_InTree s
    unfold RVT Fcon
    constructor
    · rintro ⟨hF, hch, hleaf⟩ t ht
      cases ht with
      | here => exact ⟨hF, hleaf⟩
      | sub hs hst =>
        have := (ih _ hs).mp (hch _ hs) _ hst
        exact this
    · intro hall
      refine ⟨(hall _ (InTree.here _)).1, fun s hs => (ih s hs).mpr ?_, (hall _ (InTree.here _)).2⟩
      intro t ht
      exact hall t (InTree.sub hs ht)
termination_by sizeOf root
decreasing_by
  have h := List.sizeOf_lt_of_mem hs
  simp only [NTree.node.sizeOf_spec]
  omega

end FBridge

/-! ### Assembly: `Thm:Walk_IOP` over `L_RVT` membership -/

theorem InTree_trans {a b c : NTree LT} (h1 : InTree a b) (h2 : InTree b c) : InTree a c := by
  induction h1 with
  | here => exact h2
  | sub hs _ ih => exact InTree.sub hs (ih h2)

section Assemble
variable {S DT : Type*} {n : ℕ} {K : Type*} [Field K]
variable {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}

/-- `RVT` is hereditary along `InTree` (subtrees of an `rvt` are `rvt`s). -/
theorem RVT_of_InTree {root t : NTree (S × DT)} (hroot : RVT F root) (ht : InTree root t) :
    RVT F t := by
  rw [RVT_iff_forall_InTree] at hroot ⊢
  exact fun u hu => hroot u (InTree_trans ht hu)

/-- **The bridge (membership form).**  For the prover columns of a
    candidate tree `root`, recursive-verifiable-tree membership `rvt ∈ L_RVT^{F,n}` is exactly
    the conjunction of the per-row `F`-constraints over the BFS rows.  (The BFS rows are
    exactly the nodes of the tree, `mem_bfsForest`; and `RVT` is exactly "every node satisfies
    its `F`-constraint", `RVT_iff_forall_InTree`.) -/
theorem RVT_iff_walk_Fcon (root : NTree (S × DT)) :
    RVT F root ↔ ∀ t ∈ bfsForest [root], Fcon F t := by
  rw [RVT_iff_forall_InTree]
  constructor
  · intro h t ht
    obtain ⟨c, hc, hct⟩ := (mem_bfsForest [root] t).mp ht
    rw [List.mem_singleton] at hc; subst hc
    exact h t hct
  · intro h t ht
    exact h t ((mem_bfsForest [root] t).mpr ⟨root, List.mem_singleton.mpr rfl, ht⟩)

/-- **StateSep usage — leaf rows match `S_leaf`.**  For an `rvt`, a BFS row is a leaf (no
    children, i.e. `foCol = 0`) iff its state lies in `S_leaf` (`StateSep.solely`), and then
    its `fanout` is `0` (`StateSep.fanout_leaf`).  This is the "match leaf rows to `S_leaf`"
    step of the bridge. -/
theorem walk_leaf_iff_Sleaf (St : StateSep F) {root t : NTree (S × DT)}
    (hroot : RVT F root) (ht : InTree root t) :
    (t.isLeaf ↔ St.Sleaf (NTree.label t).1) ∧
      (t.isLeaf → St.fanout (NTree.label t).1 = 0) := by
  have hrvt : RVT F t := RVT_of_InTree hroot ht
  have hsolely := St.solely t hrvt
  refine ⟨hsolely.symm, fun hleaf => St.fanout_leaf _ (hsolely.mpr hleaf)⟩

/-- **State-defined dynamic labeling.**  For an `rvt` node,
    a child slot is non-`⊥` iff its index is below the state's `fanout` — so the state alone
    determines how many children (the real fanout) the walk must traverse, exactly aligning
    the arithmetized `fanout(j(i))` with the real child structure. -/
theorem walk_childLabel_iff_fanout (St : StateSep F) {root t : NTree (S × DT)}
    (hroot : RVT F root) (ht : InTree root t) (i : Fin n) :
    (i : ℕ) < St.fanout (NTree.label t).1 ↔ t.childLabel i ≠ none := by
  have hrvt : RVT F t := RVT_of_InTree hroot ht
  rw [RVT_iff_forall_InTree] at hrvt
  have hF : F (NTree.label t) (fun i => t.childLabel i) := (hrvt t (InTree.here t)).1
  have hF' : F ((NTree.label t).1, (NTree.label t).2) (fun i => t.childLabel i) := by
    rw [Prod.mk.eta]; exact hF
  exact St.dynamic (NTree.label t).1 (NTree.label t).2 (fun i => t.childLabel i) hF' i

/-- **BRIDGE COMPLETENESS + `Thm:Walk_IOP` (⟹), the paper.**  If `root ∈ L_RVT^{F,n}`, the
    honest prover builds a `RAP_walk` table — the BFS-order columns `curCol/chldCol/foCol`
    reduced by the RLC valuation `nodeVal`, together with line/count/accumulator columns —
    that satisfies every gate (`WalkSat`), enforces the per-row `F`-constraints, and outputs
    `out_walk = acc(h) = 0`, with recognizer inputs `(seed, initial_count) = (RLC(root)·α, α)`.
    Perfect completeness. -/
theorem walk_completeness_RVT (nodeVal : NTree (S × DT) → K) (root : NTree (S × DT)) (α : K)
    (hrvt : RVT F root) :
    ∃ ln count acc : ℕ → K,
      WalkSat (curCol nodeVal (bfsForest [root])) (chldCol nodeVal (bfsForest [root]))
        (foCol (bfsForest [root])) ln count acc α (curCol nodeVal (bfsForest [root]) 1 * α) α
        (bfsForest [root]).length
      ∧ (∀ t ∈ bfsForest [root], Fcon F t)
      ∧ acc (bfsForest [root]).length = 0 := by
  have hh : 1 ≤ (bfsForest [root]).length := by
    rw [bfsForest_length]
    cases root with
    | node l ch => simp [totalSize, NTree.size]
  obtain ⟨ln, count, acc, hw⟩ :=
    walkSat_exists (curCol nodeVal (bfsForest [root])) (chldCol nodeVal (bfsForest [root]))
      (foCol (bfsForest [root])) α (curCol nodeVal (bfsForest [root]) 1 * α) α hh
  refine ⟨ln, count, acc, hw, (RVT_iff_walk_Fcon root).mp hrvt, ?_⟩
  exact walk_completeness hw rfl rfl (bfs_isFullBFT (nodeVal := nodeVal) root)

/-- **`Thm:Walk_IOP` — arithmetic packaging (bridge + completeness + the
    Schwartz–Zippel soundness ingredient).**  This bundles three facts at the walk-column
    level; the fully composed soundness of `Thm:Walk_IOP` is stated
    separately as `walk_IOP_soundness_card` / `walk_IOP_soundness_prob` (Compose section) with the
    bound `≤ h/|K| + ε_RLC`.

    * **membership bridge** — `root ∈ L_RVT^{F,n}` iff the per-row `F`-constraints hold on all
      BFS rows (`RVT_iff_walk_Fcon`); genuine structural iff.
    * **perfect completeness** — `root ∈ L_RVT^{F,n} ⟹` an accepting `RAP_walk` table
      (`out_walk = 0`) with recognizer inputs `(RLC(root)·α, α)` (`walk_completeness_RVT`).
    * **soundness ingredient** — the third conjunct is the Schwartz–Zippel engine
      `walk_soundness_card`: `¬IsFullBFT ⟹ ≤ h accepting challenges α`.  This is only the
      `h/|K|` ingredient, not the composed soundness.  The composed soundness is
      `walk_IOP_soundness_card`:
      it commits node/child VECTORS, reduces acceptance to `IsFullBFT` at the drawn `γ`
      (`walk_out_zero_iff`), applies the reverse-BFT-iff (`isFullBFT_curVals`) and the RLC lift
      (`rlc_lift_list`/`badRLCList_card_le`), yielding the vector-BFT `VecBFT` conclusion (relative
      to the claimed fanout column `fo`, constrained only by `Sf fo h + 1 = h`) EXCEPT with
      probability `≤ h/|K| + ε_RLC`, `ε_RLC = h·(node_size − 1)/|K|` (the paper
      omits `ε_RLC`).  NOTE: `StateSep` fanout-binding (`fanout_eq_children_length`) is NOT used
      by the soundness bound — it belongs to the residual `VecBFT + F ⟹ ∃ slt ∈ L_RVT`
      inverse-BFS reconstruction. -/
theorem Walk_IOP_RVT [Fintype K] [DecidableEq K]
    (nodeVal : NTree (S × DT) → K) (root : NTree (S × DT)) (α : K) :
    -- membership bridge
    (RVT F root ↔ ∀ t ∈ bfsForest [root], Fcon F t)
    ∧ -- perfect completeness
    (RVT F root → ∃ ln count acc : ℕ → K,
        WalkSat (curCol nodeVal (bfsForest [root])) (chldCol nodeVal (bfsForest [root]))
          (foCol (bfsForest [root])) ln count acc α (curCol nodeVal (bfsForest [root]) 1 * α) α
          (bfsForest [root]).length
        ∧ (∀ t ∈ bfsForest [root], Fcon F t)
        ∧ acc (bfsForest [root]).length = 0)
    ∧ -- soundness error ≤ h/|K|
    (∀ (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ),
        ¬ IsFullBFT cur chld' fo (bfsForest [root]).length →
        Sf fo (bfsForest [root]).length + 1 ≤ (bfsForest [root]).length →
        (Finset.univ.filter (fun r : K =>
          (nodeListP cur (bfsForest [root]).length).eval r
            = (nodeQueueP cur chld' fo (bfsForest [root]).length).eval r)).card
          ≤ (bfsForest [root]).length) := by
  refine ⟨RVT_iff_walk_Fcon root, fun hrvt => walk_completeness_RVT nodeVal root α hrvt,
    fun cur chld' fo hnb hdeg => walk_soundness_card hnb hdeg⟩

end Assemble

/-! ### Forest soundness `≤ h/|K|` -/

section ForestSoundness
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **General polynomial-check soundness (the `card_roots_le` pattern).**  If two polynomials
    of `natDegree ≤ h` differ, at most `h` field elements make their evaluations agree. -/
theorem eval_eq_card_le {P Q : K[X]} {h : ℕ} (hne : P ≠ Q)
    (hP : P.natDegree ≤ h) (hQ : Q.natDegree ≤ h) :
    (Finset.univ.filter (fun r : K => P.eval r = Q.eval r)).card ≤ h := by
  have hPne : (P - Q) ≠ 0 := sub_ne_zero.mpr hne
  have hset : (Finset.univ.filter (fun r : K => P.eval r = Q.eval r))
      = Finset.univ.filter (fun r : K => (P - Q).eval r = 0) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_sub, sub_eq_zero]
  rw [hset]
  refine le_trans (card_roots_le _ hPne) ?_
  refine le_trans (natDegree_sub_le _ _) ?_
  rw [max_le_iff]; exact ⟨hP, hQ⟩

/-- The per-row child-sum polynomial (`childSum` as a polynomial in `X`). -/
noncomputable def childSumP (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (i : ℕ) : K[X] :=
  ∑ l ∈ Finset.Icc 1 (fo i), C (chld' i l) * X ^ (l + Sf fo (i - 1))

/-- **Forest `node_queue` polynomial (`Corr:forest`).**  The `k` roots are preloaded as the
    `node_list` prefix (`seed = Σ_{i≤k} RLC(sltᵢ)·αⁱ`) and the queue accumulation is weighted
    by `initial_count = αᵏ` (the `Xᵏ` factor). -/
noncomputable def forestQueueP (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (kroots h : ℕ) : K[X] :=
  nodeListP cur kroots + X ^ kroots * ∑ i ∈ Finset.Icc 1 h, childSumP chld' fo i

theorem childSumP_natDegree_le (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (i : ℕ) :
    (childSumP chld' fo i).natDegree ≤ fo i + Sf fo (i - 1) := by
  unfold childSumP
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro l hl
  refine le_trans (natDegree_C_mul_le _ _) ?_
  rw [natDegree_X_pow]
  exact Nat.add_le_add_right (Finset.mem_Icc.mp hl).2 _

theorem forestQueueP_natDegree_le (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (kroots h : ℕ) (hb : kroots + Sf fo h ≤ h) :
    (forestQueueP cur chld' fo kroots h).natDegree ≤ h := by
  have hsum : (∑ i ∈ Finset.Icc 1 h, childSumP chld' fo i).natDegree ≤ Sf fo h := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    refine le_trans (childSumP_natDegree_le chld' fo i) ?_
    have hik := Finset.mem_Icc.mp hi
    have hsi : Sf fo (i - 1) + fo i = Sf fo i := (Sf_pred_succ fo hik.1).symm
    have := Sf_mono fo hik.2
    omega
  unfold forestQueueP
  refine le_trans (natDegree_add_le _ _) ?_
  rw [max_le_iff]
  refine ⟨le_trans (nodeListP_natDegree_le cur kroots) (by omega), ?_⟩
  refine le_trans natDegree_mul_le ?_
  rw [natDegree_X_pow]
  omega

/-- **`Corr:forest` soundness, cardinality form.**  If the forest columns do
    not encode a valid aggregate BFT (`node_list_h ≠ forest_queue_h`) but have the fanout
    structure of an `h`-node forest with `k` roots, at most `h` challenges `α` accept them. -/
theorem forest_soundness_card {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {kroots h : ℕ}
    (hne : nodeListP cur h ≠ forestQueueP cur chld' fo kroots h)
    (hb : kroots + Sf fo h ≤ h) :
    (Finset.univ.filter (fun r : K =>
        (nodeListP cur h).eval r = (forestQueueP cur chld' fo kroots h).eval r)).card ≤ h :=
  eval_eq_card_le hne (nodeListP_natDegree_le cur h) (forestQueueP_natDegree_le cur chld' fo kroots h hb)

/-- **`Corr:forest` soundness, probability form.**  `≤ h/|K|`. -/
theorem forest_soundness_prob {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {kroots h : ℕ}
    (hne : nodeListP cur h ≠ forestQueueP cur chld' fo kroots h)
    (hb : kroots + Sf fo h ≤ h) :
    ((Finset.univ.filter (fun r : K =>
        (nodeListP cur h).eval r = (forestQueueP cur chld' fo kroots h).eval r)).card : ℚ)
        / (Fintype.card K)
      ≤ (h : ℚ) / (Fintype.card K) := by
  have hpos : (0 : ℚ) < Fintype.card K := by
    haveI : Nonempty K := ⟨0⟩; exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff_of_pos_right hpos]
  exact_mod_cast forest_soundness_card hne hb

end ForestSoundness

/-! ### One-hot seam: the paper's un-collapsed `RAP_walk` constraints ⟹ collapsed `WalkSat`

  The paper writes the count and accumulation constraints as explicit
  sums `∑_{s_j∈S} st(i,j)·(…)` over the one-hot state column `st`.  We mechanize that these
  imply the collapsed per-row `WalkSat` form via `sum_oneHot` (the one-hot collapse) and
  `fanout_leaf` (leaf-state summands vanish, so the paper's restriction to `S∖S_leaf` is a
  no-op). -/

section OneHotSeam
variable {K : Type*} [Field K] {numStates : ℕ}

/-- The paper's `RAP_walk` initial inputs & constraints in **un-collapsed** one-hot form: the count and accumulation constraints are explicit `st`-weighted sums
    over states, with the accumulation restricted to non-leaf states `S∖S_leaf`. -/
structure PaperWalkSat (cur : ℕ → K) (chld' : ℕ → ℕ → K)
    (st : ℕ → Fin numStates → K) (jrow : ℕ → Fin numStates)
    (fanoutFn : Fin numStates → ℕ) (Sleaf : Fin numStates → Prop) [DecidablePred Sleaf]
    (ln count acc : ℕ → K) (α seed initial_count : K) (h : ℕ) : Prop where
  hpos : 1 ≤ h
  ln1 : ln 1 = α
  lnInc : ∀ i, 1 ≤ i → i < h → ln (i + 1) = α * ln i
  count1 : count 1 = initial_count * (∑ j, st 1 j * α ^ (fanoutFn j))
  countInc : ∀ i, 1 ≤ i → i < h →
    count (i + 1) = count i * (∑ j, st (i + 1) j * α ^ (fanoutFn j))
  accInit : ln 1 * cur 1 + acc 1
    = (∑ j ∈ Finset.univ.filter (fun j => ¬ Sleaf j),
        st 1 j * (∑ l ∈ Finset.Icc 1 (fanoutFn j), α ^ l * initial_count * chld' 1 l)) + seed
  accStep : ∀ i, 1 ≤ i → i < h →
    ln (i + 1) * cur (i + 1) + acc (i + 1) - acc i
      = ∑ j ∈ Finset.univ.filter (fun j => ¬ Sleaf j),
          st (i + 1) j * (∑ l ∈ Finset.Icc 1 (fanoutFn j), α ^ l * count i * chld' (i + 1) l)

/-- **One-hot collapse of a state-restricted sum.**  With `st` one-hot and `fanout(s)=0` on
    leaf states, the paper's `∑_{s_j∈S∖S_leaf} st(i,j)·(∑_{l=1}^{fanout(j)} g j l)` collapses
    to the active state's summand `∑_{l=1}^{fanout(jrow i)} g (jrow i) l`. -/
theorem collapse_restricted_sum {st : ℕ → Fin numStates → K} {jrow : ℕ → Fin numStates}
    (hoh : OneHot st jrow) {fanoutFn : Fin numStates → ℕ} {Sleaf : Fin numStates → Prop}
    [DecidablePred Sleaf] (hfl : ∀ s, Sleaf s → fanoutFn s = 0)
    (i : ℕ) (g : Fin numStates → ℕ → K) :
    (∑ j ∈ Finset.univ.filter (fun j => ¬ Sleaf j),
        st i j * (∑ l ∈ Finset.Icc 1 (fanoutFn j), g j l))
      = ∑ l ∈ Finset.Icc 1 (fanoutFn (jrow i)), g (jrow i) l := by
  -- extend the filtered sum to all states (leaf terms have empty inner sum)
  have hext : (∑ j ∈ Finset.univ.filter (fun j => ¬ Sleaf j),
        st i j * (∑ l ∈ Finset.Icc 1 (fanoutFn j), g j l))
      = ∑ j, st i j * (∑ l ∈ Finset.Icc 1 (fanoutFn j), g j l) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hjns
    have hsj : Sleaf j := by
      by_contra hc
      exact hjns (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hc⟩)
    rw [hfl j hsj]; simp
  rw [hext]
  exact sum_oneHot hoh i (fun j => ∑ l ∈ Finset.Icc 1 (fanoutFn j), g j l)

/-- **THE ONE-HOT SEAM.**  The paper's un-collapsed `RAP_walk`
    constraints (with one-hot `st`) imply the collapsed `WalkSat` form, with `fanout(j(i)) =
    fanoutFn(jrow i)`.  The count/accumulation state-sums collapse by `sum_oneHot`; the
    accumulation's restriction to `S∖S_leaf` is a no-op because `fanout_leaf` empties the
    leaf-state inner sums. -/
theorem paperWalkSat_collapse {cur : ℕ → K} {chld' : ℕ → ℕ → K}
    {st : ℕ → Fin numStates → K} {jrow : ℕ → Fin numStates}
    {fanoutFn : Fin numStates → ℕ} {Sleaf : Fin numStates → Prop} [DecidablePred Sleaf]
    {ln count acc : ℕ → K} {α seed initial_count : K} {h : ℕ}
    (hoh : OneHot st jrow) (hfl : ∀ s, Sleaf s → fanoutFn s = 0)
    (P : PaperWalkSat cur chld' st jrow fanoutFn Sleaf ln count acc α seed initial_count h) :
    WalkSat cur chld' (fun i => fanoutFn (jrow i)) ln count acc α seed initial_count h := by
  refine
    { hpos := P.hpos, ln1 := P.ln1, lnInc := P.lnInc
      count1 := ?_, countInc := ?_, accInit := ?_, accStep := ?_ }
  · rw [P.count1, sum_oneHot hoh 1 (fun j => α ^ (fanoutFn j))]
  · intro i hi hih
    rw [P.countInc i hi hih, sum_oneHot hoh (i + 1) (fun j => α ^ (fanoutFn j))]
  · rw [P.accInit, collapse_restricted_sum hoh hfl 1
        (fun j l => α ^ l * initial_count * chld' 1 l)]
  · intro i hi hih
    rw [P.accStep i hi hih, collapse_restricted_sum hoh hfl (i + 1)
        (fun j l => α ^ l * count i * chld' (i + 1) l)]

end OneHotSeam

/-! ## §3.2 Composed soundness of `Thm:Walk_IOP`

  The packaged `Walk_IOP_RVT` carries completeness and the membership bridge; its third
  conjunct is the decoupled Schwartz–Zippel engine `walk_soundness_card`, not the composed
  `Pr[slt ∉ L_RVT | accepting table]`.  This section composes the full soundness of
  `Thm:Walk_IOP`.

  The construction commits to node/child *vectors* `∈ 𝔽^{node_size}` BEFORE the challenges
  `(α, γ)` are drawn; the walk columns are their random linear combinations
  `cur i = RLC^γ(V i)`, `chld' i l = RLC^γ(Cv i l)`.  The soundness bound is
    **`≤ h/|K| + ε_RLC`**,   `ε_RLC := h·(node_size − 1)/|K|`,
  where `h/|K|` is the α-challenge Schwartz–Zippel term (`walk_soundness_card`) and `ε_RLC` is
  the γ-challenge RLC-collision term: the accumulator identity is over `RLC^γ`-scalars, and
  concluding the underlying node-VECTORS are BFS-consistent from scalar-consistency can fail
  when `RLC^γ` collides two distinct committed vectors.  The stated `h/|K|` alone omits
  `ε_RLC`; the bound above includes it.  The three steps below are the reverse-BFT-iff (pure
  algebra), the scalar→vector RLC lift (where `ε_RLC` enters), and the `StateSep` fanout
  binding, composed at the end.
-/

/-! ### Reverse BFT-iff at the RLC-scalar level

  The forward direction is `bfs_isFullBFT` (real tree ⟹ `IsFullBFT`).  Here we prove
  the reverse at the value/scalar level: `IsFullBFT cur chld' fo h` (with the `h`-node fanout
  structure `Sf fo h + 1 = h`) ⟹ the `cur` value column is the BFS reindex of the `chld'`
  value column, i.e. `[cur 1, …, cur h] = cur 1 :: (flattened children)`.  This is the algebra
  the paper calls "self-evident". -/

section ReverseBridge
variable {K : Type*} [Field K]

/-- Coefficient of `lpoly e l` at exponent `e + j` is `l.getD j 0` (`0` past the end). -/
theorem lpoly_coeff_add (e : ℕ) (l : List K) (j : ℕ) :
    (lpoly e l).coeff (e + j) = l.getD j 0 := by
  rw [lpoly_eq_sum, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single j
    (fun i _ hij => by rw [if_neg (by omega : e + j ≠ e + i), mul_zero])
    (fun hj => by
      have hlen : l.length ≤ j := by simpa using hj
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]; simp)]
  rw [if_pos rfl, mul_one]

/-- `lpoly` is injective on equal-length coefficient lists. -/
theorem lpoly_inj (e : ℕ) {l₁ l₂ : List K} (hlen : l₁.length = l₂.length)
    (h : lpoly e l₁ = lpoly e l₂) : l₁ = l₂ := by
  apply List.ext_getElem hlen
  intro j hj hj2
  have hc := congrArg (fun q => Polynomial.coeff q (e + j)) h
  rw [lpoly_coeff_add, lpoly_coeff_add] at hc
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem hj2, Option.getD_some, Option.getD_some] at hc
  exact hc

/-- Value list of the `cur` column over rows `1..h`. -/
def curVals (cur : ℕ → K) (h : ℕ) : List K := (List.range h).map (fun i => cur (i + 1))

/-- Children value block of row `i` (slots `1..fo i`). -/
def blkVals (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (i : ℕ) : List K :=
  (List.range (fo i)).map (fun l => chld' i (l + 1))

/-- Flattened children values of rows `1..k` (the BFS queue tail after `k` steps). -/
def flatBlks (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (k : ℕ) : List K :=
  (List.range k).flatMap (fun i => blkVals chld' fo (i + 1))

@[simp] theorem curVals_length (cur : ℕ → K) (h : ℕ) : (curVals cur h).length = h := by
  simp [curVals]

@[simp] theorem blkVals_length (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (i : ℕ) :
    (blkVals chld' fo i).length = fo i := by simp [blkVals]

theorem flatBlks_succ (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (k : ℕ) :
    flatBlks chld' fo (k + 1) = flatBlks chld' fo k ++ blkVals chld' fo (k + 1) := by
  unfold flatBlks; rw [List.range_succ, List.flatMap_append]; simp

@[simp] theorem flatBlks_length (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (k : ℕ) :
    (flatBlks chld' fo k).length = Sf fo k := by
  induction k with
  | zero => simp [flatBlks, Sf]
  | succ m ih => rw [flatBlks_succ, List.length_append, ih, blkVals_length, Sf_succ]

/-- **`node_list` as a value-list polynomial (generic).** -/
theorem nodeListP_eq_lpoly_gen (cur : ℕ → K) (h : ℕ) :
    nodeListP cur h = lpoly 1 (curVals cur h) := by
  unfold nodeListP
  rw [sum_Icc_one_eq_range, lpoly_eq_sum, curVals_length]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have : (curVals cur h).getD i 0 = cur (i + 1) := by
    rw [curVals, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (Finset.mem_range.mp hi)]; rfl
  rw [this]; congr 2; omega

/-- The queue accumulation contribution of row `i+1` is the `lpoly` of that row's children
    block placed after the `Sf`-many already-queued children (generic). -/
theorem queueTerm_eq_lpoly_gen (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (i : ℕ) :
    queueTerm chld' fo (i + 1) = lpoly (2 + Sf fo i) (blkVals chld' fo (i + 1)) := by
  unfold queueTerm
  rw [Nat.add_sub_cancel, lpoly_eq_sum, blkVals_length, sum_Icc_one_eq_range]
  refine Finset.sum_congr rfl (fun l hl => ?_)
  have : (blkVals chld' fo (i + 1)).getD l 0 = chld' (i + 1) (l + 1) := by
    rw [blkVals, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (Finset.mem_range.mp hl)]; rfl
  rw [this]; congr 2; omega

/-- The queue accumulation over rows `1..k` is the `lpoly` of the flattened children (generic). -/
theorem queueSum_eq_gen (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (k : ℕ) :
    ∑ i ∈ Finset.Icc 1 k, queueTerm chld' fo i = lpoly 2 (flatBlks chld' fo k) := by
  induction k with
  | zero => simp [flatBlks]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ m + 1), ih, queueTerm_eq_lpoly_gen,
      flatBlks_succ, lpoly_append, flatBlks_length]

/-- **`node_queue` as `RLC(root)·X` plus the flattened-children `lpoly` (generic).** -/
theorem nodeQueueP_eq_gen (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (h : ℕ) :
    nodeQueueP cur chld' fo h = C (cur 1) * X + lpoly 2 (flatBlks chld' fo h) := by
  unfold nodeQueueP; rw [queueSum_eq_gen]

/-- **REVERSE BFT-iff.**  If the arithmetized full-BFT identity
    `IsFullBFT cur chld' fo h` holds and the fanout column has the `h`-node tree structure
    (`Sf fo h + 1 = h`, i.e. every non-root node is exactly one child), then the `cur` value
    column is the BFS reindex of the `chld'` column: `[cur 1, …, cur h]` equals `cur 1`
    prepended to the flattened children of all rows.  Reverse of `bfs_isFullBFT`, at the
    RLC-scalar level, via `lpoly` injectivity. -/
theorem isFullBFT_curVals {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {h : ℕ}
    (hlen : Sf fo h + 1 = h) (hbft : IsFullBFT cur chld' fo h) :
    curVals cur h = cur 1 :: flatBlks chld' fo h := by
  apply lpoly_inj 1
  · rw [curVals_length, List.length_cons, flatBlks_length]; omega
  · rw [← nodeListP_eq_lpoly_gen, lpoly_cons, pow_one, ← nodeQueueP_eq_gen]
    exact hbft

end ReverseBridge

/-! ### The scalar → vector RLC lift

  `RLC^γ` maps a node vector `v ∈ 𝔽^{node_size}` to the scalar `Σ_c γ^c v(c)`.  The
  reverse-BFT-iff (Step 1) is an identity over these SCALARS; to conclude the underlying
  committed VECTORS are BFS-consistent we need `RLC^γ` to be injective on the committed
  vectors.  It is — except when the random `γ` is a root of the (nonzero, degree `< node_size`)
  difference polynomial `RLC^γ(u) − RLC^γ(v)` for a distinct pair.  Union-bounding over the
  `≤ h` node-positions gives the RLC-collision error `ε_RLC = h·(node_size − 1)/|K|`. -/

section RLCInjectivity
variable {K : Type*} [Field K] {node_size : ℕ}

/-- `RLC^γ(v)` as a polynomial in the challenge `γ`: `Σ_c v(c)·X^c` (`natDegree < node_size`). -/
noncomputable def rlcP (v : Fin node_size → K) : K[X] :=
  ∑ c : Fin node_size, C (v c) * X ^ (c : ℕ)

/-- `RLC^γ(v) = (rlcP v).eval γ`: the RLC is `rlcP` evaluated at the challenge. -/
theorem rlc_eq_rlcP_eval (γ : K) (v : Fin node_size → K) : rlc γ v = (rlcP v).eval γ := by
  unfold rlc rlcP
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]

theorem rlcP_natDegree_le (v : Fin node_size → K) : (rlcP v).natDegree ≤ node_size - 1 := by
  unfold rlcP
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro c _
  refine le_trans (natDegree_C_mul_le _ _) ?_
  rw [natDegree_X_pow]; omega

/-- The coefficient of `rlcP v` at index `c < node_size` is `v c`. -/
theorem rlcP_coeff (v : Fin node_size → K) (c : Fin node_size) : (rlcP v).coeff (c : ℕ) = v c := by
  unfold rlcP
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single c
    (fun b _ hbc => by rw [if_neg (fun heq => hbc (Fin.ext heq.symm)), mul_zero])
    (fun hcon => absurd (Finset.mem_univ c) hcon)]
  rw [if_pos rfl, mul_one]

/-- Distinct vectors have distinct RLC difference polynomials. -/
theorem rlcP_sub_ne_zero {u v : Fin node_size → K} (h : u ≠ v) : rlcP u - rlcP v ≠ 0 := by
  obtain ⟨c, hc⟩ := Function.ne_iff.mp h
  intro hzero
  have hcoe : (rlcP u - rlcP v).coeff (c : ℕ) = u c - v c := by
    rw [coeff_sub, rlcP_coeff, rlcP_coeff]
  rw [hzero, coeff_zero] at hcoe
  exact hc (sub_eq_zero.mp hcoe.symm)

variable [Fintype K] [DecidableEq K]

/-- **Single-pair RLC-collision bound.**  Two distinct committed vectors have equal RLC for at
    most `node_size − 1` challenges `γ ∈ K` (roots of a nonzero degree-`< node_size` polynomial;
    univariate Schwartz–Zippel). -/
theorem rlc_collision_card_le {u v : Fin node_size → K} (h : u ≠ v) :
    (Finset.univ.filter (fun γ : K => rlc γ u = rlc γ v)).card ≤ node_size - 1 := by
  have hne := rlcP_sub_ne_zero h
  have hset : (Finset.univ.filter (fun γ : K => rlc γ u = rlc γ v))
      = Finset.univ.filter (fun γ : K => (rlcP u - rlcP v).eval γ = 0) := by
    ext γ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_sub, sub_eq_zero,
      rlc_eq_rlcP_eval]
  rw [hset]
  refine le_trans (card_roots_le _ hne) ?_
  refine le_trans (natDegree_sub_le _ _) ?_
  rw [max_le_iff]
  exact ⟨rlcP_natDegree_le u, rlcP_natDegree_le v⟩

/-- The **bad-γ set** for two vector lists: some position (below both lengths) where the
    vectors differ yet their RLCs coincide.  On its complement, scalar RLC-equality lifts to
    genuine vector equality. -/
noncomputable def BadRLCList (L₁ L₂ : List (Fin node_size → K)) : Finset K :=
  Finset.univ.filter (fun γ : K => ∃ i ∈ Finset.range (min L₁.length L₂.length),
    L₁.getD i 0 ≠ L₂.getD i 0 ∧ rlc γ (L₁.getD i 0) = rlc γ (L₂.getD i 0))

/-- **`ε_RLC` cardinality bound.**  The bad-γ set for two vector lists has size
    `≤ (min |L₁| |L₂|)·(node_size − 1)`; union bound over the positions, each a single-pair
    collision (`rlc_collision_card_le`). -/
theorem badRLCList_card_le (L₁ L₂ : List (Fin node_size → K)) :
    (BadRLCList L₁ L₂).card ≤ (min L₁.length L₂.length) * (node_size - 1) := by
  classical
  set m := min L₁.length L₂.length with hm
  set g : ℕ → Finset K := fun i =>
    Finset.univ.filter (fun γ : K => L₁.getD i 0 ≠ L₂.getD i 0 ∧
      rlc γ (L₁.getD i 0) = rlc γ (L₂.getD i 0)) with hg
  have hsub : BadRLCList L₁ L₂ ⊆ (Finset.range m).biUnion g := by
    intro γ hγ
    simp only [BadRLCList, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    obtain ⟨i, hi, hne, heq⟩ := hγ
    exact Finset.mem_biUnion.mpr ⟨i, hi, by
      simp only [hg, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hne, heq⟩⟩
  have hcard : ∀ i ∈ Finset.range m, (g i).card ≤ node_size - 1 := by
    intro i _
    by_cases hd : L₁.getD i 0 = L₂.getD i 0
    · have : g i = ∅ := by
        simp only [hg, Finset.filter_eq_empty_iff]
        intro γ _; rintro ⟨hne, _⟩; exact hne hd
      rw [this]; simp
    · refine le_trans (Finset.card_le_card ?_) (rlc_collision_card_le hd)
      intro γ hγ
      simp only [hg, Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
      exact hγ.2
  calc (BadRLCList L₁ L₂).card ≤ ((Finset.range m).biUnion g).card := Finset.card_le_card hsub
    _ ≤ ∑ _i ∈ Finset.range m, (node_size - 1) :=
        le_trans Finset.card_biUnion_le (Finset.sum_le_sum hcard)
    _ = m * (node_size - 1) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **The RLC lift (Step 2 conclusion).**  For a challenge `γ` NOT in the bad set, two
    equal-length vector lists whose RLC-images coincide are themselves equal. -/
theorem rlc_lift_list {L₁ L₂ : List (Fin node_size → K)} {γ : K}
    (hlen : L₁.length = L₂.length) (hγ : γ ∉ BadRLCList L₁ L₂)
    (hrlc : L₁.map (rlc γ) = L₂.map (rlc γ)) : L₁ = L₂ := by
  apply List.ext_getElem hlen
  intro i hi hi2
  have e1 : L₁.getD i 0 = L₁[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have e2 : L₂.getD i 0 = L₂[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2, Option.getD_some]
  have hval : rlc γ (L₁.getD i 0) = rlc γ (L₂.getD i 0) := by
    have h1 : (L₁.map (rlc γ)).getD i (rlc γ (0 : Fin node_size → K))
        = (L₂.map (rlc γ)).getD i (rlc γ (0 : Fin node_size → K)) := by rw [hrlc]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi2] at h1
    simp only [Option.map_some, Option.getD_some] at h1
    rw [e1, e2]; exact h1
  by_contra hne
  apply hγ
  simp only [BadRLCList, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨i, Finset.mem_range.mpr (by rw [hlen, min_self]; exact hi2), ?_, hval⟩
  rw [e1, e2]; exact hne

end RLCInjectivity

/-! ### Vector-column bridges: committed vectors vs. their RLC value lists -/

section VecColumns
variable {K : Type*} [Field K] {node_size : ℕ}

/-- The committed node-vectors of rows `1..h` (the objects `RLC^γ` is applied to). -/
def curValsV (V : ℕ → Fin node_size → K) (h : ℕ) : List (Fin node_size → K) :=
  (List.range h).map (fun i => V (i + 1))

/-- The committed children-vectors block of row `i`. -/
def blkValsV (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) (i : ℕ) : List (Fin node_size → K) :=
  (List.range (fo i)).map (fun l => Cv i (l + 1))

/-- The flattened committed children-vectors of rows `1..k`. -/
def flatBlksV (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) (k : ℕ) : List (Fin node_size → K) :=
  (List.range k).flatMap (fun i => blkValsV Cv fo (i + 1))

@[simp] theorem curValsV_length (V : ℕ → Fin node_size → K) (h : ℕ) :
    (curValsV V h).length = h := by simp [curValsV]

theorem flatBlksV_succ (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) (k : ℕ) :
    flatBlksV Cv fo (k + 1) = flatBlksV Cv fo k ++ blkValsV Cv fo (k + 1) := by
  unfold flatBlksV; rw [List.range_succ, List.flatMap_append]; simp

@[simp] theorem flatBlksV_length (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) (k : ℕ) :
    (flatBlksV Cv fo k).length = Sf fo k := by
  induction k with
  | zero => simp [flatBlksV, Sf]
  | succ m ih =>
    rw [flatBlksV_succ, List.length_append, ih, blkValsV, List.length_map, List.length_range,
      Sf_succ]

/-- The `cur` column is the `RLC^γ`-image of the committed node-vector list. -/
theorem curVals_rlc (γ : K) (V : ℕ → Fin node_size → K) (h : ℕ) :
    curVals (fun i => rlc γ (V i)) h = (curValsV V h).map (rlc γ) := by
  simp only [curVals, curValsV, List.map_map]; rfl

theorem blkVals_rlc (γ : K) (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) (i : ℕ) :
    blkVals (fun i l => rlc γ (Cv i l)) fo i = (blkValsV Cv fo i).map (rlc γ) := by
  simp only [blkVals, blkValsV, List.map_map]; rfl

/-- The `chld'` column's flattened blocks are the `RLC^γ`-image of the committed
    children-vector list. -/
theorem flatBlks_rlc (γ : K) (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) (k : ℕ) :
    flatBlks (fun i l => rlc γ (Cv i l)) fo k = (flatBlksV Cv fo k).map (rlc γ) := by
  induction k with
  | zero => simp [flatBlks, flatBlksV]
  | succ m ih => rw [flatBlks_succ, flatBlksV_succ, List.map_append, ih, blkVals_rlc]

end VecColumns

/-! ### `StateSep` fanout binding

  The paper REQUIRES state-data-separation: the fanout column cannot lie about the number of
  children.  Using `walk_childLabel_iff_fanout` (via `StateSep.dynamic`), for a genuine `rvt`
  node the arithmetized `fanout(j(i))` is FORCED to equal the real child count. -/

section StateSepBinding
variable {S DT : Type*} {n : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}

/-- A child slot is non-`⊥` iff its index is below the real child count. -/
theorem childLabel_ne_none_iff (t : NTree (S × DT)) (i : Fin n) :
    t.childLabel i ≠ none ↔ (i : ℕ) < t.children.length := by
  simp only [NTree.childLabel, NTree.childOpt, ne_eq, Option.map_eq_none_iff,
    List.getElem?_eq_none_iff, not_le]

/-- **Fanout binding.**  For an `rvt` node whose child count respects the arity
    `n` (a proper `n`-ary tree), `StateSep` forces the state's `fanout` to equal the real child
    count.  A cheating prover therefore cannot misreport the fanout column. -/
theorem fanout_eq_children_length (St : StateSep F) {root t : NTree (S × DT)}
    (hroot : RVT F root) (ht : InTree root t) (hproper : t.children.length ≤ n) :
    St.fanout (NTree.label t).1 = t.children.length := by
  have key : ∀ m : ℕ, m < n →
      (m < St.fanout (NTree.label t).1 ↔ m < t.children.length) := by
    intro m hm
    have hc := walk_childLabel_iff_fanout St hroot ht ⟨m, hm⟩
    rw [hc, childLabel_ne_none_iff]
  have hfle := St.fanout_le (NTree.label t).1
  rcases Nat.lt_trichotomy (St.fanout (NTree.label t).1) t.children.length with hlt | heq | hgt
  · exact absurd ((key _ (by omega)).mpr hlt) (lt_irrefl _)
  · exact heq
  · exact absurd ((key _ (by omega)).mp hgt) (lt_irrefl _)

/-- **Tree-wide fanout binding over `L_SLT^n` — the FAITHFUL statement.**  For
    an `RVT F` tree that is a genuine `n`-ary tree (`ProperArity n`), `StateSep` forces the state's
    `fanout` to equal the real child count at EVERY node.  This is exactly the `L_SLT^n` content
    that `{t // RVT F t ∧ ProperArity n t}` carries and that
    `{t // RVT F t}` alone LACKS: without `ProperArity`, a node may carry extra children beyond the
    arity `n` (each itself `RVT`), so `RVT F` is strictly weaker than membership in `L_RVT^{F,n}`. -/
theorem fanout_eq_children_length_of_properArity (St : StateSep F) {root : NTree (S × DT)}
    (hroot : RVT F root) (hproper : ProperArity n root) :
    ∀ t, InTree root t → St.fanout (NTree.label t).1 = t.children.length :=
  fun t ht => fanout_eq_children_length St hroot ht (hproper t ht)

end StateSepBinding

/-! ### Composition: the soundness of `Thm:Walk_IOP`

  We compose Steps 1–3 into the soundness bound.  The committed data are node vectors
  `V : ℕ → 𝔽^{node_size}` and children vectors `Cv`; the challenges `(α, γ) ∈ K × K` are drawn
  AFTER the commitment.  Acceptance means `∃` line/count/accumulator columns satisfying the
  `RAP_walk` gates (`WalkSat`) on the RLC-reduced columns `cur = RLC^γ(V)`, `chld' = RLC^γ(Cv)`,
  with recognizer inputs `(RLC^γ(V 1)·α, α)` and `out_walk = acc(h) = 0`.

  The soundness bound is `≤ h/|K| + ε_RLC`, `ε_RLC := h·(node_size − 1)/|K|`. -/

section Compose
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

variable {node_size : ℕ}

/-- The **vector breadth-first-traversal fixpoint** of the committed data: the node-vectors of
    rows `1..h` equal the root vector prepended to the flattened committed children-vectors.
    This is the genuine (vector-level) encoding of a full BFT, and the
    conclusion of the soundness bound.  It is `α`- and `γ`-independent (a property of the committed vectors). -/
def VecBFT (V : ℕ → Fin node_size → K) (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ)
    (h : ℕ) : Prop :=
  curValsV V h = V 1 :: flatBlksV Cv fo h

/-- **Soundness of `Thm:Walk_IOP`, cardinality form.**
    For committed node/children vectors `V, Cv` and a fanout column `fo` with the `h`-node tree
    structure (`Sf fo h + 1 = h`), the number of challenge pairs `(α, γ) ∈ K × K` for which the
    `RAP_walk` gates accept (`out_walk = 0`) YET the committed vectors do NOT form a genuine
    vector-BFT (`¬ VecBFT`) is
      `≤ |K|·h + |K|·(h·(node_size − 1))`,
    i.e. the failure probability over uniform `(α, γ)` is `≤ h/|K| + ε_RLC` with
    `ε_RLC = h·(node_size − 1)/|K|`.

    Composition: acceptance reduces (`walk_out_zero_iff`) to `node_list(α) = node_queue_h(α)`.
    Either the polynomial identity `IsFullBFT` fails for the drawn `γ` — then acceptance pins
    `α` to `≤ h` values (`walk_soundness_card`, the paper's `h/|K|`); or it holds — then the
    reverse-BFT-iff (`isFullBFT_curVals`) plus the RLC lift (`rlc_lift_list`) yield `VecBFT`
    UNLESS `γ` lies in the RLC-collision set (`badRLCList_card_le`, the `ε_RLC` term). -/
theorem walk_IOP_soundness_card
    (V : ℕ → Fin node_size → K) (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) {h : ℕ}
    (hlen : Sf fo h + 1 = h) :
    (Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (V i)) (fun i l => rlc p.2 (Cv i l)) fo ln count acc
            p.1 (rlc p.2 (V 1) * p.1) p.1 h ∧ acc h = 0)
        ∧ ¬ VecBFT V Cv fo h)).card
      ≤ Fintype.card K * h + Fintype.card K * (h * (node_size - 1)) := by
  set L₁ := curValsV V h with hL₁
  set L₂ := (V 1 :: flatBlksV Cv fo h) with hL₂
  -- named predicates (identical lambda everywhere avoids `DecidablePred`-instance mismatch)
  set P1 : K → K → Prop := fun α γ =>
    ¬ IsFullBFT (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo h ∧
      (nodeListP (fun i => rlc γ (V i)) h).eval α
        = (nodeQueueP (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo h).eval α
    with hP1
  set P2 : K → K → Prop := fun _α γ => γ ∈ BadRLCList L₁ L₂ with hP2
  -- STEP: the bad set is contained in the two overapproximating filters
  have hsub : (Finset.univ.filter (fun p : K × K =>
      (∃ ln count acc : ℕ → K,
        WalkSat (fun i => rlc p.2 (V i)) (fun i l => rlc p.2 (Cv i l)) fo ln count acc
          p.1 (rlc p.2 (V 1) * p.1) p.1 h ∧ acc h = 0)
      ∧ ¬ VecBFT V Cv fo h))
      ⊆ Finset.univ.filter (fun p : K × K => P1 p.1 p.2)
        ∪ Finset.univ.filter (fun p : K × K => P2 p.1 p.2) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨⟨ln, count, acc, hw, hacc0⟩, hnotfix⟩ := hp.2
    -- acceptance ⟹ node_list(α) = node_queue_h(α)
    have heval := (walk_out_zero_iff hw rfl rfl).mp hacc0
    rw [Finset.mem_union]
    by_cases hbft : IsFullBFT (fun i => rlc p.2 (V i)) (fun i l => rlc p.2 (Cv i l)) fo h
    · -- IsFullBFT holds ⟹ γ ∈ BadRLCList (else VecBFT, contradiction)
      right
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show p.2 ∈ BadRLCList L₁ L₂
      by_contra hγ
      -- scalar fixpoint from Step 1, lifted to vectors by Step 2
      have hscalar := isFullBFT_curVals hlen hbft
      rw [curVals_rlc, flatBlks_rlc] at hscalar
      have hmap : L₁.map (rlc p.2) = L₂.map (rlc p.2) := by
        rw [hL₁, hL₂, List.map_cons]; exact hscalar
      have hlen12 : L₁.length = L₂.length := by
        rw [hL₁, hL₂, curValsV_length, List.length_cons, flatBlksV_length]; omega
      apply hnotfix
      show curValsV V h = V 1 :: flatBlksV Cv fo h
      rw [← hL₁, ← hL₂]
      exact rlc_lift_list hlen12 hγ hmap
    ·
      left
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hbft, heval⟩
  -- STEP: bound the two filters (α-fibers ≤ h by Schwartz–Zippel; γ-fibers = the ε_RLC set)
  have hb1 : (Finset.univ.filter (fun p : K × K => P1 p.1 p.2)).card ≤ Fintype.card K * h := by
    refine le_trans (Finset.card_le_card (?_ : _ ⊆ Finset.univ.biUnion
        (fun γ : K => (Finset.univ.filter (fun α : K => P1 α γ)).image (fun α => (α, γ))))) ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_biUnion.mpr ⟨p.2, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩, rfl⟩⟩
    · refine le_trans Finset.card_biUnion_le ?_
      refine le_trans (Finset.sum_le_sum (fun γ _ => Finset.card_image_le)) ?_
      refine le_trans (Finset.sum_le_sum (g := fun _ => h) (fun γ (_ : γ ∈ Finset.univ) => ?_)) ?_
      · simp only [hP1]
        by_cases hbft : IsFullBFT (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo h
        · have hemp : (Finset.univ.filter (fun α : K =>
              ¬ IsFullBFT (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo h ∧
                (nodeListP (fun i => rlc γ (V i)) h).eval α
                  = (nodeQueueP (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo h).eval α))
              = ∅ := by
            rw [Finset.filter_eq_empty_iff]; intro α _; rintro ⟨hn, _⟩; exact hn hbft
          rw [hemp]; simp
        · refine le_trans (Finset.card_le_card ?_) (walk_soundness_card hbft (by omega))
          intro α hα
          rw [Finset.mem_filter] at hα ⊢
          exact ⟨hα.1, hα.2.2⟩
      · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hb2 : (Finset.univ.filter (fun p : K × K => P2 p.1 p.2)).card
      ≤ Fintype.card K * (h * (node_size - 1)) := by
    refine le_trans (Finset.card_le_card (?_ : _ ⊆ Finset.univ.biUnion
        (fun α : K => (Finset.univ.filter (fun γ : K => P2 α γ)).image (fun γ => (α, γ))))) ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨p.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩, rfl⟩⟩
    · refine le_trans Finset.card_biUnion_le ?_
      refine le_trans (Finset.sum_le_sum (fun α _ => Finset.card_image_le)) ?_
      refine le_trans (Finset.sum_le_sum (g := fun _ => h * (node_size - 1)) (fun α (_ : α ∈ Finset.univ) => ?_)) ?_
      · simp only [hP2]
        have hset : (Finset.univ.filter (fun γ : K => γ ∈ BadRLCList L₁ L₂))
            = BadRLCList L₁ L₂ := by ext γ; simp
        rw [hset]
        have hmin : min L₁.length L₂.length = h := by
          rw [hL₁, hL₂, curValsV_length, List.length_cons, flatBlksV_length]; omega
        calc (BadRLCList L₁ L₂).card ≤ (min L₁.length L₂.length) * (node_size - 1) :=
              badRLCList_card_le L₁ L₂
          _ = h * (node_size - 1) := by rw [hmin]
      · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  calc _ ≤ (Finset.univ.filter (fun p : K × K => P1 p.1 p.2)
              ∪ Finset.univ.filter (fun p : K × K => P2 p.1 p.2)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun p : K × K => P1 p.1 p.2)).card
          + (Finset.univ.filter (fun p : K × K => P2 p.1 p.2)).card := Finset.card_union_le _ _
    _ ≤ Fintype.card K * h + Fintype.card K * (h * (node_size - 1)) := Nat.add_le_add hb1 hb2

/-- **Soundness of `Thm:Walk_IOP`, probability form.**
    Over uniformly random verifier challenges `(α, γ) ∈ K × K` (counting measure), the
    probability that the `RAP_walk` gates accept (`out_walk = 0`) while the committed vectors do
    NOT form a genuine vector-BFT is bounded by
      `≤ h/|K| + ε_RLC`,   `ε_RLC = h·(node_size − 1)/|K|`.
    The paper states only `h/|K|` and omits `ε_RLC`.  The `h/|K|` summand is the α-challenge
    Schwartz–Zippel term; `ε_RLC` is the γ-challenge RLC-collision term. -/
theorem walk_IOP_soundness_prob
    (V : ℕ → Fin node_size → K) (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) {h : ℕ}
    (hlen : Sf fo h + 1 = h) :
    ((Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (V i)) (fun i l => rlc p.2 (Cv i l)) fo ln count acc
            p.1 (rlc p.2 (V 1) * p.1) p.1 h ∧ acc h = 0)
        ∧ ¬ VecBFT V Cv fo h)).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (h : ℚ) / (Fintype.card K : ℚ)
          + ((h * (node_size - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  set m : ℕ := h * (node_size - 1) with hm
  have hpos : (0 : ℚ) < (Fintype.card K : ℚ) := by
    haveI : Nonempty K := ⟨0⟩; exact_mod_cast Fintype.card_pos
  have hK : (Fintype.card K : ℚ) ≠ 0 := ne_of_gt hpos
  have hpos2 : (0 : ℚ) < (Fintype.card K : ℚ) * (Fintype.card K : ℚ) := by positivity
  have hcard : ((Finset.univ.filter (fun p : K × K =>
      (∃ ln count acc : ℕ → K,
        WalkSat (fun i => rlc p.2 (V i)) (fun i l => rlc p.2 (Cv i l)) fo ln count acc
          p.1 (rlc p.2 (V 1) * p.1) p.1 h ∧ acc h = 0)
      ∧ ¬ VecBFT V Cv fo h)).card : ℚ)
      ≤ (Fintype.card K : ℚ) * h + (Fintype.card K : ℚ) * m := by
    exact_mod_cast walk_IOP_soundness_card V Cv fo hlen
  rw [div_le_iff₀ hpos2]
  refine le_trans hcard (le_of_eq ?_)
  field_simp

end Compose

/-! ## §3.2 Deterministic inverse-BFS reconstruction

  The composed soundness bound concludes at `VecBFT` (the committed node-VECTORS form a BFS
  layout).  This section closes the LITERAL `Thm:Walk_IOP` conclusion `slt ∈ L_RVT^{F,n}` by
  the paper's "self-evident" step: given a full breadth-first-traversal layout
  (a fanout column `fo` with `Sf fo h + 1 = h`, plus queue-validity), there is a UNIQUE tree
  `slt` whose level-order flatten `bfsForest [slt]` reproduces the committed node list.  This
  is a purely combinatorial, probability-free, axiom-free un-flattening — the deterministic
  inverse of the `bfsForest`/`flatBlks` machinery.

  We then lift `slt` to `L_RVT^{F,n}` via the membership bridge `RVT_iff_walk_Fcon`, the
  `StateSep` hypothesis (`walk_leaf_iff_Sleaf` / `walk_childLabel_iff_fanout` /
  `fanout_eq_children_length`), and compose with `walk_IOP_soundness_card` for the
  `≤ h/|K| + ε_RLC` bound. -/

section Reconstruct
variable {LT : Type*}

/-- First (1-indexed) BFS position of node `i`'s children: `2 + Σ_{m<i} fanout(j(m))`
    (root at 1, then the flattened children in BFS order). -/
def firstC (fo : ℕ → ℕ) (i : ℕ) : ℕ := 2 + Sf fo (i - 1)

theorem firstC_one (fo : ℕ → ℕ) : firstC fo 1 = 2 := by simp [firstC, Sf]

/-- **Contiguous tiling of child ranges.**  Node `i`'s children occupy `[firstC i, firstC i +
    fanout(i))`, and node `i+1`'s children start right where node `i`'s end. -/
theorem firstC_succ (fo : ℕ → ℕ) {i : ℕ} (hi : 1 ≤ i) :
    firstC fo (i + 1) = firstC fo i + fo i := by
  have hj : i - 1 + 1 = i := by omega
  have h2 : Sf fo i = Sf fo (i - 1) + fo i := by
    conv_lhs => rw [← hj]
    rw [Sf_succ, hj]
  unfold firstC
  rw [Nat.add_sub_cancel]
  omega

/-- **Queue-validity of a fanout column.**  Node `i` (for `1 ≤ i ≤ h`) has already been queued
    by the time nodes `1..i-1` are processed, i.e. `i ≤ 1 + Σ_{m<i}fanout(j(m))`.  Equivalent
    to `firstC fo i > i` (children are strictly later in BFS order) — the acyclicity condition
    making the BFS layout a genuine finite tree. -/
def BFSValid (fo : ℕ → ℕ) (h : ℕ) : Prop := ∀ i, 1 ≤ i → i ≤ h → i ≤ 1 + Sf fo (i - 1)

/-- The child indices of node `i`, filtered to the strictly-later, in-range positions (the
    filter makes `buildT` well-founded unconditionally; under `BFSValid` it is a no-op). -/
def childIdxs (fo : ℕ → ℕ) (h i : ℕ) : List ℕ :=
  (List.range' (firstC fo i) (fo i)).filter (fun j => decide (i < j ∧ j ≤ h))

/-- **The reconstructed subtree rooted at BFS-position `i`.**  Deterministic un-flattening
    driven by `fo`: node `i` carries label `lbl i` and its children are the subtrees at the
    contiguous later positions `[firstC i, firstC i + fanout(i))`. -/
def buildT (fo : ℕ → ℕ) (lbl : ℕ → LT) (h : ℕ) : ℕ → NTree LT := fun i =>
  NTree.node (lbl i) ((childIdxs fo h i).attach.map (fun j => buildT fo lbl h j.1))
termination_by i => h - i
decreasing_by
  · have hj := j.2
    simp only [childIdxs, List.mem_filter, decide_eq_true_eq] at hj
    omega

@[simp] theorem buildT_label (fo : ℕ → ℕ) (lbl : ℕ → LT) (h i : ℕ) :
    (buildT fo lbl h i).label = lbl i := by
  rw [buildT, NTree.label_node]

theorem buildT_children (fo : ℕ → ℕ) (lbl : ℕ → LT) (h i : ℕ) :
    (buildT fo lbl h i).children = (childIdxs fo h i).map (buildT fo lbl h) := by
  rw [buildT, NTree.children_node, List.attach_map_val]

/-- Under `BFSValid` and `1 ≤ i ≤ h`, the child-index filter is a no-op: node `i`'s children
    are exactly the contiguous range `[firstC i, firstC i + fanout(i))`. -/
theorem childIdxs_eq (fo : ℕ → ℕ) (h : ℕ) (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h)
    {i : ℕ} (hi1 : 1 ≤ i) (hih : i ≤ h) :
    childIdxs fo h i = List.range' (firstC fo i) (fo i) := by
  unfold childIdxs
  rw [List.filter_eq_self]
  intro j hj
  rw [List.mem_range'] at hj
  obtain ⟨k, hk, hjk⟩ := hj
  have hval := hvalid i hi1 hih
  have hfc : firstC fo i = 2 + Sf fo (i - 1) := rfl
  have hsfi : Sf fo i = Sf fo (i - 1) + fo i := by
    have hj' : i - 1 + 1 = i := by omega
    conv_lhs => rw [← hj']
    rw [Sf_succ, hj']
  have hmono : Sf fo i ≤ Sf fo h := Sf_mono fo hih
  rw [decide_eq_true_eq]
  omega

/-- Helper: single-step `range'` append (step 1). -/
theorem range'_append_one (s m n : ℕ) :
    List.range' s m ++ List.range' (s + m) n = List.range' s (m + n) := by
  have h1 := @List.range'_append s m n 1
  simp only [Nat.one_mul] at h1
  exact h1

/-- **Contiguous tiling of the children blocks.**  Flattening the child ranges of a contiguous
    block of nodes `[a, a+len)` yields the single contiguous range of all their children. -/
theorem tiling (fo : ℕ → ℕ) :
    ∀ (len a : ℕ), 1 ≤ a →
      (List.range' a len).flatMap (fun i => List.range' (firstC fo i) (fo i))
        = List.range' (firstC fo a) (firstC fo (a + len) - firstC fo a) := by
  intro len
  induction len with
  | zero => intro a _; simp
  | succ m ih =>
    intro a ha
    rw [List.range'_succ, List.flatMap_cons, ih (a + 1) (by omega),
      firstC_succ fo ha, range'_append_one]
    have haeq : a + 1 + m = a + (m + 1) := by omega
    rw [haeq]
    have hle : firstC fo a + fo a ≤ firstC fo (a + (m + 1)) := by
      rw [← firstC_succ fo ha]
      unfold firstC
      have : Sf fo (a + 1 - 1) ≤ Sf fo (a + (m + 1) - 1) := Sf_mono fo (by omega)
      omega
    have hlen_eq :
        fo a + (firstC fo (a + (m + 1)) - (firstC fo a + fo a))
          = firstC fo (a + (m + 1)) - firstC fo a := by omega
    rw [hlen_eq]

/-- **Round-trip invariant (inverse-BFS).**  For a queue-consistent frontier starting at `a`
    (of length `firstC a − a`), the level-order flatten of the reconstructed subtrees equals
    exactly the subtrees at positions `[a, h]`.  Strong induction on `h + 1 − a`. -/
theorem recon_bfs_aux (fo : ℕ → ℕ) (lbl : ℕ → LT) (h : ℕ)
    (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) :
    ∀ (d a : ℕ), h + 1 - a = d → 1 ≤ a → a ≤ h + 1 →
      bfsForest ((List.range' a (firstC fo a - a)).map (buildT fo lbl h))
        = (List.range' a (h + 1 - a)).map (buildT fo lbl h) := by
  have hh : 1 ≤ h := by omega
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a hd ha1 hah
    by_cases hae : a = h + 1
    · subst hae
      have hfc : firstC fo (h + 1) = h + 1 := by unfold firstC; rw [Nat.add_sub_cancel]; omega
      rw [hfc]
      simp [bfsForest_nil]
    · have hale : a ≤ h := by omega
      have hval := hvalid a ha1 hale
      have hfc : firstC fo a = 2 + Sf fo (a - 1) := rfl
      -- frontier length ≥ 1
      have hlen1 : 1 ≤ firstC fo a - a := by omega
      set len := firstC fo a - a with hlendef
      have hne : ((List.range' a len).map (buildT fo lbl h)) ≠ [] := by
        rw [ne_eq, List.map_eq_nil_iff]
        intro hnil
        have : (List.range' a len).length = 0 := by rw [hnil]; rfl
        rw [List.length_range'] at this; omega
      rw [bfsForest_cons_eq _ hne]
      -- children forest
      have hpoint : ∀ i ∈ List.range' a len,
          NTree.children (buildT fo lbl h i)
            = (List.range' (firstC fo i) (fo i)).map (buildT fo lbl h) := by
        intro i hi
        rw [List.mem_range'] at hi
        obtain ⟨k, hk, hik⟩ := hi
        have hi1 : 1 ≤ i := by omega
        have hih : i ≤ h := by
          have hmono : Sf fo (a - 1) ≤ Sf fo h := Sf_mono fo (by omega)
          omega
        rw [buildT_children, childIdxs_eq fo h hSf hvalid hi1 hih]
      have hchild : ((List.range' a len).map (buildT fo lbl h)).flatMap NTree.children
          = (List.range' (firstC fo a) (firstC fo (firstC fo a) - firstC fo a)).map
              (buildT fo lbl h) := by
        rw [List.flatMap_map, List.flatMap_congr hpoint, ← List.map_flatMap,
          tiling fo len a ha1]
        have ha'eq : a + len = firstC fo a := by omega
        rw [ha'eq]
      rw [hchild]
      -- apply IH at a' = firstC fo a
      have ha' : firstC fo a = a + len := by omega
      have ha'le : firstC fo a ≤ h + 1 := by
        have hmono : Sf fo (a - 1) ≤ Sf fo h := Sf_mono fo (by omega)
        omega
      have hlt : h + 1 - firstC fo a < d := by omega
      have hIH := ih (h + 1 - firstC fo a) hlt (firstC fo a) rfl (by omega) ha'le
      rw [hIH]
      rw [← List.map_append]
      rw [ha']
      rw [range'_append_one]
      congr 2
      omega

/-- **The reconstructed tree** `slt` from the committed BFS layout. -/
def reconTree (fo : ℕ → ℕ) (lbl : ℕ → LT) (h : ℕ) : NTree LT := buildT fo lbl h 1

/-- **INVERSE-BFS ROUND-TRIP.**  The level-order flatten of the reconstructed
    tree reproduces exactly the committed node list `[node 1, …, node h]` (each node the
    reconstructed subtree at that BFS position).  Deterministic inverse of `bfsForest`. -/
theorem bfsForest_reconTree (fo : ℕ → ℕ) (lbl : ℕ → LT) (h : ℕ)
    (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) :
    bfsForest [reconTree fo lbl h] = (List.range' 1 h).map (buildT fo lbl h) := by
  have hh : 1 ≤ h := by omega
  have key := recon_bfs_aux fo lbl h hSf hvalid (h + 1 - 1) 1 rfl le_rfl (by omega)
  rw [firstC_one] at key
  have hone : (List.range' 1 (2 - 1)).map (buildT fo lbl h) = [reconTree fo lbl h] := by
    simp [reconTree]
  rw [hone] at key
  have : h + 1 - 1 = h := by omega
  rw [this] at key
  exact key

/-- The BFS labels of the reconstructed tree are exactly the committed row labels
    `[lbl 1, …, lbl h]`. -/
theorem reconTree_labels (fo : ℕ → ℕ) (lbl : ℕ → LT) (h : ℕ)
    (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) :
    (bfsForest [reconTree fo lbl h]).map NTree.label = (List.range' 1 h).map lbl := by
  rw [bfsForest_reconTree fo lbl h hSf hvalid, List.map_map]
  apply List.map_congr_left
  intro i _
  simp

/-- The `i`-th child-label of the reconstructed node: the label of the reconstructed subtree at
    the corresponding BFS position, or `⊥` past the fanout. -/
theorem buildT_childLabel (fo : ℕ → ℕ) (lbl : ℕ → LT) (h : ℕ)
    (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h)
    {i : ℕ} (hi1 : 1 ≤ i) (hih : i ≤ h) (j : ℕ) :
    (buildT fo lbl h i).childLabel j
      = if j < fo i then some (lbl (firstC fo i + j)) else none := by
  unfold NTree.childLabel NTree.childOpt
  rw [buildT_children, childIdxs_eq fo h hSf hvalid hi1 hih, List.getElem?_map]
  by_cases hj : j < fo i
  · rw [List.getElem?_range' hj]
    simp only [Nat.one_mul, Option.map_some, buildT_label, if_pos hj]
  · rw [List.getElem?_eq_none (by rw [List.length_range']; omega)]
    simp only [Option.map_none, if_neg hj]

/-- `isLeaf` of a reconstructed node ⟺ its fanout is `0` (no children). -/
theorem buildT_isLeaf (fo : ℕ → ℕ) (lbl : ℕ → LT) (h : ℕ)
    (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h)
    {i : ℕ} (hi1 : 1 ≤ i) (hih : i ≤ h) :
    (buildT fo lbl h i).isLeaf ↔ fo i = 0 := by
  unfold NTree.isLeaf
  rw [buildT_children, childIdxs_eq fo h hSf hvalid hi1 hih, List.map_eq_nil_iff]
  constructor
  · intro he
    have hl : (List.range' (firstC fo i) (fo i)).length = 0 := by rw [he]; rfl
    rw [List.length_range'] at hl; exact hl
  · intro h0; rw [h0]; rfl

end Reconstruct

/-! ### The queue-length structural gate (`QGate`) — soundness direction

  The `RAP_walk` gates (`WalkSat`) do NOT by themselves enforce that the committed fanout column
  `fo` lays out a genuine finite tree: the malicious witness `h = 3, fo = (0,2,0)` satisfies the
  polynomial identity + tiling yet is a self-loop (`BFSValid` fails at node 2).  This
  is NOT a pointer and does NOT touch the memory multiset — it is trace well-formedness over a
  scalar accumulator local to rows `i, i+1`.

  Soundness lift.  The field column equals the integer queue length `q_ℤ(i) = q0 + Sf fo (i−1) −
  (i−1)` (closed form `qgate_closed`).  It steps down by at most `1` (`fo i ≥ 0` ⟹ `fo i − 1 ≥
  −1`), so from `q_ℤ(1) = q0 ≥ 1` it can reach a value `< 1` only by first hitting `0` — excluded
  row-by-row by the inverse-witness gate `q i ≠ 0`.  Hence `q_ℤ(i) ≥ 1` throughout, i.e. `BFSValid`
  (`qgate_bfsValidGen`; needs NO characteristic assumption).  The terminal gate `q(h+1) = 0` gives
  the tiling `q0 + Sf fo h = h` (`qgate_tilingGen`), where the natural-number equality needs the
  standard no-wraparound bound `q0 + Sf fo h < p`, `h < p` (`p` the characteristic); with `Sf fo h
  ≤ h·n` this is the paper's `h·n < |K|` side-condition. -/

section QGate
variable {K : Type*} [Field K]

/-- Partial-fanout sum is bounded by `h·n` when every fanout is `≤ n`.  Turns the abstract
    no-wraparound bound into the paper's `h·n < |K|`. -/
theorem Sf_le_mul {fo : ℕ → ℕ} {n : ℕ} (harity : ∀ i, fo i ≤ n) (h : ℕ) :
    Sf fo h ≤ h * n := by
  unfold Sf
  calc ∑ i ∈ Finset.Icc 1 h, fo i ≤ ∑ _i ∈ Finset.Icc 1 h, n :=
        Finset.sum_le_sum (fun i _ => harity i)
    _ = (Finset.Icc 1 h).card * n := by rw [Finset.sum_const, smul_eq_mul]
    _ = h * n := by rw [Nat.card_Icc]; congr 1

/-- **The queue-length structural gate.**  A committed queue-length column `q` and its inverse
    witness `qinv` over the fanout column `fo`, with initial queue size `q0` (`= 1` for a single
    tree, `= kroots` for a `kroots`-root forest).  Constraints (all local to adjacent rows):
    `q 1 = q0` (boundary); `q(i+1) = q i + fanout(i) − 1` (transition: enqueue node `i`'s `fo i`
    children, dequeue itself); `q i · qinv i = 1` (no underflow, witnessing `q i ≠ 0`); and the
    terminal tile `q h + fanout(h) − 1 = 0` (i.e. `q(h+1) = 0`). -/
structure QGate (fo : ℕ → ℕ) (q qinv : ℕ → K) (q0 h : ℕ) : Prop where
  /-- `h ≥ 1`: at least the root row. -/
  hpos : 1 ≤ h
  /-- Boundary: the queue starts with `q0` roots. -/
  q1 : q 1 = (q0 : K)
  /-- Transition: process node `i`, enqueue its `fo i` children, dequeue itself. -/
  qInc : ∀ i, 1 ≤ i → i < h → q (i + 1) = q i + (fo i : K) - 1
  /-- No underflow: `q i ≠ 0`, witnessed by the committed inverse `qinv i`. -/
  qNonzero : ∀ i, 1 ≤ i → i ≤ h → q i * qinv i = 1
  /-- Terminal tile: the queue empties exactly at row `h+1`. -/
  qTerm : q h + (fo h : K) - 1 = 0

/-- **Closed form of the queue-length column.**  For `k + 1 ≤ h`, `q (k+1) = q0 + Sf fo k − k`.
    Pure field identity from the boundary + transition; no characteristic assumption. -/
theorem qgate_closed {fo : ℕ → ℕ} {q qinv : ℕ → K} {q0 h : ℕ}
    (hq : QGate fo q qinv q0 h) :
    ∀ k, k + 1 ≤ h → q (k + 1) = (q0 : K) + (Sf fo k : K) - (k : K) := by
  intro k
  induction k with
  | zero => intro _; rw [hq.q1]; simp
  | succ m ih =>
    intro hk
    rw [hq.qInc (m + 1) (by omega) (by omega), ih (by omega), Sf_succ]
    push_cast
    ring

/-- **`BFSValid` (generalized) from the gate.**  For `k + 1 ≤ h`, `k + 1 ≤ q0 + Sf fo k` — i.e.
    the queue length `q_ℤ(k+1) = q0 + Sf fo k − k ≥ 1`.  The inverse-witness gate `q i ≠ 0`
    upgrades the "steps down by ≤ 1" monotonicity from `≥ 0` to `≥ 1` at each row.  No
    characteristic assumption. -/
theorem qgate_bfsValidGen {fo : ℕ → ℕ} {q qinv : ℕ → K} {q0 h : ℕ}
    (hq : QGate fo q qinv q0 h) (hq0 : 1 ≤ q0) :
    ∀ k, k + 1 ≤ h → k + 1 ≤ q0 + Sf fo k := by
  intro k
  induction k with
  | zero => intro _; simpa using hq0
  | succ m ih =>
    intro hk
    have ihm : m + 1 ≤ q0 + Sf fo m := ih (by omega)
    -- steps down by ≤ 1: `q0 + Sf fo (m+1) = (q0 + Sf fo m) + fo (m+1) ≥ m + 1`
    have hge : m + 1 ≤ q0 + Sf fo (m + 1) := by rw [Sf_succ]; omega
    -- the inverse-witness gate forbids the queue from being exactly `0` at row `m+2`
    have hnz : q (m + 1 + 1) ≠ 0 := by
      intro h0
      have hq2 := hq.qNonzero (m + 1 + 1) (by omega) (by omega)
      rw [h0, zero_mul] at hq2
      exact one_ne_zero hq2.symm
    have hcl : q (m + 1 + 1) = (q0 : K) + (Sf fo (m + 1) : K) - ((m + 1 : ℕ) : K) :=
      qgate_closed hq (m + 1) hk
    -- so `q0 + Sf fo (m+1) ≠ m+1` as naturals (a natural equality would force `q = 0`)
    have hAneB : q0 + Sf fo (m + 1) ≠ m + 1 := by
      intro heq
      apply hnz
      rw [hcl]
      have h2 : ((q0 + Sf fo (m + 1) : ℕ) : K) = ((m + 1 : ℕ) : K) := by rw [heq]
      push_cast at h2 ⊢
      linear_combination h2
    have hlt : m + 1 < q0 + Sf fo (m + 1) := lt_of_le_of_ne hge (Ne.symm hAneB)
    omega

/-- **Tiling (generalized) from the terminal gate.**  `q(h+1) = 0` forces `q0 + Sf fo h = h`.  The
    natural-number equality needs the no-wraparound bound `q0 + Sf fo h < p`, `h < p` (`p` the
    characteristic), lifted from the field equality by `SetEq.natCast_inj_of_lt`. -/
theorem qgate_tilingGen {p : ℕ} [CharP K p] {fo : ℕ → ℕ} {q qinv : ℕ → K} {q0 h : ℕ}
    (hq : QGate fo q qinv q0 h) (hb1 : q0 + Sf fo h < p) (hb2 : h < p) :
    q0 + Sf fo h = h := by
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by have := hq.hpos; omega⟩
  have hcl : q (m + 1) = (q0 : K) + (Sf fo m : K) - (m : K) :=
    qgate_closed hq m (le_refl (m + 1))
  have hterm := hq.qTerm
  rw [hcl] at hterm
  have hcast : ((q0 + Sf fo (m + 1) : ℕ) : K) = ((m + 1 : ℕ) : K) := by
    have hs : Sf fo (m + 1) = Sf fo m + fo (m + 1) := Sf_succ fo m
    push_cast [hs]
    linear_combination hterm
  exact SetEq.natCast_inj_of_lt hb1 hb2 hcast

/-- **#5 discharge (soundness direction), single tree.**  The queue-length gate ⟹ `BFSValid`.  A
    cheating non-BFS fanout column cannot produce a `q`/`qinv` satisfying `QGate` (contrapositive),
    so the gate rejects it — closing census #5 without assuming queue-validity. -/
theorem bfsValid_of_qgate {fo : ℕ → ℕ} {q qinv : ℕ → K} {h : ℕ}
    (hq : QGate fo q qinv 1 h) : BFSValid fo h := by
  intro i hi1 hih
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simpa using qgate_bfsValidGen hq (le_refl 1) k (by omega)

/-- **#5 discharge (soundness direction), tiling.**  The terminal gate ⟹ the tiling `Sf fo h + 1 =
    h`, given the no-wraparound bound. -/
theorem Sf_tiling_of_qgate {p : ℕ} [CharP K p] {fo : ℕ → ℕ} {q qinv : ℕ → K} {h : ℕ}
    (hq : QGate fo q qinv 1 h) (hb1 : 1 + Sf fo h < p) (hb2 : h < p) :
    Sf fo h + 1 = h := by
  have := qgate_tilingGen hq hb1 hb2
  omega

/-- **Non-vacuity / completeness of the gate.**  A genuine queue-valid, tiling fanout column
    (as any real BFS execution/decomposition tree produces — `foCol_BFSValid`/`foCol_Sf_tiling`)
    ADMITS a queue-length column `q` and inverse witness `qinv` satisfying `QGate` (the honest
    `q i = q0 + Sf fo (i−1) − (i−1) ≥ 1` is invertible under the no-wraparound bound).  So the
    gate's hypotheses are satisfiable — the soundness capstones are NOT vacuous. -/
theorem qgate_of_bfsValid {p : ℕ} [CharP K p] {fo : ℕ → ℕ} {q0 h : ℕ}
    (hh : 1 ≤ h) (hq0 : 1 ≤ q0)
    (hvalid : ∀ i, 1 ≤ i → i ≤ h → i ≤ q0 + Sf fo (i - 1))
    (htile : q0 + Sf fo h = h) (hb : q0 + Sf fo h < p) :
    ∃ q qinv : ℕ → K, QGate fo q qinv q0 h := by
  classical
  set q : ℕ → K := fun i => (q0 : K) + (Sf fo (i - 1) : K) - ((i - 1 : ℕ) : K) with hqdef
  -- each in-range queue value is a distinct-below-`p` nat difference, hence nonzero
  have hnz : ∀ i, 1 ≤ i → i ≤ h → q i ≠ 0 := by
    intro i hi1 hih
    have hval := hvalid i hi1 hih
    have hmono : Sf fo (i - 1) ≤ Sf fo h := Sf_mono fo (by omega)
    have hAlt : q0 + Sf fo (i - 1) < p := by omega
    have hBlt : i - 1 < p := by omega
    have hAB : q0 + Sf fo (i - 1) ≠ i - 1 := by omega
    have hcast : ((q0 + Sf fo (i - 1) : ℕ) : K) ≠ ((i - 1 : ℕ) : K) := fun heq =>
      hAB (SetEq.natCast_inj_of_lt hAlt hBlt heq)
    rw [hqdef]
    simp only
    intro h0
    apply hcast
    push_cast
    linear_combination h0
  refine ⟨q, fun i => (q i)⁻¹, ?_⟩
  refine ⟨hh, ?_, ?_, ?_, ?_⟩
  · -- q1
    rw [hqdef]; simp
  · -- qInc
    intro i hi1 _
    have hA : (Sf fo i : K) = (Sf fo (i - 1) : K) + (fo i : K) := by
      rw [Sf_pred_succ fo hi1]; push_cast; ring
    have hB : (i : K) = ((i - 1 : ℕ) : K) + 1 := by
      have hi : (i - 1) + 1 = i := by omega
      conv_lhs => rw [← hi]
      push_cast; ring
    rw [hqdef]; simp only [Nat.add_sub_cancel]
    rw [hA, hB]; ring
  · -- qNonzero
    intro i hi1 hih
    exact mul_inv_cancel₀ (hnz i hi1 hih)
  · -- qTerm
    have hkeyN : q0 + Sf fo (h - 1) + fo h = (h - 1) + 1 := by
      have e1 : Sf fo h = Sf fo (h - 1) + fo h := Sf_pred_succ fo hh
      omega
    have hkey : (q0 : K) + (Sf fo (h - 1) : K) + (fo h : K) = ((h - 1 : ℕ) : K) + 1 := by
      have h' := congrArg (Nat.cast (R := K)) hkeyN
      push_cast at h'
      linear_combination h'
    rw [hqdef]; simp only
    linear_combination hkey

/-- **#5 witness exclusion.**  The malicious `h = 3, fo = (0,2,0)`
    (self-loop at node 2, `BFSValid` false) is EXCLUDED by a gate: it forces `q 2 = q 1 + fo 1 − 1
    = 1 + 0 − 1 = 0`, so no inverse witness `qinv 2` with `q 2 · qinv 2 = 1` can exist.  Excluded by
    a constraint, not assumed away. -/
theorem witness_020_excluded (q qinv : ℕ → K) :
    ¬ QGate (fun i => if i = 2 then 2 else 0) q qinv 1 3 := by
  intro hq
  have hqi := hq.qInc 1 (le_refl 1) (by norm_num)
  simp only [hq.q1, Nat.cast_one, show (if (1 : ℕ) = 2 then (2 : ℕ) else 0) = 0 from
    by norm_num, Nat.cast_zero] at hqi
  have hq2 : q 2 = 0 := by rw [hqi]; ring
  have hnz := hq.qNonzero 2 (by norm_num) (by norm_num)
  rw [hq2, zero_mul] at hnz
  exact one_ne_zero hnz.symm

end QGate

/-! ### Lift the reconstructed tree to `L_RVT^{F,n}`

  Given the committed BFS layout and the per-row `F`-constraints on the layout-consistent child
  labels, the reconstructed tree `reconTree fo lbl h` is in `L_RVT^{F,n}`.  `StateSep.dynamic`
  is load-bearing for the leaf-iff clause of `Def:RVT` (a leaf ⟺ its label verifies with no
  children); the derived `fanout_eq_children_length` / `walk_leaf_iff_Sleaf` then certify the
  fanout/leaf bindings for the reconstructed tree. -/

section ReconstructRVT
variable {S DT : Type*} {n : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}

/-- **Per-node `F`-constraint of the reconstructed tree.**  Both clauses of `Def:RVT`: the label verifies against its (layout-derived) child labels, and it is a leaf iff its
    label verifies with no children.  The leaf-iff `⟸` uses `StateSep.dynamic`. -/
theorem Fcon_buildT (St : StateSep F) (fo : ℕ → ℕ) (lbl : ℕ → S × DT) (h : ℕ)
    (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hF : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (lbl (firstC fo i + j)) else none))
    {i : ℕ} (hi1 : 1 ≤ i) (hih : i ≤ h) :
    Fcon F (buildT fo lbl h i) := by
  have hlabel : (buildT fo lbl h i).label = lbl i := buildT_label fo lbl h i
  have hclab : (fun j : Fin n => (buildT fo lbl h i).childLabel ↑j)
      = (fun j : Fin n => if (j : ℕ) < fo i then some (lbl (firstC fo i + j)) else none) := by
    funext j; rw [buildT_childLabel fo lbl h hSf hvalid hi1 hih]
  refine ⟨?_, ?_⟩
  · rw [hlabel, hclab]; exact hF i hi1 hih
  · rw [hlabel, buildT_isLeaf fo lbl h hSf hvalid hi1 hih]
    constructor
    · intro h0
      have hf := hF i hi1 hih
      have hconst : (fun j : Fin n => if (j : ℕ) < fo i then some (lbl (firstC fo i + j)) else none)
          = (fun _ : Fin n => none) := by funext j; rw [h0]; simp
      rw [hconst] at hf; exact hf
    · intro hFnone
      by_contra hne
      have hpos : 0 < fo i := by omega
      have hn : 0 < n := lt_of_lt_of_le hpos (harity i)
      have hfoeq := hfo i hi1 hih
      have hF' : F ((lbl i).1, (lbl i).2) (fun _ : Fin n => none) := by
        rw [Prod.mk.eta]; exact hFnone
      have hdyn := St.dynamic (lbl i).1 (lbl i).2 (fun _ => none) hF' ⟨0, hn⟩
      simp only [ne_eq, not_true_eq_false, iff_false, not_lt, Nat.le_zero] at hdyn
      omega

/-- **THE INVERSE-BFS LIFT.**  The reconstructed tree is in `L_RVT^{F,n}`.
    Deterministic, axiom-free, probability-free: `RVT_iff_walk_Fcon` reduces membership to the
    per-BFS-row `F`-constraints, discharged by `Fcon_buildT`. -/
theorem reconTree_RVT (St : StateSep F) (fo : ℕ → ℕ) (lbl : ℕ → S × DT) (h : ℕ)
    (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hF : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (lbl (firstC fo i + j)) else none)) :
    RVT F (reconTree fo lbl h) := by
  rw [RVT_iff_walk_Fcon, bfsForest_reconTree fo lbl h hSf hvalid]
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨i, hi, rfl⟩ := ht
  rw [List.mem_range'] at hi
  obtain ⟨k, hk, hik⟩ := hi
  exact Fcon_buildT St fo lbl h hSf hvalid harity hfo hF (by omega) (by omega)

end ReconstructRVT

/-! ### The literal `Thm:Walk_IOP`: `∃ slt ∈ L_RVT^{F,n}`

  Compose the probabilistic bound of `walk_IOP_soundness_card` (concluding `VecBFT`, the committed vectors form a
  BFS layout) with the deterministic inverse-BFS reconstruction + RVT lift.  The committed data
  are row labels `lbl : ℕ → S × DT` and child labels `clab`, encoded into `𝔽^{node_size}` by an
  injective `enc` (the paper's `𝓛𝓣 ⊆ 𝔽^{node_size}`).  Result: an accepting `RAP_walk` table
  (`out_walk = 0`) over random `(α, γ)` implies, EXCEPT with probability `≤ h/|K| + ε_RLC`
  (`ε_RLC = h·(node_size − 1)/|K|`), that `∃ slt ∈ L_RVT^{F,n}` whose BFS reproduces the
  committed rows — the literal conclusion of the paper. -/

section ComposeRVT
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {node_size n : ℕ}
variable {S DT : Type*} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}

/-- getElem? of a committed children block. -/
theorem blkValsV_getElem? (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) {i l : ℕ}
    (hl : l < fo i) : (blkValsV Cv fo i)[l]? = some (Cv i (l + 1)) := by
  unfold blkValsV
  rw [List.getElem?_map, List.getElem?_range hl]; rfl

theorem Sf_split (fo : ℕ → ℕ) {i : ℕ} (hi : 1 ≤ i) : Sf fo i = Sf fo (i - 1) + fo i := by
  have hj : i - 1 + 1 = i := by omega
  conv_lhs => rw [← hj]
  rw [Sf_succ, hj]

/-- getElem? into the flattened committed children at the layout position `Σ_{m<i}fanout + l`
    reads off `Cv i (l+1)`. -/
theorem flatBlksV_getElem? (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) :
    ∀ (k i l : ℕ), 1 ≤ i → i ≤ k → l < fo i →
      (flatBlksV Cv fo k)[Sf fo (i - 1) + l]? = some (Cv i (l + 1)) := by
  intro k
  induction k with
  | zero => intro i l hi1 hik hl; omega
  | succ m ih =>
    intro i l hi1 hik hl
    rw [flatBlksV_succ]
    by_cases hik' : i ≤ m
    · have hlt : Sf fo (i - 1) + l < (flatBlksV Cv fo m).length := by
        rw [flatBlksV_length]
        have hsfi := Sf_split fo hi1
        have hmono : Sf fo i ≤ Sf fo m := Sf_mono fo hik'
        omega
      rw [List.getElem?_append_left hlt]
      exact ih i l hi1 hik' hl
    · have him : i = m + 1 := by omega
      subst him
      have hge : (flatBlksV Cv fo m).length ≤ Sf fo (m + 1 - 1) + l := by
        rw [flatBlksV_length]; simp
      rw [List.getElem?_append_right hge, flatBlksV_length]
      have hidx : Sf fo (m + 1 - 1) + l - Sf fo m = l := by simp
      rw [hidx]
      exact blkValsV_getElem? Cv fo hl

theorem curValsV_getElem? (V : ℕ → Fin node_size → K) {h m : ℕ} (hm : m < h) :
    (curValsV V h)[m]? = some (V (m + 1)) := by
  unfold curValsV
  rw [List.getElem?_map, List.getElem?_range hm]; rfl

/-- **VecBFT ⟹ committed children are the BFS-layout nodes.**  From the vector-level BFS
    fixpoint, the committed child vector `Cv i (l+1)` equals the node vector `V (firstC i + l)`
    at the corresponding BFS position. -/
theorem VecBFT_layout (V : ℕ → Fin node_size → K) (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hbft : VecBFT V Cv fo h)
    {i l : ℕ} (hi1 : 1 ≤ i) (hih : i ≤ h) (hl : l < fo i) :
    Cv i (l + 1) = V (firstC fo i + l) := by
  have hsfi := Sf_split fo hi1
  have hmono : Sf fo i ≤ Sf fo h := Sf_mono fo hih
  have e1 : (curValsV V h)[Sf fo (i - 1) + l + 1]? = some (V (Sf fo (i - 1) + l + 1 + 1)) :=
    curValsV_getElem? V (by omega)
  have e2 : (V 1 :: flatBlksV Cv fo h)[Sf fo (i - 1) + l + 1]?
      = (flatBlksV Cv fo h)[Sf fo (i - 1) + l]? := List.getElem?_cons_succ
  rw [hbft, e2, flatBlksV_getElem? Cv fo h i l hi1 hih hl] at e1
  rw [Option.some.injEq] at e1
  rw [e1]
  congr 1
  unfold firstC
  omega

/-- **The deterministic reconstruction ⟹ RVT membership.**  Under the committed per-row
    `F`-constraints, `StateSep`, arity/validity, and the vector-BFT fixpoint, the reconstructed
    tree is in `L_RVT^{F,n}`. -/
theorem VecBFT_reconstruct (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none))
    (hbft : VecBFT (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo h) :
    RVT F (reconTree fo lbl h) := by
  apply reconTree_RVT St fo lbl h hSf hvalid harity hfo
  intro i hi1 hih
  have hfun : (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)
      = (fun j : Fin n => if (j : ℕ) < fo i then some (lbl (firstC fo i + j)) else none) := by
    funext j
    by_cases hj : (j : ℕ) < fo i
    · have hkey := VecBFT_layout (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo hSf hbft
        hi1 hih hj
      rw [if_pos hj, if_pos hj, hEnc hkey]
    · rw [if_neg hj, if_neg hj]
  rw [← hfun]
  exact hFcommit i hi1 hih

/-- **Certified state-data-separation bindings for the reconstructed tree.**
    Once `slt = reconTree` is known to be in `L_RVT^{F,n}`, `StateSep` binds its structure: at
    every BFS node the state's `fanout` equals the real child count (`fanout_eq_children_length`)
    and leaf-ness is decided by the leaf-state set (`walk_leaf_iff_Sleaf`).  A cheating prover
    therefore cannot misreport the fanout column against `slt`'s real shape. -/
theorem reconTree_bindings (St : StateSep F) (fo : ℕ → ℕ) (lbl : ℕ → S × DT) (h : ℕ)
    (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hrvt : RVT F (reconTree fo lbl h)) :
    (∀ t ∈ bfsForest [reconTree fo lbl h], St.fanout (NTree.label t).1 = t.children.length) ∧
      (∀ t ∈ bfsForest [reconTree fo lbl h], t.isLeaf ↔ St.Sleaf (NTree.label t).1) := by
  have key : ∀ t ∈ bfsForest [reconTree fo lbl h],
      St.fanout (NTree.label t).1 = t.children.length ∧
        (t.isLeaf ↔ St.Sleaf (NTree.label t).1) := by
    intro t ht
    have htIn : InTree (reconTree fo lbl h) t := by
      obtain ⟨c, hc, hct⟩ := (mem_bfsForest [reconTree fo lbl h] t).mp ht
      rw [List.mem_singleton] at hc; subst hc; exact hct
    rw [bfsForest_reconTree fo lbl h hSf hvalid, List.mem_map] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    rw [List.mem_range'] at hi
    obtain ⟨k, hk, hik⟩ := hi
    have hi1 : 1 ≤ i := by omega
    have hih : i ≤ h := by omega
    have hchlen : (buildT fo lbl h i).children.length = fo i := by
      rw [buildT_children, childIdxs_eq fo h hSf hvalid hi1 hih, List.length_map,
        List.length_range']
    have hproper : (buildT fo lbl h i).children.length ≤ n := by rw [hchlen]; exact harity i
    exact ⟨fanout_eq_children_length St hrvt htIn hproper,
      (walk_leaf_iff_Sleaf St hrvt htIn).1⟩
  exact ⟨fun t ht => (key t ht).1, fun t ht => (key t ht).2⟩

/-- **The literal `Thm:Walk_IOP` conclusion:** there is an `slt ∈ L_RVT^{F,n}`
    whose BFS reproduces the committed rows, and whose fanout/leaf structure is bound by
    `StateSep`.  `α`/`γ`-independent — a property of the committed data. -/
def ReconGoal (St : StateSep F) (lbl : ℕ → S × DT) (h : ℕ) : Prop :=
  ∃ slt : NTree (S × DT), RVT F slt ∧
    (bfsForest [slt]).map NTree.label = (List.range' 1 h).map lbl ∧
    (∀ t ∈ bfsForest [slt], St.fanout (NTree.label t).1 = t.children.length) ∧
    (∀ t ∈ bfsForest [slt], t.isLeaf ↔ St.Sleaf (NTree.label t).1)

/-- Under the committed `F`-constraints + `StateSep` + queue-validity, the vector-BFT fixpoint
    yields the full literal goal. -/
theorem reconTree_ReconGoal (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none))
    (hbft : VecBFT (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo h) :
    ReconGoal St lbl h := by
  have hrvt := VecBFT_reconstruct St enc hEnc lbl clab fo hSf hvalid harity hfo hFcommit hbft
  have hbind := reconTree_bindings St fo lbl h hSf hvalid harity hrvt
  exact ⟨reconTree fo lbl h, hrvt, reconTree_labels fo lbl h hSf hvalid, hbind.1, hbind.2⟩

/-- **`Thm:Walk_IOP` — LITERAL soundness, cardinality form.**  For committed row
    labels `lbl` and child labels `clab` (encoded into `𝔽^{node_size}` by an injective `enc`),
    with a queue-valid fanout column `fo` (`Sf fo h + 1 = h`, `BFSValid`, `fo ≤ n`, state-defined
    via `St.fanout`) and the per-row `F`-constraints on the committed children, the number of
    challenge pairs `(α, γ)` for which the `RAP_walk` gates accept (`out_walk = 0`) YET the
    literal `Thm:Walk_IOP` goal `∃ slt ∈ L_RVT^{F,n}` (`ReconGoal`) FAILS is
      `≤ |K|·h + |K|·(h·(node_size − 1))`,
    i.e. probability `≤ h/|K| + ε_RLC`, `ε_RLC = h·(node_size − 1)/|K|` (the paper's
    `h/|K|` alone omits `ε_RLC`).  Composition of `walk_IOP_soundness_card` (α-Schwartz–Zippel +
    γ-RLC bound) with the deterministic inverse-BFS reconstruction + RVT lift
    (`reconTree_ReconGoal`). -/
theorem Walk_IOP_final_card (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    (Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
            ln count acc p.1 (rlc p.2 (enc (lbl 1)) * p.1) p.1 h ∧ acc h = 0)
        ∧ ¬ ReconGoal St lbl h)).card
      ≤ Fintype.card K * h + Fintype.card K * (h * (node_size - 1)) := by
  refine le_trans (Finset.card_le_card ?_)
    (walk_IOP_soundness_card (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo hSf)
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, hp.2.1, ?_⟩
  intro hbft
  exact hp.2.2 (reconTree_ReconGoal St enc hEnc lbl clab fo hSf hvalid harity hfo hFcommit hbft)

/-- **`Thm:Walk_IOP` — LITERAL soundness, probability form.**  Over uniformly
    random verifier challenges `(α, γ) ∈ K × K`, the probability that the `RAP_walk` gates
    accept while the literal goal `∃ slt ∈ L_RVT^{F,n}` (`ReconGoal`) fails is bounded by
    `≤ h/|K| + ε_RLC`, `ε_RLC = h·(node_size − 1)/|K|`. -/
theorem Walk_IOP_final_prob (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    ((Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
            ln count acc p.1 (rlc p.2 (enc (lbl 1)) * p.1) p.1 h ∧ acc h = 0)
        ∧ ¬ ReconGoal St lbl h)).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (h : ℚ) / (Fintype.card K : ℚ)
          + ((h * (node_size - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  have hpos : (0 : ℚ) < (Fintype.card K : ℚ) := by
    haveI : Nonempty K := ⟨0⟩; exact_mod_cast Fintype.card_pos
  have hpos2 : (0 : ℚ) < (Fintype.card K : ℚ) * (Fintype.card K : ℚ) := by positivity
  have hcard := Walk_IOP_final_card St enc hEnc lbl clab fo hSf hvalid harity hfo hFcommit
  have hcast : ((Finset.univ.filter (fun p : K × K =>
      (∃ ln count acc : ℕ → K,
        WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
          ln count acc p.1 (rlc p.2 (enc (lbl 1)) * p.1) p.1 h ∧ acc h = 0)
      ∧ ¬ ReconGoal St lbl h)).card : ℚ)
      ≤ (Fintype.card K : ℚ) * h + (Fintype.card K : ℚ) * (h * (node_size - 1) : ℕ) := by
    exact_mod_cast hcard
  rw [div_le_iff₀ hpos2]
  refine le_trans hcast (le_of_eq ?_)
  field_simp

/-! The walk binds what the encoder sees.  When `enc` is the paper's `LT_comp` projection rather than an injective encoding of the whole row, injectivity is replaced by
two facts: encoder-equal labels have equal projections (`hEnc`), and the labeling language reads
each child only through the projection (`RespectsChildLabels`).  The injective statements above
are the special case `labelOf = id`. -/

/-- `F` sees each child only through `labelOf`. -/
def RespectsChildLabels {L : Type*} (F : (S × DT) → (Fin n → Option (S × DT)) → Prop)
    (labelOf : S × DT → L) : Prop :=
  ∀ (lbl : S × DT) (xout xout' : Fin n → Option (S × DT)),
    (∀ j, (xout j).map labelOf = (xout' j).map labelOf) → F lbl xout → F lbl xout'

theorem respectsChildLabels_id : RespectsChildLabels F (id : S × DT → S × DT) := by
  intro lbl xout xout' h hF
  have : xout = xout' := by
    funext j
    have hj := h j
    simpa [Option.map_id'] using hj
  rw [← this]
  exact hF

theorem VecBFT_reconstruct_of_label {L : Type*} (St : StateSep F) (labelOf : S × DT → L)
    (hResp : RespectsChildLabels F labelOf)
    (enc : (S × DT) → (Fin node_size → K))
    (hEnc : ∀ a b, enc a = enc b → labelOf a = labelOf b)
    (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none))
    (hbft : VecBFT (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo h) :
    RVT F (reconTree fo lbl h) := by
  apply reconTree_RVT St fo lbl h hSf hvalid harity hfo
  intro i hi1 hih
  refine hResp (lbl i) _ _ ?_ (hFcommit i hi1 hih)
  intro j
  by_cases hj : (j : ℕ) < fo i
  · have hkey := VecBFT_layout (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo hSf hbft
      hi1 hih hj
    rw [if_pos hj, if_pos hj]
    simp only [Option.map_some]
    rw [hEnc _ _ hkey]
  · rw [if_neg hj, if_neg hj]

theorem reconTree_ReconGoal_of_label {L : Type*} (St : StateSep F) (labelOf : S × DT → L)
    (hResp : RespectsChildLabels F labelOf)
    (enc : (S × DT) → (Fin node_size → K))
    (hEnc : ∀ a b, enc a = enc b → labelOf a = labelOf b)
    (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none))
    (hbft : VecBFT (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo h) :
    ReconGoal St lbl h := by
  have hrvt := VecBFT_reconstruct_of_label St labelOf hResp enc hEnc lbl clab fo hSf hvalid
    harity hfo hFcommit hbft
  have hbind := reconTree_bindings St fo lbl h hSf hvalid harity hrvt
  exact ⟨reconTree fo lbl h, hrvt, reconTree_labels fo lbl h hSf hvalid, hbind.1, hbind.2⟩

/-- `Walk_IOP_final_card` with the encoder binding only the `labelOf` projection. -/
theorem Walk_IOP_final_card_of_label {L : Type*} (St : StateSep F) (labelOf : S × DT → L)
    (hResp : RespectsChildLabels F labelOf)
    (enc : (S × DT) → (Fin node_size → K))
    (hEnc : ∀ a b, enc a = enc b → labelOf a = labelOf b)
    (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    (Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
            ln count acc p.1 (rlc p.2 (enc (lbl 1)) * p.1) p.1 h ∧ acc h = 0)
        ∧ ¬ ReconGoal St lbl h)).card
      ≤ Fintype.card K * h + Fintype.card K * (h * (node_size - 1)) := by
  refine le_trans (Finset.card_le_card ?_)
    (walk_IOP_soundness_card (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo hSf)
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, hp.2.1, ?_⟩
  intro hbft
  exact hp.2.2 (reconTree_ReconGoal_of_label St labelOf hResp enc hEnc lbl clab fo hSf hvalid
    harity hfo hFcommit hbft)

/-- `Walk_IOP_final_prob` with the encoder binding only the `labelOf` projection. -/
theorem Walk_IOP_final_prob_of_label {L : Type*} (St : StateSep F) (labelOf : S × DT → L)
    (hResp : RespectsChildLabels F labelOf)
    (enc : (S × DT) → (Fin node_size → K))
    (hEnc : ∀ a b, enc a = enc b → labelOf a = labelOf b)
    (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    ((Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
            ln count acc p.1 (rlc p.2 (enc (lbl 1)) * p.1) p.1 h ∧ acc h = 0)
        ∧ ¬ ReconGoal St lbl h)).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (h : ℚ) / (Fintype.card K : ℚ)
          + ((h * (node_size - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  have hpos : (0 : ℚ) < (Fintype.card K : ℚ) := by
    haveI : Nonempty K := ⟨0⟩; exact_mod_cast Fintype.card_pos
  have hpos2 : (0 : ℚ) < (Fintype.card K : ℚ) * (Fintype.card K : ℚ) := by positivity
  have hcard := Walk_IOP_final_card_of_label St labelOf hResp enc hEnc lbl clab fo hSf hvalid
    harity hfo hFcommit
  have hcast : ((Finset.univ.filter (fun p : K × K =>
      (∃ ln count acc : ℕ → K,
        WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
          ln count acc p.1 (rlc p.2 (enc (lbl 1)) * p.1) p.1 h ∧ acc h = 0)
      ∧ ¬ ReconGoal St lbl h)).card : ℚ)
      ≤ (Fintype.card K : ℚ) * h + (Fintype.card K : ℚ) * (h * (node_size - 1) : ℕ) := by
    exact_mod_cast hcard
  rw [div_le_iff₀ hpos2]
  refine le_trans hcast (le_of_eq ?_)
  field_simp

end ComposeRVT

/-! ## `Corr:forest` — composed multi-root forest soundness

  The single-tree `Walk_IOP_final_*` (`ComposeRVT`) discharges soundness for ONE root
  (`Sf fo h + 1 = h`).  For a subject-mutating Nock program the memory table is a **forest** of
  `k = kroots` labeled `n`-ary trees: the walk verifies
  membership in `∏_{i=1}^k L_RVT^{F,n}` with the forest initial inputs
  `(seed, initial_count) = (Σ_{i=1}^k RLC^γ(sltᵢ)·αⁱ, αᵏ)` and the tiling
  `kroots + Sf fo h = h` (kroots roots + all children = h aggregate nodes).

  This section is the multi-root generalisation of `ComposeRVT`, mirroring it declaration for
  declaration.  Honest soundness bound `≤ h/|K| + ε_RLC`.  The single-root treatment is recovered at `kroots = 1`
  (`ForestReconGoal_one`, `Walk_IOP_final_card_of_forest`).  Everything below is sorry-free. -/

/-! ### Forest arithmetic: `forestQueueP` as an `lpoly`, forest reverse-BFT-iff -/

section ForestArith
variable {K : Type*} [Field K]

/-- `childSumP` evaluated at `α` is the scalar per-row child-sum `childSum`. -/
theorem childSumP_eval (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (i : ℕ) (α : K) :
    (childSumP chld' fo i).eval α = childSum chld' fo α i := by
  unfold childSumP childSum
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [eval_mul, eval_C, eval_pow, eval_X]

/-- **Forest queue polynomial, evaluated.**  `forest_queue_h(α) = node_list_k(α)
    + αᵏ·Σ childSum`, i.e. the roots preloaded as the `node_list` prefix plus the `αᵏ`-weighted
    accumulated children. -/
theorem forestQueueP_eval (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (kroots h : ℕ) (α : K) :
    (forestQueueP cur chld' fo kroots h).eval α
      = (nodeListP cur kroots).eval α + α ^ kroots * ∑ i ∈ Finset.Icc 1 h, childSum chld' fo α i := by
  unfold forestQueueP
  rw [eval_add, eval_mul, eval_pow, eval_X, eval_finsetSum]
  simp_rw [childSumP_eval]

/-- `Xᵐ·lpoly e l = lpoly (e+m) l`: multiplying by `Xᵐ` shifts the base exponent by `m`. -/
theorem X_pow_mul_lpoly (m e : ℕ) (l : List K) :
    (X : K[X]) ^ m * lpoly e l = lpoly (e + m) l := by
  induction l generalizing e with
  | nil => simp
  | cons a rest ih =>
    rw [lpoly_cons, lpoly_cons, mul_add, ih (e + 1)]
    have h1 : (X : K[X]) ^ m * (C a * X ^ e) = C a * X ^ (e + m) := by rw [pow_add]; ring
    have h2 : e + 1 + m = e + m + 1 := by omega
    rw [h1, h2]

/-- `childSumP` of row `i+1` as the children `lpoly` at base `1 + Σ_{m≤i}fanout`. -/
theorem childSumP_eq_lpoly_gen (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (i : ℕ) :
    childSumP chld' fo (i + 1) = lpoly (1 + Sf fo i) (blkVals chld' fo (i + 1)) := by
  unfold childSumP
  rw [Nat.add_sub_cancel, lpoly_eq_sum, blkVals_length, sum_Icc_one_eq_range]
  refine Finset.sum_congr rfl (fun l hl => ?_)
  have hb : (blkVals chld' fo (i + 1)).getD l 0 = chld' (i + 1) (l + 1) := by
    rw [blkVals, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (Finset.mem_range.mp hl)]; rfl
  rw [hb]; congr 2; omega

/-- The child-sum accumulation over rows `1..k` is the flattened-children `lpoly` at base `1`. -/
theorem queueSumP_eq_lpoly (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (k : ℕ) :
    ∑ i ∈ Finset.Icc 1 k, childSumP chld' fo i = lpoly 1 (flatBlks chld' fo k) := by
  induction k with
  | zero => simp [flatBlks]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ m + 1), ih, childSumP_eq_lpoly_gen,
      flatBlks_succ, lpoly_append, flatBlks_length]

/-- **Forest queue polynomial as a value-list `lpoly`.**  `forest_queue_h = lpoly 1 (roots ++
    flattened children)` — the aggregate BFS layout of the `kroots`-root forest. -/
theorem forestQueueP_eq_lpoly (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (kroots h : ℕ) :
    forestQueueP cur chld' fo kroots h
      = lpoly 1 (curVals cur kroots ++ flatBlks chld' fo h) := by
  unfold forestQueueP
  rw [nodeListP_eq_lpoly_gen, queueSumP_eq_lpoly, X_pow_mul_lpoly, lpoly_append, curVals_length]

/-- The arithmetized forest full-BFT identity: `node_list_h`
    equals the forest queue polynomial. -/
def IsForestFullBFT (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (kroots h : ℕ) : Prop :=
  nodeListP cur h = forestQueueP cur chld' fo kroots h

/-- **Forest reverse-BFT-iff.**  If the forest full-BFT identity
    holds and the fanout column has the `h`-node forest structure (`kroots + Sf fo h = h`), the
    `cur` value column is the aggregate BFS reindex: `[cur 1,…,cur h]` equals the `kroots` roots
    followed by the flattened children of all rows.  Multi-root analogue of
    `isFullBFT_curVals`, via `lpoly` injectivity. -/
theorem isForestFullBFT_curVals {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {kroots h : ℕ}
    (hlen : kroots + Sf fo h = h) (hbft : IsForestFullBFT cur chld' fo kroots h) :
    curVals cur h = curVals cur kroots ++ flatBlks chld' fo h := by
  apply lpoly_inj 1
  · rw [curVals_length, List.length_append, curVals_length, flatBlks_length]; omega
  · rw [← nodeListP_eq_lpoly_gen, ← forestQueueP_eq_lpoly]; exact hbft

/-- **`out_walk = 0 ⟺ forest full-BFT identity` for the forest recognizer inputs.**  Substituting
    `seed = node_list_k(α) = Σ RLC(sltᵢ)·αⁱ` and `initial_count = αᵏ` into `forest_walk`. -/
theorem forest_out_zero_iff {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {ln count acc : ℕ → K}
    {α seed initial_count : K} {h kroots : ℕ}
    (hw : WalkSat cur chld' fo ln count acc α seed initial_count h)
    (hseed : seed = (nodeListP cur kroots).eval α) (hic : initial_count = α ^ kroots) :
    acc h = 0 ↔ (nodeListP cur h).eval α = (forestQueueP cur chld' fo kroots h).eval α := by
  rw [forest_walk hw]
  unfold ForestAccepts
  rw [forestQueueP_eval, hseed, hic]

end ForestArith

/-! ### The multi-root vector-BFT fixpoint and its layout -/

section ForestVec
variable {K : Type*} [Field K] {node_size : ℕ}

/-- **The multi-root vector breadth-first-traversal fixpoint (aggregate BFS of a `kroots`-root
    forest).**  The node-vectors of rows `1..h` equal the `kroots` root vectors prepended to the
    flattened committed children-vectors.  `α`/`γ`-independent (a property of committed vectors);
    it is the conclusion of the forest soundness bound. -/
def ForestVecBFT (V : ℕ → Fin node_size → K) (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ)
    (kroots h : ℕ) : Prop :=
  curValsV V h = curValsV V kroots ++ flatBlksV Cv fo h

/-- First BFS position of node `i`'s children in a `kroots`-root forest: `kroots + 1 +
    Σ_{m<i}fanout` (roots occupy `1..kroots`, then flattened children). -/
def firstCF (kroots : ℕ) (fo : ℕ → ℕ) (i : ℕ) : ℕ := kroots + 1 + Sf fo (i - 1)

end ForestVec


section ForestComposeCard
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {node_size : ℕ}

/-- **`Corr:forest` composed soundness, cardinality form.**  For committed
    node/children vectors `V, Cv` and a queue-valid fanout column with the `h`-node **forest**
    structure (`kroots + Sf fo h = h`), the number of challenge pairs `(α,γ)` for which the walk
    gates accept (`out_walk = 0`) with the FOREST recognizer inputs
    `(seed, initial_count) = (Σ_{i≤k} RLC^γ(Vᵢ)·αⁱ, αᵏ)` YET the committed vectors do NOT form the
    aggregate vector-BFT (`¬ ForestVecBFT`) is `≤ |K|·h + |K|·(h·(node_size−1))` — probability
    `≤ h/|K| + ε_RLC`.  Multi-root analogue of `walk_IOP_soundness_card`; α-side is the forest
    Schwartz–Zippel (`forest_soundness_card`), γ-side is the same RLC-collision lift. -/
theorem walk_IOP_forest_soundness_card
    (V : ℕ → Fin node_size → K) (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) {kroots h : ℕ}
    (hlen : kroots + Sf fo h = h) :
    (Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (V i)) (fun i l => rlc p.2 (Cv i l)) fo ln count acc
            p.1 (∑ i ∈ Finset.Icc 1 kroots, rlc p.2 (V i) * p.1 ^ i) (p.1 ^ kroots) h ∧ acc h = 0)
        ∧ ¬ ForestVecBFT V Cv fo kroots h)).card
      ≤ Fintype.card K * h + Fintype.card K * (h * (node_size - 1)) := by
  set L₁ := curValsV V h with hL₁
  set L₂ := (curValsV V kroots ++ flatBlksV Cv fo h) with hL₂
  set P1 : K → K → Prop := fun α γ =>
    ¬ IsForestFullBFT (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo kroots h ∧
      (nodeListP (fun i => rlc γ (V i)) h).eval α
        = (forestQueueP (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo kroots h).eval α
    with hP1
  set P2 : K → K → Prop := fun _α γ => γ ∈ BadRLCList L₁ L₂ with hP2
  have hsub : (Finset.univ.filter (fun p : K × K =>
      (∃ ln count acc : ℕ → K,
        WalkSat (fun i => rlc p.2 (V i)) (fun i l => rlc p.2 (Cv i l)) fo ln count acc
          p.1 (∑ i ∈ Finset.Icc 1 kroots, rlc p.2 (V i) * p.1 ^ i) (p.1 ^ kroots) h ∧ acc h = 0)
      ∧ ¬ ForestVecBFT V Cv fo kroots h))
      ⊆ Finset.univ.filter (fun p : K × K => P1 p.1 p.2)
        ∪ Finset.univ.filter (fun p : K × K => P2 p.1 p.2) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨⟨ln, count, acc, hw, hacc0⟩, hnotfix⟩ := hp.2
    have hseed : (∑ i ∈ Finset.Icc 1 kroots, rlc p.2 (V i) * p.1 ^ i)
        = (nodeListP (fun i => rlc p.2 (V i)) kroots).eval p.1 := by rw [nodeListP_eval]
    have heval := (forest_out_zero_iff hw hseed rfl).mp hacc0
    rw [Finset.mem_union]
    by_cases hbft : IsForestFullBFT (fun i => rlc p.2 (V i)) (fun i l => rlc p.2 (Cv i l)) fo kroots h
    · right
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show p.2 ∈ BadRLCList L₁ L₂
      by_contra hγ
      have hscalar := isForestFullBFT_curVals hlen hbft
      rw [curVals_rlc, curVals_rlc, flatBlks_rlc] at hscalar
      have hmap : L₁.map (rlc p.2) = L₂.map (rlc p.2) := by
        rw [hL₁, hL₂, List.map_append]; exact hscalar
      have hlen12 : L₁.length = L₂.length := by
        rw [hL₁, hL₂, curValsV_length, List.length_append, curValsV_length, flatBlksV_length]
        omega
      apply hnotfix
      show curValsV V h = curValsV V kroots ++ flatBlksV Cv fo h
      rw [← hL₁, ← hL₂]
      exact rlc_lift_list hlen12 hγ hmap
    · left
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hbft, heval⟩
  have hb1 : (Finset.univ.filter (fun p : K × K => P1 p.1 p.2)).card ≤ Fintype.card K * h := by
    refine le_trans (Finset.card_le_card (?_ : _ ⊆ Finset.univ.biUnion
        (fun γ : K => (Finset.univ.filter (fun α : K => P1 α γ)).image (fun α => (α, γ))))) ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_biUnion.mpr ⟨p.2, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩, rfl⟩⟩
    · refine le_trans Finset.card_biUnion_le ?_
      refine le_trans (Finset.sum_le_sum (fun γ _ => Finset.card_image_le)) ?_
      refine le_trans (Finset.sum_le_sum (g := fun _ => h) (fun γ (_ : γ ∈ Finset.univ) => ?_)) ?_
      · simp only [hP1]
        by_cases hbft : IsForestFullBFT (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo kroots h
        · have hemp : (Finset.univ.filter (fun α : K =>
              ¬ IsForestFullBFT (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo kroots h ∧
                (nodeListP (fun i => rlc γ (V i)) h).eval α
                  = (forestQueueP (fun i => rlc γ (V i)) (fun i l => rlc γ (Cv i l)) fo kroots h).eval α))
              = ∅ := by
            rw [Finset.filter_eq_empty_iff]; intro α _; rintro ⟨hn, _⟩; exact hn hbft
          rw [hemp]; simp
        · refine le_trans (Finset.card_le_card ?_) (forest_soundness_card hbft (by omega))
          intro α hα
          rw [Finset.mem_filter] at hα ⊢
          exact ⟨hα.1, hα.2.2⟩
      · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hb2 : (Finset.univ.filter (fun p : K × K => P2 p.1 p.2)).card
      ≤ Fintype.card K * (h * (node_size - 1)) := by
    refine le_trans (Finset.card_le_card (?_ : _ ⊆ Finset.univ.biUnion
        (fun α : K => (Finset.univ.filter (fun γ : K => P2 α γ)).image (fun γ => (α, γ))))) ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨p.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩, rfl⟩⟩
    · refine le_trans Finset.card_biUnion_le ?_
      refine le_trans (Finset.sum_le_sum (fun α _ => Finset.card_image_le)) ?_
      refine le_trans (Finset.sum_le_sum (g := fun _ => h * (node_size - 1))
        (fun α (_ : α ∈ Finset.univ) => ?_)) ?_
      · simp only [hP2]
        have hset : (Finset.univ.filter (fun γ : K => γ ∈ BadRLCList L₁ L₂))
            = BadRLCList L₁ L₂ := by ext γ; simp
        rw [hset]
        have hmin : min L₁.length L₂.length = h := by
          rw [hL₁, hL₂, curValsV_length, List.length_append, curValsV_length, flatBlksV_length]
          omega
        calc (BadRLCList L₁ L₂).card ≤ (min L₁.length L₂.length) * (node_size - 1) :=
              badRLCList_card_le L₁ L₂
          _ = h * (node_size - 1) := by rw [hmin]
      · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  calc _ ≤ (Finset.univ.filter (fun p : K × K => P1 p.1 p.2)
              ∪ Finset.univ.filter (fun p : K × K => P2 p.1 p.2)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun p : K × K => P1 p.1 p.2)).card
          + (Finset.univ.filter (fun p : K × K => P2 p.1 p.2)).card := Finset.card_union_le _ _
    _ ≤ Fintype.card K * h + Fintype.card K * (h * (node_size - 1)) := Nat.add_le_add hb1 hb2

/-- **`Corr:forest` composed soundness, probability form.**  `≤ h/|K| + ε_RLC`,
    `ε_RLC = h·(node_size − 1)/|K|` (the paper's statement gives only `h/|K|`). -/
theorem walk_IOP_forest_soundness_prob
    (V : ℕ → Fin node_size → K) (Cv : ℕ → ℕ → Fin node_size → K) (fo : ℕ → ℕ) {kroots h : ℕ}
    (hlen : kroots + Sf fo h = h) :
    ((Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (V i)) (fun i l => rlc p.2 (Cv i l)) fo ln count acc
            p.1 (∑ i ∈ Finset.Icc 1 kroots, rlc p.2 (V i) * p.1 ^ i) (p.1 ^ kroots) h ∧ acc h = 0)
        ∧ ¬ ForestVecBFT V Cv fo kroots h)).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (h : ℚ) / (Fintype.card K : ℚ)
          + ((h * (node_size - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  set m : ℕ := h * (node_size - 1) with hm
  have hpos : (0 : ℚ) < (Fintype.card K : ℚ) := by
    haveI : Nonempty K := ⟨0⟩; exact_mod_cast Fintype.card_pos
  have hK : (Fintype.card K : ℚ) ≠ 0 := ne_of_gt hpos
  have hpos2 : (0 : ℚ) < (Fintype.card K : ℚ) * (Fintype.card K : ℚ) := by positivity
  have hcard : ((Finset.univ.filter (fun p : K × K =>
      (∃ ln count acc : ℕ → K,
        WalkSat (fun i => rlc p.2 (V i)) (fun i l => rlc p.2 (Cv i l)) fo ln count acc
          p.1 (∑ i ∈ Finset.Icc 1 kroots, rlc p.2 (V i) * p.1 ^ i) (p.1 ^ kroots) h ∧ acc h = 0)
      ∧ ¬ ForestVecBFT V Cv fo kroots h)).card : ℚ)
      ≤ (Fintype.card K : ℚ) * h + (Fintype.card K : ℚ) * m := by
    exact_mod_cast walk_IOP_forest_soundness_card V Cv fo hlen
  rw [div_le_iff₀ hpos2]
  refine le_trans hcard (le_of_eq ?_)
  field_simp

end ForestComposeCard

/-! ### Multi-root inverse-BFS reconstruction -/

section ForestReconstruct
variable {LT : Type*}

theorem firstCF_one (kroots : ℕ) (fo : ℕ → ℕ) : firstCF kroots fo 1 = kroots + 1 := by
  simp [firstCF, Sf_zero]

/-- Contiguous tiling: node `i`'s children start right where node `i−1`'s children end. -/
theorem firstCF_succ (kroots : ℕ) (fo : ℕ → ℕ) {i : ℕ} (hi : 1 ≤ i) :
    firstCF kroots fo (i + 1) = firstCF kroots fo i + fo i := by
  have hj : i - 1 + 1 = i := by omega
  have h2 : Sf fo i = Sf fo (i - 1) + fo i := by
    conv_lhs => rw [← hj]
    rw [Sf_succ, hj]
  unfold firstCF
  rw [Nat.add_sub_cancel]
  omega

/-- **Queue-validity of a fanout column for a `kroots`-root forest.**  Node `i` has already been
    queued by the time nodes `1..i−1` are processed: `i ≤ kroots + Σ_{m<i}fanout`.  Equivalent to
    `firstCF i > i` (children strictly later in aggregate BFS) — acyclicity. -/
def BFSValidF (kroots : ℕ) (fo : ℕ → ℕ) (h : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ h → i ≤ kroots + Sf fo (i - 1)

/-- Every row of a nonempty BFS forest has been queued by its preceding rows. -/
private theorem bfsForest_queueF_aux (n : ℕ) :
    ∀ (l : List (NTree LT)), totalSize l ≤ n → l ≠ [] →
      ∀ k, k + 1 ≤ (bfsForest l).length →
        k + 1 ≤ l.length + (((bfsForest l).take k).flatMap NTree.children).length := by
  induction n with
  | zero =>
    intro l hn hne
    cases l with
    | nil => exact absurd rfl hne
    | cons t rest =>
      have ht : 1 ≤ t.size := by cases t with | node _ _ => simp [NTree.size]
      rw [totalSize_cons] at hn
      omega
  | succ m ih =>
    intro l hn hne k hk
    have hstep : bfsForest l = l ++ bfsForest (l.flatMap NTree.children) :=
      bfsForest_cons_eq l hne
    set C := l.flatMap NTree.children with hC
    set W' := bfsForest C with hW'
    have hWlen : (bfsForest l).length = l.length + W'.length := by
      rw [hstep, List.length_append]
    by_cases hkle : k ≤ l.length
    · rw [hstep, List.take_append_of_le_length hkle]
      by_cases hklt : k < l.length
      · omega
      · have hkeq : k = l.length := le_antisymm hkle (not_lt.mp hklt)
        subst hkeq
        rw [List.take_length]
        have hW'pos : 1 ≤ W'.length := by rw [hWlen] at hk; omega
        have hCne : C ≠ [] := by
          intro hCnil
          rw [hW', hCnil, bfsForest_nil] at hW'pos
          simp at hW'pos
        have hCpos : 1 ≤ C.length := List.length_pos_of_ne_nil hCne
        change l.length + 1 ≤ l.length + C.length
        omega
    · have hkgt : l.length < k := not_le.mp hkle
      rw [hstep, List.take_append, List.flatMap_append, List.length_append]
      rw [List.take_of_length_le (le_of_lt hkgt)]
      have hClen : (l.flatMap NTree.children).length = C.length := rfl
      have hCne : C ≠ [] := by
        have hW'pos : 1 ≤ W'.length := by rw [hWlen] at hk; omega
        intro hCnil
        rw [hW', hCnil, bfsForest_nil] at hW'pos
        simp at hW'pos
      have htsC : totalSize C ≤ m := by
        have hts := totalSize_flatMap_children l
        have hlpos : 1 ≤ l.length := List.length_pos_of_ne_nil hne
        rw [← hC] at hts
        omega
      have hk' : (k - l.length) + 1 ≤ W'.length := by rw [hWlen] at hk; omega
      have hq := ih C htsC hCne (k - l.length) (by rw [← hW']; exact hk')
      rw [← hW'] at hq
      rw [hClen]
      omega

/-- The fanout column of any nonempty honest BFS forest satisfies multi-root queue validity. -/
theorem foCol_BFSValidF (l : List (NTree LT)) (hl : l ≠ []) :
    BFSValidF l.length (foCol (bfsForest l)) (bfsForest l).length := by
  intro i hi hih
  rw [Sf_foCol]
  have hq := bfsForest_queueF_aux (totalSize l) l le_rfl hl (i - 1) (by omega)
  simpa [show i - 1 + 1 = i by omega] using hq

/-- The fanout column of any nonempty honest BFS forest exactly tiles its BFS rows. -/
theorem foCol_Sf_tilingF (l : List (NTree LT)) (hl : l ≠ []) :
    l.length + Sf (foCol (bfsForest l)) (bfsForest l).length =
      (bfsForest l).length := by
  rw [Sf_foCol, List.take_length]
  have hq := bfsForest_eq_append_flatMap l hl
  have := congrArg List.length hq
  simpa using this.symm

/-- **#5 discharge (soundness direction), forest.**  The queue-length gate with initial size
    `kroots` ⟹ `BFSValidF` — a cheating non-BFS forest fanout column cannot produce a `q`/`qinv`
    satisfying `QGate … kroots …`, so the gate rejects it. -/
theorem bfsValidF_of_qgate {K : Type*} [Field K] {fo : ℕ → ℕ} {q qinv : ℕ → K} {kroots h : ℕ}
    (hk : 1 ≤ kroots) (hq : QGate fo q qinv kroots h) : BFSValidF kroots fo h := by
  intro i hi1 hih
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simpa using qgate_bfsValidGen hq hk k (by omega)

/-- **#5 discharge (soundness direction), forest tiling.**  The terminal gate ⟹ `kroots + Sf fo h
    = h`, given the no-wraparound bound. -/
theorem SfF_tiling_of_qgate {K : Type*} [Field K] {p : ℕ} [CharP K p] {fo : ℕ → ℕ}
    {q qinv : ℕ → K} {kroots h : ℕ} (hq : QGate fo q qinv kroots h)
    (hb1 : kroots + Sf fo h < p) (hb2 : h < p) : kroots + Sf fo h = h :=
  qgate_tilingGen hq hb1 hb2

/-- Child indices of node `i` in the forest layout, filtered to strictly-later in-range
    positions (makes `buildTF` well-founded unconditionally; a no-op under `BFSValidF`). -/
def childIdxsF (kroots : ℕ) (fo : ℕ → ℕ) (h i : ℕ) : List ℕ :=
  (List.range' (firstCF kroots fo i) (fo i)).filter (fun j => decide (i < j ∧ j ≤ h))

/-- **Reconstructed subtree rooted at aggregate-BFS-position `i`** in a `kroots`-root forest. -/
def buildTF (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → LT) (h : ℕ) : ℕ → NTree LT := fun i =>
  NTree.node (lbl i) ((childIdxsF kroots fo h i).attach.map (fun j => buildTF kroots fo lbl h j.1))
termination_by i => h - i
decreasing_by
  · have hj := j.2
    simp only [childIdxsF, List.mem_filter, decide_eq_true_eq] at hj
    omega

@[simp] theorem buildTF_label (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → LT) (h i : ℕ) :
    (buildTF kroots fo lbl h i).label = lbl i := by
  rw [buildTF, NTree.label_node]

theorem buildTF_children (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → LT) (h i : ℕ) :
    (buildTF kroots fo lbl h i).children = (childIdxsF kroots fo h i).map (buildTF kroots fo lbl h) := by
  rw [buildTF, NTree.children_node, List.attach_map_val]

/-- Under `BFSValidF` and `1 ≤ i ≤ h`, the child-index filter is a no-op. -/
theorem childIdxsF_eq (kroots : ℕ) (fo : ℕ → ℕ) (h : ℕ) (hSf : kroots + Sf fo h = h)
    (hvalid : BFSValidF kroots fo h) {i : ℕ} (hi1 : 1 ≤ i) (hih : i ≤ h) :
    childIdxsF kroots fo h i = List.range' (firstCF kroots fo i) (fo i) := by
  unfold childIdxsF
  rw [List.filter_eq_self]
  intro j hj
  rw [List.mem_range'] at hj
  obtain ⟨kk, hkk, hjk⟩ := hj
  have hval := hvalid i hi1 hih
  have hfc : firstCF kroots fo i = kroots + 1 + Sf fo (i - 1) := rfl
  have hsfi : Sf fo i = Sf fo (i - 1) + fo i := by
    have hj' : i - 1 + 1 = i := by omega
    conv_lhs => rw [← hj']
    rw [Sf_succ, hj']
  have hmono : Sf fo i ≤ Sf fo h := Sf_mono fo hih
  rw [decide_eq_true_eq]
  omega

/-- **Contiguous tiling of the children blocks (forest).**  Flattening the child ranges of a
    contiguous block `[a, a+len)` yields the single contiguous range of all their children. -/
theorem tilingF (kroots : ℕ) (fo : ℕ → ℕ) :
    ∀ (len a : ℕ), 1 ≤ a →
      (List.range' a len).flatMap (fun i => List.range' (firstCF kroots fo i) (fo i))
        = List.range' (firstCF kroots fo a) (firstCF kroots fo (a + len) - firstCF kroots fo a) := by
  intro len
  induction len with
  | zero => intro a _; simp
  | succ m ih =>
    intro a ha
    rw [List.range'_succ, List.flatMap_cons, ih (a + 1) (by omega),
      firstCF_succ kroots fo ha, range'_append_one]
    have haeq : a + 1 + m = a + (m + 1) := by omega
    rw [haeq]
    have hle : firstCF kroots fo a + fo a ≤ firstCF kroots fo (a + (m + 1)) := by
      rw [← firstCF_succ kroots fo ha]
      unfold firstCF
      have : Sf fo (a + 1 - 1) ≤ Sf fo (a + (m + 1) - 1) := Sf_mono fo (by omega)
      omega
    have hlen_eq :
        fo a + (firstCF kroots fo (a + (m + 1)) - (firstCF kroots fo a + fo a))
          = firstCF kroots fo (a + (m + 1)) - firstCF kroots fo a := by omega
    rw [hlen_eq]

/-- **Round-trip invariant (forest inverse-BFS).**  For a queue-consistent frontier starting at
    `a` (of length `firstCF a − a`), the aggregate level-order flatten of the reconstructed
    subtrees equals the subtrees at positions `[a, h]`.  Strong induction on `h + 1 − a`. -/
theorem recon_bfs_auxF (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → LT) (h : ℕ)
    (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h) :
    ∀ (d a : ℕ), h + 1 - a = d → 1 ≤ a → a ≤ h + 1 →
      bfsForest ((List.range' a (firstCF kroots fo a - a)).map (buildTF kroots fo lbl h))
        = (List.range' a (h + 1 - a)).map (buildTF kroots fo lbl h) := by
  have hh : 1 ≤ h := by omega
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a hd ha1 hah
    by_cases hae : a = h + 1
    · subst hae
      have hfc : firstCF kroots fo (h + 1) = h + 1 := by
        unfold firstCF; rw [Nat.add_sub_cancel]; omega
      rw [hfc]
      simp [bfsForest_nil]
    · have hale : a ≤ h := by omega
      have hval := hvalid a ha1 hale
      have hfc : firstCF kroots fo a = kroots + 1 + Sf fo (a - 1) := rfl
      have hlen1 : 1 ≤ firstCF kroots fo a - a := by omega
      set len := firstCF kroots fo a - a with hlendef
      have hne : ((List.range' a len).map (buildTF kroots fo lbl h)) ≠ [] := by
        rw [ne_eq, List.map_eq_nil_iff]
        intro hnil
        have : (List.range' a len).length = 0 := by rw [hnil]; rfl
        rw [List.length_range'] at this; omega
      rw [bfsForest_cons_eq _ hne]
      have hpoint : ∀ i ∈ List.range' a len,
          NTree.children (buildTF kroots fo lbl h i)
            = (List.range' (firstCF kroots fo i) (fo i)).map (buildTF kroots fo lbl h) := by
        intro i hi
        rw [List.mem_range'] at hi
        obtain ⟨kk, hkk, hik⟩ := hi
        have hi1 : 1 ≤ i := by omega
        have hih : i ≤ h := by
          have hmono : Sf fo (a - 1) ≤ Sf fo h := Sf_mono fo (by omega)
          omega
        rw [buildTF_children, childIdxsF_eq kroots fo h hSf hvalid hi1 hih]
      have hchild : ((List.range' a len).map (buildTF kroots fo lbl h)).flatMap NTree.children
          = (List.range' (firstCF kroots fo a)
              (firstCF kroots fo (firstCF kroots fo a) - firstCF kroots fo a)).map
              (buildTF kroots fo lbl h) := by
        rw [List.flatMap_map, List.flatMap_congr hpoint, ← List.map_flatMap,
          tilingF kroots fo len a ha1]
        have ha'eq : a + len = firstCF kroots fo a := by omega
        rw [ha'eq]
      rw [hchild]
      have ha' : firstCF kroots fo a = a + len := by omega
      have ha'le : firstCF kroots fo a ≤ h + 1 := by
        have hmono : Sf fo (a - 1) ≤ Sf fo h := Sf_mono fo (by omega)
        omega
      have hlt : h + 1 - firstCF kroots fo a < d := by omega
      have hIH := ih (h + 1 - firstCF kroots fo a) hlt (firstCF kroots fo a) rfl (by omega) ha'le
      rw [hIH]
      rw [← List.map_append]
      rw [ha']
      rw [range'_append_one]
      congr 2
      omega

/-- **The reconstructed forest** `(slt₁,…,slt_kroots)` from the committed aggregate-BFS layout. -/
def reconForest (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → LT) (h : ℕ) : List (NTree LT) :=
  (List.range' 1 kroots).map (buildTF kroots fo lbl h)

/-- **FOREST INVERSE-BFS ROUND-TRIP.**  The aggregate level-order flatten of
    the reconstructed forest reproduces exactly the committed node list `[node 1,…,node h]`. -/
theorem bfsForest_reconForest (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → LT) (h : ℕ)
    (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h) :
    bfsForest (reconForest kroots fo lbl h) = (List.range' 1 h).map (buildTF kroots fo lbl h) := by
  have key := recon_bfs_auxF kroots fo lbl h hk hSf hvalid (h + 1 - 1) 1 rfl le_rfl (by omega)
  rw [firstCF_one] at key
  have hkk : kroots + 1 - 1 = kroots := by omega
  rw [hkk] at key
  have hhh : h + 1 - 1 = h := by omega
  rw [hhh] at key
  rw [reconForest]
  exact key

/-- The aggregate BFS labels of the reconstructed forest are the committed row labels. -/
theorem reconForest_labels (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → LT) (h : ℕ)
    (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h) :
    (bfsForest (reconForest kroots fo lbl h)).map NTree.label = (List.range' 1 h).map lbl := by
  rw [bfsForest_reconForest kroots fo lbl h hk hSf hvalid, List.map_map]
  apply List.map_congr_left
  intro i _
  simp

/-- The `j`-th child-label of a reconstructed forest node. -/
theorem buildTF_childLabel (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → LT) (h : ℕ)
    (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h)
    {i : ℕ} (hi1 : 1 ≤ i) (hih : i ≤ h) (j : ℕ) :
    (buildTF kroots fo lbl h i).childLabel j
      = if j < fo i then some (lbl (firstCF kroots fo i + j)) else none := by
  unfold NTree.childLabel NTree.childOpt
  rw [buildTF_children, childIdxsF_eq kroots fo h hSf hvalid hi1 hih, List.getElem?_map]
  by_cases hj : j < fo i
  · rw [List.getElem?_range' hj]
    simp only [Nat.one_mul, Option.map_some, buildTF_label, if_pos hj]
  · rw [List.getElem?_eq_none (by rw [List.length_range']; omega)]
    simp only [Option.map_none, if_neg hj]

/-- `isLeaf` of a reconstructed forest node ⟺ its fanout is `0`. -/
theorem buildTF_isLeaf (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → LT) (h : ℕ)
    (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h)
    {i : ℕ} (hi1 : 1 ≤ i) (hih : i ≤ h) :
    (buildTF kroots fo lbl h i).isLeaf ↔ fo i = 0 := by
  unfold NTree.isLeaf
  rw [buildTF_children, childIdxsF_eq kroots fo h hSf hvalid hi1 hih, List.map_eq_nil_iff]
  constructor
  · intro he
    have hl : (List.range' (firstCF kroots fo i) (fo i)).length = 0 := by rw [he]; rfl
    rw [List.length_range'] at hl; exact hl
  · intro h0; rw [h0]; rfl

end ForestReconstruct

/-! ### Lifting the reconstructed forest to `∏ L_RVT^{F,n}` -/

section ForestReconstructRVT
variable {S DT : Type*} {n : ℕ} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}

/-- **Per-node `F`-constraint of a reconstructed forest node** (both `Def:RVT` clauses). -/
theorem Fcon_buildTF (St : StateSep F) (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → S × DT) (h : ℕ)
    (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hF : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (lbl (firstCF kroots fo i + j)) else none))
    {i : ℕ} (hi1 : 1 ≤ i) (hih : i ≤ h) :
    Fcon F (buildTF kroots fo lbl h i) := by
  have hlabel : (buildTF kroots fo lbl h i).label = lbl i := buildTF_label kroots fo lbl h i
  have hclab : (fun j : Fin n => (buildTF kroots fo lbl h i).childLabel ↑j)
      = (fun j : Fin n => if (j : ℕ) < fo i then some (lbl (firstCF kroots fo i + j)) else none) := by
    funext j; rw [buildTF_childLabel kroots fo lbl h hSf hvalid hi1 hih]
  refine ⟨?_, ?_⟩
  · rw [hlabel, hclab]; exact hF i hi1 hih
  · rw [hlabel, buildTF_isLeaf kroots fo lbl h hSf hvalid hi1 hih]
    constructor
    · intro h0
      have hf := hF i hi1 hih
      have hconst : (fun j : Fin n => if (j : ℕ) < fo i then some (lbl (firstCF kroots fo i + j)) else none)
          = (fun _ : Fin n => none) := by funext j; rw [h0]; simp
      rw [hconst] at hf; exact hf
    · intro hFnone
      by_contra hne
      have hpos : 0 < fo i := by omega
      have hn : 0 < n := lt_of_lt_of_le hpos (harity i)
      have hfoeq := hfo i hi1 hih
      have hF' : F ((lbl i).1, (lbl i).2) (fun _ : Fin n => none) := by
        rw [Prod.mk.eta]; exact hFnone
      have hdyn := St.dynamic (lbl i).1 (lbl i).2 (fun _ => none) hF' ⟨0, hn⟩
      simp only [ne_eq, not_true_eq_false, iff_false, not_lt, Nat.le_zero] at hdyn
      omega

/-- Every aggregate-BFS node of the reconstructed forest satisfies its `F`-constraint. -/
theorem reconForest_all_Fcon (St : StateSep F) (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → S × DT) (h : ℕ)
    (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h)
    (harity : ∀ i, fo i ≤ n) (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hF : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (lbl (firstCF kroots fo i + j)) else none)) :
    ∀ t ∈ bfsForest (reconForest kroots fo lbl h), Fcon F t := by
  intro t ht
  rw [bfsForest_reconForest kroots fo lbl h hk hSf hvalid, List.mem_map] at ht
  obtain ⟨i, hi, rfl⟩ := ht
  rw [List.mem_range'] at hi
  obtain ⟨kk, hkk, hik⟩ := hi
  exact Fcon_buildTF St kroots fo lbl h hSf hvalid harity hfo hF (by omega) (by omega)

/-- **THE FOREST INVERSE-BFS LIFT.**  Each reconstructed tree is in
    `L_RVT^{F,n}`.  Deterministic, axiom-free: reduce membership per root to the per-node
    `F`-constraints (`RVT_iff_walk_Fcon`), which hold for every aggregate-BFS node
    (`reconForest_all_Fcon`) since each root's subtree nodes lie in the aggregate BFS. -/
theorem reconForest_RVT (St : StateSep F) (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → S × DT) (h : ℕ)
    (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h)
    (harity : ∀ i, fo i ≤ n) (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hF : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (lbl (firstCF kroots fo i + j)) else none)) :
    ∀ t ∈ reconForest kroots fo lbl h, RVT F t := by
  intro t ht
  have hall := reconForest_all_Fcon St kroots fo lbl h hk hSf hvalid harity hfo hF
  rw [reconForest, List.mem_map] at ht
  obtain ⟨r, hr, rfl⟩ := ht
  rw [RVT_iff_walk_Fcon]
  intro s hs
  apply hall s
  rw [mem_bfsForest] at hs ⊢
  obtain ⟨c, hc, hcs⟩ := hs
  rw [List.mem_singleton] at hc; subst hc
  refine ⟨buildTF kroots fo lbl h r, ?_, hcs⟩
  rw [reconForest, List.mem_map]
  exact ⟨r, hr, rfl⟩

/-- **Certified state-data-separation bindings for the reconstructed forest.** -/
theorem reconForest_bindings (St : StateSep F) (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → S × DT) (h : ℕ)
    (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h)
    (harity : ∀ i, fo i ≤ n)
    (hrvtall : ∀ t ∈ reconForest kroots fo lbl h, RVT F t) :
    (∀ t ∈ bfsForest (reconForest kroots fo lbl h), St.fanout (NTree.label t).1 = t.children.length) ∧
      (∀ t ∈ bfsForest (reconForest kroots fo lbl h), t.isLeaf ↔ St.Sleaf (NTree.label t).1) := by
  have key : ∀ t ∈ bfsForest (reconForest kroots fo lbl h),
      St.fanout (NTree.label t).1 = t.children.length ∧
        (t.isLeaf ↔ St.Sleaf (NTree.label t).1) := by
    intro t ht
    obtain ⟨c, hc, hct⟩ := (mem_bfsForest (reconForest kroots fo lbl h) t).mp ht
    have hcrvt := hrvtall c hc
    rw [bfsForest_reconForest kroots fo lbl h hk hSf hvalid, List.mem_map] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    rw [List.mem_range'] at hi
    obtain ⟨kk, hkk, hik⟩ := hi
    have hi1 : 1 ≤ i := by omega
    have hih : i ≤ h := by omega
    have hchlen : (buildTF kroots fo lbl h i).children.length = fo i := by
      rw [buildTF_children, childIdxsF_eq kroots fo h hSf hvalid hi1 hih, List.length_map,
        List.length_range']
    have hproper : (buildTF kroots fo lbl h i).children.length ≤ n := by rw [hchlen]; exact harity i
    exact ⟨fanout_eq_children_length St hcrvt hct hproper,
      (walk_leaf_iff_Sleaf St hcrvt hct).1⟩
  exact ⟨fun t ht => (key t ht).1, fun t ht => (key t ht).2⟩

/-- **The reconstructed forest lands in `L_SLT^n` (`ProperArity n`).**  Every reconstructed tree is
    a genuine `n`-ary tree: each node's child count is `fo i ≤ n` (`harity`).  Hence the walk
    reconstruction produces trees in the FAITHFUL language `{t // RVT F t ∧ ProperArity n t}`, not merely the strictly-larger `{t // RVT F t}`
    — so the arity refinement costs no soundness/completeness (the good event still holds). -/
theorem reconForest_properArity (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → S × DT) (h : ℕ)
    (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h)
    (harity : ∀ i, fo i ≤ n) :
    ∀ t ∈ reconForest kroots fo lbl h, ProperArity n t := by
  intro t ht s hs
  have hmem : s ∈ bfsForest (reconForest kroots fo lbl h) :=
    (mem_bfsForest (reconForest kroots fo lbl h) s).mpr ⟨t, ht, hs⟩
  rw [bfsForest_reconForest kroots fo lbl h hk hSf hvalid, List.mem_map] at hmem
  obtain ⟨i, hi, rfl⟩ := hmem
  rw [List.mem_range'] at hi
  obtain ⟨kk, hkk, hik⟩ := hi
  have hi1 : 1 ≤ i := by omega
  have hih : i ≤ h := by omega
  rw [buildTF_children, childIdxsF_eq kroots fo h hSf hvalid hi1 hih, List.length_map,
    List.length_range']
  exact harity i

end ForestReconstructRVT

/-! ### The literal `Corr:forest` conclusion `∃ (sltᵢ) ∈ ∏ L_RVT^{F,n}` -/

section ForestComposeRVT
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {node_size n : ℕ}
variable {S DT : Type*} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}

/-- **The literal `Corr:forest` conclusion:** there is a list of `kroots` trees,
    each in `L_RVT^{F,n}`, whose AGGREGATE breadth-first traversal reproduces the committed rows,
    with `StateSep`-bound fanout/leaf structure.  `α`/`γ`-independent.  This genuinely asserts
    `(sltᵢ)_{i=1}^{kroots} ∈ ∏_{i=1}^{kroots} L_RVT^{F,n}` (the forest length is exactly `kroots`,
    the aggregate BFS is exactly the `h` committed rows). -/
def ForestReconGoal (St : StateSep F) (lbl : ℕ → S × DT) (kroots h : ℕ) : Prop :=
  ∃ ts : List (NTree (S × DT)), ts.length = kroots ∧ (∀ t ∈ ts, RVT F t) ∧
    (bfsForest ts).map NTree.label = (List.range' 1 h).map lbl ∧
    (∀ t ∈ bfsForest ts, St.fanout (NTree.label t).1 = t.children.length) ∧
    (∀ t ∈ bfsForest ts, t.isLeaf ↔ St.Sleaf (NTree.label t).1)

/-- **ForestVecBFT ⟹ committed children are the aggregate-BFS-layout nodes.**  `Cv i (l+1)` equals
    the node vector `V (firstCF i + l)` at the corresponding aggregate BFS position. -/
theorem ForestVecBFT_layout (V : ℕ → Fin node_size → K) (Cv : ℕ → ℕ → Fin node_size → K)
    (fo : ℕ → ℕ) {kroots h : ℕ} (hSf : kroots + Sf fo h = h)
    (hbft : ForestVecBFT V Cv fo kroots h) {i l : ℕ} (hi1 : 1 ≤ i) (hih : i ≤ h) (hl : l < fo i) :
    Cv i (l + 1) = V (firstCF kroots fo i + l) := by
  have hsfi := Sf_split fo hi1
  have hmono : Sf fo i ≤ Sf fo h := Sf_mono fo hih
  have hidx : kroots + Sf fo (i - 1) + l < h := by omega
  have e1 : (curValsV V h)[kroots + Sf fo (i - 1) + l]?
      = some (V (kroots + Sf fo (i - 1) + l + 1)) := curValsV_getElem? V hidx
  rw [hbft] at e1
  have hge : (curValsV V kroots).length ≤ kroots + Sf fo (i - 1) + l := by
    rw [curValsV_length]; omega
  rw [List.getElem?_append_right hge, curValsV_length] at e1
  have hidx2 : kroots + Sf fo (i - 1) + l - kroots = Sf fo (i - 1) + l := by omega
  rw [hidx2, flatBlksV_getElem? Cv fo h i l hi1 hih hl] at e1
  rw [Option.some.injEq] at e1
  rw [e1]; congr 1; unfold firstCF; omega

/-- Under the committed `F`-constraints + `StateSep` + queue-validity, the aggregate vector-BFT
    fixpoint yields the full literal forest goal. -/
theorem reconForest_ForestReconGoal (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {kroots h : ℕ} (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h)
    (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none))
    (hbft : ForestVecBFT (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo kroots h) :
    ForestReconGoal St lbl kroots h := by
  have hF : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (lbl (firstCF kroots fo i + j)) else none) := by
    intro i hi1 hih
    have hfun : (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)
        = (fun j : Fin n => if (j : ℕ) < fo i then some (lbl (firstCF kroots fo i + j)) else none) := by
      funext j
      by_cases hj : (j : ℕ) < fo i
      · have hkey := ForestVecBFT_layout (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo hSf hbft
          hi1 hih hj
        rw [if_pos hj, if_pos hj, hEnc hkey]
      · rw [if_neg hj, if_neg hj]
    rw [← hfun]; exact hFcommit i hi1 hih
  have hrvtall := reconForest_RVT St kroots fo lbl h hk hSf hvalid harity hfo hF
  have hbind := reconForest_bindings St kroots fo lbl h hk hSf hvalid harity hrvtall
  refine ⟨reconForest kroots fo lbl h, ?_, hrvtall,
    reconForest_labels kroots fo lbl h hk hSf hvalid, hbind.1, hbind.2⟩
  rw [reconForest, List.length_map, List.length_range']

/-- **`Corr:forest` — LITERAL soundness, cardinality form.**  For committed row
    labels `lbl` and child labels `clab` (encoded into `𝔽^{node_size}` by an injective `enc`), a
    queue-valid `kroots`-root forest fanout column (`kroots + Sf fo h = h`, `BFSValidF`, `fo ≤ n`,
    state-defined via `St.fanout`) and the per-row `F`-constraints, the number of challenge pairs
    `(α,γ)` for which the walk gates accept (`out_walk = 0`) with the FOREST recognizer inputs YET
    the literal goal `∃ (sltᵢ)_{i=1}^{kroots} ∈ ∏ L_RVT^{F,n}` (`ForestReconGoal`) FAILS is
    `≤ |K|·h + |K|·(h·(node_size−1))` — probability `≤ h/|K| + ε_RLC`. -/
theorem Walk_IOP_forest_final_card (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {kroots h : ℕ} (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h)
    (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    (Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
            ln count acc p.1 (∑ i ∈ Finset.Icc 1 kroots, rlc p.2 (enc (lbl i)) * p.1 ^ i)
            (p.1 ^ kroots) h ∧ acc h = 0)
        ∧ ¬ ForestReconGoal St lbl kroots h)).card
      ≤ Fintype.card K * h + Fintype.card K * (h * (node_size - 1)) := by
  refine le_trans (Finset.card_le_card ?_)
    (walk_IOP_forest_soundness_card (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo hSf)
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, hp.2.1, ?_⟩
  intro hbft
  exact hp.2.2 (reconForest_ForestReconGoal St enc hEnc lbl clab fo hk hSf hvalid harity hfo
    hFcommit hbft)

/-- **`Corr:forest` — LITERAL soundness, probability form.**  Over uniformly
    random challenges `(α,γ)`, the probability that the walk gates accept (FOREST inputs) while
    `∃ (sltᵢ)_{i=1}^{kroots} ∈ ∏ L_RVT^{F,n}` (`ForestReconGoal`) fails is `≤ h/|K| + ε_RLC`,
    `ε_RLC = h·(node_size − 1)/|K|`. -/
theorem Walk_IOP_forest_final_prob (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {kroots h : ℕ} (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h)
    (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    ((Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
            ln count acc p.1 (∑ i ∈ Finset.Icc 1 kroots, rlc p.2 (enc (lbl i)) * p.1 ^ i)
            (p.1 ^ kroots) h ∧ acc h = 0)
        ∧ ¬ ForestReconGoal St lbl kroots h)).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (h : ℚ) / (Fintype.card K : ℚ)
          + ((h * (node_size - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  have hpos2 : (0 : ℚ) < (Fintype.card K : ℚ) * (Fintype.card K : ℚ) := by
    haveI : Nonempty K := ⟨0⟩
    have : (0 : ℚ) < (Fintype.card K : ℚ) := by exact_mod_cast Fintype.card_pos
    positivity
  have hcard := Walk_IOP_forest_final_card St enc hEnc lbl clab fo hk hSf hvalid harity hfo hFcommit
  have hcast : ((Finset.univ.filter (fun p : K × K =>
      (∃ ln count acc : ℕ → K,
        WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
          ln count acc p.1 (∑ i ∈ Finset.Icc 1 kroots, rlc p.2 (enc (lbl i)) * p.1 ^ i)
          (p.1 ^ kroots) h ∧ acc h = 0)
      ∧ ¬ ForestReconGoal St lbl kroots h)).card : ℚ)
      ≤ (Fintype.card K : ℚ) * h + (Fintype.card K : ℚ) * (h * (node_size - 1) : ℕ) := by
    exact_mod_cast hcard
  rw [div_le_iff₀ hpos2]
  refine le_trans hcast (le_of_eq ?_)
  field_simp

/-! ### Sanity: the single-root theorem is recovered at `kroots = 1` -/

/-- **Sanity corollary (kroots = 1).**  A one-tree forest goal is exactly the single-tree
    `ReconGoal` — the forest statement is a strict generalisation, not a weakening. -/
theorem ForestReconGoal_one (St : StateSep F) (lbl : ℕ → S × DT) (h : ℕ) :
    ForestReconGoal St lbl 1 h ↔ ReconGoal St lbl h := by
  unfold ForestReconGoal ReconGoal
  constructor
  · rintro ⟨ts, hlen, hrvt, hlab, hfan, hleaf⟩
    obtain ⟨slt, rfl⟩ := List.length_eq_one_iff.mp hlen
    exact ⟨slt, hrvt slt (List.mem_singleton.mpr rfl), hlab, hfan, hleaf⟩
  · rintro ⟨slt, hrvt, hlab, hfan, hleaf⟩
    refine ⟨[slt], rfl, ?_, hlab, hfan, hleaf⟩
    intro t ht; rw [List.mem_singleton] at ht; subst ht; exact hrvt

/-- **The single-root `Walk_IOP_final_card` is the `kroots = 1` case of the forest
    theorem.**  Derives the single-tree bound from `Walk_IOP_forest_final_card` by collapsing the
    forest seed (`Σ_{i=1}^1 = RLC(lbl 1)·α`), `initial_count = α¹ = α`, and `ForestReconGoal 1 =
    ReconGoal`. -/
theorem Walk_IOP_final_card_of_forest (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    (Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
            ln count acc p.1 (rlc p.2 (enc (lbl 1)) * p.1) p.1 h ∧ acc h = 0)
        ∧ ¬ ReconGoal St lbl h)).card
      ≤ Fintype.card K * h + Fintype.card K * (h * (node_size - 1)) := by
  have hvalid1 : BFSValidF 1 fo h := hvalid
  have hSf1 : 1 + Sf fo h = h := by omega
  have hforest := Walk_IOP_forest_final_card St enc hEnc lbl clab fo (kroots := 1)
    (le_refl 1) hSf1 hvalid1 harity hfo hFcommit
  refine le_trans (le_of_eq ?_) hforest
  congr 1
  apply Finset.filter_congr
  intro p _
  have hseed_eq : (∑ i ∈ Finset.Icc 1 1, rlc p.2 (enc (lbl i)) * p.1 ^ i)
      = rlc p.2 (enc (lbl 1)) * p.1 := by
    rw [Finset.Icc_self, Finset.sum_singleton, pow_one]
  rw [hseed_eq, pow_one, ForestReconGoal_one]


theorem reconForest_ForestReconGoal_of_label {L : Type*} (St : StateSep F)
    (labelOf : S × DT → L) (hResp : RespectsChildLabels F labelOf)
    (enc : (S × DT) → (Fin node_size → K))
    (hEnc : ∀ a b, enc a = enc b → labelOf a = labelOf b)
    (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {kroots h : ℕ} (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h)
    (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none))
    (hbft : ForestVecBFT (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo kroots h) :
    ForestReconGoal St lbl kroots h := by
  have hF : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (lbl (firstCF kroots fo i + j)) else none) := by
    intro i hi1 hih
    refine hResp (lbl i) _ _ ?_ (hFcommit i hi1 hih)
    intro j
    by_cases hj : (j : ℕ) < fo i
    · have hkey := ForestVecBFT_layout (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo hSf hbft
        hi1 hih hj
      rw [if_pos hj, if_pos hj]
      simp only [Option.map_some]
      rw [hEnc _ _ hkey]
    · rw [if_neg hj, if_neg hj]
  have hrvtall := reconForest_RVT St kroots fo lbl h hk hSf hvalid harity hfo hF
  have hbind := reconForest_bindings St kroots fo lbl h hk hSf hvalid harity hrvtall
  refine ⟨reconForest kroots fo lbl h, ?_, hrvtall,
    reconForest_labels kroots fo lbl h hk hSf hvalid, hbind.1, hbind.2⟩
  rw [reconForest, List.length_map, List.length_range']

theorem Walk_IOP_forest_final_card_of_label {L : Type*} (St : StateSep F)
    (labelOf : S × DT → L) (hResp : RespectsChildLabels F labelOf)
    (enc : (S × DT) → (Fin node_size → K))
    (hEnc : ∀ a b, enc a = enc b → labelOf a = labelOf b)
    (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {kroots h : ℕ} (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h)
    (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    (Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
            ln count acc p.1 (∑ i ∈ Finset.Icc 1 kroots, rlc p.2 (enc (lbl i)) * p.1 ^ i)
            (p.1 ^ kroots) h ∧ acc h = 0)
        ∧ ¬ ForestReconGoal St lbl kroots h)).card
      ≤ Fintype.card K * h + Fintype.card K * (h * (node_size - 1)) := by
  refine le_trans (Finset.card_le_card ?_)
    (walk_IOP_forest_soundness_card (fun i => enc (lbl i)) (fun i l => enc (clab i l)) fo hSf)
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, hp.2.1, ?_⟩
  intro hbft
  exact hp.2.2 (reconForest_ForestReconGoal_of_label St labelOf hResp enc hEnc lbl clab fo hk hSf
    hvalid harity hfo hFcommit hbft)

theorem Walk_IOP_forest_final_prob_of_label {L : Type*} (St : StateSep F)
    (labelOf : S × DT → L) (hResp : RespectsChildLabels F labelOf)
    (enc : (S × DT) → (Fin node_size → K))
    (hEnc : ∀ a b, enc a = enc b → labelOf a = labelOf b)
    (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {kroots h : ℕ} (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h)
    (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    ((Finset.univ.filter (fun p : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
            ln count acc p.1 (∑ i ∈ Finset.Icc 1 kroots, rlc p.2 (enc (lbl i)) * p.1 ^ i)
            (p.1 ^ kroots) h ∧ acc h = 0)
        ∧ ¬ ForestReconGoal St lbl kroots h)).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (h : ℚ) / (Fintype.card K : ℚ)
          + ((h * (node_size - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  have hpos2 : (0 : ℚ) < (Fintype.card K : ℚ) * (Fintype.card K : ℚ) := by
    haveI : Nonempty K := ⟨0⟩
    have : (0 : ℚ) < (Fintype.card K : ℚ) := by exact_mod_cast Fintype.card_pos
    positivity
  have hcard := Walk_IOP_forest_final_card_of_label St labelOf hResp enc hEnc lbl clab fo hk hSf
    hvalid harity hfo hFcommit
  have hcast : ((Finset.univ.filter (fun p : K × K =>
      (∃ ln count acc : ℕ → K,
        WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
          ln count acc p.1 (∑ i ∈ Finset.Icc 1 kroots, rlc p.2 (enc (lbl i)) * p.1 ^ i)
          (p.1 ^ kroots) h ∧ acc h = 0)
      ∧ ¬ ForestReconGoal St lbl kroots h)).card : ℚ)
      ≤ (Fintype.card K : ℚ) * h + (Fintype.card K : ℚ) * (h * (node_size - 1) : ℕ) := by
    exact_mod_cast hcard
  rw [div_le_iff₀ hpos2]
  refine le_trans hcast (le_of_eq ?_)
  field_simp

end ForestComposeRVT

end Walk
end Nock
