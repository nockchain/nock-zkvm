/-
  Nock/NPR.lean

  The Noun Polynomial Representation (NPR) and its collision-soundness bounds.

  A noun `n = (dt, w)` is a leaf array `dt ∈ 𝔽^λ` together with a Dyck word
  `w ∈ {0,1}^{2(λ−1)}` fixing the tree shape.  We reuse the `Nock.Noun`/`Dyck`
  machinery: `Noun.leafList` (the leaves in DFS order, cast into the field via `Nat → K` —
  the ATOM MODEL (a) embedding, see `Nock/Field.lean`) supplies `dt`, and `Noun.dyckWord`
  (from `Nock/Dyck.lean`) supplies `w`.

  Contents:
  * `Φ` — the NPR: a noun ↦ triple of univariate polynomials
      `Φ(dt,w) = ( X^{|dt|},  Σ dtᵢ X^{i−1},  Σ wᵢ X^{i−1} )`.
  * `fn` — the fingerprint
      `fn(n; r) = Φ(dt,w)[r,r,r] = (r^{|dt|}, F_d(r), F_w(r))`, `r ∈ K`.
  * `collision_card_le` / `collision_prob_le` —
      distinct nouns collide under `fn` for at most `2(2Λ−1)` values of `r`, i.e. with
      probability `≤ 2(2Λ−1)/|K|`.  (Schwartz–Zippel / root counting.)
  * `collision_table_card_le` / `collision_table_prob_le` — union bound over `k` nouns: some pair collides with probability
      `≤ ε · k(k−1)/2`.

  GENERICITY.  Everything is proved over an ARBITRARY finite field `K` (`[Field K]
  [Fintype K] [DecidableEq K]`).  The concrete Goldilocks instantiation `K = 𝔽_p^3`
  lives in `Nock/Field.lean` and is applied at the end; only that instantiation depends
  on the flagged `goldilocks_prime` axiom.

  PROBABILITY CONVENTION.  "`Pr_{r∈K}[…]`" is formalized as the *counting measure*: the
  number of `r ∈ K` satisfying the event divided by `|K| = Fintype.card K`.  The core
  results are the exact cardinality bounds (`…_card_le`); the `…_prob_le` corollaries
  divide by `|K|` in `ℚ`.

  SCHWARTZ–ZIPPEL.  Univariate; we use `Polynomial.card_roots'`
  (`Multiset.card p.roots ≤ p.natDegree`) via `card_eval_zero_le`: a nonzero polynomial of
  natDegree `d` has at most `d` roots in `K`.
-/
import Nock.Dyck
import Nock.Field
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.List.GetD

open Polynomial

namespace Nock

/-! ### Leaf array of a noun (the paper's `dt`, in DFS order) -/

namespace Noun

/-- The leaf values of a noun in left-to-right (DFS) order — the paper's leaf array `dt`, here over `Nat` (cast into the field at the NPR layer). -/
def leafList : Noun → List Nat
  | .atom k   => [k]
  | .cell l r => l.leafList ++ r.leafList

@[simp] theorem leafList_length (n : Noun) : n.leafList.length = n.leaves := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp [leafList, leaves, ihl, ihr]

theorem one_le_leaves (n : Noun) : 1 ≤ n.leaves := by
  induction n with
  | atom k => simp [leaves]
  | cell l r ihl ihr => simp only [leaves]; omega

/-! ### Def "noun" uniqueness: `(dyckWord, leafList)` determines the noun

    The paper's Def "noun" defines a noun `n = (t, dt)` as a Dyck word `t`
    (the tree shape) together with a leaf array `dt`, and states that this tuple
    "corresponds to a **unique**" noun.  In our encoding
    `t = Noun.dyckWord` (`= shape.encode`, `Nock/Dyck.lean`) and `dt = Noun.leafList`
    (the DFS leaf array).  The paper's uniqueness is exactly the injectivity of
    `n ↦ (n.dyckWord, n.leafList)` — the content is that the Dyck shape plus the ordered
    leaves pin down the noun with no freedom left. -/

/-- Equal shape ⇒ equal leaf count: the Dyck shape already determines `λ`, so it constrains how the leaf array splits between the two subtrees. -/
theorem shape_leaves_eq {n₁ n₂ : Noun} (h : n₁.shape = n₂.shape) :
    n₁.leaves = n₂.leaves := by
  have hs : n₁.shape.size = n₂.shape.size := by rw [h]
  rw [shape_size, shape_size] at hs
  have e₁ := size_add_one n₁
  have e₂ := size_add_one n₂
  omega

/-- **Reconstruction.**  If two nouns have the same shape (Dyck word) and the same leaf
    array, they are the *same* noun: the shape fixes the tree structure and the leaf list
    fills the leaves in DFS order, leaving no ambiguity. -/
theorem eq_of_shape_leafList :
    ∀ {n₁ n₂ : Noun}, n₁.shape = n₂.shape → n₁.leafList = n₂.leafList → n₁ = n₂ := by
  intro n₁
  induction n₁ with
  | atom k₁ =>
      intro n₂ hshape hleaf
      cases n₂ with
      | atom k₂ =>
          simp only [leafList, List.cons.injEq, and_true] at hleaf; rw [hleaf]
      | cell l r => simp [shape] at hshape
  | cell l₁ r₁ ihl ihr =>
      intro n₂ hshape hleaf
      cases n₂ with
      | atom k₂ => simp [shape] at hshape
      | cell l₂ r₂ =>
          simp only [shape, BTree.node.injEq] at hshape
          obtain ⟨hsl, hsr⟩ := hshape
          simp only [leafList] at hleaf
          have hlen : l₁.leafList.length = l₂.leafList.length := by
            rw [leafList_length, leafList_length, shape_leaves_eq hsl]
          obtain ⟨hll, hrl⟩ := List.append_inj hleaf hlen
          rw [ihl hsl hll, ihr hsr hrl]

/-- **Def "noun" uniqueness.**  The map sending a noun to its Dyck word +
    leaf array, `n ↦ (n.dyckWord, n.leafList)`, is injective.  This is the paper's claim
    that the tuple `(t, dt)` "corresponds to a unique noun". -/
theorem noun_dyck_leaf_injective :
    Function.Injective (fun n : Noun => (n.dyckWord, n.leafList)) := by
  intro n₁ n₂ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hd, hl⟩ := h
  have hshape : n₁.shape = n₂.shape :=
    BTree.encode_injective (by simpa only [dyckWord] using hd)
  exact eq_of_shape_leafList hshape hl

end Noun

namespace NPR

/-! ### Coefficient-vector polynomials -/

section CPoly
variable {K : Type*} [Field K]

/-- `cpoly f n = Σ_{i<n} f i · X^i`: the polynomial with coefficient vector `(f 0,…,f (n−1))`. -/
noncomputable def cpoly (f : ℕ → K) (n : ℕ) : K[X] := ∑ i ∈ Finset.range n, C (f i) * X ^ i

theorem cpoly_coeff (f : ℕ → K) (n j : ℕ) :
    (cpoly f n).coeff j = if j < n then f j else 0 := by
  unfold cpoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range n) j f]
  simp [Finset.mem_range]

theorem cpoly_sub (f g : ℕ → K) (n : ℕ) :
    cpoly f n - cpoly g n = cpoly (fun i => f i - g i) n := by
  unfold cpoly
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← sub_mul, ← C_sub]

theorem cpoly_natDegree_le (f : ℕ → K) (n : ℕ) : (cpoly f n).natDegree ≤ n - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [cpoly_coeff]
  have : ¬ N < n := by omega
  simp [this]

theorem cpoly_ne_zero_of_coeff {f g : ℕ → K} {n j : ℕ} (hj : j < n) (h : f j ≠ g j) :
    cpoly f n - cpoly g n ≠ 0 := by
  rw [cpoly_sub]
  intro hzero
  apply h
  have hc : (cpoly (fun i => f i - g i) n).coeff j = f j - g j := by
    rw [cpoly_coeff]; simp [hj]
  rw [hzero, coeff_zero] at hc
  exact sub_eq_zero.mp hc.symm

end CPoly

/-! ### List-indexed polynomials -/

section ListPoly
variable {K : Type*} [Field K]

/-- The polynomial whose coefficient vector is the list `l` (default `0` past the end). -/
noncomputable def listPoly (l : List K) : K[X] :=
  cpoly (fun i => l.getD i 0) l.length

theorem listPoly_natDegree_le (l : List K) : (listPoly l).natDegree ≤ l.length - 1 :=
  cpoly_natDegree_le _ _

/-- Two equal-length lists that differ have distinct coefficient polynomials. -/
theorem listPoly_sub_ne_zero {l₁ l₂ : List K} (hlen : l₁.length = l₂.length) (hne : l₁ ≠ l₂) :
    listPoly l₁ - listPoly l₂ ≠ 0 := by
  -- find a position where they differ
  have hex : ∃ j, j < l₁.length ∧ l₁.getD j 0 ≠ l₂.getD j 0 := by
    by_contra h
    simp only [not_exists, not_and, ne_eq, not_not] at h
    apply hne
    apply List.ext_getElem hlen
    intro j hj hj2
    have hjeq := h j hj
    rwa [List.getD_eq_getElem l₁ 0 hj, List.getD_eq_getElem l₂ 0 (hlen ▸ hj)] at hjeq
  obtain ⟨j, hj, hval⟩ := hex
  unfold listPoly
  rw [hlen]
  exact cpoly_ne_zero_of_coeff (hlen ▸ hj) hval

theorem listPoly_sub_natDegree_le {l₁ l₂ : List K} (hlen : l₁.length = l₂.length) :
    (listPoly l₁ - listPoly l₂).natDegree ≤ l₁.length - 1 := by
  refine le_trans (natDegree_sub_le _ _) ?_
  rw [max_le_iff]
  exact ⟨listPoly_natDegree_le l₁, by rw [hlen]; exact listPoly_natDegree_le l₂⟩

/-! #### Concatenation identities for `listPoly` (the algebraic backbone of `Lem:NPR_decomp`).

    These express how a list-indexed polynomial factors when its coefficient list is split.
    They are what turn the DFS/Dyck concatenation of nouns under `cell` into the polynomial
    identities of `Lem:NPR_decomp`. -/

theorem listPoly_coeff (l : List K) (j : ℕ) :
    (listPoly l).coeff j = if j < l.length then l.getD j 0 else 0 := by
  unfold listPoly; rw [cpoly_coeff]

@[simp] theorem listPoly_nil : listPoly ([] : List K) = 0 := by
  unfold listPoly cpoly; simp

/-- `listPoly (x :: l) = C x + X · listPoly l`: prepending a coefficient shifts by one. -/
theorem listPoly_cons (x : K) (l : List K) :
    listPoly (x :: l) = C x + X * listPoly l := by
  ext j
  rw [coeff_add, listPoly_coeff]
  match j with
  | 0 =>
      rw [mul_coeff_zero, coeff_X_zero, zero_mul, add_zero, coeff_C_zero,
        List.getD_cons_zero]
      simp
  | k + 1 =>
      rw [coeff_X_mul, listPoly_coeff, coeff_C, List.getD_cons_succ, List.length_cons]
      simp

/-- **`listPoly (a ++ b) = listPoly a + X^{|a|} · listPoly b`** — the paper's stated
    concatenation rule: a coefficient list `a ++ b` gives the
    polynomial of `a` plus the polynomial of `b` shifted up by `|a|` places. -/
theorem listPoly_append (a b : List K) :
    listPoly (a ++ b) = listPoly a + X ^ a.length * listPoly b := by
  induction a with
  | nil => simp
  | cons x a' ih =>
      rw [List.cons_append, listPoly_cons, ih, listPoly_cons, List.length_cons, pow_succ]
      ring

end ListPoly

/-! ### The NPR and the fingerprint -/

section NPR
variable {K : Type*} [Field K]

/-- Leaf array `dt` cast into the field `K` (ATOM MODEL (a): `Nat → K`). -/
def leafF (n : Noun) : List K := n.leafList.map (fun k : ℕ => (k : K))

/-- Dyck word `w ∈ {0,1}*` cast into the field `K` (`0 ↦ 0`, `1 ↦ 1`). -/
def dyckBits (n : Noun) : List K := n.dyckWord.map (fun b => if b then (1 : K) else 0)

@[simp] theorem leafF_length (n : Noun) : (leafF (K := K) n).length = n.leaves := by
  simp [leafF]

theorem dyckBits_length (n : Noun) : (dyckBits (K := K) n).length + 2 = 2 * n.leaves := by
  simp only [dyckBits, List.length_map]
  exact n.dyckWord_length

/-- **The Noun Polynomial Representation.**
    `Φ(dt,w) = ( X₁^{|dt|},  Σ dtᵢ X₂^{i−1},  Σ wᵢ X₃^{i−1} )` — represented as a triple of
    univariate polynomials (each in its own indeterminate `X`). -/
noncomputable def Φ (n : Noun) : K[X] × K[X] × K[X] :=
  (X ^ n.leaves, listPoly (leafF n), listPoly (dyckBits n))

/-- **The fingerprint.**
    `fn(n; r) = Φ(dt,w)[r,r,r] = (r^{|dt|}, F_d(r), F_w(r))`, evaluated at `r ∈ K`. -/
noncomputable def fn (n : Noun) (r : K) : K × K × K :=
  (r ^ n.leaves, (listPoly (leafF n)).eval r, (listPoly (dyckBits n)).eval r)

/-- The fingerprint is `Φ` evaluated at `(r,r,r)`. -/
theorem fn_eq_Φ_eval (n : Noun) (r : K) :
    fn n r = ((Φ n).1.eval r, (Φ (K := K) n).2.1.eval r, (Φ n).2.2.eval r) := by
  simp [fn, Φ]

@[simp] theorem Φ_fst (n : Noun) : (Φ (K := K) n).1 = X ^ n.leaves := rfl
@[simp] theorem Φ_snd_fst (n : Noun) : (Φ (K := K) n).2.1 = listPoly (leafF n) := rfl
@[simp] theorem Φ_snd_snd (n : Noun) : (Φ (K := K) n).2.2 = listPoly (dyckBits n) := rfl

end NPR

/-! ### `Lem:NPR_decomp` — the memory-table backbone

    How the three NPR polynomials concatenate under `cons`.  We first record the two
    structural concatenation lemmas (leaf array in DFS order; Dyck word by the grammar
    `w = 0·w_L·1·w_R`), then read off the three `Φ`-identities.

    ⚠ **FAITHFULNESS — the Φ₃ (Dyck) exponents.**  The paper prints
        `Φ(n)₃ = Φ(nL)₃ + X^{2(λL−1)} + X^{2λL−1}·Φ(nR)₃`.
    Derived carefully against `Dyck.encode`'s grammar `w = 0·w_L·1·w_R` and the paper's own
    `F_w(X) = Σ_i w_i X^{i−1}` (`listPoly`), the CORRECT identity is
        `Φ(n)₃ = X·Φ(nL)₃ + X^{2λL−1} + X^{2λL}·Φ(nR)₃`.
    The paper's form is off by one global factor of `X` (equivalently: it drops the leading
    open-delimiter bit's `X`-shift), i.e. paper-RHS `= X⁻¹·(correct RHS)`.  Concretely, for
    `n = cons(atom,atom)` the Dyck word is `[0,1]`, so `F_w(n) = X`, which the correct
    identity yields (`X·0 + X^{2·1−1} + X^{2·1}·0 = X`) but the paper's yields `1`
    (`0 + X^{2(1−1)} + X^{2·1−1}·0`).  We prove and use the correct identity `Phi3_cons`
    and flag this deviation. -/

section Decomp
variable {K : Type*} [Field K]

/-- Leaf array concatenates under `cell` (DFS order). -/
@[simp] theorem leafF_cell (l r : Noun) :
    leafF (K := K) (Noun.cell l r) = leafF l ++ leafF r := by
  simp [leafF, Noun.leafList]

/-- Dyck word under `cell`: `w = 0 · w_L · 1 · w_R`, cast to field bits (`false ↦ 0`, `true ↦ 1`). -/
theorem dyckBits_cell (l r : Noun) :
    dyckBits (K := K) (Noun.cell l r)
      = (0 : K) :: (dyckBits l ++ (1 : K) :: dyckBits r) := by
  simp only [dyckBits, Noun.dyckWord, Noun.shape, Nock.BTree.encode, List.map_cons,
    List.map_append]
  norm_num

/-- **`Lem:NPR_decomp`, Φ₁:** `Φ(cons(l,r))₁ = Φ(l)₁ · Φ(r)₁`,
    i.e. `X^{|dt|} = X^{λL}·X^{λR}`. -/
theorem Phi1_cons (l r : Noun) :
    (Φ (K := K) (Noun.cell l r)).1 = (Φ l).1 * (Φ r).1 := by
  simp only [Φ_fst, Noun.leaves, pow_add]

/-- **`Lem:NPR_decomp`, Φ₂:** `Φ(cons(l,r))₂ = Φ(l)₂ + X^{λL}·Φ(r)₂`. -/
theorem Phi2_cons (l r : Noun) :
    (Φ (K := K) (Noun.cell l r)).2.1 = (Φ l).2.1 + X ^ l.leaves * (Φ r).2.1 := by
  simp only [Φ_snd_fst, leafF_cell, listPoly_append, leafF_length]

/-- **`Lem:NPR_decomp`, Φ₃, CORRECTED exponents (see the section header):**
    `Φ(cons(l,r))₃ = X·Φ(l)₃ + X^{2λL−1} + X^{2λL}·Φ(r)₃`. -/
theorem Phi3_cons (l r : Noun) :
    (Φ (K := K) (Noun.cell l r)).2.2
      = X * (Φ l).2.2 + X ^ (2 * l.leaves - 1) + X ^ (2 * l.leaves) * (Φ r).2.2 := by
  have hd : (dyckBits (K := K) l).length + 2 = 2 * l.leaves := dyckBits_length l
  have h1 : (dyckBits (K := K) l).length + 1 = 2 * l.leaves - 1 := by omega
  simp only [Φ_snd_snd, dyckBits_cell, listPoly_cons, listPoly_append, C_0, C_1]
  rw [← h1, ← hd]
  ring

/-- **`Lem:NPR_decomp`.**  The three algebraic identities characterizing
    `cons`.  We state the paper's `⟺ n = cons(nL,nR)` as `Φ n = Φ (cons nL nR)` — the
    *field-noun* equality (`Φ` is injective on field-nouns), which is exactly the
    paper's notion of noun equality over `𝔽`.  (Structural `n = cell nL nR` implies it via
    `congrArg`, `NPR_decomp_of_cons`; the converse to structural equality would additionally
    need injectivity of the leaf-atom cast `Nat → K`, which fails in small characteristic —
    the "same field-noun" phenomenon already documented for `collision_card_le`.) -/
theorem NPR_decomp (n nL nR : Noun) :
    Φ (K := K) n = Φ (K := K) (Noun.cell nL nR)
      ↔ ( (Φ (K := K) n).1 = (Φ (K := K) nL).1 * (Φ (K := K) nR).1
        ∧ (Φ (K := K) n).2.1 = (Φ (K := K) nL).2.1 + X ^ nL.leaves * (Φ (K := K) nR).2.1
        ∧ (Φ (K := K) n).2.2 = X * (Φ (K := K) nL).2.2 + X ^ (2 * nL.leaves - 1)
            + X ^ (2 * nL.leaves) * (Φ (K := K) nR).2.2 ) := by
  constructor
  · intro h
    rw [h]
    exact ⟨Phi1_cons nL nR, Phi2_cons nL nR, Phi3_cons nL nR⟩
  · rintro ⟨h1, h2, h3⟩
    have e1 : (Φ (K := K) n).1 = (Φ (K := K) (Noun.cell nL nR)).1 := by
      rw [h1, Phi1_cons]
    have e2 : (Φ (K := K) n).2.1 = (Φ (K := K) (Noun.cell nL nR)).2.1 := by
      rw [h2, Phi2_cons]
    have e3 : (Φ (K := K) n).2.2 = (Φ (K := K) (Noun.cell nL nR)).2.2 := by
      rw [h3, Phi3_cons]
    exact Prod.ext_iff.mpr ⟨e1, Prod.ext_iff.mpr ⟨e2, e3⟩⟩

/-- Structural `⟸` direction of `Lem:NPR_decomp`: if `n` is literally `cons(nL,nR)` then its
    NPR satisfies the three identities. -/
theorem NPR_decomp_of_cons {n nL nR : Noun} (h : n = Noun.cell nL nR) :
    (Φ (K := K) n).1 = (Φ (K := K) nL).1 * (Φ (K := K) nR).1
    ∧ (Φ (K := K) n).2.1 = (Φ (K := K) nL).2.1 + X ^ nL.leaves * (Φ (K := K) nR).2.1
    ∧ (Φ (K := K) n).2.2 = X * (Φ (K := K) nL).2.2 + X ^ (2 * nL.leaves - 1)
        + X ^ (2 * nL.leaves) * (Φ (K := K) nR).2.2 :=
  (NPR_decomp n nL nR).mp (by rw [h])

end Decomp

/-! ### Schwartz–Zippel / root counting -/

section SchwartzZippel
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- A nonzero polynomial of natDegree `d` vanishes at at most `d` points of `K`. -/
theorem card_eval_zero_le (q : K[X]) (hq : q ≠ 0) :
    (Finset.univ.filter (fun r : K => q.eval r = 0)).card ≤ q.natDegree := by
  have hset : (Finset.univ.filter (fun r : K => q.eval r = 0)) = q.roots.toFinset := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_toFinset,
      mem_roots hq, IsRoot.def]
  rw [hset]
  calc q.roots.toFinset.card ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := card_roots' q

end SchwartzZippel

/-! ### The collision-soundness bound -/

section Collision
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **`ε_col^{Λ,𝔽}` — the single-instance collision-soundness error.**
    The paper names the collision error `ε^{Λ,𝔽}_col := ε(Λ,K)` where
    `ε(Λ,K) = 2·(2Λ−1)/|K|` is the bound of `Lem:ion_univariate_sec`.
    We name it here as a standalone constant.  (`2·Λ−1` uses `ℕ` truncated subtraction; over
    the operative range `Λ ≥ 1` — always forced by `Noun.one_le_leaves` in every use below —
    it agrees with the paper's `2(2Λ−1)`; see `epsCol_eq` for the real-arithmetic form.) -/
def epsCol (Λ : ℕ) : ℚ := ((2 * (2 * Λ - 1) : ℕ) : ℚ) / (Fintype.card K)

omit [Field K] [DecidableEq K] in
/-- `ε_col` in the paper's real (non-truncated) arithmetic form `2(2Λ−1)/|K|`, valid for
    `Λ ≥ 1`. -/
theorem epsCol_eq {Λ : ℕ} (hΛ : 1 ≤ Λ) :
    epsCol (K := K) Λ = 2 * (2 * (Λ : ℚ) - 1) / (Fintype.card K) := by
  unfold epsCol
  have h1 : (1 : ℕ) ≤ 2 * Λ := by omega
  rw [Nat.cast_mul]
  congr 1
  push_cast [Nat.cast_sub h1]
  ring

/-- **lem:ion_univariate_sec, cardinality form — tight bound.**
    For distinct field-nouns of length `≤ Λ`, the fingerprint `fn` collides for at most
    `2Λ − 1` values of `r ∈ K`.

    "distinct field-nouns" (the paper's `n₁ ≠ n₂` in `𝒩^{λ≤Λ}(𝔽)`) is the
    hypothesis `hne`: the NPR data `(dt, w) = (leafF, dyckBits)` differ.  (Operationally
    distinct `Noun`s that agree after casting leaves into `K` are the *same* field-noun and
    genuinely have equal fingerprints, so this is exactly the right premise.)

    Proof = univariate Schwartz–Zippel: at least one of the three difference polynomials
    `X^{λ₁}−X^{λ₂}`, `F_{d₁}−F_{d₂}`, `F_{w₁}−F_{w₂}` is nonzero of natDegree `≤ 2Λ−1`, and a
    collision forces `r` to be its root. -/
theorem collision_card_le_tight (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
         ≠ (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    (Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card ≤ 2 * Λ - 1 := by
  have hΛ : 1 ≤ Λ := le_trans n₁.one_le_leaves h₁
  -- reduce to: some difference polynomial `P` is nonzero, deg ≤ 2Λ−1, and collision ⟹ root
  suffices h : ∃ P : K[X], P ≠ 0 ∧ P.natDegree ≤ 2 * Λ - 1 ∧
      (Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)) ⊆
      (Finset.univ.filter (fun r : K => P.eval r = 0)) by
    obtain ⟨P, hPne, hPdeg, hPsub⟩ := h
    calc (Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card
        ≤ (Finset.univ.filter (fun r : K => P.eval r = 0)).card := Finset.card_le_card hPsub
      _ ≤ P.natDegree := card_eval_zero_le P hPne
      _ ≤ 2 * Λ - 1 := hPdeg
  by_cases hlam : n₁.leaves = n₂.leaves
  · -- equal length λ: distinguished by the leaf poly or the dyck poly
    simp only [ne_eq, Prod.mk.injEq, not_and_or] at hne
    rcases hne with hd | hd
    · -- leaf arrays differ (equal length λ)
      refine ⟨listPoly (NPR.leafF n₁) - listPoly (NPR.leafF n₂), ?_, ?_, ?_⟩
      · exact NPR.listPoly_sub_ne_zero (by simp [hlam]) hd
      · refine le_trans (NPR.listPoly_sub_natDegree_le (by simp [hlam])) ?_
        rw [NPR.leafF_length]; omega
      · intro r hr
        rw [Finset.mem_filter] at hr ⊢
        refine ⟨hr.1, ?_⟩
        have := congrArg (fun x => x.2.1) hr.2
        simp only [NPR.fn] at this
        rw [eval_sub, sub_eq_zero]; exact this
    · -- dyck words differ (equal length 2(λ−1))
      refine ⟨listPoly (NPR.dyckBits n₁) - listPoly (NPR.dyckBits n₂), ?_, ?_, ?_⟩
      · refine NPR.listPoly_sub_ne_zero ?_ hd
        have e1 := NPR.dyckBits_length (K := K) n₁
        have e2 := NPR.dyckBits_length (K := K) n₂
        omega
      · refine le_trans (NPR.listPoly_sub_natDegree_le ?_) ?_
        · have e1 := NPR.dyckBits_length (K := K) n₁
          have e2 := NPR.dyckBits_length (K := K) n₂
          omega
        · have e1 := NPR.dyckBits_length (K := K) n₁
          omega
      · intro r hr
        rw [Finset.mem_filter] at hr ⊢
        refine ⟨hr.1, ?_⟩
        have := congrArg (fun x => x.2.2) hr.2
        simp only [NPR.fn] at this
        rw [eval_sub, sub_eq_zero]; exact this
  · -- lengths differ: distinguished by the first component X^{λ}
    refine ⟨X ^ n₁.leaves - X ^ n₂.leaves, ?_, ?_, ?_⟩
    · intro h
      have hcoeff := congrArg (fun q => Polynomial.coeff q n₁.leaves) h
      simp only [coeff_sub, coeff_X_pow, coeff_zero, if_neg hlam, sub_zero] at hcoeff
      exact one_ne_zero hcoeff
    · refine le_trans (natDegree_sub_le _ _) ?_
      rw [natDegree_X_pow, natDegree_X_pow, max_le_iff]; omega
    · intro r hr
      rw [Finset.mem_filter] at hr ⊢
      refine ⟨hr.1, ?_⟩
      have := congrArg (fun x => x.1) hr.2
      simp only [NPR.fn] at this
      rw [eval_sub, eval_X_pow, eval_X_pow, sub_eq_zero]; exact this

/-- **lem:ion_univariate_sec, cardinality form — paper's stated bound.**
    The collision set has size `≤ 2(2Λ−1)` (the constant printed in the paper; the tight
    bound `collision_card_le_tight` gives `2Λ−1`). -/
theorem collision_card_le (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
         ≠ (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    (Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card ≤ 2 * (2 * Λ - 1) :=
  le_trans (collision_card_le_tight Λ n₁ n₂ h₁ h₂ hne) (by omega)

/-- **lem:ion_univariate_sec, probability form.**  With the counting-measure
    convention, `Pr_{r∈K}[fn n₁ = fn n₂] ≤ 2(2Λ−1)/|K| = ε(Λ,K)`. -/
theorem collision_prob_le (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
         ≠ (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    ((Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card : ℚ)
        / (Fintype.card K)
      ≤ ((2 * (2 * Λ - 1) : ℕ) : ℚ) / (Fintype.card K) := by
  have hpos : (0 : ℚ) < Fintype.card K := by
    haveI : Nonempty K := ⟨0⟩
    exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff_of_pos_right hpos]
  exact_mod_cast collision_card_le Λ n₁ n₂ h₁ h₂ hne

/-- **lem:ion_univariate_sec, probability form in terms of `ε_col`.**
    Restatement of `collision_prob_le` against the named constant `epsCol`:
    `Pr_{r∈K}[fn n₁ = fn n₂; n₁ ≠ n₂] ≤ ε_col^{Λ,𝔽}`. -/
theorem collision_prob_le_epsCol (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
         ≠ (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    ((Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card : ℚ)
        / (Fintype.card K)
      ≤ epsCol (K := K) Λ :=
  collision_prob_le Λ n₁ n₂ h₁ h₂ hne

end Collision

/-! ### Union bound over a table of nouns -/

section Table
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- `k² − k = k(k−1)` (Nat, robust to truncated subtraction). -/
private theorem sq_sub_self (k : ℕ) : k * k - k = k * (k - 1) := by
  cases k with
  | zero => rfl
  | succ n => rw [Nat.succ_sub_one, Nat.mul_succ]; omega

/-- **corr:ion_single_security, cardinality form.**  For a table of `k = |s|`
    nouns of length `≤ Λ`, the number of `r ∈ K` for which *some* pair of distinct nouns
    collides is `≤ k(k−1)·(2Λ−1)`.  (Union bound over ordered distinct index pairs, each
    contributing `≤ 2Λ−1` by `collision_card_le_tight`.) -/
theorem collision_table_card_le {ι : Type*} [DecidableEq ι] (Λ : ℕ)
    (s : Finset ι) (f : ι → Noun) (hf : ∀ i ∈ s, (f i).leaves ≤ Λ) :
    (Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
        NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
        (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
          ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2)))).card
      ≤ s.card * (s.card - 1) * (2 * Λ - 1) := by
  classical
  set g : ι × ι → Finset K := fun ij =>
    Finset.univ.filter (fun r : K => NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
      (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
        ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2))) with hg
  have hsub : (Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
      NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
      (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
        ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2))))
      ⊆ s.offDiag.biUnion g := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨ij, hij, hcol, hdi⟩ := hr.2
    refine Finset.mem_biUnion.mpr ⟨ij, hij, ?_⟩
    simp only [hg, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hcol, hdi⟩
  have hcard : ∀ ij ∈ s.offDiag, (g ij).card ≤ 2 * Λ - 1 := by
    intro ij hij
    obtain ⟨hi, hj, _⟩ := Finset.mem_offDiag.mp hij
    by_cases hd : (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
        ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2))
    · -- distinct: bound by the single-pair collision count
      refine le_trans (Finset.card_le_card ?_)
        (collision_card_le_tight Λ (f ij.1) (f ij.2) (hf _ hi) (hf _ hj) hd)
      intro r hr
      simp only [hg, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact hr.1
    · -- equal field-nouns: the filtered set is empty
      have hempty : g ij = ∅ := by
        simp only [hg, Finset.filter_eq_empty_iff]
        intro r _
        rintro ⟨_, hdiff⟩
        exact hd hdiff
      rw [hempty]; simp
  calc (Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
          NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
          (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
            ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2)))).card
      ≤ (s.offDiag.biUnion g).card := Finset.card_le_card hsub
    _ ≤ ∑ _ij ∈ s.offDiag, (2 * Λ - 1) :=
        le_trans Finset.card_biUnion_le (Finset.sum_le_sum hcard)
    _ = s.offDiag.card * (2 * Λ - 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ = s.card * (s.card - 1) * (2 * Λ - 1) := by
        rw [Finset.offDiag_card, sq_sub_self]

/-- Casting helper: `↑(k(k−1)) = k(k−1)` bridging `ℕ` truncated subtraction into `ℚ`. -/
private theorem natCast_mul_pred (k : ℕ) : ((k * (k - 1) : ℕ) : ℚ) = (k : ℚ) * ((k : ℚ) - 1) := by
  rcases k with _ | k
  · simp
  · push_cast; ring

/-- **corr:ion_single_security, probability form — union bound.**  With
    `ε := ε_col = 2(2Λ−1)/|K|`, the probability that some pair among `k = |s|` nouns collides
    is `≤ ε · k(k−1)/2`.  This is the paper's second (union-bound) inequality.

    ⚠ **The paper's FIRST (tight) inequality `Pr ≤ 1 − (1−ε)^{k(k−1)/2}` is NOT proven here,
    and is not soundly provable in this model.**  The paper's proof obtains it
    by asserting "the probability of no table collisions is `(1−p)^{k(k−1)/2}`", i.e. by
    treating the `k(k−1)/2` pairwise collision events as *independent*.  In our (and the
    paper's real) probability model those events all share the SAME random `r ∈ K`, so they
    are NOT independent, and a product/independence bound is unavailable: the only estimate the
    root-counting machinery yields is the ADDITIVE union bound (`card_biUnion_le`), giving the
    `≤ ε·k(k−1)/2` below.  The product form is moreover genuinely FALSE in the worst case
    admitted by our per-pair root-count bounds: for `m := k(k−1)/2` pairwise collision sets
    that are pairwise disjoint (each of the maximal `2Λ−1` roots) and together partition `K`,
    the collision probability is `1`, which exceeds `1−(1−ε)^m < 1`.  Consistently, our proven
    union bound `ε·m` STRICTLY EXCEEDS the tight `1−(1−ε)^m` for `m ≥ 2` (Bernoulli,
    `one_sub_one_sub_pow_le`), so the tight expression is a strictly stronger claim that this
    model cannot license.  The union bound below is the rigorous, model-faithful claim; the
    paper itself calls the tight bound "optimal but [harder to show]" and the union bound the
    "non-optimal but easier to show" one it actually establishes. -/
theorem collision_table_prob_le {ι : Type*} [DecidableEq ι] (Λ : ℕ)
    (s : Finset ι) (f : ι → Noun) (hf : ∀ i ∈ s, (f i).leaves ≤ Λ) :
    ((Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
        NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
        (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
          ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2)))).card : ℚ)
        / (Fintype.card K)
      ≤ (((2 * (2 * Λ - 1) : ℕ) : ℚ) / (Fintype.card K))
          * ((s.card : ℚ) * ((s.card : ℚ) - 1) / 2) := by
  have hpos : (0 : ℚ) < Fintype.card K := by
    haveI : Nonempty K := ⟨0⟩
    exact_mod_cast Fintype.card_pos
  have hcard := collision_table_card_le (K := K) Λ s f hf
  have hne0 : (Fintype.card K : ℚ) ≠ 0 := ne_of_gt hpos
  rw [div_le_iff₀ hpos]
  -- the two `|K|`s cancel; both sides reduce to `k(k−1)·(2Λ−1)`
  have hrhs : (((2 * (2 * Λ - 1) : ℕ) : ℚ) / (Fintype.card K))
        * ((s.card : ℚ) * ((s.card : ℚ) - 1) / 2) * (Fintype.card K)
      = (s.card : ℚ) * ((s.card : ℚ) - 1) * ((2 * Λ - 1 : ℕ) : ℚ) := by
    field_simp
    push_cast
    ring
  rw [hrhs]
  calc ((_ : ℕ) : ℚ) ≤ ((s.card * (s.card - 1) * (2 * Λ - 1) : ℕ) : ℚ) := by exact_mod_cast hcard
    _ = (s.card : ℚ) * ((s.card : ℚ) - 1) * ((2 * Λ - 1 : ℕ) : ℚ) := by
        rw [Nat.cast_mul, natCast_mul_pred]

/-- **corr:ion_single_security, union bound in terms of `ε_col`.**
    Restatement of `collision_table_prob_le` against the named constant `epsCol`: `Pr[∃ colliding pair] ≤ ε_col^{Λ,𝔽} · k(k−1)/2`. -/
theorem collision_table_prob_le_epsCol {ι : Type*} [DecidableEq ι] (Λ : ℕ)
    (s : Finset ι) (f : ι → Noun) (hf : ∀ i ∈ s, (f i).leaves ≤ Λ) :
    ((Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
        NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
        (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
          ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2)))).card : ℚ)
        / (Fintype.card K)
      ≤ epsCol (K := K) Λ * ((s.card : ℚ) * ((s.card : ℚ) - 1) / 2) :=
  collision_table_prob_le Λ s f hf

/-- **Bernoulli's inequality (the paper's `1 − (1−ε)^m < ε·m` step).**
    For any `ε ≤ 2` and `m : ℕ`, `1 − (1−ε)^m ≤ m·ε`.  This is the pure real inequality
    relating the paper's two collision-error expressions: the tight
    `1 − (1−ε)^{k(k−1)/2}` and the union bound `ε·k(k−1)/2` (`m = k(k−1)/2`).

    NOTE: this lemma establishes only the *arithmetic* relation `tight ≤ union`.  It does
    NOT (and cannot, in this shared-randomness model) establish that the collision
    probability is bounded by the tight expression — see the ⚠ note on
    `collision_table_prob_le`.  It is exactly what shows the union bound we DO prove is the
    weaker (larger) of the paper's two stated bounds, faithfully reproducing the paper's
    `<` chain. -/
theorem one_sub_one_sub_pow_le (ε : ℚ) (hε : ε ≤ 2) (m : ℕ) :
    1 - (1 - ε) ^ m ≤ (m : ℚ) * ε := by
  have hb := one_add_mul_le_pow (a := -ε) (by linarith) m
  have hmul : (m : ℚ) * (-ε) = -((m : ℚ) * ε) := by ring
  have h1 : (1 : ℚ) + -ε = 1 - ε := by ring
  rw [hmul, h1] at hb
  linarith

end Table

/-! ### Concrete Goldilocks instantiation

    The collision bounds specialized to the paper's field `K = 𝔽_p^3`, `|K| = p^3 ≈ 2^192`.
    ⚠ These specializations depend on `Nock.Field.goldilocks_prime` (the flagged primality
    axiom); the generic theorems above do not. -/
section Concrete
open Nock.Field

/-- lem:ion_univariate_sec over the concrete Goldilocks field `K = 𝔽_p^3`: the collision
    probability is `≤ 2(2Λ−1)/p^3`. -/
theorem collision_prob_le_goldilocks (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
         ≠ (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    ((Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card : ℚ)
        / (p ^ 3)
      ≤ ((2 * (2 * Λ - 1) : ℕ) : ℚ) / (p ^ 3) := by
  have := collision_prob_le (K := K) Λ n₁ n₂ h₁ h₂ hne
  rwa [card_K] at this

end Concrete

end NPR
end Nock
