/-
  Nock/NockVMROM/Thm54/TraceGen/GenDyckBadSeed.lean

  **The `cons`-head condition is a bad-seed event, bounded by the paper's own fingerprint
  machinery.**

  `genComputeSkeleton_inTree_Vcomp` (`GenSkeletonVcomp.lean:521`) takes

      hdyck : ∀ v, InTree t v → v.label.skel.state = State.cons →
                (encC z (formulaHead v.label.skel.formula)).dyck ≠ 0

  and the AIR enforces exactly this with the `cons_inv` inverse-witness column
; the paper states the intended reading, that `f_h.dyck ≠ 0` holds
  precisely when `f_h` is a cell.

  That reading is **not** unconditional: `dyck` is the evaluation at the seed of a `{0,1}`-coefficient
  polynomial, which is nonzero *as a polynomial* for a cell but can vanish at a badly chosen seed.
  So `hdyck` cannot be discharged for all seeds, and the honest generic statement is a bound on how
  many seeds are bad.

  This module proves that bound **as a corollary of the machinery the paper's own collision lemma
  uses**, rather than by a parallel argument:

  * `NPR.card_eval_zero_le` (`NPR.lean:393`) -- roots of a nonzero polynomial are at most its degree.
    This is the primitive `collision_card_le_tight` (`NPR.lean:442`, pinned 1-1 to
    `lem:ion_univariate_sec`) reduces to.
  * `hornerLE_eq_eval` (`Encode.lean:38`) -- the computable Horner fold in `encC` agrees with
    evaluating `NPR.listPoly`.
  * `NPR.dyckBits_cell` (`NPR.lean:321`) -- a cell's dyck vector is `0 :: (dyck l ++ 1 :: dyck r)`,
    so it carries a literal `1` and its polynomial is nonzero.
  * `NPR.dyckBits_length` (`NPR.lean:267`) -- `length + 2 = 2 * leaves`, giving the degree bound.

  The resulting count, `2 * Λ - 3` at leaf-window `Λ`, sits inside the paper's
  `ε(Λ, K) = 2(2Λ - 1)/|K|` (`lem:ion_univariate_sec`) -- as it must, since a cell whose dyck
  fingerprint vanishes agrees with an atom in that coordinate.

  What this does **not** do: it does not discharge `hdyck`, because `hdyck` is false at a bad seed.

  -- the paper
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonVcomp
import Nock.NPR

-- A missing import otherwise becomes a silent type variable rather than an error;
-- that cost real debugging time on this module family.
set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open scoped Classical
open Nock Nock.Walk Polynomial
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-! ## A cell's dyck polynomial is nonzero -/

/-- The coefficient of a cell's dyck vector at the position of its separating `1` is `1`.

`NPR.dyckBits_cell` gives `dyckBits (cell l r) = 0 :: (dyckBits l ++ 1 :: dyckBits r)`, so index
`(dyckBits l).length + 1` holds the literal `1`. -/
theorem listPoly_dyckBits_cell_coeff (l r : Noun) :
    (NPR.listPoly (NPR.dyckBits (K := K) (Noun.cell l r))).coeff
        ((NPR.dyckBits (K := K) l).length + 1) = 1 := by
  rw [NPR.listPoly_coeff, NPR.dyckBits_cell]
  have hlt : (NPR.dyckBits (K := K) l).length + 1 <
      ((0 : K) :: (NPR.dyckBits (K := K) l ++ (1 : K) :: NPR.dyckBits (K := K) r)).length := by
    simp [List.length_append]
  rw [if_pos hlt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- **A cell's dyck polynomial is nonzero as a polynomial** -- the fact that makes
the paper's reading correct generically, and the fact a bad seed defeats pointwise. -/
theorem listPoly_dyckBits_cell_ne_zero (l r : Noun) :
    NPR.listPoly (NPR.dyckBits (K := K) (Noun.cell l r)) ≠ 0 := by
  intro hzero
  have h := listPoly_dyckBits_cell_coeff (K := K) l r
  rw [hzero, Polynomial.coeff_zero] at h
  exact zero_ne_one h

/-! ## The bad-seed count -/

/-- **Bad-seed bound for the `cons` head condition.**

The seeds at which a cell's dyck fingerprint vanishes -- i.e. at which `hdyck` fails for that cell --
number at most `2 * leaves - 3`.

Proved by the same route as `lem:ion_univariate_sec`: exhibit the nonzero polynomial, bound its
degree, and apply `NPR.card_eval_zero_le`.
-- -/
theorem consHead_dyck_zero_card_le (l r : Noun) :
    (Finset.univ.filter
        (fun z : K => (encC z (Noun.cell l r)).dyck = 0)).card
      ≤ 2 * (Noun.cell l r).leaves - 3 := by
  have hpoly := listPoly_dyckBits_cell_ne_zero (K := K) l r
  have hsub : (Finset.univ.filter (fun z : K => (encC z (Noun.cell l r)).dyck = 0)) ⊆
      (Finset.univ.filter
        (fun z : K =>
          (NPR.listPoly (NPR.dyckBits (K := K) (Noun.cell l r))).eval z = 0)) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    rw [← hornerLE_eq_eval]
    exact hz
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (NPR.card_eval_zero_le _ hpoly) ?_
  refine le_trans (NPR.listPoly_natDegree_le _) ?_
  have hlen := NPR.dyckBits_length (K := K) (Noun.cell l r)
  omega

/--

`2 * Λ - 3 ≤ 2 * Λ - 1` is the paper's `ε(Λ, K)` numerator (`lem:ion_univariate_sec`), so the `cons` bad-seed set is inside the collision bound already pinned.
-- -/
theorem consHead_dyck_zero_card_le_window (Λ : ℕ) (l r : Noun)
    (hlen : (Noun.cell l r).leaves ≤ Λ) :
    (Finset.univ.filter
        (fun z : K => (encC z (Noun.cell l r)).dyck = 0)).card ≤ 2 * Λ - 1 := by
  refine le_trans (consHead_dyck_zero_card_le (K := K) l r) ?_
  omega

/-! ## The list version, mirroring `Corr:ion_single_security` -/

/-- **Union bound over all `cons` heads of a trace.**

`consHead_dyck_zero_card_le_window` bounds the bad seeds for one cell; a trace has many `cons`
rows, so the object a consumer of `genComputeSkeleton_inTree_Vcomp` needs is the union.  This
mirrors the paper's own single-to-list step, `Corr:ion_single_security` over
`Lem:ion_univariate_sec` (`:1188`), and is proved the same way -- a union bound, here without the
Bernoulli intermediate.
-- -/
theorem consHeads_dyck_zero_card_le (Λ : ℕ) :
    ∀ ps : List (Noun × Noun),
      (∀ p ∈ ps, (Noun.cell p.1 p.2).leaves ≤ Λ) →
      (Finset.univ.filter
          (fun z : K => ∃ p ∈ ps, (encC z (Noun.cell p.1 p.2)).dyck = 0)).card
        ≤ ps.length * (2 * Λ - 1)
  | [], _ => by
      simp only [List.not_mem_nil, false_and, exists_false, List.length_nil, Nat.zero_mul]
      simp
  | p :: ps, h => by
      have hsub : (Finset.univ.filter
            (fun z : K => ∃ q ∈ p :: ps, (encC z (Noun.cell q.1 q.2)).dyck = 0)) ⊆
          (Finset.univ.filter (fun z : K => (encC z (Noun.cell p.1 p.2)).dyck = 0)) ∪
          (Finset.univ.filter
            (fun z : K => ∃ q ∈ ps, (encC z (Noun.cell q.1 q.2)).dyck = 0)) := by
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons] at hz
        obtain ⟨q, hq, hqz⟩ := hz
        rcases hq with rfl | hq
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqz⟩)
        · exact Finset.mem_union_right _ (by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨q, hq, hqz⟩)
      refine le_trans (Finset.card_le_card hsub) ?_
      refine le_trans (Finset.card_union_le _ _) ?_
      have hhead := consHead_dyck_zero_card_le_window (K := K) Λ p.1 p.2 (h p (by simp))
      have htail := consHeads_dyck_zero_card_le Λ ps
        (fun q hq => h q (by simp [hq]))
      have hcomm : (ps.length + 1) * (2 * Λ - 1)
          = (2 * Λ - 1) + ps.length * (2 * Λ - 1) := by
        rw [Nat.succ_mul, Nat.add_comm]
      simp only [List.length_cons]
      rw [hcomm]
      exact Nat.add_le_add hhead htail

/-! ## `hncol`: the OP5 condition is a fingerprint collision

`op5ResultsAgree z s` (`GenSkeletonVcomp.lean:453`) says the two OP5 operand results are equal
*or* their `encC` fingerprints differ.  Its negation is therefore exactly a fingerprint collision,
so `NPR.collision_card_le_tight` -- the declaration pinned 1-1 to `lem:ion_univariate_sec`
 -- bounds the bad seeds directly, with no new polynomial argument.

Note the hypothesis shape.  `collision_card_le_tight` asks for distinct **fingerprint coefficient
vectors** `(leafF, dyckBits)`, not distinct nouns, and that is the honest requirement: `leafF` casts
Nat atoms into `K`, which is not injective at or above the characteristic, so two
distinct nouns can share a coefficient vector.  We keep the same hypothesis rather than deriving it
from `n₁ ≠ n₂`.
-- -/

/-- `encC` equality at a seed is `NPR.fn` equality at that seed. -/
theorem encC_eq_iff_fn_eq (z : K) (n₁ n₂ : Noun) (h : encC z n₁ = encC z n₂) :
    NPR.fn (K := K) n₁ z = NPR.fn (K := K) n₂ z := by
  have hs := congrArg ComputeTable.FP.size h
  have hd := congrArg ComputeTable.FP.dyck h
  have hl := congrArg ComputeTable.FP.leaf h
  simp only [encC_size, encC_dyck, encC_leaf, hornerLE_eq_eval] at hs hd hl
  simp only [NPR.fn]
  rw [hs, hl, hd]

/-- **Bad-seed bound for an `encC` collision between two nouns**, as a corollary of
`NPR.collision_card_le_tight`.
-- -/
theorem encC_collision_card_le (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
         ≠ (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    (Finset.univ.filter (fun z : K => encC z n₁ = encC z n₂)).card ≤ 2 * Λ - 1 := by
  have hsub : (Finset.univ.filter (fun z : K => encC z n₁ = encC z n₂)) ⊆
      (Finset.univ.filter (fun z : K => NPR.fn (K := K) n₁ z = NPR.fn (K := K) n₂ z)) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact encC_eq_iff_fn_eq z n₁ n₂ hz
  exact le_trans (Finset.card_le_card hsub) (NPR.collision_card_le_tight Λ n₁ n₂ h₁ h₂ hne)

/-- **Bad-seed bound for `hncol`.**  The seeds at which `op5ResultsAgree` fails for one row number
at most `2Λ - 1` -- the same count as the `cons` head condition, and the same `ε(Λ,K)` numerator.
-- -/
theorem op5ResultsAgree_bad_card_le (Λ : ℕ) (s : ComputeRowSkeleton)
    (h₁ : (P8Census.skeletonSubformula s 0 TripleSlot.result).leaves ≤ Λ)
    (h₂ : (P8Census.skeletonSubformula s 1 TripleSlot.result).leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) (P8Census.skeletonSubformula s 0 TripleSlot.result),
            NPR.dyckBits (K := K) (P8Census.skeletonSubformula s 0 TripleSlot.result))
         ≠ (NPR.leafF (K := K) (P8Census.skeletonSubformula s 1 TripleSlot.result),
            NPR.dyckBits (K := K) (P8Census.skeletonSubformula s 1 TripleSlot.result))) :
    (Finset.univ.filter (fun z : K => ¬ op5ResultsAgree z s)).card ≤ 2 * Λ - 1 := by
  have hsub : (Finset.univ.filter (fun z : K => ¬ op5ResultsAgree z s)) ⊆
      (Finset.univ.filter
        (fun z : K =>
          encC z (P8Census.skeletonSubformula s 0 TripleSlot.result) =
            encC z (P8Census.skeletonSubformula s 1 TripleSlot.result))) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, op5ResultsAgree,
      not_or, not_ne_iff] at hz ⊢
    exact hz.2
  exact le_trans (Finset.card_le_card hsub) (encC_collision_card_le Λ _ _ h₁ h₂ hne)

/-! ## Noun distinctness from bounded atoms

`encC_collision_card_le` inherits `collision_card_le_tight`'s hypothesis of distinct fingerprint
*coefficient vectors* `(leafF, dyckBits)` rather than distinct nouns, because `leafF` casts Nat atoms
into `K` and that cast is not injective at or above the characteristic.

The paper does not have this problem, because it types leaves in the field from the start
(`DT^λ(F)`).  The condition that makes the Nock-side cast agree with that
typing is exactly the atom bound the carrier already holds: `BuildableNockExecution` carries `q`
with `q_gt_one` and `q_le_ringChar`, and `FieldEmbedding.BoundedBy q` says every atom is `< q`.

Under that hypothesis the cast is injective on the atoms that occur, so noun distinctness *does*
give distinct coefficient vectors, and the collision bound can be stated the way one wants to state
it.  Nothing here weakens `collision_card_le_tight`; it supplies its hypothesis.
-- -/

/-- Every atom of a `BoundedBy q` noun is `< q`. -/
theorem leafList_lt_of_boundedBy {q : ℕ} :
    ∀ {n : Noun}, FieldEmbedding.BoundedBy q n → ∀ k ∈ n.leafList, k < q
  | .atom m, h, k, hk => by
      simp only [Noun.leafList, List.mem_singleton] at hk
      subst hk; exact h
  | .cell l r, h, k, hk => by
      simp only [Noun.leafList, List.mem_append] at hk
      rcases hk with hk | hk
      · exact leafList_lt_of_boundedBy h.1 k hk
      · exact leafList_lt_of_boundedBy h.2 k hk

/-- `Nat.cast` is injective on lists of naturals below the characteristic. -/
theorem map_natCast_inj {q : ℕ} (hq : q ≤ ringChar K) :
    ∀ (l₁ l₂ : List ℕ), (∀ k ∈ l₁, k < q) → (∀ k ∈ l₂, k < q) →
      l₁.map (fun k : ℕ => (k : K)) = l₂.map (fun k : ℕ => (k : K)) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l₁, b :: l₂, h₁, h₂, h => by
      haveI : CharP K (ringChar K) := ringChar.charP K
      simp only [List.map_cons, List.cons.injEq] at h
      have hab : a = b :=
        CharP.natCast_injOn_Iio K (ringChar K)
          (Set.mem_Iio.mpr (lt_of_lt_of_le (h₁ a (by simp)) hq))
          (Set.mem_Iio.mpr (lt_of_lt_of_le (h₂ b (by simp)) hq)) h.1
      have htl := map_natCast_inj hq l₁ l₂
        (fun k hk => h₁ k (by simp [hk])) (fun k hk => h₂ k (by simp [hk])) h.2
      rw [hab, htl]

/-- The dyck bit-cast is injective: `0` and `1` stay distinct in a field. -/
theorem dyckWord_eq_of_dyckBits_eq {n₁ n₂ : Noun}
    (h : NPR.dyckBits (K := K) n₁ = NPR.dyckBits (K := K) n₂) :
    n₁.dyckWord = n₂.dyckWord := by
  have hinj : Function.Injective (fun b : Bool => if b then (1 : K) else 0) := by
    intro b c hbc
    cases b <;> cases c <;> simp_all
  exact List.map_injective_iff.mpr hinj h

/-- **Noun distinctness gives distinct fingerprint coefficient vectors, under the atom bound.**

This is the hypothesis `NPR.collision_card_le_tight` (and hence `lem:ion_univariate_sec`) asks for,
supplied from `n₁ ≠ n₂` plus the carrier's own `BoundedBy q` / `q ≤ ringChar K`.
-- -/
theorem fingerprint_vectors_ne_of_ne {q : ℕ} (hq : q ≤ ringChar K)
    {n₁ n₂ : Noun}
    (hb₁ : FieldEmbedding.BoundedBy q n₁) (hb₂ : FieldEmbedding.BoundedBy q n₂)
    (hne : n₁ ≠ n₂) :
    (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
      ≠ (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂) := by
  intro heq
  obtain ⟨hl, hd⟩ := Prod.mk.injEq .. ▸ heq
  refine hne (Noun.noun_dyck_leaf_injective ?_)
  refine Prod.ext (dyckWord_eq_of_dyckBits_eq (K := K) hd) ?_
  exact map_natCast_inj (K := K) hq _ _
    (leafList_lt_of_boundedBy hb₁) (leafList_lt_of_boundedBy hb₂) hl

/-- **The collision bound stated with noun distinctness**, the form the paper's typing implies.
-- -/
theorem encC_collision_card_le_of_ne {q : ℕ} (hq : q ≤ ringChar K) (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hb₁ : FieldEmbedding.BoundedBy q n₁) (hb₂ : FieldEmbedding.BoundedBy q n₂)
    (hne : n₁ ≠ n₂) :
    (Finset.univ.filter (fun z : K => encC z n₁ = encC z n₂)).card ≤ 2 * Λ - 1 :=
  encC_collision_card_le Λ n₁ n₂ h₁ h₂
    (fingerprint_vectors_ne_of_ne (K := K) hq hb₁ hb₂ hne)

/-- **`hncol`'s bad-seed bound, stated with noun distinctness.**

The usable form: if the two OP5 operand results are genuinely different nouns whose atoms are
bounded by `q ≤ ringChar K`, then `op5ResultsAgree` fails at at most `2Λ - 1` seeds.  A caller has
noun distinctness and the carrier's `q` bound; it does not naturally have distinctness of the cast
coefficient vectors, which is why this form exists.
-- -/
theorem op5ResultsAgree_bad_card_le_of_ne {q : ℕ} (hq : q ≤ ringChar K)
    (Λ : ℕ) (s : ComputeRowSkeleton)
    (h₁ : (P8Census.skeletonSubformula s 0 TripleSlot.result).leaves ≤ Λ)
    (h₂ : (P8Census.skeletonSubformula s 1 TripleSlot.result).leaves ≤ Λ)
    (hb₁ : FieldEmbedding.BoundedBy q (P8Census.skeletonSubformula s 0 TripleSlot.result))
    (hb₂ : FieldEmbedding.BoundedBy q (P8Census.skeletonSubformula s 1 TripleSlot.result))
    (hne : P8Census.skeletonSubformula s 0 TripleSlot.result
         ≠ P8Census.skeletonSubformula s 1 TripleSlot.result) :
    (Finset.univ.filter (fun z : K => ¬ op5ResultsAgree z s)).card ≤ 2 * Λ - 1 :=
  op5ResultsAgree_bad_card_le Λ s h₁ h₂
    (fingerprint_vectors_ne_of_ne (K := K) hq hb₁ hb₂ hne)

/-! ## `hsz`: the OP3 condition is an orbit condition, not a collision

`op3CallSizeOk z s` (`GenSkeletonVcomp.lean:460`) is `True` when the OP3 call result is an atom, and
otherwise `(encC z (cell x y)).size ≠ z`.  Since `size = z ^ leaves` (`encC_size`), for a cell that
reads `z ^ leaves ≠ z` -- so the bad seeds are the roots of `X ^ leaves - X`, i.e. `0` together with
the `(leaves - 1)`-th roots of unity.

The count still comes from the same root-counting primitive.
-- -/

/-- `X ^ n - X` is nonzero for `2 ≤ n`: its degree-`n` coefficient is `1`. -/
theorem X_pow_sub_X_ne_zero {n : ℕ} (hn : 2 ≤ n) :
    (X ^ n - X : K[X]) ≠ 0 := by
  intro hzero
  have h := congrArg (fun q : K[X] => q.coeff n) hzero
  simp only [coeff_sub, coeff_X_pow, if_pos rfl, coeff_X, Polynomial.coeff_zero] at h
  rw [if_neg (by omega : ¬ (1 = n))] at h
  simp at h

/-- `natDegree (X ^ n - X) = n` for `2 ≤ n`. -/
theorem natDegree_X_pow_sub_X {n : ℕ} (hn : 2 ≤ n) :
    (X ^ n - X : K[X]).natDegree = n := by
  have hlt : (X : K[X]).natDegree < (X ^ n : K[X]).natDegree := by
    rw [natDegree_X, natDegree_X_pow]; omega
  rw [natDegree_sub_eq_left_of_natDegree_lt hlt, natDegree_X_pow]

/-- **Bad-seed bound for `hsz`.**  The seeds at which an OP3 cell call result has
`size = z` -- i.e. at which `op3CallSizeOk` fails -- number at most `Λ`.

Unlike `hdyck` and `hncol` this is an orbit statement (`z ^ (leaves - 1) = 1`), but the count comes
from the same primitive `NPR.card_eval_zero_le`.
-- -/
theorem op3CallSize_bad_card_le (Λ : ℕ) (x y : Noun)
    (hlen : (Noun.cell x y).leaves ≤ Λ) :
    (Finset.univ.filter
        (fun z : K => (encC z (Noun.cell x y)).size = z)).card ≤ Λ := by
  have hn : 2 ≤ (Noun.cell x y).leaves := by
    have hx := x.one_le_leaves
    have hy := y.one_le_leaves
    have hcell : (Noun.cell x y).leaves = x.leaves + y.leaves := rfl
    omega
  have hsub : (Finset.univ.filter (fun z : K => (encC z (Noun.cell x y)).size = z)) ⊆
      (Finset.univ.filter
        (fun z : K => (X ^ (Noun.cell x y).leaves - X : K[X]).eval z = 0)) := by
    intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simp only [encC_size] at hz'
    rw [eval_sub, eval_pow, eval_X, sub_eq_zero]
    exact hz'
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (NPR.card_eval_zero_le _ (X_pow_sub_X_ne_zero (K := K) hn)) ?_
  rw [natDegree_X_pow_sub_X (K := K) hn]
  exact hlen

/-! ## Composition: a single good-seed predicate, threaded into `V_comp`

The three bounds above are per-object.  What a consumer of
`genComputeSkeleton_inTree_Vcomp` needs is one predicate on the seed, plus a count of the seeds
that fail it.  This section supplies both, and then discharges `V_comp`'s three hypotheses from the
single predicate.
-- -/

/-- **The three `V_comp` side conditions at one row, as a single predicate on the seed.** -/
def RowSeedGood (z : K) (g : GenComputeRow K) : Prop :=
  (g.skel.state = State.cons → (encC z (formulaHead g.skel.formula)).dyck ≠ 0) ∧
    (g.skel.state = State.s5 → op5ResultsAgree z g.skel) ∧
    (g.skel.state = State.s3 → op3CallSizeOk z g.skel)

/-- **The good-seed predicate for a whole generated tree.**

**Logically** equivalent to the conjunction of `genComputeSkeleton_inTree_Vcomp`'s three
hypotheses -- **not definitionally**: this is `∀ v, (A ∧ B ∧ C)` while the hypotheses are
`(∀ v, A) ∧ (∀ v, B) ∧ (∀ v, C)`, different head constructors, and the wrapper commutes them
explicitly.  Note also that `V_comp` needs `z ≠ 0`, which this predicate does not contain: the
seed-side requirement is `SeedGood z t ∧ z ≠ 0`. -/
def SeedGood (z : K) (t : NTree (GenComputeRow K)) : Prop :=
  ∀ v, InTree t v → RowSeedGood z v.label

/-- `SeedGood` follows from the row-wise condition along the BFS order, which is the form the
counting statement below uses. -/
theorem seedGood_of_bfsRows (z : K) (t : NTree (GenComputeRow K))
    (h : ∀ g ∈ bfsRows t, RowSeedGood z g) : SeedGood z t := by
  intro v hv
  have hmem : v ∈ bfsForest [t] := (mem_bfsForest [t] v).mpr ⟨t, by simp, hv⟩
  refine h v.label ?_
  unfold bfsRows
  exact List.mem_map.mpr ⟨v, hmem, rfl⟩

/-- **The bad-seed count over a list of rows**, by the union bound.

Stated over an arbitrary list so the hypothesis and conclusion are elaborated together -- composing
two separately-stated counting lemmas makes their `DecidablePred` choices disagree.

The per-row bound `B` is a hypothesis because discharging it needs the row's *shape*: that a `cons`
row's formula head is a cell, that an OP5 row's two operands are distinct nouns with bounded atoms,
that an OP3 row's call result is a cell.  Those are program-dependent; the composition is not.

Mirrors the paper's own single-to-list step, `Corr:ion_single_security` over
`Lem:ion_univariate_sec` (`:1188`).
-- -/
theorem rowsBad_card_le (B : ℕ) :
    ∀ gs : List (GenComputeRow K),
      (∀ g ∈ gs, (Finset.univ.filter (fun z : K => ¬ RowSeedGood z g)).card ≤ B) →
      (Finset.univ.filter
          (fun z : K => ∃ g ∈ gs, ¬ RowSeedGood z g)).card ≤ gs.length * B
  | [], _ => by
      simp only [List.not_mem_nil, false_and, exists_false, List.length_nil, Nat.zero_mul]
      simp
  | g :: gs, h => by
      have hsub : (Finset.univ.filter (fun z : K => ∃ q ∈ g :: gs, ¬ RowSeedGood z q)) ⊆
          (Finset.univ.filter (fun z : K => ¬ RowSeedGood z g)) ∪
          (Finset.univ.filter (fun z : K => ∃ q ∈ gs, ¬ RowSeedGood z q)) := by
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons] at hz
        obtain ⟨q, hq, hqz⟩ := hz
        rcases hq with rfl | hq
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqz⟩)
        · exact Finset.mem_union_right _ (by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨q, hq, hqz⟩)
      have hhead := h g (by simp)
      have htail := rowsBad_card_le B gs (fun q hq => h q (by simp [hq]))
      have hcomm : (gs.length + 1) * B = B + gs.length * B := by
        rw [Nat.succ_mul, Nat.add_comm]
      refine le_trans (Finset.card_le_card hsub) ?_
      refine le_trans (Finset.card_union_le _ _) ?_
      simp only [List.length_cons]
      rw [hcomm]
      exact Nat.add_le_add hhead htail

/-- The trace-level count: `rowsBad_card_le` at the BFS rows of a generated tree. -/
theorem seedBad_card_le (B : ℕ) (t : NTree (GenComputeRow K))
    (hrow : ∀ g ∈ bfsRows t,
      (Finset.univ.filter (fun z : K => ¬ RowSeedGood z g)).card ≤ B) :
    (Finset.univ.filter
        (fun z : K => ∃ g ∈ bfsRows t, ¬ RowSeedGood z g)).card
      ≤ (bfsRows t).length * B :=
  rowsBad_card_le B (bfsRows t) hrow

/-- **A seed outside the counted bad set is good.**

The step that makes the count usable, and which was described before it existed. -/
theorem seedGood_of_not_mem_seedBad (z : K) (t : NTree (GenComputeRow K))
    (hz : z ∉ Finset.univ.filter
      (fun w : K => ∃ g ∈ bfsRows t, ¬ RowSeedGood w g)) :
    SeedGood z t := by
  refine seedGood_of_bfsRows z t ?_
  intro g hg
  by_contra hbad
  exact hz (by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨g, hg, hbad⟩)

/-! ### Threading into `V_comp` -/

-- `V_comp` needs no finiteness of `K`; the section's `Fintype`/`DecidableEq` serve the counting
-- lemmas only, and demanding them here would force callers to supply instances they do not need.
omit [Fintype K] [DecidableEq K] in
/-- **`V_comp` at every node of any accepted program, from a single good-seed hypothesis.**

`genComputeSkeleton_inTree_Vcomp`'s three separate state-gated hypotheses are replaced by one
`SeedGood z t`.  Combined with `seedGood_of_bfsRows` and `seedBad_card_le`, this is the form the
generic route needs: a `V_comp` that holds for every program, at every seed outside a counted bad
set.
-- -/
theorem genComputeSkeleton_inTree_Vcomp_of_seedGood (z α : K) (hz : z ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hgood : SeedGood z t)
    (u : NTree (GenComputeRow K)) (hu : InTree t u) (acc : ℕ) :
    Vcomp (renderNode z α {(u.label) with stamp := stampOfAcc u.label.skel.state acc}).row.2.1
      (renderNode z α {(u.label) with stamp := stampOfAcc u.label.skel.state acc}).row.2.2.1
      (renderNode z α {(u.label) with stamp := stampOfAcc u.label.skel.state acc}).row.2.2.2 :=
  genComputeSkeleton_inTree_Vcomp z α hz h
    (fun v hv hc => (hgood v hv).1 hc)
    (fun v hv h5 => (hgood v hv).2.1 h5)
    (fun v hv h3 => (hgood v hv).2.2 h3)
    u hu acc

/-! ## Non-vacuity

The bound is not vacuous in either direction: cells exist whose dyck polynomial is nonzero (above),
and the bad-seed set really can be nonempty, so `hdyck` genuinely is a counted event rather than a
theorem.  A witness for the second half is left to the seed-specific fixtures, which already
`decide` the condition at their own seeds (`GenMatmulHyps.lean`, `AllCellDyckNe`).
-/

/-- A cell has at least two leaves.  This is the arithmetic fact the degree bound needs; it is
**not** a non-vacuity witness and exhibits no bad seed. -/
theorem cell_leaves_ge_two (l r : Noun) : 2 ≤ (Noun.cell l r).leaves := by
  have hl := l.one_le_leaves
  have hr := r.one_le_leaves
  have hcell : (Noun.cell l r).leaves = l.leaves + r.leaves := rfl
  omega

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.listPoly_dyckBits_cell_ne_zero
#print axioms Nock.NockVMROM.Thm54.TraceGen.consHead_dyck_zero_card_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.consHead_dyck_zero_card_le_window
#print axioms Nock.NockVMROM.Thm54.TraceGen.consHeads_dyck_zero_card_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.encC_collision_card_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.op5ResultsAgree_bad_card_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.op3CallSize_bad_card_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.fingerprint_vectors_ne_of_ne
#print axioms Nock.NockVMROM.Thm54.TraceGen.encC_collision_card_le_of_ne
#print axioms Nock.NockVMROM.Thm54.TraceGen.op5ResultsAgree_bad_card_le_of_ne
#print axioms Nock.NockVMROM.Thm54.TraceGen.rowsBad_card_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.seedGood_of_bfsRows
#print axioms Nock.NockVMROM.Thm54.TraceGen.seedBad_card_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_inTree_Vcomp_of_seedGood
#print axioms Nock.NockVMROM.Thm54.TraceGen.seedGood_of_not_mem_seedBad
