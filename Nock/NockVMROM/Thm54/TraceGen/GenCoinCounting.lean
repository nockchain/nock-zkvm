/-
  Nock/NockVMROM/Thm54/TraceGen/GenCoinCounting.lean

  **The fourth counted event: compute-table RLC coins.**

  So the condition needs the route `GenChainedLanguage.lean:401` names and nobody had built: the
  **counted** one.  On a live `.s5` row with unequal result fingerprints, `rlc5` asks that a random
  linear combination of a nonzero three-vector be nonzero, so the failing coin vectors are a
  hyperplane of `K³` and there are `|K|²` of them; over `N` rows at most `N · |K|²` of the `|K|³`
  coin vectors fail, and a good one **exists** as soon as `N < |K|`.

  * `Nock/TableWFBounds.lean` carries the whole linear algebra: `kernel`, `kernel_card`
    (`= |K| * |K|`), `badComputeAt` with `rlc5Holds_iff_not_mem_bad` and `badComputeAt_card_le`,
    `badComputeAny` over a `Fin n` family with `rlc5All_iff_not_mem_badAny` and
    `badComputeAny_card_le`, and `badComputeAny_prob_le`.
  * `GenWF.lean:435` carries `exists_rlc5_coins`: good coins exist for any `Fin n → Pub K` family
    with `n < Fintype.card K`.

  All of that is stated over an **abstract** `Fin n → ComputeTable.Pub K` family and nothing
  connected it to `ComputeCoinsGeneric`, whose index set is `List.range' 1 (bfsForest [u]).length`
  and whose rows are `renderNode z α (bfsLabelAt u i)`.  That bridge — and the existence theorem,
  the emptiness/non-emptiness criteria and the discharge — is what this module adds.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenChainedLanguage

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.TableWFBounds
open ComputeTable

variable {K : Type} [Field K]

/-! ## The three deltas are not all zero on a live row

`needsRlc5 pub` is `pub.state =.s5 ∧ pub.sf1_e ≠ pub.sf2_e`, and `ComputeTable.FP` has exactly the
three fields `size`, `dyck`, `leaf`, so the fingerprints are equal iff all three deltas vanish.
`some_delta_of_fp_ne` (`TableWFBounds.lean:127`) is that fact; this is its `needsRlc5` form, which
is what the counting consumes. -/

theorem deltas_ne_zero_of_needsRlc5 {pub : Pub K} (h : needsRlc5 pub) :
    deltaSize pub ≠ 0 ∨ deltaDyck pub ≠ 0 ∨ deltaLeaf pub ≠ 0 := by
  simpa [deltaSize, deltaDyck, deltaLeaf] using some_delta_of_fp_ne h.2

/-- Off `.s5` nothing is asked. -/
theorem not_needsRlc5_of_ne_s5 {pub : Pub K} (h : pub.state ≠ State.s5) :
    ¬ needsRlc5 pub :=
  fun hn => h hn.1

/-! ## The BFS-indexed pub family of a generated compute tree

`ComputeCoinsGeneric` quantifies over the 1-based BFS index set `List.range' 1 h`; the counting
machinery of `TableWFBounds` is stated over `Fin n`.  This is the reindexing. -/

/-- The rendered `Pub` at 0-based BFS position `j` of a generated compute tree — i.e. at the 1-based
index `j + 1` that `bfsLabelAt` uses. -/
def treeComputePub (z α : K) (u : NTree (GenComputeRow K))
    (j : Fin (bfsForest [u]).length) : Pub K :=
  (renderNode z α (bfsLabelAt u (j.1 + 1))).row.2.2.1

@[simp] theorem treeComputePub_state (z α : K) (u : NTree (GenComputeRow K))
    (j : Fin (bfsForest [u]).length) :
    (treeComputePub z α u j).state = (bfsLabelAt u (j.1 + 1)).skel.state :=
  renderNode_pub_state z α _

/-- `ComputeCoinsGeneric` in `Fin`-indexed form. -/
theorem computeCoinsGeneric_iff_forall_fin (z α a b c : K) (u : NTree (GenComputeRow K)) :
    ComputeCoinsGeneric z α a b c u ↔
      ∀ j : Fin (bfsForest [u]).length, rlc5Holds a b c (treeComputePub z α u j) := by
  constructor
  · intro h j
    exact h (j.1 + 1) (List.mem_range'_1.mpr ⟨Nat.le_add_left 1 j.1, by omega⟩)
  · intro h i hi
    obtain ⟨h1, h2⟩ := List.mem_range'_1.mp hi
    have hlt : i - 1 < (bfsForest [u]).length := by omega
    have hi' : i - 1 + 1 = i := by omega
    have := h ⟨i - 1, hlt⟩
    rwa [treeComputePub, hi'] at this

/-! ## The counted event -/

noncomputable section
variable [Fintype K] [DecidableEq K]

/-- **The failing coin vectors of a generated compute tree.**  The fourth counted event, alongside
`SeedGood`, `sizeWindowFailureSeeds` and `badSeeds` — but over **coins**, not seeds. -/
def computeCoinFailure (z α : K) (u : NTree (GenComputeRow K)) : Finset (ComputeCoins K) :=
  badComputeAny (treeComputePub z α u)

theorem mem_computeCoinFailure_iff (z α : K) (u : NTree (GenComputeRow K))
    (p : ComputeCoins K) :
    p ∈ computeCoinFailure z α u ↔
      ∃ j : Fin (bfsForest [u]).length,
        needsRlc5 (treeComputePub z α u j) ∧
          rlc5Form p.1 p.2.1 p.2.2 (treeComputePub z α u j) = 0 := by
  constructor
  · intro hmem
    simp only [computeCoinFailure, badComputeAny, Finset.mem_biUnion] at hmem
    obtain ⟨j, -, hj⟩ := hmem
    simp only [badComputeAt, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨j, hj.1, by simpa [rlc5Form, linearFormCoins, mul_comm] using hj.2⟩
  · rintro ⟨j, hn, h0⟩
    simp only [computeCoinFailure, badComputeAny, Finset.mem_biUnion]
    refine ⟨j, Finset.mem_univ _, ?_⟩
    simp only [badComputeAt, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hn, by simpa [rlc5Form, linearFormCoins, mul_comm] using h0⟩

/-- **The discharge**: coins outside the counted set satisfy the condition, and conversely. -/
theorem computeCoinsGeneric_iff_not_mem (z α a b c : K) (u : NTree (GenComputeRow K)) :
    ComputeCoinsGeneric z α a b c u ↔ (a, b, c) ∉ computeCoinFailure z α u := by
  rw [computeCoinsGeneric_iff_forall_fin]
  exact rlc5All_iff_not_mem_badAny (a, b, c) (treeComputePub z α u)

/-- The discharge, in the direction a consumer needs. -/
theorem computeCoinsGeneric_of_not_mem (z α a b c : K) (u : NTree (GenComputeRow K))
    (h : (a, b, c) ∉ computeCoinFailure z α u) :
    ComputeCoinsGeneric z α a b c u :=
  (computeCoinsGeneric_iff_not_mem z α a b c u).mpr h

/-- **The cardinality bound**: at most one hyperplane per BFS row. -/
theorem computeCoinFailure_card_le (z α : K) (u : NTree (GenComputeRow K)) :
    (computeCoinFailure z α u).card
      ≤ (bfsForest [u]).length * (Fintype.card K * Fintype.card K) :=
  badComputeAny_card_le (treeComputePub z α u)

/-- The failure probability of a uniform coin vector, `N / |K|`. -/
theorem computeCoinFailure_prob_le (z α : K) (u : NTree (GenComputeRow K)) :
    ((computeCoinFailure z α u).card : ℚ) / (Fintype.card (ComputeCoins K) : ℚ)
      ≤ ((bfsForest [u]).length : ℚ) / (Fintype.card K : ℚ) :=
  badComputeAny_prob_le (treeComputePub z α u)

/-! ## Existence — the coins as a compiler choice -/

/-- **Good coins exist** as soon as the compute-row count is below the field size.  Existence
outside a counted set, not `∀ coins`. -/
theorem exists_computeCoinsGeneric (z α : K) (u : NTree (GenComputeRow K))
    (hrow : (bfsForest [u]).length < Fintype.card K) :
    ∃ a b c : K, ComputeCoinsGeneric z α a b c u := by
  obtain ⟨coins, hc⟩ := exists_rlc5_coins (treeComputePub z α u) hrow
  exact ⟨coins.1, coins.2.1, coins.2.2,
    (computeCoinsGeneric_iff_forall_fin z α coins.1 coins.2.1 coins.2.2 u).mpr hc⟩

/-- Existence at the tree the chain's hypotheses are actually stated at, `airReorder t`. -/
theorem exists_computeCoinsGeneric_airReorder (z α : K) (t : NTree (GenComputeRow K))
    (hrow : (bfsForest [airReorder t]).length < Fintype.card K) :
    ∃ a b c : K, ComputeCoinsGeneric z α a b c (airReorder t) :=
  exists_computeCoinsGeneric z α (airReorder t) hrow

/-- Existence stated at the carrier's own `compRows`: `genExactConfig` sets
`compRows := (bfsForest [genComputeRows z α t]).length`, so this is literally the side condition
"compute row count `<` field size". -/
theorem exists_computeCoinsGeneric_of_compRows (z α : K) (t : NTree (GenComputeRow K))
    (hrow : (bfsForest [genComputeRows z α t]).length < Fintype.card K) :
    ∃ a b c : K, ComputeCoinsGeneric z α a b c (airReorder t) := by
  refine exists_computeCoinsGeneric_airReorder z α t ?_
  rwa [genComputeRows_bfsForest_length z α t, bfsRows_length] at hrow

/-! ## When the event is empty, and when it is not -/

/-- On an OP5-free program the counted event is **empty** — the counting agrees with
`computeCoinsGeneric_of_noOp5` rather than merely coexisting with it. -/
theorem computeCoinFailure_eq_empty_of_noOp5 (z α : K) (u : NTree (GenComputeRow K))
    (h5 : ∀ v, InTree u v → v.label.skel.state ≠ State.s5) :
    computeCoinFailure z α u = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
  obtain ⟨j, hn, -⟩ := (mem_computeCoinFailure_iff z α u p).mp hp
  refine not_needsRlc5_of_ne_s5 ?_ hn
  rw [treeComputePub_state]
  obtain ⟨v, hv, hskel⟩ :=
    bfsLabelAt_skel_inTree u (j.1 + 1)
      (List.mem_range'_1.mpr ⟨Nat.le_add_left 1 j.1, by omega⟩)
  rw [hskel]
  exact h5 v hv

/-- A refutation at one coin vector puts that vector **in** the event — so `GM` §6's refutations are
non-emptiness witnesses for this Finset, not a separate phenomenon. -/
theorem mem_computeCoinFailure_of_not_computeCoinsGeneric {z α a b c : K}
    {u : NTree (GenComputeRow K)} (h : ¬ ComputeCoinsGeneric z α a b c u) :
    (a, b, c) ∈ computeCoinFailure z α u := by
  by_contra hp
  exact h (computeCoinsGeneric_of_not_mem z α a b c u hp)

theorem computeCoinFailure_nonempty_of_not_computeCoinsGeneric {z α a b c : K}
    {u : NTree (GenComputeRow K)} (h : ¬ ComputeCoinsGeneric z α a b c u) :
    (computeCoinFailure z α u).Nonempty :=
  ⟨(a, b, c), mem_computeCoinFailure_of_not_computeCoinsGeneric h⟩

end

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.deltas_ne_zero_of_needsRlc5
#print axioms Nock.NockVMROM.Thm54.TraceGen.computeCoinsGeneric_iff_forall_fin
#print axioms Nock.NockVMROM.Thm54.TraceGen.mem_computeCoinFailure_iff
#print axioms Nock.NockVMROM.Thm54.TraceGen.computeCoinsGeneric_iff_not_mem
#print axioms Nock.NockVMROM.Thm54.TraceGen.computeCoinFailure_card_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.computeCoinFailure_prob_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_computeCoinsGeneric
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_computeCoinsGeneric_of_compRows
#print axioms Nock.NockVMROM.Thm54.TraceGen.computeCoinFailure_eq_empty_of_noOp5
#print axioms Nock.NockVMROM.Thm54.TraceGen.mem_computeCoinFailure_of_not_computeCoinsGeneric
