import Nock.NockVMROM.Thm54.EdgeComparisonCensus
import Nock.NockVMROM.Thm54.SizeWindowCounting
import Nock.NockVMROM.Thm54.NonterminalServedRow

/-!
# A comparison census with a genuinely distinct noun pair

Every entry of `P8Census.skeletonComparisons` is one noun pair the verifier compares through NPR
fingerprints.  Almost all of them are *honesty equations*: at a skeleton that really is the
skeleton of a Nock evaluation the two sides are the same noun, so `SepSeed` holds vacuously and the
census contributes no bad seed.

Exactly one comparison role escapes that: `equalityOperand`, which occurs at `OP_5` and only at
`OP_5` (`equalityOperand_role_iff_s5`).  `OP_5` is Nock's `=`, and the paper states its two
cases explicitly -- when the evaluation is `0` the two subformula products are equal, and "in the
contrary case when the evaluation is `1`... the two subformula products cannot be equal".  In that
contrary case the census compares two *distinct* nouns, and `Lem:ion_univariate_sec`, which is stated for `n_1 \neq n_2`, is exactly what bounds the seeds at
which they collide.

`OP_6` supplies a second source: its comparison list contains the branch call's formula against
**both** committed branch formulas, so
at most one of the two occurrences can be a self-comparison.

This module builds the `OP_5` witness at the honest Nock evaluation

```
*[0 [5 [1 [7 9]] [1 [8 10]]]] = 1
```

whose two equality operands are `[7 9]` and `[8 10]`.  They are distinct, and over
`K97cubic = GaloisField 97 3` their two-leaf NPR leaf polynomials `7 + 9X` and `8 + 10X` agree at
exactly one point.  The resulting comparison census has twenty-four entries, twenty-three of them
self-comparisons and one genuinely distinct; its bad-seed set is the non-empty singleton `{-1}`, and
its `collisionFailureEvent` is non-empty.

Scope, stated up front.  This is a *census-level* witness.  `SemanticSkeleton` is pure pre-seed data
and `EdgeComparisonCensus.CombinedSkeletonCensus` reads only that data, so the census, its bad-seed
set and its collision event are the production objects at their production definitions.  No
`BuildableNockExecution` over this skeleton is constructed here, so nothing downstream of
`HonestCommitment.Data` is claimed and no package, acceptance or containment statement is touched.
`Nock.evalN` agreement is compiled so the skeleton is certified to be the skeleton of a real Nock
evaluation rather than an invented row.
-/

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.EqualityOperandCensus

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete

noncomputable section

local instance prime97e : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97e : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-! ## A. Where a non-self comparison can occur at all

These theorems are generic in the field and in the row; they localize the only two comparison roles
whose two sides are not forced equal by honesty. -/

/-- A self-comparison separates at every seed, so a census of self-pairs is vacuous. -/
theorem sepSeed_self {K : Type*} [Field K] (z : K) (P : Noun) :
    GlobalCarryRecognizer.SepSeed z P P :=
  fun h => absurd rfl h

/-- `equalityOperand` occurs in the fixed role matrix at `OP_5` and nowhere else. -/
theorem equalityOperand_role_iff_s5 (st : ComputeTable.State) :
    SemanticTrace.ComparisonRole.equalityOperand ∈
        SemanticTrace.requiredComparisonRoles st ↔ st = ComputeTable.State.s5 := by
  cases st <;> decide

/-- Every `OP_5` row contributes the comparison of its two equality operands.  Unlike every other
occurrence in the row this is not an honesty equation: the paper requires the two operands to
be **unequal** whenever the row's evaluation is `1`. -/
theorem equalityOperand_mem_skeletonComparisons
    (K : Type*) [Field K] (s : ComputeRowSkeleton)
    (h : s.state = ComputeTable.State.s5) :
    P8Census.skeletonUse SemanticTrace.ComparisonRole.equalityOperand
        (P8Census.skeletonSubformula s 0 TripleSlot.result)
        (P8Census.skeletonSubformula s 1 TripleSlot.result) ∈
      P8Census.skeletonComparisons (K := K) s := by
  simp [P8Census.skeletonComparisons, h]

/-- The `OP_5` operand pair is an entry of the pre-seed pair list of any skeleton containing an
`OP_5` row. -/
theorem equalityOperand_pair_mem_skeletonPairs
    (K : Type*) [Field K] (S : SemanticSkeleton) (s : ComputeRowSkeleton)
    (hs : s ∈ computeSkeletonRows S) (h : s.state = ComputeTable.State.s5) :
    (P8Census.skeletonSubformula s 0 TripleSlot.result,
        P8Census.skeletonSubformula s 1 TripleSlot.result) ∈
      BoundSemanticTrace.skeletonPairs K S := by
  rw [BoundSemanticTrace.skeletonPairs, List.mem_append]
  refine Or.inr (List.mem_map.mpr ⟨P8Census.skeletonUse
    SemanticTrace.ComparisonRole.equalityOperand
    (P8Census.skeletonSubformula s 0 TripleSlot.result)
    (P8Census.skeletonSubformula s 1 TripleSlot.result), ?_, rfl⟩)
  rw [P8Census.skeletonComparisonCensus, List.mem_flatMap]
  exact ⟨s, hs, equalityOperand_mem_skeletonComparisons K s h⟩

/-- `OP_6` is the second source of a non-self pair: the census compares the branch call's formula
against **both** committed branch formulas, so the two occurrences cannot both be
self-comparisons unless the two branches carry the same formula. -/
theorem s6_branch_pairs_not_both_self
    (K : Type*) [Field K] (s : ComputeRowSkeleton)
    (h : s.state = ComputeTable.State.s6)
    (hne : P8Census.skeletonDec s DecSlot.f_tth ≠ P8Census.skeletonDec s DecSlot.f_ttt) :
    (P8Census.skeletonUse SemanticTrace.ComparisonRole.recursiveFormula
        (P8Census.skeletonSubformula s 0 TripleSlot.formula)
        (P8Census.skeletonDec s DecSlot.f_tth) ∈
          P8Census.skeletonComparisons (K := K) s) ∧
      (P8Census.skeletonUse SemanticTrace.ComparisonRole.recursiveFormula
        (P8Census.skeletonSubformula s 0 TripleSlot.formula)
        (P8Census.skeletonDec s DecSlot.f_ttt) ∈
          P8Census.skeletonComparisons (K := K) s) ∧
      ¬ (P8Census.skeletonSubformula s 0 TripleSlot.formula =
            P8Census.skeletonDec s DecSlot.f_tth ∧
          P8Census.skeletonSubformula s 0 TripleSlot.formula =
            P8Census.skeletonDec s DecSlot.f_ttt) := by
  refine ⟨by simp [P8Census.skeletonComparisons, h], by simp [P8Census.skeletonComparisons, h], ?_⟩
  rintro ⟨h1, h2⟩
  exact hne (h1.symm.trans h2)

/-! ## B. The honest `OP_5` evaluation

`*[0 [5 [1 [7 9]] [1 [8 10]]]]`: two constant subformulas returning two distinct nouns, so Nock's
`=` returns `1`. -/

/-- Left equality operand. -/
def operandLeft : Noun := .cell (.atom 7) (.atom 9)

/-- Right equality operand.  Two-leaf nouns have leaf polynomial `a + b X`; `(7,9)` and `(8,10)`
agree at exactly `X = -1`. -/
def operandRight : Noun := .cell (.atom 8) (.atom 10)

theorem operands_ne : operandLeft ≠ operandRight := by decide

def op5Subject : Noun := .atom 0
def leftFormula : Noun := .cell (.atom 1) operandLeft
def rightFormula : Noun := .cell (.atom 1) operandRight
def op5Tail : Noun := .cell leftFormula rightFormula
def op5Formula : Noun := .cell (.atom 5) op5Tail
def op5Result : Noun := .atom 1

/-- The row is a real Nock evaluation, checked against the reference interpreter that the I3
adequacy gate pins to the external Nock implementation. -/
theorem op5_is_real_nock :
    Nock.evalN 8 op5Subject op5Formula = some op5Result ∧
      Nock.evalN 8 op5Subject leftFormula = some operandLeft ∧
      Nock.evalN 8 op5Subject rightFormula = some operandRight := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The same three evaluations under the bounded modular evaluator the `OP_5` local certificate
consumes. -/
theorem op5_is_real_bounded_nock :
    FieldEmbedding.evalFBy 97 8 op5Subject op5Formula = some op5Result ∧
      FieldEmbedding.evalFBy 97 8 op5Subject leftFormula = some operandLeft ∧
      FieldEmbedding.evalFBy 97 8 op5Subject rightFormula = some operandRight := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Nock's `=` really returns `1` here, so the row's committed evaluation is the honest one. -/
theorem op5Result_is_tis : Noun.tis operandLeft operandRight = op5Result := by decide

/-! ## C. The committed skeleton -/

/-- The `OP_5` parent row.  Its two equality operands are distinct nouns. -/
def op5Row : ComputeRowSkeleton where
  state := ComputeTable.State.s5
  subject := op5Subject
  formula := op5Formula
  evaluation := op5Result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => .atom 5
    | .f_t => op5Tail
    | .f_th => leftFormula
    | .f_tt => rightFormula
    | .f_tth => .atom 0
    | .f_ttt => .atom 0
  subformula := fun i _ slot =>
    if (i : ℕ) = 0 then
      (match slot with
        | .subject => op5Subject
        | .formula => leftFormula
        | .result => operandLeft)
    else
      (match slot with
        | .subject => op5Subject
        | .formula => rightFormula
        | .result => operandRight)
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 0⟩

/-- One `OP_1` constant row: `*[a 1 b] = b`. -/
def op1RowOf (formula result : Noun) : ComputeRowSkeleton where
  state := ComputeTable.State.s1
  subject := op5Subject
  formula := formula
  evaluation := result
  decomposition := fun slot _ =>
    match slot with
    | .f_h => .atom 1
    | _ => result
  subformula := fun _ h _ => absurd h (Nat.not_lt_zero _)
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 0⟩

theorem op5Row_sf0_result :
    P8Census.skeletonSubformula op5Row 0 TripleSlot.result = operandLeft := by
  simp [P8Census.skeletonSubformula, op5Row, ComputeTable.fanoutComp]

theorem op5Row_sf1_result :
    P8Census.skeletonSubformula op5Row 1 TripleSlot.result = operandRight := by
  simp [P8Census.skeletonSubformula, op5Row, ComputeTable.fanoutComp]

def op5Tree : NTree ComputeRowSkeleton :=
  .node op5Row
    [.node (op1RowOf leftFormula operandLeft) [],
      .node (op1RowOf rightFormula operandRight) []]

/-- The pre-seed commitment.  Only `computeTree` is read by the comparison census. -/
def op5Skeleton : SemanticSkeleton where
  computeTree := op5Tree
  memoryForest := []

theorem op5Skeleton_rows :
    computeSkeletonRows op5Skeleton =
      [op5Row, op1RowOf leftFormula operandLeft, op1RowOf rightFormula operandRight] := by
  simp [computeSkeletonRows, op5Skeleton, op5Tree, bfsForest, NTree.children, NTree.label]

theorem op5Row_mem_rows : op5Row ∈ computeSkeletonRows op5Skeleton := by
  rw [op5Skeleton_rows]; simp

/-! ## D. The census content, listed exactly -/

def op5Pairs : List (Noun × Noun) :=
  EdgeComparisonCensus.combinedSkeletonPairs K97cubic op5Skeleton

/-- The complete twenty-four-entry census: three public-claim pairs, nine `OP_5` occurrences, three
occurrences at each of the two `OP_1` children, and six edge occurrences.  Exactly one entry, the
`OP_5` equality-operand pair, is not a self-comparison. -/
theorem op5Pairs_eq :
    op5Pairs =
      [ (op5Subject, op5Subject), (op5Formula, op5Formula), (op5Result, op5Result),
        (Noun.atom 5, Noun.atom 5), (op5Formula, op5Formula), (op5Tail, op5Tail),
        (op5Subject, op5Subject), (leftFormula, leftFormula),
        (op5Subject, op5Subject), (rightFormula, rightFormula),
        (operandLeft, operandRight), (op5Result, op5Result),
        (Noun.atom 1, Noun.atom 1), (leftFormula, leftFormula), (operandLeft, operandLeft),
        (Noun.atom 1, Noun.atom 1), (rightFormula, rightFormula), (operandRight, operandRight),
        (op5Subject, op5Subject), (leftFormula, leftFormula), (operandLeft, operandLeft),
        (op5Subject, op5Subject), (rightFormula, rightFormula),
        (operandRight, operandRight) ] := by
  rw [op5Pairs, EdgeComparisonCensus.combinedSkeletonPairs,
    BoundSemanticTrace.skeletonPairs, P8Census.skeletonComparisonCensus, op5Skeleton_rows]
  conv_lhs =>
    simp [P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
      P8Census.skeletonSubformula,
      SemanticTrace.ComparisonUse.pair, SemanticSkeleton.publicClaim,
      EdgeComparisonCensus.edgePairs, EdgeComparisonCensus.rowEdgePairs,
      EdgeComparisonCensus.edgeTriple, op5Skeleton, op5Tree, bfsForest, NTree.childOpt,
      NTree.children, NTree.label, op5Row, op1RowOf, decActive, hasTailDecomposition,
      ComputeTable.fanoutComp, op5Result_is_tis]
  rfl

theorem op5Pairs_length : op5Pairs.length = 24 := by
  rw [op5Pairs_eq]; rfl

/-- Every entry of the census is a self-comparison except the single `OP_5` equality-operand
pair. -/
theorem op5Pairs_dichotomy (P : Noun × Noun) (hP : P ∈ op5Pairs) :
    P.1 = P.2 ∨ P = (operandLeft, operandRight) := by
  rw [op5Pairs_eq] at hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h <;> subst h <;> simp

theorem op5Pairs_bounded (P : Noun × Noun) (hP : P ∈ op5Pairs) :
    P.1.leaves ≤ 7 ∧ P.2.leaves ≤ 7 := by
  rw [op5Pairs_eq] at hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h <;> subst h <;> exact ⟨by decide, by decide⟩

/-- The production combined census over the `OP_5` skeleton, at leaf window `Λ = 7`. -/
def op5Census : EdgeComparisonCensus.CombinedSkeletonCensus K97cubic op5Skeleton 7 where
  p8 :=
    { leaves_bounded := fun pair hp =>
        op5Pairs_bounded pair (by
          rw [op5Pairs, EdgeComparisonCensus.combinedSkeletonPairs, List.mem_append]
          exact Or.inl hp) }
  edges :=
    { leaves_bounded := fun pair hp =>
        op5Pairs_bounded pair (by
          rw [op5Pairs, EdgeComparisonCensus.combinedSkeletonPairs, List.mem_append]
          exact Or.inr hp) }

theorem op5Census_count : op5Census.census.count = 24 := op5Pairs_length

theorem op5Census_pair_mem (i : Fin op5Census.census.count) :
    op5Census.census.pair i ∈ op5Pairs :=
  List.get_mem _ _

/-- Restated at the census: exactly the `OP_5` equality operands are compared as distinct nouns. -/
theorem op5Census_dichotomy (i : Fin op5Census.census.count) :
    (op5Census.census.pair i).1 = (op5Census.census.pair i).2 ∨
      op5Census.census.pair i = (operandLeft, operandRight) :=
  op5Pairs_dichotomy _ (op5Census_pair_mem i)

/-- The distinct pair really is an entry, located through the generic `OP_5` lookup rather than by
index arithmetic. -/
theorem op5Census_has_distinct_pair :
    ∃ i : Fin op5Census.census.count,
      op5Census.census.pair i = (operandLeft, operandRight) := by
  have hmem := equalityOperand_pair_mem_skeletonPairs K97cubic op5Skeleton op5Row
    op5Row_mem_rows rfl
  rw [op5Row_sf0_result, op5Row_sf1_result] at hmem
  exact op5Census.p8_pair_lookup hmem

theorem op5Census_distinct_pair_is_distinct :
    ∃ i : Fin op5Census.census.count,
      op5Census.census.pair i = (operandLeft, operandRight) ∧
        (op5Census.census.pair i).1 ≠ (op5Census.census.pair i).2 := by
  obtain ⟨i, hi⟩ := op5Census_has_distinct_pair
  exact ⟨i, hi, by rw [hi]; exact operands_ne⟩

/-! ## E. The collision event is genuinely non-trivial

`SepSeed z P Q` is the good event that `z` separates `P` and `Q` whenever their leaf/Dyck data
differ.  For the two `OP_5` operands it is a real condition: the two leaf
polynomials `7 + 9X` and `8 + 10X` agree at exactly one point of `K97cubic`. -/

theorem operands_leafF_left :
    NPR.leafF (K := K97cubic) operandLeft = [(7 : K97cubic), (9 : K97cubic)] := by
  simp [operandLeft, NPR.leafF, Noun.leafList]

theorem operands_leafF_right :
    NPR.leafF (K := K97cubic) operandRight = [(8 : K97cubic), (10 : K97cubic)] := by
  simp [operandRight, NPR.leafF, Noun.leafList]

theorem leafPoly_eval_left (z : K97cubic) :
    (NPR.listPoly (NPR.leafF (K := K97cubic) operandLeft)).eval z = 7 + 9 * z := by
  rw [operands_leafF_left, NPR.listPoly_cons, NPR.listPoly_cons, NPR.listPoly_nil]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    mul_zero, add_zero]
  ring

theorem leafPoly_eval_right (z : K97cubic) :
    (NPR.listPoly (NPR.leafF (K := K97cubic) operandRight)).eval z = 8 + 10 * z := by
  rw [operands_leafF_right, NPR.listPoly_cons, NPR.listPoly_cons, NPR.listPoly_nil]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    mul_zero, add_zero]
  ring

/-- The two operands' leaf/Dyck data genuinely differ, so `SepSeed` is not satisfied vacuously. -/
theorem operands_data_ne :
    (NPR.leafF (K := K97cubic) operandLeft, NPR.dyckBits (K := K97cubic) operandLeft) ≠
      (NPR.leafF (K := K97cubic) operandRight, NPR.dyckBits (K := K97cubic) operandRight) := by
  intro h
  have hl := congrArg Prod.fst h
  rw [operands_leafF_left, operands_leafF_right] at hl
  simp only [List.cons.injEq] at hl
  have h1 : (1 : K97cubic) = 0 := by linear_combination -hl.1
  exact one_ne_zero h1

theorem operands_leaves_eq : operandLeft.leaves = operandRight.leaves := rfl

theorem operands_dyckBits_eq :
    NPR.dyckBits (K := K97cubic) operandLeft = NPR.dyckBits (K := K97cubic) operandRight := rfl

/-- The exact collision locus: the two distinct operands share a fingerprint at exactly one seed. -/
theorem operands_fn_eq_iff (z : K97cubic) :
    NPR.fn (K := K97cubic) operandLeft z = NPR.fn (K := K97cubic) operandRight z ↔ z = -1 := by
  constructor
  · intro h
    have hleaf := congrArg (fun x : K97cubic × K97cubic × K97cubic => x.2.1) h
    simp only [NPR.fn] at hleaf
    rw [leafPoly_eval_left, leafPoly_eval_right] at hleaf
    have h1 : (z + 1 : K97cubic) = 0 := by linear_combination -hleaf
    linear_combination h1
  · rintro rfl
    simp only [NPR.fn, Prod.mk.injEq]
    refine ⟨by rw [operands_leaves_eq], ?_, by rw [operands_dyckBits_eq]⟩
    rw [leafPoly_eval_left, leafPoly_eval_right]
    ring

theorem operands_not_sepSeed_iff (z : K97cubic) :
    ¬ GlobalCarryRecognizer.SepSeed z operandLeft operandRight ↔ z = -1 := by
  constructor
  · intro hbad
    by_contra hz
    exact hbad fun _ hfn => hz ((operands_fn_eq_iff z).mp hfn)
  · intro hz hsep
    exact hsep operands_data_ne ((operands_fn_eq_iff z).mpr hz)

theorem operands_not_sepSeed_at_neg_one :
    ¬ GlobalCarryRecognizer.SepSeed (-1 : K97cubic) operandLeft operandRight :=
  (operands_not_sepSeed_iff (-1)).mpr rfl

theorem operands_sepSeed_at_one :
    GlobalCarryRecognizer.SepSeed (1 : K97cubic) operandLeft operandRight := by
  intro hdata
  by_contra h
  exact NonterminalServedRow.neg_one_ne_one_K97 ((operands_fn_eq_iff 1).mp h).symm

/-- **The census bad-seed set is exactly the single collision seed.** -/
theorem op5Census_badSeeds :
    op5Census.census.badSeeds (K := K97cubic) = {(-1 : K97cubic)} := by
  ext z
  rw [ComparisonCensus.mem_badSeeds_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi⟩
    rcases op5Census_dichotomy i with hself | hpair
    · exfalso
      apply hi
      rw [← hself]
      exact sepSeed_self z _
    · rw [hpair] at hi
      exact (operands_not_sepSeed_iff z).mp hi
  · rintro rfl
    obtain ⟨i, hi⟩ := op5Census_has_distinct_pair
    exact ⟨i, by rw [hi]; exact operands_not_sepSeed_at_neg_one⟩

theorem op5Census_badSeeds_nonempty :
    (op5Census.census.badSeeds (K := K97cubic)).Nonempty := by
  rw [op5Census_badSeeds]
  exact ⟨-1, Finset.mem_singleton_self _⟩

theorem op5Census_badSeeds_card :
    (op5Census.census.badSeeds (K := K97cubic)).card = 1 := by
  rw [op5Census_badSeeds, Finset.card_singleton]

/-- The compiled count sits inside the paper's per-occurrence root bound `count * (2Λ - 1)`. -/
theorem op5Census_badSeeds_within_paper_bound :
    (op5Census.census.badSeeds (K := K97cubic)).card ≤ op5Census.census.count * (2 * 7 - 1) :=
  op5Census.census.badSeeds_card_le

/-- **The collision failure event is non-empty**, which is what the released fixture's census could
not exhibit. -/
theorem op5_collisionFailureEvent_nonempty :
    (collisionFailureEvent (K := K97cubic) op5Census.census).Nonempty := by
  obtain ⟨i, hi⟩ := op5Census_has_distinct_pair
  refine ⟨((0, 0), (0, -1)), ?_⟩
  rw [mem_collisionFailureEvent_iff]
  exact ⟨i, by rw [hi]; exact operands_not_sepSeed_at_neg_one⟩

theorem op5_collisionFailureEvent_ne_empty :
    collisionFailureEvent (K := K97cubic) op5Census.census ≠ ∅ :=
  Finset.nonempty_iff_ne_empty.mp op5_collisionFailureEvent_nonempty

/-- A good seed exists, and `1` is one. -/
theorem op5Census_one_not_badSeed :
    (1 : K97cubic) ∉ op5Census.census.badSeeds (K := K97cubic) := by
  rw [op5Census_badSeeds, Finset.mem_singleton]
  exact fun h => NonterminalServedRow.neg_one_ne_one_K97 h.symm

/-- At a good seed the census delivers real content: separation at the distinct `OP_5` operand pair
is a theorem about two different nouns, not a vacuity. -/
theorem op5Census_sepSeed_at_good_seed (i : Fin op5Census.census.count) :
    GlobalCarryRecognizer.SepSeed (1 : K97cubic)
      (op5Census.census.pair i).1 (op5Census.census.pair i).2 :=
  P8Census.sepSeed_of_not_mem_badSeeds op5Census.census 1 op5Census_one_not_badSeed i

/-- The four facts side by side: the same census that separates at `1` genuinely fails to separate
at `-1`, on the same pair.  This is the paper's collision event actually occurring. -/
theorem op5Census_is_substantive :
    op5Census.census.count = 24 ∧
      (∃ i : Fin op5Census.census.count,
        op5Census.census.pair i = (operandLeft, operandRight) ∧
          (op5Census.census.pair i).1 ≠ (op5Census.census.pair i).2) ∧
      op5Census.census.badSeeds (K := K97cubic) = {(-1 : K97cubic)} ∧
      (collisionFailureEvent (K := K97cubic) op5Census.census).Nonempty ∧
      (1 : K97cubic) ∉ op5Census.census.badSeeds (K := K97cubic) :=
  ⟨op5Census_count, op5Census_distinct_pair_is_distinct, op5Census_badSeeds,
    op5_collisionFailureEvent_nonempty, op5Census_one_not_badSeed⟩

/-! ## F. The size window at this skeleton

`OP_5` and `OP_1` require no size window, so the fifth failure event is empty here for a stated
reason and not for want of window nouns. -/

theorem op5Skeleton_sizeWindowNouns :
    SizeWindowCounting.skeletonSizeWindowNouns op5Skeleton = [] := by
  rw [SizeWindowCounting.skeletonSizeWindowNouns, op5Skeleton_rows]
  simp [SizeWindowCounting.requiredSizeWindowNouns, op5Row, op1RowOf]

theorem op5Skeleton_sizeWindowFailure_empty :
    SizeWindowCounting.SizeWindowFailure (K := K97cubic) op5Skeleton = ∅ := by
  ext ω
  simp [SizeWindowCounting.mem_SizeWindowFailure_iff, op5Skeleton_sizeWindowNouns]

/-! ## G. The non-trivial census inside the released containment lemmas

`ProductionP8Containment.combined_pairFaithful` is the production step that turns "outside the
bad-seed event" into `PairFaithful` at every census occurrence.  It is skeleton-level, so it applies
here, and it now applies to a census one of whose occurrences compares two different nouns. -/

theorem castInj97 : Set.InjOn (fun k : ℕ => (k : K97cubic)) (Set.Iio 97) :=
  NonterminalServedRow.cast_injOn_97

theorem op5_combinedBounded :
    ProductionP8Containment.CombinedBoundedBy K97cubic 97 op5Skeleton := by
  intro pair hpair
  have h : pair ∈ op5Pairs := hpair
  rw [op5Pairs_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h <;> subst h <;>
    simp [FieldEmbedding.BoundedBy, op5Subject, op5Formula, op5Tail, op5Result,
      leftFormula, rightFormula, operandLeft, operandRight]

/-- Every one of the twenty-four occurrences, the distinct one included, is `PairFaithful` at the
good seed, through the released production theorem rather than a re-proof. -/
theorem op5_pairFaithful_at_good_seed (pair : Noun × Noun) (hpair : pair ∈ op5Pairs) :
    OpcodeSemantics.PairFaithful (1 : K97cubic) 97 pair.1 pair.2 :=
  ProductionP8Containment.combined_pairFaithful op5Skeleton op5Census 97
    op5_combinedBounded 1 op5Census_one_not_badSeed pair hpair

theorem operands_mem_op5Pairs : (operandLeft, operandRight) ∈ op5Pairs := by
  rw [op5Pairs_eq]; simp

/-- The substantive instance: at the good seed the two *different* `OP_5` operands are separated. -/
theorem op5_operands_pairFaithful :
    OpcodeSemantics.PairFaithful (1 : K97cubic) 97 operandLeft operandRight :=
  op5_pairFaithful_at_good_seed _ operands_mem_op5Pairs

/-- Consequently the verifier's fingerprints do tell them apart there. -/
theorem operands_enc_ne_at_good_seed :
    GlobalCarryRecognizer.enc (1 : K97cubic) operandLeft ≠
      GlobalCarryRecognizer.enc (1 : K97cubic) operandRight :=
  fun h => operands_ne (op5_operands_pairFaithful.eq_of_enc_eq castInj97 h)

/-- And at the collision seed they do not: the two distinct operands carry the *same* fingerprint,
so `PairFaithful` genuinely fails.  This is the soundness failure the collision event counts, reproduced at the production `enc`. -/
theorem operands_enc_eq_at_neg_one :
    GlobalCarryRecognizer.enc (-1 : K97cubic) operandLeft =
      GlobalCarryRecognizer.enc (-1 : K97cubic) operandRight := by
  refine ComputeTable.FP.ext ?_ ?_ ?_
  · rw [GlobalCarryRecognizer.enc_size, GlobalCarryRecognizer.enc_size, operands_leaves_eq]
  · rw [GlobalCarryRecognizer.enc_dyck, GlobalCarryRecognizer.enc_dyck, operands_dyckBits_eq]
  · rw [GlobalCarryRecognizer.enc_leaf, GlobalCarryRecognizer.enc_leaf,
      leafPoly_eval_left, leafPoly_eval_right]
    ring

theorem operands_not_pairFaithful_at_neg_one :
    ¬ OpcodeSemantics.PairFaithful (-1 : K97cubic) 97 operandLeft operandRight :=
  fun h => operands_not_sepSeed_at_neg_one h.separates

/-- The released fixture's own repaired seed is exactly this census's collision seed, so a single
execution carrying both this `OP_5` row and that fixture's `OP_0` service would have to move the
seed again -- the same repair `NonterminalServedRow` already had to make once. -/
theorem servedSeed_is_the_collision_seed :
    NonterminalServedRow.servedSeed ∈ op5Census.census.badSeeds (K := K97cubic) := by
  rw [op5Census_badSeeds]
  simp [NonterminalServedRow.servedSeed]

theorem nine_ne_zero_K97 : (9 : K97cubic) ≠ 0 := by
  intro hk
  have hbase : (9 : F97) ≠ 0 := by decide
  apply hbase
  apply (algebraMap F97 K97cubic).injective
  simpa only [map_ofNat, map_zero] using hk

theorem eight_ne_neg_one_K97 : (8 : K97cubic) ≠ -1 := by
  intro h
  exact nine_ne_zero_K97 (by linear_combination h)

/-- A good seed of nontrivial multiplicative order also exists, so the choice of good seed is not
forced onto the order-one element `1`: `8` has order `16` and is not the collision seed. -/
theorem op5Census_good_seed_of_order_sixteen :
    orderOf (8 : K97cubic) = 16 ∧ (8 : K97cubic) ∉ op5Census.census.badSeeds (K := K97cubic) := by
  refine ⟨omega8_order, ?_⟩
  rw [op5Census_badSeeds, Finset.mem_singleton]
  exact eight_ne_neg_one_K97

/-! ## H. Exactly what an execution over this skeleton would still owe

The census is skeleton-level and complete.  Lifting it to a `BuildableNockExecution` -- and hence to
`HonestCommitment.Data`, `CommitmentResidual`, `buildFullPackage` and acceptance -- additionally
requires servicing every committed memory record of every row, which for this skeleton is four
records.  That number is recorded here rather than asserted in prose. -/

/-- The comparison census is a function of the compute tree alone: the memory forest is not read.
So the empty `memoryForest` above is not a weakening of the census -- it is invisible to it -- while
an execution would still have to supply the whole forest. -/
theorem census_ignores_memoryForest (K : Type) [Field K]
    (t : NTree ComputeRowSkeleton) (F₁ F₂ : List (NTree MemoryRowSkeleton)) :
    EdgeComparisonCensus.combinedSkeletonPairs K ⟨t, F₁⟩ =
      EdgeComparisonCensus.combinedSkeletonPairs K ⟨t, F₂⟩ := rfl

theorem op5Skeleton_record_budget :
    Nock.Framework.recordCount ComputeTable.State.s5 = 2 ∧
      Nock.Framework.recordCount ComputeTable.State.s1 = 1 ∧
      ((computeSkeletonRows op5Skeleton).map
        (fun s => Nock.Framework.recordCount s.state)).sum = 4 := by
  refine ⟨rfl, rfl, ?_⟩
  rw [op5Skeleton_rows]
  rfl

end

end Nock.NockVMROM.Thm54.EqualityOperandCensus

#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.sepSeed_self
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.equalityOperand_role_iff_s5
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.equalityOperand_mem_skeletonComparisons
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.equalityOperand_pair_mem_skeletonPairs
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.s6_branch_pairs_not_both_self
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5_is_real_nock
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5_is_real_bounded_nock
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Result_is_tis
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Skeleton_rows
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Pairs_eq
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Pairs_dichotomy
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Pairs_bounded
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Census
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Census_count
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Census_dichotomy
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Census_has_distinct_pair
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Census_distinct_pair_is_distinct
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.operands_data_ne
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.operands_fn_eq_iff
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.operands_not_sepSeed_iff
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.operands_sepSeed_at_one
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Census_badSeeds
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Census_badSeeds_card
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Census_badSeeds_within_paper_bound
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5_collisionFailureEvent_nonempty
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5_collisionFailureEvent_ne_empty
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Census_one_not_badSeed
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Census_sepSeed_at_good_seed
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Census_is_substantive
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Skeleton_sizeWindowNouns
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Skeleton_sizeWindowFailure_empty
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.castInj97
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5_combinedBounded
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5_pairFaithful_at_good_seed
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5_operands_pairFaithful
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.operands_enc_ne_at_good_seed
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.operands_enc_eq_at_neg_one
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.operands_not_pairFaithful_at_neg_one
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.servedSeed_is_the_collision_seed
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Census_good_seed_of_order_sixteen
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.census_ignores_memoryForest
#print axioms Nock.NockVMROM.Thm54.EqualityOperandCensus.op5Skeleton_record_budget
