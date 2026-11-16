/-
  Nock/RedTeam/Batch226Thm54GenericDataFields.lean

  **Non-vacuity for the two premises `GenGenericBounded` / `GenGenericAxisRange` retired.**

  Both take three program-level side conditions (`1 < q`, subject and
  formula `q`-bounded, and a `q`-confined run), so the first question is whether those are jointly
  satisfiable at a real program, and the second is whether the *conclusions* bite.

  For `SkeletonAxisRange` the second question is not idle.  `Batch168.dot_skeletonAxisRange` was the
  only witness in the tree, and `Batch168.dot_no_s0_row` records that Tier A has **no `.s0` row** —
  so the OP0 half of the predicate held there vacuously and only the OP9 half was ever exercised.
  This batch closes that with the smallest program that has an `.s0` row: `*[[5 7] 0 2] = 5`.

  `b226_op0_axis_is_two` is the payoff: at that program the committed OP0 row is present, its state
  *is* `.s0`, and its record-1 axis is the literal `2` — so the first conjunct of
  `SkeletonAxisRange` is a real constraint discharged from `FieldEmbedding.BoundedBy q formula`,
  exactly as `GenGenericAxisRange`'s `NodeAxisInFormula` shape claims.

  **Scope.**  One program, at arbitrary `K`.  Nothing here is a capstone or a `Data`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericAxisRange
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticData

set_option autoImplicit false

namespace Nock.RedTeam.Batch226

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TraceGen

variable {K : Type} [Field K]

/-! ## The smallest program with an `OP_0` row

`*[[5 7] 0 2] = /[2 [5 7]] = 5`. -/

def b226Subject : Noun := .cell (.atom 5) (.atom 7)
def b226Formula : Noun := .cell (.atom 0) (.atom 2)
def b226Result : Noun := .atom 5

/-- The committed OP0 row the generator emits for it. -/
noncomputable def b226Row : GenComputeRow K :=
  skelNode (genSkelOp0 b226Subject b226Formula (.atom 0) (.atom 2) b226Result 2)
    [⟨b226Formula, .atom 2, 3, 0⟩, ⟨b226Subject, b226Result, 2, 0⟩]

/-- The one-node compute tree. -/
noncomputable def b226Tree : NTree (GenComputeRow K) := .node b226Row []

theorem b226_slot : Noun.slot 2 b226Subject = some b226Result := by
  simp [b226Subject, b226Result, Noun.slot]

theorem b226_gen :
    genComputeSkeleton (K := K) 1 b226Subject b226Formula = .ok (b226Tree, b226Result) := by
  simp [genComputeSkeleton, b226Formula, b226Subject, b226Result, b226Tree, b226Row,
    Noun.slot]

theorem b226_subject_bounded {q : ℕ} (hq : 7 < q) :
    FieldEmbedding.BoundedBy q b226Subject := by
  simp [b226Subject, FieldEmbedding.BoundedBy]
  omega

theorem b226_formula_bounded {q : ℕ} (hq : 7 < q) :
    FieldEmbedding.BoundedBy q b226Formula := by
  simp [b226Formula, FieldEmbedding.BoundedBy]
  omega

theorem b226_evalG {q : ℕ} :
    FieldEmbedding.evalGBy q 1 b226Subject b226Formula = some b226Result := by
  simp [FieldEmbedding.evalGBy, b226Subject, b226Formula, b226Result, Noun.slot]

/-! ## The two derived premises, at that program -/

theorem b226_skeletonBounded {q : ℕ} (hq : 7 < q) (z α : K) (inp : MemoryTable.Inputs K) :
    (genSemanticSkeleton (bfsAssign (airReorder (b226Tree (K := K))))
      (genMemoryForest z α MemoryTable.formRDefault inp (b226Tree (K := K)))).BoundedBy q :=
  genComputeSkeleton_skeletonBounded z α inp (by omega)
    (b226_subject_bounded hq) (b226_formula_bounded hq) b226_evalG b226_gen

theorem b226_axisRange {q : ℕ} (hq : 7 < q)
    (mf : List (NTree (GenMemoryRow K))) :
    SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder (b226Tree (K := K)))) mf) :=
  genComputeSkeleton_axisRange (by omega)
    (b226_subject_bounded hq) (b226_formula_bounded hq) b226_evalG b226_gen mf

/-! ## …and the `OP_0` conjunct is not vacuous

The contrast with `Batch168.dot_no_s0_row`. -/

/-- The committed skeleton has an `.s0` row, and its record-1 axis is the literal `2`. -/
theorem b226_op0_axis_is_two (mf : List (NTree (GenMemoryRow K))) :
    ∃ s ∈ computeSkeletonRows
        (genSemanticSkeleton (bfsAssign (airReorder (b226Tree (K := K)))) mf),
      s.state = .s0 ∧ P8Census.skeletonMemoryAxis s 1 = 2 := by
  refine ⟨(genSkelOp0 b226Subject b226Formula (.atom 0) (.atom 2) b226Result 2), ?_, rfl, ?_⟩
  · rw [computeSkeletonRows_genSemantic, computeSkeletonRows_genCompute]
    refine List.mem_map.mpr ⟨bfsAssign (airReorder (b226Tree (K := K))), ?_, ?_⟩
    · exact (mem_bfsForest _ _).mpr ⟨_, List.mem_singleton.mpr rfl, InTree.here _⟩
    · rw [bfsAssign_label, bfsLabelAt_skel _ 1 (by simp [bfsRows, b226Tree,
        bfsForest_singleton])]
      simp [bfsRows, b226Tree, b226Row, skelNode, airReorder,
        bfsForest_singleton]
      split <;> rfl
  · simp [P8Census.skeletonMemoryAxis, genSkelOp0, Nock.Framework.recordCount]

/-- So the axis bound is a genuine consequence at that row, not an unused conjunct. -/
theorem b226_op0_axis_lt {q : ℕ} (hq : 7 < q) (mf : List (NTree (GenMemoryRow K))) :
    ∃ s ∈ computeSkeletonRows
        (genSemanticSkeleton (bfsAssign (airReorder (b226Tree (K := K)))) mf),
      s.state = .s0 ∧ P8Census.skeletonMemoryAxis s 1 < q := by
  obtain ⟨s, hs, h0, hax⟩ := b226_op0_axis_is_two (K := K) mf
  exact ⟨s, hs, h0, by rw [hax]; omega⟩

end Nock.RedTeam.Batch226

#print axioms Nock.RedTeam.Batch226.b226_gen
#print axioms Nock.RedTeam.Batch226.b226_skeletonBounded
#print axioms Nock.RedTeam.Batch226.b226_axisRange
#print axioms Nock.RedTeam.Batch226.b226_op0_axis_is_two
#print axioms Nock.RedTeam.Batch226.b226_op0_axis_lt
