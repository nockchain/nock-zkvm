/-
  Nock/RedTeam/Batch168Thm54AxisRangeWitness.lean

  **`SkeletonAxisRange` is a declared precondition, and here is its witness.**

  This module supplies the witness, so the
  premise does not sit in the tree unbacked.

  It is *not* an irreducible assumption.  The generator sets the OP0 axis from the formula tail:
  `Gen.lean:573-580` matches `tail` as `.atom ax` and emits
  `genSkelOp0 subject formula (.atom 0) tail result ax` with
  `memoryRecord 1 = ⟨subject, result, ax⟩` (`:154-155`).  So on a generated `.s0` row the axis
  **is** an atom of the committed formula, and `CanonicalCommitmentCheck` already bounds that atom.
  OP9 is the same shape via `Gen.lean`'s `| 9` arm.

  What is missing is the structural bridge — `skeletonDec s.f_t =.atom (skeletonMemoryAxis s 1)`
  at every generated `.s0` row — which needs a twelve-way induction over `genComputeSkeleton` of the
  kind `genComputeSkeleton_inTree_consHead` (`GenConsHead.lean`) and
  `genComputeSkeleton_inTree_fanout` (`GenSkeletonFanout.lean:31`) already are.  That is ~300 lines
  of known-shape work, not new mathematics.  Until it exists the premise is declared; when it exists
  the premise is discharged and this module becomes redundant.

  **Note on what the witness shows.**  Tier A's row states are `{s6, s2, s1×5, s9}` — there is **no
  `.s0` row**, so the OP0 clause holds vacuously here and only the OP9 clause bites.  That is stated
  rather than hidden: this witness exercises half the predicate.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticDataParts
import Nock.NockVMROM.Thm54.TraceGen.GenTierAHonestData
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge

set_option autoImplicit false

namespace Nock.RedTeam.Batch168

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.NockVMROM.Thm54.SemanticStrategy

/-- **The witness.**  `SkeletonAxisRange` holds at Tier A's committed skeleton, at its own `q = 769`.

Seven of the eight rows are neither `.s0` nor `.s9`, so both implications are vacuous there; the
`.s9` row carries axis `2`. -/
theorem dot_skeletonAxisRange :
    SkeletonAxisRange 769 (semanticSkeleton seedZ alphaA) := by
  intro s hs
  rw [semanticSkeleton_computeRows] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h | h | h | h | h <;> subst h <;>
    refine ⟨?_, ?_⟩ <;> intro hst <;>
      simp [dotTreeAir, dotOp2Tree, dotCondTree, dotOp1BTree, dotOp1CTree, dotOp9Tree,
        dotOp9CoreTree, dotOp9InvokeTree, skelNode, genSkelOp6, genSkelOp2, genSkelOp1,
        genSkelOp9, dotOp6Skel, dotOp2Skel, dotOp9Skel, P8Census.skeletonMemoryAxis,
        Nock.Framework.recordCount] at hst ⊢

/-- The OP0 half is vacuous at Tier A: no generated row of this program has state `.s0`. -/
theorem dot_no_s0_row :
    ∀ s ∈ computeSkeletonRows (semanticSkeleton seedZ alphaA), s.state ≠ ComputeTable.State.s0 := by
  intro s hs
  rw [semanticSkeleton_computeRows] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h | h | h | h | h <;> subst h <;>
    simp [dotTreeAir, dotOp2Tree, dotCondTree, dotOp1BTree, dotOp1CTree, dotOp9Tree,
      dotOp9CoreTree, dotOp9InvokeTree, skelNode, genSkelOp6, genSkelOp2, genSkelOp1,
      genSkelOp9, dotOp6Skel, dotOp2Skel, dotOp9Skel]

end Nock.RedTeam.Batch168

#print axioms Nock.RedTeam.Batch168.dot_skeletonAxisRange
#print axioms Nock.RedTeam.Batch168.dot_no_s0_row
