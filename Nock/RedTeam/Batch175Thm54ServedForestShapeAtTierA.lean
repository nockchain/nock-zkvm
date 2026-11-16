/-
  Nock/RedTeam/Batch175Thm54ServedForestShapeAtTierA.lean

  1. `bfsAssign_extract_requests_slot` now proves `Noun.slot r.axis r.root = some r.child`
     **unconditionally** — the `axis < 2` disjunct that `ER` recorded as "discharged in principle,
     not composed" is composed.  Checked here at Tier A's program, where the disjunctive form was
     the only thing available before.
  2. `rootShape_genMemForestFromTree` classifies every root of a generated memory forest as a
     one-record tree or a two-record chain of one compute node's own requests.  Checked here
     against Tier A's forest, whose ten roots are known independently
     (`GenTierAMemoryTrace.forestTrees`): the classification reproduces the shape of each.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServedForest
import Nock.NockVMROM.Thm54.TraceGen.GenMemForestOrder
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMemoryTrace
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch175

open Nock Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769

noncomputable section

/-! ## Tier A's program, as the generator emits it -/

theorem b175_dot_gen :
    genComputeSkeleton (K := K) 4 dotSubject dotFormula = .ok (dotTree, dotResult) :=
  genComputeSkeleton_dot 0

theorem b175_wf : treeRequestsWF (dotTreeAir (K := K)) := by
  rw [← airReorder_dotTree]
  exact treeRequestsWF_airReorder (genComputeSkeleton_tree_requests_wf b175_dot_gen)

/-- The serving identity on the same tree, needed for the row-level exponent `Nodup` that
`RootShape`'s chain disjunct rests on. -/
theorem b175_match : treeRequestsMatch (bfsAssign (dotTreeAir (K := K))) := by
  rw [← airReorder_dotTree]
  exact genComputeSkeleton_air_requestsMatch b175_dot_gen

/-! ## 1. `hslot`, composed

Before `ET` this returned `r.axis < 2 ∨ Noun.slot r.axis r.root = some r.child`, and the left
disjunct admits `axis = 0`, which `Noun.slot` never serves (`Reference.lean:45`). -/

/-- **Every extracted request of Tier A's assigned tree is genuinely served, with no disjunct.** -/
theorem b175_requests_served (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (dotTreeAir (K := K))) n) :
    ∀ r ∈ extractNodeReqs n.label, Noun.slot r.axis r.root = some r.child :=
  bfsAssign_extract_requests_slot (dotTreeAir (K := K)) b175_wf n hn

/-- The composed form gives axis positivity for free, at every node rather than only the root.
`genComputeSkeleton_root_requests` (`GenChainedLanguage.lean:894`) proves this for the root row
only, by design; `axis = 0` is exactly what the old disjunct could not exclude. -/
theorem b175_requests_axis_pos (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (dotTreeAir (K := K))) n) :
    ∀ r ∈ extractNodeReqs n.label, 1 ≤ r.axis := by
  intro r hr
  by_contra hlt
  have h0 : r.axis = 0 := by omega
  have hs := b175_requests_served n hn r hr
  rw [h0] at hs
  simp [Noun.slot] at hs

/-! ## 2. The forest-shape classification at Tier A -/

/-- **Every root of Tier A's assigned forest is one of the two generated shapes.** -/
theorem b175_rootShape (u : NTree (GenMemoryRow K))
    (hu : u ∈ assignedForest seedZ alphaA) :
    ∃ n, InTree (bfsAssign (dotTreeAir (K := K))) n ∧
      RootShape (encC seedZ) seedZ alphaA MemoryTable.formRDefault (extractNodeReqs n.label) u :=
  rootShape_genMemForestFromTree (encC seedZ) seedZ alphaA
    (bfsAssign (dotTreeAir (K := K)))
    (nodeExpsNodup_of_requestsMatch _ b175_match) u hu

/-- Root 1 of Tier A's forest is the one-record tree the classification's left disjunct names,
for the request `⟨dotBranchPair, dotThenFormula, 2⟩` — the same data
`GenServedRootTrace.rootTraceOfRecordTree` consumed in `Batch174`. -/
theorem b175_root1_is_record_shape :
    RootShape (encC seedZ) seedZ alphaA MemoryTable.formRDefault
      [⟨dotBranchPair, dotThenFormula, 2, 3⟩]
      (forestTrees[1]'(by simp [forestTrees])) :=
  Or.inl ⟨⟨dotBranchPair, dotThenFormula, 2, 3⟩, by simp, rfl⟩

/-- Root 0 is the two-record chain the right disjunct names, for the linked pair
`⟨dotFormula, dotParentTail, 3⟩` / `⟨dotParentTail, dotCondFormula, 2⟩`. -/
theorem b175_root0_is_chain_shape :
    RootShape (encC seedZ) seedZ alphaA MemoryTable.formRDefault
      [⟨dotFormula, dotParentTail, 3, 1⟩, ⟨dotParentTail, dotCondFormula, 2, 2⟩]
      (forestTrees[0]'(by simp [forestTrees])) :=
  Or.inr ⟨⟨dotFormula, dotParentTail, 3, 1⟩, by simp,
    ⟨dotParentTail, dotCondFormula, 2, 2⟩, by simp, rfl, by decide,
    genAnnotatedChainedTree_axis3_axis2_eq (encC seedZ) seedZ alphaA
      (.atom 6) dotCondFormula dotBranchPair 1 2⟩

/-! ## 3. A chained pair OUTSIDE axes `{2, 3}`, emitted by a real program

`ER.1` recorded that the chain half of `GenServedRootTrace` had no non-vacuity witness outside
`{2, 3}`, because Tier A's thirteen requests are all `@2`/`@3`.  The sharper question is whether the
*generator* can chain outside that window at all.  It can, and exactly once: `genRowMemForest`
(`GenMem.lean:1066`) chains consecutive requests when `r₁.child = r₂.root`, and every arm's linked
pair is formula-open `@3` into formula-tail `@2` — **except** `OP_0`, whose pair is
`⟨formula, tail, 3⟩` then `⟨subject, result, ax⟩` (`Gen.lean:578-579`).  Those link exactly when
`tail = subject`, and since `tail =.atom ax` and `Noun.slot ax (.atom ax)` must succeed, that forces
`ax = 1`.  So `*[1 [0 1]]` emits a chain at axes `(3, 1)`. -/

/-- The `OP_0` program whose formula tail is its own subject. -/
def b175Op0Formula : Noun := .cell (.atom 0) (.atom 1)

/-- Its two emitted requests: formula-open `@3`, then the identity slot read `@1`.

**The exponents are the stamped ones.**  `b175_op0_gen` below shows `genComputeSkeleton` emitting
this row with both record exponents `0` — those are the *pre-assignment* values, and `bfsAssign`
replaces them with the row's distinct slot exponents before the memory forest is built.  The
distinction matters because `RootShape`'s chain disjunct carries
`r1.recordExp ≠ r2.recordExp` (`FH`): a pair with two zeros is not a request list any assigned tree
produces, so the witness below uses `1` and `2`. -/
def b175Op0Reqs : List MemRecordReq :=
  [⟨b175Op0Formula, .atom 1, 3, 1⟩, ⟨.atom 1, .atom 1, 1, 2⟩]

theorem b175_op0_gen :
    genComputeSkeleton (K := K) 1 (.atom 1) b175Op0Formula
      = .ok (.node (skelNode
          (genSkelOp0 (.atom 1) b175Op0Formula (.atom 0) (.atom 1) (.atom 1) 1)
          [⟨b175Op0Formula, .atom 1, 3, 0⟩, ⟨.atom 1, .atom 1, 1, 0⟩]) [], .atom 1) := by
  simp only [b175Op0Formula, genComputeSkeleton, Nock.Noun.slot]

/-- The two requests link, so the row's forest is **one** chained root, not two trees. -/
theorem b175_op0_row_chains (z α : K) :
    ∃ u, genRowMemForest (encC z) z α MemoryTable.formRDefault b175Op0Reqs = [u] ∧
      genAnnotatedChainedTree (encC z) z α MemoryTable.formRDefault b175Op0Reqs = some u := by
  obtain ⟨u, hu⟩ : ∃ u, genAnnotatedChainedTree (encC z) z α MemoryTable.formRDefault b175Op0Reqs = some u :=
    ⟨_, genAnnotatedChainedTree_pair (encC z) z α _ _⟩
  refine ⟨u, ?_, hu⟩
  have hred : genRowMemForest (encC z) z α MemoryTable.formRDefault b175Op0Reqs =
      match genAnnotatedChainedTree (encC z) z α MemoryTable.formRDefault b175Op0Reqs with
      | some t => [t]
      | none =>
        [genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault b175Op0Formula (.atom 1) 3 1,
         genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault (.atom 1) (.atom 1) 1 2] := rfl
  rw [hred, hu]

/-- **A chain outside `{2, 3}`: the right disjunct of `RootShape` at axes `3` and `1`.** -/
theorem b175_rootShape_chain_axes_three_one (z α : K) :
    ∃ u, RootShape (encC z) z α MemoryTable.formRDefault b175Op0Reqs u ∧
      genAnnotatedChainedTree (encC z) z α MemoryTable.formRDefault b175Op0Reqs = some u := by
  obtain ⟨u, -, hu⟩ := b175_op0_row_chains z α
  exact ⟨u, Or.inr ⟨⟨b175Op0Formula, .atom 1, 3, 1⟩, by simp [b175Op0Reqs],
    ⟨.atom 1, .atom 1, 1, 2⟩, by simp [b175Op0Reqs], rfl, by decide, hu⟩, hu⟩

/-- The two axes really are `3` and `1`, i.e. outside the window Tier A exercises. -/
theorem b175_chain_axes : (b175Op0Reqs.map MemRecordReq.axis) = [3, 1] := rfl


end

#print axioms b175_wf
#print axioms b175_match
#print axioms b175_requests_served
#print axioms b175_requests_axis_pos
#print axioms b175_rootShape
#print axioms b175_root1_is_record_shape
#print axioms b175_root0_is_chain_shape
#print axioms b175_op0_gen
#print axioms b175_op0_row_chains
#print axioms b175_rootShape_chain_axes_three_one
#print axioms b175_chain_axes

end Nock.RedTeam.Batch175
