/-
  Nock/NockVMROM/Thm54/TraceGen/GenClaimedResult.lean

  **The committed public claim of a generated commitment is the program's own triple.**

  This module supplies it at the level where the object exists — the
  committed `P8PublicClaim`, which is what the released package's verifier carries
  (`CommitmentResidual.claim_eq`, `BuildablePackage.lean:70`;
  `buildOptimizedStrictPackageFromPins` sets `verifier := R.verifier`).

  The statement is `∀ program`:

      genComputeSkeleton fuel subject formula =.ok (t, result)
        →  (skeletonOfNodes (genComputeNodes z α a b c t) mf).publicClaim
             = ⟨subject, formula, result⟩

  and `genComputeSkeleton_evalN` (`GenMatmulBounded.lean:334`) independently gives
  `Nock.evalN fuel subject formula = some result`, so the committed claim's `result` is exactly the
  noun the reference evaluator returns on the committed `subject`/`formula`.  `publicClaim_Holds`
  packages that as `P8PublicClaim.Holds` (`JointSoundness.lean:56`), which is the paper's own
  "genuine evaluator conclusion" predicate.

  Nothing here is new mathematics.  The root of the committed node tree is the root of `t` because
  each of the three transports on the way preserves the node label's `.skel`:

  | transport | preserved by |
  |---|---|
  | `airReorder` — permutes children | `airReorder_label` (`GenAirOrder.lean:73`) |
  | `bfsAssign` — rewrites stamps | `bfsLabelAt_skel` (`BFSAssign.lean:132`) |
  | `renderRows` — fills `row`/`requests` | `renderRows_skel` (`GenTierABinds.lean:212`) |
  | `GenComputeRow.node` + `setRowCoins` | `mapNTree_node_skel` (`GenTierABinds.lean:218`) |

  and `genComputeSkeleton_root_sfe` (`GenAirOrderLinked.lean:27`) reads the triple off `t`'s root.

  **Not claimed.**  This is the committed claim, not a soundness statement: nothing here says an
  accepting transcript forces the claim: that is the capstone's own `containment` conjunct.  Nor
  does it touch `Λ`, the counted events, or any §J box.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenHonestData
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulBounded

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.SemanticStrategy

variable {K : Type} [Field K]

/-! ## The three label transports -/

/-- BFS row list of a tree starts with the root's own label. -/
theorem bfsRows_cons (t : NTree (GenComputeRow K)) :
    bfsRows t = t.label :: (bfsForest (NTree.children t)).map NTree.label := by
  rw [bfsRows, bfsForest_cons_eq [t] (List.cons_ne_nil _ _)]
  simp

/-- **`bfsAssign` preserves the root skeleton.**  It rewrites stamps and nothing else. -/
theorem bfsAssign_label_skel (t : NTree (GenComputeRow K)) :
    (bfsAssign t).label.skel = t.label.skel := by
  have hlist := bfsRows_cons t
  have hpos : (1 : ℕ) - 1 < (bfsRows t).length := by
    rw [hlist]; simp
  rw [bfsAssign_label, bfsLabelAt_skel t 1 hpos]
  simp [hlist]

/-- **`renderRows` preserves the root skeleton**, at the label rather than the whole tree. -/
theorem renderRows_label_skel (z α : K) (t : NTree (GenComputeRow K)) :
    (renderRows z α t).label.skel = t.label.skel := by
  have h := congrArg NTree.label (renderRows_skel z α t)
  simpa [mapNTree_label] using h

/-- **The committed compute tree's root skeleton is the accepted tree's root skeleton.**
`genComputeRows z α t = renderRows z α (bfsAssign (airReorder t))` (`GenBindsAt.lean:55`), and all
three stages preserve `.skel` at the root. -/
theorem genComputeRows_label_skel (z α : K) (t : NTree (GenComputeRow K)) :
    (genComputeRows z α t).label.skel = t.label.skel := by
  rw [genComputeRows, renderRows_label_skel, bfsAssign_label_skel, airReorder_label]

/-- The committed node tree's root skeleton, through `GenComputeRow.node` and the coin overwrite. -/
theorem genComputeNodes_label_skel (z α a b c : K) (t : NTree (GenComputeRow K)) :
    ComputeNode.skel (genComputeNodes z α a b c t).label = t.label.skel := by
  rw [genComputeNodes, mapNTree_label, mapNTree_label]
  exact genComputeRows_label_skel z α t

/-! ## The committed public claim -/

/-- **The committed public claim of a generated commitment is the program's triple.**

`SemanticSkeleton.publicClaim` (`SemanticStrategy.lean:737`) reads the root of the committed
compute tree; `skeletonOfNodes` (`HonestCommitment.lean:507`) is that tree.  The memory forest is
irrelevant and stays universally quantified. -/
theorem publicClaim_genComputeNodes (z α a b c : K)
    (mf : List (NTree (MemoryNode K)))
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    (skeletonOfNodes (genComputeNodes z α a b c t) mf).publicClaim =
      ⟨subject, formula, result⟩ := by
  obtain ⟨hs, hf, he⟩ := genComputeSkeleton_root_sfe h
  have hroot : ComputeNode.skel (genComputeNodes z α a b c t).label = t.label.skel :=
    genComputeNodes_label_skel z α a b c t
  show (⟨(mapNTree ComputeNode.skel (genComputeNodes z α a b c t)).label.subject,
      (mapNTree ComputeNode.skel (genComputeNodes z α a b c t)).label.formula,
      (mapNTree ComputeNode.skel (genComputeNodes z α a b c t)).label.evaluation⟩ :
    P8PublicClaim) = _
  rw [mapNTree_label, hroot, hs, hf, he]

/-- The same, in the shape `Data.skeleton` presents.  `genData`'s `computeNodes` / `memoryNodes`
fields are `genComputeNodes` / `genMemoryNodes` by definition, so a caller rewrites this at its own
`Data` term. -/
theorem publicClaim_skeletonOfNodes_result (z α a b c : K)
    (mf : List (NTree (MemoryNode K)))
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    (skeletonOfNodes (genComputeNodes z α a b c t) mf).publicClaim.result = result := by
  rw [publicClaim_genComputeNodes z α a b c mf h]

/-- **The committed claim is a genuine evaluator conclusion.**  `P8PublicClaim.Holds`
(`JointSoundness.lean:56`) is the paper's predicate; the fuel is the generator's own. -/
theorem publicClaim_Holds (z α a b c : K)
    (mf : List (NTree (MemoryNode K)))
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ((skeletonOfNodes (genComputeNodes z α a b c t) mf).publicClaim).Holds := by
  refine ⟨fuel, ?_⟩
  rw [publicClaim_genComputeNodes z α a b c mf h]
  exact genComputeSkeleton_evalN h

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.bfsAssign_label_skel
#print axioms Nock.NockVMROM.Thm54.TraceGen.renderRows_label_skel
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeRows_label_skel
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeNodes_label_skel
#print axioms Nock.NockVMROM.Thm54.TraceGen.publicClaim_genComputeNodes
#print axioms Nock.NockVMROM.Thm54.TraceGen.publicClaim_skeletonOfNodes_result
#print axioms Nock.NockVMROM.Thm54.TraceGen.publicClaim_Holds
