/-
  Nock/NockVMROM/Thm54/TraceGen/GenGenericBounded.lean

  **`skeletonBounded` for every program the generator accepts — from bounds on the program, not
  on the skeleton.**

  `hb : (genSemanticSkeleton (bfsAssign (airReorder t)) mf).BoundedBy q` is carried as a bare
  hypothesis in five places (`GenBindsAt.lean:233`, `GenSemanticDataParts.lean:115`,
  `GenSemanticData.lean:135`, and downstream), and the survey behind `GenHonestData.lean` found no
  supplier for it: the only conclusion of that shape is `genCommitment_skeletonBounded`
  (`GenCommitmentBridge.lean:120`), which wants `CanonicalCommitmentCheck` — a check **nothing in
  the tree discharges** at a generated trace, and a *harder* measurement than the
  residual it replaced.

  This module supplies it, and the reason it is cheap was already visible in the matmul files: the
  twelve-way induction `genComputeSkeleton_inTree_bounded` (`GenMatmulBounded.lean:1465`) is
  **program-generic** — quantified over `q`, `fuel`, `subject`, `formula`, `t`, `result`, with no
  fixture and no configuration — and so is every transport step
  (`inTree_airReorder_label`, `bfsAssign_inTree_computeNodeBounded`, `boundedBy_rowMemForest`,
  `boundedBy_memForestFromTree`, `genSemanticSkeleton_threadGenForest`).  Only the *assembly* was
  written per configuration: `MatmulConfig65537.semanticSkeleton_bounded`
  (`GenMatmulBounded.lean:2460`) and `DotConfig769.semanticSkeleton_bounded`
  (`GenTierABounded.lean:908`), the latter by an eight-way case split over a literal row list.
  What is below is that assembly with the configuration removed.

  **What changes, and why it is an improvement rather than a rename.**  The three premises here are
  conditions on the *program*:

  * `hs`/`hf` — every atom of the subject and the formula is `< q`;
  * `hG : FieldEmbedding.evalGBy q fuel subject formula = some result` — the run does not overflow
    `q`, `evalGBy` being `evalN` with `OP_4` crashing on overflow (`FieldEmbedding.lean:179-180`).

  ~~**Not claimed.**  A route exists — the axis of a generated `.s0`/`.s9` row *is* an atom of the committed formula
  (`Gen.lean:570-581`, `:695-703`), and `hf` already bounds it inside this very induction — but it
  needs a third conjunct on `computeNodeBounded` and a re-run, which is not done here.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenHonestData
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulBounded

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## The node bound, transported to the tree a configuration commits

`genComputeSkeleton_inTree_bounded` concludes at the raw generator output `t`.  Live carriers commit
`bfsAssign (airReorder t)`.  Both steps preserve labels, and `computeNodeBounded` reads only the
label. -/

/-- `computeNodeBounded` at every node of the AIR-reordered tree. -/
theorem genComputeSkeleton_airReorder_inTree_bounded {q fuel : ℕ} (hq : 1 < q)
    {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u, InTree (airReorder t) u → computeNodeBounded q u := by
  intro u hu
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label t u hu
  have hb := genComputeSkeleton_inTree_bounded hq hs hf hG h u0 hu0
  simp only [computeNodeBounded] at hb ⊢
  rw [hl]
  exact hb

/-- `computeNodeBounded` at every node of the BFS-assigned, AIR-reordered tree. -/
theorem genComputeSkeleton_assigned_inTree_bounded {q fuel : ℕ} (hq : 1 < q)
    {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ n, InTree (bfsAssign (airReorder t)) n → computeNodeBounded q n :=
  fun n hn =>
    bfsAssign_inTree_computeNodeBounded
      (genComputeSkeleton_airReorder_inTree_bounded hq hs hf hG h) n hn

/-! ## The memory forest

The `requests` half of `computeNodeBounded` is exactly what the memory rows are built from, which is
why one induction covers both tables. -/

/-- Every memory row emitted for one committed compute node is bounded.  The generic form of
`mmAssigned_rowBounded` (`GenMatmulBounded.lean:2394`). -/
theorem genComputeSkeleton_assigned_rowBounded (z α : K) {q fuel : ℕ} (hq : 1 < q)
    {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (n : NTree (GenComputeRow K)) (hn : InTree (bfsAssign (airReorder t)) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      ∀ v, InTree u v → v.label.skel.BoundedBy q := by
  have hbn := genComputeSkeleton_assigned_inTree_bounded hq hs hf hG h n hn
  intro u hu v hv
  refine boundedBy_rowMemForest (encC z) z α (by omega) (extractNodeReqs n.label)
    ?_ u hu v hv
  intro r hr
  unfold extractNodeReqs at hr
  obtain ⟨req, hreq, hroot, hchild, _⟩ := extractNodeReqsAux_mem _ _ _ r hr
  have hreqb := hbn.2 req hreq
  exact ⟨by rw [hroot]; exact hreqb.1, by rw [hchild]; exact hreqb.2⟩

/-- Every node of the generated memory forest is bounded. -/
theorem genComputeSkeleton_memForest_inTree_bounded (z α : K) {q fuel : ℕ} (hq : 1 < q)
    {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t)),
      ∀ v, InTree u v → v.label.skel.BoundedBy q :=
  fun u hu v hv =>
    boundedBy_memForestFromTree z α (by omega) _
      (genComputeSkeleton_assigned_rowBounded z α hq hs hf hG h) u hu v hv

/-! ## `skeletonBounded`, generically

`SemanticSkeleton.BoundedBy` has three fields (`SemanticStrategy.lean:390`): the compute BFS rows,
the memory BFS rows, and — redundantly — every `InTree` node of every forest tree.  The threading
`genMemoryForest` applies is invisible to all three (`genSemanticSkeleton_threadGenForest`). -/

/-- **`Data.skeletonBounded` for every program the generator accepts**, from bounds on the program.

This is the premise `genSemanticData` (`GenSemanticData.lean:135`), `genBindsAt`
(`GenBindsAt.lean:233`), `genCombinedBounded` and `genData` all took as `hb`.  It is now
derived rather than assumed, at three side conditions on the *input* rather than on the compiled
skeleton. -/
theorem genComputeSkeleton_skeletonBounded (z α : K) (inp : MemoryTable.Inputs K)
    {q fuel : ℕ} (hq : 1 < q)
    {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α lmb inp t)).BoundedBy q := by
  rw [genMemoryForest, genSemanticSkeleton_threadGenForest]
  have hmemRows :
      (memorySkeletonRows (genSemanticSkeleton (bfsAssign (airReorder t))
          (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t))))).Forall
        (MemoryRowSkeleton.BoundedBy q) := by
    rw [memorySkeletonRows_genSemantic]
    refine List.forall_iff_forall_mem.mpr ?_
    intro x hx
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
    obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ n).mp hn
    exact genComputeSkeleton_memForest_inTree_bounded z α hq hs hf hG h u hu n hin
  refine ⟨?_, hmemRows, ?_⟩
  · rw [computeSkeletonRows_genSemantic, computeSkeletonRows_genCompute]
    refine List.forall_iff_forall_mem.mpr ?_
    intro x hx
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
    obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ n).mp hn
    simp only [List.mem_singleton] at hu
    subst hu
    exact (genComputeSkeleton_assigned_inTree_bounded hq hs hf hG h n hin).1
  · intro tree htree node hnode
    refine List.forall_iff_forall_mem.mp hmemRows _ ?_
    show node.label ∈ (bfsForest _).map NTree.label
    exact List.mem_map.mpr ⟨node, (mem_bfsForest _ node).mpr ⟨tree, htree, hnode⟩, rfl⟩

/-! ## `Data.skeletonBounded` at the commitment's own shape

The same fact at the spelling `HonestCommitment.Data.skeletonBounded` takes, so a caller does not
have to re-apply `genSkeletonOfNodes_eq`. -/

/-- **`Data.skeletonBounded` at the committed skeleton**, derived. -/
theorem genData_skeletonBounded_of_program (z α a b c : K) (inp : MemoryTable.Inputs K)
    {q fuel : ℕ} (hq : 1 < q)
    {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    (skeletonOfNodes (genComputeNodes z α a b c t) (genMemoryNodes z α lmb inp t)).BoundedBy q :=
  genData_skeletonBounded z α a b c inp t
    (genComputeSkeleton_skeletonBounded z α inp hq hs hf hG h)

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_airReorder_inTree_bounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_assigned_inTree_bounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_assigned_rowBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_memForest_inTree_bounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_skeletonBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.genData_skeletonBounded_of_program
