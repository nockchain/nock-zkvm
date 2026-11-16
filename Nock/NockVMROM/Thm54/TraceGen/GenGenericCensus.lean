/-
  Nock/NockVMROM/Thm54/TraceGen/GenGenericCensus.lean

  **`slotSemantics` and `recordEquations` at `Data`'s field shape, for an arbitrary program.**

  `HonestCommitment.Data` takes two census premises as fields:

      slotSemantics   : ∀ s ∈ computeSkeletonRows (skeletonOfNodes computeNodes memoryNodes),
                          SkeletonSlotSemantics s
      recordEquations : ∀ s ∈ computeSkeletonRows (skeletonOfNodes computeNodes memoryNodes),
                          SkeletonRecordEquations s

  This module discharges both **for every program the generator accepts**, with no hypothesis
  beyond `genComputeSkeleton fuel subject formula =.ok (t, result)`.  Nothing here is new
  mathematics: the census induction was already program-generic, and the only missing steps were
  the two transports below.

  * `genComputeSkeleton_inTree_census` (`GenMatmulSemanticData.lean:69`) already proves
    `nodeCensus u.label` at every `InTree` node of any accepted program, by induction on fuel with
    a twelve-way opcode split, and takes no configuration-specific hypothesis.
  * `bfsAssign_computeSkeletonRows_slotSemantics` / `_recordEquations` (`GenCensus.lean:241,260`)
    already lift `∀ g ∈ bfsRows t` to `computeSkeletonRows (genSemanticSkeleton (bfsAssign t) mf)`
    for an arbitrary tree.

  Missing, and supplied here:

  1. `genComputeSkeleton_bfsRows_census` -- `InTree` scope to `bfsRows` scope, generically.  The
     proof existed only inlined at a fixed tree (`mmTreeAir_bfsRows_census`).
  2. `computeSkeletonRows_skeletonOfNodes_renderRows` -- the **skeleton bridge**:
     `skeletonOfNodes` of the *rendered, node-mapped* tree has the same compute skeleton rows as
     `genSemanticSkeleton` of the tree itself.  `skeletonOfNodes_eq` existed only as per-fixture
     `simp` lemmas (`HonestCommitment.lean:1236` at F73, `ConsData.lean:557` at cons), never for an
     arbitrary generated tree.  It follows from `mapNTree_node_skel` and `renderRows_skel`, both of
     which were already generic; `computeSkeletonRows` reads only `.computeTree`, so the memory
     forest is irrelevant and stays universally quantified.

  Scope, stated exactly: this is `∀ program accepted by genComputeSkeleton`, not `∀ E`.  It says
  nothing about executions that are not generated, and it discharges only these two premises --
  `census`, `sizeWindowBound` and `skeletonBounded` are untouched, no `§J` box moves, and no
  carrier field is added.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulSemanticData
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderChildLink

-- A missing import otherwise becomes a silent type variable rather than an error;
-- that cost real debugging time on this module family.
set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.HonestCommitment

variable {K : Type} [Field K]

/-! ## Label transport

`airReorder` only permutes children — it keeps every label (`inTree_airReorder_label`,
`GenAirOrderChildLink.lean:40`).  So a property reading only `.label` needs **one** proof, and the
two orderings are instances.  `nodeCensus` is such a property (`nodeCensus : GenComputeRow K → Prop`,
a function of the row alone), so the `_air` census below is a *corollary* of the transport rather
than a second induction. -/

/-- `t'`'s labels all come from `t`.  Satisfied reflexively, and by `airReorder`. -/
def LabelsFrom (t' t : NTree (GenComputeRow K)) : Prop :=
  ∀ u, InTree t' u → ∃ u0, InTree t u0 ∧ u.label = u0.label

theorem labelsFrom_self (t : NTree (GenComputeRow K)) : LabelsFrom t t :=
  fun u hu => ⟨u, hu, rfl⟩

theorem labelsFrom_airReorder (t : NTree (GenComputeRow K)) :
    LabelsFrom (airReorder t) t :=
  inTree_airReorder_label t

/-- **`nodeCensus` at every node of any tree whose labels come from an accepted program's tree.**

The single statement the plain and AIR-ordered censuses are both instances of. -/
theorem census_of_labelsFrom
    {fuel : ℕ} {subject formula : Noun}
    {t t' : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hlab : LabelsFrom t' t) :
    ∀ u, InTree t' u → nodeCensus u.label := by
  intro u hu
  obtain ⟨u0, hu0, heq⟩ := hlab u hu
  rw [heq]
  exact genComputeSkeleton_inTree_census h u0 hu0

/-! ## `InTree` scope to `bfsRows` scope -/

/-- Every BFS row of an accepted program's tree satisfies `nodeCensus`.

`bfsRows` is `(bfsForest [t]).map NTree.label`, and every member of `bfsForest [t]` is `InTree t`,
so this is the census induction read along the BFS order.  Generic in the program; the same proof
existed only at the fixed `mmTreeAir` (`GenMatmulSemanticData.lean:1621`). -/
theorem genComputeSkeleton_bfsRows_census
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ g ∈ bfsRows t, nodeCensus g := by
  intro g hg
  unfold bfsRows at hg
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hg
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ n).mp hn
  simp only [List.mem_singleton] at hu
  subst u
  exact genComputeSkeleton_inTree_census h n hin

/-! ## `NoHead8` is vacuous

`genComputeSkeleton_inTree_cmpKind` (`GenMatmulSemanticData.lean:1230`) carries two hypotheses
`NoHead8 subject` and `NoHead8 formula`, which read like a restriction to programs without OP8 --
the name says so.  They are not: `NoHead8` is provable for **every** noun, so the hypotheses are
dead weight and the census-comparison induction is unconditionally generic.

Measured, not assumed: the OP8 arm of `NoHead8` is `.cell (.atom _op) tl => NoHead8 tl`, which
**discards** the opcode, so no branch of the recursion can produce `False`. -/

/-- `NoHead8` holds of every noun -- including every OP8 formula.  It therefore excludes nothing,
and the two `NoHead8` hypotheses of `genComputeSkeleton_inTree_cmpKind` are vacuous. -/
theorem noHead8_all : ∀ n : Noun, NoHead8 n
  | .atom _ => trivial
  | .cell (.atom _) tl => noHead8_all tl
  | .cell (.cell a b) c => ⟨noHead8_all (.cell a b), noHead8_all c⟩

/-- The comparison census at every node of any accepted program, with **no** side hypothesis --
`genComputeSkeleton_inTree_cmpKind` with its two vacuous `NoHead8` arguments discharged. -/
theorem genComputeSkeleton_inTree_cmpKind_unconditional
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u, InTree t u → NodeCmpKind (K := K) u.label :=
  (genComputeSkeleton_inTree_cmpKind (noHead8_all subject) (noHead8_all formula) h).2

/-! ## The skeleton bridge -/

/-- **`skeletonOfNodes` of a rendered generated tree has `genSemanticSkeleton`'s compute rows.**

`computeSkeletonRows` reads only `.computeTree`, so the two memory forests are unrelated and both
stay universally quantified.  On the compute side, `mapNTree_node_skel` strips `GenComputeRow.node`
and `renderRows_skel` strips the rendering, since `renderNode` preserves `.skel`.

This is the generic form of the per-fixture `skeletonOfNodes_eq` `simp` lemmas. -/
theorem computeSkeletonRows_skeletonOfNodes_renderRows (z α : K)
    (t : NTree (GenComputeRow K))
    (mf : List (NTree (MemoryNode K)))
    (mf' : List (NTree (GenMemoryRow K))) :
    computeSkeletonRows
        (skeletonOfNodes (mapNTree GenComputeRow.node (renderRows z α t)) mf) =
      computeSkeletonRows (genSemanticSkeleton t mf') := by
  simp only [computeSkeletonRows, skeletonOfNodes, genSemanticSkeleton,
    mapNTree_node_skel, renderRows_skel]

/-! ## The two `Data` census premises, generically -/

/-- **`Data.slotSemantics` for every program the generator accepts.**

The NMR slot CORE on every committed compute skeleton row of the
generated, BFS-assigned, rendered tree -- at exactly the shape `Data.slotSemantics` takes, with the
memory forest arbitrary.  Previously discharged only at `Op9Execution` / `K3`. -/
theorem genComputeSkeleton_slotSemantics (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (mf : List (NTree (MemoryNode K))) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes
          (mapNTree GenComputeRow.node (renderRows z α (bfsAssign t))) mf),
      SkeletonSlotSemantics s := by
  rw [computeSkeletonRows_skeletonOfNodes_renderRows z α (bfsAssign t) mf []]
  exact bfsAssign_computeSkeletonRows_slotSemantics t []
    (fun g hg => (genComputeSkeleton_bfsRows_census h g hg).1)

/-- **`Data.recordEquations` for every program the generator accepts.**

The `Algorithm NockCompute` memory-record equations on every
committed compute skeleton row, at `Data.recordEquations`' shape. -/
theorem genComputeSkeleton_recordEquations (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (mf : List (NTree (MemoryNode K))) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes
          (mapNTree GenComputeRow.node (renderRows z α (bfsAssign t))) mf),
      SkeletonRecordEquations s := by
  rw [computeSkeletonRows_skeletonOfNodes_renderRows z α (bfsAssign t) mf []]
  exact bfsAssign_computeSkeletonRows_recordEquations t []
    (fun g hg => (genComputeSkeleton_bfsRows_census h g hg).2.1)

/-! ## The AIR-ordered tree — the order live configurations actually commit

The results above are stated at `bfsAssign t` for `t` the raw generator output.  **Every live
configuration commits the AIR-reordered tree instead**: `DotConfig769.computeNodes` is
`dotComputeNodesAir = mapNTree GenComputeRow.node (renderRows z α (bfsAssign (dotTreeAir)))`
(`GenTierAAirMem.lean:233`), and `dotTreeAir = airReorder dotTree ≠ dotTree`.  Since
`genComputeSkeleton … =.ok (airReorder t, _)` is not a theorem, the results above do **not** reach
a committed tree on their own; these variants do.

`airReorder` permutes nodes without changing labels (`inTree_airReorder_label`,
`GenAirOrderChildLink.lean:40`) and `nodeCensus` reads only the label, so the transport is immediate. -/

/-- `nodeCensus` at every BFS row of the AIR-reordered tree — a **corollary of the transport**,
not a second induction. -/
theorem genComputeSkeleton_bfsRows_census_air
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ g ∈ bfsRows (airReorder t), nodeCensus g := by
  intro g hg
  unfold bfsRows at hg
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hg
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ n).mp hn
  simp only [List.mem_singleton] at hu
  subst u
  exact census_of_labelsFrom h (labelsFrom_airReorder t) n hin

/-- **`Data.slotSemantics` on the AIR-ordered tree** — the shape a live configuration commits. -/
theorem genComputeSkeleton_slotSemantics_air (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (mf : List (NTree (MemoryNode K))) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes
          (mapNTree GenComputeRow.node (renderRows z α (bfsAssign (airReorder t)))) mf),
      SkeletonSlotSemantics s := by
  rw [computeSkeletonRows_skeletonOfNodes_renderRows z α (bfsAssign (airReorder t)) mf []]
  exact bfsAssign_computeSkeletonRows_slotSemantics (airReorder t) []
    (fun g hg => (genComputeSkeleton_bfsRows_census_air h g hg).1)

/-- **`Data.recordEquations` on the AIR-ordered tree.** -/
theorem genComputeSkeleton_recordEquations_air (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (mf : List (NTree (MemoryNode K))) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes
          (mapNTree GenComputeRow.node (renderRows z α (bfsAssign (airReorder t)))) mf),
      SkeletonRecordEquations s := by
  rw [computeSkeletonRows_skeletonOfNodes_renderRows z α (bfsAssign (airReorder t)) mf []]
  exact bfsAssign_computeSkeletonRows_recordEquations (airReorder t) []
    (fun g hg => (genComputeSkeleton_bfsRows_census_air h g hg).2.1)

/-! ## Non-vacuity

The premises are inhabited at a real program rather than only in principle: the Tier A dot-product
run is an accepted `genComputeSkeleton` call, so both results apply to it by instantiation. -/

/-- Both census premises hold for the Tier A dot-product program, by instantiating the generic
results at `genComputeSkeleton_dot` -- a witness that the hypotheses are satisfiable. -/
theorem genGenericCensus_nonvacuous (z α : K) (mf : List (NTree (MemoryNode K))) :
    (∀ s ∈ computeSkeletonRows
        (skeletonOfNodes
          (mapNTree GenComputeRow.node
            (renderRows z α (bfsAssign (dotTree (K := K))))) mf),
      SkeletonSlotSemantics s) ∧
    (∀ s ∈ computeSkeletonRows
        (skeletonOfNodes
          (mapNTree GenComputeRow.node
            (renderRows z α (bfsAssign (dotTree (K := K))))) mf),
      SkeletonRecordEquations s) :=
  ⟨genComputeSkeleton_slotSemantics z α (genComputeSkeleton_dot 0) mf,
    genComputeSkeleton_recordEquations z α (genComputeSkeleton_dot 0) mf⟩

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.noHead8_all
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_inTree_cmpKind_unconditional
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_bfsRows_census
#print axioms Nock.NockVMROM.Thm54.TraceGen.computeSkeletonRows_skeletonOfNodes_renderRows
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_slotSemantics
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_recordEquations
#print axioms Nock.NockVMROM.Thm54.TraceGen.genGenericCensus_nonvacuous
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_slotSemantics_air
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_recordEquations_air
