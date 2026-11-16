/-
  Nock/NockVMROM/Thm54/TraceGen/GenBindsAt.lean

  Nothing new is proved here.  Both live configurations already build `BindsAt` by the *same* two
  lines —

      BindsAt.ofTreeBindings rfl (computeTreeBinds_threaded z α) (memoryForestBinds_threaded z α)

  (`GenTierABinds.lean:597`, `GenMatmulBinds.lean:128`) — and the two arguments reduce to
  `computeTreeBinds_of_nodesOK` / `memoryTreeBinds_of_nodesOK`, which are already generic in the
  tree, applied to the configuration's `ComputeNodesOK` / `MemoryNodesOK`.  Those two are generic
  too:

  * `genComputeSkeleton_airReorder_computeNodes_OK` (`GenAirOrderBinding.lean:371`) — `ComputeNodesOK`
    at the rendered, BFS-assigned, AIR-ordered tree of any accepted program, with no hypothesis
    beyond acceptance.  This is `Data.computeOK`, and it was already generic.
  * `genComputeSkeleton_memForest_OK_air` (`GenGenericMemory.lean:91`) — `MemoryNodesOK` on the
    generated forest.

  So the module is glue: it names the composite once, instead of each configuration re-deriving it.
  The only genuinely new content is the `Forall₂` assembly over the memory forest.

  **Scope.**  `∀ program accepted by `genComputeSkeleton``, with the memory forest supplied and its
  `MemoryNodesOK` as a hypothesis, so a configuration that threads its forest differently can still
  use this.  Nothing here is about `∀ E`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenExactExecution

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.StrictCommitment

variable {F K : Type} [Field F] [Field K] [Algebra F K]

variable {lmb : K}

/-- The committed compute tree of a generated program: rendered, BFS-assigned, AIR-ordered.  This is
what both live configurations commit (`GenTierAConfig769.lean:81`, `GenMatmulConfig.lean:102`). -/
noncomputable def genComputeRows (z α : K) (t : NTree (GenComputeRow K)) :
    NTree (GenComputeRow K) :=
  renderRows z α (bfsAssign (airReorder t))

/-! ## The coin vector

`renderNode` commits inputs with coins `(0,0,0)` (`Gen.lean:2570` and siblings).  `ComputeTable.WF`
(`ComputeTable.lean:690`) has three fields, of which only `rlc5` reads `inp.a/b/c` — so its coin
sensitivity is confined to `.s5` rows, and `renderNode_WF_of_ne_s5` (`GenWF.lean:198`) discharges it
off `.s5` at *any* coins.  `DotConfig769` has no `.s5` row and commits the rendered coins unchanged;
`GenMatmulConfig` has twenty-five and overwrites them to `(0,0,1)`.

**Careful about what `c = 1` does and does not buy.** `renderNode_WF_c_one` (`:321`) is stated at
`(0,0,1)` *and* carries a per-row hypothesis about the two OP5 operands; `c = 1` is neither
necessary nor sufficient for `rlc5` on its own (the general discharge is the counting route
`badComputeAny_card_le`, `TableWFBounds.lean:338` — a further counted coin condition).

So the carrier is parametric in `(a b c : K)`, which is exactly the freedom the two configurations
use and no more.  The coins are RLC challenges: neither `BindComputeRow` nor the fan-out shape nor
the timestamp specialization mentions them, which is why the parameter costs nothing. -/

/-- Overwriting the coins of every node preserves `ComputeNodesOK`.

This is `GenMatmulData.mmComputeNodes_OK`'s inline argument, lifted off the fixed tree: shape and
stamp are untouched, and the binding and timestamp transport by `bindComputeRow_setRowCoins` /
`computeTimestampSpecializesAt_setRowCoins` (`GenWF.lean:88`, `:94`).  The node map is
`GenMatmulData.setNodeCoins a b c` written out, so that this module does not depend on the matmul
files. -/
theorem computeNodesOK_setRowCoins (a b c : K) {z α : K} {T : NTree (ComputeNode K)}
    (h : ComputeNodesOK z α T) :
    ComputeNodesOK z α
      (mapNTree (fun n : ComputeNode K => { n with row := setRowCoins a b c n.row }) T) := by
  intro u hu
  obtain ⟨u0, hu0, rfl⟩ := inTree_mapNTree _ T u hu
  obtain ⟨hshape, hst, hbind, htime⟩ := h u0 hu0
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [mapNTree] using hshape
  · simpa [mapNTree_label] using hst
  · simpa [mapNTree_label] using bindComputeRow_setRowCoins z a b c hbind
  · simpa [mapNTree_label] using computeTimestampSpecializesAt_setRowCoins α a b c htime

/-- The coin overwrite is invisible to the skeleton projection. -/
theorem mapNTree_coinNode_skel (a b c : K) (T : NTree (ComputeNode K)) :
    mapNTree ComputeNode.skel
        (mapNTree (fun n : ComputeNode K => { n with row := setRowCoins a b c n.row }) T) =
      mapNTree ComputeNode.skel T := by
  rw [mapNTree_comp]
  exact mapNTree_eq_of (fun _ => rfl) T

/-- ...and on the row projection it is exactly the coin map on the generated rows. -/
theorem mapNTree_coinNode_row (a b c : K) (t : NTree (GenComputeRow K)) :
    mapNTree ComputeNode.row
        (mapNTree (fun n : ComputeNode K => { n with row := setRowCoins a b c n.row })
          (mapNTree GenComputeRow.node t)) =
      mapNTree (fun g : GenComputeRow K => setRowCoins a b c g.row) t := by
  rw [mapNTree_comp, mapNTree_comp]
  exact mapNTree_eq_of (fun _ => rfl) t

/-- **The committed row's inputs are exactly `⟨α, z, a, b, c⟩`.**

This is the fact `ExactExecution.ComputeRowAccepted` pins (`row.2.1 = cfg.challenges.computeInputs`),
and it is why the coin parameter has to exist rather than being fixed: a carrier committing
`renderNode`'s own `(0,0,0)` can only ever match a challenge vector with zero coins, and `WF` needs
`c = 1` wherever the program has an `.s5` row. -/
theorem setRowCoins_renderNode_inputs (z α a b c : K) (g : GenComputeRow K) :
    (setRowCoins a b c (renderNode z α g).row).2.1 = ⟨α, z, a, b, c⟩ := by
  cases hst : g.skel.state <;>
    simp [setRowCoins, renderNode, hst, renderOp0Row, renderOp1Row, renderOp2Row,
      renderOp3Row, renderOp4Row, renderOp5Row, renderOp6Row, renderOp7Row,
      renderOp8Row, renderOp9Row, renderConsRow]

/-! ## The two tree bindings -/

/-- The skeleton's compute tree is the committed tree's skeleton projection — `renderRows` preserves
`.skel`, so rendering is invisible here. -/
theorem genSemanticSkeleton_computeTree (z α : K) (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    (genSemanticSkeleton (bfsAssign (airReorder t)) mf).computeTree =
      mapNTree ComputeNode.skel
        (mapNTree GenComputeRow.node (genComputeRows z α t)) := by
  change mapNTree GenComputeRow.skel (bfsAssign (airReorder t)) = _
  rw [mapNTree_node_skel, genComputeRows, renderRows_skel]

/-- `ComputeTreeBinds` for any accepted program, from the generic `ComputeNodesOK`. -/
theorem genComputeTreeBinds (z α : K) (a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (mf : List (NTree (GenMemoryRow K))) :
    ComputeTreeBinds z
      (genSemanticSkeleton (bfsAssign (airReorder t)) mf).computeTree
      (mapNTree (fun g : GenComputeRow K => setRowCoins a b c g.row) (genComputeRows z α t)) := by
  rw [genSemanticSkeleton_computeTree z α t mf, ← mapNTree_coinNode_skel a b c,
    ← mapNTree_coinNode_row a b c]
  exact computeTreeBinds_of_nodesOK z α _
    (computeNodesOK_setRowCoins a b c
      (genComputeSkeleton_airReorder_computeNodes_OK (p := (t, result)) z α h))

/-! ### Row-level executed rows -/

private theorem genBinds_wf_tree_list {A : Type*} (lbl : A) (cs : List (NTree A)) :
    2 * totalSize cs + 1 < 2 * totalSize [NTree.node lbl cs] := by
  have h : totalSize [NTree.node lbl cs] = 1 + totalSize cs := by
    rw [totalSize_cons, totalSize_nil]
    simp [NTree.size, totalSize]
  omega

private theorem genBinds_wf_list_head {A : Type*} (c : NTree A) (rest : List (NTree A)) :
    2 * totalSize [c] < 2 * totalSize (c :: rest) + 1 := by
  rw [totalSize_cons, totalSize_cons, totalSize_nil]
  omega

private theorem genBinds_wf_list_tail {A : Type*} (c : NTree A) (rest : List (NTree A)) :
    2 * totalSize rest + 1 < 2 * totalSize (c :: rest) + 1 := by
  rw [totalSize_cons]
  have hc : 0 < c.size := by cases c; simp [NTree.size]
  omega

mutual
theorem memoryTreeBinds_encode_of_nodesOK (z α : K) :
    ∀ (T : NTree (MemoryNode K)), MemoryNodesOK z α T →
      MemoryTreeBinds z (mapNTree MemoryNode.skel T)
        (mapNTree (MemoryRowTemplate.encodeRow lmb) (mapNTree MemoryNode.row T))
  | .node lbl cs, h => by
      obtain ⟨hshape, _, hbind, _⟩ := h _ (InTree.here _)
      simp only [NTree.label_node, NTree.children_node] at hshape
      rw [mapNTree, mapNTree, mapNTree, List.map_map]
      refine MemoryTreeBinds.node ?_ (bindMemoryRow_encodeRow hbind) ?_
      · simpa using hshape
      · have := memoryTreeBindsList_encode_of_nodesOK z α cs
          (fun c hc => h.child (by simpa using hc))
        simpa [List.map_map, Function.comp_def] using this
termination_by T _ => 2 * totalSize [T]
decreasing_by exact genBinds_wf_tree_list _ _

theorem memoryTreeBindsList_encode_of_nodesOK (z α : K) :
    ∀ (cs : List (NTree (MemoryNode K))),
      (∀ c ∈ cs, MemoryNodesOK z α c) →
      List.Forall₂ (MemoryTreeBinds z)
        (cs.map (mapNTree MemoryNode.skel))
        (cs.map (fun c => mapNTree (MemoryRowTemplate.encodeRow lmb) (mapNTree MemoryNode.row c)))
  | [], _ => .nil
  | c :: rest, h =>
      .cons (memoryTreeBinds_encode_of_nodesOK z α c (h c (by simp)))
        (memoryTreeBindsList_encode_of_nodesOK z α rest
          (fun x hx => h x (by simp [hx])))
termination_by cs _ => 2 * totalSize cs + 1
decreasing_by
  all_goals first
    | exact genBinds_wf_list_head _ _
    | exact genBinds_wf_list_tail _ _
end

/-- `MemoryTreeBinds` pointwise along the **executed** forest (the row encode of the generated
forest), assembled as `Forall₂`. -/
theorem genMemoryForestBinds (z α : K) (mf : List (NTree (GenMemoryRow K)))
    (hmf : ∀ u ∈ mf, MemoryNodesOK z α (mapNTree GenMemoryRow.node u)) :
    List.Forall₂ (MemoryTreeBinds z)
      (mf.map (mapNTree GenMemoryRow.skel))
      ((mf.map (mapNTree GenMemoryRow.row)).map (mapNTree (MemoryRowTemplate.encodeRow lmb))) := by
  induction mf with
  | nil => exact List.Forall₂.nil
  | cons u rest ih =>
    refine List.Forall₂.cons ?_ (ih (fun v hv => hmf v (List.mem_cons_of_mem _ hv)))
    have hb := memoryTreeBinds_encode_of_nodesOK (lmb := lmb) z α _ (hmf u List.mem_cons_self)
    rwa [mapNTree_memNode_skel, mapNTree_memNode_row] at hb

/-! ## `BindsAt` -/

/-- **`BindsAt` for any program the generator accepts.**

`ofTreeBindings` derives the two flat `Forall₂` row bindings from the recursive tree bindings, so
the two arguments below are the whole content — and both are now generic. -/
theorem genBindsAt (z α : K) (chal : ChallengeVector K) (hz : chal.z = z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h) (a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (mf : List (NTree (GenMemoryRow K)))
    (hmf : ∀ u ∈ mf, MemoryNodesOK z α (mapNTree GenMemoryRow.node u))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    BindsAt z (genSemanticSkeleton (bfsAssign (airReorder t)) mf)
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
        hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem) :=
  BindsAt.ofTreeBindings (F := F) (K := K) hz
    (genComputeTreeBinds z α a b c h mf)
    (genMemoryForestBinds z α mf hmf)

/-! ## One half of `language`, generically

`NounRealizedTraversableChainedSemanticExactLanguage` (`NounRealization.lean:503`) is
`traversable` ∧ `nounRealization`.

**Premise corrected.**  So the hypothesis is now `S.BoundedBy q` itself — strictly weaker,
and the form a configuration actually holds.  `genCommitment_skeletonBounded` remains available for
anyone who does have the commitment check.

The `traversable` half is **not** here: it needs `ChainedSemanticExactLanguage`, a **ten**-field
object (`semantic`, `z_ne_zero`, `compute_wf`, `memory_wf`, `compute_chain`, `memory_chain`, three
`memory_first_*`, and `memory_last_icur`) that both live configurations still prove
per-configuration. -/

/-- **`ExactExecutionNounRealization` for any accepted program**, from one decidable commitment check
and the generic binding. -/
theorem genNounRealization {q : ℕ} (z α : K) (hz : z ≠ 0)
    (chal : ChallengeVector K) (hzc : chal.z = z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h) (a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (mf : List (NTree (GenMemoryRow K)))
    (hmf : ∀ u ∈ mf, MemoryNodesOK z α (mapNTree GenMemoryRow.node u))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t)) mf).BoundedBy q) :
    ExactExecutionNounRealization q
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
        hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem) :=
  nounRealization_of_binds (F := F) hz hb
    (genBindsAt (F := F) z α chal hzc Ksz orbit horb a b c h mf hmf hmempos hcomp hmem)

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeTreeBinds
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemoryForestBinds
#print axioms Nock.NockVMROM.Thm54.TraceGen.genBindsAt
#print axioms Nock.NockVMROM.Thm54.TraceGen.genNounRealization
#print axioms Nock.NockVMROM.Thm54.TraceGen.computeNodesOK_setRowCoins
#print axioms Nock.NockVMROM.Thm54.TraceGen.setRowCoins_renderNode_inputs
