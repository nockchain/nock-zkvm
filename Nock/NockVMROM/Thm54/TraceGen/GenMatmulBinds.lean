/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulBinds.lean

  Canonical tree binding of the generated F65537 matmul carrier:
  `ComputeNodesOK` / `MemoryNodesOK` lift to `ComputeTreeBinds` /
  `MemoryTreeBinds`, the memory side is transported through LogUp
  `threadGenForest`, and `execThreaded` inhabits `BindsAt` against
  `genSemanticSkeleton (bfsAssign mmTree) assignedForest`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMemAccept
import Nock.NockVMROM.Thm54.TraceGen.GenTierABinds
import Nock.NockVMROM.Thm54.RawSemanticAssembly
import Nock.NockVMROM.Thm54.NounRealization

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun Nock.NockVM
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.RawSemanticAssembly

variable {K : Type} [Field K]

variable {lmb : K}

theorem mmAssigned_bfs_bindMemoryRow (z α : K) :
    ∀ t ∈ bfsForest
        (genMemForestFromTree (encC z) z α lmb (bfsAssign (mmTreeAir (K := K)))),
      BindMemoryRowA z t.label.skel t.label.row := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  exact inTree_bindMemoryRow z α (mmMemForest_OK z α u hu) hin

theorem mmAssigned_threaded_memoryTreeBinds (z α : K) :
    List.Forall₂ (MemoryTreeBinds z)
      ((genMemForestFromTree (encC z) z α lmb
          (bfsAssign (mmTreeAir (K := K)))).map (mapNTree GenMemoryRow.skel))
      ((threadGenForest (memInputs z) 0
          (genMemForestFromTree (encC z) z α lmb
            (bfsAssign (mmTreeAir (K := K))))).map
        (mapNTree (fun g : GenMemoryRow K => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb
            g.row))) := by
  refine memoryTreeBinds_forest_of_shapeMatch
    (threadGenForest_memoryShapeMatch z α (memInputs z) 0 _
      (mmMemForest_OK z α)) ?_
  have hskel :
      (bfsForest
          ((genMemForestFromTree (encC z) z α lmb
              (bfsAssign (mmTreeAir (K := K)))).map
            (mapNTree GenMemoryRow.skel))).map NTree.label =
        (bfsForest
            (genMemForestFromTree (encC z) z α lmb
              (bfsAssign (mmTreeAir (K := K))))).map
          (fun t => t.label.skel) := by
    rw [bfsForest_mapNTree, List.map_map]
    refine List.map_congr_left ?_
    intro t _
    exact mapNTree_label _ t
  have hrow :
      (bfsForest
          ((threadGenForest (memInputs z) 0
              (genMemForestFromTree (encC z) z α lmb
                (bfsAssign (mmTreeAir (K := K))))).map
            (mapNTree (fun g : GenMemoryRow K =>
                SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb g.row)))).map NTree.label =
        (bfsForest
            (threadGenForest (memInputs z) 0
              (genMemForestFromTree (encC z) z α lmb
                (bfsAssign (mmTreeAir (K := K)))))).map
          (fun t => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb t.label.row) := by
    rw [bfsForest_mapNTree, List.map_map]
    refine List.map_congr_left ?_
    intro t _
    simp [mapNTree_label]
  rw [hskel, hrow]
  exact forall₂_bind_encode z <| threadGenForest_bfs_bindMemoryRow z (memInputs z) 0 _
    (mmAssigned_bfs_bindMemoryRow z α)

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

open Nock Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

noncomputable section

def semanticSkeleton (z α : K) : SemanticSkeleton :=
  genSemanticSkeleton (bfsAssign (mmTreeAir (K := K))) (assignedForest z α)

theorem semanticSkeleton_computeTree (z α : K) :
    (semanticSkeleton z α).computeTree =
      mapNTree ComputeNode.skel (mmComputeNodes z α) := by
  change mapNTree GenComputeRow.skel (bfsAssign (mmTreeAir (K := K))) =
    mapNTree ComputeNode.skel (mmComputeNodes z α)
  rw [mmComputeNodes, mapNTree_comp]
  have hfun : ComputeNode.skel ∘ setNodeCoins (0 : K) 0 1 = ComputeNode.skel := rfl
  rw [hfun, mapNTree_node_skel, renderRows_skel]

theorem execThreaded_computeTree_nodes (z α : K) :
    (execThreaded z α).computeTree =
      mapNTree ComputeNode.row (mmComputeNodes z α) :=
  (computeNodes_rows z α).symm

theorem computeTreeBinds_threaded (z α : K) :
    ComputeTreeBinds z (semanticSkeleton z α).computeTree
      (execThreaded z α).computeTree := by
  rw [semanticSkeleton_computeTree, execThreaded_computeTree_nodes]
  exact computeTreeBinds_of_nodesOK z α _ (mmComputeNodes_OK z α)

theorem memoryForestBinds_threaded (z α : K) :
    List.Forall₂ (MemoryTreeBinds z)
      (semanticSkeleton z α).memoryForest
      (execThreaded z α).memoryForest := by
  change List.Forall₂ (MemoryTreeBinds z)
      ((assignedForest z α).map (mapNTree GenMemoryRow.skel))
      ((memoryForestThreaded z α).map
        (mapNTree (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow MemoryTable.formRDefault)))
  have hf : (memoryForestThreaded z α).map (mapNTree
      (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow MemoryTable.formRDefault)) =
      (threadedForest z α).map
        (mapNTree (fun g : GenMemoryRow K => SemanticTimestampStrategy.MemoryRowTemplate.encodeRow MemoryTable.formRDefault
            g.row)) := by
    unfold memoryForestThreaded
    rw [List.map_map]
    refine List.map_congr_left (fun t _ => ?_)
    exact mapNTree_comp _ _ t
  rw [hf]
  unfold threadedForest assignedForest
  exact mmAssigned_threaded_memoryTreeBinds z α

theorem bindsAt_threaded (z α : K) :
    BindsAt z (semanticSkeleton z α) (cfg z α) (execThreaded z α) :=
  BindsAt.ofTreeBindings (F := F) (K := K)
    (S := semanticSkeleton z α) (cfg := cfg z α) (exec := execThreaded z α)
    rfl (computeTreeBinds_threaded z α) (memoryForestBinds_threaded z α)

theorem bindsAt_seed :
    BindsAt seedZ (semanticSkeleton seedZ alphaA) (cfg seedZ alphaA)
      (execThreaded seedZ alphaA) :=
  bindsAt_threaded seedZ alphaA

end

end Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

#print axioms Nock.NockVMROM.Thm54.TraceGen.mmAssigned_threaded_memoryTreeBinds
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.bindsAt_seed
