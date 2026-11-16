/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierAHonestData.lean

  Generator-own `HonestCommitment.Data` for AIR-ordered `DotConfig769`.
  Compute/memory node trees are the generator's threaded AIR forest;
  census and size-window obligations transport from `semanticSkeleton`.

  Does not claim `Inputs` / `statement_of_generated_residual`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierABuildable
import Nock.NockVMROM.Thm54.TraceGen.GenWF

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.NockVM
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

variable {K : Type} [Field K]

theorem MemoryTimestampSpecializesAt_setGenAcc (α : K)
    (g : GenMemoryRow K) (a b : K)
    (h : MemoryTimestampSpecializesAt α g.stamp g.row) :
    MemoryTimestampSpecializesAt α (setGenAcc g a b).stamp
      (setGenAcc g a b).row := by
  unfold setGenAcc MemoryTimestampSpecializesAt
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, ?_, ?_, ?_⟩
  · simpa [setAcc_st] using h2
  · simpa [setAcc_mem] using h3
  · intro hp
    simpa [setAcc_mem] using h4 hp

theorem threadGenRows_getElem_setGenAcc (inp : MemoryTable.Inputs K) :
    ∀ acc (gs : List (GenMemoryRow K)) (i : ℕ)
      (hi : i < (threadGenRows inp acc gs).length),
      ∃ a b, (threadGenRows inp acc gs)[i] =
        setGenAcc (gs[i]'(by
          have := threadGenRows_length inp acc gs
          omega)) a b
  | acc, [], i, hi => by simp [threadGenRows] at hi
  | acc, g :: gs, 0, _ =>
      ⟨acc, (threadGenRow inp acc g).1, rfl⟩
  | acc, g :: gs, i + 1, hi => by
      have hi' : i < (threadGenRows inp (threadGenRow inp acc g).1 gs).length := by
        simpa [threadGenRows] using hi
      obtain ⟨a, b, h⟩ :=
        threadGenRows_getElem_setGenAcc inp (threadGenRow inp acc g).1 gs i hi'
      exact ⟨a, b, h⟩

omit [Field K] in
theorem getElem_of_eq {α : Type*} {l₁ l₂ : List α} (h : l₁ = l₂)
    {n : ℕ} (h₁ : n < l₁.length) (h₂ : n < l₂.length) :
    l₁[n] = l₂[n] := by
  subst h
  rfl

omit [Field K] in
theorem mem_getElem {α : Type*} {a : α} {l : List α} :
    a ∈ l ↔ ∃ (i : ℕ) (h : i < l.length), l[i] = a := by
  constructor
  · intro h
    induction l with
    | nil => cases h
    | cons b l ih =>
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact ⟨0, Nat.succ_pos _, rfl⟩
        · obtain ⟨i, hi, rfl⟩ := ih h
          exact ⟨i + 1, Nat.succ_lt_succ hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact List.getElem_mem hi

theorem MemoryNodeOK_setGenAcc (z α : K) (g : GenMemoryRow K) (a b : K)
    (cs cs' : List (NTree (MemoryNode K)))
    (hlen : cs'.length = cs.length)
    (h : MemoryNodeOK z α (.node g.node cs)) :
    MemoryNodeOK z α (.node (setGenAcc g a b).node cs') := by
  obtain ⟨hfan, hst, hbind, htime⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cs'.length = MemoryTable.fanoutMem (setGenAcc g a b).node.skel.state
    rw [hlen]
    simpa [setGenAcc, GenMemoryRow.node] using hfan
  · simpa [setGenAcc, GenMemoryRow.node] using hst
  · simpa [GenMemoryRow.node] using BindMemoryRow_setGenAcc z g a b
      (by simpa [GenMemoryRow.node] using hbind)
  · simpa [GenMemoryRow.node] using
      MemoryTimestampSpecializesAt_setGenAcc α g a b
        (by simpa [GenMemoryRow.node] using htime)

theorem MemoryNodeOK_map_setGenAcc (z α : K)
    (t0 t : NTree (GenMemoryRow K))
    (ha : ∃ a b, t.label = setGenAcc t0.label a b)
    (hch : t.children.length = t0.children.length)
    (hOK : MemoryNodeOK z α (mapNTree GenMemoryRow.node t0)) :
    MemoryNodeOK z α (mapNTree GenMemoryRow.node t) := by
  obtain ⟨a, b, hlab⟩ := ha
  cases t0 with
  | node lbl0 cs0 =>
    cases t with
    | node lbl cs =>
      simp only [NTree.label_node, NTree.children_node] at hlab hch
      simp only [mapNTree] at hOK ⊢
      subst hlab
      exact MemoryNodeOK_setGenAcc z α lbl0 a b (cs0.map _) (cs.map _)
        (by simpa using hch) hOK

theorem MemoryNodesOK_threadGenForest (z α : K)
    (inp : MemoryTable.Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K)))
    (hOK : ∀ t ∈ forest, MemoryNodesOK z α (mapNTree GenMemoryRow.node t)) :
    ∀ t ∈ threadGenForest inp acc forest,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node t) := by
  intro t ht w hw
  have htF : w ∈ bfsForest [mapNTree GenMemoryRow.node t] :=
    (mem_bfsForest _ w).mpr ⟨_, List.mem_singleton.mpr rfl, hw⟩
  rw [show [mapNTree GenMemoryRow.node t] =
        [t].map (mapNTree GenMemoryRow.node) from rfl, bfsForest_mapNTree] at htF
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp htF
  have hin : InTree t v := by
    obtain ⟨c, hc, hct⟩ := (mem_bfsForest [t] v).mp hv
    simp only [List.mem_singleton] at hc
    subst c
    exact hct
  have hvF : v ∈ bfsForest (threadGenForest inp acc forest) :=
    (mem_bfsForest _ v).mpr ⟨t, ht, hin⟩
  obtain ⟨i, hi, hvget⟩ := mem_getElem.mp hvF
  have hi0 : i < (bfsForest forest).length := by
    rw [bfsForest_length, ← threadGenForest_totalSize inp acc forest, ← bfsForest_length]
    exact hi
  have hlab_eq :
      v.label =
        (threadGenRows inp acc ((bfsForest forest).map NTree.label))[i]'(by
          rw [threadGenRows_length, List.length_map]; exact hi0) := by
    have hmap := threadGenForest_bfs_labels inp acc forest
    have h₁ :
        ((bfsForest (threadGenForest inp acc forest)).map NTree.label)[i]'(by
            rw [List.length_map]; exact hi) =
          v.label := by
      simp [List.getElem_map, hvget]
    exact h₁.symm.trans (getElem_of_eq hmap (n := i)
      (by rw [List.length_map]; exact hi)
      (by rw [threadGenRows_length, List.length_map]; exact hi0))
  obtain ⟨a, b, hset⟩ :=
    threadGenRows_getElem_setGenAcc inp acc ((bfsForest forest).map NTree.label) i
      (by rw [threadGenRows_length, List.length_map]; exact hi0)
  have hlab : v.label = setGenAcc (bfsForest forest)[i].label a b := by
    rw [hlab_eq, hset]
    simp [List.getElem_map]
  have hunit :
      mapNTree (fun _ => ()) v =
        mapNTree (fun _ => ()) (bfsForest forest)[i] := by
    have hF :
        (bfsForest (threadGenForest inp acc forest)).map
            (mapNTree (fun _ => ())) =
          (bfsForest forest).map (mapNTree (fun _ => ())) := by
      rw [← bfsForest_mapNTree, ← bfsForest_mapNTree]
      exact congrArg bfsForest (threadGenForest_shapeOf inp acc forest)
    have hget := getElem_of_eq hF (n := i)
      (by rw [List.length_map]; exact hi)
      (by rw [List.length_map]; exact hi0)
    simpa [List.getElem_map, hvget] using hget
  have hch : v.children.length = (bfsForest forest)[i].children.length := by
    have := congrArg (fun t => t.children.length) hunit
    simpa [mapNTree_children, List.length_map] using this
  have hv0F : (bfsForest forest)[i] ∈ bfsForest forest :=
    List.getElem_mem hi0
  obtain ⟨u0, hu0, hin0⟩ := (mem_bfsForest _ _).mp hv0F
  have hnode0 :
      MemoryNodeOK z α
        (mapNTree GenMemoryRow.node (bfsForest forest)[i]) :=
    hOK u0 hu0 _ (mapNTree_inTree _ hin0)
  exact MemoryNodeOK_map_setGenAcc z α (bfsForest forest)[i] v
    ⟨a, b, hlab⟩ hch hnode0

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

variable (hfirst :
  ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.indicator = 0 ∧
    ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.counts = 0)


open Nock Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.EdgeComparisonCensus
open Nock.NockVMROM.Thm54.ProductionP8Containment

noncomputable def computeNodes : NTree (ComputeNode K) :=
  dotComputeNodesAir seedZ alphaA

noncomputable def memoryNodes : List (NTree (MemoryNode K)) :=
  (threadedForest seedZ alphaA).map (mapNTree GenMemoryRow.node)

theorem compute_rows :
    mapNTree ComputeNode.row computeNodes =
      (execThreaded seedZ alphaA).computeTree :=
  (execThreaded_computeTree_nodes seedZ alphaA).symm

-- Row-level memory: `Data.memory_rows` is about the a-bearing forest (`execA`), not the executed
-- one.
theorem memory_rows :
    memoryNodes.map (mapNTree MemoryNode.row) =
      (execThreadedA seedZ alphaA).memoryForest := by
  change memoryNodes.map (mapNTree MemoryNode.row) =
    (threadedForest seedZ alphaA).map (mapNTree GenMemoryRow.row)
  simp only [memoryNodes]
  rw [List.map_map]
  exact List.map_congr_left fun t _ => mapNTree_memNode_row t

theorem computeOK :
    ComputeNodesOK seedZ alphaA computeNodes :=
  dotComputeNodesAir_OK seedZ alphaA

theorem accAt_zero (t : NTree (GenComputeRow K)) : accAt t 0 = 0 :=
  rfl

theorem compute_root_line_exponent :
    computeNodes.label.stamp.lnPrevExponent = 0 := by
  simp only [computeNodes, dotComputeNodesAir, renderRows_eq_mapNTree,
    mapNTree_label, GenComputeRow.node, renderNode_op1_stamp, bfsAssign_label]
  have hi : 1 - 1 < (bfsRows (dotTreeAir (K := K))).length := by
    simp [dot_air_bfsRows]
  rw [bfsLabelAt_lnPrev (dotTreeAir (K := K)) 1 hi]
  exact accAt_zero _

theorem compute_root_line_origin :
    computeNodes.label.row.2.2.1.ln_prev = 1 := by
  have hstamp := compute_root_line_exponent
  simp only [computeNodes, dotComputeNodesAir, renderRows_eq_mapNTree, mapNTree_label,
    GenComputeRow.node, bfsAssign_label] at hstamp ⊢
  rw [renderNode_ln_prev]
  rw [renderNode_op1_stamp] at hstamp
  rw [hstamp, pow_zero]

theorem memoryOK :
    ∀ t ∈ memoryNodes, MemoryNodesOK seedZ alphaA t := by
  intro t ht
  simp only [memoryNodes, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  exact MemoryNodesOK_threadGenForest seedZ alphaA
    (memInputs seedZ) 0 (assignedForest seedZ alphaA)
    (assignedMemForest_OK_air seedZ alphaA) u (by
      simpa [threadedForest] using hu)

theorem skeletonOfNodes_eq :
    skeletonOfNodes computeNodes memoryNodes =
      semanticSkeleton seedZ alphaA := by
  refine congrArg₂ SemanticSkeleton.mk ?_ ?_
  · simp only [skeletonOfNodes, computeNodes]
    exact (semanticSkeleton_computeTree seedZ alphaA).symm
  · simp only [skeletonOfNodes, memoryNodes]
    rw [List.map_map]
    have hmap :
        (threadedForest seedZ alphaA).map
            (mapNTree MemoryNode.skel ∘ mapNTree GenMemoryRow.node) =
          (threadedForest seedZ alphaA).map (mapNTree GenMemoryRow.skel) :=
      List.map_congr_left fun t _ => mapNTree_memNode_skel t
    rw [hmap]
    unfold threadedForest
    exact threadGenForest_map_skel (memInputs seedZ) 0 (assignedForest seedZ alphaA)

theorem slotSemantics_skel :
    ∀ s ∈ computeSkeletonRows (semanticSkeleton seedZ alphaA),
      SkeletonSlotSemantics s :=
  bfsAssign_computeSkeletonRows_slotSemantics (dotTreeAir (K := K))
    (assignedForest seedZ alphaA) air_bfsRows_slotSemantics

theorem recordEquations_skel :
    ∀ s ∈ computeSkeletonRows (semanticSkeleton seedZ alphaA),
      SkeletonRecordEquations s :=
  bfsAssign_computeSkeletonRows_recordEquations (dotTreeAir (K := K))
    (assignedForest seedZ alphaA) air_bfsRows_recordEquations

theorem sizeWindowBound_skel :
    SizeWindowNounsBoundedBy (semanticSkeleton seedZ alphaA) Λ := by
  intro n hn
  unfold skeletonSizeWindowNouns at hn
  rw [List.mem_flatMap] at hn
  obtain ⟨s, hs, hn⟩ := hn
  rw [semanticSkeleton_computeRows] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h | h | h | h | h
  · subst h
    have : (dotTreeAir (K := K)).label.skel = dotOp6Skel := rfl
    rw [this] at hn
    have hreq :
        requiredSizeWindowNouns dotOp6Skel =
          [P8Census.skeletonSubformula dotOp6Skel 1 TripleSlot.result] :=
      rfl
    have hsf :
        P8Census.skeletonSubformula dotOp6Skel 1 TripleSlot.result =
          dotCondResult := by
      simp [P8Census.skeletonSubformula, dotOp6Skel, genSkelOp6,
        ComputeTable.fanoutComp]
    rw [hreq, hsf] at hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    subst hn
    simp [dotCondResult, Noun.leaves, Λ]
  · subst h
    have hreq : requiredSizeWindowNouns (dotOp2Tree (K := K)).label.skel = [] := rfl
    rw [hreq] at hn; simp at hn
  · subst h
    have hreq : requiredSizeWindowNouns (dotCondTree (K := K)).label.skel = [] := rfl
    rw [hreq] at hn; simp at hn
  · subst h
    have hreq : requiredSizeWindowNouns (dotOp1BTree (K := K)).label.skel = [] := rfl
    rw [hreq] at hn; simp at hn
  · subst h
    have hreq : requiredSizeWindowNouns (dotOp1CTree (K := K)).label.skel = [] := rfl
    rw [hreq] at hn; simp at hn
  · subst h
    have hreq : requiredSizeWindowNouns (dotOp9Tree (K := K)).label.skel = [] := rfl
    rw [hreq] at hn; simp at hn
  · subst h
    have hreq : requiredSizeWindowNouns (dotOp9CoreTree (K := K)).label.skel = [] := rfl
    rw [hreq] at hn; simp at hn
  · subst h
    have hreq : requiredSizeWindowNouns (dotOp9InvokeTree (K := K)).label.skel = [] := rfl
    rw [hreq] at hn; simp at hn

theorem compute_row_leaves
    (s : ComputeRowSkeleton)
    (hs : s ∈ computeSkeletonRows (semanticSkeleton seedZ alphaA)) :
    s.subject.leaves ≤ Λ ∧ s.formula.leaves ≤ Λ ∧ s.evaluation.leaves ≤ Λ ∧
      (∀ i : Fin 3, ∀ slot : TripleSlot,
        (P8Census.skeletonSubformula s i slot).leaves ≤ Λ) := by
  rw [semanticSkeleton_computeRows] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h | h | h | h | h
  · subst h
    have : (dotTreeAir (K := K)).label.skel = dotOp6Skel := rfl
    rw [this]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [dotOp6Skel, genSkelOp6, Noun.leaves, Λ, dotSubject]
    · simp [dotOp6Skel, genSkelOp6, Noun.leaves, Λ, dotFormula, dotParentTail,
        dotCondFormula, dotBranchPair, dotThenFormula, dotElseFormula, dotThenTail,
        dotOp2B, dotOp2C, dotOp9Formula, dotOp9Tail, dotCoreFormula, dotCore,
        dotElem0, dotElem1]
    · simp [dotOp6Skel, genSkelOp6, Noun.leaves, Λ, dotResult]
    · intro i slot
      fin_cases i <;> cases slot <;>
        simp [P8Census.skeletonSubformula, dotOp6Skel, genSkelOp6,
          ComputeTable.fanoutComp, Noun.leaves, Λ, dotSubject, dotFormula,
          dotParentTail, dotCondFormula, dotCondResult, dotThenFormula,
          dotElseFormula, dotThenTail, dotOp2B, dotOp2C, dotOp9Formula,
          dotOp9Tail, dotCoreFormula, dotCore, dotElem0, dotElem1,
          dotResult, dotBranchPair, leaves_dotThenFormula, leaves_dotElseFormula]
  · subst h
    have : (dotOp2Tree (K := K)).label.skel = dotOp2Skel := rfl
    rw [this]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [dotOp2Skel, genSkelOp2, Noun.leaves, Λ, dotSubject]
    · simp [dotOp2Skel, genSkelOp2, Noun.leaves, Λ, leaves_dotThenFormula]
    · simp [dotOp2Skel, genSkelOp2, Noun.leaves, Λ, dotResult]
    · intro i slot
      fin_cases i <;> cases slot <;>
        simp [P8Census.skeletonSubformula, dotOp2Skel, genSkelOp2,
          ComputeTable.fanoutComp, Noun.leaves, Λ, dotSubject, dotThenFormula,
          leaves_dotThenFormula, leaves_dotElseFormula, dotThenTail, dotOp2B,
          dotOp2C, dotOp2Sf1, dotOp2Sf2, dotOp9Formula, dotOp9Tail,
          dotCoreFormula, dotCore, dotElem0, dotElem1, dotResult]
  · subst h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [dotCondTree, skelNode, genSkelOp1, Noun.leaves, Λ, dotSubject]
    · simp [dotCondTree, skelNode, genSkelOp1, Noun.leaves, Λ, dotCondFormula]
    · simp [dotCondTree, skelNode, genSkelOp1, Noun.leaves, Λ, dotCondResult]
    · intro i slot
      fin_cases i <;> cases slot <;>
        simp [P8Census.skeletonSubformula, dotCondTree, skelNode, genSkelOp1,
          ComputeTable.fanoutComp, Noun.leaves, Λ]
  · subst h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [dotOp1BTree, skelNode, genSkelOp1, Noun.leaves, Λ, dotSubject]
    · simp [dotOp1BTree, skelNode, genSkelOp1, Noun.leaves, Λ, dotOp2B]
    · simp [dotOp1BTree, skelNode, genSkelOp1, Noun.leaves, Λ, dotOp2Sf1]
    · intro i slot
      fin_cases i <;> cases slot <;>
        simp [P8Census.skeletonSubformula, dotOp1BTree, skelNode, genSkelOp1,
          ComputeTable.fanoutComp, Noun.leaves, Λ]
  · subst h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [dotOp1CTree, skelNode, genSkelOp1, Noun.leaves, Λ, dotSubject]
    · simp [dotOp1CTree, skelNode, genSkelOp1, Noun.leaves, Λ, dotOp2C,
        dotOp9Formula, dotOp9Tail, dotCoreFormula, dotCore, dotElem0, dotElem1]
    · simp [dotOp1CTree, skelNode, genSkelOp1, Noun.leaves, Λ, dotOp2Sf2,
        dotOp9Formula, dotOp9Tail, dotCoreFormula, dotCore, dotElem0, dotElem1]
    · intro i slot
      fin_cases i <;> cases slot <;>
        simp [P8Census.skeletonSubformula, dotOp1CTree, skelNode, genSkelOp1,
          ComputeTable.fanoutComp, Noun.leaves, Λ]
  · subst h
    have : (dotOp9Tree (K := K)).label.skel = dotOp9Skel := rfl
    rw [this]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [dotOp9Skel, genSkelOp9, Noun.leaves, Λ, dotOp2Sf1]
    · simp [dotOp9Skel, genSkelOp9, Noun.leaves, Λ, dotOp9Formula, dotOp9Tail,
        dotCoreFormula, dotCore, dotElem0, dotElem1]
    · simp [dotOp9Skel, genSkelOp9, Noun.leaves, Λ, dotResult]
    · intro i slot
      fin_cases i <;> cases slot <;>
        simp [P8Census.skeletonSubformula, dotOp9Skel, genSkelOp9,
          ComputeTable.fanoutComp, Noun.leaves, Λ, dotOp2Sf1, dotOp9Formula,
          dotOp9Tail, dotCoreFormula, dotCore, dotElem0, dotElem1, dotArm,
          dotResult]
  · subst h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [dotOp9CoreTree, skelNode, genSkelOp1, Noun.leaves, Λ, dotOp2Sf1]
    · simp [dotOp9CoreTree, skelNode, genSkelOp1, Noun.leaves, Λ, dotCoreFormula,
        dotCore, dotElem0, dotElem1]
    · simp [dotOp9CoreTree, skelNode, genSkelOp1, Noun.leaves, Λ, dotCore,
        dotElem0, dotElem1]
    · intro i slot
      fin_cases i <;> cases slot <;>
        simp [P8Census.skeletonSubformula, dotOp9CoreTree, skelNode, genSkelOp1,
          ComputeTable.fanoutComp, Noun.leaves, Λ]
  · subst h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [dotOp9InvokeTree, skelNode, genSkelOp1, Noun.leaves, Λ, dotCore,
        dotElem0, dotElem1]
    · simp [dotOp9InvokeTree, skelNode, genSkelOp1, Noun.leaves, Λ, dotArm,
        dotElem0]
    · simp [dotOp9InvokeTree, skelNode, genSkelOp1, Noun.leaves, Λ, dotResult]
    · intro i slot
      fin_cases i <;> cases slot <;>
        simp [P8Census.skeletonSubformula, dotOp9InvokeTree, skelNode, genSkelOp1,
          ComputeTable.fanoutComp, Noun.leaves, Λ]

theorem census_skel :
    CombinedSkeletonCensus K (semanticSkeleton seedZ alphaA) Λ where
  p8 :=
    { leaves_bounded := by
        intro pair hp
        unfold skeletonPairs at hp
        rw [List.mem_append] at hp
        rcases hp with hp | hp
        · have hroot := compute_row_leaves _
            (computeTree_label_mem_rows (semanticSkeleton seedZ alphaA))
          simp [SemanticSkeleton.publicClaim, List.mem_cons, List.not_mem_nil] at hp
          rcases hp with rfl | rfl | rfl
          · exact ⟨hroot.1, hroot.1⟩
          · exact ⟨hroot.2.1, hroot.2.1⟩
          · exact ⟨hroot.2.2.1, hroot.2.2.1⟩
        · rw [List.mem_map] at hp
          obtain ⟨c, hc, rfl⟩ := hp
          unfold P8Census.skeletonComparisonCensus at hc
          rw [List.mem_flatMap] at hc
          obtain ⟨s, hs, hc⟩ := hc
          simpa [SemanticTrace.ComparisonUse.pair,
            SemanticTrace.ComparisonUse.LeavesBounded] using
            row_comparison_leaves s hs c hc }
  edges :=
    { leaves_bounded := by
        intro pair hp
        unfold edgePairs at hp
        rw [List.mem_flatMap] at hp
        obtain ⟨node, hnode, hrow⟩ := hp
        have hs : node.label ∈
            computeSkeletonRows (semanticSkeleton seedZ alphaA) :=
          List.mem_map.mpr ⟨node, hnode, rfl⟩
        have hpL := compute_row_leaves _ hs
        unfold rowEdgePairs at hrow
        rw [List.mem_flatMap] at hrow
        obtain ⟨xs, hxs, hpair⟩ := hrow
        rw [List.mem_ofFn] at hxs
        obtain ⟨i, rfl⟩ := hxs
        cases hch : node.childOpt i with
        | none => simp [hch] at hpair
        | some child =>
            simp [hch] at hpair
            have hinNode :
                InTree (semanticSkeleton seedZ alphaA).computeTree node := by
              obtain ⟨t, ht, hin⟩ :=
                (mem_bfsForest [(semanticSkeleton seedZ alphaA).computeTree]
                  node).1 hnode
              simp only [List.mem_singleton] at ht
              subst t
              exact hin
            have hinChild :
                InTree (semanticSkeleton seedZ alphaA).computeTree child :=
              InTree_trans hinNode
                (InTree.sub (childOpt_mem (i := (i : ℕ)) hch) (InTree.here child))
            have hcs : child.label ∈
                computeSkeletonRows (semanticSkeleton seedZ alphaA) := by
              refine List.mem_map.mpr ⟨child, ?_, rfl⟩
              exact (mem_bfsForest
                  [(semanticSkeleton seedZ alphaA).computeTree] child).2
                ⟨_, by simp, hinChild⟩
            have hcL := compute_row_leaves _ hcs
            simp [edgeTriple, List.mem_cons, List.not_mem_nil] at hpair
            rcases hpair with rfl | rfl | rfl
            · exact ⟨hcL.1, hpL.2.2.2 i .subject⟩
            · exact ⟨hcL.2.1, hpL.2.2.2 i .formula⟩
            · exact ⟨hcL.2.2.1, hpL.2.2.2 i .result⟩ }

theorem axis_range_skel :
    ∀ s ∈ computeSkeletonRows (semanticSkeleton seedZ alphaA),
      (s.state = .s0 → P8Census.skeletonMemoryAxis s 1 < 769) ∧
        (s.state = .s9 → P8Census.skeletonMemoryAxis s 2 < 769) := by
  intro s hs
  rw [semanticSkeleton_computeRows] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h | h | h | h | h
  · subst h
    constructor <;> intro hst
    · have hst' : (dotTreeAir (K := K)).label.skel.state = .s6 := rfl
      rw [hst'] at hst; cases hst
    · have hst' : (dotTreeAir (K := K)).label.skel.state = .s6 := rfl
      rw [hst'] at hst; cases hst
  · subst h
    constructor <;> intro hst
    · have hst' : (dotOp2Tree (K := K)).label.skel.state = .s2 := rfl
      rw [hst'] at hst; cases hst
    · have hst' : (dotOp2Tree (K := K)).label.skel.state = .s2 := rfl
      rw [hst'] at hst; cases hst
  · subst h
    constructor <;> intro hst
    · have hst' : (dotCondTree (K := K)).label.skel.state = .s1 := rfl
      rw [hst'] at hst; cases hst
    · have hst' : (dotCondTree (K := K)).label.skel.state = .s1 := rfl
      rw [hst'] at hst; cases hst
  · subst h
    constructor <;> intro hst
    · have hst' : (dotOp1BTree (K := K)).label.skel.state = .s1 := rfl
      rw [hst'] at hst; cases hst
    · have hst' : (dotOp1BTree (K := K)).label.skel.state = .s1 := rfl
      rw [hst'] at hst; cases hst
  · subst h
    constructor <;> intro hst
    · have hst' : (dotOp1CTree (K := K)).label.skel.state = .s1 := rfl
      rw [hst'] at hst; cases hst
    · have hst' : (dotOp1CTree (K := K)).label.skel.state = .s1 := rfl
      rw [hst'] at hst; cases hst
  · subst h
    constructor
    · intro hst
      have hst' : (dotOp9Tree (K := K)).label.skel.state = .s9 := rfl
      rw [hst'] at hst; cases hst
    · intro _
      have : (dotOp9Tree (K := K)).label.skel = dotOp9Skel := rfl
      rw [this]
      rw [skeletonMemoryAxis_dotOp9]
      decide
  · subst h
    constructor <;> intro hst
    · have hst' : (dotOp9CoreTree (K := K)).label.skel.state = .s1 := rfl
      rw [hst'] at hst; cases hst
    · have hst' : (dotOp9CoreTree (K := K)).label.skel.state = .s1 := rfl
      rw [hst'] at hst; cases hst
  · subst h
    constructor <;> intro hst
    · have hst' : (dotOp9InvokeTree (K := K)).label.skel.state = .s1 := rfl
      rw [hst'] at hst; cases hst
    · have hst' : (dotOp9InvokeTree (K := K)).label.skel.state = .s1 := rfl
      rw [hst'] at hst; cases hst

theorem combinedBounded_skel :
    CombinedBoundedBy K 769 (semanticSkeleton seedZ alphaA) :=
  combinedBounded_of_skeletonBounded_and_axis_range
    (semanticSkeleton_bounded seedZ alphaA) (by decide) ringChar_K.symm
    axis_range_skel

noncomputable def data : Data (dotBuildable hfirst) where
  computeNodes := computeNodes
  memoryNodes := memoryNodes
  compute_rows := compute_rows
  memory_rows := memory_rows
  computeOK := computeOK
  memoryOK := memoryOK
  root_line_exponent := compute_root_line_exponent
  root_line_origin := compute_root_line_origin
  nounSizeBound := Λ
  Λ := Λ
  slotSemantics := skeletonOfNodes_eq ▸ slotSemantics_skel
  recordEquations := skeletonOfNodes_eq ▸ recordEquations_skel
  census := skeletonOfNodes_eq ▸ census_skel
  sizeWindowBound := skeletonOfNodes_eq ▸ sizeWindowBound_skel
  q_eq_ringChar := ringChar_K.symm
  skeletonBounded := skeletonOfNodes_eq ▸ semanticSkeleton_bounded seedZ alphaA
  combinedBounded := skeletonOfNodes_eq ▸ combinedBounded_skel

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.MemoryNodesOK_threadGenForest
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.memoryOK
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.skeletonOfNodes_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.data
