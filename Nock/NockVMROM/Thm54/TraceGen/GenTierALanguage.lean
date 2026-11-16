/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierALanguage.lean

  Cumulative language on the AIR-ordered F769 carrier, then the
  seed-independent operational core and OP6 size window that `ofSkeleton`
  needs for `ExactExecutionSemanticData`.

  `memoryTrace` / `BuildableNockExecution` are not claimed here.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierABounded
import Nock.NockVMROM.Thm54.TraceGen.GenTierABuildableParts769
import Nock.NockVMROM.Thm54.BoundSemanticTrace
import Nock.NockVMROM.Thm54.ExactTraversal
import Mathlib.GroupTheory.OrderOfElement

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock Nock.Walk Nock.NockVM Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.NockVMROM.Thm54.SemanticTrace

noncomputable section

theorem traversable_seed
    (hfirst : ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.counts = 0) :
    TraversableChainedSemanticExactLanguage (cfg seedZ alphaA)
      (execThreaded seedZ alphaA) where
  chained := chained hfirst
  compute_topology := computeExactTopology_seed
  memory_topology := memoryExactTopology_seed

theorem language_seed
    (hfirst : ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.counts = 0) :
    NounRealizedTraversableChainedSemanticExactLanguage 769
      (cfg seedZ alphaA) (execThreaded seedZ alphaA) :=
  language_of_traversable_noun (traversable_seed hfirst) nounRealization_seed

/-! ## Operational core on the eight AIR skeleton rows -/

theorem air_bfsRows_slotSemantics (g : GenComputeRow K)
    (hg : g ∈ bfsRows (dotTreeAir (K := K))) :
    SkeletonSlotSemantics g.skel := by
  rw [dot_air_bfsRows] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h
  · subst h; simpa [dotTreeAir, skelNode] using dot_op6_slotSemantics
  · subst h; simpa [dotOp2Tree, skelNode] using dot_op2_slotSemantics
  · subst h; simpa [dotCondTree, skelNode] using genSkelOp1_slotSemantics _ _ _ _
  · subst h; simpa [dotOp1BTree, skelNode] using genSkelOp1_slotSemantics _ _ _ _
  · subst h; simpa [dotOp1CTree, skelNode] using genSkelOp1_slotSemantics _ _ _ _
  · subst h; simpa [dotOp9Tree, skelNode] using dot_op9_slotSemantics
  · subst h; simpa [dotOp9CoreTree, skelNode] using
      genSkelOp1_slotSemantics _ _ _ _
  · subst h; simpa [dotOp9InvokeTree, skelNode] using
      genSkelOp1_slotSemantics _ _ _ _

theorem air_bfsRows_recordEquations (g : GenComputeRow K)
    (hg : g ∈ bfsRows (dotTreeAir (K := K))) :
    SkeletonRecordEquations g.skel := by
  rw [dot_air_bfsRows] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h
  · subst h; simpa [dotTreeAir, skelNode] using dot_op6_recordEquations
  · subst h; simpa [dotOp2Tree, skelNode] using dot_op2_recordEquations
  · subst h; simpa [dotCondTree, skelNode] using
      genSkelOp1_recordEquations _ _ _ _
  · subst h; simpa [dotOp1BTree, skelNode] using
      genSkelOp1_recordEquations _ _ _ _
  · subst h; simpa [dotOp1CTree, skelNode] using
      genSkelOp1_recordEquations _ _ _ _
  · subst h; simpa [dotOp9Tree, skelNode] using dot_op9_recordEquations
  · subst h; simpa [dotOp9CoreTree, skelNode] using
      genSkelOp1_recordEquations _ _ _ _
  · subst h; simpa [dotOp9InvokeTree, skelNode] using
      genSkelOp1_recordEquations _ _ _ _

theorem semanticSkeleton_operationalCore (z α : K) :
    ∀ s ∈ computeSkeletonRows (semanticSkeleton z α),
      SkeletonOperationalCore s :=
  bfsAssign_operationalCore (dotTreeAir (K := K)) (assignedForest z α)
    (fun g hg => air_bfsRows_recordEquations g hg)
    (fun g hg => air_bfsRows_slotSemantics g hg)

/-! ## Size window at `seedZ = φ(8)` -/

theorem eight_isOfFinOrder : IsOfFinOrder (8 : F) :=
  isOfFinOrder_iff_pow_eq_one.mpr
    ⟨768, by norm_num, ZMod.pow_card_sub_one_eq_one (by decide)⟩

theorem eight_order_gt_one : 1 < orderOf (8 : F) := by
  have hpos : 0 < orderOf (8 : F) := eight_isOfFinOrder.orderOf_pos
  have hne : orderOf (8 : F) ≠ 1 := by
    intro h
    exact absurd (orderOf_eq_one_iff.mp h) (by decide)
  omega

theorem seedZ_ne_one : seedZ ≠ 1 := by
  intro h
  have h8 : (8 : F) = 1 := φ_injective (by simpa [seedZ] using h)
  exact absurd h8 (by decide)

theorem seedZ_order_gt_one : 1 < orderOf seedZ := by
  have hinj := orderOf_injective φ.toMonoidHom φ_injective (8 : F)
  have hcoe : φ.toMonoidHom (8 : F) = seedZ := rfl
  rw [hcoe] at hinj
  rw [hinj]
  exact eight_order_gt_one

theorem windows_of_ne_s346 {z : K} {s : ComputeRowSkeleton}
    (h3 : s.state ≠ .s3) (h4 : s.state ≠ .s4) (h6 : s.state ≠ .s6) :
    SkeletonSizeWindowPremises z s where
  s3_window h := (h3 h).elim
  s4_window h := (h4 h).elim
  s6_window h := (h6 h).elim

theorem op6_windows :
    SkeletonSizeWindowPremises seedZ dotOp6Skel where
  s3_window h := by simp [dotOp6Skel, genSkelOp6] at h
  s4_window h := by simp [dotOp6Skel, genSkelOp6] at h
  s6_window _ := by
    have hsf :
        P8Census.skeletonSubformula dotOp6Skel 1 TripleSlot.result =
          dotCondResult := by
      simp [P8Census.skeletonSubformula, dotOp6Skel, genSkelOp6,
        ComputeTable.fanoutComp]
    rw [hsf]
    refine ⟨seedZ_order_gt_one, ?_⟩
    simp [dotCondResult, Noun.leaves]
    exact seedZ_order_gt_one

theorem semanticSkeleton_windows :
    ∀ s ∈ computeSkeletonRows (semanticSkeleton seedZ alphaA),
      SkeletonSizeWindowPremises seedZ s := by
  intro s hs
  rw [semanticSkeleton_computeRows] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h | h | h | h | h
  · subst h
    have : (dotTreeAir (K := K)).label.skel = dotOp6Skel := rfl
    rw [this]
    exact op6_windows
  · subst h
    have : (dotOp2Tree (K := K)).label.skel = dotOp2Skel := rfl
    rw [this]
    exact windows_of_ne_s346
      (by simp [dotOp2Skel, genSkelOp2])
      (by simp [dotOp2Skel, genSkelOp2])
      (by simp [dotOp2Skel, genSkelOp2])
  · subst h
    exact windows_of_ne_s346
      (by simp [dotCondTree, skelNode, genSkelOp1])
      (by simp [dotCondTree, skelNode, genSkelOp1])
      (by simp [dotCondTree, skelNode, genSkelOp1])
  · subst h
    exact windows_of_ne_s346
      (by simp [dotOp1BTree, skelNode, genSkelOp1])
      (by simp [dotOp1BTree, skelNode, genSkelOp1])
      (by simp [dotOp1BTree, skelNode, genSkelOp1])
  · subst h
    exact windows_of_ne_s346
      (by simp [dotOp1CTree, skelNode, genSkelOp1])
      (by simp [dotOp1CTree, skelNode, genSkelOp1])
      (by simp [dotOp1CTree, skelNode, genSkelOp1])
  · subst h
    have : (dotOp9Tree (K := K)).label.skel = dotOp9Skel := rfl
    rw [this]
    exact windows_of_ne_s346
      (by simp [dotOp9Skel, genSkelOp9])
      (by simp [dotOp9Skel, genSkelOp9])
      (by simp [dotOp9Skel, genSkelOp9])
  · subst h
    exact windows_of_ne_s346
      (by simp [dotOp9CoreTree, skelNode, genSkelOp1])
      (by simp [dotOp9CoreTree, skelNode, genSkelOp1])
      (by simp [dotOp9CoreTree, skelNode, genSkelOp1])
  · subst h
    exact windows_of_ne_s346
      (by simp [dotOp9InvokeTree, skelNode, genSkelOp1])
      (by simp [dotOp9InvokeTree, skelNode, genSkelOp1])
      (by simp [dotOp9InvokeTree, skelNode, genSkelOp1])

theorem semanticSkeleton_operationalPremises :
    ∀ s ∈ computeSkeletonRows (semanticSkeleton seedZ alphaA),
      SkeletonOperationalPremises 769 seedZ s := by
  intro s hs
  exact operationalPremises_of_core_windows ringChar_K.symm
    (semanticSkeleton_operationalCore seedZ alphaA s hs)
    (semanticSkeleton_windows s hs)

end

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.traversable_seed
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.language_seed
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.semanticSkeleton_operationalPremises
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.seedZ_order_gt_one
