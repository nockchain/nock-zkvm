/-
  Nock/NockVMROM/Thm54/TraceGen/GenAirOrder.lean

  AIR child-order combinator on generated compute trees.

  `genComputeSkeleton` emits DFS children.  AIR `childLinkComp` identifies
  child `i` with parent `sf` triple `i`.  Those orders
  differ on OP6/OP7/OP8:

  * `.s6` DFS `[condition, taken]` vs AIR `[taken, condition]`
  * `.s7`/`.s8` DFS `[helper, consumer]` vs AIR `[consumer, helper]`

  `airReorder` permutes only those nodes (recursively).  Labels, fan-out,
  and non-swap opcodes are unchanged.  `Gen.lean` is not edited here.
-/
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.NockVMROM.Thm54.TraceGen.GenTierA
import Nock.NockVMROM.Thm54.P8Census
import Nock.NockVMROM.Thm54.P8Core.TraceGen.GenAirOrder

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

set_option linter.unusedSimpArgs false

theorem swapPair_length {α : Type*} (cs : List α) :
    (swapPair cs).length = cs.length := by
  match cs with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rfl

theorem swapPair_two {α : Type*} (a b : α) :
    swapPair [a, b] = [b, a] :=
  rfl

omit [Field K] in
theorem swapPair_map_sum {α : Type*} (cs : List α) (f : α → ℕ) :
    ((swapPair cs).map f).sum = (cs.map f).sum := by
  match cs with
  | [] => rfl
  | [_] => rfl
  | [a, b] => simp [swapPair, Nat.add_comm]
  | _ :: _ :: _ :: _ => rfl

theorem airReorder_size (t : NTree (GenComputeRow K)) :
    (airReorder t).size = t.size := by
  let P := fun t : NTree (GenComputeRow K) => (airReorder t).size = t.size
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro g cs ih
    change (airReorder (NTree.node g cs)).size = (NTree.node g cs).size
    simp [airReorder]
    split_ifs
    · simp [NTree.size, List.map_map]
      rw [swapPair_map_sum, List.map_map]
      congr 1
      exact List.map_congr_left fun c hc => ih c hc
    · simp [NTree.size, List.map_map]
      congr 1
      exact List.map_congr_left fun c hc => ih c hc
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

theorem airReorder_children_length (t : NTree (GenComputeRow K)) :
    (airReorder t).children.length = t.children.length := by
  cases t with
  | node g cs =>
    simp [airReorder]
    split_ifs with h
    · simp [swapPair_length, List.length_map]
    · simp [List.length_map]

theorem airReorder_leaf (g : GenComputeRow K) :
    airReorder (.node g []) = .node g [] := by
  simp [airReorder, swapPair]

theorem airNeedsSwap_s6 : airNeedsSwap State.s6 = true := rfl
theorem airNeedsSwap_s7 : airNeedsSwap State.s7 = true := rfl
theorem airNeedsSwap_s8 : airNeedsSwap State.s8 = true := rfl
theorem airNeedsSwap_s1 : airNeedsSwap State.s1 = false := rfl
theorem airNeedsSwap_s2 : airNeedsSwap State.s2 = false := rfl
theorem airNeedsSwap_s9 : airNeedsSwap State.s9 = false := rfl

theorem airReorder_op1 (g : GenComputeRow K) (hg : g.skel.state = .s1) :
    airReorder (.node g []) = .node g [] := by
  simp [airReorder, airNeedsSwap, hg, swapPair]

theorem airReorder_no_swap_cons (g : GenComputeRow K)
    (cs : List (NTree (GenComputeRow K)))
    (h : airNeedsSwap g.skel.state = false) :
    airReorder (.node g cs) = .node g (cs.map airReorder) := by
  simp [airReorder, h]

theorem airReorder_swap_cons (g : GenComputeRow K)
    (cs : List (NTree (GenComputeRow K)))
    (h : airNeedsSwap g.skel.state = true) :
    airReorder (.node g cs) = .node g (swapPair (cs.map airReorder)) := by
  simp [airReorder, h]

theorem airReorder_dotCond :
    airReorder (dotCondTree (K := K)) = dotCondTree := by
  simp [dotCondTree, airReorder, airNeedsSwap, genSkelOp1, skelNode, swapPair]

theorem airReorder_dotOp1B :
    airReorder (dotOp1BTree (K := K)) = dotOp1BTree := by
  simp [dotOp1BTree, airReorder, airNeedsSwap, genSkelOp1, skelNode, swapPair]

theorem airReorder_dotOp1C :
    airReorder (dotOp1CTree (K := K)) = dotOp1CTree := by
  simp [dotOp1CTree, airReorder, airNeedsSwap, genSkelOp1, skelNode, swapPair]

theorem airReorder_dotOp9Core :
    airReorder (dotOp9CoreTree (K := K)) = dotOp9CoreTree := by
  simp [dotOp9CoreTree, airReorder, airNeedsSwap, genSkelOp1, skelNode, swapPair]

theorem airReorder_dotOp9Invoke :
    airReorder (dotOp9InvokeTree (K := K)) = dotOp9InvokeTree := by
  simp [dotOp9InvokeTree, airReorder, airNeedsSwap, genSkelOp1, skelNode, swapPair]

theorem airReorder_dotOp9 :
    airReorder (dotOp9Tree (K := K)) = dotOp9Tree := by
  simp [dotOp9Tree, airReorder, airNeedsSwap, skelNode, genSkelOp9, dotOp9Skel,
    airReorder_dotOp9Core, airReorder_dotOp9Invoke]

theorem airReorder_dotOp2 :
    airReorder (dotOp2Tree (K := K)) = dotOp2Tree := by
  simp [dotOp2Tree, airReorder, airNeedsSwap, skelNode, genSkelOp2, dotOp2Skel,
    airReorder_dotOp1B, airReorder_dotOp1C, airReorder_dotOp9]

/-- The AIR twin of Tier A is the combinator on the generator's own DFS tree. -/
theorem airReorder_dotTree :
    airReorder (dotTree (K := K)) = (dotTreeAir (K := K)) := by
  simp [dotTree, dotTreeAir, airReorder, airNeedsSwap, skelNode, genSkelOp6,
    dotOp6Skel, swapPair, airReorder_dotCond, airReorder_dotOp2]

/-! ## Child skeletons vs parent `sf` slots after reorder -/

def childrenMatchSf (t : NTree (GenComputeRow K)) : Prop :=
  ∀ (i : Fin 3) (hi : (i : ℕ) < t.children.length),
    (t.children[i]'hi).label.skel.subject =
      P8Census.skeletonSubformula t.label.skel i TripleSlot.subject ∧
    (t.children[i]'hi).label.skel.formula =
      P8Census.skeletonSubformula t.label.skel i TripleSlot.formula ∧
    (t.children[i]'hi).label.skel.evaluation =
      P8Census.skeletonSubformula t.label.skel i TripleSlot.result

theorem childrenMatchSf_leaf (g : GenComputeRow K) :
    childrenMatchSf (.node g []) := by
  intro i hi
  simp [NTree.children] at hi

theorem childrenMatchSf_dotTreeAir :
    childrenMatchSf (dotTreeAir (K := K)) := by
  intro i hi
  have hcs : (dotTreeAir (K := K)).children = [dotOp2Tree, dotCondTree] := rfl
  have hi2 : (i : ℕ) < 2 := by simpa [hcs] using hi
  have h01 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hi2)
  rcases h01 with h0 | h1
  · have hi0 : i = 0 := Fin.ext h0
    subst hi0
    simp [hcs, dotTreeAir, skelNode, dotOp6Skel, genSkelOp6,
      P8Census.skeletonSubformula, fanoutComp, dotOp2Tree, dotOp2Skel, genSkelOp2]
  · have hi1 : i = 1 := Fin.ext h1
    subst hi1
    simp [hcs, dotTreeAir, skelNode, dotOp6Skel, genSkelOp6,
      P8Census.skeletonSubformula, fanoutComp, dotCondTree, genSkelOp1]

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.airReorder_dotTree
#print axioms Nock.NockVMROM.Thm54.TraceGen.airReorder_size
#print axioms Nock.NockVMROM.Thm54.TraceGen.childrenMatchSf_dotTreeAir
