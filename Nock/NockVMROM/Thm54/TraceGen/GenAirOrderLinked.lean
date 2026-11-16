/-
  Nock/NockVMROM/Thm54/TraceGen/GenAirOrderLinked.lean

  After `airReorder`, every node of a successfully generated compute tree
  has children in AIR `sf` order (`childrenMatchSf`).  Root subject /
  formula / evaluation of `genComputeSkeleton` are the call's triple.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrder
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonFanout
import Nock.NockVMROM.Thm54.P8Core.TraceGen.GenAirOrderLinked

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-! ## Generated root is the call triple -/

/-! ## `childrenMatchSf` constructors -/

theorem childrenMatchSf_one (g : GenComputeRow K)
    (a : NTree (GenComputeRow K))
    (_hfan : fanoutComp g.skel.state = 1)
    (h0 :
      a.label.skel.subject = P8Census.skeletonSubformula g.skel 0 TripleSlot.subject ∧
      a.label.skel.formula = P8Census.skeletonSubformula g.skel 0 TripleSlot.formula ∧
      a.label.skel.evaluation = P8Census.skeletonSubformula g.skel 0 TripleSlot.result) :
    childrenMatchSf (.node g [a]) := by
  intro i hi
  have hi1 : (i : ℕ) < 1 := by simpa using hi
  have hi0 : (i : ℕ) = 0 := Nat.lt_one_iff.mp hi1
  have : i = 0 := Fin.ext hi0
  subst this
  simpa [NTree.children] using h0

theorem childrenMatchSf_two (g : GenComputeRow K)
    (a b : NTree (GenComputeRow K))
    (h0 :
      a.label.skel.subject = P8Census.skeletonSubformula g.skel 0 TripleSlot.subject ∧
      a.label.skel.formula = P8Census.skeletonSubformula g.skel 0 TripleSlot.formula ∧
      a.label.skel.evaluation = P8Census.skeletonSubformula g.skel 0 TripleSlot.result)
    (h1 :
      b.label.skel.subject = P8Census.skeletonSubformula g.skel 1 TripleSlot.subject ∧
      b.label.skel.formula = P8Census.skeletonSubformula g.skel 1 TripleSlot.formula ∧
      b.label.skel.evaluation = P8Census.skeletonSubformula g.skel 1 TripleSlot.result) :
    childrenMatchSf (.node g [a, b]) := by
  intro i hi
  have hi2 : (i : ℕ) < 2 := by simpa using hi
  have h01 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hi2)
  rcases h01 with h0i | h1i
  · have : i = 0 := Fin.ext h0i
    subst this
    simpa [NTree.children] using h0
  · have : i = 1 := Fin.ext h1i
    subst this
    simpa [NTree.children] using h1

theorem childrenMatchSf_three (g : GenComputeRow K)
    (a b c : NTree (GenComputeRow K))
    (h0 :
      a.label.skel.subject = P8Census.skeletonSubformula g.skel 0 TripleSlot.subject ∧
      a.label.skel.formula = P8Census.skeletonSubformula g.skel 0 TripleSlot.formula ∧
      a.label.skel.evaluation = P8Census.skeletonSubformula g.skel 0 TripleSlot.result)
    (h1 :
      b.label.skel.subject = P8Census.skeletonSubformula g.skel 1 TripleSlot.subject ∧
      b.label.skel.formula = P8Census.skeletonSubformula g.skel 1 TripleSlot.formula ∧
      b.label.skel.evaluation = P8Census.skeletonSubformula g.skel 1 TripleSlot.result)
    (h2 :
      c.label.skel.subject = P8Census.skeletonSubformula g.skel 2 TripleSlot.subject ∧
      c.label.skel.formula = P8Census.skeletonSubformula g.skel 2 TripleSlot.formula ∧
      c.label.skel.evaluation = P8Census.skeletonSubformula g.skel 2 TripleSlot.result) :
    childrenMatchSf (.node g [a, b, c]) := by
  intro i hi
  have hi3 : (i : ℕ) < 3 := by simpa using hi
  have h012 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 := by omega
  rcases h012 with h0i | h1i | h2i
  · have : i = 0 := Fin.ext h0i
    subst this
    simpa [NTree.children] using h0
  · have : i = 1 := Fin.ext h1i
    subst this
    simpa [NTree.children] using h1
  · have : i = 2 := Fin.ext h2i
    subst this
    simpa [NTree.children] using h2

/-- Every node of an AIR-ordered tree has `sf`-matching children. -/
def AirLinked : NTree (GenComputeRow K) → Prop
  | .node g cs => childrenMatchSf (.node g cs) ∧ ∀ c ∈ cs, AirLinked c

theorem AirLinked_leaf (g : GenComputeRow K) : AirLinked (.node g []) := by
  unfold AirLinked
  exact ⟨childrenMatchSf_leaf g, fun c hc => by cases hc⟩

theorem mem_swapPair {α : Type*} {c : α} {cs : List α} (h : c ∈ swapPair cs) :
    c ∈ cs := by
  match cs with
  | [] => cases h
  | [_] => simpa [swapPair] using h
  | [a, b] =>
    have h' : c = b ∨ c = a := by simpa [swapPair] using h
    simpa [List.mem_cons, List.mem_singleton] using Or.symm h'
  | _ :: _ :: _ :: _ => simpa [swapPair] using h

theorem AirLinked_of_mem_swapPair {cs : List (NTree (GenComputeRow K))}
    (hcs : ∀ c ∈ cs, AirLinked c) {c : NTree (GenComputeRow K)}
    (hc : c ∈ swapPair cs) : AirLinked c :=
  hcs c (mem_swapPair hc)

/-! ## Slot equalities after `airReorder` -/

theorem sf_eq_of_root (t : NTree (GenComputeRow K)) (s f e : Noun)
    (h : t.label.skel.subject = s ∧ t.label.skel.formula = f ∧
      t.label.skel.evaluation = e) :
    (airReorder t).label.skel.subject = s ∧
      (airReorder t).label.skel.formula = f ∧
      (airReorder t).label.skel.evaluation = e := by
  simpa [airReorder_label] using h

theorem genComputeSkeleton_root_sfe_pair
    {fuel : ℕ} {subject formula : Noun}
    {p : NTree (GenComputeRow K) × Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok p) :
    p.1.label.skel.subject = subject ∧
      p.1.label.skel.formula = formula ∧
      p.1.label.skel.evaluation = p.2 := by
  have h' : genComputeSkeleton (K := K) fuel subject formula = .ok (p.1, p.2) := by
    simpa [Prod.mk.eta] using h
  exact genComputeSkeleton_root_sfe h'

theorem genSkelOp6_sf
    (s f hd ft fth ftt ftth fttt cond taken res : Noun) :
    P8Census.skeletonSubformula
        (genSkelOp6 s f hd ft fth ftt ftth fttt cond taken res) 0 TripleSlot.subject = s ∧
      P8Census.skeletonSubformula
        (genSkelOp6 s f hd ft fth ftt ftth fttt cond taken res) 0 TripleSlot.formula = taken ∧
      P8Census.skeletonSubformula
        (genSkelOp6 s f hd ft fth ftt ftth fttt cond taken res) 0 TripleSlot.result = res ∧
      P8Census.skeletonSubformula
        (genSkelOp6 s f hd ft fth ftt ftth fttt cond taken res) 1 TripleSlot.subject = s ∧
      P8Census.skeletonSubformula
        (genSkelOp6 s f hd ft fth ftt ftth fttt cond taken res) 1 TripleSlot.formula = fth ∧
      P8Census.skeletonSubformula
        (genSkelOp6 s f hd ft fth ftt ftth fttt cond taken res) 1 TripleSlot.result = cond := by
  simp [P8Census.skeletonSubformula, fanoutComp, genSkelOp6]

theorem genSkelOp7_sf (s f hd ft fth ftt sb res : Noun) :
    P8Census.skeletonSubformula (genSkelOp7 s f hd ft fth ftt sb res) 0 TripleSlot.subject = sb ∧
      P8Census.skeletonSubformula (genSkelOp7 s f hd ft fth ftt sb res) 0 TripleSlot.formula = ftt ∧
      P8Census.skeletonSubformula (genSkelOp7 s f hd ft fth ftt sb res) 0 TripleSlot.result = res ∧
      P8Census.skeletonSubformula (genSkelOp7 s f hd ft fth ftt sb res) 1 TripleSlot.subject = s ∧
      P8Census.skeletonSubformula (genSkelOp7 s f hd ft fth ftt sb res) 1 TripleSlot.formula = fth ∧
      P8Census.skeletonSubformula (genSkelOp7 s f hd ft fth ftt sb res) 1 TripleSlot.result = sb := by
  simp [P8Census.skeletonSubformula, fanoutComp, genSkelOp7]

theorem genSkelOp8_sf (s f hd ft fth ftt sb res : Noun) :
    P8Census.skeletonSubformula (genSkelOp8 s f hd ft fth ftt sb res) 0 TripleSlot.subject =
        .cell sb s ∧
      P8Census.skeletonSubformula (genSkelOp8 s f hd ft fth ftt sb res) 0 TripleSlot.formula = ftt ∧
      P8Census.skeletonSubformula (genSkelOp8 s f hd ft fth ftt sb res) 0 TripleSlot.result = res ∧
      P8Census.skeletonSubformula (genSkelOp8 s f hd ft fth ftt sb res) 1 TripleSlot.subject = s ∧
      P8Census.skeletonSubformula (genSkelOp8 s f hd ft fth ftt sb res) 1 TripleSlot.formula = fth ∧
      P8Census.skeletonSubformula (genSkelOp8 s f hd ft fth ftt sb res) 1 TripleSlot.result = sb := by
  simp [P8Census.skeletonSubformula, fanoutComp, genSkelOp8]

theorem genSkelOp2_sf (s f hd ft fth ftt sf1 sf2 res : Noun) :
    P8Census.skeletonSubformula (genSkelOp2 s f hd ft fth ftt sf1 sf2 res) 0 TripleSlot.subject = s ∧
      P8Census.skeletonSubformula (genSkelOp2 s f hd ft fth ftt sf1 sf2 res) 0 TripleSlot.formula = fth ∧
      P8Census.skeletonSubformula (genSkelOp2 s f hd ft fth ftt sf1 sf2 res) 0 TripleSlot.result = sf1 ∧
      P8Census.skeletonSubformula (genSkelOp2 s f hd ft fth ftt sf1 sf2 res) 1 TripleSlot.subject = s ∧
      P8Census.skeletonSubformula (genSkelOp2 s f hd ft fth ftt sf1 sf2 res) 1 TripleSlot.formula = ftt ∧
      P8Census.skeletonSubformula (genSkelOp2 s f hd ft fth ftt sf1 sf2 res) 1 TripleSlot.result = sf2 ∧
      P8Census.skeletonSubformula (genSkelOp2 s f hd ft fth ftt sf1 sf2 res) 2 TripleSlot.subject = sf1 ∧
      P8Census.skeletonSubformula (genSkelOp2 s f hd ft fth ftt sf1 sf2 res) 2 TripleSlot.formula = sf2 ∧
      P8Census.skeletonSubformula (genSkelOp2 s f hd ft fth ftt sf1 sf2 res) 2 TripleSlot.result = res := by
  simp [P8Census.skeletonSubformula, fanoutComp, genSkelOp2]

theorem genSkelOp9_sf (s f hd ft fth ftt core arm res : Noun) (axis : ℕ) :
    P8Census.skeletonSubformula (genSkelOp9 s f hd ft fth ftt core arm res axis) 0 TripleSlot.subject = s ∧
      P8Census.skeletonSubformula (genSkelOp9 s f hd ft fth ftt core arm res axis) 0 TripleSlot.formula = ftt ∧
      P8Census.skeletonSubformula (genSkelOp9 s f hd ft fth ftt core arm res axis) 0 TripleSlot.result = core ∧
      P8Census.skeletonSubformula (genSkelOp9 s f hd ft fth ftt core arm res axis) 1 TripleSlot.subject = core ∧
      P8Census.skeletonSubformula (genSkelOp9 s f hd ft fth ftt core arm res axis) 1 TripleSlot.formula = arm ∧
      P8Census.skeletonSubformula (genSkelOp9 s f hd ft fth ftt core arm res axis) 1 TripleSlot.result = res := by
  simp [P8Census.skeletonSubformula, fanoutComp, genSkelOp9]

theorem genSkelOp5_sf (s f hd ft fth ftt sf1 sf2 res : Noun) :
    P8Census.skeletonSubformula (genSkelOp5 s f hd ft fth ftt sf1 sf2 res) 0 TripleSlot.subject = s ∧
      P8Census.skeletonSubformula (genSkelOp5 s f hd ft fth ftt sf1 sf2 res) 0 TripleSlot.formula = fth ∧
      P8Census.skeletonSubformula (genSkelOp5 s f hd ft fth ftt sf1 sf2 res) 0 TripleSlot.result = sf1 ∧
      P8Census.skeletonSubformula (genSkelOp5 s f hd ft fth ftt sf1 sf2 res) 1 TripleSlot.subject = s ∧
      P8Census.skeletonSubformula (genSkelOp5 s f hd ft fth ftt sf1 sf2 res) 1 TripleSlot.formula = ftt ∧
      P8Census.skeletonSubformula (genSkelOp5 s f hd ft fth ftt sf1 sf2 res) 1 TripleSlot.result = sf2 := by
  simp [P8Census.skeletonSubformula, fanoutComp, genSkelOp5]

theorem genSkelCons_sf (s leftF rightF leftR rightR : Noun) :
    P8Census.skeletonSubformula (genSkelCons s leftF rightF leftR rightR) 0 TripleSlot.subject = s ∧
      P8Census.skeletonSubformula (genSkelCons s leftF rightF leftR rightR) 0 TripleSlot.formula = leftF ∧
      P8Census.skeletonSubformula (genSkelCons s leftF rightF leftR rightR) 0 TripleSlot.result = leftR ∧
      P8Census.skeletonSubformula (genSkelCons s leftF rightF leftR rightR) 1 TripleSlot.subject = s ∧
      P8Census.skeletonSubformula (genSkelCons s leftF rightF leftR rightR) 1 TripleSlot.formula = rightF ∧
      P8Census.skeletonSubformula (genSkelCons s leftF rightF leftR rightR) 1 TripleSlot.result = rightR := by
  simp [P8Census.skeletonSubformula, fanoutComp, genSkelCons]

theorem genSkelOp3_sf (s f hd tl cs cf cr res : Noun) :
    P8Census.skeletonSubformula (genSkelOp3 s f hd tl cs cf cr res) 0 TripleSlot.subject = cs ∧
      P8Census.skeletonSubformula (genSkelOp3 s f hd tl cs cf cr res) 0 TripleSlot.formula = cf ∧
      P8Census.skeletonSubformula (genSkelOp3 s f hd tl cs cf cr res) 0 TripleSlot.result = cr := by
  simp [P8Census.skeletonSubformula, fanoutComp, genSkelOp3]

theorem genSkelOp4_sf (s f hd tl cs cf cr res : Noun) :
    P8Census.skeletonSubformula (genSkelOp4 s f hd tl cs cf cr res) 0 TripleSlot.subject = cs ∧
      P8Census.skeletonSubformula (genSkelOp4 s f hd tl cs cf cr res) 0 TripleSlot.formula = cf ∧
      P8Census.skeletonSubformula (genSkelOp4 s f hd tl cs cf cr res) 0 TripleSlot.result = cr := by
  simp [P8Census.skeletonSubformula, fanoutComp, genSkelOp4]

theorem airNeedsSwap_skelNode_op6 (reqs : List (ServiceReq K))
    (s f hd ft fth ftt ftth fttt cond taken res : Noun) :
    airNeedsSwap (skelNode (genSkelOp6 s f hd ft fth ftt ftth fttt cond taken res) reqs).skel.state =
      true := by
  simp [skelNode, genSkelOp6, airNeedsSwap]

theorem airNeedsSwap_skelNode_op7 (reqs : List (ServiceReq K))
    (s f hd ft fth ftt sb res : Noun) :
    airNeedsSwap (skelNode (genSkelOp7 s f hd ft fth ftt sb res) reqs).skel.state = true := by
  simp [skelNode, genSkelOp7, airNeedsSwap]

theorem airNeedsSwap_skelNode_op8 (reqs : List (ServiceReq K))
    (s f hd ft fth ftt sb res : Noun) :
    airNeedsSwap (skelNode (genSkelOp8 s f hd ft fth ftt sb res) reqs).skel.state = true := by
  simp [skelNode, genSkelOp8, airNeedsSwap]

theorem airNeedsSwap_skelNode_op2 (reqs : List (ServiceReq K))
    (s f hd ft fth ftt sf1 sf2 res : Noun) :
    airNeedsSwap (skelNode (genSkelOp2 s f hd ft fth ftt sf1 sf2 res) reqs).skel.state = false := by
  simp [skelNode, genSkelOp2, airNeedsSwap]

theorem airNeedsSwap_skelNode_false_op9 (reqs : List (ServiceReq K))
    (s f hd ft fth ftt core arm res : Noun) (axis : ℕ) :
    airNeedsSwap (skelNode (genSkelOp9 s f hd ft fth ftt core arm res axis) reqs).skel.state =
      false := by
  simp [skelNode, genSkelOp9, airNeedsSwap]

theorem airNeedsSwap_skelNode_false_op5 (reqs : List (ServiceReq K))
    (s f hd ft fth ftt sf1 sf2 res : Noun) :
    airNeedsSwap (skelNode (genSkelOp5 s f hd ft fth ftt sf1 sf2 res) reqs).skel.state = false := by
  simp [skelNode, genSkelOp5, airNeedsSwap]

theorem airNeedsSwap_skelNode_false_cons (reqs : List (ServiceReq K))
    (s leftF rightF leftR rightR : Noun) :
    airNeedsSwap (skelNode (genSkelCons s leftF rightF leftR rightR) reqs).skel.state = false := by
  simp [skelNode, genSkelCons, airNeedsSwap]

theorem airNeedsSwap_skelNode_false_op3 (reqs : List (ServiceReq K))
    (s f hd tl cs cf cr res : Noun) :
    airNeedsSwap (skelNode (genSkelOp3 s f hd tl cs cf cr res) reqs).skel.state = false := by
  simp [skelNode, genSkelOp3, airNeedsSwap]

theorem airNeedsSwap_skelNode_false_op4 (reqs : List (ServiceReq K))
    (s f hd tl cs cf cr res : Noun) :
    airNeedsSwap (skelNode (genSkelOp4 s f hd tl cs cf cr res) reqs).skel.state = false := by
  simp [skelNode, genSkelOp4, airNeedsSwap]

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_root_sfe
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp6_sf
