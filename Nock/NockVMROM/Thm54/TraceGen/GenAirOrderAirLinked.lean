/-
  Nock/NockVMROM/Thm54/TraceGen/GenAirOrderAirLinked.lean

  `AirLinked (airReorder t)` for every successful `genComputeSkeleton`
  run: after the OP6/OP7/OP8 child swap, every node's children match
  parent `sf` triples.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderLinked

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

theorem airLinked_node_swap (g : GenComputeRow K)
    (x y : NTree (GenComputeRow K))
    (hsw : airNeedsSwap g.skel.state = true)
    (h0 :
      (airReorder y).label.skel.subject =
        P8Census.skeletonSubformula g.skel 0 TripleSlot.subject ∧
      (airReorder y).label.skel.formula =
        P8Census.skeletonSubformula g.skel 0 TripleSlot.formula ∧
      (airReorder y).label.skel.evaluation =
        P8Census.skeletonSubformula g.skel 0 TripleSlot.result)
    (h1 :
      (airReorder x).label.skel.subject =
        P8Census.skeletonSubformula g.skel 1 TripleSlot.subject ∧
      (airReorder x).label.skel.formula =
        P8Census.skeletonSubformula g.skel 1 TripleSlot.formula ∧
      (airReorder x).label.skel.evaluation =
        P8Census.skeletonSubformula g.skel 1 TripleSlot.result)
    (hx : AirLinked (airReorder x)) (hy : AirLinked (airReorder y)) :
    AirLinked (airReorder (.node g [x, y])) := by
  rw [airReorder_swap_cons g [x, y] hsw]
  simp only [List.map_cons, List.map_nil, swapPair]
  unfold AirLinked
  exact ⟨childrenMatchSf_two g (airReorder y) (airReorder x) h0 h1,
    fun c hc => by
      simp [List.mem_cons, List.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact hy
      · exact hx⟩

theorem airLinked_node_no_swap_two (g : GenComputeRow K)
    (x y : NTree (GenComputeRow K))
    (hsw : airNeedsSwap g.skel.state = false)
    (h0 :
      (airReorder x).label.skel.subject =
        P8Census.skeletonSubformula g.skel 0 TripleSlot.subject ∧
      (airReorder x).label.skel.formula =
        P8Census.skeletonSubformula g.skel 0 TripleSlot.formula ∧
      (airReorder x).label.skel.evaluation =
        P8Census.skeletonSubformula g.skel 0 TripleSlot.result)
    (h1 :
      (airReorder y).label.skel.subject =
        P8Census.skeletonSubformula g.skel 1 TripleSlot.subject ∧
      (airReorder y).label.skel.formula =
        P8Census.skeletonSubformula g.skel 1 TripleSlot.formula ∧
      (airReorder y).label.skel.evaluation =
        P8Census.skeletonSubformula g.skel 1 TripleSlot.result)
    (hx : AirLinked (airReorder x)) (hy : AirLinked (airReorder y)) :
    AirLinked (airReorder (.node g [x, y])) := by
  rw [airReorder_no_swap_cons g [x, y] hsw]
  simp only [List.map_cons, List.map_nil]
  unfold AirLinked
  exact ⟨childrenMatchSf_two g (airReorder x) (airReorder y) h0 h1,
    fun c hc => by
      simp [List.mem_cons, List.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact hx
      · exact hy⟩

theorem airLinked_node_no_swap_three (g : GenComputeRow K)
    (x y z : NTree (GenComputeRow K))
    (hsw : airNeedsSwap g.skel.state = false)
    (h0 :
      (airReorder x).label.skel.subject =
        P8Census.skeletonSubformula g.skel 0 TripleSlot.subject ∧
      (airReorder x).label.skel.formula =
        P8Census.skeletonSubformula g.skel 0 TripleSlot.formula ∧
      (airReorder x).label.skel.evaluation =
        P8Census.skeletonSubformula g.skel 0 TripleSlot.result)
    (h1 :
      (airReorder y).label.skel.subject =
        P8Census.skeletonSubformula g.skel 1 TripleSlot.subject ∧
      (airReorder y).label.skel.formula =
        P8Census.skeletonSubformula g.skel 1 TripleSlot.formula ∧
      (airReorder y).label.skel.evaluation =
        P8Census.skeletonSubformula g.skel 1 TripleSlot.result)
    (h2 :
      (airReorder z).label.skel.subject =
        P8Census.skeletonSubformula g.skel 2 TripleSlot.subject ∧
      (airReorder z).label.skel.formula =
        P8Census.skeletonSubformula g.skel 2 TripleSlot.formula ∧
      (airReorder z).label.skel.evaluation =
        P8Census.skeletonSubformula g.skel 2 TripleSlot.result)
    (hx : AirLinked (airReorder x)) (hy : AirLinked (airReorder y))
    (hz : AirLinked (airReorder z)) :
    AirLinked (airReorder (.node g [x, y, z])) := by
  rw [airReorder_no_swap_cons g [x, y, z] hsw]
  simp only [List.map_cons, List.map_nil]
  unfold AirLinked
  exact ⟨childrenMatchSf_three g (airReorder x) (airReorder y) (airReorder z) h0 h1 h2,
    fun c hc => by
      simp [List.mem_cons, List.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hz⟩

theorem airLinked_node_no_swap_one (g : GenComputeRow K)
    (x : NTree (GenComputeRow K))
    (hsw : airNeedsSwap g.skel.state = false)
    (hfan : fanoutComp g.skel.state = 1)
    (h0 :
      (airReorder x).label.skel.subject =
        P8Census.skeletonSubformula g.skel 0 TripleSlot.subject ∧
      (airReorder x).label.skel.formula =
        P8Census.skeletonSubformula g.skel 0 TripleSlot.formula ∧
      (airReorder x).label.skel.evaluation =
        P8Census.skeletonSubformula g.skel 0 TripleSlot.result)
    (hx : AirLinked (airReorder x)) :
    AirLinked (airReorder (.node g [x])) := by
  rw [airReorder_no_swap_cons g [x] hsw]
  simp only [List.map_cons, List.map_nil]
  unfold AirLinked
  exact ⟨childrenMatchSf_one g (airReorder x) hfan h0,
    fun c hc => by
      simp [List.mem_cons, List.mem_singleton] at hc
      subst hc
      exact hx⟩

theorem airLinked_node_leaf (g : GenComputeRow K) :
    AirLinked (airReorder (.node g [])) := by
  rw [airReorder_leaf]
  exact AirLinked_leaf g

theorem childrenMatchSf_of_AirLinked {t : NTree (GenComputeRow K)}
    (h : AirLinked t) : childrenMatchSf t := by
  cases t with
  | node _g _cs =>
    unfold AirLinked at h
    exact h.1

/-- Root `(s,f,e)` plus an `sf`-slot lemma close one AIR child equation. -/
theorem air_sfe_eq {t : NTree (GenComputeRow K)} {s f e s' f' e' : Noun}
    (hs : t.label.skel.subject = s ∧ t.label.skel.formula = f ∧ t.label.skel.evaluation = e)
    (hsf : s' = s ∧ f' = f ∧ e' = e) :
    (airReorder t).label.skel.subject = s' ∧
      (airReorder t).label.skel.formula = f' ∧
      (airReorder t).label.skel.evaluation = e' :=
  ⟨(airReorder_label t ▸ hs.1).trans hsf.1.symm,
    (airReorder_label t ▸ hs.2.1).trans hsf.2.1.symm,
    (airReorder_label t ▸ hs.2.2).trans hsf.2.2.symm⟩

/-- Generated trees are AIR-linked after `airReorder` -/
theorem airLinked_airReorder_of_gen
    {fuel : ℕ} {subject formula : Noun}
    {p : NTree (GenComputeRow K) × Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok p) :
    AirLinked (airReorder p.1) := by
  induction fuel generalizing subject formula p with
  | zero =>
    simp [genComputeSkeleton] at h
  | succ n ih =>
    cases formula with
    | atom _ =>
      simp [genComputeSkeleton] at h
    | cell hd tl =>
      cases hd with
      | cell lh lt =>
        cases hL : genComputeSkeleton (K := K) n subject (.cell lh lt) with
        | error _ => simp [genComputeSkeleton, hL] at h
        | ok pL =>
          cases hR : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hL, hR] at h
          | ok pR =>
            simp [genComputeSkeleton, hL, hR] at h
            subst h
            refine airLinked_node_no_swap_two _ pL.1 pR.1
              (airNeedsSwap_skelNode_false_cons _ _ _ _ _ _) ?_ ?_
              (ih hL) (ih hR)
            · have hs := genComputeSkeleton_root_sfe_pair hL
              have hsf := genSkelCons_sf subject (.cell lh lt) tl pL.2 pR.2
              simpa [skelNode] using air_sfe_eq hs ⟨hsf.1, hsf.2.1, hsf.2.2.1⟩
            · have hs := genComputeSkeleton_root_sfe_pair hR
              have hsf := genSkelCons_sf subject (.cell lh lt) tl pL.2 pR.2
              simpa [skelNode] using air_sfe_eq hs ⟨hsf.2.2.2.1, hsf.2.2.2.2.1, hsf.2.2.2.2.2⟩
      | atom op =>
        rcases nat_lt_twelve_or_ge op with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hge
        · cases tl with
          | cell _ _ => simp [genComputeSkeleton] at h
          | atom ax =>
            cases hslot : Noun.slot ax subject with
            | none => simp [genComputeSkeleton, hslot] at h
            | some _ =>
              simp [genComputeSkeleton, hslot] at h
              subst h
              exact airLinked_node_leaf _
        · simp [genComputeSkeleton] at h
          subst h
          exact airLinked_node_leaf _
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                cases hM : genComputeSkeleton (K := K) n pB.2 pC.2 with
                | error _ => simp [genComputeSkeleton, hB, hC, hM] at h
                | ok pM =>
                  simp [genComputeSkeleton, hB, hC, hM] at h
                  subst h
                  refine airLinked_node_no_swap_three _ pB.1 pC.1 pM.1
                    (airNeedsSwap_skelNode_op2 _ _ _ _ _ _ _ _ _ _) ?_ ?_ ?_
                    (ih hB) (ih hC) (ih hM)
                  · have hs := genComputeSkeleton_root_sfe_pair hB
                    have hsf := genSkelOp2_sf subject (.cell (.atom 2) (.cell b c)) (.atom 2)
                      (.cell b c) b c pB.2 pC.2 pM.2
                    simpa [skelNode] using air_sfe_eq hs ⟨hsf.1, hsf.2.1, hsf.2.2.1⟩
                  · have hs := genComputeSkeleton_root_sfe_pair hC
                    have hsf := genSkelOp2_sf subject (.cell (.atom 2) (.cell b c)) (.atom 2)
                      (.cell b c) b c pB.2 pC.2 pM.2
                    simpa [skelNode] using air_sfe_eq hs ⟨hsf.2.2.2.1, hsf.2.2.2.2.1, hsf.2.2.2.2.2.1⟩
                  · have hs := genComputeSkeleton_root_sfe_pair hM
                    have hsf := genSkelOp2_sf subject (.cell (.atom 2) (.cell b c)) (.atom 2)
                      (.cell b c) b c pB.2 pC.2 pM.2
                    simpa [skelNode] using
                      air_sfe_eq hs ⟨hsf.2.2.2.2.2.2.1, hsf.2.2.2.2.2.2.2.1, hsf.2.2.2.2.2.2.2.2⟩
        · cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok pCall =>
            simp [genComputeSkeleton, hcall] at h
            subst h
            refine airLinked_node_no_swap_one _ pCall.1
              (airNeedsSwap_skelNode_false_op3 _ _ _ _ _ _ _ _ _)
              (by simp [skelNode, genSkelOp3, fanoutComp]) ?_ (ih hcall)
            have hs := genComputeSkeleton_root_sfe_pair hcall
            have hsf := genSkelOp3_sf subject (.cell (.atom 3) tl) (.atom 3) tl
              subject tl pCall.2 (Noun.wut pCall.2)
            simpa [skelNode] using air_sfe_eq hs hsf
        · cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok pCall =>
            cases hlus : Noun.lus pCall.2 with
            | none => simp [genComputeSkeleton, hcall, hlus] at h
            | some res =>
              simp [genComputeSkeleton, hcall, hlus] at h
              subst h
              refine airLinked_node_no_swap_one _ pCall.1
                (airNeedsSwap_skelNode_false_op4 _ _ _ _ _ _ _ _ _)
                (by simp [skelNode, genSkelOp4, fanoutComp]) ?_ (ih hcall)
              have hs := genComputeSkeleton_root_sfe_pair hcall
              have hsf := genSkelOp4_sf subject (.cell (.atom 4) tl) (.atom 4) tl
                subject tl pCall.2 res
              simpa [skelNode] using air_sfe_eq hs hsf
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                subst h
                refine airLinked_node_no_swap_two _ pB.1 pC.1
                  (airNeedsSwap_skelNode_false_op5 _ _ _ _ _ _ _ _ _ _) ?_ ?_
                  (ih hB) (ih hC)
                · have hs := genComputeSkeleton_root_sfe_pair hB
                  have hsf := genSkelOp5_sf subject (.cell (.atom 5) (.cell b c)) (.atom 5)
                    (.cell b c) b c pB.2 pC.2 (Noun.tis pB.2 pC.2)
                  simpa [skelNode] using air_sfe_eq hs ⟨hsf.1, hsf.2.1, hsf.2.2.1⟩
                · have hs := genComputeSkeleton_root_sfe_pair hC
                  have hsf := genSkelOp5_sf subject (.cell (.atom 5) (.cell b c)) (.atom 5)
                    (.cell b c) b c pB.2 pC.2 (Noun.tis pB.2 pC.2)
                  simpa [skelNode] using air_sfe_eq hs ⟨hsf.2.2.2.1, hsf.2.2.2.2.1, hsf.2.2.2.2.2⟩
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b rest =>
            cases rest with
            | atom _ => simp [genComputeSkeleton] at h
            | cell c d =>
              cases hcond : genComputeSkeleton (K := K) n subject b with
              | error _ => simp [genComputeSkeleton, hcond] at h
              | ok pCond =>
                cases hval : pCond.2 with
                | cell _ _ => simp [genComputeSkeleton, hcond, hval] at h
                | atom condv =>
                  cases condv with
                  | zero =>
                    cases htaken : genComputeSkeleton (K := K) n subject c with
                    | error _ => simp [genComputeSkeleton, hcond, hval, htaken] at h
                    | ok pTaken =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                      subst h
                      refine airLinked_node_swap _ pCond.1 pTaken.1
                        (airNeedsSwap_skelNode_op6 _ _ _ _ _ _ _ _ _ _ _ _) ?_ ?_
                        (ih hcond) (ih htaken)
                      · have hs := genComputeSkeleton_root_sfe_pair htaken
                        have hsf := genSkelOp6_sf subject
                          (.cell (.atom 6) (.cell b (.cell c d))) (.atom 6)
                          (.cell b (.cell c d)) b (.cell c d) c d (.atom 0) c pTaken.2
                        simpa [skelNode] using air_sfe_eq hs ⟨hsf.1, hsf.2.1, hsf.2.2.1⟩
                      · have hs := genComputeSkeleton_root_sfe_pair hcond
                        have hs0 : pCond.1.label.skel.subject = subject ∧
                            pCond.1.label.skel.formula = b ∧
                            pCond.1.label.skel.evaluation = .atom 0 := by
                          simpa [hval] using hs
                        have hsf := genSkelOp6_sf subject
                          (.cell (.atom 6) (.cell b (.cell c d))) (.atom 6)
                          (.cell b (.cell c d)) b (.cell c d) c d (.atom 0) c pTaken.2
                        simpa [skelNode] using
                          air_sfe_eq hs0 ⟨hsf.2.2.2.1, hsf.2.2.2.2.1, hsf.2.2.2.2.2⟩
                  | succ condv =>
                    cases condv with
                    | zero =>
                      cases htaken : genComputeSkeleton (K := K) n subject d with
                      | error _ => simp [genComputeSkeleton, hcond, hval, htaken] at h
                      | ok pTaken =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                        subst h
                        refine airLinked_node_swap _ pCond.1 pTaken.1
                          (airNeedsSwap_skelNode_op6 _ _ _ _ _ _ _ _ _ _ _ _) ?_ ?_
                          (ih hcond) (ih htaken)
                        · have hs := genComputeSkeleton_root_sfe_pair htaken
                          have hsf := genSkelOp6_sf subject
                            (.cell (.atom 6) (.cell b (.cell c d))) (.atom 6)
                            (.cell b (.cell c d)) b (.cell c d) c d (.atom 1) d pTaken.2
                          simpa [skelNode] using air_sfe_eq hs ⟨hsf.1, hsf.2.1, hsf.2.2.1⟩
                        · have hs := genComputeSkeleton_root_sfe_pair hcond
                          have hs1 : pCond.1.label.skel.subject = subject ∧
                              pCond.1.label.skel.formula = b ∧
                              pCond.1.label.skel.evaluation = .atom 1 := by
                            simpa [hval] using hs
                          have hsf := genSkelOp6_sf subject
                            (.cell (.atom 6) (.cell b (.cell c d))) (.atom 6)
                            (.cell b (.cell c d)) b (.cell c d) c d (.atom 1) d pTaken.2
                          simpa [skelNode] using
                            air_sfe_eq hs1 ⟨hsf.2.2.2.1, hsf.2.2.2.2.1, hsf.2.2.2.2.2⟩
                    | succ _ =>
                      simp [genComputeSkeleton, hcond, hval] at h
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n pB.2 c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                subst h
                refine airLinked_node_swap _ pB.1 pC.1
                  (airNeedsSwap_skelNode_op7 _ _ _ _ _ _ _ _ _) ?_ ?_
                  (ih hB) (ih hC)
                · have hs := genComputeSkeleton_root_sfe_pair hC
                  have hsf := genSkelOp7_sf subject (.cell (.atom 7) (.cell b c)) (.atom 7)
                    (.cell b c) b c pB.2 pC.2
                  simpa [skelNode] using air_sfe_eq hs ⟨hsf.1, hsf.2.1, hsf.2.2.1⟩
                · have hs := genComputeSkeleton_root_sfe_pair hB
                  have hsf := genSkelOp7_sf subject (.cell (.atom 7) (.cell b c)) (.atom 7)
                    (.cell b c) b c pB.2 pC.2
                  simpa [skelNode] using air_sfe_eq hs ⟨hsf.2.2.2.1, hsf.2.2.2.2.1, hsf.2.2.2.2.2⟩
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n (.cell pB.2 subject) c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                subst h
                refine airLinked_node_swap _ pB.1 pC.1
                  (airNeedsSwap_skelNode_op8 _ _ _ _ _ _ _ _ _) ?_ ?_
                  (ih hB) (ih hC)
                · have hs := genComputeSkeleton_root_sfe_pair hC
                  have hsf := genSkelOp8_sf subject (.cell (.atom 8) (.cell b c)) (.atom 8)
                    (.cell b c) b c pB.2 pC.2
                  simpa [skelNode] using air_sfe_eq hs ⟨hsf.1, hsf.2.1, hsf.2.2.1⟩
                · have hs := genComputeSkeleton_root_sfe_pair hB
                  have hsf := genSkelOp8_sf subject (.cell (.atom 8) (.cell b c)) (.atom 8)
                    (.cell b c) b c pB.2 pC.2
                  simpa [skelNode] using air_sfe_eq hs ⟨hsf.2.2.2.1, hsf.2.2.2.2.1, hsf.2.2.2.2.2⟩
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell axN c =>
            cases axN with
            | cell _ _ => simp [genComputeSkeleton] at h
            | atom ax =>
              cases hcore : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hcore] at h
              | ok pCore =>
                cases hslot : Noun.slot ax pCore.2 with
                | none => simp [genComputeSkeleton, hcore, hslot] at h
                | some arm =>
                  cases hinv : genComputeSkeleton (K := K) n pCore.2 arm with
                  | error _ => simp [genComputeSkeleton, hcore, hslot, hinv] at h
                  | ok pInv =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                    subst h
                    refine airLinked_node_no_swap_two _ pCore.1 pInv.1
                      (airNeedsSwap_skelNode_false_op9 _ _ _ _ _ _ _ _ _ _ _) ?_ ?_
                      (ih hcore) (ih hinv)
                    · have hs := genComputeSkeleton_root_sfe_pair hcore
                      have hsf := genSkelOp9_sf subject (.cell (.atom 9) (.cell (.atom ax) c))
                        (.atom 9) (.cell (.atom ax) c) (.atom ax) c pCore.2 arm pInv.2 ax
                      simpa [skelNode] using air_sfe_eq hs ⟨hsf.1, hsf.2.1, hsf.2.2.1⟩
                    · have hs := genComputeSkeleton_root_sfe_pair hinv
                      have hsf := genSkelOp9_sf subject (.cell (.atom 9) (.cell (.atom ax) c))
                        (.atom 9) (.cell (.atom ax) c) (.atom ax) c pCore.2 arm pInv.2 ax
                      simpa [skelNode] using air_sfe_eq hs ⟨hsf.2.2.2.1, hsf.2.2.2.2.1, hsf.2.2.2.2.2⟩
        · simp [genComputeSkeleton] at h
        · simp [genComputeSkeleton] at h
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
          simp only [genComputeSkeleton] at h
          split at h <;> first | omega | contradiction

theorem childrenMatchSf_airReorder_of_gen
    {fuel : ℕ} {subject formula : Noun}
    {p : NTree (GenComputeRow K) × Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok p) :
    childrenMatchSf (airReorder p.1) :=
  childrenMatchSf_of_AirLinked (airLinked_airReorder_of_gen h)

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.airLinked_airReorder_of_gen
#print axioms Nock.NockVMROM.Thm54.TraceGen.childrenMatchSf_airReorder_of_gen
