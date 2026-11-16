/-
  Nock/NockVMROM/Thm54/TraceGen/GenSkeletonBind.lean

  Every node of a `genComputeSkeleton` tree binds its rendered compute
  row (`BindComputeRow` of `renderNode` against the node's skeleton).
  Used with `GenSkeletonFanout` to lift `ComputeNodesOK` off named BFS
  forests (Tier A) onto opaque generated trees (matmul).

  `Gen.lean` is not edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonFanout
import Nock.NockVMROM.Thm54.TraceGen.GenRowSemantic
import Nock.NockVMROM.Thm54.TraceGen.GenSound

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open ComputeTable

variable {K : Type} [Field K]

/-! ## `renderNode` of an explicit `skelNode` binds -/

theorem bind_render_cons (z α : K) (stamp : ComputeTimestampRow)
    (subject leftF rightF leftR rightR : Noun) (reqs : List (ServiceReq K)) :
    BindComputeRow z
      (skelNode (genSkelCons subject leftF rightF leftR rightR) reqs).skel
      (renderNode z α
        {(skelNode (genSkelCons subject leftF rightF leftR rightR) reqs)
          with stamp := stamp}).row := by
  have hstate :
      ({(skelNode (genSkelCons subject leftF rightF leftR rightR) reqs)
          with stamp := stamp} : GenComputeRow K).skel.state = State.cons := by
    simp [skelNode, genSkelCons]
  rw [renderNode_cons_row z α _ hstate]
  simp [skelNode]
  exact genSkelCons_bindCompute z α subject leftF rightF leftR rightR stamp

theorem bind_render_op0 (z α : K) (stamp : ComputeTimestampRow)
    (subject formula head tail result : Noun) (axis : ℕ)
    (reqs : List (ServiceReq K))
    (hhead : formulaHead formula = head) (htail : formulaTail formula = tail) :
    BindComputeRow z
      (skelNode (genSkelOp0 subject formula head tail result axis) reqs).skel
      (renderNode z α
        {(skelNode (genSkelOp0 subject formula head tail result axis) reqs)
          with stamp := stamp}).row := by
  have hstate :
      ({(skelNode (genSkelOp0 subject formula head tail result axis) reqs)
          with stamp := stamp} : GenComputeRow K).skel.state = State.s0 := by
    simp [skelNode, genSkelOp0]
  rw [renderNode_op0_row z α _ hstate]
  simp [skelNode]
  exact genSkelOp0_bindCompute z α subject formula head tail result axis stamp
    hhead htail

theorem bind_render_op1 (z α : K) (stamp : ComputeTimestampRow)
    (subject formula result head : Noun) (reqs : List (ServiceReq K))
    (hhead : formulaHead formula = head) :
    BindComputeRow z
      (skelNode (genSkelOp1 subject formula result head) reqs).skel
      (renderNode z α
        {(skelNode (genSkelOp1 subject formula result head) reqs)
          with stamp := stamp}).row := by
  have hstate :
      ({(skelNode (genSkelOp1 subject formula result head) reqs)
          with stamp := stamp} : GenComputeRow K).skel.state = State.s1 := by
    simp [skelNode, genSkelOp1]
  rw [renderNode_op1_row z α _ hstate]
  simp [skelNode]
  exact genSkelOp1_bindCompute z α subject formula result head stamp hhead

theorem bind_render_op2 (z α : K) (stamp : ComputeTimestampRow)
    (subject formula head fTail fTh fTt sf1 sf2 result : Noun)
    (reqs : List (ServiceReq K))
    (hhead : formulaHead formula = head) (htail : formulaTail formula = fTail)
    (hth : formulaHead (formulaTail formula) = fTh)
    (htt : formulaTail (formulaTail formula) = fTt) :
    BindComputeRow z
      (skelNode (genSkelOp2 subject formula head fTail fTh fTt sf1 sf2 result)
        reqs).skel
      (renderNode z α
        {(skelNode (genSkelOp2 subject formula head fTail fTh fTt sf1 sf2 result)
            reqs) with stamp := stamp}).row := by
  have hstate :
      ({(skelNode (genSkelOp2 subject formula head fTail fTh fTt sf1 sf2 result)
          reqs) with stamp := stamp} : GenComputeRow K).skel.state =
        State.s2 := by
    simp [skelNode, genSkelOp2]
  rw [renderNode_op2_row z α _ hstate]
  simp [skelNode]
  exact genSkelOp2_bindCompute z α subject formula head fTail fTh fTt sf1 sf2
    result stamp hhead htail hth htt

theorem bind_render_op3 (z α : K) (stamp : ComputeTimestampRow)
    (subject formula head tail callSubject callFormula callResult result : Noun)
    (reqs : List (ServiceReq K))
    (hhead : formulaHead formula = head) (htail : formulaTail formula = tail) :
    BindComputeRow z
      (skelNode (genSkelOp3 subject formula head tail callSubject callFormula
          callResult result) reqs).skel
      (renderNode z α
        {(skelNode (genSkelOp3 subject formula head tail callSubject callFormula
            callResult result) reqs) with stamp := stamp}).row := by
  have hstate :
      ({(skelNode (genSkelOp3 subject formula head tail callSubject callFormula
          callResult result) reqs) with stamp := stamp} :
        GenComputeRow K).skel.state = State.s3 := by
    simp [skelNode, genSkelOp3]
  rw [renderNode_op3_row z α _ hstate]
  simp [skelNode]
  exact genSkelOp3_bindCompute z α subject formula head tail callSubject
    callFormula callResult result stamp hhead htail

theorem bind_render_op4 (z α : K) (stamp : ComputeTimestampRow)
    (subject formula head tail callSubject callFormula callResult result : Noun)
    (reqs : List (ServiceReq K))
    (hhead : formulaHead formula = head) (htail : formulaTail formula = tail) :
    BindComputeRow z
      (skelNode (genSkelOp4 subject formula head tail callSubject callFormula
          callResult result) reqs).skel
      (renderNode z α
        {(skelNode (genSkelOp4 subject formula head tail callSubject callFormula
            callResult result) reqs) with stamp := stamp}).row := by
  have hstate :
      ({(skelNode (genSkelOp4 subject formula head tail callSubject callFormula
          callResult result) reqs) with stamp := stamp} :
        GenComputeRow K).skel.state = State.s4 := by
    simp [skelNode, genSkelOp4]
  rw [renderNode_op4_row z α _ hstate]
  simp [skelNode]
  exact genSkelOp4_bindCompute z α subject formula head tail callSubject
    callFormula callResult result stamp hhead htail

theorem bind_render_op5 (z α : K) (stamp : ComputeTimestampRow)
    (subject formula head fTail fTh fTt sf1 sf2 result : Noun)
    (reqs : List (ServiceReq K))
    (hhead : formulaHead formula = head) (htail : formulaTail formula = fTail)
    (hth : formulaHead (formulaTail formula) = fTh)
    (htt : formulaTail (formulaTail formula) = fTt) :
    BindComputeRow z
      (skelNode (genSkelOp5 subject formula head fTail fTh fTt sf1 sf2 result)
        reqs).skel
      (renderNode z α
        {(skelNode (genSkelOp5 subject formula head fTail fTh fTt sf1 sf2 result)
            reqs) with stamp := stamp}).row := by
  have hstate :
      ({(skelNode (genSkelOp5 subject formula head fTail fTh fTt sf1 sf2 result)
          reqs) with stamp := stamp} : GenComputeRow K).skel.state =
        State.s5 := by
    simp [skelNode, genSkelOp5]
  rw [renderNode_op5_row z α _ hstate]
  simp [skelNode]
  exact genSkelOp5_bindCompute z α subject formula head fTail fTh fTt sf1 sf2
    result stamp hhead htail hth htt

theorem bind_render_op6 (z α : K) (stamp : ComputeTimestampRow)
    (subject formula head fTail fTh fTt fTth fTtt cond taken result : Noun)
    (reqs : List (ServiceReq K))
    (hhead : formulaHead formula = head) (htail : formulaTail formula = fTail)
    (hth : formulaHead (formulaTail formula) = fTh)
    (htt : formulaTail (formulaTail formula) = fTt)
    (htth : formulaHead (formulaTail (formulaTail formula)) = fTth)
    (httt : formulaTail (formulaTail (formulaTail formula)) = fTtt) :
    BindComputeRow z
      (skelNode (genSkelOp6 subject formula head fTail fTh fTt fTth fTtt cond
          taken result) reqs).skel
      (renderNode z α
        {(skelNode (genSkelOp6 subject formula head fTail fTh fTt fTth fTtt cond
            taken result) reqs) with stamp := stamp}).row := by
  have hstate :
      ({(skelNode (genSkelOp6 subject formula head fTail fTh fTt fTth fTtt cond
          taken result) reqs) with stamp := stamp} :
        GenComputeRow K).skel.state = State.s6 := by
    simp [skelNode, genSkelOp6]
  rw [renderNode_op6_row z α _ hstate]
  simp [skelNode]
  exact genSkelOp6_bindCompute z α subject formula head fTail fTh fTt fTth fTtt
    cond taken result stamp hhead htail hth htt htth httt

theorem bind_render_op7 (z α : K) (stamp : ComputeTimestampRow)
    (subject formula head fTail fTh fTt sb result : Noun)
    (reqs : List (ServiceReq K))
    (hhead : formulaHead formula = head) (htail : formulaTail formula = fTail)
    (hth : formulaHead (formulaTail formula) = fTh)
    (htt : formulaTail (formulaTail formula) = fTt) :
    BindComputeRow z
      (skelNode (genSkelOp7 subject formula head fTail fTh fTt sb result) reqs).skel
      (renderNode z α
        {(skelNode (genSkelOp7 subject formula head fTail fTh fTt sb result) reqs)
          with stamp := stamp}).row := by
  have hstate :
      ({(skelNode (genSkelOp7 subject formula head fTail fTh fTt sb result) reqs)
          with stamp := stamp} : GenComputeRow K).skel.state = State.s7 := by
    simp [skelNode, genSkelOp7]
  rw [renderNode_op7_row z α _ hstate]
  simp [skelNode]
  exact genSkelOp7_bindCompute z α subject formula head fTail fTh fTt sb result
    stamp hhead htail hth htt

theorem bind_render_op8 (z α : K) (stamp : ComputeTimestampRow)
    (subject formula head fTail fTh fTt sb result : Noun)
    (reqs : List (ServiceReq K))
    (hhead : formulaHead formula = head) (htail : formulaTail formula = fTail)
    (hth : formulaHead (formulaTail formula) = fTh)
    (htt : formulaTail (formulaTail formula) = fTt) :
    BindComputeRow z
      (skelNode (genSkelOp8 subject formula head fTail fTh fTt sb result) reqs).skel
      (renderNode z α
        {(skelNode (genSkelOp8 subject formula head fTail fTh fTt sb result) reqs)
          with stamp := stamp}).row := by
  have hstate :
      ({(skelNode (genSkelOp8 subject formula head fTail fTh fTt sb result) reqs)
          with stamp := stamp} : GenComputeRow K).skel.state = State.s8 := by
    simp [skelNode, genSkelOp8]
  rw [renderNode_op8_row z α _ hstate]
  simp [skelNode]
  exact genSkelOp8_bindCompute z α subject formula head fTail fTh fTt sb result
    stamp hhead htail hth htt

theorem bind_render_op9 (z α : K) (stamp : ComputeTimestampRow)
    (subject formula head fTail fTh fTt core arm result : Noun) (axis : ℕ)
    (reqs : List (ServiceReq K))
    (hhead : formulaHead formula = head) (htail : formulaTail formula = fTail)
    (hth : formulaHead (formulaTail formula) = fTh)
    (htt : formulaTail (formulaTail formula) = fTt) :
    BindComputeRow z
      (skelNode (genSkelOp9 subject formula head fTail fTh fTt core arm result
          axis) reqs).skel
      (renderNode z α
        {(skelNode (genSkelOp9 subject formula head fTail fTh fTt core arm result
            axis) reqs) with stamp := stamp}).row := by
  have hstate :
      ({(skelNode (genSkelOp9 subject formula head fTail fTh fTt core arm result
          axis) reqs) with stamp := stamp} : GenComputeRow K).skel.state =
        State.s9 := by
    simp [skelNode, genSkelOp9]
  rw [renderNode_op9_row z α _ hstate]
  simp [skelNode]
  exact genSkelOp9_bindCompute z α subject formula head fTail fTh fTt core arm
    result axis stamp hhead htail hth htt

set_option maxHeartbeats 8000000

/-! ## Generated trees bind under `renderNode` -/

/-- Every node of a successfully generated compute tree binds its rendered
    row at an arbitrary stamp -/
theorem genComputeSkeleton_inTree_bind
    (z α : K) (stamp : ComputeTimestampRow)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (u : NTree (GenComputeRow K)) (hu : InTree t u) :
    BindComputeRow z u.label.skel
      (renderNode z α {(u.label) with stamp := stamp}).row := by
  induction fuel generalizing subject formula t result u with
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
        | error _ =>
          simp [genComputeSkeleton, hL] at h
        | ok pL =>
          cases hR : genComputeSkeleton (K := K) n subject tl with
          | error _ =>
            simp [genComputeSkeleton, hL, hR] at h
          | ok pR =>
            simp [genComputeSkeleton, hL, hR] at h
            obtain ⟨rfl, rfl⟩ := h
            cases hu with
            | here =>
              exact bind_render_cons z α stamp subject (.cell lh lt) tl pL.2 pR.2 _
            | sub hs hu' =>
              simp [NTree.children] at hs
              rcases hs with rfl | rfl
              · exact ih hL _ hu'
              · exact ih hR _ hu'
      | atom op =>
        rcases nat_lt_twelve_or_ge op with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hge
        · -- OP_0
          cases tl with
          | cell _ _ =>
            simp [genComputeSkeleton] at h
          | atom ax =>
            cases hslot : Noun.slot ax subject with
            | none =>
              simp [genComputeSkeleton, hslot] at h
            | some slotR =>
              simp [genComputeSkeleton, hslot] at h
              obtain ⟨rfl, rfl⟩ := h
              cases hu with
              | here =>
                refine bind_render_op0 z α stamp subject
                  (.cell (.atom 0) (.atom ax)) (.atom 0) (.atom ax)
                  slotR ax _ ?_ ?_
                all_goals rfl
              | sub hs _ =>
                simp [NTree.children] at hs
        · -- OP_1
          simp [genComputeSkeleton] at h
          obtain ⟨rfl, rfl⟩ := h
          cases hu with
          | here =>
            exact bind_render_op1 z α stamp subject (.cell (.atom 1) tl) tl
              (.atom 1) _ (by rfl)
          | sub hs _ =>
            simp [NTree.children] at hs
        · -- OP_2
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ =>
                simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                cases hM : genComputeSkeleton (K := K) n pB.2 pC.2 with
                | error _ =>
                  simp [genComputeSkeleton, hB, hC, hM] at h
                | ok pM =>
                  simp [genComputeSkeleton, hB, hC, hM] at h
                  obtain ⟨rfl, rfl⟩ := h
                  cases hu with
                  | here =>
                    refine bind_render_op2 z α stamp subject
                      (.cell (.atom 2) (.cell b c)) (.atom 2) (.cell b c)
                      b c pB.2 pC.2 pM.2 _ ?_ ?_ ?_ ?_
                    all_goals rfl
                  | sub hs hu' =>
                    simp [NTree.children] at hs
                    rcases hs with rfl | rfl | rfl
                    · exact ih hB _ hu'
                    · exact ih hC _ hu'
                    · exact ih hM _ hu'
        · -- OP_3
          cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ =>
            simp [genComputeSkeleton, hcall] at h
          | ok p =>
            simp [genComputeSkeleton, hcall] at h
            obtain ⟨rfl, rfl⟩ := h
            cases hu with
            | here =>
              refine bind_render_op3 z α stamp subject (.cell (.atom 3) tl)
                (.atom 3) tl subject tl p.2 (Noun.wut p.2) _ ?_ ?_
              all_goals rfl
            | sub hs hu' =>
              simp [NTree.children] at hs
              cases hs
              exact ih hcall _ hu'
        · -- OP_4
          cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ =>
            simp [genComputeSkeleton, hcall] at h
          | ok p =>
            cases hlus : Noun.lus p.2 with
            | none =>
              simp [genComputeSkeleton, hcall, hlus] at h
            | some lusR =>
              simp [genComputeSkeleton, hcall, hlus] at h
              obtain ⟨rfl, rfl⟩ := h
              cases hu with
              | here =>
                refine bind_render_op4 z α stamp subject (.cell (.atom 4) tl)
                  (.atom 4) tl subject tl p.2 lusR _ ?_ ?_
                all_goals rfl
              | sub hs hu' =>
                simp [NTree.children] at hs
                cases hs
                exact ih hcall _ hu'
        · -- OP_5
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ =>
                simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                cases hu with
                | here =>
                  refine bind_render_op5 z α stamp subject
                    (.cell (.atom 5) (.cell b c)) (.atom 5) (.cell b c)
                    b c pB.2 pC.2 (Noun.tis pB.2 pC.2) _ ?_ ?_ ?_ ?_
                  all_goals rfl
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB _ hu'
                  · exact ih hC _ hu'
        · -- OP_6
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b rest =>
            cases rest with
            | atom _ =>
              simp [genComputeSkeleton] at h
            | cell c d =>
              cases hcond : genComputeSkeleton (K := K) n subject b with
              | error _ =>
                simp [genComputeSkeleton, hcond] at h
              | ok pCond =>
                cases hval : pCond.2 with
                | cell _ _ =>
                  simp [genComputeSkeleton, hcond, hval] at h
                | atom condv =>
                  cases condv with
                  | zero =>
                    cases htaken : genComputeSkeleton (K := K) n subject c with
                    | error _ =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                    | ok pTaken =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                      obtain ⟨rfl, rfl⟩ := h
                      cases hu with
                      | here =>
                        refine bind_render_op6 z α stamp subject
                          (.cell (.atom 6) (.cell b (.cell c d))) (.atom 6)
                          (.cell b (.cell c d)) b (.cell c d) c d (.atom 0) c
                          pTaken.2 _ ?_ ?_ ?_ ?_ ?_ ?_
                        all_goals rfl
                      | sub hs hu' =>
                        simp [NTree.children] at hs
                        rcases hs with rfl | rfl
                        · exact ih hcond _ hu'
                        · exact ih htaken _ hu'
                  | succ condv =>
                    cases condv with
                    | zero =>
                      cases htaken : genComputeSkeleton (K := K) n subject d with
                      | error _ =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                      | ok pTaken =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                        obtain ⟨rfl, rfl⟩ := h
                        cases hu with
                        | here =>
                          refine bind_render_op6 z α stamp subject
                            (.cell (.atom 6) (.cell b (.cell c d))) (.atom 6)
                            (.cell b (.cell c d)) b (.cell c d) c d (.atom 1) d
                            pTaken.2 _ ?_ ?_ ?_ ?_ ?_ ?_
                          all_goals rfl
                        | sub hs hu' =>
                          simp [NTree.children] at hs
                          rcases hs with rfl | rfl
                          · exact ih hcond _ hu'
                          · exact ih htaken _ hu'
                    | succ _ =>
                      simp [genComputeSkeleton, hcond, hval] at h
        · -- OP_7
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n pB.2 c with
              | error _ =>
                simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                cases hu with
                | here =>
                  refine bind_render_op7 z α stamp subject
                    (.cell (.atom 7) (.cell b c)) (.atom 7) (.cell b c)
                    b c pB.2 pC.2 _ ?_ ?_ ?_ ?_
                  all_goals rfl
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB _ hu'
                  · exact ih hC _ hu'
        · -- OP_8
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n (.cell pB.2 subject) c with
              | error _ =>
                simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                cases hu with
                | here =>
                  refine bind_render_op8 z α stamp subject
                    (.cell (.atom 8) (.cell b c)) (.atom 8) (.cell b c)
                    b c pB.2 pC.2 _ ?_ ?_ ?_ ?_
                  all_goals rfl
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB _ hu'
                  · exact ih hC _ hu'
        · -- OP_9
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell axN c =>
            cases axN with
            | cell _ _ =>
              simp [genComputeSkeleton] at h
            | atom ax =>
              cases hcore : genComputeSkeleton (K := K) n subject c with
              | error _ =>
                simp [genComputeSkeleton, hcore] at h
              | ok pCore =>
                cases hslot : Noun.slot ax pCore.2 with
                | none =>
                  simp [genComputeSkeleton, hcore, hslot] at h
                | some arm =>
                  cases hinv : genComputeSkeleton (K := K) n pCore.2 arm with
                  | error _ =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                  | ok pInv =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                    obtain ⟨rfl, rfl⟩ := h
                    cases hu with
                    | here =>
                      refine bind_render_op9 z α stamp subject
                        (.cell (.atom 9) (.cell (.atom ax) c)) (.atom 9)
                        (.cell (.atom ax) c) (.atom ax) c pCore.2 arm pInv.2 ax
                        _ ?_ ?_ ?_ ?_
                      all_goals rfl
                    | sub hs hu' =>
                      simp [NTree.children] at hs
                      rcases hs with rfl | rfl
                      · exact ih hcore _ hu'
                      · exact ih hinv _ hu'
        · -- OP_10 notROM
          simp [genComputeSkeleton] at h
        · -- OP_11 notROM
          simp [genComputeSkeleton] at h
        · -- ≥ 12 malformed
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
          simp only [genComputeSkeleton] at h
          split at h <;> first | omega | contradiction

/-- BFS rows of a generated tree bind under `renderNode` -/
theorem genComputeSkeleton_bfs_bind
    (z α : K) (stamp : ComputeTimestampRow)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    {n : NTree (GenComputeRow K)}
    (hn : n ∈ bfsForest [t]) :
    BindComputeRow z n.label.skel
      (renderNode z α {(n.label) with stamp := stamp}).row := by
  have hin : InTree t n := by
    have := (mem_bfsForest [t] n).mp hn
    obtain ⟨c, hc, hct⟩ := this
    simp at hc
    subst c
    exact hct
  exact genComputeSkeleton_inTree_bind z α stamp h n hin

theorem genComputeSkeleton_inTree_bind_own
    (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (u : NTree (GenComputeRow K)) (hu : InTree t u) :
    BindComputeRow z u.label.skel (renderNode z α u.label).row := by
  simpa using genComputeSkeleton_inTree_bind z α u.label.stamp h u hu

/-- BFS-assigned labels bind under `renderNode` at the assigned stamp. -/
theorem genComputeSkeleton_bfsLabelAt_bind
    (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    {i : ℕ} (hi : i ∈ List.range' 1 (bfsForest [t]).length) :
    BindComputeRow z (bfsLabelAt t i).skel
      (renderNode z α (bfsLabelAt t i)).row := by
  have hi' := lt_bfsRows_of_mem_range' hi
  have hlen : i - 1 < (bfsForest [t]).length := by
    simpa [bfsRows_length] using hi'
  have hmem : (bfsForest [t])[i - 1] ∈ bfsForest [t] := List.getElem_mem hlen
  have hlbl : (bfsForest [t])[i - 1].label = (bfsRows t)[i - 1] := by
    simp [bfsRows]
  rw [bfsLabelAt_eq t i hi']
  simpa [hlbl] using
    genComputeSkeleton_bfs_bind z α
      (stampOfAcc (bfsRows t)[i - 1].skel.state (accAt t (i - 1))) h hmem

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_inTree_bind
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_bfs_bind
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_bfsLabelAt_bind
