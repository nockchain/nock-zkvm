/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierAMemWeb.lean

  Memory-row web for the generated annotated forest.

  `eqBlk` on halt / decompose / read / verify is independent of the LogUp
  pair and holds on the annotated constructors.  Halt and decompose already
  satisfy `interV` because the builder writes `ipre = icur`.  Live
  `read_root` / `verify_child` rows need the BFS LogUp threader
  (`threadPubs`): the generic builder hardcodes `ipre = icur = 0`, which
  cannot inhabit `icur − ipre = pole⁻¹`.  The threader does not edit
  `Gen.lean`; it only fills the accumulator columns the paper's `V_mem`
  reads.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMem
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMem
import Nock.NockVMROM.Thm54.TraceGen.GenTierAComputeLink
import Nock.NockVMROM.Thm54.TraceGen.GenTierAConfig
import Nock.NockVMROM.Thm54.TraceGen.GenTierAConfig769
import Nock.NockVMROM.Thm54.Language

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun
open Nock.NockVMROM.Thm54
open MemoryTable

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## Challenge alignment -/

theorem memInputs_eq_challenges (z α : K)
    (v : ChallengeVector K) (hv : v =
      { a := 0, b := 0, c := 0, α := α, z := z, β := 0, γ := 0, lam := lmb }) :
    v.memoryInputs = memInputs z := by
  subst hv
  rfl

/-! ## `eqBlk` on annotated constructors -/

theorem op9HaltPub_eqBlk (z : K) (a : ℕ) :
    eqBlkE lmb (memInputs z) (op9HaltPub (encC z) a) := by
  refine eqBlkE_of_eqBlk (by simp [op9HaltPub]) (fun h => (h rfl).elim) ?_
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp [op9HaltPub, memInputs, encC_eq, GlobalCarryRecognizer.enc_atom,
      ComputeTable.FP.atomFP]
  · simp [op9HaltPub, encC_eq, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]

theorem op9HaltPub_Vmem (z : K) (a : ℕ) :
    VmemE lmb (memInputs z) (op9HaltPub (encC z) a) :=
  vmemE_of rfl (op9HaltPub_eqBlk z a) rfl

theorem annotatedDecPub_eqBlk (z : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0)
    (head tail : Noun) (lcCell rcCell : Cell K)
    (lcSt rcSt : MState) (ipre icur : K)
    (hlc : lcCell.noun = encC z head) (hrc : rcCell.noun = encC z tail) :
    eqBlkE lmb (memInputs z)
      (annotatedDecPub (encC z) (.cell head tail) head tail
        lcCell rcCell lcSt rcSt ipre icur lmb) := by
  refine eqBlkE_of_eqBlk (by simp [annotatedDecPub]) (fun _ => by simp [annotatedDecPub, Pub.lambda]) ?_
  refine ⟨?_, rfl, ?_, rfl⟩
  · simp [annotatedDecPub, memInputs, hlc, hrc, encC_eq]
    exact GlobalCarryRecognizer.enc_cons hz head tail
  · simp [annotatedDecPub]

theorem annotatedDecPub_interV (z : K)
    (head tail : Noun) (lcCell rcCell : Cell K)
    (lcSt rcSt : MState) {ipre icur : K} (h : ipre = icur) :
    interV (memInputs z)
      (annotatedDecPub (encC z) (.cell head tail) head tail
        lcCell rcCell lcSt rcSt ipre icur lmb) := by
  simpa [interV, annotatedDecPub] using h.symm

theorem annotatedDecPub_Vmem (z : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0)
    (head tail : Noun) (lcCell rcCell : Cell K)
    (lcSt rcSt : MState) {ipre icur : K} (hacc : ipre = icur)
    (hlc : lcCell.noun = encC z head) (hrc : rcCell.noun = encC z tail) :
    VmemE lmb (memInputs z)
      (annotatedDecPub (encC z) (.cell head tail) head tail
        lcCell rcCell lcSt rcSt ipre icur lmb) :=
  vmemE_of rfl
    (annotatedDecPub_eqBlk z hz htwo head tail lcCell rcCell lcSt rcSt ipre icur hlc hrc)
    (annotatedDecPub_interV z head tail lcCell rcCell lcSt rcSt hacc)

theorem annotatedReadPub_eqBlk (z : K) (root child : Noun) (ax : ℕ) (ts : K)
    (lcCell : Cell K) (ipre icur : K) (hlc : lcCell.noun = encC z root) :
    eqBlkE lmb (memInputs z)
      (annotatedReadPub (encC z) root child ax ts lcCell ipre icur lmb) :=
  annotatedReadPub_eqBlkE _ _ root child ax ts lcCell ipre icur hlc

theorem annotatedVerifyPub_eqBlk (z : K) (root child : Noun) (ax : ℕ) (ts : K)
    (lcCell : Cell K) (ipre icur : K) (hlc : lcCell.noun = encC z child) :
    eqBlkE lmb (memInputs z)
      (annotatedVerifyPub (encC z) root child ax ts lcCell ipre icur lmb) := by
  refine eqBlkE_of_eqBlk (by simp [annotatedVerifyPub]) (fun _ => by simp [annotatedVerifyPub,
      Pub.lambda]) ?_
  simp [eqBlk, annotatedVerifyPub, hlc, MemoryTable.pwScaleExp, Pub.lambda, Pub.cprime]

/-! ## Root `eqBlk` of a paper-fan-out noun walk -/

theorem genAnnotatedNounWalk_root_eqBlk (z : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    ∀ n : Noun,
      eqBlkE lmb (memInputs z)
        (genAnnotatedNounWalk (encC z) z lmb n).1.label.row.2.2
  | .atom a => by
      simp [genAnnotatedNounWalk, gMemRow9]
      exact op9HaltPub_eqBlk z a
  | .cell h t => by
      simp [genAnnotatedNounWalk, gMemRow9]
      exact annotatedDecPub_eqBlk z hz htwo h t
        (genAnnotatedNounWalk (encC z) z lmb h).2
        (genAnnotatedNounWalk (encC z) z lmb t).2
        (nounWalkRootState h) (nounWalkRootState t) 0 0
        (genAnnotatedNounWalk_pt_noun (encC z) z h)
        (genAnnotatedNounWalk_pt_noun (encC z) z t)

theorem genAnnotatedNounWalk_all_eqBlk (z : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    ∀ n : Noun, ∀ t, InTree (genAnnotatedNounWalk (encC z) z lmb n).1 t →
      eqBlkE lmb (memInputs z) t.label.row.2.2
  | .atom a, t, ht => by
      cases ht with
      | here => exact genAnnotatedNounWalk_root_eqBlk z hz htwo (.atom a)
      | sub hs _ =>
          simp [genAnnotatedNounWalk, NTree.children] at hs
  | .cell h tl, t, ht => by
      cases ht with
      | here => exact genAnnotatedNounWalk_root_eqBlk z hz htwo (.cell h tl)
      | sub hs ht' =>
          have hcs :
              (genAnnotatedNounWalk (encC z) z lmb (.cell h tl)).1.children =
                [(genAnnotatedNounWalk (encC z) z lmb h).1,
                 (genAnnotatedNounWalk (encC z) z lmb tl).1] := by
            simp [genAnnotatedNounWalk]
          rw [hcs] at hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · exact genAnnotatedNounWalk_all_eqBlk z hz htwo h t ht'
          · exact genAnnotatedNounWalk_all_eqBlk z hz htwo tl t ht'

theorem genAnnotatedVerify_root_eqBlk (z : K) (root child : Noun)
    (ax : ℕ) (ts : K) (recordExp : ℕ) :
    eqBlkE lmb (memInputs z)
      (genAnnotatedVerify (encC z) z lmb root child ax ts recordExp).1.label.row.2.2 := by
  simp [genAnnotatedVerify, gMemRow9]
  exact annotatedVerifyPub_eqBlk z root child ax ts
    (genAnnotatedNounWalk (encC z) z lmb child).2 0 0
    (genAnnotatedNounWalk_pt_noun (encC z) z child)

theorem genAnnotatedVerify_all_eqBlk (z : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    ∀ t, InTree (genAnnotatedVerify (encC z) z lmb root child ax ts recordExp).1 t →
      eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro t ht
  cases ht with
  | here => exact genAnnotatedVerify_root_eqBlk z root child ax ts recordExp
  | sub hs ht' =>
      have hcs :
          (genAnnotatedVerify (encC z) z lmb root child ax ts recordExp).1.children =
            [(genAnnotatedNounWalk (encC z) z lmb child).1] := by
        simp [genAnnotatedVerify]
      rw [hcs] at hs
      simp only [List.mem_singleton] at hs
      subst hs
      exact genAnnotatedNounWalk_all_eqBlk z hz htwo child t ht'

/-! ## Axis-2/3 annotated record trees -/

theorem genAnnotatedDescent_pt_noun (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ) :
    (genAnnotatedDescent E z lmb root child recAxis ts recordExp
      currentNoun remainingAxis).2.noun =
      if remainingAxis < 2 then E child else E currentNoun := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n _ih =>
    unfold genAnnotatedDescent
    split
    · simp [genAnnotatedVerify, annotatedVerifyPub]
    · rename_i hge
      split <;> simp [annotatedDecPub, hge]

theorem genAnnotatedRecordTree_root_eqBlk (z : K) (α : K)
    (root child : Noun) (axis : ℕ) (recordExp : ℕ) (hax : ¬ axis < 2) :
    eqBlkE lmb (memInputs z)
      (genAnnotatedRecordTree (encC z) z α lmb root child axis recordExp).label.row.2.2 := by
  simp [genAnnotatedRecordTree, gMemRow9]
  refine annotatedReadPub_eqBlk z root child axis (α ^ recordExp) _ 0 0 ?_
  have h := genAnnotatedDescent_pt_noun (lmb := lmb) (encC z) z root child axis
    (α ^ recordExp) recordExp root axis
  simp [hax] at h
  exact h

theorem genAnnotatedRecordTree_axis2_all_eqBlk (z : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0) (α : K) (hd tl : Noun) (e : ℕ) :
    ∀ t, InTree (genAnnotatedRecordTree (encC z) z α lmb (.cell hd tl) hd 2 e) t →
      eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro t ht
  unfold genAnnotatedRecordTree at ht
  unfold genAnnotatedDescent at ht
  simp only [show ¬((2 : ℕ) < 2) from by omega, formulaHead, formulaTail,
    axisTopBit_two, axisRest_two, Bool.false_eq_true, ↓reduceIte] at ht
  unfold genAnnotatedDescent at ht
  simp only [show (1 : ℕ) < 2 from by omega, ite_true,
    genAnnotatedVerify, List.cons_append, List.nil_append] at ht
  cases ht with
  | here =>
      simp [gMemRow9]
      refine annotatedReadPub_eqBlk z (.cell hd tl) hd 2 (α ^ e) _ 0 0 ?_
      simp [annotatedDecPub]
  | sub hs ht1 =>
      simp only [NTree.children, List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs
      cases ht1 with
      | here =>
          simp [gMemRow9]
          exact annotatedDecPub_eqBlk z hz htwo hd tl _ _ _ _ 0 0
            (by simp [annotatedVerifyPub, genAnnotatedNounWalk_pt_noun])
            (genAnnotatedNounWalk_pt_noun (encC z) z tl)
      | sub hs2 ht2 =>
          simp only [NTree.children, List.mem_cons, List.not_mem_nil, or_false] at hs2
          rcases hs2 with rfl | rfl
          · exact genAnnotatedVerify_all_eqBlk z hz htwo
              (.cell hd tl) hd 2 (α ^ e) e t ht2
          · exact genAnnotatedNounWalk_all_eqBlk z hz htwo tl t ht2

theorem genAnnotatedRecordTree_axis3_all_eqBlk (z : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0) (α : K) (hd tl : Noun) (e : ℕ) :
    ∀ t, InTree (genAnnotatedRecordTree (encC z) z α lmb (.cell hd tl) tl 3 e) t →
      eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro t ht
  unfold genAnnotatedRecordTree at ht
  unfold genAnnotatedDescent at ht
  simp only [show ¬((3 : ℕ) < 2) from by omega, formulaHead, formulaTail,
    axisTopBit_three, axisRest_three, ↓reduceIte] at ht
  unfold genAnnotatedDescent at ht
  simp only [show (1 : ℕ) < 2 from by omega, ite_true,
    genAnnotatedVerify, List.cons_append, List.nil_append] at ht
  cases ht with
  | here =>
      simp [gMemRow9, axisZeroBits_three]
      exact annotatedReadPub_eqBlk z (.cell hd tl) tl 3 (α ^ e) _ 0 0
        (by simp [annotatedDecPub])
  | sub hs ht1 =>
      simp only [NTree.children, List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs
      cases ht1 with
      | here =>
          simp [gMemRow9]
          exact annotatedDecPub_eqBlk z hz htwo hd tl _ _ _ _ 0 0
            (genAnnotatedNounWalk_pt_noun (encC z) z hd)
            (by simp [annotatedVerifyPub, genAnnotatedNounWalk_pt_noun])
      | sub hs2 ht2 =>
          simp only [NTree.children, List.mem_cons, List.not_mem_nil, or_false] at hs2
          rcases hs2 with rfl | rfl
          · exact genAnnotatedNounWalk_all_eqBlk z hz htwo hd t ht2
          · exact genAnnotatedVerify_all_eqBlk z hz htwo
              (.cell hd tl) tl 3 (α ^ e) e t ht2

theorem genAnnotatedRecordTree_axis2_bfs_eqBlk (z : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0) (α : K) (hd tl : Noun) (e : ℕ) :
    ∀ t ∈ bfsForest [genAnnotatedRecordTree (encC z) z α lmb (.cell hd tl) hd 2 e],
      eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro t ht
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ t).mp ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  subst c
  exact genAnnotatedRecordTree_axis2_all_eqBlk z hz htwo α hd tl e t hin

theorem genAnnotatedRecordTree_axis3_bfs_eqBlk (z : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0) (α : K) (hd tl : Noun) (e : ℕ) :
    ∀ t ∈ bfsForest [genAnnotatedRecordTree (encC z) z α lmb (.cell hd tl) tl 3 e],
      eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro t ht
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ t).mp ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  subst c
  exact genAnnotatedRecordTree_axis3_all_eqBlk z hz htwo α hd tl e t hin

theorem genAnnotatedDescentCont_axis2_all_eqBlk (z : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0)
    (cont : List (NTree (GenMemoryRow K))) (contCell : Cell K)
    (contState : MState) (hd tl : Noun)
    (hlc : contCell.noun = encC z hd)
    (hcont : ∀ u ∈ cont, ∀ t, InTree u t →
      eqBlkE lmb (memInputs z) t.label.row.2.2) :
    ∀ u ∈ (genAnnotatedDescentCont (encC z) z lmb cont contCell contState
        (.cell hd tl) 2).1,
      ∀ t, InTree u t →
        eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro u hu t ht
  rw [genAnnotatedDescentCont_axis2] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  subst u
  cases ht with
  | here =>
      simp [gMemRow9]
      exact annotatedDecPub_eqBlk z hz htwo hd tl contCell
        (genAnnotatedNounWalk (encC z) z lmb tl).2 _ _ 0 0 hlc
        (genAnnotatedNounWalk_pt_noun (encC z) z tl)
  | sub hs ht' =>
      simp only [NTree.children] at hs
      rw [List.mem_append] at hs
      rcases hs with hL | hR
      · exact hcont _ hL t ht'
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
        subst hR
        exact genAnnotatedNounWalk_all_eqBlk z hz htwo tl t ht'

theorem genAnnotatedDescentCont_axis3_all_eqBlk (z : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0)
    (cont : List (NTree (GenMemoryRow K))) (contCell : Cell K)
    (contState : MState) (hd tl : Noun)
    (hrc : contCell.noun = encC z tl)
    (hcont : ∀ u ∈ cont, ∀ t, InTree u t →
      eqBlkE lmb (memInputs z) t.label.row.2.2) :
    ∀ u ∈ (genAnnotatedDescentCont (encC z) z lmb cont contCell contState
        (.cell hd tl) 3).1,
      ∀ t, InTree u t →
        eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro u hu t ht
  rw [genAnnotatedDescentCont_axis3] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  subst u
  cases ht with
  | here =>
      simp [gMemRow9]
      exact annotatedDecPub_eqBlk z hz htwo hd tl
        (genAnnotatedNounWalk (encC z) z lmb hd).2 contCell _ _ 0 0
        (genAnnotatedNounWalk_pt_noun (encC z) z hd) hrc
  | sub hs ht' =>
      simp only [NTree.children] at hs
      rw [List.mem_append] at hs
      rcases hs with hL | hR
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
        subst hL
        exact genAnnotatedNounWalk_all_eqBlk z hz htwo hd t ht'
      · exact hcont _ hR t ht'

theorem genAnnotatedChainedInner_one_axis2_all_eqBlk (z : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0) (α : K) (prevRoot : Noun) (hd2 tl2 : Noun)
    (ePrev e2 : ℕ) :
    ∀ u ∈ (genAnnotatedChainedInner (encC z) z α lmb
        ⟨prevRoot, .cell hd2 tl2, 3, ePrev⟩
        [⟨.cell hd2 tl2, hd2, 2, e2⟩]).1,
      ∀ t, InTree u t →
        eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro u hu t ht
  unfold genAnnotatedChainedInner at hu
  simp only [genAnnotatedChainedInner_nil, chainedInnerRootState] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  subst u
  cases ht with
  | here =>
      simp [gMemRow9]
      refine annotatedReadPub_eqBlk z (.cell hd2 tl2) hd2 2 (α ^ e2) _ 0 0 ?_
      simp [annotatedVerifyPub]
  | sub hs ht1 =>
      simp only [NTree.children, List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs
      cases ht1 with
      | here =>
          simp [gMemRow9]
          refine annotatedVerifyPub_eqBlk z prevRoot (.cell hd2 tl2) 3
            (α ^ ePrev) _ 0 0 ?_
          simp [genAnnotatedDescentCont_axis2, annotatedDecPub]
      | sub hs2 ht2 =>
          refine genAnnotatedDescentCont_axis2_all_eqBlk z hz htwo
            [(genAnnotatedVerify (encC z) z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).1]
            (genAnnotatedVerify (encC z) z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).2
            .verify_child hd2 tl2 ?_ ?_ _ ?_ t ht2
          · simp [genAnnotatedVerify_pt_noun]
          · intro v hv w hw
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            subst v
            exact genAnnotatedVerify_all_eqBlk z hz htwo
              (.cell hd2 tl2) hd2 2 (α ^ e2) e2 w hw
          · simp only [NTree.children] at hs2
            exact hs2

theorem genAnnotatedChainedTree_axis3_axis2_all_eqBlk (z : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0) (α : K) (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    ∀ t, genAnnotatedChainedTree (encC z) z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩] = some t →
      ∀ u, InTree t u →
        eqBlkE lmb (memInputs z) u.label.row.2.2 := by
  intro t ht u hu
  unfold genAnnotatedChainedTree at ht
  simp only [chainedInnerRootState] at ht
  injection ht with ht
  subst t
  cases hu with
  | here =>
      simp [gMemRow9, axisZeroBits_three]
      refine annotatedReadPub_eqBlk z (.cell hd1 (.cell hd2 tl2))
        (.cell hd2 tl2) 3 (α ^ e1) _ 0 0 ?_
      simp [genAnnotatedDescentCont_axis3, annotatedDecPub]
  | sub hs hu' =>
      simp only [NTree.children] at hs
      exact genAnnotatedDescentCont_axis3_all_eqBlk z hz htwo
        (genAnnotatedChainedInner (encC z) z α lmb
          ⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩
          [⟨.cell hd2 tl2, hd2, 2, e2⟩]).1
        (genAnnotatedChainedInner (encC z) z α lmb
          ⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩
          [⟨.cell hd2 tl2, hd2, 2, e2⟩]).2
        .read_root hd1 (.cell hd2 tl2)
        (by simpa [genAnnotatedChainedInner_one_pt_noun])
        (fun v hv w hw =>
          genAnnotatedChainedInner_one_axis2_all_eqBlk z hz htwo α
            (.cell hd1 (.cell hd2 tl2)) hd2 tl2 e1 e2 v hv w hw)
        _ hs u hu'

theorem genRowMemForest_singleton_axis3_eqBlk (z : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0) (α : K) (hd tl : Noun) (e : ℕ) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb [⟨.cell hd tl, tl, 3, e⟩],
      ∀ t, InTree u t →
        eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro u hu t ht
  simp [genRowMemForest_singleton] at hu
  subst u
  exact genAnnotatedRecordTree_axis3_all_eqBlk z hz htwo α hd tl e t ht

theorem genRowMemForest_singleton_axis2_eqBlk (z : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0) (α : K) (hd tl : Noun) (e : ℕ) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb [⟨.cell hd tl, hd, 2, e⟩],
      ∀ t, InTree u t →
        eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro u hu t ht
  simp [genRowMemForest_singleton] at hu
  subst u
  exact genAnnotatedRecordTree_axis2_all_eqBlk z hz htwo α hd tl e t ht

theorem genRowMemForest_chain32_eqBlk (z : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0) (α : K) (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩],
      ∀ t, InTree u t →
        eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro u hu t ht
  unfold genRowMemForest at hu
  simp only at hu
  cases h : genAnnotatedChainedTree (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none =>
    simp [genAnnotatedChainedTree] at h
  | some tree =>
    simp [h] at hu
    subst u
    exact genAnnotatedChainedTree_axis3_axis2_all_eqBlk z hz htwo α
      hd1 hd2 tl2 e1 e2 tree h t ht

theorem genRowMemForest_three_chain32_eqBlk (z : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0) (α : K) (hd1 hd2 tl2 hd3 tl3 : Noun)
    (e1 e2 e3 : ℕ) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩,
       ⟨.cell hd3 tl3, hd3, 2, e3⟩],
      ∀ t, InTree u t →
        eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro u hu t ht
  unfold genRowMemForest at hu
  cases h : genAnnotatedChainedTree (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none =>
    simp [genAnnotatedChainedTree] at h
  | some tree =>
    simp [h, List.mem_append, List.mem_singleton] at hu
    rcases hu with hmem | hmem
    · rw [hmem] at ht
      exact genAnnotatedChainedTree_axis3_axis2_all_eqBlk z hz htwo α
        hd1 hd2 tl2 e1 e2 tree h t ht
    · rw [hmem] at ht
      exact genAnnotatedRecordTree_axis2_all_eqBlk z hz htwo α hd3 tl3 e3 t ht

/-! ## Assigned `dotTree` forest -/

theorem genMemForestFromTree_of_rowEqBlk (z α : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0) (t : NTree (GenComputeRow K))
    (H : ∀ n, InTree t n →
      ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
        ∀ v, InTree u v →
        eqBlkE lmb (memInputs z) v.label.row.2.2)
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ genMemForestFromTree (encC z) z α lmb t)
    (v : NTree (GenMemoryRow K)) (hv : InTree u v) :
    eqBlkE lmb (memInputs z) v.label.row.2.2 := by
  suffices ∀ N t,
      NTree.size t ≤ N →
      (∀ n, InTree t n →
        ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
          ∀ v, InTree u v →
        eqBlkE lmb (memInputs z) v.label.row.2.2) →
      ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
        ∀ v, InTree u v →
        eqBlkE lmb (memInputs z) v.label.row.2.2 from
    this (NTree.size t) t le_rfl H u hu v hv
  intro N
  induction N with
  | zero =>
    intro t ht H u hu v hv
    cases t with
    | node g cs =>
      simp [NTree.size] at ht
  | succ N ih =>
    intro t ht H u hu v hv
    cases t with
    | node g cs =>
      simp [genMemForestFromTree] at hu
      rcases hu with hu | hu
      · exact H (.node g cs) (InTree.here _) u hu v hv
      · have recList :
            ∀ cs', (∀ c ∈ cs', c ∈ cs) →
              (∀ t ∈ cs', NTree.size t ≤ N) →
              (∀ t ∈ cs', ∀ n, InTree t n →
                ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
                  ∀ v, InTree u v →
        eqBlkE lmb (memInputs z) v.label.row.2.2) →
              ∀ u ∈ genMemForestFromList (encC z) z α lmb cs',
                ∀ v, InTree u v →
        eqBlkE lmb (memInputs z) v.label.row.2.2 := by
          intro cs' hsub hsz H' u' hu' v' hv'
          induction cs' generalizing u' v' with
          | nil => simp [genMemForestFromList] at hu'
          | cons c rest ihcs =>
            simp [genMemForestFromList] at hu'
            rcases hu' with hu' | hu'
            · exact ih c (hsz c (by simp))
                (fun n hn => H' c (by simp) n hn) u' hu' v' hv'
            · refine ihcs ?_ ?_ ?_ u' hu' v' hv'
              · intro c' hc'; exact hsub c' (List.mem_cons_of_mem _ hc')
              · intro t htt; exact hsz t (List.mem_cons_of_mem _ htt)
              · intro t htt; exact H' t (List.mem_cons_of_mem _ htt)
        refine recList cs (fun _ h => h) ?_
          (fun t ht n hn => H n (InTree.sub ht hn)) u hu v hv
        intro c hc
        have hin : NTree.size c ∈ cs.map NTree.size := List.mem_map.mpr ⟨c, hc, rfl⟩
        have hsum : NTree.size c ≤ (cs.map NTree.size).sum := List.le_sum_of_mem hin
        simp [NTree.size] at ht
        omega

theorem dotAssigned_rowEqBlk (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0)
    (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (dotTree (K := K))) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      ∀ v, InTree u v →
        eqBlkE lmb (memInputs z) v.label.row.2.2 := by
  have hnF : n ∈ bfsForest [bfsAssign (dotTree (K := K))] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab := bfsAssign_bfsForest_labels (dotTree (K := K))
  have hmem : n.label ∈ (bfsForest [bfsAssign (dotTree (K := K))]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [hlab] at hmem
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨i, hi, hieq⟩
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTree (K := K))) hi
  rw [← hieq, extractNodeReqs, bfsLabelAt_requests (dotTree (K := K)) i hi']
  rcases dot_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hget : (bfsRows (dotTree (K := K)))[0] = (dotTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 1).stamp 0 g.requests) hget]
    simp [dotTree, skelNode, extractNodeReqsAux_cons3]
    exact genRowMemForest_three_chain32_eqBlk z hz htwo α (.atom 6) dotCondFormula
      dotBranchPair dotThenFormula dotElseFormula
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 1)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 2)
  · have hget : (bfsRows (dotTree (K := K)))[1] = (dotCondTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 2).stamp 0 g.requests) hget]
    simp [dotCondTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_eqBlk z hz htwo α (.atom 1) (.atom 0) (getRecordExp (bfsLabelAt (dotTree (K := K)) 2).stamp 0)
  · have hget : (bfsRows (dotTree (K := K)))[2] = (dotOp2Tree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 3).stamp 0 g.requests) hget]
    simp [dotOp2Tree, skelNode, extractNodeReqsAux_cons2]
    exact genRowMemForest_chain32_eqBlk z hz htwo α (.atom 2) dotOp2B dotOp2C
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 3).stamp 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 3).stamp 1)
  · have hget : (bfsRows (dotTree (K := K)))[3] = (dotOp1BTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 4).stamp 0 g.requests) hget]
    simp [dotOp1BTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_eqBlk z hz htwo α (.atom 1)
        (.cell (.atom 0) (.atom 1))
        (getRecordExp (bfsLabelAt (dotTree (K := K)) 4).stamp 0)
  · have hget : (bfsRows (dotTree (K := K)))[4] = (dotOp1CTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 5).stamp 0 g.requests) hget]
    simp [dotOp1CTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_eqBlk z hz htwo α (.atom 1) dotOp9Formula (getRecordExp (bfsLabelAt (dotTree (K := K)) 5).stamp 0)
  · have hget : (bfsRows (dotTree (K := K)))[5] = (dotOp9Tree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 6).stamp 0 g.requests) hget]
    simp [dotOp9Tree, skelNode, extractNodeReqsAux_cons3]
    exact genRowMemForest_three_chain32_eqBlk z hz htwo α (.atom 9) (.atom 2)
      dotCoreFormula dotElem0 dotElem1
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 1)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 2)
  · have hget : (bfsRows (dotTree (K := K)))[6] = (dotOp9CoreTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 7).stamp 0 g.requests) hget]
    simp [dotOp9CoreTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_eqBlk z hz htwo α (.atom 1) dotCore (getRecordExp (bfsLabelAt (dotTree (K := K)) 7).stamp 0)
  · have hget : (bfsRows (dotTree (K := K)))[7] = (dotOp9InvokeTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 8).stamp 0 g.requests) hget]
    simp [dotOp9InvokeTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_eqBlk z hz htwo α (.atom 1) (.atom 3) (getRecordExp (bfsLabelAt (dotTree (K := K)) 8).stamp 0)

theorem dotMemForest_eqBlk (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTree (K := K))),
      ∀ v, InTree u v →
        eqBlkE lmb (memInputs z) v.label.row.2.2 :=
  fun u hu v hv =>
    genMemForestFromTree_of_rowEqBlk z α hz htwo _ (dotAssigned_rowEqBlk z α hz htwo)
      u hu v hv

theorem dotMemForest_bfs_eqBlk (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    ∀ t ∈ bfsForest (genMemForestFromTree (encC z) z α lmb
        (bfsAssign (dotTree (K := K)))),
      eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  exact dotMemForest_eqBlk z α hz htwo u hu t hin

theorem dotAssigned_rowEqBlk_air (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0)
    (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (dotTreeAir (K := K))) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      ∀ v, InTree u v →
        eqBlkE lmb (memInputs z) v.label.row.2.2 := by
  have hnF : n ∈ bfsForest [bfsAssign (dotTreeAir (K := K))] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab := bfsAssign_bfsForest_labels (dotTreeAir (K := K))
  have hmem : n.label ∈ (bfsForest [bfsAssign (dotTreeAir (K := K))]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [hlab] at hmem
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨i, hi, hieq⟩
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTreeAir (K := K))) hi
  rw [← hieq, extractNodeReqs, bfsLabelAt_requests (dotTreeAir (K := K)) i hi']
  rcases dot_air_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hget : (bfsRows (dotTreeAir (K := K)))[0] = (dotTreeAir (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 0 g.requests) hget]
    simp [dotTreeAir, skelNode, extractNodeReqsAux_cons3]
    exact genRowMemForest_three_chain32_eqBlk z hz htwo α (.atom 6) dotCondFormula
      dotBranchPair dotThenFormula dotElseFormula
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 1)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 2)
  · have hget : (bfsRows (dotTreeAir (K := K)))[1] = (dotOp2Tree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 0 g.requests) hget]
    simp [dotOp2Tree, skelNode, extractNodeReqsAux_cons2]
    exact genRowMemForest_chain32_eqBlk z hz htwo α (.atom 2) dotOp2B dotOp2C
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 1)
  · have hget : (bfsRows (dotTreeAir (K := K)))[2] = (dotCondTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 3).stamp 0 g.requests) hget]
    simp [dotCondTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_eqBlk z hz htwo α (.atom 1) (.atom 0) (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 3).stamp 0)
  · have hget : (bfsRows (dotTreeAir (K := K)))[3] = (dotOp1BTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 4).stamp 0 g.requests) hget]
    simp [dotOp1BTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_eqBlk z hz htwo α (.atom 1)
        (.cell (.atom 0) (.atom 1))
        (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 4).stamp 0)
  · have hget : (bfsRows (dotTreeAir (K := K)))[4] = (dotOp1CTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 5).stamp 0 g.requests) hget]
    simp [dotOp1CTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_eqBlk z hz htwo α (.atom 1) dotOp9Formula (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 5).stamp 0)
  · have hget : (bfsRows (dotTreeAir (K := K)))[5] = (dotOp9Tree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 0 g.requests) hget]
    simp [dotOp9Tree, skelNode, extractNodeReqsAux_cons3]
    exact genRowMemForest_three_chain32_eqBlk z hz htwo α (.atom 9) (.atom 2)
      dotCoreFormula dotElem0 dotElem1
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 1)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 2)
  · have hget : (bfsRows (dotTreeAir (K := K)))[6] = (dotOp9CoreTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 7).stamp 0 g.requests) hget]
    simp [dotOp9CoreTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_eqBlk z hz htwo α (.atom 1) dotCore (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 7).stamp 0)
  · have hget : (bfsRows (dotTreeAir (K := K)))[7] = (dotOp9InvokeTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 8).stamp 0 g.requests) hget]
    simp [dotOp9InvokeTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_eqBlk z hz htwo α (.atom 1) (.atom 3) (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 8).stamp 0)

theorem dotMemForest_eqBlk_air (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTreeAir (K := K))),
      ∀ v, InTree u v →
        eqBlkE lmb (memInputs z) v.label.row.2.2 :=
  fun u hu v hv =>
    genMemForestFromTree_of_rowEqBlk z α hz htwo _ (dotAssigned_rowEqBlk_air z α hz htwo)
      u hu v hv

theorem dotMemForest_bfs_eqBlk_air (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    ∀ t ∈ bfsForest (genMemForestFromTree (encC z) z α lmb
        (bfsAssign (dotTreeAir (K := K)))),
      eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  exact dotMemForest_eqBlk_air z α hz htwo u hu t hin

/-! ## BFS forest relabel -/

/-- Replace the labels of the current BFS level, leaving child pointers intact. -/
def zipLevel {α} : List (NTree α) → List α → List (NTree α)
  | [], _ => []
  | ts, [] => ts
  | .node _ cs :: ts, lbl :: labs =>
      .node lbl cs :: zipLevel ts labs

/-- Reattach a flattened child forest onto a level of trees, consuming
    `t.children.length` children from the front of `kids` for each tree. -/
def graft {α} : List (NTree α) → List (NTree α) → List (NTree α)
  | [], _ => []
  | .node lbl cs :: ts, kids =>
      .node lbl (kids.take cs.length) :: graft ts (kids.drop cs.length)

/-- Write a BFS-ordered label list back onto a forest of the same shape. -/
def zipBfs {α} : List (NTree α) → List α → List (NTree α)
  | [], _ => []
  | t :: rest, labs =>
      let level := zipLevel (t :: rest) labs
      let kids :=
        zipBfs ((t :: rest).flatMap NTree.children) (labs.drop (t :: rest).length)
      graft level kids
termination_by ts => totalSize ts
decreasing_by
  have h := totalSize_flatMap_children (t :: rest)
  simp only [List.length_cons] at h
  omega

omit [Field K] in
theorem zipLevel_nil {α} (labs : List α) :
    zipLevel ([] : List (NTree α)) labs = [] := rfl

omit [Field K] in
theorem zipLevel_nil_labs {α} (ts : List (NTree α)) :
    zipLevel ts ([] : List α) = ts := by
  cases ts <;> rfl

omit [Field K] in
theorem zipLevel_cons {α} (lbl lbl' : α) (cs : List (NTree α))
    (ts : List (NTree α)) (labs : List α) :
    zipLevel (.node lbl' cs :: ts) (lbl :: labs) =
      .node lbl cs :: zipLevel ts labs := rfl

omit [Field K] in
theorem zipLevel_id {α} :
    ∀ ts : List (NTree α), ∀ labs,
      labs.take ts.length = ts.map NTree.label →
      zipLevel ts labs = ts
  | [], _ => by intro _; rfl
  | .node lbl cs :: rest, [] => by
      intro h
      simp at h
  | .node lbl cs :: rest, lbl' :: labs => by
      intro h
      simp only [List.length_cons, List.take_succ_cons, List.map_cons] at h
      injection h with h1 hrest
      subst h1
      rw [zipLevel_cons, zipLevel_id rest labs hrest]

omit [Field K] in
theorem graft_nil {α} (kids : List (NTree α)) :
    graft ([] : List (NTree α)) kids = [] := rfl

omit [Field K] in
theorem graft_self {α} : ∀ ts : List (NTree α),
    graft ts (ts.flatMap NTree.children) = ts
  | [] => rfl
  | .node lbl cs :: rest => by
      simp only [graft, List.flatMap_cons, NTree.children]
      have htake : ((cs ++ rest.flatMap NTree.children).take cs.length) = cs :=
        List.take_left
      have hdrop : ((cs ++ rest.flatMap NTree.children).drop cs.length) =
          rest.flatMap NTree.children :=
        List.drop_left
      rw [htake, hdrop, graft_self rest]

omit [Field K] in
theorem zipBfs_nil {α} (labs : List α) :
    zipBfs ([] : List (NTree α)) labs = [] := by
  simp [zipBfs]

omit [Field K] in
theorem zipBfs_self {α} :
    ∀ ts : List (NTree α),
      zipBfs ts ((bfsForest ts).map NTree.label) = ts := by
  intro ts
  suffices ∀ N ts, totalSize ts ≤ N →
      zipBfs ts ((bfsForest ts).map NTree.label) = ts from
    this (totalSize ts) ts le_rfl
  intro N
  induction N with
  | zero =>
    intro ts ht
    have : ts = [] := by
      cases ts with
      | nil => rfl
      | cons t rest =>
        have : 1 ≤ t.size := by
          cases t with
          | node _ _ => simp [NTree.size]
        rw [totalSize_cons] at ht
        omega
    subst this
    exact zipBfs_nil _
  | succ N ih =>
    intro ts ht
    match ts with
    | [] => exact zipBfs_nil _
    | t :: rest =>
      have hne : t :: rest ≠ [] := List.cons_ne_nil _ _
      have hbfs := bfsForest_cons_eq (t :: rest) hne
      have hlen : (t :: rest).length =
          ((t :: rest).map NTree.label).length := by
        rw [List.length_map]
      have hid : zipLevel (t :: rest)
          ((bfsForest (t :: rest)).map NTree.label) = t :: rest := by
        refine zipLevel_id _ _ ?_
        rw [hbfs, List.map_append, hlen, List.take_left]
      have hdrop :
          ((bfsForest (t :: rest)).map NTree.label).drop (t :: rest).length =
            (bfsForest ((t :: rest).flatMap NTree.children)).map NTree.label := by
        rw [hbfs, List.map_append, hlen, List.drop_left]
      have hsz : totalSize ((t :: rest).flatMap NTree.children) ≤ N := by
        have h := totalSize_flatMap_children (t :: rest)
        simp only [List.length_cons] at h
        omega
      have hih := ih _ hsz
      simp only [zipBfs]
      rw [hid, hdrop, hih, graft_self]

omit [Field K] in
theorem take_add_eq {α} (l : List α) (m n : ℕ) :
    l.take (m + n) = l.take m ++ (l.drop m).take n := by
  induction m generalizing l with
  | zero => simp
  | succ m ih =>
    cases l with
    | nil => simp
    | cons _ xs =>
      simp [List.take_succ_cons, List.drop_succ_cons, Nat.succ_add, ih]

omit [Field K] in
theorem zipLevel_length {α} : ∀ ts : List (NTree α), ∀ labs,
    (zipLevel ts labs).length = ts.length
  | [], _ => rfl
  | t :: rest, [] => by simp [zipLevel]
  | t :: rest, _ :: labs => by
      cases t
      simp [zipLevel, zipLevel_length rest labs]

omit [Field K] in
theorem zipLevel_labels {α} :
    ∀ ts : List (NTree α), ∀ labs,
      ts.length ≤ labs.length →
      (zipLevel ts labs).map NTree.label = labs.take ts.length
  | [], labs => by intro _; simp [zipLevel]
  | _ :: _, [] => by intro h; simp at h
  | .node _ _ :: rest, lbl' :: labs => by
      intro h
      simp [zipLevel_cons, List.take_succ_cons]
      exact zipLevel_labels rest labs (by simp at h ⊢; omega)

omit [Field K] in
theorem zipLevel_children {α} :
    ∀ ts : List (NTree α), ∀ labs,
      (zipLevel ts labs).flatMap NTree.children = ts.flatMap NTree.children
  | [], _ => rfl
  | ts, [] => by rw [zipLevel_nil_labs]
  | .node _ cs :: rest, _ :: labs => by
      simp [zipLevel_cons, List.flatMap_cons, NTree.children,
        zipLevel_children rest labs]

omit [Field K] in
theorem graft_length {α} : ∀ ts kids : List (NTree α),
    (graft ts kids).length = ts.length
  | [], _ => rfl
  | t :: rest, kids => by
      cases t
      simp [graft, graft_length rest]

omit [Field K] in
theorem graft_labels {α} : ∀ ts kids : List (NTree α),
    (graft ts kids).map NTree.label = ts.map NTree.label
  | [], _ => rfl
  | .node lbl _ :: rest, kids => by simp [graft, graft_labels rest]

omit [Field K] in
theorem graft_flatMap_children {α} :
    ∀ ts kids : List (NTree α),
      (graft ts kids).flatMap NTree.children =
        kids.take (ts.flatMap NTree.children).length
  | [], kids => by simp [graft]
  | t :: rest, kids => by
      cases t with
      | node _ cs =>
        rw [graft, List.flatMap_cons, NTree.children, graft_flatMap_children rest]
        rw [List.flatMap_cons, NTree.children, List.length_append, ← take_add_eq]

omit [Field K] in
theorem zipBfs_cons {α} (t : NTree α) (rest : List (NTree α)) (labs : List α) :
    zipBfs (t :: rest) labs =
      graft (zipLevel (t :: rest) labs)
        (zipBfs ((t :: rest).flatMap NTree.children)
          (labs.drop (t :: rest).length)) := by
  simp [zipBfs]

omit [Field K] in
theorem zipBfs_length {α} (ts : List (NTree α)) (labs : List α) :
    (zipBfs ts labs).length = ts.length := by
  match ts with
  | [] => rw [zipBfs_nil]
  | t :: rest =>
    rw [zipBfs_cons, graft_length, zipLevel_length]

omit [Field K] in
theorem zipBfs_labels {α} :
    ∀ ts : List (NTree α), ∀ labs,
      labs.length = totalSize ts →
      (bfsForest (zipBfs ts labs)).map NTree.label = labs := by
  intro ts
  suffices ∀ N ts, totalSize ts ≤ N → ∀ labs,
      labs.length = totalSize ts →
      (bfsForest (zipBfs ts labs)).map NTree.label = labs from
    this (totalSize ts) ts le_rfl
  intro N
  induction N with
  | zero =>
    intro ts ht labs hlen
    have : ts = [] := by
      cases ts with
      | nil => rfl
      | cons t rest =>
        have : 1 ≤ t.size := by
          cases t with
          | node _ _ => simp [NTree.size]
        rw [totalSize_cons] at ht
        omega
    subst this
    have : labs = [] := List.eq_nil_of_length_eq_zero (by simpa [totalSize] using hlen)
    subst this
    rw [zipBfs_nil, bfsForest_nil]
    rfl
  | succ N ih =>
    intro ts ht labs hlen
    match ts with
    | [] =>
      have : labs = [] := List.eq_nil_of_length_eq_zero (by simpa [totalSize] using hlen)
      subst this
      rw [zipBfs_nil, bfsForest_nil]
      rfl
    | t :: rest =>
      have hne : zipBfs (t :: rest) labs ≠ [] := by
        intro hz
        have := congrArg List.length hz
        simp [zipBfs_length] at this
      have hbfs := bfsForest_cons_eq (zipBfs (t :: rest) labs) hne
      have hkids :
          (zipBfs (t :: rest) labs).flatMap NTree.children =
            zipBfs ((t :: rest).flatMap NTree.children)
              (labs.drop (t :: rest).length) := by
        rw [zipBfs_cons, graft_flatMap_children, zipLevel_children]
        rw [← zipBfs_length ((t :: rest).flatMap NTree.children)
          (labs.drop (t :: rest).length), List.take_length]
      have hdrop_len :
          (labs.drop (t :: rest).length).length =
            totalSize ((t :: rest).flatMap NTree.children) := by
        have hsz := totalSize_flatMap_children (t :: rest)
        simp only [List.length_drop, hlen, List.length_cons] at hsz ⊢
        omega
      have hsz : totalSize ((t :: rest).flatMap NTree.children) ≤ N := by
        have h := totalSize_flatMap_children (t :: rest)
        simp only [List.length_cons] at h
        omega
      have hih := ih ((t :: rest).flatMap NTree.children) hsz
        (labs.drop (t :: rest).length) hdrop_len
      have hle : (t :: rest).length ≤ labs.length := by
        rw [hlen]
        have := totalSize_flatMap_children (t :: rest)
        omega
      rw [hbfs, List.map_append, hkids, hih, zipBfs_cons, graft_labels,
        zipLevel_labels (t :: rest) labs hle]
      exact List.take_append_drop (t :: rest).length labs

omit [Field K] in
theorem zipLevel_map_size {α} :
    ∀ ts : List (NTree α), ∀ labs,
      (zipLevel ts labs).map NTree.size = ts.map NTree.size
  | [], _ => rfl
  | ts, [] => by rw [zipLevel_nil_labs]
  | t :: rest, _ :: labs => by
      cases t with
      | node _ cs =>
        simp [zipLevel, zipLevel_map_size rest labs, NTree.size]

omit [Field K] in
theorem zipLevel_totalSize {α} (ts : List (NTree α)) (labs : List α) :
    totalSize (zipLevel ts labs) = totalSize ts := by
  simp [totalSize, zipLevel_map_size]

omit [Field K] in
theorem graft_totalSize {α} :
    ∀ ts kids : List (NTree α),
      totalSize (graft ts kids) =
        ts.length + totalSize (kids.take (ts.flatMap NTree.children).length)
  | [], kids => by simp [graft, totalSize]
  | t :: rest, kids => by
      cases t with
      | node lbl cs =>
        rw [graft, totalSize_cons]
        have hsz : NTree.size (.node lbl (kids.take cs.length)) =
            1 + totalSize (kids.take cs.length) := by
          simp [NTree.size, totalSize]
        rw [hsz, graft_totalSize rest]
        have hlen :
            ((.node lbl cs :: rest).flatMap NTree.children).length =
              cs.length + (rest.flatMap NTree.children).length := by
          simp [List.flatMap_cons, NTree.children]
        rw [hlen, take_add_eq, totalSize_append]
        simp only [List.length_cons]
        omega

omit [Field K] in
theorem zipBfs_totalSize {α} :
    ∀ ts : List (NTree α), ∀ labs, totalSize (zipBfs ts labs) = totalSize ts := by
  intro ts labs
  suffices ∀ N ts, totalSize ts ≤ N → ∀ labs,
      totalSize (zipBfs ts labs) = totalSize ts from
    this (totalSize ts) ts le_rfl labs
  intro N
  induction N with
  | zero =>
    intro ts ht labs
    have : ts = [] := by
      cases ts with
      | nil => rfl
      | cons t rest =>
        have : 1 ≤ t.size := by
          cases t with
          | node _ _ => simp [NTree.size]
        rw [totalSize_cons] at ht
        omega
    subst this
    rw [zipBfs_nil, totalSize_nil]
  | succ N ih =>
    intro ts ht labs
    match ts with
    | [] => rw [zipBfs_nil, totalSize_nil]
    | t :: rest =>
      rw [zipBfs_cons, graft_totalSize, zipLevel_length, zipLevel_children]
      rw [← zipBfs_length ((t :: rest).flatMap NTree.children)
        (labs.drop (t :: rest).length), List.take_length]
      have hsz : totalSize ((t :: rest).flatMap NTree.children) ≤ N := by
        have h := totalSize_flatMap_children (t :: rest)
        simp only [List.length_cons] at h
        omega
      rw [ih _ hsz]
      have h := totalSize_flatMap_children (t :: rest)
      omega

/-- Rewrite only the accumulator pair.  `eqBlk` does not read these columns. -/
def setAcc (p : Pub K) (ipre icur : K) : Pub K :=
  { p with ipre := ipre, icur := icur }

theorem setAcc_st (p : Pub K) (a b : K) : (setAcc p a b).st = p.st := rfl
theorem setAcc_mem (p : Pub K) (a b : K) : (setAcc p a b).mem = p.mem := rfl
theorem setAcc_pt (p : Pub K) (a b : K) : (setAcc p a b).pt = p.pt := rfl
theorem setAcc_lc (p : Pub K) (a b : K) : (setAcc p a b).lc = p.lc := rfl
theorem setAcc_rc (p : Pub K) (a b : K) : (setAcc p a b).rc = p.rc := rfl
theorem setAcc_ipre (p : Pub K) (a b : K) : (setAcc p a b).ipre = a := rfl
theorem setAcc_icur (p : Pub K) (a b : K) : (setAcc p a b).icur = b := rfl
theorem setAcc_ver (p : Pub K) (a b : K) : (setAcc p a b).ver = p.ver := rfl

theorem encPub_setAcc (p : Pub K) (a b : K) :
    encPub lmb (setAcc p a b) = setAcc (encPub lmb p) a b := by
  unfold encPub SemanticTimestampStrategy.MemoryRowTemplate.encodeRow setAcc
  by_cases h : memoryMemRecKind p.st = .active <;> simp [h]

theorem setAcc_eqBlk_raw (inp : Inputs K) (p : Pub K) (a b : K) :
    eqBlk inp (setAcc p a b) ↔ eqBlk inp p := by
  cases p.st <;> simp [eqBlk, setAcc, Pub.lambda, Pub.cprime]

theorem setAcc_eqBlk (inp : Inputs K) (p : Pub K) (a b : K) :
    eqBlkE lmb inp (setAcc p a b) ↔ eqBlkE lmb inp p := by
  unfold eqBlkE
  rw [encPub_setAcc, setAcc_eqBlk_raw]

theorem setAcc_interDelta (inp : Inputs K) (p : Pub K) (a b : K) :
    interDelta inp (setAcc p a b) = interDelta inp p := by
  cases p.st <;> rfl

/-- One BFS step: `icur = acc + interDelta`, `ipre = acc`. -/
noncomputable def threadPub (inp : Inputs K) (acc : K) (p : Pub K) : K × Pub K :=
  let icur := acc + interDelta inp p
  (icur, setAcc p acc icur)

theorem threadPub_fst (inp : Inputs K) (acc : K) (p : Pub K) :
    (threadPub inp acc p).1 = acc + interDelta inp p := rfl

theorem threadPub_snd (inp : Inputs K) (acc : K) (p : Pub K) :
    (threadPub inp acc p).2 = setAcc p acc (acc + interDelta inp p) := rfl

theorem threadPub_interV (inp : Inputs K) (acc : K) (p : Pub K) :
    interV inp (threadPub inp acc p).2 := by
  rw [interV_iff_delta, threadPub_snd, setAcc_icur, setAcc_ipre, setAcc_interDelta]
  ring

theorem threadPub_eqBlk (inp : Inputs K) (acc : K) (p : Pub K) :
    eqBlkE lmb inp (threadPub inp acc p).2 ↔ eqBlkE lmb inp p := by
  rw [threadPub_snd, setAcc_eqBlk]

theorem threadPub_Vmem (inp : Inputs K) (acc : K) (p : Pub K)
    (h : eqBlkE lmb inp p) (hγ : inp.γ = 0 := by rfl) :
    VmemE lmb inp (threadPub inp acc p).2 :=
  vmemE_of hγ ((threadPub_eqBlk inp acc p).mpr h) (threadPub_interV inp acc p)

/-- BFS-order LogUp fill of a flat public-column list. -/
noncomputable def threadPubs (inp : Inputs K) : K → List (Pub K) → List (Pub K)
  | _, [] => []
  | acc, p :: ps =>
      (threadPub inp acc p).2 :: threadPubs inp (threadPub inp acc p).1 ps

theorem threadPubs_nil (inp : Inputs K) (acc : K) :
    threadPubs inp acc ([] : List (Pub K)) = [] := rfl

theorem threadPubs_cons (inp : Inputs K) (acc : K) (p : Pub K) (ps : List (Pub K)) :
    threadPubs inp acc (p :: ps) =
      (threadPub inp acc p).2 :: threadPubs inp (threadPub inp acc p).1 ps :=
  rfl

theorem threadPubs_length (inp : Inputs K) :
    ∀ acc ps, (threadPubs inp acc ps).length = ps.length
  | _, [] => rfl
  | acc, _ :: ps => by simp [threadPubs_cons, threadPubs_length inp (threadPub inp acc _).1 ps]

theorem threadPubs_interV (inp : Inputs K) :
    ∀ acc ps, ∀ p ∈ threadPubs inp acc ps, interV inp p
  | _, [] => by intro p hp; cases hp
  | acc, q :: qs => by
      intro p hp
      simp only [threadPubs_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact threadPub_interV inp acc q
      · exact threadPubs_interV inp (threadPub inp acc q).1 qs p hp

theorem threadPubs_eqBlk (inp : Inputs K) :
    ∀ acc ps, (∀ p ∈ ps, eqBlkE lmb inp p) →
      ∀ p ∈ threadPubs inp acc ps, eqBlkE lmb inp p
  | _, [] => by intro _ p hp; cases hp
  | acc, q :: qs => by
      intro hall p hp
      simp only [threadPubs_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact (threadPub_eqBlk inp acc q).mpr (hall q List.mem_cons_self)
      · exact threadPubs_eqBlk inp (threadPub inp acc q).1 qs
          (fun r hr => hall r (List.mem_cons_of_mem _ hr)) p hp

theorem threadPubs_Vmem (inp : Inputs K) (acc : K) (ps : List (Pub K))
    (h : ∀ p ∈ ps, eqBlkE lmb inp p) (hγ : inp.γ = 0 := by rfl) :
    ∀ p ∈ threadPubs inp acc ps, VmemE lmb inp p := by
  intro p hp
  exact vmemE_of hγ (threadPubs_eqBlk inp acc ps h p hp) (threadPubs_interV inp acc ps p hp)

theorem threadPubs_interChain (inp : Inputs K) :
    ∀ acc ps,
      InterChain inp acc (acc + sumDelta inp ps) (threadPubs inp acc ps)
  | acc, [] => by
      simp [threadPubs_nil, InterChain, sumDelta]
  | acc, p :: ps => by
      refine ⟨rfl, threadPub_interV inp acc p, ?_⟩
      have hih := threadPubs_interChain inp (threadPub inp acc p).1 ps
      have hicur : (threadPub inp acc p).2.icur = (threadPub inp acc p).1 := by
        rw [threadPub_snd, threadPub_fst]
        exact setAcc_icur p acc _
      have hterm : acc + sumDelta inp (p :: ps) =
          (threadPub inp acc p).1 + sumDelta inp ps := by
        simp [threadPub_fst, sumDelta, List.map_cons, List.sum_cons]
        abel
      rw [hicur, hterm]
      exact hih

theorem threadPub_ipre (inp : Inputs K) (acc : K) (p : Pub K) :
    (threadPub inp acc p).2.ipre = acc := by
  rw [threadPub_snd]
  exact setAcc_ipre p acc _

/-- Apply `setAcc` to the public columns of one generated memory row. -/
def setGenAcc (g : GenMemoryRow K) (ipre icur : K) : GenMemoryRow K :=
  { g with row := (g.row.1, (g.row.2.1, setAcc g.row.2.2 ipre icur)) }

noncomputable def threadGenRow (inp : Inputs K) (acc : K) (g : GenMemoryRow K) :
    K × GenMemoryRow K :=
  let icur := acc + interDelta inp g.row.2.2
  (icur, setGenAcc g acc icur)

noncomputable def threadGenRows (inp : Inputs K) : K → List (GenMemoryRow K) →
    List (GenMemoryRow K)
  | _, [] => []
  | acc, g :: gs =>
      (threadGenRow inp acc g).2 :: threadGenRows inp (threadGenRow inp acc g).1 gs

/-- Fill LogUp accumulators of a generated forest in BFS order. -/
noncomputable def threadGenForest (inp : Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K))) : List (NTree (GenMemoryRow K)) :=
  zipBfs forest (threadGenRows inp acc ((bfsForest forest).map NTree.label))

theorem setGenAcc_eqBlk (inp : Inputs K) (g : GenMemoryRow K) (a b : K) :
    eqBlkE lmb inp (setGenAcc g a b).row.2.2 ↔ eqBlkE lmb inp g.row.2.2 := by
  simp [setGenAcc, setAcc_eqBlk]

theorem setGenAcc_row1 (g : GenMemoryRow K) (a b : K) :
    (setGenAcc g a b).row.1 = g.row.1 := rfl

theorem setGenAcc_inputs (g : GenMemoryRow K) (a b : K) :
    (setGenAcc g a b).row.2.1 = g.row.2.1 := rfl

theorem setGenAcc_pub_st (g : GenMemoryRow K) (a b : K) :
    (setGenAcc g a b).row.2.2.st = g.row.2.2.st := rfl
theorem setGenAcc_ver (g : GenMemoryRow K) (a b : K) :
    (setGenAcc g a b).row.2.2.ver = g.row.2.2.ver := rfl

theorem setGenAcc_cprime (g : GenMemoryRow K) (a b : K) :
    (setGenAcc g a b).row.2.2.cprime = g.row.2.2.cprime := by
  simp [setGenAcc, setAcc, MemoryTable.Pub.cprime]

theorem setGenAcc_lambda (g : GenMemoryRow K) (a b : K) :
    (setGenAcc g a b).row.2.2.lambda = g.row.2.2.lambda := by
  simp [setGenAcc, setAcc, MemoryTable.Pub.lambda]

theorem setGenAcc_state_agree (g : GenMemoryRow K) (a b : K)
    (h : g.row.1 = g.row.2.2.st) :
    (setGenAcc g a b).row.1 = (setGenAcc g a b).row.2.2.st := by
  simpa [setGenAcc_row1, setGenAcc_pub_st] using h

theorem threadGenRow_fst (inp : Inputs K) (acc : K) (g : GenMemoryRow K) :
    (threadGenRow inp acc g).1 = acc + interDelta inp g.row.2.2 := rfl

theorem threadGenRow_snd (inp : Inputs K) (acc : K) (g : GenMemoryRow K) :
    (threadGenRow inp acc g).2 =
      setGenAcc g acc (acc + interDelta inp g.row.2.2) := rfl

theorem threadGenRow_eqBlk (inp : Inputs K) (acc : K) (g : GenMemoryRow K) :
    eqBlkE lmb inp (threadGenRow inp acc g).2.row.2.2 ↔ eqBlkE lmb inp g.row.2.2 := by
  rw [threadGenRow_snd, setGenAcc_eqBlk]

theorem threadGenRow_interV (inp : Inputs K) (acc : K) (g : GenMemoryRow K) :
    interV inp (threadGenRow inp acc g).2.row.2.2 := by
  rw [interV_iff_delta, threadGenRow_snd]
  simp [setGenAcc, setAcc_icur, setAcc_ipre, setAcc_interDelta]

theorem threadGenRow_Vmem (inp : Inputs K) (acc : K) (g : GenMemoryRow K)
    (h : eqBlkE lmb inp g.row.2.2) (hγ : inp.γ = 0 := by rfl) :
    VmemE lmb inp (threadGenRow inp acc g).2.row.2.2 :=
  vmemE_of hγ ((threadGenRow_eqBlk inp acc g).mpr h) (threadGenRow_interV inp acc g)

theorem threadGenRows_nil (inp : Inputs K) (acc : K) :
    threadGenRows inp acc ([] : List (GenMemoryRow K)) = [] := rfl

theorem threadGenRows_cons (inp : Inputs K) (acc : K) (g : GenMemoryRow K)
    (gs : List (GenMemoryRow K)) :
    threadGenRows inp acc (g :: gs) =
      (threadGenRow inp acc g).2 ::
        threadGenRows inp (threadGenRow inp acc g).1 gs :=
  rfl

theorem threadGenRows_length (inp : Inputs K) :
    ∀ acc gs, (threadGenRows inp acc gs).length = gs.length
  | _, [] => rfl
  | acc, _ :: gs => by
      simp [threadGenRows_cons, threadGenRows_length inp (threadGenRow inp acc _).1 gs]

theorem threadGenRows_eqBlk (inp : Inputs K) :
    ∀ acc gs, (∀ g ∈ gs, eqBlkE lmb inp g.row.2.2) →
      ∀ g ∈ threadGenRows inp acc gs, eqBlkE lmb inp g.row.2.2
  | _, [] => by intro _ g hg; cases hg
  | acc, q :: qs => by
      intro hall g hg
      simp only [threadGenRows_cons, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact (threadGenRow_eqBlk inp acc q).mpr (hall q (List.mem_cons.mpr (Or.inl rfl)))
      · exact threadGenRows_eqBlk inp (threadGenRow inp acc q).1 qs
          (fun r hr => hall r (List.mem_cons_of_mem _ hr)) g hg

theorem threadGenRows_Vmem (inp : Inputs K) (hγ : inp.γ = 0) :
    ∀ acc gs, (∀ g ∈ gs, eqBlkE lmb inp g.row.2.2) →
      ∀ g ∈ threadGenRows inp acc gs, VmemE lmb inp g.row.2.2
  | _, [] => by intro _ g hg; cases hg
  | acc, q :: qs => by
      intro hall g hg
      simp only [threadGenRows_cons, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact threadGenRow_Vmem inp acc q (hall q (List.mem_cons.mpr (Or.inl rfl))) hγ
      · exact threadGenRows_Vmem inp hγ (threadGenRow inp acc q).1 qs
          (fun r hr => hall r (List.mem_cons_of_mem _ hr)) g hg

theorem threadGenRow_Vmem_or (inp : Inputs K) (acc : K) (g : GenMemoryRow K)
    (h : g.row.2.2.st = .read_root ∨ eqBlkE lmb inp g.row.2.2) (hγ : inp.γ = 0 := by rfl) :
    (threadGenRow inp acc g).2.row.2.2.st = .read_root ∨
      VmemE lmb inp (threadGenRow inp acc g).2.row.2.2 := by
  rcases h with hst | heq
  · left
    simpa [threadGenRow_snd, setGenAcc_pub_st] using hst
  · right
    exact threadGenRow_Vmem inp acc g heq hγ

theorem threadGenRows_eqBlk_or (inp : Inputs K) :
    ∀ acc gs,
      (∀ g ∈ gs, g.row.2.2.st = .read_root ∨ eqBlkE lmb inp g.row.2.2) →
      ∀ g ∈ threadGenRows inp acc gs,
        g.row.2.2.st = .read_root ∨ eqBlkE lmb inp g.row.2.2
  | _, [] => by intro _ g hg; cases hg
  | acc, q :: qs => by
      intro hall g hg
      simp only [threadGenRows_cons, List.mem_cons] at hg
      rcases hg with rfl | hg
      · have hq := hall q (List.mem_cons.mpr (Or.inl rfl))
        rcases hq with hst | heq
        · left; simpa [threadGenRow_snd, setGenAcc_pub_st] using hst
        · right; exact (threadGenRow_eqBlk inp acc q).mpr heq
      · exact threadGenRows_eqBlk_or inp (threadGenRow inp acc q).1 qs
          (fun r hr => hall r (List.mem_cons_of_mem _ hr)) g hg

theorem threadGenRows_Vmem_or (inp : Inputs K) (hγ : inp.γ = 0) :
    ∀ acc gs,
      (∀ g ∈ gs, g.row.2.2.st = .read_root ∨ eqBlkE lmb inp g.row.2.2) →
      ∀ g ∈ threadGenRows inp acc gs,
        g.row.2.2.st = .read_root ∨ VmemE lmb inp g.row.2.2
  | _, [] => by intro _ g hg; cases hg
  | acc, q :: qs => by
      intro hall g hg
      simp only [threadGenRows_cons, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact threadGenRow_Vmem_or inp acc q (hall q (List.mem_cons.mpr (Or.inl rfl))) hγ
      · exact threadGenRows_Vmem_or inp hγ (threadGenRow inp acc q).1 qs
          (fun r hr => hall r (List.mem_cons_of_mem _ hr)) g hg

theorem threadGenForest_bfs_labels (inp : Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K))) :
    (bfsForest (threadGenForest inp acc forest)).map NTree.label =
      threadGenRows inp acc ((bfsForest forest).map NTree.label) := by
  unfold threadGenForest
  refine zipBfs_labels forest _ ?_
  rw [threadGenRows_length, List.length_map, bfsForest_length]

theorem threadGenForest_eqBlk (inp : Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K)))
    (H : ∀ t ∈ bfsForest forest, eqBlkE lmb inp t.label.row.2.2) :
    ∀ t ∈ bfsForest (threadGenForest inp acc forest),
      eqBlkE lmb inp t.label.row.2.2 := by
  intro t ht
  have hlab : t.label ∈
      (bfsForest (threadGenForest inp acc forest)).map NTree.label :=
    List.mem_map.mpr ⟨t, ht, rfl⟩
  rw [threadGenForest_bfs_labels] at hlab
  exact threadGenRows_eqBlk inp acc _
    (fun g hg => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      exact H u hu)
    t.label hlab

theorem threadGenRow_cprime (inp : Inputs K) (acc : K) (g : GenMemoryRow K) :
    (threadGenRow inp acc g).2.row.2.2.cprime = g.row.2.2.cprime := by
  rw [threadGenRow_snd, setGenAcc_cprime]

theorem threadGenRows_cprime (inp : Inputs K) :
    ∀ acc gs, (∀ g ∈ gs, g.row.2.2.cprime = 1) →
      ∀ g ∈ threadGenRows inp acc gs, g.row.2.2.cprime = 1
  | _, [] => by intro _ g hg; cases hg
  | acc, q :: qs => by
      intro hall g hg
      simp only [threadGenRows_cons, List.mem_cons] at hg
      rcases hg with rfl | hg
      · rw [threadGenRow_cprime]
        exact hall q (by simp)
      · exact threadGenRows_cprime inp (threadGenRow inp acc q).1 qs
          (fun r hr => hall r (List.mem_cons_of_mem _ hr)) g hg

/-- Threading rewrites `ipre`/`icur` only, so a BFS label with `C' = 1` stays there. -/
theorem threadGenForest_bfs_cprime (inp : Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K)))
    (H : ∀ t ∈ bfsForest forest, t.label.row.2.2.cprime = 1) :
    ∀ t ∈ bfsForest (threadGenForest inp acc forest),
      t.label.row.2.2.cprime = 1 := by
  intro t ht
  have hlab : t.label ∈
      (bfsForest (threadGenForest inp acc forest)).map NTree.label :=
    List.mem_map.mpr ⟨t, ht, rfl⟩
  rw [threadGenForest_bfs_labels] at hlab
  exact threadGenRows_cprime inp acc _
    (fun g hg => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      exact H u hu)
    t.label hlab

theorem threadGenRow_lambda (inp : Inputs K) (acc : K) (g : GenMemoryRow K) :
    (threadGenRow inp acc g).2.row.2.2.lambda = g.row.2.2.lambda := by
  rw [threadGenRow_snd, setGenAcc_lambda]

theorem threadGenRows_lambda (inp : Inputs K) :
    ∀ acc gs, (∀ g ∈ gs, g.row.2.2.lambda = 1) →
      ∀ g ∈ threadGenRows inp acc gs, g.row.2.2.lambda = 1
  | _, [] => by intro _ g hg; cases hg
  | acc, q :: qs => by
      intro hall g hg
      simp only [threadGenRows_cons, List.mem_cons] at hg
      rcases hg with rfl | hg
      · rw [threadGenRow_lambda]
        exact hall q (by simp)
      · exact threadGenRows_lambda inp (threadGenRow inp acc q).1 qs
          (fun r hr => hall r (List.mem_cons_of_mem _ hr)) g hg

/-- Threading rewrites `ipre`/`icur` only, so a BFS label with `λ = 1` stays there. -/
theorem threadGenForest_bfs_lambda (inp : Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K)))
    (H : ∀ t ∈ bfsForest forest, t.label.row.2.2.lambda = 1) :
    ∀ t ∈ bfsForest (threadGenForest inp acc forest),
      t.label.row.2.2.lambda = 1 := by
  intro t ht
  have hlab : t.label ∈
      (bfsForest (threadGenForest inp acc forest)).map NTree.label :=
    List.mem_map.mpr ⟨t, ht, rfl⟩
  rw [threadGenForest_bfs_labels] at hlab
  exact threadGenRows_lambda inp acc _
    (fun g hg => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      exact H u hu)
    t.label hlab

theorem threadGenForest_eqBlk_or (inp : Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K)))
    (H : ∀ t ∈ bfsForest forest,
      t.label.row.2.2.st = .read_root ∨ eqBlkE lmb inp t.label.row.2.2) :
    ∀ t ∈ bfsForest (threadGenForest inp acc forest),
      t.label.row.2.2.st = .read_root ∨ eqBlkE lmb inp t.label.row.2.2 := by
  intro t ht
  have hlab : t.label ∈
      (bfsForest (threadGenForest inp acc forest)).map NTree.label :=
    List.mem_map.mpr ⟨t, ht, rfl⟩
  rw [threadGenForest_bfs_labels] at hlab
  exact threadGenRows_eqBlk_or inp acc _
    (fun g hg => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      exact H u hu)
    t.label hlab

theorem threadGenForest_Vmem (inp : Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K)))
    (H : ∀ t ∈ bfsForest forest, eqBlkE lmb inp t.label.row.2.2) (hγ : inp.γ = 0 := by rfl) :
    ∀ t ∈ bfsForest (threadGenForest inp acc forest),
      VmemE lmb inp t.label.row.2.2 := by
  intro t ht
  have hlab : t.label ∈
      (bfsForest (threadGenForest inp acc forest)).map NTree.label :=
    List.mem_map.mpr ⟨t, ht, rfl⟩
  rw [threadGenForest_bfs_labels] at hlab
  exact threadGenRows_Vmem inp hγ acc _
    (fun g hg => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      exact H u hu)
    t.label hlab

theorem threadGenForest_Vmem_or (inp : Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K)))
    (H : ∀ t ∈ bfsForest forest,
      t.label.row.2.2.st = .read_root ∨ eqBlkE lmb inp t.label.row.2.2)
    (hγ : inp.γ = 0 := by rfl) :
    ∀ t ∈ bfsForest (threadGenForest inp acc forest),
      t.label.row.2.2.st = .read_root ∨ VmemE lmb inp t.label.row.2.2 := by
  intro t ht
  have hlab : t.label ∈
      (bfsForest (threadGenForest inp acc forest)).map NTree.label :=
    List.mem_map.mpr ⟨t, ht, rfl⟩
  rw [threadGenForest_bfs_labels] at hlab
  exact threadGenRows_Vmem_or inp hγ acc _
    (fun g hg => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      exact H u hu)
    t.label hlab

theorem threadGenRow_row1 (inp : Inputs K) (acc : K) (g : GenMemoryRow K) :
    (threadGenRow inp acc g).2.row.1 = g.row.1 := by
  rw [threadGenRow_snd, setGenAcc_row1]

theorem threadGenRow_inputs (inp : Inputs K) (acc : K) (g : GenMemoryRow K) :
    (threadGenRow inp acc g).2.row.2.1 = g.row.2.1 := by
  rw [threadGenRow_snd, setGenAcc_inputs]

theorem threadGenRow_pub_st (inp : Inputs K) (acc : K) (g : GenMemoryRow K) :
    (threadGenRow inp acc g).2.row.2.2.st = g.row.2.2.st := by
  rw [threadGenRow_snd, setGenAcc_pub_st]

theorem threadGenRows_state_agree (inp : Inputs K) :
    ∀ acc gs, (∀ g ∈ gs, g.row.1 = g.row.2.2.st) →
      ∀ g ∈ threadGenRows inp acc gs, g.row.1 = g.row.2.2.st
  | _, [] => by intro _ g hg; cases hg
  | acc, q :: qs => by
      intro hall g hg
      simp only [threadGenRows_cons, List.mem_cons] at hg
      rcases hg with rfl | hg
      · simpa [threadGenRow_row1, threadGenRow_pub_st] using
          hall q (List.mem_cons.mpr (Or.inl rfl))
      · exact threadGenRows_state_agree inp (threadGenRow inp acc q).1 qs
          (fun r hr => hall r (List.mem_cons_of_mem _ hr)) g hg

theorem threadGenRows_inputs (inp : Inputs K) :
    ∀ acc gs, (∀ g ∈ gs, g.row.2.1 = inp) →
      ∀ g ∈ threadGenRows inp acc gs, g.row.2.1 = inp
  | _, [] => by intro _ g hg; cases hg
  | acc, q :: qs => by
      intro hall g hg
      simp only [threadGenRows_cons, List.mem_cons] at hg
      rcases hg with rfl | hg
      · simpa [threadGenRow_inputs] using hall q (List.mem_cons.mpr (Or.inl rfl))
      · exact threadGenRows_inputs inp (threadGenRow inp acc q).1 qs
          (fun r hr => hall r (List.mem_cons_of_mem _ hr)) g hg

theorem threadGenRows_map_pub (inp : Inputs K) :
    ∀ acc gs,
      (threadGenRows inp acc gs).map (fun g => g.row.2.2) =
        threadPubs inp acc (gs.map (fun g => g.row.2.2))
  | _, [] => rfl
  | acc, g :: gs => by
      simp [threadGenRows_cons, threadPubs_cons, threadGenRow_snd, threadPub_snd,
        setGenAcc, threadGenRow_fst, threadPub_fst]
      exact threadGenRows_map_pub inp (threadGenRow inp acc g).1 gs

theorem threadGenForest_length (inp : Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K))) :
    (threadGenForest inp acc forest).length = forest.length := by
  unfold threadGenForest
  exact zipBfs_length _ _

theorem threadGenForest_totalSize (inp : Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K))) :
    totalSize (threadGenForest inp acc forest) = totalSize forest := by
  unfold threadGenForest
  exact zipBfs_totalSize _ _

theorem threadGenForest_state_agree (inp : Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K)))
    (H : ∀ t ∈ bfsForest forest, t.label.row.1 = t.label.row.2.2.st) :
    ∀ t ∈ bfsForest (threadGenForest inp acc forest),
      t.label.row.1 = t.label.row.2.2.st := by
  intro t ht
  have hlab : t.label ∈
      (bfsForest (threadGenForest inp acc forest)).map NTree.label :=
    List.mem_map.mpr ⟨t, ht, rfl⟩
  rw [threadGenForest_bfs_labels] at hlab
  exact threadGenRows_state_agree inp acc _
    (fun g hg => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      exact H u hu)
    t.label hlab

theorem threadGenForest_inputs (inp : Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K)))
    (H : ∀ t ∈ bfsForest forest, t.label.row.2.1 = inp) :
    ∀ t ∈ bfsForest (threadGenForest inp acc forest),
      t.label.row.2.1 = inp := by
  intro t ht
  have hlab : t.label ∈
      (bfsForest (threadGenForest inp acc forest)).map NTree.label :=
    List.mem_map.mpr ⟨t, ht, rfl⟩
  rw [threadGenForest_bfs_labels] at hlab
  exact threadGenRows_inputs inp acc _
    (fun g hg => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      exact H u hu)
    t.label hlab

theorem gMemRow9_inputs (sk : SemanticStrategy.MemoryRowSkeleton) (e : ℕ)
    (z : K) (pub : Pub K) :
    (gMemRow9 sk e z pub).row.2.1 = memInputs z := rfl

theorem gMemRow9_state_agree (sk : SemanticStrategy.MemoryRowSkeleton) (e : ℕ)
    (z : K) (pub : Pub K) (h : sk.state = pub.st) :
    (gMemRow9 sk e z pub).row.1 = (gMemRow9 sk e z pub).row.2.2.st := by
  simp [gMemRow9, h]

theorem genAnnotatedNounWalk_inputs (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n : Noun, ∀ t, InTree (genAnnotatedNounWalk E z lmb n).1 t →
      t.label.row.2.1 = memInputs z
  | .atom a, t, ht => by
      cases ht with
      | here => simp [genAnnotatedNounWalk, gMemRow9]
      | sub hs _ => simp [genAnnotatedNounWalk, NTree.children] at hs
  | .cell h tl, t, ht => by
      cases ht with
      | here => simp [genAnnotatedNounWalk, gMemRow9]
      | sub hs ht' =>
          have hcs :
              (genAnnotatedNounWalk E z lmb (.cell h tl)).1.children =
                [(genAnnotatedNounWalk E z lmb h).1,
                 (genAnnotatedNounWalk E z lmb tl).1] := by
            simp [genAnnotatedNounWalk]
          rw [hcs] at hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · exact genAnnotatedNounWalk_inputs E z h t ht'
          · exact genAnnotatedNounWalk_inputs E z tl t ht'

theorem genAnnotatedVerify_inputs (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    ∀ t, InTree (genAnnotatedVerify E z lmb root child ax ts recordExp).1 t →
      t.label.row.2.1 = memInputs z := by
  intro t ht
  cases ht with
  | here => simp [genAnnotatedVerify, gMemRow9]
  | sub hs ht' =>
      have hcs :
          (genAnnotatedVerify E z lmb root child ax ts recordExp).1.children =
            [(genAnnotatedNounWalk E z lmb child).1] := by
        simp [genAnnotatedVerify]
      rw [hcs] at hs
      simp only [List.mem_singleton] at hs
      subst hs
      exact genAnnotatedNounWalk_inputs E z child t ht'

theorem interChain_handoff (inp : Inputs K) :
    ∀ seed term (ps : List (Pub K)),
      InterChain inp seed term ps →
      ∀ i, (hilt : i + 1 < ps.length) →
        ps[i].icur = ps[i + 1].ipre
  | _, _, [] => by intro _ i hilt; simp at hilt
  | seed, term, p :: ps => by
      intro h i hilt
      obtain ⟨_, _, hrest⟩ := h
      match ps, i with
      | [], i =>
        simp at hilt
      | q :: qs, 0 =>
        exact hrest.1.symm
      | q :: qs, i + 1 =>
        have hrest' : InterChain inp p.icur term (q :: qs) := hrest
        have hlen : i + 1 < (q :: qs).length := by
          simp only [List.length_cons] at hilt ⊢
          omega
        simpa [List.getElem_cons_succ] using
          interChain_handoff inp p.icur term (q :: qs) hrest' i hlen

theorem interChain_head_ipre (inp : Inputs K) (seed term : K) (p : Pub K)
    (ps : List (Pub K)) (h : InterChain inp seed term (p :: ps)) :
    p.ipre = seed :=
  h.1

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig257

open Nock Nock.Walk
open Nock.NockVMROM.Thm54.TraceGen
open MemoryTable

theorem memoryInputs_eq (z α : K) :
    (cfg z α).challenges.memoryInputs = memInputs z := by
  simp [cfg, ChallengeVector.memoryInputs, memInputs]

theorem assigned_bfs_eqBlk (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    ∀ t ∈ bfsForest (genMemForestFromTree (encC z) z α lmb
        (bfsAssign (dotTree (K := K)))),
      eqBlkE lmb (memInputs z) t.label.row.2.2 :=
  dotMemForest_bfs_eqBlk z α hz htwo

theorem assigned_threaded_Vmem (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    ∀ t ∈ bfsForest (threadGenForest (memInputs z) 0
        (genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTree (K := K))))),
      VmemE lmb (memInputs z) t.label.row.2.2 :=
  threadGenForest_Vmem (memInputs z) 0 _
    (assigned_bfs_eqBlk z α hz htwo)

end Nock.NockVMROM.Thm54.TraceGen.DotConfig257

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock Nock.Walk
open Nock.NockVMROM.Thm54.TraceGen
open MemoryTable

theorem memoryInputs_eq (z α : K) :
    (cfg z α).challenges.memoryInputs = memInputs z := by
  simp [cfg, ChallengeVector.memoryInputs, memInputs]

theorem assigned_bfs_eqBlk (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    ∀ t ∈ bfsForest (genMemForestFromTree (encC z) z α lmb
        (bfsAssign (dotTreeAir (K := K)))),
      eqBlkE lmb (memInputs z) t.label.row.2.2 :=
  dotMemForest_bfs_eqBlk_air z α hz htwo

theorem assigned_threaded_Vmem (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    ∀ t ∈ bfsForest (threadGenForest (memInputs z) 0
        (genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTreeAir (K := K))))),
      VmemE lmb (memInputs z) t.label.row.2.2 :=
  threadGenForest_Vmem (memInputs z) 0 _
    (assigned_bfs_eqBlk z α hz htwo)

theorem assigned_threaded_Vmem_seed :
    ∀ t ∈ bfsForest (threadGenForest (memInputs seedZ) 0
        (genMemForestFromTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
          (bfsAssign (dotTreeAir (K := K))))),
      VmemE MemoryTable.formRDefault (memInputs seedZ) t.label.row.2.2 := by
  refine assigned_threaded_Vmem seedZ alphaA seedZ_ne_zero ?_
  intro h
  have : 769 ∣ 2 := (CharP.cast_eq_zero_iff K 769 2).mp h
  omega

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.genRowMemForest_three_chain32_eqBlk
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotMemForest_bfs_eqBlk
#print axioms Nock.NockVMROM.Thm54.TraceGen.zipBfs_self
#print axioms Nock.NockVMROM.Thm54.TraceGen.zipBfs_labels
#print axioms Nock.NockVMROM.Thm54.TraceGen.threadGenForest_Vmem
#print axioms Nock.NockVMROM.Thm54.TraceGen.zipBfs_totalSize
#print axioms Nock.NockVMROM.Thm54.TraceGen.threadGenForest_totalSize
#print axioms Nock.NockVMROM.Thm54.TraceGen.interChain_handoff
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedNounWalk_inputs
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.assigned_threaded_Vmem_seed
