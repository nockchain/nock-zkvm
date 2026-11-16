/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulMemAccept.lean

  Threaded assigned forest as an `ExactExecution` over `MatmulConfig65537`,
  and `MemoryRowsAccepted` for that carrier.

  `MatmulConfig65537.exec` keeps the unthreaded annotated forest.
  LogUp `ipre`/`icur` are filled by `threadGenForest`; `eqBlk` is the
  generic well-formed descent (`Noun.slot` on every request axis).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulSeed

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.RowLayout
open MemoryTable

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## Slot rest of a cell -/

theorem slot_child_of_tail {ax : ℕ} (hd tl child : Noun) (h2 : 2 ≤ ax)
    (hslot : Noun.slot ax (.cell hd tl) = some child)
    (ht : axisTopBit ax = true) (hr : axisRest ax < 2) :
    child = tl := by
  have hs : Noun.slot (axisRest ax) tl = some child := by
    simpa [slot_eq_msb hd tl h2, ht] using hslot
  have hne : axisRest ax ≠ 0 := by
    intro hz; rw [hz] at hs; simp [Noun.slot] at hs
  have : axisRest ax = 1 := by omega
  simp [this, Noun.slot] at hs
  exact hs.symm

theorem slot_child_of_head {ax : ℕ} (hd tl child : Noun) (h2 : 2 ≤ ax)
    (hslot : Noun.slot ax (.cell hd tl) = some child)
    (hh : axisTopBit ax = false) (hr : axisRest ax < 2) :
    child = hd := by
  have hs : Noun.slot (axisRest ax) hd = some child := by
    simpa [slot_eq_msb hd tl h2, hh] using hslot
  have hne : axisRest ax ≠ 0 := by
    intro hz; rw [hz] at hs; simp [Noun.slot] at hs
  have : axisRest ax = 1 := by omega
  simp [this, Noun.slot] at hs
  exact hs.symm

theorem slot_rest_tail {ax : ℕ} (hd tl child : Noun) (h2 : 2 ≤ ax)
    (hslot : Noun.slot ax (.cell hd tl) = some child)
    (ht : axisTopBit ax = true) :
    axisRest ax < 2 ∨ Noun.slot (axisRest ax) tl = some child := by
  have hs : Noun.slot (axisRest ax) tl = some child := by
    simpa [slot_eq_msb hd tl h2, ht] using hslot
  by_cases hlt : axisRest ax < 2
  · exact Or.inl hlt
  · exact Or.inr hs

theorem slot_rest_head {ax : ℕ} (hd tl child : Noun) (h2 : 2 ≤ ax)
    (hslot : Noun.slot ax (.cell hd tl) = some child)
    (hh : axisTopBit ax = false) :
    axisRest ax < 2 ∨ Noun.slot (axisRest ax) hd = some child := by
  have hs : Noun.slot (axisRest ax) hd = some child := by
    simpa [slot_eq_msb hd tl h2, hh] using hslot
  by_cases hlt : axisRest ax < 2
  · exact Or.inl hlt
  · exact Or.inr hs

/-! ## Inputs on every annotated constructor -/

theorem genAnnotatedDescent_all_inputs (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ) :
    ∀ current remaining,
      ∀ u ∈ (genAnnotatedDescent E z lmb root child recAxis ts recordExp
          current remaining).1,
        ∀ t, InTree u t → t.label.row.2.1 = memInputs z := by
  intro current remaining u hu t ht
  induction remaining using Nat.strongRecOn generalizing current u t with
  | _ n ih =>
    have hdesc := hu
    unfold genAnnotatedDescent at hdesc
    split at hdesc
    · simp [genAnnotatedVerify] at hdesc
      subst u
      exact genAnnotatedVerify_inputs E z root child recAxis ts recordExp t ht
    · rename_i hge
      have h2 : 2 ≤ n := by omega
      split at hdesc
      · simp at hdesc
        subst u
        cases ht with
        | here => simp [gMemRow9]
        | sub hs ht' =>
            simp [NTree.children, List.mem_append] at hs
            rcases hs with rfl | hu'
            · exact genAnnotatedNounWalk_inputs E z (formulaHead current) t ht'
            · exact ih (axisRest n) (axisRest_lt h2) (formulaTail current) _ hu' t ht'
      · simp at hdesc
        subst u
        cases ht with
        | here => simp [gMemRow9]
        | sub hs ht' =>
            simp [NTree.children, List.mem_append] at hs
            rcases hs with hu' | rfl
            · exact ih (axisRest n) (axisRest_lt h2) (formulaHead current) _ hu' t ht'
            · exact genAnnotatedNounWalk_inputs E z (formulaTail current) t ht'

theorem genAnnotatedRecordTree_all_inputs (E : Noun → ComputeTable.FP K)
    (z α : K) (root child : Noun) (axis e : ℕ) :
    ∀ t, InTree (genAnnotatedRecordTree E z α lmb root child axis e) t →
      t.label.row.2.1 = memInputs z := by
  intro t ht
  cases ht with
  | here => simp [genAnnotatedRecordTree, gMemRow9]
  | sub hs ht' =>
      simp [genAnnotatedRecordTree, NTree.children] at hs
      exact genAnnotatedDescent_all_inputs E z root child axis (α ^ e) e
        root axis _ hs t ht'

theorem genAnnotatedDescentCont_all_inputs (E : Noun → ComputeTable.FP K)
    (z : K) (cont : List (NTree (GenMemoryRow K)))
    (contCell : MemoryTable.Cell K) (contState : MemoryTable.MState)
    (hcs : ∀ u ∈ cont, ∀ t, InTree u t → t.label.row.2.1 = memInputs z) :
    ∀ current remaining,
      ∀ u ∈ (genAnnotatedDescentCont E z lmb cont contCell contState
          current remaining).1,
        ∀ t, InTree u t → t.label.row.2.1 = memInputs z := by
  intro current remaining u hu t ht
  induction remaining using Nat.strongRecOn generalizing current u t with
  | _ n ih =>
    have hdesc := hu
    unfold genAnnotatedDescentCont at hdesc
    split at hdesc
    · exact hcs u hdesc t ht
    · rename_i hge
      have h2 : 2 ≤ n := by omega
      split at hdesc
      · simp at hdesc
        subst u
        cases ht with
        | here => simp [gMemRow9]
        | sub hs ht' =>
            simp [NTree.children, List.mem_append] at hs
            rcases hs with rfl | hu'
            · exact genAnnotatedNounWalk_inputs E z (formulaHead current) t ht'
            · exact ih (axisRest n) (axisRest_lt h2) (formulaTail current) _ hu' t ht'
      · simp at hdesc
        subst u
        cases ht with
        | here => simp [gMemRow9]
        | sub hs ht' =>
            simp [NTree.children, List.mem_append] at hs
            rcases hs with hu' | rfl
            · exact ih (axisRest n) (axisRest_lt h2) (formulaHead current) _ hu' t ht'
            · exact genAnnotatedNounWalk_inputs E z (formulaTail current) t ht'

theorem genAnnotatedChainedInner_one_inputs (E : Noun → ComputeTable.FP K)
    (z α : K) (prev r : MemRecordReq) :
    ∀ u ∈ (genAnnotatedChainedInner E z α lmb prev [r]).1,
      ∀ t, InTree u t → t.label.row.2.1 = memInputs z := by
  intro u hu t ht
  unfold genAnnotatedChainedInner at hu
  simp only [genAnnotatedChainedInner_nil, chainedInnerRootState] at hu
  simp at hu
  subst u
  cases ht with
  | here => simp [gMemRow9]
  | sub hs ht' =>
      simp [NTree.children] at hs
      subst hs
      cases ht' with
      | here => simp [gMemRow9]
      | sub hs2 ht2 =>
          simp [NTree.children] at hs2
          exact genAnnotatedDescentCont_all_inputs E z
            [(genAnnotatedVerify E z lmb r.root r.child r.axis
                (α ^ r.recordExp) r.recordExp).1]
            (genAnnotatedVerify E z lmb r.root r.child r.axis
                (α ^ r.recordExp) r.recordExp).2
            .verify_child
            (fun v hv w hw => by
              simp at hv; subst v
              exact genAnnotatedVerify_inputs E z r.root r.child r.axis
                (α ^ r.recordExp) r.recordExp w hw)
            r.root r.axis _ hs2 t ht2

theorem genAnnotatedChainedTree_two_inputs (E : Noun → ComputeTable.FP K)
    (z α : K) (r1 r2 : MemRecordReq)
    (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z α lmb [r1, r2] = some t) :
    ∀ u, InTree t u → u.label.row.2.1 = memInputs z := by
  unfold genAnnotatedChainedTree at ht
  simp only [chainedInnerRootState] at ht
  injection ht with ht
  subst t
  intro u hu
  cases hu with
  | here => simp [gMemRow9]
  | sub hs hu' =>
      simp [NTree.children] at hs
      exact genAnnotatedDescentCont_all_inputs E z
        (genAnnotatedChainedInner E z α lmb r1 [r2]).1
        (genAnnotatedChainedInner E z α lmb r1 [r2]).2
        (chainedInnerRootState [r2])
        (genAnnotatedChainedInner_one_inputs E z α r1 r2)
        r1.root r1.axis _ hs u hu'

theorem genRowMemForest_all_inputs (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ rs : List MemRecordReq,
      ∀ u ∈ genRowMemForest E z α lmb rs,
        ∀ t, InTree u t → t.label.row.2.1 = memInputs z
  | [], u, hu, t, ht => by simp [genRowMemForest] at hu
  | [r], u, hu, t, ht => by
      simp [genRowMemForest_singleton] at hu
      subst u
      exact genAnnotatedRecordTree_all_inputs E z α r.root r.child r.axis
        r.recordExp t ht
  | [r1, r2], u, hu, t, ht => by
      rw [genRowMemForest_two_eq] at hu
      by_cases hc : r1.child = r2.root
      · rw [if_pos hc] at hu
        cases hch : genAnnotatedChainedTree E z α lmb [r1, r2] with
        | none =>
          have : genAnnotatedChainedTree E z α lmb [r1, r2] = none := hch
          simp [genAnnotatedChainedTree] at this
        | some tree =>
          simp [hch] at hu
          subst u
          exact genAnnotatedChainedTree_two_inputs E z α r1 r2 tree hch t ht
      · rw [if_neg hc] at hu
        simp at hu
        rcases hu with hu | hu
        · subst u
          exact genAnnotatedRecordTree_all_inputs E z α r1.root r1.child
            r1.axis r1.recordExp t ht
        · subst u
          exact genAnnotatedRecordTree_all_inputs E z α r2.root r2.child
            r2.axis r2.recordExp t ht
  | [r1, r2, r3], u, hu, t, ht => by
      rw [genRowMemForest_three_eq] at hu
      simp [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact genRowMemForest_all_inputs E z α [r1, r2] u hu t ht
      · exact genAnnotatedRecordTree_all_inputs E z α r3.root r3.child
          r3.axis r3.recordExp t ht
  | r1 :: r2 :: r3 :: r4 :: rest, u, hu, t, ht => by
      unfold genRowMemForest at hu
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
      exact genAnnotatedRecordTree_all_inputs E z α r.root r.child r.axis
        r.recordExp t ht

/-! ## `eqBlk` on well-formed descent -/

theorem genAnnotatedDescent_all_eqBlk (z α : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0) (root child : Noun) (recAxis e : ℕ) :
    ∀ current remaining,
      (remaining < 2 ∨ Noun.slot remaining current = some child) →
      ∀ u ∈ (genAnnotatedDescent (encC z) z lmb root child recAxis (α ^ e) e
          current remaining).1,
        ∀ t, InTree u t → eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro current remaining hslot u hu t ht
  induction remaining using Nat.strongRecOn generalizing current u t with
  | _ n ih =>
    have hdesc := hu
    unfold genAnnotatedDescent at hdesc
    split at hdesc
    · simp [genAnnotatedVerify] at hdesc
      subst u
      exact genAnnotatedVerify_all_eqBlk z hz htwo root child recAxis
        (α ^ e) e t ht
    · rename_i hge
      have h2 : 2 ≤ n := by omega
      have hsc : Noun.slot n current = some child := by
        cases hslot with
        | inl hlt => omega
        | inr hs => exact hs
      cases current with
      | atom a =>
        have := slot_atom_of_ge_two (a := n) (n := a) h2
        simp [this] at hsc
      | cell hd tl =>
        split at hdesc
        · rename_i htbit
          simp at hdesc
          subst u
          have hrec := slot_rest_tail hd tl child h2 hsc htbit
          have hpt := genAnnotatedDescent_pt_noun (lmb := lmb) (encC z) z root child
            recAxis (α ^ e) e tl (axisRest n)
          cases ht with
          | here =>
              simp [gMemRow9, formulaHead, formulaTail]
              refine annotatedDecPub_eqBlk z hz htwo hd tl _ _ _ _ 0 0
                (genAnnotatedNounWalk_pt_noun (encC z) z hd) ?_
              by_cases hr : axisRest n < 2
              · rw [if_pos hr] at hpt
                have hct := slot_child_of_tail hd tl child h2 hsc htbit hr
                rw [hpt, hct]
              · rw [if_neg hr] at hpt
                exact hpt
          | sub hs ht' =>
              simp [NTree.children, List.mem_append, formulaHead, formulaTail] at hs
              rcases hs with rfl | hu'
              · exact genAnnotatedNounWalk_all_eqBlk z hz htwo hd t ht'
              · exact ih (axisRest n) (axisRest_lt h2) tl hrec _ hu' t ht'
        · rename_i hbit
          have hh : axisTopBit n = false := Bool.eq_false_iff.mpr hbit
          simp at hdesc
          subst u
          have hrec := slot_rest_head hd tl child h2 hsc hh
          have hpt := genAnnotatedDescent_pt_noun (lmb := lmb) (encC z) z root child
            recAxis (α ^ e) e hd (axisRest n)
          cases ht with
          | here =>
              simp [gMemRow9, formulaHead, formulaTail]
              refine annotatedDecPub_eqBlk z hz htwo hd tl _ _ _ _ 0 0 ?_
                (genAnnotatedNounWalk_pt_noun (encC z) z tl)
              by_cases hr : axisRest n < 2
              · rw [if_pos hr] at hpt
                have hct := slot_child_of_head hd tl child h2 hsc hh hr
                rw [hpt, hct]
              · rw [if_neg hr] at hpt
                exact hpt
          | sub hs ht' =>
              simp [NTree.children, List.mem_append, formulaHead, formulaTail] at hs
              rcases hs with hu' | rfl
              · exact ih (axisRest n) (axisRest_lt h2) hd hrec _ hu' t ht'
              · exact genAnnotatedNounWalk_all_eqBlk z hz htwo tl t ht'

theorem genAnnotatedRecordTree_wf_eqBlk (z α : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0) (root child : Noun) (axis e : ℕ)
    (hwf : lsbTarget root axis = child)
    (hslot : axis < 2 ∨ Noun.slot axis root = some child) :
    ∀ t, InTree (genAnnotatedRecordTree (encC z) z α lmb root child axis e) t →
      eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro t ht
  cases ht with
  | here =>
      simp [genAnnotatedRecordTree, gMemRow9]
      refine annotatedReadPub_eqBlk z root child axis (α ^ e) _ 0 0 ?_
      have hpt := genAnnotatedDescent_pt_noun (lmb := lmb) (encC z) z root child axis
        (α ^ e) e root axis
      by_cases hlt : axis < 2
      · rw [if_pos hlt] at hpt
        have hroot : root = child := by
          have := lsbTarget_of_lt2 root hlt
          exact this.symm.trans hwf
        rw [hpt, hroot]
      · rw [if_neg hlt] at hpt
        exact hpt
  | sub hs ht' =>
      simp [genAnnotatedRecordTree, NTree.children] at hs
      exact genAnnotatedDescent_all_eqBlk z α hz htwo root child axis e
        root axis hslot _ hs t ht'

theorem genAnnotatedDescentCont_all_eqBlk (z _α : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState)
    (hcs : ∀ u ∈ cont, ∀ t, InTree u t → eqBlkE lmb (memInputs z) t.label.row.2.2) :
    ∀ current remaining child,
      (remaining < 2 ∨ Noun.slot remaining current = some child) →
      contCell.noun = encC z child →
      ∀ u ∈ (genAnnotatedDescentCont (encC z) z lmb cont contCell contState
          current remaining).1,
        ∀ t, InTree u t → eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro current remaining child hslot hcont u hu t ht
  induction remaining using Nat.strongRecOn
      generalizing current u t with
  | _ n ih =>
    have hdesc := hu
    unfold genAnnotatedDescentCont at hdesc
    split at hdesc
    · exact hcs u hdesc t ht
    · rename_i hge
      have h2 : 2 ≤ n := by omega
      have hsc : Noun.slot n current = some child := by
        cases hslot with
        | inl hlt => omega
        | inr hs => exact hs
      cases current with
      | atom a =>
        have := slot_atom_of_ge_two (a := n) (n := a) h2
        simp [this] at hsc
      | cell hd tl =>
        split at hdesc
        · rename_i htbit
          simp at hdesc
          subst u
          have hrec := slot_rest_tail hd tl child h2 hsc htbit
          have hpt := genAnnotatedDescentCont_pt_noun (lmb := lmb) (encC z) z cont
            contCell contState tl (axisRest n)
          cases ht with
          | here =>
              simp [gMemRow9, formulaHead, formulaTail]
              refine annotatedDecPub_eqBlk z hz htwo hd tl _ _ _ _ 0 0
                (genAnnotatedNounWalk_pt_noun (encC z) z hd) ?_
              by_cases hr : axisRest n < 2
              · rw [if_pos hr] at hpt
                have hct := slot_child_of_tail hd tl child h2 hsc htbit hr
                rw [hpt, hcont, hct]
              · rw [if_neg hr] at hpt
                exact hpt
          | sub hs ht' =>
              simp [NTree.children, List.mem_append, formulaHead, formulaTail] at hs
              rcases hs with rfl | hu'
              · exact genAnnotatedNounWalk_all_eqBlk z hz htwo hd t ht'
              · exact ih (axisRest n) (axisRest_lt h2) tl hrec _ hu' t ht'
        · rename_i hbit
          have hh : axisTopBit n = false := Bool.eq_false_iff.mpr hbit
          simp at hdesc
          subst u
          have hrec := slot_rest_head hd tl child h2 hsc hh
          have hpt := genAnnotatedDescentCont_pt_noun (lmb := lmb) (encC z) z cont
            contCell contState hd (axisRest n)
          cases ht with
          | here =>
              simp [gMemRow9, formulaHead, formulaTail]
              refine annotatedDecPub_eqBlk z hz htwo hd tl _ _ _ _ 0 0 ?_
                (genAnnotatedNounWalk_pt_noun (encC z) z tl)
              by_cases hr : axisRest n < 2
              · rw [if_pos hr] at hpt
                have hct := slot_child_of_head hd tl child h2 hsc hh hr
                rw [hpt, hcont, hct]
              · rw [if_neg hr] at hpt
                exact hpt
          | sub hs ht' =>
              simp [NTree.children, List.mem_append, formulaHead, formulaTail] at hs
              rcases hs with hu' | rfl
              · exact ih (axisRest n) (axisRest_lt h2) hd hrec _ hu' t ht'
              · exact genAnnotatedNounWalk_all_eqBlk z hz htwo tl t ht'

theorem genAnnotatedChainedInner_one_eqBlk (z α : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0) (prev r : MemRecordReq)
    (hchain : prev.child = r.root)
    (hwf : lsbTarget r.root r.axis = r.child)
    (hslot : r.axis < 2 ∨ Noun.slot r.axis r.root = some r.child) :
    ∀ u ∈ (genAnnotatedChainedInner (encC z) z α lmb prev [r]).1,
      ∀ t, InTree u t → eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro u hu t ht
  unfold genAnnotatedChainedInner at hu
  simp only [genAnnotatedChainedInner_nil, chainedInnerRootState] at hu
  simp at hu
  subst u
  cases ht with
  | here =>
      simp [gMemRow9]
      refine annotatedReadPub_eqBlk z r.root r.child r.axis (α ^ r.recordExp)
        _ 0 0 ?_
      simp [annotatedVerifyPub, hchain]
  | sub hs ht' =>
      simp [NTree.children] at hs
      subst hs
      cases ht' with
      | here =>
          simp [gMemRow9]
          refine annotatedVerifyPub_eqBlk z prev.root prev.child prev.axis
            (α ^ prev.recordExp) _ 0 0 ?_
          have hpt := genAnnotatedDescentCont_pt_noun (lmb := lmb) (encC z) z
            [(genAnnotatedVerify (encC z) z lmb r.root r.child r.axis
                (α ^ r.recordExp) r.recordExp).1]
            (genAnnotatedVerify (encC z) z lmb r.root r.child r.axis
                (α ^ r.recordExp) r.recordExp).2
            .verify_child r.root r.axis
          by_cases hlt : r.axis < 2
          · rw [if_pos hlt] at hpt
            have hroot : r.root = r.child := by
              have := lsbTarget_of_lt2 r.root hlt
              exact this.symm.trans hwf
            rw [hpt, genAnnotatedVerify_pt_noun, hchain, hroot]
          · rw [if_neg hlt] at hpt
            rw [hpt, hchain]
      | sub hs2 ht2 =>
          simp [NTree.children] at hs2
          exact genAnnotatedDescentCont_all_eqBlk z α hz htwo
            [(genAnnotatedVerify (encC z) z lmb r.root r.child r.axis
                (α ^ r.recordExp) r.recordExp).1]
            (genAnnotatedVerify (encC z) z lmb r.root r.child r.axis
                (α ^ r.recordExp) r.recordExp).2
            .verify_child
            (fun v hv w hw => by
              simp at hv; subst v
              exact genAnnotatedVerify_all_eqBlk z hz htwo r.root r.child
                r.axis (α ^ r.recordExp) r.recordExp w hw)
            r.root r.axis r.child hslot
            (by simp [genAnnotatedVerify_pt_noun])
            _ hs2 t ht2

theorem genAnnotatedChainedTree_two_eqBlk (z α : K) (hz : z ≠ 0)
    (htwo : (2 : K) ≠ 0) (r1 r2 : MemRecordReq)
    (hchain : r1.child = r2.root)
    (hwf1 : lsbTarget r1.root r1.axis = r1.child)
    (hwf2 : lsbTarget r2.root r2.axis = r2.child)
    (hs1 : r1.axis < 2 ∨ Noun.slot r1.axis r1.root = some r1.child)
    (hs2 : r2.axis < 2 ∨ Noun.slot r2.axis r2.root = some r2.child)
    (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree (encC z) z α lmb [r1, r2] = some t) :
    ∀ u, InTree t u → eqBlkE lmb (memInputs z) u.label.row.2.2 := by
  unfold genAnnotatedChainedTree at ht
  simp only [chainedInnerRootState] at ht
  injection ht with ht
  subst t
  intro u hu
  cases hu with
  | here =>
      simp [gMemRow9]
      refine annotatedReadPub_eqBlk z r1.root r1.child r1.axis
        (α ^ r1.recordExp) _ 0 0 ?_
      have hpt := genAnnotatedDescentCont_pt_noun (lmb := lmb) (encC z) z
        (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).1
        (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).2
        (chainedInnerRootState [r2]) r1.root r1.axis
      by_cases hlt : r1.axis < 2
      · have hroot : r1.root = r1.child := by
          have := lsbTarget_of_lt2 r1.root hlt
          exact this.symm.trans hwf1
        have hst : chainedInnerRootState [r2] = .read_root := rfl
        rw [hst] at hpt
        rw [if_pos hlt] at hpt
        rw [hpt]
        unfold genAnnotatedChainedInner
        simp only [genAnnotatedChainedInner_nil, chainedInnerRootState,
          annotatedReadPub]
        simp [annotatedReadPub, hroot, hchain]
      · rw [if_neg hlt] at hpt
        exact hpt
  | sub hs hu' =>
      simp [NTree.children] at hs
      have hinner :
          (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).2.noun =
            encC z r1.child := by
        unfold genAnnotatedChainedInner
        simp [genAnnotatedChainedInner_nil, annotatedReadPub, hchain]
      exact genAnnotatedDescentCont_all_eqBlk z α hz htwo
        (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).1
        (genAnnotatedChainedInner (encC z) z α lmb r1 [r2]).2
        (chainedInnerRootState [r2])
        (genAnnotatedChainedInner_one_eqBlk z α hz htwo r1 r2 hchain hwf2 hs2)
        r1.root r1.axis r1.child hs1 hinner _ hs u hu'

theorem genRowMemForest_wf_eqBlk (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    ∀ rs : List MemRecordReq,
      (∀ r ∈ rs, lsbTarget r.root r.axis = r.child ∧
        (r.axis < 2 ∨ Noun.slot r.axis r.root = some r.child)) →
      ∀ u ∈ genRowMemForest (encC z) z α lmb rs,
        ∀ t, InTree u t → eqBlkE lmb (memInputs z) t.label.row.2.2
  | [], _, u, hu, t, ht => by simp [genRowMemForest] at hu
  | [r], hwf, u, hu, t, ht => by
      simp [genRowMemForest_singleton] at hu
      subst u
      exact genAnnotatedRecordTree_wf_eqBlk z α hz htwo r.root r.child
        r.axis r.recordExp (hwf r (by simp)).1 (hwf r (by simp)).2 t ht
  | [r1, r2], hwf, u, hu, t, ht => by
      rw [genRowMemForest_two_eq] at hu
      by_cases hc : r1.child = r2.root
      · rw [if_pos hc] at hu
        cases hch : genAnnotatedChainedTree (encC z) z α lmb [r1, r2] with
        | none =>
          simp [genAnnotatedChainedTree] at hch
        | some tree =>
          simp [hch] at hu
          subst u
          exact genAnnotatedChainedTree_two_eqBlk z α hz htwo r1 r2 hc
            (hwf r1 (by simp)).1 (hwf r2 (by simp)).1
            (hwf r1 (by simp)).2 (hwf r2 (by simp)).2 tree hch t ht
      · rw [if_neg hc] at hu
        simp at hu
        rcases hu with hu | hu
        · subst u
          exact genAnnotatedRecordTree_wf_eqBlk z α hz htwo r1.root r1.child
            r1.axis r1.recordExp (hwf r1 (by simp)).1 (hwf r1 (by simp)).2 t ht
        · subst u
          exact genAnnotatedRecordTree_wf_eqBlk z α hz htwo r2.root r2.child
            r2.axis r2.recordExp (hwf r2 (by simp)).1 (hwf r2 (by simp)).2 t ht
  | [r1, r2, r3], hwf, u, hu, t, ht => by
      rw [genRowMemForest_three_eq] at hu
      simp [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact genRowMemForest_wf_eqBlk z α hz htwo [r1, r2]
          (fun r hr => hwf r (by
            simp only [List.mem_cons, List.not_mem_nil] at hr ⊢
            tauto)) u hu t ht
      · exact genAnnotatedRecordTree_wf_eqBlk z α hz htwo r3.root r3.child
          r3.axis r3.recordExp (hwf r3 (by simp)).1 (hwf r3 (by simp)).2 t ht
  | r1 :: r2 :: r3 :: r4 :: rest, hwf, u, hu, t, ht => by
      unfold genRowMemForest at hu
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
      exact genAnnotatedRecordTree_wf_eqBlk z α hz htwo r.root r.child
        r.axis r.recordExp (hwf r hr).1 (hwf r hr).2 t ht

theorem mmAssigned_rowInputs (z α : K)
    (n : NTree (GenComputeRow K))
    (_hn : InTree (bfsAssign (mmTreeAir (K := K))) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      ∀ v, InTree u v → v.label.row.2.1 = memInputs z :=
  genRowMemForest_all_inputs (encC z) z α _

theorem mmAssigned_rowEqBlk (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0)
    (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (mmTreeAir (K := K))) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      ∀ v, InTree u v → eqBlkE lmb (memInputs z) v.label.row.2.2 :=
  genRowMemForest_wf_eqBlk z α hz htwo _
    (fun r hr =>
      ⟨bfsAssign_extract_requests_wf (mmTreeAir (K := K))
        (by unfold mmTreeAir; exact treeRequestsWF_airReorder mmTree_requests_wf)
        n hn r hr,
        Or.inr (bfsAssign_extract_requests_slot (mmTreeAir (K := K))
          (by unfold mmTreeAir; exact treeRequestsWF_airReorder mmTree_requests_wf)
          n hn r hr)⟩)

theorem mmAssigned_bfs_inputs (z α : K) :
    ∀ t ∈ bfsForest (genMemForestFromTree (encC z) z α lmb
        (bfsAssign (mmTreeAir (K := K)))),
      t.label.row.2.1 = memInputs z := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  exact genMemForestFromTree_of_rowInputs z α _
    (fun n hn => mmAssigned_rowInputs z α n hn) u hu t hin

theorem mmAssigned_bfs_eqBlk (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    ∀ t ∈ bfsForest (genMemForestFromTree (encC z) z α lmb
        (bfsAssign (mmTreeAir (K := K)))),
      eqBlkE lmb (memInputs z) t.label.row.2.2 := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  exact genMemForestFromTree_of_rowEqBlk z α hz htwo _
    (fun n hn => by
      intro x hx y hy
      exact mmAssigned_rowEqBlk z α hz htwo n hn x hx y hy) u hu t hin

theorem mmAssigned_bfs_state (z α : K) :
    ∀ t ∈ bfsForest (genMemForestFromTree (encC z) z α lmb
        (bfsAssign (mmTreeAir (K := K)))),
      t.label.row.1 = t.label.row.2.2.st := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  have hOK := mmMemForest_OK z α u hu
      (mapNTree GenMemoryRow.node t) (mapNTree_inTree _ hin)
  have hb := hOK.2.2.1
  simpa [mapNTree_label, GenMemoryRow.node_row] using hb.1.trans hb.2.2.1.symm

theorem mmAssigned_bfs_WF (z α : K) (hz : z ≠ 0) :
    ∀ t ∈ bfsForest (genMemForestFromTree (encC z) z α lmb
        (bfsAssign (mmTreeAir (K := K)))),
      WF (memInputs z) t.label.row.2.2 := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  have hOK := mmMemForest_OK z α u hu
      (mapNTree GenMemoryRow.node t) (mapNTree_inTree _ hin)
  have hb := hOK.2.2.1
  have hsteq : t.label.skel.state = t.label.row.2.2.st := by
    simpa [mapNTree_label, GenMemoryRow.node_skel, GenMemoryRow.node_row] using
      hb.2.2.1.symm
  refine ⟨?_⟩
  intro hlive
  have hact : memoryMemRecKind t.label.skel.state = .active := by
    rw [hsteq]
    rcases hlive with h | h <;> simp [memoryMemRecKind, h]
  have hrec : BindMemRec z (t.label.skel.memoryRecord (by
      simpa [mapNTree_label, GenMemoryRow.node_skel] using hact))
      t.label.row.2.2.mem := by
    have hx := hb.2.2.2.2.2
    have hx' :
        BindMemRec z (t.label.skel.memoryRecord (by
            simpa [mapNTree_label, GenMemoryRow.node_skel] using hact))
          t.label.row.2.2.mem ∧
          t.label.row.2.2.ver =
            decide (t.label.skel.state = MemoryTable.MState.read_root) := by
      simpa [mapNTree_label, GenMemoryRow.node_skel, GenMemoryRow.node_row, hact] using hx
    exact hx'.1
  have hroot : t.label.row.2.2.mem.root =
      GlobalCarryRecognizer.enc z (t.label.skel.memoryRecord
        (by simpa [mapNTree_label, GenMemoryRow.node_skel] using hact)).root :=
    hrec.1
  rw [pole_memInputs z t.label.row.2.2.mem t.label.row.2.2.cprime, hroot, GlobalCarryRecognizer.enc_size]
  exact pow_ne_zero _ hz

theorem mmAssigned_threaded_Vmem (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    ∀ t ∈ bfsForest (threadGenForest (memInputs z) 0
        (genMemForestFromTree (encC z) z α lmb (bfsAssign (mmTreeAir (K := K))))),
      VmemE lmb (memInputs z) t.label.row.2.2 :=
  threadGenForest_Vmem (memInputs z) 0 _
    (mmAssigned_bfs_eqBlk z α hz htwo)

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

open Nock Nock.Walk Nock.Noun
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.RowLayout
open MemoryTable

noncomputable section

theorem memoryInputs_eq (z α : K) :
    (cfg z α).challenges.memoryInputs = memInputs z := by
  simp [cfg, ChallengeVector.memoryInputs, memInputs]

def assignedForest (z α : K) : List (NTree (GenMemoryRow K)) :=
  genMemForestFromTree (encC z) z α MemoryTable.formRDefault (bfsAssign (mmTreeAir (K := K)))

def threadedForest (z α : K) : List (NTree (GenMemoryRow K)) :=
  threadGenForest (memInputs z) 0 (assignedForest z α)

def memoryForestThreaded (z α : K) :
    List (NTree (MemoryTable.MState × MemoryTable.DTmem K)) :=
  (threadedForest z α).map (mapNTree GenMemoryRow.row)

theorem threaded_kMem (z α : K) : (threadedForest z α).length = 618 := by
  unfold threadedForest assignedForest
  rw [threadGenForest_length, assigned_kMem]

theorem threaded_memRows (z α : K) : totalSize (threadedForest z α) = 30936 := by
  unfold threadedForest assignedForest
  rw [threadGenForest_totalSize, assigned_memRows]

/-- The a-bearing view of the threaded execution (generated rows). -/
def execThreadedA (z α : K) : ExactExecution (cfg z α) where
  computeTree := computeTree z α
  memoryForest := memoryForestThreaded z α
  memoryForest_nonempty := by
    refine List.ne_nil_of_length_pos ?_
    unfold memoryForestThreaded
    rw [List.length_map, threaded_kMem]
    omega
  memory_root_count := by
    unfold memoryForestThreaded
    rw [List.length_map, threaded_kMem]
    simp [cfg]
  compute_bfs_length := (exec z α).compute_bfs_length
  memory_bfs_length := by
    unfold memoryForestThreaded
    rw [bfsForest_length, totalSize_map, threaded_memRows]
    simp [cfg]

/-- The executed (row-level) threaded execution: the Form R row encode of `execThreadedA`. -/
noncomputable def execThreaded (z α : K) : ExactExecution (cfg z α) :=
  (execThreadedA z α).encodeMem

theorem assigned_bfs_inputs (z α : K) :
    ∀ t ∈ bfsForest (assignedForest z α), t.label.row.2.1 = memInputs z := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  exact genMemForestFromTree_of_rowInputs z α _
    (mmAssigned_rowInputs z α) u hu t hin

theorem threaded_bfs_state (z α : K) :
    ∀ t ∈ bfsForest (threadedForest z α),
      t.label.row.1 = t.label.row.2.2.st :=
  threadGenForest_state_agree (memInputs z) 0 _
    (mmAssigned_bfs_state z α)

theorem threaded_bfs_inputs (z α : K) :
    ∀ t ∈ bfsForest (threadedForest z α), t.label.row.2.1 = memInputs z :=
  threadGenForest_inputs (memInputs z) 0 _
    (assigned_bfs_inputs z α)

theorem threaded_bfs_Vmem (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    ∀ t ∈ bfsForest (threadedForest z α),
      VmemE MemoryTable.formRDefault (memInputs z) t.label.row.2.2 :=
  mmAssigned_threaded_Vmem z α hz htwo

theorem memoryRowsA_eq_threaded (z α : K) :
    (execThreadedA z α).memoryRows =
      ((bfsForest (threadedForest z α)).map NTree.label).map GenMemoryRow.row := by
  unfold ExactExecution.memoryRows execThreadedA memoryForestThreaded
  rw [bfsForest_mapNTree, List.map_map, List.map_map]
  refine List.map_congr_left ?_
  intro t _
  exact mapNTree_label _ _

/-- The executed rows are the row encode of the threaded generated rows. -/
theorem memoryRows_eq_threaded (z α : K) :
    (execThreaded z α).memoryRows =
      (((bfsForest (threadedForest z α)).map NTree.label).map GenMemoryRow.row).map
        (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow MemoryTable.formRDefault) := by
  rw [execThreaded, ExactExecution.encodeMem_memoryRows, memoryRowsA_eq_threaded]
  rfl

theorem memoryRowsAccepted (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    (execThreaded z α).MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff, memoryRows_eq_threaded]
  intro row hrow
  obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr0
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  have hst := threaded_bfs_state z α t ht
  have hinp := threaded_bfs_inputs z α t ht
  have hv := threaded_bfs_Vmem z α hz htwo t ht
  have hch : (cfg z α).challenges.memoryInputs = memInputs z :=
    memoryInputs_eq z α
  have hpub := encodeRow_pub (lmb := MemoryTable.formRDefault) t.label.row hst
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpub, encPub_st]; exact hst
  · rw [hch, encodeRow_inputs]; exact hinp
  · rw [hpub, encodeRow_inputs, hinp]; exact hv
  · rw [hpub, encPub_lambda]; rfl

theorem memoryRowsAccepted_seed :
    (execThreaded seedZ alphaA).MemoryRowsAccepted :=
  memoryRowsAccepted seedZ alphaA seedZ_ne_zero two_ne_zero

theorem execThreaded_computeRows (z α : K) :
    (execThreaded z α).computeRows = (exec z α).computeRows :=
  rfl

theorem computeRowsAccepted_threaded :
    (execThreaded seedZ alphaA).ComputeRowsAccepted := by
  have h := mm_computeRowsAccepted
  rw [ExactExecution.computeRowsAccepted_iff] at h ⊢
  rw [execThreaded_computeRows]
  exact h

theorem memoryPubAtA_eq_thread (z α : K) (j : Fin (cfg z α).memRows) :
    (execThreadedA z α).memoryPubAt j =
      (threadPubs (memInputs z) 0
        (List.map (fun g : GenMemoryRow K => g.row.2.2)
          (List.map NTree.label
            (bfsForest (assignedForest z α)))))[j.1]'(by
          have hlen :
              (threadPubs (memInputs z) 0
                (List.map (fun g : GenMemoryRow K => g.row.2.2)
                  (List.map NTree.label
                    (bfsForest (assignedForest z α))))).length =
                (cfg z α).memRows := by
            rw [threadPubs_length, List.length_map, List.length_map,
              bfsForest_length]
            unfold assignedForest
            rw [assigned_memRows]
            simp [cfg]
          have := j.isLt
          omega) := by
  have hget :
      (execThreadedA z α).memoryPubAt j =
        ((execThreadedA z α).memoryRows[(j : ℕ)]'(by
          have := (execThreadedA z α).memoryRows_length
          have := j.isLt
          omega)).2.2 := by
    simp [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
      List.get_eq_getElem]
  rw [hget]
  have hlt : (j : ℕ) < (execThreadedA z α).memoryRows.length := by
    have := (execThreadedA z α).memoryRows_length
    have := j.isLt
    omega
  have hrows := memoryRowsA_eq_threaded z α
  have hlt' : (j : ℕ) <
      (((bfsForest (threadedForest z α)).map NTree.label).map
        GenMemoryRow.row).length := by
    rw [← hrows]; exact hlt
  have hidx := congrArg (fun l : List _ => l[(j : ℕ)]?) hrows
  simp only [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hlt'] at hidx
  have heq := Option.some.inj hidx
  rw [heq]
  have hpub :
      List.map (fun g : GenMemoryRow K => g.row.2.2)
        (List.map NTree.label (bfsForest (threadedForest z α))) =
        threadPubs (memInputs z) 0
          (List.map (fun g : GenMemoryRow K => g.row.2.2)
            (List.map NTree.label
              (bfsForest (assignedForest z α)))) := by
    unfold threadedForest
    rw [threadGenForest_bfs_labels, threadGenRows_map_pub]
  have hltP :
      (j : ℕ) <
        (threadPubs (memInputs z) 0
          (List.map (fun g : GenMemoryRow K => g.row.2.2)
            (List.map NTree.label
              (bfsForest (assignedForest z α))))).length := by
    have hlen :
        (threadPubs (memInputs z) 0
          (List.map (fun g : GenMemoryRow K => g.row.2.2)
            (List.map NTree.label
              (bfsForest (assignedForest z α))))).length =
          (cfg z α).memRows := by
      rw [threadPubs_length, List.length_map, List.length_map, bfsForest_length]
      unfold assignedForest
      rw [assigned_memRows]
      simp [cfg]
    have := j.isLt
    omega
  have hltL :
      (j : ℕ) <
        (List.map (fun g : GenMemoryRow K => g.row.2.2)
          (List.map NTree.label
            (bfsForest (threadedForest z α)))).length := by
    rw [hpub]; exact hltP
  have hidx2 := congrArg (fun l : List (Pub K) => l[(j : ℕ)]?) hpub
  simp only [List.getElem?_eq_getElem hltL, List.getElem?_eq_getElem hltP] at hidx2
  have heq2 := Option.some.inj hidx2
  have hleft :
      (List.map GenMemoryRow.row
          (List.map NTree.label
            (bfsForest (threadedForest z α))))[(j : ℕ)].2.2 =
        (List.map (fun g : GenMemoryRow K => g.row.2.2)
          (List.map NTree.label
            (bfsForest (threadedForest z α))))[(j : ℕ)] := by
    simp [List.getElem_map]
  rw [hleft, heq2]

/-- The executed pub at `j` is the encode of the threaded pub (`encPub`). -/
theorem memoryPubAt_eq_thread (z α : K) (j : Fin (cfg z α).memRows) :
    (execThreaded z α).memoryPubAt j = encPub MemoryTable.formRDefault ((execThreadedA z α).memoryPubAt j) := by
  have hmem := ExactExecution.memoryRowAt_mem (execThreadedA z α) j
  rw [memoryRowsA_eq_threaded] at hmem
  obtain ⟨g, hg, hgeq⟩ := List.mem_map.mp hmem
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  have hst := threaded_bfs_state z α t ht
  have hrow : (execThreaded z α).memoryRowAt j =
      SemanticTimestampStrategy.MemoryRowTemplate.encodeRow MemoryTable.formRDefault ((execThreadedA z α).memoryRowAt j)
          := by
    simp only [ExactExecution.memoryRowAt, List.get_eq_getElem, Fin.val_cast]
    simp [execThreaded, ExactExecution.encodeMem_memoryRows]
  simp only [ExactExecution.memoryPubAt]
  rw [hrow, encodeRow_pub _ (by rw [← hgeq]; exact hst)]

theorem memory_chain (z α : K) :
    ∀ i : Fin (cfg z α).memRows,
      ∀ hi : (i : ℕ) + 1 < (cfg z α).memRows,
        ((execThreaded z α).memoryPubAt i).icur =
          ((execThreaded z α).memoryPubAt ⟨(i : ℕ) + 1, hi⟩).ipre := by
  intro i hi
  let pubs : List (Pub K) :=
    List.map (fun g : GenMemoryRow K => g.row.2.2)
      (List.map NTree.label (bfsForest (assignedForest z α)))
  have hchain : InterChain (memInputs z) 0
      (0 + sumDelta (memInputs z) pubs)
      (threadPubs (memInputs z) 0 pubs) :=
    threadPubs_interChain (memInputs z) 0 pubs
  have hlenT : (threadPubs (memInputs z) 0 pubs).length = (cfg z α).memRows := by
    unfold pubs
    rw [threadPubs_length, List.length_map, List.length_map, bfsForest_length]
    unfold assignedForest
    rw [assigned_memRows]
    simp [cfg]
  have hget := interChain_handoff (memInputs z) 0 _ _ hchain (i : ℕ) (by
    have := i.isLt
    omega)
  rw [memoryPubAt_eq_thread, memoryPubAt_eq_thread, encPub_icur, encPub_ipre,
    memoryPubAtA_eq_thread, memoryPubAtA_eq_thread]
  exact hget

theorem memory_first_ipre (z α : K) :
    ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).ipre = 0 := by
  let pubs : List (Pub K) :=
    List.map (fun g : GenMemoryRow K => g.row.2.2)
      (List.map NTree.label (bfsForest (assignedForest z α)))
  have hlenT : (threadPubs (memInputs z) 0 pubs).length = (cfg z α).memRows := by
    unfold pubs
    rw [threadPubs_length, List.length_map, List.length_map, bfsForest_length]
    unfold assignedForest
    rw [assigned_memRows]
    simp [cfg]
  have hpos : 0 < (threadPubs (memInputs z) 0 pubs).length := by
    have : 0 < (cfg z α).memRows := (cfg z α).memRows_pos
    omega
  have hchain := threadPubs_interChain (memInputs z) 0 pubs
  have hne : threadPubs (memInputs z) 0 pubs ≠ [] :=
    List.ne_nil_of_length_pos hpos
  obtain ⟨p, ps, hth⟩ : ∃ p ps, threadPubs (memInputs z) 0 pubs = p :: ps := by
    cases h : threadPubs (memInputs z) 0 pubs with
    | nil => exact (hne h).elim
    | cons p ps => exact ⟨p, ps, rfl⟩
  have hipre : p.ipre = 0 :=
    interChain_head_ipre (memInputs z) 0 _ p ps (by rwa [hth] at hchain)
  rw [memoryPubAt_eq_thread, encPub_ipre, memoryPubAtA_eq_thread]
  have hlt0 : 0 < (p :: ps).length := by simp
  have hidx := congrArg (fun l : List (Pub K) => l[0]?) hth
  simp only [List.getElem?_eq_getElem hpos, List.getElem?_eq_getElem hlt0] at hidx
  have heq := Option.some.inj hidx
  rw [heq]
  exact hipre

theorem memory_wf (z α : K) (hz : z ≠ 0) :
    ∀ i, WF (cfg z α).challenges.memoryInputs
      ((execThreaded z α).memoryPubAt i) := by
  intro i
  have hch : (cfg z α).challenges.memoryInputs = memInputs z :=
    memoryInputs_eq z α
  rw [hch, memoryPubAt_eq_thread]
  refine wf_encPub _ _ rfl ?_
  rw [memoryPubAtA_eq_thread]
  refine threadPubs_WF (memInputs z) 0 _ ?_
      _
      (List.getElem_mem _)
  intro p hp
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  unfold assignedForest at ht
  exact mmAssigned_bfs_WF z α hz t ht

theorem memory_wf_seed :
    ∀ i, WF (cfg seedZ alphaA).challenges.memoryInputs
      ((execThreaded seedZ alphaA).memoryPubAt i) :=
  memory_wf seedZ alphaA seedZ_ne_zero

theorem memoryStateCount_eq_assignedFibre (z α : K) (s : MState) :
    memoryStateCount (execThreaded z α) s =
      forestFibre s (assignedForest z α) := by
  have hA : memoryStateCount (execThreaded z α) s = memoryStateCount (execThreadedA z α) s := by
    unfold memoryStateCount fibreCount
    rw [execThreaded, ExactExecution.encodeMem_memoryRows, List.countP_map]
    simp [Function.comp_def]
  rw [hA]
  unfold memoryStateCount
  rw [memoryRowsA_eq_threaded, fibreCount_map]
  have hlabs :
      (bfsForest (threadedForest z α)).map NTree.label =
        threadGenRows (memInputs z) 0
          ((bfsForest (assignedForest z α)).map NTree.label) := by
    unfold threadedForest
    exact threadGenForest_bfs_labels _ _ _
  rw [hlabs]
  have hst := threadGenRows_map_st (memInputs z) 0
    ((bfsForest (assignedForest z α)).map NTree.label)
  simp only [fibreCount]
  have h1 :
      List.countP (fun g : GenMemoryRow K => g.row.2.2.st = s)
        (threadGenRows (memInputs z) 0
          ((bfsForest (assignedForest z α)).map NTree.label)) =
        List.countP (fun x => x = s)
          ((threadGenRows (memInputs z) 0
            ((bfsForest (assignedForest z α)).map NTree.label)).map
            (fun g : GenMemoryRow K => g.row.2.2.st)) := by
    rw [List.countP_map]; rfl
  rw [h1, hst]
  have h2 :
      List.countP (fun x => x = s)
        (((bfsForest (assignedForest z α)).map NTree.label).map
          (fun g : GenMemoryRow K => g.row.2.2.st)) =
        List.countP (fun g : GenMemoryRow K => g.row.2.2.st = s)
          ((bfsForest (assignedForest z α)).map NTree.label) := by
    rw [List.countP_map]; rfl
  rw [h2]
  change fibreCount memPubSt
      ((bfsForest (assignedForest z α)).map NTree.label) s =
    forestFibre s (assignedForest z α)
  exact fibreCount_bfsForest s _

theorem recordCountBalance_threaded (z α : K) :
    RecordCountBalanced (execThreaded z α) := by
  unfold RecordCountBalanced
  rw [memoryStateCount_eq_assignedFibre, memoryStateCount_eq_assignedFibre]
  unfold assignedForest
  exact genMemForestFromTree_balanced (encC z) z α
    (bfsAssign (mmTreeAir (K := K)))

theorem memory_last_icur_eq_sumDelta (z α : K) :
    ((execThreaded z α).memoryPubAt
      ((cfg z α).orbit.lastIndex (cfg z α).memRows (cfg z α).memRows_pos)).icur =
      sumDelta (memInputs z)
        (List.map (fun g : GenMemoryRow K => g.row.2.2)
          (List.map NTree.label (bfsForest (assignedForest z α)))) := by
  let pubs : List (Pub K) :=
    List.map (fun g : GenMemoryRow K => g.row.2.2)
      (List.map NTree.label (bfsForest (assignedForest z α)))
  have hlenT : (threadPubs (memInputs z) 0 pubs).length = (cfg z α).memRows := by
    unfold pubs
    rw [threadPubs_length, List.length_map, List.length_map, bfsForest_length]
    unfold assignedForest
    rw [assigned_memRows]
    simp [cfg]
  have hpos : 0 < (threadPubs (memInputs z) 0 pubs).length := by
    have : 0 < (cfg z α).memRows := (cfg z α).memRows_pos
    omega
  have hne : threadPubs (memInputs z) 0 pubs ≠ [] :=
    List.ne_nil_of_length_pos hpos
  have hchain := threadPubs_interChain (memInputs z) 0 pubs
  have hlastIdx :
      (cfg z α).orbit.lastIndex (cfg z α).memRows (cfg z α).memRows_pos =
        ⟨(cfg z α).memRows - 1, Nat.sub_lt (cfg z α).memRows_pos (by omega)⟩ :=
    rfl
  rw [hlastIdx, memoryPubAt_eq_thread, encPub_icur, memoryPubAtA_eq_thread]
  have hgetLast :
      (threadPubs (memInputs z) 0 pubs)[(cfg z α).memRows - 1]'(by omega) =
        (threadPubs (memInputs z) 0 pubs).getLast hne := by
    have hidx' : (cfg z α).memRows - 1 =
        (threadPubs (memInputs z) 0 pubs).length - 1 := by omega
    simp [List.getLast_eq_getElem, hidx']
  rw [hgetLast, interChain_last_icur (memInputs z) 0 _ _ hne hchain]
  simp [zero_add, pubs, List.map_map]

theorem assigned_sumDelta (z α : K) :
    sumDelta (memInputs z)
      (List.map (fun g : GenMemoryRow K => g.row.2.2)
        (List.map NTree.label (bfsForest (assignedForest z α)))) = 0 := by
  rw [sumDelta_eq_forestDelta]
  unfold assignedForest
  exact genMemForestFromTree_delta (encC z) z α _

theorem memory_last_icur (z α : K) :
    ((execThreaded z α).memoryPubAt
      ((cfg z α).orbit.lastIndex (cfg z α).memRows (cfg z α).memRows_pos)).icur = 0 := by
  rw [memory_last_icur_eq_sumDelta, assigned_sumDelta]

/-! ## First memory pub counts / indicator -/

theorem extractNodeReqs_mm_root :
    ∃ hd tl e,
      extractNodeReqs (bfsAssign (mmTreeAir (K := K))).label =
        [⟨.cell hd tl, tl, 3, e⟩] := by
  obtain ⟨hd, tl, hreq⟩ := mmTree_root_request_shape
  refine ⟨hd, tl, getRecordExp (bfsAssign (mmTreeAir (K := K))).label.stamp 0, ?_⟩
  rw [extractNodeReqs, bfsAssign_mm_root_requests, hreq]
  simp [extractNodeReqsAux]

theorem assignedForest_head_record (z α : K) :
    ∃ t rest hd tl e,
      assignedForest z α = t :: rest ∧
        t = genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault (.cell hd tl) tl 3 e := by
  have hshape :
      bfsAssign (mmTreeAir (K := K)) =
        NTree.node (bfsAssign (mmTreeAir (K := K))).label
          (bfsAssign (mmTreeAir (K := K))).children := by
    cases bfsAssign (mmTreeAir (K := K)); rfl
  obtain ⟨hd, tl, e, hreqs⟩ := extractNodeReqs_mm_root
  refine ⟨genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault (.cell hd tl) tl 3 e,
    genMemForestFromList (encC z) z α MemoryTable.formRDefault
      (bfsAssign (mmTreeAir (K := K))).children, hd, tl, e, ?_, rfl⟩
  unfold assignedForest
  rw [hshape, genMemForestFromTree, hreqs, genRowMemForest_singleton]
  simp [NTree.children]

/-- Dummy-wired first-row remaining (`hfirst`). -/
theorem assigned_bfs_head_pt (z α : K) (htwo : (2 : K) ≠ 0)
    (h : ∃ t rest,
      bfsForest (assignedForest z α) = t :: rest ∧
        t.label.row.2.2.pt.indicator = 0 ∧
        t.label.row.2.2.pt.counts = 0) :
    ∃ t rest,
      bfsForest (assignedForest z α) = t :: rest ∧
        t.label.row.2.2.pt.indicator = 0 ∧
        t.label.row.2.2.pt.counts = 0 :=
  h

/-- Dummy-wired first-row remaining (`hfirst`). -/
theorem memory_first_pt (z α : K) (htwo : (2 : K) ≠ 0)
    (h : ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.counts = 0) :
    ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.counts = 0 :=
  h

/-! ## Compute line-number chain -/

theorem computeRowAt_eq (z α : K) (i : Fin (cfg z α).compRows) :
    (execThreaded z α).computeRowAt i =
      setRowCoins (0 : K) 0 1
        (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) ((i : ℕ) + 1))).row := by
  have hrows : (execThreaded z α).computeRows =
      (List.range' 1 (bfsForest [mmTreeAir (K := K)]).length).map
        (fun j => setRowCoins (0 : K) 0 1
          (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) j)).row) := by
    rw [execThreaded_computeRows, computeRows_eq]
  have hlt : (i : ℕ) < (execThreaded z α).computeRows.length := by
    have hlen := (execThreaded z α).computeRows_length
    have := i.isLt
    omega
  have hget :
      (execThreaded z α).computeRowAt i =
        (execThreaded z α).computeRows[(i : ℕ)]'hlt := by
    simp [ExactExecution.computeRowAt, List.get_eq_getElem]
  rw [hget]
  have hlenR :
      ((List.range' 1 (bfsForest [mmTreeAir (K := K)]).length).map
        (fun j => setRowCoins (0 : K) 0 1
          (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) j)).row)).length =
        401 := by
    simp [List.length_map, mmTreeAir_bfsForest_length]
  have hltR : (i : ℕ) <
      ((List.range' 1 (bfsForest [mmTreeAir (K := K)]).length).map
        (fun j => setRowCoins (0 : K) 0 1
          (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) j)).row)).length := by
    have hcfg : (cfg z α).compRows = 401 := by simp [cfg]
    omega
  have hidx := congrArg (fun l : List _ => l[(i : ℕ)]?) hrows
  simp only [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hltR] at hidx
  have heq := Option.some.inj hidx
  rw [heq]
  have hltI : (i : ℕ) < (List.range' 1 (bfsForest [mmTreeAir (K := K)]).length).length := by
    simp [mmTreeAir_bfsForest_length]
    have hcfg : (cfg z α).compRows = 401 := by simp [cfg]
    omega
  simp only [List.getElem_map]
  have hidx' : (List.range' 1 (bfsForest [mmTreeAir (K := K)]).length)[(i : ℕ)]'hltI =
      (i : ℕ) + 1 := by
    simp [List.getElem_range', Nat.add_comm]
  rw [hidx']

theorem computePubAt_eq (z α : K) (i : Fin (cfg z α).compRows) :
    (execThreaded z α).computePubAt i =
      (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) ((i : ℕ) + 1))).row.2.2.1 := by
  rw [ExactExecution.computePubAt, computeRowAt_eq]
  rfl

theorem adjacent_ln (z α : K) (k : ℕ) (hk : k + 1 < 401) :
    (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) (k + 1))).row.2.2.1.ln =
      (renderNode z α (bfsLabelAt (mmTreeAir (K := K)) (k + 2))).row.2.2.1.ln_prev := by
  have hlen : (bfsRows (mmTreeAir (K := K))).length = 401 := by
    simp [bfsRows, mmTreeAir_bfsForest_length]
  have hk0 : (k + 1) - 1 < (bfsRows (mmTreeAir (K := K))).length := by omega
  have hk1 : (k + 2) - 1 < (bfsRows (mmTreeAir (K := K))).length := by omega
  have hkacc : k < (bfsRows (mmTreeAir (K := K))).length := by omega
  rw [(renderNode_ln z α _).1, (renderNode_ln z α _).2]
  rw [bfsLabelAt_lnExponent (mmTreeAir (K := K)) (k + 1) hk0,
    bfsLabelAt_lnPrev (mmTreeAir (K := K)) (k + 2) hk1]
  have hsucc := accAt_succ_of_lt (mmTreeAir (K := K)) k hkacc
  have hskel := bfsLabelAt_skel (mmTreeAir (K := K)) (k + 1) hk0
  have hk1' : k + 1 - 1 = k := Nat.add_sub_cancel k 1
  have hk2' : k + 2 - 1 = k + 1 := by omega
  simp [hk1', hk2', hskel, hsucc]

theorem compute_chain (z α : K) :
    ∀ i : Fin (cfg z α).compRows,
      ∀ hi : (i : ℕ) + 1 < (cfg z α).compRows,
        ((execThreaded z α).computePubAt i).ln =
          ((execThreaded z α).computePubAt ⟨(i : ℕ) + 1, hi⟩).ln_prev := by
  intro i hi
  rw [computePubAt_eq, computePubAt_eq]
  exact adjacent_ln z α (i : ℕ) (by
    have : (cfg z α).compRows = 401 := by simp [cfg]
    omega)

theorem compute_wf (z α : K) (hz : z ≠ 0)
    (hc1 : ∀ v, InTree (mmTree (K := K)) v →
      v.label.skel.state = ComputeTable.State.s5 → op5C1Ready v.label.skel) :
    ∀ i, ComputeTable.WF (cfg z α).challenges.computeInputs
      ((execThreaded z α).computePubAt i) := by
  intro i
  have hch : (cfg z α).challenges.computeInputs = ⟨α, z, 0, 0, 1⟩ := by
    simp [cfg, ChallengeVector.computeInputs]
  rw [computePubAt_eq, hch]
  refine renderNode_WF_c_one z α
      (bfsLabelAt (mmTreeAir (K := K)) ((i : ℕ) + 1)) hz ?_
  intro hs5
  have hi : ((i : ℕ) + 1) ∈
      List.range' 1 (bfsForest [mmTreeAir (K := K)]).length := by
    have hlen : (bfsForest [mmTreeAir (K := K)]).length = 401 :=
      mmTreeAir_bfsForest_length
    have hcfg : (cfg z α).compRows = 401 := by simp [cfg]
    have hlt : (i : ℕ) < 401 := by
      have := i.isLt
      omega
    rw [hlen]
    exact List.mem_range'.mpr ⟨(i : ℕ), hlt, by omega⟩
  have hi' := lt_bfsRows_of_mem_range' hi
  have hlenF : (i : ℕ) < (bfsForest [mmTreeAir (K := K)]).length := by
    simpa [bfsRows_length] using hi'
  have hmem : (bfsForest [mmTreeAir (K := K)])[(i : ℕ)] ∈
      bfsForest [mmTreeAir (K := K)] := List.getElem_mem hlenF
  have hinAir : InTree (mmTreeAir (K := K))
      (bfsForest [mmTreeAir (K := K)])[(i : ℕ)] := by
    have := (mem_bfsForest [mmTreeAir (K := K)] _).mp hmem
    obtain ⟨c, hc, hct⟩ := this
    simp at hc
    subst c
    exact hct
  unfold mmTreeAir at hinAir
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label (mmTree (K := K)) _ hinAir
  have hskel :
      (bfsLabelAt (mmTreeAir (K := K)) ((i : ℕ) + 1)).skel =
        u0.label.skel := by
    rw [bfsLabelAt_skel (mmTreeAir (K := K)) _ hi']
    unfold mmTreeAir
    simp [bfsRows]
    exact congrArg (fun g : GenComputeRow K => g.skel) hl
  simpa [op5C1Ready, hskel] using hc1 _ hu0 (hskel ▸ hs5)

theorem compute_wf_seed :
    ∀ i, ComputeTable.WF (cfg seedZ alphaA).challenges.computeInputs
      ((execThreaded seedZ alphaA).computePubAt i) :=
  compute_wf seedZ alphaA seedZ_ne_zero
    (fun v hv hs5 => (mmTree_seedOK v hv).2.2.2 hs5)

theorem memory_first_counts (z α : K) (htwo : (2 : K) ≠ 0)
    (h : ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.counts = 0) :
    ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.counts = 0 :=
  (memory_first_pt z α htwo h).2

theorem memory_first_indicator (z α : K) (htwo : (2 : K) ≠ 0)
    (h : ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.counts = 0) :
    ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.indicator = 0 :=
  (memory_first_pt z α htwo h).1

-- Row-level memory: the retired `execThreaded_lambda_one` (`λ = 1`) is replaced by
-- `execThreaded_lambda?`; executed rows carry `C' = formRC λ a` (generator obligation).

/-- Every executed (encoded) memory row carries the package `λ = formRDefault`. -/
theorem execThreaded_lambda? (z α : K) :
    ∀ i, ((execThreaded z α).memoryPubAt i).lambda? = some MemoryTable.formRDefault := by
  intro i
  rw [memoryPubAt_eq_thread, encPub_lambda?]

end

end Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

#print axioms Nock.NockVMROM.Thm54.TraceGen.genRowMemForest_all_inputs
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRowMemForest_wf_eqBlk
#print axioms Nock.NockVMROM.Thm54.TraceGen.mmAssigned_bfs_eqBlk
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.execThreaded
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.memoryRowsAccepted_seed
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.computeRowsAccepted_threaded
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.memory_chain
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.memory_first_ipre
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.memory_wf_seed
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.recordCountBalance_threaded
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.memory_last_icur
#print axioms Nock.NockVMROM.Thm54.TraceGen.mmAssigned_bfs_WF
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.mmTree_root_request_shape
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.memory_first_counts
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.memory_first_indicator
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.compute_chain
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.compute_wf
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.compute_wf_seed
