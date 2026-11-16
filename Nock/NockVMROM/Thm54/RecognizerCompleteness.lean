/-
  Nock/NockVMROM/Thm54/RecognizerCompleteness.lean

  The **converse** of the global-carry axis soundness capstone.

  `GlobalCarryRecognizer.axis_sound_recognizer'` proves that a served `(axis, noun)` tuple of the
  anchored reconstruction `ofNoun s 1` IS the true `Noun.slot`.  Nothing so far proved the other
  direction, so the two `GlobalCarryAxis.ServedLookup` obligations of
  `StrictOperationalEvidence.StrictRowOperationalEvidence` could only be assumed, never traded for a
  Nock-level fact.

  This module closes that: `servedLookup_of_slot` shows every genuine `Noun.slot a root = some child`
  IS served by `ofNoun root 1`, and `servedLookup_iff_slot` packages the two directions as an
  equivalence.  The axis labeling of the paper is stated as a biconditional
  (`axis(nᵢ) = aᵢ ⟺ axis(left nᵢ) = 2aᵢ ∧ axis(right nᵢ) = 2aᵢ+1`, the paper consumed by
  `Def:NMR` the paper), so both directions are paper content; only the soundness half had been
  formalized.

  Nothing here is post-seed, field-valued, or acceptance-dependent: the whole module is a statement
  about nouns, `Noun.slot`, and the structural reconstruction.
-/

import Nock.GlobalCarryRecognizer

namespace Nock.NockVMROM.Thm54.RecognizerCompleteness

open Nock (Noun)
open Nock.GlobalCarryAxis
open Nock.GlobalCarryRecognizer

/-! ## Subtree reachability is transitive -/

/-- Reflexive subtree reachability composes. -/
theorem sub_trans {a b c : MemTree} (hab : Sub a b) (hbc : Sub b c) : Sub a c := by
  induction hbc with
  | refl => exact hab
  | node_l _ ih => exact .node_l ih
  | node_r _ ih => exact .node_r ih

/-! ## Every subtree of an anchored reconstruction is itself an anchored reconstruction

The recursion of `ofNoun` builds each child by the same function, so the family of reconstructions
is closed under `Sub`.  That is what lets a slot descent be continued inside the tree. -/

/-- A subtree of `ofNoun n a` is the reconstruction of its own committed noun at its own committed
axis. -/
theorem sub_ofNoun_canonical :
    ∀ (n : Noun) (a : Nat) (m : MemTree),
      Sub m (ofNoun n a) → m = ofNoun (nounOf m) (axisOf m) := by
  intro n
  induction n with
  | atom k =>
      intro a m hsub
      have hleaf : ofNoun (Noun.atom k) a = MemTree.leaf (Noun.atom k) a := rfl
      rw [hleaf] at hsub
      cases hsub
      rfl
  | cell l r ihl ihr =>
      intro a m hsub
      have hnode : ofNoun (Noun.cell l r) a =
          MemTree.node (Noun.cell l r) a (ofNoun l (2 * a)) (ofNoun r (2 * a + 1)) := rfl
      rw [hnode] at hsub
      cases hsub with
      | refl => rfl
      | node_l hl => exact ihl (2 * a) m hl
      | node_r hr => exact ihr (2 * a + 1) m hr

/-- The left reconstruction child is reachable from a cell reconstruction. -/
theorem sub_ofNoun_left (l r : Noun) (a : Nat) :
    Sub (ofNoun l (2 * a)) (ofNoun (Noun.cell l r) a) := by
  have hnode : ofNoun (Noun.cell l r) a =
      MemTree.node (Noun.cell l r) a (ofNoun l (2 * a)) (ofNoun r (2 * a + 1)) := rfl
  rw [hnode]
  exact .node_l .refl

/-- The right reconstruction child is reachable from a cell reconstruction. -/
theorem sub_ofNoun_right (l r : Noun) (a : Nat) :
    Sub (ofNoun r (2 * a + 1)) (ofNoun (Noun.cell l r) a) := by
  have hnode : ofNoun (Noun.cell l r) a =
      MemTree.node (Noun.cell l r) a (ofNoun l (2 * a)) (ofNoun r (2 * a + 1)) := rfl
  rw [hnode]
  exact .node_r .refl

/-! ## Recognizer completeness -/

/-- **Recognizer completeness, raw match form.**  Every true Nock slot of `root` occurs as a
committed `(axis, noun)` pair of the anchored reconstruction `ofNoun root 1`.

The induction is on the axis: axis `1` is the root itself, and the descent step is
the paper's carry `2a` / `2a+1`, replayed through `slot_double` /
`slot_double_succ`. -/
theorem servedMatch_of_slot :
    ∀ a : Nat, ∀ root v : Noun, Noun.slot a root = some v →
      ∃ m, Sub m (ofNoun root 1) ∧ axisOf m = a ∧ nounOf m = v := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro root v hslot
    by_cases h0 : a = 0
    · subst h0
      simp [Noun.slot] at hslot
    by_cases h1 : a = 1
    · subst h1
      have hv : v = root := by
        have hone : Noun.slot 1 root = some root := by simp [Noun.slot]
        rw [hone] at hslot
        exact (Option.some.inj hslot).symm
      subst hv
      exact ⟨ofNoun v 1, .refl, ofNoun_root_axis v, ofNoun_root_noun v⟩
    have ha2 : 2 ≤ a := by omega
    have hk1 : 1 ≤ a / 2 := by omega
    have hklt : a / 2 < a := by omega
    have hsplit : a = 2 * (a / 2) ∨ a = 2 * (a / 2) + 1 := by omega
    rcases hsplit with heven | hodd
    · rw [heven, slot_double (a / 2) hk1 root] at hslot
      obtain ⟨w, hw, hhead⟩ := Option.bind_eq_some_iff.1 hslot
      cases w with
      | atom n => simp [headOpt] at hhead
      | cell x y =>
          have hxv : x = v := by simpa [headOpt] using hhead
          subst hxv
          obtain ⟨m, hsub, hax, hn⟩ := ih (a / 2) hklt root (Noun.cell x y) hw
          have hm : m = ofNoun (Noun.cell x y) (a / 2) := by
            rw [sub_ofNoun_canonical root 1 m hsub, hax, hn]
          refine ⟨ofNoun x (2 * (a / 2)), ?_, ?_, ?_⟩
          · refine sub_trans ?_ hsub
            rw [hm]
            exact sub_ofNoun_left x y (a / 2)
          · rw [ofNoun_axisOf]; omega
          · exact ofNoun_nounOf x _
    · rw [hodd, slot_double_succ (a / 2) hk1 root] at hslot
      obtain ⟨w, hw, htail⟩ := Option.bind_eq_some_iff.1 hslot
      cases w with
      | atom n => simp [tailOpt] at htail
      | cell x y =>
          have hyv : y = v := by simpa [tailOpt] using htail
          subst hyv
          obtain ⟨m, hsub, hax, hn⟩ := ih (a / 2) hklt root (Noun.cell x y) hw
          have hm : m = ofNoun (Noun.cell x y) (a / 2) := by
            rw [sub_ofNoun_canonical root 1 m hsub, hax, hn]
          refine ⟨ofNoun y (2 * (a / 2) + 1), ?_, ?_, ?_⟩
          · refine sub_trans ?_ hsub
            rw [hm]
            exact sub_ofNoun_right x y (a / 2)
          · rw [ofNoun_axisOf]; omega
          · exact ofNoun_nounOf y _

/-- **Recognizer completeness (`ServedLookup` form).**  The exact converse of
`GlobalCarryRecognizer.axis_sound_recognizer'`. -/
theorem servedLookup_of_slot {a : Nat} {root child : Noun}
    (h : Noun.slot a root = some child) :
    ServedLookup (ofNoun root 1) a child :=
  ⟨servedMatch_of_slot a root child h⟩

/-- **The recognizer is exactly the slot operator.**  On the anchored reconstruction of `root`, being
served at axis `a` with value `child` is *equivalent* to `\(a, root) = child`.

Soundness is `axis_sound_recognizer'`; completeness is `servedLookup_of_slot`.  Consequently the two
`ServedLookup` fields of `StrictOperationalEvidence.StrictRowOperationalEvidence` carry neither more
nor less information than the corresponding `Noun.slot` facts. -/
theorem servedLookup_iff_slot (a : Nat) (root child : Noun) :
    ServedLookup (ofNoun root 1) a child ↔ Noun.slot a root = some child :=
  ⟨fun h => axis_sound_recognizer' root h, servedLookup_of_slot⟩

/-- Root reconstruction always serves the whole noun at axis `1`. -/
theorem servedLookup_root (root : Noun) : ServedLookup (ofNoun root 1) 1 root :=
  servedLookup_of_slot (by simp [Noun.slot])

/-- A cell reconstruction serves its head at axis `2`. -/
theorem servedLookup_head (l r : Noun) :
    ServedLookup (ofNoun (Noun.cell l r) 1) 2 l :=
  servedLookup_of_slot (local_cons_head (Noun.cell l r) l r rfl)

/-- A cell reconstruction serves its tail at axis `3`. -/
theorem servedLookup_tail (l r : Noun) :
    ServedLookup (ofNoun (Noun.cell l r) 1) 3 r :=
  servedLookup_of_slot (local_cons_tail (Noun.cell l r) l r rfl)

/-- Completeness does not manufacture forgeries: a served value at an axis with a different genuine
slot is impossible. -/
theorem servedLookup_unique {a : Nat} {root child child' : Noun}
    (h : ServedLookup (ofNoun root 1) a child)
    (h' : ServedLookup (ofNoun root 1) a child') : child = child' :=
  Option.some.inj
    (((servedLookup_iff_slot a root child).1 h).symm.trans
      ((servedLookup_iff_slot a root child').1 h'))

end Nock.NockVMROM.Thm54.RecognizerCompleteness

#print axioms Nock.NockVMROM.Thm54.RecognizerCompleteness.sub_trans
#print axioms Nock.NockVMROM.Thm54.RecognizerCompleteness.sub_ofNoun_canonical
#print axioms Nock.NockVMROM.Thm54.RecognizerCompleteness.sub_ofNoun_left
#print axioms Nock.NockVMROM.Thm54.RecognizerCompleteness.sub_ofNoun_right
#print axioms Nock.NockVMROM.Thm54.RecognizerCompleteness.servedMatch_of_slot
#print axioms Nock.NockVMROM.Thm54.RecognizerCompleteness.servedLookup_of_slot
#print axioms Nock.NockVMROM.Thm54.RecognizerCompleteness.servedLookup_iff_slot
#print axioms Nock.NockVMROM.Thm54.RecognizerCompleteness.servedLookup_root
#print axioms Nock.NockVMROM.Thm54.RecognizerCompleteness.servedLookup_head
#print axioms Nock.NockVMROM.Thm54.RecognizerCompleteness.servedLookup_tail
#print axioms Nock.NockVMROM.Thm54.RecognizerCompleteness.servedLookup_unique
