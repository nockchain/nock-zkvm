import Nock.Reference

/-!
# Global anchored carry for Nock axes

This production module models the single-root memory reconstruction as one physical binary tree.
The root axis is `1`; child axes are carried globally as `2*a` and `2*a+1`.  Together with the
local cons equations, that carry forces every committed `(axis,noun)` pair to be the corresponding
`Noun.slot`.

This is a uniqueness/soundness result for an already reconstructed noun.  It does not construct a
decoder from field fingerprints to `Noun`.
-/

namespace Nock
namespace GlobalCarryAxis

open Nock (Noun)

/-- Head projection as an `Option`. -/
def headOpt : Noun → Option Noun
  | .cell l _ => some l
  | .atom _ => none

/-- Tail projection as an `Option`. -/
def tailOpt : Noun → Option Noun
  | .cell _ r => some r
  | .atom _ => none

/-- Left-child recurrence for the globally anchored Nock axis. -/
theorem slot_double (k : Nat) (hk : 1 ≤ k) (s : Noun) :
    Noun.slot (2 * k) s = (Noun.slot k s).bind headOpt := by
  obtain ⟨a, ha⟩ : ∃ a, 2 * k = a + 2 := ⟨2 * k - 2, by omega⟩
  have hd : (a + 2) / 2 = k := by omega
  have hm : (a + 2) % 2 = 0 := by omega
  rw [ha]
  simp only [Noun.slot]
  rw [hd]
  cases hs : Noun.slot k s with
  | none => simp
  | some w =>
    cases w with
    | atom _ => simp [headOpt]
    | cell l r => simp [headOpt, hm]

/-- Right-child recurrence for the globally anchored Nock axis. -/
theorem slot_double_succ (k : Nat) (hk : 1 ≤ k) (s : Noun) :
    Noun.slot (2 * k + 1) s = (Noun.slot k s).bind tailOpt := by
  obtain ⟨a, ha⟩ : ∃ a, 2 * k + 1 = a + 2 := ⟨2 * k - 1, by omega⟩
  have hd : (a + 2) / 2 = k := by omega
  have hm : (a + 2) % 2 = 1 := by omega
  rw [ha]
  simp only [Noun.slot]
  rw [hd]
  cases hs : Noun.slot k s with
  | none => simp
  | some w =>
    cases w with
    | atom _ => simp [tailOpt]
    | cell l r => simp [tailOpt, hm]

/-- One physical memory reconstruction with committed nouns and globally carried axes. -/
inductive MemTree where
  | leaf : Noun → Nat → MemTree
  | node : Noun → Nat → MemTree → MemTree → MemTree
  deriving Repr

/-- Committed noun at a subtree root. -/
def nounOf : MemTree → Noun
  | .leaf n _ => n
  | .node n _ _ _ => n

/-- Committed global axis at a subtree root. -/
def axisOf : MemTree → Nat
  | .leaf _ a => a
  | .node _ a _ _ => a

/-- Local cons reconstruction and parent-to-child global-axis constraints. -/
def WF : MemTree → Prop
  | .leaf n _ => n.isAtom = true
  | .node n a l r =>
      n = Noun.cell (nounOf l) (nounOf r)
        ∧ axisOf l = 2 * a
        ∧ axisOf r = 2 * a + 1
        ∧ WF l
        ∧ WF r

/-- Reflexive subtree reachability. -/
inductive Sub : MemTree → MemTree → Prop where
  | refl : Sub t t
  | node_l : Sub m l → Sub m (.node n a l r)
  | node_r : Sub m r → Sub m (.node n a l r)

/-- Relative core: a correct positive-axis subtree forces every reachable descendant slot. -/
theorem sub_slot (root : Noun) :
    ∀ (t : MemTree), WF t → 1 ≤ axisOf t →
      Noun.slot (axisOf t) root = some (nounOf t) →
      ∀ m, Sub m t → Noun.slot (axisOf m) root = some (nounOf m) := by
  intro t
  induction t with
  | leaf n a =>
      intro _ _ hslot m hsub
      cases hsub with
      | refl => exact hslot
  | node n a l r ihl ihr =>
      intro hwf hpos hslot m hsub
      simp only [axisOf, nounOf] at hpos hslot
      simp only [WF] at hwf
      obtain ⟨hcons, hla, hra, hwfl, hwfr⟩ := hwf
      cases hsub with
      | refl => simpa only [axisOf, nounOf] using hslot
      | node_l hsubl =>
          have hslotL : Noun.slot (axisOf l) root = some (nounOf l) := by
            rw [hla, slot_double a hpos root, hslot, hcons]
            rfl
          exact ihl hwfl (by rw [hla]; omega) hslotL m hsubl
      | node_r hsubr =>
          have hslotR : Noun.slot (axisOf r) root = some (nounOf r) := by
            rw [hra, slot_double_succ a hpos root, hslot, hcons]
            rfl
          exact ihr hwfr (by rw [hra]; omega) hslotR m hsubr

/-- Every reachable node in a well-formed root-axis-1 tree is its true root-noun slot. -/
theorem memtree_noun_eq_slot (t : MemTree) (hwf : WF t) (hroot : axisOf t = 1) :
    ∀ m, Sub m t → Noun.slot (axisOf m) (nounOf t) = some (nounOf m) :=
  sub_slot (nounOf t) t hwf (by simp [hroot]) (by rw [hroot]; simp [Noun.slot])

/-- A served whole-tuple match `(axis,noun)` is sound. -/
theorem lookup_sound (t : MemTree) (hwf : WF t) (hroot : axisOf t = 1)
    {s : Noun} (hs : nounOf t = s) {a : Nat} {v : Noun}
    (h : ∃ m, Sub m t ∧ axisOf m = a ∧ nounOf m = v) :
    Noun.slot a s = some v := by
  obtain ⟨m, hsub, ham, hmn⟩ := h
  have hm := memtree_noun_eq_slot t hwf hroot m hsub
  rw [ham, hmn, hs] at hm
  exact hm

/-- Doubling is injective on natural-number axes. -/
theorem axis_double_inj {a b : Nat} (h : 2 * a = 2 * b) : a = b := by omega

/-- Left and right child axes are disjoint. -/
theorem axis_left_ne_right (a b : Nat) : 2 * a ≠ 2 * b + 1 := by omega

/-- A committed axis determines at most one committed noun. -/
theorem axis_determines_noun (t : MemTree) (hwf : WF t) (hroot : axisOf t = 1)
    {m₁ m₂ : MemTree} (h₁ : Sub m₁ t) (h₂ : Sub m₂ t) (hax : axisOf m₁ = axisOf m₂) :
    nounOf m₁ = nounOf m₂ := by
  have e₁ := memtree_noun_eq_slot t hwf hroot m₁ h₁
  have e₂ := memtree_noun_eq_slot t hwf hroot m₂ h₂
  rw [hax] at e₁
  exact Option.some.inj (e₁.symm.trans e₂)

/-- A node cannot serve a noun different from the genuine slot value at the same axis. -/
theorem forgery_rejected (t : MemTree) (hwf : WF t) (hroot : axisOf t = 1)
    {s : Noun} (hs : nounOf t = s) {a : Nat} {v v' : Noun}
    (hgen : Noun.slot a s = some v') (hne : v ≠ v') :
    ¬ ∃ m, Sub m t ∧ axisOf m = a ∧ nounOf m = v := by
  rintro ⟨m, hsub, ham, hmn⟩
  have hm := memtree_noun_eq_slot t hwf hroot m hsub
  rw [ham, hmn, hs] at hm
  exact hne (Option.some.inj (hm.symm.trans hgen))

/-- The recognizer's whole-tuple match for a served lookup. -/
structure ServedLookup (t : MemTree) (a : Nat) (v : Noun) : Prop where
  matched : ∃ m, Sub m t ∧ axisOf m = a ∧ nounOf m = v

/-- Global-carry axis soundness capstone. -/
theorem axis_sound_globalcarry
    (t : MemTree) (hcons_and_carry : WF t) (hroot : axisOf t = 1)
    {s : Noun} (hs : nounOf t = s) {a : Nat} {v : Noun}
    (hserved : ServedLookup t a v) :
    Noun.slot a s = some v :=
  lookup_sound t hcons_and_carry hroot hs hserved.matched

end GlobalCarryAxis
end Nock
