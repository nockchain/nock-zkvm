/-
  Nock/RedTeam/Batch2420Thm54EditSemantics.lean

  Op 10 is a DECLARED EXTENSION beyond NockVMROM (SPEC §1.0).

  The statements below are restated by `example` so a change to any of them breaks this file:
  `edit_of_slots` (both forms), `genuineFX_evalFBy`, `genuineFX_chainOK`, `holdsF_of_genuineFX`,
  the 17-state count, the embedding of the released states.
-/
import Nock.Edit.SemanticsX

set_option autoImplicit false

namespace Nock.RedTeam.Batch2420

open Nock Nock.Walk Nock.FieldEmbedding
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVGenuineF
open Nock.Edit

example {a : ℕ} {new old e : Noun} (hchain : ChainOK a old e)
    (hnew : Noun.slot a e = some new) : Noun.edit a new old = some e :=
  edit_of_slots hchain hnew

example {a : ℕ} {new old e : Noun}
    (hsib : ∀ k < Nat.log 2 a, ∃ x, Noun.slot ((a / 2 ^ k) ^^^ 1) old = some x ∧
      Noun.slot ((a / 2 ^ k) ^^^ 1) e = some x)
    (hnew : Noun.slot a e = some new) : Noun.edit a new old = some e :=
  edit_of_slots_depth hsib hnew

example {q : ℕ} {T : NTree RowX} (hT : GenuineSkelFX q T)
    (hreal : T.label.state.isChain = false) :
    evalFBy q T.size T.label.subject T.label.formula = some T.label.evaluation :=
  genuineFX_evalFBy hT hreal

example {q : ℕ} {T : NTree RowX} (hT : GenuineSkelFX q T)
    (hchain : T.label.state.isChain = true) :
    ChainOK (chainAxis T.label.formula) T.label.subject T.label.evaluation :=
  genuineFX_chainOK hT hchain

/-- `ChainOK` unfolds to the SPEC §1.4 text. -/
example (a : ℕ) (old e : Noun) : ChainOK a old e ↔
    ∀ j, 2 ≤ a / 2 ^ j → ∃ x, Noun.slot ((a / 2 ^ j) ^^^ 1) old = some x ∧
      Noun.slot ((a / 2 ^ j) ^^^ 1) e = some x := Iff.rfl

/-- Seventeen states (SPEC §2.1); the released eleven embed injectively, none of them a chain. -/
def allX : List StateX :=
  [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .cons, .s10, .s10L, .s10T, .s11s, .s11d, .s11j]

theorem allX_complete (s : StateX) : s ∈ allX := by cases s <;> simp [allX]

theorem allX_nodup : allX.Nodup := by decide

theorem allX_length : allX.length = 17 := rfl

example : Function.Injective StateX.ofState := StateX.ofState_injective
example (st : ComputeTable.State) : (StateX.ofState st).isChain = false := StateX.isChain_ofState st

theorem no_genuine_s11j (q : ℕ) (T : NTree RowX) (hT : GenuineSkelFX q T)
    (hst : T.label.state = .s11j) : False := by
  obtain ⟨_, hin, _⟩ := genuineFX_root hT
  rw [hst] at hin
  generalize T.children.map NTree.label = ks at hin
  rcases ks with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
    simp [KidInputsX] at hin

end Nock.RedTeam.Batch2420

#print axioms Nock.Edit.edit_of_slots
#print axioms Nock.Edit.edit_of_slots_depth
#print axioms Nock.Edit.genuineFX_evalFBy
#print axioms Nock.Edit.genuineFX_chainOK
#print axioms Nock.Edit.holdsF_of_genuineFX
#print axioms Nock.RedTeam.Batch2420.no_genuine_s11j

