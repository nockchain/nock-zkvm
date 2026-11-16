/-
  Nock/RedTeam/Batch607Thm54PreseedFormulaServed.lean

  - `dec.f_t = mr1.child` on every row;
  - on the two-level opcodes (OP2/5/7/8, OP6, OP9) `dec.f_th = mr2.child` and
    `FP.cons z f_th f_tt = f_t` (`memBlk`, `:1731`, `:1856-1862`), so `f_tt` is determined;
  - OP6 adds `dec.f_tth = mr3.child` with `FP.cons z f_tth f_ttt = f_tt`.
  The forest's `halt` leaves are therefore the ONLY free atoms of a
  trace — the domain for a pre-seed atom column. Identity.
-/
import Nock.ComputeTable

set_option autoImplicit false

namespace Nock.RedTeam.Batch607

open Nock.ComputeTable

variable {K : Type*} [Field K]

/-- Every row: the formula's tail is the served child of `mr1`; the head is then determined by
`f = FP.cons z f_h f_t`. -/
theorem formula_tail_served (inp : Inputs K) (pub : Pub K) (dec : Dec K) (hv : Vcomp inp pub dec) :
    dec.f_t = pub.mr1.child ∧ pub.f = FP.cons inp.z dec.f_h dec.f_t := by
  obtain ⟨hf, hmr1, _, _, _⟩ := hv
  exact ⟨by rw [hmr1], hf⟩

/-- Two-level opcodes: the tail's head is `mr2`'s served child and the tail's tail is determined. -/
theorem formula_second_level_served (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (hv : Vcomp inp pub dec)
    (hs : pub.state = .s2 ∨ pub.state = .s5 ∨ pub.state = .s7 ∨ pub.state = .s8 ∨
          pub.state = .s6 ∨ pub.state = .s9) :
    dec.f_th = pub.mr2.child ∧ FP.cons inp.z dec.f_th dec.f_tt = dec.f_t := by
  have hm := hv.2.2.2.1
  unfold memBlk at hm
  rcases hs with h | h | h | h | h | h <;> rw [h] at hm
  all_goals exact ⟨by rw [hm.1], hm.2.1⟩

/-- OP6: the third level is `mr3`'s served child, and the last tail is determined. -/
theorem formula_third_level_served_op6 (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (hv : Vcomp inp pub dec) (hs : pub.state = .s6) :
    dec.f_tth = pub.mr3.child ∧ FP.cons inp.z dec.f_tth dec.f_ttt = dec.f_tt := by
  have hm := hv.2.2.2.1
  unfold memBlk at hm
  rw [hs] at hm
  exact ⟨by rw [hm.2.2.1], hm.2.2.2.1⟩

/-- OP9: the core lookup's served child is the formula fetched from the computed core. -/
theorem op9_core_formula_served (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (hv : Vcomp inp pub dec) (hs : pub.state = .s9) :
    pub.mr3.child = pub.sf2_f := by
  have hm := hv.2.2.2.1
  unfold memBlk at hm
  rw [hs] at hm
  rw [hm.2.2.1]

end Nock.RedTeam.Batch607

#print axioms Nock.RedTeam.Batch607.formula_tail_served
#print axioms Nock.RedTeam.Batch607.formula_second_level_served
#print axioms Nock.RedTeam.Batch607.formula_third_level_served_op6
#print axioms Nock.RedTeam.Batch607.op9_core_formula_served
