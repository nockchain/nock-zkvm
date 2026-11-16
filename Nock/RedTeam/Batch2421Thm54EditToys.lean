/-
  Nock/RedTeam/Batch2421Thm54EditToys.lean

  * **T1** `*[[1 2] [10 [2 [1 9]] [0 1]]] = [9 2]` under `evalN` and `evalFBy q` (every `q`), and a
    field-genuine extended tree (`s10` row, one `s10L` level, `s10T`) whose root is the claim, so
    `holdsF_of_genuineFX` proves `HoldsF` of it through `edit_of_slots`.
  * **T3** a depth-3 edit at the mixed-parity axis `13 = 0b1101` (path `13 → 6 → 3 → 1`):
    `*[[[1 2] [[3 4] [5 6]]] [10 [13 [1 9]] [0 1]]] = [[1 2] [[3 9] [5 6]]]`, again with a genuine
    tree (three `s10L` levels) and `HoldsF`.
  * **TC** a crashing clue: `*[7 [11 [[1 0] [0 0]] [1 5]]]` crashes at EVERY fuel (`evalN` and
    `evalFBy q`), so `¬ HoldsF`, and no field-genuine extended tree with a real root carries the
    claim with ANY result; while the body alone, `*[7 [1 5]] = 5`, succeeds — a chip that skipped
    the clue would accept `5` (SPEC §1.2).
-/
import Nock.Edit.SemanticsX

set_option autoImplicit false

namespace Nock.RedTeam.Batch2421

open Nock Nock.Walk Nock.FieldEmbedding
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVGenuineF
open Nock.Edit

local notation "A" n => Noun.atom n
local infixr:70 " ⬝ " => Noun.cell

/-! ## T1 — `*[[1 2] [10 [2 [1 9]] [0 1]]] = [9 2]` -/

def s1 : Noun := (A 1) ⬝ (A 2)
def f1 : Noun := (A 10) ⬝ (((A 2) ⬝ ((A 1) ⬝ (A 9))) ⬝ ((A 0) ⬝ (A 1)))
def e1 : Noun := (A 9) ⬝ (A 2)

theorem toy1_evalN : evalN 2 s1 f1 = some e1 := by
  simp [evalN, s1, f1, e1, Noun.edit, Noun.slot]

theorem toy1_evalFBy (q : ℕ) : evalFBy q 2 s1 f1 = some e1 := by
  simp [evalFBy, s1, f1, e1, Noun.edit, Noun.slot]

/-- The field-genuine extended tree of T1. -/
def tree1 : NTree RowX :=
  .node ⟨.s10, s1, f1, e1⟩
    [.node ⟨.s1, s1, (A 1) ⬝ (A 9), A 9⟩ [],
     .node ⟨.s0, s1, (A 0) ⬝ (A 1), s1⟩ [],
     .node ⟨.s10L, s1, A 2, e1⟩ [.node ⟨.s10T, s1, A 1, e1⟩ []]]

theorem tree1_genuine (q : ℕ) : GenuineSkelFX q tree1 := by
  refine .node ?_ ?_ ?_ ?_ ?_
  · exact ⟨2, (A 1) ⬝ (A 9), (A 0) ⬝ (A 1), rfl⟩
  · simp [KidInputsX, f1, op10Axis, ComputedWindow.hd, ComputedWindow.tl,
      StrategyOfTraces.nounHead, StrategyOfTraces.nounTail]
  · simp [RowOutputFX, f1, e1, op10Axis, Noun.slot]
  · intro i h; simp only [List.length_cons, List.length_nil] at h
    interval_cases i <;> rfl
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · refine .node ⟨A 9, rfl⟩ (by simp [KidInputsX]) ?_ (by simp) (by simp)
      simp [RowOutputFX, ComputedWindow.tl, StrategyOfTraces.nounTail]
    · refine .node ⟨1, rfl⟩ (by simp [KidInputsX]) ?_ (by simp) (by simp)
      simp [RowOutputFX, ComputedWindow.op0Axis, Noun.slot]
    · refine .node ⟨2, rfl, le_rfl⟩ (by simp [KidInputsX, chainAxis]) ?_ ?_ ?_
      · simp [RowOutputFX, chainAxis, s1, e1, Noun.slot]
      · intro i h; simp only [List.length_cons, List.length_nil] at h
        interval_cases i; rfl
      · intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        subst hk
        exact .node rfl (by simp [KidInputsX]) (by simp [RowOutputFX]) (by simp) (by simp)

theorem toy1_holdsF (q : ℕ) : HoldsF q ⟨s1, f1, e1⟩ :=
  holdsF_of_genuineFX (tree1_genuine q) rfl rfl rfl rfl

/-! ## T3 — a depth-3 edit at axis 13 -/

def s3 : Noun := ((A 1) ⬝ (A 2)) ⬝ (((A 3) ⬝ (A 4)) ⬝ ((A 5) ⬝ (A 6)))
def f3 : Noun := (A 10) ⬝ (((A 13) ⬝ ((A 1) ⬝ (A 9))) ⬝ ((A 0) ⬝ (A 1)))
def e3 : Noun := ((A 1) ⬝ (A 2)) ⬝ (((A 3) ⬝ (A 9)) ⬝ ((A 5) ⬝ (A 6)))

theorem toy3_evalN : evalN 2 s3 f3 = some e3 := by
  simp [evalN, s3, f3, e3, Noun.edit, Noun.slot]

theorem toy3_evalFBy (q : ℕ) : evalFBy q 2 s3 f3 = some e3 := by
  simp [evalFBy, s3, f3, e3, Noun.edit, Noun.slot]

/-- The edit is `edit_of_slots` at the three sibling agreements `12, 7, 2`. -/
theorem toy3_chainOK : ChainOK 13 s3 e3 := by
  intro j hj
  have hj3 : j < 3 := by
    by_contra h
    have : 13 / 2 ^ j ≤ 13 / 2 ^ 3 := Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num)
      (by omega)) (by positivity)
    norm_num at this; omega
  interval_cases j
  · exact ⟨A 3, by simp [s3, Noun.slot], by simp [e3, Noun.slot]⟩
  · exact ⟨(A 5) ⬝ (A 6), by simp [s3, Noun.slot], by simp [e3, Noun.slot]⟩
  · exact ⟨(A 1) ⬝ (A 2), by simp [s3, Noun.slot], by simp [e3, Noun.slot]⟩

theorem toy3_edit : Noun.edit 13 (A 9) s3 = some e3 :=
  edit_of_slots toy3_chainOK (by simp [e3, Noun.slot])

/-- The field-genuine extended tree of T3: `s10`, levels `13, 6, 3`, terminal `1`. -/
def tree3 : NTree RowX :=
  .node ⟨.s10, s3, f3, e3⟩
    [.node ⟨.s1, s3, (A 1) ⬝ (A 9), A 9⟩ [],
     .node ⟨.s0, s3, (A 0) ⬝ (A 1), s3⟩ [],
     .node ⟨.s10L, s3, A 13, e3⟩
       [.node ⟨.s10L, s3, A 6, e3⟩
         [.node ⟨.s10L, s3, A 3, e3⟩ [.node ⟨.s10T, s3, A 1, e3⟩ []]]]]

theorem level_genuine (q a : ℕ) (ha : 2 ≤ a) (T : NTree RowX)
    (hT : GenuineSkelFX q T) (hst : T.label.state.isChain = true)
    (hs : T.label.subject = s3) (hf : T.label.formula = A (a / 2)) (he : T.label.evaluation = e3)
    (hsib : ∃ x, Noun.slot (a ^^^ 1) s3 = some x ∧ Noun.slot (a ^^^ 1) e3 = some x) :
    GenuineSkelFX q (.node ⟨.s10L, s3, A a, e3⟩ [T]) := by
  refine .node ⟨a, rfl, ha⟩ ?_ ?_ ?_ ?_
  · simp [KidInputsX, chainAxis, hs, hf]
  · simpa [RowOutputFX, chainAxis, he] using hsib
  · intro i h; simp only [List.length_cons, List.length_nil] at h
    interval_cases i; simpa [chainPosX] using hst
  · intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; subst hk; exact hT

theorem tree3_genuine (q : ℕ) : GenuineSkelFX q tree3 := by
  have hT : GenuineSkelFX q (.node ⟨.s10T, s3, A 1, e3⟩ []) :=
    .node rfl (by simp [KidInputsX]) (by simp [RowOutputFX]) (by simp) (by simp)
  have h3 := level_genuine q 3 (by norm_num) _ hT rfl rfl rfl rfl
    ⟨(A 1) ⬝ (A 2), by simp [s3, Noun.slot], by simp [e3, Noun.slot]⟩
  have h6 := level_genuine q 6 (by norm_num) _ h3 rfl rfl rfl rfl
    ⟨(A 5) ⬝ (A 6), by simp [s3, Noun.slot], by simp [e3, Noun.slot]⟩
  have h13 := level_genuine q 13 (by norm_num) _ h6 rfl rfl rfl rfl
    ⟨A 3, by simp [s3, Noun.slot], by simp [e3, Noun.slot]⟩
  refine .node ?_ ?_ ?_ ?_ ?_
  · exact ⟨13, (A 1) ⬝ (A 9), (A 0) ⬝ (A 1), rfl⟩
  · simp [KidInputsX, f3, op10Axis, ComputedWindow.hd, ComputedWindow.tl,
      StrategyOfTraces.nounHead, StrategyOfTraces.nounTail]
  · simp [RowOutputFX, f3, e3, op10Axis, Noun.slot]
  · intro i h; simp only [List.length_cons, List.length_nil] at h
    interval_cases i <;> rfl
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · refine .node ⟨A 9, rfl⟩ (by simp [KidInputsX]) ?_ (by simp) (by simp)
      simp [RowOutputFX, ComputedWindow.tl, StrategyOfTraces.nounTail]
    · refine .node ⟨1, rfl⟩ (by simp [KidInputsX]) ?_ (by simp) (by simp)
      simp [RowOutputFX, ComputedWindow.op0Axis, Noun.slot]
    · exact h13

theorem toy3_holdsF (q : ℕ) : HoldsF q ⟨s3, f3, e3⟩ :=
  holdsF_of_genuineFX (tree3_genuine q) rfl rfl rfl rfl

/-! ## TC — a crashing clue -/

def sC : Noun := A 7
/-- `[11 [[1 0] [0 0]] [1 5]]`: dynamic hint, tag `[1 0]`, clue `[0 0]` (axis 0 crashes). -/
def fC : Noun := (A 11) ⬝ ((((A 1) ⬝ (A 0)) ⬝ ((A 0) ⬝ (A 0))) ⬝ ((A 1) ⬝ (A 5)))

theorem toyC_evalN_crash (fuel : ℕ) : evalN fuel sC fC = none := by
  rcases fuel with _ | _ | fuel <;> simp [evalN, sC, fC, Noun.slot]

theorem toyC_evalFBy_crash (q fuel : ℕ) : evalFBy q fuel sC fC = none := by
  rcases fuel with _ | _ | fuel <;> simp [evalFBy, sC, fC, Noun.slot]

/-- The body alone succeeds: skipping the clue would accept `5`. -/
theorem toyC_body : evalN 1 sC ((A 1) ⬝ (A 5)) = some (A 5) := by
  simp [evalN]

theorem toyC_not_holdsF (q : ℕ) (r : Noun) : ¬ HoldsF q ⟨sC, fC, r⟩ := by
  rintro ⟨fuel, h⟩
  rw [toyC_evalFBy_crash] at h
  exact absurd h (by simp)

/-- No field-genuine extended tree with a real root carries the crashing claim, at any result. -/
theorem toyC_no_genuine (q : ℕ) (T : NTree RowX) (hT : GenuineSkelFX q T)
    (hreal : T.label.state.isChain = false) (hs : T.label.subject = sC)
    (hf : T.label.formula = fC) : False := by
  have h := genuineFX_evalFBy hT hreal
  rw [hs, hf, toyC_evalFBy_crash] at h
  exact absurd h (by simp)

end Nock.RedTeam.Batch2421

#print axioms Nock.RedTeam.Batch2421.toy1_evalN
#print axioms Nock.RedTeam.Batch2421.toy1_holdsF
#print axioms Nock.RedTeam.Batch2421.toy3_evalN
#print axioms Nock.RedTeam.Batch2421.toy3_edit
#print axioms Nock.RedTeam.Batch2421.toy3_holdsF
#print axioms Nock.RedTeam.Batch2421.toyC_evalN_crash
#print axioms Nock.RedTeam.Batch2421.toyC_not_holdsF
#print axioms Nock.RedTeam.Batch2421.toyC_no_genuine

