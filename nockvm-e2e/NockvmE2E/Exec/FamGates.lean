/-
the family-generic gates of the exe.  `famGates F XI` is the conjunction of exactly the five executed Bool checks named as
binders by `exec_e2e_generic` / `exec_e2e_J9A_absent` (`shapeOkF`, `shapeXOkF`, `chipsOkF`, `maskOkF`, `numeralOkF`).  Pure; the exe's IO
wrapper (VerifyMain `--family`) is a thin `if`.
-/
import NockvmE2E.J9A.LagrJ9A

set_option autoImplicit false

namespace NockvmE2E.Exec.FamGates
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips NockvmE2E.J9A.LagrJ9A
open NockvmE2E.Exec.MaskOk NockvmE2E.Exec.J8Shape NockvmE2E.Exec.J8Chips

def famGates (F : Fam) (XI : ExecInst) : Bool :=
  shapeOkF F XI && shapeXOkF F XI && chipsOkF F XI && maskOkF F XI && numeralOkF F XI

/-- the name of the first failing conjunct, if any -/
def famGatesFail (F : Fam) (XI : ExecInst) : Option String :=
  if !shapeOkF F XI then some "shapeOkF (instance is not shaped like the family)"
  else if !shapeXOkF F XI then some "shapeXOkF (nq/pubCap/blockTab/public layout)"
  else if !chipsOkF F XI then some "chipsOkF (a loaded chip is not a literal of the family)"
  else if !maskOkF F XI then some "maskOkF (a preprocessed mask column is not the first/last/root-row pattern)"
  else if !numeralOkF F XI then some "numeralOkF (a walk chip's numeral differs from its root-mask kroots)"
  else none

theorem famGates_sound {F : Fam} {XI : ExecInst} (h : famGates F XI = true) :
    shapeOkF F XI = true ∧ shapeXOkF F XI = true ∧ chipsOkF F XI = true ∧ maskOkF F XI = true ∧ numeralOkF F XI = true := by
  unfold famGates at h
  simp only [Bool.and_eq_true] at h
  tauto

theorem famGates_of {F : Fam} {XI : ExecInst} (h1 : shapeOkF F XI = true) (h2 : shapeXOkF F XI = true) (h3 : chipsOkF F XI = true)
    (h4 : maskOkF F XI = true) (h5 : numeralOkF F XI = true) : famGates F XI = true := by
  simp [famGates, h1, h2, h3, h4, h5]

theorem famGatesFail_none {F : Fam} {XI : ExecInst} : famGatesFail F XI = none ↔ famGates F XI = true := by
  unfold famGatesFail famGates
  cases shapeOkF F XI <;> cases shapeXOkF F XI <;> cases chipsOkF F XI <;> cases maskOkF F XI <;> cases numeralOkF F XI <;> simp

theorem chipsOkF_famJ8 : chipsOkF famJ8 = chipsOk := rfl
theorem shapeOkF_famJ8 : shapeOkF famJ8 = j8ShapeOk := rfl
theorem shapeXOkF_famJ8 : shapeXOkF famJ8 = j8ShapeXOk := rfl

/-- `hop0Check` succeeds iff its three Bool conjuncts hold -/
theorem hop0Check_ok_iff (XI : ExecInst) : (hop0Check XI).toBool = true ↔ chipsOk XI = true ∧ maskOk XI = true ∧ numeralOk XI = true := by
  unfold hop0Check
  cases chipsOk XI <;> cases maskOk XI <;> cases numeralOk XI <;> simp [Except.toBool]

/-- at the J-8 family `famGates` is exactly the J-8 gates of the exe (`j8ShapeOk`, `j8ShapeXOk`, `hop0Check`) -/
theorem famGates_J8 (XI : ExecInst) :
    famGates famJ8 XI = true ↔ (j8ShapeOk XI = true ∧ j8ShapeXOk XI = true ∧ (hop0Check XI).toBool = true) := by
  rw [hop0Check_ok_iff]
  constructor
  · intro h
    obtain ⟨a, b, c, d, e⟩ := famGates_sound h
    exact ⟨a, b, c, d, e⟩
  · rintro ⟨a, b, c, d, e⟩
    exact famGates_of a b c d e

end NockvmE2E.Exec.FamGates

#print axioms NockvmE2E.Exec.FamGates.famGates_sound
#print axioms NockvmE2E.Exec.FamGates.famGates_J8
#print axioms NockvmE2E.Exec.FamGates.famGatesFail_none
