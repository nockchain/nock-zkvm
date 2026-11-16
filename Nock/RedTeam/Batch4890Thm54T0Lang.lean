/-
  Nock/RedTeam/Batch4890Thm54T0Lang.lean

  **the opaque-noun type `Ty.N` in the template language.**

  * `Ty.N` accepts every noun (`shapeOK p .N _ = true`), `HasTy.weakN` weakens any typing to `.N`.
  * Guard at `N`: `gTy p .N f = op6 (op3 f) (op1 0) (op1 0)` -- it EVALUATES the argument slot (so the
    compiled formula crashes iff the slot is missing, which `compile_complete` needs) and always
    returns `0`.  (The design's `op1 0` never reads, and falsifies `compile_complete`.)
  * Positive control: the `N`-free equations `gTy p .F`, `gTy p (.L ..)` and the compiled matmul
    template (`2`-matrix: 1092 cells, as `AutogenMatmul.matmul2_cells`) are unchanged.
  * An `N`-typed toy accepts an atom `>= p`; a template ignoring its `N` argument crashes on a
    subject lacking that slot, matching `Tpl.sem = none`.
-/
import Nock.Jet.Autogen
import Nock.Jet.AutogenMatmul
import Nock.Jet.Interp

set_option autoImplicit false

namespace Nock.RedTeam.Batch4890

open Nock Nock.Noun Nock.Jet.Autogen

/-! ### Positive control: N-free compile is unchanged -/

theorem gTy_F_unchanged (p : ℕ) (f : Noun) :
    gTy p .F f = op6 (op3 f) (op1 (A 1)) (call 4 (.cell f (op1 (A 0))) (op0 1)) := rfl

theorem gTy_L_unchanged (p n : ℕ) (τ : Ty) (f : Noun) : gTy p (.L n τ) f = gL (gTy p τ) n f := rfl

theorem gTy_matmul_unchanged (p : ℕ) (f : Noun) :
    gTy p (matTy 2) f = gL (gTy p (.L 2 .F)) 2 f := rfl

theorem matmul2_compile_unchanged : cells (compile 7 (matmulT 2)) = 1092 := matmul2_cells

theorem shapeOK_N (p : ℕ) (v : Noun) : shapeOK p .N v = true := rfl

theorem gTy_N (p : ℕ) (f : Noun) : gTy p .N f = op6 (op3 f) (op1 (A 0)) (op1 (A 0)) := rfl

/-! ### An `N`-typed toy accepting a big atom -/

/-- `[x d]`, `x : F` at axis 2, `d : N` at axis 3; returns `x * x`. -/
def toyN : Tpl where
  k := 2
  ax := ![2, 3]
  inTy := ![.F, .N]
  outTy := .F
  body := .mul (.var 0) (.var 0)

theorem toyN_wellTyped (p : ℕ) : toyN.WellTyped p := by
  unfold Tpl.WellTyped toyN
  exact HasTy.mul (by simpa using HasTy.var (p := p) (inTy := ![.F, .N]) 0)
    (by simpa using HasTy.var (p := p) (inTy := ![.F, .N]) 0)

/-- `[3 12]`: the `N` argument `12 >= 7 = p` is not a field atom. -/
def bigS : Noun := .cell (.atom 3) (.atom 12)

theorem toyN_sem : toyN.sem 7 bigS = some (.atom 2) := by
  refine sem_eq_some_iff.2 ⟨![.atom 3, .atom 12], ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [toyN, bigS, Noun.slot]
  · intro i; fin_cases i <;> decide
  · decide

theorem toyN_evalN : ∃ fuel, evalN fuel bigS (compile 7 toyN) = some (.atom 2) :=
  compile_faithful (by norm_num) toyN (toyN_wellTyped 7) _ _ toyN_sem

/-- The same argument typed `F` is rejected (negative control for the typing). -/
def toyF : Tpl := { toyN with inTy := ![.F, .F] }

theorem toyF_sem : toyF.sem 7 bigS = none := by
  cases hs : toyF.sem 7 bigS with
  | none => rfl
  | some r =>
    obtain ⟨a, hs', hok, -⟩ := sem_eq_some_iff.1 hs
    have h1 := hs' ⟨1, by decide⟩
    have h2 := hok ⟨1, by decide⟩
    simp [toyF, toyN, bigS, Noun.slot] at h1
    have h3 : a ⟨1, by decide⟩ = .atom 12 := h1.symm
    rw [h3] at h2
    exact absurd h2 (by decide)

/-! ### Negative control: ignoring an `N` argument still crashes without the slot -/

def ignoreT : Tpl where
  k := 1
  ax := ![2]
  inTy := ![.N]
  outTy := .N
  body := .const 0

theorem ignoreT_wellTyped (p : ℕ) : ignoreT.WellTyped p :=
  HasTy.weakN (HasTy.nil .F)

theorem ignoreT_sem_none : ignoreT.sem 7 (.atom 0) = none := by
  cases hs : ignoreT.sem 7 (.atom 0) with
  | none => rfl
  | some r =>
    obtain ⟨a, hs', -, -⟩ := sem_eq_some_iff.1 hs
    have := hs' ⟨0, by decide⟩
    simp [ignoreT, Noun.slot] at this

theorem ignoreT_crashes : ∀ fuel, evalN fuel (.atom 0) (compile 7 ignoreT) = none :=
  compile_crash_exact (by norm_num) ignoreT (ignoreT_wellTyped 7) _ ignoreT_sem_none

/-! ### Axioms -/

#print axioms Nock.Jet.Autogen.compile_faithful
#print axioms Nock.Jet.Autogen.compile_complete
#print axioms Nock.Jet.Autogen.compile_jetSpec_faithful
#print axioms Nock.Jet.Interp.interp_sound
#print axioms Nock.Jet.Interp.interp_complete
#print axioms toyN_evalN
#print axioms ignoreT_crashes
#print axioms toyF_sem

end Nock.RedTeam.Batch4890
