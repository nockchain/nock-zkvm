/-
  Nock/RedTeam/Batch2491Thm54JetAutogen.lean

  Restates the
  exact statements by `example` (so a change of any statement breaks this file), adds a negative
  control (an ill-shaped input crashes at every fuel), and prints the axioms.

  * The generic theorem: `compile_faithful`, `compile_complete`, `compile_crash_exact`,
    `compile_jetSpec_faithful` (J-1's `JetSpec.Faithful`), `compile_rel_iff_holdsN`.
  * Library specs `isf_spec`, `subc_spec`, `fadl_spec`, `fmll_spec`; `ev_spec`, `guard_spec`.
-/
import Nock.Jet.AutogenMatmul

set_option autoImplicit false

namespace Nock.RedTeam.Batch2491

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen

/-! ## Statements -/

example {p : ℕ} (hp : 0 < p) (T : Tpl) (hT : T.WellTyped p) (s r : Noun)
    (h : T.sem p s = some r) : ∃ fuel, evalN fuel s (compile p T) = some r :=
  compile_faithful hp T hT s r h

example {p : ℕ} (hp : 0 < p) (T : Tpl) (hT : T.WellTyped p) (fuel : ℕ) (s r : Noun)
    (h : evalN fuel s (compile p T) = some r) : T.sem p s = some r :=
  compile_complete hp T hT fuel s r h

example {p : ℕ} (hp : 0 < p) (T : Tpl) (hT : T.WellTyped p) (s : Noun) (h : T.sem p s = none) :
    ∀ fuel, evalN fuel s (compile p T) = none :=
  compile_crash_exact hp T hT s h

example {p : ℕ} (hp : 0 < p) (T : Tpl) (hT : T.WellTyped p) :
    (⟨T.toTemplate p, compile p T⟩ : JetSpec).Faithful :=
  compile_jetSpec_faithful hp T hT

example {p : ℕ} (hp : 0 < p) (T : Tpl) (hT : T.WellTyped p) (s r : Noun) :
    (T.toTemplate p).rel s r ↔ HoldsN ⟨s, compile p T, r⟩ :=
  compile_rel_iff_holdsN hp T hT s r

/-- The compiled shape: `[8 [1 LIB] [6 GUARD BODY [0 0]]]`. -/
example (p : ℕ) (T : Tpl) : compile p T =
    .cell (.atom 8) (.cell (.cell (.atom 1) (LIB p))
      (.cell (.atom 6) (.cell (guardAll p T (List.finRange T.k))
        (.cell (cEx T.ax T.body) (.cell (.atom 0) (.atom 0)))))) := rfl

/-- `Tpl.toTemplate` is J-1's `Template` with the same arity and axes. -/
example (p : ℕ) (T : Tpl) : (T.toTemplate p).k = T.k ∧ (T.toTemplate p).ax = T.ax := ⟨rfl, rfl⟩

example {p : ℕ} (hp : 0 < p) (x y : ℕ) (hx : x < p) (hy : y < p) (ctx : Noun) :
    EvalsTo (core p (.cell (.atom x) (.cell (.atom 0) (.atom y))) ctx) (fadlArm p)
      (.atom ((x + y) % p)) := fadd_spec hp hx hy ctx

example {p : ℕ} (hp : 0 < p) (x y : ℕ) (hx : x < p) (ctx : Noun) :
    EvalsTo (core p (.cell (.atom 0) (.cell (.atom 0) (.cell (.atom x) (.atom y)))) ctx) fmllArm
      (.atom ((x * y) % p)) := fmul_spec hp hx ctx

example {p : ℕ} (hp : 0 < p) (n : ℕ) :
    (⟨(matmulT n).toTemplate p, compile p (matmulT n)⟩ : JetSpec).Faithful :=
  matmul_jetSpec_faithful hp n

example : HoldsN ⟨toyS, compile 7 (matmulT 2), toyC⟩ := Autogen.toy_holdsN
example : evalN 200 toyS (compile 7 (matmulT 2)) = some toyC := Autogen.toy_evalN
example : (matmulT 2).sem Nock.Field.p toyS = some toyCG := toyG_sem
example : cells (compile 7 (matmulT 8)) = 57108 := matmul8_cells

/-! ## Negative control: an ill-shaped argument (an entry `7 ≥ p = 7`) crashes at every fuel -/

def badA : Noun := mat [[1, 2], [3, 7]]
def badS : Noun := .cell (.atom 0) (.cell (.cell badA toyB) (.atom 0))

theorem bad_sem : (matmulT 2).sem 7 badS = none := by
  cases h : (matmulT 2).sem 7 badS with
  | none => rfl
  | some r =>
    obtain ⟨a, hs, hok, -⟩ := sem_eq_some_iff.1 h
    have h0 := hs (0 : Fin 2)
    simp [matmulT, badS, Noun.slot] at h0
    have := hok (0 : Fin 2)
    rw [← h0] at this
    exact absurd this (by decide)

theorem bad_crash : ∀ fuel, evalN fuel badS (compile 7 (matmulT 2)) = none :=
  compile_crash_exact (by norm_num) _ (matmul_wellTyped (by norm_num) 2) _ bad_sem

/-- The same, by direct kernel evaluation at one fuel. -/
theorem bad_evalN : evalN 200 badS (compile 7 (matmulT 2)) = none := by decide +kernel

/-! ## Axioms -/

#print axioms compile_faithful
#print axioms compile_complete
#print axioms compile_crash_exact
#print axioms compile_jetSpec_faithful
#print axioms compile_rel_iff_holdsN
#print axioms matmul_jetSpec_faithful
#print axioms Autogen.toy_holdsN
#print axioms Autogen.toy_evalN
#print axioms toyG_evalN
#print axioms toyG_sem
#print axioms matmul8_cells
#print axioms bad_crash
#print axioms bad_evalN

end Nock.RedTeam.Batch2491
