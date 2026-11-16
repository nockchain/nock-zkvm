/-
  Nock/RedTeam/Batch2431Thm54JetSemantics.lean

  Restates the exact statements by `example` (so a change of any
  statement breaks this file) and prints their axioms.

  * `HoldsN` (verbatim copy of A-1's), `Faithful` / `Complete` against `evalN` only (no
    `RunBoundedBy`), `JetSpec.faithful_iff`, `Registry.Faithful`.
  * `evalN_hint_jet` / `evalN_hint_crash` / `holdsN_hint_iff`; `registry_hint_holdsN` /
    `registry_hint_rel` / `registry_hint_iff`.
  * The `s11j` row specs `FormulaShapeJ` / `KidInputsJ` / `RowOutputJ` with `rowJ_holdsN`,
    `rowOutputJ_unique`, `rowOutputJ_of_holdsN`.
  * Toys: the `swap` jet, `toyR`, `toy_holdsN`, `toy_evalN`, `toy_result_unique`, the crashing-clue
    negative control.
-/
import Nock.Jet.Semantics

set_option autoImplicit false

namespace Nock.RedTeam.Batch2431

open Nock Nock.Jet Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SemanticStrategy

example (x : P8PublicClaim) :
    HoldsN x = ∃ fuel, Nock.evalN fuel x.subject x.formula = some x.result := rfl

example (T : Template) (c : Noun) :
    Jet.Faithful T c = ∀ s r, T.rel s r → ∃ fuel, Nock.evalN fuel s c = some r := rfl

example (T : Template) (c : Noun) :
    Complete T c = ∀ s fuel r, Nock.evalN fuel s c = some r → T.rel s r := rfl

example (R : Registry) : Registry.Faithful R = ∀ n j, R n = some j → j.Faithful := rfl

example (j : JetSpec) : j.Faithful ↔ ∀ s r, j.T.rel s r ↔ HoldsN ⟨s, j.c, r⟩ :=
  j.faithful_iff

example (id d c : Noun) : hint id d c = .cell (.atom 11) (.cell (.cell id d) c) := rfl

example {fuel : ℕ} {s id d c v : Noun} (hd : Nock.evalN fuel s d = some v) :
    Nock.evalN (fuel + 1) s (hint id d c) = Nock.evalN fuel s c := evalN_hint_jet hd

example {fuel : ℕ} {s id d c : Noun} (hd : Nock.evalN fuel s d = none) :
    Nock.evalN (fuel + 1) s (hint id d c) = none := evalN_hint_crash hd

example {s id d c r : Noun} :
    HoldsN ⟨s, hint id d c, r⟩ ↔ (∃ fuel v, Nock.evalN fuel s d = some v) ∧ HoldsN ⟨s, c, r⟩ :=
  holdsN_hint_iff

example {R : Registry} (hR : Registry.Faithful R) {n : ℕ} {j : JetSpec} (hj : R n = some j)
    {s d r : Noun} :
    HoldsN ⟨s, jetCall n d j.c, r⟩ ↔ (∃ fuel v, Nock.evalN fuel s d = some v) ∧ j.T.rel s r :=
  registry_hint_iff hR hj

example {R : Registry} (hR : Registry.Faithful R) {s f e : Noun} {ks : List ComputeRowSkeleton}
    (hin : KidInputsJ s f ks) (hkid : ∀ k ∈ ks, HoldsN ⟨k.subject, k.formula, k.evaluation⟩)
    (hout : RowOutputJ R s f ks e) : HoldsN ⟨s, f, e⟩ :=
  rowJ_holdsN hR hin hkid hout

example (R : Registry) (s f : Noun) (k0 : ComputeRowSkeleton) (e : Noun) :
    RowOutputJ R s f [k0] e =
      ∃ (n : ℕ) (d : Noun) (j : JetSpec), f = jetCall n d j.c ∧ R n = some j ∧ j.T.rel s e := rfl

example (s f : Noun) (k0 : ComputeRowSkeleton) :
    KidInputsJ s f [k0] = (k0.subject = s ∧ k0.formula = jetClue f) := rfl

example {R : Registry} {s f : Noun} {ks : List ComputeRowSkeleton} {e₁ e₂ : Noun}
    (h₁ : RowOutputJ R s f ks e₁) (h₂ : RowOutputJ R s f ks e₂) : e₁ = e₂ :=
  rowOutputJ_unique h₁ h₂

-- Toys
example : toyProg = .cell (.atom 11) (.cell (.cell (.atom 7) (.cell (.atom 1) (.atom 42)))
    (.cell (.cell (.atom 0) (.atom 3)) (.cell (.atom 0) (.atom 2)))) := rfl
example : Registry.Faithful toyR := toyR_faithful
example : HoldsN ⟨toySubj, toyProg, .cell (.atom 6) (.atom 5)⟩ := toy_holdsN
example : Nock.evalN 3 toySubj toyProg = some (.cell (.atom 6) (.atom 5)) := toy_evalN
example {r : Noun} (h : HoldsN ⟨toySubj, toyProg, r⟩) : r = .cell (.atom 6) (.atom 5) :=
  toy_result_unique h
example : ∀ r, ¬ HoldsN ⟨toySubj, toyCrash, r⟩ := toy_crash_rel_but_not_holdsN.2.2

end Nock.RedTeam.Batch2431

#print axioms Nock.Jet.Template.args_eq_some
#print axioms Nock.Jet.Template.rel_iff
#print axioms Nock.Jet.Template.rel_functional
#print axioms Nock.Jet.JetSpec.faithful_iff
#print axioms Nock.Jet.evalN_hint_jet
#print axioms Nock.Jet.evalN_hint_crash
#print axioms Nock.Jet.evalN_hint_some_iff
#print axioms Nock.Jet.holdsN_hint_iff
#print axioms Nock.Jet.registry_hint_holdsN
#print axioms Nock.Jet.registry_hint_rel
#print axioms Nock.Jet.registry_hint_iff
#print axioms Nock.Jet.formulaShapeJ_of_rowOutputJ
#print axioms Nock.Jet.rowJ_holdsN
#print axioms Nock.Jet.rowOutputJ_unique
#print axioms Nock.Jet.rowOutputJ_of_holdsN
#print axioms Nock.Jet.swapT_rel_iff
#print axioms Nock.Jet.evalN_swapC
#print axioms Nock.Jet.swapJet_faithful
#print axioms Nock.Jet.toyR_faithful
#print axioms Nock.Jet.toy_holdsN
#print axioms Nock.Jet.toy_evalN
#print axioms Nock.Jet.toy_result_unique
#print axioms Nock.Jet.toy_row_holdsN
#print axioms Nock.Jet.toy_crash_rel_but_not_holdsN
