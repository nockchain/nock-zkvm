/-
  Nock/RedTeam/Batch2404Thm54AtomsHoldsN.lean

  Restates the exact statements by `example` (so a change of any
  statement breaks this file) and prints their axioms.

  * `HoldsN x := ∃ fuel, evalN fuel x.subject x.formula = some x.result`.
  * Under the guards (`BoundedBy q` subject / formula, a guarded run `evalGBy q` or `evalGRom q`):
    `HoldsN ↔ HoldsF q`; the named bridge `evalGRom_evalN_evalFBy`.
  * Negative controls at `*[p−1 [4 0 1]]`: `HoldsF p` without `HoldsN` (result `0`), `HoldsN` without
    `HoldsF p` (result `p`), no guarded run although the inputs are `p`-bounded, incomparability.
-/
import Nock.Atoms.HoldsN

set_option autoImplicit false

namespace Nock.RedTeam.Batch2404

open Nock Nock.FieldEmbedding Nock.Atoms Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVGenuineF

example (x : P8PublicClaim) :
    HoldsN x = ∃ fuel, Nock.evalN fuel x.subject x.formula = some x.result := rfl

example {q : ℕ} (hq : 1 < q) {x : P8PublicClaim} (hx : HoldsF q x)
    (hs : BoundedBy q x.subject) (hf : BoundedBy q x.formula)
    (hguard : ∃ fuel r, evalGBy q fuel x.subject x.formula = some r) : HoldsN x :=
  holdsN_of_holdsF hq hx hs hf hguard

example {q : ℕ} (hq : 1 < q) {x : P8PublicClaim}
    (hs : BoundedBy q x.subject) (hf : BoundedBy q x.formula)
    (hguard : ∃ fuel r, TraceGen.evalGRom q fuel x.subject x.formula = some r) :
    HoldsN x ↔ HoldsF q x :=
  holdsN_iff_holdsF_of_evalGRom hq hs hf hguard

example {q : ℕ} (hq : 1 < q) {fuel : ℕ} {s f r : Nock.Noun}
    (hs : BoundedBy q s) (hf : BoundedBy q f) (h : TraceGen.evalGRom q fuel s f = some r) :
    Nock.evalN fuel s f = some r ∧ evalFBy q fuel s f = some r ∧ BoundedBy q r :=
  evalGRom_evalN_evalFBy hq hs hf h

example : HoldsF p (crossClaim 0) ∧ ¬ HoldsN (crossClaim 0) := holdsF_not_holdsN_at_crossing
example : HoldsN (crossClaim p) ∧ ¬ HoldsF p (crossClaim p) := holdsN_not_holdsF_at_crossing
example : (¬ ∀ x, HoldsF p x → HoldsN x) ∧ (¬ ∀ x, HoldsN x → HoldsF p x) :=
  holdsN_holdsF_incomparable
example : crossClaim 0 = ⟨.atom (p - 1), .cell (.atom 4) (.cell (.atom 0) (.atom 1)), .atom 0⟩ :=
  rfl

end Nock.RedTeam.Batch2404

#print axioms Nock.Atoms.holdsN_of_holdsF
#print axioms Nock.Atoms.holdsF_of_holdsN
#print axioms Nock.Atoms.holdsN_iff_holdsF_of_guard
#print axioms Nock.Atoms.holdsN_iff_holdsF_of_evalGRom
#print axioms Nock.Atoms.evalGRom_evalN_evalFBy
#print axioms Nock.Atoms.holdsF_not_holdsN_at_crossing
#print axioms Nock.Atoms.holdsN_not_holdsF_at_crossing
#print axioms Nock.Atoms.no_guard_at_crossing
#print axioms Nock.Atoms.holdsN_holdsF_incomparable
