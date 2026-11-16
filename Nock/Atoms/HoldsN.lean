/-
  Nock/Atoms/HoldsN.lean

  **The ℕ-Nock claim predicate `HoldsN` and its relation to the
  field predicate `HoldsF`.**

  * `HoldsN x := ∃ fuel, evalN fuel x.subject x.formula = some x.result`.
  * `holdsN_of_holdsF` — `HoldsF q ⇒ HoldsN` under the existing guards (`BoundedBy q` on subject and
    formula and a successful guarded run `evalGBy q`): `SVInductionGenericF.evalN_of_holdsF`
     restated at `HoldsN`.
  * `holdsF_of_holdsN` and `holdsN_iff_holdsF_of_guard` — the converse under the same guards, so
    on guarded inputs the two predicates coincide.
  * **Negative controls (the `p − 1 + 1` counterexample).**  At the Goldilocks prime `p`, subject
    `p − 1`, formula `[4 0 1]`: `HoldsF p ⟨p−1, [4 0 1], 0⟩` holds while `HoldsN` of it fails, and
    `HoldsN ⟨p−1, [4 0 1], p⟩` holds while `HoldsF p` of it fails.  So without the guard the two
    predicates differ in BOTH directions; and indeed no guarded run exists there
    (`no_guard_at_crossing`).
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1515Thm54SVInductionGenericF
import Nock.NockVMROM.Thm54.TraceGen.GenGuardedRom

set_option autoImplicit false

namespace Nock.Atoms

open Nock Nock.Noun Nock.FieldEmbedding
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SVGenuineF

/-- **The ℕ-Nock claim predicate** (SPEC-SEMANTICS S1.2): the claim's formula, run on its subject
under the reference interpreter `Nock.evalN` (Nock 4K atoms, increment `n ↦ n + 1`), returns its
result at some fuel. -/
def HoldsN (x : P8PublicClaim) : Prop :=
  ∃ fuel, Nock.evalN fuel x.subject x.formula = some x.result

/-- `HoldsF ⇒ HoldsN` under the existing guards: `SVInductionGenericF.evalN_of_holdsF`. -/
theorem holdsN_of_holdsF {q : ℕ} (hq : 1 < q) {x : P8PublicClaim} (hx : HoldsF q x)
    (hs : BoundedBy q x.subject) (hf : BoundedBy q x.formula)
    (hguard : ∃ fuel r, evalGBy q fuel x.subject x.formula = some r) : HoldsN x :=
  SVInductionGenericF.evalN_of_holdsF hq hx hs hf hguard

/-- The converse under the same guards: a guarded run fixes the result of both evaluators, so an
ℕ-run's result is the field-run's result. -/
theorem holdsF_of_holdsN {q : ℕ} (hq : 1 < q) {x : P8PublicClaim} (hx : HoldsN x)
    (hs : BoundedBy q x.subject) (hf : BoundedBy q x.formula)
    (hguard : ∃ fuel r, evalGBy q fuel x.subject x.formula = some r) : HoldsF q x := by
  obtain ⟨fuel, r, hG⟩ := hguard
  obtain ⟨hN, hF, -⟩ := agreeBy q hq fuel _ _ r hs hf hG
  obtain ⟨fuel', hN'⟩ := hx
  have : x.result = r := evalN_deterministic hN' hN
  exact ⟨fuel, this ▸ hF⟩

/-- **On guarded inputs `HoldsN` and `HoldsF q` coincide.** -/
theorem holdsN_iff_holdsF_of_guard {q : ℕ} (hq : 1 < q) {x : P8PublicClaim}
    (hs : BoundedBy q x.subject) (hf : BoundedBy q x.formula)
    (hguard : ∃ fuel r, evalGBy q fuel x.subject x.formula = some r) :
    HoldsN x ↔ HoldsF q x :=
  ⟨fun h => holdsF_of_holdsN hq h hs hf hguard, fun h => holdsN_of_holdsF hq h hs hf hguard⟩

/-- **The named bridge** (SPEC-SEMANTICS S1.2, "`evalGRom q fuel s f = some r → evalFBy q fuel s f =
some r ∧ evalN fuel s f = some r`"): on `q`-bounded inputs a guarded ROM run is a run of both the
ℕ-evaluator and the field evaluator, with the same result, and that result is `q`-bounded.
(`TraceGen.evalGRom_le_evalGBy` then `FieldEmbedding.agreeBy`.) -/
theorem evalGRom_evalN_evalFBy {q : ℕ} (hq : 1 < q) {fuel : ℕ} {s f r : Noun}
    (hs : BoundedBy q s) (hf : BoundedBy q f) (h : TraceGen.evalGRom q fuel s f = some r) :
    Nock.evalN fuel s f = some r ∧ evalFBy q fuel s f = some r ∧ BoundedBy q r :=
  agreeBy q hq fuel s f r hs hf (TraceGen.evalGRom_le_evalGBy h)

theorem holdsN_iff_holdsF_of_evalGRom {q : ℕ} (hq : 1 < q) {x : P8PublicClaim}
    (hs : BoundedBy q x.subject) (hf : BoundedBy q x.formula)
    (hguard : ∃ fuel r, TraceGen.evalGRom q fuel x.subject x.formula = some r) :
    HoldsN x ↔ HoldsF q x := by
  obtain ⟨fuel, r, h⟩ := hguard
  exact holdsN_iff_holdsF_of_guard hq hs hf ⟨fuel, r, TraceGen.evalGRom_le_evalGBy h⟩

/-! ## Negative controls: the `p − 1 + 1` crossing

At the Goldilocks prime `p = Nock.Field.p`, the program `*[p−1 [4 0 1]]` increments its subject.
ℕ-Nock returns `p`; the field evaluator returns `(p−1+1) % p = 0`. -/

/-- The crossing claim's formula `[4 [0 1]]` (increment the whole subject). -/
def incFormula : Noun := .cell (.atom 4) (.cell (.atom 0) (.atom 1))

/-- Every successful ℕ-run of `[4 [0 1]]` on atom `n` returns `n + 1`. -/
theorem evalN_incFormula {fuel n : ℕ} {r : Noun}
    (h : Nock.evalN fuel (.atom n) incFormula = some r) : r = .atom (n + 1) := by
  match fuel with
  | 0 => simp [evalN] at h
  | 1 => simp [evalN, incFormula] at h
  | k + 2 =>
    simp [evalN, incFormula, slot, lus] at h
    exact h.symm

/-- Every successful field run of `[4 [0 1]]` on atom `n` returns `(n + 1) % q`. -/
theorem evalFBy_incFormula {q fuel n : ℕ} {r : Noun}
    (h : evalFBy q fuel (.atom n) incFormula = some r) : r = .atom ((n + 1) % q) := by
  match fuel with
  | 0 => simp [evalFBy] at h
  | 1 => simp [evalFBy, incFormula] at h
  | k + 2 =>
    simp [evalFBy, incFormula, slot, lusFBy] at h
    exact h.symm

theorem evalN_incFormula_two (n : ℕ) :
    Nock.evalN 2 (.atom n) incFormula = some (.atom (n + 1)) := by
  simp [evalN, incFormula, slot, lus]

theorem evalFBy_incFormula_two (q n : ℕ) :
    evalFBy q 2 (.atom n) incFormula = some (.atom ((n + 1) % q)) := by
  simp [evalFBy, incFormula, slot, lusFBy]

/-- The claim `⟨p−1, [4 0 1], r⟩`. -/
def crossClaim (r : ℕ) : P8PublicClaim := ⟨.atom (p - 1), incFormula, .atom r⟩

/-- **NC 1.** `HoldsF p` holds at result `0` (wrap-around), `HoldsN` does not. -/
theorem holdsF_not_holdsN_at_crossing : HoldsF p (crossClaim 0) ∧ ¬ HoldsN (crossClaim 0) := by
  have hp : p - 1 + 1 = p := Nat.sub_add_cancel p_pos
  refine ⟨⟨2, ?_⟩, ?_⟩
  · simp only [crossClaim]
    rw [evalFBy_incFormula_two, hp, Nat.mod_self]
  · rintro ⟨fuel, h⟩
    have := Noun.atom.inj (evalN_incFormula (n := p - 1) (r := .atom 0) h)
    rw [hp] at this
    exact absurd this (Nat.ne_of_lt p_pos)

/-- **NC 2.** `HoldsN` holds at result `p` (ℕ increment), `HoldsF p` does not. -/
theorem holdsN_not_holdsF_at_crossing : HoldsN (crossClaim p) ∧ ¬ HoldsF p (crossClaim p) := by
  have hp : p - 1 + 1 = p := Nat.sub_add_cancel p_pos
  refine ⟨⟨2, ?_⟩, ?_⟩
  · simp only [crossClaim]
    rw [evalN_incFormula_two, hp]
  · rintro ⟨fuel, h⟩
    have := Noun.atom.inj (evalFBy_incFormula (n := p - 1) (r := .atom p) h)
    rw [hp, Nat.mod_self] at this
    exact absurd this (Nat.ne_of_gt p_pos)

/-- **NC 3.** The crossing has no guarded run, so the guards of `holdsN_iff_holdsF_of_guard` are
exactly what fails there (the inputs ARE `p`-bounded). -/
theorem no_guard_at_crossing :
    BoundedBy p (crossClaim 0).subject ∧ BoundedBy p (crossClaim 0).formula ∧
      ¬ ∃ fuel r, evalGBy p fuel (crossClaim 0).subject (crossClaim 0).formula = some r := by
  have hp1 : p - 1 < p := Nat.sub_lt p_pos one_pos
  refine ⟨hp1, ?_, ?_⟩
  · simp only [crossClaim, incFormula, BoundedBy_cell, BoundedBy_atom]
    refine ⟨?_, ?_, ?_⟩ <;> norm_num [p, Field.p]
  · rintro ⟨fuel, r, h⟩
    have hp : p - 1 + 1 = p := Nat.sub_add_cancel p_pos
    match fuel with
    | 0 => simp [evalGBy] at h
    | 1 => simp [evalGBy, crossClaim, incFormula] at h
    | k + 2 =>
      simp [evalGBy, crossClaim, incFormula, slot, lusGBy, hp] at h

/-- **NC 4.** So `HoldsN` and `HoldsF p` are incomparable in general: neither implies the other. -/
theorem holdsN_holdsF_incomparable :
    (¬ ∀ x, HoldsF p x → HoldsN x) ∧ (¬ ∀ x, HoldsN x → HoldsF p x) :=
  ⟨fun h => holdsF_not_holdsN_at_crossing.2 (h _ holdsF_not_holdsN_at_crossing.1),
   fun h => holdsN_not_holdsF_at_crossing.2 (h _ holdsN_not_holdsF_at_crossing.1)⟩

end Nock.Atoms
