/-
  Nock/RedTeam/Batch2551Thm54JetInterp.lean

  Restates the exact statements by `example` (a change of
  any statement breaks this file), adds negative controls and prints the axioms.

  * `interp_sound`: skeleton + `LocalOK` + `NodeLookupSound` + `ReadsGenuine` ⇒ output = `T.sem`,
    and `HoldsN ⟨s, compile p T, out⟩` (via J-2's `compile_rel_iff_holdsN`).
  * `interp_complete`: the honest table satisfies every constraint and outputs `T.sem p s`.
  * `nodesOf_length`: rows = `exSz body + Σ_i (1 + gSz (inTy i))`.
  * Matmul: `n = 2` honest table (103 rows, kernel), one tampered row rejected; `n = 8` 4,423 rows.
  * NC: the soundness hypotheses are not vacuous (the honest table meets them), and the tampered
    table fails `LocalOK`, so `interp_sound` cannot be applied to it.
-/
import Nock.Jet.Interp

set_option autoImplicit false

namespace Nock.RedTeam.Batch2551

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp

/-! ## Statements -/

example {p : ℕ} (hp : 0 < p) (T : Tpl) (hT : T.WellTyped p) (s : Noun) (t : JTable) (c : ℕ)
    (hsk : (callRows t c).map JRow.node = nodesOf T)
    (hloc : ∀ r ∈ callRows t c, LocalOK p r) (hlk : NodeLookupSound (callRows t c))
    (hrd : ReadsGenuine s (callRows t c)) (out : JRow) (hout : out ∈ callRows t c)
    (hid : out.node.id = 0) :
    T.sem p s = some out.val ∧ HoldsN ⟨s, compile p T, out.val⟩ :=
  interp_sound hp T hT s t c hsk hloc hlk hrd out hout hid

example {p : ℕ} (hp : 0 < p) (T : Tpl) (hT : T.WellTyped p) (s r : Noun) (c : ℕ)
    (h : T.sem p s = some r) :
    callRows (honestRows p T s c) c = honestRows p T s c ∧
    (honestRows p T s c).map JRow.node = nodesOf T ∧
    (∀ row ∈ honestRows p T s c, LocalOK p row) ∧
    NodeLookupSound (honestRows p T s c) ∧
    ReadsGenuine s (honestRows p T s c) ∧
    ∃ out ∈ honestRows p T s c, out.node.id = 0 ∧ out.val = r :=
  interp_complete hp T hT s r c h

example (T : Tpl) : (nodesOf T).length = exSz T.body + inSz T (List.finRange T.k) :=
  nodesOf_length T

/-- `NodeLookupSound` is exactly one functional map serving provides and used consumes. -/
example (rows : List JRow) : NodeLookupSound rows ↔
    ∃ look : ℕ → Noun, (∀ r ∈ rows, look r.node.id = r.val) ∧
      ∀ r ∈ rows, (0 < r.node.op.arity → r.x = look r.node.a) ∧
        (1 < r.node.op.arity → r.y = look r.node.b) := Iff.rfl

/-- `ReadsGenuine` asserts only what a genuine record asserts: subject axis reads, `nth`/`tail`
reads of a noun, and the cell of a `pair`. -/
example (s : Noun) (rows : List JRow) : ReadsGenuine s rows ↔
    ∀ r ∈ rows, readOK s r.node.op r.val r.x r.y = true := Iff.rfl

/-! ## Matmul -/

example : matmulRows 2 = 103 := matmul2_rows
example : matmulRows 8 = 4423 := matmul8_rows
example : exSz (matmulT 8).body = 4113 := matmul8_body
example : toyRows.length = 103 := toyRows_length

/-! ## Negative controls -/

/-- Non-vacuity: the honest 2×2 table meets every hypothesis of `interp_sound`. -/
theorem toy_hyps_met :
    (callRows toyRows 0).map JRow.node = nodesOf (matmulT 2) ∧
    (∀ r ∈ callRows toyRows 0, LocalOK 7 r) ∧ NodeLookupSound (callRows toyRows 0) ∧
    ReadsGenuine toyS (callRows toyRows 0) := by
  obtain ⟨hc, hsk, hl, hk, hr, -⟩ := toy_complete
  rw [hc]; exact ⟨hsk, hl, hk, hr⟩

/-- The tampered table (row 3, the degree-2 gate, claims `1·5 = 6`) is rejected. -/
example : ¬ ∀ row ∈ toyTampered, LocalOK 7 row := toyTampered_rejected

/-- The tampered row's operands are the honest ones; only the value moved. -/
example : toyRows[3]? = some ⟨⟨3, .mul, 4, 7⟩, 0, .atom 5, .atom 1, .atom 5⟩ := toyRow3

/-- A wrong output claim cannot pass: every accepted table outputs `toyC`. -/
example (t : JTable) (hsk : (callRows t 0).map JRow.node = nodesOf (matmulT 2))
    (hloc : ∀ r ∈ callRows t 0, LocalOK 7 r) (hlk : NodeLookupSound (callRows t 0))
    (hrd : ReadsGenuine toyS (callRows t 0)) (out : JRow) (hout : out ∈ callRows t 0)
    (hid : out.node.id = 0) : out.val = toyC :=
  toy_sound_output t hsk hloc hlk hrd out hout hid

/-! ## Axioms -/

#print axioms interp_sound
#print axioms interp_complete
#print axioms nodesOf_length
#print axioms toy_complete
#print axioms toy_sound_output
#print axioms toyTampered_rejected
#print axioms matmul8_rows
#print axioms toyRows_length
#print axioms toy_hyps_met

end Nock.RedTeam.Batch2551
