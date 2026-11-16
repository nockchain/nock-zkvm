import Nock.NockVMROM.Thm54.NounRealization
import Nock.NockVMROM.Thm54.OpcodeSemantics

/-!
# Candidate verifier-side bound gates (Track B0)

Two obstructions to arbitrary-prover soundness are **not coin events**: they are properties of the
prover's committed arrays, fixed before any challenge is sampled, so the probabilistic
failure-union counting framework cannot absorb them. Each therefore must become an explicit
**verifier check** in any future raw arbitrary-prover closure.

1. **Non-noun forgery.** `NounRealizationCounterRegression.badFP` is an accepted fingerprint whose
   leaf coordinate `badLeaf` is a field element with no bounded-natural preimage; `badRow` is a
   publicly accepted memory row built from it that satisfies no noun realization at any bound `q`
   (`badRow_not_nounRealized`). The gate that rejects it is a **decode/leaf-bound gate** requiring
   every accepted active fingerprint to be the global-carry encoding of a `q`-bounded noun — exactly
   `FPRealized`.
2. **OP4 overflow.** The field-modular increment `(1 + n) mod p` disagrees with Nock's unbounded
   `Noun.lus` at the top atom. The gate that rejects it is an **operand-bound gate**, exactly
   `OpcodeSemantics.IncrementNoOverflow q`, under which the two increments provably agree.

Both definitions are deterministic predicates with no `JointCoins` argument; that is the compiled
statement of "not a coin event". They are **not currently conjuncts of**
`ProductionRawVerifier.Message.VerifierChecks`. Wiring is not a type-only edit:

* `LeafBoundGate` needs a finite scan of every active fingerprint and a verifier-visible noun bound
  `q`; current production containment supplies `q` externally rather than storing it in the raw
  message or claim.
* `OP4BoundGate` takes a noun, while the raw row carries only the operand fingerprint. Identifying a
  decoded witness with the pre-seed skeleton operand needs the still-open Track-B assembly and
  pair-local collision bridge.

Accordingly this module compiles the exact predicates and counter-regressions without claiming that
production acceptance enforces them.
-/

namespace Nock.NockVMROM.Thm54.BoundGates

open Nock Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.NounRealizationCounterRegression

/-! ## Leaf/decode bound gate versus the non-noun forgery -/

/-- The candidate verifier-side leaf/decode bound gate: an accepted active fingerprint must be the
global-carry encoding of a `q`-bounded noun. This is a deterministic decode requirement on the
committed fingerprint, taking only `(z, q, fp)` — no `JointCoins`. -/
def LeafBoundGate {K : Type} [Field K] (z : K) (q : ℕ) (fp : ComputeTable.FP K) : Prop :=
  FPRealized z q fp

/-- **The non-noun forgery fails the leaf bound gate**, for every bound `q`: `badFP` has no bounded
noun preimage, so it is not `FPRealized`. -/
theorem badFP_fails_leafBoundGate (q : ℕ) :
    ¬ LeafBoundGate (1 : K289) q badFP :=
  badFP_not_realized q

/-- The gate is non-vacuous: any genuinely realized fingerprint passes it. -/
theorem leafBoundGate_of_realized {K : Type} [Field K] {z : K} {q : ℕ}
    {fp : ComputeTable.FP K} (h : FPRealized z q fp) :
    LeafBoundGate z q fp := h

/-- **The gate rejects the accepted `badRow`.** `badRow` is publicly accepted yet realizes no noun
at any `q`, so `acceptance ∧ leaf-bound-gate` excludes it. Compare `allZero`-style forgeries: this
one passes plain acceptance and is stopped only by the decode gate. -/
theorem leafBoundGate_rejects_badRow (q : ℕ) :
    MemoryPublicRowAccepted badRow ∧ ¬ MemoryPublicRowNounRealization q badRow :=
  ⟨badRow_publicAccepted, badRow_not_nounRealized q⟩

/-! ## OP4 operand-bound gate versus increment overflow -/

/-- The candidate verifier-side OP4 operand-bound gate: the increment operand must be a bounded atom with
`n + 1 < q`. Deterministic in `(q, operand)`; no `JointCoins`. -/
def OP4BoundGate (q : ℕ) (operand : Noun) : Prop :=
  OpcodeSemantics.IncrementNoOverflow q operand

/-- **Under the OP4 bound gate the two increments agree**: the field-modular `lusFBy` returns the
no-wrap successor, matching Nock's `Noun.lus` on atoms. -/
theorem op4BoundGate_forces_agreement {q : ℕ} {operand : Noun}
    (h : OP4BoundGate q operand) :
    FieldEmbedding.lusFBy q operand = some (OpcodeSemantics.incNoWrap operand) :=
  OpcodeSemantics.lusFBy_eq_incNoWrap h

/-- **The top atom `q − 1` fails the OP4 gate** (the overflow point). -/
theorem op4BoundGate_fails_at_top (q : ℕ) (hq : 0 < q) :
    ¬ OP4BoundGate q (.atom (q - 1)) := by
  simp only [OP4BoundGate, OpcodeSemantics.IncrementNoOverflow]
  omega

/-- **The atom one below the top passes the OP4 gate**, so the gate is non-vacuous and cuts exactly
at the overflow boundary. -/
theorem op4BoundGate_holds_below_top (q : ℕ) (hq : 1 < q) :
    OP4BoundGate q (.atom (q - 2)) := by
  simp only [OP4BoundGate, OpcodeSemantics.IncrementNoOverflow]
  omega

end Nock.NockVMROM.Thm54.BoundGates

#print axioms Nock.NockVMROM.Thm54.BoundGates.badFP_fails_leafBoundGate
#print axioms Nock.NockVMROM.Thm54.BoundGates.leafBoundGate_rejects_badRow
#print axioms Nock.NockVMROM.Thm54.BoundGates.op4BoundGate_forces_agreement
#print axioms Nock.NockVMROM.Thm54.BoundGates.op4BoundGate_fails_at_top
#print axioms Nock.NockVMROM.Thm54.BoundGates.op4BoundGate_holds_below_top
