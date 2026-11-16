/-
  Nock/RedTeam/Batch22Thm54ModularOperational.lean

  `BoundSemanticTrace.SkeletonOperationalCore` still carries an `s4_noOverflow` field of the form
  `IncrementNoOverflow q value`.  That obligation is a *Nat-evaluator artifact*: it only matters for
  the unbounded increment `incNoWrap`/`Noun.lus`, which crashes when it would leave the range.  Under
  the strict **modular** OP4 fixed in Packet 0 (`lusFBy q`, i.e. `(n+1) mod q`), the increment is
  *total* — it wraps instead of crashing — so no no-overflow side condition is needed.

  These receipts make that precise:

  * `b22_modular_op4_total` — `lusFBy q` succeeds on every atom.
  * `b22_incNoWrap_fails_at_top` — the Nat increment guard fails exactly at the top residue…
  * `b22_modular_op4_succeeds_at_top` — …while modular OP4 wraps to `0` there.

  Consequence: the strict language removes `s4_noOverflow` from the per-row operational content; only
  the served-lookup / record facts (`s0`/`s9`), which are genuine memory-binding obligations, remain.
-/

import Nock.FieldEmbedding
import Nock.NockVMROM.Thm54.OpcodeSemantics

namespace Nock.RedTeam.Batch22

open Nock Nock.Noun
open Nock.NockVMROM.Thm54

/-- **Modular OP4 is total.**  `lusFBy q` always succeeds on an atom — no overflow crash. -/
theorem b22_modular_op4_total (q : ℕ) (n : ℕ) :
    (FieldEmbedding.lusFBy q (.atom n)).isSome = true := by
  simp [FieldEmbedding.lusFBy]

/-- **Modular OP4 wraps at the top residue.**  Incrementing `q-1` modulo `q` yields `0`. -/
theorem b22_modular_op4_succeeds_at_top (q : ℕ) (hq : 0 < q) :
    FieldEmbedding.lusFBy q (.atom (q - 1)) = some (.atom 0) := by
  simp only [FieldEmbedding.lusFBy, Option.some.injEq]
  have hq' : q - 1 + 1 = q := by omega
  rw [hq', Nat.mod_self]

/-- **The Nat no-overflow guard fails exactly at the top residue.**  So `s4_noOverflow` is a genuine
obstruction *only* for the unbounded evaluator — the one Packet 0 does not use. -/
theorem b22_incNoWrap_fails_at_top (q : ℕ) :
    ¬ OpcodeSemantics.IncrementNoOverflow q (.atom (q - 1)) := by
  cases q with
  | zero => simp [OpcodeSemantics.IncrementNoOverflow]
  | succ k =>
      simp only [OpcodeSemantics.IncrementNoOverflow, Nat.succ_sub_one]
      omega

/-- **Below the top, the guard holds** (non-vacuity of the contrast). -/
theorem b22_incNoWrap_holds_below_top (q n : ℕ) (h : n + 1 < q) :
    OpcodeSemantics.IncrementNoOverflow q (.atom n) := by
  simpa [OpcodeSemantics.IncrementNoOverflow] using h

end Nock.RedTeam.Batch22

#print axioms Nock.RedTeam.Batch22.b22_modular_op4_total
#print axioms Nock.RedTeam.Batch22.b22_modular_op4_succeeds_at_top
#print axioms Nock.RedTeam.Batch22.b22_incNoWrap_fails_at_top
