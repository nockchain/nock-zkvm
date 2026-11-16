/-
  Nock/RedTeam/Batch480Thm54QueueGateWitnesses.lean

  Negative controls (every `α`, every field):
  * `fo5_rejected_by_ratio_gate` — `Batch469`'s `fo5 = (0,0,2,0,2)` (the OP9 self-calling
    core, `Batch472::loop_diverges`) has `q(1) = 1 + Sf fo5 1 − 1 = 0`, so the transition
    gate `count(1) ≠ ln(1)` is `α ≠ α`: rejected.
  * `fo5_rejected_by_acc_gate` — every `WalkSat` instance of `Batch469`'s shape has
    `acc(1) = −R·α + R·α = 0`: rejected by the client's form.
  * `fo3_rejected_by_ratio_gate` — `Batch470`'s memory shape `kroots = 1`, `fo3 = (0,0,2)`:
    `q(1) = 0`, rejected.
  * `fo020_rejected_by_ratio_gate` — census #5's `(0,2,0)` (`Batch459::walkSat_without_bfsValid`):
    `q(1) = 0`, rejected.
  * `walkSat_without_tiling_rejected` — `Batch459`'s `h = 2`, `fo = (0,0)`: `q(1) = 0`,
    rejected by the transition gate (the tiling witness dies at the FIRST gate, before the
    terminal one is consulted).

  Cost ledger (strings, instrument: the gate files named):
  * ratio form: `walk_inv : 𝕂` (`e = 3` base columns), gates `notLast·(walk_inv·(count−ln) − 1)`
    (degree 3 with the last-row mask, as the deployed `walkStepGates` are masked:
    `OptimizedMemoryGateBasis.walkStepGates` `(1 − bcur 5)·…`, compute `notLastCoeff`) and
    `isLast·(count − ln)` (degree 2) — `2·e = 6` base gates in the `s` accounting, not "2 gates".  The brief's
    "degree ≤ 2" holds only without the mask.
  * acc form (client): `acc_inv : 𝕂` (`e = 3`), one gate `notLast·(acc·acc_inv − 1)` (degree 3),
    `e = 3` base gates; the terminal `out_walk = acc(h)` already exists.  Cheapest, but leaves
    the overflow branch (`Batch479::tiling_or_overflow_of_acc_nonzero`) and makes completeness
    statistical (`Batch479::honest_acc_zero_is_root_event`).
  * `Walk.QGate` (K side, proofs exist: `bfsValid_of_qgate`, `Sf_tiling_of_qgate`): `q, qinv : 𝔽`
    (2 base columns), 4 base gates (boundary, transition with the one-hot fanout sum,
    `q·qinv = 1`, terminal), degree ≤ 3 with masks; side condition `1 + Sf fo h < p ∧ h < p`
    on the CHARACTERISTIC — no coin event, perfect completeness, but a hypothesis
    `h < p` that `nockCompiles_zmod` does not carry (`hp : 25 ≤ p`; `hΛp` bounds leaf counts,
    not rows) — a §1 change, unless `h < p` is derived from `hbound`/`hcomp` (not checked
    here).
-/
import Nock.RedTeam.Batch478Thm54QueueGateRatioForm
import Nock.RedTeam.Batch479Thm54QueueGateAccForm
import Nock.RedTeam.Batch469Thm54GarbageWitness
import Nock.RedTeam.Batch470Thm54MemoryPrefix

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch480

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk

section Witnesses
variable {K : Type} [Field K]

/-- `Batch469`'s `fo5 = (0,0,2,0,2)`: `1 + Sf fo5 1 = 1`. -/
theorem fo5_Sf_one : 1 + Sf Batch469.fo5 1 = 1 := by decide

/-- **The OP9 self-caller shape is rejected by the ratio gate at every `α`.** -/
theorem fo5_rejected_by_ratio_gate (α : K) :
    ¬ (∀ i, 1 ≤ i → i < 5 → α ^ (1 + Sf Batch469.fo5 i) ≠ α ^ i) := by
  intro hgate
  exact hgate 1 (le_refl 1) (by norm_num) (by rw [fo5_Sf_one])

/-- **The OP9 self-caller shape is rejected by the client's acc gate at every `α`:** every
`WalkSat` instance of the shape has `acc 1 = 0`. -/
theorem fo5_rejected_by_acc_gate (R L N L' M α : K) (ln count acc : ℕ → K)
    (hw : WalkSat (Batch469.cur5 R L N L' M) (Batch469.chld5 L N L' M) Batch469.fo5
      ln count acc α (R * α) α 5) :
    acc 1 = 0 := by
  have hseed : R * α = Batch469.cur5 R L N L' M 1 * α := by simp [Batch469.cur5]
  rw [acc_closed hw hseed rfl 1 (le_refl 1) (by norm_num), nodeListP_eval, nodeQueueP_eval]
  simp [Batch469.cur5, Batch469.fo5]

/-- Hence the shape fails the acc gate. -/
theorem fo5_acc_gate_unsat (R L N L' M α : K) (ln count acc : ℕ → K)
    (hw : WalkSat (Batch469.cur5 R L N L' M) (Batch469.chld5 L N L' M) Batch469.fo5
      ln count acc α (R * α) α 5) :
    ¬ (∀ k, 1 ≤ k → k < 5 → acc k ≠ 0) := by
  intro hgate
  exact hgate 1 (le_refl 1) (by norm_num) (fo5_rejected_by_acc_gate R L N L' M α ln count acc hw)

/-- `Batch470`'s memory shape (`kroots = 1`, `fo3 = (0,0,2)`) is rejected by the ratio gate. -/
theorem fo3_rejected_by_ratio_gate (α : K) :
    ¬ (∀ i, 1 ≤ i → i < 3 → α ^ (1 + Sf Batch470.fo3 i) ≠ α ^ i) := by
  intro hgate
  exact hgate 1 (le_refl 1) (by norm_num) (by simp [Sf, Batch470.fo3])

/-- Census #5's `(0,2,0)` (`Batch459::walkSat_without_bfsValid`) is rejected by the ratio gate. -/
theorem fo020_rejected_by_ratio_gate (α : K) :
    ¬ (∀ i, 1 ≤ i → i < 3 →
        α ^ (1 + Sf (fun i => if i = 2 then 2 else 0) i) ≠ α ^ i) := by
  intro hgate
  exact hgate 1 (le_refl 1) (by norm_num) (by simp [Sf])

/-- `Batch459::walkSat_without_tiling`'s `h = 2`, `fo = (0,0)` is rejected at the FIRST gate. -/
theorem walkSat_without_tiling_rejected (α : K) :
    ¬ (∀ i, 1 ≤ i → i < 2 → α ^ (1 + Sf (fun _ => 0) i) ≠ α ^ i) := by
  intro hgate
  exact hgate 1 (le_refl 1) (by norm_num) (by simp [Sf])

end Witnesses

/-! ## Cost ledger -/

def costLedger : List (String × String) :=
  [("ratio form", "1 K column (e=3), 2 K gates (2e=6 base gates), degree 3 masked / 2 unmasked; tiling forced; terminal event ≤ (d+1)/|K|; completeness needs h ≤ orderOf α"),
    ("acc form (client)", "1 K column (e=3), 1 K gate (e=3 base gates), degree 3 masked; tiling NOT forced (overflow branch); completeness statistical O(h²)/|K|"),
    ("Walk.QGate (K side)", "2 F columns, 4 base gates, degree ≤ 3 masked; no coin event, perfect completeness; needs 1 + Sf < p ∧ h < p — not among nockCompiles_zmod's hypotheses"),
    ("deployed chips today", "no queue gate (Batch462 inventory at f4b9575); compiler walk α = 0 (GenNockCompilesBounded.lean:447,639)")]

theorem costLedger_length : costLedger.length = 4 := by decide

end Nock.RedTeam.Batch480

#print axioms Nock.RedTeam.Batch480.fo5_rejected_by_ratio_gate
#print axioms Nock.RedTeam.Batch480.fo5_rejected_by_acc_gate
#print axioms Nock.RedTeam.Batch480.fo5_acc_gate_unsat
#print axioms Nock.RedTeam.Batch480.fo3_rejected_by_ratio_gate
#print axioms Nock.RedTeam.Batch480.fo020_rejected_by_ratio_gate
#print axioms Nock.RedTeam.Batch480.walkSat_without_tiling_rejected
