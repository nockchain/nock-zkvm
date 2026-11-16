/-
  Nock/RedTeam/Batch468Thm54WalkPrefixAlphaEvent.lean

`Thm:Walk_IOP` and its proof (`:2301`) price the root event of
  `node_list(X) − node_queue_h(X)` at `h/|K|`.  That constant is the degree bound
  `deg(node_queue_h) = 1 + Σ fanout` (`:2278`) read as `≤ h`, i.e. it PRESUPPOSES the tiling
  `1 + Σ fanout ≤ h` — `Walk.walk_soundness_card` carries it as `hdeg`.  Without a queue gate a
  hostile fanout column need not tile, so the honest event is `Walk.walkPrefixAlphaEvent`
  (`Nock/WalkPrefix.lean`) with size `≤ max h (1 + Sf fo h)`:

  * `compute_alpha_event_card_le`: at the compute walk's `fanoutComp ≤ 3`
    (`fanoutComp_le_three` below, the same fact as `Batch433::fanout_le_three`) the event has size `≤ 1 + 3h`;
  * `paper_constant_iff_tiling` (re-exported): the paper's `h` is the bound iff `1 + Sf ≤ h`;
  * `paper_constant_fails_without_tiling`: the concrete `h = 1`, `fo 1 = 3` has
    `max h (1 + Sf) = 4 > 1` — a one-row table whose queue polynomial has degree `4`, so the
    root-count `h = 1` is not a bound for it (the event's size is `≤ 4`, and a degree-`4`
    nonzero polynomial can have `4` roots).
  * `alpha_event_membership`: `WalkSat ∧ out_walk = 0` with the recognizer inputs puts every
    non-identity table's coin in the event (`Walk.isFullBFT_or_mem_alphaEvent`).

  No event is added to the union here.

  -- the paper
-/
import Nock.WalkPrefix
import Nock.NockVM

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch468

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable

section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem fanoutComp_le_three (st : State) : fanoutComp st ≤ 3 := by
  cases st <;> decide

/-- **The compute walk's α-event has size `≤ 1 + 3h`** for ANY state column `st`, with no
tiling and no queue-validity hypothesis (`fanoutComp ≤ 3`). -/
theorem compute_alpha_event_card_le (cur : ℕ → K) (chld' : ℕ → ℕ → K) (st : ℕ → State)
    (h : ℕ) :
    (walkPrefixAlphaEvent cur chld' (fun i => fanoutComp (st i)) h).card ≤ 1 + h * 3 :=
  walkPrefixAlphaEvent_card_le_arity cur chld' _ h (by norm_num)
    (fun i => fanoutComp_le_three (st i))

/-- The paper's constant `h` is the event bound iff the table tiles. -/
theorem paper_constant_iff (fo : ℕ → ℕ) (h : ℕ) :
    max h (1 + Sf fo h) = h ↔ 1 + Sf fo h ≤ h :=
  paper_constant_iff_tiling fo h

/-- Negative control for the paper's constant: one row of fanout `3` (an `OP_2` root with no
children rows) — the degree-free bound is `4`, not `h = 1`. -/
theorem paper_constant_fails_without_tiling :
    max 1 (1 + Sf (fun _ => 3) 1) = 4 ∧ ¬ (1 + Sf (fun _ => 3) 1 ≤ 1) := by
  simp [Sf]

/-- A degree-`4` witness at `h = 1`: the queue polynomial `X²+X³+X⁴` of a root declaring three
children of RLC `1`, against `node_list = C (cur 1) · X`: the difference is nonzero of
`natDegree 4`, so `card_roots_le` gives `4`, and nothing gives `1`. -/
theorem degree_four_at_one_row (r : K) :
    (nodeQueueP (fun _ => r) (fun _ _ => (1 : K)) (fun _ => 3) 1
      - nodeListP (fun _ => r) 1).natDegree = 4 := by
  have hq : nodeQueueP (fun _ => r) (fun _ _ => (1 : K)) (fun _ => 3) 1
      = C r * X + (X ^ 2 + X ^ 3 + X ^ 4) := by
    unfold nodeQueueP queueTerm
    rw [Finset.Icc_self, Finset.sum_singleton]
    have h3 : Finset.Icc (1 : ℕ) 3 = {1, 2, 3} := by decide
    rw [h3]
    simp [Sf]
    ring
  have hl : nodeListP (fun _ => r) 1 = C r * X := by
    unfold nodeListP; rw [Finset.Icc_self, Finset.sum_singleton, pow_one]
  rw [hq, hl]
  have : C r * X + (X ^ 2 + X ^ 3 + X ^ 4) - C r * X = (X ^ 2 + X ^ 3 + X ^ 4 : K[X]) := by ring
  rw [this]
  compute_degree!

/-- Membership: an accepted non-identity table's coin lies in the event (recognizer inputs
`seed = α·cur 1`, `initial_count = α`). -/
theorem alpha_event_membership {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α : K} {h : ℕ}
    (hw : WalkSat cur chld' fo ln count acc α (cur 1 * α) α h) (hout : acc h = 0)
    (hne : ¬ IsFullBFT cur chld' fo h) :
    α ∈ walkPrefixAlphaEvent cur chld' fo h := by
  rcases isFullBFT_or_mem_alphaEvent hw rfl rfl hout with h1 | h2
  · exact absurd h1 hne
  · exact h2

end

/-- Coordination record: no committed walk-α event name to reuse at the time of writing. -/
def walkAlphaLaneCoordination : String :=
  "lean-w0 at 05c2932, uncommitted edits, no Batch46[3-6] file; generic shape Walk.walkPrefixAlphaEvent"


def alphaEventNotInUnion : String :=
  "walkPrefixAlphaEvent at alphaC c.1 is not a summand of ProductionP8Containment.FailureUnion"

end Nock.RedTeam.Batch468

#print axioms Nock.RedTeam.Batch468.compute_alpha_event_card_le
#print axioms Nock.RedTeam.Batch468.paper_constant_fails_without_tiling
#print axioms Nock.RedTeam.Batch468.degree_four_at_one_row
#print axioms Nock.RedTeam.Batch468.alpha_event_membership
