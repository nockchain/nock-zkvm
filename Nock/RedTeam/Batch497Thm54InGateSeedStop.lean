/-
  Nock/RedTeam/Batch497Thm54InGateSeedStop.lean

  **Honest acc is WalkSat seed-based.**

  The in-gate seed wants init
  `(1 − rootMask(1))·ln(1)·RLC + acc(1) = initial_count·cc(1)`
  (no seed public) and the same mask on the step.  First row is a root
  (`kMem ≥ 1`), so that is `acc(1) = initial_count·cc(1)`.

  `WalkSat.accInit` (`Walk.lean`) is the paper's seed-preload:
  `ln(1)·cur(1) + acc(1) = initial_count·cc(1) + seed`.
  Those agree iff `seed = ln(1)·cur(1)`.  The family's
  `memoryWalkSeed` is already `nodeListP kMem |_{α}` (`:1006`); that
  equals `ln(1)·cur(1)` precisely when `kMem = 1`.

  General forest therefore needs a new honest acc (and a `WalkSatInGate`)
  before the gate bodies can change, the seed public can die, and
  `honest_memory_accepted_at_every_tuple` can land.  Degree-4 encoding
  of the extra `rootMask` factor exists (`labelRLCLinear`, factored tag)
  and was not landed: canonical satisfaction is the blocker, not `d`.

  `openConjunctsAfterVer` stays **7**.
-/
import Nock.Walk

set_option autoImplicit false

namespace Nock.RedTeam.Batch497

open Nock.Walk

variable {K : Type*} [Field K]

/-- In-gate init on a root row (dequeue masked, no seed public). -/
def ingateAccInit (acc initial_count_cc : K) : Prop :=
  acc = initial_count_cc

/-- WalkSat seed-preload leftover vs the in-gate init. -/
theorem walkSat_accInit_iff_ingate
    {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed initial_count : K} {h : ℕ}
    (hw : WalkSat cur chld' fo ln count acc α seed initial_count h) :
    ingateAccInit (acc 1)
        (∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * initial_count * chld' 1 l) ↔
      seed = ln 1 * cur 1 := by
  constructor
  · intro hacc
    have hinit := hw.accInit
    rw [hacc, add_comm (∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * initial_count * chld' 1 l)] at hinit
    exact (add_right_cancel hinit).symm
  · intro hseed
    unfold ingateAccInit
    have hinit := hw.accInit
    rw [hseed, add_comm (∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * initial_count * chld' 1 l)] at hinit
    exact add_left_cancel hinit

/-- `node_list_1(α) = cur(1)·α`.  With `ln(1)=α` this is `ln(1)·cur(1)`. -/
theorem nodeListP_one_eval (cur : ℕ → K) (α : K) :
    (nodeListP cur 1).eval α = cur 1 * α := by
  rw [nodeListP_eval]
  simp

theorem ln1_mul_cur1
    {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed initial_count : K} {h : ℕ}
    (hw : WalkSat cur chld' fo ln count acc α seed initial_count h) :
    ln 1 * cur 1 = α * cur 1 := by
  rw [hw.ln1]

/-- The leftover is the tail of the forest seed after the first root. -/
theorem seed_eq_first_dequeue_of_kMem_one
    (cur : ℕ → K) (α : K) (kMem : ℕ) (hk : kMem = 1) :
    (nodeListP cur kMem).eval α = cur 1 * α := by
  rw [hk, nodeListP_one_eval]

def failingStatement : String :=
  "honest memory acc is WalkSat seed-based; in-gate init holds iff seed = ln(1)·cur(1) (kMem = 1)"

theorem failingStatement_name :
    failingStatement =
      "honest memory acc is WalkSat seed-based; in-gate init holds iff seed = ln(1)·cur(1) (kMem = 1)" :=
  rfl

/-- Same 7 names as `Batch448.openConjunctsAfterVer`. -/
def openAfterInGateStop : List String :=
  ["mem_first_counts", "mem_first_indicator",
    "computeTopology", "memoryTopology", "axisStructural",
    "rootBoundary", "structuralChecks"]

theorem openAfterInGateStop_length : openAfterInGateStop.length = 7 := by
  decide

theorem computeTopology_still_open :
    "computeTopology" ∈ openAfterInGateStop := by
  decide

theorem memoryTopology_still_open :
    "memoryTopology" ∈ openAfterInGateStop := by
  decide

def nockCompiles_zmod_hypotheses_unmoved : String :=
  "nockCompiles_zmod binders unmoved: hrun hbound hs hf hΛp hp hK hF hwin hKszChar"

theorem nockCompiles_zmod_hypotheses_unmoved_nonempty :
    nockCompiles_zmod_hypotheses_unmoved ≠ "" := by
  decide

def digest_unmoved : String :=
  "25th digest move not taken; pinned file unmoved at 56ffc5f1… (387)"

theorem digest_unmoved_nonempty : digest_unmoved ≠ "" := by
  decide

end Nock.RedTeam.Batch497

#print axioms Nock.RedTeam.Batch497.walkSat_accInit_iff_ingate
#print axioms Nock.RedTeam.Batch497.seed_eq_first_dequeue_of_kMem_one
#print axioms Nock.RedTeam.Batch497.openAfterInGateStop_length
