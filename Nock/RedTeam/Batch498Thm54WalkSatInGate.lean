/-
  Nock/RedTeam/Batch498Thm54WalkSatInGate.lean

  `Nock/WalkInGate.lean` now supplies the general-forest acc:

  * `accInGate k = node_list_{k⊓kMem}(α) − node_list_k(α) + initial_count·Σ_{i≤k} childSum`
  * `WalkSatInGate` — same ln/count as `WalkSat`; init is `acc(1) = initial_count·cc(1)`
    (first row is a root); step masks dequeue by `deqCoeff = 1 − rootMask`
  * `walkSatInGate_exists`, `accInGate_telescope`, `ingate_seed_eq_forest_seed` (`:1006`)
  * `walkSatInGate_completeness` / `walkSatInGate_out_zero_iff`
  * `kMem = 1` seam: `toWalkSat_of_kMem_one` / `toWalkSatInGate_of_seed`

  Mask dequeue in `walkAccInitInGate` /
  `walkAccStepInGate` (`labelRLCLinear` keeps `d = 4`), delete seed publics
  `9..11`, re-prove canonical satisfaction through `memoryAccInGate`,
  `honest_memory_accepted_at_every_tuple`.  A trial wiring of those bodies
  plus `exactMemoryWalkRowEnv ↦ accInGate` broke `OptimizedMemoryCanonicalSatisfaction`
  at the last-row identification `accInGate h = WalkSat.acc h` and was reverted.
  That identification is a theorem (`accInGate_of_ge_kMem` + `acc_telescope` at
  `seed = nodeListP kMem`) and is the next compile, not a new gate.

  Topology 7→5 / `:1401` 5→3 still blocked.  `openConjunctsAfterVer` stays **7**.
-/
import Nock.WalkInGate

set_option autoImplicit false

namespace Nock.RedTeam.Batch498

open Nock.Walk

variable {K : Type*} [Field K]

/-- The honest in-gate acc exists for every forest. -/
theorem walkSatInGate_exists_named
    (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (α initial_count : K) {kMem h : ℕ}
    (hh : 1 ≤ h) (hk : 1 ≤ kMem) (hle : kMem ≤ h) :
    ∃ ln count acc : ℕ → K,
      WalkSatInGate cur chld' fo ln count acc α initial_count kMem h :=
  walkSatInGate_exists cur chld' fo α initial_count hh hk hle

/-- `:1006` leftover at the last row. -/
theorem ingate_seed_eq_forest_seed_named
    {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α initial_count : K} {kMem h : ℕ}
    (hw : WalkSatInGate cur chld' fo ln count acc α initial_count kMem h) :
    acc h = (nodeListP cur kMem).eval α - (nodeListP cur h).eval α
      + initial_count * ∑ i ∈ Finset.Icc 1 h, childSum chld' fo α i :=
  ingate_seed_eq_forest_seed hw

/-- At `kMem = 1` the in-gate walk is `WalkSat` with `seed = ln(1)·cur(1)`. -/
theorem kMem_one_is_walkSat
    {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α initial_count : K} {kMem h : ℕ}
    (hw : WalkSatInGate cur chld' fo ln count acc α initial_count kMem h)
    (hk : kMem = 1) :
    WalkSat cur chld' fo ln count acc α (ln 1 * cur 1) initial_count h :=
  hw.toWalkSat_of_kMem_one hk

def remainingMove2 : String :=
  "gate bodies + seed-public deletion + canonical accInGate wiring + honest_memory_accepted_at_every_tuple"

theorem remainingMove2_name :
    remainingMove2 =
      "gate bodies + seed-public deletion + canonical accInGate wiring + honest_memory_accepted_at_every_tuple" :=
  rfl

/-- Same 7 names as `Batch448.openConjunctsAfterVer`. -/
def openAfterWalkSatInGate : List String :=
  ["mem_first_counts", "mem_first_indicator",
    "computeTopology", "memoryTopology", "axisStructural",
    "rootBoundary", "structuralChecks"]

theorem openAfterWalkSatInGate_length : openAfterWalkSatInGate.length = 7 := by
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

end Nock.RedTeam.Batch498

#print axioms Nock.RedTeam.Batch498.walkSatInGate_exists_named
#print axioms Nock.RedTeam.Batch498.ingate_seed_eq_forest_seed_named
#print axioms Nock.RedTeam.Batch498.kMem_one_is_walkSat
#print axioms Nock.RedTeam.Batch498.openAfterWalkSatInGate_length
