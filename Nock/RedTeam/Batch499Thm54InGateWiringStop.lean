/-
  Nock/RedTeam/Batch499Thm54InGateWiringStop.lean

  **Chip acc vs hosted walkAcc census.**

  `WalkSatInGate` / `accInGate` / `:1006` are compiled.  A
  wiring attempt of the authorized gate-body change
  (`walkAccInitInGate` drops seed; `walkAccStepInGate` scales dequeue by
  `1 − rootMask(next)` through `labelRLCLinear`) plus putting `accInGate`
  on the physical walk-acc column was reverted.  The blocker is not `d`
  (`labelRLCLinear` is degree 1; the extra base mask stays at 4) and not
  a new `nockCompiles_zmod` hypothesis.

  The physical acc column is one column.  Hosted census Exprs
  (`walkBoundarySources` / `walkAccInit` / `forestSeedSource`) still
  evaluate the seed-preload formula on `exactMemoryWalkRowEnv`
  (`WalkSat.acc`).  In-gate MixedExpr gates need `accInGate` on that
  same column.  They agree only for `k ≥ kMem`; on root rows they
  differ.  Hosted `walkAccStep` cannot even name `rootMask` (base
  column 153) in `Expr`.

  `computeTopology_of_deployed` still
  carries `hγ` (priced event is `computePrefixGammaEventOf` on
  `computeSourceEnv`; topology reads `Vd`/`Cvd`/`foC` — transport
  remaining).  `openConjunctsAfterVer` stays **7**.

  Writer is not a pass on `WalkSatInGate` (same lane).
-/
import Nock.WalkInGate
import Nock.RedTeam.Batch498Thm54WalkSatInGate

set_option autoImplicit false

namespace Nock.RedTeam.Batch499

open Nock.Walk
open Nock.RedTeam.Batch498

variable {K : Type*} [Field K]

/-- The two accs agree past the last root, at the paper seed. -/
theorem accInGate_eq_walkSat_of_ge
    (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (α seed initial_count : K) {kMem k : ℕ}
    (hseed : seed = (nodeListP cur kMem).eval α)
    (hk : kMem ≤ k) (hk1 : 1 ≤ k)
    {ln count acc : ℕ → K} {h : ℕ}
    (hw : WalkSat cur chld' fo ln count acc α seed initial_count h)
    (hkh : k ≤ h) :
    accInGate cur chld' fo α initial_count kMem k = acc k := by
  rw [accInGate_of_ge_kMem _ _ _ _ _ hk, acc_telescope hw k hk1 hkh, hseed]

def failingStatement : String :=
  "physical acc column cannot be both WalkSat.acc (hosted walkAccInit / forestSeedSource) and accInGate (in-gate MixedExpr); they differ on root rows"

theorem failingStatement_name :
    failingStatement =
      "physical acc column cannot be both WalkSat.acc (hosted walkAccInit / forestSeedSource) and accInGate (in-gate MixedExpr); they differ on root rows" :=
  rfl

/-- Same 7 names as `Batch448.openConjunctsAfterVer`. -/
def openAfterWiringStop : List String :=
  ["mem_first_counts", "mem_first_indicator",
    "computeTopology", "memoryTopology", "axisStructural",
    "rootBoundary", "structuralChecks"]

theorem openAfterWiringStop_length : openAfterWiringStop.length = 7 := by
  decide

theorem computeTopology_still_open :
    "computeTopology" ∈ openAfterWiringStop := by
  decide

theorem memoryTopology_still_open :
    "memoryTopology" ∈ openAfterWiringStop := by
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

def remainingMove2 : String :=
  Batch498.remainingMove2

theorem remainingMove2_eq : remainingMove2 = Batch498.remainingMove2 := rfl

end Nock.RedTeam.Batch499

#print axioms Nock.RedTeam.Batch499.accInGate_eq_walkSat_of_ge
#print axioms Nock.RedTeam.Batch499.openAfterWiringStop_length
