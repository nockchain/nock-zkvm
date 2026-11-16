/-
  Nock/RedTeam/Batch409Thm54SeedBoundaryKside.lean

  K-side `memSeedBoundaryExprs` is first-row `.boundary` zero
  (`Nock/AIR.lean::memSeedBoundary_sound`, `tc 8` / `tc 7`).

  `deployed_root_accumulators_zero` reads the two
  new gates at `memoryChipAt c`.
-/
import Nock.AIR
import Nock.WalkPrefix
import Nock.Walk
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.RedTeam.Batch408Thm54SeedBoundaryGates
import Nock.RedTeam.Batch395Thm54SeedBoundaryDeployed
import Nock.NockVMROM.Thm54.P8Core.Batch409Thm54SeedBoundaryKside
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch409

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Reified.Trans
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.RedTeam.Batch408
open Nock.RedTeam.Batch395

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- K-side seed boundary is first-row `axis_counts` / `axis_indicator` (`tc 8` / `tc 7`).
    This is a walk-root `.boundary`, not Algorithm `read_root`. -/
theorem kside_seed_is_first_row_zero
    (minp : MemoryTable.Inputs K) (mop : MemoryTable.MState → K)
    (mrow : MemoryTable.Pub K) (mg : K) :
    (∀ e ∈ memSeedBoundaryExprs, e.eval (memoryEnvFull minp mop mrow mg) = 0) ↔
      (mrow.pt.counts = 0 ∧ mrow.pt.indicator = 0) :=
  memSeedBoundary_sound minp mop mrow mg

/-- Proposed pair (receipt-only, DECLINED) at a `read_root` selector is the same
    zero condition on source roles `4` / `3`.  **Not** a deployed-chip theorem. -/
theorem proposed_at_read_root (eK : Env K) (eF : Env F)
    (hsel : algebraMap F K (eF.trace 2) = 1) :
    (proposedSeedCountsGate (F := F)).eval eK eF = 0 ∧
      (proposedSeedIndicatorGate (F := F)).eval eK eF = 0 ↔
        (eK.trace 4 = 0 ∧ eK.trace 3 = 0) := by
  rw [proposed_seed_gates_vanish_iff]
  constructor
  · intro h
    exact h.resolve_left (by simp [hsel])
  · exact Or.inr

theorem axis_roles : axisAccumRoles = [3, 4] := rfl

/-- The first-row-mask instrument still sees no first-row zero pin of roles
    `3`/`4` (the authorized pin uses physical column `153`, not column `4`). -/
theorem deployed_still_has_no_first_row_zero_pin :
    (paperKGates (K := ℚ) (F := ℚ)).all
      (fun g => !isFirstRowAxisSeedPin g || readsSeedPublic g) = true :=
  no_committed_zero_pin

def kside_is_not_paper_read_root : String :=
  "memSeedBoundaryExprs is first-row .boundary zero (AIR); paper :2065-2070 is P = L - ts at read_root; halt-zero is :2061-2063; authorized pin is rootMask on 1..kMem"

/-- Deployed walk: `rootRowMask` at the package `kMem` is `1` on the BFS
    prefix `i < kMem` and `0` afterwards. -/
theorem rootMask_sound_for_every_k
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (rootRowMask P.optimized.memoryNodes
      P.optimized.family.problem.cfg.kMem).eval
        (P.optimized.memoryNodes i) =
      if (i : ℕ) < P.optimized.family.problem.cfg.kMem then 1 else 0 :=
  rootRowMask_eval P.optimized.memoryNodes
    P.optimized.family.problem.cfg.kMem
    P.optimized.memoryNodes_injective i

section DeployedZero

variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
  (i : Fin P.optimized.family.problem.cfg.memRows)
  (hi : (i : ℕ) < P.optimized.family.problem.cfg.kMem)

include hsat hi

end DeployedZero

/-- `mem_first_counts` / `mem_first_indicator` leave `Batch448.openConjunctsAfterVer`
    (still 7 names).  First-row zero is the `kMem ≥ 1` instance of
    `deployed_root_accumulators_zero`; the AcceptedContent fields are not
    retyped here. -/
def openConjunctsAfterVerStill : List String :=
  ["mem_first_counts", "mem_first_indicator"]

/-- Receipt 1 of the nineteenth move ("accepted at the OLD `k = 1` chip") is
    **uncompiled**.  The old-chip object is gone (`P.memoryChip` now takes
    `cfg.kMem`); do not claim a Satisfies proof that was never written.
    The new-chip rejection half is `deployed_root_accumulators_zero`. -/
def receipt_one_old_chip_acceptance_uncompiled : String :=
  "Batch407Generic.countsAttack accepted-at-old-chip: uncompiled (object deleted)"

end Nock.RedTeam.Batch409

#print axioms Nock.RedTeam.Batch409.kside_seed_is_first_row_zero
#print axioms Nock.RedTeam.Batch409.rootMask_sound_for_every_k
#print axioms Nock.RedTeam.Batch409.deployed_root_accumulators_zero
#print axioms Nock.RedTeam.Batch409.deployed_still_has_no_first_row_zero_pin
