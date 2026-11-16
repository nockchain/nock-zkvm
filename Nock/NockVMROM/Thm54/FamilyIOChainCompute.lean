/-
  Nock/NockVMROM/Thm54/FamilyIOChainCompute.lean

  Each twin has the conclusion of its package-chip original, with the package chip's
  challenge/public maps replaced by the tuple's (`computeChalValOfTuple c`,
  `familyComputePublic c`).  The timestamp base is the coin `alphaM c.1` and the NPR seed is
  `nprSeed c.1`, both by definition (`computeKOfTuple c 0`, `… 1`); no pin, no `same_problem`.

  Paper: the paper (request accumulator), `:1852-1887` (timestamps, `ln`),
  `:603-613`, `:1441` (unique requests).
-/
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.P8Core.FamilyIOChainCompute
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.FamilyIOChain

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedStrictPackage
open OptimizedStrictFullPackage
open OptimizedComputeBaseGates
open OptimizedComputeFinal
open OptimizedComputeCorrectedFinal
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeSemanticRealization
open OptimizedComputeFiniteIOGates
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open DeployedChipFamily
open FamilyComputeRows
open Module

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)

/-! ## A. Widths and challenge slots of the family compute chip -/

variable (Qc : Fin (P.computeChipAt c).rap.w → F[X])

theorem zZinv_at_rowEnvAt' (i : Fin (rows P)) (hz : nprSeed c.1 ≠ 0) :
    (zZinvExpr.subst computeSubst).eval (rowEnvAt P c Qc i).toSourceEnv = 0 :=
  zZinv_at_rowEnvAt P c Qc i hz

/-! ## B. What every accepted family trace commits, row by row (twin of §B) -/

section Rows

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

/-! ### Telescoping (twin of §C) -/

/-! ### The denominator pins (twin of §D) -/

/-! ### Boolean masks (twin of §E) -/

end Rows

/-! ## C. The request list read off a family trace (twin of §F) -/

/-- Twin of `hostile_requests_eq_sum_over_records`: the public `requests` is the LogUp sum of the
records read off the family trace, at the tuple's own IO coins. -/
theorem hostile_requests_eq_sum_over_records_at
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hpole : ∀ (i : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnvAt P c Qc i) j = 1 → slotDenominator (rowEnvAt P c Qc i) j ≠ 0) :
    (rowEnvAt P c Qc (lastRow P)).extensionPublic 2 =
      ((hostileRequestsAt P c Qc).map fun r => (FiniteIO.compress (chipCoinsAt c) r)⁻¹).sum := by
  rw [hostile_requests_eq_sum_logUp_at P c Qc hsat
    (fun i j => activeMask_bool_at P c Qc hsat hchar i j) hpole, hostileRequestsAt,
    List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [logUpRowTerm_eq_rowRequests_at P c Qc i (fun j => activeMask_bool_at P c Qc hsat hchar i j)]
  rfl

/-! ## D. Exponent bookkeeping at the family chip (twin of `OptimizedHostileTimestamps` §D) -/

section Deployed

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

end Deployed

/-! ## E. `Nodup` of the family request list (twin of `OptimizedHostileTimestamps` §F) -/

section Nodup

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
  (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
  (hz0 : nprSeed c.1 ≠ 0)
  (hα : alphaM c.1 ∉ TimestampCollisionEvent (totalRequestsAt P c Qc))
include hsat hchar hz0 hα

end Nodup

end

end Nock.NockVMROM.Thm54.FamilyIOChain
