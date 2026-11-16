/-
  Nock/RedTeam/Batch907Thm54R4HonestPremises.lean

  At `c = P.honestTuple` with the honest traces `QcH` / `QmH`, from `HonestFill P`:

  * `hio_honest`   : `FamilyIOGood`, by `hostileRecordsAt P c QmH QcH = P.hostileRecords..` (the
    family request list equals the package's at the honest tuple: the typed row environments
    coincide because the challenge map and the public map do, `hchalC` and the seed wiring) and
    `canonical_coins_not_hostile_failure` (`ioGood10`);
  * `hb_honest`    : `CertBitsBoolean`, from acceptance;
  * `h1_honest`    : `coord b 1 0 ≠ 0`, from `FormRBasis`.

  The row bound `hrb` is NOT derived here: no package field states it (the config's
  `compRows ≤ 2^cfg.orbit.h` is on the `K`-orbit `OrbitDomain`, the package's `orbit` is a
  `StrictOrbitDomain F 3 hOrb`, and nothing in the package ties `cfg.orbit.h` to `hOrb`).
-/
import Nock.RedTeam.Batch906Thm54R4HonestFamily
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch907

open scoped Polynomial
open Polynomial
open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.RedTeam.Batch906

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  {P : OptimizedFullStrictNockVMROMPackage F K hOrb}

/-- The family public map at the honest tuple is the package map. -/
theorem familyComputePublic_honest (H : HonestFill P) :
    P.familyComputePublic P.honestTuple = P.optimized.computePublic :=
  DeployedChipFamily.computePublicOfTuple_eq_pkg_of_seed
    P.optimized.basis P.optimized.verifier.raw.claim P.optimized.family
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computePublic
    P.honestTuple P.optimized.computePublicPins rfl
    (P.computeWalkSeed_eq_seedOfClaim_honest H.hst H.hs H.hf H.he).symm

/-- **The family row environment at the honest tuple is the package's row environment at the
canonical trace.** -/
theorem rowEnvAt_honest (H : HonestFill P) (a : Fin P.optimized.family.problem.cfg.compRows) :
    rowEnvAt P P.honestTuple (QcH P) a =
      gatherCorrectedFinalTypedEnv P.optimized.basis
        (P.computeBaseEnv (canonicalComputeTrace P) a) := by
  unfold rowEnvAt
  rw [H.hchalC, familyComputePublic_honest H]
  congr 1

/-- **The family request list at the honest tuple is the package's** at the canonical trace. -/
theorem hostileRequestsAt_honest (H : HonestFill P) :
    hostileRequestsAt P P.honestTuple (QcH P) = P.hostileRequests (canonicalComputeTrace P) := by
  unfold hostileRequestsAt OptimizedFullStrictNockVMROMPackage.hostileRequests
  refine congrArg List.flatten (congrArg List.ofFn (funext fun a => ?_))
  rw [rowEnvAt_honest H a]

/-- **The family records at the honest tuple are the package's** at the canonical traces. -/
theorem hostileRecordsAt_honest (H : HonestFill P) :
    hostileRecordsAt P P.honestTuple (QmH P) (QcH P) =
      P.hostileRecords (canonicalComputeTrace P) (canonicalMemoryTrace P) := by
  unfold hostileRecordsAt OptimizedFullStrictNockVMROMPackage.hostileRecords
  rw [hostileRequestsAt_honest H, hostileResponsesAt_eq_package, honestQm_QmH]

/-- **`hio` at the honest instance**: `FamilyIOGood`, from the package's sampled-coin goodness
`ioGood10` at the honest records. -/
theorem hio_honest (H : HonestFill P) : FamilyIOGood P P.honestTuple (QcH P) (QmH P) := by
  unfold FamilyIOGood
  rw [hostileRecordsAt_honest H]
  exact OptimizedCanonicalHostileLists.canonical_coins_not_hostile_failure P H.hax H.hwidth

/-- **`hb` at the honest instance**, from acceptance at the current gates. -/
theorem hb_honest (H : HonestFill P) : Batch823.CertBitsBoolean P P.honestTuple (QcH P) :=
  Batch823.certBitsBoolean_of_sat P P.honestTuple (QcH P)
    (deployedAcceptance_honest H).compute_satisfies

/-- **`h1` at the honest instance**, from `FormRBasis`. -/
theorem h1_honest (H : HonestFill P) :
    coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0 :=
  Batch824.coord_one_ne_zero_of_formRBasis P H.hbasis

end

end Nock.RedTeam.Batch907

#print axioms Nock.RedTeam.Batch907.rowEnvAt_honest
#print axioms Nock.RedTeam.Batch907.hio_honest
#print axioms Nock.RedTeam.Batch907.hb_honest
#print axioms Nock.RedTeam.Batch907.h1_honest
