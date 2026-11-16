/-
  Nock/NockVMROM/Thm54/FamilyIOChainRouteB.lean

  Family-chip twins of:
  * `hz0` (`OptimizedHostileTimestamps.nprSeed_ne_of_good`) at family-width traces;
  * `optimizedFullStrict_hostile_LIO` / `hostile_LIO_of_good`, exclusions from
    `optimizedFailureEvent_good_components` (never the capstone statement `S`);
  * `MemoryInternalPole.optimizedFullStrict_paired_records` (the `intermediate` LogUp);
  * `Batch672`: the compute carrier `S` (`expCol_eq_prefixExp`, `compute_slot9_eq_expOf`),
    `memory_row_bound`, `natLift_reqIdx`, `ts_eq_alpha_pow_natLift`, `natLift_reqIdx_window`,
    `verify_row_inherits`;
  * `Batch742`'s route-B exclusions: `row_record_is_request`, `ver_reqIdx_injective`,
    `request_named_by_row`;
  * the hrows (a′) window wrappers (`scratchpad/hrows-wrappers/HrowsWrappers.lean`) with
    `hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K`
    explicit (the future `rowsBound` field's type).

  `hostile_LIO'_at` itself takes the three IO events explicitly, exactly as `hostile_LIO'`.

  No `S`, no `same_problem`,
  no `p8`, no `OptimizedSameProblemAt` (receipt: `Batch786`).
-/
import Nock.NockVMROM.Thm54.FamilyIOChainMemory
import Nock.NockVMROM.Thm54.MemoryInternalPole
import Nock.NockVMROM.Thm54.OptimizedHostileConfiguration
import Nock.NockVMROM.Thm54.P8Core.FamilyIOChainRouteB
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
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open OptimizedStrictPackage
open OptimizedStrictFullPackage
open OptimizedComputeCorrectedFinal
open OptimizedComputeSemanticRealization
open OptimizedComputeSubstitution
open StrictExtension
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open OptimizedMemoryHostileAccumulator (memRowTerm rowResponseTerms rowResponses
  chainMixed_mem)
open MemoryInternalPole (chipInterCoins rowDelta AggregatorAt aggregatorAt_of_paperAggregator
  delta_eq_signed_inv rowReadsOf rowVerifiesOf rowReadsOf_length_le rowVerifiesOf_length_le
  paperAggregator_mem req_denom_ne_of_not_hit resp_denom_ne_of_not_hit)
open DeployedChipFamily
open FamilyComputeRows
open FamilyMemoryRows
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
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

/-! ## A. -/

/-! ## B. The twin of `hz0`, and the named family IO premise -/

/-! ## C. The compute carrier `S` at the family chip (twin of `Batch672` §A) -/

section Carrier

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

end Carrier

/-! ## D. The memory `intermediate` LogUp at the family chip (twin of `MemoryInternalPole`) -/

section Paired

variable (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)

end Paired

/-! ## E. Route B and the exponent binding at the family chip (twins of `Batch742`, `Batch672`) -/

section Binding

end Binding

/-! ## F. The hrows (a′) window wrappers at the family chips

`hrb` is the future package field `rowsBound`'s type, explicit.  Window
`Ksz := max (3 * P.objects.cfg.compRows) P.objects.cfg.memRows` (inlined, no new def). -/

section Hrows

theorem hostile_LIO_of_rowsBound_at (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K :=
      P.rowsBound) :
    IO.LIO (max (3 * P.objects.cfg.compRows) P.objects.cfg.memRows)
      (hostileRequestsAt P c Qc) (hostileResponsesAt P c Qm) :=
  hostile_LIO_of_good_at P c Qc Qm hacc hgood hio
    (OptimizedHostileConfiguration.hchar_of_package P) (hKp_of_rowsBound_at P hrb)
    (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm)

/-- Same through the core `hostile_LIO'_at`, every event explicit. -/
theorem hostile_LIO'_of_rowsBound_at (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hz0 : nprSeed c.1 ≠ 0)
    (hts : alphaM c.1 ∉ TimestampCollisionEvent (hostileRequestsAt P c Qc).length)
    (hpole : c.2.1.2 ∉ FiniteIO.IOPoleHitEvent (hostileRecordsAt P c Qm Qc) c.2.1.1)
    (hrlc : c.2.1.1 ∉ FiniteIO.IORLCCollisionEvent (hostileRecordsAt P c Qm Qc))
    (hlog : c.2.1.2 ∉ FiniteIO.IOLogDerivEvent (hostileRecordsAt P c Qm Qc) c.2.1.1)
    (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K :=
      P.rowsBound) :
    IO.LIO (max (3 * P.objects.cfg.compRows) P.objects.cfg.memRows)
      (hostileRequestsAt P c Qc) (hostileResponsesAt P c Qm) :=
  hostile_LIO'_at P c Qm Qc hacc (OptimizedHostileConfiguration.hchar_of_package P) hz0 hts
    (hKp_of_rowsBound_at P hrb) (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm)
    hpole hrlc hlog

/-- The IO exclusion is component 2 of the event
(`FamilyEnvCore.familyIOGood_of_not_mem`); nothing else is assumed beyond `hchar` and the window
premises. -/
theorem optimizedFullStrict_hostile_LIO_at {Ksz : ℕ}
    (Qc0 : Fin P.computeChip.rap.w → F[X]) (Qm0 : Fin P.memoryChip.rap.w → F[X])
    (hacc : P.OptimizedProductionAcceptanceAt Qc0 Qm0 c)
    (hgood : c ∉ P.optimizedFailureEvent Qc0 Qm0)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c (P.familyQc c Qc0)).length)
    (hKresp : (hostileResponsesAt P c (P.familyQm c Qm0)).length ≤ Ksz) :
    IO.LIO Ksz (hostileRequestsAt P c (P.familyQc c Qc0))
      (hostileResponsesAt P c (P.familyQm c Qm0)) := by
  have hio : FamilyIOGood P c (P.familyQc c Qc0) (P.familyQm c Qm0) :=
    FamilyEnvCore.familyIOGood_of_not_mem P.optimized Qc0 Qm0 c
      (P.optimizedFailureEvent_good_components Qc0 Qm0 c hgood).2.1
  have hgood' : c ∉ P.optimizedFailureEvent (honestQc P c (P.familyQc c Qc0))
      (honestQm P c (P.familyQm c Qm0)) := by
    rw [show honestQc P c (P.familyQc c Qc0) = Qc0 from
        FamilyEnvCore.honestQc_familyQc P.optimized c Qc0,
      show honestQm P c (P.familyQm c Qm0) = Qm0 from
        FamilyEnvCore.honestQm_familyQm P.optimized c Qm0]
    exact hgood
  exact hostile_LIO_of_good_at P c (P.familyQc c Qc0) (P.familyQm c Qm0)
    (DeployedAcceptanceAt.of_acceptance hacc) hgood' hio hchar hKp hKreq hKresp

/-- The same at the hostile window `max (3·compRows) memRows`, with every range premise
discharged (`hKp` from the package field `rowsBound`). -/
theorem optimizedFullStrict_hostile_LIO_at_window
    (Qc0 : Fin P.computeChip.rap.w → F[X]) (Qm0 : Fin P.memoryChip.rap.w → F[X])
    (hacc : P.OptimizedProductionAcceptanceAt Qc0 Qm0 c)
    (hgood : c ∉ P.optimizedFailureEvent Qc0 Qm0) :
    IO.LIO (max (3 * P.objects.cfg.compRows) P.objects.cfg.memRows)
      (hostileRequestsAt P c (P.familyQc c Qc0)) (hostileResponsesAt P c (P.familyQm c Qm0)) :=
  optimizedFullStrict_hostile_LIO_at P c Qc0 Qm0 hacc hgood
    (OptimizedHostileConfiguration.hchar_of_package P) (hKp_of_rowsBound_at P)
    (hKreq_of_rowsBound_at P c _) (hKresp_of_rowsBound_at P c _)

end Hrows

end

end Nock.NockVMROM.Thm54.FamilyIOChain

#print axioms Nock.NockVMROM.Thm54.FamilyIOChain.optimizedFullStrict_hostile_LIO_at
#print axioms Nock.NockVMROM.Thm54.FamilyIOChain.optimizedFullStrict_hostile_LIO_at_window
