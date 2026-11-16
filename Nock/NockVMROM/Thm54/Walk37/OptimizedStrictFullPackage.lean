import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackageDefs
import Nock.NockVMROM.Thm54.P8Core.PlacementAEvOnly
import Nock.NockVMROM.Thm54.P8Core.PlacementABridge
import Nock.NockVMROM.Thm54.P8Core.PartATarget309

/-!
# Full optimized strict package: the statement and its consequences

The structure `OptimizedFullStrictThm54Statement`, the capstone theorem `optimizedFullStrictNockVMROM_of_package`
that inhabits it, and the supporting results: the same-problem and genuine-target predicates, the
consumed failure event and its cardinality and probability bounds (with the α-collision summand and
the IO summand priced at the committed records), the bit forms of those bounds, and the
fifteen-summand and staged false-acceptance bounds at the parallel package.
-/

open Nock Nock.NockVMROM Nock.NockVMROM.Thm54
namespace Nock.Walk37

namespace Nock.NockVMROM.Thm54
namespace OptimizedStrictFullPackage

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open MonolithicRAP
open RawSemanticAssembly SemanticStrategy StrictCommitment
open TemplateRawJointSoundness ServedLookupBridge
open ProductionP8Containment
open ProductionAxisStructureVerifier TemplateAxisCounting
open OptimizedComputeCorrectedFinal
open OptimizedComputeFinalTrace
open OptimizedComputeSampledTrace
open OptimizedComputeSemanticRealization
open OptimizedComputeCollisionBound
open OptimizedComputeSubstitution
open OptimizedMemoryRAP
open OptimizedMemoryGateBasis
open OptimizedMemoryCanonicalTrace
open OptimizedMemoryCanonicalSatisfaction
open OptimizedMemoryCollisionAccounting
open OptimizedStrictPackage
open SharedTableWalkRow

noncomputable section

namespace OptimizedFullStrictNockVMROMPackage

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The whole raw-problem equality binds the package cfg/exec; the cfg equality and dependent execution
`HEq` bind the exact optimized family, whose additional proof fields are not part of `RawProblem`. -/
structure OptimizedSameProblemAt (j : JointCoins K) (lmb : K) : Prop where
  nprSeed_ne : nprSeed j ≠ 0
  specialized_eq_objects :
    specializedProblem P.optimized.verifier.raw.timestamp
        (nprSeed j) nprSeed_ne (alphaM j) lmb =
      { cfg := P.objects.cfg, exec := P.objects.exec }
  specialized_cfg_eq_family :
    (specializedProblem P.optimized.verifier.raw.timestamp
      (nprSeed j) nprSeed_ne (alphaM j) lmb).cfg =
      P.optimized.family.problem.cfg
  specialized_exec_heq_family :
    HEq
      (specializedProblem P.optimized.verifier.raw.timestamp
        (nprSeed j) nprSeed_ne (alphaM j) lmb).exec
      P.optimized.family.problem.exec

/-- The mandatory problem link pins the sampled `λ` to the objects' `λ`, exactly as it pins
`alphaM` to the objects' `α` (`specializedProblem_tableLam`). -/
theorem OptimizedSameProblemAt.lam_eq {j : JointCoins K} {lmb : K}
    (h : P.OptimizedSameProblemAt j lmb) : lmb = P.objects.cfg.challenges.lam :=
  congrArg (fun Q : RawProblem F K => Q.cfg.challenges.lam) h.specialized_eq_objects

/-- A package-object equality supplies the optimized-family equality through the same dependent
family link. -/
theorem OptimizedSameProblemAt.of_objects
    (j : JointCoins K) (lmb : K) (hz : nprSeed j ≠ 0)
    (hobjects :
      specializedProblem P.optimized.verifier.raw.timestamp
          (nprSeed j) hz (alphaM j) lmb =
        { cfg := P.objects.cfg, exec := P.objects.exec }) :
    P.OptimizedSameProblemAt j lmb :=
  { nprSeed_ne := hz
    specialized_eq_objects := hobjects
    specialized_cfg_eq_family :=
      (congrArg RawProblem.cfg hobjects).trans P.optimized.family_cfg.symm
    specialized_exec_heq_family := by
      have hsigma :
          (⟨(specializedProblem P.optimized.verifier.raw.timestamp
              (nprSeed j) hz (alphaM j) lmb).cfg,
            (specializedProblem P.optimized.verifier.raw.timestamp
              (nprSeed j) hz (alphaM j) lmb).exec⟩ :
              Σ cfg : ExactConfig F K, ExactExecution cfg) =
            ⟨P.objects.cfg, P.objects.exec⟩ :=
        congrArg
          (fun Q : RawProblem F K =>
            (⟨Q.cfg, Q.exec⟩ : Σ cfg : ExactConfig F K, ExactExecution cfg))
          hobjects
      exact (Sigma.mk.inj_iff.mp hsigma).2.trans P.optimized.family_exec.symm }

/-- `DeployedAcceptanceAt` is a definitional alias. -/
structure OptimizedProductionAcceptanceAt
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : Prop where
  compute_satisfies :
    RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (P.familyQc c Qc)
  memory_satisfies :
    RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (P.familyQm c Qm)

def consumedFailureEvent
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  OptimizedFailureEventEv.p8SlotEv P Qc Qm ∪
    P.famIOEventOf Qc Qm ∪
    liftTimestampFailure
      (OptimizedHostileTimestamps.TimestampCollisionEvent (P.hostileRequests Qc).length) ∪
    liftInterPoleFailure
      (interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm)) ∪
    liftP8Failure (P.computeWalkRootEvent Qc) ∪
    liftP8Failure (P.computeTilingEventOf Qc) ∪
    liftP8Failure (P.memoryTilingEventOf Qm) ∪
    liftP8Failure (P.computePrefixGammaEventOf Qc) ∪
    liftP8Failure (P.memoryPrefixGammaEventOf Qm) ∪
    liftP8Failure (P.memoryForestAlphaEventOf Qm) ∪
    P.decodedLambdaEventOf Qc Qm ∪
    liftP8Failure (OptimizedFailureEventEv.reqPairEv P Qc Qm) ∪
    liftP8Failure (OptimizedFailureEventEv.rootResultEv P Qc Qm) ∪
    liftP8Failure (OptimizedFailureEventEv.alphaZeroEvent : Finset (JointCoins K))

theorem consumedFailureEvent_eq_ev
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    P.consumedFailureEvent Qc Qm = OptimizedFailureEventEv.optimizedFailureEventEv P Qc Qm := rfl

theorem consumedFailureEvent_card_le
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.consumedFailureEvent Qc Qm).card ≤
      optimizedHostileProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (OptimizedFailureEventEv.workloadEv P P.optimized.Λ) P.hostileIOWork
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows :=
  OptimizedFailureEventEv.optimizedFailureEventEv_card_le P Qc Qm

/-- The target that the claim "models a NockVM instance": the claim holds under Nock's semantics,
together with the committed-trace facts that give it.  It does not contain `same_problem` or
`sampled_io_event_good`, and no `𝕂`-side `GenuineTargetAt` is stated at the built strategy. -/
structure OptimizedProductionGenuineTargetAt
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : Prop where
  sampled_io :
    IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs
  hostile_io_event_good :
    c.2.1 ∉ FiniteIO.IOFailureEvent (P.hostileRecordsAt c (P.familyQm c Qm) (P.familyQc c Qc))
  timestamp_collision_good :
    alphaM c.1 ∉ OptimizedHostileTimestamps.TimestampCollisionEvent
      (P.hostileRequestsAt c (P.familyQc c Qc)).length
  compute_source :
    ∀ i,
      CorrectedComputeSourceObligations P.optimized.family.problem.cfg.compRows
        (FamilyEnvCore.rowEnvAt P.optimized c (P.familyQc c Qc) i)
        (envOfTrace (P.familyQc c Qc) P.optimized.orbit.ω (P.optimized.computeNodes i)
          (DeployedChipFamily.computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c))
  compute :
    ∀ (i : Fin P.optimized.family.problem.cfg.compRows),
      (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows →
      CorrectedDecodedTransitionSources (FamilyEnvCore.rowEnvAt P.optimized c (P.familyQc c Qc) i)
  memory :
    ∀ i,
      (∀ g ∈ baseTransitionGates P.optimized.basis,
        g.eval (P.memEnvF c (P.familyQm c Qm) i) = 0) ∧
      (∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
        g.eval (P.memEnvK c (P.familyQm c Qm) i) (P.memEnvF c (P.familyQm c Qm) i) = 0)
  aggregate_forest_axis : P.optimized.OptimizedSharedMemoryConnective
  p8 :
    ∃ fuel, Nock.evalN fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result

/-- Slot `6` is the package's sampled internal pole (`memoryCoordinatePins.sampledInterPole`). -/
theorem packageInterPole_eq_sampled :
    P.packageInterPole = P.optimized.sampled.interPole :=
  P.optimized.memoryCoordinatePins.sampledInterPole

theorem memory_source_gate_facts
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedProductionAcceptanceAt Qc Qm c) :
    ∀ i,
      (∀ g ∈ baseTransitionGates P.optimized.basis,
        g.eval (P.memEnvF c (P.familyQm c Qm) i) = 0) ∧
      (∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
        g.eval (P.memEnvK c (P.familyQm c Qm) i) (P.memEnvF c (P.familyQm c Qm) i) = 0) :=
  fun i => FamilyEnvCore.memory_row_parts_at P.optimized c (P.familyQm c Qm)
    hacc.memory_satisfies i

/-- The gate conjuncts come from the two family satisfaction facts; the IO
and timestamp exclusions are components 1 and 2 of the consumed event (`PlacementA.good_components_of_Ev`);
`p8` is `PlacementA.holds_of_acceptance_evOnly` at the family traces, with the package's `generated`
and `primeField` fields and `of_package`'s Form R hypotheses. -/
theorem acceptance_outside_failure_implies_target
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedProductionAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.consumedFailureEvent Qc Qm) :
    P.OptimizedProductionGenuineTargetAt Qc Qm c := by
  have hgood' : c ∉ OptimizedFailureEventEv.optimizedFailureEventEv P Qc Qm := by
    rw [← P.consumedFailureEvent_eq_ev]; exact hgood
  have hc := PlacementA.good_components_of_Ev P Qc Qm c hgood'
  have hio : c.2.1 ∉ FiniteIO.IOFailureEvent
      (P.hostileRecordsAt c (P.familyQm c Qm) (P.familyQc c Qc)) :=
    FamilyEnvCore.familyIOGood_of_not_mem P.optimized Qc Qm c hc.2.1
  have hts : alphaM c.1 ∉ OptimizedHostileTimestamps.TimestampCollisionEvent
      (P.hostileRequestsAt c (P.familyQc c Qc)).length := by
    have h := hc.2.2.1
    have hlen := FamilyEnvCore.hostileRequestsAt_length_eq P.optimized c Qc
    rw [show (P.hostileRequestsAt c (P.familyQc c Qc)).length = (P.hostileRequests Qc).length
      from hlen]
    exact h
  have hw0 : P.computeChip.rap.w = 303 := P.optimized.exact_chip_resources.1
  have hacc' : DeployedAcceptanceAt P c (P.familyQc c Qc) (P.familyQm c Qm) :=
    ⟨hacc.compute_satisfies, hacc.memory_satisfies⟩
  have hgoodEv : c ∉ OptimizedFailureEventEv.optimizedFailureEventEv P
      (FamilyComputeRows.honestQc P c (P.familyQc c Qc))
      (FamilyMemoryRows.honestQm P c (P.familyQm c Qm)) := by
    rw [show FamilyComputeRows.honestQc P c (P.familyQc c Qc) = Qc from
          FamilyEnvCore.honestQc_familyQc P.optimized c Qc,
        show FamilyMemoryRows.honestQm P c (P.familyQm c Qm) = Qm from
          FamilyEnvCore.honestQm_familyQm P.optimized c Qm]
    exact hgood'
  obtain ⟨gfuel, G, R, fuel, r, hgen, hG, hΛG⟩ := P.generated
  exact
    { sampled_io := P.shared_io
      hostile_io_event_good := hio
      timestamp_collision_good := hts
      compute_source := fun i =>
        FamilyEnvCore.row_obligations_at P.optimized c (P.familyQc c Qc) hacc.compute_satisfies i
      compute := fun i hi =>
        corrected_conditional_transition_soundness
          (FamilyEnvCore.row_obligations_at P.optimized c (P.familyQc c Qc)
            hacc.compute_satisfies i)
          (FamilyEnvCore.notLast_at P.optimized c hw0 (P.familyQc c Qc)
            hacc.compute_satisfies i hi)
      memory := P.memory_source_gate_facts Qc Qm c hacc
      aggregate_forest_axis := P.optimized.shared_memory_connective
      p8 := ⟨fuel, (PlacementA.holds_of_acceptance_evOnly P c (P.familyQc c Qc) (P.familyQm c Qm)
        hacc' hgoodEv hax hbasis hwidth hgen hG hΛG P.primeField).2⟩ }

def OptimizedFalseAcceptanceSet
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter fun c =>
    P.OptimizedProductionAcceptanceAt Qc Qm c ∧
      ¬ P.OptimizedProductionGenuineTargetAt Qc Qm c

theorem optimizedFalseAcceptanceSet_subset_failure
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    P.OptimizedFalseAcceptanceSet Qc Qm ⊆ P.consumedFailureEvent Qc Qm := by
  intro c hc
  simp only [OptimizedFalseAcceptanceSet, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  by_contra hgood
  exact hc.2 (P.acceptance_outside_failure_implies_target hax hbasis hwidth Qc Qm c hc.1 hgood)

/-! ### The consumed bound

The statement shape of `complete_false_acceptance_bound` is
`Bound |𝕂| |𝔽| p8Work ioWork compRows memRows`, with the bound function carrying the α-collision
summand and `ioWork = ioFailureUnionBound 8 (3·compRows) memRows |𝕂|`. -/

theorem optimizedFalseAcceptance_card_le_records
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.OptimizedFalseAcceptanceSet Qc Qm).card ≤
      optimizedHostileProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (OptimizedFailureEventEv.workloadEv P P.optimized.Λ)
        P.hostileIOWork
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows :=
  (Finset.card_le_card (P.optimizedFalseAcceptanceSet_subset_failure hax hbasis hwidth Qc Qm)).trans
    (P.consumedFailureEvent_card_le Qc Qm)

/-- The IO summand is priced at the records the traces commit to (`|requests| ≤ 3·compRows`,
`|responses| ≤ memRows`, for every trace), and the α-collision summand is `|𝕂|⁸·(1 + 3N(3N−1)/2)`.
The base-field lifts of both chips are not part of the union. -/
theorem optimizedFalseAcceptance_card_le
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.OptimizedFalseAcceptanceSet Qc Qm).card ≤
      optimizedHostileProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (OptimizedFailureEventEv.workloadEv P P.optimized.Λ)
        P.hostileIOWork
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows :=
  P.optimizedFalseAcceptance_card_le_records hax hbasis hwidth Qc Qm

theorem optimizedFalseAcceptance_card_le_trimmed
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.OptimizedFalseAcceptanceSet Qc Qm).card ≤
      optimizedTrimmedProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (OptimizedFailureEventEv.workloadEv P P.optimized.Λ +
          OptimizedHostileTimestamps.timestampCollisionBound
            (3 * P.optimized.family.problem.cfg.compRows) +
          pricedWalkWork P.optimized.family.problem.cfg.compRows
            P.optimized.family.problem.cfg.memRows)
        (P.hostileIOWork + P.hostileInterWork)
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows := by
  simp only [hostileInterWork]
  rw [← optimizedHostileProductionFailureCardBound_eq_trimmed_shift]
  exact P.optimizedFalseAcceptance_card_le hax hbasis hwidth Qc Qm

theorem optimizedFalseAcceptance_card_le_extension
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.OptimizedFalseAcceptanceSet Qc Qm).card ≤
      optimizedTrimmedProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (OptimizedFailureEventEv.workloadEv P P.optimized.Λ +
          OptimizedHostileTimestamps.timestampCollisionBound
            (3 * P.optimized.family.problem.cfg.compRows) +
          pricedWalkWork P.optimized.family.problem.cfg.compRows
            P.optimized.family.problem.cfg.memRows)
        (P.hostileIOWork + P.hostileInterWork)
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows :=
  P.optimizedFalseAcceptance_card_le_trimmed hax hbasis hwidth Qc Qm

theorem optimizedFalseAcceptance_card_le_merged
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.OptimizedFalseAcceptanceSet Qc Qm).card ≤
      optimizedTrimmedProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (OptimizedFailureEventEv.workloadEv P P.optimized.Λ +
          OptimizedHostileTimestamps.timestampCollisionBound
            (3 * P.optimized.family.problem.cfg.compRows) +
          pricedWalkWork P.optimized.family.problem.cfg.compRows
            P.optimized.family.problem.cfg.memRows)
        (P.hostileIOWork + P.hostileInterWork)
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows :=
  P.optimizedFalseAcceptance_card_le_trimmed hax hbasis hwidth Qc Qm

theorem optimizedFalseAcceptance_card_le_legacy
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.OptimizedFalseAcceptanceSet Qc Qm).card ≤
      optimizedTrimmedProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (OptimizedFailureEventEv.workloadEv P P.optimized.Λ +
          OptimizedHostileTimestamps.timestampCollisionBound
            (3 * P.optimized.family.problem.cfg.compRows) +
          pricedWalkWork P.optimized.family.problem.cfg.compRows
            P.optimized.family.problem.cfg.memRows)
        (P.hostileIOWork + P.hostileInterWork)
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows :=
  P.optimizedFalseAcceptance_card_le_trimmed hax hbasis hwidth Qc Qm

/-- **The consumed false-acceptance probability.**
In full: `(p8Work + (1 + 3N(3N−1)/2))/|𝕂| + ioWork/|𝕂|²` with
`ioWork = ioFailureUnionBound 8 (3N) M |𝕂| = |𝕂|·(7(3N+M)² + 2(3N+M))`.
The remaining `1` inside `(1 + 3N(3N−1)/2)` is the α-collision event's
`0 ∈ TimestampCollisionEvent`, not a coin event.

The memory-fold lift `extensionMemoryCollisionEvent` and its `|𝕂|` coordinate are absent: no
committed gate reads slot 6, so a pin there would constrain nothing.  The
`normalized_hostile_card_bound_eq_separate_denominators` restatement over `|𝕂|⁶` gives the same
`/|𝕂|` normalisation for the remaining lifts.

**The bit figure.**  At `N = M = 2^31`, `p8Work ≤ 2^60`, `ioWork ≤ 16^65` the bound function is
`< 2^-123` (`GoldilocksParameters.hostile_soundness_at_paper_configuration`; the α-summand
`≈ 4.5·2^62/|𝕂| ≈ 2^-127.8` is below the `2^-124` IO term).  The `ioWork` ceiling is not met by
real executions (`RealProgramSoundness.not_ioWork_le_at_two_records_per_row`).  The ceiling-free
figure for real programs at the consumed bound is `122` bits at `2^31` rows and `120` at `2^32`
(`RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_31`, `…_two_pow_32`,
`…hostile_soundness_for_execution`): the quadratic `311S²` decides `b = 184 − 2r`. -/
theorem optimizedFalseAcceptance_probability_le
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    ((P.OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤
      optimizedHostileProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
        (OptimizedFailureEventEv.workloadEv P P.optimized.Λ)
        P.hostileIOWork
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows := by
  rw [card_optimizedProductionChallengeTuple]
  norm_num only [Nat.cast_pow]
  have hcast :
      ((P.OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) ≤
        optimizedHostileProductionFailureCardBound (Fintype.card K) (Fintype.card F)
          (OptimizedFailureEventEv.workloadEv P P.optimized.Λ)
          P.hostileIOWork
          P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows := by
    exact_mod_cast P.optimizedFalseAcceptance_card_le hax hbasis hwidth Qc Qm
  calc
    _ ≤ (optimizedHostileProductionFailureCardBound (Fintype.card K) (Fintype.card F)
          (OptimizedFailureEventEv.workloadEv P P.optimized.Λ)
          P.hostileIOWork
          P.optimized.family.problem.cfg.compRows
          P.optimized.family.problem.cfg.memRows : ℚ) /
        (Fintype.card K ^ 11) :=
      div_le_div_of_nonneg_right hcast (by positivity)
    _ = _ := normalized_hostile_card_bound_eq_separate_denominators _ _ _ _ _ _
      Fintype.card_pos

theorem optimizedFalseAcceptance_probability_le_trimmed
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    ((P.OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤
      optimizedTrimmedProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
        (OptimizedFailureEventEv.workloadEv P P.optimized.Λ +
          OptimizedHostileTimestamps.timestampCollisionBound
            (3 * P.optimized.family.problem.cfg.compRows) +
          pricedWalkWork P.optimized.family.problem.cfg.compRows
            P.optimized.family.problem.cfg.memRows)
        (P.hostileIOWork + P.hostileInterWork)
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows := by
  simp only [hostileInterWork]
  rw [← optimizedHostileProductionFailureProbabilityBound_eq_trimmed_shift]
  exact P.optimizedFalseAcceptance_probability_le hax hbasis hwidth Qc Qm

/-- The probability bound carrying a `20/|𝔽|` term, as a corollary with slack. -/
theorem optimizedFalseAcceptance_probability_le_extension
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    ((P.OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤
      optimizedExtensionProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
        (OptimizedFailureEventEv.workloadEv P P.optimized.Λ +
          OptimizedHostileTimestamps.timestampCollisionBound
            (3 * P.optimized.family.problem.cfg.compRows) +
          pricedWalkWork P.optimized.family.problem.cfg.compRows
            P.optimized.family.problem.cfg.memRows)
        (P.hostileIOWork + P.hostileInterWork)
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows :=
  (P.optimizedFalseAcceptance_probability_le_trimmed hax hbasis hwidth Qc Qm).trans
    (optimizedTrimmedProductionFailureProbabilityBound_le _ _ _ _ _ _)

/-- The probability bound carrying `19·M` plus `14·M/|𝔽|` terms, as a corollary with slack. -/
theorem optimizedFalseAcceptance_probability_le_merged
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    ((P.OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤
      optimizedMergedProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
        (OptimizedFailureEventEv.workloadEv P P.optimized.Λ +
          OptimizedHostileTimestamps.timestampCollisionBound
            (3 * P.optimized.family.problem.cfg.compRows) +
          pricedWalkWork P.optimized.family.problem.cfg.compRows
            P.optimized.family.problem.cfg.memRows)
        (P.hostileIOWork + P.hostileInterWork)
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows :=
  (P.optimizedFalseAcceptance_probability_le_extension hax hbasis hwidth Qc Qm).trans
    (optimizedExtensionProductionFailureProbabilityBound_le _ _ _ _ _ _)

theorem optimizedFalseAcceptance_probability_le_legacy
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    ((P.OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤
      optimizedProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
        (OptimizedFailureEventEv.workloadEv P P.optimized.Λ +
          OptimizedHostileTimestamps.timestampCollisionBound
            (3 * P.optimized.family.problem.cfg.compRows) +
          pricedWalkWork P.optimized.family.problem.cfg.compRows
            P.optimized.family.problem.cfg.memRows)
        (P.hostileIOWork + P.hostileInterWork)
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows :=
  (P.optimizedFalseAcceptance_probability_le_merged hax hbasis hwidth Qc Qm).trans
    (optimizedMergedProductionFailureProbabilityBound_le _ _ _ _ _ _ Fintype.card_pos)

theorem optimizedFalseAcceptance_probability_le_two_pow_neg
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (b : ℕ)
    (hsupport :
      optimizedHostileProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
          (OptimizedFailureEventEv.workloadEv P P.optimized.Λ)
          P.hostileIOWork
          P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows *
          2 ^ b ≤ 1) :
    ((P.OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤ 1 / 2 ^ b := by
  refine (P.optimizedFalseAcceptance_probability_le hax hbasis hwidth Qc Qm).trans ?_
  have hpow : (0 : ℚ) < 2 ^ b := by positivity
  apply (le_div_iff₀ hpow).2
  simpa [mul_comm] using hsupport

theorem optimizedFalseAcceptance_probability_le_two_pow_neg_trimmed
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (b : ℕ)
    (hsupport :
      optimizedTrimmedProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
          (OptimizedFailureEventEv.workloadEv P P.optimized.Λ +
            OptimizedHostileTimestamps.timestampCollisionBound
              (3 * P.optimized.family.problem.cfg.compRows) +
            pricedWalkWork P.optimized.family.problem.cfg.compRows
            P.optimized.family.problem.cfg.memRows)
          (P.hostileIOWork + P.hostileInterWork)
          P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows *
          2 ^ b ≤ 1) :
    ((P.OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤ 1 / 2 ^ b :=
  P.optimizedFalseAcceptance_probability_le_two_pow_neg hax hbasis hwidth Qc Qm b
    (optimizedTrimmedProductionFailure_support_of_hostile _ _ _ _ _ _ _
      (by simpa [hostileInterWork] using hsupport))

/-- The same bit conclusion from the *extension* support premise. -/
theorem optimizedFalseAcceptance_probability_le_two_pow_neg_extension
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (b : ℕ)
    (hsupport :
      optimizedExtensionProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
          (OptimizedFailureEventEv.workloadEv P P.optimized.Λ +
            OptimizedHostileTimestamps.timestampCollisionBound
              (3 * P.optimized.family.problem.cfg.compRows) +
            pricedWalkWork P.optimized.family.problem.cfg.compRows
            P.optimized.family.problem.cfg.memRows)
          (P.hostileIOWork + P.hostileInterWork)
          P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows *
          2 ^ b ≤ 1) :
    ((P.OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤ 1 / 2 ^ b :=
  P.optimizedFalseAcceptance_probability_le_two_pow_neg_trimmed hax hbasis hwidth Qc Qm b
    (optimizedTrimmedProductionFailure_support_of_extension _ _ _ _ _ _ _ hsupport)

/-- The same bit conclusion from the pre-`KX` *merged* support premise. -/
theorem optimizedFalseAcceptance_probability_le_two_pow_neg_merged
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (b : ℕ)
    (hsupport :
      optimizedMergedProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
          (OptimizedFailureEventEv.workloadEv P P.optimized.Λ +
            OptimizedHostileTimestamps.timestampCollisionBound
              (3 * P.optimized.family.problem.cfg.compRows) +
            pricedWalkWork P.optimized.family.problem.cfg.compRows
            P.optimized.family.problem.cfg.memRows)
          (P.hostileIOWork + P.hostileInterWork)
          P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows *
          2 ^ b ≤ 1) :
    ((P.OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤ 1 / 2 ^ b :=
  P.optimizedFalseAcceptance_probability_le_two_pow_neg_extension hax hbasis hwidth Qc Qm b
    (optimizedExtensionProductionFailure_support_of_merged _ _ _ _ _ _ _ hsupport)

theorem optimizedFalseAcceptance_probability_le_two_pow_neg_legacy
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (b : ℕ)
    (hsupport :
      optimizedProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
          (OptimizedFailureEventEv.workloadEv P P.optimized.Λ +
            OptimizedHostileTimestamps.timestampCollisionBound
              (3 * P.optimized.family.problem.cfg.compRows) +
            pricedWalkWork P.optimized.family.problem.cfg.compRows
            P.optimized.family.problem.cfg.memRows)
          (P.hostileIOWork + P.hostileInterWork)
          P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows *
          2 ^ b ≤ 1) :
    ((P.OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤ 1 / 2 ^ b :=
  P.optimizedFalseAcceptance_probability_le_two_pow_neg_merged hax hbasis hwidth Qc Qm b
    (optimizedMergedProductionFailure_support_of_legacy _ _ _ _ _ _ _ Fintype.card_pos hsupport)

/-- Every field is a fact about the COMMITTED traces `(Qc, Qm)` at the twelve-coin tuple
`c` (the compute trace read at `forget12 c`, the memory trace at the memory view `walkView11 c`,
i.e. at the walk coin `αW`); no transport (`reHost` / `reWalk`) is named.  The 309 source
obligations and the decoded transitions of the committed compute trace (`compute309`, `compute`),
the twelve-coin memory buckets of the committed memory trace (`memory12`), the IO and
request-timestamp exclusions at the committed traces, summand 15's walk-line exclusion at the
timestamp coin over the memory rows (`walk_timestamp_good`), the honest-record `IO.LIO`, the
forest/axis connective, and `p8`: the claim HOLDS under Nock's semantics. -/
structure OptimizedProductionGenuineTargetAt309
    [Fintype F] [DecidableEq F]
    (Qc : Fin 309 → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : PartA12.OptimizedProductionChallengeTuple12 K F) : Prop where
  sampled_io :
    IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs
  hostile_io_event_good :
    (PartA12.forget12 c).2.1 ∉ FiniteIO.IOFailureEvent (P.hostileRecordsAt (PartA12.forget12 c)
      (P.familyQm (PartA12.forget12 c) Qm)
      (P.familyQc (PartA12.forget12 c) (PartAStaged.truncQc P Qc)))
  timestamp_collision_good :
    alphaM c.1 ∉ OptimizedHostileTimestamps.TimestampCollisionEvent
      (P.hostileRequestsAt (PartA12.forget12 c)
        (P.familyQc (PartA12.forget12 c) (PartAStaged.truncQc P Qc))).length
  walk_timestamp_good :
    alphaM c.1 ∉ OptimizedHostileTimestamps.TimestampCollisionEvent
      P.optimized.family.problem.cfg.memRows
  compute309 :
    ∀ i : Fin P.optimized.family.problem.cfg.compRows,
      Unhosted309.SourceObligations309 P.optimized.family.problem.cfg.compRows
        (Unhosted309.gather309 P.optimized.basis
          (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
            (DeployedChipFamily.computeChalValOfTuple P.optimized.basis (PartA12.forget12 c))
            (P.familyComputePublic (PartA12.forget12 c))))
        (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
          (DeployedChipFamily.computeChalValOfTuple P.optimized.basis (PartA12.forget12 c))
          (P.familyComputePublic (PartA12.forget12 c)))
  compute :
    ∀ i : Fin P.optimized.family.problem.cfg.compRows,
      (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows →
      Unhosted309.DecodedTransitionSources309
        (Unhosted309.gather309 P.optimized.basis
          (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
            (DeployedChipFamily.computeChalValOfTuple P.optimized.basis (PartA12.forget12 c))
            (P.familyComputePublic (PartA12.forget12 c))))
  memory12 :
    ∀ i,
      (∀ g ∈ baseTransitionGates P.optimized.basis,
        g.eval (P.memEnvF (PartA12.walkView11 c) (P.familyQm (PartA12.walkView11 c) Qm) i) = 0) ∧
      (∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
        g.eval (P.memEnvK (PartA12.walkView11 c) (P.familyQm (PartA12.walkView11 c) Qm) i)
          (P.memEnvF (PartA12.walkView11 c) (P.familyQm (PartA12.walkView11 c) Qm) i) = 0)
  aggregate_forest_axis : P.optimized.OptimizedSharedMemoryConnective
  p8 :
    ∃ fuel, Nock.evalN fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result

/-- **Acceptance at the parallel package outside the fifteen-summand event gives the
committed-trace target**: the committed-trace fields of
`PartATarget309.acceptance_outside_failure_implies_target12` (R-T steps 1–6), and the decoded 309
transitions by `Unhosted309.conditional_transition_soundness309` on every non-last row (the
last-row mask from `PartAReHost.rowHyps_of_sat`).  The three Form R premises are `of_package`'s. -/
theorem acceptance_outside_failure_implies_target309
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin 309 → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : PartA12.OptimizedProductionChallengeTuple12 K F)
    (hacc : PartAStaged.AcceptanceAt309 P Qc Qm c)
    (hgood : c ∉ PartAStaged.consumedFailureEvent309 P Qc Qm) :
    P.OptimizedProductionGenuineTargetAt309 Qc Qm c := by
  have h := PartATarget309.acceptance_outside_failure_implies_target12 P hax hbasis hwidth
    Qc Qm c hacc hgood
  have hrow := (PartAReHost.rowHyps_of_sat P (PartA12.forget12 c) Qc hacc.compute_satisfies).1
  exact
    { sampled_io := h.landed_sampled_io
      hostile_io_event_good := h.hostile_io_event_good
      timestamp_collision_good := h.timestamp_collision_good
      walk_timestamp_good := h.walk_timestamp_good
      compute309 := h.compute309
      compute := fun i hi => by
        have hmask12 := hrow.mask12 i
        refine Unhosted309.conditional_transition_soundness309 (h.compute309 i) ?_
        change (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
            (DeployedChipFamily.computeChalValOfTuple P.optimized.basis (PartA12.forget12 c))
            (P.familyComputePublic (PartA12.forget12 c))).trace 12 = 0
        rw [hmask12, if_neg]
        intro he
        have := congrArg Fin.val he
        simp only [PartAReHost.rowL, PartAReHost.nC] at this
        omega
      memory12 := h.memory12
      aggregate_forest_axis := h.landed_aggregate_forest_axis
      p8 := h.landed_p8 }

/-- **The fixed-trace false-acceptance probability at the parallel package**, at the fifteen-summand
bound: the constant-strategy corollary of the staged bound
(`PartAStaged.complete_false_acceptance_bound_of_staged12`), at the same `ε`. -/
theorem optimizedFalseAcceptance309_probability_le
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin 309 → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    ((Finset.univ.filter fun c =>
        PartAStaged.AcceptanceAt309 P Qc Qm c ∧ ¬ P.OptimizedProductionGenuineTargetAt309 Qc Qm c).card : ℚ) /
        Fintype.card (PartA12.OptimizedProductionChallengeTuple12 K F) ≤
      PartA12.optimizedHostileProductionFailureProbabilityBound15 (Fintype.card K) (Fintype.card F)
          (OptimizedFailureEventEv.workloadEv P P.optimized.Λ)
          (FiniteIO.ioFailureUnionBound 10 (3 * P.optimized.family.problem.cfg.compRows)
            P.optimized.family.problem.cfg.memRows (Fintype.card K))
          P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows :=
  PartAStaged.complete_false_acceptance_bound_of_staged12 P (P.OptimizedProductionGenuineTargetAt309)
    (fun Qc Qm c hacc hgood =>
      P.acceptance_outside_failure_implies_target309 hax hbasis hwidth Qc Qm c hacc hgood) Qc Qm

/-- **The bits form of the fifteen-summand bound** (the restated `complete_false_acceptance_bits`):
`ε · 2^b ≤ 1` gives the fixed-trace false-acceptance probability `≤ 2^-b`. -/
theorem optimizedFalseAcceptance309_probability_le_two_pow_neg
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin 309 → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (b : ℕ)
    (hsupport :
      PartA12.optimizedHostileProductionFailureProbabilityBound15 (Fintype.card K) (Fintype.card F)
          (OptimizedFailureEventEv.workloadEv P P.optimized.Λ)
          (FiniteIO.ioFailureUnionBound 10 (3 * P.optimized.family.problem.cfg.compRows)
            P.optimized.family.problem.cfg.memRows (Fintype.card K))
          P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows *
          2 ^ b ≤ 1) :
    ((Finset.univ.filter fun c =>
        PartAStaged.AcceptanceAt309 P Qc Qm c ∧ ¬ P.OptimizedProductionGenuineTargetAt309 Qc Qm c).card : ℚ) /
        Fintype.card (PartA12.OptimizedProductionChallengeTuple12 K F) ≤ 1 / 2 ^ b := by
  refine (P.optimizedFalseAcceptance309_probability_le hax hbasis hwidth Qc Qm).trans ?_
  have hpow : (0 : ℚ) < 2 ^ b := by positivity
  apply (le_div_iff₀ hpow).2
  simpa [mul_comm] using hsupport

/-- **The staged false-acceptance bound, at `repartitionedChronology`.**  For every staged
prover strategy (`PartAStaged.StagedTraces12`: block B0 fixed, B1 a function of the M1 coins, B2
of all twelve), the fraction of the twelve coins at which its traces are accepted by the parallel
chips while the committed-trace target fails is at most `ε`
(`PartAStaged.staged_false_acceptance_bound12`, no `hAT`) -/
theorem stagedFalseAcceptance309_probability_le
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : PartA12.OptimizedProductionChallengeTuple12 K F → Fin 309 → F[X])
    (Qm : PartA12.OptimizedProductionChallengeTuple12 K F → Fin P.memoryChip.rap.w → F[X])
    (hst : PartAStaged.StagedTraces12 P Qc Qm) :
    ((Finset.univ.filter fun c =>
        PartAStaged.AcceptanceAt309 P (Qc c) (Qm c) c ∧
          ¬ P.OptimizedProductionGenuineTargetAt309 (Qc c) (Qm c) c).card : ℚ) /
        Fintype.card (PartA12.OptimizedProductionChallengeTuple12 K F) ≤
      PartA12.optimizedHostileProductionFailureProbabilityBound15 (Fintype.card K) (Fintype.card F)
          (OptimizedFailureEventEv.workloadEv P P.optimized.Λ)
          (FiniteIO.ioFailureUnionBound 10 (3 * P.optimized.family.problem.cfg.compRows)
            P.optimized.family.problem.cfg.memRows (Fintype.card K))
          P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows :=
  PartAStaged.staged_false_acceptance_bound12 P (P.OptimizedProductionGenuineTargetAt309)
    (fun Qc Qm c hacc hgood =>
      P.acceptance_outside_failure_implies_target309 hax hbasis hwidth Qc Qm c hacc hgood) Qc Qm hst

/-- Prime-field residue: `card F = char F` means every scalar is a nat cast
below the characteristic. -/
theorem package_prime_field_residue {F : Type} [Field F] [Fintype F]
    (hpf : Fintype.card F = ringChar F) (x : F) :
    ∃ a : ℕ, a < ringChar F ∧ (a : F) = x := by
  have hne : ringChar F ≠ 0 := by
    intro h0
    exact Fintype.card_ne_zero (hpf.trans h0)
  have hcard : Fintype.card (Fin (ringChar F)) = Fintype.card F := by
    rw [Fintype.card_fin, hpf]
  let f : Fin (ringChar F) → F := fun i => (i.val : F)
  have hinj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have hmod : a.val ≡ b.val [MOD ringChar F] :=
      (CharP.natCast_eq_natCast (R := F) (p := ringChar F)).mp (by
        simpa [f] using hab)
    exact Nat.ModEq.eq_of_lt_of_lt hmod a.isLt b.isLt
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  obtain ⟨i, hi⟩ := hbij.2 x
  exact ⟨i.val, i.isLt, hi⟩

/-- Prime-field image of a difference of nat casts. -/
theorem package_nat_sub_residue [Fintype F] (a b : ℕ) :
    ∃ r : ℕ, r < ringChar F ∧ (r : F) = (a : F) - (b : F) := by
  haveI : CharP F (ringChar F) := ringChar.charP F
  have hpr : Nat.Prime (ringChar F) := CharP.char_is_prime F (ringChar F)
  haveI : Fact (ringChar F).Prime := ⟨hpr⟩
  haveI : NeZero (ringChar F) := ⟨Nat.Prime.ne_zero hpr⟩
  haveI : Algebra (ZMod (ringChar F)) F := ZMod.algebra _ _
  let z : ZMod (ringChar F) := (a : ZMod (ringChar F)) - (b : ZMod (ringChar F))
  refine ⟨z.val, ZMod.val_lt z, ?_⟩
  have hmap : (algebraMap (ZMod (ringChar F)) F) z = (a : F) - (b : F) := by
    simp [z, map_sub, map_natCast]
  have hval : (algebraMap (ZMod (ringChar F)) F) z = (z.val : F) := by
    rw [← map_natCast (algebraMap (ZMod (ringChar F)) F) z.val]
    congr 1
    exact (ZMod.natCast_zmod_val z).symm
  exact hval.symm.trans hmap

/-- Honest Form R axis bound of this package.  Window classifiers deleted.
Not `∀ L : F` and not a binder of `nockCompiles_zmod`.  Discharge is
`runAxesBoundedBy_of_hyps` plus the committed-leaf correspondence. -/
theorem package_formRAxisBound [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis) :
    FormRAxisBound P.optimized.sampled P.optimized.basis :=
  hax

end OptimizedFullStrictNockVMROMPackage

open OptimizedFullStrictNockVMROMPackage

/-- The full Theorem 5.4 statement for the package.

`shared_io` and the target's `sampled_io` state `IO.LIO` at the **honest** records; the
hostile-record `IO.LIO` is the separate theorem
`OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO`, consumed from this statement's
`acceptance_to_target`.  The `19·M/|𝕂|` memory-fold summand is absent.

`acceptance_to_target` and `complete_false_acceptance_bound` / `_bits` are stated at the parallel
package objects: the twelve-coin tuple `PartA12.OptimizedProductionChallengeTuple12` (timestamp coin
`α`, separate memory walk coin `αW`), the 309 compute trace, `PartAStaged.AcceptanceAt309` (what the
two chips check), the fifteen-summand event `PartAStaged.consumedFailureEvent309`, the committed-trace
target `OptimizedProductionGenuineTargetAt309` and the bound
`PartA12.optimizedHostileProductionFailureProbabilityBound15` (the fixed-trace bound plus summand
15's `(1 + M(M−1)/2)/|𝕂|`).  The conjunct `staged_false_acceptance_bound` is the bound for every
staged prover strategy at `RepartitionedStaging.repartitionedChronology` (B0 fixed, B1 a function of
the M1 coins, B2 of all twelve); the fixed-trace conjunct is its constant-strategy corollary at the
same `ε`.  The statement does not assert soundness at `deployedChronology`. -/
structure OptimizedFullStrictThm54Statement
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) where
  optimized_chips :
    OptimizedComputeRealizationAt P.optimized.sampled P.optimized.computeObligations
        P.optimized.computeNodes P.optimized.basis P.optimized.computeChallenge
        P.optimized.computePublic P.optimized.orbit ∧
      OptimizedMemoryRealizationAt P.optimized.sampled P.optimized.memoryProduction
        P.optimized.memoryNodes P.optimized.basis P.optimized.memoryChallenge
        P.optimized.memoryPublic P.optimized.orbit
  structural :
    VerifiableVMCompilation
      (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
      (nmrMEF F K) K 10 3
      (∀ lmb : K, FixedFieldSoundnessClaim P.strategy P.q P.optimized.Λ lmb)
      P.p8_fixedField_falseAcceptance_le
      (P.OptimizedFullCostRealization) P.optimizedFullCostRealization
      (CombinedCompletenessAt P.objects.cfg P.objects.exec)
      (exactChainedHasPerfectCompleteness F K P.objects.cfg P.objects.exec)
      (P.OptimizedFullTwoRAPRealization) (P.optimizedFullTwoRAPRealizationOf optimized_chips)
      (nock_uniqueMES F K _ _ _)
      (ExactChainedHasCanonicalRAP2 F K) (exactChainedHasCanonicalRAP2 F K)
      (OneHotRealization P.objects.cfg P.objects.exec) P.chained.oneHotRealization
      (DefTraversableRealization P.objects.cfg)
      (defTraversableRealization P.objects.cfg P.objects.exec.memoryRootCount_pos)
      ⟨⟨stmtOfExact P.objects.cfg P.objects.exec, P.perfect_completeness⟩⟩
  shared_io : IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs
  perfect_completeness :
    Language
      (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
      (stmtOfExact P.objects.cfg P.objects.exec)
  containment :
    ∀ (ω : JointCoins K) (lmb : K), P.strategy.Accepts ω lmb →
      ω ∉ ProductionP8Containment.FailureUnion P.strategy P.optimized.census lmb →
      GenuineTargetAt P.strategy P.q P.optimized.Λ ω lmb
  walk_bounds :
    P.computeWalkBadRatio ≤ P.computeWalkBound ∧
      P.memoryWalkBadRatio ≤ P.memoryWalkBound
  p8_fixed_field_soundness :
    ∀ lmb : K, |jointProbability (FalseAcceptanceSet P.strategy P.q P.optimized.Λ lmb)| ≤
      (workload P.strategy P.optimized.Λ
          (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy) : ℝ) /
        (Fintype.card K : ℝ)
  p8_fixed_field_bits :
    ∀ (lmb : K) (b : ℕ),
      workload P.strategy P.optimized.Λ
          (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy) * 2 ^ b ≤
          Fintype.card K →
      |jointProbability (FalseAcceptanceSet P.strategy P.q P.optimized.Λ lmb)| ≤ 1 / 2 ^ b
  acceptance_to_target :
    ∀ (Qc : Fin 309 → F[X])
      (Qm : Fin P.memoryChip.rap.w → F[X])
      (c : PartA12.OptimizedProductionChallengeTuple12 K F),
      PartAStaged.AcceptanceAt309 P Qc Qm c →
      c ∉ PartAStaged.consumedFailureEvent309 P Qc Qm →
      P.OptimizedProductionGenuineTargetAt309 Qc Qm c
  complete_false_acceptance_bound :
    ∀ (Qc : Fin 309 → F[X])
      (Qm : Fin P.memoryChip.rap.w → F[X]),
      ((Finset.univ.filter fun c =>
          PartAStaged.AcceptanceAt309 P Qc Qm c ∧
            ¬ P.OptimizedProductionGenuineTargetAt309 Qc Qm c).card : ℚ) /
          Fintype.card (PartA12.OptimizedProductionChallengeTuple12 K F) ≤
        PartA12.optimizedHostileProductionFailureProbabilityBound15 (Fintype.card K) (Fintype.card F)
          (OptimizedFailureEventEv.workloadEv P P.optimized.Λ)
          (FiniteIO.ioFailureUnionBound 10 (3 * P.optimized.family.problem.cfg.compRows)
            P.optimized.family.problem.cfg.memRows (Fintype.card K))
          P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows
  complete_false_acceptance_bits :
    ∀ (Qc : Fin 309 → F[X])
      (Qm : Fin P.memoryChip.rap.w → F[X]) (b : ℕ),
      PartA12.optimizedHostileProductionFailureProbabilityBound15 (Fintype.card K) (Fintype.card F)
          (OptimizedFailureEventEv.workloadEv P P.optimized.Λ)
          (FiniteIO.ioFailureUnionBound 10 (3 * P.optimized.family.problem.cfg.compRows)
            P.optimized.family.problem.cfg.memRows (Fintype.card K))
          P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows *
          2 ^ b ≤ 1 →
      ((Finset.univ.filter fun c =>
          PartAStaged.AcceptanceAt309 P Qc Qm c ∧
            ¬ P.OptimizedProductionGenuineTargetAt309 Qc Qm c).card : ℚ) /
          Fintype.card (PartA12.OptimizedProductionChallengeTuple12 K F) ≤ 1 / 2 ^ b
  staged_false_acceptance_bound :
    ∀ (Qc : PartA12.OptimizedProductionChallengeTuple12 K F → Fin 309 → F[X])
      (Qm : PartA12.OptimizedProductionChallengeTuple12 K F → Fin P.memoryChip.rap.w → F[X]),
      PartAStaged.StagedTraces12 P Qc Qm →
      ((Finset.univ.filter fun c =>
          PartAStaged.AcceptanceAt309 P (Qc c) (Qm c) c ∧
            ¬ P.OptimizedProductionGenuineTargetAt309 (Qc c) (Qm c) c).card : ℚ) /
          Fintype.card (PartA12.OptimizedProductionChallengeTuple12 K F) ≤
        PartA12.optimizedHostileProductionFailureProbabilityBound15 (Fintype.card K) (Fintype.card F)
          (OptimizedFailureEventEv.workloadEv P P.optimized.Λ)
          (FiniteIO.ioFailureUnionBound 10 (3 * P.optimized.family.problem.cfg.compRows)
            P.optimized.family.problem.cfg.memRows (Fintype.card K))
          P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows
  exact_resources : P.OptimizedFullCostRealization
  row_budgets :
    P.computeChip.rap.H.card = P.objects.cfg.compRows ∧
      P.memoryChip.rap.H.card =
        RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec
  shared_forest_axis : P.optimized.OptimizedSharedMemoryConnective

def optimizedFullStrictNockVMROM_of_package
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedFullStrictThm54Statement P where
  optimized_chips :=
    P.optimized.realization_surface_of_leafCover hax hbasis hwidth
  structural := ⟨⟩
  shared_io := P.shared_io
  perfect_completeness := P.perfect_completeness
  containment := P.containment
  walk_bounds := ⟨P.computeWalk_bound, P.memoryWalk_bound⟩
  p8_fixed_field_soundness := P.p8_fixedField_falseAcceptance_le
  p8_fixed_field_bits := P.p8_fixedField_falseAcceptance_le_two_pow_neg
  acceptance_to_target := P.acceptance_outside_failure_implies_target309 hax hbasis hwidth
  complete_false_acceptance_bound := P.optimizedFalseAcceptance309_probability_le hax hbasis hwidth
  complete_false_acceptance_bits :=
    P.optimizedFalseAcceptance309_probability_le_two_pow_neg hax hbasis hwidth
  staged_false_acceptance_bound := P.stagedFalseAcceptance309_probability_le hax hbasis hwidth
  exact_resources := P.optimizedFullCostRealization
  row_budgets := ⟨P.compute_row_budget, P.memory_row_budget⟩
  shared_forest_axis := P.optimized.shared_memory_connective


/-- **The released capstone's deployed numerals, read back off the statement.**  `Def:RAP`'s `e`
is named in the capstone's resource conjunct, so this reads the width, transition-count, degree and
round numerals of the compute and memory chips off the statement that
`optimizedFullStrictNockVMROM_of_package` produces.

The deployed compute chip has a tree gate that the paper's `V_comp` does not have; `Lem:equiv_compute`
is an iff against `V_comp`, and the deployed chip is strictly stronger than it: without that gate the
committed timestamps are `ln₀ · α^k` with `ln₀` a free prover value.

The memory equality-check bucket consists of four `𝕂`-valued checks, which the parametric conjunct
records as `memoryEqualityChecks e : 4 → 4·e`.  These counters count *committed base gates*, whereas
the paper's "Two equality checks" and "Four" count *verifier-side equalities on terminal outputs*;
`EqualityCheckLedger.paper_equality_checks_reconstructed` carries the paper's own `2` and `4`. -/
theorem released_capstone_deployed_numerals
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    (P.computeChip.rap.w = 303 ∧ P.computeChip.rap.s = 418 ∧
        P.computeChip.rap.d = 4 ∧ P.computeChip.rap.k = 2) ∧
      (P.memoryChip.rap.w = 205 ∧ P.memoryChip.rap.s = 156 ∧
        P.memoryChip.rap.d = 4 ∧ P.memoryChip.rap.k = 1) ∧
      (P.computeChip.rap.s - 44 = 374 ∧ P.memoryChip.rap.s - 0 = 156) :=
  P.cost_realization_deployed_numerals P.optimizedFullCostRealization

structure HistoricalNonB29FieldMap
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) : Prop where
  optimized_named_chips :
    OptimizedComputeRealizationAt P.optimized.sampled P.optimized.computeObligations
        P.optimized.computeNodes P.optimized.basis P.optimized.computeChallenge
        P.optimized.computePublic P.optimized.orbit ∧
      OptimizedMemoryRealizationAt P.optimized.sampled P.optimized.memoryProduction
        P.optimized.memoryNodes P.optimized.basis P.optimized.memoryChallenge
        P.optimized.memoryPublic P.optimized.orbit
  structural :
    VerifiableVMCompilation
      (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
      (nmrMEF F K) K 10 3
      (∀ lmb : K, FixedFieldSoundnessClaim P.strategy P.q P.optimized.Λ lmb)
      P.p8_fixedField_falseAcceptance_le
      (P.OptimizedFullCostRealization) P.optimizedFullCostRealization
      (CombinedCompletenessAt P.objects.cfg P.objects.exec)
      (exactChainedHasPerfectCompleteness F K P.objects.cfg P.objects.exec)
      (P.OptimizedFullTwoRAPRealization)
      (P.optimizedFullTwoRAPRealizationOf optimized_named_chips)
      (nock_uniqueMES F K _ _ _)
      (ExactChainedHasCanonicalRAP2 F K) (exactChainedHasCanonicalRAP2 F K)
      (OneHotRealization P.objects.cfg P.objects.exec) P.chained.oneHotRealization
      (DefTraversableRealization P.objects.cfg)
      (defTraversableRealization P.objects.cfg P.objects.exec.memoryRootCount_pos)
      ⟨⟨stmtOfExact P.objects.cfg P.objects.exec, P.perfect_completeness⟩⟩
  shared_io : IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs
  perfect_completeness :
    Language
      (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
      (stmtOfExact P.objects.cfg P.objects.exec)
  containment :
    ∀ (ω : JointCoins K) (lmb : K), P.strategy.Accepts ω lmb →
      ω ∉ ProductionP8Containment.FailureUnion P.strategy P.optimized.census lmb →
      GenuineTargetAt P.strategy P.q P.optimized.Λ ω lmb
  walk_bounds :
    P.computeWalkBadRatio ≤ P.computeWalkBound ∧
      P.memoryWalkBadRatio ≤ P.memoryWalkBound
  fixed_field_soundness :
    ∀ lmb : K, |jointProbability (FalseAcceptanceSet P.strategy P.q P.optimized.Λ lmb)| ≤
      (workload P.strategy P.optimized.Λ
          (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy) : ℝ) /
        (Fintype.card K : ℝ)
  exact_resources : P.OptimizedFullCostRealization
  row_budgets :
    P.computeChip.rap.H.card = P.objects.cfg.compRows ∧
      P.memoryChip.rap.H.card =
        RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec
  stronger_event :
    ∀ (Qc : Fin 309 → F[X])
      (Qm : Fin P.memoryChip.rap.w → F[X])
      (c : PartA12.OptimizedProductionChallengeTuple12 K F),
      PartAStaged.AcceptanceAt309 P Qc Qm c →
      c ∉ PartAStaged.consumedFailureEvent309 P Qc Qm →
      P.OptimizedProductionGenuineTargetAt309 Qc Qm c
  aggregate_forest_axis : P.optimized.OptimizedSharedMemoryConnective

theorem full_statement_field_map
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} {P : OptimizedFullStrictNockVMROMPackage F K hOrb}
    (S : OptimizedFullStrictThm54Statement P) :
    HistoricalNonB29FieldMap P where
  optimized_named_chips := S.optimized_chips
  structural := ⟨⟩
  shared_io := S.shared_io
  perfect_completeness := S.perfect_completeness
  containment := S.containment
  walk_bounds := S.walk_bounds
  fixed_field_soundness := S.p8_fixed_field_soundness
  exact_resources := S.exact_resources
  row_budgets := S.row_budgets
  stronger_event := S.acceptance_to_target
  aggregate_forest_axis := S.shared_forest_axis

/-- Compiled surface receipt: production consists only of the optimized package and the restored
non-B29 core. -/
theorem production_surface_is_full_and_optimized
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    Nonempty (OptimizedFullStrictThm54Statement P) :=
  ⟨optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth⟩

end
end OptimizedStrictFullPackage
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.structural
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.acceptance_outside_failure_implies_target
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.optimizedFalseAcceptance_probability_le
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.exact_resources_iff_deployed_numerals
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.cost_realization_deployed_numerals
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.released_capstone_deployed_numerals
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.production_surface_is_full_and_optimized

end Nock.Walk37
