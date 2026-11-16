import Nock.RedTeam.Batch68Thm54P8TraceThreading
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

They do not
change production semantics.
-/

namespace Nock.RedTeam.Batch69

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness

noncomputable section

/-! ## Whole dependent problem identity and transport attacks -/

/-- The proof argument used to specialize at a nonzero seed cannot select different data:
proof irrelevance identifies the complete dependent `RawProblem`. -/
theorem specialization_nonzero_proof_irrelevant
    {F K : Type} [Field F] [Field K] [Algebra F K]
    (T : SemanticTimestampStrategy.DataOnlyTemplateFixedStagedTimestampStrategy
      (F := F) (K := K))
    (z : K) (h₁ h₂ : z ≠ 0) (α lmb : K) :
    specializedProblem T z h₁ α lmb = specializedProblem T z h₂ α lmb := by
  have hp : h₁ = h₂ := Subsingleton.elim _ _
  cases hp
  rfl

/-- Equality of a `RawProblem` forces both its configuration and its dependent execution.
The second conclusion is heterogeneous because the execution type depends on the first field. -/
theorem raw_problem_equality_forces_cfg_and_exec
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {Q R : RawProblem F K} (h : Q = R) :
    Q.cfg = R.cfg ∧ HEq Q.exec R.exec := by
  cases h
  exact ⟨rfl, HEq.rfl⟩

/-- Same raw-problem equality cannot hide a different configuration. -/
theorem different_cfg_rejects_raw_problem_equality
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {Q R : RawProblem F K} (hcfg : Q.cfg ≠ R.cfg) :
    Q ≠ R := by
  intro h
  exact hcfg (raw_problem_equality_forces_cfg_and_exec h).1

/-- Even with the same configuration, a different dependent execution cannot be hidden in a
whole-`RawProblem` equality. -/
theorem same_cfg_different_exec_rejects_raw_problem_equality
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} {e₁ e₂ : ExactExecution cfg}
    (hexec : e₁ ≠ e₂) :
    ({ cfg := cfg, exec := e₁ } : RawProblem F K) ≠
      { cfg := cfg, exec := e₂ } := by
  intro h
  exact hexec (eq_of_heq (raw_problem_equality_forces_cfg_and_exec h).2)

/-- The repaired record is equivalent to one nonzero witness plus equality of the entire dependent
specialization to the package objects.  Its cfg/exec family fields cannot be detached: the reverse
direction derives them from that whole equality and the package's family link. -/
theorem same_problem_iff_whole_problem_equality
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (j : JointCoins K) (lmb : K) :
    P.OptimizedSameProblemAt j lmb ↔
      ∃ hz : nprSeed j ≠ 0,
        specializedProblem P.optimized.verifier.raw.timestamp
            (nprSeed j) hz (alphaM j) lmb =
          { cfg := P.objects.cfg, exec := P.objects.exec } := by
  constructor
  · intro h
    exact ⟨h.nprSeed_ne, h.specialized_eq_objects⟩
  · rintro ⟨hz, hwhole⟩
    exact OptimizedSameProblemAt.of_objects P j lmb hz hwhole

/-- The three repaired fields jointly identify the specialization with the exact optimized family
as a dependent sigma pair.  Thus family cfg and execution are not independently attachable. -/
theorem same_problem_identifies_optimized_family_sigma
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (j : JointCoins K) (lmb : K) (h : P.OptimizedSameProblemAt j lmb) :
    (⟨(specializedProblem P.optimized.verifier.raw.timestamp
          (nprSeed j) h.nprSeed_ne (alphaM j) lmb).cfg,
        (specializedProblem P.optimized.verifier.raw.timestamp
          (nprSeed j) h.nprSeed_ne (alphaM j) lmb).exec⟩ :
        Σ cfg : ExactConfig F K, ExactExecution cfg) =
      ⟨P.optimized.family.problem.cfg, P.optimized.family.problem.exec⟩ :=
  Sigma.ext h.specialized_cfg_eq_family h.specialized_exec_heq_family

/-- Whole-problem equality forces both sampled specialization coordinates to be the package's
actual configuration coordinates; an alternate seed or `alphaM` cannot survive by transport. -/
theorem same_problem_forces_seed_and_alpha
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (j : JointCoins K) (lmb : K) (h : P.OptimizedSameProblemAt j lmb) :
    nprSeed j = P.objects.cfg.challenges.z ∧
      alphaM j = P.objects.cfg.challenges.α := by
  have hcfg := congrArg RawProblem.cfg h.specialized_eq_objects
  constructor
  · calc
      nprSeed j =
          (specializedProblem P.optimized.verifier.raw.timestamp
            (nprSeed j) h.nprSeed_ne (alphaM j) lmb).cfg.challenges.z := by
            symm
            exact specializedProblem_seed _ _ _ _ _
      _ = P.objects.cfg.challenges.z :=
        congrArg (fun cfg : ExactConfig F K => cfg.challenges.z) hcfg
  · calc
      alphaM j =
          (specializedProblem P.optimized.verifier.raw.timestamp
            (nprSeed j) h.nprSeed_ne (alphaM j) lmb).cfg.challenges.α := by
            symm
            exact specializedProblem_tableAlpha _ _ _ _ _
      _ = P.objects.cfg.challenges.α :=
        congrArg (fun cfg : ExactConfig F K => cfg.challenges.α) hcfg

/-- Any alternate seed/alpha specialization whose whole problem differs from the package objects
is rejected by repaired acceptance.  This is generic and does not rely on the honest constructor. -/
theorem acceptance_rejects_any_alternate_specialization
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hz : nprSeed c.1 ≠ 0)
    (hne :
      specializedProblem P.optimized.verifier.raw.timestamp
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda ≠
        { cfg := P.objects.cfg, exec := P.objects.exec }) :
    ¬ P.OptimizedHistoricalAcceptanceAt Qc Qm c := by
  intro hacc
  apply hne
  exact (specialization_nonzero_proof_irrelevant
    P.optimized.verifier.raw.timestamp (nprSeed c.1) hz
    hacc.same_problem.nprSeed_ne (alphaM c.1) c.2.2.2.lambda).trans
      hacc.same_problem.specialized_eq_objects

/-! ## Acceptance and target load-bearing shape

The production acceptance is the two family-chip
satisfactions, and the target carries neither `p8` nor `same_problem` (the disclosed p8 gap).  The
acceptance receipts of this batch are restated against `OptimizedHistoricalAcceptanceAt` /
`OptimizedHistoricalTraceAcceptanceAt` (the pre-2a objects, verbatim).  Deleted, because the
target fields they read are gone: `target_factorization_requires_same_problem`,
`connective_preserves_exact_same_problem_witness`, `target_p8_witness_uses_identified_specialization`,
`target_threads_all_semantics_at_identified_problem`, `concrete_repaired_connective_nonvacuous`. -/

theorem repaired_acceptance_eta
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} {P : OptimizedFullStrictNockVMROMPackage F K hOrb}
    {Qc : Fin P.computeChip.rap.w → F[X]}
    {Qm : Fin P.memoryChip.rap.w → F[X]}
    {c : OptimizedProductionChallengeTuple K F}
    (h : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    h =
      { p8 := h.p8
        same_problem := h.same_problem
        sampled_io_coins := h.sampled_io_coins
        memory_sampled_coins := h.memory_sampled_coins
        memory_intermediate_pole := h.memory_intermediate_pole
        compute_satisfies := h.compute_satisfies
        memory_satisfies := h.memory_satisfies } := by
  cases h
  rfl

/-- Equality/proof transport cannot manufacture a second semantic choice inside the proposition:
all witnesses of the repaired same-problem record are proof-irrelevant. -/
theorem same_problem_witnesses_are_proof_irrelevant
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (j : JointCoins K) (lmb : K) (h₁ h₂ : P.OptimizedSameProblemAt j lmb) :
    h₁ = h₂ :=
  Subsingleton.elim _ _

/-- Current acceptance factors only with the repaired whole-problem conjunct.  This independently
replays the production factorization at the consumed type. -/
theorem acceptance_factorization_requires_same_problem
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (j : JointCoins K)
    (r : (K × K) × (FinalComputeChallengeTuple K × MemoryChallengeTuple K)) :
    P.OptimizedHistoricalAcceptanceAt Qc Qm (j, r) ↔
      P.strategy.Accepts j r.2.2.lambda ∧ P.OptimizedSameProblemAt j r.2.2.lambda ∧
        P.OptimizedHistoricalTraceAcceptanceAt Qc Qm r := by
  constructor
  · intro h
    exact ⟨h.p8, h.same_problem,
      { sampled_io_coins := h.sampled_io_coins
        memory_sampled_coins := h.memory_sampled_coins
        memory_intermediate_pole := h.memory_intermediate_pole
        compute_satisfies := h.compute_satisfies
        memory_satisfies := h.memory_satisfies }⟩
  · rintro ⟨hp8, hsame, htrace⟩
    exact
      { p8 := hp8
        same_problem := hsame
        sampled_io_coins := htrace.sampled_io_coins
        memory_sampled_coins := htrace.memory_sampled_coins
        memory_intermediate_pole := htrace.memory_intermediate_pole
        compute_satisfies := htrace.compute_satisfies
        memory_satisfies := htrace.memory_satisfies }

/-! ## Same event and unchanged mixed-field accounting -/

/-- False acceptance remains exactly repaired acceptance and failure of the repaired target, for
the same traces and tuple. -/
theorem false_acceptance_membership_is_repaired_event
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    c ∈ P.OptimizedFalseAcceptanceSet Qc Qm ↔
      P.OptimizedProductionAcceptanceAt Qc Qm c ∧
        ¬ P.OptimizedProductionGenuineTargetAt Qc Qm c := by
  simp [OptimizedFalseAcceptanceSet]

theorem failure_event_has_no_problem_mismatch_component
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    P.optimizedFailureEvent Qc Qm =
      OptimizedProductionFailureEvent P.strategy P.optimized.census
        P.objects.cfg.challenges.lam
        (P.computeSourceEnv Qc) (P.computeWalkEnv Qc) (P.computeScalarEnv Qc)
        (P.memorySourceEnv Qm) (P.memoryScalarFamilies Qm) ∪
      P.famIOEventOf Qc Qm ∪
      liftTimestampFailure
        (OptimizedHostileTimestamps.TimestampCollisionEvent (P.hostileRequests Qc).length) ∪
      liftInterPoleFailure
        (interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm)
          (P.memoryBaseEnv Qm)) ∪
      liftP8Failure (P.computeWalkRootEvent Qc) ∪
      liftP8Failure (P.computeTilingEventOf Qc) ∪
      liftP8Failure (P.memoryTilingEventOf Qm) ∪
      liftP8Failure (P.computePrefixGammaEventOf Qc) ∪
      liftP8Failure (P.memoryPrefixGammaEventOf Qm) ∪
      liftP8Failure (P.memoryForestAlphaEventOf Qm) ∪
      P.decodedLambdaEventOf Qc Qm ∪
      P.reqPairEventOf Qm :=
  rfl

/-- The exact mixed bound is unchanged. -/
theorem repaired_mixed_denominator_formula_exact
    (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedProductionFailureProbabilityBound cardK cardF p8Work ioWork N M =
      (p8Work + 494 * N + 1 + 61 * M : ℚ) / cardK +
        (ioWork : ℚ) / cardK ^ 2 +
        (20 + 14 * M : ℚ) / cardF :=
  rfl

/-- Subset, probability, and supported-bit consequences all consume the repaired false-acceptance
set. -/
theorem repaired_event_accounting_receipt
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
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
    P.OptimizedFalseAcceptanceSet Qc Qm ⊆ P.consumedFailureEvent Qc Qm ∧
      ((P.OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
          Fintype.card (OptimizedProductionChallengeTuple K F) ≤
        optimizedProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
          (OptimizedFailureEventEv.workloadEv P P.optimized.Λ +
            OptimizedHostileTimestamps.timestampCollisionBound
              (3 * P.optimized.family.problem.cfg.compRows) +
            pricedWalkWork P.optimized.family.problem.cfg.compRows
              P.optimized.family.problem.cfg.memRows)
          (P.hostileIOWork + P.hostileInterWork)
          P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows ∧
      ((P.OptimizedFalseAcceptanceSet Qc Qm).card : ℚ) /
          Fintype.card (OptimizedProductionChallengeTuple K F) ≤ 1 / 2 ^ b :=
  ⟨P.optimizedFalseAcceptanceSet_subset_failure hax hbasis hwidth Qc Qm,
    P.optimizedFalseAcceptance_probability_le_legacy hax hbasis hwidth Qc Qm,
    P.optimizedFalseAcceptance_probability_le_two_pow_neg_legacy hax hbasis hwidth Qc Qm b hsupport⟩


open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- Honest specialization is the actual equality source used by the inhabited repaired
acceptance. -/
theorem concrete_acceptance_uses_honest_specialization
    (hbasis : FormRBasis basis73)
    (hmore : ∀ i : Fin honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < honestLegacyFamily.problem.cfg.kMem →
        (honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0) :
    let P := concreteOptimizedFullStrictPackage
    specializedProblem P.optimized.verifier.raw.timestamp
        P.honestSeed P.honestSeed_ne P.honestAlpha P.objects.cfg.challenges.lam =
        { cfg := P.objects.cfg, exec := P.objects.exec } ∧
      P.OptimizedHistoricalAcceptanceAt
        concreteComputeTrace concreteMemoryTrace concreteProductionChallenge := by
  let P := concreteOptimizedFullStrictPackage
  exact ⟨P.honest_specialization, concrete_production_acceptance hbasis hmore⟩

/-- It uses the generic rejection
lemma above, not the honest acceptance constructor and not an event-complement premise. -/
theorem concrete_seed2_rejected_by_generic_whole_problem_attack :
    ¬ concreteOptimizedFullStrictPackage.OptimizedHistoricalAcceptanceAt
      concreteComputeTrace concreteMemoryTrace
        Nock.RedTeam.Batch68.alternateProductionChallenge := by
  let P := concreteOptimizedFullStrictPackage
  apply acceptance_rejects_any_alternate_specialization P
    concreteComputeTrace concreteMemoryTrace
    Nock.RedTeam.Batch68.alternateProductionChallenge
    Nock.RedTeam.Batch68.alternateSeed_ne
  intro hwhole
  apply Nock.RedTeam.Batch68.concrete_seed2_specialization_differs_from_optimized_family.2
  have hcfg := congrArg RawProblem.cfg hwhole
  have hl : concreteProductionChallenge.2.2.2.lambda = MemoryTable.formRDefault := rfl
  simp only [P, Nock.RedTeam.Batch68.alternateProductionChallenge,
    Nock.RedTeam.Batch68.alternateJointCoins, Nock.RedTeam.Batch68.alternateSeed,
    nprSeed, alphaM] at hcfg
  rw [hl] at hcfg
  exact hcfg

/-! ## Capstone shape, resources, nonterminal execution, aliases, and history -/

set_option maxHeartbeats 800000

/-- All fourteen outer capstone fields remain one-package threaded after the inner acceptance
repair. -/
theorem fourteen_capstone_fields_still_reconstruct
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} {P : OptimizedFullStrictNockVMROMPackage F K hOrb}
    (S : OptimizedFullStrictThm54Statement P) :
    S =
      { structural := S.structural
        optimized_chips := S.optimized_chips
        shared_io := S.shared_io
        perfect_completeness := S.perfect_completeness
        containment := S.containment
        walk_bounds := S.walk_bounds
        p8_fixed_field_soundness := S.p8_fixed_field_soundness
        p8_fixed_field_bits := S.p8_fixed_field_bits
        acceptance_to_target := S.acceptance_to_target
        complete_false_acceptance_bound := S.complete_false_acceptance_bound
        complete_false_acceptance_bits := S.complete_false_acceptance_bits
        staged_false_acceptance_bound := S.staged_false_acceptance_bound
        exact_resources := S.exact_resources
        row_budgets := S.row_budgets
        shared_forest_axis := S.shared_forest_axis } := by
  cases S
  rfl

/-- Exact optimized resources, transition counts, and raw `N` / `M+2L` budgets remain unchanged. -/
theorem repaired_exact_resource_and_budget_receipt
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    P.computeChip.rap.w = 303 ∧ P.computeChip.rap.s = 418 ∧
      P.computeChip.rap.d = 4 ∧ P.computeChip.rap.k = 2 ∧
      P.memoryChip.rap.w = 205 ∧ P.memoryChip.rap.s = 156 ∧
      P.memoryChip.rap.d = 4 ∧ P.memoryChip.rap.k = 1 ∧
      P.computeChip.rap.s - 44 = 374 ∧ P.memoryChip.rap.s - 0 = 156 ∧
      P.computeChip.rap.H.card = P.objects.cfg.compRows ∧
      P.memoryChip.rap.H.card =
        RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec :=
  Nock.RedTeam.Batch67.exact_resource_and_raw_budget_receipt P

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-- The genuine F97 two-row nonterminal fixture still reaches corrected 199/98 satisfaction and
the same-execution decoder. -/
theorem f97_nonterminal_same_execution_unaffected
    (hbasis : FormRBasis basis97) :
    family97.problem.cfg.compRows = 2 ∧
      parentPub.state = .s4 ∧ ComputeTable.fanoutComp parentPub.state = 1 ∧
      parentOut 0 = some childLabel ∧
      exec97.derivedRequestIO.Nodup ∧
      sampledAssignment97.ComputeSampledObligations ∧
      RAP.SatisfiesWithPreprocessing
        (ProductionNamedComputeRAP family97.problem.cfg.compRows_pos computeNodes97 basis97
          challengeCoordinates97 publicCoordinates97 strictOrbit97)
        correctedTrace97 ∧
      CorrectedDecodedTransitionSources
        (gatherCorrectedFinalTypedEnv basis97
          (Nock.Framework.Reify.envOfTrace correctedTrace97 strictOrbit97.ω
            (computeNodes97 row0) challengeCoordinates97 publicCoordinates97)) :=
  strict_release_nonterminal_fixture hbasis

theorem repaired_alias_and_forest_control :
    @«Thm:NockVMROM» =
        @Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  ⟨rfl, rfl⟩

theorem batch68_history_preserved_with_repair :
    let P := concreteOptimizedFullStrictPackage
    (specializedProblem P.optimized.verifier.raw.timestamp
      Nock.RedTeam.Batch68.alternateSeed Nock.RedTeam.Batch68.alternateSeed_ne
      honestAlpha MemoryTable.formRDefault).cfg ≠ P.optimized.family.problem.cfg ∧
    ¬ P.OptimizedHistoricalAcceptanceAt concreteComputeTrace concreteMemoryTrace
      Nock.RedTeam.Batch68.alternateProductionChallenge :=
  ⟨Nock.RedTeam.Batch68.concrete_seed2_specialization_differs_from_optimized_family.1,
    concrete_seed2_rejected_by_generic_whole_problem_attack⟩

#print axioms specialization_nonzero_proof_irrelevant
#print axioms raw_problem_equality_forces_cfg_and_exec
#print axioms same_problem_iff_whole_problem_equality
#print axioms same_problem_identifies_optimized_family_sigma
#print axioms same_problem_forces_seed_and_alpha
#print axioms acceptance_rejects_any_alternate_specialization
#print axioms repaired_acceptance_eta
#print axioms acceptance_factorization_requires_same_problem
#print axioms false_acceptance_membership_is_repaired_event
#print axioms failure_event_has_no_problem_mismatch_component
#print axioms repaired_event_accounting_receipt
#print axioms concrete_acceptance_uses_honest_specialization
#print axioms concrete_seed2_rejected_by_generic_whole_problem_attack
#print axioms fourteen_capstone_fields_still_reconstruct
#print axioms repaired_exact_resource_and_budget_receipt
#print axioms f97_nonterminal_same_execution_unaffected
#print axioms repaired_alias_and_forest_control
#print axioms batch68_history_preserved_with_repair

end
end Nock.RedTeam.Batch69
