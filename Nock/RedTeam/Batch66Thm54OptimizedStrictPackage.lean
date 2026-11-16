import Nock.NockVMROM.Thm54.OptimizedStrictPackageConcrete

/-!
The optimized compute and memory realization layers are substantive and
same-assignment on their own `PlusIOSegmentedFamily`.  In particular,
its `completeS7` field is a cardinality theorem for arbitrary environments; it has no
acceptance-outside-event-to-`GenuineTargetAt` conclusion.

This is a statement-shape finding about the proposed optimized strict package, not a verdict on the
paper construction and not a repair of production.
-/

namespace Nock.RedTeam.Batch66

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.StrictPackage
open Nock.NockVMROM.Thm54.RawSemanticAssembly
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedStrictPackage

noncomputable section

open ConcreteStrictPackage

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-! ## Exact statement-shape inventory -/

/-- Exhaustive eta receipt: the replacement statement has exactly these six projections. -/
theorem optimized_capstone_reconstructs_from_six_fields
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} {P : OptimizedStrictNockVMROMPackage F K hOrb}
    (S : OptimizedStrictThm54Statement P) :
    S =
      { sameExecution := S.sameExecution
        structuralResiduals := S.structuralResiduals
        optimizedChips := S.optimizedChips
        exactResources := S.exactResources
        sharedForestAxis := S.sharedForestAxis
        completeS7 := S.completeS7 } := by
  cases S
  rfl

theorem historical_capstone_reconstructs_from_thirteen_fields
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} {P : StrictNockVMROMPackage F K hOrb q Λ}
    (S : StrictThm54Statement P) :
    S =
      { structural := S.structural
        named_raps := S.named_raps
        comp_language := S.comp_language
        mem_language := S.mem_language
        shared_io := S.shared_io
        perfect_completeness := S.perfect_completeness
        containment := S.containment
        walk_bounds := S.walk_bounds
        fixed_field_soundness := S.fixed_field_soundness
        fixed_field_bits := S.fixed_field_bits
        fingerprint := S.fingerprint
        chip_shape := S.chip_shape
        row_budgets := S.row_budgets } := by
  cases S
  rfl

theorem historical_nock_bearing_projection
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} {P : StrictNockVMROMPackage F K hOrb q Λ}
    (S : StrictThm54Statement P) :
    Language
        (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
        (stmtOfExact P.objects.cfg P.objects.exec) ∧
      IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs ∧
      (∀ (ω : JointCoins K) (lmb : K), P.strategy.Accepts ω lmb →
        ω ∉ FailureUnion P.strategy P.census lmb →
        GenuineTargetAt P.strategy q Λ ω lmb) ∧
      (P.computeWalkBadRatio ≤ P.computeWalkBound ∧
        P.memoryWalkBadRatio ≤ P.memoryWalkBound) ∧
      (P.compRAP.H.card = P.objects.cfg.compRows ∧
        P.memRAP.H.card =
          RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec) :=
  ⟨S.perfect_completeness, S.shared_io, S.containment, S.walk_bounds, S.row_budgets⟩

/-- The replacement's structural residual is definitionally only this six-clause sub-bundle. -/
theorem optimized_structural_residual_inventory
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedStrictNockVMROMPackage F K hOrb) :
    P.OptimizedStrictStructuralResiduals ↔
      (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
        ActiveFingerprintChecksAt z P.commitment
          (TemplateRawJointSoundness.specializedProblem
            P.verifier.raw.timestamp z hz α lmb).exec) ∧
      (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
        RawSemanticAssembly.ExecTreeShapeMatchesAt P.commitment
          (TemplateRawJointSoundness.specializedProblem
            P.verifier.raw.timestamp z hz α lmb).exec) ∧
      (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
        RawSemanticAssembly.RowFrameChecksAt z P.commitment
          (TemplateRawJointSoundness.specializedProblem
            P.verifier.raw.timestamp z hz α lmb).exec) ∧
      (∀ s ∈ computeSkeletonRows P.commitment.skeleton,
        ServedLookupBridge.SkeletonSlotSemantics s) ∧
      RowLayout.RecordCountBalanced P.objects.exec ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy P.commitment.skeleton P.Λ :=
  Iff.rfl

/-! ## Same-assignment scope and the unconsumed transport -/

/-- Compute and memory realizations really are indexed by one sampled assignment on the family
side; this is the strongest true same-object reading of the optimized realization layer. -/
theorem family_side_assignment_is_shared
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedStrictNockVMROMPackage F K hOrb)
    (hax : FormRAxisBound P.sampled P.basis)
    (hbasis : FormRBasis P.basis)
    (hwidth : FormRWidth F) :
    P.sampled.sampled.records.requests =
        P.family.problem.exec.derivedRequestIO ∧
      P.sampled.sampled.records.responses =
        P.family.problem.exec.derivedResponseIO ∧
      OptimizedComputeRealizationAt P.sampled P.computeObligations P.computeNodes P.basis
        P.computeChallenge P.computePublic P.orbit ∧
      OptimizedMemoryRealizationAt P.sampled P.memoryProduction P.memoryNodes P.basis
        P.memoryChallenge P.memoryPublic P.orbit :=
  ⟨P.sampled.requests_eq, P.sampled.responses_eq,
    P.computeRealization hax hbasis hwidth, P.memoryRealization⟩

/-- At the replacement capstone, the family-to-`objects` link is only co-listed as configuration
equality and dependent execution `HEq`.  No request/response, row, RAP, or semantic transport appears
in this projection's conclusion. -/
theorem capstone_family_objects_link_is_only_cfg_exec
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} {P : OptimizedStrictNockVMROMPackage F K hOrb}
    (S : OptimizedStrictThm54Statement P) :
    P.family.problem.cfg = P.objects.cfg ∧
      HEq P.family.problem.exec P.objects.exec :=
  S.sameExecution

theorem derived_io_of_heq
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {c₁ c₂ : ExactConfig F K} {e₁ : ExactExecution c₁} {e₂ : ExactExecution c₂}
    (h : c₁ = c₂) (he : HEq e₁ e₂) :
    e₁.derivedRequestIO = e₂.derivedRequestIO ∧ e₁.derivedResponseIO = e₂.derivedResponseIO := by
  subst h
  cases he
  exact ⟨rfl, rfl⟩

/-- The package data are nevertheless sufficient to derive the missing record transport:
`family_cfg` and `family_exec` identify the dependent execution sigma-pairs, and both record lists
meet at the derived-IO projections.  This bridge is true, but it is not a field or a consumed
subtheorem of `optimizedStrictNockVMROM_of_package`. -/
theorem package_data_derives_objects_shared_io
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedStrictNockVMROMPackage F K hOrb) :
    P.sampled.sampled.records.requests = P.objects.reqRecs ∧
      P.sampled.sampled.records.responses = P.objects.respRecs ∧
      IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs := by
  have hsigma :
      (⟨P.family.problem.cfg, P.family.problem.exec⟩ :
          Σ cfg : ExactConfig F K, ExactExecution cfg) =
        ⟨P.objects.cfg, P.objects.exec⟩ :=
    Sigma.ext P.family_cfg P.family_exec
  have hreqDerived :
      P.family.problem.exec.derivedRequestIO = P.objects.exec.derivedRequestIO :=
    (derived_io_of_heq P.family_cfg P.family_exec).1
  have hrespDerived :
      P.family.problem.exec.derivedResponseIO = P.objects.exec.derivedResponseIO :=
    (derived_io_of_heq P.family_cfg P.family_exec).2
  have hk : P.family.problem.cfg.Ksz = P.objects.cfg.Ksz :=
    congrArg ExactConfig.Ksz P.family_cfg
  have hreq : P.sampled.sampled.records.requests = P.objects.reqRecs := by
    rw [P.sampled.requests_eq, P.objects.req_eq_derived, hreqDerived]
  have hresp : P.sampled.sampled.records.responses = P.objects.respRecs := by
    rw [P.sampled.responses_eq, P.objects.resp_eq_derived, hrespDerived]
  refine ⟨hreq, hresp, ?_⟩
  rw [P.objects.req_eq_derived, P.objects.resp_eq_derived,
    ← hreqDerived, ← hrespDerived, ← hk]
  exact P.sampled.lio

/-- The family node-image counts can likewise be transported to `objects.cfg`. -/
theorem package_data_derives_objects_node_counts
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedStrictNockVMROMPackage F K hOrb) :
    (rowNodeSet P.computeNodes).card = P.objects.cfg.compRows ∧
      (rowNodeSet P.memoryNodes).card = P.objects.cfg.memRows := by
  constructor
  · calc
      (rowNodeSet P.computeNodes).card = P.family.problem.cfg.compRows :=
        P.exact_row_domains.1
      _ = P.objects.cfg.compRows := congrArg ExactConfig.compRows P.family_cfg
  · calc
      (rowNodeSet P.memoryNodes).card = P.family.problem.cfg.memRows :=
        P.exact_row_domains.2
      _ = P.objects.cfg.memRows := congrArg ExactConfig.memRows P.family_cfg

/-! ## Event linkage -/

/-- Exact projection of `completeS7`: it is a cardinality statement over caller-supplied
environments.  Its conclusion contains neither verifier acceptance nor `GenuineTargetAt`. -/
theorem completeS7_is_cardinality_only
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} {P : OptimizedStrictNockVMROMPackage F K hOrb}
    (S : OptimizedStrictThm54Statement P)
    {N M : ℕ} (topologyBound axisWorkload : ℕ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload
          (P.strategy.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload
          (ProductionAxisStructureVerifier.committedTemplate P.strategy.verifier z hz) ≤
            axisWorkload)
    (lmb : K) (ioWork : ℕ)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F) :
    (OptimizedProductionFailureEvent P.strategy P.census lmb computeEnvK
      computeWalkEnv computeEnvF memoryEnvK memoryFamilies).card ≤
      optimizedTrimmedProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (workload P.strategy P.Λ topologyBound axisWorkload) ioWork N M :=
  S.completeS7 lmb topologyBound axisWorkload htopology haxis ioWork computeEnvK computeWalkEnv
    computeEnvF memoryEnvK memoryFamilies

/-- The tuple cardinality itself is exact and independently reproducible. -/
theorem optimized_tuple_cardinality_exact
    (K F : Type) [Fintype K] [Fintype F] :
    Fintype.card (OptimizedProductionChallengeTuple K F) = Fintype.card K ^ 11 :=
  card_optimizedProductionChallengeTuple K F

/-! ## Concrete scope and conditional reverse boundary -/

/-- The proposed replacement capstone is concretely inhabited over the singleton-compute,
five-memory-row fixture. -/
theorem concrete_replacement_capstone_inhabited
    (hbasis : FormRBasis ConcreteStrictPackage.basis73) :
    OptimizedStrictThm54Statement
      OptimizedStrictPackage.Concrete.concreteOptimizedStrictPackage :=
  OptimizedStrictPackage.Concrete.concrete_strict_capstone hbasis

/-- The concrete compute fixture has one row. -/
theorem concrete_compute_rows_are_singleton :
    OptimizedStrictPackage.Concrete.concreteOptimizedStrictPackage.family.problem.cfg.compRows = 1 :=
  Nock.RedTeam.Batch62.concrete_compRows_eq_one

/-- The only canonical compute row is terminal, so its `isLast` base coordinate is one. -/
theorem concrete_canonical_row_is_terminal :
    let P := OptimizedStrictPackage.Concrete.concreteOptimizedStrictPackage
    let Q := correctedCanonicalFinalTrace P.sampled P.family.problem.cfg.compRows_pos
      P.computeNodes P.basis P.computeChallenge P.computePublic P.orbit
    let env := gatherCorrectedFinalTypedEnv P.basis
      (envOfTrace Q P.orbit.ω (P.computeNodes ⟨0, P.family.problem.cfg.compRows_pos⟩)
        P.computeChallenge P.computePublic)
    env.baseTrace 12 = 1 := by
  dsimp only
  let P := OptimizedStrictPackage.Concrete.concreteOptimizedStrictPackage
  have h := canonical_gather_base_current P.sampled P.family.problem.cfg.compRows_pos
    P.computeNodes P.computeNodes_injective P.basis P.computeChallenge P.computePublic P.orbit
    (⟨0, P.family.problem.cfg.compRows_pos⟩ : Fin P.family.problem.cfg.compRows) (12 : Fin 13)
  have hrows : P.family.problem.cfg.compRows = 1 :=
    Nock.RedTeam.Batch62.concrete_compRows_eq_one
  have hlast : 0 = P.family.problem.cfg.compRows - 1 := by omega
  simpa [OptimizedComputeFinalTrace.finalBaseCell, hlast] using h

/-- Therefore the replacement's arbitrary-trace decoder premise `baseTrace 12 = 0` is unavailable
on the concrete canonical singleton row.  This does not refute nonterminal decoding; it limits the
concrete witness to forward satisfaction at that boundary. -/
theorem concrete_canonical_row_does_not_inhabit_decode_premise :
    let P := OptimizedStrictPackage.Concrete.concreteOptimizedStrictPackage
    let Q := correctedCanonicalFinalTrace P.sampled P.family.problem.cfg.compRows_pos
      P.computeNodes P.basis P.computeChallenge P.computePublic P.orbit
    let env := gatherCorrectedFinalTypedEnv P.basis
      (envOfTrace Q P.orbit.ω (P.computeNodes ⟨0, P.family.problem.cfg.compRows_pos⟩)
        P.computeChallenge P.computePublic)
    env.baseTrace 12 ≠ 0 := by
  dsimp only
  rw [concrete_canonical_row_is_terminal]
  exact one_ne_zero

/-- Memory forward satisfaction, all-92 conditional recovery, aggregate forest, axis, and sampled
IO are genuinely present on one family-side assignment. -/
theorem concrete_memory_realization_is_substantive :
    let P := OptimizedStrictPackage.Concrete.concreteOptimizedStrictPackage
    OptimizedMemoryRealizationAt P.sampled P.memoryProduction P.memoryNodes P.basis
        P.memoryChallenge P.memoryPublic P.orbit ∧
      P.OptimizedSharedMemoryConnective :=
  ⟨OptimizedStrictPackage.Concrete.concreteOptimizedStrictPackage.memoryRealization,
    OptimizedStrictPackage.Concrete.concreteOptimizedStrictPackage.shared_memory_connective⟩

theorem paper_alias_remains_historical_forest :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  rfl

#print OptimizedStrictNockVMROMPackage
#print OptimizedStrictThm54Statement
#print StrictThm54Statement

#print axioms optimizedStrictNockVMROM_of_package
#print axioms OptimizedStrictPackage.Concrete.concrete_strict_capstone
#print axioms correctedCanonicalFinalTrace_satisfies
#print axioms Nock.RedTeam.Batch65.actual_production_recovers_all_92_sources
#print axioms optimizedProductionFailureEvent_card_le
#print axioms normalized_card_bound_eq_separate_denominators
#print axioms OptimizedStrictPackage.Concrete.concrete_compute_malformed_rejection
#print axioms OptimizedStrictPackage.Concrete.concrete_memory_malformed_rejection
#print axioms optimized_capstone_reconstructs_from_six_fields
#print axioms historical_nock_bearing_projection
#print axioms family_side_assignment_is_shared
#print axioms package_data_derives_objects_shared_io
#print axioms package_data_derives_objects_node_counts
#print axioms completeS7_is_cardinality_only
#print axioms concrete_replacement_capstone_inhabited
#print axioms concrete_canonical_row_is_terminal
#print axioms concrete_canonical_row_does_not_inhabit_decode_premise
#print axioms concrete_memory_realization_is_substantive
#print axioms paper_alias_remains_historical_forest

end
end Nock.RedTeam.Batch66
