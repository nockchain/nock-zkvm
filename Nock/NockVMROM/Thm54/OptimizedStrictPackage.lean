import Nock.NockVMROM.Thm54.StrictPackage
import Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
import Nock.NockVMROM.Thm54.OptimizedComputeCollisionConcrete
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
import Nock.RedTeam.Batch65Thm54CertifiedOptimizedMemory
import Nock.NockVMROM.Thm54.PaperResourceCounts
import Nock.NockVMROM.Thm54.HostileRecordLists
import Nock.NockVMROM.Thm54.ComputeWalkRootEvents
import Nock.NockVMROM.Thm54.WalkTilingEvents
import Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
import Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents

/-!
# Theorem 5.4 optimized strict package

It threads one
execution through one sampled-IO assignment, the corrected `199/98` compute RAP, and the repaired
`196/104` memory RAP.

-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedStrictPackage

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open MonolithicRAP
open RawSemanticAssembly SemanticStrategy StrictCommitment
open TemplateRawJointSoundness
open ServedLookupBridge
open CoordinateBasis CoordinateCompiler
open StrictExtension
open OptimizedComputeCorrectedFinal
open OptimizedComputeGateBasis
open OptimizedComputeFinalTrace
open OptimizedComputeCanonicalSatisfaction
open OptimizedComputeSemanticRealization
open OptimizedComputeCollisionBound
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open OptimizedMemoryCanonicalTrace
open OptimizedMemoryCanonicalSatisfaction
open OptimizedMemorySameExecution
open OptimizedMemorySemanticRealization
open OptimizedMemoryCollisionAccounting
open ProductionP8Containment
open ProductionAxisStructureVerifier TemplateAxisCounting

noncomputable section

/-! ## Exact optimized realization surfaces -/

/-- Same-parameter compute realization. The canonical witness and the arbitrary-trace language
equivalence mention exactly this assignment's row count, nodes, basis, coordinates, and orbit. -/
structure OptimizedComputeRealizationAt
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h) : Prop where
  rows_pos : 0 < R.problem.cfg.compRows
  nodes_injective : Function.Injective nodes
  adjacent_orbit :
    ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i
  challenge_pins : ExactFinalChallengeCoordinates b A chalVal
  public_pins : ExactFinalPublicCoordinates b R rows_pos pubVal
  /-- The post-challenge public `requests` (extension public role `2`) is the sampled IO terminal
. -/
  requests_pins : ExactFinalRequestsCoordinate b A pubVal
  /-- The honest execution's compute line starts at `1` — the value
  the W6.1 stage-2A gate `finalLnInit = isFirst · (ln_prev − 1)` pins; a completeness obligation
  the paper's `V_comp` (`:1728-1742`) does not impose. -/
  line_origin : ExactFinalLineOrigin R rows_pos
  canonical_satisfies :
    RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP rows_pos nodes b chalVal pubVal orbit)
      (correctedCanonicalFinalTrace A rows_pos nodes b chalVal pubVal orbit)
  arbitrary_trace_source_iff :
    ∀ P : Fin
        (ProductionNamedComputeRAP rows_pos nodes b chalVal pubVal orbit).rap.w → F[X],
      RAP.SatisfiesWithPreprocessing
          (ProductionNamedComputeRAP rows_pos nodes b chalVal pubVal orbit) P ↔
        CorrectedFinalComputeSourceLanguage rows_pos nodes b chalVal pubVal orbit P
  conditional_row_decode :
    ∀ (P : Fin
          (ProductionNamedComputeRAP rows_pos nodes b chalVal pubVal orbit).rap.w → F[X])
      (_hSat : RAP.SatisfiesWithPreprocessing
        (ProductionNamedComputeRAP rows_pos nodes b chalVal pubVal orbit) P)
      (x : F) (_hx : x ∈ rowNodeSet nodes),
      let envF := envOfTrace P orbit.ω x chalVal pubVal
      let env := gatherCorrectedFinalTypedEnv b envF
      env.baseTrace 12 = 0 →
      CorrectedDecodedTransitionSources env

/-- Same-parameter memory realization. Forward source/final satisfaction and every root-indexed
axis consequence are tied to `P : MemoryProductionAssignment A`. -/
structure OptimizedMemoryRealizationAt
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    {execA : ExactExecution R.problem.cfg}
    (P : MemoryProductionAssignment A execA)
    (nodes : Fin R.problem.cfg.memRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h) : Prop where
  nodes_injective : Function.Injective nodes
  coordinate_pins : ExactMemoryCoordinatePins A b chalVal pubVal
  orbit_aligned : MemoryOrbitAligned nodes orbit
  denominators_safe : MemoryDenominatorsSafe A
  two_ne_zero : (2 : K) ≠ 0
  /-- Canonical source/final RAP satisfaction is `canonicalMemoryRealization` and takes
  later-seed zeros (`LaterSeedZeros` / Relaxis remaining join).  Not a field of this
  structure: the capstone is hyp-free and completeness at `0 < i < kMem` is not. -/
  axis_batching_sound :
    ∀ (root : Fin R.problem.cfg.kMem) (e : ℕ),
      e ∈ AxisBridge.readExps (exactAxisTree R.problem.cfg execA root) →
      e ∈ AxisBridge.verifyExps (exactAxisTree R.problem.cfg execA root) →
      AxisBatching.MTree.vaxis e (exactAxisTree R.problem.cfg execA root) =
        AxisBatching.MTree.Relaxis e (exactAxisTree R.problem.cfg execA root)
  arbitrary_final_iff_source :
    ∀ Q : Fin
        (namedFinalMemoryRAP R.problem.cfg.memRows_pos nodes b chalVal pubVal orbit R.problem.cfg.kMem).rap.w → F[X],
      RAP.SatisfiesWithPreprocessing
          (namedFinalMemoryRAP R.problem.cfg.memRows_pos nodes b chalVal pubVal orbit R.problem.cfg.kMem) Q ↔
        RAP.SatisfiesWithPreprocessing
          (namedSourceMemoryRAP R.problem.cfg.memRows_pos nodes b chalVal pubVal orbit R.problem.cfg.kMem)
          (RAPPadding.projectTrace
            (namedSourceMemoryRAP R.problem.cfg.memRows_pos nodes b chalVal pubVal orbit R.problem.cfg.kMem).rap
            (RAPPadding.firstRoundExtra
              (namedSourceMemoryRAP R.problem.cfg.memRows_pos nodes b chalVal pubVal orbit R.problem.cfg.kMem).rap
              (namedSourceMemoryRAP R.problem.cfg.memRows_pos nodes b chalVal pubVal orbit R.problem.cfg.kMem).rounds_pos
              (RAPPadding.memoryResidualColumns 3)) Q)
  /-- W2 stage 2: the committed memory language is the paper base + paper `𝕂` gates. -/
  conditional_all_92_sources :
    ∀ (envF : Env F),
      (∀ g ∈ baseTransitionGates b, g.eval envF = 0) →
      (∀ g ∈ mixedTransitionGates (F := F) (K := K) b,
        g.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) envF = 0) →
      (∀ g ∈ baseTransitionGates b, g.eval envF = 0) ∧
        (∀ g ∈ mixedTransitionGates (F := F) (K := K) b,
          g.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) envF = 0)

def optimizedComputeRealization
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (hstep : ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hchal : ExactFinalChallengeCoordinates b A chalVal)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal)
    (hreq : ExactFinalRequestsCoordinate b A pubVal)
    (hln : ExactFinalLineOrigin R hn)
    (hord : 2 ≤ R.problem.cfg.compRows →
      R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha)
    (hax : FormRAxisBound A b)
    (hbasis : FormRBasis b)
    (hwidth : FormRWidth F) :
    OptimizedComputeRealizationAt A hA nodes b chalVal pubVal orbit where
  rows_pos := hn
  nodes_injective := hnodes
  adjacent_orbit := hstep
  challenge_pins := hchal
  public_pins := hpub
  requests_pins := hreq
  line_origin := hln
  canonical_satisfies :=
    correctedCanonicalFinalTrace_satisfies
      A hA hn nodes hnodes b chalVal pubVal orbit hstep hchal hpub hreq hln hord hax hbasis hwidth
  arbitrary_trace_source_iff :=
    productionNamedComputeRAP_satisfies_iff_sourceLanguage hn nodes b chalVal pubVal orbit
  conditional_row_decode := by
    intro Q hSat x hx
    have hsource :=
      (productionNamedComputeRAP_satisfies_iff_sourceLanguage
        hn nodes b chalVal pubVal orbit Q).1 hSat
    dsimp only
    intro hlast
    exact corrected_conditional_transition_soundness (hsource.2 x hx) hlast

def optimizedMemoryRealization
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    {execA : ExactExecution R.problem.cfg}
    (P : MemoryProductionAssignment A execA)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (halign : MemoryOrbitAligned nodes orbit)
    (hsafe : MemoryDenominatorsSafe A)
    (h2 : (2 : K) ≠ 0) :
    OptimizedMemoryRealizationAt A P nodes b chalVal pubVal orbit where
  nodes_injective := hnodes
  coordinate_pins := pins
  orbit_aligned := halign
  denominators_safe := hsafe
  two_ne_zero := h2
  axis_batching_sound := fun root e hread hverify =>
    MemoryProductionAssignment.axis_eq_relaxis_of_used h2 P root e hread hverify
  arbitrary_final_iff_source := final_satisfies_iff_source
    R.problem.cfg.memRows_pos nodes b chalVal pubVal orbit R.problem.cfg.kMem
  conditional_all_92_sources := fun _envF hbase hmix => ⟨hbase, hmix⟩

/-! ## One execution, one assignment, two optimized chips -/

/-- `computeObligations` and
`memoryProduction` are indexed by the very same `sampled` field. `family_problem` is the sole
transport from that assignment's problem to `objects`; there is no independently chosen execution. -/
structure OptimizedStrictNockVMROMPackage
    (F K : Type) [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    (hOrb : ℕ) where
  objects : StrictThreadedObjects F K
  verifier : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K)
  commitment : SkeletonCommitment
  claim_eq : commitment.skeleton.publicClaim = verifier.raw.claim
  scan : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    ActiveFingerprintChecksAt z commitment
      (specializedProblem verifier.raw.timestamp z hz α lmb).exec
  shapeMatch : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    ExecTreeShapeMatchesAt commitment
      (specializedProblem verifier.raw.timestamp z hz α lmb).exec
  rowFrame : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    RowFrameChecksAt z commitment
      (specializedProblem verifier.raw.timestamp z hz α lmb).exec
  slotSemantics : ∀ s ∈ computeSkeletonRows commitment.skeleton,
    SkeletonSlotSemantics s
  recordCountBalance : RowLayout.RecordCountBalanced objects.exec
  Λ : ℕ
  census : EdgeComparisonCensus.CombinedSkeletonCensus K commitment.skeleton Λ
  sizeWindowBound :
    SizeWindowCounting.SizeWindowNounsBoundedBy commitment.skeleton Λ
  family : PlusIOSegmentedFamily F K
  family_cfg : family.problem.cfg = objects.cfg
  family_exec : HEq family.problem.exec objects.exec
  sampled : SampledIOSameExecutionAssignment family (ringChar K)
  computeObligations : sampled.ComputeSampledObligations
  /-- The a-bearing (Form R) view of the family's memory rows; the served memory trace, exact
  axis tree and axis validity are stated on it (`memoryProduction.exec_encode`, 28th). -/
  memoryExecA : ExactExecution family.problem.cfg
  memoryProduction : MemoryProductionAssignment sampled memoryExecA
  basis : Basis (Fin 3) F K
  orbit : StrictOrbitDomain F 3 hOrb
  computeNodes : Fin family.problem.cfg.compRows → F
  computeNodes_injective : Function.Injective computeNodes
  computeAdjacentOrbit :
    ∀ (i : Fin family.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < family.problem.cfg.compRows),
      computeNodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * computeNodes i
  computeChallenge : ℕ → F
  computePublic : ℕ → F
  computeChallengePins :
    ExactFinalChallengeCoordinates basis sampled computeChallenge
  computePublicPins :
    ExactFinalPublicCoordinates basis family family.problem.cfg.compRows_pos computePublic
  /-- `requests` = the sampled IO terminal at compute base publics `6..8`. -/
  computeRequestsPins : ExactFinalRequestsCoordinate basis sampled computePublic
  /-- The honest compute line starts at `1`: `ln_prev(0) = 1` of the package's own execution
.  This is the honest prover's
  line-number origin — the paper's "Prover builds columns `ln`" — which the deployed chip
  now checks (`OptimizedComputeCorrectedFinal.finalLnInit`) and the paper's `V_comp`
  (`:1728-1742`) does not; the generator supplies it as `α ^ 0` (`Gen.lean` `renderOp*Row`). -/
  computeLineOrigin : ExactFinalLineOrigin family family.problem.cfg.compRows_pos
  /-- Vacuous on one-row fixtures; discharged from `compilerWalkCoin` at the
  compiler and from the fixture coin elsewhere. Not a field of `E`. -/
  computeWalkOrder :
    2 ≤ family.problem.cfg.compRows →
      family.problem.cfg.compRows ≤ orderOf family.computeWalkAlpha
  memoryNodes : Fin family.problem.cfg.memRows → F
  memoryNodes_injective : Function.Injective memoryNodes
  memoryChallenge : ℕ → F
  memoryPublic : ℕ → F
  memoryCoordinatePins :
    ExactMemoryCoordinatePins sampled basis memoryChallenge memoryPublic
  memoryOrbitAligned : MemoryOrbitAligned memoryNodes orbit
  memoryDenominatorsSafe : MemoryDenominatorsSafe sampled
  two_ne_zero : (2 : K) ≠ 0
  /-- Honest `PairedRecordLayout` of the family's execution.  Not a
  field of `E`; filled at package construction
  from `genBuildableOfProgram_pairedRecordLayout` or a fixture listing. -/
  pairedRecordLayout : RowLayout.PairedRecordLayout family.problem.exec
  /-- Vacuous on one-row fixtures; discharged from `compilerWalkCoin` at the
  compiler (`hmemCap`) and from the fixture coin elsewhere. Not a field of `E`
  and not a `nockCompiles_zmod` hypothesis. -/
  memoryWalkOrder :
    2 ≤ family.problem.cfg.memRows →
      family.problem.cfg.memRows ≤ orderOf family.memoryWalkAlpha

namespace OptimizedStrictNockVMROMPackage

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedStrictNockVMROMPackage F K hOrb)

def strategy : ProductionStrategy F K :=
  productionStrategy_of_scan P.verifier P.commitment P.claim_eq
    P.shapeMatch P.rowFrame P.scan

@[simp] theorem strategy_skeleton : P.strategy.skeleton = P.commitment.skeleton := rfl

/-- The package strategy binds at every specialization: it is `ProductionStrategy.ofBare` of the
scan-derived `BareSemanticSupport`. -/
theorem strategy_bindsAll : P.strategy.BindsAll :=
  productionStrategy_of_scan_bindsAll P.verifier P.commitment P.claim_eq
    P.shapeMatch P.rowFrame P.scan

def OptimizedStrictStructuralResiduals : Prop :=
  (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      ActiveFingerprintChecksAt z P.commitment
        (specializedProblem P.verifier.raw.timestamp z hz α lmb).exec) ∧
    (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      ExecTreeShapeMatchesAt P.commitment
        (specializedProblem P.verifier.raw.timestamp z hz α lmb).exec) ∧
    (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      RowFrameChecksAt z P.commitment
        (specializedProblem P.verifier.raw.timestamp z hz α lmb).exec) ∧
    (∀ s ∈ computeSkeletonRows P.commitment.skeleton, SkeletonSlotSemantics s) ∧
    RowLayout.RecordCountBalanced P.objects.exec ∧
    SizeWindowCounting.SizeWindowNounsBoundedBy P.commitment.skeleton P.Λ

theorem structural_residuals : OptimizedStrictStructuralResiduals P :=
  ⟨P.scan, P.shapeMatch, P.rowFrame, P.slotSemantics,
    P.recordCountBalance, P.sizeWindowBound⟩

/-- The corrected compute realization is derived from the package's own assignment and parameters.
Leaf-local Form R cover of this package's honest axis coordinates; not `∀ L : F`.
-/
def computeRealization_of_leafCover
    (hax : FormRAxisBound P.sampled P.basis)
    (hbasis : FormRBasis P.basis)
    (hwidth : FormRWidth F) :
    OptimizedComputeRealizationAt P.sampled P.computeObligations P.computeNodes P.basis
      P.computeChallenge P.computePublic P.orbit :=
  optimizedComputeRealization P.sampled P.computeObligations
    P.family.problem.cfg.compRows_pos P.computeNodes P.computeNodes_injective P.basis
    P.computeChallenge P.computePublic P.orbit P.computeAdjacentOrbit
    P.computeChallengePins P.computePublicPins P.computeRequestsPins P.computeLineOrigin
    P.computeWalkOrder hax hbasis hwidth

/-- The corrected compute realization is derived from the package's own assignment and parameters.
-/
def computeRealization
    (hax : FormRAxisBound P.sampled P.basis)
    (hbasis : FormRBasis P.basis)
    (hwidth : FormRWidth F) :
    OptimizedComputeRealizationAt P.sampled P.computeObligations P.computeNodes P.basis
      P.computeChallenge P.computePublic P.orbit :=
  P.computeRealization_of_leafCover hax hbasis hwidth

/-- Honest-side completeness hyps for the paper aggregator (`canonicalMemoryRealization`).
Discharged from the package's PRL field, `memoryWalkOrder`, `sampled.honestVer`,
and `sampled.interPoleHitGood`; not a capstone hypothesis. -/
def MemoryCompletenessHyps : Prop :=
  RowLayout.PairedRecordLayout P.family.problem.exec ∧
    (2 ≤ P.family.problem.cfg.memRows →
      P.family.problem.cfg.memRows ≤ orderOf P.family.memoryWalkAlpha) ∧
    ∀ i : Fin P.family.problem.cfg.memRows,
      MemoryPaperFactorization.poleSourceMixed.eval
          (canonicalGatheredEnv P.sampled P.memoryNodes P.basis
            P.memoryChallenge P.memoryPublic P.orbit i)
          (canonicalPhysicalEnv P.sampled P.memoryNodes P.basis
            P.memoryChallenge P.memoryPublic P.orbit i) ≠ 0 ∨
        MemoryPaperFactorization.aggregatorSign
          (P.family.problem.exec.memoryPubAt i).st = (0 : K)

theorem memoryCompletenessHyps
    (hC : P.family.problem.exec.CprimeCoherent) :
    P.MemoryCompletenessHyps :=
  ⟨P.pairedRecordLayout, P.memoryWalkOrder,
    MemoryPaperFactorization.hdenAll_of_interPoleHitGood P.sampled
      P.memoryNodes P.memoryNodes_injective P.basis P.memoryChallenge P.memoryPublic
      P.orbit P.memoryCoordinatePins P.sampled.honestVer hC⟩

/-- The repaired memory realization is derived from that same assignment. -/
def memoryRealization :
    OptimizedMemoryRealizationAt P.sampled P.memoryProduction P.memoryNodes P.basis
      P.memoryChallenge P.memoryPublic P.orbit :=
  optimizedMemoryRealization P.sampled P.memoryProduction P.memoryNodes
    P.memoryNodes_injective P.basis P.memoryChallenge P.memoryPublic P.orbit
    P.memoryCoordinatePins P.memoryOrbitAligned P.memoryDenominatorsSafe
    P.two_ne_zero


theorem realization_surface_of_leafCover
    (hax : FormRAxisBound P.sampled P.basis)
    (hbasis : FormRBasis P.basis)
    (hwidth : FormRWidth F) :
    OptimizedComputeRealizationAt P.sampled P.computeObligations P.computeNodes P.basis
        P.computeChallenge P.computePublic P.orbit ∧
      OptimizedMemoryRealizationAt P.sampled P.memoryProduction P.memoryNodes P.basis
        P.memoryChallenge P.memoryPublic P.orbit :=
  ⟨P.computeRealization_of_leafCover hax hbasis hwidth, P.memoryRealization⟩

theorem realization_surface_is_optimized
    (hax : FormRAxisBound P.sampled P.basis)
    (hbasis : FormRBasis P.basis)
    (hwidth : FormRWidth F) :
    OptimizedComputeRealizationAt P.sampled P.computeObligations P.computeNodes P.basis
        P.computeChallenge P.computePublic P.orbit ∧
      OptimizedMemoryRealizationAt P.sampled P.memoryProduction P.memoryNodes P.basis
        P.memoryChallenge P.memoryPublic P.orbit :=
  P.realization_surface_of_leafCover hax hbasis hwidth

/-- In particular, satisfying this theorem requires the concrete
canonical/conditional surfaces above and cannot be discharged by constructing a
`B29SemanticTemplate`. -/
theorem replacement_does_not_consume_B29SemanticTemplate
    (hax : FormRAxisBound P.sampled P.basis)
    (hbasis : FormRBasis P.basis)
    (hwidth : FormRWidth F) :
    OptimizedComputeRealizationAt P.sampled P.computeObligations P.computeNodes P.basis
        P.computeChallenge P.computePublic P.orbit ∧
      OptimizedMemoryRealizationAt P.sampled P.memoryProduction P.memoryNodes P.basis
        P.memoryChallenge P.memoryPublic P.orbit :=
  P.realization_surface_is_optimized hax hbasis hwidth

theorem compute_source_to_final_satisfaction
    (hax : FormRAxisBound P.sampled P.basis)
    (hbasis : FormRBasis P.basis)
    (hwidth : FormRWidth F)
    (Q : Fin
        (ProductionNamedComputeRAP P.family.problem.cfg.compRows_pos P.computeNodes P.basis
          P.computeChallenge P.computePublic P.orbit).rap.w → F[X])
    (hsource : CorrectedFinalComputeSourceLanguage P.family.problem.cfg.compRows_pos
      P.computeNodes P.basis P.computeChallenge P.computePublic P.orbit Q) :
    RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP P.family.problem.cfg.compRows_pos P.computeNodes P.basis
        P.computeChallenge P.computePublic P.orbit) Q :=
  ((P.computeRealization hax hbasis hwidth).arbitrary_trace_source_iff Q).2 hsource

theorem compute_final_satisfaction_to_source
    (hax : FormRAxisBound P.sampled P.basis)
    (hbasis : FormRBasis P.basis)
    (hwidth : FormRWidth F)
    (Q : Fin
        (ProductionNamedComputeRAP P.family.problem.cfg.compRows_pos P.computeNodes P.basis
          P.computeChallenge P.computePublic P.orbit).rap.w → F[X])
    (hSat : RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP P.family.problem.cfg.compRows_pos P.computeNodes P.basis
        P.computeChallenge P.computePublic P.orbit) Q) :
    CorrectedFinalComputeSourceLanguage P.family.problem.cfg.compRows_pos
      P.computeNodes P.basis P.computeChallenge P.computePublic P.orbit Q :=
  ((P.computeRealization hax hbasis hwidth).arbitrary_trace_source_iff Q).1 hSat

theorem memory_source_to_final_satisfaction
    (Q : Fin
        (namedFinalMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes P.basis
          P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem).rap.w → F[X])
    (hsource : RAP.SatisfiesWithPreprocessing
      (namedSourceMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes P.basis
        P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem)
      (RAPPadding.projectTrace
        (namedSourceMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes P.basis
          P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem).rap
        (RAPPadding.firstRoundExtra
          (namedSourceMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes P.basis
            P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem).rap
          (namedSourceMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes P.basis
            P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem).rounds_pos
          (RAPPadding.memoryResidualColumns 3)) Q)) :
    RAP.SatisfiesWithPreprocessing
      (namedFinalMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes P.basis
        P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem) Q :=
  (P.memoryRealization |>.arbitrary_final_iff_source Q).2 hsource

theorem memory_final_satisfaction_to_source
    (Q : Fin
        (namedFinalMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes P.basis
          P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem).rap.w → F[X])
    (hSat : RAP.SatisfiesWithPreprocessing
      (namedFinalMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes P.basis
        P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem) Q) :
    RAP.SatisfiesWithPreprocessing
      (namedSourceMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes P.basis
        P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem)
      (RAPPadding.projectTrace
        (namedSourceMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes P.basis
          P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem).rap
        (RAPPadding.firstRoundExtra
          (namedSourceMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes P.basis
            P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem).rap
          (namedSourceMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes P.basis
            P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem).rounds_pos
          (RAPPadding.memoryResidualColumns 3)) Q) :=
  (P.memoryRealization |>.arbitrary_final_iff_source Q).1 hSat

theorem compute_semantic_or_collision
    (hax : FormRAxisBound P.sampled P.basis)
    (hbasis : FormRBasis P.basis)
    (hwidth : FormRWidth F)
    (Q : Fin
        (ProductionNamedComputeRAP P.family.problem.cfg.compRows_pos P.computeNodes P.basis
          P.computeChallenge P.computePublic P.orbit).rap.w → F[X])
    (hSat : RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP P.family.problem.cfg.compRows_pos P.computeNodes P.basis
        P.computeChallenge P.computePublic P.orbit) Q)
    (x : F) (hx : x ∈ rowNodeSet P.computeNodes)
    (hnotLast :
      (gatherCorrectedFinalTypedEnv P.basis
        (envOfTrace Q P.orbit.ω x P.computeChallenge P.computePublic)).baseTrace 12 = 0) :
    let envF := envOfTrace Q P.orbit.ω x P.computeChallenge P.computePublic
    let env := gatherCorrectedFinalTypedEnv P.basis envF
    CorrectedDecodedTransitionSources env := by
  dsimp only
  exact (P.computeRealization hax hbasis hwidth).conditional_row_decode Q hSat x hx hnotLast

/-- W2 stage 2: RAP.Satisfies is the paper gate lists. -/
theorem memory_semantic_or_collision
    (envF : Env F)
    (hbase : ∀ g ∈ baseTransitionGates P.basis, g.eval envF = 0)
    (hmix : ∀ g ∈ mixedTransitionGates (F := F) (K := K) P.basis,
      g.eval (gatherEnv P.basis ((memorySourceTemplate P.basis).col0 3) envF) envF = 0) :
    (∀ g ∈ baseTransitionGates P.basis, g.eval envF = 0) ∧
      (∀ g ∈ mixedTransitionGates (F := F) (K := K) P.basis,
        g.eval (gatherEnv P.basis ((memorySourceTemplate P.basis).col0 3) envF) envF = 0) :=
  P.memoryRealization.conditional_all_92_sources envF hbase hmix

/-- **The all-row memory event consumed by the named reverse premise.**  Vacuous since W2
stage 3: the fold pin and the event are gone.  Previously stated as the implication from
the pin and `ExtensionMemoryCollisionGood` to row-wise `FoldCollisionExcluded`. -/
theorem memory_extension_event_to_fold_excluded
    [Fintype F] [DecidableEq F]
    (envK : Fin P.family.problem.cfg.memRows → Env K)
    (c : MemoryChallengeTuple K)
    (hgood : ExtensionMemoryCollisionGood envK c) :
    True :=
  foldCollisionExcluded_of_extension_good envK c hgood


theorem exact_chip_resources :
    let C := ProductionNamedComputeRAP P.family.problem.cfg.compRows_pos P.computeNodes
      P.basis P.computeChallenge P.computePublic P.orbit
    let M := namedFinalMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes
      P.basis P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem
    C.rap.w = 303 ∧ C.rap.s = 418 ∧ C.rap.d = 4 ∧ C.rap.k = 2 ∧
      M.rap.w = 205 ∧ M.rap.s = 156 ∧ M.rap.d = 4 ∧ M.rap.k = 1 := by
  dsimp only
  have hc := corrected_rap_fingerprint
    (n := P.family.problem.cfg.compRows) P.basis P.computeChallenge P.computePublic P.orbit
    (rowNodeSet P.computeNodes)
  have hm := finalMemoryRAP_fingerprint P.family.problem.cfg.memRows_pos P.memoryNodes
    P.basis P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
    hm.1, hm.2.1, hm.2.2.1, hm.2.2.2⟩

/-- Transition-versus-endpoint fingerprint: the corrected compute total is `87 + 40` since the
de-compression of the two `challenge36` column pins, the two
IO-accumulator anchors of the A-comp stage and the line-number origin
`isFirst · (ln_prev − 1)` of W6.1 stage 2A (`+e`), while the repaired memory
total is `89 + 24`: `88 + 24` since the `𝔽 → 𝕂` retyping of the four memory equality checks
, and `+1` on the transition side since A-mem-2, when the
response-denominator pin `OptimizedMemoryGateBasis.denominatorPinMixed`
exhausted the residual padding.  The compute degree-`4` transition count `87` is exactly as it
was; the memory one moved for the first time. -/
theorem exact_transition_fingerprints :
    let C := ProductionNamedComputeRAP P.family.problem.cfg.compRows_pos P.computeNodes
      P.basis P.computeChallenge P.computePublic P.orbit
    let M := namedFinalMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes
      P.basis P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem
    C.rap.s - 44 = 374 ∧ M.rap.s - 0 = 156 := by
  have h := P.exact_chip_resources
  dsimp only at h ⊢
  omega

/-- **Theorem 5.4's resource list in the paper's own shape.**

`Def:RAP` carries `(𝕂, e)` as a component of the tuple, recorded here as
`RAP.e`, and Theorem 5.4 states every resource of both chips as an affine function of that `e`:
`62·e+13` / `61·e+13` columns, `24·e+15` / `24·e+16` degree-`4` transition
gates, `2·e` / `2·e` degree-`1` gates, `e` / `2·e`
degree-`3` gates, and two / four equality checks.

This is the same content as `exact_chip_resources`, stated at the chip's own recorded degree
rather than at that degree's value; `Thm54Resources.compute_resources_iff` and
`Thm54Resources.memory_resources_iff` prove the two propositions equivalent. -/
theorem exact_chip_resources_paper :
    let C := ProductionNamedComputeRAP P.family.problem.cfg.compRows_pos P.computeNodes
      P.basis P.computeChallenge P.computePublic P.orbit
    let M := namedFinalMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes
      P.basis P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem
    (C.rap.e = Thm54Resources.deployedExtensionDegree ∧
        C.rap.w = Thm54Resources.computeColumns C.rap.e ∧
        C.rap.s = Thm54Resources.computeConstraints C.rap.e ∧
        C.rap.d = Thm54Resources.maxConstraintDegree ∧
        C.rap.k = Thm54Resources.computeCommittedRounds) ∧
      (M.rap.e = Thm54Resources.deployedExtensionDegree ∧
        M.rap.w = Thm54Resources.memoryColumns M.rap.e ∧
        M.rap.s = Thm54Resources.memoryConstraints M.rap.e ∧
        M.rap.d = Thm54Resources.maxConstraintDegree ∧
        M.rap.k = Thm54Resources.memoryCommittedRounds) := by
  dsimp only
  have hc := corrected_rap_fingerprint
    (n := P.family.problem.cfg.compRows) P.basis P.computeChallenge P.computePublic P.orbit
    (rowNodeSet P.computeNodes)
  have hm := finalMemoryRAP_fingerprint P.family.problem.cfg.memRows_pos P.memoryNodes
    P.basis P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem
  have hme := finalMemoryRAP_e P.family.problem.cfg.memRows_pos P.memoryNodes
    P.basis P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem
  refine ⟨(Thm54Resources.compute_resources_iff _ _ _ _ _).mpr
      ⟨hc.2.2.2.2, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩,
    (Thm54Resources.memory_resources_iff _ _ _ _ _).mpr
      ⟨hme, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2⟩⟩

/-- **The transition bucket, at the chip's own extension degree.**  Removing the endpoint and
equality bucket from the total constraint count leaves exactly
the paper's degree-`4` transition count.  This is the parametric form of
`exact_transition_fingerprints`. -/
theorem exact_transition_fingerprints_paper :
    let C := ProductionNamedComputeRAP P.family.problem.cfg.compRows_pos P.computeNodes
      P.basis P.computeChallenge P.computePublic P.orbit
    let M := namedFinalMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes
      P.basis P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem
    C.rap.s - Thm54Resources.computeEndpointConstraints C.rap.e
        = Thm54Resources.computeTransitionGates C.rap.e ∧
      M.rap.s - Thm54Resources.memoryEndpointConstraints M.rap.e
        = Thm54Resources.memoryTransitionGates M.rap.e := by
  have hpaper := P.exact_chip_resources_paper
  have hnum := P.exact_transition_fingerprints
  dsimp only at hpaper hnum ⊢
  exact ⟨(Thm54Resources.compute_transition_fingerprint_iff _ _ hpaper.1.1).mpr hnum.1,
    (Thm54Resources.memory_transition_fingerprint_iff _ _ hpaper.2.1).mpr hnum.2⟩

/-- The two concrete node images have exactly the shared assignment's compute/memory row counts. -/
theorem exact_row_domains :
    (rowNodeSet P.computeNodes).card = P.family.problem.cfg.compRows ∧
      (rowNodeSet P.memoryNodes).card = P.family.problem.cfg.memRows := by
  constructor
  · rw [rowNodeSet, Finset.card_image_of_injective _ P.computeNodes_injective]
    simp
  · rw [rowNodeSet, Finset.card_image_of_injective _ P.memoryNodes_injective]
    simp

def OptimizedSharedMemoryConnective : Prop :=
    Nock.Walk.WalkSat
        (Nock.Walk.curCol P.family.memoryNodeVal P.family.memoryWalkRows)
        (Nock.Walk.chldCol P.family.memoryNodeVal P.family.memoryWalkRows)
        (Nock.Walk.foCol P.family.memoryWalkRows)
        P.sampled.exact.memoryWalk.ln P.sampled.exact.memoryWalk.count
        P.sampled.exact.memoryWalk.acc P.family.memoryWalkAlpha P.family.memoryWalkSeed
        (P.family.memoryWalkAlpha ^ P.family.problem.cfg.kMem)
        P.family.problem.cfg.memRows ∧
      P.sampled.exact.memoryWalk.acc P.family.problem.cfg.memRows = 0 ∧
      (∀ root e,
        e ∈ AxisBridge.readExps
          (exactAxisTree P.family.problem.cfg P.memoryExecA root) →
        e ∈ AxisBridge.verifyExps
          (exactAxisTree P.family.problem.cfg P.memoryExecA root) →
        AxisBatching.MTree.vaxis e
            (exactAxisTree P.family.problem.cfg P.memoryExecA root) =
          AxisBatching.MTree.Relaxis e
            (exactAxisTree P.family.problem.cfg P.memoryExecA root)) ∧
      (FiniteIO.FiniteIOAccepts
          P.sampled.sampled.records P.sampled.sampled.coins P.sampled.sampled.witness ∧
        P.sampled.sampled.records.responses = P.family.problem.exec.derivedResponseIO ∧
        P.sampled.sampled.coins.pole ∉
          FiniteIO.IOPoleHitEvent P.sampled.sampled.records
            P.sampled.sampled.coins.gamma ∧
        P.sampled.sampled.coins.gamma ∉
          FiniteIO.IORLCCollisionEvent P.sampled.sampled.records ∧
        P.sampled.sampled.coins.pole ∉
          FiniteIO.IOLogDerivEvent P.sampled.sampled.records
            P.sampled.sampled.coins.gamma)

/-- The aggregate forest, finite sampled IO, and root-indexed carried axis are all consequences of
the package's single `memoryProduction`; no positional memory lookup is introduced here. -/
theorem shared_memory_connective :
    OptimizedSharedMemoryConnective P := by
  exact ⟨P.memoryProduction.oneForestWalk.1, P.memoryProduction.oneForestWalk.2,
    P.memoryRealization.axis_batching_sound, P.memoryProduction.sampledMemoryIO⟩

end OptimizedStrictNockVMROMPackage

/-! ## One strict product challenge and the complete consumed failure event -/

/-- **The one production challenge tuple: ten `𝕂` coordinates and no `𝔽` coordinate.**
`JointCoins` (four), the two sampled-IO coins, the compute RAP equality coins `(a, b, c)`
, and the memory table's internal `intermediate`
LogUp pole (W4 stage 2, Design A). Until H1.U exit 1 the compute
block was the unit type (`|𝕂|⁷`). `(a, b, c)` sit in `FinalComputeChallengeTuple` at
`c.2.2.1` so JointCoins / IO / `MemoryChallengeTuple` projections are unmoved.

-/
abbrev OptimizedProductionChallengeTuple (K F : Type) [Fintype K] [Fintype F] :=
  JointCoins K ×
    ((K × K) ×
      (FinalComputeChallengeTuple K × MemoryChallengeTuple K))

theorem card_finalComputeChallengeTuple
    (K : Type) [Fintype K] :
    Fintype.card (FinalComputeChallengeTuple K) = Fintype.card K ^ 3 := by
  let e : FinalComputeChallengeTuple K ≃ (K × K × K) :=
    { toFun := fun c => (c.eqA, c.eqB, c.eqC)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      left_inv := by intro c; cases c; rfl
      right_inv := by intro p; rfl }
  rw [Fintype.card_congr e]
  simp [pow_three]

theorem card_memoryChallengeTuple
    (K : Type) [Fintype K] :
    Fintype.card (MemoryChallengeTuple K) = Fintype.card K ^ 2 :=
  memoryChallengeTuple_card K

def liftP8Failure
    {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F]
    (bad : Finset (JointCoins K)) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  bad ×ˢ Finset.univ

def liftIOFailure
    {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F]
    (bad : Finset (K × K)) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ ×ˢ (bad ×ˢ Finset.univ)

/-- Lift a counted event on `(ioGamma, interPole)` — Design A's reused `γ` (the first IO
coordinate) together with the new internal pole (`c.2.2.2.interPole`).  The IO pole
`c.2.1.2` is free in this lift. -/
def liftInterPoleFailure
    {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F]
    (bad : Finset (K × K)) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter (fun c => (c.2.1.1, c.2.2.2.interPole) ∈ bad)

theorem mem_liftInterPoleFailure_iff
    {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F]
    (bad : Finset (K × K)) (c : OptimizedProductionChallengeTuple K F) :
    c ∈ liftInterPoleFailure (K := K) (F := F) bad ↔
      (c.2.1.1, c.2.2.2.interPole) ∈ bad := by
  simp [liftInterPoleFailure]

/-- The fibre of `(ioGamma, interPole)` is `|𝕂|⁹` (four JointCoins + the IO pole +
`(a, b, c)` + `lambda`). -/
theorem card_liftInterPoleFailure
    {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F]
    (bad : Finset (K × K)) :
    (liftInterPoleFailure (K := K) (F := F) bad).card ≤
      bad.card * Fintype.card K ^ 9 := by
  classical
  let encode : OptimizedProductionChallengeTuple K F →
      (K × K) × (JointCoins K × K × FinalComputeChallengeTuple K × K) :=
    fun c => ((c.2.1.1, c.2.2.2.interPole), (c.1, c.2.1.2, c.2.2.1, c.2.2.2.lambda))
  have hinj : Function.Injective encode := by
    intro c d henc
    rcases c with ⟨j, ⟨⟨γ, pol⟩, ⟨comp, mem⟩⟩⟩
    rcases d with ⟨j', ⟨⟨γ', pol'⟩, ⟨comp', mem'⟩⟩⟩
    cases mem
    cases mem'
    simp [encode] at henc
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := henc
    rfl
  have hsub :
      (liftInterPoleFailure (K := K) (F := F) bad).image encode ⊆
        bad ×ˢ Finset.univ := by
    intro q hq
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hq
    simp only [liftInterPoleFailure, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp [encode, hc]
  have hcard := Finset.card_image_of_injective
    (liftInterPoleFailure (K := K) (F := F) bad) hinj
  have hprod :
      ((bad ×ˢ (Finset.univ :
          Finset (JointCoins K × K × FinalComputeChallengeTuple K × K))).card) =
      bad.card * Fintype.card K ^ 9 := by
    rw [Finset.card_product, Finset.card_univ]
    simp only [Fintype.card_prod, card_jointCoins, card_finalComputeChallengeTuple]
    ring
  calc (liftInterPoleFailure (K := K) (F := F) bad).card
      = ((liftInterPoleFailure (K := K) (F := F) bad).image encode).card := hcard.symm
    _ ≤ (bad ×ˢ (Finset.univ :
          Finset (JointCoins K × K × FinalComputeChallengeTuple K × K))).card :=
      Finset.card_le_card hsub
    _ = bad.card * Fintype.card K ^ 9 := hprod

def liftComputeFailure
    {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F]
    (bad : Finset (FinalComputeChallengeTuple K)) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ ×ˢ (Finset.univ ×ˢ (bad ×ˢ Finset.univ))

def liftMemoryFailure
    {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F]
    (bad : Finset (MemoryChallengeTuple K)) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ bad))

/-- The one production failure event: all five P8 classes, lifted through the P8 cylinder.

**H1.5b Part 2a: the IO lift `liftIOFailure (IOFailureEvent records)`
and the `records` parameter LEFT this event.**  The IO exclusion is priced instead by the family
IO event `famIO` of `OptimizedHostileProductionFailureEvent` (at the records the family chips
read, `FamilyEnvCore.famIOEventOf`), REPLACING the package-chip lift, never beside it (the added
form is 121/119 bits, `Batch881.doubled_745_not_122`).

Previously inhabited as the three-lift union (P8, IO, memory fold).

`memoryFamilies` is **retained in the signature** — it is what `memoryScalarFamilies` supplies at
every call site — but the consumed event does not read it. -/
def OptimizedProductionFailureEvent
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M : ℕ}
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (_computeEnvK : Fin N → Env K) (_computeWalkEnv : Env K) (_computeEnvF : Env F)
    (_memoryEnvK : Fin M → Env K)
    (_memoryFamilies : Fin M → Fin 7 → Fin 3 → F) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  liftP8Failure (ProductionP8Containment.FailureUnion T C lmb)

def optimizedProductionFailureCardBound
    (cardK cardF p8Work ioWork N M : ℕ) : ℕ :=
  p8Work * cardK ^ 3 * (cardK ^ 2 * ((cardK ^ 2 * cardF) * cardK)) +
    cardK ^ 4 * ioWork * ((cardK ^ 2 * cardF) * cardK) +
    cardK ^ 6 *
      (((494 * N) * cardK * cardF + cardK * cardF + cardK ^ 2 * 20) * cardK) +
    (cardK ^ 8 * cardF * (61 * M) + cardK ^ 9 * (14 * M))

def optimizedProductionFailureProbabilityBound
    (cardK cardF p8Work ioWork N M : ℕ) : ℚ :=
  (p8Work + 494 * N + 1 + 61 * M : ℚ) / cardK +
    (ioWork : ℚ) / cardK ^ 2 +
    (20 + 14 * M : ℚ) / cardF

/-!

Merging the memory core takes each fold bucket from four sources to two, so the per-row
fold bad-challenge count falls `61 → 19`
(`OptimizedMemoryCollisionAccounting.extensionFoldFamilies_workload`).  The definitions above
are **kept at `61` under their existing names** — they are still true, now with slack — and the
tighter numbers below are what the released capstone consumes: `OptimizedStrictThm54Statement.
completeS7`, `OptimizedFullStrictNockVMROMPackage.optimizedFalseAcceptance_probability_le` and
the two `complete_false_acceptance_*` conjuncts of `OptimizedFullStrictThm54Statement` all name
the merged bound, with `…_legacy` corollaries recovering the `61·M` phrasing for statements
written against it.  Nothing else in the accounting moves: `494·N`, `20`, `14·M` and the IO
term are untouched. -/

/-- The `19·M` card bound.  Identical to `optimizedProductionFailureCardBound` except in the
memory summand. -/
def optimizedMergedProductionFailureCardBound
    (cardK cardF p8Work ioWork N M : ℕ) : ℕ :=
  p8Work * cardK ^ 3 * (cardK ^ 2 * ((cardK ^ 2 * cardF) * cardK)) +
    cardK ^ 4 * ioWork * ((cardK ^ 2 * cardF) * cardK) +
    cardK ^ 6 *
      (((494 * N) * cardK * cardF + cardK * cardF + cardK ^ 2 * 20) * cardK) +
    (cardK ^ 8 * cardF * (19 * M) + cardK ^ 9 * (14 * M))

/-- The `19·M` probability bound. -/
def optimizedMergedProductionFailureProbabilityBound
    (cardK cardF p8Work ioWork N M : ℕ) : ℚ :=
  (p8Work + 494 * N + 1 + 19 * M : ℚ) / cardK +
    (ioWork : ℚ) / cardK ^ 2 +
    (20 + 14 * M : ℚ) / cardF

theorem optimizedMergedProductionFailureCardBound_le
    (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedMergedProductionFailureCardBound cardK cardF p8Work ioWork N M ≤
      optimizedProductionFailureCardBound cardK cardF p8Work ioWork N M := by
  simp only [optimizedMergedProductionFailureCardBound, optimizedProductionFailureCardBound]
  refine Nat.add_le_add_left ?_ _
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _

/-- **The merged bound is never worse.** -/
theorem optimizedMergedProductionFailureProbabilityBound_le
    (cardK cardF p8Work ioWork N M : ℕ) (hk : 0 < cardK) :
    optimizedMergedProductionFailureProbabilityBound cardK cardF p8Work ioWork N M ≤
      optimizedProductionFailureProbabilityBound cardK cardF p8Work ioWork N M := by
  have hkq : (0 : ℚ) < (cardK : ℚ) := by exact_mod_cast hk
  have hM : (0 : ℚ) ≤ (M : ℚ) := by positivity
  have hnum : (p8Work + 494 * N + 1 + 19 * M : ℚ)
      ≤ (p8Work + 494 * N + 1 + 61 * M : ℚ) := by linarith
  have hdiv := div_le_div_of_nonneg_right hnum hkq.le
  simp only [optimizedMergedProductionFailureProbabilityBound,
    optimizedProductionFailureProbabilityBound]
  linarith

/-- This is the only arithmetic a consumer of
the legacy phrasing needs. -/
theorem optimizedMergedProductionFailure_support_of_legacy
    (cardK cardF p8Work ioWork N M b : ℕ) (hk : 0 < cardK)
    (h : optimizedProductionFailureProbabilityBound cardK cardF p8Work ioWork N M * 2 ^ b
      ≤ 1) :
    optimizedMergedProductionFailureProbabilityBound cardK cardF p8Work ioWork N M * 2 ^ b
      ≤ 1 := by
  refine le_trans ?_ h
  have hpow : (0 : ℚ) < 2 ^ b := by positivity
  exact mul_le_mul_of_nonneg_right
    (optimizedMergedProductionFailureProbabilityBound_le cardK cardF p8Work ioWork N M hk)
    hpow.le

/-!

Stage 3c of the `𝔽 → 𝕂` migration.  `OptimizedProductionFailureEvent`'s memory summand is now
the single extension-fold lift, so the four base-field memory lifts — and with them the whole
`14 · M / |𝔽|` summand — are gone from the union.  The `20 / |𝔽|` summand **remains**: it is the
compute chip's `challenge36` scalar compression, which this stage does not touch.

The `19·M` definitions above are **kept under their existing names** — they are still true, now
with slack — and the released capstone's primary statements name the definitions below, with
`…_merged` and `…_legacy` corollaries recovering the `19·M`-plus-`14·M/|𝔽|` and `61·M` readings. -/

/-- The extension-only card bound.  Identical to `optimizedMergedProductionFailureCardBound`
except that the memory summand loses its `cardK * (14 * M) * cardF ^ 3` half. -/
def optimizedExtensionProductionFailureCardBound
    (cardK cardF p8Work ioWork N M : ℕ) : ℕ :=
  p8Work * cardK ^ 3 * (cardK ^ 2 * ((cardK ^ 2 * cardF) * cardK)) +
    cardK ^ 4 * ioWork * ((cardK ^ 2 * cardF) * cardK) +
    cardK ^ 6 *
      (((494 * N) * cardK * cardF + cardK * cardF + cardK ^ 2 * 20) * cardK) +
    cardK ^ 8 * cardF * (19 * M)

/-- **The extension-only probability bound: `(p8Work + 494·N + 1 + 19·M)/|𝕂| + ioWork/|𝕂|² +
20/|𝔽|`.**  The base-field summand has lost its `14·M`; the constant `20` is compute's and stays.

This is *not* the `𝕂`-typed bound of `ExtensionChallengeMigration` — that one retypes the
compute scalar coin too, and `naive_deletion_undershoots` records that deleting a term from a
bound is the wrong function.  Here the term is deleted because the **event** lost those lifts. -/
def optimizedExtensionProductionFailureProbabilityBound
    (cardK cardF p8Work ioWork N M : ℕ) : ℚ :=
  (p8Work + 494 * N + 1 + 19 * M : ℚ) / cardK +
    (ioWork : ℚ) / cardK ^ 2 +
    (20 : ℚ) / cardF

theorem optimizedExtensionProductionFailureCardBound_le
    (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedExtensionProductionFailureCardBound cardK cardF p8Work ioWork N M ≤
      optimizedMergedProductionFailureCardBound cardK cardF p8Work ioWork N M := by
  simp only [optimizedExtensionProductionFailureCardBound,
    optimizedMergedProductionFailureCardBound]
  refine Nat.add_le_add_left ?_ _
  exact Nat.le_add_right _ _

/-- **The extension-only bound is never worse than the merged one.** -/
theorem optimizedExtensionProductionFailureProbabilityBound_le
    (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedExtensionProductionFailureProbabilityBound cardK cardF p8Work ioWork N M ≤
      optimizedMergedProductionFailureProbabilityBound cardK cardF p8Work ioWork N M := by
  simp only [optimizedExtensionProductionFailureProbabilityBound,
    optimizedMergedProductionFailureProbabilityBound]
  have hM : (0 : ℚ) ≤ (14 * M : ℚ) := by positivity
  have : (20 : ℚ) / cardF ≤ (20 + 14 * M : ℚ) / cardF := by
    rcases Nat.eq_zero_or_pos cardF with h | h
    · simp [h]
    · have : (0 : ℚ) < (cardF : ℚ) := by exact_mod_cast h
      gcongr
      linarith
  linarith

/-- **Support transfer.**  A bit budget the merged `19·M` bound supports is a fortiori supported
by the extension-only bound, so every `1/2^b` statement phrased against the merged bound survives
the re-pointing of the capstone unchanged. -/
theorem optimizedExtensionProductionFailure_support_of_merged
    (cardK cardF p8Work ioWork N M b : ℕ)
    (h : optimizedMergedProductionFailureProbabilityBound cardK cardF p8Work ioWork N M * 2 ^ b
      ≤ 1) :
    optimizedExtensionProductionFailureProbabilityBound cardK cardF p8Work ioWork N M * 2 ^ b
      ≤ 1 := by
  refine le_trans ?_ h
  have hpow : (0 : ℚ) < 2 ^ b := by positivity
  exact mul_le_mul_of_nonneg_right
    (optimizedExtensionProductionFailureProbabilityBound_le cardK cardF p8Work ioWork N M)
    hpow.le

/-!

Stage 3e de-compressed the compute chip's two `challenge36`-folded endpoint equality checks into
the twenty-two individual masked equations `OptimizedComputeFinal.finalEndpointEqualityChecks`.
Those gates determine the eleven column-vs-public equations of each family with **no coin**
(`endpointEqualityChecks_determine_public`), so the `liftChallenge36` summand left
`OptimizedProductionFailureEvent` and the `20/|𝔽|` summand of the probability bound went with it.

**The consumed bound is therefore `𝕂`-denominated throughout.**

-/

/-- **The consumed card bound, over the `|𝕂|¹¹` challenge space.**  Two summands — P8 and IO —
each lifted by the universe of the coordinates it does not constrain. H1.U exit 1 grew the
compute block by `(a, b, c)` (`|𝕂|⁷ → |𝕂|¹⁰`); W4 stage 2 grew the rest-of-tuple by the
`interPole` coordinate; W2 stage 3 dropped the memory-fold `19·M` summand with the fold coin;
W3 stage 2 dropped `(494·N + 1)`. The
`cardF` and `N` parameters are retained for signature stability and are read by nothing. -/
def optimizedTrimmedProductionFailureCardBound
    (cardK cardF p8Work ioWork N M : ℕ) : ℕ :=
  p8Work * cardK ^ 3 * (cardK ^ 7) +
    cardK ^ 9 * ioWork

/-- **The trimmed probability bound: `p8Work/|𝕂| + ioWork/|𝕂|²`.**  W2 stage 3 dropped the
`19·M/|𝕂|` memory-fold summand with the fold coin.  W3 stage 2 dropped `(494·N + 1)/|𝕂|`.
There is no `/|𝔽|` term. -/
def optimizedTrimmedProductionFailureProbabilityBound
    (cardK cardF p8Work ioWork N M : ℕ) : ℚ :=
  (p8Work : ℚ) / cardK + (ioWork : ℚ) / cardK ^ 2

/-- The
probability comparison `optimizedTrimmedProductionFailureProbabilityBound_le` is unmoved. -/
theorem optimizedTrimmedProductionFailureCardBound_le
    (cardK cardF p8Work ioWork N M : ℕ) (_hf : 0 < cardF) :
    optimizedTrimmedProductionFailureCardBound cardK cardF p8Work ioWork N M ≤
      optimizedTrimmedProductionFailureCardBound cardK cardF p8Work ioWork N M :=
  le_rfl

/-- **The trimmed bound is never worse than the extension-only one.** -/
theorem optimizedTrimmedProductionFailureProbabilityBound_le
    (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedTrimmedProductionFailureProbabilityBound cardK cardF p8Work ioWork N M ≤
      optimizedExtensionProductionFailureProbabilityBound cardK cardF p8Work ioWork N M := by
  simp only [optimizedTrimmedProductionFailureProbabilityBound,
    optimizedExtensionProductionFailureProbabilityBound]
  have hN : (0 : ℚ) ≤ (494 * N + 1 : ℚ) := by positivity
  have h20 : (0 : ℚ) ≤ (20 : ℚ) / cardF := by positivity
  have hM : (0 : ℚ) ≤ (19 * M : ℚ) := by positivity
  have hnum : (p8Work : ℚ) / cardK
      ≤ (p8Work + 494 * N + 1 + 19 * M : ℚ) / cardK := by
    rcases Nat.eq_zero_or_pos cardK with h | h
    · simp [h]
    · have : (0 : ℚ) < (cardK : ℚ) := by exact_mod_cast h
      gcongr
      linarith
  linarith

/-- **Support transfer.**  A bit budget the extension-only bound supports is a fortiori supported
by the trimmed bound, so every `1/2^b` statement phrased against it survives the re-pointing. -/
theorem optimizedTrimmedProductionFailure_support_of_extension
    (cardK cardF p8Work ioWork N M b : ℕ)
    (h : optimizedExtensionProductionFailureProbabilityBound cardK cardF p8Work ioWork N M
      * 2 ^ b ≤ 1) :
    optimizedTrimmedProductionFailureProbabilityBound cardK cardF p8Work ioWork N M * 2 ^ b
      ≤ 1 := by
  refine le_trans ?_ h
  have hpow : (0 : ℚ) < 2 ^ b := by positivity
  exact mul_le_mul_of_nonneg_right
    (optimizedTrimmedProductionFailureProbabilityBound_le cardK cardF p8Work ioWork N M)
    hpow.le

/-- `|𝕂|⁷` until H1.U exit 1 inserted `(a, b, c)` at `c.2.2.1`; `|𝕂|⁶` until
    W4 stage 2 inserted `interPole`; `|𝕂|⁷` until W2 stage 3 deleted `extensionFold`; `|𝕂|⁹`
    until W3 stage 2 deleted `challenge9`/`challenge11`. -/
theorem card_optimizedProductionChallengeTuple
    (K F : Type) [Fintype K] [Fintype F] :
    Fintype.card (OptimizedProductionChallengeTuple K F) = Fintype.card K ^ 11 := by
  simp only [Fintype.card_prod, card_finalComputeChallengeTuple,
    card_memoryChallengeTuple]
  ring


theorem normalized_card_bound_eq_separate_denominators
    (cardK cardF p8Work ioWork N M : ℕ)
    (hk : 0 < cardK) (hf : 0 < cardF) :
    (optimizedProductionFailureCardBound cardK cardF p8Work ioWork N M : ℚ) /
        (cardK ^ 9 * cardF) =
      optimizedProductionFailureProbabilityBound cardK cardF p8Work ioWork N M := by
  have hkq : (cardK : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hfq : (cardF : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hf
  simp only [optimizedProductionFailureCardBound,
    optimizedProductionFailureProbabilityBound, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow]
  field_simp
  ring

theorem optimizedTrimmedProductionFailureEvent_card_le
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M : ℕ}
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (topologyBound axisWorkload : ℕ)
    (hwindow : SizeWindowCounting.SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (ioWork : ℕ)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F) :
    (OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
      memoryEnvK memoryFamilies).card ≤
      optimizedTrimmedProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (workload T Λ topologyBound axisWorkload)
        ioWork N M := by
  have hp8 :
      (OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies).card ≤
        workload T Λ topologyBound axisWorkload * Fintype.card K ^ 3 * (Fintype.card K ^ 7) := by
    rw [show OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies =
        ProductionP8Containment.FailureUnion T C lmb ×ˢ Finset.univ by rfl,
      Finset.card_product, Finset.card_univ]
    calc
      (ProductionP8Containment.FailureUnion T C lmb).card *
          Fintype.card ((K × K) ×
            (FinalComputeChallengeTuple K × MemoryChallengeTuple K))
          ≤ (workload T Λ topologyBound axisWorkload * Fintype.card K ^ 3) *
            Fintype.card ((K × K) ×
              (FinalComputeChallengeTuple K × MemoryChallengeTuple K)) :=
        Nat.mul_le_mul_right _
          (ProductionP8Containment.failureUnion_card_le
            h2 T lmb C topologyBound axisWorkload hwindow htopology haxis)
      _ = workload T Λ topologyBound axisWorkload * Fintype.card K ^ 3 *
          (Fintype.card K ^ 7) := by
        simp only [Fintype.card_prod, card_finalComputeChallengeTuple,
          card_memoryChallengeTuple]
        ring
  simp only [optimizedTrimmedProductionFailureCardBound]
  omega

/-- **The trimmed card bound with the Form R slot left free**: the four
lifts use the P8 numerator without its Form R summand — since the thirty-second move the
trace-uniform `formRUniformWorkload` (was `fixedFormRWorkload`)
(`ProductionP8Containment.failureUnion_card_add_formR_le`), so the λ-event's
`|𝕂|¹⁰ · formRUniformWorkload` fits beside them in the same numerator; since the thirty-third
move the pair event's `|𝕂|¹⁰ · reqPairWorkload T Λ` does too. -/
theorem optimizedTrimmedProductionFailureEvent_card_add_formR_le
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M : ℕ}
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (topologyBound axisWorkload : ℕ)
    (hwindow : SizeWindowCounting.SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (ioWork : ℕ)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F)
    (famIO : Finset (OptimizedProductionChallengeTuple K F))
    (hfam : famIO.card ≤ Fintype.card K ^ 9 * ioWork) :
    (OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
      memoryEnvK memoryFamilies).card + famIO.card +
        Fintype.card K ^ 10 * ProductionP8Containment.formRUniformWorkload T +
        Fintype.card K ^ 10 * ProductionP8Containment.reqPairWorkload T Λ ≤
      optimizedTrimmedProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (workload T Λ topologyBound axisWorkload)
        ioWork N M := by
  have hp8 :
      (OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies).card + Fintype.card K ^ 10 * ProductionP8Containment.formRUniformWorkload T +
          Fintype.card K ^ 10 * ProductionP8Containment.reqPairWorkload T Λ ≤
        workload T Λ topologyBound axisWorkload * Fintype.card K ^ 3 *
          (Fintype.card K ^ 7) := by
    rw [show OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies =
        ProductionP8Containment.FailureUnion T C lmb ×ˢ Finset.univ by rfl,
      Finset.card_product, Finset.card_univ]
    have hrest :
        Fintype.card ((K × K) × (FinalComputeChallengeTuple K × MemoryChallengeTuple K)) =
          Fintype.card K ^ 7 := by
      simp only [Fintype.card_prod, card_finalComputeChallengeTuple, card_memoryChallengeTuple]
      ring
    rw [hrest]
    have h := ProductionP8Containment.failureUnion_card_add_formR_le
      h2 T lmb C topologyBound axisWorkload hwindow htopology haxis
    have h' := Nat.mul_le_mul_right (Fintype.card K ^ 7) h
    calc (ProductionP8Containment.FailureUnion T C lmb).card * Fintype.card K ^ 7 +
          Fintype.card K ^ 10 * ProductionP8Containment.formRUniformWorkload T +
          Fintype.card K ^ 10 * ProductionP8Containment.reqPairWorkload T Λ
        = ((ProductionP8Containment.FailureUnion T C lmb).card +
            ProductionP8Containment.formRUniformWorkload T * Fintype.card K ^ 3 +
            ProductionP8Containment.reqPairWorkload T Λ * Fintype.card K ^ 3) *
              Fintype.card K ^ 7 := by ring
      _ ≤ _ := h'
  simp only [optimizedTrimmedProductionFailureCardBound]
  omega

/-- The extension-only card bound, now a corollary of the trimmed one. -/
theorem optimizedExtensionProductionFailureEvent_card_le
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M : ℕ}
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (topologyBound axisWorkload : ℕ)
    (hwindow : SizeWindowCounting.SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (ioWork : ℕ)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F) :
    (OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
      memoryEnvK memoryFamilies).card ≤
      optimizedTrimmedProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (workload T Λ topologyBound axisWorkload)
        ioWork N M :=

  -- (`|𝕂| ≰ |𝔽|`).  The live event bound is the trimmed card.
  optimizedTrimmedProductionFailureEvent_card_le h2 T C lmb topologyBound axisWorkload hwindow
    htopology haxis ioWork computeEnvK computeWalkEnv computeEnvF memoryEnvK
    memoryFamilies

/-- The `19·M`-plus-`14·M/|𝔽|` card bound, now a corollary of the extension-only one. -/
theorem optimizedMergedProductionFailureEvent_card_le
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M : ℕ}
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (topologyBound axisWorkload : ℕ)
    (hwindow : SizeWindowCounting.SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (ioWork : ℕ)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F) :
    (OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
      memoryEnvK memoryFamilies).card ≤
      optimizedTrimmedProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (workload T Λ topologyBound axisWorkload)
        ioWork N M :=
  optimizedTrimmedProductionFailureEvent_card_le h2 T C lmb topologyBound axisWorkload hwindow
    htopology haxis ioWork computeEnvK computeWalkEnv computeEnvF memoryEnvK
    memoryFamilies


theorem optimizedProductionFailureEvent_card_le
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M : ℕ}
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (topologyBound axisWorkload : ℕ)
    (hwindow : SizeWindowCounting.SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (ioWork : ℕ)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F) :
    (OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
      memoryEnvK memoryFamilies).card ≤
      optimizedTrimmedProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (workload T Λ topologyBound axisWorkload)
        ioWork N M :=
  optimizedTrimmedProductionFailureEvent_card_le h2 T C lmb topologyBound axisWorkload hwindow
    htopology haxis ioWork computeEnvK computeWalkEnv computeEnvF memoryEnvK
    memoryFamilies

/-- Normalization of the consumed card bound over the **`|𝕂|¹¹`** challenge space: dividing by
`|𝕂|¹¹` gives exactly `p8Work/|𝕂| + ioWork/|𝕂|²`.

H1.U exit 1 grew the rest-of-tuple by `(a, b, c)`, so the universe gained a `|𝕂|³` factor —
and so did every surviving lift (a cylinder).  The quotient on the surviving summands is
**the same probability bound**.  No `0 < cardF` hypothesis is needed: `cardF` occurs in
neither side. -/
theorem normalized_trimmed_card_bound_eq_separate_denominators
    (cardK cardF p8Work ioWork N M : ℕ) (hk : 0 < cardK) :
    (optimizedTrimmedProductionFailureCardBound cardK cardF p8Work ioWork N M : ℚ) /
        (cardK ^ 11) =
      optimizedTrimmedProductionFailureProbabilityBound cardK cardF p8Work ioWork N M := by
  have hkq : (cardK : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  simp only [optimizedTrimmedProductionFailureCardBound,
    optimizedTrimmedProductionFailureProbabilityBound, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow]
  field_simp


theorem optimizedTrimmedProductionFailureProbability_le
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M : ℕ}
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (topologyBound axisWorkload : ℕ)
    (hwindow : SizeWindowCounting.SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (ioWork : ℕ)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F) :
    ((OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤
      optimizedTrimmedProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
        (workload T Λ topologyBound axisWorkload)
        ioWork N M := by
  have hcard := optimizedTrimmedProductionFailureEvent_card_le h2 T C lmb topologyBound
    axisWorkload hwindow htopology haxis ioWork computeEnvK computeWalkEnv computeEnvF
    memoryEnvK memoryFamilies
  have hcast :
      ((OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
          memoryEnvK memoryFamilies).card : ℚ) ≤
        optimizedTrimmedProductionFailureCardBound (Fintype.card K) (Fintype.card F)
          (workload T Λ topologyBound axisWorkload)
          ioWork N M := by
    exact_mod_cast hcard
  rw [card_optimizedProductionChallengeTuple]
  norm_num only [Nat.cast_pow]
  calc
    ((OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies).card : ℚ) / (Fintype.card K ^ 11)
        ≤ (optimizedTrimmedProductionFailureCardBound (Fintype.card K) (Fintype.card F)
            (workload T Λ topologyBound axisWorkload)
            ioWork N M : ℚ) / (Fintype.card K ^ 11) :=
      div_le_div_of_nonneg_right hcast (by positivity)
    _ = _ := normalized_trimmed_card_bound_eq_separate_denominators _ _ _ _ _ _
      Fintype.card_pos

/-! ### The W6.1 stage 2B hostile event — the IO summand at the traces' own records, plus the
α-collision summand

**Round structure.**  The prover commits
`Com(IO_prog)` (`:508`) — and the memory table's records, which are "obtained from the
computation table" (`:547`) — *before* the verifier "responds with random elements `α, β ∈ 𝕂`"
(`:509`; "one round of interaction, providing two random elements in `𝕂`", `:634`), and the IO
consistency checks are "solely a function of their output values" and that randomness (`:594-599`).
In this tree the committed traces `Qc`, `Qm` carry those records (`hostileRecords P Qc Qm` is a
function of the traces alone) and the tuple `c` is sampled afterwards, so the event
`{c | c.2.1 ∈ IOFailureEvent (hostileRecords P Qc Qm)}` is a fixed subset of the coin space for
each trace pair and the union bound over `c` at fixed `(Qc, Qm)` is exactly the paper's argument.
The honest records `P.optimized.sampled.sampled.records` need no pricing at all: the package's
`FiniteIOStrategy.coins_not_failure` already excludes its own coins from that event, and
`sampled_io_coins` pins `c.2.1` to those coins
(`OptimizedStrictFullPackage.sampled_io_event_good_of_acceptance`). -/

/-- The α-collision event lifted to the production tuple: through `liftAlphaM` (the `alphaM`
coordinate of `JointCoins`, `AxisSoundness.liftAlphaM`) and then through every other
coordinate. -/
def liftTimestampFailure
    {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F]
    (bad : Finset K) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  liftP8Failure (liftAlphaM bad)

theorem mem_liftTimestampFailure_iff
    {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F]
    (bad : Finset K) (c : OptimizedProductionChallengeTuple K F) :
    c ∈ liftTimestampFailure bad ↔ alphaM c.1 ∈ bad := by
  simp [liftTimestampFailure, liftP8Failure]

theorem card_liftTimestampFailure
    {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F]
    (bad : Finset K) :
    (liftTimestampFailure (F := F) bad).card = bad.card * Fintype.card K ^ 10 := by
  rw [liftTimestampFailure, liftP8Failure, Finset.card_product, Finset.card_univ,
    card_liftAlphaM]
  simp only [Fintype.card_prod, card_finalComputeChallengeTuple, card_memoryChallengeTuple]
  ring

/-- **The consumed failure event since W4 stage 2.**  The four lifts of
`OptimizedProductionFailureEvent` at the caller's IO `records`, the α-collision
event at request count `D`, and `liftInterPoleFailure` on `(ioGamma, interPole)`
over the memory table's intermediate records.  The sampled pole is priced, not slack.

Pole-hit on every memory row's committed record (halt / decompose included)
is priced inside the internal-pole lift so `hden` on every row follows from
`hgood`. -/
def allRowPoleHitEvent
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] {M : ℕ}
    (memoryEnvK : Fin M → Env K) (memoryEnvF : Fin M → Env F) : Finset (K × K) :=
  Finset.univ.filter (fun q =>
    q.2 ∈ FiniteIO.IOPoleHitEvent
      ⟨List.ofFn (fun i =>
        OptimizedMemoryHostileAccumulator.rowRecord (memoryEnvK i) (memoryEnvF i)), []⟩
      q.1)

/-- The priced internal-pole pairs: the three counted events on the active
read / verify lists, plus pole-hit on every row record. -/
def interFailurePairs
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] {M : ℕ}
    (interRecords : FiniteIO.PreChallengeRecords K 10)
    (memoryEnvK : Fin M → Env K) (memoryEnvF : Fin M → Env F) : Finset (K × K) :=
  FiniteIO.IOFailureEvent interRecords ∪ allRowPoleHitEvent memoryEnvK memoryEnvF

/-- **The consumed failure event since H1.5a γ-pricing.**
The walk-queue union plus the two whole-table prefix γ-collision events
(`WalkPrefixGammaEvents.computePrefixGammaEventOf` / `memoryPrefixGammaEventOfEnvs`),
lifted through the same P8 cylinder.  Cards `≤ 9N` and `≤ 5M`
(`node_size − 1` at `LT_comp` width 10 / `x^mem` width 6).

The pinned
`optimizedFailureEvent` instantiated it with `FormRAxisEvent.formRLambdaEvent`, priced by
`fixedFormRWorkload`. **Thirty-second move:** the pinned instance is the decoded
event `decodedLambdaEventOf` (`DecodedLambdaEvent.decodedLambdaEventOfEnvs` at the committed
envs), priced by `ProductionP8Containment.formRUniformWorkload` inside `workload`. **Thirty-third move:** the last parameter `pairSeeds` is the
request-indexed pre-`z` pair event on `JointCoins` (the pinned instance is
`PreSeedCensus.reqPairEventOfEnvs` at the committed memory base envs), lifted through the P8
cylinder and priced by `ProductionP8Containment.reqPairWorkload` inside `workload`. -/
def OptimizedHostileProductionFailureEvent
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M : ℕ}
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (famIO : Finset (OptimizedProductionChallengeTuple K F)) (D : ℕ)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F)
    (interRecords : FiniteIO.PreChallengeRecords K 10)
    (memoryEnvF : Fin M → Env F)
    (walkRoot : Finset (JointCoins K))
    (tilingC : Finset (JointCoins K))
    (tilingM : Finset (JointCoins K))
    (gammaC : Finset (JointCoins K))
    (gammaM : Finset (JointCoins K))
    (forestAlpha : Finset (JointCoins K))
    (formRLambda : Finset (OptimizedProductionChallengeTuple K F))
    (pairSeeds : Finset (JointCoins K)) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
      memoryEnvK memoryFamilies ∪
    famIO ∪
    liftTimestampFailure (OptimizedHostileTimestamps.TimestampCollisionEvent D) ∪
    liftInterPoleFailure (interFailurePairs interRecords memoryEnvK memoryEnvF) ∪
    liftP8Failure walkRoot ∪
    liftP8Failure tilingC ∪
    liftP8Failure tilingM ∪
    liftP8Failure gammaC ∪
    liftP8Failure gammaM ∪
    liftP8Failure forestAlpha ∪
    formRLambda ∪
    liftP8Failure pairSeeds

/-- Form R λ-event majorant `M + 3N + 2(n−1) + 4`. Kept, unused by the consumed bound, until it is deleted. -/
def pwAccountingWork' (n N M : ℕ) : ℕ := M + 3 * N + 2 * (n - 1) + 4

/-- Walk-priced `|𝕂|`-numerator: root + tiling + whole-table γ (`9N + 5M`) + forest α (`M`). -/
def pricedWalkWork (N M : ℕ) : ℕ :=
  ComputeWalkRootEvents.walkRootBound N +
    WalkTilingEvents.computeTilingBound N +
    WalkTilingEvents.memoryTilingBound M +
    WalkPrefixGammaEvents.computePrefixGammaBound N +
    WalkPrefixGammaEvents.memoryPrefixGammaBound M +
    WalkForestPrefixAlphaEvents.memoryForestAlphaBound M

/-- **The consumed card bound since H1.5a γ-pricing**: walk-queue body plus the two
prefix-γ lifts `|𝕂|⁹ · (9N + 5M)`. -/
def optimizedHostileProductionFailureCardBound
    (cardK cardF p8Work ioWork N M : ℕ) : ℕ :=
  optimizedTrimmedProductionFailureCardBound cardK cardF p8Work ioWork N M +
    cardK ^ 10 * OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
    cardK ^ 9 * (FiniteIO.ioFailureUnionBound 10 M M cardK + cardK * M) +
    cardK ^ 10 * pricedWalkWork N M

/-- **The consumed probability bound since H1.5a γ-pricing:
`(p8Work + (1 + 3N(3N−1)/2) + (N + 9) + (2N+2) + (2M+1) + 9N + 5M + M)/|𝕂| + ioWork/|𝕂|² + interWork/|𝕂|²`.**
Whole-table γ is `h·(node_size − 1)` per walk; paper `:966`/`:1008` quotes `h/|K|`. -/
def optimizedHostileProductionFailureProbabilityBound
    (cardK cardF p8Work ioWork N M : ℕ) : ℚ :=
    (p8Work +
      OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
      pricedWalkWork N M : ℚ) / cardK +
    (ioWork : ℚ) / cardK ^ 2 +
    ((FiniteIO.ioFailureUnionBound 10 M M cardK + cardK * M : ℕ) : ℚ) / cardK ^ 2

/-- **The consumed probability bound's body, asserted by `rfl`.** -/
theorem optimizedHostileProductionFailureProbabilityBound_byte_identical
    (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureProbabilityBound cardK cardF p8Work ioWork N M =
      (p8Work +
        OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
        pricedWalkWork N M : ℚ) / cardK +
      (ioWork : ℚ) / cardK ^ 2 +
      ((FiniteIO.ioFailureUnionBound 10 M M cardK + cardK * M : ℕ) : ℚ) / cardK ^ 2 :=
  rfl

/-- Positive control: P8-lift density is unchanged by the `(a, b, c)` cylinder. -/
theorem liftP8Failure_density
    {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F] [Nonempty K]
    (bad : Finset (JointCoins K)) :
    ((liftP8Failure (K := K) (F := F) bad).card : ℚ) /
        (Fintype.card (OptimizedProductionChallengeTuple K F) : ℚ) =
      (bad.card : ℚ) / (Fintype.card (JointCoins K) : ℚ) := by
  have hrest :
      Fintype.card ((K × K) × FinalComputeChallengeTuple K × MemoryChallengeTuple K) =
        Fintype.card K ^ 7 := by
    simp [Fintype.card_prod, card_finalComputeChallengeTuple, card_memoryChallengeTuple]
    ring
  rw [liftP8Failure, Finset.card_product, Finset.card_univ,
    card_optimizedProductionChallengeTuple, card_jointCoins, hrest]
  push_cast
  have hK : (Fintype.card K : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Positive control: IO-lift density is unchanged by the `(a, b, c)` cylinder. -/
theorem liftIOFailure_density
    {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F] [Nonempty K]
    (bad : Finset (K × K)) :
    ((liftIOFailure (K := K) (F := F) bad).card : ℚ) /
        (Fintype.card (OptimizedProductionChallengeTuple K F) : ℚ) =
      (bad.card : ℚ) / (Fintype.card (K × K) : ℚ) := by
  rw [liftIOFailure, Finset.card_product, Finset.card_product, Finset.card_univ,
    Finset.card_univ, card_optimizedProductionChallengeTuple]
  push_cast
  have hK : (Fintype.card K : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Fintype.card_prod, card_jointCoins, card_finalComputeChallengeTuple,
    card_memoryChallengeTuple]
  push_cast
  field_simp

/-- Positive control: timestamp-lift density is unchanged by the `(a, b, c)` cylinder. -/
theorem liftTimestampFailure_density
    {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F] [Nonempty K]
    (bad : Finset K) :
    ((liftTimestampFailure (F := F) bad).card : ℚ) /
        (Fintype.card (OptimizedProductionChallengeTuple K F) : ℚ) =
      (bad.card : ℚ) / (Fintype.card K : ℚ) := by
  rw [card_liftTimestampFailure, card_optimizedProductionChallengeTuple]
  push_cast
  have hK : (Fintype.card K : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Positive control: interPole-lift density is unchanged (cylinder over `(a, b, c)`
and the free IO pole / JointCoins).  The card lemma is an inequality, so this is
`≤` the two-coordinate density. -/
theorem liftInterPoleFailure_density_le
    {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F] [Nonempty K]
    (bad : Finset (K × K)) :
    ((liftInterPoleFailure (K := K) (F := F) bad).card : ℚ) /
        (Fintype.card (OptimizedProductionChallengeTuple K F) : ℚ) ≤
      (bad.card : ℚ) / (Fintype.card (K × K) : ℚ) := by
  have hcard := card_liftInterPoleFailure (K := K) (F := F) bad
  have hcast : ((liftInterPoleFailure (K := K) (F := F) bad).card : ℚ) ≤
      (bad.card * Fintype.card K ^ 9 : ℚ) := by exact_mod_cast hcard
  rw [card_optimizedProductionChallengeTuple]
  have hK : (0 : ℚ) < (Fintype.card K : ℚ) := by exact_mod_cast Fintype.card_pos
  have hden : (0 : ℚ) < (Fintype.card K : ℚ) ^ 11 := by positivity
  calc
    _ ≤ (bad.card * Fintype.card K ^ 9 : ℚ) / (Fintype.card K ^ 11 : ℚ) :=
      div_le_div_of_nonneg_right hcast hden.le
    _ = (bad.card : ℚ) / (Fintype.card K : ℚ) ^ 2 := by
      push_cast
      field_simp
    _ = (bad.card : ℚ) / (Fintype.card (K × K) : ℚ) := by
      simp [Fintype.card_prod, pow_two]

/-- The α-collision and walk-root summands sit on P8 coordinates and the internal-pole
summand sits on the IO slot, so the hostile bound **is** the trimmed bound with those counts
added. -/
theorem optimizedHostileProductionFailureProbabilityBound_eq_trimmed_shift
    (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureProbabilityBound cardK cardF p8Work ioWork N M =
      optimizedTrimmedProductionFailureProbabilityBound cardK cardF
        (p8Work + OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
          pricedWalkWork N M)
        (ioWork + (FiniteIO.ioFailureUnionBound 10 M M cardK + cardK * M)) N M := by
  simp only [optimizedHostileProductionFailureProbabilityBound,
    optimizedTrimmedProductionFailureProbabilityBound]
  push_cast
  ring

theorem optimizedHostileProductionFailureCardBound_eq_trimmed_shift
    (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureCardBound cardK cardF p8Work ioWork N M =
      optimizedTrimmedProductionFailureCardBound cardK cardF
        (p8Work + OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
          pricedWalkWork N M)
        (ioWork + (FiniteIO.ioFailureUnionBound 10 M M cardK + cardK * M)) N M := by
  simp only [optimizedHostileProductionFailureCardBound,
    optimizedTrimmedProductionFailureCardBound]
  ring

/-- Normalisation over the `|𝕂|¹⁰` challenge space. -/
theorem normalized_hostile_card_bound_eq_separate_denominators
    (cardK cardF p8Work ioWork N M : ℕ) (hk : 0 < cardK) :
    (optimizedHostileProductionFailureCardBound cardK cardF p8Work ioWork N M : ℚ) /
        (cardK ^ 11) =
      optimizedHostileProductionFailureProbabilityBound cardK cardF p8Work ioWork N M := by
  rw [optimizedHostileProductionFailureCardBound_eq_trimmed_shift,
    optimizedHostileProductionFailureProbabilityBound_eq_trimmed_shift]
  exact normalized_trimmed_card_bound_eq_separate_denominators _ _ _ _ _ _ hk

/-- Support transfer to the trimmed reading with the shifted P8 slot. -/
theorem optimizedTrimmedProductionFailure_support_of_hostile
    (cardK cardF p8Work ioWork N M b : ℕ)
    (h : optimizedTrimmedProductionFailureProbabilityBound cardK cardF
      (p8Work + OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
        pricedWalkWork N M)
      (ioWork + (FiniteIO.ioFailureUnionBound 10 M M cardK + cardK * M)) N M
      * 2 ^ b ≤ 1) :
    optimizedHostileProductionFailureProbabilityBound cardK cardF p8Work ioWork N M * 2 ^ b
      ≤ 1 := by
  rw [optimizedHostileProductionFailureProbabilityBound_eq_trimmed_shift]
  exact h

/-- `ioFailureUnionBound` is monotone in both record counts. -/
theorem ioFailureUnionBound_mono₂ (m k₁ k₂ n₁ n₂ cardK : ℕ) (h1 : k₁ ≤ n₁) (h2 : k₂ ≤ n₂) :
    FiniteIO.ioFailureUnionBound m k₁ k₂ cardK ≤ FiniteIO.ioFailureUnionBound m n₁ n₂ cardK := by
  simp only [FiniteIO.ioFailureUnionBound]
  have hs : k₁ + k₂ ≤ n₁ + n₂ := Nat.add_le_add h1 h2
  exact Nat.add_le_add
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul hs hs)))
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hs))

/-- The hostile card bound is monotone in `ioWork`. -/
theorem optimizedHostileProductionFailureCardBound_mono_io
    (cardK cardF p8Work ioWork ioWork' N M : ℕ) (h : ioWork ≤ ioWork') :
    optimizedHostileProductionFailureCardBound cardK cardF p8Work ioWork N M ≤
      optimizedHostileProductionFailureCardBound cardK cardF p8Work ioWork' N M := by
  simp only [optimizedHostileProductionFailureCardBound,
    optimizedTrimmedProductionFailureCardBound]
  gcongr

/-- **The hostile event's card bound.**  At IO records with `|requests| = k₁`, `|responses| = k₂`,
request count `D ≤ 3·N`, and intermediate records with both lists of length `≤ M`: the trimmed
summands plus `|𝕂|⁶ · timestampCollisionBound (3N)` plus `|𝕂|⁵ · interWork(M)`. -/
theorem optimizedHostileProductionFailureEvent_card_le
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M : ℕ}
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (topologyBound axisWorkload : ℕ)
    (hwindow : SizeWindowCounting.SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (famIO : Finset (OptimizedProductionChallengeTuple K F))
    (hfam : famIO.card ≤ Fintype.card K ^ 9 * (FiniteIO.ioFailureUnionBound 10 (3 * N) M (Fintype.card K)))
    (D : ℕ) (hD : D ≤ 3 * N)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F)
    (interRecords : FiniteIO.PreChallengeRecords K 10)
    (memoryEnvF : Fin M → Env F)
    (hinterN : interRecords.requests.length ≤ M)
    (hinterM : interRecords.responses.length ≤ M)
    (walkRoot tilingC tilingM gammaC gammaM forestAlpha : Finset (JointCoins K))
    (hwalk : walkRoot.card ≤ ComputeWalkRootEvents.walkRootBound N * Fintype.card K ^ 3)
    (htileC : tilingC.card ≤ WalkTilingEvents.computeTilingBound N * Fintype.card K ^ 3)
    (htileM : tilingM.card ≤ WalkTilingEvents.memoryTilingBound M * Fintype.card K ^ 3)
    (hγC : gammaC.card ≤ WalkPrefixGammaEvents.computePrefixGammaBound N * Fintype.card K ^ 3)
    (hγM : gammaM.card ≤ WalkPrefixGammaEvents.memoryPrefixGammaBound M * Fintype.card K ^ 3)
    (hαM : forestAlpha.card ≤
      WalkForestPrefixAlphaEvents.memoryForestAlphaBound M * Fintype.card K ^ 3)
    (formRLambda : Finset (OptimizedProductionChallengeTuple K F))
    (hlamEv : formRLambda.card ≤
      Fintype.card K ^ 10 * ProductionP8Containment.formRUniformWorkload T)
    (pairSeeds : Finset (JointCoins K))
    (hpair : pairSeeds.card ≤ ProductionP8Containment.reqPairWorkload T Λ * Fintype.card K ^ 3) :
    (OptimizedHostileProductionFailureEvent T C lmb famIO D computeEnvK computeWalkEnv computeEnvF
      memoryEnvK memoryFamilies interRecords memoryEnvF walkRoot tilingC tilingM gammaC gammaM
        forestAlpha formRLambda pairSeeds).card ≤
      optimizedHostileProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (workload T Λ topologyBound axisWorkload)
        (FiniteIO.ioFailureUnionBound 10 (3 * N) M (Fintype.card K)) N M := by
  have hfour := optimizedTrimmedProductionFailureEvent_card_add_formR_le h2 T C lmb
    topologyBound axisWorkload hwindow htopology haxis (FiniteIO.ioFailureUnionBound 10 (3 * N) M (Fintype.card K)) computeEnvK computeWalkEnv
    computeEnvF memoryEnvK memoryFamilies famIO hfam
  have hwalkLift : (liftP8Failure (F := F) walkRoot).card ≤
      Fintype.card K ^ 10 * ComputeWalkRootEvents.walkRootBound N := by
    have hrest :
        Fintype.card ((K × K) × FinalComputeChallengeTuple K × MemoryChallengeTuple K) =
          Fintype.card K ^ 7 := by
      simp [Fintype.card_prod, card_finalComputeChallengeTuple, card_memoryChallengeTuple]
      ring
    rw [liftP8Failure, Finset.card_product, Finset.card_univ, hrest]
    calc walkRoot.card * Fintype.card K ^ 7
        ≤ ComputeWalkRootEvents.walkRootBound N * Fintype.card K ^ 3 * Fintype.card K ^ 7 :=
          Nat.mul_le_mul_right _ hwalk
      _ = Fintype.card K ^ 10 * ComputeWalkRootEvents.walkRootBound N := by ring
  have htileCLift : (liftP8Failure (F := F) tilingC).card ≤
      Fintype.card K ^ 10 * WalkTilingEvents.computeTilingBound N := by
    have hrest :
        Fintype.card ((K × K) × FinalComputeChallengeTuple K × MemoryChallengeTuple K) =
          Fintype.card K ^ 7 := by
      simp [Fintype.card_prod, card_finalComputeChallengeTuple, card_memoryChallengeTuple]
      ring
    rw [liftP8Failure, Finset.card_product, Finset.card_univ, hrest]
    calc tilingC.card * Fintype.card K ^ 7
        ≤ WalkTilingEvents.computeTilingBound N * Fintype.card K ^ 3 * Fintype.card K ^ 7 :=
          Nat.mul_le_mul_right _ htileC
      _ = Fintype.card K ^ 10 * WalkTilingEvents.computeTilingBound N := by ring
  have htileMLift : (liftP8Failure (F := F) tilingM).card ≤
      Fintype.card K ^ 10 * WalkTilingEvents.memoryTilingBound M := by
    have hrest :
        Fintype.card ((K × K) × FinalComputeChallengeTuple K × MemoryChallengeTuple K) =
          Fintype.card K ^ 7 := by
      simp [Fintype.card_prod, card_finalComputeChallengeTuple, card_memoryChallengeTuple]
      ring
    rw [liftP8Failure, Finset.card_product, Finset.card_univ, hrest]
    calc tilingM.card * Fintype.card K ^ 7
        ≤ WalkTilingEvents.memoryTilingBound M * Fintype.card K ^ 3 * Fintype.card K ^ 7 :=
          Nat.mul_le_mul_right _ htileM
      _ = Fintype.card K ^ 10 * WalkTilingEvents.memoryTilingBound M := by ring
  have hγCLift : (liftP8Failure (F := F) gammaC).card ≤
      Fintype.card K ^ 10 * WalkPrefixGammaEvents.computePrefixGammaBound N := by
    have hrest :
        Fintype.card ((K × K) × FinalComputeChallengeTuple K × MemoryChallengeTuple K) =
          Fintype.card K ^ 7 := by
      simp [Fintype.card_prod, card_finalComputeChallengeTuple, card_memoryChallengeTuple]
      ring
    rw [liftP8Failure, Finset.card_product, Finset.card_univ, hrest]
    calc gammaC.card * Fintype.card K ^ 7
        ≤ WalkPrefixGammaEvents.computePrefixGammaBound N * Fintype.card K ^ 3 *
            Fintype.card K ^ 7 :=
          Nat.mul_le_mul_right _ hγC
      _ = Fintype.card K ^ 10 * WalkPrefixGammaEvents.computePrefixGammaBound N := by ring
  have hγMLift : (liftP8Failure (F := F) gammaM).card ≤
      Fintype.card K ^ 10 * WalkPrefixGammaEvents.memoryPrefixGammaBound M := by
    have hrest :
        Fintype.card ((K × K) × FinalComputeChallengeTuple K × MemoryChallengeTuple K) =
          Fintype.card K ^ 7 := by
      simp [Fintype.card_prod, card_finalComputeChallengeTuple, card_memoryChallengeTuple]
      ring
    rw [liftP8Failure, Finset.card_product, Finset.card_univ, hrest]
    calc gammaM.card * Fintype.card K ^ 7
        ≤ WalkPrefixGammaEvents.memoryPrefixGammaBound M * Fintype.card K ^ 3 *
            Fintype.card K ^ 7 :=
          Nat.mul_le_mul_right _ hγM
      _ = Fintype.card K ^ 10 * WalkPrefixGammaEvents.memoryPrefixGammaBound M := by ring
  have hαMLift : (liftP8Failure (F := F) forestAlpha).card ≤
      Fintype.card K ^ 10 * WalkForestPrefixAlphaEvents.memoryForestAlphaBound M := by
    have hrest :
        Fintype.card ((K × K) × FinalComputeChallengeTuple K × MemoryChallengeTuple K) =
          Fintype.card K ^ 7 := by
      simp [Fintype.card_prod, card_finalComputeChallengeTuple, card_memoryChallengeTuple]
      ring
    rw [liftP8Failure, Finset.card_product, Finset.card_univ, hrest]
    calc forestAlpha.card * Fintype.card K ^ 7
        ≤ WalkForestPrefixAlphaEvents.memoryForestAlphaBound M * Fintype.card K ^ 3 *
            Fintype.card K ^ 7 :=
          Nat.mul_le_mul_right _ hαM
      _ = Fintype.card K ^ 10 * WalkForestPrefixAlphaEvents.memoryForestAlphaBound M := by ring
  have hpairLift : (liftP8Failure (F := F) pairSeeds).card ≤
      Fintype.card K ^ 10 * ProductionP8Containment.reqPairWorkload T Λ := by
    have hrest :
        Fintype.card ((K × K) × FinalComputeChallengeTuple K × MemoryChallengeTuple K) =
          Fintype.card K ^ 7 := by
      simp [Fintype.card_prod, card_finalComputeChallengeTuple, card_memoryChallengeTuple]
      ring
    rw [liftP8Failure, Finset.card_product, Finset.card_univ, hrest]
    calc pairSeeds.card * Fintype.card K ^ 7
        ≤ ProductionP8Containment.reqPairWorkload T Λ * Fintype.card K ^ 3 *
            Fintype.card K ^ 7 :=
          Nat.mul_le_mul_right _ hpair
      _ = Fintype.card K ^ 10 * ProductionP8Containment.reqPairWorkload T Λ := by ring
  have hts : (liftTimestampFailure (F := F)
      (OptimizedHostileTimestamps.TimestampCollisionEvent (K := K) D)).card ≤
      Fintype.card K ^ 10 * OptimizedHostileTimestamps.timestampCollisionBound (3 * N) := by
    rw [card_liftTimestampFailure, mul_comm]
    exact Nat.mul_le_mul_left _
      ((OptimizedHostileTimestamps.TimestampCollisionEvent_card_le_bound D).trans
        (OptimizedHostileTimestamps.timestampCollisionBound_mono hD))
  have hinter : (liftInterPoleFailure (F := F)
      (interFailurePairs interRecords memoryEnvK memoryEnvF)).card ≤
      Fintype.card K ^ 9 * (FiniteIO.ioFailureUnionBound 10 M M (Fintype.card K) +
        Fintype.card K * M) := by
    refine (card_liftInterPoleFailure (F := F) _).trans ?_
    rw [mul_comm]
    refine Nat.mul_le_mul_left _ ?_
    refine (Finset.card_union_le _ _).trans ?_
    refine Nat.add_le_add ?_ ?_
    · exact (FiniteIO.IOFailureEvent_card_le interRecords).trans
        (ioFailureUnionBound_mono₂ 10 interRecords.requests.length interRecords.responses.length
          M M (Fintype.card K) hinterN hinterM)
    · have hcov : allRowPoleHitEvent memoryEnvK memoryEnvF ⊆
          (Finset.univ : Finset K).biUnion (fun γ =>
            ({γ} : Finset K) ×ˢ
              FiniteIO.IOPoleHitEvent
                ⟨List.ofFn (fun i =>
        OptimizedMemoryHostileAccumulator.rowRecord (memoryEnvK i) (memoryEnvF i)), []⟩
                γ) := by
        intro q hq
        simp only [allRowPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        refine Finset.mem_biUnion.mpr ⟨q.1, Finset.mem_univ _, ?_⟩
        exact Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, hq⟩
      refine (Finset.card_le_card hcov).trans ?_
      refine (Finset.card_biUnion_le (s := (Finset.univ : Finset K))
        (t := fun γ => ({γ} : Finset K) ×ˢ
          FiniteIO.IOPoleHitEvent
            ⟨List.ofFn (fun i =>
        OptimizedMemoryHostileAccumulator.rowRecord (memoryEnvK i) (memoryEnvF i)), []⟩
            γ)).trans ?_
      have hsum : ∀ γ ∈ (Finset.univ : Finset K),
          (({γ} : Finset K) ×ˢ
            FiniteIO.IOPoleHitEvent
              ⟨List.ofFn (fun i =>
        OptimizedMemoryHostileAccumulator.rowRecord (memoryEnvK i) (memoryEnvF i)), []⟩
              γ).card ≤ M := by
        intro γ _
        rw [Finset.card_product, Finset.card_singleton, one_mul]
        exact (FiniteIO.IOPoleHitEvent_card_le _ γ).trans (by simp [List.length_ofFn])
      refine (Finset.sum_le_sum hsum).trans ?_
      simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  unfold OptimizedHostileProductionFailureEvent
  have hsplit :
      optimizedHostileProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (workload T Λ topologyBound axisWorkload)
        (FiniteIO.ioFailureUnionBound 10 (3 * N) M (Fintype.card K)) N M =
      optimizedTrimmedProductionFailureCardBound (Fintype.card K) (Fintype.card F)
          (workload T Λ topologyBound axisWorkload)
          (FiniteIO.ioFailureUnionBound 10 (3 * N) M (Fintype.card K)) N M +
        Fintype.card K ^ 10 * OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
        Fintype.card K ^ 9 * (FiniteIO.ioFailureUnionBound 10 M M (Fintype.card K) +
          Fintype.card K * M) +
        Fintype.card K ^ 10 * ComputeWalkRootEvents.walkRootBound N +
        Fintype.card K ^ 10 * WalkTilingEvents.computeTilingBound N +
        Fintype.card K ^ 10 * WalkTilingEvents.memoryTilingBound M +
        Fintype.card K ^ 10 * WalkPrefixGammaEvents.computePrefixGammaBound N +
        Fintype.card K ^ 10 * WalkPrefixGammaEvents.memoryPrefixGammaBound M +
        Fintype.card K ^ 10 * WalkForestPrefixAlphaEvents.memoryForestAlphaBound M := by
    simp only [optimizedHostileProductionFailureCardBound, pricedWalkWork]
    ring
  rw [hsplit]
  have hA :
      (OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
            memoryEnvK memoryFamilies ∪
          famIO ∪
          liftTimestampFailure (OptimizedHostileTimestamps.TimestampCollisionEvent D) ∪
          liftInterPoleFailure (interFailurePairs interRecords memoryEnvK memoryEnvF) ∪
          liftP8Failure walkRoot ∪
          liftP8Failure tilingC ∪
          liftP8Failure tilingM ∪
          liftP8Failure gammaC ∪
          liftP8Failure gammaM ∪
          liftP8Failure forestAlpha).card ≤
        (OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
            memoryEnvK memoryFamilies).card + famIO.card +
        Fintype.card K ^ 10 * OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
        Fintype.card K ^ 9 * (FiniteIO.ioFailureUnionBound 10 M M (Fintype.card K) +
          Fintype.card K * M) +
        Fintype.card K ^ 10 * ComputeWalkRootEvents.walkRootBound N +
        Fintype.card K ^ 10 * WalkTilingEvents.computeTilingBound N +
        Fintype.card K ^ 10 * WalkTilingEvents.memoryTilingBound M +
        Fintype.card K ^ 10 * WalkPrefixGammaEvents.computePrefixGammaBound N +
        Fintype.card K ^ 10 * WalkPrefixGammaEvents.memoryPrefixGammaBound M +
        Fintype.card K ^ 10 * WalkForestPrefixAlphaEvents.memoryForestAlphaBound M := by
    refine (Finset.card_union_le _ _).trans ?_
    refine Nat.add_le_add ?_ hαMLift
    refine (Finset.card_union_le _ _).trans ?_
    refine Nat.add_le_add ?_ hγMLift
    refine (Finset.card_union_le _ _).trans ?_
    refine Nat.add_le_add ?_ hγCLift
    refine (Finset.card_union_le _ _).trans ?_
    refine Nat.add_le_add ?_ htileMLift
    refine (Finset.card_union_le _ _).trans ?_
    refine Nat.add_le_add ?_ htileCLift
    refine (Finset.card_union_le _ _).trans ?_
    refine Nat.add_le_add ?_ hwalkLift
    refine (Finset.card_union_le _ _).trans ?_
    refine Nat.add_le_add ?_ hinter
    refine (Finset.card_union_le _ _).trans ?_
    refine Nat.add_le_add ?_ hts
    exact Finset.card_union_le _ _
  refine (Finset.card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (Finset.card_union_le _ _) _).trans ?_
  omega

theorem optimizedHostileProductionFailureProbability_le
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M : ℕ}
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (topologyBound axisWorkload : ℕ)
    (hwindow : SizeWindowCounting.SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (famIO : Finset (OptimizedProductionChallengeTuple K F))
    (hfam : famIO.card ≤ Fintype.card K ^ 9 * (FiniteIO.ioFailureUnionBound 10 (3 * N) M (Fintype.card K)))
    (D : ℕ) (hD : D ≤ 3 * N)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F)
    (interRecords : FiniteIO.PreChallengeRecords K 10)
    (memoryEnvF : Fin M → Env F)
    (hinterN : interRecords.requests.length ≤ M)
    (hinterM : interRecords.responses.length ≤ M)
    (walkRoot tilingC tilingM gammaC gammaM forestAlpha : Finset (JointCoins K))
    (hwalk : walkRoot.card ≤ ComputeWalkRootEvents.walkRootBound N * Fintype.card K ^ 3)
    (htileC : tilingC.card ≤ WalkTilingEvents.computeTilingBound N * Fintype.card K ^ 3)
    (htileM : tilingM.card ≤ WalkTilingEvents.memoryTilingBound M * Fintype.card K ^ 3)
    (hγC : gammaC.card ≤ WalkPrefixGammaEvents.computePrefixGammaBound N * Fintype.card K ^ 3)
    (hγM : gammaM.card ≤ WalkPrefixGammaEvents.memoryPrefixGammaBound M * Fintype.card K ^ 3)
    (hαM : forestAlpha.card ≤
      WalkForestPrefixAlphaEvents.memoryForestAlphaBound M * Fintype.card K ^ 3)
    (formRLambda : Finset (OptimizedProductionChallengeTuple K F))
    (hlamEv : formRLambda.card ≤
      Fintype.card K ^ 10 * ProductionP8Containment.formRUniformWorkload T)
    (pairSeeds : Finset (JointCoins K))
    (hpair : pairSeeds.card ≤ ProductionP8Containment.reqPairWorkload T Λ * Fintype.card K ^ 3) :
    ((OptimizedHostileProductionFailureEvent T C lmb famIO D computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies interRecords memoryEnvF walkRoot tilingC tilingM gammaC gammaM
          forestAlpha formRLambda pairSeeds).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤
      optimizedHostileProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
        (workload T Λ topologyBound axisWorkload)
        (FiniteIO.ioFailureUnionBound 10 (3 * N) M (Fintype.card K)) N M := by
  have hcard := optimizedHostileProductionFailureEvent_card_le h2 T C lmb topologyBound
    axisWorkload hwindow htopology haxis famIO hfam D hD computeEnvK computeWalkEnv computeEnvF
    memoryEnvK memoryFamilies interRecords memoryEnvF hinterN hinterM walkRoot tilingC tilingM
    gammaC gammaM forestAlpha hwalk htileC htileM hγC hγM hαM formRLambda hlamEv pairSeeds hpair
  have hcast :
      ((OptimizedHostileProductionFailureEvent T C lmb famIO D computeEnvK computeWalkEnv
          computeEnvF memoryEnvK memoryFamilies interRecords memoryEnvF walkRoot tilingC tilingM
          gammaC gammaM forestAlpha formRLambda pairSeeds).card : ℚ) ≤
        optimizedHostileProductionFailureCardBound (Fintype.card K) (Fintype.card F)
          (workload T Λ topologyBound axisWorkload)
          (FiniteIO.ioFailureUnionBound 10 (3 * N) M (Fintype.card K)) N M := by
    exact_mod_cast hcard
  rw [card_optimizedProductionChallengeTuple]
  norm_num only [Nat.cast_pow]
  calc
    ((OptimizedHostileProductionFailureEvent T C lmb famIO D computeEnvK computeWalkEnv
        computeEnvF memoryEnvK memoryFamilies interRecords memoryEnvF walkRoot tilingC tilingM
        gammaC gammaM forestAlpha formRLambda pairSeeds).card : ℚ) / (Fintype.card K ^ 11)
        ≤ (optimizedHostileProductionFailureCardBound (Fintype.card K) (Fintype.card F)
            (workload T Λ topologyBound axisWorkload)
            (FiniteIO.ioFailureUnionBound 10 (3 * N) M (Fintype.card K)) N M : ℚ) / (Fintype.card K ^ 11) :=
      div_le_div_of_nonneg_right hcast (by positivity)
    _ = _ := normalized_hostile_card_bound_eq_separate_denominators _ _ _ _ _ _
      Fintype.card_pos

/-!

`…_extension`, `…_merged` (`KD`, `+ (20 + 14·M)/|𝔽|`) and the
legacy `61·M` reading are **weaker upper bounds** and are recovered from the consumed one by
the `…ProbabilityBound_le` comparisons alone. -/


theorem optimizedExtensionProductionFailureProbability_le
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M : ℕ}
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (topologyBound axisWorkload : ℕ)
    (hwindow : SizeWindowCounting.SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (ioWork : ℕ)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F) :
    ((OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤
      optimizedExtensionProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
        (workload T Λ topologyBound axisWorkload)
        ioWork N M :=
  (optimizedTrimmedProductionFailureProbability_le h2 T C lmb topologyBound axisWorkload hwindow
    htopology haxis ioWork computeEnvK computeWalkEnv computeEnvF memoryEnvK memoryFamilies).trans
    (optimizedTrimmedProductionFailureProbabilityBound_le _ _ _ _ _ _)


theorem optimizedMergedProductionFailureProbability_le
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M : ℕ}
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (topologyBound axisWorkload : ℕ)
    (hwindow : SizeWindowCounting.SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (ioWork : ℕ)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F) :
    ((OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤
      optimizedMergedProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
        (workload T Λ topologyBound axisWorkload)
        ioWork N M :=
  (optimizedExtensionProductionFailureProbability_le h2 T C lmb topologyBound axisWorkload hwindow
    htopology haxis ioWork computeEnvK computeWalkEnv computeEnvF memoryEnvK memoryFamilies).trans
    (optimizedExtensionProductionFailureProbabilityBound_le _ _ _ _ _ _)


theorem optimizedProductionFailureProbability_le
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M : ℕ}
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (topologyBound axisWorkload : ℕ)
    (hwindow : SizeWindowCounting.SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (ioWork : ℕ)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F) :
    ((OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple K F) ≤
      optimizedProductionFailureProbabilityBound (Fintype.card K) (Fintype.card F)
        (workload T Λ topologyBound axisWorkload)
        ioWork N M :=
  (optimizedMergedProductionFailureProbability_le h2 T C lmb topologyBound axisWorkload hwindow
    htopology haxis ioWork computeEnvK computeWalkEnv computeEnvF memoryEnvK memoryFamilies).trans
    (optimizedMergedProductionFailureProbabilityBound_le _ _ _ _ _ _ Fintype.card_pos)


theorem normalized_merged_card_bound_eq_separate_denominators
    (cardK cardF p8Work ioWork N M : ℕ)
    (hk : 0 < cardK) (hf : 0 < cardF) :
    (optimizedMergedProductionFailureCardBound cardK cardF p8Work ioWork N M : ℚ) /
        (cardK ^ 9 * cardF) =
      optimizedMergedProductionFailureProbabilityBound cardK cardF p8Work ioWork N M := by
  have hkq : (cardK : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hfq : (cardF : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hf
  simp only [optimizedMergedProductionFailureCardBound,
    optimizedMergedProductionFailureProbabilityBound, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow]
  field_simp
  ring


theorem normalized_extension_card_bound_eq_separate_denominators
    (cardK cardF p8Work ioWork N M : ℕ)
    (hk : 0 < cardK) (hf : 0 < cardF) :
    (optimizedExtensionProductionFailureCardBound cardK cardF p8Work ioWork N M : ℚ) /
        (cardK ^ 9 * cardF) =
      optimizedExtensionProductionFailureProbabilityBound cardK cardF p8Work ioWork N M := by
  have hkq : (cardK : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hfq : (cardF : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hf
  simp only [optimizedExtensionProductionFailureCardBound,
    optimizedExtensionProductionFailureProbabilityBound, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow]
  field_simp
  ring


/-! ## Replacement capstone -/

/-- Replacement Theorem-5.4 strict statement. S5/S8 are the two optimized same-assignment
realizations and exact fixed-preprocessing resources; S7 is the complete four-class product-space
event theorem above. -/
structure OptimizedStrictThm54Statement
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedStrictNockVMROMPackage F K hOrb) : Prop where
  sameExecution :
    P.family.problem.cfg = P.objects.cfg ∧ HEq P.family.problem.exec P.objects.exec
  structuralResiduals : P.OptimizedStrictStructuralResiduals
  optimizedChips :
    OptimizedComputeRealizationAt P.sampled P.computeObligations P.computeNodes P.basis
        P.computeChallenge P.computePublic P.orbit ∧
      OptimizedMemoryRealizationAt P.sampled P.memoryProduction P.memoryNodes P.basis
        P.memoryChallenge P.memoryPublic P.orbit
  exactResources :
    let C := ProductionNamedComputeRAP P.family.problem.cfg.compRows_pos P.computeNodes
      P.basis P.computeChallenge P.computePublic P.orbit
    let M := namedFinalMemoryRAP P.family.problem.cfg.memRows_pos P.memoryNodes
      P.basis P.memoryChallenge P.memoryPublic P.orbit P.family.problem.cfg.kMem
    C.rap.w = 303 ∧ C.rap.s = 418 ∧ C.rap.d = 4 ∧ C.rap.k = 2 ∧
      M.rap.w = 205 ∧ M.rap.s = 156 ∧ M.rap.d = 4 ∧ M.rap.k = 1
  sharedForestAxis : P.OptimizedSharedMemoryConnective
  completeS7 :
    ∀ {N M : ℕ} (lmb : K)
      (topologyBound axisWorkload : ℕ)
      (_htopology :
        ∀ z (hz : z ≠ 0) α lmb,
          topologyWorkload
            (P.strategy.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
      (_haxis :
        ∀ z (hz : z ≠ 0),
          templateAxisWorkload (committedTemplate P.strategy.verifier z hz) ≤ axisWorkload)
      (ioWork : ℕ)
      (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
      (memoryEnvK : Fin M → Env K)
      (memoryFamilies : Fin M → Fin 7 → Fin 3 → F),
      (OptimizedProductionFailureEvent P.strategy P.census lmb computeEnvK
        computeWalkEnv computeEnvF memoryEnvK memoryFamilies).card ≤
        optimizedTrimmedProductionFailureCardBound (Fintype.card K) (Fintype.card F)
          (workload P.strategy P.Λ topologyBound axisWorkload)
          ioWork N M

theorem optimizedStrictNockVMROM_of_package
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedStrictNockVMROMPackage F K hOrb)
    (hax : FormRAxisBound P.sampled P.basis)
    (hbasis : FormRBasis P.basis)
    (hwidth : FormRWidth F) :
    OptimizedStrictThm54Statement P where
  sameExecution := ⟨P.family_cfg, P.family_exec⟩
  structuralResiduals := P.structural_residuals
  optimizedChips := P.realization_surface_is_optimized hax hbasis hwidth
  exactResources := P.exact_chip_resources
  sharedForestAxis := P.shared_memory_connective
  completeS7 := by
    intro N M lmb topologyBound axisWorkload htopology haxis ioWork computeEnvK computeWalkEnv
      computeEnvF memoryEnvK memoryFamilies
    exact optimizedMergedProductionFailureEvent_card_le P.two_ne_zero P.strategy P.census lmb
      topologyBound axisWorkload P.sizeWindowBound htopology haxis ioWork computeEnvK
      computeWalkEnv computeEnvF memoryEnvK memoryFamilies

#print axioms OptimizedStrictNockVMROMPackage.exact_chip_resources_paper
#print axioms OptimizedStrictNockVMROMPackage.exact_transition_fingerprints_paper
#print axioms optimizedProductionFailureEvent_card_le
#print axioms optimizedMergedProductionFailureEvent_card_le
#print axioms optimizedMergedProductionFailureProbability_le
#print axioms OptimizedStrictNockVMROMPackage.memory_extension_event_to_fold_excluded
#print axioms optimizedStrictNockVMROM_of_package

end
end OptimizedStrictPackage
end Nock.NockVMROM.Thm54
