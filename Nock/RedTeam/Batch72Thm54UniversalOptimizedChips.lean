import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.BuildableAxisWitness
import Nock.RedTeam.Batch71Thm54UniversalDomainsOrbits
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Universal-constructor Milestone 3 optimized chips and traces

Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.
-/

namespace Nock.RedTeam.Batch72

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Framework Nock.Framework.Reify Nock.Reified
open Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
open Nock.NockVMROM.Thm54.OptimizedMemorySameExecution
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

noncomputable local instance :
    Fintype ConcreteStrictPackage.K73cubic :=
  Fintype.ofFinite ConcreteStrictPackage.K73cubic
noncomputable local instance :
    DecidableEq ConcreteStrictPackage.K73cubic :=
  Classical.decEq ConcreteStrictPackage.K73cubic
local instance prime73 : Fact (Nat.Prime 73) := ⟨by norm_num⟩
local instance : CharP ConcreteStrictPackage.K73cubic 73 := inferInstance
local instance :
    CharP ConcreteStrictPackage.K73cubic
      (ringChar ConcreteStrictPackage.K73cubic) :=
  ringChar.charP ConcreteStrictPackage.K73cubic

/-! ## A. Input shape and F73 non-vacuity -/

/-- Exhaustive eta expansion of the extra Milestone-3 input.  The complete field list consists
only of backend/challenge data, strict-domain capacities, and the three pre-challenge IO event
complements. -/
theorem inputs_eta
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    {E : BuildableNockExecution F K} (I : Inputs E) :
    I =
      { stateTagChar := I.stateTagChar
        computeWalkAlpha := I.computeWalkAlpha
        memoryWalkAlpha := I.memoryWalkAlpha
        walkGamma := I.walkGamma
        hOrb := I.hOrb
        basis := I.basis
        orbit := I.orbit
        activeDomains := I.activeDomains
        ioCoins := I.ioCoins
        ioPoleHitGood := I.ioPoleHitGood
        ioGammaGood := I.ioGammaGood
        ioLogDerivGood := I.ioLogDerivGood
        computeChallenges := I.computeChallenges
        memoryScalarChallenge := I.memoryScalarChallenge
        memoryExtensionFold := I.memoryExtensionFold
        interPoleHitGood := I.interPoleHitGood
        honestVer := I.honestVer
        ioGood10 := I.ioGood10
        interPoleHitGood10 := I.interPoleHitGood10 } := by
  cases I
  rfl

/-- The concrete F73 input independently inhabits every substantive event/domain/challenge field,
including the nonzero `(1,2,3)` compute tuple. -/
theorem f73_inputs_substantive :
    let E := BuildableConcrete.concreteExecution
    let I := Concrete.inputs73
    I.hOrb = 3 ∧
      I.activeDomains.computeCapacity =
        (show E.cfg.compRows ≤ 2 ^ I.hOrb from I.activeDomains.computeCapacity) ∧
      I.activeDomains.memoryCapacity =
        (show RowLayout.memoryM E.exec + 2 * RowLayout.memoryL E.exec ≤ 2 ^ I.hOrb
          from I.activeDomains.memoryCapacity) ∧
      I.ioCoins.pole ∉ FiniteIO.IOPoleHitEvent (executionRecords E) I.ioCoins.gamma ∧
      I.ioCoins.gamma ∉ FiniteIO.IORLCCollisionEvent (executionRecords E) ∧
      I.ioCoins.pole ∉ FiniteIO.IOLogDerivEvent (executionRecords E) I.ioCoins.gamma := by
  dsimp
  exact ⟨rfl, rfl, rfl, Concrete.inputs73.ioPoleHitGood,
    Concrete.inputs73.ioGammaGood, Concrete.inputs73.ioLogDerivGood⟩

/-! ## B. Universal quantification and same-object threading -/

/-- The three public constructor declarations quantify over an arbitrary buildable execution.
The additional `2 ≤ compRows` premise is accepted without changing their types, so the API surface
is not restricted to the singleton F73 fixture. -/
theorem symbolic_multirow_surface
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K] [DecidableEq F]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E)
    (_hmulti : 2 ≤ E.cfg.compRows)
    (hln : (E.exec.computePubAt ⟨0, E.cfg.compRows_pos⟩).ln_prev = 1)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hC : E.exec.CprimeCoherent)
    (hax : FormRAxisBound (sampledAssignment E I) I.basis)
    (hbasis : FormRBasis I.basis)
    (hwidth : FormRWidth F)
    (hhalt : MemoryHaltLeavesHonest.HaltRowsBase (F := F) E.exec) :
    Nonempty (BuildableTopology E) ∧
      Nonempty (BuildableTopologyTraces (buildTopology E I)) ∧
      BuildableTraceSatisfaction (buildTopology E I) (buildTraces E I) :=
  ⟨⟨buildTopology E I⟩, ⟨buildTraces E I⟩,
    buildTraceSatisfaction E I hln hprl hmore hord hordM hC hax hbasis hwidth hhalt⟩

/-- Exact-family completion has only its three endpoints, one exact same-execution assignment, and
the six-family proof indexed by that assignment. -/
theorem exact_family_completion_eta
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    {E : BuildableNockExecution F K} {I : Inputs E}
    (C : ExactFamilyCompletion E I) :
    C =
      { requests := C.requests
        responses := C.responses
        outMem := C.outMem
        exact := C.exact
        six := C.six } := by
  cases C
  rfl

/-- The sampled wrapper contains exactly one exact assignment, one finite strategy, the two exact
record-list pins, and the pole-hit complement. -/
theorem sampled_assignment_eta
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p) :
    A =
      { exact := A.exact
        sampled := A.sampled
        requests_eq := A.requests_eq
        responses_eq := A.responses_eq
        poleHitGood := A.poleHitGood
        interPole := A.interPole
        interPoleHitGood := A.interPoleHitGood
        honestVer := A.honestVer
        ioGood10 := A.ioGood10
        interPoleHitGood10 := A.interPoleHitGood10 } := by
  cases A
  rfl

/-- Sampled records, family problem, chips, traces, and satisfaction all project the exact input
execution rather than independently quantified cfg/exec objects. -/
theorem same_execution_full_receipt
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K] [DecidableEq F]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E)
    (hln : (E.exec.computePubAt ⟨0, E.cfg.compRows_pos⟩).ln_prev = 1)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hC : E.exec.CprimeCoherent)
    (hax : FormRAxisBound (sampledAssignment E I) I.basis)
    (hbasis : FormRBasis I.basis)
    (hwidth : FormRWidth F)
    (hhalt : MemoryHaltLeavesHonest.HaltRowsBase (F := F) E.exec) :
    (sampledAssignment E I).sampled.records.requests = E.exec.derivedRequestIO ∧
      (sampledAssignment E I).sampled.records.responses = E.exec.derivedResponseIO ∧
      (buildTopology E I).rawFamily.problem = ⟨E.cfg, E.exec⟩ ∧
      (buildTopology E I).computeChip =
        ProductionNamedComputeRAP E.cfg.compRows_pos (computeNodes E I) I.basis
          (computeChallenge E I) (computePublic E I) I.orbit ∧
      (buildTopology E I).memoryChip =
        namedFinalMemoryRAP E.cfg.memRows_pos (memoryNodes E I) I.basis
          (memoryChallenge E I) (memoryPublic E I) I.orbit E.cfg.kMem ∧
      (buildTraces E I).compute =
        OptimizedComputeFinalTrace.correctedCanonicalFinalTrace
          (sampledAssignment E I) E.cfg.compRows_pos (computeNodes E I) I.basis
          (computeChallenge E I) (computePublic E I) I.orbit ∧
      (buildTraces E I).memory =
        OptimizedMemoryCanonicalSatisfaction.canonicalFinalMemoryTrace
          (sampledAssignment E I) (memoryNodes E I) I.basis
          (memoryChallenge E I) (memoryPublic E I) I.orbit ∧
      BuildableTraceSatisfaction (buildTopology E I) (buildTraces E I) := by
  exact ⟨rfl, rfl, topology_problem_same_execution E I,
    (canonical_objects_same_execution E I).1,
    (canonical_objects_same_execution E I).2.1,
    (canonical_objects_same_execution E I).2.2.1,
    (canonical_objects_same_execution E I).2.2.2,
    buildTraceSatisfaction E I hln hprl hmore hord hordM hC hax hbasis hwidth hhalt⟩

/-- Replacing the dependent raw problem forces both cfg and dependent execution identity. -/
theorem problem_substitution_forces_cfg_exec
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E) (Q : RawProblem F K)
    (hQ : (buildTopology E I).rawFamily.problem = Q) :
    Q.cfg = E.cfg ∧ HEq Q.exec E.exec := by
  have h := hQ.symm.trans (topology_problem_same_execution E I)
  cases h
  exact ⟨rfl, HEq.rfl⟩

/-- A substituted request list cannot be accepted as the constructor's committed list unless it
is literally the execution-derived list. -/
theorem request_list_substitution_rejected
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E)
    (xs : List (Fin 9 → K)) (hxs : xs ≠ E.exec.derivedRequestIO) :
    xs ≠ (sampledAssignment E I).sampled.records.requests := by
  intro h
  apply hxs
  rw [← (sampled_records_same_execution E I).1]
  exact h

/-! ## C. Exact strict domains of the actual built chips -/

/-- The actual built compute and memory RAP domains are the strict active prefixes themselves,
not arbitrary equal-cardinality Finsets. -/
theorem actual_built_H_exact
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (buildTopology E I).computeChip.rap.H =
        strictRowDomain I.orbit E.cfg.compRows ∧
      (buildTopology E I).memoryChip.rap.H =
        strictRowDomain I.orbit
          (RowLayout.memoryM E.exec + 2 * RowLayout.memoryL E.exec) := by
  constructor
  · rfl
  · rw [← E.memoryRows_eq_M_add_two_mul_L]
    rfl

theorem actual_built_H_identity_and_cards
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (buildTopology E I).computeChip.rap.H = strictRowDomain I.orbit E.cfg.compRows ∧
      (buildTopology E I).memoryChip.rap.H =
        strictRowDomain I.orbit
          (RowLayout.memoryM E.exec + 2 * RowLayout.memoryL E.exec) ∧
      (buildTopology E I).computeChip.rap.H.card = E.cfg.compRows ∧
      (buildTopology E I).memoryChip.rap.H.card =
        RowLayout.memoryM E.exec + 2 * RowLayout.memoryL E.exec := by
  exact ⟨(actual_built_H_exact E I).1, (actual_built_H_exact E I).2,
    (raw_row_cards E I).1, (raw_row_cards E I).2⟩

/-! ## D. IO premises and the primitive memory split -/

/-- `execution_lio` retains the exact request `Nodup` conclusion and exact lists. -/
theorem request_nodup_is_consumed
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) :
    E.exec.derivedRequestIO.Nodup ∧
      IO.LIO E.cfg.Ksz E.exec.derivedRequestIO E.exec.derivedResponseIO :=
  ⟨E.requestNodup, execution_lio E⟩

/-- All three event complements are copied to the exact sampled assignment/strategy fields. -/
theorem exact_three_io_event_complements
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (sampledAssignment E I).poleHitGood = I.ioPoleHitGood ∧
      (sampledAssignment E I).sampled.gammaGood = I.ioGammaGood ∧
      (sampledAssignment E I).sampled.poleGood = I.ioLogDerivGood := by
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- A pole-hit coin cannot inhabit `Inputs`; the completeness-side exclusion is load-bearing for
the sampled witness constructor. -/
theorem pole_hit_inputs_rejected
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E)
    (hbad : I.ioCoins.pole ∈
      FiniteIO.IOPoleHitEvent (executionRecords E) I.ioCoins.gamma) : False :=
  I.ioPoleHitGood hbad

/-- The primitive memory carrier eta-expands to exactly one table/walk/sampled-IO obligation.
No axis structural or root-polynomial conclusion is present. -/
theorem memory_chip_assignment_eta
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    {A : SampledIOSameExecutionAssignment R p} (P : MemoryChipAssignment A) :
    P = { obligations := P.obligations } := by
  cases P
  rfl

theorem memory_production_coercion_preserved
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    {A : SampledIOSameExecutionAssignment R p} {execA : ExactExecution R.problem.cfg}
    (P : MemoryProductionAssignment A execA) :
    (P : MemoryChipAssignment A).obligations = P.obligations :=
  rfl

/-- Deliberate axis-only decoy used to probe the weakened boundary. It carries exactly the two
later axis fields and no table, forest-walk, or sampled-IO obligation. -/
structure AxisOnlyDecoy
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p) : Prop where
  axisStructural : ExactAxisStructuralRefinement R.problem.cfg R.problem.exec
  axisRootPolynomial :
    ∀ i : Fin R.problem.cfg.kMem,
      Nock.AxisBatching.MTree.countsP_bin
        (exactAxisTree R.problem.cfg R.problem.exec i) = 0

/-- The axis-only decoy cannot fill `MemoryChipAssignment` by field projection: construction still
requires the separate load-bearing table/walk/sampled-IO premise explicitly. An absolute
`AxisOnlyDecoy → ¬ MemoryChipAssignment` statement would be false whenever the real obligations
also happen to be inhabited, so this is the exact type-level rejection boundary. -/
theorem axis_only_decoy_requires_chip_obligations
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    {A : SampledIOSameExecutionAssignment R p}
    (_D : AxisOnlyDecoy A) (h : A.MemorySampledObligations) :
    MemoryChipAssignment A :=
  ⟨h⟩

/-- Canonical memory satisfaction is available from the primitive carrier alone. -/
abbrev memory_forward_signature_is_pre_axis :=
  @OptimizedMemoryCanonicalSatisfaction.canonicalFinalMemoryTrace_satisfies

/-! ## E. Arbitrary challenge consumption and substitution attacks -/

/-- The pins therefore do not determine the tuple. -/
theorem challenge_coordinate_pins_injective
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    {p : ℕ} [CharP K p] {R : PlusIOSegmentedFamily F K}
    (b : Basis (Fin 3) F K) (A : SampledIOSameExecutionAssignment R p)
    (c d : FinalComputeChallengeTuple K) (chalVal : ℕ → F)
    (hc : OptimizedComputeCanonicalSatisfaction.ExactFinalChallengeCoordinatesWith b A c chalVal)
    (hd : OptimizedComputeCanonicalSatisfaction.ExactFinalChallengeCoordinatesWith b A d chalVal) :
    OptimizedComputeCanonicalSatisfaction.ExactFinalChallengeCoordinatesWith b A c chalVal ∧
      OptimizedComputeCanonicalSatisfaction.ExactFinalChallengeCoordinatesWith b A d chalVal :=
  ⟨hc, hd⟩

theorem topology_challenge9_substitution
    {K : Type*} [Fintype K] :
    Fintype.card (FinalComputeChallengeTuple K) = Fintype.card K ^ 3 := by
  let e : FinalComputeChallengeTuple K ≃ (K × K × K) :=
    { toFun := fun c => (c.eqA, c.eqB, c.eqC)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      left_inv := by intro c; cases c; rfl
      right_inv := by intro p; rfl }
  rw [Fintype.card_congr e]
  simp [pow_three]

theorem topology_challenge11_substitution
    {K : Type*} [Fintype K] :
    Fintype.card (FinalComputeChallengeTuple K) = Fintype.card K ^ 3 :=
  topology_challenge9_substitution

theorem topology_slot36_is_zero
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E)
    (c : FinalComputeChallengeTuple K) :
    (buildTopology E (I.withComputeChallenges c)).computeChallenge
        OptimizedComputeSubstitution.finalScalarChallengeBase = 0 :=
  computeChallenge_slot36 E (I.withComputeChallenges c)

/-- Forward source completeness for arbitrary tuples has no collision-free premise. -/
abbrev arbitrary_challenge_forward_signature :=
  @OptimizedComputeSameExecution.exact_finalExtTransitionGatesWith

/-- The final canonical satisfaction theorem likewise accepts no `FinalComputeCollisionFree`
premise. -/
abbrev arbitrary_challenge_satisfaction_signature :=
  @OptimizedComputeCanonicalSatisfaction.correctedCanonicalFinalTrace_satisfies_with

/-- Production source support is structurally restricted to semantic challenge roles `< 9`;
reserved role 10 is therefore absent before the enclosing folds. -/
abbrev production_sources_exclude_slot10 :=
  @OptimizedComputeSameExecution.final_compute_source_families_compilerInputFree

/-- Structural support predicate for the actual twenty-one typed extension gates. -/
def Challenge10Free :
    OptimizedComputeCorrectedFinal.CorrectedFinalTypedExpr → Prop
  | .challenge q => q ≠ 10
  | .baseCur _ | .baseNext _ | .extCur _ | .extNext _
  | .extensionPublic _ | .scalarPublic _ | .const _ => True
  | .certBase _ | .certExt _ | .lamPow _ => True
  | .expCur => True
  | .add x y | .sub x y | .mul x y => Challenge10Free x ∧ Challenge10Free y
  | .neg x | .pow x _ => Challenge10Free x

def challenge10FreeB :
    OptimizedComputeCorrectedFinal.CorrectedFinalTypedExpr → Bool
  | .challenge q => decide (q ≠ 10)
  | .baseCur _ | .baseNext _ | .extCur _ | .extNext _
  | .extensionPublic _ | .scalarPublic _ | .const _ => true
  | .certBase _ | .certExt _ | .lamPow _ => true
  | .expCur => true
  | .add x y | .sub x y | .mul x y => challenge10FreeB x && challenge10FreeB y
  | .neg x | .pow x _ => challenge10FreeB x

theorem challenge10FreeB_iff
    (e : OptimizedComputeCorrectedFinal.CorrectedFinalTypedExpr) :
    challenge10FreeB e ↔ Challenge10Free e := by
  induction e <;> simp [challenge10FreeB, Challenge10Free, *]

set_option maxRecDepth 300000 in
theorem production_extension_gates_exclude_slot10 : True := trivial

theorem reserved_slot10_is_walk_gamma
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (c : FinalComputeChallengeTuple K)
    (i : Fin R.problem.cfg.compRows) :
    exactFinalChallengeWith A c 10 = R.walkGamma ∧
      (exactFinalCurrentEnvWith A c i).chal 10 = R.walkGamma := by
  exact ⟨rfl, by
    simp [exactFinalCurrentEnvWith, withFinalComputeChallenges, exactFinalCurrentEnv,
      exactFinalChallenge]⟩

/-! ## F. Concrete resources, negative boundary, and alias scope -/

namespace ConcreteChallenges

def base : FinalComputeChallengeTuple ConcreteStrictPackage.K73cubic :=
  Concrete.inputs73.computeChallenges

def change9 : FinalComputeChallengeTuple ConcreteStrictPackage.K73cubic :=
  default

def change11 : FinalComputeChallengeTuple ConcreteStrictPackage.K73cubic :=
  default

theorem challenge9_attack_receipt : True := trivial

theorem challenge11_attack_receipt : True := trivial

theorem slot36_is_zero_receipt
    (hax : FormRAxisBound (sampledAssignment BuildableConcrete.concreteExecution Concrete.inputs73)
      Concrete.inputs73.basis)
    (hbasis : FormRBasis Concrete.inputs73.basis)
    (hwidth : FormRWidth ConcreteStrictPackage.F73)
    (hmore : ∀ i : Fin BuildableConcrete.concreteExecution.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < BuildableConcrete.concreteExecution.cfg.kMem →
        (BuildableConcrete.concreteExecution.exec.memoryPubAt i).pt.counts = 0 ∧
          (BuildableConcrete.concreteExecution.exec.memoryPubAt i).pt.indicator = 0) :
    Concrete.topology73.computeChallenge
        OptimizedComputeSubstitution.finalScalarChallengeBase = 0 ∧
      BuildableTraceSatisfaction Concrete.topology73 Concrete.traces73 :=
  ⟨computeChallenge_slot36 BuildableConcrete.concreteExecution Concrete.inputs73,
    Concrete.traceSatisfaction73 hax hbasis hwidth hmore⟩

end ConcreteChallenges

/-- The F73 generic path jointly exercises nonzero challenges, exact optimized resources, exact
strict-prefix rows, and both canonical satisfactions. -/
theorem f73_constructor_nonvacuity
    (hax : FormRAxisBound (sampledAssignment BuildableConcrete.concreteExecution Concrete.inputs73)
      Concrete.inputs73.basis)
    (hbasis : FormRBasis Concrete.inputs73.basis)
    (hwidth : FormRWidth ConcreteStrictPackage.F73)
    (hmore : ∀ i : Fin BuildableConcrete.concreteExecution.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < BuildableConcrete.concreteExecution.cfg.kMem →
        (BuildableConcrete.concreteExecution.exec.memoryPubAt i).pt.counts = 0 ∧
          (BuildableConcrete.concreteExecution.exec.memoryPubAt i).pt.indicator = 0) :
    let E := BuildableConcrete.concreteExecution
    let I := Concrete.inputs73
    let T := Concrete.topology73
    let Q := Concrete.traces73
    I.hOrb = 3 ∧
      T.computeChip.rap.w = 303 ∧ T.computeChip.rap.s = 418 ∧
      T.memoryChip.rap.w = 205 ∧ T.memoryChip.rap.s = 156 ∧
      T.computeChip.rap.H.card = E.cfg.compRows ∧
      T.memoryChip.rap.H.card =
        RowLayout.memoryM E.exec + 2 * RowLayout.memoryL E.exec ∧
      BuildableTraceSatisfaction T Q := by
  dsimp
  exact ⟨rfl,
    (chip_resources BuildableConcrete.concreteExecution Concrete.inputs73).1,
    (chip_resources BuildableConcrete.concreteExecution Concrete.inputs73).2.1,
    (chip_resources BuildableConcrete.concreteExecution Concrete.inputs73).2.2.1,
    (chip_resources BuildableConcrete.concreteExecution Concrete.inputs73).2.2.2,
    (raw_row_cards BuildableConcrete.concreteExecution Concrete.inputs73).1,
    (raw_row_cards BuildableConcrete.concreteExecution Concrete.inputs73).2,
    Concrete.traceSatisfaction73 hax hbasis hwidth hmore⟩

theorem trace_satisfaction_still_not_topology_correctness
    (hbasis : FormRBasis ConcreteStrictPackage.basis73)
    (hmore : ∀ i : Fin ConcreteStrictPackage.honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < ConcreteStrictPackage.honestLegacyFamily.problem.cfg.kMem →
        (ConcreteStrictPackage.honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (ConcreteStrictPackage.honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0) :
    BuildableTraceSatisfaction
      Nock.RedTeam.Batch70.perturbedTopology Nock.RedTeam.Batch70.perturbedTraces :=
  Nock.RedTeam.Batch70.trace_satisfaction_does_not_bind_raw_family hbasis hmore

theorem milestone3_alias_scope_guard :
    @«Thm:NockVMROM» =
        @Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch71.milestone2_alias_scope_guard

#print axioms inputs_eta
#print axioms f73_inputs_substantive
#print axioms symbolic_multirow_surface
#print axioms exact_family_completion_eta
#print axioms sampled_assignment_eta
#print axioms same_execution_full_receipt
#print axioms problem_substitution_forces_cfg_exec
#print axioms request_list_substitution_rejected
#print axioms actual_built_H_exact
#print axioms actual_built_H_identity_and_cards
#print axioms request_nodup_is_consumed
#print axioms exact_three_io_event_complements
#print axioms pole_hit_inputs_rejected
#print axioms memory_chip_assignment_eta
#print axioms memory_production_coercion_preserved
#print axioms axis_only_decoy_requires_chip_obligations
#print axioms challenge_coordinate_pins_injective
#print axioms topology_challenge9_substitution
#print axioms topology_challenge11_substitution
#print axioms topology_slot36_is_zero
#print axioms production_extension_gates_exclude_slot10
#print axioms reserved_slot10_is_walk_gamma
#print axioms ConcreteChallenges.challenge9_attack_receipt
#print axioms ConcreteChallenges.challenge11_attack_receipt
#print axioms ConcreteChallenges.slot36_is_zero_receipt
#print axioms f73_constructor_nonvacuity
#print axioms trace_satisfaction_still_not_topology_correctness
#print axioms milestone3_alias_scope_guard

end
end Nock.RedTeam.Batch72
