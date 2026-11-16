import Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
import Nock.NockVMROM.Thm54.GlobalOpcodeScheduling
import Nock.NockVMROM.Thm54.PointwiseBridge
import Nock.NockVMROM.Thm54.SizeWindowCounting
import Nock.NockVMROM.Thm54.TemplateMemoryWalkCounting
import Nock.NockVMROM.Thm54.FormRTemplatePolynomial

/-!
# Production P8 false-acceptance containment

This is the final assembly over the phase-authenticated, topology-enabled raw verifier.  The
failure union has exactly five classes: zero NPR seed, one fixed combined NPR census, the
verifier-generated topology `gamma` event, the checker-guarded template-axis `alphaM` event, and
the counted low-order size-window seed event.  The regenerated compute and memory walks contribute
no event.
-/

namespace Nock.NockVMROM.Thm54.ProductionP8Containment

open scoped Classical BigOperators
open Nock Nock.Walk
open Nock.AxisBridge AxisBatching.MTree
open SemanticTimestampStrategy
open TemplateRawJointSoundness
open TemplateAxisCounting
open ProductionAxisStructureVerifier
open SizeWindowCounting

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable [charRing : CharP K (ringChar K)]

/-! ## Bare semantic support fixed independently of verifier messages -/

/-- The complete semantic support admitted by the production theorem.

There is one pre-`z` skeleton and, for each raw specialization, only the proposition that this
skeleton binds to the specialization's explicit configuration and execution.  In particular this
structure cannot carry a segmented family, exact-problem WF proof, exact IO assignment, table
auxiliary witness, walk response, acceptance proof, topology proof, evaluator, or target. -/
structure BareSemanticSupport
    (F K : Type) [Field F] [Field K] [Algebra F K]
    [charRing : CharP K (ringChar K)]
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K)) where
  skeleton : SemanticStrategy.SemanticSkeleton
  publicClaim_eq : skeleton.publicClaim = V.raw.claim
  binds :
    ∀ z (hz : z ≠ 0) α lmb,
      SemanticStrategy.BindsAt z skeleton
        (specializedProblem V.raw.timestamp z hz α lmb).cfg
        (specializedProblem V.raw.timestamp z hz α lmb).exec

/-- Type-level discrimination: after fixing the one skeleton, bare support has no further data
that can distinguish an IO assignment, table-WF witness, or `afterWalk` response.  The remaining
field is proposition-valued and hence proof-irrelevant. -/
theorem bareSemanticSupport_no_proof_carrying_fields
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (A B : BareSemanticSupport F K V)
    (h : A.skeleton = B.skeleton) :
    A = B := by
  cases A
  cases B
  cases h
  rfl

/-- Compiled raw-type regression: the complete transitive timestamp object under a production
verifier has exactly a public claim and data-only seed commitments.  In particular no semantic
skeleton or consistency certificate can be projected from this path. -/
theorem productionRawTimestamp_exact_shape
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K)) :
    V.raw.timestamp =
      { claim := V.raw.timestamp.claim
        afterSeed := V.raw.timestamp.afterSeed } :=
  SemanticTimestampStrategy.DataOnlyTemplateFixedStagedTimestampStrategy.eta _

/-- The seed-level transitive projection likewise exposes only raw config/execution templates and
the phase equation fixing `z`. -/
theorem productionRawSeedCarrier_exact_shape
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (z : K) (hz : z ≠ 0) :
    V.raw.timestamp.afterSeed ⟨z, hz⟩ =
      { configTemplate := (V.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate
        executionTemplate := (V.raw.timestamp.afterSeed ⟨z, hz⟩).executionTemplate
        sampledSeed := (V.raw.timestamp.afterSeed ⟨z, hz⟩).sampledSeed } :=
  rfl

/-- Final production strategy: verifier data plus the one committed skeleton and its public claim.

**H1.5b Part 1.**  There is no binding field.  Binding is a property
of a strategy *at a coin* (`BindsAtCoin`), supplied by the caller: on the honest side from
`BareSemanticSupport.binds` (`honestBinds`), on the hostile side as a theorem of the traces given
the tree bindings (`StrategyOfTraces.strategyOfTraces_bindsAtCoin`).  The old field
`semantics : BareSemanticSupport F K verifier` demanded `BindsAt` at EVERY `(z, α, λ)`, which is
refuted for the hostile traces (`Batch573.bindsAt_traces_forces_seed`: the decoded execution writes
the sampled seed into every memory row), so a strategy of the traces could never be formed. -/
structure ProductionStrategy
    (F K : Type) [Field F] [Field K] [Algebra F K]
    [charRing : CharP K (ringChar K)] where
  verifier : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K)
  skeleton : SemanticStrategy.SemanticSkeleton
  publicClaim_eq : skeleton.publicClaim = verifier.raw.claim

namespace ProductionStrategy

abbrev specializedCfg (T : ProductionStrategy F K)
    (z : K) (hz : z ≠ 0) (α lmb : K) : ExactConfig F K :=
  (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg

abbrev specializedExec (T : ProductionStrategy F K)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    ExactExecution (T.specializedCfg z hz α lmb) :=
  (specializedProblem T.verifier.raw.timestamp z hz α lmb).exec

/-- The a-bearing view of the specialized execution (`specializeA`): the object the axis
accounting is stated on; executed memory rows carry `(T, C')`. -/
abbrev specializedExecA (T : ProductionStrategy F K)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    ExactExecution (T.specializedCfg z hz α lmb) :=
  TemplateRawJointSoundness.specializedExecA T.verifier.raw.timestamp z hz α lmb

/-- **Seed-local binding** (H1.5b Part 1): the skeleton binds the specialization at the sampled
seed `nprSeed ω`, `alphaM ω` and the Form R coin `λ` — the one place the containment spine reads a
binding (`accepted_outside_failureUnion_at`). -/
def BindsAtCoin (T : ProductionStrategy F K) (ω : JointCoins K) (lmb : K) : Prop :=
  ∀ hz : nprSeed ω ≠ 0,
    SemanticStrategy.BindsAt (nprSeed ω) T.skeleton
      (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb)
      (T.specializedExec (nprSeed ω) hz (alphaM ω) lmb)

/-- Binding at every specialization — what the old field `semantics.binds` carried.  True of the
honest strategies (`ofBare_bindsAll`); refuted for the hostile traces at `3 ≤ |K|`
(`Batch573.tracesBindsAll_unsat`). -/
def BindsAll (T : ProductionStrategy F K) : Prop :=
  ∀ z (hz : z ≠ 0) α lmb,
    SemanticStrategy.BindsAt z T.skeleton (T.specializedCfg z hz α lmb)
      (T.specializedExec z hz α lmb)

omit [Fintype K] [DecidableEq K] in
theorem BindsAll.atCoin {T : ProductionStrategy F K} (h : T.BindsAll)
    (ω : JointCoins K) (lmb : K) : T.BindsAtCoin ω lmb :=
  fun hz => h (nprSeed ω) hz (alphaM ω) lmb

/-- The honest strategy of a bare semantic support (the forgetful split map). -/
def ofBare {V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K)}
    (S : BareSemanticSupport F K V) : ProductionStrategy F K where
  verifier := V
  skeleton := S.skeleton
  publicClaim_eq := S.publicClaim_eq

omit [Fintype K] [DecidableEq K] in
@[simp] theorem ofBare_verifier
    {V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K)}
    (S : BareSemanticSupport F K V) : (ofBare S).verifier = V := rfl

omit [Fintype K] [DecidableEq K] in
@[simp] theorem ofBare_skeleton
    {V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K)}
    (S : BareSemanticSupport F K V) : (ofBare S).skeleton = S.skeleton := rfl

omit [Fintype K] [DecidableEq K] in
/-- The honest strategy binds at every specialization: `BareSemanticSupport.binds`. -/
theorem ofBare_bindsAll
    {V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K)}
    (S : BareSemanticSupport F K V) : (ofBare S).BindsAll :=
  S.binds

omit [Fintype K] [DecidableEq K] in
/-- **Honest `BindsAtCoin` at every coin**, projected from
`BareSemanticSupport.binds`, which survives as the honest object. -/
theorem honestBinds
    {V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K)}
    (S : BareSemanticSupport F K V) (ω : JointCoins K) (lmb : K) :
    (ofBare S).BindsAtCoin ω lmb :=
  (ofBare_bindsAll S).atCoin ω lmb

omit [Fintype K] [DecidableEq K] in
/-- Two strategies with the same verifier and skeleton are equal (`publicClaim_eq` is a proof). -/
theorem ext_of_verifier_skeleton {T U : ProductionStrategy F K}
    (hv : T.verifier = U.verifier) (hs : T.skeleton = U.skeleton) : T = U := by
  cases T
  cases U
  cases hv
  cases hs
  rfl

/-- The deterministic per-root boundary checked at the sampled `alphaM`.
    Form R `eqBlk` does not force Relaxis (`Batch558.cancellingTree_is_remaining_join`);
    completeness is the 2-adic substrate `countsP_bin`, which honest reconstruction
    vanishes on. -/
def RootAxisBoundaryAt
    (T : ProductionStrategy F K) (z : K) (hz : z ≠ 0) (α : K) : Prop :=
  ∀ i,
    (countsP_bin
      (templateAxisTree
        (templateMemoryTreeAt (committedTemplate T.verifier z hz) i))).eval α = 0

/-- Final production acceptance.  It consists of the phase-authenticated eight-family verifier,
the alpha-free/no-wrap structural checks, and the deterministic per-root axis boundary. -/
def Accepts (T : ProductionStrategy F K) (ω : JointCoins K) (lmb : K) : Prop :=
  if hz : nprSeed ω ≠ 0 then
    ProductionAxisStructureAccepts T.verifier ω lmb ∧
      T.RootAxisBoundaryAt (nprSeed ω) hz (alphaM ω)
  else False

omit [Fintype K] in
theorem accepts_iff
    (T : ProductionStrategy F K) (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    T.Accepts ω lmb ↔
      ProductionAxisStructureAccepts T.verifier ω lmb ∧
        T.RootAxisBoundaryAt (nprSeed ω) hz (alphaM ω) := by
  simp [Accepts, hz]

omit [Fintype K] in
theorem productionAxisAccepts_of_accepts
    (T : ProductionStrategy F K) (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (h : T.Accepts ω lmb) :
    ProductionAxisStructureAccepts T.verifier ω lmb :=
  ((T.accepts_iff ω lmb hz).1 h).1

theorem productionRawAccepts_of_accepts
    (T : ProductionStrategy F K) (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (h : T.Accepts ω lmb) :
    T.verifier.Accepts ω lmb :=
  ProductionAxisStructureVerifier.productionRawAccepts_of_accepts
    T.verifier ω lmb hz (T.productionAxisAccepts_of_accepts ω lmb hz h)

end ProductionStrategy

/-! ## Fixed semantic support and the genuine target -/

/-- Numeric bounds for every local and parent/child occurrence in the one combined census. -/
def FixedCombinedBoundedBy
    (q : ℕ) (T : ProductionStrategy F K) : Prop :=
  ∀ pair ∈ EdgeComparisonCensus.combinedSkeletonPairs K T.skeleton,
    FieldEmbedding.BoundedBy q pair.1 ∧
      FieldEmbedding.BoundedBy q pair.2

def CombinedBoundedBy
    (K : Type) [Field K] (q : ℕ) (S : SemanticStrategy.SemanticSkeleton) : Prop :=
  ∀ pair ∈ EdgeComparisonCensus.combinedSkeletonPairs K S,
    FieldEmbedding.BoundedBy q pair.1 ∧
      FieldEmbedding.BoundedBy q pair.2

theorem combined_pairFaithful
    (S : SemanticStrategy.SemanticSkeleton)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K S Λ)
    (q : ℕ) (hb : CombinedBoundedBy K q S)
    (z : K) (hgood : z ∉ C.census.badSeeds (K := K))
    (pair : Noun × Noun)
    (hpair : pair ∈ EdgeComparisonCensus.combinedSkeletonPairs K S) :
    OpcodeSemantics.PairFaithful z q pair.1 pair.2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hpair
  let i : Fin C.census.count := ⟨j, by
    simpa only [EdgeComparisonCensus.CombinedSkeletonCensus.census,
      ComparisonCensus.ofPairList_count] using j.isLt⟩
  have hi : C.census.pair i = pair := by
    simpa [EdgeComparisonCensus.CombinedSkeletonCensus.census, i] using hj
  have hsep := P8Census.sepSeed_of_not_mem_badSeeds C.census z hgood i
  have hbounded := hb pair hpair
  exact
    { separates := by
        rw [hi] at hsep
        exact hsep
      left_bounded := hbounded.1
      right_bounded := hbounded.2 }

theorem p8_good_of_combined_good
    (S : SemanticStrategy.SemanticSkeleton)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K S Λ)
    (z : K) (hgood : z ∉ C.census.badSeeds (K := K)) :
    z ∉ C.p8.census.badSeeds (K := K) := by
  intro hbad
  obtain ⟨i, hi⟩ :=
    (ComparisonCensus.mem_badSeeds_iff C.p8.census z).1 hbad
  let pair := C.p8.census.pair i
  have hp : pair ∈ BoundSemanticTrace.skeletonPairs K S := by
    exact List.get_mem _ i
  obtain ⟨j, hj⟩ := C.p8_pair_lookup hp
  apply hgood
  rw [ComparisonCensus.mem_badSeeds_iff]
  refine ⟨j, ?_⟩
  simpa [pair, hj] using hi

theorem canonicalTreePremises_of_bare
    (S : SemanticStrategy.SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (z : K) (binds : SemanticStrategy.BindsAt z S cfg exec)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K S Λ)
    (q : ℕ) (hb : S.BoundedBy q)
    (hcombined : CombinedBoundedBy K q S)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hop :
      ∀ s ∈ SemanticStrategy.computeSkeletonRows S,
        BoundSemanticTrace.SkeletonOperationalPremises q z s)
    (hrows : exec.ComputeRowsAccepted) :
    GlobalOpcodeScheduling.CanonicalTreePremises q Λ z
      S.computeTree exec.computeTree := by
  let sourceWhole := S.computeTree
  let targetWhole := exec.computeTree
  have sourceMem {t : NTree SemanticStrategy.ComputeRowSkeleton}
      (ht : InTree sourceWhole t) :
      t.label ∈ SemanticStrategy.computeSkeletonRows S := by
    unfold SemanticStrategy.computeSkeletonRows
    apply List.mem_map.mpr
    refine ⟨t, ?_, rfl⟩
    rw [mem_bfsForest]
    exact ⟨S.computeTree, by simp, ht⟩
  have targetMem {t : NTree (ComputeTable.State × ComputeTable.DTcomp K)}
      (ht : InTree targetWhole t) :
      t.label ∈ exec.computeRows := by
    rw [ExactExecution.computeRows]
    apply List.mem_map.mpr
    refine ⟨t, ?_, rfl⟩
    rw [mem_bfsForest]
    exact ⟨targetWhole, by simp [targetWhole], ht⟩
  let motiveTree := fun
      (st : NTree SemanticStrategy.ComputeRowSkeleton)
      (et : NTree (ComputeTable.State × ComputeTable.DTcomp K))
      (_ : SemanticStrategy.ComputeTreeBinds z st et) =>
        InTree sourceWhole st → InTree targetWhole et →
          GlobalOpcodeScheduling.CanonicalTreePremises q Λ z st et
  let motiveList := fun
      (sts : List (NTree SemanticStrategy.ComputeRowSkeleton))
      (ets : List (NTree (ComputeTable.State × ComputeTable.DTcomp K)))
      (_ : List.Forall₂ (SemanticStrategy.ComputeTreeBinds z) sts ets) =>
        (∀ st ∈ sts, InTree sourceWhole st) →
        (∀ et ∈ ets, InTree targetWhole et) →
          List.Forall₂
            (GlobalOpcodeScheduling.CanonicalTreePremises q Λ z) sts ets
  apply SemanticStrategy.ComputeTreeBinds.rec
    (motive_1 := motiveTree) (motive_2 := motiveList)
    (t := binds.computeTree)
  · intro s sc row rc shape hbind children ih hinS hinE
    apply GlobalOpcodeScheduling.CanonicalTreePremises.node shape
    · exact (List.forall_iff_forall_mem.mp hb.computeRows) s (sourceMem hinS)
    · exact hop s (sourceMem hinS)
    · exact hbind
    · intro c hc
      apply combined_pairFaithful S C q hcombined z hgood c.pair
      rw [EdgeComparisonCensus.combinedSkeletonPairs, List.mem_append]
      apply Or.inl
      rw [BoundSemanticTrace.skeletonPairs, List.mem_append]
      apply Or.inr
      apply List.mem_map.mpr
      refine ⟨c, ?_, rfl⟩
      rw [P8Census.skeletonComparisonCensus, List.mem_flatMap]
      exact ⟨s, sourceMem hinS, hc⟩
    · intro c hc
      apply C.p8.leaves_bounded c.pair
      rw [BoundSemanticTrace.skeletonPairs, List.mem_append]
      apply Or.inr
      apply List.mem_map.mpr
      refine ⟨c, ?_, rfl⟩
      rw [P8Census.skeletonComparisonCensus, List.mem_flatMap]
      exact ⟨s, sourceMem hinS, hc⟩
    · exact ((ExactExecution.computeRowsAccepted_iff _).1 hrows row
        (targetMem hinE)).2.2
    · apply ih
      · intro st hst
        exact InTree_trans hinS (InTree.sub hst (InTree.here st))
      · intro et het
        exact InTree_trans hinE (InTree.sub het (InTree.here et))
  · intro _ _
    exact .nil
  · intro st et sts ets htree htrees ihTree ihTrees hsource htarget
    apply List.Forall₂.cons
    · exact ihTree (hsource st (by simp)) (htarget et (by simp))
    · apply ihTrees
      · intro st' hst'
        exact hsource st' (by simp [hst'])
      · intro et' het'
        exact htarget et' (by simp [het'])
  · exact InTree.here sourceWhole
  · exact InTree.here targetWhole

set_option maxHeartbeats 800000 in
noncomputable def canonicalRowsOfBare
    (S : SemanticStrategy.SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (z : K) (binds : SemanticStrategy.BindsAt z S cfg exec)
    (P : BoundSemanticTrace.SkeletonP8Census K S Λ)
    (q : ℕ) (hb : S.BoundedBy q)
    (hcmp : BoundSemanticTrace.SkeletonComparisonBoundedBy K q S)
    (hgood : z ∉ P.census.badSeeds (K := K))
    (hop : ∀ s ∈ SemanticStrategy.computeSkeletonRows S,
      BoundSemanticTrace.SkeletonOperationalPremises q z s) :
    ∀ i : Fin cfg.compRows,
      SemanticTrace.ComputeRowSemanticData q Λ
        (exec.computeRowAt i) :=
  fun i =>
    SemanticTrace.ComputeRowSemanticData.ofSkeleton
      S exec binds P hb hcmp hgood hop i

structure GenuineWitness
    (T : ProductionStrategy F K)
    (q Λ : ℕ) (z : K) (hz : z ≠ 0) (α lmb : K) where
  computeRowsAccepted :
    (T.specializedExec z hz α lmb).ComputeRowsAccepted
  memoryRowsAccepted :
    (T.specializedExec z hz α lmb).MemoryRowsAccepted
  vcomp :
    ∀ i, ComputeTable.Vcomp
      (T.specializedCfg z hz α lmb).challenges.computeInputs
      ((T.specializedExec z hz α lmb).computePubAt i)
      ((T.specializedExec z hz α lmb).computeDecAt i)
  vmem :
    ∀ i, MemoryTable.Vmem
      (T.specializedCfg z hz α lmb).challenges.memoryInputs
      ((T.specializedExec z hz α lmb).memoryPubAt i)
  exactLIO :
    IO.LIO (T.specializedCfg z hz α lmb).Ksz
      (T.specializedExec z hz α lmb).derivedRequestIO
      (T.specializedExec z hz α lmb).derivedResponseIO
  computeTopology :
    ComputeExactTopology (T.specializedExec z hz α lmb)
  memoryTopology :
    MemoryExactTopology (T.specializedExec z hz α lmb)
  localPairFaithful :
    ∀ s ∈ SemanticStrategy.computeSkeletonRows T.skeleton,
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right
  edgePairFaithful :
    ∀ pair ∈ EdgeComparisonCensus.edgePairs T.skeleton.computeTree,
      OpcodeSemantics.PairFaithful z q pair.1 pair.2
  canonicalRows :
    ∀ i : Fin (T.specializedCfg z hz α lmb).compRows,
      SemanticTrace.ComputeRowSemanticData q Λ
        ((T.specializedExec z hz α lmb).computeRowAt i)
  rootPublicNouns :
    T.skeleton.computeTree.label.subject = T.verifier.raw.claim.subject ∧
      T.skeleton.computeTree.label.formula = T.verifier.raw.claim.formula ∧
      T.skeleton.computeTree.label.evaluation = T.verifier.raw.claim.result
  bottomUp :
    GlobalOpcodeScheduling.NodeSchedulingConclusion q T.skeleton.computeTree.label
  evalFByPublic :
    ∃ fuel, FieldEmbedding.evalFBy q fuel T.verifier.raw.claim.subject
      T.verifier.raw.claim.formula = some T.verifier.raw.claim.result
  publicClaimHoldsMod : T.verifier.raw.claim.HoldsMod q
  axisStructural :
    ExactAxisStructuralRefinement
      (T.specializedCfg z hz α lmb)
      (T.specializedExecA z hz α lmb)
  /-- Ancestry and axis validity on the a-bearing view.  Validity is
      restored from acceptance: the guarded event prices the same
      2-adic `countsP_bin` polynomial `RootAxisBoundaryAt` checks
      (`specializedAxisValidity_of_accepts`).  The executed row-level rows carry `(T, C')`, so
      validity is stated on `specializedExecA`, not on `specializedExec`. -/
  axisSemantics :
    ExactMemoryAxisSemantics
      (T.specializedCfg z hz α lmb)
      (T.specializedExecA z hz α lmb)

def GenuineTargetAt
    (T : ProductionStrategy F K) (q Λ : ℕ) (ω : JointCoins K) (lmb : K) : Prop :=
  if hz : nprSeed ω ≠ 0 then
    Nonempty (GenuineWitness T q Λ (nprSeed ω) hz (alphaM ω) lmb)
  else False

def FalseAcceptanceSet
    (T : ProductionStrategy F K) (q Λ : ℕ) (lmb : K) : Finset (JointCoins K) :=
  Finset.univ.filter fun ω => T.Accepts ω lmb ∧ ¬ GenuineTargetAt T q Λ ω lmb

@[simp] theorem mem_falseAcceptanceSet_iff
    (T : ProductionStrategy F K) (q Λ : ℕ) (lmb : K) (ω : JointCoins K) :
    ω ∈ FalseAcceptanceSet T q Λ lmb ↔
      T.Accepts ω lmb ∧ ¬ GenuineTargetAt T q Λ ω lmb := by
  simp [FalseAcceptanceSet]

/-! ## The checker-guarded specialized axis event -/

def guardedSeedAxisPairs (T : ProductionStrategy F K) (lmb : K) : Finset (K × K) :=
  (Finset.univ : Finset K).biUnion fun z =>
    if hz : z ≠ 0 then
      (verifierGuardedRootUnion (committedTemplate T.verifier z hz) lmb).map
        (seedAlphaEmbedding z)
    else ∅

@[simp] theorem mem_guardedSeedAxisPairs_iff
    (T : ProductionStrategy F K) (lmb α z : K) :
    (α, z) ∈ guardedSeedAxisPairs T lmb ↔
      ∃ hz : z ≠ 0,
        α ∈ verifierGuardedRootUnion (committedTemplate T.verifier z hz) lmb := by
  simp only [guardedSeedAxisPairs, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨z', h⟩
    split at h
    · rename_i hz'
      simp only [Finset.mem_map] at h
      obtain ⟨α', hα', hp⟩ := h
      have hzEq : z' = z := congrArg Prod.snd hp
      subst z'
      have hαEq : α' = α := congrArg Prod.fst hp
      subst α'
      exact ⟨hz', hα'⟩
    · simp at h
  · rintro ⟨hz, hα⟩
    refine ⟨z, ?_⟩
    simp [hz, seedAlphaEmbedding]
    exact ⟨α, hα, rfl⟩

/-- The exact joint event: the first two coordinates are unrestricted, while `(alphaM,z)` belongs
to the checker-guarded seed fibers. -/
def guardedAxisFailureEvent (T : ProductionStrategy F K) (lmb : K) :
    Finset (JointCoins K) :=
  (Finset.univ : Finset (K × K)) ×ˢ guardedSeedAxisPairs T lmb

@[simp] theorem mem_guardedAxisFailureEvent_iff
    (T : ProductionStrategy F K) (lmb : K) (ω : JointCoins K) :
    ω ∈ guardedAxisFailureEvent T lmb ↔
      ∃ hz : nprSeed ω ≠ 0,
        alphaM ω ∈
          verifierGuardedRootUnion
            (committedTemplate T.verifier (nprSeed ω) hz) lmb := by
  rcases ω with ⟨cg, ⟨α, z⟩⟩
  simp [guardedAxisFailureEvent, mem_guardedSeedAxisPairs_iff,
    nprSeed, Thm54.alphaM]

theorem guardedSeedAxisPairs_card_le
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K) (lmb : K) (axisWorkload : ℕ)
    (hwork :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload) :
    (guardedSeedAxisPairs T lmb).card ≤ axisWorkload * Fintype.card K := by
  calc
    (guardedSeedAxisPairs T lmb).card
        ≤ ∑ z : K,
            (if hz : z ≠ 0 then
              (verifierGuardedRootUnion
                (committedTemplate T.verifier z hz) lmb).map (seedAlphaEmbedding z)
            else ∅).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _z : K, axisWorkload := by
      apply Finset.sum_le_sum
      intro z _
      split
      · rename_i hz
        simpa using
          (production_guarded_axis_cardinal h2 T.verifier z hz lmb).trans
            (hwork z hz)
      · simp
    _ = axisWorkload * Fintype.card K := by
      simp [Nat.mul_comm]

theorem guardedAxisFailureEvent_card_le
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K) (lmb : K) (axisWorkload : ℕ)
    (hwork :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload) :
    (guardedAxisFailureEvent T lmb).card ≤
      axisWorkload * Fintype.card K ^ 3 := by
  simp only [guardedAxisFailureEvent, Finset.card_product, Finset.card_univ,
    Fintype.card_prod]
  have hpairs := guardedSeedAxisPairs_card_le h2 T lmb axisWorkload hwork
  calc
    Fintype.card K * Fintype.card K * (guardedSeedAxisPairs T lmb).card
        ≤ Fintype.card K * Fintype.card K *
            (axisWorkload * Fintype.card K) :=
      Nat.mul_le_mul_left _ hpairs
    _ = axisWorkload * Fintype.card K ^ 3 := by ring

/-- `char K ∉ {2}` from the state-tag characteristic premise. -/
theorem two_ne_zero_of_stateTagChar
    (hchar : NodeEncoding.StateTagChar K) : (2 : K) ≠ 0 := by
  intro h2
  have h := hchar (show (2 : ℕ) ∈ Set.Iic 11 by simp) (show (0 : ℕ) ∈ Set.Iic 11 by simp)
    (by simpa using h2)
  omega

/-- **Axis validity from acceptance, on the a-bearing view.**  The guarded event and the
acceptance boundary `RootAxisBoundaryAt` are the same 2-adic polynomial
(`templateAxisPolynomial = countsP_bin ∘ templateAxisTree`).  A wrong committed axis on the
a-bearing specialized tree, with structural refinement from the accepted checks, makes that
polynomial nonzero (`templateAxisPolynomial_ne_zero_of_specialized_bad`, through
`axis_batching_sound` and the 2-adic reindex), so an accepted `alphaM` with a wrong axis lies in
`guardedAxisFailureEvent`.  Executed (row-level) rows carry `(T, C')`; this is stated on
`specializedExecA`. -/
theorem specializedAxisValidity_of_accepts
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K) (lmb : K) (ω : JointCoins K)
    (hz : nprSeed ω ≠ 0)
    (hacc : T.Accepts ω lmb)
    (hout : ω ∉ guardedAxisFailureEvent T lmb) :
    ExactMemoryAxisValidity
      (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb)
      (T.specializedExecA (nprSeed ω) hz (alphaM ω) lmb) := by
  have haxis := T.productionAxisAccepts_of_accepts ω lmb hz hacc
  have hchecks :=
    ((ProductionAxisStructureVerifier.accepts_iff
      T.verifier ω lmb hz).1 haxis).2
  have hparts :
      alphaFreeAxisStructureCheck
          (committedTemplate T.verifier (nprSeed ω) hz) = true ∧
        noWrapCheck
          (committedTemplate T.verifier (nprSeed ω) hz) (alphaM ω) = true := by
    simpa [structuralChecksAt] using hchecks
  have hroot := ((T.accepts_iff ω lmb hz).1 hacc).2
  have R := ProductionAxisStructureVerifier.exactAxisStructuralRefinement_of_checks
    (committedTemplate T.verifier (nprSeed ω) hz) (alphaM ω) (lmb := lmb) hparts.1 hparts.2
  intro i e hre hve
  by_contra hwrong
  apply hout
  rw [mem_guardedAxisFailureEvent_iff]
  refine ⟨hz, ?_⟩
  simp only [verifierGuardedRootUnion, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  refine ⟨i, ?_⟩
  simp only [verifierGuardedRootAlphas, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨hparts.1, hparts.2, ⟨e, hre, hve, hwrong⟩,
    templateAxisPolynomial_ne_zero_of_specialized_bad h2 _ (alphaM ω) R i
      ⟨e, hre, hve, hwrong⟩,
    hroot i⟩

/-! ## Pointwise production containment

The guarded axis event prices `countsP_bin` of the template axis tree, the polynomial
`RootAxisBoundaryAt` checks; validity follows (`specializedAxisValidity_of_accepts`). -/

def FailureUnion
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K) :
    Finset (JointCoins K) :=
  (((zeroSeedFailureEvent ∪ collisionFailureEvent C.census) ∪
      specializedTopologyFailureEvent T.verifier.raw lmb) ∪
    guardedAxisFailureEvent T lmb) ∪
      SizeWindowFailure T.skeleton

/-- **The Form R λ-event summand**:
`sup_z Σ_{i < kMem} (sup_{k ≤ E'} deg_Y B^{(i)}_k + E')` over the committed post-seed template
`committedTemplate T.verifier z hz = (T.verifier.raw.timestamp.afterSeed z).executionTemplate`,
with `B^{(i)}_k` the `α^k`-coefficient of the template's Form R polynomial
`FormRAxisEvent.formRTemplatePolynomial` and the envelope degree `E' = 3N + 3`
(`N = |computeSkeletonRows T.skeleton|`, the compute-row count `workload`'s census summand
already reads).  By `natDegree`, with no premise, as `fixedAxisWorkload` is by `templateAxisWorkload`.

`sup_{k ≤ E'}` majorises `deg_Y B_{e₀}` at every guard witness `e₀ ≤ E'`
(`FormRAxisEvent.formRRootBad_card_le`), so the guarded union's card is
`≤ |𝕂|⁹ · Σ_i |𝕂|·(deg_i + E')` with no choice of `e₀` in the definition.  The body is written
out (no helper names) so that the closure watchlist's fingerprint of this one name covers it.
The supremum over seeds is `⨆` (on `ℕ`, bounded because `K` is finite), not `Finset.univ.sup`, so
the definition — and hence `workload`'s signature — needs no `Fintype K` / `DecidableEq K`
instance: `workload`'s users (`FixedFieldSoundnessClaim`, …) keep their terms. -/
noncomputable def fixedFormRWorkload {F K : Type} [Field F] [Field K] [Algebra F K]
    [CharP K (ringChar K)] (T : ProductionStrategy F K) : ℕ :=
  ⨆ z : K,
    if hz : z ≠ 0 then
      ∑ i : Fin (T.verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate.kMem,
        (((Finset.range (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 3 + 1)).sup
            fun k => ((FormRAxisEvent.formRTemplatePolynomial
              (committedTemplate T.verifier z hz) i).coeff k).natDegree) +
          (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 3))
    else 0

/-- The per-seed Form R summand is below the canonical fixed-field maximum. -/
theorem formRSeedWorkload_le_fixedFormRWorkload
    (T : ProductionStrategy F K) (z : K) (hz : z ≠ 0) :
    (∑ i : Fin (T.verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate.kMem,
        (((Finset.range (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 3 + 1)).sup
            fun k => ((FormRAxisEvent.formRTemplatePolynomial
              (committedTemplate T.verifier z hz) i).coeff k).natDegree) +
          (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 3))) ≤
      fixedFormRWorkload T := by
  have hle := le_ciSup (Set.finite_range (fun z' : K =>
      if hz' : z' ≠ 0 then
        ∑ i : Fin (T.verifier.raw.timestamp.afterSeed ⟨z', hz'⟩).configTemplate.kMem,
          (((Finset.range
              (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 3 + 1)).sup
              fun k => ((FormRAxisEvent.formRTemplatePolynomial
                (committedTemplate T.verifier z' hz') i).coeff k).natDegree) +
            (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 3))
      else 0)).bddAbove z
  simpa [fixedFormRWorkload, hz] using hle

/-- It prices the decoded λ-event
`DecodedLambdaEvent.decodedLambdaEventOfEnvs` at every committed env tuple
(`decodedLambdaEventOfEnvs_card_le`, no premise). The body is written out, with no helper names, so
that the closure watchlist's fingerprint of this one name covers it. It replaces
`fixedFormRWorkload` in `workload`; `fixedFormRWorkload` stays as a definition. -/
noncomputable def formRUniformWorkload {F K : Type} [Field F] [Field K] [Algebra F K]
    [CharP K (ringChar K)] (T : ProductionStrategy F K) : ℕ :=
  (SemanticStrategy.memorySkeletonRows T.skeleton).length *
    (3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length + 67 +
      (FormRAxisEvent.formRN K - 1))

/-- **The thirty-third move's request-indexed pre-`z` pair summand**: `M_T · (2·(M_T ⊔ Λ) − 1)`, one memory row
per pair and at most `2Λg − 1` bad seeds per pair at the window `Λg = M_T ⊔ Λ`
(`PreSeedCensus.reqPairEventOfEnvs_card_le`). It prices the pinned
`OptimizedStrictFullPackage.reqPairEventOf` at every committed env tuple, with no premise. -/
def reqPairWorkload {F K : Type} [Field F] [Field K] [Algebra F K]
    [CharP K (ringChar K)] (T : ProductionStrategy F K) (Λ : ℕ) : ℕ :=
  (SemanticStrategy.memorySkeletonRows T.skeleton).length *
    (2 * ((SemanticStrategy.memorySkeletonRows T.skeleton).length ⊔ Λ) - 1)

/-- The P8 numerator. Since the thirty-third it also carries the request-indexed pair summand
`reqPairWorkload T Λ`. Both events are priced in the consumed hostile bound through this slot
(`OptimizedStrictPackage.optimizedHostileProductionFailureEvent_card_le`); the `JointCoins` failure
union reads neither (`failureUnion_card_add_formR_le`). -/
def workload
    (T : ProductionStrategy F K) (Λ topologyWorkload axisWorkload : ℕ) : ℕ :=
  1 +
    (3 + 19 *
      (SemanticStrategy.computeSkeletonRows T.skeleton).length) *
        (2 * Λ - 1) +
    topologyWorkload + axisWorkload + formRUniformWorkload T + reqPairWorkload T Λ +
    sizeWindowRootBound Λ

/-! ### Canonical fixed-field majorants

The varying-family theorem takes topology and axis majorants as family data because it must also
prove that those majorants grow polynomially.  At one fixed finite field no external majorant is
needed: both challenge-indexed workloads have a canonical finite supremum.  These definitions are
the fixed-field form of the paper's pointwise soundness accounting; they carry no
response, witness, or acceptance proof. -/

/-- The maximum topology workload over every staged `(z, α)` specialization of one fixed strategy.
This is the existing `TemplateMemoryWalkCounting` maximum, named at the production-strategy layer. -/
def fixedTopologyWorkload (T : ProductionStrategy F K) : ℕ :=
  TemplateMemoryWalkCounting.memoryWalkTopologyWorkload T.verifier.raw

/-- Every specialized topology workload is bounded by the canonical fixed-field maximum. -/
theorem topologyWorkload_le_fixedTopologyWorkload
    (T : ProductionStrategy F K) (z : K) (hz : z ≠ 0) (α lmb : K) :
    topologyWorkload
        (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤
      fixedTopologyWorkload T :=
  TemplateMemoryWalkCounting.topologyWorkload_le_memoryWalkTopologyWorkload
    T.verifier.raw z hz α lmb

/-- The maximum checker-guarded axis workload over every nonzero seed of one fixed strategy. -/
def fixedAxisWorkload (T : ProductionStrategy F K) : ℕ :=
  (Finset.univ : Finset K).sup fun z =>
    if hz : z ≠ 0 then
      templateAxisWorkload (committedTemplate T.verifier z hz)
    else 0

/-- Every seed-specialized axis workload is bounded by the canonical fixed-field maximum. -/
theorem templateAxisWorkload_le_fixedAxisWorkload
    (T : ProductionStrategy F K) (z : K) (hz : z ≠ 0) :
    templateAxisWorkload (committedTemplate T.verifier z hz) ≤ fixedAxisWorkload T := by
  have hle := Finset.le_sup
    (f := fun z' : K =>
      if hz' : z' ≠ 0 then
        templateAxisWorkload (committedTemplate T.verifier z' hz')
      else 0)
    (Finset.mem_univ z)
  simpa [fixedAxisWorkload, hz, proof_irrel_heq] using hle

set_option maxHeartbeats 800000 in
theorem accepted_outside_failureUnion_at
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (q : ℕ)
    (hchar : NodeEncoding.StateTagChar K)
    (hq : 1 < q)
    (hqChar : q = ringChar K)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbound : T.skeleton.BoundedBy q)
    (hcombined : FixedCombinedBoundedBy q T)
    (hop : ∀ s ∈ SemanticStrategy.computeSkeletonRows T.skeleton,
      BoundSemanticTrace.SkeletonOperationalCore s)
    (hKp : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.Ksz <
        ringChar K)
    (hProgCap : ∀ z (hz : z ≠ 0) α lmb,
      ((specializedProblem T.verifier.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1) ≤
        2 ^ (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.orbit.h)
    (hMemCap : ∀ z (hz : z ≠ 0) α lmb,
      ((specializedProblem T.verifier.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1) ≤
        2 ^ (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.orbit.h)
    (ω : JointCoins K) (lmb : K)
    (hbinds : T.BindsAtCoin ω lmb)
    (hacc : T.Accepts ω lmb)
    (hout : ω ∉ FailureUnion T C lmb)
    (hlam : ∀ (hz : nprSeed ω ≠ 0) i,
      ((T.verifier.familyAt ω lmb hz).exec.memoryPubAt i).lambda = (T.verifier.familyAt ω lmb hz).cfg.challenges.lam) :
    GenuineTargetAt T q Λ ω lmb := by
  have hz : nprSeed ω ≠ 0 := by
    intro hz0
    simp [ProductionStrategy.Accepts, hz0] at hacc
  let exec := T.specializedExec (nprSeed ω) hz (alphaM ω) lmb
  have binds : SemanticStrategy.BindsAt (nprSeed ω) T.skeleton
      (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb) exec :=
    hbinds hz
  have houtC : ω ∉ collisionFailureEvent C.census := by
    intro h
    apply hout
    simp [FailureUnion, h]
  have houtG : ω ∉ specializedTopologyFailureEvent T.verifier.raw lmb := by
    intro h
    apply hout
    simp [FailureUnion, h]
  have houtA : ω ∉ guardedAxisFailureEvent T lmb := by
    intro h
    apply hout
    simp [FailureUnion, h]
  have houtW : ω ∉ SizeWindowFailure T.skeleton := by
    intro h
    apply hout
    simp [FailureUnion, h]
  have hgood : nprSeed ω ∉ C.census.badSeeds (K := K) := by
    intro hbad
    apply houtC
    rw [mem_collisionFailureEvent_iff]
    exact (ComparisonCensus.mem_badSeeds_iff C.census (nprSeed ω)).1 hbad
  have hgoodP8 : nprSeed ω ∉ C.p8.census.badSeeds (K := K) :=
    p8_good_of_combined_good T.skeleton C (nprSeed ω) hgood
  have hraw := T.productionRawAccepts_of_accepts ω lmb hz hacc
  have hmsg :=
    (T.verifier.accepts_iff_production ω lmb hz).1 hraw
  have hrawMsg :=
    ProductionRawVerifier.Message.rawAccepts_of_verifierChecks hmsg
  have hrowsProd :=
    (T.verifier.messageAt ω lmb hz).raw.computeRowsAccepted_of_accepts
      hchar hrawMsg
  have hmemRowsProd :=
    (T.verifier.messageAt ω lmb hz).raw.memoryRowsAccepted_of_accepts
      hchar (hlam hz) hrawMsg
  have htopProd :=
    T.verifier.exactTopology_of_accepts ω lmb hz hchar (hlam hz) hraw houtG
  have hrows : exec.ComputeRowsAccepted := by
    simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base, exec,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using hrowsProd
  have hmemRows : exec.MemoryRowsAccepted := by
    simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base, exec,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using hmemRowsProd
  have htop :
      ComputeExactTopology exec ∧ MemoryExactTopology exec := by
    simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base, exec,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using htopProd
  have hstructProd :=
    ProductionAxisStructureVerifier.exactAxisStructuralRefinement_of_accepts
      T.verifier ω lmb hz (T.productionAxisAccepts_of_accepts ω lmb hz hacc)
  have hstruct : ExactAxisStructuralRefinement
      (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb)
      (T.specializedExecA (nprSeed ω) hz (alphaM ω) lmb) := by
    exact hstructProd
  have hioProd :=
    ProductionRawVerifier.Message.io_sound
      (T.verifier.messageAt ω lmb hz) T.verifier.raw.claim ω
      (by simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
        TemplateRawJointSoundness.Strategy.familyAt,
        TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
        TemplateRawJointSoundness.AlphaMFamilyData.base] using
          hKp (nprSeed ω) hz (alphaM ω) lmb)
      (by simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
        TemplateRawJointSoundness.Strategy.familyAt,
        TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
        TemplateRawJointSoundness.AlphaMFamilyData.base] using
          hProgCap (nprSeed ω) hz (alphaM ω) lmb)
      (by simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
        TemplateRawJointSoundness.Strategy.familyAt,
        TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
        TemplateRawJointSoundness.AlphaMFamilyData.base] using
          hMemCap (nprSeed ω) hz (alphaM ω) lmb)
      hmsg
  have hio : IO.LIO
      (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb).Ksz
      exec.derivedRequestIO exec.derivedResponseIO := by
    simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base, exec,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using hioProd
  have hcombinedAt : CombinedBoundedBy K q T.skeleton := by
    exact hcombined
  have hlocal :
      ∀ s ∈ SemanticStrategy.computeSkeletonRows T.skeleton,
        ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
          OpcodeSemantics.PairFaithful (nprSeed ω) q c.left c.right := by
    intro s hs c hc
    apply combined_pairFaithful T.skeleton C q hcombinedAt
      (nprSeed ω) hgood c.pair
    rw [EdgeComparisonCensus.combinedSkeletonPairs, List.mem_append]
    apply Or.inl
    rw [BoundSemanticTrace.skeletonPairs, List.mem_append]
    apply Or.inr
    apply List.mem_map.mpr
    refine ⟨c, ?_, rfl⟩
    rw [P8Census.skeletonComparisonCensus, List.mem_flatMap]
    exact ⟨s, hs, hc⟩
  have hedge :
      ∀ pair ∈ EdgeComparisonCensus.edgePairs T.skeleton.computeTree,
        OpcodeSemantics.PairFaithful (nprSeed ω) q pair.1 pair.2 := by
    intro pair hp
    apply combined_pairFaithful T.skeleton C q hcombinedAt
      (nprSeed ω) hgood pair
    rw [EdgeComparisonCensus.combinedSkeletonPairs, List.mem_append]
    exact Or.inr hp
  have hcmp : BoundSemanticTrace.SkeletonComparisonBoundedBy K q T.skeleton := by
    intro s hs c hc
    exact hcombinedAt c.pair (by
      rw [EdgeComparisonCensus.combinedSkeletonPairs, List.mem_append]
      apply Or.inl
      rw [BoundSemanticTrace.skeletonPairs, List.mem_append]
      apply Or.inr
      apply List.mem_map.mpr
      refine ⟨c, ?_, rfl⟩
      rw [P8Census.skeletonComparisonCensus, List.mem_flatMap]
      exact ⟨s, hs, hc⟩)
  have hopAt :
      ∀ s ∈ SemanticStrategy.computeSkeletonRows T.skeleton,
        BoundSemanticTrace.SkeletonOperationalPremises q (nprSeed ω) s := by
    intro s hs
    exact BoundSemanticTrace.SkeletonOperationalPremises.ofCoreAndWindows
      hqChar
      (hop s hs)
      (windows_of_not_mem_SizeWindowFailure T.skeleton ω hz houtW s hs)
  have hcanonical :
      ∀ i : Fin (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb).compRows,
        SemanticTrace.ComputeRowSemanticData q Λ (exec.computeRowAt i) := by
    exact canonicalRowsOfBare T.skeleton exec (nprSeed ω) binds C.p8
      q hbound hcmp hgoodP8 hopAt
  have hprem :=
    canonicalTreePremises_of_bare T.skeleton exec (nprSeed ω) binds C
      q hbound hcombinedAt hgood hopAt hrows
  have hbottom :=
    GlobalOpcodeScheduling.bareCensus_bottomUp
      T.skeleton exec (nprSeed ω) binds C hz hq hbound hcast
      htop.1 hgood hprem
  have heval :=
    GlobalOpcodeScheduling.bareCensus_evalFBy
      T.skeleton exec (nprSeed ω) binds C hz hq hbound hcast
      htop.1 hgood hprem
  have hroot :
      T.skeleton.computeTree.label.subject = T.verifier.raw.claim.subject ∧
        T.skeleton.computeTree.label.formula = T.verifier.raw.claim.formula ∧
        T.skeleton.computeTree.label.evaluation = T.verifier.raw.claim.result := by
    have hs : T.skeleton.publicClaim = T.verifier.raw.claim := T.publicClaim_eq
    exact ⟨congrArg P8PublicClaim.subject hs,
      congrArg P8PublicClaim.formula hs,
      congrArg P8PublicClaim.result hs⟩
  have hevalPublic :
      ∃ fuel, FieldEmbedding.evalFBy q fuel T.verifier.raw.claim.subject
        T.verifier.raw.claim.formula = some T.verifier.raw.claim.result := by
    obtain ⟨fuel, heval⟩ := heval
    exact ⟨fuel, by simpa [hroot.1, hroot.2.1, hroot.2.2] using heval⟩
  rw [GenuineTargetAt, dif_pos hz]
  refine ⟨{
    computeRowsAccepted := hrows
    memoryRowsAccepted := hmemRows
    vcomp := ?_
    vmem := ?_
    exactLIO := hio
    computeTopology := htop.1
    memoryTopology := htop.2
    localPairFaithful := hlocal
    edgePairFaithful := hedge
    canonicalRows := hcanonical
    rootPublicNouns := hroot
    bottomUp := hbottom
    evalFByPublic := hevalPublic
    publicClaimHoldsMod := hevalPublic
    axisStructural := hstruct
    axisSemantics := ⟨hstruct.ancestry,
      specializedAxisValidity_of_accepts (two_ne_zero_of_stateTagChar hchar)
        T lmb ω hz hacc houtA⟩ }⟩
  · intro i
    have hr := ExactExecution.computeRowAt_accepted hrows i
    rw [← hr.2.1]
    exact hr.2.2
  · intro i
    have hr := ExactExecution.memoryRowAt_accepted hmemRows i
    rw [← hr.2.1]
    exact hr.2.2.1

/-- The spine for a strategy that binds at every specialization (`BindsAll`, which every honest
strategy `ProductionStrategy.ofBare S` satisfies, `ofBare_bindsAll`): the seed-local spine at
`hbinds.atCoin`.  Before H1.5b Part 1 this binding was the field `T.semantics.binds`.  Memory rows
carry the configuration's `λ` (`hlam`, 28th λ-fix); the RAP is checked at that value. -/
theorem accepted_outside_failureUnion
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (q : ℕ)
    (hchar : NodeEncoding.StateTagChar K)
    (hq : 1 < q)
    (hqChar : q = ringChar K)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbound : T.skeleton.BoundedBy q)
    (hcombined : FixedCombinedBoundedBy q T)
    (hop : ∀ s ∈ SemanticStrategy.computeSkeletonRows T.skeleton,
      BoundSemanticTrace.SkeletonOperationalCore s)
    (hKp : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.Ksz <
        ringChar K)
    (hProgCap : ∀ z (hz : z ≠ 0) α lmb,
      ((specializedProblem T.verifier.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1) ≤
        2 ^ (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.orbit.h)
    (hMemCap : ∀ z (hz : z ≠ 0) α lmb,
      ((specializedProblem T.verifier.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1) ≤
        2 ^ (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.orbit.h)
    (hbinds : T.BindsAll)
    (ω : JointCoins K) (lmb : K)
    (hacc : T.Accepts ω lmb)
    (hout : ω ∉ FailureUnion T C lmb)
    (hlam : ∀ (hz : nprSeed ω ≠ 0) i,
      ((T.verifier.familyAt ω lmb hz).exec.memoryPubAt i).lambda = (T.verifier.familyAt ω lmb hz).cfg.challenges.lam) :
    GenuineTargetAt T q Λ ω lmb :=
  accepted_outside_failureUnion_at T C q hchar hq hqChar hcast hbound hcombined
    hop hKp hProgCap hMemCap ω lmb (hbinds.atCoin ω lmb)
    hacc hout hlam

/-! ## Exact five-class failure union and workload -/

theorem failureUnion_card_add_formR_le
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K) (lmb : K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (topologyBound axisWorkload : ℕ)
    (hwindowBound : SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload
          (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload) :
    (FailureUnion T C lmb).card + formRUniformWorkload T * Fintype.card K ^ 3 +
        reqPairWorkload T Λ * Fintype.card K ^ 3 ≤
      workload T Λ topologyBound axisWorkload * Fintype.card K ^ 3 := by
  let k3 := Fintype.card K ^ 3
  have hZ : (zeroSeedFailureEvent (K := K)).card ≤ 1 * k3 := by
    simp [k3, zeroSeedFailureEvent_card]
  have hC :
      (collisionFailureEvent (K := K) C.census).card ≤
        ((3 + 19 *
          (SemanticStrategy.computeSkeletonRows T.skeleton).length) *
            (2 * Λ - 1)) * k3 := by
    exact collisionFailureEvent_card_le C.census |>.trans
      (Nat.mul_le_mul_right k3
        (Nat.mul_le_mul_right (2 * Λ - 1) C.count_le))
  have hG :
      (specializedTopologyFailureEvent T.verifier.raw lmb).card ≤
        topologyBound * k3 :=
    specializedTopologyFailureEvent_card_le T.verifier.raw lmb topologyBound
      (fun z hz α => htopology z hz α lmb)
  have hA :
      (guardedAxisFailureEvent T lmb).card ≤ axisWorkload * k3 :=
    guardedAxisFailureEvent_card_le h2 T lmb axisWorkload haxis
  have hW :
      (SizeWindowFailure (K := K) T.skeleton).card ≤
        sizeWindowRootBound Λ * k3 := by
    simpa [k3] using
      SizeWindowFailure_card_le (K := K) T.skeleton Λ hwindowBound
  have hcore :
      (FailureUnion T C lmb).card ≤
        1 * k3 +
          ((3 + 19 *
            (SemanticStrategy.computeSkeletonRows T.skeleton).length) *
              (2 * Λ - 1)) * k3 +
          topologyBound * k3 + axisWorkload * k3 +
          sizeWindowRootBound Λ * k3 := by
    calc
      (FailureUnion T C lmb).card
          ≤ zeroSeedFailureEvent.card +
              (collisionFailureEvent C.census).card +
              (specializedTopologyFailureEvent T.verifier.raw lmb).card +
              (guardedAxisFailureEvent T lmb).card +
              (SizeWindowFailure T.skeleton).card := by
        simpa [FailureUnion, add_assoc] using
          (calc
            ((((zeroSeedFailureEvent ∪ collisionFailureEvent C.census) ∪
                specializedTopologyFailureEvent T.verifier.raw lmb) ∪
                guardedAxisFailureEvent T lmb) ∪
                SizeWindowFailure T.skeleton).card
                ≤ (((zeroSeedFailureEvent ∪ collisionFailureEvent C.census) ∪
                    specializedTopologyFailureEvent T.verifier.raw lmb) ∪
                    guardedAxisFailureEvent T lmb).card +
                    (SizeWindowFailure T.skeleton).card :=
              Finset.card_union_le _ _
            _ ≤ ((zeroSeedFailureEvent ∪ collisionFailureEvent C.census) ∪
                    specializedTopologyFailureEvent T.verifier.raw lmb).card +
                    (guardedAxisFailureEvent T lmb).card +
                    (SizeWindowFailure T.skeleton).card := by
              exact Nat.add_le_add_right (Finset.card_union_le _ _) _
            _ ≤ (zeroSeedFailureEvent ∪ collisionFailureEvent C.census).card +
                  (specializedTopologyFailureEvent T.verifier.raw lmb).card +
                  (guardedAxisFailureEvent T lmb).card +
                  (SizeWindowFailure T.skeleton).card := by
              exact Nat.add_le_add_right
                (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
            _ ≤ zeroSeedFailureEvent.card + (collisionFailureEvent C.census).card +
                  (specializedTopologyFailureEvent T.verifier.raw lmb).card +
                  (guardedAxisFailureEvent T lmb).card +
                  (SizeWindowFailure T.skeleton).card := by
              exact Nat.add_le_add_right
                (Nat.add_le_add_right
                  (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _)
      _ ≤ 1 * k3 +
            ((3 + 19 *
              (SemanticStrategy.computeSkeletonRows T.skeleton).length) *
                (2 * Λ - 1)) * k3 +
            topologyBound * k3 + axisWorkload * k3 +
            sizeWindowRootBound Λ * k3 := by omega
  have hw : workload T Λ topologyBound axisWorkload * Fintype.card K ^ 3 =
      (1 * k3 +
          ((3 + 19 *
            (SemanticStrategy.computeSkeletonRows T.skeleton).length) *
              (2 * Λ - 1)) * k3 +
          topologyBound * k3 + axisWorkload * k3 +
          sizeWindowRootBound Λ * k3) + formRUniformWorkload T * Fintype.card K ^ 3 +
        reqPairWorkload T Λ * Fintype.card K ^ 3 := by
    simp only [workload, k3]
    ring
  rw [hw]
  omega

/-- The P8 failure union's card is below the P8 numerator (`failureUnion_card_add_formR_le`
without the Form R and pair summands it leaves free). -/
theorem failureUnion_card_le
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K) (lmb : K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (topologyBound axisWorkload : ℕ)
    (hwindowBound : SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload
          (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload) :
    (FailureUnion T C lmb).card ≤
      workload T Λ topologyBound axisWorkload * Fintype.card K ^ 3 :=
  le_trans (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
    (failureUnion_card_add_formR_le h2 T lmb C topologyBound axisWorkload hwindowBound
      htopology haxis)

theorem falseAcceptanceSet_subset_failureUnion
    (T : ProductionStrategy F K) (lmb : K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (q : ℕ)
    (hcontain : ∀ ω, T.Accepts ω lmb → ω ∉ FailureUnion T C lmb →
      GenuineTargetAt T q Λ ω lmb) :
    FalseAcceptanceSet T q Λ lmb ⊆ FailureUnion T C lmb := by
  intro ω hω
  rw [mem_falseAcceptanceSet_iff] at hω
  by_contra hout
  exact hω.2 (hcontain ω hω.1 hout)

theorem jointProbability_falseAcceptance_le
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K) (lmb : K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (q topologyBound axisWorkload : ℕ)
    (hwindowBound : SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology : ∀ z (hz : z ≠ 0) α lmb,
      topologyWorkload
        (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis : ∀ z (hz : z ≠ 0),
      templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (hcontain : ∀ ω, T.Accepts ω lmb → ω ∉ FailureUnion T C lmb →
      GenuineTargetAt T q Λ ω lmb) :
    |jointProbability (FalseAcceptanceSet T q Λ lmb)| ≤
      (workload T Λ topologyBound axisWorkload : ℝ) /
        (Fintype.card K : ℝ) := by
  apply jointProbability_le_workload_div_card
    (FalseAcceptanceSet T q Λ lmb) (workload T Λ topologyBound axisWorkload)
  exact (Finset.card_le_card
    (falseAcceptanceSet_subset_failureUnion T lmb C q hcontain)).trans
      (failureUnion_card_le h2 T lmb C topologyBound axisWorkload hwindowBound
        htopology haxis)

/-- The exact fixed-field S7 conclusion for one Nock production strategy, its false-acceptance
event, and the canonical five-class workload. -/
def FixedFieldSoundnessClaim
    (T : ProductionStrategy F K) (q Λ : ℕ) (lmb : K) : Prop :=
  |jointProbability (FalseAcceptanceSet T q Λ lmb)| ≤
    (workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) : ℝ) /
      (Fintype.card K : ℝ)

/-- Universal Nock-production fixed-field soundness.  Unlike the legacy
`ConcreteSoundnessModel`, this proposition names the Nock strategy, exact false-acceptance event,
failure union/census, noun-size premise, and canonical workload. -/
abbrev ExactProductionFixedFieldSoundness (F K : Type)
    [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] : Prop :=
  ∀ (Λ q : ℕ) (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ),
    (2 : K) ≠ 0 →
    SizeWindowNounsBoundedBy T.skeleton Λ →
    ∀ lmb : K,
    (∀ ω, T.Accepts ω lmb → ω ∉ FailureUnion T C lmb →
      GenuineTargetAt T q Λ ω lmb) →
    FixedFieldSoundnessClaim T q Λ lmb

/-- The production union bound proves the exact fixed-field S7 proposition for every strategy
satisfying the same-event containment and noun-size premises. -/
theorem exactProductionFixedFieldSoundness (F K : Type)
    [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] :
    ExactProductionFixedFieldSoundness F K := by
  intro Λ q T C h2 hwindow lmb hcontain
  exact jointProbability_falseAcceptance_le h2 T lmb C q
    (fixedTopologyWorkload T) (fixedAxisWorkload T) hwindow
    (topologyWorkload_le_fixedTopologyWorkload T)
    (templateAxisWorkload_le_fixedAxisWorkload T) hcontain

/-- **Fixed-field soundness error, `≤ workload / |K|`, with containment derived rather than
assumed.**

⚠️ **Carried restriction — read `hop` before quoting this theorem's scope.**  The type variables are
generic (`K` free, no `GaloisField` pin), so `#check` reports it as a statement about an *arbitrary*
`ProductionStrategy`.  It is not.  `hop : ∀ s ∈ computeSkeletonRows T.skeleton,
SkeletonOperationalCore s` is contentful — a legal skeleton can violate it — and is **not** a
consequence of acceptance, by design (`BoundSemanticTrace.lean:22-26`: "not consequences of
noun/fingerprint binding").  Worse, it is re-emitted *inside* the conclusion: `hop.s0_served` /
`hop.s9_served` are used verbatim as the `served` field of the `ServedNounLookup`s built by
`buildCoveredRow` (`BoundSemanticTrace.lean:437-438`), which become `GenuineWitness.canonicalRows`
via `canonicalRowsOfBare` (built at `:767`, consumed at `:807`).  So the OP0/OP9 served-lookup half
of the genuine target is assumed on the committed skeleton, not derived.

The theorem is sound as stated; its scope is strategies whose committed skeleton is already
operationally well-formed.  On the *generated* path that is fine and tight: `hop` reaches this
theorem through the carrier fields `Data.slotSemantics` / `Data.recordEquations`, which
`packageOf`'s `containment` consumes (`OptimizedStrictFullPackage.lean:157`) and which
`genData_slotSemantics` (`GenHonestData.lean:182`) and `genData_recordEquations` (`:194`) discharge
at the generated carrier.  (`TraceGen.genOperationalCore`, `GenSemanticDataParts.lean:85`, is a
second route to the same content from `genComputeSkeleton_bfsRows_census_air`; it is not the one
`packageOf` uses.)

* The **record** half (`s0_record`, `s9_record`) is now derived `∀ skeleton` by
  `GenOperationalCore.operationalCore_of_accepted_and_slots`, from `ComputeRowsAccepted` + `BindsAt`
  + a counted seed event over a new `SkeletonRecordCensus`.  The paper gates are the paper
  (`op_0 = 1`: `mem_root_2 = input_subject`, `mem_child_2 = evaluation`, `mem_axis_2 = f_t.leaf`)
  and the paper for the OP9 twin, both at the `𝕂^3` fingerprint level, so the fingerprint→noun
  step is a census bridge.  Note the four record pairs are **not** entries of
  `P8Census.skeletonComparisons` — only their *axis* halves are — hence the separate census.
What does stand: no compute constraint mentions `Noun.slot` (`ComputeTable.memBlk`/`evalV` relate
  record fingerprints only to other row fingerprints); `ServedLookupBridge.slotSemantics_of_served`
  is genuinely circular here, wanting an `ExactServedMemoryTrace` whose `rows` field
  (`SemanticTrace.lean:689-691`) is what `canonicalRowsOfBare` produces from `hop`; and — the real
  content — `MTree.verify` retains only `(ℕ, K)`, so recovering a `MemRec` from its exponent is
  *equivalent* to `TimestampClosedAt` (`timestampExp_recovers_ts_iff_closed`,
  `GenericHonestData.lean:4417`). The residual is therefore `timestampClosed` /
  `AddedRemovedAgain`, an already-tracked premise.

⚠️ **`hop`'s reach is wider than `canonicalRows`** (`ID`, F-RV2): it also feeds `bottomUp`,
`evalFByPublic` and `publicClaimHoldsMod`, and `.s0` rows are the compute tree's **leaves**, so the
induction's base case is assumed too. Do not read the restriction as confined to the canonical-row
field.

-/
theorem production_jointProbability_falseAcceptance_le
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K) (lmb : K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (q topologyBound axisWorkload : ℕ)
    (hchar : NodeEncoding.StateTagChar K)
    (hq : 1 < q)
    (hqChar : q = ringChar K)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbound : T.skeleton.BoundedBy q)
    (hcombined : FixedCombinedBoundedBy q T)
    (hop : ∀ s ∈ SemanticStrategy.computeSkeletonRows T.skeleton,
      BoundSemanticTrace.SkeletonOperationalCore s)
    (hwindowBound : SizeWindowNounsBoundedBy T.skeleton Λ)
    (hKp : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.Ksz <
        ringChar K)
    (hProgCap : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem T.verifier.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1 ≤
        2 ^ (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.orbit.h)
    (hMemCap : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem T.verifier.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1 ≤
        2 ^ (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.orbit.h)
    (htopology : ∀ z (hz : z ≠ 0) α lmb,
      topologyWorkload
        (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis : ∀ z (hz : z ≠ 0),
      templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (hlam : ∀ ω (hz : nprSeed ω ≠ 0) i,
      ((T.verifier.familyAt ω lmb hz).exec.memoryPubAt i).lambda = (T.verifier.familyAt ω lmb hz).cfg.challenges.lam)
    (hbinds : T.BindsAll) :
    |jointProbability (FalseAcceptanceSet T q Λ lmb)| ≤
      (workload T Λ topologyBound axisWorkload : ℝ) /
        (Fintype.card K : ℝ) := by
  apply jointProbability_falseAcceptance_le h2 T lmb C q topologyBound axisWorkload
    hwindowBound htopology haxis
  intro ω hacc hout
  exact accepted_outside_failureUnion T C q hchar hq hqChar hcast hbound hcombined
    hop hKp hProgCap hMemCap hbinds ω lmb hacc hout (fun hz => hlam ω hz)

end

end Nock.NockVMROM.Thm54.ProductionP8Containment

#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.failureUnion_card_le
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.bareSemanticSupport_no_proof_carrying_fields
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.productionRawTimestamp_exact_shape
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.productionRawSeedCarrier_exact_shape
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.topologyWorkload_le_fixedTopologyWorkload
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.templateAxisWorkload_le_fixedAxisWorkload
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.accepted_outside_failureUnion_at
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.accepted_outside_failureUnion
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.honestBinds
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.ext_of_verifier_skeleton
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.jointProbability_falseAcceptance_le
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.exactProductionFixedFieldSoundness
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.production_jointProbability_falseAcceptance_le
#check Nock.NockVMROM.Thm54.ProductionP8Containment.production_jointProbability_falseAcceptance_le
#check Nock.NockVMROM.Thm54.SemanticTimestampStrategy.DataOnlyTemplateFixedStagedTimestampStrategy.ofRawData
#check Nock.NockVMROM.Thm54.SemanticTimestampStrategy.DataOnlyTemplateFixedStagedTimestampStrategy.claim
#check Nock.NockVMROM.Thm54.SemanticTimestampStrategy.DataOnlyTemplateFixedStagedTimestampStrategy.afterSeed
#check Nock.NockVMROM.Thm54.SemanticTimestampStrategy.DataOnlySeedFixedTimestampCarrier.configTemplate
#check Nock.NockVMROM.Thm54.SemanticTimestampStrategy.DataOnlySeedFixedTimestampCarrier.executionTemplate
#check Nock.NockVMROM.Thm54.SemanticTimestampStrategy.DataOnlySeedFixedTimestampCarrier.sampledSeed
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.specializedAxisValidity_of_accepts

