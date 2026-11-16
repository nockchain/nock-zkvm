/-
  Nock/NockVMROM/Thm54/TraceGen/GenGenuineTarget.lean

  **`GenuineTargetAt` at the generic honest carrier, and over the program.**

  `GenAcceptingCoin.lean`'s header states the open item precisely: a non-empty
  acceptance set "is not yet an informative `containment` conclusion — that
  additionally needs `honestCoin E a g ∉ ProductionP8Containment.FailureUnion`,
  which is not supplied here".  This module supplies it.

  ## Which route was taken for the topology and axis summands

  `FailureUnion T C` (`ProductionP8Containment.lean:539`) has five summands.
  Two of them — `specializedTopologyFailureEvent` (3) and
  `guardedAxisFailureEvent` (4) — are the ones the counting route
  (`GenFailureUnionCounting.lean`) reaches without acceptance and the honest
  fibre reaches without escape.  They are discharged here **directly at the
  committed `(z, alphaM)`**, i.e. route (a):

  * Summand 4 depends on `(alphaM, nprSeed)` only
    (`guardedAxisFailureEvent := univ ×ˢ guardedSeedAxisPairs`), and the honest
    fibre `honestCoin E a g` fixes both to `(E.cfg.challenges.α,
    E.cfg.challenges.z)` (`GenericHonestArrays.honestCoin_coordinates`).  So
    **no** member of the fibre can escape summand 4 by varying `(a, g)`: route
    (b) is impossible for it, not merely expensive.  What discharges it is
    `verifierGuardedRootAlphas`' third conjunct — the existence of a record
    where `vaxis ≠ Relaxis` — contradicted at the honest specialization by
    `ExactMemoryAxisValidity`, which `BuildableNockExecution.memoryTrace`
    already carries (`ServedMemoryTrace.axisValidity`).  This is the paper's
    per-node axis carry.
  * Summand 3 does read `gamma ω`, so route (b) is *not* a priori dead there,
    but it is unnecessary: at the honest specialization the topology binding
    holds, and `topologyBadGammas` of a bound family is **empty**
    (`MultiRootHonestArrays.topologyBadGammas_empty_of_binding`, a `∀`-generic
    theorem despite its fixture filename).  So every `gamma` escapes.

  Summands 1, 2 and 5 are the seed-side ones `GenCombinedCensusGood.lean`
  already owns.  Summand 1 is `Data.honestSeed_ne`.  Summands 2 and 5 stay
  **hypotheses** here: census goodness and the size-window seed condition are
  genuine premises of the honest carrier — no `Data` field implies them — and
  they are exactly what `nockCompiles_of_accepted_accepting` already carries on
  the generated path (`hbad`, `hout`).

  ## Scope: what is new and what already existed

  `GenuineTargetAt` is **not** reached here for the first time.  It is already instantiated at
  three K97cubic fixtures over hand-written commitments: `MultiRootHonestArrays.genuineTargetM`,
  `MultiRootNonzeroChallenges.genuineTargetN` and `MultiRootPhaseCorrect.lean:579`, each by the
  same `P.containment` route and each with its own fixture-specific proofs that the honest coin
  misses summands 3 and 4.  What is new is (i) that those two arguments are `∀ E, ∀ D` facts about
  *any* buildable carrier and *any* commitment over it, not fixture computations, and (ii) that the
  resulting conclusion therefore reaches the **generator's own** carrier and program
  (`nockCompiles_of_accepted_genuine`, §9) rather than a renderer-constructed fixture.

  ## What is *not* re-derived

  `accepted_outside_failureUnion` (`ProductionP8Containment.lean:598`) is not
  called here.  The released statement `OptimizedFullStrictThm54Statement`
  already carries its conclusion as the `containment` field
  (`OptimizedStrictFullPackage.lean:880`), discharged once and for all by
  `OptimizedFullStrictNockVMROMPackage.containment`
  (`OptimizedStrictFullPackage.lean:149`) from package fields.  So `hchar`,
  `hq`, `hqChar`, `hcast`, `hbound`, `hcombined`, `hop`, `hKp`, `hProgCap` and
  `hMemCap` are all already discharged by the constructed package and need not
  reappear.  Only `hacc` and `hout` are open, and this module closes `hout`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenAcceptingCoin
import Nock.NockVMROM.Thm54.TraceGen.GenCombinedCensusGood
import Nock.NockVMROM.Thm54.MultiRootHonestArrays
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.AxisBridge AxisBatching.MTree
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.ForestExponentOrderClosure
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

variable {lmb : K}
variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
variable {E : BuildableNockExecution F K}

/-! ## 1. The honest specialization of the committed template

Everything below rests on `Data.honest_exec`: at the honest sample the committed template
specializes to the supplied execution, on the nose and at the *same* configuration
(`Data.honest_cfg` is `rfl`).  So the two carried semantic conclusions of
`BuildableNockExecution` — the two exact topologies and the served axis validity — transport to
the object the two verifier events are computed from. -/

/-- The committed post-`alphaM` base family, at the honest sample, is a family over the supplied
execution.  This is `Data.honest_specialization` named at the family layer. -/
theorem honestBase_problem (D : Data E) (hchar : NodeEncoding.StateTagChar K)
    (hz : E.cfg.challenges.z ≠ 0) :
    ((rawStrategyOf D hchar).afterAlphaM E.cfg.challenges.z hz
        E.cfg.challenges.α E.cfg.challenges.lam).familyData.base.problem =
      (⟨E.cfg, E.exec⟩ : RawProblem F K) :=
  D.honest_specialization

/-- **The honest topology binding, generically.**  Both exact topologies and both
rows-accepted facts are carried by `BuildableNockExecution`, so the raw topology binding
residual holds at the committed base family -/
theorem honestBase_topologyBinding (D : Data E) (hchar : NodeEncoding.StateTagChar K)
    (hz : E.cfg.challenges.z ≠ 0) :
    RawTopologyBindingResidual
      (((rawStrategyOf D hchar).afterAlphaM E.cfg.challenges.z hz
        E.cfg.challenges.α E.cfg.challenges.lam).familyData.base) := by
  have hexec :
      ((D.executionTemplate E.cfg.challenges.z).specialize E.cfg.challenges.α E.cfg.challenges.lam) = E.exec :=
    D.honest_exec
  have hc :
      (((rawStrategyOf D hchar).afterAlphaM E.cfg.challenges.z hz
        E.cfg.challenges.α E.cfg.challenges.lam).familyData.base).exec.ComputeRowsAccepted := by
    show ((D.executionTemplate E.cfg.challenges.z).specialize
      E.cfg.challenges.α E.cfg.challenges.lam).ComputeRowsAccepted
    rw [hexec]
    exact BuildablePackage.computeRowsAccepted E
  have hm :
      (((rawStrategyOf D hchar).afterAlphaM E.cfg.challenges.z hz
        E.cfg.challenges.α E.cfg.challenges.lam).familyData.base).exec.MemoryRowsAccepted := by
    show ((D.executionTemplate E.cfg.challenges.z).specialize
      E.cfg.challenges.α E.cfg.challenges.lam).MemoryRowsAccepted
    rw [hexec]
    exact BuildablePackage.memoryRowsAccepted E
  refine (exactTopology_iff_rawTopologyBindingResidual_of_rowsAccepted _ hc hm).1 ?_
  constructor
  · show ComputeExactTopology
      ((D.executionTemplate E.cfg.challenges.z).specialize E.cfg.challenges.α E.cfg.challenges.lam)
    rw [hexec]
    exact E.traversal.1
  · show MemoryExactTopology
      ((D.executionTemplate E.cfg.challenges.z).specialize E.cfg.challenges.α E.cfg.challenges.lam)
    rw [hexec]
    exact E.traversal.2

/-! ## 2. Summand 3: the verifier-generated topology event -/

/-- **Summand 3 at the honest fibre.**  Every later-round `gamma` escapes: a bound family has an
empty bad-`gamma` set, so the event is empty at the committed `(z, alphaM)` fibre. -/
theorem honestCoin_not_mem_specializedTopologyFailureEvent
    (D : Data E) (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    honestCoin E a g ∉ specializedTopologyFailureEvent (rawStrategyOf D hchar) E.cfg.challenges.lam := by
  intro hmem
  rw [mem_specializedTopologyFailureEvent_iff] at hmem
  obtain ⟨hz, hbad⟩ := hmem
  have hbad' : g ∈ topologyBadGammas
      (((rawStrategyOf D hchar).afterAlphaM E.cfg.challenges.z D.honestSeed_ne
        E.cfg.challenges.α E.cfg.challenges.lam).familyData.base) := hbad
  rw [MultiRootHonestArrays.topologyBadGammas_empty_of_binding _
    (honestBase_topologyBinding D hchar D.honestSeed_ne)] at hbad'
  exact absurd hbad' (Finset.notMem_empty _)

/-! ## 3. Summand 4: the checker-guarded template-axis event

`RootAxisBoundaryAt` is documented as "a verifier equation, not an assumed
`ExactAxisRefinement.root_accepts` field" (`ProductionP8Containment.lean:110`), and indeed the
guarded set's third conjunct is a *bad-record witness*.  At the honest specialization there is no
bad record: `ExactMemoryAxisValidity` is a projection of the carried served memory trace. -/

/-- Served axis validity of the supplied carrier, transported to the honest specialization of the
committed template.  `Data.honest_cfg` is `rfl`, so no configuration transport is needed. -/
theorem honestTemplate_axisValidity (D : Data E) :
    ExactMemoryAxisValidity
      ((configTemplateOf E E.cfg.challenges.z).specialize E.cfg.challenges.α E.cfg.challenges.lam)
      ((D.executionTemplate E.cfg.challenges.z).specializeA E.cfg.challenges.α E.cfg.challenges.lam) := by
  have hexec :
      ((D.executionTemplate E.cfg.challenges.z).specializeA E.cfg.challenges.α E.cfg.challenges.lam) = E.execA :=
    D.honest_execA
  rw [hexec]
  exact E.memoryTrace.axisValidity

/-- **Summand 4 at the honest fibre.**  The honest `alphaM` is guarded by no root: the guarded set
requires a record on which `vaxis` and `Relaxis` disagree, and axis validity says there is none. -/
theorem honestAlpha_not_mem_verifierGuardedRootUnion (D : Data E) :
    E.cfg.challenges.α ∉
      verifierGuardedRootUnion (D.executionTemplate E.cfg.challenges.z) E.cfg.challenges.lam := by
  intro hmem
  obtain ⟨i, -, hf⟩ := Finset.mem_biUnion.1 hmem
  simp only [verifierGuardedRootAlphas, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  obtain ⟨-, -, ⟨e, hread, hverify, hne⟩, -⟩ := hf
  exact hne (honestTemplate_axisValidity D i e hread hverify)

/-! ## 4. The full failure union at the honest fibre -/

variable {hOrb : ℕ}

/-- `packageOf`'s strategy verifier is the honest adapter over `rawStrategyOf`; the committed
template at the honest seed is `D.executionTemplate`.  Both by `rfl`. -/
theorem packageOf_strategy_raw (D : Data E) (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier.raw =
      rawStrategyOf D (stateTagChar_of_paper_char hgt) :=
  rfl

/-- **The honest coin lies outside `FailureUnion`.**  Three summands are theorems about the
carrier; census goodness and the size-window seed condition are hypotheses, and they are exactly
`nockCompiles_of_accepted_accepting`'s `hbad`/`hout` -/
theorem honestCoin_not_mem_failureUnion
    (D : Data E) (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hgood : E.cfg.challenges.z ∉ D.census.census.badSeeds (K := K))
    (hwin : E.cfg.challenges.z ∉ sizeWindowFailureSeeds (K := K) D.skeleton)
    (a g : K) :
    honestCoin E a g ∉
      ProductionP8Containment.FailureUnion (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy
        (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).optimized.census E.cfg.challenges.lam := by
  refine not_mem_failureUnion_of_seed _ _ D.honestSeed_ne (z := E.cfg.challenges.z) rfl
    hgood hwin ?_ ?_
  · exact honestCoin_not_mem_specializedTopologyFailureEvent D
      (stateTagChar_of_paper_char hgt) a g
  · intro hmem
    rw [mem_guardedAxisFailureEvent_iff] at hmem
    obtain ⟨hz, hmem⟩ := hmem
    have hmem' : E.cfg.challenges.α ∈
        verifierGuardedRootUnion (D.executionTemplate E.cfg.challenges.z) E.cfg.challenges.lam := hmem
    exact honestAlpha_not_mem_verifierGuardedRootUnion D hmem'

/-! ## 5. `GenuineTargetAt` at the generic honest carrier -/

/-- **The soundness conclusion, at any honest carrier, at any accepted honest coin.**

`GenuineWitness` carries `Vcomp` and `Vmem` at every row, `exactLIO`, both topologies,
`localPairFaithful`/`edgePairFaithful`, `canonicalRows`, `rootPublicNouns`, `evalFByPublic`,
`publicClaimHoldsMod` and the two axis refinements
(`ProductionP8Containment.lean:314-366`) -/
theorem genuineTarget_of_honest_coin
    (D : Data E) (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hgood : E.cfg.challenges.z ∉ D.census.census.badSeeds (K := K))
    (hwin : E.cfg.challenges.z ∉ sizeWindowFailureSeeds (K := K) D.skeleton)
    (a g : K)
    (hacc : (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts (honestCoin E a g) E.cfg.challenges.lam) :
    GenuineTargetAt (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy E.q D.Λ (honestCoin E a g) E.cfg.challenges.lam :=
  (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).containment (honestCoin E a g) E.cfg.challenges.lam hacc
    (honestCoin_not_mem_failureUnion D hgt I hprl hmore hord hordM hrows hgenF hF hgood hwin a g)

/-- **The genuine target at the canonically stamped commitment, with acceptance unconditional.**
`normalised_package_fibre_accepts` needs no hypothesis on `α`, so the only premises left are the
census and size-window seed conditions at `normData D` -/
theorem exists_accepting_genuineTarget_of_carrier
    (D : Data E) (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hgood : E.cfg.challenges.z ∉ (normData D).census.census.badSeeds (K := K))
    (hwin : E.cfg.challenges.z ∉ sizeWindowFailureSeeds (K := K) (normData D).skeleton) :
    ∃ ω : JointCoins K,
      (packageOf (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF).strategy.Accepts ω E.cfg.challenges.lam ∧
        GenuineTargetAt (packageOf (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF).strategy E.q (normData D).Λ ω E.cfg.challenges.lam :=
  ⟨honestCoin E 0 0,
    normalised_package_fibre_accepts D hgt I hprl hmore hord hordM hrows hgenF hF 0 0,
    genuineTarget_of_honest_coin (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF hgood hwin 0 0
      (normalised_package_fibre_accepts D hgt I hprl hmore hord hordM hrows hgenF hF 0 0)⟩


/-! ## 6. Transport along a skeleton equality

`EdgeComparisonCensus.CombinedSkeletonCensus` is a `Prop` and its `census` projection is
`ComparisonCensus.ofPairList (combinedSkeletonPairs K S)`, so the bad-seed set is a function of
the *committed skeleton alone*.  That is what makes the two carried premises transport across
`normData` (which preserves the skeleton) and across `genSkeletonOfNodes_eq`. -/

/-- Two combined censuses over equal skeletons have the same bad seeds. -/
theorem combinedCensus_badSeeds_congr {Λ : ℕ}
    {S₁ S₂ : SemanticStrategy.SemanticSkeleton} (h : S₁ = S₂)
    (C₁ : EdgeComparisonCensus.CombinedSkeletonCensus K S₁ Λ)
    (C₂ : EdgeComparisonCensus.CombinedSkeletonCensus K S₂ Λ) :
    C₁.census.badSeeds (K := K) = C₂.census.badSeeds (K := K) := by
  subst h
  rfl

/-- Membership-transport form of `combinedCensus_badSeeds_congr`.  Stated separately because the
`census` projection carries the skeleton as an implicit argument, so `rw` cannot bridge two
syntactically different but definitionally equal indices. -/
theorem not_mem_combinedCensus_badSeeds_congr {Λ : ℕ}
    {S₁ S₂ : SemanticStrategy.SemanticSkeleton} (h : S₁ = S₂)
    (C₁ : EdgeComparisonCensus.CombinedSkeletonCensus K S₁ Λ)
    (C₂ : EdgeComparisonCensus.CombinedSkeletonCensus K S₂ Λ)
    {z : K} (hz : z ∉ C₂.census.badSeeds (K := K)) :
    z ∉ C₁.census.badSeeds (K := K) := by
  subst h
  exact hz

/-- `normData` preserves the committed bad-seed set, because it preserves the committed
skeleton -/
theorem normData_census_badSeeds (D : Data E) :
    (normData D).census.census.badSeeds (K := K) = D.census.census.badSeeds (K := K) :=
  combinedCensus_badSeeds_congr (normData_skeleton D) _ _

/-! ## 7. The genuine target at the canonically stamped commitment, premises stated at `D` -/

/-- `exists_accepting_genuineTarget_of_carrier` with both premises stated at `D` itself rather
than at `normData D` -/
theorem exists_accepting_genuineTarget_of_carrier'
    (D : Data E) (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hgood : E.cfg.challenges.z ∉ D.census.census.badSeeds (K := K))
    (hwin : E.cfg.challenges.z ∉ sizeWindowFailureSeeds (K := K) D.skeleton) :
    ∃ ω : JointCoins K,
      (packageOf (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF).strategy.Accepts ω E.cfg.challenges.lam ∧
        GenuineTargetAt (packageOf (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF).strategy E.q D.Λ ω E.cfg.challenges.lam := by
  refine exists_accepting_genuineTarget_of_carrier D hgt I hprl hmore hord hordM hrows hgenF hF ?_ ?_
  · rw [normData_census_badSeeds D]
    exact hgood
  · rw [normData_skeleton D]
    exact hwin

/-! ## 8. The released package with a genuine target, at an arbitrary carrier

This is `exists_accepting_package_of_carrier` (`GenAcceptingCoin.lean:89`) with a fourth
conjunct: the acceptance set is not only non-empty, it contains a coin at which the **soundness
conclusion** `GenuineTargetAt` holds. -/

/-- **`∃ package, Statement package ∧ the claim is this triple ∧ the whole honest fibre accepts ∧
some accepted coin reaches `GenuineTargetAt`**, at an arbitrary buildable carrier and an
arbitrary committed `Data` over it, given census goodness and the size-window seed condition at
the committed seed.

The witnessed coin discharges **both** of `containment`'s antecedents
(`OptimizedStrictFullPackage.lean:880`): `Accepts ω` *and*
`ω ∉ ProductionP8Containment.FailureUnion`, the latter from
`honestCoin_not_mem_failureUnion`.  Stating only the first would leave open whether any
accepting coin is also outside the failure union, which is where `containment`'s conclusion
becomes reachable -/
theorem exists_genuine_package_of_carrier
    (D : Data E) {hOrb : ℕ}
    (hgt : 11 < ringChar K)
    (stc : NodeEncoding.StateTagChar K)
    (bas : Module.Basis (Fin 3) F K)
    (orbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ E.cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : E.exec.derivedRequestIO.length ≤ n)
    (hresp : E.exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (computeWalkAlpha memoryWalkAlpha walkGamma : K)
    (memoryScalarChallenge : Fin 4 → F) (memoryExtensionFold : K)
    (hmemn : E.cfg.memRows ≤ n)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    {subject formula result : Noun}
    (hclaim : (Data.skeleton D).publicClaim = ⟨subject, formula, result⟩)
    (hgood : E.cfg.challenges.z ∉ D.census.census.badSeeds (K := K))
    (hwin : E.cfg.challenges.z ∉ sizeWindowFailureSeeds (K := K) D.skeleton)
    (hax : FormRAxisBound
      (packageOf (normData D) hgt
        (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
          computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound E hmemn hcard) hhon)
        hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (packageOf (normData D) hgt
        (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
          computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound E hmemn hcard) hhon)
        hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hbasis : FormRBasis
      (packageOf (normData D) hgt
        (inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
          computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound E hmemn hcard) hhon)
        hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : FormRWidth F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ (∀ a g : K, package.strategy.Accepts (honestCoin E a g) E.cfg.challenges.lam)
        ∧ ∃ ω : JointCoins K,
            package.strategy.Accepts ω E.cfg.challenges.lam ∧
              ω ∉ ProductionP8Containment.FailureUnion package.strategy
                    package.optimized.census E.cfg.challenges.lam ∧
              GenuineTargetAt package.strategy E.q D.Λ ω E.cfg.challenges.lam := by
  set I : Inputs E :=
    inputsOfCarrier E stc bas orbit hcap n hreq hresp hcard
      computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
      (interCard_of_unionBound E hmemn hcard) hhon
    with hI
  refine ⟨packageOf (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF,
    statementOf (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF hax hbasis hwidth,
    ?_, ?_, ?_⟩
  · have h2 : (Data.skeleton (normData D)).publicClaim = ⟨subject, formula, result⟩ := by
      rw [normData_skeleton D]; exact hclaim
    exact (commitmentResidualOfArrays_of_char (normData D) hgt).claim_eq.symm.trans h2
  · exact normalised_package_fibre_accepts D hgt I hprl hmore hord hordM hrows hgenF hF
  · have hgood' : E.cfg.challenges.z ∉ (normData D).census.census.badSeeds (K := K) := by
      rw [normData_census_badSeeds D]; exact hgood
    have hwin' : E.cfg.challenges.z ∉
        sizeWindowFailureSeeds (K := K) (normData D).skeleton := by
      rw [normData_skeleton D]; exact hwin
    have hacc : (packageOf (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF).strategy.Accepts (honestCoin E 0 0) E.cfg.challenges.lam :=
      normalised_package_fibre_accepts D hgt I hprl hmore hord hordM hrows hgenF hF 0 0
    have hout : honestCoin E (0 : K) (0 : K) ∉
        ProductionP8Containment.FailureUnion (packageOf (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF).strategy
          (packageOf (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF).optimized.census E.cfg.challenges.lam :=
      honestCoin_not_mem_failureUnion (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF hgood' hwin' 0 0
    have hgen : GenuineTargetAt (packageOf (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF).strategy E.q
        (normData D).Λ (honestCoin E 0 0) E.cfg.challenges.lam :=
      genuineTarget_of_honest_coin (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF hgood' hwin' 0 0 hacc
    exact ⟨honestCoin E 0 0, hacc, hout, hgen⟩

/-! ## 9. Over the program

`nockCompiles_of_accepted_accepting`'s premise list, unchanged and with nothing added: the two
seed conditions the genuine target needs are `hbad` (at the p8 census) and `hout`, which that
theorem already carries.  The witnessed coin satisfies both of `containment`'s antecedents; see
§8 -/

theorem nockCompiles_of_accepted_genuine {q Λ : ℕ}
    (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hseed : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)))
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t)))
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hmore : BuildableAxisWitness.LaterSeedZeros
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    {hOrb : ℕ}
    (stc : NodeEncoding.StateTagChar K)
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreqn : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ n)
    (hrespn : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (computeWalkAlpha memoryWalkAlpha walkGamma : K)
    (memoryScalarChallenge : Fin 4 → F) (memoryExtensionFold : K)
    (hord : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows ≤
        orderOf computeWalkAlpha)
    (hordM : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤
        orderOf memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
          hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    {fuelG : ℕ} {rG : Noun} (hG : FieldEmbedding.evalGBy q fuelG subject formula = some rG)
    (hF : GeneratedField.PrimeFieldElems F)
    (hax : FormRAxisBound
      (packageOf (normData (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst)) (hchar ▸ hq)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
              haxis hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
                  haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.sampled
      (packageOf (normData (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst)) (hchar ▸ hq)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
              haxis hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
                  haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.basis)
    (hbasis : FormRBasis
      (packageOf (normData (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst)) (hchar ▸ hq)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
              haxis hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
                  haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.basis)
    (hwidth : FormRWidth F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ (∀ a' g' : K, package.strategy.Accepts
            (honestCoin (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
              hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
              hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) a' g') chal.lam)
        ∧ ∃ ω : JointCoins K,
            package.strategy.Accepts ω chal.lam ∧
              ω ∉ ProductionP8Containment.FailureUnion package.strategy
                    package.optimized.census chal.lam ∧
              ProductionP8Containment.GenuineTargetAt package.strategy q Λ ω chal.lam := by
  have hgt : 11 < ringChar K := hchar ▸ hq
  have hzeq : chal.z = z := by
    have hproj := congrArg (fun inp : ComputeTable.Inputs K => inp.z) hinp
    simpa [ChallengeVector.computeInputs] using hproj
  set E : BuildableNockExecution F K :=
    genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
      haxis hbad hout hKszChar hprogCap hmemCap hfirst with hE
  set D : Data E :=
    genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
      haxis hbad hout hKszChar hprogCap hmemCap hfirst with hD
  have hseedz : E.cfg.challenges.z = z := hzeq
  have hskel : D.skeleton =
      genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t) :=
    genSkeletonOfNodes_eq z α a b c (memInputs z) t
  have hgood : E.cfg.challenges.z ∉ D.census.census.badSeeds (K := K) := by
    rw [hseedz]
    exact not_mem_combinedCensus_badSeeds_congr (Λ := Λ) hskel D.census
      (genComputeSkeleton_census_gen hΛ h hconf (genMemoryForest z α chal.lam (memInputs z) t))
      (combined_good_of_p8_good_bfsAssign hΛ h hconf
        (genMemoryForest z α chal.lam (memInputs z) t) z hbad)
  have hwindow : E.cfg.challenges.z ∉
      SizeWindowCounting.sizeWindowFailureSeeds (K := K) D.skeleton := by
    rw [hseedz, hskel]
    exact hout
  obtain ⟨package, hstmt, hclaim', hfibre, hgen⟩ :=
    exists_genuine_package_of_carrier (E := E) D (hOrb := hOrb) hgt stc bas packageOrbit
      (by
        show 2 ^ orbit.h ≤ 2 ^ hOrb
        exact hcap)
      n
      (by
        show (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
          (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).derivedRequestIO.length ≤ n
        exact genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
          (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
      (by
        show (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
          (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).derivedResponseIO.length ≤ n
        exact genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
          (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
      hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
      (by
        show (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
        exact hrespn)
      (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst)
      (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
        hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
        hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
      hmore
      hord hordM hrows (genDataOfProgram_claimGeneratedD hG) hF
      (genDataOfProgram_publicClaim (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst)
      hgood hwindow hax hbasis hwidth
  exact ⟨package, hstmt, hclaim', hfibre, hgen⟩

end

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.honestBase_topologyBinding
#print axioms Nock.NockVMROM.Thm54.TraceGen.honestCoin_not_mem_specializedTopologyFailureEvent
#print axioms Nock.NockVMROM.Thm54.TraceGen.honestAlpha_not_mem_verifierGuardedRootUnion
#print axioms Nock.NockVMROM.Thm54.TraceGen.honestCoin_not_mem_failureUnion
#print axioms Nock.NockVMROM.Thm54.TraceGen.genuineTarget_of_honest_coin
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_accepting_genuineTarget_of_carrier
#print axioms Nock.NockVMROM.Thm54.TraceGen.combinedCensus_badSeeds_congr
#print axioms Nock.NockVMROM.Thm54.TraceGen.not_mem_combinedCensus_badSeeds_congr
#print axioms Nock.NockVMROM.Thm54.TraceGen.normData_census_badSeeds
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_accepting_genuineTarget_of_carrier'
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_genuine_package_of_carrier
#print axioms Nock.NockVMROM.Thm54.TraceGen.nockCompiles_of_accepted_genuine
#check Nock.NockVMROM.Thm54.TraceGen.exists_genuine_package_of_carrier
#check Nock.NockVMROM.Thm54.TraceGen.nockCompiles_of_accepted_genuine
