import Nock.NockVMROM.Thm54.ProductionP8Containment

/-!
# AcceptedContent — what the production spine consumes from `Accepts`

`T.Accepts ω lmb` is
`VerifierChecks` = `VerifierGates ∧ SixRAPSatisfy` at the abstract K-side
RAPs (`computeTableRAP kind`, `w = 94`, `e = 1`).  The spine does not
consume that RAP satisfaction.  It consumes the row predicates, lists and
equalities that `computeTable_sound_wfFree` / `memoryTable_sound_wfFree`
and the endpoint / IO extraction get out of it.

This module names that conjunction `AcceptedContent` and restates the
spine at it.  The type mentions no `computeTableRAP`, no `SixRAPSatisfy`,
no `RAP.Satisfies`.
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
open ProductionRawVerifier

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable [charRing : CharP K (ringChar K)]
variable {Λ : ℕ}

/-! ## The extracted content of `Accepts` -/

/-- Facts the production spine reads off `hacc : T.Accepts ω lmb`.

Row predicates (`Vcomp`/`Vmem`, BFS `ComputeRowsAccepted`/`MemoryRowsAccepted`,
`RVT` topology), IO lists and `IO.LIO`, walk-boundary zeros, public-input
equalities, the α-free axis Bool, and `z ≠ 0`.  No `computeTableRAP`,
`SixRAPSatisfy`, or `RAP.Satisfies`.

Topology is the one conjunct whose *extraction* from `Accepts` uses
`ω ∉ specializedTopologyFailureEvent` (the same `houtG` the original
spine already had).  The proposition itself is `RVTWithArity` on the
authoritative trees. -/
structure AcceptedContent
    (T : ProductionStrategy F K) (ω : JointCoins K) (lmb : K) : Prop where
  seed_ne : nprSeed ω ≠ 0
  z_eq :
    (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).challenges.z =
      nprSeed ω
  computeRows :
    (T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).ComputeRowsAccepted
  memoryRows :
    (T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).MemoryRowsAccepted
  vcomp :
    ∀ i, ComputeTable.Vcomp
      (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).challenges.computeInputs
      ((T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).computePubAt i)
      ((T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).computeDecAt i)
  vmem :
    ∀ i, MemoryTable.Vmem
      (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).challenges.memoryInputs
      ((T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).memoryPubAt i)
  ln_chain :
    ∀ i : Fin (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).compRows,
      ∀ hi : (i : ℕ) + 1 <
          (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).compRows,
        ((T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).computePubAt i).ln =
          ((T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).computePubAt
            ⟨(i : ℕ) + 1, hi⟩).ln_prev
  mem_icur_chain :
    ∀ i : Fin (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).memRows,
      ∀ hi : (i : ℕ) + 1 <
          (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).memRows,
        ((T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).memoryPubAt i).icur =
          ((T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).memoryPubAt
            ⟨(i : ℕ) + 1, hi⟩).ipre
  mem_first_counts :
    ((T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).memoryPubAt
      ⟨0, (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).memRows_pos⟩).pt.counts =
      0
  mem_first_indicator :
    ((T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).memoryPubAt
      ⟨0, (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).memRows_pos⟩).pt.indicator =
      0
  mem_first_ipre :
    ((T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).memoryPubAt
      ⟨0, (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).memRows_pos⟩).ipre = 0
  mem_last_icur :
    ((T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).memoryPubAt
      ((T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).orbit.lastIndex
        (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).memRows
        (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).memRows_pos)).icur = 0
  io :
    IO.LIO (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).Ksz
      (T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).derivedRequestIO
      (T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).derivedResponseIO
  public_subject :
    ((T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).computePubAt
      ⟨0, (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).compRows_pos⟩).s =
      GlobalCarryRecognizer.enc (nprSeed ω) T.verifier.raw.claim.subject
  public_formula :
    ((T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).computePubAt
      ⟨0, (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).compRows_pos⟩).f =
      GlobalCarryRecognizer.enc (nprSeed ω) T.verifier.raw.claim.formula
  public_result :
    ((T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb).computePubAt
      ⟨0, (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb).compRows_pos⟩).e =
      GlobalCarryRecognizer.enc (nprSeed ω) T.verifier.raw.claim.result
  computeTopology :
    ComputeExactTopology (T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb)
  memoryTopology :
    MemoryExactTopology (T.specializedExec (nprSeed ω) seed_ne (alphaM ω) lmb)
  -- Was `specializedExec`.
  axisStructural :
    ExactAxisStructuralRefinement
      (T.specializedCfg (nprSeed ω) seed_ne (alphaM ω) lmb)
      (T.specializedExecA (nprSeed ω) seed_ne (alphaM ω) lmb)
  rootBoundary :
    T.RootAxisBoundaryAt (nprSeed ω) seed_ne (alphaM ω)
  structuralChecks :
    structuralChecksAt T.verifier (nprSeed ω) seed_ne (alphaM ω) = true

set_option maxHeartbeats 800000 in
theorem acceptedContent_of_accepts
    (T : ProductionStrategy F K)
    (ω : JointCoins K) (lmb : K)
    (hchar : NodeEncoding.StateTagChar K)
    (hKp : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.Ksz <
        ringChar K)
    (hProgCap : ∀ z (hz : z ≠ 0) α lmb,
      ((specializedProblem T.verifier.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1) ≤
        2 ^ (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.orbit.h)
    (hMemCap : ∀ z (hz : z ≠ 0) α lmb,
      ((specializedProblem T.verifier.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1) ≤
        2 ^ (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.orbit.h)
    (hacc : T.Accepts ω lmb)
    (houtG : ω ∉ specializedTopologyFailureEvent T.verifier.raw lmb)
    (hlam : ∀ (hz : nprSeed ω ≠ 0) i,
      ((T.verifier.familyAt ω lmb hz).exec.memoryPubAt i).lambda = (T.verifier.familyAt ω lmb hz).cfg.challenges.lam) :
    AcceptedContent T ω lmb := by
  have hz : nprSeed ω ≠ 0 := by
    intro hz0
    simp [ProductionStrategy.Accepts, hz0] at hacc
  have hraw := T.productionRawAccepts_of_accepts ω lmb hz hacc
  have hmsg := (T.verifier.accepts_iff_production ω lmb hz).1 hraw
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
  have hct :=
    ProductionRawVerifier.Message.computeTable_sound_wfFree
      (T.verifier.messageAt ω lmb hz) T.verifier.raw.claim ω hchar hmsg
  have hmt :=
    ProductionRawVerifier.Message.memoryTable_sound_wfFree
      (T.verifier.messageAt ω lmb hz) T.verifier.raw.claim ω hchar (hlam hz) hmsg
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
  have hstructProd :=
    ProductionAxisStructureVerifier.exactAxisStructuralRefinement_of_accepts
      T.verifier ω lmb hz (T.productionAxisAccepts_of_accepts ω lmb hz hacc)
  have hroot := ((T.accepts_iff ω lmb hz).1 hacc).2
  have hchecks :=
    ((ProductionAxisStructureVerifier.accepts_iff T.verifier ω lmb hz).1
      (T.productionAxisAccepts_of_accepts ω lmb hz hacc)).2
  have hgates := hmsg.1
  refine
    { seed_ne := hz
      z_eq := ?z_eq
      computeRows := ?rows
      memoryRows := ?mems
      vcomp := ?vcomp
      vmem := ?vmem
      ln_chain := ?ln
      mem_icur_chain := ?icur
      mem_first_counts := ?cnt
      mem_first_indicator := ?ind
      mem_first_ipre := ?ipre
      mem_last_icur := ?icur0
      io := ?io
      public_subject := ?ps
      public_formula := ?pf
      public_result := ?pe
      computeTopology := ?ctop
      memoryTopology := ?mtop
      axisStructural := hstructProd
      rootBoundary := hroot
      structuralChecks := hchecks }
  · simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedCfg] using hgates.2.1
  · simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using hrowsProd
  · simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using hmemRowsProd
  · intro i
    simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using hct.1.1 i
  · intro i
    simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using hmt.1.1 i
  · intro i hi
    simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using hct.1.2 i hi
  · intro i hi
    simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using hmt.1.2.1 i hi
  · simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using hmt.1.2.2.1
  · simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using hmt.1.2.2.2.1
  · simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using hmt.1.2.2.2.2.1
  · simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using hmt.1.2.2.2.2.2
  · simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using hioProd
  · simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using
        hgates.2.2.2.2.2.2.2.1
  · simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using
        hgates.2.2.2.2.2.2.2.2.1
  · simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using
        hgates.2.2.2.2.2.2.2.2.2.1
  · simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using htopProd.1
  · simpa [ProductionRawVerifier.TemplateAdapter.Strategy.familyAt,
      TemplateRawJointSoundness.Strategy.familyAt,
      TemplateRawJointSoundness.AlphaMFamilyData.atCoins,
      TemplateRawJointSoundness.AlphaMFamilyData.base,
      ProductionStrategy.specializedExec, ProductionStrategy.specializedCfg] using htopProd.2

/-- `acceptedContent_of_accepts` from the spine's `hout` (the topology
event is one class of `FailureUnion`). -/
theorem acceptedContent_of_accepts_outside
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (ω : JointCoins K) (lmb : K)
    (hchar : NodeEncoding.StateTagChar K)
    (hKp : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.Ksz <
        ringChar K)
    (hProgCap : ∀ z (hz : z ≠ 0) α lmb,
      ((specializedProblem T.verifier.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1) ≤
        2 ^ (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.orbit.h)
    (hMemCap : ∀ z (hz : z ≠ 0) α lmb,
      ((specializedProblem T.verifier.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1) ≤
        2 ^ (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.orbit.h)
    (hacc : T.Accepts ω lmb)
    (hout : ω ∉ FailureUnion T C lmb)
    (hlam : ∀ (hz : nprSeed ω ≠ 0) i,
      ((T.verifier.familyAt ω lmb hz).exec.memoryPubAt i).lambda = (T.verifier.familyAt ω lmb hz).cfg.challenges.lam) :
    AcceptedContent T ω lmb :=
  acceptedContent_of_accepts T ω lmb hchar hKp hProgCap hMemCap hacc (by
    intro h
    apply hout
    simp [FailureUnion, h]) hlam

set_option maxHeartbeats 800000 in
/-- **Axis validity from the extracted content** (the tail of
`specializedAxisValidity_of_accepts`, from `structuralChecks`/`rootBoundary` instead of `Accepts`):
`AcceptedContent` carries exactly the two acceptance facts the argument reads. -/
theorem specializedAxisValidity_of_content
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K) (ω : JointCoins K) (lmb : K)
    (hz : nprSeed ω ≠ 0)
    (hchecks : structuralChecksAt T.verifier (nprSeed ω) hz (alphaM ω) = true)
    (hroot : T.RootAxisBoundaryAt (nprSeed ω) hz (alphaM ω))
    (hout : ω ∉ guardedAxisFailureEvent T lmb) :
    ExactMemoryAxisValidity
      (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb)
      (T.specializedExecA (nprSeed ω) hz (alphaM ω) lmb) := by
  have hparts :
      alphaFreeAxisStructureCheck
          (committedTemplate T.verifier (nprSeed ω) hz) = true ∧
        noWrapCheck
          (committedTemplate T.verifier (nprSeed ω) hz) (alphaM ω) = true := by
    simpa [structuralChecksAt] using hchecks
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

set_option maxHeartbeats 800000 in
/-- Relaxis recovery is the remaining join
    (`Batch558.cancellingTree_is_remaining_join`); not derived from
    `AcceptedContent` plus the priced event. -/
theorem accepted_outside_failureUnion_content
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
    (_hKp : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.Ksz <
        ringChar K)
    (_hProgCap : ∀ z (hz : z ≠ 0) α lmb,
      ((specializedProblem T.verifier.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1) ≤
        2 ^ (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.orbit.h)
    (_hMemCap : ∀ z (hz : z ≠ 0) α lmb,
      ((specializedProblem T.verifier.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1) ≤
        2 ^ (specializedProblem T.verifier.raw.timestamp z hz α lmb).cfg.orbit.h)
    (ω : JointCoins K) (lmb : K)
    (hbinds : T.BindsAtCoin ω lmb)
    (hacc : AcceptedContent T ω lmb)
    (hout : ω ∉ FailureUnion T C lmb) :
    GenuineTargetAt T q Λ ω lmb := by
  have hz : nprSeed ω ≠ 0 := hacc.seed_ne
  let exec := T.specializedExec (nprSeed ω) hz (alphaM ω) lmb
  have binds : SemanticStrategy.BindsAt (nprSeed ω) T.skeleton
      (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb) exec :=
    hbinds hz
  have houtC : ω ∉ collisionFailureEvent C.census := by
    intro h
    apply hout
    simp [FailureUnion, h]
  have _houtA : ω ∉ guardedAxisFailureEvent T lmb := by
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
  have hrows : exec.ComputeRowsAccepted := hacc.computeRows
  have hmemRows : exec.MemoryRowsAccepted := hacc.memoryRows
  have htop : ComputeExactTopology exec ∧ MemoryExactTopology exec :=
    ⟨hacc.computeTopology, hacc.memoryTopology⟩
  have hstruct : ExactAxisStructuralRefinement
      (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb)
      (T.specializedExecA (nprSeed ω) hz (alphaM ω) lmb) :=
    hacc.axisStructural
  have hio : IO.LIO
      (T.specializedCfg (nprSeed ω) hz (alphaM ω) lmb).Ksz
      exec.derivedRequestIO exec.derivedResponseIO :=
    hacc.io
  have hcombinedAt : CombinedBoundedBy K q T.skeleton := hcombined
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
      specializedAxisValidity_of_content (two_ne_zero_of_stateTagChar hchar) T ω lmb hz
        hacc.structuralChecks hacc.rootBoundary _houtA⟩ }⟩
  · intro i
    have hr := ExactExecution.computeRowAt_accepted hrows i
    rw [← hr.2.1]
    exact hr.2.2
  · intro i
    have hr := ExactExecution.memoryRowAt_accepted hmemRows i
    rw [← hr.2.1]
    exact hr.2.2.1

/-- Converse control: the seed-local `Accepts` spine is the content
restatement at `acceptedContent_of_accepts_outside`. -/
theorem accepted_outside_failureUnion_at_of_content
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
    GenuineTargetAt T q Λ ω lmb :=
  accepted_outside_failureUnion_content T C q hchar hq hqChar hcast hbound
    hcombined hop hKp hProgCap hMemCap ω lmb hbinds
    (acceptedContent_of_accepts_outside T C ω lmb hchar hKp hProgCap hMemCap hacc hout hlam)
    hout

end

end Nock.NockVMROM.Thm54.ProductionP8Containment

#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.acceptedContent_of_accepts
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.accepted_outside_failureUnion_content
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.accepted_outside_failureUnion_at_of_content
