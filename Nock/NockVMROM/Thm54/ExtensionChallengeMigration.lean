import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.GatheredMemoryScalarGates
import Nock.NockVMROM.Thm54.EqualityCheckLedger
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Stage 1 of the `𝔽 → 𝕂` challenge migration: the `𝕂`-typed track, carried to the package

`ExtensionChallenges.lean` re-types the five base-field challenge coordinates and re-derives the
whole counting over `ProductionChallengeTupleK K`, ending at
`ExtensionChallenges.soundnessK_at_paper_configuration` (`123` bits) and
`ExtensionChallenges.soundnessK_of_counted_event`.  That development is **parallel**: it lives
over its own tuple, and `probabilityBoundK_le_old` compares the two *formulas*, not the two
*events*.  The released capstone still carries `OptimizedProductionChallengeTuple K F`.

This module closes the distance that can be closed additively.  It carries the `𝕂`-typed track
onto `OptimizedFullStrictNockVMROMPackage`'s own objects — the same `Qc`/`Qm`, the same
environments, the same `workload`/`ioFailureUnionBound` quantities — and proves the
false-acceptance chain there:

```
OptimizedFalseAcceptanceSetK ⊆ optimizedFailureEventK
  → card ≤ productionFailureCardBoundK
  → probability ≤ (p8Work + 494N + 21 + 33M)/|𝕂| + ioWork/|𝕂|²   -- no `/|𝔽|` summand
  → at Goldilocks, `N = M = 2^31`:  < 2^-123
```

**Nothing here changes the released capstone**, which is untouched: `optimizedFailureEvent`,
`OptimizedProductionAcceptanceAt` and `optimizedFalseAcceptance_probability_le` keep their
`𝔽`-mixed tuple and their `29`-bit Goldilocks figure.  Every name below is new.

## The one residual, stated in the open

The deployed memory chip commits `firstMaskBindingGate`, `lastMaskBindingGate`,
`intermediateChainGate` and the four `selectorEquality` gates as **base-field** `CoeffExpr 𝔽`
gates read at base challenge slots `0..3`.  Rather than pretend otherwise, `OptimizedProductionAcceptanceAtK`
carries the gathered gates' vanishing as an explicit field, `memory_gathered_gates` — exactly the
commitment the retyped chip would supply and today's chip does not.  `deployed_chip_does_not_supply_memory_gathered_gates`
records that this is a real residual and not a bookkeeping step, and
`EqualityCheckLedger.migration_ledger` prices the chip change that would discharge it
(`C.rap.s 98 → 102`, `M.rap.s 104 → 112`).
-/

namespace Nock.NockVMROM.Thm54
namespace ExtensionChallengeMigration

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open MonolithicRAP
open ProductionP8Containment
open OptimizedComputeCorrectedFinal
open OptimizedComputeSemanticRealization
open OptimizedComputeCollisionBound
open OptimizedComputeSubstitution
open OptimizedMemoryRAP
open OptimizedMemoryGateBasis
open OptimizedMemoryCanonicalSatisfaction
open OptimizedMemoryCollisionAccounting
open OptimizedStrictPackage
open OptimizedStrictFullPackage
open OptimizedComputeFinalTrace
open ExtensionChallenges
open GatheredMemoryScalarGates

noncomputable section

/-! ## 1. From the `𝕂`-typed exclusions to the bundle the memory chain consumes

`RepairedMemoryCollisionGood` (`OptimizedMemoryCollisionAccounting.lean`) is a bundle of four
implications *triggered by the base-field gates*, plus the fold exclusion.
`RepairedMemoryCollisionGoodK` (`GatheredMemoryScalarGates.lean`) is the same bundle triggered by
the **gathered** gates.  Supplying the gathered triggers turns one into the other. -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **What the retyped memory chip would commit**: the four scalar gates, at an extension coin. -/
def GatheredScalarGatesVanish (b : Basis (Fin 3) F K) (envF : Env F) (envK : Env K) : Prop :=
  firstMaskBindingGateK b envK envF = 0 ∧
  lastMaskBindingGateK b envK envF = 0 ∧
  intermediateChainGateK (F := F) envK envF = 0 ∧
  ∀ s : Fin 4, selectorEqualityGateK b envK envF s = 0

/-- The `𝕂`-typed exclusion bundle plus the gathered gates gives the base-field bundle the
memory chain consumes — the four implications hold because their conclusions do. -/
theorem repairedMemoryCollisionGood_of_K
    (b : Basis (Fin 3) F K) (envF : Env F) (envK : Env K)
    (hK : RepairedMemoryCollisionGoodK b envF envK)
    (hgates : GatheredScalarGatesVanish b envF envK) :
    RepairedMemoryCollisionGood b envF envK := by
  obtain ⟨hfirst, hlast, hchain, hsel⟩ := hgates
  exact ⟨hK.1, fun _ => hK.2.1 hfirst, fun _ => hK.2.2.1 hlast,
    fun _ => hK.2.2.2.1 hchain, fun s _ => hK.2.2.2.2 s (hsel s)⟩

/-! ## 2. Coordinate projections of the `𝕂`-typed compute collision event

The analogue of `fullFinalComputeCollisionFree_components`
(`OptimizedComputeCollisionBound.lean`). -/

theorem fullFinalComputeCollisionGoodK_components
    [Fintype K] [DecidableEq K]
    {N : ℕ} (envK : Fin N → Env K) (walkEnv : Env K) (envF : Env F)
    (c : FinalComputeChallengeTupleK K)
    (hgood : c ∉ FullFinalComputeCollisionEventK envK walkEnv envF) :
    (∀ i, c.challenge9 ∉ finalComputeBadChallenges (envK i)) ∧
      c.challenge11 ∉ walkInitBadChallenges walkEnv ∧
      c.challenge36 ∉ liftedFinalSelectorBadChallenges (K := K) envF := by
  simp only [FullFinalComputeCollisionEventK, Finset.mem_union, not_or] at hgood
  rcases hgood with ⟨⟨h9, h11⟩, h36⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    apply h9
    refine Finset.mem_image.mpr ⟨(c.challenge9, (c.challenge11, c.challenge36)), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩, by simp⟩
    · cases c; rfl
  · intro hi
    exact h11 (Finset.mem_image.mpr
      ⟨(c.challenge9, (c.challenge11, c.challenge36)), by simp [hi], by cases c; rfl⟩)
  · intro hi
    exact h36 (Finset.mem_image.mpr
      ⟨(c.challenge9, (c.challenge11, c.challenge36)), by simp [hi], by cases c; rfl⟩)

/-! ## 3. The `𝕂`-typed track at the package's own objects -/

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The `𝕂`-typed production failure event at the package's own environments: the same four
summands as `optimizedFailureEvent` (`OptimizedStrictFullPackage.lean`), over
`ProductionChallengeTupleK K`. -/
def optimizedFailureEventK
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    Finset (ProductionChallengeTupleK K) :=
  ProductionFailureEventK P.strategy P.optimized.census P.objects.cfg.challenges.lam
    P.optimized.sampled.sampled.records
    (P.computeSourceEnv Qc) (P.computeWalkEnv Qc) (P.computeScalarEnv Qc)
    (P.memorySourceEnv Qm) (P.memoryScalarFamilies Qm)

theorem optimizedFailureEventK_good_components
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : ProductionChallengeTupleK K)
    (hgood : c ∉ optimizedFailureEventK P Qc Qm) :
    c.1 ∉ ProductionP8Containment.FailureUnion P.strategy P.optimized.census
        P.objects.cfg.challenges.lam ∧
      c.2.1 ∉ FiniteIO.IOFailureEvent P.optimized.sampled.sampled.records ∧
      c.2.2.1 ∉ FullFinalComputeCollisionEventK
        (P.computeSourceEnv Qc) (P.computeWalkEnv Qc) (P.computeScalarEnv Qc) ∧
      c.2.2.2 ∉ fullMemoryCollisionEventK
        (P.memorySourceEnv Qm) (P.memoryScalarFamilies Qm) := by
  simp only [optimizedFailureEventK, ProductionFailureEventK,
    Finset.mem_union, not_or] at hgood
  rcases hgood with ⟨⟨⟨hp8, hio⟩, hcompute⟩, hmemory⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact hp8 (Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩)
  · intro h
    exact hio (by simp [liftIOFailureK, h])
  · intro h
    exact hcompute (by simp [liftComputeFailureK, h])
  · intro h
    exact hmemory (by simp [liftMemoryFailureK, h])

/-- **The retyped acceptance predicate.**  Field for field the same as
`OptimizedProductionAcceptanceAt` (`OptimizedStrictFullPackage.lean`), with the five scalar pins
moved into `𝕂`:

* `compute_challenge36` pins the coin to the basis combination of the three consecutive base
  challenge slots `36, 37, 38` — `make-pelt-chal` (`five.hoon:159`), and exactly the block the
  retyped compute chip's thirteenth `𝕂` challenge would occupy
  (`final_coordinate_challenges_disjoint_scalar` puts `finalScalarChallengeBase = 3 · 12`);
* the four memory pins read the gathered `𝕂` slots `7..10`
  (`GatheredMemoryScalarGates.gathered_scalar_challenges_fresh`), which are the base blocks
  `col0 7 … col0 10`.

`memory_gathered_gates` is the one field with no counterpart in the `𝔽`-typed predicate: it is
the commitment the **retyped** memory chip would make, and the deployed chip does not make it
(§5). -/
structure OptimizedProductionAcceptanceAtK
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : ProductionChallengeTupleK K) : Prop where
  p8 : P.strategy.Accepts c.1 P.objects.cfg.challenges.lam
  same_problem : P.OptimizedSameProblemAt c.1 P.objects.cfg.challenges.lam
  sampled_io_coins :
    c.2.1 =
      (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole)
  compute_satisfies :
    RAP.SatisfiesWithPreprocessing P.computeChip Qc
  memory_satisfies :
    RAP.SatisfiesWithPreprocessing P.memoryChip Qm
  compute_challenge9 :
    ∀ i, (P.computeSourceEnv Qc i).chal compilerChallengeBase = c.2.2.1.challenge9
  compute_challenge11 :
    (P.computeWalkEnv Qc).chal (compilerChallengeBase + 2) = c.2.2.1.challenge11
  compute_challenge36 :
    ∑ k : Fin 3,
        (P.computeScalarEnv Qc).chal (finalScalarChallengeBase + (k : ℕ)) •
          P.optimized.basis k = c.2.2.1.challenge36
  memory_fold_challenge :
    ∀ i, (P.memorySourceEnv Qm i).chal 6 = c.2.2.2.extensionFold
  memory_selector_challenge :
    ∀ i, (P.memorySourceEnv Qm i).chal selectorEqualityChallengeK = c.2.2.2.selectorEquality
  memory_first_challenge :
    ∀ i, (P.memorySourceEnv Qm i).chal firstMaskBindingChallengeK = c.2.2.2.firstMask
  memory_last_challenge :
    ∀ i, (P.memorySourceEnv Qm i).chal lastMaskBindingChallengeK = c.2.2.2.lastMask
  memory_chain_challenge :
    ∀ i, (P.memorySourceEnv Qm i).chal chainBindingChallengeK = c.2.2.2.chain
  memory_gathered_gates :
    ∀ i, GatheredScalarGatesVanish P.optimized.basis
      (P.memoryBaseEnv Qm i) (P.memorySourceEnv Qm i)

/-- The retyped genuine-target predicate.  Identical to `OptimizedProductionGenuineTargetAt`
except that the two collision-good conjuncts name the `𝕂`-typed events. -/
structure OptimizedProductionGenuineTargetAtK
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : ProductionChallengeTupleK K) : Prop where
  p8 : GenuineTargetAt P.strategy P.q P.optimized.Λ c.1 P.objects.cfg.challenges.lam
  same_problem : P.OptimizedSameProblemAt c.1 P.objects.cfg.challenges.lam
  sampled_io :
    IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs
  sampled_io_event_good :
    c.2.1 ∉ FiniteIO.IOFailureEvent P.optimized.sampled.sampled.records
  compute_source :
    ∀ i,
      CorrectedComputeSourceObligations P.optimized.family.problem.cfg.compRows
        (gatherCorrectedFinalTypedEnv P.optimized.basis (P.computeBaseEnv Qc i))
        (P.computeBaseEnv Qc i)
  compute :
    ∀ (i : Fin P.optimized.family.problem.cfg.compRows),
      (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows →
      CorrectedDecodedTransitionSources
        (gatherCorrectedFinalTypedEnv P.optimized.basis (P.computeBaseEnv Qc i))
  memory :
    ∀ i,
      (∀ g ∈ baseTransitionGates P.optimized.basis,
        g.eval (P.memoryBaseEnv Qm i) = 0) ∧
      (∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
        g.eval (P.memorySourceEnv Qm i) (P.memoryBaseEnv Qm i) = 0)
  compute_collision_good :
    c.2.2.1 ∉ FullFinalComputeCollisionEventK
      (P.computeSourceEnv Qc) (P.computeWalkEnv Qc) (P.computeScalarEnv Qc)
  memory_collision_good :
    c.2.2.2 ∉ fullMemoryCollisionEventK
      (P.memorySourceEnv Qm) (P.memoryScalarFamilies Qm)
  aggregate_forest_axis : P.optimized.OptimizedSharedMemoryConnective

/-- The memory half of the retyped acceptance-to-target step.  Identical in shape to
`memory_source_gate_facts`, routed through `repairedMemoryCollisionGoodK_of_full` and
`repairedMemoryCollisionGood_of_K`. -/
theorem memory_source_gate_factsK
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : ProductionChallengeTupleK K)
    (hacc : OptimizedProductionAcceptanceAtK P Qc Qm c)
    (_hgood : c ∉ optimizedFailureEventK P Qc Qm) :
    ∀ i,
      (∀ g ∈ baseTransitionGates P.optimized.basis,
        g.eval (P.memoryBaseEnv Qm i) = 0) ∧
      (∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
        g.eval (P.memorySourceEnv Qm i) (P.memoryBaseEnv Qm i) = 0) := by
  have hsource :=
    (P.optimized.memoryRealization.arbitrary_final_iff_source Qm).1 hacc.memory_satisfies
  have hlanguage :=
    (sourceMemoryRAP_satisfies_iff_language P.optimized.sampled
      P.optimized.memoryNodes P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit (P.memorySourceTrace Qm)).1 hsource.1
  intro i
  have hi : P.optimized.memoryNodes i ∈ rowNodeSet P.optimized.memoryNodes := by
    simp [rowNodeSet]
  have hgates := hlanguage (P.optimized.memoryNodes i) hi
  exact P.optimized.memoryRealization.conditional_all_92_sources
    (P.memoryBaseEnv Qm i) hgates.1 hgates.2.2.2

/-- **The retyped acceptance-to-target step.**  The `𝕂`-typed analogue of
`acceptance_outside_failure_implies_target`. -/
theorem acceptance_outside_failure_implies_targetK
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : ProductionChallengeTupleK K)
    (hacc : OptimizedProductionAcceptanceAtK P Qc Qm c)
    (hgood : c ∉ optimizedFailureEventK P Qc Qm) :
    OptimizedProductionGenuineTargetAtK P Qc Qm c := by
  have hc := optimizedFailureEventK_good_components P Qc Qm c hgood
  have hsource :=
    ((P.optimized.computeRealization hax hbasis hwidth).arbitrary_trace_source_iff Qc).1 hacc.compute_satisfies
  refine
    { p8 := P.containment c.1 P.objects.cfg.challenges.lam hacc.p8 hc.1
      same_problem := hacc.same_problem
      sampled_io := P.shared_io
      sampled_io_event_good := hc.2.1
      compute_source := fun i => hsource.2 (P.optimized.computeNodes i)
        (by simp [rowNodeSet])
      compute := ?_
      memory := memory_source_gate_factsK P Qc Qm c hacc hgood
      compute_collision_good := hc.2.2.1
      memory_collision_good := hc.2.2.2
      aggregate_forest_axis := P.optimized.shared_memory_connective }
  intro i hi
  have hnotLast :
      (gatherCorrectedFinalTypedEnv P.optimized.basis
        (P.computeBaseEnv Qc i)).baseTrace 12 = 0 := by
    have hbind := hacc.compute_satisfies.2 (1 : Fin 2)
    have hresources := P.optimized.exact_chip_resources
    dsimp only at hresources
    have hw : P.computeChip.rap.w = 303 := by
      exact hresources.1
    have hj12 : 12 < P.computeChip.rap.w := by omega
    change Qc ⟨12, hj12⟩ =
      Nock.Framework.lastRowMask P.optimized.family.problem.cfg.compRows_pos
        P.optimized.computeNodes at hbind
    have heval := congrArg
      (fun f : F[X] => f.eval (P.optimized.computeNodes i)) hbind
    rw [Nock.Framework.lastRowMask_eval
      P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
      P.optimized.computeNodes_injective] at heval
    have hne : i ≠
        ⟨P.optimized.family.problem.cfg.compRows - 1,
          Nat.sub_lt P.optimized.family.problem.cfg.compRows_pos (by omega)⟩ := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only at hv
      omega
    simp only [hne, if_false] at heval
    change (Qc ⟨12, hj12⟩).eval (P.optimized.computeNodes i) = 0
    exact heval
  exact (P.optimized.computeRealization hax hbasis hwidth).conditional_row_decode Qc hacc.compute_satisfies
    (P.optimized.computeNodes i)
    (by simp [rowNodeSet]) hnotLast

/-- The retyped false-acceptance set. -/
def OptimizedFalseAcceptanceSetK
    [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    Finset (ProductionChallengeTupleK K) :=
  Finset.univ.filter fun c =>
    OptimizedProductionAcceptanceAtK P Qc Qm c ∧
      ¬ OptimizedProductionGenuineTargetAtK P Qc Qm c

theorem optimizedFalseAcceptanceSetK_subset_failure
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    OptimizedFalseAcceptanceSetK P Qc Qm ⊆ optimizedFailureEventK P Qc Qm := by
  intro c hc
  simp only [OptimizedFalseAcceptanceSetK, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  by_contra hgood
  exact hc.2 (acceptance_outside_failure_implies_targetK P hax hbasis hwidth Qc Qm c hc.1 hgood)

/-! ## 4. The bound the package now carries, with **no base-field denominator**

`productionFailureProbabilityBoundK` is `(p8Work + 494·N + 21 + 33·M)/|𝕂| + ioWork/|𝕂|²`.  The
`21` and the `33·M` are **not** the `1` and `19·M` of the released bound with the `/|𝔽|` summand
deleted: the `20` from `challenge36` joins the `1`, and the `14·M` from the four memory scalars
joins the `19·M` (`19 + 8 + 2 + 2 + 2 = 33`).  Moving a coordinate from `𝔽` to `𝕂` moves its
numerator into the `𝕂` bucket; it does not delete it. -/

theorem falseAcceptanceK_card_le
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (OptimizedFalseAcceptanceSetK P Qc Qm).card ≤
      productionFailureCardBoundK (Fintype.card K)
        (workload P.strategy P.optimized.Λ
          (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy))
        (FiniteIO.ioFailureUnionBound 9
          P.optimized.sampled.sampled.records.requests.length
          P.optimized.sampled.sampled.records.responses.length (Fintype.card K))
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows :=
  (Finset.card_le_card (optimizedFalseAcceptanceSetK_subset_failure P hax hbasis hwidth Qc Qm)).trans
    (productionFailureEventK_card_le P.two_ne_zero P.strategy P.optimized.census
      P.objects.cfg.challenges.lam
      (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy)
      P.optimized.sizeWindowBound
      (topologyWorkload_le_fixedTopologyWorkload P.strategy)
      (templateAxisWorkload_le_fixedAxisWorkload P.strategy)
      P.optimized.sampled.sampled.records
      (P.computeSourceEnv Qc) (P.computeWalkEnv Qc) (P.computeScalarEnv Qc)
      (P.memorySourceEnv Qm) (P.memoryScalarFamilies Qm))

/-- **The retyped false-acceptance probability**, over `|𝕂|¹⁴` points.  Compare
`optimizedFalseAcceptance_probability_le` (`OptimizedStrictFullPackage.lean`), whose right-hand
side still carries `(20 + 14·M)/|𝔽|`. -/
theorem falseAcceptanceK_probability_le
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    ((OptimizedFalseAcceptanceSetK P Qc Qm).card : ℚ) /
        Fintype.card (ProductionChallengeTupleK K) ≤
      productionFailureProbabilityBoundK (Fintype.card K)
        (workload P.strategy P.optimized.Λ
          (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy))
        (FiniteIO.ioFailureUnionBound 9
          P.optimized.sampled.sampled.records.requests.length
          P.optimized.sampled.sampled.records.responses.length (Fintype.card K))
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows := by
  refine le_trans ?_ (productionFailureProbabilityK_le P.two_ne_zero P.strategy
    P.optimized.census P.objects.cfg.challenges.lam
    (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy)
    P.optimized.sizeWindowBound
    (topologyWorkload_le_fixedTopologyWorkload P.strategy)
    (templateAxisWorkload_le_fixedAxisWorkload P.strategy)
    P.optimized.sampled.sampled.records
    (P.computeSourceEnv Qc) (P.computeWalkEnv Qc) (P.computeScalarEnv Qc)
    (P.memorySourceEnv Qm) (P.memoryScalarFamilies Qm))
  have hcast :
      ((OptimizedFalseAcceptanceSetK P Qc Qm).card : ℚ) ≤
        ((optimizedFailureEventK P Qc Qm).card : ℚ) := by
    exact_mod_cast Finset.card_le_card (optimizedFalseAcceptanceSetK_subset_failure P hax hbasis hwidth Qc Qm)
  exact div_le_div_of_nonneg_right hcast (by positivity)

/-- The bit form, with the support premise carried exactly as
`optimizedFalseAcceptance_probability_le_two_pow_neg` carries its own. -/
theorem falseAcceptanceK_probability_le_two_pow_neg
    [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (b : ℕ)
    (hsupport :
      productionFailureProbabilityBoundK (Fintype.card K)
          (workload P.strategy P.optimized.Λ
            (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy))
          (FiniteIO.ioFailureUnionBound 9
            P.optimized.sampled.sampled.records.requests.length
            P.optimized.sampled.sampled.records.responses.length (Fintype.card K))
          P.optimized.family.problem.cfg.compRows
          P.optimized.family.problem.cfg.memRows * 2 ^ b ≤ 1) :
    ((OptimizedFalseAcceptanceSetK P Qc Qm).card : ℚ) /
        Fintype.card (ProductionChallengeTupleK K) ≤ 1 / 2 ^ b := by
  refine (falseAcceptanceK_probability_le P hax hbasis hwidth Qc Qm).trans ?_
  have hpow : (0 : ℚ) < 2 ^ b := by positivity
  apply (le_div_iff₀ hpow).2
  simpa [mul_comm] using hsupport

end

/-! ## 5. Goldilocks: `123` bits for the retyped false-acceptance set

Stage 2 of the migration.  The figure is **not** inferred from the disappearance of the
base-field summand: `soundnessK_at_paper_configuration` evaluates the `21`/`33·M` numerators over
`|𝕂| = p³` at `N = M = 2^31`, and this theorem applies that to the package's own
false-acceptance set.  The released capstone's own figure at the same configuration is `29` bits
(`GoldilocksParameters.merged_soundness_at_paper_configuration`) and is untouched. -/

section Goldilocks

open Nock.Field

local instance extensionChallengeMigrationRingCharP :
    CharP Nock.Field.K (ringChar Nock.Field.K) := ringChar.charP _

variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage Nock.Field.Fp Nock.Field.K hOrb)

open GoldilocksParameters in
/-- **The retyped bound is NOT the consumed bound with its base-field summand deleted.**
Retyping moves a coordinate's numerator into the `𝕂` bucket; it does not delete it.  The `20`
joins the `1` and the `14·M` joins the `19·M` (`21`, `33·M`), so the naive "drop `(20+14M)/|𝔽|`"
reading strictly **undershoots** the real `𝕂` bound whenever there is a memory row.  Quoting
`123` off the deletion would be quoting the wrong function;
`ExtensionChallenges.soundnessK_at_paper_configuration` evaluates the real one. -/
theorem naive_deletion_undershoots (p8Work ioWork N M : ℕ) (hM : 0 < M) :
    (p8Work + 494 * N + 1 + 19 * M : ℚ) / (cardKGold : ℚ)
        + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
      < goldilocksFailureBoundK p8Work ioWork N M := by
  rw [goldilocksFailureBoundK_eq]
  have hM' : (1 : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
  have hd : (0 : ℚ) < (cardKGold : ℚ) := by norm_num
  have hlt : (p8Work + 494 * N + 1 + 19 * M : ℚ) < (p8Work + 494 * N + 21 + 33 * M : ℚ) := by
    linarith
  have hdiv : (p8Work + 494 * N + 1 + 19 * M : ℚ) / (cardKGold : ℚ)
      < (p8Work + 494 * N + 21 + 33 * M : ℚ) / (cardKGold : ℚ) := by
    gcongr
  linarith

open GoldilocksParameters in
/-- **The `123` is not slack.**  At the paper's configuration with both ceilings saturated the
`𝕂`-typed bound is strictly above `2^-124`: the `ioWork/|𝕂|²` term alone is `2^260/2^384`.  So
`soundnessK_at_paper_configuration`'s `123` is one bit off the true value of the majorant, not an
arbitrary round number. -/
theorem soundnessK_at_paper_configuration_is_one_bit_from_sharp :
    1 / (2 : ℚ) ^ 124 < goldilocksFailureBoundK (2 ^ 60) (16 ^ 65) (2 ^ 31) (2 ^ 31) := by
  rw [goldilocksFailureBoundK_eq]
  norm_num

/-- **`< 2^-123` for the retyped false-acceptance set at the paper's headline configuration**. -/
theorem falseAcceptanceK_soundness_at_paper_configuration
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth Nock.Field.Fp)
    (Qc : Fin P.computeChip.rap.w → Nock.Field.Fp[X])
    (Qm : Fin P.memoryChip.rap.w → Nock.Field.Fp[X])
    (hN : P.optimized.family.problem.cfg.compRows = 2 ^ 31)
    (hM : P.optimized.family.problem.cfg.memRows = 2 ^ 31)
    (hp8 : workload P.strategy P.optimized.Λ
      (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy) ≤ 2 ^ 60)
    (hio : FiniteIO.ioFailureUnionBound 9
      P.optimized.sampled.sampled.records.requests.length
      P.optimized.sampled.sampled.records.responses.length
      (Fintype.card Nock.Field.K) ≤ 16 ^ 65) :
    ((OptimizedFalseAcceptanceSetK P Qc Qm).card : ℚ) /
        Fintype.card (ProductionChallengeTupleK Nock.Field.K) < 1 / (2 : ℚ) ^ 123 := by
  refine lt_of_le_of_lt (falseAcceptanceK_probability_le P hax hbasis hwidth Qc Qm) ?_
  rw [hN, hM]
  simpa [goldilocksFailureBoundK] using
    (soundnessK_at_paper_configuration
      (workload P.strategy P.optimized.Λ
        (fixedTopologyWorkload P.strategy) (fixedAxisWorkload P.strategy))
      (FiniteIO.ioFailureUnionBound 9
        P.optimized.sampled.sampled.records.requests.length
        P.optimized.sampled.sampled.records.responses.length
        (Fintype.card Nock.Field.K)) hp8 hio).2

end Goldilocks

/-! ## 6. What is NOT done, compiled

The migration is **not** landed.  `memory_gathered_gates` is a hypothesis of
`OptimizedProductionAcceptanceAtK`, not a consequence of `memory_satisfies`, and the two theorems
below say why in Lean rather than in prose. -/

section Residual

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
/-- The compute chip's retyped scalar coin, read as `make-pelt-chal` (`five.hoon:159`): the pin
`OptimizedProductionAcceptanceAtK.compute_challenge36` carries is exactly the gathered read of
the `𝕂` challenge whose coordinate block starts at `finalScalarChallengeBase = 3 · 12`
(`final_coordinate_challenges_disjoint_scalar`), i.e. the thirteenth `𝕂` challenge of a compute
chip that has twelve today. -/
theorem compute_scalar_coin_is_three_base_slots
    (b : Basis (Fin 3) F K) (col0 : VarKind → ℕ → ℕ) (envF : Env F) (j : ℕ)
    (hj : col0 .challenge j = finalScalarChallengeBase) :
    (gatherEnv b col0 envF).chal j =
      ∑ k : Fin 3, envF.chal (finalScalarChallengeBase + (k : ℕ)) • b k := by
  rw [gathered_coin_is_three_base_slots b col0 envF j, hj]

/-- **The residual is real.**  Base-gate satisfaction — which is all the deployed memory chip
delivers — does not give `GatheredScalarGatesVanish`: for a trace whose mask binding is broken
there is an extension coin at which the gathered gate is nonzero while the committed base gate
still vanishes.  This is `base_gate_is_strictly_weaker_than_gathered_gate` transported to the
package-level residual, and it is why `memory_gathered_gates` is a field rather than a lemma.
Discharging it means committing the gathered gates, priced by
`EqualityCheckLedger.migration_ledger` at `C.rap.s 98 → 102` and `M.rap.s 104 → 112`. -/
theorem deployed_chip_does_not_supply_memory_gathered_gates
    (b : Basis (Fin 3) F K) (envF : Env F)
    (hbroken : ∃ k : Fin 3, (maskBindingCoord b 47 4 k).eval envF ≠ 0)
    (hbase : (firstMaskBindingGate b).eval envF = 0)
    (hK : 2 < Fintype.card K) :
    ∃ envK : Env K,
      (firstMaskBindingGate b).eval envF = 0 ∧
        ¬ GatheredScalarGatesVanish b envF envK := by
  obtain ⟨ρ, -, hρ⟩ :=
    base_gate_is_strictly_weaker_than_gathered_gate b envF hbroken hbase hK
  let envK : Env K :=
    { trace := fun _ => 0
      traceNext := fun _ => 0
      chal := fun _ => ρ
      pub := fun _ => 0 }
  refine ⟨envK, hbase, ?_⟩
  rintro ⟨hfirst, -, -, -⟩
  exact hρ hfirst

end Residual

end ExtensionChallengeMigration
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.ExtensionChallengeMigration.repairedMemoryCollisionGood_of_K
#print axioms Nock.NockVMROM.Thm54.ExtensionChallengeMigration.fullFinalComputeCollisionGoodK_components
#print axioms Nock.NockVMROM.Thm54.ExtensionChallengeMigration.optimizedFailureEventK_good_components
#print axioms Nock.NockVMROM.Thm54.ExtensionChallengeMigration.memory_source_gate_factsK
#print axioms Nock.NockVMROM.Thm54.ExtensionChallengeMigration.acceptance_outside_failure_implies_targetK
#print axioms Nock.NockVMROM.Thm54.ExtensionChallengeMigration.optimizedFalseAcceptanceSetK_subset_failure
#print axioms Nock.NockVMROM.Thm54.ExtensionChallengeMigration.falseAcceptanceK_card_le
#print axioms Nock.NockVMROM.Thm54.ExtensionChallengeMigration.falseAcceptanceK_probability_le
#print axioms Nock.NockVMROM.Thm54.ExtensionChallengeMigration.falseAcceptanceK_probability_le_two_pow_neg
#print axioms Nock.NockVMROM.Thm54.ExtensionChallengeMigration.naive_deletion_undershoots
#print axioms Nock.NockVMROM.Thm54.ExtensionChallengeMigration.soundnessK_at_paper_configuration_is_one_bit_from_sharp
#print axioms Nock.NockVMROM.Thm54.ExtensionChallengeMigration.falseAcceptanceK_soundness_at_paper_configuration
#print axioms Nock.NockVMROM.Thm54.ExtensionChallengeMigration.compute_scalar_coin_is_three_base_slots
#print axioms Nock.NockVMROM.Thm54.ExtensionChallengeMigration.deployed_chip_does_not_supply_memory_gathered_gates
