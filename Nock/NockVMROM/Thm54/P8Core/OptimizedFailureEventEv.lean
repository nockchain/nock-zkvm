/-
  Nock/NockVMROM/Thm54/P8Core/OptimizedFailureEventEv.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.OptimizedFailureEventEv`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/OptimizedFailureEventEv.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackageDefs
import Nock.NockVMROM.Thm54.P8EventEv

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.OptimizedFailureEventEv

open scoped Polynomial BigOperators Classical
open Polynomial
open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.P8EventEv
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

noncomputable section

section AlphaZero

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The `α = 0` event: the memory walk / timestamp coin is zero. -/
def alphaZeroEvent : Finset (JointCoins K) :=
  Finset.univ.filter fun ω => alphaM ω = 0

@[simp] theorem mem_alphaZeroEvent_iff (ω : JointCoins K) :
    ω ∈ alphaZeroEvent ↔ alphaM ω = 0 := by
  simp [alphaZeroEvent]

theorem alphaZeroEvent_eq :
    (alphaZeroEvent : Finset (JointCoins K)) =
      (Finset.univ : Finset (K × K)) ×ˢ (({0} : Finset K) ×ˢ (Finset.univ : Finset K)) := by
  ext ω
  rcases ω with ⟨cg, ⟨α, z⟩⟩
  simp [alphaZeroEvent, Thm54.alphaM, eq_comm]
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))

theorem alphaZeroEvent_card : (alphaZeroEvent : Finset (JointCoins K)).card = Fintype.card K ^ 3 := by
  rw [alphaZeroEvent_eq]
  simp only [Finset.card_product, Finset.card_univ, Finset.card_singleton, Fintype.card_prod]
  ring

theorem alphaZeroEvent_card_le :
    (alphaZeroEvent : Finset (JointCoins K)).card ≤ 1 * Fintype.card K ^ 3 := by
  rw [alphaZeroEvent_card, one_mul]

end AlphaZero

section AtP

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])

/-- The traces' compute row count. -/
abbrev N : ℕ := P.optimized.family.problem.cfg.compRows

/-- The traces' memory row count. -/
abbrev M : ℕ := P.optimized.family.problem.cfg.memRows

/-- The pair window `Λg = M ⊔ Λ` (the 33rd's). -/
abbrev Λg : ℕ := P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ

/-- **The event-side built strategy at `P`**: coin-free, `h`-free, at `P.stateTagChar`. -/
def builtStrategyEv : ProductionStrategy F K :=
  strategyOfTracesEv P.optimized Qc Qm P.stateTagChar

/-- **The event skeleton at `P`.** -/
def builtSkeletonEv : SemanticSkeleton := skeletonEv P.optimized Qc Qm

/-- **The built request targets** (`builtRequestTargets`): `requestTargets` of the event
skeleton — the C2 rows' structural records at round 0 (`c2SkeletonRow.memoryRecord`). -/
def builtRequestTargets : MemoryTable.MState → ℕ → Noun :=
  PreSeedCensus.requestTargets (builtSkeletonEv P Qc Qm)

/-- **The P8 slot, fibred over `λ`**: the tuples whose `JointCoins` lie in the event union at the
built strategy at the tuple's own `λ`.  Coin-free strategy: for each `λ` the fibre is a cylinder
over one `JointCoins` set. -/
def p8SlotEv : Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter fun c =>
    c.1 ∈ evFailureUnion (builtStrategyEv P Qc Qm) P.optimized.Λ c.2.2.2.lambda

@[simp] theorem mem_p8SlotEv_iff (c : OptimizedProductionChallengeTuple K F) :
    c ∈ p8SlotEv P Qc Qm ↔
      c.1 ∈ evFailureUnion (builtStrategyEv P Qc Qm) P.optimized.Λ c.2.2.2.lambda := by
  simp [p8SlotEv]

/-- The `λ`-fibre of the slot embeds into `U(λ) × (K × K) × FinalComputeChallengeTuple × K`. -/
theorem p8SlotEv_card_le :
    (p8SlotEv P Qc Qm).card ≤
      Fintype.card K ^ 10 * p8WorkEv (N P) (M P) P.optimized.Λ := by
  -- cover by the `λ`-fibres
  have hcover : p8SlotEv P Qc Qm ⊆
      (Finset.univ : Finset K).biUnion fun lam =>
        (evFailureUnion (builtStrategyEv P Qc Qm) P.optimized.Λ lam) ×ˢ
          (Finset.univ.filter fun r : (K × K) ×
              (FinalComputeChallengeTuple K × MemoryChallengeTuple K) => r.2.2.lambda = lam) := by
    intro c hc
    rw [mem_p8SlotEv_iff] at hc
    refine Finset.mem_biUnion.mpr ⟨c.2.2.2.lambda, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_product]
    exact ⟨hc, by simp⟩
  -- each `λ`-fibre of the rest has `≤ |𝕂|⁶` elements
  have hfibre : ∀ lam : K,
      (Finset.univ.filter fun r : (K × K) ×
          (FinalComputeChallengeTuple K × MemoryChallengeTuple K) => r.2.2.lambda = lam).card ≤
        Fintype.card K ^ 6 := by
    intro lam
    let π : (K × K) × (FinalComputeChallengeTuple K × MemoryChallengeTuple K) →
        (K × K) × (FinalComputeChallengeTuple K × K) :=
      fun r => (r.1, (r.2.1, r.2.2.interPole))
    have hinj : Set.InjOn π ((Finset.univ.filter fun r : (K × K) ×
        (FinalComputeChallengeTuple K × MemoryChallengeTuple K) => r.2.2.lambda = lam) :
          Set ((K × K) × (FinalComputeChallengeTuple K × MemoryChallengeTuple K))) := by
      rintro ⟨a, ⟨b, ⟨ip, l⟩⟩⟩ ha ⟨a', ⟨b', ⟨ip', l'⟩⟩⟩ ha' h
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ha'
      simp only [π, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      subst ha; subst ha'
      rfl
    calc _ ≤ (Finset.univ : Finset ((K × K) × (FinalComputeChallengeTuple K × K))).card :=
          Finset.card_le_card_of_injOn π (fun _ _ => Finset.mem_univ _) hinj
      _ = Fintype.card K ^ 6 := by
          simp only [Finset.card_univ, Fintype.card_prod, card_finalComputeChallengeTuple]
          ring
  have h2 : (2 : K) ≠ 0 := P.two_ne_zero
  calc (p8SlotEv P Qc Qm).card
      ≤ ((Finset.univ : Finset K).biUnion fun lam =>
          (evFailureUnion (builtStrategyEv P Qc Qm) P.optimized.Λ lam) ×ˢ
            (Finset.univ.filter fun r : (K × K) ×
              (FinalComputeChallengeTuple K × MemoryChallengeTuple K) =>
                r.2.2.lambda = lam)).card := Finset.card_le_card hcover
    _ ≤ ∑ lam : K, ((evFailureUnion (builtStrategyEv P Qc Qm) P.optimized.Λ lam) ×ˢ
          (Finset.univ.filter fun r : (K × K) ×
            (FinalComputeChallengeTuple K × MemoryChallengeTuple K) =>
              r.2.2.lambda = lam)).card := Finset.card_biUnion_le
    _ ≤ ∑ _lam : K, (p8WorkEv (N P) (M P) P.optimized.Λ * Fintype.card K ^ 3) *
          Fintype.card K ^ 6 := by
        apply Finset.sum_le_sum
        intro lam _
        rw [Finset.card_product]
        exact Nat.mul_le_mul (evFailureUnion_Ev_card_le P.optimized Qc Qm P.stateTagChar h2
          P.optimized.Λ lam) (hfibre lam)
    _ = Fintype.card K ^ 10 * p8WorkEv (N P) (M P) P.optimized.Λ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

/-- **The 33rd's pair event at the built targets** (`reqPairEventOf` re-pointed). -/
def reqPairEv : Finset (JointCoins K) :=
  PreSeedCensus.reqPairEventOfEnvs K P.q P.optimized.family.problem.cfg.kMem (Λg P)
    (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.memRows_pos
    (builtRequestTargets P Qc Qm)

theorem reqPairEv_card_le :
    (reqPairEv P Qc Qm).card ≤ M P * (2 * Λg P - 1) * Fintype.card K ^ 3 :=
  PreSeedCensus.reqPairEventOfEnvs_card_le K P.q _ _ _ _ _

set_option maxRecDepth 16384 in
/-- The pinned memory base env and the family base env at any tuple have the same trace (the
chal / pub fields differ, which the pre-`z` decoder never reads). -/
theorem memoryBaseEnv_trace (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (P.memoryBaseEnv Qm i).trace = (memoryEnvsR0 P.optimized Qm c i).trace := rfl

/-- **The root-result 1-pair event**: the built root evaluation against the package claim's result,
at the window `Λg`. -/
def rootResultEv : Finset (JointCoins K) :=
  liftSeed (PreSeedCensus.pairBadSeeds (K := K) (Λg P)
    [((builtSkeletonEv P Qc Qm).publicClaim.result, P.optimized.verifier.raw.claim.result)])

theorem rootResultEv_card_le :
    (rootResultEv P Qc Qm).card ≤ (2 * Λg P - 1) * Fintype.card K ^ 3 := by
  rw [rootResultEv, card_liftSeed]
  refine Nat.mul_le_mul_right _ ?_
  have := PreSeedCensus.pairBadSeeds_card_le (K := K) (Λg P)
    [((builtSkeletonEv P Qc Qm).publicClaim.result, P.optimized.verifier.raw.claim.result)]
  simpa using this

/-- **The assembled failure event as 2b-ii would pin it**: the P8 slot at the built strategy
(fibred over `λ`), every unchanged summand of `optimizedFailureEvent`, the 33rd's pair event at the
built targets, the root-result event and the `α = 0` event.  No S3 summand. -/
def optimizedFailureEventEv : Finset (OptimizedProductionChallengeTuple K F) :=
  p8SlotEv P Qc Qm ∪
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
    liftP8Failure (reqPairEv P Qc Qm) ∪
    liftP8Failure (rootResultEv P Qc Qm) ∪
    liftP8Failure (alphaZeroEvent : Finset (JointCoins K))

/-- **The P8 numerator of the assembled event** (the `p8Work` argument of the consumed bound
function): the built P8 slot `p8WorkEv N M Λ`, the λ-event's `formRUniformWorkload`, the pair term
`M·(2Λg − 1)`, the root-result term `2Λg − 1` and the `α = 0` term `1`. -/
def workloadEv (Λ : ℕ) : ℕ :=
  p8WorkEv (N P) (M P) Λ + formRUniformWorkload P.strategy +
    M P * (2 * (M P ⊔ Λ) - 1) + (2 * (M P ⊔ Λ) - 1) + 1

/-- Lift a `JointCoins` bound through the P8 cylinder. -/
theorem liftP8_card_le (B : Finset (JointCoins K)) (b : ℕ) (hB : B.card ≤ b * Fintype.card K ^ 3) :
    (liftP8Failure (F := F) B).card ≤ Fintype.card K ^ 10 * b := by
  have hrest :
      Fintype.card ((K × K) × FinalComputeChallengeTuple K × MemoryChallengeTuple K) =
        Fintype.card K ^ 7 := by
    simp [Fintype.card_prod, card_finalComputeChallengeTuple, card_memoryChallengeTuple]
    ring
  rw [liftP8Failure, Finset.card_product, Finset.card_univ, hrest]
  calc B.card * Fintype.card K ^ 7 ≤ b * Fintype.card K ^ 3 * Fintype.card K ^ 7 :=
        Nat.mul_le_mul_right _ hB
    _ = Fintype.card K ^ 10 * b := by ring

/-- **THE TOTAL CARD BOUND, every `(Qc, Qm)`, no premise**: the assembled event's card is below
the consumed bound function at `p8Work := workloadEv P Λ` (`Λ := P.optimized.Λ`), `ioWork :=
P.hostileIOWork`, the traces' row counts. -/
theorem optimizedFailureEventEv_card_le :
    (optimizedFailureEventEv P Qc Qm).card ≤
      optimizedHostileProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (workloadEv P P.optimized.Λ) P.hostileIOWork (N P) (M P) := by
  -- the summands
  have hp8 := p8SlotEv_card_le P Qc Qm
  have hio := P.famIOEventOf_card_le Qc Qm
  have hts : (liftTimestampFailure (F := F)
      (OptimizedHostileTimestamps.TimestampCollisionEvent (K := K)
        (P.hostileRequests Qc).length)).card ≤
      Fintype.card K ^ 10 *
        OptimizedHostileTimestamps.timestampCollisionBound (3 * N P) := by
    rw [card_liftTimestampFailure, mul_comm]
    exact Nat.mul_le_mul_left _
      ((OptimizedHostileTimestamps.TimestampCollisionEvent_card_le_bound _).trans
        (OptimizedHostileTimestamps.timestampCollisionBound_mono
          (P.hostileRequests_length_le Qc)))
  have hinter : (liftInterPoleFailure (F := F)
      (interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm)
        (P.memoryBaseEnv Qm))).card ≤
      Fintype.card K ^ 9 * (FiniteIO.ioFailureUnionBound 10 (M P) (M P) (Fintype.card K) +
        Fintype.card K * M P) := by
    refine (card_liftInterPoleFailure (F := F) _).trans ?_
    rw [mul_comm]
    refine Nat.mul_le_mul_left _ ?_
    refine (Finset.card_union_le _ _).trans ?_
    refine Nat.add_le_add ?_ ?_
    · exact (FiniteIO.IOFailureEvent_card_le (P.hostileInterRecords Qm)).trans
        (ioFailureUnionBound_mono₂ 10 (P.hostileInterRecords Qm).requests.length
          (P.hostileInterRecords Qm).responses.length (M P) (M P) (Fintype.card K)
          (P.hostileInterReads_length_le Qm) (P.hostileInterVerifies_length_le Qm))
    · have hcov : allRowPoleHitEvent (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) ⊆
          (Finset.univ : Finset K).biUnion (fun γ =>
            ({γ} : Finset K) ×ˢ
              FiniteIO.IOPoleHitEvent
                ⟨List.ofFn (fun i =>
                  OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv Qm i)
                    (P.memoryBaseEnv Qm i)), []⟩ γ) := by
        intro q hq
        simp only [allRowPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        refine Finset.mem_biUnion.mpr ⟨q.1, Finset.mem_univ _, ?_⟩
        exact Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, hq⟩
      refine (Finset.card_le_card hcov).trans ?_
      refine (Finset.card_biUnion_le (s := (Finset.univ : Finset K))
        (t := fun γ => ({γ} : Finset K) ×ˢ
          FiniteIO.IOPoleHitEvent
            ⟨List.ofFn (fun i =>
              OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv Qm i)
                (P.memoryBaseEnv Qm i)), []⟩ γ)).trans ?_
      have hsum : ∀ γ ∈ (Finset.univ : Finset K),
          (({γ} : Finset K) ×ˢ
            FiniteIO.IOPoleHitEvent
              ⟨List.ofFn (fun i =>
                OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv Qm i)
                  (P.memoryBaseEnv Qm i)), []⟩ γ).card ≤ M P := by
        intro γ _
        rw [Finset.card_product, Finset.card_singleton, one_mul]
        exact (FiniteIO.IOPoleHitEvent_card_le _ γ).trans (by simp [List.length_ofFn])
      refine (Finset.sum_le_sum hsum).trans ?_
      simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hwalk := liftP8_card_le (F := F) _ _ (P.computeWalkRootEvent_card_le Qc)
  have htileC := liftP8_card_le (F := F) _ _ (P.computeTilingEventOf_card_le Qc)
  have htileM := liftP8_card_le (F := F) _ _ (P.memoryTilingEventOf_card_le Qm)
  have hγC := liftP8_card_le (F := F) _ _ (P.computePrefixGammaEventOf_card_le Qc)
  have hγM := liftP8_card_le (F := F) _ _ (P.memoryPrefixGammaEventOf_card_le Qm)
  have hαM := liftP8_card_le (F := F) _ _ (P.memoryForestAlphaEventOf_card_le Qm)
  have hlam := P.decodedLambdaEventOf_card_le Qc Qm
  have hpair := liftP8_card_le (F := F) _ _ (reqPairEv_card_le P Qc Qm)
  have hroot := liftP8_card_le (F := F) _ _ (rootResultEv_card_le P Qc Qm)
  have hα0 := liftP8_card_le (F := F) _ _ (alphaZeroEvent_card_le (K := K))
  -- the bound function, split
  have hsplit :
      optimizedHostileProductionFailureCardBound (Fintype.card K) (Fintype.card F)
        (workloadEv P P.optimized.Λ) P.hostileIOWork (N P) (M P) =
      Fintype.card K ^ 10 * p8WorkEv (N P) (M P) P.optimized.Λ +
        Fintype.card K ^ 9 * P.hostileIOWork +
        Fintype.card K ^ 10 *
          OptimizedHostileTimestamps.timestampCollisionBound (3 * N P) +
        Fintype.card K ^ 9 * (FiniteIO.ioFailureUnionBound 10 (M P) (M P) (Fintype.card K) +
          Fintype.card K * M P) +
        Fintype.card K ^ 10 * ComputeWalkRootEvents.walkRootBound (N P) +
        Fintype.card K ^ 10 * WalkTilingEvents.computeTilingBound (N P) +
        Fintype.card K ^ 10 * WalkTilingEvents.memoryTilingBound (M P) +
        Fintype.card K ^ 10 * WalkPrefixGammaEvents.computePrefixGammaBound (N P) +
        Fintype.card K ^ 10 * WalkPrefixGammaEvents.memoryPrefixGammaBound (M P) +
        Fintype.card K ^ 10 * WalkForestPrefixAlphaEvents.memoryForestAlphaBound (M P) +
        Fintype.card K ^ 10 * formRUniformWorkload P.strategy +
        Fintype.card K ^ 10 * (M P * (2 * Λg P - 1)) +
        Fintype.card K ^ 10 * (2 * Λg P - 1) +
        Fintype.card K ^ 10 * 1 := by
    simp only [optimizedHostileProductionFailureCardBound,
      optimizedTrimmedProductionFailureCardBound, pricedWalkWork, workloadEv]
    ring
  rw [hsplit]
  have hio' : (P.famIOEventOf Qc Qm).card ≤ Fintype.card K ^ 9 * P.hostileIOWork := hio
  unfold optimizedFailureEventEv
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ hα0
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ hroot
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ hpair
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ hlam
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ hαM
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ hγM
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ hγC
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ htileM
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ htileC
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ hwalk
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ hinter
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ hts
  refine (Finset.card_union_le _ _).trans ?_
  exact Nat.add_le_add hp8 hio'

/-- **Membership, component by component** (the shape `acceptance_to_target` consumes). -/
theorem optimizedFailureEventEv_good_components (c : OptimizedProductionChallengeTuple K F)
    (hgood : c ∉ optimizedFailureEventEv P Qc Qm) :
    c.1 ∉ evFailureUnion (builtStrategyEv P Qc Qm) P.optimized.Λ c.2.2.2.lambda ∧
      c ∉ P.famIOEventOf Qc Qm ∧
      alphaM c.1 ∉
        OptimizedHostileTimestamps.TimestampCollisionEvent (P.hostileRequests Qc).length ∧
      (c.2.1.1, c.2.2.2.interPole) ∉
        interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) ∧
      c.1 ∉ P.computeWalkRootEvent Qc ∧
      c.1 ∉ P.computeTilingEventOf Qc ∧
      c.1 ∉ P.memoryTilingEventOf Qm ∧
      c.1 ∉ P.computePrefixGammaEventOf Qc ∧
      c.1 ∉ P.memoryPrefixGammaEventOf Qm ∧
      c.1 ∉ P.memoryForestAlphaEventOf Qm ∧
      c ∉ P.decodedLambdaEventOf Qc Qm ∧
      c.1 ∉ reqPairEv P Qc Qm ∧
      c.1 ∉ rootResultEv P Qc Qm ∧
      alphaM c.1 ≠ 0 := by
  simp only [optimizedFailureEventEv, Finset.mem_union, not_or] at hgood
  rcases hgood with
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hp8, hio⟩, hts⟩, hinter⟩, hwalk⟩, htileC⟩, htileM⟩, hγC⟩, hγM⟩, hαM⟩, hlamEv⟩,
      hpair⟩, hroot⟩, hα0⟩
  refine ⟨?_, hio, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlamEv, ?_, ?_, ?_⟩
  · intro h; exact hp8 ((mem_p8SlotEv_iff P Qc Qm c).2 h)
  · intro h; exact hts ((mem_liftTimestampFailure_iff _ _).2 h)
  · intro h; exact hinter ((mem_liftInterPoleFailure_iff _ _).2 h)
  · intro h; exact hwalk (Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩)
  · intro h; exact htileC (Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩)
  · intro h; exact htileM (Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩)
  · intro h; exact hγC (Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩)
  · intro h; exact hγM (Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩)
  · intro h; exact hαM (Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩)
  · intro h; exact hpair (Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩)
  · intro h; exact hroot (Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩)
  · intro h
    exact hα0 (Finset.mem_product.mpr ⟨(mem_alphaZeroEvent_iff _).2 h, Finset.mem_univ _⟩)

/-- Outside the event, the P8 union at the C2 strategy of the SAME tuple excludes the coin
(the agreement lemma, applied where the containment proof runs). -/
theorem not_mem_evFailureUnion_C2 (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P.optimized Qc Qm c) (hgood : c ∉ optimizedFailureEventEv P Qc Qm) :
    c.1 ∉ evFailureUnion (StrategyOfTracesR0AC2.strategyOfTracesR0AC2 P.optimized P.stateTagChar
      Qc Qm c h) P.optimized.Λ c.2.2.2.lambda := by
  rw [evFailureUnion_agree]
  exact (optimizedFailureEventEv_good_components P Qc Qm c hgood).1

end AtP

end

end Nock.NockVMROM.Thm54.OptimizedFailureEventEv
