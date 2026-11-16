/-
  Nock/NockVMROM/Thm54/P8Core/PartAEvents12.lean

  Below the statement.

  * `cyl12 S` — a landed event lifted through the free `αW` coordinate (card `|S|·|𝕂|`).
  * `liftWalkWFailure B` — summands `7` (memory tiling) and `10` (memory forest-α) lifted on the
    walk JointCoins `(αC, γ, αW, z)` (`walkJoint`), i.e. their walk role reads `αW` (card
    `|B|·|𝕂|⁸`).  This is an event lift only; nothing here is fed to the P8 strategy (C2).
  * `consumedFailureEvent12` — the statement's fourteen summands, 7 and 10 by `liftWalkWFailure`,
    the other twelve by `cyl12`, and a FIFTEENTH constant summand `cyl12 (liftTimestampFailure
    (TimestampCollisionEvent memRows))`: the walk-line collision at the timestamp coin `α`, paid
    because the transport of `hAT` re-runs the memory walk at `α` (`PartAReWalk`).
  * `consumedFailureEvent12_card_le` — `≤ optimizedHostileProductionFailureCardBound15 …`: the first
    fourteen terms are `|𝕂| · optimizedHostileProductionFailureCardBound …` term by term
    (`optimizedHostileProductionFailureCardBound12_eq_shift`: every card numeral up one power), the
    fifteenth is `|𝕂|¹¹ · (1 + M(M−1)/2)`.
  * `cylinder₂` / `cylinder₂_card_le` — the two-coordinate cylinder on `Fin n → C`, with the
    instances for the pair summands 2 `(IOγ, IOpole)`, 4 `(IOγ, interPole)`, 11 `(αM, λ)`.
  * `AdaptiveEnvs.const`, `Staged12`, `fixed_of_staged` — the C6.4 constant-strategy shape.

  -- the paper
-/
import Nock.NockVMROM.Thm54.P8Core.PartAPackage12
import Nock.NockVMROM.Thm54.P8Core.RepartitionedStaging
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.PartAEvents12

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.PartA12

open scoped Polynomial BigOperators Classical
open Polynomial
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.P8EventEv

noncomputable section

/-! ## 1. The two lifts -/

section Lifts

variable {K F : Type} [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F]

/-- **The `αW`-cylinder** of a landed event. -/
def cyl12 (S : Finset (OptimizedProductionChallengeTuple K F)) :
    Finset (OptimizedProductionChallengeTuple12 K F) :=
  (S ×ˢ (Finset.univ : Finset K)).map tuple12Equiv.symm.toEmbedding

@[simp] theorem mem_cyl12 (S : Finset (OptimizedProductionChallengeTuple K F))
    (c : OptimizedProductionChallengeTuple12 K F) : c ∈ cyl12 S ↔ forget12 c ∈ S := by
  simp [cyl12, Finset.mem_map_equiv, tuple12Equiv]
  exact Iff.rfl

theorem card_cyl12 (S : Finset (OptimizedProductionChallengeTuple K F)) :
    (cyl12 S).card = S.card * Fintype.card K := by
  simp [cyl12, Finset.card_map, Finset.card_product]

/-- The eight coordinates other than the walk JointCoins `(αC, γ, αW, z)`: the timestamp `αM`,
the IO pair, `(a, b, c)`, `interPole`, `λ`. -/
abbrev WalkRest (K : Type) := K × ((K × K) × (FinalComputeChallengeTuple K × (K × K)))

theorem card_walkRest : Fintype.card (WalkRest K) = Fintype.card K ^ 8 := by
  simp only [WalkRest, Fintype.card_prod, card_finalComputeChallengeTuple]
  ring

/-- `Tuple12 ≃ (αC, γ, αW, z) × rest`. -/
def walkSplitEquiv : OptimizedProductionChallengeTuple12 K F ≃ JointCoins K × WalkRest K where
  toFun c := (walkJoint c, (alphaM c.1, (c.2.1, (c.2.2.1, (c.2.2.2.interPole, c.2.2.2.lambda)))))
  invFun p := (((p.1.1.1, p.1.1.2), (p.2.1, p.1.2.2)),
    (p.2.2.1, (p.2.2.2.1, ⟨p.2.2.2.2.1, p.2.2.2.2.2, p.1.2.1⟩)))
  left_inv c := by
    rcases c with ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, ⟨⟨a5, a6⟩, ⟨comp, ⟨a10, a11, a12⟩⟩⟩⟩
    rfl
  right_inv p := by
    rcases p with ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, ⟨r1, ⟨⟨r2, r3⟩, ⟨comp, ⟨r4, r5⟩⟩⟩⟩⟩
    rfl

/-- **Summands `7` and `10` on the walk coin**: a JointCoins event read at `(αC, γ, αW, z)`. -/
def liftWalkWFailure (B : Finset (JointCoins K)) : Finset (OptimizedProductionChallengeTuple12 K F) :=
  (B ×ˢ (Finset.univ : Finset (WalkRest K))).map walkSplitEquiv.symm.toEmbedding

@[simp] theorem mem_liftWalkWFailure (B : Finset (JointCoins K))
    (c : OptimizedProductionChallengeTuple12 K F) : c ∈ liftWalkWFailure B ↔ walkJoint c ∈ B := by
  simp [liftWalkWFailure, Finset.mem_map_equiv, walkSplitEquiv]

theorem card_liftWalkWFailure (B : Finset (JointCoins K)) :
    (liftWalkWFailure (F := F) B).card = B.card * Fintype.card K ^ 8 := by
  simp only [liftWalkWFailure, Finset.card_map, Finset.card_product, Finset.card_univ,
    card_walkRest]

theorem cyl12_card_le (S : Finset (OptimizedProductionChallengeTuple K F)) (B : ℕ)
    (h : S.card ≤ B) : (cyl12 S).card ≤ Fintype.card K * B := by
  rw [card_cyl12, mul_comm]; exact Nat.mul_le_mul_left _ h

theorem liftWalkW_card_le (B : Finset (JointCoins K)) (b : ℕ)
    (h : B.card ≤ b * Fintype.card K ^ 3) :
    (liftWalkWFailure (F := F) B).card ≤ Fintype.card K * (Fintype.card K ^ 10 * b) := by
  rw [card_liftWalkWFailure]
  calc B.card * Fintype.card K ^ 8 ≤ b * Fintype.card K ^ 3 * Fintype.card K ^ 8 :=
        Nat.mul_le_mul_right _ h
    _ = Fintype.card K * (Fintype.card K ^ 10 * b) := by ring

/-- The landed P8 cylinder of a JointCoins event, lifted to twelve coins, is the cylinder on
`c.1` (the timestamp view), NOT the walk view. -/
theorem mem_cyl12_liftP8 (B : Finset (JointCoins K)) (c : OptimizedProductionChallengeTuple12 K F) :
    c ∈ cyl12 (liftP8Failure (F := F) B) ↔ c.1 ∈ B := by
  simp [liftP8Failure, forget12]

theorem forget12_mem_liftP8 (B : Finset (JointCoins K)) (c : OptimizedProductionChallengeTuple12 K F) :
    forget12 c ∈ liftP8Failure (F := F) B ↔ c.1 ∈ B := by
  simp [liftP8Failure, forget12]

end Lifts

/-! ## 2. The card bound function, one power up -/

/-- **The twelve-coin card bound**: `|𝕂| ·` the consumed card bound. -/
def optimizedHostileProductionFailureCardBound12 (cardK cardF p8Work ioWork N M : ℕ) : ℕ :=
  cardK * optimizedHostileProductionFailureCardBound cardK cardF p8Work ioWork N M

/-- **Term by term: only the card numerals move, each up one power** (`|𝕂|^10/^9 → ^11/^10`). -/
theorem optimizedHostileProductionFailureCardBound12_eq_shift (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureCardBound12 cardK cardF p8Work ioWork N M =
      cardK ^ 11 * p8Work + cardK ^ 10 * ioWork +
        cardK ^ 11 * OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
        cardK ^ 10 * (FiniteIO.ioFailureUnionBound 10 M M cardK + cardK * M) +
        cardK ^ 11 * pricedWalkWork N M := by
  simp only [optimizedHostileProductionFailureCardBound12, optimizedHostileProductionFailureCardBound,
    optimizedTrimmedProductionFailureCardBound]
  ring

/-- Normalised over `|𝕂|¹²`, the FOURTEEN-summand twelve-coin card bound is the consumed probability
bound function. -/
theorem cardBound12_normalised (cardK cardF p8Work ioWork N M : ℕ) (hk : 0 < cardK) :
    (optimizedHostileProductionFailureCardBound12 cardK cardF p8Work ioWork N M : ℚ) / (cardK ^ 12) =
      optimizedHostileProductionFailureProbabilityBound cardK cardF p8Work ioWork N M := by
  rw [← normalized_hostile_card_bound_eq_separate_denominators _ _ _ _ _ _ hk]
  simp only [optimizedHostileProductionFailureCardBound12, Nat.cast_mul]
  have hk' : (cardK : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [pow_succ, mul_comm ((cardK : ℚ) ^ 11), mul_div_mul_left _ _ hk']

/-- **The fifteen-summand card bound**: the fourteen-summand twelve-coin card
bound plus the walk-line collision summand `|𝕂|¹¹ · timestampCollisionBound M`. -/
def optimizedHostileProductionFailureCardBound15 (cardK cardF p8Work ioWork N M : ℕ) : ℕ :=
  optimizedHostileProductionFailureCardBound12 cardK cardF p8Work ioWork N M +
    cardK ^ 11 * OptimizedHostileTimestamps.timestampCollisionBound M

/-- **The fifteen-summand probability bound**:
the consumed fixed-trace bound function, UNCHANGED and not redefined, plus
`(1 + M(M−1)/2)/|𝕂|` for the walk-line collision at the timestamp coin. -/
def optimizedHostileProductionFailureProbabilityBound15 (cardK cardF p8Work ioWork N M : ℕ) : ℚ :=
  optimizedHostileProductionFailureProbabilityBound cardK cardF p8Work ioWork N M +
    (OptimizedHostileTimestamps.timestampCollisionBound M : ℚ) / cardK

/-- The new bound's body, asserted by `rfl`: `ε + (1 + M(M−1)/2)/|𝕂|`. -/
theorem optimizedHostileProductionFailureProbabilityBound15_eq (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureProbabilityBound15 cardK cardF p8Work ioWork N M =
      optimizedHostileProductionFailureProbabilityBound cardK cardF p8Work ioWork N M +
        ((1 + M * (M - 1) / 2 : ℕ) : ℚ) / cardK := rfl

/-- **Normalised over `|𝕂|¹²`, the fifteen-summand card bound is the fifteen-summand probability
bound.** -/
theorem cardBound15_normalised (cardK cardF p8Work ioWork N M : ℕ) (hk : 0 < cardK) :
    (optimizedHostileProductionFailureCardBound15 cardK cardF p8Work ioWork N M : ℚ) / (cardK ^ 12) =
      optimizedHostileProductionFailureProbabilityBound15 cardK cardF p8Work ioWork N M := by
  unfold optimizedHostileProductionFailureCardBound15 optimizedHostileProductionFailureProbabilityBound15
  rw [Nat.cast_add, add_div, cardBound12_normalised _ _ _ _ _ _ hk]
  congr 1
  have hk' : (cardK : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [Nat.cast_mul, Nat.cast_pow]
  field_simp

/-! ## 3. The twelve-coin consumed event -/

namespace Pkg12

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])

/-- **The consumed failure event on the twelve-coin tuple** (`consumedFailureEvent`'s fourteen
summands): summands 7 (memory tiling) and 10 (memory forest-α) on the walk coin `αW`
(`liftWalkWFailure`), every other summand as an `αW`-cylinder; plus the fifteenth, constant summand `summand15`: the walk-line collision
`TimestampCollisionEvent memRows` at the timestamp coin `α`. -/
def consumedFailureEvent12 : Finset (OptimizedProductionChallengeTuple12 K F) :=
  cyl12 (p8SlotEv P Qc Qm) ∪
    cyl12 (P.famIOEventOf Qc Qm) ∪
    cyl12 (liftTimestampFailure
      (OptimizedHostileTimestamps.TimestampCollisionEvent (P.hostileRequests Qc).length)) ∪
    cyl12 (liftInterPoleFailure
      (interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm))) ∪
    cyl12 (liftP8Failure (P.computeWalkRootEvent Qc)) ∪
    cyl12 (liftP8Failure (P.computeTilingEventOf Qc)) ∪
    liftWalkWFailure (P.memoryTilingEventOf Qm) ∪
    cyl12 (liftP8Failure (P.computePrefixGammaEventOf Qc)) ∪
    cyl12 (liftP8Failure (P.memoryPrefixGammaEventOf Qm)) ∪
    liftWalkWFailure (P.memoryForestAlphaEventOf Qm) ∪
    cyl12 (P.decodedLambdaEventOf Qc Qm) ∪
    cyl12 (liftP8Failure (reqPairEv P Qc Qm)) ∪
    cyl12 (liftP8Failure (rootResultEv P Qc Qm)) ∪
    cyl12 (liftP8Failure (alphaZeroEvent : Finset (JointCoins K))) ∪
    cyl12 (liftTimestampFailure
      (OptimizedHostileTimestamps.TimestampCollisionEvent (M P)))

/-- The first fourteen summands (L3's event, verbatim); `consumedFailureEvent12` is this plus
summand 15 (`consumedFailureEvent12_eq`, `rfl`). -/
def consumedFailureEvent14 : Finset (OptimizedProductionChallengeTuple12 K F) :=
  cyl12 (p8SlotEv P Qc Qm) ∪
    cyl12 (P.famIOEventOf Qc Qm) ∪
    cyl12 (liftTimestampFailure
      (OptimizedHostileTimestamps.TimestampCollisionEvent (P.hostileRequests Qc).length)) ∪
    cyl12 (liftInterPoleFailure
      (interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm))) ∪
    cyl12 (liftP8Failure (P.computeWalkRootEvent Qc)) ∪
    cyl12 (liftP8Failure (P.computeTilingEventOf Qc)) ∪
    liftWalkWFailure (P.memoryTilingEventOf Qm) ∪
    cyl12 (liftP8Failure (P.computePrefixGammaEventOf Qc)) ∪
    cyl12 (liftP8Failure (P.memoryPrefixGammaEventOf Qm)) ∪
    liftWalkWFailure (P.memoryForestAlphaEventOf Qm) ∪
    cyl12 (P.decodedLambdaEventOf Qc Qm) ∪
    cyl12 (liftP8Failure (reqPairEv P Qc Qm)) ∪
    cyl12 (liftP8Failure (rootResultEv P Qc Qm)) ∪
    cyl12 (liftP8Failure (alphaZeroEvent : Finset (JointCoins K)))

/-- **Summand 15**: the walk-line collision at the timestamp coin `α`,
at the memory row count.  Constant: it reads no trace. -/
def summand15 : Finset (OptimizedProductionChallengeTuple12 K F) :=
  cyl12 (liftTimestampFailure (OptimizedHostileTimestamps.TimestampCollisionEvent (M P)))

theorem mem_summand15 (c : OptimizedProductionChallengeTuple12 K F) :
    c ∈ summand15 P ↔ alphaM c.1 ∈ OptimizedHostileTimestamps.TimestampCollisionEvent (M P) := by
  simp only [summand15, mem_cyl12, mem_liftTimestampFailure_iff]
  rfl

/-- Summand 15's card: `|𝕂|¹¹ · (1 + M(M−1)/2)` (summand 3's lemma at `D := M`). -/
theorem summand15_card_le :
    (summand15 (F := F) P).card ≤
      Fintype.card K ^ 11 * OptimizedHostileTimestamps.timestampCollisionBound (M P) := by
  have h := cyl12_card_le (F := F) (liftTimestampFailure (F := F)
      (OptimizedHostileTimestamps.TimestampCollisionEvent (K := K) (M P)))
    (Fintype.card K ^ 10 * OptimizedHostileTimestamps.timestampCollisionBound (M P)) (by
      rw [card_liftTimestampFailure, mul_comm]
      exact Nat.mul_le_mul_left _
        (OptimizedHostileTimestamps.TimestampCollisionEvent_card_le_bound _))
  refine h.trans (le_of_eq ?_)
  ring

/-- The first fourteen summands' card (the L3 bound, unchanged). -/
theorem consumedFailureEvent14_card_le :
    (consumedFailureEvent14 P Qc Qm).card ≤
      optimizedHostileProductionFailureCardBound12 (Fintype.card K) (Fintype.card F)
        (workloadEv P P.optimized.Λ) P.hostileIOWork (N P) (M P) := by
  have hp8 := p8SlotEv_card_le P Qc Qm
  have hio : (P.famIOEventOf Qc Qm).card ≤ Fintype.card K ^ 9 * P.hostileIOWork :=
    P.famIOEventOf_card_le Qc Qm
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
  have hγC := liftP8_card_le (F := F) _ _ (P.computePrefixGammaEventOf_card_le Qc)
  have hγM := liftP8_card_le (F := F) _ _ (P.memoryPrefixGammaEventOf_card_le Qm)
  have hlam := P.decodedLambdaEventOf_card_le Qc Qm
  have hpair := liftP8_card_le (F := F) _ _ (reqPairEv_card_le P Qc Qm)
  have hroot := liftP8_card_le (F := F) _ _ (rootResultEv_card_le P Qc Qm)
  have hα0 := liftP8_card_le (F := F) _ _ (alphaZeroEvent_card_le (K := K))
  -- summands 7 and 10, on the walk coin
  have htileM := liftWalkW_card_le (F := F) _ _ (P.memoryTilingEventOf_card_le Qm)
  have hαM := liftWalkW_card_le (F := F) _ _ (P.memoryForestAlphaEventOf_card_le Qm)
  have hsplit :
      optimizedHostileProductionFailureCardBound12 (Fintype.card K) (Fintype.card F)
        (workloadEv P P.optimized.Λ) P.hostileIOWork (N P) (M P) =
      Fintype.card K * (Fintype.card K ^ 10 * p8WorkEv (N P) (M P) P.optimized.Λ) +
        Fintype.card K * (Fintype.card K ^ 9 * P.hostileIOWork) +
        Fintype.card K * (Fintype.card K ^ 10 *
          OptimizedHostileTimestamps.timestampCollisionBound (3 * N P)) +
        Fintype.card K * (Fintype.card K ^ 9 *
          (FiniteIO.ioFailureUnionBound 10 (M P) (M P) (Fintype.card K) +
            Fintype.card K * M P)) +
        Fintype.card K * (Fintype.card K ^ 10 * ComputeWalkRootEvents.walkRootBound (N P)) +
        Fintype.card K * (Fintype.card K ^ 10 * WalkTilingEvents.computeTilingBound (N P)) +
        Fintype.card K * (Fintype.card K ^ 10 * WalkTilingEvents.memoryTilingBound (M P)) +
        Fintype.card K * (Fintype.card K ^ 10 *
          WalkPrefixGammaEvents.computePrefixGammaBound (N P)) +
        Fintype.card K * (Fintype.card K ^ 10 *
          WalkPrefixGammaEvents.memoryPrefixGammaBound (M P)) +
        Fintype.card K * (Fintype.card K ^ 10 *
          WalkForestPrefixAlphaEvents.memoryForestAlphaBound (M P)) +
        Fintype.card K * (Fintype.card K ^ 10 * formRUniformWorkload P.strategy) +
        Fintype.card K * (Fintype.card K ^ 10 * (M P * (2 * Λg P - 1))) +
        Fintype.card K * (Fintype.card K ^ 10 * (2 * Λg P - 1)) +
        Fintype.card K * (Fintype.card K ^ 10 * 1) := by
    simp only [optimizedHostileProductionFailureCardBound12,
      optimizedHostileProductionFailureCardBound,
      optimizedTrimmedProductionFailureCardBound, pricedWalkWork, workloadEv]
    ring
  rw [hsplit]
  unfold consumedFailureEvent14
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ (cyl12_card_le _ _ hα0)
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ (cyl12_card_le _ _ hroot)
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ (cyl12_card_le _ _ hpair)
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ (cyl12_card_le _ _ hlam)
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ hαM
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ (cyl12_card_le _ _ hγM)
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ (cyl12_card_le _ _ hγC)
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ htileM
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ (cyl12_card_le _ _ htileC)
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ (cyl12_card_le _ _ hwalk)
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ (cyl12_card_le _ _ hinter)
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ (cyl12_card_le _ _ hts)
  refine (Finset.card_union_le _ _).trans ?_
  exact Nat.add_le_add (cyl12_card_le _ _ hp8) (cyl12_card_le _ _ hio)

theorem consumedFailureEvent12_eq :
    consumedFailureEvent12 P Qc Qm = consumedFailureEvent14 P Qc Qm ∪ summand15 P := rfl

/-- **The twelve-coin card bound, every `(Qc, Qm)`, no premise**: `|𝕂| ·` the consumed bound,
summand by summand, plus summand 15. -/
theorem consumedFailureEvent12_card_le :
    (consumedFailureEvent12 P Qc Qm).card ≤
      optimizedHostileProductionFailureCardBound15 (Fintype.card K) (Fintype.card F)
        (workloadEv P P.optimized.Λ) P.hostileIOWork (N P) (M P) := by
  have h15 := summand15_card_le (F := F) P
  unfold optimizedHostileProductionFailureCardBound15
  rw [consumedFailureEvent12_eq]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (consumedFailureEvent14_card_le P Qc Qm) h15)

/-- **The twelve-coin probability bound is the fifteen-summand bound function**: the consumed
fixed-trace function plus `(1 + M(M−1)/2)/|𝕂|` (summand 15). -/
theorem consumedFailureEvent12_probability_le :
    ((consumedFailureEvent12 P Qc Qm).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple12 K F) ≤
      optimizedHostileProductionFailureProbabilityBound15 (Fintype.card K) (Fintype.card F)
        (workloadEv P P.optimized.Λ) P.hostileIOWork (N P) (M P) := by
  rw [card_optimizedProductionChallengeTuple12, ← cardBound15_normalised _ _ _ _ _ _ Fintype.card_pos]
  have hcast : ((consumedFailureEvent12 P Qc Qm).card : ℚ) ≤
      (optimizedHostileProductionFailureCardBound15 (Fintype.card K) (Fintype.card F)
        (workloadEv P P.optimized.Λ) P.hostileIOWork (N P) (M P) : ℚ) := by
    exact_mod_cast consumedFailureEvent12_card_le P Qc Qm
  push_cast
  exact div_le_div_of_nonneg_right hcast (by positivity)

/-- **Membership, component by component**: outside the twelve-coin event, the landed tuple
`forget12 c` avoids every cylinder summand, the walk JointCoins `walkJoint c` avoid the
memory tiling and forest-α events, and (summand 15) the timestamp coin `α` is outside the
walk-line collision event at `memRows`. -/
theorem notMem_consumedFailureEvent12 (c : OptimizedProductionChallengeTuple12 K F)
    (h : c ∉ consumedFailureEvent12 P Qc Qm) :
    forget12 c ∉ p8SlotEv P Qc Qm ∧ forget12 c ∉ P.famIOEventOf Qc Qm ∧
      forget12 c ∉ liftTimestampFailure
        (OptimizedHostileTimestamps.TimestampCollisionEvent (P.hostileRequests Qc).length) ∧
      forget12 c ∉ liftInterPoleFailure
        (interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm)) ∧
      c.1 ∉ P.computeWalkRootEvent Qc ∧ c.1 ∉ P.computeTilingEventOf Qc ∧
      walkJoint c ∉ P.memoryTilingEventOf Qm ∧
      c.1 ∉ P.computePrefixGammaEventOf Qc ∧ c.1 ∉ P.memoryPrefixGammaEventOf Qm ∧
      walkJoint c ∉ P.memoryForestAlphaEventOf Qm ∧
      forget12 c ∉ P.decodedLambdaEventOf Qc Qm ∧
      c.1 ∉ reqPairEv P Qc Qm ∧ c.1 ∉ rootResultEv P Qc Qm ∧
      c.1 ∉ (alphaZeroEvent : Finset (JointCoins K)) ∧
      alphaM c.1 ∉ OptimizedHostileTimestamps.TimestampCollisionEvent (M P) := by
  simp only [consumedFailureEvent12, Finset.mem_union, not_or, mem_cyl12,
    mem_liftWalkWFailure] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩ := h
  exact ⟨h1, h2, h3, h4, fun hm => h5 ((forget12_mem_liftP8 _ c).2 hm),
    fun hm => h6 ((forget12_mem_liftP8 _ c).2 hm), h7,
    fun hm => h8 ((forget12_mem_liftP8 _ c).2 hm), fun hm => h9 ((forget12_mem_liftP8 _ c).2 hm),
    h10, h11, fun hm => h12 ((forget12_mem_liftP8 _ c).2 hm),
    fun hm => h13 ((forget12_mem_liftP8 _ c).2 hm), fun hm => h14 ((forget12_mem_liftP8 _ c).2 hm),
    fun hm => h15 ((mem_liftTimestampFailure_iff _ _).2 hm)⟩

end Pkg12

/-! ## 4. The two-coordinate cylinder -/

section Cylinder2

variable {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

/-- The event that the coordinate PAIR `(i, j)` lands in a bad set of pairs determined by the whole
vector. -/
def cylinder₂ (i j : Fin n) (bad : (Fin n → C) → Finset (C × C)) : Finset (Fin n → C) :=
  Finset.univ.filter fun x => (x i, x j) ∈ bad x

theorem card_free_coords₂ (i j : Fin n) (hij : i ≠ j) :
    Fintype.card ({k : Fin n // k ≠ i ∧ k ≠ j} → C) = Fintype.card C ^ (n - 2) := by
  rw [Fintype.card_fun]
  congr 1
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun k : Fin n => k ≠ i ∧ k ≠ j) = Finset.univ \ {i, j} := by
    ext k; simp [not_or]
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    Finset.card_pair hij]

/-- **The pair-cylinder bound** (summands 2, 4, 11): if the bad pair-set of `(i, j)` reads only
coordinates in `dep ∌ i, j`, the cylinder has at most `|C|^{n-2} · B` points.  The proof is the
fibre principle (`SeedFibers.fiberEvent_card_le`) over the `n − 2` free coordinates, with the pair
`(x i, x j)` as the fibre — `fiberEvent₂_card_le` with its second block trivial. -/
theorem cylinder₂_card_le (i j : Fin n) (hij : i ≠ j) (dep : Finset (Fin n))
    (hi : i ∉ dep) (hj : j ∉ dep)
    (bad : (Fin n → C) → Finset (C × C)) (hdep : ReadsOn dep bad) (B : ℕ)
    (hB : ∀ x, (bad x).card ≤ B) :
    (cylinder₂ i j bad).card ≤ Fintype.card C ^ (n - 2) * B := by
  classical
  let R := {k : Fin n // k ≠ i ∧ k ≠ j}
  let ext : (R → C) → (Fin n → C) :=
    fun r k => if h : k ≠ i ∧ k ≠ j then r ⟨k, h⟩ else Classical.arbitrary C
  let g : (R → C) → Finset (C × C) := fun r => bad (ext r)
  have key : ∀ x : Fin n → C, g (fun k : R => x k.1) = bad x := by
    intro x
    refine hdep _ _ ?_
    intro k hk
    have hki : k ≠ i := fun h => hi (h ▸ hk)
    have hkj : k ≠ j := fun h => hj (h ▸ hk)
    simp [ext, hki, hkj]
  have h1 : (cylinder₂ i j bad).card ≤
      (fiberEvent (Finset.univ : Finset (R → C)) g).card := by
    refine Finset.card_le_card_of_injOn
      (fun x : Fin n → C => ((fun k : R => x k.1), (x i, x j))) ?_ ?_
    · intro x hx
      have hx' : (x i, x j) ∈ bad x := by simpa [cylinder₂] using hx
      refine (mem_fiberEvent_iff (Finset.univ : Finset (R → C)) g _ _).2 ⟨Finset.mem_univ _, ?_⟩
      rw [key]
      exact hx'
    · intro x _ y _ hxy
      funext k
      by_cases hki : k = i
      · subst hki; exact congrArg (fun p => p.2.1) hxy
      · by_cases hkj : k = j
        · subst hkj; exact congrArg (fun p => p.2.2) hxy
        · exact congrFun (congrArg Prod.fst hxy) ⟨k, hki, hkj⟩
  refine h1.trans ?_
  refine le_trans (fiberEvent_card_le (Finset.univ : Finset (R → C)) g B (fun r _ => hB _)) ?_
  rw [Finset.card_univ, card_free_coords₂ i j hij]

end Cylinder2

/-! ### The instances: summands 2 `(IOγ, IOpole)`, 4 `(IOγ, interPole)`, 11 `(αM, λ)` -/

section PairInstances

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])

/-- The coin vector of the landed rest (`FamilyEnvCore.restOf`) of a twelve-coin vector. -/
def restOfVec (x : Fin 12 → K) : FamilyEnvCore.Rest K :=
  (((x 0, x 1), (x 2, x 3)), (⟨x 6, x 7, x 8⟩, ⟨x 9, x 10⟩))

/-- **Summand 2 as a pair cylinder on `(IOγ, IOpole) = (4, 5)`.** -/
theorem summand2_eq_cylinder₂ (c : OptimizedProductionChallengeTuple12 K F) :
    c ∈ cyl12 (P.famIOEventOf Qc Qm) ↔
      landedVec12 c ∈ cylinder₂ 4 5
        (fun x => FiniteIO.IOFailureEvent (FamilyEnvCore.famR P.optimized Qc Qm (restOfVec x))) := by
  rw [mem_cyl12]
  have hr := FamilyEnvCore.records_eq_famR P.optimized Qc Qm (forget12 c)
  simp only [cylinder₂, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show P.hostileRecordsAt (forget12 c) (P.familyQm (forget12 c) Qm) (P.familyQc (forget12 c) Qc) =
    _ from hr]
  rfl

/-- The summand-2 bad set reads only the nine non-IO coins of the landed eleven. -/
theorem summand2_readsOn :
    ReadsOn (C := K) ({0, 1, 2, 3, 6, 7, 8, 9, 10} : Finset (Fin 12))
      (fun x => FiniteIO.IOFailureEvent (FamilyEnvCore.famR P.optimized Qc Qm (restOfVec x))) := by
  intro x y h
  have e : restOfVec x = restOfVec y := by
    simp only [restOfVec]
    rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 6 (by decide),
      h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide)]
  show FiniteIO.IOFailureEvent (FamilyEnvCore.famR P.optimized Qc Qm (restOfVec x)) =
    FiniteIO.IOFailureEvent (FamilyEnvCore.famR P.optimized Qc Qm (restOfVec y))
  rw [e]

/-- **Summand 2, pair-cylinder bound** at twelve coins: `|𝕂|¹⁰ · ioFailureUnionBound`. -/
theorem summand2_cylinder₂_card_le :
    (cylinder₂ (4 : Fin 12) 5
        (fun x => FiniteIO.IOFailureEvent (FamilyEnvCore.famR P.optimized Qc Qm (restOfVec x)))).card ≤
      Fintype.card K ^ 10 *
        FiniteIO.ioFailureUnionBound 10 (3 * P.optimized.family.problem.cfg.compRows)
          P.optimized.family.problem.cfg.memRows (Fintype.card K) :=
  cylinder₂_card_le 4 5 (by decide) _ (by decide) (by decide) _ (summand2_readsOn P Qc Qm) _
    (fun x => (FiniteIO.IOFailureEvent_card_le _).trans
      (ioFailureUnionBound_mono₂ 10 _ _ _ _ (Fintype.card K)
        (FamilyEnvCore.hostileRequestsAt_length_le P.optimized _ _)
        (FamilyEnvCore.hostileResponsesAt_length_le P.optimized _ _)))

/-- **Summand 4 as a pair cylinder on `(IOγ, interPole) = (4, 9)`** (the bad set is fixed by the
committed trace, `ReadsOn ∅`). -/
theorem summand4_eq_cylinder₂ (S : Finset (K × K)) (c : OptimizedProductionChallengeTuple12 K F) :
    c ∈ cyl12 (liftInterPoleFailure (F := F) S) ↔ landedVec12 c ∈ cylinder₂ 4 9 (fun _ => S) := by
  rw [mem_cyl12, mem_liftInterPoleFailure_iff]
  simp only [cylinder₂, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem summand4_cylinder₂_card_le (S : Finset (K × K)) :
    (cylinder₂ (4 : Fin 12) 9 (fun _ => S)).card ≤ Fintype.card K ^ 10 * S.card :=
  cylinder₂_card_le 4 9 (by decide) ∅ (by simp) (by simp) _ (fun _ _ _ => rfl) _ (fun _ => le_rfl)

/-- **Summand 11 as a pair cylinder on `(αM, λ) = (2, 10)`** (fixed traces: `ReadsOn ∅`). -/
theorem summand11_eq_cylinder₂ (c : OptimizedProductionChallengeTuple12 K F) :
    c ∈ cyl12 (P.decodedLambdaEventOf Qc Qm) ↔
      landedVec12 c ∈ cylinder₂ 2 10 (fun _ =>
        (Finset.Icc 1 P.optimized.family.problem.cfg.kMem).biUnion fun r =>
          DecodedLambdaEvent.decodedRootBad (P.computeSourceEnv Qc) (P.memorySourceEnv Qm)
            (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.kMem r) := by
  rw [mem_cyl12]
  simp only [OptimizedFullStrictNockVMROMPackage.decodedLambdaEventOf,
    DecodedLambdaEvent.decodedLambdaEventOfEnvs, cylinder₂, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rfl

theorem summand11_cylinder₂_card_le (S : Finset (K × K)) :
    (cylinder₂ (2 : Fin 12) 10 (fun _ => S)).card ≤ Fintype.card K ^ 10 * S.card :=
  cylinder₂_card_le 2 10 (by decide) ∅ (by simp) (by simp) _ (fun _ _ _ => rfl) _ (fun _ => le_rfl)

end PairInstances

/-! ## 5. The C6.4 corollary shape: a fixed trace is a constant strategy -/

section ConstStrategy

open RepartitionedStaging
open Nock.Reified

variable {n M : ℕ} {K F : Type} [Fintype K] [DecidableEq K] [Fintype F]

/-- **A fixed trace is an `AdaptiveEnvs` constant in the coins.**  The read discipline holds
trivially (`rfl`). -/
def constAdaptiveEnvs (roleRound baseRound : ℕ → ℕ) (sampledAfter : Fin n → ℕ)
    (eK : Fin M → Env K) (eF : Fin M → Env F) : AdaptiveEnvs n M K F where
  roleRound := roleRound
  baseRound := baseRound
  sampledAfter := sampledAfter
  envK := fun _ => eK
  envF := fun _ => eF
  K_reads := fun _ _ _ _ _ => rfl
  F_reads := fun _ _ _ _ _ => rfl

@[simp] theorem constAdaptiveEnvs_envK (roleRound baseRound : ℕ → ℕ) (sampledAfter : Fin n → ℕ)
    (eK : Fin M → Env K) (eF : Fin M → Env F) (χ : Fin n → K) :
    (constAdaptiveEnvs roleRound baseRound sampledAfter eK eF).envK χ = eK := rfl

@[simp] theorem constAdaptiveEnvs_envF (roleRound baseRound : ℕ → ℕ) (sampledAfter : Fin n → ℕ)
    (eK : Fin M → Env K) (eF : Fin M → Env F) (χ : Fin n → K) :
    (constAdaptiveEnvs roleRound baseRound sampledAfter eK eF).envF χ = eF := rfl

/-- **The fixed-trace bound from any staged bound over adaptive envs** (the constant-strategy
instance). -/
theorem fixed_of_staged_envs (roleRound baseRound : ℕ → ℕ) (sampledAfter : Fin n → ℕ)
    (bad : (Fin M → Env K) → (Fin M → Env F) → (Fin n → K) → Prop) [∀ a b χ, Decidable (bad a b χ)]
    (B : ℕ)
    (hstaged : ∀ A : AdaptiveEnvs n M K F, A.roleRound = roleRound → A.baseRound = baseRound →
      A.sampledAfter = sampledAfter →
      (Finset.univ.filter fun χ => bad (A.envK χ) (A.envF χ) χ).card ≤ B)
    (eK : Fin M → Env K) (eF : Fin M → Env F) :
    (Finset.univ.filter fun χ => bad eK eF χ).card ≤ B :=
  hstaged (constAdaptiveEnvs roleRound baseRound sampledAfter eK eF) rfl rfl rfl

/-- A fixed trace is staged (B0 constant, and every later block trivially). -/
theorem staged12_const {ι β : Type*} (colRound : ι → ℕ) (q : ι → β) :
    Staged12 colRound (fun (_ : OptimizedProductionChallengeTuple12 K F) => q) :=
  fun _ _ _ _ => rfl

/-- **`complete_false_acceptance_bound_of_staged`'s shape**: any bound over every staged strategy
gives the fixed-trace bound at every fixed trace pair. -/
theorem fixed_of_staged {ι β : Type*} (colRound : ι → ℕ)
    (Bad : (ι → β) → OptimizedProductionChallengeTuple12 K F → Prop) [∀ q c, Decidable (Bad q c)]
    (bound : ℚ)
    (hstaged : ∀ Q : OptimizedProductionChallengeTuple12 K F → ι → β, Staged12 colRound Q →
      ((Finset.univ.filter fun c => Bad (Q c) c).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple12 K F) ≤ bound)
    (q : ι → β) :
    ((Finset.univ.filter fun c => Bad q c).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple12 K F) ≤ bound :=
  hstaged (fun _ => q) (staged12_const colRound q)

end ConstStrategy

end

end Nock.NockVMROM.Thm54.PartA12
