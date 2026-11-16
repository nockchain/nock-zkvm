/-
  Nock/NockVMROM/Thm54/P8Core/PartAStaged12.lean

  **H2.2, the staged false-acceptance bound at the parallel
  package and `repartitionedChronology`.**

  Objects (design §5, at the parallel package):
  * traces: a 309-column compute strategy `Qc : Tuple12 → Fin 309 → F[X]` and a 205-column memory
    strategy `Qm : Tuple12 → Fin P.memoryChip.rap.w → F[X]`;
  * `StagedTraces12 P Qc Qm` — every column a function of the coins sampled strictly before its
    block (`newComputeColRound`, `newMemoryColRound`, `repartitionedChronology.sampledAfter`);
    B0 is constant;
  * `consumedFailureEvent309 P Qc Qm` — L3's twelve-coin consumed event at the 303-column
    truncation (no summand reads the six walk columns; summands 5 and 8 ARE L2's 309 events,
    `summand5_eq309`, `summand8_eq309`);
  * `AcceptanceAt309` — the un-hosted 309 compute chip at `forget12 c` (it reads the timestamp
    `αM` only) and the twelve-coin memory chip at `c` (walk coin `αW` at slot 9).

  Main results:
  * `staged_consumed_card_le` — along a staged strategy the consumed event has at most
    `optimizedHostileProductionFailureCardBound15 …` points, term by term;
  * `staged_false_acceptance_bound12` — for every staged strategy,
    `Pr_c[Accept(Qc c, Qm c, c) ∧ ¬target] ≤ optimizedHostileProductionFailureProbabilityBound15 …`
    (the consumed fixed-trace function plus `(1 + M(M−1)/2)/|𝕂|`), GIVEN an acceptance-to-target
    implication; the unconditional form, with the parallel package's own target and no `hAT`, is
    `PartATarget309.staged_false_acceptance_bound12'`;
  * `strategy_staged` — the strategy form (B0 fixed, B1 a function of the M1 coins, B2 of all
    twelve) implies `StagedTraces12`, and conversely;
  * `complete_false_acceptance_bound_of_staged12` — the fixed-trace corollary (constant strategy).

  Scope: every statement is at `repartitionedChronology` and the parallel package; nothing here
  states or implies a bound at `deployedChronology`
-/
import Nock.NockVMROM.Thm54.P8Core.PartATopology12
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.PartAStaged

open scoped Polynomial
open Nock Nock.Reified Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.RepartitionedStaging
open Nock.NockVMROM.Thm54.PartA12
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.Framework
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.SizeWindowCounting

noncomputable section

/-! ## 1. Counting helpers -/

section Count

variable {K F : Type} [Fintype K] [DecidableEq K] [Fintype F] [DecidableEq F]

/-- A set of coin vectors, as a set of twelve-coin tuples. -/
def vecSet (s : Finset (Fin 12 → K)) : Finset (OptimizedProductionChallengeTuple12 K F) :=
  s.map (tuple12VecEquiv (K := K) (F := F)).symm.toEmbedding

theorem mem_vecSet (s : Finset (Fin 12 → K)) (c : OptimizedProductionChallengeTuple12 K F) :
    c ∈ vecSet s ↔ landedVec12 c ∈ s := by
  unfold vecSet
  rw [Finset.mem_map_equiv]
  rfl

theorem card_vecSet (s : Finset (Fin 12 → K)) : (vecSet (F := F) s).card = s.card := by
  simp [vecSet]

/-- A landed event whose fibre over `λ` is a `JointCoins` set of `≤ w·|𝕂|³` points. -/
theorem card_jointLam_le (B : K → Finset (JointCoins K)) (w : ℕ)
    (hB : ∀ l, (B l).card ≤ w * Fintype.card K ^ 3) :
    (Finset.univ.filter fun c : OptimizedProductionChallengeTuple K F =>
      c.1 ∈ B c.2.2.2.lambda).card ≤ Fintype.card K ^ 10 * w := by
  have hcover : (Finset.univ.filter fun c : OptimizedProductionChallengeTuple K F =>
      c.1 ∈ B c.2.2.2.lambda) ⊆
      (Finset.univ : Finset K).biUnion fun lam =>
        (B lam) ×ˢ (Finset.univ.filter fun r : (K × K) ×
            (FinalComputeChallengeTuple K × MemoryChallengeTuple K) => r.2.2.lambda = lam) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    refine Finset.mem_biUnion.mpr ⟨c.2.2.2.lambda, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_product]
    exact ⟨hc, by simp⟩
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
  calc _ ≤ ((Finset.univ : Finset K).biUnion fun lam =>
          (B lam) ×ˢ (Finset.univ.filter fun r : (K × K) ×
              (FinalComputeChallengeTuple K × MemoryChallengeTuple K) => r.2.2.lambda = lam)).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ lam : K, ((B lam) ×ˢ (Finset.univ.filter fun r : (K × K) ×
          (FinalComputeChallengeTuple K × MemoryChallengeTuple K) => r.2.2.lambda = lam)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _lam : K, (w * Fintype.card K ^ 3) * Fintype.card K ^ 6 := by
        apply Finset.sum_le_sum
        intro lam _
        rw [Finset.card_product]
        exact Nat.mul_le_mul (hB lam) (hfibre lam)
    _ = Fintype.card K ^ 10 * w := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

end Count

/-! ## 2. The parallel package's objects -/

section Package

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **`StagedTraces` at the parallel package** (design §5): each 309 compute column and each 205
memory column is a function of the coins sampled strictly before its block. -/
def StagedTraces12 (Qc : OptimizedProductionChallengeTuple12 K F → Fin 309 → F[X])
    (Qm : OptimizedProductionChallengeTuple12 K F → Fin P.memoryChip.rap.w → F[X]) : Prop :=
  Staged12 (fun j : Fin 309 => newComputeColRound j) Qc ∧
    Staged12 (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) Qm

/-- **The parallel package's consumed event**: L3's twelve-coin event at the 303-column truncation
of the 309 trace. -/
def consumedFailureEvent309 (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    Finset (OptimizedProductionChallengeTuple12 K F) :=
  Pkg12.consumedFailureEvent12 P (truncQc P Qc) Qm

/-- **Acceptance at the parallel package**: the un-hosted 309 compute chip at `forget12 c` and the
twelve-coin memory chip at `c`. -/
structure AcceptanceAt309 (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple12 K F) : Prop where
  compute_satisfies : RAP.SatisfiesWithPreprocessing (Unhosted309.pkgComputeChipAt309 P (forget12 c)) Qc
  memory_satisfies : RAP.SatisfiesWithPreprocessing (Pkg12.memoryChipAt12 P c) (Pkg12.familyQm12 P c Qm)

/-- The consumed-bound arguments at the parallel package. -/
abbrev bound12 : ℕ :=
  optimizedHostileProductionFailureCardBound12 (Fintype.card K) (Fintype.card F)
    (workloadEv P P.optimized.Λ) P.hostileIOWork (N P) (M P)

abbrev bound15 : ℕ :=
  optimizedHostileProductionFailureCardBound15 (Fintype.card K) (Fintype.card F)
    (workloadEv P P.optimized.Λ) P.hostileIOWork (N P) (M P)

/-! ## 3. -/

theorem m1Part_card_le (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (lmb : K) :
    (PartAB0.m1Part (builtStrategyEv P Qc Qm) P.optimized.Λ lmb).card ≤
      (1 + (3 + 19 * N P) * (2 * P.optimized.Λ - 1) + axisUniformWorkload (N P) (M P) +
        sizeWindowRootBound P.optimized.Λ) * Fintype.card K ^ 3 := by
  have h2 : (2 : K) ≠ 0 := P.two_ne_zero
  have hZ : (zeroSeedFailureEvent (K := K)).card ≤ 1 * Fintype.card K ^ 3 := by
    simp [zeroSeedFailureEvent_card]
  have hs : (SemanticStrategy.computeSkeletonRows (builtStrategyEv P Qc Qm).skeleton).length ≤ N P :=
    StrategyOfTracesEv.skeletonEv_computeRows_le P.optimized Qc Qm
  have hC : (collisionFailureEvent (K := K)
      (guardedCensusEv K (builtStrategyEv P Qc Qm).skeleton P.optimized.Λ)).card ≤
      ((3 + 19 * N P) * (2 * P.optimized.Λ - 1)) * Fintype.card K ^ 3 :=
    (collisionFailureEvent_guardedCensusEv_card_le _ _).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
  have hA' : (envelopeAxisFailureEvent (builtStrategyEv P Qc Qm) lmb).card ≤
      axisUniformWorkload (N P) (M P) * Fintype.card K ^ 3 :=
    envelopeAxisFailureEvent_Ev_card_le P.optimized Qc Qm P.stateTagChar h2 lmb
  have hW := guardedSizeWindowFailure_card_le (K := K) (builtStrategyEv P Qc Qm).skeleton P.optimized.Λ
  unfold PartAB0.m1Part
  refine ((Finset.card_union_le _ _).trans (Nat.add_le_add_right ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _)).trans ?_
  refine (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hZ hC) hA') hW).trans (le_of_eq ?_)
  ring

/-! ## 4. The H2.1 table along a staged strategy (coin vectors) -/

variable {qc : (Fin 12 → K) → Fin 309 → F[X]} {qm : (Fin 12 → K) → Fin P.memoryChip.rap.w → F[X]}

theorem agree_of_staged0C (hC : StagedVec (fun j : Fin 309 => newComputeColRound j) qc)
    (x y : Fin 12 → K) : AgreeC309 0 (qc x) (qc y) :=
  fun j hj => staged_B0_const hC x y j (Nat.le_zero.mp hj)

theorem agree_of_staged0M (hM : StagedVec (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) qm)
    (x y : Fin 12 → K) : AgreeM P 0 (qm x) (qm y) :=
  fun j hj => staged_B0_const hM x y j (Nat.le_zero.mp hj)

/-- **Summand 1 (topology part, coin `γ`)**: `ReadsOn ({αM, z, λ} ∪ M1)`, `γ ∉`. -/
theorem summand1_topo_readsOn12 (hC : StagedVec (fun j : Fin 309 => newComputeColRound j) qc)
    (hM : StagedVec (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) qm) :
    ReadsOn (C := K) ({2, 3, 10} ∪ coinsBefore 1) (fun x => badTopo P (qc x) (qm x) x) :=
  readsOn_of_colCongr₂ hC hM 1 _ (fun q₁ q₂ x => badTopo P q₁ q₂ x)
    (fun _ _ _ _ h₁ h₂ => badTopo_B01 P h₁ h₂) (fun q₁ q₂ => badTopo_coins P q₁ q₂)

theorem summand2_readsOn12 (hC : StagedVec (fun j : Fin 309 => newComputeColRound j) qc)
    (hM : StagedVec (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) qm) :
    ReadsOn (C := K) ({0, 1, 2, 3, 6, 7, 8, 9, 10} ∪ coinsBefore 1)
      (fun x => bad2 P (qc x) (qm x) x) :=
  readsOn_of_colCongr₂ hC hM 1 _ (fun q₁ q₂ x => bad2 P q₁ q₂ x)
    (fun _ _ _ _ h₁ h₂ => by funext x; unfold bad2; rw [famR_B01 P h₁ h₂])
    (fun q₁ q₂ => bad2_coins P q₁ q₂)

theorem summand4_readsOn12 (hC : StagedVec (fun j : Fin 309 => newComputeColRound j) qc)
    (hM : StagedVec (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) qm) :
    ReadsOn (C := K) (∅ ∪ coinsBefore 1) (fun x => bad4 P (qm x)) :=
  readsOn_of_colCongr₂ hC hM 1 ∅ (fun (_ : Fin 309 → F[X]) q₂ (_ : Fin 12 → K) => bad4 P q₂)
    (fun _ _ _ _ _ h₂ => by funext _; exact bad4_B01 P h₂) (fun _ _ _ _ _ => rfl)

theorem summand5a_readsOn12 (hC : StagedVec (fun j : Fin 309 => newComputeColRound j) qc)
    (hM : StagedVec (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) qm) :
    ReadsOn (C := K) ({1, 2, 3} ∪ coinsBefore 1) (fun x => bad5a P (qc x) x) :=
  readsOn_of_colCongr₂ hC hM 1 _ (fun q₁ (_ : Fin P.memoryChip.rap.w → F[X]) x => bad5a P q₁ x)
    (fun _ _ _ _ h₁ _ => bad5a_B01 P h₁) (fun q₁ _ => bad5a_coins P q₁)

theorem summand5g_readsOn12 (hC : StagedVec (fun j : Fin 309 => newComputeColRound j) qc)
    (hM : StagedVec (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) qm) :
    ReadsOn (C := K) ({3} ∪ coinsBefore 1) (fun x => bad5g P (qc x) x) :=
  readsOn_of_colCongr₂ hC hM 1 _ (fun q₁ (_ : Fin P.memoryChip.rap.w → F[X]) x => bad5g P q₁ x)
    (fun _ _ _ _ h₁ _ => bad5g_B01 P h₁) (fun q₁ _ => bad5g_coins P q₁)

theorem summand8_readsOn12 (hC : StagedVec (fun j : Fin 309 => newComputeColRound j) qc)
    (hM : StagedVec (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) qm) :
    ReadsOn (C := K) (∅ ∪ coinsBefore 1) (fun x => bad8 P (qc x)) :=
  readsOn_of_colCongr₂ hC hM 1 ∅ (fun q₁ (_ : Fin P.memoryChip.rap.w → F[X]) (_ : Fin 12 → K) => bad8 P q₁)
    (fun _ _ _ _ h₁ _ => by funext _; exact bad8_B01 P h₁) (fun _ _ _ _ _ => rfl)

theorem summand9_readsOn12 (hC : StagedVec (fun j : Fin 309 => newComputeColRound j) qc)
    (hM : StagedVec (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) qm) :
    ReadsOn (C := K) (∅ ∪ coinsBefore 1) (fun x => bad9 P (qm x)) :=
  readsOn_of_colCongr₂ hC hM 1 ∅ (fun (_ : Fin 309 → F[X]) q₂ (_ : Fin 12 → K) => bad9 P q₂)
    (fun _ _ _ _ _ h₂ => by funext _; exact bad9_B01 P h₂) (fun _ _ _ _ _ => rfl)

theorem summand10_readsOn12 (hC : StagedVec (fun j : Fin 309 => newComputeColRound j) qc)
    (hM : StagedVec (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) qm) :
    ReadsOn (C := K) ({1} ∪ coinsBefore 1) (fun x => bad10 P (qm x) x) :=
  readsOn_of_colCongr₂ hC hM 1 _ (fun (_ : Fin 309 → F[X]) q₂ x => bad10 P q₂ x)
    (fun _ _ _ _ _ h₂ => bad10_B01 P h₂) (fun _ q₂ => bad10_coins P q₂)

/-- **The B0 summands are fixed along the strategy** (1-M1, 3, 6, 7, 11, 12, 13; 14 reads
nothing). -/
theorem summands_B0_const (hC : StagedVec (fun j : Fin 309 => newComputeColRound j) qc)
    (hM : StagedVec (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) qm)
    (x y : Fin 12 → K) :
    (∀ lmb, PartAB0.m1Part (builtStrategyEv P (truncQc P (qc x)) (qm x)) P.optimized.Λ lmb =
        PartAB0.m1Part (builtStrategyEv P (truncQc P (qc y)) (qm y)) P.optimized.Λ lmb) ∧
      (P.hostileRequests (truncQc P (qc x))).length = (P.hostileRequests (truncQc P (qc y))).length ∧
      P.computeTilingEventOf (truncQc P (qc x)) = P.computeTilingEventOf (truncQc P (qc y)) ∧
      P.memoryTilingEventOf (qm x) = P.memoryTilingEventOf (qm y) ∧
      P.decodedLambdaEventOf (truncQc P (qc x)) (qm x) = P.decodedLambdaEventOf (truncQc P (qc y)) (qm y) ∧
      reqPairEv P (truncQc P (qc x)) (qm x) = reqPairEv P (truncQc P (qc y)) (qm y) ∧
      rootResultEv P (truncQc P (qc x)) (qm x) = rootResultEv P (truncQc P (qc y)) (qm y) := by
  have h0C := agree_of_staged0C hC x y
  have h0M := agree_of_staged0M P hM x y
  exact ⟨fun lmb => summand1_m1_B0 P h0C h0M lmb, hostileRequests_length_B0 P h0C,
    summand6_B0 P h0C, summand7_B0 P h0M, summand11_B0' P h0C h0M, summand12_B0' P h0C h0M,
    summand13_B0' P h0C h0M⟩

/-- **The H2.1 table, collected** (the fourteen summands of `consumedFailureEvent12`, at the parallel
package, along any staged strategy): the B0 summands are constant, and every M2 summand's bad set
reads only the M1 coins and its own direct reads, its own coin excluded. -/
theorem consumedFailureEvent12_roundLocal
    (hC : StagedVec (fun j : Fin 309 => newComputeColRound j) qc)
    (hM : StagedVec (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) qm) :
    (∀ x y, (∀ lmb, PartAB0.m1Part (builtStrategyEv P (truncQc P (qc x)) (qm x)) P.optimized.Λ lmb =
        PartAB0.m1Part (builtStrategyEv P (truncQc P (qc y)) (qm y)) P.optimized.Λ lmb) ∧
      (P.hostileRequests (truncQc P (qc x))).length = (P.hostileRequests (truncQc P (qc y))).length ∧
      P.computeTilingEventOf (truncQc P (qc x)) = P.computeTilingEventOf (truncQc P (qc y)) ∧
      P.memoryTilingEventOf (qm x) = P.memoryTilingEventOf (qm y) ∧
      P.decodedLambdaEventOf (truncQc P (qc x)) (qm x) = P.decodedLambdaEventOf (truncQc P (qc y)) (qm y) ∧
      reqPairEv P (truncQc P (qc x)) (qm x) = reqPairEv P (truncQc P (qc y)) (qm y) ∧
      rootResultEv P (truncQc P (qc x)) (qm x) = rootResultEv P (truncQc P (qc y)) (qm y)) ∧
    ReadsOn (C := K) ({2, 3, 10} ∪ coinsBefore 1) (fun x => badTopo P (qc x) (qm x) x) ∧
    ReadsOn (C := K) ({0, 1, 2, 3, 6, 7, 8, 9, 10} ∪ coinsBefore 1) (fun x => bad2 P (qc x) (qm x) x) ∧
    ReadsOn (C := K) (∅ ∪ coinsBefore 1) (fun x => bad4 P (qm x)) ∧
    ReadsOn (C := K) ({1, 2, 3} ∪ coinsBefore 1) (fun x => bad5a P (qc x) x) ∧
    ReadsOn (C := K) ({3} ∪ coinsBefore 1) (fun x => bad5g P (qc x) x) ∧
    ReadsOn (C := K) (∅ ∪ coinsBefore 1) (fun x => bad8 P (qc x)) ∧
    ReadsOn (C := K) (∅ ∪ coinsBefore 1) (fun x => bad9 P (qm x)) ∧
    ReadsOn (C := K) ({1} ∪ coinsBefore 1) (fun x => bad10 P (qm x) x) :=
  ⟨summands_B0_const P hC hM, summand1_topo_readsOn12 P hC hM, summand2_readsOn12 P hC hM,
    summand4_readsOn12 P hC hM, summand5a_readsOn12 P hC hM, summand5g_readsOn12 P hC hM,
    summand8_readsOn12 P hC hM, summand9_readsOn12 P hC hM, summand10_readsOn12 P hC hM⟩

theorem summand15_readsOn12 :
    ReadsOn (C := K) (∅ : Finset (Fin 12))
      (fun _ : Fin 12 → K => OptimizedHostileTimestamps.TimestampCollisionEvent (K := K) (M P)) :=
  fun _ _ _ => rfl

/-! ## 5. -/

theorem not_mem_coins_topo : (1 : Fin 12) ∉ ({2, 3, 10} : Finset (Fin 12)) ∪ coinsBefore 1 := by
  rw [coinsBefore_one]; decide
theorem not_mem_coins_2 : (4 : Fin 12) ∉ ({0, 1, 2, 3, 6, 7, 8, 9, 10} : Finset (Fin 12)) ∪ coinsBefore 1 ∧
    (5 : Fin 12) ∉ ({0, 1, 2, 3, 6, 7, 8, 9, 10} : Finset (Fin 12)) ∪ coinsBefore 1 := by
  rw [coinsBefore_one]; decide
theorem not_mem_coins_4 : (4 : Fin 12) ∉ (∅ : Finset (Fin 12)) ∪ coinsBefore 1 ∧
    (9 : Fin 12) ∉ (∅ : Finset (Fin 12)) ∪ coinsBefore 1 := by
  rw [coinsBefore_one]; decide
theorem not_mem_coins_5a : (0 : Fin 12) ∉ ({1, 2, 3} : Finset (Fin 12)) ∪ coinsBefore 1 := by
  rw [coinsBefore_one]; decide
theorem not_mem_coins_5g : (1 : Fin 12) ∉ ({3} : Finset (Fin 12)) ∪ coinsBefore 1 := by
  rw [coinsBefore_one]; decide
theorem not_mem_coins_γ : (1 : Fin 12) ∉ (∅ : Finset (Fin 12)) ∪ coinsBefore 1 := by
  rw [coinsBefore_one]; decide
theorem not_mem_coins_10 : (11 : Fin 12) ∉ ({1} : Finset (Fin 12)) ∪ coinsBefore 1 := by
  rw [coinsBefore_one]; decide

open Classical in
theorem staged_consumed_card_le
    (Qc : OptimizedProductionChallengeTuple12 K F → Fin 309 → F[X])
    (Qm : OptimizedProductionChallengeTuple12 K F → Fin P.memoryChip.rap.w → F[X])
    (hst : StagedTraces12 P Qc Qm) :
    (Finset.univ.filter fun c => c ∈ consumedFailureEvent309 P (Qc c) (Qm c)).card ≤ bound15 P := by
  classical
  haveI : Nonempty K := ⟨0⟩
  let qc : (Fin 12 → K) → Fin 309 → F[X] := fun x => Qc (tuple12OfVec x)
  let qm : (Fin 12 → K) → Fin P.memoryChip.rap.w → F[X] := fun x => Qm (tuple12OfVec x)
  have hC : StagedVec (fun j : Fin 309 => newComputeColRound j) qc := stagedVec_of_staged12 hst.1
  have hM : StagedVec (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) qm :=
    stagedVec_of_staged12 hst.2
  let x0 : Fin 12 → K := fun _ => 0
  let T0 := builtStrategyEv P (truncQc P (qc x0)) (qm x0)
  let A1 : Finset (OptimizedProductionChallengeTuple12 K F) :=
    cyl12 (Finset.univ.filter fun c : OptimizedProductionChallengeTuple K F =>
      c.1 ∈ PartAB0.m1Part T0 P.optimized.Λ c.2.2.2.lambda)
  let A1t : Finset (OptimizedProductionChallengeTuple12 K F) :=
    vecSet (cylinder (1 : Fin 12) (fun x => badTopo P (qc x) (qm x) x))
  let A2 : Finset (OptimizedProductionChallengeTuple12 K F) :=
    vecSet (cylinder₂ (4 : Fin 12) 5 (fun x => bad2 P (qc x) (qm x) x))
  let A3 : Finset (OptimizedProductionChallengeTuple12 K F) :=
    cyl12 (liftTimestampFailure (OptimizedHostileTimestamps.TimestampCollisionEvent
      (P.hostileRequests (truncQc P (qc x0))).length))
  let A4 : Finset (OptimizedProductionChallengeTuple12 K F) :=
    vecSet (cylinder₂ (4 : Fin 12) 9 (fun x => bad4 P (qm x)))
  let A5a : Finset (OptimizedProductionChallengeTuple12 K F) :=
    vecSet (cylinder (0 : Fin 12) (fun x => bad5a P (qc x) x))
  let A5g : Finset (OptimizedProductionChallengeTuple12 K F) :=
    vecSet (cylinder (1 : Fin 12) (fun x => bad5g P (qc x) x))
  let A6 : Finset (OptimizedProductionChallengeTuple12 K F) :=
    cyl12 (liftP8Failure (P.computeTilingEventOf (truncQc P (qc x0))))
  let A7 : Finset (OptimizedProductionChallengeTuple12 K F) :=
    liftWalkWFailure (P.memoryTilingEventOf (qm x0))
  let A8 : Finset (OptimizedProductionChallengeTuple12 K F) :=
    vecSet (cylinder (1 : Fin 12) (fun x => bad8 P (qc x)))
  let A9 : Finset (OptimizedProductionChallengeTuple12 K F) :=
    vecSet (cylinder (1 : Fin 12) (fun x => bad9 P (qm x)))
  let A10 : Finset (OptimizedProductionChallengeTuple12 K F) :=
    vecSet (cylinder (11 : Fin 12) (fun x => bad10 P (qm x) x))
  let A11 : Finset (OptimizedProductionChallengeTuple12 K F) :=
    cyl12 (P.decodedLambdaEventOf (truncQc P (qc x0)) (qm x0))
  let A12 : Finset (OptimizedProductionChallengeTuple12 K F) :=
    cyl12 (liftP8Failure (reqPairEv P (truncQc P (qc x0)) (qm x0)))
  let A13 : Finset (OptimizedProductionChallengeTuple12 K F) :=
    cyl12 (liftP8Failure (rootResultEv P (truncQc P (qc x0)) (qm x0)))
  let A14 : Finset (OptimizedProductionChallengeTuple12 K F) :=
    cyl12 (liftP8Failure (alphaZeroEvent : Finset (JointCoins K)))
  let A15 : Finset (OptimizedProductionChallengeTuple12 K F) := Pkg12.summand15 P
  -- membership
  have hsub : (Finset.univ.filter fun c => c ∈ consumedFailureEvent309 P (Qc c) (Qm c)) ⊆
      A1 ∪ (A1t ∪ (A2 ∪ (A3 ∪ (A4 ∪ (A5a ∪ (A5g ∪ (A6 ∪ (A7 ∪ (A8 ∪ (A9 ∪ (A10 ∪ (A11 ∪ (A12 ∪ (A13 ∪ (A14 ∪ A15))))))))))))))) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨x, rfl⟩ : ∃ x, c = tuple12OfVec x := ⟨landedVec12 c, (tuple12OfVec_landedVec12 c).symm⟩
    obtain ⟨e1, e3, e6, e7, e11, e12, e13⟩ := summands_B0_const P hC hM x x0
    have hqc : Qc (tuple12OfVec x) = qc x := rfl
    have hqm : Qm (tuple12OfVec x) = qm x := rfl
    have hvx : landedVec12 (tuple12OfVec (F := F) x) = x := landedVec12_tuple12OfVec x
    rw [hqc, hqm] at hc
    simp only [consumedFailureEvent309, Pkg12.consumedFailureEvent12, Finset.mem_union] at hc
    rcases hc with (((((((((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9) | h10) | h11) | h12) |
      h13) | h14) | h15
    · rcases mem_topo P (qc x) (qm x) x h1 with hm | ht
      · have : tuple12OfVec (F := F) x ∈ A1 := by
          show tuple12OfVec (F := F) x ∈ cyl12 _
          rw [mem_cyl12]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← e1]
          exact hm
        exact Finset.mem_union.mpr (Or.inl this)
      · have : tuple12OfVec (F := F) x ∈ A1t := by
          show _ ∈ vecSet _
          rw [mem_vecSet, hvx]; simpa [cylinder] using ht
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl this)))
    · have : tuple12OfVec (F := F) x ∈ A2 := by
        show _ ∈ vecSet _
        rw [mem_vecSet, hvx]; simpa [cylinder₂] using mem_summand2 P (qc x) (qm x) x h2
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl this)))))
    · have : tuple12OfVec (F := F) x ∈ A3 := by
        show _ ∈ cyl12 _
        rw [mem_cyl12, mem_liftTimestampFailure_iff] at h3 ⊢
        rw [← e3]; exact h3
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl this)))))))
    · have : tuple12OfVec (F := F) x ∈ A4 := by
        show _ ∈ vecSet _
        rw [mem_vecSet, hvx]; simpa [cylinder₂] using mem_summand4 P (qm x) x h4
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl this)))))))))
    · rcases mem_summand5 P (qc x) x h5 with h | h
      · have : tuple12OfVec (F := F) x ∈ A5a := by
          show _ ∈ vecSet _
          rw [mem_vecSet, hvx]; simpa [cylinder] using h
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl this)))))))))))
      · have : tuple12OfVec (F := F) x ∈ A5g := by
          show _ ∈ vecSet _
          rw [mem_vecSet, hvx]; simpa [cylinder] using h
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl this)))))))))))))
    · have : tuple12OfVec (F := F) x ∈ A6 := by
        show _ ∈ cyl12 _
        rw [← e6]; exact h6
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl this)))))))))))))))
    · have : tuple12OfVec (F := F) x ∈ A7 := by
        show _ ∈ liftWalkWFailure _
        rw [← e7]; exact h7
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl this)))))))))))))))))
    · have : tuple12OfVec (F := F) x ∈ A8 := by
        show _ ∈ vecSet _
        rw [mem_vecSet, hvx]; simpa [cylinder] using mem_summand8 P (qc x) x h8
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl this)))))))))))))))))))
    · have : tuple12OfVec (F := F) x ∈ A9 := by
        show _ ∈ vecSet _
        rw [mem_vecSet, hvx]; simpa [cylinder] using mem_summand9 P (qm x) x h9
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl this)))))))))))))))))))))
    · have : tuple12OfVec (F := F) x ∈ A10 := by
        show _ ∈ vecSet _
        rw [mem_vecSet, hvx]; simpa [cylinder] using mem_summand10 P (qm x) x h10
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl this)))))))))))))))))))))))
    · have : tuple12OfVec (F := F) x ∈ A11 := by
        show _ ∈ cyl12 _
        rw [← e11]; exact h11
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl this)))))))))))))))))))))))))
    · have : tuple12OfVec (F := F) x ∈ A12 := by
        show _ ∈ cyl12 _
        rw [← e12]; exact h12
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl this)))))))))))))))))))))))))))
    · have : tuple12OfVec (F := F) x ∈ A13 := by
        show _ ∈ cyl12 _
        rw [← e13]; exact h13
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl this)))))))))))))))))))))))))))))
    · have : tuple12OfVec (F := F) x ∈ A14 ∪ A15 := Finset.mem_union.mpr (Or.inl h14)
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (this))))))))))))))))))))))))))))))
    · have : tuple12OfVec (F := F) x ∈ A14 ∪ A15 := Finset.mem_union.mpr (Or.inr h15)
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr (this))))))))))))))))))))))))))))))
  have hA1 : A1.card ≤ Fintype.card K * (Fintype.card K ^ 10 *
      (1 + (3 + 19 * N P) * (2 * P.optimized.Λ - 1) + axisUniformWorkload (N P) (M P) +
        sizeWindowRootBound P.optimized.Λ)) :=
    cyl12_card_le _ _ (card_jointLam_le _ _ (fun l => m1Part_card_le P _ _ l))
  have hA1t : A1t.card ≤ Fintype.card K ^ (12 - 1) * (24 * N P + 8 * M P) := by
    rw [card_vecSet]
    exact cylinder_card_le 1 _ not_mem_coins_topo _ (summand1_topo_readsOn12 P hC hM) _
      (fun x => badTopo_card P _ _ x)
  have hA2 : A2.card ≤ Fintype.card K ^ (12 - 2) * P.hostileIOWork := by
    rw [card_vecSet]
    exact cylinder₂_card_le 4 5 (by decide) _ not_mem_coins_2.1 not_mem_coins_2.2 _
      (summand2_readsOn12 P hC hM) _ (fun x => bad2_card P _ _ x)
  have hA3 : A3.card ≤ Fintype.card K * (Fintype.card K ^ 10 *
      OptimizedHostileTimestamps.timestampCollisionBound (3 * N P)) := by
    refine cyl12_card_le _ _ ?_
    rw [card_liftTimestampFailure, mul_comm]
    exact Nat.mul_le_mul_left _
      ((OptimizedHostileTimestamps.TimestampCollisionEvent_card_le_bound _).trans
        (OptimizedHostileTimestamps.timestampCollisionBound_mono (P.hostileRequests_length_le _)))
  have hA4 : A4.card ≤ Fintype.card K ^ (12 - 2) *
      (FiniteIO.ioFailureUnionBound 10 (M P) (M P) (Fintype.card K) + Fintype.card K * M P) := by
    rw [card_vecSet]
    exact cylinder₂_card_le 4 9 (by decide) _ not_mem_coins_4.1 not_mem_coins_4.2 _
      (summand4_readsOn12 P hC hM) _ (fun x => bad4_card P _)
  have hA5a : A5a.card ≤ Fintype.card K ^ (12 - 1) * ComputeWalkRootEvents.walkAlphaRootBound (N P) := by
    rw [card_vecSet]
    exact cylinder_card_le 0 _ not_mem_coins_5a _ (summand5a_readsOn12 P hC hM) _
      (fun x => bad5a_card P _ x)
  have hA5g : A5g.card ≤ Fintype.card K ^ (12 - 1) * ComputeWalkRootEvents.walkRootGammaBound := by
    rw [card_vecSet]
    exact cylinder_card_le 1 _ not_mem_coins_5g _ (summand5g_readsOn12 P hC hM) _
      (fun x => bad5g_card P _ x)
  have hA6 : A6.card ≤ Fintype.card K * (Fintype.card K ^ 10 *
      WalkTilingEvents.computeTilingBound (N P)) :=
    cyl12_card_le _ _ (liftP8_card_le (F := F) _ _ (P.computeTilingEventOf_card_le _))
  have hA7 : A7.card ≤ Fintype.card K * (Fintype.card K ^ 10 *
      WalkTilingEvents.memoryTilingBound (M P)) :=
    liftWalkW_card_le _ _ (P.memoryTilingEventOf_card_le _)
  have hA8 : A8.card ≤ Fintype.card K ^ (12 - 1) *
      WalkPrefixGammaEvents.computePrefixGammaBound (N P) := by
    rw [card_vecSet]
    exact cylinder_card_le 1 _ not_mem_coins_γ _ (summand8_readsOn12 P hC hM) _
      (fun x => bad8_card P _)
  have hA9 : A9.card ≤ Fintype.card K ^ (12 - 1) *
      WalkPrefixGammaEvents.memoryPrefixGammaBound (M P) := by
    rw [card_vecSet]
    exact cylinder_card_le 1 _ not_mem_coins_γ _ (summand9_readsOn12 P hC hM) _
      (fun x => bad9_card P _)
  have hA10 : A10.card ≤ Fintype.card K ^ (12 - 1) *
      WalkForestPrefixAlphaEvents.memoryForestAlphaBound (M P) := by
    rw [card_vecSet]
    exact cylinder_card_le 11 _ not_mem_coins_10 _ (summand10_readsOn12 P hC hM) _
      (fun x => bad10_card P _ x)
  have hA11 : A11.card ≤ Fintype.card K * (Fintype.card K ^ 10 * formRUniformWorkload P.strategy) :=
    cyl12_card_le _ _ (P.decodedLambdaEventOf_card_le _ _)
  have hA12 : A12.card ≤ Fintype.card K * (Fintype.card K ^ 10 * (M P * (2 * Λg P - 1))) :=
    cyl12_card_le _ _ (liftP8_card_le (F := F) _ _ (reqPairEv_card_le P _ _))
  have hA13 : A13.card ≤ Fintype.card K * (Fintype.card K ^ 10 * (2 * Λg P - 1)) :=
    cyl12_card_le _ _ (liftP8_card_le (F := F) _ _ (rootResultEv_card_le P _ _))
  have hA14 : A14.card ≤ Fintype.card K * (Fintype.card K ^ 10 * 1) :=
    cyl12_card_le _ _ (liftP8_card_le (F := F) _ _ (alphaZeroEvent_card_le (K := K)))
  have hA15 : A15.card ≤ Fintype.card K ^ 11 * OptimizedHostileTimestamps.timestampCollisionBound (M P) :=
    Pkg12.summand15_card_le P
  have hA1415 : (A14 ∪ A15).card ≤ Fintype.card K * (Fintype.card K ^ 10 * 1) +
      Fintype.card K ^ 11 * OptimizedHostileTimestamps.timestampCollisionBound (M P) :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add hA14 hA15)
  refine (Finset.card_le_card hsub).trans (((Finset.card_union_le _ _).trans (Nat.add_le_add hA1 ((Finset.card_union_le _ _).trans (Nat.add_le_add hA1t ((Finset.card_union_le _ _).trans (Nat.add_le_add hA2 ((Finset.card_union_le _ _).trans (Nat.add_le_add hA3 ((Finset.card_union_le _ _).trans (Nat.add_le_add hA4 ((Finset.card_union_le _ _).trans (Nat.add_le_add hA5a ((Finset.card_union_le _ _).trans (Nat.add_le_add hA5g ((Finset.card_union_le _ _).trans (Nat.add_le_add hA6 ((Finset.card_union_le _ _).trans (Nat.add_le_add hA7 ((Finset.card_union_le _ _).trans (Nat.add_le_add hA8 ((Finset.card_union_le _ _).trans (Nat.add_le_add hA9 ((Finset.card_union_le _ _).trans (Nat.add_le_add hA10 ((Finset.card_union_le _ _).trans (Nat.add_le_add hA11 ((Finset.card_union_le _ _).trans (Nat.add_le_add hA12 ((Finset.card_union_le _ _).trans (Nat.add_le_add hA13 (hA1415))))))))))))))))))))))))))))))).trans (le_of_eq ?_))
  simp only [bound15, optimizedHostileProductionFailureCardBound15,
    optimizedHostileProductionFailureCardBound12,
    optimizedHostileProductionFailureCardBound, optimizedTrimmedProductionFailureCardBound,
    pricedWalkWork, workloadEv, p8WorkEv, ComputeWalkRootEvents.walkRootBound, N, M, Λg,
    OptimizedFullStrictNockVMROMPackage.hostileIOWork]
  norm_num
  ring

/-! ## 6. **H2.2, the probability form** and the staged false-acceptance bound -/

open Classical in
/-- **The staged consumed probability bound**: normalised over `|𝕂|¹²`, the consumed event along a
staged strategy has probability at most `optimizedHostileProductionFailureProbabilityBound15` —
the consumed fixed-trace bound function plus summand 15's `(1 + M(M−1)/2)/|𝕂|`
(`cardBound15_normalised`). -/
theorem staged_consumed_probability_le
    (Qc : OptimizedProductionChallengeTuple12 K F → Fin 309 → F[X])
    (Qm : OptimizedProductionChallengeTuple12 K F → Fin P.memoryChip.rap.w → F[X])
    (hst : StagedTraces12 P Qc Qm) :
    ((Finset.univ.filter fun c => c ∈ consumedFailureEvent309 P (Qc c) (Qm c)).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple12 K F) ≤
      optimizedHostileProductionFailureProbabilityBound15 (Fintype.card K) (Fintype.card F)
        (workloadEv P P.optimized.Λ) P.hostileIOWork (N P) (M P) := by
  rw [card_optimizedProductionChallengeTuple12, ← cardBound15_normalised _ _ _ _ _ _ Fintype.card_pos]
  have hcast : ((Finset.univ.filter fun c => c ∈ consumedFailureEvent309 P (Qc c) (Qm c)).card : ℚ) ≤
      (bound15 P : ℚ) := by exact_mod_cast staged_consumed_card_le P Qc Qm hst
  push_cast
  exact div_le_div_of_nonneg_right hcast (by positivity)

open Classical in
/-- **The staged false-acceptance bound at the parallel package** (design §5's
`staged_false_acceptance_bound`, at `repartitionedChronology`).  For every staged prover strategy —
each committed column a function only of the coins sampled before its block, B0 constant — the
fraction of the twelve coins at which the strategy's own traces are accepted by the parallel
chips while the target fails is at most the fifteen-summand bound function (the consumed
fixed-trace function plus `(1 + M(M−1)/2)/|𝕂|`; it is NOT the same function as the fixed-trace
statement's).

The target and its acceptance-to-target implication `hAT` are the statement's
`acceptance_to_target` shape at the parallel package; they are a hypothesis here (see the module
docstring).  Nothing here is about `deployedChronology`. -/
theorem staged_false_acceptance_bound12
    (Target : (Fin 309 → F[X]) → (Fin P.memoryChip.rap.w → F[X]) →
      OptimizedProductionChallengeTuple12 K F → Prop)
    (hAT : ∀ Qc Qm c, AcceptanceAt309 P Qc Qm c → c ∉ consumedFailureEvent309 P Qc Qm →
      Target Qc Qm c)
    (Qc : OptimizedProductionChallengeTuple12 K F → Fin 309 → F[X])
    (Qm : OptimizedProductionChallengeTuple12 K F → Fin P.memoryChip.rap.w → F[X])
    (hst : StagedTraces12 P Qc Qm) :
    ((Finset.univ.filter fun c =>
        AcceptanceAt309 P (Qc c) (Qm c) c ∧ ¬ Target (Qc c) (Qm c) c).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple12 K F) ≤
      optimizedHostileProductionFailureProbabilityBound15 (Fintype.card K) (Fintype.card F)
        (workloadEv P P.optimized.Λ)
        (FiniteIO.ioFailureUnionBound 10 (3 * P.optimized.family.problem.cfg.compRows)
          P.optimized.family.problem.cfg.memRows (Fintype.card K))
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows := by
  have hsub : (Finset.univ.filter fun c =>
        AcceptanceAt309 P (Qc c) (Qm c) c ∧ ¬ Target (Qc c) (Qm c) c) ⊆
      Finset.univ.filter fun c => c ∈ consumedFailureEvent309 P (Qc c) (Qm c) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    by_contra hn
    exact hc.2 (hAT _ _ c hc.1 hn)
  refine le_trans ?_ (staged_consumed_probability_le P Qc Qm hst)
  have hcard : ((Finset.univ.filter fun c =>
        AcceptanceAt309 P (Qc c) (Qm c) c ∧ ¬ Target (Qc c) (Qm c) c).card : ℚ) ≤
      ((Finset.univ.filter fun c => c ∈ consumedFailureEvent309 P (Qc c) (Qm c)).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact div_le_div_of_nonneg_right hcard (by positivity)

open Classical in
/-- **The fixed-trace corollary** (`complete_false_acceptance_bound_of_staged`, C6.4): a fixed
trace pair is the constant strategy, which is staged (`staged12_const`). -/
theorem complete_false_acceptance_bound_of_staged12
    (Target : (Fin 309 → F[X]) → (Fin P.memoryChip.rap.w → F[X]) →
      OptimizedProductionChallengeTuple12 K F → Prop)
    (hAT : ∀ Qc Qm c, AcceptanceAt309 P Qc Qm c → c ∉ consumedFailureEvent309 P Qc Qm →
      Target Qc Qm c)
    (qc : Fin 309 → F[X]) (qm : Fin P.memoryChip.rap.w → F[X]) :
    ((Finset.univ.filter fun c => AcceptanceAt309 P qc qm c ∧ ¬ Target qc qm c).card : ℚ) /
        Fintype.card (OptimizedProductionChallengeTuple12 K F) ≤
      optimizedHostileProductionFailureProbabilityBound15 (Fintype.card K) (Fintype.card F)
        (workloadEv P P.optimized.Λ)
        (FiniteIO.ioFailureUnionBound 10 (3 * P.optimized.family.problem.cfg.compRows)
          P.optimized.family.problem.cfg.memRows (Fintype.card K))
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows :=
  staged_false_acceptance_bound12 P Target hAT (fun _ => qc) (fun _ => qm)
    ⟨staged12_const _ qc, staged12_const _ qm⟩


/-! ## 7. -/

/-- The M1 coins `(αM, z, a, b, c, λ)` of a tuple, as the coin vector cut to message M1 (every
other coordinate `0`). -/
def m1Coins (c : OptimizedProductionChallengeTuple12 K F) : Fin 12 → K :=
  fun i => if (repartitionedChronology.sampledAfter i : ℕ) < 1 then landedVec12 c i else 0

/-- **The strategy form of one committed table**: a fixed base block, a block-1 part that is a
function of the M1 coins only, and a block-2 part that is any function of all twelve coins. -/
def StrategyFormOf {ι : Type*} (colRound : ι → ℕ)
    (Q : OptimizedProductionChallengeTuple12 K F → ι → F[X]) : Prop :=
  ∃ (b0 : ι → F[X]) (b1 : (Fin 12 → K) → ι → F[X])
    (b2 : OptimizedProductionChallengeTuple12 K F → ι → F[X]),
    ∀ c j, Q c j = if colRound j = 0 then b0 j else if colRound j = 1 then b1 (m1Coins c) j else b2 c j

theorem m1Coins_agree (c c' : OptimizedProductionChallengeTuple12 K F)
    (h : ∀ i : Fin 12, (repartitionedChronology.sampledAfter i : ℕ) < 1 →
      landedVec12 c i = landedVec12 c' i) :
    m1Coins c = m1Coins c' := by
  funext i
  unfold m1Coins
  split_ifs with hi
  · exact h i hi
  · rfl

/-- **Strategy form ⇒ staged.** -/
theorem staged_of_strategyForm {ι : Type*} {colRound : ι → ℕ} (hr : ∀ j, colRound j ≤ 2)
    {Q : OptimizedProductionChallengeTuple12 K F → ι → F[X]} (h : StrategyFormOf colRound Q) :
    Staged12 colRound Q := by
  obtain ⟨b0, b1, b2, hQ⟩ := h
  intro j c c' hc
  rw [hQ c j, hQ c' j]
  by_cases h0 : colRound j = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : colRound j = 1
    · rw [if_pos h1, if_pos h1, m1Coins_agree c c' (fun i hi => hc i (by rw [h1]; exact hi))]
    · rw [if_neg h1, if_neg h1]
      have hle : ∀ i : Fin 12, (repartitionedChronology.sampledAfter i : ℕ) ≤ 1 := by decide
      have h2 : colRound j = 2 := by have := hr j; omega
      have : c = c' := (tuple12VecEquiv (K := K) (F := F)).injective (funext fun i =>
        hc i (by have := hle i; omega))
      rw [this]

/-- **Staged ⇒ strategy form**: B0 is the value at any tuple, B1 is the value at the tuple of the
cut M1 vector, B2 is the strategy itself. -/
theorem strategyForm_of_staged {ι : Type*} {colRound : ι → ℕ}
    {Q : OptimizedProductionChallengeTuple12 K F → ι → F[X]} (h : Staged12 colRound Q) :
    StrategyFormOf colRound Q := by
  refine ⟨Q (tuple12OfVec 0), fun m => Q (tuple12OfVec m), Q, fun c j => ?_⟩
  by_cases h0 : colRound j = 0
  · rw [if_pos h0]
    exact h j c _ (fun i hi => absurd hi (by omega))
  · rw [if_neg h0]
    by_cases h1 : colRound j = 1
    · rw [if_pos h1]
      refine h j c _ (fun i hi => ?_)
      rw [landedVec12_tuple12OfVec]
      unfold m1Coins
      rw [if_pos (by omega)]
    · rw [if_neg h1]

theorem newMemoryColRound_le_two (j : ℕ) : newMemoryColRound j ≤ 2 := by
  unfold newMemoryColRound newMemoryRoleRound DeployedStaging.memoryRoleRound
  split_ifs <;> omega

theorem newComputeColRound_le_two (j : ℕ) : newComputeColRound j ≤ 2 := by
  unfold newComputeColRound
  rw [newComputeRoleRound_eq]
  split_ifs <;> omega

/-- **The strategy form, both tables, is equivalent to `StagedTraces12`.** -/
theorem strategy_staged (Qc : OptimizedProductionChallengeTuple12 K F → Fin 309 → F[X])
    (Qm : OptimizedProductionChallengeTuple12 K F → Fin P.memoryChip.rap.w → F[X]) :
    (StrategyFormOf (fun j : Fin 309 => newComputeColRound j) Qc ∧
        StrategyFormOf (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) Qm) ↔
      StagedTraces12 P Qc Qm := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨staged_of_strategyForm (fun j : Fin 309 => newComputeColRound_le_two (j : ℕ)) h1,
      staged_of_strategyForm (fun j : Fin P.memoryChip.rap.w => newMemoryColRound_le_two (j : ℕ)) h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨strategyForm_of_staged h1, strategyForm_of_staged h2⟩

end Package

end

end Nock.NockVMROM.Thm54.PartAStaged
