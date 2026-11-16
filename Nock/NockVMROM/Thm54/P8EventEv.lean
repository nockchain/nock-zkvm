/-
  Nock/NockVMROM/Thm54/P8EventEv.lean

  **H1.5b Part 2b-event — the P8 slot at the event strategy: envelope-guarded, trace-uniform,
  premise-free**.

  * **§A — the envelope-guarded axis share** (the 30th/32nd λ-event pattern: the guard is inside
    the bad set).  `envelopeRootAlphas E lmb i` prices root `i`'s guarded bad `αM` set only when
    the committed axis polynomial's degree is within the envelope `E' = 3·compRows + 3`; its card is
    `≤ E'` with no premise, so the union over the `kMem ≤ memRows` roots is `≤ M·(3N + 3)` —
    `axisUniformWorkload N M`, a function of the traces' row counts only, which no hostile
    `reqIdx` can inflate (change 1).  `envelopeAxisFailureEvent T lmb ⊆ guardedAxisFailureEvent
    T lmb`; the two agree when every root polynomial is within the envelope (the honest window).
  * **§B — the guarded census and size-window twins** of `CombinedSkeletonCensus.census` /
    `SizeWindowFailure`: `guardedCensusEv K S Λ := guardedCensus Λ (combinedSkeletonPairs K S)`
    (card `≤ (3 + 19·R_S)(2Λ − 1)` with no premise) and `guardedSizeWindowFailure S Λ` (only
    nouns with `≤ Λ` leaves are priced; card `≤ sizeWindowRootBound Λ` with no premise).  Each
    coincides with the proof-carrying original when the original's premise holds.
  * **§C — the event union** `evFailureUnion T Λ lmb` (zero seed ∪ guarded census collisions ∪
    topology ∪ envelope axis ∪ guarded size windows) with its trace-uniform card
    `p8WorkEv N M Λ · |𝕂|³` at every strategy whose templates have `≤ N` compute / `≤ M` memory rows
    and whose skeleton has `≤ N` compute rows.
  * **§D — at the event strategy**: `evFailureUnion (strategyOfTracesEv O Qc Qm tag) Λ lmb` has
    card `≤ p8WorkEv N M Λ · |𝕂|³` at EVERY `(Qc, Qm)`, no premise (rule 8(b)): the templates'
    row counts are the traces' by `rfl`, the skeleton's by `ReconTreeSize`.
  The axis tree ignores the placeholder's
    challenge record and `λ` (`templateAxisTree_mapNTree`); the topology payloads ignore the
    compute inputs record and the memory challenge record (`computeSlotBadGammas_mapNTree`,
    `memorySlotBadGammas_mapNTree`).

  -- the paper (collision counting), :1413-1431 (timestamps / axis), :1450
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesEv

namespace Nock.NockVMROM.Thm54.P8EventEv

open scoped Polynomial BigOperators Classical
open Polynomial
open Nock
open Nock.Walk
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.ReconTreeSize

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 800000

noncomputable section

/-! ## §A  The envelope-guarded axis share -/

section Envelope

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-- The envelope degree of a config template: `3·compRows + 3` (`DecodedLambdaEvent.decodedEnvelopeDeg`
at the template's own row count; the honest record exponents are `≤ 3N`). -/
def envelopeDeg (T : ExactConfigTemplate F K) : ℕ := 3 * T.compRows + 3

/-- **Root `i`'s envelope-guarded bad `αM` set**: the checker-guarded set when the committed axis
polynomial's degree is within the envelope, else nothing. -/
def envelopeRootAlphas {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (lmb : K)
    (i : Fin T.kMem) : Finset K :=
  if (templateAxisPolynomial E i).natDegree ≤ envelopeDeg T then verifierGuardedRootAlphas E lmb i
  else ∅

theorem envelopeRootAlphas_subset {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (lmb : K) (i : Fin T.kMem) :
    envelopeRootAlphas E lmb i ⊆ verifierGuardedRootAlphas E lmb i := by
  unfold envelopeRootAlphas
  split_ifs
  · exact Finset.Subset.refl _
  · exact Finset.empty_subset _

/-- Per root, `≤ E'` with no premise. -/
theorem envelopeRootAlphas_card_le (h2 : (2 : K) ≠ 0) {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (lmb : K) (i : Fin T.kMem) :
    (envelopeRootAlphas E lmb i).card ≤ envelopeDeg T := by
  unfold envelopeRootAlphas
  split_ifs with hdeg
  · exact Nat.le_trans (verifierGuardedRootAlphas_card_le h2 E lmb i) hdeg
  · simp

def envelopeRootUnion {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (lmb : K) :
    Finset K :=
  (Finset.univ : Finset (Fin T.kMem)).biUnion (envelopeRootAlphas E lmb)

theorem envelopeRootUnion_subset {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (lmb : K) : envelopeRootUnion E lmb ⊆ verifierGuardedRootUnion E lmb := by
  intro α hα
  simp only [envelopeRootUnion, Finset.mem_biUnion, Finset.mem_univ, true_and] at hα
  obtain ⟨i, hi⟩ := hα
  simp only [verifierGuardedRootUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨i, envelopeRootAlphas_subset E lmb i hi⟩

/-- Every template has at least one node per root: `kMem ≤ memRows`. -/
theorem kMem_le_memRows {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) :
    T.kMem ≤ T.memRows := by
  rw [← E.memory_root_count, ← E.memory_bfs_length, bfsForest_length]
  unfold totalSize
  have hone : ∀ l : List ℕ, (∀ x ∈ l, 1 ≤ x) → l.length ≤ l.sum := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons x xs ih =>
        intro hx
        simp only [List.length_cons, List.sum_cons]
        have h1 := ih fun y hy => hx y (by simp [hy])
        have h2 := hx x (by simp)
        omega
  have hlen : (E.memoryForest.map NTree.size).length = E.memoryForest.length := by simp
  rw [← hlen]
  apply hone
  intro x hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
  cases t; simp [NTree.size]

/-- **Per seed, `≤ memRows · E'` with no premise**: the trace-uniform axis share. -/
theorem envelopeRootUnion_card_le (h2 : (2 : K) ≠ 0) {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (lmb : K) :
    (envelopeRootUnion E lmb).card ≤ T.memRows * envelopeDeg T := by
  calc (envelopeRootUnion E lmb).card
      ≤ ∑ i : Fin T.kMem, (envelopeRootAlphas E lmb i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin T.kMem, envelopeDeg T :=
        Finset.sum_le_sum fun i _ => envelopeRootAlphas_card_le h2 E lmb i
    _ = T.kMem * envelopeDeg T := by simp
    _ ≤ T.memRows * envelopeDeg T := Nat.mul_le_mul_right _ (kMem_le_memRows E)

/-- When every root polynomial is within the envelope the guard is a no-op. -/
theorem envelopeRootUnion_eq_of_deg_le {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (lmb : K)
    (hdeg : ∀ i : Fin T.kMem, (templateAxisPolynomial E i).natDegree ≤ envelopeDeg T) :
    envelopeRootUnion E lmb = verifierGuardedRootUnion E lmb := by
  unfold envelopeRootUnion verifierGuardedRootUnion
  congr 1
  funext i
  unfold envelopeRootAlphas
  rw [if_pos (hdeg i)]

/-- The strategy-level `(αM, z)` pairs, the 30th's `guardedSeedAxisPairs` with the envelope guard. -/
def envelopeSeedAxisPairs (T : ProductionP8Containment.ProductionStrategy F K) (lmb : K) : Finset (K × K) :=
  (Finset.univ : Finset K).biUnion fun z =>
    if hz : z ≠ 0 then
      (envelopeRootUnion (committedTemplate T.verifier z hz) lmb).map (seedAlphaEmbedding z)
    else ∅

@[simp] theorem mem_envelopeSeedAxisPairs_iff (T : ProductionP8Containment.ProductionStrategy F K) (lmb α z : K) :
    (α, z) ∈ envelopeSeedAxisPairs T lmb ↔
      ∃ hz : z ≠ 0, α ∈ envelopeRootUnion (committedTemplate T.verifier z hz) lmb := by
  simp only [envelopeSeedAxisPairs, Finset.mem_biUnion, Finset.mem_univ, true_and]
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

/-- **The envelope-guarded axis failure event** on `JointCoins`: the first two coordinates free,
`(alphaM, z)` in the envelope-guarded fibres. -/
def envelopeAxisFailureEvent (T : ProductionP8Containment.ProductionStrategy F K) (lmb : K) : Finset (JointCoins K) :=
  (Finset.univ : Finset (K × K)) ×ˢ envelopeSeedAxisPairs T lmb

@[simp] theorem mem_envelopeAxisFailureEvent_iff (T : ProductionP8Containment.ProductionStrategy F K) (lmb : K)
    (ω : JointCoins K) :
    ω ∈ envelopeAxisFailureEvent T lmb ↔
      ∃ hz : nprSeed ω ≠ 0,
        alphaM ω ∈ envelopeRootUnion (committedTemplate T.verifier (nprSeed ω) hz) lmb := by
  rcases ω with ⟨cg, ⟨α, z⟩⟩
  simp [envelopeAxisFailureEvent, mem_envelopeSeedAxisPairs_iff, nprSeed, Thm54.alphaM]

theorem envelopeAxisFailureEvent_subset (T : ProductionP8Containment.ProductionStrategy F K) (lmb : K) :
    envelopeAxisFailureEvent T lmb ⊆ guardedAxisFailureEvent T lmb := by
  intro ω hω
  rw [mem_envelopeAxisFailureEvent_iff] at hω
  rw [mem_guardedAxisFailureEvent_iff]
  obtain ⟨hz, hα⟩ := hω
  exact ⟨hz, envelopeRootUnion_subset _ lmb hα⟩

/-- **The trace-uniform axis workload**: `M·(3N + 3)`, a function of the row counts only. -/
def axisUniformWorkload (N M : ℕ) : ℕ := M * (3 * N + 3)

/-- The config template committed at seed `z`. -/
abbrev seedConfig (T : ProductionP8Containment.ProductionStrategy F K) (z : K) (hz : z ≠ 0) : ExactConfigTemplate F K :=
  (T.verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate

/-- **THE CARD LEMMA OF THE AXIS SHARE: `≤ M·(3N + 3)·|𝕂|³` with no premise beyond the row
counts of the committed templates** (every seed's template has `≤ N` compute and `≤ M` memory
rows; at the built strategies these are the traces' row counts by `rfl`). -/
theorem envelopeAxisFailureEvent_card_le (h2 : (2 : K) ≠ 0) (T : ProductionP8Containment.ProductionStrategy F K)
    (lmb : K) (N M : ℕ)
    (hN : ∀ z (hz : z ≠ 0), (seedConfig T z hz).compRows ≤ N)
    (hM : ∀ z (hz : z ≠ 0), (seedConfig T z hz).memRows ≤ M) :
    (envelopeAxisFailureEvent T lmb).card ≤ axisUniformWorkload N M * Fintype.card K ^ 3 := by
  have hpairs : (envelopeSeedAxisPairs T lmb).card ≤ axisUniformWorkload N M * Fintype.card K := by
    calc (envelopeSeedAxisPairs T lmb).card
        ≤ ∑ z : K, (if hz : z ≠ 0 then
            (envelopeRootUnion (committedTemplate T.verifier z hz) lmb).map (seedAlphaEmbedding z)
          else ∅).card := Finset.card_biUnion_le
      _ ≤ ∑ _z : K, axisUniformWorkload N M := by
          apply Finset.sum_le_sum
          intro z _
          split
          · rename_i hz
            rw [Finset.card_map]
            refine (envelopeRootUnion_card_le h2 _ lmb).trans ?_
            unfold axisUniformWorkload envelopeDeg
            have h1 : (T.verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate.compRows ≤ N :=
              hN z hz
            have h2' : (T.verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate.memRows ≤ M :=
              hM z hz
            exact Nat.mul_le_mul h2' (by omega)
          · simp
      _ = axisUniformWorkload N M * Fintype.card K := by simp [Nat.mul_comm]
  simp only [envelopeAxisFailureEvent, Finset.card_product, Finset.card_univ, Fintype.card_prod]
  calc Fintype.card K * Fintype.card K * (envelopeSeedAxisPairs T lmb).card
      ≤ Fintype.card K * Fintype.card K * (axisUniformWorkload N M * Fintype.card K) :=
        Nat.mul_le_mul_left _ hpairs
    _ = axisUniformWorkload N M * Fintype.card K ^ 3 := by ring

end Envelope

/-! ## §B  The guarded census and size-window twins -/

section Guarded

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- **The guarded census of a bare skeleton**: `PreSeedCensus.guardedCensus` of the combined P8 /
edge pair list — every pair with `≤ Λ` leaves on both sides, no proof field. -/
def guardedCensusEv (K : Type) [Field K] (S : SemanticSkeleton) (Λ : ℕ) : ComparisonCensus Λ :=
  PreSeedCensus.guardedCensus Λ (EdgeComparisonCensus.combinedSkeletonPairs K S)

theorem guardedCensusEv_count_le (S : SemanticSkeleton) (Λ : ℕ) :
    (guardedCensusEv K S Λ).count ≤ 3 + 19 * (computeSkeletonRows S).length := by
  show (PreSeedCensus.guardedPairs Λ (EdgeComparisonCensus.combinedSkeletonPairs K S)).length ≤ _
  refine (PreSeedCensus.guardedPairs_length_le _ _).trans ?_
  unfold EdgeComparisonCensus.combinedSkeletonPairs
  rw [List.length_append]
  have hp : (BoundSemanticTrace.skeletonPairs K S).length ≤
      3 + 10 * (computeSkeletonRows S).length := by
    unfold BoundSemanticTrace.skeletonPairs
    rw [List.length_append, List.length_map]
    have := P8Census.BoundP8Census.skeletonComparisonCensus_length_le (K := K) S
    simp only [List.length_cons, List.length_nil]
    omega
  have he := EdgeComparisonCensus.edgePairs_length_le S.computeTree
  have hrows : (computeSkeletonRows S).length = (bfsForest [S.computeTree]).length := by
    simp [computeSkeletonRows]
  rw [hrows] at hp ⊢
  omega

/-- Card of the guarded census's collision event: `≤ (3 + 19·R_S)(2Λ − 1)·|𝕂|³`, no premise. -/
theorem collisionFailureEvent_guardedCensusEv_card_le (S : SemanticSkeleton) (Λ : ℕ) :
    (collisionFailureEvent (K := K) (guardedCensusEv K S Λ)).card ≤
      ((3 + 19 * (computeSkeletonRows S).length) * (2 * Λ - 1)) * Fintype.card K ^ 3 :=
  (collisionFailureEvent_card_le _).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (guardedCensusEv_count_le S Λ)))

/-- When the proof-carrying census exists, the guard keeps every pair. -/
theorem guardedPairs_eq_of_census {S : SemanticSkeleton} {Λ : ℕ}
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K S Λ) :
    PreSeedCensus.guardedPairs Λ (EdgeComparisonCensus.combinedSkeletonPairs K S) =
      EdgeComparisonCensus.combinedSkeletonPairs K S := by
  unfold PreSeedCensus.guardedPairs
  rw [List.filter_eq_self]
  intro pair hp
  rw [decide_eq_true_eq]
  unfold EdgeComparisonCensus.combinedSkeletonPairs at hp
  rw [List.mem_append] at hp
  exact hp.elim (C.p8.leaves_bounded pair) (C.edges.leaves_bounded pair)

/-- The guarded census's bad seeds are the proof-carrying census's when the latter exists. -/
theorem guardedCensusEv_badSeeds_eq {S : SemanticSkeleton} {Λ : ℕ}
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K S Λ) :
    (guardedCensusEv K S Λ).badSeeds (K := K) = C.census.badSeeds := by
  ext z
  show z ∈ PreSeedCensus.pairBadSeeds Λ (EdgeComparisonCensus.combinedSkeletonPairs K S) ↔ _
  rw [PreSeedCensus.mem_pairBadSeeds_iff, ComparisonCensus.mem_badSeeds_iff]
  constructor
  · rintro ⟨pair, hp, -, -, hsep⟩
    unfold EdgeComparisonCensus.combinedSkeletonPairs at hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨i, hi⟩ := C.p8_pair_lookup hp
      exact ⟨i, by rw [hi]; exact hsep⟩
    · obtain ⟨i, hi⟩ := C.edge_pair_lookup hp
      exact ⟨i, by rw [hi]; exact hsep⟩
  · rintro ⟨i, hi⟩
    refine ⟨C.census.pair i, ?_, (C.census.leaves_bounded i).1, (C.census.leaves_bounded i).2, hi⟩
    show (EdgeComparisonCensus.combinedSkeletonPairs K S).get _ ∈ _
    exact List.get_mem _ _

/-- **The guarded size-window seeds**: nonzero `z` at which some required noun WITH `≤ Λ` leaves
lacks its window (the guard is inside the set). -/
def guardedSizeWindowSeeds (S : SemanticSkeleton) (Λ : ℕ) : Finset K :=
  Finset.univ.filter fun z =>
    z ≠ 0 ∧ ∃ n ∈ skeletonSizeWindowNouns S, n.leaves ≤ Λ ∧ ¬ OpcodeSemantics.SizeWindow z n

@[simp] theorem mem_guardedSizeWindowSeeds_iff (S : SemanticSkeleton) (Λ : ℕ) (z : K) :
    z ∈ guardedSizeWindowSeeds (K := K) S Λ ↔
      z ≠ 0 ∧ ∃ n ∈ skeletonSizeWindowNouns S, n.leaves ≤ Λ ∧ ¬ OpcodeSemantics.SizeWindow z n := by
  simp [guardedSizeWindowSeeds]

/-- The guarded size-window event on `JointCoins`. -/
def guardedSizeWindowFailure (S : SemanticSkeleton) (Λ : ℕ) : Finset (JointCoins K) :=
  liftSeed (guardedSizeWindowSeeds (K := K) S Λ)

theorem guardedSizeWindowFailure_subset (S : SemanticSkeleton) (Λ : ℕ) :
    guardedSizeWindowFailure (K := K) S Λ ⊆ SizeWindowFailure S := by
  intro ω hω
  rw [guardedSizeWindowFailure, mem_liftSeed_iff, mem_guardedSizeWindowSeeds_iff] at hω
  rw [mem_SizeWindowFailure_iff]
  obtain ⟨hz, n, hn, -, hw⟩ := hω
  exact ⟨hz, n, hn, hw⟩

/-- Outside the guarded event, every required noun with `≤ Λ` leaves has its window. -/
theorem window_of_not_mem_guardedSizeWindowFailure (S : SemanticSkeleton) (Λ : ℕ)
    (ω : JointCoins K) (hz : nprSeed ω ≠ 0) (hout : ω ∉ guardedSizeWindowFailure (K := K) S Λ)
    (n : Noun) (hn : n ∈ skeletonSizeWindowNouns S) (hΛ : n.leaves ≤ Λ) :
    OpcodeSemantics.SizeWindow (nprSeed ω) n := by
  by_contra hw
  apply hout
  rw [guardedSizeWindowFailure, mem_liftSeed_iff, mem_guardedSizeWindowSeeds_iff]
  exact ⟨hz, n, hn, hΛ, hw⟩

/-- The guarded event is the original when the original's premise holds. -/
theorem guardedSizeWindowFailure_eq_of_bounded (S : SemanticSkeleton) (Λ : ℕ)
    (hb : SizeWindowNounsBoundedBy S Λ) :
    guardedSizeWindowFailure (K := K) S Λ = SizeWindowFailure S := by
  ext ω
  rw [guardedSizeWindowFailure, mem_liftSeed_iff, mem_guardedSizeWindowSeeds_iff,
    mem_SizeWindowFailure_iff]
  constructor
  · rintro ⟨hz, n, hn, -, hw⟩
    exact ⟨hz, n, hn, hw⟩
  · rintro ⟨hz, n, hn, hw⟩
    exact ⟨hz, n, hn, hb n hn, hw⟩

/-- **The guarded seeds lie in the low-order root union** (the mirror of
`sizeWindowFailureSeeds_subset_lowOrderRootSeeds`, with the guard supplying the leaf bound). -/
theorem guardedSizeWindowSeeds_subset_lowOrderRootSeeds (S : SemanticSkeleton) (Λ : ℕ) :
    guardedSizeWindowSeeds (K := K) S Λ ⊆ lowOrderRootSeeds (K := K) Λ := by
  intro z hzbad
  obtain ⟨hz, n, hn, hΛ, hwindow⟩ := (mem_guardedSizeWindowSeeds_iff S Λ z).1 hzbad
  have hcard : 0 < Fintype.card K - 1 := by
    have := Fintype.one_lt_card (α := K)
    omega
  have horderPos : 0 < orderOf z := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    exact ⟨Fintype.card K - 1, hcard, FiniteField.pow_card_sub_one_eq_one z hz⟩
  have horderLeN : orderOf z ≤ n.leaves := by
    by_contra hle
    have hnlt : n.leaves < orderOf z := Nat.lt_of_not_ge hle
    exact hwindow ⟨n.one_le_leaves.trans_lt hnlt, hnlt⟩
  have horderLe : orderOf z ≤ Λ := horderLeN.trans hΛ
  rw [lowOrderRootSeeds, Finset.mem_biUnion]
  refine ⟨orderOf z, Finset.mem_Icc.mpr ⟨horderPos, horderLe⟩, ?_⟩
  rw [mem_nthRootsFinset horderPos]
  exact pow_orderOf_eq_one z

/-- Card `≤ sizeWindowRootBound Λ · |𝕂|³`, no premise. -/
theorem guardedSizeWindowFailure_card_le (S : SemanticSkeleton) (Λ : ℕ) :
    (guardedSizeWindowFailure (K := K) S Λ).card ≤ sizeWindowRootBound Λ * Fintype.card K ^ 3 := by
  rw [guardedSizeWindowFailure, card_liftSeed]
  exact Nat.mul_le_mul_right _
    ((Finset.card_le_card (guardedSizeWindowSeeds_subset_lowOrderRootSeeds S Λ)).trans
      (lowOrderRootSeeds_card_le Λ))

end Guarded

/-! ## §C  The event union and its trace-uniform card -/

section Union

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-- **The P8 event union at a strategy, guarded throughout** (2b-ii's P8 slot shape, fibred over
`lmb` by the caller): zero seed, the guarded census's collisions, the topology event, the
envelope-guarded axis share, the guarded size windows. -/
def evFailureUnion (T : ProductionP8Containment.ProductionStrategy F K) (Λ : ℕ) (lmb : K) : Finset (JointCoins K) :=
  (((zeroSeedFailureEvent ∪ collisionFailureEvent (guardedCensusEv K T.skeleton Λ)) ∪
      specializedTopologyFailureEvent T.verifier.raw lmb) ∪
    envelopeAxisFailureEvent T lmb) ∪
      guardedSizeWindowFailure T.skeleton Λ

/-- **The trace-uniform P8 numerator**: `1 + (3 + 19N)(2Λ − 1) + (24N + 8M) + M(3N + 3) +
sizeWindowRootBound Λ` — `ProductionP8Containment.workload`'s P8 part with the topology bound at
its row-count value and the axis share at `axisUniformWorkload`. -/
def p8WorkEv (N M Λ : ℕ) : ℕ :=
  1 + (3 + 19 * N) * (2 * Λ - 1) + (24 * N + 8 * M) + axisUniformWorkload N M +
    sizeWindowRootBound Λ

/-- The topology workload at any strategy is `24·compRows + 8·memRows` of the seed's template. -/
theorem topologyWorkload_afterAlphaM (T : ProductionP8Containment.ProductionStrategy F K) (z : K) (hz : z ≠ 0)
    (α lmb : K) :
    topologyWorkload (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base =
      (seedConfig T z hz).compRows * 3 * 8 + (seedConfig T z hz).memRows * 2 * 4 := rfl

/-- **THE CARD LEMMA OF THE UNION**: `≤ p8WorkEv N M Λ · |𝕂|³` at every strategy whose committed
templates have `≤ N` compute / `≤ M` memory rows and whose skeleton has `≤ N` compute rows.  No
census proof, no size-window premise, no axis-workload premise. -/
theorem evFailureUnion_card_le (h2 : (2 : K) ≠ 0) (T : ProductionP8Containment.ProductionStrategy F K) (Λ : ℕ)
    (lmb : K) (N M : ℕ)
    (hR : (computeSkeletonRows T.skeleton).length ≤ N)
    (hN : ∀ z (hz : z ≠ 0), (seedConfig T z hz).compRows ≤ N)
    (hM : ∀ z (hz : z ≠ 0), (seedConfig T z hz).memRows ≤ M) :
    (evFailureUnion T Λ lmb).card ≤ p8WorkEv N M Λ * Fintype.card K ^ 3 := by
  let k3 := Fintype.card K ^ 3
  have hZ : (zeroSeedFailureEvent (K := K)).card ≤ 1 * k3 := by
    simp [k3, zeroSeedFailureEvent_card]
  have hC : (collisionFailureEvent (K := K) (guardedCensusEv K T.skeleton Λ)).card ≤
      ((3 + 19 * N) * (2 * Λ - 1)) * k3 :=
    (collisionFailureEvent_guardedCensusEv_card_le T.skeleton Λ).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
  have hG : (specializedTopologyFailureEvent T.verifier.raw lmb).card ≤ (24 * N + 8 * M) * k3 :=
    specializedTopologyFailureEvent_card_le T.verifier.raw lmb (24 * N + 8 * M)
      (fun z hz α => by
        rw [topologyWorkload_afterAlphaM]
        have := hN z hz
        have := hM z hz
        nlinarith)
  have hA : (envelopeAxisFailureEvent T lmb).card ≤ axisUniformWorkload N M * k3 :=
    envelopeAxisFailureEvent_card_le h2 T lmb N M hN hM
  have hW : (guardedSizeWindowFailure (K := K) T.skeleton Λ).card ≤ sizeWindowRootBound Λ * k3 :=
    guardedSizeWindowFailure_card_le T.skeleton Λ
  have hunion : (evFailureUnion T Λ lmb).card ≤
      (zeroSeedFailureEvent (K := K)).card +
        (collisionFailureEvent (K := K) (guardedCensusEv K T.skeleton Λ)).card +
        (specializedTopologyFailureEvent T.verifier.raw lmb).card +
        (envelopeAxisFailureEvent T lmb).card +
        (guardedSizeWindowFailure (K := K) T.skeleton Λ).card := by
    unfold evFailureUnion
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    exact Finset.card_union_le _ _
  have hw : p8WorkEv N M Λ * Fintype.card K ^ 3 =
      1 * k3 + ((3 + 19 * N) * (2 * Λ - 1)) * k3 + (24 * N + 8 * M) * k3 +
        axisUniformWorkload N M * k3 + sizeWindowRootBound Λ * k3 := by
    simp only [p8WorkEv, k3]; ring
  rw [hw]
  omega

end Union

/-! ## §D  At the event strategy: premise-free, at every `(Qc, Qm)` -/

section AtEv

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

variable (O : OptimizedStrictNockVMROMPackage F K hOrb)

local notation "CC[" O "]" =>
  ProductionNamedComputeRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.compRows_pos
    (OptimizedStrictNockVMROMPackage.computeNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.computeChallenge O)
    (OptimizedStrictNockVMROMPackage.computePublic O) (OptimizedStrictNockVMROMPackage.orbit O)

local notation "MC[" O "]" =>
  namedFinalMemoryRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.memoryChallenge O)
    (OptimizedStrictNockVMROMPackage.memoryPublic O) (OptimizedStrictNockVMROMPackage.orbit O)
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem

variable (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X])
  (tag : NodeEncoding.StateTagChar K)

/-- **The axis share at the event strategy, every `(Qc, Qm)`, no premise**: `≤ M·(3N+3)·|𝕂|³`
at the traces' row counts. -/
theorem envelopeAxisFailureEvent_Ev_card_le (h2 : (2 : K) ≠ 0) (lmb : K) :
    (envelopeAxisFailureEvent (strategyOfTracesEv O Qc Qm tag) lmb).card ≤
      axisUniformWorkload O.family.problem.cfg.compRows O.family.problem.cfg.memRows *
        Fintype.card K ^ 3 :=
  envelopeAxisFailureEvent_card_le h2 _ lmb _ _
    (fun z hz => (committedTemplate_Ev_compRows O Qc Qm tag z hz).le)
    (fun z hz => (committedTemplate_Ev_memRows O Qc Qm tag z hz).le)

/-- **The union at the event strategy, every `(Qc, Qm)`, no premise**: `≤ p8WorkEv N M Λ · |𝕂|³`. -/
theorem evFailureUnion_Ev_card_le (h2 : (2 : K) ≠ 0) (Λ : ℕ) (lmb : K) :
    (evFailureUnion (strategyOfTracesEv O Qc Qm tag) Λ lmb).card ≤
      p8WorkEv O.family.problem.cfg.compRows O.family.problem.cfg.memRows Λ *
        Fintype.card K ^ 3 :=
  evFailureUnion_card_le h2 _ Λ lmb _ _ (skeletonEv_computeRows_le O Qc Qm)
    (fun z hz => (committedTemplate_Ev_compRows O Qc Qm tag z hz).le)
    (fun z hz => (committedTemplate_Ev_memRows O Qc Qm tag z hz).le)

end AtEv

/-! ## §E  Agreement with `strategyOfTracesR0AC2 … c h` at the event level -/

section Invariance

variable {K : Type} [Field K]

/-- The axis tree ignores any relabelling that keeps the timestamp metadata and the stored axis. -/
theorem templateAxisTree_mapNTree (φ : MemoryRowTemplate (K := K) → MemoryRowTemplate (K := K))
    (hstamp : ∀ T, (φ T).timestamp = T.timestamp)
    (haxis : ∀ T, (φ T).placeholder.2.2.mem.axis = T.placeholder.2.2.mem.axis) :
    ∀ t : NTree (MemoryRowTemplate (K := K)),
      templateAxisTree (mapNTree φ t) = templateAxisTree t := by
  intro t
  let P := fun t : NTree (MemoryRowTemplate (K := K)) =>
    templateAxisTree (mapNTree φ t) = templateAxisTree t
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro row children ih
    simp only [P, mapNTree]
    cases hs : row.timestamp.state with
    | decompose =>
        rcases children with _ | ⟨l, rest⟩
        · simp [templateAxisTree, hstamp, hs]
        · rcases rest with _ | ⟨r, tail⟩
          · simp [templateAxisTree, hstamp, hs]
          · rcases tail with _ | ⟨x, xs⟩
            · have hl := ih l (by simp)
              have hr := ih r (by simp)
              simp only [P] at hl hr
              simp [templateAxisTree, hstamp, hs, hl, hr]
            · simp [templateAxisTree, hstamp, hs]
    | halt => simp [templateAxisTree, hstamp, hs]
    | read_root =>
        rcases children with _ | ⟨c, rest⟩
        · simp [templateAxisTree, hstamp, hs]
        · rcases rest with _ | ⟨x, xs⟩
          · have hc := ih c (by simp)
            simp only [P] at hc
            simp [templateAxisTree, hstamp, hs, hc]
          · simp [templateAxisTree, hstamp, hs]
    | verify_child =>
        rcases children with _ | ⟨c, rest⟩
        · simp [templateAxisTree, hstamp, hs]
        · rcases rest with _ | ⟨x, xs⟩
          · have hc := ih c (by simp)
            simp only [P] at hc
            simp [templateAxisTree, hstamp, haxis, hs, hc]
          · simp [templateAxisTree, hstamp, hs]
  · intro c hc
    simp at hc
  · intro head tail ihHead ihTail c hc
    simp only [List.mem_cons] at hc
    exact hc.elim (fun h => h ▸ ihHead) (ihTail c)

variable [Fintype K] [DecidableEq K]

theorem childLabel_mapNTree {α β : Type*} (f : α → β) (t : NTree α) (i : ℕ) :
    (mapNTree f t).childLabel i = (t.childLabel i).map f := by
  simp [NTree.childLabel, NTree.childOpt, mapNTree_children, List.getElem?_map, Option.map_map,
    Function.comp_def, mapNTree_label]

/-- The compute topology payloads ignore the inputs record. -/
theorem computeSlotBadGammas_mapNTree (f : State × DTcomp K → State × DTcomp K)
    (hst : ∀ l, (f l).1 = l.1) (hpub : ∀ l, (f l).2.2.1 = l.2.2.1)
    (t : NTree (State × DTcomp K)) (i : Fin 3) :
    computeSlotBadGammas (mapNTree f t) i = computeSlotBadGammas t i := by
  have hact : computeActualPayload (mapNTree f t) i = computeActualPayload t i := by
    unfold computeActualPayload
    rw [childLabel_mapNTree]
    cases t.childLabel i with
    | none => rfl
    | some c => simp [hpub]
  have hexp : computeExpectedPayload (mapNTree f t) i = computeExpectedPayload t i := by
    unfold computeExpectedPayload
    rw [mapNTree_label, hpub]
  unfold computeSlotBadGammas
  rw [hact, hexp, mapNTree_label, hst]

/-- The memory topology payloads ignore the challenge record and `λ`. -/
theorem memorySlotBadGammas_mapNTree (f : MState × DTmem K → MState × DTmem K)
    (hst : ∀ l, (f l).1 = l.1) (hpt : ∀ l, (f l).2.2.pt = l.2.2.pt)
    (hlc : ∀ l, (f l).2.2.lc = l.2.2.lc) (hrc : ∀ l, (f l).2.2.rc = l.2.2.rc)
    (t : NTree (MState × DTmem K)) (i : Fin 2) :
    memorySlotBadGammas (mapNTree f t) i = memorySlotBadGammas t i := by
  have hact : memoryActualPayload (mapNTree f t) i = memoryActualPayload t i := by
    unfold memoryActualPayload
    rw [childLabel_mapNTree]
    cases t.childLabel i with
    | none => rfl
    | some c => simp [hpt]
  have hexp : memoryExpectedPayload (mapNTree f t) i = memoryExpectedPayload t i := by
    unfold memoryExpectedPayload memCell
    rw [mapNTree_label]
    fin_cases i
    · simp [hlc]
    · simp [hrc]
  unfold memorySlotBadGammas
  rw [hact, hexp, mapNTree_label, hst]

variable {F : Type} [Field F] [Algebra F K]

/-- **The topology bad-γ set is invariant under label resets the payloads ignore.** -/
theorem topologyBadGammas_congr (R R' : RawPlusIOSegmentedFamily F K)
    (fC : State × DTcomp K → State × DTcomp K)
    (hstC : ∀ l, (fC l).1 = l.1) (hpub : ∀ l, (fC l).2.2.1 = l.2.2.1)
    (fM : MState × DTmem K → MState × DTmem K)
    (hstM : ∀ l, (fM l).1 = l.1) (hpt : ∀ l, (fM l).2.2.pt = l.2.2.pt)
    (hlc : ∀ l, (fM l).2.2.lc = l.2.2.lc) (hrc : ∀ l, (fM l).2.2.rc = l.2.2.rc)
    (hC : R.exec.computeTree = mapNTree fC R'.exec.computeTree)
    (hM : R.exec.memoryForest = R'.exec.memoryForest.map (mapNTree fM)) :
    topologyBadGammas R = topologyBadGammas R' := by
  unfold topologyBadGammas computeTopologyBadGammas memoryTopologyBadGammas
  have hrowsC : R.computeWalkRows = R'.computeWalkRows.map (mapNTree fC) := by
    show bfsForest [R.exec.computeTree] = (bfsForest [R'.exec.computeTree]).map (mapNTree fC)
    rw [hC, show [mapNTree fC R'.exec.computeTree] =
      [R'.exec.computeTree].map (mapNTree fC) from rfl, bfsForest_mapNTree]
  have hrowsM : R.memoryWalkRows = R'.memoryWalkRows.map (mapNTree fM) := by
    show bfsForest R.exec.memoryForest = (bfsForest R'.exec.memoryForest).map (mapNTree fM)
    rw [hM, bfsForest_mapNTree]
  congr 1
  · rw [hrowsC, List.length_map]
    apply Finset.biUnion_congr rfl
    intro x _
    rw [hC, List.getD_map, computeSlotBadGammas_mapNTree fC hstC hpub]
  · rw [hrowsM, List.length_map]
    apply Finset.biUnion_congr rfl
    intro x _
    have hfb : R.exec.memoryForest.get ⟨0, List.length_pos_of_ne_nil R.exec.memoryForest_nonempty⟩ =
        mapNTree fM (R'.exec.memoryForest.get
          ⟨0, List.length_pos_of_ne_nil R'.exec.memoryForest_nonempty⟩) := by
      simp only [List.get_eq_getElem]
      rw [List.getElem_of_eq hM]
      simp only [List.getElem_map]
    rw [hfb, List.getD_map, memorySlotBadGammas_mapNTree fM hstM hpt hlc hrc]

end Invariance

section AgreementAtO

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

variable (O : OptimizedStrictNockVMROMPackage F K hOrb)

local notation "CC[" O "]" =>
  ProductionNamedComputeRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.compRows_pos
    (OptimizedStrictNockVMROMPackage.computeNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.computeChallenge O)
    (OptimizedStrictNockVMROMPackage.computePublic O) (OptimizedStrictNockVMROMPackage.orbit O)

local notation "MC[" O "]" =>
  namedFinalMemoryRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.memoryChallenge O)
    (OptimizedStrictNockVMROMPackage.memoryPublic O) (OptimizedStrictNockVMROMPackage.orbit O)
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem

variable (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X])
  (tag : NodeEncoding.StateTagChar K)
  (c : OptimizedProductionChallengeTuple K F) (h : TracesWalkHyps O Qc Qm c)

/-- The C2 strategy's template root `i` is the event template's root relabelled by `ψT`. -/
theorem templateMemoryTreeAt_agree (z : K) (hz : z ≠ 0) (i : Fin O.family.problem.cfg.kMem) :
    templateMemoryTreeAt (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz) i =
      mapNTree (ψT c (lamAt O Qm c))
        (templateMemoryTreeAt (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz) i) := by
  -- MIG 4.35: closing by `simp`/`rfl` made defeq compare the two templates' `kMem` head-to-head
  -- (unfolds both strategies); compare the two root indices by value through `Fin.val_cast`
  unfold templateMemoryTreeAt
  have key : ∀ {α β : Type} (g : β → α) (l : List α) (l' : List β), l = l'.map g →
      ∀ (j : Fin l.length) (j' : Fin l'.length), (j : ℕ) = j' → l.get j = g (l'.get j') := by
    intro α β g l l' hl j j' hj
    subst hl
    simp [List.get_eq_getElem, hj]
  exact key _ _ _ (template_memoryForest_agree O Qc Qm tag c h z hz) _ _
    ((Fin.val_cast _ i).trans (Fin.val_cast _ i).symm)

/-- **The committed axis trees agree at every root.** -/
theorem axisTree_agree (z : K) (hz : z ≠ 0) (i : Fin O.family.problem.cfg.kMem) :
    templateAxisTree (templateMemoryTreeAt
        (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz) i) =
      templateAxisTree (templateMemoryTreeAt
        (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz) i) := by
  rw [templateMemoryTreeAt_agree O Qc Qm tag c h z hz i]
  exact templateAxisTree_mapNTree (K := K) (ψT c (lamAt O Qm c)) (fun T => rfl) (fun T => rfl) _

theorem alphaFreeRoot_agree (z : K) (hz : z ≠ 0) (i : Fin O.family.problem.cfg.kMem) :
    alphaFreeRoot (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz) i =
      alphaFreeRoot (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz) i :=
  axisTree_agree O Qc Qm tag c h z hz i

theorem templateAxisPolynomial_agree (z : K) (hz : z ≠ 0) (i : Fin O.family.problem.cfg.kMem) :
    templateAxisPolynomial (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz) i =
      templateAxisPolynomial (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz) i := by
  unfold templateAxisPolynomial
  rw [axisTree_agree O Qc Qm tag c h z hz i]

theorem alphaFreeAxisStructureCheck_agree (z : K) (hz : z ≠ 0) :
    alphaFreeAxisStructureCheck (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz) =
      alphaFreeAxisStructureCheck (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz) := by
  unfold alphaFreeAxisStructureCheck forestExponentPartitionCheck templateForestReadExps
    templateForestVerifyExps
  show (decide (∀ i : Fin O.family.problem.cfg.kMem, alphaFreeRootStructureCheck
      (alphaFreeRoot (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz) i) =
        true) &&
      finiteLmIOCheck O.family.problem.cfg.Ksz
        ((List.finRange O.family.problem.cfg.kMem).flatMap fun (i : Fin O.family.problem.cfg.kMem) => readExps (templateAxisTree
          (templateMemoryTreeAt
            (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz) i)))
        ((List.finRange O.family.problem.cfg.kMem).flatMap fun (i : Fin O.family.problem.cfg.kMem) => verifyExps (templateAxisTree
          (templateMemoryTreeAt
            (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz) i)))) =
    (decide (∀ i : Fin O.family.problem.cfg.kMem, alphaFreeRootStructureCheck
      (alphaFreeRoot (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz) i) =
        true) &&
      finiteLmIOCheck O.family.problem.cfg.Ksz
        ((List.finRange O.family.problem.cfg.kMem).flatMap fun (i : Fin O.family.problem.cfg.kMem) => readExps (templateAxisTree
          (templateMemoryTreeAt
            (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz) i)))
        ((List.finRange O.family.problem.cfg.kMem).flatMap fun (i : Fin O.family.problem.cfg.kMem) => verifyExps (templateAxisTree
          (templateMemoryTreeAt
            (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz) i))))
  -- MIG 4.35: the `flatMap` binders are typed `Fin O.family.problem.cfg.kMem` in the `show` above, so
  -- `axisTree_agree` matches syntactically and the old fallback `rfl` (which compared the two
  -- templates' `kMem` head-to-head and timed out in whnf) is not needed
  simp only [alphaFreeRoot_agree O Qc Qm tag c h z hz, axisTree_agree O Qc Qm tag c h z hz]

theorem noWrapCheck_agree (z : K) (hz : z ≠ 0) (α : K) :
    noWrapCheck (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz) α =
      noWrapCheck (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz) α := by
  unfold noWrapCheck
  show decide (∀ i : Fin O.family.problem.cfg.kMem, rootNoWrapCheck α
      (alphaFreeRoot (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz) i) =
        true) =
    decide (∀ i : Fin O.family.problem.cfg.kMem, rootNoWrapCheck α
      (alphaFreeRoot (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz) i) = true)
  simp only [alphaFreeRoot_agree O Qc Qm tag c h z hz]
  try rfl

/-- **The checker-guarded root sets agree** (the specialized exact tree is the reindexed template
tree, `exactAxisTree_specialize`). -/
theorem verifierGuardedRootAlphas_agree (z : K) (hz : z ≠ 0) (lmb : K)
    (i : Fin O.family.problem.cfg.kMem) :
    verifierGuardedRootAlphas
        (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz) lmb i =
      verifierGuardedRootAlphas
        (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz) lmb i := by
  unfold verifierGuardedRootAlphas
  apply Finset.filter_congr
  intro α _
  -- MIG 4.35: explicit template/index arguments, so `rw` does not unify the root index type
  -- across the two templates
  rw [exactAxisTree_specialize
      (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz) α i,
    exactAxisTree_specialize (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz) α i,
    recoveredAxisTree_eq_reindexAxisTree, recoveredAxisTree_eq_reindexAxisTree,
    alphaFreeAxisStructureCheck_agree O Qc Qm tag c h z hz, noWrapCheck_agree O Qc Qm tag c h z hz α,
    axisTree_agree O Qc Qm tag c h z hz i, templateAxisPolynomial_agree O Qc Qm tag c h z hz i]

theorem envelopeRootUnion_agree (z : K) (hz : z ≠ 0) (lmb : K) :
    envelopeRootUnion (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz) lmb =
      envelopeRootUnion (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz) lmb := by
  unfold envelopeRootUnion envelopeRootAlphas envelopeDeg
  show (Finset.univ : Finset (Fin O.family.problem.cfg.kMem)).biUnion (fun i =>
      if (templateAxisPolynomial
          (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz) i).natDegree ≤
          3 * (computeLabelList O Qc c).length + 3 then
        verifierGuardedRootAlphas
          (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz) lmb i
      else ∅) =
    (Finset.univ : Finset (Fin O.family.problem.cfg.kMem)).biUnion (fun i =>
      if (templateAxisPolynomial
          (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz) i).natDegree ≤
          3 * (computeLabelList O Qc coinFree).length + 3 then
        verifierGuardedRootAlphas
          (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz) lmb i
      else ∅)
  apply Finset.biUnion_congr rfl
  intro i _
  rw [templateAxisPolynomial_agree O Qc Qm tag c h z hz i,
    verifierGuardedRootAlphas_agree O Qc Qm tag c h z hz lmb i,
    computeLabelList_length, computeLabelList_length]

/-- **Agreement — the envelope axis share**, every `c`, every `h`. -/
theorem envelopeAxisFailureEvent_agree (lmb : K) :
    envelopeAxisFailureEvent (strategyOfTracesR0AC2 O tag Qc Qm c h) lmb =
      envelopeAxisFailureEvent (strategyOfTracesEv O Qc Qm tag) lmb := by
  ext ω
  rw [mem_envelopeAxisFailureEvent_iff, mem_envelopeAxisFailureEvent_iff]
  constructor
  · rintro ⟨hz, hα⟩
    exact ⟨hz, by rwa [envelopeRootUnion_agree O Qc Qm tag c h _ hz lmb] at hα⟩
  · rintro ⟨hz, hα⟩
    exact ⟨hz, by rwa [envelopeRootUnion_agree O Qc Qm tag c h _ hz lmb]⟩

/-- The `(z, αM)` family bases agree on their topology bad-γ sets. -/
theorem topologyBadGammas_agree (z : K) (hz : z ≠ 0) (α lmb : K) :
    topologyBadGammas
        ((strategyOfTracesR0AC2 O tag Qc Qm c h).verifier.raw.afterAlphaM z hz α lmb).familyData.base =
      topologyBadGammas
        ((strategyOfTracesEv O Qc Qm tag).verifier.raw.afterAlphaM z hz α lmb).familyData.base := by
  refine topologyBadGammas_congr _ _ (setInp { inpAt O Qc c with α := α })
    (fun l => rfl) (fun l => rfl) (setMemRec c) (fun l => rfl) (fun l => rfl) (fun l => rfl)
    (fun l => rfl) ?_ ?_
  · show mapNTree (fun r => r.specialize α)
        (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz).computeTree =
      mapNTree (setInp { inpAt O Qc c with α := α }) (mapNTree (fun r => r.specialize α)
        (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz).computeTree)
    exact template_computeTree_spec_agree O Qc Qm tag c h z hz α
  · show (committedTemplate (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier z hz).memoryForest.map
        (mapNTree (fun r => r.specialize α lmb)) =
      ((committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz).memoryForest.map
        (mapNTree (fun r => r.specialize α lmb))).map (mapNTree (setMemRec c))
    rw [template_memoryForest_agree O Qc Qm tag c h z hz, List.map_map, List.map_map]
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_def, ReconTreeSize.mapNTree_comp]
    exact congrArg (fun g => mapNTree g t) (funext fun T => specialize_ψT c (lamAt O Qm c) T α lmb)

/-- **Agreement — the topology event**, every `c`, every `h`. -/
theorem specializedTopologyFailureEvent_agree (lmb : K) :
    specializedTopologyFailureEvent (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier.raw lmb =
      specializedTopologyFailureEvent (strategyOfTracesEv O Qc Qm tag).verifier.raw lmb := by
  ext ω
  rw [mem_specializedTopologyFailureEvent_iff, mem_specializedTopologyFailureEvent_iff]
  constructor
  · rintro ⟨hz, hb⟩
    exact ⟨hz, by rwa [topologyBadGammas_agree O Qc Qm tag c h _ hz _ lmb] at hb⟩
  · rintro ⟨hz, hb⟩
    exact ⟨hz, by rwa [topologyBadGammas_agree O Qc Qm tag c h _ hz _ lmb]⟩

/-- **THE AGREEMENT LEMMA AT THE EVENT LEVEL**: for every `c` and every tiling proof `h`, the
P8 event union at `strategyOfTracesR0AC2 O tag Qc Qm c h` is the union at the coin-free, `h`-free
`strategyOfTracesEv O Qc Qm tag`.  The pinned slot can be stated at the latter and bounded fibre
by fibre; the containment proof can be run at the former. -/
theorem evFailureUnion_agree (Λ : ℕ) (lmb : K) :
    evFailureUnion (strategyOfTracesR0AC2 O tag Qc Qm c h) Λ lmb =
      evFailureUnion (strategyOfTracesEv O Qc Qm tag) Λ lmb := by
  unfold evFailureUnion guardedCensusEv guardedSizeWindowFailure guardedSizeWindowSeeds
  rw [combinedSkeletonPairs_agree O Qc Qm tag c h, skeletonSizeWindowNouns_agree O Qc Qm tag c h,
    specializedTopologyFailureEvent_agree O Qc Qm tag c h lmb,
    envelopeAxisFailureEvent_agree O Qc Qm tag c h lmb]

end AgreementAtO

end

end Nock.NockVMROM.Thm54.P8EventEv
