import Nock.NockVMROM.Thm54.P8Core.PartATopology12
import Nock.RedTeam.Batch1409Thm54PartAStaging
import Nock.RedTeam.Batch1410Thm54PartAUnhosted309
import Nock.RedTeam.Batch1420Thm54PartAL3Honest12
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1430Thm54PartAH21.lean

  * §1 gap 1 composed with L1: L1's composed `summand9_readsOn` / `summand10W_readsOn` (stated for an
    ARBITRARY `AdaptiveEnvs` with the repartitioned role rounds) instantiate at the adaptive
    environments BUILT from a staged strategy's committed memory columns
    (`PartAStaged.memoryAdaptiveEnvs`), so L1's receipts are about traces, not envs.
  * §2 the H2.1 table, one receipt per summand (`summand_k_readsOn12`), collected in
    `PartAStaged.consumedFailureEvent12_roundLocal`; summands 5 and 8 at the parallel package ARE
    L2's 309 events (`summand5_eq309`, `summand8_eq309`).
  * §3 **event-level negative control at `deployedChronology`** (`nc_event_deployed_*`): an
    adaptive memory strategy that commits the timestamp (role 26, round 2 at the deployed
    schedule) after the IO coin `IOγ` and the internal pole; its bad set is the ACTUAL consumed
    summand-4 function `summand4OfEnvs` (`tie4`, `rfl` to the package's), and its pair cylinder
    contains every tuple with `IOγ ≠ 0` — strictly more than the pair-cylinder bound
    `|𝕂|⁹ · (ioFailureUnionBound 10 1 1 |𝕂| + |𝕂|)` once `|𝕂| ≥ 43`; so the bad set is NOT
    `ReadsOn priorCoords`.  Positive control: the same strategy is NOT an adaptive strategy at the
    repartitioned schedule (role 26 is block B1 there: `nc_not_adaptive_repartitioned`).
  * §4 silent-gate controls (one per C5 family): (a) the walk line gate at slot 9 vs slot 3
    (L3's concrete pair, restated jointly); (b) the walk lift `liftWalkWFailure` vs the landed
    cylinder `cyl12 ∘ liftP8Failure` on a concrete set and tuple; (c) the codec
    `sampledEncodeExtension309` vs `sampledEncodeExtension` (the old one reads the walk count, the
    new one does not); (d) the decoder: the 309 source environment vs the landed one at source
    index 303.

  Scope: the repartitioned schedule and the parallel package; §3 is the only statement at
  `deployedChronology`, and it is a NEGATIVE control
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1430

open Nock Nock.Reified Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.RepartitionedStaging
open Nock.NockVMROM.Thm54.DeployedStaging
open Nock.NockVMROM.Thm54.PartA12
open Nock.NockVMROM.Thm54.PartAStaged
open scoped Polynomial

noncomputable section

/-! ## §1 Gap 1 composed with L1's env-level receipts -/

section Gap1

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem sched_eq_newSampled : (sched : Fin 12 → ℕ) = Nock.RedTeam.Batch1409.newSampled := by
  funext i; fin_cases i <;> rfl

/-- **Gap 1 + L1, summand 9**: at the adaptive environments built from a staged memory strategy's
committed columns, L1's composed `ReadsOn` holds. -/
theorem summand9_on_committed_columns (Qm : (Fin 12 → K) → Fin P.memoryChip.rap.w → F[X])
    (hst : StagedVec (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) Qm) (kroots : ℕ) :
    ReadsOn (C := K) (∅ ∪ priorCoords (memoryAdaptiveEnvs P Qm hst).sampledAfter 1)
      (fun χ => Nock.RedTeam.Batch1409.bad9 kroots ((memoryAdaptiveEnvs P Qm hst).envK χ)
        ((memoryAdaptiveEnvs P Qm hst).envF χ) χ) :=
  Nock.RedTeam.Batch1409.summand9_readsOn _ rfl
    (fun b hb => by
      show newMemoryColRound b = 0
      simp only [Nock.RedTeam.Batch1409.stateBase, List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> rfl)
    sched_eq_newSampled kroots

/-- **Gap 1 + L1, summand 10 at `αW`.** -/
theorem summand10W_on_committed_columns (Qm : (Fin 12 → K) → Fin P.memoryChip.rap.w → F[X])
    (hst : StagedVec (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) Qm) (kroots : ℕ) :
    ReadsOn (C := K) ({1} ∪ priorCoords (memoryAdaptiveEnvs P Qm hst).sampledAfter 11)
      (fun χ => Nock.RedTeam.Batch1409.bad10W kroots ((memoryAdaptiveEnvs P Qm hst).envK χ)
        ((memoryAdaptiveEnvs P Qm hst).envF χ) χ) :=
  Nock.RedTeam.Batch1409.summand10W_readsOn _ rfl
    (fun b hb => by
      show newMemoryColRound b = 0
      simp only [Nock.RedTeam.Batch1409.stateBase, List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> rfl)
    sched_eq_newSampled kroots

/-- The adaptive environments are the package's row environments of the committed columns. -/
theorem memoryAdaptiveEnvs_envK (Qm : (Fin 12 → K) → Fin P.memoryChip.rap.w → F[X])
    (hst : StagedVec (fun j : Fin P.memoryChip.rap.w => newMemoryColRound j) Qm) (χ : Fin 12 → K) :
    (memoryAdaptiveEnvs P Qm hst).envK χ = P.memorySourceEnv (Qm χ) := rfl

theorem computeAdaptiveEnvs_envK (Qc : (Fin 12 → K) → Fin 309 → F[X])
    (hst : StagedVec (fun j : Fin 309 => newComputeColRound j) Qc) (χ : Fin 12 → K) :
    (computeAdaptiveEnvs P Qc hst).envK χ = P.computeSourceEnv (truncQc P (Qc χ)) := rfl

/-! ## §2 The H2.1 table (one receipt per summand) -/

/-- Summands 5 and 8 at the parallel package are L2's events at the un-hosted 309 chip. -/
theorem summands58_are_309 (Qc : Fin 309 → F[X]) :
    P.computeWalkRootEvent (truncQc P Qc) = Unhosted309.computeWalkRootEvent309 P Qc ∧
      P.computePrefixGammaEventOf (truncQc P Qc) = Unhosted309.computePrefixGammaEventOf309 P Qc :=
  ⟨summand5_eq309 P Qc, summand8_eq309 P Qc⟩

end Gap1


section NCEvent

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The deployed eleven-coin schedule. -/
abbrev oldSched : Fin 11 → ℕ := Nock.RedTeam.Batch1409.oldSampled

/-- The forger's timestamp: `-interPole / IOγ⁷` (`IOγ` = coin 4, `interPole` = coin 9). -/
def forgedTs (χ : Fin 11 → K) : K := -(χ 9) / (χ 4) ^ 7

/-- **The adaptive memory strategy at `deployedChronology`**: one memory row, a `read_root` row
whose record is zero except its timestamp slot (role 26), which the prover commits AFTER seeing
the IO coin and the internal pole — allowed by `K_reads`, because role 26 is round 2 at the
deployed schedule while both coins are sampled after round 1. -/
def ncDeployed : AdaptiveEnvs 11 1 K K where
  roleRound := memoryRoleRound
  baseRound := fun _ => 0
  sampledAfter := oldSched
  envK := fun χ _ => ⟨fun r => if r = 26 then forgedTs χ else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩
  envF := fun _ _ => ⟨fun b => if b = 2 then 1 else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩
  K_reads := by
    intro r χ χ' h i
    by_cases hr : r = 26
    · subst hr
      have : χ = χ' := funext fun j => h j (by
        show oldSched j < memoryRoleRound 26
        fin_cases j <;> decide)
      subst this; rfl
    · simp [hr]
  F_reads := by intro b χ χ' _ i; rfl

/-- The ACTUAL consumed summand-4 bad set (`summand4OfEnvs`, `tie4` to the package's) along the
forger's strategy. -/
def ncBad (χ : Fin 11 → K) : Finset (K × K) :=
  PartAB0.summand4OfEnvs (ncDeployed.envK χ) (ncDeployed.envF χ)

theorem ncBad_hit (χ : Fin 11 → K) (h4 : χ 4 ≠ 0) : (χ 4, χ 9) ∈ ncBad χ := by
  unfold ncBad PartAB0.summand4OfEnvs interFailurePairs
  refine Finset.mem_union_right _ ?_
  simp only [allRowPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    FiniteIO.IOPoleHitEvent]
  refine ⟨_, List.mem_append_left _ (List.mem_ofFn.2 ⟨0, rfl⟩), ?_⟩
  simp only [rlc, Fin.sum_univ_succ, Fin.sum_univ_zero, OptimizedMemoryHostileAccumulator.rowRecord,
    ncDeployed, forgedTs]
  norm_num
  field_simp
  ring

/-- **The pair cylinder of the deployed summand 4 contains every tuple with `IOγ ≠ 0`.** -/
theorem nc_event_deployed_cylinder :
    (Finset.univ.filter fun χ : Fin 11 → K => χ 4 ≠ 0) ⊆ cylinder₂ (4 : Fin 11) 9 ncBad := by
  intro χ hχ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
  simp only [cylinder₂, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ncBad_hit χ hχ

theorem card_nonzero4 :
    (Finset.univ.filter fun χ : Fin 11 → K => χ 4 ≠ 0).card =
      (Fintype.card K - 1) * Fintype.card K ^ 10 := by
  have h1 : (Finset.univ.filter fun χ : Fin 11 → K => χ 4 ≠ 0) =
      Finset.univ \ (Finset.univ.filter fun χ : Fin 11 → K => χ 4 = 0) := by
    ext χ; simp
  have h2 : (Finset.univ.filter fun χ : Fin 11 → K => χ 4 = 0).card = Fintype.card K ^ 10 := by
    have := cylinder_card_le (C := K) (4 : Fin 11) (∅ : Finset (Fin 11)) (by simp) (fun _ => {0}) (fun _ _ _ => rfl) 1
      (fun _ => by simp)
    have hge : Fintype.card K ^ 10 ≤ (Finset.univ.filter fun χ : Fin 11 → K => χ 4 = 0).card := by
      let e : ({j : Fin 11 // j ≠ 4} → K) → (Fin 11 → K) :=
        fun r j => if h : j = 4 then 0 else r ⟨j, h⟩
      have hinj : Function.Injective e := by
        intro r r' h; funext ⟨j, hj⟩
        have := congrFun h j; simpa [e, hj] using this
      calc Fintype.card K ^ 10 = Fintype.card ({j : Fin 11 // j ≠ 4} → K) := by
            rw [card_free_coords]
        _ = (Finset.univ.image e).card := by
            rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
        _ ≤ _ := Finset.card_le_card (by
            intro χ hχ
            obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hχ
            simp [e])
    have hle : (Finset.univ.filter fun χ : Fin 11 → K => χ 4 = 0).card ≤ Fintype.card K ^ 10 := by
      have h' : (Finset.univ.filter fun χ : Fin 11 → K => χ 4 = 0) = cylinder (4 : Fin 11) (fun _ => {0}) := by
        ext χ; simp [cylinder]
      rw [h']; simpa using this
    omega
  rw [h1, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, h2]
  have : Fintype.card K ^ 11 = Fintype.card K * Fintype.card K ^ 10 := by ring
  rw [this, Nat.sub_mul, one_mul]

theorem nc_event_deployed_not_readsOn (hK : 43 ≤ Fintype.card K) :
    ¬ ReadsOn (C := K) (priorCoords oldSched 4 ∪ priorCoords oldSched 9) ncBad := by
  intro h
  haveI : Nonempty K := ⟨0⟩
  have hb : ∀ χ : Fin 11 → K, (ncBad χ).card ≤ FiniteIO.ioFailureUnionBound 10 1 1 (Fintype.card K) +
      Fintype.card K * 1 := by
    intro χ
    unfold ncBad PartAB0.summand4OfEnvs interFailurePairs
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
    · refine (FiniteIO.IOFailureEvent_card_le _).trans (ioFailureUnionBound_mono₂ 10 _ _ 1 1 _ ?_ ?_)
      · simp only [PartAB0.interRecordsOfEnvs, ncDeployed, List.length_flatten, List.map_ofFn,
          List.sum_ofFn, Fin.sum_univ_one]
        split_ifs <;> simp
      · simp only [PartAB0.interRecordsOfEnvs, ncDeployed, List.length_flatten, List.map_ofFn,
          List.sum_ofFn, Fin.sum_univ_one]
        split_ifs <;> simp
    · have hcov : allRowPoleHitEvent (ncDeployed.envK χ) (ncDeployed.envF χ) ⊆
          (Finset.univ : Finset K).biUnion (fun γ => ({γ} : Finset K) ×ˢ
            FiniteIO.IOPoleHitEvent ⟨List.ofFn (fun i =>
              OptimizedMemoryHostileAccumulator.rowRecord (ncDeployed.envK χ i)
                (ncDeployed.envF χ i)), []⟩ γ) := by
        intro q hq
        simp only [allRowPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        exact Finset.mem_biUnion.mpr ⟨q.1, Finset.mem_univ _,
          Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, hq⟩⟩
      refine (Finset.card_le_card hcov).trans (Finset.card_biUnion_le.trans ?_)
      have hsum : ∀ γ ∈ (Finset.univ : Finset K), (({γ} : Finset K) ×ˢ
          FiniteIO.IOPoleHitEvent ⟨List.ofFn (fun i =>
            OptimizedMemoryHostileAccumulator.rowRecord (ncDeployed.envK χ i)
              (ncDeployed.envF χ i)), []⟩ γ).card ≤ 1 := by
        intro γ _
        rw [Finset.card_product, Finset.card_singleton, one_mul]
        exact (FiniteIO.IOPoleHitEvent_card_le _ γ).trans (by simp [List.length_ofFn])
      refine (Finset.sum_le_sum hsum).trans (le_of_eq ?_)
      simp
  have hcyl := cylinder₂_card_le (C := K) (4 : Fin 11) 9 (by decide) _ (by decide) (by decide)
    ncBad h _ hb
  have hsub := Finset.card_le_card (nc_event_deployed_cylinder (K := K))
  rw [card_nonzero4] at hsub
  have hfin := hsub.trans hcyl
  simp only [FiniteIO.ioFailureUnionBound] at hfin
  have hk : Fintype.card K ^ 10 = Fintype.card K * Fintype.card K ^ 9 := by ring
  rw [hk] at hfin
  have hpos : 0 < Fintype.card K ^ 9 := by positivity
  have : (Fintype.card K - 1) * Fintype.card K ≤ 41 * Fintype.card K := by
    have h' : ((Fintype.card K - 1) * Fintype.card K) * Fintype.card K ^ 9 ≤
        (41 * Fintype.card K) * Fintype.card K ^ 9 := by
      calc _ = (Fintype.card K - 1) * (Fintype.card K * Fintype.card K ^ 9) := by ring
        _ ≤ Fintype.card K ^ (11 - 2) * (((1 + 1) * (1 + 1) * (10 - 1)) * Fintype.card K +
              Fintype.card K * (2 * (1 + 1)) + Fintype.card K * 1) := hfin
        _ = (41 * Fintype.card K) * Fintype.card K ^ 9 := by norm_num; ring
    exact Nat.le_of_mul_le_mul_right h' hpos
  have : Fintype.card K - 1 ≤ 41 := Nat.le_of_mul_le_mul_right this (by omega)
  omega

/-- **Positive control: the same strategy is not adaptive at the repartitioned schedule** — role 26
(`ts`) is block B1 there, committed before `IOγ` and the internal pole (M2), so a timestamp
depending on them violates the read discipline. -/
theorem nc_not_adaptive_repartitioned (h01 : (1 : K) ≠ 0) :
    ¬ ∀ χ χ' : Fin 12 → K, (∀ j, sched j < newMemoryRoleRound 26 → χ j = χ' j) →
      (fun χ : Fin 12 → K => -(χ 9) / (χ 4) ^ 7) χ = (fun χ : Fin 12 → K => -(χ 9) / (χ 4) ^ 7) χ' := by
  intro h
  have := h (fun j => if j = 4 then 1 else 0) (fun j => if j = 4 then 1 else if j = 9 then 1 else 0)
    (fun j hj => by
      have hr : newMemoryRoleRound 26 = 1 := by decide
      rw [hr] at hj
      fin_cases j <;> simp_all <;> revert hj <;> decide)
  simp at this

end NCEvent


section Silent
open MixedCoordinateCompiler OptimizedMemoryGateBasis CoordinateCompiler

/-- **(a) Walk gates**: on one concrete row, the landed (slot-3) line gate holds and the
twelve-coin (slot-9) line gate fails. -/
theorem silent_walkGate_differs :
    (MixedExpr.Scale (bcur 4)
        (MixedExpr.ofExpr
          (Nock.Reified.Trans.walkLn1.subst walkBoundarySubst)) :
          MixedExpr (ZMod 5)).eval
        Nock.RedTeam.Batch1420.concreteEnvK Nock.RedTeam.Batch1420.concreteEnvF = 0 ∧
      (MixedExpr.Scale (bcur 4)
        (MixedExpr.ofExpr
          (Nock.Reified.Trans.walkLn1.subst walkBoundarySubst12)) :
          MixedExpr (ZMod 5)).eval
        Nock.RedTeam.Batch1420.concreteEnvK Nock.RedTeam.Batch1420.concreteEnvF ≠ 0 :=
  ⟨Nock.RedTeam.Batch1420.concrete_ln1_accepted_landed, Nock.RedTeam.Batch1420.concrete_ln1_rejected12⟩

theorem silent_walkLift_differs :
    ∃ c : OptimizedProductionChallengeTuple12 (ZMod 5) (ZMod 5),
      c ∈ cyl12 (liftP8Failure (F := ZMod 5)
          (OptimizedFailureEventEv.alphaZeroEvent : Finset (JointCoins (ZMod 5)))) ∧
        c ∉ liftWalkWFailure (F := ZMod 5)
          (OptimizedFailureEventEv.alphaZeroEvent : Finset (JointCoins (ZMod 5))) := by
  refine ⟨tuple12OfVec (fun j => if j = 11 then 1 else 0), ?_, ?_⟩
  · rw [mem_cyl12_liftP8]; simp [tuple12OfVec, alphaM]
  · rw [mem_liftWalkWFailure]; simp [tuple12OfVec, walkJoint, walkView11, alphaM]

/-- **(c) Codec**: the landed encoding reads the walk count at a role-A host cell, the 309 encoding
does not — so they are different functions of the overlay values. -/
theorem silent_codec_differs {K : Type} [Field K] (pub : ComputeTable.Pub K)
    (dec : ComputeTable.Dec K) (ex : ComputeTable.Extra K)
    (v : OptimizedComputeOverlay.SampledOverlayValues K) :
    ¬ ∀ w : OptimizedComputeOverlay.SampledOverlayValues K,
      OptimizedComputeOverlay.sampledEncodeExtension pub dec ex w =
        Unhosted309.sampledEncodeExtension309 pub dec ex w := by
  intro h
  let v0 : OptimizedComputeOverlay.SampledOverlayValues K :=
    { v with toOverlayValues := { v.toOverlayValues with walkCount := 0, walkAcc := 0 } }
  let v1 : OptimizedComputeOverlay.SampledOverlayValues K :=
    { v with toOverlayValues := { v.toOverlayValues with walkCount := 1, walkAcc := 0 } }
  have hc0 := congrFun (h v0) (.inl (OptimizedComputeOverlay.overlayRoleA pub.state, 0))
  have hc1 := congrFun (h v1) (.inl (OptimizedComputeOverlay.overlayRoleA pub.state, 0))
  rw [Nock.RedTeam.Batch1410.deployed_encoding_hosts_count] at hc0 hc1
  have hw := Nock.RedTeam.Batch1410.encode309_walkFree pub dec ex v0 1 0
  have e01 : (0 : K) = 1 :=
    calc (0 : K) = v0.walkCount := rfl
      _ = _ := hc0
      _ = Unhosted309.sampledEncodeExtension309 pub dec ex v1
            (.inl (OptimizedComputeOverlay.overlayRoleA pub.state, 0)) := congrFun hw _
      _ = v1.walkCount := hc1.symm
      _ = 1 := rfl
  exact zero_ne_one e01

/-- **(d) Decoder**: at a base environment whose walk-count limb is `1`, the 309 source environment
reads it at source index 303 while the landed decoder returns the constant `0` there. -/
theorem silent_decoder_differs {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (b : Module.Basis (Fin 3) F K) :
    ∃ E : Env F, (Unhosted309.gather309 b E).toSourceEnv.trace 303 ≠
      (OptimizedComputeSemanticRealization.gatherCorrectedFinalTypedEnv b E).toSourceEnv.trace 303 := by
  refine ⟨⟨fun c => if c = 303 then 1 else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩, ?_⟩
  simp only [Unhosted309.gather309, Unhosted309.Env309.toSourceEnv, if_true,
    OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv.toSourceEnv]
  simp [Unhosted309.walkLimb, Fin.sum_univ_succ]
  exact b.ne_zero 0

end Silent

end

end Nock.RedTeam.Batch1430

#print axioms Nock.RedTeam.Batch1430.summand9_on_committed_columns
#print axioms Nock.RedTeam.Batch1430.summand10W_on_committed_columns
#print axioms Nock.RedTeam.Batch1430.summands58_are_309
#print axioms Nock.RedTeam.Batch1430.nc_event_deployed_cylinder
#print axioms Nock.RedTeam.Batch1430.nc_event_deployed_not_readsOn
#print axioms Nock.RedTeam.Batch1430.nc_not_adaptive_repartitioned
#print axioms Nock.RedTeam.Batch1430.silent_walkGate_differs
#print axioms Nock.RedTeam.Batch1430.silent_walkLift_differs
#print axioms Nock.RedTeam.Batch1430.silent_codec_differs
#print axioms Nock.RedTeam.Batch1430.silent_decoder_differs
