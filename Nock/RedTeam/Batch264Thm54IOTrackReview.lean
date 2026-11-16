/-
  Nock/RedTeam/Batch264Thm54IOTrackReview.lean

  Every the paper line below was re-opened at source
  (`sha256 ddc90d3bb0e9d0bef98cdeaf8d7da261658120631e7e73a9d86210be0321f326`).

  No `sorry`, `admit`, `native_decide`.

  ## Contents, by brief priority

  * At the broad generated program (`Batch232.bp_buildable`,
    `K = GaloisField 769 3`, `Ksz = 64`, 22 request / 22 response records built by
    `NockVM.encRec`): events (2) and (3) are PROPER subsets of `K`, the joint event is a proper
    subset of `K × K`, acceptance is inhabited at a coin pair outside all three events, and all
    eight hypotheses of `finiteIO_sound` hold at once.  The pole-hit event is rejected, never
    mis-accepted, and `finiteIO_sound` needs only the two-event `IOSoundnessEvent`.
  * The target's `sampled_io` is `P.shared_io` — the same proposition at
    every trace pair and tuple.  What acceptance
    yields about `Qc`'s own record columns is exactly the four per-row sampled-IO source gates.
    The finite chip cannot be a block of the compute trace: `|requests| + 1 ≠ compRows` at every
    package, `23 ≠ 17` at the broad program; `199` columns over `F` vs `12` over `K`.
  * `compress` is the paper's `(RLC^Y + X)` at `X ↦ pole`, `= RLC^α − β` at
    `pole = −β`, used consistently in the certificates; the optimized fold's active slots are the
    paper's `{0,2,5,6,7,8,9}` / `{6,9}` selector sums; an active zero-compression record is
    rejected by the fold; `L_IO` is the paper's set with `σ` read as `Perm`; the verifier checks
    of `:597-598`/`:270`/`:603-607` are `RawMessage.VerifierGates` conjuncts; `ver` booleanity is
    a gate on both chips; the `char > K` window is at `ringChar K = ringChar F`.
  * F-R4-1's hostile declaration FAILS `columns_commit_before_
    sampling` on `nockChronologyIO3` (negative control), the honest declaration passes (positive
    control), and the same hostile declaration PASSES on the two-message `nockChronologyWithIO`
    (contrast control).  `computeChip3` is the 112-column giga-RAP chip, not the deployed 199-column
    `P.computeChip`.
  * Proof-term traversal with
    `value? (allowOpaque := true)`: no completeness/`Data`/`BuildableNockExecution` constant in the
    soundness chain; the honest-side positive control finds them; the types-only traversal
    reproduces the false pass.  No external-LogUp consumer reads `ChallengeVector.β` or
    `interCoins`; the internal-pole theorem does (positive control).
-/
import Nock.NockVMROM.Thm54.IOCapstoneRedundancy
import Nock.NockVMROM.Thm54.GatedIOChip
import Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.CrossRapChronology
import Nock.NockVMROM.Thm54.GigaRAPThirdMessageProduction
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticLmIO
import Nock.RedTeam.Batch256Thm54InputsAtBroadProgram
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.RedTeam.Batch264

open Nock Nock.Walk Polynomial
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.IOCoinReconciliation
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam

noncomputable section


section P1

abbrev DK := DotConfig769.K
abbrev DF := DotConfig769.F

local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK




/-- The `m = 8` record lists of the broad program, built by `NockVM.encRec` through
`derivedRequestIO` / `derivedResponseIO`. -/
abbrev bpRecords : PreChallengeRecords DK 9 := executionRecords Batch232.bp_buildable

theorem b264_bpRecords_requests_length : bpRecords.requests.length = 22 :=
  Batch256.b256_requestIO_length

theorem b264_bpRecords_responses_length : bpRecords.responses.length = 22 := by
  have h := (execution_lio Batch232.bp_buildable).2.2.length_eq
  show Batch232.bp_buildable.exec.derivedResponseIO.length = 22
  rw [← h]
  exact Batch256.b256_requestIO_length

/-- The closed form of the union bound at equal record counts, from the three certificates:
`(2n)²(m−1)·c + c·2(2n) = c·(28n² + 4n)` at `m = 8`. -/
theorem b264_ioFailureUnionBound_eight_closed (n c : ℕ) :
    ioFailureUnionBound 8 n n c = c * (28 * n * n + 4 * n) := by
  simp only [ioFailureUnionBound]
  ring

/-- Event (2) is a PROPER subset of `K`: `card ≤ 44² · 7 = 13552 < 769³`. -/
theorem b264_rlc_event_proper :
    (IORLCCollisionEvent bpRecords).card < Fintype.card DK := by
  have h := IORLCCollisionEvent_card_le bpRecords
  rw [b264_bpRecords_requests_length, b264_bpRecords_responses_length,
    DotConfig769.card_K] at *
  omega

theorem b264_exists_good_gamma : ∃ γ : DK, γ ∉ IORLCCollisionEvent bpRecords := by
  refine Classical.byContradiction fun h => ?_
  have hall : ∀ γ : DK, γ ∈ IORLCCollisionEvent bpRecords :=
    fun γ => Classical.byContradiction fun hγ => h ⟨γ, hγ⟩
  have : IORLCCollisionEvent bpRecords = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
  have hc := b264_rlc_event_proper
  rw [this, Finset.card_univ] at hc
  exact lt_irrefl _ hc

/-- Event (3) is a PROPER subset of `K` at every `γ`: `card ≤ 44 < 769³`. -/
theorem b264_logDeriv_event_proper (γ : DK) :
    (IOLogDerivEvent bpRecords γ).card < Fintype.card DK := by
  have h := IOLogDerivEvent_card_le bpRecords γ
  rw [b264_bpRecords_requests_length, b264_bpRecords_responses_length,
    DotConfig769.card_K] at *
  omega

theorem b264_exists_good_pole (γ : DK) : ∃ z : DK, z ∉ IOLogDerivEvent bpRecords γ := by
  refine Classical.byContradiction fun h => ?_
  have hall : ∀ z : DK, z ∈ IOLogDerivEvent bpRecords γ :=
    fun z => Classical.byContradiction fun hz => h ⟨z, hz⟩
  have : IOLogDerivEvent bpRecords γ = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
  have hc := b264_logDeriv_event_proper γ
  rw [this, Finset.card_univ] at hc
  exact lt_irrefl _ hc

/-- Event (1) likewise. -/
theorem b264_poleHit_event_proper (γ : DK) :
    (IOPoleHitEvent bpRecords γ).card < Fintype.card DK := by
  have h := IOPoleHitEvent_card_le bpRecords γ
  rw [b264_bpRecords_requests_length, b264_bpRecords_responses_length,
    DotConfig769.card_K] at *
  omega

/-- The union bound at the ACTUAL record counts (`22`/`22`), not the `255` ceiling, is below
`|K|²`: `769³ · 13640 < 769⁶`. -/
theorem b264_union_bound_at_actual_counts :
    ioFailureUnionBound 9 bpRecords.requests.length bpRecords.responses.length
        (Fintype.card DK) < Fintype.card DK ^ 2 := by
  rw [b264_bpRecords_requests_length, b264_bpRecords_responses_length,
    DotConfig769.card_K,
    ioFailureUnionBound]
  norm_num

/-- The joint event is a proper subset of the coin space `K × K`. -/
theorem b264_joint_event_proper :
    (IOFailureEvent bpRecords).card < Fintype.card (DK × DK) := by
  have h := IOFailureEvent_card_le bpRecords
  have h2 := b264_union_bound_at_actual_counts
  rw [Fintype.card_prod]
  have : Fintype.card DK * Fintype.card DK = Fintype.card DK ^ 2 := by ring
  rw [this]
  omega

/-- **Acceptance is inhabited at a coin pair outside all three events**, at the broad program's
own records.  The witness is the generator's
(`sampledWitness`), the coins `bpInputs.ioCoins`. -/
theorem b264_acceptance_inhabited_at_good_coins :
    ∃ (coins : IOCoins DK) (w : PostChallengeIOWitness bpRecords coins),
      FiniteIOAccepts bpRecords coins w
        ∧ (coins.gamma, coins.pole) ∉ IOFailureEvent bpRecords :=
  ⟨Batch256.bpInputs.ioCoins, sampledWitness Batch232.bp_buildable Batch256.bpInputs,
    sampledWitness_accepts Batch232.bp_buildable Batch256.bpInputs,
    Batch256.b256_ioCoins_good⟩

/-- **`finiteIO_sound`'s eight hypotheses are simultaneously satisfiable** at 22-element record
lists with `Ksz = 64 < 769 = char K`. -/
theorem b264_finiteIO_sound_hypotheses_inhabited :
    ∃ (coins : IOCoins DK) (w : PostChallengeIOWitness bpRecords coins),
      FiniteIOAccepts bpRecords coins w
        ∧ Batch232.bp_buildable.cfg.Ksz < ringChar DK
        ∧ IO.InRange Batch232.bp_buildable.cfg.Ksz bpRecords.requests.length
        ∧ bpRecords.responses.length ≤ Batch232.bp_buildable.cfg.Ksz
        ∧ bpRecords.requests.Nodup ∧ bpRecords.responses.Nodup
        ∧ coins.gamma ∉ IORLCCollisionEvent bpRecords
        ∧ coins.pole ∉ IOLogDerivEvent bpRecords coins.gamma := by
  obtain ⟨coins, w, hacc, hgood⟩ := b264_acceptance_inhabited_at_good_coins
  simp only [IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hgood
  have hlio := execution_lio Batch232.bp_buildable
  refine ⟨coins, w, hacc, Batch232.bp_buildable.Ksz_lt_ringChar, ?_, ?_,
    Batch232.bp_buildable.requestNodup, hlio.2.1, hgood.1, hgood.2.2⟩
  · show IO.InRange Batch232.bp_buildable.cfg.Ksz
      Batch232.bp_buildable.exec.derivedRequestIO.length
    rw [hlio.2.2.length_eq]; exact hlio.1
  · exact hlio.1.2

theorem b264_bp_Ksz : Batch232.bp_buildable.cfg.Ksz = 64 := rfl

/-! ### The pole-hit event: rejected, never mis-accepted; its place in the union -/

/-- The soundness-side event: events (2) and (3) only. -/
def IOSoundnessEvent {K : Type*} [Field K] [Fintype K] [DecidableEq K] {m : ℕ}
    (records : PreChallengeRecords K m) : Finset (K × K) :=
  Finset.univ.filter (fun q => q.1 ∈ IORLCCollisionEvent records
    ∨ q.2 ∈ IOLogDerivEvent records q.1)

theorem b264_soundnessEvent_subset {K : Type*} [Field K] [Fintype K] [DecidableEq K] {m : ℕ}
    (records : PreChallengeRecords K m) :
    IOSoundnessEvent records ⊆ IOFailureEvent records := by
  intro q hq
  simp only [IOSoundnessEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hq
  simp only [IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hq with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

/-- **`finiteIO_sound` needs only the soundness event**: the pole-hit component is excluded by
acceptance itself (`pole_not_hit_of_accepts`), so event (1) is a completeness-side event
(`finiteIO_complete_of_LIO`'s `hpole`), carried in the union for the honest prover, not for the
hostile one. -/
theorem b264_finiteIO_sound_of_soundnessEvent {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p : ℕ} [CharP K p] {m Ksz : ℕ} {records : PreChallengeRecords K m} {coins : IOCoins K}
    {w : PostChallengeIOWitness records coins}
    (h : FiniteIOAccepts records coins w)
    (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz records.requests.length)
    (hKresp : records.responses.length ≤ Ksz)
    (hreqnd : records.requests.Nodup) (hrespnd : records.responses.Nodup)
    (hgood : (coins.gamma, coins.pole) ∉ IOSoundnessEvent records) :
    IO.LIO Ksz records.requests records.responses := by
  simp only [IOSoundnessEvent, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hgood
  exact finiteIO_sound h hKp hKreq hKresp hreqnd hrespnd hgood.1 hgood.2

/-- Acceptance at a pole in the pole-hit component is impossible: rejected, never mis-accepted. -/
theorem b264_no_acceptance_in_poleHit {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m : ℕ} {records : PreChallengeRecords K m} {coins : IOCoins K}
    (hhit : coins.pole ∈ IOPoleHitEvent records coins.gamma) :
    ¬ ∃ w : PostChallengeIOWitness records coins, FiniteIOAccepts records coins w := by
  rintro ⟨w, hw⟩
  exact pole_not_hit_of_accepts hw hhit

/-- The soundness-only event is bounded by `(k₁+k₂)²(m−1)·c + c·(k₁+k₂)` — the union bound minus
the pole-hit term `c·(k₁+k₂)`. -/
theorem b264_soundnessEvent_card_le {K : Type*} [Field K] [Fintype K] [DecidableEq K] {m : ℕ}
    (records : PreChallengeRecords K m) :
    (IOSoundnessEvent records).card
      ≤ (records.requests.length + records.responses.length)
          * (records.requests.length + records.responses.length) * (m - 1) * Fintype.card K
        + Fintype.card K * (records.requests.length + records.responses.length) := by
  classical
  set k₁ := records.requests.length
  set k₂ := records.responses.length
  set S : Finset (K × K) := (IORLCCollisionEvent records) ×ˢ Finset.univ with hS
  set T : Finset (K × K) := Finset.univ.biUnion (fun γ : K =>
    ({γ} : Finset K) ×ˢ (IOLogDerivEvent records γ)) with hT
  have hsub : IOSoundnessEvent records ⊆ S ∪ T := by
    intro q hq
    simp only [IOSoundnessEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rcases hq with h1 | h3
    · exact Finset.mem_union_left _ (by simp only [hS, Finset.mem_product]; exact ⟨h1, by simp⟩)
    · refine Finset.mem_union_right _ ?_
      refine Finset.mem_biUnion.mpr ⟨q.1, Finset.mem_univ _, ?_⟩
      simp only [Finset.mem_product, Finset.mem_singleton]
      exact ⟨trivial, h3⟩
  have hScard : S.card ≤ (k₁ + k₂) * (k₁ + k₂) * (m - 1) * Fintype.card K := by
    rw [hS, Finset.card_product, Finset.card_univ]
    exact Nat.mul_le_mul_right _ (IORLCCollisionEvent_card_le records)
  have hTcard : T.card ≤ Fintype.card K * (k₁ + k₂) := by
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_sum (g := fun _ : K => k₁ + k₂)
      (fun γ (_ : γ ∈ Finset.univ) => ?_)) ?_
    · rw [Finset.card_product, Finset.card_singleton, one_mul]
      exact IOLogDerivEvent_card_le records γ
    · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  calc (IOSoundnessEvent records).card ≤ (S ∪ T).card := Finset.card_le_card hsub
    _ ≤ S.card + T.card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add hScard hTcard

/-- At the broad program: `23 ≠ 17`. -/
theorem b264_bp_row_count_obstruction :
    Batch232.bp_buildable.exec.derivedRequestIO.length + 1 = 23
      ∧ Batch232.bp_buildable.cfg.compRows = 17 := by
  refine ⟨?_, Batch256.b256_compRows⟩
  rw [Batch256.b256_requestIO_length]

end P1

/-! # Bundling and threading at the consumed capstone -/

section P2

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The IO conjunct of the genuine target is inhabited from the package alone. -/
theorem b264_sampled_io_from_package_alone :
    IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs :=
  P.shared_io

/-- Two genuine targets at *different* traces and tuples have
`sampled_io` fields of the *same* proposition: this elaborates only because the field's type
mentions neither `Qc`, `Qm` nor `c`. -/
theorem b264_sampled_io_same_prop_across_traces
    (Qc Qc' : Fin P.computeChip.rap.w → F[X]) (Qm Qm' : Fin P.memoryChip.rap.w → F[X])
    (c c' : OptimizedProductionChallengeTuple K F)
    (h : P.OptimizedProductionGenuineTargetAt Qc Qm c)
    (h' : P.OptimizedProductionGenuineTargetAt Qc' Qm' c') :
    h.sampled_io = h'.sampled_io := rfl

/-- The tuple's IO coordinate is outside the IO
failure event at the package's records: `sampled_io_coins` pins it to the package's own coins,
and the package's strategy certifies those good (`FiniteIOStrategy.coins_not_failure`). -/
theorem b264_io_event_good_of_acceptance
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    c.2.1 ∉ FiniteIO.IOFailureEvent P.optimized.sampled.sampled.records := by
  rw [hacc.sampled_io_coins]
  exact FiniteIOStrategy.coins_not_failure P.optimized.sampled.sampled

/-- Hence no accepted tuple lies in the lifted IO summand of the consumed failure event. -/
theorem b264_accepted_outside_io_summand
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    c ∉ liftIOFailure (K := K) (F := F)
      (FiniteIO.IOFailureEvent P.optimized.sampled.sampled.records) := by
  rw [mem_liftIOFailure_iff, ioCoinsOf_pair]
  exact b264_io_event_good_of_acceptance P Qc Qm c hacc

/-- The two IO fields of the target follow from `P` and the `sampled_io_coins` pin alone:
`compute_satisfies` / `memory_satisfies` are never read for them. -/
theorem b264_target_io_fields_from_package_and_pin
    (c : OptimizedProductionChallengeTuple K F)
    (hpin : c.2.1 =
      (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole)) :
    IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs ∧
      c.2.1 ∉ FiniteIO.IOFailureEvent P.optimized.sampled.sampled.records := by
  refine ⟨P.shared_io, ?_⟩
  rw [hpin]
  exact FiniteIOStrategy.coins_not_failure P.optimized.sampled.sampled

/-- The records the bad set is stated at are the package's `objects.reqRecs` / `respRecs`. -/
theorem b264_io_summand_records_are_the_packages :
    P.optimized.sampled.sampled.records.requests = P.objects.reqRecs ∧
      P.optimized.sampled.sampled.records.responses = P.objects.respRecs :=
  ⟨IOCapstoneRedundancy.sampled_requests_eq_reqRecs P,
    IOCapstoneRedundancy.sampled_responses_eq_respRecs P⟩

/-! ### The consumed bound holds with `ioWork := 0` -/

/-- The empty record pair — its union bound is literally `0`. -/
def emptyRecords : PreChallengeRecords K 9 := ⟨[], []⟩

theorem b264_ioFailureUnionBound_empty (c : ℕ) : ioFailureUnionBound 8 0 0 c = 0 := by
  simp [ioFailureUnionBound]


/-- **Per row, the four sampled-IO source gates vanish on `Qc`'s row environment** — the three
inactive-safe denominator pins and the degree-4 fold.  This is the entire IO content of the target about `Qc`: no `IO.LIO` at
`Qc`'s records appears anywhere in `OptimizedProductionGenuineTargetAt`. -/
theorem b264_qc_rows_satisfy_sampled_io_gates
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedProductionAcceptanceAt Qc Qm c)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F)
    (hgood : c ∉ P.consumedFailureEvent Qc Qm)
    (i : Fin P.optimized.family.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows) :
    ∀ e ∈ OptimizedComputeGateBasis.finalSampledIOTransitionGates,
      e.eval (FamilyEnvCore.rowEnvAt P.optimized c (P.familyQc c Qc) i).toSourceEnv = 0 :=
  ((P.acceptance_outside_failure_implies_target hax hbasis hwidth Qc Qm c hacc hgood).compute i hi).sampledIOSafe4


/-- The package's sampled request list is `|derivedRequestIO|`, and one record per row never fits
the compute table. -/
theorem b264_package_requests_row_count_ne :
    P.optimized.sampled.sampled.records.requests.length + 1
      ≠ P.optimized.family.problem.cfg.compRows := by
  rw [P.optimized.sampled.requests_eq]
  exact GatedIO.requests_row_count_ne P.optimized.family.problem.exec

/-- The deployed compute chip is `199` columns over the base field `F`; the finite IO chip is `12`
columns over `K`. -/
theorem b264_chip_widths :
    P.computeChip.rap.w = 303 ∧ (FiniteIO.finiteIOProgAIR 8).numTraceCols = 12 := by
  refine ⟨?_, rfl⟩
  have h := P.optimized.exact_chip_resources
  dsimp only at h
  exact h.1

end P2


section P3

open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
open Nock.Reified

/-- `RLC^Y(array) = Σ Y^{i-1} array(i)`, zero-indexed. -/
theorem b264_rlc_is_paper_rlc {K : Type*} [Field K] {n : ℕ} (γ : K) (v : Fin n → K) :
    Walk.rlc γ v = ∑ c : Fin n, γ ^ (c : ℕ) * v c := rfl

/-- `compress = pole + RLC^γ(v)` is the paper's `(RLC^Y(·) + X)` at `X ↦ pole`. -/
theorem b264_compress_is_ldse_factor {K : Type*} [Field K] {m : ℕ} (coins : IOCoins K)
    (v : Fin m → K) : compress coins v = coins.pole + Walk.rlc coins.gamma v := rfl

/-- the paper's `RLC^α(·) − β` is the same factor at `pole = −β`. -/
theorem b264_compress_at_neg_beta {K : Type*} [Field K] {m : ℕ} (α β : K) (v : Fin m → K) :
    compress ⟨α, -β⟩ v = Walk.rlc α v - β := by
  simp [compress, sub_eq_neg_add]

/-- The sign is used consistently in `finiteIO_sound`'s certificates: `denomP` at the pole is the
product of the compressed denominators. -/
theorem b264_denomP_eval_is_prod_compress {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m : ℕ} (records : PreChallengeRecords K m) (γ z : K) :
    (denomP (reqVals records γ)).eval z
      = ∏ i, compress ⟨γ, z⟩ (records.requests.get i) := by
  rw [denomP_eval]; rfl

/-- The pole-hit event is exactly "some compressed denominator vanishes". -/
theorem b264_poleHit_iff_compress_zero {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m : ℕ} (records : PreChallengeRecords K m) (γ z : K) :
    z ∈ IOPoleHitEvent records γ
      ↔ ∃ v ∈ records.requests ++ records.responses, compress ⟨γ, z⟩ v = 0 := by
  simp [IOPoleHitEvent, compress]

/-- The identity acceptance extracts is the paper's log-derivative identity at `X = pole`. -/
theorem b264_endpoint_is_ldse_at_pole {K : Type*} [Field K] {m : ℕ}
    {records : PreChallengeRecords K m} {coins : IOCoins K}
    {w : PostChallengeIOWitness records coins} (h : FiniteIOAccepts records coins w) :
    (∑ i, (coins.pole + Walk.rlc coins.gamma (records.requests.get i))⁻¹)
      = ∑ j, (coins.pole + Walk.rlc coins.gamma (records.responses.get j))⁻¹ :=
  endpoint_sum_eq h

/-- Slot 0 is always active. -/
theorem b264_active_slot0 (kind : VarKind) : sampledActive kind 0 = .Const 1 := rfl

/-- Slot 1 is active for `op ∈ {0,2,5,6,7,8,9}` — the paper's `Σ_{i=2,5,6,7,8,9} op_i`
with `:1863`'s `op_0`, as a sum of the one-hot selector columns (`opCol`). -/
theorem b264_active_slot1 (kind : VarKind) :
    sampledActive kind 1 =
      .Add (.Var kind (opCol .s0)) (.Add (.Var kind (opCol .s2)) (.Add (.Var kind (opCol .s5))
        (.Add (.Var kind (opCol .s6)) (.Add (.Var kind (opCol .s7))
          (.Add (.Var kind (opCol .s8)) (.Var kind (opCol .s9))))))) := rfl

/-- Slot 2 is active for `op ∈ {6, 9}`. -/
theorem b264_active_slot2 (kind : VarKind) :
    sampledActive kind 2 = .Add (.Var kind (opCol .s6)) (.Var kind (opCol .s9)) := rfl

/-- The record emission per state agrees with the paper's arity table:
`1` for `{1,3,4,cons}`, `2` for `{0,2,5,7,8}`, `3` for `{6,9}`. -/
theorem b264_activeRequestRecords_length {K : Type*} [Field K] (pub : ComputeTable.Pub K) :
    (NockVM.activeRequestRecords pub).length = Nock.Framework.recordCount pub.state := by
  cases h : pub.state <;> simp [NockVM.activeRequestRecords, h, Nock.Framework.recordCount]

/-- `encRec` has eight coordinates — the paper's `(𝕂³)² × 𝔽 × 𝕂`, hence `m = 8`. -/
theorem b264_encRec_width {K : Type*} [Field K] (r : ComputeTable.MemRec K) :
    NockVM.encRec r = ![r.root.size, r.root.dyck, r.root.leaf, r.child.size, r.child.dyck,
      r.child.leaf, r.axis, r.ts, 0] := rfl

/-- The inactive-slot pin `safeD = a·d + (1 − a)`: `1` on an inactive slot, `d` on an active one. -/
theorem b264_safeDenom_inactive {K : Type*} [Field K] (d : K) : SafeDenom (0 : K) d = 1 := by
  simp [SafeDenom]
theorem b264_safeDenom_active {K : Type*} [Field K] (d : K) : SafeDenom (1 : K) d = d := by
  simp [SafeDenom]

/-- **An active record whose compression is genuinely `0` is rejected by the fold itself**: with
`a₀ = 1`, `d₀ = 0` and the other slots inactive the gate reads `0 = 1`. -/
theorem b264_fold_rejects_active_zero_denominator {K : Type*} [Field K] (acc accNext : K) :
    ¬ FoldedProgStep3 acc accNext (SafeDenom (1 : K) 0) (SafeDenom (0 : K) 0)
        (SafeDenom (0 : K) 0) 1 0 0 := by
  simp [FoldedProgStep3, SafeDenom]

/-- **On the optimized fold, TWO active pole hits in one row make the gate vacuous**: with
`a₀ = a₁ = 1` and `d₀ = d₁ = 0` both sides are `0` for every `acc`, `acc'`.  So on the deployed
chip event (1) is soundness-relevant — unlike on the finite chip, where `ioInvPin` rejects any
pole hit — and it IS a component of the consumed `IOFailureEvent` (`FiniteFieldIOSoundness.lean::
IOFailureEvent`).  Two distinct records compressing to the same `−pole` are also in event (2);
two equal requests violate the paper's unique-request condition. -/
theorem b264_fold_vacuous_at_double_pole_hit {K : Type*} [Field K] (acc accNext a₂ d₂ : K) :
    FoldedProgStep3 acc accNext (SafeDenom (1 : K) 0) (SafeDenom (1 : K) 0)
      (SafeDenom a₂ d₂) 1 1 a₂ := by
  simp [FoldedProgStep3, SafeDenom]

/-- The double pole hit is inside the consumed IO failure event (component (1)). -/
theorem b264_double_pole_hit_in_failure_event {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m : ℕ} (records : PreChallengeRecords K m) (γ z : K)
    (hz : ∃ v ∈ records.requests ++ records.responses, z + Walk.rlc γ v = 0) :
    (γ, z) ∈ IOFailureEvent records := by
  simp only [IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr (Or.inl (by simpa [IOPoleHitEvent] using hz))

/-- **`L_IO` transcription.**  `σ(responses) = requests`, `σ ∈ Sym_k`, is
`responses.Perm requests`; `Perm` is symmetric, so the Lean `requests.Perm responses` is the same
set. -/
theorem b264_lio_iff_sigma_form {R : Type*} [DecidableEq R] (K : ℕ) (req resp : List R) :
    IO.LIO K req resp ↔ IO.InRange K resp.length ∧ resp.Nodup ∧ resp.Perm req := by
  unfold IO.LIO
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3.symm⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3.symm⟩

/-- Unique request is *derived* from `L_IO`, not an extra conjunct of it. -/
theorem b264_lio_requests_nodup {R : Type*} [DecidableEq R] (K : ℕ) (req resp : List R)
    (h : IO.LIO K req resp) : req.Nodup :=
  h.2.2.nodup_iff.mpr h.2.1

theorem b264_verifierGates_io_conjuncts {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : RawPlusIOSegmentedFamily F K} {claim : P8PublicClaim} {ω : JointCoins K}
    {M : RawMessage R p} (h : M.VerifierGates claim ω) :
    R.requests = R.responses ∧ R.outMem = 0 ∧ (∀ j, M.io.multiplicity j ≠ 0)
      ∧ IO.InRange R.cfg.Ksz R.exec.derivedRequestIO.length
      ∧ R.exec.derivedRequestIO.Nodup
      ∧ R.exec.derivedResponseIO.length ≤ R.cfg.Ksz
      ∧ R.exec.derivedResponseIO.Nodup := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hend, hclose, hmul, hKreq, hreqnd, hKresp, hrespnd⟩
  exact ⟨hend, hclose, hmul, hKreq, hreqnd, hKresp, hrespnd⟩

/-- Finite chip: `ver` booleanity is a transition gate of `finiteIOMemAIR`. -/
theorem b264_finite_chip_has_ver_booleanity (m : ℕ) :
    (⟨.transition, ioMultBool⟩ : Constraint) ∈ (finiteIOMemAIR m).constraints := by
  simp [finiteIOMemAIR]

/-- Optimized memory chip: `multiplicitySource` is `ver·(ver − 1)` on role `39`, one of the ten
`sampledSources`. -/
theorem b264_optimized_memory_has_ver_booleanity :
    OptimizedMemoryGateBasis.multiplicitySource =
      .Mul (OptimizedMemoryGateBasis.extVar .traceCur 39)
        (.Sub (OptimizedMemoryGateBasis.extVar .traceCur 39) (.Const 1)) := rfl

theorem b264_finite_prog_chip_gates (m : ℕ) :
    (finiteIOProgAIR m).constraints =
      [⟨.boundary, ioAccInit⟩, ⟨.transition, ioInvPin m 4⟩,
        ⟨.transition, ioProgAccStep⟩, ⟨.terminal, ioTerm⟩] := rfl

/-- The optimized compute chip's endpoint buckets hold the walk's three endpoint gates and the
twenty-two selector equality checks — read off the definitions. -/
theorem b264_optimized_compute_endpoint_buckets :
    OptimizedComputeCorrectedFinal.correctedEndpoint2.length = 6 ∧
      OptimizedComputeCorrectedFinal.correctedEndpoint4.length = 1 ∧
      (OptimizedComputeFinal.finalEndpointEqualityChecks (F := ℚ)).length = 22 :=
  ⟨OptimizedComputeCorrectedFinal.corrected_lowered_counts.2.1,
    OptimizedComputeCorrectedFinal.corrected_lowered_counts.2.2, rfl⟩

/-- The `char > K` window is typed at `p = ringChar K`, the extension the coins are drawn from. -/
theorem b264_charBound_is_at_K {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    P.objects.cfg.Ksz < ringChar K :=
  P.ioStrategy.charBound

/-- The extension has the base field's characteristic, so the two readings coincide. -/
theorem b264_ringChar_ext_eq_base {F K : Type} [Field F] [Field K] [Algebra F K] :
    ringChar K = ringChar F := by
  haveI : CharP K (ringChar F) :=
    charP_of_injective_algebraMap (algebraMap F K).injective (ringChar F)
  exact ringChar.eq K (ringChar F)

end P3


section P5

open Nock.Framework Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.Staging Nock.NockVMROM.Thm54.Staged
open Nock.NockVMROM.Thm54.GigaChips
open Nock.NockVMROM.Thm54.GigaFinite
open Nock.NockVMROM.Thm54.GigaIOSlots
open Nock.NockVMROM.Thm54.GigaIOThirdMessage
open Nock.NockVMROM.Thm54.IOCoinReconciliation.Chronology
open Nock.NockVMROM.Thm54.CrossRap

/-- Record timestamps are round-2 columns; the IO coins are message 2. -/
theorem b264_timestamp_columns_round_two :
    (finComputeRoundOf4 111 : ℕ) = 2 ∧ (finMemRoundOf4 53 : ℕ) = 2 := ⟨by decide, by decide⟩

theorem b264_io_coins_message_two :
    (nockSampledAfterIO3 ioGammaSlot : ℕ) = 2 ∧ (nockSampledAfterIO3 ioPoleSlot : ℕ) = 2 :=
  ⟨by decide, by decide⟩

/-- The accumulator / reciprocal columns move to the fourth block (`:510` after `:509`). -/
theorem b264_io_coin_columns_round_three :
    (finComputeRoundOf4 100 : ℕ) = 3 ∧ (finComputeRoundOf4 101 : ℕ) = 3
      ∧ (finMemRoundOf4 42 : ℕ) = 3 ∧ (finMemRoundOf4 43 : ℕ) = 3 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- F-R4-1's hostile declaration on the four-round schedule: both IO coins declared at the
record-timestamp column `111`. -/
def hostileColumnChallenges3 (c : Fin 113) : Finset (Fin 10) :=
  if (c : ℕ) = 111 then
    insert ioGammaSlot (insert ioPoleSlot
      (finComputeRoundChalOf4 canonicalPlacement3 (finComputeRoundOf4 c)))
  else finComputeRoundChalOf4 canonicalPlacement3 (finComputeRoundOf4 c)

/-- **NEGATIVE CONTROL.**  It fails `columns_commit_before_sampling`: no
`StagedChip K 4 nockChronologyIO3` with `schedule := finComputeSchedule4` can carry it. -/
theorem b264_hostile3_fails_commit_before_sampling :
    ¬ ∀ c : Fin 113, ∀ j ∈ hostileColumnChallenges3 c,
      nockChronologyIO3.usableByColumnOf (finComputeSchedule4.roundOf c) j := by
  intro h
  have h111 := h 111 ioGammaSlot (by simp [hostileColumnChallenges3])
  simp only [ChallengeChronology.usableByColumnOf, nockChronologyIO3, finComputeSchedule4] at h111
  have : (nockSampledAfterIO3 ioGammaSlot : ℕ) = 2 := by decide
  have h2 : (finComputeRoundOf4 111 : ℕ) = 2 := by decide
  omega

/-- The memory twin: the pole declared at the memory record timestamp `53`. -/
theorem b264_hostile3_memory_fails_commit_before_sampling :
    ¬ ∀ c : Fin 55, ∀ j ∈ (if (c : ℕ) = 53 then insert ioPoleSlot
        (finMemRoundChalOf4 canonicalPlacement3 (finMemRoundOf4 c))
      else finMemRoundChalOf4 canonicalPlacement3 (finMemRoundOf4 c)),
      nockChronologyIO3.usableByColumnOf (finMemorySchedule4.roundOf c) j := by
  intro h
  have h53 := h 53 ioPoleSlot (by simp)
  simp only [ChallengeChronology.usableByColumnOf, nockChronologyIO3, finMemorySchedule4] at h53
  have : (nockSampledAfterIO3 ioPoleSlot : ℕ) = 2 := by decide
  have h2 : (finMemRoundOf4 53 : ℕ) = 2 := by decide
  omega

/-- **POSITIVE CONTROL on the instrument**: the honest per-round declaration of `computeChip3`
passes the same field (it is the chip's own `columns_commit_before_sampling`). -/
theorem b264_honest3_passes_commit_before_sampling {L : Type*} [Field L]
    (q : SegmentedRAPParams L) :
    ∀ c, ∀ j ∈ (computeChip3 canonicalPlacement3 q).columnChallenges c,
      nockChronologyIO3.usableByColumnOf
        ((computeChip3 canonicalPlacement3 q).schedule.roundOf c) j :=
  (computeChip3 canonicalPlacement3 q).columns_commit_before_sampling

/-- F-R4-1's declaration on the two-message schedule. -/
def hostileColumnChallenges2 (c : Fin 113) : Finset (Fin 10) :=
  if (c : ℕ) = 111 then
    insert (canonicalIOSlots.slot 0) (insert (canonicalIOSlots.slot 1)
      (finComputeColumnChallenges canonicalIOSlots c))
  else finComputeColumnChallenges canonicalIOSlots c

/-- **CONTRAST CONTROL.**  On `nockChronologyWithIO` (two messages) the hostile declaration
PASSES commit-before-sample — which is why F-R4-1's hostile chip existed there and cannot here. -/
theorem b264_hostile2_passes_commit_before_sampling :
    ∀ c : Fin 113, ∀ j ∈ hostileColumnChallenges2 c,
      (nockSampledAfterWithIO j : ℕ) < (finComputeRoundOf c : ℕ) := by
  intro c j hj
  by_cases hc : (c : ℕ) = 111
  · have h111 : (finComputeRoundOf c : ℕ) = 2 := by
      have : c = 111 := Fin.ext hc
      subst this; decide
    rw [h111]
    exact nockSampledAfterWithIO_lt_two j
  · simp only [hostileColumnChallenges2, if_neg hc] at hj
    exact finComputeColumns_commit_before_sampling canonicalIOSlots c j hj

/-- The tree's chips exclude both IO coins at the timestamps (in tree; restated as consumed). -/
theorem b264_shipped_chips_exclude_io_coins_at_timestamps {L : Type*} [Field L]
    (S : IOPlacement3) (q : SegmentedRAPParams L) (i : Fin 2) :
    S.slot i ∉ (computeChip3 S q).columnChallenges ((111 : Fin 113))
      ∧ S.slot i ∉ (memoryChip3 S q).columnChallenges ((53 : Fin 55)) :=
  ⟨computeChip3_io_data_undeclared S q 111 (by decide) (by decide) i,
    memoryChip3_io_data_undeclared S q 53 (by decide) (by decide) i⟩

/-- **Scope of "shipped".**  `computeChip3` / `memoryChip3` are the 113- / 55-column giga-RAP
substitute chips over `K`; `external_*_pole_is_disciplined` are about exactly them. -/
theorem b264_computeChip3_is_the_giga_chip {L : Type*} [Field L] (S : IOPlacement3)
    (q : SegmentedRAPParams L) :
    (computeChip3 S q).air = computeCombinedFiniteAIR 10 9 S.map
      ∧ (computeChip3 S q).air.numTraceCols = 113
      ∧ (memoryChip3 S q).air.numTraceCols = 55 :=
  ⟨rfl, rfl, rfl⟩

theorem b264_disciplined_is_about_computeChip3 {L : Type*} [Field L] (S : IOPlacement3)
    (q : SegmentedRAPParams L) :
    PoleDisciplined (computeChip3 S q) progIORecordCols (ioSlots S)
      ∧ PoleDisciplined (memoryChip3 S q) memIORecordCols (ioSlots S) :=
  ⟨external_prog_io_pole_is_disciplined S q, external_mem_io_pole_is_disciplined S q⟩

end P5

end

end Nock.RedTeam.Batch264

/-! `reach` traverses TYPE and PROOF TERM (`value? Every `throwError`
fails the build. -/

namespace Nock.RedTeam.Batch264.Audit

open Lean Meta Elab Command

partial def reach (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : List Name := roots
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        let used := ci.type.getUsedConstants
        let used := match ci.value? (allowOpaque := true) with
          | some v => used ++ v.getUsedConstants
          | none => used
        for u in used do
          if !seen.contains u then stack := u :: stack
  return seen

/-- `reach` with the constants in `opaques` treated as OPAQUE: an opaque constant is recorded
as reached and its TYPE is walked, but its value (definition body / proof term) is not. -/
partial def reachOpaque (env : Environment) (roots : List Name) (opaques : List Name) :
    NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : List Name := roots
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        let used := ci.type.getUsedConstants
        let used := if opaques.contains n then used else
          match ci.value? (allowOpaque := true) with
          | some v => used ++ v.getUsedConstants
          | none => used
        for u in used do
          if !seen.contains u then stack := u :: stack
  return seen

/-- Measured: it is the
single route from the three soundness roots to `finiteIO_complete_of_LIO`; the mask route
(`Batch457.masks_at_row_at → computeRealization → … → witness10 → witness10_exists`) is a
sub-route through it. -/
def completenessCut : Name := `Nock.NockVMROM.Thm54.SampledIOSameExecutionAssignment.witness10_exists

def completenessCutPerturbed : Name := `Nock.RedTeam.Batch457.masks_at_row_at

/-- The false-pass instrument: `value?` without `allowOpaque` skips every theorem body. -/
partial def reachTypesOnly (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : List Name := roots
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        let used := ci.type.getUsedConstants
        let used := match ci.value? with
          | some v => used ++ v.getUsedConstants
          | none => used
        for u in used do
          if !seen.contains u then stack := u :: stack
  return seen

def forbidden : List Name :=
  [ `Nock.NockVMROM.Thm54.BuildableChips.execution_lio,
    `Nock.NockVMROM.Thm54.BuildableChips.sampledWitness_accepts,
    `Nock.NockVMROM.Thm54.BuildableChips.finiteIOStrategy,
    `Nock.NockVMROM.Thm54.BuildableChips.executionRecords,
    `Nock.NockVMROM.Thm54.FiniteIO.finiteIO_complete_of_LIO,
    `Nock.NockVMROM.Thm54.GenericHonestData.execution_lio_of_requestNodup,
    `Nock.NockVMROM.Thm54.TraceGen.genSemantic_lio,
    `Nock.NockVMROM.Thm54.TraceGen.genSemantic_lmio,
    `Nock.NockVMROM.Thm54.BuildableNockExecution,
    `Nock.NockVMROM.Thm54.HonestCommitment.Data ]

def soundnessRoots : List Name :=
  [ `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.acceptance_outside_failure_implies_target,
    `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.optimizedFalseAcceptanceSet_subset_failure,
    `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.optimizedFalseAcceptance_probability_le ]

/-- Positive controls inside the capstone closure: the IO conclusion reaches `finiteIO_sound`
through the package field's `lio` and `shared_io`. -/
def expectedPresent : List Name :=
  [ `Nock.NockVMROM.Thm54.FiniteIO.finiteIO_sound,
    `Nock.NockVMROM.Thm54.FiniteIO.FiniteIOStrategy.lio,
    `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.shared_io ]

def redundancyRoot : Name := `Nock.NockVMROM.Thm54.IOCapstoneRedundancy.sharedIo_derivable

/-- `sharedIo_derivable` goes through the chip route, not the field. -/
def redundancyExpected : List Name :=
  [ `Nock.NockVMROM.Thm54.FiniteIO.finiteIO_sound,
    `Nock.NockVMROM.Thm54.IOChip.io_lio_of_satisfies,
    `Nock.NockVMROM.Thm54.IOChip.projWitness_accepts ]

def redundancyAbsent : List Name :=
  [ `Nock.NockVMROM.Thm54.FiniteIO.FiniteIOStrategy.lio,
    `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.shared_io ]

def controlRoot : Name := `Nock.NockVMROM.Thm54.BuildableChips.finiteIOStrategy

def controlExpected : List Name :=
  [ `Nock.NockVMROM.Thm54.FiniteIO.finiteIO_complete_of_LIO,
    `Nock.NockVMROM.Thm54.BuildableChips.execution_lio,
    `Nock.NockVMROM.Thm54.BuildableChips.sampledWitness_accepts ]

def internalPole : List Name :=
  [ `Nock.NockVMROM.Thm54.ChallengeVector.β,
    `Nock.NockVMROM.Thm54.PairedRecordCountedEvent.interCoins,
    `Nock.NockVMROM.Thm54.ChallengeVector.memoryInputs ]

/-- The external LogUp chain, record-level theorem to production composition. -/
def externalChain : List Name :=
  [ `Nock.NockVMROM.Thm54.FiniteIO.finiteIO_sound,
    `Nock.NockVMROM.Thm54.FiniteIO.FiniteIOStrategy.lio,
    `Nock.NockVMROM.Thm54.IOChip.io_lio_of_satisfies,
    `Nock.NockVMROM.Thm54.IOChip.projWitness_accepts,
    `Nock.NockVMROM.Thm54.IOCoinReconciliation.io_lio_of_satisfies_at_production_coins,
    `Nock.NockVMROM.Thm54.IOCapstoneRedundancy.sharedIo_derivable,
    `Nock.NockVMROM.Thm54.GigaIOThirdMessage.io_lio_of_giga3_satisfies,
    `Nock.NockVMROM.Thm54.GigaIOThirdMessageProduction.io_lio_of_giga3_satisfies_at_production_coins ]

def externalExpected : List Name :=
  [ `Nock.NockVMROM.Thm54.FiniteIO.IOCoins.pole,
    `Nock.NockVMROM.Thm54.FiniteIO.compress ]

def poleControlRoot : Name :=
  `Nock.NockVMROM.Thm54.IOCoinReconciliation.interCoins_logDeriv_is_a_fixed_point_test


/-! `Batch1351` keeps the earlier `witness10_exists` opaque-cut measurement as history; the cut now
covers only the DATA reading of `witness10` (`Classical.choose`).  The specification consumers
(`witness10_accepts`) must be reached only inside the Prop constructor arguments of
`OptimizedComputeRealizationAt.mk`, which are walked separately, and the structure's fields must
never be projected beyond the allowed two. -/

open Nock.NockVMROM.Thm54 in
/-- Negative-control probe: a declaration that really projects `canonical_satisfies`. -/
def probe_projects_canonical_satisfies {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K} {A : SampledIOSameExecutionAssignment R p}
    {hA : A.ComputeSampledObligations} {nodes : Fin R.problem.cfg.compRows → F}
    {b : Module.Basis (Fin 3) F K} {chalVal pubVal : ℕ → F} {h : ℕ}
    {orbit : Nock.NockVMROM.Thm54.StrictExtension.StrictOrbitDomain F 3 h}
    (r : OptimizedStrictPackage.OptimizedComputeRealizationAt A hA nodes b chalVal pubVal orbit) :=
  r.canonical_satisfies

def realizationStruct : Name :=
  `Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedComputeRealizationAt

/-- Uses of the realization structure in an expression: projection functions by field name,
`Expr.proj` by field index, and any other constant under the structure's namespace
(`mk`, `casesOn`, `rec`,...). -/
partial def realizationUses (e : Expr) : List String :=
  match e with
  | .const n _ =>
    if realizationStruct.isPrefixOf n && n != realizationStruct then [s!"const {n.getString!}"] else []
  | .proj s i b => (if s == realizationStruct then [s!"proj#{i}"] else []) ++ realizationUses b
  | .app f a => realizationUses f ++ realizationUses a
  | .lam _ t b _ => realizationUses t ++ realizationUses b
  | .forallE _ t b _ => realizationUses t ++ realizationUses b
  | .letE _ t v b _ => realizationUses t ++ realizationUses v ++ realizationUses b
  | .mdata _ b => realizationUses b
  | _ => []

/-- The only uses allowed in the reach set (`proj#1`/`proj#2` are the bodies of the two
projection functions; `nodes_injective` is field 1, `adjacent_orbit` field 2). -/
def allowedUses : List String :=
  ["const nodes_injective", "const adjacent_orbit", "proj#1", "proj#2", "const mk"]

def usesOf (env : Environment) (n : Name) : List String :=
  match env.find? n with
  | none => []
  | some ci =>
    realizationUses ci.type ++ (match ci.value? (allowOpaque := true) with
      | some v => realizationUses v | none => [])


/-- Constants of `e`, split into those outside and those inside the field arguments of
applications of the constructor `mk` (`np` parameters, `nf` Prop fields). -/
partial def splitPropArgs (mk : Name) (np nf : Nat) (e : Expr) : Array Name × Array Name :=
  let go (es : Array Expr) : Array Name × Array Name :=
    es.foldl (fun (m, p) x => let (m', p') := splitPropArgs mk np nf x; (m ++ m', p ++ p')) (#[], #[])
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if f.isConstOf mk && args.size ≥ np + nf then
      let (m, p) := go (args.extract 0 np ++ args.extract (np + nf) args.size)
      let pc := (args.extract np (np + nf)).foldl (fun acc x => acc ++ x.getUsedConstants) #[]
      (m, p ++ pc)
    else
      let (m, p) := go args
      let (m2, p2) := splitPropArgs mk np nf f
      (m ++ m2, p ++ p2)
  | .const n _ => (#[n], #[])
  | .lam _ t b _ => go #[t, b]
  | .forallE _ t b _ => go #[t, b]
  | .letE _ t v b _ => go #[t, v, b]
  | .mdata _ b => splitPropArgs mk np nf b
  | .proj _ _ b => splitPropArgs mk np nf b
  | _ => (#[], #[])

/-- Reach that does NOT walk the Prop constructor arguments of `mk` but RECORDS them: returns the
main reach and the set of recorded Prop-argument constants (to be walked separately). -/
partial def reachSkipProp (env : Environment) (roots : List Name) (mk : Name) (np nf : Nat) :
    NameSet × NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut recd : NameSet := {}
  let mut stack : List Name := roots
  while true do
    match stack with
    | [] => break
    | n :: r =>
      stack := r
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        let (mt, pt) := splitPropArgs mk np nf ci.type
        let (mv, pv) := match ci.value? (allowOpaque := true) with
          | some v => splitPropArgs mk np nf v
          | none => (#[], #[])
        for u in mt ++ mv do
          if !seen.contains u then stack := u :: stack
        for u in pt ++ pv do recd := recd.insert u
  return (seen, recd)

/-- The first use of the realization structure in `ns` outside the allowed ones. -/
def firstOffender (env : Environment) (ns : List Name) : Option (Name × String) :=
  ns.findSome? fun n => (usesOf env n).find? (fun u => !allowedUses.contains u) |>.map (n, ·)

/-- The retyped admissibility rule for the spec consumer `spec` from the roots' reach `full`. -/
def specAdmissible (env : Environment) (roots : List Name) (spec : Name) : Except String Unit := do
  let mk := realizationStruct ++ `mk
  let some (.ctorInfo cv) := env.find? mk | throw s!"{mk} missing"
  let (main, recd) := reachSkipProp env roots mk cv.numParams cv.numFields
  let full := reach env roots
  let propWalk := reach env recd.toList
  unless full.contains spec do throw s!"{spec} not reached at all (instrument suspect)"
  if main.contains spec then throw s!"{spec} reached outside the Prop constructor arguments"
  unless propWalk.contains spec do throw s!"{spec} not reached inside the recorded Prop arguments"
  let mut ns : List Name := []
  for n in full do ns := n :: ns
  if let some (n, u) := firstOffender env ns then
    throw s!"{n} uses the realization structure beyond the allowed projections ({u})"

def probeRoot : Name := `Nock.RedTeam.Batch264.Audit.probe_projects_canonical_satisfies

def specConsumer : Name := `Nock.NockVMROM.Thm54.SampledIOSameExecutionAssignment.witness10_accepts

end Nock.RedTeam.Batch264.Audit

open Nock.RedTeam.Batch264.Audit Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  for n in forbidden ++ soundnessRoots ++ expectedPresent ++ controlExpected ++ [controlRoot, completenessCut, completenessCutPerturbed, probeRoot, specConsumer]
      ++ redundancyExpected ++ redundancyAbsent ++ [redundancyRoot]
      ++ internalPole ++ externalChain ++ externalExpected ++ [poleControlRoot] do
    if env.find? n |>.isNone then throwError "[B264] AUDIT VACUOUS: unresolved name {n}"
  for r in soundnessRoots do
    let s := reach env [r]
    for f in forbidden do
      -- Measurement: `Batch1351`.
      if f == `Nock.NockVMROM.Thm54.FiniteIO.finiteIO_complete_of_LIO && s.contains f then
        let sO := reachOpaque env [r] [completenessCut]
        if sO.contains f then
          throwError "[B264 P6] FORBIDDEN {f} reached from {r} by a path avoiding {completenessCut}"
        let sNC := reachOpaque env [r] [completenessCutPerturbed]
        if !sNC.contains f then
          throwError "[B264 P6] NC FAILED: {f} unreached from {r} with {completenessCutPerturbed} opaque — instrument suspect"
        logInfo m!"[B264 P6] {f} reached from {r} ONLY through {completenessCut} (opaque walk: unreached, reach {sO.size}; NC with {completenessCutPerturbed} opaque: reached)"
        continue
      if s.contains f then throwError "[B264 P6] FORBIDDEN {f} present in {r}"
    for e in expectedPresent do
      if !s.contains e then throwError "[B264 P6] EXPECTED {e} absent from {r} — instrument suspect"
    logInfo m!"[B264 P6] {r} : reach {s.size}; {forbidden.length} forbidden absent; {expectedPresent.length} expected present"
    -- the retyped rule: spec consumer only inside Prop constructor args, fields never projected
    match specAdmissible env [r] specConsumer with
    | .ok () => logInfo m!"[B264 P6] {specConsumer} reached from {r} ONLY inside Prop constructor arguments of {realizationStruct}.mk; no field of it projected beyond {allowedUses}"
    | .error msg => throwError "[B264 P6] retyped rule FAILED for {r}: {msg}"
    -- negative control: the same rule on a probe that projects canonical_satisfies must fail
    match specAdmissible env [r, probeRoot] specConsumer with
    | .ok () => throwError "[B264 P6] NC FAILED: the projection probe was not rejected"
    | .error msg => logInfo m!"[B264 P6] NC (probe projecting canonical_satisfies) rejected: {msg}"
  let sR := reach env [redundancyRoot]
  for f in forbidden do
    if sR.contains f then throwError "[B264 P6] FORBIDDEN {f} present in {redundancyRoot}"
  for e in redundancyExpected do
    if !sR.contains e then throwError "[B264 P6] EXPECTED {e} absent from {redundancyRoot}"
  for a in redundancyAbsent do
    if sR.contains a then throwError "[B264 P6] {a} unexpectedly present in {redundancyRoot}"
  logInfo m!"[B264 P6] {redundancyRoot} : reach {sR.size}; forbidden absent; chip route present; package-field route absent"
  let c := reach env [controlRoot]
  for e in controlExpected do
    if !c.contains e then throwError "[B264 P6] POSITIVE CONTROL FAILED: {e} absent from {controlRoot}"
  logInfo m!"[B264 P6] POSITIVE CONTROL {controlRoot} : reach {c.size}; all {controlExpected.length} completeness constants present"
  let cNaive := reachTypesOnly env [controlRoot]
  if cNaive.contains `Nock.NockVMROM.Thm54.FiniteIO.finiteIO_complete_of_LIO then
    throwError "[B264 P6] naive traversal unexpectedly found the control constant"
  logInfo m!"[B264 P6] NAIVE types-only traversal of {controlRoot} : size {cNaive.size}; reports finiteIO_complete_of_LIO ABSENT (false pass reproduced)"
  for r in externalChain do
    let s := reach env [r]
    for f in internalPole do
      if s.contains f then throwError "[B264 P7] INTERNAL POLE {f} read by external {r}"
    for e in externalExpected do
      if !s.contains e then throwError "[B264 P7] {e} absent from {r} — instrument suspect"
    logInfo m!"[B264 P7] {r} : reach {s.size}; internal pole absent; sampled pole present"
  let pc := reach env [poleControlRoot]
  for f in [`Nock.NockVMROM.Thm54.ChallengeVector.β,
            `Nock.NockVMROM.Thm54.PairedRecordCountedEvent.interCoins] do
    if !pc.contains f then throwError "[B264 P7] POSITIVE CONTROL FAILED: {f} absent from {poleControlRoot}"
  logInfo m!"[B264 P7] POSITIVE CONTROL {poleControlRoot} : reach {pc.size}; ChallengeVector.β and interCoins present"

#print axioms Nock.RedTeam.Batch264.b264_bpRecords_requests_length
#print axioms Nock.RedTeam.Batch264.b264_bpRecords_responses_length
#print axioms Nock.RedTeam.Batch264.b264_ioFailureUnionBound_eight_closed
#print axioms Nock.RedTeam.Batch264.b264_rlc_event_proper
#print axioms Nock.RedTeam.Batch264.b264_exists_good_gamma
#print axioms Nock.RedTeam.Batch264.b264_logDeriv_event_proper
#print axioms Nock.RedTeam.Batch264.b264_exists_good_pole
#print axioms Nock.RedTeam.Batch264.b264_poleHit_event_proper
#print axioms Nock.RedTeam.Batch264.b264_union_bound_at_actual_counts
#print axioms Nock.RedTeam.Batch264.b264_joint_event_proper
#print axioms Nock.RedTeam.Batch264.b264_acceptance_inhabited_at_good_coins
#print axioms Nock.RedTeam.Batch264.b264_finiteIO_sound_hypotheses_inhabited
#print axioms Nock.RedTeam.Batch264.b264_bp_Ksz
#print axioms Nock.RedTeam.Batch264.b264_soundnessEvent_subset
#print axioms Nock.RedTeam.Batch264.b264_finiteIO_sound_of_soundnessEvent
#print axioms Nock.RedTeam.Batch264.b264_no_acceptance_in_poleHit
#print axioms Nock.RedTeam.Batch264.b264_soundnessEvent_card_le
#print axioms Nock.RedTeam.Batch264.b264_sampled_io_from_package_alone
#print axioms Nock.RedTeam.Batch264.b264_sampled_io_same_prop_across_traces
#print axioms Nock.RedTeam.Batch264.b264_io_event_good_of_acceptance
#print axioms Nock.RedTeam.Batch264.b264_accepted_outside_io_summand
#print axioms Nock.RedTeam.Batch264.b264_target_io_fields_from_package_and_pin
#print axioms Nock.RedTeam.Batch264.b264_io_summand_records_are_the_packages
#print axioms Nock.RedTeam.Batch264.b264_ioFailureUnionBound_empty
#print axioms Nock.RedTeam.Batch264.b264_qc_rows_satisfy_sampled_io_gates
#print axioms Nock.RedTeam.Batch264.b264_package_requests_row_count_ne
#print axioms Nock.RedTeam.Batch264.b264_chip_widths
#print axioms Nock.RedTeam.Batch264.b264_bp_row_count_obstruction
#print axioms Nock.RedTeam.Batch264.b264_rlc_is_paper_rlc
#print axioms Nock.RedTeam.Batch264.b264_compress_is_ldse_factor
#print axioms Nock.RedTeam.Batch264.b264_compress_at_neg_beta
#print axioms Nock.RedTeam.Batch264.b264_denomP_eval_is_prod_compress
#print axioms Nock.RedTeam.Batch264.b264_poleHit_iff_compress_zero
#print axioms Nock.RedTeam.Batch264.b264_endpoint_is_ldse_at_pole
#print axioms Nock.RedTeam.Batch264.b264_active_slot0
#print axioms Nock.RedTeam.Batch264.b264_active_slot1
#print axioms Nock.RedTeam.Batch264.b264_active_slot2
#print axioms Nock.RedTeam.Batch264.b264_activeRequestRecords_length
#print axioms Nock.RedTeam.Batch264.b264_encRec_width
#print axioms Nock.RedTeam.Batch264.b264_safeDenom_inactive
#print axioms Nock.RedTeam.Batch264.b264_safeDenom_active
#print axioms Nock.RedTeam.Batch264.b264_fold_rejects_active_zero_denominator
#print axioms Nock.RedTeam.Batch264.b264_fold_vacuous_at_double_pole_hit
#print axioms Nock.RedTeam.Batch264.b264_double_pole_hit_in_failure_event
#print axioms Nock.RedTeam.Batch264.b264_lio_iff_sigma_form
#print axioms Nock.RedTeam.Batch264.b264_lio_requests_nodup
#print axioms Nock.RedTeam.Batch264.b264_verifierGates_io_conjuncts
#print axioms Nock.RedTeam.Batch264.b264_finite_chip_has_ver_booleanity
#print axioms Nock.RedTeam.Batch264.b264_optimized_memory_has_ver_booleanity
#print axioms Nock.RedTeam.Batch264.b264_finite_prog_chip_gates
#print axioms Nock.RedTeam.Batch264.b264_optimized_compute_endpoint_buckets
#print axioms Nock.RedTeam.Batch264.b264_charBound_is_at_K
#print axioms Nock.RedTeam.Batch264.b264_ringChar_ext_eq_base
#print axioms Nock.RedTeam.Batch264.b264_timestamp_columns_round_two
#print axioms Nock.RedTeam.Batch264.b264_io_coins_message_two
#print axioms Nock.RedTeam.Batch264.b264_io_coin_columns_round_three
#print axioms Nock.RedTeam.Batch264.b264_hostile3_fails_commit_before_sampling
#print axioms Nock.RedTeam.Batch264.b264_hostile3_memory_fails_commit_before_sampling
#print axioms Nock.RedTeam.Batch264.b264_honest3_passes_commit_before_sampling
#print axioms Nock.RedTeam.Batch264.b264_hostile2_passes_commit_before_sampling
#print axioms Nock.RedTeam.Batch264.b264_shipped_chips_exclude_io_coins_at_timestamps
#print axioms Nock.RedTeam.Batch264.b264_computeChip3_is_the_giga_chip
#print axioms Nock.RedTeam.Batch264.b264_disciplined_is_about_computeChip3
