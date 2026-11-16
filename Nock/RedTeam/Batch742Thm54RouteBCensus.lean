/-
  Nock/RedTeam/Batch742Thm54RouteBCensus.lean

* **(A) The route-B census is `zipPairs` at a pre-`z` target.**  `reqTgt P Qm T j` reads the
    target off a FIXED map `T : MState → ℕ → Noun` (the package's request nouns: root for
    `read_root`, child for `verify_child`) at the row's state (selector columns `0..2`) and at
    `natLift reqIdx` (column `181`).  Both are round-0 columns, so the census, its bad seeds and
    its lifted event are `PreZReads` (`reqPairEvent_preZReads`), the staged model meets the same
    fixed event (`reqPairEvent_adaptive_eq`), the card is the positional `M·(2Λ − 1)·|𝕂|¹⁰`
    (`reqPairEvent_card_le`), and the H1.3 conjunct applies verbatim
    (`reqPair_conjunct`).  `#pairs = M`, independent of the trace.
  * **(B) The key exclusion (Q1).**  Outside the consumed failure event, on any accepted trace pair:
    two `ver = 1` memory rows with the same `reqIdx` are the same row (`ver_reqIdx_injective`);
    every `ver = 1` row names an active request (`Batch672.memory_row_bound`), and every active
    request is named by a `ver = 1` row whose whole ten-slot record is that request's
    (`request_named_by_row`).  So `reqIdx` is a bijection between `ver = 1` rows and active request
    slots; there is no adaptive choice left in the pairing.
  * **(C) Figures (Q3).**  The row-indexed census is the positional one (`457S² + 404S + 28`,
    `PreSeedCensusFigures.hostile_soundness_formR_pair_at_two_pow_31/_32`): 122 / 120 / 123.
    The request-indexed form with `3N` pairs gives `465S² + 404S + 28`
    (`hostile_soundness_formR_req3_at_two_pow_31/_32`); with root AND child per request (`6N`
    pairs) `477S² + 404S + 28` (`…_req6_…`); both hold 122 / 120, and 123 at the paper
    configuration (`hostile_soundness_at_paper_configuration_req6`).  The `S²` coefficient ceiling
    for `b = 184 − 2r` is `486` (`coefficient_ceiling`).  At the hostile workload majorant
    (`HostileWorkloadMajorant.p8WorkHostile`, which alone costs the paper configuration one bit)
    the `6N` form still gives 122 / 120, and 122 at the paper configuration
    (`hostile_soundness_majorant_req6_at_two_pow_31/_32`,
    `hostile_soundness_at_paper_configuration_majorant_req6`).

  -- the paper
-/
import Nock.NockVMROM.Thm54.PreSeedCensus
import Nock.NockVMROM.Thm54.PreSeedCensusFigures
import Nock.RedTeam.Batch672Thm54ExponentCarrierBinding
import Nock.NockVMROM.Thm54.HostileWorkloadMajorant

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Nock.RedTeam.Batch742

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedStaging
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding

noncomputable section

/-! ## (A) The route-B census: `zipPairs` at a target read off `(state, reqIdx)` -/

section RouteB

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem reqIdxCol_round_zero : memoryColRound OptimizedMemoryGateBasis.reqIdxCol = 0 := by
  decide

/-- Row `i`'s committed request index (`reqIdx`, base column `181`). -/
def preReqIdxRow (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : F :=
  (preEnv P Qm i).trace OptimizedMemoryGateBasis.reqIdxCol

/-- The request index at aggregate-BFS position `j` (1-indexed, `preLbl`'s convention). -/
def preReqIdx (Qm : Fin P.memoryChip.rap.w → F[X]) (j : ℕ) : F :=
  if hj : j - 1 < P.optimized.family.problem.cfg.memRows then
    preReqIdxRow P Qm ⟨j - 1, hj⟩
  else
    preReqIdxRow P Qm ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩

theorem preReqIdx_congr {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hag : PreZAgreeOn (memCC P) Qm Qm') : preReqIdx P Qm = preReqIdx P Qm' := by
  funext j
  unfold preReqIdx preReqIdxRow
  split_ifs <;> exact preEnv_trace_congr P hag _ _ reqIdxCol_round_zero

/-- **The route-B target**: a fixed map `T` (reads neither trace nor coins) evaluated at the
row's pre-`z` state and at the natural lift of its pre-`z` request index. -/
def reqTgt (Qm : Fin P.memoryChip.rap.w → F[X]) (T : MState → ℕ → Noun) : ℕ → Noun :=
  fun j => T (preLbl P Qm j).1 (RecordCarrier.natLift (preReqIdx P Qm j))

theorem reqTgt_congr {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hag : PreZAgreeOn (memCC P) Qm Qm') (T : MState → ℕ → Noun) :
    reqTgt P Qm T = reqTgt P Qm' T := by
  funext j
  simp only [reqTgt, preLbl_congr P hag, preReqIdx_congr P hag]

/-- **The route-B pair event**: H1.3's `pairEvent` at the target `reqTgt`. -/
def reqPairEvent (q Λ : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) (T : MState → ℕ → Noun) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  pairEvent P q Λ Qm (reqTgt P Qm T)

/-- **`#pairs = M`**, for every trace (rule 8(b): the count is a configuration constant). -/
theorem reqPairs_length (q : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) (T : MState → ℕ → Noun) :
    (zipPairs P q Qm (reqTgt P Qm T)).length = P.optimized.family.problem.cfg.memRows :=
  zipPairs_length P q Qm _

/-- **Card `≤ M·(2Λ − 1)·|𝕂|¹⁰`** at every `Qm`. -/
theorem reqPairEvent_card_le (q Λ : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X])
    (T : MState → ℕ → Noun) :
    (reqPairEvent (K := K) P q Λ Qm T).card ≤
      P.optimized.family.problem.cfg.memRows * (2 * Λ - 1) * Fintype.card K ^ 10 :=
  pairEvent_card_le P q Λ Qm _

/-- **Cylinder, trace side**: the route-B event reads only the pre-`z` columns of `Qm`. -/
theorem reqPairEvent_preZReads (q Λ : ℕ) (T : MState → ℕ → Noun) :
    PreZReadsFnOn (memCC P) (fun Qm => reqPairEvent (K := K) P q Λ Qm T) := by
  intro Qm Qm' hag
  have h : preZNoun P q Qm = preZNoun P q Qm' :=
    funext fun i => preZNoun_preZReads P q i Qm Qm' hag
  simp only [reqPairEvent, pairEvent, zipPairs, h, reqTgt_congr P hag T]
  rfl

/-- **Staged model**: a prover that fixes the round-0 columns (selectors, `atom`, `reqIdx`) as
`Qm₀` and picks every other column after the coins meets the same fixed event. -/
theorem reqPairEvent_adaptive_eq (q Λ : ℕ) (T : MState → ℕ → Noun)
    (Qm₀ : Fin P.memoryChip.rap.w → F[X])
    (σ : OptimizedProductionChallengeTuple K F → Fin P.memoryChip.rap.w → F[X])
    (hσ : ∀ c, PreZAgreeOn (memCC P) (σ c) Qm₀) :
    Finset.univ.filter (fun c => nprSeed c.1 ∈
        pairBadSeeds (K := K) Λ (zipPairs P q (σ c) (reqTgt P (σ c) T)))
      = reqPairEvent P q Λ Qm₀ T := by
  ext c
  have h : preZNoun P q (σ c) = preZNoun P q Qm₀ :=
    funext fun i => preZNoun_preZReads P q i (σ c) Qm₀ (hσ c)
  simp only [reqPairEvent, pairEvent, zipPairs]
  erw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, h, reqTgt_congr P (hσ c) T]

/-- **The conjunct at the route-B target** (`accepted_outside_pairEvent_decoded_eq` verbatim):
outside the event, a decoded node whose fingerprint equals its request's target IS the target. -/
theorem reqPair_conjunct (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    {q Λ : ℕ} (hq0 : 0 < q) (hqp : q ≤ ringChar K) (T : MState → ℕ → Noun)
    (hout : c ∉ reqPairEvent P q Λ (honestQm P c Qm) T)
    {i : ℕ} (hi : i ∈ List.range' 1 P.optimized.family.problem.cfg.memRows)
    (hwin : (preZNoun P q (honestQm P c Qm) i).leaves ≤ Λ)
    (htwin : (reqTgt P (honestQm P c Qm) T i).leaves ≤ Λ)
    (htgt : ∀ k ∈ (reqTgt P (honestQm P c Qm) T i).leafList, k < q)
    (hbind : GlobalCarryRecognizer.enc (nprSeed c.1)
        (decodeNoun q (buildTF P.optimized.family.problem.cfg.kMem (foM P (honestQm P c Qm) c)
          (lblM P (honestQm P c Qm) c) P.optimized.family.problem.cfg.memRows i)) =
      GlobalCarryRecognizer.enc (nprSeed c.1) (reqTgt P (honestQm P c Qm) T i)) :
    decodeNoun q (buildTF P.optimized.family.problem.cfg.kMem (foM P (honestQm P c Qm) c)
        (lblM P (honestQm P c Qm) c) P.optimized.family.problem.cfg.memRows i) =
      reqTgt P (honestQm P c Qm) T i :=
  accepted_outside_pairEvent_decoded_eq P c Qm hsat hq0 hqp _ hout hi hwin htwin htgt hbind

/-- **Non-vacuity of the indexing (positive control)**: the route-B target genuinely reads the
request index — two traces that differ only in what `natLift reqIdx` names at position `j` get
different targets whenever `T` separates the two indices. -/
theorem reqTgt_reads_reqIdx (Qm Qm' : Fin P.memoryChip.rap.w → F[X]) (T : MState → ℕ → Noun)
    (j : ℕ) (hst : (preLbl P Qm j).1 = (preLbl P Qm' j).1)
    (hT : T (preLbl P Qm j).1 (RecordCarrier.natLift (preReqIdx P Qm j)) ≠
      T (preLbl P Qm j).1 (RecordCarrier.natLift (preReqIdx P Qm' j))) :
    reqTgt P Qm T j ≠ reqTgt P Qm' T j := by
  simp only [reqTgt, ← hst]
  exact hT

end RouteB

/-! ## (B) The key exclusion: `reqIdx` is a bijection between `ver = 1` rows and requests -/

section Exclusion

open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
  (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)

/-- Distinct blocks of a `Nodup` flattened `ofFn` share no element. -/
theorem eq_of_mem_flatten_ofFn_nodup {α : Type*} {n : ℕ} (f : Fin n → List α)
    (h : (List.ofFn f).flatten.Nodup) {i i' : Fin n} {x : α}
    (hx : x ∈ f i) (hx' : x ∈ f i') : i = i' := by
  rw [List.nodup_flatten, List.pairwise_ofFn] at h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h.2 hlt hx hx'
  · exact h.2 hlt hx' hx

/-- A `ver = 1` row's record is in its own response block. -/
theorem rowRecord_mem_rowResponses (i : Fin (OptimizedMemoryHostileAccumulator.rows P))
    (hver : (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i).trace 39 = 1) :
    OptimizedMemoryHostileAccumulator.rowRecord
        (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i)
        (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i) ∈
      OptimizedMemoryHostileAccumulator.rowResponses
        (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i)
        (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i) := by
  simp [OptimizedMemoryHostileAccumulator.rowResponses,
    OptimizedMemoryHostileAccumulator.rowResponseTerms, hver]

/-- Active request slots are separated by their exponents (`S` strictly increases by the arity). -/
theorem expOf_injective
    {a a' : Fin (rows P)} {j j' : Fin 3}
    (hact : activeMask (rowEnv P Qc a) j = 1) (hact' : activeMask (rowEnv P Qc a') j' = 1)
    (h : expOf P Qc a j = expOf P Qc a' j') : a = a' ∧ j = j' := by
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (expOf_lt_of_row_lt P Qc hlt j j' hact))
  · subst heq
    refine ⟨rfl, Fin.ext ?_⟩
    unfold expOf at h
    omega
  · exact absurd h.symm (Nat.ne_of_lt (expOf_lt_of_row_lt P Qc hgt j' j hact'))

/-- Every `ver = 1` row's record is an active request's record (all ten slots; `hostile_LIO'`). -/
theorem row_record_is_request {Ksz : ℕ}
    (S : OptimizedFullStrictThm54Statement P)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hio : c.2.1 ∉ FiniteIO.IOFailureEvent (OptimizedHostileIOAssembly.hostileRecords P Qc Qm))
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequests P Qc).length)
    (hKresp : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).length ≤ Ksz)
    (i : Fin (OptimizedMemoryHostileAccumulator.rows P))
    (hver : (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i).trace 39 = 1) :
    ∃ (a : Fin (rows P)) (j : Fin 3), activeMask (rowEnv P Qc a) j = 1 ∧
      OptimizedMemoryHostileAccumulator.rowRecord
          (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i)
          (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i) =
        rowRecord (rowEnv P Qc a) j := by
  have hlio := optimizedFullStrict_hostile_LIO_historical P Qc Qm c hacc hgood hio hchar hKp hKreq hKresp
  have hresp : OptimizedMemoryHostileAccumulator.rowRecord
      (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i)
      (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i) ∈
      OptimizedMemoryHostileAccumulator.hostileResponses P Qm :=
    List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, rowRecord_mem_rowResponses P Qm i hver⟩
  exact OptimizedHostileIOAssembly.mem_hostileRequests P Qc ((List.Perm.mem_iff hlio.2.2).2 hresp)

/-- An active request's exponent is below the characteristic of `𝔽`. -/
theorem expOf_lt_ringChar {Ksz : ℕ} (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequests P Qc).length)
    {a : Fin (rows P)} {j : Fin 3} (hact : activeMask (rowEnv P Qc a) j = 1) :
    expOf P Qc a j < ringChar F := by
  have hle : expOf P Qc a j ≤ (hostileRequests P Qc).length := by
    rw [← totalRequests_eq_length P Qc hsat hchar]
    exact expOf_le_total P Qc a j hact
  rw [Algebra.ringChar_eq F K]
  exact lt_of_le_of_lt (le_trans hle hKreq.2) hKp

/-- **Q1's key exclusion (compiled).**  Outside the consumed failure event, two `ver = 1` memory
rows of an accepted trace pair with the same committed `reqIdx` are the same row.  Proof: each
row's ten-slot record is an active request's (`hostile_LIO'`); slot `9` makes the two requests'
exponents equal in `𝔽` and, below the characteristic, in `ℕ`; exponents separate active slots
(`expOf_injective`), so the two records are one request record; the response list is `Nodup`
(`IO.LIO`), so one row. -/
theorem ver_reqIdx_injective {Ksz : ℕ}
    (S : OptimizedFullStrictThm54Statement P)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hio : c.2.1 ∉ FiniteIO.IOFailureEvent (OptimizedHostileIOAssembly.hostileRecords P Qc Qm))
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequests P Qc).length)
    (hKresp : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).length ≤ Ksz)
    (i i' : Fin (OptimizedMemoryHostileAccumulator.rows P))
    (hv : (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i).trace 39 = 1)
    (hv' : (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i').trace 39 = 1)
    (heq : (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i).trace
        OptimizedMemoryGateBasis.reqIdxCol =
      (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i').trace
        OptimizedMemoryGateBasis.reqIdxCol) :
    i = i' := by
  have hsat := hacc.compute_satisfies
  have hlio := optimizedFullStrict_hostile_LIO_historical P Qc Qm c hacc hgood hio hchar hKp hKreq hKresp
  obtain ⟨a, j, hact, hr⟩ :=
    row_record_is_request P Qc Qm c S hacc hgood hio hchar hKp hKreq hKresp i hv
  obtain ⟨a', j', hact', hr'⟩ :=
    row_record_is_request P Qc Qm c S hacc hgood hio hchar hKp hKreq hKresp i' hv'
  -- slot 9 of the two records
  have h9 := congrFun hr 9
  have h9' := congrFun hr' 9
  rw [Batch672.compute_slot9_eq_expOf P Qc hsat hchar a j] at h9
  rw [Batch672.compute_slot9_eq_expOf P Qc hsat hchar a' j'] at h9'
  have hF : ((expOf P Qc a j : ℕ) : F) = ((expOf P Qc a' j' : ℕ) : F) := by
    apply (algebraMap F K).injective
    rw [← h9, ← h9']
    simp [OptimizedMemoryHostileAccumulator.rowRecord, OptimizedMemoryGateBasis.reqIdxCol] at heq ⊢
    rw [heq]
  haveI : CharP F (ringChar F) := ringChar.charP F
  have hN : expOf P Qc a j = expOf P Qc a' j' :=
    CharP.natCast_injOn_Iio F (ringChar F)
      (Set.mem_Iio.2 (expOf_lt_ringChar P Qc hsat hchar hKp hKreq hact))
      (Set.mem_Iio.2 (expOf_lt_ringChar P Qc hsat hchar hKp hKreq hact')) hF
  obtain ⟨rfl, rfl⟩ := expOf_injective P Qc hact hact' hN
  -- the two rows serve one record; responses are `Nodup`
  have hrec : OptimizedMemoryHostileAccumulator.rowRecord
      (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i)
      (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i) ∈
      OptimizedMemoryHostileAccumulator.rowResponses
        (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i')
        (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i') := by
    rw [hr, ← hr']
    exact rowRecord_mem_rowResponses P Qm i' hv'
  exact eq_of_mem_flatten_ofFn_nodup _ hlio.2.1
    (rowRecord_mem_rowResponses P Qm i hv) hrec

/-- **Surjectivity**: every active request slot is named by a `ver = 1` row that serves exactly
that request's record (hence carries its `reqIdx`). -/
theorem request_named_by_row {Ksz : ℕ}
    (S : OptimizedFullStrictThm54Statement P)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hio : c.2.1 ∉ FiniteIO.IOFailureEvent (OptimizedHostileIOAssembly.hostileRecords P Qc Qm))
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequests P Qc).length)
    (hKresp : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).length ≤ Ksz)
    (a : Fin (rows P)) (j : Fin 3) (hact : activeMask (rowEnv P Qc a) j = 1) :
    ∃ i : Fin (OptimizedMemoryHostileAccumulator.rows P),
      (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i).trace 39 = 1 ∧
      OptimizedMemoryHostileAccumulator.rowRecord
          (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i)
          (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i) =
        rowRecord (rowEnv P Qc a) j ∧
      (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i).trace
          OptimizedMemoryGateBasis.reqIdxCol = ((expOf P Qc a j : ℕ) : F) := by
  have hsat := hacc.compute_satisfies
  have hlio := optimizedFullStrict_hostile_LIO_historical P Qc Qm c hacc hgood hio hchar hKp hKreq hKresp
  have hreq : rowRecord (rowEnv P Qc a) j ∈ hostileRequests P Qc := by
    simp only [hostileRequests, List.mem_flatten, List.mem_ofFn]
    refine ⟨_, ⟨a, rfl⟩, ?_⟩
    simp only [rowRequests, List.mem_filterMap, List.mem_finRange, true_and]
    exact ⟨j, by simp [hact]⟩
  have hresp := (List.Perm.mem_iff hlio.2.2).1 hreq
  simp only [OptimizedMemoryHostileAccumulator.hostileResponses, List.mem_flatten,
    List.mem_ofFn] at hresp
  obtain ⟨l, ⟨i, rfl⟩, hl⟩ := hresp
  simp only [OptimizedMemoryHostileAccumulator.rowResponses,
    OptimizedMemoryHostileAccumulator.rowResponseTerms] at hl
  split_ifs at hl with hver
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hl
    refine ⟨i, hver, hl.symm, ?_⟩
    have h9 := congrFun hl 9
    rw [Batch672.compute_slot9_eq_expOf P Qc hsat hchar a j] at h9
    apply (algebraMap F K).injective
    simpa [OptimizedMemoryHostileAccumulator.rowRecord, OptimizedMemoryGateBasis.reqIdxCol]
      using h9.symm
  · simp at hl

end Exclusion

/-! ## (C) Figures with the route-B summand -/

section Figures

open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.PreSeedCensusFigures

/-- Request-indexed census, one pair per request: `3N` pairs. -/
def req3Work (R Λ : ℕ) : ℕ := 3 * R * (2 * Λ - 1)

/-- Request-indexed census, root and child per request: `6N` pairs. -/
def req6Work (R Λ : ℕ) : ℕ := 6 * R * (2 * Λ - 1)

theorem two_hostileTotalWork_req3_le_of_size (S R M Λ A p8Work : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    2 * (hostileTotalWork p8Work R M + req3Work R Λ) ≤ 465 * (S * S) + 404 * S + 28 := by
  have h := two_hostileTotalWork_le_of_size_formR_prePair S R M Λ A p8Work hR hM hΛ hA hp8
  have hp : req3Work R Λ ≤ 3 * S * (2 * S) := by
    unfold req3Work
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 3 hR) (by omega)
  nlinarith

theorem two_hostileTotalWork_req6_le_of_size (S R M Λ A p8Work : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    2 * (hostileTotalWork p8Work R M + req6Work R Λ) ≤ 477 * (S * S) + 404 * S + 28 := by
  have h := two_hostileTotalWork_le_of_size_formR_prePair S R M Λ A p8Work hR hM hΛ hA hp8
  have hp : req6Work R Λ ≤ 6 * S * (2 * S) := by
    unfold req6Work
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 6 hR) (by omega)
  nlinarith

theorem sizeWork_lt_cardK (a r b : ℕ) (ha : a ≤ 486) (hr : 4 ≤ r) (hb : 2 * r + b = 184) :
    (a * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ b < 2 * cardKGold := by
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ b = 2 ^ 184 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have h2 : (2 : ℕ) ^ r * 2 ^ b ≤ 2 ^ 180 := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ b ≤ 2 ^ 176 := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (a * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ b
      = a * (2 ^ r * 2 ^ r * 2 ^ b) + 404 * (2 ^ r * 2 ^ b) + 28 * 2 ^ b := by ring
    _ ≤ 486 * 2 ^ 184 + 404 * 2 ^ 180 + 28 * 2 ^ 176 := by
        rw [h1]
        exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ ha)
          (Nat.mul_le_mul_left 404 h2)) (Nat.mul_le_mul_left 28 h3)
    _ < 2 * cardKGold := by norm_num

/-- The `S²` coefficient of the doubled numerator that keeps `b = 184 − 2r` is at most `486`
(`487` fails): the route-B forms have slack `21` (`465`) and `9` (`477`); the positional `457`
has `29`. -/
theorem coefficient_ceiling :
    ¬ ((487 * 2 ^ 184 + 404 * 2 ^ 180 + 28 * 2 ^ 176 : ℕ) < 2 * cardKGold) := by norm_num

theorem hostile_soundness_formR_req3_at_row_budget (r b R M Λ A p8Work : ℕ)
    (hr : 4 ≤ r) (hb : 2 * r + b = 184)
    (hR : R ≤ 2 ^ r) (hM : M ≤ 2 ^ r) (hΛ : Λ ≤ 2 ^ r) (hA : A ≤ 2 ^ r)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
        + (req3Work R Λ : ℚ) / (cardKGold : ℚ)
      < 1 / (2 : ℚ) ^ b := by
  refine hostileBound_add_lt_of_totalWork _ _ _ _ _ ?_
  have h := two_hostileTotalWork_req3_le_of_size (2 ^ r) R M Λ A p8Work hR hM hΛ hA hp8
  have h' := sizeWork_lt_cardK 465 r b (by norm_num) hr hb
  have : 2 * ((hostileTotalWork p8Work R M + req3Work R Λ) * 2 ^ b)
      ≤ (465 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ b := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ h
  omega

theorem hostile_soundness_formR_req6_at_row_budget (r b R M Λ A p8Work : ℕ)
    (hr : 4 ≤ r) (hb : 2 * r + b = 184)
    (hR : R ≤ 2 ^ r) (hM : M ≤ 2 ^ r) (hΛ : Λ ≤ 2 ^ r) (hA : A ≤ 2 ^ r)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
        + (req6Work R Λ : ℚ) / (cardKGold : ℚ)
      < 1 / (2 : ℚ) ^ b := by
  refine hostileBound_add_lt_of_totalWork _ _ _ _ _ ?_
  have h := two_hostileTotalWork_req6_le_of_size (2 ^ r) R M Λ A p8Work hR hM hΛ hA hp8
  have h' := sizeWork_lt_cardK 477 r b (by norm_num) hr hb
  have : 2 * ((hostileTotalWork p8Work R M + req6Work R Λ) * 2 ^ b)
      ≤ (477 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ b := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ h
  omega

/-- **122 at `2^31`, request-indexed (`3N` pairs).** -/
theorem hostile_soundness_formR_req3_at_two_pow_31 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
        + (req3Work R Λ : ℚ) / (cardKGold : ℚ) < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_formR_req3_at_row_budget 31 122 R M Λ A p8Work (by norm_num) (by norm_num)
    hR hM hΛ hA hp8

/-- **120 at `2^32`, request-indexed (`3N` pairs).** -/
theorem hostile_soundness_formR_req3_at_two_pow_32 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
        + (req3Work R Λ : ℚ) / (cardKGold : ℚ) < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_formR_req3_at_row_budget 32 120 R M Λ A p8Work (by norm_num) (by norm_num)
    hR hM hΛ hA hp8

/-- **122 at `2^31`, request-indexed root and child (`6N` pairs).** -/
theorem hostile_soundness_formR_req6_at_two_pow_31 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
        + (req6Work R Λ : ℚ) / (cardKGold : ℚ) < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_formR_req6_at_row_budget 31 122 R M Λ A p8Work (by norm_num) (by norm_num)
    hR hM hΛ hA hp8

/-- **120 at `2^32`, request-indexed root and child (`6N` pairs).** -/
theorem hostile_soundness_formR_req6_at_two_pow_32 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
        + (req6Work R Λ : ℚ) / (cardKGold : ℚ) < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_formR_req6_at_row_budget 32 120 R M Λ A p8Work (by norm_num) (by norm_num)
    hR hM hΛ hA hp8

/-- The `6N` summand at the paper configuration (`N = Λ = 2^31`) is below `2^66`. -/
theorem req6Work_at_paper_configuration : req6Work (2 ^ 31) (2 ^ 31) ≤ 2 ^ 66 := by
  unfold req6Work; norm_num

/-- **123 at the paper configuration with the `6N` route-B summand** (the largest route-B
form; `M`- and `3N`-pair forms are below it). -/
theorem hostile_soundness_at_paper_configuration_req6 (p8Work ioWork pw : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) (hpw : pw ≤ 2 ^ 66) :
    goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) + (pw : ℚ) / (cardKGold : ℚ)
      < 1 / (2 : ℚ) ^ 123 := by
  rw [goldilocksHostileFailureBound_eq]
  have hts := timestampCollisionBound_at_paper_configuration
  have hwr := walkAndTilingBound_at_paper_configuration
  have hinter :
      ((FiniteIO.ioFailureUnionBound 10 (2 ^ 31) (2 ^ 31) cardKGold
          + cardKGold * 2 ^ 31 : ℕ) : ℚ) / (cardKGold : ℚ) ^ 2
      = ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ) := by
    rw [ioFailureUnionBound_ten]
    have hnat : 36 * 2 ^ 31 * 2 ^ 31 + 4 * 2 ^ 31 = 9 * 2 ^ 64 + 2 ^ 33 := by norm_num
    rw [hnat]
    have hk : (cardKGold : ℚ) ≠ 0 := by norm_num
    field_simp
    ring
  have hmaj :
      ((2 : ℚ) ^ 60 + (2 : ℚ) ^ 65 + (2 : ℚ) ^ 36) / (cardKGold : ℚ)
        + ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2
        + ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ)
        + (2 : ℚ) ^ 66 / (cardKGold : ℚ)
        < 1 / (2 : ℚ) ^ 123 := by
    norm_num
  have hp8' : (p8Work : ℚ) ≤ (2 : ℚ) ^ 60 := by exact_mod_cast hp8
  have hts' : (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ)
      ≤ (2 : ℚ) ^ 65 := by exact_mod_cast hts
  have hwr' : (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) ≤ (2 : ℚ) ^ 36 := by
    exact_mod_cast hwr
  have hio' : (ioWork : ℚ) ≤ (16 : ℚ) ^ 65 := by exact_mod_cast hio
  have hpw' : (pw : ℚ) ≤ (2 : ℚ) ^ 66 := by exact_mod_cast hpw
  calc
    (p8Work + OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) +
          pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) /
          (cardKGold : ℚ)
        + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
        + ((FiniteIO.ioFailureUnionBound 10 (2 ^ 31) (2 ^ 31) cardKGold
            + cardKGold * 2 ^ 31 : ℕ) : ℚ) / (cardKGold : ℚ) ^ 2
        + (pw : ℚ) / (cardKGold : ℚ)
        = ((p8Work : ℚ) +
            (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ) +
            (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ)) /
            (cardKGold : ℚ)
          + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
          + ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ)
          + (pw : ℚ) / (cardKGold : ℚ) := by
            rw [hinter]
    _ ≤ ((2 : ℚ) ^ 60 + (2 : ℚ) ^ 65 + (2 : ℚ) ^ 36) / (cardKGold : ℚ)
          + ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2
          + ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ)
          + (2 : ℚ) ^ 66 / (cardKGold : ℚ) := by
            gcongr
    _ < 1 / (2 : ℚ) ^ 123 := hmaj

/-! ### At the hostile workload majorant (steps 1–2's closed form, `HostileWorkloadMajorant`)

`p8WorkHostile` already costs the paper configuration one bit (`123 → 122`,
`HostileWorkloadMajorant.not_123_at_paper_configuration_majorant`).  The route-B summand, in its
largest (`6N`) form, does not cost another. -/

open Nock.NockVMROM.Thm54.HostileWorkloadMajorant in
theorem two_hostileTotalWork_majorant_req6_le (S N M Λ : ℕ)
    (hN : N ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) :
    2 * (hostileTotalWork (p8WorkHostile N M) N M + req6Work N Λ)
      ≤ 477 * (S * S) + 150 * S + 288 := by
  have h := two_hostileTotalWork_le_p8WorkHostile_prePair S N M hN hM
  have hp : req6Work N Λ ≤ 6 * S * (2 * S) := by
    unfold req6Work
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 6 hN) (by omega)
  nlinarith

open Nock.NockVMROM.Thm54.HostileWorkloadMajorant in
theorem hostile_soundness_majorant_req6_at_row_budget (r b N M Λ : ℕ)
    (hr : 4 ≤ r) (hb : 2 * r + b = 184)
    (hN : N ≤ 2 ^ r) (hM : M ≤ 2 ^ r) (hΛ : Λ ≤ 2 ^ r) :
    goldilocksHostileFailureBound (p8WorkHostile N M)
        (ioFailureUnionBound 10 (3 * N) M (Fintype.card Nock.Field.K)) N M
        + (req6Work N Λ : ℚ) / (cardKGold : ℚ)
      < 1 / (2 : ℚ) ^ b := by
  refine hostileBound_add_lt_of_totalWork _ _ _ _ _ ?_
  have h := two_hostileTotalWork_majorant_req6_le (2 ^ r) N M Λ hN hM hΛ
  have h1 : (2 : ℕ) ^ r * 2 ^ r * 2 ^ b = 2 ^ 184 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have h2 : (2 : ℕ) ^ r * 2 ^ b ≤ 2 ^ 180 := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ b ≤ 2 ^ 176 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h' : (477 * (2 ^ r * 2 ^ r) + 150 * 2 ^ r + 288) * 2 ^ b < 2 * cardKGold := by
    calc (477 * (2 ^ r * 2 ^ r) + 150 * 2 ^ r + 288) * 2 ^ b
        = 477 * (2 ^ r * 2 ^ r * 2 ^ b) + 150 * (2 ^ r * 2 ^ b) + 288 * 2 ^ b := by ring
      _ ≤ 477 * 2 ^ 184 + 150 * 2 ^ 180 + 288 * 2 ^ 176 := by
          rw [h1]
          exact Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 150 h2) _)
            (Nat.mul_le_mul_left 288 h3)
      _ < 2 * cardKGold := by norm_num
  have : 2 * ((hostileTotalWork (p8WorkHostile N M) N M + req6Work N Λ) * 2 ^ b)
      ≤ (477 * (2 ^ r * 2 ^ r) + 150 * 2 ^ r + 288) * 2 ^ b := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ h
  omega

open Nock.NockVMROM.Thm54.HostileWorkloadMajorant in
/-- **122 at `2^31` at the hostile majorant with the `6N` route-B summand.** -/
theorem hostile_soundness_majorant_req6_at_two_pow_31 (N M Λ : ℕ)
    (hN : N ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) :
    goldilocksHostileFailureBound (p8WorkHostile N M)
        (ioFailureUnionBound 10 (3 * N) M (Fintype.card Nock.Field.K)) N M
        + (req6Work N Λ : ℚ) / (cardKGold : ℚ) < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_majorant_req6_at_row_budget 31 122 N M Λ (by norm_num) (by norm_num) hN hM hΛ

open Nock.NockVMROM.Thm54.HostileWorkloadMajorant in
/-- **120 at `2^32` at the hostile majorant with the `6N` route-B summand.** -/
theorem hostile_soundness_majorant_req6_at_two_pow_32 (N M Λ : ℕ)
    (hN : N ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) :
    goldilocksHostileFailureBound (p8WorkHostile N M)
        (ioFailureUnionBound 10 (3 * N) M (Fintype.card Nock.Field.K)) N M
        + (req6Work N Λ : ℚ) / (cardKGold : ℚ) < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_majorant_req6_at_row_budget 32 120 N M Λ (by norm_num) (by norm_num) hN hM hΛ

/-- **122 at the paper configuration at a `2^68` P8 numerator (the majorant's,
`p8WorkHostile_at_two_pow_31`) with the `6N` route-B summand** — route B costs no bit beyond
the one the majorant already costs. -/
theorem hostile_soundness_at_paper_configuration_majorant_req6 (p8Work ioWork pw : ℕ)
    (hp8 : p8Work ≤ 2 ^ 68) (hio : ioWork ≤ 16 ^ 65) (hpw : pw ≤ 2 ^ 66) :
    goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) + (pw : ℚ) / (cardKGold : ℚ)
      < 1 / (2 : ℚ) ^ 122 := by
  rw [goldilocksHostileFailureBound_eq]
  have hts := timestampCollisionBound_at_paper_configuration
  have hwr := walkAndTilingBound_at_paper_configuration
  have hinter :
      ((FiniteIO.ioFailureUnionBound 10 (2 ^ 31) (2 ^ 31) cardKGold
          + cardKGold * 2 ^ 31 : ℕ) : ℚ) / (cardKGold : ℚ) ^ 2
      = ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ) := by
    rw [ioFailureUnionBound_ten]
    have hnat : 36 * 2 ^ 31 * 2 ^ 31 + 4 * 2 ^ 31 = 9 * 2 ^ 64 + 2 ^ 33 := by norm_num
    rw [hnat]
    have hk : (cardKGold : ℚ) ≠ 0 := by norm_num
    field_simp
    ring
  have hmaj :
      ((2 : ℚ) ^ 68 + (2 : ℚ) ^ 65 + (2 : ℚ) ^ 36) / (cardKGold : ℚ)
        + ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2
        + ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ)
        + (2 : ℚ) ^ 66 / (cardKGold : ℚ)
        < 1 / (2 : ℚ) ^ 122 := by
    norm_num
  have hp8' : (p8Work : ℚ) ≤ (2 : ℚ) ^ 68 := by exact_mod_cast hp8
  have hts' : (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ)
      ≤ (2 : ℚ) ^ 65 := by exact_mod_cast hts
  have hwr' : (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) ≤ (2 : ℚ) ^ 36 := by
    exact_mod_cast hwr
  have hio' : (ioWork : ℚ) ≤ (16 : ℚ) ^ 65 := by exact_mod_cast hio
  have hpw' : (pw : ℚ) ≤ (2 : ℚ) ^ 66 := by exact_mod_cast hpw
  calc
    (p8Work + OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) +
          pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) /
          (cardKGold : ℚ)
        + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
        + ((FiniteIO.ioFailureUnionBound 10 (2 ^ 31) (2 ^ 31) cardKGold
            + cardKGold * 2 ^ 31 : ℕ) : ℚ) / (cardKGold : ℚ) ^ 2
        + (pw : ℚ) / (cardKGold : ℚ)
        = ((p8Work : ℚ) +
            (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ) +
            (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ)) /
            (cardKGold : ℚ)
          + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
          + ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ)
          + (pw : ℚ) / (cardKGold : ℚ) := by
            rw [hinter]
    _ ≤ ((2 : ℚ) ^ 68 + (2 : ℚ) ^ 65 + (2 : ℚ) ^ 36) / (cardKGold : ℚ)
          + ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2
          + ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ)
          + (2 : ℚ) ^ 66 / (cardKGold : ℚ) := by
            gcongr
    _ < 1 / (2 : ℚ) ^ 122 := hmaj

/-- `> 2^-98`, which is what takes 122 to 97. -/
theorem allPairs_minus_routeB :
    allPairWork (2 ^ 31) (2 ^ 31) - pairWork (2 ^ 31) (2 ^ 31) =
      (2 ^ 62 - 2 ^ 31) * (2 ^ 32 - 1) := by
  unfold allPairWork pairWork; norm_num

end Figures

end

end Nock.RedTeam.Batch742

#print axioms Nock.RedTeam.Batch742.reqPairEvent_card_le
#print axioms Nock.RedTeam.Batch742.reqPairEvent_preZReads
#print axioms Nock.RedTeam.Batch742.reqPairEvent_adaptive_eq
#print axioms Nock.RedTeam.Batch742.reqPair_conjunct
#print axioms Nock.RedTeam.Batch742.reqTgt_reads_reqIdx
#print axioms Nock.RedTeam.Batch742.ver_reqIdx_injective
#print axioms Nock.RedTeam.Batch742.request_named_by_row
#print axioms Nock.RedTeam.Batch742.hostile_soundness_formR_req3_at_two_pow_31
#print axioms Nock.RedTeam.Batch742.hostile_soundness_formR_req3_at_two_pow_32
#print axioms Nock.RedTeam.Batch742.hostile_soundness_formR_req6_at_two_pow_31
#print axioms Nock.RedTeam.Batch742.hostile_soundness_formR_req6_at_two_pow_32
#print axioms Nock.RedTeam.Batch742.hostile_soundness_at_paper_configuration_req6
#print axioms Nock.RedTeam.Batch742.coefficient_ceiling
#print axioms Nock.RedTeam.Batch742.allPairs_minus_routeB
#print axioms Nock.RedTeam.Batch742.hostile_soundness_majorant_req6_at_two_pow_31
#print axioms Nock.RedTeam.Batch742.hostile_soundness_majorant_req6_at_two_pow_32
#print axioms Nock.RedTeam.Batch742.hostile_soundness_at_paper_configuration_majorant_req6
