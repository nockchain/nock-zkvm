/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/FamilyIOChainRouteBEv.lean

  The originals are untouched.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.FamilyIOChainRouteB
import Nock.NockVMROM.Thm54.P8Core.PlacementABridge
import Nock.NockVMROM.Thm54.P8Core.EvOnly.OptimizedHostileTimestampsEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.FamilyIOChain

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open OptimizedStrictPackage
open OptimizedStrictFullPackage
open OptimizedComputeCorrectedFinal
open OptimizedComputeSemanticRealization
open OptimizedComputeSubstitution
open StrictExtension
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open OptimizedMemoryHostileAccumulator (memRowTerm rowResponseTerms rowResponses
  chainMixed_mem)
open MemoryInternalPole (chipInterCoins rowDelta AggregatorAt aggregatorAt_of_paperAggregator
  delta_eq_signed_inv rowReadsOf rowVerifiesOf rowReadsOf_length_le rowVerifiesOf_length_le
  paperAggregator_mem req_denom_ne_of_not_hit resp_denom_ne_of_not_hit)
open DeployedChipFamily
open FamilyComputeRows
open FamilyMemoryRows
open Module
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

/-- Needs only
`hgood` — no `same_problem`, no package `z`. -/
theorem nprSeed_ne_of_good_at_ev
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm)) :
    nprSeed c.1 ≠ 0 :=
  nprSeed_ne_of_good_ev P (honestQc P c Qc) (honestQm P c Qm) c hgood

/-- The timestamp exclusion at the family request count, from component 3 of
`optimizedFailureEvent_good_components` (the count is the package count at `honestQc`). -/
theorem timestamp_good_at_ev
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm)) :
    alphaM c.1 ∉ TimestampCollisionEvent (hostileRequestsAt P c Qc).length := by
  rw [hostileRequestsAt_length_eq]
  exact (Nock.NockVMROM.Thm54.PlacementA.good_components_of_Ev P _ _ c hgood).2.2.1

/-- **Twin of `optimizedFullStrict_hostile_LIO` / census `hostile_LIO_of_good`.**  No `S`. -/
theorem hostile_LIO_of_good_at_ev {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz) :
    IO.LIO Ksz (hostileRequestsAt P c Qc) (hostileResponsesAt P c Qm) :=
  hostile_LIO'_at_of_not_failure P c Qm Qc hacc hchar (nprSeed_ne_of_good_at_ev P c Qc Qm hgood)
    (timestamp_good_at_ev P c Qc Qm hgood) hKp hKreq hKresp hio

section Carrier

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

end Carrier

section Paired

variable (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)

end Paired

/-- **Twin of `MemoryInternalPole.optimizedFullStrict_paired_records`.**  The internal-pole component of `optimizedFailureEvent_good_components`
prices exactly these records (memory records read trace columns only), and the chip's coins
`(γ, interPole)` are the tuple's by definition — no `memory_intermediate_pole` /
`memory_sampled_coins` pin, no `S`. -/
theorem paired_records_of_good_at_ev (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hK : memRows P < ringChar K) :
    (hostileReadsAt P c Qm).Perm (hostileVerifiesAt P c Qm) := by
  have hsat := hacc.memory_satisfies
  have hinter := (Nock.NockVMROM.Thm54.PlacementA.good_components_of_Ev P _ _ c hgood).2.2.2.1
  have hfail : (c.2.1.1, c.2.2.2.interPole) ∉ FiniteIO.IOFailureEvent (interRecordsAt P c Qm) := by
    intro h
    apply hinter
    refine Finset.mem_union.mpr (Or.inl ?_)
    rwa [interRecordsAt_eq_package] at h
  have hagg : ∀ i : Fin (memRows P),
      AggregatorAt (memEnvK P c Qm i) (memEnvF P c Qm i) c.2.2.2.interPole c.2.1.1 := by
    intro i
    have happ := aggregatorAt_of_paperAggregator (memEnvK P c Qm i) (memEnvF P c Qm i)
      (aggregator_at_mem P c Qm hsat i)
    have h4 := memEnvK_chal P c Qm i ⟨4, by decide⟩
    have h6 := memEnvK_chal P c Qm i ⟨6, by decide⟩
    have hcoins : chipInterCoins (memEnvK P c Qm i) = ⟨c.2.1.1, c.2.2.2.interPole⟩ := by
      simp only [chipInterCoins]
      rw [h4, h6]
      rfl
    simpa [hcoins] using happ
  have hden : ∀ i : Fin (memRows P),
      c.2.2.2.interPole +
        Walk.rlc c.2.1.1 (MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i)) ≠ 0 := by
    intro i h0
    apply hinter
    refine Finset.mem_union.mpr (Or.inr ?_)
    simp only [allRowPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i), ?_, h0⟩
    rw [memRecord_eq_package]
    simp [List.mem_ofFn]
  have hn1 : (hostileReadsAt P c Qm).length < ringChar K :=
    lt_of_le_of_lt (hostileReadsAt_length_le P c Qm) hK
  have hn2 : (hostileVerifiesAt P c Qm).length < ringChar K :=
    lt_of_le_of_lt (hostileVerifiesAt_length_le P c Qm) hK
  exact internalPole_multiset_eq_at P c Qm hsat c.2.2.2.interPole c.2.1.1 hagg hfail hn1 hn2 hden

section Binding

/-- **Twin of `Batch742.row_record_is_request`.**  Every `ver = 1` family memory row's ten-slot
record is an active family request's record. -/
theorem row_record_is_request_at_ev {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (i : Fin (memRows P)) (hver : (memEnvK P c Qm i).trace 39 = 1) :
    ∃ (a : Fin (rows P)) (j : Fin 3), activeMask (rowEnvAt P c Qc a) j = 1 ∧
      OptimizedMemoryHostileAccumulator.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) =
        rowRecord (rowEnvAt P c Qc a) j := by
  have hlio := hostile_LIO_of_good_at_ev P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp
  have hresp : OptimizedMemoryHostileAccumulator.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) ∈
      hostileResponsesAt P c Qm :=
    List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, rowRecord_mem_rowResponses_at P c Qm i hver⟩
  exact mem_hostileRequestsAt P c Qc ((List.Perm.mem_iff hlio.2.2).2 hresp)

/-- **Twin of `Batch742.ver_reqIdx_injective`** (route B's key exclusion at the family chip). -/
theorem ver_reqIdx_injective_at_ev {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (i i' : Fin (memRows P))
    (hv : (memEnvK P c Qm i).trace 39 = 1) (hv' : (memEnvK P c Qm i').trace 39 = 1)
    (heq : (memEnvF P c Qm i).trace reqIdxCol = (memEnvF P c Qm i').trace reqIdxCol) :
    i = i' := by
  have hsat := hacc.compute_satisfies
  have hlio := hostile_LIO_of_good_at_ev P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp
  obtain ⟨a, j, hact, hr⟩ :=
    row_record_is_request_at_ev P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp i hv
  obtain ⟨a', j', hact', hr'⟩ :=
    row_record_is_request_at_ev P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp i' hv'
  have h9 := congrFun hr 9
  have h9' := congrFun hr' 9
  rw [compute_slot9_eq_expOf_at P c Qc hsat hchar a j] at h9
  rw [compute_slot9_eq_expOf_at P c Qc hsat hchar a' j'] at h9'
  have hF : ((expOfAt P c Qc a j : ℕ) : F) = ((expOfAt P c Qc a' j' : ℕ) : F) := by
    apply (algebraMap F K).injective
    rw [← h9, ← h9']
    simp [OptimizedMemoryHostileAccumulator.rowRecord, reqIdxCol] at heq ⊢
    rw [heq]
  haveI : CharP F (ringChar F) := ringChar.charP F
  have hN : expOfAt P c Qc a j = expOfAt P c Qc a' j' :=
    CharP.natCast_injOn_Iio F (ringChar F)
      (Set.mem_Iio.2 (expOfAt_lt_ringChar P c Qc hsat hchar hKp hKreq hact))
      (Set.mem_Iio.2 (expOfAt_lt_ringChar P c Qc hsat hchar hKp hKreq hact')) hF
  obtain ⟨rfl, rfl⟩ := expOfAt_injective P c Qc hact hact' hN
  have hrec : OptimizedMemoryHostileAccumulator.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) ∈
      rowResponses (memEnvK P c Qm i') (memEnvF P c Qm i') := by
    rw [hr, ← hr']
    exact rowRecord_mem_rowResponses_at P c Qm i' hv'
  exact eq_of_mem_flatten_ofFn_nodup' _ hlio.2.1
    (rowRecord_mem_rowResponses_at P c Qm i hv) hrec

/-- **Twin of `Batch742.request_named_by_row`** (surjectivity). -/
theorem request_named_by_row_at_ev {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (a : Fin (rows P)) (j : Fin 3) (hact : activeMask (rowEnvAt P c Qc a) j = 1) :
    ∃ i : Fin (memRows P), (memEnvK P c Qm i).trace 39 = 1 ∧
      OptimizedMemoryHostileAccumulator.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) =
        rowRecord (rowEnvAt P c Qc a) j ∧
      (memEnvF P c Qm i).trace reqIdxCol = ((expOfAt P c Qc a j : ℕ) : F) := by
  have hsat := hacc.compute_satisfies
  have hlio := hostile_LIO_of_good_at_ev P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp
  have hreq := rowRecord_mem_hostileRequestsAt P c Qc a j hact
  have hresp := (List.Perm.mem_iff hlio.2.2).1 hreq
  obtain ⟨i, hver, hl⟩ := mem_hostileResponsesAt P c Qm hresp
  refine ⟨i, hver, hl.symm, ?_⟩
  have h9 := congrFun hl 9
  rw [compute_slot9_eq_expOf_at P c Qc hsat hchar a j] at h9
  apply (algebraMap F K).injective
  have h9' := h9
  simp only [OptimizedMemoryHostileAccumulator.rowRecord] at h9'
  simp at h9'
  rw [map_natCast]
  exact h9'.symm

/-- **Twin of `Batch672.memory_row_bound`.**  Every `ver = 1` family memory row carries the
exponent of the request it answers (`reqIdx = S(i') + j + 1`) and the timestamp
`(alphaM c.1)^{S(i') + j + 1}` — the coin is the family chip's slot `0` by definition. -/
theorem memory_row_bound_at_ev {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (i : Fin (memRows P)) (hver : (memEnvK P c Qm i).trace 39 = 1) :
    ∃ (i' : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnvAt P c Qc i') j = 1 ∧
      (memEnvF P c Qm i).trace reqIdxCol = ((expOfAt P c Qc i' j : ℕ) : F) ∧
      (memEnvF P c Qm i).trace reqIdxCol = (rowEnvAt P c Qc i').expCol + (((j : ℕ) + 1 : ℕ) : F) ∧
      (memEnvK P c Qm i).trace 26 = alphaM c.1 ^ expOfAt P c Qc i' j := by
  have hsat := hacc.compute_satisfies
  have hz0 := nprSeed_ne_of_good_at_ev P c Qc Qm hgood
  obtain ⟨i', j, hact, heq⟩ :=
    row_record_is_request_at_ev P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp i hver
  have h9 := congrFun heq 9
  rw [compute_slot9_eq_expOf_at P c Qc hsat hchar i' j] at h9
  have h9' : (memEnvF P c Qm i).trace reqIdxCol = ((expOfAt P c Qc i' j : ℕ) : F) := by
    apply (algebraMap F K).injective
    simpa [OptimizedMemoryHostileAccumulator.rowRecord, reqIdxCol] using h9
  have h7 := congrFun heq 7
  rw [hostile_timestamp_eq_at P c Qc hsat hchar hz0 i' j hact, hostile_ln0_eq_one_at P c Qc hsat,
    one_mul] at h7
  have h7' : (memEnvK P c Qm i).trace 26 = alphaM c.1 ^ expOfAt P c Qc i' j := by
    simpa [OptimizedMemoryHostileAccumulator.rowRecord, expOfAt] using h7
  refine ⟨i', j, hact, h9', ?_, h7'⟩
  rw [h9', expCol_eq_prefixExp_at P c Qc hsat hchar i' i'.isLt]
  simp only [expOfAt]
  push_cast
  ring

/-- Twin of `Batch672.natLift_reqIdx`. -/
theorem natLift_reqIdx_at_ev {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (i : Fin (memRows P)) (hver : (memEnvK P c Qm i).trace 39 = 1) :
    ∃ (i' : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnvAt P c Qc i') j = 1 ∧
      RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) = prefixExpAt P c Qc i' + (j : ℕ) + 1 ∧
      (memEnvK P c Qm i).trace 26 =
        alphaM c.1 ^ RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) := by
  obtain ⟨i', j, hact, hreqIdx, -, hts⟩ :=
    memory_row_bound_at_ev P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp i hver
  have hlt := expOfAt_lt_ringChar P c Qc hacc.compute_satisfies hchar hKp hKreq hact
  have hlift : RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) = expOfAt P c Qc i' j := by
    rw [hreqIdx]; exact RecordCarrier.natLift_natCast hlt
  refine ⟨i', j, hact, ?_, ?_⟩
  · rw [hlift]; rfl
  · rw [hlift]; exact hts

/-- **Twin of `Batch672.ts_eq_alpha_pow_natLift`**: `ts_mem = (alphaM c.1)^{natLift reqIdx}`. -/
theorem ts_eq_alpha_pow_natLift_at_ev {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (i : Fin (memRows P)) (hver : (memEnvK P c Qm i).trace 39 = 1) :
    (memEnvK P c Qm i).trace 26 =
      alphaM c.1 ^ RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) := by
  obtain ⟨_, _, _, _, h⟩ :=
    natLift_reqIdx_at_ev P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp i hver
  exact h

/-- **Twin of `Batch672.natLift_reqIdx_window`**: `natLift reqIdx ≤ 3·compRows + 3`. -/
theorem natLift_reqIdx_window_at_ev {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (i : Fin (memRows P)) (hver : (memEnvK P c Qm i).trace 39 = 1) :
    RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) ≤
      3 * P.optimized.family.problem.cfg.compRows + 3 := by
  obtain ⟨i', j, hact, hlift, -⟩ :=
    natLift_reqIdx_at_ev P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp i hver
  have h := expOfAt_le_total P c Qc i' j hact
  have h3 := totalRequestsAt_le P c Qc
  rw [hlift]
  unfold expOfAt at h
  change prefixExpAt P c Qc i' + (j : ℕ) + 1 ≤ totalRequestsAt P c Qc at h
  have : totalRequestsAt P c Qc ≤ 3 * P.optimized.family.problem.cfg.compRows := h3
  omega

/-- **Twin of `Batch672.verify_row_inherits`**: every `verify_child`-selected family memory row's
record is a `read_root`-selected row's, so it carries the same `reqIdx` and timestamp. -/
theorem verify_row_inherits_at_ev (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hK : memRows P < ringChar K)
    (i : Fin (memRows P)) (hv : (memEnvF P c Qm i).trace 3 = 1) :
    ∃ i'' : Fin (memRows P),
      (memEnvF P c Qm i'').trace 2 = 1 ∧
      (memEnvF P c Qm i'').trace reqIdxCol = (memEnvF P c Qm i).trace reqIdxCol ∧
      (memEnvK P c Qm i'').trace 26 = (memEnvK P c Qm i).trace 26 := by
  have hperm := paired_records_of_good_at_ev P c Qc Qm hacc hgood hK
  have hmem : MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) ∈
      hostileVerifiesAt P c Qm := by
    simp only [hostileVerifiesAt, List.mem_flatten, List.mem_ofFn]
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    simp [rowVerifiesOf, hv]
  have hread := (List.Perm.mem_iff hperm).2 hmem
  simp only [hostileReadsAt, List.mem_flatten, List.mem_ofFn] at hread
  obtain ⟨l, ⟨i'', rfl⟩, hl⟩ := hread
  unfold rowReadsOf at hl
  split_ifs at hl with hr
  · simp only [List.mem_singleton] at hl
    refine ⟨i'', hr, ?_, ?_⟩
    · have h9 := congrFun hl 9
      apply (algebraMap F K).injective
      simpa [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord,
        reqIdxCol] using h9.symm
    · have h7 := congrFun hl 7
      simpa [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord]
        using h7.symm
  · simp at hl

end Binding

section Hrows

/-- `paired_records`' `hK` is `hrb.2` via `family_cfg`. -/
theorem paired_records_of_rowsBound_at_ev (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K :=
      P.rowsBound) :
    (hostileReadsAt P c Qm).Perm (hostileVerifiesAt P c Qm) := by
  refine paired_records_of_good_at_ev P c Qc Qm hacc hgood ?_
  change P.optimized.family.problem.cfg.memRows < ringChar K
  rw [P.optimized.family_cfg]
  exact hrb.2

theorem window_of_rowsBound_at_ev (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K :=
      P.rowsBound)
    (i : Fin (memRows P)) (hver : (memEnvK P c Qm i).trace 39 = 1) :
    RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) ≤
      3 * P.optimized.family.problem.cfg.compRows + 3 ∧
    (memEnvK P c Qm i).trace 26 =
      alphaM c.1 ^ RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) :=
  ⟨natLift_reqIdx_window_at_ev P c Qc Qm hacc hgood hio
      (OptimizedHostileConfiguration.hchar_of_package P) (hKp_of_rowsBound_at P hrb)
      (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm) i hver,
    ts_eq_alpha_pow_natLift_at_ev P c Qc Qm hacc hgood hio
      (OptimizedHostileConfiguration.hchar_of_package P) (hKp_of_rowsBound_at P hrb)
      (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm) i hver⟩

end Hrows

end

end Nock.NockVMROM.Thm54.FamilyIOChain

