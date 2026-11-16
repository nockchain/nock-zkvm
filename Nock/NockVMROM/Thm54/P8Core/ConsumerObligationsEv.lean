/-
  Nock/NockVMROM/Thm54/P8Core/ConsumerObligationsEv.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.ConsumerObligationsEv`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/ConsumerObligationsEv.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.OptimizedFailureEventEv
import Nock.NockVMROM.Thm54.P8Core.UniqueExponentsBridge
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.ConsumerObligationsEv

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.AxisBridge
open Nock.AxisBatching
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.ReconTreeSize
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.UniqueExponentsBridge
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.MemoryInternalPole
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis (reqIdxCol)
open Nock.NockVMROM.Thm54.WalkTilingEvents (memRowStateOf)
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.EdgeComparisonCensus
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

noncomputable section

section Generic

variable {K : Type} [Field K]

/-- Every timestamp exponent the committed axis tree reads (`readExps`) or verifies
(`verifyExps`) is the `recordExponent` of a `read_root` / `verify_child` node label of the
template tree (`pre t` is the preorder label list). -/
theorem exps_of_templateAxisTree :
    ∀ t : NTree (MemoryRowTemplate (K := K)),
      (∀ e ∈ readExps (templateAxisTree t), ∃ l ∈ pre t,
        l.timestamp.state = .read_root ∧ e = l.timestamp.recordExponent) ∧
      (∀ e ∈ verifyExps (templateAxisTree t), ∃ l ∈ pre t,
        l.timestamp.state = .verify_child ∧ e = l.timestamp.recordExponent) := by
  intro t
  let P := fun t : NTree (MemoryRowTemplate (K := K)) =>
    (∀ e ∈ readExps (templateAxisTree t), ∃ l ∈ pre t,
        l.timestamp.state = .read_root ∧ e = l.timestamp.recordExponent) ∧
      (∀ e ∈ verifyExps (templateAxisTree t), ∃ l ∈ pre t,
        l.timestamp.state = .verify_child ∧ e = l.timestamp.recordExponent)
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro row children ih
    have hlift : ∀ c ∈ children, ∀ l ∈ pre c, l ∈ pre (NTree.node row children) := by
      intro c hc l hl
      simp only [pre, List.mem_cons, List.mem_flatten, List.mem_map]
      exact Or.inr ⟨pre c, ⟨c, hc, rfl⟩, hl⟩
    have hself : row ∈ pre (NTree.node row children) := by simp [pre]
    simp only [P]
    cases hs : row.timestamp.state with
    | decompose =>
        rcases children with _ | ⟨l, rest⟩
        · simp [templateAxisTree, hs, readExps, verifyExps]
        · rcases rest with _ | ⟨r, tail⟩
          · simp [templateAxisTree, hs, readExps, verifyExps]
          · rcases tail with _ | ⟨x, xs⟩
            · obtain ⟨ihlR, ihlV⟩ := ih l (by simp)
              obtain ⟨ihrR, ihrV⟩ := ih r (by simp)
              simp only [templateAxisTree, hs, readExps, verifyExps, List.mem_append]
              refine ⟨?_, ?_⟩
              · rintro e (he | he)
                · obtain ⟨l', hl', hst, rfl⟩ := ihlR e he
                  exact ⟨l', hlift l (by simp) l' hl', hst, rfl⟩
                · obtain ⟨l', hl', hst, rfl⟩ := ihrR e he
                  exact ⟨l', hlift r (by simp) l' hl', hst, rfl⟩
              · rintro e (he | he)
                · obtain ⟨l', hl', hst, rfl⟩ := ihlV e he
                  exact ⟨l', hlift l (by simp) l' hl', hst, rfl⟩
                · obtain ⟨l', hl', hst, rfl⟩ := ihrV e he
                  exact ⟨l', hlift r (by simp) l' hl', hst, rfl⟩
            · simp [templateAxisTree, hs, readExps, verifyExps]
    | halt => simp [templateAxisTree, hs, readExps, verifyExps]
    | read_root =>
        rcases children with _ | ⟨c, rest⟩
        · simp [templateAxisTree, hs, readExps, verifyExps]
        · rcases rest with _ | ⟨x, xs⟩
          · obtain ⟨ihR, ihV⟩ := ih c (by simp)
            simp only [templateAxisTree, hs, readExps, verifyExps, List.mem_cons]
            refine ⟨?_, ?_⟩
            · rintro e (rfl | he)
              · exact ⟨row, hself, hs, rfl⟩
              · obtain ⟨l', hl', hst, rfl⟩ := ihR e he
                exact ⟨l', hlift c (by simp) l' hl', hst, rfl⟩
            · intro e he
              obtain ⟨l', hl', hst, rfl⟩ := ihV e he
              exact ⟨l', hlift c (by simp) l' hl', hst, rfl⟩
          · simp [templateAxisTree, hs, readExps, verifyExps]
    | verify_child =>
        rcases children with _ | ⟨c, rest⟩
        · simp [templateAxisTree, hs, readExps, verifyExps]
        · rcases rest with _ | ⟨x, xs⟩
          · obtain ⟨ihR, ihV⟩ := ih c (by simp)
            simp only [templateAxisTree, hs, readExps, verifyExps, List.mem_cons]
            refine ⟨?_, ?_⟩
            · intro e he
              obtain ⟨l', hl', hst, rfl⟩ := ihR e he
              exact ⟨l', hlift c (by simp) l' hl', hst, rfl⟩
            · rintro e (rfl | he)
              · exact ⟨row, hself, hs, rfl⟩
              · obtain ⟨l', hl', hst, rfl⟩ := ihV e he
                exact ⟨l', hlift c (by simp) l' hl', hst, rfl⟩
          · simp [templateAxisTree, hs, readExps, verifyExps]
  · intro c hc
    simp at hc
  · intro head tail ihHead ihTail c hc
    simp only [List.mem_cons] at hc
    exact hc.elim (fun h => h ▸ ihHead) (ihTail c)

/-- The preorder label list of a relabelled tree is the relabelled list. -/
theorem pre_mapNTree {α β : Type*} (f : α → β) :
    ∀ t : NTree α, pre (mapNTree f t) = (pre t).map f := by
  intro t
  let P := fun t : NTree α => pre (mapNTree f t) = (pre t).map f
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro l ch ih
    simp only [P, mapNTree, pre, List.map_cons, List.map_flatten, List.map_map]
    congr 2
    apply List.map_congr_left
    intro c hc
    exact ih c hc
  · intro c hc
    simp at hc
  · intro head tail ihHead ihTail c hc
    simp only [List.mem_cons] at hc
    exact hc.elim (fun h => h ▸ ihHead) (ihTail c)

/-- Every label of a reconstructed forest tree is `lbl j` for some index `j`. -/
theorem mem_pre_buildTF {α : Type*} (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → α) (h i : ℕ)
    {l : α} (hl : l ∈ pre (buildTF kroots fo lbl h i)) : ∃ j, l = lbl j := by
  have hmap : buildTF kroots fo lbl h i = mapNTree lbl (buildTF kroots fo id h i) := by
    rw [mapNTree_buildTF]
    rfl
  rw [hmap, pre_mapNTree, List.mem_map] at hl
  obtain ⟨j, _, rfl⟩ := hl
  exact ⟨j, rfl⟩

theorem mem_pre_of_mem_reconForest {α : Type*} {kroots : ℕ} {fo : ℕ → ℕ} {lbl : ℕ → α} {h : ℕ}
    {t : NTree α} (ht : t ∈ reconForest kroots fo lbl h) {l : α} (hl : l ∈ pre t) :
    ∃ j, l = lbl j := by
  unfold reconForest at ht
  rw [List.mem_map] at ht
  obtain ⟨i, _, rfl⟩ := ht
  exact mem_pre_buildTF kroots fo lbl h i hl

end Generic

section GenericDegree

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

/-- **The axis-degree bound from a label-wise exponent window.**  If every `read_root` /
`verify_child` label of root `i`'s template tree has `recordExponent ≤ B`, the root's axis
polynomial has degree `≤ B` (`natDegree_indP_bin_countsP_bin_le`). -/
theorem natDegree_templateAxisPolynomial_le_of_labels
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (i : Fin T.kMem) (B : ℕ)
    (hB : ∀ l ∈ pre (templateMemoryTreeAt E i),
      (l.timestamp.state = .read_root ∨ l.timestamp.state = .verify_child) →
        l.timestamp.recordExponent ≤ B) :
    (templateAxisPolynomial E i).natDegree ≤ B := by
  obtain ⟨hR, hV⟩ := exps_of_templateAxisTree (K := K) (templateMemoryTreeAt E i)
  unfold templateAxisPolynomial
  refine (natDegree_indP_bin_countsP_bin_le B _ ?_ ?_).2
  · intro e he
    obtain ⟨l, hl, hst, rfl⟩ := hR e he
    exact hB l hl (Or.inl hst)
  · intro e he
    obtain ⟨l, hl, hst, rfl⟩ := hV e he
    exact hB l hl (Or.inr hst)

end GenericDegree

section EventChain

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

/-- The four event facts the family IO chain reads off `hgood`. -/
structure ChainEvents : Prop where
  hz0 : nprSeed c.1 ≠ 0
  hts : alphaM c.1 ∉ TimestampCollisionEvent (hostileRequestsAt P c Qc).length
  hio : FamilyIOGood P c Qc Qm
  hinter : (c.2.1.1, c.2.2.2.interPole) ∉
    interFailurePairs (P.hostileInterRecords (honestQm P c Qm))
      (P.memorySourceEnv (honestQm P c Qm)) (P.memoryBaseEnv (honestQm P c Qm))

/-- `hostile_LIO_of_good_at` with the events explicit. -/
theorem hostile_LIO_of_events_at {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hE : ChainEvents P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz) :
    IO.LIO Ksz (hostileRequestsAt P c Qc) (hostileResponsesAt P c Qm) :=
  hostile_LIO'_at_of_not_failure P c Qm Qc hacc hchar hE.hz0 hE.hts hKp hKreq hKresp hE.hio

/-- `paired_records_of_good_at` with the internal-pole exclusion explicit. -/
theorem paired_records_of_inter_at (hsat : Framework.RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (hinter : (c.2.1.1, c.2.2.2.interPole) ∉
      interFailurePairs (P.hostileInterRecords (honestQm P c Qm))
        (P.memorySourceEnv (honestQm P c Qm)) (P.memoryBaseEnv (honestQm P c Qm)))
    (hK : memRows P < ringChar K) :
    (hostileReadsAt P c Qm).Perm (hostileVerifiesAt P c Qm) := by
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

/-- `row_record_is_request_at` with the events explicit. -/
theorem row_record_is_request_of_events_at {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hE : ChainEvents P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (i : Fin (memRows P)) (hver : (memEnvK P c Qm i).trace 39 = 1) :
    ∃ (a : Fin (OptimizedComputeHostileAccumulator.rows P)) (j : Fin 3),
      OptimizedComputeHostileAccumulator.activeMask (rowEnvAt P c Qc a) j = 1 ∧
      OptimizedMemoryHostileAccumulator.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) =
        OptimizedComputeHostileAccumulator.rowRecord (rowEnvAt P c Qc a) j := by
  have hlio := hostile_LIO_of_events_at P c Qc Qm hacc hE hchar hKp hKreq hKresp
  have hresp : OptimizedMemoryHostileAccumulator.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) ∈
      hostileResponsesAt P c Qm :=
    List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, rowRecord_mem_rowResponses_at P c Qm i hver⟩
  exact mem_hostileRequestsAt P c Qc ((List.Perm.mem_iff hlio.2.2).2 hresp)

/-- `memory_row_bound_at` with the events explicit (the `reqIdx` of a `ver = 1` row is the
exponent of the request it answers). -/
theorem memory_row_bound_of_events_at {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hE : ChainEvents P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (i : Fin (memRows P)) (hver : (memEnvK P c Qm i).trace 39 = 1) :
    ∃ (i' : Fin (OptimizedComputeHostileAccumulator.rows P)) (j : Fin 3),
      OptimizedComputeHostileAccumulator.activeMask (rowEnvAt P c Qc i') j = 1 ∧
      (memEnvF P c Qm i).trace reqIdxCol = ((expOfAt P c Qc i' j : ℕ) : F) := by
  have hsat := hacc.compute_satisfies
  obtain ⟨i', j, hact, heq⟩ :=
    row_record_is_request_of_events_at P c Qc Qm hacc hE hchar hKp hKreq hKresp i hver
  have h9 := congrFun heq 9
  rw [compute_slot9_eq_expOf_at P c Qc hsat hchar i' j] at h9
  refine ⟨i', j, hact, ?_⟩
  apply (algebraMap F K).injective
  simpa [OptimizedMemoryHostileAccumulator.rowRecord, reqIdxCol] using h9

theorem natLift_reqIdx_window_of_events_at {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hE : ChainEvents P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (i : Fin (memRows P)) (hver : (memEnvK P c Qm i).trace 39 = 1) :
    RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) ≤
      3 * P.optimized.family.problem.cfg.compRows + 3 := by
  obtain ⟨i', j, hact, hreqIdx⟩ :=
    memory_row_bound_of_events_at P c Qc Qm hacc hE hchar hKp hKreq hKresp i hver
  have hlt := expOfAt_lt_ringChar P c Qc hacc.compute_satisfies hchar hKp hKreq hact
  have hlift : RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) = expOfAt P c Qc i' j := by
    rw [hreqIdx]
    exact RecordCarrier.natLift_natCast hlt
  have h := expOfAt_le_total P c Qc i' j hact
  have h3 := totalRequestsAt_le P c Qc
  rw [hlift]
  have : totalRequestsAt P c Qc ≤ 3 * P.optimized.family.problem.cfg.compRows := h3
  omega

/-- `verify_row_inherits_at` with the internal-pole exclusion explicit: a selector-`3` row carries
a selector-`2` row's `reqIdx`. -/
theorem verify_partner_reqIdx_of_inter_at (hsat : Framework.RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (hinter : (c.2.1.1, c.2.2.2.interPole) ∉
      interFailurePairs (P.hostileInterRecords (honestQm P c Qm))
        (P.memorySourceEnv (honestQm P c Qm)) (P.memoryBaseEnv (honestQm P c Qm)))
    (hK : memRows P < ringChar K)
    (i : Fin (memRows P)) (hv : (memEnvF P c Qm i).trace 3 = 1) :
    ∃ i'' : Fin (memRows P),
      (memEnvF P c Qm i'').trace 2 = 1 ∧
      (memEnvF P c Qm i'').trace reqIdxCol = (memEnvF P c Qm i).trace reqIdxCol := by
  have hperm := paired_records_of_inter_at P c Qm hsat hinter hK
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
    refine ⟨i'', hr, ?_⟩
    have h9 := congrFun hl 9
    apply (algebraMap F K).injective
    simpa [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord,
      reqIdxCol] using h9.symm
  · simp at hl

/-- **The window on every `read_root` / `verify_child` row** (decoded by the round-0 selectors):
`natLift reqIdx ≤ 3·compRows + 3`, from acceptance, the four event facts, the package field
`rowsBound` and the basis premise `hb1`. -/
theorem reqIdx_window_of_state_at (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hE : ChainEvents P c Qc Qm)
    (hb1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)
    (i : Fin (memRows P))
    (hst : memRowStateOf (memEnvF P c Qm i) = .read_root ∨
      memRowStateOf (memEnvF P c Qm i) = .verify_child) :
    RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) ≤
      3 * P.optimized.family.problem.cfg.compRows + 3 := by
  have hchar := OptimizedHostileConfiguration.hchar_of_package P
  have hKp := hKp_of_rowsBound_at P
  have hKreq := hKreq_of_rowsBound_at P c Qc
  have hKresp := hKresp_of_rowsBound_at P c Qm
  have hK : memRows P < ringChar K := by
    change P.optimized.family.problem.cfg.memRows < ringChar K
    rw [P.optimized.family_cfg]
    exact P.rowsBound.2
  rcases hst with hst | hst
  · exact natLift_reqIdx_window_of_events_at P c Qc Qm hacc hE hchar hKp hKreq hKresp i
      (readSel_ver_at P c Qm hacc.memory_satisfies hb1 i (sel2_of_read hst))
  · have h3 := verify_sel_at P c Qm hacc.memory_satisfies i hst
    obtain ⟨i'', h2, hreq⟩ :=
      verify_partner_reqIdx_of_inter_at P c Qm hacc.memory_satisfies hE.hinter hK i h3
    rw [← hreq]
    exact natLift_reqIdx_window_of_events_at P c Qc Qm hacc hE hchar hKp hKreq hKresp i''
      (readSel_ver_at P c Qm hacc.memory_satisfies hb1 i'' h2)

/-- `coord b 1 0 ≠ 0` from `FormRBasis` (a hypothesis of `of_package`; `Batch824`'s receipt, in
production). -/
theorem hb1_of_formRBasis (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis) :
    coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0 := by
  rw [hbasis.1]
  exact one_ne_zero

end EventChain

section FromEv

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])

theorem chainEvents_of_evEvent (hgood : c ∉ optimizedFailureEventEv P Qc Qm) :
    ChainEvents P c (P.familyQc c Qc) (P.familyQm c Qm) := by
  have hc := optimizedFailureEventEv_good_components P Qc Qm c hgood
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hz
    apply hc.1
    simp [evFailureUnion, mem_zeroSeedFailureEvent_iff, hz]
  · rw [hostileRequestsAt_length_eq, show honestQc P c (P.familyQc c Qc) = Qc from
      FamilyEnvCore.honestQc_familyQc P.optimized c Qc]
    exact hc.2.2.1
  · exact FamilyEnvCore.familyIOGood_of_not_mem P.optimized Qc Qm c hc.2.1
  · rw [show honestQm P c (P.familyQm c Qm) = Qm from FamilyEnvCore.honestQm_familyQm P.optimized c Qm]
    exact hc.2.2.2.1

end FromEv

section Built

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])

/-- A round-0 template row's state and record exponent are the decoded state and `natLift reqIdx`
of ONE memory row of the trace (`lblM`'s / `memRowExpOfEnvs`' shared off-range convention). -/
theorem lblMR0_label_facts (c' : OptimizedProductionChallengeTuple K F) (j : ℕ) :
    ∃ r : Fin P.optimized.family.problem.cfg.memRows,
      (lblMR0 P.optimized Qc Qm c' j).timestamp.state =
          StrategyOfTraces.memoryStateOf (FamilyEnvCore.memoryBaseEnvAt P.optimized c' Qm r) ∧
      (lblMR0 P.optimized Qc Qm c' j).timestamp.recordExponent =
          RecordCarrier.natLift ((FamilyEnvCore.memoryBaseEnvAt P.optimized c' Qm r).trace reqIdxCol) := by
  unfold lblMR0 wrapR0OfEnvs
  simp only [wrapMemoryLabelR0_state, wrapMemoryLabelR0_recordExponent]
  unfold memRowExpOfEnvs lblM memoryEnvsR0
  by_cases h : j - 1 < P.optimized.family.problem.cfg.memRows
  · exact ⟨⟨j - 1, h⟩, by simp [h, lblMAt], by simp [h]⟩
  · exact ⟨⟨0, P.optimized.family.problem.cfg.memRows_pos⟩, by simp [h, lblMAt], by simp [h]⟩

/-- The family memory base env of the reindexed trace has the round-0 env's trace at any tuple. -/
theorem memEnvF_trace_eq_R0 (c' : OptimizedProductionChallengeTuple K F)
    (r : Fin (memRows P)) :
    (memEnvF P c (P.familyQm c Qm) r).trace =
      (FamilyEnvCore.memoryBaseEnvAt P.optimized c' Qm r).trace := by
  funext j
  rw [memEnvF_trace, show honestQm P c (P.familyQm c Qm) = Qm from
    FamilyEnvCore.honestQm_familyQm P.optimized c Qm]
  exact congrFun (memoryBaseEnv_trace P Qm c' r) j

theorem memoryStateOf_eq_memRowStateOf (E : Env F) :
    StrategyOfTraces.memoryStateOf E = memRowStateOf E := rfl

theorem memRowStateOf_congr {E E' : Env F} (h : E.trace = E'.trace) :
    memRowStateOf E = memRowStateOf E' := by
  unfold memRowStateOf
  rw [h]

/-- Every label of root `i` of the round-0 template is a round-0 wrap row. -/
theorem label_of_mem_R0 (c' : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P.optimized Qc Qm c') (z : K)
    (i : Fin (cfgTemplateOfTraces P.optimized Qc Qm c' z).kMem)
    {l : MemoryRowTemplate (K := K)}
    (hl : l ∈ pre (templateMemoryTreeAt (execTemplateOfTracesR0 P.optimized Qc Qm c' h z) i)) :
    ∃ j, l = lblMR0 P.optimized Qc Qm c' j := by
  have hmem : templateMemoryTreeAt (execTemplateOfTracesR0 P.optimized Qc Qm c' h z) i ∈
      (execTemplateOfTracesR0 P.optimized Qc Qm c' h z).memoryForest := List.get_mem _ _
  exact mem_pre_of_mem_reconForest hmem hl

/-- Every label of root `i` of the honest wrap has record exponent `0`. -/
theorem label_of_mem_honest (z : K)
    (i : Fin (cfgTemplateOfTraces P.optimized Qc Qm coinFree z).kMem)
    {l : MemoryRowTemplate (K := K)}
    (hl : l ∈ pre (templateMemoryTreeAt (honestTemplateEv P.optimized Qc Qm z) i)) :
    l.timestamp.recordExponent = 0 := by
  have hmem : templateMemoryTreeAt (honestTemplateEv P.optimized Qc Qm z) i ∈
      (honestTemplateEv P.optimized Qc Qm z).memoryForest := List.get_mem _ _
  change _ ∈ P.optimized.family.problem.exec.memoryForest.map (mapNTree (wrapMemoryLabelR0 0 0))
    at hmem
  rw [List.mem_map] at hmem
  obtain ⟨t, _, ht⟩ := hmem
  rw [← ht, pre_mapNTree, List.mem_map] at hl
  obtain ⟨l', _, rfl⟩ := hl
  rfl

/-- **(c) at the event strategy.**  On an accepted family trace outside the 2b-ii event, every
seed's template axis polynomial at every root has degree `≤ envelopeDeg = 3·N + 3`.  Sources:
acceptance at the family chips, `c ∉ optimizedFailureEventEv` (four components), `rowsBound`,
and `hb1` (from `FormRBasis`). -/
theorem axisPolynomial_natDegree_le_Ev
    (hacc : DeployedAcceptanceAt P c (P.familyQc c Qc) (P.familyQm c Qm))
    (hgood : c ∉ optimizedFailureEventEv P Qc Qm)
    (hb1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)
    (z : K) (hz : z ≠ 0) (i : Fin (seedConfig (builtStrategyEv P Qc Qm) z hz).kMem) :
    (templateAxisPolynomial (committedTemplate (builtStrategyEv P Qc Qm).verifier z hz) i).natDegree ≤
      envelopeDeg (seedConfig (builtStrategyEv P Qc Qm) z hz) := by
  have hE := chainEvents_of_evEvent P c Qc Qm hgood
  have hN : envelopeDeg (seedConfig (builtStrategyEv P Qc Qm) z hz) =
      3 * P.optimized.family.problem.cfg.compRows + 3 := by
    unfold envelopeDeg
    rw [show (seedConfig (builtStrategyEv P Qc Qm) z hz).compRows =
        P.optimized.family.problem.cfg.compRows from
      committedTemplate_Ev_compRows P.optimized Qc Qm P.stateTagChar z hz]
  rw [hN]
  apply natDegree_templateAxisPolynomial_le_of_labels
  intro l hl hst
  change l ∈ pre (templateMemoryTreeAt (execTemplateEv P.optimized Qc Qm z) i) at hl
  by_cases h : TracesWalkHyps P.optimized Qc Qm coinFree
  · rw [execTemplateEv_eq P.optimized Qc Qm h] at hl
    obtain ⟨j, rfl⟩ := label_of_mem_R0 P Qc Qm coinFree h z i hl
    obtain ⟨r, hst', hexp⟩ := lblMR0_label_facts P Qc Qm coinFree j
    rw [hexp]
    have htr := memEnvF_trace_eq_R0 P c Qm coinFree r
    rw [← htr]
    apply reqIdx_window_of_state_at P c _ _ hacc hE hb1 r
    rw [hst', memoryStateOf_eq_memRowStateOf, ← memRowStateOf_congr htr] at hst
    exact hst
  · have heq : execTemplateEv P.optimized Qc Qm z = honestTemplateEv P.optimized Qc Qm z := by
      unfold execTemplateEv
      rw [dif_neg h]
    rw [heq] at hl
    rw [label_of_mem_honest P Qc Qm z i hl]
    exact Nat.zero_le _

/-- **(c) at the C2 strategy** (where `p8` and the containment proof run), by the c-invariance
lemma `templateAxisPolynomial_agree`. -/
theorem axisPolynomial_natDegree_le_C2
    (hacc : DeployedAcceptanceAt P c (P.familyQc c Qc) (P.familyQm c Qm))
    (hgood : c ∉ optimizedFailureEventEv P Qc Qm)
    (hb1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)
    (h : TracesWalkHyps P.optimized Qc Qm c)
    (z : K) (hz : z ≠ 0)
    (i : Fin (seedConfig (strategyOfTracesR0AC2 P.optimized P.stateTagChar Qc Qm c h) z hz).kMem) :
    (templateAxisPolynomial (committedTemplate
      (strategyOfTracesR0AC2 P.optimized P.stateTagChar Qc Qm c h).verifier z hz) i).natDegree ≤
      envelopeDeg (seedConfig (strategyOfTracesR0AC2 P.optimized P.stateTagChar Qc Qm c h) z hz) := by
  have hN : envelopeDeg (seedConfig (strategyOfTracesR0AC2 P.optimized P.stateTagChar Qc Qm c h) z hz) =
      3 * P.optimized.family.problem.cfg.compRows + 3 := by
    unfold envelopeDeg
    show 3 * (computeLabelList P.optimized Qc c).length + 3 = _
    rw [computeLabelList_length]
  have hNev : envelopeDeg (seedConfig (builtStrategyEv P Qc Qm) z hz) =
      3 * P.optimized.family.problem.cfg.compRows + 3 := by
    unfold envelopeDeg
    rw [show (seedConfig (builtStrategyEv P Qc Qm) z hz).compRows =
        P.optimized.family.problem.cfg.compRows from
      committedTemplate_Ev_compRows P.optimized Qc Qm P.stateTagChar z hz]
  rw [hN, templateAxisPolynomial_agree P.optimized Qc Qm P.stateTagChar c h z hz i]
  have := axisPolynomial_natDegree_le_Ev P c Qc Qm hacc hgood hb1 z hz i
  rwa [hNev] at this

end Built

section Transport

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])
  (h : TracesWalkHyps P.optimized Qc Qm c)

/-- **(a) transported**: a proof-carrying census of the event skeleton is one of the C2 strategy's
skeleton (`combinedSkeletonPairs_agree`). -/
theorem census_C2_of_Ev {Λ : ℕ}
    (C : CombinedSkeletonCensus K (skeletonEv P.optimized Qc Qm) Λ) :
    CombinedSkeletonCensus K (strategyOfTracesR0AC2 P.optimized P.stateTagChar Qc Qm c h).skeleton Λ := by
  have hp := combinedSkeletonPairs_agree P.optimized Qc Qm P.stateTagChar c h
  refine ⟨⟨fun pair hp' => ?_⟩, ⟨fun pair hp' => ?_⟩⟩
  · have hmem : pair ∈ combinedSkeletonPairs K (skeletonEv P.optimized Qc Qm) := by
      rw [show skeletonEv P.optimized Qc Qm = (strategyOfTracesEv P.optimized Qc Qm P.stateTagChar).skeleton
        from rfl, ← hp]
      exact List.mem_append_left _ hp'
    rw [combinedSkeletonPairs, List.mem_append] at hmem
    exact hmem.elim (C.p8.leaves_bounded pair) (C.edges.leaves_bounded pair)
  · have hmem : pair ∈ combinedSkeletonPairs K (skeletonEv P.optimized Qc Qm) := by
      rw [show skeletonEv P.optimized Qc Qm = (strategyOfTracesEv P.optimized Qc Qm P.stateTagChar).skeleton
        from rfl, ← hp]
      exact List.mem_append_right _ hp'
    rw [combinedSkeletonPairs, List.mem_append] at hmem
    exact hmem.elim (C.p8.leaves_bounded pair) (C.edges.leaves_bounded pair)

/-- **(b) transported** (`skeletonSizeWindowNouns_agree`). -/
theorem sizeWindow_C2_of_Ev {Λ : ℕ}
    (hwin : SizeWindowNounsBoundedBy (skeletonEv P.optimized Qc Qm) Λ) :
    SizeWindowNounsBoundedBy (strategyOfTracesR0AC2 P.optimized P.stateTagChar Qc Qm c h).skeleton Λ := by
  intro n hn
  rw [skeletonSizeWindowNouns_agree] at hn
  exact hwin n hn

end Transport

section Bridge

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])
  (h : TracesWalkHyps P.optimized Qc Qm c)

theorem not_mem_FailureUnion_C2_of_obligations
    (hgood : c ∉ optimizedFailureEventEv P Qc Qm)
    (C : CombinedSkeletonCensus K
      (strategyOfTracesR0AC2 P.optimized P.stateTagChar Qc Qm c h).skeleton P.optimized.Λ)
    (hwin : SizeWindowNounsBoundedBy
      (strategyOfTracesR0AC2 P.optimized P.stateTagChar Qc Qm c h).skeleton P.optimized.Λ)
    (hdeg : ∀ (z : K) (hz : z ≠ 0) i,
      (templateAxisPolynomial (committedTemplate
        (strategyOfTracesR0AC2 P.optimized P.stateTagChar Qc Qm c h).verifier z hz) i).natDegree ≤
        envelopeDeg (seedConfig (strategyOfTracesR0AC2 P.optimized P.stateTagChar Qc Qm c h) z hz)) :
    c.1 ∉ ProductionP8Containment.FailureUnion (strategyOfTracesR0AC2 P.optimized P.stateTagChar Qc Qm c h) C
      c.2.2.2.lambda := by
  set T := strategyOfTracesR0AC2 P.optimized P.stateTagChar Qc Qm c h with hT
  have hout := not_mem_evFailureUnion_C2 P Qc Qm c h hgood
  intro hmem
  apply hout
  have hax : guardedAxisFailureEvent T c.2.2.2.lambda = envelopeAxisFailureEvent T c.2.2.2.lambda := by
    ext ω
    rw [mem_guardedAxisFailureEvent_iff, mem_envelopeAxisFailureEvent_iff]
    constructor
    · rintro ⟨hz, hα⟩
      exact ⟨hz, by rw [envelopeRootUnion_eq_of_deg_le _ _ (hdeg _ hz)]; exact hα⟩
    · rintro ⟨hz, hα⟩
      exact ⟨hz, by rw [envelopeRootUnion_eq_of_deg_le _ _ (hdeg _ hz)] at hα; exact hα⟩
  have hcen : collisionFailureEvent (K := K) C.census =
      collisionFailureEvent (guardedCensusEv K T.skeleton P.optimized.Λ) := by
    unfold collisionFailureEvent
    rw [guardedCensusEv_badSeeds_eq C]
  have hsw : SizeWindowFailure T.skeleton = guardedSizeWindowFailure (K := K) T.skeleton P.optimized.Λ :=
    (guardedSizeWindowFailure_eq_of_bounded T.skeleton P.optimized.Λ hwin).symm
  unfold ProductionP8Containment.FailureUnion at hmem
  unfold evFailureUnion
  rw [hax, hcen, hsw] at hmem
  exact hmem

/-- **THE ASSEMBLED THEOREM.**  On an accepted family trace outside the 2b-ii event, under the two
lane-B premises at the EVENT skeleton — (a) a proof-carrying census, (b) the size-window leaf
bound — the coin is outside the proof-carrying `FailureUnion` of the C2 strategy.  (c) is
discharged here (`axisPolynomial_natDegree_le_C2`).  Premises and sources:
* `hgood` — `c ∉ optimizedFailureEventEv P Qc Qm` (the 2b-ii event);
* `h` — the tiling hypotheses (from acceptance + the tiling summands, `WalkQueueDeployed.
  tracesWalkHyps_of_chips`, as the 2b-event review's `tracesWalkHyps_of_evEvent`);
* `rowsBound` — package field, read inside.
No `S`, no `same_problem`, no `p8`. -/
theorem not_mem_FailureUnion_C2
    (hacc : DeployedAcceptanceAt P c (P.familyQc c Qc) (P.familyQm c Qm))
    (hgood : c ∉ optimizedFailureEventEv P Qc Qm)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (C : CombinedSkeletonCensus K (skeletonEv P.optimized Qc Qm) P.optimized.Λ)
    (hwin : SizeWindowNounsBoundedBy (skeletonEv P.optimized Qc Qm) P.optimized.Λ) :
    c.1 ∉ ProductionP8Containment.FailureUnion (strategyOfTracesR0AC2 P.optimized P.stateTagChar Qc Qm c h)
      (census_C2_of_Ev P c Qc Qm h C) c.2.2.2.lambda :=
  not_mem_FailureUnion_C2_of_obligations P c Qc Qm h hgood (census_C2_of_Ev P c Qc Qm h C)
    (sizeWindow_C2_of_Ev P c Qc Qm h hwin)
    (fun z hz i => axisPolynomial_natDegree_le_C2 P c Qc Qm hacc hgood
      (hb1_of_formRBasis P hbasis) h z hz i)

end Bridge

end

end Nock.NockVMROM.Thm54.ConsumerObligationsEv
