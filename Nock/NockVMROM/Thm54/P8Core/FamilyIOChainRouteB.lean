/-
  Nock/NockVMROM/Thm54/P8Core/FamilyIOChainRouteB.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.FamilyIOChainRouteB`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/FamilyIOChainRouteB.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.FamilyIOChainMemory
import Nock.NockVMROM.Thm54.P8Core.OptimizedHostileConfiguration
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.FamilyIOChainRouteB
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

/-- The package compute base environment at the reindexed trace has the family environment's
trace columns (only the challenge/public maps differ). -/
theorem computeBaseEnv_honestQc_trace (i : Fin (rows P)) :
    (P.computeBaseEnv (honestQc P c Qc) i).trace =
      (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
        (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).trace := by
  funext k
  have hw := computeChipAt_width P c
  simp only [OptimizedFullStrictNockVMROMPackage.computeBaseEnv, envOfTrace, honestQc]
  by_cases h : k < P.computeChip.rap.w
  · have h' : k < (P.computeChipAt c).rap.w := by rw [hw]; exact h
    rw [dif_pos h, dif_pos h']
    rfl
  · have h' : ¬ k < (P.computeChipAt c).rap.w := by rw [hw]; exact h
    rw [dif_neg h, dif_neg h']

/-- `activeMask` reads the base selectors only. -/
theorem activeMask_congr {env env' : CorrectedFinalTypedEnv F K}
    (h : env.baseTrace = env'.baseTrace) (j : Fin 3) : activeMask env j = activeMask env' j := by
  fin_cases j <;> simp [activeMask, sampledActive, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, h]

theorem activeMask_honestQc (i : Fin (rows P)) (j : Fin 3) :
    activeMask (gatherCorrectedFinalTypedEnv P.optimized.basis (P.computeBaseEnv (honestQc P c Qc) i))
        j = activeMask (rowEnvAt P c Qc i) j := by
  apply activeMask_congr
  funext k
  simp only [gatherCorrectedFinalTypedEnv, rowEnvAt]
  rw [computeBaseEnv_honestQc_trace]

theorem rowRequests_length_congr {env env' : CorrectedFinalTypedEnv F K}
    (h : ∀ j, activeMask env j = activeMask env' j) :
    (rowRequests env).length = (rowRequests env').length := by
  simp only [rowRequests, List.finRange, List.ofFn_succ, List.ofFn_zero, List.filterMap_cons,
    List.filterMap_nil, h]
  split_ifs <;> simp

/-- **The family request list has the package request list's length at the reindexed trace**:
the activity masks read base selector columns only.  (The records themselves differ: slot `7`
reads the coin `alphaM c.1` at the family chip and the package `cfg.α` at the package chip.) -/
theorem hostileRequestsAt_length_eq :
    (hostileRequestsAt P c Qc).length = (P.hostileRequests (honestQc P c Qc)).length := by
  unfold hostileRequestsAt OptimizedFullStrictNockVMROMPackage.hostileRequests
  rw [List.length_flatten, List.length_flatten, List.map_ofFn, List.map_ofFn, List.sum_ofFn,
    List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact rowRequests_length_congr (fun j => (activeMask_honestQc P c Qc i j).symm)

/-- Needs only
`hgood` — no `same_problem`, no package `z`. -/
theorem nprSeed_ne_of_good_at
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm)) :
    nprSeed c.1 ≠ 0 :=
  nprSeed_ne_of_good P (honestQc P c Qc) (honestQm P c Qm) c hgood

/-- The timestamp exclusion at the family request count, from component 3 of
`optimizedFailureEvent_good_components` (the count is the package count at `honestQc`). -/
theorem timestamp_good_at
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm)) :
    alphaM c.1 ∉ TimestampCollisionEvent (hostileRequestsAt P c Qc).length := by
  rw [hostileRequestsAt_length_eq]
  exact (P.optimizedFailureEvent_good_components _ _ c hgood).2.2.1

/-- **The named premise.**  The IO failure event of `FiniteIO` at the **family** records and the
tuple's IO coins. -/
def FamilyIOGood : Prop :=
  c.2.1 ∉ FiniteIO.IOFailureEvent (hostileRecordsAt P c Qm Qc)

/-- **Twin of `optimizedFullStrict_hostile_LIO` / census `hostile_LIO_of_good`.**  No `S`. -/
theorem hostile_LIO_of_good_at {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz) :
    IO.LIO Ksz (hostileRequestsAt P c Qc) (hostileResponsesAt P c Qm) :=
  hostile_LIO'_at_of_not_failure P c Qm Qc hacc hchar (nprSeed_ne_of_good_at P c Qc Qm hgood)
    (timestamp_good_at P c Qc Qm hgood) hKp hKreq hKresp hio

section Carrier

/-- The base-field family row environment. -/
abbrev envFcAt (i : Fin (rows P)) : Env F :=
  envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
    (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)

theorem expCol_eq_trace_at (i : Fin (rows P)) :
    (rowEnvAt P c Qc i).expCol = (envFcAt P c Qc i).trace computeExpCol := rfl

theorem baseTrace_eq_at (i : Fin (rows P)) (k : Fin 13) :
    (rowEnvAt P c Qc i).baseTrace k = (envFcAt P c Qc i).trace k := rfl

theorem next_expCol_at (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (envFcAt P c Qc i).traceNext computeExpCol = (rowEnvAt P c Qc ⟨(i : ℕ) + 1, hi⟩).expCol := by
  have hadj := P.optimized.computeAdjacentOrbit i hi
  have hlt : computeExpCol < (P.computeChipAt c).rap.w := by
    rw [computeChipAt_w]; change 302 < 303; norm_num
  simp only [envFcAt, envOfTrace, dif_pos hlt, expCol_eq_trace_at]
  rw [hadj]

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

/-- Twin of `Batch672.expCol_first`: `S(0) = 0`. -/
theorem expCol_first_at : (rowEnvAt P c Qc (firstRow P)).expCol = 0 := by
  have h := (row_obligations_at P c Qc hsat (firstRow P)).expGates expInitGate
    (by simp [computeExpGates])
  have hm := (masks_at_row_at P c Qc hsat (firstRow P)).1
  rw [baseTrace_eq_at] at hm
  simp only [expInitGate, CoeffExpr.eval] at h
  have h11 : (envFcAt P c Qc (firstRow P)).trace 11 = 1 := by simpa using hm
  rw [expCol_eq_trace_at]
  simpa [h11] using h

/-- Twin of `Batch672.base_selector`. -/
theorem base_selector_at (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (i : Fin (rows P)) :
    ∃ s, (∀ st, (rowEnvAt P c Qc i).toSourceEnv.trace (opCol st) = ComputeTable.opSel s st) ∧
      ∀ k : ℕ, k < 11 →
        (envFcAt P c Qc i).trace k =
          if k = (OptimizedComputeCodec.stateIndex s : ℕ) then 1 else 0 := by
  obtain ⟨s, hsel⟩ := source_selector_at P c Qc hsat hchar i
  refine ⟨s, hsel, fun k hk => ?_⟩
  have hF : ∀ st, (envFcAt P c Qc i).trace (opCol st) = ComputeTable.opSel s st := by
    intro st
    have h := hsel st
    rw [source_trace_base _ (opCol st) (by cases st <;> decide)] at h
    have hinj := (algebraMap F K).injective
    apply hinj
    rw [show (rowEnvAt P c Qc i).baseTrace ⟨opCol st, by cases st <;> decide⟩ =
      (envFcAt P c Qc i).trace (opCol st) from rfl] at h
    rw [h]
    simp only [ComputeTable.opSel]
    split_ifs <;> simp
  obtain ⟨st, rfl⟩ : ∃ st : ComputeTable.State, opCol st = k := by
    interval_cases k
    exacts [⟨.s0, rfl⟩, ⟨.s1, rfl⟩, ⟨.s2, rfl⟩, ⟨.s3, rfl⟩, ⟨.s4, rfl⟩, ⟨.s5, rfl⟩,
      ⟨.s6, rfl⟩, ⟨.s7, rfl⟩, ⟨.s8, rfl⟩, ⟨.s9, rfl⟩, ⟨.cons, rfl⟩]
  rw [hF st]
  by_cases h : st = s
  · subst h; simp [ComputeTable.opSel, (opCol_eq_stateIndex_iff' st st).2 rfl]
  · have h' : opCol st ≠ (OptimizedComputeCodec.stateIndex s : ℕ) :=
      fun he => h ((opCol_eq_stateIndex_iff' st s).1 he)
    simp [ComputeTable.opSel, h, h']

/-- Twin of `Batch672.expCol_step`: `S(i + 1) = S(i) + arity(i)` off the last row. -/
theorem expCol_step_at (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnvAt P c Qc ⟨(i : ℕ) + 1, hi⟩).expCol =
      (rowEnvAt P c Qc i).expCol + ((rowArity (rowEnvAt P c Qc i) : ℕ) : F) := by
  have h := (row_obligations_at P c Qc hsat i).expGates expStepGate
    (by simp [computeExpGates])
  have hm := (masks_at_row_at P c Qc hsat i).2
  rw [baseTrace_eq_at] at hm
  have h12 : (envFcAt P c Qc i).trace 12 = 0 := by
    have hne : i ≠ lastRow P := by
      intro heq
      have hv : (i : ℕ) = rows P - 1 := congrArg Fin.val heq
      omega
    simpa [hne] using hm
  obtain ⟨s, hsel, hselF⟩ := base_selector_at P c Qc hsat hchar i
  have harity : (arityForm (F := F)).eval (envFcAt P c Qc i) = ((arity s : ℕ) : F) := by
    simp only [arityForm, List.range, List.range.loop, List.foldr, CoeffExpr.eval]
    rw [hselF 0 (by omega), hselF 1 (by omega), hselF 2 (by omega), hselF 3 (by omega),
      hselF 4 (by omega), hselF 5 (by omega), hselF 6 (by omega), hselF 7 (by omega),
      hselF 8 (by omega), hselF 9 (by omega), hselF 10 (by omega)]
    cases s <;> simp [OptimizedComputeCodec.stateIndex, arityCoeff, arity]
  have hra := rowArity_eq_arity_at P c Qc i s hsel
  simp only [expStepGate, CoeffExpr.eval] at h
  rw [h12, sub_zero, one_mul, harity, next_expCol_at P c Qc i hi] at h
  rw [hra, ← expCol_eq_trace_at] at *
  linear_combination h

/-- Twin of `Batch672.expCol_eq_prefixExp`: `S(m) = (prefixExpAt m : 𝔽)`. -/
theorem expCol_eq_prefixExp_at (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) :
    ∀ (m : ℕ) (hm : m < rows P),
      (rowEnvAt P c Qc ⟨m, hm⟩).expCol = ((prefixExpAt P c Qc m : ℕ) : F) := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [prefixExpAt, Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
      exact expCol_first_at P c Qc hsat
  | succ m ih =>
      intro hm
      have hm' : m < rows P := by omega
      rw [expCol_step_at P c Qc hsat hchar ⟨m, hm'⟩ hm, ih hm', prefixExpAt_succ P c Qc m hm']
      push_cast
      ring

omit hsat in
/-- Twin of `Batch672.rowRecord_slot9`. -/
theorem rowRecord_slot9_at (i : Fin (rows P)) (j : Fin 3) :
    rowRecord (rowEnvAt P c Qc i) j 9 =
      algebraMap F K (rowEnvAt P c Qc i).expCol + (((j : ℕ) + 1 : ℕ) : K) :=
  by
  fin_cases j <;>
    simp [rowRecord, sampledSlotE, Expr.subst, finalSampledNamespace, Expr.eval,
      CorrectedFinalTypedEnv.toSourceEnv]

/-- Twin of `Batch672.compute_slot9_eq_expOf`. -/
theorem compute_slot9_eq_expOf_at (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (i : Fin (rows P)) (j : Fin 3) :
    rowRecord (rowEnvAt P c Qc i) j 9 = algebraMap F K ((expOfAt P c Qc i j : ℕ) : F) := by
  rw [rowRecord_slot9_at, expCol_eq_prefixExp_at P c Qc hsat hchar i i.isLt]
  simp only [expOfAt]
  push_cast
  ring

end Carrier

section Paired

variable (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)

include hsat in
theorem aggregator_at_mem (i : Fin (memRows P)) :
    (paperAggregator (F := F)).eval (memEnvK P c Qm i) (memEnvF P c Qm i) = 0 :=
  mixed_at_mem P c Qm hsat i _ (paperAggregator_mem P.optimized.basis)

include hsat in
theorem intermediate_chain_at_mem (i : Fin (memRows P)) (hi : (i : ℕ) + 1 < memRows P) :
    (memEnvK P c Qm i).trace 28 = (memEnvK P c Qm i).traceNext 27 := by
  have hc := mixed_at_mem P c Qm hsat i _ (chainMixed_mem P.optimized.basis)
  have h5 : (memEnvF P c Qm i).trace 5 = 0 := by
    rw [(masks_at_mem_at P c Qm hsat i).2, if_neg (by omega)]
  simp only [chainMixed, MixedExpr.eval, bcur, CoeffExpr.eval, h5, sub_zero, map_one,
    one_mul, sub_eq_zero] at hc
  exact hc

/-- Twin of `MemoryInternalPole.deltaPrefix`. -/
def deltaPrefixAt (m : ℕ) : K :=
  ∑ k ∈ Finset.range m, if h : k < memRows P then rowDelta (memEnvK P c Qm ⟨k, h⟩) else 0

theorem deltaPrefixAt_succ (m : ℕ) (hm : m < memRows P) :
    deltaPrefixAt P c Qm (m + 1) = deltaPrefixAt P c Qm m + rowDelta (memEnvK P c Qm ⟨m, hm⟩) := by
  simp [deltaPrefixAt, Finset.sum_range_succ, hm]

include hsat in
theorem ipre_eq_deltaPrefix_at :
    ∀ (m : ℕ) (hm : m < memRows P), (memEnvK P c Qm ⟨m, hm⟩).trace 27 = deltaPrefixAt P c Qm m := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [deltaPrefixAt, Finset.range_zero, Finset.sum_empty]
      exact (hostile_intermediate_anchored_at P c Qm hsat).1
  | succ m ih =>
      intro hm
      have hm' : m < memRows P := by omega
      rw [← next_trace_mem_at P c Qm 27 (by norm_num) ⟨m, hm'⟩ hm,
        ← intermediate_chain_at_mem P c Qm hsat ⟨m, hm'⟩ hm,
        deltaPrefixAt_succ P c Qm m hm', ← ih hm']
      simp [rowDelta]

include hsat in
/-- Twin of `hostile_intermediate_telescopes`. -/
theorem hostile_intermediate_telescopes_at :
    ∑ i : Fin (memRows P), rowDelta (memEnvK P c Qm i) = 0 := by
  have hpos := P.optimized.family.problem.cfg.memRows_pos
  have hm : memRows P - 1 < memRows P := Nat.sub_lt hpos (by omega)
  have hlast : (memEnvK P c Qm (OptimizedMemoryHostileAccumulator.lastRow P)).trace 28 =
      deltaPrefixAt P c Qm (memRows P - 1 + 1) := by
    have hipre := ipre_eq_deltaPrefix_at P c Qm hsat (memRows P - 1) hm
    have hΔ : rowDelta (memEnvK P c Qm (OptimizedMemoryHostileAccumulator.lastRow P)) =
        (memEnvK P c Qm (OptimizedMemoryHostileAccumulator.lastRow P)).trace 28 -
          (memEnvK P c Qm (OptimizedMemoryHostileAccumulator.lastRow P)).trace 27 := rfl
    rw [deltaPrefixAt_succ P c Qm (memRows P - 1) hm, ← hipre,
      OptimizedMemoryHostileAccumulator.lastRow, hΔ]
    ring
  rw [(hostile_intermediate_anchored_at P c Qm hsat).2, Nat.sub_add_cancel hpos] at hlast
  have hsum : ∑ i : Fin (memRows P), rowDelta (memEnvK P c Qm i) = deltaPrefixAt P c Qm (memRows P) := by
    unfold deltaPrefixAt
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [i.isLt]
  rw [hsum, ← hlast]

include hsat in
theorem selector_zero_or_one_at (i : Fin (memRows P)) (j : Fin 4) :
    (memEnvF P c Qm i).trace j = 0 ∨ (memEnvF P c Qm i).trace j = 1 := by
  have hb := (row_parts_at P c Qm hsat i).1
  have hj : bbool (bcur (j : ℕ)) ∈ baseTransitionGates P.optimized.basis := by
    simp [baseTransitionGates, paperBaseGates]
    fin_cases j <;> simp [bbool, bcur]
  have h := hb _ hj
  have h' : (memEnvF P c Qm i).trace j * ((memEnvF P c Qm i).trace j - 1) = 0 := by
    simpa [bbool, bcur, CoeffExpr.eval] using h
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- Twin of `MemoryInternalPole.hostileReads`: the records of the `read_root`-selected rows. -/
def hostileReadsAt : List (Fin 10 → K) :=
  (List.ofFn fun i : Fin (memRows P) => rowReadsOf (memEnvF P c Qm i) (memEnvK P c Qm i)).flatten

/-- Twin of `MemoryInternalPole.hostileVerifies`: the records of the `verify_child` rows. -/
def hostileVerifiesAt : List (Fin 10 → K) :=
  (List.ofFn fun i : Fin (memRows P) =>
    rowVerifiesOf (memEnvF P c Qm i) (memEnvK P c Qm i)).flatten

theorem hostileReadsAt_length_le : (hostileReadsAt P c Qm).length ≤ memRows P := by
  simp only [hostileReadsAt, List.length_flatten, List.map_ofFn]
  rw [List.sum_ofFn]
  calc ∑ i : Fin (memRows P), (rowReadsOf (memEnvF P c Qm i) (memEnvK P c Qm i)).length
      ≤ ∑ _i : Fin (memRows P), 1 := Finset.sum_le_sum fun i _ => rowReadsOf_length_le _ _
    _ = memRows P := by simp

theorem hostileVerifiesAt_length_le : (hostileVerifiesAt P c Qm).length ≤ memRows P := by
  simp only [hostileVerifiesAt, List.length_flatten, List.map_ofFn]
  rw [List.sum_ofFn]
  calc ∑ i : Fin (memRows P), (rowVerifiesOf (memEnvF P c Qm i) (memEnvK P c Qm i)).length
      ≤ ∑ _i : Fin (memRows P), 1 := Finset.sum_le_sum fun i _ => rowVerifiesOf_length_le _ _
    _ = memRows P := by simp

/-- Twin of `MemoryInternalPole.interRecordsOf`. -/
def interRecordsAt : FiniteIO.PreChallengeRecords K 10 where
  requests := hostileReadsAt P c Qm
  responses := hostileVerifiesAt P c Qm

/-- Memory records at the family env are the package env's at the reindexed trace. -/
theorem memRecord_eq_package (i : Fin (memRows P)) :
    MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) =
      OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv (honestQm P c Qm) i)
        (P.memoryBaseEnv (honestQm P c Qm) i) := by
  funext j
  simp only [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord,
    memEnvK_trace, memEnvF_trace]

theorem hostileReadsAt_eq_package :
    hostileReadsAt P c Qm = P.hostileInterReads (honestQm P c Qm) := by
  unfold hostileReadsAt rowReadsOf OptimizedFullStrictNockVMROMPackage.hostileInterReads
  refine congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_))
  rw [memEnvF_trace, memRecord_eq_package]

theorem hostileVerifiesAt_eq_package :
    hostileVerifiesAt P c Qm = P.hostileInterVerifies (honestQm P c Qm) := by
  unfold hostileVerifiesAt rowVerifiesOf OptimizedFullStrictNockVMROMPackage.hostileInterVerifies
  refine congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_))
  rw [memEnvF_trace, memRecord_eq_package]

theorem interRecordsAt_eq_package :
    interRecordsAt P c Qm = P.hostileInterRecords (honestQm P c Qm) := by
  simp only [interRecordsAt, OptimizedFullStrictNockVMROMPackage.hostileInterRecords]
  rw [hostileReadsAt_eq_package, hostileVerifiesAt_eq_package]

include hsat in
theorem internalPoleIdentity_abstract_at (pole γ : K)
    (hagg : ∀ i : Fin (memRows P), AggregatorAt (memEnvK P c Qm i) (memEnvF P c Qm i) pole γ)
    (hden : ∀ i : Fin (memRows P),
      pole + Walk.rlc γ (MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i)) ≠ 0) :
    (∑ i : Fin (memRows P),
        algebraMap F K ((memEnvF P c Qm i).trace 2) *
          (pole + Walk.rlc γ (MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i)))⁻¹) =
      ∑ i : Fin (memRows P),
        algebraMap F K ((memEnvF P c Qm i).trace 3) *
          (pole + Walk.rlc γ (MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i)))⁻¹ := by
  have htel := hostile_intermediate_telescopes_at P c Qm hsat
  have hΔ : ∀ i : Fin (memRows P),
      rowDelta (memEnvK P c Qm i) =
        (algebraMap F K ((memEnvF P c Qm i).trace 2) -
          algebraMap F K ((memEnvF P c Qm i).trace 3)) *
          (pole + Walk.rlc γ (MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i)))⁻¹ :=
    fun i => delta_eq_signed_inv _ _ pole γ (hagg i) (hden i)
  have htel' : ∑ i, ((algebraMap F K ((memEnvF P c Qm i).trace 2) -
        algebraMap F K ((memEnvF P c Qm i).trace 3)) *
        (pole + Walk.rlc γ (MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i)))⁻¹) = 0 := by
    simpa [hΔ] using htel
  simp only [sub_mul] at htel'
  rw [Finset.sum_sub_distrib] at htel'
  exact sub_eq_zero.mp htel'

include hsat in
theorem rowReadsOf_sum_at (i : Fin (memRows P)) (pole γ : K) :
    ((rowReadsOf (memEnvF P c Qm i) (memEnvK P c Qm i)).map
        fun r => (pole + Walk.rlc γ r)⁻¹).sum =
      algebraMap F K ((memEnvF P c Qm i).trace 2) *
        (pole + Walk.rlc γ (MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i)))⁻¹ := by
  have h01 := selector_zero_or_one_at P c Qm hsat i ⟨2, by decide⟩
  unfold rowReadsOf
  rcases h01 with h0 | h1
  · simp [h0, map_zero]
  · simp [h1, map_one]

include hsat in
theorem rowVerifiesOf_sum_at (i : Fin (memRows P)) (pole γ : K) :
    ((rowVerifiesOf (memEnvF P c Qm i) (memEnvK P c Qm i)).map
        fun r => (pole + Walk.rlc γ r)⁻¹).sum =
      algebraMap F K ((memEnvF P c Qm i).trace 3) *
        (pole + Walk.rlc γ (MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i)))⁻¹ := by
  have h01 := selector_zero_or_one_at P c Qm hsat i ⟨3, by decide⟩
  unfold rowVerifiesOf
  rcases h01 with h0 | h1
  · simp [h0, map_zero]
  · simp [h1, map_one]

include hsat in
theorem internalPoleIdentity_lists_at (pole γ : K)
    (hagg : ∀ i : Fin (memRows P), AggregatorAt (memEnvK P c Qm i) (memEnvF P c Qm i) pole γ)
    (hden : ∀ i : Fin (memRows P),
      pole + Walk.rlc γ (MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i)) ≠ 0) :
    ((hostileReadsAt P c Qm).map fun r => (pole + Walk.rlc γ r)⁻¹).sum =
      ((hostileVerifiesAt P c Qm).map fun r => (pole + Walk.rlc γ r)⁻¹).sum := by
  have h1 : ((hostileReadsAt P c Qm).map fun r => (pole + Walk.rlc γ r)⁻¹).sum =
      ∑ i : Fin (memRows P),
        ((rowReadsOf (memEnvF P c Qm i) (memEnvK P c Qm i)).map
          fun r => (pole + Walk.rlc γ r)⁻¹).sum := by
    simp [hostileReadsAt, List.map_flatten, List.map_ofFn, List.sum_ofFn, List.sum_flatten]
  have h2 : ((hostileVerifiesAt P c Qm).map fun r => (pole + Walk.rlc γ r)⁻¹).sum =
      ∑ i : Fin (memRows P),
        ((rowVerifiesOf (memEnvF P c Qm i) (memEnvK P c Qm i)).map
          fun r => (pole + Walk.rlc γ r)⁻¹).sum := by
    simp [hostileVerifiesAt, List.map_flatten, List.map_ofFn, List.sum_ofFn, List.sum_flatten]
  rw [h1, h2]
  have h := internalPoleIdentity_abstract_at P c Qm hsat pole γ hagg hden
  convert h using 1
  · simp_rw [rowReadsOf_sum_at P c Qm hsat _ pole γ]
  · simp_rw [rowVerifiesOf_sum_at P c Qm hsat _ pole γ]

include hsat in
theorem internalPole_compressed_perm_at (pole γ : K)
    (hagg : ∀ i : Fin (memRows P), AggregatorAt (memEnvK P c Qm i) (memEnvF P c Qm i) pole γ)
    (hden : ∀ i : Fin (memRows P),
      pole + Walk.rlc γ (MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i)) ≠ 0)
    (hn1 : (hostileReadsAt P c Qm).length < ringChar K)
    (hn2 : (hostileVerifiesAt P c Qm).length < ringChar K)
    (hlog : pole ∉ FiniteIO.IOLogDerivEvent (interRecordsAt P c Qm) γ) :
    ((hostileReadsAt P c Qm).map (Walk.rlc γ)).Perm ((hostileVerifiesAt P c Qm).map (Walk.rlc γ)) := by
  classical
  set records := interRecordsAt P c Qm
  set coins : FiniteIO.IOCoins K := ⟨γ, pole⟩
  have hend_list := internalPoleIdentity_lists_at P c Qm hsat pole γ hagg hden
  have hend : (∑ i, (coins.pole + FiniteIO.reqVals records coins.gamma i)⁻¹) =
      ∑ j, (coins.pole + FiniteIO.respVals records coins.gamma j)⁻¹ := by
    have e1 := FiniteIO.sum_fin_get (hostileReadsAt P c Qm) (fun r => (pole + Walk.rlc γ r)⁻¹)
    have e2 := FiniteIO.sum_fin_get (hostileVerifiesAt P c Qm) (fun r => (pole + Walk.rlc γ r)⁻¹)
    rw [← e1, ← e2] at hend_list
    dsimp [records, coins, FiniteIO.reqVals, FiniteIO.respVals, interRecordsAt]
    exact hend_list
  have hhit : coins.pole ∉ FiniteIO.IOPoleHitEvent records coins.gamma := by
    intro hmem
    simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨v, hv, hz⟩ := hmem
    have hv' : v ∈ hostileReadsAt P c Qm ∨ v ∈ hostileVerifiesAt P c Qm := by
      simpa [records, interRecordsAt, List.mem_append] using hv
    have hex : ∃ i, MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) = v := by
      rcases hv' with h | h
      · simp only [hostileReadsAt, List.mem_flatten, List.mem_ofFn] at h
        obtain ⟨l, ⟨i, rfl⟩, hl⟩ := h
        unfold rowReadsOf at hl; split_ifs at hl with hs
        · simp at hl; exact ⟨i, hl.symm⟩
        · simp at hl
      · simp only [hostileVerifiesAt, List.mem_flatten, List.mem_ofFn] at h
        obtain ⟨l, ⟨i, rfl⟩, hl⟩ := h
        unfold rowVerifiesOf at hl; split_ifs at hl with hs
        · simp at hl; exact ⟨i, hl.symm⟩
        · simp at hl
    obtain ⟨i, hi⟩ := hex
    exact (hden i) (by simpa [hi] using hz)
  have hdA := req_denom_ne_of_not_hit coins hhit
  have hdB := resp_denom_ne_of_not_hit coins hhit
  have hfrac := FiniteIO.frac_identity_of_pole_identity records coins hdA hdB hend
    (by simpa [records, coins] using hlog)
  have hmse :
      (∏ i, (Polynomial.X + Polynomial.C (FiniteIO.reqVals records coins.gamma i)))
        = ∏ j, (Polynomial.X + Polynomial.C (FiniteIO.respVals records coins.gamma j)) :=
    (SetEq.mse_ldse_general (p := ringChar K) hn1 hn2 _ _).mpr hfrac
  have hms :
      ((records.requests.map (Walk.rlc γ) : List K) : Multiset K)
        = ((records.responses.map (Walk.rlc γ) : List K) : Multiset K) := by
    refine (IO.prodXaddC_ms_inj _ _).mp ?_
    rw [← PairedRecordCountedEvent.denomP_eq_ms_prod, ← PairedRecordCountedEvent.denomP_eq_ms_prod]
    simpa [FiniteIO.denomP, FiniteIO.reqVals, FiniteIO.respVals, coins] using hmse
  exact Multiset.coe_eq_coe.mp (by simpa [records, interRecordsAt] using hms)

include hsat in
/-- Twin of `MemoryInternalPole.internalPole_multiset_eq`. -/
theorem internalPole_multiset_eq_at (pole γ : K)
    (hagg : ∀ i : Fin (memRows P), AggregatorAt (memEnvK P c Qm i) (memEnvF P c Qm i) pole γ)
    (hfail : (γ, pole) ∉ FiniteIO.IOFailureEvent (interRecordsAt P c Qm))
    (hn1 : (hostileReadsAt P c Qm).length < ringChar K)
    (hn2 : (hostileVerifiesAt P c Qm).length < ringChar K)
    (hden : ∀ i : Fin (memRows P),
      pole + Walk.rlc γ (MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i)) ≠ 0) :
    (hostileReadsAt P c Qm).Perm (hostileVerifiesAt P c Qm) := by
  have hγ : γ ∉ FiniteIO.IORLCCollisionEvent (interRecordsAt P c Qm) := fun h =>
    hfail ((FiniteIO.mem_IOFailureEvent_iff).2 (Or.inl h))
  have hlog : pole ∉ FiniteIO.IOLogDerivEvent (interRecordsAt P c Qm) γ := fun h =>
    hfail ((FiniteIO.mem_IOFailureEvent_iff).2 (Or.inr (Or.inr h)))
  have hcomp := internalPole_compressed_perm_at P c Qm hsat pole γ hagg hden hn1 hn2 hlog
  refine PairedRecordCountedEvent.perm_of_perm_map_of_injOn (Walk.rlc γ) ?_ hcomp
  intro u hu v hv heq
  exact FiniteIO.rlc_inj_of_not_collision hγ hu hv heq

end Paired

/-- **Twin of `MemoryInternalPole.optimizedFullStrict_paired_records`.**  The internal-pole component of `optimizedFailureEvent_good_components`
prices exactly these records (memory records read trace columns only), and the chip's coins
`(γ, interPole)` are the tuple's by definition — no `memory_intermediate_pole` /
`memory_sampled_coins` pin, no `S`. -/
theorem paired_records_of_good_at (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hK : memRows P < ringChar K) :
    (hostileReadsAt P c Qm).Perm (hostileVerifiesAt P c Qm) := by
  have hsat := hacc.memory_satisfies
  have hinter := (P.optimizedFailureEvent_good_components _ _ c hgood).2.2.2.1
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

/-- `Batch742.eq_of_mem_flatten_ofFn_nodup`, restated (no `Nock.RedTeam` import). -/
theorem eq_of_mem_flatten_ofFn_nodup' {α : Type*} {n : ℕ} (f : Fin n → List α)
    (h : (List.ofFn f).flatten.Nodup) {i i' : Fin n} {x : α}
    (hx : x ∈ f i) (hx' : x ∈ f i') : i = i' := by
  rw [List.nodup_flatten, List.pairwise_ofFn] at h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h.2 hlt hx hx'
  · exact h.2 hlt hx' hx

/-- Twin of `Batch742.rowRecord_mem_rowResponses`. -/
theorem rowRecord_mem_rowResponses_at (i : Fin (memRows P))
    (hver : (memEnvK P c Qm i).trace 39 = 1) :
    OptimizedMemoryHostileAccumulator.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) ∈
      rowResponses (memEnvK P c Qm i) (memEnvF P c Qm i) := by
  simp [rowResponses, rowResponseTerms, hver]

/-- Twin of `Batch742.expOf_injective`. -/
theorem expOfAt_injective {a a' : Fin (rows P)} {j j' : Fin 3}
    (hact : activeMask (rowEnvAt P c Qc a) j = 1) (hact' : activeMask (rowEnvAt P c Qc a') j' = 1)
    (h : expOfAt P c Qc a j = expOfAt P c Qc a' j') : a = a' ∧ j = j' := by
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (expOfAt_lt_of_row_lt P c Qc hlt j j' hact))
  · subst heq
    refine ⟨rfl, Fin.ext ?_⟩
    unfold expOfAt at h
    omega
  · exact absurd h.symm (Nat.ne_of_lt (expOfAt_lt_of_row_lt P c Qc hgt j' j hact'))

/-- **Twin of `Batch742.row_record_is_request`.**  Every `ver = 1` family memory row's ten-slot
record is an active family request's record. -/
theorem row_record_is_request_at {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (i : Fin (memRows P)) (hver : (memEnvK P c Qm i).trace 39 = 1) :
    ∃ (a : Fin (rows P)) (j : Fin 3), activeMask (rowEnvAt P c Qc a) j = 1 ∧
      OptimizedMemoryHostileAccumulator.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) =
        rowRecord (rowEnvAt P c Qc a) j := by
  have hlio := hostile_LIO_of_good_at P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp
  have hresp : OptimizedMemoryHostileAccumulator.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) ∈
      hostileResponsesAt P c Qm :=
    List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, rowRecord_mem_rowResponses_at P c Qm i hver⟩
  exact mem_hostileRequestsAt P c Qc ((List.Perm.mem_iff hlio.2.2).2 hresp)

/-- Twin of `Batch742.expOf_lt_ringChar`. -/
theorem expOfAt_lt_ringChar {Ksz : ℕ} (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    {a : Fin (rows P)} {j : Fin 3} (hact : activeMask (rowEnvAt P c Qc a) j = 1) :
    expOfAt P c Qc a j < ringChar F := by
  have hle : expOfAt P c Qc a j ≤ (hostileRequestsAt P c Qc).length := by
    rw [← totalRequestsAt_eq_length P c Qc hsat hchar]
    exact expOfAt_le_total P c Qc a j hact
  rw [Algebra.ringChar_eq F K]
  exact lt_of_le_of_lt (le_trans hle hKreq.2) hKp

/-- **Twin of `Batch742.ver_reqIdx_injective`** (route B's key exclusion at the family chip). -/
theorem ver_reqIdx_injective_at {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
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
  have hlio := hostile_LIO_of_good_at P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp
  obtain ⟨a, j, hact, hr⟩ :=
    row_record_is_request_at P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp i hv
  obtain ⟨a', j', hact', hr'⟩ :=
    row_record_is_request_at P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp i' hv'
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
theorem request_named_by_row_at {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
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
  have hlio := hostile_LIO_of_good_at P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp
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
theorem memory_row_bound_at {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
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
  have hz0 := nprSeed_ne_of_good_at P c Qc Qm hgood
  obtain ⟨i', j, hact, heq⟩ :=
    row_record_is_request_at P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp i hver
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
theorem natLift_reqIdx_at {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
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
    memory_row_bound_at P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp i hver
  have hlt := expOfAt_lt_ringChar P c Qc hacc.compute_satisfies hchar hKp hKreq hact
  have hlift : RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) = expOfAt P c Qc i' j := by
    rw [hreqIdx]; exact RecordCarrier.natLift_natCast hlt
  refine ⟨i', j, hact, ?_, ?_⟩
  · rw [hlift]; rfl
  · rw [hlift]; exact hts

/-- **Twin of `Batch672.ts_eq_alpha_pow_natLift`**: `ts_mem = (alphaM c.1)^{natLift reqIdx}`. -/
theorem ts_eq_alpha_pow_natLift_at {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (i : Fin (memRows P)) (hver : (memEnvK P c Qm i).trace 39 = 1) :
    (memEnvK P c Qm i).trace 26 =
      alphaM c.1 ^ RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) := by
  obtain ⟨_, _, _, _, h⟩ :=
    natLift_reqIdx_at P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp i hver
  exact h

/-- **Twin of `Batch672.natLift_reqIdx_window`**: `natLift reqIdx ≤ 3·compRows + 3`. -/
theorem natLift_reqIdx_window_at {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (i : Fin (memRows P)) (hver : (memEnvK P c Qm i).trace 39 = 1) :
    RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) ≤
      3 * P.optimized.family.problem.cfg.compRows + 3 := by
  obtain ⟨i', j, hact, hlift, -⟩ :=
    natLift_reqIdx_at P c Qc Qm hacc hgood hio hchar hKp hKreq hKresp i hver
  have h := expOfAt_le_total P c Qc i' j hact
  have h3 := totalRequestsAt_le P c Qc
  rw [hlift]
  unfold expOfAt at h
  change prefixExpAt P c Qc i' + (j : ℕ) + 1 ≤ totalRequestsAt P c Qc at h
  have : totalRequestsAt P c Qc ≤ 3 * P.optimized.family.problem.cfg.compRows := h3
  omega

/-- **Twin of `Batch672.verify_row_inherits`**: every `verify_child`-selected family memory row's
record is a `read_root`-selected row's, so it carries the same `reqIdx` and timestamp. -/
theorem verify_row_inherits_at (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hK : memRows P < ringChar K)
    (i : Fin (memRows P)) (hv : (memEnvF P c Qm i).trace 3 = 1) :
    ∃ i'' : Fin (memRows P),
      (memEnvF P c Qm i'').trace 2 = 1 ∧
      (memEnvF P c Qm i'').trace reqIdxCol = (memEnvF P c Qm i).trace reqIdxCol ∧
      (memEnvK P c Qm i'').trace 26 = (memEnvK P c Qm i).trace 26 := by
  have hperm := paired_records_of_good_at P c Qc Qm hacc hgood hK
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

/-- `hKp` at the hostile window: `max_lt hrb.1 hrb.2`. -/
theorem hKp_of_rowsBound_at
    (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K :=
      P.rowsBound) :
    max (3 * P.objects.cfg.compRows) P.objects.cfg.memRows < ringChar K :=
  max_lt hrb.1 hrb.2

/-- `hKreq` at the hostile window, unconditional (family request count = package count at the
reindexed trace; `hostileRequests_length_pos` / `_le`). -/
theorem hKreq_of_rowsBound_at :
    IO.InRange (max (3 * P.objects.cfg.compRows) P.objects.cfg.memRows)
      (hostileRequestsAt P c Qc).length := by
  rw [hostileRequestsAt_length_eq]
  refine ⟨OptimizedHostileConfiguration.hostileRequests_length_pos P _, ?_⟩
  have hle := P.hostileRequests_length_le (honestQc P c Qc)
  rw [P.optimized.family_cfg] at hle
  exact hle.trans (le_max_left _ _)

/-- `hKresp` at the hostile window, unconditional (`hostileResponses_length_le`). -/
theorem hKresp_of_rowsBound_at :
    (hostileResponsesAt P c Qm).length ≤ max (3 * P.objects.cfg.compRows) P.objects.cfg.memRows := by
  rw [hostileResponsesAt_eq_package]
  have hle := P.hostileResponses_length_le (honestQm P c Qm)
  rw [P.optimized.family_cfg] at hle
  exact hle.trans (le_max_right _ _)

/-- `paired_records`' `hK` is `hrb.2` via `family_cfg`. -/
theorem paired_records_of_rowsBound_at (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K :=
      P.rowsBound) :
    (hostileReadsAt P c Qm).Perm (hostileVerifiesAt P c Qm) := by
  refine paired_records_of_good_at P c Qc Qm hacc hgood ?_
  change P.optimized.family.problem.cfg.memRows < ringChar K
  rw [P.optimized.family_cfg]
  exact hrb.2

theorem window_of_rowsBound_at (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K :=
      P.rowsBound)
    (i : Fin (memRows P)) (hver : (memEnvK P c Qm i).trace 39 = 1) :
    RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) ≤
      3 * P.optimized.family.problem.cfg.compRows + 3 ∧
    (memEnvK P c Qm i).trace 26 =
      alphaM c.1 ^ RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) :=
  ⟨natLift_reqIdx_window_at P c Qc Qm hacc hgood hio
      (OptimizedHostileConfiguration.hchar_of_package P) (hKp_of_rowsBound_at P hrb)
      (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm) i hver,
    ts_eq_alpha_pow_natLift_at P c Qc Qm hacc hgood hio
      (OptimizedHostileConfiguration.hchar_of_package P) (hKp_of_rowsBound_at P hrb)
      (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm) i hver⟩

end Hrows

end

end Nock.NockVMROM.Thm54.FamilyIOChain
