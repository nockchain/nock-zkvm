/-
  Nock/RedTeam/Batch672Thm54ExponentCarrierBinding.lean

  **C2 of the THIRTY-FIRST move (lane `exponent-carrier`): the binding and the window.**

  * **The compute carrier is the prefix sum, hostilely** (`expCol_eq_prefixExp`): for ANY trace
    the consumed compute chip accepts, under `hchar`, the round-0 column `S` (`computeExpCol = 302`)
    at row `m` is `(prefixExp m : 𝔽)` — from the two committed gates `isFirst·S = 0`,
    `(1 − isLast)·(S(i+1) − S(i) − arity(i)) = 0` and the one-hot selectors.  Slot `9` of the
    `j`-th request record of row `i` is `(expOf i j : 𝔽) = (S(i) + j + 1 : 𝔽)`
    (`compute_slot9_eq_expOf`).
  * **The memory carrier is bound** (`memory_row_bound`): outside the consumed failure event (the
    IO, timestamp and inter-pole events are summands of it), at every `ver = 1` memory row of any
    accepted trace pair there is an active compute request `(i', j)` with
    `reqIdx = ((S(i') + j + 1 : ℕ) : 𝔽)` and `ts_mem = α^{S(i') + j + 1}` — `hostile_LIO'` equates
    all ten slots (slot `9`: `reqIdx` vs the in-gate `S + j + 1`; slot `7`: the timestamp,
    `hostile_timestamp_eq` with `hostile_ln0_eq_one`).
  * **The natural lift** (`natLift_reqIdx`): `natLift reqIdx = S(i') + j + 1`, because
    `S(i') + j + 1 ≤ |hostileRequests| ≤ Ksz < ringChar K = ringChar 𝔽` (`hKreq`, `hKp`, already
    hypotheses of `hostile_LIO'`; `Algebra.ringChar_eq`).  Hence
    `ts_mem = α^{natLift reqIdx}` (`ts_eq_alpha_pow_natLift`), with no new coin and no new binder.
  * **The window** (`PO` N1): `natLift reqIdx ≤ 3·compRows + 3` (`natLift_reqIdx_window`), indeed
    `≤ 3·compRows` (`totalRequests_le`).
-/
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly
import Nock.NockVMROM.Thm54.MemoryInternalPole
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch672

open Nock Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.StrictExtension
open scoped Polynomial

noncomputable section

theorem opCol_eq_stateIndex_iff (st s : ComputeTable.State) :
    opCol st = (OptimizedComputeCodec.stateIndex s : ℕ) ↔ st = s := by
  cases st <;> cases s <;> decide

section Compute

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])

/-! ## A. The compute carrier `S`, hostilely -/

/-- The base-field row environment the compute obligations are read at. -/
abbrev envFc (i : Fin (rows P)) : Env F :=
  envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
    P.optimized.computeChallenge P.optimized.computePublic

theorem expCol_eq_trace (i : Fin (rows P)) :
    (rowEnv P Qc i).expCol = (envFc P Qc i).trace computeExpCol := rfl

theorem baseTrace_eq (i : Fin (rows P)) (c : Fin 13) :
    (rowEnv P Qc i).baseTrace c = (envFc P Qc i).trace c := rfl

/-- `S(i + 1)` is the next-row read of `S` at row `i` (orbit alignment). -/
theorem next_expCol (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (envFc P Qc i).traceNext computeExpCol = (rowEnv P Qc ⟨(i : ℕ) + 1, hi⟩).expCol := by
  have hadj := P.optimized.computeAdjacentOrbit i hi
  have hlt : computeExpCol < P.computeChip.rap.w := by
    change 302 < 303; norm_num
  simp only [envFc, envOfTrace, dif_pos hlt, expCol_eq_trace]
  rw [hadj]

variable (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
include hsat

/-- **`S(0) = 0`** from the committed gate `isFirst · S = 0`. -/
theorem expCol_first : (rowEnv P Qc (firstRow P)).expCol = 0 := by
  have h := (row_obligations P Qc hsat (firstRow P)).expGates expInitGate
    (by simp [computeExpGates])
  have hm := (masks_at_row P Qc hsat (firstRow P)).1
  rw [baseTrace_eq] at hm
  simp only [expInitGate, CoeffExpr.eval] at h
  have h11 : (envFc P Qc (firstRow P)).trace 11 = 1 := by simpa using hm
  rw [show ((11 : Fin 13) : ℕ) = 11 from rfl] at hm
  rw [expCol_eq_trace]
  simpa [h11] using h

/-- The selectors are one-hot at the base-field level. -/
theorem base_selector (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (i : Fin (rows P)) :
    ∃ s, (∀ st, (rowEnv P Qc i).toSourceEnv.trace (opCol st) = ComputeTable.opSel s st) ∧
      ∀ c : ℕ, c < 11 →
        (envFc P Qc i).trace c =
          if c = (OptimizedComputeCodec.stateIndex s : ℕ) then 1 else 0 := by
  obtain ⟨s, hsel⟩ := source_selector P Qc hsat hchar i
  refine ⟨s, hsel, fun c hc => ?_⟩
  have hF : ∀ st, (envFc P Qc i).trace (opCol st) = ComputeTable.opSel s st := by
    intro st
    have h := hsel st
    rw [source_trace_base _ (opCol st) (by cases st <;> decide)] at h
    have hinj := (algebraMap F K).injective
    apply hinj
    rw [show (rowEnv P Qc i).baseTrace ⟨opCol st, by cases st <;> decide⟩ =
      (envFc P Qc i).trace (opCol st) from rfl] at h
    rw [h]
    simp only [ComputeTable.opSel]
    split_ifs <;> simp
  obtain ⟨st, rfl⟩ : ∃ st : ComputeTable.State, opCol st = c := by
    interval_cases c
    exacts [⟨.s0, rfl⟩, ⟨.s1, rfl⟩, ⟨.s2, rfl⟩, ⟨.s3, rfl⟩, ⟨.s4, rfl⟩, ⟨.s5, rfl⟩,
      ⟨.s6, rfl⟩, ⟨.s7, rfl⟩, ⟨.s8, rfl⟩, ⟨.s9, rfl⟩, ⟨.cons, rfl⟩]
  rw [hF st]
  by_cases h : st = s
  · subst h; simp [ComputeTable.opSel, (opCol_eq_stateIndex_iff st st).2 rfl]
  · have h' : opCol st ≠ (OptimizedComputeCodec.stateIndex s : ℕ) :=
      fun he => h ((opCol_eq_stateIndex_iff st s).1 he)
    simp [ComputeTable.opSel, h, h']

theorem arityCoeff_stateIndex (s : ComputeTable.State) :
    arityCoeff (OptimizedComputeCodec.stateIndex s) = arity s := by
  cases s <;> rfl

/-- **`S(i + 1) = S(i) + arity(i)`** off the last row, from the committed step gate. -/
theorem expCol_step (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnv P Qc ⟨(i : ℕ) + 1, hi⟩).expCol =
      (rowEnv P Qc i).expCol + ((rowArity (rowEnv P Qc i) : ℕ) : F) := by
  have h := (row_obligations P Qc hsat i).expGates expStepGate
    (by simp [computeExpGates])
  have hm := (masks_at_row P Qc hsat i).2
  rw [baseTrace_eq] at hm
  have h12 : (envFc P Qc i).trace 12 = 0 := by
    have hne : i ≠ lastRow P := by
      intro heq
      have hv : (i : ℕ) = rows P - 1 := congrArg Fin.val heq
      omega
    simpa [hne] using hm
  obtain ⟨s, hsel, hselF⟩ := base_selector P Qc hsat hchar i
  have harity : (arityForm (F := F)).eval (envFc P Qc i) = ((arity s : ℕ) : F) := by
    simp only [arityForm, List.range, List.range.loop, List.foldr, CoeffExpr.eval]
    rw [hselF 0 (by omega), hselF 1 (by omega), hselF 2 (by omega), hselF 3 (by omega),
      hselF 4 (by omega), hselF 5 (by omega), hselF 6 (by omega), hselF 7 (by omega),
      hselF 8 (by omega), hselF 9 (by omega), hselF 10 (by omega)]
    cases s <;> simp [OptimizedComputeCodec.stateIndex, arityCoeff, arity]
  have hra := rowArity_eq_arity P Qc i s hsel
  simp only [expStepGate, CoeffExpr.eval] at h
  rw [h12, sub_zero, one_mul, harity, next_expCol P Qc i hi] at h
  rw [hra, ← expCol_eq_trace] at *
  linear_combination h

/-- **The hostile carrier is the prefix sum**: `S(m) = (prefixExp m : 𝔽)` at every row of every
accepted trace. -/
theorem expCol_eq_prefixExp (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) :
    ∀ (m : ℕ) (hm : m < rows P),
      (rowEnv P Qc ⟨m, hm⟩).expCol = ((prefixExp P Qc m : ℕ) : F) := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [prefixExp, Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
      exact expCol_first P Qc hsat
  | succ m ih =>
      intro hm
      have hm' : m < rows P := by omega
      rw [expCol_step P Qc hsat hchar ⟨m, hm'⟩ hm, ih hm', prefixExp_succ P Qc m hm']
      push_cast
      ring

omit hsat in
/-- Slot `9` of the `j`-th request record of row `i` is `S(i) + j + 1`, in-gate. -/
theorem rowRecord_slot9 (i : Fin (rows P)) (j : Fin 3) :
    rowRecord (rowEnv P Qc i) j 9 =
      algebraMap F K (rowEnv P Qc i).expCol + (((j : ℕ) + 1 : ℕ) : K) := by
  fin_cases j <;>
    simp [rowRecord, sampledSlotE, Expr.subst, finalSampledNamespace, Expr.eval,
      CorrectedFinalTypedEnv.toSourceEnv]

/-- **Compute slot `9` is `(expOf i j : 𝔽)`**, lifted. -/
theorem compute_slot9_eq_expOf (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (i : Fin (rows P)) (j : Fin 3) :
    rowRecord (rowEnv P Qc i) j 9 = algebraMap F K ((expOf P Qc i j : ℕ) : F) := by
  rw [rowRecord_slot9, expCol_eq_prefixExp P Qc hsat hchar i i.isLt]
  simp only [expOf, Fin.eta]
  push_cast
  ring

end Compute

/-! ## B. The memory carrier `reqIdx`, bound outside the consumed failure event -/

section Binding

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
  (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)

/-- **C2, the binding.**  Outside the consumed failure event, every `ver = 1` memory row of an
accepted trace pair carries the exponent of the compute request it answers: `reqIdx` (base
column `181`) is `((S(i') + j + 1 : ℕ) : 𝔽)` and the record timestamp (`𝕂` role `26`) is
`α^{S(i') + j + 1}`, with `(i', j)` an active request slot. -/
theorem memory_row_bound {Ksz : ℕ}
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
    ∃ (i' : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnv P Qc i') j = 1 ∧
      (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i).trace OptimizedMemoryGateBasis.reqIdxCol =
        ((expOf P Qc i' j : ℕ) : F) ∧
      (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i).trace OptimizedMemoryGateBasis.reqIdxCol =
        (rowEnv P Qc i').expCol + (((j : ℕ) + 1 : ℕ) : F) ∧
      (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i).trace 26 =
        alphaM c.1 ^ expOf P Qc i' j := by
  have hlio := optimizedFullStrict_hostile_LIO_historical P Qc Qm c hacc hgood hio hchar hKp hKreq hKresp
  have hz0 := hz0_of_good P Qc Qm c hacc hgood
  have hsat := hacc.compute_satisfies
  -- the row's ten-slot record is a hostile response, hence a hostile request
  have hresp : OptimizedMemoryHostileAccumulator.rowRecord
      (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i)
      (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i) ∈
      OptimizedMemoryHostileAccumulator.hostileResponses P Qm := by
    simp only [OptimizedMemoryHostileAccumulator.hostileResponses, List.mem_flatten,
      List.mem_ofFn]
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    simp [OptimizedMemoryHostileAccumulator.rowResponses,
      OptimizedMemoryHostileAccumulator.rowResponseTerms, hver]
  have hreq := (List.Perm.mem_iff hlio.2.2).2 hresp
  obtain ⟨i', j, hact, heq⟩ := OptimizedHostileIOAssembly.mem_hostileRequests P Qc hreq
  -- slot 9
  have h9 := congrFun heq 9
  rw [compute_slot9_eq_expOf P Qc hsat hchar i' j] at h9
  have h9' : (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i).trace
      OptimizedMemoryGateBasis.reqIdxCol = ((expOf P Qc i' j : ℕ) : F) := by
    apply (algebraMap F K).injective
    simpa [OptimizedMemoryHostileAccumulator.rowRecord, OptimizedMemoryGateBasis.reqIdxCol]
      using h9
  -- slot 7
  have h7 := congrFun heq 7
  rw [hostile_timestamp_eq P Qc hsat hchar hz0 i' j hact, hostile_ln0_eq_one P Qc hsat, one_mul,
    chipAlpha_eq_alphaM P Qc Qm c hacc] at h7
  have h7' : (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i).trace 26 =
      alphaM c.1 ^ expOf P Qc i' j := by
    simpa [OptimizedMemoryHostileAccumulator.rowRecord, expOf] using h7
  refine ⟨i', j, hact, h9', ?_, h7'⟩
  rw [h9', expCol_eq_prefixExp P Qc hsat hchar i' i'.isLt]
  simp only [expOf, Fin.eta]
  push_cast
  ring

/-- **The natural lift of the bound carrier is the exponent**: `natLift reqIdx = S(i') + j + 1`,
since `S(i') + j + 1 ≤ |hostileRequests| ≤ Ksz < ringChar K = ringChar 𝔽`. -/
theorem natLift_reqIdx {Ksz : ℕ}
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
    ∃ (i' : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnv P Qc i') j = 1 ∧
      RecordCarrier.natLift ((OptimizedMemoryHostileAccumulator.rowEnvF P Qm i).trace
        OptimizedMemoryGateBasis.reqIdxCol) = prefixExp P Qc i' + (j : ℕ) + 1 ∧
      (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i).trace 26 =
        alphaM c.1 ^
          RecordCarrier.natLift ((OptimizedMemoryHostileAccumulator.rowEnvF P Qm i).trace
            OptimizedMemoryGateBasis.reqIdxCol) := by
  obtain ⟨i', j, hact, hreqIdx, -, hts⟩ :=
    memory_row_bound P Qc Qm c S hacc hgood hio hchar hKp hKreq hKresp i hver
  have hsat := hacc.compute_satisfies
  have hle : expOf P Qc i' j ≤ (hostileRequests P Qc).length := by
    rw [← totalRequests_eq_length P Qc hsat hchar]
    exact expOf_le_total P Qc i' j hact
  have hlt : expOf P Qc i' j < ringChar F := by
    rw [Algebra.ringChar_eq F K]
    exact lt_of_le_of_lt (le_trans hle hKreq.2) hKp
  have hlift : RecordCarrier.natLift ((OptimizedMemoryHostileAccumulator.rowEnvF P Qm i).trace
      OptimizedMemoryGateBasis.reqIdxCol) = expOf P Qc i' j := by
    rw [hreqIdx]; exact RecordCarrier.natLift_natCast hlt
  refine ⟨i', j, hact, ?_, ?_⟩
  · rw [hlift]; rfl
  · rw [hlift]; exact hts

theorem ts_eq_alpha_pow_natLift {Ksz : ℕ}
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
    (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i).trace 26 =
      alphaM c.1 ^
        RecordCarrier.natLift ((OptimizedMemoryHostileAccumulator.rowEnvF P Qm i).trace
          OptimizedMemoryGateBasis.reqIdxCol) := by
  obtain ⟨_, _, _, _, h⟩ := natLift_reqIdx P Qc Qm c S hacc hgood hio hchar hKp hKreq hKresp i hver
  exact h

/-- **The window (`PO` N1)**: `natLift reqIdx ≤ 3·compRows + 3` — in fact `≤ 3·compRows`
(`totalRequests_le`); `compRows` is the package configuration's compute row count
(`OptimizedComputeHostileAccumulator.rows`). -/
theorem natLift_reqIdx_window {Ksz : ℕ}
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
    RecordCarrier.natLift ((OptimizedMemoryHostileAccumulator.rowEnvF P Qm i).trace
        OptimizedMemoryGateBasis.reqIdxCol) ≤
      3 * P.optimized.family.problem.cfg.compRows + 3 := by
  obtain ⟨i', j, hact, hlift, -⟩ :=
    natLift_reqIdx P Qc Qm c S hacc hgood hio hchar hKp hKreq hKresp i hver
  have h := expOf_le_total P Qc i' j hact
  have h3 := totalRequests_le P Qc
  rw [hlift]
  unfold expOf at h
  change prefixExp P Qc i' + (j : ℕ) + 1 ≤ totalRequests P Qc at h
  have : totalRequests P Qc ≤ 3 * P.optimized.family.problem.cfg.compRows := h3
  omega

/-- With `Batch521.readRoot_sel_implies_ver1` the `read_root` row is `ver = 1`, hence
bound by `memory_row_bound`. -/
theorem verify_row_inherits
    (S : OptimizedFullStrictThm54Statement P)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hK : OptimizedMemoryHostileAccumulator.rows P < ringChar K)
    (i : Fin (OptimizedMemoryHostileAccumulator.rows P))
    (hv : (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i).trace 3 = 1) :
    ∃ i'' : Fin (OptimizedMemoryHostileAccumulator.rows P),
      (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i'').trace 2 = 1 ∧
      (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i'').trace OptimizedMemoryGateBasis.reqIdxCol =
        (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i).trace OptimizedMemoryGateBasis.reqIdxCol ∧
      (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i'').trace 26 =
        (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i).trace 26 := by
  have hperm := MemoryInternalPole.optimizedFullStrict_paired_records P Qc Qm c S hacc hgood hK
  have hmem : MemoryInternalPole.rowRecord (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i)
      (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i) ∈ MemoryInternalPole.hostileVerifies P Qm := by
    simp only [MemoryInternalPole.hostileVerifies, List.mem_flatten, List.mem_ofFn]
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    simp [MemoryInternalPole.rowVerifiesOf, hv]
  have hread := (List.Perm.mem_iff hperm).2 hmem
  simp only [MemoryInternalPole.hostileReads, List.mem_flatten, List.mem_ofFn] at hread
  obtain ⟨l, ⟨i'', rfl⟩, hl⟩ := hread
  unfold MemoryInternalPole.rowReadsOf at hl
  split_ifs at hl with hr
  · simp only [List.mem_singleton] at hl
    refine ⟨i'', hr, ?_, ?_⟩
    · have h9 := congrFun hl 9
      apply (algebraMap F K).injective
      simpa [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord,
        OptimizedMemoryGateBasis.reqIdxCol] using h9.symm
    · have h7 := congrFun hl 7
      simpa [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord]
        using h7.symm
  · simp at hl

end Binding

end

end Nock.RedTeam.Batch672

#print axioms Nock.RedTeam.Batch672.expCol_eq_prefixExp
#print axioms Nock.RedTeam.Batch672.compute_slot9_eq_expOf
#print axioms Nock.RedTeam.Batch672.memory_row_bound
#print axioms Nock.RedTeam.Batch672.natLift_reqIdx
#print axioms Nock.RedTeam.Batch672.ts_eq_alpha_pow_natLift
#print axioms Nock.RedTeam.Batch672.natLift_reqIdx_window
#print axioms Nock.RedTeam.Batch672.verify_row_inherits
