import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly
import Nock.NockVMROM.Thm54.ComputePaperPacking
import Nock.NockVMROM.Thm54.P8Core.OptimizedHostileTimestamps
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
This module
discharges both the paper's way: from what the consumed compute chip `P.computeChip` commits
about the timestamp coordinate of every request record, plus one priced coin event.

## 1. What the optimized compute chip commits about timestamps (measured, §A–§D)

The paper's `mem_record_k = (…, timestamp_k)` with `timestamp_k = ln(i−1)·α^k` and the `ln` recurrence
`ln(i−1)·(α·Σ_{1,3,4} op + α²·Σ_{0,2,5,7,8} op + α³·Σ_{6,9} op) = ln(i)`
appear in the optimized layout as follows.

* **The timestamp field of every request record is not a committed column.**  Slot `j`'s eighth
  scalar is *decoded* from `ln_prev` (extension role `54`) and the timestamp challenge (compute
  challenge slot `0`): `computeTraceSubst 74 = ln_prev·α`, `mr2Field 7 = (op₀ + Σ_{2,5,6,7,8,9} op)·
  ln_prev·α²`, `mr3Field 7 = (op₆ + op₉)·ln_prev·α³` (`OptimizedComputeSubstitution`).  So for
  **every** typed row environment, with no gate and no hypothesis,
  `rowRecord env 0 7 = ln_prev·α`, `rowRecord env 1 7 = a₁·ln_prev·α²`, `rowRecord env 2 7 =
  a₂·ln_prev·α³` where `aⱼ = activeMask env j` (`rowRecord_ts_zero/one/two`,
  `rowRecord_ts_active`).  The paper's `:1852-1881` timestamp equations hold by construction.
* **The `ln` recurrence is committed**, per opcode, inside the eleven per-state source blocks
  (`Nock.Reified.memBlkExprs`: `ln − ln_prev·α^{arity}` gated by the opcode selector), which the
  chip folds with the compiler challenge `9` (`finalNonIOSourceFamilies17`, eight of the
  seventeen non-IO extension gates).  Reading a source equation off its fold needs the row's
  `FinalComputeCollisionFree` — the compute fold event the consumed bound already prices at
  `494·N` (`finalComputeRLCWorkload_exact`).
* **The cross-row hand-off `ln(i) = ln_prev(i+1)`** is the singleton fold `Trans.lnChainExpr`
  (extension gate `8`, masked off the last row): `ln_chain_at`.
* Now `OptimizedComputeCorrectedFinal.finalLnInit = isFirst · (ln_prev − 1)` sits in the
  compute chip's degree-two endpoint bucket and **`hostile_ln0_eq_one`** reads `ln₀ = 1` off any
  accepted trace (`rowRecord_ts_at` still states the general form).  The paper's uniqueness
  argument needs exactly this origin and its `V_comp` (`:1728-1742`)
  lacks it: the deployed chip is strictly stronger than `V_comp`, a disclosed deviation
  (`vcomp_s1_ignores_first_ln_prev`, `GenericHonestCommitment.lean`, is the exhibit).
* **The challenge slots.**  The NPR seed `z` plays
  no role in the timestamps; the collision event below is over `α` alone.

## 2. The event (§E)

`TimestampCollisionEvent D : Finset K` — the `α` for which two distinct exponents `1 ≤ e < e' ≤ D`
give `α^e = α^{e'}` (this includes `α = 0`).  Here `D` is
the number of hostile requests, which equals the total exponent `S(rows)` (`totalRequests_eq_length`).

## 3. The theorems (§F–§H)

* **`hostile_requests_nodup`**: for any accepted `Qc`, under `hchar`, the compute fold exclusion
  at every row and `alphaM ∉ TimestampCollisionEvent |hostileRequests|`,
  `(hostileRequests P Qc).Nodup` — distinct list entries have distinct timestamp coordinates.
  (Stage 1 also needed `hln0`; stage 2A discharges it from the chip.)
* **`FiniteIO.finiteIO_sound_of_identity'`**: `finiteIO_sound_of_identity` without `hrespnd`.
  The paper's `:2213` argument: the sampled-pole identity lifts to `Σ 1/(X+aᵢ) = Σ 1/(X+bⱼ)` in
  `K(X)`, `SetEq.mse_ldse_general` turns that into equality of the value **multisets**, and a
  multiset equal to a `Nodup` one is `Nodup`; RLC injectivity outside event (2) carries `Nodup`
  back to the response records (`hostile_responses_nodup_core`).
* **`hostile_LIO'`**: `hostile_LIO` with `hreqnd`/`hrespnd` replaced by `hcfree`, `hα`;
  every other hypothesis unchanged.  Non-vacuity: `concrete73_hostile_LIO'` at
  `concreteOptimizedFullStrictPackage` with the real acceptance.
-/

namespace Nock.NockVMROM.Thm54

/-! ## G. `finiteIO_sound_of_identity` without the response `Nodup` premise -/

namespace FiniteIO

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] {m : ℕ} [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]

/-- **`finiteIO_sound_of_identity` without `hrespnd`.**  Same statement, the response-side `Nodup`
derived by `responses_nodup_of_identity`. -/
theorem finiteIO_sound_of_identity' {Ksz : ℕ} (records : PreChallengeRecords K m)
    (coins : IOCoins K)
    (hdA : ∀ i, coins.pole + reqVals records coins.gamma i ≠ 0)
    (hdB : ∀ j, coins.pole + respVals records coins.gamma j ≠ 0)
    (hend : (∑ i, (coins.pole + reqVals records coins.gamma i)⁻¹) =
      ∑ j, (coins.pole + respVals records coins.gamma j)⁻¹)
    (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz records.requests.length)
    (hKresp : records.responses.length ≤ Ksz)
    (hreqnd : records.requests.Nodup)
    (hγ : coins.gamma ∉ IORLCCollisionEvent records)
    (hpole : coins.pole ∉ IOLogDerivEvent records coins.gamma) :
    IO.LIO Ksz records.requests records.responses :=
  finiteIO_sound_of_identity records coins hdA hdB hend hKp hKreq hKresp hreqnd
    (responses_nodup_of_identity records coins hdA hdB hend hKp hKreq hKresp hreqnd hγ hpole)
    hγ hpole

end FiniteIO

namespace OptimizedHostileTimestamps

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedComputeBaseGates
open OptimizedComputeFinal
open OptimizedComputeCorrectedFinal
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeFiniteIOGates
open OptimizedComputeSemanticRealization
open OptimizedComputeHostileAccumulator
open OptimizedMemoryGateBasis
open StrictExtension
open OptimizedStrictFullPackage
open OptimizedComputeFinalTrace
open ConcreteStrictPackage
open TemplateRawJointSoundness
open MultiRootOptimizedAcceptance
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F]
  [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## A. The timestamp coordinates of a typed row, definitionally

`ln_prev` is extension role `54`, `ln` role `55` (`OptimizedComputeSubstitution.lnPrev/lnCur`,
`ext0 + 54/55`), the timestamp base is challenge slot `0`. -/

/-! ## B. The `ln` recurrence, read off the committed per-state fold

the paper: `ln(i) = ln(i−1)·α^{arity(op)}` with `arity = 1` on `{1,3,4,cons}`, `2` on
`{0,2,5,7,8}`, `3` on `{6,9}`.  In the tree the equation is `memBlkExprs st`'s last entry
`ln − ln_prev·α^{arity}` (`Nock/AIR.lean`), selector-gated (`gateBy`) and folded into the
opcode's family with challenge `9`. -/

theorem arity_pos (s : ComputeTable.State) : 1 ≤ arity s := by cases s <;> decide

/-- Every per-state block is contained in one of the eight unmasked non-IO families
(`finalNonIOSourceFamilies17` positions `0,1,2,12..16`). -/
theorem stateBlock_subset_family (s : ComputeTable.State) :
    ∃ k : Fin 17, k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 10 ∧ k ≠ 11 ∧
      ∀ e ∈ stateBlock s, e ∈ finalNonIOSourceFamilies17.get
        ⟨k, by simp [finalNonIOSourceFamilies17, nonIOSourceFamilies17With]⟩ := by
  cases s
  · exact ⟨0, by decide, by decide, by decide, by decide,
      fun e he => List.mem_append_left _ he⟩
  · exact ⟨0, by decide, by decide, by decide, by decide,
      fun e he => List.mem_append_right _ he⟩
  · exact ⟨1, by decide, by decide, by decide, by decide,
      fun e he => List.mem_append_left _ he⟩
  · exact ⟨1, by decide, by decide, by decide, by decide,
      fun e he => List.mem_append_right _ he⟩
  · exact ⟨2, by decide, by decide, by decide, by decide,
      fun e he => List.mem_append_left _ he⟩
  · exact ⟨2, by decide, by decide, by decide, by decide,
      fun e he => List.mem_append_right _ he⟩
  · exact ⟨12, by decide, by decide, by decide, by decide, fun e he => he⟩
  · exact ⟨13, by decide, by decide, by decide, by decide, fun e he => he⟩
  · exact ⟨14, by decide, by decide, by decide, by decide, fun e he => he⟩
  · exact ⟨15, by decide, by decide, by decide, by decide, fun e he => he⟩
  · exact ⟨16, by decide, by decide, by decide, by decide, fun e he => he⟩

/-! ## B'. -/

/-! ## C. The cross-row hand-off `ln(i) = ln_prev(i+1)` (`Trans.lnChainExpr`, packed slot `73`) -/

section Arity

variable [DecidableEq K]

omit [FiniteDimensional F K] in
theorem rowArity_pos (env : CorrectedFinalTypedEnv F K) : 1 ≤ rowArity env := by
  unfold rowArity; split_ifs <;> omega

end Arity

/-! ## D. At the consumed chip: the exponent bookkeeping -/

section Deployed

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The timestamp base as the chip reads it: compute challenge slot `0`, a package field. -/
def chipAlpha : K :=
  ∑ k : Fin 3, P.optimized.computeChallenge (3 * 0 + (k : ℕ)) • P.optimized.basis k

variable (Qc : Fin P.computeChip.rap.w → F[X])

/-- The base is the same at every row (it is a challenge, not a column). -/
theorem alphaAt_rowEnv (i : Fin (rows P)) : alphaAt (rowEnv P Qc i) = chipAlpha P := by
  simp only [alphaAt, CorrectedFinalTypedEnv.toSourceEnv, rowEnv, gatherCorrectedFinalTypedEnv,
    envOfTrace]
  rfl

/-- **Which coin the timestamp base is**: `computeChallengePins` pins slot `0` to the package's
`cfg.challenges.α` for every trace (`exactFinalChallenge 0 = computeInputs.α`). -/
theorem chipAlpha_eq_cfg :
    chipAlpha P = P.optimized.family.problem.cfg.challenges.α := by
  have h0 : ∀ k : Fin 3, P.optimized.computeChallenge (3 * 0 + (k : ℕ)) =
      coord P.optimized.basis P.optimized.family.problem.cfg.challenges.α k :=
    fun k => P.optimized.computeChallengePins 0 k
  unfold chipAlpha
  simp_rw [h0]
  exact reconstruct_coord _ _

theorem chipZ_eq_cfg :
    (∑ k : Fin 3, P.optimized.computeChallenge (3 * 1 + (k : ℕ)) • P.optimized.basis k) =
      P.optimized.family.problem.cfg.challenges.z := by
  have h1 : ∀ k : Fin 3, P.optimized.computeChallenge (3 * 1 + (k : ℕ)) =
      coord P.optimized.basis P.optimized.family.problem.cfg.challenges.z k :=
    fun k => P.optimized.computeChallengePins 1 k
  simp_rw [h1]
  exact reconstruct_coord _ _

theorem chipZinv_eq_cfg :
    (∑ k : Fin 3, P.optimized.computeChallenge (3 * 5 + (k : ℕ)) • P.optimized.basis k) =
      P.optimized.family.problem.cfg.challenges.z⁻¹ := by
  have h5 : ∀ k : Fin 3, P.optimized.computeChallenge (3 * 5 + (k : ℕ)) =
      coord P.optimized.basis (P.optimized.family.problem.cfg.challenges.z⁻¹) k :=
    fun k => P.optimized.computeChallengePins 5 k
  simp_rw [h5]
  exact reconstruct_coord _ _

theorem zZinv_at_rowEnv (i : Fin (rows P))
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0) :
    (zZinvExpr.subst computeSubst).eval (rowEnv P Qc i).toSourceEnv = 0 := by
  have h1 : (rowEnv P Qc i).toSourceEnv.chal 1 =
      P.optimized.family.problem.cfg.challenges.z := by
    simp only [CorrectedFinalTypedEnv.toSourceEnv, rowEnv, gatherCorrectedFinalTypedEnv,
      envOfTrace]
    exact chipZ_eq_cfg P
  have h5 : (rowEnv P Qc i).toSourceEnv.chal 5 =
      P.optimized.family.problem.cfg.challenges.z⁻¹ := by
    simp only [CorrectedFinalTypedEnv.toSourceEnv, rowEnv, gatherCorrectedFinalTypedEnv,
      envOfTrace]
    exact chipZinv_eq_cfg P
  simp [zZinvExpr, Expr.subst, computeSubst, computeTraceSubst, chl, tc, Expr.eval, h1, h5]
  exact sub_eq_zero.mpr (mul_inv_cancel₀ hz0)

variable (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
include hsat

/-- A one-hot selector read at the source level. -/
theorem source_selector (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (i : Fin (rows P)) :
    ∃ s, ∀ st, (rowEnv P Qc i).toSourceEnv.trace (opCol st) = ComputeTable.opSel s st := by
  obtain ⟨s, hs⟩ := rowSelector_oneHot P Qc hsat hchar i
  refine ⟨s, fun st => ?_⟩
  rw [source_trace_base _ (opCol st) (by cases st <;> decide)]
  exact congrFun hs st

omit hsat in
/-- Under a one-hot selector the mask-derived arity is the opcode's. -/
theorem rowArity_eq_arity (i : Fin (rows P)) (s : ComputeTable.State)
    (hsel : ∀ st, (rowEnv P Qc i).toSourceEnv.trace (opCol st) = ComputeTable.opSel s st) :
    rowArity (rowEnv P Qc i) = arity s := by
  have h0 := hsel .s0; have h2 := hsel .s2; have h5 := hsel .s5; have h6 := hsel .s6
  have h7 := hsel .s7; have h8 := hsel .s8; have h9 := hsel .s9
  simp only [opCol] at h0 h2 h5 h6 h7 h8 h9
  unfold rowArity
  simp only [activeMask, sampledActive, Expr.eval, Fin.isValue, Fin.val_one, Fin.val_two, h0, h2,
    h5, h6, h7, h8, h9]
  cases s <;> simp [ComputeTable.opSel, arity]

/-- **The `ln` recurrence at the consumed chip.**  At every row of an
accepted trace, under `hchar`, `ln = ln_prev · chipAlpha^{rowArity}`. -/
theorem ln_recurrence_at (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0)
    (i : Fin (rows P)) :
    lnCurAt (rowEnv P Qc i) =
      lnPrevAt (rowEnv P Qc i) * chipAlpha P ^ rowArity (rowEnv P Qc i) := by
  obtain ⟨s, hsel⟩ := source_selector P Qc hsat hchar i
  have h := ln_recurrence (row_obligations P Qc hsat i) s hsel (zZinv_at_rowEnv P Qc i hz0)
  rw [alphaAt_rowEnv] at h
  rw [rowArity_eq_arity P Qc i s hsel]
  exact h

/-- The hand-off at the consumed chip: off the last row, `ln(i) = ln_prev(i+1)`. -/
theorem ln_chain_at (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    lnCurAt (rowEnv P Qc i) = lnPrevAt (rowEnv P Qc ⟨(i : ℕ) + 1, hi⟩) := by
  have hnl : (rowEnv P Qc i).baseTrace 12 = 0 := by
    rw [(masks_at_row P Qc hsat i).2, if_neg]
    intro heq
    have hv : (i : ℕ) = rows P - 1 := congrArg Fin.val heq
    omega
  rw [ln_chain (row_obligations P Qc hsat i) hnl]
  -- orbit alignment of role `54`, as `next_acc` does for role `32`
  have hadj := P.optimized.computeAdjacentOrbit i hi
  unfold lnPrevAt
  simp only [rowEnv, gatherCorrectedFinalTypedEnv]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hlt : correctedFinalExtCoordIndex (e := 3) (54 : Fin 63) k < P.computeChip.rap.w := by
    change _ < 303; simp [correctedFinalExtCoordIndex]; omega
  simp only [envOfTrace, dif_pos hlt]
  rw [hadj]

omit hsat in
/-- `S(m) = Σ_{i < m} rowArity(i)`: the exponent `ln_prev(m)` carries over `ln_prev(0)`. -/
def prefixExp (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range m, if h : k < rows P then rowArity (rowEnv P Qc ⟨k, h⟩) else 0

omit hsat in
theorem prefixExp_succ (m : ℕ) (hm : m < rows P) :
    prefixExp P Qc (m + 1) = prefixExp P Qc m + rowArity (rowEnv P Qc ⟨m, hm⟩) := by
  simp [prefixExp, Finset.sum_range_succ, hm]

omit hsat in
theorem prefixExp_mono {a b : ℕ} (hab : a ≤ b) : prefixExp P Qc a ≤ prefixExp P Qc b := by
  unfold prefixExp
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) (fun _ _ _ => Nat.zero_le _)

omit hsat in
/-- `ln_prev` of row `0`. -/
def ln0 : K := lnPrevAt (rowEnv P Qc (firstRow P))

theorem hostile_ln0_eq_one : ln0 P Qc = 1 := by
  have hgate := (row_obligations P Qc hsat (firstRow P)).endpointDegreeTwo2 _ lnInit_mem_endpoint2
  rw [lnInit_eval, (masks_at_row P Qc hsat (firstRow P)).1] at hgate
  simp only [firstRow, Fin.val_mk, if_true, map_one, one_mul, sub_eq_zero] at hgate
  exact hgate

/-- The former premise `hln0` of `hostile_requests_nodup` / `hostile_LIO'`, now a theorem. -/
theorem hostile_ln0_ne_zero : ln0 P Qc ≠ 0 := by
  rw [hostile_ln0_eq_one P Qc hsat]; exact one_ne_zero

/-- **`ln_prev(m) = ln₀ · α^{S(m)}`** at every row of an accepted trace, from the recurrence and
the hand-off. -/
theorem lnPrev_at (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0) :
    ∀ (m : ℕ) (hm : m < rows P),
      lnPrevAt (rowEnv P Qc ⟨m, hm⟩) = ln0 P Qc * chipAlpha P ^ prefixExp P Qc m := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [prefixExp, Finset.range_zero, Finset.sum_empty, pow_zero, mul_one]
      rfl
  | succ m ih =>
      intro hm
      have hm' : m < rows P := by omega
      rw [← ln_chain_at P Qc hsat ⟨m, hm'⟩ hm,
        ln_recurrence_at P Qc hsat hchar hz0 ⟨m, hm'⟩, ih hm', prefixExp_succ P Qc m hm',
        pow_add, mul_assoc]

omit hsat in
/-- The exponent of the `j`-th slot of row `i`: `S(i) + j + 1`. -/
def expOf (i : Fin (rows P)) (j : Fin 3) : ℕ := prefixExp P Qc i + (j : ℕ) + 1

/-- **`hostile_timestamp_eq` — the committed timestamp of every active request slot at the
consumed chip:** `ts(i, j) = ln₀ · α^{S(i) + j + 1}`, for any accepted
trace under `hchar`. -/
theorem rowRecord_ts_at (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0)
    (i : Fin (rows P)) (j : Fin 3) (hact : activeMask (rowEnv P Qc i) j = 1) :
    rowRecord (rowEnv P Qc i) j 7 = ln0 P Qc * chipAlpha P ^ expOf P Qc i j := by
  rw [rowRecord_ts_active _ j hact, alphaAt_rowEnv, lnPrev_at P Qc hsat hchar hz0 i i.isLt,
    expOf, mul_assoc, ← pow_add]
  rfl

/-- The task's name for `rowRecord_ts_at`: the exact committed timestamp form
`ts(i, j) = ln₀ · α^{S(i) + j + 1}`. -/
theorem hostile_timestamp_eq (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0)
    (i : Fin (rows P)) (j : Fin 3) (hact : activeMask (rowEnv P Qc i) j = 1) :
    rowRecord (rowEnv P Qc i) j 7 =
      ln0 P Qc * chipAlpha P ^ (prefixExp P Qc i + (j : ℕ) + 1) :=
  rowRecord_ts_at P Qc hsat hchar hz0 i j hact

omit hsat in
/-- The total exponent budget: `S(rows)`. -/
def totalRequests : ℕ := prefixExp P Qc (rows P)

omit hsat in
theorem totalRequests_le : totalRequests P Qc ≤ 3 * rows P := by
  unfold totalRequests prefixExp
  calc (∑ k ∈ Finset.range (rows P), if h : k < rows P then rowArity (rowEnv P Qc ⟨k, h⟩) else 0)
      ≤ ∑ _k ∈ Finset.range (rows P), 3 := by
        refine Finset.sum_le_sum fun k _ => ?_
        split_ifs
        · exact rowArity_le _
        · omega
    _ = 3 * rows P := by simp [mul_comm]

omit hsat in
theorem expOf_pos (i : Fin (rows P)) (j : Fin 3) : 1 ≤ expOf P Qc i j := by
  unfold expOf; omega

omit hsat in
/-- Every active exponent is at most the total. -/
theorem expOf_le_total (i : Fin (rows P)) (j : Fin 3) (hact : activeMask (rowEnv P Qc i) j = 1) :
    expOf P Qc i j ≤ totalRequests P Qc := by
  have h1 := active_lt_rowArity (rowEnv P Qc i) j hact
  have h2 : prefixExp P Qc ((i : ℕ) + 1) ≤ prefixExp P Qc (rows P) :=
    prefixExp_mono P Qc i.isLt
  rw [prefixExp_succ P Qc i i.isLt, Fin.eta] at h2
  unfold expOf totalRequests
  omega

omit hsat in
/-- Exponents are strictly increasing across rows. -/
theorem expOf_lt_of_row_lt {i i' : Fin (rows P)} (hii : i < i') (j j' : Fin 3)
    (hact : activeMask (rowEnv P Qc i) j = 1) :
    expOf P Qc i j < expOf P Qc i' j' := by
  have h1 := active_lt_rowArity (rowEnv P Qc i) j hact
  have h2 : prefixExp P Qc ((i : ℕ) + 1) ≤ prefixExp P Qc i' := prefixExp_mono P Qc hii
  rw [prefixExp_succ P Qc i i.isLt, Fin.eta] at h2
  unfold expOf
  omega

omit hsat in
/-- Exponents within a row separate the slots. -/
theorem expOf_inj_row (i : Fin (rows P)) {j j' : Fin 3} (h : expOf P Qc i j = expOf P Qc i j') :
    j = j' := by
  unfold expOf at h
  exact Fin.ext (by omega)

omit hsat in
/-- With boolean masks (and slot `2` active only when slot `1` is), the row emits exactly
`rowArity` records. -/
theorem rowRequests_length (i : Fin (rows P))
    (hbool : ∀ j : Fin 3, activeMask (rowEnv P Qc i) j = 0 ∨ activeMask (rowEnv P Qc i) j = 1)
    (h21 : activeMask (rowEnv P Qc i) 2 = 1 → activeMask (rowEnv P Qc i) 1 = 1) :
    (rowRequests (rowEnv P Qc i)).length = rowArity (rowEnv P Qc i) := by
  have h0 := activeMask_zero (rowEnv P Qc i)
  simp only [rowRequests, List.finRange, List.ofFn_succ, List.ofFn_zero, List.filterMap_cons,
    List.filterMap_nil, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, h0, if_true, rowArity]
  rcases hbool 2 with h2 | h2
  · rcases hbool 1 with h1 | h1
    · simp [h1, h2]
    · simp [h1, h2]
  · have h1 := h21 h2
    simp [h1, h2]

omit hsat in
theorem active_two_imp_one (i : Fin (rows P)) (s : ComputeTable.State)
    (hsel : ∀ st, (rowEnv P Qc i).toSourceEnv.trace (opCol st) = ComputeTable.opSel s st) :
    activeMask (rowEnv P Qc i) 2 = 1 → activeMask (rowEnv P Qc i) 1 = 1 := by
  have h0 := hsel .s0; have h2 := hsel .s2; have h5 := hsel .s5; have h6 := hsel .s6
  have h7 := hsel .s7; have h8 := hsel .s8; have h9 := hsel .s9
  simp only [opCol] at h0 h2 h5 h6 h7 h8 h9
  simp only [activeMask, sampledActive, Expr.eval, Fin.isValue, Fin.val_one, Fin.val_two, h0, h2,
    h5, h6, h7, h8, h9]
  cases s <;> simp [ComputeTable.opSel]

/-- **The total exponent is the number of hostile requests**: the exponents `1..|hostileRequests|`
are exactly the active slots' exponents. -/
theorem totalRequests_eq_length (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) :
    totalRequests P Qc = (hostileRequests P Qc).length := by
  unfold totalRequests prefixExp hostileRequests
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn,
    ← Fin.sum_univ_eq_sum_range
      (fun k => if h : k < rows P then rowArity (rowEnv P Qc ⟨k, h⟩) else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨s, hsel⟩ := source_selector P Qc hsat hchar i
  simp only [i.isLt, dite_true, Function.comp]
  rw [rowRequests_length P Qc i (fun j => activeMask_bool P Qc hsat hchar i j)
    (active_two_imp_one P Qc i s hsel)]

end Deployed

/-! ## E. The timestamp collision event and its degree count -/

/-! ## F. `Nodup` of the hostile request list -/

section Nodup

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
  (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
  (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0)
  (hα : chipAlpha P ∉ TimestampCollisionEvent (totalRequests P Qc))
include hsat hchar hz0 hα

/-- **Distinct active slots have distinct committed timestamps** (outside the event; `ln₀ = 1` is
now the chip's, `hostile_ln0_eq_one`): equal timestamp coordinates force equal exponents. -/
theorem expOf_eq_of_ts_eq {i i' : Fin (rows P)} {j j' : Fin 3}
    (hact : activeMask (rowEnv P Qc i) j = 1) (hact' : activeMask (rowEnv P Qc i') j' = 1)
    (h : rowRecord (rowEnv P Qc i) j 7 = rowRecord (rowEnv P Qc i') j' 7) :
    expOf P Qc i j = expOf P Qc i' j' := by
  rw [rowRecord_ts_at P Qc hsat hchar hz0 i j hact,
    rowRecord_ts_at P Qc hsat hchar hz0 i' j' hact'] at h
  have hpow := mul_left_cancel₀ (hostile_ln0_ne_zero P Qc hsat) h
  exact pow_inj_of_not_collision hα (expOf_pos P Qc i j) (expOf_le_total P Qc i j hact)
    (expOf_pos P Qc i' j') (expOf_le_total P Qc i' j' hact') hpow

/-- Each row's emitted records are pairwise distinct. -/
theorem rowRequests_nodup (i : Fin (rows P)) : (rowRequests (rowEnv P Qc i)).Nodup := by
  unfold rowRequests
  refine List.Nodup.filterMap ?_ (List.nodup_finRange 3)
  intro j j' r hj hj'
  by_cases ha : activeMask (rowEnv P Qc i) j = 1
  · rw [if_pos ha] at hj
    by_cases ha' : activeMask (rowEnv P Qc i) j' = 1
    · rw [if_pos ha'] at hj'
      have hr : rowRecord (rowEnv P Qc i) j = rowRecord (rowEnv P Qc i) j' :=
        (Option.some_inj.mp hj).trans (Option.some_inj.mp hj').symm
      exact expOf_inj_row P Qc i
        (expOf_eq_of_ts_eq P Qc hsat hchar hz0 hα ha ha' (congrFun hr 7))
    · rw [if_neg ha'] at hj'; cases hj'
  · rw [if_neg ha] at hj; cases hj

/-- Records emitted by different rows are disjoint. -/
theorem rowRequests_disjoint {i i' : Fin (rows P)} (hii : i < i') :
    List.Disjoint (rowRequests (rowEnv P Qc i)) (rowRequests (rowEnv P Qc i')) := by
  intro r hr hr'
  simp only [rowRequests, List.mem_filterMap, List.mem_finRange, true_and] at hr hr'
  obtain ⟨j, hj⟩ := hr
  obtain ⟨j', hj'⟩ := hr'
  by_cases ha : activeMask (rowEnv P Qc i) j = 1
  · by_cases ha' : activeMask (rowEnv P Qc i') j' = 1
    · rw [if_pos ha] at hj
      rw [if_pos ha'] at hj'
      have hr : rowRecord (rowEnv P Qc i) j = rowRecord (rowEnv P Qc i') j' :=
        (Option.some_inj.mp hj).trans (Option.some_inj.mp hj').symm
      have heq := expOf_eq_of_ts_eq P Qc hsat hchar hz0 hα ha ha' (congrFun hr 7)
      have hlt := expOf_lt_of_row_lt P Qc hii j j' ha
      omega
    · rw [if_neg ha'] at hj'; cases hj'
  · rw [if_neg ha] at hj; cases hj

/-- **`hostile_requests_nodup`.**  For any
trace `P.computeChip` accepts, under `hchar`, the compute fold exclusion at every row and
`α ∉ TimestampCollisionEvent (total exponent)`, the hostile request list is `Nodup`: distinct
entries have distinct timestamp coordinates. -/
theorem hostile_requests_nodup_of_total : (hostileRequests P Qc).Nodup := by
  unfold hostileRequests
  rw [List.nodup_flatten]
  constructor
  · intro l hl
    rw [List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    exact rowRequests_nodup P Qc hsat hchar hz0 hα i
  · rw [List.pairwise_ofFn]
    intro i i' hii
    exact rowRequests_disjoint P Qc hsat hchar hz0 hα hii

end Nodup

section NodupLength

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])

/-- **`hostile_requests_nodup`**, with the event parametrised by the request count itself. -/
theorem hostile_requests_nodup
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0)
    (hα : chipAlpha P ∉ TimestampCollisionEvent (hostileRequests P Qc).length) :
    (hostileRequests P Qc).Nodup := by
  rw [← totalRequests_eq_length P Qc hsat hchar] at hα
  exact hostile_requests_nodup_of_total P Qc hsat hchar hz0 hα

end NodupLength

/-! ## H. `hostile_LIO'` — `hostile_LIO` with the `Nodup` premises discharged -/

section Assembly

open OptimizedHostileIOAssembly

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])

/-- The fold exclusion in the package's own `computeSourceEnv` form is the row form. -/
theorem computeSourceEnv_eq (i : Fin (rows P)) :
    P.computeSourceEnv Qc i = (rowEnv P Qc i).toSourceEnv := rfl

/-- **`hostile_responses_nodup_of_identity`**: at the chips' own coins, the response list is
`Nodup` as a consequence of the identity and the request-side `Nodup`. -/
theorem hostile_responses_nodup_core {Ksz : ℕ}
    (hsatc : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hsatm : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
    (hbool : ∀ (i : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnv P Qc i) j = 0 ∨ activeMask (rowEnv P Qc i) j = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequests P Qc).length)
    (hKresp : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).length ≤ Ksz)
    (hreqnd : (hostileRequests P Qc).Nodup)
    (hpoleHit : P.optimized.sampled.sampled.coins.pole ∉
      FiniteIO.IOPoleHitEvent (hostileRecords P Qc Qm) P.optimized.sampled.sampled.coins.gamma)
    (hγ : P.optimized.sampled.sampled.coins.gamma ∉
      FiniteIO.IORLCCollisionEvent (hostileRecords P Qc Qm))
    (hpoleEv : P.optimized.sampled.sampled.coins.pole ∉
      FiniteIO.IOLogDerivEvent (hostileRecords P Qc Qm) P.optimized.sampled.sampled.coins.gamma) :
    (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).Nodup := by
  set coins := P.optimized.sampled.sampled.coins with hcoinsdef
  have hpole := pole_excluded_of_not_poleHit P Qc Qm (by
    rw [compute_chipCoins_eq_sampled]; exact hpoleHit)
  have hdA : ∀ i, coins.pole + FiniteIO.reqVals (hostileRecords P Qc Qm) coins.gamma i ≠ 0 := by
    intro i
    rw [pole_add_reqVals, hcoinsdef, ← compute_chipCoins_eq_sampled]
    exact compress_request_ne_zero P Qc hpole (List.get_mem (hostileRecords P Qc Qm).requests i)
  have hdB : ∀ j, coins.pole + FiniteIO.respVals (hostileRecords P Qc Qm) coins.gamma j ≠ 0 := by
    intro j
    rw [pole_add_respVals, hcoinsdef, ← memory_chipCoins_eq_sampled P Qm]
    exact compress_response_ne_zero P Qm hsatm
      (List.get_mem (hostileRecords P Qc Qm).responses j)
  have hend : (∑ i, (coins.pole + FiniteIO.reqVals (hostileRecords P Qc Qm) coins.gamma i)⁻¹) =
      ∑ j, (coins.pole + FiniteIO.respVals (hostileRecords P Qc Qm) coins.gamma j)⁻¹ := by
    have h := hostile_io_identity_core P Qc Qm hsatc hsatm hbool hpole
    rw [← hostileRecords_requests P Qc Qm, ← hostileRecords_responses P Qc Qm,
      sum_requests_eq_sum_fin, sum_responses_eq_sum_fin] at h
    exact h
  exact FiniteIO.responses_nodup_of_identity (hostileRecords P Qc Qm) coins hdA hdB hend
    hKp hKreq hKresp hreqnd hγ hpoleEv

section Acceptance

variable [Fintype F] [DecidableEq F]

section PackageZ
omit Qc Qm
omit [Fintype F] [DecidableEq F]

/-- **The NPR seed `cfg.challenges.z` is the package's `honestSeed`.**
`honest_specialization` plus `specializedProblem_seed` pin `objects.cfg.z`; `family_cfg`
identifies the family configuration the compute chip reads (`computeChallengePins` slot 1). -/
theorem cfg_z_eq_honestSeed :
    P.optimized.family.problem.cfg.challenges.z = P.honestSeed := by
  have hfam : P.optimized.family.problem.cfg = P.objects.cfg := P.optimized.family_cfg
  have hobj : P.objects.cfg.challenges.z = P.honestSeed := by
    have h := congrArg (fun Q : RawProblem F K => Q.cfg.challenges.z) P.honest_specialization
    exact h.symm.trans (specializedProblem_seed P.optimized.verifier.raw.timestamp
      P.honestSeed P.honestSeed_ne P.honestAlpha _)
  exact (congrArg (fun cfg : ExactConfig F K => cfg.challenges.z) hfam).trans hobj

/-- **Package-field `hz0`.**  `honestSeed_ne`; the MF pattern. -/
theorem hz0_of_package : P.optimized.family.problem.cfg.challenges.z ≠ 0 := by
  rw [cfg_z_eq_honestSeed]
  exact P.honestSeed_ne

end PackageZ

variable (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)

theorem chipAlpha_eq_alphaM (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    chipAlpha P = alphaM c.1 := by
  rw [chipAlpha_eq_cfg]
  have h := hacc.same_problem.specialized_cfg_eq_family
  exact (congrArg (fun cfg : ExactConfig F K => cfg.challenges.α) h).symm

/-- **`hz0` from `hgood` (route (a)).**  Both hypotheses are already on
`optimizedFullStrict_hostile_LIO`. -/
theorem hz0_of_good (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm) :
    P.optimized.family.problem.cfg.challenges.z ≠ 0 := by
  have hz := congrArg (fun cfg : ExactConfig F K => cfg.challenges.z)
    hacc.same_problem.specialized_cfg_eq_family
  rw [hz.symm.trans (specializedProblem_seed P.optimized.verifier.raw.timestamp
    (nprSeed c.1) hacc.same_problem.nprSeed_ne (alphaM c.1) c.2.2.2.lambda)]
  exact nprSeed_ne_of_good P Qc Qm c hgood

/-- `OptimizedHostileIOAssembly.hostile_LIO` with the two
`Nodup` premises `hreqnd`/`hrespnd` replaced by `hα` — the sampled `alphaM c.1` is outside
`TimestampCollisionEvent |hostileRequests|` (`card ≤ 1 + D(D−1)/2`).  The compute-fold
exclusion `hcfree` is gone: the packed `ln` gate is read directly (`ln_recurrence`).

Every other hypothesis is unchanged.  `hreqnd` is `hostile_requests_nodup`; `hrespnd` is
`hostile_responses_nodup_core`. -/
theorem hostile_LIO' {Ksz : ℕ} (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0)
    (hα : alphaM c.1 ∉ TimestampCollisionEvent (hostileRequests P Qc).length)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequests P Qc).length)
    (hKresp : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).length ≤ Ksz)
    (hpoleHit : c.2.1.2 ∉ FiniteIO.IOPoleHitEvent (hostileRecords P Qc Qm) c.2.1.1)
    (hγ : c.2.1.1 ∉ FiniteIO.IORLCCollisionEvent (hostileRecords P Qc Qm))
    (hpoleEv : c.2.1.2 ∉ FiniteIO.IOLogDerivEvent (hostileRecords P Qc Qm) c.2.1.1) :
    IO.LIO Ksz (hostileRequests P Qc)
      (OptimizedMemoryHostileAccumulator.hostileResponses P Qm) := by
  have hα' : chipAlpha P ∉ TimestampCollisionEvent (hostileRequests P Qc).length := by
    rw [chipAlpha_eq_alphaM P Qc Qm c hacc]; exact hα
  have hreqnd : (hostileRequests P Qc).Nodup :=
    hostile_requests_nodup P Qc hacc.compute_satisfies hchar hz0 hα'
  have hcoins := sampled_eq_sampledCoins P Qc Qm c hacc
  have hγ' : P.optimized.sampled.sampled.coins.gamma ∉
      FiniteIO.IORLCCollisionEvent (hostileRecords P Qc Qm) := by rw [hcoins]; exact hγ
  have hpoleHit' : P.optimized.sampled.sampled.coins.pole ∉
      FiniteIO.IOPoleHitEvent (hostileRecords P Qc Qm) P.optimized.sampled.sampled.coins.gamma := by
    rw [hcoins]; exact hpoleHit
  have hpoleEv' : P.optimized.sampled.sampled.coins.pole ∉
      FiniteIO.IOLogDerivEvent (hostileRecords P Qc Qm) P.optimized.sampled.sampled.coins.gamma := by
    rw [hcoins]; exact hpoleEv
  have hbool := fun i j => activeMask_bool P Qc hacc.compute_satisfies hchar i j
  have hrespnd : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).Nodup :=
    hostile_responses_nodup_core P Qc Qm hacc.compute_satisfies hacc.memory_satisfies hbool
      hKp hKreq hKresp hreqnd hpoleHit' hγ' hpoleEv'
  exact hostile_LIO P Qc Qm c hacc hchar hKp hKreq hKresp hreqnd hrespnd hpoleHit hγ hpoleEv

/-- The capstone's named hostile-IO conclusion is the family-chip
`FamilyIOChain.optimizedFullStrict_hostile_LIO_at`. -/
theorem optimizedFullStrict_hostile_LIO_historical {Ksz : ℕ}
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hio : c.2.1 ∉ FiniteIO.IOFailureEvent (hostileRecords P Qc Qm))
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequests P Qc).length)
    (hKresp : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).length ≤ Ksz) :
    IO.LIO Ksz (hostileRequests P Qc)
      (OptimizedMemoryHostileAccumulator.hostileResponses P Qm) := by
  have hnot : ¬ (c.2.1.1 ∈ FiniteIO.IORLCCollisionEvent (hostileRecords P Qc Qm) ∨
      c.2.1.2 ∈ FiniteIO.IOPoleHitEvent (hostileRecords P Qc Qm) c.2.1.1 ∨
      c.2.1.2 ∈ FiniteIO.IOLogDerivEvent (hostileRecords P Qc Qm) c.2.1.1) := by
    intro h
    apply hio
    simp only [FiniteIO.IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  have hα : alphaM c.1 ∉ TimestampCollisionEvent (hostileRequests P Qc).length := by
    have h := (P.optimizedFailureEvent_good_components Qc Qm c hgood).2.2.1
    rwa [← hostileRequests_eq_package] at h
  exact hostile_LIO' P Qc Qm c hacc hchar (hz0_of_good P Qc Qm c hacc hgood) hα hKp hKreq hKresp
    (fun h => hnot (Or.inr (Or.inl h))) (fun h => hnot (Or.inl h))
    (fun h => hnot (Or.inr (Or.inr h)))

/-! ## H'.

`OptimizedFullStrictThm54Statement.shared_io` and the target's `sampled_io` state `IO.LIO` at the
**honest** records `P.objects.reqRecs / respRecs` (the package's own `FiniteIOStrategy.lio`).
Since stage 2B the consumed failure event prices the three IO events at the traces' own records
and the α-collision event at the trace's request count, so every probabilistic premise of
`hostile_LIO'` is now a field of the genuine target reached by `acceptance_to_target`:
`hostile_io_event_good` (events (1)–(3) over `hostileRecords`), `timestamp_collision_good` (`hα`),
and `memory_collision_good` (→ `hfold`).  `hz0 : cfg.z ≠ 0` is discharged from `hacc`/`hgood`.  What remains explicit is what no gate supplies
(`LY` §2, `MA` §2): `hchar`, the range premises `hKp`/`hKreq`/`hKresp`. -/

end Acceptance

end Assembly

/-! ## I. Non-vacuity — the honest first row and the F73 package -/

section Canonical

open OptimizedComputeCanonicalDenominator

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- At the honest trace, `ln_prev` of row `i` is the execution's `ln_prev`. -/
theorem canonical_lnPrevAt [Fintype F] [DecidableEq F] (i : Fin (rows P)) :
    lnPrevAt (honestRow P i) = (P.optimized.family.problem.exec.computePubAt i).ln_prev := by
  have h1 : lnPrevAt (honestRow P i) = (lnPrev .traceCur).eval (honestRow P i).toSourceEnv :=
    (source_trace_lnPrev _).symm
  rw [h1, honestRow_eval_eq P i _ (by decide)]
  have h2 : (lnPrev .traceCur).eval (exactRow P i).toSourceEnv =
      (Env.ofSubst computeSubst (exactRow P i).toSourceEnv).trace 65 := by
    rw [← subst_tc65]; rfl
  rw [h2, OptimizedComputeSameExecution.exactFinalCurrentEnv_table_current P.optimized.sampled P.optimized.computeObligations i
    65 (by norm_num)]
  rfl

/-- **`ln₀` at the honest trace is the execution's first `ln_prev`** — which the package's
`computeLineOrigin` field makes `1`, as the chip's `finalLnInit` gate now requires. -/
theorem canonical_ln0 [Fintype F] [DecidableEq F] :
    ln0 P (canonicalComputeTrace P) =
      (P.optimized.family.problem.exec.computePubAt (firstRow P)).ln_prev :=
  canonical_lnPrevAt P (firstRow P)

end Canonical

section F73

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.BuildablePackage.Concrete
open OptimizedStrictFullPackage.Concrete
open OptimizedHostileIOAssembly
open OptimizedComputeCanonicalDenominator

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- The F73 package has one compute row. -/
theorem concrete73_rows : rows concreteOptimizedFullStrictPackage = 1 := by
  change (ConcreteStrictPackage.cfg honestSeed honestAlpha).compRows = 1
  norm_num [ConcreteStrictPackage.cfg]

/-- The honest first `ln_prev` at F73 is `1` — read off the execution, agreeing with what the chip
now pins (`hostile_ln0_eq_one`). -/
theorem concrete73_ln0 :
    ln0 concreteOptimizedFullStrictPackage
      (canonicalComputeTrace concreteOptimizedFullStrictPackage) = 1 := by
  rw [canonical_ln0]
  have h := OptimizedComputeSampledTrace.Concrete.honest_computePubAt
  have hij : firstRow concreteOptimizedFullStrictPackage =
      OptimizedComputeSampledTrace.Concrete.honestRowIndex := Fin.ext rfl
  rw [hij]
  change (honestLegacyFamily.problem.exec.computePubAt
    OptimizedComputeSampledTrace.Concrete.honestRowIndex).ln_prev = 1
  rw [h]
  rfl

/-- `honestAlpha ≠ 0` (it has order `9`). -/
theorem honestAlpha_ne_zero : honestAlpha ≠ 0 := by
  intro h0
  have h := pow_orderOf_eq_one honestAlpha
  rw [honestAlpha_order, h0, zero_pow (by norm_num)] at h
  exact zero_ne_one h

/-- **`hα` at F73**: the request count is at most `3 · rows = 3 < 9 = orderOf honestAlpha`. -/
theorem concrete73_alpha_not_collision
    (hax : FormRAxisBound
      concreteOptimizedFullStrictPackage.optimized.sampled
      concreteOptimizedFullStrictPackage.optimized.basis)
    (hbasis : FormRBasis concreteOptimizedFullStrictPackage.optimized.basis)
    (hwidth : FormRWidth F73) :
    alphaM concreteProductionChallenge.1 ∉
      TimestampCollisionEvent
        (hostileRequests concreteOptimizedFullStrictPackage
          (canonicalComputeTrace concreteOptimizedFullStrictPackage)).length := by
  have hlen : (hostileRequests concreteOptimizedFullStrictPackage
      (canonicalComputeTrace concreteOptimizedFullStrictPackage)).length ≤ 3 := by
    rw [← totalRequests_eq_length _ _
      (canonicalComputeTrace_satisfies _ hax hbasis hwidth)
      OptimizedHostileIOAssembly.hchar_K73cubic]
    have := totalRequests_le concreteOptimizedFullStrictPackage
      (canonicalComputeTrace concreteOptimizedFullStrictPackage)
    rw [concrete73_rows] at this
    omega
  change honestAlpha ∉ _
  exact not_mem_event_of_le_orderOf honestAlpha_ne_zero (by rw [honestAlpha_order]; omega)

theorem concrete73_hostile_LIO'
    (hax : FormRAxisBound
      concreteOptimizedFullStrictPackage.optimized.sampled
      concreteOptimizedFullStrictPackage.optimized.basis)
    (hbasis : FormRBasis basis73)
    (hwidth : FormRWidth F73)
    (hmoreC : ∀ i : Fin honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < honestLegacyFamily.problem.cfg.kMem →
        (honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0) :
    IO.LIO concreteOptimizedFullStrictPackage.optimized.family.problem.cfg.Ksz
      (hostileRequests concreteOptimizedFullStrictPackage concreteComputeTrace)
      (OptimizedMemoryHostileAccumulator.hostileResponses concreteOptimizedFullStrictPackage
        concreteMemoryTrace) := by
  rw [concreteComputeTrace_eq, concreteMemoryTrace_eq]
  have hR := canonical_hostileRecords concreteOptimizedFullStrictPackage hax hwidth
  have hreq := canonical_hostileRequests concreteOptimizedFullStrictPackage hax hwidth
  have hresp := canonical_hostileResponses concreteOptimizedFullStrictPackage
  have hacc : concreteOptimizedFullStrictPackage.OptimizedHistoricalAcceptanceAt
      (canonicalComputeTrace concreteOptimizedFullStrictPackage)
      (canonicalMemoryTrace concreteOptimizedFullStrictPackage)
      concreteProductionChallenge := concrete_production_acceptance hbasis hmoreC
  have hl := concreteOptimizedFullStrictPackage.optimized.sampled.lio10
  have hfail := concreteOptimizedFullStrictPackage.optimized.sampled.ioGood10
  simp only [FiniteIO.IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    not_or] at hfail
  have hcoins := OptimizedHostileIOAssembly.sampled_eq_sampledCoins
    concreteOptimizedFullStrictPackage _ _ concreteProductionChallenge hacc
  refine hostile_LIO' concreteOptimizedFullStrictPackage _ _ concreteProductionChallenge hacc
    OptimizedHostileIOAssembly.hchar_K73cubic
    ConcreteStrictPackage.honestSeed_ne
    (concrete73_alpha_not_collision hax hbasis hwidth)
    concreteOptimizedFullStrictPackage.optimized.sampled.sampled.charBound ?_ ?_ ?_ ?_ ?_
  · rw [hreq, hl.2.2.length_eq]; exact hl.1
  · rw [hresp]; exact hl.1.2
  · rw [hR]; have h := hfail.2.1; rw [hcoins] at h; exact h
  · rw [hR]; have h := hfail.1; rw [hcoins] at h; exact h
  · rw [hR]; have h := hfail.2.2; rw [hcoins] at h; exact h

end F73

end

end OptimizedHostileTimestamps
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.FiniteIO.responses_nodup_of_identity
#print axioms Nock.NockVMROM.Thm54.FiniteIO.finiteIO_sound_of_identity'
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.rowRecord_ts_active
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.ln_recurrence
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.ln_chain
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.rowRecord_ts_at
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hostile_timestamp_eq
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.TimestampCollisionEvent_card_le
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hostile_ln0_eq_one
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hostile_requests_nodup
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hostile_responses_nodup_core
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.cfg_z_eq_honestSeed
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hz0_of_package
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.nprSeed_ne_of_good
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hz0_of_good
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hostile_LIO'
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.canonical_ln0
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.concrete73_hostile_LIO'
