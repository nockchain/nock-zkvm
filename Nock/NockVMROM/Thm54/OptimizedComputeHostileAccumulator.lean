import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.HostileRecordLists
import Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
import Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists
import Nock.NockVMROM.Thm54.P8Core.OptimizedComputeHostileAccumulator
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# The compute chip's IO accumulator, telescoped hostilely

* the unmasked step `correctedAccAfterStep` — `(acc_after − acc)·d₀d₁d₂ = a₀d₁d₂ + a₁d₀d₂ + a₂d₀d₁`
  with `acc` = role `32`, `acc_after` = role `60`, `dⱼ` = the inactive-safe denominator witnesses
  (roles `33..35`) and `aⱼ` the selector-derived activity masks;
* the chain `accAfterChain` — off the last row `acc_after(i) = acc(i+1)`;
* the anchors `isFirst · acc = 0` and `isLast · (acc_after − requests) = 0`,
  `requests` being the compute `𝕂` public role `2`.

This module reads those gates back at the `𝕂` level of the gathered row environment and
**telescopes** them: whenever every committed safe denominator is nonzero — the pole-hit
exclusion, which is the priced event and is taken here as a hypothesis in exactly that form —
the sum over all rows of `Σⱼ aⱼ/dⱼ` equals the public `requests`
(`hostile_requests_eq_sum_rowTerms`).  Nothing here is about the honest trace: the environments
are read off an arbitrary accepted `Qc` through `productionNamedComputeRAP_satisfies_iff_sourceLanguage`.

Section D goes one step further through the three denominator pins (`correctedFinalExtGate 76..78`):
the committed safe denominator IS `aⱼ · (pole + RLC^γ(recordⱼ)) + (1 − aⱼ)` with the record read off
the row's own columns (`slotDenominator`), so under boolean masks the sum is the paper-form
`Σᵢ Σⱼ aⱼ(i)/(pole + RLC^γ(recordⱼ(i)))` (`hostile_requests_eq_sum_logUp`).

`hostile_requests_eq_sum_logUp_of_pole` is the assembled compute-side statement.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeHostileAccumulator

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
open StrictExtension
open OptimizedStrictFullPackage
open OptimizedComputeFinalTrace
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## A. The anchors and the step, read at the `𝕂` level of an arbitrary typed environment -/


/-! ### The denominator pins: what the committed safe denominator IS -/

/-! ### The record the row decodes to, and the coins it is compressed with -/

/-! `rowRecord` (the eight-scalar record of request slot `j`) now lives upstream in
`HostileRecordLists.lean`, under this namespace. -/

/-! ## B. At the consumed chip: what every accepted trace commits, row by row -/

section Deployed

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

variable (Qc : Fin P.computeChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
include hsat

theorem row_obligations (i : Fin (rows P)) :
    CorrectedComputeSourceObligations (rows P) (rowEnv P Qc i)
      (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
        P.optimized.computeChallenge P.optimized.computePublic) := by
  have h := (productionNamedComputeRAP_satisfies_iff_sourceLanguage
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes P.optimized.basis
    P.optimized.computeChallenge P.optimized.computePublic P.optimized.orbit Qc).1 hsat
  exact h.2 _ (by simp [rowNodeSet])

/-- Base slots `11`/`12` are the fixed first/last-row masks, by the preprocessing binding. -/
theorem masks_at_row (i : Fin (rows P)) :
    (rowEnv P Qc i).baseTrace 11 = (if (i : ℕ) = 0 then 1 else 0) ∧
      (rowEnv P Qc i).baseTrace 12 = (if i = lastRow P then 1 else 0) := by
  have hbind := ((productionNamedComputeRAP_satisfies_iff_sourceLanguage
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes P.optimized.basis
    P.optimized.computeChallenge P.optimized.computePublic P.optimized.orbit Qc).1 hsat).1
  have hinj := P.optimized.computeNodes_injective
  have h0 := hbind ⟨0, by change 0 < 2; norm_num⟩
  have h1 := hbind ⟨1, by change 1 < 2; norm_num⟩
  have h11 : 11 < P.computeChip.rap.w := by change 11 < 303; norm_num
  have h12 : 12 < P.computeChip.rap.w := by change 12 < 303; norm_num
  have hc0 : (ProductionNamedComputeRAP P.optimized.family.problem.cfg.compRows_pos
      P.optimized.computeNodes P.optimized.basis P.optimized.computeChallenge
      P.optimized.computePublic P.optimized.orbit).preprocessingColumn
        ⟨0, by change 0 < 2; norm_num⟩ = ⟨11, h11⟩ := rfl
  have hc1 : (ProductionNamedComputeRAP P.optimized.family.problem.cfg.compRows_pos
      P.optimized.computeNodes P.optimized.basis P.optimized.computeChallenge
      P.optimized.computePublic P.optimized.orbit).preprocessingColumn
        ⟨1, by change 1 < 2; norm_num⟩ = ⟨12, h12⟩ := rfl
  rw [hc0] at h0
  rw [hc1] at h1
  constructor
  · show (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
      P.optimized.computeChallenge P.optimized.computePublic).trace 11 = _
    simp only [envOfTrace, dif_pos h11]
    rw [show (Qc ⟨11, h11⟩) = Nock.Framework.firstRowMask P.optimized.computeNodes from h0,
      Nock.Framework.firstRowMask_eval _ hinj]
  · show (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
      P.optimized.computeChallenge P.optimized.computePublic).trace 12 = _
    simp only [envOfTrace, dif_pos h12]
    rw [show (Qc ⟨12, h12⟩) = Nock.Framework.lastRowMask
      P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes from h1,
      Nock.Framework.lastRowMask_eval _ _ hinj]

/-- `isFirst · acc = 0` at the first row: the accumulator starts at `0`. -/
theorem acc_first : (rowEnv P Qc (firstRow P)).extTrace 32 = 0 := by
  have hgate := (row_obligations P Qc hsat (firstRow P)).endpointDegreeTwo2 _
    anchors_mem_endpoint2.1
  rw [accInit_eval, (masks_at_row P Qc hsat (firstRow P)).1] at hgate
  simpa using hgate

/-- `isLast · (acc_after − requests) = 0` at the last row. -/
theorem accAfter_last : (rowEnv P Qc (lastRow P)).extTrace 60 =
    (rowEnv P Qc (lastRow P)).extensionPublic 2 := by
  have hgate := (row_obligations P Qc hsat (lastRow P)).endpointDegreeTwo2 _
    anchors_mem_endpoint2.2
  rw [accTerminal_eval, (masks_at_row P Qc hsat (lastRow P)).2, if_pos rfl] at hgate
  simpa [sub_eq_zero] using hgate

/-- The step gate at every row. -/
theorem step_at (i : Fin (rows P)) : correctedAccAfterStep.eval (rowEnv P Qc i) = 0 := by
  have h := (row_obligations P Qc hsat i).residualAux3 2
  simpa [correctedAuxSemanticValue] using h

/-- The chain gate off the last row. -/
theorem chain_at (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnv P Qc i).extTrace 60 = (rowEnv P Qc i).extTraceNext 32 := by
  have h := (row_obligations P Qc hsat i).extensionCore21 packedChainId
  have hnl : (rowEnv P Qc i).baseTrace 12 = 0 := by
    rw [(masks_at_row P Qc hsat i).2, if_neg]
    intro heq
    have hv : (i : ℕ) = rows P - 1 := congrArg Fin.val heq
    omega
  simp only [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, packedChainId,
    ↓reduceIte] at h
  simpa [accAfterChain, CorrectedFinalTypedExpr.eval, hnl, sub_eq_zero] using h

omit hsat in
/-- Orbit alignment: the next-row read of role `32` at row `i` is role `32` at row `i+1`. -/
theorem next_acc (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnv P Qc i).extTraceNext 32 = (rowEnv P Qc ⟨(i : ℕ) + 1, hi⟩).extTrace 32 := by
  have hadj := P.optimized.computeAdjacentOrbit i hi
  simp only [rowEnv, gatherCorrectedFinalTypedEnv]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hlt : correctedFinalExtCoordIndex (e := 3) (32 : Fin 63) k < P.computeChip.rap.w := by
    change _ < 303; simp [correctedFinalExtCoordIndex]; omega
  simp only [envOfTrace, dif_pos hlt]
  rw [hadj]

omit hsat in
/-- The public `requests` gathered at any row is the package's `computePublic` block `6..8`. -/
theorem gathered_requests (i : Fin (rows P)) :
    (rowEnv P Qc i).extensionPublic 2 =
      ∑ k : Fin 3, P.optimized.computePublic (6 + (k : ℕ)) • P.optimized.basis k := by
  simp only [rowEnv, gatherCorrectedFinalTypedEnv, envOfTrace]
  rfl

/-! ## C. Telescoping -/

/-- The sum of the first `m` row terms. -/
def prefixSum (m : ℕ) : K :=
  ∑ k ∈ Finset.range m, if h : k < rows P then rowTerm (rowEnv P Qc ⟨k, h⟩) else 0

omit hsat in
theorem prefixSum_succ (m : ℕ) (hm : m < rows P) :
    prefixSum P Qc (m + 1) = prefixSum P Qc m + rowTerm (rowEnv P Qc ⟨m, hm⟩) := by
  simp [prefixSum, Finset.sum_range_succ, hm]

/-- **The accumulator at row `m` is the sum of the row terms before it**, for any accepted trace
whose committed safe denominators are all nonzero. -/
theorem acc_eq_prefixSum
    (hden : ∀ (i : Fin (rows P)) (j : Fin 3), safeDenomWitness (rowEnv P Qc i) j ≠ 0) :
    ∀ (m : ℕ) (hm : m < rows P), (rowEnv P Qc ⟨m, hm⟩).extTrace 32 = prefixSum P Qc m := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [prefixSum, Finset.range_zero, Finset.sum_empty]
      exact acc_first P Qc hsat
  | succ m ih =>
      intro hm
      have hm' : m < rows P := by omega
      rw [← next_acc P Qc ⟨m, hm'⟩ hm, ← chain_at P Qc hsat ⟨m, hm'⟩ hm,
        accAfter_eq_of_step _ (step_at P Qc hsat ⟨m, hm'⟩) (hden _), ih hm',
        prefixSum_succ P Qc m hm']

/-- **Hostile telescoping at the consumed chip.**  For any trace `P.computeChip` accepts whose
committed safe denominators are nonzero at every row and slot, the public `requests` is the
sum over all rows of the committed log-derivative row terms `Σⱼ aⱼ · dⱼ⁻¹` — the paper's
`requests = acc_prog(h₁)` with `acc_prog` unfolded through `:526-527`,
proved from the committed gates alone. -/
theorem hostile_requests_eq_sum_rowTerms
    (hden : ∀ (i : Fin (rows P)) (j : Fin 3), safeDenomWitness (rowEnv P Qc i) j ≠ 0) :
    (rowEnv P Qc (lastRow P)).extensionPublic 2 = ∑ i : Fin (rows P), rowTerm (rowEnv P Qc i) := by
  have hpos := P.optimized.family.problem.cfg.compRows_pos
  have hlast : (rowEnv P Qc (lastRow P)).extTrace 32 = prefixSum P Qc (rows P - 1) :=
    acc_eq_prefixSum P Qc hsat hden (rows P - 1) _
  have hstep := accAfter_eq_of_step _ (step_at P Qc hsat (lastRow P)) (hden _)
  rw [← accAfter_last P Qc hsat, hstep, hlast, ← prefixSum_succ P Qc (rows P - 1) _,
    Nat.sub_add_cancel hpos]
  simp only [prefixSum]
  rw [← Fin.sum_univ_eq_sum_range (fun k => if h : k < rows P then
    rowTerm (rowEnv P Qc ⟨k, h⟩) else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [i.isLt]

/-! ## D. Through the denominator pins: the row terms in LogUp form -/

/-- The three denominator pins hold at every row of an accepted trace. -/
theorem denomPin_at (i : Fin (rows P)) (j : Fin 3) :
    safeDenomWitness (rowEnv P Qc i) j =
      SafeDenom (activeMask (rowEnv P Qc i) j) (slotDenominator (rowEnv P Qc i) j) := by
  have h := (row_obligations P Qc hsat i).extensionCore21 ⟨78 + (j : ℕ), by have := j.isLt; omega⟩
  have hne : ∀ q : CorrectedCoreExtGateId, q = ⟨78 + (j : ℕ), by have := j.isLt; omega⟩ →
      q ≠ packedWalkCountId ∧ q ≠ packedWalkAccId ∧ q ≠ packedChainId ∧
        ¬ (q = packedLnChainId ∨ q = packedWalkLnId) := by
    rintro q rfl
    fin_cases j <;> decide
  obtain ⟨h10, h11, h20, h89⟩ := hne _ rfl
  simp only [correctedCoreSemanticValue, h10, h11, h20, h89, ↓reduceIte] at h
  exact (denomPin_eval_iff _ j).1 h

/-- With boolean activity masks the committed row term is the paper-form one — inactive slots
contribute `0` whatever the (possibly zero) raw denominator, active slots `1/denominator`. -/
theorem rowTerm_eq_logUp (i : Fin (rows P))
    (hbool : ∀ j : Fin 3, activeMask (rowEnv P Qc i) j = 0 ∨ activeMask (rowEnv P Qc i) j = 1) :
    rowTerm (rowEnv P Qc i) = logUpRowTerm (rowEnv P Qc i) := by
  simp only [rowTerm, logUpRowTerm, denomPin_at P Qc hsat i,
    active_mul_safeDenom_inv _ _ (hbool 0), active_mul_safeDenom_inv _ _ (hbool 1),
    active_mul_safeDenom_inv _ _ (hbool 2)]

/-- **Hostile telescoping in LogUp form.**  For any accepted trace whose activity masks are
boolean at every row and whose **active** slot denominators are nonzero (the pole-hit exclusion,
the paper's `RLC^α(IO) − β ≠ 0` for the emitted records), the public `requests` is
`Σᵢ Σⱼ aⱼ(i) / (pole + RLC^γ(recordⱼ(i)))` — the request side of the paper's log-derivative
multiset argument, read off the committed columns alone. -/
theorem hostile_requests_eq_sum_logUp
    (hbool : ∀ (i : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnv P Qc i) j = 0 ∨ activeMask (rowEnv P Qc i) j = 1)
    (hpole : ∀ (i : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnv P Qc i) j = 1 → slotDenominator (rowEnv P Qc i) j ≠ 0) :
    (rowEnv P Qc (lastRow P)).extensionPublic 2 =
      ∑ i : Fin (rows P), logUpRowTerm (rowEnv P Qc i) := by
  have hden : ∀ (i : Fin (rows P)) (j : Fin 3), safeDenomWitness (rowEnv P Qc i) j ≠ 0 := by
    intro i j
    rw [denomPin_at P Qc hsat i j]
    exact safeDenom_ne_zero _ _ (hbool i j) (hpole i j)
  rw [hostile_requests_eq_sum_rowTerms P Qc hsat hden]
  exact Finset.sum_congr rfl fun i _ => rowTerm_eq_logUp P Qc hsat i (hbool i)

/-! ## E. Boolean masks from the committed base gates (needs the characteristic) -/

/-- The eleven selector booleanities and the one-hot gate hold at every row of an accepted trace,
read in `𝔽`. -/
theorem selector_gates_at (i : Fin (rows P)) :
    (∀ (k : ℕ) (hk : k < 11),
      (rowEnv P Qc i).baseTrace ⟨k, by omega⟩ = 0 ∨ (rowEnv P Qc i).baseTrace ⟨k, by omega⟩ = 1) ∧
    ((rowEnv P Qc i).baseTrace ⟨0, by norm_num⟩ + (rowEnv P Qc i).baseTrace ⟨1, by norm_num⟩ + (rowEnv P Qc i).baseTrace ⟨2, by norm_num⟩ + (rowEnv P Qc i).baseTrace ⟨3, by norm_num⟩ + (rowEnv P Qc i).baseTrace ⟨4, by norm_num⟩ + (rowEnv P Qc i).baseTrace ⟨5, by norm_num⟩ + (rowEnv P Qc i).baseTrace ⟨6, by norm_num⟩ + (rowEnv P Qc i).baseTrace ⟨7, by norm_num⟩ + (rowEnv P Qc i).baseTrace ⟨8, by norm_num⟩ + (rowEnv P Qc i).baseTrace ⟨9, by norm_num⟩ + (rowEnv P Qc i).baseTrace ⟨10, by norm_num⟩) = 1 := by
  have hb := (row_obligations P Qc hsat i).base15
  set envF := envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
    P.optimized.computeChallenge P.optimized.computePublic with hE
  have hbase : ∀ k : ℕ, (hk : k < 13) → (rowEnv P Qc i).baseTrace ⟨k, hk⟩ = envF.trace k :=
    fun _ _ => rfl
  constructor
  · intro k hk
    have hg := hb (selectorBool k) (by
      simp only [finalBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl ⟨k, hk, rfl⟩)
    rw [hbase k (by omega)]
    simp only [selectorBool, bv, CoeffExpr.eval, mul_eq_zero, sub_eq_zero] at hg
    rcases hg with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  · have hg := hb selectorOneHot (by simp [finalBaseTransitionGates])
    simp [selectorOneHot, selectorSum, CoeffExpr.sumList, List.range_succ, bv, CoeffExpr.eval,
      sub_eq_zero] at hg
    change envF.trace 0 + envF.trace 1 + envF.trace 2 + envF.trace 3 + envF.trace 4 +
      envF.trace 5 + envF.trace 6 + envF.trace 7 + envF.trace 8 + envF.trace 9 +
      envF.trace 10 = 1
    linear_combination hg

/-- **Hostile one-hotness.** -/
theorem rowSelector_oneHot (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (i : Fin (rows P)) :
    ∃ s, rowSelector (rowEnv P Qc i) = Nock.ComputeTable.opSel s := by
  obtain ⟨hbool, hsum⟩ := selector_gates_at P Qc hsat i
  apply Nock.ComputeTable.oneHot_of_bool_sum _ hchar
  · intro st
    rcases hbool (Nock.Reified.opCol st) (by cases st <;> decide) with h | h
    · left; simp [rowSelector, h]
    · right; simp [rowSelector, h]
  · have hK := congrArg (algebraMap F K) hsum
    simp only [map_add, map_one] at hK
    simp only [rowSelector, Nock.ComputeTable.sum09, Nock.Reified.opCol]
    linear_combination hK

/-- **Boolean activity masks**, derived from the committed base gates at every accepted row. -/
theorem activeMask_bool (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (i : Fin (rows P)) (j : Fin 3) :
    activeMask (rowEnv P Qc i) j = 0 ∨ activeMask (rowEnv P Qc i) j = 1 := by
  obtain ⟨s, hs⟩ := rowSelector_oneHot P Qc hsat hchar i
  have hv : ∀ st, algebraMap F K ((rowEnv P Qc i).baseTrace
      ⟨Nock.Reified.opCol st, by cases st <;> decide⟩) = Nock.ComputeTable.opSel s st :=
    fun st => congrFun hs st
  have h0 := hv .s0; have h2 := hv .s2; have h5 := hv .s5; have h6 := hv .s6
  have h7 := hv .s7; have h8 := hv .s8; have h9 := hv .s9
  simp only [Nock.Reified.opCol] at h0 h2 h5 h6 h7 h8 h9
  fin_cases j
  · right
    simp [activeMask, sampledActive, Expr.eval]
  · simp only [activeMask, sampledActive, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
      Fin.isValue, Fin.val_one]
    simp only [show (0 : ℕ) < 13 by norm_num, show (2 : ℕ) < 13 by norm_num,
      show (5 : ℕ) < 13 by norm_num, show (6 : ℕ) < 13 by norm_num,
      show (7 : ℕ) < 13 by norm_num, show (8 : ℕ) < 13 by norm_num,
      show (9 : ℕ) < 13 by norm_num, dite_true]
    rw [h0, h2, h5, h6, h7, h8, h9]
    cases s <;> simp [Nock.ComputeTable.opSel]
  · simp only [activeMask, sampledActive, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
      Fin.isValue, Fin.val_two]
    simp only [show (6 : ℕ) < 13 by norm_num, show (9 : ℕ) < 13 by norm_num, dite_true]
    rw [h6, h9]
    cases s <;> simp [Nock.ComputeTable.opSel]

/-! ## F. The request list read off the trace -/

/-! `rowRequests` (the records a row emits, hostilely) now lives upstream in
`HostileRecordLists.lean`, under this namespace. -/

omit hsat in
/-- With boolean masks the paper-form row term is the sum of reciprocals over the row's emitted
records. -/
theorem logUpRowTerm_eq_rowRequests (i : Fin (rows P))
    (hbool : ∀ j : Fin 3, activeMask (rowEnv P Qc i) j = 0 ∨ activeMask (rowEnv P Qc i) j = 1) :
    logUpRowTerm (rowEnv P Qc i) =
      ((rowRequests (rowEnv P Qc i)).map
        fun r => (FiniteIO.compress (rowCoins (rowEnv P Qc i)) r)⁻¹).sum := by
  have hterm : ∀ j : Fin 3, activeMask (rowEnv P Qc i) j * (slotDenominator (rowEnv P Qc i) j)⁻¹ =
      if activeMask (rowEnv P Qc i) j = 1
        then (FiniteIO.compress (rowCoins (rowEnv P Qc i)) (rowRecord (rowEnv P Qc i) j))⁻¹
        else 0 := by
    intro j
    rw [← slotDenominator_eq_compress]
    rcases hbool j with h | h <;> simp [h]
  simp only [logUpRowTerm, hterm 0, hterm 1, hterm 2, rowRequests, List.finRange,
    List.ofFn_succ, List.ofFn_zero, List.filterMap_cons, List.filterMap_nil,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  split_ifs <;> simp [add_assoc]

omit hsat in
/-- The coins are the same at every row (they are challenges, not columns). -/
theorem rowCoins_const (i : Fin (rows P)) :
    rowCoins (rowEnv P Qc i) =
      ⟨∑ k : Fin 3, P.optimized.computeChallenge (3 * 7 + (k : ℕ)) • P.optimized.basis k,
        ∑ k : Fin 3, P.optimized.computeChallenge (3 * 8 + (k : ℕ)) • P.optimized.basis k⟩ := by
  simp only [rowCoins, CorrectedFinalTypedEnv.toSourceEnv, rowEnv, gatherCorrectedFinalTypedEnv,
    envOfTrace]
  rfl

/-- The coins the chip reads. -/
def chipCoins : FiniteIO.IOCoins K :=
  ⟨∑ k : Fin 3, P.optimized.computeChallenge (3 * 7 + (k : ℕ)) • P.optimized.basis k,
    ∑ k : Fin 3, P.optimized.computeChallenge (3 * 8 + (k : ℕ)) • P.optimized.basis k⟩

/-- For any accepted trace, under `hchar`
and the pole-hit exclusion on the emitted records, the public `requests` is the sum of the
reciprocals of the compressed records read off the trace — the request side of `finiteIO_sound`'s
sampled-pole identity, at the records the chip commits to. -/
theorem hostile_requests_eq_sum_over_records
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hpole : ∀ (i : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnv P Qc i) j = 1 → slotDenominator (rowEnv P Qc i) j ≠ 0) :
    (rowEnv P Qc (lastRow P)).extensionPublic 2 =
      ((hostileRequests P Qc).map fun r => (FiniteIO.compress (chipCoins P) r)⁻¹).sum := by
  rw [hostile_requests_eq_sum_logUp P Qc hsat (fun i j => activeMask_bool P Qc hsat hchar i j)
    hpole, hostileRequests, List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn,
    List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [logUpRowTerm_eq_rowRequests P Qc i (fun j => activeMask_bool P Qc hsat hchar i j),
    rowCoins_const]
  rfl

/-- For any trace `P.computeChip` accepts, under
the characteristic hypothesis and the pole-hit exclusion on the **active** slots only, the public
`requests` is the LogUp sum of the records read off the trace's own rows. -/
theorem hostile_requests_eq_sum_logUp_of_pole
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hpole : ∀ (i : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnv P Qc i) j = 1 → slotDenominator (rowEnv P Qc i) j ≠ 0) :
    (rowEnv P Qc (lastRow P)).extensionPublic 2 =
      ∑ i : Fin (rows P), logUpRowTerm (rowEnv P Qc i) :=
  hostile_requests_eq_sum_logUp P Qc hsat (fun i j => activeMask_bool P Qc hsat hchar i j) hpole

/-- The same statement with `requests` read as the package's public block. -/
theorem hostile_requests_public_eq_sum_rowTerms
    (hden : ∀ (i : Fin (rows P)) (j : Fin 3), safeDenomWitness (rowEnv P Qc i) j ≠ 0) :
    (∑ k : Fin 3, P.optimized.computePublic (6 + (k : ℕ)) • P.optimized.basis k) =
      ∑ i : Fin (rows P), rowTerm (rowEnv P Qc i) := by
  rw [← gathered_requests P Qc (lastRow P)]
  exact hostile_requests_eq_sum_rowTerms P Qc hsat hden

end Deployed

end
end OptimizedComputeHostileAccumulator
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.correctedAccAfterStep_eval_iff
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.accAfter_eq_of_step
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.acc_eq_prefixSum
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.hostile_requests_eq_sum_rowTerms
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.hostile_requests_public_eq_sum_rowTerms
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.denomPin_eval_iff
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.denomPin_at
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.hostile_requests_eq_sum_logUp
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.rowSelector_oneHot
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.activeMask_bool
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.hostile_requests_eq_sum_logUp_of_pole
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.slotDenominator_eq_compress
#print axioms Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.hostile_requests_eq_sum_over_records
