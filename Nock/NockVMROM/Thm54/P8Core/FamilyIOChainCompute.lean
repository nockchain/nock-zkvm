/-
  Nock/NockVMROM/Thm54/P8Core/FamilyIOChainCompute.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.FamilyIOChainCompute`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/FamilyIOChainCompute.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.FamilyComputeRows
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.FamilyIOChainCompute
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
open OptimizedStrictPackage
open OptimizedStrictFullPackage
open OptimizedComputeBaseGates
open OptimizedComputeFinal
open OptimizedComputeCorrectedFinal
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeSemanticRealization
open OptimizedComputeFiniteIOGates
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open DeployedChipFamily
open FamilyComputeRows
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

/-- The family compute chip's width is the deployed `303` (as `computeChipAt_width`'s first half). -/
theorem computeChipAt_w : (P.computeChipAt c).rap.w = 303 := by
  simp only [OptimizedFullStrictNockVMROMPackage.computeChipAt,
    DeployedChipFamily.computeChipAt, ProductionNamedComputeRAP]
  exact (corrected_rap_fingerprint P.optimized.basis
    (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)
    P.optimized.orbit (rowNodeSet P.optimized.computeNodes)).1

/-- The coins the family chip's request side reads (slots `7`/`8`): the tuple's IO coins. -/
abbrev chipCoinsAt : FiniteIO.IOCoins K := ⟨c.2.1.1, c.2.1.2⟩

variable (Qc : Fin (P.computeChipAt c).rap.w → F[X])

theorem alphaAt_rowEnvAt (i : Fin (rows P)) : alphaAt (rowEnvAt P c Qc i) = chipAlphaAt c := by
  unfold alphaAt
  exact rowEnvAt_chal P c Qc i ⟨0, by decide⟩

theorem rowCoins_rowEnvAt (i : Fin (rows P)) : rowCoins (rowEnvAt P c Qc i) = chipCoinsAt c := by
  have h7 := rowEnvAt_chal P c Qc i ⟨7, by decide⟩
  have h8 := rowEnvAt_chal P c Qc i ⟨8, by decide⟩
  simp only [rowCoins]
  rw [h7, h8]
  rfl

/-- The public `requests` gathered at any family row is the package's `computePublic` block
`6..8` (the family public map is the package map off the walk block `0..5`). -/
theorem gathered_requests_at (i : Fin (rows P)) :
    (rowEnvAt P c Qc i).extensionPublic 2 =
      ∑ k : Fin 3, P.optimized.computePublic (6 + (k : ℕ)) • P.optimized.basis k := by
  simp only [rowEnvAt, gatherCorrectedFinalTypedEnv, envOfTrace]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [OptimizedFullStrictNockVMROMPackage.familyComputePublic,
    computePublicOfTuple_eq_pkg_off_seed _ _ _ _ _ (by omega)]
  congr 1

section Rows

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

/-- Twin of `masks_at_row`: base slots `11`/`12` are the fixed first/last-row masks. -/
theorem masks_at_row_at (i : Fin (rows P)) :
    (rowEnvAt P c Qc i).baseTrace 11 = (if (i : ℕ) = 0 then 1 else 0) ∧
      (rowEnvAt P c Qc i).baseTrace 12 = (if i = lastRow P then 1 else 0) := by
  have hbind := ((productionNamedComputeRAP_satisfies_iff_sourceLanguage
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes P.optimized.basis
    (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)
    P.optimized.orbit Qc).1 hsat).1
  have hinj := P.optimized.computeNodes_injective
  have h0 := hbind ⟨0, by change 0 < 2; norm_num⟩
  have h1 := hbind ⟨1, by change 1 < 2; norm_num⟩
  have h11 : 11 < (P.computeChipAt c).rap.w := by rw [computeChipAt_w]; norm_num
  have h12 : 12 < (P.computeChipAt c).rap.w := by rw [computeChipAt_w]; norm_num
  have hc0 : (ProductionNamedComputeRAP P.optimized.family.problem.cfg.compRows_pos
      P.optimized.computeNodes P.optimized.basis (computeChalValOfTuple P.optimized.basis c)
      (P.familyComputePublic c) P.optimized.orbit).preprocessingColumn
        ⟨0, by change 0 < 2; norm_num⟩ = ⟨11, h11⟩ := rfl
  have hc1 : (ProductionNamedComputeRAP P.optimized.family.problem.cfg.compRows_pos
      P.optimized.computeNodes P.optimized.basis (computeChalValOfTuple P.optimized.basis c)
      (P.familyComputePublic c) P.optimized.orbit).preprocessingColumn
        ⟨1, by change 1 < 2; norm_num⟩ = ⟨12, h12⟩ := rfl
  rw [hc0] at h0
  rw [hc1] at h1
  constructor
  · show (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
      (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).trace 11 = _
    simp only [envOfTrace, dif_pos h11]
    rw [show (Qc ⟨11, h11⟩) = Nock.Framework.firstRowMask P.optimized.computeNodes from h0,
      Nock.Framework.firstRowMask_eval _ hinj]
  · show (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
      (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).trace 12 = _
    simp only [envOfTrace, dif_pos h12]
    rw [show (Qc ⟨12, h12⟩) = Nock.Framework.lastRowMask
      P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes from h1,
      Nock.Framework.lastRowMask_eval _ _ hinj]

/-- Twin of `acc_first`. -/
theorem acc_first_at : (rowEnvAt P c Qc (firstRow P)).extTrace 32 = 0 := by
  have hgate := (row_obligations_at P c Qc hsat (firstRow P)).endpointDegreeTwo2 _
    anchors_mem_endpoint2.1
  rw [accInit_eval, (masks_at_row_at P c Qc hsat (firstRow P)).1] at hgate
  simpa using hgate

/-- Twin of `accAfter_last`. -/
theorem accAfter_last_at : (rowEnvAt P c Qc (lastRow P)).extTrace 60 =
    (rowEnvAt P c Qc (lastRow P)).extensionPublic 2 := by
  have hgate := (row_obligations_at P c Qc hsat (lastRow P)).endpointDegreeTwo2 _
    anchors_mem_endpoint2.2
  rw [accTerminal_eval, (masks_at_row_at P c Qc hsat (lastRow P)).2, if_pos rfl] at hgate
  simpa [sub_eq_zero] using hgate

/-- Twin of `step_at`. -/
theorem step_at_at (i : Fin (rows P)) : correctedAccAfterStep.eval (rowEnvAt P c Qc i) = 0 := by
  have h := (row_obligations_at P c Qc hsat i).residualAux3 2
  simpa [correctedAuxSemanticValue] using h

/-- Twin of `chain_at`. -/
theorem chain_at_at (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnvAt P c Qc i).extTrace 60 = (rowEnvAt P c Qc i).extTraceNext 32 := by
  have h := (row_obligations_at P c Qc hsat i).extensionCore21 packedChainId
  have hnl : (rowEnvAt P c Qc i).baseTrace 12 = 0 := by
    rw [(masks_at_row_at P c Qc hsat i).2, if_neg]
    intro heq
    have hv : (i : ℕ) = rows P - 1 := congrArg Fin.val heq
    omega
  simp only [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, packedChainId,
    ↓reduceIte] at h
  simpa [accAfterChain, CorrectedFinalTypedExpr.eval, hnl, sub_eq_zero] using h

omit hsat in
/-- Twin of `next_acc` (orbit alignment of role `32`). -/
theorem next_acc_at (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnvAt P c Qc i).extTraceNext 32 = (rowEnvAt P c Qc ⟨(i : ℕ) + 1, hi⟩).extTrace 32 := by
  have hadj := P.optimized.computeAdjacentOrbit i hi
  simp only [rowEnvAt, gatherCorrectedFinalTypedEnv]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hlt : correctedFinalExtCoordIndex (e := 3) (32 : Fin 63) k < (P.computeChipAt c).rap.w := by
    rw [computeChipAt_w]; simp [correctedFinalExtCoordIndex]; omega
  simp only [envOfTrace, dif_pos hlt]
  rw [hadj]

omit hsat in
/-- Twin of `prefixSum`. -/
def prefixSumAt (m : ℕ) : K :=
  ∑ k ∈ Finset.range m, if h : k < rows P then rowTerm (rowEnvAt P c Qc ⟨k, h⟩) else 0

omit hsat in
theorem prefixSumAt_succ (m : ℕ) (hm : m < rows P) :
    prefixSumAt P c Qc (m + 1) = prefixSumAt P c Qc m + rowTerm (rowEnvAt P c Qc ⟨m, hm⟩) := by
  simp [prefixSumAt, Finset.sum_range_succ, hm]

/-- Twin of `acc_eq_prefixSum`. -/
theorem acc_eq_prefixSum_at
    (hden : ∀ (i : Fin (rows P)) (j : Fin 3), safeDenomWitness (rowEnvAt P c Qc i) j ≠ 0) :
    ∀ (m : ℕ) (hm : m < rows P), (rowEnvAt P c Qc ⟨m, hm⟩).extTrace 32 = prefixSumAt P c Qc m := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [prefixSumAt, Finset.range_zero, Finset.sum_empty]
      exact acc_first_at P c Qc hsat
  | succ m ih =>
      intro hm
      have hm' : m < rows P := by omega
      rw [← next_acc_at P c Qc ⟨m, hm'⟩ hm, ← chain_at_at P c Qc hsat ⟨m, hm'⟩ hm,
        accAfter_eq_of_step _ (step_at_at P c Qc hsat ⟨m, hm'⟩) (hden _), ih hm',
        prefixSumAt_succ P c Qc m hm']

/-- Twin of `hostile_requests_eq_sum_rowTerms`. -/
theorem hostile_requests_eq_sum_rowTerms_at
    (hden : ∀ (i : Fin (rows P)) (j : Fin 3), safeDenomWitness (rowEnvAt P c Qc i) j ≠ 0) :
    (rowEnvAt P c Qc (lastRow P)).extensionPublic 2 =
      ∑ i : Fin (rows P), rowTerm (rowEnvAt P c Qc i) := by
  have hpos := P.optimized.family.problem.cfg.compRows_pos
  have hlast : (rowEnvAt P c Qc (lastRow P)).extTrace 32 = prefixSumAt P c Qc (rows P - 1) :=
    acc_eq_prefixSum_at P c Qc hsat hden (rows P - 1) _
  have hstep := accAfter_eq_of_step _ (step_at_at P c Qc hsat (lastRow P)) (hden _)
  rw [← accAfter_last_at P c Qc hsat, hstep, hlast, ← prefixSumAt_succ P c Qc (rows P - 1) _,
    Nat.sub_add_cancel hpos]
  simp only [prefixSumAt]
  rw [← Fin.sum_univ_eq_sum_range (fun k => if h : k < rows P then
    rowTerm (rowEnvAt P c Qc ⟨k, h⟩) else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [i.isLt]

/-- Twin of `denomPin_at`. -/
theorem denomPin_at_at (i : Fin (rows P)) (j : Fin 3) :
    safeDenomWitness (rowEnvAt P c Qc i) j =
      SafeDenom (activeMask (rowEnvAt P c Qc i) j) (slotDenominator (rowEnvAt P c Qc i) j) := by
  have h := (row_obligations_at P c Qc hsat i).extensionCore21
    ⟨78 + (j : ℕ), by have := j.isLt; omega⟩
  have hne : ∀ q : CorrectedCoreExtGateId, q = ⟨78 + (j : ℕ), by have := j.isLt; omega⟩ →
      q ≠ packedWalkCountId ∧ q ≠ packedWalkAccId ∧ q ≠ packedChainId ∧
        ¬ (q = packedLnChainId ∨ q = packedWalkLnId) := by
    rintro q rfl
    fin_cases j <;> decide
  obtain ⟨h10, h11, h20, h89⟩ := hne _ rfl
  simp only [correctedCoreSemanticValue, h10, h11, h20, h89, ↓reduceIte] at h
  exact (denomPin_eval_iff _ j).1 h

/-- Twin of `rowTerm_eq_logUp`. -/
theorem rowTerm_eq_logUp_at (i : Fin (rows P))
    (hbool : ∀ j : Fin 3,
      activeMask (rowEnvAt P c Qc i) j = 0 ∨ activeMask (rowEnvAt P c Qc i) j = 1) :
    rowTerm (rowEnvAt P c Qc i) = logUpRowTerm (rowEnvAt P c Qc i) := by
  simp only [rowTerm, logUpRowTerm, denomPin_at_at P c Qc hsat i,
    active_mul_safeDenom_inv _ _ (hbool 0), active_mul_safeDenom_inv _ _ (hbool 1),
    active_mul_safeDenom_inv _ _ (hbool 2)]

/-- Twin of `hostile_requests_eq_sum_logUp`. -/
theorem hostile_requests_eq_sum_logUp_at
    (hbool : ∀ (i : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnvAt P c Qc i) j = 0 ∨ activeMask (rowEnvAt P c Qc i) j = 1)
    (hpole : ∀ (i : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnvAt P c Qc i) j = 1 → slotDenominator (rowEnvAt P c Qc i) j ≠ 0) :
    (rowEnvAt P c Qc (lastRow P)).extensionPublic 2 =
      ∑ i : Fin (rows P), logUpRowTerm (rowEnvAt P c Qc i) := by
  have hden : ∀ (i : Fin (rows P)) (j : Fin 3), safeDenomWitness (rowEnvAt P c Qc i) j ≠ 0 := by
    intro i j
    rw [denomPin_at_at P c Qc hsat i j]
    exact safeDenom_ne_zero _ _ (hbool i j) (hpole i j)
  rw [hostile_requests_eq_sum_rowTerms_at P c Qc hsat hden]
  exact Finset.sum_congr rfl fun i _ => rowTerm_eq_logUp_at P c Qc hsat i (hbool i)

/-- Twin of `activeMask_bool`. -/
theorem activeMask_bool_at (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (i : Fin (rows P)) (j : Fin 3) :
    activeMask (rowEnvAt P c Qc i) j = 0 ∨ activeMask (rowEnvAt P c Qc i) j = 1 := by
  obtain ⟨s, hs⟩ := rowSelector_oneHot_at P c Qc hsat hchar i
  have hv : ∀ st, algebraMap F K ((rowEnvAt P c Qc i).baseTrace
      ⟨Nock.Reified.opCol st, by cases st <;> decide⟩) = Nock.ComputeTable.opSel s st :=
    fun st => congrFun hs st
  have h0 := hv .s0; have h2 := hv .s2; have h5 := hv .s5; have h6 := hv .s6
  have h7 := hv .s7; have h8 := hv .s8; have h9 := hv .s9
  simp only [Nock.Reified.opCol] at h0 h2 h5 h6 h7 h8 h9
  fin_cases j
  · right
    simp [activeMask, sampledActive, Expr.eval]
  · simp only [activeMask, sampledActive, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
      Fin.isValue]
    simp only [show (0 : ℕ) < 13 by norm_num, show (2 : ℕ) < 13 by norm_num,
      show (5 : ℕ) < 13 by norm_num, show (6 : ℕ) < 13 by norm_num,
      show (7 : ℕ) < 13 by norm_num, show (8 : ℕ) < 13 by norm_num,
      show (9 : ℕ) < 13 by norm_num, dite_true]
    rw [h0, h2, h5, h6, h7, h8, h9]
    cases s <;> simp [Nock.ComputeTable.opSel]
  · simp only [activeMask, sampledActive, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
      Fin.isValue]
    simp only [show (6 : ℕ) < 13 by norm_num, show (9 : ℕ) < 13 by norm_num, dite_true]
    rw [h6, h9]
    cases s <;> simp [Nock.ComputeTable.opSel]

end Rows

/-- Twin of `logUpRowTerm_eq_rowRequests`, with the row's coins read as the tuple's. -/
theorem logUpRowTerm_eq_rowRequests_at (i : Fin (rows P))
    (hbool : ∀ j : Fin 3,
      activeMask (rowEnvAt P c Qc i) j = 0 ∨ activeMask (rowEnvAt P c Qc i) j = 1) :
    logUpRowTerm (rowEnvAt P c Qc i) =
      ((rowRequests (rowEnvAt P c Qc i)).map
        fun r => (FiniteIO.compress (chipCoinsAt c) r)⁻¹).sum := by
  have hterm : ∀ j : Fin 3,
      activeMask (rowEnvAt P c Qc i) j * (slotDenominator (rowEnvAt P c Qc i) j)⁻¹ =
      if activeMask (rowEnvAt P c Qc i) j = 1
        then (FiniteIO.compress (chipCoinsAt c) (rowRecord (rowEnvAt P c Qc i) j))⁻¹
        else 0 := by
    intro j
    rw [slotDenominator_eq_compress, rowCoins_rowEnvAt]
    rcases hbool j with h | h <;> simp [h]
  simp only [logUpRowTerm, hterm 0, hterm 1, hterm 2, rowRequests, List.finRange,
    List.ofFn_succ, List.ofFn_zero, List.filterMap_cons, List.filterMap_nil,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  split_ifs <;> simp [add_assoc]

/-- **Twin of `hostileRequests`**: the request list a family trace commits to, every row's
active-slot records in row order. -/
def hostileRequestsAt : List (Fin 10 → K) :=
  (List.ofFn fun i : Fin (rows P) => rowRequests (rowEnvAt P c Qc i)).flatten

section Deployed

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

/-- Twin of `source_selector`. -/
theorem source_selector_at (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (i : Fin (rows P)) :
    ∃ s, ∀ st, (rowEnvAt P c Qc i).toSourceEnv.trace (opCol st) = ComputeTable.opSel s st := by
  obtain ⟨s, hs⟩ := rowSelector_oneHot_at P c Qc hsat hchar i
  refine ⟨s, fun st => ?_⟩
  rw [source_trace_base _ (opCol st) (by cases st <;> decide)]
  exact congrFun hs st

omit hsat in
/-- Twin of `rowArity_eq_arity`. -/
theorem rowArity_eq_arity_at (i : Fin (rows P)) (s : ComputeTable.State)
    (hsel : ∀ st, (rowEnvAt P c Qc i).toSourceEnv.trace (opCol st) = ComputeTable.opSel s st) :
    rowArity (rowEnvAt P c Qc i) = arity s := by
  have h0 := hsel .s0; have h2 := hsel .s2; have h5 := hsel .s5; have h6 := hsel .s6
  have h7 := hsel .s7; have h8 := hsel .s8; have h9 := hsel .s9
  simp only [opCol] at h0 h2 h5 h6 h7 h8 h9
  unfold rowArity
  simp only [activeMask, sampledActive, Expr.eval, Fin.isValue, Fin.val_one, Fin.val_two, h0, h2,
    h5, h6, h7, h8, h9]
  cases s <;> simp [ComputeTable.opSel, arity]

/-- Twin of `ln_recurrence_at`: `ln = ln_prev · (alphaM c.1)^{rowArity}`; the NPR-seed premise
is the family chip's own slot `1`, `nprSeed c.1 ≠ 0`. -/
theorem ln_recurrence_at_at (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : nprSeed c.1 ≠ 0) (i : Fin (rows P)) :
    lnCurAt (rowEnvAt P c Qc i) =
      lnPrevAt (rowEnvAt P c Qc i) * chipAlphaAt c ^ rowArity (rowEnvAt P c Qc i) := by
  obtain ⟨s, hsel⟩ := source_selector_at P c Qc hsat hchar i
  have h := ln_recurrence (row_obligations_at P c Qc hsat i) s hsel
    (zZinv_at_rowEnvAt P c Qc i hz0)
  rw [alphaAt_rowEnvAt] at h
  rw [rowArity_eq_arity_at P c Qc i s hsel]
  exact h

/-- Twin of `ln_chain_at`. -/
theorem ln_chain_at_at (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    lnCurAt (rowEnvAt P c Qc i) = lnPrevAt (rowEnvAt P c Qc ⟨(i : ℕ) + 1, hi⟩) := by
  have hnl : (rowEnvAt P c Qc i).baseTrace 12 = 0 := by
    rw [(masks_at_row_at P c Qc hsat i).2, if_neg]
    intro heq
    have hv : (i : ℕ) = rows P - 1 := congrArg Fin.val heq
    omega
  rw [ln_chain (row_obligations_at P c Qc hsat i) hnl]
  have hadj := P.optimized.computeAdjacentOrbit i hi
  unfold lnPrevAt
  simp only [rowEnvAt, gatherCorrectedFinalTypedEnv]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hlt : correctedFinalExtCoordIndex (e := 3) (54 : Fin 63) k < (P.computeChipAt c).rap.w := by
    rw [computeChipAt_w]; simp [correctedFinalExtCoordIndex]; omega
  simp only [envOfTrace, dif_pos hlt]
  rw [hadj]

omit hsat in
/-- Twin of `prefixExp`. -/
def prefixExpAt (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range m, if h : k < rows P then rowArity (rowEnvAt P c Qc ⟨k, h⟩) else 0

omit hsat in
theorem prefixExpAt_succ (m : ℕ) (hm : m < rows P) :
    prefixExpAt P c Qc (m + 1) = prefixExpAt P c Qc m + rowArity (rowEnvAt P c Qc ⟨m, hm⟩) := by
  simp [prefixExpAt, Finset.sum_range_succ, hm]

omit hsat in
theorem prefixExpAt_mono {a b : ℕ} (hab : a ≤ b) : prefixExpAt P c Qc a ≤ prefixExpAt P c Qc b := by
  unfold prefixExpAt
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) (fun _ _ _ => Nat.zero_le _)

omit hsat in
/-- Twin of `ln0`. -/
def ln0At : K := lnPrevAt (rowEnvAt P c Qc (firstRow P))

/-- **Twin of `hostile_ln0_eq_one`**: the committed origin gate `isFirst · (ln_prev − 1) = 0`
read at the family chip's first row. -/
theorem hostile_ln0_eq_one_at : ln0At P c Qc = 1 := by
  have hgate := (row_obligations_at P c Qc hsat (firstRow P)).endpointDegreeTwo2 _
    lnInit_mem_endpoint2
  rw [lnInit_eval, (masks_at_row_at P c Qc hsat (firstRow P)).1] at hgate
  simp only [firstRow, if_true, map_one, one_mul, sub_eq_zero] at hgate
  exact hgate

theorem hostile_ln0_ne_zero_at : ln0At P c Qc ≠ 0 := by
  rw [hostile_ln0_eq_one_at P c Qc hsat]; exact one_ne_zero

/-- Twin of `lnPrev_at`: `ln_prev(m) = ln₀ · (alphaM c.1)^{S(m)}`. -/
theorem lnPrev_at_at (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : nprSeed c.1 ≠ 0) :
    ∀ (m : ℕ) (hm : m < rows P),
      lnPrevAt (rowEnvAt P c Qc ⟨m, hm⟩) = ln0At P c Qc * chipAlphaAt c ^ prefixExpAt P c Qc m := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [prefixExpAt, Finset.range_zero, Finset.sum_empty, pow_zero, mul_one]
      rfl
  | succ m ih =>
      intro hm
      have hm' : m < rows P := by omega
      rw [← ln_chain_at_at P c Qc hsat ⟨m, hm'⟩ hm,
        ln_recurrence_at_at P c Qc hsat hchar hz0 ⟨m, hm'⟩, ih hm', prefixExpAt_succ P c Qc m hm',
        pow_add, mul_assoc]

omit hsat in
/-- Twin of `expOf`. -/
def expOfAt (i : Fin (rows P)) (j : Fin 3) : ℕ := prefixExpAt P c Qc i + (j : ℕ) + 1

/-- Twin of `rowRecord_ts_at`. -/
theorem rowRecord_ts_at_at (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : nprSeed c.1 ≠ 0)
    (i : Fin (rows P)) (j : Fin 3) (hact : activeMask (rowEnvAt P c Qc i) j = 1) :
    rowRecord (rowEnvAt P c Qc i) j 7 = ln0At P c Qc * chipAlphaAt c ^ expOfAt P c Qc i j := by
  rw [rowRecord_ts_active _ j hact, alphaAt_rowEnvAt, lnPrev_at_at P c Qc hsat hchar hz0 i i.isLt,
    expOfAt, mul_assoc, ← pow_add]
  rfl

/-- **Twin of `hostile_timestamp_eq`**: `ts(i, j) = ln₀ · (alphaM c.1)^{S(i) + j + 1}` at the family chip; the base is the coin by definition. -/
theorem hostile_timestamp_eq_at (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : nprSeed c.1 ≠ 0)
    (i : Fin (rows P)) (j : Fin 3) (hact : activeMask (rowEnvAt P c Qc i) j = 1) :
    rowRecord (rowEnvAt P c Qc i) j 7 =
      ln0At P c Qc * alphaM c.1 ^ (prefixExpAt P c Qc i + (j : ℕ) + 1) :=
  rowRecord_ts_at_at P c Qc hsat hchar hz0 i j hact

omit hsat in
/-- Twin of `totalRequests`. -/
def totalRequestsAt : ℕ := prefixExpAt P c Qc (rows P)

omit hsat in
theorem totalRequestsAt_le : totalRequestsAt P c Qc ≤ 3 * rows P := by
  unfold totalRequestsAt prefixExpAt
  calc (∑ k ∈ Finset.range (rows P),
        if h : k < rows P then rowArity (rowEnvAt P c Qc ⟨k, h⟩) else 0)
      ≤ ∑ _k ∈ Finset.range (rows P), 3 := by
        refine Finset.sum_le_sum fun k _ => ?_
        split_ifs
        · exact rowArity_le _
        · omega
    _ = 3 * rows P := by simp [mul_comm]

omit hsat in
theorem expOfAt_pos (i : Fin (rows P)) (j : Fin 3) : 1 ≤ expOfAt P c Qc i j := by
  unfold expOfAt; omega

omit hsat in
theorem expOfAt_le_total (i : Fin (rows P)) (j : Fin 3)
    (hact : activeMask (rowEnvAt P c Qc i) j = 1) :
    expOfAt P c Qc i j ≤ totalRequestsAt P c Qc := by
  have h1 := active_lt_rowArity (rowEnvAt P c Qc i) j hact
  have h2 : prefixExpAt P c Qc ((i : ℕ) + 1) ≤ prefixExpAt P c Qc (rows P) :=
    prefixExpAt_mono P c Qc i.isLt
  rw [prefixExpAt_succ P c Qc i i.isLt, Fin.eta] at h2
  unfold expOfAt totalRequestsAt
  omega

omit hsat in
theorem expOfAt_lt_of_row_lt {i i' : Fin (rows P)} (hii : i < i') (j j' : Fin 3)
    (hact : activeMask (rowEnvAt P c Qc i) j = 1) :
    expOfAt P c Qc i j < expOfAt P c Qc i' j' := by
  have h1 := active_lt_rowArity (rowEnvAt P c Qc i) j hact
  have h2 : prefixExpAt P c Qc ((i : ℕ) + 1) ≤ prefixExpAt P c Qc i' := prefixExpAt_mono P c Qc hii
  rw [prefixExpAt_succ P c Qc i i.isLt, Fin.eta] at h2
  unfold expOfAt
  omega

omit hsat in
theorem expOfAt_inj_row (i : Fin (rows P)) {j j' : Fin 3}
    (h : expOfAt P c Qc i j = expOfAt P c Qc i j') : j = j' := by
  unfold expOfAt at h
  exact Fin.ext (by omega)

omit hsat in
theorem rowRequests_length_at (i : Fin (rows P))
    (hbool : ∀ j : Fin 3,
      activeMask (rowEnvAt P c Qc i) j = 0 ∨ activeMask (rowEnvAt P c Qc i) j = 1)
    (h21 : activeMask (rowEnvAt P c Qc i) 2 = 1 → activeMask (rowEnvAt P c Qc i) 1 = 1) :
    (rowRequests (rowEnvAt P c Qc i)).length = rowArity (rowEnvAt P c Qc i) := by
  have h0 := activeMask_zero (rowEnvAt P c Qc i)
  simp only [rowRequests, List.finRange, List.ofFn_succ, List.ofFn_zero, List.filterMap_cons,
    List.filterMap_nil, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, h0, if_true, rowArity]
  rcases hbool 2 with h2 | h2
  · rcases hbool 1 with h1 | h1
    · simp [h1, h2]
    · simp [h1, h2]
  · have h1 := h21 h2
    simp [h1, h2]

omit hsat in
theorem active_two_imp_one_at (i : Fin (rows P)) (s : ComputeTable.State)
    (hsel : ∀ st, (rowEnvAt P c Qc i).toSourceEnv.trace (opCol st) = ComputeTable.opSel s st) :
    activeMask (rowEnvAt P c Qc i) 2 = 1 → activeMask (rowEnvAt P c Qc i) 1 = 1 := by
  have h0 := hsel .s0; have h2 := hsel .s2; have h5 := hsel .s5; have h6 := hsel .s6
  have h7 := hsel .s7; have h8 := hsel .s8; have h9 := hsel .s9
  simp only [opCol] at h0 h2 h5 h6 h7 h8 h9
  simp only [activeMask, sampledActive, Expr.eval, Fin.isValue, Fin.val_one, Fin.val_two, h0, h2,
    h5, h6, h7, h8, h9]
  cases s <;> simp [ComputeTable.opSel]

/-- Twin of `totalRequests_eq_length`. -/
theorem totalRequestsAt_eq_length (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) :
    totalRequestsAt P c Qc = (hostileRequestsAt P c Qc).length := by
  unfold totalRequestsAt prefixExpAt hostileRequestsAt
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn,
    ← Fin.sum_univ_eq_sum_range
      (fun k => if h : k < rows P then rowArity (rowEnvAt P c Qc ⟨k, h⟩) else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨s, hsel⟩ := source_selector_at P c Qc hsat hchar i
  simp only [i.isLt, dite_true, Function.comp]
  rw [rowRequests_length_at P c Qc i (fun j => activeMask_bool_at P c Qc hsat hchar i j)
    (active_two_imp_one_at P c Qc i s hsel)]

end Deployed

section Nodup

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
  (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
  (hz0 : nprSeed c.1 ≠ 0)
  (hα : alphaM c.1 ∉ TimestampCollisionEvent (totalRequestsAt P c Qc))
include hsat hchar hz0 hα

/-- Twin of `expOf_eq_of_ts_eq`. -/
theorem expOfAt_eq_of_ts_eq {i i' : Fin (rows P)} {j j' : Fin 3}
    (hact : activeMask (rowEnvAt P c Qc i) j = 1) (hact' : activeMask (rowEnvAt P c Qc i') j' = 1)
    (h : rowRecord (rowEnvAt P c Qc i) j 7 = rowRecord (rowEnvAt P c Qc i') j' 7) :
    expOfAt P c Qc i j = expOfAt P c Qc i' j' := by
  rw [rowRecord_ts_at_at P c Qc hsat hchar hz0 i j hact,
    rowRecord_ts_at_at P c Qc hsat hchar hz0 i' j' hact'] at h
  have hpow := mul_left_cancel₀ (hostile_ln0_ne_zero_at P c Qc hsat) h
  exact pow_inj_of_not_collision hα (expOfAt_pos P c Qc i j) (expOfAt_le_total P c Qc i j hact)
    (expOfAt_pos P c Qc i' j') (expOfAt_le_total P c Qc i' j' hact') hpow

theorem rowRequests_nodup_at (i : Fin (rows P)) : (rowRequests (rowEnvAt P c Qc i)).Nodup := by
  unfold rowRequests
  refine List.Nodup.filterMap ?_ (List.nodup_finRange 3)
  intro j j' r hj hj'
  by_cases ha : activeMask (rowEnvAt P c Qc i) j = 1
  · rw [if_pos ha] at hj
    by_cases ha' : activeMask (rowEnvAt P c Qc i) j' = 1
    · rw [if_pos ha'] at hj'
      have hr : rowRecord (rowEnvAt P c Qc i) j = rowRecord (rowEnvAt P c Qc i) j' :=
        (Option.some_inj.mp hj).trans (Option.some_inj.mp hj').symm
      exact expOfAt_inj_row P c Qc i
        (expOfAt_eq_of_ts_eq P c Qc hsat hchar hz0 hα ha ha' (congrFun hr 7))
    · rw [if_neg ha'] at hj'; cases hj'
  · rw [if_neg ha] at hj; cases hj

theorem rowRequests_disjoint_at {i i' : Fin (rows P)} (hii : i < i') :
    List.Disjoint (rowRequests (rowEnvAt P c Qc i)) (rowRequests (rowEnvAt P c Qc i')) := by
  intro r hr hr'
  simp only [rowRequests, List.mem_filterMap, List.mem_finRange, true_and] at hr hr'
  obtain ⟨j, hj⟩ := hr
  obtain ⟨j', hj'⟩ := hr'
  by_cases ha : activeMask (rowEnvAt P c Qc i) j = 1
  · by_cases ha' : activeMask (rowEnvAt P c Qc i') j' = 1
    · rw [if_pos ha] at hj
      rw [if_pos ha'] at hj'
      have hr : rowRecord (rowEnvAt P c Qc i) j = rowRecord (rowEnvAt P c Qc i') j' :=
        (Option.some_inj.mp hj).trans (Option.some_inj.mp hj').symm
      have heq := expOfAt_eq_of_ts_eq P c Qc hsat hchar hz0 hα ha ha' (congrFun hr 7)
      have hlt := expOfAt_lt_of_row_lt P c Qc hii j j' ha
      omega
    · rw [if_neg ha'] at hj'; cases hj'
  · rw [if_neg ha] at hj; cases hj

theorem hostile_requests_nodup_of_total_at : (hostileRequestsAt P c Qc).Nodup := by
  unfold hostileRequestsAt
  rw [List.nodup_flatten]
  constructor
  · intro l hl
    rw [List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    exact rowRequests_nodup_at P c Qc hsat hchar hz0 hα i
  · rw [List.pairwise_ofFn]
    intro i i' hii
    exact rowRequests_disjoint_at P c Qc hsat hchar hz0 hα hii

end Nodup

/-- **Twin of `hostile_requests_nodup`**: for any trace `computeChipAt c` accepts, under `hchar`,
`nprSeed c.1 ≠ 0` and `alphaM c.1 ∉ TimestampCollisionEvent |requests|`, the family request
list is `Nodup`. -/
theorem hostile_requests_nodup_at
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : nprSeed c.1 ≠ 0)
    (hα : alphaM c.1 ∉ TimestampCollisionEvent (hostileRequestsAt P c Qc).length) :
    (hostileRequestsAt P c Qc).Nodup := by
  rw [← totalRequestsAt_eq_length P c Qc hsat hchar] at hα
  exact hostile_requests_nodup_of_total_at P c Qc hsat hchar hz0 hα

end

end Nock.NockVMROM.Thm54.FamilyIOChain
