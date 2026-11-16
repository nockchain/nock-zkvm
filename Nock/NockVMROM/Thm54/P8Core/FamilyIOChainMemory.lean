/-
  Nock/NockVMROM/Thm54/P8Core/FamilyIOChainMemory.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.FamilyIOChainMemory`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/FamilyIOChainMemory.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.FamilyIOChainCompute
import Nock.NockVMROM.Thm54.P8Core.FamilyMemoryRows
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
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open OptimizedMemoryCanonicalSatisfaction
open OptimizedMemoryHostileAccumulator (memRowCoins memRowRecord10 memRowTerm
  rowRecord_eq_memRowRecord10 denominatorPin_eval_iff contribution_eq_memRowTerm_of_io
  rowResponseTerms
  rowResponses rowDenominator accInit_mem accTerminal_mem accStep_mem contribution_mem
  verBool_mem safeNormalisation_mem safeInverse_mem denominatorPinMixed_mem
  intermediateInit_mem intermediateTerminal_mem chainMixed_mem)
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

/-- The memory chip's row count (`OptimizedMemoryHostileAccumulator.rows`). -/
abbrev memRows : ℕ := OptimizedMemoryHostileAccumulator.rows P

/-- Base-field family memory row environment of a family trace. -/
abbrev memEnvF (Qm : Fin (P.memoryChipAt c).rap.w → F[X]) (i : Fin (memRows P)) : Env F :=
  memoryBaseEnvAt P c (honestQm P c Qm) i

/-- Gathered `𝕂` family memory row environment of a family trace. -/
abbrev memEnvK (Qm : Fin (P.memoryChipAt c).rap.w → F[X]) (i : Fin (memRows P)) : Env K :=
  memorySourceEnvAt P c (honestQm P c Qm) i

variable (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

/-- The family memory env's `𝕂` slot `q < 9` is `memoryKOfTuple c q`. -/
theorem memEnvK_chal (i : Fin (memRows P)) (q : Fin 9) :
    (memEnvK P c Qm i).chal q = memoryKOfTuple c q := by
  simp only [memEnvK, memorySourceEnvAt, memorySourceTemplate_col0, gatherEnv, memoryCol0,
    memoryBaseEnvAt, envOfTrace]
  simp_rw [memoryChalValOfTuple_slot P.optimized.basis c q]
  change reconstruct P.optimized.basis (coord P.optimized.basis (memoryKOfTuple c q)) =
    memoryKOfTuple c q
  exact reconstruct_coord P.optimized.basis (memoryKOfTuple c q)

/-- The family memory chip's IO coins (slots `4`/`5`) are the tuple's `c.2.1`. -/
theorem memRowCoins_at (i : Fin (memRows P)) : memRowCoins (memEnvK P c Qm i) = chipCoinsAt c := by
  have h4 := memEnvK_chal P c Qm i ⟨4, by decide⟩
  have h5 := memEnvK_chal P c Qm i ⟨5, by decide⟩
  simp only [memRowCoins]
  rw [h4, h5]
  rfl

/-- The family memory env's traces are the package memory env's at the reindexed trace. -/
theorem memEnvK_trace (i : Fin (memRows P)) (j : ℕ) :
    (memEnvK P c Qm i).trace j = (P.memorySourceEnv (honestQm P c Qm) i).trace j := by
  simp only [memEnvK, memorySourceEnvAt, OptimizedFullStrictNockVMROMPackage.memorySourceEnv,
    gatherEnv, memoryBaseEnvAt, OptimizedFullStrictNockVMROMPackage.memoryBaseEnv, envOfTrace]

theorem memEnvF_trace (i : Fin (memRows P)) (j : ℕ) :
    (memEnvF P c Qm i).trace j = (P.memoryBaseEnv (honestQm P c Qm) i).trace j := by
  simp only [memEnvF, memoryBaseEnvAt, OptimizedFullStrictNockVMROMPackage.memoryBaseEnv,
    envOfTrace]

/-- The public `requests` gathered at any family memory row is the package's `memoryPublic`
block `12..14` (the family public map is the package map off `6..8`). -/
theorem gathered_requests_mem_at (i : Fin (memRows P)) :
    (memEnvK P c Qm i).pub 2 =
      ∑ k : Fin 3, P.optimized.memoryPublic (12 + (k : ℕ)) • P.optimized.basis k := by
  simp only [memEnvK, memorySourceEnvAt, memorySourceTemplate_col0, gatherEnv, memoryCol0,
    memoryBaseEnvAt, envOfTrace]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [OptimizedFullStrictNockVMROMPackage.familyMemoryPublic,
    memoryPublicOfTuple_eq_pkg _ _ _ _ _ _ (by omega)]

section Rows

variable (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
include hsat

/-- Twin of `masks_at` (memory): base columns `4`/`5` are the first/last-row masks. -/
theorem masks_at_mem_at (i : Fin (memRows P)) :
    (memEnvF P c Qm i).trace 4 = (if (i : ℕ) = 0 then 1 else 0) ∧
      (memEnvF P c Qm i).trace 5 = (if (i : ℕ) + 1 = memRows P then 1 else 0) := by
  have hbind := (source_sat_at P c Qm hsat).2
  have hinj := P.optimized.memoryNodes_injective
  have hw : (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
      P.optimized.memoryNodes P.optimized.basis (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit
      P.optimized.family.problem.cfg.kMem).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit (rowNodeSet P.optimized.memoryNodes)).1
  have h4 : 4 < (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
      P.optimized.memoryNodes P.optimized.basis (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit
      P.optimized.family.problem.cfg.kMem).rap.w := by rw [hw]; norm_num
  have h5 : 5 < (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
      P.optimized.memoryNodes P.optimized.basis (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit
      P.optimized.family.problem.cfg.kMem).rap.w := by rw [hw]; norm_num
  have h0 := hbind ⟨0, by change 0 < 4; norm_num⟩
  have h1 := hbind ⟨1, by change 1 < 4; norm_num⟩
  have hc0 : (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
      P.optimized.memoryNodes P.optimized.basis (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit
      P.optimized.family.problem.cfg.kMem).preprocessingColumn
        ⟨0, by change 0 < 4; norm_num⟩ = ⟨4, h4⟩ := rfl
  have hc1 : (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
      P.optimized.memoryNodes P.optimized.basis (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit
      P.optimized.family.problem.cfg.kMem).preprocessingColumn
        ⟨1, by change 1 < 4; norm_num⟩ = ⟨5, h5⟩ := rfl
  rw [hc0] at h0
  rw [hc1] at h1
  have h4' : (4 : ℕ) < 182 := by norm_num
  have h5' : (5 : ℕ) < 182 := by norm_num
  constructor
  · rw [memEnvF, ← envF_eq_base P c Qm i]
    simp only [envOfTrace, dif_pos h4']
    rw [show projAt P c Qm ⟨4, h4'⟩ = OptimizedMemoryCanonicalTrace.firstRowMask
      P.optimized.memoryNodes from h0,
      OptimizedMemoryCanonicalTrace.firstRowMask_eval _ hinj]
  · rw [memEnvF, ← envF_eq_base P c Qm i]
    simp only [envOfTrace, dif_pos h5']
    rw [show projAt P c Qm ⟨5, h5'⟩ = OptimizedMemoryCanonicalTrace.lastRowMask
      P.optimized.memoryNodes from h1,
      OptimizedMemoryCanonicalTrace.lastRowMask_eval _ hinj]

/-- Twin of `mixed_at` (memory). -/
theorem mixed_at_mem (i : Fin (memRows P)) :
    ∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
      g.eval (memEnvK P c Qm i) (memEnvF P c Qm i) = 0 :=
  mixed_at_family P c Qm hsat i

/-- Twin of `hostile_intermediate_anchored`. -/
theorem hostile_intermediate_anchored_at :
    (memEnvK P c Qm (OptimizedMemoryHostileAccumulator.firstRow P)).trace 27 = 0 ∧
      (memEnvK P c Qm (OptimizedMemoryHostileAccumulator.lastRow P)).trace 28 = 0 := by
  have hI := fun i => mixed_at_mem P c Qm hsat i _ (intermediateInit_mem P.optimized.basis)
  have hT := fun i => mixed_at_mem P c Qm hsat i _ (intermediateTerminal_mem P.optimized.basis)
  constructor
  · have h := hI (OptimizedMemoryHostileAccumulator.firstRow P)
    simp only [intermediateInit, MixedExpr.eval, bcur, CoeffExpr.eval] at h
    rw [(masks_at_mem_at P c Qm hsat _).1, if_pos rfl, map_one, one_mul] at h
    exact h
  · have h := hT (OptimizedMemoryHostileAccumulator.lastRow P)
    simp only [intermediateTerminal, MixedExpr.eval, bcur, CoeffExpr.eval] at h
    have hlast : ((OptimizedMemoryHostileAccumulator.lastRow P : ℕ) + 1 = memRows P) :=
      Nat.sub_add_cancel P.optimized.family.problem.cfg.memRows_pos
    rw [(masks_at_mem_at P c Qm hsat _).2, if_pos hlast, map_one, one_mul] at h
    exact h

/-- Twin of `acc_step_nonlast`. -/
theorem acc_step_nonlast_at (i : Fin (memRows P)) (hi : (i : ℕ) + 1 < memRows P) :
    (memEnvK P c Qm i).traceNext 43 =
      (memEnvK P c Qm i).trace 43 + (memEnvK P c Qm i).trace 42 := by
  have hc := mixed_at_mem P c Qm hsat i _ (accStep_mem P.optimized.basis)
  have h5 : (memEnvF P c Qm i).trace 5 = 0 := by
    rw [(masks_at_mem_at P c Qm hsat i).2, if_neg (by omega)]
  simp only [accStep, MixedExpr.eval, bcur, CoeffExpr.eval, h5, sub_zero, map_one,
    one_mul, sub_eq_zero] at hc
  exact hc

omit hsat in
/-- Orbit alignment on the family memory env: next-row role `r` at row `i` is role `r` at
row `i+1` (`r < 58`). -/
theorem next_trace_mem_at (r : ℕ) (hr : r < 58) (i : Fin (memRows P))
    (hi : (i : ℕ) + 1 < memRows P) :
    (memEnvK P c Qm i).traceNext r = (memEnvK P c Qm ⟨(i : ℕ) + 1, hi⟩).trace r := by
  have hadj := P.optimized.memoryOrbitAligned i hi
  simp only [memEnvK, memorySourceEnvAt, memorySourceTemplate_col0, gatherEnv, memoryCol0,
    memoryBaseEnvAt, envOfTrace]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hlt : 6 + 3 * r + (k : ℕ) < 182 := by have := k.isLt; omega
  simp only [dif_pos hlt]
  rw [hadj, mul_comm]

omit hsat in
/-- Twin of `next_acc` (memory). -/
theorem next_acc_mem_at (i : Fin (memRows P)) (hi : (i : ℕ) + 1 < memRows P) :
    (memEnvK P c Qm i).traceNext 43 = (memEnvK P c Qm ⟨(i : ℕ) + 1, hi⟩).trace 43 :=
  next_trace_mem_at P c Qm 43 (by norm_num) i hi

/-- Twin of `acc_first` (memory). -/
theorem acc_first_mem_at :
    (memEnvK P c Qm (OptimizedMemoryHostileAccumulator.firstRow P)).trace 43 = 0 := by
  have h := mixed_at_mem P c Qm hsat (OptimizedMemoryHostileAccumulator.firstRow P) _
    (accInit_mem P.optimized.basis)
  simp only [accInit, MixedExpr.eval, bcur, CoeffExpr.eval] at h
  rw [(masks_at_mem_at P c Qm hsat _).1, if_pos rfl, map_one, one_mul] at h
  exact h

/-- Twin of `contrib_eq_term`. -/
theorem contrib_eq_term_at (i : Fin (memRows P)) :
    (memEnvK P c Qm i).trace 42 = memRowTerm (memEnvK P c Qm i) :=
  contribution_eq_memRowTerm_of_io (memEnvK P c Qm i) (memEnvF P c Qm i)
    (mixed_at_mem P c Qm hsat i _ (verBool_mem P.optimized.basis))
    (mixed_at_mem P c Qm hsat i _ (safeNormalisation_mem P.optimized.basis))
    (mixed_at_mem P c Qm hsat i _ (safeInverse_mem P.optimized.basis))
    (mixed_at_mem P c Qm hsat i _ (contribution_mem P.optimized.basis))

/-- Twin of `acc_last_plus_contrib`. -/
theorem acc_last_plus_contrib_at :
    (memEnvK P c Qm (OptimizedMemoryHostileAccumulator.lastRow P)).trace 43 +
        (memEnvK P c Qm (OptimizedMemoryHostileAccumulator.lastRow P)).trace 42 =
      (memEnvK P c Qm (OptimizedMemoryHostileAccumulator.lastRow P)).pub 2 := by
  have h := mixed_at_mem P c Qm hsat (OptimizedMemoryHostileAccumulator.lastRow P) _
    (accTerminal_mem P.optimized.basis)
  have hlast : ((OptimizedMemoryHostileAccumulator.lastRow P : ℕ) + 1 = memRows P) :=
    Nat.sub_add_cancel P.optimized.family.problem.cfg.memRows_pos
  simp only [accTerminal, MixedExpr.eval, bcur, CoeffExpr.eval] at h
  rw [(masks_at_mem_at P c Qm hsat _).2, if_pos hlast, map_one, one_mul, sub_eq_zero] at h
  exact h

/-- **Twin of `hostile_role37_eq_compress`**: at every row of an accepted family memory trace,
role `37` is `compress (c.2.1) (record)` — the tuple's IO coins by definition, no pin. -/
theorem hostile_role37_eq_compress_at (i : Fin (memRows P)) :
    (memEnvK P c Qm i).trace 37 =
      FiniteIO.compress (chipCoinsAt c) (memRowRecord10 (memEnvK P c Qm i) (memEnvF P c Qm i)) := by
  rw [← memRowCoins_at P c Qm i]
  exact (denominatorPin_eval_iff _ _).1
    (mixed_at_mem P c Qm hsat i _ (denominatorPinMixed_mem P.optimized.basis))

omit hsat in
/-- Twin of the memory `prefixSum`. -/
def memPrefixSumAt (m : ℕ) : K :=
  ∑ k ∈ Finset.range m, if h : k < memRows P then memRowTerm (memEnvK P c Qm ⟨k, h⟩) else 0

omit hsat in
theorem memPrefixSumAt_succ (m : ℕ) (hm : m < memRows P) :
    memPrefixSumAt P c Qm (m + 1) =
      memPrefixSumAt P c Qm m + memRowTerm (memEnvK P c Qm ⟨m, hm⟩) := by
  simp [memPrefixSumAt, Finset.sum_range_succ, hm]

theorem acc_eq_memPrefixSum_at :
    ∀ (m : ℕ) (hm : m < memRows P), (memEnvK P c Qm ⟨m, hm⟩).trace 43 = memPrefixSumAt P c Qm m := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [memPrefixSumAt, Finset.range_zero, Finset.sum_empty]
      exact acc_first_mem_at P c Qm hsat
  | succ m ih =>
      intro hm
      have hm' : m < memRows P := by omega
      rw [← next_acc_mem_at P c Qm ⟨m, hm'⟩ hm, acc_step_nonlast_at P c Qm hsat ⟨m, hm'⟩ hm,
        contrib_eq_term_at P c Qm hsat ⟨m, hm'⟩, ih hm', memPrefixSumAt_succ P c Qm m hm']

/-- **Twin of `hostile_requests_eq_sum_memRowTerms`**: the memory public `requests` is
`Σᵢ ver(i) · denom(i)⁻¹` at any accepted family memory trace. -/
theorem hostile_requests_eq_sum_memRowTerms_at :
    (memEnvK P c Qm (OptimizedMemoryHostileAccumulator.lastRow P)).pub 2 =
      ∑ i : Fin (memRows P), memRowTerm (memEnvK P c Qm i) := by
  have hpos := P.optimized.family.problem.cfg.memRows_pos
  have hlast : (memEnvK P c Qm (OptimizedMemoryHostileAccumulator.lastRow P)).trace 43 =
      memPrefixSumAt P c Qm (memRows P - 1) :=
    acc_eq_memPrefixSum_at P c Qm hsat (memRows P - 1) _
  rw [← acc_last_plus_contrib_at P c Qm hsat,
    contrib_eq_term_at P c Qm hsat (OptimizedMemoryHostileAccumulator.lastRow P), hlast,
    ← memPrefixSumAt_succ P c Qm (memRows P - 1) _, Nat.sub_add_cancel hpos]
  simp only [memPrefixSumAt]
  rw [← Fin.sum_univ_eq_sum_range (fun k => if h : k < memRows P then
    memRowTerm (memEnvK P c Qm ⟨k, h⟩) else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [i.isLt]

/-- Twin of `ver_bool`. -/
theorem ver_bool_at (i : Fin (memRows P)) :
    (memEnvK P c Qm i).trace 39 = 0 ∨ (memEnvK P c Qm i).trace 39 = 1 := by
  have h1 := mixed_at_mem P c Qm hsat i _ (verBool_mem P.optimized.basis)
  simp only [verBool, MixedExpr.eval, mul_eq_zero, sub_eq_zero, Int.cast_one] at h1
  exact h1

/-- Twin of `denom_ne_zero_of_ver`. -/
theorem denom_ne_zero_of_ver_at (i : Fin (memRows P))
    (hver : (memEnvK P c Qm i).trace 39 = 1) : (memEnvK P c Qm i).trace 37 ≠ 0 := by
  have s0 := mixed_at_mem P c Qm hsat i _ (safeInverse_mem P.optimized.basis)
  have s4 := mixed_at_mem P c Qm hsat i _ (safeNormalisation_mem P.optimized.basis)
  simp only [safeInverse, safeNormalisation, MixedExpr.eval, Int.cast_one, hver] at s0 s4
  intro h0
  have h50 : (memEnvK P c Qm i).trace 50 = 0 := by linear_combination s4 + h0
  rw [h50, zero_mul] at s0
  exact one_ne_zero (by linear_combination -s0)

end Rows

/-- **Twin of `OptimizedMemoryHostileAccumulator.hostileResponses`**: the records of the
`ver = 1` rows of a family memory trace, in row order. -/
def hostileResponsesAt : List (Fin 10 → K) :=
  (List.ofFn fun i : Fin (memRows P) =>
    rowResponses (memEnvK P c Qm i) (memEnvF P c Qm i)).flatten

/-- The family response list is the package's at the reindexed trace: memory records read
trace columns only (`HostileRecordLists.rowRecord`), and the traces agree. -/
theorem hostileResponsesAt_eq_package :
    hostileResponsesAt P c Qm = P.hostileResponses (honestQm P c Qm) := by
  unfold hostileResponsesAt OptimizedFullStrictNockVMROMPackage.hostileResponses
  refine congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_))
  have hK : ∀ j, (memEnvK P c Qm i).trace j = (P.memorySourceEnv (honestQm P c Qm) i).trace j :=
    memEnvK_trace P c Qm i
  have hF : ∀ j, (memEnvF P c Qm i).trace j = (P.memoryBaseEnv (honestQm P c Qm) i).trace j :=
    memEnvF_trace P c Qm i
  have hrec : OptimizedMemoryHostileAccumulator.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) =
      OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv (honestQm P c Qm) i)
        (P.memoryBaseEnv (honestQm P c Qm) i) := by
    funext j
    simp only [OptimizedMemoryHostileAccumulator.rowRecord, hK, hF]
  simp only [rowResponses, rowResponseTerms, rowDenominator, hK 39]
  split_ifs <;> simp [hrec]

/-- Twin of `hostile_responses_eq_sum_compress_of_denominatorPin`, unconditional: at the family
chip the pin holds at every row of an accepted trace (`hostile_role37_eq_compress_at`). -/
theorem hostile_responses_eq_sum_compress_at
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm) :
    (∑ i : Fin (memRows P), memRowTerm (memEnvK P c Qm i)) =
      ((hostileResponsesAt P c Qm).map fun r => (FiniteIO.compress (chipCoinsAt c) r)⁻¹).sum := by
  rw [hostileResponsesAt, List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn,
    List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases ver_bool_at P c Qm hsat i with h | h
  · simp [memRowTerm, rowResponses, rowResponseTerms, h]
  · have h37 := hostile_role37_eq_compress_at P c Qm hsat i
    rw [← rowRecord_eq_memRowRecord10] at h37
    simp [memRowTerm, rowResponses, rowResponseTerms, h, h37]

variable (Qc : Fin (P.computeChipAt c).rap.w → F[X])

/-- **Twin of `OptimizedHostileIOAssembly.hostileRecords`**: the records both family chips
commit to. -/
def hostileRecordsAt : FiniteIO.PreChallengeRecords K 10 :=
  ⟨hostileRequestsAt P c Qc, hostileResponsesAt P c Qm⟩

@[simp] theorem hostileRecordsAt_requests :
    (hostileRecordsAt P c Qm Qc).requests = hostileRequestsAt P c Qc := rfl

@[simp] theorem hostileRecordsAt_responses :
    (hostileRecordsAt P c Qm Qc).responses = hostileResponsesAt P c Qm := rfl

/-- Twin of `mem_hostileRequests`. -/
theorem mem_hostileRequestsAt {r : Fin 10 → K} (hr : r ∈ hostileRequestsAt P c Qc) :
    ∃ (i : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnvAt P c Qc i) j = 1 ∧ r = rowRecord (rowEnvAt P c Qc i) j := by
  simp only [hostileRequestsAt, List.mem_flatten, List.mem_ofFn] at hr
  obtain ⟨l, ⟨i, rfl⟩, hl⟩ := hr
  simp only [rowRequests, List.mem_filterMap, List.mem_finRange, true_and] at hl
  obtain ⟨j, hj⟩ := hl
  by_cases hact : activeMask (rowEnvAt P c Qc i) j = 1
  · rw [if_pos hact] at hj
    exact ⟨i, j, hact, (Option.some_inj.mp hj).symm⟩
  · rw [if_neg hact] at hj
    exact absurd hj (by simp)

/-- Twin of `mem_hostileResponses`. -/
theorem mem_hostileResponsesAt {r : Fin 10 → K} (hr : r ∈ hostileResponsesAt P c Qm) :
    ∃ i : Fin (memRows P), (memEnvK P c Qm i).trace 39 = 1 ∧
      r = OptimizedMemoryHostileAccumulator.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) := by
  simp only [hostileResponsesAt, List.mem_flatten, List.mem_ofFn] at hr
  obtain ⟨l, ⟨i, rfl⟩, hl⟩ := hr
  simp only [rowResponses, rowResponseTerms] at hl
  split_ifs at hl with hver
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hl
    exact ⟨i, hver, hl⟩
  · simp at hl

/-- Twin of `rowRecord_mem_hostileRequests`. -/
theorem rowRecord_mem_hostileRequestsAt (i : Fin (rows P)) (j : Fin 3)
    (hact : activeMask (rowEnvAt P c Qc i) j = 1) :
    rowRecord (rowEnvAt P c Qc i) j ∈ hostileRequestsAt P c Qc := by
  simp only [hostileRequestsAt, List.mem_flatten, List.mem_ofFn]
  refine ⟨_, ⟨i, rfl⟩, ?_⟩
  simp only [rowRequests, List.mem_filterMap, List.mem_finRange, true_and]
  exact ⟨j, by rw [if_pos hact]⟩

/-- Twin of `pole_excluded_of_not_poleHit`, at the tuple's coins. -/
theorem pole_excluded_of_not_poleHit_at
    (hhit : c.2.1.2 ∉ FiniteIO.IOPoleHitEvent (hostileRecordsAt P c Qm Qc) c.2.1.1) :
    ∀ (i : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnvAt P c Qc i) j = 1 → slotDenominator (rowEnvAt P c Qc i) j ≠ 0 := by
  intro i j hact h0
  apply hhit
  simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨rowRecord (rowEnvAt P c Qc i) j,
    List.mem_append_left _ (rowRecord_mem_hostileRequestsAt P c Qc i j hact), ?_⟩
  rw [slotDenominator_eq_compress, rowCoins_rowEnvAt] at h0
  exact h0

/-- Twin of `compress_request_ne_zero`. -/
theorem compress_request_ne_zero_at
    (hpole : ∀ (i : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnvAt P c Qc i) j = 1 → slotDenominator (rowEnvAt P c Qc i) j ≠ 0)
    {r : Fin 10 → K} (hr : r ∈ hostileRequestsAt P c Qc) :
    FiniteIO.compress (chipCoinsAt c) r ≠ 0 := by
  obtain ⟨i, j, hact, rfl⟩ := mem_hostileRequestsAt P c Qc hr
  have h := hpole i j hact
  rwa [slotDenominator_eq_compress, rowCoins_rowEnvAt] at h

/-- Twin of `compress_response_ne_zero`: a consequence of acceptance (inverse column, pin). -/
theorem compress_response_ne_zero_at
    (hsatm : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    {r : Fin 10 → K} (hr : r ∈ hostileResponsesAt P c Qm) :
    FiniteIO.compress (chipCoinsAt c) r ≠ 0 := by
  obtain ⟨i, hver, rfl⟩ := mem_hostileResponsesAt P c Qm hr
  have h37 := denom_ne_zero_of_ver_at P c Qm hsatm i hver
  rwa [hostile_role37_eq_compress_at P c Qm hsatm i, ← rowRecord_eq_memRowRecord10] at h37

/-- **Twin of `hostile_io_identity_core`**: for two family traces the family chips accept, under
boolean masks and the compute-side pole exclusion,
`Σ_{r ∈ requests} (compress c.2.1 r)⁻¹ = Σ_{r ∈ responses} (compress c.2.1 r)⁻¹`.  The shared `requests` public is the package's on
both chips (`compute_requests_eq_memory_requests`). -/
theorem hostile_io_identity_core_at
    (hsatc : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hsatm : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (hbool : ∀ (i : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnvAt P c Qc i) j = 0 ∨ activeMask (rowEnvAt P c Qc i) j = 1)
    (hpole : ∀ (i : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnvAt P c Qc i) j = 1 → slotDenominator (rowEnvAt P c Qc i) j ≠ 0) :
    ((hostileRequestsAt P c Qc).map fun r => (FiniteIO.compress (chipCoinsAt c) r)⁻¹).sum =
      ((hostileResponsesAt P c Qm).map fun r => (FiniteIO.compress (chipCoinsAt c) r)⁻¹).sum := by
  have hreq : (rowEnvAt P c Qc (lastRow P)).extensionPublic 2 =
      ((hostileRequestsAt P c Qc).map fun r => (FiniteIO.compress (chipCoinsAt c) r)⁻¹).sum := by
    rw [hostile_requests_eq_sum_logUp_at P c Qc hsatc hbool hpole, hostileRequestsAt,
      List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn, List.sum_ofFn]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [logUpRowTerm_eq_rowRequests_at P c Qc i (hbool i)]
    rfl
  rw [← hreq, gathered_requests_at,
    OptimizedMemoryHostileAccumulator.compute_requests_eq_memory_requests P,
    ← gathered_requests_mem_at P c Qm (OptimizedMemoryHostileAccumulator.lastRow P),
    hostile_requests_eq_sum_memRowTerms_at P c Qm hsatm,
    hostile_responses_eq_sum_compress_at P c Qm hsatm]

theorem pole_add_reqVals_at (coins : FiniteIO.IOCoins K)
    (i : Fin (hostileRecordsAt P c Qm Qc).requests.length) :
    coins.pole + FiniteIO.reqVals (hostileRecordsAt P c Qm Qc) coins.gamma i =
      FiniteIO.compress coins ((hostileRecordsAt P c Qm Qc).requests.get i) :=
  rfl

theorem pole_add_respVals_at (coins : FiniteIO.IOCoins K)
    (j : Fin (hostileRecordsAt P c Qm Qc).responses.length) :
    coins.pole + FiniteIO.respVals (hostileRecordsAt P c Qm Qc) coins.gamma j =
      FiniteIO.compress coins ((hostileRecordsAt P c Qm Qc).responses.get j) :=
  rfl

/-- The three nonvanishing / identity premises of `finiteIO_sound_of_identity` at the family
records and the tuple's coins. -/
theorem family_identity_premises
    (hsatc : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hsatm : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hpoleHit : c.2.1.2 ∉ FiniteIO.IOPoleHitEvent (hostileRecordsAt P c Qm Qc) c.2.1.1) :
    (∀ i, (chipCoinsAt c).pole +
        FiniteIO.reqVals (hostileRecordsAt P c Qm Qc) (chipCoinsAt c).gamma i ≠ 0) ∧
    (∀ j, (chipCoinsAt c).pole +
        FiniteIO.respVals (hostileRecordsAt P c Qm Qc) (chipCoinsAt c).gamma j ≠ 0) ∧
    (∑ i, ((chipCoinsAt c).pole +
        FiniteIO.reqVals (hostileRecordsAt P c Qm Qc) (chipCoinsAt c).gamma i)⁻¹) =
      ∑ j, ((chipCoinsAt c).pole +
        FiniteIO.respVals (hostileRecordsAt P c Qm Qc) (chipCoinsAt c).gamma j)⁻¹ := by
  have hpole := pole_excluded_of_not_poleHit_at P c Qm Qc hpoleHit
  have hbool := fun i j => activeMask_bool_at P c Qc hsatc hchar i j
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [pole_add_reqVals_at]
    exact compress_request_ne_zero_at P c Qc hpole
      (List.get_mem (hostileRecordsAt P c Qm Qc).requests i)
  · intro j
    rw [pole_add_respVals_at]
    exact compress_response_ne_zero_at P c Qm hsatm
      (List.get_mem (hostileRecordsAt P c Qm Qc).responses j)
  · have h := hostile_io_identity_core_at P c Qm Qc hsatc hsatm hbool hpole
    rw [← hostileRecordsAt_requests P c Qm Qc, ← hostileRecordsAt_responses P c Qm Qc,
      OptimizedHostileIOAssembly.sum_requests_eq_sum_fin,
      OptimizedHostileIOAssembly.sum_responses_eq_sum_fin] at h
    exact h

/-- **Twin of `OptimizedHostileIOAssembly.hostile_LIO`**: at `DeployedAcceptanceAt`, with the
same premises (range, both `Nodup`, the three IO events at the family records and the tuple's
coins), `IO.LIO` of the family request and response lists.  No coin pin is read. -/
theorem hostile_LIO_at {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (hreqnd : (hostileRequestsAt P c Qc).Nodup)
    (hrespnd : (hostileResponsesAt P c Qm).Nodup)
    (hpoleHit : c.2.1.2 ∉ FiniteIO.IOPoleHitEvent (hostileRecordsAt P c Qm Qc) c.2.1.1)
    (hγ : c.2.1.1 ∉ FiniteIO.IORLCCollisionEvent (hostileRecordsAt P c Qm Qc))
    (hpoleEv : c.2.1.2 ∉ FiniteIO.IOLogDerivEvent (hostileRecordsAt P c Qm Qc) c.2.1.1) :
    IO.LIO Ksz (hostileRequestsAt P c Qc) (hostileResponsesAt P c Qm) := by
  obtain ⟨hdA, hdB, hend⟩ := family_identity_premises P c Qm Qc hacc.compute_satisfies
    hacc.memory_satisfies hchar hpoleHit
  exact FiniteIO.finiteIO_sound_of_identity (hostileRecordsAt P c Qm Qc) (chipCoinsAt c)
    hdA hdB hend hKp hKreq hKresp hreqnd hrespnd hγ hpoleEv

/-- Twin of `hostile_responses_nodup_core`. -/
theorem hostile_responses_nodup_core_at {Ksz : ℕ}
    (hsatc : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hsatm : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (hreqnd : (hostileRequestsAt P c Qc).Nodup)
    (hpoleHit : c.2.1.2 ∉ FiniteIO.IOPoleHitEvent (hostileRecordsAt P c Qm Qc) c.2.1.1)
    (hγ : c.2.1.1 ∉ FiniteIO.IORLCCollisionEvent (hostileRecordsAt P c Qm Qc))
    (hpoleEv : c.2.1.2 ∉ FiniteIO.IOLogDerivEvent (hostileRecordsAt P c Qm Qc) c.2.1.1) :
    (hostileResponsesAt P c Qm).Nodup := by
  obtain ⟨hdA, hdB, hend⟩ := family_identity_premises P c Qm Qc hsatc hsatm hchar hpoleHit
  exact FiniteIO.responses_nodup_of_identity (hostileRecordsAt P c Qm Qc) (chipCoinsAt c)
    hdA hdB hend hKp hKreq hKresp hreqnd hγ hpoleEv

/-- **Twin of `OptimizedHostileTimestamps.hostile_LIO'`.**  At `DeployedAcceptanceAt` (the
family chips, no pin field), `IO.LIO` of the family request and response lists, with the two
`Nodup` premises discharged: requests from the committed timestamps outside
`TimestampCollisionEvent` at the coin `alphaM c.1` (the chip's slot `0` **is** that coin), and
responses from the sampled-pole identity.  The NPR-seed premise is the chip's own slot `1`,
`nprSeed c.1 ≠ 0`, where the original reads the package constant `cfg.z`.  Same conclusion
shape as the original; no `same_problem`, no `p8`, no `S`. -/
theorem hostile_LIO'_at {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : nprSeed c.1 ≠ 0)
    (hα : alphaM c.1 ∉ TimestampCollisionEvent (hostileRequestsAt P c Qc).length)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (hpoleHit : c.2.1.2 ∉ FiniteIO.IOPoleHitEvent (hostileRecordsAt P c Qm Qc) c.2.1.1)
    (hγ : c.2.1.1 ∉ FiniteIO.IORLCCollisionEvent (hostileRecordsAt P c Qm Qc))
    (hpoleEv : c.2.1.2 ∉ FiniteIO.IOLogDerivEvent (hostileRecordsAt P c Qm Qc) c.2.1.1) :
    IO.LIO Ksz (hostileRequestsAt P c Qc) (hostileResponsesAt P c Qm) := by
  have hreqnd := hostile_requests_nodup_at P c Qc hacc.compute_satisfies hchar hz0 hα
  have hrespnd := hostile_responses_nodup_core_at P c Qm Qc hacc.compute_satisfies
    hacc.memory_satisfies hchar hKp hKreq hKresp hreqnd hpoleHit hγ hpoleEv
  exact hostile_LIO_at P c Qm Qc hacc hchar hKp hKreq hKresp hreqnd hrespnd hpoleHit hγ hpoleEv

/-- Twin of `hostile_LIO_of_not_failure`-shape for `hostile_LIO'`: the three IO events packaged
as `IOFailureEvent` over the family records. -/
theorem hostile_LIO'_at_of_not_failure {Ksz : ℕ} (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : nprSeed c.1 ≠ 0)
    (hα : alphaM c.1 ∉ TimestampCollisionEvent (hostileRequestsAt P c Qc).length)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (hostileRequestsAt P c Qc).length)
    (hKresp : (hostileResponsesAt P c Qm).length ≤ Ksz)
    (hio : c.2.1 ∉ FiniteIO.IOFailureEvent (hostileRecordsAt P c Qm Qc)) :
    IO.LIO Ksz (hostileRequestsAt P c Qc) (hostileResponsesAt P c Qm) := by
  have hnot : ¬ (c.2.1.1 ∈ FiniteIO.IORLCCollisionEvent (hostileRecordsAt P c Qm Qc) ∨
      c.2.1.2 ∈ FiniteIO.IOPoleHitEvent (hostileRecordsAt P c Qm Qc) c.2.1.1 ∨
      c.2.1.2 ∈ FiniteIO.IOLogDerivEvent (hostileRecordsAt P c Qm Qc) c.2.1.1) := by
    intro h
    apply hio
    simp only [FiniteIO.IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  exact hostile_LIO'_at P c Qm Qc hacc hchar hz0 hα hKp hKreq hKresp
    (fun h => hnot (Or.inr (Or.inl h))) (fun h => hnot (Or.inl h))
    (fun h => hnot (Or.inr (Or.inr h)))

end

end Nock.NockVMROM.Thm54.FamilyIOChain
