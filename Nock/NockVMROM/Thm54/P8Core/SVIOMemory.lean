/-
  Nock/NockVMROM/Thm54/P8Core/SVIOMemory.lean

`FamilyIOChainMemory` derives the memory LogUp identity from the package.  Here it is derived
  once over an abstract accepted memory row family `MemIORows` (the IO accumulator gates of the
  deployed mixed bucket, the first/last masks, orbit alignment of the accumulator role `43`, a
  row-constant pair of IO coins), and instantiated at the twelve-coin memory chip
  `PartA12.DeployedChipFamily12.memoryChipAt12` with **arbitrary** nodes, basis, orbit, public map
  and `kMem` (`memRows12`).

  * `MemIORows.requests_eq_sum_compress`: the memory terminal public `pub 2` equals the LogUp
    sum of the committed response records (the `ver = 1` rows) at the row coins.
  * `MemIORows.compress_response_ne_zero`: every committed response record has a nonzero
    compressed denominator (consequence of acceptance).

  **Memory-chip dependence.**  `MemIORows`
  fixes the deployed mixed bucket (`mixedTransitionGates b`, roles `37`, `39`, `42`, `43`) and
  `memRows12` is `memoryChipAt12`-specific.  The assembly in `SVIOAssembly` reads neither: it
  consumes only `MemIOFacts` (a response list, its LogUp identity at `ρ`, nonvanishing), which a
  new memory chip supplies by its own instance.

  Paper: the paper (one record per row, `ver`-selected), `:568-599` (the memory accumulator,
  seeded "as-is" with `requests`), `:577-579` (the denominator pin).
-/
import Nock.NockVMROM.Thm54.P8Core.PartAMemoryChip12
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.OptimizedMemoryHostileAccumulator

namespace Nock.NockVMROM.Thm54.SVIO

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
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open OptimizedMemoryHostileAccumulator (memRowCoins memRowRecord10 memRowTerm
  rowRecord_eq_memRowRecord10 denominatorPin_eval_iff contribution_eq_memRowTerm_of_io
  rowResponseTerms rowResponses rowDenominator accInit_mem accTerminal_mem accStep_mem
  contribution_mem verBool_mem safeNormalisation_mem safeInverse_mem denominatorPinMixed_mem)
open StrictExtension
open Nock.NockVMROM.Thm54.PartA12
open Module
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## 1. An abstract accepted memory row family -/

/-- **An accepted memory row family** at basis `b`: `m` rows of base / gathered environments on
which the deployed mixed bucket vanishes, with the first/last masks at base columns `4`/`5`,
orbit alignment of the accumulator role `43`, and one pair of IO coins read at every row. -/
structure MemIORows (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) where
  m : ℕ
  hm : 0 < m
  envK : Fin m → Env K
  envF : Fin m → Env F
  mixed : ∀ i, ∀ g ∈ mixedTransitionGates (F := F) (K := K) b, g.eval (envK i) (envF i) = 0
  first : ∀ i, (envF i).trace 4 = if (i : ℕ) = 0 then 1 else 0
  last : ∀ i, (envF i).trace 5 = if (i : ℕ) + 1 = m then 1 else 0
  next43 : ∀ (i : Fin m) (hi : (i : ℕ) + 1 < m),
    (envK i).traceNext 43 = (envK ⟨(i : ℕ) + 1, hi⟩).trace 43
  coins : FiniteIO.IOCoins K
  coins_eq : ∀ i, memRowCoins (envK i) = coins

namespace MemIORows

variable {b : Basis (Fin 3) F K} (R : MemIORows F K b)

abbrev firstRow : Fin R.m := ⟨0, R.hm⟩
abbrev lastRow : Fin R.m := ⟨R.m - 1, Nat.sub_lt R.hm (by omega)⟩

theorem acc_step_nonlast (i : Fin R.m) (hi : (i : ℕ) + 1 < R.m) :
    (R.envK i).traceNext 43 = (R.envK i).trace 43 + (R.envK i).trace 42 := by
  have hc := R.mixed i _ (accStep_mem b)
  have h5 : (R.envF i).trace 5 = 0 := by rw [R.last i, if_neg (by omega)]
  simp only [accStep, MixedExpr.eval, bcur, CoeffExpr.eval, h5, sub_zero, map_one,
    one_mul, sub_eq_zero] at hc
  exact hc

theorem acc_first : (R.envK R.firstRow).trace 43 = 0 := by
  have h := R.mixed R.firstRow _ (accInit_mem b)
  simp only [accInit, MixedExpr.eval, bcur, CoeffExpr.eval] at h
  rw [R.first, if_pos rfl, map_one, one_mul] at h
  exact h

theorem contrib_eq_term (i : Fin R.m) : (R.envK i).trace 42 = memRowTerm (R.envK i) :=
  contribution_eq_memRowTerm_of_io (R.envK i) (R.envF i)
    (R.mixed i _ (verBool_mem b)) (R.mixed i _ (safeNormalisation_mem b))
    (R.mixed i _ (safeInverse_mem b)) (R.mixed i _ (contribution_mem b))

theorem acc_last_plus_contrib :
    (R.envK R.lastRow).trace 43 + (R.envK R.lastRow).trace 42 = (R.envK R.lastRow).pub 2 := by
  have h := R.mixed R.lastRow _ (accTerminal_mem b)
  have hlast : ((R.lastRow : ℕ) + 1 = R.m) := Nat.sub_add_cancel R.hm
  simp only [accTerminal, MixedExpr.eval, bcur, CoeffExpr.eval] at h
  rw [R.last, if_pos hlast, map_one, one_mul, sub_eq_zero] at h
  exact h

/-- Role `37` is the compression of the row's record at the row coins (the denominator pin). -/
theorem role37_eq_compress (i : Fin R.m) :
    (R.envK i).trace 37 =
      FiniteIO.compress R.coins (memRowRecord10 (R.envK i) (R.envF i)) := by
  rw [← R.coins_eq i]
  exact (denominatorPin_eval_iff _ _).1 (R.mixed i _ (denominatorPinMixed_mem b))

def prefixSum (k : ℕ) : K :=
  ∑ j ∈ Finset.range k, if h : j < R.m then memRowTerm (R.envK ⟨j, h⟩) else 0

theorem prefixSum_succ (k : ℕ) (hk : k < R.m) :
    R.prefixSum (k + 1) = R.prefixSum k + memRowTerm (R.envK ⟨k, hk⟩) := by
  simp [prefixSum, Finset.sum_range_succ, hk]

theorem acc_eq_prefixSum :
    ∀ (k : ℕ) (hk : k < R.m), (R.envK ⟨k, hk⟩).trace 43 = R.prefixSum k := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp only [prefixSum, Finset.range_zero, Finset.sum_empty]
      exact R.acc_first
  | succ k ih =>
      intro hk
      have hk' : k < R.m := by omega
      rw [← R.next43 ⟨k, hk'⟩ hk, R.acc_step_nonlast ⟨k, hk'⟩ hk,
        R.contrib_eq_term ⟨k, hk'⟩, ih hk', R.prefixSum_succ k hk']

/-- The memory terminal public is `Σᵢ ver(i) · denom(i)⁻¹`. -/
theorem requests_eq_sum_memRowTerms :
    (R.envK R.lastRow).pub 2 = ∑ i : Fin R.m, memRowTerm (R.envK i) := by
  have hlast : (R.envK R.lastRow).trace 43 = R.prefixSum (R.m - 1) :=
    R.acc_eq_prefixSum (R.m - 1) _
  rw [← R.acc_last_plus_contrib, R.contrib_eq_term R.lastRow, hlast,
    ← R.prefixSum_succ (R.m - 1) _, Nat.sub_add_cancel R.hm]
  simp only [prefixSum]
  rw [← Fin.sum_univ_eq_sum_range (fun k => if h : k < R.m then
    memRowTerm (R.envK ⟨k, h⟩) else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [i.isLt]

theorem ver_bool (i : Fin R.m) : (R.envK i).trace 39 = 0 ∨ (R.envK i).trace 39 = 1 := by
  have h1 := R.mixed i _ (verBool_mem b)
  simp only [verBool, MixedExpr.eval, mul_eq_zero, sub_eq_zero, Int.cast_one] at h1
  exact h1

theorem denom_ne_zero_of_ver (i : Fin R.m) (hver : (R.envK i).trace 39 = 1) :
    (R.envK i).trace 37 ≠ 0 := by
  have s0 := R.mixed i _ (safeInverse_mem b)
  have s4 := R.mixed i _ (safeNormalisation_mem b)
  simp only [safeInverse, safeNormalisation, MixedExpr.eval, Int.cast_one, hver] at s0 s4
  intro h0
  have h50 : (R.envK i).trace 50 = 0 := by linear_combination s4 + h0
  rw [h50, zero_mul] at s0
  exact one_ne_zero (by linear_combination -s0)

variable [DecidableEq K]

/-- **The committed response list**: the records of the `ver = 1` rows, in row order
. -/
def responses : List (Fin 10 → K) :=
  (List.ofFn fun i : Fin R.m => rowResponses (R.envK i) (R.envF i)).flatten

theorem mem_responses {r : Fin 10 → K} (hr : r ∈ R.responses) :
    ∃ i : Fin R.m, (R.envK i).trace 39 = 1 ∧
      r = OptimizedMemoryHostileAccumulator.rowRecord (R.envK i) (R.envF i) := by
  simp only [responses, List.mem_flatten, List.mem_ofFn] at hr
  obtain ⟨l, ⟨i, rfl⟩, hl⟩ := hr
  simp only [rowResponses, rowResponseTerms] at hl
  split_ifs at hl with hver
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hl
    exact ⟨i, hver, hl⟩
  · simp at hl

theorem sum_memRowTerms_eq_sum_compress :
    (∑ i : Fin R.m, memRowTerm (R.envK i)) =
      (R.responses.map fun r => (FiniteIO.compress R.coins r)⁻¹).sum := by
  rw [responses, List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn,
    List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases R.ver_bool i with h | h
  · simp [memRowTerm, rowResponses, rowResponseTerms, h]
  · have h37 := R.role37_eq_compress i
    rw [← rowRecord_eq_memRowRecord10] at h37
    simp [memRowTerm, rowResponses, rowResponseTerms, h, h37]

/-- **The memory LogUp identity, package-free**: the memory terminal public is the LogUp sum of
the committed responses at the row coins. -/
theorem requests_eq_sum_compress :
    (R.envK R.lastRow).pub 2 =
      (R.responses.map fun r => (FiniteIO.compress R.coins r)⁻¹).sum := by
  rw [R.requests_eq_sum_memRowTerms, R.sum_memRowTerms_eq_sum_compress]

theorem compress_response_ne_zero {r : Fin 10 → K} (hr : r ∈ R.responses) :
    FiniteIO.compress R.coins r ≠ 0 := by
  obtain ⟨i, hver, rfl⟩ := R.mem_responses hr
  have h37 := R.denom_ne_zero_of_ver i hver
  rwa [R.role37_eq_compress i, ← rowRecord_eq_memRowRecord10] at h37

end MemIORows

/-! ## 2. The instance at the twelve-coin memory chip, at any public map (`memoryChipAt12`) -/

section At12

open DeployedChipFamily12

variable [Fintype K] [Fintype F] [DecidableEq K]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (hinj : Function.Injective nodes)
  (b : Basis (Fin 3) F K) (pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
  (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
  (c : OptimizedProductionChallengeTuple12 K F) (kMem : ℕ)

abbrev src12 : FixedPreprocessingRAP F :=
  namedSourceMemoryRAP12 hn nodes b (memoryChalValOfTuple12 b c) pubVal orbit kMem

/-- The source trace (first `182` columns) of a twelve-coin memory trace. -/
abbrev proj12 (Q : Fin (memoryChipAt12 hn nodes b pubVal orbit c kMem).rap.w → F[X]) :
    Fin (src12 hn nodes b pubVal orbit c kMem).rap.w → F[X] :=
  RAPPadding.projectTrace (src12 hn nodes b pubVal orbit c kMem).rap
    (RAPPadding.firstRoundExtra (src12 hn nodes b pubVal orbit c kMem).rap
      (src12 hn nodes b pubVal orbit c kMem).rounds_pos (RAPPadding.memoryResidualColumns 3)) Q

/-- Base row environment of a twelve-coin memory trace. -/
abbrev envF12 (Q : Fin (memoryChipAt12 hn nodes b pubVal orbit c kMem).rap.w → F[X]) (i : Fin n) :
    Env F :=
  envOfTrace (proj12 hn nodes b pubVal orbit c kMem Q) orbit.ω (nodes i)
    (memoryChalValOfTuple12 b c) pubVal

/-- Gathered row environment, with the challenge slots read through the walk swap `3 ↔ 9`
(the deployed bucket's view of the twelve-coin chip). -/
abbrev envK12 (Q : Fin (memoryChipAt12 hn nodes b pubVal orbit c kMem).rap.w → F[X]) (i : Fin n) :
    Env K :=
  { gatherEnv b memoryCol0 (envF12 hn nodes b pubVal orbit c kMem Q i) with
    chal := fun j => (gatherEnv b memoryCol0 (envF12 hn nodes b pubVal orbit c kMem Q i)).chal
      (walkSlotSwap j) }

theorem envK12_chal (Q : Fin (memoryChipAt12 hn nodes b pubVal orbit c kMem).rap.w → F[X])
    (i : Fin n) (q : ℕ) (hq : q < 10) (h3 : q ≠ 3) (h9 : q ≠ 9) :
    (envK12 hn nodes b pubVal orbit c kMem Q i).chal q = memoryKOfTuple12 c q := by
  have hs : walkSlotSwap q = q := by simp [walkSlotSwap, h3, h9]
  simp only [hs, gatherEnv, memoryCol0, envOfTrace]
  have hcoord : ∀ k : Fin 3, memoryChalValOfTuple12 b c (6 + 3 * q + (k : ℕ)) =
      coord b (memoryKOfTuple12 c q) k := fun k =>
    memoryChalValOfTuple12_slot b c ⟨q, hq⟩ k
  simp_rw [hcoord]
  exact reconstruct_coord b (memoryKOfTuple12 c q)

/-- The memory terminal public gathered at any row is the public map's block `12..14`. -/
theorem envK12_pub2 (Q : Fin (memoryChipAt12 hn nodes b pubVal orbit c kMem).rap.w → F[X])
    (i : Fin n) :
    (envK12 hn nodes b pubVal orbit c kMem Q i).pub 2 = ∑ k : Fin 3, pubVal (12 + (k : ℕ)) • b k := by
  simp only [gatherEnv, memoryCol0, envOfTrace]

include hinj hadj in
/-- **The row family of an accepted twelve-coin memory trace**, at any nodes / basis / orbit /
public map / `kMem` and any tuple `c`.  The IO coins are `c.2.1` (memory slots `4`/`5`). -/
def memRows12 (Q : Fin (memoryChipAt12 hn nodes b pubVal orbit c kMem).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (memoryChipAt12 hn nodes b pubVal orbit c kMem) Q) :
    MemIORows F K b where
  m := n
  hm := hn
  envK := envK12 hn nodes b pubVal orbit c kMem Q
  envF := envF12 hn nodes b pubVal orbit c kMem Q
  mixed := fun i g hg => by
    have hs := (RAPPadding.padFixedPreprocessing_satisfies_iff _ _ _ Q).1 hsat
    have hraw := hs.1
    change (expandChipTail (memorySourceTemplate12 b) b (memoryChalValOfTuple12 b c) pubVal orbit
      (rowNodeSet nodes) 2).Satisfies _ at hraw
    erw [expandChipTail_satisfies_iff_language] at hraw
    have hrow := (hraw (nodes i) (by simp [rowNodeSet])).2.2.2
    rw [memorySourceTemplate12_col0] at hrow
    have hg' := hrow (renameChal walkSlotSwap g)
      (by
        show renameChal walkSlotSwap g ∈ mixedTransitionGates12 (F := F) (K := K) b
        rw [mixedTransitionGates12_eq_rename]; exact List.mem_map_of_mem hg)
    rw [eval_renameChal] at hg'
    exact hg'
  first := fun i => by
    have hs := (RAPPadding.padFixedPreprocessing_satisfies_iff _ _ _ Q).1 hsat
    have h0 := hs.2 ⟨0, by change 0 < 4; norm_num⟩
    have h4 : 4 < (src12 hn nodes b pubVal orbit c kMem).rap.w := by show 4 < 182; norm_num
    have hc0 : (src12 hn nodes b pubVal orbit c kMem).preprocessingColumn
        ⟨0, by change 0 < 4; norm_num⟩ = ⟨4, h4⟩ := rfl
    rw [hc0] at h0
    show (envOfTrace (proj12 hn nodes b pubVal orbit c kMem Q) orbit.ω (nodes i)
      (memoryChalValOfTuple12 b c) pubVal).trace 4 = _
    simp only [envOfTrace]
    rw [dif_pos h4]
    rw [show (proj12 hn nodes b pubVal orbit c kMem Q) ⟨4, h4⟩ =
      OptimizedMemoryCanonicalTrace.firstRowMask nodes from h0,
      OptimizedMemoryCanonicalTrace.firstRowMask_eval _ hinj]
  last := fun i => by
    have hs := (RAPPadding.padFixedPreprocessing_satisfies_iff _ _ _ Q).1 hsat
    have h1 := hs.2 ⟨1, by change 1 < 4; norm_num⟩
    have h5 : 5 < (src12 hn nodes b pubVal orbit c kMem).rap.w := by show 5 < 182; norm_num
    have hc1 : (src12 hn nodes b pubVal orbit c kMem).preprocessingColumn
        ⟨1, by change 1 < 4; norm_num⟩ = ⟨5, h5⟩ := rfl
    rw [hc1] at h1
    show (envOfTrace (proj12 hn nodes b pubVal orbit c kMem Q) orbit.ω (nodes i)
      (memoryChalValOfTuple12 b c) pubVal).trace 5 = _
    simp only [envOfTrace]
    rw [dif_pos h5]
    rw [show (proj12 hn nodes b pubVal orbit c kMem Q) ⟨5, h5⟩ =
      OptimizedMemoryCanonicalTrace.lastRowMask nodes from h1,
      OptimizedMemoryCanonicalTrace.lastRowMask_eval _ hinj]
  next43 := fun i hi => by
    show (∑ k : Fin 3, (envF12 hn nodes b pubVal orbit c kMem Q i).traceNext (6 + 3 * 43 + (k : ℕ)) • b k) =
      ∑ k : Fin 3, (envF12 hn nodes b pubVal orbit c kMem Q ⟨(i : ℕ) + 1, hi⟩).trace (6 + 3 * 43 + (k : ℕ)) • b k
    refine Finset.sum_congr rfl fun k _ => ?_
    have hlt : 6 + 3 * 43 + (k : ℕ) < (src12 hn nodes b pubVal orbit c kMem).rap.w := by
      show 6 + 3 * 43 + (k : ℕ) < 182; have := k.isLt; omega
    simp only [envF12, envOfTrace, dif_pos hlt]
    rw [hadj i hi]
  coins := ⟨c.2.1.1, c.2.1.2⟩
  coins_eq := fun i => by
    simp only [memRowCoins]
    rw [envK12_chal hn nodes b pubVal orbit c kMem Q i 4 (by norm_num) (by norm_num) (by norm_num),
      envK12_chal hn nodes b pubVal orbit c kMem Q i 5 (by norm_num) (by norm_num) (by norm_num)]
    rfl

end At12

end

end Nock.NockVMROM.Thm54.SVIO
