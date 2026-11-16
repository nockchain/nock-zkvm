import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.RedTeam.Batch272Thm54UnanchoredIntermediateEndpoints

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!

Paper re-read
at source: the paper (`RAP.Satisfies`: every constraint at every `x ∈ H`), `:1431`
(`intermediate` anchored at both ends, prose), `:1487` (`2·e` gates of degree `1`, `2·e` of degree
`3`), `:526-537`, `:577-599`, `:603-613`.

## A. Wrong layer? (attack 1) — the anchors sit on PREPROCESSED masks

`hostile_intermediate_anchored` reads the masks through the mirrors `47`/`48`, which
`firstMaskMixed`/`lastMaskMixed` bind to base columns `4`/`5`.  Those columns are not
prover-chosen: `RAP.SatisfiesWithPreprocessing` (`FixedPreprocessingRAP.BindsPreprocessing`)
fixes them to `firstRowMask`/`lastRowMask memoryNodes` as **polynomials**.
* `firstMask_column_is_preprocessing`: at any accepted trace the projected column `4` **is** the
  Lagrange first-row selector of the package's nodes.
* `anchor_void_without_mask`: with mirror `47 = 0` the anchor gate is `0` at any environment —
  the attack the anchors would be exposed to if the mask were free…
* `hostile_zero_mask_rejected`: …and it is unavailable: a trace whose column `4` is the zero
  polynomial (or any polynomial with `≠ 1` at the first node, `hostile_mask_ne_one_rejected`) is
  REJECTED by `P.memoryChip`.  No acceptance structure, no fold hypothesis.

## B. Non-constant perturbations (attack 2) — `ipre`/`icur` are DETERMINED row by row

Here the general statement, at the consumed chip, under
the fold-collision exclusion at every row (the priced fold event, exactly the hypothesis
`hostile_requests_eq_sum_memRowTerms` carries):
* `delta_at`: `icur(i) − ipre(i) = (sel_read(i) − sel_verify(i)) · g(i)` (`hostileDelta`; roles
  `53`, `54`, `29`) from the `Δ` class and the selector-sum source — **no one-hot needed**, the
  merged class is linear in `icur − ipre` with coefficient `Σ sel = 1`;
* `delta_pole_witness`: wherever `hostileDelta ≠ 0`, `pole · g = 1` (class `24` and the selector
  booleanities) — so the step is `± (RLC^γ(record) − β)⁻¹`, the paper's `:2123`;
* `intermediate_chain_at`, `next_ipre`: `icur(i) = ipre(i+1)` off the last row (`chainMixed`
  under the fixed last mask);
* `ipre_eq_deltaPrefix`, `icur_eq_deltaPrefix`: `ipre(m) = Σ_{k<m} Δ_k`, `icur(m) = Σ_{k≤m} Δ_k`
  (anchor `ipre(0) = 0` + chain + step);
* `hostile_intermediate_telescopes`: `Σ_i Δ_i = 0` (the terminal anchor) — the paper's global
  check at `:1431` as a compiled consequence of acceptance;
* `intermediate_determined`: two accepted traces agreeing on roles `29`/`53`/`54` at every row
  agree on `ipre`/`icur` at every row.  **No perturbation of `ipre`/`icur` alone — constant or
  not — survives**; the only freedom left is in the inputs of `Δ` (the selectors, which are
  one-hot-bound to the base state, and `g`, pinned to `pole⁻¹` wherever it is read).

## C. The count (attack 3)

* `degreeThreeEndpoints_degrees`: the bucket is `[1, 2, 2, 2]` under `Expr.degree` (the forest
  count pin `41`, the walk terminal `48 · 33`, the two anchors) — the anchors are degree `2` because the mask mirror is a trace variable; `:1487`'s "`2·e` of degree `1`"
  prices the mask as a verifier constant.  Disclosed as `memoryDegreeOneGates 0`/
  `memoryDegreeThreeGates 4·e` against the paper's `…Paper 2·e/2·e`, totals equal
  (`endpoint_buckets_disclosed`); `M.rap.s = 113` unmoved at every package (`memory_s_unmoved`).

## D. `hostile_LIO` off the honest trace (attack 4)

* `padPerturbed P Qm`: the final memory trace with residual column `182` (the first of the
  `RAPPadding.memoryResidualColumns 3 = 25` padding columns the source projection drops) moved
  by `1`.  `padPerturbed_ne`: a different trace; `memorySourceTrace_padPerturbed`: the same
  projected source trace.
* `acceptance_padPerturbed`: **the consumed acceptance is preserved** — every `Qm`-dependent
  field reads the projection only.
* `hostileResponses_padPerturbed`: the hostile response list is unchanged.
* `concrete73_hostile_LIO_padPerturbed`: `hostile_LIO` at F73 with the real
  `concrete_production_acceptance` at the pair `(concreteComputeTrace, padPerturbed
  concreteMemoryTrace)` — a **non-honest accepted pair** (`padPerturbed_concrete_ne_canonical`)
  at which every hypothesis of `hostile_LIO` holds.  So the hypothesis set does not force the
  trace honest.  (Honest modulo padding: the hostile lists coincide with the honest ones; a
  source-level non-honest accepted trace would need a dead source column — roles `45`/`46`/`49`
  are dead, `Batch272.role46_49_anywhere` — and is left to W2 stage 2.)
* `hchar` is used exactly once in the `LY` route: `activeMask_bool` (compute selectors → boolean
  masks); `hostile_LIO_core` carries `hbool` instead (`hchar_only_feeds_hbool`).

## E. The lists (attack 5)

* `LIO_perm_invariant`: `IO.LIO` is order-insensitive in both lists (`requests.Perm responses`,
  `Nock/IO.lean:60`), so the chips' row orders are immaterial — the paper's `:597`
  `requests = responses` is a multiset statement.
* `mem_rowRequests_iff`: a record enters a compute row's request list **iff** its slot's
  activity mask is `1`; `masked_slot_not_emitted`: a slot with mask `0` and garbage record is not
  listed.  `activeMask_slot0_always_one`: slot `0` is always active (`sampledActive 0 = 1`, the
  always-on record of the paper).

## F. The coins (attack 6)

* `compute_chipCoins_trace_free`: `OptimizedComputeHostileAccumulator.chipCoins P` takes no
  trace — it is two package challenges.
Moving the event was the `LY` draft's W6.1 item (ii) — done.

## G. Hygiene (attack 7)

* `#print axioms` on every named theorem of `LX`/`LY` and of this file.
-/

namespace Nock.RedTeam.Batch274

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.MemoryPaperFactorization
open Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## A. The anchors sit on preprocessed masks -/

section Masks

variable (Qm : Fin P.memoryChip.rap.w → F[X])

theorem sourceOf_w : (sourceOf P).rap.w = 182 :=
  (sourceMemoryRAP_fingerprint P.optimized.basis P.optimized.memoryChallenge
    P.optimized.memoryPublic P.optimized.orbit (rowNodeSet P.optimized.memoryNodes)).1

theorem four_lt_w : 4 < (sourceOf P).rap.w := by rw [sourceOf_w]; norm_num

/-- **Base column `4` of any accepted trace is the preprocessing first-row selector, as a
polynomial** — `BindsPreprocessing`, the second conjunct of `SatisfiesWithPreprocessing`. -/
theorem firstMask_column_is_preprocessing (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm) :
    projOf P Qm ⟨4, four_lt_w P⟩ =
      OptimizedMemoryCanonicalTrace.firstRowMask P.optimized.memoryNodes := by
  have hbind := (source_sat P Qm hsat).2
  have h0 := hbind ⟨0, by change 0 < 4; norm_num⟩
  have hc0 : (sourceOf P).preprocessingColumn ⟨0, by change 0 < 4; norm_num⟩ =
      ⟨4, four_lt_w P⟩ := rfl
  rw [hc0] at h0
  exact h0

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
/-- **Without the binding the anchor is void**: at any environment with mirror `47 = 0` the
gate `47 · 27` vanishes whatever `ipre` is. -/
theorem anchor_void_without_mask (env : Env K) (h47 : env.trace 47 = 0) :
    intermediateInitGate.eval env = 0 := by
  simp [intermediateInitGate, extVar, Expr.eval, h47]

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
theorem terminal_anchor_void_without_mask (env : Env K) (h48 : env.trace 48 = 0) :
    intermediateTerminalGate.eval env = 0 := by
  simp [intermediateTerminalGate, extVar, Expr.eval, h48]

/-- **A trace whose base column `4` is not `1` at the first node is REJECTED** — so the prover
cannot zero the mask to void the anchor. -/
theorem hostile_mask_ne_one_rejected
    (hne : (projOf P Qm ⟨4, four_lt_w P⟩).eval (P.optimized.memoryNodes (firstRow P)) ≠ 1) :
    ¬ RAP.SatisfiesWithPreprocessing P.memoryChip Qm := by
  intro hsat
  have h := (masks_at P Qm hsat (firstRow P)).1
  simp only [rowEnvF, envOfTrace, dif_pos (four_lt_w P)] at h
  exact hne (by simpa using h)

/-- The zero column in particular. -/
theorem hostile_zero_mask_rejected (hz : projOf P Qm ⟨4, four_lt_w P⟩ = 0) :
    ¬ RAP.SatisfiesWithPreprocessing P.memoryChip Qm := by
  apply hostile_mask_ne_one_rejected
  rw [hz]
  simp

/-- At the first row of any accepted trace the preprocessing first-mask is `1`, so the
committed mixed anchor `first · ipre` **is** `ipre(0)`. -/
theorem anchor_is_ipre_at_first_row (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm) :
    (OptimizedMemoryGateBasis.intermediateInit (F := F)).eval
        (rowEnvK P Qm (firstRow P)) (rowEnvF P Qm (firstRow P)) =
      (rowEnvK P Qm (firstRow P)).trace 27 := by
  have h4 : (rowEnvF P Qm (firstRow P)).trace 4 = 1 := by
    rw [(masks_at P Qm hsat (firstRow P)).1, if_pos rfl]
  simp [OptimizedMemoryGateBasis.intermediateInit, MixedExpr.eval, bcur, CoeffExpr.eval, h4]

end Masks

/-! ## B. `ipre`/`icur` are determined row by row -/

section Telescoping

/-- The hostile per-row step of the `intermediate` aggregator: `(sel_read − sel_verify) · g`
(roles `53`, `54` are the mirrors of base selectors `2`/`3`; role `29` is the LogUp witness
`g`, memory-table column `33` under `memorySubst`). -/
def hostileDelta (env : Env K) : K := (env.trace 53 - env.trace 54) * env.trace 29

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
theorem deltaSource_mem :
    deltaSource (K := ZMod 31) ∈ transitionSources (K := ZMod 31) := by
  set_option maxRecDepth 100000 in decide

/-- The `pole · g = 1` class (`24`) under `memorySubst`. -/
def poleWitnessSource {K : Type} [Field K] : Expr :=
  (MemoryFactorizationScope.mergedGate (K := K) 24).subst memorySubst

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
theorem poleWitnessSource_mem :
    (MemoryFactorizationScope.mergedGate (K := ZMod 31) 24).subst memorySubst ∈
      transitionSources (K := ZMod 31) := by
  set_option maxRecDepth 100000 in decide

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
theorem selectorSum_mem : memSvOneHotExpr.subst memorySubst ∈ transitionSources (K := K) := by
  simp only [transitionSources, List.mem_append]
  left; left; left; left
  refine List.mem_map.mpr ⟨_, ?_, rfl⟩
  simp [mergedMemoryConstraints, memSvExprs]

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
theorem selectorBool_mem (j : MemoryTable.MState) :
    (memSvBoolExprF (mopCol j)).subst memorySubst ∈ transitionSources (K := K) := by
  simp only [transitionSources, List.mem_append]
  left; left; left; left
  refine List.mem_map.mpr ⟨_, ?_, rfl⟩
  simp [mergedMemoryConstraints, memSvExprs, memSvBoolExprs, mem_allMStates]

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
/-- **The `Δ` class is linear in `icur − ipre` with coefficient `Σ sel`**: with the selector-sum
source it gives `icur − ipre = hostileDelta` at any environment, one-hot or not. -/
theorem delta_of_sources (env : Env K) (h : (deltaSource (K := K)).eval env = 0)
    (hsum : (memSvOneHotExpr.subst memorySubst).eval env = 0) :
    env.trace 28 - env.trace 27 = hostileDelta env := by
  simp only [deltaSource, MemoryFactorizationScope.mergedGate, gateByM, mopCol,
    memQuantity_23_decompose, memQuantity_23_halt, memQuantity_23_read, memQuantity_23_verify,
    Expr.subst, Expr.eval, memorySubst, Reified.tc, extVar] at h
  simp only [memSvOneHotExpr, Expr.subst, Expr.eval, memorySubst, Reified.tc, extVar] at hsum
  norm_num [Expr.eval] at h hsum
  unfold hostileDelta
  linear_combination h - (env.trace 28 - env.trace 27) * hsum

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
theorem poleWitness_of_sources (env : Env K) (h : (poleWitnessSource (K := K)).eval env = 0) :
    (env.trace 53 + env.trace 54) *
      ((Expr.subst memorySubst poleExpr).eval env * env.trace 29 - 1) = 0 := by
  simp only [poleWitnessSource, MemoryFactorizationScope.mergedGate, gateByM, mopCol,
    memQuantity_24_decompose, memQuantity_24_halt, memQuantity_24_read, memQuantity_24_verify,
    Expr.subst, Expr.eval, memorySubst, Reified.tc, extVar] at h
  norm_num [Expr.eval] at h
  linear_combination h

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
theorem selectorBool_of_source (env : Env K) (j : MemoryTable.MState)
    (h : ((memSvBoolExprF (mopCol j)).subst memorySubst).eval env = 0) :
    env.trace (51 + mopCol j) = 0 ∨ env.trace (51 + mopCol j) = 1 := by
  have hlt : mopCol j < 4 := by cases j <;> decide
  simp only [memSvBoolExprF, Expr.subst, Expr.eval, memorySubst, Reified.tc, extVar,
    if_pos hlt] at h
  norm_num [Expr.eval] at h
  rcases h with h | h
  · exact Or.inl h
  · right; linear_combination -h

variable (Qm : Fin P.memoryChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
include hsat

/-- **The step at the consumed chip** (W2 stage 2): the paper aggregator
`pole · (icur − ipre) − (sel_read − sel_verify)` vanishes at every row.  The pre-swap
`sources_at` discharge of class `23` was last statable. -/
theorem delta_at (i : Fin (rows P)) :
    (OptimizedMemoryGateBasis.paperAggregator (F := F)).eval (rowEnvK P Qm i) (rowEnvF P Qm i) = 0 :=
  mixed_at P Qm hsat i _ (by
    simp [mixedTransitionGates, OptimizedMemoryGateBasis.paperKGates,
      OptimizedMemoryGateBasis.paperKGatesCore, OptimizedMemoryGateBasis.rapMemGates])

/-- **Wherever the folded class-`24` witness vanishes and the step is nonzero, `pole · g = 1`.**
Previously RAP-discharged via `sources_at`. -/
theorem delta_pole_witness (i : Fin (rows P))
    (h24 : (poleWitnessSource (K := K)).eval (rowEnvK P Qm i) = 0)
    (hread : ((memSvBoolExprF (mopCol .read_root)).subst memorySubst).eval (rowEnvK P Qm i) = 0)
    (hver : ((memSvBoolExprF (mopCol .verify_child)).subst memorySubst).eval (rowEnvK P Qm i) = 0)
    (hne : hostileDelta (rowEnvK P Qm i) ≠ 0) :
    (Expr.subst memorySubst poleExpr).eval (rowEnvK P Qm i) * (rowEnvK P Qm i).trace 29 = 1 := by
  have h24' := poleWitness_of_sources _ h24
  have h53 := selectorBool_of_source _ .read_root hread
  have h54 := selectorBool_of_source _ .verify_child hver
  simp only [mopCol] at h53 h54
  rcases mul_eq_zero.mp h24' with h0 | h0
  · exfalso
    apply hne
    unfold hostileDelta
    rcases h53 with h53 | h53 <;> rcases h54 with h54 | h54
    · simp [h53, h54]
    · rw [h53, h54] at h0; exfalso; exact zero_ne_one (by linear_combination -h0)
    · rw [h53, h54] at h0; exfalso; exact zero_ne_one (by linear_combination -h0)
    · simp [h53, h54]
  · linear_combination h0

omit [Fintype K] [DecidableEq K] [CharP K (ringChar K)] hsat in
theorem chainMixed_mem (b : Basis (Fin 3) F K) :
    chainMixed (F := F) ∈ mixedTransitionGates (K := K) b := by
  simp [mixedTransitionGates, OptimizedMemoryGateBasis.paperKGates,
    OptimizedMemoryGateBasis.paperKGatesCore, OptimizedMemoryGateBasis.intermediateChain]

/-- The `intermediate` chain off the last row: `icur(i) = ipre(i+1)` (`chainMixed` under the
fixed last mask). -/
theorem intermediate_chain_at (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnvK P Qm i).trace 28 = (rowEnvK P Qm i).traceNext 27 := by
  have hc := (row_parts P Qm hsat i).2.2.2 _ (chainMixed_mem P.optimized.basis)
  have h5 : (rowEnvF P Qm i).trace 5 = 0 := by
    rw [(masks_at P Qm hsat i).2, if_neg (by omega)]
  simp only [chainMixed, MixedExpr.eval, bcur, CoeffExpr.eval, h5, sub_zero, map_one,
    one_mul, sub_eq_zero] at hc
  exact hc

omit hsat in
/-- Orbit alignment for role `27`: the next-row read at row `i` is row `i+1`'s `ipre`. -/
theorem next_ipre (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnvK P Qm i).traceNext 27 = (rowEnvK P Qm ⟨(i : ℕ) + 1, hi⟩).trace 27 := by
  have hadj := P.optimized.memoryOrbitAligned i hi
  simp only [rowEnvK, gatherEnv, memoryCol0]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hlt : 6 + 3 * 27 + (k : ℕ) < (sourceOf P).rap.w := by rw [sourceOf_w]; omega
  simp only [rowEnvF, envOfTrace, dif_pos hlt]
  rw [hadj, mul_comm]

omit hsat in
/-- `Σ_{k<m} hostileDelta(k)`. -/
def deltaPrefix (m : ℕ) : K :=
  ∑ k ∈ Finset.range m, if h : k < rows P then hostileDelta (rowEnvK P Qm ⟨k, h⟩) else 0

omit hsat in
theorem deltaPrefix_succ (m : ℕ) (hm : m < rows P) :
    deltaPrefix P Qm (m + 1) = deltaPrefix P Qm m + hostileDelta (rowEnvK P Qm ⟨m, hm⟩) := by
  simp [deltaPrefix, Finset.sum_range_succ, hm]

/-- **`ipre(m) = Σ_{k<m} Δ_k`** under the folded class-`23` identity (previously RAP-discharged
via `sources_at`).  The live committed step is `delta_at` / `paperAggregator`. -/
theorem ipre_eq_deltaPrefix
    (hΔ : ∀ i : Fin (rows P),
      (rowEnvK P Qm i).trace 28 - (rowEnvK P Qm i).trace 27 = hostileDelta (rowEnvK P Qm i)) :
    ∀ (m : ℕ) (hm : m < rows P), (rowEnvK P Qm ⟨m, hm⟩).trace 27 = deltaPrefix P Qm m := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [deltaPrefix, Finset.range_zero, Finset.sum_empty]
      exact (hostile_intermediate_anchored P Qm hsat).1
  | succ m ih =>
      intro hm
      have hm' : m < rows P := by omega
      rw [← next_ipre P Qm ⟨m, hm'⟩ hm, ← intermediate_chain_at P Qm hsat ⟨m, hm'⟩ hm,
        deltaPrefix_succ P Qm m hm', ← ih hm', ← hΔ ⟨m, hm'⟩]
      ring

/-- **`icur(m) = Σ_{k≤m} Δ_k`** under the folded class-`23` identity. -/
theorem icur_eq_deltaPrefix
    (hΔ : ∀ i : Fin (rows P),
      (rowEnvK P Qm i).trace 28 - (rowEnvK P Qm i).trace 27 = hostileDelta (rowEnvK P Qm i)) :
    ∀ (m : ℕ) (hm : m < rows P), (rowEnvK P Qm ⟨m, hm⟩).trace 28 = deltaPrefix P Qm (m + 1) := by
  intro m hm
  rw [deltaPrefix_succ P Qm m hm, ← ipre_eq_deltaPrefix P Qm hsat hΔ m hm, ← hΔ ⟨m, hm⟩]
  ring

/-- **The paper's global check under the folded class-`23` identity:
`Σ_i Δ_i = 0`.**  Live: `hostile_intermediate_anchored`. -/
theorem hostile_intermediate_telescopes
    (hΔ : ∀ i : Fin (rows P),
      (rowEnvK P Qm i).trace 28 - (rowEnvK P Qm i).trace 27 = hostileDelta (rowEnvK P Qm i)) :
    ∑ i : Fin (rows P), hostileDelta (rowEnvK P Qm i) = 0 := by
  have hpos := P.optimized.family.problem.cfg.memRows_pos
  have hlast : (rowEnvK P Qm (lastRow P)).trace 28 = deltaPrefix P Qm (rows P - 1 + 1) :=
    icur_eq_deltaPrefix P Qm hsat hΔ (rows P - 1) _
  rw [(hostile_intermediate_anchored P Qm hsat).2, Nat.sub_add_cancel hpos] at hlast
  rw [hlast]
  simp only [deltaPrefix]
  rw [← Fin.sum_univ_eq_sum_range (fun k => if h : k < rows P then
    hostileDelta (rowEnvK P Qm ⟨k, h⟩) else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [i.isLt]

end Telescoping

/-- **No perturbation of `ipre`/`icur` alone survives, constant or not**: two accepted traces
that agree on roles `29`, `53`, `54` at every row agree on `ipre`/`icur` at every row.  (Under
the fold exclusion at every row of both, the hypothesis every hostile reading of the folded
sources carries.) -/
theorem intermediate_determined (Qm Qm' : Fin P.memoryChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
    (hsat' : RAP.SatisfiesWithPreprocessing P.memoryChip Qm')
    (hΔ : ∀ i : Fin (rows P),
      (rowEnvK P Qm i).trace 28 - (rowEnvK P Qm i).trace 27 = hostileDelta (rowEnvK P Qm i))
    (hΔ' : ∀ i : Fin (rows P),
      (rowEnvK P Qm' i).trace 28 - (rowEnvK P Qm' i).trace 27 = hostileDelta (rowEnvK P Qm' i))
    (hagree : ∀ i : Fin (rows P),
      (rowEnvK P Qm' i).trace 29 = (rowEnvK P Qm i).trace 29 ∧
      (rowEnvK P Qm' i).trace 53 = (rowEnvK P Qm i).trace 53 ∧
      (rowEnvK P Qm' i).trace 54 = (rowEnvK P Qm i).trace 54) :
    ∀ i : Fin (rows P),
      (rowEnvK P Qm' i).trace 27 = (rowEnvK P Qm i).trace 27 ∧
      (rowEnvK P Qm' i).trace 28 = (rowEnvK P Qm i).trace 28 := by
  have hD : ∀ i : Fin (rows P), hostileDelta (rowEnvK P Qm' i) = hostileDelta (rowEnvK P Qm i) := by
    intro i
    obtain ⟨h29, h53, h54⟩ := hagree i
    simp only [hostileDelta, h29, h53, h54]
  have hpre : ∀ m, deltaPrefix P Qm' m = deltaPrefix P Qm m := by
    intro m
    simp only [deltaPrefix]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with h
    · exact hD ⟨k, h⟩
    · rfl
  intro i
  constructor
  · rw [ipre_eq_deltaPrefix P Qm' hsat' hΔ' i i.isLt, ipre_eq_deltaPrefix P Qm hsat hΔ i i.isLt,
      hpre]
  · rw [icur_eq_deltaPrefix P Qm' hsat' hΔ' i i.isLt, icur_eq_deltaPrefix P Qm hsat hΔ i i.isLt,
      hpre]

/-! ## C. The count -/

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
/-- The degree-`3` endpoint bucket under `Expr.degree`: the two forest endpoints and the two
anchors at degree `2`. -/
theorem degreeThreeEndpoints_degrees :
    degreeThreeEndpoints = [] := rfl

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
theorem endpoint_buckets_disclosed (e : ℕ) :
    Thm54Resources.memoryDegreeOneGates e = 0 ∧
      Thm54Resources.memoryDegreeThreeGates e = 0 ∧
      Thm54Resources.memoryDegreeOneGatesPaper e = 2 * e ∧
      Thm54Resources.memoryDegreeThreeGatesPaper e = 2 * e := by
  exact ⟨rfl, rfl, rfl, rfl⟩


theorem memory_s_unmoved : P.memoryChip.rap.s = 156 ∧ P.memoryChip.rap.w = 205 :=
  ⟨(finalMemoryRAP_fingerprint P.optimized.family.problem.cfg.memRows_pos P.optimized.memoryNodes
      P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit
      P.optimized.family.problem.cfg.kMem).2.1,
    (finalMemoryRAP_fingerprint P.optimized.family.problem.cfg.memRows_pos P.optimized.memoryNodes
      P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit
      P.optimized.family.problem.cfg.kMem).1⟩

/-! ## D. `hostile_LIO` at a non-honest accepted pair -/

section Padding

variable (Qm : Fin P.memoryChip.rap.w → F[X])

theorem memoryChip_w : P.memoryChip.rap.w = 205 := (memory_s_unmoved P).2

/-- `Qm` with residual column `182` (the first padding column; the source projection keeps
columns `< 182`, form R `C'` lives at `177..179`, the 29th's `atom` at `180`, the 31st's `reqIdx`
at `181`) moved by the constant polynomial `1`.  Before the 29th the first padding column was
`180`; before the 31st, `181`. -/
def padPerturbed : Fin P.memoryChip.rap.w → F[X] :=
  fun c => if (c : ℕ) = 182 then Qm c + 1 else Qm c

theorem padPerturbed_ne : padPerturbed P Qm ≠ Qm := by
  intro h
  have hc : (182 : ℕ) < P.memoryChip.rap.w := by rw [memoryChip_w]; norm_num
  have := congrFun h ⟨182, hc⟩
  simp [padPerturbed] at this

/-- The projected source trace does not see the padding column. -/
theorem memorySourceTrace_padPerturbed :
    P.memorySourceTrace (padPerturbed P Qm) = P.memorySourceTrace Qm := by
  funext i
  simp only [OptimizedFullStrictNockVMROMPackage.memorySourceTrace, RAPPadding.projectTrace,
    padPerturbed]
  split_ifs with h
  · exfalso
    have hi := i.isLt
    have h2 : (i : ℕ) = 182 := h
    omega
  · rfl

theorem memoryBaseEnv_padPerturbed (i : Fin (rows P)) :
    P.memoryBaseEnv (padPerturbed P Qm) i = P.memoryBaseEnv Qm i := by
  simp only [OptimizedFullStrictNockVMROMPackage.memoryBaseEnv, memorySourceTrace_padPerturbed]

theorem memorySourceEnv_padPerturbed (i : Fin (rows P)) :
    P.memorySourceEnv (padPerturbed P Qm) i = P.memorySourceEnv Qm i := by
  simp only [OptimizedFullStrictNockVMROMPackage.memorySourceEnv, memoryBaseEnv_padPerturbed]

theorem rowEnvK_padPerturbed (i : Fin (rows P)) :
    rowEnvK P (padPerturbed P Qm) i = rowEnvK P Qm i := by
  rw [Batch271.rowEnvK_eq_memorySourceEnv, Batch271.rowEnvK_eq_memorySourceEnv,
    memorySourceEnv_padPerturbed]

theorem projOf_padPerturbed : projOf P (padPerturbed P Qm) = projOf P Qm :=
  memorySourceTrace_padPerturbed P Qm

/-- The consumed chip accepts the padded trace iff it accepts `Qm`. -/
theorem memory_satisfies_padPerturbed :
    RAP.SatisfiesWithPreprocessing P.memoryChip (padPerturbed P Qm) ↔
      RAP.SatisfiesWithPreprocessing P.memoryChip Qm := by
  rw [final_satisfies_iff_source P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic
    P.optimized.orbit P.optimized.family.problem.cfg.kMem,
    final_satisfies_iff_source P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic
    P.optimized.orbit P.optimized.family.problem.cfg.kMem]
  change RAP.SatisfiesWithPreprocessing (sourceOf P) (projOf P (padPerturbed P Qm)) ↔
    RAP.SatisfiesWithPreprocessing (sourceOf P) (projOf P Qm)
  rw [projOf_padPerturbed]

/-- **The hostile response list is unchanged by the padding perturbation.** -/
theorem hostileResponses_padPerturbed :
    hostileResponses P (padPerturbed P Qm) = hostileResponses P Qm := by
  simp only [hostileResponses, rowEnvK_padPerturbed, rowEnvF, projOf_padPerturbed]

variable [Fintype F] [DecidableEq F]
  (Qc : Fin P.computeChip.rap.w → F[X])
  (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)

/-- **The consumed acceptance is preserved by the padding perturbation** — every `Qm`-dependent
field reads the projected source trace only. -/
theorem acceptance_padPerturbed (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    P.OptimizedHistoricalAcceptanceAt Qc (padPerturbed P Qm) c where
  p8 := hacc.p8
  same_problem := hacc.same_problem
  sampled_io_coins := hacc.sampled_io_coins
  memory_sampled_coins := by
    intro i
    rw [memorySourceEnv_padPerturbed]
    exact hacc.memory_sampled_coins i
  memory_intermediate_pole := by
    intro i
    rw [memorySourceEnv_padPerturbed]
    exact hacc.memory_intermediate_pole i
  compute_satisfies := hacc.compute_satisfies
  memory_satisfies := (memory_satisfies_padPerturbed P Qm).mpr hacc.memory_satisfies

omit [Fintype F] [DecidableEq F] in
/-- The hostile records at the padded pair are those at the original pair. -/
theorem hostileRecords_padPerturbed :
    hostileRecords P Qc (padPerturbed P Qm) = hostileRecords P Qc Qm := by
  simp only [hostileRecords, hostileResponses_padPerturbed]

end Padding

/-- `hchar` enters the `LY` route through `activeMask_bool` only: the acceptance-free core takes
the boolean masks themselves. -/
theorem hchar_only_feeds_hbool [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (hsatc : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) :
    ∀ (i : Fin (OptimizedComputeHostileAccumulator.rows P)) (j : Fin 3),
      OptimizedComputeHostileAccumulator.activeMask
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j = 0 ∨
      OptimizedComputeHostileAccumulator.activeMask
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j = 1 :=
  fun i j => OptimizedComputeHostileAccumulator.activeMask_bool P Qc hsatc hchar i j

/-! ## E. The lists -/

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
/-- **`IO.LIO` is order-insensitive in both lists** — the paper's `requests = responses`
 is a multiset statement, so the chips' row orders are immaterial. -/
theorem LIO_perm_invariant {R : Type} (Ksz : ℕ) {r r' s s' : List R}
    (h : IO.LIO Ksz r s) (hr : r.Perm r') (hs : s.Perm s') : IO.LIO Ksz r' s' := by
  obtain ⟨hrange, hnd, hperm⟩ := h
  refine ⟨?_, hs.nodup_iff.mp hnd, hr.symm.trans (hperm.trans hs)⟩
  rwa [← hs.length_eq]

omit [FiniteDimensional F K] [Fintype K] [CharP K (ringChar K)] in
/-- A record enters a compute row's request list **iff** its slot's activity mask is `1`. -/
theorem mem_rowRequests_iff (env : OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv F K)
    (r : Fin 10 → K) :
    r ∈ OptimizedComputeHostileAccumulator.rowRequests env ↔
      ∃ j : Fin 3, OptimizedComputeHostileAccumulator.activeMask env j = 1 ∧
        r = OptimizedComputeHostileAccumulator.rowRecord env j := by
  simp only [OptimizedComputeHostileAccumulator.rowRequests, List.mem_filterMap,
    List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hact : OptimizedComputeHostileAccumulator.activeMask env j = 1
    · rw [if_pos hact] at hj
      exact ⟨j, hact, (Option.some_inj.mp hj).symm⟩
    · rw [if_neg hact] at hj
      exact absurd hj (by simp)
  · rintro ⟨j, hact, rfl⟩
    exact ⟨j, by rw [if_pos hact]⟩

omit [FiniteDimensional F K] [Fintype K] [CharP K (ringChar K)] in
/-- A masked-out slot's record is not listed on its own account: if it is in the list, some
**active** slot carries the same record. -/
theorem masked_slot_not_emitted (env : OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv F K)
    (j : Fin 3) (hj : OptimizedComputeHostileAccumulator.activeMask env j ≠ 1)
    (hr : OptimizedComputeHostileAccumulator.rowRecord env j ∈
      OptimizedComputeHostileAccumulator.rowRequests env) :
    ∃ j' : Fin 3, j' ≠ j ∧ OptimizedComputeHostileAccumulator.activeMask env j' = 1 ∧
      OptimizedComputeHostileAccumulator.rowRecord env j' =
        OptimizedComputeHostileAccumulator.rowRecord env j := by
  obtain ⟨j', hact, heq⟩ := (mem_rowRequests_iff env _).mp hr
  refine ⟨j', ?_, hact, heq.symm⟩
  rintro rfl
  exact hj hact

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
/-- Slot `0` is always active: `sampledActive 0 = 1` (the always-on record). -/
theorem activeMask_slot0_always_one (env : OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv F K) :
    OptimizedComputeHostileAccumulator.activeMask env 0 = 1 := by
  simp [OptimizedComputeHostileAccumulator.activeMask, OptimizedComputeSubstitution.sampledActive,
    Expr.eval]

/-! ## F. The coins -/

/-- The compute chip's coins are two package challenges: the definition takes no trace. -/
theorem compute_chipCoins_trace_free :
    OptimizedComputeHostileAccumulator.chipCoins P =
      ⟨∑ k : Fin 3, P.optimized.computeChallenge (3 * 7 + (k : ℕ)) • P.optimized.basis k,
        ∑ k : Fin 3, P.optimized.computeChallenge (3 * 8 + (k : ℕ)) • P.optimized.basis k⟩ := rfl

section Coins

variable [Fintype F] [DecidableEq F]
  (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
  (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)

/-- The acceptance identifies the tuple's sampled IO coin with the package's. -/
theorem acceptance_pins_sampled_coin (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    c.2.1 = (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole) :=
  hacc.sampled_io_coins

/-- **Where the coins are counted — since W6.1 stage 2B.**  The consumed `optimizedFailureEvent`
is `OptimizedHostileProductionFailureEvent` at the trace's request count. Previously this
theorem (`failureEvent_prices_package_records`) stated the event at
`P.optimized.sampled.sampled.records`, which was `LY` §2's W6.1 item (i). -/
theorem failureEvent_prices_hostile_records :
    P.optimizedFailureEvent Qc Qm =
      OptimizedStrictPackage.OptimizedHostileProductionFailureEvent P.strategy P.optimized.census
        P.objects.cfg.challenges.lam (P.famIOEventOf Qc Qm)
        (OptimizedComputeHostileAccumulator.hostileRequests P Qc).length
        (P.computeSourceEnv Qc) (P.computeWalkEnv Qc) (P.computeScalarEnv Qc)
        (P.memorySourceEnv Qm) (P.memoryScalarFamilies Qm)
        (P.hostileInterRecords Qm) (P.memoryBaseEnv Qm) (P.computeWalkRootEvent Qc)
        (P.computeTilingEventOf Qc) (P.memoryTilingEventOf Qm)
        (P.computePrefixGammaEventOf Qc) (P.memoryPrefixGammaEventOf Qm)
        (P.memoryForestAlphaEventOf Qm)
        (P.decodedLambdaEventOf Qc Qm)
        (PreSeedCensus.reqPairEventOfEnvs K P.q P.optimized.family.problem.cfg.kMem
          (P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ) (P.memoryBaseEnv Qm)
          P.optimized.family.problem.cfg.memRows_pos
          (PreSeedCensus.requestTargets P.strategy.skeleton)) := by
  rw [hostileRequests_eq_package]
  rfl

/-- At the honest traces the two record sets coincide, so the priced event and the `LY`
hypotheses `hγ`/`hpoleEv`/`hpoleHit` are about the same object there. -/
theorem honest_hostileRecords_are_priced
    -- 28th: the canonical record identity now carries the Form R axis/width premises.
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis) (hwidth : FormRWidth F) :
    hostileRecords P (canonicalComputeTrace P) (canonicalMemoryTrace P) =
      honestRecords10 P.optimized.family :=
  canonical_hostileRecords P hax hwidth

end Coins

end

/-! ## D'. The F73 instance of §D -/

section F73

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.BuildablePackage.Concrete
open OptimizedStrictFullPackage.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance inst73 : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic


theorem hchar_K73cubic_local : ∀ n : ℕ, n ≤ 11 → (n : K73cubic) = 1 → n = 1 := by
  intro n hn h
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact absurd h (by simp)
  · have h' : ((n - 1 : ℕ) : K73cubic) = 0 := by
      rw [Nat.cast_sub hpos, Nat.cast_one, h, sub_self]
    have hdvd := (@CharP.cast_eq_zero_iff K73cubic _ 73 inst73 (n - 1)).mp h'
    rcases hdvd with ⟨m, hm⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · omega
    · have : 73 * 1 ≤ 73 * m := Nat.mul_le_mul_left 73 hm0
      omega

/-- The padded concrete memory trace is a **non-honest** trace. -/
theorem padPerturbed_concrete_ne_canonical :
    padPerturbed concreteOptimizedFullStrictPackage concreteMemoryTrace ≠
      canonicalMemoryTrace concreteOptimizedFullStrictPackage := by
  rw [← concreteMemoryTrace_eq]
  exact padPerturbed_ne _ _

/-- **`hostile_LIO` at a non-honest accepted pair at F73**: the real
`concrete_production_acceptance` transported to `(concreteComputeTrace, padPerturbed
concreteMemoryTrace)`, `hchar` local, every W6.1 obligation discharged from the package's
fields through `hostileResponses_padPerturbed`. -/
theorem concrete73_hostile_LIO_padPerturbed
    (hbasis : FormRBasis basis73)
    (hmoreC : ∀ i : Fin honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < honestLegacyFamily.problem.cfg.kMem →
        (honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0)
    -- 28th: Form R axis/width premises of the canonical record identities.
    (hax : FormRAxisBound concreteOptimizedFullStrictPackage.optimized.sampled
      concreteOptimizedFullStrictPackage.optimized.basis)
    (hwidth : FormRWidth F73) :
    IO.LIO concreteOptimizedFullStrictPackage.optimized.family.problem.cfg.Ksz
      (OptimizedComputeHostileAccumulator.hostileRequests concreteOptimizedFullStrictPackage
        concreteComputeTrace)
      (OptimizedMemoryHostileAccumulator.hostileResponses concreteOptimizedFullStrictPackage
        (padPerturbed concreteOptimizedFullStrictPackage concreteMemoryTrace)) := by
  have hacc : concreteOptimizedFullStrictPackage.OptimizedHistoricalAcceptanceAt
      concreteComputeTrace
      (padPerturbed concreteOptimizedFullStrictPackage concreteMemoryTrace)
      concreteProductionChallenge :=
    acceptance_padPerturbed _ _ _ _ (concrete_production_acceptance hbasis hmoreC)
  have hR := canonical_hostileRecords concreteOptimizedFullStrictPackage hax hwidth
  have hreq := canonical_hostileRequests concreteOptimizedFullStrictPackage hax hwidth
  have hresp := canonical_hostileResponses concreteOptimizedFullStrictPackage
  rw [← concreteComputeTrace_eq] at hreq hR
  rw [← concreteMemoryTrace_eq] at hresp hR
  have hpad := hostileResponses_padPerturbed concreteOptimizedFullStrictPackage concreteMemoryTrace
  have hpadR := hostileRecords_padPerturbed concreteOptimizedFullStrictPackage concreteMemoryTrace
    concreteComputeTrace
  have hl := concreteOptimizedFullStrictPackage.optimized.sampled.lio10
  have hfail := concreteOptimizedFullStrictPackage.optimized.sampled.ioGood10
  simp only [FiniteIO.IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    not_or] at hfail
  have hcoins := sampled_eq_sampledCoins concreteOptimizedFullStrictPackage _ _
    concreteProductionChallenge hacc
  refine hostile_LIO concreteOptimizedFullStrictPackage _ _ concreteProductionChallenge hacc
    hchar_K73cubic_local
    concreteOptimizedFullStrictPackage.optimized.sampled.sampled.charBound ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hreq, hl.2.2.length_eq]; exact hl.1
  · rw [hpad, hresp]
    exact hl.1.2
  · rw [hreq]; exact hl.2.2.nodup_iff.2 hl.2.1
  · rw [hpad, hresp]
    exact hl.2.1
  · rw [hpadR, hR]; have h := hfail.2.1; rw [hcoins] at h; exact h
  · rw [hpadR, hR]; have h := hfail.1; rw [hcoins] at h; exact h
  · rw [hpadR, hR]; have h := hfail.2.2; rw [hcoins] at h; exact h

end F73

end Nock.RedTeam.Batch274

-- LX, LY named theorems
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.hostile_intermediate_anchored
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.canonical_endpointSources
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.deployed_implies_intermediateInit
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.deployed_implies_intermediateTerminal
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.deployed_iff_paper
#print axioms Nock.RedTeam.Batch272.repaired_chip_rejects_intermediate_shift
#print axioms Nock.RedTeam.Batch272.packageM_intermediate_attack_rejected
#print axioms Nock.RedTeam.Batch272.packageM_honest_accepted
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.hostile_coins_agree
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.hostile_io_identity
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.hostile_LIO
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.hostile_LIO_of_not_failure
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.canonical_hostileRecords
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.canonical_hostile_LIO
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.concrete73_hostile_LIO
-- this file
#print axioms Nock.RedTeam.Batch274.firstMask_column_is_preprocessing
#print axioms Nock.RedTeam.Batch274.hostile_zero_mask_rejected
#print axioms Nock.RedTeam.Batch274.hostile_mask_ne_one_rejected
#print axioms Nock.RedTeam.Batch274.anchor_is_ipre_at_first_row
#print axioms Nock.RedTeam.Batch274.delta_at
#print axioms Nock.RedTeam.Batch274.delta_pole_witness
#print axioms Nock.RedTeam.Batch274.ipre_eq_deltaPrefix
#print axioms Nock.RedTeam.Batch274.icur_eq_deltaPrefix
#print axioms Nock.RedTeam.Batch274.hostile_intermediate_telescopes
#print axioms Nock.RedTeam.Batch274.intermediate_determined
#print axioms Nock.RedTeam.Batch274.degreeThreeEndpoints_degrees
#print axioms Nock.RedTeam.Batch274.endpoint_buckets_disclosed
#print axioms Nock.RedTeam.Batch274.memory_s_unmoved
#print axioms Nock.RedTeam.Batch274.padPerturbed_ne
#print axioms Nock.RedTeam.Batch274.acceptance_padPerturbed
#print axioms Nock.RedTeam.Batch274.hostileResponses_padPerturbed
#print axioms Nock.RedTeam.Batch274.padPerturbed_concrete_ne_canonical
#print axioms Nock.RedTeam.Batch274.concrete73_hostile_LIO_padPerturbed
#print axioms Nock.RedTeam.Batch274.hchar_only_feeds_hbool
#print axioms Nock.RedTeam.Batch274.LIO_perm_invariant
#print axioms Nock.RedTeam.Batch274.mem_rowRequests_iff
#print axioms Nock.RedTeam.Batch274.masked_slot_not_emitted
#print axioms Nock.RedTeam.Batch274.activeMask_slot0_always_one
#print axioms Nock.RedTeam.Batch274.acceptance_pins_sampled_coin
#print axioms Nock.RedTeam.Batch274.failureEvent_prices_hostile_records
#print axioms Nock.RedTeam.Batch274.honest_hostileRecords_are_priced
#print axioms Nock.RedTeam.Batch274.hchar_K73cubic_local
