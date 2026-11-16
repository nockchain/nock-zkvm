import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.HostileRecordLists
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
import Nock.NockVMROM.Thm54.P8Core.OptimizedMemoryHostileAccumulator

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# The memory chip's IO accumulator, telescoped hostilely

The memory mirror of `OptimizedComputeHostileAccumulator` (W6.0 step (b)+(c)).

* the sampled sources (`OptimizedMemoryGateBasis.sampledSources`):
  `safe · inv = 1` (roles `50`, `38`), `ver` boolean (`39`), `contribution = ver · inv` (`42`),
  `acc_after = acc_before + contribution` (`44`, `43`), `safe = ver · denom + (1 − ver)` (`37`),
  `first · acc_before = 0`, `last · (acc_after − terminal) = 0`, `terminal = requests` (`40`,
  public `2`);
* the mixed gates: the mask bindings `47 = first`, `48 = last`, the chain
  `(1 − last) · (acc_after(i) − acc_before(i+1)) = 0`, and — since A-mem-2 — the
  response-denominator pin `37 = pole + RLC^γ(record)` (`denominatorPinMixed`, coins at memory
  `𝕂` challenge slots `4`/`5`, record at roles `19..26`; the paper).

The seed and terminal sources sit in the coin-folded buckets `17`/`18`, so reading them
hostilely costs `FoldCollisionExcluded` at the row — the priced fold-collision event
(`extensionMemoryCollisionEvent`), taken here as a hypothesis in exactly that form (W2 removes the
fold and with it this hypothesis).  Unlike the compute side, **no pole-hit exclusion is needed**:
the committed inverse column `38` witnesses `denom ≠ 0` wherever `ver = 1`.

Result: `hostile_requests_eq_sum_memRowTerms` — the memory public `requests` is
`Σᵢ ver(i) · denom(i)⁻¹`, read off the committed columns alone; and since A-mem-2
`hostile_role37_eq_compress` — `denom(i) = compress (γ, pole) (record(i))` with the acceptance's
own sampled coins, so the sum is over the **records** the trace commits
(`memRowTerm_eq_record_form`).

Section E (F-5-2 groundwork) defines the **hostile response list** `hostileResponses` — the
records of the rows with `ver = 1`, never the `read_root` rows — and puts the sum in list form
over the committed denominators (`hostile_responses_eq_sum_over_records`), with the record form
`Σ (compress coins r)⁻¹` under the per-row denominator pin
(`hostile_responses_eq_sum_compress_of_denominatorPin`), which A-mem-2's acceptance now supplies
(`hostile_role37_eq_compress`).

Section B also carries the `LU` repair's hostile payoff: **`hostile_intermediate_anchored`**
— at any accepted trace `ipre(0) = 0` and `icur(last) = 0`, from the two
committed endpoint gates `intermediateInitGate = 47 · 27`, `intermediateTerminalGate = 48 · 28`
(`degreeThreeEndpoints`), the mask bindings and the fixed preprocessing masks.  Previously
the chip pinned the product columns `46`/`49` instead and `Nock/RedTeam/Batch272…` shifted
`ipre`/`icur` by any constant at the consumed chip.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedMemoryHostileAccumulator

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
open OptimizedMemoryCanonicalSatisfaction
open StrictExtension
open OptimizedStrictFullPackage
open OptimizedComputeFinalTrace
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## A. The sampled sources and mixed gates, named -/

theorem sampledSources_mem (e : Expr) (he : e ∈ sampledSources) :
    e ∈ transitionSources (K := K) := by
  simp only [transitionSources, List.mem_append]
  exact Or.inr he

/-- Pre-W2 mixed-bucket membership. -/
theorem accChainMixed_mem_folded :
    accChainMixed (F := F) ∈ foldedMixedTransitionGates (F := F) := by
  simp [foldedMixedTransitionGates]

theorem firstMaskMixed_mem_folded :
    firstMaskMixed (F := F) ∈ foldedMixedTransitionGates (F := F) := by
  simp [foldedMixedTransitionGates]

theorem lastMaskMixed_mem_folded :
    lastMaskMixed (F := F) ∈ foldedMixedTransitionGates (F := F) := by
  simp [foldedMixedTransitionGates]

/-! ### The record the row decodes to, and the coins it is compressed with (A-mem-2) -/

/-- **From the sampled sources alone**: the committed contribution (role `42`) is `ver · denom⁻¹`,
with no nonvanishing hypothesis — the inverse column `38` witnesses `safe ≠ 0`, and `safe = denom`
where `ver = 1`. -/
theorem contribution_eq_memRowTerm (envK : Env K)
    (hs : ∀ e ∈ sampledSources, e.eval envK = 0) :
    envK.trace 42 = memRowTerm envK := by
  have h0 := hs (.Sub (.Mul (extVar .traceCur 50) (extVar .traceCur 38)) (.Const 1))
    (by simp [sampledSources])
  have h1 := hs (.Mul (extVar .traceCur 39) (.Sub (extVar .traceCur 39) (.Const 1)))
    (by simp [sampledSources])
  have h2 := hs (.Sub (extVar .traceCur 42) (.Mul (extVar .traceCur 39) (extVar .traceCur 38)))
    (by simp [sampledSources])
  have h4 := hs (.Sub (extVar .traceCur 50)
      (.Add (.Mul (extVar .traceCur 39) (extVar .traceCur 37))
        (.Sub (.Const 1) (extVar .traceCur 39)))) (by simp [sampledSources])
  simp only [extVar, Expr.eval, sub_eq_zero, mul_eq_zero, Int.cast_one] at h0 h1 h2 h4
  rw [memRowTerm, h2]
  rcases h1 with hv | hv
  · rw [hv]; simp
  · rw [hv] at h4 ⊢
    simp only [one_mul, sub_self, add_zero] at h4
    rw [h4] at h0
    rw [one_mul, one_mul]
    exact eq_inv_of_mul_eq_one_right h0

/-! ## B. At the consumed chip -/

section Deployed

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

abbrev extraOf : Fin (sourceOf P).rap.k → ℕ :=
  RAPPadding.firstRoundExtra (sourceOf P).rap (sourceOf P).rounds_pos
    (RAPPadding.memoryResidualColumns 3)

/-- The projected source trace of a final trace. -/
abbrev projOf (Qm : Fin P.memoryChip.rap.w → F[X]) : Fin (sourceOf P).rap.w → F[X] :=
  RAPPadding.projectTrace (sourceOf P).rap (extraOf P) Qm

/-- Base-field row environment of the projected trace. -/
abbrev rowEnvF (Qm : Fin P.memoryChip.rap.w → F[X]) (i : Fin (rows P)) : Env F :=
  envOfTrace (projOf P Qm) P.optimized.orbit.ω (P.optimized.memoryNodes i)
    P.optimized.memoryChallenge P.optimized.memoryPublic

/-- Gathered `𝕂` row environment. -/
abbrev rowEnvK (Qm : Fin P.memoryChip.rap.w → F[X]) (i : Fin (rows P)) : Env K :=
  gatherEnv P.optimized.basis memoryCol0 (rowEnvF P Qm i)

variable (Qm : Fin P.memoryChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
include hsat

theorem source_sat :
    RAP.SatisfiesWithPreprocessing (sourceOf P) (projOf P Qm) :=
  (final_satisfies_iff_source P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic
    P.optimized.orbit P.optimized.family.problem.cfg.kMem Qm).mp hsat

/-- The four gate-list parts of the source language at row `i`. -/
theorem row_parts (i : Fin (rows P)) :
    (∀ g ∈ baseTransitionGates P.optimized.basis, g.eval (rowEnvF P Qm i) = 0) ∧
    (∀ g ∈ equalityChecks P.optimized.basis, g.eval (rowEnvF P Qm i) = 0) ∧
    (∀ g ∈ (memorySourceTemplate P.optimized.basis).extTransition ++
        (memorySourceTemplate P.optimized.basis).extDeg1 ++
        (memorySourceTemplate P.optimized.basis).extDeg3,
      g.eval (rowEnvK P Qm i) = 0) ∧
    (∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
      g.eval (rowEnvK P Qm i) (rowEnvF P Qm i) = 0) := by
  have hraw : (sourceMemoryRAP P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit (rowNodeSet P.optimized.memoryNodes)).Satisfies
      (projOf P Qm) := (source_sat P Qm hsat).1
  replace hraw := (sourceMemoryRAP_satisfies_iff_language P.optimized.sampled _ _ _ _ _ _).mp hraw
  have hx : P.optimized.memoryNodes i ∈ rowNodeSet P.optimized.memoryNodes := by
    simp [rowNodeSet]
  exact hraw _ hx

/-- The fixed masks: base column `4` is the first-row mask and `5` the last-row mask. -/
theorem masks_at (i : Fin (rows P)) :
    (rowEnvF P Qm i).trace 4 = (if (i : ℕ) = 0 then 1 else 0) ∧
      (rowEnvF P Qm i).trace 5 = (if (i : ℕ) + 1 = rows P then 1 else 0) := by
  have hbind := (source_sat P Qm hsat).2
  have hinj := P.optimized.memoryNodes_injective
  have hw : (sourceOf P).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit (rowNodeSet P.optimized.memoryNodes)).1
  have h4 : 4 < (sourceOf P).rap.w := by rw [hw]; norm_num
  have h5 : 5 < (sourceOf P).rap.w := by rw [hw]; norm_num
  have h0 := hbind ⟨0, by change 0 < 4; norm_num⟩
  have h1 := hbind ⟨1, by change 1 < 4; norm_num⟩
  have hc0 : (sourceOf P).preprocessingColumn ⟨0, by change 0 < 4; norm_num⟩ = ⟨4, h4⟩ := rfl
  have hc1 : (sourceOf P).preprocessingColumn ⟨1, by change 1 < 4; norm_num⟩ = ⟨5, h5⟩ := rfl
  rw [hc0] at h0
  rw [hc1] at h1
  constructor
  · simp only [rowEnvF, envOfTrace, dif_pos h4]
    rw [show projOf P Qm ⟨4, h4⟩ = OptimizedMemoryCanonicalTrace.firstRowMask
      P.optimized.memoryNodes from h0,
      OptimizedMemoryCanonicalTrace.firstRowMask_eval _ hinj]
  · simp only [rowEnvF, envOfTrace, dif_pos h5]
    rw [show projOf P Qm ⟨5, h5⟩ = OptimizedMemoryCanonicalTrace.lastRowMask
      P.optimized.memoryNodes from h1,
      OptimizedMemoryCanonicalTrace.lastRowMask_eval _ hinj]

theorem masks_bool (i : Fin (rows P)) :
    (rowEnvF P Qm i).trace 4 * ((rowEnvF P Qm i).trace 4 - 1) = 0 ∧
      (rowEnvF P Qm i).trace 5 * ((rowEnvF P Qm i).trace 5 - 1) = 0 := by
  obtain ⟨h4, h5⟩ := masks_at P Qm hsat i
  rw [h4, h5]
  constructor <;> split_ifs <;> simp

/-- The committed mixed gates at row `i`. -/
theorem mixed_at (i : Fin (rows P)) :
    ∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
      g.eval (rowEnvK P Qm i) (rowEnvF P Qm i) = 0 :=
  (row_parts P Qm hsat i).2.2.2

/-- The two `intermediate` endpoint gates at a row, in `𝕂`-level form: `first · ipre = 0` and
`last · icur = 0`, masked by the preprocessing columns `4`/`5`.  W2 stage 2
commits `intermediateInit`/`intermediateTerminal` as mixed `Scale` gates, so no extension-mask
binding is required. -/
theorem intermediate_endpoints_at (i : Fin (rows P)) :
    algebraMap F K ((rowEnvF P Qm i).trace 4) * (rowEnvK P Qm i).trace 27 = 0 ∧
      algebraMap F K ((rowEnvF P Qm i).trace 5) * (rowEnvK P Qm i).trace 28 = 0 := by
  have hI := mixed_at P Qm hsat i _ (intermediateInit_mem P.optimized.basis)
  have hT := mixed_at P Qm hsat i _ (intermediateTerminal_mem P.optimized.basis)
  simp only [intermediateInit, intermediateTerminal, MixedExpr.eval, bcur, CoeffExpr.eval] at hI hT
  exact ⟨hI, hT⟩

/-- **The `intermediate` aggregator is anchored at both ends at ANY accepted trace**
: the
first row's `ipre` (role `27`) and the last row's `icur` (role `28`) are `0`.  No fold hypothesis
— the two gates are committed mixed endpoints. -/
theorem hostile_intermediate_anchored :
    (rowEnvK P Qm (firstRow P)).trace 27 = 0 ∧ (rowEnvK P Qm (lastRow P)).trace 28 = 0 := by
  constructor
  · have h := (intermediate_endpoints_at P Qm hsat (firstRow P)).1
    rw [(masks_at P Qm hsat (firstRow P)).1, if_pos rfl, map_one, one_mul] at h
    exact h
  · have h := (intermediate_endpoints_at P Qm hsat (lastRow P)).2
    have hlast : ((lastRow P : ℕ) + 1 = rows P) :=
      Nat.sub_add_cancel P.optimized.family.problem.cfg.memRows_pos
    rw [(masks_at P Qm hsat (lastRow P)).2, if_pos hlast, map_one, one_mul] at h
    exact h

/-- Single-column accumulator step (`accStep`): off the last row,
`acc(i+1) = acc(i) + contribution(i)` on role `43`.  Replaces the two-role `accChainMixed`. -/
theorem acc_step_nonlast (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnvK P Qm i).traceNext 43 =
      (rowEnvK P Qm i).trace 43 + (rowEnvK P Qm i).trace 42 := by
  have hc := mixed_at P Qm hsat i _ (accStep_mem P.optimized.basis)
  have h5 : (rowEnvF P Qm i).trace 5 = 0 := by
    rw [(masks_at P Qm hsat i).2, if_neg (by omega)]
  simp only [accStep, MixedExpr.eval, bcur, CoeffExpr.eval, h5, sub_zero, map_one,
    one_mul, sub_eq_zero] at hc
  exact hc

omit hsat in
/-- Orbit alignment: the next-row read of role `43` at row `i` is role `43` at row `i+1`. -/
theorem next_acc (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnvK P Qm i).traceNext 43 = (rowEnvK P Qm ⟨(i : ℕ) + 1, hi⟩).trace 43 := by
  have hadj := P.optimized.memoryOrbitAligned i hi
  simp only [rowEnvK, gatherEnv, memoryCol0]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hw : (sourceOf P).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit (rowNodeSet P.optimized.memoryNodes)).1
  have hlt : 6 + 3 * 43 + (k : ℕ) < (sourceOf P).rap.w := by rw [hw]; omega
  simp only [rowEnvF, envOfTrace, dif_pos hlt]
  rw [hadj, mul_comm]

/-- Seed: at the first row `acc = 0` (`accInit = first · acc`, with `first = 1`).
No fold hypothesis — the gate is committed. -/
theorem acc_first : (rowEnvK P Qm (firstRow P)).trace 43 = 0 := by
  have h := mixed_at P Qm hsat (firstRow P) _ (accInit_mem P.optimized.basis)
  simp only [accInit, MixedExpr.eval, bcur, CoeffExpr.eval] at h
  rw [(masks_at P Qm hsat (firstRow P)).1, if_pos rfl, map_one, one_mul] at h
  exact h

/-- Contribution column equals the LogUp term, from the committed IO gates. -/
theorem contrib_eq_term (i : Fin (rows P)) :
    (rowEnvK P Qm i).trace 42 = memRowTerm (rowEnvK P Qm i) :=
  contribution_eq_memRowTerm_of_io (rowEnvK P Qm i) (rowEnvF P Qm i)
    (mixed_at P Qm hsat i _ (verBool_mem P.optimized.basis))
    (mixed_at P Qm hsat i _ (safeNormalisation_mem P.optimized.basis))
    (mixed_at P Qm hsat i _ (safeInverse_mem P.optimized.basis))
    (mixed_at P Qm hsat i _ (contribution_mem P.optimized.basis))

/-- Terminal: at the last row `acc + contribution = requests` (`accTerminal`). -/
theorem acc_last_plus_contrib :
    (rowEnvK P Qm (lastRow P)).trace 43 + (rowEnvK P Qm (lastRow P)).trace 42 =
      (rowEnvK P Qm (lastRow P)).pub 2 := by
  have h := mixed_at P Qm hsat (lastRow P) _ (accTerminal_mem P.optimized.basis)
  have hlast : ((lastRow P : ℕ) + 1 = rows P) :=
    Nat.sub_add_cancel P.optimized.family.problem.cfg.memRows_pos
  simp only [accTerminal, MixedExpr.eval, bcur, CoeffExpr.eval] at h
  rw [(masks_at P Qm hsat (lastRow P)).2, if_pos hlast, map_one, one_mul, sub_eq_zero] at h
  exact h

/-- **The response denominator is bound to the record and the coins at every row** (A-mem-2):
for any trace `P.memoryChip` accepts, role `37` at row `i` **is**
`FiniteIO.compress (γ, pole) (record)` with `γ`, `pole` the row's memory challenge slots `4`/`5`
and the record read off roles `19..26` — the paper. No fold hypothesis: the pin is a
mixed gate, not a folded source. -/
theorem hostile_role37_eq_compress_rowCoins (i : Fin (rows P)) :
    (rowEnvK P Qm i).trace 37 =
      FiniteIO.compress (memRowCoins (rowEnvK P Qm i))
        (memRowRecord10 (rowEnvK P Qm i) (rowEnvF P Qm i)) :=
  (denominatorPin_eval_iff _ _).1
    ((row_parts P Qm hsat i).2.2.2 _ (denominatorPinMixed_mem P.optimized.basis))

omit hsat in
/-- The row's coin slots are the package's memory challenge block, whatever the trace. -/
theorem memRowCoins_eq (i : Fin (rows P)) :
    memRowCoins (rowEnvK P Qm i) =
      ⟨(P.memorySourceEnv Qm i).chal 4, (P.memorySourceEnv Qm i).chal 5⟩ := rfl

omit hsat in
/-- **`hostile_role37_eq_compress` — with the acceptance's own coins.**  Under
`DeployedAcceptance` at tuple `c` (the pre-2a acceptance's constant-chip-plus-pins half; H1.5b
Part 2a re-pointed this from `OptimizedProductionAcceptanceAt`), the field `memory_sampled_coins` identifies the
row's coin slots with the tuple's sampled IO coins `c.2.1 = (γ, pole)`, so at every row
`role 37 = FiniteIO.compress ⟨γ, pole⟩ (record)` — the memory side of the sampled-pole identity
`FiniteFieldIOSoundness.finiteIO_sound_of_identity` consumes, at the records the chip commits to. -/
theorem hostile_role37_eq_compress [Fintype F] [DecidableEq F]
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : DeployedAcceptance P Qc Qm c) (i : Fin (rows P)) :
    (rowEnvK P Qm i).trace 37 =
      FiniteIO.compress ⟨c.2.1.1, c.2.1.2⟩
        (memRowRecord10 (rowEnvK P Qm i) (rowEnvF P Qm i)) := by
  rw [hostile_role37_eq_compress_rowCoins P Qm hacc.memory_satisfies i, memRowCoins_eq]
  obtain ⟨h4, h5⟩ := hacc.memory_sampled_coins i
  rw [h4, h5]

/-- **The response-side LogUp term, in record form** (A-mem-2): `ver · (pole + RLC^γ(record))⁻¹`
at every row of every accepted trace.  This is what `hostile_requests_eq_sum_memRowTerms` sums,
so the memory chip's `requests` is now a sum over **records read off the trace**, as the compute
chip's is (`OptimizedComputeHostileAccumulator.hostile_requests_eq_sum_over_records`). -/
theorem memRowTerm_eq_record_form (i : Fin (rows P)) :
    memRowTerm (rowEnvK P Qm i) =
      (rowEnvK P Qm i).trace 39 *
        (FiniteIO.compress (memRowCoins (rowEnvK P Qm i))
          (memRowRecord10 (rowEnvK P Qm i) (rowEnvF P Qm i)))⁻¹ := by
  rw [memRowTerm, hostile_role37_eq_compress_rowCoins P Qm hsat i]

omit hsat in
/-- The public `requests` gathered at any row is the package's `memoryPublic` block `12..14`. -/
theorem gathered_requests (i : Fin (rows P)) :
    (rowEnvK P Qm i).pub 2 =
      ∑ k : Fin 3, P.optimized.memoryPublic (12 + (k : ℕ)) • P.optimized.basis k := by
  simp only [rowEnvK, gatherEnv, memoryCol0, rowEnvF, envOfTrace]

/-! ## C. Telescoping -/

def prefixSum (m : ℕ) : K :=
  ∑ k ∈ Finset.range m, if h : k < rows P then memRowTerm (rowEnvK P Qm ⟨k, h⟩) else 0

omit hsat in
theorem prefixSum_succ (m : ℕ) (hm : m < rows P) :
    prefixSum P Qm (m + 1) = prefixSum P Qm m + memRowTerm (rowEnvK P Qm ⟨m, hm⟩) := by
  simp [prefixSum, Finset.sum_range_succ, hm]

theorem acc_eq_prefixSum :
    ∀ (m : ℕ) (hm : m < rows P), (rowEnvK P Qm ⟨m, hm⟩).trace 43 = prefixSum P Qm m := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [prefixSum, Finset.range_zero, Finset.sum_empty]
      exact acc_first P Qm hsat
  | succ m ih =>
      intro hm
      have hm' : m < rows P := by omega
      rw [← next_acc P Qm ⟨m, hm'⟩ hm, acc_step_nonlast P Qm hsat ⟨m, hm'⟩ hm,
        contrib_eq_term P Qm hsat ⟨m, hm'⟩, ih hm', prefixSum_succ P Qm m hm']

/-- **Hostile telescoping at the consumed memory chip.**  For any trace `P.memoryChip` accepts,
the memory public `requests` is `Σᵢ ver(i) · denom(i)⁻¹` — the response side of the paper's
log-derivative argument, read off the committed paper IO gates
(`accInit`/`accStep`/`accTerminal`/`contribution`).  No fold-collision hypothesis. -/
theorem hostile_requests_eq_sum_memRowTerms :
    (rowEnvK P Qm (lastRow P)).pub 2 = ∑ i : Fin (rows P), memRowTerm (rowEnvK P Qm i) := by
  have hpos := P.optimized.family.problem.cfg.memRows_pos
  have hlast : (rowEnvK P Qm (lastRow P)).trace 43 = prefixSum P Qm (rows P - 1) :=
    acc_eq_prefixSum P Qm hsat (rows P - 1) _
  rw [← acc_last_plus_contrib P Qm hsat, contrib_eq_term P Qm hsat (lastRow P), hlast,
    ← prefixSum_succ P Qm (rows P - 1) _, Nat.sub_add_cancel hpos]
  simp only [prefixSum]
  rw [← Fin.sum_univ_eq_sum_range (fun k => if h : k < rows P then
    memRowTerm (rowEnvK P Qm ⟨k, h⟩) else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [i.isLt]

theorem hostile_requests_public_eq_sum_memRowTerms :
    (∑ k : Fin 3, P.optimized.memoryPublic (12 + (k : ℕ)) • P.optimized.basis k) =
      ∑ i : Fin (rows P), memRowTerm (rowEnvK P Qm i) := by
  rw [← gathered_requests P Qm (lastRow P)]
  exact hostile_requests_eq_sum_memRowTerms P Qm hsat

/-! ## D. Across the two chips: one `requests`, two hostile sums -/

/-- **W6.0 (c) across the chips.**  For any pair of traces the two consumed chips accept, under
the compute chip's characteristic hypothesis and active-slot pole-hit exclusion and the memory
chip's fold-collision exclusion, the request-side and response-side LogUp sums read off the two
committed traces are **equal** — the sampled-pole identity between the two record lists that
`finiteIO_sound` consumes next. -/
theorem hostile_logUp_sums_agree
    (Qc : Fin P.computeChip.rap.w → F[X])
    (hsatc : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hpole : ∀ (i : Fin (OptimizedComputeHostileAccumulator.rows P)) (j : Fin 3),
      OptimizedComputeHostileAccumulator.activeMask
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j = 1 →
      OptimizedComputeHostileAccumulator.slotDenominator
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j ≠ 0) :
    (∑ i : Fin (OptimizedComputeHostileAccumulator.rows P),
        OptimizedComputeHostileAccumulator.logUpRowTerm
          (OptimizedComputeHostileAccumulator.rowEnv P Qc i)) =
      ∑ i : Fin (rows P), memRowTerm (rowEnvK P Qm i) := by
  rw [← hostile_requests_public_eq_sum_memRowTerms P Qm hsat,
    ← compute_requests_eq_memory_requests P,
    ← OptimizedComputeHostileAccumulator.gathered_requests P Qc
      (OptimizedComputeHostileAccumulator.lastRow P)]
  exact (OptimizedComputeHostileAccumulator.hostile_requests_eq_sum_logUp_of_pole P Qc hsatc
    hchar hpole).symm

end Deployed

/-! ## E. The response list read off the trace (F-5-2 groundwork for W6.0 (d))

So the
hostile response list a trace commits to is **"the records of rows with `ver = 1`"**, never
"the `read_root` rows". This section defines that list and telescopes the memory chip's
`Σᵢ ver(i)·denom(i)⁻¹` onto it, mirroring `OptimizedComputeHostileAccumulator` §F.

What the deployed chip does **not** yet bind is the denominator: role `37` is a free column
.  So the unconditional
statement here sums the **committed** denominators of the `ver = 1` rows
(`hostile_responses_eq_sum_over_records`), and the record form
`Σ (compress coins r)⁻¹` over `hostileResponses` is stated **conditionally** on the denominator
pin `role 37 = pole + Σ_{c<8} γ^c · role(19 + c)` at every `ver = 1` row
(`hostile_responses_eq_sum_compress_of_denominatorPin`) — the paper's
`RLC^α(x_mem(i,·)) − β`, which is exactly what A-mem-2 /
`MemoryPaperFactorization.denominatorPin` commits (`LP` §3, `LR`).  No pole-hit hypothesis is
needed on this side: the committed inverse column `38` witnesses every listed denominator nonzero
(`hostileResponse_denominators_ne_zero`). -/

section Responses

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! `rowRecord`, `rowDenominator`, `rowResponseTerms` and `rowResponses` now live upstream in
`HostileRecordLists.lean`, under this namespace, so that the pinned capstone module can read the
response list off a trace (W6.1 stage 2B). -/

/-- The memory chip's coin slots as `LP` §3 / `MemoryPaperFactorization.denominatorPin` read them:
`γ` at `𝕂` challenge `4`, the pole at `5`.  Both are `0` in `BuildableChips.memoryChallengeTargets`
today; A-mem-2 pins them to the sampled coins. -/
def rowCoins (envK : Env K) : FiniteIO.IOCoins K := ⟨envK.chal 4, envK.chal 5⟩

omit [Fintype K] [CharP K (ringChar K)] in
/-- With boolean `ver` the committed row term `ver · denom⁻¹` is the sum of the reciprocals of
the row's served denominators (one or none). -/
theorem memRowTerm_eq_rowResponseTerms (envK : Env K) (envF : Env F)
    (hbool : envK.trace 39 = 0 ∨ envK.trace 39 = 1) :
    memRowTerm envK = ((rowResponseTerms envK envF).map fun rd => rd.2⁻¹).sum := by
  rcases hbool with h | h <;> simp [memRowTerm, rowResponseTerms, rowDenominator, h]

/-- **The denominator pin, per row** — what A-mem-2 / `MemoryPaperFactorization.denominatorPin`
commits: at a `ver = 1` row the committed denominator is `pole + Σ_{c<8} γ^c · role(19 + c)`,
the paper's `RLC^α(x_mem(i,·)) − β` in `FiniteIO.compress`'s additive
convention, with the row's own record. -/
def DenominatorPinned (envK : Env K) (envF : Env F) : Prop :=
  envK.trace 39 = 1 →
    envK.trace 37 =
      envK.chal 5 + ∑ c : Fin 10, envK.chal 4 ^ (c : ℕ) * rowRecord envK envF c

omit [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
/-- The pin says exactly `rowDenominator = compress (rowCoins) (rowRecord)`. -/
theorem denominatorPinned_iff (envK : Env K) (envF : Env F) :
    DenominatorPinned envK envF ↔
      (envK.trace 39 = 1 →
        rowDenominator envK = FiniteIO.compress (rowCoins envK) (rowRecord envK envF)) := by
  simp only [DenominatorPinned, rowDenominator, FiniteIO.compress, rowCoins, Walk.rlc]

variable (Qm : Fin P.memoryChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
include hsat

/-- **`ver` is boolean at every row of an accepted trace**, from the chip's own gate
(`sampledSources[1]`, the paper's `ver(i)·(ver(i) − 1) = 0`). -/
theorem ver_bool (i : Fin (rows P)) :
    (rowEnvK P Qm i).trace 39 = 0 ∨ (rowEnvK P Qm i).trace 39 = 1 := by
  have h1 := mixed_at P Qm hsat i _ (verBool_mem P.optimized.basis)
  simp only [verBool, MixedExpr.eval, mul_eq_zero, sub_eq_zero, Int.cast_one] at h1
  exact h1

/-- Where `ver = 1` the committed denominator is nonzero: `safe · inv = 1` and `safe = denom`.
The memory side's counterpart of the compute side's pole-hit exclusion is thus a **consequence**
of acceptance, not a hypothesis. -/
theorem denom_ne_zero_of_ver (i : Fin (rows P))
    (hver : (rowEnvK P Qm i).trace 39 = 1) : (rowEnvK P Qm i).trace 37 ≠ 0 := by
  have s0 := mixed_at P Qm hsat i _ (safeInverse_mem P.optimized.basis)
  have s4 := mixed_at P Qm hsat i _ (safeNormalisation_mem P.optimized.basis)
  simp only [safeInverse, safeNormalisation, MixedExpr.eval, Int.cast_one, hver] at s0 s4
  intro h0
  have h50 : (rowEnvK P Qm i).trace 50 = 0 := by linear_combination s4 + h0
  rw [h50, zero_mul] at s0
  exact one_ne_zero (by linear_combination -s0)

omit hsat in
/-- The coins are the same at every row (they are challenges, not columns). -/
theorem rowCoins_const (i : Fin (rows P)) :
    rowCoins (rowEnvK P Qm i) =
      ⟨∑ k : Fin 3, P.optimized.memoryChallenge (6 + 3 * 4 + (k : ℕ)) • P.optimized.basis k,
        ∑ k : Fin 3,
          P.optimized.memoryChallenge (6 + 3 * 5 + (k : ℕ)) • P.optimized.basis k⟩ := by
  simp only [rowCoins, rowEnvK, gatherEnv, memoryCol0, rowEnvF, envOfTrace]

/-- The coins the memory chip reads (`𝕂` challenge slots `4`, `5`; cf.
`MemoryPaperFactorization.HonestSampledCoinSlots`). -/
def chipCoins : FiniteIO.IOCoins K :=
  ⟨∑ k : Fin 3, P.optimized.memoryChallenge (6 + 3 * 4 + (k : ℕ)) • P.optimized.basis k,
    ∑ k : Fin 3, P.optimized.memoryChallenge (6 + 3 * 5 + (k : ℕ)) • P.optimized.basis k⟩

/-- **The response list read off the trace, with its committed denominators**: every `ver = 1`
row's `(record, role 37)` in row order. -/
def hostileResponseTerms : List ((Fin 10 → K) × K) :=
  (List.ofFn fun i : Fin (rows P) => rowResponseTerms (rowEnvK P Qm i) (rowEnvF P Qm i)).flatten

/-- **The response list read off the trace** (F-5-2): the records of the `ver = 1` rows, in row
order — defined by `ver`, never by the state. -/
def hostileResponses : List (Fin 10 → K) :=
  (List.ofFn fun i : Fin (rows P) => rowResponses (rowEnvK P Qm i) (rowEnvF P Qm i)).flatten

omit hsat in
theorem hostileResponses_eq_map_fst :
    hostileResponses P Qm = (hostileResponseTerms P Qm).map Prod.fst := by
  simp only [hostileResponses, hostileResponseTerms, rowResponses, List.map_flatten,
    List.map_ofFn]
  rfl

/-- **The memory chip's hostile sum in list form.**  For any accepted trace,
`Σᵢ ver(i)·denom(i)⁻¹` is the sum of the reciprocals of the **committed** denominators of the
rows the trace marks `ver = 1`. -/
theorem hostile_responses_eq_sum_over_records :
    (∑ i : Fin (rows P), memRowTerm (rowEnvK P Qm i)) =
      ((hostileResponseTerms P Qm).map fun rd => rd.2⁻¹).sum := by
  rw [hostileResponseTerms, List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn,
    List.sum_ofFn]
  exact Finset.sum_congr rfl fun i _ =>
    memRowTerm_eq_rowResponseTerms _ _ (ver_bool P Qm hsat i)

/-- With it, `requests` itself in list form (`hostile_requests_eq_sum_memRowTerms`). -/
theorem hostile_requests_eq_sum_over_response_terms :
    (rowEnvK P Qm (lastRow P)).pub 2 =
      ((hostileResponseTerms P Qm).map fun rd => rd.2⁻¹).sum := by
  rw [hostile_requests_eq_sum_memRowTerms P Qm hsat]
  exact hostile_responses_eq_sum_over_records P Qm hsat

/-- Every listed committed denominator is nonzero (from the inverse column, row by row). -/
theorem hostileResponse_denominators_ne_zero :
    ∀ rd ∈ hostileResponseTerms P Qm, rd.2 ≠ 0 := by
  intro rd hrd
  simp only [hostileResponseTerms, List.mem_flatten, List.mem_ofFn] at hrd
  obtain ⟨l, ⟨i, rfl⟩, hl⟩ := hrd
  simp only [rowResponseTerms] at hl
  split_ifs at hl with hver
  · simp only [List.mem_singleton] at hl
    subst hl
    exact denom_ne_zero_of_ver P Qm hsat i hver
  · simp at hl

/-- **The record form, conditional on the pin.**  If every `ver = 1` row of an accepted trace
satisfies the denominator pin, the memory chip's hostile sum is
`Σ_{r ∈ hostileResponses} (compress chipCoins r)⁻¹` — the response side of the identity
`FiniteFieldIOSoundness.finiteIO_sound_of_identity` consumes, at the records the chip commits to.
This is the exact statement A-mem-2 turns unconditional. -/
theorem hostile_responses_eq_sum_compress_of_denominatorPin
    (hpin : ∀ i : Fin (rows P), DenominatorPinned (rowEnvK P Qm i) (rowEnvF P Qm i)) :
    (∑ i : Fin (rows P), memRowTerm (rowEnvK P Qm i)) =
      ((hostileResponses P Qm).map fun r => (FiniteIO.compress (chipCoins P) r)⁻¹).sum := by
  rw [hostile_responses_eq_sum_over_records P Qm hsat, hostileResponses_eq_map_fst,
    List.map_map]
  congr 1
  simp only [hostileResponseTerms, List.map_flatten, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  simp only [Function.comp_apply, rowResponseTerms]
  split_ifs with hver
  · have hp := (denominatorPinned_iff (rowEnvK P Qm i) (rowEnvF P Qm i)).1 (hpin i) hver
    simp only [List.map_cons, List.map_nil, Function.comp_apply, hp, rowCoins_const]
    rfl
  · rfl

/-- `requests` in the conditional record form. -/
theorem hostile_requests_eq_sum_compress_of_denominatorPin
    (hpin : ∀ i : Fin (rows P), DenominatorPinned (rowEnvK P Qm i) (rowEnvF P Qm i)) :
    (rowEnvK P Qm (lastRow P)).pub 2 =
      ((hostileResponses P Qm).map fun r => (FiniteIO.compress (chipCoins P) r)⁻¹).sum := by
  rw [hostile_requests_eq_sum_memRowTerms P Qm hsat]
  exact hostile_responses_eq_sum_compress_of_denominatorPin P Qm hsat hpin

end Responses

end
end OptimizedMemoryHostileAccumulator
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.contribution_eq_memRowTerm
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.contribution_eq_memRowTerm_of_io
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.intermediate_endpoints_at
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.hostile_intermediate_anchored
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.acc_eq_prefixSum
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.hostile_requests_eq_sum_memRowTerms
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.hostile_requests_public_eq_sum_memRowTerms
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.compute_requests_eq_memory_requests
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.hostile_logUp_sums_agree
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.ver_bool
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.hostile_responses_eq_sum_over_records
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.hostileResponse_denominators_ne_zero
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.hostile_responses_eq_sum_compress_of_denominatorPin
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.hostile_requests_eq_sum_compress_of_denominatorPin
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.denominatorPin_eval_iff
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.hostile_role37_eq_compress_rowCoins
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.hostile_role37_eq_compress
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator.memRowTerm_eq_record_form
