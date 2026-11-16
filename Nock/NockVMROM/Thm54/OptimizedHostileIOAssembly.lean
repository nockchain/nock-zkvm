import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.OptimizedComputeCanonicalDenominator
import Nock.NockVMROM.Thm54.OptimizedStrictFullPackageConcrete
import Nock.NockVMROM.Thm54.BuildableAxisWitness
import Nock.NockVMROM.Thm54.P8Core.OptimizedHostileIOAssembly
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
## What is assembled

For **any** trace pair `(Qc, Qm)` and tuple `c` with `P.OptimizedHistoricalAcceptanceAt Qc Qm c`
— the consumed chip-level acceptance, never the honest package traces —

1. `hostileRecords P Qc Qm : FiniteIO.PreChallengeRecords K 9` pairs the compute chip's request
   list `OptimizedComputeHostileAccumulator.hostileRequests P Qc` with the memory chip's response list
   `OptimizedMemoryHostileAccumulator.hostileResponses P Qm`.  `pole_add_reqVals`/`pole_add_respVals`: the values
   `FiniteFieldIOSoundness.finiteIO_sound_of_identity` sums are `FiniteIO.compress coins r`
   per entry — `pole + RLC^γ(r)`.
2. `hostile_coins_agree`: both chips read the **same** sampled coins `c.2.1 = (γ, pole)`.  On
   the compute side the acceptance has **no** field naming challenge slots `7`/`8` hostilely — and
   none is needed: the compute chip's challenges are the package's `computeChallenge`, not trace
   columns, so `chipCoins P` does not depend on `Qc` at all; `computeChallengePins` (slots `7`/`8`
   are `exactFinalChallenge 7 = coins.gamma`, `8 = coins.pole`) plus `sampled_io_coins` give
   `chipCoins P = ⟨c.2.1.1, c.2.1.2⟩` (`compute_chipCoins_eq_sampled`).
4. **`hostile_LIO`**: `finiteIO_sound_of_identity` at `hostileRecords`, concluding
   `IO.LIO Ksz (hostileRequests P Qc) (hostileResponses P Qm)`.  The nonzero denominators are
   derived (compute: from the pole-hit exclusion; memory: from the committed inverse column,
   `hostileResponse_denominators_ne_zero`), the identity is (3).
5. `canonical_*` / `package73_*`: non-vacuity.  At the honest traces of **any** package the two
   hostile lists **are** the package's sampled records (`canonical_hostileRecords`), so every
   premise of `hostile_LIO` is discharged from the package's own `FiniteIOStrategy` fields, and
   `hostile_io_identity` holds with no hypothesis at all (`canonical_hostile_io_identity`).

## §5.

`hostile_LIO` takes the following as explicit hypotheses because **no committed gate of
`P.computeChip` or `P.memoryChip` implies them** for an arbitrary accepted trace:

* `hKp : Ksz < ringChar K` — a field-size condition on the configuration (the package carries it
  as `FiniteIOStrategy.charBound`; it is a parameter, not a gate);
* `hKreq : IO.InRange Ksz (hostileRequests P Qc).length`, `hKresp : (hostileResponses P Qm).length
  ≤ Ksz` — the paper's `1 ≤ |requests| ≤ K`, `|responses| ≤ K`; the chips bound
  the row counts, not the record counts;
* **`hreqnd : (hostileRequests P Qc).Nodup`, `hrespnd : (hostileResponses P Qm).Nodup`** — the
  paper's `Def:unique_request` / `cor_uni_req_uni_resp`.  Honestly these come
  from the execution (`BuildableNockExecution.requestNodup`, `timestampBounds` through
  `GenericHonestData.execution_lio_of_requestNodup`) — timestamps make the honest request records
  distinct.  Hostilely, **neither chip commits a gate that forces distinct records**: the memory
  chip has no timestamp-ordering gate (`ForestExponentOrder` is a property of the honest
  execution, `GenericHonestPackage.ForestExponentOrder_is_exponent_window`), and the compute chip
  has none either.
* `hγ : c.2.1.1 ∉ IORLCCollisionEvent (hostileRecords P Qc Qm)`, `hpoleEv : c.2.1.2 ∉
  IOLogDerivEvent (hostileRecords P Qc Qm) c.2.1.1` — the two counted soundness events (2), (3),
  **restated over the hostile records**.
* `hpoleHit : c.2.1.2 ∉ IOPoleHitEvent (hostileRecords P Qc Qm) c.2.1.1` — event (1) over the
  hostile records.  On the memory side this is a consequence of acceptance (the inverse column);
  on the compute side it is **not** — two active records both hitting the pole free the step
  (`Batch271.double_pole_frees_step`) — so it stays a hypothesis, priced by `IOPoleHitEvent_card_le`.

`hostile_LIO_of_not_failure` packages the three events as `c.2.1 ∉ IOFailureEvent (hostileRecords
P Qc Qm)`, the exact shape of `FiniteIOStrategy.coins_not_failure`.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedHostileIOAssembly

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedComputeSubstitution
open OptimizedComputeFiniteIOGates
open OptimizedComputeSameExecution
open OptimizedComputeSampledTrace
open OptimizedComputeCanonicalSatisfaction
open OptimizedMemoryGateBasis
open OptimizedMemoryCanonicalSatisfaction
open OptimizedMemorySemanticRealization
open StrictExtension
open OptimizedStrictFullPackage
open MultiRootOptimizedAcceptance
open OptimizedComputeFinalTrace
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F]
  [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## A. The hostile records -/

/-- **The records both chips commit to**, read off an arbitrary trace pair: the compute chip's
request list and the memory chip's response list. -/
def hostileRecords (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    FiniteIO.PreChallengeRecords K 10 :=
  ⟨OptimizedComputeHostileAccumulator.hostileRequests P Qc,
    OptimizedMemoryHostileAccumulator.hostileResponses P Qm⟩

variable (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])

@[simp] theorem hostileRecords_requests :
    (hostileRecords P Qc Qm).requests = OptimizedComputeHostileAccumulator.hostileRequests P Qc :=
  rfl

@[simp] theorem hostileRecords_responses :
    (hostileRecords P Qc Qm).responses =
      OptimizedMemoryHostileAccumulator.hostileResponses P Qm :=
  rfl

theorem hostileResponses_eq_package :
    OptimizedMemoryHostileAccumulator.hostileResponses P Qm = P.hostileResponses Qm := by
  unfold OptimizedMemoryHostileAccumulator.hostileResponses
    OptimizedFullStrictNockVMROMPackage.hostileResponses
  rfl

theorem hostileRecords_eq_package : hostileRecords P Qc Qm = P.hostileRecords Qc Qm := by
  unfold hostileRecords OptimizedFullStrictNockVMROMPackage.hostileRecords
  rw [hostileRequests_eq_package, hostileResponses_eq_package]

/-- The request-side value `finiteIO_sound_of_identity` sums is `compress coins r` per entry
(`pole + RLC^γ(r)`). -/
theorem pole_add_reqVals (coins : FiniteIO.IOCoins K)
    (i : Fin (hostileRecords P Qc Qm).requests.length) :
    coins.pole + FiniteIO.reqVals (hostileRecords P Qc Qm) coins.gamma i =
      FiniteIO.compress coins ((hostileRecords P Qc Qm).requests.get i) :=
  rfl

/-- The response-side value, likewise. -/
theorem pole_add_respVals (coins : FiniteIO.IOCoins K)
    (j : Fin (hostileRecords P Qc Qm).responses.length) :
    coins.pole + FiniteIO.respVals (hostileRecords P Qc Qm) coins.gamma j =
      FiniteIO.compress coins ((hostileRecords P Qc Qm).responses.get j) :=
  rfl

/-! ## B. The sampled coins, as each chip reads them -/

/-- **The compute chip's coin slots `7`/`8` are the package's sampled coins**, whatever the
trace: they are challenges (`P.optimized.computeChallenge`), not columns, and
`computeChallengePins` pins them to `exactFinalChallenge 7 = coins.gamma`, `8 = coins.pole`.  The
compute twin of `OptimizedFullStrictNockVMROMPackage.memorySourceEnv_sampled_coins`. -/
theorem compute_chipCoins_eq_sampled :
    OptimizedComputeHostileAccumulator.chipCoins P = P.optimized.sampled.sampled.coins := by
  have h7 : ∀ k : Fin 3, P.optimized.computeChallenge (3 * 7 + (k : ℕ)) =
      coord P.optimized.basis P.optimized.sampled.sampled.coins.gamma k :=
    fun k => P.optimized.computeChallengePins 7 k
  have h8 : ∀ k : Fin 3, P.optimized.computeChallenge (3 * 8 + (k : ℕ)) =
      coord P.optimized.basis P.optimized.sampled.sampled.coins.pole k :=
    fun k => P.optimized.computeChallengePins 8 k
  have hg : (∑ k : Fin 3, P.optimized.computeChallenge (3 * 7 + (k : ℕ)) • P.optimized.basis k) =
      P.optimized.sampled.sampled.coins.gamma := by
    simp_rw [h7]; exact reconstruct_coord _ _
  have hp : (∑ k : Fin 3, P.optimized.computeChallenge (3 * 8 + (k : ℕ)) • P.optimized.basis k) =
      P.optimized.sampled.sampled.coins.pole := by
    simp_rw [h8]; exact reconstruct_coord _ _
  unfold OptimizedComputeHostileAccumulator.chipCoins
  rw [hg, hp]

/-- **The memory chip's coin slots `4`/`5` are the package's sampled coins**, whatever the trace
(`memorySourceEnv_sampled_coins`, A-mem-2). -/
theorem memory_chipCoins_eq_sampled (Qm : Fin P.memoryChip.rap.w → F[X]) :
    OptimizedMemoryHostileAccumulator.chipCoins P = P.optimized.sampled.sampled.coins := by
  have h := P.memorySourceEnv_sampled_coins Qm (OptimizedMemoryHostileAccumulator.firstRow P)
  have hc := OptimizedMemoryHostileAccumulator.rowCoins_const P Qm
    (OptimizedMemoryHostileAccumulator.firstRow P)
  have hr : OptimizedMemoryHostileAccumulator.rowCoins
      (OptimizedMemoryHostileAccumulator.rowEnvK P Qm
        (OptimizedMemoryHostileAccumulator.firstRow P)) =
      ⟨(P.memorySourceEnv Qm (OptimizedMemoryHostileAccumulator.firstRow P)).chal 4,
        (P.memorySourceEnv Qm (OptimizedMemoryHostileAccumulator.firstRow P)).chal 5⟩ := rfl
  rw [hr] at hc
  unfold OptimizedMemoryHostileAccumulator.chipCoins
  rw [← hc, h.1, h.2]

section Acceptance

variable [Fintype F] [DecidableEq F]

/-- The tuple's sampled IO coins `c.2.1 = (γ, pole)` as an `IOCoins`. -/
def sampledCoins (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F) :
    FiniteIO.IOCoins K :=
  ⟨c.2.1.1, c.2.1.2⟩

variable (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)

/-- The package's sampled coins are the tuple's, under `sampled_io_coins`. -/
theorem sampled_eq_sampledCoins (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    P.optimized.sampled.sampled.coins = sampledCoins c := by
  have h := hacc.sampled_io_coins
  unfold sampledCoins
  rw [h]

/-- **`hostile_coins_agree`.**  Under the consumed acceptance the compute chip's `chipCoins`
(challenges `7`/`8`) and the memory chip's `chipCoins` (slots `4`/`5`) are both the sampled
`c.2.1 = (γ, pole)` — from `sampled_io_coins`, `memory_sampled_coins` and the compute-side
`computeChallengePins`.  Nothing is assumed of `Qc` or `Qm`: challenges are not trace columns. -/
theorem hostile_coins_agree (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    OptimizedComputeHostileAccumulator.chipCoins P = sampledCoins c ∧
      OptimizedMemoryHostileAccumulator.chipCoins P = sampledCoins c := by
  rw [compute_chipCoins_eq_sampled, memory_chipCoins_eq_sampled P Qm,
    sampled_eq_sampledCoins P Qc Qm c hacc]
  exact ⟨rfl, rfl⟩

end Acceptance

/-! ## C. Membership in the two hostile lists -/

/-- Every hostile request is the record of an **active** slot of some row. -/
theorem mem_hostileRequests {r : Fin 10 → K}
    (hr : r ∈ OptimizedComputeHostileAccumulator.hostileRequests P Qc) :
    ∃ (i : Fin (OptimizedComputeHostileAccumulator.rows P)) (j : Fin 3),
      OptimizedComputeHostileAccumulator.activeMask
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j = 1 ∧
      r = OptimizedComputeHostileAccumulator.rowRecord
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j := by
  simp only [OptimizedComputeHostileAccumulator.hostileRequests, List.mem_flatten,
    List.mem_ofFn] at hr
  obtain ⟨l, ⟨i, rfl⟩, hl⟩ := hr
  simp only [OptimizedComputeHostileAccumulator.rowRequests, List.mem_filterMap,
    List.mem_finRange, true_and] at hl
  obtain ⟨j, hj⟩ := hl
  by_cases hact : OptimizedComputeHostileAccumulator.activeMask
      (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j = 1
  · rw [if_pos hact] at hj
    exact ⟨i, j, hact, (Option.some_inj.mp hj).symm⟩
  · rw [if_neg hact] at hj
    exact absurd hj (by simp)

/-- Every hostile response is the record of a `ver = 1` row. -/
theorem mem_hostileResponses {r : Fin 10 → K}
    (hr : r ∈ OptimizedMemoryHostileAccumulator.hostileResponses P Qm) :
    ∃ i : Fin (OptimizedMemoryHostileAccumulator.rows P),
      (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i).trace 39 = 1 ∧
      r = OptimizedMemoryHostileAccumulator.rowRecord
        (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i)
        (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i) := by
  simp only [OptimizedMemoryHostileAccumulator.hostileResponses, List.mem_flatten,
    List.mem_ofFn] at hr
  obtain ⟨l, ⟨i, rfl⟩, hl⟩ := hr
  simp only [OptimizedMemoryHostileAccumulator.rowResponses,
    OptimizedMemoryHostileAccumulator.rowResponseTerms] at hl
  split_ifs at hl with hver
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hl
    exact ⟨i, hver, hl⟩
  · simp at hl

/-- An active slot's record is in the hostile request list. -/
theorem rowRecord_mem_hostileRequests (i : Fin (OptimizedComputeHostileAccumulator.rows P))
    (j : Fin 3)
    (hact : OptimizedComputeHostileAccumulator.activeMask
      (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j = 1) :
    OptimizedComputeHostileAccumulator.rowRecord (OptimizedComputeHostileAccumulator.rowEnv P Qc i)
        j ∈ OptimizedComputeHostileAccumulator.hostileRequests P Qc := by
  simp only [OptimizedComputeHostileAccumulator.hostileRequests, List.mem_flatten, List.mem_ofFn]
  refine ⟨_, ⟨i, rfl⟩, ?_⟩
  simp only [OptimizedComputeHostileAccumulator.rowRequests, List.mem_filterMap,
    List.mem_finRange, true_and]
  exact ⟨j, by rw [if_pos hact]⟩

/-! ## D. The compute-side pole-hit exclusion, over the hostile records -/

/-- The chip-level active-slot pole-hit exclusion `hpole` of `OptimizedComputeHostileAccumulator`
follows from `pole ∉ IOPoleHitEvent (hostileRecords) γ` at the chip's own coins. -/
theorem pole_excluded_of_not_poleHit
    (hhit : (OptimizedComputeHostileAccumulator.chipCoins P).pole ∉
      FiniteIO.IOPoleHitEvent (hostileRecords P Qc Qm)
        (OptimizedComputeHostileAccumulator.chipCoins P).gamma) :
    ∀ (i : Fin (OptimizedComputeHostileAccumulator.rows P)) (j : Fin 3),
      OptimizedComputeHostileAccumulator.activeMask
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j = 1 →
      OptimizedComputeHostileAccumulator.slotDenominator
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j ≠ 0 := by
  intro i j hact h0
  apply hhit
  simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨OptimizedComputeHostileAccumulator.rowRecord
    (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j,
    List.mem_append_left _ (rowRecord_mem_hostileRequests P Qc i j hact), ?_⟩
  rw [OptimizedComputeHostileAccumulator.slotDenominator_eq_compress,
    OptimizedComputeHostileAccumulator.rowCoins_const] at h0
  exact h0

/-- Conversely, under the chip-level exclusion every hostile request has a nonzero compressed
denominator at the chip's coins. -/
theorem compress_request_ne_zero
    (hpole : ∀ (i : Fin (OptimizedComputeHostileAccumulator.rows P)) (j : Fin 3),
      OptimizedComputeHostileAccumulator.activeMask
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j = 1 →
      OptimizedComputeHostileAccumulator.slotDenominator
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j ≠ 0)
    {r : Fin 10 → K} (hr : r ∈ OptimizedComputeHostileAccumulator.hostileRequests P Qc) :
    FiniteIO.compress (OptimizedComputeHostileAccumulator.chipCoins P) r ≠ 0 := by
  obtain ⟨i, j, hact, rfl⟩ := mem_hostileRequests P Qc hr
  have h := hpole i j hact
  rwa [OptimizedComputeHostileAccumulator.slotDenominator_eq_compress,
    OptimizedComputeHostileAccumulator.rowCoins_const] at h

/-- On the memory side the nonzero compressed denominator of every hostile response is a
**consequence of acceptance** (the inverse column `38`, `hostileResponse_denominators_ne_zero`)
together with the A-mem-2 pin (`hostile_role37_eq_compress_rowCoins`). -/
theorem compress_response_ne_zero
    (hsatm : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
    {r : Fin 10 → K} (hr : r ∈ OptimizedMemoryHostileAccumulator.hostileResponses P Qm) :
    FiniteIO.compress (OptimizedMemoryHostileAccumulator.chipCoins P) r ≠ 0 := by
  obtain ⟨i, hver, rfl⟩ := mem_hostileResponses P Qm hr
  have h37 := OptimizedMemoryHostileAccumulator.denom_ne_zero_of_ver P Qm hsatm i hver
  rw [OptimizedMemoryHostileAccumulator.hostile_role37_eq_compress_rowCoins P Qm hsatm i,
    ← OptimizedMemoryHostileAccumulator.rowRecord_eq_memRowRecord10] at h37
  have hc := OptimizedMemoryHostileAccumulator.rowCoins_const P Qm i
  have hrc : OptimizedMemoryHostileAccumulator.memRowCoins
      (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i) =
      OptimizedMemoryHostileAccumulator.chipCoins P := hc
  rw [hrc] at h37
  exact h37

/-! ## E. The identity between the two committed record lists -/

/-- Every accepted memory trace satisfies the per-row denominator pin (A-mem-2). -/
theorem denominatorPinned_at (hsatm : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
    (i : Fin (OptimizedMemoryHostileAccumulator.rows P)) :
    OptimizedMemoryHostileAccumulator.DenominatorPinned
      (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i)
      (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i) := by
  rw [OptimizedMemoryHostileAccumulator.denominatorPinned_iff,
    OptimizedMemoryHostileAccumulator.rowRecord_eq_memRowRecord10]
  intro _
  exact OptimizedMemoryHostileAccumulator.hostile_role37_eq_compress_rowCoins P Qm hsatm i

/-- **The identity at the chips' own coins** (both `chipCoins` are the package's sampled coins,
`compute_chipCoins_eq_sampled` / `memory_chipCoins_eq_sampled`, so they are stated here as one
`coins`).  For any two traces the chips accept, under `hchar`, the compute-side pole-hit exclusion
and the memory-side fold exclusion:
`Σ_{r ∈ hostileRequests} (compress coins r)⁻¹ = Σ_{r ∈ hostileResponses} (compress coins r)⁻¹`. -/
theorem hostile_io_identity_core
    (hsatc : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hsatm : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
    (hbool : ∀ (i : Fin (OptimizedComputeHostileAccumulator.rows P)) (j : Fin 3),
      OptimizedComputeHostileAccumulator.activeMask
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j = 0 ∨
      OptimizedComputeHostileAccumulator.activeMask
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j = 1)
    (hpole : ∀ (i : Fin (OptimizedComputeHostileAccumulator.rows P)) (j : Fin 3),
      OptimizedComputeHostileAccumulator.activeMask
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j = 1 →
      OptimizedComputeHostileAccumulator.slotDenominator
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j ≠ 0) :
    ((OptimizedComputeHostileAccumulator.hostileRequests P Qc).map
        fun r => (FiniteIO.compress P.optimized.sampled.sampled.coins r)⁻¹).sum =
      ((OptimizedMemoryHostileAccumulator.hostileResponses P Qm).map
        fun r => (FiniteIO.compress P.optimized.sampled.sampled.coins r)⁻¹).sum := by
  have hreq : (OptimizedComputeHostileAccumulator.rowEnv P Qc
      (OptimizedComputeHostileAccumulator.lastRow P)).extensionPublic 2 =
      ((OptimizedComputeHostileAccumulator.hostileRequests P Qc).map
        fun r => (FiniteIO.compress (OptimizedComputeHostileAccumulator.chipCoins P) r)⁻¹).sum := by
    rw [OptimizedComputeHostileAccumulator.hostile_requests_eq_sum_logUp P Qc hsatc hbool hpole,
      OptimizedComputeHostileAccumulator.hostileRequests, List.map_flatten, List.sum_flatten,
      List.map_map, List.map_ofFn, List.sum_ofFn]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [OptimizedComputeHostileAccumulator.logUpRowTerm_eq_rowRequests P Qc i (hbool i),
      OptimizedComputeHostileAccumulator.rowCoins_const]
    rfl
  rw [← compute_chipCoins_eq_sampled P, ← hreq,
    OptimizedComputeHostileAccumulator.gathered_requests,
    OptimizedMemoryHostileAccumulator.compute_requests_eq_memory_requests P,
    ← OptimizedMemoryHostileAccumulator.gathered_requests P Qm
      (OptimizedMemoryHostileAccumulator.lastRow P),
    OptimizedMemoryHostileAccumulator.hostile_requests_eq_sum_compress_of_denominatorPin P Qm
      hsatm (denominatorPinned_at P Qm hsatm),
    memory_chipCoins_eq_sampled P Qm, compute_chipCoins_eq_sampled P]

/-- **`IO.LIO` at the hostile records, at the chips' own coins** (the acceptance-free core of
`hostile_LIO`). -/
theorem hostile_LIO_core {Ksz : ℕ}
    (hsatc : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hsatm : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
    (hbool : ∀ (i : Fin (OptimizedComputeHostileAccumulator.rows P)) (j : Fin 3),
      OptimizedComputeHostileAccumulator.activeMask
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j = 0 ∨
      OptimizedComputeHostileAccumulator.activeMask
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (OptimizedComputeHostileAccumulator.hostileRequests P Qc).length)
    (hKresp : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).length ≤ Ksz)
    (hreqnd : (OptimizedComputeHostileAccumulator.hostileRequests P Qc).Nodup)
    (hrespnd : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).Nodup)
    (hpoleHit : P.optimized.sampled.sampled.coins.pole ∉
      FiniteIO.IOPoleHitEvent (hostileRecords P Qc Qm) P.optimized.sampled.sampled.coins.gamma)
    (hγ : P.optimized.sampled.sampled.coins.gamma ∉
      FiniteIO.IORLCCollisionEvent (hostileRecords P Qc Qm))
    (hpoleEv : P.optimized.sampled.sampled.coins.pole ∉
      FiniteIO.IOLogDerivEvent (hostileRecords P Qc Qm) P.optimized.sampled.sampled.coins.gamma) :
    IO.LIO Ksz (OptimizedComputeHostileAccumulator.hostileRequests P Qc)
      (OptimizedMemoryHostileAccumulator.hostileResponses P Qm) := by
  set coins := P.optimized.sampled.sampled.coins with hcoinsdef
  have hpole := pole_excluded_of_not_poleHit P Qc Qm (by
    rw [compute_chipCoins_eq_sampled]; exact hpoleHit)
  have hdA : ∀ i, coins.pole + FiniteIO.reqVals (hostileRecords P Qc Qm) coins.gamma i ≠ 0 := by
    intro i
    rw [pole_add_reqVals, hcoinsdef, ← compute_chipCoins_eq_sampled]
    have hmem : (hostileRecords P Qc Qm).requests.get i ∈
        OptimizedComputeHostileAccumulator.hostileRequests P Qc :=
      List.get_mem (hostileRecords P Qc Qm).requests i
    exact compress_request_ne_zero P Qc hpole hmem
  have hdB : ∀ j, coins.pole + FiniteIO.respVals (hostileRecords P Qc Qm) coins.gamma j ≠ 0 := by
    intro j
    rw [pole_add_respVals, hcoinsdef, ← memory_chipCoins_eq_sampled P Qm]
    have hmem : (hostileRecords P Qc Qm).responses.get j ∈
        OptimizedMemoryHostileAccumulator.hostileResponses P Qm :=
      List.get_mem (hostileRecords P Qc Qm).responses j
    exact compress_response_ne_zero P Qm hsatm hmem
  have hend : (∑ i, (coins.pole + FiniteIO.reqVals (hostileRecords P Qc Qm) coins.gamma i)⁻¹) =
      ∑ j, (coins.pole + FiniteIO.respVals (hostileRecords P Qc Qm) coins.gamma j)⁻¹ := by
    have h := hostile_io_identity_core P Qc Qm hsatc hsatm hbool hpole
    rw [← hostileRecords_requests P Qc Qm, ← hostileRecords_responses P Qc Qm,
      sum_requests_eq_sum_fin, sum_responses_eq_sum_fin] at h
    exact h
  exact FiniteIO.finiteIO_sound_of_identity (hostileRecords P Qc Qm) coins hdA hdB hend
    hKp hKreq hKresp hreqnd hrespnd hγ hpoleEv

section Acceptance

variable [Fintype F] [DecidableEq F]
  (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)

/-- For any `(Qc, Qm, c)` the consumed
acceptance accepts, under `hchar`, the compute-side pole-hit exclusion stated as the tree's event
(1) over the **hostile** records, and the memory-side fold exclusion at every row,
`Σ_{r ∈ hostileRequests} (compress c.2.1 r)⁻¹ = Σ_{r ∈ hostileResponses} (compress c.2.1 r)⁻¹`. -/
theorem hostile_io_identity (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hpoleHit : c.2.1.2 ∉ FiniteIO.IOPoleHitEvent (hostileRecords P Qc Qm) c.2.1.1) :
    ((OptimizedComputeHostileAccumulator.hostileRequests P Qc).map
        fun r => (FiniteIO.compress (sampledCoins c) r)⁻¹).sum =
      ((OptimizedMemoryHostileAccumulator.hostileResponses P Qm).map
        fun r => (FiniteIO.compress (sampledCoins c) r)⁻¹).sum := by
  have hcoins := sampled_eq_sampledCoins P Qc Qm c hacc
  have hpole := pole_excluded_of_not_poleHit P Qc Qm (by
    rw [compute_chipCoins_eq_sampled, hcoins]; exact hpoleHit)
  rw [← hcoins]
  exact hostile_io_identity_core P Qc Qm hacc.compute_satisfies hacc.memory_satisfies
    (fun i j => OptimizedComputeHostileAccumulator.activeMask_bool P Qc hacc.compute_satisfies
      hchar i j) hpole

/-! ## F. `IO.LIO` at the hostile records -/

/-- For any `(Qc, Qm, c)` the consumed acceptance accepts,
`finiteIO_sound_of_identity` at `hostileRecords P Qc Qm` and the sampled coins `c.2.1` gives
`IO.LIO Ksz (hostileRequests P Qc) (hostileResponses P Qm)`.

Supplied by the chips: the nonzero denominators (compute: from `hpoleHit`; memory: from the
inverse column and the A-mem-2 pin) and the sampled-pole identity (`hostile_io_identity`). -/
theorem hostile_LIO {Ksz : ℕ} (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (OptimizedComputeHostileAccumulator.hostileRequests P Qc).length)
    (hKresp : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).length ≤ Ksz)
    (hreqnd : (OptimizedComputeHostileAccumulator.hostileRequests P Qc).Nodup)
    (hrespnd : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).Nodup)
    (hpoleHit : c.2.1.2 ∉ FiniteIO.IOPoleHitEvent (hostileRecords P Qc Qm) c.2.1.1)
    (hγ : c.2.1.1 ∉ FiniteIO.IORLCCollisionEvent (hostileRecords P Qc Qm))
    (hpoleEv : c.2.1.2 ∉ FiniteIO.IOLogDerivEvent (hostileRecords P Qc Qm) c.2.1.1) :
    IO.LIO Ksz (OptimizedComputeHostileAccumulator.hostileRequests P Qc)
      (OptimizedMemoryHostileAccumulator.hostileResponses P Qm) := by
  have hcoins := sampled_eq_sampledCoins P Qc Qm c hacc
  have hγ' : P.optimized.sampled.sampled.coins.gamma ∉
      FiniteIO.IORLCCollisionEvent (hostileRecords P Qc Qm) := by rw [hcoins]; exact hγ
  have hpoleHit' : P.optimized.sampled.sampled.coins.pole ∉
      FiniteIO.IOPoleHitEvent (hostileRecords P Qc Qm) P.optimized.sampled.sampled.coins.gamma := by
    rw [hcoins]; exact hpoleHit
  have hpoleEv' : P.optimized.sampled.sampled.coins.pole ∉
      FiniteIO.IOLogDerivEvent (hostileRecords P Qc Qm) P.optimized.sampled.sampled.coins.gamma := by
    rw [hcoins]; exact hpoleEv
  exact hostile_LIO_core P Qc Qm hacc.compute_satisfies hacc.memory_satisfies
    (fun i j => OptimizedComputeHostileAccumulator.activeMask_bool P Qc hacc.compute_satisfies
      hchar i j) hKp hKreq hKresp hreqnd hrespnd hpoleHit' hγ' hpoleEv'

/-- The three events packaged as the tree's `IOFailureEvent` over the hostile records — the
shape of `FiniteIOStrategy.coins_not_failure`. -/
theorem hostile_LIO_of_not_failure {Ksz : ℕ} (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (OptimizedComputeHostileAccumulator.hostileRequests P Qc).length)
    (hKresp : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).length ≤ Ksz)
    (hreqnd : (OptimizedComputeHostileAccumulator.hostileRequests P Qc).Nodup)
    (hrespnd : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).Nodup)
    (hgood : c.2.1 ∉ FiniteIO.IOFailureEvent (hostileRecords P Qc Qm)) :
    IO.LIO Ksz (OptimizedComputeHostileAccumulator.hostileRequests P Qc)
      (OptimizedMemoryHostileAccumulator.hostileResponses P Qm) := by
  have hnot : ¬ (c.2.1.1 ∈ FiniteIO.IORLCCollisionEvent (hostileRecords P Qc Qm) ∨
      c.2.1.2 ∈ FiniteIO.IOPoleHitEvent (hostileRecords P Qc Qm) c.2.1.1 ∨
      c.2.1.2 ∈ FiniteIO.IOLogDerivEvent (hostileRecords P Qc Qm) c.2.1.1) := by
    intro h
    apply hgood
    simp only [FiniteIO.IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  exact hostile_LIO P Qc Qm c hacc hchar hKp hKreq hKresp hreqnd hrespnd
    (fun h => hnot (Or.inr (Or.inl h))) (fun h => hnot (Or.inl h))
    (fun h => hnot (Or.inr (Or.inr h)))

end Acceptance

/-! ## G. Non-vacuity — at the honest traces the hostile lists ARE the package's records

`hostileRequests P (canonicalComputeTrace P)` is the package's sampled request list and
`hostileResponses P (canonicalMemoryTrace P)` its sampled response list, so `hostileRecords` at
the honest traces **is** `P.optimized.sampled.sampled.records` and every premise of
`hostile_LIO_core` is a field of the package's `FiniteIOStrategy` — `hchar` is not even needed,
the honest masks being boolean by inspection (`canonical_activeMask_bool`). -/

section Canonical

open OptimizedComputeCanonicalDenominator

variable [Fintype F] [DecidableEq F]

/-- Slot `j`'s record column `c` reads only current-row trace columns `< 71` and challenges
`< 12`. -/
theorem rowRecord_rowScoped (j : Fin 3) (c : Fin 8) :
    ((computeTraceSubst .traceCur (67 + 8 * (j : ℕ) + (c : ℕ))).subst
      finalSampledNamespace).rowScoped 71 12 = true := by
  fin_cases j <;> fin_cases c <;> decide

theorem canonical_rowRecord
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis) (hwidth : FormRWidth F)
    (i : Fin (OptimizedComputeHostileAccumulator.rows P)) (j : Fin 3)
    (hact : OptimizedComputeFormRDenoms.slotActive P.optimized.family i j = 1) :
    OptimizedComputeHostileAccumulator.rowRecord (honestRow P i) j =
      RecordCarrier.extRec P.optimized.family.problem.exec.derivedRequestIO
        (NockVM.encRecFormR (requestRegister P i j) P.optimized.family.problem.cfg.challenges.lam) :=
  OptimizedCanonicalHostileLists.canonical_rowRecord P hax hwidth i j hact

/-- At the honest row the emitted request list is the opcode's active request prefix, Form R
encoded with its honest exponent. -/
theorem canonical_rowRequests
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis) (hwidth : FormRWidth F)
    (i : Fin (OptimizedComputeHostileAccumulator.rows P)) :
    OptimizedComputeHostileAccumulator.rowRequests (honestRow P i) =
      (NockVM.activeRequestRecords (P.optimized.family.problem.exec.computePubAt i)).map
        (fun r => RecordCarrier.extRec P.optimized.family.problem.exec.derivedRequestIO
          (NockVM.encRecFormR r P.optimized.family.problem.cfg.challenges.lam)) :=
  OptimizedCanonicalHostileLists.canonical_rowRequests P hax hwidth i

/-- **The hostile request list at the honest compute trace is the package's honest ten-slot
request list.** -/
theorem canonical_hostileRequests
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis) (hwidth : FormRWidth F) :
    OptimizedComputeHostileAccumulator.hostileRequests P (canonicalComputeTrace P) =
      (honestRecords10 P.optimized.family).requests := by
  rw [hostileRequests_eq_package]
  exact OptimizedCanonicalHostileLists.canonical_hostileRequests P hax hwidth

/-- The honest gathered memory row. -/
abbrev honestMemRow (i : Fin (OptimizedMemoryHostileAccumulator.rows P)) : Env K :=
  OptimizedMemoryHostileAccumulator.rowEnvK P (canonicalMemoryTrace P) i

theorem honestMemRow_eq (i : Fin (OptimizedMemoryHostileAccumulator.rows P)) :
    honestMemRow P i =
      canonicalGatheredEnv P.optimized.sampled P.optimized.memoryNodes P.optimized.basis
        P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit i :=
  canonical_memorySourceEnv P i

/-- Honest `ver` (role `39`) is the `read_root` indicator (`responseActive`). -/
theorem canonical_ver (i : Fin (OptimizedMemoryHostileAccumulator.rows P)) :
    (honestMemRow P i).trace 39 =
      responseActive (K := K) (P.optimized.family.problem.exec.memoryPubAt i).ver := by
  rw [honestMemRow_eq]
  have h := canonical_gather_sampled_index P.optimized.sampled P.optimized.memoryNodes
    P.optimized.memoryNodes_injective P.optimized.basis P.optimized.memoryChallenge
    P.optimized.memoryPublic P.optimized.orbit i (2 : Fin 14) (by decide)
  simpa [sampledMemoryRoleValue] using h

/-- **The hostile response list at the honest memory trace is the package's honest ten-slot
response list.** -/
theorem canonical_hostileResponses :
    OptimizedMemoryHostileAccumulator.hostileResponses P (canonicalMemoryTrace P) =
      (honestRecords10 P.optimized.family).responses := by
  rw [hostileResponses_eq_package]
  exact OptimizedCanonicalHostileLists.canonical_hostileResponses P

/-- **The hostile records at the honest traces are the package's honest ten-slot records.** -/
theorem canonical_hostileRecords
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis) (hwidth : FormRWidth F) :
    hostileRecords P (canonicalComputeTrace P) (canonicalMemoryTrace P) =
      honestRecords10 P.optimized.family := by
  unfold hostileRecords
  rw [canonical_hostileRequests P hax hwidth, canonical_hostileResponses]

/-- **`hostile_io_identity` at the honest traces of any package, hypothesis-free.** -/
theorem canonical_hostile_io_identity
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
        (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    ((OptimizedComputeHostileAccumulator.hostileRequests P (canonicalComputeTrace P)).map
        fun r => (FiniteIO.compress P.optimized.sampled.sampled.coins r)⁻¹).sum =
      ((OptimizedMemoryHostileAccumulator.hostileResponses P (canonicalMemoryTrace P)).map
        fun r => (FiniteIO.compress P.optimized.sampled.sampled.coins r)⁻¹).sum :=
  hostile_io_identity_core P (canonicalComputeTrace P) (canonicalMemoryTrace P)
    (canonicalComputeTrace_satisfies P hax hbasis hwidth) (canonicalMemoryTrace_satisfies P hmore hC)
    (canonical_activeMask_bool P) (canonical_pole_excluded P hax hwidth)

/-- **`hostile_LIO_core` at the honest traces of any package, every premise discharged** from
the package's own `FiniteIOStrategy` (`charBound`, `requestRange`, `responseRange`,
`uniqueRequest`, `uniqueResponse`, `gammaGood`, `poleGood`) and the sampled assignment's
`poleHitGood`, through `canonical_hostileRecords`. -/
theorem canonical_hostile_LIO
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
        (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    IO.LIO P.optimized.family.problem.cfg.Ksz
      (OptimizedComputeHostileAccumulator.hostileRequests P (canonicalComputeTrace P))
      (OptimizedMemoryHostileAccumulator.hostileResponses P (canonicalMemoryTrace P)) := by
  have hR := canonical_hostileRecords P hax hwidth
  have hreq := canonical_hostileRequests P hax hwidth
  have hresp := canonical_hostileResponses P
  have hl := P.optimized.sampled.lio10
  have hfail := P.optimized.sampled.ioGood10
  simp only [FiniteIO.IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    not_or] at hfail
  refine hostile_LIO_core P (canonicalComputeTrace P) (canonicalMemoryTrace P)
    (canonicalComputeTrace_satisfies P hax hbasis hwidth) (canonicalMemoryTrace_satisfies P hmore hC)
    (canonical_activeMask_bool P)
    P.optimized.sampled.sampled.charBound ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hreq, hl.2.2.length_eq]; exact hl.1
  · rw [hresp]; exact hl.1.2
  · rw [hreq]; exact hl.2.2.nodup_iff.2 hl.2.1
  · rw [hresp]; exact hl.2.1
  · rw [hR]; exact hfail.2.1
  · rw [hR]; exact hfail.1
  · rw [hR]; exact hfail.2.2

end Canonical

end

/-! ## F73. The fixture instances -/

section F73

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.BuildablePackage.Concrete
open Nock.NockVMROM.Thm54.BuildableConcrete
open OptimizedStrictFullPackage.Concrete
open OptimizedComputeFinalTrace
open ConcreteStrictPackage
open Nock.NockVMROM.Thm54.BuildableAxisWitness

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance inst73 : CharP K73cubic 73 := inferInstance

variable (hmore73 : LaterSeedZeros (F := F73) (K := K73cubic)
  BuildableConcrete.concreteExecution)
include hmore73

omit hmore73 in
theorem hchar_K73cubic : ∀ n : ℕ, n ≤ 11 → (n : K73cubic) = 1 → n = 1 := by
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
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- `hostile_io_identity_core` at the honest F73 `package73` traces, no hypothesis. -/
theorem package73_hostile_io_identity
    (hax : FormRAxisBound (package73 hmore73).optimized.sampled
      (package73 hmore73).optimized.basis)
    (hbasis : FormRBasis (package73 hmore73).optimized.basis)
    (hwidth : FormRWidth F73) :
    ((OptimizedComputeHostileAccumulator.hostileRequests (package73 hmore73)
        (canonicalComputeTrace (package73 hmore73))).map
        fun r => (FiniteIO.compress (package73 hmore73).optimized.sampled.sampled.coins r)⁻¹).sum =
      ((OptimizedMemoryHostileAccumulator.hostileResponses (package73 hmore73)
        (canonicalMemoryTrace (package73 hmore73))).map
        fun r => (FiniteIO.compress (package73 hmore73).optimized.sampled.sampled.coins r)⁻¹).sum :=
  canonical_hostile_io_identity (package73 hmore73) hax hbasis hwidth hmore73
    (execution_cprimeCoherent honestSeed honestAlpha)

/-- `hostile_LIO_core` at the honest F73 `package73` traces, every premise discharged. -/
theorem package73_hostile_LIO
    (hax : FormRAxisBound (package73 hmore73).optimized.sampled
      (package73 hmore73).optimized.basis)
    (hbasis : FormRBasis (package73 hmore73).optimized.basis)
    (hwidth : FormRWidth F73) :
    IO.LIO (package73 hmore73).optimized.family.problem.cfg.Ksz
      (OptimizedComputeHostileAccumulator.hostileRequests (package73 hmore73)
        (canonicalComputeTrace (package73 hmore73)))
      (OptimizedMemoryHostileAccumulator.hostileResponses (package73 hmore73)
        (canonicalMemoryTrace (package73 hmore73))) :=
  canonical_hostile_LIO (package73 hmore73) hax hbasis hwidth hmore73
    (execution_cprimeCoherent honestSeed honestAlpha)

omit hmore73 in
/-- The concrete F73 traces of `OptimizedStrictFullPackageConcrete` are the canonical ones. -/
theorem concreteComputeTrace_eq :
    concreteComputeTrace = canonicalComputeTrace concreteOptimizedFullStrictPackage := rfl

omit hmore73 in
theorem concreteMemoryTrace_eq :
    concreteMemoryTrace = canonicalMemoryTrace concreteOptimizedFullStrictPackage := rfl

omit hmore73 in
theorem concrete73_hostile_LIO
    (hax : FormRAxisBound concreteOptimizedFullStrictPackage.optimized.sampled
      concreteOptimizedFullStrictPackage.optimized.basis)
    (hwidth : FormRWidth F73)
    (hbasis : FormRBasis basis73)
    (hmoreC : ∀ i : Fin honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < honestLegacyFamily.problem.cfg.kMem →
        (honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0) :
    IO.LIO concreteOptimizedFullStrictPackage.optimized.family.problem.cfg.Ksz
      (OptimizedComputeHostileAccumulator.hostileRequests concreteOptimizedFullStrictPackage
        concreteComputeTrace)
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
  have hcoins := sampled_eq_sampledCoins concreteOptimizedFullStrictPackage _ _
    concreteProductionChallenge hacc
  refine hostile_LIO concreteOptimizedFullStrictPackage _ _ concreteProductionChallenge hacc
    hchar_K73cubic
    concreteOptimizedFullStrictPackage.optimized.sampled.sampled.charBound ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hreq, hl.2.2.length_eq]; exact hl.1
  · rw [hresp]; exact hl.1.2
  · rw [hreq]; exact hl.2.2.nodup_iff.2 hl.2.1
  · rw [hresp]; exact hl.2.1
  · rw [hR]; have h := hfail.2.1; rw [hcoins] at h; exact h
  · rw [hR]; have h := hfail.1; rw [hcoins] at h; exact h
  · rw [hR]; have h := hfail.2.2; rw [hcoins] at h; exact h

end F73

end OptimizedHostileIOAssembly
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.compute_chipCoins_eq_sampled
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.hostile_coins_agree
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.hostile_io_identity_core
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.hostile_io_identity
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.hostile_LIO
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.hostile_LIO_of_not_failure
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.hostile_LIO_core
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.canonical_hostileRecords
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.canonical_hostile_io_identity
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.canonical_hostile_LIO
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.package73_hostile_LIO
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly.concrete73_hostile_LIO
