/-
  Nock/NockVMROM/Thm54/FamilyChipTwins.lean

  Since QE the originals rest on `OptimizedHistoricalAcceptanceAt` (the pre-2a acceptance, which
  keeps `p8` / `same_problem` / the sampled pins as assumed fields) and take the IO exclusion `hio`
  at the PACKAGE records explicitly.  The twins here take only:
  * the capstone acceptance `P.OptimizedProductionAcceptanceAt Qc Qm c` (the two family-chip
    satisfactions; `DeployedAcceptanceAt` at the reindexed traces);
  * `c ∉ P.optimizedFailureEvent Qc Qm` (its IO component is `FamilyIOGood` through
    `FamilyEnvCore.familyIOGood_of_not_mem`);
  * the package field `rowsBound` (the window premises `hKp` / `hKreq` / `hKresp`);
  * the package field `stateTagChar` (`hchar` and `MemStateTagChar F`, as in
    `optimizedFullStrict_hostile_LIO_at_window`).
  The `_of_good_at` forms take `DeployedAcceptanceAt`, the event at the reindexed traces and
  `FamilyIOGood` explicitly, exactly as `FamilyIOChainRouteB`'s twins.  `response_ts_mem_powers*_at`
  keeps the original's own conclusion side condition `alphaM c.1 ≠ 0` (resp. `_of_two`'s
  `2 ≤ |requests|`), verbatim.

  **The conclusions say the same thing** (`*_original` below): at the original's own binders and
  the original's own conclusion (package compute env `OptimizedComputeHostileAccumulator.rowEnv`,
  package response list), both follow from the production acceptance and the event alone.  For the
  roots this is because the request record's root slots `0..2` and the activity masks read trace
  columns only (`slotExpr_root_traceOnly`, `activeMask_honestQc`), so they agree between the family
  and the package compute environments; for the responses because the family response list IS the
  package list at the reindexed trace (`hostileResponsesAt_eq_package`).

  Additive.  Paper: the paper.
-/
import Nock.NockVMROM.Thm54.FamilyIOChainRouteB
import Nock.NockVMROM.Thm54.MemoryWalkRoots
import Nock.NockVMROM.Thm54.ResponseTsMemPowers
import Nock.NockVMROM.Thm54.TraceOnlyExpr
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Module

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

namespace Nock.NockVMROM.Thm54.FamilyChipTwins

/-! ## A. Shared facts: package-derived side conditions, and trace-only reads -/

/-- **The request record's root slots `0..2` read trace columns only** (no challenge, no
public): `pubFP` / `mr2Field` / `mr3Field` over `.traceCur`. -/
theorem slotExpr_root_traceOnly :
    ∀ j : Fin 3, ∀ k : Fin 3, traceOnly (FamilyEnvCore.slotExpr j ⟨k, by omega⟩) = true := by
  decide +kernel

theorem rowRecord_eq_slotExpr {F K : Type} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) (j : Fin 3) (k : Fin 10) :
    OptimizedComputeHostileAccumulator.rowRecord env j k = (FamilyEnvCore.slotExpr j k).eval env.toSourceEnv := by
  unfold OptimizedComputeHostileAccumulator.rowRecord FamilyEnvCore.slotExpr
  split_ifs <;> rfl

/-- Root slots `0..2` of a request record agree whenever the source traces agree. -/
theorem rowRecord_root_congr {F K : Type} [Field F] [Field K] [Algebra F K]
    {env env' : CorrectedFinalTypedEnv F K} (h : env.toSourceEnv.trace = env'.toSourceEnv.trace)
    (j : Fin 3) (k : Fin 3) :
    OptimizedComputeHostileAccumulator.rowRecord env j ⟨k, by omega⟩ =
      OptimizedComputeHostileAccumulator.rowRecord env' j ⟨k, by omega⟩ := by
  rw [rowRecord_eq_slotExpr, rowRecord_eq_slotExpr]
  exact eval_congr_of_traceOnly _ h (slotExpr_root_traceOnly j k)

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- `MemStateTagChar F` from the package field `stateTagChar` (`11 < ringChar K = ringChar F`);
the production restatement of `Batch824.memStateTagChar_of_package`. -/
theorem memStateTagChar_of_package (P' : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    MemStateTagChar F := by
  intro n hn heq
  have h11 := OptimizedHostileConfiguration.eleven_lt_ringChar_of_package P'
  have hFK : ringChar F = ringChar K := Algebra.ringChar_eq F K
  haveI : CharP F (ringChar F) := ringChar.charP F
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact absurd heq (by simp)
  · have h' : ((n - 1 : ℕ) : F) = 0 := by
      rw [Nat.cast_sub hpos, Nat.cast_one, heq, sub_self]
    have hdvd := (CharP.cast_eq_zero_iff F (ringChar F) (n - 1)).mp h'
    have hlt : n - 1 < ringChar F := by rw [hFK]; omega
    have := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega

/-- The package compute env at a package trace and the family compute env at its reindexing have
the same source trace (only challenge / public maps differ). -/
theorem rowEnv_toSourceEnv_trace (c : OptimizedProductionChallengeTuple K F)
    (Qc0 : Fin P.computeChip.rap.w → F[X]) (i : Fin (rows P)) :
    (OptimizedComputeHostileAccumulator.rowEnv P Qc0 i).toSourceEnv.trace =
      (rowEnvAt P c (P.familyQc c Qc0) i).toSourceEnv.trace := by
  have h := computeBaseEnv_honestQc_trace P c (P.familyQc c Qc0) i
  rw [show honestQc P c (P.familyQc c Qc0) = Qc0 from
    FamilyEnvCore.honestQc_familyQc P.optimized c Qc0] at h
  exact FamilyEnvCore.gather_toSourceEnv_trace_congr P.optimized h

/-- The activity masks agree between the package and the family compute envs. -/
theorem activeMask_rowEnv_eq (c : OptimizedProductionChallengeTuple K F)
    (Qc0 : Fin P.computeChip.rap.w → F[X]) (i : Fin (rows P)) (j : Fin 3) :
    activeMask (OptimizedComputeHostileAccumulator.rowEnv P Qc0 i) j =
      activeMask (rowEnvAt P c (P.familyQc c Qc0) i) j := by
  have h := activeMask_honestQc P c (P.familyQc c Qc0) i j
  rw [show honestQc P c (P.familyQc c Qc0) = Qc0 from
    FamilyEnvCore.honestQc_familyQc P.optimized c Qc0] at h
  exact h

/-- From the capstone's event to the `_of_good_at` premises at the reindexed traces. -/
theorem good_at_of_good (c : OptimizedProductionChallengeTuple K F)
    (Qc0 : Fin P.computeChip.rap.w → F[X]) (Qm0 : Fin P.memoryChip.rap.w → F[X])
    (hgood : c ∉ P.optimizedFailureEvent Qc0 Qm0) :
    c ∉ P.optimizedFailureEvent (honestQc P c (P.familyQc c Qc0))
        (honestQm P c (P.familyQm c Qm0)) ∧
      FamilyIOGood P c (P.familyQc c Qc0) (P.familyQm c Qm0) := by
  refine ⟨?_, FamilyEnvCore.familyIOGood_of_not_mem P.optimized Qc0 Qm0 c
    (P.optimizedFailureEvent_good_components Qc0 Qm0 c hgood).2.1⟩
  rw [show honestQc P c (P.familyQc c Qc0) = Qc0 from
      FamilyEnvCore.honestQc_familyQc P.optimized c Qc0,
    show honestQm P c (P.familyQm c Qm0) = Qm0 from
      FamilyEnvCore.honestQm_familyQm P.optimized c Qm0]
  exact hgood

end Nock.NockVMROM.Thm54.FamilyChipTwins

/-! ## B. `memory_roots_bound_by_LIO_at` -/

namespace Nock.NockVMROM.Thm54.MemoryWalkRoots

open Nock.NockVMROM.Thm54.FamilyChipTwins

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **Family twin of `memory_roots_bound_by_LIO`, core form** (family-width traces): under
`DeployedAcceptanceAt`, the event at the reindexed traces, `FamilyIOGood` and `rowsBound`, every
`ver`-selected `read_root` row's `x^mem` noun is the root of an active FAMILY request record. -/
theorem memory_roots_bound_by_LIO_of_good_at
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X]) (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K :=
      P.rowsBound)
    (i : Fin (FamilyIOChain.memRows P))
    (hst : memoryStateOf (FamilyIOChain.memEnvF P c Qm i) = .read_root)
    (hver : (FamilyIOChain.memEnvK P c Qm i).trace 39 = 1) :
    ∃ (i' : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnvAt P c Qc i') j = 1 ∧
      memoryPtNoun (FamilyIOChain.memEnvK P c Qm i) =
        ⟨OptimizedComputeHostileAccumulator.rowRecord (rowEnvAt P c Qc i') j 0,
          OptimizedComputeHostileAccumulator.rowRecord (rowEnvAt P c Qc i') j 1,
          OptimizedComputeHostileAccumulator.rowRecord (rowEnvAt P c Qc i') j 2⟩ := by
  have hnoun := read_root_noun_eq_record_root P c Qm hacc.memory_satisfies
    (memStateTagChar_of_package P) i hst
  obtain ⟨i', j, hact, heq⟩ := row_record_is_request_at P c Qc Qm hacc hgood hio
    (OptimizedHostileConfiguration.hchar_of_package P) (hKp_of_rowsBound_at P hrb)
    (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm) i hver
  refine ⟨i', j, hact, ?_⟩
  have hk : ∀ k : Fin 10, (k : ℕ) < 3 →
      (FamilyIOChain.memEnvK P c Qm i).trace (19 + (k : ℕ)) =
        OptimizedComputeHostileAccumulator.rowRecord (rowEnvAt P c Qc i') j k := by
    intro k hk3
    rw [← heq]
    simp [OptimizedMemoryHostileAccumulator.rowRecord, show (k : ℕ) < 8 by omega]
  have hnoun' : memoryPtNoun (FamilyIOChain.memEnvK P c Qm i) =
      memoryMemRoot (FamilyIOChain.memEnvK P c Qm i) := by
    simp only [memoryPtNoun, memoryMemRoot, memEnvK_trace]
    simpa [rowLabelNoun, rowRecordRoot, memoryPtNoun, memoryMemRoot] using hnoun
  rw [hnoun']
  exact ComputeTable.FP.ext (hk 0 (by decide)) (hk 1 (by decide)) (hk 2 (by decide))

/-- **`memory_roots_bound_by_LIO_at`** — the family twin at the capstone's interface: from the
acceptance, `c ∉ optimizedFailureEvent` and the package's `rowsBound` / `stateTagChar` alone, every
`ver`-selected `read_root` row of the reindexed memory trace has its `x^mem` noun equal to the root
of an active family request record of the reindexed compute trace. -/
theorem memory_roots_bound_by_LIO_at
    (c : OptimizedProductionChallengeTuple K F)
    (Qc0 : Fin P.computeChip.rap.w → F[X]) (Qm0 : Fin P.memoryChip.rap.w → F[X])
    (hacc : P.OptimizedProductionAcceptanceAt Qc0 Qm0 c)
    (hgood : c ∉ P.optimizedFailureEvent Qc0 Qm0)
    (i : Fin (FamilyIOChain.memRows P))
    (hst : memoryStateOf (FamilyIOChain.memEnvF P c (P.familyQm c Qm0) i) = .read_root)
    (hver : (FamilyIOChain.memEnvK P c (P.familyQm c Qm0) i).trace 39 = 1) :
    ∃ (i' : Fin (rows P)) (j : Fin 3),
      activeMask (rowEnvAt P c (P.familyQc c Qc0) i') j = 1 ∧
      memoryPtNoun (FamilyIOChain.memEnvK P c (P.familyQm c Qm0) i) =
        ⟨OptimizedComputeHostileAccumulator.rowRecord (rowEnvAt P c (P.familyQc c Qc0) i') j 0,
          OptimizedComputeHostileAccumulator.rowRecord (rowEnvAt P c (P.familyQc c Qc0) i') j 1,
          OptimizedComputeHostileAccumulator.rowRecord (rowEnvAt P c (P.familyQc c Qc0) i') j 2⟩ := by
  obtain ⟨hgood', hio⟩ := good_at_of_good P c Qc0 Qm0 hgood
  exact memory_roots_bound_by_LIO_of_good_at P c _ _ (DeployedAcceptanceAt.of_acceptance hacc)
    hgood' hio P.rowsBound i hst hver

/-- **Bridge: the twin gives the ORIGINAL's conclusion, at the original's binders.** -/
theorem memory_roots_bound_by_LIO_at_original
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hacc : P.OptimizedProductionAcceptanceAt Qc (honestQm P c Qm) c)
    (hgood : c ∉ P.optimizedFailureEvent Qc (honestQm P c Qm))
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hst : memoryStateOf (memoryBaseEnvAt P c (honestQm P c Qm) i) = .read_root)
    (hver : (P.memorySourceEnv (honestQm P c Qm) i).trace 39 = 1) :
    ∃ (i' : Fin (OptimizedComputeHostileAccumulator.rows P)) (j : Fin 3),
      OptimizedComputeHostileAccumulator.activeMask
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i') j = 1 ∧
      rowLabelNoun P (honestQm P c Qm) i =
        ⟨OptimizedComputeHostileAccumulator.rowRecord
            (OptimizedComputeHostileAccumulator.rowEnv P Qc i') j 0,
          OptimizedComputeHostileAccumulator.rowRecord
            (OptimizedComputeHostileAccumulator.rowEnv P Qc i') j 1,
          OptimizedComputeHostileAccumulator.rowRecord
            (OptimizedComputeHostileAccumulator.rowEnv P Qc i') j 2⟩ := by
  have hQm : P.familyQm c (honestQm P c Qm) = Qm := FamilyEnvCore.familyQm_honestQm P.optimized c Qm
  have hst' : memoryStateOf (FamilyIOChain.memEnvF P c (P.familyQm c (honestQm P c Qm)) i) =
      .read_root := by rw [hQm]; exact hst
  have hver' : (FamilyIOChain.memEnvK P c (P.familyQm c (honestQm P c Qm)) i).trace 39 = 1 := by
    rw [hQm, memEnvK_trace]; exact hver
  obtain ⟨i', j, hact, hnoun⟩ :=
    memory_roots_bound_by_LIO_at P c Qc (honestQm P c Qm) hacc hgood i hst' hver'
  refine ⟨i', j, by rw [activeMask_rowEnv_eq P c Qc i' j]; exact hact, ?_⟩
  have htr := rowEnv_toSourceEnv_trace P c Qc i'
  rw [hQm] at hnoun
  have hL : rowLabelNoun P (honestQm P c Qm) i = memoryPtNoun (FamilyIOChain.memEnvK P c Qm i) := by
    simp only [rowLabelNoun, memoryPtNoun, memEnvK_trace]
  rw [hL, hnoun]
  exact ComputeTable.FP.ext (rowRecord_root_congr htr.symm j 0)
    (rowRecord_root_congr htr.symm j 1) (rowRecord_root_congr htr.symm j 2)

end Nock.NockVMROM.Thm54.MemoryWalkRoots

/-! ## C. `response_ts_mem_powers_at` (+ `_of_two`) -/

namespace Nock.NockVMROM.Thm54.ResponseTsMemPowers

open Nock.NockVMROM.Thm54.FamilyChipTwins

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **Family twin of `response_ts_mem_powers`, core form** (family-width traces): every family
response record's timestamp is an `alphaM c.1`-power below the order, under `alphaM c.1 ≠ 0` (the
original's own side condition).  Directly from the family chip: `ts = alphaM c.1 ^ natLift reqIdx`
(`ts_eq_alpha_pow_natLift_at`); no `chipAlpha = alphaM` pin is needed. -/
theorem response_ts_mem_powers_of_good_at
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X]) (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hio : FamilyIOGood P c Qc Qm)
    (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K :=
      P.rowsBound)
    (hα0 : alphaM c.1 ≠ 0)
    (r : Fin 10 → K) (hr : r ∈ FamilyIOChain.hostileResponsesAt P c Qm) :
    MemPower (alphaM c.1) (recordTs r) := by
  obtain ⟨i, hver, rfl⟩ := mem_hostileResponsesAt P c Qm hr
  have hts := ts_eq_alpha_pow_natLift_at P c Qc Qm hacc hgood hio
    (OptimizedHostileConfiguration.hchar_of_package P) (hKp_of_rowsBound_at P hrb)
    (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm) i hver
  have h7 : recordTs (OptimizedMemoryHostileAccumulator.rowRecord (FamilyIOChain.memEnvK P c Qm i)
      (FamilyIOChain.memEnvF P c Qm i)) = (FamilyIOChain.memEnvK P c Qm i).trace 26 := by
    simp [recordTs, OptimizedMemoryHostileAccumulator.rowRecord]
  rw [h7, hts]
  exact memPower_of_pow hα0 _

/-- **`response_ts_mem_powers_at`** — the family twin at the capstone's interface: from the
acceptance, `c ∉ optimizedFailureEvent`, the package's `rowsBound` / `stateTagChar` and the
original's side condition `alphaM c.1 ≠ 0`, every response record of the reindexed memory trace
has an `alphaM c.1`-power timestamp below the order. -/
theorem response_ts_mem_powers_at
    (c : OptimizedProductionChallengeTuple K F)
    (Qc0 : Fin P.computeChip.rap.w → F[X]) (Qm0 : Fin P.memoryChip.rap.w → F[X])
    (hacc : P.OptimizedProductionAcceptanceAt Qc0 Qm0 c)
    (hgood : c ∉ P.optimizedFailureEvent Qc0 Qm0)
    (hα0 : alphaM c.1 ≠ 0)
    (r : Fin 10 → K) (hr : r ∈ FamilyIOChain.hostileResponsesAt P c (P.familyQm c Qm0)) :
    MemPower (alphaM c.1) (recordTs r) := by
  obtain ⟨hgood', hio⟩ := good_at_of_good P c Qc0 Qm0 hgood
  exact response_ts_mem_powers_of_good_at P c _ _ (DeployedAcceptanceAt.of_acceptance hacc)
    hgood' hio P.rowsBound hα0 r hr

/-- **`response_ts_mem_powers_at_of_two`**: with at least two family requests, `alphaM c.1 ≠ 0` is
discharged from the timestamp-collision component of the event (`timestamp_good_at`). -/
theorem response_ts_mem_powers_at_of_two
    (c : OptimizedProductionChallengeTuple K F)
    (Qc0 : Fin P.computeChip.rap.w → F[X]) (Qm0 : Fin P.memoryChip.rap.w → F[X])
    (hacc : P.OptimizedProductionAcceptanceAt Qc0 Qm0 c)
    (hgood : c ∉ P.optimizedFailureEvent Qc0 Qm0)
    (hD : 2 ≤ (FamilyIOChain.hostileRequestsAt P c (P.familyQc c Qc0)).length)
    (r : Fin 10 → K) (hr : r ∈ FamilyIOChain.hostileResponsesAt P c (P.familyQm c Qm0)) :
    MemPower (alphaM c.1) (recordTs r) := by
  have hα0 : alphaM c.1 ≠ 0 :=
    alpha_ne_zero_of_not_collision
      (timestamp_good_at P c (P.familyQc c Qc0) (P.familyQm c Qm0)
        (good_at_of_good P c Qc0 Qm0 hgood).1) hD
  exact response_ts_mem_powers_at P c Qc0 Qm0 hacc hgood hα0 r hr

/-- **Bridge: the twin gives the ORIGINAL's conclusion, at the original's binders.**  Same `Qc`,
`Qm` (package width), `c`, `hgood`, `hα0`, `r ∈ OptimizedMemoryHostileAccumulator.hostileResponses
P Qm` and the same conclusion as `response_ts_mem_powers`; the historical acceptance, `hio`,
`hchar`, `hKp`, `hKreq`, `hKresp` are replaced by the production acceptance alone.  The family
response list IS the package list at the reindexed trace (`hostileResponsesAt_eq_package`). -/
theorem response_ts_mem_powers_at_original
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedProductionAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hα0 : alphaM c.1 ≠ 0)
    (r : Fin 10 → K)
    (hr : r ∈ OptimizedMemoryHostileAccumulator.hostileResponses P Qm) :
    MemPower (alphaM c.1) (recordTs r) := by
  refine response_ts_mem_powers_at P c Qc Qm hacc hgood hα0 r ?_
  rw [hostileResponsesAt_eq_package, show honestQm P c (P.familyQm c Qm) = Qm from
    FamilyEnvCore.honestQm_familyQm P.optimized c Qm, ← OptimizedHostileIOAssembly.hostileResponses_eq_package]
  exact hr

/-- Bridge for `_of_two`, at the original's binders (`hD` at the package request count, as in
`response_ts_mem_powers_of_two`). -/
theorem response_ts_mem_powers_at_of_two_original
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedProductionAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hD : 2 ≤ (P.hostileRequests Qc).length)
    (r : Fin 10 → K)
    (hr : r ∈ OptimizedMemoryHostileAccumulator.hostileResponses P Qm) :
    MemPower (alphaM c.1) (recordTs r) :=
  response_ts_mem_powers_at_original P Qc Qm c hacc hgood
    (alphaM_ne_zero_of_good_two P Qc Qm c hgood hD) r hr

end Nock.NockVMROM.Thm54.ResponseTsMemPowers

end

#print axioms Nock.NockVMROM.Thm54.MemoryWalkRoots.memory_roots_bound_by_LIO_at
#print axioms Nock.NockVMROM.Thm54.MemoryWalkRoots.memory_roots_bound_by_LIO_at_original
#print axioms Nock.NockVMROM.Thm54.ResponseTsMemPowers.response_ts_mem_powers_at
#print axioms Nock.NockVMROM.Thm54.ResponseTsMemPowers.response_ts_mem_powers_at_of_two
#print axioms Nock.NockVMROM.Thm54.ResponseTsMemPowers.response_ts_mem_powers_at_original
#print axioms Nock.NockVMROM.Thm54.ResponseTsMemPowers.response_ts_mem_powers_at_of_two_original
