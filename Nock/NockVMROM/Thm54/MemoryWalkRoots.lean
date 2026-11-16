/-
  Nock/NockVMROM/Thm54/MemoryWalkRoots.lean

  The memory chip's walk seed `Σ_i RLC^γ(root_i) · α^i` is public role `1`, a
  prover-committed value.  What binds a preloaded root is not the seed but the IO argument: a
  tree's root row is a `read_root` row, `V_mem` pins that row's
  `mem_root` to its `parent` cell (`:2067`), and when the row is `ver`-selected (`:555-557`)
  its record is a memory RESPONSE; hostile LIO
  (`OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO`, at `hostileRecords`) makes
  the response list a permutation of the compute chip's REQUEST list, so the root's `x^mem`
  noun is the root coordinate of some compute row's active request record — the noun the
  compute row's `V_comp` fixes (`ComputeTable.lean::Vcomp`, `mr1 = ((f, f_t), 3, ts)`).

  Landed here: the memory half and the LIO transfer, at the deployed chips.
  * `read_root_noun_eq_record_root` — accepted `read_root` row: `x^mem` noun = record root.
  * `record_mem_hostileResponses` — a `ver = 1` row's record is in the committed response list.
  * `served_root_record_is_request` — by hostile LIO it is in the committed request list.
  * `mem_hostileRequests_iff` — a request is some compute row's active-slot decoded record.
  * `memory_roots_bound_by_LIO` — the assembly.
  Not landed (disclosed, `COMPUTE_ROOT_PIN_REMAINING`): the chip-level bridge from the raw
  request record (`rowRecord`, columns `67 + 8j + c`) to the decoded `Pub.mr_j` of
  `FamilyComputeRows.deployed_row_vcomp_at`, which is where `V_comp` pins the record's root to
  the row's `f`/`s` fingerprint.  The LIO route binds the roots; that bridge is compute-lane
  bookkeeping and not a memory-side obstruction.

  Residual, stated: a root row that is NOT a `ver`-selected `read_root` row emits no response
  (`unserved_row_emits_nothing`) and is bound by nothing here; such a tree is harmless to the
  soundness claim (it serves no request) — it is the paper's `∪ {⊥}³` slack (`:2025`).
-/
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.NockVMROM.Thm54.MemoryFactorizationScope
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.MemoryWalkRoots

open scoped Polynomial
open Polynomial
open Nock
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.MemoryFactorizationScope
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open ComputeTable
open Module

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## The family-chip and package-chip `𝕂` rows agree on every trace column -/

theorem memorySourceEnvAt_trace (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) (j : ℕ) :
    (memorySourceEnvAt P c Qm i).trace j = (P.memorySourceEnv Qm i).trace j := by
  simp only [memorySourceEnvAt, OptimizedFullStrictNockVMROMPackage.memorySourceEnv, gatherEnv,
    memoryBaseEnvAt, OptimizedFullStrictNockVMROMPackage.memoryBaseEnv, envOfTrace]

theorem rowEnvK_eq (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin (OptimizedMemoryHostileAccumulator.rows P)) :
    OptimizedMemoryHostileAccumulator.rowEnvK P Qm i = P.memorySourceEnv Qm i := by
  unfold OptimizedMemoryHostileAccumulator.rowEnvK
    OptimizedFullStrictNockVMROMPackage.memorySourceEnv
  rw [memorySourceTemplate_col0]
  rfl

/-! ## The root row's `x^mem` noun and the record it serves -/

/-- The `x^mem` noun of hostile memory row `i` — roles `0..2`, what the in-gate label RLC reads
(`MemoryWalkLabel.labelCoordAt`). -/
def rowLabelNoun (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : FP K :=
  memoryPtNoun (P.memorySourceEnv Qm i)

/-- The root of the record hostile memory row `i` serves — roles `19..21`. -/
def rowRecordRoot (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : FP K :=
  memoryMemRoot (P.memorySourceEnv Qm i)

theorem rowRecordRoot_eq (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    rowRecordRoot P Qm i =
      ⟨OptimizedMemoryHostileAccumulator.rowRecord
          (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i) (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i) 0,
        OptimizedMemoryHostileAccumulator.rowRecord
          (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i) (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i) 1,
        OptimizedMemoryHostileAccumulator.rowRecord
          (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i) (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i) 2⟩ := by
  simp only [rowRecordRoot, memoryMemRoot, OptimizedMemoryHostileAccumulator.rowRecord,
    rowEnvK_eq]
  rfl

/-- **`:2067` at the deployed chip:** on every accepted `read_root` row the `x^mem` noun (what the
walk commits, `MemoryWalkLabel.labelRLC`) is the served record's root fingerprint. -/
theorem read_root_noun_eq_record_root
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (hchar : MemStateTagChar F)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hst : memoryStateOf (memoryBaseEnvAt P c (honestQm P c Qm) i) = .read_root) :
    rowLabelNoun P (honestQm P c Qm) i = rowRecordRoot P (honestQm P c Qm) i := by
  obtain ⟨st, hone⟩ := baseOneHot_at_family P c Qm hsat i hchar
  have hst' : st = .read_root := (memoryStateOf_eq_of_baseOneHot _ _ hone).symm.trans hst
  subst hst'
  set Qmh := honestQm P c Qm
  set envK := memorySourceEnvAt P c Qmh i
  have hroot0 : envK.trace 19 = envK.trace 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .read_root hone 15 (by decide)
    simp [memQuantity, paddedBlock, blockReadRoot, Expr.subst, memorySubst,
      Expr.eval, mMem, mPt, fpCol, tc, extVar, sub_eq_zero] at h
    exact h
  have hroot1 : envK.trace 20 = envK.trace 1 := by
    have h := paper_qty_vanishes P c Qm hsat i .read_root hone 16 (by decide)
    simp [memQuantity, paddedBlock, blockReadRoot, Expr.subst, memorySubst,
      Expr.eval, mMem, mPt, fpCol, tc, extVar, sub_eq_zero] at h
    exact h
  have hroot2 : envK.trace 21 = envK.trace 2 := by
    have h := paper_qty_vanishes P c Qm hsat i .read_root hone 17 (by decide)
    simp [memQuantity, paddedBlock, blockReadRoot, Expr.subst, memorySubst,
      Expr.eval, mMem, mPt, fpCol, tc, extVar, sub_eq_zero] at h
    exact h
  refine ComputeTable.FP.ext ?_ ?_ ?_
  · simpa [rowLabelNoun, rowRecordRoot, memoryPtNoun, memoryMemRoot,
      memorySourceEnvAt_trace, envK, Qmh] using hroot0.symm
  · simpa [rowLabelNoun, rowRecordRoot, memoryPtNoun, memoryMemRoot,
      memorySourceEnvAt_trace, envK, Qmh] using hroot1.symm
  · simpa [rowLabelNoun, rowRecordRoot, memoryPtNoun, memoryMemRoot,
      memorySourceEnvAt_trace, envK, Qmh] using hroot2.symm

/-! ## The served record is a compute request (hostile LIO) -/

/-- A `ver = 1` row's record is in the committed response list. -/
theorem record_mem_hostileResponses (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hver : (P.memorySourceEnv Qm i).trace 39 = 1) :
    OptimizedMemoryHostileAccumulator.rowRecord
        (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i) (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i) ∈
      OptimizedMemoryHostileAccumulator.hostileResponses P Qm := by
  simp only [OptimizedMemoryHostileAccumulator.hostileResponses, List.mem_flatten, List.mem_ofFn]
  refine ⟨_, ⟨i, rfl⟩, ?_⟩
  have hver' : (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i).trace 39 = 1 := by
    rw [rowEnvK_eq]; exact hver
  simp [OptimizedMemoryHostileAccumulator.rowResponses,
    OptimizedMemoryHostileAccumulator.rowResponseTerms, hver']

/-- A row that is not `ver`-selected serves nothing: it is outside the IO argument (and outside
the soundness claim — it answers no request). -/
theorem unserved_row_emits_nothing (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hver : (P.memorySourceEnv Qm i).trace 39 ≠ 1) :
    OptimizedMemoryHostileAccumulator.rowResponses
      (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i) (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i) = [] := by
  have hver' : (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i).trace 39 ≠ 1 := by
    rw [rowEnvK_eq]; exact hver
  simp [OptimizedMemoryHostileAccumulator.rowResponses,
    OptimizedMemoryHostileAccumulator.rowResponseTerms, hver']

/-- **By hostile LIO the served record is a committed compute request.** -/
theorem served_root_record_is_request {Ksz : ℕ}
    (S : OptimizedFullStrictThm54Statement P)
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hio : c.2.1 ∉ FiniteIO.IOFailureEvent (OptimizedHostileIOAssembly.hostileRecords P Qc Qm))
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (OptimizedComputeHostileAccumulator.hostileRequests P Qc).length)
    (hKresp : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).length ≤ Ksz)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hver : (P.memorySourceEnv Qm i).trace 39 = 1) :
    OptimizedMemoryHostileAccumulator.rowRecord
        (OptimizedMemoryHostileAccumulator.rowEnvK P Qm i) (OptimizedMemoryHostileAccumulator.rowEnvF P Qm i) ∈
      OptimizedComputeHostileAccumulator.hostileRequests P Qc := by
  have hlio := optimizedFullStrict_hostile_LIO_historical P Qc Qm c hacc hgood hio hchar hKp hKreq
    hKresp
  exact (List.Perm.mem_iff hlio.2.2).2 (record_mem_hostileResponses P Qm i hver)

/-- A committed compute request is some compute row's active-slot decoded record. -/
theorem mem_hostileRequests_iff (Qc : Fin P.computeChip.rap.w → F[X]) (v : Fin 10 → K) :
    v ∈ OptimizedComputeHostileAccumulator.hostileRequests P Qc ↔
      ∃ (i : Fin (OptimizedComputeHostileAccumulator.rows P)) (j : Fin 3),
        OptimizedComputeHostileAccumulator.activeMask
          (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j = 1 ∧
        v = OptimizedComputeHostileAccumulator.rowRecord
          (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j := by
  simp only [OptimizedComputeHostileAccumulator.hostileRequests, List.mem_flatten, List.mem_ofFn]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, hv⟩
    rw [OptimizedComputeHostileAccumulator.rowRequests, List.mem_filterMap] at hv
    obtain ⟨j, -, hj⟩ := hv
    split_ifs at hj with h
    exact ⟨i, j, h, (Option.some.inj hj).symm⟩
  · rintro ⟨i, j, h, rfl⟩
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    rw [OptimizedComputeHostileAccumulator.rowRequests, List.mem_filterMap]
    exact ⟨j, List.mem_finRange j, by rw [if_pos h]⟩

/-! ## The assembly -/

/-- **`memory_roots_bound_by_LIO`.**  For an accepted trace pair, every `ver`-selected
`read_root` row's `x^mem` noun — the label the in-gate memory walk commits for that tree's
root — is the root coordinate of an active request record of some compute row.  The seed stays
prover-committed; the roots are bound through `:2067` and hostile LIO. -/
theorem memory_roots_bound_by_LIO {Ksz : ℕ}
    (S : OptimizedFullStrictThm54Statement P)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsatAt : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc (honestQm P c Qm) c)
    (hgood : c ∉ P.optimizedFailureEvent Qc (honestQm P c Qm))
    (hio : c.2.1 ∉ FiniteIO.IOFailureEvent
      (OptimizedHostileIOAssembly.hostileRecords P Qc (honestQm P c Qm)))
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hcharF : MemStateTagChar F)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (OptimizedComputeHostileAccumulator.hostileRequests P Qc).length)
    (hKresp : (OptimizedMemoryHostileAccumulator.hostileResponses P (honestQm P c Qm)).length ≤ Ksz)
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
  have hnoun := read_root_noun_eq_record_root P c Qm hsatAt hcharF i hst
  have hmem := served_root_record_is_request P S Qc (honestQm P c Qm) c hacc hgood hio hchar hKp
    hKreq hKresp i hver
  obtain ⟨i', j, hact, heq⟩ := (mem_hostileRequests_iff P Qc _).1 hmem
  refine ⟨i', j, hact, ?_⟩
  rw [hnoun, rowRecordRoot_eq, heq]

/-- **Disclosed, not landed:** the compute-side bookkeeping that turns "the root is an active
request record's root" into "the root is the compute row's `f`/`s` fingerprint" — the bridge
from the raw record columns to `FamilyComputeRows.deployed_row_vcomp_at`'s decoded `Pub.mr_j`,
where `V_comp` pins `mr1 = ((f, f_t), 3, ts)`. -/
def COMPUTE_ROOT_PIN_REMAINING : List String :=
  ["rowRecord (rowEnv P Qc i) j = NockVM.encRec (decodePub (rowEnvAt P c Qc i) st).mr_j",
   "Vcomp at the decoded row pins mr1.root = f (deployed_row_vcomp_at)"]

theorem compute_root_pin_remaining_length : COMPUTE_ROOT_PIN_REMAINING.length = 2 := by decide

end

end Nock.NockVMROM.Thm54.MemoryWalkRoots

#print axioms Nock.NockVMROM.Thm54.MemoryWalkRoots.read_root_noun_eq_record_root
#print axioms Nock.NockVMROM.Thm54.MemoryWalkRoots.memory_roots_bound_by_LIO
