/-
  Nock/RedTeam/Batch522Thm54RemainingActiveMemPower.lean

  **`remainingActiveMemPower` without
  `ActiveLblMIsVerSelected`.**

  `verify_child` rows: `optimizedFullStrict_paired_records` identifies
  the record with a `read_root` record, which the gate serves.  Honest `verify_child` has `ver = false`;
  do not prove `ActiveLblMIsVerSelected`.
-/
import Nock.NockVMROM.Thm54.MemoryInternalPole
import Nock.NockVMROM.Thm54.NounRealization
import Nock.NockVMROM.Thm54.ResponseTsMemPowers
import Nock.RedTeam.Batch513Thm54ActiveMemPower
import Nock.RedTeam.Batch521Thm54ReadRootImpliesVer
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch522

open scoped Polynomial
open Polynomial
open Nock
open Nock.IO
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.MemoryInternalPole
open Nock.NockVMROM.Thm54.MemoryPaperFactorization
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.ResponseTsMemPowers
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.RedTeam.Batch509
open Nock.RedTeam.Batch513
open Nock.RedTeam.Batch521
open Module

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm₀)

include hsat

/-- One-hot: `st = verify_child` is column 3. -/
theorem verify_child_state_implies_sel
    (i : Fin (rows P))
    (hchar : MemStateTagChar F)
    (hst : memoryStateOf (rowEnvF P Qm₀ i) = .verify_child) :
    (rowEnvF P Qm₀ i).trace 3 = 1 := by
  have hbase := (row_parts P Qm₀ hsat i).1
  have hpaper : ∀ g ∈ MemoryPaperFactorization.paperBaseGates (F := F),
      g.eval (rowEnvF P Qm₀ i) = 0 := by
    intro g hg
    have hmem : g ∈ baseTransitionGates P.optimized.basis := by
      simp only [baseTransitionGates]
      refine List.mem_append.mpr (Or.inl ?_)
      simpa [MemoryPaperFactorization.paperBaseGates_eq_committed] using hg
    exact hbase g hmem
  obtain ⟨st, hone⟩ := (baseOneHot_of_paperBaseGates (rowEnvF P Qm₀ i) hchar hpaper)
  have hst' : st = .verify_child :=
    (memoryStateOf_eq_of_baseOneHot _ _ hone).symm.trans hst
  simpa [hst', mopCol] using hone .verify_child

theorem verify_child_record_mem_hostileVerifies
    (i : Fin (rows P))
    (hchar : MemStateTagChar F)
    (hst : memoryStateOf (rowEnvF P Qm₀ i) = .verify_child) :
    MemoryInternalPole.rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) ∈ hostileVerifies P Qm₀ := by
  have hsel := verify_child_state_implies_sel P Qm₀ hsat i hchar hst
  simp only [hostileVerifies, List.mem_flatten, List.mem_ofFn]
  refine ⟨_, ⟨i, rfl⟩, ?_⟩
  simp [rowVerifiesOf, hsel]

theorem read_root_record_mem_hostileReads
    (i : Fin (rows P))
    (hsel : (rowEnvF P Qm₀ i).trace 2 = 1) :
    MemoryInternalPole.rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) ∈ hostileReads P Qm₀ := by
  simp only [hostileReads, List.mem_flatten, List.mem_ofFn]
  refine ⟨_, ⟨i, rfl⟩, ?_⟩
  simp [rowReadsOf, hsel]

omit hsat

/-- A `verify_child` record equals some served `read_root` record, so its
    timestamp is an `α`-power. -/
theorem memPower_of_verify_child {Ksz : ℕ}
    (S : OptimizedFullStrictThm54Statement P)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc₀ Qm₀ c)
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀)
    (hio : c.2.1 ∉ FiniteIO.IOFailureEvent (P.hostileRecords Qc₀ Qm₀))
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hcharF : MemStateTagChar F)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (P.hostileRequests Qc₀).length)
    (hKresp : (P.hostileResponses Qm₀).length ≤ Ksz)
    (hα0 : alphaM c.1 ≠ 0)
    (hK : rows P < ringChar K)
    (h1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)
    (i : Fin (rows P))
    (hst : memoryStateOf (rowEnvF P Qm₀ i) = .verify_child) :
    MemPower (alphaM c.1) (lblMAt P Qm₀ c i).2.2.mem.ts := by
  have hsat := hacc.memory_satisfies
  have hperm :=
    optimizedFullStrict_paired_records P Qc₀ Qm₀ c S hacc hgood hK
  have hveri :=
    verify_child_record_mem_hostileVerifies P Qm₀ hsat i hcharF hst
  have hread : MemoryInternalPole.rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) ∈ hostileReads P Qm₀ :=
    (List.Perm.mem_iff hperm).2 hveri
  simp only [hostileReads, List.mem_flatten, List.mem_ofFn] at hread
  obtain ⟨recs, ⟨j, rfl⟩, hrecs⟩ := hread
  simp only [rowReadsOf] at hrecs
  split_ifs at hrecs with hsel
  · have heq : MemoryInternalPole.rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) =
        MemoryInternalPole.rowRecord (rowEnvK P Qm₀ j) (rowEnvF P Qm₀ j) := by
      simpa using hrecs
    have hverj :=
      readRoot_sel_implies_ver1 P Qm₀ hsat j hsel h1
    have hr : MemoryInternalPole.rowRecord (rowEnvK P Qm₀ j) (rowEnvF P Qm₀ j) ∈
        OptimizedMemoryHostileAccumulator.hostileResponses P Qm₀ :=
      ver1_rowRecord_mem_hostileResponses P Qm₀ j hverj
    have hpow :=
      response_ts_mem_powers (Ksz := Ksz) P Qc₀ Qm₀ c hacc hgood hio hchar
        hKp hKreq hKresp hα0
        (MemoryInternalPole.rowRecord (rowEnvK P Qm₀ j) (rowEnvF P Qm₀ j)) hr
    have hts := lblM_mem_ts_eq_rowEnvK P c Qm₀ i
    have htsi : (rowEnvK P Qm₀ i).trace 26 = (rowEnvK P Qm₀ j).trace 26 := by
      have h7 : MemoryInternalPole.rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) 7 =
          MemoryInternalPole.rowRecord (rowEnvK P Qm₀ j) (rowEnvF P Qm₀ j) 7 := by
        rw [heq]
      simpa [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord,
        OptimizedMemoryHostileAccumulator.memRowRecord] using h7
    simpa [hts, recordTs, MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord,
      OptimizedMemoryHostileAccumulator.memRowRecord, htsi] using hpow
  · simp at hrecs

/-- Not `ActiveLblMIsVerSelected`. -/
theorem remainingActiveMemPower_of_deployed {Ksz : ℕ}
    (S : OptimizedFullStrictThm54Statement P)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc₀ Qm₀ c)
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀)
    (hio : c.2.1 ∉ FiniteIO.IOFailureEvent (P.hostileRecords Qc₀ Qm₀))
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hcharF : MemStateTagChar F)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (P.hostileRequests Qc₀).length)
    (hKresp : (P.hostileResponses Qm₀).length ≤ Ksz)
    (hα0 : alphaM c.1 ≠ 0)
    (hK : rows P < ringChar K)
    (h1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0) :
    remainingActiveMemPower P c Qm₀ := by
  intro i hi1 hih hact
  have hlt : i - 1 < P.optimized.family.problem.cfg.memRows := by omega
  have hidx : lblM P Qm₀ c i = lblMAt P Qm₀ c ⟨i - 1, hlt⟩ := by
    simp [lblM, hlt]
  rw [hidx] at hact ⊢
  have hsat := hacc.memory_satisfies
  cases hst : (lblMAt P Qm₀ c ⟨i - 1, hlt⟩).1 with
  | decompose =>
    have hact' : memoryMemRecKind MState.decompose = .active := by
      simpa [hst] using hact
    simp [memoryMemRecKind] at hact'
  | halt =>
    have hact' : memoryMemRecKind MState.halt = .active := by
      simpa [hst] using hact
    simp [memoryMemRecKind] at hact'
  | read_root =>
    have hver :=
      lblM_read_root_implies_ver1 P Qm₀ hsat c ⟨i - 1, hlt⟩ hcharF h1 hst
    exact memPower_of_ver1 (Ksz := Ksz) P c Qc₀ Qm₀ hacc hgood hio hchar
      hKp hKreq hKresp hα0 ⟨i - 1, hlt⟩ hver
  | verify_child =>
    have hstF : memoryStateOf (rowEnvF P Qm₀ ⟨i - 1, hlt⟩) = .verify_child := by
      have hfam := memoryStateOf_family_eq_rowEnvF P Qm₀ hsat c ⟨i - 1, hlt⟩
      simpa [lblMAt, hfam] using hst
    exact memPower_of_verify_child (Ksz := Ksz) P c Qc₀ Qm₀ S hacc hgood hio
      hchar hcharF hKp hKreq hKresp hα0 hK h1 ⟨i - 1, hlt⟩ hstF

end Nock.RedTeam.Batch522

#print axioms Nock.RedTeam.Batch522.verify_child_state_implies_sel
#print axioms Nock.RedTeam.Batch522.memPower_of_verify_child
#print axioms Nock.RedTeam.Batch522.remainingActiveMemPower_of_deployed
