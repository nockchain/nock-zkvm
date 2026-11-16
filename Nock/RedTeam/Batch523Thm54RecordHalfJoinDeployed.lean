/-
  Nock/RedTeam/Batch523Thm54RecordHalfJoinDeployed.lean

  **`recordHalfJoin_of_deployed` at the committed
  records.**  `optimizedFullStrict_paired_records` identifies every
  `read_root` 8-tuple with a `verify_child` 8-tuple.
  `RecordHalfJoin.placeholder`
  stays `atom 0` in `decodeMemoryRow`; the noun fill is the next
  consumer, not a chip gate.
-/
import Nock.NockVMROM.Thm54.MemoryInternalPole
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding
import Nock.NockVMROM.Thm54.NounRealization
import Nock.RedTeam.Batch514Thm54RecordHalfJoin
import Nock.RedTeam.Batch521Thm54ReadRootImpliesVer
import Nock.RedTeam.Batch522Thm54RemainingActiveMemPower
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch523

open scoped Polynomial
open Polynomial
open Nock
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.MemoryInternalPole
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.RedTeam.Batch514
open Nock.RedTeam.Batch521
open Nock.RedTeam.Batch522

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])

theorem rowRecord_coord
    (i : Fin (rows P)) (k : Fin 9) :
    MemoryInternalPole.rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) k.castSucc =
      if (k : ℕ) < 8 then (rowEnvK P Qm₀ i).trace (19 + (k : ℕ))
      else (rowEnvK P Qm₀ i).trace 57 := by
  have hk := k.isLt
  by_cases h8 : (k : ℕ) < 8
  · simp [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord, h8]
  · have : (k : ℕ) = 8 := by omega
    simp [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord, h8, this]

theorem decodeMem_root_of_rowRecord
    (i : Fin (rows P)) :
    (decodeMemPub P Qm₀ c i).mem.root =
      ⟨(rowEnvK P Qm₀ i).trace 19, (rowEnvK P Qm₀ i).trace 20,
        (rowEnvK P Qm₀ i).trace 21⟩ := by
  have h19 := memorySourceEnvAt_trace_eq_rowEnvK P c Qm₀ i 19 (by omega)
  have h20 := memorySourceEnvAt_trace_eq_rowEnvK P c Qm₀ i 20 (by omega)
  have h21 := memorySourceEnvAt_trace_eq_rowEnvK P c Qm₀ i 21 (by omega)
  simp [decodeMemPub, memoryMemRoot, h19, h20, h21]

theorem decodeMem_child_of_rowRecord
    (i : Fin (rows P)) :
    (decodeMemPub P Qm₀ c i).mem.child =
      ⟨(rowEnvK P Qm₀ i).trace 22, (rowEnvK P Qm₀ i).trace 23,
        (rowEnvK P Qm₀ i).trace 24⟩ := by
  have h22 := memorySourceEnvAt_trace_eq_rowEnvK P c Qm₀ i 22 (by omega)
  have h23 := memorySourceEnvAt_trace_eq_rowEnvK P c Qm₀ i 23 (by omega)
  have h24 := memorySourceEnvAt_trace_eq_rowEnvK P c Qm₀ i 24 (by omega)
  simp [decodeMemPub, memoryMemChild, h22, h23, h24]

theorem decodeMem_ts_of_rowRecord
    (i : Fin (rows P)) :
    (decodeMemPub P Qm₀ c i).mem.ts = (rowEnvK P Qm₀ i).trace 26 := by
  have h26 := memorySourceEnvAt_trace_eq_rowEnvK P c Qm₀ i 26 (by omega)
  simp [decodeMemPub, h26]

/-- Equal committed 8-tuples share both record halves. -/
theorem recordHalfJoin_of_equal_records
    (i j : Fin (rows P))
    (heq : MemoryInternalPole.rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) =
      MemoryInternalPole.rowRecord (rowEnvK P Qm₀ j) (rowEnvF P Qm₀ j)) :
    (decodeMemPub P Qm₀ c i).mem.child = (decodeMemPub P Qm₀ c j).mem.child ∧
      (decodeMemPub P Qm₀ c j).mem.root = (decodeMemPub P Qm₀ c i).mem.root := by
  have hch_i := decodeMem_child_of_rowRecord P c Qm₀ i
  have hch_j := decodeMem_child_of_rowRecord P c Qm₀ j
  have hrt_i := decodeMem_root_of_rowRecord P c Qm₀ i
  have hrt_j := decodeMem_root_of_rowRecord P c Qm₀ j
  have h3 : MemoryInternalPole.rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) 3 =
      MemoryInternalPole.rowRecord (rowEnvK P Qm₀ j) (rowEnvF P Qm₀ j) 3 := by rw [heq]
  have h4 : MemoryInternalPole.rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) 4 =
      MemoryInternalPole.rowRecord (rowEnvK P Qm₀ j) (rowEnvF P Qm₀ j) 4 := by rw [heq]
  have h5 : MemoryInternalPole.rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) 5 =
      MemoryInternalPole.rowRecord (rowEnvK P Qm₀ j) (rowEnvF P Qm₀ j) 5 := by rw [heq]
  have h0 : MemoryInternalPole.rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) 0 =
      MemoryInternalPole.rowRecord (rowEnvK P Qm₀ j) (rowEnvF P Qm₀ j) 0 := by rw [heq]
  have h1 : MemoryInternalPole.rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) 1 =
      MemoryInternalPole.rowRecord (rowEnvK P Qm₀ j) (rowEnvF P Qm₀ j) 1 := by rw [heq]
  have h2 : MemoryInternalPole.rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) 2 =
      MemoryInternalPole.rowRecord (rowEnvK P Qm₀ j) (rowEnvF P Qm₀ j) 2 := by rw [heq]
  constructor
  · rw [hch_i, hch_j]
    apply ComputeTable.FP.ext
    · simpa [MemoryInternalPole.rowRecord,
        OptimizedMemoryHostileAccumulator.memRowRecord, OptimizedMemoryHostileAccumulator.rowRecord] using h3
    · simpa [MemoryInternalPole.rowRecord,
        OptimizedMemoryHostileAccumulator.memRowRecord, OptimizedMemoryHostileAccumulator.rowRecord] using h4
    · simpa [MemoryInternalPole.rowRecord,
        OptimizedMemoryHostileAccumulator.memRowRecord, OptimizedMemoryHostileAccumulator.rowRecord] using h5
  · rw [hrt_j, hrt_i]
    apply ComputeTable.FP.ext
    · simpa [MemoryInternalPole.rowRecord,
        OptimizedMemoryHostileAccumulator.memRowRecord, OptimizedMemoryHostileAccumulator.rowRecord] using h0.symm
    · simpa [MemoryInternalPole.rowRecord,
        OptimizedMemoryHostileAccumulator.memRowRecord, OptimizedMemoryHostileAccumulator.rowRecord] using h1.symm
    · simpa [MemoryInternalPole.rowRecord,
        OptimizedMemoryHostileAccumulator.memRowRecord, OptimizedMemoryHostileAccumulator.rowRecord] using h2.symm

/-- Column 3 one-hot is `verify_child`. -/
theorem sel3_implies_verify_child
    (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm₀)
    (i : Fin (rows P))
    (hchar : MemStateTagChar F)
    (hsel : (rowEnvF P Qm₀ i).trace 3 = 1) :
    memoryStateOf (rowEnvF P Qm₀ i) = .verify_child := by
  have hbase := (row_parts P Qm₀ hsat i).1
  have hpaper : ∀ g ∈ MemoryPaperFactorization.paperBaseGates (F := F),
      g.eval (rowEnvF P Qm₀ i) = 0 := by
    intro g hg
    have hmem : g ∈ OptimizedMemoryGateBasis.baseTransitionGates P.optimized.basis := by
      simp only [OptimizedMemoryGateBasis.baseTransitionGates]
      refine List.mem_append.mpr (Or.inl ?_)
      simpa [MemoryPaperFactorization.paperBaseGates_eq_committed] using hg
    exact hbase g hmem
  obtain ⟨st, hone⟩ :=
    (MemoryPaperFactorization.baseOneHot_of_paperBaseGates
      (rowEnvF P Qm₀ i) hchar hpaper)
  have h3 := hone .verify_child
  simp only [mopCol] at h3
  have hst : st = .verify_child := by
    cases st <;> simp [hsel] at h3 ⊢
  exact (memoryStateOf_eq_of_baseOneHot _ _ hone).trans hst

/-- Every accepted `read_root` record equals some `verify_child` record. -/
theorem exists_paired_verify
    (S : OptimizedFullStrictThm54Statement P)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc₀ Qm₀ c)
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀)
    (hcharF : MemStateTagChar F)
    (hK : rows P < ringChar K)
    (i : Fin (rows P))
    (hri : memoryStateOf (rowEnvF P Qm₀ i) = .read_root) :
    ∃ j : Fin (rows P),
      memoryStateOf (rowEnvF P Qm₀ j) = .verify_child ∧
        MemoryInternalPole.rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) =
          MemoryInternalPole.rowRecord (rowEnvK P Qm₀ j) (rowEnvF P Qm₀ j) := by
  have hsat := hacc.memory_satisfies
  have hsel := read_root_state_implies_sel P Qm₀ hsat i hcharF hri
  have hread := read_root_record_mem_hostileReads P Qm₀ hsat i hsel
  have hperm :=
    optimizedFullStrict_paired_records P Qc₀ Qm₀ c S hacc hgood hK
  have hveri : MemoryInternalPole.rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) ∈
      hostileVerifies P Qm₀ :=
    (List.Perm.mem_iff hperm).1 hread
  simp only [hostileVerifies, List.mem_flatten, List.mem_ofFn] at hveri
  obtain ⟨recs, ⟨j, rfl⟩, hrecs⟩ := hveri
  simp only [rowVerifiesOf] at hrecs
  split_ifs at hrecs with hsel3
  · refine ⟨j, ?_, ?_⟩
    · exact sel3_implies_verify_child P Qm₀ hsat j hcharF hsel3
    · simpa [List.mem_singleton] using hrecs
  · simp at hrecs

/-- **Deployed half-join.**  A `read_root` row and its intermediate-paired
    `verify_child` share both record halves. -/
theorem recordHalfJoin_of_deployed
    (S : OptimizedFullStrictThm54Statement P)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc₀ Qm₀ c)
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀)
    (hcharF : MemStateTagChar F)
    (hK : rows P < ringChar K)
    (i : Fin (rows P))
    (hri : memoryStateOf (rowEnvF P Qm₀ i) = .read_root) :
    ∃ j : Fin (rows P),
      memoryStateOf (rowEnvF P Qm₀ j) = .verify_child ∧
        RecordHalfJoinAt (decodeMemPub P Qm₀ c i) (decodeMemPub P Qm₀ c j) := by
  obtain ⟨j, hvj, heq⟩ :=
    exists_paired_verify P c Qc₀ Qm₀ S hacc hgood hcharF hK i hri
  refine ⟨j, hvj, ?_⟩
  intro _ _ _
  exact recordHalfJoin_of_equal_records P c Qm₀ i j heq

/-- **Exact remaining statement** the chips do not supply: the decoder
    still writes `atom 0` on the paper-`⊥` half. -/
theorem decodeMemoryRow_readRoot_child_is_atom0
    (q : ℕ) (data : DTmem K)
    (child : Nock.Walk.NTree (MState × DTmem K)) :
    ((decodeMemoryRow (K := K) q (.node (.read_root, data) [child])).memoryRecord
      (by simp [decodeMemoryRow, decodeMemoryRowIn_readRoot_state,
        memoryMemRecKind])).child = Noun.atom 0 := by
  simp [decodeMemoryRow, decodeMemoryRowIn, nounByFP_nil]

end Nock.RedTeam.Batch523

#print axioms Nock.RedTeam.Batch523.recordHalfJoin_of_equal_records
#print axioms Nock.RedTeam.Batch523.exists_paired_verify
#print axioms Nock.RedTeam.Batch523.recordHalfJoin_of_deployed
#print axioms Nock.RedTeam.Batch523.decodeMemoryRow_readRoot_child_is_atom0
