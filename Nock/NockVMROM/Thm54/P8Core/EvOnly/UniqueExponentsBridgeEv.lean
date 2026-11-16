/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/UniqueExponentsBridgeEv.lean

  The originals are untouched.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.UniqueExponentsBridge
import Nock.NockVMROM.Thm54.P8Core.PlacementABridge
import Nock.NockVMROM.Thm54.P8Core.EvOnly.OptimizedHostileTimestampsEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.FamilyIOChainRouteBEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Nock.NockVMROM.Thm54.UniqueExponentsBridge

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.RedTeam.Batch575 (UniqueExponents)

noncomputable section

section Generic

variable {F K : Type} [Field F] [Field K] [DecidableEq F] {M : ℕ}
variable (envsK : Fin M → Env K) (envsF : Fin M → Env F) (kroots : ℕ)

end Generic

section Family

open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedStrictPackage
open OptimizedStrictFullPackage
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open DeployedChipFamily
open FamilyComputeRows
open FamilyMemoryRows
open FamilyIOChain
open Module
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

section Accepted

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
  (hio : FamilyIOGood P c Qc Qm)
  (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K)
  (hb1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)
include hacc hgood hio hrb hb1

/-- Two selector-`2` family memory rows with one `reqIdx` are one row (route B through `ver`). -/
theorem read_reqIdx_injective_at_ev (i i' : Fin (memRows P))
    (hs : (memEnvF P c Qm i).trace 2 = 1) (hs' : (memEnvF P c Qm i').trace 2 = 1)
    (heq : (memEnvF P c Qm i).trace reqIdxCol = (memEnvF P c Qm i').trace reqIdxCol) :
    i = i' :=
  ver_reqIdx_injective_at_ev P c Qc Qm hacc hgood hio
    (OptimizedHostileConfiguration.hchar_of_package P) (hKp_of_rowsBound_at P hrb)
    (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm) i i'
    (readSel_ver_at P c Qm hacc.memory_satisfies hb1 i hs)
    (readSel_ver_at P c Qm hacc.memory_satisfies hb1 i' hs') heq

omit hb1 in
/-- On a `ver = 1` family row, `natLift reqIdx` determines `reqIdx`. -/
theorem reqIdx_eq_natLift_at_ev (i : Fin (memRows P)) (hver : (memEnvK P c Qm i).trace 39 = 1) :
    (memEnvF P c Qm i).trace reqIdxCol =
      ((RecordCarrier.natLift ((memEnvF P c Qm i).trace reqIdxCol) : ℕ) : F) := by
  obtain ⟨a, j, hact, h1, -, -⟩ :=
    memory_row_bound_at_ev P c Qc Qm hacc hgood hio
      (OptimizedHostileConfiguration.hchar_of_package P) (hKp_of_rowsBound_at P hrb)
      (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm) i hver
  rw [h1, RecordCarrier.natLift_natCast
    (expOfAt_lt_ringChar P c Qc hacc.compute_satisfies
      (OptimizedHostileConfiguration.hchar_of_package P) (hKp_of_rowsBound_at P hrb)
      (hKreq_of_rowsBound_at P c Qc) hact)]

/-- **`read_root` exponent injectivity at the family chip.** -/
theorem expInj_read_at_ev : ExpInjOn (memEnvF P c Qm) .read_root := by
  intro r r' hs hs' he
  have h2 := sel2_of_read hs
  have h2' := sel2_of_read hs'
  have hv := readSel_ver_at P c Qm hacc.memory_satisfies hb1 r h2
  have hv' := readSel_ver_at P c Qm hacc.memory_satisfies hb1 r' h2'
  refine read_reqIdx_injective_at_ev P c Qc Qm hacc hgood hio hrb hb1 r r' h2 h2' ?_
  rw [reqIdx_eq_natLift_at_ev P c Qc Qm hacc hgood hio hrb r hv,
    reqIdx_eq_natLift_at_ev P c Qc Qm hacc hgood hio hrb r' hv']
  unfold rowExp at he
  simp only [reqIdxCol]
  rw [he]

/-- The family read records are nodup. -/
theorem hostileReadsAt_nodup_ev : (hostileReadsAt P c Qm).Nodup := by
  unfold hostileReadsAt
  rw [List.nodup_flatten, List.pairwise_ofFn]
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
    unfold MemoryInternalPole.rowReadsOf
    split_ifs <;> simp
  · intro i i' hii x hx hx'
    unfold MemoryInternalPole.rowReadsOf at hx hx'
    split_ifs at hx hx' with h2 h2'
    · simp only [List.mem_singleton] at hx hx'
      have h9 := congrFun (hx.symm.trans hx') 9
      have heq : (memEnvF P c Qm i).trace reqIdxCol = (memEnvF P c Qm i').trace reqIdxCol := by
        apply (algebraMap F K).injective
        simpa [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord,
          reqIdxCol] using h9
      exact absurd (read_reqIdx_injective_at_ev P c Qc Qm hacc hgood hio hrb hb1 i i' h2 h2' heq)
        (ne_of_lt hii)
    all_goals simp at hx hx'

omit hio hb1 in
/-- Every selector-`3` family row's record is a selector-`2` row's record (`intermediate`). -/
theorem verify_partner_at_ev (i : Fin (memRows P)) (h3 : (memEnvF P c Qm i).trace 3 = 1) :
    ∃ i'' : Fin (memRows P), (memEnvF P c Qm i'').trace 2 = 1 ∧
      MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) =
        MemoryInternalPole.rowRecord (memEnvK P c Qm i'') (memEnvF P c Qm i'') := by
  have hperm := paired_records_of_rowsBound_at_ev P c Qc Qm hacc hgood hrb
  have hmem : MemoryInternalPole.rowRecord (memEnvK P c Qm i) (memEnvF P c Qm i) ∈
      hostileVerifiesAt P c Qm := by
    simp only [hostileVerifiesAt, List.mem_flatten, List.mem_ofFn]
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    simp [MemoryInternalPole.rowVerifiesOf, h3]
  have hread := (List.Perm.mem_iff hperm).2 hmem
  simp only [hostileReadsAt, List.mem_flatten, List.mem_ofFn] at hread
  obtain ⟨l, ⟨i'', rfl⟩, hl⟩ := hread
  unfold MemoryInternalPole.rowReadsOf at hl
  split_ifs at hl with hr
  · simp only [List.mem_singleton] at hl
    exact ⟨i'', hr, hl⟩
  · simp at hl

/-- **`verify_child` exponent injectivity at the family chip.** -/
theorem expInj_verify_at_ev : ExpInjOn (memEnvF P c Qm) .verify_child := by
  intro r r' hs hs' he
  have hsat := hacc.memory_satisfies
  have h3 := verify_sel_at P c Qm hsat r hs
  have h3' := verify_sel_at P c Qm hsat r' hs'
  obtain ⟨a, ha2, hra⟩ := verify_partner_at_ev P c Qc Qm hacc hgood hrb r h3
  obtain ⟨a', ha2', hra'⟩ := verify_partner_at_ev P c Qc Qm hacc hgood hrb r' h3'
  have hslot : ∀ x y : Fin (memRows P),
      MemoryInternalPole.rowRecord (memEnvK P c Qm x) (memEnvF P c Qm x) =
        MemoryInternalPole.rowRecord (memEnvK P c Qm y) (memEnvF P c Qm y) →
      (memEnvF P c Qm x).trace reqIdxCol = (memEnvF P c Qm y).trace reqIdxCol := by
    intro x y hxy
    have h9 := congrFun hxy 9
    apply (algebraMap F K).injective
    simpa [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord,
      reqIdxCol] using h9
  have hva := readSel_ver_at P c Qm hsat hb1 a ha2
  have hva' := readSel_ver_at P c Qm hsat hb1 a' ha2'
  have hq : (memEnvF P c Qm r).trace reqIdxCol = (memEnvF P c Qm r').trace reqIdxCol := by
    rw [hslot r a hra, hslot r' a' hra',
      reqIdx_eq_natLift_at_ev P c Qc Qm hacc hgood hio hrb a hva,
      reqIdx_eq_natLift_at_ev P c Qc Qm hacc hgood hio hrb a' hva', ← hslot r a hra,
      ← hslot r' a' hra']
    unfold rowExp at he
    simp only [reqIdxCol]
    rw [he]
  have haa : a = a' := read_reqIdx_injective_at_ev P c Qc Qm hacc hgood hio hrb hb1 a a' ha2 ha2'
    (by rw [← hslot r a hra, ← hslot r' a' hra']; exact hq)
  subst haa
  have hrec : MemoryInternalPole.rowRecord (memEnvK P c Qm r) (memEnvF P c Qm r) =
      MemoryInternalPole.rowRecord (memEnvK P c Qm r') (memEnvF P c Qm r') := hra.trans hra'.symm
  have hnd : (hostileVerifiesAt P c Qm).Nodup :=
    (List.Perm.nodup_iff (paired_records_of_rowsBound_at_ev P c Qc Qm hacc hgood hrb)).1
      (hostileReadsAt_nodup_ev P c Qc Qm hacc hgood hio hrb hb1)
  have hx : MemoryInternalPole.rowRecord (memEnvK P c Qm r) (memEnvF P c Qm r) ∈
      MemoryInternalPole.rowVerifiesOf (memEnvF P c Qm r) (memEnvK P c Qm r) := by simp [MemoryInternalPole.rowVerifiesOf, h3]
  have hx' : MemoryInternalPole.rowRecord (memEnvK P c Qm r) (memEnvF P c Qm r) ∈
      MemoryInternalPole.rowVerifiesOf (memEnvF P c Qm r') (memEnvK P c Qm r') := by
    rw [hrec]; simp [MemoryInternalPole.rowVerifiesOf, h3']
  exact eq_of_mem_flatten_ofFn_nodup' _ hnd hx hx'

theorem uniqueExponents_decoded_pkg_ev (kroots i : ℕ) :
    UniqueExponents (decodedMTreeOfEnvs (P.memorySourceEnv (honestQm P c Qm))
      (P.memoryBaseEnv (honestQm P c Qm)) kroots i) := by
  have ht : ∀ r, (memEnvF P c Qm r).trace = (P.memoryBaseEnv (honestQm P c Qm) r).trace :=
    fun r => funext fun j => memEnvF_trace P c Qm r j
  exact uniqueExponents_of_expInj _ _ kroots
    (expInjOn_congr (memEnvF P c Qm) ht (expInj_read_at_ev P c Qc Qm hacc hgood hio hrb hb1))
    (expInjOn_congr (memEnvF P c Qm) ht (expInj_verify_at_ev P c Qc Qm hacc hgood hio hrb hb1)) i

end Accepted

end Family

end

end Nock.NockVMROM.Thm54.UniqueExponentsBridge

