/-
  Nock/RedTeam/Batch513Thm54ActiveMemPower.lean

  **`remainingActiveMemPower` / `TsExists`.**

  Every `ver = 1` memory row's record is a compute request outside the
  priced events (`optimizedFullStrict_hostile_LIO`); every compute
  request timestamp is `ln · α^j` with `ln₀ = 1`
  (`hostile_ln0_eq_one`, `request_ts_mem_powers`).
  `lblM.mem.ts` is `rowRecord` slot 7 (`trace 26`).

  Active (`read_root` / `verify_child`) rows with `ver = 0` are not
  on the response list.  The chips do not pin `active → ver = 1`
  (`Vmem.verBool` is only boolean).  Coverage: **ver-selected
  active rows** close; the remaining statement is
  `ActiveLblMIsVerSelected`.
-/
import Nock.NockVMROM.Thm54.ResponseTsMemPowers
import Nock.NockVMROM.Thm54.HostileRecordLists
import Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.NounRealization
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch509Thm54WrapSpecialize
import Nock.RedTeam.Batch512Thm54MemoryAlphaRecord
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch513

open scoped Polynomial
open Polynomial
open Nock
open Nock.IO
open Nock.Reified
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly
open Nock.NockVMROM.Thm54.ResponseTsMemPowers
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.RedTeam.Batch448
open Nock.RedTeam.Batch509
open Nock.RedTeam.Batch512

/-! ## Ledger stays 5: power hyp not dropped -/

theorem openAfterActivePower_is_five :
    openConjunctsAfterWrap.length = 5 :=
  openConjunctsAfterWrap_length

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])

/-- `lblM.mem.ts` is the memory record's timestamp coordinate
    (`encRec` slot 7 = role 26). -/
theorem lblM_mem_ts_eq_rowRecord
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (lblMAt P Qm₀ c i).2.2.mem.ts =
      rowRecord (memorySourceEnvAt P c Qm₀ i) (memoryBaseEnvAt P c Qm₀ i) 7 := by
  simp [lblMAt, decodeMemPub, rowRecord]

theorem lblM_mem_ts_eq_trace26
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (lblMAt P Qm₀ c i).2.2.mem.ts =
      (memorySourceEnvAt P c Qm₀ i).trace 26 := by
  simp [lblMAt, decodeMemPub]

/-- Family env and raw `rowEnvK` agree on the record timestamp. -/
theorem lblM_mem_ts_eq_rowEnvK
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (lblMAt P Qm₀ c i).2.2.mem.ts = (rowEnvK P Qm₀ i).trace 26 := by
  rw [lblM_mem_ts_eq_trace26]
  exact memorySourceEnvAt_trace_eq_rowEnvK P c Qm₀ i 26 (by norm_num)

theorem rowRecord7_eq_trace26 (envK : Env K) (envF : Env F) :
    rowRecord envK envF 7 = envK.trace 26 :=
  rfl

/-- A `ver = 1` row's record is on the hostile response list. -/
theorem ver1_rowRecord_mem_hostileResponses
    (i : Fin (rows P))
    (hver : (rowEnvK P Qm₀ i).trace 39 = 1) :
    rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) ∈
      OptimizedMemoryHostileAccumulator.hostileResponses P Qm₀ := by
  simp only [OptimizedMemoryHostileAccumulator.hostileResponses,
    List.mem_flatten, List.mem_ofFn]
  refine ⟨_, ⟨i, rfl⟩, ?_⟩
  simp [rowResponses, rowResponseTerms, hver]

/-- **Coverage of this batch.**  Ver-selected active rows: `MemPower`
    from LIO + the line chain.  `ver = 0` active rows are not on
    `hostileResponses`. -/
def ActiveLblMIsVerSelected : Prop :=
  ∀ i : Fin P.optimized.family.problem.cfg.memRows,
    memoryMemRecKind (lblMAt P Qm₀ c i).1 = .active →
      (memorySourceEnvAt P c Qm₀ i).trace 39 = 1

/-- Family `ver` is the raw `rowEnvK` `ver`. -/
theorem ver_family_eq_rowEnvK
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (memorySourceEnvAt P c Qm₀ i).trace 39 = (rowEnvK P Qm₀ i).trace 39 :=
  memorySourceEnvAt_trace39_eq_rowEnvK P c Qm₀ i

/-- Ver-selected row: `mem.ts` is an `α`-power, from
    `response_ts_mem_powers`. -/
theorem memPower_of_ver1 {Ksz : ℕ}
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc₀ Qm₀ c)
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀)
    (hio : c.2.1 ∉ FiniteIO.IOFailureEvent (P.hostileRecords Qc₀ Qm₀))
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (P.hostileRequests Qc₀).length)
    (hKresp : (P.hostileResponses Qm₀).length ≤ Ksz)
    (hα0 : alphaM c.1 ≠ 0)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hver : (rowEnvK P Qm₀ i).trace 39 = 1) :
    MemPower (alphaM c.1) (lblMAt P Qm₀ c i).2.2.mem.ts := by
  have hts := lblM_mem_ts_eq_rowEnvK P c Qm₀ i
  have hr : rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i) ∈
      OptimizedMemoryHostileAccumulator.hostileResponses P Qm₀ :=
    ver1_rowRecord_mem_hostileResponses P Qm₀ i hver
  have hpow :=
    response_ts_mem_powers (Ksz := Ksz) P Qc₀ Qm₀ c hacc hgood hio hchar
      hKp hKreq hKresp hα0 (rowRecord (rowEnvK P Qm₀ i) (rowEnvF P Qm₀ i)) hr
  simpa [hts, recordTs, rowRecord] using hpow

/-- `remainingActiveMemPower` from LIO once every active `lblM` is
    `ver`-selected. -/
theorem remainingActiveMemPower_of_ver_selected {Ksz : ℕ}
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc₀ Qm₀ c)
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀)
    (hio : c.2.1 ∉ FiniteIO.IOFailureEvent (P.hostileRecords Qc₀ Qm₀))
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (P.hostileRequests Qc₀).length)
    (hKresp : (P.hostileResponses Qm₀).length ≤ Ksz)
    (hα0 : alphaM c.1 ≠ 0)
    (hver : ActiveLblMIsVerSelected P c Qm₀) :
    remainingActiveMemPower P c Qm₀ := by
  intro i hi1 hih hact
  have hlt : i - 1 < P.optimized.family.problem.cfg.memRows := by omega
  have hidx : lblM P Qm₀ c i = lblMAt P Qm₀ c ⟨i - 1, hlt⟩ := by
    simp [lblM, hlt]
  have hact' : memoryMemRecKind (lblMAt P Qm₀ c ⟨i - 1, hlt⟩).1 = .active := by
    simpa [hidx] using hact
  have hverFam := hver ⟨i - 1, hlt⟩ hact'
  have hverRaw : (rowEnvK P Qm₀ ⟨i - 1, hlt⟩).trace 39 = 1 := by
    rw [← ver_family_eq_rowEnvK P c Qm₀ ⟨i - 1, hlt⟩]
    exact hverFam
  rw [hidx]
  exact memPower_of_ver1 (Ksz := Ksz) P c Qc₀ Qm₀ hacc hgood hio hchar
    hKp hKreq hKresp hα0 ⟨i - 1, hlt⟩ hverRaw

/-- **Exact remaining statement** the chips do not supply: `Vmem`
    pins `ver · (ver − 1) = 0`, not `active → ver = 1`.  `ver = 0`
    `read_root` / `verify_child` rows are outside `hostileResponses`,
    so LIO does not price their `mem.ts`. -/
def remainingJoin : Prop :=
  ActiveLblMIsVerSelected P c Qm₀

theorem remainingJoin_is_active_ver :
    remainingJoin P c Qm₀ = ActiveLblMIsVerSelected P c Qm₀ :=
  rfl

end

end Nock.RedTeam.Batch513

#print axioms Nock.RedTeam.Batch513.lblM_mem_ts_eq_rowEnvK
#print axioms Nock.RedTeam.Batch513.ver1_rowRecord_mem_hostileResponses
#print axioms Nock.RedTeam.Batch513.remainingActiveMemPower_of_ver_selected
#print axioms Nock.RedTeam.Batch513.remainingJoin_is_active_ver
