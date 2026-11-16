import Nock.NockVMROM.Thm54.ExactOneHot
import Nock.RedTeam.Thm54P3Nonvacuity


namespace Nock.RedTeam.Thm54P5Regression

open scoped Classical

open Nock Nock.ComputeTable
open Nock.NockVMROM.Thm54

abbrev K17 := Nock.RedTeam.Thm54P2Nonvacuity.K17
noncomputable abbrev p3Cfg : ExactConfig K17 K17 :=
  Nock.RedTeam.Thm54P3Nonvacuity.cfg
noncomputable abbrev p3Exec : ExactExecution p3Cfg :=
  Nock.RedTeam.Thm54P3Nonvacuity.exec
local notation "sharedRecord" => Nock.RedTeam.Thm54P2Nonvacuity.sharedRecord
local notation "rowRecord" => Nock.RedTeam.Thm54P2Nonvacuity.rowRecord

noncomputable def productionRealization : OneHotRealization p3Cfg p3Exec :=
  Nock.RedTeam.Thm54P3Nonvacuity.production_chained.oneHotRealization

/-- The concrete active prefixes use the exact configured capacities. -/
theorem production_capacities :
    p3Cfg.compRows ≤ 2 ^ p3Cfg.orbit.h ∧
      p3Cfg.memRows ≤ 2 ^ p3Cfg.orbit.h :=
  productionRealization.active_capacities

/-- The condition-4b no-requesting-action antecedent is explicitly impossible. -/
theorem production_condition4b_antecedent_impossible
    (i : ExactComputeRow p3Cfg) :
    ¬ (∑ action ∈ exactOPIO, actionSelector p3Exec i action) = 0 :=
  productionRealization.condition4.no_zero_opIO_antecedent i

/-- The concrete canonical raw response list contains exactly the one `read_root` record. -/
theorem production_raw_response_singleton :
    p3Exec.rawResponses = [rowRecord] := by
  rw [ExactExecution.rawResponses_eq_memoryRows,
    Nock.RedTeam.Thm54P3Nonvacuity.execution_rows.2]
  rfl

/-- Removing every memory-row occurrence of the emitted record is rejected. -/
theorem production_missing_memory_row_rejected
    (hmissing :
      ∀ i : ExactMemoryRow p3Cfg,
        (exactMemoryPubAt p3Exec i).mem ≠ rowRecord) :
    False := by
  apply productionRealization.missing_memory_row_rejected rowRecord
  · rw [production_raw_response_singleton]
    simp
  · exact hmissing

/-- A concrete record absent from all six actual memory-row `mem` columns. -/
def foreignRecord : MemRec K17 := ⟨0, 0, 0, 2⟩

theorem foreignRecord_not_actual :
    foreignRecord ∉ actualMemoryRecords p3Exec := by
  intro h
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
  fin_cases i
  · rw [Nock.RedTeam.Thm54P3Nonvacuity.memoryPubAt_zero] at hi
    have hts := congrArg (fun r : MemRec K17 => r.ts) hi
    exact (by decide : (0 : K17) ≠ 2) (by
      simpa [foreignRecord, Nock.RedTeam.Thm54P3Nonvacuity.pDummy,
        MemRec.zero] using hts)
  · rw [Nock.RedTeam.Thm54P3Nonvacuity.memoryPubAt_one] at hi
    have hts := congrArg (fun r : MemRec K17 => r.ts) hi
    exact (by decide : (4 : K17) ≠ 2) (by
      simpa [foreignRecord, Nock.RedTeam.Thm54P3Nonvacuity.pRead,
        Nock.RedTeam.Thm54P2Nonvacuity.rowRecord] using hts)
  · rw [Nock.RedTeam.Thm54P3Nonvacuity.memoryPubAt_two] at hi
    have hts := congrArg (fun r : MemRec K17 => r.ts) hi
    exact (by decide : (0 : K17) ≠ 2) (by
      simpa [foreignRecord, Nock.RedTeam.Thm54P3Nonvacuity.pDecomp,
        MemRec.zero] using hts)
  · rw [Nock.RedTeam.Thm54P3Nonvacuity.memoryPubAt_three] at hi
    have hts := congrArg (fun r : MemRec K17 => r.ts) hi
    exact (by decide : (0 : K17) ≠ 2) (by
      simpa [foreignRecord, Nock.RedTeam.Thm54P3Nonvacuity.pHead,
        MemRec.zero] using hts)
  · rw [Nock.RedTeam.Thm54P3Nonvacuity.memoryPubAt_four] at hi
    have hts := congrArg (fun r : MemRec K17 => r.ts) hi
    exact (by decide : (4 : K17) ≠ 2) (by
      simpa [foreignRecord, Nock.RedTeam.Thm54P3Nonvacuity.pVerify,
        Nock.RedTeam.Thm54P2Nonvacuity.rowRecord] using hts)
  · rw [Nock.RedTeam.Thm54P3Nonvacuity.memoryPubAt_five] at hi
    have hts := congrArg (fun r : MemRec K17 => r.ts) hi
    exact (by decide : (0 : K17) ≠ 2) (by
      simpa [foreignRecord, Nock.RedTeam.Thm54P3Nonvacuity.pTail,
        MemRec.zero] using hts)

/-- The official in-place condition rejects the concrete foreign response. -/
theorem production_foreign_response_rejected :
    foreignRecord ∉ p3Exec.rawResponses :=
  productionRealization.foreign_raw_response_rejected foreignRecord foreignRecord_not_actual

/-- Zero padding from the unused compute slots is absent from the emitted request list. -/
theorem production_zero_padding_excluded :
    (MemRec.zero : MemRec K17) ∉ p3Exec.rawRequests := by
  apply zero_padding_not_mem_rawRequests p3Exec
  intro row hrow
  rw [Nock.RedTeam.Thm54P3Nonvacuity.execution_rows.1] at hrow
  simp only [List.mem_singleton] at hrow
  subst row
  simp [NockVM.activeRequestRecords, Nock.RedTeam.Thm54P2Nonvacuity.cLabel,
    Nock.RedTeam.Thm54P2Nonvacuity.cPub,
    Nock.RedTeam.Thm54P2Nonvacuity.sharedRecord_ne_zero]

/-- The two official tagged row domains are both nonempty. -/
theorem production_row_domains_nonempty :
    Nonempty (ExactComputeRow p3Cfg) ∧ Nonempty (ExactMemoryRow p3Cfg) :=
  exactRowDomains_nonempty p3Cfg

#print axioms productionRealization
#print axioms production_condition4b_antecedent_impossible
#print axioms production_missing_memory_row_rejected
#print axioms production_foreign_response_rejected
#print axioms production_zero_padding_excluded
#print axioms production_row_domains_nonempty

end Nock.RedTeam.Thm54P5Regression
