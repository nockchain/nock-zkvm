/-
  Nock/RedTeam/Batch399Thm54MemExponent.lean

  **Memory wrap exponent installed.**

  Live hostile wrap now uses `memExponent α mem.ts` (`StrategyOfTracesCore`).
  Receipts: `memExponent_spec`, active wrap recovers `ts`, padding writes
  zero, `HonestCommitment.memory_specialize_placeholder_eq` still applies
  (not edited).  Vmem case remains (b) (`Batch387.vmemCase_is_b`).
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.RemainingIoObstructions
import Nock.NockVMROM.Thm54.HonestCommitment
import Nock.RedTeam.Batch387Thm54MemoryConjuncts

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch399

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.RemainingIoObstructions

/-- Exponent change is live: wrap takes `α` and stores `memExponent`. -/
theorem wrapMemoryLabel_uses_memExponent
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (α : K) (row : Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K) :
    (wrapMemoryLabel α row).timestamp.recordExponent =
      StrategyOfTracesCore.memExponent α row.2.2.mem.ts :=
  rfl

theorem memExponent_spec_alias
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {α ts : K} (h : ∃ e : ℕ, e < orderOf α ∧ α ^ e = ts) :
    α ^ StrategyOfTracesCore.memExponent α ts = ts :=
  StrategyOfTracesCore.memExponent_spec h

theorem active_ts_recovered_alias
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (α lmb : K) (row : Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K)
    (hact : memoryMemRecKind row.1 = .active)
    (h : ∃ n : ℕ, n < orderOf α ∧ α ^ n = row.2.2.mem.ts) :
    ((wrapMemoryLabel α row).specialize α lmb).2.2.mem.ts = row.2.2.mem.ts :=
  wrapMemory_active_ts_recovered α lmb row hact h

/-- The honest specialize lemma is still the same declaration. -/
theorem memory_specialize_placeholder_eq_untouched :
    ∀ {K : Type} [Field K] {α lmb : K} {stamp : MemoryTimestampRow}
      {r : Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K},
      MemoryTimestampSpecializesAt α stamp r →
        MemoryRowTemplate.specialize ⟨stamp, r⟩ α lmb = MemoryRowTemplate.encodeRow lmb r :=
  fun {_} {_} {_} {_} {_} {_} h =>
    HonestCommitment.memory_specialize_placeholder_eq h

theorem vmemCase_still_b : Nock.RedTeam.Batch387.vmemCase = "b" :=
  Nock.RedTeam.Batch387.vmemCase_is_b

end Nock.RedTeam.Batch399

#print axioms Nock.RedTeam.Batch399.wrapMemoryLabel_uses_memExponent
#print axioms Nock.RedTeam.Batch399.memory_specialize_placeholder_eq_untouched
#print axioms Nock.RedTeam.Batch399.vmemCase_still_b
