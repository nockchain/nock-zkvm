/-
  Nock/NockVMROM/Thm54/RemainingIoObstructions.lean

  Memory wrap exponent installed.

  Hostile `wrapMemoryLabel α` now stores
  `recordExponent := memExponent α mem.ts`.  On an active row whose
  committed `ts` lies in `⟨α⟩` below `orderOf α`, specialize recovers
  `mem.ts` (`wrap_preserves_mem_ts`).
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts
import Nock.NockVMROM.Thm54.NounRealization
import Nock.NockVMROM.Thm54.HonestCommitment

namespace Nock.NockVMROM.Thm54.RemainingIoObstructions

open Nock
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.HonestCommitment

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

theorem specializeMemRec_active_zero_ts (α : K) (rec : MemRec K) :
    (specializeMemRec α true 0 rec).ts = 1 := by
  simp [specializeMemRec]

theorem wrapMemory_active_ts_recovered [Fintype K] [DecidableEq K]
    (α lmb : K) (row : MemoryTable.MState × MemoryTable.DTmem K)
    (hact : memoryMemRecKind row.1 = .active)
    (h : ∃ n : ℕ, n < orderOf α ∧ α ^ n = row.2.2.mem.ts) :
    ((wrapMemoryLabel α row).specialize α lmb).2.2.mem.ts = row.2.2.mem.ts :=
  wrap_preserves_mem_ts α lmb row hact h

/-- `HonestCommitment.memory_specialize_placeholder_eq` is applied, not
edited: it takes `MemoryTimestampSpecializesAt` as a hypothesis, and the
hostile wrap discharges that hyp via `memExponent`. -/
theorem memory_specialize_placeholder_eq_still_applies :
    ∀ {α lmb : K} {stamp : MemoryTimestampRow}
      {r : MemoryTable.MState × MemoryTable.DTmem K},
      MemoryTimestampSpecializesAt α stamp r →
        MemoryRowTemplate.specialize ⟨stamp, r⟩ α lmb = MemoryRowTemplate.encodeRow lmb r :=
  fun {_} {_} {_} {_} h => HonestCommitment.memory_specialize_placeholder_eq h

end Nock.NockVMROM.Thm54.RemainingIoObstructions
