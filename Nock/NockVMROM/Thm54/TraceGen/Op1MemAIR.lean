/-
  Nock/NockVMROM/Thm54/TraceGen/Op1MemAIR.lean

  Phase 1 of the trace-generator track (memory-AIR vertical slice, terminal row).

  The companion to `Op1AIR.lean` for the second chip.  We build that row directly over `F = ZMod 97` and prove — as a *theorem*, not an `#eval` — that
  every constraint of the reified per-row memory AIR `memoryAIR` evaluates to
  zero at the honest witness, via the tight biconditional `memoryAIR_sound`.

  This is the row-local memory chip; the full memory forest builder (matching services by
  fingerprint value, the `AddedRemovedAgain` pairing) is Phase 3b and remains open.
-/
import Nock.AIR
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.Op1Mem

open Nock Nock.MemoryTable Nock.Reified

/-- `ZMod 97` is a field. -/
instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- The Phase-1 slice field. -/
abbrev F : Type := ZMod 97

/-- The memory RAP inputs `(z, β, γ)`: `z = 8`; the LogUp challenges are
    irrelevant to a `halt` row (it touches no live memory record). -/
def memInp : Inputs F := { z := 8, β := 0, γ := 0 }

/-- The terminal `halt` memory row: the parent noun is an atom `(z, 0, ⊥)`,
    both children are null, the served record is `0`, and the LogUp accumulator is unchanged. -/
def memPub : Pub F where
  st := .halt
  pt := { noun := ⟨memInp.z, 0, 0⟩, indicator := 0, counts := 0 }
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := ComputeTable.MemRec.zero
  ipre := 0
  icur := 0

/-- The LogUp inverse-witness column `g`, unused by a `halt` row. -/
def memG : F := 0

/-- The seed is nonzero. -/
theorem mem_z_ne_zero : memInp.z ≠ 0 := by decide

/-- **The terminal `halt` memory row satisfies `RAP_mem`**: the one-hot
    State-Variables block holds automatically, the `halt` equality block pins the atom shape and
    nulls the children/record, and the `intermediate` accumulator is unchanged. -/
theorem memHalt_rapmem : RAPmem memInp memPub memG := by
  refine ⟨SVsat_holds _, ?_, ?_⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rfl

/-- **Phase-1 deliverable (theorem, not `#eval`).**  Every constraint of the reified per-row
    memory AIR `memoryAIR` evaluates to zero on the
    honest environment of the terminal `halt` row, via `memoryAIR_sound`. -/
theorem memHalt_memoryAIR_zero :
    ∀ c ∈ (memoryAIR (K := F)).constraints,
      c.expr.eval (memoryEnvFull memInp (MemoryTable.opSel memPub.st) memPub memG) = 0 :=
  (memoryAIR_sound memInp memPub memG).mpr ⟨memHalt_rapmem, mem_z_ne_zero⟩

end Nock.NockVMROM.Thm54.TraceGen.Op1Mem
