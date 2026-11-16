/-
  Walk-chip round trips (in the source `Chips.lean`; split out).
-/
import NockvmE2E.Emit.Chips

set_option autoImplicit false

namespace Nock.Emit

open Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.ChipH

/-! ### Walk documents at the run's root counts (S-6)

The only `kroots`-dependence of a walk chip is the numeral in the gate `q - kroots - cL`.  `walkJ8SpecAt k` / `walkAtomSpecAt k` are the same
specs at another numeral; the kernel round trip is proved (`decide +kernel`, no `native_decide`) for EVERY numeral the ten M1-suite programs use:
`walkChipJ8`: kroots ∈ {1, 9, 25, 42, 48, 174} (toy1/mat/cnt/ne5/eq5, add, mul, dec, ack, fib); `walkChipHQK`: krootsV ∈ {1, 2}
(the fixture, ne5; the chip is absent when krootsV = 0).  A ∀ k statement is NOT proved (the numeral is baked into the emitted DAG). -/
def walkJ8SpecAt (k : ℕ) : TSpec := (TSpec.ofTemplate (WalkJ8.walkTemplateJ8 δ k)).rename fM id id
def walkAtomSpecAt (k : ℕ) : TSpec := (TSpec.ofTemplate (CellTwinK.walkTemplateHQK δ k)).rename fM id id

theorem emit_walkAtom_eq : decodeDag emit_walkAtom = some walkAtomSpec.gates := by decide +kernel
theorem emit_walkJ8_eq : decodeDag emit_walkJ8 = some walkJ8Spec.gates := by decide +kernel

theorem emit_walkJ8_at_1 : decodeDag (emitDag (walkJ8SpecAt 1)) = some (walkJ8SpecAt 1).gates := by decide +kernel
theorem emit_walkJ8_at_9 : decodeDag (emitDag (walkJ8SpecAt 9)) = some (walkJ8SpecAt 9).gates := by decide +kernel
theorem emit_walkJ8_at_25 : decodeDag (emitDag (walkJ8SpecAt 25)) = some (walkJ8SpecAt 25).gates := by decide +kernel
theorem emit_walkJ8_at_42 : decodeDag (emitDag (walkJ8SpecAt 42)) = some (walkJ8SpecAt 42).gates := by decide +kernel
theorem emit_walkJ8_at_3 : decodeDag (emitDag (walkJ8SpecAt 3)) = some (walkJ8SpecAt 3).gates := by decide +kernel
theorem emit_walkJ8_at_48: decodeDag (emitDag (walkJ8SpecAt 48)) = some (walkJ8SpecAt 48).gates := by decide +kernel
theorem emit_walkJ8_at_174 : decodeDag (emitDag (walkJ8SpecAt 174)) = some (walkJ8SpecAt 174).gates := by decide +kernel
theorem emit_walkAtom_at_1 : decodeDag (emitDag (walkAtomSpecAt 1)) = some (walkAtomSpecAt 1).gates := by decide +kernel
theorem emit_walkAtom_at_2 : decodeDag (emitDag (walkAtomSpecAt 2)) = some (walkAtomSpecAt 2).gates := by decide +kernel

theorem emit_walkJ8_at_eq : ∀ k ∈ [1, 9, 25, 42, 48, 174],
    decodeDag (emitDag (walkJ8SpecAt k)) = some (walkJ8SpecAt k).gates := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [emit_walkJ8_at_1, emit_walkJ8_at_9, emit_walkJ8_at_25, emit_walkJ8_at_42, emit_walkJ8_at_48, emit_walkJ8_at_174]
theorem emit_walkAtom_at_eq : ∀ k ∈ [1, 2],
    decodeDag (emitDag (walkAtomSpecAt k)) = some (walkAtomSpecAt k).gates := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  exacts [emit_walkAtom_at_1, emit_walkAtom_at_2]

end Nock.Emit

#print axioms Nock.Emit.emit_walkJ8_at_eq
#print axioms Nock.Emit.emit_walkJ8_at_3
#print axioms Nock.Emit.emit_walkAtom_at_eq
#print axioms Nock.Emit.emit_walkJ8_eq
#print axioms Nock.Emit.emit_walkAtom_eq
