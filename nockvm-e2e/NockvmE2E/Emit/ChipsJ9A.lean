/-
  NockvmE2E/Emit/ChipsJ9A.lean

  The J-9 A axis and split chips as emitter specs, with kernel-checked `decodeDag (emitDag spec) = some spec.gates`.
  (The twin compute chip is `Emit/ComputeX9.lean`.)  Both chips read the memory-family challenges
  (`AcceptsJ9A`: `chalsMJ8 δ χ`), so the slot map is `fM`; publics and `𝕂`-roles are the template's own (`id`).
  `splitTemplateJ9` bakes the verifier-written `pubNA = nA` (atom-table row count) into one gate: `splitSpecAt nA`.
-/
import NockvmE2E.Emit.Chips
import Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9
import Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9

set_option autoImplicit false

namespace Nock.Emit

open Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle

def axisTemplate : ChipTemplate Gl := AxisChipJ9.axisTemplateJ9 δ
def splitTemplateAt (nA : ℕ) : ChipTemplate Gl := SplitChipJ9.splitTemplateJ9 δ nA

def axisSpec : TSpec := (TSpec.ofTemplate axisTemplate).rename fM id id
def splitSpecAt (nA : ℕ) : TSpec := (TSpec.ofTemplate (splitTemplateAt nA)).rename fM id id

def emit_axis := emitDag axisSpec
def emit_splitAt (nA : ℕ) := emitDag (splitSpecAt nA)

theorem axisSpec_shape : axisSpec.baseCols.sum + 3 * axisSpec.extCols.sum = 52 ∧
    axisSpec.rounds = 3 ∧ axisSpec.base.length = 35 ∧ axisSpec.mixed.length = 18 := by decide +kernel
theorem splitSpec_shape (nA : ℕ) : (splitSpecAt nA).baseCols.sum + 3 * (splitSpecAt nA).extCols.sum = 90 := by
  simp only [splitSpecAt, TSpec.rename, TSpec.ofTemplate, splitTemplateAt, SplitChipJ9.splitTemplateJ9]
  decide

theorem emit_axis_eq : decodeDag emit_axis = some axisSpec.gates := by decide +kernel

theorem emit_split_at_1 : decodeDag (emit_splitAt 1) = some (splitSpecAt 1).gates := by decide +kernel
theorem emit_split_at_2 : decodeDag (emit_splitAt 2) = some (splitSpecAt 2).gates := by decide +kernel

end Nock.Emit

#print axioms Nock.Emit.emit_axis_eq
#print axioms Nock.Emit.emit_split_at_1
#print axioms Nock.Emit.emit_split_at_2
#print axioms Nock.Emit.axisSpec_shape
