/-
  Nock/NockVMROM/Thm54/VclL/Handle/InhabJ8Base.lean

  **The claim and run of THE inhabitant** — `*[[0 0] [0 1]] = [0 0]`,
  no jets (empty registry `R0`), no big atoms.

  * `s0 = [0 0]`, `f0 = [0 1]`, `c0 = ⟨s0, f0, s0⟩`.
  * `t0`: the one-row compute tree (`s0` state, axis `1`); `gen0 : genX R0 1 s0 f0 = some (t0, s0)`.
  * `holds0`: the claim holds (`HoldsN c0`), so the inhabitant is a TRUE claim.
-/
import Nock.Edit.GenX
import Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base

open Nock Nock.Noun Nock.Walk Nock.Jet Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54

/-- The subject (and the result) `[0 0]`. -/
def s0 : Noun := .cell (.atom 0) (.atom 0)
/-- The formula `[0 1]`: Nock 0 at axis `1`. -/
def f0 : Noun := .cell (.atom 0) (.atom 1)
/-- **The claim** `*[[0 0] [0 1]] = [0 0]`. -/
def c0 : P8PublicClaim := ⟨s0, f0, s0⟩

/-- The empty registry (no jets). -/
def R0 : Registry := fun _ => none

/-- The honest compute tree: one `s0` row, no children. -/
def t0 : NTree SkelX := mkX .s0 s0 f0 s0 []

theorem gen0 : genX R0 1 s0 f0 = some (t0, s0) := by
  simp [genX, genComputeSkeletonX, s0, f0, t0, Noun.slot]

theorem c0_subject : c0.subject = s0 := rfl
theorem c0_formula : c0.formula = f0 := rfl
theorem c0_result : c0.result = s0 := rfl

theorem evalN0 : evalN 1 s0 f0 = some s0 := by
  simp [evalN, s0, f0, Noun.slot]

end Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base
