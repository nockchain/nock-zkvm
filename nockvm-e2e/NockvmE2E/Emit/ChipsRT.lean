/-
  Round trips for the non-walk chips (split from Chips.lean to bound the peak memory of the `decide +kernel`s).
-/
import NockvmE2E.Emit.Chips

set_option autoImplicit false

namespace Nock.Emit

open Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.ChipH

theorem emit_jet_eq : decodeDag emit_jet = some jetSpec.gates := by decide +kernel
theorem emit_atom_eq : decodeDag emit_atom = some atomSpec.gates := by decide +kernel
theorem emit_cellKW_eq : decodeDag emit_cellKW = some cellKWSpec.gates := by decide +kernel
theorem emit_compute_eq : decodeDag emit_compute = some computeSpec.gates := by decide +kernel

/-- The jet chip's 26 gates (4 base + 22 `𝕂`-valued, D5 census). -/
theorem emit_jet_count : jetSpec.base.length + jetSpec.mixed.length = 26 := by decide +kernel

/-- `norm` is semantics-preserving, so the decoded (normalised) gates are the chips' gates. -/
theorem emit_norm_sound {K : Type*} [Field K] [Algebra Gl K] (eK : Env K) (eF : Env Gl) (g : MixedExpr Gl) :
    (norm g).eval eK eF = g.eval eK eF := eval_norm eK eF g

end Nock.Emit

#print axioms Nock.Emit.eval_norm
#print axioms Nock.Emit.emit_jet_eq
#print axioms Nock.Emit.emit_atom_eq
#print axioms Nock.Emit.emit_cellKW_eq
#print axioms Nock.Emit.emit_compute_eq
#print axioms Nock.Emit.emit_jet_count
