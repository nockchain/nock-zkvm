/-
  Nock/NockVMROM/Thm54/P8Core/Batch758Thm54HbindComputeCancel.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch758Thm54HbindComputeCancel`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch758Thm54HbindComputeCancel.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch525Thm54ComputeTreeBinds

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch758

open Nock
open Nock.ComputeTable
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.GlobalCarryRecognizer
variable {K : Type} [Field K] [DecidableEq K]

/-- **`cons` is injective in its tail** once the head's size is non-zero; no hypothesis on `z` (the `z⁻¹` term cancels). -/
theorem cons_right_cancel {z : K} {a b b' : FP K} (ha : a.size ≠ 0)
    (h : FP.cons z a b = FP.cons z a b') : b = b' := by
  have hs := congrArg FP.size h
  have hd := congrArg FP.dyck h
  have hl := congrArg FP.leaf h
  simp only [FP.cons] at hs hd hl
  have haa : a.size * a.size ≠ 0 := mul_ne_zero ha ha
  apply FP.ext
  · exact mul_left_cancel₀ ha hs
  · exact mul_left_cancel₀ haa (add_left_cancel hd)
  · exact mul_left_cancel₀ ha (add_left_cancel hl)

end Nock.RedTeam.Batch758
