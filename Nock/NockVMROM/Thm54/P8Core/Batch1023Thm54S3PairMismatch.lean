/-
  Nock/NockVMROM/Thm54/P8Core/Batch1023Thm54S3PairMismatch.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch1023Thm54S3PairMismatch`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch1023Thm54S3PairMismatch.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1023

open Nock
open Nock.ComputeTable
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.GlobalCarryRecognizer
variable {K : Type} [Field K] [DecidableEq K]

/-- `cons` is cancellative in its head once the tail's size is nonzero and `z ≠ 0`
(the twin of `Batch758.cons_right_cancel`). -/
theorem cons_left_cancel {z : K} (hz : z ≠ 0) {a a' b : FP K} (hb : b.size ≠ 0)
    (h : FP.cons z a b = FP.cons z a' b) : a = a' := by
  have hs := congrArg FP.size h
  have hd := congrArg FP.dyck h
  have hl := congrArg FP.leaf h
  simp only [FP.cons] at hs hd hl
  have hsize : a.size = a'.size := mul_right_cancel₀ hb hs
  apply FP.ext
  · exact hsize
  · rw [hsize] at hd
    have := add_right_cancel hd
    have := add_right_cancel this
    exact mul_left_cancel₀ hz this
  · rw [hsize] at hl
    exact add_right_cancel hl

end Nock.RedTeam.Batch1023
