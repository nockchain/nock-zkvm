/-
  Nock/RedTeam/Batch325Thm54RunBoundedNotTyping.lean

  **`hs` / `hf` measurement (negative).**  A successful `evalGRom` does not
  bound every atom of the subject or of the formula.  `OP_1` returns the
  formula tail unguarded (`GenGuardedRom.lean`); unvisited subject atoms
  are never read.  So `RunBoundedBy` does not imply `BoundedBy`, and
  `hs` / `hf` stay as the paper's typing.
  `RunBoundedBy` is not widened.
-/
import Nock.FieldEmbedding
import Nock.NockVMROM.Thm54.TraceGen.GenGuardedRom

set_option autoImplicit false

namespace Nock.RedTeam.Batch325

open Nock
open Nock.NockVMROM.Thm54.TraceGen

/-- `[1 0]` — `OP_1` constant zero.  Never reads the subject. -/
def constZero : Noun := .cell (.atom 1) (.atom 0)

/-- `[1 100]` — `OP_1` constant 100.  Formula atom `100` is not guarded. -/
def constHundred : Noun := .cell (.atom 1) (.atom 100)

/-- Guarded ROM run that never visits the subject atom `100` -/
theorem b325_grom_unvisited_subject :
    evalGRom 12 1 (.atom 100) constZero = some (.atom 0) := by
  simp [evalGRom, constZero]

/-- The unused subject is not `BoundedBy 12` -/
theorem b325_subject_not_bounded :
    ¬ FieldEmbedding.BoundedBy 12 (.atom 100) := by
  simp [FieldEmbedding.BoundedBy]

/-- Guarded ROM run whose formula tail `100` is returned unguarded. -/
theorem b325_grom_unbounded_formula :
    evalGRom 12 1 (.atom 0) constHundred = some (.atom 100) := by
  simp [evalGRom, constHundred]

/-- The formula `[1 100]` is not `BoundedBy 12` -/
theorem b325_formula_not_bounded :
    ¬ FieldEmbedding.BoundedBy 12 constHundred := by
  simp [FieldEmbedding.BoundedBy, constHundred]

/-- Compiled obstruction: `RunBoundedBy` does not imply `BoundedBy` of
    the subject.  Do not widen `RunBoundedBy` to fake a count. -/
theorem b325_run_not_imp_hs :
    ∃ q fuel s f r,
      evalGRom q fuel s f = some r ∧ ¬ FieldEmbedding.BoundedBy q s :=
  ⟨12, 1, .atom 100, constZero, .atom 0,
    b325_grom_unvisited_subject, b325_subject_not_bounded⟩

/-- Compiled obstruction: `RunBoundedBy` does not imply `BoundedBy` of
    the formula -/
theorem b325_run_not_imp_hf :
    ∃ q fuel s f r,
      evalGRom q fuel s f = some r ∧ ¬ FieldEmbedding.BoundedBy q f :=
  ⟨12, 1, .atom 0, constHundred, .atom 100,
    b325_grom_unbounded_formula, b325_formula_not_bounded⟩

end Nock.RedTeam.Batch325

#print axioms Nock.RedTeam.Batch325.b325_run_not_imp_hs
#print axioms Nock.RedTeam.Batch325.b325_run_not_imp_hf
