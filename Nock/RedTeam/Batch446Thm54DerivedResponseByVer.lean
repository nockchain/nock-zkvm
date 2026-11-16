/-
  Nock/RedTeam/Batch446Thm54DerivedResponseByVer.lean

  **`derivedResponseIO` is `ver`-selected.**

  `rawResponses` / `derivedResponseIO` filter on `MemoryTable.responseRecords`
  (`ver`), matching the paper.
-/
import Nock.MemoryTable
import Nock.NockVM
import Nock.NockVMROM.Thm54.Language

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch446

open Nock
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open ExactExecution

#check rawResponses
#check derivedResponseIO
#check responseRecords
#check responseRecords_of_honest_ver

/-- `rawResponses` is definitionally the flatMap of `responseRecords` (ver filter). -/
theorem rawResponses_ver_selected {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.rawResponses =
      exec.memoryRows.flatMap fun row => responseRecords row.2.2 :=
  rawResponses_eq_memoryRows exec

/-- `derivedResponseIO` is the encoded ver-selected list. -/
theorem derivedResponseIO_ver_selected {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.derivedResponseIO =
      exec.memoryRows.flatMap fun row =>
        if row.2.2.ver then [NockVM.encRecC row.2.2.mem row.2.2.cprime] else [] :=
  rfl

def byStateResponseIO {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) : List (Fin 9 → K) :=
  exec.memoryRows.flatMap fun row =>
    match row.2.2.st with
    | .read_root => [NockVM.encRecC row.2.2.mem row.2.2.cprime]
    | .decompose | .halt | .verify_child => []

/-- Per-list form of honest recovery (inducts on the list, not on `exec.memoryRows`). -/
theorem flatMap_responseRecords_of_honest_ver {K : Type} [Field K]
    (l : List (MState × DTmem K))
    (hhon : ∀ row ∈ l, row.2.2.ver = decide (row.2.2.st = MState.read_root)) :
    l.flatMap (fun row => responseRecords row.2.2) =
      l.flatMap fun row =>
        match row.2.2.st with
        | .read_root => [row.2.2.mem]
        | .decompose | .halt | .verify_child => [] := by
  induction l with
  | nil => rfl
  | cons row rest ih =>
    have hr := hhon row (by simp)
    have hrest : ∀ r ∈ rest,
        r.2.2.ver = decide (r.2.2.st = MState.read_root) :=
      fun r hr => hhon r (List.mem_cons_of_mem row hr)
    rw [List.flatMap_cons, List.flatMap_cons, ih hrest,
      responseRecords_of_honest_ver row.2.2 hr]
    cases row.2.2.st <;> rfl

/-- FlatMap of `responseRecords` equals the by-state raw list under honest `ver`. -/
theorem rawResponses_of_honest_ver {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (hhon : ∀ row ∈ exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MState.read_root)) :
    exec.rawResponses =
      exec.memoryRows.flatMap fun row =>
        match row.2.2.st with
        | .read_root => [row.2.2.mem]
        | .decompose | .halt | .verify_child => [] := by
  rw [rawResponses_eq_memoryRows]
  exact flatMap_responseRecords_of_honest_ver exec.memoryRows hhon

theorem flatMap_encRecC_of_honest_ver {K : Type} [Field K]
    (l : List (MState × DTmem K))
    (hhon : ∀ row ∈ l, row.2.2.ver = decide (row.2.2.st = MState.read_root)) :
    l.flatMap (fun row =>
        if row.2.2.ver then [NockVM.encRecC row.2.2.mem row.2.2.cprime] else []) =
      l.flatMap fun row =>
        match row.2.2.st with
        | .read_root => [NockVM.encRecC row.2.2.mem row.2.2.cprime]
        | .decompose | .halt | .verify_child => [] := by
  induction l with
  | nil => rfl
  | cons row rest ih =>
    have hr := hhon row (by simp)
    have hrest : ∀ r ∈ rest,
        r.2.2.ver = decide (r.2.2.st = MState.read_root) :=
      fun r hr => hhon r (List.mem_cons_of_mem row hr)
    simp only [List.flatMap_cons, ih hrest]
    cases hst : row.2.2.st <;> simp [hr, hst]

/-- Under honest `ver` on every memory row, `derivedResponseIO` recovers the by-state list. -/
theorem derivedResponseIO_honest {F K : Type} [Field F] [Field K] [Algebra F K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (hhon : ∀ row ∈ exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MState.read_root)) :
    exec.derivedResponseIO = byStateResponseIO exec := by
  unfold byStateResponseIO ExactExecution.derivedResponseIO
  exact flatMap_encRecC_of_honest_ver exec.memoryRows hhon

end Nock.RedTeam.Batch446

#print axioms Nock.RedTeam.Batch446.rawResponses_ver_selected
#print axioms Nock.RedTeam.Batch446.derivedResponseIO_ver_selected
#print axioms Nock.RedTeam.Batch446.derivedResponseIO_honest
