/-
  Nock/NockVMROM/Thm54/BelowDefs/P8Core/WrapFixesVcomp.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/P8Core/WrapFixesVcomp.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.P8Core.StrategyOfTraces

namespace Nock.NockVMROM.Thm54.WrapFixesVcomp

open scoped Polynomial
open Polynomial
open Nock
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.Reified
open Nock.Framework
open MonolithicRAP
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {K : Type} [Field K]

/-- One-hot selectors recover `computeStateOf`. -/
theorem computeStateOf_of_oneHot [DecidableEq K] {env : Env K} {st : State}
    (h : OneHotSelector env st) :
    computeStateOf env = st := by
  have h1 : env.trace 1 = if .s1 = st then 1 else 0 := by simpa [opCol] using h .s1
  have h2 : env.trace 2 = if .s2 = st then 1 else 0 := by simpa [opCol] using h .s2
  have h3 : env.trace 3 = if .s3 = st then 1 else 0 := by simpa [opCol] using h .s3
  have h4 : env.trace 4 = if .s4 = st then 1 else 0 := by simpa [opCol] using h .s4
  have h5 : env.trace 5 = if .s5 = st then 1 else 0 := by simpa [opCol] using h .s5
  have h6 : env.trace 6 = if .s6 = st then 1 else 0 := by simpa [opCol] using h .s6
  have h7 : env.trace 7 = if .s7 = st then 1 else 0 := by simpa [opCol] using h .s7
  have h8 : env.trace 8 = if .s8 = st then 1 else 0 := by simpa [opCol] using h .s8
  have h9 : env.trace 9 = if .s9 = st then 1 else 0 := by simpa [opCol] using h .s9
  have h10 : env.trace 10 = if .cons = st then 1 else 0 := by simpa [opCol] using h .cons
  simp only [computeStateOf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  cases st <;> simp

end Nock.NockVMROM.Thm54.WrapFixesVcomp
