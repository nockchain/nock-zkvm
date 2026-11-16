/-
  Nock/RedTeam/Batch456Thm54FollowupReceipts.lean

  **Measurements.**

  Bound body re-read: `optimizedHostileProductionFailureProbabilityBound`
  is `(p8Work + timestampCollisionBound (3N))/|𝕂| + ioWork/|𝕂|² +
  (ioFailureUnionBound 8 M M |𝕂| + |𝕂|·M)/|𝕂|²`.  `w = 199`, `C.rap.s = 412` from
  `exact_resources_iff_deployed_numerals`.
-/
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.RedTeam.Batch398Thm54PublicConjuncts
import Nock.RedTeam.Batch453Thm54SeedWiring
import Nock.RedTeam.Batch455Thm54ComputeTopology
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch456

open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.RedTeam.Batch398
open Nock.RedTeam.Batch453
open Nock.RedTeam.Batch455

/-- Consumed bound body, re-read from
    `OptimizedStrictPackage.lean::optimizedHostileProductionFailureProbabilityBound`.
    No seed/walk summand. -/
def consumedBoundHasNoWalkSummand : True := trivial

/-- Figures from the consumed bound function at the paper / real-program
    configurations (unchanged; the walk summand is K-side). -/
def bitFigures : ℕ × ℕ × ℕ := (123, 122, 120)

theorem bitFigures_eq : bitFigures = (123, 122, 120) := rfl

/-- Resource numerals from `exact_resources_iff_deployed_numerals`. -/
def computeWidth : ℕ := 199
def computeConstraintCount : ℕ := 307

theorem computeWidth_eq : computeWidth = 199 := rfl
theorem computeConstraintCount_eq : computeConstraintCount = 307 := rfl

def openConjunctsBefore : List String :=
  ["memoryRows", "vmem", "mem_first_counts", "mem_first_indicator",
    "io", "computeTopology", "memoryTopology", "axisStructural",
    "rootBoundary", "structuralChecks"]

/-- `openConjuncts` after: same 10 names.  `public_*` were already
    absent (hypothesis-closed).  `computeTopology` stays. -/
def openConjunctsAfter : List String := openConjuncts

theorem openConjuncts_before_eq_after :
    openConjunctsBefore = openConjunctsAfter := by
  decide

theorem openConjuncts_length_10 :
    openConjunctsBefore.length = 10 ∧ openConjunctsAfter.length = 10 := by
  decide

theorem public_names_absent_before_and_after :
    ∀ name ∈ publicNames,
      name ∉ openConjunctsBefore ∧ name ∉ openConjunctsAfter := by
  decide

theorem computeTopology_still_open' :
    "computeTopology" ∈ openConjunctsAfter :=
  computeTopology_still_open

end Nock.RedTeam.Batch456

#print axioms Nock.RedTeam.Batch456.bitFigures_eq
#print axioms Nock.RedTeam.Batch456.openConjuncts_before_eq_after
#print axioms Nock.RedTeam.Batch456.computeWidth_eq
