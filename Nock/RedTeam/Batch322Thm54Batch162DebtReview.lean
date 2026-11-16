/-
  Nock/RedTeam/Batch322Thm54Batch162DebtReview.lean

  Paper re-read at source:
  `:1090-1098`, `:1097`, `:1288-1291`, `:1413`, `:1415`, `:1427`,
  `:1429`, `:1431`, `:1728-1801`, `:1737-1738`, `:1751`, `:1850-1868`.

  Every named theorem `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`
  except the `True` / `rfl` pins (axiom-free).
-/
import Nock.RedTeam.Batch162Thm54GeneratedRowHandshake
import Nock.NockVMROM.Thm54.GenericHonestCommitment
import Nock.NockVMROM.Thm54.GenericHonestData
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch322

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.RedTeam.Batch162

noncomputable section

variable {F K : Type} [Field F] 
  [Field K] [Algebra F K]

/-! CY's covered-row handshake elaborates at the signatures
it claims; it does **not** inhabit `SkeletonOperationalPremises`,
`BindComputeRow`, or `Vcomp + hcalls`. Reconstruction of the public
triple / active decomposition / windowed subformula is a 4-conjunct
`And`, not skeleton equality. Memory reconstruction is `memRecSkelOf`,
not `s.memoryRecord`. PRL is the paper; CY's
`1415-1431` range includes the mutated-subject forest (`:1429`) and the
intermediate accumulator (`:1431`). Same conversation produced CY:
this is a compiled scope-attack, not an RTS-1.1 distinct-context flip. -/

/-- Covered row data is `buildCoveredRow.1` -/
def b322_coveredRow_is_buildCoveredRow :=
  @coveredRow_is_buildCoveredRow

/-- Root identification elaborates. Not an inhabitant -/
def b322_covered_root_elaborates :=
  @covered_root_subject_exists

/-- Reconstruction `And`, not skeleton equality -/
def b322_covered_root_is_and :=
  @computeSkeletonOf_covered_root_exists

/-- Seven-field eta on `ComputeRowSkeleton`. CY names four -/
theorem b322_computeRowSkeleton_eta_seven (s : ComputeRowSkeleton) :
    s = { state := s.state
          subject := s.subject
          formula := s.formula
          evaluation := s.evaluation
          decomposition := s.decomposition
          subformula := s.subformula
          memoryRecord := s.memoryRecord } :=
  computeRowSkeleton_eta_seven s

/-- Memory reconstruction is `memRecSkelOf` -/
def b322_memoryRecord_is_memRecSkelOf :=
  @computeSkeletonOf_memoryRecord_is_memRecSkelOf

/-- Residual premises still three fields. Handshake added none. -/
theorem b322_residual_eta_three (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    P = { inactiveDec := P.inactiveDec
          axisAtoms := P.axisAtoms
          q_eq_ringChar := P.q_eq_ringChar } :=
  residualPremises_eta_three_batch162 E P

/-- Not `∀ E, Data E` -/
def b322_not_forall_E_data :=
  @not_forall_E_data_batch162

/-- PRL / IO matching is `:1413`, `:1415`, `:1427`. `:1429` is the
mutated-subject forest; `:1431` is the intermediate accumulator. -/
def b322_prl_locations : True :=
  prl_paper_locations_are_1413_1415_1427

/-- Capstone alias still resolves -/
def b322_capstone_alias :=
  @consumed_capstone_and_alias_remain_frozen_batch162

/-- Accounting pin still elaborates. -/
def b322_eleven_one_two :=
  @independent_exact_eleven_one_two_accounting_batch162

/-- Independence disclosure: CZ's own header says the same conversation
produced CY. -/
def b322_cz_discloses_same_conversation : True := trivial

end

#print axioms b322_coveredRow_is_buildCoveredRow
#print axioms b322_covered_root_elaborates
#print axioms b322_covered_root_is_and
#print axioms b322_computeRowSkeleton_eta_seven
#print axioms b322_memoryRecord_is_memRecSkelOf
#print axioms b322_residual_eta_three
#print axioms b322_not_forall_E_data
#print axioms b322_prl_locations
#print axioms b322_capstone_alias
#print axioms b322_eleven_one_two
#print axioms b322_cz_discloses_same_conversation

end Nock.RedTeam.Batch322
