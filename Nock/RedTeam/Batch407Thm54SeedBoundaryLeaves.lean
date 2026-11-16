/-
  Nock/RedTeam/Batch407Thm54SeedBoundaryLeaves.lean

  Do not import package73 / K73cubic here — that reintroduces the decide thrash.
-/
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.RedTeam.Batch272Thm54UnanchoredIntermediateEndpoints

set_option autoImplicit false

namespace Nock.RedTeam.Batch407Leaves

open Nock.Reified
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MemoryPaperFactorization
open Nock.RedTeam.Batch272
open Nock.MemoryTable

abbrev F := ZMod 73

/-- Seed-shift roles after Form R (`w = 203`, `extCols 58`, C′ at role `57`).
`pt.counts` (`q = 3`) now reads `25` via the range / `λ` gadget. -/
def isShiftedRole (r : ℕ) : Bool := decide (r = 4 ∨ r = 9 ∨ r = 14 ∨ r = 25)

def leavesM_avoid_shift (g : MixedExpr F) : Bool :=
  (leavesM g).all fun v =>
    ((v.1 != .traceCur && v.1 != .traceNext) || !isShiftedRole v.2)

def leavesMC_base_only (g : MixedExpr F) : Bool :=
  (leavesMC g).all fun v => decide (v.2 < 6)

def readsShiftedRoles (g : MixedExpr F) : Bool :=
  readsRoleM (F := F)  4 g || readsRoleM 9 g || readsRoleM 14 g || readsRoleM 25 g

theorem paperKGates_length_47 : (paperKGates (F := F) (K := F)).length = 49 := by
  set_option maxRecDepth 100000 in decide

/-- The two root-mask gates read physical column `153` (endpoints, not core). -/
theorem paperKGatesCore_base_only :
    (paperKGatesCore (F := F) (K := F)).all
      (fun g => leavesMC_base_only g ||
        (leavesMC g).any (fun v => decide (v.2 = 154)) ||
        (leavesMC g).all (fun v => decide (v.2 < 6 ∨ v.2 = 181))) = true := by
  set_option maxRecDepth 100000 in decide

/-- Nonspecial class indices (paper lists minus `{3,4,9,14,21}`).
`q = 3` is `pt.counts`: dummy T=1 remaining dropped
role `25`, but the class still sits outside this census (C′ / `λ`). -/
def nonspecialClassIndices : List ℕ :=
  (tabVMemClassIndices ++ baseTypedClassIndices ++ bottomPinIndices).filter
    (fun q => !(q = 3 || q = 4 || q = 9 || q = 14 || q = 21))

/-- Form R: the counts class reads shift role `25` (`λ` / remaining-T gadget). -/
theorem class_counts_reads_shift :
    readsShiftedRoles (paperClassGate (F := F) (K := F) 3) = true := by
  set_option maxRecDepth 100000 in decide

theorem nonspecial_classes_avoid :
    nonspecialClassIndices.all
      (fun q => leavesM_avoid_shift (paperClassGate (F := F) (K := F)  q) &&
        leavesMC_base_only (paperClassGate (F := F) (K := F)  q)) = true := by
  set_option maxRecDepth 100000 in decide

theorem nonspecial_classes_not_reads :
    nonspecialClassIndices.all
      (fun q => !readsShiftedRoles (paperClassGate (F := F) (K := F)  q)) = true := by
  set_option maxRecDepth 100000 in decide

theorem class_nonspecial_blind (q : ℕ) (hq : q ∈ nonspecialClassIndices) :
    leavesM_avoid_shift (paperClassGate (F := F) (K := F)  q) = true ∧
      leavesMC_base_only (paperClassGate (F := F) (K := F)  q) = true := by
  have h := (List.all_eq_true.1 nonspecial_classes_avoid) q hq
  simpa [Bool.and_eq_true] using h

theorem named_blind_cons :
    leavesM_avoid_shift (paperConsDyck (F := F) (K := F) ) = true ∧
      leavesMC_base_only (paperConsDyck (F := F) (K := F) ) = true := by
  set_option maxRecDepth 100000 in decide

theorem named_blind_timestamp :
    leavesM_avoid_shift (timestampGate (F := F) (K := F)) = true ∧
      leavesMC_base_only (timestampGate (F := F) (K := F)) = true := by
  set_option maxRecDepth 100000 in decide

theorem named_blind_intermediateChain :
    leavesM_avoid_shift (intermediateChain (F := F) ) = true ∧
      leavesMC_base_only (intermediateChain (F := F) ) = true := by
  set_option maxRecDepth 100000 in decide

theorem named_blind_walkTerminal :
    leavesM_avoid_shift (walkTerminal (F := F) ) = true ∧
      leavesMC_base_only (walkTerminal (F := F) ) = true := by
  set_option maxRecDepth 100000 in decide

/-- Committed in-gate walk (OD / twenty-first): not shift-blind. -/
theorem walkInit_committed_not_shift_blind :
    (walkInitGates (F := F) ).all
      (fun g => leavesM_avoid_shift g && leavesMC_base_only g) = false := by
  set_option maxRecDepth 100000 in decide

theorem walkStep_committed_not_shift_blind :
    (walkStepGates (F := F) ).all
      (fun g => leavesM_avoid_shift g && leavesMC_base_only g) = false := by
  set_option maxRecDepth 100000 in decide

theorem hostedWalkInit_blind :
    (hostedWalkInitGates (F := F) ).all
      (fun g => leavesM_avoid_shift g && leavesMC_base_only g) = true := by
  set_option maxRecDepth 100000 in decide

theorem hostedWalkStep_blind :
    (hostedWalkStepGates (F := F) ).all
      (fun g => leavesM_avoid_shift g && leavesMC_base_only g) = true := by
  set_option maxRecDepth 100000 in decide

/-- `ioCoreGates` minus the denominator pin (last entry). -/
theorem ioCore_prefix_blind :
    (ioCoreGates (F := F) ).dropLast.all
      (fun g => leavesM_avoid_shift g && leavesMC_base_only g) = true := by
  set_option maxRecDepth 100000 in decide

theorem ioCore_length : (ioCoreGates (F := F) ).length = 9 := by
  set_option maxRecDepth 100000 in decide

theorem hostedNewGates_blind :
    (hostedNewGates (F := F) ).all
      (fun g => leavesM_avoid_shift g && leavesMC_base_only g) = true := by
  set_option maxRecDepth 100000 in decide

theorem base_only_of_core (g : MixedExpr F) (hg : g ∈ paperKGatesCore (F := F) (K := F))
    (h154 : (leavesMC g).any (fun v => decide (v.2 = 154)) = false)
    (h181 : (leavesMC g).any (fun v => decide (v.2 = 181)) = false) :
    leavesMC_base_only g = true := by
  have h := (List.all_eq_true.1 paperKGatesCore_base_only) g hg
  simp [h154] at h
  rcases h with h | h
  · exact h
  · simp only [leavesMC_base_only, List.all_eq_true, decide_eq_true_eq]
    intro v hv
    rcases h v.1 v.2 hv with h6 | h181'
    · exact h6
    · exfalso
      have : (leavesMC g).any (fun v => decide (v.2 = 181)) = true :=
        List.any_eq_true.2 ⟨v, hv, by simp [h181']⟩
      rw [h181] at this
      exact Bool.false_ne_true this

end Nock.RedTeam.Batch407Leaves
