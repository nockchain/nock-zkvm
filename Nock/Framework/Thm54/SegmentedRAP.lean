import Nock.Framework
import Nock.AIR
import Nock.Counts

/-!
# Kind-segmented ordinary RAPs

Option E realizes per-kind AIR semantics with four ordinary shipped `RAP`s, each over its own
evaluation domain.  No `RAP`, `RAP.Satisfies`, expression, variable-kind, or trace-column interface
is changed here.
-/

namespace Nock.Framework.Thm54

open Nock Nock.Framework Nock.Framework.Reify Nock.Reified
open scoped Polynomial

variable {F : Type*} [Field F]

/-- Restrict an AIR to constraints of one kind.  Every non-constraint interface field is preserved
definitionally. -/
def kindSeg (air : Reified.AIR) (k : Reified.ConstraintKind) : Reified.AIR :=
  { air with constraints := air.constraints.filter (fun c => c.kind == k) }

@[simp]
theorem kindSeg_numTraceCols (air : Reified.AIR) (k : Reified.ConstraintKind) :
    (kindSeg air k).numTraceCols = air.numTraceCols := rfl

/-- A family of ordinary per-kind RAP satisfaction obligations is exactly pointwise constraint
satisfaction over the domain assigned to each constraint kind. -/
theorem segmented_is_kinded (air : Reified.AIR) (chalVal pubVal : ℕ → F)
    (eDeg hExp : ℕ) (ω β : F) (hβ : β ≠ 0) (hh1 : 1 ≤ hExp)
    (Hof : Reified.ConstraintKind → Finset F) (P : Fin air.numTraceCols → F[X]) :
    (∀ k : Reified.ConstraintKind,
        (airToRAP (kindSeg air k) chalVal pubVal eDeg hExp ω β (Hof k) hβ hh1).Satisfies P)
      ↔ (∀ c ∈ air.constraints, ∀ x ∈ Hof c.kind,
            c.expr.eval (envOfTrace P ω x chalVal pubVal) = 0) := by
  constructor
  · intro h c hc x hx
    have hk := (airToRAP_satisfies_iff (kindSeg air c.kind) chalVal pubVal eDeg hExp ω β
      (Hof c.kind) hβ hh1 P).mp (h c.kind) x hx c ?_
    · exact hk
    · simp only [kindSeg, List.mem_filter]
      exact ⟨hc, by simp⟩
  · intro h k
    refine (airToRAP_satisfies_iff (kindSeg air k) chalVal pubVal eDeg hExp ω β
      (Hof k) hβ hh1 P).mpr ?_
    intro x hx c hc
    simp only [kindSeg, List.mem_filter, beq_iff_eq] at hc
    obtain ⟨hc1, hc2⟩ := hc
    subst hc2
    exact h c hc1 x hx

/-! ## Compute chained-AIR segments -/

set_option maxRecDepth 200000 in
theorem comp_row_seg_is_computeAIR :
    (kindSeg Reified.Trans.computeAIRchained .row).constraints =
      Reified.computeAIR.constraints := by
  rfl

set_option maxRecDepth 200000 in
theorem comp_trans_seg :
    (kindSeg Reified.Trans.computeAIRchained .transition).constraints =
      [⟨.transition, Reified.Trans.lnChainExpr⟩] := by
  rfl

set_option maxRecDepth 200000 in
theorem comp_boundary_terminal_segs_empty :
    (kindSeg Reified.Trans.computeAIRchained .boundary).constraints = [] ∧
      (kindSeg Reified.Trans.computeAIRchained .terminal).constraints = [] := by
  constructor <;> rfl

set_option maxRecDepth 200000 in
theorem comp_seg_counts :
    (kindSeg Reified.Trans.computeAIRchained .row).constraints.length = 526 ∧
      (kindSeg Reified.Trans.computeAIRchained .transition).constraints.length = 1 ∧
      (kindSeg Reified.Trans.computeAIRchained .boundary).constraints.length = 0 ∧
      (kindSeg Reified.Trans.computeAIRchained .terminal).constraints.length = 0 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 200000 in
theorem comp_seg_degrees :
    (kindSeg Reified.Trans.computeAIRchained .row).maxDegree = 4 ∧
      (kindSeg Reified.Trans.computeAIRchained .transition).maxDegree = 1 := by
  constructor <;> rfl

set_option maxRecDepth 200000 in
theorem comp_all_seg_degrees :
    (kindSeg Reified.Trans.computeAIRchained .row).maxDegree = 4 ∧
      (kindSeg Reified.Trans.computeAIRchained .transition).maxDegree = 1 ∧
      (kindSeg Reified.Trans.computeAIRchained .boundary).maxDegree = 0 ∧
      (kindSeg Reified.Trans.computeAIRchained .terminal).maxDegree = 0 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 200000 in
theorem comp_seg_cols :
    (kindSeg Reified.Trans.computeAIRchained .row).numTraceCols = 94 ∧
      (kindSeg Reified.Trans.computeAIRchained .transition).numTraceCols = 94 := by
  constructor <;> rfl

set_option maxRecDepth 200000 in
theorem comp_all_seg_cols :
    (kindSeg Reified.Trans.computeAIRchained .row).numTraceCols = 94 ∧
      (kindSeg Reified.Trans.computeAIRchained .transition).numTraceCols = 94 ∧
      (kindSeg Reified.Trans.computeAIRchained .boundary).numTraceCols = 94 ∧
      (kindSeg Reified.Trans.computeAIRchained .terminal).numTraceCols = 94 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## Memory chained-AIR segments -/

set_option maxRecDepth 200000 in
theorem mem_row_seg_is_memoryAIR :
    (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .row).constraints =
      (Reified.memoryAIR (K := F)).constraints := by
  rfl

set_option maxRecDepth 200000 in
theorem mem_trans_seg :
    (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .transition).constraints =
      [⟨.transition, Reified.Trans.icurChainExpr⟩] := by
  rfl

set_option maxRecDepth 200000 in
theorem mem_boundary_seg :
    (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .boundary).constraints =
      [⟨.boundary, Reified.Trans.memSeedCountsExpr⟩,
        ⟨.boundary, Reified.Trans.memSeedIndicatorExpr⟩,
        ⟨.boundary, Reified.Trans.memIpreInitExpr⟩] := by
  rfl

set_option maxRecDepth 200000 in
theorem mem_terminal_seg :
    (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .terminal).constraints =
      [⟨.terminal, Reified.Trans.memIcurTermExpr⟩] := by
  rfl

set_option maxRecDepth 200000 in
theorem mem_seg_counts :
    (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .row).constraints.length = 75 ∧
      (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .transition).constraints.length = 1 ∧
      (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .boundary).constraints.length = 3 ∧
      (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .terminal).constraints.length = 1 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 200000 in
theorem mem_seg_degrees :
    (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .row).maxDegree = 4 ∧
      (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .transition).maxDegree = 1 ∧
      (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .boundary).maxDegree = 1 := by
  refine ⟨?_, rfl, rfl⟩
  have hrow : (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .row).constraints =
      (Reified.memoryAIR (K := F)).constraints := mem_row_seg_is_memoryAIR
  have hdeg : (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .row).maxDegree =
      (Reified.memoryAIR (K := F)).maxDegree := by
    simp only [Reified.AIR.maxDegree, hrow]
  rw [hdeg]
  exact Reified.memoryAIR_maxDegree

set_option maxRecDepth 200000 in
theorem mem_all_seg_degrees :
    (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .row).maxDegree = 4 ∧
      (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .transition).maxDegree = 1 ∧
      (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .boundary).maxDegree = 1 ∧
      (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .terminal).maxDegree = 1 := by
  refine ⟨mem_seg_degrees.1, rfl, rfl, rfl⟩

set_option maxRecDepth 200000 in
theorem mem_seg_cols :
    (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .row).numTraceCols = 36 ∧
      (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .transition).numTraceCols = 36 ∧
      (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .boundary).numTraceCols = 36 ∧
      (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .terminal).numTraceCols = 36 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## Definitional reuse of shipped RAPs -/

set_option maxRecDepth 200000 in
theorem comp_row_seg_rap_eq (chalVal pubVal : ℕ → F) (eDeg hExp : ℕ) (ω β : F)
    (H : Finset F) (hβ : β ≠ 0) (hh1 : 1 ≤ hExp) :
    airToRAP (kindSeg Reified.Trans.computeAIRchained .row) chalVal pubVal eDeg hExp ω β H hβ hh1
      = airToRAP Reified.computeAIR chalVal pubVal eDeg hExp ω β H hβ hh1 := rfl

set_option maxRecDepth 200000 in
theorem mem_row_seg_rap_eq (chalVal pubVal : ℕ → F) (eDeg hExp : ℕ) (ω β : F)
    (H : Finset F) (hβ : β ≠ 0) (hh1 : 1 ≤ hExp) :
    airToRAP (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .row) chalVal pubVal eDeg hExp ω β H hβ hh1
      = airToRAP (Reified.memoryAIR (K := F)) chalVal pubVal eDeg hExp ω β H hβ hh1 := rfl

set_option maxRecDepth 200000 in
theorem comp_trans_seg_rap_s (chalVal pubVal : ℕ → F) (eDeg hExp : ℕ) (ω β : F)
    (H : Finset F) (hβ : β ≠ 0) (hh1 : 1 ≤ hExp) :
    (airToRAP (kindSeg Reified.Trans.computeAIRchained .transition) chalVal pubVal eDeg hExp ω β H
      hβ hh1).s = 1 := rfl

end Nock.Framework.Thm54

#print axioms Nock.Framework.Thm54.segmented_is_kinded
#print axioms Nock.Framework.Thm54.comp_row_seg_is_computeAIR
#print axioms Nock.Framework.Thm54.comp_seg_counts
#print axioms Nock.Framework.Thm54.mem_row_seg_is_memoryAIR
#print axioms Nock.Framework.Thm54.mem_trans_seg
#print axioms Nock.Framework.Thm54.mem_boundary_seg
#print axioms Nock.Framework.Thm54.mem_terminal_seg
#print axioms Nock.Framework.Thm54.mem_seg_counts
#print axioms Nock.Framework.Thm54.mem_all_seg_degrees
#print axioms Nock.Framework.Thm54.comp_row_seg_rap_eq
#print axioms Nock.Framework.Thm54.mem_row_seg_rap_eq
#print axioms Nock.Framework.Thm54.comp_trans_seg_rap_s
