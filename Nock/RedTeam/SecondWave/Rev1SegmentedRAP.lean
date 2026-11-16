/-
  FOURTH-PASS ADVERSARIAL REVIEW of plan §D1b.  Part 1: option E (segmented RAPs).
-/
import Nock.Framework
import Nock.AIR
import Nock.Counts

namespace Rev1

open Nock Nock.Framework Nock.Framework.Reify Nock.Reified
open scoped Polynomial

variable {F : Type*} [Field F]

/-! ## E.  A FIFTH OPTION: per-kind domains via SEGMENTED plain `RAP`s.

  No `VarKind.point`, no selector column, no new structure, no change to `RAP`,
  `RAP.compose`, `RAP.Satisfies`, `exprToMv`, `eval_exprToMv`, or `airToRAP`. -/

/-- Restrict an AIR to the constraints of one kind.  Structure update ⇒ `numTraceCols` is
    definitionally unchanged. -/
def kindSeg (air : Reified.AIR) (k : Reified.ConstraintKind) : Reified.AIR :=
  { air with constraints := air.constraints.filter (fun c => c.kind == k) }

theorem kindSeg_numTraceCols (air : Reified.AIR) (k : Reified.ConstraintKind) :
    (kindSeg air k).numTraceCols = air.numTraceCols := rfl

/-- **THE OPTION-E THEOREM.**  A conjunction of four ordinary `RAP.Satisfies` obligations — one per
    constraint kind, each over its *own* evaluation domain `Hof k` — is EXACTLY the per-constraint
    domain semantics that option D's `KindedRAP`/`Hof` was invented to provide.  Proved from the
    shipped `airToRAP_satisfies_iff` alone. -/
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
    erw [airToRAP_satisfies_iff]
    intro x hx c hc
    simp only [kindSeg, List.mem_filter, beq_iff_eq] at hc
    obtain ⟨hc1, hc2⟩ := hc
    subst hc2
    exact h c hc1 x hx

/-! ## E1.  Measurements: the segments of the chained AIRs.  No column changes, no degree
    changes, and the `.row` segment is *literally the shipped row-local AIR*. -/

set_option maxRecDepth 200000 in
theorem comp_row_seg_is_computeAIR :
    (kindSeg Reified.Trans.computeAIRchained .row).constraints = Reified.computeAIR.constraints := by
  rfl

set_option maxRecDepth 200000 in
theorem comp_trans_seg :
    (kindSeg Reified.Trans.computeAIRchained .transition).constraints
      = [⟨.transition, Reified.Trans.lnChainExpr⟩] := by rfl

set_option maxRecDepth 200000 in
theorem comp_boundary_terminal_segs_empty :
    (kindSeg Reified.Trans.computeAIRchained .boundary).constraints = [] ∧
    (kindSeg Reified.Trans.computeAIRchained .terminal).constraints = [] := by
  constructor <;> rfl

set_option maxRecDepth 200000 in
theorem comp_seg_degrees :
    (kindSeg Reified.Trans.computeAIRchained .row).maxDegree = 4 ∧
    (kindSeg Reified.Trans.computeAIRchained .transition).maxDegree = 1 := by
  constructor <;> rfl

set_option maxRecDepth 200000 in
theorem comp_seg_cols :
    (kindSeg Reified.Trans.computeAIRchained .row).numTraceCols = 94 ∧
    (kindSeg Reified.Trans.computeAIRchained .transition).numTraceCols = 94 := by
  constructor <;> rfl

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
    (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .boundary).maxDegree = 1 ∧
    (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .terminal).maxDegree = 1 := by
  refine ⟨?_, rfl, rfl, rfl⟩
  have hrow : (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .row).constraints =
      (Reified.memoryAIR (K := F)).constraints := by rfl
  have hdeg : (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .row).maxDegree =
      (Reified.memoryAIR (K := F)).maxDegree := by
    simp only [Reified.AIR.maxDegree, hrow]
  rw [hdeg]
  exact memoryAIR_maxDegree

set_option maxRecDepth 200000 in
theorem mem_row_seg_is_memoryAIR :
    (kindSeg (Reified.Trans.memoryAIRchained (K := F)) .row).constraints =
      (Reified.memoryAIR (K := F)).constraints := by
  rfl

/-! ## E2.  Consequence: the whole D1b "bridge" for the compute chip is ONE extra `RAP` with
    `s = 1` and a degree-1 constraint.  The 526-constraint row segment IS the shipped
    `computeAIR`, so `computeTable_reified_iff` discharges it verbatim. -/

set_option maxRecDepth 200000 in
theorem comp_row_seg_rap_eq (chalVal pubVal : ℕ → F) (eDeg hExp : ℕ) (ω β : F)
    (H : Finset F) (hβ : β ≠ 0) (hh1 : 1 ≤ hExp) :
    airToRAP (kindSeg Reified.Trans.computeAIRchained .row) chalVal pubVal eDeg hExp ω β H hβ hh1
      = airToRAP Reified.computeAIR chalVal pubVal eDeg hExp ω β H hβ hh1 := rfl

set_option maxRecDepth 200000 in
theorem comp_trans_seg_rap_s (chalVal pubVal : ℕ → F) (eDeg hExp : ℕ) (ω β : F)
    (H : Finset F) (hβ : β ≠ 0) (hh1 : 1 ≤ hExp) :
    (airToRAP (kindSeg Reified.Trans.computeAIRchained .transition) chalVal pubVal eDeg hExp ω β H
      hβ hh1).s = 1 := rfl

end Rev1

section Audit
#print axioms Rev1.segmented_is_kinded
#print axioms Rev1.comp_row_seg_is_computeAIR
#print axioms Rev1.comp_trans_seg
#print axioms Rev1.comp_boundary_terminal_segs_empty
#print axioms Rev1.comp_seg_degrees
#print axioms Rev1.comp_seg_cols
#print axioms Rev1.mem_seg_counts
#print axioms Rev1.mem_seg_degrees
#print axioms Rev1.mem_row_seg_is_memoryAIR
#print axioms Rev1.comp_row_seg_rap_eq
#print axioms Rev1.comp_trans_seg_rap_s
end Audit
