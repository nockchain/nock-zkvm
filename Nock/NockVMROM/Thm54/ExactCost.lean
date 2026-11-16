import Nock.NockVMROM.Thm54.PlusIOSegmentedRAP
import Nock.NockVMROM.Cost

/-!
# AIR-linked exact cost certificate for the segmented `+IO` construction

This is a certificate for `PlusIOSegmentedFamily`, not a `VMSystem` cost typeclass.  Its six
component records are tied to the exact production AIRs and its widths and RAP metadata are tied
to the supplied family's exact problem.  The two accumulator AIRs remain over `IOField K`.

`AIR.maxDegree` is a computable census of the deep AIR.  The separately recorded `rapDegreeBound`
is only an upper bound on the noncomputable `RAP.d` supremum; no tightness claim is made.
-/

namespace Nock.NockVMROM.Thm54

open Classical
open Nock Framework Framework.Reify Framework.Thm54
open Nock.Reified

variable {K : Type} [Field K]

noncomputable section

set_option maxRecDepth 200000

/-- Reification can cancel terms after challenges are substituted, but it cannot increase degree. -/
theorem exprToMv_totalDegree_le_degree {L : Type*} [Field L] {w : ℕ}
    (chalVal pubVal : ℕ → L) (e : Expr) :
    (exprToMv (w := w) chalVal pubVal e).totalDegree ≤ e.degree := by
  induction e with
  | Var kind i =>
      cases kind with
      | traceCur => simp only [exprToMv, Expr.degree]; split <;> simp
      | traceNext => simp only [exprToMv, Expr.degree]; split <;> simp
      | challenge => exact (MvPolynomial.totalDegree_C (chalVal i)).le
      | publicVal => exact (MvPolynomial.totalDegree_C (pubVal i)).le
  | Const c => exact (MvPolynomial.totalDegree_C (c : L)).le
  | Add a b ha hb => exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max ha hb)
  | Sub a b ha hb => exact (MvPolynomial.totalDegree_sub _ _).trans (max_le_max ha hb)
  | Mul a b ha hb => exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add ha hb)
  | Neg a ha => simpa [exprToMv, Expr.degree] using ha
  | Pow a n ha =>
      refine (MvPolynomial.totalDegree_pow _ _).trans ?_
      cases hdeg : a.degree with
      | zero =>
        have htd : (exprToMv chalVal pubVal a).totalDegree = 0 :=
          le_antisymm (by simpa [hdeg] using ha) (Nat.zero_le _)
        simp [Expr.degree, Expr.powDegree, hdeg, htd]
      | succ d =>
        have hmul : n * (exprToMv chalVal pubVal a).totalDegree ≤ n * (d + 1) :=
          Nat.mul_le_mul_left n (by simpa [hdeg] using ha)
        simpa [Expr.degree, Expr.powDegree, hdeg, Nat.mul_comm] using hmul

private theorem constraint_degree_le_fold (l : List Constraint) {c : Constraint} (h : c ∈ l) :
    c.degree ≤ l.foldr (fun q n => max q.expr.degree n) 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
      simp only [List.foldr, List.mem_cons] at h ⊢
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact (ih h).trans (Nat.le_max_right _ _)

/-- `RAP.d` is bounded by the computable deep-AIR maximum.  This intentionally proves only `≤`. -/
theorem airToRAP_d_le_maxDegree {L : Type*} [Field L] (air : AIR)
    (chalVal pubVal : ℕ → L) (e h : ℕ) (ω β : L) (H : Finset L)
    (hβ : β ≠ 0) (hh : 1 ≤ h) :
    (airToRAP air chalVal pubVal e h ω β H hβ hh).d ≤ air.maxDegree := by
  change Finset.univ.sup (fun i => (airC air chalVal pubVal i).totalDegree) ≤ air.maxDegree
  apply Finset.sup_le
  intro i _
  exact (exprToMv_totalDegree_le_degree chalVal pubVal
    (air.constraints.get i).expr).trans
      (constraint_degree_le_fold air.constraints (List.get_mem air.constraints i))

theorem kindSeg_maxDegree_le (air : AIR) (kind : ConstraintKind) :
    (kindSeg air kind).maxDegree ≤ air.maxDegree := by
  unfold AIR.maxDegree kindSeg
  simp only
  induction air.constraints with
  | nil => simp
  | cons a l ih =>
      simp only [List.filter_cons, List.foldr]
      split
      · exact max_le_max_left _ ih
      · exact ih.trans (Nat.le_max_right _ _)

theorem SegmentedRAPParams.rap_d_le_air_max {L : Type*} [Field L]
    (p : SegmentedRAPParams L) (air : AIR) (kind : ConstraintKind) :
    (p.rap air kind).d ≤ air.maxDegree :=
  (airToRAP_d_le_maxDegree (kindSeg air kind) p.chalVal p.pubVal
    p.eDeg p.hExp p.ω p.βcoset (p.domain kind) p.βcoset_ne_zero p.hExp_pos).trans
      (kindSeg_maxDegree_le air kind)

/-- Complete degree census used by the final certificate. -/
structure DegreeHistogram where
  deg0 : ℕ
  deg1 : ℕ
  deg2 : ℕ
  deg3 : ℕ
  deg4 : ℕ
  degGe5 : ℕ
deriving DecidableEq, Repr

def degreeHistogram (air : AIR) : DegreeHistogram where
  deg0 := air.constraints.countP (fun c => c.degree == 0)
  deg1 := air.constraints.countP (fun c => c.degree == 1)
  deg2 := air.constraints.countP (fun c => c.degree == 2)
  deg3 := air.constraints.countP (fun c => c.degree == 3)
  deg4 := air.constraints.countP (fun c => c.degree == 4)
  degGe5 := air.constraints.countP (fun c => 5 ≤ c.degree)

/-- Every field is independently checked by `ExactCostCertificate`. -/
structure ComponentCost where
  localWidth : ℕ
  constraints : ℕ
  degree4Gates : ℕ
  airMaxDegree : ℕ
  histogram : DegreeHistogram
deriving DecidableEq, Repr

inductive IOLayer
  | separateRatFuncAccumulatorField
deriving DecidableEq, Repr

/-- Final segmented cost data.  This is indexed by no arbitrary VM tag. -/
structure ReifiedFinalCost where
  computeTable : ComponentCost
  computeWalk : ComponentCost
  computeIO : ComponentCost
  memoryTable : ComponentCost
  memoryWalk : ComponentCost
  memoryIO : ComponentCost
  computeDisjointWidth : ℕ
  memoryDisjointWidth : ℕ
  eDeg : ℕ
  rapDegreeBound : ℕ
  ioLayer : IOLayer
deriving DecidableEq, Repr

private def component (width : ℕ) (air : AIR) : ComponentCost where
  localWidth := width
  constraints := air.constraints.length
  degree4Gates := air.constraints.countP (fun c => c.degree == 4)
  airMaxDegree := air.maxDegree
  histogram := degreeHistogram air

/-- The exact data, evaluated from the production AIR objects. -/
def finalSegmentedCost : ReifiedFinalCost where
  computeTable := component 94 Trans.computeAIRchained
  computeWalk := component 6 Trans.walkAIR
  computeIO := component 2 Trans.ioProgAIR
  memoryTable := component 36 (Trans.memoryAIRchained (K := K))
  memoryWalk := component 6 Trans.walkAIR
  memoryIO := component 3 Trans.ioMemAIR
  computeDisjointWidth := 102
  memoryDisjointWidth := 45
  eDeg := 1
  rapDegreeBound := 4
  ioLayer := .separateRatFuncAccumulatorField

/-- Dependent certificate: all RAP equalities mention the supplied exact family `R`, while all
AIR censuses mention the literal production AIR identities.  It cannot be inherited by an
arbitrary or rejecting `VMSystem`. -/
structure ExactCostCertificate {F K : Type} [Field F] [Field K] [Algebra F K]
    (R : PlusIOSegmentedFamily F K) (c : ReifiedFinalCost) : Prop where
  computeTable_width : ∀ kind, c.computeTable.localWidth = (R.computeTableRAP kind).w
  computeWalk_width : ∀ kind, c.computeWalk.localWidth = (R.computeWalkRAP kind).w
  computeIO_width : ∀ kind, c.computeIO.localWidth = (R.computeIORAP kind).w
  memoryTable_width : ∀ kind, c.memoryTable.localWidth = (R.memoryTableRAP kind).w
  memoryWalk_width : ∀ kind, c.memoryWalk.localWidth = (R.memoryWalkRAP kind).w
  memoryIO_width : ∀ kind, c.memoryIO.localWidth = (R.memoryIORAP kind).w
  computeTable_constraints :
    c.computeTable.constraints = Trans.computeAIRchained.constraints.length
  computeWalk_constraints : c.computeWalk.constraints = Trans.walkAIR.constraints.length
  computeIO_constraints : c.computeIO.constraints = Trans.ioProgAIR.constraints.length
  memoryTable_constraints :
    c.memoryTable.constraints = (Trans.memoryAIRchained (K := K)).constraints.length
  memoryWalk_constraints : c.memoryWalk.constraints = Trans.walkAIR.constraints.length
  memoryIO_constraints : c.memoryIO.constraints = Trans.ioMemAIR.constraints.length
  computeTable_deg4 :
    c.computeTable.degree4Gates =
      Trans.computeAIRchained.constraints.countP (fun x => x.degree == 4)
  computeWalk_deg4 :
    c.computeWalk.degree4Gates = Trans.walkAIR.constraints.countP (fun x => x.degree == 4)
  computeIO_deg4 :
    c.computeIO.degree4Gates = Trans.ioProgAIR.constraints.countP (fun x => x.degree == 4)
  memoryTable_deg4 :
    c.memoryTable.degree4Gates =
      (Trans.memoryAIRchained (K := K)).constraints.countP (fun x => x.degree == 4)
  memoryWalk_deg4 :
    c.memoryWalk.degree4Gates = Trans.walkAIR.constraints.countP (fun x => x.degree == 4)
  memoryIO_deg4 :
    c.memoryIO.degree4Gates = Trans.ioMemAIR.constraints.countP (fun x => x.degree == 4)
  computeTable_max : c.computeTable.airMaxDegree = Trans.computeAIRchained.maxDegree
  computeWalk_max : c.computeWalk.airMaxDegree = Trans.walkAIR.maxDegree
  computeIO_max : c.computeIO.airMaxDegree = Trans.ioProgAIR.maxDegree
  memoryTable_max : c.memoryTable.airMaxDegree = (Trans.memoryAIRchained (K := K)).maxDegree
  memoryWalk_max : c.memoryWalk.airMaxDegree = Trans.walkAIR.maxDegree
  memoryIO_max : c.memoryIO.airMaxDegree = Trans.ioMemAIR.maxDegree
  computeTable_hist : c.computeTable.histogram = degreeHistogram Trans.computeAIRchained
  computeWalk_hist : c.computeWalk.histogram = degreeHistogram Trans.walkAIR
  computeIO_hist : c.computeIO.histogram = degreeHistogram Trans.ioProgAIR
  memoryTable_hist : c.memoryTable.histogram = degreeHistogram (Trans.memoryAIRchained (K := K))
  memoryWalk_hist : c.memoryWalk.histogram = degreeHistogram Trans.walkAIR
  memoryIO_hist : c.memoryIO.histogram = degreeHistogram Trans.ioMemAIR
  computeTotal :
    c.computeDisjointWidth = Fintype.card ComputePlusIOColumn
  memoryTotal :
    c.memoryDisjointWidth = Fintype.card MemoryPlusIOColumn
  e_metadata : c.eDeg = R.problem.cfg.eDeg ∧ R.problem.cfg.eDeg = 1
  rap_e_metadata :
    ∀ kind,
      (R.computeTableRAP kind).e = c.eDeg ∧
      (R.computeWalkRAP kind).e = c.eDeg ∧
      (R.computeIORAP kind).e = c.eDeg ∧
      (R.memoryTableRAP kind).e = c.eDeg ∧
      (R.memoryWalkRAP kind).e = c.eDeg ∧
      (R.memoryIORAP kind).e = c.eDeg
  rap_bound_value : c.rapDegreeBound = 4
  rap_d_upper :
    ∀ kind,
      (R.computeTableRAP kind).d ≤ c.rapDegreeBound ∧
      (R.computeWalkRAP kind).d ≤ c.rapDegreeBound ∧
      (R.computeIORAP kind).d ≤ c.rapDegreeBound ∧
      (R.memoryTableRAP kind).d ≤ c.rapDegreeBound ∧
      (R.memoryWalkRAP kind).d ≤ c.rapDegreeBound ∧
      (R.memoryIORAP kind).d ≤ c.rapDegreeBound
  io_layer : c.ioLayer = .separateRatFuncAccumulatorField

/-- The final segmented object has a fully field-by-field exact certificate. -/
theorem finalSegmentedCost_certificate {F K : Type} [Field F] [Field K] [Algebra F K]
    (R : PlusIOSegmentedFamily F K) :
    ExactCostCertificate R (finalSegmentedCost (K := K)) := by
  refine
    { computeTable_width := fun kind => (R.actual_component_widths kind).1.symm
      computeWalk_width := fun kind => (R.actual_component_widths kind).2.1.symm
      computeIO_width := fun kind => (R.actual_component_widths kind).2.2.1.symm
      memoryTable_width := fun kind => (R.actual_component_widths kind).2.2.2.1.symm
      memoryWalk_width := fun kind => (R.actual_component_widths kind).2.2.2.2.1.symm
      memoryIO_width := fun kind => (R.actual_component_widths kind).2.2.2.2.2.symm
      computeTable_constraints := rfl
      computeWalk_constraints := rfl
      computeIO_constraints := rfl
      memoryTable_constraints := rfl
      memoryWalk_constraints := rfl
      memoryIO_constraints := rfl
      computeTable_deg4 := rfl
      computeWalk_deg4 := rfl
      computeIO_deg4 := rfl
      memoryTable_deg4 := rfl
      memoryWalk_deg4 := rfl
      memoryIO_deg4 := rfl
      computeTable_max := rfl
      computeWalk_max := rfl
      computeIO_max := rfl
      memoryTable_max := rfl
      memoryWalk_max := rfl
      memoryIO_max := rfl
      computeTable_hist := rfl
      computeWalk_hist := rfl
      computeIO_hist := rfl
      memoryTable_hist := rfl
      memoryWalk_hist := rfl
      memoryIO_hist := rfl
      computeTotal := compute_disjoint_width.symm
      memoryTotal := memory_disjoint_width.symm
      e_metadata := ?_
      rap_e_metadata := ?_
      rap_bound_value := rfl
      rap_d_upper := ?_
      io_layer := rfl }
  · exact ⟨by simpa [finalSegmentedCost] using R.problem.cfg.eDeg_eq_one.symm,
      R.problem.cfg.eDeg_eq_one⟩
  · intro kind
    simpa only [finalSegmentedCost, component] using
      (show
        (R.computeTableRAP kind).e = 1 ∧
        (R.computeWalkRAP kind).e = 1 ∧
        (R.computeIORAP kind).e = 1 ∧
        (R.memoryTableRAP kind).e = 1 ∧
        (R.memoryWalkRAP kind).e = 1 ∧
        (R.memoryIORAP kind).e = 1 by
          simp only [PlusIOSegmentedFamily.computeTableRAP,
            PlusIOSegmentedFamily.computeWalkRAP,
            PlusIOSegmentedFamily.computeIORAP,
            PlusIOSegmentedFamily.memoryTableRAP,
            PlusIOSegmentedFamily.memoryWalkRAP,
            PlusIOSegmentedFamily.memoryIORAP,
            SegmentedRAPParams.rap, airToRAP, PlusIOSegmentedFamily.computeWalkParams,
            PlusIOSegmentedFamily.memoryWalkParams, PlusIOSegmentedFamily.progIOParams,
            PlusIOSegmentedFamily.memIOParams,
            exactCanonicalProgParams, exactCanonicalMemParams]
          exact ⟨R.problem.cfg.eDeg_eq_one, R.problem.cfg.eDeg_eq_one,
            R.problem.cfg.eDeg_eq_one, R.problem.cfg.eDeg_eq_one,
            R.problem.cfg.eDeg_eq_one, R.problem.cfg.eDeg_eq_one⟩)
  · intro kind
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [finalSegmentedCost, component,
        PlusIOSegmentedFamily.computeTableRAP] using
        ((exactCanonicalProgParams (F := F) (K := K) R.problem).rap_d_le_air_max
          Trans.computeAIRchained kind).trans Trans.computeAIRchained_maxDegree.le
    · simpa only [finalSegmentedCost, component,
        PlusIOSegmentedFamily.computeWalkRAP] using
        (R.computeWalkParams.rap_d_le_air_max Trans.walkAIR kind).trans
          (by rw [Trans.walkAIR_maxDegree]; omega)
    · simpa only [finalSegmentedCost, component,
        PlusIOSegmentedFamily.computeIORAP] using
        (R.progIOParams.rap_d_le_air_max Trans.ioProgAIR kind).trans
          (by rw [Trans.ioProgAIR_maxDegree]; omega)
    · simpa only [finalSegmentedCost, component,
        PlusIOSegmentedFamily.memoryTableRAP] using
        ((exactCanonicalMemParams (F := F) (K := K) R.problem).rap_d_le_air_max
          (Trans.memoryAIRchained (K := K)) kind).trans (Trans.memoryAIRchained_maxDegree (K := K)).le
    · simpa only [finalSegmentedCost, component,
        PlusIOSegmentedFamily.memoryWalkRAP] using
        (R.memoryWalkParams.rap_d_le_air_max Trans.walkAIR kind).trans
          (by rw [Trans.walkAIR_maxDegree]; omega)
    · simpa only [finalSegmentedCost, component,
        PlusIOSegmentedFamily.memoryIORAP] using
        (R.memIOParams.rap_d_le_air_max Trans.ioMemAIR kind).trans
          (by rw [Trans.ioMemAIR_maxDegree]; omega)

/-- **Exact Layer-1 S8 verification.**  Every exact segmented `+IO`
family over `F ⊂ K` carries the literal six-production-AIR certificate at the current
`102/44`, `e = 1` scope.  This proposition is deliberately distinct from the strict monolithic
`199/196`, `e = 3` package claim; `paper_layer_mismatch` records that open R6 boundary. -/
def ExactSegmentedCostVerification (F K : Type) [Field F] [Field K] [Algebra F K] : Prop :=
  ∀ R : PlusIOSegmentedFamily F K, ExactCostCertificate R (finalSegmentedCost (K := K))

/-- The exact segmented Layer-1 S8 claim follows field-by-field from the production AIRs. -/
theorem exactSegmentedCostVerification (F K : Type) [Field F] [Field K] [Algebra F K] :
    ExactSegmentedCostVerification F K :=
  fun R => finalSegmentedCost_certificate R

/-- AIR maxima are exact computable censuses.  They remain `4` for both final sides. -/
theorem final_air_maxima :
    finalSegmentedCost (K := K).computeTable.airMaxDegree = 4 ∧
    finalSegmentedCost (K := K).computeWalk.airMaxDegree = 2 ∧
    finalSegmentedCost (K := K).computeIO.airMaxDegree = 1 ∧
    finalSegmentedCost (K := K).memoryTable.airMaxDegree = 4 ∧
    finalSegmentedCost (K := K).memoryWalk.airMaxDegree = 2 ∧
    finalSegmentedCost (K := K).memoryIO.airMaxDegree = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · simpa [finalSegmentedCost, component] using (Trans.memoryAIRchained_maxDegree (K := K))
  · rfl
  · rfl

/-- Full exact degree histograms, in `(0,1,2,3,4,≥5)` order. -/
theorem final_degree_histograms :
    finalSegmentedCost (K := K).computeTable.histogram = ⟨0, 11, 472, 31, 13, 0⟩ ∧
    finalSegmentedCost (K := K).computeWalk.histogram = ⟨0, 4, 3, 0, 0, 0⟩ ∧
    finalSegmentedCost (K := K).computeIO.histogram = ⟨0, 3, 0, 0, 0, 0⟩ ∧
    finalSegmentedCost (K := K).memoryTable.histogram = degreeHistogram (Trans.memoryAIRchained (K := K)) ∧
    finalSegmentedCost (K := K).memoryWalk.histogram = ⟨0, 4, 3, 0, 0, 0⟩ ∧
    finalSegmentedCost (K := K).memoryIO.histogram = ⟨0, 2, 1, 0, 0, 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- Exact constraint and top-degree-gate counts for all six production AIRs. -/
theorem final_constraint_and_gate_counts :
    (finalSegmentedCost (K := K).computeTable.constraints,
      finalSegmentedCost (K := K).computeTable.degree4Gates) = (527, 13) ∧
    (finalSegmentedCost (K := K).computeWalk.constraints,
      finalSegmentedCost (K := K).computeWalk.degree4Gates) = (7, 0) ∧
    (finalSegmentedCost (K := K).computeIO.constraints,
      finalSegmentedCost (K := K).computeIO.degree4Gates) = (3, 0) ∧
    (finalSegmentedCost (K := K).memoryTable.constraints,
      finalSegmentedCost (K := K).memoryTable.degree4Gates) =
      ((Trans.memoryAIRchained (K := K)).constraints.length,
        (Trans.memoryAIRchained (K := K)).constraints.countP (fun x => x.degree == 4)) ∧
    (finalSegmentedCost (K := K).memoryWalk.constraints,
      finalSegmentedCost (K := K).memoryWalk.degree4Gates) = (7, 0) ∧
    (finalSegmentedCost (K := K).memoryIO.constraints,
      finalSegmentedCost (K := K).memoryIO.degree4Gates) = (3, 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

theorem finalSegmentedCost_localWidths :
    (finalSegmentedCost (K := K)).computeIO.localWidth = 2 ∧
      (finalSegmentedCost (K := K)).memoryIO.localWidth = 3 ∧
      (finalSegmentedCost (K := K)).computeDisjointWidth = 102 ∧
      (finalSegmentedCost (K := K)).memoryDisjointWidth = 45 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

theorem finalSegmentedCost_constraintTotal :
    (finalSegmentedCost (K := K)).computeTable.constraints +
      (finalSegmentedCost (K := K)).computeWalk.constraints +
      (finalSegmentedCost (K := K)).computeIO.constraints +
      (finalSegmentedCost (K := K)).memoryTable.constraints +
      (finalSegmentedCost (K := K)).memoryWalk.constraints +
      (finalSegmentedCost (K := K)).memoryIO.constraints = 627 := by
  simp only [finalSegmentedCost, component]
  rfl

/-- Every field of a component is load-bearing. -/
private theorem ComponentCost.eq_of_fields {a b : ComponentCost}
    (hw : a.localWidth = b.localWidth)
    (hc : a.constraints = b.constraints)
    (hg : a.degree4Gates = b.degree4Gates)
    (hm : a.airMaxDegree = b.airMaxDegree)
    (hh : a.histogram = b.histogram) : a = b := by
  cases a
  cases b
  simp_all

private theorem ReifiedFinalCost.eq_of_fields {a b : ReifiedFinalCost}
    (hct : a.computeTable = b.computeTable)
    (hcw : a.computeWalk = b.computeWalk)
    (hci : a.computeIO = b.computeIO)
    (hmt : a.memoryTable = b.memoryTable)
    (hmw : a.memoryWalk = b.memoryWalk)
    (hmi : a.memoryIO = b.memoryIO)
    (hctw : a.computeDisjointWidth = b.computeDisjointWidth)
    (hmtw : a.memoryDisjointWidth = b.memoryDisjointWidth)
    (he : a.eDeg = b.eDeg)
    (hd : a.rapDegreeBound = b.rapDegreeBound)
    (hio : a.ioLayer = b.ioLayer) : a = b := by
  cases a
  cases b
  simp_all

/-- Strong anti-phantom theorem: for a fixed exact family there is only one certifiable cost
record.  In particular, changing any nested or top-level field destroys certification. -/
theorem certified_cost_unique {F K : Type} [Field F] [Field K] [Algebra F K]
    {R : PlusIOSegmentedFamily F K} {c : ReifiedFinalCost}
    (h : ExactCostCertificate R c) : c = finalSegmentedCost (K := K) := by
  let h0 := finalSegmentedCost_certificate R
  apply ReifiedFinalCost.eq_of_fields
  · apply ComponentCost.eq_of_fields
    · exact (h.computeTable_width .row).trans (h0.computeTable_width .row).symm
    · exact h.computeTable_constraints.trans h0.computeTable_constraints.symm
    · exact h.computeTable_deg4.trans h0.computeTable_deg4.symm
    · exact h.computeTable_max.trans h0.computeTable_max.symm
    · exact h.computeTable_hist.trans h0.computeTable_hist.symm
  · apply ComponentCost.eq_of_fields
    · exact (h.computeWalk_width .row).trans (h0.computeWalk_width .row).symm
    · exact h.computeWalk_constraints.trans h0.computeWalk_constraints.symm
    · exact h.computeWalk_deg4.trans h0.computeWalk_deg4.symm
    · exact h.computeWalk_max.trans h0.computeWalk_max.symm
    · exact h.computeWalk_hist.trans h0.computeWalk_hist.symm
  · apply ComponentCost.eq_of_fields
    · exact (h.computeIO_width .row).trans (h0.computeIO_width .row).symm
    · exact h.computeIO_constraints.trans h0.computeIO_constraints.symm
    · exact h.computeIO_deg4.trans h0.computeIO_deg4.symm
    · exact h.computeIO_max.trans h0.computeIO_max.symm
    · exact h.computeIO_hist.trans h0.computeIO_hist.symm
  · apply ComponentCost.eq_of_fields
    · exact (h.memoryTable_width .row).trans (h0.memoryTable_width .row).symm
    · exact h.memoryTable_constraints.trans h0.memoryTable_constraints.symm
    · exact h.memoryTable_deg4.trans h0.memoryTable_deg4.symm
    · exact h.memoryTable_max.trans h0.memoryTable_max.symm
    · exact h.memoryTable_hist.trans h0.memoryTable_hist.symm
  · apply ComponentCost.eq_of_fields
    · exact (h.memoryWalk_width .row).trans (h0.memoryWalk_width .row).symm
    · exact h.memoryWalk_constraints.trans h0.memoryWalk_constraints.symm
    · exact h.memoryWalk_deg4.trans h0.memoryWalk_deg4.symm
    · exact h.memoryWalk_max.trans h0.memoryWalk_max.symm
    · exact h.memoryWalk_hist.trans h0.memoryWalk_hist.symm
  · apply ComponentCost.eq_of_fields
    · exact (h.memoryIO_width .row).trans (h0.memoryIO_width .row).symm
    · exact h.memoryIO_constraints.trans h0.memoryIO_constraints.symm
    · exact h.memoryIO_deg4.trans h0.memoryIO_deg4.symm
    · exact h.memoryIO_max.trans h0.memoryIO_max.symm
    · exact h.memoryIO_hist.trans h0.memoryIO_hist.symm
  · exact h.computeTotal.trans h0.computeTotal.symm
  · exact h.memoryTotal.trans h0.memoryTotal.symm
  · exact h.e_metadata.1.trans h0.e_metadata.1.symm
  · exact h.rap_bound_value.trans h0.rap_bound_value.symm
  · exact h.io_layer.trans h0.io_layer.symm

/-- Anti-phantom discrimination: a certificate cannot carry a different compute-table width. -/
theorem no_certificate_of_compute_width_ne {F K : Type} [Field F] [Field K] [Algebra F K]
    {R : PlusIOSegmentedFamily F K} {c : ReifiedFinalCost}
    (hne : c.computeTable.localWidth ≠ 94) :
    ¬ ExactCostCertificate R c := by
  intro h
  exact hne (h.computeTable_width .row |>.trans (R.actual_component_widths .row).1)

/-- Histogram discrimination similarly rejects a phantom table census. -/
theorem no_certificate_of_compute_hist_ne {F K : Type} [Field F] [Field K] [Algebra F K]
    {R : PlusIOSegmentedFamily F K} {c : ReifiedFinalCost}
    (hne : c.computeTable.histogram ≠ degreeHistogram Trans.computeAIRchained) :
    ¬ ExactCostCertificate R c := fun h => hne h.computeTable_hist

theorem AffineE.eq_of_eval_zero_one {a b : AffineE}
    (h0 : a.eval 0 = b.eval 0) (h1 : a.eval 1 = b.eval 1) : a = b := by
  cases a with
  | mk ac ak =>
    cases b with
    | mk bc bk =>
      simp only [AffineE.eval, Nat.mul_zero, zero_add] at h0
      simp only [AffineE.eval, Nat.mul_one] at h1
      subst bk
      have : ac = bc := Nat.add_right_cancel h1
      subst bc
      rfl

/-- Two operational evaluation points (`e=1,2`) determine an affine cost. -/
theorem AffineE.eq_of_eval_one_two {a b : AffineE}
    (h1 : a.eval 1 = b.eval 1) (h2 : a.eval 2 = b.eval 2) : a = b := by
  cases a with
  | mk ac ak =>
    cases b with
    | mk bc bk =>
      simp only [AffineE.eval, Nat.mul_one] at h1
      norm_num [AffineE.eval] at h2
      congr <;> omega

theorem batch13_decoy_killed :
    ¬ ((⟨94, 0⟩ : AffineE).eval 1 = (⟨80, 14⟩ : AffineE).eval 1 ∧
       (⟨94, 0⟩ : AffineE).eval 2 = (⟨80, 14⟩ : AffineE).eval 2) := by
  decide

/-- Honest paper-layer comparison.  These are per-unit mismatches: the exact segmented object is
at `e=1`, while the transcription is the paper's deployed `e=3` layer.  No layout translator or
equality between the two objects is asserted. -/
theorem paper_layer_mismatch :
    Nock.NockVMROM.paperParamCost.compIOCols.eval 3 = 199 ∧
    Nock.NockVMROM.paperParamCost.memIOCols.eval 3 = 196 ∧
    Nock.NockVMROM.paperParamCost.compIODeg4.eval 3 = 87 ∧
    Nock.NockVMROM.paperParamCost.memIODeg4.eval 3 = 88 ∧
    finalSegmentedCost (K := K).eDeg = 1 ∧
    finalSegmentedCost (K := K).computeDisjointWidth = 102 ∧
    finalSegmentedCost (K := K).memoryDisjointWidth = 45 ∧
    finalSegmentedCost (K := K).computeDisjointWidth ≠ 199 ∧
    finalSegmentedCost (K := K).memoryDisjointWidth ≠ 196 ∧
    finalSegmentedCost (K := K).computeTable.degree4Gates +
        finalSegmentedCost (K := K).computeWalk.degree4Gates +
        finalSegmentedCost (K := K).computeIO.degree4Gates ≠ 87 ∧
    finalSegmentedCost (K := K).memoryTable.degree4Gates +
        finalSegmentedCost (K := K).memoryWalk.degree4Gates +
        finalSegmentedCost (K := K).memoryIO.degree4Gates ≠ 88 := by
  refine ⟨Nock.NockVMROM.paperParamCost_IO_thm54.1,
    Nock.NockVMROM.paperParamCost_IO_thm54.2.1,
    Nock.NockVMROM.paperParamCost_IO_thm54.2.2.1,
    Nock.NockVMROM.paperParamCost_IO_thm54.2.2.2, ?_⟩
  simp only [finalSegmentedCost, component]
  refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · have hc : List.countP (fun c => c.degree == 4) Trans.computeAIRchained.constraints = 13 := by rfl
    have hw : List.countP (fun c => c.degree == 4) Trans.walkAIR.constraints = 0 := by rfl
    have hi : List.countP (fun c => c.degree == 4) Trans.ioProgAIR.constraints = 0 := by rfl
    rw [hc, hw, hi]
    decide
  · have hm : List.countP (fun c => c.degree == 4)
        (Trans.memoryAIRchained (K := K)).constraints = 2 := by rfl
    have hw : List.countP (fun c => c.degree == 4) Trans.walkAIR.constraints = 0 := by rfl
    have hi : List.countP (fun c => c.degree == 4) Trans.ioMemAIR.constraints = 0 := by rfl
    rw [hm, hw, hi]
    decide

/-- This certificate closes cost for the existing segmented object only; it deliberately contains
no strict-G10/full-Theorem-5.4 proposition. -/
theorem exact_cost_scope_only {F K : Type} [Field F] [Field K] [Algebra F K]
    (R : PlusIOSegmentedFamily F K) :
    Nonempty (ExactCostCertificate R (finalSegmentedCost (K := K))) :=
  ⟨finalSegmentedCost_certificate R⟩

end
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.finalSegmentedCost_certificate
#print axioms Nock.NockVMROM.Thm54.exactSegmentedCostVerification
#print axioms Nock.NockVMROM.Thm54.final_air_maxima
#print axioms Nock.NockVMROM.Thm54.final_degree_histograms
#print axioms Nock.NockVMROM.Thm54.final_constraint_and_gate_counts
#print axioms Nock.NockVMROM.Thm54.certified_cost_unique
#print axioms Nock.NockVMROM.Thm54.no_certificate_of_compute_width_ne
#print axioms Nock.NockVMROM.Thm54.no_certificate_of_compute_hist_ne
#print axioms Nock.NockVMROM.Thm54.AffineE.eq_of_eval_zero_one
#print axioms Nock.NockVMROM.Thm54.AffineE.eq_of_eval_one_two
#print axioms Nock.NockVMROM.Thm54.batch13_decoy_killed
#print axioms Nock.NockVMROM.Thm54.paper_layer_mismatch
#print axioms Nock.NockVMROM.Thm54.exact_cost_scope_only
