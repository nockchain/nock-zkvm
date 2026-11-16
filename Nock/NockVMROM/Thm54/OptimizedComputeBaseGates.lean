import Nock.NockVMROM.Thm54.OptimizedComputeGateBasis

/-!
# Concrete thirteen-gate optimized compute base basis

The thirteen base transition gates enforce eleven selector booleanities, selector sum-to-one, and
one RLC-compressed pair of structural-summary pins (fanout and memory-record count).  The summary
compression uses challenge 9 and carries an explicit collision-free premise.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeBaseGates

open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54.CoordinateCompiler

variable {F : Type*} [Field F]

def bv (i : ℕ) : CoeffExpr F := .var .traceCur i

def selectorBool (i : ℕ) : CoeffExpr F :=
  .mul (bv i) (.sub (.const 1) (bv i))

def selectorSum : CoeffExpr F :=
  CoeffExpr.sumList (List.range 11) bv

def selectorOneHot : CoeffExpr F :=
  .sub selectorSum (.const 1)

def expectedSummary (f : State → ℕ) : CoeffExpr F :=
  CoeffExpr.sumList Nock.Reified.allStates
    (fun st => .mul (.const (f st : F)) (bv (Nock.Reified.opCol st)))

def fanoutPin : CoeffExpr F :=
  .sub (bv 11) (expectedSummary fanoutComp)

def recordCountPin : CoeffExpr F :=
  .sub (bv 12) (expectedSummary Nock.Framework.recordCount)

def summaryFold : CoeffExpr F :=
  .add fanoutPin (.mul (.var .challenge 9) recordCountPin)

/-- Fourteen unfurled base equations. -/
def baseSourceGates : List (CoeffExpr F) :=
  (List.range 11).map selectorBool ++
    [selectorOneHot, fanoutPin, recordCountPin]

/-- Exact thirteen-gate base basis. -/
def baseTransitionGates : List (CoeffExpr F) :=
  (List.range 11).map selectorBool ++ [selectorOneHot, summaryFold]

/-- Every trace variable of a base-bucket gate is one of the thirteen base-column IDs. -/
def BaseSupportFits13 : CoeffExpr F → Prop
  | .const _ => True
  | .var .traceCur i | .var .traceNext i => i < 13
  | .var .challenge _ | .var .publicVal _ => True
  | .add x y | .sub x y | .mul x y => BaseSupportFits13 x ∧ BaseSupportFits13 y
  | .neg x | .pow x _ => BaseSupportFits13 x

theorem support_sumList {ι : Type*} (xs : List ι) (f : ι → CoeffExpr F)
    (h : ∀ i ∈ xs, BaseSupportFits13 (f i)) :
    BaseSupportFits13 (CoeffExpr.sumList xs f) := by
  induction xs with
  | nil => simp [CoeffExpr.sumList, BaseSupportFits13]
  | cons a xs ih =>
      simp only [CoeffExpr.sumList, List.foldr_cons, BaseSupportFits13]
      exact ⟨h a (by simp), ih (fun i hi => h i (by simp [hi]))⟩

theorem baseTransitionGates_support :
    ∀ g ∈ (baseTransitionGates (F := F)), BaseSupportFits13 g := by
  intro g hg
  simp only [baseTransitionGates, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ⟨i, hi, rfl⟩ | rfl | rfl
  · simp [selectorBool, bv, BaseSupportFits13]
    omega
  · simp only [selectorOneHot, BaseSupportFits13]
    constructor
    · apply support_sumList
      intro i hi
      have hi' : i < 11 := List.mem_range.mp hi
      simpa [bv, BaseSupportFits13] using (hi'.trans (by norm_num : 11 < 13))
    · trivial
  · simp [summaryFold, fanoutPin, recordCountPin, expectedSummary, CoeffExpr.sumList,
      BaseSupportFits13, bv, Nock.Reified.allStates, Nock.Reified.opCol]

@[simp] theorem baseSourceGates_length : (baseSourceGates (F := F)).length = 14 := by
  simp [baseSourceGates]

@[simp] theorem baseTransitionGates_length :
    (baseTransitionGates (F := F)).length = 13 := by
  simp [baseTransitionGates]

def SummaryCollisionFree (env : Env F) : Prop :=
  summaryFold.eval env = 0 →
    fanoutPin.eval env = 0 ∧ recordCountPin.eval env = 0

theorem summaryFold_zero_of_pins (env : Env F)
    (hf : fanoutPin.eval env = 0) (hr : recordCountPin.eval env = 0) :
    summaryFold.eval env = 0 := by
  simp [summaryFold, CoeffExpr.eval, hf, hr]

theorem summaryFold_zero_iff (env : Env F) (hfree : SummaryCollisionFree env) :
    summaryFold.eval env = 0 ↔
      fanoutPin.eval env = 0 ∧ recordCountPin.eval env = 0 :=
  ⟨hfree, fun h => summaryFold_zero_of_pins env h.1 h.2⟩

theorem baseTransitionGates_eval_iff (env : Env F)
    (hfree : SummaryCollisionFree env) :
    (∀ g ∈ baseTransitionGates, g.eval env = 0) ↔
      ∀ g ∈ baseSourceGates, g.eval env = 0 := by
  simp only [baseTransitionGates, baseSourceGates, List.forall_mem_append,
    List.forall_mem_map, List.forall_mem_cons,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  rw [summaryFold_zero_iff env hfree]

theorem selectorSum_degree :
    (selectorSum (F := F)).degree ≤ 1 := by
  apply CoeffExpr.degree_sumList_le
  intro i hi
  simp [bv, CoeffExpr.degree]

theorem expectedSummary_degree (f : State → ℕ) :
    (expectedSummary (F := F) f).degree ≤ 1 := by
  apply CoeffExpr.degree_sumList_le
  intro st hst
  simp [bv, CoeffExpr.degree]

theorem baseTransitionGates_degree :
    ∀ g ∈ (baseTransitionGates (F := F)), g.degree ≤ 4 := by
  intro g hg
  simp only [baseTransitionGates, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ⟨i, hi, rfl⟩ | rfl | rfl
  · simp [selectorBool, bv, CoeffExpr.degree]
  · simp only [selectorOneHot, CoeffExpr.degree]
    exact (max_le selectorSum_degree (by simp)).trans (by decide)
  · simp only [summaryFold, fanoutPin, recordCountPin, CoeffExpr.degree]
    exact max_le
      (max_le (by simp [bv, CoeffExpr.degree])
        ((expectedSummary_degree fanoutComp).trans (by decide)))
      (by
        simp only [Nat.zero_add]
        exact max_le (by simp [bv, CoeffExpr.degree])
          ((expectedSummary_degree Nock.Framework.recordCount).trans (by decide)))

abbrev BaseGateId := Fin 13

def allBaseGateIds : List BaseGateId := List.ofFn id

theorem allBaseGateIds_nodup : allBaseGateIds.Nodup := by
  rw [allBaseGateIds, List.nodup_ofFn]
  exact Function.injective_id

@[simp] theorem allBaseGateIds_length : allBaseGateIds.length = 13 := by
  simp [allBaseGateIds]

def baseGate (id : BaseGateId) : CoeffExpr F :=
  baseTransitionGates.get ⟨id, by simpa using id.isLt⟩

theorem baseGate_mem (id : BaseGateId) :
    baseGate (F := F) id ∈ baseTransitionGates :=
  List.get_mem _ _

theorem baseGate_coverage (g : CoeffExpr F) :
    g ∈ baseTransitionGates ↔ ∃ id : BaseGateId, baseGate id = g := by
  constructor
  · intro hg
    obtain ⟨n, hn⟩ := List.get_of_mem hg
    exact ⟨⟨n, by simpa using n.isLt⟩, hn⟩
  · rintro ⟨id, rfl⟩
    exact baseGate_mem id

theorem baseTransitionGates_nonzero :
    ∀ g ∈ (baseTransitionGates (F := F)), g ≠ .const 0 := by
  intro g hg
  simp only [baseTransitionGates, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ⟨i, hi, rfl⟩ | rfl | rfl
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h

/-! ## Fixed-endpoint-mask Base13 layout

The
production fixed-preprocessing layout repurposes slots 11 and 12 as exact first/last selectors.
-/

def isFirstVar : CoeffExpr F := bv 11
def isLastVar : CoeffExpr F := bv 12

/-- One exact gate checks booleanity of both fixed endpoint selectors.  The fold challenge is
verifier data (trace degree zero), so this stays quadratic.  Unlike a disjointness gate, this also
accepts the required singleton case, where both selectors equal one. -/
def endpointMaskBooleanFold : CoeffExpr F :=
  .add
    (.mul isFirstVar (.sub (.const 1) isFirstVar))
    (.mul (.var .challenge 11)
      (.mul isLastVar (.sub (.const 1) isLastVar)))

/-- Exact thirteen-gate Base13 basis for a multirow fixed-mask trace. -/
def maskedBaseTransitionGates : List (CoeffExpr F) :=
  (List.range 11).map selectorBool ++ [selectorOneHot, endpointMaskBooleanFold]

/-- There is no RLC weakening in the fixed-mask base basis. -/
def maskedBaseSourceGates : List (CoeffExpr F) :=
  maskedBaseTransitionGates

@[simp] theorem maskedBaseTransitionGates_length :
    (maskedBaseTransitionGates (F := F)).length = 13 := by
  simp [maskedBaseTransitionGates]

theorem maskedBaseTransitionGates_degree :
    ∀ g ∈ (maskedBaseTransitionGates (F := F)), g.degree ≤ 2 := by
  intro g hg
  simp only [maskedBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ⟨i, hi, rfl⟩ | rfl | rfl
  · simp [selectorBool, bv, CoeffExpr.degree]
  · simp only [selectorOneHot, CoeffExpr.degree]
    exact max_le (selectorSum_degree.trans (by decide)) (by simp)
  · simp [endpointMaskBooleanFold, isFirstVar, isLastVar, bv, CoeffExpr.degree]

theorem maskedBaseTransitionGates_support :
    ∀ g ∈ (maskedBaseTransitionGates (F := F)), BaseSupportFits13 g := by
  intro g hg
  simp only [maskedBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ⟨i, hi, rfl⟩ | rfl | rfl
  · simp [selectorBool, bv, BaseSupportFits13]
    omega
  · simp only [selectorOneHot, BaseSupportFits13]
    constructor
    · apply support_sumList (F := F)
      intro i hi
      simp [bv, BaseSupportFits13]
      exact (List.mem_range.mp hi).trans (by norm_num)
    · trivial
  · simp [endpointMaskBooleanFold, isFirstVar, isLastVar, bv, BaseSupportFits13]

theorem endpointMaskBooleanFold_zero_of_boolean (env : Env F)
    (hfirst : isFirstVar.eval env = 0 ∨ isFirstVar.eval env = 1)
    (hlast : isLastVar.eval env = 0 ∨ isLastVar.eval env = 1) :
    endpointMaskBooleanFold.eval env = 0 := by
  rcases hfirst with hfirst | hfirst <;>
    rcases hlast with hlast | hlast
  all_goals
    change isFirstVar.eval env * (1 - isFirstVar.eval env) +
      env.chal 11 * (isLastVar.eval env * (1 - isLastVar.eval env)) = 0
    rw [hfirst, hlast]
    ring

theorem maskedBaseTransitionGates_eval_iff (env : Env F) :
    (∀ g ∈ maskedBaseTransitionGates, g.eval env = 0) ↔
      ∀ g ∈ maskedBaseSourceGates, g.eval env = 0 :=
  Iff.rfl

#print axioms summaryFold_zero_iff
#print axioms baseTransitionGates_eval_iff
#print axioms baseTransitionGates_degree
#print axioms baseGate_coverage
#print axioms allBaseGateIds_nodup
#print axioms baseTransitionGates_nonzero
#print axioms maskedBaseTransitionGates_degree
#print axioms maskedBaseTransitionGates_eval_iff
#print axioms endpointMaskBooleanFold_zero_of_boolean

end OptimizedComputeBaseGates
end Nock.NockVMROM.Thm54
