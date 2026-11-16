import Nock.NockVMROM.Thm54.OptimizedComputeTemplate
import Nock.NockVMROM.Thm54.ComputeWalkLabel

/-!
# Direct final 13-base / 62-extension typed lowering

The production compiler has four
additional semantic extension roles and therefore uses this distinct AST.  In particular, final
walk-line role 61 cannot be dropped or interpreted through the 58-role core.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeFinalTypedLowering

open Nock
open Nock.Reified
open Module
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open OptimizedComputeSubstitution
open OptimizedComputeGateBasis
open OptimizedComputeTypedLowering
open OptimizedComputeTemplate
open OptimizedComputeBaseGates

noncomputable section

inductive FinalTypedExpr where
  | baseCur : Fin 13 → FinalTypedExpr
  | baseNext : Fin 13 → FinalTypedExpr
  | extCur : Fin 62 → FinalTypedExpr
  | extNext : Fin 62 → FinalTypedExpr
  | challenge : ℕ → FinalTypedExpr
  | publicVal : ℕ → FinalTypedExpr
  | const : ℤ → FinalTypedExpr
  | add : FinalTypedExpr → FinalTypedExpr → FinalTypedExpr
  | sub : FinalTypedExpr → FinalTypedExpr → FinalTypedExpr
  | mul : FinalTypedExpr → FinalTypedExpr → FinalTypedExpr
  | neg : FinalTypedExpr → FinalTypedExpr
  | pow : FinalTypedExpr → ℕ → FinalTypedExpr
deriving DecidableEq

/-- Lower one mixed-layout expression into the direct final layout. -/
def lowerFinal : Expr → Option FinalTypedExpr
  | .Var .traceCur i =>
      if h : i < 13 then some (.baseCur ⟨i, h⟩)
      else if h : i < 75 then some (.extCur ⟨i - 13, by omega⟩)
      else none
  | .Var .traceNext i =>
      if h : i < 13 then some (.baseNext ⟨i, h⟩)
      else if h : i < 75 then some (.extNext ⟨i - 13, by omega⟩)
      else none
  | .Var .challenge i => some (.challenge i)
  | .Var .publicVal i => some (.publicVal i)
  | .Const c => some (.const c)
  | .Add x y => return .add (← lowerFinal x) (← lowerFinal y)
  | .Sub x y => return .sub (← lowerFinal x) (← lowerFinal y)
  | .Mul x y => return .mul (← lowerFinal x) (← lowerFinal y)
  | .Neg x => return .neg (← lowerFinal x)
  | .Pow x n => return .pow (← lowerFinal x) n

def lowerFinalTotal (e : Expr) : FinalTypedExpr :=
  (lowerFinal e).getD (.const 0)

def FinalTypedExpr.degree : FinalTypedExpr → ℕ
  | .baseCur _ | .baseNext _ | .extCur _ | .extNext _ => 1
  | .challenge _ | .publicVal _ | .const _ => 0
  | .add x y | .sub x y => max x.degree y.degree
  | .mul x y => x.degree + y.degree
  | .neg x => x.degree
  | .pow x n => n * x.degree

def FinalTypedSupportFits : FinalTypedExpr → Prop
  | .baseCur _ | .baseNext _ | .extCur _ | .extNext _ | .const _ => True
  | .challenge i => i < 12
  | .publicVal i => i < 42
  | .add x y | .sub x y | .mul x y =>
      FinalTypedSupportFits x ∧ FinalTypedSupportFits y
  | .neg x | .pow x _ => FinalTypedSupportFits x

instance finalTypedSupportFitsDecidable (t : FinalTypedExpr) :
    Decidable (FinalTypedSupportFits t) := by
  induction t <;> simp only [FinalTypedSupportFits] <;> infer_instance

def finalExtCoordIndex {e : ℕ} (i : Fin 62) (k : Fin e) : ℕ :=
  13 + e * (i : ℕ) + (k : ℕ)

/-- Coordinate compiler for the direct final typed AST. -/
def finalTypedCompile {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) : FinalTypedExpr → Fin e → CoeffExpr F
  | .baseCur i => fun k =>
      .mul (.var .traceCur i) (.const (coord b (1 : K) k))
  | .baseNext i => fun k =>
      .mul (.var .traceNext i) (.const (coord b (1 : K) k))
  | .extCur i => fun k => .var .traceCur (finalExtCoordIndex i k)
  | .extNext i => fun k => .var .traceNext (finalExtCoordIndex i k)
  | .challenge i => fun k => .var .challenge (e * i + (k : ℕ))
  | .publicVal i => fun k => .var .publicVal (e * i + (k : ℕ))
  | .const c => fun k => .const ((c : F) * coord b (1 : K) k)
  | .add x y => fun k => .add (finalTypedCompile b x k) (finalTypedCompile b y k)
  | .sub x y => fun k => .sub (finalTypedCompile b x k) (finalTypedCompile b y k)
  | .neg x => fun k => .neg (finalTypedCompile b x k)
  | .mul x y => mulVec b (finalTypedCompile b x) (finalTypedCompile b y)
  | .pow x n => powVec b (finalTypedCompile b x) n

theorem finalTypedCompile_degree_le
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (t : FinalTypedExpr) (k : Fin e) :
    (finalTypedCompile b t k).degree ≤ t.degree := by
  induction t generalizing k with
  | baseCur i => simp [finalTypedCompile, FinalTypedExpr.degree, CoeffExpr.degree]
  | baseNext i => simp [finalTypedCompile, FinalTypedExpr.degree, CoeffExpr.degree]
  | extCur i => simp [finalTypedCompile, FinalTypedExpr.degree, CoeffExpr.degree]
  | extNext i => simp [finalTypedCompile, FinalTypedExpr.degree, CoeffExpr.degree]
  | challenge i => simp [finalTypedCompile, FinalTypedExpr.degree, CoeffExpr.degree]
  | publicVal i => simp [finalTypedCompile, FinalTypedExpr.degree, CoeffExpr.degree]
  | const c => simp [finalTypedCompile, FinalTypedExpr.degree, CoeffExpr.degree]
  | add x y ihx ihy =>
      simp only [finalTypedCompile, FinalTypedExpr.degree, CoeffExpr.degree]
      exact max_le_max (ihx k) (ihy k)
  | sub x y ihx ihy =>
      simp only [finalTypedCompile, FinalTypedExpr.degree, CoeffExpr.degree]
      exact max_le_max (ihx k) (ihy k)
  | neg x ih =>
      simpa [finalTypedCompile, FinalTypedExpr.degree, CoeffExpr.degree] using ih k
  | mul x y ihx ihy =>
      exact degree_mulVec_le b _ _ x.degree y.degree ihx ihy k
  | pow x n ih => exact degree_powVec_le b _ x.degree ih n k

/-- The packed 81-gate list is lowered separately as `correctedLoweredExt`. -/
def finalLoweredExtTransitionGates : List FinalTypedExpr :=
  historicalFinalExtTransitionGates.filterMap lowerFinal

@[simp] theorem finalLoweredExtTransitionGates_length :
    finalLoweredExtTransitionGates.length = 21 := by
  set_option maxRecDepth 100000 in
  decide

theorem finalLoweredExtTransitionGates_degree :
    ∀ t ∈ finalLoweredExtTransitionGates, t.degree ≤ 4 := by
  set_option maxRecDepth 100000 in
  decide

theorem finalLoweredExtTransitionGates_support :
    ∀ t ∈ finalLoweredExtTransitionGates, FinalTypedSupportFits t := by
  set_option maxRecDepth 100000 in
  decide

/-- The final line role is present in both phases and cannot be represented by the core lowering. -/
theorem walk_line_requires_final_lowering :
    lower (finalWalkSubst .traceCur 0) = none ∧
      lower (finalWalkSubst .traceNext 0) = none ∧
      lowerFinal (finalWalkSubst .traceCur 0) = some (.extCur 61) ∧
      lowerFinal (finalWalkSubst .traceNext 0) = some (.extNext 61) := by
  decide

/-! ## Final endpoint expressions -/

/-- First-row walk subst. -/
def finalWalkInitialSubst : VarKind → ℕ → Expr
  | .traceCur, 0 => finalWalkLine .traceCur
  | .traceCur, 1 => initialOverlayCoord 0
  | .traceCur, 2 => initialOverlayCoord 1
  | .traceCur, 3 => ComputeWalkLabel.labelRLC ComputeWalkLabel.firstReader
  | .traceCur, 4 => ComputeWalkLabel.childSumCC ComputeWalkLabel.firstReader
  | .traceCur, 5 => ComputeWalkLabel.selectorCM ComputeWalkLabel.firstReader
  | .traceCur, i + 1 => initialOverlayCoord i
  | .traceNext, i => .Var .traceNext i
  | .challenge, i => walkChallenge i
  | .publicVal, i => .Var .publicVal i

theorem initialMask_eq_initialMaskExpr (st : ComputeTable.State) :
    initialMask st = ComputeWalkLabel.initialMaskExpr st := rfl

def finalWalkTerminalSubst : VarKind → ℕ → Expr
  | .traceCur, 0 => finalWalkLine .traceCur
  | .traceCur, i + 1 => terminalOverlayCoord i
  | .traceNext, i => .Var .traceNext i
  | .challenge, i => walkChallenge i
  | .publicVal, i => .Var .publicVal i

def finalOptimizedWalkLn1 : Expr := Trans.walkLn1.subst finalWalkInitialSubst
def finalOptimizedWalkCount1 : Expr := Trans.walkCount1.subst finalWalkInitialSubst
def finalOptimizedWalkAccInit : Expr := Trans.walkAccInit.subst finalWalkInitialSubst
def finalOptimizedWalkOut : Expr := Trans.walkOut.subst finalWalkTerminalSubst

def finalMaskedWalkLn1 : Expr := .Mul fixedIsFirst finalOptimizedWalkLn1
def finalMaskedWalkCount1 : Expr := .Mul fixedIsFirst finalOptimizedWalkCount1
def finalMaskedWalkAccInit : Expr :=
  .Mul (.Pow fixedIsFirst 2) finalOptimizedWalkAccInit
def finalMaskedWalkOut : Expr := .Mul fixedIsLast finalOptimizedWalkOut
def finalMaskedWalkInitFold : Expr :=
  .Add finalMaskedWalkLn1
    (.Mul (.Var .challenge (compilerChallengeBase + 2)) finalMaskedWalkCount1)

def finalLoweredMaskedEndpointDeg2 : List FinalTypedExpr :=
  [finalMaskedWalkInitFold, finalMaskedWalkOut].filterMap lowerFinal

def finalLoweredMaskedEndpointDeg4 : List FinalTypedExpr :=
  [finalMaskedWalkAccInit].filterMap lowerFinal

theorem finalLoweredMaskedEndpoint_counts :
    finalLoweredMaskedEndpointDeg2.length = 2 ∧
      finalLoweredMaskedEndpointDeg4.length = 1 := by
  decide

theorem finalLoweredMaskedEndpoint_degrees :
    (∀ t ∈ finalLoweredMaskedEndpointDeg2, t.degree ≤ 2) ∧
      (∀ t ∈ finalLoweredMaskedEndpointDeg4, t.degree ≤ 4) := by
  decide

def compileFinalTypedList {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (ts : List FinalTypedExpr) :
    List (CoeffExpr F) :=
  ts.flatMap fun t => List.ofFn fun k : Fin e => finalTypedCompile b t k

theorem compileFinalTypedList_length
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (ts : List FinalTypedExpr) :
    (compileFinalTypedList b ts).length = ts.length * e := by
  simp [compileFinalTypedList]

theorem compileFinalTypedList_degree
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (ts : List FinalTypedExpr) (d : ℕ)
    (hdeg : ∀ t ∈ ts, t.degree ≤ d) :
    ∀ g ∈ compileFinalTypedList b ts, g.degree ≤ d := by
  intro g hg
  rw [compileFinalTypedList] at hg
  obtain ⟨xs, hxs, hg⟩ := List.mem_flatten.mp hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hxs
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
  exact (finalTypedCompile_degree_le b t k).trans (hdeg t ht)

#print axioms finalTypedCompile_degree_le
#print axioms finalLoweredExtTransitionGates_length
#print axioms walk_line_requires_final_lowering

end
end OptimizedComputeFinalTypedLowering
end Nock.NockVMROM.Thm54
