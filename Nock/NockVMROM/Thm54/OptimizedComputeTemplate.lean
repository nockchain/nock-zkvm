import Nock.NockVMROM.Thm54.OptimizedComputeRowSemantics
import Nock.NockVMROM.Thm54.OptimizedComputeTypedLowering
import Nock.NockVMROM.Thm54.RAPPadding
import Nock.Framework.EndpointMasks

/-!
# Repaired optimized compute `ChipTemplate`

Initial walk endpoints use public one-hot state masks (`publicVal 20..30`) to select the physical
overlay hosts.  Public values have trace degree zero, so this avoids the degree-two endpoint caused
by selecting dynamic hosts with current-row opcode columns.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeTemplate

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedComputeSubstitution
open OptimizedComputeGateBasis
open OptimizedComputeBaseGates
open OptimizedComputeTypedLowering

noncomputable section

variable {F : Type*} [Field F]

/-- Public initial-state mask for one compute state. -/
def initialMask (st : State) : Expr :=
  .Var .publicVal (20 + Nock.Reified.opCol st)

/-- Public-mask selection of a dynamic overlay coordinate at the first row. -/
def initialOverlayCoord (coord : ℕ) : Expr :=
  if coord < 3 then
    Nock.Reified.allStates.foldr
      (fun st acc => .Add (.Mul (initialMask st)
        (pubFP .traceCur (overlayANat st) coord)) acc) (.Const 0)
  else if coord < 5 then
    Nock.Reified.allStates.foldr
      (fun st acc => .Add (.Mul (initialMask st)
        (pubFP .traceCur (overlayBNat st) (coord - 3))) acc) (.Const 0)
  else if coord = 5 then pubFP .traceCur 10 2
  else pubFP .traceCur 11 (coord - 6)

/-- Public terminal-state mask for one compute state. -/
def terminalMask (st : State) : Expr :=
  .Var .publicVal (31 + Nock.Reified.opCol st)

/-- Public-mask selection of a dynamic overlay coordinate at the terminal row. -/
def terminalOverlayCoord (coord : ℕ) : Expr :=
  if coord < 3 then
    Nock.Reified.allStates.foldr
      (fun st acc => .Add (.Mul (terminalMask st)
        (pubFP .traceCur (overlayANat st) coord)) acc) (.Const 0)
  else if coord < 5 then
    Nock.Reified.allStates.foldr
      (fun st acc => .Add (.Mul (terminalMask st)
        (pubFP .traceCur (overlayBNat st) (coord - 3))) acc) (.Const 0)
  else if coord = 5 then pubFP .traceCur 10 2
  else pubFP .traceCur 11 (coord - 6)

/-- First-row walk environment.  Unlike `walkSubst`, host selection uses degree-zero public masks. -/
def walkInitialSubst : VarKind → ℕ → Expr
  | .traceCur, 0 => lnCur .traceCur
  | .traceCur, i + 1 => initialOverlayCoord i
  | .traceNext, i => .Var .traceNext i
  | .challenge, i => .Var .challenge i
  | .publicVal, i => .Var .publicVal i

def walkTerminalSubst : VarKind → ℕ → Expr
  | .traceCur, 0 => lnCur .traceCur
  | .traceCur, i + 1 => terminalOverlayCoord i
  | .traceNext, i => .Var .traceNext i
  | .challenge, i => .Var .challenge i
  | .publicVal, i => .Var .publicVal i

def optimizedWalkLn1 : Expr := Trans.walkLn1.subst walkInitialSubst
def optimizedWalkCount1 : Expr := Trans.walkCount1.subst walkInitialSubst
def optimizedWalkAccInit : Expr := Trans.walkAccInit.subst walkInitialSubst
def optimizedWalkOut : Expr := Trans.walkOut.subst walkTerminalSubst

/-- Fold the two degree-one initial equations without changing trace degree. -/
def optimizedWalkInitFold : Expr :=
  .Add optimizedWalkLn1
    (.Mul (.Var .challenge 11) optimizedWalkCount1)

theorem optimizedWalkEndpoint_degrees :
    optimizedWalkLn1.degree = 1 ∧
      optimizedWalkCount1.degree = 1 ∧
      optimizedWalkAccInit.degree = 2 ∧
      optimizedWalkOut.degree = 1 ∧
      optimizedWalkInitFold.degree = 1 := by
  decide

def WalkInitCollisionFree {K : Type*} [Field K] (env : Env K) : Prop :=
  optimizedWalkInitFold.eval env = 0 →
    optimizedWalkLn1.eval env = 0 ∧ optimizedWalkCount1.eval env = 0

theorem optimizedWalkInitFold_iff {K : Type*} [Field K] (env : Env K)
    (hfree : WalkInitCollisionFree env) :
    optimizedWalkInitFold.eval env = 0 ↔
      optimizedWalkLn1.eval env = 0 ∧ optimizedWalkCount1.eval env = 0 := by
  constructor
  · exact hfree
  · rintro ⟨hln, hcount⟩
    simp [optimizedWalkInitFold, Expr.eval, hln, hcount]

def optimizedWalkEndpointSources : List Expr :=
  [optimizedWalkLn1, optimizedWalkCount1, optimizedWalkAccInit, optimizedWalkOut]

theorem optimizedWalk_endpoint_source_partition :
    optimizedWalkEndpointSources.length = 4 ∧
      optimizedWalkEndpointSources.Nodup ∧
      optimizedWalkOut ∈ optimizedWalkEndpointSources := by
  decide

/-- Base-field RLC equality between a row's selector vector and eleven public state masks. -/
def selectorPublicCheck (kind : VarKind) (publicBase : ℕ) : CoeffExpr F :=
  CoeffExpr.sumList (List.range 11) fun i =>
    .mul (.pow (.var .challenge 10) i)
      (.sub (.var kind i) (.var .publicVal (publicBase + i)))

def endpointEqualityChecks : List (CoeffExpr F) :=
  [selectorPublicCheck .traceCur 20, selectorPublicCheck .traceCur 31]

theorem endpointEqualityChecks_degree :
    ∀ g ∈ (endpointEqualityChecks (F := F)), g.degree ≤ 1 := by
  intro g hg
  simp only [endpointEqualityChecks, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;>
    apply CoeffExpr.degree_sumList_le <;>
    intro i hi <;>
    simp [CoeffExpr.degree]

/-- A template whose extension gates carry typed base/extension roles. -/
structure TypedChipTemplate (F : Type*) [Field F] where
  rounds : ℕ
  baseCols : ℕ
  extCols : ℕ
  baseTransition : List (CoeffExpr F)
  extTransition : List TypedExpr
  extDeg1 : List TypedExpr
  extDeg3 : List TypedExpr
  equalityChecks : List (CoeffExpr F)

def TypedChipTemplate.width (T : TypedChipTemplate F) (e : ℕ) : ℕ :=
  T.baseCols + T.extCols * e

def loweredEndpointDeg1 : List TypedExpr :=
  [optimizedWalkInitFold, optimizedWalkOut].filterMap lower

def loweredEndpointDeg3 : List TypedExpr :=
  [optimizedWalkAccInit].filterMap lower

theorem loweredEndpoint_counts :
    loweredEndpointDeg1.length = 2 ∧ loweredEndpointDeg3.length = 1 := by
  decide

theorem loweredEndpoint_degrees :
    (∀ t ∈ loweredEndpointDeg1, t.degree ≤ 1) ∧
      (∀ t ∈ loweredEndpointDeg3, t.degree ≤ 3) := by
  decide

theorem loweredEndpoint_support :
    (∀ t ∈ loweredEndpointDeg1, TypedSupportFits t) ∧
      (∀ t ∈ loweredEndpointDeg3, TypedSupportFits t) := by
  decide

def TypedEndpointSat {K : Type*} [Field K] {F : Type*} [Field F] [Algebra F K]
    (env : TypedEnv F K) : Prop :=
  (∀ t ∈ loweredEndpointDeg1, t.eval env = 0) ∧
    (∀ t ∈ loweredEndpointDeg3, t.eval env = 0)

def CompleteEndpointSource {K : Type*} [Field K] {F : Type*} [Field F] [Algebra F K]
    (env : TypedEnv F K) : Prop :=
  optimizedWalkLn1.eval env.toMixedEnv = 0 ∧
    optimizedWalkCount1.eval env.toMixedEnv = 0 ∧
    optimizedWalkAccInit.eval env.toMixedEnv = 0 ∧
    optimizedWalkOut.eval env.toMixedEnv = 0

theorem typedEndpointSat_iff_completeSource
    {K : Type*} [Field K] {F : Type*} [Field F] [Algebra F K]
    (env : TypedEnv F K) (hfree : WalkInitCollisionFree env.toMixedEnv) :
    TypedEndpointSat env ↔ CompleteEndpointSource env := by
  unfold TypedEndpointSat CompleteEndpointSource
  unfold loweredEndpointDeg1 loweredEndpointDeg3
  rw [
    filterMap_eval_iff env [optimizedWalkInitFold, optimizedWalkOut]
      loweredEndpoint_counts.1,
    filterMap_eval_iff env [optimizedWalkAccInit] loweredEndpoint_counts.2]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rw [optimizedWalkInitFold_iff env.toMixedEnv hfree]
  tauto

/-- Actual repaired typed optimized compute template. -/
def compOptimizedTemplate (F : Type*) [Field F] : TypedChipTemplate F where
  rounds := 2
  baseCols := 13
  extCols := 58
  baseTransition := baseTransitionGates
  extTransition := loweredExtTransitionGates
  extDeg1 := loweredEndpointDeg1
  extDeg3 := loweredEndpointDeg3
  equalityChecks := endpointEqualityChecks

theorem compOptimizedTemplate_shape :
    (compOptimizedTemplate F).rounds = 2 ∧
      (compOptimizedTemplate F).baseCols = 13 ∧
      (compOptimizedTemplate F).extCols = 58 ∧
      (compOptimizedTemplate F).baseTransition.length = 13 ∧
      (compOptimizedTemplate F).extTransition.length = 21 ∧
      (compOptimizedTemplate F).extDeg1.length = 2 ∧
      (compOptimizedTemplate F).extDeg3.length = 1 ∧
      (compOptimizedTemplate F).equalityChecks.length = 2 := by
  norm_num [compOptimizedTemplate, endpointEqualityChecks, loweredEndpoint_counts]

theorem compOptimizedTemplate_cubic_counts :
    (compOptimizedTemplate F).width 3 = 187 ∧
      (compOptimizedTemplate F).baseTransition.length +
          (compOptimizedTemplate F).extTransition.length * 3 = 76 ∧
      (compOptimizedTemplate F).baseTransition.length +
          (compOptimizedTemplate F).extTransition.length * 3 +
          (compOptimizedTemplate F).extDeg1.length * 3 +
          (compOptimizedTemplate F).extDeg3.length * 3 +
          (compOptimizedTemplate F).equalityChecks.length = 87 := by
  norm_num [TypedChipTemplate.width, compOptimizedTemplate, endpointEqualityChecks,
    loweredEndpoint_counts]

/-! ## Cubic core and structural padding -/

open Nock.Framework
open Module
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.RAPPadding
open scoped Polynomial

variable {K : Type*} [Field K] [Algebra F K] [FiniteDimensional F K]

/-- Coordinate-expand a list of typed extension equations. -/
def compileTypedList {e : ℕ} (b : Basis (Fin e) F K) (ts : List TypedExpr) :
    List (CoeffExpr F) :=
  ts.flatMap fun t => List.ofFn fun k : Fin e => typedCompile b t k

def compOptimizedAllGates (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  baseTransitionGates ++
    compileTypedList b loweredExtTransitionGates ++
    compileTypedList b loweredEndpointDeg1 ++
    compileTypedList b loweredEndpointDeg3 ++
    endpointEqualityChecks

theorem compileTypedList_length {e : ℕ} (b : Basis (Fin e) F K) (ts : List TypedExpr) :
    (compileTypedList b ts).length = ts.length * e := by
  simp [compileTypedList]

theorem compOptimizedAllGates_length (b : Basis (Fin 3) F K) :
    (compOptimizedAllGates b).length = 87 := by
  simp [compOptimizedAllGates, compileTypedList_length, loweredEndpoint_counts,
    endpointEqualityChecks]

theorem compileTypedList_degree (b : Basis (Fin 3) F K) (ts : List TypedExpr)
    (d : ℕ) (hts : ∀ t ∈ ts, t.degree ≤ d) :
    ∀ g ∈ compileTypedList b ts, g.degree ≤ d := by
  intro g hg
  simp only [compileTypedList, List.mem_flatMap, List.mem_ofFn] at hg
  obtain ⟨t, ht, k, rfl⟩ := hg
  exact (typedCompile_degree_le b t k).trans (hts t ht)

theorem compOptimizedAllGates_degree (b : Basis (Fin 3) F K) :
    ∀ g ∈ compOptimizedAllGates b, g.degree ≤ 4 := by
  intro g hg
  change g ∈
    baseTransitionGates ++
      compileTypedList b loweredExtTransitionGates ++
      compileTypedList b loweredEndpointDeg1 ++
      compileTypedList b loweredEndpointDeg3 ++
      endpointEqualityChecks at hg
  simp only [List.mem_append] at hg
  rcases hg with (((hb | ht) | h1) | h3) | heq
  · exact baseTransitionGates_degree g hb
  · exact compileTypedList_degree b loweredExtTransitionGates 4
      loweredExtTransitionGates_degree g ht
  · exact (compileTypedList_degree b loweredEndpointDeg1 1
      loweredEndpoint_degrees.1 g h1).trans (by decide)
  · exact (compileTypedList_degree b loweredEndpointDeg3 3
      loweredEndpoint_degrees.2 g h3).trans (by decide)
  · exact (endpointEqualityChecks_degree g heq).trans (by decide)

def compOptimizedCoreRAP {h : ℕ} (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    RAP F where
  e := 3
  k := 2
  wRAP := ![184, 3]
  w := 187
  w_eq := by rw [Fin.sum_univ_two]; norm_num
  h := h
  d := 4
  s := (compOptimizedAllGates b).length
  ω := orbit.ω
  β := orbit.βcoset
  I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
  C := fun i => coeffToMv chalVal pubVal ((compOptimizedAllGates b).get i)
  C_vars := fun i => coeffToMv_vars chalVal pubVal _
  C_deg := fun i =>
    (coeffToMv_totalDegree_le chalVal pubVal _).trans
      (compOptimizedAllGates_degree b _ (List.get_mem _ _))
  H := H
  β_ne_zero := orbit.βcoset_ne_zero
  I_bound := by
    intro q hq
    have hq2 : q.2 = 0 ∨ q.2 = 1 := by
      have h2 := (Finset.mem_product.mp hq).2
      simpa [Finset.mem_insert, Finset.mem_singleton] using h2
    have hge : 2 ≤ 2 ^ h := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) orbit.h_pos
    rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega

theorem compOptimizedCoreRAP_fingerprint {h : ℕ} (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (compOptimizedCoreRAP b chalVal pubVal orbit H).w = 187 ∧
      (compOptimizedCoreRAP b chalVal pubVal orbit H).s = 87 := by
  exact ⟨rfl, compOptimizedAllGates_length b⟩

theorem compOptimizedCoreRAP_rounds {h : ℕ} (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (compOptimizedCoreRAP b chalVal pubVal orbit H).k = 2 := by
  rfl

def compOptimizedPaddedRAP {h : ℕ} (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    RAP F :=
  let R := compOptimizedCoreRAP b chalVal pubVal orbit H
  padComputeCore R (by
    rw [show R.k = 2 from compOptimizedCoreRAP_rounds b chalVal pubVal orbit H]
    norm_num) 3

theorem compOptimizedPaddedRAP_fingerprint {h : ℕ} (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (compOptimizedPaddedRAP b chalVal pubVal orbit H).w = 199 ∧
      (compOptimizedPaddedRAP b chalVal pubVal orbit H).s = 98 := by
  unfold compOptimizedPaddedRAP
  apply padComputeCore_e3_fingerprint
  · exact (compOptimizedCoreRAP_fingerprint b chalVal pubVal orbit H).1
  · exact (compOptimizedCoreRAP_fingerprint b chalVal pubVal orbit H).2

theorem compOptimizedPaddedRAP_satisfies_iff {h : ℕ} (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (H : Finset F)
    (P : Fin (compOptimizedPaddedRAP b chalVal pubVal orbit H).w → F[X]) :
    (compOptimizedPaddedRAP b chalVal pubVal orbit H).Satisfies P ↔
      let R := compOptimizedCoreRAP b chalVal pubVal orbit H
      R.Satisfies
        (projectTrace R
          (firstRoundExtra R (by
              rw [show R.k = 2 from
                compOptimizedCoreRAP_rounds b chalVal pubVal orbit H]
              norm_num)
            (computeResidualColumns 3)) P) := by
  unfold compOptimizedPaddedRAP
  exact padComputeCore_satisfies_iff _ _ 3 P

/-! ## Production fixed-mask endpoint variant

The production local interface
uses Base13 slots 11/12 as verifier-fixed first/last masks. Public endpoint-state masks still
select the state-dependent overlay host; the fixed trace masks control on which row the resulting
endpoint equation is active. -/

def fixedIsFirst : Expr := .Var .traceCur 11
def fixedIsLast : Expr := .Var .traceCur 12

def maskedWalkLn1 : Expr := .Mul fixedIsFirst optimizedWalkLn1
def maskedWalkCount1 : Expr := .Mul fixedIsFirst optimizedWalkCount1

/-- Squaring the exact boolean first-row selector preserves endpoint semantics and retains the
authorized degree-four accumulator bucket. -/
def maskedWalkAccInit : Expr :=
  .Mul (.Pow fixedIsFirst 2) optimizedWalkAccInit

def maskedWalkOut : Expr := .Mul fixedIsLast optimizedWalkOut

def maskedWalkInitFold : Expr :=
  .Add maskedWalkLn1 (.Mul (.Var .challenge 11) maskedWalkCount1)

/-- Endpoint selector/public-state equality is active only at its designated endpoint. -/
def maskedSelectorPublicCheck (mask : CoeffExpr F) (publicBase : ℕ) : CoeffExpr F :=
  .mul mask (selectorPublicCheck .traceCur publicBase)

def maskedEndpointEqualityChecks : List (CoeffExpr F) :=
  [maskedSelectorPublicCheck isFirstVar 20, maskedSelectorPublicCheck isLastVar 31]

@[simp] theorem maskedEndpointEqualityChecks_length :
    (maskedEndpointEqualityChecks (F := F)).length = 2 :=
  rfl

theorem maskedEndpointEqualityChecks_degree :
    ∀ g ∈ (maskedEndpointEqualityChecks (F := F)), g.degree ≤ 2 := by
  intro g hg
  simp only [maskedEndpointEqualityChecks, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · simp only [maskedSelectorPublicCheck, CoeffExpr.degree, isFirstVar, bv]
    exact Nat.add_le_add_right
      (endpointEqualityChecks_degree
        (selectorPublicCheck (F := F) .traceCur 20)
        (by simp [endpointEqualityChecks])) 1
  · simp only [maskedSelectorPublicCheck, CoeffExpr.degree, isLastVar, bv]
    exact Nat.add_le_add_right
      (endpointEqualityChecks_degree
        (selectorPublicCheck (F := F) .traceCur 31)
        (by simp [endpointEqualityChecks])) 1

theorem maskedWalkEndpoint_degrees :
    maskedWalkLn1.degree = 2 ∧
      maskedWalkCount1.degree = 2 ∧
      maskedWalkAccInit.degree = 4 ∧
      maskedWalkOut.degree = 2 ∧
      maskedWalkInitFold.degree = 2 := by
  decide

def MaskedWalkInitCollisionFree {K : Type*} [Field K] (env : Env K) : Prop :=
  maskedWalkInitFold.eval env = 0 →
    maskedWalkLn1.eval env = 0 ∧ maskedWalkCount1.eval env = 0

theorem maskedWalkInitFold_iff {K : Type*} [Field K] (env : Env K)
    (hfree : MaskedWalkInitCollisionFree env) :
    maskedWalkInitFold.eval env = 0 ↔
      maskedWalkLn1.eval env = 0 ∧ maskedWalkCount1.eval env = 0 := by
  constructor
  · exact hfree
  · rintro ⟨hln, hcount⟩
    simp [maskedWalkInitFold, Expr.eval, hln, hcount]

def loweredMaskedEndpointDeg2 : List TypedExpr :=
  [maskedWalkInitFold, maskedWalkOut].filterMap lower

def loweredMaskedEndpointDeg4 : List TypedExpr :=
  [maskedWalkAccInit].filterMap lower

theorem loweredMaskedEndpoint_counts :
    loweredMaskedEndpointDeg2.length = 2 ∧
      loweredMaskedEndpointDeg4.length = 1 := by
  decide

theorem loweredMaskedEndpoint_degrees :
    (∀ t ∈ loweredMaskedEndpointDeg2, t.degree ≤ 2) ∧
      (∀ t ∈ loweredMaskedEndpointDeg4, t.degree ≤ 4) := by
  decide

def compMaskedOptimizedAllGates (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  maskedBaseTransitionGates ++
    compileTypedList b loweredExtTransitionGates ++
    compileTypedList b loweredMaskedEndpointDeg2 ++
    compileTypedList b loweredMaskedEndpointDeg4 ++
    maskedEndpointEqualityChecks

theorem compMaskedOptimizedAllGates_length (b : Basis (Fin 3) F K) :
    (compMaskedOptimizedAllGates b).length = 87 := by
  simp [compMaskedOptimizedAllGates, compileTypedList_length,
    loweredMaskedEndpoint_counts, maskedEndpointEqualityChecks]

theorem compMaskedOptimizedAllGates_degree (b : Basis (Fin 3) F K) :
    ∀ g ∈ compMaskedOptimizedAllGates b, g.degree ≤ 4 := by
  intro g hg
  simp only [compMaskedOptimizedAllGates, List.mem_append] at hg
  rcases hg with (((hb | ht) | h2) | h4) | heq
  · exact (maskedBaseTransitionGates_degree g hb).trans (by decide)
  · exact compileTypedList_degree b loweredExtTransitionGates 4
      loweredExtTransitionGates_degree g ht
  · exact (compileTypedList_degree b loweredMaskedEndpointDeg2 2
      loweredMaskedEndpoint_degrees.1 g h2).trans (by decide)
  · exact compileTypedList_degree b loweredMaskedEndpointDeg4 4
      loweredMaskedEndpoint_degrees.2 g h4
  · exact (maskedEndpointEqualityChecks_degree g heq).trans (by decide)

def compMaskedOptimizedCoreRAP {h : ℕ} (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    RAP F where
  e := 3
  k := 2
  wRAP := ![184, 3]
  w := 187
  w_eq := by rw [Fin.sum_univ_two]; norm_num
  h := h
  d := 4
  s := (compMaskedOptimizedAllGates b).length
  ω := orbit.ω
  β := orbit.βcoset
  I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
  C := fun i => coeffToMv chalVal pubVal ((compMaskedOptimizedAllGates b).get i)
  C_vars := fun i => coeffToMv_vars chalVal pubVal _
  C_deg := fun i =>
    (coeffToMv_totalDegree_le chalVal pubVal _).trans
      (compMaskedOptimizedAllGates_degree b _ (List.get_mem _ _))
  H := H
  β_ne_zero := orbit.βcoset_ne_zero
  I_bound := by
    intro q hq
    have hq2 : q.2 = 0 ∨ q.2 = 1 := by
      have h2 := (Finset.mem_product.mp hq).2
      simpa [Finset.mem_insert, Finset.mem_singleton] using h2
    have hge : 2 ≤ 2 ^ h := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) orbit.h_pos
    rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega

theorem compMaskedOptimizedCoreRAP_fingerprint {h : ℕ}
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (compMaskedOptimizedCoreRAP b chalVal pubVal orbit H).w = 187 ∧
      (compMaskedOptimizedCoreRAP b chalVal pubVal orbit H).s = 87 :=
  ⟨rfl, compMaskedOptimizedAllGates_length b⟩

/-- Slots 11 and 12 are the only verifier-fixed columns, and both lie inside round zero's exact
184-column prefix. -/
def endpointMaskRoundIndices : Fin 2 ↪ Fin 184 where
  toFun
    | 0 => 11
    | 1 => 12
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢

def compFixedPreprocessingCoreRAP {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) :
    FixedPreprocessingRAP F where
  rap := compMaskedOptimizedCoreRAP b chalVal pubVal orbit
    (rowNodeSet nodes)
  rounds_pos := by norm_num [compMaskedOptimizedCoreRAP]
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨11 + (j : ℕ), by
        change 11 + (j : ℕ) < 184
        omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

def compFixedFirstIndex {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) :
    Fin (compFixedPreprocessingCoreRAP hn nodes b chalVal pubVal orbit).fixedCount :=
  ⟨0, by simp [compFixedPreprocessingCoreRAP]⟩

def compFixedLastIndex {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) :
    Fin (compFixedPreprocessingCoreRAP hn nodes b chalVal pubVal orbit).fixedCount :=
  ⟨1, by simp [compFixedPreprocessingCoreRAP]⟩

theorem compFixedPreprocessingCoreRAP_designated_columns {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) :
    ((compFixedPreprocessingCoreRAP hn nodes b chalVal pubVal orbit).preprocessingColumn
        (compFixedFirstIndex hn nodes b chalVal pubVal orbit) : ℕ)
        = 11 ∧
      ((compFixedPreprocessingCoreRAP hn nodes b chalVal pubVal orbit).preprocessingColumn
        (compFixedLastIndex hn nodes b chalVal pubVal orbit) : ℕ)
        = 12 ∧
      (compFixedPreprocessingCoreRAP hn nodes b chalVal pubVal orbit).rap.wRAP
        ((compFixedPreprocessingCoreRAP hn nodes b chalVal pubVal orbit).rap.firstRound
          (compFixedPreprocessingCoreRAP hn nodes b chalVal pubVal orbit).rounds_pos) = 184 := by
  exact ⟨rfl, rfl, rfl⟩

theorem compFixedPreprocessingCoreRAP_wrong_first_rejected {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin 187 → F[X])
    (hwrong : P 11 ≠ firstRowMask nodes) :
    ¬ RAP.SatisfiesWithPreprocessing
      (compFixedPreprocessingCoreRAP hn nodes b chalVal pubVal orbit) P := by
  apply RAP.not_satisfiesWithPreprocessing_of_wrong
    (compFixedPreprocessingCoreRAP hn nodes b chalVal pubVal orbit) P
      (compFixedFirstIndex hn nodes b chalVal pubVal orbit)
  intro heq
  exact hwrong heq

def compFixedPreprocessingPaddedRAP {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) :
    FixedPreprocessingRAP F :=
  let R := compFixedPreprocessingCoreRAP hn nodes b chalVal pubVal orbit
  padFixedPreprocessing R
    (firstRoundExtra R.rap R.rounds_pos (computeResidualColumns 3))
    (residualTransitionGates 3)

theorem compFixedPreprocessingPaddedRAP_fingerprint {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) :
    (compFixedPreprocessingPaddedRAP hn nodes b chalVal pubVal orbit).rap.w = 199 ∧
      (compFixedPreprocessingPaddedRAP hn nodes b chalVal pubVal orbit).rap.s = 98 := by
  unfold compFixedPreprocessingPaddedRAP
  apply padComputeCore_e3_fingerprint
  · exact (compMaskedOptimizedCoreRAP_fingerprint b chalVal pubVal orbit
      (rowNodeSet nodes)).1
  · exact (compMaskedOptimizedCoreRAP_fingerprint b chalVal pubVal orbit
      (rowNodeSet nodes)).2

theorem compFixedPreprocessingPaddedRAP_satisfies_iff {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin 199 → F[X]) :
    RAP.SatisfiesWithPreprocessing
        (compFixedPreprocessingPaddedRAP hn nodes b chalVal pubVal orbit) P ↔
      let R := compFixedPreprocessingCoreRAP hn nodes b chalVal pubVal orbit
      RAP.SatisfiesWithPreprocessing R
        (projectTrace R.rap
          (firstRoundExtra R.rap R.rounds_pos (computeResidualColumns 3)) P) := by
  let R := compFixedPreprocessingCoreRAP hn nodes b chalVal pubVal orbit
  change RAP.SatisfiesWithPreprocessing
      (padFixedPreprocessing R
        (firstRoundExtra R.rap R.rounds_pos (computeResidualColumns 3))
        (residualTransitionGates 3)) P ↔
    RAP.SatisfiesWithPreprocessing R
      (projectTrace R.rap
        (firstRoundExtra R.rap R.rounds_pos (computeResidualColumns 3)) P)
  exact padFixedPreprocessing_satisfies_iff R
    (firstRoundExtra R.rap R.rounds_pos (computeResidualColumns 3))
    (residualTransitionGates 3) P

/-- Same-object all-row semantics of the fixed-preprocessing core at its exact compiled gate
boundary.  Unlike raw `RAP.Satisfies`, the right side explicitly retains polynomial-level
preprocessing binding. -/
theorem compFixedPreprocessingCoreRAP_satisfies_iff_allRows {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin 187 → F[X]) :
    RAP.SatisfiesWithPreprocessing
        (compFixedPreprocessingCoreRAP hn nodes b chalVal pubVal orbit) P ↔
      (compFixedPreprocessingCoreRAP hn nodes b chalVal pubVal orbit).BindsPreprocessing P ∧
        ∀ x ∈ rowNodeSet nodes, ∀ g ∈ compMaskedOptimizedAllGates b,
          g.eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0 := by
  let R := compFixedPreprocessingCoreRAP hn nodes b chalVal pubVal orbit
  have key : ∀ (i : Fin R.rap.s) (x : F),
      (R.rap.compose P i).eval x =
        ((compMaskedOptimizedAllGates b).get i).eval
          (Reify.envOfTrace P orbit.ω x chalVal pubVal) := by
    intro i x
    erw [Reify.compose_eval]
    exact eval_coeffToMv P orbit.ω x chalVal pubVal _
  constructor
  · rintro ⟨hraw, hfixed⟩
    refine ⟨hfixed, ?_⟩
    intro x hx g hg
    obtain ⟨i, hget⟩ := List.mem_iff_get.mp hg
    have hz := hraw i x hx
    rw [key i x] at hz
    rwa [← hget]
  · rintro ⟨hfixed, hall⟩
    refine ⟨?_, hfixed⟩
    intro i x hx
    rw [key i x]
    exact hall x hx _ (List.get_mem _ _)

#print axioms optimizedWalkEndpoint_degrees
#print axioms compOptimizedTemplate_shape
#print axioms compOptimizedTemplate_cubic_counts
#print axioms compOptimizedCoreRAP_fingerprint
#print axioms compOptimizedPaddedRAP_fingerprint
#print axioms compOptimizedPaddedRAP_satisfies_iff
#print axioms maskedWalkEndpoint_degrees
#print axioms compMaskedOptimizedCoreRAP_fingerprint
#print axioms compFixedPreprocessingCoreRAP_designated_columns
#print axioms compFixedPreprocessingCoreRAP_wrong_first_rejected
#print axioms compFixedPreprocessingPaddedRAP_fingerprint
#print axioms compFixedPreprocessingPaddedRAP_satisfies_iff
#print axioms compFixedPreprocessingCoreRAP_satisfies_iff_allRows

end
end OptimizedComputeTemplate
end Nock.NockVMROM.Thm54
