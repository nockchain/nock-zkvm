import Nock.MemoryTable
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace
import Nock.NockVMROM.Thm54.CoordinateRAPCore
import Nock.NockVMROM.Thm54.ExprSubstitution
import Nock.NockVMROM.Thm54.MemoryFactorizationScope
import Nock.NockVMROM.Thm54.MemoryWalkLabel

/-!
# Complete folded source basis for optimized memory

The twenty-one extension transition bodies fold the disjoint 40-source partition after selector,
mask, terminal, accumulator, and chain equations are assigned to authoritative base/equality
buckets. Fold challenge `6` is disjoint from memory challenges `0..2`, forest challenge `3`, and
the scalar compression coins. Reverse extraction is stated only under the exact named per-bucket
collision exclusion.

The
row-local source list therefore falls `75 → 33` and `extensionFoldSources (K := K)` falls `82 → 40`, so
each fold bucket carries two sources instead of four and the per-row bad-challenge count falls
`61 → 19` (`OptimizedMemoryCollisionAccounting.extensionFoldFamilies_workload`). `memorySourceTemplate`'s `6/55/14/21/2/2/4` shape, `RAPPadding.memoryCoreTransitionGates = 21e+14`,
the padding and every capstone numeral are untouched. -/

namespace Nock.NockVMROM.Thm54
namespace OptimizedMemoryGateBasis

open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open CoordinateCompiler
open CoordinateBasis
open MonolithicRAP
open OptimizedMemoryCoreInventory
open MixedCoordinateCompiler
open MixedCoordinateCompiler.MixedExpr (ofExpr)
open Nock.MemoryTable (MState)

noncomputable section

variable {F K : Type} [Field F] [fieldK : Field K] [Algebra F K]
variable [FiniteDimensional F K]

def extVar (kind : VarKind) (i : ℕ) : Expr := .Var kind i

/-- **Root-mask mirror for `Expr`.**  Physical column `153` is the preprocessing
    `rootMask` (`bcur 153`).  `Expr` cannot read a base coefficient, so this is
    the 47/48 pattern: `.traceCur 153` names the column, and the K-env used
    by the hosted census lifts `algebraMap` of the F-value (see
    `withRootMaskLift`).  No new column (`w = 199`). -/
def rootMaskE : Expr := extVar .traceCur 153
def rootMaskENext : Expr := extVar .traceNext 153
def notRootMaskE : Expr := .Sub (.Const 1) rootMaskE
def notRootMaskENext : Expr := .Sub (.Const 1) rootMaskENext

/-- **Dequeue-mask mirror** (K-role `56`), the first/last-mask mechanism (`firstE`/`lastE`
    at 47/48) applied to preprocessing column `154`.  `gatherEnv` reconstructs it from
    physical columns `174..176`. -/
def dequeueMaskE : Expr := extVar .traceCur 56
def dequeueMaskENext : Expr := extVar .traceNext 56

/-- Source `35` is the extra record coordinate `C'` (deployed 𝕂-role `57`,
    the new last template role after `extCols 57 → 58`; do not shift `19..33`).
    Challenge `8` is the accounting base `λ` (`memoryKOfTuple 8`). -/
def memorySubst : VarKind → ℕ → Expr
  | .traceCur, i =>
      if i < 4 then extVar .traceCur (51 + i)
      else if i < 35 then extVar .traceCur (i - 4)
      else if i = 35 then extVar .traceCur 57
      else .Const 0
  | .traceNext, _ => .Const 0
  | .challenge, i =>
      if i < 3 then .Var .challenge i
      else if i = 8 then .Var .challenge 8
      else .Const 0
  | .publicVal, _ => .Const 0

theorem subst_memory_tc_lo (n : ℕ) (hlo : n < 4) :
    Expr.subst memorySubst (tc n) = .Var .traceCur (51 + n) := by
  simp only [tc, Expr.subst, memorySubst, extVar, hlo, if_pos]

theorem subst_memory_tc_mid (n : ℕ) (hlo : ¬ n < 4) (hhi : n < 35) :
    Expr.subst memorySubst (tc n) = .Var .traceCur (n - 4) := by
  simp only [tc, Expr.subst, memorySubst, extVar, hlo, hhi, if_false, if_pos]

/-- Form R `C'` (`recC' = tc 35`) hosts at 𝕂-role `57`. -/
theorem subst_memory_tc_cprime :
    Expr.subst memorySubst (tc 35) = .Var .traceCur 57 := by
  simp [tc, Expr.subst, memorySubst, extVar]

/-- Form R `λ` (`lamE`) is memory challenge slot `8`. -/
theorem subst_memory_lamE :
    Expr.subst memorySubst MemoryFactorizationScope.lamE = .Var .challenge 8 := by
  simp [MemoryFactorizationScope.lamE, Expr.subst, memorySubst]

theorem recC'_eval_memorySubst (env : Env K) :
    (Expr.subst memorySubst MemoryFactorizationScope.recC').eval env = env.trace 57 := by
  simp [MemoryFactorizationScope.recC', subst_memory_tc_cprime, Expr.eval]

theorem lamE_eval_memorySubst (env : Env K) :
    (Expr.subst memorySubst MemoryFactorizationScope.lamE).eval env = env.chal 8 := by
  simp [subst_memory_lamE, Expr.eval]

theorem lamScaleE_eval_memorySubst [CharP K (ringChar K)] (env : Env K) :
    (Expr.subst memorySubst (MemoryFactorizationScope.lamScaleE (K := K))).eval env =
      env.chal 8 ^ MemoryTable.pwScaleExp K := by
  simp [MemoryFactorizationScope.lamScaleE, MemoryFactorizationScope.lamE,
    Expr.subst, memorySubst, Expr.eval]

def memoryChainSubst : VarKind → ℕ → Expr
  | .traceCur, i =>
      if i < 4 then extVar .traceCur (51 + i)
      else if i < 35 then extVar .traceCur (i - 4)
      else if i = 35 then extVar .traceCur 57
      else .Const 0
  | .traceNext, i =>
      if i < 4 then extVar .traceNext (51 + i)
      else if i < 35 then extVar .traceNext (i - 4)
      else if i = 35 then extVar .traceNext 57
      else .Const 0
  | .challenge, i =>
      if i < 3 then .Var .challenge i
      else if i = 8 then .Var .challenge 8
      else .Const 0
  | .publicVal, _ => .Const 0

def walkSubst : VarKind → ℕ → Expr
  | .traceCur, i =>
      if i < 6 then extVar .traceCur (31 + i)
      else if i = 6 then rootMaskE else .Const 0
  | .traceNext, i =>
      if i < 6 then extVar .traceNext (31 + i)
      else if i = 6 then rootMaskENext else .Const 0
  | .challenge, 0 => .Var .challenge 3
  | .challenge, _ + 1 => .Const 0
  | .publicVal, 0 => .Var .publicVal 0
  | .publicVal, 1 => .Const 0
  | .publicVal, _ + 2 => .Const 0

def walkBoundarySubst : VarKind → ℕ → Expr
  | .traceCur, i =>
      if i < 6 then extVar .traceCur (31 + i)
      else if i = 6 then rootMaskE else .Const 0
  | .traceNext, _ => .Const 0
  | .challenge, 0 => .Var .challenge 3
  | .challenge, _ + 1 => .Const 0
  | .publicVal, 0 => .Var .publicVal 0
  | .publicVal, 1 => .Const 0
  | .publicVal, _ + 2 => .Const 0

def firstE : Expr := extVar .traceCur 47
def lastE : Expr := extVar .traceCur 48
def notLastE : Expr := .Sub (.Const 1) lastE

/-! ### The merged memory core

`MemoryFactorizationScope.mergedMemCore` is the twenty-seven selector-summed quantity classes. The order in which they enter the source list is a free choice — the fold's bucket assignment is
`i % 21` — and it is fixed here by `mergedCoreOrder`, which transposes classes `3 ↔ 20` and
`4 ↔ 16` against the natural order. Without them the timestamp class
would share bucket `4` with the `pole · g = 1` class — the inverse witness for
the paper, `:2080` — which reads the same committed timestamp column. -/

/-- Fold order of the twenty-seven merged quantity classes: the identity except for the
transpositions `3 ↔ 20` and `4 ↔ 16`. -/
def mergedCoreOrder : List ℕ :=
  [0, 1, 2, 20, 16, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 4, 17, 18, 19, 3,
   21, 22, 23, 24, 25, 26]

theorem mergedCoreOrder_length : mergedCoreOrder.length = 27 := by decide

/-- The chosen order is a permutation of `List.range 27`, so the ordered core is a permutation of
`MemoryFactorizationScope.mergedMemCore` and inherits every statement about it. -/
theorem mergedCoreOrder_perm_range : mergedCoreOrder.Perm (List.range 27) := by decide

/-- The row-local memory core in fold order: the merged quantity classes. -/
def mergedMemoryCore : List Expr :=
  mergedCoreOrder.map (@MemoryFactorizationScope.mergedGate K fieldK)

theorem mergedMemoryCore_perm :
    (mergedMemoryCore (K := K)).Perm (@MemoryFactorizationScope.mergedMemCore K fieldK) :=
  mergedCoreOrder_perm_range.map (@MemoryFactorizationScope.mergedGate K fieldK)

theorem mem_mergedMemoryCore_iff (e : Expr) :
    e ∈ mergedMemoryCore (K := K) ↔ e ∈ @MemoryFactorizationScope.mergedMemCore K fieldK :=
  List.Perm.mem_iff (mergedMemoryCore_perm (K := K))

theorem mergedMemoryCore_length : (mergedMemoryCore (K := K)).length = 27 := by
  simp only [mergedMemoryCore, List.length_map, mergedCoreOrder_length]

/-- **The row-local memory constraint list, merged.**  The state-variable block and the
`z · zinv = 1` witness of `Nock.Reified.memoryAIR` are unchanged; its `69` selector-gated
per-state equations are replaced by the `27` selector-summed quantity classes. -/
def mergedMemoryConstraints : List Expr :=
  memSvExprs ++ [zZinvExprM] ++ mergedMemoryCore (K := K)

theorem mergedMemoryConstraints_length : (mergedMemoryConstraints (K := K)).length = 33 := by
  have hsv : memSvExprs.length = 5 := by
    simp only [memSvExprs, memSvBoolExprs, allMStates, List.length_append, List.length_map,
      List.length_singleton]
    rfl
  simp only [mergedMemoryConstraints, List.length_append, List.length_singleton,
    mergedMemoryCore_length, hsv]

def memoryRowSources : List Expr :=
  (mergedMemoryConstraints (K := K)).map (fun e => e.subst memorySubst)

theorem memoryRowSources_length : (memoryRowSources (K := K)).length = 33 := by
  simp only [memoryRowSources, List.length_map, mergedMemoryConstraints_length]

/-! ### Completeness: the merged core vanishes wherever the per-state core does -/

theorem gateByM_mem_memPerStateGated (st : MemoryTable.MState) (e : Expr)
    (he : e ∈ @memEqBlkExprs K fieldK st ++ memInterExprs st) :
    gateByM st e ∈ @memPerStateGated K fieldK :=
  List.mem_flatMap.mpr ⟨st, mem_allMStates st, List.mem_map.mpr ⟨e, he, rfl⟩⟩

/-- Every summand of a merged gate is either literally vacuous or one of the tree's own gated
per-state equations (`MemoryFactorizationScope.paddedBlock_subset_block`). -/
theorem mergedGate_eval_zero_of_perStateGated (env : Env K)
    (h : ∀ e ∈ @memPerStateGated K fieldK, e.eval env = 0) (q : ℕ) :
    (@MemoryFactorizationScope.mergedGate K fieldK q).eval env = 0 := by
  have key : ∀ st : MemoryTable.MState,
      (gateByM st (@MemoryFactorizationScope.memQuantity K fieldK st q)).eval env = 0 := by
    intro st
    by_cases hq : q < 27
    · have hlt : q < (@MemoryFactorizationScope.paddedBlock K fieldK st).length := by
        rw [MemoryFactorizationScope.paddedBlock_length]; exact hq
      have hmem : @MemoryFactorizationScope.memQuantity K fieldK st q ∈
          @MemoryFactorizationScope.paddedBlock K fieldK st := by
        rw [MemoryFactorizationScope.memQuantity, List.getD_eq_getElem _ _ hlt]
        exact List.getElem_mem hlt
      rcases MemoryFactorizationScope.paddedBlock_subset_block st _ hmem with heq | hin
      · rw [heq]; simp [gateByM, Expr.eval]
      · exact h _ (gateByM_mem_memPerStateGated st _ hin)
    · have hlt : (@MemoryFactorizationScope.paddedBlock K fieldK st).length ≤ q := by
        rw [MemoryFactorizationScope.paddedBlock_length]; omega
      rw [MemoryFactorizationScope.memQuantity, List.getD_eq_default _ _ hlt]
      simp [gateByM, Expr.eval]
  simp only [MemoryFactorizationScope.mergedGate, Expr.eval, key MemoryTable.MState.decompose,
    key MemoryTable.MState.halt, key MemoryTable.MState.read_root,
    key MemoryTable.MState.verify_child, add_zero]

/-- **Completeness of the merge.**  Any environment satisfying `memoryAIR` satisfies the merged
constraint list, with no one-hot hypothesis needed. -/
theorem mergedMemoryConstraints_eval_zero (env : Env K)
    (h : ∀ c ∈ (@memoryAIR K fieldK).constraints, c.expr.eval env = 0) :
    ∀ e ∈ mergedMemoryConstraints (K := K), e.eval env = 0 := by
  have hsv : ∀ e ∈ memSvExprs, e.eval env = 0 := fun e he =>
    h ⟨.row, e⟩ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨e, he, rfl⟩)))
  have hz : zZinvExprM.eval env = 0 :=
    h ⟨.row, zZinvExprM⟩ (List.mem_append_left _
      (List.mem_append_right _ List.mem_cons_self))
  have hgated : ∀ e ∈ @memPerStateGated K fieldK, e.eval env = 0 := fun e he =>
    h ⟨.row, e⟩ (List.mem_append_right _ (List.mem_map.mpr ⟨e, he, rfl⟩))
  intro e he
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · exact hsv e he
    · rw [List.mem_singleton.mp he]; exact hz
  · obtain ⟨q, -, rfl⟩ := List.mem_map.mp he
    exact mergedGate_eval_zero_of_perStateGated env hgated q

/-!

`MemoryFactorizationScope.mergedMemCore_iff_perStateGated` (`:366`) is stated over an arbitrary
environment under an arbitrary one-hot selector.  Here it is transported along `memorySubst`, so
it applies to the *sources* rather than to the pre-substitution core. -/

/-- The four extension selector roles `51..54` are the substituted images of the memory table's
selector columns `0..3`. -/
theorem substituted_selectorOneHot (env : Env K) (st : MemoryTable.MState)
    (hone : ∀ j : MemoryTable.MState,
      env.trace (51 + mopCol j) = if j = st then 1 else 0) :
    MemoryFactorizationScope.SelectorOneHot (Env.ofSubst memorySubst env) st := by
  intro j
  have := hone j
  cases j <;>
    simpa [Reified.tc, Expr.eval, Env.ofSubst, memorySubst, extVar, mopCol] using this


theorem mergedMemoryCore_subst_iff_perStateGated
    (env : Env K) (st : MemoryTable.MState)
    (hone : MemoryFactorizationScope.SelectorOneHot (Env.ofSubst memorySubst env) st) :
    (∀ g ∈ mergedMemoryCore (K := K), (g.subst memorySubst).eval env = 0)
      ↔ (∀ e ∈ @memPerStateGated K fieldK, e.eval (Env.ofSubst memorySubst env) = 0) := by
  rw [← MemoryFactorizationScope.mergedMemCore_iff_perStateGated
    (Env.ofSubst memorySubst env) st hone]
  constructor
  · intro hh g hg
    have := hh g ((mem_mergedMemoryCore_iff g).mpr hg)
    rwa [Expr.eval_subst] at this
  · intro hh g hg
    rw [Expr.eval_subst]
    exact hh g ((mem_mergedMemoryCore_iff g).mp hg)

/-- The merged gate reduces to the active state's quantity, after substitution. -/
theorem mergedGate_subst_eval (env : Env K) (st : MemoryTable.MState)
    (hone : MemoryFactorizationScope.SelectorOneHot (Env.ofSubst memorySubst env) st) (q : ℕ) :
    ((@MemoryFactorizationScope.mergedGate K fieldK q).subst memorySubst).eval env
      = ((@MemoryFactorizationScope.memQuantity K fieldK st q).subst memorySubst).eval env := by
  rw [Expr.eval_subst, Expr.eval_subst]
  exact MemoryFactorizationScope.mergedGate_eval _ st hone q

/-- A merged gate is a selector-weighted sum, so it vanishes at any environment whose four
extension selector roles are all zero — no unfolding of the quantity blocks required. -/
theorem mergedGate_subst_eval_zero_of_selectors_zero (env : Env K)
    (h51 : env.trace 51 = 0) (h52 : env.trace 52 = 0) (h53 : env.trace 53 = 0)
    (h54 : env.trace 54 = 0) (q : ℕ) :
    ((@MemoryFactorizationScope.mergedGate K fieldK q).subst memorySubst).eval env = 0 := by
  simp [MemoryFactorizationScope.mergedGate, gateByM, mopCol, memorySubst, Reified.tc,
    extVar, Expr.subst, Expr.eval, h51, h52, h53, h54]

/-- Named production source: the merged **counts** quantity class (`tab:v_mem` the paper),
whose active `verify_child` branch binds the committed axis through the counts recurrence
. -/
def verifyAxisSource : Expr :=
  (@MemoryFactorizationScope.mergedGate K fieldK 4).subst memorySubst

/-- Named production source: the merged **indicator** quantity class (`tab:v_mem`
the paper), whose active `read_root` branch binds the unique timestamp through the
indicator recurrence. -/
def readTimestampSource : Expr :=
  (@MemoryFactorizationScope.mergedGate K fieldK 3).subst memorySubst

theorem mergedGate_mem_mergedMemoryConstraints (q : ℕ) (hq : q ∈ mergedCoreOrder) :
    @MemoryFactorizationScope.mergedGate K fieldK q ∈ mergedMemoryConstraints (K := K) :=
  List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩)

theorem verifyAxisSource_mem : verifyAxisSource (K := K) ∈ memoryRowSources (K := K) :=
  List.mem_map.mpr ⟨_, mergedGate_mem_mergedMemoryConstraints 4
    (by decide : (4 : ℕ) ∈ mergedCoreOrder), rfl⟩

theorem readTimestampSource_mem : readTimestampSource (K := K) ∈ memoryRowSources (K := K) :=
  List.mem_map.mpr ⟨_, mergedGate_mem_mergedMemoryConstraints 3
    (by decide : (3 : ℕ) ∈ mergedCoreOrder), rfl⟩

/-- The `verify_child` branch of the merged counts class. -/
theorem verifyAxisSource_eval_active (env : Env K)
    (hone : MemoryFactorizationScope.SelectorOneHot (Env.ofSubst memorySubst env)
      MemoryTable.MState.verify_child) :
    (verifyAxisSource (K := K)).eval env
      = ((@MemoryFactorizationScope.memQuantity K fieldK MemoryTable.MState.verify_child 4).subst
          memorySubst).eval env :=
  mergedGate_subst_eval env MemoryTable.MState.verify_child hone 4

/-- The `read_root` branch of the merged indicator class. -/
theorem readTimestampSource_eval_active (env : Env K)
    (hone : MemoryFactorizationScope.SelectorOneHot (Env.ofSubst memorySubst env)
      MemoryTable.MState.read_root) :
    (readTimestampSource (K := K)).eval env
      = ((@MemoryFactorizationScope.memQuantity K fieldK MemoryTable.MState.read_root 3).subst
          memorySubst).eval env :=
  mergedGate_subst_eval env MemoryTable.MState.read_root hone 3

def memoryChainSource : Expr :=
  .Mul notLastE (Trans.icurChainExpr.subst memoryChainSubst)

def walkBoundarySources : List Expr :=
  [Trans.walkLn1, Trans.walkCount1, Trans.walkAccInitMasked].map
    (fun e => .Mul firstE (e.subst walkBoundarySubst))

/-- Ln/count stay `(1−last)`-gated.  The acc step is the same degree-4 split
    as `walkAccStepInGate`: `dequeueMask·ln·cur + notLast·(Δacc − count·cc)`. -/
def walkAccStepHosted : Expr :=
  Expr.Add
    (Expr.Mul dequeueMaskE ((Expr.Mul (Trans.tn 0) (Trans.tn 3)).subst walkSubst))
    (Expr.Mul notLastE
      ((Expr.Sub (Expr.Sub (Trans.tn 2) (Reified.tc 2))
          (Expr.Mul (Reified.tc 1) (Trans.tn 4))).subst walkSubst))

def walkLnCountTransitionSources : List Expr :=
  [Trans.walkLnStep, Trans.walkCountStep].map
    (fun e => Expr.Mul notLastE (e.subst walkSubst))

def walkTransitionSources : List Expr :=
  walkLnCountTransitionSources ++ [walkAccStepHosted]

/-- Current-row sampled response controls.  Roles `37..50` are the fourteen sampled-memory roles
from the codec. -/
def sampledSources : List Expr :=
  [ .Sub (.Mul (extVar .traceCur 50) (extVar .traceCur 38)) (.Const 1),
    .Mul (extVar .traceCur 39)
      (.Sub (extVar .traceCur 39) (.Const 1)),
    .Sub (extVar .traceCur 42)
      (.Mul (extVar .traceCur 39) (extVar .traceCur 38)),
    .Sub (extVar .traceCur 44)
      (.Add (extVar .traceCur 43) (extVar .traceCur 42)),
    .Sub (extVar .traceCur 50)
      (.Add (.Mul (extVar .traceCur 39) (extVar .traceCur 37))
        (.Sub (.Const 1) (extVar .traceCur 39))),
    .Mul (extVar .traceCur 47)
      (.Sub (extVar .traceCur 47) (.Const 1)),
    .Mul (extVar .traceCur 48)
      (.Sub (extVar .traceCur 48) (.Const 1)),
    .Mul (extVar .traceCur 47) (extVar .traceCur 43),
    .Mul (extVar .traceCur 48)
      (.Sub (extVar .traceCur 44) (extVar .traceCur 40)),
    .Sub (extVar .traceCur 40) (extVar .publicVal 2) ]

def forestCountSource : Expr := walkBoundarySources.get ⟨1, by decide⟩
def forestSeedSource : Expr := walkBoundarySources.get ⟨2, by decide⟩
def denominatorSource : Expr := sampledSources.get ⟨0, by decide⟩
def multiplicitySource : Expr := sampledSources.get ⟨1, by decide⟩

theorem forestCountSource_mem : forestCountSource ∈ walkBoundarySources :=
  List.get_mem _ _

theorem forestSeedSource_mem : forestSeedSource ∈ walkBoundarySources :=
  List.get_mem _ _

theorem denominatorSource_mem : denominatorSource ∈ sampledSources :=
  List.get_mem _ _

theorem multiplicitySource_mem : multiplicitySource ∈ sampledSources :=
  List.get_mem _ _

/-- Lift physical column `153` into `Expr` as `algebraMap` of the F-valued root
    mask.  Column `154` is mirrored by K-role `56` (`dequeueMaskE` /
    `dequeueMaskMixed`), the 47/48 mechanism; `gatherEnv` reconstructs it. -/
def withRootMaskLift (eK : Env K) (eF : Env F) : Env K where
  trace := fun i =>
    if i = 153 then algebraMap F K (eF.trace 153)
    else eK.trace i
  traceNext := fun i =>
    if i = 153 then algebraMap F K (eF.traceNext 153)
    else eK.traceNext i
  chal := eK.chal
  pub := eK.pub

/-- Coherent mutation of one extension-valued current-row role. -/
def mutateExtensionTrace (env : Env K) (role : ℕ) (δ : K) : Env K where
  trace q := if q = role then env.trace q + δ else env.trace q
  traceNext := env.traceNext
  chal := env.chal
  pub := env.pub

/-- Coherent mutation of one extension-valued public role. -/
def mutateExtensionPublic (env : Env K) (role : ℕ) (δ : K) : Env K where
  trace := env.trace
  traceNext := env.traceNext
  chal := env.chal
  pub q := if q = role then env.pub q + δ else env.pub q

/-- The substituted selector one-hot at `verify_child` from its four extension roles. -/
theorem selectorRoles_oneHot_verify (env : Env K)
    (h51 : env.trace 51 = 0) (h52 : env.trace 52 = 0) (h53 : env.trace 53 = 0)
    (h54 : env.trace 54 = 1) :
    MemoryFactorizationScope.SelectorOneHot (Env.ofSubst memorySubst env)
      MemoryTable.MState.verify_child := by
  refine substituted_selectorOneHot env _ ?_
  intro j; cases j <;> simpa [mopCol] using ‹_›

/-- The substituted selector one-hot at `read_root` from its four extension roles. -/
theorem selectorRoles_oneHot_read (env : Env K)
    (h51 : env.trace 51 = 0) (h52 : env.trace 52 = 0) (h53 : env.trace 53 = 1)
    (h54 : env.trace 54 = 0) :
    MemoryFactorizationScope.SelectorOneHot (Env.ofSubst memorySubst env)
      MemoryTable.MState.read_root := by
  refine substituted_selectorOneHot env _ ?_
  intro j; cases j <;> simpa [mopCol] using ‹_›

/-- Syntactic variable support of an expression. -/
def exprVariableSupport : Expr → Finset (VarKind × ℕ)
  | .Const _ => ∅
  | .Var k i => {(k, i)}
  | .Add x y | .Sub x y | .Mul x y => exprVariableSupport x ∪ exprVariableSupport y
  | .Neg x | .Pow x _ => exprVariableSupport x

/-- Read a variable off an environment. -/
def envAt (env : Env K) : VarKind → ℕ → K
  | .traceCur, i => env.trace i
  | .traceNext, i => env.traceNext i
  | .challenge, i => env.chal i
  | .publicVal, i => env.pub i

theorem lift_agree_off_masks (envK : Env K) (envF : Env F)
    (k : VarKind) {n : ℕ} (h153 : n ≠ 153) (h154 : n ≠ 154) :
    envAt (withRootMaskLift envK envF) k n = envAt envK k n := by
  cases k <;> simp [envAt, withRootMaskLift, h153, h154]

/-- Two environments agreeing on an expression's support evaluate it alike. -/
theorem eval_eq_of_support_agree (env env' : Env K) :
    ∀ e : Expr, (∀ v ∈ exprVariableSupport e, envAt env' v.1 v.2 = envAt env v.1 v.2) →
      e.eval env' = e.eval env
  | .Const _, _ => rfl
  | .Var k i, h => by
      have := h (k, i) (by simp [exprVariableSupport])
      cases k <;> simpa [envAt, Expr.eval] using this
  | .Add x y, h => by
      simp only [exprVariableSupport, Finset.mem_union] at h
      simp [Expr.eval, eval_eq_of_support_agree env env' x (fun v hv => h v (Or.inl hv)),
        eval_eq_of_support_agree env env' y (fun v hv => h v (Or.inr hv))]
  | .Sub x y, h => by
      simp only [exprVariableSupport, Finset.mem_union] at h
      simp [Expr.eval, eval_eq_of_support_agree env env' x (fun v hv => h v (Or.inl hv)),
        eval_eq_of_support_agree env env' y (fun v hv => h v (Or.inr hv))]
  | .Mul x y, h => by
      simp only [exprVariableSupport, Finset.mem_union] at h
      simp [Expr.eval, eval_eq_of_support_agree env env' x (fun v hv => h v (Or.inl hv)),
        eval_eq_of_support_agree env env' y (fun v hv => h v (Or.inr hv))]
  | .Neg x, h => by
      simp only [exprVariableSupport] at h
      simp [Expr.eval, eval_eq_of_support_agree env env' x h]
  | .Pow x n, h => by
      simp only [exprVariableSupport] at h
      simp [Expr.eval, eval_eq_of_support_agree env env' x h]

/-- A coherent current-row mutation is invisible to any source that does not read the role. -/
theorem eval_mutateExtensionTrace_of_not_mem_support
    (role : ℕ) (env : Env K) (δ : K) :
    ∀ e : Expr, (VarKind.traceCur, role) ∉ exprVariableSupport e →
      e.eval (mutateExtensionTrace env role δ) = e.eval env
  | .Const _, _ => rfl
  | .Var k i, h => by
      rcases k with _ | _ | _ | _ <;>
        simp_all [exprVariableSupport, Expr.eval, mutateExtensionTrace] <;>
        omega
  | .Add x y, h => by
      simp only [exprVariableSupport, Finset.mem_union, not_or] at h
      simp [Expr.eval, eval_mutateExtensionTrace_of_not_mem_support role env δ x h.1,
        eval_mutateExtensionTrace_of_not_mem_support role env δ y h.2]
  | .Sub x y, h => by
      simp only [exprVariableSupport, Finset.mem_union, not_or] at h
      simp [Expr.eval, eval_mutateExtensionTrace_of_not_mem_support role env δ x h.1,
        eval_mutateExtensionTrace_of_not_mem_support role env δ y h.2]
  | .Mul x y, h => by
      simp only [exprVariableSupport, Finset.mem_union, not_or] at h
      simp [Expr.eval, eval_mutateExtensionTrace_of_not_mem_support role env δ x h.1,
        eval_mutateExtensionTrace_of_not_mem_support role env δ y h.2]
  | .Neg x, h => by
      simp only [exprVariableSupport] at h
      simp [Expr.eval, eval_mutateExtensionTrace_of_not_mem_support role env δ x h]
  | .Pow x n, h => by
      simp only [exprVariableSupport] at h
      simp [Expr.eval, eval_mutateExtensionTrace_of_not_mem_support role env δ x h]

open Lean Meta Elab Tactic in
/-- Kernel WHNF under constructors. Binders are opened as free variables:
the kernel rejects loose `bvar`s. `exprVariableSupport` of `.Pow` ignores the
exponent, so `pwScaleExp K` disappears without reducing `ringChar`. -/
private partial def kernelNorm (e : Lean.Expr) : MetaM Lean.Expr := do
  let env ← getEnv
  let lctx ← getLCtx
  match Kernel.whnf env lctx e with
  | .error ex =>
    let kind : String := match ex with
      | .deterministicTimeout => "deterministic timeout"
      | .deepRecursion => "deep recursion"
      | .excessiveMemory => "excessive memory"
      | .interrupted => "interrupted"
      | .other msg => s!"other: {msg}"
      | .unknownConstant _ n => s!"unknown constant {n}"
      | .declHasMVars _ n _ => s!"has mvars {n}"
      | .declHasFVars _ n _ => s!"has fvars {n}"
      | .funExpected .. => "fun expected"
      | .typeExpected .. => "type expected"
      | .exprTypeMismatch .. => "expr type mismatch"
      | .appTypeMismatch .. => "app type mismatch"
      | .invalidProj .. => "invalid proj"
      | .letTypeMismatch _ _ n _ _ => s!"let mismatch {n}"
      | .alreadyDeclared _ n => s!"already declared {n}"
      | .declTypeMismatch .. => "decl type mismatch"
      | .thmTypeIsNotProp .. => "thm type is not prop"
    throwError s!"reduce_decide: kernel reduction failed ({kind})"
  | .ok e =>
    match e with
    | .lit _ | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ =>
      return e
    | .app .. =>
      let mut args : Array Lean.Expr := Array.mkEmpty e.getAppNumArgs
      for a in e.getAppArgs do
        args := args.push (← kernelNorm a)
      return mkAppN e.getAppFn args
    | .forallE n d b bi =>
      let d ← kernelNorm d
      withLocalDecl n bi d fun fv => do
        mkForallFVars #[fv] (← kernelNorm (b.instantiate1 fv))
    | .lam n d b bi =>
      let d ← kernelNorm d
      withLocalDecl n bi d fun fv => do
        mkLambdaFVars #[fv] (← kernelNorm (b.instantiate1 fv))
    | .letE n t v b _ =>
      let t ← kernelNorm t
      let v ← kernelNorm v
      withLetDecl n t v fun fv => do
        mkLetFVars #[fv] (← kernelNorm (b.instantiate1 fv))
    | .mdata md e => return .mdata md (← kernelNorm e)
    | .proj s i e => return .proj s i (← kernelNorm e)

open Lean Meta Elab Tactic in
/-- Kernel-reduce a goal, then `decide` the closed list. -/
elab "reduce_decide" : tactic => do
  let g ← getMainGoal
  let ty ← kernelNorm (← instantiateMVars (← g.getType))
  if ty.hasFVar || ty.hasMVar then
    throwError m!"reduce_decide left free variables: {ty}"
  let g ← g.change ty
  replaceMainGoal [g]
  evalTactic (← `(tactic| decide))

open Lean Meta Elab Tactic in
/-- Reduce only the two sides of a concrete `≤` goal.
`Expr.powDegree` sends a degree-0 base to `0` without reducing `pwScaleExp K`. -/
elab "degree_le" : tactic => do
  let g ← getMainGoal
  let ty ← whnf (← instantiateMVars (← g.getType))
  let some fn := ty.getAppFn.constName?
    | throwError m!"degree goal head is not a constant: {ty}"
  let (lhs, rhs) ←
    if fn == ``Nat.le then pure (ty.getArg! 0, ty.getArg! 1)
    else if fn == ``LE.le then pure (ty.getArg! 2, ty.getArg! 3)
    else throwError m!"degree goal is {fn}"
  let lhs ← reduce lhs (skipProofs := false)
  let rhs ← reduce rhs (skipProofs := false)
  let natOf (e : Lean.Expr) (what : String) : MetaM ℕ := do
    match e with
    | .lit (.natVal n) => pure n
    | _ =>
      match e.nat? with
      | some n => pure n
      | none => throwError m!"{what} did not reduce: {e}"
  let n ← natOf lhs "degree"
  let m ← natOf rhs "bound"
  if n ≤ m then
    let litN := Syntax.mkNumLit s!"{n}"
    let litM := Syntax.mkNumLit s!"{m}"
    let pf ← elabTerm (← `(term| (by decide : $litN ≤ $litM))) (← g.getType)
    g.assign pf
  else
    throwError s!"degree {n} exceeds {m}"

private theorem getElem_congr_list {α : Type} {l l' : List α} (h : l = l')
    {i : ℕ} (hi : i < l.length) :
    l[i] = l'[i]'(h ▸ hi) := by
  subst h
  rfl

/-- The same for a coherent public-value mutation. -/
theorem eval_mutateExtensionPublic_of_not_mem_support
    (role : ℕ) (env : Env K) (δ : K) :
    ∀ e : Expr, (VarKind.publicVal, role) ∉ exprVariableSupport e →
      e.eval (mutateExtensionPublic env role δ) = e.eval env
  | .Const _, _ => rfl
  | .Var k i, h => by
      rcases k with _ | _ | _ | _ <;>
        simp_all [exprVariableSupport, Expr.eval, mutateExtensionPublic] <;>
        omega
  | .Add x y, h => by
      simp only [exprVariableSupport, Finset.mem_union, not_or] at h
      simp [Expr.eval, eval_mutateExtensionPublic_of_not_mem_support role env δ x h.1,
        eval_mutateExtensionPublic_of_not_mem_support role env δ y h.2]
  | .Sub x y, h => by
      simp only [exprVariableSupport, Finset.mem_union, not_or] at h
      simp [Expr.eval, eval_mutateExtensionPublic_of_not_mem_support role env δ x h.1,
        eval_mutateExtensionPublic_of_not_mem_support role env δ y h.2]
  | .Mul x y, h => by
      simp only [exprVariableSupport, Finset.mem_union, not_or] at h
      simp [Expr.eval, eval_mutateExtensionPublic_of_not_mem_support role env δ x h.1,
        eval_mutateExtensionPublic_of_not_mem_support role env δ y h.2]
  | .Neg x, h => by
      simp only [exprVariableSupport] at h
      simp [Expr.eval, eval_mutateExtensionPublic_of_not_mem_support role env δ x h]
  | .Pow x n, h => by
      simp only [exprVariableSupport] at h
      simp [Expr.eval, eval_mutateExtensionPublic_of_not_mem_support role env δ x h]

theorem verifyAxisSource_mutation_rejected (env : Env K) (δ : K)
    (h51 : env.trace 51 = 0) (h52 : env.trace 52 = 0) (h53 : env.trace 53 = 0)
    (hsel : env.trace 54 = 1) (hLam : env.chal 8 ≠ 0)
    (hz : (verifyAxisSource (K := K)).eval env = 0) (hδ : δ ≠ 0) :
    (verifyAxisSource (K := K)).eval (mutateExtensionTrace env 26 δ) ≠ 0 := by
  have hone := selectorRoles_oneHot_verify env h51 h52 h53 hsel
  have honeBad := selectorRoles_oneHot_verify (mutateExtensionTrace env 26 δ)
    (by simpa [mutateExtensionTrace] using h51) (by simpa [mutateExtensionTrace] using h52)
    (by simpa [mutateExtensionTrace] using h53) (by simpa [mutateExtensionTrace] using hsel)
  rw [verifyAxisSource_eval_active env hone] at hz
  rw [verifyAxisSource_eval_active _ honeBad]
  simp [MemoryFactorizationScope.memQuantity, MemoryFactorizationScope.paddedBlock,
    MemoryFactorizationScope.blockVerifyChild, MemoryFactorizationScope.lamScaleE,
    MemoryFactorizationScope.lamE, MemoryFactorizationScope.pwScaleExp,
    memorySubst, Reified.tc, Expr.subst, Expr.eval, mutateExtensionTrace, extVar] at hz ⊢
  intro hbad
  have hpow : env.chal 8 ^ MemoryTable.pwScaleExp K ≠ 0 := pow_ne_zero _ hLam
  apply mul_ne_zero hδ hpow
  linear_combination hz - hbad

theorem readTimestampSource_mutation_rejected (env : Env K) (δ : K)
    (h51 : env.trace 51 = 0) (h52 : env.trace 52 = 0) (hsel : env.trace 53 = 1)
    (h54 : env.trace 54 = 0) (hLam : env.chal 8 ≠ 0)
    (haxis : env.trace 25 ≠ 0)
    (hz : (readTimestampSource (K := K)).eval env = 0) (hδ : δ ≠ 0) :
    (readTimestampSource (K := K)).eval (mutateExtensionTrace env 26 δ) ≠ 0 := by
  have hone := selectorRoles_oneHot_read env h51 h52 hsel h54
  have honeBad := selectorRoles_oneHot_read (mutateExtensionTrace env 26 δ)
    (by simpa [mutateExtensionTrace] using h51) (by simpa [mutateExtensionTrace] using h52)
    (by simpa [mutateExtensionTrace] using hsel) (by simpa [mutateExtensionTrace] using h54)
  rw [readTimestampSource_eval_active env hone] at hz
  rw [readTimestampSource_eval_active _ honeBad]
  simp [MemoryFactorizationScope.memQuantity, MemoryFactorizationScope.paddedBlock,
    MemoryFactorizationScope.blockReadRoot, MemoryFactorizationScope.lamScaleE,
    MemoryFactorizationScope.lamE, MemoryFactorizationScope.pwScaleExp,
    memorySubst, Reified.tc, Expr.subst, Expr.eval, mutateExtensionTrace, extVar] at hz ⊢
  intro hbad
  -- Form R read_root indicator: `pt − (lc − λ^{n−1} · axis · ts)`.
  -- Mutating `ts` (trace 26) changes the gate by `λ^{n−1} · axis · δ`, and `axis` is trace 25.
  have hpow : env.chal 8 ^ MemoryTable.pwScaleExp K ≠ 0 := pow_ne_zero _ hLam
  have hfac : δ * env.chal 8 ^ MemoryTable.pwScaleExp K * env.trace 25 = 0 := by
    linear_combination hbad - hz
  exact absurd hfac (mul_ne_zero (mul_ne_zero hδ hpow) haxis)

theorem forestCountSource_mutation_rejected (env : Env K) (δ : K)
    (hfirst : env.trace 47 = 1)
    (hz : forestCountSource.eval env = 0) (hδ : δ ≠ 0) :
    forestCountSource.eval (mutateExtensionTrace env 32 δ) ≠ 0 := by
  simp [forestCountSource, walkBoundarySources, firstE, walkBoundarySubst, extVar,
    Trans.walkCount1, Trans.pubv, Reified.tc, Expr.subst, Expr.eval,
    mutateExtensionTrace, hfirst] at hz ⊢
  intro hbad
  apply hδ
  linear_combination hbad - hz

/-- Mutation of the physical acc role is still rejected. -/
theorem forestSeedSource_mutation_rejected (env : Env K) (δ : K)
    (hfirst : env.trace 47 = 1)
    (hz : forestSeedSource.eval env = 0) (hδ : δ ≠ 0) :
    forestSeedSource.eval (mutateExtensionTrace env 33 δ) ≠ 0 := by
  simp [forestSeedSource, walkBoundarySources, firstE, walkBoundarySubst, extVar,
    Trans.walkAccInitMasked, Trans.pubv, Reified.tc, Expr.subst, Expr.eval,
    mutateExtensionTrace, hfirst] at hz ⊢
  intro hbad
  apply hδ
  linear_combination hbad - hz

theorem denominatorSource_mutation_rejected (env : Env K) (δ : K)
    (hinv : env.trace 50 ≠ 0)
    (hz : denominatorSource.eval env = 0) (hδ : δ ≠ 0) :
    denominatorSource.eval (mutateExtensionTrace env 38 δ) ≠ 0 := by
  simp [denominatorSource, sampledSources, extVar, Expr.eval, mutateExtensionTrace] at hz ⊢
  intro hbad
  apply mul_ne_zero hinv hδ
  linear_combination hbad - hz

theorem multiplicitySource_mutation_rejected (env : Env K)
    (hmult : env.trace 39 = 1) (h2 : (2 : K) ≠ 0) :
    multiplicitySource.eval (mutateExtensionTrace env 39 1) ≠ 0 := by
  simp [multiplicitySource, sampledSources, extVar, Expr.eval, mutateExtensionTrace,
    hmult]
  intro h
  apply h2
  linear_combination h

/-- Complete semantic transition census before assigning each equation to one authoritative
production bucket. -/
def transitionSources : List Expr :=
  memoryRowSources (K := K) ++ [memoryChainSource] ++
    walkBoundarySources ++ walkTransitionSources ++ sampledSources

/-- The five selector equations are authoritative in base IDs `0..4`. -/
def selectorBaseSources : List Expr := (memoryRowSources (K := K)).take 5

/-- The sampled accumulator, mask booleanities, and terminal are assigned outside extension folds. -/
def sampledFoldSources : List Expr :=
  [sampledSources.get ⟨0, by decide⟩, sampledSources.get ⟨1, by decide⟩,
   sampledSources.get ⟨2, by decide⟩, sampledSources.get ⟨4, by decide⟩,
   sampledSources.get ⟨7, by decide⟩, sampledSources.get ⟨8, by decide⟩]

/-- Genuine disjoint extension-fold partition: no selector equation, promoted chain,
accumulator/terminal equation, or derived extension-mask booleanity remains here. -/
def extensionFoldSources : List Expr :=
  (memoryRowSources (K := K)).drop 5 ++ walkBoundarySources ++ walkTransitionSources ++ sampledFoldSources

/-- Ten semantic equations represented outside extension folds: five base selector equations,
the promoted chain/accumulator/terminal equations, and two derived extension-mask booleanities. -/
def authoritativeSemanticSources : List Expr :=
  (selectorBaseSources (K := K)) ++ [memoryChainSource,
    sampledSources.get ⟨3, by decide⟩, sampledSources.get ⟨5, by decide⟩,
    sampledSources.get ⟨6, by decide⟩, sampledSources.get ⟨9, by decide⟩]

theorem walkBoundarySources_length : walkBoundarySources.length = 3 := by
  simp only [walkBoundarySources, List.length_map]
  rfl

theorem walkLnCountTransitionSources_length : walkLnCountTransitionSources.length = 2 := by
  simp only [walkLnCountTransitionSources, List.length_map]
  rfl

theorem walkTransitionSources_length : walkTransitionSources.length = 3 := by
  simp only [walkTransitionSources, List.length_append, List.length_singleton,
    walkLnCountTransitionSources_length]

theorem sampledSources_length : sampledSources.length = 10 := by
  simp only [sampledSources, List.length_cons, List.length_nil]

theorem sampledFoldSources_length : sampledFoldSources.length = 6 := by
  simp only [sampledFoldSources, List.length_cons, List.length_nil]

theorem transitionSources_length : (transitionSources (K := K)).length = 50 := by
  simp only [transitionSources, List.length_append, List.length_singleton,
    memoryRowSources_length, walkBoundarySources_length, walkTransitionSources_length,
    sampledSources_length]

theorem extensionFoldSources_length : (extensionFoldSources (K := K)).length = 40 := by
  simp only [extensionFoldSources, List.length_append, List.length_drop,
    memoryRowSources_length, walkBoundarySources_length, walkTransitionSources_length,
    sampledFoldSources_length]

theorem extensionFoldSources_get_lt (n : ℕ) (h : n < 40 := by decide) :
    n < (extensionFoldSources (K := K)).length := by
  simpa [extensionFoldSources_length] using h

theorem transitionSources_get_lt (n : ℕ) (h : n < 50 := by decide) :
    n < (transitionSources (K := K)).length := by
  simpa [transitionSources_length] using h

/-- Core slot `k` of the merged constraints sits at index `6 + k`
(`5` state-variable gates, then `z·zinv`). -/
theorem memoryConstraints_core (k : Fin 27) :
    mergedMemoryConstraints (K := K)[6 + (k : ℕ)]'(by
        rw [mergedMemoryConstraints_length]; omega) =
      @MemoryFactorizationScope.mergedGate K fieldK
        (mergedCoreOrder[(k : ℕ)]'(by rw [mergedCoreOrder_length]; exact k.isLt)) := by
  have hsv : memSvExprs.length = 5 := by
    simp only [memSvExprs, memSvBoolExprs, allMStates, List.length_append, List.length_map,
      List.length_singleton]
    rfl
  have hge : memSvExprs.length ≤ 6 + (k : ℕ) := by rw [hsv]; omega
  have hcons : mergedMemoryConstraints (K := K) =
      memSvExprs ++ [zZinvExprM] ++ mergedMemoryCore (K := K) := rfl
  have hi : 6 + (k : ℕ) < (mergedMemoryConstraints (K := K)).length := by
    rw [mergedMemoryConstraints_length]; omega
  rw [getElem_congr_list hcons hi]
  have hgeOuter : (memSvExprs ++ [zZinvExprM]).length ≤ 6 + (k : ℕ) := by
    simp only [List.length_append, List.length_singleton, hsv]; omega
  rw [List.getElem_append_right hgeOuter]
  have hidx : 6 + (k : ℕ) - (memSvExprs ++ [zZinvExprM]).length = (k : ℕ) := by
    simp only [List.length_append, List.length_singleton, hsv]; omega
  simp only [hidx, mergedMemoryCore, List.getElem_map]

theorem memoryRow_coreGate (k : Fin 27) :
    memoryRowSources (K := K)[6 + (k : ℕ)]'(by rw [memoryRowSources_length]; omega) =
      ((@MemoryFactorizationScope.mergedGate K fieldK
          (mergedCoreOrder[(k : ℕ)]'(by rw [mergedCoreOrder_length]; exact k.isLt))).subst
        memorySubst) := by
  simp only [memoryRowSources, List.getElem_map, memoryConstraints_core]

theorem extensionFold_coreGate (k : Fin 27) :
    extensionFoldSources (K := K)[1 + (k : ℕ)]'(extensionFoldSources_get_lt (K := K) (1 + (k : ℕ)) (by omega)) =
      memoryRowSources (K := K)[6 + (k : ℕ)]'(by rw [memoryRowSources_length]; omega) := by
  have hi : 1 + (k : ℕ) < ((memoryRowSources (K := K)).drop 5).length := by
    simp only [List.length_drop, memoryRowSources_length]
    omega
  have hmid : 1 + (k : ℕ) <
      ((memoryRowSources (K := K)).drop 5 ++ walkBoundarySources).length := by
    simp only [List.length_append, hi]
    omega
  have hout : 1 + (k : ℕ) <
      ((memoryRowSources (K := K)).drop 5 ++ walkBoundarySources ++ walkTransitionSources).length := by
    simp only [List.length_append, hmid]
    omega
  simp only [extensionFoldSources]
  rw [List.getElem_append_left hout, List.getElem_append_left hmid,
    List.getElem_append_left hi, List.getElem_drop]
  have hidx : 5 + (1 + (k : ℕ)) = 6 + (k : ℕ) := by omega
  simp only [hidx]

theorem extensionFold_at0 :
    extensionFoldSources (K := K)[0]'(extensionFoldSources_get_lt (K := K) 0) =
      zZinvExprM.subst memorySubst := by
  have hdrop : 0 < ((memoryRowSources (K := K)).drop 5).length := by
    simp only [List.length_drop, memoryRowSources_length]
    omega
  have hmid : 0 < ((memoryRowSources (K := K)).drop 5 ++ walkBoundarySources).length := by
    simp only [List.length_append, hdrop]
    omega
  have hout : 0 <
      ((memoryRowSources (K := K)).drop 5 ++ walkBoundarySources ++ walkTransitionSources).length := by
    simp only [List.length_append, hmid]
    omega
  simp only [extensionFoldSources]
  rw [List.getElem_append_left hout, List.getElem_append_left hmid,
    List.getElem_append_left hdrop, List.getElem_drop]
  simp only [memoryRowSources, List.getElem_map]
  have hsv : memSvExprs.length = 5 := by
    simp only [memSvExprs, memSvBoolExprs, allMStates, List.length_append, List.length_map,
      List.length_singleton]
    rfl
  have hcons : mergedMemoryConstraints (K := K) =
      memSvExprs ++ [zZinvExprM] ++ mergedMemoryCore (K := K) := rfl
  have hi : 5 < (mergedMemoryConstraints (K := K)).length := by
    rw [mergedMemoryConstraints_length]; omega
  rw [getElem_congr_list hcons hi]
  have hlt : 5 < (memSvExprs ++ [zZinvExprM]).length := by
    simp only [List.length_append, List.length_singleton, hsv]
    omega
  rw [List.getElem_append_left hlt]
  have hge : memSvExprs.length ≤ 5 := by rw [hsv]
  rw [List.getElem_append_right hge]
  simp only [hsv, Nat.sub_self, List.getElem_cons_zero]

private def extensionFoldTail : List Expr :=
  walkBoundarySources ++ walkTransitionSources ++ sampledFoldSources

theorem extensionFold_eq_drop_append :
    extensionFoldSources (K := K) = (memoryRowSources (K := K)).drop 5 ++ extensionFoldTail := by
  simp only [extensionFoldSources, extensionFoldTail, List.append_assoc]

theorem extensionFold_tail_get (i : ℕ) (h28 : 28 ≤ i) (hi : i < 40) :
    extensionFoldSources (K := K)[i]'(extensionFoldSources_get_lt (K := K) i hi) =
      extensionFoldTail[i - 28]'(by
        simp only [extensionFoldTail, List.length_append, walkBoundarySources_length,
          walkTransitionSources_length, sampledFoldSources_length]
        omega) := by
  have hEq := extensionFold_eq_drop_append (K := K)
  have hge : ((memoryRowSources (K := K)).drop 5).length ≤ i := by
    simp only [List.length_drop, memoryRowSources_length]
    omega
  rw [getElem_congr_list hEq (extensionFoldSources_get_lt (K := K) i hi),
    List.getElem_append_right hge]
  have hsub : i - ((memoryRowSources (K := K)).drop 5).length = i - 28 := by
    simp only [List.length_drop, memoryRowSources_length]
  simp only [hsub]

set_option maxHeartbeats 2000000 in
/-- Class `23` sits at fold index `24`. -/
theorem extensionFoldSources_get_eq_merged23_iff (q : Fin 40) :
    (extensionFoldSources (K := K)).get ⟨q.val, extensionFoldSources_get_lt (K := K) q.val (by omega)⟩ =
      (@MemoryFactorizationScope.mergedGate K fieldK 23).subst memorySubst ↔ (q : ℕ) = 24 := by
  constructor
  · intro hEq
    by_cases h28 : (q : ℕ) < 28
    · by_cases hz : (q : ℕ) = 0
      · have : q = ⟨0, extensionFoldSources_get_lt (K := K) 0⟩ := by
          apply Fin.ext
          simpa using hz
        subst this
        exfalso
        rw [List.get_eq_getElem] at hEq
        rw [extensionFold_at0] at hEq
        injections
      · have hk : (q : ℕ) - 1 < 27 := by omega
        generalize hkfin : (⟨(q : ℕ) - 1, hk⟩ : Fin 27) = k at *
        have hkval : (k : ℕ) = (q : ℕ) - 1 := by rw [← hkfin]
        have hqk : (q : ℕ) = 1 + (k : ℕ) := by omega
        have hget : (extensionFoldSources (K := K)).get ⟨q.val, extensionFoldSources_get_lt (K := K) q.val (by omega)⟩ =
            extensionFoldSources (K := K)[1 + (k : ℕ)]'(extensionFoldSources_get_lt (K := K) (1 + (k : ℕ)) (by omega)) := by
          apply congrArg (fun i => (extensionFoldSources (K := K)).get i)
          apply Fin.ext
          simpa using hqk
        rw [hget, extensionFold_coreGate, memoryRow_coreGate] at hEq
        fin_cases k <;> first
          | omega
          | (exfalso
             have hdec : MemoryFactorizationScope.blockDecompose.getD 23 (.Const 0) =
                 .Sub (tc 32) (tc 31) := rfl
             have hhalt : MemoryFactorizationScope.blockHalt.getD 23 (.Const 0) =
                 .Sub (tc 32) (tc 31) := rfl
             have hread : (MemoryFactorizationScope.blockReadRoot (K := K)).getD 23 (.Const 0) =
                 .Sub (.Sub (tc 32) (tc 31)) (tc 33) := rfl
             have hver : (MemoryFactorizationScope.blockVerifyChild (K := K)).getD 23 (.Const 0) =
                 .Add (.Sub (tc 32) (tc 31)) (tc 33) := rfl
             have hright : MemoryFactorizationScope.mergedGate (K := K) 23 =
                 .Add (gateByM .decompose (.Sub (tc 32) (tc 31)))
                   (.Add (gateByM .halt (.Sub (tc 32) (tc 31)))
                     (.Add (gateByM .read_root (.Sub (.Sub (tc 32) (tc 31)) (tc 33)))
                       (gateByM .verify_child (.Add (.Sub (tc 32) (tc 31)) (tc 33))))) := by
               simp_rw [MemoryFactorizationScope.mergedGate, MemoryFactorizationScope.memQuantity,
                 MemoryFactorizationScope.paddedBlock, hdec, hhalt, hread, hver]
             rw [hright] at hEq
             simp only [mergedCoreOrder, List.getElem_cons_zero, List.getElem_cons_succ,
               List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
               MemoryFactorizationScope.mergedGate, MemoryFactorizationScope.memQuantity,
               MemoryFactorizationScope.paddedBlock, MemoryFactorizationScope.blockDecompose,
               MemoryFactorizationScope.blockHalt, MemoryFactorizationScope.blockReadRoot,
               MemoryFactorizationScope.blockVerifyChild, Expr.subst, gateByM, mPt, fpCol] at hEq
             simp (disch := decide) only [subst_memory_tc_lo, subst_memory_tc_mid] at hEq
             try norm_num at hEq
             try (obtain ⟨h1, h2, h3⟩ := hEq)
             try injections
             done)
    · exfalso
      have hge : 28 ≤ (q : ℕ) := by omega
      rw [List.get_eq_getElem] at hEq
      rw [extensionFold_tail_get (q : ℕ) hge (by omega)] at hEq
      fin_cases q <;> first
        | exact absurd hge (by decide)
        | injections
  · intro hq
    have : q = ⟨24, extensionFoldSources_get_lt (K := K) 24⟩ := by
      apply Fin.ext
      simpa using hq
    subst this
    have h24 : (extensionFoldSources (K := K)).get ⟨24, extensionFoldSources_get_lt (K := K) 24⟩ =
        extensionFoldSources (K := K)[1 + ((⟨23, by decide⟩ : Fin 27) : ℕ)]'(
          extensionFoldSources_get_lt (K := K) (1 + ((⟨23, by decide⟩ : Fin 27) : ℕ)) (by omega)) := by
      apply congrArg (fun i => (extensionFoldSources (K := K)).get i)
      apply Fin.ext
      omega
    rw [h24, extensionFold_coreGate, memoryRow_coreGate]
    rfl

set_option maxHeartbeats 2000000 in
/-- Class `24` sits at fold index `25`. -/
theorem extensionFoldSources_get_eq_merged24_iff (q : Fin 40) :
    (extensionFoldSources (K := K)).get ⟨q.val, extensionFoldSources_get_lt (K := K) q.val (by omega)⟩ =
      (@MemoryFactorizationScope.mergedGate K fieldK 24).subst memorySubst ↔ (q : ℕ) = 25 := by
  constructor
  · intro hEq
    by_cases h28 : (q : ℕ) < 28
    · by_cases hz : (q : ℕ) = 0
      · have : q = ⟨0, extensionFoldSources_get_lt (K := K) 0⟩ := by
          apply Fin.ext
          simpa using hz
        subst this
        exfalso
        rw [List.get_eq_getElem] at hEq
        rw [extensionFold_at0] at hEq
        injections
      · have hk : (q : ℕ) - 1 < 27 := by omega
        generalize hkfin : (⟨(q : ℕ) - 1, hk⟩ : Fin 27) = k at *
        have hkval : (k : ℕ) = (q : ℕ) - 1 := by rw [← hkfin]
        have hqk : (q : ℕ) = 1 + (k : ℕ) := by omega
        have hget : (extensionFoldSources (K := K)).get ⟨q.val, extensionFoldSources_get_lt (K := K) q.val (by omega)⟩ =
            extensionFoldSources (K := K)[1 + (k : ℕ)]'(extensionFoldSources_get_lt (K := K) (1 + (k : ℕ)) (by omega)) := by
          apply congrArg (fun i => (extensionFoldSources (K := K)).get i)
          apply Fin.ext
          simpa using hqk
        rw [hget, extensionFold_coreGate, memoryRow_coreGate] at hEq
        fin_cases k <;> first
          | omega
          | (exfalso
             have hdec : MemoryFactorizationScope.blockDecompose.getD 24 (.Const 0) =
                 .Const 0 := rfl
             have hhalt : MemoryFactorizationScope.blockHalt.getD 24 (.Const 0) =
                 .Const 0 := rfl
             have hread : (MemoryFactorizationScope.blockReadRoot (K := K)).getD 24 (.Const 0) =
                 .Sub (.Mul poleExpr (tc 33)) (.Const 1) := rfl
             have hver : (MemoryFactorizationScope.blockVerifyChild (K := K)).getD 24 (.Const 0) =
                 .Sub (.Mul poleExpr (tc 33)) (.Const 1) := rfl
             have hright : MemoryFactorizationScope.mergedGate (K := K) 24 =
                 .Add (gateByM .decompose (.Const 0))
                   (.Add (gateByM .halt (.Const 0))
                     (.Add (gateByM .read_root (.Sub (.Mul poleExpr (tc 33)) (.Const 1)))
                       (gateByM .verify_child (.Sub (.Mul poleExpr (tc 33)) (.Const 1))))) := by
               simp_rw [MemoryFactorizationScope.mergedGate, MemoryFactorizationScope.memQuantity,
                 MemoryFactorizationScope.paddedBlock, hdec, hhalt, hread, hver]
             rw [hright] at hEq
             simp only [mergedCoreOrder, List.getElem_cons_zero, List.getElem_cons_succ,
               List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
               MemoryFactorizationScope.mergedGate, MemoryFactorizationScope.memQuantity,
               MemoryFactorizationScope.paddedBlock, MemoryFactorizationScope.blockDecompose,
               MemoryFactorizationScope.blockHalt, MemoryFactorizationScope.blockReadRoot,
               MemoryFactorizationScope.blockVerifyChild, Expr.subst, gateByM, mPt, fpCol] at hEq
             simp (disch := decide) only [subst_memory_tc_lo, subst_memory_tc_mid] at hEq
             try norm_num at hEq
             try (obtain ⟨h1, h2, h3⟩ := hEq)
             try injections
             done)
    · exfalso
      have hge : 28 ≤ (q : ℕ) := by omega
      rw [List.get_eq_getElem] at hEq
      rw [extensionFold_tail_get (q : ℕ) hge (by omega)] at hEq
      fin_cases q <;> first
        | exact absurd hge (by decide)
        | injections
  · intro hq
    have : q = ⟨25, extensionFoldSources_get_lt (K := K) 25⟩ := by
      apply Fin.ext
      simpa using hq
    subst this
    have h25 : (extensionFoldSources (K := K)).get ⟨25, extensionFoldSources_get_lt (K := K) 25⟩ =
        extensionFoldSources (K := K)[1 + ((⟨24, by decide⟩ : Fin 27) : ℕ)]'(
          extensionFoldSources_get_lt (K := K) (1 + ((⟨24, by decide⟩ : Fin 27) : ℕ)) (by omega)) := by
      apply congrArg (fun i => (extensionFoldSources (K := K)).get i)
      apply Fin.ext
      omega
    rw [h25, extensionFold_coreGate, memoryRow_coreGate]
    rfl

/-- The merged indicator class sits at fold index `21`, hence in bucket `0` — the production ID
its `read_root` branch carried before the merge. -/
theorem readTimestampSource_extension_index :
    (extensionFoldSources (K := K)).get ⟨21, extensionFoldSources_get_lt (K := K) 21⟩ = readTimestampSource (K := K) := by
  rfl

/-- Bucket `0`'s other source is the `z · zinv = 1` witness (`Nock/AIR.lean:1496`). -/
theorem readTimestampBucket0_index :
    (extensionFoldSources (K := K)).get ⟨0, extensionFoldSources_get_lt (K := K) 0⟩ =
      .Sub (.Mul (.Var .challenge 0) (.Var .traceCur 30)) (.Const 1) := by
  rfl

theorem readTimestamp_fold_bucket_other_unchanged (env : Env K) :
    ((extensionFoldSources (K := K)).get ⟨0, extensionFoldSources_get_lt (K := K) 0⟩).eval
        (mutateExtensionTrace env 26 1) =
      ((extensionFoldSources (K := K)).get ⟨0, extensionFoldSources_get_lt (K := K) 0⟩).eval env := by
  rw [readTimestampBucket0_index]
  simp [mutateExtensionTrace, Expr.eval]

theorem malformed_named_source_indices :
    (extensionFoldSources (K := K)).get ⟨17, extensionFoldSources_get_lt (K := K) 17⟩ = verifyAxisSource (K := K) ∧
    (extensionFoldSources (K := K)).get ⟨29, extensionFoldSources_get_lt (K := K) 29⟩ = forestCountSource ∧
    (extensionFoldSources (K := K)).get ⟨30, extensionFoldSources_get_lt (K := K) 30⟩ = forestSeedSource ∧
    (extensionFoldSources (K := K)).get ⟨34, extensionFoldSources_get_lt (K := K) 34⟩ = denominatorSource ∧
    (extensionFoldSources (K := K)).get ⟨35, extensionFoldSources_get_lt (K := K) 35⟩ = multiplicitySource := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem axis_fold_bucket_other_unchanged (env : Env K) :
    ((extensionFoldSources (K := K)).get ⟨38, extensionFoldSources_get_lt (K := K) 38⟩).eval (mutateExtensionTrace env 26 1) =
      ((extensionFoldSources (K := K)).get ⟨38, extensionFoldSources_get_lt (K := K) 38⟩).eval env := by
  rw [show (extensionFoldSources (K := K)).get ⟨38, extensionFoldSources_get_lt (K := K) 38⟩ =
      .Mul (.Var .traceCur 47) (.Var .traceCur 43) by rfl]
  simp [mutateExtensionTrace, Expr.eval]

/-- Fold index `1 + k` is merged class `mergedCoreOrder[k]`, after `memorySubst`. -/
theorem extensionFold_at_core (k : Fin 27) :
    (extensionFoldSources (K := K)).get ⟨1 + (k : ℕ),
        extensionFoldSources_get_lt (K := K) (1 + (k : ℕ)) (by omega)⟩ =
      ((@MemoryFactorizationScope.mergedGate K fieldK
          (mergedCoreOrder[(k : ℕ)]'(by rw [mergedCoreOrder_length]; exact k.isLt))).subst
        memorySubst) := by
  rw [List.get_eq_getElem, extensionFold_coreGate, memoryRow_coreGate]

/-- Class `7` (left-child leaf) does not read trace column `32`.  The four
`fold_bucket_other_unchanged` facts at indices `8/9/13/14` are this class and
its neighbours; `reduce_decide` cannot see them because other fold entries carry
`pwScaleExp K`. -/
theorem class7_fold_avoids (col : ℕ) (hcol : col = 32 ∨ col = 33 ∨ col = 38 ∨ col = 39) :
    (VarKind.traceCur, col) ∉ exprVariableSupport
      ((extensionFoldSources (K := K)).get ⟨8, extensionFoldSources_get_lt (K := K) 8⟩) := by
  have hget : (extensionFoldSources (K := K)).get ⟨8, extensionFoldSources_get_lt (K := K) 8⟩ =
      (extensionFoldSources (K := K)).get ⟨1 + ((⟨7, by decide⟩ : Fin 27) : ℕ),
        extensionFoldSources_get_lt (K := K) (1 + ((⟨7, by decide⟩ : Fin 27) : ℕ)) (by omega)⟩ := by
    apply congrArg (fun i => (extensionFoldSources (K := K)).get i)
    exact Fin.ext rfl
  rw [hget, extensionFold_at_core]
  have hdec : MemoryFactorizationScope.blockDecompose.getD 7 (.Const 0) = .Const 0 := rfl
  have hhalt : MemoryFactorizationScope.blockHalt.getD 7 (.Const 0) = mLc.leaf := rfl
  have hread : (MemoryFactorizationScope.blockReadRoot (K := K)).getD 7 (.Const 0) = .Const 0 := rfl
  have hver : (MemoryFactorizationScope.blockVerifyChild (K := K)).getD 7 (.Const 0) = .Const 0 := rfl
  simp only [mergedCoreOrder, List.getElem_cons_succ, List.getElem_cons_zero]
  simp_rw [MemoryFactorizationScope.mergedGate, MemoryFactorizationScope.memQuantity,
    MemoryFactorizationScope.paddedBlock, hdec, hhalt, hread, hver]
  simp (disch := decide) only [Expr.subst, gateByM, mLc, fpCol, tc, memorySubst, extVar,
    subst_memory_tc_lo, subst_memory_tc_mid, exprVariableSupport, mopCol]
  rcases hcol with rfl | rfl | rfl | rfl <;> decide

theorem forestCount_fold_bucket_other_unchanged (env : Env K) :
    ((extensionFoldSources (K := K)).get ⟨8, extensionFoldSources_get_lt (K := K) 8⟩).eval
        (mutateExtensionTrace env 32 1) =
      ((extensionFoldSources (K := K)).get ⟨8, extensionFoldSources_get_lt (K := K) 8⟩).eval env :=
  eval_mutateExtensionTrace_of_not_mem_support 32 env 1 _
    (class7_fold_avoids 32 (Or.inl rfl))

theorem forestSeed_fold_bucket_other_unchanged (env : Env K) :
    ((extensionFoldSources (K := K)).get ⟨9, extensionFoldSources_get_lt (K := K) 9⟩).eval
        (mutateExtensionTrace env 33 1) =
      ((extensionFoldSources (K := K)).get ⟨9, extensionFoldSources_get_lt (K := K) 9⟩).eval env := by
  -- Index 9 is merged class 8 (left-child indicator), not class 7.  Same spine,
  -- different quantity: `halt` reads `tc 12`, which `memorySubst` sends to column 8.
  have hget : (extensionFoldSources (K := K)).get ⟨9, extensionFoldSources_get_lt (K := K) 9⟩ =
      (extensionFoldSources (K := K)).get ⟨1 + ((⟨8, by decide⟩ : Fin 27) : ℕ),
        extensionFoldSources_get_lt (K := K) (1 + ((⟨8, by decide⟩ : Fin 27) : ℕ)) (by omega)⟩ := by
    apply congrArg (fun i => (extensionFoldSources (K := K)).get i)
    exact Fin.ext rfl
  rw [hget, extensionFold_at_core]
  have hdec : MemoryFactorizationScope.blockDecompose.getD 8 (.Const 0) = .Const 0 := rfl
  have hhalt : MemoryFactorizationScope.blockHalt.getD 8 (.Const 0) = tc 12 := rfl
  have hread : (MemoryFactorizationScope.blockReadRoot (K := K)).getD 8 (.Const 0) = .Const 0 := rfl
  have hver : (MemoryFactorizationScope.blockVerifyChild (K := K)).getD 8 (.Const 0) = .Const 0 := rfl
  simp only [mergedCoreOrder, List.getElem_cons_succ, List.getElem_cons_zero]
  simp_rw [MemoryFactorizationScope.mergedGate, MemoryFactorizationScope.memQuantity,
    MemoryFactorizationScope.paddedBlock, hdec, hhalt, hread, hver]
  apply eval_mutateExtensionTrace_of_not_mem_support
  simp (disch := decide) only [Expr.subst, gateByM, tc, memorySubst, extVar,
    subst_memory_tc_lo, subst_memory_tc_mid, exprVariableSupport, mopCol]
  decide

theorem denominator_fold_bucket_other_unchanged (env : Env K) :
    ((extensionFoldSources (K := K)).get ⟨13, extensionFoldSources_get_lt (K := K) 13⟩).eval
        (mutateExtensionTrace env 38 1) =
      ((extensionFoldSources (K := K)).get ⟨13, extensionFoldSources_get_lt (K := K) 13⟩).eval env := by
  have hget : (extensionFoldSources (K := K)).get ⟨13, extensionFoldSources_get_lt (K := K) 13⟩ =
      (extensionFoldSources (K := K)).get ⟨1 + ((⟨12, by decide⟩ : Fin 27) : ℕ),
        extensionFoldSources_get_lt (K := K) (1 + ((⟨12, by decide⟩ : Fin 27) : ℕ)) (by omega)⟩ := by
    apply congrArg (fun i => (extensionFoldSources (K := K)).get i)
    exact Fin.ext rfl
  rw [hget, extensionFold_at_core]
  have hdec : MemoryFactorizationScope.blockDecompose.getD 12 (.Const 0) = .Const 0 := rfl
  have hhalt : MemoryFactorizationScope.blockHalt.getD 12 (.Const 0) = mRc.leaf := rfl
  have hread : (MemoryFactorizationScope.blockReadRoot (K := K)).getD 12 (.Const 0) = mRc.leaf := rfl
  have hver : (MemoryFactorizationScope.blockVerifyChild (K := K)).getD 12 (.Const 0) = mRc.leaf := rfl
  simp only [mergedCoreOrder, List.getElem_cons_succ, List.getElem_cons_zero]
  simp_rw [MemoryFactorizationScope.mergedGate, MemoryFactorizationScope.memQuantity,
    MemoryFactorizationScope.paddedBlock, hdec, hhalt, hread, hver]
  apply eval_mutateExtensionTrace_of_not_mem_support
  simp (disch := decide) only [Expr.subst, gateByM, mRc, fpCol, tc, memorySubst, extVar,
    subst_memory_tc_lo, subst_memory_tc_mid, exprVariableSupport, mopCol]
  decide

theorem multiplicity_fold_bucket_other_unchanged (env : Env K) :
    ((extensionFoldSources (K := K)).get ⟨14, extensionFoldSources_get_lt (K := K) 14⟩).eval
        (mutateExtensionTrace env 39 1) =
      ((extensionFoldSources (K := K)).get ⟨14, extensionFoldSources_get_lt (K := K) 14⟩).eval env := by
  have hget : (extensionFoldSources (K := K)).get ⟨14, extensionFoldSources_get_lt (K := K) 14⟩ =
      (extensionFoldSources (K := K)).get ⟨1 + ((⟨13, by decide⟩ : Fin 27) : ℕ),
        extensionFoldSources_get_lt (K := K) (1 + ((⟨13, by decide⟩ : Fin 27) : ℕ)) (by omega)⟩ := by
    apply congrArg (fun i => (extensionFoldSources (K := K)).get i)
    exact Fin.ext rfl
  rw [hget, extensionFold_at_core]
  have hdec : MemoryFactorizationScope.blockDecompose.getD 13 (.Const 0) = .Const 0 := rfl
  have hhalt : MemoryFactorizationScope.blockHalt.getD 13 (.Const 0) = tc 17 := rfl
  have hread : (MemoryFactorizationScope.blockReadRoot (K := K)).getD 13 (.Const 0) = tc 17 := rfl
  have hver : (MemoryFactorizationScope.blockVerifyChild (K := K)).getD 13 (.Const 0) = tc 17 := rfl
  simp only [mergedCoreOrder, List.getElem_cons_succ, List.getElem_cons_zero]
  simp_rw [MemoryFactorizationScope.mergedGate, MemoryFactorizationScope.memQuantity,
    MemoryFactorizationScope.paddedBlock, hdec, hhalt, hread, hver]
  apply eval_mutateExtensionTrace_of_not_mem_support
  simp (disch := decide) only [Expr.subst, gateByM, tc, memorySubst, extVar,
    subst_memory_tc_lo, subst_memory_tc_mid, exprVariableSupport, mopCol]
  decide

inductive SourceAuthority
  | selectorBase
  | promotedChain
  | promotedAccumulator
  | derivedFirstMask
  | derivedLastMask
  | promotedTerminal
  | extensionFold
  deriving DecidableEq

/-- Occurrence-level source partition. The
`def` itself was updated with the merge — the promoted chain moved `75 → 33`, the accumulator
`85 → 43`, the first mask `87 → 45`, the last mask `88 → 46` and the terminal `91 → 49`, all by
the same `−42` that `memoryRowSources (K := K)` lost — but its stated reason was not. What is actually
stable is the **order** of `transitionSources (K := K)`: `memoryRowSources (K := K)` first, then the chain, the
walk boundary and transition sources, and the sampled sources last, so each index is
`33 + (offset within the tail)`. -/
def sourceAuthority (i : Fin (transitionSources (K := K)).length) : SourceAuthority :=
  if (i : ℕ) < 5 then .selectorBase
  else if (i : ℕ) = 33 then .promotedChain
  else if (i : ℕ) = 43 then .promotedAccumulator
  else if (i : ℕ) = 45 then .derivedFirstMask
  else if (i : ℕ) = 46 then .derivedLastMask
  else if (i : ℕ) = 49 then .promotedTerminal
  else .extensionFold

/-- No omission and no overlap: every original semantic-source occurrence has exactly one
authoritative production owner. -/
theorem source_partition_exact (i : Fin (transitionSources (K := K)).length) :
    ∃! a : SourceAuthority, a = sourceAuthority i := by
  exact ⟨sourceAuthority i, rfl, fun _ h => h⟩

private theorem source_partition_counts_fin50 :
    (Finset.univ.filter fun i : Fin 50 =>
        (if (i : ℕ) < 5 then SourceAuthority.selectorBase
          else if (i : ℕ) = 33 then SourceAuthority.promotedChain
          else if (i : ℕ) = 43 then SourceAuthority.promotedAccumulator
          else if (i : ℕ) = 45 then SourceAuthority.derivedFirstMask
          else if (i : ℕ) = 46 then SourceAuthority.derivedLastMask
          else if (i : ℕ) = 49 then SourceAuthority.promotedTerminal
          else SourceAuthority.extensionFold) = .selectorBase).card = 5 ∧
      (Finset.univ.filter fun i : Fin 50 =>
        (if (i : ℕ) < 5 then SourceAuthority.selectorBase
          else if (i : ℕ) = 33 then SourceAuthority.promotedChain
          else if (i : ℕ) = 43 then SourceAuthority.promotedAccumulator
          else if (i : ℕ) = 45 then SourceAuthority.derivedFirstMask
          else if (i : ℕ) = 46 then SourceAuthority.derivedLastMask
          else if (i : ℕ) = 49 then SourceAuthority.promotedTerminal
          else SourceAuthority.extensionFold) = .promotedChain).card = 1 ∧
      (Finset.univ.filter fun i : Fin 50 =>
        (if (i : ℕ) < 5 then SourceAuthority.selectorBase
          else if (i : ℕ) = 33 then SourceAuthority.promotedChain
          else if (i : ℕ) = 43 then SourceAuthority.promotedAccumulator
          else if (i : ℕ) = 45 then SourceAuthority.derivedFirstMask
          else if (i : ℕ) = 46 then SourceAuthority.derivedLastMask
          else if (i : ℕ) = 49 then SourceAuthority.promotedTerminal
          else SourceAuthority.extensionFold) = .promotedAccumulator).card = 1 ∧
      (Finset.univ.filter fun i : Fin 50 =>
        (if (i : ℕ) < 5 then SourceAuthority.selectorBase
          else if (i : ℕ) = 33 then SourceAuthority.promotedChain
          else if (i : ℕ) = 43 then SourceAuthority.promotedAccumulator
          else if (i : ℕ) = 45 then SourceAuthority.derivedFirstMask
          else if (i : ℕ) = 46 then SourceAuthority.derivedLastMask
          else if (i : ℕ) = 49 then SourceAuthority.promotedTerminal
          else SourceAuthority.extensionFold) = .derivedFirstMask).card = 1 ∧
      (Finset.univ.filter fun i : Fin 50 =>
        (if (i : ℕ) < 5 then SourceAuthority.selectorBase
          else if (i : ℕ) = 33 then SourceAuthority.promotedChain
          else if (i : ℕ) = 43 then SourceAuthority.promotedAccumulator
          else if (i : ℕ) = 45 then SourceAuthority.derivedFirstMask
          else if (i : ℕ) = 46 then SourceAuthority.derivedLastMask
          else if (i : ℕ) = 49 then SourceAuthority.promotedTerminal
          else SourceAuthority.extensionFold) = .derivedLastMask).card = 1 ∧
      (Finset.univ.filter fun i : Fin 50 =>
        (if (i : ℕ) < 5 then SourceAuthority.selectorBase
          else if (i : ℕ) = 33 then SourceAuthority.promotedChain
          else if (i : ℕ) = 43 then SourceAuthority.promotedAccumulator
          else if (i : ℕ) = 45 then SourceAuthority.derivedFirstMask
          else if (i : ℕ) = 46 then SourceAuthority.derivedLastMask
          else if (i : ℕ) = 49 then SourceAuthority.promotedTerminal
          else SourceAuthority.extensionFold) = .promotedTerminal).card = 1 ∧
      (Finset.univ.filter fun i : Fin 50 =>
        (if (i : ℕ) < 5 then SourceAuthority.selectorBase
          else if (i : ℕ) = 33 then SourceAuthority.promotedChain
          else if (i : ℕ) = 43 then SourceAuthority.promotedAccumulator
          else if (i : ℕ) = 45 then SourceAuthority.derivedFirstMask
          else if (i : ℕ) = 46 then SourceAuthority.derivedLastMask
          else if (i : ℕ) = 49 then SourceAuthority.promotedTerminal
          else SourceAuthority.extensionFold) = .extensionFold).card = 40 := by
  decide

theorem source_partition_counts :
    (Finset.univ.filter fun i : Fin (transitionSources (K := K)).length =>
      sourceAuthority i = .selectorBase).card = 5 ∧
    (Finset.univ.filter fun i : Fin (transitionSources (K := K)).length =>
      sourceAuthority i = .promotedChain).card = 1 ∧
    (Finset.univ.filter fun i : Fin (transitionSources (K := K)).length =>
      sourceAuthority i = .promotedAccumulator).card = 1 ∧
    (Finset.univ.filter fun i : Fin (transitionSources (K := K)).length =>
      sourceAuthority i = .derivedFirstMask).card = 1 ∧
    (Finset.univ.filter fun i : Fin (transitionSources (K := K)).length =>
      sourceAuthority i = .derivedLastMask).card = 1 ∧
    (Finset.univ.filter fun i : Fin (transitionSources (K := K)).length =>
      sourceAuthority i = .promotedTerminal).card = 1 ∧
    (Finset.univ.filter fun i : Fin (transitionSources (K := K)).length =>
      sourceAuthority i = .extensionFold).card = 40 := by
  simp only [sourceAuthority]
  exact source_partition_counts_fin50

theorem semantic_source_census_exact :
    (transitionSources (K := K)).length = 50 ∧ (extensionFoldSources (K := K)).length = 40 :=
  ⟨transitionSources_length, extensionFoldSources_length⟩

theorem source_partition_overlap_free
    (i : Fin (transitionSources (K := K)).length) (a b : SourceAuthority)
    (ha : sourceAuthority i = a) (hb : sourceAuthority i = b) : a = b := by
  exact ha.symm.trans hb

theorem source_partition_exhaustive
    (i : Fin (transitionSources (K := K)).length) :
    sourceAuthority i = .selectorBase ∨
    sourceAuthority i = .promotedChain ∨
    sourceAuthority i = .promotedAccumulator ∨
    sourceAuthority i = .derivedFirstMask ∨
    sourceAuthority i = .derivedLastMask ∨
    sourceAuthority i = .promotedTerminal ∨
    sourceAuthority i = .extensionFold := by
  cases h : sourceAuthority i <;> simp [h]

theorem extensionFoldSources_subset_transitionSources :
    ∀ e ∈ extensionFoldSources (K := K), e ∈ transitionSources (K := K) := by
  intro e he
  simp only [extensionFoldSources, transitionSources, List.mem_append] at he ⊢
  rcases he with ((hrow | hboundary) | htransition) | hsampled
  · exact Or.inl (Or.inl (Or.inl (Or.inl (List.mem_of_mem_drop hrow))))
  · exact Or.inl (Or.inl (Or.inr hboundary))
  · exact Or.inl (Or.inr htransition)
  · right
    simp only [sampledFoldSources, List.mem_cons, List.not_mem_nil, or_false] at hsampled
    rcases hsampled with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact List.get_mem _ _

def foldChallenge : Expr := .Var .challenge 6

def sourceIndices : List (Fin (extensionFoldSources (K := K)).length) :=
  List.ofFn fun i : Fin 40 => ⟨i, by
    rw [extensionFoldSources_length]
    omega⟩

def foldAt (j : Fin 21) : Expr :=
  (sourceIndices (K := K)).foldr
    (fun (i : Fin (extensionFoldSources (K := K)).length) acc =>
      if (i : ℕ) % 21 = j then
        .Add (.Mul (.Pow foldChallenge ((i : ℕ) / 21))
          ((extensionFoldSources (K := K)).get i)) acc
      else acc)
    (.Const 0)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
/-- With `40` sources over `21` buckets the first nineteen buckets carry exactly two sources. -/
theorem foldAt_eval_two (j : Fin 21) (hj : (j : ℕ) < 19) (env : Env K) :
    (foldAt (K := K) j).eval env =
      ((extensionFoldSources (K := K)).get ⟨(j : ℕ), extensionFoldSources_get_lt (K := K) (j : ℕ)
        (by omega)⟩).eval env +
      foldChallenge.eval env *
        ((extensionFoldSources (K := K)).get ⟨(j : ℕ) + 21,
          extensionFoldSources_get_lt (K := K) ((j : ℕ) + 21) (by omega)⟩).eval env := by
  fin_cases j <;> simp [foldAt, sourceIndices, Expr.eval] at hj ⊢ <;> ring

theorem foldAt0_eval (env : Env K) :
    (foldAt (K := K) (0 : Fin 21)).eval env =
      ((extensionFoldSources (K := K)).get ⟨0, extensionFoldSources_get_lt (K := K) 0⟩).eval env +
      foldChallenge.eval env *
        ((extensionFoldSources (K := K)).get ⟨21, extensionFoldSources_get_lt (K := K) 21⟩).eval env := by
  simpa using foldAt_eval_two (0 : Fin 21) (by decide) env

theorem foldAt8_eval (env : Env K) :
    (foldAt (K := K) (8 : Fin 21)).eval env =
      ((extensionFoldSources (K := K)).get ⟨8, extensionFoldSources_get_lt (K := K) 8⟩).eval env +
      foldChallenge.eval env * ((extensionFoldSources (K := K)).get ⟨29, extensionFoldSources_get_lt (K := K) 29⟩).eval env := by
  simpa using foldAt_eval_two (8 : Fin 21) (by decide) env

theorem foldAt9_eval (env : Env K) :
    (foldAt (K := K) (9 : Fin 21)).eval env =
      ((extensionFoldSources (K := K)).get ⟨9, extensionFoldSources_get_lt (K := K) 9⟩).eval env +
      foldChallenge.eval env * ((extensionFoldSources (K := K)).get ⟨30, extensionFoldSources_get_lt (K := K) 30⟩).eval env := by
  simpa using foldAt_eval_two (9 : Fin 21) (by decide) env

theorem foldAt13_eval (env : Env K) :
    (foldAt (K := K) (13 : Fin 21)).eval env =
      ((extensionFoldSources (K := K)).get ⟨13, extensionFoldSources_get_lt (K := K) 13⟩).eval env +
      foldChallenge.eval env * ((extensionFoldSources (K := K)).get ⟨34, extensionFoldSources_get_lt (K := K) 34⟩).eval env := by
  simpa using foldAt_eval_two (13 : Fin 21) (by decide) env

theorem foldAt14_eval (env : Env K) :
    (foldAt (K := K) (14 : Fin 21)).eval env =
      ((extensionFoldSources (K := K)).get ⟨14, extensionFoldSources_get_lt (K := K) 14⟩).eval env +
      foldChallenge.eval env * ((extensionFoldSources (K := K)).get ⟨35, extensionFoldSources_get_lt (K := K) 35⟩).eval env := by
  simpa using foldAt_eval_two (14 : Fin 21) (by decide) env

theorem foldAt17_eval (env : Env K) :
    (foldAt (K := K) (17 : Fin 21)).eval env =
      ((extensionFoldSources (K := K)).get ⟨17, extensionFoldSources_get_lt (K := K) 17⟩).eval env +
      foldChallenge.eval env * ((extensionFoldSources (K := K)).get ⟨38, extensionFoldSources_get_lt (K := K) 38⟩).eval env := by
  simpa using foldAt_eval_two (17 : Fin 21) (by decide) env

def extensionTransitionGates : List Expr :=
  List.ofFn (foldAt (K := K))

theorem extensionTransitionGates_length :
    (extensionTransitionGates (K := K)).length = 21 := by
  simp [extensionTransitionGates]

def extensionGateSupportFingerprints : List (Finset (VarKind × ℕ)) :=
  (extensionTransitionGates (K := K)).map exprVariableSupport

/-- Replace exponents on degree-0 bases by `0`. -/
def zeroChallengePow : Expr → Expr
  | .Var k i => .Var k i
  | .Const c => .Const c
  | .Add a b => .Add (zeroChallengePow a) (zeroChallengePow b)
  | .Sub a b => .Sub (zeroChallengePow a) (zeroChallengePow b)
  | .Mul a b => .Mul (zeroChallengePow a) (zeroChallengePow b)
  | .Neg a => .Neg (zeroChallengePow a)
  | .Pow e n =>
      let e' := zeroChallengePow e
      if e'.degree = 0 then .Pow e' 0 else .Pow e' n

theorem degree_zeroChallengePow : ∀ e : Expr, (zeroChallengePow e).degree = e.degree := by
  intro e
  induction e with
  | Var k i => rfl
  | Const c => rfl
  | Add a b iha ihb => simp [zeroChallengePow, Expr.degree, iha, ihb]
  | Sub a b iha ihb => simp [zeroChallengePow, Expr.degree, iha, ihb]
  | Mul a b iha ihb => simp [zeroChallengePow, Expr.degree, iha, ihb]
  | Neg a ih => simp [zeroChallengePow, Expr.degree, ih]
  | Pow e n ih =>
      simp only [zeroChallengePow]
      split
      · rename_i h0
        have he : e.degree = 0 := by simpa [ih] using h0
        simp only [Expr.degree]
        rw [h0, he]
        rfl
      · simp [Expr.degree, Expr.powDegree, ih]

theorem support_zeroChallengePow : ∀ e : Expr,
    exprVariableSupport (zeroChallengePow e) = exprVariableSupport e := by
  intro e
  induction e with
  | Var k i => rfl
  | Const c => rfl
  | Add a b iha ihb => simp [zeroChallengePow, exprVariableSupport, iha, ihb]
  | Sub a b iha ihb => simp [zeroChallengePow, exprVariableSupport, iha, ihb]
  | Mul a b iha ihb => simp [zeroChallengePow, exprVariableSupport, iha, ihb]
  | Neg a ih => simp [zeroChallengePow, exprVariableSupport, ih]
  | Pow e n ih =>
      simp only [zeroChallengePow]
      split <;> simp [exprVariableSupport, ih]

/-- Drop every `.Pow` exponent.  `exprVariableSupport` does not read the exponent, and
Form R's only carrier dependence in the fold sources is `λ^{pwScaleExp K}`. -/
def erasePowExp : Expr → Expr
  | .Var k i => .Var k i
  | .Const c => .Const c
  | .Add a b => .Add (erasePowExp a) (erasePowExp b)
  | .Sub a b => .Sub (erasePowExp a) (erasePowExp b)
  | .Mul a b => .Mul (erasePowExp a) (erasePowExp b)
  | .Neg a => .Neg (erasePowExp a)
  | .Pow e _ => .Pow (erasePowExp e) 0

theorem exprVariableSupport_erasePowExp :
    ∀ e : Expr, exprVariableSupport (erasePowExp e) = exprVariableSupport e := by
  intro e
  induction e with
  | Var k i => rfl
  | Const c => rfl
  | Add a b iha ihb => simp [erasePowExp, exprVariableSupport, iha, ihb]
  | Sub a b iha ihb => simp [erasePowExp, exprVariableSupport, iha, ihb]
  | Mul a b iha ihb => simp [erasePowExp, exprVariableSupport, iha, ihb]
  | Neg a ih => simp [erasePowExp, exprVariableSupport, ih]
  | Pow e n ih => simp [erasePowExp, exprVariableSupport, ih]

theorem erasePowExp_memorySubst (k : VarKind) (i : ℕ) :
    erasePowExp (memorySubst k i) = memorySubst k i := by
  cases k with
  | traceCur => simp only [memorySubst]; split_ifs <;> simp [erasePowExp, extVar]
  | traceNext => simp [memorySubst, erasePowExp]
  | challenge => simp only [memorySubst]; split_ifs <;> simp [erasePowExp, extVar]
  | publicVal => simp [memorySubst, erasePowExp]

theorem erasePowExp_subst_memory :
    ∀ e : Expr, erasePowExp (Expr.subst memorySubst e) =
      Expr.subst memorySubst (erasePowExp e) := by
  intro e
  induction e with
  | Var k i =>
      simp only [Expr.subst, erasePowExp]
      exact erasePowExp_memorySubst k i
  | Const c => simp [Expr.subst, erasePowExp]
  | Add a b iha ihb => simp [Expr.subst, erasePowExp, iha, ihb]
  | Sub a b iha ihb => simp [Expr.subst, erasePowExp, iha, ihb]
  | Mul a b iha ihb => simp [Expr.subst, erasePowExp, iha, ihb]
  | Neg a ih => simp [Expr.subst, erasePowExp, ih]
  | Pow a n ih => simp [Expr.subst, erasePowExp, ih]

private theorem erasePowExp_getD {l₁ l₂ : List Expr}
    (h : l₁.map erasePowExp = l₂.map erasePowExp) {d : Expr}
    (hd : erasePowExp d = d) (q : ℕ) :
    erasePowExp (l₁.getD q d) = erasePowExp (l₂.getD q d) := by
  induction l₁ generalizing l₂ q with
  | nil =>
      cases l₂ with
      | nil => simp [List.getD, hd]
      | cons _ _ => simp at h
  | cons a l ih =>
      cases l₂ with
      | nil => simp at h
      | cons b m =>
          simp only [List.map_cons, List.cons.injEq] at h
          cases q with
          | zero =>
              change erasePowExp a = erasePowExp b
              exact h.1
          | succ q =>
              change erasePowExp (l.getD q d) = erasePowExp (m.getD q d)
              exact ih h.2 q

private theorem map_erase_blockReadRoot {K₁ K₂ : Type} [Field K₁] [Field K₂] :
    (MemoryFactorizationScope.blockReadRoot (K := K₁)).map erasePowExp =
      (MemoryFactorizationScope.blockReadRoot (K := K₂)).map erasePowExp := by
  simp [MemoryFactorizationScope.blockReadRoot, erasePowExp,
    MemoryFactorizationScope.lamScaleE, MemoryFactorizationScope.lamE]

private theorem map_erase_blockVerifyChild {K₁ K₂ : Type} [Field K₁] [Field K₂] :
    (MemoryFactorizationScope.blockVerifyChild (K := K₁)).map erasePowExp =
      (MemoryFactorizationScope.blockVerifyChild (K := K₂)).map erasePowExp := by
  simp [MemoryFactorizationScope.blockVerifyChild, erasePowExp,
    MemoryFactorizationScope.lamScaleE, MemoryFactorizationScope.lamE]

private theorem erasePowExp_memQuantity {K₁ K₂ : Type} [Field K₁] [Field K₂]
    (st : MemoryTable.MState) (q : ℕ) :
    erasePowExp (MemoryFactorizationScope.memQuantity (K := K₁) st q) =
      erasePowExp (MemoryFactorizationScope.memQuantity (K := K₂) st q) := by
  cases st with
  | decompose =>
      simp only [MemoryFactorizationScope.memQuantity, MemoryFactorizationScope.paddedBlock]
  | halt =>
      simp only [MemoryFactorizationScope.memQuantity, MemoryFactorizationScope.paddedBlock]
  | read_root =>
      simp only [MemoryFactorizationScope.memQuantity, MemoryFactorizationScope.paddedBlock]
      exact erasePowExp_getD map_erase_blockReadRoot (by simp [erasePowExp]) q
  | verify_child =>
      simp only [MemoryFactorizationScope.memQuantity, MemoryFactorizationScope.paddedBlock]
      exact erasePowExp_getD map_erase_blockVerifyChild (by simp [erasePowExp]) q

private theorem erasePowExp_mergedGate {K₁ K₂ : Type} [Field K₁] [Field K₂] (q : ℕ) :
    erasePowExp (MemoryFactorizationScope.mergedGate (K := K₁) q) =
      erasePowExp (MemoryFactorizationScope.mergedGate (K := K₂) q) := by
  simp only [MemoryFactorizationScope.mergedGate, gateByM, erasePowExp]
  rw [erasePowExp_memQuantity (K₁ := K₁) (K₂ := K₂) (st := .decompose),
    erasePowExp_memQuantity (K₁ := K₁) (K₂ := K₂) (st := .halt),
    erasePowExp_memQuantity (K₁ := K₁) (K₂ := K₂) (st := .read_root),
    erasePowExp_memQuantity (K₁ := K₁) (K₂ := K₂) (st := .verify_child)]

private theorem map_erase_mergedMemoryCore {K₁ K₂ : Type} [Field K₁] [Field K₂] :
    (mergedMemoryCore (K := K₁)).map erasePowExp =
      (mergedMemoryCore (K := K₂)).map erasePowExp := by
  simp only [mergedMemoryCore, List.map_map]
  congr 1
  funext q
  exact erasePowExp_mergedGate q

private theorem map_erase_mergedMemoryConstraints {K₁ K₂ : Type} [Field K₁] [Field K₂] :
    (mergedMemoryConstraints (K := K₁)).map erasePowExp =
      (mergedMemoryConstraints (K := K₂)).map erasePowExp := by
  have hcore := map_erase_mergedMemoryCore (K₁ := K₁) (K₂ := K₂)
  simp only [mergedMemoryConstraints, List.map_append, List.map_cons, List.map_nil,
    hcore]

private theorem map_erase_memoryRowSources {K₁ K₂ : Type} [Field K₁] [Field K₂] :
    (memoryRowSources (K := K₁)).map erasePowExp =
      (memoryRowSources (K := K₂)).map erasePowExp := by
  have hsub : erasePowExp ∘ Expr.subst memorySubst =
      Expr.subst memorySubst ∘ erasePowExp := by
    funext e
    exact erasePowExp_subst_memory e
  have hcons := map_erase_mergedMemoryConstraints (K₁ := K₁) (K₂ := K₂)
  simp only [memoryRowSources, List.map_map]
  rw [hsub]
  rw [← List.map_map, ← List.map_map]
  exact congrArg (List.map (Expr.subst memorySubst)) hcons

private theorem map_erase_extensionFoldSources {K₁ K₂ : Type} [Field K₁] [Field K₂] :
    (extensionFoldSources (K := K₁)).map erasePowExp =
      (extensionFoldSources (K := K₂)).map erasePowExp := by
  have hrow := map_erase_memoryRowSources (K₁ := K₁) (K₂ := K₂)
  simp only [extensionFoldSources, List.map_append, List.map_drop, hrow]

private theorem extensionFoldSource_erase_carrier {K₁ K₂ : Type} [Field K₁] [Field K₂]
    (n : ℕ) (h₁ : n < (extensionFoldSources (K := K₁)).length)
    (h₂ : n < (extensionFoldSources (K := K₂)).length) :
    erasePowExp ((extensionFoldSources (K := K₁))[n]'h₁) =
      erasePowExp ((extensionFoldSources (K := K₂))[n]'h₂) := by
  have hm := map_erase_extensionFoldSources (K₁ := K₁) (K₂ := K₂)
  have hidx : n < ((extensionFoldSources (K := K₁)).map erasePowExp).length := by
    simpa [List.length_map] using h₁
  have hget := getElem_congr_list hm hidx
  simp only [List.getElem_map] at hget
  exact hget

theorem extensionFoldSource_support_carrier {K₁ K₂ : Type} [Field K₁] [Field K₂]
    (n : ℕ) (h₁ : n < (extensionFoldSources (K := K₁)).length)
    (h₂ : n < (extensionFoldSources (K := K₂)).length) :
    exprVariableSupport ((extensionFoldSources (K := K₁))[n]'h₁) =
      exprVariableSupport ((extensionFoldSources (K := K₂))[n]'h₂) := by
  conv_lhs => rw [← exprVariableSupport_erasePowExp]
  conv_rhs => rw [← exprVariableSupport_erasePowExp]
  exact congrArg exprVariableSupport (extensionFoldSource_erase_carrier n h₁ h₂)

private theorem memoryRowSource_erase_carrier {K₁ K₂ : Type} [Field K₁] [Field K₂]
    (n : ℕ) (h₁ : n < (memoryRowSources (K := K₁)).length)
    (h₂ : n < (memoryRowSources (K := K₂)).length) :
    erasePowExp ((memoryRowSources (K := K₁))[n]'h₁) =
      erasePowExp ((memoryRowSources (K := K₂))[n]'h₂) := by
  have hm := map_erase_memoryRowSources (K₁ := K₁) (K₂ := K₂)
  have hidx : n < ((memoryRowSources (K := K₁)).map erasePowExp).length := by
    simpa [List.length_map] using h₁
  have hget := getElem_congr_list hm hidx
  simp only [List.getElem_map] at hget
  exact hget

theorem memoryRowSource_support_carrier {K₁ K₂ : Type} [Field K₁] [Field K₂]
    (n : ℕ) (h₁ : n < (memoryRowSources (K := K₁)).length)
    (h₂ : n < (memoryRowSources (K := K₂)).length) :
    exprVariableSupport ((memoryRowSources (K := K₁))[n]'h₁) =
      exprVariableSupport ((memoryRowSources (K := K₂))[n]'h₂) := by
  conv_lhs => rw [← exprVariableSupport_erasePowExp]
  conv_rhs => rw [← exprVariableSupport_erasePowExp]
  exact congrArg exprVariableSupport (memoryRowSource_erase_carrier n h₁ h₂)

theorem extensionTransition_support_zero :
    (extensionTransitionGates (K := K)).map exprVariableSupport =
      ((extensionTransitionGates (K := K)).map zeroChallengePow).map exprVariableSupport := by
  induction extensionTransitionGates (K := K) with
  | nil => rfl
  | cons e t ih => simp [support_zeroChallengePow, ih]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
theorem extensionGateSupportFingerprints_carrier
    {K₁ K₂ : Type} [Field K₁] [Field K₂] :
    extensionGateSupportFingerprints (K := K₁) =
      extensionGateSupportFingerprints (K := K₂) := by
  simp only [extensionGateSupportFingerprints, extensionTransitionGates, List.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp]
  -- Support ignores `.Pow` exponents.  Erase them before comparing carriers so
  -- `pwScaleExp K` never has to reduce, and do not unfold the source list
  -- (its `getElem` does not compute).
  fin_cases j <;>
    simp [foldAt, sourceIndices, exprVariableSupport, List.get_eq_getElem] <;>
    first
      | rw [extensionFoldSource_support_carrier (K₁ := K₁) (K₂ := K₂),
          extensionFoldSource_support_carrier (K₁ := K₁) (K₂ := K₂)]; try rfl
      | rw [extensionFoldSource_support_carrier (K₁ := K₁) (K₂ := K₂)]; try rfl

theorem prime_31 : Nat.Prime 31 := by decide

instance : Fact (Nat.Prime 31) := ⟨prime_31⟩

theorem extensionGateSupportFingerprints_nodup :
    (extensionGateSupportFingerprints (K := K)).Nodup := by
  rw [extensionGateSupportFingerprints_carrier (K₁ := K) (K₂ := ZMod 31)]
  decide

theorem extensionGateSupportFingerprints_nonempty :
    ∀ s ∈ extensionGateSupportFingerprints (K := K), s.Nonempty := by
  rw [extensionGateSupportFingerprints_carrier (K₁ := K) (K₂ := ZMod 31)]
  decide

theorem foldAt_support_eq_fingerprint (j : Fin 21) :
    exprVariableSupport (foldAt (K := K) j) =
      (extensionGateSupportFingerprints (K := K))[j.val]'(by
        simp only [extensionGateSupportFingerprints, extensionTransitionGates,
          List.length_map, List.length_ofFn]
        exact j.isLt) := by
  simp only [extensionGateSupportFingerprints, extensionTransitionGates,
    List.getElem_map, List.getElem_ofFn]

/-- Folds other than `17`/`18` do not read the two accumulator roles. Closed at
    `ZMod 31`; transport with `extensionGateSupportFingerprints_carrier`. -/
theorem extensionGateSupportFingerprints_avoid_acc :
    ∀ (j : Fin 21), (j : ℕ) ≠ 17 → (j : ℕ) ≠ 18 →
      ∀ v ∈ ({(VarKind.traceCur, 43), (VarKind.traceCur, 44),
              (VarKind.traceNext, 43), (VarKind.traceNext, 44)} : Finset (VarKind × ℕ)),
        v ∉ (extensionGateSupportFingerprints (K := ZMod 31))[j.val]'(by
          simp only [extensionGateSupportFingerprints, extensionTransitionGates,
            List.length_map, List.length_ofFn]
          exact j.isLt) := by
  set_option maxRecDepth 100000 in decide

theorem extensionFoldSource17_avoid_acc :
    ∀ v ∈ ({(VarKind.traceCur, 43), (VarKind.traceCur, 44),
            (VarKind.traceNext, 43), (VarKind.traceNext, 44)} : Finset (VarKind × ℕ)),
      v ∉ exprVariableSupport
        ((extensionFoldSources (K := ZMod 31))[17]'(
          extensionFoldSources_get_lt (K := ZMod 31) 17)) := by
  set_option maxRecDepth 100000 in decide

theorem extensionFoldSource18_avoid_acc :
    ∀ v ∈ ({(VarKind.traceCur, 43), (VarKind.traceCur, 44),
            (VarKind.traceNext, 43), (VarKind.traceNext, 44)} : Finset (VarKind × ℕ)),
      v ∉ exprVariableSupport
        ((extensionFoldSources (K := ZMod 31))[18]'(
          extensionFoldSources_get_lt (K := ZMod 31) 18)) := by
  set_option maxRecDepth 100000 in decide

/-- Transport of `extensionGateSupportFingerprints_avoid_acc` to a general carrier. -/
theorem foldAt_support_avoids_acc (j : Fin 21) (h17 : (j : ℕ) ≠ 17) (h18 : (j : ℕ) ≠ 18) :
    ∀ v ∈ ({(VarKind.traceCur, 43), (VarKind.traceCur, 44),
            (VarKind.traceNext, 43), (VarKind.traceNext, 44)} : Finset (VarKind × ℕ)),
      v ∉ exprVariableSupport (foldAt (K := K) j) := by
  intro v hv
  have hget : (extensionGateSupportFingerprints (K := K))[j.val]? =
      some (exprVariableSupport (foldAt (K := K) j)) := by
    simp only [extensionGateSupportFingerprints, extensionTransitionGates,
      List.getElem?_map, List.getElem?_ofFn, j.isLt, ↓reduceDIte, Option.map_some]
  have hget31 : (extensionGateSupportFingerprints (K := ZMod 31))[j.val]? =
      some (exprVariableSupport (foldAt (K := K) j)) := by
    rw [← extensionGateSupportFingerprints_carrier (K₁ := K) (K₂ := ZMod 31)]
    exact hget
  have hj : (j : ℕ) < (extensionGateSupportFingerprints (K := ZMod 31)).length := by
    simp only [extensionGateSupportFingerprints, extensionTransitionGates,
      List.length_map, List.length_ofFn]
    exact j.isLt
  have hsome : (extensionGateSupportFingerprints (K := ZMod 31))[j.val]? =
      some ((extensionGateSupportFingerprints (K := ZMod 31))[j.val]'hj) :=
    List.getElem?_eq_getElem hj
  have heq : exprVariableSupport (foldAt (K := K) j) =
      (extensionGateSupportFingerprints (K := ZMod 31))[j.val]'hj :=
    Option.some.inj (hget31.symm.trans hsome)
  exact heq ▸ extensionGateSupportFingerprints_avoid_acc j h17 h18 v hv

theorem extensionTransitionGates_nodup : (extensionTransitionGates (K := K)).Nodup :=
  List.Nodup.of_map exprVariableSupport extensionGateSupportFingerprints_nodup

theorem extensionTransitionGates_no_literal_zero :
    ∀ g ∈ extensionTransitionGates (K := K), g ≠ (.Const 0 : Expr) := by
  intro g hg heq
  have hs := extensionGateSupportFingerprints_nonempty
    (exprVariableSupport g) (List.mem_map.mpr ⟨g, hg, rfl⟩)
  rw [heq] at hs
  exact hs.ne_empty rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
private theorem extensionFoldSources_degree_at (n : ℕ) (hn : n < 40) :
    ((extensionFoldSources (K := K)).get
      ⟨n, by simpa [extensionFoldSources_length] using hn⟩).degree ≤ 4 := by
  interval_cases n <;> degree_le

theorem extensionFoldSources_degree :
    ∀ g ∈ extensionFoldSources (K := K), g.degree ≤ 4 := by
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
  have hn : i.1 < 40 := by
    simpa [extensionFoldSources_length] using i.isLt
  have hidx :
      (⟨i.1, by simpa [extensionFoldSources_length] using hn⟩ : Fin _) = i := by
    apply Fin.ext
    rfl
  simpa [hidx] using extensionFoldSources_degree_at (K := K) i.1 hn

theorem foldAt_degree (j : Fin 21) : (foldAt (K := K) j).degree ≤ 4 := by
  unfold foldAt
  induction (sourceIndices (K := K)) with
  | nil => simp [Expr.degree]
  | cons i t ih =>
      simp only [List.foldr_cons]
      split
      · have hs := extensionFoldSources_degree
          ((extensionFoldSources (K := K)).get i) (List.get_mem _ _)
        simp only [Expr.degree, Expr.powDegree, foldChallenge]
        exact max_le (by simpa [Nat.zero_add] using hs) ih
      · exact ih

theorem extensionTransitionGates_degree :
    ∀ g ∈ extensionTransitionGates (K := K), g.degree ≤ 4 := by
  intro g hg
  obtain ⟨j, -, rfl⟩ := List.mem_ofFn.mp hg
  exact foldAt_degree j

/-- Exact named reverse premise: no selected fold bucket cancels a nonzero source tuple at the
committed fold challenge. -/
def FoldCollisionExcluded (env : Env K) : Prop :=
  ∀ j : Fin 21,
    (foldAt (K := K) j).eval env = 0 →
      ∀ i : Fin (extensionFoldSources (K := K)).length,
        (i : ℕ) % 21 = j → ((extensionFoldSources (K := K)).get i).eval env = 0

theorem source_to_fold_complete (env : Env K)
    (h : ∀ e ∈ extensionFoldSources (K := K), e.eval env = 0) :
    ∀ g ∈ extensionTransitionGates (K := K), g.eval env = 0 := by
  intro g hg
  obtain ⟨j, -, rfl⟩ := List.mem_ofFn.mp hg
  simp only [foldAt]
  induction sourceIndices (K := K) with
  | nil => simp [Expr.eval]
  | cons i t ih =>
      simp only [List.foldr_cons]
      by_cases hj : (i : ℕ) % 21 = j
      · rw [if_pos hj]
        simp only [Expr.eval]
        rw [h ((extensionFoldSources (K := K)).get i) (List.get_mem _ _), mul_zero, zero_add]
        exact ih
      · rw [if_neg hj]
        exact ih

theorem fold_to_source_of_collision_excluded (env : Env K)
    (hfold : ∀ g ∈ extensionTransitionGates (K := K), g.eval env = 0)
    (hcollision : FoldCollisionExcluded env) :
    ∀ e ∈ extensionFoldSources (K := K), e.eval env = 0 := by
  intro e he
  obtain ⟨i, hi⟩ := List.get_of_mem he
  let j : Fin 21 := ⟨(i : ℕ) % 21, Nat.mod_lt _ (by omega)⟩
  rw [← hi]
  apply hcollision j
  · apply hfold (foldAt (K := K) j)
    exact List.mem_ofFn.mpr ⟨j, by simp⟩
  · simp [j]

/-- Fold reverse on the non-aggregator sources, plus `chal 6 ≠ 0` so a vanishing
bucket forces the aggregator class in that bucket (indices `24`/`25`) to vanish
too.  Not `canonical_foldCollisionExcluded` — no canonical environment. -/
theorem foldCollisionExcluded_of_nonagg
    (env : Env K)
    (hrest : ∀ e ∈ extensionFoldSources (K := K),
      e ≠ (@MemoryFactorizationScope.mergedGate K fieldK 23).subst memorySubst →
      e ≠ (@MemoryFactorizationScope.mergedGate K fieldK 24).subst memorySubst →
      e.eval env = 0)
    (hchal : foldChallenge.eval env ≠ 0) :
    FoldCollisionExcluded env := by
  intro j hfold q hq
  have hlen : (extensionFoldSources (K := K)).length = 40 := extensionFoldSources_length
  have hq40 : (q : ℕ) < 40 := by omega
  have hmem : (extensionFoldSources (K := K)).get q ∈ extensionFoldSources (K := K) := List.get_mem _ _
  have hgetq : (extensionFoldSources (K := K)).get q =
      (extensionFoldSources (K := K)).get ⟨q.val, by omega⟩ := rfl
  by_cases h23 : (extensionFoldSources (K := K)).get q =
      (@MemoryFactorizationScope.mergedGate K fieldK 23).subst memorySubst
  · have hidx : (q : ℕ) = 24 :=
      (extensionFoldSources_get_eq_merged23_iff ⟨q.val, hq40⟩).1 (hgetq ▸ h23)
    have hj : (j : ℕ) = 3 := by
      have hmod : (q : ℕ) % 21 = (j : ℕ) := hq
      rw [hidx] at hmod
      exact hmod.symm
    have hj19 : (j : ℕ) < 19 := by omega
    rw [foldAt_eval_two j hj19 env] at hfold
    have hother :
        ((extensionFoldSources (K := K)).get ⟨j, by omega⟩).eval env = 0 := by
      refine hrest _ (List.get_mem _ _) ?_ ?_
      · intro heq
        have : (j : ℕ) = 24 :=
          (extensionFoldSources_get_eq_merged23_iff ⟨j.val, by omega⟩).1 (by
            change (extensionFoldSources (K := K)).get ⟨j.val, _⟩ = _
            exact heq)
        omega
      · intro heq
        have : (j : ℕ) = 25 :=
          (extensionFoldSources_get_eq_merged24_iff ⟨j.val, by omega⟩).1 (by
            change (extensionFoldSources (K := K)).get ⟨j.val, _⟩ = _
            exact heq)
        omega
    have hlt : (j : ℕ) + 21 < (extensionFoldSources (K := K)).length := by
      rw [hlen, hj]; norm_num
    have hagg :
        ((extensionFoldSources (K := K)).get ⟨(j : ℕ) + 21, hlt⟩).eval env = 0 := by
      rw [hother, zero_add] at hfold
      exact (mul_eq_zero.mp hfold).resolve_left hchal
    have hqj : (q : ℕ) = (j : ℕ) + 21 := by rw [hidx, hj]
    rw [show (extensionFoldSources (K := K)).get q =
        (extensionFoldSources (K := K)).get ⟨(j : ℕ) + 21, hlt⟩ from
      congrArg _ (Fin.eq_of_val_eq hqj)]
    exact hagg
  · by_cases h24 : (extensionFoldSources (K := K)).get q =
        (@MemoryFactorizationScope.mergedGate K fieldK 24).subst memorySubst
    · have hidx : (q : ℕ) = 25 :=
        (extensionFoldSources_get_eq_merged24_iff ⟨q.val, hq40⟩).1 (hgetq ▸ h24)
      have hj : (j : ℕ) = 4 := by
        have hmod : (q : ℕ) % 21 = (j : ℕ) := hq
        rw [hidx] at hmod
        exact hmod.symm
      have hj19 : (j : ℕ) < 19 := by omega
      rw [foldAt_eval_two j hj19 env] at hfold
      have hother :
          ((extensionFoldSources (K := K)).get ⟨j, by omega⟩).eval env = 0 := by
        refine hrest _ (List.get_mem _ _) ?_ ?_
        · intro heq
          have : (j : ℕ) = 24 :=
            (extensionFoldSources_get_eq_merged23_iff ⟨j.val, by omega⟩).1 (by
              change (extensionFoldSources (K := K)).get ⟨j.val, _⟩ = _
              exact heq)
          omega
        · intro heq
          have : (j : ℕ) = 25 :=
            (extensionFoldSources_get_eq_merged24_iff ⟨j.val, by omega⟩).1 (by
              change (extensionFoldSources (K := K)).get ⟨j.val, _⟩ = _
              exact heq)
          omega
      have hlt : (j : ℕ) + 21 < (extensionFoldSources (K := K)).length := by
        rw [hlen, hj]; norm_num
      have hagg :
          ((extensionFoldSources (K := K)).get ⟨(j : ℕ) + 21, hlt⟩).eval env = 0 := by
        rw [hother, zero_add] at hfold
        exact (mul_eq_zero.mp hfold).resolve_left hchal
      have hqj : (q : ℕ) = (j : ℕ) + 21 := by rw [hidx, hj]
      rw [show (extensionFoldSources (K := K)).get q =
          (extensionFoldSources (K := K)).get ⟨(j : ℕ) + 21, hlt⟩ from
        congrArg _ (Fin.eq_of_val_eq hqj)]
      exact hagg
    · exact hrest _ hmem h23 h24

def bcur (i : ℕ) : CoeffExpr F := .var .traceCur i
def bnext (i : ℕ) : CoeffExpr F := .var .traceNext i
def bbool (e : CoeffExpr F) : CoeffExpr F := .mul e (.sub e (.const 1))
def bsum4 (kind : VarKind) : CoeffExpr F :=
  .sub (.add (.var kind 0)
    (.add (.var kind 1) (.add (.var kind 2) (.var kind 3)))) (.const 1)

/-- Physical coordinate of one extension-valued role in the `6 + 3·55` source layout. -/
def extCoord (kind : VarKind) (role : ℕ) (k : Fin 3) : CoeffExpr F :=
  .var kind (6 + 3 * role + (k : ℕ))

/-- Three independently committed coordinates of sampled source ID `9`, **the terminal binding**
`terminal − requests = 0`: the shared terminal role `40` equals the post-challenge public
`requests` (extension public role `2`, base publics `12..14`) at every row. This is
the paper's `out_mem = acc_mem(h₂)` read together with the IO consistency check
`requests = responses` (`:597`), in the tree's shared-terminal layout. Exposed without a compression challenge. -/
def sampledTerminalCoord (k : Fin 3) : CoeffExpr F :=
  .sub (extCoord .traceCur 40 k) (.var .publicVal (6 + 3 * 2 + (k : ℕ)))

/-- Three independently committed coordinates of
`responseAccNext - responseAccCur - contribution` (sampled source ID `3`). -/
def sampledAccumulatorCoord (k : Fin 3) : CoeffExpr F :=
  .sub (extCoord .traceCur 44 k)
    (.add (extCoord .traceCur 43 k) (extCoord .traceCur 42 k))

/-! ### The four retyped scalar gates, as mixed `𝕂`-valued gates -/

open MixedCoordinateCompiler in
/-- Extension first-mask role `47` binds to base column `4`. -/
def firstMaskMixed : MixedExpr F := .Sub (.Var .traceCur 47) (.Lift (bcur 4))

open MixedCoordinateCompiler in
/-- Extension last-mask role `48` binds to base column `5`. -/
def lastMaskMixed : MixedExpr F := .Sub (.Var .traceCur 48) (.Lift (bcur 5))

open MixedCoordinateCompiler in
/-- Extension dequeue-mask role `56` binds to preprocessing column `154`.
    Coin-free, degree `1` (the 47/48 pin). -/
def dequeueMaskMixed : MixedExpr F := .Sub (.Var .traceCur 56) (.Lift (bcur 154))

open MixedCoordinateCompiler in
/-- Extension selector mirror `51 + s` binds to base column `s`. -/
def selectorMixed (s : Fin 4) : MixedExpr F :=
  .Sub (.Var .traceCur (51 + (s : ℕ))) (.Lift (bcur (s : ℕ)))

open MixedCoordinateCompiler in
/-- The masked intermediate-chain gate. -/
def chainMixed : MixedExpr F :=
  .Scale (.sub (.const 1) (bcur 5)) (.Sub (.Var .traceCur 28) (.Var .traceNext 27))

open MixedCoordinateCompiler in
/-- **The response-accumulator chain** — the paper's row-to-row identity for
`acc_mem`, in the two-role layout: off the last row, the *after* accumulator of this row (role
`44`) is the *before* accumulator of the next (role `43` at the next row). It is the exact analogue of
`chainMixed` for the `intermediate` aggregator. The paper spends `e` on one accumulator column
read at two rows; the two-role layout spends `e` (the step, `sampledAccumulatorCoord`) plus this
`e` — the extra `e` is the interim price, absorbed into the inert residual padding at `e = 3`
(`RAPPadding.memoryResidualTransitionGates`) until W2's single-column accumulator. -/
def accChainMixed : MixedExpr F :=
  .Scale (.sub (.const 1) (bcur 5)) (.Sub (.Var .traceCur 44) (.Var .traceNext 43))

/-- The same identity as a `𝕂`-level source over the extension roles (mask role `48`), the shape
`memoryChainSource` has for the intermediate aggregator.  Not a member of `transitionSources (K := K)`
; the committed gate is `accChainMixed`. -/
def accChainSource : Expr :=
  .Mul notLastE (.Sub (extVar .traceCur 44) (extVar .traceNext 43))

/-! ### The 31st: the pre-`α` memory exponent carrier `reqIdx`

One round-0 `𝔽` column `reqIdx`, appended after `atom` (`CoordinateRAPTail.expandChipTail … 2`), so
no extension role moves. It has no gate of its own: it enters only as the tenth slot of the
memory record RLC (`γ⁹ · algebraMap reqIdx`), in both the IO response denominator and the
`intermediate` pole. Honest value: the exponent of the request the row answers on `read_root` /
`verify_child`, `0` elsewhere. **Deviation (recorded):** the paper commits no exponent before `α`
, and its record (`:1852`) has no such slot. -/

/-- Physical base-field column of the memory exponent carrier `reqIdx` (after `atom` at `180`). -/
def reqIdxCol : ℕ := 181

theorem reqIdxCol_eq : reqIdxCol = 181 := rfl

/-- `RLC^γ(mem_record)` over the record roles `19..26` plus `C'` at role `57`
    (`NockVM.encRec` 9-wide; `γ^8` term).  Slot `4` is sampled IO `γ`
. -/
def recordRLCExpr : Expr :=
  .Add (.Add (.Add (.Add (.Add (.Add (.Add (.Add
    (.Var .traceCur 19)
    (.Mul (.Pow (.Var .challenge 4) 1) (.Var .traceCur 20)))
    (.Mul (.Pow (.Var .challenge 4) 2) (.Var .traceCur 21)))
    (.Mul (.Pow (.Var .challenge 4) 3) (.Var .traceCur 22)))
    (.Mul (.Pow (.Var .challenge 4) 4) (.Var .traceCur 23)))
    (.Mul (.Pow (.Var .challenge 4) 5) (.Var .traceCur 24)))
    (.Mul (.Pow (.Var .challenge 4) 6) (.Var .traceCur 25)))
    (.Mul (.Pow (.Var .challenge 4) 7) (.Var .traceCur 26)))
    (.Mul (.Pow (.Var .challenge 4) 8) (.Var .traceCur 57))

open MixedCoordinateCompiler in
/-- **The 31st: the record's tenth slot**, `γ⁹ · algebraMap reqIdx` (`γ` at memory slot `4`).
Degree `1`, so the record RLC's trace degree is unchanged. -/
def reqIdxRLCTerm : MixedExpr F :=
  .Scale (bcur reqIdxCol) (.Pow (.Var .challenge 4) 9)

open MixedCoordinateCompiler in
/-- `RLC^γ(mem_record)` over the ten-slot record (31st): `recordRLCExpr` (roles `19..26`, `C'` at
role `57`) plus the base-field exponent carrier `reqIdx` at `γ⁹`. -/
def recordRLC : MixedExpr F := .Add (MixedExpr.ofExpr recordRLCExpr) reqIdxRLCTerm

open MixedCoordinateCompiler in
/-- **The response-denominator pin**:
`role 37 = pole + RLC^γ(mem_record)` — the paper's `RLC^α(x_mem(i,·)) − β` of
the paper (the coins are "the randomness `α, β` of the computation table", `:594`),
written in `FiniteIO.compress`'s additive convention `pole + Walk.rlc γ record`, so that the
honest role `37` (`OptimizedMemorySemanticRealization.responseDenominator =
FiniteIO.compress A.sampled.coins (NockVM.encRec mem)`) satisfies it literally.  `γ` is read from
memory `𝕂` challenge slot `4` and `pole` from slot `5`, both pinned to the sampled IO coins by
`OptimizedProductionAcceptanceAt.memory_sampled_coins`; the record fields are extension roles
`19..26`.  Degree `1`.  Until this gate the denominator was a free column: exactly one source
(the safe normalisation) read role `37`, and `Nock/RedTeam/Batch271Thm54AnchoringReview.lean`
 exhibited an accepted trace at `P.memoryChip` with two response denominators
swapped for a compensating pair.  This gate is the twin of the compute chip's three denominator
pins (`OptimizedComputeHostileAccumulator.slotDenominator_eq_compress`), and is the same term
as W2's `MemoryPaperFactorization.denominatorPin`. -/
def denominatorPinMixed : MixedExpr F :=
  .Sub (.Var .traceCur 37) (.Add (.Var .challenge 5) recordRLC)

/-! ### W2 stage 2: the paper-shaped committed gate set

Production swap: `memorySourceTemplate` commits these lists, not the fold. `ChipTemplate.extDeg1`/`extDeg3` are `Expr`-typed with degree fields `≤ 1`/`≤ 3`; the paper
endpoints are `MixedExpr.Scale` of a base preprocessing mask and so have degree `2`. They cannot inhabit those buckets. `MaskedChipTemplate` solves the `Expr` case only. Extending `ChipTemplate` would touch
`CoordinateRAPCore` (shared with the W3 compute swap). The paper's `:1487-1489` formulas
are kept as `memoryDegreeOneGatesPaper` / `memoryDegreeThreeGatesPaper` / the equality
`4` under `memoryEqualityChecksPaper`; the
tree's honest counts are `0`/`0`/`0` with every paper `𝕂` gate billed in `mixedTransition`. -/

/-- The paper's selector-summed gate: `Σ_j op_j · f(st_j)`, `op_j` the **base** selector column
`mopCol st_j`. -/
def selScale (f : MState → Expr) : MixedExpr F :=
  .Add (.Scale (bcur 0) (ofExpr (f .decompose)))
    (.Add (.Scale (bcur 1) (ofExpr (f .halt)))
      (.Add (.Scale (bcur 2) (ofExpr (f .read_root)))
        (.Scale (bcur 3) (ofExpr (f .verify_child)))))

/-- The paper's gate for quantity class `q` (`MemoryFactorizationScope.paddedBlock` order):
`Σ_j op_j · (block st_j).q`, base selectors, bodies transported along `memorySubst`. -/
def paperClassGate (q : ℕ) : MixedExpr F :=
  selScale (fun st => (@MemoryFactorizationScope.memQuantity K fieldK st q).subst memorySubst)

/-- The `tab:v_mem` classes other than the `cons` dyck row (`q = 1`), in quantity order. -/
def tabVMemClassIndices : List ℕ := [0, 2, 3, 4, 5, 6, 7, 10, 11, 12, 15, 16, 17, 18, 19, 20]

/-- The three classes the paper types in `𝔽`: `mem.axis` (`q = 21`),
`left_state = state` at `read_root` (`q = 25`, `:2068`) and at `verify_child` (`q = 26`, `:2076`). -/
def baseTypedClassIndices : List ℕ := [21, 25, 26]

/-- The four `x_out = ⊥` pins with no `tab:v_mem` row. -/
def bottomPinIndices : List ℕ := [8, 9, 13, 14]

def paperClassIndices : List ℕ :=
  tabVMemClassIndices ++ [22] ++ baseTypedClassIndices ++ bottomPinIndices

/-- The `cons` dyck row of `tab:v_mem` through `mconsDyckNoInv`
: no `z⁻¹` column. -/
def consDyckQuantity : MState → Expr
  | .decompose => .Sub (.Mul (chl 0) mPt.dyck)
      (MemoryFactorizationScope.mconsDyckNoInv mLc mRc)
  | .halt => @MemoryFactorizationScope.memQuantity K fieldK .halt 1
  | .read_root => @MemoryFactorizationScope.memQuantity K fieldK .read_root 1
  | .verify_child => @MemoryFactorizationScope.memQuantity K fieldK .verify_child 1

def paperConsDyck : MixedExpr F :=
  selScale (fun st => (consDyckQuantity (K := K) st).subst memorySubst)

def tabVMemGates : List (MixedExpr F) :=
  tabVMemClassIndices.map (paperClassGate (K := K)) ++ [paperConsDyck (K := K)]

def timestampGate : MixedExpr F := paperClassGate (K := K) 22

/-- **W4 stage 2.**  The internal `intermediate` LogUp pole at the sampled coins
: `interPole + RLC^γ(mem_record)` in `FiniteIO.compress`'s additive
convention, reading `γ` from slot `4` (shared with IO / `denominatorPinMixed`) and
the pole from slot `6` (`MemoryChallengeTuple.interPole`).  Until this retarget the
source was `poleExpr.subst memorySubst` (chal `1`/`2`, table `β = 0`). -/
def poleSource : Expr := .Add (.Var .challenge 6) recordRLCExpr

/-- **The 31st:** the `intermediate` pole over the ten-slot record, `poleSource + γ⁹ · reqIdx`
(`interPole + RLC^γ(mem_record)` with the exponent carrier). -/
def poleSourceMixed : MixedExpr F := .Add (ofExpr poleSource) reqIdxRLCTerm

/-- The `:2123` aggregator as one paper-form gate (`Algorithm:Memspec` sign, the paper/
`:2080`). -/
def paperAggregator : MixedExpr F :=
  .Sub (.Mul poleSourceMixed (.Sub (.Var .traceCur 28) (.Var .traceCur 27)))
    (.Sub (.Lift (bcur 2)) (.Lift (bcur 3)))

def rapMemGates : List (MixedExpr F) :=
  tabVMemGates (K := K) ++ [timestampGate (K := K), paperAggregator]

def baseTypedClassGates : List (MixedExpr F) :=
  baseTypedClassIndices.map (paperClassGate (K := K))

def bottomPins : List (MixedExpr F) :=
  bottomPinIndices.map (paperClassGate (K := K))

def intermediateChain : MixedExpr F := chainMixed


def hostedWalkInitGates : List (MixedExpr F) :=
  [Trans.walkLn1, Trans.walkCount1, Trans.walkAccInit].map
    (fun e => .Scale (bcur 4) (ofExpr (e.subst walkBoundarySubst)))


def hostedWalkStepGates : List (MixedExpr F) :=
  [Trans.walkLnStep, Trans.walkCountStep, Trans.walkAccStep].map
    (fun e => .Scale (.sub (.const 1) (bcur 5)) (ofExpr (e.subst walkSubst)))

/-- **H1.W memory: the walk boundary gates.**  `ln(1) = α`
through the walk line role (unchanged); then the count and accumulator boundary gates with
`cur(1) = RLC^γ(x^mem)`, `cc(1)` the one-hot child-payload sum and `cm(1) = α^{fanout}` IN THE
GATE (`MemoryWalkLabel`; the paper, `:1006`, `:2028-2031`). -/
def walkInitGates : List (MixedExpr F) :=
  [.Scale (bcur 4) (ofExpr (Trans.walkLn1.subst walkBoundarySubst)),
   MemoryWalkLabel.walkCount1InGate, MemoryWalkLabel.walkAccInitInGate]

/-- **H1.W memory: the walk transition gates**, `cur`/`cc`/`cm` of the successor row in-gate
(`MemoryWalkLabel.walkCountStepInGate` / `walkAccStepInGate`); the line recurrence unchanged. -/
def walkStepGates : List (MixedExpr F) :=
  [.Scale (.sub (.const 1) (bcur 5)) (ofExpr (Trans.walkLnStep.subst walkSubst)),
   MemoryWalkLabel.walkCountStepInGate, MemoryWalkLabel.walkAccStepInGate]

def walkTerminal : MixedExpr F := .Scale (bcur 5) (.Var .traceCur 33)

def walkGates : List (MixedExpr F) := walkInitGates ++ walkStepGates ++ [walkTerminal]


def hostedWalkGates : List (MixedExpr F) :=
  hostedWalkInitGates ++ hostedWalkStepGates ++ [walkTerminal]

def verBool : MixedExpr F :=
  .Mul (.Var .traceCur 39) (.Sub (.Var .traceCur 39) (.Const 1))

def safeNormalisation : MixedExpr F :=
  .Sub (.Var .traceCur 50)
    (.Add (.Mul (.Var .traceCur 39) (.Var .traceCur 37)) (.Sub (.Const 1) (.Var .traceCur 39)))

def safeInverse : MixedExpr F :=
  .Sub (.Mul (.Var .traceCur 50) (.Var .traceCur 38)) (.Const 1)

def contribution : MixedExpr F :=
  .Sub (.Var .traceCur 42) (.Mul (.Var .traceCur 39) (.Var .traceCur 38))

abbrev denominatorPin : MixedExpr F := denominatorPinMixed

/-- Single-column accumulator step on role `43`; role `44` unread. -/
def accStep : MixedExpr F :=
  .Scale (.sub (.const 1) (bcur 5))
    (.Sub (.Var .traceNext 43) (.Add (.Var .traceCur 43) (.Var .traceCur 42)))

def accInit : MixedExpr F := .Scale (bcur 4) (.Var .traceCur 43)

def accTerminal : MixedExpr F :=
  .Scale (bcur 5)
    (.Sub (.Add (.Var .traceCur 43) (.Var .traceCur 42)) (.Var .publicVal 2))

def terminalRole : MixedExpr F := .Sub (.Var .traceCur 40) (.Var .publicVal 2)

def ioCoreGates : List (MixedExpr F) :=
  [verBool, safeNormalisation, safeInverse, contribution, accStep, accInit, accTerminal,
    terminalRole, denominatorPin]

/-- `first · ipre` / `last · icur`, masked by the preprocessing columns. -/
def intermediateInit : MixedExpr F := .Scale (bcur 4) (.Var .traceCur 27)

def intermediateTerminal : MixedExpr F := .Scale (bcur 5) (.Var .traceCur 28)

/-- Physical base-field column of the forest root mask. This is coordinate `0` of unread
sampled-IO role `49`. Role `44` is `acc_after` (`accChainMixed`) and must not be reused. It is **not** a new
witness column (`w = 196` unmoved): the verifier pins it as the third preprocessing slot, the
forest generalisation of the first-row mask (`bcur 4`). -/
def rootMaskCol : ℕ := 153

/-- Physical dequeue mask: coord `1` of the same dead role `49` (`6+3·49+1 = 154`).
    `notLast · (1 − rootMask(next))`; fourth preprocessing slot.  Mirrored at
    K-role `56` (`dequeueMaskMixed`); source `174 → 177`, residual shrink
    yields disclosed `w 199 → 200`. -/
def dequeueMaskCol : ℕ := 154

/-- Preprocessing selector `rootMask`: one on memory walk rows `1..kMem`, zero after. -/
def rootMask : CoeffExpr F := bcur rootMaskCol

/-- Preprocessing dequeue mask, current row. -/
def dequeueMask : CoeffExpr F := bcur dequeueMaskCol

/-- `rootMask · pt.axis_counts = 0` (source role `4`).  Coin-free, degree 2. -/
def rootMaskCountsGate : MixedExpr F := .Scale rootMask (.Var .traceCur 4)

/-- `rootMask · pt.pw = 0` (source role `3`; the paper's `axis_indicator` slot
    now carries `pw`, form (b)). Coin-free, degree 2. -/
def rootMaskPwGate : MixedExpr F := .Scale rootMask (.Var .traceCur 3)

abbrev rootMaskIndicatorGate : MixedExpr F := rootMaskPwGate

theorem rootMaskCol_eq : rootMaskCol = 153 := rfl
theorem dequeueMaskCol_eq : dequeueMaskCol = 154 := rfl

theorem walk_gamma_slot_untouched : MemoryWalkLabel.walkGammaChallengeIndex = 7 := rfl

/-! ### The 29th: the pre-seed `atom` column and the `halt`-row atom gate

One `𝔽` column `atom`, committed in the memory chip's
single (round-0) commitment, before the seed `z` is used; on `halt` rows the `𝕂` leaf of
`pt.noun` (role `2`) equals the `algebraMap` image of `atom`. `size = z` and `dyck = 0` on
`halt` are already `eqBlk` and are not duplicated.

**Deviation (recorded, not a transcription):** the paper commits no atom before `z`
.  This moves the `:800` leaf
commitment before `z` on the memory chip only; the compute chip needs no atom column. -/

/-- Physical base-field column of the pre-seed atom: appended after the `6 + 3·58 = 180`
source layout (`CoordinateRAPTail.expandChipTail … 1`), so no extension role moves. -/
def atomCol : ℕ := 180

theorem atomCol_eq : atomCol = 180 := rfl

/-- The `halt` selector: base column `1` (`MState.toIdx .halt = 1`). -/
def haltSel : CoeffExpr F := bcur 1

/-- **The `halt`-row atom gate** (`𝕂`-valued, degree 2):
`sel_halt · (pt.noun.leaf − algebraMap atom) = 0`.  `pt.noun.leaf` is source role `2`
(`StrategyOfTraces.memoryPtNoun`).  Its three coordinate gates are
`sel_halt · (leaf_k − coord b 1 k · atom)`, `k = 0, 1, 2`; at a basis with `b 0 = 1`
(`compilerBasis_formR`) these are `sel_halt·(leaf₀ − atom)`, `sel_halt·leaf₁`, `sel_halt·leaf₂`
(`MemoryHaltAtomDecode.haltAtomGateCoord_formR`). -/
def haltAtomMixed : MixedExpr F :=
  .Scale haltSel (.Sub (.Var .traceCur 2) (.Lift (bcur atomCol)))

theorem haltAtomMixed_degree : (haltAtomMixed (F := F)).degree = 2 := rfl

/-- Semantics of the atom gate: it vanishes iff the row is not `halt` or its leaf is the lifted
atom. -/
theorem haltAtomMixed_eval (eK : Env K) (eF : Env F) :
    (haltAtomMixed (F := F)).eval eK eF =
      algebraMap F K (eF.trace 1) * (eK.trace 2 - algebraMap F K (eF.trace 180)) := by
  simp [haltAtomMixed, haltSel, atomCol, bcur, MixedExpr.eval, CoeffExpr.eval]

def paperEndpointGates : List (MixedExpr F) :=
  [intermediateInit, intermediateTerminal, rootMaskCountsGate, rootMaskIndicatorGate]


abbrev newGates : List (MixedExpr F) := paperEndpointGates

/-- State-Variables: four booleanities and the one-hot sum. -/
def paperBaseGates : List (CoeffExpr F) :=
  [bbool (bcur 0), bbool (bcur 1), bbool (bcur 2), bbool (bcur 3), bsum4 .traceCur]

def paperKGatesCore : List (MixedExpr F) :=
  rapMemGates (K := K) ++ baseTypedClassGates (K := K) ++ bottomPins (K := K)
    ++ [intermediateChain] ++ walkGates ++ ioCoreGates

/-- **The paper-shaped `𝕂` gate set committed by the memory chip since W2 stage 2.** -/
def paperKGates : List (MixedExpr F) :=
  paperKGatesCore (K := K) (F := F) ++ paperEndpointGates (F := F) ++
    MemoryWalkLabel.queueWitnessGates (F := F)

theorem paperBaseGates_length : (paperBaseGates (F := F)).length = 5 := rfl

theorem paperKGates_length : (paperKGates (K := K) (F := F)).length = 49 := rfl

omit [FiniteDimensional F K] in
theorem paperBaseGates_degree : ∀ g ∈ paperBaseGates (F := F), g.degree ≤ 2 := by
  intro g hg
  simp only [paperBaseGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;>
    simp [bbool, bcur, bsum4, CoeffExpr.degree]

omit [Field F] [FiniteDimensional F K] in
theorem selScale_degree_le (f : MState → Expr) (d : ℕ) (h : ∀ st, (f st).degree ≤ d) :
    (selScale (F := F) f).degree ≤ 1 + d := by
  have h0 := h .decompose
  have h1 := h .halt
  have h2 := h .read_root
  have h3 := h .verify_child
  simp only [selScale, MixedExpr.degree, MixedExpr.ofExpr_degree, bcur, CoeffExpr.degree]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem classBodies_degree :
    ∀ q ∈ paperClassIndices, ∀ st : MState,
      ((@MemoryFactorizationScope.memQuantity K fieldK st q).subst memorySubst).degree ≤ 3 := by
  intro q hq st
  simp only [paperClassIndices, tabVMemClassIndices, baseTypedClassIndices, bottomPinIndices,
    List.append_assoc, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false, or_assoc] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases st <;> degree_le

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem consBodies_degree :
    ∀ st : MState, ((consDyckQuantity (K := K) st).subst memorySubst).degree ≤ 3 := by
  intro st
  cases st <;> degree_le

omit [Field F] [FiniteDimensional F K] in
theorem paperClassGate_degree (q : ℕ) (hq : q ∈ paperClassIndices) :
    (paperClassGate (K := K) (F := F) q).degree ≤ 4 :=
  selScale_degree_le _ 3 (classBodies_degree q hq)

omit [Field F] [FiniteDimensional F K] in
theorem paperConsDyck_degree : (paperConsDyck (K := K) (F := F)).degree ≤ 4 :=
  selScale_degree_le _ 3 consBodies_degree

omit [Algebra F K] [FiniteDimensional F K] in
theorem mem_paperKGatesCore_iff (g : MixedExpr F) :
    g ∈ paperKGatesCore (K := K) (F := F) ↔
      (∃ q ∈ tabVMemClassIndices, paperClassGate (K := K) q = g) ∨
        g = paperConsDyck (K := K) ∨
      g = timestampGate (K := K) ∨ g = paperAggregator ∨
      (∃ q ∈ baseTypedClassIndices, paperClassGate (K := K) q = g) ∨
      (∃ q ∈ bottomPinIndices, paperClassGate (K := K) q = g) ∨
      g = intermediateChain ∨ g ∈ walkInitGates ∨ g ∈ walkStepGates ∨ g = walkTerminal ∨
      g ∈ ioCoreGates := by
  simp only [paperKGatesCore, rapMemGates, tabVMemGates, baseTypedClassGates, bottomPins,
    walkGates, List.mem_append, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc]

omit [FiniteDimensional F K] in
set_option maxRecDepth 100000 in
theorem paperKGates_degree : ∀ g ∈ paperKGates (K := K) (F := F), g.degree ≤ 4 := by
  intro g hg
  simp only [paperKGates, List.mem_append] at hg
  rcases hg with hfront | hqueue
  · rcases hfront with hcore | hend
    · rcases (mem_paperKGatesCore_iff g).1 hcore with ⟨q, hq, rfl⟩ | rfl | rfl | rfl | ⟨q, hq, rfl⟩
        | ⟨q, hq, rfl⟩ | rfl | hwalk | hwalk | rfl | hio
      · exact paperClassGate_degree q (by simp [paperClassIndices, hq])
      · exact paperConsDyck_degree
      · exact paperClassGate_degree 22 (by simp [paperClassIndices])
      · have h : (paperAggregator (F := F)).degree = 2 := rfl; omega
      · exact paperClassGate_degree q (by simp [paperClassIndices, hq])
      · exact paperClassGate_degree q (by simp [paperClassIndices, hq])
      · have h : (intermediateChain (F := F)).degree = 2 := rfl; omega
      · simp only [walkInitGates, List.mem_cons, List.not_mem_nil, or_false] at hwalk
        rcases hwalk with rfl | rfl | rfl
        · simp only [MixedExpr.degree, MixedExpr.ofExpr_degree, bcur, CoeffExpr.degree]; decide
        · exact MemoryWalkLabel.walkCount1InGate_degree
        · exact MemoryWalkLabel.walkAccInitInGate_degree
      · simp only [walkStepGates, List.mem_cons, List.not_mem_nil, or_false] at hwalk
        rcases hwalk with rfl | rfl | rfl
        · simp only [MixedExpr.degree, MixedExpr.ofExpr_degree, bcur, CoeffExpr.degree]; decide
        · exact MemoryWalkLabel.walkCountStepInGate_degree
        · exact MemoryWalkLabel.walkAccStepInGate_degree
      · have h : (walkTerminal (F := F)).degree = 2 := rfl; omega
      · simp only [ioCoreGates, List.mem_cons, List.not_mem_nil, or_false] at hio
        rcases hio with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · have h : (verBool (F := F)).degree = 2 := rfl; omega
        · have h : (safeNormalisation (F := F)).degree = 2 := rfl; omega
        · have h : (safeInverse (F := F)).degree = 2 := rfl; omega
        · have h : (contribution (F := F)).degree = 2 := rfl; omega
        · have h : (accStep (F := F)).degree = 2 := rfl; omega
        · have h : (accInit (F := F)).degree = 2 := rfl; omega
        · have h : (accTerminal (F := F)).degree = 2 := rfl; omega
        · have h : (terminalRole (F := F)).degree = 1 := rfl; omega
        · have h : (denominatorPin (F := F)).degree = 1 := rfl; omega
    · simp only [paperEndpointGates, List.mem_cons, List.not_mem_nil, or_false] at hend
      rcases hend with rfl | rfl | rfl | rfl
      · have h : (intermediateInit (F := F)).degree = 2 := rfl; omega
      · have h : (intermediateTerminal (F := F)).degree = 2 := rfl; omega
      · have h : (rootMaskCountsGate (F := F)).degree = 2 := rfl; omega
      · have h : (rootMaskIndicatorGate (F := F)).degree = 2 := rfl; omega
  · simp only [MemoryWalkLabel.queueWitnessGates, List.mem_cons, List.not_mem_nil,
      or_false] at hqueue
    rcases hqueue with rfl | rfl
    · exact MemoryWalkLabel.walkQueueNonEmpty_degree
    · exact MemoryWalkLabel.walkQueueTiling_degree

/-- The deployed memory chip's coordinate layout, `baseCols = 6`, `e = 3`. -/
def memoryCol0 : VarKind → ℕ → ℕ := fun _ idx => 6 + 3 * idx

/-- The three compiled coordinate gates of `haltAtomMixed` at the deployed layout. -/
def haltAtomGateCoord (b : Basis (Fin 3) F K) (k : Fin 3) : CoeffExpr F :=
  MixedCoordinateCompiler.mixedCompile b memoryCol0 haltAtomMixed k

/-- Pre-W2 mixed bucket plus the dequeue-mask pin (`dequeueMaskMixed`). -/
def foldedMixedTransitionGates : List (MixedExpr F) :=
  [firstMaskMixed, lastMaskMixed, chainMixed, accChainMixed, denominatorPinMixed,
    dequeueMaskMixed]

/-- **W2 stage 2.**  The committed mixed transition bucket is the paper-shaped `𝕂` set
(`paperKGates (K := K)`, 49 gates). -/
def mixedTransitionGates (_b : Basis (Fin 3) F K) : List (MixedExpr F) :=
  paperKGates (K := K) (F := F) ++ [haltAtomMixed]

open MixedCoordinateCompiler in
/-- The four gates that join the `𝕂`-valued equality-check bucket. -/
def mixedEqualityChecks (_b : Basis (Fin 3) F K) : List (MixedExpr F) :=
  List.ofFn (selectorMixed (F := F))

open MixedCoordinateCompiler in
theorem foldedMixedTransitionGates_length :
    (foldedMixedTransitionGates (F := F)).length = 6 := rfl

open MixedCoordinateCompiler in
theorem mixedTransitionGates_length (b : Basis (Fin 3) F K) :
    (mixedTransitionGates (F := F) (K := K) b).length = 50 := by
  simp [mixedTransitionGates, paperKGates_length]

open MixedCoordinateCompiler in
theorem mixedEqualityChecks_length (b : Basis (Fin 3) F K) :
    (mixedEqualityChecks (F := F) (K := K) b).length = 4 := by simp [mixedEqualityChecks]

theorem mixedTransitionGates_degree (b : Basis (Fin 3) F K) :
    ∀ g ∈ mixedTransitionGates (F := F) (K := K) b, g.degree ≤ 4 := by
  intro g hg
  simp only [mixedTransitionGates, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact paperKGates_degree g hg
  · rw [haltAtomMixed_degree]; omega

open MixedCoordinateCompiler in
theorem mixedEqualityChecks_degree (b : Basis (Fin 3) F K) :
    ∀ g ∈ mixedEqualityChecks (F := F) (K := K) b, g.degree ≤ 1 := by
  intro g hg
  obtain ⟨s, -, rfl⟩ := List.mem_ofFn.mp hg
  have h : (selectorMixed (F := F) s).degree = 1 := rfl
  omega

/-- Reserved independent scalar compression coins.  They lie below coordinate-expanded challenge
index `6`, so they do not alias any `K`-valued memory or forest challenge. -/
def selectorEqualityChallenge : CoeffExpr F := .var .challenge 0
def firstMaskBindingChallenge : CoeffExpr F := .var .challenge 1
def lastMaskBindingChallenge : CoeffExpr F := .var .challenge 2
def chainBindingChallenge : CoeffExpr F := .var .challenge 3

def maskBindingCoord (b : Basis (Fin 3) F K) (role base : ℕ) (k : Fin 3) : CoeffExpr F :=
  .sub (extCoord .traceCur role k)
    (.mul (.const (coord b (1 : K) k)) (bcur base))

def rlc3 (ρ : CoeffExpr F) (f : Fin 3 → CoeffExpr F) : CoeffExpr F :=
  CoeffExpr.sumList (List.finRange 3) fun k => .mul (.pow ρ k) (f k)

/-- New base ID `5`: all coordinates of extension first-mask role `47` bind to fixed base column 4. -/
def firstMaskBindingGate (b : Basis (Fin 3) F K) : CoeffExpr F :=
  rlc3 firstMaskBindingChallenge (maskBindingCoord b 47 4)

/-- New base ID `6`: all coordinates of extension last-mask role `48` bind to fixed base column 5. -/
def lastMaskBindingGate (b : Basis (Fin 3) F K) : CoeffExpr F :=
  rlc3 lastMaskBindingChallenge (maskBindingCoord b 48 5)

def chainCoord (k : Fin 3) : CoeffExpr F :=
  .mul (.sub (.const 1) (bcur 5))
    (.sub (extCoord .traceCur 28 k) (extCoord .traceNext 27 k))

/-- The `k`-th deployed coordinate body of the response-accumulator chain `accChainMixed`:
`(1 − last) · (acc_after_k(i) − acc_before_k(i+1))`, columns `138 + k` and next-row `135 + k`. -/
def accChainCoord (k : Fin 3) : CoeffExpr F :=
  .mul (.sub (.const 1) (bcur 5))
    (.sub (extCoord .traceCur 44 k) (extCoord .traceNext 43 k))

/-- New base ID `13`: scalar RLC of all three masked intermediate-chain coordinates. -/
def intermediateChainGate : CoeffExpr F :=
  rlc3 chainBindingChallenge (chainCoord (F := F))

/-- The nine post-selector semantic base bodies in IDs `5..13`. -/
def semanticBaseTail (_b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  (List.ofFn (sampledTerminalCoord (F := F))) ++
    (List.ofFn (sampledAccumulatorCoord (F := F)))

/-- Pre-W2 base transition list (eleven gates). -/
def foldedBaseTransitionGates (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  [bbool (F := F) (bcur (F := F) 0), bbool (F := F) (bcur (F := F) 1),
   bbool (F := F) (bcur (F := F) 2), bbool (F := F) (bcur (F := F) 3),
   bsum4 (F := F) .traceCur] ++ semanticBaseTail b

/-- Coin-free base gate: `read_root ⇒ ver = 1`.  Coordinate-0
expansion of `readRootSel · (1 − ver) = 0`; `ver` is K-role 39.  The F-constant
is `coord b 1 0` so the honest `ver = 1` vanishes against any basis. -/
def readRootVerGate (b : Basis (Fin 3) F K) : CoeffExpr F :=
  .mul (bcur 2) (.sub (.const (coord b (1 : K) (0 : Fin 3))) (extCoord .traceCur 39 0))

/-- **W2 stage 2 + H1.4 ver-gate (27th).**  The committed base transition bucket is
the paper's five State-Variables gates plus
`readRootVerGate`.  The six coordinate bodies of `semanticBaseTail` live in
`paperKGates (K := K)` as mixed gates (`terminalRole`, `accStep`). -/
def baseTransitionGates (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  paperBaseGates ++ [readRootVerGate b]

theorem foldedBaseTransitionGates_length (b : Basis (Fin 3) F K) :
    (foldedBaseTransitionGates b).length = 11 := by
  simp [foldedBaseTransitionGates, semanticBaseTail]

theorem readRootVerGate_degree (b : Basis (Fin 3) F K) :
    (readRootVerGate b).degree ≤ 2 := by
  simp [readRootVerGate, bcur, extCoord, CoeffExpr.degree]

theorem baseTransitionGates_length (b : Basis (Fin 3) F K) :
    (baseTransitionGates b).length = 6 := by
  simp [baseTransitionGates, paperBaseGates]

theorem paperBaseGates_eq_folded_prefix (b : Basis (Fin 3) F K) :
    paperBaseGates (F := F) = (foldedBaseTransitionGates b).take 5 := rfl

theorem firstMaskBindingGate_degree (b : Basis (Fin 3) F K) :
    (firstMaskBindingGate b).degree ≤ 2 := by
  unfold firstMaskBindingGate rlc3
  apply CoeffExpr.degree_sumList_le
  intro k hk
  simp [maskBindingCoord, firstMaskBindingChallenge, extCoord, bcur, CoeffExpr.degree]

theorem lastMaskBindingGate_degree (b : Basis (Fin 3) F K) :
    (lastMaskBindingGate b).degree ≤ 2 := by
  unfold lastMaskBindingGate rlc3
  apply CoeffExpr.degree_sumList_le
  intro k hk
  simp [maskBindingCoord, lastMaskBindingChallenge, extCoord, bcur, CoeffExpr.degree]

theorem intermediateChainGate_degree :
    (intermediateChainGate (F := F)).degree ≤ 2 := by
  unfold intermediateChainGate rlc3
  apply CoeffExpr.degree_sumList_le
  intro k hk
  simp [chainCoord, chainBindingChallenge, extCoord, bcur, CoeffExpr.degree]

theorem foldedBaseTransitionGates_degree (b : Basis (Fin 3) F K) :
    ∀ g ∈ foldedBaseTransitionGates b, g.degree ≤ 4 := by
  intro g hg
  rw [foldedBaseTransitionGates] at hg
  rcases List.mem_append.mp hg with hg | hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;>
      simp [bbool, bcur, bsum4, CoeffExpr.degree]
  · simp only [semanticBaseTail, List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨k, -, rfl⟩ := List.mem_ofFn.mp hg
      simp [sampledTerminalCoord, extCoord, CoeffExpr.degree]
    · obtain ⟨k, -, rfl⟩ := List.mem_ofFn.mp hg
      simp [sampledAccumulatorCoord, extCoord, CoeffExpr.degree]

theorem baseTransitionGates_degree (b : Basis (Fin 3) F K) :
    ∀ g ∈ baseTransitionGates b, g.degree ≤ 4 := by
  intro g hg
  simp only [baseTransitionGates, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hg
  rcases hg with hg | rfl
  · have := paperBaseGates_degree g hg
    omega
  · have := readRootVerGate_degree b
    omega

theorem foldedBaseTransitionGates_no_literal_zero [DecidableEq F]
    (b : Basis (Fin 3) F K) :
    ∀ g ∈ foldedBaseTransitionGates b, g ≠ .const 0 := by
  intro g hg
  rw [foldedBaseTransitionGates] at hg
  rcases List.mem_append.mp hg with hg | hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;>
      simp [bbool, bcur, bsum4]
  · simp only [semanticBaseTail, List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨k, -, rfl⟩ := List.mem_ofFn.mp hg
      fin_cases k <;> simp [sampledTerminalCoord, extCoord]
    · obtain ⟨k, -, rfl⟩ := List.mem_ofFn.mp hg
      fin_cases k <;> simp [sampledAccumulatorCoord, extCoord]

theorem baseTransitionGates_no_literal_zero [DecidableEq F]
    (b : Basis (Fin 3) F K) :
    ∀ g ∈ baseTransitionGates b, g ≠ .const 0 := by
  intro g hg
  simp only [baseTransitionGates, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hg
  rcases hg with hg | rfl
  · simp only [paperBaseGates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp [bbool, bcur, bsum4]
  · simp [readRootVerGate, bcur, extCoord]

/-- Distinct pivot-support fingerprints for the final eleven-list.  The selector sum uses
fingerprint `4`; the promoted mask and chain gates have left for the mixed `𝕂` bucket. -/
def baseGateSupportFingerprints : List ℕ :=
  [0, 1, 2, 3, 4, 141, 142, 143, 138, 139, 140]

theorem baseTransitionGates_no_support_alias :
    baseGateSupportFingerprints.Nodup := by decide

theorem foldedBaseTransitionGates_nodup [DecidableEq F] (b : Basis (Fin 3) F K) :
    (foldedBaseTransitionGates b).Nodup := by
  simp [foldedBaseTransitionGates, semanticBaseTail,
    sampledTerminalCoord, sampledAccumulatorCoord,
    extCoord, bbool, bcur, bsum4]

theorem baseTransitionGates_nodup [DecidableEq F] (b : Basis (Fin 3) F K) :
    (baseTransitionGates b).Nodup := by
  simp [baseTransitionGates, paperBaseGates, readRootVerGate, bbool, bcur, bsum4,
    extCoord]

/-- Exact collision exclusions for the three base scalar compressions. -/
def FirstMaskCollisionExcluded (b : Basis (Fin 3) F K) (env : Env F) : Prop :=
  (firstMaskBindingGate b).eval env = 0 →
    ∀ k : Fin 3, (maskBindingCoord b 47 4 k).eval env = 0

def LastMaskCollisionExcluded (b : Basis (Fin 3) F K) (env : Env F) : Prop :=
  (lastMaskBindingGate b).eval env = 0 →
    ∀ k : Fin 3, (maskBindingCoord b 48 5 k).eval env = 0

def ChainCollisionExcluded (env : Env F) : Prop :=
  intermediateChainGate.eval env = 0 →
    ∀ k : Fin 3, (chainCoord (F := F) k).eval env = 0

/-- The removed extension mask-boolean sources are derived, not omitted: exact mask binding plus
fixed-preprocessing booleanity transports booleanity through the algebra map. -/
theorem extension_mask_boolean_derived (x : F) (y : K)
    (hbind : y = algebraMap F K x) (hbool : x * (x - 1) = 0) :
    y * (y - 1) = 0 := by
  rw [hbind, ← map_one (algebraMap F K), ← map_sub, ← map_mul, hbool, map_zero]

theorem first_extension_mask_boolean_derived (x : F) (y : K)
    (hbind : y = algebraMap F K x) (hbool : x * (x - 1) = 0) :
    y * (y - 1) = 0 :=
  extension_mask_boolean_derived x y hbind hbool

theorem last_extension_mask_boolean_derived (x : F) (y : K)
    (hbind : y = algebraMap F K x) (hbool : x * (x - 1) = 0) :
    y * (y - 1) = 0 :=
  extension_mask_boolean_derived x y hbind hbool

/-! ### The `intermediate` aggregator's two endpoint gates

the paper: "a global terminal constraint check is required to ensure that the final value
of `intermediate` is zero, while its initial value is also constrained to be zero as part of the
memory table RAP"; priced at the paper as "`2·e` gates of degree `1`" under Initial &
Terminal Constraints.  The paper writes no gate for either (the appendix `:2118-2123` gives only
the step), so the tree transcribes the prose.

Nothing bound those columns
to `ipre`/`icur`: `Batch272.shiftedTrace_accepted` showed that for ANY
accepted trace and ANY `δ`, moving `ipre` and `icur` by the constant `δ` at every row was ACCEPTED
at the consumed `P.memoryChip`, so the telescoped `Σ Δ = icur(last) − ipre(0)` was bound to
nothing. The `LK`/`LM`/`LP` shape a fourth time.

**The repair (`LU` §4, user-authorized):** the gates are now the paper's `first · ipre` and
`last · icur` themselves, read through the extension mask mirrors `47`/`48` — which
`firstMaskMixed`/`lastMaskMixed` bind to the preprocessing masks (base columns `4`/`5`) at every
row — so by value they are `MemoryPaperFactorization.intermediateInit`/`intermediateTerminal`.
`RAP.Satisfies` (`Nock/Framework/Core.lean`) holds every constraint at EVERY row,
so an endpoint gate must carry its own mask: `first · ipre` vanishes trivially off row `0` and
reads `ipre(0)` at it.  That makes the gates degree `2`, so they cannot sit in the template's
degree-`1` bucket (`ChipTemplate.extDeg1_deg`); they sit in the degree-`≤ 3` bucket beside the
forest endpoints.  Gate count unchanged (`2·e` for `2·e`); `M.rap.s = 113` unmoved.  Roles `46`
and `49` are now unread (dead columns; W2 stage 2 retires them). -/

/-- `first · ipre`, as a `𝕂` gate over the mirrored
first-row mask (role `47` = base column `4` by `firstMaskMixed`) and `ipre` (role `27`). -/
def intermediateInitGate : Expr := .Mul (extVar .traceCur 47) (extVar .traceCur 27)

/-- `last · icur`, as a `𝕂` gate over the mirrored
last-row mask (role `48` = base column `5` by `lastMaskMixed`) and `icur` (role `28`). -/
def intermediateTerminalGate : Expr := .Mul (extVar .traceCur 48) (extVar .traceCur 28)

/-- The degree-`1` endpoint bucket is empty: W2 bills the paper's masked endpoints in
`mixedTransition` (`paperEndpointGates`).  Until W2 this was already `[]` since the `LU` repair
(the two product-column pins `[extVar 46, extVar 49]` left). -/
def degreeOneEndpoints : List Expr := []

/-- Pre-W2 degree-`≤ 3` endpoint list (four `Expr` gates using extension mask roles `47`/`48`).
W2 commits the same constraints as mixed `Scale` of the base
masks (`paperEndpointGates`). -/
def foldedDegreeThreeEndpoints : List Expr :=
  [extVar .traceCur 41,
   .Mul (extVar .traceCur 48) (extVar .traceCur 33),
   intermediateInitGate,
   intermediateTerminalGate]

/-- **W2 stage 2.**  Empty: walk initial/terminal and `intermediate` init/terminal live in
`paperKGates (K := K)` as mixed `Scale` gates. -/
def degreeThreeEndpoints : List Expr := []

theorem endpoint_lengths :
    degreeOneEndpoints.length = 0 ∧ degreeThreeEndpoints.length = 0 := by
  decide

theorem folded_endpoint_lengths :
    foldedDegreeThreeEndpoints.length = 4 := by decide

theorem endpoint_gates_nodup_nonzero :
    degreeOneEndpoints.Nodup ∧ degreeThreeEndpoints.Nodup ∧
    (∀ g ∈ degreeOneEndpoints, g ≠ (.Const 0 : Expr)) ∧
    (∀ g ∈ degreeThreeEndpoints, g ≠ (.Const 0 : Expr)) := by
  simp [degreeOneEndpoints, degreeThreeEndpoints]

theorem degreeOneEndpoints_degree :
    ∀ g ∈ degreeOneEndpoints, g.degree ≤ 1 := by decide

theorem degreeThreeEndpoints_degree :
    ∀ g ∈ degreeThreeEndpoints, g.degree ≤ 3 := by decide

/-- The two `intermediate` endpoint gates have degree exactly `2` — which is why they cannot be
in `degreeOneEndpoints`. -/
theorem intermediate_endpoint_gates_degree :
    intermediateInitGate.degree = 2 ∧ intermediateTerminalGate.degree = 2 := by decide


theorem intermediateInitGate_mem : intermediateInitGate ∈ foldedDegreeThreeEndpoints := by
  simp [foldedDegreeThreeEndpoints]

theorem intermediateTerminalGate_mem : intermediateTerminalGate ∈ foldedDegreeThreeEndpoints := by
  simp [foldedDegreeThreeEndpoints]

def selectorEquality (b : Basis (Fin 3) F K) (s : Fin 4) : CoeffExpr F :=
  CoeffExpr.sumList (List.finRange 3) fun k =>
    .mul (.pow selectorEqualityChallenge k)
      (CoeffExpr.sub
        (.var .traceCur (6 + 3 * (51 + s) + k))
        (.mul (.const (coord b (1 : K) ⟨k, by omega⟩)) (.var .traceCur s)))

/-- Pre-W2 equality checks: twelve coordinates of the four selector-mirror mixed gates.
The paper's selectors are the base columns themselves, so the mirrors and these checks are tree-only. -/
def foldedEqualityChecks (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  MixedCoordinateCompiler.mixedExpandList b memoryCol0 (mixedEqualityChecks b)

/-- **W2 stage 2.**  Empty: the paper has no selector-mirror equality checks. -/
def equalityChecks (_b : Basis (Fin 3) F K) : List (CoeffExpr F) := []

def SelectorEqualityCollisionExcluded (b : Basis (Fin 3) F K) (env : Env F) : Prop :=
  ∀ s : Fin 4, (selectorEquality b s).eval env = 0 →
    ∀ k : Fin 3,
      (CoeffExpr.sub
        (CoeffExpr.var .traceCur (6 + 3 * (51 + s) + k))
        (CoeffExpr.mul (CoeffExpr.const (coord b (1 : K) ⟨k, by omega⟩))
          (CoeffExpr.var .traceCur s))).eval env = 0

theorem foldedEqualityChecks_length (b : Basis (Fin 3) F K) :
    (foldedEqualityChecks b).length = 12 := by
  rw [foldedEqualityChecks, MixedCoordinateCompiler.length_mixedExpandList,
    mixedEqualityChecks_length]

theorem equalityChecks_length (b : Basis (Fin 3) F K) :
    (equalityChecks b).length = 0 := rfl

/-- Membership in the pre-W2 equality bucket. -/
theorem mem_foldedEqualityChecks (b : Basis (Fin 3) F K) (u : CoeffExpr F) :
    u ∈ foldedEqualityChecks b ↔
      ∃ (s : Fin 4) (k : Fin 3),
        u = MixedCoordinateCompiler.mixedCompile b memoryCol0 (selectorMixed (F := F) s) k := by
  rw [foldedEqualityChecks, MixedCoordinateCompiler.mem_mixedExpandList]
  constructor
  · rintro ⟨g, hg, k, rfl⟩
    obtain ⟨s, -, rfl⟩ := List.mem_ofFn.mp hg
    exact ⟨s, k, rfl⟩
  · rintro ⟨s, k, rfl⟩
    exact ⟨selectorMixed s, List.mem_ofFn.mpr ⟨s, rfl⟩, k, rfl⟩

/-- Pre-W2 membership; unstatable of the committed (empty) list. -/
theorem mem_equalityChecks (b : Basis (Fin 3) F K) (u : CoeffExpr F) :
    u ∈ equalityChecks b ↔ False := by
  simp [equalityChecks]

theorem foldedEqualityChecks_no_literal_zero (b : Basis (Fin 3) F K) :
    ∀ g ∈ foldedEqualityChecks b, g ≠ (.const 0 : CoeffExpr F) := by
  intro g hg
  obtain ⟨s, k, rfl⟩ := (mem_foldedEqualityChecks b g).mp hg
  simp [selectorMixed, MixedCoordinateCompiler.mixedCompile]

theorem equalityChecks_no_literal_zero (b : Basis (Fin 3) F K) :
    ∀ g ∈ equalityChecks b, g ≠ (.const 0 : CoeffExpr F) := by
  intro g hg
  simp [equalityChecks] at hg

def coeffVariableSupport : CoeffExpr F → Finset (VarKind × ℕ)
  | .const _ => ∅
  | .var k i => {(k, i)}
  | .add x y | .sub x y | .mul x y => coeffVariableSupport x ∪ coeffVariableSupport y
  | .neg x | .pow x _ => coeffVariableSupport x

/-- The pivot column of a committed selector-mirror coordinate: the extension slot it binds.
The twelve are `159 … 170`, pairwise distinct, which is what makes the retyped equality bucket
alias-free without any coin. -/
def equalityCheckPivot : CoeffExpr F → ℕ
  | .sub (.var _ i) _ => i
  | _ => 0

theorem foldedEqualityCheckPivots (b : Basis (Fin 3) F K) :
    (foldedEqualityChecks b).map equalityCheckPivot
      = [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170] := by
  simp [foldedEqualityChecks, mixedEqualityChecks, memoryCol0, selectorMixed, bcur,
    MixedCoordinateCompiler.mixedExpandList, MixedCoordinateCompiler.mixedCoordVec,
    MixedCoordinateCompiler.mixedCompile, equalityCheckPivot, List.finRange,
    List.ofFn_succ]

theorem equalityCheckPivots (b : Basis (Fin 3) F K) :
    (equalityChecks b).map equalityCheckPivot = [] := rfl

theorem foldedEqualityChecks_nodup (b : Basis (Fin 3) F K) :
    (foldedEqualityChecks b).Nodup := by
  refine List.Nodup.of_map equalityCheckPivot ?_
  rw [foldedEqualityCheckPivots b]
  decide

theorem equalityChecks_nodup (b : Basis (Fin 3) F K) :
    (equalityChecks b).Nodup := by
  simp [equalityChecks]

theorem foldedEqualityChecks_degree (b : Basis (Fin 3) F K) :
    ∀ g ∈ foldedEqualityChecks b, g.degree ≤ 1 := by
  rw [foldedEqualityChecks]
  exact MixedCoordinateCompiler.degree_mixedExpandList_le b memoryCol0 _ 1
    (mixedEqualityChecks_degree b)

theorem equalityChecks_degree (b : Basis (Fin 3) F K) :
    ∀ g ∈ equalityChecks b, g.degree ≤ 1 := by
  intro g hg
  simp [equalityChecks] at hg

/-- Source `6/55`, one-round optimized memory chip.
**W2 stage 2:** commits `paperBaseGates` (base) and `paperKGates (K := K)` (mixed); no fold, no
equality checks, no `Expr` endpoint buckets (masked endpoints sit in the mixed list). -/
def memorySourceTemplate (b : Basis (Fin 3) F K) : ChipTemplate F where
  rounds := 1
  rounds_pos := by omega
  baseColsOf := fun _ => 6
  extColsOf := fun _ => 58
  baseTransition := baseTransitionGates b
  extTransition := []
  mixedTransition := mixedTransitionGates b
  extDeg1 := degreeOneEndpoints
  extDeg3 := degreeThreeEndpoints
  equalityChecks := equalityChecks b
  baseTransition_deg := baseTransitionGates_degree b
  extTransition_deg := by intro g hg; cases hg
  mixedTransition_deg := mixedTransitionGates_degree b
  extDeg1_deg := degreeOneEndpoints_degree
  extDeg3_deg := degreeThreeEndpoints_degree
  equalityChecks_deg := equalityChecks_degree b

/-- The `𝕂`-valued mixed transition bucket of the deployed memory chip
(`MixedCoordinateCompiler`).  Stated separately from `memorySourceTemplate_shape` so that the
existing seven-component projection chain is unaffected. -/
theorem memorySourceTemplate_mixedTransition (b : Basis (Fin 3) F K) :
    (memorySourceTemplate b).mixedTransition = mixedTransitionGates b := rfl

theorem memorySourceTemplate_mixed_shape (b : Basis (Fin 3) F K) :
    (memorySourceTemplate b).mixedTransition.length = 50 :=
  mixedTransitionGates_length b

/-- The deployed layout really is `memoryCol0`. -/
theorem memorySourceTemplate_col0 (b : Basis (Fin 3) F K) :
    (memorySourceTemplate b).col0 3 = memoryCol0 := rfl

theorem memorySourceTemplate_shape (b : Basis (Fin 3) F K) :
    (memorySourceTemplate b).baseCols = 6 ∧
      (memorySourceTemplate b).extCols = 58 ∧
      (memorySourceTemplate b).baseTransition.length = 6 ∧
      (memorySourceTemplate b).extTransition.length = 0 ∧
      (memorySourceTemplate b).extDeg1.length = 0 ∧
      (memorySourceTemplate b).extDeg3.length = 0 ∧
      (memorySourceTemplate b).equalityChecks.length = 0 := by
  simp [memorySourceTemplate, ChipTemplate.baseCols, ChipTemplate.extCols,
    baseTransitionGates_length b, endpoint_lengths, equalityChecks_length] <;> first | rfl | decide

end
end OptimizedMemoryGateBasis
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.source_to_fold_complete
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.fold_to_source_of_collision_excluded
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.source_partition_exact
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.source_partition_overlap_free
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.extensionTransitionGates_nodup
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.baseTransitionGates_nodup
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.extension_mask_boolean_derived
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.memorySourceTemplate_shape
