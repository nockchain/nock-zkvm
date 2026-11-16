import Nock.AIR
import Nock.NockVMROM.Thm54.RAPPadding
import Nock.NockVMROM.Thm54.PaperResourceCounts

/-!
# Scoping probes: the paper's own memory-gate factorization

**Status: §3 is shipped; §1, §2, §4, §5 are scoping only.**  `OptimizedMemoryGateBasis.lean` now imports this file
(`:4`) and builds the shipped row-local source list
`OptimizedMemoryGateBasis.memoryRowSources` (`:140`) out of §3's `mergedGate` (`:270`), so §3's
objects are production.  What is still a scoping probe is the paper arithmetic (§1, §2), the
typing split (§4) and the underdetermination receipts (§5).

`Nock/AIR.lean` `memEqBlkExprs` now carries the form R `pw`/`counts` identities (`λ^{n−1}` at
Goldilocks `n = 64`); `MergedSourceBridge.merged_sources_recover_memoryAIR` must stay in lockstep.

## The question

`Thm:mem_38` prices `RAP_mem` at `20·e + 13` degree-`4` transition gates,
and `Thm:NockVMROM` prices the whole memory chip at `24·e + 16`.  The candidate under
scope is that the paper's `20` is the count of **selector-summed** gates — one gate per
*quantity*, `Σ_st op_st · (LHS − RHS_st)` — where this tree carries one gate per
*(state, equation)* pair, `op_st · (LHS − RHS_st)`.

## What this file establishes

1. §1 — the paper's `24·e+16` decomposition, re-derived from the paper 
   `:655`, `:656`, and its `𝕂`/`𝔽` split `24 = 20+2+1+1`, `16 = 13+2+1`.
2. §2 — `tab:v_mem` has exactly **17** `𝕂`-valued components, so the
   paper's `20` is `17 + 3` and the identity of the three is underdetermined (§5).
3. §3 — the **merge**: this tree's `69` per-state gated equations
   (`Nock.Reified.memPerStateGated`) are the *same* `27` quantities repeated across states, and
   the selector-summed form is **equivalent** to the per-state form at any one-hot selector
   (`mergedMemCore_iff_perStateGated`, `:366`), at unchanged degree `≤ 4`.  That equivalence
   *assumes* the one-hot rather than deriving it; the derivation from the five retained
   State-Variables sources, together with the characteristic condition it needs, is
   `MergedSourceBridge.lean`.
4. §4 — the typing split of the `27`: `24` are `𝕂`-valued and `3` are `𝔽`-valued, and exactly `17` of the `24` have a `tab:v_mem` row.
5. §5 — the underdetermination receipts: three distinct decompositions of the paper's base `13`,
   and the equality-check accounting `1 + 2 = 3 ≠ 4`.
6. §6 — the cost ledger of adopting the merge.
-/

namespace Nock.NockVMROM.Thm54
namespace MemoryFactorizationScope

open Nock
open Nock.Reified
open Nock.MemoryTable

/-! ## §1  The paper's `24·e + 16`, re-derived

Five cited quantities, no slack:

| object | transition gates | line |
|---|---|---|
| `RAP_mem` (`Thm:mem_38`) | `20·e + 13` | the paper |
| walk gadget, degree `1` | `2 + 2·e` | the paper |
| walk gadget, degree `3` | `e` | the paper |
| `RAP_mem-IO`, degree `1` | `1` | the paper |
| `RAP_mem-IO`, degree `3` | `e` | the paper |
-/

/-- `Thm:mem_38`, the paper. -/
def papRAPmemGates (e : ℕ) : ℕ := 20 * e + 13

/-- `Thm:Walk_IOP` transition constraints, degree `1`. -/
def papWalkDegOne (e : ℕ) : ℕ := 2 + 2 * e

/-- `Thm:Walk_IOP` transition constraints, degree `3`. -/
def papWalkDegThree (e : ℕ) : ℕ := e

/-- `Thm:IO_result`, `RAP_mem-IO` additional transition, degree `1`. -/
def papMemIODegOne : ℕ := 1

/-- `Thm:IO_result`, `RAP_mem-IO` additional transition, degree `3`. -/
def papMemIODegThree (e : ℕ) : ℕ := e

/-- **The paper's memory transition budget decomposes with zero slack.**  the paper. -/
theorem paper_memory_transition_decomposes (e : ℕ) :
    papRAPmemGates e + papWalkDegOne e + papWalkDegThree e
        + papMemIODegOne + papMemIODegThree e
      = Thm54Resources.memoryTransitionGatesPaper e := by
  simp [papRAPmemGates, papWalkDegOne, papWalkDegThree, papMemIODegOne, papMemIODegThree,
    Thm54Resources.memoryTransitionGatesPaper]
  omega

/-! ### The `𝕂` / `𝔽` split

A `𝕂`-valued gate is committed by its `e` base-field coordinates, so in `a·e + b` the coefficient
`a` counts `𝕂`-valued gates and `b` counts `𝔽`-valued ones. -/

/-- `𝕂`-valued gates the paper's memory chip carries: `20 + 2 + 1 + 1`. -/
def papMemoryKGates : ℕ := 20 + 2 + 1 + 1

/-- `𝔽`-valued gates the paper's memory chip carries: `13 + 2 + 1`. -/
def papMemoryFGates : ℕ := 13 + 2 + 1

theorem paper_memory_typing_split :
    papMemoryKGates = 24 ∧ papMemoryFGates = 16 ∧
      ∀ e, papMemoryKGates * e + papMemoryFGates = Thm54Resources.memoryTransitionGatesPaper e := by
  refine ⟨rfl, rfl, fun e => ?_⟩
  simp [papMemoryKGates, papMemoryFGates, Thm54Resources.memoryTransitionGatesPaper]

/-! ## §2  `tab:v_mem` has seventeen `𝕂` components

the paper.  Rows and their `𝕂`-component counts, all cited at source:
`pt.noun` `:2142` (3), `pt.indicator` `:2144` (1), `pt.counts` `:2152` (1), `lc.noun` `:2160` (3),
`rc.noun` `:2162` (3), `mem.root` `:2164` (3), `mem.child` `:2166` (3).
`⊥` cells contribute no gate, only a missing summand. -/

/-- One entry per `tab:v_mem` row: its number of `𝕂` components. -/
def tabVMemRowComponents : List ℕ := [3, 1, 1, 3, 3, 3, 3]

theorem tabVMem_row_count : tabVMemRowComponents.length = 7 := by decide

/-- **Seventeen.**  The selector-summed gate count of `tab:v_mem` alone. -/
theorem tabVMem_components : tabVMemRowComponents.sum = 17 := by decide

/-- The paper's `20` needs exactly three gates beyond `tab:v_mem`. -/
theorem paper_twenty_is_seventeen_plus_three :
    tabVMemRowComponents.sum + 3 = 20 := by decide

/-! ## §3  The merge

`Nock.Reified.memPerStateGated` is `Σ_st |block st|` gates `op_st · e`.  Grouping them by the
*quantity* they constrain gives `27` classes; the merged gate for class `q` is
`Σ_st op_st · (block st).q`, with `.Const 0` where the state imposes nothing.

The four padded blocks below are literal re-orderings of `memEqBlkExprs st ++ memInterExprs st`
(`Nock/AIR.lean:1530`, `:1560`) into the fixed quantity order

```
0 pt.size      1 pt.dyck     2 pt.leaf     3 pt.indicator  4 pt.counts
5 lc.size      6 lc.dyck     7 lc.leaf     8 lc.indicator  9 lc.counts
10 rc.size    11 rc.dyck    12 rc.leaf    13 rc.indicator 14 rc.counts
15 mem.root.size 16 .dyck   17 .leaf      18 mem.child.size 19 .dyck  20 .leaf
21 mem.axis   22 mem.timestamp            23 intermediate Δ
24 pole·g − 1 25 left_state@read_root     26 left_state@verify_child
```
-/

variable {K : Type*} [Field K]

/-- Source challenge 8 is memory slot 8. -/
def lamE : Expr := .Var .challenge 8
/-- Form R scale exponent `n − 1` for `n := Nat.size p`. -/
def pwScaleExp (n : ℕ) : ℕ := n - 1
theorem pwScaleExp_goldilocks : pwScaleExp 64 = 63 := rfl
/-- `λ^{n−1}` at `n = Nat.size (ringChar K)`. -/
noncomputable def lamScaleE : Expr := .Pow lamE (MemoryTable.pwScaleExp K)
/-- Extra record coordinate `C'` (deployed 𝕂-role `57`). -/
def recC' : Expr := tc 35

/-- Replaces `:2059-2060`.  Fourteen live entries. -/
def blockDecompose : List Expr :=
  [ .Sub mPt.size (mconsExpr mLc mRc).size
  , .Sub mPt.dyck (mconsExpr mLc mRc).dyck
  , .Sub mPt.leaf (mconsExpr mLc mRc).leaf
  , .Sub (tc 7) (.Mul lamE (.Add (tc 12) (tc 17)))
  , .Sub (tc 8) (.Add (.Add (.Add (tc 13) (tc 18))
      (.Mul (.Sub lamE (.Const 1)) (.Add (tc 12) (tc 17)))) (tc 17))
  , .Const 0, .Const 0, .Const 0, .Const 0, .Const 0
  , .Const 0, .Const 0, .Const 0, .Const 0, .Const 0
  , mMem.root.size, mMem.root.dyck, mMem.root.leaf
  , mMem.child.size, mMem.child.dyck, mMem.child.leaf
  , mMem.axis, mMem.ts
  , .Sub (tc 32) (tc 31)
  , .Const 0, .Const 0, .Const 0 ]

/-- `halt`: the paper / `tab:v_mem` col 3.  Twenty-three live entries. -/
def blockHalt : List Expr :=
  [ .Sub mPt.size (chl 0)
  , mPt.dyck
  , .Const 0
  , tc 7
  , tc 8
  , mLc.size, mLc.dyck, mLc.leaf, tc 12, tc 13
  , mRc.size, mRc.dyck, mRc.leaf, tc 17, tc 18
  , mMem.root.size, mMem.root.dyck, mMem.root.leaf
  , mMem.child.size, mMem.child.dyck, mMem.child.leaf
  , mMem.axis, mMem.ts
  , .Sub (tc 32) (tc 31)
  , .Const 0, .Const 0, .Const 0 ]

/-- `read_root`: the paper / `tab:v_mem` col 4.  Sixteen live entries. -/
noncomputable def blockReadRoot : List Expr :=
  [ .Sub mPt.size mLc.size
  , .Sub mPt.dyck mLc.dyck
  , .Sub mPt.leaf mLc.leaf
  , .Sub (tc 7) (.Sub (tc 12) (.Mul (.Mul (lamScaleE (K := K)) (tc 29)) (tc 30)))
  , .Sub (tc 8) (.Sub (tc 13) (.Mul (.Mul (tc 29) recC') (tc 30)))
  , .Const 0, .Const 0, .Const 0, .Const 0, .Const 0
  , mRc.size, mRc.dyck, mRc.leaf, tc 17, tc 18
  , .Sub mMem.root.size mPt.size, .Sub mMem.root.dyck mPt.dyck, .Sub mMem.root.leaf mPt.leaf
  , .Const 0, .Const 0, .Const 0
  , .Const 0, .Const 0
  , .Sub (.Sub (tc 32) (tc 31)) (tc 33)
  , .Sub (.Mul poleExpr (tc 33)) (.Const 1)
  , .Sub (tc 21) (.Const 1)
  , .Const 0 ]

/-- `verify_child`: the paper / `tab:v_mem` col 5.  Sixteen live entries. -/
noncomputable def blockVerifyChild : List Expr :=
  [ .Sub mPt.size mLc.size
  , .Sub mPt.dyck mLc.dyck
  , .Sub mPt.leaf mLc.leaf
  , .Sub (tc 7) (.Add (tc 12) (.Mul (lamScaleE (K := K)) (tc 30)))
  , .Sub (tc 8) (.Add (tc 13) (.Mul (lamScaleE (K := K)) (tc 30)))
  , .Const 0, .Const 0, .Const 0, .Const 0, .Const 0
  , mRc.size, mRc.dyck, mRc.leaf, tc 17, tc 18
  , .Const 0, .Const 0, .Const 0
  , .Sub mMem.child.size mPt.size, .Sub mMem.child.dyck mPt.dyck, .Sub mMem.child.leaf mPt.leaf
  , .Const 0, .Const 0
  , .Add (.Sub (tc 32) (tc 31)) (tc 33)
  , .Sub (.Mul poleExpr (tc 33)) (.Const 1)
  , .Const 0
  , .Sub (tc 22) (.Const 1) ]

/-- The padded quantity block of a state. -/
noncomputable def paddedBlock : MState → List Expr
  | .decompose => blockDecompose
  | .halt => blockHalt
  | .read_root => blockReadRoot (K := K)
  | .verify_child => blockVerifyChild (K := K)

/-- **Twenty-seven quantity classes.**  Every state's block has exactly this length. -/
theorem paddedBlock_length (st : MState) : (paddedBlock (K := K) st).length = 27 := by
  cases st <;> rfl

/-- Quantity `q` of state `st`, `.Const 0` when the state imposes nothing on it. -/
noncomputable def memQuantity (st : MState) (q : ℕ) : Expr :=
  (paddedBlock (K := K) st).getD q (.Const 0)

/-! ### The padded block is the tree's own block, reordered -/

/-! Syntactic equality of `Expr` is decidable; deriving the instance here lets the two coverage
facts below be checked by the kernel rather than argued by hand.  (The same instance is derived in
`OptimizedComputeSubstitution.lean:19`, which this module does not import.) -/

deriving instance DecidableEq for Nock.Reified.Expr

open Lean Meta Elab Tactic in
/-- `DecidableEq Expr` cannot reduce `Nat.size (ringChar K)`, so coverage is a
definitional walk instead of `decide`. -/
partial def proveInList (mvar : MVarId) : MetaM Unit := do
  let s ← saveState
  let headed ← try
    let r ← mvar.apply (← mkConstWithFreshMVarLevels ``List.Mem.head)
    pure r.isEmpty
  catch _ =>
    restoreState s
    pure false
  if headed then return
  restoreState s
  let r ← mvar.apply (← mkConstWithFreshMVarLevels ``List.Mem.tail)
  if h : r.length = 1 then
    proveInList r[0]
  else
    throwError "mem walk failed"

open Lean Meta Elab Tactic in
partial def proveGoal (mvar : MVarId) : MetaM Unit := do
  let ty ← whnf (← mvar.getType)
  if ty.isAppOf ``Or then
    let s ← saveState
    let inlOk ← try
      let gs ← mvar.apply (← mkConstWithFreshMVarLevels ``Or.inl)
      if h : gs.length = 1 then
        gs[0].refl
        pure true
      else pure false
    catch _ =>
      restoreState s
      pure false
    if inlOk then return
    restoreState s
    let gs ← mvar.apply (← mkConstWithFreshMVarLevels ``Or.inr)
    if h : gs.length = 1 then
      proveInList gs[0]
    else
      throwError "or walk failed"
  else
    proveInList mvar

open Lean Meta Elab Tactic in
def memField? (sg : CasesSubgoal) : MetaM (Option FVarId) := sg.mvarId.withContext do
  let mut next : Option FVarId := none
  for f in sg.fields do
    let ty ← whnf (← inferType f)
    if ty.isAppOf ``List.Mem then
      next := some f.fvarId!
  return next

open Lean Meta Elab Tactic in
partial def consumeMem (g : MVarId) (he : FVarId) : TacticM Unit := g.withContext do
  let sgs ← g.cases he
  match sgs.toList with
  | [] => return ()
  | [sg] =>
    match ← memField? sg with
    | some he' => consumeMem sg.mvarId he'
    | none => proveGoal sg.mvarId
  | [head, tail] =>
    proveGoal head.mvarId
    match ← memField? tail with
    | some he' => consumeMem tail.mvarId he'
    | none => throwError "tail without mem hyp"
  | _ => throwError s!"unexpected {sgs.size}"

open Lean Meta Elab Tactic in
elab "subset_by_defeq" : tactic => do
  evalTactic (← `(tactic| dsimp only [paddedBlock, blockDecompose, blockHalt, blockReadRoot,
    blockVerifyChild, memEqBlkExprs, memInterExprs, fpEqC, fpZeroC, memZeroC, lamE, lamScaleE,
    recC'] at *))
  let g ← getMainGoal
  let (_, g) ← g.intro `e
  let (he, g) ← g.intro `he
  consumeMem g he

/-- Every gate of the tree's per-state block is one of the padded quantities. -/
theorem block_subset_paddedBlock (st : MState) :
    ∀ e ∈ memEqBlkExprs (K := K) st ++ memInterExprs st, e ∈ paddedBlock (K := K) st := by
  cases st <;> subset_by_defeq

/-- Every padded quantity is either vacuous or one of the tree's own per-state gates. -/
theorem paddedBlock_subset_block (st : MState) :
    ∀ e ∈ paddedBlock (K := K) st,
      e = (.Const 0 : Expr) ∨ e ∈ memEqBlkExprs (K := K) st ++ memInterExprs st := by
  cases st <;> subset_by_defeq

variable {K : Type*} [Field K]

/-- **The reordering is semantically faithful**: the padded block vanishes exactly when the
tree's own per-state block does. -/
theorem paddedBlock_eval_iff (st : MState) (env : Env K) :
    (∀ e ∈ paddedBlock (K := K) st, e.eval env = 0)
      ↔ (∀ e ∈ memEqBlkExprs (K := K) st ++ memInterExprs st, e.eval env = 0) := by
  constructor
  · intro h e he; exact h e (block_subset_paddedBlock (K := K) st e he)
  · intro h e he
    rcases paddedBlock_subset_block st e he with rfl | hmem
    · simp [Expr.eval]
    · exact h e hmem

/-! ### The selector-summed gates -/

/-- The merged gate for quantity `q`: `Σ_st op_st · (block st).q`.  This is the paper's
factorization shape — one gate per row of `tab:v_mem`, summed over the state one-hot. -/
noncomputable def mergedGate (q : ℕ) : Expr :=
  .Add (gateByM .decompose (memQuantity (K := K) .decompose q))
    (.Add (gateByM .halt (memQuantity (K := K) .halt q))
      (.Add (gateByM .read_root (memQuantity (K := K) .read_root q))
        (gateByM .verify_child (memQuantity (K := K) .verify_child q))))

/-- The candidate factorized memory core: twenty-seven selector-summed gates. -/
noncomputable def mergedMemCore : List Expr := (List.range 27).map (mergedGate (K := K))

theorem mergedMemCore_length : (mergedMemCore (K := K)).length = 27 := by
  simp [mergedMemCore]

open Lean Meta Elab Tactic in
elab "degree_le_4" : tactic => do
  let g ← getMainGoal
  let ty ← whnf (← instantiateMVars (← g.getType))
  let some fn := ty.getAppFn.constName?
    | throwError m!"degree goal head is not a constant: {ty}"
  let lhs ←
    if fn == ``Nat.le then pure (ty.getArg! 0)
    else if fn == ``LE.le then pure (ty.getArg! 2)
    else throwError m!"degree goal is {fn}"
  let lhs ← reduce lhs (skipProofs := false)
  let n ← match lhs with
    | .lit (.natVal n) => pure n
    | _ =>
      match lhs.nat? with
      | some n => pure n
      | none => throwError m!"degree did not reduce: {lhs}"
  if n ≤ 4 then
    let lit := Syntax.mkNumLit s!"{n}"
    let pf ← elabTerm (← `(term| (by decide : $lit ≤ 4))) (← g.getType)
    g.assign pf
  else
    throwError s!"degree {n} exceeds 4"

/-- **The merge does not raise the constraint degree.**  Still `≤ 4`. -/
theorem mergedMemCore_degree : ∀ g ∈ mergedMemCore (K := K), g.degree ≤ 4 := by
  intro g hg
  simp only [mergedMemCore, List.mem_map, List.mem_range] at hg
  obtain ⟨q, hq, rfl⟩ := hg
  interval_cases q <;> degree_le_4

/-- Every state contributes at least one gate of degree exactly `4`: the `cons` dyck row is the tight one, as it is today. -/
theorem mergedGate_one_is_degree_four : (mergedGate (K := K) 1).degree = 4 := by
  rfl

/-! ### The one-hot hypothesis, stated on an arbitrary environment -/

/-- The four state-selector columns read as the one-hot encoding of `st`.  This is exactly what `memSvExprs` forces
(`MemoryTable.oneHot_of_bool_sum`, `Nock/MemoryTable.lean:400`). -/
def SelectorOneHot (env : Env K) (st : MState) : Prop :=
  ∀ j : MState, (tc (mopCol j)).eval env = if j = st then 1 else 0

theorem selectorOneHot_memoryEnvFull
    (minp : MemoryTable.Inputs K) (mrow : MemoryTable.Pub K) (mg : K) (st : MState) :
    SelectorOneHot (memoryEnvFull minp (MemoryTable.opSel st) mrow mg) st := by
  intro j
  cases j <;> simp [mopCol, MemoryTable.opSel, Expr.eval, tc, memoryEnvFull]

/-- **The selector-summed gate evaluates to the active state's equation.** -/
theorem mergedGate_eval (env : Env K) (st : MState) (hone : SelectorOneHot env st) (q : ℕ) :
    (mergedGate (K := K) q).eval env = (memQuantity (K := K) st q).eval env := by
  have h0 := hone .decompose
  have h1 := hone .halt
  have h2 := hone .read_root
  have h3 := hone .verify_child
  cases st <;>
    simp_all [mergedGate, gateByM, Expr.eval]

/-! ### The gating collapse, generalized off `memoryEnvFull`

`Nock.Reified.mem_gated_forall` (`Nock/AIR.lean:1716`) states this at `memoryEnvFull`; the same
argument works at any one-hot environment, which is what a general statement needs. -/

theorem memPerStateGated_iff_block (env : Env K) (st : MState) (hone : SelectorOneHot env st) :
    (∀ e ∈ memPerStateGated (K := K), e.eval env = 0)
      ↔ (∀ e ∈ memEqBlkExprs (K := K) st ++ memInterExprs st, e.eval env = 0) := by
  have hself : (tc (mopCol st)).eval env = 1 := by simp [hone st]
  constructor
  · intro h e he
    have hmem : gateByM st e ∈ memPerStateGated (K := K) := by
      unfold memPerStateGated
      exact List.mem_flatMap.mpr ⟨st, mem_allMStates st, List.mem_map.mpr ⟨e, he, rfl⟩⟩
    have h2 := h _ hmem
    simp only [gateByM, Expr.eval, hself, one_mul] at h2
    exact h2
  · intro h e he
    unfold memPerStateGated at he
    obtain ⟨k, -, hke⟩ := List.mem_flatMap.mp he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hke
    by_cases hk : k = st
    · subst hk
      simp only [gateByM, Expr.eval, hself, one_mul]
      exact h e' he'
    · have : (tc (mopCol k)).eval env = 0 := by simp [hone k, hk]
      simp [gateByM, Expr.eval, this]

/-! ### The equivalence -/

theorem mergedMemCore_iff_paddedBlock (env : Env K) (st : MState) (hone : SelectorOneHot env st) :
    (∀ g ∈ mergedMemCore (K := K), g.eval env = 0)
      ↔ (∀ e ∈ paddedBlock (K := K) st, e.eval env = 0) := by
  constructor
  · intro h e he
    obtain ⟨q, hqlt, rfl⟩ := List.getElem_of_mem he
    have hlt : q < 27 := by rw [paddedBlock_length] at hqlt; exact hqlt
    have hg : mergedGate (K := K) q ∈ mergedMemCore (K := K) :=
      List.mem_map.mpr ⟨q, List.mem_range.mpr hlt, rfl⟩
    have hz := h _ hg
    rwa [mergedGate_eval env st hone, memQuantity,
      List.getD_eq_getElem _ _ hqlt] at hz
  · intro h g hg
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
    rw [mergedGate_eval env st hone]
    have hlt : q < (paddedBlock (K := K) st).length := by
      rw [paddedBlock_length]; exact List.mem_range.mp hq
    rw [memQuantity, List.getD_eq_getElem _ _ hlt]
    exact h _ (List.getElem_mem hlt)

/-- **The main probe.**  The twenty-seven selector-summed gates and this tree's per-state gated
equations cut out exactly the same set at every one-hot selector.  Adopting the paper's
factorization for the memory core is therefore a *regrouping*, not a change of language. -/
theorem mergedMemCore_iff_perStateGated
    (env : Env K) (st : MState) (hone : SelectorOneHot env st) :
    (∀ g ∈ mergedMemCore (K := K), g.eval env = 0)
      ↔ (∀ e ∈ memPerStateGated (K := K), e.eval env = 0) :=
  (mergedMemCore_iff_paddedBlock env st hone).trans
    ((paddedBlock_eval_iff st env).trans (memPerStateGated_iff_block env st hone).symm)

/-- The same statement at the tree's own decoded memory environment. -/
theorem mergedMemCore_iff_perStateGated_memoryEnv
    (minp : MemoryTable.Inputs K) (mrow : MemoryTable.Pub K) (mg : K) (st : MState) :
    (∀ g ∈ mergedMemCore (K := K),
        g.eval (memoryEnvFull minp (MemoryTable.opSel st) mrow mg) = 0)
      ↔ (∀ e ∈ memPerStateGated (K := K),
        e.eval (memoryEnvFull minp (MemoryTable.opSel st) mrow mg) = 0) :=
  mergedMemCore_iff_perStateGated _ st (selectorOneHot_memoryEnvFull minp mrow mg st)

/-! ### The compression ratio -/

/-- The tree's per-state gate count, state by state
(`Nock/AIR.lean:1530-1573`): `14 + 23 + 16 + 16`. -/
def perStateBlockSizes : List ℕ := [14, 23, 16, 16]

theorem perStateGated_count : perStateBlockSizes.sum = 69 := by decide

/-- `memoryAIR` (`Nock/AIR.lean:1748`) is `5` state-variable gates, the `z·zinv = 1` witness, and
the `69` gated per-state equations. -/
theorem memoryAIR_gate_arithmetic : 5 + 1 + perStateBlockSizes.sum = 75 := by decide

/-- Merging replaces the `69` by `27`, taking the row-local memory AIR from `75` to `33`. -/
theorem merge_ratio : perStateBlockSizes.sum - 27 = 42 ∧ 5 + 1 + 27 = 33 := by decide

/-! ### The `z⁻¹` witness is not one of the twenty

It is not forced, and taking it would
break the degree bound the same paragraph asserts.

`Lem:NPR_decomp` is `Φ(n)_3 = Φ(n_L)_3 + X^{2(λ_L−1)} + X^{2λ_L−1}·Φ(n_R)_3`,
and `Φ_1 = Φ(n_L)_1 · Φ(n_R)_1` (`:1221`) makes the size fingerprint `X^λ`, so
`X^{2(λ_L−1)} = lc.size²·X⁻²` and `X^{2λ_L−1} = lc.size²·X⁻¹`.  This tree clears **one** power of
`X` (`mconsExpr`, `Nock/AIR.lean:1480-1484`) and pays for the remaining `X⁻¹` with witness column
`34` plus the gate `zZinvExprM` (`:1496`).  Clearing **two** removes the inverse entirely at the
same degree, which is what the paper's "only three gates" (`:1226`) budgets. -/

/-- `Lem:NPR_decomp`'s third identity cleared of `X⁻¹`: multiply by `X²`.
`X` is the challenge `z`, so it contributes degree `0`; no witness column is read. -/
def mconsDyckNoInv (a b : FPExpr) : Expr :=
  .Add (.Add (.Mul (.Pow (chl 0) 2) a.dyck) (.Mul a.size a.size))
       (.Mul (.Mul (.Mul (chl 0) a.size) a.size) b.dyck)

/-- **Same degree, no inverse witness.**  Both forms of the `cons` third identity are degree `3`
before the state selector, hence degree `4` after it — the tight cell of the paper. -/
theorem mconsDyck_degrees :
    (mconsExpr mLc mRc).dyck.degree = 3 ∧ (mconsDyckNoInv mLc mRc).degree = 3 ∧
      (gateByM MState.decompose (.Sub (.Mul (chl 0) mPt.dyck)
        (mconsDyckNoInv mLc mRc))).degree = 4 := by
  refine ⟨by decide, by decide, by decide⟩

/-- The inverse-free form reads no trace column above `18`; in particular it never reads the
`zinv` column `34`. -/
theorem mconsDyckNoInv_reads_no_zinv (env : Env K) (c : K) :
    (mconsDyckNoInv mLc mRc).eval
        { env with trace := fun i => if i = 34 then c else env.trace i }
      = (mconsDyckNoInv mLc mRc).eval env := by
  simp [mconsDyckNoInv, mLc, mRc, fpCol, tc, chl, Expr.eval]

/-- **The two forms agree.**  At any environment where the `zinv` column really is `z⁻¹`, the
inverse-free body is the tree's body scaled by `z`. -/
theorem mconsDyckNoInv_eq_scaled (env : Env K)
    (hzinv : (chl 0).eval env * (tc 34).eval env = 1) :
    (mconsDyckNoInv mLc mRc).eval env
      = (chl 0).eval env * (mconsExpr mLc mRc).dyck.eval env := by
  simp only [mconsDyckNoInv, mconsExpr, mLc, mRc, fpCol, tc, chl, Expr.eval] at hzinv ⊢
  linear_combination (-(env.trace 9 ^ 2)) * hzinv

/-- **Same zero set at `z ≠ 0`.**  So dropping column `34` and the gate `z·zinv = 1` changes
nothing about the language the `cons` row recognizes. -/
theorem cons_dyck_gate_equiv (env : Env K)
    (hz : (chl 0).eval env ≠ 0)
    (hzinv : (chl 0).eval env * (tc 34).eval env = 1) :
    ((Expr.Sub (.Mul (chl 0) mPt.dyck) (mconsDyckNoInv mLc mRc)).eval env = 0)
      ↔ ((Expr.Sub mPt.dyck (mconsExpr mLc mRc).dyck).eval env = 0) := by
  have h := mconsDyckNoInv_eq_scaled env hzinv
  simp only [Expr.eval, h, sub_eq_zero]
  constructor
  · intro hh; exact mul_left_cancel₀ hz hh
  · intro hh; rw [hh]

/-! ## §4  The typing split of the twenty-seven

the paper types `mem_record ∈ (𝕂³)² × 𝔽 × 𝕂` — so `mem.axis` is the *only* base-field
component of the record and `timestamp` is `𝕂`-valued.  the paper types the state selectors
`𝔽⁴`, so the two `left_state = state` quantities are base-valued too. -/

/-- Base-field quantity classes: `mem.axis` (`21`), `left_state@read_root` (`25`),
`left_state@verify_child` (`26`).  Everything else is `𝕂`-valued. -/
def baseQuantityClasses : List ℕ := [21, 25, 26]

/-- Quantity classes carried by a `tab:v_mem` row. -/
def tabVMemBackedClasses : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 15, 16, 17, 18, 19, 20]

/-- Quantity classes with **no** `tab:v_mem` row: the four `x_out = ⊥` pins of
`Algorithm:Memspec`, the `timestamp = 0` half of
`mem_record = (0,0,0,0)` (`:2057`, `:2062`), the aggregator (`:2123`), and the tree-only
LogUp inverse witness. -/
def algorithmOnlyKClasses : List ℕ := [8, 9, 13, 14, 22, 23, 24]

theorem quantity_partition :
    baseQuantityClasses.length = 3 ∧
      tabVMemBackedClasses.length = 17 ∧
      algorithmOnlyKClasses.length = 7 ∧
      baseQuantityClasses.length + tabVMemBackedClasses.length
        + algorithmOnlyKClasses.length = 27 := by
  decide

theorem quantity_partition_disjoint :
    (baseQuantityClasses ++ tabVMemBackedClasses ++ algorithmOnlyKClasses).Nodup ∧
      ∀ q < 27,
        q ∈ baseQuantityClasses ∨ q ∈ tabVMemBackedClasses ∨ q ∈ algorithmOnlyKClasses := by
  refine ⟨by decide, ?_⟩
  decide

/-- **The tree's merged core carries `24` `𝕂` gates where the paper prices `20`.**  The gap is
exactly four, and it is exactly the four `x_out = ⊥` pins that `tab:v_mem` has no row for. -/
theorem merged_K_count_versus_paper :
    tabVMemBackedClasses.length + algorithmOnlyKClasses.length = 24 ∧
      24 - 20 = 4 ∧
      ([8, 9, 13, 14] : List ℕ).length = 4 ∧
      ∀ q ∈ ([8, 9, 13, 14] : List ℕ), q ∈ algorithmOnlyKClasses := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **The paper's `20` is reachable, and only along the `tab:v_mem` reading.**  Dropping the four
`⊥` pins from the merged core leaves `17 + 3 = 20`: the table's seventeen, `timestamp = 0`, the aggregator identity (`:2123`), and one further gate. -/
theorem twenty_from_table_reading :
    tabVMemBackedClasses.length + ([22, 23] : List ℕ).length + 1 = 20 := by decide

/-! ## §5  What is *not* determined

Two receipts that the reconstruction cannot be pushed further from the text. -/

/-- **The base `13` is underdetermined.**  At least three structurally different readings of
`Thm:mem_38`'s base coefficient sum to `13`, and `App:Memconstraints` itemizes none of them:

* `A` — four selector booleanities (`:2130`) + one-hot (`:2131`) + `left_state` as `𝔽⁴`
  (`:2068`, `:2076`) + `right_state` as `𝔽⁴` (`:2064`, `:2071`, `:2079`);
* `B` — the same five, plus `left_state`/`right_state` as single field elements, plus
  `axis = 0` (`:2057`, `:2062`), plus a child-state one-hot block;
* `C` — the five, plus `axis = 0`, plus two `left_state` clause gates, plus a child booleanity
  block.

Nothing in the text selects among them; the tree exhibits none of them (it spends `8`). -/
def base13ReadingA : List ℕ := [4, 1, 4, 4]
def base13ReadingB : List ℕ := [4, 1, 1, 1, 1, 4, 1]
def base13ReadingC : List ℕ := [4, 1, 1, 2, 5]

theorem base_thirteen_underdetermined :
    base13ReadingA.sum = 13 ∧ base13ReadingB.sum = 13 ∧ base13ReadingC.sum = 13 ∧
      base13ReadingA ≠ base13ReadingB ∧ base13ReadingA ≠ base13ReadingC ∧
      base13ReadingB ≠ base13ReadingC := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The tree's base-valued share of the merged core plus the state-variable block: `3 + 5 = 8`,
five short of the paper's `13`.  The five missing are the child-state one-hot gates the tree
does not spend (`Nock/AIR.lean:1383-1387` reads only `tc 21`, `tc 22`). -/
theorem tree_base_share : baseQuantityClasses.length + 5 = 8 ∧ 13 - 8 = 5 := by decide

/-- **The paper's own equality-check accounting does not close.**  Under the same decomposition
that makes `24·e + 16` exact, the initial/terminal *equality checks* sum to
`1` `+ 2` `= 3`, while the paper
states four.  `Thm:mem_38` (`:1434`) lists no initial/terminal constraints for `RAP_mem` at all.
The compute chip's analogous sum *does* close: `1` (`:990`) `+ 1` (`:666`) `= 2` (`:1469`).

The `3 ≠ 4`
discrepancy above is untouched — it is about the paper's internal sum.

**Compute, after the de-compression.**  `computeEqualityChecks` is now `22`:
`11 + 11`, the two eleven-term `challenge36` column-pin families written out
(`OptimizedComputeFinal.finalEndpointEqualityChecks`).  The compute pins have no counterpart
on the paper's side of that unit at all: they are first/last-row column-vs-public pins, not
terminal output equalities. -/
theorem equality_check_accounting :
    1 + 2 = 3 ∧ 3 ≠ 4 ∧
      Thm54Resources.memoryEqualityChecks Thm54Resources.deployedExtensionDegree = 0 ∧
      11 + 11 = Thm54Resources.computeEqualityChecks Thm54Resources.deployedExtensionDegree := by
  refine ⟨rfl, by decide, rfl, rfl⟩

/-- The degree-`1` and degree-`3` endpoint budgets close **on the paper's side**: walk `2·e`
degree-`1` matches `:1487`, and walk `e` (`:989`) plus `RAP_mem-IO` `e`
(`:670`) matches `:1488`. -/
theorem endpoint_accounting (e : ℕ) :
    2 * e = Thm54Resources.memoryDegreeOneGatesPaper e ∧
      e + e = Thm54Resources.memoryDegreeThreeGatesPaper e ∧
      Thm54Resources.memoryDegreeOneGates e = 0 ∧
      Thm54Resources.memoryDegreeThreeGates e = 0 := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  simp [Thm54Resources.memoryDegreeThreeGatesPaper]
  omega

/-! ## §6  Cost ledger of adopting the merge -/

/-- Before the `𝔽 → 𝕂` retyping: `memorySourceTemplate` carried `14` base and `21` extension
transition gates, i.e. `21·e + 14` (`RAPPadding.memoryCoreTransitionGates`), and
`RAPPadding.residualTransitionGates` appended `3·e + 2` gates that compose to zero
(`RAPPadding.padMemoryCore_residual_compose_zero`). -/
theorem today_needs_padding (e : ℕ) :
    RAPPadding.memoryCoreTransitionGates e + RAPPadding.residualTransitionGates e
        = Thm54Resources.memoryTransitionGatesPaper e ∧
      RAPPadding.residualTransitionGates 3 = 11 := by
  refine ⟨?_, by decide⟩
  simpa [Thm54Resources.memoryTransitionGatesPaper] using RAPPadding.memory_transition_arithmetic e

/-- After the merge the *target* core is `24·e + 16` and the residual is zero — the padding
disappears rather than being re-justified. -/
def mergedCoreTransitionGates (e : ℕ) : ℕ := 24 * e + 16

theorem merged_core_needs_no_padding (e : ℕ) :
    mergedCoreTransitionGates e + 0 = Thm54Resources.memoryTransitionGatesPaper e := by
  simp [mergedCoreTransitionGates, Thm54Resources.memoryTransitionGatesPaper]

/-- **The paper-facing resource conjuncts do not move — under the Option-B merge.**  `RAP.s` and
the column width are functions of the *totals*, and the merge changes only how the transition
total is composed.  Scope: this is about the merge only. -/
theorem capstone_numerals_unmoved :
    RAPPadding.memoryFinalTotalConstraints 3 = 104 ∧
      Thm54Resources.memoryColumns 3 = 205 ∧
      Thm54Resources.memoryTransitionGatesPaper 3 = 88 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The merge alone does not empty the fold.**  `extensionFoldSources` has `82` entries
(`OptimizedMemoryGateBasis.lean:240`): `1` `z·zinv` witness `+ 69` gated per-state equations
`+ 3` walk-boundary `+ 3` walk-transition `+ 6` sampled.

1. drop the `z·zinv` witness (`−1`; available at no cost — see `cons_dyck_gate_equiv`);
2. move the three base-typed quantity classes to the base list;
3. drop the four `⊥` pins with no `tab:v_mem` row;
4. move the three walk-boundary sources to the endpoint buckets;
5. collapse the six sampled sources to the one degree-`3` gate the paper prices (`−5`; also
   a weakening). -/
def foldSourcesToday : ℕ := 1 + 69 + 3 + 3 + 6
def foldSourcesAfterMerge : ℕ := 1 + 27 + 3 + 3 + 6

theorem fold_shrinks_but_does_not_vanish :
    foldSourcesToday = 82 ∧ foldSourcesAfterMerge = 40 ∧ 24 < foldSourcesAfterMerge ∧
      foldSourcesAfterMerge - 1 - 3 - 4 - 3 - 5 = 24 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem paper_extension_list_closes : 20 + 2 + 1 + 1 = 24 := by decide

/-! ### Soundness

`optimizedProductionFailureProbabilityBound` (`OptimizedStrictPackage.lean:691-695`) is

```
(p8Work + 494·N + 1 + 61·M)/|𝕂| + ioWork/|𝕂|² + (20 + 14·M)/|𝔽|
```

The `61·M` summand is the fold-coin term:
`OptimizedMemoryCollisionAccounting.extensionFoldBadChallenges_card_le_61` (`:110-112`) bounds one
row's bad fold challenges by `61`, and `:228` sums it over `M` rows.  A factorization with one
semantic gate per bucket has **no** fold challenge and hence no such event, so the whole `61·M/|𝕂|`
summand is deleted rather than reduced.  The `14·M/|𝔽|` summand belongs to the four base-field
compression coins, which the merge does not touch. -/

/-- The fold's share of the row bound: `19` buckets of four sources (degree-`3` families, three
roots each) and `2` of three (degree-`2`, two roots each). -/
theorem fold_bad_challenge_arithmetic :
    82 = 21 * 3 + 19 ∧ 19 * 3 + 2 * 2 = 61 := by
  refine ⟨by decide, by decide⟩

/-- Removing the fold coin deletes a whole summand of the production bound; removing the four
base-field compressions would delete the `14·M/|𝔽|` one, which is the worse-denominated of the
two (`ChallengeInventory.cardF_lt_cardK`). -/
theorem soundness_delta (p8Work N M : ℕ) :
    (p8Work + 494 * N + 1 + 61 * M : ℚ) - (p8Work + 494 * N + 1 : ℚ) = 61 * M ∧
      (20 + 14 * M : ℚ) - 20 = 14 * M := by
  refine ⟨by ring, by ring⟩

end MemoryFactorizationScope
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.MemoryFactorizationScope.paper_memory_transition_decomposes
#print axioms Nock.NockVMROM.Thm54.MemoryFactorizationScope.tabVMem_components
#print axioms Nock.NockVMROM.Thm54.MemoryFactorizationScope.mergedMemCore_iff_perStateGated
#print axioms Nock.NockVMROM.Thm54.MemoryFactorizationScope.mergedMemCore_iff_perStateGated_memoryEnv
#print axioms Nock.NockVMROM.Thm54.MemoryFactorizationScope.mergedMemCore_degree
#print axioms Nock.NockVMROM.Thm54.MemoryFactorizationScope.mconsDyck_degrees
#print axioms Nock.NockVMROM.Thm54.MemoryFactorizationScope.cons_dyck_gate_equiv
#print axioms Nock.NockVMROM.Thm54.MemoryFactorizationScope.quantity_partition
#print axioms Nock.NockVMROM.Thm54.MemoryFactorizationScope.merged_K_count_versus_paper
#print axioms Nock.NockVMROM.Thm54.MemoryFactorizationScope.twenty_from_table_reading
#print axioms Nock.NockVMROM.Thm54.MemoryFactorizationScope.base_thirteen_underdetermined
#print axioms Nock.NockVMROM.Thm54.MemoryFactorizationScope.equality_check_accounting
#print axioms Nock.NockVMROM.Thm54.MemoryFactorizationScope.today_needs_padding
#print axioms Nock.NockVMROM.Thm54.MemoryFactorizationScope.fold_shrinks_but_does_not_vanish
#print axioms Nock.NockVMROM.Thm54.MemoryFactorizationScope.soundness_delta
