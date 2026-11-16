/-
  Nock/NockVMROM/Thm54/MemoryPaperFactorization.lean

  **W2 stage 1 — the paper-shaped `𝕂` gate set for the memory chip, over the DEPLOYED layout.**

  Every gate below reads the deployed `6/55` source layout
  (`171` columns, extension role `r` at columns `6 + 3·r .. 8 + 3·r`, `OptimizedMemoryGateBasis.
  memoryCol0`), with the memory-table payload at extension roles `0..30` (`memorySubst`: table
  column `4 + r ↦ role r`; the state selectors `tc 0..3` ↦ mirror roles `51..54`), the forest walk
  at roles `31..36`, the sampled IO at roles `37..50` and the
  record fields at roles `19..26` in `NockVM.encRec` order (`root.size, root.dyck, root.leaf,
  child.size, child.dyck, child.leaf, axis, ts`).

  ## What is built

  * `tabVMemGates` — the seventeen `tab:v_mem` classes, one selector-summed
    `𝕂` gate per (row × NPR component), with the paper's **base-field** selectors `op_j ∈ 𝔽⁴`
 — `MixedExpr.Scale (bcur j)` — where the deployed `mergedGate` reads the
    extension mirrors `51..54`.  The `cons` dyck row goes through
    `MemoryFactorizationScope.mconsDyckNoInv`: no `z⁻¹` witness column.
  * `timestampGate` — `timestamp = 0` at `decompose`/`halt`.
  * `paperAggregator` — the `:2123` aggregator as ONE ungated paper-form gate
    `(RLC^γ(mem_record) − β)·(intermediate(i) − intermediate(i−1)) = op_read − op_verify`.  The sign
    is `Algorithm:Memspec`'s, which the
    tree follows; `:2123` writes `op_3 − op_2`, the opposite sign — recorded, not resolved.
  * `baseTypedClassGates` — the three classes the paper types in `𝔽` (`mem.axis`, the paper;
    `left_state = state` at `:2068`/`:2076` with `op_j ∈ 𝔽⁴` at `:2129`).  **Not matchable 1-1 over
    the deployed layout as base gates**: the deployed layout commits `axis` and the child-state
    selectors as `𝕂` roles `25`, `17`, `18` (three columns each), so a single base gate per class
    needs base columns the layout does not have.  They are committed here as mixed gates (`e`
    coordinates each) and counted separately; the single-base-gate form is a layout change (`w`
    moves) deferred to stage 2 and recorded as the one item stage 1 could not match.
  * `bottomPins` — the four `⊥` pins `lc.indicator`, `lc.counts` at `halt` and `rc.indicator`,
    `rc.counts` at `halt`/`read_root`/`verify_child` (`Algorithm:Memspec` the paper,
    `:2071`, `:2079`).  **No `tab:v_mem` row** — kept as a separate named block, as decided.
  * `intermediateChain` — `chainMixed` kept verbatim.
  * `walkGates` — the forest walk's initial, transition
    (`:981`, `:983`) and terminal (`:857`, `:963`) constraints, masked by the **preprocessing**
    masks (base columns `4`/`5`) instead of the tree's extension mask roles `47`/`48`.
  Role
    `44` (the deployed `acc_after`) becomes unread.
  * `denominatorPin` — `role 37 = pole + Σ_{c<8} γ^c · role(19 + c)`, the paper's
    `RLC^α(x_mem(i,·)) − β` with `γ` in memory `𝕂` challenge slot `4` and
    `pole` in slot `5`. **A-mem-2 made this the committed gate
    `OptimizedMemoryGateBasis.denominatorPinMixed`** (fifth member of `mixedTransitionGates`),
    pinned the two slots to the sampled coins (`OptimizedProductionAcceptanceAt.memory_sampled_coins`,
    `BuildableChips.memoryChallengeTargets | 4 | 5`, `ExactMemoryCoordinatePins.sampledGamma`/
    `sampledPole`) and moved the digest. `denominatorPin` is now an `abbrev` of the committed gate
    and lives in `ioCoreGates`; the deployed set **implies** it (`deployed_implies_denominatorPin`,
    where stage 1 had `deployed_does_not_imply_denominatorPin`).
  * `newGates` — the two `intermediate` endpoint gates, **implied by the deployed set since the
    `LU` repair** — previously the two gates the deployed set did not imply
    (§6; three before A-mem-2):
    - `intermediateInit = first · ipre`, `intermediateTerminal = last · icur`
      (the paper: "a global terminal constraint … the final value of `intermediate` is
      zero, while its initial value is also constrained to be zero"). It now commits
      `OptimizedMemoryGateBasis.intermediateInitGate = role 47 · role 27` and
      `intermediateTerminalGate = role 48 · role 28` in `degreeThreeEndpoints`, which under the
      mask bindings ARE these two gates by value (`deployed_implies_intermediateInit/Terminal`). The list is kept under its name so the exactness statements keep their shape.
  * `paperBaseGates` — the State-Variables block, five base gates, identical
    to the deployed `baseTransitionGates b` prefix.

  ## Exactness (§4)

  `DeployedRow b envF` is the right-hand side of
  `OptimizedMemoryCanonicalSatisfaction.sourceMemoryRAP_satisfies_iff_language` at one row (11 base
  / 12 equality / 25 `𝕂` / 5 mixed since A-mem-2; the `𝕂` endpoint buckets are `0 + 4` since the
  `LU` repair).  `PaperRowCore b envF` is the paper set minus `newGates`; `PaperRow` is the full set.

  * `deployed_to_paper` — `DeployedRow` ⇒ `PaperRowCore`, under `FoldCollisionExcluded` (the
    deployed folds are involved) and an explicit base one-hot.
  * `deployed_to_paperRow` — `DeployedRow` ⇒ `PaperRow` (the FULL set), same hypotheses, since the
    `LU` repair.
  * `paper_to_deployed` — `PaperRow` ⇒ `DeployedRow` (`PaperRowCore` until the repair), under the base one-hot, the tree-only
    bindings (`TreeOnlyBindings`: the twelve selector-mirror checks and the two mask bindings, which
    bind columns the paper set never reads), booleanity of the two preprocessing masks, the honest
    values of the columns the paper set leaves unread (`DeadWitnessesHonest`: `zinv`, the LogUp
    witness `g`, `acc_after`, and the `0`-pinned product column `41`; `46`/`49` left it with the
    `LU` repair — nothing reads them now), and
    `pole ≠ 0` at the row (the one-gate aggregator gives `pole·Δ = 0` at `decompose`/`halt`; with
    the tree's internal `β = 0` that is `0 = 0` — this is where W4's sampled pole bites).
  * `deployed_iff_paper` — the two together: `DeployedRow ↔ TreeOnlyBindings ∧ PaperRow`.

  ## Counts (§5), degree (§7), canonical satisfaction (§8)

  See the docstrings of `paper_gate_counts` and `count_comparison`.  Every gate has degree `≤ 4`
  (`paperKGates_degree`).  The honest canonical memory trace satisfies every gate
  (`canonical_paperRow`); the denominator pin under the honest values of the two coin slots
  (`HonestSampledCoinSlots`, now supplied by `ExactMemoryCoordinatePins` through
  `HonestSampledCoinSlots.ofPins`).
-/

import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.MemoryWalkLabelCanonical
import Lean

namespace Nock.NockVMROM.Thm54
namespace MemoryPaperFactorization

open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Nock.MemoryTable (MState)
open StrictExtension
open Module
open CoordinateBasis
open CoordinateCompiler
open MonolithicRAP
open MixedCoordinateCompiler
open MixedCoordinateCompiler.MixedExpr (ofExpr)
open OptimizedMemoryGateBasis
open MemoryFactorizationScope

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## §1  The paper's selector-summed shape with base-field selectors

`Σ_j op_j · body_j` with `op_j ∈ 𝔽⁴` read from the deployed base columns `0..3`.
The deployed `MemoryFactorizationScope.mergedGate` reads the extension mirrors `51..54` instead
(`OptimizedMemoryGateBasis.memorySubst`), and binds them to the base columns through the twelve
`equalityChecks`; the paper has one selector, so the mirrors and their checks are tree-only. -/

/-- The paper's selector-summed gate: `Σ_j op_j · f(st_j)`, `op_j` the **base** selector column
`mopCol st_j`. -/
def selScale (f : MState → Expr) : MixedExpr F :=
  .Add (.Scale (bcur 0) (ofExpr (f .decompose)))
    (.Add (.Scale (bcur 1) (ofExpr (f .halt)))
      (.Add (.Scale (bcur 2) (ofExpr (f .read_root)))
        (.Scale (bcur 3) (ofExpr (f .verify_child)))))

/-- The base selector columns read as the one-hot encoding of `st`. -/
def BaseOneHot (envF : Env F) (st : MState) : Prop :=
  ∀ j : MState, envF.trace (mopCol j) = if j = st then 1 else 0

/-- The tree-only mirror binding: extension role `51 + j` is the lift of base column `j`
(the content of the deployed `equalityChecks`, `OptimizedMemoryGateBasis.selectorMixed`). -/
def MirrorBound (envK : Env K) (envF : Env F) : Prop :=
  ∀ j : ℕ, j < 4 → envK.trace (51 + j) = algebraMap F K (envF.trace j)

omit [FiniteDimensional F K] in
/-- **The paper's selector-summed gate evaluates to the active state's body** at a base one-hot. -/
theorem selScale_eval (envK : Env K) (envF : Env F) (st : MState) (hone : BaseOneHot envF st)
    (f : MState → Expr) :
    (selScale (F := F) f).eval envK envF = (f st).eval envK := by
  have h0 := hone .decompose
  have h1 := hone .halt
  have h2 := hone .read_root
  have h3 := hone .verify_child
  simp only [mopCol] at h0 h1 h2 h3
  cases st <;>
    simp [selScale, MixedExpr.eval, MixedExpr.ofExpr_eval, bcur, CoeffExpr.eval, h0, h1, h2, h3]

omit [FiniteDimensional F K] in
/-- Under the mirror binding the paper's base-selector sum and the deployed mirror-selector sum
(`MemoryFactorizationScope.mergedGate`'s shape, transported along `memorySubst`) take the same
value — **no one-hot hypothesis is needed** for this. -/
theorem selScale_eval_eq_merged (envK : Env K) (envF : Env F) (hb : MirrorBound envK envF)
    (f : MState → Expr) :
    (selScale (F := F) (fun st => (f st).subst memorySubst)).eval envK envF
      = ((Expr.Add (gateByM .decompose (f .decompose))
          (.Add (gateByM .halt (f .halt))
            (.Add (gateByM .read_root (f .read_root))
              (gateByM .verify_child (f .verify_child))))).subst memorySubst).eval envK := by
  have h0 : envK.trace 51 = algebraMap F K (envF.trace 0) := hb 0 (by norm_num)
  have h1 : envK.trace 52 = algebraMap F K (envF.trace 1) := hb 1 (by norm_num)
  have h2 : envK.trace 53 = algebraMap F K (envF.trace 2) := hb 2 (by norm_num)
  have h3 : envK.trace 54 = algebraMap F K (envF.trace 3) := hb 3 (by norm_num)
  simp [selScale, gateByM, mopCol, MixedExpr.eval, MixedExpr.ofExpr_eval, Expr.subst, Expr.eval,
    memorySubst, Reified.tc, extVar, bcur, CoeffExpr.eval, h0, h1, h2, h3]

omit [FiniteDimensional F K] in
/-- A base one-hot transports to the deployed mirror one-hot under the mirror binding. -/
theorem selectorOneHot_of_base (envK : Env K) (envF : Env F) (st : MState)
    (hone : BaseOneHot envF st) (hb : MirrorBound envK envF) :
    SelectorOneHot (Env.ofSubst memorySubst envK) st := by
  apply substituted_selectorOneHot envK st
  intro j
  have hj := hone j
  rw [hb (mopCol j) (by cases j <;> simp [mopCol]), hj]
  split_ifs <;> simp

/-! ## §2  The `RAP_mem` core -/

/-- The paper's gate for quantity class `q` (`MemoryFactorizationScope.paddedBlock` order):
`Σ_j op_j · (block st_j).q`, base selectors, bodies transported along `memorySubst`. -/
def paperClassGate (q : ℕ) : MixedExpr F :=
  selScale (fun st => (memQuantity (K := K) st q).subst memorySubst)

omit [FiniteDimensional F K] in
/-- **Value equality with the deployed class source**, under the mirror binding alone. -/
theorem paperClassGate_eval_eq_deployed (envK : Env K) (envF : Env F) (hb : MirrorBound envK envF)
    (q : ℕ) :
    (paperClassGate (F := F) (K := K) q).eval envK envF
      = ((MemoryFactorizationScope.mergedGate (K := K) q).subst memorySubst).eval envK :=
  selScale_eval_eq_merged envK envF hb (fun st => memQuantity (K := K) st q)

/-- The `tab:v_mem` classes other than the `cons` dyck row (`q = 1`), in quantity order:
`pt.noun` size/leaf `:2142`; `pt.indicator` `:2144`; `pt.counts` `:2152`; `lc.noun` `:2160`;
`rc.noun` `:2162`; `mem.root` `:2164`; `mem.child` `:2166`.  Sixteen. -/
def tabVMemClassIndices : List ℕ := [0, 2, 3, 4, 5, 6, 7, 10, 11, 12, 15, 16, 17, 18, 19, 20]

/-- The three classes the paper types in `𝔽`: `mem.axis` (`q = 21`),
`left_state = state` at `read_root` (`q = 25`, `:2068`) and at `verify_child` (`q = 26`, `:2076`). -/
def baseTypedClassIndices : List ℕ := [21, 25, 26]

/-- The four `x_out = ⊥` pins with no `tab:v_mem` row:
`lc.indicator`, `lc.counts`, `rc.indicator`, `rc.counts`. -/
def bottomPinIndices : List ℕ := [8, 9, 13, 14]

/-- Every class index the paper set commits through `paperClassGate`: the sixteen table classes,
`timestamp` (`22`), the three base-typed classes and the four `⊥` pins.  Twenty-four; the missing
three of `0..26` are the `cons` dyck row (`1`, `paperConsDyck`) and the two aggregator halves
(`23`, `24`, replaced by `paperAggregator`). -/
def paperClassIndices : List ℕ :=
  tabVMemClassIndices ++ [22] ++ baseTypedClassIndices ++ bottomPinIndices

theorem paperClassIndices_length : paperClassIndices.length = 24 := by decide

theorem paperClassIndices_subset_mergedCoreOrder :
    ∀ q ∈ paperClassIndices, q ∈ mergedCoreOrder := by decide

/-- The class partition: every class `q < 27` is a `paperClassGate` class, the `cons` dyck row or
one of the two aggregator halves. -/
theorem class_partition :
    ∀ q ∈ mergedCoreOrder, q ∈ paperClassIndices ∨ q = 1 ∨ q = 23 ∨ q = 24 := by decide

/-- The `cons` dyck row of `tab:v_mem` with
`Lem:NPR_decomp`'s identity cleared of `X⁻¹`:
`z · pt.dyck = mconsDyckNoInv(lc, rc)`, degree `3`, no `zinv` column.  The other three states
keep their class-`1` bodies (`halt`: `pt.dyck = 0`, `:2142`; `read_root`/`verify_child`:
`pt.dyck = lc.dyck`, `:2142`). -/
def consDyckQuantity : MState → Expr
  | .decompose => .Sub (.Mul (chl 0) mPt.dyck) (mconsDyckNoInv mLc mRc)
  | .halt => memQuantity (K := K) .halt 1
  | .read_root => memQuantity (K := K) .read_root 1
  | .verify_child => memQuantity (K := K) .verify_child 1

/-- `tab:v_mem` `pt.noun` dyck component, through `mconsDyckNoInv`. -/
def paperConsDyck : MixedExpr F :=
  selScale (fun st => ((consDyckQuantity (K := K) st).subst memorySubst))

/-- The seventeen `tab:v_mem` gates. -/
def tabVMemGates : List (MixedExpr F) :=
  tabVMemClassIndices.map (paperClassGate (K := K)) ++ [paperConsDyck (K := K)]

/-- `timestamp = 0` at `decompose`/`halt`: the fourth component of `mem_record = (0,0,0,0)`
; `𝕂`-typed by `:2117`.  No `tab:v_mem` row. -/
def timestampGate : MixedExpr F := paperClassGate (K := K) 22

/-- **W4 stage 2.**  The internal `intermediate` LogUp pole at the sampled coins
: `interPole + RLC^γ(mem_record)`, slots `6`/`4`.  Same term as
`OptimizedMemoryGateBasis.poleSource`. -/
def poleSource : Expr := .Add (.Var .challenge 6) recordRLCExpr

/-- **The 31st:** the pole over the ten-slot record, `poleSource + γ⁹ · reqIdx`; the same term as
`OptimizedMemoryGateBasis.poleSourceMixed`. -/
def poleSourceMixed : MixedExpr F := .Add (ofExpr poleSource) reqIdxRLCTerm

/-- **The `:2123` aggregator as one paper-form gate:**
`(RLC^γ(mem_record(i)) − β) · (intermediate(i) − intermediate(i−1)) = op_read − op_verify`
with the base selectors `op_2`, `op_3`, `intermediate(i) = icur` (role `28`),
`intermediate(i−1) = ipre` (role `27`).  Sign: `Algorithm:Memspec` the paper
(`read_root`: `intermediate_{i+1} − intermediate_i = (RLC + X)⁻¹`) and `:2080` (`verify_child`,
negated), which the tree's `memInterExprs` follow; the paper writes `op_3 − op_2`, the
opposite sign.  Degree `2`.  It replaces the deployed classes `q = 23` (`Δ ∓ g`) and `q = 24`
(`pole · g − 1`), and leaves the witness column `g` (role `29`) unread. -/
def paperAggregator : MixedExpr F :=
  .Sub (.Mul poleSourceMixed (.Sub (.Var .traceCur 28) (.Var .traceCur 27)))
    (.Sub (.Lift (bcur 2)) (.Lift (bcur 3)))

/-- `RAP_mem`'s `𝕂` gates: seventeen table gates, `timestamp`, the aggregator — nineteen against
`Thm:mem_38`'s coefficient `20`. -/
def rapMemGates : List (MixedExpr F) :=
  tabVMemGates (K := K) ++ [timestampGate (K := K), paperAggregator]

/-- The three `𝔽`-typed classes, as mixed gates over the deployed layout (module docstring). -/
def baseTypedClassGates : List (MixedExpr F) := baseTypedClassIndices.map (paperClassGate (K := K))

/-- **The four `⊥` pins**, `Algorithm:Memspec` the paper (`x_out = ⊥` at `halt`), `:2071`
and `:2079` (`right_child, right_state, axis_indicator_R, axis_counts_R = ⊥`). **No `tab:v_mem`
row** (`:2138-2168` has no `lc.indicator`/`lc.counts`/`rc.indicator`/`rc.counts` row); the tree
reads `⊥` as `0`. -/
def bottomPins : List (MixedExpr F) := bottomPinIndices.map (paperClassGate (K := K))

/-- `chainMixed`, kept verbatim: `(1 − last) · (icur(i) − ipre(i+1))`, forced by
the paper putting `intermediate_i` and `intermediate_{i+1}` in one witness row. -/
def intermediateChain : MixedExpr F := chainMixed

/-! ## §3  Walk, IO, endpoints -/

/-- Forest-walk initial constraints (`Thm:Walk_IOP`; `Trans.walkLn1`, `walkCount1`,
`walkAccInit` along `walkBoundarySubst`), masked by the preprocessing first-row mask (base column
`4`) rather than the tree's extension mask role `47`.  Paper: initial constraints of `RAP_walk`
, the accumulator seed the paper at `i = 1`. -/
def hostedWalkInitGates : List (MixedExpr F) :=
  [Trans.walkLn1, Trans.walkCount1, Trans.walkAccInitMasked].map
    (fun e => .Scale (bcur 4) (ofExpr (e.subst walkBoundarySubst)))

/-- Forest-walk transition constraints over the HOSTED roles (the paper `2 + 2·e` of degree
`1`, `:983` `e` of degree `3`; `Trans.walkLnStep`, `walkCountStep`, `walkAccStep` along
`walkSubst`), masked by `(1 − last)` on base column `5`. -/
def hostedWalkStepGates : List (MixedExpr F) :=
  [Trans.walkLnStep, Trans.walkCountStep].map
    (fun e => .Scale (.sub (.const 1) (bcur 5)) (ofExpr (e.subst walkSubst)))

/-- Hosted acc step as a MixedExpr: the 47/48-style lift of `walkAccStepHosted`,
    reading preprocessing column `154` and last-mask column `5`. -/
def hostedWalkAccStep : MixedExpr F :=
  .Add
    (.Scale (bcur 154)
      (ofExpr ((Expr.Mul (Trans.tn 0) (Trans.tn 3)).subst walkSubst)))
    (.Scale (.sub (.const 1) (bcur 5))
      (ofExpr ((Expr.Sub (Expr.Sub (Trans.tn 2) (Reified.tc 2))
          (Expr.Mul (Reified.tc 1) (Trans.tn 4))).subst walkSubst)))

/-- **H1.W memory (twenty-first move): the committed walk boundary gates** — the line gate
unchanged, then `MemoryWalkLabel.walkCount1InGate` / `walkAccInitInGate` with `cur`/`cc`/`cm`
IN THE GATE.  Byte-identical to
`OptimizedMemoryGateBasis.walkInitGates`. -/
def walkInitGates : List (MixedExpr F) :=
  [.Scale (bcur 4) (ofExpr (Trans.walkLn1.subst walkBoundarySubst)),
   MemoryWalkLabel.walkCount1InGate, MemoryWalkLabel.walkAccInitInGate]

/-- **H1.W memory: the committed walk transition gates**, `cur`/`cc`/`cm` of the successor row
in-gate.  Byte-identical to `OptimizedMemoryGateBasis.walkStepGates`. -/
def walkStepGates : List (MixedExpr F) :=
  [.Scale (.sub (.const 1) (bcur 5)) (ofExpr (Trans.walkLnStep.subst walkSubst)),
   MemoryWalkLabel.walkCountStepInGate, MemoryWalkLabel.walkAccStepInGate]

/-- Forest-walk terminal: `out_walk = acc_walk(h)` with `out_walk = 0`
(`:963`), as `last · acc_walk` (role `33`). -/
def walkTerminal : MixedExpr F := .Scale (bcur 5) (.Var .traceCur 33)

def walkGates : List (MixedExpr F) := walkInitGates ++ walkStepGates ++ [walkTerminal]


def hostedWalkGates : List (MixedExpr F) :=
  hostedWalkInitGates ++ hostedWalkStepGates ++ [hostedWalkAccStep, walkTerminal]

/-- `ver(i) · (ver(i) − 1) = 0`.  The paper types `ver ∈ 𝔽` (`:557`); the
deployed layout carries it as `𝕂` role `39`, so this is a `𝕂` gate here (same remark as
`baseTypedClassGates`). -/
def verBool : MixedExpr F :=
  .Mul (.Var .traceCur 39) (.Sub (.Var .traceCur 39) (.Const 1))

/-- The inactive-safe denominator `safe = ver · denom + (1 − ver)` (role `50`; the tree's
factorisation of the paper's `ver · (RLC − β)`). -/
def safeNormalisation : MixedExpr F :=
  .Sub (.Var .traceCur 50)
    (.Add (.Mul (.Var .traceCur 39) (.Var .traceCur 37)) (.Sub (.Const 1) (.Var .traceCur 39)))

/-- `safe · inv = 1` (roles `50`, `38`): the committed reciprocal that witnesses `denom ≠ 0` at a
verify row. -/
def safeInverse : MixedExpr F :=
  .Sub (.Mul (.Var .traceCur 50) (.Var .traceCur 38)) (.Const 1)

/-- `contribution = ver · inv` (role `42`): the row's LogUp term `ver / (RLC − β)`
. -/
def contribution : MixedExpr F :=
  .Sub (.Var .traceCur 42) (.Mul (.Var .traceCur 39) (.Var .traceCur 38))

/-- **The denominator pin**: `role 37 = pole + RLC^γ(mem_record)`, the
paper's `RLC^α(x_mem(i,·)) − β` in `FiniteIO.compress`'s additive convention, with `γ` at memory challenge slot `4` and
`pole` at slot `5`.  Degree `1`.  **Since A-mem-2 this is the committed gate
`OptimizedMemoryGateBasis.denominatorPinMixed`** (the same term; `recordRLCExpr`/`recordRLC`
moved there with it), the fifth member of `mixedTransitionGates`, and the two slots are pinned to
the sampled coins by `OptimizedProductionAcceptanceAt.memory_sampled_coins`. -/
abbrev denominatorPin : MixedExpr F := denominatorPinMixed

theorem denominatorPin_eq_committed : (denominatorPin (F := F)) = denominatorPinMixed := rfl

/-- **Single-column accumulator step**:
`(1 − last) · (acc(i+1) − acc(i) − contribution(i))` on role `43` alone, next-row read.  The
deployed two-role layout spends `e` more; role `44` is unread here. -/
def accStep : MixedExpr F :=
  .Scale (.sub (.const 1) (bcur 5))
    (.Sub (.Var .traceNext 43) (.Add (.Var .traceCur 43) (.Var .traceCur 42)))

/-- `first · acc = 0` — the accumulator starts at `0` (the tree's count-up convention; the paper
seeds `acc_mem(1)` from `responses`, the paper, and the shared-terminal design (A) makes both
chips count `0 → requests`, `:597`). -/
def accInit : MixedExpr F := .Scale (bcur 4) (.Var .traceCur 43)

/-- `last · (acc(h₂) + contribution(h₂) − requests) = 0`: `out_mem = acc_mem(h₂)`
against the post-challenge public `requests` (extension public role `2`, `:597`
`requests = responses`).  In the single-column layout `acc_after(h₂) = acc(h₂) + contribution(h₂)`. -/
def accTerminal : MixedExpr F :=
  .Scale (bcur 5)
    (.Sub (.Add (.Var .traceCur 43) (.Var .traceCur 42)) (.Var .publicVal 2))

/-- `role 40 = requests`. -/
def terminalRole : MixedExpr F := .Sub (.Var .traceCur 40) (.Var .publicVal 2)

/-- The IO block, with the denominator pin (since A-mem-2; before it the pin sat in `newGates`
as a gate the deployed set did not imply). -/
def ioCoreGates : List (MixedExpr F) :=
  [verBool, safeNormalisation, safeInverse, contribution, accStep, accInit, accTerminal,
    terminalRole, denominatorPin]

/-- `first · ipre = 0`: the initial value of `intermediate` is zero. -/
def intermediateInit : MixedExpr F := .Scale (bcur 4) (.Var .traceCur 27)

/-- `last · icur = 0`: the terminal value of `intermediate` is zero. -/
def intermediateTerminal : MixedExpr F := .Scale (bcur 5) (.Var .traceCur 28)

/-- **The two `intermediate` endpoint gates** — since the `LU` repair implied by the
deployed set (`deployed_implies_intermediateInit/Terminal`, §6); previously the two gates it
did not imply. Three until A-mem-2: the denominator pin was the first, and is committed
(`deployed_implies_denominatorPin`). -/
def newGates : List (MixedExpr F) :=
  [intermediateInit, intermediateTerminal,
    OptimizedMemoryGateBasis.rootMaskCountsGate,
    OptimizedMemoryGateBasis.rootMaskIndicatorGate]

/-- The State-Variables block: four booleanities and the one-hot sum on
base columns `0..3`.  Identical to the first five deployed base gates. -/
def paperBaseGates : List (CoeffExpr F) :=
  [bbool (bcur 0), bbool (bcur 1), bbool (bcur 2), bbool (bcur 3), bsum4 .traceCur]

/-- The paper set's `𝕂` gates **without** `newGates`: the part the deployed set implies. -/
def paperKGatesCore : List (MixedExpr F) :=
  rapMemGates (K := K) ++ baseTypedClassGates (K := K) ++ bottomPins (K := K)
    ++ [intermediateChain] ++ walkGates ++ ioCoreGates

/-- **The paper-shaped `𝕂` gate set** (committed; H1.W memory walk gates in-gate). -/
def paperKGates : List (MixedExpr F) :=
  paperKGatesCore (K := K) ++ newGates ++ MemoryWalkLabel.queueWitnessGates


def hostedPaperKGatesCore : List (MixedExpr F) :=
  rapMemGates (K := K) ++ baseTypedClassGates (K := K) ++ bottomPins (K := K)
    ++ [intermediateChain] ++ hostedWalkGates
    ++ ioCoreGates

def hostedNewGates : List (MixedExpr F) := [intermediateInit, intermediateTerminal]

def hostedPaperKGates : List (MixedExpr F) :=
  hostedPaperKGatesCore (K := K) ++ hostedNewGates

omit [FiniteDimensional F K] in
theorem paperBaseGates_eq_prefix (b : Basis (Fin 3) F K) :
    paperBaseGates (F := F) = (foldedBaseTransitionGates b).take 5 := rfl

/-! ## §4  Exactness against the deployed semantic language -/

/-- The **pre-W2** (folded) row language, kept so `deployed_to_paper` still has a subject.
The committed chip since W2 is `PaperRow` (`memorySourceTemplate` commits `paperBaseGates` /
`paperKGates`). -/
def DeployedRow (b : Basis (Fin 3) F K) (envF : Env F) : Prop :=
  (∀ g ∈ foldedBaseTransitionGates b, g.eval envF = 0) ∧
  (∀ g ∈ foldedEqualityChecks b, g.eval envF = 0) ∧
  (∀ g ∈ extensionTransitionGates (K := K) ++ degreeOneEndpoints ++ foldedDegreeThreeEndpoints,
    g.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) = 0) ∧
  (∀ g ∈ foldedMixedTransitionGates (F := F),
    g.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) envF = 0)

/-- The paper row language, core part. -/
def PaperRowCore (b : Basis (Fin 3) F K) (envF : Env F) : Prop :=
  (∀ g ∈ paperBaseGates (F := F), g.eval envF = 0) ∧
  (∀ g ∈ paperKGatesCore (F := F) (K := K), g.eval (gatherEnv b memoryCol0 envF) envF = 0)

/-- The full paper row language. -/
def PaperRow (b : Basis (Fin 3) F K) (envF : Env F) : Prop :=
  (∀ g ∈ paperBaseGates (F := F), g.eval envF = 0) ∧
  (∀ g ∈ paperKGates (F := F) (K := K), g.eval (gatherEnv b memoryCol0 envF) envF = 0)


def HostedPaperRowCore (b : Basis (Fin 3) F K) (envF : Env F) : Prop :=
  (∀ g ∈ paperBaseGates (F := F), g.eval envF = 0) ∧
  (∀ g ∈ hostedPaperKGatesCore (F := F) (K := K), g.eval (gatherEnv b memoryCol0 envF) envF = 0)


def HostedPaperRow (b : Basis (Fin 3) F K) (envF : Env F) : Prop :=
  (∀ g ∈ paperBaseGates (F := F), g.eval envF = 0) ∧
  (∀ g ∈ hostedPaperKGates (F := F) (K := K), g.eval (gatherEnv b memoryCol0 envF) envF = 0)

/-- **Tree-only bindings**: the twelve selector-mirror equality checks and the three mask
bindings (`firstMaskMixed`, `lastMaskMixed`, `dequeueMaskMixed`).  They bind extension
columns (`51..54`, `47`, `48`, `56`) that exist only because the tree splits its row into
base and extension parts; the paper set reads the base columns directly
and never reads these. -/
structure TreeOnlyBindings (envK : Env K) (envF : Env F) : Prop where
  mirror : MirrorBound envK envF
  firstMask : envK.trace 47 = algebraMap F K (envF.trace 4)
  lastMask : envK.trace 48 = algebraMap F K (envF.trace 5)
  dequeueMask : envK.trace 56 = algebraMap F K (envF.trace 154)

/-- The two preprocessing masks are boolean (they are `firstRowMask`/`lastRowMask`, fixed by
`BindsPreprocessing` on any accepted trace). -/
structure PreprocessingMasksBoolean (envF : Env F) : Prop where
  first : envF.trace 4 * (envF.trace 4 - 1) = 0
  last : envF.trace 5 * (envF.trace 5 - 1) = 0

/-- **Honest values of the columns the paper set leaves unread.**  Each deployed gate that reads
one of them is that column's definition, so the reverse direction needs the value as a hypothesis:
`zinv` (role `30`, `z · zinv = 1`); the LogUp witness `g` (role `29`, `= ±Δ intermediate` at the
active state); `acc_after` (role `44`, `= acc + contribution`); and the product column the
deployed chip pins to `0` — `41` (`first · walkAccInit`). -/
structure DeadWitnessesHonest (envK : Env K) (st : MState) : Prop where
  zinv : envK.chal 0 * envK.trace 30 = 1
  logUpRead : st = .read_root → envK.trace 29 = envK.trace 28 - envK.trace 27
  logUpVerify : st = .verify_child → envK.trace 29 = envK.trace 27 - envK.trace 28
  accAfter : envK.trace 44 = envK.trace 43 + envK.trace 42
  forestInitResidual : envK.trace 41 = 0

/-! ### Membership in the deployed fold sources -/

omit [FiniteDimensional F K] in
theorem memoryRowSources_drop_five :
    (memoryRowSources (K := K)).drop 5 =
      ([zZinvExprM] ++ mergedMemoryCore (K := K)).map (fun e => e.subst memorySubst) := by
  simp [memoryRowSources, mergedMemoryConstraints, memSvExprs, memSvBoolExprs, allMStates]

omit [FiniteDimensional F K] in
/-- The forty deployed fold sources, by name. -/
theorem mem_extensionFoldSources_iff (e : Expr) :
    e ∈ extensionFoldSources (K := K) ↔
      e = zZinvExprM.subst memorySubst ∨
      (∃ q ∈ mergedCoreOrder, e = (MemoryFactorizationScope.mergedGate (K := K) q).subst memorySubst) ∨
      e ∈ walkBoundarySources ∨ e ∈ walkTransitionSources ∨ e ∈ sampledFoldSources := by
  simp only [extensionFoldSources, memoryRowSources_drop_five, mergedMemoryCore, List.mem_append,
    List.mem_map, List.mem_singleton]
  constructor
  · rintro (((⟨c, hc | ⟨q, hq, rfl⟩, rfl⟩ | h) | h) | h)
    · exact Or.inl (by rw [hc])
    · exact Or.inr (Or.inl ⟨q, hq, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rintro (rfl | ⟨q, hq, rfl⟩ | h | h | h)
    · exact Or.inl (Or.inl (Or.inl ⟨_, Or.inl rfl, rfl⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨_, Or.inr ⟨q, hq, rfl⟩, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-! ### Per-block correspondence lemmas -/

section RowLemmas

variable (envK : Env K) (envF : Env F)

omit [FiniteDimensional F K] in
/-- The `cons` dyck gate and the deployed class `1` agree at any one-hot state where the `zinv`
column is honest (`MemoryFactorizationScope.cons_dyck_gate_equiv`). -/
theorem paperConsDyck_iff (st : MState) (hone : BaseOneHot envF st) (hb : MirrorBound envK envF)
    (hzinv : envK.chal 0 * envK.trace 30 = 1) :
    (paperConsDyck (F := F) (K := K)).eval envK envF = 0 ↔
      ((MemoryFactorizationScope.mergedGate (K := K) 1).subst memorySubst).eval envK = 0 := by
  rw [paperConsDyck, selScale_eval envK envF st hone,
    mergedGate_subst_eval envK st (selectorOneHot_of_base envK envF st hone hb) 1]
  cases st
  · rw [Expr.eval_subst, Expr.eval_subst]
    have hz' : (chl 0).eval (Env.ofSubst memorySubst envK) *
        (Reified.tc 34).eval (Env.ofSubst memorySubst envK) = 1 := by
      simpa [Env.ofSubst, memorySubst, chl, Reified.tc, extVar, Expr.eval] using hzinv
    have hz : (chl 0).eval (Env.ofSubst memorySubst envK) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hz'
      exact zero_ne_one hz'
    exact cons_dyck_gate_equiv _ hz hz'
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl

omit [FiniteDimensional F K] in
theorem memQuantity_23_decompose :
    memQuantity (K := K) .decompose 23 = .Sub (Reified.tc 32) (Reified.tc 31) := rfl
omit [FiniteDimensional F K] in
theorem memQuantity_23_halt :
    memQuantity (K := K) .halt 23 = .Sub (Reified.tc 32) (Reified.tc 31) := rfl
omit [FiniteDimensional F K] in
theorem memQuantity_23_read :
    memQuantity (K := K) .read_root 23 = .Sub (.Sub (Reified.tc 32) (Reified.tc 31)) (Reified.tc 33) := rfl
omit [FiniteDimensional F K] in
theorem memQuantity_23_verify :
    memQuantity (K := K) .verify_child 23 =
      .Add (.Sub (Reified.tc 32) (Reified.tc 31)) (Reified.tc 33) := rfl
omit [FiniteDimensional F K] in
theorem memQuantity_24_decompose : memQuantity (K := K) .decompose 24 = .Const 0 := rfl
omit [FiniteDimensional F K] in
theorem memQuantity_24_halt : memQuantity (K := K) .halt 24 = .Const 0 := rfl
omit [FiniteDimensional F K] in
theorem memQuantity_24_read :
    memQuantity (K := K) .read_root 24 = .Sub (.Mul poleExpr (Reified.tc 33)) (.Const 1) := rfl
omit [FiniteDimensional F K] in
theorem memQuantity_24_verify :
    memQuantity (K := K) .verify_child 24 = .Sub (.Mul poleExpr (Reified.tc 33)) (.Const 1) := rfl

omit [FiniteDimensional F K] in
/-- `op_read − op_verify` at state `st`: `+1` at `read_root`, `−1` at `verify_child`, `0` else
(`Algorithm:Memspec` the paper, `:2080`). -/
def aggregatorSign : MState → K
  | .read_root => 1
  | .verify_child => -1
  | _ => 0

omit [FiniteDimensional F K] in
/-- The paper aggregator's value at a base one-hot: `pole · (icur − ipre) − (op_read − op_verify)`. -/
theorem paperAggregator_eval (st : MState) (hone : BaseOneHot envF st) :
    (paperAggregator (F := F)).eval envK envF =
      poleSourceMixed.eval envK envF * (envK.trace 28 - envK.trace 27) - aggregatorSign st := by
  have h2 := hone .read_root
  have h3 := hone .verify_child
  simp only [mopCol] at h2 h3
  simp only [paperAggregator, MixedExpr.eval, MixedExpr.ofExpr_eval, bcur, CoeffExpr.eval, h2, h3]
  cases st <;> simp [aggregatorSign]

omit [FiniteDimensional F K] in

theorem paperAggregator_of_signed_inv (st : MState) (hone : BaseOneHot envF st)
    (hden : poleSourceMixed.eval envK envF ≠ 0)
    (hΔ : envK.trace 28 - envK.trace 27 =
      aggregatorSign st * (poleSourceMixed.eval envK envF)⁻¹) :
    (paperAggregator (F := F)).eval envK envF = 0 := by
  rw [paperAggregator_eval envK envF st hone, hΔ, mul_left_comm, mul_inv_cancel₀ hden, mul_one,
    sub_self]

omit [FiniteDimensional F K] in
/-- **Paper ⇒ deployed** for the aggregator: the one-gate form gives classes `23` and `24`, given
the honest LogUp witness `g` and `pole ≠ 0` (needed at `decompose`/`halt`, where the paper form
reads `pole · Δ = 0`). -/
theorem deployed_aggregator_of_paper (st : MState) (hone : BaseOneHot envF st)
    (hb : MirrorBound envK envF)
    (hpole : poleSourceMixed.eval envK envF ≠ 0)
    (hread : st = .read_root → envK.trace 29 = envK.trace 28 - envK.trace 27)
    (hverify : st = .verify_child → envK.trace 29 = envK.trace 27 - envK.trace 28)
    (hpeq : (st = .read_root ∨ st = .verify_child) →
      (Expr.subst memorySubst poleExpr).eval envK = poleSourceMixed.eval envK envF)
    (hp : (paperAggregator (F := F)).eval envK envF = 0) :
    ((MemoryFactorizationScope.mergedGate (K := K) 23).subst memorySubst).eval envK = 0 ∧
      ((MemoryFactorizationScope.mergedGate (K := K) 24).subst memorySubst).eval envK = 0 := by
  have hone' := selectorOneHot_of_base envK envF st hone hb
  rw [mergedGate_subst_eval envK st hone' 23, mergedGate_subst_eval envK st hone' 24]
  rw [paperAggregator_eval envK envF st hone] at hp
  cases st
  · rw [memQuantity_23_decompose, memQuantity_24_decompose]
    simp only [Expr.subst, Expr.eval, memorySubst, Reified.tc, extVar]
    simp only [aggregatorSign, sub_zero] at hp
    norm_num [Expr.eval]
    exact (mul_eq_zero.mp hp).resolve_left hpole
  · rw [memQuantity_23_halt, memQuantity_24_halt]
    simp only [Expr.subst, Expr.eval, memorySubst, Reified.tc, extVar]
    simp only [aggregatorSign, sub_zero] at hp
    norm_num [Expr.eval]
    exact (mul_eq_zero.mp hp).resolve_left hpole
  · have hg := hread rfl
    have hpe := hpeq (Or.inl rfl)
    rw [memQuantity_23_read, memQuantity_24_read]
    simp only [Expr.subst, Expr.eval, memorySubst, Reified.tc, extVar]
    simp only [aggregatorSign] at hp
    norm_num [Expr.eval]
    change _ ∧ (Expr.subst memorySubst poleExpr).eval envK * envK.trace 29 - 1 = 0
    refine ⟨by rw [hg]; ring, ?_⟩
    rw [hpe, hg]; linear_combination hp
  · have hg := hverify rfl
    have hpe := hpeq (Or.inr rfl)
    rw [memQuantity_23_verify, memQuantity_24_verify]
    simp only [Expr.subst, Expr.eval, memorySubst, Reified.tc, extVar]
    simp only [aggregatorSign] at hp
    norm_num [Expr.eval]
    change _ ∧ (Expr.subst memorySubst poleExpr).eval envK * envK.trace 29 - 1 = 0
    refine ⟨by rw [hg]; ring, ?_⟩
    rw [hpe, hg]; linear_combination -hp

omit [FiniteDimensional F K] in
/-- A first-row-masked paper gate and the deployed `firstE`-masked source agree under the mask
binding. -/
theorem scale_first_eval (hfirst : envK.trace 47 = algebraMap F K (envF.trace 4)) (X : Expr) :
    (MixedExpr.Scale (bcur 4) (ofExpr X) : MixedExpr F).eval envK envF
      = (Expr.Mul firstE X).eval envK := by
  simp [MixedExpr.eval, MixedExpr.ofExpr_eval, bcur, CoeffExpr.eval, firstE, extVar, Expr.eval,
    hfirst]

omit [FiniteDimensional F K] in
theorem scale_notLast_eval (hlast : envK.trace 48 = algebraMap F K (envF.trace 5)) (X : Expr) :
    (MixedExpr.Scale (.sub (.const 1) (bcur 5)) (ofExpr X) : MixedExpr F).eval envK envF
      = (Expr.Mul notLastE X).eval envK := by
  simp [MixedExpr.eval, MixedExpr.ofExpr_eval, bcur, CoeffExpr.eval, notLastE, lastE, extVar,
    Expr.eval, hlast]

omit [FiniteDimensional F K] in
/-- A dequeue-masked paper gate and the deployed `dequeueMaskE`-masked source agree under
    the 47/48-style pin `role 56 = col 154`. -/
theorem scale_dequeue_eval (hdeq : envK.trace 56 = algebraMap F K (envF.trace 154)) (X : Expr) :
    (MixedExpr.Scale (bcur 154) (ofExpr X) : MixedExpr F).eval envK envF
      = (Expr.Mul dequeueMaskE X).eval envK := by
  simp [MixedExpr.eval, MixedExpr.ofExpr_eval, bcur, CoeffExpr.eval, dequeueMaskE, extVar,
    Expr.eval, hdeq]

omit [FiniteDimensional F K] in
theorem hostedWalkInitGates_iff (hfirst : envK.trace 47 = algebraMap F K (envF.trace 4)) :
    (∀ g ∈ hostedWalkInitGates (F := F), g.eval envK envF = 0) ↔
      ∀ e ∈ walkBoundarySources, e.eval envK = 0 := by
  simp only [hostedWalkInitGates, walkBoundarySources, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro h e he; rw [← scale_first_eval envK envF hfirst]; exact h e he
  · intro h e he; rw [scale_first_eval envK envF hfirst]; exact h e he

omit [FiniteDimensional F K] in
theorem hostedWalkStepGates_iff (hlast : envK.trace 48 = algebraMap F K (envF.trace 5)) :
    (∀ g ∈ hostedWalkStepGates (F := F), g.eval envK envF = 0) ↔
      ∀ e ∈ walkLnCountTransitionSources, e.eval envK = 0 := by
  simp only [hostedWalkStepGates, walkLnCountTransitionSources, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro h e he; rw [← scale_notLast_eval envK envF hlast]; exact h e he
  · intro h e he; rw [scale_notLast_eval envK envF hlast]; exact h e he

omit [FiniteDimensional F K] in
theorem hostedWalkAccStep_eval
    (hdeq : envK.trace 56 = algebraMap F K (envF.trace 154))
    (hlast : envK.trace 48 = algebraMap F K (envF.trace 5)) :
    (hostedWalkAccStep (F := F)).eval envK envF = walkAccStepHosted.eval envK := by
  unfold hostedWalkAccStep walkAccStepHosted
  rw [MixedExpr.eval, Expr.eval]
  rw [scale_dequeue_eval envK envF hdeq, scale_notLast_eval envK envF hlast]

omit [FiniteDimensional F K] in
theorem walkTerminal_iff (hlast : envK.trace 48 = algebraMap F K (envF.trace 5)) :
    (walkTerminal (F := F)).eval envK envF = 0 ↔
      (Expr.Mul (extVar .traceCur 48) (extVar .traceCur 33)).eval envK = 0 := by
  simp [walkTerminal, MixedExpr.eval, bcur, CoeffExpr.eval, extVar, Expr.eval, hlast]

end RowLemmas

/-! ### The compiled coordinates of the two deployed IO base gates -/

omit [FiniteDimensional F K] in
theorem sampledTerminalCoord_eq_compile (b : Basis (Fin 3) F K) (k : Fin 3) :
    mixedCompile b memoryCol0 (terminalRole (F := F)) k = sampledTerminalCoord k := rfl

omit [FiniteDimensional F K] in
theorem sampledAccumulatorCoord_eq_compile (b : Basis (Fin 3) F K) (k : Fin 3) :
    mixedCompile b memoryCol0
      (MixedExpr.Sub (.Var .traceCur 44) (.Add (.Var .traceCur 43) (.Var .traceCur 42))) k
      = sampledAccumulatorCoord k := rfl

/-- The deployed accumulator step at the `𝕂` level ⟺ its three committed coordinates. -/
theorem accAfter_iff_coords (b : Basis (Fin 3) F K) (envF : Env F) :
    (gatherEnv b memoryCol0 envF).trace 44 =
        (gatherEnv b memoryCol0 envF).trace 43 + (gatherEnv b memoryCol0 envF).trace 42 ↔
      ∀ k : Fin 3, (sampledAccumulatorCoord (F := F) k).eval envF = 0 := by
  have h := mixedCompile_zero_iff b memoryCol0 (isCoordEnv_gather b memoryCol0 envF)
    (MixedExpr.Sub (.Var .traceCur 44) (.Add (.Var .traceCur 43) (.Var .traceCur 42)) :
      MixedExpr F)
  simp only [MixedExpr.eval, sub_eq_zero] at h
  simpa only [sampledAccumulatorCoord_eq_compile] using h

theorem terminalRole_iff_coords (b : Basis (Fin 3) F K) (envF : Env F) :
    (terminalRole (F := F)).eval (gatherEnv b memoryCol0 envF) envF = 0 ↔
      ∀ k : Fin 3, (sampledTerminalCoord (F := F) k).eval envF = 0 := by
  have h := mixedCompile_zero_iff b memoryCol0 (isCoordEnv_gather b memoryCol0 envF)
    (terminalRole (F := F))
  simpa only [sampledTerminalCoord_eq_compile] using h

/-- The twelve deployed equality checks ⟺ the mirror binding. -/
theorem equalityChecks_iff_mirror (b : Basis (Fin 3) F K) (envF : Env F) :
    (∀ g ∈ foldedEqualityChecks b, g.eval envF = 0) ↔ MirrorBound (gatherEnv b memoryCol0 envF) envF := by
  constructor
  · intro h j hj
    have hs := (mixedCompile_zero_iff b memoryCol0 (isCoordEnv_gather b memoryCol0 envF)
      (selectorMixed (F := F) ⟨j, hj⟩)).2
      (fun k => h _ ((mem_foldedEqualityChecks b _).2 ⟨⟨j, hj⟩, k, rfl⟩))
    simpa [selectorMixed, MixedExpr.eval, bcur, CoeffExpr.eval, sub_eq_zero] using hs
  · intro h g hg
    obtain ⟨s, k, rfl⟩ := (mem_foldedEqualityChecks b g).mp hg
    refine (mixedCompile_zero_iff b memoryCol0 (isCoordEnv_gather b memoryCol0 envF)
      (selectorMixed (F := F) s)).1 ?_ k
    have := h s s.isLt
    simp [selectorMixed, MixedExpr.eval, bcur, CoeffExpr.eval, this]

/-- The deployed row language yields the tree-only bindings. -/
theorem bindings_of_deployed (b : Basis (Fin 3) F K) (envF : Env F) (hd : DeployedRow b envF) :
    TreeOnlyBindings (gatherEnv b memoryCol0 envF) envF := by
  obtain ⟨-, heq, -, hmixed⟩ := hd
  refine ⟨(equalityChecks_iff_mirror b envF).1 heq, ?_, ?_, ?_⟩
  · have := hmixed firstMaskMixed (by simp [foldedMixedTransitionGates])
    simpa [firstMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval, sub_eq_zero,
      memorySourceTemplate_col0] using this
  · have := hmixed lastMaskMixed (by simp [foldedMixedTransitionGates])
    simpa [lastMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval, sub_eq_zero,
      memorySourceTemplate_col0] using this
  · have := hmixed dequeueMaskMixed (by simp [foldedMixedTransitionGates])
    simpa [dequeueMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval, sub_eq_zero,
      memorySourceTemplate_col0] using this

/-- Membership in the paper core, by named block. -/
theorem mem_paperKGatesCore_iff (g : MixedExpr F) :
    g ∈ paperKGatesCore (F := F) (K := K) ↔
      (∃ q ∈ tabVMemClassIndices, paperClassGate (K := K) q = g) ∨ g = paperConsDyck (K := K) ∨
      g = timestampGate (K := K) ∨ g = paperAggregator ∨
      (∃ q ∈ baseTypedClassIndices, paperClassGate (K := K) q = g) ∨
      (∃ q ∈ bottomPinIndices, paperClassGate (K := K) q = g) ∨
      g = intermediateChain ∨ g ∈ walkInitGates ∨ g ∈ walkStepGates ∨ g = walkTerminal ∨
      g ∈ ioCoreGates := by
  simp only [paperKGatesCore, rapMemGates, tabVMemGates, baseTypedClassGates, bottomPins,
    walkGates, List.mem_append, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc]

theorem classGate_mem_paperKGatesCore (q : ℕ) (hq : q ∈ paperClassIndices) :
    paperClassGate (F := F) (K := K) q ∈ paperKGatesCore (K := K) := by
  rw [mem_paperKGatesCore_iff]
  simp only [paperClassIndices, List.mem_append, List.mem_singleton] at hq
  rcases hq with ((hq | rfl) | hq) | hq
  · exact Or.inl ⟨q, hq, rfl⟩
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hq, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hq, rfl⟩)))))


theorem mem_hostedPaperKGatesCore_iff (g : MixedExpr F) :
    g ∈ hostedPaperKGatesCore (F := F) (K := K) ↔
      (∃ q ∈ tabVMemClassIndices, paperClassGate (K := K) q = g) ∨ g = paperConsDyck (K := K) ∨
      g = timestampGate (K := K) ∨ g = paperAggregator ∨
      (∃ q ∈ baseTypedClassIndices, paperClassGate (K := K) q = g) ∨
      (∃ q ∈ bottomPinIndices, paperClassGate (K := K) q = g) ∨
      g = intermediateChain ∨ g ∈ hostedWalkInitGates ∨ g ∈ hostedWalkStepGates ∨
      g = hostedWalkAccStep ∨ g = walkTerminal ∨ g ∈ ioCoreGates := by
  simp only [hostedPaperKGatesCore, rapMemGates, tabVMemGates, baseTypedClassGates, bottomPins,
    hostedWalkGates, List.mem_append, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc]

theorem classGate_mem_hostedPaperKGatesCore (q : ℕ) (hq : q ∈ paperClassIndices) :
    paperClassGate (F := F) (K := K) q ∈ hostedPaperKGatesCore (K := K) := by
  rw [mem_hostedPaperKGatesCore_iff]
  simp only [paperClassIndices, List.mem_append, List.mem_singleton] at hq
  rcases hq with ((hq | rfl) | hq) | hq
  · exact Or.inl ⟨q, hq, rfl⟩
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hq, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hq, rfl⟩)))))

/-- **Hosted core + the four in-gate walk gates ⇒ the committed core.**  The two cores share every
gate but the walk count/acc gates: the line gates and the terminal are the same terms. -/
theorem paperRowCore_of_hosted (b : Basis (Fin 3) F K) (envF : Env F)
    (hh : HostedPaperRowCore b envF)
    (hwalk : ∀ g ∈ MemoryWalkLabel.inGateWalkGates (F := F),
      g.eval (gatherEnv b memoryCol0 envF) envF = 0) :
    PaperRowCore b envF := by
  refine ⟨hh.1, fun g hg => ?_⟩
  have hin : ∀ g ∈ walkInitGates (F := F), g.eval (gatherEnv b memoryCol0 envF) envF = 0 := by
    intro g hg
    simp only [walkInitGates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact hh.2 _ ((mem_hostedPaperKGatesCore_iff _).2 (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_map.2 ⟨Trans.walkLn1, by simp, rfl⟩))))))))))
    · exact hwalk _ (by simp [MemoryWalkLabel.inGateWalkGates])
    · exact hwalk _ (by simp [MemoryWalkLabel.inGateWalkGates])
  have hstep : ∀ g ∈ walkStepGates (F := F), g.eval (gatherEnv b memoryCol0 envF) envF = 0 := by
    intro g hg
    simp only [walkStepGates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact hh.2 _ ((mem_hostedPaperKGatesCore_iff _).2 (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_map.2 ⟨Trans.walkLnStep, by simp, rfl⟩)))))))))))
    · exact hwalk _ (by simp [MemoryWalkLabel.inGateWalkGates])
    · exact hwalk _ (by simp [MemoryWalkLabel.inGateWalkGates])
  rcases (mem_paperKGatesCore_iff g).1 hg with h | h | h | h | h | h | h | h | h | h | h
  · exact hh.2 g ((mem_hostedPaperKGatesCore_iff g).2 (Or.inl h))
  · exact hh.2 g ((mem_hostedPaperKGatesCore_iff g).2 (Or.inr (Or.inl h)))
  · exact hh.2 g ((mem_hostedPaperKGatesCore_iff g).2 (Or.inr (Or.inr (Or.inl h))))
  · exact hh.2 g ((mem_hostedPaperKGatesCore_iff g).2 (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact hh.2 g ((mem_hostedPaperKGatesCore_iff g).2 (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h))))))
  · exact hh.2 g ((mem_hostedPaperKGatesCore_iff g).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h)))))))
  · exact hh.2 g ((mem_hostedPaperKGatesCore_iff g).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h))))))))
  · exact hin g h
  · exact hstep g h
  · exact hh.2 g ((mem_hostedPaperKGatesCore_iff g).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
  · exact hh.2 g ((mem_hostedPaperKGatesCore_iff g).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))))))

/-! ### The two directions -/

/-- **Deployed ⇒ paper (core).**  Hypotheses: the deployed fold's collision exclusion (the twenty-
one folds must give back their forty sources) and an explicit base one-hot (needed only for the
`cons` dyck row and the aggregator, whose shapes differ from the deployed classes). -/
theorem deployed_to_paper (b : Basis (Fin 3) F K) (envF : Env F) (st : MState)
    (hone : BaseOneHot envF st)
    (hfold : FoldCollisionExcluded (gatherEnv b memoryCol0 envF))
    (hd : DeployedRow b envF)
    (hagg : (paperAggregator (F := F)).eval (gatherEnv b memoryCol0 envF) envF = 0) :
    HostedPaperRowCore b envF := by
  have hbind := bindings_of_deployed b envF hd
  obtain ⟨hbase, heq, hext, hmixed⟩ := hd
  rw [memorySourceTemplate_col0] at hext hmixed
  set envK := gatherEnv b memoryCol0 envF with henvK
  have hsrc : ∀ e ∈ extensionFoldSources (K := K), e.eval envK = 0 :=
    fold_to_source_of_collision_excluded envK (fun g hg => hext g (by simp [hg])) hfold
  have hmerged : ∀ q ∈ mergedCoreOrder,
      ((MemoryFactorizationScope.mergedGate (K := K) q).subst memorySubst).eval envK = 0 :=
    fun q hq => hsrc _ ((mem_extensionFoldSources_iff _).2 (Or.inr (Or.inl ⟨q, hq, rfl⟩)))
  have hclass : ∀ q ∈ paperClassIndices, (paperClassGate (F := F) (K := K) q).eval envK envF = 0 := by
    intro q hq
    rw [paperClassGate_eval_eq_deployed envK envF hbind.mirror]
    exact hmerged q (paperClassIndices_subset_mergedCoreOrder q hq)
  have hzinv : envK.chal 0 * envK.trace 30 = 1 := by
    have := hsrc _ ((mem_extensionFoldSources_iff _).2 (Or.inl rfl))
    simp only [zZinvExprM, Expr.subst, Expr.eval, memorySubst, chl, Reified.tc, extVar] at this
    norm_num [Expr.eval] at this
    exact sub_eq_zero.mp this
  have hwalkB : ∀ e ∈ walkBoundarySources, e.eval envK = 0 :=
    fun e he => hsrc e ((mem_extensionFoldSources_iff _).2 (Or.inr (Or.inr (Or.inl he))))
  have hwalkT : ∀ e ∈ walkLnCountTransitionSources, e.eval envK = 0 :=
    fun e he =>
      hsrc e ((mem_extensionFoldSources_iff _).2
        (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_append.mpr (Or.inl he)))))))
  have hsamp : ∀ e ∈ sampledFoldSources, e.eval envK = 0 :=
    fun e he => hsrc e ((mem_extensionFoldSources_iff _).2 (Or.inr (Or.inr (Or.inr (Or.inr he)))))
  have hs0 : (Expr.Sub (.Mul (extVar .traceCur 50) (extVar .traceCur 38)) (.Const 1)).eval envK
      = 0 := hsamp _ (by decide)
  have hs1 : (Expr.Mul (extVar .traceCur 39) (.Sub (extVar .traceCur 39) (.Const 1))).eval envK
      = 0 := hsamp _ (by decide)
  have hs2 : (Expr.Sub (extVar .traceCur 42) (.Mul (extVar .traceCur 39) (extVar .traceCur 38))).eval
      envK = 0 := hsamp _ (by decide)
  have hs4 : (Expr.Sub (extVar .traceCur 50)
      (.Add (.Mul (extVar .traceCur 39) (extVar .traceCur 37))
        (.Sub (.Const 1) (extVar .traceCur 39)))).eval envK = 0 := hsamp _ (by decide)
  have hs7 : (Expr.Mul (extVar .traceCur 47) (extVar .traceCur 43)).eval envK = 0 :=
    hsamp _ (by decide)
  have hs8 : (Expr.Mul (extVar .traceCur 48)
      (.Sub (extVar .traceCur 44) (extVar .traceCur 40))).eval envK = 0 := hsamp _ (by decide)
  -- the two IO base gates at the `𝕂` level
  have hacc : envK.trace 44 = envK.trace 43 + envK.trace 42 :=
    (accAfter_iff_coords b envF).2 fun k =>
      hbase _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨k, rfl⟩)))
  have hterm : (terminalRole (F := F)).eval envK envF = 0 :=
    (terminalRole_iff_coords b envF).2 fun k =>
      hbase _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨k, rfl⟩)))
  have hchain : (chainMixed (F := F)).eval envK envF = 0 :=
    hmixed chainMixed (by simp [foldedMixedTransitionGates])
  have haccChain : (accChainMixed (F := F)).eval envK envF = 0 :=
    hmixed accChainMixed (by simp [foldedMixedTransitionGates])
  have hpin : (denominatorPinMixed (F := F)).eval envK envF = 0 :=
    hmixed denominatorPinMixed (by simp [foldedMixedTransitionGates])
  have hlastAcc : (Expr.Mul (extVar .traceCur 48) (extVar .traceCur 33)).eval envK = 0 :=
    hext _ (by simp [foldedDegreeThreeEndpoints])
  refine ⟨?_, ?_⟩
  · intro g hg
    apply hbase
    rw [paperBaseGates_eq_prefix b] at hg
    exact List.mem_of_mem_take hg
  · intro g hg
    rcases (mem_hostedPaperKGatesCore_iff g).1 hg with ⟨q, hq, rfl⟩ | rfl | rfl | rfl | ⟨q, hq, rfl⟩
      | ⟨q, hq, rfl⟩ | rfl | hwalk | hwalk | rfl | rfl | hio
    · exact hclass q (by simp [paperClassIndices, hq])
    · exact (paperConsDyck_iff envK envF st hone hbind.mirror hzinv).2
        (hmerged 1 (by decide))
    · exact hclass 22 (by simp [paperClassIndices])
    · exact hagg
    · exact hclass q (by simp [paperClassIndices, hq])
    · exact hclass q (by simp [paperClassIndices, hq])
    · exact hchain
    · exact (hostedWalkInitGates_iff envK envF hbind.firstMask).2 hwalkB g hwalk
    · exact (hostedWalkStepGates_iff envK envF hbind.lastMask).2 hwalkT g hwalk
    · rw [hostedWalkAccStep_eval envK envF hbind.dequeueMask hbind.lastMask]
      exact hsrc walkAccStepHosted (by
        simp [extensionFoldSources, walkTransitionSources, walkLnCountTransitionSources])
    · exact (walkTerminal_iff envK envF hbind.lastMask).2 hlastAcc
    · simp only [ioCoreGates, List.mem_cons, List.not_mem_nil, or_false] at hio
      rcases hio with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [verBool, MixedExpr.eval, extVar, Expr.eval] using hs1
      · simpa [safeNormalisation, MixedExpr.eval, extVar, Expr.eval] using hs4
      · simpa [safeInverse, MixedExpr.eval, extVar, Expr.eval] using hs0
      · simpa [contribution, MixedExpr.eval, extVar, Expr.eval] using hs2
      · -- the single-column step from the deployed step and chain
        simp only [accChainMixed, MixedExpr.eval, bcur, CoeffExpr.eval] at haccChain
        simp only [accStep, MixedExpr.eval, bcur, CoeffExpr.eval]
        rw [hacc] at haccChain
        linear_combination -haccChain
      · simp only [accInit, MixedExpr.eval, bcur, CoeffExpr.eval, ← hbind.firstMask]
        simpa [extVar, Expr.eval] using hs7
      · simp only [accTerminal, MixedExpr.eval, bcur, CoeffExpr.eval, ← hbind.lastMask]
        simp only [extVar, Expr.eval] at hs8
        simp only [terminalRole, MixedExpr.eval, sub_eq_zero] at hterm
        rw [hacc, hterm] at hs8
        exact hs8
      · exact hterm
      · exact hpin

omit [FiniteDimensional F K] in
theorem mergedCoreOrder_lt {q : ℕ} (hq : q ∈ mergedCoreOrder) : q < 27 := by
  have := mergedCoreOrder_perm_range.mem_iff.1 hq
  simpa [List.mem_range] using this

section QtyNe
open Lean Meta Elab Tactic

/-- Close a raw-literal `n = m` with `n ≠ m`.  The equality is closed, so `decide` does not
see the section variable `K`. -/
def closeNatClash (g : MVarId) : MetaM Bool := g.withContext do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let some (_, lhs, rhs) := ty.eq? | continue
    let some n := (← whnf lhs).rawNatLit? | continue
    let some m := (← whnf rhs).rawNatLit? | continue
    if n == m then continue
    let notEq ← mkDecideProof (mkNot ty)
    g.assign (← mkAppM ``absurd #[mkFVar decl.fvarId, notEq])
    return true
  return false

def crushQtyGoal (g : MVarId) : TacticM Unit := do
  match ← injections g [] (maxDepth := 40) with
  | .solved => pure ()
  | .subgoal g' _ _ =>
    if ← closeNatClash g' then
      pure ()
    else
      let msg ← g'.withContext do
        match (← getLCtx).findFromUserName? `hQ with
        | none => pure m!"no hQ"
        | some decl => pure m!"{(toString (← ppExpr decl.type)).take 400}"
      throwError m!"qty_ne stuck: {msg}"

elab "qty_ne" : tactic => do
  evalTactic (← `(tactic| intro hQ))
  evalTactic (← `(tactic|
    dsimp [MemoryFactorizationScope.memQuantity, MemoryFactorizationScope.paddedBlock,
      MemoryFactorizationScope.blockDecompose, MemoryFactorizationScope.blockReadRoot,
      List.getD, getElem?, List.get?Internal, Option.getD, Expr.subst, memorySubst, extVar,
      mPt, mLc, mRc, mMem, fpCol, mrCol, mconsExpr, tc, chl, poleExpr, recRLCExpr,
      MemoryFactorizationScope.lamE, MemoryFactorizationScope.recC'] at hQ))
  crushQtyGoal (← getMainGoal)

end QtyNe

omit [FiniteDimensional F K] in
theorem mergedGate_subst_ne_23 {q : ℕ} (hq : q ∈ mergedCoreOrder) (hne : q ≠ 23) :
    (MemoryFactorizationScope.mergedGate (K := K) q).subst memorySubst ≠
      (MemoryFactorizationScope.mergedGate (K := K) 23).subst memorySubst := by
  have hlt := mergedCoreOrder_lt hq
  intro h
  simp only [MemoryFactorizationScope.mergedGate, gateByM, Expr.subst] at h
  injection h with hL _
  injection hL with _ hQ
  revert hQ
  interval_cases q <;> first
    | exact fun _ => (hne rfl).elim
    | qty_ne

omit [FiniteDimensional F K] in
theorem mergedGate_subst_ne_24 {q : ℕ} (hq : q ∈ mergedCoreOrder) (hne : q ≠ 24) :
    (MemoryFactorizationScope.mergedGate (K := K) q).subst memorySubst ≠
      (MemoryFactorizationScope.mergedGate (K := K) 24).subst memorySubst := by
  have hlt := mergedCoreOrder_lt hq
  intro h
  simp only [MemoryFactorizationScope.mergedGate, gateByM, Expr.subst] at h
  injection h with _ h1
  injection h1 with _ h2
  injection h2 with hR _
  injection hR with _ hQ
  revert hQ
  interval_cases q <;> first
    | exact fun _ => (hne rfl).elim
    | qty_ne

omit [FiniteDimensional F K] in
theorem walkBoundarySources_ne_agg {e : Expr} (he : e ∈ walkBoundarySources) :
    e ≠ (MemoryFactorizationScope.mergedGate (K := K) 23).subst memorySubst ∧
      e ≠ (MemoryFactorizationScope.mergedGate (K := K) 24).subst memorySubst := by
  simp only [walkBoundarySources, List.mem_map] at he
  obtain ⟨_, he0, rfl⟩ := he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he0
  rcases he0 with rfl | rfl | rfl <;>
    simp only [MemoryFactorizationScope.mergedGate, Expr.subst] <;>
    constructor <;> intro h <;> nomatch h

omit [FiniteDimensional F K] in
theorem walkTransitionSources_ne_agg {e : Expr} (he : e ∈ walkTransitionSources) :
    e ≠ (MemoryFactorizationScope.mergedGate (K := K) 23).subst memorySubst ∧
      e ≠ (MemoryFactorizationScope.mergedGate (K := K) 24).subst memorySubst := by
  simp only [walkTransitionSources, List.mem_append, List.mem_singleton] at he
  rcases he with he | rfl
  · simp only [walkLnCountTransitionSources, List.mem_map] at he
    obtain ⟨_, he0, rfl⟩ := he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he0
    rcases he0 with rfl | rfl <;>
      simp only [MemoryFactorizationScope.mergedGate, Expr.subst] <;>
      constructor <;> intro h <;> nomatch h
  · simp only [walkAccStepHosted, MemoryFactorizationScope.mergedGate, Expr.subst]
    constructor <;> intro h <;> (injection h with _ hR; nomatch hR)

omit [FiniteDimensional F K] in
theorem sampledFoldSources_ne_agg {e : Expr} (he : e ∈ sampledFoldSources) :
    e ≠ (MemoryFactorizationScope.mergedGate (K := K) 23).subst memorySubst ∧
      e ≠ (MemoryFactorizationScope.mergedGate (K := K) 24).subst memorySubst := by
  simp only [sampledFoldSources, sampledSources, List.get] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [MemoryFactorizationScope.mergedGate, Expr.subst] <;>
    constructor <;> intro h <;> nomatch h

/-- **Non-aggregator sources ⇒ paper core.**  Completeness after the W4 overlay:
classes `23`/`24` are not assumed to vanish; `paperAggregator` is supplied
separately from the sampled-role + PRL path. -/
theorem sources_except_aggregator_to_paper (b : Basis (Fin 3) F K) (envF : Env F)
    (st : MState) (hone : BaseOneHot envF st)
    (hbind : TreeOnlyBindings (gatherEnv b memoryCol0 envF) envF)
    (hbase : ∀ g ∈ foldedBaseTransitionGates b, g.eval envF = 0)
    (hmixed : ∀ g ∈ foldedMixedTransitionGates (F := F),
      g.eval (gatherEnv b memoryCol0 envF) envF = 0)
    (hsrc : ∀ e ∈ extensionFoldSources (K := K),
      e ≠ (MemoryFactorizationScope.mergedGate (K := K) 23).subst memorySubst →
      e ≠ (MemoryFactorizationScope.mergedGate (K := K) 24).subst memorySubst →
      e.eval (gatherEnv b memoryCol0 envF) = 0)
    (hextEnd : ∀ e ∈ degreeOneEndpoints ++ foldedDegreeThreeEndpoints,
      e.eval (gatherEnv b memoryCol0 envF) = 0)
    (hagg : (paperAggregator (F := F)).eval (gatherEnv b memoryCol0 envF) envF = 0) :
    HostedPaperRowCore b envF := by
  set envK := gatherEnv b memoryCol0 envF with henvK
  have hsrc' (e : Expr) (he : e ∈ extensionFoldSources (K := K))
      (h23 : e ≠ (MemoryFactorizationScope.mergedGate (K := K) 23).subst memorySubst)
      (h24 : e ≠ (MemoryFactorizationScope.mergedGate (K := K) 24).subst memorySubst) :
      e.eval envK = 0 := hsrc e he h23 h24
  have hmerged (q : ℕ) (hq : q ∈ mergedCoreOrder) (h23 : q ≠ 23) (h24 : q ≠ 24) :
      ((MemoryFactorizationScope.mergedGate (K := K) q).subst memorySubst).eval envK = 0 := by
    refine hsrc' _ ((mem_extensionFoldSources_iff _).2 (Or.inr (Or.inl ⟨q, hq, rfl⟩))) ?_ ?_
    · exact mergedGate_subst_ne_23 hq h23
    · exact mergedGate_subst_ne_24 hq h24
  have hclass : ∀ q ∈ paperClassIndices, (paperClassGate (F := F) (K := K) q).eval envK envF = 0 := by
    intro q hq
    rw [paperClassGate_eval_eq_deployed envK envF hbind.mirror]
    have h23 : q ≠ 23 := by
      simp [paperClassIndices, tabVMemClassIndices, baseTypedClassIndices,
        bottomPinIndices] at hq; omega
    have h24 : q ≠ 24 := by
      simp [paperClassIndices, tabVMemClassIndices, baseTypedClassIndices,
        bottomPinIndices] at hq; omega
    exact hmerged q (paperClassIndices_subset_mergedCoreOrder q hq) h23 h24
  have hzinv : envK.chal 0 * envK.trace 30 = 1 := by
    have := hsrc' _ ((mem_extensionFoldSources_iff _).2 (Or.inl rfl))
      (by
        simp only [zZinvExprM, MemoryFactorizationScope.mergedGate, Expr.subst]
        intro h; nomatch h)
      (by
        simp only [zZinvExprM, MemoryFactorizationScope.mergedGate, Expr.subst]
        intro h; nomatch h)
    simp only [zZinvExprM, Expr.subst, Expr.eval, memorySubst, chl, Reified.tc, extVar] at this
    norm_num [Expr.eval] at this
    exact sub_eq_zero.mp this
  have hwalkB : ∀ e ∈ walkBoundarySources, e.eval envK = 0 :=
    fun e he =>
      let hne := walkBoundarySources_ne_agg he
      hsrc' e ((mem_extensionFoldSources_iff _).2 (Or.inr (Or.inr (Or.inl he))))
        hne.1 hne.2
  have hwalkT : ∀ e ∈ walkLnCountTransitionSources, e.eval envK = 0 :=
    fun e he =>
      have htr : e ∈ walkTransitionSources :=
        List.mem_append.mpr (Or.inl he)
      let hne := walkTransitionSources_ne_agg htr
      hsrc' e ((mem_extensionFoldSources_iff _).2
        (Or.inr (Or.inr (Or.inr (Or.inl htr))))) hne.1 hne.2
  have hsamp : ∀ e ∈ sampledFoldSources, e.eval envK = 0 :=
    fun e he =>
      let hne := sampledFoldSources_ne_agg he
      hsrc' e ((mem_extensionFoldSources_iff _).2
        (Or.inr (Or.inr (Or.inr (Or.inr he))))) hne.1 hne.2
  have hs0 : (Expr.Sub (.Mul (extVar .traceCur 50) (extVar .traceCur 38)) (.Const 1)).eval envK
      = 0 := hsamp _ (by decide)
  have hs1 : (Expr.Mul (extVar .traceCur 39) (.Sub (extVar .traceCur 39) (.Const 1))).eval envK
      = 0 := hsamp _ (by decide)
  have hs2 : (Expr.Sub (extVar .traceCur 42) (.Mul (extVar .traceCur 39) (extVar .traceCur 38))).eval
      envK = 0 := hsamp _ (by decide)
  have hs4 : (Expr.Sub (extVar .traceCur 50)
      (.Add (.Mul (extVar .traceCur 39) (extVar .traceCur 37))
        (.Sub (.Const 1) (extVar .traceCur 39)))).eval envK = 0 := hsamp _ (by decide)
  have hs7 : (Expr.Mul (extVar .traceCur 47) (extVar .traceCur 43)).eval envK = 0 :=
    hsamp _ (by decide)
  have hs8 : (Expr.Mul (extVar .traceCur 48)
      (.Sub (extVar .traceCur 44) (extVar .traceCur 40))).eval envK = 0 := hsamp _ (by decide)
  have hacc : envK.trace 44 = envK.trace 43 + envK.trace 42 :=
    (accAfter_iff_coords b envF).2 fun k =>
      hbase _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨k, rfl⟩)))
  have hterm : (terminalRole (F := F)).eval envK envF = 0 :=
    (terminalRole_iff_coords b envF).2 fun k =>
      hbase _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨k, rfl⟩)))
  have hchain : (chainMixed (F := F)).eval envK envF = 0 :=
    hmixed chainMixed (by simp [foldedMixedTransitionGates])
  have haccChain : (accChainMixed (F := F)).eval envK envF = 0 :=
    hmixed accChainMixed (by simp [foldedMixedTransitionGates])
  have hpin : (denominatorPinMixed (F := F)).eval envK envF = 0 :=
    hmixed denominatorPinMixed (by simp [foldedMixedTransitionGates])
  have hlastAcc : (Expr.Mul (extVar .traceCur 48) (extVar .traceCur 33)).eval envK = 0 :=
    hextEnd _ (by simp [foldedDegreeThreeEndpoints])
  refine ⟨?_, ?_⟩
  · intro g hg
    apply hbase
    rw [paperBaseGates_eq_prefix b] at hg
    exact List.mem_of_mem_take hg
  · intro g hg
    rcases (mem_hostedPaperKGatesCore_iff g).1 hg with ⟨q, hq, rfl⟩ | rfl | rfl | rfl | ⟨q, hq, rfl⟩
      | ⟨q, hq, rfl⟩ | rfl | hwalk | hwalk | rfl | rfl | hio
    · exact hclass q (by simp [paperClassIndices, hq])
    · exact (paperConsDyck_iff envK envF st hone hbind.mirror hzinv).2
        (hmerged 1 (by decide) (by decide) (by decide))
    · exact hclass 22 (by simp [paperClassIndices])
    · exact hagg
    · exact hclass q (by simp [paperClassIndices, hq])
    · exact hclass q (by simp [paperClassIndices, hq])
    · exact hchain
    · exact (hostedWalkInitGates_iff envK envF hbind.firstMask).2 hwalkB g hwalk
    · exact (hostedWalkStepGates_iff envK envF hbind.lastMask).2 hwalkT g hwalk
    · rw [hostedWalkAccStep_eval envK envF hbind.dequeueMask hbind.lastMask]
      exact hsrc walkAccStepHosted (by
        simp [extensionFoldSources, walkTransitionSources, walkLnCountTransitionSources])
        (by
          simp only [walkAccStepHosted, MemoryFactorizationScope.mergedGate, Expr.subst]
          intro h; injection h with _ hR; nomatch hR)
        (by
          simp only [walkAccStepHosted, MemoryFactorizationScope.mergedGate, Expr.subst]
          intro h; injection h with _ hR; nomatch hR)
    · exact (walkTerminal_iff envK envF hbind.lastMask).2 hlastAcc
    · simp only [ioCoreGates, List.mem_cons, List.not_mem_nil, or_false] at hio
      rcases hio with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [verBool, MixedExpr.eval, extVar, Expr.eval] using hs1
      · simpa [safeNormalisation, MixedExpr.eval, extVar, Expr.eval] using hs4
      · simpa [safeInverse, MixedExpr.eval, extVar, Expr.eval] using hs0
      · simpa [contribution, MixedExpr.eval, extVar, Expr.eval] using hs2
      · simp only [accChainMixed, MixedExpr.eval, bcur, CoeffExpr.eval] at haccChain
        simp only [accStep, MixedExpr.eval, bcur, CoeffExpr.eval]
        rw [hacc] at haccChain
        linear_combination -haccChain
      · simp only [accInit, MixedExpr.eval, bcur, CoeffExpr.eval, ← hbind.firstMask]
        simpa [extVar, Expr.eval] using hs7
      · simp only [accTerminal, MixedExpr.eval, bcur, CoeffExpr.eval, ← hbind.lastMask]
        simp only [extVar, Expr.eval] at hs8
        simp only [terminalRole, MixedExpr.eval, sub_eq_zero] at hterm
        rw [hacc, hterm] at hs8
        exact hs8
      · exact hterm
      · exact hpin

/-- **Paper ⇒ deployed.**  Hypotheses: the base one-hot; the tree-only bindings; booleanity
of the preprocessing masks; the honest values of the unread columns; `pole ≠ 0`.  Since the `LU`
repair the hypothesis is the **full** paper row (`PaperRow`, with the two `intermediate` endpoint
gates): the deployed chip now commits `first · ipre` and `last · icur` through the mask mirrors,
so the converse needs them — previously it took `PaperRowCore` and got the two product-column
pins `46 = 0`, `49 = 0` from `DeadWitnessesHonest` instead. -/
theorem paper_to_deployed (b : Basis (Fin 3) F K) (envF : Env F) (st : MState)
    (hone : BaseOneHot envF st)
    (hbind : TreeOnlyBindings (gatherEnv b memoryCol0 envF) envF)
    (hmask : PreprocessingMasksBoolean envF)
    (hdead : DeadWitnessesHonest (gatherEnv b memoryCol0 envF) st)
    (hpole : poleSourceMixed.eval (gatherEnv b memoryCol0 envF) envF ≠ 0)
    (hpeq : (st = .read_root ∨ st = .verify_child) →
      (Expr.subst memorySubst poleExpr).eval (gatherEnv b memoryCol0 envF) =
        poleSourceMixed.eval (gatherEnv b memoryCol0 envF) envF)
    (hp : HostedPaperRow b envF) : DeployedRow b envF := by
  obtain ⟨hpb, hpkAll⟩ := hp
  have hpk : ∀ g ∈ hostedPaperKGatesCore (F := F) (K := K), g.eval (gatherEnv b memoryCol0 envF) envF = 0 :=
    fun g hg => hpkAll g (by simp [hostedPaperKGates, hg])
  have hiInit := hpkAll intermediateInit (by simp [hostedPaperKGates, hostedNewGates])
  have hiTerm := hpkAll intermediateTerminal (by simp [hostedPaperKGates, hostedNewGates])
  set envK := gatherEnv b memoryCol0 envF with henvK
  -- named paper gates
  have hclass : ∀ q ∈ paperClassIndices,
      ((MemoryFactorizationScope.mergedGate (K := K) q).subst memorySubst).eval envK = 0 := by
    intro q hq
    rw [← paperClassGate_eval_eq_deployed envK envF hbind.mirror]
    exact hpk _ (classGate_mem_hostedPaperKGatesCore q hq)
  have hmemIO : ∀ g ∈ ioCoreGates (F := F),
      g ∈ hostedPaperKGatesCore (F := F) (K := K) := fun g hg =>
    (mem_hostedPaperKGatesCore_iff g).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr hg)))))))))))
  have hcons := hpk (paperConsDyck (K := K)) ((mem_hostedPaperKGatesCore_iff _).2 (Or.inr (Or.inl rfl)))
  have hagg := hpk paperAggregator
    ((mem_hostedPaperKGatesCore_iff _).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hchain := hpk intermediateChain
    ((mem_hostedPaperKGatesCore_iff _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl rfl))))))))
  have hwalkI : ∀ g ∈ hostedWalkInitGates (F := F), g.eval envK envF = 0 := fun g hg =>
    hpk g ((mem_hostedPaperKGatesCore_iff _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl hg)))))))))
  have hwalkS : ∀ g ∈ hostedWalkStepGates (F := F), g.eval envK envF = 0 := fun g hg =>
    hpk g ((mem_hostedPaperKGatesCore_iff _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl hg))))))))))
  have hwalkT := hpk walkTerminal
    ((mem_hostedPaperKGatesCore_iff _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))
  have hver := hpk verBool (hmemIO _ (by simp [ioCoreGates]))
  have hsafe := hpk safeNormalisation (hmemIO _ (by simp [ioCoreGates]))
  have hinv := hpk safeInverse (hmemIO _ (by simp [ioCoreGates]))
  have hcontrib := hpk contribution (hmemIO _ (by simp [ioCoreGates]))
  have hstep := hpk accStep (hmemIO _ (by simp [ioCoreGates]))
  have hinit := hpk accInit (hmemIO _ (by simp [ioCoreGates]))
  have hterm := hpk accTerminal (hmemIO _ (by simp [ioCoreGates]))
  have hrole := hpk terminalRole (hmemIO _ (by simp [ioCoreGates]))
  have hpin := hpk denominatorPin (hmemIO _ (by simp [ioCoreGates]))
  have hmerged : ∀ q ∈ mergedCoreOrder,
      ((MemoryFactorizationScope.mergedGate (K := K) q).subst memorySubst).eval envK = 0 := by
    intro q hq
    rcases class_partition q hq with h | rfl | rfl | rfl
    · exact hclass q h
    · exact (paperConsDyck_iff envK envF st hone hbind.mirror hdead.zinv).1 hcons
    · exact (deployed_aggregator_of_paper envK envF st hone hbind.mirror hpole hdead.logUpRead
        hdead.logUpVerify hpeq hagg).1
    · exact (deployed_aggregator_of_paper envK envF st hone hbind.mirror hpole hdead.logUpRead
        hdead.logUpVerify hpeq hagg).2
  have hmaskK1 : envK.trace 47 * (envK.trace 47 - 1) = 0 := by
    rw [hbind.firstMask]
    exact extension_mask_boolean_derived _ _ rfl hmask.first
  have hmaskK2 : envK.trace 48 * (envK.trace 48 - 1) = 0 := by
    rw [hbind.lastMask]
    exact extension_mask_boolean_derived _ _ rfl hmask.last
  have hsrc : ∀ e ∈ extensionFoldSources (K := K), e.eval envK = 0 := by
    intro e he
    rcases (mem_extensionFoldSources_iff e).1 he with rfl | ⟨q, hq, rfl⟩ | h | h | h
    · simp only [zZinvExprM, Expr.subst, Expr.eval, memorySubst, chl, Reified.tc, extVar]
      norm_num [Expr.eval]
      exact sub_eq_zero.mpr hdead.zinv
    · exact hmerged q hq
    · exact (hostedWalkInitGates_iff envK envF hbind.firstMask).1 hwalkI e h
    · rcases List.mem_append.mp h with hln | hacc
      · exact (hostedWalkStepGates_iff envK envF hbind.lastMask).1 hwalkS e hln
      · simp only [List.mem_singleton] at hacc
        subst e
        have haccG := hpk hostedWalkAccStep
          ((mem_hostedPaperKGatesCore_iff _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
        exact (hostedWalkAccStep_eval envK envF hbind.dequeueMask hbind.lastMask).symm.trans haccG
    · simp only [sampledFoldSources, sampledSources, List.get_eq_getElem, List.getElem_cons_zero,
        List.getElem_cons_succ, List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [terminalRole, MixedExpr.eval, sub_eq_zero] at hrole
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [safeInverse, MixedExpr.eval, extVar, Expr.eval] using hinv
      · simpa [verBool, MixedExpr.eval, extVar, Expr.eval] using hver
      · simpa [contribution, MixedExpr.eval, extVar, Expr.eval] using hcontrib
      · simpa [safeNormalisation, MixedExpr.eval, extVar, Expr.eval] using hsafe
      · simp only [accInit, MixedExpr.eval, bcur, CoeffExpr.eval, ← hbind.firstMask] at hinit
        simpa [extVar, Expr.eval] using hinit
      · simp only [accTerminal, MixedExpr.eval, bcur, CoeffExpr.eval, ← hbind.lastMask] at hterm
        simp only [extVar, Expr.eval]
        rw [hdead.accAfter, hrole]
        exact hterm
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- eleven base gates
    intro g hg
    simp only [foldedBaseTransitionGates, semanticBaseTail, List.mem_append, List.mem_ofFn] at hg
    rcases hg with hg | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact hpb g hg
    · exact (terminalRole_iff_coords b envF).1 hrole k
    · exact (accAfter_iff_coords b envF).1 hdead.accAfter k
  · exact (equalityChecks_iff_mirror b envF).2 hbind.mirror
  · rw [memorySourceTemplate_col0, ← henvK]
    intro g hg
    simp only [List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact source_to_fold_complete envK hsrc g hg
    · simp only [degreeOneEndpoints, List.not_mem_nil] at hg
    · simp only [foldedDegreeThreeEndpoints, intermediateInitGate, intermediateTerminalGate,
        List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · simpa [extVar, Expr.eval] using hdead.forestInitResidual
      · exact (walkTerminal_iff envK envF hbind.lastMask).1 hwalkT
      · -- `first · ipre` through the first-mask binding `47 = first`
        simp only [intermediateInit, MixedExpr.eval, bcur, CoeffExpr.eval, ← hbind.firstMask]
          at hiInit
        simpa [extVar, Expr.eval] using hiInit
      · -- `last · icur` through the last-mask binding `48 = last`
        simp only [intermediateTerminal, MixedExpr.eval, bcur, CoeffExpr.eval, ← hbind.lastMask]
          at hiTerm
        simpa [extVar, Expr.eval] using hiTerm
  · rw [memorySourceTemplate_col0, ← henvK]
    intro g hg
    simp only [foldedMixedTransitionGates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [firstMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval, hbind.firstMask]
    · simp [lastMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval, hbind.lastMask]
    · exact hchain
    · simp only [accChainMixed, MixedExpr.eval, bcur, CoeffExpr.eval]
      simp only [accStep, MixedExpr.eval, bcur, CoeffExpr.eval] at hstep
      rw [hdead.accAfter]
      linear_combination -hstep
    · exact hpin
    · simp [dequeueMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval, hbind.dequeueMask]

/-- **Deployed ⇒ the FULL paper set**.  The core
by `deployed_to_paper`; the two `intermediate` endpoint gates by the committed
`intermediateInitGate`/`intermediateTerminalGate` read through the mask bindings.  Previously this needed `DeadPinsHonest` (`46 = 47 · 27`, `49 = 48 · 28` — the honest values of
two columns the chip pinned to `0` and never bound) and was called
`deployed_and_honest_pins_to_paper`. -/
theorem deployed_to_paperRow (b : Basis (Fin 3) F K) (envF : Env F) (st : MState)
    (hone : BaseOneHot envF st)
    (hfold : FoldCollisionExcluded (gatherEnv b memoryCol0 envF))
    (hd : DeployedRow b envF)
    (hagg : (paperAggregator (F := F)).eval (gatherEnv b memoryCol0 envF) envF = 0) :
    HostedPaperRow b envF := by
  have hcore := deployed_to_paper b envF st hone hfold hd hagg
  have hbind := bindings_of_deployed b envF hd
  obtain ⟨-, -, hext, -⟩ := hd
  rw [memorySourceTemplate_col0] at hext
  set envK := gatherEnv b memoryCol0 envF with henvK
  refine ⟨hcore.1, fun g hg => ?_⟩
  rw [← henvK]
  simp only [hostedPaperKGates, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hcore.2 g hg
  · simp only [hostedNewGates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · have h := hext intermediateInitGate (List.mem_append_right _ intermediateInitGate_mem)
      simp only [intermediateInitGate, extVar, Expr.eval, hbind.firstMask] at h
      simpa [intermediateInit, MixedExpr.eval, bcur, CoeffExpr.eval] using h
    · have h := hext intermediateTerminalGate (List.mem_append_right _ intermediateTerminalGate_mem)
      simp only [intermediateTerminalGate, extVar, Expr.eval, hbind.lastMask] at h
      simpa [intermediateTerminal, MixedExpr.eval, bcur, CoeffExpr.eval] using h

/-- **Exactness.**  The deployed row language is the **full** paper set together with the
tree-only bindings (the paper core only, until the `LU` repair).  Left-to-right needs the fold's
collision exclusion (the deployed folds are involved); right-to-left needs the mask booleanity,
the honest unread columns and `pole ≠ 0`; both need the base one-hot. -/
theorem deployed_iff_paper (b : Basis (Fin 3) F K) (envF : Env F) (st : MState)
    (hone : BaseOneHot envF st)
    (hfold : FoldCollisionExcluded (gatherEnv b memoryCol0 envF))
    (hmask : PreprocessingMasksBoolean envF)
    (hdead : DeadWitnessesHonest (gatherEnv b memoryCol0 envF) st)
    (hagg : (paperAggregator (F := F)).eval (gatherEnv b memoryCol0 envF) envF = 0)
    (hpole : poleSourceMixed.eval (gatherEnv b memoryCol0 envF) envF ≠ 0)
    (hpeq : (st = .read_root ∨ st = .verify_child) →
      (Expr.subst memorySubst poleExpr).eval (gatherEnv b memoryCol0 envF) =
        poleSourceMixed.eval (gatherEnv b memoryCol0 envF) envF) :
    DeployedRow b envF ↔
      TreeOnlyBindings (gatherEnv b memoryCol0 envF) envF ∧ HostedPaperRow b envF :=
  ⟨fun hd => ⟨bindings_of_deployed b envF hd,
      deployed_to_paperRow b envF st hone hfold hd hagg⟩,
   fun ⟨hbind, hp⟩ => paper_to_deployed b envF st hone hbind hmask hdead hpole hpeq hp⟩

omit [FiniteDimensional F K] in
/-- **The paper core ⟺ the tree's per-state gated equations** (`Nock.Reified.memPerStateGated`),
through `MemoryFactorizationScope.mergedMemCore_iff_perStateGated`: the twenty-four
`paperClassGate`s together with `paperConsDyck` and `paperAggregator` cut out, at a one-hot state
with honest `zinv`/`g` and `pole ≠ 0`, exactly the per-state block `memoryAIR` transcribes. -/
theorem paperCore_iff_perStateGated (envK : Env K) (envF : Env F) (st : MState)
    (hone : BaseOneHot envF st) (hb : MirrorBound envK envF)
    (hzinv : envK.chal 0 * envK.trace 30 = 1)
    (hread : st = .read_root → envK.trace 29 = envK.trace 28 - envK.trace 27)
    (hverify : st = .verify_child → envK.trace 29 = envK.trace 27 - envK.trace 28)
    (hpole : poleSourceMixed.eval envK envF ≠ 0)
    (hpeq : (st = .read_root ∨ st = .verify_child) →
      (Expr.subst memorySubst poleExpr).eval envK = poleSourceMixed.eval envK envF) :
    ((∀ q ∈ paperClassIndices, (paperClassGate (F := F) (K := K) q).eval envK envF = 0) ∧
      (paperConsDyck (F := F) (K := K)).eval envK envF = 0 ∧
      (paperAggregator (F := F)).eval envK envF = 0) ↔
      ∀ e ∈ memPerStateGated (K := K), e.eval (Env.ofSubst memorySubst envK) = 0 := by
  rw [← mergedMemoryCore_subst_iff_perStateGated envK st (selectorOneHot_of_base envK envF st hone hb)]
  simp only [mergedMemoryCore, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · rintro ⟨hclass, hcons, hagg⟩ q hq
    rcases class_partition q hq with h | rfl | rfl | rfl
    · rw [← paperClassGate_eval_eq_deployed envK envF hb]; exact hclass q h
    · exact (paperConsDyck_iff envK envF st hone hb hzinv).1 hcons
    · exact (deployed_aggregator_of_paper envK envF st hone hb hpole hread hverify hpeq hagg).1
    · exact (deployed_aggregator_of_paper envK envF st hone hb hpole hread hverify hpeq hagg).2
  · intro h
    refine ⟨fun q hq => ?_, ?_, ?_⟩
    · rw [paperClassGate_eval_eq_deployed envK envF hb]
      exact h q (paperClassIndices_subset_mergedCoreOrder q hq)
    · exact (paperConsDyck_iff envK envF st hone hb hzinv).2 (h 1 (by decide))
    · have hone' := selectorOneHot_of_base envK envF st hone hb
      have h23 := h 23 (by decide)
      have h24 := h 24 (by decide)
      rw [mergedGate_subst_eval envK st hone' 23] at h23
      rw [mergedGate_subst_eval envK st hone' 24] at h24
      rw [paperAggregator_eval envK envF st hone]
      cases st
      · rw [memQuantity_23_decompose] at h23
        simp only [Expr.subst, Expr.eval, memorySubst, Reified.tc, extVar, aggregatorSign] at h23 ⊢
        norm_num [Expr.eval] at h23
        rw [h23, mul_zero, sub_zero]
      · rw [memQuantity_23_halt] at h23
        simp only [Expr.subst, Expr.eval, memorySubst, Reified.tc, extVar, aggregatorSign] at h23 ⊢
        norm_num [Expr.eval] at h23
        rw [h23, mul_zero, sub_zero]
      · have hpe := hpeq (Or.inl rfl)
        rw [memQuantity_23_read] at h23
        rw [memQuantity_24_read] at h24
        simp only [Expr.subst, Expr.eval, memorySubst, Reified.tc, extVar, aggregatorSign] at h23 h24 ⊢
        norm_num [Expr.eval] at h23 h24
        rw [hpe] at h24
        linear_combination h24 + (poleSourceMixed.eval envK envF) * h23
      · have hpe := hpeq (Or.inr rfl)
        rw [memQuantity_23_verify] at h23
        rw [memQuantity_24_verify] at h24
        simp only [Expr.subst, Expr.eval, memorySubst, Reified.tc, extVar, aggregatorSign] at h23 h24 ⊢
        norm_num [Expr.eval] at h23 h24
        rw [hpe] at h24
        linear_combination -h24 + (poleSourceMixed.eval envK envF) * h23

/-- The base one-hot is derivable from the five State-Variables gates under the characteristic
hypothesis the P8 layer already carries (`MemoryTable.oneHot_of_bool_sum`; three ones sum to one
in characteristic `2`). -/
theorem baseOneHot_of_paperBaseGates (envF : Env F)
    (hchar : ∀ n : ℕ, n ≤ 4 → (n : F) = 1 → n = 1)
    (h : ∀ g ∈ paperBaseGates (F := F), g.eval envF = 0) :
    ∃ st, BaseOneHot envF st := by
  have hb : ∀ j : MState, envF.trace (mopCol j) = 0 ∨ envF.trace (mopCol j) = 1 := by
    intro j
    have := h (bbool (bcur (mopCol j))) (by cases j <;> simp [paperBaseGates, mopCol])
    simp only [bbool, bcur, CoeffExpr.eval, mul_eq_zero, sub_eq_zero] at this
    exact this
  have hsum : MemoryTable.sum4 (fun j => envF.trace (mopCol j)) = 1 := by
    have := h (bsum4 .traceCur) (by simp [paperBaseGates])
    simp only [bsum4, CoeffExpr.eval, sub_eq_zero] at this
    simpa [MemoryTable.sum4, mopCol, add_assoc] using this
  obtain ⟨s, hs⟩ := MemoryTable.oneHot_of_bool_sum _ hchar hb hsum
  refine ⟨s, fun j => ?_⟩
  have := congrFun hs j
  exact this

/-! ## §5  Counts

The paper prices the memory chip's transition bucket at `24·e + 16`, a
zero-slack sum of `RAP_mem` `20·e + 13` (`:1434`), the walk's `2 + 2·e` (`:981`) and `e` (`:983`),
and `RAP_mem-IO`'s `1` (`:655`) and `e` (`:656`) — i.e. **24 `𝕂` gates and 16 base gates**
(`MemoryFactorizationScope.paper_memory_typing_split`); its endpoint buckets are `2·e` degree-`1`
(`:1487`) and `2·e` degree-`3` (`:1488`), i.e. **4 `𝕂` gates**, with "Four equality checks"
(`:1489`).  This set has **45 `𝕂` gates and 5 base gates**, and the discrepancy is itemised in
`count_comparison` rather than folded away:

| block | here | paper | where the difference comes from |
|---|---|---|---|
| `RAP_mem` core (`tabVMem` 17 + `timestamp` + aggregator) | 19 `𝕂` | 20 `𝕂` (`:1434`) | no `z⁻¹` witness (`:1226`) |
| `baseTypedClassGates` | 3 `𝕂` | 3 of the base 13 (`:1434`) | layout: `axis`/child-state are `𝕂` roles |
| `bottomPins` | 4 `𝕂` | 0 (no `tab:v_mem` row) | `Algorithm:Memspec` `:2064`/`:2071`/`:2079` kept |
| `intermediateChain` | 1 `𝕂` | 0 (implicit, `:2037`) | the tree's two-row witness needs a gate |
| walk | 7 `𝕂` | 2 base + 3 `𝕂` transition (`:981`, `:983`) + 2 `𝕂` deg-1 + 1 `𝕂` deg-3 endpoints (`:988-989`) | masks turn the endpoints into gates; `ln`/`count` steps are `𝕂` here |
| IO core | 9 `𝕂` | 1 base + 1 `𝕂` (`:655-656`) + 1 `𝕂` deg-3 endpoint (`:670`) | the tree's column factorisation of the denominator, including its pin (A-mem-2, `:577-579`); anchors (`LL`/`LN`) |
| `newGates` | 2 `𝕂` | unpriced (`:1431` endpoints) | this module §6 |
| State-Variables | 5 base | 5 of the base 13 (`:2130-2131`) | — |

The paper's remaining base gates (`13 − 5 − 3 = 5`, plus the walk's `2` and IO's `1`) have no
counterpart here: `MemoryFactorizationScope.base_thirteen_underdetermined` records that the text
does not itemise them. -/

theorem paper_gate_counts :
    (paperKGates (F := F) (K := K)).length = 49 ∧
    (paperKGatesCore (F := F) (K := K)).length = 43 ∧
    (paperBaseGates (F := F)).length = 5 ∧
    (rapMemGates (F := F) (K := K)).length = 19 ∧
    (tabVMemGates (F := F) (K := K)).length = 17 ∧
    (baseTypedClassGates (F := F) (K := K)).length = 3 ∧
    (bottomPins (F := F) (K := K)).length = 4 ∧
    (walkGates (F := F)).length = 7 ∧
    (ioCoreGates (F := F)).length = 9 ∧
    (newGates (F := F)).length = 4 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The paper's numerals, re-derived, against this set's, in the same unit (`𝕂` gates / base gates).  The set is
**not** `24·e + 16`: `45·e + 5` in the transition-plus-endpoint bucket at any `e`, i.e. `140` at
`e = 3` against the paper's `88 + 12 = 100`.  The `RAP_mem` core alone is `19` against `20`. -/
theorem count_comparison :
    MemoryFactorizationScope.papMemoryKGates = 24 ∧
    MemoryFactorizationScope.papMemoryFGates = 16 ∧
    (paperKGates (F := F) (K := K)).length = 49 ∧
    (paperBaseGates (F := F)).length = 5 ∧
    (rapMemGates (F := F) (K := K)).length + 1 = 20 ∧
    (∀ e, (paperKGates (F := F) (K := K)).length * e + (paperBaseGates (F := F)).length = 49 * e + 5) ∧
    (49 * 3 + 5 = 152 ∧ Thm54Resources.memoryTransitionGatesPaper 3 + 2 * 3 + 2 * 3 = 100) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun e => rfl, by decide, by decide⟩

/-- The pre-W2 (folded) chip: `11` base, `12` equality, `21 + 0 + 4` `𝕂`, `5` mixed.
The committed chip is `paperBaseGates` / `paperKGates` (`memorySourceTemplate_shape`). -/
theorem folded_counts (b : Basis (Fin 3) F K) :
    (foldedBaseTransitionGates b).length = 11 ∧ (foldedEqualityChecks b).length = 12 ∧
      (extensionTransitionGates (K := K)).length = 21 ∧ (foldedMixedTransitionGates (F := F)).length = 6 :=
  ⟨foldedBaseTransitionGates_length b, foldedEqualityChecks_length b, extensionTransitionGates_length,
    foldedMixedTransitionGates_length⟩

/-- The committed chip after W2: `5` base, no equality, no fold, `47` mixed. -/
theorem deployed_counts (b : Basis (Fin 3) F K) :
    (baseTransitionGates b).length = 6 ∧ (equalityChecks b).length = 0 ∧
      (memorySourceTemplate b).extTransition.length = 0 ∧
      (mixedTransitionGates (F := F) (K := K) b).length = 50 :=
  ⟨baseTransitionGates_length b, equalityChecks_length b, rfl,
    mixedTransitionGates_length b⟩

omit [FiniteDimensional F K] in
/-- The committed base-field form: `45 · 3 = 135` coordinate gates plus `5` base gates. -/
theorem expanded_counts (b : Basis (Fin 3) F K) :
    (mixedExpandList b memoryCol0 (paperKGates (F := F) (K := K))).length = 147 := by
  rw [length_mixedExpandList]; rfl

/-! ## §6  The gates the deployed set does not imply (row language) — NONE since the `LU` repair

Each statement here is at the level of the deployed row language — the fifty `transitionSources`,
the four endpoint gates and the five mixed gates evaluated at a `𝕂` environment.  Stage 1 exhibited three paper gates the deployed set did not imply, each by a one-row modification
keeping every deployed gate at `0` while moving the paper gate.  All three are implied now:
* the denominator pin since A-mem-2 committed it — `deployed_implies_denominatorPin`;
* the two `intermediate` endpoints since the
  `LU` repair committed `first · ipre`/`last · icur` — `deployed_implies_intermediateInit/Terminal`.
The shift instruments (`shiftIntermediate`, `deltaSource_shift`, …) are kept: they now show the
repair is exactly two gates wide (`shift_moves_only_the_intermediate_endpoints`). -/

section NotImplied

/-- The five pre-W2 mixed gates, as a basis-free list (`foldedMixedTransitionGates`). -/
def deployedMixedGates : List (MixedExpr F) :=
  [firstMaskMixed, lastMaskMixed, chainMixed, accChainMixed, denominatorPinMixed,
    dequeueMaskMixed]

omit [FiniteDimensional F K] in
theorem deployedMixedGates_eq :
    deployedMixedGates (F := F) = foldedMixedTransitionGates (F := F) := rfl

/-- The pre-W2 row language at the `𝕂` level: the fifty sources, the four endpoint gates and
the five mixed gates. -/
def DeployedRowK (envK : Env K) (envF : Env F) : Prop :=
  (∀ e ∈ transitionSources (K := K), e.eval envK = 0) ∧
  (∀ e ∈ degreeOneEndpoints ++ foldedDegreeThreeEndpoints, e.eval envK = 0) ∧
  (∀ g ∈ deployedMixedGates (F := F), g.eval envK envF = 0)

/-! ### (a) The denominator pin — IMPLIED since A-mem-2 -/

/-- The one deployed **source** that reads role `37`: the inactive-safe normalisation. -/
def safeSource : Expr :=
  .Sub (extVar .traceCur 50)
    (.Add (.Mul (extVar .traceCur 39) (extVar .traceCur 37)) (.Sub (.Const 1) (extVar .traceCur 39)))

omit [FiniteDimensional F K] in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
/-- Of the fifty deployed **sources** exactly one reads the denominator role `37`
(`Batch270.role37_read_only_by_safe_normalisation`, re-measured here).  Unchanged by A-mem-2 —
the pin is a *mixed* gate, not a source; the second reader of role `37` is `denominatorPinMixed` in
`deployedMixedGates` (`denominatorPin_mem_deployedMixedGates`), and it is what stage 1's
`deployed_does_not_imply_denominatorPin` said was missing. -/
theorem role37_readers :
    (transitionSources (K := K)).filter (fun e => decide ((VarKind.traceCur, 37) ∈ exprVariableSupport e))
      = [safeSource] := by
  reduce_decide

omit [FiniteDimensional F K] in
/-- The committed reader of role `37` beyond the safe normalisation: the denominator pin is a
member of the deployed mixed bucket. -/
theorem denominatorPin_mem_deployedMixedGates :
    (denominatorPin (F := F)) ∈ deployedMixedGates (F := F) := by
  simp [deployedMixedGates]

omit [FiniteDimensional F K] in
/-- **The deployed row language implies the denominator pin** (A-mem-2).  Stage 1's
`deployed_does_not_imply_denominatorPin` — at any `ver = 0` row, moving role `37` by `δ`
preserved every deployed gate and moved the pin by `δ` — is unstatable now: the pin *is* a
deployed gate, so moving role `37` moves a deployed gate. -/
theorem deployed_implies_denominatorPin (envK : Env K) (envF : Env F)
    (hd : DeployedRowK envK envF) :
    (denominatorPin (F := F)).eval envK envF = 0 :=
  hd.2.2 _ denominatorPin_mem_deployedMixedGates

omit [FiniteDimensional F K] in
/-- The same, at the value level: on any deployed row, role `37` **is** `pole + RLC^γ(record)`
. -/
theorem deployed_role37_eq (envK : Env K) (envF : Env F) (hd : DeployedRowK envK envF) :
    envK.trace 37 = envK.chal 5 + (recordRLCExpr.eval envK +
      algebraMap F K (envF.trace reqIdxCol) * envK.chal 4 ^ 9) := by
  have h := deployed_implies_denominatorPin envK envF hd
  simp only [denominatorPin, denominatorPinMixed, recordRLC, reqIdxRLCTerm, bcur, MixedExpr.eval,
    MixedExpr.ofExpr_eval, CoeffExpr.eval, sub_eq_zero] at h
  exact h

/-! ### (b), (c) The `intermediate` endpoints -/

/-- Shift `ipre`, `icur` at the current row and `ipre` at the next row by `δ`. -/
def shiftIntermediate (env : Env K) (δ : K) : Env K where
  trace q := if q = 27 ∨ q = 28 then env.trace q + δ else env.trace q
  traceNext q := if q = 27 then env.traceNext q + δ else env.traceNext q
  chal := env.chal
  pub := env.pub

/-- Shift `ipre`, `icur` at the current row only. -/
def shiftIntermediateCur (env : Env K) (δ : K) : Env K where
  trace q := if q = 27 ∨ q = 28 then env.trace q + δ else env.trace q
  traceNext := env.traceNext
  chal := env.chal
  pub := env.pub

/-- The deployed `Δ intermediate` class source. -/
def deltaSource : Expr := (MemoryFactorizationScope.mergedGate (K := K) 23).subst memorySubst

omit [FiniteDimensional F K] in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
/-- Exactly two deployed sources read `ipre`/`icur` (roles `27`/`28`, current or next row): the
`Δ intermediate` class and the chain. -/
theorem intermediate_readers :
    (transitionSources (K := K)).filter (fun e => decide ((VarKind.traceCur, 27) ∈ exprVariableSupport e ∨
        (VarKind.traceCur, 28) ∈ exprVariableSupport e ∨
        (VarKind.traceNext, 27) ∈ exprVariableSupport e))
      = [deltaSource (K := K), memoryChainSource] := by
  reduce_decide

theorem deltaSource_shift (env : Env K) (δ : K) :
    (deltaSource (K := K)).eval (shiftIntermediate env δ) = (deltaSource (K := K)).eval env := by
  simp only [deltaSource, MemoryFactorizationScope.mergedGate, gateByM, mopCol,
    memQuantity_23_decompose, memQuantity_23_halt, memQuantity_23_read, memQuantity_23_verify,
    Expr.subst, Expr.eval, memorySubst, Reified.tc, extVar]
  norm_num [Expr.eval, shiftIntermediate]

theorem deltaSource_shiftCur (env : Env K) (δ : K) :
    (deltaSource (K := K)).eval (shiftIntermediateCur env δ) = (deltaSource (K := K)).eval env := by
  simp only [deltaSource, MemoryFactorizationScope.mergedGate, gateByM, mopCol,
    memQuantity_23_decompose, memQuantity_23_halt, memQuantity_23_read, memQuantity_23_verify,
    Expr.subst, Expr.eval, memorySubst, Reified.tc, extVar]
  norm_num [Expr.eval, shiftIntermediateCur]

theorem eval_shiftIntermediate_of_off (env : Env K) (δ : K) (e : Expr)
    (h27 : (VarKind.traceCur, 27) ∉ exprVariableSupport e)
    (h28 : (VarKind.traceCur, 28) ∉ exprVariableSupport e)
    (hn27 : (VarKind.traceNext, 27) ∉ exprVariableSupport e) :
    e.eval (shiftIntermediate env δ) = e.eval env := by
  apply eval_eq_of_support_agree
  rintro ⟨k, i⟩ hv
  cases k
  · have : i ≠ 27 := fun h => h27 (by subst h; exact hv)
    have : i ≠ 28 := fun h => h28 (by subst h; exact hv)
    simp_all [envAt, shiftIntermediate]
  · have : i ≠ 27 := fun h => hn27 (by subst h; exact hv)
    simp_all [envAt, shiftIntermediate]
  · rfl
  · rfl

theorem eval_shiftIntermediateCur_of_off (env : Env K) (δ : K) (e : Expr)
    (h27 : (VarKind.traceCur, 27) ∉ exprVariableSupport e)
    (h28 : (VarKind.traceCur, 28) ∉ exprVariableSupport e) :
    e.eval (shiftIntermediateCur env δ) = e.eval env := by
  apply eval_eq_of_support_agree
  rintro ⟨k, i⟩ hv
  cases k
  · have : i ≠ 27 := fun h => h27 (by subst h; exact hv)
    have : i ≠ 28 := fun h => h28 (by subst h; exact hv)
    simp_all [envAt, shiftIntermediateCur]
  · rfl
  · rfl
  · rfl

omit [FiniteDimensional F K] in
/-- **Exactly two of the four endpoint gates read `ipre`/`icur`: the two `intermediate` anchors**
(positive control of the reader instrument; previously this list was empty). -/
theorem intermediate_endpoint_readers :
    (degreeOneEndpoints ++ foldedDegreeThreeEndpoints).filter
        (fun e => decide ((VarKind.traceCur, 27) ∈ exprVariableSupport e ∨
          (VarKind.traceCur, 28) ∈ exprVariableSupport e ∨
          (VarKind.traceNext, 27) ∈ exprVariableSupport e))
      = [intermediateInitGate, intermediateTerminalGate] := by
  decide

omit [FiniteDimensional F K] in
/-- **The deployed row language implies `first · ipre = 0`**.
The committed `intermediateInitGate = role 47 · role 27` vanishes and `firstMaskMixed` binds
role `47` to the first-row mask (base column `4`), so `first · ipre = 0`.  Previously this
was `deployed_does_not_imply_intermediateInit`: shifting `ipre`, `icur` (and the next row's
`ipre`) by `δ` kept every deployed gate at `0` while `intermediateInit` moved by `first · δ`,
because the chip pinned the product column `46` and read `ipre` against no mask.  Read the
negative there. -/
theorem deployed_implies_intermediateInit (envK : Env K) (envF : Env F)
    (hd : DeployedRowK envK envF) :
    (intermediateInit (F := F)).eval envK envF = 0 := by
  obtain ⟨-, hend, hmixed⟩ := hd
  have h := hend intermediateInitGate (List.mem_append_right _ intermediateInitGate_mem)
  have h47 := hmixed firstMaskMixed (by simp [deployedMixedGates])
  simp only [firstMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval, sub_eq_zero] at h47
  simp only [intermediateInitGate, extVar, Expr.eval, h47] at h
  simpa [intermediateInit, MixedExpr.eval, bcur, CoeffExpr.eval] using h

omit [FiniteDimensional F K] in
/-- **The deployed row language implies `last · icur = 0`**, the
same way through `intermediateTerminalGate = role 48 · role 28` and `lastMaskMixed`.  Previously this was `deployed_does_not_imply_intermediateTerminal` (at a last row, shifting
`ipre`, `icur` by `δ` kept every deployed gate at `0` while `intermediateTerminal` moved by
`δ`). -/
theorem deployed_implies_intermediateTerminal (envK : Env K) (envF : Env F)
    (hd : DeployedRowK envK envF) :
    (intermediateTerminal (F := F)).eval envK envF = 0 := by
  obtain ⟨-, hend, hmixed⟩ := hd
  have h := hend intermediateTerminalGate (List.mem_append_right _ intermediateTerminalGate_mem)
  have h48 := hmixed lastMaskMixed (by simp [deployedMixedGates])
  simp only [lastMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval, sub_eq_zero] at h48
  simp only [intermediateTerminalGate, extVar, Expr.eval, h48] at h
  simpa [intermediateTerminal, MixedExpr.eval, bcur, CoeffExpr.eval] using h

omit [FiniteDimensional F K] in
/-- The value form at a first row: `ipre = 0`. -/
theorem deployed_first_row_ipre (envK : Env K) (envF : Env F)
    (hd : DeployedRowK envK envF) (hb4 : envF.trace 4 = 1) : envK.trace 27 = 0 := by
  have h := deployed_implies_intermediateInit envK envF hd
  simpa [intermediateInit, MixedExpr.eval, bcur, CoeffExpr.eval, hb4] using h

omit [FiniteDimensional F K] in
/-- The value form at a last row: `icur = 0`. -/
theorem deployed_last_row_icur (envK : Env K) (envF : Env F)
    (hd : DeployedRowK envK envF) (hb5 : envF.trace 5 = 1) : envK.trace 28 = 0 := by
  have h := deployed_implies_intermediateTerminal envK envF hd
  simpa [intermediateTerminal, MixedExpr.eval, bcur, CoeffExpr.eval, hb5] using h

omit [FiniteDimensional F K] in
/-- **The repair is exactly two gates wide.**  Under `shiftIntermediate` every deployed source
and every deployed mixed gate still vanishes and the two forest endpoints are blind — only the two
`intermediate` anchors move, by `first · δ` and `last · δ` (through the mask mirrors).  This is
the proof body of the former non-implication, re-read as a measurement of what the repair added. -/
theorem shift_moves_only_the_intermediate_endpoints (envK : Env K) (envF : Env F)
    (hd : DeployedRowK envK envF) (δ : K) :
    (∀ e ∈ transitionSources (K := K), e.eval (shiftIntermediate envK δ) = 0) ∧
    (∀ g ∈ deployedMixedGates (F := F), g.eval (shiftIntermediate envK δ) envF = 0) ∧
    (∀ e ∈ degreeOneEndpoints ++ foldedDegreeThreeEndpoints, e ≠ intermediateInitGate →
      e ≠ intermediateTerminalGate → e.eval (shiftIntermediate envK δ) = 0) ∧
    intermediateInitGate.eval (shiftIntermediate envK δ) = envK.trace 47 * δ ∧
    intermediateTerminalGate.eval (shiftIntermediate envK δ) = envK.trace 48 * δ := by
  obtain ⟨hsrc, hend, hmixed⟩ := hd
  have hI := hend intermediateInitGate (List.mem_append_right _ intermediateInitGate_mem)
  have hT := hend intermediateTerminalGate (List.mem_append_right _ intermediateTerminalGate_mem)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    by_cases hr : (VarKind.traceCur, 27) ∈ exprVariableSupport e ∨
        (VarKind.traceCur, 28) ∈ exprVariableSupport e ∨
        (VarKind.traceNext, 27) ∈ exprVariableSupport e
    · have hmem : e ∈ transitionSources (K := K).filter
          (fun e => decide ((VarKind.traceCur, 27) ∈ exprVariableSupport e ∨
            (VarKind.traceCur, 28) ∈ exprVariableSupport e ∨
            (VarKind.traceNext, 27) ∈ exprVariableSupport e)) :=
        List.mem_filter.mpr ⟨he, by simpa using hr⟩
      rw [intermediate_readers] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · rw [deltaSource_shift]; exact hsrc _ he
      · have := hsrc _ he
        simp only [memoryChainSource, notLastE, lastE, Trans.icurChainExpr, Reified.tc, Trans.tn,
          Expr.subst, Expr.eval, memoryChainSubst, extVar] at this ⊢
        simp [Expr.eval, shiftIntermediate, -mul_eq_zero] at this ⊢
        linear_combination this
    · push Not at hr
      rw [eval_shiftIntermediate_of_off envK δ e hr.1 hr.2.1 hr.2.2]
      exact hsrc e he
  · intro g hg
    have := hmixed g hg
    simp only [deployedMixedGates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [firstMaskMixed, MixedExpr.eval, shiftIntermediate] using this
    · simpa [lastMaskMixed, MixedExpr.eval, shiftIntermediate] using this
    · simp only [chainMixed, MixedExpr.eval, bcur, CoeffExpr.eval, shiftIntermediate] at this ⊢
      simp [-mul_eq_zero] at this ⊢
      linear_combination this
    · simpa [accChainMixed, MixedExpr.eval, shiftIntermediate] using this
    · simpa [denominatorPinMixed, recordRLC, recordRLCExpr, reqIdxRLCTerm, MixedExpr.eval,
        MixedExpr.ofExpr_eval, Expr.eval, shiftIntermediate] using this
    · simpa [dequeueMaskMixed, MixedExpr.eval, shiftIntermediate] using this
  · intro e he hne1 hne2
    have := hend e he
    simp only [degreeOneEndpoints, foldedDegreeThreeEndpoints, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · simpa [extVar, Expr.eval, shiftIntermediate] using this
    · simpa [extVar, Expr.eval, shiftIntermediate] using this
    · exact absurd rfl hne1
    · exact absurd rfl hne2
  · simp only [intermediateInitGate, extVar, Expr.eval] at hI ⊢
    simp [shiftIntermediate, mul_add, hI]
  · simp only [intermediateTerminalGate, extVar, Expr.eval] at hT ⊢
    simp [shiftIntermediate, mul_add, hT]

omit [FiniteDimensional F K] in
/-- **At a first row (`role 47 = 1`) the shifted row is REJECTED for every `δ ≠ 0`** — the row-
language form of `Batch272.repaired_chip_rejects_intermediate_shift`. -/
theorem shift_rejected_at_first_row (envK : Env K) (envF : Env F)
    (hd : DeployedRowK envK envF) (h47 : envK.trace 47 = 1) (δ : K) (hδ : δ ≠ 0) :
    ¬ DeployedRowK (shiftIntermediate envK δ) envF := by
  intro hd'
  have h := hd'.2.1 intermediateInitGate (List.mem_append_right _ intermediateInitGate_mem)
  rw [(shift_moves_only_the_intermediate_endpoints envK envF hd δ).2.2.2.1, h47, one_mul] at h
  exact hδ h

end NotImplied



omit [Field F] [FiniteDimensional F K] in
/-- A base-selector-summed gate costs one degree over its bodies (`Scale (bcur j)` adds `1`). -/
theorem selScale_degree_le (f : MState → Expr) (d : ℕ) (h : ∀ st, (f st).degree ≤ d) :
    (selScale (F := F) f).degree ≤ 1 + d := by
  have h0 := h .decompose
  have h1 := h .halt
  have h2 := h .read_root
  have h3 := h .verify_child
  simp only [selScale, MixedExpr.degree, MixedExpr.ofExpr_degree, bcur, CoeffExpr.degree]
  omega

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
/-- Every committed class body has degree `≤ 3` at every state.  `degree_le` reduces
`Expr.powDegree` on a degree-0 challenge base without reading `pwScaleExp K`. -/
theorem classBodies_degree :
    ∀ q ∈ paperClassIndices, ∀ st : MState,
      ((memQuantity (K := K) st q).subst memorySubst).degree ≤ 3 := by
  intro q hq st
  have hlt : q < 27 := mergedCoreOrder_lt (paperClassIndices_subset_mergedCoreOrder q hq)
  interval_cases q <;> cases st <;> first
    | exact absurd hq (by decide)
    | degree_le

set_option maxHeartbeats 4000000 in
theorem consBodies_degree :
    ∀ st : MState, ((consDyckQuantity (K := K) st).subst memorySubst).degree ≤ 3 := by
  intro st
  cases st <;> degree_le

omit [Field F] [FiniteDimensional F K] in
theorem paperClassGate_degree (q : ℕ) (hq : q ∈ paperClassIndices) :
    (paperClassGate (F := F) (K := K) q).degree ≤ 4 :=
  selScale_degree_le _ 3 (classBodies_degree q hq)

omit [Field F] [FiniteDimensional F K] in
/-- The `cons` dyck row is the tight cell: degree exactly `4` (`3 + 1`). -/
theorem paperConsDyck_degree : (paperConsDyck (F := F) (K := K)).degree ≤ 4 :=
  selScale_degree_le _ 3 consBodies_degree

omit [Field F] [FiniteDimensional F K] in
theorem paperAggregator_degree : (paperAggregator (F := F)).degree = 2 := rfl

omit [Field F] [FiniteDimensional F K] in
theorem denominatorPin_degree : (denominatorPin (F := F)).degree = 1 := rfl

set_option maxRecDepth 100000 in
/-- **Every paper `𝕂` gate has degree `≤ 4`**; the tight cell is the `cons` dyck row (`3 + 1`).
    The in-gate acc step is the degree-4 split `dequeueMask·ln·RLC + notLast·(Δacc − count·cc)`. -/
theorem paperKGates_degree : ∀ g ∈ paperKGates (F := F) (K := K), g.degree ≤ 4 := by
  intro g hg
  simp only [paperKGates, List.mem_append] at hg
  rcases hg with hfront | hqueue
  · rcases hfront with hcore | hend
    · rcases (mem_paperKGatesCore_iff g).1 hcore with ⟨q, hq, rfl⟩ | rfl | rfl | rfl | ⟨q, hq, rfl⟩
        | ⟨q, hq, rfl⟩ | rfl | hwalk | hwalk | rfl | hio
      · exact paperClassGate_degree q (by simp [paperClassIndices, hq])
      · exact paperConsDyck_degree
      · exact paperClassGate_degree 22 (by simp [paperClassIndices])
      · rw [paperAggregator_degree]; omega
      · exact paperClassGate_degree q (by simp [paperClassIndices, hq])
      · exact paperClassGate_degree q (by simp [paperClassIndices, hq])
      · rw [show (intermediateChain (F := F)).degree = 2 from rfl]; omega
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
      · show (walkTerminal (F := F)).degree ≤ 4
        rw [show (walkTerminal (F := F)).degree = 2 from rfl]; omega
      · simp only [ioCoreGates, List.mem_cons, List.not_mem_nil, or_false] at hio
        rcases hio with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [show (verBool (F := F)).degree = 2 from rfl]; omega
        · rw [show (safeNormalisation (F := F)).degree = 2 from rfl]; omega
        · rw [show (safeInverse (F := F)).degree = 2 from rfl]; omega
        · rw [show (contribution (F := F)).degree = 2 from rfl]; omega
        · rw [show (accStep (F := F)).degree = 2 from rfl]; omega
        · rw [show (accInit (F := F)).degree = 2 from rfl]; omega
        · rw [show (accTerminal (F := F)).degree = 2 from rfl]; omega
        · rw [show (terminalRole (F := F)).degree = 1 from rfl]; omega
        · rw [denominatorPin_degree]; omega
    · simp only [newGates, List.mem_cons, List.not_mem_nil, or_false] at hend
      rcases hend with rfl | rfl | rfl | rfl
      · rw [show (intermediateInit (F := F)).degree = 2 from rfl]; omega
      · rw [show (intermediateTerminal (F := F)).degree = 2 from rfl]; omega
      · rw [show (OptimizedMemoryGateBasis.rootMaskCountsGate (F := F)).degree = 2 from rfl]; omega
      · rw [show (OptimizedMemoryGateBasis.rootMaskIndicatorGate (F := F)).degree = 2 from rfl]; omega
  · simp only [MemoryWalkLabel.queueWitnessGates, List.mem_cons, List.not_mem_nil,
      or_false] at hqueue
    rcases hqueue with rfl | rfl
    · exact MemoryWalkLabel.walkQueueNonEmpty_degree
    · exact MemoryWalkLabel.walkQueueTiling_degree

omit [FiniteDimensional F K] in
theorem paperBaseGates_degree : ∀ g ∈ paperBaseGates (F := F), g.degree ≤ 2 := by
  intro g hg
  simp only [paperBaseGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;>
    simp [bbool, bcur, bsum4, CoeffExpr.degree]

/-- Compiled to the deployed layout, the `135` coordinate gates keep degree `≤ 4`
(`MixedCoordinateCompiler.degree_mixedExpandList_le`). -/
theorem expanded_degree (b : Basis (Fin 3) F K) :
    ∀ u ∈ mixedExpandList b memoryCol0 (paperKGates (F := F) (K := K)), u.degree ≤ 4 :=
  degree_mixedExpandList_le b memoryCol0 _ 4 paperKGates_degree

/-! ## §8  Canonical satisfaction: the honest canonical memory trace satisfies every gate -/

section Canonical
set_option maxHeartbeats 8000000

open OptimizedMemoryCanonicalSatisfaction
open OptimizedMemoryCanonicalTrace
open OptimizedMemorySemanticRealization
open OptimizedMemoryCodec
open OptimizedMemoryCoreInventory
open OptimizedMemorySameExecution
open OptimizedMemoryRAP
open MonolithicRAP

variable [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p] {R : PlusIOSegmentedFamily F K}

/-- **The honest values of the two memory coin slots the denominator pin reads**: slot `4` is
the sampled `γ`, slot `5` the sampled `pole` (`FiniteIO.IOCoins`).  Stated in the shape of
`ExactMemoryCoordinatePins` — and since A-mem-2 **carried by it** (`sampledGamma`/`sampledPole`,
discharged by `BuildableChips.memoryCoordinatePins` from `memoryChallengeTargets | 4 | 5`), so
`HonestSampledCoinSlots.ofPins` supplies it. -/
structure HonestSampledCoinSlots (A : SampledIOSameExecutionAssignment R p)
    (b : Basis (Fin 3) F K) (chalVal : ℕ → F) : Prop where
  gamma : (∑ k : Fin 3, chalVal (6 + 3 * 4 + (k : ℕ)) • b k) = A.sampled.coins.gamma
  pole : (∑ k : Fin 3, chalVal (6 + 3 * 5 + (k : ℕ)) • b k) = A.sampled.coins.pole

/-- The coin slots are part of the package's coordinate pins since A-mem-2. -/
theorem HonestSampledCoinSlots.ofPins {A : SampledIOSameExecutionAssignment R p}
    {b : Basis (Fin 3) F K} {chalVal pubVal : ℕ → F}
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal) : HonestSampledCoinSlots A b chalVal :=
  ⟨pins.sampledGamma, pins.sampledPole⟩

variable (A : SampledIOSameExecutionAssignment R p) {execA : ExactExecution R.problem.cfg}
  (P : MemoryProductionAssignment A execA)
  (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
  (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
  {h : ℕ} (orbit : StrictOrbitDomain F 3 h)

theorem canonical_gathered_eq (i : Fin R.problem.cfg.memRows) :
    gatherEnv b memoryCol0 (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) =
      canonicalGatheredEnv A nodes b chalVal pubVal orbit i := rfl

include P hnodes

-- DeployedRow completeness is not claimed after the 27/28 overlay: fold
-- sources `23`/`24` do not vanish.  Committed completeness is `canonical_paperRow`.

omit P in
theorem canonical_baseOneHot (i : Fin R.problem.cfg.memRows) :
    BaseOneHot (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i)
      (R.problem.exec.memoryPubAt i).st := by
  intro j
  have hj : mopCol j < 6 := by cases j <;> simp [mopCol]
  have := canonical_base_current A nodes hnodes b chalVal pubVal orbit i ⟨mopCol j, hj⟩
  rw [this]
  simp only [encodedRowAt, encode, encodeBase, semanticRowAt, stateSelector, stateIndex]
  generalize (R.problem.exec.memoryPubAt i).st = s
  cases j <;> cases s <;> simp [mopCol]

omit P in
/-- Canonical nine-slot `poleSource` is `compress` of the row's `mem_record` at sampled
`(ioGamma, interPole)`. -/
theorem poleSource_eval_eq_compress9
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (i : Fin R.problem.cfg.memRows) :
    poleSource.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i) =
      FiniteIO.compress A.interCoins
        (NockVM.encRecC (R.problem.exec.memoryRowAt i).2.2.mem
          (R.problem.exec.memoryRowAt i).2.2.cprime) := by
  set envK := canonicalGatheredEnv A nodes b chalVal pubVal orbit i
  have hγ : envK.chal 4 = A.sampled.coins.gamma := by
    change (∑ k : Fin 3, chalVal (6 + 3 * 4 + (k : ℕ)) • b k) = A.sampled.coins.gamma
    exact pins.sampledGamma
  have hpole6 : envK.chal 6 = A.interPole := by
    change (∑ k : Fin 3, chalVal (6 + 3 * 6 + (k : ℕ)) • b k) = A.interPole
    exact pins.sampledInterPole
  have hrole : ∀ c : ℕ, c < 8 →
      envK.trace (19 + c) = (exactMemoryRowEnv A i).trace (23 + c) := by
    intro c hc
    have := canonical_table_role A nodes hnodes b chalVal pubVal orbit pins i (23 + c)
      (by omega) (by omega) (by omega)
    simp [envK]
    convert this using 2
    omega
  have r0 := hrole 0 (by norm_num)
  have r1 := hrole 1 (by norm_num)
  have r2 := hrole 2 (by norm_num)
  have r3 := hrole 3 (by norm_num)
  have r4 := hrole 4 (by norm_num)
  have r5 := hrole 5 (by norm_num)
  have r6 := hrole 6 (by norm_num)
  have r7 := hrole 7 (by norm_num)
  have r57 : envK.trace 57 = (R.problem.exec.memoryPubAt i).cprime :=
    canonical_gather_cprime A nodes hnodes b chalVal pubVal orbit i
  simp [poleSource, recordRLCExpr, Expr.eval, FiniteIO.compress,
    SampledIOSameExecutionAssignment.interCoins, Walk.rlc, Fin.sum_univ_succ,
    NockVM.encRecC, ExactExecution.memoryPubAt,
    exactMemoryRowEnv, memoryEnvFull, hγ, hpole6, r0, r1, r2, r3, r4, r5, r6, r7,
    r57]
  ring

omit P in
/-- **The 31st:** canonical `poleSourceMixed` is `compress` of the row's honest ten-slot record
(`rowRecord10`: the record plus `reqIdx`) at sampled `(ioGamma, interPole)`. -/
theorem poleSource_eval_eq_compress
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (i : Fin R.problem.cfg.memRows) :
    poleSourceMixed.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) =
      FiniteIO.compress A.interCoins (rowRecord10 R i) := by
  have hγ : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).chal 4 =
      A.sampled.coins.gamma := by
    change (∑ k : Fin 3, chalVal (6 + 3 * 4 + (k : ℕ)) • b k) = A.sampled.coins.gamma
    exact pins.sampledGamma
  have r181 := canonical_physical_reqIdx A nodes hnodes b chalVal pubVal orbit i
  have h9 := poleSource_eval_eq_compress9 A nodes hnodes b chalVal pubVal orbit pins i
  simp only [poleSourceMixed, reqIdxRLCTerm, reqIdxCol, bcur, MixedExpr.eval,
    MixedExpr.ofExpr_eval, CoeffExpr.eval, Expr.eval, r181, hγ, h9]
  simp only [rowRecord10, FiniteIO.compress, RecordCarrier.rlc_withExp, honestReqIdx,
    map_natCast, SampledIOSameExecutionAssignment.interCoins, ExactExecution.memoryPubAt]
  ring

omit P in
/-- Twin of `memoryDenominatorsSafe_of_sampled`: every honest row has a nonzero
internal compress, or the aggregator is inactive. -/
theorem hdenAll_of_interPoleHitGood
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (hhon : ∀ row ∈ R.problem.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : R.problem.exec.CprimeCoherent)
    (i : Fin R.problem.cfg.memRows) :
    poleSourceMixed.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) ≠ 0 ∨
      aggregatorSign (R.problem.exec.memoryPubAt i).st = (0 : K) := by
  set st := (R.problem.exec.memoryPubAt i).st
  cases hst : st with
  | read_root =>
    refine Or.inl ?_
    rw [poleSource_eval_eq_compress A nodes hnodes b chalVal pubVal orbit pins i,
      rowRecord10_of_active R i (Or.inl hst)]
    intro hzero
    apply A.interPoleHitGood10
    simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨RecordCarrier.extRec R.problem.exec.derivedRequestIO
        (NockVM.encRecC (R.problem.exec.memoryPubAt i).mem
        (R.problem.exec.memoryPubAt i).cprime), ?_, ?_⟩
    · refine List.mem_append_right _ (List.mem_map.mpr ⟨_, ?_, rfl⟩)
      rw [ExactExecution.derivedResponseIO_eq_memoryRows, List.mem_flatMap]
      refine ⟨R.problem.exec.memoryRowAt i, ExactExecution.memoryRowAt_mem _ i, ?_⟩
      have hv := hhon _ (ExactExecution.memoryRowAt_mem _ i)
      have hst' : (R.problem.exec.memoryRowAt i).2.2.st = MState.read_root := by
        rw [← ExactExecution.memoryPubAt]
        exact hst
      have hver : (R.problem.exec.memoryRowAt i).2.2.ver = true := by
        rw [hst'] at hv
        have hdec : decide (MState.read_root = MState.read_root) = true := by decide
        rw [hdec] at hv
        exact hv
      simp [hver, ExactExecution.memoryPubAt]
    · simpa [FiniteIO.compress, SampledIOSameExecutionAssignment.interCoins,
        ExactExecution.memoryPubAt] using hzero
  | verify_child =>
    refine Or.inl ?_
    rw [poleSource_eval_eq_compress A nodes hnodes b chalVal pubVal orbit pins i,
      rowRecord10_of_active R i (Or.inr hst)]
    intro hzero
    apply A.interPoleHitGood10
    simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨RecordCarrier.extRec R.problem.exec.derivedRequestIO
        (NockVM.encRecC (R.problem.exec.memoryPubAt i).mem
        (R.problem.exec.memoryPubAt i).cprime), ?_, ?_⟩
    · refine List.mem_append_left _ (List.mem_map.mpr ⟨_, ?_, rfl⟩)
      rw [List.mem_map]
      refine ⟨(R.problem.exec.memoryPubAt i).mem,
        RowLayout.mem_consumedRecordList_of_verify_child R.problem.exec i hst, ?_⟩
      have hc : (R.problem.exec.memoryPubAt i).cprime =
          R.problem.exec.cprimeOf (R.problem.exec.memoryPubAt i).mem :=
        ExactExecution.cprime_eq_cprimeOf hC _ (ExactExecution.memoryRowAt_mem _ i)
      rw [hc]
    · simpa [FiniteIO.compress, SampledIOSameExecutionAssignment.interCoins,
        ExactExecution.memoryPubAt] using hzero
  | _ =>
    exact Or.inr (by simp [aggregatorSign, hst])

omit P in
/-- **Lemma 6.**  The paper aggregator holds on every canonical row at the sampled
`(ioGamma, interPole)`.  Roles `27`/`28` are the overlay
`interResidentAcc` at the honest ten-slot compression `A.interCompress10`; `poleSourceMixed` is
slot `6` + `recordRLC` at slot `4` (with the 31st's `reqIdx` slot).
`hden` is the F-A-1 / `IOPoleHitEvent` exclusion at those coins. -/
theorem canonical_paperAggregator
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (hC : R.problem.exec.CprimeCoherent)
    (i : Fin R.problem.cfg.memRows)
    (hden : poleSourceMixed.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) ≠ 0 ∨
      aggregatorSign (R.problem.exec.memoryPubAt i).st = (0 : K)) :
    (paperAggregator (F := F)).eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  set envK := canonicalGatheredEnv A nodes b chalVal pubVal orbit i
  set envF := canonicalPhysicalEnv A nodes b chalVal pubVal orbit i
  set st := (R.problem.exec.memoryPubAt i).st
  have hone := canonical_baseOneHot A nodes hnodes b chalVal pubVal orbit i
  have hlen : (i : ℕ) < R.problem.exec.memoryRows.length := by
    simpa [R.problem.exec.memoryRows_length] using i.isLt
  have hipre := canonical_ipre A nodes hnodes b chalVal pubVal orbit i
  have hicur := canonical_icur A nodes hnodes b chalVal pubVal orbit i
  have hrow : R.problem.exec.memoryRows[(i : ℕ)] = R.problem.exec.memoryRowAt i := by
    simp [ExactExecution.memoryRowAt, List.get_eq_getElem]
  have hΔ :
      envK.trace 28 - envK.trace 27 =
        RowLayout.interRowTerm A.interCompress10 (R.problem.exec.memoryRowAt i) := by
    rw [hipre, hicur, RowLayout.interResidentAcc_succ _ _ hlen, hrow]
    simp [envK]
  have hsel :
      RowLayout.interSelector (R.problem.exec.memoryRowAt i) = aggregatorSign st := by
    have hst : (R.problem.exec.memoryRowAt i).2.2.st = st := rfl
    simp only [RowLayout.interSelector, aggregatorSign, hst]
    cases st <;> simp
  have hpm := poleSource_eval_eq_compress A nodes hnodes b chalVal pubVal orbit pins i
  rw [paperAggregator_eval envK envF st hone, hΔ]
  simp only [RowLayout.interRowTerm, hsel]
  by_cases hact : st = .read_root ∨ st = .verify_child
  · have hcomp : A.interCompress10
        (NockVM.encRecC (R.problem.exec.memoryRowAt i).2.2.mem
          (R.problem.exec.memoryRowAt i).2.2.cprime) = poleSourceMixed.eval envK envF := by
      rw [hpm, rowRecord10_of_active R i hact]
      rfl
    rcases hden with hne | h0
    · rw [← hcomp] at hne
      rw [← hcomp, mul_left_comm, mul_inv_cancel₀ hne, mul_one, sub_self]
    · have h00 : aggregatorSign (st) = (0 : K) := h0
      rw [h00]
      ring
  · have h00 : aggregatorSign st = (0 : K) := by
      cases hs : st <;> simp_all [aggregatorSign]
    rw [h00]
    ring

/-- **The paper core holds on every canonical row** — off DeployedRow, from
non-aggregator sources + `canonical_paperAggregator` (sampled-role + PRL). -/
theorem canonical_paperRowCore
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (halign : MemoryOrbitAligned nodes orbit) (hsafe : MemoryDenominatorsSafe A)
    (hprl : RowLayout.PairedRecordLayout R.problem.exec)
    (hhon : ∀ row ∈ R.problem.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hlam : ∀ i : Fin R.problem.cfg.memRows,
      (R.problem.exec.memoryPubAt i).lambda =
        (R.problem.exec.memoryPubAt ⟨0, R.problem.cfg.memRows_pos⟩).lambda)
    (hC : R.problem.exec.CprimeCoherent)
    (i : Fin R.problem.cfg.memRows)
    (hden : poleSourceMixed.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) ≠ 0 ∨
      aggregatorSign (R.problem.exec.memoryPubAt i).st = (0 : K)) :
    PaperRowCore b (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) := by
  let envF := canonicalPhysicalEnv A nodes b chalVal pubVal orbit i
  have heq := canonical_selectorEqualityChecks A nodes hnodes b chalVal pubVal orbit i
  have hmixed := canonical_mixedTransitionGates A P nodes hnodes b chalVal pubVal orbit
    pins halign i
  have hbind : TreeOnlyBindings (gatherEnv b memoryCol0 envF) envF := by
    refine ⟨(equalityChecks_iff_mirror b envF).1 ?_, ?_, ?_, ?_⟩
    · simpa [envF] using heq
    · have := hmixed firstMaskMixed (by simp [foldedMixedTransitionGates])
      simpa [firstMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval, sub_eq_zero,
        memorySourceTemplate_col0, envF] using this
    · have := hmixed lastMaskMixed (by simp [foldedMixedTransitionGates])
      simpa [lastMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval, sub_eq_zero,
        memorySourceTemplate_col0, envF] using this
    · have := hmixed dequeueMaskMixed (by simp [foldedMixedTransitionGates])
      simpa [dequeueMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval, sub_eq_zero,
        memorySourceTemplate_col0, envF] using this
  refine paperRowCore_of_hosted b envF ?_ ?_
  swap
  · -- H1.W memory: the four in-gate walk gates, from the walk certificate at the `x^mem` label
    intro g hg
    simpa [envF, canonical_gathered_eq] using
      MemoryWalkLabelCanonical.canonical_inGateWalkGates A nodes hnodes b chalVal pubVal orbit
        P pins halign i g hg
  refine sources_except_aggregator_to_paper b envF
    (R.problem.exec.memoryPubAt i).st
    (canonical_baseOneHot A nodes hnodes b chalVal pubVal orbit i) hbind
    (canonical_baseTransitionGates A P nodes hnodes b chalVal pubVal orbit pins
      halign hsafe i)
    (by
      intro g hg
      simpa [envF, memorySourceTemplate_col0] using hmixed g hg)
    (fun e he h23 h24 => by
      have htr := extensionFoldSources_subset_transitionSources e he
      simpa [envF, canonical_gathered_eq] using
        canonical_transitionSources A P hlam nodes hnodes b chalVal pubVal orbit
          pins halign hsafe i e htr h23 h24)
    (fun e he => by
      have hend := canonical_endpointSources A P nodes hnodes b chalVal pubVal orbit
        pins hprl hhon hC i
      rcases List.mem_append.mp he with h1 | h3
      · simpa [envF, canonical_gathered_eq] using hend.1 e h1
      · simpa [envF, canonical_gathered_eq] using hend.2 e h3)
    (by
      simpa [envF, canonical_gathered_eq] using
        canonical_paperAggregator A nodes hnodes b chalVal pubVal orbit pins hC i hden)

omit P in
theorem canonical_base4 (i : Fin R.problem.cfg.memRows) :
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 4 = firstMask i := by
  have := canonical_base_current A nodes hnodes b chalVal pubVal orbit i (4 : Fin 6)
  simpa [encodedRowAt, encode, encodeBase, semanticRowAt] using this

omit P in
theorem canonical_base5 (i : Fin R.problem.cfg.memRows) :
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 5 = lastMask i := by
  have := canonical_base_current A nodes hnodes b chalVal pubVal orbit i (5 : Fin 6)
  simpa [encodedRowAt, encode, encodeBase, semanticRowAt] using this

omit P in
/-- `first · ipre = 0` on canonical rows. -/
theorem canonical_intermediateInit
    (i : Fin R.problem.cfg.memRows) :
    (intermediateInit (F := F)).eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  simp only [intermediateInit, MixedExpr.eval, bcur, CoeffExpr.eval,
    canonical_base4 A nodes hnodes b chalVal pubVal orbit i]
  rw [canonical_ipre A nodes hnodes b chalVal pubVal orbit i]
  by_cases hi0 : (i : ℕ) = 0
  · have hi : i = ⟨0, R.problem.cfg.memRows_pos⟩ := Fin.ext hi0
    subst hi
    simp [firstMask, RowLayout.interResidentAcc_zero]
  · simp [firstMask, hi0]

omit P in
/-- `last · icur = 0` on canonical rows. -/
theorem canonical_intermediateTerminal
    (hprl : RowLayout.PairedRecordLayout R.problem.exec)
    (hhon : ∀ row ∈ R.problem.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : R.problem.exec.CprimeCoherent)
    (i : Fin R.problem.cfg.memRows) :
    (intermediateTerminal (F := F)).eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  simp only [intermediateTerminal, MixedExpr.eval, bcur, CoeffExpr.eval,
    canonical_base5 A nodes hnodes b chalVal pubVal orbit i]
  rw [canonical_icur A nodes hnodes b chalVal pubVal orbit i]
  by_cases hilast : (i : ℕ) + 1 = R.problem.cfg.memRows
  · have hlen : (i : ℕ) + 1 = R.problem.exec.memoryRows.length := by
      simpa [R.problem.exec.memoryRows_length] using hilast
    simp only [lastMask, hilast, ↓reduceIte, algebraMap.coe_one, one_mul]
    have hlen' : R.problem.cfg.memRows = R.problem.exec.memoryRows.length :=
      hilast.symm.trans hlen
    rw [hlen']
    exact RowLayout.interResidentAcc_last_of_paired _ _ hprl hC
  · simp [lastMask, hilast]

theorem canonical_rootMaskCounts
    (hmore : ∀ i : Fin R.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < R.problem.cfg.kMem →
        (R.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (R.problem.exec.memoryPubAt i).pt.indicator = 0)
    (i : Fin R.problem.cfg.memRows) :
    (OptimizedMemoryGateBasis.rootMaskCountsGate (F := F)).eval
      (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  have hmask :
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 153 =
        if (i : ℕ) < R.problem.cfg.kMem then 1 else 0 := by
    simp only [canonicalPhysicalEnv, envOfTrace]
    rw [dif_pos (by decide : (153 : ℕ) < 182)]
    rw [canonicalSourceTrace_root_fixed]
    exact rootRowMask_eval nodes R.problem.cfg.kMem hnodes i
  have hcnt :
      (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 4 =
        (exactMemoryRowEnv A i).trace 8 := by
    have h := canonical_gather_table_current A nodes hnodes b chalVal pubVal orbit i
      (.inl ⟨4, by decide⟩)
    simpa [extensionEquiv_apply, extensionIndex, memoryTableSourceColumn] using h
  have hcnt' :
      (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 4 =
        (R.problem.exec.memoryPubAt i).pt.counts := by
    rw [hcnt]
    simp [exactMemoryRowEnv, memoryEnvFull]
  simp only [OptimizedMemoryGateBasis.rootMaskCountsGate, MixedExpr.eval,
    OptimizedMemoryGateBasis.rootMask, bcur, CoeffExpr.eval,
    OptimizedMemoryGateBasis.rootMaskCol]
  rw [hmask, hcnt']
  by_cases hi : (i : ℕ) < R.problem.cfg.kMem
  · by_cases h0 : (i : ℕ) = 0
    · simp [hi, (P.rootPubZero i h0).1]
    · simp [hi, (hmore i (Nat.pos_of_ne_zero h0) hi).1]
  · simp [hi]

theorem canonical_rootMaskIndicator
    (hmore : ∀ i : Fin R.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < R.problem.cfg.kMem →
        (R.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (R.problem.exec.memoryPubAt i).pt.indicator = 0)
    (i : Fin R.problem.cfg.memRows) :
    (OptimizedMemoryGateBasis.rootMaskIndicatorGate (F := F)).eval
      (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  have hmask :
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 153 =
        if (i : ℕ) < R.problem.cfg.kMem then 1 else 0 := by
    simp only [canonicalPhysicalEnv, envOfTrace]
    rw [dif_pos (by decide : (153 : ℕ) < 182)]
    rw [canonicalSourceTrace_root_fixed]
    exact rootRowMask_eval nodes R.problem.cfg.kMem hnodes i
  have hind :
      (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 3 =
        (exactMemoryRowEnv A i).trace 7 := by
    have h := canonical_gather_table_current A nodes hnodes b chalVal pubVal orbit i
      (.inl ⟨3, by decide⟩)
    simpa [extensionEquiv_apply, extensionIndex, memoryTableSourceColumn] using h
  have hind' :
      (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 3 =
        (R.problem.exec.memoryPubAt i).pt.indicator := by
    rw [hind]
    simp [exactMemoryRowEnv, memoryEnvFull]
  simp only [OptimizedMemoryGateBasis.rootMaskIndicatorGate,
    OptimizedMemoryGateBasis.rootMaskPwGate, MixedExpr.eval,
    OptimizedMemoryGateBasis.rootMask, bcur, CoeffExpr.eval,
    OptimizedMemoryGateBasis.rootMaskCol]
  rw [hmask, hind']
  by_cases hi : (i : ℕ) < R.problem.cfg.kMem
  · by_cases h0 : (i : ℕ) = 0
    · simp [hi, (P.rootPubZero i h0).2]
    · simp [hi, (hmore i (Nat.pos_of_ne_zero h0) hi).2]
  · simp [hi]

omit P in
/-- **The denominator pin holds on canonical rows**: role `37` is
`responseDenominator = compress coins (encRec mem)` and roles `19..26` are the record fields in
`encRec` order.  Since A-mem-2 this is the upstream
`OptimizedMemoryCanonicalSatisfaction.canonical_denominatorPinMixed`, with the coin slots read
from `pins` (`HonestSampledCoinSlots.ofPins` is the stage-1 hypothesis it discharges). -/
theorem canonical_denominatorPin
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal) (i : Fin R.problem.cfg.memRows) :
    (denominatorPin (F := F)).eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 :=
  canonical_denominatorPinMixed A nodes hnodes b chalVal pubVal orbit pins i

/-- **Canonical satisfaction of the full paper set.**
    `hmore` is later-seed table zeros; at form R this is the remaining Relaxis
    join (`Batch558.cancellingTree_is_remaining_join`). -/
theorem canonical_paperRow
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (halign : MemoryOrbitAligned nodes orbit) (hsafe : MemoryDenominatorsSafe A)
    (hprl : RowLayout.PairedRecordLayout R.problem.exec)
    (hhon : ∀ row ∈ R.problem.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hord : 2 ≤ R.problem.cfg.memRows →
      R.problem.cfg.memRows ≤ orderOf R.memoryWalkAlpha)
    (hmore : ∀ i : Fin R.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < R.problem.cfg.kMem →
        (R.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (R.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hlam : ∀ i : Fin R.problem.cfg.memRows,
      (R.problem.exec.memoryPubAt i).lambda =
        (R.problem.exec.memoryPubAt ⟨0, R.problem.cfg.memRows_pos⟩).lambda)
    (hC : R.problem.exec.CprimeCoherent)
    (i : Fin R.problem.cfg.memRows)
    (hden : poleSourceMixed.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) ≠ 0 ∨
      aggregatorSign (R.problem.exec.memoryPubAt i).st = (0 : K)) :
    PaperRow b (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) := by
  have hcore := canonical_paperRowCore A P nodes hnodes b chalVal pubVal orbit pins
    halign hsafe hprl hhon hlam hC i hden
  refine ⟨hcore.1, fun g hg => ?_⟩
  simp only [paperKGates, List.mem_append] at hg
  rcases hg with hfront | hqueue
  · rcases hfront with hg | hg
    · exact hcore.2 g hg
    · rw [canonical_gathered_eq]
      simp only [newGates, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact canonical_intermediateInit A nodes hnodes b chalVal pubVal orbit i
      · exact canonical_intermediateTerminal A nodes hnodes b chalVal pubVal orbit hprl hhon hC i
      · exact canonical_rootMaskCounts A P nodes hnodes b chalVal pubVal orbit hmore i
      · exact canonical_rootMaskIndicator A P nodes hnodes b chalVal pubVal orbit hmore i
  · exact MemoryWalkLabelCanonical.canonical_queueWitnessGates
      A nodes hnodes b chalVal pubVal orbit P hord i g hqueue

/-- The committed base-field form of the same fact: all `135` coordinate gates vanish on every
canonical row (`MixedCoordinateCompiler.mixedExpandList_zero_iff`, no coin). -/
theorem canonical_expanded
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (halign : MemoryOrbitAligned nodes orbit) (hsafe : MemoryDenominatorsSafe A)
    (hprl : RowLayout.PairedRecordLayout R.problem.exec)
    (hhon : ∀ row ∈ R.problem.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hord : 2 ≤ R.problem.cfg.memRows →
      R.problem.cfg.memRows ≤ orderOf R.memoryWalkAlpha)
    (hmore : ∀ i : Fin R.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < R.problem.cfg.kMem →
        (R.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (R.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hlam : ∀ j : Fin R.problem.cfg.memRows,
      (R.problem.exec.memoryPubAt j).lambda =
        (R.problem.exec.memoryPubAt ⟨0, R.problem.cfg.memRows_pos⟩).lambda)
    (hC : R.problem.exec.CprimeCoherent)
    (i : Fin R.problem.cfg.memRows)
    (hden : poleSourceMixed.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) ≠ 0 ∨
      aggregatorSign (R.problem.exec.memoryPubAt i).st = (0 : K)) :
    ∀ u ∈ mixedExpandList b memoryCol0 (paperKGates (F := F) (K := K)),
      u.eval (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 :=
  (mixedExpandList_zero_iff b memoryCol0 (isCoordEnv_gather b memoryCol0 _) _).2
    (canonical_paperRow A P nodes hnodes b chalVal pubVal orbit pins
      halign hsafe hprl hhon hord hmore hlam hC i hden).2

omit P hnodes in
theorem paperBaseGates_eq_committed :
    paperBaseGates (F := F) = OptimizedMemoryGateBasis.paperBaseGates (F := F) := rfl

omit P hnodes in
theorem paperKGates_eq_committed :
    paperKGates (F := F) (K := K) = OptimizedMemoryGateBasis.paperKGates (F := F) (K := K) := rfl

/-- Canonical polynomial satisfaction of the W2 source memory RAP (`171/140`).
The committed language is `PaperRow` (`paperBaseGates` / `paperKGates`). -/
theorem canonicalSourceTrace_satisfies
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (halign : MemoryOrbitAligned nodes orbit)
    (hsafe : MemoryDenominatorsSafe A)
    (hprl : RowLayout.PairedRecordLayout R.problem.exec)
    (hhon : ∀ row ∈ R.problem.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hord : 2 ≤ R.problem.cfg.memRows →
      R.problem.cfg.memRows ≤ orderOf R.memoryWalkAlpha)
    (hmore : ∀ i : Fin R.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < R.problem.cfg.kMem →
        (R.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (R.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hlam : ∀ j : Fin R.problem.cfg.memRows,
      (R.problem.exec.memoryPubAt j).lambda =
        (R.problem.exec.memoryPubAt ⟨0, R.problem.cfg.memRows_pos⟩).lambda)
    (hC : R.problem.exec.CprimeCoherent)
    (hdenAll : ∀ i : Fin R.problem.cfg.memRows,
      poleSourceMixed.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) ≠ 0 ∨
        aggregatorSign (R.problem.exec.memoryPubAt i).st = (0 : K))
    (hhalt : HaltLeavesBase A) :
    RAP.SatisfiesWithPreprocessing
      (namedSourceMemoryRAP R.problem.cfg.memRows_pos nodes b chalVal pubVal orbit R.problem.cfg.kMem)
      (canonicalSourceTrace A nodes b R.problem.cfg.kMem) := by
  classical
  constructor
  · change (sourceMemoryRAP b chalVal pubVal orbit (rowNodeSet nodes)).Satisfies
      (canonicalSourceTrace A nodes b R.problem.cfg.kMem)
    apply (sourceMemoryRAP_satisfies_iff_language A nodes b chalVal pubVal orbit
      (canonicalSourceTrace A nodes b R.problem.cfg.kMem)).2
    intro x hx
    rw [rowNodeSet, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    have hpr := canonical_paperRow A P nodes hnodes b chalVal pubVal orbit pins
      halign hsafe hprl hhon hord hmore hlam hC i (hdenAll i)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [baseTransitionGates, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hpr.1 g hg
      · exact canonical_readRootVerGate A nodes hnodes b chalVal pubVal orbit
          hhon i
    · intro g hg
      change g ∈ ([] : List (CoeffExpr F)) at hg
      cases hg
    · intro g hg
      change g ∈ ([] : List Expr) at hg
      cases hg
    · intro g hg
      change g ∈ paperKGates (F := F) (K := K) ++ [haltAtomMixed] at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hpr.2 g hg
      · rw [List.mem_singleton] at hg
        subst hg
        exact canonical_haltAtomMixed A nodes hnodes b chalVal pubVal orbit pins hhalt i
  · exact canonicalSourceTrace_binds A nodes b chalVal pubVal orbit R.problem.cfg.kMem

/-- Canonical polynomial satisfaction of the authorized `196/140`, `d = 4`, `k = 1`
final memory RAP. -/
theorem canonicalFinalMemoryTrace_satisfies
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (halign : MemoryOrbitAligned nodes orbit)
    (hsafe : MemoryDenominatorsSafe A)
    (hprl : RowLayout.PairedRecordLayout R.problem.exec)
    (hhon : ∀ row ∈ R.problem.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hord : 2 ≤ R.problem.cfg.memRows →
      R.problem.cfg.memRows ≤ orderOf R.memoryWalkAlpha)
    (hmore : ∀ i : Fin R.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < R.problem.cfg.kMem →
        (R.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (R.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hlam : ∀ j : Fin R.problem.cfg.memRows,
      (R.problem.exec.memoryPubAt j).lambda =
        (R.problem.exec.memoryPubAt ⟨0, R.problem.cfg.memRows_pos⟩).lambda)
    (hC : R.problem.exec.CprimeCoherent)
    (hdenAll : ∀ i : Fin R.problem.cfg.memRows,
      poleSourceMixed.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) ≠ 0 ∨
        aggregatorSign (R.problem.exec.memoryPubAt i).st = (0 : K))
    (hhalt : HaltLeavesBase A) :
    RAP.SatisfiesWithPreprocessing
      (namedFinalMemoryRAP R.problem.cfg.memRows_pos nodes b chalVal pubVal orbit R.problem.cfg.kMem)
      (canonicalFinalMemoryTrace A nodes b chalVal pubVal orbit) := by
  let S := namedSourceMemoryRAP R.problem.cfg.memRows_pos nodes b chalVal pubVal orbit R.problem.cfg.kMem
  apply (RAPPadding.padFixedPreprocessing_satisfies_iff S
    (RAPPadding.firstRoundExtra S.rap S.rounds_pos
      (RAPPadding.memoryResidualColumns 3))
    (RAPPadding.memoryResidualTransitionGates 3)
    (canonicalFinalMemoryTrace A nodes b chalVal pubVal orbit)).2
  have hsrc := canonicalSourceTrace_satisfies A P nodes hnodes b chalVal pubVal orbit
      pins halign hsafe hprl hhon hord hmore hlam hC hdenAll hhalt
  simp only [canonicalFinalMemoryTrace, S]
  erw [OptimizedMemoryCanonicalSatisfaction.project_rightPadTrace]
  exact hsrc

omit A P nodes hnodes b chalVal pubVal orbit in
/-- Canonical memory realization export: source/final RAP satisfaction and every
root-indexed carried-axis consequence. -/
theorem canonicalMemoryRealization
    (A : SampledIOSameExecutionAssignment R p) {execA : ExactExecution R.problem.cfg}
    (P : MemoryProductionAssignment A execA)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (halign : MemoryOrbitAligned nodes orbit)
    (hsafe : MemoryDenominatorsSafe A)
    (hprl : RowLayout.PairedRecordLayout R.problem.exec)
    (hhon : ∀ row ∈ R.problem.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hord : 2 ≤ R.problem.cfg.memRows →
      R.problem.cfg.memRows ≤ orderOf R.memoryWalkAlpha)
    (hmore : ∀ i : Fin R.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < R.problem.cfg.kMem →
        (R.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (R.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hlam : ∀ j : Fin R.problem.cfg.memRows,
      (R.problem.exec.memoryPubAt j).lambda =
        (R.problem.exec.memoryPubAt ⟨0, R.problem.cfg.memRows_pos⟩).lambda)
    (hC : R.problem.exec.CprimeCoherent)
    (hdenAll : ∀ i : Fin R.problem.cfg.memRows,
      poleSourceMixed.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) ≠ 0 ∨
        aggregatorSign (R.problem.exec.memoryPubAt i).st = (0 : K))
    (hhalt : HaltLeavesBase A)
    (h2 : (2 : K) ≠ 0) :
    RAP.SatisfiesWithPreprocessing
        (namedSourceMemoryRAP R.problem.cfg.memRows_pos nodes b chalVal pubVal orbit R.problem.cfg.kMem)
        (canonicalSourceTrace A nodes b R.problem.cfg.kMem) ∧
      RAP.SatisfiesWithPreprocessing
        (namedFinalMemoryRAP R.problem.cfg.memRows_pos nodes b chalVal pubVal orbit R.problem.cfg.kMem)
        (canonicalFinalMemoryTrace A nodes b chalVal pubVal orbit) ∧
      -- carried-axis consequence on the a-bearing view (row-level rows carry `(T, C')`)
      ∀ (root : Fin R.problem.cfg.kMem) (e : ℕ),
        e ∈ AxisBridge.readExps (exactAxisTree R.problem.cfg execA root) →
        e ∈ AxisBridge.verifyExps (exactAxisTree R.problem.cfg execA root) →
        Nock.AxisBatching.MTree.vaxis e
            (exactAxisTree R.problem.cfg execA root) =
          Nock.AxisBatching.MTree.Relaxis e
            (exactAxisTree R.problem.cfg execA root) := by
  refine ⟨canonicalSourceTrace_satisfies A P nodes hnodes b chalVal pubVal orbit
      pins halign hsafe hprl hhon hord hmore hlam hC hdenAll hhalt,
    canonicalFinalMemoryTrace_satisfies A P nodes hnodes b chalVal pubVal orbit
      pins halign hsafe hprl hhon hord hmore hlam hC hdenAll hhalt, ?_⟩
  intro root e hread hverify
  exact MemoryProductionAssignment.axis_eq_relaxis_of_used h2 P root e hread hverify

end Canonical

end
end MemoryPaperFactorization

namespace OptimizedMemoryCanonicalSatisfaction
export MemoryPaperFactorization (canonicalSourceTrace_satisfies canonicalFinalMemoryTrace_satisfies canonicalMemoryRealization)
end OptimizedMemoryCanonicalSatisfaction

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.deployed_to_paper
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.paper_to_deployed
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.deployed_iff_paper
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.paperCore_iff_perStateGated
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.paper_gate_counts
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.count_comparison
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.paperKGates_degree
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.deployed_implies_denominatorPin
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.deployed_role37_eq
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.deployed_implies_intermediateInit
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.deployed_implies_intermediateTerminal
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.deployed_first_row_ipre
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.deployed_last_row_icur
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.shift_moves_only_the_intermediate_endpoints
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.shift_rejected_at_first_row
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.intermediate_endpoint_readers
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.deployed_to_paperRow
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.canonical_paperRow
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.canonical_expanded
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.canonicalSourceTrace_satisfies
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.canonicalFinalMemoryTrace_satisfies
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.canonicalMemoryRealization
