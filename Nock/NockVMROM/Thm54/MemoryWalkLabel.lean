/-
  Nock/NockVMROM/Thm54/MemoryWalkLabel.lean

  **The memory walk label is the paper's `x^mem`, IN THE GATES.**

  Paper: `x^mem := (state, (parent, (axis_counts_P, axis_indicator_P)))` —
  the row's state and its parent cell: six base coordinates (one tag, a `size/dyck/leaf` noun
  fingerprint, `axis_counts_P`, `axis_indicator_P`).  Children (`:2031`):
  `x_out^mem := ((left_state, (left_child, (axis_counts_L, axis_indicator_L))),
  (right_state, (right_child, (…))))` — the same six-coordinate alphabet per slot.  The walk's
  accumulator identity (`:848-850`) carries `RLC^γ(current_node)` and the one-hot selected
  `Σ_{k=1}^{fanout} α^k · RLC^γ(children(i,k,·))` **in the constraint**; `Corr:forest`
  (`:1004-1008`) seeds the `k` roots.  Until this move the deployed memory chip hosted
  `cur`/`cc`/`cm` as free extension roles `34`/`35`/`36` through
  `OptimizedMemoryGateBasis.walkSubst` (`Batch439`, FINDING).

  **Child states.**  Absent slots carry `MemoryTable.nullMStateTag`; the
  `:848-850` one-hot fanout selector keeps them out of the sum.

  **Readers.**  Every in-gate quantity is built over a `RowReader`: a `𝕂`-role reader and a
  BASE selector reader, so the gates are `MixedExpr`s: `Scale sel body`.  `curReader` serves the
  boundary gates (first row), `nextReader` the transitions.  Degrees: selector `1` × RLC `1` =
  `2`; `ln · cur` = `3`; the base mask adds `1`: every walk gate stays at `d = 4`.

  Walk-γ: memory `𝕂` challenge index `7` (`walkGammaChallengeIndex`; JointCoins `gamma`, the
  same walk-node coin the compute walk reads at compute slot `10`; wired at
  `DeployedChipFamily.memoryKOfTuple` and `BuildableChips.memoryChallengeTargets`).  Walk-α:
  memory slot `3` (`memoryWalkAlpha`).
-/
import Nock.NockVMROM.Thm54.MixedCoordinateCompiler
import Nock.NockVMROM.Thm54.NodeEncoding
import Nock.AIR
import Nock.Walk

namespace Nock.NockVMROM.Thm54
namespace MemoryWalkLabel

open Nock
open Nock.Reified
open Nock.MemoryTable
open MixedCoordinateCompiler
open CoordinateCompiler

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F]

/-! ## Widths, challenge slots, hosts and walk roles -/

/-- Width of the paper `x^mem` label: state tag + parent cell. -/
def memoryLabelWidth : ℕ := 6

/-- Width of a parent-declared child payload: the same `x^mem` alphabet. -/
def childPayloadWidth : ℕ := 6

theorem memoryLabelWidth_eq : memoryLabelWidth = 6 := rfl
theorem childPayloadWidth_eq : childPayloadWidth = 6 := rfl

/-- Own and child payloads share the `x^mem` width. -/
theorem child_payload_matches_label_width : childPayloadWidth = memoryLabelWidth := rfl

/-- The deployed memory label width is the paper's. -/
theorem memoryNodeWidth_eq_label_width :
    NodeEncoding.memoryNodeWidth = memoryLabelWidth := rfl

/-- Walk-γ lives at memory `𝕂` challenge index `7` (physical slots `27..29`); slots `0..6` are
`z`, table `β` (dead), record-RLC, walk-α, IO `γ`, IO pole, `interPole`. -/
def walkGammaChallengeIndex : ℕ := 7

/-- Walk-γ as a `MixedExpr`. -/
def walkGammaChallenge : MixedExpr F := .Var .challenge walkGammaChallengeIndex

/-- Walk-α is memory `𝕂` challenge index `3` (`memoryWalkAlpha`; `walkSubst.challenge 0`). -/
def walkAlphaChallengeIndex : ℕ := 3

def walkAlphaChallenge : MixedExpr F := .Var .challenge walkAlphaChallengeIndex

def childTagHostRole : Fin 2 → ℕ
  | 0 => 45
  | 1 => 46

theorem childTagHostRole_left : childTagHostRole 0 = 45 := rfl
theorem childTagHostRole_right : childTagHostRole 1 = 46 := rfl

/-- The walk's line / count / accumulator roles (`walkSubst 31 + i`, `i = 0, 1, 2`). -/
def lnRole : ℕ := 31
def countRole : ℕ := 32
def accRole : ℕ := 33
/-- Dedicated queue-inverse column.  Not hosted role `34`. -/
def walkInvRole : ℕ := 55

/-- Base of the child cell `j`'s five roles: `lc` at `5..9`, `rc` at `10..14`
(`memoryTableSourceColumn`: table columns `9..13` / `14..18`). -/
def cellBase : Fin 2 → ℕ
  | 0 => 5
  | 1 => 10

/-! ## Row readers -/

/-- How an in-gate expression reads one row: its `𝕂` roles and its BASE one-hot state
selectors. -/
structure RowReader (F : Type*) where
  col : ℕ → MixedExpr F
  sel : MState → CoeffExpr F

/-- The current row (boundary gates and the honest-side lemmas). -/
def curReader : RowReader F :=
  ⟨fun r => .Var .traceCur r, fun st => .var .traceCur (mopCol st)⟩

/-- The successor row (the walk transitions read `cur`/`cc`/`cm` there). -/
def nextReader : RowReader F :=
  ⟨fun r => .Var .traceNext r, fun st => .var .traceNext (mopCol st)⟩

/-! ## One-hot selector sums and RLCs -/

/-- `Σ_st sel(st) · f(st)` over the four states. -/
def selSum (r : RowReader F) (f : MState → MixedExpr F) : MixedExpr F :=
  allMStates.foldr (fun st acc => .Add (.Scale (r.sel st) (f st)) acc) (.Const 0)

/-- `RLC^γ` of six coordinate expressions. -/
def rlcExpr (γ : MixedExpr F) (coords : Fin 6 → MixedExpr F) : MixedExpr F :=
  (List.ofFn fun k : Fin 6 => .Mul (.Pow γ (k : ℕ)) (coords k)).foldr .Add (.Const 0)

/-- Memory state tag as a field constant. -/
def stateTagExpr (st : MState) : MixedExpr F := .Const ↑(NodeEncoding.memoryStateTag st)

/-- Own-row `x^mem` coordinate `k` in state `st`: the tag, then the parent noun fingerprint
(roles `0,1,2`), `axis_counts_P` (role `4`), `axis_indicator_P` (role `3`). -/
def labelCoordAt (r : RowReader F) (st : MState) : Fin 6 → MixedExpr F
  | 0 => stateTagExpr st
  | 1 => r.col 0
  | 2 => r.col 1
  | 3 => r.col 2
  | 4 => r.col 4
  | 5 => r.col 3

def labelRLCAt (r : RowReader F) (st : MState) : MixedExpr F :=
  rlcExpr walkGammaChallenge (labelCoordAt r st)

/-- **`RLC^γ(current_node)`, in-gate**: one-hot over the row's state. -/
def labelRLC (r : RowReader F) : MixedExpr F := selSum r (labelRLCAt r)

/-- Host of child slot `j`'s state tag. -/
def childTagHost (r : RowReader F) (j : Fin 2) : MixedExpr F := r.col (childTagHostRole j)

/-- Child slot `j`'s payload coordinate `k`: its hosted tag, then its cell (`lc`/`rc`, `:2031`):
noun fingerprint (`cellBase j + 0,1,2`), `axis_counts` (`+ 4`), `axis_indicator` (`+ 3`). -/
def childCoordAt (r : RowReader F) (j : Fin 2) : Fin 6 → MixedExpr F
  | 0 => childTagHost r j
  | 1 => r.col (cellBase j)
  | 2 => r.col (cellBase j + 1)
  | 3 => r.col (cellBase j + 2)
  | 4 => r.col (cellBase j + 4)
  | 5 => r.col (cellBase j + 3)

def childRLCAt (r : RowReader F) (j : Fin 2) : MixedExpr F :=
  rlcExpr walkGammaChallenge (childCoordAt r j)

/-- The paper's inner sum `Σ_{k=1}^{fanout} α^k · RLC^γ(children(i,k,·))` for fanout `fo`. -/
def childInnerSum (r : RowReader F) : ℕ → MixedExpr F
  | 0 => .Const 0
  | 1 => .Mul (.Pow walkAlphaChallenge 1) (childRLCAt r 0)
  | 2 =>
      .Add (.Mul (.Pow walkAlphaChallenge 1) (childRLCAt r 0))
        (.Mul (.Pow walkAlphaChallenge 2) (childRLCAt r 1))
  | _ => .Const 0

def childSumAt (r : RowReader F) (st : MState) : MixedExpr F := childInnerSum r (fanoutMem st)

/-- **`cc`, in-gate**: `Σ_st sel(st) · Σ_{k=1}^{fanout(st)} α^k · RLC^γ(child_k)`. -/
def childSumCC (r : RowReader F) : MixedExpr F := selSum r (childSumAt r)

def cmAt (st : MState) : MixedExpr F := .Pow walkAlphaChallenge (fanoutMem st)

/-- **`cm`, in-gate**: `Σ_st sel(st) · α^{fanout(st)}`. -/
def selectorCM (r : RowReader F) : MixedExpr F := selSum r cmAt

/-- Every memory state has fanout ≤ 2. -/
theorem fanoutMem_le_two (st : MState) : fanoutMem st ≤ 2 := by
  cases st <;> decide

/-! ## The in-gate walk gates -/

/-- Preprocessing first-row mask (base column `4`). -/
def firstMaskBase : CoeffExpr F := .var .traceCur 4
/-- Preprocessing last-row mask (base column `5`). -/
def lastMaskBase : CoeffExpr F := .var .traceCur 5
def notLastBase : CoeffExpr F := .sub (.const 1) lastMaskBase

def lnCur : MixedExpr F := .Var .traceCur lnRole
def lnNext : MixedExpr F := .Var .traceNext lnRole
def countCur : MixedExpr F := .Var .traceCur countRole
def countNext : MixedExpr F := .Var .traceNext countRole
def accCur : MixedExpr F := .Var .traceCur accRole
def accNext : MixedExpr F := .Var .traceNext accRole
def walkInvCur : MixedExpr F := .Var .traceCur walkInvRole
/-- `initial_count = α^k`, public role `0`. -/
def initialCountPub : MixedExpr F := .Var .publicVal 0
def seedPub : MixedExpr F := .Var .publicVal 1

/-- Preprocessing root mask (column `153`, same physical slot as
    `OptimizedMemoryGateBasis.rootMask`).  Kept for the nineteenth-move
    zero gates (`rootMask · counts/indicator = 0`). -/
abbrev rootMaskCol : ℕ := 153
def rootMaskCur : CoeffExpr F := .var .traceCur rootMaskCol
def rootMaskNext : CoeffExpr F := .var .traceNext rootMaskCol
def notRootMaskCur : CoeffExpr F := .sub (.const 1) rootMaskCur
def notRootMaskNext : CoeffExpr F := .sub (.const 1) rootMaskNext

/-- Preprocessing dequeue mask (column `154`, coord `1` of dead role `49`):
    `notLast · (1 − rootMask(next))`.  One on every non-last row whose
    successor is not a root; verifier-computed.  The product of two
    fixed columns is itself a fixed column, so the degree-5 monomial
    `notLast·(1−rootMask)·ln·RLC` splits at `d = 4`. -/
abbrev dequeueMaskCol : ℕ := 154
def dequeueMaskCur : CoeffExpr F := .var .traceCur dequeueMaskCol
def dequeueMaskNext : CoeffExpr F := .var .traceNext dequeueMaskCol

/-- Initial count (boundary): `first · (count(1) − initial_count · cm(1))`, `cm` in-gate. -/
def walkCount1InGate : MixedExpr F :=
  .Scale firstMaskBase (.Sub countCur (.Mul initialCountPub (selectorCM curReader)))

/-- Initial accumulator (boundary), **mask form**: first row is always a root
    (`kMem ≥ 1`), so the dequeue is absent and `acc(1) = initial_count·cc(1)`.  No seed public
    and no `(1−rootMask)` product. -/
def walkAccInitInGate : MixedExpr F :=
  .Scale firstMaskBase
    (.Sub accCur (.Mul initialCountPub (childSumCC curReader)))

/-- Count increment (transition): `(1 − last) · (count(i+1) − count(i) · cm(i+1))`. -/
def walkCountStepInGate : MixedExpr F :=
  .Scale notLastBase (.Sub countNext (.Mul countCur (selectorCM nextReader)))

/-- **Accumulation step, degree-4 split:**
`dequeueMask·ln·RLC^γ(x^mem) + notLast·(Δacc − count·cc)`.
Both summands are degree 4 (`1+1+2` and the pre-existing 4). -/
def walkAccStepInGate : MixedExpr F :=
  .Add
    (.Scale dequeueMaskCur (.Mul lnNext (labelRLC nextReader)))
    (.Scale notLastBase
      (.Sub (.Sub accNext accCur) (.Mul countCur (childSumCC nextReader))))

/-- The four in-gate walk gates, in the committed order (count then acc, boundary then step). -/
def inGateWalkGates : List (MixedExpr F) :=
  [walkCount1InGate, walkAccInitInGate, walkCountStepInGate, walkAccStepInGate]

/-- Ratio-form queue gates.  `count` and `ln` are
dedicated columns, so nonempty is degree 3.  `walk_inv` is a NEW column (role `55`),
not a reuse of hosted `cur`/`cc`/`cm` at `34`/`35`/`36`. -/
def walkQueueNonEmpty : MixedExpr F :=
  .Scale notLastBase
    (.Sub (.Mul walkInvCur (.Sub countCur lnCur)) (.Const 1))

def walkQueueTiling : MixedExpr F :=
  .Scale lastMaskBase (.Sub countCur lnCur)

def queueWitnessGates : List (MixedExpr F) :=
  [walkQueueNonEmpty, walkQueueTiling]

theorem walkQueueNonEmpty_degree : (walkQueueNonEmpty (F := F)).degree ≤ 4 := by
  simp only [walkQueueNonEmpty, MixedExpr.degree, notLastBase, lastMaskBase,
    CoeffExpr.degree, walkInvCur, countCur, lnCur]
  decide

theorem walkQueueTiling_degree : (walkQueueTiling (F := F)).degree ≤ 4 := by
  simp only [walkQueueTiling, MixedExpr.degree, lastMaskBase, CoeffExpr.degree,
    countCur, lnCur]
  decide

/-! ## Degrees (`d = 4`)

Structural: a base selector costs `1`, an RLC of degree-`≤ 1` coordinates costs `1`, so the
selector-summed `cur`/`cc` cost `2` and `cm` costs `1`; `ln · cur` and `count · cc` cost `3`; the
preprocessing mask adds `1`. -/

theorem curReader_sel_degree (st : MState) : ((curReader (F := F)).sel st).degree = 1 := rfl
theorem nextReader_sel_degree (st : MState) : ((nextReader (F := F)).sel st).degree = 1 := rfl
theorem curReader_col_degree (i : ℕ) : ((curReader (F := F)).col i).degree = 1 := rfl
theorem nextReader_col_degree (i : ℕ) : ((nextReader (F := F)).col i).degree = 1 := rfl

theorem selSum_degree_le (r : RowReader F) (f : MState → MixedExpr F) (d : ℕ)
    (hsel : ∀ st, (r.sel st).degree ≤ 1) (hf : ∀ st, (f st).degree ≤ d) :
    (selSum r f).degree ≤ d + 1 := by
  have h0 := hsel .decompose
  have h1 := hsel .halt
  have h2 := hsel .read_root
  have h3 := hsel .verify_child
  have f0 := hf .decompose
  have f1 := hf .halt
  have f2 := hf .read_root
  have f3 := hf .verify_child
  simp only [selSum, allMStates, List.foldr, MixedExpr.degree, max_le_iff]
  omega

theorem foldr_add_degree_le (l : List (MixedExpr F)) (d : ℕ) (h : ∀ x ∈ l, x.degree ≤ d) :
    (l.foldr MixedExpr.Add (.Const 0)).degree ≤ d := by
  induction l with
  | nil => simp [MixedExpr.degree]
  | cons x xs ih =>
    simp only [List.foldr, MixedExpr.degree, max_le_iff]
    exact ⟨h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩

theorem rlcExpr_degree_le (γ : MixedExpr F) (coords : Fin 6 → MixedExpr F)
    (hγ : γ.degree = 0) (hc : ∀ k, (coords k).degree ≤ 1) :
    (rlcExpr γ coords).degree ≤ 1 := by
  unfold rlcExpr
  apply foldr_add_degree_le
  intro x hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  simp only [MixedExpr.degree, hγ, Nat.mul_zero, Nat.zero_add]
  exact hc k

omit [Field F] in
theorem walkGammaChallenge_degree : (walkGammaChallenge (F := F)).degree = 0 := rfl
omit [Field F] in
theorem walkAlphaChallenge_degree : (walkAlphaChallenge (F := F)).degree = 0 := rfl

theorem labelCoordAt_degree (r : RowReader F) (hcol : ∀ i, (r.col i).degree ≤ 1)
    (st : MState) (k : Fin 6) : (labelCoordAt r st k).degree ≤ 1 := by
  fin_cases k
  · simp [labelCoordAt, stateTagExpr, MixedExpr.degree]
  all_goals exact hcol _

theorem labelRLC_degree (r : RowReader F) (hsel : ∀ st, (r.sel st).degree ≤ 1)
    (hcol : ∀ i, (r.col i).degree ≤ 1) : (labelRLC r).degree ≤ 2 :=
  selSum_degree_le r _ 1 hsel fun st =>
    rlcExpr_degree_le _ _ walkGammaChallenge_degree (labelCoordAt_degree r hcol st)

theorem childCoordAt_degree (r : RowReader F) (hcol : ∀ i, (r.col i).degree ≤ 1)
    (j : Fin 2) (k : Fin 6) : (childCoordAt r j k).degree ≤ 1 := by
  fin_cases k <;> exact hcol _

theorem childRLCAt_degree (r : RowReader F) (hcol : ∀ i, (r.col i).degree ≤ 1) (j : Fin 2) :
    (childRLCAt r j).degree ≤ 1 :=
  rlcExpr_degree_le _ _ walkGammaChallenge_degree (childCoordAt_degree r hcol j)

theorem childInnerSum_degree (r : RowReader F) (hcol : ∀ i, (r.col i).degree ≤ 1) (n : ℕ) :
    (childInnerSum r n).degree ≤ 1 := by
  have h0 := childRLCAt_degree r hcol 0
  have h1 := childRLCAt_degree r hcol 1
  match n with
  | 0 => simp [childInnerSum, MixedExpr.degree]
  | 1 =>
      simp only [childInnerSum, MixedExpr.degree, walkAlphaChallenge_degree, Nat.mul_zero,
        Nat.zero_add]
      exact h0
  | 2 =>
      simp only [childInnerSum, MixedExpr.degree, walkAlphaChallenge_degree, Nat.mul_zero,
        Nat.zero_add, max_le_iff]
      exact ⟨h0, h1⟩
  | n + 3 => simp [childInnerSum, MixedExpr.degree]

theorem childSumCC_degree (r : RowReader F) (hsel : ∀ st, (r.sel st).degree ≤ 1)
    (hcol : ∀ i, (r.col i).degree ≤ 1) : (childSumCC r).degree ≤ 2 :=
  selSum_degree_le r _ 1 hsel fun st => childInnerSum_degree r hcol _

theorem selectorCM_degree (r : RowReader F) (hsel : ∀ st, (r.sel st).degree ≤ 1) :
    (selectorCM r).degree ≤ 1 :=
  selSum_degree_le r _ 0 hsel fun _ => by
    simp [cmAt, MixedExpr.degree, walkAlphaChallenge_degree]

theorem walkCount1InGate_degree : (walkCount1InGate (F := F)).degree ≤ 4 := by
  have h := selectorCM_degree (curReader (F := F)) (fun st => (curReader_sel_degree st).le)
  simp only [walkCount1InGate, MixedExpr.degree, firstMaskBase, CoeffExpr.degree, countCur,
    initialCountPub, max_le_iff]
  omega

theorem walkAccInitInGate_degree : (walkAccInitInGate (F := F)).degree ≤ 4 := by
  have h2 := childSumCC_degree (curReader (F := F)) (fun st => (curReader_sel_degree st).le)
    (fun i => (curReader_col_degree i).le)
  simp only [walkAccInitInGate, MixedExpr.degree, firstMaskBase, CoeffExpr.degree,
    accCur, initialCountPub, max_le_iff]
  omega

theorem walkCountStepInGate_degree : (walkCountStepInGate (F := F)).degree ≤ 4 := by
  have h := selectorCM_degree (nextReader (F := F)) (fun st => (nextReader_sel_degree st).le)
  simp only [walkCountStepInGate, MixedExpr.degree, notLastBase, lastMaskBase, CoeffExpr.degree,
    countCur, countNext, max_le_iff]
  omega

theorem walkAccStepInGate_degree : (walkAccStepInGate (F := F)).degree ≤ 4 := by
  have h1 := labelRLC_degree (nextReader (F := F)) (fun st => (nextReader_sel_degree st).le)
    (fun i => (nextReader_col_degree i).le)
  have h2 := childSumCC_degree (nextReader (F := F)) (fun st => (nextReader_sel_degree st).le)
    (fun i => (nextReader_col_degree i).le)
  simp only [walkAccStepInGate, MixedExpr.degree, dequeueMaskCur, notLastBase, lastMaskBase,
    CoeffExpr.degree, lnNext, accNext, accCur, countCur, max_le_iff]
  omega

theorem inGateWalkGates_degree : ∀ g ∈ inGateWalkGates (F := F), g.degree ≤ 4 := by
  intro g hg
  simp only [inGateWalkGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact walkCount1InGate_degree
  · exact walkAccInitInGate_degree
  · exact walkCountStepInGate_degree
  · exact walkAccStepInGate_degree

/-! ## Honest evaluation (reader-generic)

The in-gate quantities evaluate, on any row whose base selectors are one-hot at `pub.st`, whose
parent-cell roles carry `pub.pt`, whose child-cell roles carry `pub.lc`/`pub.rc` and whose two
hosts carry the declared tags, to the paper's values: `RLC^γ` of the `x^mem` label vector, the
one-hot child sum, and `α^{fanout}`. -/

section HonestEval

variable {K : Type*} [Field K] [Algebra F K]

/-- The five cell coordinates in role order: noun `size, dyck, leaf`, then `axis_indicator`,
`axis_counts` (table columns `7`, `8` ↦ roles `3`, `4`). -/
def cellCoord (c : Cell K) : Fin 5 → K
  | 0 => c.noun.size
  | 1 => c.noun.dyck
  | 2 => c.noun.leaf
  | 3 => c.indicator
  | 4 => c.counts

/-- The parent's declared child cell for slot `j`: `lc` / `rc`. -/
def childCell (pub : Pub K) : Fin 2 → Cell K
  | 0 => pub.lc
  | 1 => pub.rc

theorem childCell_eq_memCell (l : MState × DTmem K) (j : Fin 2) :
    childCell l.2.2 j = memCell l j := by
  fin_cases j <;> rfl

/-- The vector a parent declares for child slot `j`: the hosted tag, then its cell in `x^mem`
order. -/
def childVec (pub : Pub K) (tags : Fin 2 → K) (j : Fin 2) : Fin 6 → K
  | 0 => tags j
  | 1 => (childCell pub j).noun.size
  | 2 => (childCell pub j).noun.dyck
  | 3 => (childCell pub j).noun.leaf
  | 4 => (childCell pub j).counts
  | 5 => (childCell pub j).indicator

/-- `childVec` at a natural slot index; out-of-range slots read the zero vector. -/
def childVecN (pub : Pub K) (tags : Fin 2 → K) : ℕ → Fin 6 → K
  | 0 => childVec pub tags 0
  | 1 => childVec pub tags 1
  | _ => fun _ => 0

theorem childVecN_fin (pub : Pub K) (tags : Fin 2 → K) (j : Fin 2) :
    childVecN pub tags j = childVec pub tags j := by
  fin_cases j <;> rfl

/-- A declared child vector IS the child's own `x^mem` label vector when the tag is the child's
state tag and the cell is the child's parent cell. -/
theorem childVec_eq_labelVec (pub : Pub K) (tags : Fin 2 → K) (j : Fin 2) (child : Pub K)
    (htag : tags j = mstateTagField child.st) (hcell : childCell pub j = child.pt) :
    childVec pub tags j = memoryLabelVec child := by
  funext k
  fin_cases k <;> simp [childVec, memoryLabelVec, htag, hcell]

theorem selSum_eval (r : RowReader F) (f : MState → MixedExpr F) (eK : Env K) (eF : Env F)
    (active : MState)
    (hsel : ∀ st, (r.sel st).eval eF = if st = active then 1 else 0) :
    (selSum r f).eval eK eF = (f active).eval eK eF := by
  have h0 := hsel .decompose
  have h1 := hsel .halt
  have h2 := hsel .read_root
  have h3 := hsel .verify_child
  cases active <;>
    simp at h0 h1 h2 h3 <;>
    simp [selSum, allMStates, MixedExpr.eval, h0, h1, h2, h3]

theorem rlcExpr_eval (γ : MixedExpr F) (coords : Fin 6 → MixedExpr F) (eK : Env K) (eF : Env F) :
    (rlcExpr γ coords).eval eK eF =
      Walk.rlc (node_size := 6) (γ.eval eK eF) (fun k => (coords k).eval eK eF) := by
  simp only [rlcExpr, List.ofFn_succ, List.ofFn_zero, List.foldr, MixedExpr.eval]
  simp [Walk.rlc, Fin.sum_univ_succ]

/-- The row's own label RLC is `RLC^γ` of the paper's `x^mem` label vector. -/
theorem labelRLC_eval (r : RowReader F) (eK : Env K) (eF : Env F) (pub : Pub K) (g : K)
    (hsel : ∀ st, (r.sel st).eval eF = if st = pub.st then 1 else 0)
    (hcol : ∀ k : Fin 5, (r.col k).eval eK eF = cellCoord pub.pt k)
    (hγ : (walkGammaChallenge (F := F)).eval eK eF = g) :
    (labelRLC r).eval eK eF = Walk.rlc g (memoryLabelVec pub) := by
  rw [labelRLC, selSum_eval r _ eK eF pub.st hsel, labelRLCAt, rlcExpr_eval, hγ]
  congr 1
  funext k
  fin_cases k
  · simp [labelCoordAt, stateTagExpr, memoryLabelVec, MixedExpr.eval,
      NodeEncoding.memoryStateTag_cast]
  · exact hcol 0
  · exact hcol 1
  · exact hcol 2
  · exact hcol 4
  · exact hcol 3

theorem childRLCAt_eval (r : RowReader F) (eK : Env K) (eF : Env F) (pub : Pub K) (g : K)
    (tags : Fin 2 → K) (j : Fin 2)
    (hcol : ∀ k : Fin 5, (r.col (cellBase j + k)).eval eK eF = cellCoord (childCell pub j) k)
    (hγ : (walkGammaChallenge (F := F)).eval eK eF = g)
    (htag : (childTagHost r j).eval eK eF = tags j) :
    (childRLCAt r j).eval eK eF = Walk.rlc g (childVec pub tags j) := by
  rw [childRLCAt, rlcExpr_eval, hγ]
  congr 1
  funext k
  have h0 := hcol 0
  have h1 := hcol 1
  have h2 := hcol 2
  have h3 := hcol 3
  have h4 := hcol 4
  simp only [Fin.val_zero, Nat.add_zero, Fin.val_one, Fin.val_two] at h0 h1 h2 h3 h4
  fin_cases k
  · exact htag
  · exact h0
  · exact h1
  · exact h2
  · exact h4
  · exact h3

/-- The in-gate `cc` is the paper's one-hot child sum over the declared payloads. -/
theorem childSumCC_eval (r : RowReader F) (eK : Env K) (eF : Env F) (pub : Pub K) (a g : K)
    (tags : Fin 2 → K)
    (hsel : ∀ st, (r.sel st).eval eF = if st = pub.st then 1 else 0)
    (hcol : ∀ (j : Fin 2) (k : Fin 5),
      (r.col (cellBase j + k)).eval eK eF = cellCoord (childCell pub j) k)
    (hα : (walkAlphaChallenge (F := F)).eval eK eF = a)
    (hγ : (walkGammaChallenge (F := F)).eval eK eF = g)
    (htag : ∀ j, (childTagHost r j).eval eK eF = tags j) :
    (childSumCC r).eval eK eF =
      ∑ l ∈ Finset.Icc 1 (fanoutMem pub.st),
        a ^ l * Walk.rlc g (childVecN pub tags (l - 1)) := by
  rw [childSumCC, selSum_eval r _ eK eF pub.st hsel, childSumAt]
  have c0 := childRLCAt_eval r eK eF pub g tags 0 (hcol 0) hγ (htag 0)
  have c1 := childRLCAt_eval r eK eF pub g tags 1 (hcol 1) hγ (htag 1)
  rw [Walk.sum_Icc_one_eq_range]
  cases hs : pub.st <;>
    simp [fanoutMem, childInnerSum, MixedExpr.eval, hα, c0, c1, childVecN,
      Finset.sum_range_succ]

/-- The in-gate `cm` is `α^{fanout(state)}`. -/
theorem selectorCM_eval (r : RowReader F) (eK : Env K) (eF : Env F) (pub : Pub K) (a : K)
    (hsel : ∀ st, (r.sel st).eval eF = if st = pub.st then 1 else 0)
    (hα : (walkAlphaChallenge (F := F)).eval eK eF = a) :
    (selectorCM r).eval eK eF = a ^ fanoutMem pub.st := by
  rw [selectorCM, selSum_eval r _ eK eF pub.st hsel, cmAt]
  simp [MixedExpr.eval, hα]

/-! ### The gates, evaluated -/

theorem walkCount1InGate_eval (eK : Env K) (eF : Env F) :
    (walkCount1InGate (F := F)).eval eK eF =
      algebraMap F K (eF.trace 4) *
        (eK.trace countRole - eK.pub 0 * (selectorCM (curReader (F := F))).eval eK eF) := by
  simp [walkCount1InGate, MixedExpr.eval, CoeffExpr.eval, firstMaskBase, countCur,
    initialCountPub]

theorem walkAccInitInGate_eval (eK : Env K) (eF : Env F) :
    (walkAccInitInGate (F := F)).eval eK eF =
      algebraMap F K (eF.trace 4) *
        (eK.trace accRole -
          eK.pub 0 * (childSumCC (curReader (F := F))).eval eK eF) := by
  simp [walkAccInitInGate, MixedExpr.eval, CoeffExpr.eval, firstMaskBase, accCur,
    initialCountPub]

theorem walkCountStepInGate_eval (eK : Env K) (eF : Env F) :
    (walkCountStepInGate (F := F)).eval eK eF =
      algebraMap F K (1 - eF.trace 5) *
        (eK.traceNext countRole -
          eK.trace countRole * (selectorCM (nextReader (F := F))).eval eK eF) := by
  simp [walkCountStepInGate, MixedExpr.eval, CoeffExpr.eval, notLastBase, lastMaskBase,
    countCur, countNext]

theorem walkAccStepInGate_eval (eK : Env K) (eF : Env F) :
    (walkAccStepInGate (F := F)).eval eK eF =
      algebraMap F K (eF.trace dequeueMaskCol) *
          (eK.traceNext lnRole * (labelRLC (nextReader (F := F))).eval eK eF) +
        algebraMap F K (1 - eF.trace 5) *
          (eK.traceNext accRole - eK.trace accRole -
            eK.trace countRole * (childSumCC (nextReader (F := F))).eval eK eF) := by
  simp [walkAccStepInGate, MixedExpr.eval, CoeffExpr.eval, dequeueMaskCur, notLastBase,
    lastMaskBase, lnNext, accNext, accCur, countCur, dequeueMaskCol]

theorem walkQueueNonEmpty_eval (eK : Env K) (eF : Env F) :
    (walkQueueNonEmpty (F := F)).eval eK eF =
      algebraMap F K (1 - eF.trace 5) *
        (eK.trace walkInvRole * (eK.trace countRole - eK.trace lnRole) - 1) := by
  simp [walkQueueNonEmpty, MixedExpr.eval, CoeffExpr.eval, notLastBase, lastMaskBase,
    walkInvCur, countCur, lnCur]

theorem walkQueueTiling_eval (eK : Env K) (eF : Env F) :
    (walkQueueTiling (F := F)).eval eK eF =
      algebraMap F K (eF.trace 5) * (eK.trace countRole - eK.trace lnRole) := by
  simp [walkQueueTiling, MixedExpr.eval, CoeffExpr.eval, lastMaskBase, countCur, lnCur]

/-! ### Reader instances of the value hypotheses -/

theorem curReader_sel_eval (eF : Env F) (st : MState) :
    ((curReader (F := F)).sel st).eval eF = eF.trace (mopCol st) := rfl
theorem nextReader_sel_eval (eF : Env F) (st : MState) :
    ((nextReader (F := F)).sel st).eval eF = eF.traceNext (mopCol st) := rfl
theorem curReader_col_eval (eK : Env K) (eF : Env F) (i : ℕ) :
    ((curReader (F := F)).col i).eval eK eF = eK.trace i := rfl
theorem nextReader_col_eval (eK : Env K) (eF : Env F) (i : ℕ) :
    ((nextReader (F := F)).col i).eval eK eF = eK.traceNext i := rfl

end HonestEval

end MemoryWalkLabel
end Nock.NockVMROM.Thm54
