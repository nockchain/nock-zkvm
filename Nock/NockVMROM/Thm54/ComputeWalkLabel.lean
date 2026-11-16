/-
  Nock/NockVMROM/Thm54/ComputeWalkLabel.lean

Paper: `LT_comp = {OP_i ∪ cons} × ((N^λ, N^λ), N^λ)` — state × (subject,
  formula, evaluation): ten base coordinates (one tag + `s`/`f`/`e` × 3).  The walk's
  accumulator identity (`:848-850`) carries `RLC^γ(current_node)` and the one-hot selected
  `Σ_k α^k · RLC^γ(children(i,k,·))` **in the constraint**; the paper's walk has no `cur`
  column.  Until this move the deployed chip hosted `cur`/`cc`/`cm` as free overlay columns
.

  **Option A:** child slots carry `sf_state_j`.  A
  parent declares `(sf_state_j, sf_j)` — ten coordinates, the same alphabet as its own label —
  and the three tags are hosted in the overlay coordinates freed by the in-gate `cur`/`cc`/`cm`
  (`overlayCoord 2..4`, i.e. `pubFP (overlayANat st) 2`, `pubFP (overlayBNat st) 0/1`).  Absent
  slots carry `nullStateTag = 10` (`:1748`/`:1752` compute `⊥`), and the `:848-850` one-hot fanout
  selector keeps them out of the sum.

  **Reader parametrisation.**  Every in-gate expression is built over a `RowReader` — a column
  reader and a state-selector reader — because the three deployments differ only there:
  * `nextReader` (successor row, trace selectors): the walk transitions read `cur`/`cc`/`cm` on
    the successor row only (`walkAccStep`, `walkCountStep`);
  * `firstReader` (first row, **public** `initialMask` selectors): the boundary gates
    `walkAccInit`/`walkCount1` — public selectors keep `isFirst² · walkAccInit` at degree `4`;
  * `curReader`: the honest-side evaluation lemmas, transported to the other two.

  **Restored sources.**  Fingerprint roles are HOSTS in some states (`overlayANat .s1 = 2` is
  the row's own `e`; roles `3`/`4` host in `s0`/`s2`), so inside a state branch a label
  coordinate is read through `sourcePubAtR` — the restored source (`decFP` / `pubFP` /
  `Const 0`), degree `1` — exactly as `semanticPub` restores the table gates.  Under one outer
  selector sum `cur` and `cc` therefore have degree `2` on a transition row, so
  `count(i) · cc(i+1)` is degree `4`: the whole packing stays at `d = 4`.

  Walk-γ: compute `𝕂` challenge index `10` (`walkGammaChallenge`; JointCoins `gamma`, wired at
  `DeployedChipFamily.computeKOfTuple` and `exactFinalChallenge`).  Walk-α: slot `6`.

  Paper: the paper.
-/
import Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
import Nock.NockVMROM.Thm54.NodeEncoding
import Nock.NockVMROM.Thm54.JointCoins
import Nock.ComputeTable

namespace Nock.NockVMROM.Thm54
namespace ComputeWalkLabel

open Nock
open Nock.Reified
open Nock.ComputeTable
open OptimizedComputeSubstitution

/-! ## Widths and challenge slots -/

/-- Width of the paper `LT_comp` label: state tag + `s`/`f`/`e` (9). -/
def computeLabelWidth : ℕ := 10

/-- Width of a parent-declared child payload: the same `LT_comp` alphabet (Option A). -/
def childPayloadWidth : ℕ := 10

theorem computeLabelWidth_eq : computeLabelWidth = 10 := rfl
theorem childPayloadWidth_eq : childPayloadWidth = 10 := rfl

/-- Own and child payloads share the `LT_comp` width (Option A). -/
theorem child_payload_matches_label_width : childPayloadWidth = computeLabelWidth := rfl

/-- The deployed label width is the paper's. -/
theorem computeNodeWidth_eq_label_width :
    NodeEncoding.computeNodeWidth = computeLabelWidth := rfl

/-- Walk-γ lives at compute `𝕂` challenge index `10`. -/
def walkGammaChallengeIndex : ℕ := 10

/-- Walk-γ as an `Expr`. -/
def walkGammaChallenge : Expr := .Var .challenge walkGammaChallengeIndex

/-- Walk-α remains challenge slot `6` (`walkChallengeBase`). -/
def walkAlphaChallenge : Expr := walkChallenge 0

theorem null_state_tag_eq : ComputeTable.nullStateTag = 10 := rfl

/-! ## Row readers -/

/-- How an in-gate expression reads one row: its columns and its one-hot state selectors. -/
structure RowReader where
  col : ℕ → Expr
  sel : State → Expr

/-- The current row through its trace selectors (honest-side lemmas). -/
def curReader : RowReader := ⟨fun i => .Var .traceCur i, fun st => .Var .traceCur (opCol st)⟩

/-- The successor row through its trace selectors (the walk transitions). -/
def nextReader : RowReader := ⟨fun i => .Var .traceNext i, fun st => .Var .traceNext (opCol st)⟩

/-- Public first-row state mask (`OptimizedComputeTemplate.initialMask`, slots `20..30`). -/
def initialMaskExpr (st : State) : Expr := .Var .publicVal (20 + opCol st)

/-- The first row through the public initial-state masks (the walk boundary gates). -/
def firstReader : RowReader := ⟨fun i => .Var .traceCur i, initialMaskExpr⟩

/-! ## Restored public sources through a reader (mirrors `sourcePubAt`) -/

def pubFPR (r : RowReader) (role coord : ℕ) : Expr := r.col (ext0 + 3 * role + coord)
def decFPR (r : RowReader) (role coord : ℕ) : Expr := r.col (ext0 + 36 + 3 * role + coord)

def restoredAFieldR (r : RowReader) (st : State) (coord : ℕ) : Expr :=
  match st with
  | .s1 => decFPR r 1 coord
  | .s2 => pubFPR r 0 coord
  | _ => .Const 0

def restoredBFieldR (r : RowReader) (st : State) (coord : ℕ) : Expr :=
  match st with
  | .s2 => decFPR r 2 coord
  | _ => .Const 0

def restoredIOHostFieldR (r : RowReader) (st : State) : Expr :=
  match st with
  | .s2 => pubFPR r 8 2
  | _ => .Const 0

def restoredDenomHostFieldR (r : RowReader) (st : State) (coord : ℕ) : Expr :=
  match st with
  | .s2 => pubFPR r 2 coord
  | _ => .Const 0

/-- The restored source of public fingerprint coordinate `role, coord` in state `st`. -/
def sourcePubAtR (r : RowReader) (st : State) (role coord : ℕ) : Expr :=
  if role = 10 ∧ coord = 2 then restoredIOHostFieldR r st
  else if role = 11 then restoredDenomHostFieldR r st coord
  else if role = overlayANat st then restoredAFieldR r st coord
  else if role = overlayBNat st ∧ coord < 2 then restoredBFieldR r st coord
  else pubFPR r role coord

theorem sourcePubAtR_cur (st : State) (role coord : ℕ) :
    sourcePubAtR curReader st role coord = sourcePubAt .traceCur st role coord := by
  cases st <;> rfl

/-- 4.35 migration helper: `Expr.eval` commutes with an `Expr`-valued `if`. Proof-only addition. -/
theorem eval_ite_aux {K : Type*} [Field K] (c : Prop) [Decidable c] (a b : Expr) (env : Env K) :
    (if c then a else b).eval env = if c then a.eval env else b.eval env := by
  split <;> rfl

/-- Shifting a `nextReader` expression onto the successor row as a current row. -/
def shiftNext {K : Type*} (env : Env K) : Env K :=
  { env with trace := env.traceNext }

theorem sourcePubAtR_next_eval {K : Type*} [Field K] (env : Env K) (st : State)
    (role coord : ℕ) :
    (sourcePubAtR nextReader st role coord).eval env =
      (sourcePubAtR curReader st role coord).eval (shiftNext env) := by
  cases st <;>
    simp only [sourcePubAtR, restoredAFieldR, restoredBFieldR, restoredIOHostFieldR,
      restoredDenomHostFieldR, pubFPR, decFPR, nextReader, curReader, overlayANat,
      overlayBNat] <;>
    split_ifs <;> simp_all [Expr.eval, shiftNext, eval_ite_aux]

theorem pubFPR_next_eval {K : Type*} [Field K] (env : Env K) (role coord : ℕ) :
    (pubFPR nextReader role coord).eval env =
      (pubFPR curReader role coord).eval (shiftNext env) := by
  simp [pubFPR, nextReader, curReader, shiftNext, Expr.eval]

/-! ## One-hot selector sums and RLCs -/

/-- `Σ_st sel(st) · f(st)` over the eleven states. -/
def selSum (r : RowReader) (f : State → Expr) : Expr :=
  allStates.foldr (fun st acc => .Add (.Mul (r.sel st) (f st)) acc) (.Const 0)

/-- `RLC^γ` of ten coordinate expressions. -/
def rlcExpr (γ : Expr) (coords : Fin 10 → Expr) : Expr :=
  (List.ofFn fun k : Fin 10 => .Mul (.Pow γ (k : ℕ)) (coords k)).foldr .Add (.Const 0)

/-- Opcode tag as a field constant (paper tags `0..9 ∪ {11}`). -/
def stateTagExpr (st : State) : Expr := .Const ↑(NodeEncoding.computeStateTag st)

/-- Own-row `LT_comp` coordinate `k` in state `st`: the tag, then `s`,`f`,`e` (roles `0,1,2`)
through the restored source. -/
def labelCoordAt (r : RowReader) (st : State) : Fin 10 → Expr
  | 0 => stateTagExpr st
  | 1 => sourcePubAtR r st 0 0
  | 2 => sourcePubAtR r st 0 1
  | 3 => sourcePubAtR r st 0 2
  | 4 => sourcePubAtR r st 1 0
  | 5 => sourcePubAtR r st 1 1
  | 6 => sourcePubAtR r st 1 2
  | 7 => sourcePubAtR r st 2 0
  | 8 => sourcePubAtR r st 2 1
  | 9 => sourcePubAtR r st 2 2

def labelRLCAt (r : RowReader) (st : State) : Expr :=
  rlcExpr walkGammaChallenge (labelCoordAt r st)

/-- **`RLC^γ(current_node)`, in-gate**: one-hot over the row's state. -/
def labelRLC (r : RowReader) : Expr := selSum r (labelRLCAt r)

/-- Host of child slot `j`'s state tag in state `st` (the overlay coordinates `2..4` freed by the
in-gate `cur`/`cc`/`cm`; Option A). -/
def childTagHost (r : RowReader) (st : State) : Fin 3 → Expr
  | 0 => pubFPR r (overlayANat st) 2
  | 1 => pubFPR r (overlayBNat st) 0
  | 2 => pubFPR r (overlayBNat st) 1

/-- Child slot `j`'s payload coordinate `k` in state `st`: its hosted tag, then `sf_j`'s
`(s, f, e)` (roles `3+3j .. 5+3j`) through the restored source. -/
def childCoordAt (r : RowReader) (st : State) (j : Fin 3) : Fin 10 → Expr
  | 0 => childTagHost r st j
  | 1 => sourcePubAtR r st (3 + 3 * (j : ℕ)) 0
  | 2 => sourcePubAtR r st (3 + 3 * (j : ℕ)) 1
  | 3 => sourcePubAtR r st (3 + 3 * (j : ℕ)) 2
  | 4 => sourcePubAtR r st (4 + 3 * (j : ℕ)) 0
  | 5 => sourcePubAtR r st (4 + 3 * (j : ℕ)) 1
  | 6 => sourcePubAtR r st (4 + 3 * (j : ℕ)) 2
  | 7 => sourcePubAtR r st (5 + 3 * (j : ℕ)) 0
  | 8 => sourcePubAtR r st (5 + 3 * (j : ℕ)) 1
  | 9 => sourcePubAtR r st (5 + 3 * (j : ℕ)) 2

def childRLCAt (r : RowReader) (st : State) (j : Fin 3) : Expr :=
  rlcExpr walkGammaChallenge (childCoordAt r st j)

/-- The paper's inner sum `Σ_{k=1}^{fanout} α^k · RLC^γ(children(i,k,·))` for fanout `fo`. -/
def childInnerSum (r : RowReader) (st : State) : ℕ → Expr
  | 0 => .Const 0
  | 1 => .Mul (.Pow walkAlphaChallenge 1) (childRLCAt r st 0)
  | 2 =>
      .Add (.Mul (.Pow walkAlphaChallenge 1) (childRLCAt r st 0))
        (.Mul (.Pow walkAlphaChallenge 2) (childRLCAt r st 1))
  | 3 =>
      .Add (.Mul (.Pow walkAlphaChallenge 1) (childRLCAt r st 0))
        (.Add (.Mul (.Pow walkAlphaChallenge 2) (childRLCAt r st 1))
          (.Mul (.Pow walkAlphaChallenge 3) (childRLCAt r st 2)))
  | _ => .Const 0

def childSumAt (r : RowReader) (st : State) : Expr := childInnerSum r st (fanoutComp st)

/-- **`cc`, in-gate**: `Σ_st sel(st) · Σ_{k=1}^{fanout(st)} α^k · RLC^γ(child_k)`
. -/
def childSumCC (r : RowReader) : Expr := selSum r (childSumAt r)

def cmAt (st : State) : Expr := .Pow walkAlphaChallenge (fanoutComp st)

/-- **`cm`, in-gate**: `Σ_st sel(st) · α^{fanout(st)}`. -/
def selectorCM (r : RowReader) : Expr := selSum r cmAt

/-- Every compute state has fanout ≤ 3. -/
theorem fanoutComp_le_three (st : State) : fanoutComp st ≤ 3 := by
  cases st <;> decide

/-! ## The deployed substitutions -/

/-- Production walk transition subst: `count`/`acc` stay overlay columns `0`/`1`, `ln` the walk
line; `cur`/`cc`/`cm` are in-gate on both rows (only the successor's are read by the walk
transitions). -/
def finalWalkSubstInGate : VarKind → ℕ → Expr
  | .traceCur, 0 => finalWalkLine .traceCur
  | .traceCur, 1 => overlayCoord .traceCur 0
  | .traceCur, 2 => overlayCoord .traceCur 1
  | .traceCur, 3 => labelRLC curReader
  | .traceCur, 4 => childSumCC curReader
  | .traceCur, 5 => selectorCM curReader
  | .traceNext, 0 => finalWalkLine .traceNext
  | .traceNext, 1 => overlayCoord .traceNext 0
  | .traceNext, 2 => overlayCoord .traceNext 1
  | .traceNext, 3 => labelRLC nextReader
  | .traceNext, 4 => childSumCC nextReader
  | .traceNext, 5 => selectorCM nextReader
  | .challenge, i => walkChallenge i
  | .publicVal, i => .Var .publicVal i
  | .traceCur, i => .Var .traceCur i
  | .traceNext, i => .Var .traceNext i

theorem finalWalkSubstInGate_next :
    finalWalkSubstInGate .traceNext 3 = labelRLC nextReader ∧
      finalWalkSubstInGate .traceNext 4 = childSumCC nextReader ∧
      finalWalkSubstInGate .traceNext 5 = selectorCM nextReader :=
  ⟨rfl, rfl, rfl⟩

theorem finalWalkSubstInGate_line :
    finalWalkSubstInGate .traceCur 0 = finalWalkLine .traceCur ∧
      finalWalkSubstInGate .traceNext 0 = finalWalkLine .traceNext ∧
      finalWalkSubstInGate .challenge 0 = walkChallenge 0 :=
  ⟨rfl, rfl, rfl⟩

/-! ## Honest evaluation (reader-generic)

The three in-gate quantities evaluate, on any row whose selectors are one-hot at `pub.state`
and whose restored sources are the genuine fingerprints, to the paper's values: `RLC^γ` of the
`LT_comp` label vector, the one-hot child sum, and `α^{fanout}`. -/

section HonestEval

variable {K : Type*} [Field K]

theorem selSum_eval (r : RowReader) (f : State → Expr) (env : Env K) (active : State)
    (hsel : ∀ st, (r.sel st).eval env = if st = active then 1 else 0) :
    (selSum r f).eval env = (f active).eval env := by
  have h0 := hsel .s0
  have h1 := hsel .s1
  have h2 := hsel .s2
  have h3 := hsel .s3
  have h4 := hsel .s4
  have h5 := hsel .s5
  have h6 := hsel .s6
  have h7 := hsel .s7
  have h8 := hsel .s8
  have h9 := hsel .s9
  have hc := hsel .cons
  cases active <;>
    simp at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hc <;>
    simp [selSum, allStates, Expr.eval, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hc]

theorem rlcExpr_eval (γ : Expr) (coords : Fin 10 → Expr) (env : Env K) :
    (rlcExpr γ coords).eval env =
      Walk.rlc (node_size := 10) (γ.eval env) (fun k => (coords k).eval env) := by
  simp only [rlcExpr, List.ofFn_succ, List.ofFn_zero, List.foldr, Expr.eval]
  simp [Walk.rlc, Fin.sum_univ_succ]

/-- The row's own label RLC is `RLC^γ` of the paper's label vector. -/
theorem labelRLC_eval (r : RowReader) (env : Env K) (pub : Pub K) (g : K)
    (hsel : ∀ st, (r.sel st).eval env = if st = pub.state then 1 else 0)
    (hsrc : ∀ (role c : ℕ) (hr : role < 12) (hc : c < 3),
      (sourcePubAtR r pub.state role c).eval env =
        OptimizedComputeCodec.fpCoordinate
          (OptimizedComputeCodec.pubFingerprint pub ⟨role, hr⟩) ⟨c, hc⟩)
    (hγ : walkGammaChallenge.eval env = g) :
    (labelRLC r).eval env = Walk.rlc g (ComputeTable.labelVecOfPub pub) := by
  rw [labelRLC, selSum_eval r _ env pub.state hsel, labelRLCAt, rlcExpr_eval, hγ]
  congr 1
  funext k
  fin_cases k
  · simp [labelCoordAt, stateTagExpr, ComputeTable.labelVecOfPub, Expr.eval,
      NodeEncoding.computeStateTag_cast]
  · exact hsrc 0 0 (by decide) (by decide)
  · exact hsrc 0 1 (by decide) (by decide)
  · exact hsrc 0 2 (by decide) (by decide)
  · exact hsrc 1 0 (by decide) (by decide)
  · exact hsrc 1 1 (by decide) (by decide)
  · exact hsrc 1 2 (by decide) (by decide)
  · exact hsrc 2 0 (by decide) (by decide)
  · exact hsrc 2 1 (by decide) (by decide)
  · exact hsrc 2 2 (by decide) (by decide)

/-- The vector a parent declares for child slot `j`: the hosted tag, then `sf_j`. -/
def childVec (pub : Pub K) (tags : Fin 3 → K) (j : Fin 3) : Fin 10 → K
  | 0 => tags j
  | 1 => (sfTriple pub j).1.size
  | 2 => (sfTriple pub j).1.dyck
  | 3 => (sfTriple pub j).1.leaf
  | 4 => (sfTriple pub j).2.1.size
  | 5 => (sfTriple pub j).2.1.dyck
  | 6 => (sfTriple pub j).2.1.leaf
  | 7 => (sfTriple pub j).2.2.size
  | 8 => (sfTriple pub j).2.2.dyck
  | 9 => (sfTriple pub j).2.2.leaf

/-- `childVec` at a natural slot index; out-of-range slots read the zero vector. -/
def childVecN (pub : Pub K) (tags : Fin 3 → K) : ℕ → Fin 10 → K
  | 0 => childVec pub tags 0
  | 1 => childVec pub tags 1
  | 2 => childVec pub tags 2
  | _ => fun _ => 0

theorem childVecN_fin (pub : Pub K) (tags : Fin 3 → K) (j : Fin 3) :
    childVecN pub tags j = childVec pub tags j := by
  fin_cases j <;> rfl

theorem childRLCAt_eval (r : RowReader) (env : Env K) (pub : Pub K) (g : K)
    (tags : Fin 3 → K) (j : Fin 3)
    (hsrc : ∀ (role c : ℕ) (hr : role < 12) (hc : c < 3),
      (sourcePubAtR r pub.state role c).eval env =
        OptimizedComputeCodec.fpCoordinate
          (OptimizedComputeCodec.pubFingerprint pub ⟨role, hr⟩) ⟨c, hc⟩)
    (hγ : walkGammaChallenge.eval env = g)
    (htag : (childTagHost r pub.state j).eval env = tags j) :
    (childRLCAt r pub.state j).eval env = Walk.rlc g (childVec pub tags j) := by
  rw [childRLCAt, rlcExpr_eval, hγ]
  congr 1
  funext k
  have hj := j.isLt
  have h1 := hsrc (3 + 3 * (j : ℕ)) 0 (by omega) (by decide)
  have h2 := hsrc (3 + 3 * (j : ℕ)) 1 (by omega) (by decide)
  have h3 := hsrc (3 + 3 * (j : ℕ)) 2 (by omega) (by decide)
  have h4 := hsrc (4 + 3 * (j : ℕ)) 0 (by omega) (by decide)
  have h5 := hsrc (4 + 3 * (j : ℕ)) 1 (by omega) (by decide)
  have h6 := hsrc (4 + 3 * (j : ℕ)) 2 (by omega) (by decide)
  have h7 := hsrc (5 + 3 * (j : ℕ)) 0 (by omega) (by decide)
  have h8 := hsrc (5 + 3 * (j : ℕ)) 1 (by omega) (by decide)
  have h9 := hsrc (5 + 3 * (j : ℕ)) 2 (by omega) (by decide)
  fin_cases j <;> fin_cases k <;>
    first
    | exact htag
    | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 | exact h7 | exact h8
    | exact h9

/-- The in-gate `cc` is the paper's one-hot child sum over the declared payloads. -/
theorem childSumCC_eval (r : RowReader) (env : Env K) (pub : Pub K) (a g : K)
    (tags : Fin 3 → K)
    (hsel : ∀ st, (r.sel st).eval env = if st = pub.state then 1 else 0)
    (hsrc : ∀ (role c : ℕ) (hr : role < 12) (hc : c < 3),
      (sourcePubAtR r pub.state role c).eval env =
        OptimizedComputeCodec.fpCoordinate
          (OptimizedComputeCodec.pubFingerprint pub ⟨role, hr⟩) ⟨c, hc⟩)
    (hα : walkAlphaChallenge.eval env = a)
    (hγ : walkGammaChallenge.eval env = g)
    (htag : ∀ j, (childTagHost r pub.state j).eval env = tags j) :
    (childSumCC r).eval env =
      ∑ l ∈ Finset.Icc 1 (fanoutComp pub.state),
        a ^ l * Walk.rlc g (childVecN pub tags (l - 1)) := by
  rw [childSumCC, selSum_eval r _ env pub.state hsel, childSumAt]
  have c0 := childRLCAt_eval r env pub g tags 0 hsrc hγ (htag 0)
  have c1 := childRLCAt_eval r env pub g tags 1 hsrc hγ (htag 1)
  have c2 := childRLCAt_eval r env pub g tags 2 hsrc hγ (htag 2)
  rw [Walk.sum_Icc_one_eq_range]
  cases hs : pub.state <;>
    simp only [hs] at c0 c1 c2 ⊢ <;>
    simp [fanoutComp, childInnerSum, Expr.eval, hα, c0, c1, c2, childVecN,
      Finset.sum_range_succ] <;>
    ring

/-- The in-gate `cm` is `α^{fanout(state)}`. -/
theorem selectorCM_eval (r : RowReader) (env : Env K) (pub : Pub K) (a : K)
    (hsel : ∀ st, (r.sel st).eval env = if st = pub.state then 1 else 0)
    (hα : walkAlphaChallenge.eval env = a) :
    (selectorCM r).eval env = a ^ fanoutComp pub.state := by
  rw [selectorCM, selSum_eval r _ env pub.state hsel, cmAt]
  simp [Expr.eval, hα]

/-! ### Transport of the successor-row forms onto the shifted environment -/

theorem sel_eval_next (env : Env K) (st : State) :
    (nextReader.sel st).eval env = (curReader.sel st).eval (shiftNext env) := rfl

theorem gamma_eval_shift (env : Env K) :
    walkGammaChallenge.eval (shiftNext env) = walkGammaChallenge.eval env := rfl

theorem alpha_eval_shift (env : Env K) :
    walkAlphaChallenge.eval (shiftNext env) = walkAlphaChallenge.eval env := rfl

theorem childTagHost_next_eval (env : Env K) (st : State) (j : Fin 3) :
    (childTagHost nextReader st j).eval env =
      (childTagHost curReader st j).eval (shiftNext env) := by
  fin_cases j <;> simp [childTagHost, pubFPR, nextReader, curReader, shiftNext, Expr.eval]

theorem labelRLCAt_next_eval (env : Env K) (st : State) :
    (labelRLCAt nextReader st).eval env = (labelRLCAt curReader st).eval (shiftNext env) := by
  rw [labelRLCAt, labelRLCAt, rlcExpr_eval, rlcExpr_eval, gamma_eval_shift]
  congr 1
  funext k
  fin_cases k <;> first | rfl | exact sourcePubAtR_next_eval env st _ _

theorem labelRLC_next_eval (env : Env K) :
    (labelRLC nextReader).eval env = (labelRLC curReader).eval (shiftNext env) := by
  simp only [labelRLC, selSum, allStates, List.foldr, Expr.eval, sel_eval_next,
    labelRLCAt_next_eval]

theorem childRLCAt_next_eval (env : Env K) (st : State) (j : Fin 3) :
    (childRLCAt nextReader st j).eval env = (childRLCAt curReader st j).eval (shiftNext env) := by
  rw [childRLCAt, childRLCAt, rlcExpr_eval, rlcExpr_eval, gamma_eval_shift]
  congr 1
  funext k
  fin_cases k <;>
    first
    | exact childTagHost_next_eval env st j
    | exact sourcePubAtR_next_eval env st _ _

theorem childSumAt_next_eval (env : Env K) (st : State) :
    (childSumAt nextReader st).eval env = (childSumAt curReader st).eval (shiftNext env) := by
  cases st <;>
    simp only [childSumAt, fanoutComp, childInnerSum, Expr.eval, alpha_eval_shift,
      childRLCAt_next_eval]

theorem childSumCC_next_eval (env : Env K) :
    (childSumCC nextReader).eval env = (childSumCC curReader).eval (shiftNext env) := by
  simp only [childSumCC, selSum, allStates, List.foldr, Expr.eval, sel_eval_next,
    childSumAt_next_eval]

theorem selectorCM_next_eval (env : Env K) :
    (selectorCM nextReader).eval env = (selectorCM curReader).eval (shiftNext env) := by
  simp only [selectorCM, selSum, allStates, List.foldr, Expr.eval, sel_eval_next, cmAt,
    alpha_eval_shift]

/-! ### Congruences: the current-row forms read trace columns below `71` only -/

theorem sourcePubAtR_first (st : State) (role coord : ℕ) :
    sourcePubAtR firstReader st role coord = sourcePubAtR curReader st role coord := by
  cases st <;> rfl

theorem childTagHost_first (st : State) (j : Fin 3) :
    childTagHost firstReader st j = childTagHost curReader st j := by
  fin_cases j <;> rfl

theorem sourcePubAtR_cur_eval_congr {env env' : Env K}
    (h : ∀ j, j < 71 → env.trace j = env'.trace j) (st : State) (role coord : ℕ)
    (hr : role < 12) (hc : coord < 3) :
    (sourcePubAtR curReader st role coord).eval env =
      (sourcePubAtR curReader st role coord).eval env' := by
  cases st <;>
    simp only [sourcePubAtR, restoredAFieldR, restoredBFieldR, restoredIOHostFieldR,
      restoredDenomHostFieldR, pubFPR, decFPR, curReader, overlayANat, overlayBNat, ext0] <;>
    split_ifs <;> simp_all [Expr.eval, eval_ite_aux] <;> (try split_ifs) <;> first | rfl | (apply h; omega)

theorem childTagHost_cur_eval_congr {env env' : Env K}
    (h : ∀ j, j < 71 → env.trace j = env'.trace j) (st : State) (j : Fin 3) :
    (childTagHost curReader st j).eval env = (childTagHost curReader st j).eval env' := by
  fin_cases j <;> cases st <;>
    simp only [childTagHost, pubFPR, curReader, overlayANat, overlayBNat, ext0, Expr.eval] <;>
    apply h <;> omega

/-- `sourcePubAtR` reads column `54` only for `s1`, role `2`, coord `2`.
Column `57` is never read.  Off that one triple the two environments may differ
at the Form R leaf columns. -/
theorem sourcePubAtR_cur_eval_congr_offLeaf {env env' : Env K}
    (h : ∀ j, j < 71 → j ≠ 54 → j ≠ 57 → env.trace j = env'.trace j)
    (st : State) (role coord : ℕ) (hr : role < 12) (hc : coord < 3)
    (hnot : st ≠ .s1 ∨ role ≠ 2 ∨ coord ≠ 2) :
    (sourcePubAtR curReader st role coord).eval env =
      (sourcePubAtR curReader st role coord).eval env' := by
  cases st with
  | s1 =>
      have hnot' : role ≠ 2 ∨ coord ≠ 2 := by
        rcases hnot with hst | hrole | hcoord
        · exact (hst rfl).elim
        · exact Or.inl hrole
        · exact Or.inr hcoord
      simp only [sourcePubAtR, restoredAFieldR, restoredBFieldR, restoredIOHostFieldR,
        restoredDenomHostFieldR, pubFPR, decFPR, curReader, overlayANat, overlayBNat, ext0]
      split_ifs <;> simp_all [Expr.eval, eval_ite_aux] <;> (try split_ifs) <;>
        first | rfl | (apply h <;> (try omega) <;> (try (rcases hnot' with hrole | hcoord <;> omega)))
  | _ =>
      simp only [sourcePubAtR, restoredAFieldR, restoredBFieldR, restoredIOHostFieldR,
        restoredDenomHostFieldR, pubFPR, decFPR, curReader, overlayANat, overlayBNat, ext0]
      split_ifs <;> simp_all [Expr.eval, eval_ite_aux] <;> (try split_ifs) <;> first | rfl | (apply h <;> omega)

/-- Child-tag hosts read public overlay columns `≤ 45`, never the Form R leaf columns `54`/`57`. -/
theorem childTagHost_cur_eval_congr_offLeaf {env env' : Env K}
    (h : ∀ j, j < 71 → j ≠ 54 → j ≠ 57 → env.trace j = env'.trace j) (st : State) (j : Fin 3) :
    (childTagHost curReader st j).eval env = (childTagHost curReader st j).eval env' := by
  fin_cases j <;> cases st <;>
    simp only [childTagHost, pubFPR, curReader, overlayANat, overlayBNat, ext0, Expr.eval] <;>
    apply h <;> omega

end HonestEval

end ComputeWalkLabel
end Nock.NockVMROM.Thm54
