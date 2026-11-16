/-
  Nock/AIRPacked.lean

  Paper-faithful **selector packing** of the compute-row evaluation / memory-record
  gates.

  The production `computeAIR` stays the atomic expansion (`perStateGated`, 526 constraints).
  This module is the optimal packing: one polynomial per `(slot, component)` of the
  equality table,

      Σ_k op_k · (slot − target_k) = 0

  plus the paper's four-way nonlinear fold `Σ op_k · (G_k − 1) = 0`, plus packed `mr2`/`mr3`/`ln` and the two `cons`
  identities.  Perfect soundness given the one-hot SV block; no Schwartz–Zippel.

  FLAG `[combined-op8-factor]`: the paper display at 2016 omits `input_subject.size` from
  EC.8.1 (2000); this fold keeps the actual 3-factor gate.
-/
import Nock.AIR

namespace Nock
namespace Reified

open ComputeTable
open Classical
attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K]
variable (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K)

set_option linter.unusedSimpArgs false

/-! ## 1. Selector-sum combinators -/

/-- Fold `Σ_i op_{k_i} · e_i`. -/
def selSum : List (State × Expr) → Expr
  | [] => .Const 0
  | p :: rest => .Add (gateBy p.1 p.2) (selSum rest)

/-- Paper packing of one scalar slot: `Σ_k op_k · (slot − target_k)`, omitting `⊥`. -/
def packSlot (f : State → Option Expr) : Expr :=
  selSum (allStates.filterMap (fun k => (f k).map (fun e => (k, e))))

/-- `Σ_k op_k · (slot − target_k)` with a per-opcode optional target. -/
def packComp (slot : Expr) (t : State → Option Expr) : Expr :=
  packSlot (fun k => (t k).map (fun u => .Sub slot u))

/-- The zero fingerprint `(0,0,0)` used as a table target (`sfz*`). -/
def zeroFP : FPExpr := ⟨.Const 0, .Const 0, .Const 0⟩

/-- The zero memory record used as a table target (`mr2`/`mr3` inactive). -/
def zeroMR : MemRecExpr := ⟨zeroFP, zeroFP, .Const 0, .Const 0⟩

/-- Pack three fingerprint components with a shared optional `FPExpr` target. -/
def packFP (slot : FPExpr) (t : State → Option FPExpr) : List Expr :=
  [packComp slot.size (fun k => (t k).map FPExpr.size),
   packComp slot.dyck (fun k => (t k).map FPExpr.dyck),
   packComp slot.leaf (fun k => (t k).map FPExpr.leaf)]

/-- Pack three fingerprint components with independent optional scalar targets
    (the `(z,0,⊥)` cells of `tab:V_comp_equality`). -/
def packFP3 (slot : FPExpr) (ts td tl : State → Option Expr) : List Expr :=
  [packComp slot.size ts, packComp slot.dyck td, packComp slot.leaf tl]

/-- Pack eight memory-record components with a shared optional `MemRecExpr` target. -/
def packMR (slot : MemRecExpr) (t : State → Option MemRecExpr) : List Expr :=
  packFP slot.root (fun k => (t k).map MemRecExpr.root) ++
  packFP slot.child (fun k => (t k).map MemRecExpr.child) ++
  [packComp slot.axis (fun k => (t k).map MemRecExpr.axis),
   packComp slot.ts (fun k => (t k).map MemRecExpr.ts)]

/-- Sum of selector columns. -/
def selAdd : List State → Expr
  | [] => .Const 0
  | k :: rest => .Add (tc (opCol k)) (selAdd rest)

theorem allStates_nodup : allStates.Nodup := by decide

theorem gateBy_eval_opSel (st k : State) (e : Expr) :
    (gateBy k e).eval (computeEnvFull inp (opSel (K := K) st) pub dec ex)
      = if k = st then e.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex) else 0 := by
  unfold gateBy
  simp only [Expr.eval, eval_op, opSel, ite_mul, one_mul, zero_mul]

theorem selSum_filterMap_opSel (st : State) (f : State → Option Expr) :
    ∀ ks : List State, ks.Nodup →
      (selSum (ks.filterMap (fun k => (f k).map (fun e => (k, e))))).eval
          (computeEnvFull inp (opSel (K := K) st) pub dec ex)
        = if st ∈ ks then
            match f st with
            | some e => e.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex)
            | none => 0
          else 0 := by
  intro ks hnd
  induction ks with
  | nil => simp [selSum, Expr.eval]
  | cons k rest ih =>
    have ⟨hnin, hnd'⟩ := List.nodup_cons.mp hnd
    rw [List.filterMap_cons]
    cases hf : f k with
    | none =>
      simp only [hf, Option.map_none]
      rw [ih hnd']
      by_cases hst : st = k
      · subst hst
        simp [List.mem_cons, hnin, hf]
      · simp [List.mem_cons, hst, eq_comm]
    | some e =>
      simp only [hf, Option.map_some, selSum, Expr.eval]
      rw [gateBy_eval_opSel, ih hnd']
      by_cases hst : st = k
      · subst hst
        simp [List.mem_cons, hnin, hf]
      · simp [List.mem_cons, hst, eq_comm]

theorem packSlot_eval_opSel (st : State) (f : State → Option Expr) :
    (packSlot f).eval (computeEnvFull inp (opSel (K := K) st) pub dec ex)
      = match f st with
        | some e => e.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex)
        | none => 0 := by
  unfold packSlot
  rw [selSum_filterMap_opSel inp pub dec ex st f allStates allStates_nodup]
  simp [mem_allStates]

theorem packComp_eval_opSel (st : State) (slot : Expr) (t : State → Option Expr) :
    (packComp slot t).eval (computeEnvFull inp (opSel (K := K) st) pub dec ex)
      = match t st with
        | some u =>
            slot.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex)
              - u.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex)
        | none => 0 := by
  unfold packComp
  rw [packSlot_eval_opSel]
  cases t st <;> simp [Expr.eval]

theorem packFP_zero_opSel (st : State) (slot : FPExpr) (t : State → Option FPExpr) :
    (∀ e ∈ packFP slot t,
        e.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex) = 0) ↔
      match t st with
      | some u =>
          slot.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex)
            = u.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex)
      | none => True := by
  unfold packFP
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  rw [packComp_eval_opSel, packComp_eval_opSel, packComp_eval_opSel]
  cases t st with
  | none => simp
  | some u =>
    simp [sub_eq_zero, FP.ext_iff, FPExpr.eval_size, FPExpr.eval_dyck, FPExpr.eval_leaf]
    try tauto

theorem packFP3_zero_opSel (st : State) (slot : FPExpr)
    (ts td tl : State → Option Expr) :
    (∀ e ∈ packFP3 slot ts td tl,
        e.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex) = 0) ↔
      (match ts st with
        | some u => slot.size.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex) = u.eval
            (computeEnvFull inp (opSel (K := K) st) pub dec ex)
        | none => True) ∧
      (match td st with
        | some u => slot.dyck.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex) = u.eval
            (computeEnvFull inp (opSel (K := K) st) pub dec ex)
        | none => True) ∧
      (match tl st with
        | some u => slot.leaf.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex) = u.eval
            (computeEnvFull inp (opSel (K := K) st) pub dec ex)
        | none => True) := by
  unfold packFP3
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  rw [packComp_eval_opSel, packComp_eval_opSel, packComp_eval_opSel]
  cases ts st <;> cases td st <;> cases tl st <;> simp only [sub_eq_zero]

theorem packMR_zero_opSel (st : State) (slot : MemRecExpr) (t : State → Option MemRecExpr) :
    (∀ e ∈ packMR slot t,
        e.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex) = 0) ↔
      match t st with
      | some u =>
          slot.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex)
            = u.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex)
      | none => True := by
  unfold packMR
  simp only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true]
  rw [packFP_zero_opSel, packFP_zero_opSel, packComp_eval_opSel, packComp_eval_opSel]
  cases t st with
  | none => simp
  | some u =>
    simp [sub_eq_zero, MemRec.ext_iff, MemRecExpr.eval_root, MemRecExpr.eval_child,
      MemRecExpr.eval_axis, MemRecExpr.eval_ts]
    try tauto

theorem selAdd_eval_opSel (st : State) :
    ∀ ks : List State, ks.Nodup →
      (selAdd ks).eval (computeEnvFull inp (opSel (K := K) st) pub dec ex)
        = if st ∈ ks then 1 else 0 := by
  intro ks hnd
  induction ks with
  | nil => simp [selAdd, Expr.eval]
  | cons k rest ih =>
    have ⟨hnin, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [selAdd, Expr.eval, eval_op, opSel]
    rw [ih hnd']
    by_cases hst : st = k
    · subst hst
      simp [List.mem_cons, hnin]
    · simp [List.mem_cons, hst, eq_comm]

/-! ## 2. Equality-table targets -/

/-- `sf1_s` row.  s0/s1 → 0; s7 → `sf2_e`; s8 → `cons(sf2_e, s)`; else `s`. -/
def sf1sTarget : State → Option FPExpr
  | .s0 | .s1 => some zeroFP
  | .s7 => some cSf2e
  | .s8 => some (consExpr cSf2e cS)
  | .s2 | .s3 | .s4 | .s5 | .s6 | .s9 | .cons => some cS

/-- `sf1_f` row. -/
def sf1fTarget : State → Option FPExpr
  | .s0 | .s1 => some zeroFP
  | .s2 | .s5 => some cFth
  | .s3 | .s4 => some cFt
  | .s6 => some (fpBranchExpr cSf2e.leaf cFtth cFttt)
  | .s7 | .s8 | .s9 => some cFtt
  | .cons => some cFh

/-- `sf1_e` size: s0/s1 → 0; s4 → `z`; s6/s7/s8 → `e.size`; else `⊥`. -/
def sf1eSize : State → Option Expr
  | .s0 | .s1 => some (.Const 0)
  | .s4 => some (chl 1)
  | .s6 | .s7 | .s8 => some cE.size
  | _ => none

def sf1eDyck : State → Option Expr
  | .s0 | .s1 | .s4 => some (.Const 0)
  | .s6 | .s7 | .s8 => some cE.dyck
  | _ => none

def sf1eLeaf : State → Option Expr
  | .s0 | .s1 => some (.Const 0)
  | .s6 | .s7 | .s8 => some cE.leaf
  | _ => none

/-- `sf2_s` row. -/
def sf2sTarget : State → Option FPExpr
  | .s0 | .s1 | .s3 | .s4 => some zeroFP
  | .s9 => some cSf1e
  | .s2 | .s5 | .s6 | .s7 | .s8 | .cons => some cS

/-- `sf2_f` row.  s9 is `⊥`. -/
def sf2fTarget : State → Option FPExpr
  | .s0 | .s1 | .s3 | .s4 => some zeroFP
  | .s2 | .s5 => some cFtt
  | .s6 | .s7 | .s8 => some cFth
  | .cons => some cFt
  | .s9 => none

/-- `sf2_e`: s0/s1/s3/s4 → 0; s6 → `(z,0,⊥)`; else `⊥`. -/
def sf2eSize : State → Option Expr
  | .s0 | .s1 | .s3 | .s4 => some (.Const 0)
  | .s6 => some (chl 1)
  | _ => none

def sf2eDyck : State → Option Expr
  | .s0 | .s1 | .s3 | .s4 | .s6 => some (.Const 0)
  | _ => none

def sf2eLeaf : State → Option Expr
  | .s0 | .s1 | .s3 | .s4 => some (.Const 0)
  | _ => none

/-- `sf3_*`: s2 carries the OP2 triple; every other opcode zeros the slot. -/
def sf3sTarget : State → Option FPExpr
  | .s2 => some cSf1e
  | _ => some zeroFP

def sf3fTarget : State → Option FPExpr
  | .s2 => some cSf2e
  | _ => some zeroFP

def sf3eTarget : State → Option FPExpr
  | .s2 => some cE
  | _ => some zeroFP

/-- `f_t` row: only OP0 writes `(z,0,⊥)` (`memBlk` of s0; table cell, not `evalR`). -/
def ftSize : State → Option Expr
  | .s0 => some (chl 1)
  | _ => none

def ftDyck : State → Option Expr
  | .s0 => some (.Const 0)
  | _ => none

/-- `e` row.  s1 → `f_t`; s3/s5 → `(z,0,⊥)`; s4 → `inc(sf1_e)`; s9 → `sf2_e`;
    cons → `cons(sf1_e, sf2_e)`; s6/s7/s8 live on `sf1_e`; s2 lives on `sf3_e`. -/
def eSize : State → Option Expr
  | .s1 => some cFt.size
  | .s3 | .s5 => some (chl 1)
  | .s4 => some (incExpr cSf1e).size
  | .s9 => some cSf2e.size
  | .cons => some (consExpr cSf1e cSf2e).size
  | _ => none

def eDyck : State → Option Expr
  | .s1 => some cFt.dyck
  | .s3 | .s5 => some (.Const 0)
  | .s4 => some (incExpr cSf1e).dyck
  | .s9 => some cSf2e.dyck
  | .cons => some (consExpr cSf1e cSf2e).dyck
  | _ => none

def eLeaf : State → Option Expr
  | .s1 => some cFt.leaf
  | .s4 => some (incExpr cSf1e).leaf
  | .s9 => some cSf2e.leaf
  | .cons => some (consExpr cSf1e cSf2e).leaf
  | _ => none

/-- Packed equality table: one polynomial per `(slot, component)`. -/
def evalPacked : List Expr :=
  packFP cSf1s sf1sTarget ++
  packFP cSf1f sf1fTarget ++
  packFP3 cSf1e sf1eSize sf1eDyck sf1eLeaf ++
  packFP cSf2s sf2sTarget ++
  packFP cSf2f sf2fTarget ++
  packFP3 cSf2e sf2eSize sf2eDyck sf2eLeaf ++
  packFP cSf3s sf3sTarget ++
  packFP cSf3f sf3fTarget ++
  packFP cSf3e sf3eTarget ++
  [packComp cFt.size ftSize, packComp cFt.dyck ftDyck] ++
  packFP3 cE eSize eDyck eLeaf

/-! ## 3. Extra nonlinear gates, still selector-gated except the four-way fold -/

/-- Selector-activated transcription of the paper's four-way nonlinear fold.  Copied from `combinedSourceExpr` (`OptimizedComputeGateBasis`):
    `Σ op_s · (G_s − 1) = 0`, so inactive opcodes contribute zero.  The OP8 term retains
    the corrected subject-size factor. -/
def combinedPackedExpr : Expr :=
  .Sub
    (.Add
      (.Add
        (.Add
          (.Mul (tc 3)
            (.Add (.Mul (tc 92) (.Sub (chl 1) cSf1e.size))
              cE.leaf))
          (.Mul (tc 5)
            (.Mul (tc 92)
              (.Add
                (.Add
                  (.Add (.Mul (chl 2)
                    (.Sub cSf1e.size cSf2e.size))
                    (.Mul (chl 3)
                      (.Sub cSf1e.dyck cSf2e.dyck)))
                  (.Mul (chl 4)
                    (.Sub cSf1e.leaf cSf2e.leaf)))
                (.Sub (.Const 1) cE.leaf)))))
        (.Mul (tc 8)
          (.Mul (.Mul cSf2e.size cS.size) (tc 92))))
      (.Mul (tc 10)
        (.Mul (.Mul cSf1e.size cSf2e.size) (tc 92))))
    (.Add (.Add (.Add (tc 3) (tc 5)) (tc 8)) (tc 10))

/-- OP3/OP5 booleanity + quadratics (not the `= 1` gates, which the fold replaces),
    OP6 `sf2_e.leaf` booleanity, OP9 `f_th.size = z` / `f_th.dyck = 0`, plus the fold. -/
def extraPacked : List Expr :=
  [gateBy .s3 (.Mul cE.leaf (.Sub (.Const 1) cE.leaf)),
   gateBy .s3 (.Mul (tc 92)
     (.Sub (.Mul (tc 92) (.Sub (chl 1) cSf1e.size)) (.Const 1))),
   gateBy .s3 (.Mul (.Sub (chl 1) cSf1e.size)
     (.Sub (.Mul (tc 92) (.Sub (chl 1) cSf1e.size)) (.Const 1))),
   gateBy .s5 (.Mul cE.leaf (.Sub (.Const 1) cE.leaf)),
   gateBy .s5 (.Mul (.Sub (.Const 1) cE.leaf) (.Sub cSf1e.size cSf2e.size)),
   gateBy .s5 (.Mul (.Sub (.Const 1) cE.leaf) (.Sub cSf1e.dyck cSf2e.dyck)),
   gateBy .s5 (.Mul (.Sub (.Const 1) cE.leaf) (.Sub cSf1e.leaf cSf2e.leaf)),
   gateBy .s6 (.Mul cSf2e.leaf (.Sub (.Const 1) cSf2e.leaf)),
   gateBy .s9 (.Sub cFth.size (chl 1)),
   gateBy .s9 cFth.dyck,
   combinedPackedExpr]

/-! ## 4. Packed memory records and `ln` -/

/-- `mr2` is always some: OP0 the `(s, e, f_t.leaf)` record; `{2,5,6,7,8,9}` the
    `(f_t, f_th, 2)` record; else zero. -/
def mr2Target : State → MemRecExpr
  | .s0 => ⟨cS, cE, cFt.leaf, lnA2⟩
  | .s1 | .s3 | .s4 | .cons => zeroMR
  | .s2 | .s5 | .s6 | .s7 | .s8 | .s9 => ⟨cFt, cFth, .Const 2, lnA2⟩

/-- `mr3`: OP6 `(f_tt, f_tth, 2)`; OP9 `(sf1_e, sf2_f, f_th.leaf)`; else zero. -/
def mr3Target : State → MemRecExpr
  | .s6 => ⟨cFtt, cFtth, .Const 2, lnA3⟩
  | .s9 => ⟨cSf1e, cSf2f, cFth.leaf, lnA3⟩
  | _ => zeroMR

/-- `cons(f_th, f_tt) = f_t` over `{2,5,6,7,8,9}`. -/
def ftConsTarget : State → Option FPExpr
  | .s2 | .s5 | .s6 | .s7 | .s8 | .s9 => some cFt
  | _ => none

/-- `cons(f_tth, f_ttt) = f_tt` at OP6. -/
def fttConsTarget : State → Option FPExpr
  | .s6 => some cFtt
  | _ => none

/-- Packed `ln` recurrence.  The paper display omits `op_11` (cons);
    Lean places cons in the `α` group with `{1,3,4}` (`memBlkExprs`). -/
def lnPackedExpr : Expr :=
  .Sub (tc 66)
    (.Add (.Add (.Mul lnA1 (selAdd [.s1, .s3, .s4, .cons]))
                (.Mul lnA2 (selAdd [.s0, .s2, .s5, .s7, .s8])))
          (.Mul lnA3 (selAdd [.s6, .s9])))

def memPacked : List Expr :=
  packMR cMr2 (fun k => some (mr2Target k)) ++
  packMR cMr3 (fun k => some (mr3Target k)) ++
  packFP (consExpr cFth cFtt) ftConsTarget ++
  packFP (consExpr cFtth cFttt) fttConsTarget ++
  [lnPackedExpr]

/-- All packed per-row polynomials (equality table + extras + memory). -/
def allPacked : List Expr := evalPacked ++ extraPacked ++ memPacked

/-- Packed compute AIR.  Same always-on prefix as `computeAIR`; the 499 gated atomics
    are replaced by `allPacked`.  Production `computeAIR` is not swapped. -/
def computeAIRPacked : AIR where
  numTraceCols  := 94
  numChallenges := 5
  numPublic     := 0
  constraints :=
    (svExprs.map (fun e => ⟨.row, e⟩)) ++
    (formulaExprs.map (fun e => ⟨.row, e⟩)) ++
    (mr1Exprs.map (fun e => ⟨.row, e⟩)) ++
    [⟨.row, zZinvExpr⟩] ++
    (allPacked.map (fun e => ⟨.row, e⟩))

/-! ## 5. Honest-selector evaluation of the packed blocks -/

private abbrev envS (st : State) : Env K :=
  computeEnvFull inp (opSel (K := K) st) pub dec ex

theorem combinedPacked_eval (st : State) :
    combinedPackedExpr.eval (envS inp pub dec ex st)
      = match st with
        | .s3 =>
            (ex.invGen * (inp.z - pub.sf1_e.size) + pub.e.leaf) - 1
        | .s5 =>
            (ex.invGen *
              (inp.a * (pub.sf1_e.size - pub.sf2_e.size)
                + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
                + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf)
                + (1 - pub.e.leaf))) - 1
        | .s8 => (pub.sf2_e.size * pub.s.size * ex.invGen) - 1
        | .cons => (pub.sf1_e.size * pub.sf2_e.size * ex.invGen) - 1
        | _ => 0 := by
  unfold combinedPackedExpr envS
  cases st <;>
    simp [Expr.eval, eval_op, opSel, eval_invGen, eval_chZ, eval_chA, eval_chB, eval_chC,
      eval_cSf1e, eval_cSf2e, eval_cE, eval_cS, FPExpr.eval_size, FPExpr.eval_dyck,
      FPExpr.eval_leaf, Int.cast_one]

theorem lnPacked_eval (st : State) :
    lnPackedExpr.eval (envS inp pub dec ex st)
      = pub.ln -
          match st with
          | .s1 | .s3 | .s4 | .cons => pub.ln_prev * inp.α
          | .s0 | .s2 | .s5 | .s7 | .s8 => pub.ln_prev * inp.α ^ 2
          | .s6 | .s9 => pub.ln_prev * inp.α ^ 3 := by
  have h1 : ([.s1, .s3, .s4, .cons] : List State).Nodup := by decide
  have h2 : ([.s0, .s2, .s5, .s7, .s8] : List State).Nodup := by decide
  have h3 : ([.s6, .s9] : List State).Nodup := by decide
  unfold lnPackedExpr envS lnA1 lnA2 lnA3
  simp only [Expr.eval, eval_ln, eval_lnPrev, eval_chAlpha]
  rw [selAdd_eval_opSel inp pub dec ex st [.s1, .s3, .s4, .cons] h1,
      selAdd_eval_opSel inp pub dec ex st [.s0, .s2, .s5, .s7, .s8] h2,
      selAdd_eval_opSel inp pub dec ex st [.s6, .s9] h3]
  cases st <;> simp [List.mem_cons, List.not_mem_nil]

/-- At the honest selector, packed extras vanish iff the opcode's extra gates vanish. -/
theorem extraPacked_zero (st : State) :
    (∀ e ∈ extraPacked, e.eval (envS inp pub dec ex st) = 0) ↔
      match st with
      | .s3 =>
          pub.e.leaf * (1 - pub.e.leaf) = 0 ∧
          ex.invGen * (ex.invGen * (inp.z - pub.sf1_e.size) - 1) = 0 ∧
          (inp.z - pub.sf1_e.size) * (ex.invGen * (inp.z - pub.sf1_e.size) - 1) = 0 ∧
          ex.invGen * (inp.z - pub.sf1_e.size) + pub.e.leaf = 1
      | .s5 =>
          pub.e.leaf * (1 - pub.e.leaf) = 0 ∧
          (1 - pub.e.leaf) * (pub.sf1_e.size - pub.sf2_e.size) = 0 ∧
          (1 - pub.e.leaf) * (pub.sf1_e.dyck - pub.sf2_e.dyck) = 0 ∧
          (1 - pub.e.leaf) * (pub.sf1_e.leaf - pub.sf2_e.leaf) = 0 ∧
          ex.invGen *
            (inp.a * (pub.sf1_e.size - pub.sf2_e.size)
              + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
              + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf)
              + (1 - pub.e.leaf)) = 1
      | .s6 => pub.sf2_e.leaf * (1 - pub.sf2_e.leaf) = 0
      | .s8 => pub.sf2_e.size * pub.s.size * ex.invGen = 1
      | .s9 => dec.f_th.size = inp.z ∧ dec.f_th.dyck = 0
      | .cons => pub.sf1_e.size * pub.sf2_e.size * ex.invGen = 1
      | _ => True := by
  unfold extraPacked envS
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  simp only [gateBy_eval_opSel, combinedPacked_eval]
  cases st <;>
    simp [Expr.eval, eval_cE, eval_cSf1e, eval_cSf2e, eval_cS, eval_cFth, eval_invGen, eval_chZ,
      eval_chA, eval_chB, eval_chC, FPExpr.eval_size, FPExpr.eval_dyck, FPExpr.eval_leaf,
      Int.cast_one, sub_eq_zero]

/-! ## 6. Packed zeros ↔ atomic `memBlkExprs ++ evalRExprs` at the honest selector -/
set_option maxHeartbeats 800000

private lemma zeroFP_eval (env : Env K) : zeroFP.eval env = 0 := by
  simp [zeroFP, FPExpr.eval, Expr.eval, FP.ext_iff, FP.zero_size, FP.zero_dyck, FP.zero_leaf]

private lemma zeroMR_eval (env : Env K) : zeroMR.eval env = MemRec.zero := by
  simp [zeroMR, zeroFP, FPExpr.eval, Expr.eval, MemRec.zero, MemRec.ext_iff,
    MemRecExpr.eval_root, MemRecExpr.eval_child, MemRecExpr.eval_axis, MemRecExpr.eval_ts,
    FP.ext_iff, FP.zero_size, FP.zero_dyck, FP.zero_leaf]

/-- Honesty of the packed equality table at one opcode. -/
theorem evalPacked_zero (st : State) :
    (∀ e ∈ evalPacked, e.eval (envS inp pub dec ex st) = 0) ↔
      match st with
      | .s0 => sfz1 pub ∧ sfz2 pub ∧ sfz3 pub ∧ dec.f_t.size = inp.z ∧ dec.f_t.dyck = 0
      | .s1 => pub.e = dec.f_t ∧ sfz1 pub ∧ sfz2 pub ∧ sfz3 pub
      | .s2 => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_th ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_tt
          ∧ pub.sf3_s = pub.sf1_e ∧ pub.sf3_f = pub.sf2_e ∧ pub.e = pub.sf3_e
      | .s3 => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_t ∧ sfz2 pub ∧ sfz3 pub
          ∧ pub.e.size = inp.z ∧ pub.e.dyck = 0
      | .s4 => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_t ∧ pub.sf1_e.size = inp.z ∧ pub.sf1_e.dyck = 0
          ∧ sfz2 pub ∧ sfz3 pub ∧ pub.e = FP.inc inp.z pub.sf1_e
      | .s5 => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_th ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_tt
          ∧ sfz3 pub ∧ pub.e.size = inp.z ∧ pub.e.dyck = 0
      | .s6 => pub.sf1_s = pub.s
          ∧ pub.sf1_f = FP.add (FP.smul (1 - pub.sf2_e.leaf) dec.f_tth)
              (FP.smul pub.sf2_e.leaf dec.f_ttt)
          ∧ pub.e = pub.sf1_e ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_th
          ∧ pub.sf2_e.size = inp.z ∧ pub.sf2_e.dyck = 0 ∧ sfz3 pub
      | .s7 => pub.sf1_s = pub.sf2_e ∧ pub.sf1_f = dec.f_tt ∧ pub.e = pub.sf1_e
          ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_th ∧ sfz3 pub
      | .s8 => pub.sf1_s = FP.cons inp.z pub.sf2_e pub.s ∧ pub.sf1_f = dec.f_tt
          ∧ pub.e = pub.sf1_e ∧ pub.sf2_s = pub.s ∧ pub.sf2_f = dec.f_th ∧ sfz3 pub
      | .s9 => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_tt ∧ pub.sf2_s = pub.sf1_e
          ∧ pub.e = pub.sf2_e ∧ sfz3 pub
      | .cons => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_h ∧ pub.sf2_s = pub.s
          ∧ pub.sf2_f = dec.f_t ∧ pub.e = FP.cons inp.z pub.sf1_e pub.sf2_e ∧ sfz3 pub := by
  unfold evalPacked envS
  simp only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true]
  rw [packFP_zero_opSel, packFP_zero_opSel, packFP3_zero_opSel, packFP_zero_opSel,
      packFP_zero_opSel, packFP3_zero_opSel, packFP_zero_opSel, packFP_zero_opSel,
      packFP_zero_opSel, packComp_eval_opSel, packComp_eval_opSel, packFP3_zero_opSel]
  cases st <;> simp [sf1sTarget, sf1fTarget, sf1eSize, sf1eDyck, sf1eLeaf, sf2sTarget,
    sf2fTarget, sf2eSize, sf2eDyck, sf2eLeaf, sf3sTarget, sf3fTarget, sf3eTarget, ftSize,
    ftDyck, eSize, eDyck, eLeaf, zeroFP_eval, ComputeTable.sfz1, ComputeTable.sfz2,
    ComputeTable.sfz3, sub_eq_zero, eval_cS, eval_cE, eval_cSf1s, eval_cSf1f, eval_cSf1e,
    eval_cSf2s, eval_cSf2f, eval_cSf2e, eval_cSf3s, eval_cSf3f, eval_cSf3e, eval_cFh, eval_cFt,
    eval_cFth, eval_cFtt, eval_cFtth, eval_cFttt, eval_chZ, consExpr_eval, incExpr_eval,
    fpBranchExpr_eval, FP.ext_iff, FPExpr.eval_size, FPExpr.eval_dyck, FPExpr.eval_leaf,
    Expr.eval, Int.cast_one, Int.cast_zero]
  all_goals (
    try simp only [eq_comm (a := pub.sf3_e.size) (b := pub.e.size),
      eq_comm (a := pub.sf3_e.dyck) (b := pub.e.dyck),
      eq_comm (a := pub.sf3_e.leaf) (b := pub.e.leaf),
      eq_comm (a := pub.sf1_e.size) (b := pub.e.size),
      eq_comm (a := pub.sf1_e.dyck) (b := pub.e.dyck),
      eq_comm (a := pub.sf1_e.leaf) (b := pub.e.leaf)]
    try tauto)

theorem memPacked_zero (st : State) :
    (∀ e ∈ memPacked, e.eval (envS inp pub dec ex st) = 0) ↔
      match st with
      | .s0 => pub.mr2 = ⟨pub.s, pub.e, dec.f_t.leaf, pub.ln_prev * inp.α ^ 2⟩
          ∧ pub.mr3 = MemRec.zero ∧ pub.ln = pub.ln_prev * inp.α ^ 2
      | .s1 | .s3 | .s4 | .cons =>
          pub.mr2 = MemRec.zero ∧ pub.mr3 = MemRec.zero ∧ pub.ln = pub.ln_prev * inp.α
      | .s2 | .s5 | .s7 | .s8 =>
          pub.mr2 = ⟨dec.f_t, dec.f_th, 2, pub.ln_prev * inp.α ^ 2⟩
          ∧ FP.cons inp.z dec.f_th dec.f_tt = dec.f_t
          ∧ pub.mr3 = MemRec.zero ∧ pub.ln = pub.ln_prev * inp.α ^ 2
      | .s6 =>
          pub.mr2 = ⟨dec.f_t, dec.f_th, 2, pub.ln_prev * inp.α ^ 2⟩
          ∧ FP.cons inp.z dec.f_th dec.f_tt = dec.f_t
          ∧ pub.mr3 = ⟨dec.f_tt, dec.f_tth, 2, pub.ln_prev * inp.α ^ 3⟩
          ∧ FP.cons inp.z dec.f_tth dec.f_ttt = dec.f_tt
          ∧ pub.ln = pub.ln_prev * inp.α ^ 3
      | .s9 =>
          pub.mr2 = ⟨dec.f_t, dec.f_th, 2, pub.ln_prev * inp.α ^ 2⟩
          ∧ FP.cons inp.z dec.f_th dec.f_tt = dec.f_t
          ∧ pub.mr3 = ⟨pub.sf1_e, pub.sf2_f, dec.f_th.leaf, pub.ln_prev * inp.α ^ 3⟩
          ∧ pub.ln = pub.ln_prev * inp.α ^ 3 := by
  unfold memPacked envS
  simp only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true]
  rw [packMR_zero_opSel, packMR_zero_opSel, packFP_zero_opSel, packFP_zero_opSel]
  simp only [lnPacked_eval]
  cases st <;> simp [mr2Target, mr3Target, ftConsTarget, fttConsTarget, zeroMR_eval,
    zeroFP_eval, eval_cMr2, eval_cMr3, eval_cS, eval_cE, eval_cFt, eval_cFth, eval_cFtt,
    eval_cFtth, eval_cFttt, eval_cSf1e, eval_cSf2f, eval_lnPrev, eval_chAlpha, consExpr_eval,
    MemRecExpr.eval_mk, FPExpr.eval_mk, Expr.eval, Int.cast_ofNat, sub_eq_zero, MemRec.ext_iff,
    FP.ext_iff, MemRec.zero, lnA1, lnA2, lnA3]
  all_goals try tauto

/-- Packed per-row polynomials vanish at the honest selector iff the atomic
    `memBlkExprs ++ evalRExprs` block of that opcode vanishes. -/
theorem packed_iff_atomic (st : State) :
    (∀ e ∈ allPacked, e.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex) = 0)
      ↔ (∀ e ∈ memBlkExprs st ++ evalRExprs st,
            e.eval (computeEnvFull inp (opSel (K := K) st) pub dec ex) = 0) := by
  unfold allPacked
  simp only [List.forall_mem_append]
  rw [evalPacked_zero, extraPacked_zero, memPacked_zero]
  cases st <;> simp only [List.forall_mem_append]
  · rw [memBlkExprs_s0_sound, evalRExprs_s0_sound]; tauto
  · rw [memBlkExprs_s1_sound, evalRExprs_s1_sound]; tauto
  · rw [memBlkExprs_s2_sound, evalRExprs_s2_sound]; tauto
  · rw [memBlkExprs_s3_sound, evalRExprs_s3_sound]; tauto
  · rw [memBlkExprs_s4_sound, evalRExprs_s4_sound]; tauto
  · rw [memBlkExprs_s5_sound, evalRExprs_s5_sound]; tauto
  · rw [memBlkExprs_s6_sound, evalRExprs_s6_sound]; tauto
  · rw [memBlkExprs_s7_sound, evalRExprs_s7_sound]; tauto
  · rw [memBlkExprs_s8_sound, evalRExprs_s8_sound]; tauto
  · rw [memBlkExprs_s9_sound, evalRExprs_s9_sound]; tauto
  · rw [memBlkExprs_cons_sound, evalRExprs_cons_sound]; tauto

/-! ## 7. Packed AIR soundness (honest witness + free-selector form) -/

/-- Honest-witness reflection for the packed AIR.  Same shape as `computeAIR_sound`:
    packed constraints vanish at `opSel pub.state` iff `RAPcomp ∧ z ≠ 0`. -/
theorem computeAIRPacked_sound :
    (∀ c ∈ computeAIRPacked.constraints,
        c.expr.eval (computeEnvFull inp (opSel pub.state) pub dec ex) = 0)
      ↔ (RAPcomp inp pub dec ex ∧ inp.z ≠ 0) := by
  simp only [computeAIRPacked, List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  rw [reified_sv_sound, reified_formula_sound, reified_mr1_sound, zZinvExpr_eval,
    packed_iff_atomic inp pub dec ex pub.state, perState_sound]
  simp only [RAPcomp]
  tauto

theorem computeAIRPacked_toRAP
    (h : ∀ c ∈ computeAIRPacked.constraints,
        c.expr.eval (computeEnvFull inp (opSel pub.state) pub dec ex) = 0) :
    RAPcomp inp pub dec ex :=
  ((computeAIRPacked_sound inp pub dec ex).mp h).1

/-- Free-selector soundness, mirroring `computeAIR_sound_free`.  The SV prefix is identical,
    so the same `SV_pins_head` pin applies. -/
theorem computeAIRPacked_sound_free
    (op : State → K)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (h : ∀ c ∈ computeAIRPacked.constraints,
        c.expr.eval (computeEnvFull inp op pub dec ex) = 0) :
    ∃ s : State, op = opSel s ∧ RAPcomp inp { pub with state := s } dec ex ∧ inp.z ≠ 0 := by
  have hSV : ∀ e ∈ svExprs, e.eval (computeEnvFull inp op pub dec ex) = 0 := by
    intro e he
    have hmem : (⟨.row, e⟩ : Constraint) ∈ computeAIRPacked.constraints := by
      apply List.mem_append_left; apply List.mem_append_left
      apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    exact h ⟨.row, e⟩ hmem
  have hSVsat : SVsatFree inp op dec ex.consInv :=
    (reified_sv_sound_free inp op pub dec ex).mp hSV
  obtain ⟨s, hs, _hhead⟩ := SV_pins_head inp op pub dec ex.consInv hchar hSVsat
  subst hs
  exact ⟨s, rfl, (computeAIRPacked_sound inp { pub with state := s } dec ex).mp h⟩

#print axioms packed_iff_atomic
#print axioms computeAIRPacked_sound
#print axioms computeAIRPacked_sound_free

end Reified
end Nock
