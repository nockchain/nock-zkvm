/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestRows.lean

A row is built from a `RowN` (`HonestShape`) and the honest cell-row list `cells`:
  a cell noun `n` is the handle `(1, cells.idxOf n)`, an atom `v` is `(0, v)`.  The hosted columns:
  `v, β, v2, w, pr, z1`, OP6's branch `m`, OP8's subject `m`, OP9's arm `m`, and for OP5 the first
  difference of the two operands (`fdN`): leaves `x1 x2` in `f_tth / f_ttt`, the axis atom in `m`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestShape
import Nock.NockVMROM.Thm54.VclL.Handle.ChipH
import Nock.NockVMROM.Thm54.VclL.Handle.HashCons
import Nock.NockVMROM.Thm54.VclL.Handle.HonestLink

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Reified
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.VclL

/-! ## 1. The first difference of two nouns -/

/-- First difference: the path (head `false`, tail `true`) to the first place where the nouns differ
as leaves (not both cells), with the two nouns there. -/
def fdN : Noun → Noun → List Bool × Noun × Noun
  | .cell a1 a2, .cell b1 b2 =>
    if a1 = b1 then ((true :: (fdN a2 b2).1), (fdN a2 b2).2)
    else ((false :: (fdN a1 b1).1), (fdN a1 b1).2)
  | a, b => ([], a, b)

/-- The axis of a path. -/
def axisOfPath (p : List Bool) : ℕ := p.foldl (fun a b => 2 * a + (if b then 1 else 0)) 1

theorem fdN_spec : ∀ (a b : Noun), a ≠ b →
    ¬ ((fdN a b).2.1.isCell = true ∧ (fdN a b).2.2.isCell = true) ∧
    (fdN a b).2.1 ≠ (fdN a b).2.2 ∧
    ((fdN a b).1 = [] → (fdN a b).2.1 = a ∧ (fdN a b).2.2 = b) ∧
    ((fdN a b).1 ≠ [] → a.isCell = true ∧ b.isCell = true)
  | .atom x, .atom y, h => by simp [fdN, h, Noun.isCell]
  | .atom x, .cell y z, h => by simp [fdN, Noun.isCell]
  | .cell x y, .atom z, h => by simp [fdN, Noun.isCell]
  | .cell a1 a2, .cell b1 b2, h => by
    by_cases h1 : a1 = b1
    · have h2 : a2 ≠ b2 := fun h2 => h (by rw [h1, h2])
      have := fdN_spec a2 b2 h2
      simp only [fdN, h1, if_true]
      refine ⟨this.1, this.2.1, by simp, by simp [Noun.isCell]⟩
    · have := fdN_spec a1 b1 h1
      simp only [fdN, h1, if_false]
      refine ⟨this.1, this.2.1, by simp, by simp [Noun.isCell]⟩

theorem fdN_atomsLt {q : ℕ} : ∀ (a b : Noun), AtomsLt q a → AtomsLt q b →
    AtomsLt q (fdN a b).2.1 ∧ AtomsLt q (fdN a b).2.2
  | .atom x, .atom y, ha, hb => by simpa [fdN] using ⟨ha, hb⟩
  | .atom x, .cell y z, ha, hb => by simpa [fdN] using ⟨ha, hb⟩
  | .cell x y, .atom z, ha, hb => by simpa [fdN] using ⟨ha, hb⟩
  | .cell a1 a2, .cell b1 b2, ha, hb => by
    by_cases h1 : a1 = b1
    · simp only [fdN, h1, if_true]; exact fdN_atomsLt a2 b2 ha.right hb.right
    · simp only [fdN, h1, if_false]; exact fdN_atomsLt a1 b1 ha.left hb.left

/-! ## 2. Honest handles and rows -/

section Rows
variable {F : Type} [Field F]

/-- The honest handle of a noun: `(0, v)` for an atom, `(1, serial)` for a cell. -/
def hdl (cells : List Noun) (n : Noun) : F × F :=
  match n with
  | .atom v => (0, (v : F))
  | .cell _ _ => (1, (cells.idxOf n : F))

@[simp] theorem hdl_atom (cells : List Noun) (v : ℕ) : (hdl cells (.atom v) : F × F) = (0, (v : F)) := rfl
@[simp] theorem hdl_cell (cells : List Noun) (a b : Noun) :
    (hdl cells (.cell a b) : F × F) = (1, (cells.idxOf (.cell a b) : F)) := rfl

def atomVal : Noun → ℕ
  | .atom v => v
  | _ => 0

/-- The effective nouns of a row: OP5 hosts the first difference of its operands. -/
def hn (r : RowN) : RowN :=
  if r.op = 5 then
    { r with ftth := (fdN r.sf1 r.sf2).2.1, fttt := (fdN r.sf1 r.sf2).2.2,
             m := .atom (axisOfPath (fdN r.sf1 r.sf2).1) }
  else r

open Classical in
/-- `z1`: axis-1 local read (OP0 / OP9) or first difference at the root (OP5 "≠"). -/
noncomputable def z1v (r : RowN) : F :=
  if (r.op = 0 ∧ r.ft = .atom 1) ∨ (r.op = 9 ∧ r.fth = .atom 1) ∨
      (r.op = 5 ∧ r.e = .atom 1 ∧ (fdN r.sf1 r.sf2).1 = []) then 1 else 0

open Classical in
noncomputable def betav (r : RowN) : F := if r.op = 3 ∨ r.op = 5 then (atomVal r.e : F) else 0

open Classical in
noncomputable def vv (r : RowN) : F :=
  if r.op = 0 then (atomVal r.ft : F) else if r.op = 4 then (atomVal r.sf1 : F)
  else if r.op = 6 then (atomVal r.sf2 : F) else if r.op = 9 then (atomVal r.fth : F)
  else if r.op = 5 then (atomVal (fdN r.sf1 r.sf2).2.1 : F) else 0

open Classical in
noncomputable def v2v (r : RowN) : F :=
  if r.op = 4 then (atomVal r.e : F) else if r.op = 5 then (atomVal (fdN r.sf1 r.sf2).2.2 : F) else 0

open Classical in
noncomputable def wv (r : RowN) : F :=
  if r.op = 5 ∧ (fdN r.sf1 r.sf2).2.1.isCell = false ∧ (fdN r.sf1 r.sf2).2.2.isCell = false then
    ((atomVal (fdN r.sf1 r.sf2).2.1 : F) - (atomVal (fdN r.sf1 r.sf2).2.2 : F))⁻¹ else 0

open Classical in
noncomputable def prv (r : RowN) : F :=
  if r.op = 5 ∧ r.e = .atom 1 ∧ (fdN r.sf1 r.sf2).1 ≠ [] then 1 else 0

open Classical in
/-- **The honest base columns `0 .. 42` of a row** (`fst / lst` = the `isFirst / isLast` flags). -/
noncomputable def colVal (cells : List Noun) (r : RowN) (fst lst : F) : ℕ → F := fun i =>
  if i ≤ 10 then (if r.op = i then 1 else 0) else
  match i with
  | 11 => fst
  | 12 => lst
  | 13 => z1v r
  | 14 => vv r
  | 15 => betav r
  | 16 => v2v r
  | 17 => wv r
  | 18 => prv r
  | 19 => (hdl cells (hn r).s).1
  | 20 => (hdl cells (hn r).s).2
  | 21 => (hdl cells (hn r).f).1
  | 22 => (hdl cells (hn r).f).2
  | 23 => (hdl cells (hn r).e).1
  | 24 => (hdl cells (hn r).e).2
  | 25 => (hdl cells (hn r).sf1).1
  | 26 => (hdl cells (hn r).sf1).2
  | 27 => (hdl cells (hn r).sf2).1
  | 28 => (hdl cells (hn r).sf2).2
  | 29 => (hdl cells (hn r).fh).1
  | 30 => (hdl cells (hn r).fh).2
  | 31 => (hdl cells (hn r).ft).1
  | 32 => (hdl cells (hn r).ft).2
  | 33 => (hdl cells (hn r).fth).1
  | 34 => (hdl cells (hn r).fth).2
  | 35 => (hdl cells (hn r).ftt).1
  | 36 => (hdl cells (hn r).ftt).2
  | 37 => (hdl cells (hn r).ftth).1
  | 38 => (hdl cells (hn r).ftth).2
  | 39 => (hdl cells (hn r).fttt).1
  | 40 => (hdl cells (hn r).fttt).2
  | 41 => (hdl cells (hn r).m).1
  | 42 => (hdl cells (hn r).m).2
  | _ => 0

variable (cells : List Noun) (r : RowN) (fst lst : F)

@[simp] theorem cvOne (j : ℕ) (hj : j ≤ 10) : colVal cells r fst lst j = if r.op = j then 1 else 0 := by
  simp [colVal, hj]
@[simp] theorem cv11 : colVal cells r fst lst 11 = fst := by simp [colVal]
@[simp] theorem cv12 : colVal cells r fst lst 12 = lst := by simp [colVal]
@[simp] theorem cv13 : colVal cells r fst lst 13 = z1v r := by simp [colVal]
@[simp] theorem cv14 : colVal cells r fst lst 14 = vv r := by simp [colVal]
@[simp] theorem cv15 : colVal cells r fst lst 15 = betav r := by simp [colVal]
@[simp] theorem cv16 : colVal cells r fst lst 16 = v2v r := by simp [colVal]
@[simp] theorem cv17 : colVal cells r fst lst 17 = wv r := by simp [colVal]
@[simp] theorem cv18 : colVal cells r fst lst 18 = prv r := by simp [colVal]
@[simp] theorem cv19 : colVal cells r fst lst 19 = (hdl cells (hn r).s).1 := by simp [colVal]
@[simp] theorem cv20 : colVal cells r fst lst 20 = (hdl cells (hn r).s).2 := by simp [colVal]
@[simp] theorem cv21 : colVal cells r fst lst 21 = (hdl cells (hn r).f).1 := by simp [colVal]
@[simp] theorem cv22 : colVal cells r fst lst 22 = (hdl cells (hn r).f).2 := by simp [colVal]
@[simp] theorem cv23 : colVal cells r fst lst 23 = (hdl cells (hn r).e).1 := by simp [colVal]
@[simp] theorem cv24 : colVal cells r fst lst 24 = (hdl cells (hn r).e).2 := by simp [colVal]
@[simp] theorem cv25 : colVal cells r fst lst 25 = (hdl cells (hn r).sf1).1 := by simp [colVal]
@[simp] theorem cv26 : colVal cells r fst lst 26 = (hdl cells (hn r).sf1).2 := by simp [colVal]
@[simp] theorem cv27 : colVal cells r fst lst 27 = (hdl cells (hn r).sf2).1 := by simp [colVal]
@[simp] theorem cv28 : colVal cells r fst lst 28 = (hdl cells (hn r).sf2).2 := by simp [colVal]
@[simp] theorem cv29 : colVal cells r fst lst 29 = (hdl cells (hn r).fh).1 := by simp [colVal]
@[simp] theorem cv30 : colVal cells r fst lst 30 = (hdl cells (hn r).fh).2 := by simp [colVal]
@[simp] theorem cv31 : colVal cells r fst lst 31 = (hdl cells (hn r).ft).1 := by simp [colVal]
@[simp] theorem cv32 : colVal cells r fst lst 32 = (hdl cells (hn r).ft).2 := by simp [colVal]
@[simp] theorem cv33 : colVal cells r fst lst 33 = (hdl cells (hn r).fth).1 := by simp [colVal]
@[simp] theorem cv34 : colVal cells r fst lst 34 = (hdl cells (hn r).fth).2 := by simp [colVal]
@[simp] theorem cv35 : colVal cells r fst lst 35 = (hdl cells (hn r).ftt).1 := by simp [colVal]
@[simp] theorem cv36 : colVal cells r fst lst 36 = (hdl cells (hn r).ftt).2 := by simp [colVal]
@[simp] theorem cv37 : colVal cells r fst lst 37 = (hdl cells (hn r).ftth).1 := by simp [colVal]
@[simp] theorem cv38 : colVal cells r fst lst 38 = (hdl cells (hn r).ftth).2 := by simp [colVal]
@[simp] theorem cv39 : colVal cells r fst lst 39 = (hdl cells (hn r).fttt).1 := by simp [colVal]
@[simp] theorem cv40 : colVal cells r fst lst 40 = (hdl cells (hn r).fttt).2 := by simp [colVal]
@[simp] theorem cv41 : colVal cells r fst lst 41 = (hdl cells (hn r).m).1 := by simp [colVal]
@[simp] theorem cv42 : colVal cells r fst lst 42 = (hdl cells (hn r).m).2 := by simp [colVal]


/-! ## 3. Gate evaluation over the `ℚ` template -/

/-- Evaluation of a `ℚ`-template gate in `F`: constants are cast. -/
def evalQ : CoeffExpr ℚ → Env F → F
  | .const c, _ => (c : F)
  | .var .traceCur i, env => env.trace i
  | .var .traceNext i, env => env.traceNext i
  | .var .challenge i, env => env.chal i
  | .var .publicVal i, env => env.pub i
  | .add a b, env => evalQ a env + evalQ b env
  | .sub a b, env => evalQ a env - evalQ b env
  | .mul a b, env => evalQ a env * evalQ b env
  | .neg a, env => - evalQ a env
  | .pow a n, env => (evalQ a env) ^ n

theorem eval_mapC_cast (g : CoeffExpr ℚ) (env : Env F) :
    (mapC (fun q : ℚ => (q : F)) g).eval env = evalQ g env := by
  induction g with
  | const c => rfl
  | var k i => cases k <;> rfl
  | add a b iha ihb => simp only [mapC, CoeffExpr.eval, evalQ, iha, ihb]
  | sub a b iha ihb => simp only [mapC, CoeffExpr.eval, evalQ, iha, ihb]
  | mul a b iha ihb => simp only [mapC, CoeffExpr.eval, evalQ, iha, ihb]
  | neg a iha => simp only [mapC, CoeffExpr.eval, evalQ, iha]
  | pow a n iha => simp only [mapC, CoeffExpr.eval, evalQ, iha]

theorem evalQ_sumList {ι : Type} (l : List ι) (f : ι → CoeffExpr ℚ) (env : Env F) :
    evalQ (CoeffExpr.sumList l f) env = (l.map fun i => evalQ (f i) env).sum := by
  induction l with
  | nil => simp [CoeffExpr.sumList, evalQ]
  | cons a l ih => simp only [CoeffExpr.sumList, List.foldr_cons, evalQ] at ih ⊢; simp [ih]

theorem evalQ_prodL (l : List (CoeffExpr ℚ)) (env : Env F) :
    evalQ (prodL l) env = (l.map fun g => evalQ g env).prod := by
  induction l with
  | nil => simp [prodL, evalQ]
  | cons a l ih => simp only [prodL, List.foldr_cons, evalQ] at ih ⊢; simp [ih]

theorem hn_of_ne (r : RowN) (h : r.op ≠ 5) : hn r = r := by simp [hn, h]

/-- The honest environment of a row (next-row and coin columns are not read by base gates). -/
noncomputable def hEnv (cells : List Noun) (r : RowN) (fst lst : F) (pub : ℕ → F) : Env F :=
  ⟨colVal cells r fst lst, colVal cells r fst lst, fun _ => 0, pub⟩


theorem hdl_k_cell (cells : List Noun) {n : Noun} (h : n.isCell = true) : (hdl cells n : F × F).1 = 1 := by
  cases n with
  | atom _ => simp [Noun.isCell] at h
  | cell _ _ => rfl

theorem hdl_k_atom (cells : List Noun) {n : Noun} (h : n.isCell = false) : (hdl cells n : F × F).1 = 0 := by
  cases n with
  | atom _ => rfl
  | cell _ _ => simp [Noun.isCell] at h

theorem hdl_bool (cells : List Noun) (n : Noun) :
    (hdl cells n : F × F).1 = 0 ∨ (hdl cells n : F × F).1 - 1 = 0 := by
  cases n <;> simp

theorem slot_cell : ∀ (ax : ℕ) (s e : Noun), Noun.slot ax s = some e → ax ≠ 1 → s.isCell = true := by
  intro ax
  induction ax using Nat.strong_induction_on with
  | _ ax ih =>
    intro s e h hax
    match ax, ih, h, hax with
    | 0, _, h, _ => simp [Noun.slot] at h
    | 1, _, _, hax => exact absurd rfl hax
    | a + 2, ih, h, _ =>
      rw [Noun.slot] at h
      cases hs : Noun.slot ((a + 2) / 2) s with
      | none => rw [hs] at h; simp at h
      | some v =>
        cases v with
        | atom _ => rw [hs] at h; simp at h
        | cell l r =>
          by_cases h1 : (a + 2) / 2 = 1
          · rw [h1] at hs; simp [Noun.slot] at hs; subst hs; rfl
          · exact ih _ (by omega) s _ hs h1

theorem onehot_bool (cells : List Noun) (r : RowN) (fst lst : F) :
    ∀ j < 11, colVal cells r fst lst j = 0 ∨ colVal cells r fst lst j - 1 = 0 := by
  intro j hj
  rw [cvOne cells r fst lst j (by omega)]
  by_cases h : r.op = j <;> simp [h]

section Exp
variable (cells : List Noun) (r : RowN) (fst lst : F) (pub : ℕ → F)


open Lean in
macro "gsimp" : tactic => `(tactic| simp [evalQ, evalQ_sumList, evalQ_prodL, cc, notC, selS, neGate, prGate,
    hEnv, hS, hF, hE, hSf1, hSf2, hFh, hFt, hFth, hFtt, hFtth, hFttt, hM, hd, consCol, z1C, vC, betaC,
    v2C, wC, prC, allHandles, l2States, hn, atomVal, Noun.tis, z1v, betav, vv, v2v, wv, prv, hdl_bool, onehot_bool,
    hdl_k_cell, hdl_k_atom, List.range_succ, *])

theorem forall_lt_true_of {P : ℕ → Prop} {n : ℕ} (h : ∀ j < n, P j) : (∀ j < n, P j) ↔ True :=
  ⟨fun _ => trivial, fun _ => h⟩

theorem oh_gate : ∀ j < 11, evalQ ((cc j).mul ((cc j).sub (CoeffExpr.const 1)))
    (hEnv cells r fst lst pub) = (0 : F) := by
  intro j hj
  rcases onehot_bool cells r fst lst j hj with h | h
  · simp [evalQ, cc, hEnv, h]
  · have h' : colVal cells r fst lst j = 1 := sub_eq_zero.mp h
    simp [evalQ, cc, hEnv, h']

open Lean in
macro "gsimp2" : tactic => `(tactic| simp [evalQ, evalQ_sumList, evalQ_prodL, cc, notC, selS,
    hEnv, hS, hF, hE, hSf1, hSf2, hFh, hFt, hFth, hFtt, hFtth, hFttt, hM, hd, consCol, z1C, vC, betaC,
    v2C, wC, prC, allHandles, l2States, hn, atomVal, z1v, betav, vv, v2v, wv, prv,
    EqG.gate, Opnd.expr, Noun.tis, firstCol, lastCol, sub_eq_zero, hdl_k_cell, hdl_k_atom, *])

theorem arith_hold (hs : r.Sem)
    (hA : AtomsLt (ringChar F) r.sf1 ∧ AtomsLt (ringChar F) r.sf2) :
    ∀ g ∈ (arithGates : List (CoeffExpr ℚ)), evalQ g (hEnv cells r fst lst pub) = 0 := by
  simp only [arithGates, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_range, forall_lt_true_of (oh_gate cells r fst lst pub)]
  match hop : r.op with
  | 1 =>
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    gsimp
  | 0 =>
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, ax, h3, h4⟩ := hs
    gsimp
    by_cases hax : ax = 1
    · simp [hax]
    · have hc := slot_cell ax r.s r.e h4 hax
      simp [hax, hdl_k_cell cells hc]
  | 2 =>
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    gsimp
  | 3 =>
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    gsimp
    rcases hs1 : r.sf1 with x | ⟨a, b⟩ <;> simp [hs1, Noun.wut]
  | 4 =>
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, n, h3, h4⟩ := hs
    gsimp
  | 5 =>
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, h3, h4⟩ := hs
    by_cases hd : r.sf1 = r.sf2
    · gsimp
    · obtain ⟨hnc, hne, hz, hp⟩ := fdN_spec _ _ hd
      have hat := fdN_atomsLt (q := ringChar F) _ _ hA.1 hA.2
      have hdt : r.sf1.tis r.sf2 = atom 1 := by simp [Noun.tis, hd]
      rcases hfd : fdN r.sf1 r.sf2 with ⟨pp, x1, x2⟩
      simp only [hfd] at hnc hne hz hp hat
      gsimp
      have hatm : ∀ u u' : ℕ, x1 = atom u → x2 = atom u' → ((u : ℕ) : F) ≠ ((u' : ℕ) : F) := by
        intro u u' e1 e2 h
        exact hne (by rw [e1, e2, cast_inj_of_lt (hat.1 u (by simp [e1, Noun.leafList]))
          (hat.2 u' (by simp [e2, Noun.leafList])) h])
      by_cases hp0 : pp = []
      · obtain ⟨e1, e2⟩ := hz hp0
        rcases hx1 : x1 with u | ⟨a1, a2⟩ <;> rcases hx2 : x2 with u' | ⟨b1, b2⟩
        · simp [hp0, wv, hfd, Noun.isCell, mul_inv_cancel₀ (sub_ne_zero.mpr (hatm u u' hx1 hx2))]
        · rw [hx1] at e1; rw [hx2] at e2
          rw [← e1, ← e2]; simp [wv, Noun.isCell, hfd, hp0]
        · rw [hx1] at e1; rw [hx2] at e2
          rw [← e1, ← e2]; simp [wv, Noun.isCell, hfd, hp0]
        · rw [hx1, hx2] at hnc; simp [Noun.isCell] at hnc
      · have hc := hp hp0
        rcases hx1 : x1 with u | ⟨a1, a2⟩ <;> rcases hx2 : x2 with u' | ⟨b1, b2⟩
        · simp [hp0, wv, hfd, Noun.isCell, mul_inv_cancel₀ (sub_ne_zero.mpr (hatm u u' hx1 hx2)),
            hdl_k_cell cells hc.1, hdl_k_cell cells hc.2]
        · simp [hp0, wv, hfd, Noun.isCell, hdl_k_cell cells hc.1, hdl_k_cell cells hc.2]
        · simp [hp0, wv, hfd, Noun.isCell, hdl_k_cell cells hc.1, hdl_k_cell cells hc.2]
        · rw [hx1, hx2] at hnc; simp [Noun.isCell] at hnc
  | 6 =>
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
    gsimp
    rcases h6 with ⟨h6, -⟩ | ⟨h6, -⟩ <;> simp [h6]
  | 7 =>
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, h3, h4⟩ := hs
    gsimp
  | 8 =>
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, h3, h4, h5⟩ := hs
    gsimp
  | 9 =>
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, h3, h4, ax, h5, h6⟩ := hs
    gsimp
    by_cases hax : ax = 1
    · simp [hax]
    · have hc := slot_cell ax r.sf1 r.m h6 hax
      simp [hax, hdl_k_cell cells hc]
  | 10 =>
    simp only [RowN.Sem, hop] at hs
    obtain ⟨⟨a, b, h1⟩, h2, h3⟩ := hs
    gsimp
  | n + 11 => simp [RowN.Sem, hop] at hs


theorem eq_hold_1 (hs : r.Sem) (hop : r.op = 1)
    (hA : AtomsLt (ringChar F) r.sf1 ∧ AtomsLt (ringChar F) r.sf2)
    (hpb : fst = 0 ∨ (pub 0 = (hdl cells r.s).1 ∧ pub 1 = (hdl cells r.s).2 ∧
      pub 2 = (hdl cells r.f).1 ∧ pub 3 = (hdl cells r.f).2 ∧
      pub 4 = (hdl cells r.e).1 ∧ pub 5 = (hdl cells r.e).2)) :
    ∀ g ∈ (eqGates : List (EqG ℚ)), evalQ g.gate (hEnv cells r fst lst pub) = 0 := by
  unfold eqGates
  simp only [heq, hpub, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.append_assoc, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_nil, List.map_cons, List.map_nil, List.map_append, List.mem_cons,
    List.not_mem_nil, forall_eq_or_imp, forall_eq]
  rcases hpb with hf | ⟨q0, q1, q2, q3, q4, q5⟩
  all_goals
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    gsimp2

theorem eq_hold_0 (hs : r.Sem) (hop : r.op = 0)
    (hA : AtomsLt (ringChar F) r.sf1 ∧ AtomsLt (ringChar F) r.sf2)
    (hpb : fst = 0 ∨ (pub 0 = (hdl cells r.s).1 ∧ pub 1 = (hdl cells r.s).2 ∧
      pub 2 = (hdl cells r.f).1 ∧ pub 3 = (hdl cells r.f).2 ∧
      pub 4 = (hdl cells r.e).1 ∧ pub 5 = (hdl cells r.e).2)) :
    ∀ g ∈ (eqGates : List (EqG ℚ)), evalQ g.gate (hEnv cells r fst lst pub) = 0 := by
  unfold eqGates
  simp only [heq, hpub, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.append_assoc, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_nil, List.map_cons, List.map_nil, List.map_append, List.mem_cons,
    List.not_mem_nil, forall_eq_or_imp, forall_eq]
  rcases hpb with hf | ⟨q0, q1, q2, q3, q4, q5⟩
  all_goals
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, ax, h3, h4⟩ := hs
    gsimp2
    by_cases hax : ax = 1
    · subst hax
      have : r.e = r.s := by simpa [Noun.slot] using h4.symm
      simp [this]
    · simp [hax]

theorem eq_hold_2 (hs : r.Sem) (hop : r.op = 2)
    (hA : AtomsLt (ringChar F) r.sf1 ∧ AtomsLt (ringChar F) r.sf2)
    (hpb : fst = 0 ∨ (pub 0 = (hdl cells r.s).1 ∧ pub 1 = (hdl cells r.s).2 ∧
      pub 2 = (hdl cells r.f).1 ∧ pub 3 = (hdl cells r.f).2 ∧
      pub 4 = (hdl cells r.e).1 ∧ pub 5 = (hdl cells r.e).2)) :
    ∀ g ∈ (eqGates : List (EqG ℚ)), evalQ g.gate (hEnv cells r fst lst pub) = 0 := by
  unfold eqGates
  simp only [heq, hpub, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.append_assoc, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_nil, List.map_cons, List.map_nil, List.map_append, List.mem_cons,
    List.not_mem_nil, forall_eq_or_imp, forall_eq]
  rcases hpb with hf | ⟨q0, q1, q2, q3, q4, q5⟩
  all_goals
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    gsimp2

theorem eq_hold_3 (hs : r.Sem) (hop : r.op = 3)
    (hA : AtomsLt (ringChar F) r.sf1 ∧ AtomsLt (ringChar F) r.sf2)
    (hpb : fst = 0 ∨ (pub 0 = (hdl cells r.s).1 ∧ pub 1 = (hdl cells r.s).2 ∧
      pub 2 = (hdl cells r.f).1 ∧ pub 3 = (hdl cells r.f).2 ∧
      pub 4 = (hdl cells r.e).1 ∧ pub 5 = (hdl cells r.e).2)) :
    ∀ g ∈ (eqGates : List (EqG ℚ)), evalQ g.gate (hEnv cells r fst lst pub) = 0 := by
  unfold eqGates
  simp only [heq, hpub, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.append_assoc, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_nil, List.map_cons, List.map_nil, List.map_append, List.mem_cons,
    List.not_mem_nil, forall_eq_or_imp, forall_eq]
  rcases hpb with hf | ⟨q0, q1, q2, q3, q4, q5⟩
  all_goals
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    gsimp2
    rcases hs1 : r.sf1 with x | ⟨a, b⟩ <;> simp [hs1, Noun.wut]

theorem eq_hold_4 (hs : r.Sem) (hop : r.op = 4)
    (hA : AtomsLt (ringChar F) r.sf1 ∧ AtomsLt (ringChar F) r.sf2)
    (hpb : fst = 0 ∨ (pub 0 = (hdl cells r.s).1 ∧ pub 1 = (hdl cells r.s).2 ∧
      pub 2 = (hdl cells r.f).1 ∧ pub 3 = (hdl cells r.f).2 ∧
      pub 4 = (hdl cells r.e).1 ∧ pub 5 = (hdl cells r.e).2)) :
    ∀ g ∈ (eqGates : List (EqG ℚ)), evalQ g.gate (hEnv cells r fst lst pub) = 0 := by
  unfold eqGates
  simp only [heq, hpub, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.append_assoc, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_nil, List.map_cons, List.map_nil, List.map_append, List.mem_cons,
    List.not_mem_nil, forall_eq_or_imp, forall_eq]
  rcases hpb with hf | ⟨q0, q1, q2, q3, q4, q5⟩
  all_goals
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, n, h3, h4⟩ := hs
    gsimp2

theorem eq_hold_5 (hs : r.Sem) (hop : r.op = 5)
    (hA : AtomsLt (ringChar F) r.sf1 ∧ AtomsLt (ringChar F) r.sf2)
    (hpb : fst = 0 ∨ (pub 0 = (hdl cells r.s).1 ∧ pub 1 = (hdl cells r.s).2 ∧
      pub 2 = (hdl cells r.f).1 ∧ pub 3 = (hdl cells r.f).2 ∧
      pub 4 = (hdl cells r.e).1 ∧ pub 5 = (hdl cells r.e).2)) :
    ∀ g ∈ (eqGates : List (EqG ℚ)), evalQ g.gate (hEnv cells r fst lst pub) = 0 := by
  unfold eqGates
  simp only [heq, hpub, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.append_assoc, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_nil, List.map_cons, List.map_nil, List.map_append, List.mem_cons,
    List.not_mem_nil, forall_eq_or_imp, forall_eq]
  rcases hpb with hf | ⟨q0, q1, q2, q3, q4, q5⟩
  all_goals
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, h3, h4⟩ := hs
    by_cases hd : r.sf1 = r.sf2
    · gsimp2
    · obtain ⟨hnc, hne, hz, hp⟩ := fdN_spec _ _ hd
      have hdt : r.sf1.tis r.sf2 = atom 1 := by simp [Noun.tis, hd]
      rcases hfd : fdN r.sf1 r.sf2 with ⟨pp, x1, x2⟩
      simp only [hfd] at hnc hne hz hp
      gsimp2
      by_cases hp0 : pp = []
      · obtain ⟨e1, e2⟩ := hz hp0
        rcases hx1 : x1 with u | ⟨a1, a2⟩ <;> rcases hx2 : x2 with u' | ⟨b1, b2⟩
        all_goals first
          | (rw [hx1, hx2] at hnc; simp [Noun.isCell] at hnc; done)
          | (rw [hx1] at e1; rw [hx2] at e2; rw [← e1, ← e2]; simp [Noun.isCell, hp0]; done)
      · rcases hx1 : x1 with u | ⟨a1, a2⟩ <;> rcases hx2 : x2 with u' | ⟨b1, b2⟩
        all_goals first
          | (rw [hx1, hx2] at hnc; simp [Noun.isCell] at hnc; done)
          | simp [hp0]

theorem eq_hold_6 (hs : r.Sem) (hop : r.op = 6)
    (hA : AtomsLt (ringChar F) r.sf1 ∧ AtomsLt (ringChar F) r.sf2)
    (hpb : fst = 0 ∨ (pub 0 = (hdl cells r.s).1 ∧ pub 1 = (hdl cells r.s).2 ∧
      pub 2 = (hdl cells r.f).1 ∧ pub 3 = (hdl cells r.f).2 ∧
      pub 4 = (hdl cells r.e).1 ∧ pub 5 = (hdl cells r.e).2)) :
    ∀ g ∈ (eqGates : List (EqG ℚ)), evalQ g.gate (hEnv cells r fst lst pub) = 0 := by
  unfold eqGates
  simp only [heq, hpub, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.append_assoc, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_nil, List.map_cons, List.map_nil, List.map_append, List.mem_cons,
    List.not_mem_nil, forall_eq_or_imp, forall_eq]
  rcases hpb with hf | ⟨q0, q1, q2, q3, q4, q5⟩
  all_goals
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
    gsimp2
    rcases h6 with ⟨h6, h7⟩ | ⟨h6, h7⟩ <;> simp [h6, h7]

theorem eq_hold_7 (hs : r.Sem) (hop : r.op = 7)
    (hA : AtomsLt (ringChar F) r.sf1 ∧ AtomsLt (ringChar F) r.sf2)
    (hpb : fst = 0 ∨ (pub 0 = (hdl cells r.s).1 ∧ pub 1 = (hdl cells r.s).2 ∧
      pub 2 = (hdl cells r.f).1 ∧ pub 3 = (hdl cells r.f).2 ∧
      pub 4 = (hdl cells r.e).1 ∧ pub 5 = (hdl cells r.e).2)) :
    ∀ g ∈ (eqGates : List (EqG ℚ)), evalQ g.gate (hEnv cells r fst lst pub) = 0 := by
  unfold eqGates
  simp only [heq, hpub, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.append_assoc, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_nil, List.map_cons, List.map_nil, List.map_append, List.mem_cons,
    List.not_mem_nil, forall_eq_or_imp, forall_eq]
  rcases hpb with hf | ⟨q0, q1, q2, q3, q4, q5⟩
  all_goals
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, h3, h4⟩ := hs
    gsimp2

theorem eq_hold_8 (hs : r.Sem) (hop : r.op = 8)
    (hA : AtomsLt (ringChar F) r.sf1 ∧ AtomsLt (ringChar F) r.sf2)
    (hpb : fst = 0 ∨ (pub 0 = (hdl cells r.s).1 ∧ pub 1 = (hdl cells r.s).2 ∧
      pub 2 = (hdl cells r.f).1 ∧ pub 3 = (hdl cells r.f).2 ∧
      pub 4 = (hdl cells r.e).1 ∧ pub 5 = (hdl cells r.e).2)) :
    ∀ g ∈ (eqGates : List (EqG ℚ)), evalQ g.gate (hEnv cells r fst lst pub) = 0 := by
  unfold eqGates
  simp only [heq, hpub, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.append_assoc, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_nil, List.map_cons, List.map_nil, List.map_append, List.mem_cons,
    List.not_mem_nil, forall_eq_or_imp, forall_eq]
  rcases hpb with hf | ⟨q0, q1, q2, q3, q4, q5⟩
  all_goals
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, h3, h4, h5⟩ := hs
    gsimp2

theorem eq_hold_9 (hs : r.Sem) (hop : r.op = 9)
    (hA : AtomsLt (ringChar F) r.sf1 ∧ AtomsLt (ringChar F) r.sf2)
    (hpb : fst = 0 ∨ (pub 0 = (hdl cells r.s).1 ∧ pub 1 = (hdl cells r.s).2 ∧
      pub 2 = (hdl cells r.f).1 ∧ pub 3 = (hdl cells r.f).2 ∧
      pub 4 = (hdl cells r.e).1 ∧ pub 5 = (hdl cells r.e).2)) :
    ∀ g ∈ (eqGates : List (EqG ℚ)), evalQ g.gate (hEnv cells r fst lst pub) = 0 := by
  unfold eqGates
  simp only [heq, hpub, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.append_assoc, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_nil, List.map_cons, List.map_nil, List.map_append, List.mem_cons,
    List.not_mem_nil, forall_eq_or_imp, forall_eq]
  rcases hpb with hf | ⟨q0, q1, q2, q3, q4, q5⟩
  all_goals
    simp only [RowN.Sem, hop] at hs
    obtain ⟨h1, h2, h3, h4, ax, h5, h6⟩ := hs
    gsimp2
    by_cases hax : ax = 1
    · subst hax
      have : r.m = r.sf1 := by simpa [Noun.slot] using h6.symm
      simp [this]
    · simp [hax]

theorem eq_hold_10 (hs : r.Sem) (hop : r.op = 10)
    (hA : AtomsLt (ringChar F) r.sf1 ∧ AtomsLt (ringChar F) r.sf2)
    (hpb : fst = 0 ∨ (pub 0 = (hdl cells r.s).1 ∧ pub 1 = (hdl cells r.s).2 ∧
      pub 2 = (hdl cells r.f).1 ∧ pub 3 = (hdl cells r.f).2 ∧
      pub 4 = (hdl cells r.e).1 ∧ pub 5 = (hdl cells r.e).2)) :
    ∀ g ∈ (eqGates : List (EqG ℚ)), evalQ g.gate (hEnv cells r fst lst pub) = 0 := by
  unfold eqGates
  simp only [heq, hpub, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.append_assoc, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_nil, List.map_cons, List.map_nil, List.map_append, List.mem_cons,
    List.not_mem_nil, forall_eq_or_imp, forall_eq]
  rcases hpb with hf | ⟨q0, q1, q2, q3, q4, q5⟩
  all_goals
    simp only [RowN.Sem, hop] at hs
    obtain ⟨⟨a, b, h1⟩, h2, h3⟩ := hs
    gsimp2

theorem eq_hold (hs : r.Sem)
    (hA : AtomsLt (ringChar F) r.sf1 ∧ AtomsLt (ringChar F) r.sf2)
    (hpb : fst = 0 ∨ (pub 0 = (hdl cells r.s).1 ∧ pub 1 = (hdl cells r.s).2 ∧
      pub 2 = (hdl cells r.f).1 ∧ pub 3 = (hdl cells r.f).2 ∧
      pub 4 = (hdl cells r.e).1 ∧ pub 5 = (hdl cells r.e).2)) :
    ∀ g ∈ (eqGates : List (EqG ℚ)), evalQ g.gate (hEnv cells r fst lst pub) = 0 := by
  match hop : r.op with
  | 1 => exact eq_hold_1 cells r fst lst pub hs hop hA hpb
  | 0 => exact eq_hold_0 cells r fst lst pub hs hop hA hpb
  | 2 => exact eq_hold_2 cells r fst lst pub hs hop hA hpb
  | 3 => exact eq_hold_3 cells r fst lst pub hs hop hA hpb
  | 4 => exact eq_hold_4 cells r fst lst pub hs hop hA hpb
  | 5 => exact eq_hold_5 cells r fst lst pub hs hop hA hpb
  | 6 => exact eq_hold_6 cells r fst lst pub hs hop hA hpb
  | 7 => exact eq_hold_7 cells r fst lst pub hs hop hA hpb
  | 8 => exact eq_hold_8 cells r fst lst pub hs hop hA hpb
  | 9 => exact eq_hold_9 cells r fst lst pub hs hop hA hpb
  | 10 => exact eq_hold_10 cells r fst lst pub hs hop hA hpb
  | n + 11 => simp [RowN.Sem, hop] at hs


/-- The claim publics `0..5` of the honest trace: the handles of the root row's `s f e`. -/
def pubVec (cells : List Noun) (r0 : RowN) : ℕ → F := fun i =>
  match i with
  | 0 => (hdl cells r0.s).1
  | 1 => (hdl cells r0.s).2
  | 2 => (hdl cells r0.f).1
  | 3 => (hdl cells r0.f).2
  | 4 => (hdl cells r0.e).1
  | 5 => (hdl cells r0.e).2
  | _ => 0

/-- **The non-lookup BASE gates** of `computeChipVCLH` (arithmetic and equality gates), at the
chip's own `ℚ`-template transported along `Rat.cast`, vanish on the honest row. -/
theorem base_gates_hold (hs : r.Sem)
    (hA : AtomsLt (ringChar F) r.sf1 ∧ AtomsLt (ringChar F) r.sf2)
    (hpb : fst = 0 ∨ (pub 0 = (hdl cells r.s).1 ∧ pub 1 = (hdl cells r.s).2 ∧
      pub 2 = (hdl cells r.f).1 ∧ pub 3 = (hdl cells r.f).2 ∧
      pub 4 = (hdl cells r.e).1 ∧ pub 5 = (hdl cells r.e).2)) :
    ∀ g ∈ (arithGates : List (CoeffExpr ℚ)) ++ (eqGates : List (EqG ℚ)).map EqG.gate,
      (mapC (fun q : ℚ => (q : F)) g).eval (hEnv cells r fst lst pub) = 0 := by
  intro g hg
  rw [eval_mapC_cast]
  rcases List.mem_append.mp hg with h | h
  · exact arith_hold cells r fst lst pub hs hA g h
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    exact eq_hold cells r fst lst pub hs hA hpb e he

end Exp

end Rows

end Nock.NockVMROM.Thm54.VclL.Handle
