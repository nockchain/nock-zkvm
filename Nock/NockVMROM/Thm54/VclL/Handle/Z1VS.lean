/-
  Nock/NockVMROM/Thm54/VclL/Handle/Z1VS.lean

  Additive.

  `z1` (column `13` of `computeChipVCLH`) is constrained only on OP0 / OP5 / OP9 rows.  The receipt:
  OFF those rows (selectors `0, 5, 9` zero) no gate reads `z1`, except its own booleanity gate.

  * `zp`: zero propagation of the selector columns `{0, 5, 9}` (a partial evaluator: `none` = the
    expression is identically `0` when the three selectors are); `zp_eval` (sound, through the `ℚ → 𝔽` constant
    transport, at every env with `s0 = s5 = s9 = 0`; zero constants propagate).
  * `z1FreeB g`: after zero propagation, column `13` is not read (`colsOf`); `zpM` / `z1FreeM` the
    same for `MixedExpr` (base leaves only: `Lift` / `Scale`).
  * **`base_z1_receipt`**: exactly ONE base template gate fails `z1FreeB` (`decide +kernel`), and it
    is the booleanity gate `z1·(z1 − 1)` (**`z1_bool_flagged`**, the positive control: the instrument
    fires on a gate that reads `z1` unguarded).  **`k_z1_receipt`**: every `𝕂` template gate passes.
  * **`baseGatesF_z1_irrel`**: every deployed base gate other than the booleanity gate takes the
    same value at two environments that differ only in column `13` (current and next row), off
    OP0 / OP5 / OP9.  **`kGatesF_z1_irrel`**: the same for the `𝕂` gates at a FIXED `𝕂` environment
    (the gathered `𝕂` roles are separate columns; that they exclude `13` is not re-checked here).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChipH

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.Z1VS

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH

/-! ## 1. Zero propagation of the selectors `{0, 5, 9}` -/

section Zp

def isSel (i : ℕ) : Bool := i = 0 || i = 5 || i = 9

/-- **Zero propagation**: `none` means identically `0` once `s0 = s5 = s9 = 0`. -/
def zp : CoeffExpr ℚ → Option (CoeffExpr ℚ)
  | .const c => if c = 0 then none else some (.const c)
  | .var k i =>
    match k with
    | .traceCur => if isSel i then none else some (.var .traceCur i)
    | k => some (.var k i)
  | .add a b =>
    match zp a, zp b with
    | none, none => none
    | none, some y => some y
    | some x, none => some x
    | some x, some y => some (.add x y)
  | .sub a b =>
    match zp a, zp b with
    | none, none => none
    | none, some y => some (.neg y)
    | some x, none => some x
    | some x, some y => some (.sub x y)
  | .mul a b =>
    match zp a, zp b with
    | some x, some y => some (.mul x y)
    | _, _ => none
  | .neg a => (zp a).map .neg
  | .pow a n =>
    match zp a with
    | some x => some (.pow x n)
    | none => if n = 0 then some (.pow a 0) else none

/-- `z1` is not read after zero propagation. -/
def z1FreeB (g : CoeffExpr ℚ) : Bool :=
  match zp g with
  | none => true
  | some g' => !((colsOf g').contains z1C)

/-- Zero propagation for `MixedExpr` (base leaves only; `𝕂` columns are kept). -/
def zpM : MixedExpr ℚ → Option (MixedExpr ℚ)
  | .Var k i => some (.Var k i)
  | .Lift g => (zp g).map .Lift
  | .Scale g u =>
    match zp g, zpM u with
    | some x, some y => some (.Scale x y)
    | _, _ => none
  | .Const c => if c = 0 then none else some (.Const c)
  | .Add x y =>
    match zpM x, zpM y with
    | none, none => none
    | none, some b => some b
    | some a, none => some a
    | some a, some b => some (.Add a b)
  | .Sub x y =>
    match zpM x, zpM y with
    | none, none => none
    | none, some b => some (.Neg b)
    | some a, none => some a
    | some a, some b => some (.Sub a b)
  | .Neg x => (zpM x).map .Neg
  | .Mul x y =>
    match zpM x, zpM y with
    | some a, some b => some (.Mul a b)
    | _, _ => none
  | .Pow x n =>
    match zpM x with
    | some a => some (.Pow a n)
    | none => if n = 0 then some (.Pow x 0) else none

/-- Base columns read by a mixed expression (through `Lift` / `Scale` only). -/
def colsOfM {G : Type} : MixedExpr G → List ℕ
  | .Var _ _ => []
  | .Lift g => colsOf g
  | .Scale g u => colsOf g ++ colsOfM u
  | .Const _ => []
  | .Add x y => colsOfM x ++ colsOfM y
  | .Sub x y => colsOfM x ++ colsOfM y
  | .Neg x => colsOfM x
  | .Mul x y => colsOfM x ++ colsOfM y
  | .Pow x _ => colsOfM x

def z1FreeM (g : MixedExpr ℚ) : Bool :=
  match zpM g with
  | none => true
  | some g' => !((colsOfM g').contains z1C)

end Zp

/-! ## 2. The receipts (kernel `decide` on the `ℚ` templates) -/

/-- The booleanity gate of `z1`. -/
def z1Bool : CoeffExpr ℚ := .mul (cc z1C) (.sub (cc z1C) (.const 1))

/-- **Positive control**: the instrument flags the gate that reads `z1` unguarded. -/
theorem z1_bool_flagged : z1FreeB z1Bool = false := by decide

theorem z1Bool_mem : z1Bool ∈ (baseGatesH (F := ℚ)) := by
  simp [z1Bool, baseGatesH, arithGates]

/-- **The base receipt**: exactly one base template gate reads `z1` off OP0 / OP5 / OP9 (its booleanity). -/
theorem base_z1_receipt : ((baseGatesH (F := ℚ)).filter fun g => !z1FreeB g).length = 1 := by
  decide +kernel

/-- **The `𝕂` receipt**: no `𝕂` template gate reads `z1` off OP0 / OP5 / OP9. -/
theorem k_z1_receipt : (kGatesH (F := ℚ)).all z1FreeM = true := by
  decide +kernel

theorem base_z1_free_or_bool : ∀ g ∈ (baseGatesH (F := ℚ)), z1FreeB g = true ∨ g = z1Bool := by
  intro g hg
  by_contra hne
  push Not at hne
  have hgf : g ∈ (baseGatesH (F := ℚ)).filter fun g => !z1FreeB g := by
    simp only [List.mem_filter, hg, true_and]
    simp [hne.1]
  have hbf : z1Bool ∈ (baseGatesH (F := ℚ)).filter fun g => !z1FreeB g := by
    simp only [List.mem_filter, z1Bool_mem, true_and]
    rw [z1_bool_flagged]; rfl
  have hl := base_z1_receipt
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hl
  rw [ha, List.mem_singleton] at hgf hbf
  exact hne.2 (hgf.trans hbf.symm)

/-! ## 3. Semantics -/

section Sem
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Value of a zero-propagated expression (`none ↦ 0`). -/
def zv (o : Option (CoeffExpr F)) (e : Env F) : F :=
  match o with
  | none => 0
  | some g => g.eval e

def zvM (o : Option (MixedExpr F)) (eK : Env K) (eF : Env F) : K :=
  match o with
  | none => 0
  | some g => g.eval eK eF

theorem isSel_zero (e : Env F) (h0 : e.trace 0 = 0) (h5 : e.trace 5 = 0) (h9 : e.trace 9 = 0)
    (i : ℕ) (hi : isSel i = true) : e.trace i = 0 := by
  simp only [isSel, Bool.or_eq_true, decide_eq_true_eq] at hi
  rcases hi with (rfl | rfl) | rfl <;> assumption

local notation "cQ" => (fun q : ℚ => (q : F))

theorem zp_eval (e : Env F) (h0 : e.trace 0 = 0) (h5 : e.trace 5 = 0) (h9 : e.trace 9 = 0) :
    ∀ g : CoeffExpr ℚ, zv ((zp g).map (mapC cQ)) e = (mapC cQ g).eval e
  | .const c => by
    simp only [zp]
    split_ifs with hc
    · subst hc; simp [zv, mapC, CoeffExpr.eval]
    · rfl
  | .var k i => by
    cases k with
    | traceCur =>
      simp only [zp]
      split_ifs with hs
      · simp only [Option.map, zv, mapC, CoeffExpr.eval]; exact (isSel_zero e h0 h5 h9 i hs).symm
      · rfl
    | traceNext => rfl
    | challenge => rfl
    | publicVal => rfl
  | .add a b => by
    have ha := zp_eval e h0 h5 h9 a
    have hb := zp_eval e h0 h5 h9 b
    cases hza : zp a <;> cases hzb : zp b <;>
      simp only [zp, hza, hzb, Option.map, zv, mapC, CoeffExpr.eval] at ha hb ⊢ <;>
      linear_combination ha + hb
  | .sub a b => by
    have ha := zp_eval e h0 h5 h9 a
    have hb := zp_eval e h0 h5 h9 b
    cases hza : zp a <;> cases hzb : zp b <;>
      simp only [zp, hza, hzb, Option.map, zv, mapC, CoeffExpr.eval] at ha hb ⊢ <;>
      linear_combination ha - hb
  | .mul a b => by
    have ha := zp_eval e h0 h5 h9 a
    have hb := zp_eval e h0 h5 h9 b
    cases hza : zp a <;> cases hzb : zp b <;>
      simp only [zp, hza, hzb, Option.map, zv, mapC, CoeffExpr.eval] at ha hb ⊢
    · rw [← ha]; ring
    · rw [← ha]; ring
    · rw [← hb]; ring
    · rw [ha, hb]
  | .neg a => by
    have ha := zp_eval e h0 h5 h9 a
    cases hza : zp a <;> simp only [zp, hza, Option.map, zv, mapC, CoeffExpr.eval] at ha ⊢ <;>
      linear_combination (-1 : F) * ha
  | .pow a n => by
    have ha := zp_eval e h0 h5 h9 a
    cases hza : zp a with
    | some x =>
      simp only [zp, hza, Option.map, zv, mapC, CoeffExpr.eval] at ha ⊢; rw [ha]
    | none =>
      simp only [zp, hza, Option.map, zv] at ha ⊢
      split_ifs with hn
      · subst hn; rfl
      · simp only [Option.map, zv, mapC, CoeffExpr.eval]; rw [← ha, zero_pow hn]

theorem zpM_eval (eK : Env K) (eF : Env F) (h0 : eF.trace 0 = 0) (h5 : eF.trace 5 = 0)
    (h9 : eF.trace 9 = 0) : ∀ g : MixedExpr ℚ, zvM ((zpM g).map (mapM cQ)) eK eF = (mapM cQ g).eval eK eF
  | .Var k i => rfl
  | .Lift g => by
    have hg := zp_eval eF h0 h5 h9 g
    cases hz : zp g <;> simp only [zpM, hz, Option.map, zvM, zv, mapM, MixedExpr.eval] at hg ⊢
    · rw [← hg, map_zero]
    · rw [hg]
  | .Scale g u => by
    have hg := zp_eval eF h0 h5 h9 g
    have hu := zpM_eval eK eF h0 h5 h9 u
    cases hz : zp g <;> cases hzu : zpM u <;>
      simp only [zpM, hz, hzu, Option.map, zvM, zv, mapM, MixedExpr.eval] at hg hu ⊢
    · rw [← hg, map_zero, zero_mul]
    · rw [← hg, map_zero, zero_mul]
    · rw [← hu, mul_zero]
    · rw [hg, hu]
  | .Const c => by
    simp only [zpM]
    split_ifs with hc
    · subst hc; simp [zvM, mapM, MixedExpr.eval]
    · rfl
  | .Add x y => by
    have hx := zpM_eval eK eF h0 h5 h9 x
    have hy := zpM_eval eK eF h0 h5 h9 y
    cases hzx : zpM x <;> cases hzy : zpM y <;>
      simp only [zpM, hzx, hzy, Option.map, zvM, mapM, MixedExpr.eval] at hx hy ⊢ <;>
      linear_combination hx + hy
  | .Sub x y => by
    have hx := zpM_eval eK eF h0 h5 h9 x
    have hy := zpM_eval eK eF h0 h5 h9 y
    cases hzx : zpM x <;> cases hzy : zpM y <;>
      simp only [zpM, hzx, hzy, Option.map, zvM, mapM, MixedExpr.eval] at hx hy ⊢ <;>
      linear_combination hx - hy
  | .Neg x => by
    have hx := zpM_eval eK eF h0 h5 h9 x
    cases hzx : zpM x <;> simp only [zpM, hzx, Option.map, zvM, mapM, MixedExpr.eval] at hx ⊢ <;>
      linear_combination (-1 : K) * hx
  | .Mul x y => by
    have hx := zpM_eval eK eF h0 h5 h9 x
    have hy := zpM_eval eK eF h0 h5 h9 y
    cases hzx : zpM x <;> cases hzy : zpM y <;>
      simp only [zpM, hzx, hzy, Option.map, zvM, mapM, MixedExpr.eval] at hx hy ⊢
    · rw [← hx]; ring
    · rw [← hx]; ring
    · rw [← hy]; ring
    · rw [hx, hy]
  | .Pow x n => by
    have hx := zpM_eval eK eF h0 h5 h9 x
    cases hzx : zpM x with
    | some a =>
      simp only [zpM, hzx, Option.map, zvM, mapM, MixedExpr.eval] at hx ⊢; rw [hx]
    | none =>
      simp only [zpM, hzx, Option.map, zvM] at hx ⊢
      split_ifs with hn
      · subst hn; rfl
      · simp only [Option.map, zvM, mapM, MixedExpr.eval]; rw [← hx, zero_pow hn]

theorem colsOf_mapC (φ : ℚ → F) : ∀ g : CoeffExpr ℚ, colsOf (mapC φ g) = colsOf g
  | .const c => rfl
  | .var k i => by cases k <;> rfl
  | .add a b => by simp only [mapC, colsOf, colsOf_mapC φ a, colsOf_mapC φ b]
  | .sub a b => by simp only [mapC, colsOf, colsOf_mapC φ a, colsOf_mapC φ b]
  | .mul a b => by simp only [mapC, colsOf, colsOf_mapC φ a, colsOf_mapC φ b]
  | .neg a => by simp only [mapC, colsOf, colsOf_mapC φ a]
  | .pow a n => by simp only [mapC, colsOf, colsOf_mapC φ a]

theorem colsOfM_mapM (φ : ℚ → F) : ∀ g : MixedExpr ℚ, colsOfM (mapM φ g) = colsOfM g
  | .Var k i => rfl
  | .Lift g => by simp only [mapM, colsOfM, colsOf_mapC φ g]
  | .Scale g u => by simp only [mapM, colsOfM, colsOf_mapC φ g, colsOfM_mapM φ u]
  | .Const c => rfl
  | .Add x y => by simp only [mapM, colsOfM, colsOfM_mapM φ x, colsOfM_mapM φ y]
  | .Sub x y => by simp only [mapM, colsOfM, colsOfM_mapM φ x, colsOfM_mapM φ y]
  | .Neg x => by simp only [mapM, colsOfM, colsOfM_mapM φ x]
  | .Mul x y => by simp only [mapM, colsOfM, colsOfM_mapM φ x, colsOfM_mapM φ y]
  | .Pow x n => by simp only [mapM, colsOfM, colsOfM_mapM φ x]

/-- Two environments that agree off column `13` (current and next row) and on coins and publics. -/
def AgreeOff13 (e e' : Env F) : Prop :=
  (∀ i, i ≠ z1C → e.trace i = e'.trace i) ∧ (∀ i, i ≠ z1C → e.traceNext i = e'.traceNext i) ∧
    e.chal = e'.chal ∧ e.pub = e'.pub

theorem eval_congr13 {e e' : Env F} (h : AgreeOff13 e e') :
    ∀ g : CoeffExpr F, (colsOf g).contains z1C = false → g.eval e = g.eval e'
  | .const c, _ => rfl
  | .var k i, hc => by
    cases k with
    | traceCur =>
      have hi : i ≠ z1C := by intro hi; subst hi; simp [colsOf] at hc
      exact h.1 i hi
    | traceNext =>
      have hi : i ≠ z1C := by intro hi; subst hi; simp [colsOf] at hc
      exact h.2.1 i hi
    | challenge => show e.chal i = e'.chal i; rw [h.2.2.1]
    | publicVal => show e.pub i = e'.pub i; rw [h.2.2.2]
  | .add a b, hc => by
    simp only [colsOf, List.contains_append, Bool.or_eq_false_iff] at hc
    simp only [CoeffExpr.eval, eval_congr13 h a hc.1, eval_congr13 h b hc.2]
  | .sub a b, hc => by
    simp only [colsOf, List.contains_append, Bool.or_eq_false_iff] at hc
    simp only [CoeffExpr.eval, eval_congr13 h a hc.1, eval_congr13 h b hc.2]
  | .mul a b, hc => by
    simp only [colsOf, List.contains_append, Bool.or_eq_false_iff] at hc
    simp only [CoeffExpr.eval, eval_congr13 h a hc.1, eval_congr13 h b hc.2]
  | .neg a, hc => by simp only [CoeffExpr.eval, eval_congr13 h a hc]
  | .pow a n, hc => by simp only [CoeffExpr.eval, eval_congr13 h a hc]

theorem evalM_congr13 (eK : Env K) {e e' : Env F} (h : AgreeOff13 e e') :
    ∀ g : MixedExpr F, (colsOfM g).contains z1C = false → g.eval eK e = g.eval eK e'
  | .Var k i, _ => by cases k <;> rfl
  | .Lift g, hc => by simp only [MixedExpr.eval, eval_congr13 h g hc]
  | .Scale g u, hc => by
    simp only [colsOfM, List.contains_append, Bool.or_eq_false_iff] at hc
    simp only [MixedExpr.eval, eval_congr13 h g hc.1, evalM_congr13 eK h u hc.2]
  | .Const c, _ => rfl
  | .Add x y, hc => by
    simp only [colsOfM, List.contains_append, Bool.or_eq_false_iff] at hc
    simp only [MixedExpr.eval, evalM_congr13 eK h x hc.1, evalM_congr13 eK h y hc.2]
  | .Sub x y, hc => by
    simp only [colsOfM, List.contains_append, Bool.or_eq_false_iff] at hc
    simp only [MixedExpr.eval, evalM_congr13 eK h x hc.1, evalM_congr13 eK h y hc.2]
  | .Neg x, hc => by simp only [MixedExpr.eval, evalM_congr13 eK h x hc]
  | .Mul x y, hc => by
    simp only [colsOfM, List.contains_append, Bool.or_eq_false_iff] at hc
    simp only [MixedExpr.eval, evalM_congr13 eK h x hc.1, evalM_congr13 eK h y hc.2]
  | .Pow x n, hc => by simp only [MixedExpr.eval, evalM_congr13 eK h x hc]

theorem sel_zero' {e e' : Env F} (h : AgreeOff13 e e') (h0 : e.trace 0 = 0) (h5 : e.trace 5 = 0)
    (h9 : e.trace 9 = 0) : e'.trace 0 = 0 ∧ e'.trace 5 = 0 ∧ e'.trace 9 = 0 :=
  ⟨(h.1 0 (by decide)).symm.trans h0, (h.1 5 (by decide)).symm.trans h5,
    (h.1 9 (by decide)).symm.trans h9⟩

/-- **The z1 read-set receipt, base gates**: off OP0 / OP5 / OP9, every deployed base gate except the
booleanity of `z1` takes the same value whatever `z1` (current or next row) is. -/
theorem baseGatesF_z1_irrel (t : CoeffExpr ℚ) (ht : t ∈ (baseGatesH (F := ℚ))) (hb : t ≠ z1Bool)
    {e e' : Env F} (h : AgreeOff13 e e') (h0 : e.trace 0 = 0) (h5 : e.trace 5 = 0) (h9 : e.trace 9 = 0) :
    (mapC (fun q : ℚ => (q : F)) t).eval e = (mapC (fun q : ℚ => (q : F)) t).eval e' := by
  have hfree : z1FreeB t = true := (base_z1_free_or_bool t ht).resolve_right hb
  obtain ⟨h0', h5', h9'⟩ := sel_zero' h h0 h5 h9
  rw [← zp_eval e h0 h5 h9, ← zp_eval e' h0' h5' h9']
  unfold z1FreeB at hfree
  cases hz : zp t with
  | none => rfl
  | some g =>
    rw [hz] at hfree
    simp only [Option.map, zv]
    refine eval_congr13 h _ ?_
    rw [colsOf_mapC]
    simpa using hfree

/-- **The z1 read-set receipt, `𝕂` gates** (at a fixed `𝕂` environment). -/
theorem kGatesF_z1_irrel (t : MixedExpr ℚ) (ht : t ∈ (kGatesH (F := ℚ))) (eK : Env K)
    {e e' : Env F} (h : AgreeOff13 e e') (h0 : e.trace 0 = 0) (h5 : e.trace 5 = 0) (h9 : e.trace 9 = 0) :
    (mapM (fun q : ℚ => (q : F)) t).eval eK e = (mapM (fun q : ℚ => (q : F)) t).eval eK e' := by
  have hfree : z1FreeM t = true := List.all_eq_true.mp k_z1_receipt t ht
  obtain ⟨h0', h5', h9'⟩ := sel_zero' h h0 h5 h9
  rw [← zpM_eval eK e h0 h5 h9, ← zpM_eval eK e' h0' h5' h9']
  unfold z1FreeM at hfree
  cases hz : zpM t with
  | none => rfl
  | some g =>
    rw [hz] at hfree
    simp only [Option.map, zvM]
    refine evalM_congr13 eK h _ ?_
    rw [colsOfM_mapM]
    simpa using hfree

end Sem

end Nock.NockVMROM.Thm54.VclL.Handle.Z1VS
