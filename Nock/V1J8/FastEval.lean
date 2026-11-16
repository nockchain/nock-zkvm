/-
  Nock/V1J8/FastEval.lean

  Every function is proved equal to its spec evaluator over the `Gold` image of the row environment
  (`gEnvOf`): `CE.eval_comp`, `ME.eval_comp`, `EE.eval_comp`, `srcOKX_eq`, `srcOKM_eq`. No proved definition changes. -/
import Nock.V1J8.FastLag
import Nock.TraceGenExe.GoldFast

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.V1J8.FastEval

open Nock Nock.Reified Nock.Framework Nock.TraceGenExe Nock.Field Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.V1Check Nock.V1J8.Exe Nock.V1J8.CompX Nock.V1J8.MemX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (baseGatesFX slotPairsX walkGatesFX)

/-! ## 1. `Gold` / `K3` arithmetic on registers -/

theorem ofZ_add (x y : ZMod p) : Gold.ofZ (x + y) = Gold.ofZ x + Gold.ofZ y :=
  Gold.toZ_injective (by rw [Gold.toZ_add, Gold.toZ_ofZ, Gold.toZ_ofZ, Gold.toZ_ofZ])
theorem ofZ_sub (x y : ZMod p) : Gold.ofZ (x - y) = Gold.ofZ x - Gold.ofZ y :=
  Gold.toZ_injective (by rw [Gold.toZ_sub, Gold.toZ_ofZ, Gold.toZ_ofZ, Gold.toZ_ofZ])
theorem ofZ_mul (x y : ZMod p) : Gold.ofZ (x * y) = Gold.mulF (Gold.ofZ x) (Gold.ofZ y) :=
  Gold.toZ_injective (by rw [Gold.mulF_eq, Gold.toZ_mul, Gold.toZ_ofZ, Gold.toZ_ofZ, Gold.toZ_ofZ])
theorem ofZ_neg (x : ZMod p) : Gold.ofZ (-x) = -Gold.ofZ x :=
  Gold.toZ_injective (by rw [Gold.toZ_neg, Gold.toZ_ofZ, Gold.toZ_ofZ])
theorem ofZ_pow (x : ZMod p) (n : ℕ) : Gold.ofZ (x ^ n) = Gold.powF' (Gold.ofZ x) n :=
  Gold.toZ_injective (by rw [Gold.powF'_eq, Gold.toZ_pow, Gold.toZ_ofZ, Gold.toZ_ofZ])
theorem ofZ_zero : Gold.ofZ (0 : ZMod p) = 0 :=
  Gold.toZ_injective (by rw [Gold.toZ_ofZ, Gold.toZ_zero])

def mulK (a b : K3) : K3 :=
  ⟨Gold.mulF a.c0 b.c0 + Gold.mulF Gold.seven (Gold.mulF a.c1 b.c2 + Gold.mulF a.c2 b.c1),
   Gold.mulF a.c0 b.c1 + Gold.mulF a.c1 b.c0 + Gold.mulF Gold.seven (Gold.mulF a.c2 b.c2),
   Gold.mulF a.c0 b.c2 + Gold.mulF a.c1 b.c1 + Gold.mulF a.c2 b.c0⟩

theorem mulK_eq (a b : K3) : mulK a b = a * b := by
  show mulK a b = K3.mul a b
  simp only [mulK, K3.mul, Gold.mulF_eq]

def smulK (s : Gold) (a : K3) : K3 := ⟨Gold.mulF s a.c0, Gold.mulF s a.c1, Gold.mulF s a.c2⟩

theorem smulK_eq (s : Gold) (a : K3) : smulK s a = K3.smul s a := by
  simp only [smulK, K3.smul, Gold.mulF_eq]

def powKF (a : K3) : ℕ → K3
  | 0 => 1
  | n + 1 => mulK (powKF a n) a

theorem powKF_eq (a : K3) : ∀ n, powKF a n = powK a n
  | 0 => rfl
  | n + 1 => by rw [powKF, powK, powKF_eq a n, mulK_eq]

/-! ## 2. Compiled gate trees (constants already `Gold`) -/

/-- Base-field gate, constants as `Gold`. -/
inductive CE where
  | const : Gold → CE
  | var : VarKind → ℕ → CE
  | add : CE → CE → CE
  | sub : CE → CE → CE
  | mul : CE → CE → CE
  | neg : CE → CE
  | pow : CE → ℕ → CE

def CE.comp : CoeffExpr (ZMod p) → CE
  | .const c => .const (Gold.ofZ c)
  | .var k i => .var k i
  | .add a b => .add (comp a) (comp b)
  | .sub a b => .sub (comp a) (comp b)
  | .mul a b => .mul (comp a) (comp b)
  | .neg a => .neg (comp a)
  | .pow a n => .pow (comp a) n

def CE.eval (e : Env Gold) : CE → Gold
  | .const c => c
  | .var .traceCur i => e.trace i
  | .var .traceNext i => e.traceNext i
  | .var .challenge i => e.chal i
  | .var .publicVal i => e.pub i
  | .add a b => a.eval e + b.eval e
  | .sub a b => a.eval e - b.eval e
  | .mul a b => Gold.mulF (a.eval e) (b.eval e)
  | .neg a => - a.eval e
  | .pow a n => Gold.powF' (a.eval e) n

/-- The `Gold` image of a `ZMod p` environment. -/
def gEnvOf (e : Env (ZMod p)) : Env Gold :=
  ⟨fun j => Gold.ofZ (e.trace j), fun j => Gold.ofZ (e.traceNext j), fun j => Gold.ofZ (e.chal j),
    fun j => Gold.ofZ (e.pub j)⟩

theorem CE.eval_comp (e : Env (ZMod p)) (g : CoeffExpr (ZMod p)) :
    (CE.comp g).eval (gEnvOf e) = Gold.ofZ (g.eval e) := by
  induction g with
  | const c => rfl
  | var k i => cases k <;> rfl
  | add a b ha hb => simp only [CE.comp, CE.eval, CoeffExpr.eval, ha, hb, ofZ_add]
  | sub a b ha hb => simp only [CE.comp, CE.eval, CoeffExpr.eval, ha, hb, ofZ_sub]
  | mul a b ha hb => simp only [CE.comp, CE.eval, CoeffExpr.eval, ha, hb, ofZ_mul]
  | neg a ha => simp only [CE.comp, CE.eval, CoeffExpr.eval, ha, ofZ_neg]
  | pow a n ha => simp only [CE.comp, CE.eval, CoeffExpr.eval, ha, ofZ_pow]

/-- Mixed (`𝕂`-valued) gate, constants as `K3`. -/
inductive ME where
  | var : VarKind → ℕ → ME
  | lift : CE → ME
  | scale : CE → ME → ME
  | const : K3 → ME
  | add : ME → ME → ME
  | sub : ME → ME → ME
  | neg : ME → ME
  | mul : ME → ME → ME
  | pow : ME → ℕ → ME

def ME.comp : MixedExpr (ZMod p) → ME
  | .Var k i => .var k i
  | .Lift g => .lift (CE.comp g)
  | .Scale g u => .scale (CE.comp g) (comp u)
  | .Const c => .const (g3 (Gold.ofZ (c : ZMod p)))
  | .Add x y => .add (comp x) (comp y)
  | .Sub x y => .sub (comp x) (comp y)
  | .Neg x => .neg (comp x)
  | .Mul x y => .mul (comp x) (comp y)
  | .Pow x n => .pow (comp x) n

def ME.eval (eK : Env K3) (eG : Env Gold) : ME → K3
  | .var .traceCur i => eK.trace i
  | .var .traceNext i => eK.traceNext i
  | .var .challenge i => eK.chal i
  | .var .publicVal i => eK.pub i
  | .lift g => g3 (g.eval eG)
  | .scale g u => smulK (g.eval eG) (u.eval eK eG)
  | .const c => c
  | .add x y => x.eval eK eG + y.eval eK eG
  | .sub x y => x.eval eK eG - y.eval eK eG
  | .neg x => - x.eval eK eG
  | .mul x y => mulK (x.eval eK eG) (y.eval eK eG)
  | .pow x n => powKF (x.eval eK eG) n

theorem ME.eval_comp (eK : Env K3) (e : Env (ZMod p)) (m : MixedExpr (ZMod p)) :
    (ME.comp m).eval eK (gEnvOf e) = evalMZ eK e m := by
  induction m with
  | Var k i => cases k <;> rfl
  | Lift g => simp only [ME.comp, ME.eval, evalMZ, CE.eval_comp]
  | Scale g u ih => simp only [ME.comp, ME.eval, evalMZ, CE.eval_comp, ih, smulK_eq]
  | Const c => rfl
  | Add x y ihx ihy => simp only [ME.comp, ME.eval, evalMZ, ihx, ihy]
  | Sub x y ihx ihy => simp only [ME.comp, ME.eval, evalMZ, ihx, ihy]
  | Neg x ihx => simp only [ME.comp, ME.eval, evalMZ, ihx]
  | Mul x y ihx ihy => simp only [ME.comp, ME.eval, evalMZ, ihx, ihy, mulK_eq]
  | Pow x n ihx => simp only [ME.comp, ME.eval, evalMZ, ihx, powKF_eq]

/-- `𝕂`-valued `Expr` gate, constants as `K3`. -/
inductive EE where
  | var : VarKind → ℕ → EE
  | const : K3 → EE
  | add : EE → EE → EE
  | sub : EE → EE → EE
  | mul : EE → EE → EE
  | neg : EE → EE
  | pow : EE → ℕ → EE

def EE.comp : Expr → EE
  | .Var k i => .var k i
  | .Const c => .const (g3 (Gold.ofZ (c : ZMod p)))
  | .Add x y => .add (comp x) (comp y)
  | .Sub x y => .sub (comp x) (comp y)
  | .Mul x y => .mul (comp x) (comp y)
  | .Neg x => .neg (comp x)
  | .Pow x n => .pow (comp x) n

def EE.eval (eK : Env K3) : EE → K3
  | .var .traceCur i => eK.trace i
  | .var .traceNext i => eK.traceNext i
  | .var .challenge i => eK.chal i
  | .var .publicVal i => eK.pub i
  | .const c => c
  | .add x y => x.eval eK + y.eval eK
  | .sub x y => x.eval eK - y.eval eK
  | .neg x => - x.eval eK
  | .mul x y => mulK (x.eval eK) (y.eval eK)
  | .pow x n => powKF (x.eval eK) n

theorem EE.eval_comp (eK : Env K3) (g : Expr) : (EE.comp g).eval eK = evalEZ eK g := by
  induction g with
  | Var k i => cases k <;> rfl
  | Const c => rfl
  | Add x y ihx ihy => simp only [EE.comp, EE.eval, evalEZ, ihx, ihy]
  | Sub x y ihx ihy => simp only [EE.comp, EE.eval, evalEZ, ihx, ihy]
  | Mul x y ihx ihy => simp only [EE.comp, EE.eval, evalEZ, ihx, ihy, mulK_eq]
  | Neg x ihx => simp only [EE.comp, EE.eval, evalEZ, ihx]
  | Pow x n ihx => simp only [EE.comp, EE.eval, evalEZ, ihx, powKF_eq]

/-! ### Bounds on the coin / public indices a gate reads (performance only: the cache falls back outside) -/

def CE.mx : CE → ℕ
  | .const _ => 0
  | .var .challenge i => i + 1
  | .var .publicVal i => i + 1
  | .var _ _ => 0
  | .add a b => max a.mx b.mx
  | .sub a b => max a.mx b.mx
  | .mul a b => max a.mx b.mx
  | .neg a => a.mx
  | .pow a _ => a.mx

def ME.mx : ME → ℕ
  | .var .challenge i => i + 1
  | .var .publicVal i => i + 1
  | .var _ _ => 0
  | .lift g => g.mx
  | .scale g u => max g.mx u.mx
  | .const _ => 0
  | .add a b => max a.mx b.mx
  | .sub a b => max a.mx b.mx
  | .neg a => a.mx
  | .mul a b => max a.mx b.mx
  | .pow a _ => a.mx

def EE.mx : EE → ℕ
  | .var .challenge i => i + 1
  | .var .publicVal i => i + 1
  | .var _ _ => 0
  | .const _ => 0
  | .add a b => max a.mx b.mx
  | .sub a b => max a.mx b.mx
  | .neg a => a.mx
  | .mul a b => max a.mx b.mx
  | .pow a _ => a.mx

/-! ## 3. Source gates, fast -/

theorem decide_eqG (x : ZMod p) : decide (x = 0) = eqG (Gold.ofZ x) 0 := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, eqG_iff]
  constructor
  · intro h; subst h; exact ofZ_zero
  · intro h
    have := congrArg Gold.toZ h
    rwa [Gold.toZ_ofZ, Gold.toZ_zero] at this

/-- The `K3` environment of a `Gold` environment (`readK`, base `B`, stride `s`). -/
def rk (f : ℕ → Gold) (c : ℕ) : K3 := ⟨f c, f (c + 1), f (c + 2)⟩

def kenvG (B s : ℕ) (g : Env Gold) : Env K3 :=
  ⟨fun i => rk g.trace (B + s * i), fun i => rk g.traceNext (B + s * i), fun i => rk g.chal (B + s * i),
    fun i => rk g.pub (B + s * i)⟩

theorem kenv_eq (e : Env (ZMod p)) : kenv e = kenvG 0 1 (gEnvOf e) := by
  simp only [kenv, kenvG, readK, rk, gEnvOf, zero_add, one_mul]

theorem kenvB_eq (B : ℕ) (e : Env (ZMod p)) : kenvB B e = kenvG B 3 (gEnvOf e) := by
  simp only [kenvB, kenvG, readK, rk, gEnvOf]

/-- Compiled source gate of the compute chip. -/
inductive SGX where
  | base : CE → SGX
  | mix : ME → SGX

def SGX.comp : CompX.SG → SGX
  | .base g => .base (CE.comp g)
  | .mix m => .mix (ME.comp m)

def SGX.mx : SGX → ℕ
  | .base c => c.mx
  | .mix m => m.mx

def srcOKX (g : Env Gold) : SGX → Bool
  | .base c => eqG (c.eval g) 0
  | .mix m => zero3 (m.eval (kenvG 0 1 g) g)

theorem srcOKX_eq (e : Env (ZMod p)) (s : CompX.SG) : srcOKX (gEnvOf e) (SGX.comp s) = CompX.srcOK e s := by
  cases s with
  | base g => simp only [SGX.comp, srcOKX, CompX.srcOK, CE.eval_comp, decide_eqG]
  | mix m => simp only [SGX.comp, srcOKX, CompX.srcOK, ME.eval_comp, kenv_eq]

/-- Compiled source gate of a memory-side chip. -/
inductive SGF where
  | base : CE → SGF
  | ext : EE → SGF
  | mix : ME → SGF

def SGF.comp : SGM → SGF
  | .base g => .base (CE.comp g)
  | .ext g => .ext (EE.comp g)
  | .mix m => .mix (ME.comp m)

def SGF.mx : SGF → ℕ
  | .base c => c.mx
  | .ext c => c.mx
  | .mix m => m.mx

def srcOKM (B : ℕ) (g : Env Gold) : SGF → Bool
  | .base c => eqG (c.eval g) 0
  | .ext c => zero3 (c.eval (kenvG B 3 g))
  | .mix m => zero3 (m.eval (kenvG B 3 g) g)

theorem srcOKM_eq (B : ℕ) (e : Env (ZMod p)) (s : SGM) :
    srcOKM B (gEnvOf e) (SGF.comp s) = MemX.srcOK B e s := by
  cases s with
  | base g => simp only [SGF.comp, srcOKM, MemX.srcOK, CE.eval_comp, decide_eqG]
  | ext g => simp only [SGF.comp, srcOKM, MemX.srcOK, EE.eval_comp, kenvB_eq]
  | mix m => simp only [SGF.comp, srcOKM, MemX.srcOK, ME.eval_comp, kenvB_eq]

/-! ## 4. Tables: `Gold` columns converted once, the cached last-row extrapolation -/

/-- `f` on `0..m-1` as `Gold`, converted once (outside the range: converted on demand).  A structure, so that the
compiler cannot eta-expand the array construction into the lookup (which would rebuild it at every call). -/
structure GC where
  arr : Array Gold
  f : ℕ → ZMod p

def GC.mk' (f : ℕ → ZMod p) (m : ℕ) : GC := ⟨Array.ofFn (n := m) fun j => Gold.ofZ (f j), f⟩

def GC.get (c : GC) (j : ℕ) : Gold := if h : j < c.arr.size then c.arr[j] else Gold.ofZ (c.f j)

theorem GC.get_mk' (f : ℕ → ZMod p) (m : ℕ) (j : ℕ) : (GC.mk' f m).get j = Gold.ofZ (f j) := by
  simp only [GC.mk', GC.get]
  by_cases h : j < m
  · simp [Array.getElem_ofFn, h]
  · simp [h]

/-- Column-major `Gold` copy of the first `w` columns. -/
def goldCols {n : ℕ} (cols : ℕ → Fin n → ZMod p) (w : ℕ) : Array (Array Gold) :=
  Array.ofFn (n := w) fun j => Array.ofFn (n := n) fun i => Gold.ofZ (cols j i)

def colG (A : Array (Array Gold)) (j i : ℕ) : Gold :=
  if h : j < A.size then (if h2 : i < (A[j]'h).size then (A[j]'h)[i]'h2 else 0) else 0

theorem colG_goldCols {n : ℕ} (cols : ℕ → Fin n → ZMod p) (w j : ℕ) (hj : j < w) (i : Fin n) :
    colG (goldCols cols w) j i = Gold.ofZ (cols j i) := by
  simp [colG, goldCols, hj, Array.getElem_ofFn]

theorem getD_map_ofZ (a : Array (ZMod p)) (j : ℕ) : (a.map Gold.ofZ).getD j 0 = Gold.ofZ (a.getD j 0) := by
  by_cases h : j < a.size
  · simp [Array.getD, h]
  · simp [Array.getD, h, ofZ_zero]

/-- The row environment of a compute table over `Gold`. -/
def rowEnvX {n : ℕ} (A : Array (Array Gold)) (nxG : Array Gold) (cG pG : GC) (i : Fin n) : Env Gold where
  trace := fun j => if j < 123 then colG A j i else 0
  traceNext := fun j => if j < 123 then
      (if (i : ℕ) + 1 < n then colG A j (i + 1) else nxG.getD j 0) else 0
  chal := fun j => cG.get j
  pub := fun j => pG.get j

theorem rowEnvX_eq {n : ℕ} (T : TabX n) (m : ℕ) (i : Fin n) :
    rowEnvX (goldCols T.cols 123) ((FastLag.nextArr T.nodes T.ω T.cols 123).map Gold.ofZ) (GC.mk' T.chal m)
      (GC.mk' T.pub m) i = gEnvOf (T.env i) := by
  simp only [rowEnvX, gEnvOf, TabX.env, Env.mk.injEq, GC.get_mk', and_true, true_and]
  constructor
  · funext j
    split_ifs with h
    · exact colG_goldCols _ _ _ h _
    · exact ofZ_zero.symm
  · funext j
    by_cases h1 : j < 123
    · by_cases h2 : (i : ℕ) + 1 < n
      · simp only [h1, h2, if_true, dif_pos]
        exact colG_goldCols T.cols 123 j h1 ⟨(i : ℕ) + 1, h2⟩
      · simp only [h1, h2, if_true, if_false, dif_neg, not_false_eq_true]
        rw [getD_map_ofZ, FastLag.nextArr_getD _ _ _ _ i h2 j h1]
    · simp [h1, ofZ_zero]

def srcXG : List SGX := CompX.srcX.map SGX.comp

/-- Cache size for the coins / publics read by the compute gates. -/
def srcXM : ℕ := 3 * srcXG.foldl (fun m g => max m g.mx) 0 + 3

def checkCompXG {n : ℕ} (T : TabX n) : Bool :=
  let A := goldCols T.cols 123
  let nxG := (FastLag.nextArr T.nodes T.ω T.cols 123).map Gold.ofZ
  let cG := GC.mk' T.chal srcXM
  let pG := GC.mk' T.pub srcXM
  (List.finRange n).all (fun i => srcXG.all (srcOKX (rowEnvX A nxG cG pG i))) &&
  ([(17, firstMaskE n), (18, lastMaskE n)] : List (ℕ × (Fin n → ZMod p))).all
    (fun q => (List.finRange n).all fun i => decide (T.cols q.1 i = q.2 i))

theorem checkCompX_eq_G : @checkCompX = @checkCompXG := by
  funext n T
  simp only [checkCompXG, checkCompX, rowEnvX_eq, srcXG, List.all_map, Function.comp_def, srcOKX_eq]

attribute [csimp] checkCompX_eq_G

section Mem
variable (Tm : ChipTemplate (ZMod p))

def rowEnvM {n : ℕ} (w : ℕ) (A : Array (Array Gold)) (nxG : Array Gold) (cG pG : GC) (i : Fin n) : Env Gold where
  trace := fun j => if j < w then colG A j i else 0
  traceNext := fun j => if j < w then
      (if (i : ℕ) + 1 < n then colG A j (i + 1) else nxG.getD j 0) else 0
  chal := fun j => cG.get j
  pub := fun j => pG.get j

theorem rowEnvM_eq {n : ℕ} (T : TabM n) (m : ℕ) (i : Fin n) :
    rowEnvM (Tm.width 3) (goldCols T.cols (Tm.width 3))
      ((FastLag.nextArr T.nodes T.ω T.cols (Tm.width 3)).map Gold.ofZ)
      (GC.mk' (slotE Tm.baseCols T.chals) m) (GC.mk' (slotE Tm.baseCols T.pubs) m) i =
      gEnvOf (T.env Tm i) := by
  simp only [rowEnvM, gEnvOf, TabM.env, Env.mk.injEq, GC.get_mk', and_true, true_and]
  constructor
  · funext j
    split_ifs with h
    · exact colG_goldCols _ _ _ h _
    · exact ofZ_zero.symm
  · funext j
    by_cases h1 : j < Tm.width 3
    · by_cases h2 : (i : ℕ) + 1 < n
      · simp only [h1, h2, if_true, dif_pos]
        exact colG_goldCols T.cols (Tm.width 3) j h1 ⟨(i : ℕ) + 1, h2⟩
      · simp only [h1, h2, if_true, if_false, dif_neg, not_false_eq_true]
        rw [getD_map_ofZ, FastLag.nextArr_getD _ _ _ _ i h2 j h1]
    · simp [h1, ofZ_zero]

def checkMG {n : ℕ} (T : TabM n) : Bool :=
  let src := (srcM Tm).map SGF.comp
  let mm := 3 * (src.foldl (fun m g => max m g.mx) 0) + Tm.baseCols + 3
  let w := Tm.width 3
  let A := goldCols T.cols w
  let nxG := (FastLag.nextArr T.nodes T.ω T.cols w).map Gold.ofZ
  let cG := GC.mk' (slotE Tm.baseCols T.chals) mm
  let pG := GC.mk' (slotE Tm.baseCols T.pubs) mm
  (List.finRange n).all (fun i => src.all (srcOKM Tm.baseCols (rowEnvM w A nxG cG pG i))) &&
  T.prep.all (fun q => (List.finRange n).all fun i => decide (T.cols q.1 i = q.2 i))

theorem checkM_eq_G : @checkM = @checkMG := by
  funext Tm n T
  simp only [checkMG, checkM, rowEnvM_eq, List.all_map, Function.comp_def, srcOKM_eq]

end Mem

attribute [csimp] checkM_eq_G

end Nock.V1J8.FastEval
