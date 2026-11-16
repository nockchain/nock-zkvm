/-
  Nock/NockVMROM/Thm54/CoordinateCompiler.lean

  `CoordinateBasis.lean` pilots coordinate expansion for the *linear* fragment and records the
  obstruction (lines 27-29 there): `Nock.Reified.Expr.Const` carries `ℤ`, so a basis element
  `b i ∈ K \ ℤ` cannot be an `Expr` constant, and `Mul`/`Pow` expansion additionally needs the
  extension's structure constants.  This module removes that obstruction:

  * `CoeffExpr F` — a **base-field** constraint expression language (constants in `F`, not `ℤ`),
    with `eval` and `degree` mirroring `Nock.Reified.Expr`'s conventions exactly.
  * `mulTensor` — the multiplication tensor (structure constants) of `K/F` against a coordinate
    basis, and `coord_mul`: `coord b (x*y) k = ∑ i, ∑ j, coord b x i * coord b y j * T i j k`.
  * `coordinateCompile` — compiles one `K`-valued `Expr` into `e` base-field `CoeffExpr F`s, one per
    coordinate: `Var` expands to `e` columns at offset `col0`, `Const`/`Add`/`Sub`/`Neg` are linear,
    `Mul` goes through the tensor, `Pow` through iterated `Mul`.
  * `coordinateCompile_eval` — **evaluation correctness**, against the coordinate-expanded
    environment relation `IsCoordEnv` (inhabited by `stdCoordEnv`/`isCoordEnv_std`, so the
    hypothesis is not vacuous).
  * `coordinateCompile_degree_le` — **degree is not increased**, which is what keeps the paper's
    max-degree-4 budget intact under expansion.
  * `coordinateCompile_zero_iff` — one `K`-equation `E = 0` is equivalent to the `e` base-field
    coordinate equations.

  Scope: this is the *compiler*, not the RAP.  Row layouts, `StagedRAP` and the named monolithic
  RAPs are downstream packets and are not claimed here.
-/

import Nock.NockVMROM.Thm54.CoordinateBasis

namespace Nock.NockVMROM.Thm54
namespace CoordinateCompiler

open Nock.Reified
open Module
open CoordinateBasis

/-! ## 1. A base-field coefficient expression language

`Nock.Reified.Expr` restricts constants to `ℤ`.  Coordinate expansion produces constants that are
genuine base-field elements (coordinates of `1 : K`, and structure constants), so the target
language carries `F`-valued constants.  Everything else mirrors `Expr` one-for-one, including the
`VarKind` variable discipline and both `eval` and `degree`. -/

/-- Base-field constraint expressions: the image language of the coordinate compiler. -/
inductive CoeffExpr (F : Type*) where
  /-- A base-field constant (this is the constructor `Expr.Const : ℤ → Expr` cannot provide). -/
  | const : F → CoeffExpr F
  /-- A base-field column of the given `VarKind`. -/
  | var : VarKind → ℕ → CoeffExpr F
  /-- Addition. -/
  | add : CoeffExpr F → CoeffExpr F → CoeffExpr F
  /-- Subtraction. -/
  | sub : CoeffExpr F → CoeffExpr F → CoeffExpr F
  /-- Multiplication. -/
  | mul : CoeffExpr F → CoeffExpr F → CoeffExpr F
  /-- Negation. -/
  | neg : CoeffExpr F → CoeffExpr F
  /-- Natural-number power. -/
  | pow : CoeffExpr F → ℕ → CoeffExpr F

namespace CoeffExpr

/-- Evaluate a base-field expression under an `F`-environment (mirrors `Expr.eval`). -/
def eval {F : Type*} [Field F] : CoeffExpr F → Env F → F
  | .const c, _ => c
  | .var .traceCur i, env => env.trace i
  | .var .traceNext i, env => env.traceNext i
  | .var .challenge i, env => env.chal i
  | .var .publicVal i, env => env.pub i
  | .add a b, env => a.eval env + b.eval env
  | .sub a b, env => a.eval env - b.eval env
  | .mul a b, env => a.eval env * b.eval env
  | .neg a, env => -a.eval env
  | .pow a n, env => (a.eval env) ^ n

/-- Trace-degree of a base-field expression (mirrors `Expr.degree`: trace columns are degree `1`,
constants / challenges / public values are degree `0`). -/
def degree {F : Type*} : CoeffExpr F → ℕ
  | .const _ => 0
  | .var .traceCur _ => 1
  | .var .traceNext _ => 1
  | .var .challenge _ => 0
  | .var .publicVal _ => 0
  | .add a b => max a.degree b.degree
  | .sub a b => max a.degree b.degree
  | .mul a b => a.degree + b.degree
  | .neg a => a.degree
  | .pow a n => n * a.degree

/-- A finite sum of base-field expressions, indexed by a list. -/
def sumList {F : Type*} [Field F] {ι : Type*} (l : List ι) (f : ι → CoeffExpr F) : CoeffExpr F :=
  l.foldr (fun i acc => .add (f i) acc) (.const 0)

/-- Evaluating a listed sum is the sum of the evaluations. -/
theorem eval_sumList {F : Type*} [Field F] {ι : Type*} (l : List ι) (f : ι → CoeffExpr F)
    (env : Env F) : (sumList l f).eval env = (l.map (fun i => (f i).eval env)).sum := by
  induction l with
  | nil => simp [sumList, eval]
  | cons a l ih => simp [sumList, eval] at ih ⊢; rw [ih]

/-- A listed sum has degree at most any common bound on its summands. -/
theorem degree_sumList_le {F : Type*} [Field F] {ι : Type*} (l : List ι) (f : ι → CoeffExpr F)
    (d : ℕ) (h : ∀ i ∈ l, (f i).degree ≤ d) : (sumList l f).degree ≤ d := by
  induction l with
  | nil => simp [sumList, degree]
  | cons a l ih =>
      have ha : (f a).degree ≤ d := h a (by simp)
      have hl : ∀ i ∈ l, (f i).degree ≤ d := fun i hi => h i (by simp [hi])
      simp only [sumList, List.foldr_cons, degree]
      exact max_le ha (ih hl)

end CoeffExpr

/-! ## 2. Structure constants of `K/F` -/

noncomputable section

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **The multiplication tensor of `K/F`.**  `mulTensor b i j k` is the `k`-th coordinate of
`b i * b j`; these are the structure constants of the extension in the chosen basis. -/
def mulTensor {e : ℕ} (b : Basis (Fin e) F K) (i j k : Fin e) : F :=
  coord b (b i * b j) k

omit [FiniteDimensional F K] in
/-- Coordinates commute with finite sums. -/
theorem coord_sum {ι : Type*} {e : ℕ} (b : Basis (Fin e) F K) (s : Finset ι) (f : ι → K)
    (k : Fin e) : coord b (∑ i ∈ s, f i) k = ∑ i ∈ s, coord b (f i) k := by
  classical
  simp only [coord, map_sum, Finset.sum_apply']

omit [FiniteDimensional F K] in
/-- Coordinates of a negation. -/
theorem coord_neg {e : ℕ} (b : Basis (Fin e) F K) (x : K) (k : Fin e) :
    coord b (-x) k = -coord b x k := by
  simp only [coord, map_neg, Finsupp.neg_apply]

omit [FiniteDimensional F K] in
/-- Coordinates of a difference. -/
theorem coord_sub {e : ℕ} (b : Basis (Fin e) F K) (x y : K) (k : Fin e) :
    coord b (x - y) k = coord b x k - coord b y k := by
  simp only [coord, map_sub, Finsupp.sub_apply]

omit [FiniteDimensional F K] in
/-- Coordinates of a zero. -/
theorem coord_zero {e : ℕ} (b : Basis (Fin e) F K) (k : Fin e) : coord b (0 : K) k = 0 := by
  simp only [coord, map_zero, Finsupp.coe_zero, Pi.zero_apply]

/-- **Coordinates of an integer constant.**  `Expr.Const c` denotes `(c : K)`, whose coordinates are
`(c : F)` times those of `1 : K` — determined, but generally *not* integers, which is exactly why
the target language needs `F`-valued constants. -/
theorem coord_intCast {e : ℕ} (b : Basis (Fin e) F K) (c : ℤ) (k : Fin e) :
    coord b ((c : K)) k = (c : F) * coord b (1 : K) k := by
  have h : ((c : K)) = (c : F) • (1 : K) := by
    rw [Algebra.smul_def, mul_one, map_intCast]
  rw [h, coord_smul, smul_eq_mul]

/-- **The bilinear expansion of multiplication** — the crux of nonlinear coordinate expansion:
the coordinates of a product are the tensor contraction of the factors' coordinates. -/
theorem coord_mul {e : ℕ} (b : Basis (Fin e) F K) (x y : K) (k : Fin e) :
    coord b (x * y) k = ∑ i, ∑ j, coord b x i * coord b y j * mulTensor b i j k := by
  have hx : x = ∑ i, coord b x i • b i := (b.sum_repr x).symm
  have hy : y = ∑ j, coord b y j • b j := (b.sum_repr y).symm
  calc coord b (x * y) k
      = coord b ((∑ i, coord b x i • b i) * (∑ j, coord b y j • b j)) k := by
        rw [← hx, ← hy]
    _ = ∑ i, ∑ j, coord b x i * coord b y j * mulTensor b i j k := by
        rw [Finset.sum_mul_sum, coord_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [coord_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_mul_smul_comm, coord_smul, smul_eq_mul, mulTensor]

omit [FiniteDimensional F K] in
/-- **The multiplication tensor is not all-zero.**  For any pair of basis indices some structure
constant is nonzero, so the `Mul` case of the compiler genuinely contracts against nontrivial data
(this is what rules out a degenerate/vacuous tensor). -/
theorem mulTensor_not_all_zero {e : ℕ} (b : Basis (Fin e) F K) (i j : Fin e) :
    ∃ k, mulTensor b i j k ≠ 0 := by
  by_contra hcon
  have hall : ∀ k, mulTensor b i j k = 0 := by
    intro k
    by_contra hk
    exact hcon ⟨k, hk⟩
  have hzero : b i * b j = 0 := by
    have hrepr : b.repr (b i * b j) = 0 := by
      ext k
      simpa [coord, mulTensor] using hall k
    have := congrArg b.repr.symm hrepr
    simpa using this
  rcases mul_eq_zero.mp hzero with h | h
  · exact b.ne_zero i h
  · exact b.ne_zero j h

/-! ## 3. The compiler -/

/-- The `k`-th coordinate expression of the product of two already-compiled coordinate vectors:
`∑ i, ∑ j, u i * v j * T i j k`. -/
def mulVec {e : ℕ} (b : Basis (Fin e) F K) (u v : Fin e → CoeffExpr F) (k : Fin e) : CoeffExpr F :=
  CoeffExpr.sumList (Finset.univ : Finset (Fin e)).toList fun i =>
    CoeffExpr.sumList (Finset.univ : Finset (Fin e)).toList fun j =>
      .mul (.mul (u i) (v j)) (.const (mulTensor b i j k))

/-- The compiled coordinate vector of `1 : K`. -/
def oneVec {e : ℕ} (b : Basis (Fin e) F K) (k : Fin e) : CoeffExpr F :=
  .const (coord b (1 : K) k)

/-- Iterated `mulVec`: the compiled coordinate vector of an `n`-th power. -/
def powVec {e : ℕ} (b : Basis (Fin e) F K) (u : Fin e → CoeffExpr F) :
    ℕ → Fin e → CoeffExpr F
  | 0 => oneVec b
  | n + 1 => mulVec b (powVec b u n) u

/-- **The coordinate compiler.**  Compiles one `K`-valued constraint expression into its `e`
base-field coordinate expressions.  Each `K`-column `Var kind idx` occupies the `e` base columns
`col0 kind idx, …, col0 kind idx + (e-1)`. -/
def coordinateCompile {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ) :
    Expr → Fin e → CoeffExpr F
  | .Var kind idx => fun k => .var kind (col0 kind idx + (k : ℕ))
  | .Const c => fun k => .const ((c : F) * coord b (1 : K) k)
  | .Add x y => fun k => .add (coordinateCompile b col0 x k) (coordinateCompile b col0 y k)
  | .Sub x y => fun k => .sub (coordinateCompile b col0 x k) (coordinateCompile b col0 y k)
  | .Neg x => fun k => .neg (coordinateCompile b col0 x k)
  | .Mul x y => mulVec b (coordinateCompile b col0 x) (coordinateCompile b col0 y)
  | .Pow x n => powVec b (coordinateCompile b col0 x) n

/-! ## 4. The coordinate-expanded environment -/

/-- **`envF` is the coordinate expansion of `envK`**: every `K`-column's value has its `e`
coordinates laid at the base columns starting at `col0`. -/
structure IsCoordEnv {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    (envK : Env K) (envF : Env F) : Prop where
  /-- Current-row trace columns. -/
  trace : ∀ (idx : ℕ) (k : Fin e),
    envF.trace (col0 .traceCur idx + (k : ℕ)) = coord b (envK.trace idx) k
  /-- Next-row trace columns. -/
  traceNext : ∀ (idx : ℕ) (k : Fin e),
    envF.traceNext (col0 .traceNext idx + (k : ℕ)) = coord b (envK.traceNext idx) k
  /-- Challenge columns. -/
  chal : ∀ (idx : ℕ) (k : Fin e),
    envF.chal (col0 .challenge idx + (k : ℕ)) = coord b (envK.chal idx) k
  /-- Public columns. -/
  pub : ∀ (idx : ℕ) (k : Fin e),
    envF.pub (col0 .publicVal idx + (k : ℕ)) = coord b (envK.pub idx) k

/-- The canonical striding layout: the `e` coordinates of `K`-column `idx` occupy base columns
`e·idx, …, e·idx + (e-1)`. -/
def stdCol0 (e : ℕ) : VarKind → ℕ → ℕ := fun _ idx => e * idx

/-- The canonical coordinate expansion of a `K`-environment under `stdCol0`. -/
def stdCoordEnv {e : ℕ} [NeZero e] (b : Basis (Fin e) F K) (envK : Env K) : Env F where
  trace := fun j =>
    coord b (envK.trace (j / e)) ⟨j % e, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne e))⟩
  traceNext := fun j =>
    coord b (envK.traceNext (j / e)) ⟨j % e, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne e))⟩
  chal := fun j =>
    coord b (envK.chal (j / e)) ⟨j % e, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne e))⟩
  pub := fun j =>
    coord b (envK.pub (j / e)) ⟨j % e, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne e))⟩

/-- Decoding the canonical striding layout: base column `e·idx + k` carries coordinate `k` of
`K`-column `idx`. -/
theorem std_index {e : ℕ} [NeZero e] (idx : ℕ) (k : Fin e) :
    (e * idx + (k : ℕ)) / e = idx ∧ (e * idx + (k : ℕ)) % e = (k : ℕ) := by
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  constructor
  · rw [Nat.mul_add_div he, Nat.div_eq_of_lt k.isLt, add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt k.isLt]

omit [FiniteDimensional F K] in
/-- **The canonical expansion really is a coordinate environment** — so `IsCoordEnv` is inhabited
and the correctness theorems below are not vacuous. -/
theorem isCoordEnv_std {e : ℕ} [NeZero e] (b : Basis (Fin e) F K) (envK : Env K) :
    IsCoordEnv b (stdCol0 e) envK (stdCoordEnv b envK) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · intro idx k
      obtain ⟨h1, h2⟩ := std_index (e := e) idx k
      simp only [stdCoordEnv, stdCol0, h1, h2, Fin.eta]

/-! ## 5. Correctness: evaluation -/

/-- Evaluating the compiled product against the tensor reproduces the product's coordinate. -/
theorem eval_mulVec {e : ℕ} (b : Basis (Fin e) F K) (envF : Env F) (u v : Fin e → CoeffExpr F)
    (x y : K) (hu : ∀ i, coord b x i = (u i).eval envF)
    (hv : ∀ j, coord b y j = (v j).eval envF) (k : Fin e) :
    coord b (x * y) k = (mulVec b u v k).eval envF := by
  rw [coord_mul b x y k]
  simp only [mulVec, CoeffExpr.eval_sumList, Finset.sum_map_toList, CoeffExpr.eval]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by rw [hu i, hv j]

/-- Evaluating the compiled power reproduces the power's coordinate. -/
theorem eval_powVec {e : ℕ} (b : Basis (Fin e) F K) (envF : Env F) (u : Fin e → CoeffExpr F)
    (x : K) (hu : ∀ i, coord b x i = (u i).eval envF) :
    ∀ (n : ℕ) (k : Fin e), coord b (x ^ n) k = (powVec b u n k).eval envF
  | 0, k => by simp only [pow_zero, powVec, oneVec, CoeffExpr.eval]
  | n + 1, k => by
      rw [pow_succ]
      exact eval_mulVec b envF (powVec b u n) u (x ^ n) x
        (fun i => eval_powVec b envF u x hu n i) hu k

/-- **Evaluation correctness of the coordinate compiler.**  The `k`-th coordinate of the `K`-value
of a constraint expression equals the value of its `k`-th compiled base-field expression, evaluated
in any coordinate-expanded environment. -/
theorem coordinateCompile_eval {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    {envK : Env K} {envF : Env F} (h : IsCoordEnv b col0 envK envF) (E : Expr) (k : Fin e) :
    coord b (E.eval envK) k = (coordinateCompile b col0 E k).eval envF := by
  induction E generalizing k with
  | Var kind idx =>
      cases kind
      · exact (h.trace idx k).symm
      · exact (h.traceNext idx k).symm
      · exact (h.chal idx k).symm
      · exact (h.pub idx k).symm
  | Const c => exact coord_intCast b c k
  | Add x y ihx ihy =>
      simp only [Expr.eval, coordinateCompile, CoeffExpr.eval, coord_add, ihx, ihy]
  | Sub x y ihx ihy =>
      simp only [Expr.eval, coordinateCompile, CoeffExpr.eval, coord_sub, ihx, ihy]
  | Neg x ihx =>
      simp only [Expr.eval, coordinateCompile, CoeffExpr.eval, coord_neg, ihx]
  | Mul x y ihx ihy =>
      exact eval_mulVec b envF _ _ (x.eval envK) (y.eval envK) ihx ihy k
  | Pow x n ihx =>
      exact eval_powVec b envF _ (x.eval envK) ihx n k

/-! ## 6. Correctness: degree is not increased -/

omit [FiniteDimensional F K] in
/-- The compiled product's degree is bounded by the sum of the factors' bounds. -/
theorem degree_mulVec_le {e : ℕ} (b : Basis (Fin e) F K) (u v : Fin e → CoeffExpr F) (du dv : ℕ)
    (hu : ∀ i, (u i).degree ≤ du) (hv : ∀ j, (v j).degree ≤ dv) (k : Fin e) :
    (mulVec b u v k).degree ≤ du + dv := by
  refine CoeffExpr.degree_sumList_le _ _ _ fun i _ => ?_
  refine CoeffExpr.degree_sumList_le _ _ _ fun j _ => ?_
  simp only [CoeffExpr.degree, add_zero]
  exact Nat.add_le_add (hu i) (hv j)

omit [FiniteDimensional F K] in
/-- The compiled power's degree is bounded by `n` times the base's bound. -/
theorem degree_powVec_le {e : ℕ} (b : Basis (Fin e) F K) (u : Fin e → CoeffExpr F) (d : ℕ)
    (hu : ∀ i, (u i).degree ≤ d) : ∀ (n : ℕ) (k : Fin e), (powVec b u n k).degree ≤ n * d
  | 0, k => by simp [powVec, oneVec, CoeffExpr.degree]
  | n + 1, k => by
      have := degree_mulVec_le b (powVec b u n) u (n * d) d
        (fun i => degree_powVec_le b u d hu n i) hu k
      simpa [powVec, Nat.succ_mul] using this

omit [FiniteDimensional F K] in
/-- **The coordinate compiler does not increase constraint degree.**  Every compiled coordinate
expression has trace-degree at most that of the source `K`-expression, so coordinate expansion
preserves the AIR's max-degree budget. -/
theorem coordinateCompile_degree_le {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    (E : Expr) (k : Fin e) : (coordinateCompile b col0 E k).degree ≤ E.degree := by
  induction E generalizing k with
  | Var kind idx => cases kind <;> simp [coordinateCompile, CoeffExpr.degree, Expr.degree]
  | Const c => simp [coordinateCompile, CoeffExpr.degree, Expr.degree]
  | Add x y ihx ihy =>
      simp only [coordinateCompile, CoeffExpr.degree, Expr.degree]
      exact max_le_max (ihx k) (ihy k)
  | Sub x y ihx ihy =>
      simp only [coordinateCompile, CoeffExpr.degree, Expr.degree]
      exact max_le_max (ihx k) (ihy k)
  | Neg x ihx =>
      simp only [coordinateCompile, CoeffExpr.degree, Expr.degree]
      exact ihx k
  | Mul x y ihx ihy =>
      exact degree_mulVec_le b _ _ x.degree y.degree ihx ihy k
  | Pow x n ihx =>
      refine le_trans (degree_powVec_le b _ x.degree ihx n k) ?_
      simp only [Expr.degree]
      cases hd : x.degree with
      | zero => simp [Expr.powDegree, hd]
      | succ d =>
          simp only [Expr.powDegree, hd]
          rw [Nat.mul_comm]

/-! ## 7. One `K`-equation ⟺ `e` base-field equations -/

/-- **The full-vector form.**  A single `K`-valued constraint `E = 0` holds iff all `e` compiled
base-field coordinate constraints vanish. -/
theorem coordinateCompile_zero_iff {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    {envK : Env K} {envF : Env F} (h : IsCoordEnv b col0 envK envF) (E : Expr) :
    E.eval envK = 0 ↔ ∀ k, (coordinateCompile b col0 E k).eval envF = 0 := by
  rw [eq_iff_coords_eq b (E.eval envK) 0]
  constructor
  · intro hk k
    rw [← coordinateCompile_eval b col0 h E k, hk k, coord_zero]
  · intro hk k
    rw [coord_zero, coordinateCompile_eval b col0 h E k]
    exact hk k

/-- The same statement against the canonical expansion, with no environment hypothesis at all. -/
theorem coordinateCompile_zero_iff_std {e : ℕ} [NeZero e] (b : Basis (Fin e) F K) (envK : Env K)
    (E : Expr) :
    E.eval envK = 0 ↔
      ∀ k, (coordinateCompile b (stdCol0 e) E k).eval (stdCoordEnv b envK) = 0 :=
  coordinateCompile_zero_iff b (stdCol0 e) (isCoordEnv_std b envK) E

/-- Consecutive `K`-columns occupy disjoint blocks of exactly `e` base columns under the canonical
layout — the width bookkeeping behind `base + ext·e`. -/
theorem stdCol0_succ (e : ℕ) (kind : VarKind) (idx : ℕ) :
    stdCol0 e kind (idx + 1) = stdCol0 e kind idx + e := by
  simp [stdCol0, Nat.mul_succ]

end

end CoordinateCompiler
end Nock.NockVMROM.Thm54
