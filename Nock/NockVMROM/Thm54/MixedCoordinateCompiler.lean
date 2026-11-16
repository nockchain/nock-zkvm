/-
  Nock/NockVMROM/Thm54/MixedCoordinateCompiler.lean

  **A `𝕂`-valued expression language whose leaves may be base-field expressions.**

  `CoordinateCompiler.coordinateCompile` compiles `Nock.Reified.Expr` — a language in which every
  `Var` is a `𝕂`-column — so a gate that must read a *base-field* column is unwritable, and the
  memory chip transcribes such gates by hand at coordinate level and then compresses the `e`
  coordinates with a scalar random-linear-combination coin.  That coin is the entire source of the
  memory half of the `/|𝔽|` false-acceptance summand.

  The restriction is **the tree's, not the paper's.**  `Def:RAP` carries one
  coefficient field: `:139` "`𝔽` is the field over which the trace and polynomials are defined",
  and `:140` is the *whole* content of the `(𝕂, e)` component.  No coercion mechanism is ever
  named.  Yet the paper mixes base-field and extension data inside single gates, load-bearingly:

  * the paper — `ver(i)·(RLC^α(x_mem(i,·)) − β)·(acc_mem(i−1) − acc_mem(i)) =
    (acc_mem(i−1) − acc_mem(i))·(1 − ver(i)) + ver(i)`, with `ver` typed `𝔽` (`:557`) and
    `acc_mem` typed `𝕂` (`:488`): a bare base-field column as both a multiplicand and an
    **additive summand** of a `𝕂`-valued equation.
  * the paper — `(1 − op_11(i))·f_h.size(i) = z·Σ_{j≤9} op_j(i)`, and `:1898`
    `(1 − op_11(i))·f_h.leaf(i) = Σ_{j≤9} j·op_j(i)`, with `op_j : 𝔽^11` (`:1893`): base-field
    flags against a `𝕂` challenge.  This is exactly the "extension column = base-field data,
    possibly scaled" shape the memory chip calls `maskBindingCoord`.
  * also the paper.

  So the mechanism this module supplies is the paper's own construction, made writable.

  ## Shape

  `MixedExpr` is `Expr`'s nine constructors plus two:

  * `Lift  : CoeffExpr F → MixedExpr F` — the `algebraMap` of a base-field expression;
  * `Scale : CoeffExpr F → MixedExpr F → MixedExpr F` — a base-field scalar times a `𝕂` value.

  `Scale g u` is **semantically** `Mul (Lift g) u` (`scale_eval_eq_mul_lift`).  It is not redundant
  as *compilation*: through `Mul` the compiler routes to `mulVec`'s full `e²`-term tensor
  contraction, whereas `Scale` emits one scalar multiplication per coordinate.  Only the latter is
  definitionally the gate body the deployed memory chip already commits, so `Scale` is a
  constructor and not sugar.

  ## What it costs

  * **`mixedCompile_eval` takes exactly `IsCoordEnv b col0 envK envF`** — the same relation
    `coordinateCompile_eval` takes, with no added clause and no side condition.  The base-field
    leaves need no hypothesis at all: they are read from `envF` directly.
  * **`mixedCompile_degree_le`** — degree is *not* increased.  A base leaf costs its own
    `CoeffExpr.degree`, so a base column leaf costs degree `1`, the same as a `𝕂`-column leaf, and
    the paper's degree-`4` transition budget is untouched.
  * **`mixedCompile_zero_iff`** — one mixed `𝕂`-equation ⟺ its `e` base-field coordinate
    equations, unconditionally.  `∑ₖ cₖ·bₖ = 0 ↔ ∀ k, cₖ = 0` needs no randomness because `b` is a
    basis; this is what lets a retyped gate replace an RLC-compressed one *without a coin*.
  * **columns: zero.**  A mixed gate reads existing columns; nothing in `ChipTemplate.width`
    depends on the gate lists.

  SCOPE.  This module is additive and changes nothing deployed.  It supplies the compiler; which
  gates a chip commits is decided by the chip's own template.
-/

import Nock.NockVMROM.Thm54.CoordinateCompiler

namespace Nock.NockVMROM.Thm54
namespace MixedCoordinateCompiler

open Nock.Reified
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Module

noncomputable section

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## 1. The mixed expression language -/

/-- A `𝕂`-valued expression whose leaves may be **base-field** expressions.

`Var`/`Const`/`Add`/`Sub`/`Neg`/`Mul`/`Pow` mirror `Nock.Reified.Expr`; `Lift` and `Scale` are the
two new leaves that make base-field data readable inside a `𝕂`-valued gate. -/
inductive MixedExpr (F : Type*) where
  /-- A `𝕂`-valued column of the given kind. -/
  | Var    : VarKind → ℕ → MixedExpr F
  /-- The `algebraMap` image of a base-field expression. -/
  | Lift   : CoeffExpr F → MixedExpr F
  /-- A base-field scalar multiplying a `𝕂`-valued expression. -/
  | Scale  : CoeffExpr F → MixedExpr F → MixedExpr F
  /-- An integer constant, read in `𝕂`. -/
  | Const  : ℤ → MixedExpr F
  | Add    : MixedExpr F → MixedExpr F → MixedExpr F
  | Sub    : MixedExpr F → MixedExpr F → MixedExpr F
  | Neg    : MixedExpr F → MixedExpr F
  | Mul    : MixedExpr F → MixedExpr F → MixedExpr F
  | Pow    : MixedExpr F → ℕ → MixedExpr F

namespace MixedExpr

/-- Evaluation: `𝕂`-leaves read the `𝕂` environment, base-field leaves read the base environment
and are lifted along `algebraMap`. -/
def eval : MixedExpr F → Env K → Env F → K
  | .Var .traceCur i,  eK, _  => eK.trace i
  | .Var .traceNext i, eK, _  => eK.traceNext i
  | .Var .challenge i, eK, _  => eK.chal i
  | .Var .publicVal i, eK, _  => eK.pub i
  | .Lift g, _, eF => algebraMap F K (g.eval eF)
  | .Scale g u, eK, eF => algebraMap F K (g.eval eF) * u.eval eK eF
  | .Const c, _, _ => (c : K)
  | .Add x y, eK, eF => x.eval eK eF + y.eval eK eF
  | .Sub x y, eK, eF => x.eval eK eF - y.eval eK eF
  | .Neg x, eK, eF => - x.eval eK eF
  | .Mul x y, eK, eF => x.eval eK eF * y.eval eK eF
  | .Pow x n, eK, eF => (x.eval eK eF) ^ n

/-- Total degree in the trace variables; base-field leaves contribute their own
`CoeffExpr.degree`, so a base column leaf costs degree `1`, exactly as a `𝕂` column leaf does. -/
def degree : MixedExpr F → ℕ
  | .Var .traceCur _ => 1
  | .Var .traceNext _ => 1
  | .Var .challenge _ => 0
  | .Var .publicVal _ => 0
  | .Lift g => g.degree
  | .Scale g u => g.degree + u.degree
  | .Const _ => 0
  | .Add x y => max x.degree y.degree
  | .Sub x y => max x.degree y.degree
  | .Neg x => x.degree
  | .Mul x y => x.degree + y.degree
  | .Pow x n => n * x.degree

/-- The embedding of the `𝕂`-only language: every `Nock.Reified.Expr` is a `MixedExpr`. -/
def ofExpr : Expr → MixedExpr F
  | .Var kind idx => .Var kind idx
  | .Const c => .Const c
  | .Add x y => .Add (ofExpr x) (ofExpr y)
  | .Sub x y => .Sub (ofExpr x) (ofExpr y)
  | .Neg x => .Neg (ofExpr x)
  | .Mul x y => .Mul (ofExpr x) (ofExpr y)
  | .Pow x n => .Pow (ofExpr x) n

omit [FiniteDimensional F K] in
/-- `Scale` is semantically `Mul (Lift ·) ·`; it exists for what it *compiles* to, not for what it
means. -/
theorem scale_eval_eq_mul_lift (g : CoeffExpr F) (u : MixedExpr F)
    (eK : Env K) (eF : Env F) :
    (MixedExpr.Scale g u).eval (K := K) eK eF
      = (MixedExpr.Mul (MixedExpr.Lift g) u).eval (K := K) eK eF := rfl

omit [FiniteDimensional F K] in
/-- The embedding preserves evaluation: the base environment is simply unused. -/
theorem ofExpr_eval (E : Expr) (eK : Env K) (eF : Env F) :
    (ofExpr E : MixedExpr F).eval eK eF = E.eval eK := by
  induction E with
  | Var kind idx => cases kind <;> rfl
  | Const c => rfl
  | Add x y ihx ihy => simp only [ofExpr, eval, Expr.eval, ihx, ihy]
  | Sub x y ihx ihy => simp only [ofExpr, eval, Expr.eval, ihx, ihy]
  | Neg x ihx => simp only [ofExpr, eval, Expr.eval, ihx]
  | Mul x y ihx ihy => simp only [ofExpr, eval, Expr.eval, ihx, ihy]
  | Pow x n ihx => simp only [ofExpr, eval, Expr.eval, ihx]

omit [Field F] [FiniteDimensional F K] in
/-- The embedding preserves degree. -/
theorem ofExpr_degree (E : Expr) : (ofExpr E : MixedExpr F).degree = E.degree := by
  induction E with
  | Var kind idx => cases kind <;> rfl
  | Const c => rfl
  | Add x y ihx ihy => simp only [ofExpr, degree, Expr.degree, ihx, ihy]
  | Sub x y ihx ihy => simp only [ofExpr, degree, Expr.degree, ihx, ihy]
  | Neg x ihx => simp only [ofExpr, degree, Expr.degree, ihx]
  | Mul x y ihx ihy => simp only [ofExpr, degree, Expr.degree, ihx, ihy]
  | Pow x n ihx =>
      simp only [ofExpr, degree, Expr.degree, ihx]
      cases h : x.degree with
      | zero => simp [Expr.powDegree, h]
      | succ k => simp [Expr.powDegree, h, Nat.mul_comm]

end MixedExpr

/-! ## 2. The mixed coordinate compiler -/

/-- **The mixed coordinate compiler.**  Identical to `coordinateCompile` on the shared
constructors; the two new leaves are the point:

* `Lift g` compiles to `coord b 1 k • g` — **one** base column read per coordinate, not `e`;
* `Scale g u` compiles to `g · (compile u k)` — one scalar multiplication per coordinate, rather
  than `mulVec`'s `e²`-term tensor contraction. -/
def mixedCompile {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ) :
    MixedExpr F → Fin e → CoeffExpr F
  | .Var kind idx => fun k => .var kind (col0 kind idx + (k : ℕ))
  | .Lift g => fun k => .mul (.const (coord b (1 : K) k)) g
  | .Scale g u => fun k => .mul g (mixedCompile b col0 u k)
  | .Const c => fun k => .const ((c : F) * coord b (1 : K) k)
  | .Add x y => fun k => .add (mixedCompile b col0 x k) (mixedCompile b col0 y k)
  | .Sub x y => fun k => .sub (mixedCompile b col0 x k) (mixedCompile b col0 y k)
  | .Neg x => fun k => .neg (mixedCompile b col0 x k)
  | .Mul x y => mulVec b (mixedCompile b col0 x) (mixedCompile b col0 y)
  | .Pow x n => powVec b (mixedCompile b col0 x) n

/-- The `k`-th coordinate of a lifted base-field scalar is that scalar times `coord b 1 k`. -/
theorem coord_algebraMap {e : ℕ} (b : Basis (Fin e) F K) (x : F) (k : Fin e) :
    coord b (algebraMap F K x) k = x * coord b (1 : K) k := by
  rw [Algebra.algebraMap_eq_smul_one, coord_smul, smul_eq_mul]

/-- Multiplying by a lifted base-field scalar acts coordinatewise. -/
theorem coord_algebraMap_mul {e : ℕ} (b : Basis (Fin e) F K) (y : F) (x : K) (k : Fin e) :
    coord b (algebraMap F K y * x) k = y * coord b x k := by
  rw [← Algebra.smul_def, coord_smul, smul_eq_mul]

/-- **Evaluation correctness.**  The hypothesis is *exactly* `IsCoordEnv b col0 envK envF`, the
same relation `coordinateCompile_eval` takes: the base-field leaves need no extra hypothesis, so
the coordinate-environment discipline survives the extension verbatim. -/
theorem mixedCompile_eval {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    {envK : Env K} {envF : Env F} (h : IsCoordEnv b col0 envK envF)
    (E : MixedExpr F) (k : Fin e) :
    coord b (E.eval envK envF) k = (mixedCompile b col0 E k).eval envF := by
  induction E generalizing k with
  | Var kind idx =>
      cases kind
      · exact (h.trace idx k).symm
      · exact (h.traceNext idx k).symm
      · exact (h.chal idx k).symm
      · exact (h.pub idx k).symm
  | Lift g =>
      simp only [MixedExpr.eval, mixedCompile, CoeffExpr.eval, coord_algebraMap, mul_comm]
  | Scale g u ihu =>
      simp only [MixedExpr.eval, mixedCompile, CoeffExpr.eval, coord_algebraMap_mul, ihu]
  | Const c => exact coord_intCast b c k
  | Add x y ihx ihy =>
      simp only [MixedExpr.eval, mixedCompile, CoeffExpr.eval, coord_add, ihx, ihy]
  | Sub x y ihx ihy =>
      simp only [MixedExpr.eval, mixedCompile, CoeffExpr.eval, coord_sub, ihx, ihy]
  | Neg x ihx => simp only [MixedExpr.eval, mixedCompile, CoeffExpr.eval, coord_neg, ihx]
  | Mul x y ihx ihy =>
      exact eval_mulVec b envF _ _ (x.eval envK envF) (y.eval envK envF) ihx ihy k
  | Pow x n ihx => exact eval_powVec b envF _ (x.eval envK envF) ihx n k

omit [FiniteDimensional F K] in
/-- **Compilation does not increase degree.**  In particular a base-field column leaf costs
degree `1` — the same as a `𝕂`-column leaf — so the paper's degree-`4` transition budget and degree-`1` endpoint budget (`:1467`, `:1487`) are untouched. -/
theorem mixedCompile_degree_le {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    (E : MixedExpr F) (k : Fin e) : (mixedCompile b col0 E k).degree ≤ E.degree := by
  induction E generalizing k with
  | Var kind idx => cases kind <;> simp [mixedCompile, CoeffExpr.degree, MixedExpr.degree]
  | Lift g => simp [mixedCompile, CoeffExpr.degree, MixedExpr.degree]
  | Scale g u ihu =>
      simp only [mixedCompile, CoeffExpr.degree, MixedExpr.degree]
      exact Nat.add_le_add_left (ihu k) _
  | Const c => simp [mixedCompile, CoeffExpr.degree, MixedExpr.degree]
  | Add x y ihx ihy =>
      simp only [mixedCompile, CoeffExpr.degree, MixedExpr.degree]
      exact max_le_max (ihx k) (ihy k)
  | Sub x y ihx ihy =>
      simp only [mixedCompile, CoeffExpr.degree, MixedExpr.degree]
      exact max_le_max (ihx k) (ihy k)
  | Neg x ihx => simp only [mixedCompile, CoeffExpr.degree, MixedExpr.degree]; exact ihx k
  | Mul x y ihx ihy => exact degree_mulVec_le b _ _ x.degree y.degree ihx ihy k
  | Pow x n ihx => exact degree_powVec_le b _ x.degree ihx n k

/-- **One mixed `𝕂`-equation ⟺ its `e` base-field coordinate equations.**

This is the whole reason a retyped gate needs no compression coin: `∑ₖ cₖ·bₖ = 0 ↔ ∀ k, cₖ = 0`
holds because `b` is a basis, with no randomness anywhere. -/
theorem mixedCompile_zero_iff {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    {envK : Env K} {envF : Env F} (h : IsCoordEnv b col0 envK envF) (E : MixedExpr F) :
    E.eval envK envF = 0 ↔ ∀ k, (mixedCompile b col0 E k).eval envF = 0 := by
  rw [eq_iff_coords_eq b (E.eval envK envF) 0]
  constructor
  · intro hk k
    rw [← mixedCompile_eval b col0 h E k, hk k, coord_zero]
  · intro hk k
    rw [coord_zero, mixedCompile_eval b col0 h E k]
    exact hk k

omit [FiniteDimensional F K] in
/-- On the embedded `𝕂`-only language the mixed compiler **is** `coordinateCompile`. -/
theorem mixedCompile_ofExpr {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    (E : Expr) (k : Fin e) :
    mixedCompile b col0 (MixedExpr.ofExpr E : MixedExpr F) k = coordinateCompile b col0 E k := by
  induction E generalizing k with
  | Var kind idx => cases kind <;> rfl
  | Const c => rfl
  | Add x y ihx ihy => simp only [MixedExpr.ofExpr, mixedCompile, coordinateCompile, ihx, ihy]
  | Sub x y ihx ihy => simp only [MixedExpr.ofExpr, mixedCompile, coordinateCompile, ihx, ihy]
  | Neg x ihx => simp only [MixedExpr.ofExpr, mixedCompile, coordinateCompile, ihx]
  | Mul x y ihx ihy =>
      simp only [MixedExpr.ofExpr, mixedCompile, coordinateCompile]
      congr 1 <;> funext j <;> [exact ihx j; exact ihy j]
  | Pow x n ihx =>
      simp only [MixedExpr.ofExpr, mixedCompile, coordinateCompile]
      congr 1
      funext j
      exact ihx j

/-! ## 3. Expanding a list of mixed gates

The chip-level analogues of `coordVec` / `expandList`, with the same counting law: one mixed
`𝕂`-valued gate becomes exactly `e` base-field gates, so it belongs in the paper's `·e` bucket. -/

/-- The `e` compiled base-field coordinate gates of one mixed `𝕂`-valued gate. -/
def mixedCoordVec {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ) (g : MixedExpr F) :
    List (CoeffExpr F) :=
  (List.finRange e).map (mixedCompile b col0 g)

/-- Coordinate-expand a whole list of mixed `𝕂`-valued gates. -/
def mixedExpandList {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    (l : List (MixedExpr F)) : List (CoeffExpr F) :=
  l.flatMap (mixedCoordVec b col0)

omit [FiniteDimensional F K] in
@[simp] theorem length_mixedCoordVec {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    (g : MixedExpr F) : (mixedCoordVec b col0 g).length = e := by
  simp [mixedCoordVec]

omit [FiniteDimensional F K] in
/-- **One mixed `𝕂`-valued gate becomes exactly `e` base-field gates.** -/
theorem length_mixedExpandList {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    (l : List (MixedExpr F)) : (mixedExpandList b col0 l).length = l.length * e := by
  induction l with
  | nil => simp [mixedExpandList]
  | cons a t ih =>
      simp only [mixedExpandList, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
      rw [ih, length_mixedCoordVec]
      ring

omit [FiniteDimensional F K] in
theorem mem_mixedExpandList {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    (l : List (MixedExpr F)) (u : CoeffExpr F) :
    u ∈ mixedExpandList b col0 l ↔ ∃ g ∈ l, ∃ k : Fin e, u = mixedCompile b col0 g k := by
  simp only [mixedExpandList, List.mem_flatMap, mixedCoordVec, List.mem_map, List.mem_finRange]
  constructor
  · rintro ⟨g, hg, k, -, rfl⟩; exact ⟨g, hg, k, rfl⟩
  · rintro ⟨g, hg, k, rfl⟩; exact ⟨g, hg, k, trivial, rfl⟩

omit [FiniteDimensional F K] in
/-- **Mixed expansion does not increase gate degree**, so a chip's paper degree budgets survive. -/
theorem degree_mixedExpandList_le {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    (l : List (MixedExpr F)) (d : ℕ) (hl : ∀ g ∈ l, g.degree ≤ d) :
    ∀ u ∈ mixedExpandList b col0 l, u.degree ≤ d := by
  intro u hu
  obtain ⟨g, hg, k, rfl⟩ := (mem_mixedExpandList b col0 l u).mp hu
  exact (mixedCompile_degree_le b col0 g k).trans (hl g hg)

/-- **The whole expanded list vanishes ⟺ every mixed gate vanishes in the `𝕂` environment.**
The chip-level form of `mixedCompile_zero_iff`; again unconditional, again coin-free. -/
theorem mixedExpandList_zero_iff {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    {envK : Env K} {envF : Env F} (h : IsCoordEnv b col0 envK envF) (l : List (MixedExpr F)) :
    (∀ u ∈ mixedExpandList b col0 l, u.eval envF = 0) ↔ ∀ g ∈ l, g.eval envK envF = 0 := by
  constructor
  · intro hu g hg
    exact (mixedCompile_zero_iff b col0 h g).2 fun k =>
      hu _ ((mem_mixedExpandList b col0 l _).2 ⟨g, hg, k, rfl⟩)
  · intro hg u hu
    obtain ⟨g, hgmem, k, rfl⟩ := (mem_mixedExpandList b col0 l u).mp hu
    exact (mixedCompile_zero_iff b col0 h g).1 (hg g hgmem) k

end
end MixedCoordinateCompiler
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.MixedCoordinateCompiler.mixedCompile_eval
#print axioms Nock.NockVMROM.Thm54.MixedCoordinateCompiler.mixedCompile_degree_le
#print axioms Nock.NockVMROM.Thm54.MixedCoordinateCompiler.mixedCompile_zero_iff
#print axioms Nock.NockVMROM.Thm54.MixedCoordinateCompiler.mixedCompile_ofExpr
#print axioms Nock.NockVMROM.Thm54.MixedCoordinateCompiler.mixedExpandList_zero_iff
