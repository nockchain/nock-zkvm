/-
  Nock/NockVMROM/Thm54/CoordinateRAPCore.lean

  Theorem 5.4 states both chips' widths in the shape `base + ext · e`
  (`62·e + 13` compute, `61·e + 13` memory) and both gate counts in the shape `base + ext · e`
  (`24·e + 15` compute, `24·e + 16` memory).  `Nock/RedTeam/Batch17Thm54ColumnCensus.lean`
  (`b17_paper_is_coordinate_expansion`) pins that reading: the paper's numbers are already the
  *coordinate-expanded* form of a `(13, 62)` / `(13, 61)` base/extension column split.  This module
  supplies the mechanism for the whole chip rather than for one expression:

  * `ChipTemplate` — the abstract `𝕂`-level shape of one chip: how many base-field and how many
    extension-valued columns each interaction round commits, plus five gate lists (base-field
    transition gates, `𝕂`-valued transition gates, `𝕂`-valued degree-`1` and degree-`3` endpoint
    gates, base-field equality checks) with their paper degree bounds.
  * the exact fingerprint theorems, stated **about the constructed value** (`.w`, `.k`, `.d`,
    `.h`, `.s`, `.ω`, `.H`), not about the `Nock.NockVM` transcription defs.
  * `expandChip_satisfies_iff` / `expandChip_satisfies_iff_language` — `RAP.Satisfies` for the
    constructed monolithic RAP is *exactly* the pointwise vanishing of the base-field gates
    together with the pointwise vanishing of the `𝕂`-valued gates read in the gathered `𝕂`
    environment.

  SCOPE.  This module builds the chip out of a template and proves the paper's counts for *every*
  template of the paper's shape.  It does **not** claim that any particular template's gate list is
  the Nock compute / memory / walk / finite-field-IO semantics; that identification is the
  remaining obligation named in `MonolithicCompRAP.lean`.
-/

import Nock.NockVMROM.Thm54.CoordinateCompiler
import Nock.NockVMROM.Thm54.MixedCoordinateCompiler
import Nock.NockVMROM.Thm54.MultiRoundRAP
import Nock.Framework.NockInstances

namespace Nock.NockVMROM.Thm54
namespace MonolithicRAP

open Module
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension

open scoped Polynomial

noncomputable section

/-! ## 1. Reifying base-field coefficient expressions into the `Def:RAP` polynomial form

`Framework.Reify.exprToMv`
performs that translation for `Nock.Reified.Expr`; `coeffToMv` is its exact analogue for
`CoeffExpr F`, with the same adjacent-row variable discipline `I = [w] × {0,1}`. -/

section Reification

variable {F : Type*} [Field F]

/-- Reify a base-field coefficient expression into the `Def:RAP` symbolic-polynomial form: current-row column `i ↦ Y_{i,0}`, next-row column `i ↦ Y_{i,1}`, challenges and
public values substituted by their already-fixed field constants. -/
def coeffToMv {w : ℕ} (chalVal pubVal : ℕ → F) :
    CoeffExpr F → MvPolynomial (Fin w × ℕ) F
  | .const c => MvPolynomial.C c
  | .var .traceCur i => if h : i < w then MvPolynomial.X (⟨i, h⟩, 0) else 0
  | .var .traceNext i => if h : i < w then MvPolynomial.X (⟨i, h⟩, 1) else 0
  | .var .challenge i => MvPolynomial.C (chalVal i)
  | .var .publicVal i => MvPolynomial.C (pubVal i)
  | .add a b => coeffToMv chalVal pubVal a + coeffToMv chalVal pubVal b
  | .sub a b => coeffToMv chalVal pubVal a - coeffToMv chalVal pubVal b
  | .mul a b => coeffToMv chalVal pubVal a * coeffToMv chalVal pubVal b
  | .neg a => - coeffToMv chalVal pubVal a
  | .pow a n => (coeffToMv chalVal pubVal a) ^ n

/-- **Faithfulness of the reification.**  Evaluating the reified polynomial under the paper's
assignment `Y_{i,j} ↦ P_i(ω^j·x)` reproduces `CoeffExpr.eval` under the induced
environment. -/
theorem eval_coeffToMv {w : ℕ} (P : Fin w → F[X]) (ω x : F) (chalVal pubVal : ℕ → F)
    (g : CoeffExpr F) :
    MvPolynomial.eval (fun q : Fin w × ℕ => (P q.1).eval (ω ^ (q.2 : ℕ) * x))
        (coeffToMv chalVal pubVal g)
      = g.eval (Reify.envOfTrace P ω x chalVal pubVal) := by
  induction g with
  | const c => simp [coeffToMv, CoeffExpr.eval]
  | var kind i =>
      cases kind
      · simp only [coeffToMv, CoeffExpr.eval, Reify.envOfTrace]
        by_cases hi : i < w
        · simp [hi, pow_zero, one_mul]
        · simp [hi]
      · simp only [coeffToMv, CoeffExpr.eval, Reify.envOfTrace]
        by_cases hi : i < w
        · simp [hi, pow_one]
        · simp [hi]
      · simp [coeffToMv, CoeffExpr.eval, Reify.envOfTrace]
      · simp [coeffToMv, CoeffExpr.eval, Reify.envOfTrace]
  | add a b iha ihb => simp only [coeffToMv, CoeffExpr.eval, map_add, iha, ihb]
  | sub a b iha ihb => simp only [coeffToMv, CoeffExpr.eval, map_sub, iha, ihb]
  | mul a b iha ihb => simp only [coeffToMv, CoeffExpr.eval, map_mul, iha, ihb]
  | neg a iha => simp only [coeffToMv, CoeffExpr.eval, map_neg, iha]
  | pow a n iha => simp only [coeffToMv, CoeffExpr.eval, map_pow, iha]

/-- The reification uses only the adjacent-trace-row symbolic variables `I = [w] × {0,1}`, as `Def:RAP`'s `C_vars` field requires. -/
theorem coeffToMv_vars {w : ℕ} (chalVal pubVal : ℕ → F) (g : CoeffExpr F) :
    (coeffToMv (w := w) chalVal pubVal g).vars ⊆ Finset.univ ×ˢ ({0, 1} : Finset ℕ) := by
  induction g with
  | const c => simp only [coeffToMv, MvPolynomial.vars_C]; exact Finset.empty_subset _
  | var kind i =>
      cases kind
      · simp only [coeffToMv]
        by_cases hi : i < w
        · rw [dif_pos hi, MvPolynomial.vars_X, Finset.singleton_subset_iff, Finset.mem_product]
          exact ⟨Finset.mem_univ _, by simp⟩
        · rw [dif_neg hi]; simp
      · simp only [coeffToMv]
        by_cases hi : i < w
        · rw [dif_pos hi, MvPolynomial.vars_X, Finset.singleton_subset_iff, Finset.mem_product]
          exact ⟨Finset.mem_univ _, by simp⟩
        · rw [dif_neg hi]; simp
      · simp only [coeffToMv, MvPolynomial.vars_C]; exact Finset.empty_subset _
      · simp only [coeffToMv, MvPolynomial.vars_C]; exact Finset.empty_subset _
  | add a b iha ihb =>
      exact (MvPolynomial.vars_add_subset _ _).trans (Finset.union_subset iha ihb)
  | sub a b iha ihb =>
      simp only [coeffToMv, sub_eq_add_neg]
      refine (MvPolynomial.vars_add_subset _ _).trans (Finset.union_subset iha ?_)
      rw [MvPolynomial.vars_neg]; exact ihb
  | mul a b iha ihb =>
      exact (MvPolynomial.vars_mul _ _).trans (Finset.union_subset iha ihb)
  | neg a iha => rw [coeffToMv, MvPolynomial.vars_neg]; exact iha
  | pow a n iha =>
      simp only [coeffToMv]
      have hpow : ((coeffToMv (w := w) chalVal pubVal a) ^ n).vars
          ⊆ (coeffToMv (w := w) chalVal pubVal a).vars := by
        induction n with
        | zero => rw [pow_zero, MvPolynomial.vars_one]; exact Finset.empty_subset _
        | succ m ihm =>
            rw [pow_succ]
            exact (MvPolynomial.vars_mul _ _).trans (Finset.union_subset ihm (Finset.Subset.refl _))
      exact hpow.trans iha

/-- **Reification does not increase degree.** -/
theorem coeffToMv_totalDegree_le {w : ℕ} (chalVal pubVal : ℕ → F) (g : CoeffExpr F) :
    (coeffToMv (w := w) chalVal pubVal g).totalDegree ≤ g.degree := by
  induction g with
  | const c => exact (MvPolynomial.totalDegree_C c).le
  | var kind i =>
      cases kind
      · simp only [coeffToMv, CoeffExpr.degree]; split <;> simp
      · simp only [coeffToMv, CoeffExpr.degree]; split <;> simp
      · exact (MvPolynomial.totalDegree_C (chalVal i)).le
      · exact (MvPolynomial.totalDegree_C (pubVal i)).le
  | add a b iha ihb => exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max iha ihb)
  | sub a b iha ihb => exact (MvPolynomial.totalDegree_sub _ _).trans (max_le_max iha ihb)
  | mul a b iha ihb => exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add iha ihb)
  | neg a iha => simpa [coeffToMv, CoeffExpr.degree] using iha
  | pow a n iha => exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left n iha)

end Reification

/-! ## 2. Gathering a `𝕂` environment out of the base-field columns

`stdCoordEnv` inhabits it in the `envK ↦ envF` direction.  For the RAP the
other direction is what is needed: the prover commits base-field columns, and the `𝕂` semantics is
read off them.  `gatherEnv` performs that read, and `isCoordEnv_gather` proves it is a coordinate
environment **unconditionally** — which is what makes the satisfaction equivalence below
hypothesis-free. -/

section Gather

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- Reassemble a `𝕂`-environment from the base-field columns: `𝕂`-column `idx` is the basis
combination of the `e` base columns of its block. -/
def gatherEnv {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ) (envF : Env F) : Env K where
  trace := fun idx => ∑ k : Fin e, envF.trace (col0 .traceCur idx + (k : ℕ)) • b k
  traceNext := fun idx => ∑ k : Fin e, envF.traceNext (col0 .traceNext idx + (k : ℕ)) • b k
  chal := fun idx => ∑ k : Fin e, envF.chal (col0 .challenge idx + (k : ℕ)) • b k
  pub := fun idx => ∑ k : Fin e, envF.pub (col0 .publicVal idx + (k : ℕ)) • b k

/-- Coordinates of a basis combination are its own coefficients. -/
theorem coord_sum_smul {e : ℕ} (b : Basis (Fin e) F K) (c : Fin e → F) (k : Fin e) :
    coord b (∑ i, c i • b i) k = c k := by
  simp only [coord, map_sum, map_smul, Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply]
  simp

/-- **The gathered environment is a coordinate environment.**  Unconditional, so every statement
below that quantifies over `IsCoordEnv` is inhabited at the base-field trace actually committed. -/
theorem isCoordEnv_gather {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ) (envF : Env F) :
    IsCoordEnv b col0 (gatherEnv b col0 envF) envF where
  trace := fun idx k =>
    (coord_sum_smul b (fun j => envF.trace (col0 .traceCur idx + (j : ℕ))) k).symm
  traceNext := fun idx k =>
    (coord_sum_smul b (fun j => envF.traceNext (col0 .traceNext idx + (j : ℕ))) k).symm
  chal := fun idx k =>
    (coord_sum_smul b (fun j => envF.chal (col0 .challenge idx + (j : ℕ))) k).symm
  pub := fun idx k =>
    (coord_sum_smul b (fun j => envF.pub (col0 .publicVal idx + (j : ℕ))) k).symm

end Gather

/-! ## 3. The abstract chip template

One `ChipTemplate` records the paper's per-chip shape *before* coordinate expansion: the
base/extension column split per interaction round, and the five gate families of
Theorem 5.4's per-chip listing. -/

/-- **The `𝕂`-level shape of one Theorem 5.4 chip.**  `baseColsOf r` / `extColsOf r` are the
base-field and extension-valued columns committed in interaction round `r`; the five
gate lists are the paper's transition gates (`base + ext·e` of them), the degree-`1` and degree-`3`
initial/terminal gates, and the base-field equality checks. -/
structure ChipTemplate (F : Type*) [Field F] where
  /-- Number of interaction rounds `k`: `2` compute, `1` memory. -/
  rounds : ℕ
  /-- There is at least one round. -/
  rounds_pos : 0 < rounds
  /-- Base-field columns committed in each round. -/
  baseColsOf : Fin rounds → ℕ
  /-- Extension-valued columns committed in each round; each expands to `e` base columns. -/
  extColsOf : Fin rounds → ℕ
  /-- Base-field transition gates (the paper's constant summand: `15` compute, `16` memory). -/
  baseTransition : List (CoeffExpr F)
  /-- Extension-valued transition gates (the paper's `24`), each expanding to `e` base gates. -/
  extTransition : List Expr
  /-- **Mixed `𝕂`-valued transition gates**, whose leaves may be base-field expressions
  (`MixedCoordinateCompiler`).  They sit in the same paper `·e` bucket as `extTransition` — one
  `𝕂`-valued constraint is billed as `e` `𝔽` gates — and exist because the paper's own gates mix base and extension data inside a single
  `𝕂`-valued equation while `Expr` cannot express that.
  Defaults to `[]`, so a template that does not use them is unchanged. -/
  mixedTransition : List (MixedCoordinateCompiler.MixedExpr F) := []
  /-- Extension-valued degree-`1` initial/terminal gates (the paper's `2`, giving `2e`). -/
  extDeg1 : List Expr
  /-- Extension-valued degree-`3` initial/terminal gates (`1` compute → `e`, `2` memory → `2e`). -/
  extDeg3 : List Expr
  /-- Base-field equality checks (`2` compute, `4` memory). -/
  equalityChecks : List (CoeffExpr F)
  /-- Transition gates are of degree at most `4`. -/
  baseTransition_deg : ∀ g ∈ baseTransition, g.degree ≤ 4
  /-- Extension transition gates are of degree at most `4`. -/
  extTransition_deg : ∀ g ∈ extTransition, g.degree ≤ 4
  /-- Mixed transition gates are of degree at most `4`. -/
  mixedTransition_deg : ∀ g ∈ mixedTransition, g.degree ≤ 4 := by simp
  /-- The `2e` endpoint gates are of degree `1`. -/
  extDeg1_deg : ∀ g ∈ extDeg1, g.degree ≤ 1
  /-- The degree-`3` endpoint gates are of degree `3`. -/
  extDeg3_deg : ∀ g ∈ extDeg3, g.degree ≤ 3
  /-- Equality checks are linear. -/
  equalityChecks_deg : ∀ g ∈ equalityChecks, g.degree ≤ 1

namespace ChipTemplate

variable {F : Type*} [Field F] (T : ChipTemplate F)

/-- Total base-field columns (the paper's constant `13`). -/
def baseCols : ℕ := ∑ r, T.baseColsOf r

/-- Total extension-valued columns (the paper's `62` / `61`). -/
def extCols : ℕ := ∑ r, T.extColsOf r

/-- **The coordinate-expanded width** `base + ext · e`. -/
def width (e : ℕ) : ℕ := T.baseCols + T.extCols * e

/-- Per-round expanded width `w_RAP(r)`. -/
def roundWidth (e : ℕ) (r : Fin T.rounds) : ℕ := T.baseColsOf r + T.extColsOf r * e

/-- **The column layout.**  The base-field columns occupy `0 … baseCols-1`; the `e` coordinates of
`𝕂`-column `idx` occupy the disjoint block `baseCols + e·idx … baseCols + e·idx + (e-1)`. -/
def col0 (e : ℕ) : VarKind → ℕ → ℕ := fun _ idx => T.baseCols + e * idx

/-- `Def:RAP`'s `w = Σ_r w_RAP(r)` for the expanded layout. -/
theorem width_eq_sum (e : ℕ) : T.width e = ∑ r, T.roundWidth e r := by
  unfold width roundWidth baseCols extCols
  rw [Finset.sum_add_distrib, Finset.sum_mul]

/-- Consecutive `𝕂`-columns occupy disjoint blocks of exactly `e` base columns. -/
theorem col0_succ (e : ℕ) (kind : VarKind) (idx : ℕ) :
    T.col0 e kind (idx + 1) = T.col0 e kind idx + e := by
  simp only [col0, Nat.mul_succ]
  omega

/-- **The layout fits inside the expanded width.**  Every coordinate of every one of the
`extCols` extension columns lands strictly below `width e`, disjointly from the base block. -/
theorem col0_lt_width {e : ℕ} {idx k : ℕ} (hidx : idx < T.extCols) (hk : k < e) :
    T.col0 e .traceCur idx + k < T.width e := by
  have h : e * idx + k < e * T.extCols := by
    calc e * idx + k < e * idx + e := by omega
      _ = e * (idx + 1) := by ring
      _ ≤ e * T.extCols := Nat.mul_le_mul_left e hidx
  have hcomm : T.extCols * e = e * T.extCols := Nat.mul_comm _ _
  simp only [col0, width]
  omega

end ChipTemplate

/-! ## 4. Coordinate-expanding the gate lists -/

section Expansion

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

def coordVec {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ) (g : Expr) :
    List (CoeffExpr F) :=
  (List.finRange e).map (coordinateCompile b col0 g)

/-- Coordinate-expand a whole list of `𝕂`-valued gates. -/
def expandList {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ) (l : List Expr) :
    List (CoeffExpr F) :=
  l.flatMap (coordVec b col0)

@[simp] theorem length_coordVec {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    (g : Expr) : (coordVec b col0 g).length = e := by
  simp [coordVec]

/-- **One `𝕂`-valued gate becomes exactly `e` base-field gates**, so a list of `n` of them becomes
`n · e` — the paper's `ext · e` summand. -/
theorem length_expandList {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    (l : List Expr) : (expandList b col0 l).length = l.length * e := by
  induction l with
  | nil => simp [expandList]
  | cons a t ih =>
      simp only [expandList, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
      rw [ih, length_coordVec]
      ring

theorem mem_expandList {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    (l : List Expr) (u : CoeffExpr F) :
    u ∈ expandList b col0 l ↔ ∃ g ∈ l, ∃ k : Fin e, u = coordinateCompile b col0 g k := by
  simp only [expandList, List.mem_flatMap, coordVec, List.mem_map, List.mem_finRange]
  constructor
  · rintro ⟨g, hg, k, -, rfl⟩; exact ⟨g, hg, k, rfl⟩
  · rintro ⟨g, hg, k, rfl⟩; exact ⟨g, hg, k, trivial, rfl⟩

theorem degree_expandList_le {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ)
    (l : List Expr) (d : ℕ) (hl : ∀ g ∈ l, g.degree ≤ d) :
    ∀ u ∈ expandList b col0 l, u.degree ≤ d := by
  intro u hu
  obtain ⟨g, hg, k, rfl⟩ := (mem_expandList b col0 l u).mp hu
  exact (coordinateCompile_degree_le b col0 g k).trans (hl g hg)

end Expansion

/-! ## 5. The constructed monolithic RAP -/

section Chip

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

namespace ChipTemplate

variable (T : ChipTemplate F) {e : ℕ} (b : Basis (Fin e) F K)

/-- **The expanded transition gates**: the base-field transition gates together with the `e`
coordinate gates of each extension transition gate — `base + ext·e` in total. -/
def transitionGates : List (CoeffExpr F) :=
  T.baseTransition ++ expandList b (T.col0 e) T.extTransition
    ++ MixedCoordinateCompiler.mixedExpandList b (T.col0 e) T.mixedTransition

/-- The expanded degree-`1` initial/terminal gates: `2e` of them. -/
def deg1Gates : List (CoeffExpr F) := expandList b (T.col0 e) T.extDeg1

/-- The expanded degree-`3` initial/terminal gates. -/
def deg3Gates : List (CoeffExpr F) := expandList b (T.col0 e) T.extDeg3

/-- The base-field equality checks, which are not coordinate-expanded. -/
def equalityGates : List (CoeffExpr F) := T.equalityChecks

/-- Every constraint of the chip, in the order transition, degree-`1`, degree-`3`, equality. -/
def allGates : List (CoeffExpr F) :=
  T.transitionGates b ++ T.deg1Gates b ++ T.deg3Gates b ++ T.equalityGates

theorem length_transitionGates :
    (T.transitionGates b).length =
      T.baseTransition.length + T.extTransition.length * e
        + T.mixedTransition.length * e := by
  simp [transitionGates, length_expandList, MixedCoordinateCompiler.length_mixedExpandList]
  omega

theorem length_deg1Gates : (T.deg1Gates b).length = T.extDeg1.length * e := by
  simp [deg1Gates, length_expandList]

theorem length_deg3Gates : (T.deg3Gates b).length = T.extDeg3.length * e := by
  simp [deg3Gates, length_expandList]

theorem length_equalityGates : (T.equalityGates).length = T.equalityChecks.length := rfl

theorem length_allGates :
    (T.allGates b).length =
      (T.transitionGates b).length + (T.deg1Gates b).length + (T.deg3Gates b).length
        + (T.equalityGates).length := by
  simp only [allGates, List.length_append]

/-- The degree-`1` endpoint gates really are degree `1` after expansion. -/
theorem deg1Gates_degree : ∀ u ∈ T.deg1Gates b, u.degree ≤ 1 :=
  degree_expandList_le b (T.col0 e) T.extDeg1 1 T.extDeg1_deg

/-- The degree-`3` endpoint gates really are degree `3` after expansion. -/
theorem deg3Gates_degree : ∀ u ∈ T.deg3Gates b, u.degree ≤ 3 :=
  degree_expandList_le b (T.col0 e) T.extDeg3 3 T.extDeg3_deg

/-- **Every constraint of the expanded chip has degree at most `4`**. -/
theorem allGates_degree : ∀ u ∈ T.allGates b, u.degree ≤ 4 := by
  intro u hu
  simp only [allGates, List.mem_append] at hu
  rcases hu with ((hu | hu) | hu) | hu
  · rcases List.mem_append.mp hu with hu | hu
    · rcases List.mem_append.mp hu with hu | hu
      · exact T.baseTransition_deg u hu
      · exact degree_expandList_le b (T.col0 e) T.extTransition 4 T.extTransition_deg u hu
    · exact MixedCoordinateCompiler.degree_mixedExpandList_le b (T.col0 e) T.mixedTransition 4
        T.mixedTransition_deg u hu
  · exact (T.deg1Gates_degree b u hu).trans (by norm_num)
  · exact (T.deg3Gates_degree b u hu).trans (by norm_num)
  · exact (T.equalityChecks_deg u hu).trans (by norm_num)

end ChipTemplate

/-- **THE CONSTRUCTED CHIP.**  A single `Def:RAP` over one base coefficient field
`F` and one row domain `H`: `w = base + ext·e` coordinate-expanded columns split over the
template's `k` interaction rounds, `s` constraints obtained by coordinate-expanding the template's
`𝕂`-valued gates and keeping its base-field gates, maximal degree `4`, and the `Def:RAP` orbit data
`(ω, β)` taken from a `StrictOrbitDomain` so that `ord(ω) = e·2^h`. -/
def expandChip (T : ChipTemplate F) {e h : ℕ} (b : Basis (Fin e) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F e h) (H : Finset F) : RAP F where
  e := e
  k := T.rounds
  wRAP := T.roundWidth e
  w := T.width e
  w_eq := T.width_eq_sum e
  h := h
  d := 4
  s := (T.allGates b).length
  ω := orbit.ω
  β := orbit.βcoset
  I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
  C := fun i => coeffToMv chalVal pubVal ((T.allGates b).get i)
  C_vars := fun i => coeffToMv_vars chalVal pubVal _
  C_deg := fun i =>
    (coeffToMv_totalDegree_le chalVal pubVal _).trans
      (T.allGates_degree b _ (List.get_mem _ _))
  H := H
  β_ne_zero := orbit.βcoset_ne_zero
  I_bound := by
    intro q hq
    have hq2 : q.2 = 0 ∨ q.2 = 1 := by
      have h2 := (Finset.mem_product.mp hq).2
      simpa [Finset.mem_insert, Finset.mem_singleton] using h2
    have hge : 2 ≤ 2 ^ h := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) orbit.h_pos
    rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega

variable (T : ChipTemplate F) {e h : ℕ} (b : Basis (Fin e) F K)
  (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F e h) (H : Finset F)

/-! ### Fingerprints of the constructed value -/

/-- **Width of the constructed RAP** — the paper's `base + ext·e`. -/
theorem expandChip_w :
    (expandChip T b chalVal pubVal orbit H).w = T.baseCols + T.extCols * e := rfl

/-- **Rounds of interaction of the constructed RAP**. -/
theorem expandChip_k : (expandChip T b chalVal pubVal orbit H).k = T.rounds := rfl

/-- The constructed RAP's extension degree. -/
theorem expandChip_e : (expandChip T b chalVal pubVal orbit H).e = e := rfl

/-- The constructed RAP's column height exponent. -/
theorem expandChip_h : (expandChip T b chalVal pubVal orbit H).h = h := rfl

/-- **Maximal constraint degree `4`** — and it is not metadata: `C_deg`
is discharged from `coordinateCompile_degree_le` for every constraint. -/
theorem expandChip_d : (expandChip T b chalVal pubVal orbit H).d = 4 := rfl

/-- Every constraint polynomial of the constructed RAP really has total degree at most `4`. -/
theorem expandChip_constraint_totalDegree_le
    (i : Fin (expandChip T b chalVal pubVal orbit H).s) :
    ((expandChip T b chalVal pubVal orbit H).C i).totalDegree ≤ 4 :=
  (expandChip T b chalVal pubVal orbit H).C_deg i

/-- The constructed RAP's row domain. -/
theorem expandChip_H : (expandChip T b chalVal pubVal orbit H).H = H := rfl

/-- **`Def:RAP`'s order condition holds for the constructed generator.** -/
theorem expandChip_omega_order :
    orderOf (expandChip T b chalVal pubVal orbit H).ω
      = (expandChip T b chalVal pubVal orbit H).e * 2 ^ (expandChip T b chalVal pubVal orbit H).h :=
  orbit.order_ω

/-- **Total constraint count of the constructed RAP**, split into the paper's four families. -/
theorem expandChip_s :
    (expandChip T b chalVal pubVal orbit H).s =
      (T.baseTransition.length + T.extTransition.length * e + T.mixedTransition.length * e)
        + T.extDeg1.length * e + T.extDeg3.length * e + T.equalityChecks.length := by
  show (T.allGates b).length = _
  rw [T.length_allGates b, T.length_transitionGates b, T.length_deg1Gates b,
    T.length_deg3Gates b, T.length_equalityGates]

/-- **Transition-gate count of the constructed RAP** — the paper's `base + 24·e`, measured on the actual expanded gate list. -/
theorem expandChip_transition_gates :
    (T.transitionGates b).length =
      T.baseTransition.length + T.extTransition.length * e + T.mixedTransition.length * e :=
  T.length_transitionGates b

/-- Per-round column widths `w_RAP(r)` of the constructed RAP, and `w = Σ_r w_RAP(r)`. -/
theorem expandChip_wRAP :
    ((expandChip T b chalVal pubVal orbit H).wRAP = T.roundWidth e) ∧
      (expandChip T b chalVal pubVal orbit H).w
        = ∑ r, (expandChip T b chalVal pubVal orbit H).wRAP r :=
  ⟨rfl, (expandChip T b chalVal pubVal orbit H).w_eq⟩

/-! ### Satisfaction of the constructed RAP is exactly the expanded gate language -/

/-- **`Def:RAP` satisfaction of the constructed chip**: a trace of univariate
polynomials satisfies the constructed monolithic RAP iff every expanded base-field gate vanishes at
every row-domain point, reading each column at `x` (current row) and `ω·x` (next row). -/
theorem expandChip_satisfies_iff
    (P : Fin (expandChip T b chalVal pubVal orbit H).w → F[X]) :
    (expandChip T b chalVal pubVal orbit H).Satisfies P
      ↔ ∀ x ∈ H, ∀ g ∈ T.allGates b,
          g.eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0 := by
  have key : ∀ (i : Fin (expandChip T b chalVal pubVal orbit H).s) (x : F),
      ((expandChip T b chalVal pubVal orbit H).compose P i).eval x
        = ((T.allGates b).get i).eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) := by
    intro i x
    rw [Reify.compose_eval]
    exact eval_coeffToMv P orbit.ω x chalVal pubVal _
  constructor
  · intro hsat x hx g hg
    obtain ⟨i, hget⟩ := List.mem_iff_get.mp hg
    have hz := hsat i x hx
    rw [key i x] at hz
    rw [← hget]
    exact hz
  · intro hall i x hx
    rw [key i x]
    exact hall x hx _ (List.get_mem _ _)

/-- **The constructed chip's language, separated into its base-field and `𝕂`-valued halves.**

Satisfaction of the single monolithic RAP is equivalent to: at every row-domain point, the
template's base-field transition gates and equality checks vanish in the committed base-field
environment, **and** the template's `𝕂`-valued transition and endpoint gates vanish in the `𝕂`
environment gathered from the same base-field columns. -/
theorem expandChip_satisfies_iff_language
    (P : Fin (expandChip T b chalVal pubVal orbit H).w → F[X]) :
    (expandChip T b chalVal pubVal orbit H).Satisfies P
      ↔ ∀ x ∈ H,
          (∀ g ∈ T.baseTransition,
              g.eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0)
            ∧ (∀ g ∈ T.equalityChecks,
              g.eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0)
            ∧ (∀ g ∈ T.extTransition ++ T.extDeg1 ++ T.extDeg3,
              g.eval (gatherEnv b (T.col0 e)
                (Reify.envOfTrace P orbit.ω x chalVal pubVal)) = 0)
            ∧ (∀ g ∈ T.mixedTransition,
              g.eval (gatherEnv b (T.col0 e)
                (Reify.envOfTrace P orbit.ω x chalVal pubVal))
                (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0) := by
  rw [expandChip_satisfies_iff T b chalVal pubVal orbit H P]
  refine forall_congr' fun x => ?_
  refine imp_congr_right fun _ => ?_
  let envF := Reify.envOfTrace P orbit.ω x chalVal pubVal
  have hK : ∀ g : Expr,
      (g.eval (gatherEnv b (T.col0 e) envF) = 0
        ↔ ∀ k : Fin e, (coordinateCompile b (T.col0 e) g k).eval envF = 0) := fun g =>
    coordinateCompile_zero_iff b (T.col0 e) (isCoordEnv_gather b (T.col0 e) envF) g
  have hM : ∀ g : MixedCoordinateCompiler.MixedExpr F,
      (g.eval (gatherEnv b (T.col0 e) envF) envF = 0
        ↔ ∀ k : Fin e,
            (MixedCoordinateCompiler.mixedCompile b (T.col0 e) g k).eval envF = 0) := fun g =>
    MixedCoordinateCompiler.mixedCompile_zero_iff b (T.col0 e)
      (isCoordEnv_gather b (T.col0 e) envF) g
  constructor
  · intro hall
    refine ⟨fun g hg => hall g (by simp [ChipTemplate.allGates, ChipTemplate.transitionGates, hg]),
      fun g hg => hall g (by simp [ChipTemplate.allGates, ChipTemplate.equalityGates, hg]), ?_, ?_⟩
    case refine_2 =>
      intro g hg
      refine (hM g).mpr fun k => hall _ ?_
      have hmem : MixedCoordinateCompiler.mixedCompile b (T.col0 e) g k ∈ T.transitionGates b :=
        List.mem_append_right _
          ((MixedCoordinateCompiler.mem_mixedExpandList b _ _ _).mpr ⟨g, hg, k, rfl⟩)
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hmem))
    intro g hg
    refine (hK g).mpr fun k => hall _ ?_
    have hmem : coordinateCompile b (T.col0 e) g k ∈ expandList b (T.col0 e) T.extTransition
        ∨ coordinateCompile b (T.col0 e) g k ∈ expandList b (T.col0 e) T.extDeg1
        ∨ coordinateCompile b (T.col0 e) g k ∈ expandList b (T.col0 e) T.extDeg3 := by
      rcases List.mem_append.mp hg with hg' | hg'
      · rcases List.mem_append.mp hg' with hg'' | hg''
        · exact Or.inl ((mem_expandList b _ _ _).mpr ⟨g, hg'', k, rfl⟩)
        · exact Or.inr (Or.inl ((mem_expandList b _ _ _).mpr ⟨g, hg'', k, rfl⟩))
      · exact Or.inr (Or.inr ((mem_expandList b _ _ _).mpr ⟨g, hg', k, rfl⟩))
    rcases hmem with hm | hm | hm <;>
      simp [ChipTemplate.allGates, ChipTemplate.transitionGates, ChipTemplate.deg1Gates,
        ChipTemplate.deg3Gates, hm]
  · rintro ⟨hbase, heq, hext, hmix⟩ u hu
    simp only [ChipTemplate.allGates, ChipTemplate.transitionGates, ChipTemplate.deg1Gates,
      ChipTemplate.deg3Gates, ChipTemplate.equalityGates, List.mem_append] at hu
    rcases hu with ((hu | hu) | hu) | hu
    · rcases hu with hu | hu
      · rcases hu with hu | hu
        · exact hbase u hu
        · obtain ⟨g, hg, k, rfl⟩ := (mem_expandList b _ _ _).mp hu
          exact (hK g).mp (hext g (by simp [hg])) k
      · obtain ⟨g, hg, k, rfl⟩ :=
          (MixedCoordinateCompiler.mem_mixedExpandList b _ _ _).mp hu
        exact (hM g).mp (hmix g hg) k
    · obtain ⟨g, hg, k, rfl⟩ := (mem_expandList b _ _ _).mp hu
      exact (hK g).mp (hext g (by simp [hg])) k
    · obtain ⟨g, hg, k, rfl⟩ := (mem_expandList b _ _ _).mp hu
      exact (hK g).mp (hext g (by simp [hg])) k
    · exact heq u hu

end Chip

end

end MonolithicRAP
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.eval_coeffToMv
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.coeffToMv_vars
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.coeffToMv_totalDegree_le
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.coord_sum_smul
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.isCoordEnv_gather
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.length_expandList
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.mem_expandList
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.degree_expandList_le
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.ChipTemplate.width_eq_sum
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.ChipTemplate.col0_lt_width
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.ChipTemplate.allGates_degree
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.expandChip_w
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.expandChip_k
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.expandChip_d
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.expandChip_s
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.expandChip_omega_order
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.expandChip_satisfies_iff
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.expandChip_satisfies_iff_language
