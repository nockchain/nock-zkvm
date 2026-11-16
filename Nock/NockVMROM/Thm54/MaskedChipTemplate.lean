/-
  Nock/NockVMROM/Thm54/MaskedChipTemplate.lean

  **Recovering the paper's segmented (Initial / Transition / Terminal) semantics from
  `Def:RAP`'s flat satisfaction, by masking — with the paper's degree labels kept intact.**

  `Def:RAP` satisfaction is flat:
  `∀ i ∈ [s], ∀ x ∈ H, (C_i ∘ P)(x) = 0` — every constraint at every row of one domain, and
  `Def:Canonical_RAP` allows exactly one such tuple per table.  The paper
  nevertheless lists its gates in *Initial / Transition / Terminal* categories and
  prices the endpoint ones at degree `1` and degree `3`.  The only
  mechanism `Def:RAP` offers for a row-dependent gate is the preprocessing/selector block, so an endpoint gate must be multiplied by a verifier-fixed Lagrange row
  indicator.  That is what this module formalizes.

  Masking costs degree, unavoidably: `Reified.Expr.degree` (`Nock/AIR.lean:120`) counts trace
  variables only, so a mask *column* has degree `1` and a degree-`1` endpoint gate becomes
  degree `2`, a degree-`3` one degree `4`.  The consequence for `ChipTemplate`
  (`Nock/NockVMROM/Thm54/CoordinateRAPCore.lean:224`), which carries `extDeg1_deg : ≤ 1` and
  `extDeg3_deg : ≤ 3` as *fields*, is that a template holding **masked** gates cannot be built.

  The resolution implemented here: the paper's `≤ 1` / `≤ 3` labels describe the endpoint gates
  *before* they are placed in a flat-satisfaction RAP.  So

  * `MaskedChipTemplate.toChipTemplate` performs the masking when the chip is *built*, moving the
    masked endpoint gates into the degree-`4` transition bucket, where flat satisfaction is the
    correct semantics.  The realized degrees `≤ 2` / `≤ 4` are **theorems**
    (`masked_deg1_degree_le`, `masked_deg3_degree_le`), not fields;
  * This is what recovers the paper's segmented semantics from
    `Def:RAP`'s flat one, and it is the reason masking is faithful rather than a weakening;
  * `expandChip_toChipTemplate_satisfies_iff_segmented` chains it through
    `expandChip_satisfies_iff_language`, so satisfaction of the single constructed
    `Framework.RAP F` is *equivalent* to (row gates at every row) ∧ (unmasked endpoint gates at
    their target rows).

  PINNING.  `zero_mask_admits_false_endpoint` exhibits exactly that.  The equivalence therefore takes the
  indicator property `IsRowIndicator` as an explicit hypothesis, and the indicator property is
  **derived**, not assumed, from `Framework.FixedPreprocessingRAP.BindsPreprocessing`
  (`Nock/Framework/FixedPreprocessingRAP.lean:81`) by
  `isRowIndicator_gathered_first_of_binds` / `..._last_of_binds`.

  SCOPE.  Everything here is `∀` field / `∀` template / `∀` row-node family; no fixture, no
  `CompIOShape`, no claim that any particular gate list is the Nock semantics.  The Lagrange
  selectors and their node evaluations are reused from `Nock/Framework/EndpointMasks.lean`
  (`firstRowMask`, `lastRowMask`, `firstRowMask_eval`, `lastRowMask_eval`), including its
  singleton handling; `endpointNode_singleton` records that at `n = 1` both endpoints are the
  unique row.

  LIMITS, stated so they are not mistaken for closed.

  * The segmented equivalence holds for the row domain `H := rowNodeSet nodes` — the actual row
    nodes of the (arbitrary) node family.  It says nothing about a `Def:RAP` whose `H` is unrelated
    to the interpolation nodes of its own trace.
  * It masks **endpoint** gates only, and it does so because a degree-`1`/`3` gate has room for the
    extra degree.  It does **not** solve the complementary problem of *excluding* the last row from
    a degree-`4` transition gate: `(1 - isLast) · g` on an already-degree-`4` gate reaches degree
    `5`, which `OptimizedComputeAllRowsObstruction.literal_fixed_last_mask_exceeds_degree_four`
    (`:178`, census at `:164`) proves is outside `Def:RAP`'s `d = 4`.  That
    obstruction is untouched here.
  * The template fixes the mask exponent at `1`.  `isRowIndicator_pow` and `masked_pow_degree_le`
    cover an arbitrary positive exponent, so the tree's `.Pow fixedIsFirst 2` form is inside the
    theory, but `toChipTemplate` does not emit it.

The deployed client (`stark/verifier.hoon:639-655`) restricts a constraint to a row range by
**dividing by that category's zerofier** — `1/(X−1)` boundary, `1/(X^N−1)` row,
`(X−g^{-1})/(X^N−1)` transition, `1/(X−g^{-1})` terminal — and has **no row-mask columns at all**.
Zerofier division is free in trace degree; masking costs one degree per factor.

So the theorems here are correct and are the right tool for a *single shared domain* reading of
`Def:RAP`, which is what `expandChip` builds. They are **not** the route to the
paper's chip. The per-kind domain mechanism the client matches already exists in this tree as
`CanonicalRAP.SegmentedRAPParams.domain : ConstraintKind → Finset K`, with
`SegmentedRAP.segmented_is_kinded` proving the four-per-kind conjunction equals per-constraint-domain
satisfaction.

`masked_gate_vanishes_iff` and `zero_mask_admits_false_endpoint` stand on their own: the first is the
segmentation-recovery statement, the second shows an unpinned mask carries no endpoint information.
-/

import Nock.NockVMROM.Thm54.CoordinateRAPCore
import Nock.Framework.EndpointMasks

namespace Nock.NockVMROM.Thm54
namespace MaskedChip

open Module
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension

open scoped Polynomial

noncomputable section

/-! ## 1. Exact row indicators, and the masking equivalence -/

/-- **`mfac` is an exact row indicator for node `t`.**  It evaluates to `1` at the row node `t`
and to `0` at every other row node of the family.  The environment is `𝕂`-valued while the nodes
live in the base field `F`, so this covers both an uncompiled base-field mask (`K = F`) and a
coordinate-gathered `𝕂`-valued mask column. -/
def IsRowIndicator {F K : Type*} [Field F] [Field K] {n : ℕ}
    (nodes : Fin n → F) (env : F → Env K) (mfac : Expr) (t : Fin n) : Prop :=
  ∀ i : Fin n, mfac.eval (env (nodes i)) = if i = t then 1 else 0

/-- **THE MASKING EQUIVALENCE.**

This is what recovers the paper's Initial / Terminal segmentation from flat satisfaction. -/
theorem masked_gate_vanishes_iff {F K : Type*} [Field F] [Field K] {n : ℕ}
    (nodes : Fin n → F) (env : F → Env K) (mfac g : Expr) (t : Fin n)
    (hm : IsRowIndicator nodes env mfac t) :
    (∀ x ∈ rowNodeSet nodes, (Expr.Mul mfac g).eval (env x) = 0)
      ↔ g.eval (env (nodes t)) = 0 := by
  classical
  constructor
  · intro hall
    have hx : nodes t ∈ rowNodeSet nodes := by simp [rowNodeSet]
    have h := hall _ hx
    rw [Expr.eval, hm t] at h
    simpa using h
  · intro h0 x hx
    have hex : ∃ i : Fin n, nodes i = x := by simpa [rowNodeSet] using hx
    obtain ⟨i, rfl⟩ := hex
    rw [Expr.eval, hm i]
    by_cases hit : i = t
    · subst hit; simpa using h0
    · simp [hit]

/-- A positive power of an exact row indicator is again an exact row indicator.  This is what
covers the tree's `.Pow fixedIsFirst 2` masking form
(`OptimizedComputeFinalTypedLowering.lean:179`). -/
theorem isRowIndicator_pow {F K : Type*} [Field F] [Field K] {n : ℕ}
    (nodes : Fin n → F) (env : F → Env K) (mfac : Expr) (t : Fin n)
    (hm : IsRowIndicator nodes env mfac t) {m : ℕ} (hmpos : 0 < m) :
    IsRowIndicator nodes env (Expr.Pow mfac m) t := by
  intro i
  rw [Expr.eval, hm i]
  by_cases hit : i = t
  · simp [hit]
  · simp [hit, zero_pow (show m ≠ 0 by omega)]

/-- If the mask factor happens to evaluate
to `0` at every row node — which a prover-chosen mask column may — then *every* masked gate
vanishes at every row of the domain while the unmasked gate is the constant `1`, false at the
endpoint.  So flat satisfaction of an unpinned masked gate carries no endpoint information. -/
theorem zero_mask_admits_false_endpoint {F K : Type*} [Field F] [Field K] {n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (env : F → Env K) (mfac : Expr)
    (hzero : ∀ i : Fin n, mfac.eval (env (nodes i)) = 0) :
    (∀ x ∈ rowNodeSet nodes, (Expr.Mul mfac (Expr.Const 1)).eval (env x) = 0)
      ∧ ¬ (Expr.Const 1).eval (env (nodes ⟨0, hn⟩)) = 0 := by
  classical
  refine ⟨?_, ?_⟩
  · intro x hx
    have hex : ∃ i : Fin n, nodes i = x := by simpa [rowNodeSet] using hx
    obtain ⟨i, rfl⟩ := hex
    rw [Expr.eval, hzero i, zero_mul]
  · show ¬ ((1 : ℤ) : K) = 0
    simp

/-! ## 2. Pinning a base-field mask column -/

/-- `hpin` is exactly what `FixedPreprocessingRAP.BindsPreprocessing` supplies. -/
theorem isRowIndicator_base_first {F : Type*} [Field F] {n w : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (hnodes : Function.Injective nodes)
    (P : Fin w → F[X]) (ω : F) (chalVal pubVal : ℕ → F)
    (idx : ℕ) (hidx : idx < w) (hpin : P ⟨idx, hidx⟩ = firstRowMask nodes) :
    IsRowIndicator nodes (fun x => Reify.envOfTrace P ω x chalVal pubVal)
      (Expr.Var .traceCur idx) ⟨0, hn⟩ := by
  intro i
  have hcell : (Reify.envOfTrace P ω (nodes i) chalVal pubVal).trace idx
      = (firstRowMask nodes).eval (nodes i) := by
    show (if h : idx < w then (P ⟨idx, h⟩).eval (nodes i) else 0) = _
    rw [dif_pos hidx, hpin]
  show (Reify.envOfTrace P ω (nodes i) chalVal pubVal).trace idx = _
  rw [hcell, firstRowMask_eval nodes hnodes i]
  by_cases h0 : (i : ℕ) = 0
  · have : i = ⟨0, hn⟩ := Fin.ext (by simpa using h0)
    simp [this]
  · have : i ≠ ⟨0, hn⟩ := fun h => h0 (by rw [h])
    simp [h0, this]

theorem isRowIndicator_base_last {F : Type*} [Field F] {n w : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (hnodes : Function.Injective nodes)
    (P : Fin w → F[X]) (ω : F) (chalVal pubVal : ℕ → F)
    (idx : ℕ) (hidx : idx < w) (hpin : P ⟨idx, hidx⟩ = lastRowMask hn nodes) :
    IsRowIndicator nodes (fun x => Reify.envOfTrace P ω x chalVal pubVal)
      (Expr.Var .traceCur idx) ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ := by
  intro i
  have hcell : (Reify.envOfTrace P ω (nodes i) chalVal pubVal).trace idx
      = (lastRowMask hn nodes).eval (nodes i) := by
    show (if h : idx < w then (P ⟨idx, h⟩).eval (nodes i) else 0) = _
    rw [dif_pos hidx, hpin]
  show (Reify.envOfTrace P ω (nodes i) chalVal pubVal).trace idx = _
  rw [hcell, lastRowMask_eval hn nodes hnodes i]

/-! ## 3. Pinning a `𝕂`-valued mask column through the coordinate expansion

A `ChipTemplate`'s endpoint gates are `𝕂`-valued and are read in `gatherEnv`, so their mask is a
`𝕂`-column occupying an `e`-wide base-field block.  Pinning it to the *scalar* indicator means
pinning coordinate `k` to `b.repr 1 k • mask`, so that the gathered value is `mask(x) • (1 : 𝕂)`.
-/

section Gathered

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- **The `e` base-field preprocessing polynomials that pin one `𝕂`-valued mask column** to the
scalar polynomial `mask`: coordinate `k` carries `b.repr 1 k • mask`. -/
def maskBlock {e : ℕ} (b : Basis (Fin e) F K) (mask : F[X]) (k : Fin e) : F[X] :=
  Polynomial.C (b.repr (1 : K) k) * mask

theorem gathered_trace_of_maskBlock {e w : ℕ} (b : Basis (Fin e) F K)
    (col0 : VarKind → ℕ → ℕ) (idx : ℕ) (P : Fin w → F[X]) (ω x : F) (chalVal pubVal : ℕ → F)
    (mask : F[X]) (hlt : ∀ k : Fin e, col0 .traceCur idx + (k : ℕ) < w)
    (hpin : ∀ k : Fin e, P ⟨col0 .traceCur idx + (k : ℕ), hlt k⟩ = maskBlock b mask k) :
    (gatherEnv b col0 (Reify.envOfTrace P ω x chalVal pubVal)).trace idx
      = (mask.eval x) • (1 : K) := by
  have hcell : ∀ k : Fin e,
      (Reify.envOfTrace P ω x chalVal pubVal).trace (col0 .traceCur idx + (k : ℕ))
        = b.repr (1 : K) k * mask.eval x := by
    intro k
    show (if h : col0 .traceCur idx + (k : ℕ) < w then (P ⟨_, h⟩).eval x else 0) = _
    rw [dif_pos (hlt k), hpin k]
    simp [maskBlock]
  show ∑ k : Fin e,
      (Reify.envOfTrace P ω x chalVal pubVal).trace (col0 .traceCur idx + (k : ℕ)) • b k = _
  calc ∑ k : Fin e,
        (Reify.envOfTrace P ω x chalVal pubVal).trace (col0 .traceCur idx + (k : ℕ)) • b k
      = ∑ k : Fin e, (mask.eval x) • ((b.repr (1 : K) k) • b k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hcell k, smul_smul, mul_comm]
    _ = (mask.eval x) • ∑ k : Fin e, (b.repr (1 : K) k) • b k := Finset.smul_sum.symm
    _ = (mask.eval x) • (1 : K) := by rw [b.sum_repr]

theorem isRowIndicator_gathered_first {e w n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ) (idx : ℕ)
    (P : Fin w → F[X]) (ω : F) (chalVal pubVal : ℕ → F)
    (hlt : ∀ k : Fin e, col0 .traceCur idx + (k : ℕ) < w)
    (hpin : ∀ k : Fin e,
      P ⟨col0 .traceCur idx + (k : ℕ), hlt k⟩ = maskBlock b (firstRowMask nodes) k) :
    IsRowIndicator nodes
      (fun x => gatherEnv b col0 (Reify.envOfTrace P ω x chalVal pubVal))
      (Expr.Var .traceCur idx) ⟨0, hn⟩ := by
  intro i
  show (gatherEnv b col0 (Reify.envOfTrace P ω (nodes i) chalVal pubVal)).trace idx = _
  rw [gathered_trace_of_maskBlock b col0 idx P ω (nodes i) chalVal pubVal
        (firstRowMask nodes) hlt hpin, firstRowMask_eval nodes hnodes i]
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = ⟨0, hn⟩ := Fin.ext (by simpa using h0)
    simp [hi]
  · have hi : i ≠ ⟨0, hn⟩ := fun h => h0 (by rw [h])
    simp [h0, hi]

theorem isRowIndicator_gathered_last {e w n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ) (idx : ℕ)
    (P : Fin w → F[X]) (ω : F) (chalVal pubVal : ℕ → F)
    (hlt : ∀ k : Fin e, col0 .traceCur idx + (k : ℕ) < w)
    (hpin : ∀ k : Fin e,
      P ⟨col0 .traceCur idx + (k : ℕ), hlt k⟩ = maskBlock b (lastRowMask hn nodes) k) :
    IsRowIndicator nodes
      (fun x => gatherEnv b col0 (Reify.envOfTrace P ω x chalVal pubVal))
      (Expr.Var .traceCur idx) ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ := by
  intro i
  show (gatherEnv b col0 (Reify.envOfTrace P ω (nodes i) chalVal pubVal)).trace idx = _
  rw [gathered_trace_of_maskBlock b col0 idx P ω (nodes i) chalVal pubVal
        (lastRowMask hn nodes) hlt hpin, lastRowMask_eval hn nodes hnodes i]
  by_cases hl : i = (⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ : Fin n)
  · simp [hl]
  · simp [hl]

/-- **The pinning is derived, not assumed.**  `BindsPreprocessing` on the `e` designated columns of the mask block forces the
mask-block equations that `gathered_trace_of_maskBlock` consumes. -/
theorem maskBlock_of_binds (R : FixedPreprocessingRAP F) (P : Fin R.rap.w → F[X])
    (hbind : R.BindsPreprocessing P) {e : ℕ} (b : Basis (Fin e) F K) (mask : F[X])
    (jdx : Fin e → Fin R.fixedCount)
    (hfix : ∀ k : Fin e, R.preprocessing (jdx k) = maskBlock b mask k)
    (col0 : VarKind → ℕ → ℕ) (idx : ℕ)
    (hlt : ∀ k : Fin e, col0 .traceCur idx + (k : ℕ) < R.rap.w)
    (hcol : ∀ k : Fin e,
      ((R.preprocessingColumn (jdx k) : Fin R.rap.w) : ℕ) = col0 .traceCur idx + (k : ℕ)) :
    ∀ k : Fin e, P ⟨col0 .traceCur idx + (k : ℕ), hlt k⟩ = maskBlock b mask k := by
  intro k
  have hP : P (R.preprocessingColumn (jdx k)) = maskBlock b mask k := by
    rw [hbind (jdx k), hfix k]
  have hidx : (⟨col0 .traceCur idx + (k : ℕ), hlt k⟩ : Fin R.rap.w)
      = R.preprocessingColumn (jdx k) := Fin.ext (by simp [hcol k])
  rw [hidx, hP]

/-- `BindsPreprocessing` on a first-row mask block yields the exact row indicator for row `0`. -/
theorem isRowIndicator_gathered_first_of_binds
    (R : FixedPreprocessingRAP F) (P : Fin R.rap.w → F[X])
    (hbind : R.BindsPreprocessing P) {e n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin e) F K) (jdx : Fin e → Fin R.fixedCount)
    (hfix : ∀ k : Fin e, R.preprocessing (jdx k) = maskBlock b (firstRowMask nodes) k)
    (col0 : VarKind → ℕ → ℕ) (idx : ℕ)
    (hlt : ∀ k : Fin e, col0 .traceCur idx + (k : ℕ) < R.rap.w)
    (hcol : ∀ k : Fin e,
      ((R.preprocessingColumn (jdx k) : Fin R.rap.w) : ℕ) = col0 .traceCur idx + (k : ℕ))
    (ω : F) (chalVal pubVal : ℕ → F) :
    IsRowIndicator nodes
      (fun x => gatherEnv b col0 (Reify.envOfTrace P ω x chalVal pubVal))
      (Expr.Var .traceCur idx) ⟨0, hn⟩ :=
  isRowIndicator_gathered_first hn nodes hnodes b col0 idx P ω chalVal pubVal hlt
    (maskBlock_of_binds R P hbind b (firstRowMask nodes) jdx hfix col0 idx hlt hcol)

/-- `BindsPreprocessing` on a last-row mask block yields the exact row indicator for row `n-1`. -/
theorem isRowIndicator_gathered_last_of_binds
    (R : FixedPreprocessingRAP F) (P : Fin R.rap.w → F[X])
    (hbind : R.BindsPreprocessing P) {e n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin e) F K) (jdx : Fin e → Fin R.fixedCount)
    (hfix : ∀ k : Fin e, R.preprocessing (jdx k) = maskBlock b (lastRowMask hn nodes) k)
    (col0 : VarKind → ℕ → ℕ) (idx : ℕ)
    (hlt : ∀ k : Fin e, col0 .traceCur idx + (k : ℕ) < R.rap.w)
    (hcol : ∀ k : Fin e,
      ((R.preprocessingColumn (jdx k) : Fin R.rap.w) : ℕ) = col0 .traceCur idx + (k : ℕ))
    (ω : F) (chalVal pubVal : ℕ → F) :
    IsRowIndicator nodes
      (fun x => gatherEnv b col0 (Reify.envOfTrace P ω x chalVal pubVal))
      (Expr.Var .traceCur idx) ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ :=
  isRowIndicator_gathered_last hn nodes hnodes b col0 idx P ω chalVal pubVal hlt
    (maskBlock_of_binds R P hbind b (lastRowMask hn nodes) jdx hfix col0 idx hlt hcol)

/-- **A zero mask block is exactly the vacuity witness.**  Pinning nothing and letting the prover
put `0` in the `e` coordinates of the mask column makes the gathered indicator identically `0`. -/
theorem gathered_zero_mask {e w : ℕ} (b : Basis (Fin e) F K)
    (col0 : VarKind → ℕ → ℕ) (idx : ℕ) (P : Fin w → F[X]) (ω x : F) (chalVal pubVal : ℕ → F)
    (hlt : ∀ k : Fin e, col0 .traceCur idx + (k : ℕ) < w)
    (hpin : ∀ k : Fin e, P ⟨col0 .traceCur idx + (k : ℕ), hlt k⟩ = 0) :
    (Expr.Var .traceCur idx).eval
        (gatherEnv b col0 (Reify.envOfTrace P ω x chalVal pubVal)) = 0 := by
  have h := gathered_trace_of_maskBlock b col0 idx P ω x chalVal pubVal (0 : F[X]) hlt
    (by intro k; rw [hpin k]; simp [maskBlock])
  show (gatherEnv b col0 (Reify.envOfTrace P ω x chalVal pubVal)).trace idx = 0
  rw [h]
  simp

end Gathered

/-! ## 4. Realized degrees of the masked gates -/

/-- Masking multiplies by a trace column, so it costs exactly `1` degree
(`Reified.Expr.degree`, `Nock/AIR.lean:120`: `.Mul` adds, `.Var.traceCur` is `1`). -/
theorem degree_mask_mul (idx : ℕ) (g : Expr) :
    (Expr.Mul (Expr.Var .traceCur idx) g).degree = 1 + g.degree := rfl

/-- Masking with the `m`-th power of a mask column costs exactly `m` degrees (`.Pow` multiplies). -/
theorem degree_maskPow_mul (idx m : ℕ) (g : Expr) :
    (Expr.Mul (Expr.Pow (Expr.Var .traceCur idx) m) g).degree = m + g.degree := by
  simp [Expr.degree, Expr.powDegree, Nat.one_mul]

/-- **Realized degree of a masked degree-`1` endpoint gate is `≤ 2`** — the paper's `1` plus the mask column, still inside `Def:RAP`'s `d = 4`. -/
theorem masked_deg1_degree_le (idx : ℕ) {g : Expr} (hg : g.degree ≤ 1) :
    (Expr.Mul (Expr.Var .traceCur idx) g).degree ≤ 2 := by
  rw [degree_mask_mul]; omega

/-- **Realized degree of a masked degree-`3` endpoint gate is `≤ 4`** — the paper's `3` plus the mask column, exactly meeting `Def:RAP`'s `d = 4`. -/
theorem masked_deg3_degree_le (idx : ℕ) {g : Expr} (hg : g.degree ≤ 3) :
    (Expr.Mul (Expr.Var .traceCur idx) g).degree ≤ 4 := by
  rw [degree_mask_mul]; omega

/-- General mask-power budget.  Instantiated at `m = 2`, `g.degree ≤ 2` this is the tree's
`finalMaskedWalkAccInit` shape (`OptimizedComputeFinalTypedLowering.lean:179`), whose measured
degree is `4`. -/
theorem masked_pow_degree_le (idx m d : ℕ) {g : Expr} (h : m + g.degree ≤ d) :
    (Expr.Mul (Expr.Pow (Expr.Var .traceCur idx) m) g).degree ≤ d := by
  rw [degree_maskPow_mul]; omega

/-- The tree's squared-mask form on a degree-`2` gate lands at exactly `4`. -/
theorem masked_pow_two_deg_two (idx : ℕ) {g : Expr} (hg : g.degree = 2) :
    (Expr.Mul (Expr.Pow (Expr.Var .traceCur idx) 2) g).degree = 4 := by
  rw [degree_maskPow_mul, hg]

/-! ## 5. The masked chip template -/

inductive EndpointRow
  | first
  | last
deriving DecidableEq, Repr

/-- One **unmasked** endpoint gate of Theorem 5.4's per-chip listing,
together with the endpoint it is masked to when the chip is built. -/
structure EndpointGate where
  /-- The unmasked gate body, subject to the paper's `≤ 1` / `≤ 3` degree label. -/
  gate : Expr
  row : EndpointRow
deriving Repr

/-- **The `𝕂`-level shape of one Theorem 5.4 chip with endpoint gates kept unmasked.**

Masking happens in `toChipTemplate`. -/
structure MaskedChipTemplate (F : Type*) [Field F] where
  /-- Number of interaction rounds `k`. -/
  rounds : ℕ
  /-- There is at least one round. -/
  rounds_pos : 0 < rounds
  /-- Base-field columns committed in each round. -/
  baseColsOf : Fin rounds → ℕ
  /-- Extension-valued columns committed in each round. -/
  extColsOf : Fin rounds → ℕ
  /-- Base-field transition gates. -/
  baseTransition : List (CoeffExpr F)
  /-- Extension-valued transition gates. -/
  extTransition : List Expr
  /-- Extension-valued degree-`1` endpoint gates, **unmasked**. -/
  extDeg1 : List EndpointGate
  /-- Extension-valued degree-`3` endpoint gates, **unmasked**. -/
  extDeg3 : List EndpointGate
  /-- Base-field equality checks. -/
  equalityChecks : List (CoeffExpr F)
  maskCol : EndpointRow → ℕ
  /-- Transition gates are of degree at most `4`. -/
  baseTransition_deg : ∀ g ∈ baseTransition, g.degree ≤ 4
  /-- Extension transition gates are of degree at most `4`. -/
  extTransition_deg : ∀ g ∈ extTransition, g.degree ≤ 4
  /-- **The paper's degree-`1` label, met exactly**. -/
  extDeg1_deg : ∀ g ∈ extDeg1, g.gate.degree ≤ 1
  /-- **The paper's degree-`3` label, met exactly**. -/
  extDeg3_deg : ∀ g ∈ extDeg3, g.gate.degree ≤ 3
  /-- Equality checks are linear. -/
  equalityChecks_deg : ∀ g ∈ equalityChecks, g.degree ≤ 1

namespace MaskedChipTemplate

variable {F : Type*} [Field F] (T : MaskedChipTemplate F)

/-- The row indicator expression of an endpoint: a `𝕂`-valued trace column, as the paper's
selector block requires (a coefficient cannot depend on the row). -/
def maskOf (r : EndpointRow) : Expr := Expr.Var .traceCur (T.maskCol r)

/-- Mask a bucket of unmasked endpoint gates. -/
def maskedGates (l : List EndpointGate) : List Expr :=
  l.map fun eg => Expr.Mul (T.maskOf eg.row) eg.gate

@[simp] theorem length_maskedGates (l : List EndpointGate) :
    (T.maskedGates l).length = l.length := by simp [maskedGates]

theorem mem_maskedGates {l : List EndpointGate} {eg : EndpointGate} (h : eg ∈ l) :
    Expr.Mul (T.maskOf eg.row) eg.gate ∈ T.maskedGates l :=
  List.mem_map_of_mem h

/-- **Realized degrees of the masked buckets: `≤ 2` and `≤ 4`.**  Derived from the template's
paper-exact `≤ 1` / `≤ 3` fields, not assumed — this is the `2 / 4` deviation `Thm54.lean:451-452`
records, now with the paper's `1 / 3` still available on the same object. -/
theorem maskedGates_deg1_degree : ∀ u ∈ T.maskedGates T.extDeg1, u.degree ≤ 2 := by
  intro u hu
  obtain ⟨eg, heg, rfl⟩ := List.mem_map.mp hu
  exact masked_deg1_degree_le _ (T.extDeg1_deg eg heg)

theorem maskedGates_deg3_degree : ∀ u ∈ T.maskedGates T.extDeg3, u.degree ≤ 4 := by
  intro u hu
  obtain ⟨eg, heg, rfl⟩ := List.mem_map.mp hu
  exact masked_deg3_degree_le _ (T.extDeg3_deg eg heg)

/-- **Placement.**  Masked endpoint gates go into the degree-`4` transition bucket, which is where
`Def:RAP`'s flat satisfaction is the intended semantics; the endpoint buckets of the
constructed `ChipTemplate` are therefore empty.  Every degree obligation of the target structure is
discharged by a theorem. -/
def toChipTemplate : ChipTemplate F where
  rounds := T.rounds
  rounds_pos := T.rounds_pos
  baseColsOf := T.baseColsOf
  extColsOf := T.extColsOf
  baseTransition := T.baseTransition
  extTransition := T.extTransition ++ T.maskedGates T.extDeg1 ++ T.maskedGates T.extDeg3
  extDeg1 := []
  extDeg3 := []
  mixedTransition := []
  equalityChecks := T.equalityChecks
  baseTransition_deg := T.baseTransition_deg
  extTransition_deg := by
    intro u hu
    rcases List.mem_append.mp hu with hu' | hu'
    · rcases List.mem_append.mp hu' with hu'' | hu''
      · exact T.extTransition_deg u hu''
      · exact (T.maskedGates_deg1_degree u hu'').trans (by norm_num)
    · exact T.maskedGates_deg3_degree u hu'
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := T.equalityChecks_deg

@[simp] theorem toChipTemplate_mixedTransition : T.toChipTemplate.mixedTransition = [] := rfl
@[simp] theorem toChipTemplate_rounds : T.toChipTemplate.rounds = T.rounds := rfl
@[simp] theorem toChipTemplate_baseColsOf : T.toChipTemplate.baseColsOf = T.baseColsOf := rfl
@[simp] theorem toChipTemplate_extColsOf : T.toChipTemplate.extColsOf = T.extColsOf := rfl
@[simp] theorem toChipTemplate_extDeg1 : T.toChipTemplate.extDeg1 = [] := rfl
@[simp] theorem toChipTemplate_extDeg3 : T.toChipTemplate.extDeg3 = [] := rfl

/-- Total base-field columns. -/
def baseCols : ℕ := ∑ r, T.baseColsOf r

/-- Total extension-valued columns. -/
def extCols : ℕ := ∑ r, T.extColsOf r

/-- **Masking adds gates, not columns.**  The constructed chip's width is the masked template's own
`base + ext·e`; the row-indicator columns are ordinary preprocessing columns of
the paper's first round and are already counted in `extColsOf`. -/
theorem toChipTemplate_width (e : ℕ) :
    T.toChipTemplate.width e = T.baseCols + T.extCols * e := rfl

/-- **Gate accounting of the placement.**  The transition bucket absorbs both endpoint buckets. -/
theorem toChipTemplate_transition_length :
    T.toChipTemplate.extTransition.length
      = T.extTransition.length + T.extDeg1.length + T.extDeg3.length := by
  simp [toChipTemplate, List.length_append, Nat.add_assoc]

end MaskedChipTemplate

/-! ### Non-vacuity: the structure is inhabited with the paper's endpoint counts -/

/-- **A witness that `MaskedChipTemplate` is inhabited with *non-empty* endpoint buckets at the
paper's degrees.**  The endpoint counts are the compute chip's: two degree-`1` gates split first/last, and one degree-`3` gate.  The gate bodies are placeholders — this is an inhabitation witness for the
structure, not a semantic claim, exactly as `MonolithicCompRAP`'s `compTemplate` footer says of
itself. -/
def endpointWitness (F : Type*) [Field F] : MaskedChipTemplate F where
  rounds := 1
  rounds_pos := Nat.one_pos
  baseColsOf := fun _ => 0
  extColsOf := fun _ => 4
  baseTransition := []
  extTransition := []
  extDeg1 := [⟨Expr.Var .traceCur 0, .first⟩, ⟨Expr.Var .traceCur 1, .last⟩]
  extDeg3 := [⟨Expr.Pow (Expr.Var .traceCur 2) 3, .first⟩]
  equalityChecks := []
  maskCol := fun r => match r with | .first => 3 | .last => 4
  baseTransition_deg := by simp
  extTransition_deg := by simp
  extDeg1_deg := by decide
  extDeg3_deg := by decide
  equalityChecks_deg := by simp

/-- The witness's endpoint buckets have the compute chip's counts `2` and `1` with the paper's degrees `1` and `3`, and their **masked** realizations have
degrees `2, 2` and `4` — the deviation, now derived rather than assumed. -/
theorem endpointWitness_degrees (F : Type*) [Field F] :
    ((endpointWitness F).extDeg1.length = 2 ∧ (endpointWitness F).extDeg3.length = 1)
      ∧ ((endpointWitness F).maskedGates (endpointWitness F).extDeg1).map Expr.degree = [2, 2]
      ∧ ((endpointWitness F).maskedGates (endpointWitness F).extDeg3).map Expr.degree = [4] := by
  refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩ <;>
    simp [MaskedChipTemplate.maskedGates, MaskedChipTemplate.maskOf, endpointWitness,
      Expr.degree, Expr.powDegree, Nat.one_mul]

/-! ## 6. Recovering the segmented semantics from flat `Def:RAP` satisfaction -/

/-- The row node an endpoint bucket is masked to. -/
def endpointNode {n : ℕ} (hn : 0 < n) : EndpointRow → Fin n
  | .first => ⟨0, hn⟩
  | .last => ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩

/-- **The singleton case.**  At `n = 1` the two endpoints are the same row, matching
`Framework.singleton_endpoint_masks`: both Lagrange selectors evaluate to `1` there, so the
segmented reading collapses to "the endpoint gates hold at the unique row". -/
theorem endpointNode_singleton (hn : 0 < 1) (r r' : EndpointRow) :
    endpointNode (n := 1) hn r = endpointNode (n := 1) hn r' := by
  cases r <;> cases r' <;> rfl

section Recover

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **THE CENTREPIECE.**  Flat `Def:RAP` satisfaction of the single constructed
chip is *equivalent* to the paper's segmented reading:

* the base-field transition gates, the equality checks, and the `𝕂`-valued transition gates
  vanish at **every** row of the domain, and
* each **unmasked** degree-`1` and degree-`3` endpoint gate vanishes at **exactly** the row its
  bucket is masked to.

The row domain is the actual row-node family `rowNodeSet nodes`; the mask columns are supplied as
exact row indicators (`hmask`), which `isRowIndicator_gathered_first_of_binds` /
`..._last_of_binds` derive from `FixedPreprocessingRAP.BindsPreprocessing`.  Without that
hypothesis the `→` direction of the endpoint conjuncts fails —
`zero_mask_admits_false_endpoint`. -/
theorem expandChip_toChipTemplate_satisfies_iff_segmented
    (T : MaskedChipTemplate F) {e h n : ℕ} (b : Basis (Fin e) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F e h)
    (hn : 0 < n) (nodes : Fin n → F)
    (P : Fin (expandChip T.toChipTemplate b chalVal pubVal orbit (rowNodeSet nodes)).w → F[X])
    (hmask : ∀ r : EndpointRow,
      IsRowIndicator nodes
        (fun x => gatherEnv b (T.toChipTemplate.col0 e)
          (Reify.envOfTrace P orbit.ω x chalVal pubVal))
        (T.maskOf r) (endpointNode hn r)) :
    (expandChip T.toChipTemplate b chalVal pubVal orbit (rowNodeSet nodes)).Satisfies P
      ↔ (∀ x ∈ rowNodeSet nodes,
            (∀ g ∈ T.baseTransition,
                g.eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0)
              ∧ (∀ g ∈ T.equalityChecks,
                g.eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0)
              ∧ (∀ g ∈ T.extTransition,
                g.eval (gatherEnv b (T.toChipTemplate.col0 e)
                  (Reify.envOfTrace P orbit.ω x chalVal pubVal)) = 0))
        ∧ (∀ eg ∈ T.extDeg1,
            eg.gate.eval (gatherEnv b (T.toChipTemplate.col0 e)
              (Reify.envOfTrace P orbit.ω (nodes (endpointNode hn eg.row)) chalVal pubVal)) = 0)
        ∧ (∀ eg ∈ T.extDeg3,
            eg.gate.eval (gatherEnv b (T.toChipTemplate.col0 e)
              (Reify.envOfTrace P orbit.ω (nodes (endpointNode hn eg.row)) chalVal pubVal)) = 0)
        := by
  classical
  rw [expandChip_satisfies_iff_language T.toChipTemplate b chalVal pubVal orbit
    (rowNodeSet nodes) P]
  set envK : F → Env K := fun x =>
    gatherEnv b (T.toChipTemplate.col0 e) (Reify.envOfTrace P orbit.ω x chalVal pubVal) with hEnvK
  have hlist : T.toChipTemplate.extTransition ++ T.toChipTemplate.extDeg1
        ++ T.toChipTemplate.extDeg3
      = T.extTransition ++ T.maskedGates T.extDeg1 ++ T.maskedGates T.extDeg3 := by
    simp [MaskedChipTemplate.toChipTemplate]
  constructor
  · intro hsat
    refine ⟨fun x hx => ⟨(hsat x hx).1, (hsat x hx).2.1, fun g hg => ?_⟩, ?_, ?_⟩
    · refine (hsat x hx).2.2.1 g ?_
      rw [hlist]
      exact List.mem_append_left _ (List.mem_append_left _ hg)
    · intro eg heg
      refine (masked_gate_vanishes_iff nodes envK (T.maskOf eg.row) eg.gate
        (endpointNode hn eg.row) (hmask eg.row)).mp ?_
      intro x hx
      refine (hsat x hx).2.2.1 _ ?_
      rw [hlist]
      exact List.mem_append_left _
        (List.mem_append_right _ (T.mem_maskedGates heg))
    · intro eg heg
      refine (masked_gate_vanishes_iff nodes envK (T.maskOf eg.row) eg.gate
        (endpointNode hn eg.row) (hmask eg.row)).mp ?_
      intro x hx
      refine (hsat x hx).2.2.1 _ ?_
      rw [hlist]
      exact List.mem_append_right _ (T.mem_maskedGates heg)
  · rintro ⟨hrow, h1, h3⟩ x hx
    refine ⟨(hrow x hx).1, (hrow x hx).2.1, fun g hg => ?_, by simp⟩
    rw [hlist] at hg
    rcases List.mem_append.mp hg with hg' | hg'
    · rcases List.mem_append.mp hg' with hg'' | hg''
      · exact (hrow x hx).2.2 g hg''
      · obtain ⟨eg, heg, rfl⟩ := List.mem_map.mp hg''
        exact (masked_gate_vanishes_iff nodes envK (T.maskOf eg.row) eg.gate
          (endpointNode hn eg.row) (hmask eg.row)).mpr (h1 eg heg) x hx
    · obtain ⟨eg, heg, rfl⟩ := List.mem_map.mp hg'
      exact (masked_gate_vanishes_iff nodes envK (T.maskOf eg.row) eg.gate
        (endpointNode hn eg.row) (hmask eg.row)).mpr (h3 eg heg) x hx

/-- **The constructed chip still has `Def:RAP` degree `4`** with the masked
endpoint gates in it, and its declared width is the template's `base + ext·e`. -/
theorem expandChip_toChipTemplate_fingerprint
    (T : MaskedChipTemplate F) {e h : ℕ} (b : Basis (Fin e) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F e h) (H : Finset F) :
    (expandChip T.toChipTemplate b chalVal pubVal orbit H).d = 4
      ∧ (expandChip T.toChipTemplate b chalVal pubVal orbit H).w
          = T.toChipTemplate.baseCols + T.toChipTemplate.extCols * e
      ∧ ∀ i, ((expandChip T.toChipTemplate b chalVal pubVal orbit H).C i).totalDegree ≤ 4 :=
  ⟨rfl, rfl, fun i => (expandChip T.toChipTemplate b chalVal pubVal orbit H).C_deg i⟩

end Recover

end

end MaskedChip
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.MaskedChip.masked_gate_vanishes_iff
#print axioms Nock.NockVMROM.Thm54.MaskedChip.isRowIndicator_pow
#print axioms Nock.NockVMROM.Thm54.MaskedChip.zero_mask_admits_false_endpoint
#print axioms Nock.NockVMROM.Thm54.MaskedChip.isRowIndicator_base_first
#print axioms Nock.NockVMROM.Thm54.MaskedChip.isRowIndicator_base_last
#print axioms Nock.NockVMROM.Thm54.MaskedChip.gathered_trace_of_maskBlock
#print axioms Nock.NockVMROM.Thm54.MaskedChip.isRowIndicator_gathered_first
#print axioms Nock.NockVMROM.Thm54.MaskedChip.isRowIndicator_gathered_last
#print axioms Nock.NockVMROM.Thm54.MaskedChip.maskBlock_of_binds
#print axioms Nock.NockVMROM.Thm54.MaskedChip.isRowIndicator_gathered_first_of_binds
#print axioms Nock.NockVMROM.Thm54.MaskedChip.isRowIndicator_gathered_last_of_binds
#print axioms Nock.NockVMROM.Thm54.MaskedChip.gathered_zero_mask
#print axioms Nock.NockVMROM.Thm54.MaskedChip.masked_deg1_degree_le
#print axioms Nock.NockVMROM.Thm54.MaskedChip.masked_deg3_degree_le
#print axioms Nock.NockVMROM.Thm54.MaskedChip.masked_pow_degree_le
#print axioms Nock.NockVMROM.Thm54.MaskedChip.masked_pow_two_deg_two
#print axioms Nock.NockVMROM.Thm54.MaskedChip.MaskedChipTemplate.maskedGates_deg1_degree
#print axioms Nock.NockVMROM.Thm54.MaskedChip.MaskedChipTemplate.maskedGates_deg3_degree
#print axioms Nock.NockVMROM.Thm54.MaskedChip.MaskedChipTemplate.toChipTemplate_transition_length
#print axioms Nock.NockVMROM.Thm54.MaskedChip.endpointWitness_degrees
#print axioms Nock.NockVMROM.Thm54.MaskedChip.endpointNode_singleton
#print axioms Nock.NockVMROM.Thm54.MaskedChip.expandChip_toChipTemplate_satisfies_iff_segmented
#print axioms Nock.NockVMROM.Thm54.MaskedChip.expandChip_toChipTemplate_fingerprint
