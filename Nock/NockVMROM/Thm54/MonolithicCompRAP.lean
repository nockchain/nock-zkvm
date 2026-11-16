/-
  Nock/NockVMROM/Thm54/MonolithicCompRAP.lean

  Theorem 5.4's compute listing is:

  * `62·e + 13` columns;
  * `15 + 24·e` transition gates of degree at most `4`;
  * `2·e` initial/terminal gates of degree `1`, `e` of degree `3`, and two equality checks;
  * `N` total rows;
  * two rounds of interaction.

  Every one of those numbers is the coordinate expansion of an abstract `𝕂`-level count against a
  `(13, 62)` base/extension column split (`Batch17.b17_paper_is_coordinate_expansion`).
  `CompIOShape` names that abstract shape; `RAP_NockCompIO` is the constructed RAP of a template
  having it; and the theorems below read the paper's formulas off the constructed `.w`, `.k`, `.d`,
  `.h`, `.H` and the actual expanded gate lists.

  HONEST SCOPE.  `compTemplate` is a *witness* that the shape class is inhabited, not a claim that
  its gate bodies are the Nock compute / walk / finite-field-IO semantics.  All fingerprint
  theorems are stated for **every** template of the shape (`CompIOShape`), so they will apply
  verbatim to the semantic template once the `(13, 62)` / `15 + 24` census of §5's appendices is
  derived.  That census — identifying which `𝕂`-level gate is which Nock gate — is the residual
  named in the module footer and is NOT claimed here.
-/

import Nock.NockVMROM.Thm54.CoordinateRAPCore
import Nock.NockVMROM.Thm54.MonolithicRowLayout

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

/-! ## 1. The abstract compute shape

The `𝕂`-level counts whose coordinate expansion is Theorem 5.4's compute listing. -/

/-- **The abstract `𝕂`-level shape of `RAP_NockComp-IO`**: `13` base-field and
`62` extension-valued columns over two interaction rounds, `15` base-field and `24`
extension-valued transition gates, `2` degree-`1` and `1` degree-`3` extension endpoint gates, and
`2` base-field equality checks. -/
structure CompIOShape {F : Type*} [Field F] (T : ChipTemplate F) : Prop where
  /-- Two rounds of interaction. -/
  rounds : T.rounds = 2
  /-- The paper's constant column summand. -/
  base_cols : T.baseCols = 13
  /-- The paper's `e`-scaled column summand. -/
  ext_cols : T.extCols = 62
  /-- The paper's constant transition-gate summand. -/
  base_transition : T.baseTransition.length = 15
  /-- The paper's `e`-scaled transition-gate summand.  Both `𝕂`-valued buckets
  count here: the paper bills one `𝕂`-valued constraint as `e` `𝔽` gates (`:651`, `:983`)
  regardless of whether its leaves are all extension columns (`extTransition`) or mix in
  base-field data (`mixedTransition`). -/
  ext_transition : T.extTransition.length + T.mixedTransition.length = 24
  /-- `2·e` degree-`1` initial/terminal gates. -/
  ext_deg1 : T.extDeg1.length = 2
  /-- `e` degree-`3` initial/terminal gates. -/
  ext_deg3 : T.extDeg3.length = 1
  /-- Two equality checks. -/
  equality : T.equalityChecks.length = 2

/-! ## 2. A witness that the shape class is inhabited

These gate bodies carry the paper's *degrees* and *counts*, and reference only in-range columns.
They are deliberately not claimed to be the Nock semantics; see the module header. -/

section Witness

variable {F : Type*} [Field F]

/-- A degree-`4` extension-valued shape gate on `𝕂`-column `j`. -/
def extGate4 (j : ℕ) : Expr :=
  .Mul (.Sub (.Var .traceNext j) (.Var .traceCur j)) (.Pow (.Var .traceCur j) 3)

/-- A degree-`1` extension-valued endpoint shape gate on `𝕂`-column `j`. -/
def extGate1 (j : ℕ) : Expr := .Sub (.Var .traceCur j) (.Var .publicVal j)

/-- A degree-`3` extension-valued endpoint shape gate on `𝕂`-column `j`. -/
def extGate3 (j : ℕ) : Expr := .Pow (.Var .traceCur j) 3

/-- A degree-`4` base-field shape gate on base column `i`. -/
def baseGate4 (i : ℕ) : CoeffExpr F :=
  .mul (.sub (.var .traceNext i) (.var .traceCur i)) (.pow (.var .traceCur i) 3)

/-- A degree-`1` base-field equality-check shape gate on base column `i`. -/
def baseGate1 (i : ℕ) : CoeffExpr F := .sub (.var .traceCur i) (.var .publicVal i)

@[simp] theorem extGate4_degree (j : ℕ) : (extGate4 j).degree = 4 := by
  simp [extGate4, Expr.degree, Expr.powDegree]

@[simp] theorem extGate1_degree (j : ℕ) : (extGate1 j).degree = 1 := by
  simp [extGate1, Expr.degree]

@[simp] theorem extGate3_degree (j : ℕ) : (extGate3 j).degree = 3 := by
  simp [extGate3, Expr.degree, Expr.powDegree]

@[simp] theorem baseGate4_degree (i : ℕ) : (baseGate4 (F := F) i).degree = 4 := by
  simp [baseGate4, CoeffExpr.degree]

@[simp] theorem baseGate1_degree (i : ℕ) : (baseGate1 (F := F) i).degree = 1 := by
  simp [baseGate1, CoeffExpr.degree]

/-- `n` extension shape gates of degree `4`, laid on the first `m` `𝕂`-columns. -/
def extGate4List (n m : ℕ) : List Expr := (List.range n).map (fun j => extGate4 (j % m))

/-- `n` extension endpoint shape gates of degree `1`. -/
def extGate1List (n m : ℕ) : List Expr := (List.range n).map (fun j => extGate1 (j % m))

/-- `n` extension endpoint shape gates of degree `3`. -/
def extGate3List (n m : ℕ) : List Expr := (List.range n).map (fun j => extGate3 (j % m))

/-- `n` base-field shape gates of degree `4`, laid on the first `m` base columns. -/
def baseGate4List (n m : ℕ) : List (CoeffExpr F) := (List.range n).map (fun i => baseGate4 (i % m))

/-- `n` base-field equality checks. -/
def baseGate1List (n m : ℕ) : List (CoeffExpr F) := (List.range n).map (fun i => baseGate1 (i % m))

@[simp] theorem length_extGate4List (n m : ℕ) : (extGate4List n m).length = n := by
  simp [extGate4List]

@[simp] theorem length_extGate1List (n m : ℕ) : (extGate1List n m).length = n := by
  simp [extGate1List]

@[simp] theorem length_extGate3List (n m : ℕ) : (extGate3List n m).length = n := by
  simp [extGate3List]

@[simp] theorem length_baseGate4List (n m : ℕ) :
    (baseGate4List (F := F) n m).length = n := by simp [baseGate4List]

@[simp] theorem length_baseGate1List (n m : ℕ) :
    (baseGate1List (F := F) n m).length = n := by simp [baseGate1List]

theorem extGate4List_degree (n m : ℕ) : ∀ g ∈ extGate4List n m, g.degree ≤ 4 := by
  intro g hg
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hg
  simp

theorem extGate1List_degree (n m : ℕ) : ∀ g ∈ extGate1List n m, g.degree ≤ 1 := by
  intro g hg
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hg
  simp

theorem extGate3List_degree (n m : ℕ) : ∀ g ∈ extGate3List n m, g.degree ≤ 3 := by
  intro g hg
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hg
  simp

theorem baseGate4List_degree (n m : ℕ) :
    ∀ g ∈ baseGate4List (F := F) n m, g.degree ≤ 4 := by
  intro g hg
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hg
  simp

theorem baseGate1List_degree (n m : ℕ) :
    ∀ g ∈ baseGate1List (F := F) n m, g.degree ≤ 1 := by
  intro g hg
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hg
  simp

end Witness

/-! ## 3. The compute template and the constructed `RAP_NockComp-IO` -/

section Compute

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **A compute-shaped chip template.**  Round `0` commits the `13` base-field columns and `61` of
the extension columns; round `1` commits the single post-challenge extension accumulator column,
which is what makes the chip's interaction two rounds. -/
@[reducible] def compTemplate (F : Type*) [Field F] : ChipTemplate F where
  rounds := 2
  rounds_pos := by norm_num
  baseColsOf := ![13, 0]
  extColsOf := ![61, 1]
  baseTransition := baseGate4List 15 13
  extTransition := extGate4List 24 62
  extDeg1 := extGate1List 2 62
  extDeg3 := extGate3List 1 62
  equalityChecks := baseGate1List 2 13
  baseTransition_deg := baseGate4List_degree 15 13
  extTransition_deg := extGate4List_degree 24 62
  extDeg1_deg := extGate1List_degree 2 62
  extDeg3_deg := extGate3List_degree 1 62
  equalityChecks_deg := baseGate1List_degree 2 13

/-- The compute template really has the paper's abstract compute shape. -/
theorem compTemplate_shape : CompIOShape (compTemplate F) where
  rounds := rfl
  base_cols := by
    show ∑ r, ![(13 : ℕ), 0] r = 13
    rw [Fin.sum_univ_two]
    simp
  ext_cols := by
    show ∑ r, ![(61 : ℕ), 1] r = 62
    rw [Fin.sum_univ_two]
    simp
  base_transition := by simp [compTemplate]
  ext_transition := by simp [compTemplate]
  ext_deg1 := by simp [compTemplate]
  ext_deg3 := by simp [compTemplate]
  equality := by simp [compTemplate]

/-- **`RAP_NockComp-IO`.**  The constructed monolithic compute RAP: one base
coefficient field `F`, one row domain `H`, `62·e + 13` coordinate-expanded columns over two
interaction rounds, and the coordinate-expanded gate set. -/
def RAP_NockCompIO {e h : ℕ} (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F e h) (H : Finset F) : RAP F :=
  expandChip (compTemplate F) b chalVal pubVal orbit H

variable {e h : ℕ} (T : ChipTemplate F) (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F)
  (orbit : StrictOrbitDomain F e h) (H : Finset F)

/-! ### Generic fingerprints: every compute-shaped template -/

/-- **`62·e + 13` columns**, read off the constructed `.w`. -/
theorem compShape_width (hT : CompIOShape T) :
    (expandChip T b chalVal pubVal orbit H).w = 62 * e + 13 := by
  rw [expandChip_w, hT.base_cols, hT.ext_cols]
  omega

/-- **`15 + 24·e` transition gates**, counted on the actual expanded gate list. -/
theorem compShape_transition_gates (hT : CompIOShape T) :
    (T.transitionGates b).length = 24 * e + 15 := by
  have hmul : T.extTransition.length * e + T.mixedTransition.length * e = 24 * e := by
    rw [← Nat.add_mul, hT.ext_transition]
  rw [T.length_transitionGates b, hT.base_transition]
  omega

/-- **`2·e` initial/terminal gates of degree `1`.** -/
theorem compShape_deg1_gates (hT : CompIOShape T) :
    (T.deg1Gates b).length = 2 * e ∧ ∀ u ∈ T.deg1Gates b, u.degree ≤ 1 := by
  refine ⟨?_, T.deg1Gates_degree b⟩
  rw [T.length_deg1Gates b, hT.ext_deg1]

/-- **`e` initial/terminal gates of degree `3`.** -/
theorem compShape_deg3_gates (hT : CompIOShape T) :
    (T.deg3Gates b).length = e ∧ ∀ u ∈ T.deg3Gates b, u.degree ≤ 3 := by
  refine ⟨?_, T.deg3Gates_degree b⟩
  rw [T.length_deg3Gates b, hT.ext_deg3, one_mul]

/-- **Two equality checks.** -/
theorem compShape_equality_checks (hT : CompIOShape T) :
    (T.equalityGates).length = 2 := hT.equality

/-- **Two rounds of interaction**, read off the constructed `.k`. -/
theorem compShape_rounds (hT : CompIOShape T) :
    (expandChip T b chalVal pubVal orbit H).k = 2 := hT.rounds

/-! ### The named value's fingerprints -/

/-- `RAP_NockComp-IO` has `62·e + 13` columns. -/
theorem RAP_NockCompIO_width :
    (RAP_NockCompIO b chalVal pubVal orbit H).w = 62 * e + 13 :=
  compShape_width (compTemplate F) b chalVal pubVal orbit H compTemplate_shape

/-- `RAP_NockComp-IO` has `24·e + 15` transition gates. -/
theorem RAP_NockCompIO_transition_gates :
    ((compTemplate F).transitionGates b).length = 24 * e + 15 :=
  compShape_transition_gates (compTemplate F) b compTemplate_shape

/-- `RAP_NockComp-IO` has maximal constraint degree `4`, and every one of its
constraint polynomials really has total degree at most `4`. -/
theorem RAP_NockCompIO_maxDegree :
    (RAP_NockCompIO b chalVal pubVal orbit H).d = 4 ∧
      ∀ i, ((RAP_NockCompIO b chalVal pubVal orbit H).C i).totalDegree ≤ 4 :=
  ⟨rfl, fun i => (RAP_NockCompIO b chalVal pubVal orbit H).C_deg i⟩

/-- `RAP_NockComp-IO`'s initial/terminal budget: `2·e` degree-`1` gates and `e` degree-`3` gates. -/
theorem RAP_NockCompIO_endpoint_gates :
    ((compTemplate F).deg1Gates b).length = 2 * e ∧
      (∀ u ∈ (compTemplate F).deg1Gates b, u.degree ≤ 1) ∧
      ((compTemplate F).deg3Gates b).length = e ∧
      (∀ u ∈ (compTemplate F).deg3Gates b, u.degree ≤ 3) :=
  ⟨(compShape_deg1_gates (compTemplate F) b compTemplate_shape).1,
    (compShape_deg1_gates (compTemplate F) b compTemplate_shape).2,
    (compShape_deg3_gates (compTemplate F) b compTemplate_shape).1,
    (compShape_deg3_gates (compTemplate F) b compTemplate_shape).2⟩

/-- `RAP_NockComp-IO` has two equality checks. -/
theorem RAP_NockCompIO_equality_checks :
    ((compTemplate F).equalityGates).length = 2 := compTemplate_shape.equality

/-- `RAP_NockComp-IO` has two rounds of interaction. -/
theorem RAP_NockCompIO_rounds :
    (RAP_NockCompIO b chalVal pubVal orbit H).k = 2 := rfl

/-- `RAP_NockComp-IO` satisfies `Def:RAP`'s order condition `ord(ω) = e·2^h`. -/
theorem RAP_NockCompIO_omega_order :
    orderOf (RAP_NockCompIO b chalVal pubVal orbit H).ω
      = (RAP_NockCompIO b chalVal pubVal orbit H).e
        * 2 ^ (RAP_NockCompIO b chalVal pubVal orbit H).h :=
  orbit.order_ω

/-- `RAP_NockComp-IO`'s per-round column widths, with `w = Σ_r w_RAP(r)`: the two
rounds are genuine column commitments, not metadata. -/
theorem RAP_NockCompIO_round_widths :
    (compTemplate F).roundWidth e 0 = 61 * e + 13 ∧
      (compTemplate F).roundWidth e 1 = e ∧
      (RAP_NockCompIO b chalVal pubVal orbit H).wRAP = (compTemplate F).roundWidth e ∧
      (RAP_NockCompIO b chalVal pubVal orbit H).w
        = ∑ r, (RAP_NockCompIO b chalVal pubVal orbit H).wRAP r := by
  refine ⟨?_, ?_, rfl, (RAP_NockCompIO b chalVal pubVal orbit H).w_eq⟩
  · show (13 : ℕ) + 61 * e = 61 * e + 13
    omega
  · show (0 : ℕ) + 1 * e = e
    omega

/-- The total constraint count of `RAP_NockComp-IO`, as the paper's four families sum. -/
theorem RAP_NockCompIO_s :
    (RAP_NockCompIO b chalVal pubVal orbit H).s = (24 * e + 15) + 2 * e + e + 2 := by
  show (expandChip (compTemplate F) b chalVal pubVal orbit H).s = _
  rw [expandChip_s]
  simp only [compTemplate, length_baseGate4List, length_extGate4List, length_extGate1List,
    length_extGate3List, length_baseGate1List, List.length_nil, Nat.zero_mul]
  omega

end Compute

/-! ## 4. `N` total rows over the authoritative compute-row carrier -/

section Rows

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable {F₀ K₀ : Type} [Field F₀] [Field K₀] [Algebra F₀ K₀]

/-- **`N` total number of rows.** -/
theorem RAP_NockCompIO_rows {e h : ℕ} (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F e h) (H : Finset F)
    {cfg : ExactConfig F₀ K₀} (exec : ExactExecution cfg)
    (hH : H.card = exec.computeRows.length) :
    (RAP_NockCompIO b chalVal pubVal orbit H).H.card = cfg.compRows := by
  show H.card = cfg.compRows
  rw [hH]
  exact RowLayout.computeRows_count exec

end Rows

/-! ## 5. Satisfaction of `RAP_NockComp-IO` is exactly its expanded gate language -/

section Language

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **`Def:RAP` satisfaction of the constructed compute chip** splits exactly
into its base-field half (read in the committed base-field environment) and its `𝕂`-valued half
(read in the `𝕂` environment gathered from the very same base columns).  Unconditional: no
coordinate-environment hypothesis is carried, because `isCoordEnv_gather` supplies it. -/
theorem RAP_NockCompIO_satisfies_iff_language {e h : ℕ} (b : Basis (Fin e) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F e h) (H : Finset F)
    (P : Fin (RAP_NockCompIO b chalVal pubVal orbit H).w → F[X]) :
    (RAP_NockCompIO b chalVal pubVal orbit H).Satisfies P
      ↔ ∀ x ∈ H,
          (∀ g ∈ (compTemplate F).baseTransition,
              g.eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0)
            ∧ (∀ g ∈ (compTemplate F).equalityChecks,
              g.eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0)
            ∧ (∀ g ∈ (compTemplate F).extTransition ++ (compTemplate F).extDeg1
                  ++ (compTemplate F).extDeg3,
              g.eval (gatherEnv b ((compTemplate F).col0 e)
                (Reify.envOfTrace P orbit.ω x chalVal pubVal)) = 0)
            ∧ (∀ g ∈ (compTemplate F).mixedTransition,
              g.eval (gatherEnv b ((compTemplate F).col0 e)
                (Reify.envOfTrace P orbit.ω x chalVal pubVal))
                (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0) :=
  expandChip_satisfies_iff_language (compTemplate F) b chalVal pubVal orbit H P

end Language

end

end MonolithicRAP
end Nock.NockVMROM.Thm54

/-
  RESIDUAL (named precisely, not claimed).  What is proved above is that the coordinate-expansion
  construction turns *any* `CompIOShape` template into a single-field, single-domain `Def:RAP` with
  exactly Theorem 5.4's compute fingerprint, and that its `RAP.Satisfies` is exactly the pointwise
  vanishing of the template's base-field gates plus the pointwise vanishing of its `𝕂`-valued gates
  in the gathered `𝕂` environment.

  NOT proved here: that the Nock compute table / walk / finite-field-IO semantics can be presented
  as a `CompIOShape` template — i.e. the `(13, 62)` column census and the `15 + 24` transition-gate
  census of Appendix `Appendix:CompConstraints`.  Our mechanized abstract compute AIR is `94`
  columns / `527` constraints (`Nock/NockVMROM/Thm54/ExactCost.lean`), a genuinely different and
  larger abstract column set; `Nock/RedTeam/Batch17Thm54ColumnCensus.lean` records that no
  relabelling reconciles the two and that re-deriving the split is the honest mechanism.  Supplying
  that semantic template is the remaining obligation.
-/

#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.compTemplate_shape
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.compShape_width
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.compShape_transition_gates
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.compShape_deg1_gates
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.compShape_deg3_gates
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.compShape_equality_checks
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.compShape_rounds
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockCompIO_width
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockCompIO_transition_gates
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockCompIO_maxDegree
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockCompIO_endpoint_gates
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockCompIO_equality_checks
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockCompIO_rounds
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockCompIO_omega_order
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockCompIO_round_widths
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockCompIO_s
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockCompIO_rows
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockCompIO_satisfies_iff_language
