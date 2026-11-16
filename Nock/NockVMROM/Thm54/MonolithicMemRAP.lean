/-
  Nock/NockVMROM/Thm54/MonolithicMemRAP.lean

  Theorem 5.4's memory listing is:

  * `61·e + 13` columns in `𝔽`;
  * `24·e + 16` transition gates of degree at most `4`;
  * `2·e` initial/terminal gates of degree `1`, `2·e` of degree `3`, and four equality checks;
  * `M + 2L` total rows;
  * one round of interaction.

  The construction, the honest-scope caveat and the named residual are exactly as in
  `MonolithicCompRAP.lean`; only the abstract shape differs.
-/

import Nock.NockVMROM.Thm54.MonolithicCompRAP
import Nock.NockVMROM.Thm54.MemoryMplus2L

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

/-! ## 1. The abstract memory shape -/

/-- **The abstract `𝕂`-level shape of `RAP_NockMem-IO`**: `13` base-field and
`61` extension-valued columns over a single interaction round, `16` base-field and `24`
extension-valued transition gates, `2` degree-`1` and `2` degree-`3` extension endpoint gates, and
`4` base-field equality checks. -/
structure MemIOShape {F : Type*} [Field F] (T : ChipTemplate F) : Prop where
  /-- One round of interaction. -/
  rounds : T.rounds = 1
  /-- The paper's constant column summand. -/
  base_cols : T.baseCols = 13
  /-- The paper's `e`-scaled column summand. -/
  ext_cols : T.extCols = 61
  /-- The paper's constant transition-gate summand. -/
  base_transition : T.baseTransition.length = 16
  /-- The paper's `e`-scaled transition-gate summand.  Both `𝕂`-valued buckets
  count here: the paper bills one `𝕂`-valued constraint as `e` `𝔽` gates (`:670`, `:989`)
  regardless of whether its leaves are all extension columns (`extTransition`) or mix in
  base-field data (`mixedTransition`). -/
  ext_transition : T.extTransition.length + T.mixedTransition.length = 24
  /-- `2·e` degree-`1` initial/terminal gates. -/
  ext_deg1 : T.extDeg1.length = 2
  /-- `2·e` degree-`3` initial/terminal gates. -/
  ext_deg3 : T.extDeg3.length = 2
  /-- Four equality checks. -/
  equality : T.equalityChecks.length = 4

/-! ## 2. The memory template and the constructed `RAP_NockMem-IO` -/

section Memory

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **A memory-shaped chip template.**  The single interaction round commits all `13` base-field
and all `61` extension-valued columns. -/
@[reducible] def memTemplate (F : Type*) [Field F] : ChipTemplate F where
  rounds := 1
  rounds_pos := by norm_num
  baseColsOf := ![13]
  extColsOf := ![61]
  baseTransition := baseGate4List 16 13
  extTransition := extGate4List 24 61
  extDeg1 := extGate1List 2 61
  extDeg3 := extGate3List 2 61
  equalityChecks := baseGate1List 4 13
  baseTransition_deg := baseGate4List_degree 16 13
  extTransition_deg := extGate4List_degree 24 61
  extDeg1_deg := extGate1List_degree 2 61
  extDeg3_deg := extGate3List_degree 2 61
  equalityChecks_deg := baseGate1List_degree 4 13

/-- The memory template really has the paper's abstract memory shape. -/
theorem memTemplate_shape : MemIOShape (memTemplate F) where
  rounds := rfl
  base_cols := by
    show ∑ r, ![(13 : ℕ)] r = 13
    rw [Fin.sum_univ_one]
    simp
  ext_cols := by
    show ∑ r, ![(61 : ℕ)] r = 61
    rw [Fin.sum_univ_one]
    simp
  base_transition := by simp
  ext_transition := by simp
  ext_deg1 := by simp
  ext_deg3 := by simp
  equality := by simp

/-- **`RAP_NockMem-IO`.**  The constructed monolithic memory RAP: one base
coefficient field `F`, one row domain `H`, `61·e + 13` coordinate-expanded columns committed in a
single interaction round, and the coordinate-expanded gate set. -/
def RAP_NockMemIO {e h : ℕ} (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F e h) (H : Finset F) : RAP F :=
  expandChip (memTemplate F) b chalVal pubVal orbit H

variable {e h : ℕ} (T : ChipTemplate F) (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F)
  (orbit : StrictOrbitDomain F e h) (H : Finset F)

/-! ### Generic fingerprints: every memory-shaped template -/

/-- **`61·e + 13` columns**, read off the constructed `.w`. -/
theorem memShape_width (hT : MemIOShape T) :
    (expandChip T b chalVal pubVal orbit H).w = 61 * e + 13 := by
  rw [expandChip_w, hT.base_cols, hT.ext_cols]
  omega

/-- **`24·e + 16` transition gates**, counted on the actual expanded gate list. -/
theorem memShape_transition_gates (hT : MemIOShape T) :
    (T.transitionGates b).length = 24 * e + 16 := by
  have hmul : T.extTransition.length * e + T.mixedTransition.length * e = 24 * e := by
    rw [← Nat.add_mul, hT.ext_transition]
  rw [T.length_transitionGates b, hT.base_transition]
  omega

/-- **`2·e` initial/terminal gates of degree `1`.** -/
theorem memShape_deg1_gates (hT : MemIOShape T) :
    (T.deg1Gates b).length = 2 * e ∧ ∀ u ∈ T.deg1Gates b, u.degree ≤ 1 := by
  refine ⟨?_, T.deg1Gates_degree b⟩
  rw [T.length_deg1Gates b, hT.ext_deg1]

/-- **`2·e` initial/terminal gates of degree `3`.** -/
theorem memShape_deg3_gates (hT : MemIOShape T) :
    (T.deg3Gates b).length = 2 * e ∧ ∀ u ∈ T.deg3Gates b, u.degree ≤ 3 := by
  refine ⟨?_, T.deg3Gates_degree b⟩
  rw [T.length_deg3Gates b, hT.ext_deg3]

/-- **Four equality checks.** -/
theorem memShape_equality_checks (hT : MemIOShape T) :
    (T.equalityGates).length = 4 := hT.equality

/-- **One round of interaction**, read off the constructed `.k`. -/
theorem memShape_rounds (hT : MemIOShape T) :
    (expandChip T b chalVal pubVal orbit H).k = 1 := hT.rounds

/-! ### The named value's fingerprints -/

/-- `RAP_NockMem-IO` has `61·e + 13` columns. -/
theorem RAP_NockMemIO_width :
    (RAP_NockMemIO b chalVal pubVal orbit H).w = 61 * e + 13 :=
  memShape_width (memTemplate F) b chalVal pubVal orbit H memTemplate_shape

/-- `RAP_NockMem-IO` has `24·e + 16` transition gates. -/
theorem RAP_NockMemIO_transition_gates :
    ((memTemplate F).transitionGates b).length = 24 * e + 16 :=
  memShape_transition_gates (memTemplate F) b memTemplate_shape

/-- `RAP_NockMem-IO` has maximal constraint degree `4`, and every one of its
constraint polynomials really has total degree at most `4`. -/
theorem RAP_NockMemIO_maxDegree :
    (RAP_NockMemIO b chalVal pubVal orbit H).d = 4 ∧
      ∀ i, ((RAP_NockMemIO b chalVal pubVal orbit H).C i).totalDegree ≤ 4 :=
  ⟨rfl, fun i => (RAP_NockMemIO b chalVal pubVal orbit H).C_deg i⟩

/-- `RAP_NockMem-IO`'s initial/terminal budget: `2·e` degree-`1` and `2·e` degree-`3` gates. -/
theorem RAP_NockMemIO_endpoint_gates :
    ((memTemplate F).deg1Gates b).length = 2 * e ∧
      (∀ u ∈ (memTemplate F).deg1Gates b, u.degree ≤ 1) ∧
      ((memTemplate F).deg3Gates b).length = 2 * e ∧
      (∀ u ∈ (memTemplate F).deg3Gates b, u.degree ≤ 3) :=
  ⟨(memShape_deg1_gates (memTemplate F) b memTemplate_shape).1,
    (memShape_deg1_gates (memTemplate F) b memTemplate_shape).2,
    (memShape_deg3_gates (memTemplate F) b memTemplate_shape).1,
    (memShape_deg3_gates (memTemplate F) b memTemplate_shape).2⟩

/-- `RAP_NockMem-IO` has four equality checks. -/
theorem RAP_NockMemIO_equality_checks :
    ((memTemplate F).equalityGates).length = 4 := memTemplate_shape.equality

/-- `RAP_NockMem-IO` has one round of interaction. -/
theorem RAP_NockMemIO_rounds :
    (RAP_NockMemIO b chalVal pubVal orbit H).k = 1 := rfl

/-- `RAP_NockMem-IO` satisfies `Def:RAP`'s order condition `ord(ω) = e·2^h`. -/
theorem RAP_NockMemIO_omega_order :
    orderOf (RAP_NockMemIO b chalVal pubVal orbit H).ω
      = (RAP_NockMemIO b chalVal pubVal orbit H).e
        * 2 ^ (RAP_NockMemIO b chalVal pubVal orbit H).h :=
  orbit.order_ω

/-- The single memory round commits every column, and `w = Σ_r w_RAP(r)`. -/
theorem RAP_NockMemIO_round_widths :
    (memTemplate F).roundWidth e 0 = 61 * e + 13 ∧
      (RAP_NockMemIO b chalVal pubVal orbit H).wRAP = (memTemplate F).roundWidth e ∧
      (RAP_NockMemIO b chalVal pubVal orbit H).w
        = ∑ r, (RAP_NockMemIO b chalVal pubVal orbit H).wRAP r := by
  refine ⟨?_, rfl, (RAP_NockMemIO b chalVal pubVal orbit H).w_eq⟩
  show (13 : ℕ) + 61 * e = 61 * e + 13
  omega

/-- The total constraint count of `RAP_NockMem-IO`, as the paper's four families sum. -/
theorem RAP_NockMemIO_s :
    (RAP_NockMemIO b chalVal pubVal orbit H).s = (24 * e + 16) + 2 * e + 2 * e + 4 := by
  show (expandChip (memTemplate F) b chalVal pubVal orbit H).s = _
  rw [expandChip_s]
  simp only [memTemplate, length_baseGate4List, length_extGate4List, length_extGate1List,
    length_extGate3List, length_baseGate1List, List.length_nil, Nat.zero_mul]
  omega

end Memory

/-! ## 3. `M + 2L` total rows over the authoritative memory-row carrier -/

section Rows

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable {F₀ K₀ : Type} [Field F₀] [Field K₀] [Algebra F₀ K₀]

/-- **`M + 2L` total number of rows.**  Under honest `ver` this is the
paper's `M + 2L` with `L = derivedResponseIO.length`. -/
theorem RAP_NockMemIO_rows {e h : ℕ} (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F e h) (H : Finset F)
    {cfg : ExactConfig F₀ K₀} {exec : ExactExecution cfg}
    (hbalance : RowLayout.RecordCountBalanced exec)
    (hH : H.card = exec.memoryRows.length) :
    (RAP_NockMemIO b chalVal pubVal orbit H).H.card
      = RowLayout.memoryM exec + 2 * RowLayout.memoryL exec := by
  show H.card = _
  rw [hH]
  exact RowLayout.memory_rows_eq_M_add_two_mul_L_of_count_balance hbalance

end Rows

/-! ## 4. Satisfaction of `RAP_NockMem-IO` is exactly its expanded gate language -/

section Language

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **`Def:RAP` satisfaction of the constructed memory chip** splits exactly into
its base-field half and its `𝕂`-valued half, unconditionally. -/
theorem RAP_NockMemIO_satisfies_iff_language {e h : ℕ} (b : Basis (Fin e) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F e h) (H : Finset F)
    (P : Fin (RAP_NockMemIO b chalVal pubVal orbit H).w → F[X]) :
    (RAP_NockMemIO b chalVal pubVal orbit H).Satisfies P
      ↔ ∀ x ∈ H,
          (∀ g ∈ (memTemplate F).baseTransition,
              g.eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0)
            ∧ (∀ g ∈ (memTemplate F).equalityChecks,
              g.eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0)
            ∧ (∀ g ∈ (memTemplate F).extTransition ++ (memTemplate F).extDeg1
                  ++ (memTemplate F).extDeg3,
              g.eval (gatherEnv b ((memTemplate F).col0 e)
                (Reify.envOfTrace P orbit.ω x chalVal pubVal)) = 0)
            ∧ (∀ g ∈ (memTemplate F).mixedTransition,
              g.eval (gatherEnv b ((memTemplate F).col0 e)
                (Reify.envOfTrace P orbit.ω x chalVal pubVal))
                (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0) :=
  expandChip_satisfies_iff_language (memTemplate F) b chalVal pubVal orbit H P

end Language

end

end MonolithicRAP
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.memTemplate_shape
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.memShape_width
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.memShape_transition_gates
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.memShape_deg1_gates
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.memShape_deg3_gates
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.memShape_equality_checks
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.memShape_rounds
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockMemIO_width
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockMemIO_transition_gates
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockMemIO_maxDegree
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockMemIO_endpoint_gates
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockMemIO_equality_checks
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockMemIO_rounds
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockMemIO_omega_order
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockMemIO_round_widths
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockMemIO_s
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockMemIO_rows
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.RAP_NockMemIO_satisfies_iff_language
