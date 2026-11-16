/-
  Nock/NockVMROM/Thm54/CoordinateRAPTail.lean

  `expandChipTail`: `CoordinateRAPCore.expandChip` with `tail` extra base-field columns appended
  **after** the template's base + extension blocks, all committed in the first round.

  The deployed memory layout
  pins every extension coordinate at `6 + 3·role` (`OptimizedMemoryGateBasis.memoryCol0`), so the
  new column is appended at physical index `baseCols + extCols·e` (= `180`) instead of being
  inserted in the base block, which would shift every extension role.  The gate language is the
  template's own (`ChipTemplate.allGates`); the extra column is read by gates through ordinary
  `CoeffExpr` / `MixedExpr.Lift` leaves.  At `tail = 0` this is `expandChip` up to the `wRAP`
  presentation; every other chip keeps `expandChip`.
-/

import Nock.NockVMROM.Thm54.CoordinateRAPCore

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

section Tail

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- Per-round width with `tail` extra base columns committed in the first round. -/
def ChipTemplate.roundWidthTail (T : ChipTemplate F) (e tail : ℕ) (r : Fin T.rounds) : ℕ :=
  T.roundWidth e r + if (r : ℕ) = 0 then tail else 0

theorem ChipTemplate.width_tail_eq_sum (T : ChipTemplate F) (e tail : ℕ) :
    T.width e + tail = ∑ r, T.roundWidthTail e tail r := by
  unfold ChipTemplate.roundWidthTail
  rw [Finset.sum_add_distrib, ← T.width_eq_sum e]
  congr 1
  have h0 : (⟨0, T.rounds_pos⟩ : Fin T.rounds) ∈ (Finset.univ : Finset (Fin T.rounds)) :=
    Finset.mem_univ _
  rw [Finset.sum_eq_single (⟨0, T.rounds_pos⟩ : Fin T.rounds)]
  · simp
  · intro r _ hr
    have : (r : ℕ) ≠ 0 := fun h => hr (Fin.ext h)
    simp [this]
  · intro h; exact absurd h0 h

/-- **The constructed chip with `tail` appended first-round base columns.** -/
def expandChipTail (T : ChipTemplate F) {e h : ℕ} (b : Basis (Fin e) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F e h) (H : Finset F) (tail : ℕ) :
    RAP F where
  e := e
  k := T.rounds
  wRAP := T.roundWidthTail e tail
  w := T.width e + tail
  w_eq := T.width_tail_eq_sum e tail
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
  (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F e h) (H : Finset F) (tail : ℕ)

theorem expandChipTail_w :
    (expandChipTail T b chalVal pubVal orbit H tail).w =
      T.baseCols + T.extCols * e + tail := rfl

theorem expandChipTail_k : (expandChipTail T b chalVal pubVal orbit H tail).k = T.rounds := rfl

theorem expandChipTail_d : (expandChipTail T b chalVal pubVal orbit H tail).d = 4 := rfl

theorem expandChipTail_H : (expandChipTail T b chalVal pubVal orbit H tail).H = H := rfl

theorem expandChipTail_s :
    (expandChipTail T b chalVal pubVal orbit H tail).s =
      (T.baseTransition.length + T.extTransition.length * e + T.mixedTransition.length * e)
        + T.extDeg1.length * e + T.extDeg3.length * e + T.equalityChecks.length := by
  show (T.allGates b).length = _
  rw [T.length_allGates b, T.length_transitionGates b, T.length_deg1Gates b,
    T.length_deg3Gates b, T.length_equalityGates]

/-- Satisfaction of the tailed chip is exactly the expanded gate language (as `expandChip`). -/
theorem expandChipTail_satisfies_iff
    (P : Fin (expandChipTail T b chalVal pubVal orbit H tail).w → F[X]) :
    (expandChipTail T b chalVal pubVal orbit H tail).Satisfies P
      ↔ ∀ x ∈ H, ∀ g ∈ T.allGates b,
          g.eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0 := by
  have key : ∀ (i : Fin (expandChipTail T b chalVal pubVal orbit H tail).s) (x : F),
      ((expandChipTail T b chalVal pubVal orbit H tail).compose P i).eval x
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

/-- The tailed chip's language, split into base-field and `𝕂`-valued halves
(`expandChip_satisfies_iff_language`, verbatim). -/
theorem expandChipTail_satisfies_iff_language
    (P : Fin (expandChipTail T b chalVal pubVal orbit H tail).w → F[X]) :
    (expandChipTail T b chalVal pubVal orbit H tail).Satisfies P
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
  rw [expandChipTail_satisfies_iff T b chalVal pubVal orbit H tail P]
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

end Tail

end

end MonolithicRAP
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.ChipTemplate.width_tail_eq_sum
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.expandChipTail_satisfies_iff
#print axioms Nock.NockVMROM.Thm54.MonolithicRAP.expandChipTail_satisfies_iff_language
