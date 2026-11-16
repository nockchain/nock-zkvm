/-
  Nock/NockVMROM/Thm54/VclL/Handle/ExtendH.lean

  Additive: a new module, no existing module edited.

  A twin template `T'` that keeps `T`'s base and mixed gates (each reading only `T`'s columns /
  `𝕂`-roles) accepts a trace `Q'` whenever (i) the original `T` accepts the restriction of `Q'` and
  (ii) every gate of `T'` that is not a gate of `T` holds row by row.  Generic in the twin.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ProvideH
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemQ

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module
open scoped Polynomial

noncomputable section

section Extend
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (b : Basis (Fin 3) F K) {h : ℕ} (orbit : StrictOrbitDomain F 3 h) (H : Finset F)
  (chals pubs : ℕ → K)

/-- **`expandChip_extend`.**  The converse of `expandChip_restrict`: if the original accepts the
restriction of `Q'`, and every NEW gate of the twin (not a gate of the original) holds at every row
of `Q'`, then the twin accepts `Q'`.  The twin carries no equality / extension-field gates. -/
theorem expandChip_extend (T T' : ChipTemplate F) (B B' : ℕ) (hBe : T.baseCols = B)
    (hB'e : T'.baseCols = B') (hB : B ≤ B') (hR : T.extCols ≤ T'.extCols)
    (hbase : ∀ g ∈ T.baseTransition, g ∈ T'.baseTransition ∧ colsBelow B g = true)
    (hmix : ∀ g ∈ T.mixedTransition,
      g ∈ T'.mixedTransition ∧ mixBelow T.extCols B g = true)
    (hEq' : T'.equalityChecks = []) (hExt' : T'.extTransition ++ T'.extDeg1 ++ T'.extDeg3 = [])
    (Q : Fin (expandChip T' b (slotVal b B' chals) (slotVal b B' pubs) orbit H).w → F[X])
    (hsat : (expandChip T b (slotVal b B chals) (slotVal b B pubs) orbit H).Satisfies
      (restrictQ B B' (shift_lt T T' B B' hBe hB'e hB hR) Q))
    (hnewB : ∀ x ∈ H, ∀ g ∈ T'.baseTransition, g ∉ T.baseTransition →
      g.eval (Reify.envOfTrace Q orbit.ω x (slotVal b B' chals) (slotVal b B' pubs)) = 0)
    (hnewM : ∀ x ∈ H, ∀ g ∈ T'.mixedTransition, g ∉ T.mixedTransition →
      g.eval (gatherEnv b (T'.col0 3) (Reify.envOfTrace Q orbit.ω x (slotVal b B' chals) (slotVal b B' pubs)))
        (Reify.envOfTrace Q orbit.ω x (slotVal b B' chals) (slotVal b B' pubs)) = 0) :
    (expandChip T' b (slotVal b B' chals) (slotVal b B' pubs) orbit H).Satisfies Q := by
  subst hBe hB'e
  rw [expandChip_satisfies_iff_language]
  have hsat' := (expandChip_satisfies_iff_language T b _ _ orbit H _).mp hsat
  intro x hx
  obtain ⟨hb0, -, -, hm0⟩ := hsat' x hx
  set e0 := Reify.envOfTrace (restrictQ T.baseCols T'.baseCols (shift_lt T T' _ _ rfl rfl hB hR) Q) orbit.ω x
    (slotVal b T.baseCols chals) (slotVal b T.baseCols pubs)
  set e1 := Reify.envOfTrace Q orbit.ω x (slotVal b T'.baseCols chals) (slotVal b T'.baseCols pubs)
  have ht : ∀ j < T.baseCols, e0.trace j = e1.trace j := by
    intro j hj
    have := envOfTrace_restrict_trace T.baseCols T'.baseCols (shift_lt T T' _ _ rfl rfl hB hR) Q orbit.ω x
      (slotVal b T.baseCols chals) (slotVal b T.baseCols pubs) (slotVal b T'.baseCols chals)
      (slotVal b T'.baseCols pubs) (j := j) (by show j < T.width 3; unfold ChipTemplate.width; omega)
    rw [this]; simp only [shiftCol, if_pos hj]; rfl
  have hn : ∀ j < T.baseCols, e0.traceNext j = e1.traceNext j := by
    intro j hj
    have := envOfTrace_restrict_traceNext T.baseCols T'.baseCols (shift_lt T T' _ _ rfl rfl hB hR) Q orbit.ω x
      (slotVal b T.baseCols chals) (slotVal b T.baseCols pubs) (slotVal b T'.baseCols chals)
      (slotVal b T'.baseCols pubs) (j := j) (by show j < T.width 3; unfold ChipTemplate.width; omega)
    rw [this]; simp only [shiftCol, if_pos hj]; rfl
  have hlimb : ∀ i < T.extCols, ∀ k : Fin 3,
      e0.trace (T.col0 3 .traceCur i + k) = e1.trace (T'.col0 3 .traceCur i + k) ∧
      e0.traceNext (T.col0 3 .traceNext i + k) = e1.traceNext (T'.col0 3 .traceNext i + k) := by
    intro i hi k
    have hk := k.isLt
    have hlt : T.col0 3 .traceCur i + k < T.width 3 := by
      unfold ChipTemplate.col0 ChipTemplate.width; nlinarith
    have hsh : shiftCol T.baseCols T'.baseCols (T.col0 3 .traceCur i + k) = T'.col0 3 .traceCur i + k := by
      unfold shiftCol ChipTemplate.col0
      rw [if_neg (by omega)]; omega
    constructor
    · exact (envOfTrace_restrict_trace T.baseCols T'.baseCols (shift_lt T T' _ _ rfl rfl hB hR) Q orbit.ω x _ _
        (slotVal b T'.baseCols chals) (slotVal b T'.baseCols pubs) hlt).trans (by rw [hsh]; try rfl)
    · have hsh' : shiftCol T.baseCols T'.baseCols (T.col0 3 .traceNext i + k) = T'.col0 3 .traceNext i + k := hsh
      have hlt' : T.col0 3 .traceNext i + k < T.width 3 := hlt
      exact (envOfTrace_restrict_traceNext T.baseCols T'.baseCols (shift_lt T T' _ _ rfl rfl hB hR) Q orbit.ω x _ _
        (slotVal b T'.baseCols chals) (slotVal b T'.baseCols pubs) hlt').trans (by rw [hsh']; try rfl)
  refine ⟨fun g hg => ?_, by simp [hEq'], by simp [hExt'], fun g hg => ?_⟩
  · by_cases hg0 : g ∈ T.baseTransition
    · show g.eval e1 = 0
      rw [← colsBelow_eval (hbase g hg0).2 ht hn]
      exact hb0 g hg0
    · exact hnewB x hx g hg hg0
  · by_cases hg0 : g ∈ T.mixedTransition
    · show g.eval (gatherEnv b (T'.col0 3) e1) e1 = 0
      have this : g.eval (gatherEnv b (T.col0 3) e0) e0 = 0 := hm0 g hg0
      rw [mixBelow_eval (hmix g hg0).2 (eK' := gatherEnv b (T'.col0 3) e1) (eF' := e1) ?_ ?_ ?_ ?_ ht hn]
        at this
      · exact this
      · intro i hi
        simp only [gatherEnv]
        exact Finset.sum_congr rfl fun k _ => by rw [(hlimb i hi k).1]
      · intro i hi
        simp only [gatherEnv]
        exact Finset.sum_congr rfl fun k _ => by rw [(hlimb i hi k).2]
      · funext i
        simp only [gatherEnv, ChipTemplate.col0]
        show ∑ k : Fin 3, slotVal b T.baseCols chals (T.baseCols + 3 * i + k) • b k =
          ∑ k : Fin 3, slotVal b T'.baseCols chals (T'.baseCols + 3 * i + k) • b k
        rw [sum_slotVal, sum_slotVal]
      · funext i
        simp only [gatherEnv, ChipTemplate.col0]
        show ∑ k : Fin 3, slotVal b T.baseCols pubs (T.baseCols + 3 * i + k) • b k =
          ∑ k : Fin 3, slotVal b T'.baseCols pubs (T'.baseCols + 3 * i + k) • b k
        rw [sum_slotVal, sum_slotVal]
    · exact hnewM x hx g hg hg0

end Extend

/-! ## The honest extension of a column function -/

section HonestExt
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- The twin's column function from the original's `col` and the NEW columns `new` (indexed by the
twin's column number): original columns below `B` stay, the new base columns sit at `[B, B')`, the
original `𝕂`-role limbs move up by `B' − B`, and the new role limbs sit after them. -/
def extColF {n : ℕ} (B B' W : ℕ) (col new : ℕ → Fin n → F) (j : ℕ) (i : Fin n) : F :=
  if j < B then col j i else if j < B' then new j i
  else if j < W + (B' - B) then col (j - (B' - B)) i else new j i

theorem fullCol_extColF_shift {n : ℕ} (hn : 0 < n) (B B' W : ℕ) (hB : 1 < B) (hBB : B ≤ B')
    (col new : ℕ → Fin n → F) (j : ℕ) (hj : j < W) (i : Fin n) :
    fullCol hn (extColF B B' W col new) (shiftCol B B' j) i = fullCol hn col j i := by
  by_cases h : j < B
  · simp only [fullCol, shiftCol, extColF, if_pos h]
  · have h1 : ¬ (j + (B' - B) < B) := by omega
    have h2 : ¬ (j + (B' - B) < B') := by omega
    have h3 : j + (B' - B) < W + (B' - B) := by omega
    have h4 : j + (B' - B) - (B' - B) = j := by omega
    simp only [fullCol, shiftCol, extColF, if_neg h, if_neg h1, if_neg h2, if_pos h3, h4]
    try (split_ifs <;> first | rfl | omega)

theorem honestQ_restrict_extColF {n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (B B' W : ℕ) (hB : 1 < B)
    (hBB : B ≤ B') (col new : ℕ → Fin n → F) {w w' : ℕ} (hw : ∀ j < w, shiftCol B B' j < w')
    (hwW : w = W) :
    restrictQ B B' hw (honestQ hn nodes (extColF B B' W col new) w') = honestQ hn nodes col w := by
  funext j
  simp only [restrictQ, honestQ]
  congr 1
  funext i
  exact fullCol_extColF_shift hn B B' W hB hBB col new j (hwW ▸ j.isLt) i

end HonestExt

section HonestExtend
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (b : Basis (Fin 3) F K) {h : ℕ} (orbit : StrictOrbitDomain F 3 h) (H : Finset F)
  (chals pubs : ℕ → K)

/-- **The honest twin trace is accepted** once the original honest trace is and the new gates hold at
every row of the extended column function: `expandChip_extend` with the restriction computed. -/
theorem expandChip_extend_honest (T T' : ChipTemplate F) (B B' : ℕ) (hBe : T.baseCols = B)
    (hB'e : T'.baseCols = B') (hB : B ≤ B') (hB1 : 1 < B) (hR : T.extCols ≤ T'.extCols)
    (hbase : ∀ g ∈ T.baseTransition, g ∈ T'.baseTransition ∧ colsBelow B g = true)
    (hmix : ∀ g ∈ T.mixedTransition,
      g ∈ T'.mixedTransition ∧ mixBelow T.extCols B g = true)
    (hEq' : T'.equalityChecks = []) (hExt' : T'.extTransition ++ T'.extDeg1 ++ T'.extDeg3 = [])
    {n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (col new : ℕ → Fin n → F)
    (hsat : (expandChip T b (slotVal b B chals) (slotVal b B pubs) orbit H).Satisfies
      (honestQ hn nodes col _))
    (hnewB : ∀ x ∈ H, ∀ g ∈ T'.baseTransition, g ∉ T.baseTransition →
      g.eval (Reify.envOfTrace (honestQ hn nodes (extColF B B' (T.width 3) col new) (T'.width 3))
        orbit.ω x (slotVal b B' chals) (slotVal b B' pubs)) = 0)
    (hnewM : ∀ x ∈ H, ∀ g ∈ T'.mixedTransition, g ∉ T.mixedTransition →
      g.eval (gatherEnv b (T'.col0 3)
        (Reify.envOfTrace (honestQ hn nodes (extColF B B' (T.width 3) col new) (T'.width 3))
          orbit.ω x (slotVal b B' chals) (slotVal b B' pubs)))
        (Reify.envOfTrace (honestQ hn nodes (extColF B B' (T.width 3) col new) (T'.width 3))
          orbit.ω x (slotVal b B' chals) (slotVal b B' pubs)) = 0) :
    (expandChip T' b (slotVal b B' chals) (slotVal b B' pubs) orbit H).Satisfies
      (honestQ hn nodes (extColF B B' (T.width 3) col new) _) := by
  refine expandChip_extend b orbit H chals pubs T T' B B' hBe hB'e hB hR hbase hmix hEq' hExt' _ ?_
    hnewB hnewM
  have e := honestQ_restrict_extColF hn nodes B B' (T.width 3) hB1 hB col new
    (shift_lt T T' B B' hBe hB'e hB hR) (w := T.width 3) (w' := T'.width 3) rfl
  exact e ▸ hsat

end HonestExtend


end

end Nock.NockVMROM.Thm54.VclL.Handle
