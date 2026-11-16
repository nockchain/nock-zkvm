/-
  Nock/RedTeam/Batch628Thm54LambdaEventLift.lean

  * **Q2, the lift.**  `liftedBad T E' x := ⋃_{i < kMem} formRBadAt (T.afterSeed ⟨x z, _⟩).exec i E' x`
    (empty at `x z = 0`, where acceptance rejects anyway).  `lifted_readsOn_seed`: it is
    `ReadsOn {seedIdx}` — from A4's `formRBadAt_eq_template` (the per-template set is a template
    constant) and the dependent `if` on `x seedIdx`; `lifted_readsOn_prior`: hence `ReadsOn
    (priorCoords landedRound lamIdx)` by monotonicity (`{3} ⊆ {3, 6, 7, 8}`).  `{seedIdx}` is the
    right prior: λ is in `αM`'s round (1), `z` in round 0, and the template is a function of `z`
    alone (`afterSeed`); nothing of round 1 is read.
  * **Q3, the figure.**  The union over `kMem` trees therefore has
    `card ≤ |K| · Σ_i (2(n−1) + M_i + E) = |K| · (M + kMem · (2(n−1) + E))`
    (`union_card_le`, `sum_figure`).  At `n = 64`, `E = 3N + 3`: **`M + kMem · (3N + 129)`**.
    The grant's single summand `pwAccountingWork' 64 N M = M + 3N + 130` covers this iff
    `kMem ≤ 1` (`fits_iff_one_tree`); for `kMem ≥ 2` it is short by `(kMem − 1)(3N + 129) − 1`
    (`shortfall`).
  * **Bit figures, recomputed (not quoted) under the TRUE summand** with `kMem ≤ M` (every tree
    has a root): `(367·2^62 + 144·2^31 + 28 + 2·(M + M·(3N+129)))·2^122 < 2·|𝕂|` at `N = M = 2^31`
    (`figure_122_true`), and `… · 2^120 < 2·|𝕂|` at `2^32` (`figure_120_true`).  The `123` figure is
    the `𝕂²` summands' and does not see the walk work.  So the figures do NOT move even at the true
    figure — the grant's number is wrong but harmless to the bit budget.
-/
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.RedTeam.Batch556Thm54PwEvent

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch628

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.RoundFibred

noncomputable section

/-! ## Q2 — the lifted bad set and its read set -/

section Lift
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

/-- The λ-event's bad set at a coin vector `x`, over the strategy's post-seed template: the union
over the memory trees of the Form R root set.  Empty at `x z = 0` (acceptance rejects there). -/
def liftedBad (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)) (E' : ℕ)
    (x : Fin 11 → K) : Finset (K × K) :=
  if hz : x seedIdx ≠ 0 then
    Finset.univ.biUnion fun i : Fin (T.afterSeed ⟨x seedIdx, hz⟩).configTemplate.kMem =>
      formRBadAt (T.afterSeed ⟨x seedIdx, hz⟩).executionTemplate i E' x
  else ∅

/-- **The lift reads `{z}` only.** -/
theorem lifted_readsOn_seed (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (E' : ℕ) :
    ReadsOn (C := K) (n := 11) ({seedIdx} : Finset (Fin 11)) (liftedBad T E') := by
  intro x y hxy
  have hz : x seedIdx = y seedIdx := hxy seedIdx (Finset.mem_singleton_self _)
  unfold liftedBad
  by_cases h : x seedIdx ≠ 0
  · have h' : y seedIdx ≠ 0 := hz ▸ h
    rw [dif_pos h, dif_pos h']
    -- the two carriers are the same object once the seeds agree
    have hc : (⟨x seedIdx, h⟩ : { z : K // z ≠ 0 }) = ⟨y seedIdx, h'⟩ := Subtype.ext hz
    -- generalize the two subtype points and identify them
    generalize hs : (⟨x seedIdx, h⟩ : { z : K // z ≠ 0 }) = s at hc ⊢
    generalize hs' : (⟨y seedIdx, h'⟩ : { z : K // z ≠ 0 }) = s' at hc ⊢
    subst hc
    apply Finset.biUnion_congr rfl
    intro i _
    rw [formRBadAt_eq_template, formRBadAt_eq_template]
  · have h' : ¬ y seedIdx ≠ 0 := hz ▸ h
    rw [dif_neg h, dif_neg h']

/-- Hence the `priorCoords landedRound lamIdx` statement (`{3} ⊆ {3, 6, 7, 8}`). -/
theorem lifted_readsOn_prior (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (E' : ℕ) :
    ReadsOn (C := K) (n := 11) (priorCoords landedRound lamIdx) (liftedBad T E') := by
  intro x y hxy
  apply lifted_readsOn_seed T E' x y
  intro j hj
  rw [Finset.mem_singleton] at hj
  subst hj
  exact hxy _ (by decide)

/-- `{z}` is strictly below λ's round; the IO pair, `interPole` and `αM` are not read. -/
theorem seed_prior : seedIdx ∈ priorCoords landedRound lamIdx ∧
    alphaMIdx ∉ priorCoords landedRound lamIdx ∧ (4 : Fin 11) ∉ priorCoords landedRound lamIdx ∧
    (9 : Fin 11) ∉ priorCoords landedRound lamIdx := by decide

theorem union_card_le (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (E' : ℕ) (x : Fin 11 → K) (hz : x seedIdx ≠ 0) :
    (liftedBad T E' x).card ≤
      ∑ i : Fin (T.afterSeed ⟨x seedIdx, hz⟩).configTemplate.kMem,
        (formRBadAt (T.afterSeed ⟨x seedIdx, hz⟩).executionTemplate i E' x).card := by
  unfold liftedBad
  rw [dif_pos hz]
  exact Finset.card_biUnion_le

end Lift

/-! ## Q3 — the figure of the union -/

/-- Per-tree majorant at scale `n`: `2(n−1) + M_i + E`. -/
def perTree (n Mi E : ℕ) : ℕ := 2 * (n - 1) + Mi + E

/-- The sum over `k` trees with node counts `Ms` (`Σ Ms = M`). -/
theorem sum_figure (n E : ℕ) (Ms : List ℕ) :
    (Ms.map fun Mi => perTree n Mi E).sum = Ms.sum + Ms.length * (2 * (n - 1) + E) := by
  induction Ms with
  | nil => simp
  | cons m rest ih =>
      rw [List.map_cons, List.sum_cons, ih, List.sum_cons, List.length_cons]
      unfold perTree
      ring

/-- The true figure at `n = 64`, `E = 3N + 3`: `M + kMem · (3N + 129)`. -/
def trueFigure (N M kMem : ℕ) : ℕ := M + kMem * (3 * N + 129)

theorem trueFigure_eq (N : ℕ) (Ms : List ℕ) :
    (Ms.map fun Mi => perTree 64 Mi (3 * N + 3)).sum = trueFigure N Ms.sum Ms.length := by
  rw [sum_figure, trueFigure]; ring

/-- The grant's single summand covers the union iff there is at most one tree. -/
theorem fits_iff_one_tree (N M kMem : ℕ) :
    trueFigure N M kMem ≤ Batch557.pwAccountingWork' 64 N M ↔ kMem ≤ 1 := by
  unfold trueFigure Batch557.pwAccountingWork'
  constructor
  · intro h
    by_contra hk
    push_neg at hk
    have : 2 * (3 * N + 129) ≤ kMem * (3 * N + 129) := Nat.mul_le_mul_right _ hk
    omega
  · intro h
    have : kMem * (3 * N + 129) ≤ 1 * (3 * N + 129) := Nat.mul_le_mul_right _ h
    omega

theorem shortfall (N M kMem : ℕ) (hk : 2 ≤ kMem) :
    trueFigure N M kMem = Batch557.pwAccountingWork' 64 N M + ((kMem - 1) * (3 * N + 129) - 1) := by
  unfold trueFigure Batch557.pwAccountingWork'
  have h1 : (kMem - 1) * (3 * N + 129) = kMem * (3 * N + 129) - (3 * N + 129) := by
    rw [Nat.sub_mul, one_mul]
  have h2 : 2 * (3 * N + 129) ≤ kMem * (3 * N + 129) := Nat.mul_le_mul_right _ hk
  omega

/-! ## Bit figures under the true summand (`kMem ≤ M`) -/

open Nock.NockVMROM.Thm54.GoldilocksParameters in
/-- `122` bits at `2^31` rows still hold with the TRUE summand at `kMem = M`. -/
theorem figure_122_true :
    (367 * 2 ^ 62 + 144 * 2 ^ 31 + 28 + 2 * trueFigure (2 ^ 31) (2 ^ 31) (2 ^ 31)) * 2 ^ 122
      < 2 * cardKGold := by
  norm_num [trueFigure, cardKGold]

open Nock.NockVMROM.Thm54.GoldilocksParameters in
/-- `120` bits at `2^32` rows still hold with the TRUE summand at `kMem = M`. -/
theorem figure_120_true :
    (367 * 2 ^ 64 + 144 * 2 ^ 32 + 28 + 2 * trueFigure (2 ^ 32) (2 ^ 32) (2 ^ 32)) * 2 ^ 120
      < 2 * cardKGold := by
  norm_num [trueFigure, cardKGold]

/-- The grant's figure is the `kMem = 1` instance (sanity). -/
theorem grant_is_one_tree (N M : ℕ) : trueFigure N M 1 + 1 = Batch557.pwAccountingWork' 64 N M := by
  unfold trueFigure Batch557.pwAccountingWork'; ring

end

end Nock.RedTeam.Batch628
