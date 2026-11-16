/-
  Nock/NockVMROM/Thm54/TraceGen/GenTowerSeed.lean

  **The tower seed and the window `hΛK` at the generator.**

  1. **`FP (Quad K)` through the generator, below the pin.**  The generator
     (`renderNode`, `genComputeRows`, `encC`) is field-generic: `[Field K]` only.  Its
     instantiation at `K′ := Quad δ` with the tower seed `z′ = Quad.mk δ z₁ z₂` therefore needs no
     edit.  Every fingerprint the rendered compute rows commit is `FP (Quad δ)`, and its
     `𝕂`-coordinate form (`FP2`, `Batch1542`) is `fn2 δ n (z₁, z₂)`.  The 𝕂′-column carrier is the
     `FP2` pair view; no `Module.finrank` enters any `FP` consumer here, and no object is typed
     over 𝕂 and 𝕂′ side by side (the timestamp `α` is embedded by `algebraMap`).
  2. **`hΛK` at the generator.**  `hLambdaK pG 6 R Λ` at `Λ := programLeafBound (airReorder t)`,
     `R := (bfsRows (airReorder t)).length` (the compute rows only; no forest), discharged from the
     numerals `Λ ≤ 2^110`, `R ≤ 2^32` (`hLambdaK6_goldilocks_hΛK_proved`); and the seed budget
     (the divisor-priced budget of `Batch1541.tower_window_card_le`) `< |𝕂′| = p⁶`.
-/
import Nock.Primality.Goldilocks
import Nock.NockVMROM.Thm54.P8Core.Batch1542Thm54T0TowerFP
import Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen.GenTowerSeed

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TightWindow

noncomputable section

/-! ## 1. `FP (Quad K)` at the generator -/

section Seed
variable {K : Type} [Field K] [Fintype K] (δ : K) [Fact (¬ IsSquare δ)]

/-- The tower seed `z′ = z₁ + z₂√δ ∈ 𝕂′`. -/
def towerSeed (z₁ z₂ : K) : Quad δ := Quad.mk δ z₁ z₂

/-- The committed compute tree of a generated program at the tower seed: the existing generator,
instantiated at `K′ = Quad δ`; the timestamp base `α ∈ 𝕂` is embedded. -/
def genComputeRowsQ (z₁ z₂ α : K) (t : NTree (GenComputeRow (Quad δ))) :
    NTree (GenComputeRow (Quad δ)) :=
  genComputeRows (towerSeed δ z₁ z₂) (algebraMap K (Quad δ) α) t

/-- **The generator's fingerprint at the tower seed is `FP (Quad δ)`, the `FP2` coordinates of
`fn2`.**  (`encC` is the generator's fingerprint.) -/
theorem encC_towerSeed (z₁ z₂ : K) (n : Noun) :
    encC (towerSeed δ z₁ z₂) n = FP2.toFP δ (fn2 δ n (z₁, z₂)) := by
  rw [toFP_fn2, encC_eq]; rfl

/-- The coordinate view: `ofFP` of the committed fingerprint is `fn2`. -/
theorem ofFP_encC_towerSeed (z₁ z₂ : K) (n : Noun) :
    FP2.ofFP δ (encC (towerSeed δ z₁ z₂) n) = fn2 δ n (z₁, z₂) := by
  rw [encC_towerSeed, FP2.ofFP_toFP]

/-- Rendered `s0` row: the committed tail fingerprint is `fn2` of the formula tail at the tower
seed (the seeding site of `GenFormRAxisLambda`, at `K′`). -/
theorem renderNode_s0_f_t_tower (z₁ z₂ α : K) (g : GenComputeRow (Quad δ))
    (h : g.skel.state = .s0) :
    FP2.ofFP δ
        (renderNode (towerSeed δ z₁ z₂) (algebraMap K (Quad δ) α) g).row.2.2.2.f_t =
      fn2 δ (formulaTail g.skel.formula) (z₁, z₂) := by
  rw [(GenFormRAxisLambda.renderNode_row_s0 _ _ g h).2, ofFP_encC_towerSeed]

/-- Rendered `s9` row, same. -/
theorem renderNode_s9_f_th_tower (z₁ z₂ α : K) (g : GenComputeRow (Quad δ))
    (h : g.skel.state = .s9) :
    FP2.ofFP δ
        (renderNode (towerSeed δ z₁ z₂) (algebraMap K (Quad δ) α) g).row.2.2.2.f_th =
      fn2 δ (formulaHead (formulaTail g.skel.formula)) (z₁, z₂) := by
  rw [(GenFormRAxisLambda.renderNode_row_s9 _ _ g h).2, ofFP_encC_towerSeed]

omit [Fintype K] in
/-- The tower seed is injective in its coordinates (distinct `(z₁, z₂)` are distinct seeds). -/
theorem towerSeed_injective : Function.Injective (fun p : K × K => towerSeed δ p.1 p.2) :=
  Quad.mk_injective δ

end Seed

/-! ## 2. `hΛK` at the generator -/

section Window

/-- Monotonicity of `hΛK` in the row count and the window. -/
theorem hLambdaK_mono {p e R R' Λ Λ' : ℕ} (h : hLambdaK p e R' Λ') (hR : R ≤ R') (hΛ : Λ ≤ Λ') :
    hLambdaK p e R Λ := by
  unfold hLambdaK at h ⊢
  have h1 : (3 + 13 * R) * (2 * Λ - 1) ≤ (3 + 13 * R') * (2 * Λ' - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : ∑ d ∈ (p ^ e - 1).divisors.filter (· ≤ Λ), d ≤
      ∑ d ∈ (p ^ e - 1).divisors.filter (· ≤ Λ'), d :=
    Finset.sum_le_sum_of_subset (by
      intro d hd
      simp only [Finset.mem_filter] at hd ⊢
      exact ⟨hd.1, le_trans hd.2 hΛ⟩)
  omega

variable {K : Type} [Field K]

/-- The compute-row count of a generated tree: `bfsForest` length, compute rows only (no forest). -/
def computeRowCount (t : NTree (GenComputeRow K)) : ℕ := (bfsRows (airReorder t)).length

/-- **`hΛK` at the generator**: `Λ := programLeafBound (airReorder t)`, `R := computeRowCount t`,
at the tower field `p⁶`, from the numerals `Λ ≤ 2^110` and `R ≤ 2^32`. -/
theorem hLambdaK_generator (t : NTree (GenComputeRow K))
    (hΛ : programLeafBound (airReorder t) ≤ 2 ^ 110) (hR : computeRowCount t ≤ 2 ^ 32) :
    hLambdaK pG 6 (computeRowCount t) (programLeafBound (airReorder t)) :=
  hLambdaK_mono (hLambdaK6_goldilocks_hΛK_proved (2 ^ 32) le_rfl) hR hΛ

/-- **The seed-budget half of `hp`, re-derived from `hΛK` at the tower**: the divisor-priced
budget is `< |𝕂′| = p⁶` (`|𝕂| = p³`). -/
theorem towerSeedBudget_lt_card {K : Type} [Field K] [Fintype K] (δ : K) [Fact (¬ IsSquare δ)]
    (hcard : Fintype.card K = pG ^ 3) {R Λ : ℕ} (h : hLambdaK pG 6 R Λ) :
    1 + (3 + 13 * R) * (2 * Λ - 1) +
        ∑ d ∈ (Fintype.card (Quad δ) - 1).divisors.filter (· ≤ Λ), d <
      Fintype.card (Quad δ) := by
  have hq : Fintype.card (Quad δ) = pG ^ 6 := by
    rw [quad_card, hcard, ← pow_mul]
  rw [hq]; exact h

/-- At the generator, in one statement. -/
theorem towerSeedBudget_generator {K' : Type} [Field K'] [Fintype K'] (δ : K')
    [Fact (¬ IsSquare δ)] (hcard : Fintype.card K' = pG ^ 3)
    (t : NTree (GenComputeRow K))
    (hΛ : programLeafBound (airReorder t) ≤ 2 ^ 110) (hR : computeRowCount t ≤ 2 ^ 32) :
    1 + (3 + 13 * computeRowCount t) * (2 * programLeafBound (airReorder t) - 1) +
        ∑ d ∈ (Fintype.card (Quad δ) - 1).divisors.filter
          (· ≤ programLeafBound (airReorder t)), d < Fintype.card (Quad δ) :=
  towerSeedBudget_lt_card δ hcard (hLambdaK_generator t hΛ hR)

end Window

end

end Nock.NockVMROM.Thm54.TraceGen.GenTowerSeed
