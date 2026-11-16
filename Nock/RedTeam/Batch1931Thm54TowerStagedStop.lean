/-
  Nock/RedTeam/Batch1931Thm54TowerStagedStop.lean

  `tableVCLT` puts EVERY Im column `232.. 393` in round 1.  Two of those triples are the Im halves of
  quantities whose honest values are functions of the walk coins `χ₀ = α`, `χ₁ = γ`, which `frameVCL`
  samples AFTER round 1 (`sampledAfter = 1`):
  * `391.. 393` = Im of walk column `W1` (the walk accumulator; `fullImMap.walk 1`, source `486`);
  * `388.. 390` = Im of role `59` (the walk-acc residual witness; `fullImMap.ext 59`).

  Compiled here:
  * `col_round_one`: `colRound` of `388.. 393` is `1`; `walk_coins_after_one`: `χ₀, χ₁` are sampled after
    round 1, so a round-1 column may NOT read them (`StagedCols`).
  * `fullImMap_walk_59`: the two triples are `fullImMap.walk 1 = 391` and `fullImMap.ext 59 = 388`.
  * `staged_col_irrel`: any `StagedCols` family is constant in `(χ₀, χ₁)` on columns `388.. 393`.
  * `honest_col391`: the honest fill (`vclColT`) puts `coord (Im (row.walk 1))` in `391 + k`, and
    `rowGen_walk1`: the honest row's `walk 1` is the walk accumulator `D.acc (j+1)`.
  * `acc_one`: the walk accumulator at row 1 is `Σ_{l ≤ fo 1} α^l·α·chld(1,l)` (from `WalkSat.accInit`,
    `ln 1 = α`, `initial_count = α`, `seed = RLC^γ(label₀)·α`): a polynomial in the walk coin `α` with no
    constant term, whose coefficients are the `RLC^γ` child labels.
  * `staged_forces_im_zero` (the NC): an honest staged family (column `391 + k` at row 0 equal to
    `coord (Im (acc₁ χ))` for every `χ`, `acc₁` at `α = ι χ₀`) forces `Im (Σ_l α^{l+1} c_l) = 0` at EVERY
    `α ∈ K` — i.e. all root-child labels `RLC^γ`-valued in `K`.  Honest labels carry `𝕂′` fingerprints at
    `z′ = χ₂ + χ₃√δ` (Im ≠ 0 at a cell noun): that last step is READING, unconfirmed by Lean.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerAssembled
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Nock.RedTeam.Batch1931

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Compute Module Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.ComputeTable Nock.NockVMROM.Thm54.ComputeWalkLabel

noncomputable section

def oldColRound (hC : ℕ) (j : Fin (tableVCLT hC).width) : ℕ :=
  if j.1 < 232 then colRoundVCLE j.1 else if j.1 < 394 then 1 else 2

/-- The six Im columns `388.. 393` were round `1` of the (old) tower table. -/
theorem col_round_one (hC : ℕ) (c : ℕ) (h1 : 388 ≤ c) (h2 : c < 394) (hw : c < (tableVCLT hC).width) :
    oldColRound hC ⟨c, hw⟩ = 1 := by
  simp only [oldColRound]
  rw [if_neg (by omega), if_pos h2]

/-- The walk coins `χ₀ = α`, `χ₁ = γ` are sampled after round 1. -/
theorem walk_coins_after_one :
    frameVCL.sampledAfter ⟨0, by decide⟩ = 1 ∧ frameVCL.sampledAfter ⟨1, by decide⟩ = 1 := by
  decide

/-- The two triples: Im of walk `W1` at `391`, Im of role `59` at `388`. -/
theorem fullImMap_walk_59 : fullImMap.walk 1 = some 391 ∧ fullImMap.ext 59 = some 388 := by
  decide +kernel

/-- **A staged family is constant in the walk coins on `388.. 393`.** -/
theorem staged_col_irrel {K β : Type} (hC : ℕ)
    (Q : Coins frameVCL K → Fin (tableVCLT hC).width → β)
    (hQ : StagedCols frameVCL (oldColRound hC) Q)
    (χ χ' : Coins frameVCL K) (hχ : ∀ i : Fin frameVCL.n, (i : ℕ) ≠ 0 → (i : ℕ) ≠ 1 → χ i = χ' i)
    (c : ℕ) (h1 : 388 ≤ c) (h2 : c < 394) (hw : c < (tableVCLT hC).width) :
    Q χ ⟨c, hw⟩ = Q χ' ⟨c, hw⟩ := by
  refine hQ ⟨c, hw⟩ χ χ' fun i hi => hχ i ?_ ?_
  · intro h0
    rw [col_round_one hC c h1 h2 hw] at hi
    have : frameVCL.sampledAfter i = 1 := by
      rw [show i = ⟨0, by decide⟩ from Fin.ext h0]; rfl
    omega
  · intro h0
    rw [col_round_one hC c h1 h2 hw] at hi
    have : frameVCL.sampledAfter i = 1 := by
      rw [show i = ⟨1, by decide⟩ from Fin.ext h0]; rfl
    omega

section Fill
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **The honest fill puts `Im (W1)` in `391.. 393`.** -/
theorem honest_col391 (b : Basis (Fin 3) F K) {n : ℕ} (rows : Fin n → TowerRowVals (K := K) δ)
    (i : Fin n) (k : Fin 3) :
    vclColT b rows (391 + k) i = coord b (Quad.im _ ((rows i).walk 1)) k := by
  fin_cases k <;> simp [vclColT, srcColT, imOwner]

/-- **The honest row's `walk 1` is the walk accumulator** `D.acc (j+1)`. -/
theorem rowGen_walk1 (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ))
    (D : HonestWalk (Quad (algebraMap F K δ))) (n : ℕ)
    (decAt : ℕ → Dec (Quad (algebraMap F K δ))) (vclAt : ℕ → ℕ → F) (j : ℕ)
    (r58 r59 : Quad (algebraMap F K δ)) :
    (rowGen χ αs D n decAt vclAt j r58 r59).walk 1 = D.acc (j + 1) := rfl

end Fill

/-- **The walk accumulator at row 1** (`WalkSat.accInit` at the honest walk: `ln 1 = α`,
`initial_count = α`, `seed = RLC^γ(label₀)·α`). -/
theorem acc_one {L : Type} [Field L] (D : HonestWalk L) :
    D.acc 1 = ∑ l ∈ Finset.Icc 1 (Walk.foCol D.W 1),
      D.α ^ l * D.α * Walk.chldCol D.nodeVal D.W 1 l := by
  have hI := D.sat.accInit
  have hl := D.sat.ln1
  have hc : Walk.curCol D.nodeVal D.W (0 + 1) = Walk.rlc D.γ (labelVecOfPub (D.pubAt 0)) :=
    D.cur_eq 0 (by have := bfsForest_length_pos D.root; simp only [HonestWalk.W]; omega)
  simp only [HonestWalk.W, zero_add] at hc ⊢
  rw [hl, hc, D.seed_eq] at hI
  linear_combination hI

section NC
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **NC: an honest staged family forces the root-child labels to be `K`-valued.**  `Q` is any staged
family; `acc₁ χ` is the honest row-1 accumulator at walk coin `α = ι χ₀` with child labels `c l` that do
not read `χ₀` (they are `RLC^γ` of the generator's labels; `γ = χ₁` is held fixed by `χ ↦ χ[0 ↦ a]`).
Honesty at column `391 + k` (the chip's `W1`-Im column, forced by the walk gates) and stagedness give
`Im (Σ_l α^{l+1} c_l) = 0` at EVERY `α ∈ K`. -/
theorem staged_forces_im_zero (hC : ℕ) (b : Basis (Fin 3) F K) (x0 : F)
    (Q : Coins frameVCL K → Fin (tableVCLT hC).width → Polynomial F)
    (hQ : StagedCols frameVCL (oldColRound hC) Q)
    (f : ℕ) (c : Coins frameVCL K → ℕ → Quad (algebraMap F K δ))
    (hc : ∀ χ χ', (∀ i : Fin frameVCL.n, (i : ℕ) ≠ 0 → χ i = χ' i) → c χ = c χ')
    (hhon : ∀ (χ : Coins frameVCL K) (k : Fin 3) (hw : 391 + (k : ℕ) < (tableVCLT hC).width),
      (Q χ ⟨391 + k, hw⟩).eval x0 = coord b (Quad.im _ (∑ l ∈ Finset.Icc 1 f,
        (algebraMap K (Quad (algebraMap F K δ)) (χ ⟨0, by decide⟩)) ^ l *
          algebraMap K (Quad (algebraMap F K δ)) (χ ⟨0, by decide⟩) * c χ l)) k)
    (χ : Coins frameVCL K) (a : K) :
    Quad.im _ (∑ l ∈ Finset.Icc 1 f, (algebraMap K (Quad (algebraMap F K δ)) a) ^ l *
      algebraMap K (Quad (algebraMap F K δ)) a * c χ l) = 0 := by
  classical
  let upd : K → Coins frameVCL K := fun v => Function.update χ ⟨0, by decide⟩ v
  have hagree : ∀ v v' : K, ∀ i : Fin frameVCL.n, (i : ℕ) ≠ 0 → (i : ℕ) ≠ 1 → upd v i = upd v' i := by
    intro v v' i h0 _
    have : i ≠ ⟨0, by decide⟩ := fun h => h0 (by rw [h])
    simp [upd, Function.update_of_ne this]
  have hcu : ∀ v, c (upd v) = c χ := fun v => hc _ _ fun i h0 => by
    have : i ≠ ⟨0, by decide⟩ := fun h => h0 (by rw [h])
    simp [upd, Function.update_of_ne this]
  have h0 : ∀ v, upd v ⟨0, by decide⟩ = v := fun v => by simp [upd]
  have hw : ∀ k : Fin 3, 391 + (k : ℕ) < (tableVCLT hC).width := fun k => by
    have := k.isLt; simp [tableVCLT, vclWidthT]; omega
  have hcoord : ∀ k : Fin 3,
      coord b (Quad.im _ (∑ l ∈ Finset.Icc 1 f, (algebraMap K (Quad (algebraMap F K δ)) a) ^ l *
        algebraMap K (Quad (algebraMap F K δ)) a * c χ l)) k =
      coord b (Quad.im _ (∑ l ∈ Finset.Icc 1 f, (algebraMap K (Quad (algebraMap F K δ)) 0) ^ l *
        algebraMap K (Quad (algebraMap F K δ)) 0 * c χ l)) k := by
    intro k
    have e1 := hhon (upd a) k (hw k)
    have e2 := hhon (upd 0) k (hw k)
    rw [h0, hcu] at e1 e2
    rw [← e1, ← e2, staged_col_irrel hC Q hQ (upd a) (upd 0) (hagree a 0) (391 + k) (by omega)
      (by have := k.isLt; omega) (hw k)]
  have hzero : Quad.im _ (∑ l ∈ Finset.Icc 1 f, (algebraMap K (Quad (algebraMap F K δ)) 0) ^ l *
      algebraMap K (Quad (algebraMap F K δ)) 0 * c χ l) = 0 := by
    simp only [map_zero, mul_zero, zero_mul, Finset.sum_const_zero]
    rw [← Quad.mk_zero' (algebraMap F K δ), Quad.im_mk]
  rw [hzero] at hcoord
  have : b.repr (Quad.im _ (∑ l ∈ Finset.Icc 1 f, (algebraMap K (Quad (algebraMap F K δ)) a) ^ l *
      algebraMap K (Quad (algebraMap F K δ)) a * c χ l)) = b.repr 0 := by
    ext k; simpa [coord] using hcoord k
  exact b.repr.injective this

end NC

end

#print axioms col_round_one
#print axioms walk_coins_after_one
#print axioms fullImMap_walk_59
#print axioms staged_col_irrel
#print axioms honest_col391
#print axioms rowGen_walk1
#print axioms acc_one
#print axioms staged_forces_im_zero

end Nock.RedTeam.Batch1931
