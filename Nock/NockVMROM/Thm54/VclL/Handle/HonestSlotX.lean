/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestSlotX.lean

  **The `𝕂′` slot pairs and the three
  accumulators of `computeChipVCLHX` at honest data, row level.**  Additive: a NEW module.

  * `slotDQ` / `slotAQ` — a slot's `𝕂′` denominator `D = Σ act_x · den_x (+ fl · den_a · den_b)` and
    activity `A = Σ act_x (+ fl · (den_a + den_b))`; `slotGateQX = inv · D − A` (`slotGateQX_eq`, `rfl`).
  * **`slotGateQX_honest`** — at any row whose `inv` limbs hold `A · D⁻¹` (the honest `𝕂′` inverse,
    `= Σ 1/den` on the active entries), the six coordinate gates of the slot pair vanish, provided
    `D ≠ 0 ∨ A = 0` (the priced pole event, `NotBad`).
  * **`accGatesX_prefixK`** — the accumulator gates of `ChipHX` (masks `isFirst = 17`, `isLast = 18`)
    vanish at a row whose accumulator limbs are the exclusive prefix sums of the per-row terms and
    whose public limbs are the coordinates of the total.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChipHX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.HonestSlotX

open Nock Nock.Reified Nock.Framework Module
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX

noncomputable section

/-! ## 1. A slot pair as `inv · D − A` -/

section SlotQ
variable (F : Type) [Field F] (δ : F)

def slotDQ (S : SlotX F) : Q F :=
  qadd F (sumQ F (S.ents.map fun x => qmul F δ (qlift F x.act) (denQX F δ x.rcd)))
    (match S.pair with
     | some (fl, a, b, _) => qmul F δ (qlift F (cc fl)) (qmul F δ (denQX F δ a) (denQX F δ b))
     | none => qconst F 0)

def slotAQ (S : SlotX F) : Q F :=
  qadd F (qlift F (CoeffExpr.sumList S.ents EntX.act))
    (match S.pair with
     | some (fl, a, b, _) => qmul F δ (qlift F (cc fl)) (qadd F (denQX F δ a) (denQX F δ b))
     | none => qconst F 0)

theorem slotGateQX_eq (S : SlotX F) :
    slotGateQX F δ S = qsub F (qmul F δ (qvar F .traceCur S.inv (some S.invIm)) (slotDQ F δ S))
      (slotAQ F δ S) := rfl

end SlotQ

section Honest
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (b : Basis (Fin 3) F K) (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- The `𝕂′` value held at a slot's inverse limbs. -/
def invAt (S : SlotX F) (eF : Env F) : 𝕂′ :=
  Quad.mk _ (limbVal b eF.trace S.inv) (limbVal b eF.trace S.invIm)

/-- `D` and `A` at a row (the coins are read through the limb gather). -/
def dVal (S : SlotX F) (eF : Env F) : 𝕂′ := Q.val δ (slotDQ F δ S) (gatherEnv b eF) eF
def aVal (S : SlotX F) (eF : Env F) : 𝕂′ := Q.val δ (slotAQ F δ S) (gatherEnv b eF) eF

/-- **The slot pair at an honest row**: inverse limbs `A · D⁻¹`, outside the pole event. -/
theorem slotGateQX_honest (S : SlotX F) (eF : Env F)
    (hinv : invAt b δ S eF = aVal b δ S eF * (dVal b δ S eF)⁻¹)
    (hnb : dVal b δ S eF ≠ 0 ∨ aVal b δ S eF = 0) :
    ∀ g ∈ qGates b (slotGateQX F δ S), g.eval eF = 0 := by
  rw [qGates_iff b (isCoordEnv_gather b eF), Q.isZero_iff δ, slotGateQX_eq, qsub_val, qmul_val,
    qvar_val]
  have hv : Quad.mk (algebraMap F K δ) (kread (gatherEnv b eF) .traceCur S.inv)
      (imVal (kread (gatherEnv b eF) .traceCur) (some S.invIm)) = invAt b δ S eF := rfl
  rw [hv, hinv]
  change aVal b δ S eF * (dVal b δ S eF)⁻¹ * dVal b δ S eF - aVal b δ S eF = 0
  rcases hnb with hd | ha
  · rw [inv_mul_cancel_right₀ hd, sub_self]
  · rw [ha]; ring

end Honest

/-! ## 2. The accumulators at a prefix-sum fill -/

section Acc
variable {F K : Type} [Field F] [Field K] [Algebra F K] (b : Basis (Fin 3) F K)

theorem coord_sumF (s : Finset ℕ) (f : ℕ → K) (k : Fin 3) :
    coord b (∑ j ∈ s, f j) k = ∑ j ∈ s, coord b (f j) k := by
  simp only [coord, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]

/-- **The `ChipHX` accumulator gates at honest data** (masks `17 / 18`): the accumulator limbs are the
coordinates of the exclusive prefix `Σ_{j<i} termVal`, the public limbs those of the total `ρ`. -/
theorem accGatesX_prefixK (slots : List (Slot F)) (accBase pubBase N i : ℕ) (hi : i < N)
    (envs : ℕ → Env F) (ρ : K)
    (h17 : (envs i).trace 17 = if i = 0 then 1 else 0)
    (h18 : (envs i).trace 18 = if i + 1 = N then 1 else 0)
    (hacc : ∀ k : Fin 3, (envs i).trace (accBase + k) =
      coord b (∑ j ∈ Finset.range i, termVal b slots (envs j)) k)
    (haccN : i + 1 < N → ∀ k : Fin 3, (envs i).traceNext (accBase + k) =
      coord b (∑ j ∈ Finset.range (i + 1), termVal b slots (envs j)) k)
    (hpub : ∀ k : Fin 3, (envs i).pub (pubBase + k) = coord b ρ k)
    (hρ : ∑ j ∈ Finset.range N, termVal b slots (envs j) = ρ) :
    ∀ g ∈ accGatesX slots accBase pubBase, g.eval (envs i) = 0 := by
  have ht : ∀ k : Fin 3, (termCoord slots k).eval (envs i) = coord b (termVal b slots (envs i)) k :=
    fun k => (coord_termVal b slots (envs i) k).symm
  intro g hg
  simp only [accGatesX, List.mem_append, List.mem_map, List.mem_range] at hg
  rcases hg with (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩
  · simp only [accInitX, cc, CoeffExpr.eval, firstX, h17]
    by_cases h0 : i = 0
    · subst h0
      have := hacc ⟨k, hk⟩
      simp only [Finset.range_zero, Finset.sum_empty] at this
      simp [this, coord]
    · simp [h0]
  · simp only [accStepX, cc, notC, CoeffExpr.eval, lastX, h18]
    by_cases hl : i + 1 = N
    · simp [hl]
    · simp only [hl, if_false, sub_zero, one_mul]
      have e1 := haccN (by omega) ⟨k, hk⟩
      have e2 := hacc ⟨k, hk⟩
      have e3 := ht ⟨k, hk⟩
      simp only at e1 e2 e3
      rw [e1, e2, e3, Finset.sum_range_succ]
      simp only [coord, map_add, Finsupp.add_apply]; ring
  · simp only [accTermX, cc, CoeffExpr.eval, lastX, h18]
    by_cases hl : i + 1 = N
    · simp only [hl, if_true, one_mul]
      have e2 := hacc ⟨k, hk⟩
      have e3 := ht ⟨k, hk⟩
      have e4 := hpub ⟨k, hk⟩
      simp only at e2 e3 e4
      rw [e2, e3, e4, ← hρ, ← hl, Finset.sum_range_succ]
      simp only [coord, map_add, Finsupp.add_apply]; ring
    · simp [hl]

end Acc

end

end Nock.NockVMROM.Thm54.VclL.Handle.HonestSlotX
