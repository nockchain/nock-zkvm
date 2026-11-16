/-
  Nock/NockVMROM/Thm54/VclL/Handle/ChalsAZJ8.lean

  R1 found (`AcceptsJ8P.chalsAJ8_zAt`, kernel) that the g5 key's size entry `zAt = QE.chal 37 38` reads, at
  `ProbJ8.chalsAJ8`, the coordinates of `γ′^13` (a round-1 validity coin).

  * **`chalsAJ8Z`** = `chalsAJ8` except leaves `37 / 38`, which carry `χ₂ / χ₃`;
  * `chalsAJ8Z_of_ne` (agreement off `37 / 38`), **`chalsAJ8Z_agree`** (FinalJ8's `hchA`, leaves `33..36`),
    **`chalsAJ8Z_y`** (the limb coin `y` at leaves `2 / 3`), **`chalsAJ8Z_ok`** (`ChalsOK … γ′ ρ′ 11`: the
    validity coins, leaves `5, 7, 11..32`), `chalsAJ8Z_01` (leaves `0 / 1`), and **`chalsAJ8Z_zAt`**: the size
    entry now reads `z`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree chalsAJ8_y chalsAJ8_ok)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

noncomputable section

section Vectors
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

def chalsAJ8Z (χ : Coins frameJ8 K) (j : ℕ) : K :=
  if j = 37 then χ c2 else if j = 38 then χ c3 else chalsAJ8 δ χ j

theorem chalsAJ8Z_of_ne (χ : Coins frameJ8 K) {j : ℕ} (h37 : j ≠ 37) (h38 : j ≠ 38) :
    chalsAJ8Z δ χ j = chalsAJ8 δ χ j := by
  simp only [chalsAJ8Z, if_neg h37, if_neg h38]

/-- FinalJ8's `hchA`: the rewired vector agrees with `chalsMJ8` at the handle leaves. -/
theorem chalsAJ8Z_agree (χ : Coins frameJ8 K) : ∀ j, 33 ≤ j → j ≤ 36 → chalsAJ8Z δ χ j = chalsMJ8 δ χ j := by
  intro j h1 h2
  rw [chalsAJ8Z_of_ne δ χ (by omega) (by omega)]
  exact chalsAJ8_agree δ χ j h1 h2

/-- The atom table's coin is still `y`. -/
theorem chalsAJ8Z_y (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 2) (chalsAJ8Z δ χ 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2) := by
  rw [chalsAJ8Z_of_ne δ χ (by omega) (by omega), chalsAJ8Z_of_ne δ χ (by omega) (by omega)]
  exact chalsAJ8_y δ χ

/-- Leaves `0 / 1` (the atom walk's `walkEvent` coins) are unchanged. -/
theorem chalsAJ8Z_01 (χ : Coins frameJ8 K) :
    chalsAJ8Z δ χ 0 = chalsAJ8 δ χ 0 ∧ chalsAJ8Z δ χ 1 = chalsAJ8 δ χ 1 :=
  ⟨chalsAJ8Z_of_ne δ χ (by omega) (by omega), chalsAJ8Z_of_ne δ χ (by omega) (by omega)⟩

/-- **The rewired vector carries the validity coins** (`ChalsOK … γ′ ρ′ 11` reads leaves `5, 7, 11..32`). -/
theorem chalsAJ8Z_ok (χ : Coins frameJ8 K) :
    ChalsOK δ (chalsAJ8Z δ χ) (Quad.mk _ (χ c4) (χ c6)) (Quad.mk _ (χ c5) (χ c7)) 11 := by
  have h := chalsAJ8_ok δ χ
  refine ⟨?_, fun i hi => ?_⟩
  · rw [chalsAJ8Z_of_ne δ χ (by omega) (by omega), chalsAJ8Z_of_ne δ χ (by omega) (by omega)]; exact h.1
  · rw [chalsAJ8Z_of_ne δ χ (by omega) (by omega), chalsAJ8Z_of_ne δ χ (by omega) (by omega)]; exact h.2 i hi

theorem chalsAJ8Z_zAt (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 37) (chalsAJ8Z δ χ 38) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) := by
  simp [chalsAJ8Z]

end Vectors

end

end Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
