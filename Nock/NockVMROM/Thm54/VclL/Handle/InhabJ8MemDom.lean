/-
  Nock/NockVMROM/Thm54/VclL/Handle/InhabJ8MemDom.lean

  **The row domains and the handle map** of THE inhabitant
  `*[[0 0] [0 1]] = [0 0]`.

  * `ωM hdvd`: an element of exact order `3·2 = 6` in `ZMod p`, from `3 * 2 ^ 1 ∣ p - 1` (`orbitM`, height `1`).
  * `nodesM n i = ω^i`: injective for `n ≤ 6`, adjacent (`nodes (i+1) = nodes i * ω`).
  * `H0 p`: the handle map (small atom `v ↦ (0, v)`, big atom `↦ (2, 0)`, cell `↦ (1, serial)` with serial `1`
    for `f0 = [0 1]` and `0` otherwise, i.e. `s0 = [0 0]` is cell row `0`, `f0` cell row `1`); `hdlOK_H0`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base
import Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemDom

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base

noncomputable section

section Dom
variable {p : ℕ} [Fact p.Prime]

/-- An element of exact order `6 = 3·2^1`. -/
def ωM (hdvd : 3 * 2 ^ 1 ∣ p - 1) : ZMod p :=
  Classical.choose (exists_zmod_generator_of_dvd_sub_one p (3 * 2 ^ 1) hdvd)

theorem ωM_order (hdvd : 3 * 2 ^ 1 ∣ p - 1) : orderOf (ωM hdvd) = 3 * 2 ^ 1 :=
  Classical.choose_spec (exists_zmod_generator_of_dvd_sub_one p (3 * 2 ^ 1) hdvd)

/-- **The memory orbit** (`e = 3`, height `1`, `β = 1`). -/
def orbitM (hdvd : 3 * 2 ^ 1 ∣ p - 1) : StrictOrbitDomain (ZMod p) 3 1 where
  ω := ωM hdvd
  βcoset := 1
  e_pos := by norm_num
  h_pos := le_rfl
  order_ω := ωM_order hdvd
  βcoset_ne_zero := one_ne_zero

/-- The row nodes `ω^i`. -/
def nodesM (hdvd : 3 * 2 ^ 1 ∣ p - 1) (n : ℕ) : Fin n → ZMod p := fun i => ωM hdvd ^ (i : ℕ)

theorem nodesM_inj (hdvd : 3 * 2 ^ 1 ∣ p - 1) (n : ℕ) (hn : n ≤ 6) :
    Function.Injective (nodesM hdvd n) := by
  intro i j hij
  have ho : orderOf (ωM hdvd) = 6 := by rw [ωM_order]; norm_num
  have hpos : 0 < orderOf (ωM hdvd) := by rw [ho]; norm_num
  have h := pow_injOn_Iio_orderOf (x := ωM hdvd)
    (show (i : ℕ) ∈ Set.Iio (orderOf (ωM hdvd)) by rw [ho]; exact lt_of_lt_of_le i.isLt hn)
    (show (j : ℕ) ∈ Set.Iio (orderOf (ωM hdvd)) by rw [ho]; exact lt_of_lt_of_le j.isLt hn) hij
  exact Fin.ext h

theorem nodesM_adj (hdvd : 3 * 2 ^ 1 ∣ p - 1) (n : ℕ) :
    ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      nodesM hdvd n ⟨(i : ℕ) + 1, hi⟩ = nodesM hdvd n i * (orbitM hdvd).ω := by
  intro i hi
  show ωM hdvd ^ ((i : ℕ) + 1) = ωM hdvd ^ (i : ℕ) * ωM hdvd
  exact pow_succ _ _

end Dom

/-! ## The handle map -/

/-- **`H0`**: small atom `v ↦ (0, v)`, big atom `↦ (2, 0)`, cell `↦ (1, s)` with `s` the cell's row index in the
cell table (`f0 ↦ 1`, every other cell — in particular `s0` — `↦ 0`). -/
def H0 (p : ℕ) : Noun → ℕ × ℕ
  | .atom v => if v < p then (0, v) else (2, 0)
  | .cell a b => (1, if Noun.cell a b = f0 then 1 else 0)

theorem hdlOK_H0 (p : ℕ) : HonestCompX.HdlOK p (H0 p) where
  small v hv := by simp [H0, hv]
  big v hv := by simp [H0, not_lt.mpr hv]
  cell a b := rfl

theorem hdlOK_H0_ring {p : ℕ} [Fact p.Prime] : HonestCompX.HdlOK (ringChar (ZMod p)) (H0 p) := by
  rw [ZMod.ringChar_zmod_n]; exact hdlOK_H0 p

theorem H0_s0 (p : ℕ) : H0 p s0 = (1, 0) := by simp [H0, s0, f0]
theorem H0_f0 (p : ℕ) : H0 p f0 = (1, 1) := by simp [H0, f0]

end

end Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemDom
