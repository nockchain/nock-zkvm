/-
  NockvmE2E/Exec/ProverLink.lean
  The prover's Mathlib-free Tip5 (`Tip5Core`) is the kernel-checked `Tip5` (20/20 vectors): definitional equality by `rfl`.
-/
import NockvmE2E.Exec.Tip5
import NockvmE2E.Exec.Tip5Core
set_option autoImplicit false

namespace NockvmE2E.Exec
theorem tip5Core_permute : Tip5Core.permute = Tip5.permute := rfl
theorem tip5Core_hash10 : Tip5Core.hash10 = Tip5.hash10 := rfl
theorem a1 : Tip5Core.pad = Tip5.pad := rfl
theorem a2 : Tip5Core.montify = Tip5.montify := rfl
theorem ab : Tip5Core.absorbBlock = Tip5.absorbBlock := rfl
theorem a3 : Tip5Core.absorbFuel = Tip5.absorbFuel := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih => funext s l; simp only [Tip5Core.absorbFuel, Tip5.absorbFuel, ih, ab, Tip5Core.RATE, Tip5.RATE]
theorem a4 : Tip5Core.digestOf = Tip5.digestOf := rfl
theorem a5 : Tip5Core.initVar = Tip5.initVar := rfl
theorem tip5Core_hashVarlen : Tip5Core.hashVarlen = Tip5.hashVarlen := by
  funext x
  simp only [Tip5Core.hashVarlen, Tip5.hashVarlen, a1, a2, a3, a4, a5, Tip5Core.RATE, Tip5.RATE]
theorem s1 : ∀ s t d, Tip5Core.absorb s t d = Tip5.absorb s t d := by
  intro s t d; simp only [Tip5Core.absorb, Tip5.absorb, tip5Core_hashVarlen, Tip5Core.tAbs, Tip5.tAbs]
theorem s2 : ∀ s n, Tip5Core.squeeze s n = Tip5.squeeze s n := by
  intro s n; simp only [Tip5Core.squeeze, Tip5.squeeze, tip5Core_hashVarlen, Tip5Core.tSqz, Tip5.tSqz]
end NockvmE2E.Exec
