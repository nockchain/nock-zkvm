/-
  Nock/NockVMROM/Thm54/VclL/Chips/HonestMemQ.lean

  **The honest trace polynomials** — interpolation of a
  column function at the verifier's row nodes, and what the chip's row environment reads off it.

  `honestQ nodes col w : Fin w → F[X]` interpolates column `j` through the values `fullCol col j i`
  at node `i` (columns `0`, `1` are the endpoint masks, so `BindsPreprocessing` holds by
  construction: `honestQ_zero`, `honestQ_one`); `col : ℕ → Fin n → F` supplies the rest, and is the
  instance's EXPLICIT construction (a function of the run and the coins, never a choice).
  `env_trace` / `env_traceNext`: the chip environment at row `i` reads `fullCol j i`, and under row
  adjacency the next row reads `fullCol j (i+1)`.  `gather_trace`: the `𝕂`-role environment
  `gatherEnv b (col0..)` reads the `𝕂`-value whose coordinates sit in the role's three columns.
  `honest_trace_cols_*` (`stagedness`): a column whose function reads only data `D` yields a
  polynomial that depends on `D` alone (`honestQ_congr`).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemBridge

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Module
open scoped Polynomial

noncomputable section

section Q

variable {F : Type} [Field F] {n : ℕ} (hn : 0 < n)

/-- The full column function: columns `0`, `1` are the first / last-row masks, the rest is `col`. -/
def fullCol (col : ℕ → Fin n → F) (j : ℕ) (i : Fin n) : F :=
  if j = 0 then (if (i : ℕ) = 0 then 1 else 0)
  else if j = 1 then (if i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0)
  else col j i

/-- **The honest trace**: column `j` interpolates `fullCol col j` at the row nodes. -/
def honestQ (nodes : Fin n → F) (col : ℕ → Fin n → F) (w : ℕ) : Fin w → F[X] :=
  fun j => Lagrange.interpolate Finset.univ nodes (fullCol hn col j)

theorem honestQ_eval (nodes : Fin n → F) (hinj : Function.Injective nodes) (col : ℕ → Fin n → F)
    {w : ℕ} (j : Fin w) (i : Fin n) :
    (honestQ hn nodes col w j).eval (nodes i) = fullCol hn col j i :=
  Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)

theorem honestQ_zero (nodes : Fin n → F) (col : ℕ → Fin n → F) {w : ℕ} (hw : 0 < w) :
    honestQ hn nodes col w ⟨0, hw⟩ = firstRowMask nodes := by
  simp [honestQ, fullCol, firstRowMask]

theorem honestQ_one (nodes : Fin n → F) (col : ℕ → Fin n → F) {w : ℕ} (hw : 1 < w) :
    honestQ hn nodes col w ⟨1, hw⟩ = lastRowMask hn nodes := by
  simp [honestQ, fullCol, lastRowMask]

/-- **Stagedness**: the polynomial of column `j` depends only on the column function's values. -/
theorem honestQ_congr (nodes : Fin n → F) (col col' : ℕ → Fin n → F) (w : ℕ) (j : Fin w)
    (h : col j = col' j) : honestQ hn nodes col w j = honestQ hn nodes col' w j := by
  have : fullCol hn col j = fullCol hn col' j := by
    funext i; simp only [fullCol, h]
  simp only [honestQ, this]

/-- The chip environment's current row reads the column function. -/
theorem env_trace (nodes : Fin n → F) (hinj : Function.Injective nodes) (col : ℕ → Fin n → F)
    {w : ℕ} (ω : F) (cv pv : ℕ → F) (i : Fin n) {j : ℕ} (hj : j < w) :
    (Reify.envOfTrace (honestQ hn nodes col w) ω (nodes i) cv pv).trace j = fullCol hn col j i := by
  simp only [Reify.envOfTrace, hj, dif_pos]
  exact honestQ_eval hn nodes hinj col ⟨j, hj⟩ i

/-- Under adjacency the next row reads row `i + 1`. -/
theorem env_traceNext (nodes : Fin n → F) (hinj : Function.Injective nodes) (col : ℕ → Fin n → F)
    {w : ℕ} (ω : F) (cv pv : ℕ → F)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) {j : ℕ} (hj : j < w) :
    (Reify.envOfTrace (honestQ hn nodes col w) ω (nodes i) cv pv).traceNext j =
      fullCol hn col j ⟨(i : ℕ) + 1, hi⟩ := by
  simp only [Reify.envOfTrace, hj, dif_pos]
  rw [mul_comm, ← hadj i hi]
  exact honestQ_eval hn nodes hinj col ⟨j, hj⟩ _

end Q

section Gather
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **The `𝕂`-role environment reads the `𝕂`-value whose coordinates fill the role's columns.** -/
theorem gather_trace {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ) (envF : Env F)
    (r : ℕ) (v : K) (hv : ∀ k : Fin e, envF.trace (col0 .traceCur r + (k : ℕ)) = coord b v k) :
    (gatherEnv b col0 envF).trace r = v := by
  simp only [gatherEnv, hv, coord]
  exact b.sum_repr v

theorem gather_traceNext {e : ℕ} (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ) (envF : Env F)
    (r : ℕ) (v : K) (hv : ∀ k : Fin e, envF.traceNext (col0 .traceNext r + (k : ℕ)) = coord b v k) :
    (gatherEnv b col0 envF).traceNext r = v := by
  simp only [gatherEnv, hv, coord]
  exact b.sum_repr v

end Gather

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
