/-
  Nock/NockVMROM/Thm54/P8Core/OptimizedHostileConfiguration.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.OptimizedHostileConfiguration`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/OptimizedHostileConfiguration.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.OptimizedHostileTimestamps
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54

namespace OptimizedHostileConfiguration

open scoped Classical Polynomial
open Nock
open Nock.Framework
open Nock.Reified
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedComputeCorrectedFinal
open OptimizedComputeHostileAccumulator
open OptimizedMemoryHostileAccumulator
open OptimizedHostileTimestamps
open OptimizedHostileIOAssembly
open OptimizedStrictFullPackage
open OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
open OptimizedComputeSemanticRealization
open OptimizedComputeFinalTrace
open ConcreteStrictPackage
open Module
set_option linter.unusedSectionVars false

noncomputable section

/-- **`hchar` from `StateTagChar`.**  Weaker than `11 < ringChar K` (holds in characteristic
zero too).  `StateTagChar` is injectivity of `Nat.cast` on `{0,…,11}`; `hchar` is the same
injectivity at the point `1`. -/
theorem hchar_of_stateTagChar {K : Type} [Field K] (h : NodeEncoding.StateTagChar K) :
    ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1 := by
  intro n hn heq
  exact h hn (by simp : (1 : ℕ) ≤ 11) (heq.trans (Nat.cast_one (R := K)).symm)

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- **`11 < ringChar K` from the package.**  `stateTagChar` plus `1 < q = ringChar K`
(`q_gt_one`, `q_eq_ringChar`) is `NodeEncoding.ringChar_gt_eleven_of_stateTagChar`. -/
theorem eleven_lt_ringChar_of_package
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb) : 11 < ringChar K :=
  NodeEncoding.ringChar_gt_eleven_of_stateTagChar P.stateTagChar
    (by have hq := P.q_gt_one; rw [P.q_eq_ringChar] at hq; omega)

/-- **`hchar` from the package field `stateTagChar` — no extra hypothesis.** -/
theorem hchar_of_package (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1 :=
  hchar_of_stateTagChar P.stateTagChar

variable (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Slot `0` is always active (`sampledActive 0 = 1`), so every row emits at least one
request.  No acceptance, no `hchar` -/
theorem rowRequests_length_pos (env : CorrectedFinalTypedEnv F K) :
    1 ≤ (rowRequests env).length := by
  have hmem : (0 : Fin 3) ∈ List.finRange 3 := List.mem_finRange 0
  have h0 : activeMask env 0 = 1 := activeMask_zero env
  have : rowRecord env 0 ∈ rowRequests env := by
    unfold rowRequests
    exact List.mem_filterMap.mpr ⟨0, hmem, by simp [h0]⟩
  exact Nat.succ_le_of_lt (List.length_pos_of_mem this)

/-- **`1 ≤ |hostileRequests|` for every trace.**  `compRows_pos` plus
`rowRequests_length_pos`.  No acceptance. -/
theorem hostileRequests_length_pos
    (Qc : Fin P.computeChip.rap.w → F[X]) :
    1 ≤ (P.hostileRequests Qc).length := by
  have i0 : Fin P.optimized.family.problem.cfg.compRows :=
    ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩
  have hrow : 1 ≤ (rowRequests (rowEnv P Qc i0)).length :=
    rowRequests_length_pos (rowEnv P Qc i0)
  rw [← hostileRequests_eq_package]
  unfold OptimizedComputeHostileAccumulator.hostileRequests
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  have hle : (rowRequests (rowEnv P Qc i0)).length ≤
      ∑ i : Fin P.optimized.family.problem.cfg.compRows,
        (rowRequests (rowEnv P Qc i)).length :=
    Finset.single_le_sum
      (f := fun i => (rowRequests (rowEnv P Qc i)).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i0)
  exact hrow.trans hle

end

end OptimizedHostileConfiguration

end Nock.NockVMROM.Thm54
