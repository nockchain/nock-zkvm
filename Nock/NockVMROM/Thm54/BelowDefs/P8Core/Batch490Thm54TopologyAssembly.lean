/-
  Nock/NockVMROM/Thm54/BelowDefs/P8Core/Batch490Thm54TopologyAssembly.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/P8Core/Batch490Thm54TopologyAssembly.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.ComputeWalkRootEvents
import Nock.NockVMROM.Thm54.MemoryTopoBetaFree
import Nock.WalkPrefix

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch490

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.Framework
open Nock.Framework.Reify
open MonolithicRAP

section AlphaEventEq

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- After `cur 1 = root`, the prefix `α`-event is `alphaBadOf` of `rootDiffP`. -/
theorem walkPrefixAlphaEvent_eq_alphaBadOf
    {cur : ℕ → K} {chld : ℕ → ℕ → K} {fo : ℕ → ℕ} {root : K} {h : ℕ}
    (hcur : cur 1 = root) :
    walkPrefixAlphaEvent cur chld fo h =
      alphaBadOf (rootDiffP cur chld fo root h) := by
  have hQ : nodeQueueP (fun _ => root) chld fo h = nodeQueueP cur chld fo h :=
    nodeQueueP_const_root_eq hcur h
  by_cases hBFT : IsFullBFT cur chld fo h
  · have hD0 : rootDiffP cur chld fo root h = 0 := by
      unfold rootDiffP
      rw [hQ, hBFT, sub_self]
    simp [walkPrefixAlphaEvent, alphaBadOf, hBFT, hD0]
  · have hDne : rootDiffP cur chld fo root h ≠ 0 := by
      intro h0
      apply hBFT
      unfold IsFullBFT
      unfold rootDiffP at h0
      rw [hQ] at h0
      exact sub_eq_zero.mp h0
    apply Finset.ext
    intro a
    simp only [walkPrefixAlphaEvent, alphaBadOf, hBFT, hDne, ↓reduceIte,
      Finset.mem_filter, Finset.mem_univ, true_and]
    unfold rootDiffP
    rw [eval_sub, hQ]
    constructor
    · intro he
      rw [he, sub_self]
    · intro he
      exact sub_eq_zero.mp he

end AlphaEventEq

end Nock.RedTeam.Batch490
