/-
  Nock/RedTeam/Batch959Thm54HonestMemoryTiling.lean

  `memoryTilingEventOf Qm = memoryTilingEvent (foOfMem (memoryBaseEnv Qm)) kMem M` is
  `{ω | αM^(kMem + Sf fo M) = αM^M ∧ kMem + Sf fo M ≠ M}`: EMPTY once the committed fanout column
  tiles.  At the canonical memory trace the base selectors are the exec row's one-hot state
  (`OptimizedCanonicalHostileLists.canonical_base_sel`, `encodedRowAt_base_state`), so
  `foOfMem (i+1) = fanoutMem st_i = foCol memoryWalkRows (i+1)` (`foCol_eq_fanout`, from the
  package's own `MemoryWalkLabelObligations`), and the exec memory forest tiles
  (`MemoryWalkLabelCanonical.exact_memory_tiling`, unconditional).

  Status: **proved** (honest-trace identity), for every coin, at EVERY package (no hypothesis).
-/
import Nock.RedTeam.Batch909Thm54R4HonestInstance
import Nock.NockVMROM.Thm54.MemoryWalkLabelCanonical
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch959

open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists
open Nock.NockVMROM.Thm54.OptimizedMemoryCodec

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The canonical memory row's decoded state is the exec row's state (every package). -/
theorem memRowState_honest (i : Fin P.optimized.family.problem.cfg.memRows) :
    WalkTilingEvents.memRowStateOf (P.memoryBaseEnv (canonicalMemoryTrace P) i) =
      (P.optimized.family.problem.exec.memoryPubAt i).st := by
  have hsel : ∀ j : Fin 4, (P.memoryBaseEnv (canonicalMemoryTrace P) i).trace j =
      stateSelector (F := F) (P.optimized.family.problem.exec.memoryPubAt i).st j := by
    intro j
    exact (canonical_base_sel P i ⟨j.val, by omega⟩).trans (encodedRowAt_base_state P i j)
  have h0 := hsel 0
  have h1 := hsel 1
  have h2 := hsel 2
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  unfold WalkTilingEvents.memRowStateOf
  rw [h0, h1, h2]
  cases (P.optimized.family.problem.exec.memoryPubAt i).st <;> simp [stateSelector, stateIndex]

/-- The committed memory fanout column at the canonical trace is the exec walk's `foCol`. -/
theorem foOfMem_honest (i : ℕ) (hi1 : 1 ≤ i) (hiM : i ≤ P.optimized.family.problem.cfg.memRows) :
    WalkTilingEvents.foOfMem (P.memoryBaseEnv (canonicalMemoryTrace P)) i =
      Walk.foCol P.optimized.family.memoryWalkRows i := by
  have hlt : i - 1 < P.optimized.family.problem.cfg.memRows := by omega
  unfold WalkTilingEvents.foOfMem
  rw [dif_pos ⟨hi1, hlt⟩, memRowState_honest]
  have h := MemoryWalkLabelCanonical.foCol_eq_fanout (R := P.optimized.family)
    P.optimized.memoryProduction.obligations.2.2.2.2 ⟨i - 1, hlt⟩
  have hi : ((⟨i - 1, hlt⟩ : Fin _) : ℕ) + 1 = i := by simp; omega
  rw [hi] at h
  exact h.symm

/-- **Component 7 at the honest instance**: the memory tiling event is empty at the canonical
trace, for every coin, at every package. -/
theorem memoryTiling_empty_honest :
    P.memoryTilingEventOf (canonicalMemoryTrace P) = ∅ := by
  apply WalkTilingEvents.memoryTilingEvent_empty_of_tiling
  rw [WalkForestPrefixAlphaEvents.Sf_congr_on (fun i h1 h2 => foOfMem_honest P i h1 h2)]
  exact MemoryWalkLabelCanonical.exact_memory_tiling (R := P.optimized.family)

theorem tileM_honest : P.honestTuple.1 ∉ P.memoryTilingEventOf (canonicalMemoryTrace P) := by
  rw [memoryTiling_empty_honest P]
  exact Finset.notMem_empty _

end

end Nock.RedTeam.Batch959

#print axioms Nock.RedTeam.Batch959.memRowState_honest
#print axioms Nock.RedTeam.Batch959.memoryTiling_empty_honest
#print axioms Nock.RedTeam.Batch959.tileM_honest
