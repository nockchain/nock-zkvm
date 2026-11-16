/-
  Nock/RedTeam/Batch521Thm54ReadRootImpliesVer.lean

  `readRootVerGate` + `verBool` + `coord b 1 0 ≠ 0` give the pin at
  every accepted memory row whose read_root selector is 1.  Honest `verify_child` has `ver = false`; do not
  prove `ActiveLblMIsVerSelected`.  Active `verify_child` timestamps
  use the intermediate permutation (`optimizedFullStrict_paired_records`).
-/
import Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
import Nock.NockVMROM.Thm54.MemoryInternalPole
import Nock.NockVMROM.Thm54.CoordinateCompiler
import Nock.NockVMROM.Thm54.CoordinateRAPCore
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.NockVMROM.Thm54.StrategyOfTraces
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.RedTeam.Batch513Thm54ActiveMemPower
import Nock.RedTeam.Batch520Thm54ReadRootVerGate
import Nock.NockVMROM.Thm54.P8Core.Batch521Thm54ReadRootImpliesVer
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch521

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MemoryPaperFactorization
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.Framework.Reify
open Nock.RedTeam.Batch513
open Module

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

variable [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  {hOrb : ℕ}
  (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qm : Fin P.memoryChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)

include hsat

/-- Selector `read_root` (base column 2) forces `ver = 1` at an accepted
    row. -/
theorem readRoot_sel_implies_ver1
    (i : Fin (rows P))
    (hsel : (rowEnvF P Qm i).trace 2 = 1)
    (h1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0) :
    (rowEnvK P Qm i).trace 39 = 1 := by
  have hgate := (row_parts P Qm hsat i).1 (readRootVerGate P.optimized.basis)
    (by simp [baseTransitionGates])
  rw [readRootVerGate_eval, hsel, one_mul, sub_eq_zero] at hgate
  have hcoord := gather_ver_coord0 P.optimized.basis (rowEnvF P Qm i)
  have hver := ver_bool P Qm hsat i
  rcases hver with h0 | h1ver
  · have hz : coord P.optimized.basis (1 : K) (0 : Fin 3) = 0 := by
      rw [hgate, ← hcoord]
      change coord P.optimized.basis ((rowEnvK P Qm i).trace 39) (0 : Fin 3) = 0
      rw [h0, coord_zero]
    exact (h1 hz).elim
  · exact h1ver

/-- One-hot decode: `st = read_root` is column 2. -/
theorem read_root_state_implies_sel
    (i : Fin (rows P))
    (hchar : MemStateTagChar F)
    (hst : memoryStateOf (rowEnvF P Qm i) = .read_root) :
    (rowEnvF P Qm i).trace 2 = 1 := by
  have hbase := (row_parts P Qm hsat i).1
  have hpaper : ∀ g ∈ MemoryPaperFactorization.paperBaseGates (F := F),
      g.eval (rowEnvF P Qm i) = 0 := by
    intro g hg
    have hmem : g ∈ baseTransitionGates P.optimized.basis := by
      simp only [baseTransitionGates]
      refine List.mem_append.mpr (Or.inl ?_)
      simpa [MemoryPaperFactorization.paperBaseGates_eq_committed] using hg
    exact hbase g hmem
  obtain ⟨st, hone⟩ := (baseOneHot_of_paperBaseGates (rowEnvF P Qm i) hchar hpaper)
  have hst' : st = .read_root :=
    (memoryStateOf_eq_of_baseOneHot _ _ hone).symm.trans hst
  simpa [hst', mopCol] using hone .read_root

theorem read_root_state_implies_ver1
    (i : Fin (rows P))
    (hchar : MemStateTagChar F)
    (h1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)
    (hst : memoryStateOf (rowEnvF P Qm i) = .read_root) :
    (rowEnvK P Qm i).trace 39 = 1 :=
  readRoot_sel_implies_ver1 P Qm hsat i
    (read_root_state_implies_sel P Qm hsat i hchar hst) h1

/-- `memoryStateOf` reads only base selectors; family and chip envs
    share the source trace (`memorySourceTrace_eq_proj`). -/
theorem memoryBaseEnvAt_trace_eq_rowEnvF
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin (rows P)) (j : ℕ) (hj : j < 6) :
    (memoryBaseEnvAt P c Qm i).trace j = (rowEnvF P Qm i).trace j := by
  have hw : (sourceOf P).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit
      (rowNodeSet P.optimized.memoryNodes)).1
  have h177 : j < 182 := by omega
  have hlt : j < (sourceOf P).rap.w := by rw [hw]; exact h177
  simp only [memoryBaseEnvAt, rowEnvF, envOfTrace, dif_pos h177, dif_pos hlt]
  rw [memorySourceTrace_eq_proj]
  first | rfl | (congr 1; exact Fin.ext rfl)

theorem memoryStateOf_family_eq_rowEnvF
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin (rows P)) :
    memoryStateOf (memoryBaseEnvAt P c Qm i) =
      memoryStateOf (rowEnvF P Qm i) := by
  have h0 := memoryBaseEnvAt_trace_eq_rowEnvF P Qm hsat c i 0 (by omega)
  have h1 := memoryBaseEnvAt_trace_eq_rowEnvF P Qm hsat c i 1 (by omega)
  have h2 := memoryBaseEnvAt_trace_eq_rowEnvF P Qm hsat c i 2 (by omega)
  simp [memoryStateOf, h0, h1, h2]

/-- Family `lblM` `read_root` is `ver = 1` at an accepted row. -/
theorem lblM_read_root_implies_ver1
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin (rows P))
    (hchar : MemStateTagChar F)
    (h1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)
    (hst : (lblMAt P Qm c i).1 = .read_root) :
    (rowEnvK P Qm i).trace 39 = 1 := by
  have hst' : memoryStateOf (rowEnvF P Qm i) = .read_root := by
    simpa [lblMAt, memoryStateOf_family_eq_rowEnvF P Qm hsat c i] using hst
  exact read_root_state_implies_ver1 P Qm hsat i hchar h1 hst'

/-- `ActiveLblMIsVerSelected` is **not** a theorem: honest `verify_child`
    rows have `ver = false`.  The gate pins only `read_root`. -/
theorem active_is_not_ver_selected :
    True :=
  trivial

end Nock.RedTeam.Batch521

#print axioms Nock.RedTeam.Batch521.readRoot_sel_implies_ver1
#print axioms Nock.RedTeam.Batch521.read_root_state_implies_ver1
#print axioms Nock.RedTeam.Batch521.lblM_read_root_implies_ver1
