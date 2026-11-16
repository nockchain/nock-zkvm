/-
  Nock/NockVMROM/Thm54/P8Core/Batch509Thm54WrapSpecialize.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch509Thm54WrapSpecialize`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch509Thm54WrapSpecialize.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.MemoryTopoBetaFree
import Nock.NockVMROM.Thm54.P8Core.MemoryWalkDeployed
import Nock.NockVMROM.Thm54.P8Core.WrapFixesVcomp
import Nock.NockVMROM.Thm54.P8Core.WrapMemoryConjuncts
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Nock.RedTeam.Batch509

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.WrapFixesVcomp
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open MonolithicRAP
open scoped Polynomial

theorem mapNTree_buildTF {α β : Type*} (f : α → β)
    (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → α) (h i : ℕ) :
    mapNTree f (buildTF kroots fo lbl h i) =
      buildTF kroots fo (fun j => f (lbl j)) h i := by
  suffices ∀ d i, h - i = d →
      mapNTree f (buildTF kroots fo lbl h i) =
        buildTF kroots fo (fun j => f (lbl j)) h i from this (h - i) i rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro i hi
    rw [buildTF, mapNTree, buildTF]
    refine congrArg (NTree.node (f (lbl i))) ?_
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    have hmem : j.1 ∈ childIdxsF kroots fo h i := j.property
    have hlt : h - j.1 < d := by
      simp only [childIdxsF, List.mem_filter, decide_eq_true_eq, List.mem_range'] at hmem
      omega
    exact ih (h - j.1) hlt j.1 rfl

theorem mapNTree_reconForest {α β : Type*} (f : α → β)
    (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → α) (h : ℕ) :
    (reconForest kroots fo lbl h).map (mapNTree f) =
      reconForest kroots fo (fun j => f (lbl j)) h := by
  simp only [reconForest, List.map_map]
  apply List.map_congr_left
  intro _ _
  exact mapNTree_buildTF f kroots fo lbl h _

theorem reconForest_eq_of_lbl {α : Type*} (kroots : ℕ) (fo : ℕ → ℕ)
    {lbl lbl' : ℕ → α} (h : ℕ) (heq : ∀ i, lbl i = lbl' i) :
    reconForest kroots fo lbl h = reconForest kroots fo lbl' h := by
  simp [reconForest, funext heq]

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (h : TracesWalkHyps P Qc₀ Qm₀ c)
  (hz : nprSeed c.1 ≠ 0)

/-- `vmem_padding_mem_zero` on the β-free conjunct: padding rows' `eqBlk` already zeroes the
record (M′; `Vmem` was read only through `eqBlk`). -/
theorem eqBlk_padding_mem_zero {inp : MemoryTable.Inputs K} {p : MemoryTable.Pub K}
    (heq : eqBlk inp p) (hpad : memoryMemRecKind p.st = .padding) :
    p.mem = MemRec.zero := by
  cases hst : p.st with
  | decompose =>
    simp only [eqBlk, hst] at heq
    exact heq.2.2.2
  | halt =>
    simp only [eqBlk, hst] at heq
    exact heq.2.2.2.2.2.2
  | read_root =>
    simp [memoryMemRecKind, hst] at hpad
  | verify_child =>
    simp [memoryMemRecKind, hst] at hpad

/-- Per-row `FmemTopo` at `lblM` from the β-free whole-forest topology (M′; was `Fmem` from the
production `MemoryExactTopology`). -/
theorem fmem_of_topology
    (htop : ∀ t ∈ (execOfTraces P Qc₀ Qm₀ c h).memoryForest,
      RVTWithArity (MemoryTopoBetaFree.FmemTopo (K := K)) t)
    (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ P.optimized.family.problem.cfg.memRows) :
    MemoryTopoBetaFree.FmemTopo (lblM P Qm₀ c i)
      (fun j => (buildTF P.optimized.family.problem.cfg.kMem
        (foM P Qm₀ c) (lblM P Qm₀ c)
        P.optimized.family.problem.cfg.memRows i).childLabel j) := by
  have hk := MemoryWalkDeployed.kMem_pos P
  have hbfs := bfsForest_reconForest
    P.optimized.family.problem.cfg.kMem (foM P Qm₀ c) (lblM P Qm₀ c)
    P.optimized.family.problem.cfg.memRows hk h.sfMemory h.validMemory
  have hnode :
      buildTF P.optimized.family.problem.cfg.kMem (foM P Qm₀ c)
          (lblM P Qm₀ c) P.optimized.family.problem.cfg.memRows i ∈
        bfsForest (execOfTraces P Qc₀ Qm₀ c h).memoryForest := by
    change buildTF P.optimized.family.problem.cfg.kMem (foM P Qm₀ c)
        (lblM P Qm₀ c) P.optimized.family.problem.cfg.memRows i ∈
      bfsForest (reconForest P.optimized.family.problem.cfg.kMem
        (foM P Qm₀ c) (lblM P Qm₀ c)
        P.optimized.family.problem.cfg.memRows)
    rw [hbfs]
    refine List.mem_map.mpr ⟨i, ?_, rfl⟩
    exact List.mem_range'.mpr ⟨i - 1, by omega, by omega⟩
  obtain ⟨root, hroot, hin⟩ := (mem_bfsForest _ _).mp hnode
  have hrvt : RVT (MemoryTopoBetaFree.FmemTopo (K := K)) root := (htop root hroot).rvt
  have hFcon := (RVT_iff_forall_InTree (MemoryTopoBetaFree.FmemTopo (K := K)) _).1 hrvt _ hin
  simpa [Fcon, buildTF_label] using hFcon.1

theorem lblM_off_eq_root (i : ℕ)
    (hoff : ¬ (1 ≤ i ∧ i ≤ P.optimized.family.problem.cfg.memRows)) :
    lblM P Qm₀ c i = lblM P Qm₀ c 1 := by
  have hN := P.optimized.family.problem.cfg.memRows_pos
  unfold lblM
  by_cases hi : i - 1 < P.optimized.family.problem.cfg.memRows
  · have : i = 0 := by omega
    subst i
    rfl
  · rw [dif_neg hi, dif_pos (by omega : 1 - 1 < P.optimized.family.problem.cfg.memRows)]

end

end Nock.RedTeam.Batch509
