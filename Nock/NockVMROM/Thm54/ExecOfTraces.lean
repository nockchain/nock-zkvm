/-
  Nock/NockVMROM/Thm54/ExecOfTraces.lean

  375 — row labels off `(Qc, Qm)` and the trace-built
  `ExactExecution`.

  Tree structure is `Walk.reconTree` / `Walk.reconForest`
  (`Walk.lean::reconForest`, `::bfsForest_reconForest`, `::reconTree_labels`).
  Walk-tiling `hSf` / `hvalid` are hypotheses of `execOfTraces` (brief step 2:
  close from deployed walk gates in step 5; do not fake them).

  Paper: the paper (inverse-BFS), `:1450` (Thm 5.4),
  `:1690` (`sfTriple`), `:2031` (`memCell`).
-/
import Nock.Walk
import Nock.NockVM
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.DeployedComputeRows
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.StrategyOfTraces
import Nock.NockVMROM.Thm54.P8Core.ExecOfTraces
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.ExecOfTraces

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## Row labels off the traces (`Qc` / `Qm`) -/

/-- Child label `sfTriple`-derived from the parent `Qc` row. -/
def clabC
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i j : ℕ) :
    Option (State × DTcomp K) :=
  let parent := lblC P Qc c i
  if hj : j < foC P Qc c i then
    have hj3 : j < 3 :=
      Nat.lt_of_lt_of_le hj ((comp_stateSep (K := K)).fanout_le parent.1)
    let trip := sfTriple parent.2.2.1 ⟨j, hj3⟩
    some (parent.1,
      (parent.2.1,
        { parent.2.2.1 with s := trip.1, f := trip.2.1, e := trip.2.2 },
        parent.2.2.2))
  else
    none

/-- Child label `memCell`-derived from the parent `Qm` row. -/
def clabM
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i j : ℕ) :
    Option (MState × DTmem K) :=
  let parent := lblM P Qm c i
  if hj : j < foM P Qm c i then
    have hj2 : j < 2 :=
      Nat.lt_of_lt_of_le hj ((mem_stateSep (K := K)).fanout_le parent.1)
    let cell := memCell parent ⟨j, hj2⟩
    some (parent.1, (parent.2.1, { parent.2.2 with pt := cell }))
  else
    none

theorem lblC_succ
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    lblC P Qc c (i.val + 1) = lblCAt P Qc c i := by
  have h : (i.val + 1) - 1 < P.optimized.family.problem.cfg.compRows := by
    simpa [Nat.add_sub_cancel] using i.isLt
  simp [lblC, h]

/-! ## `cfgOfTraces` / `execOfTraces` -/

theorem cfgOfTraces_z
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (cfgOfTraces P Qc Qm c).challenges.z = nprSeed c.1 :=
  rfl

theorem execOfTraces_computeRows
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) :
    (execOfTraces P Qc Qm c h).computeRows =
      (List.range' 1 (cfgOfTraces P Qc Qm c).compRows).map (lblC P Qc c) := by
  have hN := cfgOfTraces_compRows P Qc Qm c
  unfold ExactExecution.computeRows execOfTraces
  rw [reconTree_labels (foC P Qc c) (lblC P Qc c)
    P.optimized.family.problem.cfg.compRows h.sfCompute h.validCompute]
  rw [hN]

private theorem getElem_map_range'_one {α : Type*} (f : ℕ → α) {n : ℕ}
    {i : ℕ} (hi : i < n) :
    ((List.range' 1 n).map f)[i]'(by simp [List.length_map, List.length_range']; exact hi) =
      f (i + 1) := by
  rw [List.getElem_map, List.getElem_range']
  simp [Nat.add_comm]

/-- Round-trip: the `i`-th BFS compute row **is** the decoded `Qc` label. -/
theorem execOfTraces_computeRowAt_eq_lblC
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (i : Fin (cfgOfTraces P Qc Qm c).compRows) :
    (execOfTraces P Qc Qm c h).computeRowAt i =
      lblC P Qc c (i.val + 1) := by
  have hrows := execOfTraces_computeRows P Qc Qm c h
  unfold ExactExecution.computeRowAt
  rw [List.get_eq_getElem]
  have hidx : ((Fin.cast (ExactExecution.computeRows_length
      (execOfTraces P Qc Qm c h)).symm i) : ℕ) = (i : ℕ) :=
    Fin.val_cast _ _
  simp only [hidx]
  rw [List.getElem_of_eq hrows]
  exact getElem_map_range'_one (lblC P Qc c) i.isLt

/-- Round-trip: the `i`-th BFS memory row **is** the decoded `Qm` label. -/
theorem execOfTraces_memoryRowAt_eq_lblM
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (i : Fin (cfgOfTraces P Qc Qm c).memRows) :
    (execOfTraces P Qc Qm c h).memoryRowAt i =
      lblM P Qm c (i.val + 1) := by
  have hrows := execOfTraces_memoryRows P Qc Qm c h
  unfold ExactExecution.memoryRowAt
  rw [List.get_eq_getElem]
  have hidx : ((Fin.cast (ExactExecution.memoryRows_length
      (execOfTraces P Qc Qm c h)).symm i) : ℕ) = (i : ℕ) :=
    Fin.val_cast _ _
  simp only [hidx]
  rw [List.getElem_of_eq hrows]
  exact getElem_map_range'_one (lblM P Qm c) i.isLt

/-- **Defining equation (compute `Pub`).**  Proved from `reconTree_labels`,
not assumed. -/
theorem execOfTraces_computePubAt_eq_decodePub
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (i : Fin (cfgOfTraces P Qc Qm c).compRows) :
    (execOfTraces P Qc Qm c h).computePubAt i =
      decodePub
        (rowEnvAt P c (familyQc P c Qc)
          (Fin.cast (cfgOfTraces_compRows P Qc Qm c) i))
        (lblC P Qc c (i.val + 1)).1 := by
  have hrow := execOfTraces_computeRowAt_eq_lblC P Qc Qm c h i
  have hi : (i : ℕ) < P.optimized.family.problem.cfg.compRows := by
    rw [← cfgOfTraces_compRows P Qc Qm c]; exact i.isLt
  have hlbl := lblC_succ P Qc c ⟨i.val, hi⟩
  have heq : Fin.cast (cfgOfTraces_compRows P Qc Qm c) i = ⟨i.val, hi⟩ :=
    Fin.ext rfl
  simp only [ExactExecution.computePubAt, hrow, hlbl, lblCAt, heq]

/-- Defining equation (compute `Dec`). -/
theorem execOfTraces_computeDecAt_eq_decodeDec
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (i : Fin (cfgOfTraces P Qc Qm c).compRows) :
    (execOfTraces P Qc Qm c h).computeDecAt i =
      decodeDec
        (rowEnvAt P c (familyQc P c Qc)
          (Fin.cast (cfgOfTraces_compRows P Qc Qm c) i)) := by
  have hrow := execOfTraces_computeRowAt_eq_lblC P Qc Qm c h i
  have hi : (i : ℕ) < P.optimized.family.problem.cfg.compRows := by
    rw [← cfgOfTraces_compRows P Qc Qm c]; exact i.isLt
  have hlbl := lblC_succ P Qc c ⟨i.val, hi⟩
  have heq : Fin.cast (cfgOfTraces_compRows P Qc Qm c) i = ⟨i.val, hi⟩ :=
    Fin.ext rfl
  simp only [ExactExecution.computeDecAt, hrow, hlbl, lblCAt, heq]

/-- Defining equation (memory `Pub`). -/
theorem execOfTraces_memoryPubAt_eq_decodeMemPub
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (i : Fin (cfgOfTraces P Qc Qm c).memRows) :
    (execOfTraces P Qc Qm c h).memoryPubAt i =
      decodeMemPub P Qm c (Fin.cast (cfgOfTraces_memRows P Qc Qm c) i) := by
  have hrow := execOfTraces_memoryRowAt_eq_lblM P Qc Qm c h i
  have hi : (i : ℕ) < P.optimized.family.problem.cfg.memRows := by
    rw [← cfgOfTraces_memRows P Qc Qm c]; exact i.isLt
  have hlbl := lblM_succ P Qm c ⟨i.val, hi⟩
  have heq : Fin.cast (cfgOfTraces_memRows P Qc Qm c) i = ⟨i.val, hi⟩ :=
    Fin.ext rfl
  simp only [ExactExecution.memoryPubAt, hrow, hlbl, lblMAt, heq]

end

end Nock.NockVMROM.Thm54.ExecOfTraces

#print axioms Nock.NockVMROM.Thm54.ExecOfTraces.execOfTraces_computePubAt_eq_decodePub
#print axioms Nock.NockVMROM.Thm54.ExecOfTraces.execOfTraces_computeDecAt_eq_decodeDec
#print axioms Nock.NockVMROM.Thm54.ExecOfTraces.execOfTraces_memoryPubAt_eq_decodeMemPub
#print axioms Nock.NockVMROM.Thm54.ExecOfTraces.lblCAt_eq_rowEnvAt
