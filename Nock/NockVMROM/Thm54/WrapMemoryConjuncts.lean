/-
  Nock/NockVMROM/Thm54/WrapMemoryConjuncts.lean

  400 — memory wrap exponent installed.

  **Vmem case (b)** (`Batch387.vmemCase_is_b`): `Vmem = eqBlk ∧ interV`
  reads `mem.ts` on `read_root` / `verify_child`.
  Hostile `wrapMemoryLabel α` now sets
  `recordExponent := memExponent α mem.ts`, so specialize recovers the
  committed timestamp when the discrete log exists.  Honest templates and
  `HonestCommitment.memory_specialize_placeholder_eq` are untouched — that
  lemma is applied under `MemoryTimestampSpecializesAt`.
-/
import Nock.NockVMROM.Thm54.WrapComputeConjuncts
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.Language
import Nock.NockVMROM.Thm54.HonestCommitment
import Nock.NockVMROM.Thm54.ResponseTsMemPowers
import Nock.NockVMROM.Thm54.HostilePoleAlignment
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.NockVMROM.Thm54.NounRealization
import Nock.NockVMROM.Thm54.P8Core.WrapMemoryConjuncts
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.WrapMemoryConjuncts

open scoped Polynomial Classical
open Polynomial
open Nock
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.MemoryPaperFactorization
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.Framework.Thm54
open MonolithicRAP

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

/-- Case (b) discrete log — re-exported from the live wrap module. -/
noncomputable abbrev memExponent [Fintype K] [DecidableEq K] (α ts : K) : ℕ :=
  StrategyOfTracesCore.memExponent α ts

theorem memExponent_pow [Fintype K] [DecidableEq K] {α ts : K}
    (h : ∃ n : ℕ, n < orderOf α ∧ α ^ n = ts) :
    α ^ memExponent α ts = ts :=
  StrategyOfTracesCore.memExponent_pow h

/-- On an active record whose `ts` is in `⟨α⟩` below the order, specialize at
`memExponent` recovers the committed record (case (b) identity). -/
theorem specializeMemRec_memExponent [Fintype K] [DecidableEq K]
    (α : K) (rec : ComputeTable.MemRec K)
    (h : ∃ n : ℕ, n < orderOf α ∧ α ^ n = rec.ts) :
    specializeMemRec α true (memExponent α rec.ts) rec = rec := by
  simp only [specializeMemRec, if_true]
  refine ComputeTable.MemRec.ext rfl rfl rfl ?_
  exact memExponent_pow h

/-- The wrap does not touch `ipre`. -/
theorem wrap_preserves_ipre [Fintype K] [DecidableEq K]
    (α lmb : K) (row : MState × DTmem K) :
    ((wrapMemoryLabel α row).specialize α lmb).2.2.ipre = row.2.2.ipre := by
  simp [wrapMemoryLabel]

/-- The wrap does not touch `icur`. -/
theorem wrap_preserves_icur [Fintype K] [DecidableEq K]
    (α lmb : K) (row : MState × DTmem K) :
    ((wrapMemoryLabel α row).specialize α lmb).2.2.icur = row.2.2.icur := by
  simp [wrapMemoryLabel]

/-- The wrap does not touch `pt`. -/
theorem wrap_preserves_pt [Fintype K] [DecidableEq K]
    (α lmb : K) (row : MState × DTmem K) :
    ((wrapMemoryLabel α row).specialize α lmb).2.2.pt = row.2.2.pt := by
  simp [wrapMemoryLabel]

/-- Active wrap recovers `mem.ts` when the discrete log exists. -/
theorem wrap_preserves_mem_ts [Fintype K] [DecidableEq K]
    (α lmb : K) (row : MState × DTmem K)
    (hact : memoryMemRecKind row.1 = .active)
    (h : ∃ n : ℕ, n < orderOf α ∧ α ^ n = row.2.2.mem.ts) :
    ((wrapMemoryLabel α row).specialize α lmb).2.2.mem.ts = row.2.2.mem.ts := by
  simp only [wrapMemoryLabel, MemoryRowTemplate.specialize, MemoryRowTemplate.encodeRow,
    MemoryRowTemplate.specializeA, specializeMemRec, hact, decide_true, if_true]
  simpa [NockVM.formRRow] using memExponent_pow h

/-- Padding wrap writes `MemRec.zero`. -/
theorem wrap_padding_mem_zero [Fintype K] [DecidableEq K]
    (α lmb : K) (row : MState × DTmem K)
    (hpad : memoryMemRecKind row.1 = .padding) :
    ((wrapMemoryLabel α row).specialize α lmb).2.2.mem = ComputeTable.MemRec.zero := by
  unfold wrapMemoryLabel MemoryRowTemplate.specialize MemoryRowTemplate.encodeRow
    MemoryRowTemplate.specializeA specializeMemRec
  simp [hpad]

variable {F : Type} [Field F] [Algebra F K]

noncomputable section

variable [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem execTemplate_memoryRows_wrap
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (z : K) :
    (execTemplateOfTraces P Qc Qm c h z).memoryRows =
    (execOfTraces P Qc Qm c h).memoryRows.map
      (wrapMemoryLabel (alphaM c.1)) := by
  simp only [ExactExecutionTemplate.memoryRows, execTemplateOfTraces,
    ExactExecution.memoryRows]
  rw [bfsForest_mapNTree]
  simp [List.map_map]

theorem specialized_memoryRows_map
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0) :
    ((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryRows =
      (execOfTraces P Qc Qm c h).memoryRows.map
        (fun row => (wrapMemoryLabel (alphaM c.1) row).specialize (alphaM c.1) c.2.2.2.lambda) := by
  change ((execTemplateOfTraces P Qc Qm c h (nprSeed c.1)).specialize
      (alphaM c.1) c.2.2.2.lambda).memoryRows =
    (execOfTraces P Qc Qm c h).memoryRows.map
      (fun row => (wrapMemoryLabel (alphaM c.1) row).specialize (alphaM c.1) c.2.2.2.lambda)
  rw [ExactExecutionTemplate.specialize_memoryRows
        (execTemplateOfTraces P Qc Qm c h (nprSeed c.1)) (alphaM c.1) c.2.2.2.lambda]
  rw [execTemplate_memoryRows_wrap]
  simp [List.map_map, Function.comp_def]

theorem specializedExec_memRows
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0) :
    ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows =
      (cfgOfTraces P Qc Qm c).memRows :=
  rfl

private theorem getElem_map_range'_one {α : Type*} (f : ℕ → α) {n i : ℕ}
    (hi : i < n) :
    ((List.range' 1 n).map f)[i]'(by simp [List.length_map, List.length_range']; exact hi) =
      f (i + 1) := by
  rw [List.getElem_map, List.getElem_range']
  simp [Nat.add_comm]

theorem specialized_memoryPubAt_ipre
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (i : Fin ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows) :
    (((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryPubAt i).ipre =
      (decodeMemPub P Qm c
        (Fin.cast
          ((specializedExec_memRows P Qc Qm c h hz).trans
            (cfgOfTraces_memRows P Qc Qm c)) i)).ipre := by
  have hcfg := specializedExec_memRows P Qc Qm c h hz
  have hN := cfgOfTraces_memRows P Qc Qm c
  have hi : (i : ℕ) < P.optimized.family.problem.cfg.memRows := by omega
  have hi' : (i : ℕ) < (cfgOfTraces P Qc Qm c).memRows := by omega
  have hmap := specialized_memoryRows_map P Qc Qm c h hz
  have hexec := execOfTraces_memoryRows P Qc Qm c h
  have hlenE : (execOfTraces P Qc Qm c h).memoryRows.length =
      (cfgOfTraces P Qc Qm c).memRows :=
    (execOfTraces P Qc Qm c h).memoryRows_length
  have hidxE : (i : ℕ) < (execOfTraces P Qc Qm c h).memoryRows.length := by
    omega
  have hget :
      (execOfTraces P Qc Qm c h).memoryRows[(i : ℕ)]'hidxE =
        lblMAt P Qm c ⟨i.val, hi⟩ := by
    rw [List.getElem_of_eq hexec, getElem_map_range'_one (lblM P Qm c) hi']
    exact lblM_succ P Qm c ⟨i.val, hi⟩
  have hlenS :
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryRows.length =
        (execOfTraces P Qc Qm c h).memoryRows.length := by
    rw [hmap, List.length_map]
  have hidxS : (i : ℕ) <
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryRows.length := by
    omega
  have hrow :
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryRows[(i : ℕ)]'hidxS =
        (wrapMemoryLabel (alphaM c.1) (lblMAt P Qm c ⟨i.val, hi⟩)).specialize (alphaM c.1)
          c.2.2.2.lambda := by
    simp only [hmap]
    rw [List.getElem_map]
    exact congrArg (fun row => (wrapMemoryLabel (alphaM c.1) row).specialize (alphaM c.1) c.2.2.2.lambda) hget
  have hpub :
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryPubAt i =
        (((strategyOfTraces P Qc Qm c h).specializedExec
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryRows[(i : ℕ)]'hidxS).2.2 := by
    unfold ExactExecution.memoryPubAt ExactExecution.memoryRowAt
    rw [List.get_eq_getElem]
    congr 1
  have hcast :
      Fin.cast (hcfg.trans hN) i = ⟨i.val, hi⟩ := Fin.ext rfl
  rw [hpub, hrow, wrap_preserves_ipre, hcast]
  simp [lblMAt]

theorem specialized_memoryPubAt_icur
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (i : Fin ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows) :
    (((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryPubAt i).icur =
      (decodeMemPub P Qm c
        (Fin.cast
          ((specializedExec_memRows P Qc Qm c h hz).trans
            (cfgOfTraces_memRows P Qc Qm c)) i)).icur := by
  have hcfg := specializedExec_memRows P Qc Qm c h hz
  have hN := cfgOfTraces_memRows P Qc Qm c
  have hi : (i : ℕ) < P.optimized.family.problem.cfg.memRows := by omega
  have hi' : (i : ℕ) < (cfgOfTraces P Qc Qm c).memRows := by omega
  have hmap := specialized_memoryRows_map P Qc Qm c h hz
  have hexec := execOfTraces_memoryRows P Qc Qm c h
  have hidxE : (i : ℕ) < (execOfTraces P Qc Qm c h).memoryRows.length := by
    rw [(execOfTraces P Qc Qm c h).memoryRows_length]; exact hi'
  have hget :
      (execOfTraces P Qc Qm c h).memoryRows[(i : ℕ)]'hidxE =
        lblMAt P Qm c ⟨i.val, hi⟩ := by
    rw [List.getElem_of_eq hexec, getElem_map_range'_one (lblM P Qm c) hi']
    exact lblM_succ P Qm c ⟨i.val, hi⟩
  have hidxS : (i : ℕ) <
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryRows.length := by
    rw [hmap, List.length_map]; exact hidxE
  have hrow :
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryRows[(i : ℕ)]'hidxS =
        (wrapMemoryLabel (alphaM c.1) (lblMAt P Qm c ⟨i.val, hi⟩)).specialize (alphaM c.1)
          c.2.2.2.lambda := by
    simp only [hmap]
    rw [List.getElem_map]
    exact congrArg (fun row => (wrapMemoryLabel (alphaM c.1) row).specialize (alphaM c.1) c.2.2.2.lambda) hget
  have hpub :
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryPubAt i =
        (((strategyOfTraces P Qc Qm c h).specializedExec
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryRows[(i : ℕ)]'hidxS).2.2 := by
    unfold ExactExecution.memoryPubAt ExactExecution.memoryRowAt
    rw [List.get_eq_getElem]
    congr 1
  have hcast : Fin.cast (hcfg.trans hN) i = ⟨i.val, hi⟩ := Fin.ext rfl
  rw [hpub, hrow, wrap_preserves_icur, hcast]
  simp [lblMAt]

theorem specialized_memoryPubAt_pt
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (i : Fin ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows) :
    (((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryPubAt i).pt =
      (decodeMemPub P Qm c
        (Fin.cast
          ((specializedExec_memRows P Qc Qm c h hz).trans
            (cfgOfTraces_memRows P Qc Qm c)) i)).pt := by
  have hcfg := specializedExec_memRows P Qc Qm c h hz
  have hN := cfgOfTraces_memRows P Qc Qm c
  have hi : (i : ℕ) < P.optimized.family.problem.cfg.memRows := by omega
  have hi' : (i : ℕ) < (cfgOfTraces P Qc Qm c).memRows := by omega
  have hmap := specialized_memoryRows_map P Qc Qm c h hz
  have hexec := execOfTraces_memoryRows P Qc Qm c h
  have hidxE : (i : ℕ) < (execOfTraces P Qc Qm c h).memoryRows.length := by
    rw [(execOfTraces P Qc Qm c h).memoryRows_length]; exact hi'
  have hget :
      (execOfTraces P Qc Qm c h).memoryRows[(i : ℕ)]'hidxE =
        lblMAt P Qm c ⟨i.val, hi⟩ := by
    rw [List.getElem_of_eq hexec, getElem_map_range'_one (lblM P Qm c) hi']
    exact lblM_succ P Qm c ⟨i.val, hi⟩
  have hidxS : (i : ℕ) <
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryRows.length := by
    rw [hmap, List.length_map]; exact hidxE
  have hrow :
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryRows[(i : ℕ)]'hidxS =
        (wrapMemoryLabel (alphaM c.1) (lblMAt P Qm c ⟨i.val, hi⟩)).specialize (alphaM c.1)
          c.2.2.2.lambda := by
    simp only [hmap]
    rw [List.getElem_map]
    exact congrArg (fun row => (wrapMemoryLabel (alphaM c.1) row).specialize (alphaM c.1) c.2.2.2.lambda) hget
  have hpub :
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryPubAt i =
        (((strategyOfTraces P Qc Qm c h).specializedExec
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryRows[(i : ℕ)]'hidxS).2.2 := by
    unfold ExactExecution.memoryPubAt ExactExecution.memoryRowAt
    rw [List.get_eq_getElem]
    congr 1
  have hcast : Fin.cast (hcfg.trans hN) i = ⟨i.val, hi⟩ := Fin.ext rfl
  rw [hpub, hrow, wrap_preserves_pt, hcast]
  simp [lblMAt]

theorem memorySourceTrace_eq_proj
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    P.memorySourceTrace Qm = projOf P Qm :=
  rfl

/-- Source width is 171; roles 27 and 28 sit in the packed block. -/
theorem memory_role_col_lt (j : ℕ) (hj : j ≤ 28) (k : Fin 3) :
    6 + 3 * j + (k : ℕ) < 182 := by
  have : (k : ℕ) < 3 := k.isLt
  omega

theorem memorySourceEnvAt_trace_eq_rowEnvK
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (j : ℕ) (hj : j ≤ 28) :
    (memorySourceEnvAt P c Qm i).trace j = (rowEnvK P Qm i).trace j := by
  have hw : (sourceOf P).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit
      (rowNodeSet P.optimized.memoryNodes)).1
  simp only [memorySourceEnvAt, rowEnvK, memorySourceTemplate_col0,
    memoryBaseEnvAt, rowEnvF, gatherEnv]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hlt174 : 6 + 3 * j + (k : ℕ) < 182 := memory_role_col_lt j hj k
  have hlt : 6 + 3 * j + (k : ℕ) < (sourceOf P).rap.w := by
    rw [hw]; exact hlt174
  simp only [envOfTrace, memoryCol0, dif_pos hlt174, dif_pos hlt]
  have hidx : (⟨6 + 3 * j + (k : ℕ), hlt174⟩ : Fin 182) =
      Fin.cast hw.symm ⟨6 + 3 * j + (k : ℕ), hlt⟩ := Fin.ext rfl
  rw [memorySourceTrace_eq_proj, hidx]
  rfl

theorem memorySourceEnvAt_traceNext_eq_rowEnvK
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (j : ℕ) (hj : j ≤ 28) :
    (memorySourceEnvAt P c Qm i).traceNext j = (rowEnvK P Qm i).traceNext j := by
  have hw : (sourceOf P).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit
      (rowNodeSet P.optimized.memoryNodes)).1
  simp only [memorySourceEnvAt, rowEnvK, memorySourceTemplate_col0,
    memoryBaseEnvAt, rowEnvF, gatherEnv]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hlt174 : 6 + 3 * j + (k : ℕ) < 182 := memory_role_col_lt j hj k
  have hlt : 6 + 3 * j + (k : ℕ) < (sourceOf P).rap.w := by
    rw [hw]; exact hlt174
  simp only [envOfTrace, memoryCol0, dif_pos hlt174, dif_pos hlt]
  have hidx : (⟨6 + 3 * j + (k : ℕ), hlt174⟩ : Fin 182) =
      Fin.cast hw.symm ⟨6 + 3 * j + (k : ℕ), hlt⟩ := Fin.ext rfl
  rw [memorySourceTrace_eq_proj, hidx]
  rfl

/-- `mem_first_ipre`: wrap-preserved `ipre` is the anchored first-row role 27. -/
theorem specialized_mem_first_ipre
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (hsatM : RAP.SatisfiesWithPreprocessing P.memoryChip Qm) :
    (((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryPubAt
      ⟨0, (strategyOfTraces P Qc Qm c h).specializedCfg
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda |>.memRows_pos⟩).ipre = 0 := by
  have hpos :=
    ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows_pos
  have hipre :=
    specialized_memoryPubAt_ipre P Qc Qm c h hz ⟨0, hpos⟩
  have hcast :
      Fin.cast
        ((specializedExec_memRows P Qc Qm c h hz).trans
          (cfgOfTraces_memRows P Qc Qm c)) ⟨0, hpos⟩ =
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩ :=
    Fin.ext rfl
  have hdec : (decodeMemPub P Qm c
      ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).ipre = 0 := by
    change (memorySourceEnvAt P c Qm
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).trace 27 = 0
    rw [memorySourceEnvAt_trace_eq_rowEnvK P c Qm _ 27 (by norm_num)]
    exact (hostile_intermediate_anchored P Qm hsatM).1
  rw [hipre, hcast, hdec]

/-- `mem_last_icur`: wrap-preserved `icur` is the anchored last-row role 28. -/
theorem specialized_mem_last_icur
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (hsatM : RAP.SatisfiesWithPreprocessing P.memoryChip Qm) :
    (((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryPubAt
      (((strategyOfTraces P Qc Qm c h).specializedCfg
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).orbit.lastIndex
        ((strategyOfTraces P Qc Qm c h).specializedCfg
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows
        ((strategyOfTraces P Qc Qm c h).specializedCfg
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows_pos)).icur = 0 := by
  have hcfg := specializedExec_memRows P Qc Qm c h hz
  have hN := cfgOfTraces_memRows P Qc Qm c
  have hpos :=
    ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows_pos
  let iLast :=
    ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).orbit.lastIndex
      ((strategyOfTraces P Qc Qm c h).specializedCfg
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows hpos
  have hi : (iLast : ℕ) < P.optimized.family.problem.cfg.memRows := by
    have : (iLast : ℕ) <
        ((strategyOfTraces P Qc Qm c h).specializedCfg
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows := iLast.isLt
    omega
  have hicur := specialized_memoryPubAt_icur P Qc Qm c h hz iLast
  have hcast : Fin.cast (hcfg.trans hN) iLast = lastRow P := by
    apply Fin.ext
    change (iLast : ℕ) = (lastRow P : ℕ)
    have hval : (iLast : ℕ) =
        ((strategyOfTraces P Qc Qm c h).specializedCfg
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows - 1 :=
      rfl
    simp only [lastRow, rows]
    omega
  have hdec : (decodeMemPub P Qm c (lastRow P)).icur = 0 := by
    change (memorySourceEnvAt P c Qm (lastRow P)).trace 28 = 0
    rw [memorySourceEnvAt_trace_eq_rowEnvK P c Qm _ 28 (by norm_num)]
    exact (hostile_intermediate_anchored P Qm hsatM).2
  rw [hicur, hcast, hdec]

/-- `mem_icur_chain`: off the last row, `icur(i) = ipre(i+1)` via `chainMixed`. -/
theorem specialized_mem_icur_chain
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (hsatM : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
    (i : Fin ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows)
    (hi : (i : ℕ) + 1 <
        ((strategyOfTraces P Qc Qm c h).specializedCfg
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memRows) :
    (((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryPubAt i).icur =
      (((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryPubAt
        ⟨(i : ℕ) + 1, hi⟩).ipre := by
  have hcfg := specializedExec_memRows P Qc Qm c h hz
  have hN := cfgOfTraces_memRows P Qc Qm c
  have hi0 : (i : ℕ) < P.optimized.family.problem.cfg.memRows := by omega
  have hi1 : (i : ℕ) + 1 < P.optimized.family.problem.cfg.memRows := by omega
  have hicur := specialized_memoryPubAt_icur P Qc Qm c h hz i
  have hipre :=
    specialized_memoryPubAt_ipre P Qc Qm c h hz ⟨(i : ℕ) + 1, hi⟩
  have hcast0 : Fin.cast (hcfg.trans hN) i = ⟨i.val, hi0⟩ := Fin.ext rfl
  have hcast1 :
      Fin.cast (hcfg.trans hN) ⟨(i : ℕ) + 1, hi⟩ = ⟨(i : ℕ) + 1, hi1⟩ :=
    Fin.ext rfl
  rw [hicur, hipre, hcast0, hcast1]
  change (memorySourceEnvAt P c Qm ⟨i.val, hi0⟩).trace 28 =
      (memorySourceEnvAt P c Qm ⟨(i : ℕ) + 1, hi1⟩).trace 27
  rw [memorySourceEnvAt_trace_eq_rowEnvK P c Qm _ 28 (by norm_num),
    memorySourceEnvAt_trace_eq_rowEnvK P c Qm _ 27 (by norm_num)]
  have hmix0 := mixed_at P Qm hsatM ⟨i.val, hi0⟩ _ (chainMixed_mem P.optimized.basis)
  have h5 : (rowEnvF P Qm ⟨i.val, hi0⟩).trace 5 = 0 := by
    have hm := (masks_at P Qm hsatM ⟨i.val, hi0⟩).2
    simp only [rows] at hm
    rw [hm, if_neg (Nat.ne_of_lt hi1)]
  have hmix : (rowEnvK P Qm ⟨i.val, hi0⟩).trace 28 =
      (rowEnvK P Qm ⟨i.val, hi0⟩).traceNext 27 := by
    simp only [chainMixed, MixedExpr.eval, bcur, CoeffExpr.eval] at hmix0
    rw [h5, sub_zero, map_one, one_mul, sub_eq_zero] at hmix0
    exact hmix0
  have hadj := P.optimized.memoryOrbitAligned ⟨i.val, hi0⟩ hi1
  have hw : (sourceOf P).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit
      (rowNodeSet P.optimized.memoryNodes)).1
  have hnext :
      (rowEnvK P Qm ⟨i.val, hi0⟩).traceNext 27 =
        (rowEnvK P Qm ⟨(i : ℕ) + 1, hi1⟩).trace 27 := by
    simp only [rowEnvK, gatherEnv, memoryCol0]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hlt : 6 + 3 * 27 + (k : ℕ) < (sourceOf P).rap.w := by
      rw [hw]; exact memory_role_col_lt 27 (by norm_num) k
    simp only [rowEnvF, envOfTrace, dif_pos hlt]
    rw [hadj, mul_comm]
  rw [hmix, hnext]

/-! ## C2-β transfer: wrap identity, `vmem`, `memoryRows` (under `MemPower`) -/

open ExactExecution
open ResponseTsMemPowers
open FamilyMemoryRows
open HostilePoleAlignment
open HonestCommitment

theorem encRec_decodeMem_eq_rowRecord
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    NockVM.encRecC (decodeMemPub P Qm c i).mem
        ((memorySourceEnvAt P c Qm i).trace 57) =
      OptimizedMemoryHostileAccumulator.memRowRecord
        (memorySourceEnvAt P c Qm i) := by
  funext d
  simp only [NockVM.encRecC, decodeMemPub, memoryMemRoot, memoryMemChild,
    OptimizedMemoryHostileAccumulator.memRowRecord, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
  fin_cases d <;> first | rfl | simp

theorem specializedCfg_memoryInputs
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0) :
    ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).challenges.memoryInputs =
      { z := nprSeed c.1
        β := -(c.2.2.2.interPole)
        γ := c.2.1.1 } :=
  rfl

/-- Case (b) wrap identity under `MemPower` / padding-zero.
Outer BFS state must agree with `pub.st` (as on `lblMAt`). -/
theorem wrap_fixes_vmem_row (α : K) (row : MState × DTmem K)
    (hst : row.1 = row.2.2.st)
    (hpow : memoryMemRecKind row.1 = .active → MemPower α row.2.2.mem.ts)
    (hpad : memoryMemRecKind row.1 = .padding →
      row.2.2.mem = ComputeTable.MemRec.zero) :
    (wrapMemoryLabel α row).specializeA α = row := by
  refine memory_specializeA_placeholder_eq ?_
  refine ⟨rfl, hst.symm, ?_, hpad⟩
  by_cases hact : memoryMemRecKind row.1 = .active
  · simp only [wrapMemoryLabel, hact, ↓reduceIte]
    exact (memExponent_pow (hpow hact)).symm
  · have hpad' : memoryMemRecKind row.1 = .padding := by
      cases hk : memoryMemRecKind row.1 with
      | active => exact absurd hk hact
      | padding => rfl
    have hz := hpad hpad'
    simp only [hact, ↓reduceIte]
    simpa [ComputeTable.MemRec.zero] using congrArg ComputeTable.MemRec.ts hz

end

end Nock.NockVMROM.Thm54.WrapMemoryConjuncts
