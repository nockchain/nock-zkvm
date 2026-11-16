/-
  Nock/RedTeam/Batch940Thm54LiftStrategyReceipts.lean

Every declaration of `Nock/NockVMROM/Thm54/StrategyOfTracesLift.lean` (below the pinned file,
  re-parameterised over `O : OptimizedStrictNockVMROMPackage`, `stateTagChar` explicit as `tag`) is
  proved here equal, at `O := P.optimized` and `tag := P.stateTagChar`, to the ORIGINAL it restates
  (`DeployedComputeRows`, `ExecOfTraces`, `StrategyOfTraces`, `StrategyOfTracesCore`,
  `OptimizedComputeHostileAccumulator`, and the pinned `OptimizedStrictFullPackage`).

  Exceptions, each with its reason:
  * `TracesWalkHyps` is an inductive; two distinct inductives are never definitionally equal.
-/
import Batteries.Tactic.OpenPrivate
import Nock.NockVMROM.Thm54.StrategyOfTracesLift
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.StrategyOfTraces
import Nock.NockVMROM.Thm54.DeployedComputeRows
import Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
import Nock.NockVMROM.Thm54.ComputedWindow

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

set_option smartUnfolding false

namespace Nock.RedTeam.Batch940

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ProductionP8Containment

noncomputable section

/-! ## A. Package-free helpers -/

section Free

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

theorem decodeSource_eq (env : OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv F K) :
    StrategyOfTracesLift.decodeSource env = DeployedComputeRows.decodeSource env := rfl

theorem decodeInputs_eq (env : OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv F K) :
    StrategyOfTracesLift.decodeInputs env = DeployedComputeRows.decodeInputs env := rfl

theorem decodePub_eq (env : OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv F K)
    (st : State) :
    StrategyOfTracesLift.decodePub env st = DeployedComputeRows.decodePub env st := rfl

theorem decodeDec_eq (env : OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv F K) :
    StrategyOfTracesLift.decodeDec env = DeployedComputeRows.decodeDec env := rfl

theorem decodeEx_eq (env : OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv F K) :
    StrategyOfTracesLift.decodeEx env = DeployedComputeRows.decodeEx env := rfl

theorem dummyMemRec_eq :
    StrategyOfTracesLift.dummyMemRec = StrategyOfTraces.dummyMemRec := rfl

theorem dummyComputeRow_eq :
    StrategyOfTracesLift.dummyComputeRow = StrategyOfTraces.dummyComputeRow := rfl

theorem dummyDTmem_eq :
    StrategyOfTracesLift.dummyDTmem (K := K) = StrategyOfTraces.dummyDTmem := rfl

theorem dummyMemoryLabel_eq :
    StrategyOfTracesLift.dummyMemoryLabel (K := K) = StrategyOfTraces.dummyMemoryLabel := rfl

theorem dummyComputeLabel_eq :
    StrategyOfTracesLift.dummyComputeLabel (K := K) = StrategyOfTraces.dummyComputeLabel := rfl

theorem groupChildren_eq {α : Type} (fs : List ℕ) (kids : List (NTree α)) :
    StrategyOfTracesLift.groupChildren fs kids = StrategyOfTraces.groupChildren fs kids := rfl

theorem unbfs_eq {α : Type} (fanout : α → ℕ) (fuel : ℕ) (level rest : List α) :
    StrategyOfTracesLift.unbfs fanout fuel level rest =
      StrategyOfTraces.unbfs fanout fuel level rest := rfl

theorem rebuildForest_eq {α : Type} (fanout : α → ℕ) (kRoots : ℕ) (rows : List α) :
    StrategyOfTracesLift.rebuildForest fanout kRoots rows =
      StrategyOfTraces.rebuildForest fanout kRoots rows := rfl

theorem computeStateOf_eq (env : Env K) :
    StrategyOfTracesLift.computeStateOf env = StrategyOfTraces.computeStateOf env := rfl

theorem memoryPtNoun_eq (envK : Env K) :
    StrategyOfTracesLift.memoryPtNoun envK = StrategyOfTraces.memoryPtNoun envK := rfl

theorem memoryMemRoot_eq (envK : Env K) :
    StrategyOfTracesLift.memoryMemRoot envK = StrategyOfTraces.memoryMemRoot envK := rfl

theorem memoryMemChild_eq (envK : Env K) :
    StrategyOfTracesLift.memoryMemChild envK = StrategyOfTraces.memoryMemChild envK := rfl

theorem computeFanout_eq (row : State × DTcomp K) :
    StrategyOfTracesLift.computeFanout row = StrategyOfTraces.computeFanout row := rfl

theorem memoryFanout_eq (row : MState × DTmem K) :
    StrategyOfTracesLift.memoryFanout row = StrategyOfTraces.memoryFanout row := rfl

theorem nounByFP_eq (q : ℕ) (forest : List (NTree (MState × DTmem K))) (fp : FP K) :
    StrategyOfTracesLift.nounByFP q forest fp = StrategyOfTraces.nounByFP q forest fp := rfl

theorem memRecJoin_eq (q : ℕ) (forest : List (NTree (MState × DTmem K))) (mr : MemRec K) :
    StrategyOfTracesLift.memRecJoin q forest mr = StrategyOfTraces.memRecJoin q forest mr := rfl

theorem kidSkel_eq (kids : List ComputeRowSkeleton) (i : ℕ) :
    StrategyOfTracesLift.kidSkel kids i = StrategyOfTraces.kidSkel kids i := rfl

theorem joinNoun_eq (q : ℕ) (z : K) (forest : List (NTree (MState × DTmem K))) (fp : FP K) :
    StrategyOfTracesLift.joinNoun q z forest fp = StrategyOfTraces.joinNoun q z forest fp := rfl

theorem nounHead_eq (n : Noun) :
    StrategyOfTracesLift.nounHead n = StrategyOfTraces.nounHead n := rfl

theorem nounTail_eq (n : Noun) :
    StrategyOfTracesLift.nounTail n = StrategyOfTraces.nounTail n := rfl

theorem joinEvaluation_eq (q : ℕ) (forest : List (NTree (MState × DTmem K))) (formula : Noun)
    (row : State × DTcomp K) (kids : List ComputeRowSkeleton) :
    StrategyOfTracesLift.joinEvaluation q forest formula row kids =
      StrategyOfTraces.joinEvaluation q forest formula row kids := rfl

theorem computeSkeletonRow_eq (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun) (row : State × DTcomp K) (kids : List ComputeRowSkeleton) :
    StrategyOfTracesLift.computeSkeletonRow q forest subj formula row kids =
      StrategyOfTraces.computeSkeletonRow q forest subj formula row kids := rfl

theorem mapComputeJoinInFuel_eq (fuel q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (t : NTree (State × DTcomp K)) (subj formula : Noun) :
    StrategyOfTracesLift.mapComputeJoinInFuel fuel q forest t subj formula =
      StrategyOfTraces.mapComputeJoinInFuel fuel q forest t subj formula := rfl

/-- The lifted kid map `mapComputeJoinKids` is the original one. -/
theorem mapComputeJoinKids_eq :
    @StrategyOfTracesLift.mapComputeJoinKids = @StrategyOfTraces.mapComputeJoinKids := rfl

/-- The lifted `mapComputeJoinInFuel_succ` proves the original's statement. -/
theorem mapComputeJoinInFuel_succ_rcpt : HEq @StrategyOfTracesLift.mapComputeJoinInFuel_succ @StrategyOfTraces.mapComputeJoinInFuel_succ := HEq.rfl

/-- The lifted `mapComputeJoinInFuel_eq_1_old` proves the original's statement. -/
theorem mapComputeJoinInFuel_eq_1_old_rcpt : HEq @StrategyOfTracesLift.mapComputeJoinInFuel_eq_1_old @StrategyOfTraces.mapComputeJoinInFuel_eq_1_old := HEq.rfl

/-- The lifted `mapComputeJoinInFuel_eq_2_old` proves the original's statement. -/
theorem mapComputeJoinInFuel_eq_2_old_rcpt : HEq @StrategyOfTracesLift.mapComputeJoinInFuel_eq_2_old @StrategyOfTraces.mapComputeJoinInFuel_eq_2_old := HEq.rfl

/-- The lifted `mapComputeJoinInFuel_eq_3_old` proves the original's statement. -/
theorem mapComputeJoinInFuel_eq_3_old_rcpt : HEq @StrategyOfTracesLift.mapComputeJoinInFuel_eq_3_old @StrategyOfTraces.mapComputeJoinInFuel_eq_3_old := HEq.rfl

/-- The lifted `mapComputeJoinInFuel_eq_4_old` proves the original's statement. -/
theorem mapComputeJoinInFuel_eq_4_old_rcpt : HEq @StrategyOfTracesLift.mapComputeJoinInFuel_eq_4_old @StrategyOfTraces.mapComputeJoinInFuel_eq_4_old := HEq.rfl

/-- The lifted `mapComputeJoinInFuel_eq_5_old` proves the original's statement. -/
theorem mapComputeJoinInFuel_eq_5_old_rcpt : HEq @StrategyOfTracesLift.mapComputeJoinInFuel_eq_5_old @StrategyOfTraces.mapComputeJoinInFuel_eq_5_old := HEq.rfl

/-- The lifted `mapComputeJoinInFuel_eq_6_old` proves the original's statement. -/
theorem mapComputeJoinInFuel_eq_6_old_rcpt : HEq @StrategyOfTracesLift.mapComputeJoinInFuel_eq_6_old @StrategyOfTraces.mapComputeJoinInFuel_eq_6_old := HEq.rfl

/-- The lifted `mapComputeJoinInFuel_eq_7_old` proves the original's statement. -/
theorem mapComputeJoinInFuel_eq_7_old_rcpt : HEq @StrategyOfTracesLift.mapComputeJoinInFuel_eq_7_old @StrategyOfTraces.mapComputeJoinInFuel_eq_7_old := HEq.rfl

/-- The lifted `mapComputeJoinInFuel_eq_8_old` proves the original's statement. -/
theorem mapComputeJoinInFuel_eq_8_old_rcpt : HEq @StrategyOfTracesLift.mapComputeJoinInFuel_eq_8_old @StrategyOfTraces.mapComputeJoinInFuel_eq_8_old := HEq.rfl

/-- The lifted `mapComputeJoinInFuel_eq_9_old` proves the original's statement. -/
theorem mapComputeJoinInFuel_eq_9_old_rcpt : HEq @StrategyOfTracesLift.mapComputeJoinInFuel_eq_9_old @StrategyOfTraces.mapComputeJoinInFuel_eq_9_old := HEq.rfl

/-- The lifted `mapComputeJoinInFuel_eq_10_old` proves the original's statement. -/
theorem mapComputeJoinInFuel_eq_10_old_rcpt : HEq @StrategyOfTracesLift.mapComputeJoinInFuel_eq_10_old @StrategyOfTraces.mapComputeJoinInFuel_eq_10_old := HEq.rfl

/-- The lifted `mapComputeJoinInFuel_eq_11_old` proves the original's statement. -/
theorem mapComputeJoinInFuel_eq_11_old_rcpt : HEq @StrategyOfTracesLift.mapComputeJoinInFuel_eq_11_old @StrategyOfTraces.mapComputeJoinInFuel_eq_11_old := HEq.rfl

/-- The lifted `mapComputeJoinInFuel_eq_12_old` proves the original's statement. -/
theorem mapComputeJoinInFuel_eq_12_old_rcpt : HEq @StrategyOfTracesLift.mapComputeJoinInFuel_eq_12_old @StrategyOfTraces.mapComputeJoinInFuel_eq_12_old := HEq.rfl

/-- The lifted `mapComputeJoinInFuel_eq_13_old` proves the original's statement. -/
theorem mapComputeJoinInFuel_eq_13_old_rcpt : HEq @StrategyOfTracesLift.mapComputeJoinInFuel_eq_13_old @StrategyOfTraces.mapComputeJoinInFuel_eq_13_old := HEq.rfl

theorem mapComputeJoinIn_eq (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (t : NTree (State × DTcomp K)) (subj formula : Noun) :
    StrategyOfTracesLift.mapComputeJoinIn q forest t subj formula =
      StrategyOfTraces.mapComputeJoinIn q forest t subj formula := rfl

theorem joinFormulaDeep_eq (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (t : NTree (State × DTcomp K)) :
    StrategyOfTracesLift.joinFormulaDeep q forest t =
      StrategyOfTraces.joinFormulaDeep q forest t := rfl

theorem mapComputeJoin_eq (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (t : NTree (State × DTcomp K)) :
    StrategyOfTracesLift.mapComputeJoin q forest t = StrategyOfTraces.mapComputeJoin q forest t :=
  rfl

theorem configTemplateOf_eq (cfg : ExactConfig F K) (z : K) :
    StrategyOfTracesLift.configTemplateOf cfg z = StrategyOfTraces.configTemplateOf cfg z := rfl

theorem wrapComputeLabel_eq (row : State × DTcomp K) :
    StrategyOfTracesLift.wrapComputeLabel row = StrategyOfTracesCore.wrapComputeLabel row := rfl

theorem memExponent_eq (α ts : K) :
    StrategyOfTracesLift.memExponent α ts = StrategyOfTracesCore.memExponent α ts := rfl

theorem wrapMemoryLabel_eq (α : K) (row : MState × DTmem K) :
    StrategyOfTracesLift.wrapMemoryLabel α row = StrategyOfTracesCore.wrapMemoryLabel α row := rfl

end Free

/-! ## B. The package layer at `O := P.optimized`, `tag := P.stateTagChar` -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])

theorem memorySourceTrace_eq :
    StrategyOfTracesLift.memorySourceTrace P.optimized Qm = P.memorySourceTrace Qm := rfl

theorem memoryBaseEnv_eq (i : Fin P.optimized.family.problem.cfg.memRows) :
    StrategyOfTracesLift.memoryBaseEnv P.optimized Qm i = P.memoryBaseEnv Qm i := rfl

theorem memorySourceEnv_eq (i : Fin P.optimized.family.problem.cfg.memRows) :
    StrategyOfTracesLift.memorySourceEnv P.optimized Qm i = P.memorySourceEnv Qm i := rfl

theorem rowEnv_eq (i : Fin P.optimized.family.problem.cfg.compRows) :
    StrategyOfTracesLift.rowEnv P.optimized Qc i = OptimizedComputeHostileAccumulator.rowEnv P Qc i :=
  rfl

theorem typedComputeLabel_eq (i : Fin P.optimized.family.problem.cfg.compRows) :
    StrategyOfTracesLift.typedComputeLabel P.optimized Qc i =
      StrategyOfTraces.typedComputeLabel P Qc i := rfl

theorem typedMemoryLabel_eq (i : Fin P.optimized.family.problem.cfg.memRows) :
    StrategyOfTracesLift.typedMemoryLabel P.optimized Qm i =
      StrategyOfTraces.typedMemoryLabel P Qm i := rfl

theorem typedComputeRows_eq :
    StrategyOfTracesLift.typedComputeRows P.optimized Qc = StrategyOfTraces.typedComputeRows P Qc :=
  rfl

theorem typedMemoryRows_eq :
    StrategyOfTracesLift.typedMemoryRows P.optimized Qm = StrategyOfTraces.typedMemoryRows P Qm :=
  rfl

theorem typedComputeForest_eq :
    StrategyOfTracesLift.typedComputeForest P.optimized Qc =
      StrategyOfTraces.typedComputeForest P Qc := rfl

theorem typedComputeTree_eq :
    StrategyOfTracesLift.typedComputeTree P.optimized Qc = StrategyOfTraces.typedComputeTree P Qc :=
  rfl

theorem typedMemoryForest_eq :
    StrategyOfTracesLift.typedMemoryForest P.optimized Qm =
      StrategyOfTraces.typedMemoryForest P Qm := rfl

theorem computeJoinOf_eq :
    StrategyOfTracesLift.computeJoinOf P.optimized Qc Qm = StrategyOfTraces.computeJoinOf P Qc Qm :=
  rfl

theorem decodedSkeletonOf_eq :
    StrategyOfTracesLift.decodedSkeletonOf P.optimized Qc Qm =
      StrategyOfTraces.decodedSkeletonOf P Qc Qm := rfl

theorem publicClaimOf_eq :
    StrategyOfTracesLift.publicClaimOf P.optimized Qc Qm = StrategyOfTraces.publicClaimOf P Qc Qm :=
  rfl

theorem lblCAt_eq (i : Fin P.optimized.family.problem.cfg.compRows) :
    StrategyOfTracesLift.lblCAt P.optimized Qc c i = ExecOfTraces.lblCAt P Qc c i := rfl

theorem lblC_eq (i : ℕ) :
    StrategyOfTracesLift.lblC P.optimized Qc c i = ExecOfTraces.lblC P Qc c i := rfl

theorem decodeMemPub_eq (i : Fin P.optimized.family.problem.cfg.memRows) :
    StrategyOfTracesLift.decodeMemPub P.optimized Qm c i = ExecOfTraces.decodeMemPub P Qm c i :=
  rfl

theorem lblMAt_eq (i : Fin P.optimized.family.problem.cfg.memRows) :
    StrategyOfTracesLift.lblMAt P.optimized Qm c i = ExecOfTraces.lblMAt P Qm c i := rfl

theorem lblM_eq (i : ℕ) :
    StrategyOfTracesLift.lblM P.optimized Qm c i = ExecOfTraces.lblM P Qm c i := rfl

theorem foC_eq (i : ℕ) :
    StrategyOfTracesLift.foC P.optimized Qc c i = ExecOfTraces.foC P Qc c i := rfl

theorem foM_eq (i : ℕ) :
    StrategyOfTracesLift.foM P.optimized Qm c i = ExecOfTraces.foM P Qm c i := rfl

theorem clabC_eq (i j : ℕ) :
    StrategyOfTracesLift.clabC P.optimized Qc c i j = ExecOfTraces.clabC P Qc c i j := rfl

theorem clabM_eq (i j : ℕ) :
    StrategyOfTracesLift.clabM P.optimized Qm c i j = ExecOfTraces.clabM P Qm c i j := rfl

theorem computeLabelList_eq :
    StrategyOfTracesLift.computeLabelList P.optimized Qc c = ExecOfTraces.computeLabelList P Qc c :=
  rfl

theorem memoryLabelList_eq :
    StrategyOfTracesLift.memoryLabelList P.optimized Qm c = ExecOfTraces.memoryLabelList P Qm c :=
  rfl

theorem computeLabelList_length_eq :
    StrategyOfTracesLift.computeLabelList_length P.optimized Qc c =
      ExecOfTraces.computeLabelList_length P Qc c := rfl

theorem memoryLabelList_length_eq :
    StrategyOfTracesLift.memoryLabelList_length P.optimized Qm c =
      ExecOfTraces.memoryLabelList_length P Qm c := rfl

theorem cfgOfTraces_eq :
    StrategyOfTracesLift.cfgOfTraces P.optimized Qc Qm c = ExecOfTraces.cfgOfTraces P Qc Qm c := rfl

theorem cfgOfTraces_compRows_eq :
    StrategyOfTracesLift.cfgOfTraces_compRows P.optimized Qc Qm c =
      ExecOfTraces.cfgOfTraces_compRows P Qc Qm c := rfl

theorem cfgOfTraces_memRows_eq :
    StrategyOfTracesLift.cfgOfTraces_memRows P.optimized Qc Qm c =
      ExecOfTraces.cfgOfTraces_memRows P Qc Qm c := rfl

theorem cfgOfTraces_kMem_eq :
    StrategyOfTracesLift.cfgOfTraces_kMem P.optimized Qc Qm c =
      ExecOfTraces.cfgOfTraces_kMem P Qc Qm c := rfl

/-! ### `TracesWalkHyps` (inductive: field-wise `rfl`, constructor-wise iff) -/

theorem tracesWalkHyps_field_sfCompute_eq :
    (Walk.Sf (StrategyOfTracesLift.foC P.optimized Qc c) P.optimized.family.problem.cfg.compRows + 1 =
        P.optimized.family.problem.cfg.compRows) =
      (Walk.Sf (ExecOfTraces.foC P Qc c) P.optimized.family.problem.cfg.compRows + 1 =
        P.optimized.family.problem.cfg.compRows) := rfl

theorem tracesWalkHyps_field_validCompute_eq :
    Walk.BFSValid (StrategyOfTracesLift.foC P.optimized Qc c) P.optimized.family.problem.cfg.compRows =
      Walk.BFSValid (ExecOfTraces.foC P Qc c) P.optimized.family.problem.cfg.compRows := rfl

theorem tracesWalkHyps_field_sfMemory_eq :
    (P.optimized.family.problem.cfg.kMem +
        Walk.Sf (StrategyOfTracesLift.foM P.optimized Qm c) P.optimized.family.problem.cfg.memRows =
      P.optimized.family.problem.cfg.memRows) =
    (P.optimized.family.problem.cfg.kMem +
        Walk.Sf (ExecOfTraces.foM P Qm c) P.optimized.family.problem.cfg.memRows =
      P.optimized.family.problem.cfg.memRows) := rfl

theorem tracesWalkHyps_field_validMemory_eq :
    Walk.BFSValidF P.optimized.family.problem.cfg.kMem (StrategyOfTracesLift.foM P.optimized Qm c)
        P.optimized.family.problem.cfg.memRows =
      Walk.BFSValidF P.optimized.family.problem.cfg.kMem (ExecOfTraces.foM P Qm c)
        P.optimized.family.problem.cfg.memRows := rfl


theorem tracesWalkHyps_iff :
    StrategyOfTracesLift.TracesWalkHyps P.optimized Qc Qm c ↔ ExecOfTraces.TracesWalkHyps P Qc Qm c :=
  ⟨fun h => ⟨h.sfCompute, h.validCompute, h.sfMemory, h.validMemory⟩,
   fun h => ⟨h.sfCompute, h.validCompute, h.sfMemory, h.validMemory⟩⟩

/-- The original walk hypotheses, read as the lifted ones. -/
abbrev liftWalk (h : ExecOfTraces.TracesWalkHyps P Qc Qm c) :
    StrategyOfTracesLift.TracesWalkHyps P.optimized Qc Qm c :=
  (tracesWalkHyps_iff P c Qc Qm).2 h

variable (h : ExecOfTraces.TracesWalkHyps P Qc Qm c)

theorem execOfTraces_eq :
    StrategyOfTracesLift.execOfTraces P.optimized Qc Qm c (liftWalk P c Qc Qm h) =
      ExecOfTraces.execOfTraces P Qc Qm c h := rfl

theorem cfgTemplateOfTraces_eq (z : K) :
    StrategyOfTracesLift.cfgTemplateOfTraces P.optimized Qc Qm c z =
      StrategyOfTracesCore.cfgTemplateOfTraces P Qc Qm c z := rfl

theorem execTemplateOfTraces_eq (z : K) :
    StrategyOfTracesLift.execTemplateOfTraces P.optimized Qc Qm c (liftWalk P c Qc Qm h) z =
      StrategyOfTracesCore.execTemplateOfTraces P Qc Qm c h z := rfl

theorem timestampOfTraces_eq :
    StrategyOfTracesLift.timestampOfTraces P.optimized Qc Qm c (liftWalk P c Qc Qm h) =
      StrategyOfTracesCore.timestampOfTraces P Qc Qm c h := rfl

theorem familyDataOfTraces_eq (z : K) (hz : z ≠ 0) (α lmb : K) :
    StrategyOfTracesLift.familyDataOfTraces P.optimized P.stateTagChar Qc Qm c
        (liftWalk P c Qc Qm h) z hz α lmb =
      StrategyOfTracesCore.familyDataOfTraces P Qc Qm c h z hz α lmb := rfl

theorem tablesOfTraces_eq (z : K) (hz : z ≠ 0) (α lmb : K) :
    StrategyOfTracesLift.tablesOfTraces P.optimized P.stateTagChar Qc Qm c
        (liftWalk P c Qc Qm h) z hz α lmb =
      StrategyOfTracesCore.tablesOfTraces P Qc Qm c h z hz α lmb := rfl

theorem walksOfTraces_eq :
    StrategyOfTracesLift.walksOfTraces P.optimized Qc Qm c =
      StrategyOfTracesCore.walksOfTraces P Qc Qm c := rfl

theorem ioOfTraces_eq (z : K) (hz : z ≠ 0) (α lmb : K) :
    StrategyOfTracesLift.ioOfTraces P.optimized P.stateTagChar Qc Qm c
        (liftWalk P c Qc Qm h) z hz α lmb =
      StrategyOfTracesCore.ioOfTraces P Qc Qm c h z hz α lmb := rfl

theorem afterAlphaMOfTraces_eq (z : K) (hz : z ≠ 0) (α lmb : K) :
    StrategyOfTracesLift.afterAlphaMOfTraces P.optimized P.stateTagChar Qc Qm c
        (liftWalk P c Qc Qm h) z hz α lmb =
      StrategyOfTracesCore.afterAlphaMOfTraces P Qc Qm c h z hz α lmb := rfl

theorem topologyOfTraces_eq (z : K) (hz : z ≠ 0) (α lmb : K) :
    StrategyOfTracesLift.topologyOfTraces P.optimized P.stateTagChar Qc Qm c
        (liftWalk P c Qc Qm h) z hz α lmb =
      StrategyOfTracesCore.topologyOfTraces P Qc Qm c h z hz α lmb := rfl

theorem rawVerifierOfTraces_eq :
    StrategyOfTracesLift.rawVerifierOfTraces P.optimized P.stateTagChar Qc Qm c
        (liftWalk P c Qc Qm h) =
      StrategyOfTracesCore.rawVerifierOfTraces P Qc Qm c h := rfl

theorem verifierOfTraces_eq :
    StrategyOfTracesLift.verifierOfTraces P.optimized P.stateTagChar Qc Qm c
        (liftWalk P c Qc Qm h) =
      StrategyOfTracesCore.verifierOfTraces P Qc Qm c h := rfl


theorem strategyOfTraces_eq :
    StrategyOfTracesLift.strategyOfTraces P.optimized P.stateTagChar Qc Qm c
        (liftWalk P c Qc Qm h) =
      StrategyOfTracesCore.strategyOfTraces P Qc Qm c h := rfl


theorem strategyOfTraces_accepts_iff (z : JointCoins K) (lmb : K) :
    (StrategyOfTracesLift.strategyOfTraces P.optimized P.stateTagChar Qc Qm c
        (liftWalk P c Qc Qm h)).Accepts z lmb ↔
      (StrategyOfTracesCore.strategyOfTraces P Qc Qm c h).Accepts z lmb := Iff.rfl

theorem strategyOfTraces_genuine_iff (z : JointCoins K) (lmb : K) :
    GenuineTargetAt (StrategyOfTracesLift.strategyOfTraces P.optimized P.stateTagChar Qc Qm c
        (liftWalk P c Qc Qm h)) P.q P.optimized.Λ z lmb ↔
      GenuineTargetAt (StrategyOfTracesCore.strategyOfTraces P Qc Qm c h) P.q P.optimized.Λ z lmb :=
  Iff.rfl


theorem strategy_eq_any (h' : StrategyOfTracesLift.TracesWalkHyps P.optimized Qc Qm c) :
    StrategyOfTracesLift.strategyOfTraces P.optimized P.stateTagChar Qc Qm c h' =
      StrategyOfTracesCore.strategyOfTraces P Qc Qm c ((tracesWalkHyps_iff P c Qc Qm).1 h') := rfl

/-- The restored `p8` at the lifted constants is the one at the originals. -/
theorem p8_transport :
    (∃ h : StrategyOfTracesLift.TracesWalkHyps P.optimized Qc Qm c,
        (StrategyOfTracesLift.strategyOfTraces P.optimized P.stateTagChar Qc Qm c h).Accepts
          c.1 c.2.2.2.lambda ∧
        GenuineTargetAt (StrategyOfTracesLift.strategyOfTraces P.optimized P.stateTagChar Qc Qm c h)
          P.q P.optimized.Λ c.1 c.2.2.2.lambda) ↔
    (∃ h : ExecOfTraces.TracesWalkHyps P Qc Qm c,
        (StrategyOfTracesCore.strategyOfTraces P Qc Qm c h).Accepts c.1 c.2.2.2.lambda ∧
        GenuineTargetAt (StrategyOfTracesCore.strategyOfTraces P Qc Qm c h)
          P.q P.optimized.Λ c.1 c.2.2.2.lambda) :=
  ⟨fun ⟨h, hh⟩ => ⟨(tracesWalkHyps_iff P c Qc Qm).1 h, hh⟩,
   fun ⟨h, hh⟩ => ⟨(tracesWalkHyps_iff P c Qc Qm).2 h, hh⟩⟩

/-- The P8 slot predicate (`∀ h, ∃ cen, …`) at the lifted constants is the one at the originals. -/
theorem slot_transport :
    (∀ h : StrategyOfTracesLift.TracesWalkHyps P.optimized Qc Qm c,
      ∃ cen : EdgeComparisonCensus.CombinedSkeletonCensus K
          (StrategyOfTracesLift.strategyOfTraces P.optimized P.stateTagChar Qc Qm c h).skeleton
          P.optimized.Λ,
        c.1 ∈ FailureUnion (StrategyOfTracesLift.strategyOfTraces P.optimized P.stateTagChar Qc Qm c h)
          cen c.2.2.2.lambda) ↔
    (∀ h : ExecOfTraces.TracesWalkHyps P Qc Qm c,
      ∃ cen : EdgeComparisonCensus.CombinedSkeletonCensus K
          (StrategyOfTracesCore.strategyOfTraces P Qc Qm c h).skeleton P.optimized.Λ,
        c.1 ∈ FailureUnion (StrategyOfTracesCore.strategyOfTraces P Qc Qm c h) cen c.2.2.2.lambda) :=
  ⟨fun H h => H ((tracesWalkHyps_iff P c Qc Qm).2 h),
   fun H h => H ((tracesWalkHyps_iff P c Qc Qm).1 h)⟩

end

open private family_kMem_pos from Nock.NockVMROM.Thm54.P8Core.ExecOfTraces in
/-- `family_kMem_pos` (private in `ExecOfTraces`): two proofs of the same proposition at
`O := P.optimized`. -/
theorem family_kMem_pos_eq {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F]
    [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    HEq (StrategyOfTracesLift.family_kMem_pos P.optimized) (family_kMem_pos P) := HEq.rfl

/-! ## Z.

Then every user-facing constant of the lifted module
(auxiliaries, the structure's generated constants and its projections excluded) appears in the
`lifted` column (`family_kMem_pos`, whose original is `private`, by its own check below). -/

open Lean in
/-- ``. -/
def receiptTable : List (Name × Name × Name) := [
  (`decodeSource_eq, `decodeSource, `Nock.NockVMROM.Thm54.DeployedComputeRows.decodeSource),
  (`decodeInputs_eq, `decodeInputs, `Nock.NockVMROM.Thm54.DeployedComputeRows.decodeInputs),
  (`decodePub_eq, `decodePub, `Nock.NockVMROM.Thm54.DeployedComputeRows.decodePub),
  (`decodeDec_eq, `decodeDec, `Nock.NockVMROM.Thm54.DeployedComputeRows.decodeDec),
  (`decodeEx_eq, `decodeEx, `Nock.NockVMROM.Thm54.DeployedComputeRows.decodeEx),
  (`dummyMemRec_eq, `dummyMemRec, `Nock.NockVMROM.Thm54.StrategyOfTraces.dummyMemRec),
  (`dummyComputeRow_eq, `dummyComputeRow, `Nock.NockVMROM.Thm54.StrategyOfTraces.dummyComputeRow),
  (`dummyDTmem_eq, `dummyDTmem, `Nock.NockVMROM.Thm54.StrategyOfTraces.dummyDTmem),
  (`dummyMemoryLabel_eq, `dummyMemoryLabel, `Nock.NockVMROM.Thm54.StrategyOfTraces.dummyMemoryLabel),
  (`dummyComputeLabel_eq, `dummyComputeLabel, `Nock.NockVMROM.Thm54.StrategyOfTraces.dummyComputeLabel),
  (`groupChildren_eq, `groupChildren, `Nock.NockVMROM.Thm54.StrategyOfTraces.groupChildren),
  (`unbfs_eq, `unbfs, `Nock.NockVMROM.Thm54.StrategyOfTraces.unbfs),
  (`rebuildForest_eq, `rebuildForest, `Nock.NockVMROM.Thm54.StrategyOfTraces.rebuildForest),
  (`computeStateOf_eq, `computeStateOf, `Nock.NockVMROM.Thm54.StrategyOfTraces.computeStateOf),
  (`memoryPtNoun_eq, `memoryPtNoun, `Nock.NockVMROM.Thm54.StrategyOfTraces.memoryPtNoun),
  (`memoryMemRoot_eq, `memoryMemRoot, `Nock.NockVMROM.Thm54.StrategyOfTraces.memoryMemRoot),
  (`memoryMemChild_eq, `memoryMemChild, `Nock.NockVMROM.Thm54.StrategyOfTraces.memoryMemChild),
  (`computeFanout_eq, `computeFanout, `Nock.NockVMROM.Thm54.StrategyOfTraces.computeFanout),
  (`memoryFanout_eq, `memoryFanout, `Nock.NockVMROM.Thm54.StrategyOfTraces.memoryFanout),
  (`nounByFP_eq, `nounByFP, `Nock.NockVMROM.Thm54.StrategyOfTraces.nounByFP),
  (`memRecJoin_eq, `memRecJoin, `Nock.NockVMROM.Thm54.StrategyOfTraces.memRecJoin),
  (`kidSkel_eq, `kidSkel, `Nock.NockVMROM.Thm54.StrategyOfTraces.kidSkel),
  (`joinNoun_eq, `joinNoun, `Nock.NockVMROM.Thm54.StrategyOfTraces.joinNoun),
  (`nounHead_eq, `nounHead, `Nock.NockVMROM.Thm54.StrategyOfTraces.nounHead),
  (`nounTail_eq, `nounTail, `Nock.NockVMROM.Thm54.StrategyOfTraces.nounTail),
  (`joinEvaluation_eq, `joinEvaluation, `Nock.NockVMROM.Thm54.StrategyOfTraces.joinEvaluation),
  (`computeSkeletonRow_eq, `computeSkeletonRow, `Nock.NockVMROM.Thm54.StrategyOfTraces.computeSkeletonRow),
  (`mapComputeJoinInFuel_eq, `mapComputeJoinInFuel, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel),
  (`mapComputeJoinIn_eq, `mapComputeJoinIn, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinIn),
  (`joinFormulaDeep_eq, `joinFormulaDeep, `Nock.NockVMROM.Thm54.StrategyOfTraces.joinFormulaDeep),
  (`mapComputeJoin_eq, `mapComputeJoin, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoin),
  (`configTemplateOf_eq, `configTemplateOf, `Nock.NockVMROM.Thm54.StrategyOfTraces.configTemplateOf),
  (`wrapComputeLabel_eq, `wrapComputeLabel, `Nock.NockVMROM.Thm54.StrategyOfTracesCore.wrapComputeLabel),
  (`memExponent_eq, `memExponent, `Nock.NockVMROM.Thm54.StrategyOfTracesCore.memExponent),
  (`wrapMemoryLabel_eq, `wrapMemoryLabel, `Nock.NockVMROM.Thm54.StrategyOfTracesCore.wrapMemoryLabel),
  (`memorySourceTrace_eq, `memorySourceTrace, `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.memorySourceTrace),
  (`memoryBaseEnv_eq, `memoryBaseEnv, `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.memoryBaseEnv),
  (`memorySourceEnv_eq, `memorySourceEnv, `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.memorySourceEnv),
  (`rowEnv_eq, `rowEnv, `Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.rowEnv),
  (`typedComputeLabel_eq, `typedComputeLabel, `Nock.NockVMROM.Thm54.StrategyOfTraces.typedComputeLabel),
  (`typedMemoryLabel_eq, `typedMemoryLabel, `Nock.NockVMROM.Thm54.StrategyOfTraces.typedMemoryLabel),
  (`typedComputeRows_eq, `typedComputeRows, `Nock.NockVMROM.Thm54.StrategyOfTraces.typedComputeRows),
  (`typedMemoryRows_eq, `typedMemoryRows, `Nock.NockVMROM.Thm54.StrategyOfTraces.typedMemoryRows),
  (`typedComputeForest_eq, `typedComputeForest, `Nock.NockVMROM.Thm54.StrategyOfTraces.typedComputeForest),
  (`typedComputeTree_eq, `typedComputeTree, `Nock.NockVMROM.Thm54.StrategyOfTraces.typedComputeTree),
  (`typedMemoryForest_eq, `typedMemoryForest, `Nock.NockVMROM.Thm54.StrategyOfTraces.typedMemoryForest),
  (`computeJoinOf_eq, `computeJoinOf, `Nock.NockVMROM.Thm54.StrategyOfTraces.computeJoinOf),
  (`decodedSkeletonOf_eq, `decodedSkeletonOf, `Nock.NockVMROM.Thm54.StrategyOfTraces.decodedSkeletonOf),
  (`publicClaimOf_eq, `publicClaimOf, `Nock.NockVMROM.Thm54.StrategyOfTraces.publicClaimOf),
  (`lblCAt_eq, `lblCAt, `Nock.NockVMROM.Thm54.ExecOfTraces.lblCAt),
  (`lblC_eq, `lblC, `Nock.NockVMROM.Thm54.ExecOfTraces.lblC),
  (`decodeMemPub_eq, `decodeMemPub, `Nock.NockVMROM.Thm54.ExecOfTraces.decodeMemPub),
  (`lblMAt_eq, `lblMAt, `Nock.NockVMROM.Thm54.ExecOfTraces.lblMAt),
  (`lblM_eq, `lblM, `Nock.NockVMROM.Thm54.ExecOfTraces.lblM),
  (`foC_eq, `foC, `Nock.NockVMROM.Thm54.ExecOfTraces.foC),
  (`foM_eq, `foM, `Nock.NockVMROM.Thm54.ExecOfTraces.foM),
  (`clabC_eq, `clabC, `Nock.NockVMROM.Thm54.ExecOfTraces.clabC),
  (`clabM_eq, `clabM, `Nock.NockVMROM.Thm54.ExecOfTraces.clabM),
  (`computeLabelList_eq, `computeLabelList, `Nock.NockVMROM.Thm54.ExecOfTraces.computeLabelList),
  (`memoryLabelList_eq, `memoryLabelList, `Nock.NockVMROM.Thm54.ExecOfTraces.memoryLabelList),
  (`computeLabelList_length_eq, `computeLabelList_length, `Nock.NockVMROM.Thm54.ExecOfTraces.computeLabelList_length),
  (`memoryLabelList_length_eq, `memoryLabelList_length, `Nock.NockVMROM.Thm54.ExecOfTraces.memoryLabelList_length),
  (`cfgOfTraces_eq, `cfgOfTraces, `Nock.NockVMROM.Thm54.ExecOfTraces.cfgOfTraces),
  (`cfgOfTraces_compRows_eq, `cfgOfTraces_compRows, `Nock.NockVMROM.Thm54.ExecOfTraces.cfgOfTraces_compRows),
  (`cfgOfTraces_memRows_eq, `cfgOfTraces_memRows, `Nock.NockVMROM.Thm54.ExecOfTraces.cfgOfTraces_memRows),
  (`cfgOfTraces_kMem_eq, `cfgOfTraces_kMem, `Nock.NockVMROM.Thm54.ExecOfTraces.cfgOfTraces_kMem),
  (`execOfTraces_eq, `execOfTraces, `Nock.NockVMROM.Thm54.ExecOfTraces.execOfTraces),
  (`tracesWalkHyps_iff, `TracesWalkHyps, `Nock.NockVMROM.Thm54.ExecOfTraces.TracesWalkHyps),
  (`cfgTemplateOfTraces_eq, `cfgTemplateOfTraces, `Nock.NockVMROM.Thm54.StrategyOfTracesCore.cfgTemplateOfTraces),
  (`execTemplateOfTraces_eq, `execTemplateOfTraces, `Nock.NockVMROM.Thm54.StrategyOfTracesCore.execTemplateOfTraces),
  (`timestampOfTraces_eq, `timestampOfTraces, `Nock.NockVMROM.Thm54.StrategyOfTracesCore.timestampOfTraces),
  (`familyDataOfTraces_eq, `familyDataOfTraces, `Nock.NockVMROM.Thm54.StrategyOfTracesCore.familyDataOfTraces),
  (`tablesOfTraces_eq, `tablesOfTraces, `Nock.NockVMROM.Thm54.StrategyOfTracesCore.tablesOfTraces),
  (`walksOfTraces_eq, `walksOfTraces, `Nock.NockVMROM.Thm54.StrategyOfTracesCore.walksOfTraces),
  (`ioOfTraces_eq, `ioOfTraces, `Nock.NockVMROM.Thm54.StrategyOfTracesCore.ioOfTraces),
  (`afterAlphaMOfTraces_eq, `afterAlphaMOfTraces, `Nock.NockVMROM.Thm54.StrategyOfTracesCore.afterAlphaMOfTraces),
  (`topologyOfTraces_eq, `topologyOfTraces, `Nock.NockVMROM.Thm54.StrategyOfTracesCore.topologyOfTraces),
  (`rawVerifierOfTraces_eq, `rawVerifierOfTraces, `Nock.NockVMROM.Thm54.StrategyOfTracesCore.rawVerifierOfTraces),
  (`verifierOfTraces_eq, `verifierOfTraces, `Nock.NockVMROM.Thm54.StrategyOfTracesCore.verifierOfTraces),
  (`strategyOfTraces_eq, `strategyOfTraces, `Nock.NockVMROM.Thm54.StrategyOfTracesCore.strategyOfTraces),
  (`mapComputeJoinKids_eq, `mapComputeJoinKids, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinKids),
  (`mapComputeJoinInFuel_succ_rcpt, `mapComputeJoinInFuel_succ, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel_succ),
  (`mapComputeJoinInFuel_eq_1_old_rcpt, `mapComputeJoinInFuel_eq_1_old, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel_eq_1_old),
  (`mapComputeJoinInFuel_eq_2_old_rcpt, `mapComputeJoinInFuel_eq_2_old, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel_eq_2_old),
  (`mapComputeJoinInFuel_eq_3_old_rcpt, `mapComputeJoinInFuel_eq_3_old, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel_eq_3_old),
  (`mapComputeJoinInFuel_eq_4_old_rcpt, `mapComputeJoinInFuel_eq_4_old, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel_eq_4_old),
  (`mapComputeJoinInFuel_eq_5_old_rcpt, `mapComputeJoinInFuel_eq_5_old, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel_eq_5_old),
  (`mapComputeJoinInFuel_eq_6_old_rcpt, `mapComputeJoinInFuel_eq_6_old, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel_eq_6_old),
  (`mapComputeJoinInFuel_eq_7_old_rcpt, `mapComputeJoinInFuel_eq_7_old, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel_eq_7_old),
  (`mapComputeJoinInFuel_eq_8_old_rcpt, `mapComputeJoinInFuel_eq_8_old, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel_eq_8_old),
  (`mapComputeJoinInFuel_eq_9_old_rcpt, `mapComputeJoinInFuel_eq_9_old, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel_eq_9_old),
  (`mapComputeJoinInFuel_eq_10_old_rcpt, `mapComputeJoinInFuel_eq_10_old, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel_eq_10_old),
  (`mapComputeJoinInFuel_eq_11_old_rcpt, `mapComputeJoinInFuel_eq_11_old, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel_eq_11_old),
  (`mapComputeJoinInFuel_eq_12_old_rcpt, `mapComputeJoinInFuel_eq_12_old, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel_eq_12_old),
  (`mapComputeJoinInFuel_eq_13_old_rcpt, `mapComputeJoinInFuel_eq_13_old, `Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel_eq_13_old)]

end Nock.RedTeam.Batch940

open Lean Nock.RedTeam.Batch940 in
run_cmd do
  let env ← getEnv
  let LIFT : Name := `Nock.NockVMROM.Thm54.StrategyOfTracesLift
  let PIN : Name := `Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
  let names := env.header.moduleNames
  let data := env.header.moduleData
  let mut above : NameSet := {}
  for i in [0:names.size] do
    let m := names[i]!
    if m == PIN || m == `Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackageDefs || data[i]!.imports.any (fun imp => above.contains imp.module) then
      above := above.insert m
  let liftMod : Name := `Nock.NockVMROM.Thm54.StrategyOfTracesLift
  if above.contains liftMod then throwError "the lifted module imports the pinned file"
  let mut covered : NameSet := {}
  for (r, l, o) in receiptTable do
    let rn := `Nock.RedTeam.Batch940 ++ r
    let ln := LIFT ++ l
    let some rci := env.find? rn | throwError s!"missing receipt {rn}"
    let used := rci.type.getUsedConstants
    unless used.contains ln do throwError s!"receipt {rn} does not name the lifted {ln}"
    unless used.contains o do throwError s!"receipt {rn} does not name the original {o} (vacuous)"
    if ln == o then throwError s!"receipt {rn}: lifted = original"
    let some om := env.getModuleFor? o | throwError s!"no module for {o}"


    -- S0: likewise verbatim into `Thm54.BelowDefs.*`, below both pinned halves
    unless above.contains om || (`Nock.NockVMROM.Thm54.P8Core).isPrefixOf om ||
        (`Nock.NockVMROM.Thm54.BelowDefs).isPrefixOf om do
      throwError s!"original {o} [{om}] is neither above the pin nor relocated into P8Core"
    if om == liftMod then throwError s!"original {o} is in the lifted module (vacuous)"
    covered := covered.insert ln
  -- completeness over the lifted module's own constants
  let noise (n : Name) : Bool :=
    n.isInternal || n.components.any fun c =>
      let s := c.toString
      s.startsWith "_" || s.startsWith "match_" || s.startsWith "eq_" || s == "proof_1"
        || c == `rec || c == `recOn || c == `casesOn || c == `brecOn || c == `below
        || c == `noConfusion || c == `noConfusionType || c == `ndrec || c == `ndrecOn
        || c == `mk || c == `binductionOn || c == `ibelow || c == `congr_simp

  match env.find? `Nock.RedTeam.Batch940.family_kMem_pos_eq with
  | none => throwError "missing receipt family_kMem_pos_eq"
  | some ci =>
    let used := ci.type.getUsedConstants
    unless used.contains (LIFT ++ `family_kMem_pos) do throwError "family_kMem_pos_eq: lifted absent"
    unless used.any (fun n => env.getModuleFor? n == some `Nock.NockVMROM.Thm54.P8Core.ExecOfTraces &&
        (n.toString.splitOn "family_kMem_pos").length > 1) do
      throwError "family_kMem_pos_eq: private original absent (vacuous)"
    covered := covered.insert (LIFT ++ `family_kMem_pos)
  let exempt : List Name := []
  let mut missing : Array Name := #[]
  let mut total := 0
  for (n, _) in env.constants.toList do
    if env.getModuleFor? n == some liftMod && !noise n && !exempt.contains n then
      if (env.getProjectionFnInfo? n).isSome then continue
      total := total + 1
      unless covered.contains n do missing := missing.push n
  unless missing.isEmpty do throwError s!"lifted names without a receipt: {missing}"
  logInfo s!"Batch940: {receiptTable.length + 1} receipts, each naming the lifted constant and an above-pin original; {total} user-facing lifted constants, all covered (+ exempt {exempt})"
