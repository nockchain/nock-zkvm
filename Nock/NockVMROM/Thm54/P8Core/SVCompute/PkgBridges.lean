/-
  Nock/NockVMROM/Thm54/P8Core/SVCompute/PkgBridges.lean

  Every definition bridge is `rfl`
  at `D := toCD O`, `L := layout309`; every theorem bridge is the twin applied there.  Nothing
  live is edited.
-/
import Nock.NockVMROM.Thm54.P8Core.SVCompute.EnvTwins
import Nock.NockVMROM.Thm54.P8Core.ExecOfTraces
import Nock.NockVMROM.Thm54.P8Core.OptimizedComputeHostileAccumulator
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.SVCompute

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.Reified Nock.Framework Nock.Framework.Reify
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] {hOrb : ℕ}
  (O : OptimizedStrictNockVMROMPackage F K hOrb)

/-! ## 1. `StrategyOfTracesLift` (frontier module; bridges beside, nothing edited) -/

section Lift

variable (Qc : Fin (ProductionNamedComputeRAP O.family.problem.cfg.compRows_pos O.computeNodes
    O.basis O.computeChallenge O.computePublic O.orbit).rap.w → F[X])
  (c : OptimizedProductionChallengeTuple K F)

theorem famQ_toCD : famQ (toCD O) layout309 c Qc = FamilyEnvCore.familyQc O c Qc := rfl

theorem typedComputeLabelD_toCD (i : Fin O.family.problem.cfg.compRows) :
    typedComputeLabelD (toCD O) layout309 Qc i = StrategyOfTracesLift.typedComputeLabel O Qc i :=
  rfl

theorem typedComputeRowsD_toCD :
    typedComputeRowsD (toCD O) layout309 Qc = StrategyOfTracesLift.typedComputeRows O Qc := rfl

theorem typedComputeForestD_toCD :
    typedComputeForestD (toCD O) layout309 Qc = StrategyOfTracesLift.typedComputeForest O Qc := rfl

theorem typedComputeTreeD_toCD :
    typedComputeTreeD (toCD O) layout309 Qc = StrategyOfTracesLift.typedComputeTree O Qc := rfl

theorem lblCAtD_toCD (i : Fin O.family.problem.cfg.compRows) :
    lblCAtD (toCD O) layout309 c Qc i = StrategyOfTracesLift.lblCAt O Qc c i := rfl

theorem lblCD_toCD : lblCD (toCD O) layout309 c Qc = StrategyOfTracesLift.lblC O Qc c := rfl

theorem foCD_toCD : foCD (toCD O) layout309 c Qc = StrategyOfTracesLift.foC O Qc c := rfl

theorem clabCD_toCD : clabCD (toCD O) layout309 c Qc = StrategyOfTracesLift.clabC O Qc c := rfl

theorem computeLabelListD_toCD :
    computeLabelListD (toCD O) layout309 c Qc = StrategyOfTracesLift.computeLabelList O Qc c := rfl

theorem computeLabelListD_length_toCD :
    (computeLabelListD (toCD O) layout309 c Qc).length = (toCD O).N :=
  computeLabelListD_length (toCD O) layout309 c Qc

theorem cfgOfTracesD_toCD
    (Qm : Fin (namedFinalMemoryRAP O.family.problem.cfg.memRows_pos O.memoryNodes O.basis
      O.memoryChallenge O.memoryPublic O.orbit O.family.problem.cfg.kMem).rap.w → F[X]) :
    cfgOfTracesD (toCD O) layout309 O.family.problem.cfg rfl
        (StrategyOfTracesLift.memoryLabelList O Qm c).length
        (StrategyOfTracesLift.memoryLabelList_length O Qm c) c Qc =
      StrategyOfTracesLift.cfgOfTraces O Qc Qm c := rfl

theorem computeEnvsR0D_toCD :
    computeEnvsR0D (toCD O) layout309 c Qc = StrategyOfTracesR0.computeEnvsR0 O Qc c := rfl

end Lift

/-! ## 2. `StrategyOfTracesR0AC2` -/

section R0AC2

variable (Qc : Fin (ProductionNamedComputeRAP O.family.problem.cfg.compRows_pos O.computeNodes
    O.basis O.computeChallenge O.computePublic O.orbit).rap.w → F[X])
  (c : OptimizedProductionChallengeTuple K F)

theorem c2AxOfD_toCD : c2AxOfD (toCD O) layout309 c Qc = StrategyOfTracesR0AC2.c2AxOf O Qc c := rfl

theorem c2SAtD_toCD (i : Fin O.family.problem.cfg.compRows) :
    c2SAtD (toCD O) layout309 c Qc i = StrategyOfTracesR0AC2.c2SAt O Qc c i := rfl

theorem lblCSD_toCD : lblCSD (toCD O) layout309 c Qc = StrategyOfTracesR0AC2.lblCS O Qc c := rfl

theorem c2TreeOfTracesD_toCD :
    c2TreeOfTracesD (toCD O) layout309 c Qc = StrategyOfTracesR0AC2.c2TreeOfTraces O Qc c := rfl

end R0AC2

/-! ## 3. `StrategyOfTracesEv` (the coin-invariance lemmas, from the twins) -/

section Ev

variable (Qc : Fin (ProductionNamedComputeRAP O.family.problem.cfg.compRows_pos O.computeNodes
    O.basis O.computeChallenge O.computePublic O.orbit).rap.w → F[X])
  (c c' : OptimizedProductionChallengeTuple K F)

theorem inpAtD_toCD : inpAtD (toCD O) layout309 c Qc = StrategyOfTracesEv.inpAt O Qc c := rfl

theorem inpOf_rowEnvAt_of_D (i : Fin O.family.problem.cfg.compRows) :
    inpOf (StrategyOfTracesLift.decodeSource
        (FamilyEnvCore.rowEnvAt O c (FamilyEnvCore.familyQc O c Qc) i)) =
      StrategyOfTracesEv.inpAt O Qc c :=
  inpOf_rowEnvAtD (toCD O) layout309 c Qc i

theorem lblCAt_inputs_of_D (i : Fin O.family.problem.cfg.compRows) :
    (StrategyOfTracesLift.lblCAt O Qc c i).2.1 = StrategyOfTracesEv.inpAt O Qc c :=
  lblCAt_inputsD (toCD O) layout309 c Qc i

theorem lblC_inputs_of_D (i : ℕ) :
    (StrategyOfTracesLift.lblC O Qc c i).2.1 = StrategyOfTracesEv.inpAt O Qc c :=
  lblC_inputsD (toCD O) layout309 c Qc i

theorem computeEnvsR0_trace_of_D (i : Fin O.family.problem.cfg.compRows) :
    (StrategyOfTracesR0.computeEnvsR0 O Qc c i).trace =
      (StrategyOfTracesR0.computeEnvsR0 O Qc c' i).trace :=
  computeEnvsR0_traceD (toCD O) layout309 c c' Qc i

theorem lblC_state_of_D (i : ℕ) :
    (StrategyOfTracesLift.lblC O Qc c i).1 = (StrategyOfTracesLift.lblC O Qc c' i).1 :=
  lblC_stateD (toCD O) layout309 c c' Qc i

theorem c2SAt_eq_of_D (i : Fin O.family.problem.cfg.compRows) :
    StrategyOfTracesR0AC2.c2SAt O Qc c i = StrategyOfTracesR0AC2.c2SAt O Qc c' i :=
  c2SAt_eqD (toCD O) layout309 c c' Qc i

theorem foC_eq_of_D :
    StrategyOfTracesLift.foC O Qc c = StrategyOfTracesLift.foC O Qc c' :=
  foC_eqD (toCD O) layout309 c c' Qc

theorem c2AxOf_eq_of_D :
    StrategyOfTracesR0AC2.c2AxOf O Qc c = StrategyOfTracesR0AC2.c2AxOf O Qc c' :=
  c2AxOf_eqD (toCD O) layout309 c c' Qc

theorem c2TreeOfTraces_proj_of_D :
    mapNTree (fun l : (State × DTcomp K) × ℕ => (l.1.1, l.2))
        (StrategyOfTracesR0AC2.c2TreeOfTraces O Qc c) =
      mapNTree (fun l : (State × DTcomp K) × ℕ => (l.1.1, l.2))
        (StrategyOfTracesR0AC2.c2TreeOfTraces O Qc c') :=
  c2TreeOfTraces_projD (toCD O) layout309 c c' Qc

end Ev

/-! ## 4. `ExecOfTraces` and `OptimizedComputeHostileAccumulator` (the full package `P`) -/

section Full

variable (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X]) (c : OptimizedProductionChallengeTuple K F)

theorem ExecOfTraces_lblCAt_D (i : Fin P.optimized.family.problem.cfg.compRows) :
    ExecOfTraces.lblCAt P Qc c i = lblCAtD (toCD P.optimized) layout309 c Qc i := rfl

theorem ExecOfTraces_lblC_D : ExecOfTraces.lblC P Qc c = lblCD (toCD P.optimized) layout309 c Qc :=
  rfl

theorem ExecOfTraces_foC_D : ExecOfTraces.foC P Qc c = foCD (toCD P.optimized) layout309 c Qc := rfl

theorem ExecOfTraces_computeLabelList_D :
    ExecOfTraces.computeLabelList P Qc c = computeLabelListD (toCD P.optimized) layout309 c Qc :=
  rfl

theorem ExecOfTraces_computeLabelList_length_D :
    (computeLabelListD (toCD P.optimized) layout309 c Qc).length = (toCD P.optimized).N :=
  computeLabelListD_length (toCD P.optimized) layout309 c Qc

theorem ExecOfTraces_lblCAt_eq_rowEnvAt_D (i : Fin P.optimized.family.problem.cfg.compRows) :
    ExecOfTraces.lblCAt P Qc c i =
      (StrategyOfTracesLift.computeStateOf
          (StrategyOfTracesLift.decodeSource
            (rowEnvAtD (toCD P.optimized) c (famQ (toCD P.optimized) layout309 c Qc) i)),
        (StrategyOfTracesLift.decodeInputs
            (rowEnvAtD (toCD P.optimized) c (famQ (toCD P.optimized) layout309 c Qc) i),
          StrategyOfTracesLift.decodePub
            (rowEnvAtD (toCD P.optimized) c (famQ (toCD P.optimized) layout309 c Qc) i)
            (StrategyOfTracesLift.computeStateOf
              (StrategyOfTracesLift.decodeSource
                (rowEnvAtD (toCD P.optimized) c (famQ (toCD P.optimized) layout309 c Qc) i))),
          StrategyOfTracesLift.decodeDec
            (rowEnvAtD (toCD P.optimized) c (famQ (toCD P.optimized) layout309 c Qc) i))) := rfl

theorem rowEnvD_toCD_full (i : Fin P.optimized.family.problem.cfg.compRows) :
    OptimizedComputeHostileAccumulator.rowEnv P Qc i = rowEnvD (toCD P.optimized) Qc i := rfl

theorem rowsD_toCD : OptimizedComputeHostileAccumulator.rows P = rowsD (toCD P.optimized) := rfl

theorem firstRowD_toCD :
    OptimizedComputeHostileAccumulator.firstRow P = firstRowD (toCD P.optimized) := rfl

theorem lastRowD_toCD :
    OptimizedComputeHostileAccumulator.lastRow P = lastRowD (toCD P.optimized) := rfl

theorem hostileRequestsD_toCD :
    OptimizedComputeHostileAccumulator.hostileRequests P Qc =
      hostileRequestsD (toCD P.optimized) layout309 rv309 Qc := rfl


theorem ExecOfTraces_cfgOfTraces_D
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    ExecOfTraces.cfgOfTraces P Qc Qm c =
      cfgOfTracesD (toCD P.optimized) layout309 P.optimized.family.problem.cfg rfl
        (ExecOfTraces.memoryLabelList P Qm c).length
        (ExecOfTraces.memoryLabelList_length P Qm c) c Qc := rfl

end Full

end

end Nock.NockVMROM.Thm54.SVCompute
