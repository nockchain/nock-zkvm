/-
  Nock/RedTeam/Batch1680Thm54SVComputeRoute2.lean

`P8Core/SVCompute/*` (all new):
  * `ChipData` — `ChipData`, `SharedGateSet`, `ChipLayout`
    (`w`, `colRound`, `base : 13 ≤ w`, `role`, `nRoles`, `serial`, `serial_round0`, `gates`, plus the
    builder `build` and the three facts a builder supplies: `build_w`, `sat_iff`, `masks_of_bind`),
    `chipOf`, `layout309` (the live package chip, physical width `303`, serial `302`), `layoutVCL` (a
    STUB for V4), `toCD`, `rowEnvAtD`, `rowEnvD`, `RowFacts` (+ `RowFacts.of_sat`);
  * `EnvTwins` — the Lift / ExecOfTraces / Ev / R0AC2 / HostileAccumulator compute halves
    (`lblCAtD`, `lblCD`, `foCD`, `clabCD`, `computeLabelListD`, `cfgOfTracesD`, `typedCompute*D`,
    `c2AxOfD`, `c2SAtD` (reads `L.serial`), `lblCSD`, `c2TreeOfTracesD`, `inpAtD`, the coin-invariance
    lemmas, `rowsD`, `firstRowD`, `lastRowD`, `hostileRequestsD` at a `RecordView`, `rv309`);
  * `PkgBridges` — every definition bridge `rfl` at `toCD O`, `layout309`;
  * `ChainTwins` / `ChainBridges` — `FamilyIOChain` chain skeletons at `(D, L)` and as corollaries;

Asserted here (the build fails otherwise):
  * every SHARED twin named below exists and its axioms are `{propext, Classical.choice,
    Quot.sound}` (`collectAxioms` over the whole `SVCompute` namespace, no `sorryAx`);
  * `layout309.GatesOK D` is discharged for every `D` (`layout309_gatesOK`), and the layout premises
    of the twins (`63 ≤ nRoles`, `serial = computeExpCol`, `SerialIsExp`) by `le_refl` / `rfl`;
-/
import Nock.NockVMROM.Thm54.P8Core.SVCompute.TopoBridges

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Lean Nock Nock.Reified Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.SVCompute
open scoped Polynomial

namespace Nock.RedTeam.Batch1680

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (O : OptimizedStrictNockVMROMPackage F K hOrb)

/-! ## 1. Fingerprint replicas of five frontier defs and one non-frontier def -/

/-- Verbatim replica of `FamilyEnvCore.rowEnvAt`. -/
def rowEnvAt_r (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (DeployedChipFamily.computeChipAt O.family.problem.cfg.compRows_pos O.computeNodes
      O.basis (computePublicOfTuple O.basis O.verifier.raw.claim O.computePublic c) O.orbit c).rap.w
      → F[X])
    (i : Fin O.family.problem.cfg.compRows) : CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv O.basis
    (envOfTrace Qc O.orbit.ω (O.computeNodes i)
      (computeChalValOfTuple O.basis c)
      (computePublicOfTuple O.basis O.verifier.raw.claim O.computePublic c))

/-- The wrapper of `FamilyEnvCore.rowEnvAt` through the route-2 twin at `layout309`. -/
def rowEnvAt_w (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (DeployedChipFamily.computeChipAt O.family.problem.cfg.compRows_pos O.computeNodes
      O.basis (computePublicOfTuple O.basis O.verifier.raw.claim O.computePublic c) O.orbit c).rap.w
      → F[X])
    (i : Fin O.family.problem.cfg.compRows) : CorrectedFinalTypedEnv F K :=
  rowEnvAtD (toCD O) c Qc i

theorem rowEnvAt_w_eq (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (DeployedChipFamily.computeChipAt O.family.problem.cfg.compRows_pos O.computeNodes
      O.basis (computePublicOfTuple O.basis O.verifier.raw.claim O.computePublic c) O.orbit c).rap.w
      → F[X])
    (i : Fin O.family.problem.cfg.compRows) :
    rowEnvAt_w O c Qc i = FamilyEnvCore.rowEnvAt O c Qc i := rfl

/-- Verbatim replica of `FamilyEnvCore.familyQc`. -/
def familyQc_r (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (ProductionNamedComputeRAP O.family.problem.cfg.compRows_pos O.computeNodes O.basis
      O.computeChallenge O.computePublic O.orbit).rap.w → F[X]) :
    Fin (DeployedChipFamily.computeChipAt O.family.problem.cfg.compRows_pos O.computeNodes
      O.basis (computePublicOfTuple O.basis O.verifier.raw.claim O.computePublic c) O.orbit c).rap.w
      → F[X] :=
  fun j => Qc (Fin.cast (FamilyEnvCore.computeChipAt_width O c) j)

def familyQc_w (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (ProductionNamedComputeRAP O.family.problem.cfg.compRows_pos O.computeNodes O.basis
      O.computeChallenge O.computePublic O.orbit).rap.w → F[X]) :
    Fin (DeployedChipFamily.computeChipAt O.family.problem.cfg.compRows_pos O.computeNodes
      O.basis (computePublicOfTuple O.basis O.verifier.raw.claim O.computePublic c) O.orbit c).rap.w
      → F[X] :=
  famQ (toCD O) layout309 c Qc

theorem familyQc_w_eq (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (ProductionNamedComputeRAP O.family.problem.cfg.compRows_pos O.computeNodes O.basis
      O.computeChallenge O.computePublic O.orbit).rap.w → F[X]) :
    familyQc_w O c Qc = FamilyEnvCore.familyQc O c Qc := rfl

variable (Qc : Fin (ProductionNamedComputeRAP O.family.problem.cfg.compRows_pos O.computeNodes
    O.basis O.computeChallenge O.computePublic O.orbit).rap.w → F[X])
  (c : OptimizedProductionChallengeTuple K F)

/-- Verbatim replica of `StrategyOfTracesR0AC2.c2SAt`. -/
def c2SAt_r (i : Fin O.family.problem.cfg.compRows) : ℕ :=
  RecordCarrier.natLift ((StrategyOfTracesR0.computeEnvsR0 O Qc c i).trace 302)

def c2SAt_w (i : Fin O.family.problem.cfg.compRows) : ℕ :=
  c2SAtD (toCD O) layout309 c Qc i

theorem c2SAt_w_eq (i : Fin O.family.problem.cfg.compRows) :
    c2SAt_w O Qc c i = StrategyOfTracesR0AC2.c2SAt O Qc c i := rfl

/-- Verbatim replica of `StrategyOfTracesR0AC2.c2AxOf`. -/
def c2AxOf_r : ℕ → ℕ := fun e =>
  StrategyOfTracesR0.certAxisOfEnvs (StrategyOfTracesR0.computeEnvsR0 O Qc c) e

def c2AxOf_w : ℕ → ℕ := c2AxOfD (toCD O) layout309 c Qc

theorem c2AxOf_w_eq : c2AxOf_w O Qc c = StrategyOfTracesR0AC2.c2AxOf O Qc c := rfl

/-- Verbatim replica of `StrategyOfTracesR0AC2.c2TreeOfTraces`. -/
def c2TreeOfTraces_r : Nock.Walk.NTree ((Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K) × ℕ) :=
  Nock.Walk.reconTree (StrategyOfTracesLift.foC O Qc c) (StrategyOfTracesR0AC2.lblCS O Qc c)
    O.family.problem.cfg.compRows

def c2TreeOfTraces_w : Nock.Walk.NTree ((Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K) × ℕ) :=
  c2TreeOfTracesD (toCD O) layout309 c Qc

theorem c2TreeOfTraces_w_eq :
    c2TreeOfTraces_w O Qc c = StrategyOfTracesR0AC2.c2TreeOfTraces O Qc c := rfl

/-- Verbatim replica of `StrategyOfTracesLift.lblCAt` (NOT on the frontier). -/
def lblCAt_r (i : Fin O.family.problem.cfg.compRows) :
    Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K :=
  let env := FamilyEnvCore.rowEnvAt O c (FamilyEnvCore.familyQc O c Qc) i
  let st := StrategyOfTracesLift.computeStateOf (StrategyOfTracesLift.decodeSource env)
  (st, (StrategyOfTracesLift.decodeInputs env, StrategyOfTracesLift.decodePub env st,
    StrategyOfTracesLift.decodeDec env))

def lblCAt_w (i : Fin O.family.problem.cfg.compRows) :
    Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K :=
  lblCAtD (toCD O) layout309 c Qc i

theorem lblCAt_w_eq (i : Fin O.family.problem.cfg.compRows) :
    lblCAt_w O Qc c i = StrategyOfTracesLift.lblCAt O Qc c i := rfl

end

end Nock.RedTeam.Batch1680

/-- Normalised hash: module-local `_proof_*` auxiliaries replaced by one placeholder. -/
def normHash1680 (e : Lean.Expr) : UInt64 :=
  (e.replace fun x => match x with
    | .const n _ => match n with
      | .str _ s => if s.startsWith "_proof" then some (.const `AUXPROOF []) else none
      | _ => none
    | _ => none).hash

run_cmd do
  let env ← Lean.getEnv
  let B := `Nock.RedTeam.Batch1680
  let T := `Nock.NockVMROM.Thm54
  -- (live, replica, wrapper, onFrontier)
  for (o, r, w, fr) in [
      (T ++ `FamilyEnvCore.rowEnvAt, B ++ `rowEnvAt_r, B ++ `rowEnvAt_w, true),
      (T ++ `FamilyEnvCore.familyQc, B ++ `familyQc_r, B ++ `familyQc_w, true),
      (T ++ `StrategyOfTracesR0AC2.c2SAt, B ++ `c2SAt_r, B ++ `c2SAt_w, true),
      (T ++ `StrategyOfTracesR0AC2.c2AxOf, B ++ `c2AxOf_r, B ++ `c2AxOf_w, true),
      (T ++ `StrategyOfTracesR0AC2.c2TreeOfTraces, B ++ `c2TreeOfTraces_r, B ++ `c2TreeOfTraces_w, true),
      (T ++ `StrategyOfTracesLift.lblCAt, B ++ `lblCAt_r, B ++ `lblCAt_w, false)] do
    let v := fun n => normHash1680 ((env.find? n).get!.value!)
    let t := fun n => normHash1680 ((env.find? n).get!.type)
    unless t o == t r && t o == t w do throwError "type hash mismatch at {o}: live {t o} replica {t r} wrapper {t w}"
    unless v o == v r do throwError "replica control failed at {o}"
    if v o == v w then throwError "wrapper did not change the value hash at {o}"
    Lean.logInfo m!"{o} (frontier: {fr}): live = replica {v o}; wrapper {v w} (moves)"

/-! ## 2. The SHARED coverage table against `classify2.log` -/

run_cmd do
  let env ← Lean.getEnv
  let T := `Nock.NockVMROM.Thm54
  let R := `Nock.RedTeam
  let S := `Nock.NockVMROM.Thm54.SVCompute
  -- (SHARED parent, covering twin)
  let table : List (Name × Name) := [
    (T ++ `ExecOfTraces.cfgOfTraces, S ++ `cfgOfTracesD),
    (T ++ `ExecOfTraces.computeLabelList, S ++ `computeLabelListD),
    (T ++ `ExecOfTraces.computeLabelList_length, S ++ `computeLabelListD_length),
    (T ++ `ExecOfTraces.foC, S ++ `foCD),
    (T ++ `ExecOfTraces.lblC, S ++ `lblCD),
    (T ++ `ExecOfTraces.lblCAt, S ++ `lblCAtD),
    (T ++ `ExecOfTraces.lblCAt_eq_rowEnvAt, S ++ `ExecOfTraces_lblCAt_eq_rowEnvAt_D),
    (T ++ `FamilyEnvCore.familyQc, S ++ `famQ),
    (T ++ `FamilyEnvCore.gather_toSourceEnv_trace_congr, S ++ `gather_toSourceEnv_trace_congrD),
    (T ++ `FamilyIOChain.acc_eq_prefixSum_at, S ++ `acc_eq_prefixSum_atD),
    (T ++ `FamilyIOChain.chain_at_at, S ++ `chain_at_atD),
    (T ++ `FamilyIOChain.expCol_eq_prefixExp_at, S ++ `expCol_eq_prefixExp_atD),
    (T ++ `FamilyIOChain.expCol_step_at, S ++ `expCol_step_atD),
    (T ++ `FamilyIOChain.ln_chain_at_at, S ++ `ln_chain_at_atD),
    (T ++ `FamilyIOChain.lnPrev_at_at, S ++ `lnPrev_at_atD),
    (T ++ `FamilyIOChain.next_acc_at, S ++ `next_acc_atD),
    (T ++ `FamilyIOChain.totalRequestsAt_le, S ++ `totalRequestsAt_leD),
    (T ++ `OptimizedComputeHostileAccumulator.firstRow, S ++ `firstRowD),
    (T ++ `OptimizedComputeHostileAccumulator.hostileRequests, S ++ `hostileRequestsD),
    (T ++ `OptimizedComputeHostileAccumulator.lastRow, S ++ `lastRowD),
    (T ++ `OptimizedComputeHostileAccumulator.rowEnv, S ++ `rowEnvD),
    (T ++ `OptimizedComputeHostileAccumulator.rows, S ++ `rowsD),
    (T ++ `StrategyOfTracesEv.c2AxOf_eq, S ++ `c2AxOf_eqD),
    (T ++ `StrategyOfTracesEv.c2SAt_eq, S ++ `c2SAt_eqD),
    (T ++ `StrategyOfTracesEv.c2TreeOfTraces_proj, S ++ `c2TreeOfTraces_projD),
    (T ++ `StrategyOfTracesEv.computeEnvsR0_trace, S ++ `computeEnvsR0_traceD),
    (T ++ `StrategyOfTracesEv.foC_eq, S ++ `foC_eqD),
    (T ++ `StrategyOfTracesEv.inpAt, S ++ `inpAtD),
    (T ++ `StrategyOfTracesEv.inpOf_rowEnvAt, S ++ `inpOf_rowEnvAtD),
    (T ++ `StrategyOfTracesEv.lblCAt_inputs, S ++ `lblCAt_inputsD),
    (T ++ `StrategyOfTracesEv.lblC_inputs, S ++ `lblC_inputsD),
    (T ++ `StrategyOfTracesEv.lblC_state, S ++ `lblC_stateD),
    (T ++ `StrategyOfTracesLift.cfgOfTraces, S ++ `cfgOfTracesD),
    (T ++ `StrategyOfTracesLift.clabC, S ++ `clabCD),
    (T ++ `StrategyOfTracesLift.computeLabelList, S ++ `computeLabelListD),
    (T ++ `StrategyOfTracesLift.computeLabelList_length, S ++ `computeLabelListD_length),
    (T ++ `StrategyOfTracesLift.foC, S ++ `foCD),
    (T ++ `StrategyOfTracesLift.lblC, S ++ `lblCD),
    (T ++ `StrategyOfTracesLift.lblCAt, S ++ `lblCAtD),
    (T ++ `StrategyOfTracesLift.rowEnv, S ++ `rowEnvD),
    (T ++ `StrategyOfTracesLift.typedComputeForest, S ++ `typedComputeForestD),
    (T ++ `StrategyOfTracesLift.typedComputeLabel, S ++ `typedComputeLabelD),
    (T ++ `StrategyOfTracesLift.typedComputeRows, S ++ `typedComputeRowsD),
    (T ++ `StrategyOfTracesLift.typedComputeTree, S ++ `typedComputeTreeD),
    (T ++ `StrategyOfTracesR0AC2.c2AxOf, S ++ `c2AxOfD),
    (T ++ `StrategyOfTracesR0AC2.c2SAt, S ++ `c2SAtD),
    (T ++ `StrategyOfTracesR0AC2.c2TreeOfTraces, S ++ `c2TreeOfTracesD),
    (T ++ `StrategyOfTracesR0AC2.lblCS, S ++ `lblCSD),
    (T ++ `WalkQueueDeployed.deployed_bfsValid, S ++ `deployed_bfsValidD),
    (R ++ `Batch1140.rowIdx, S ++ `rowIdxD),
    (R ++ `Batch1172.lblCS_succ_fst, S ++ `lblCS_succ_fstD),
    (R ++ `Batch459.deployed_walkSat, S ++ `deployed_walkSatD),
    (R ++ `Batch459.notLast_at, S ++ `notLast_walkD),
    (R ++ `Batch459.rowOf, S ++ `rowOfD),
    (R ++ `Batch459.rowOf_one, S ++ `rowOf_oneD),
    (R ++ `Batch459.rowOf_rows, S ++ `rowOf_rowsD),
    (R ++ `Batch459.rowOf_succ, S ++ `rowOf_succD),
    (R ++ `Batch465.chldOf_eq_chldW, S ++ `chldOf_eq_chldWD),
    (R ++ `Batch465.curOf_eq_curW, S ++ `curOf_eq_curWD),
    (R ++ `Batch465.familyRow_trace_eq, S ++ `familyRow_trace_eqD),
    (R ++ `Batch465.familyRow_traceNext_eq, S ++ `familyRow_traceNext_eqD),
    (R ++ `Batch465.foOf_eq_foW, S ++ `foOf_eq_foWD),
    (R ++ `Batch471.Vd, S ++ `VdD),
    (R ++ `Batch471.lblC_state, S ++ `lblC_state'D),
    (R ++ `Batch500.Cvd_eq_committed, S ++ `Cvd_eq_committedD),
    (R ++ `Batch500.Vd_eq_committed, S ++ `Vd_eq_committedD),
    (R ++ `Batch823.computePrefix_eq, S ++ `computePrefix_eqD)]
  for (live, twin) in table do
    unless env.contains live do throwError "SHARED name missing from the environment: {live}"
    unless env.contains twin do throwError "twin missing: {twin} (for {live})"
  -- the four SHARED parents with NO twin (reported, not covered)
  let gap : List Name := [
    T ++ `FamilyIOChain.hostile_intermediate_telescopes_at,
    T ++ `StrategyOfTracesLift.family_kMem_pos,
    R ++ `Batch1172.pos_of_pr,
    R ++ `Batch1172.prefix_eq]
  for g in gap do
    unless env.contains g do throwError "gap name missing from the environment: {g}"
  Lean.logInfo m!"SHARED parents covered by a twin: {table.length} of {table.length + gap.length}; gap: {gap}"
  -- every route-2 declaration is kernel-clean
  let mut n : Nat := 0
  for (nm, ci) in env.constants.toList do
    if S.isPrefixOf nm && !nm.isInternal then
      match ci with
      | .thmInfo _ | .defnInfo _ =>
        let axs ← Lean.collectAxioms nm
        for a in axs do
          unless a == `propext || a == `Classical.choice || a == `Quot.sound do
            throwError "{nm} depends on the axiom {a}"
        n := n + 1
      | _ => pure ()
  Lean.logInfo m!"SVCompute declarations checked kernel-clean: {n}"

namespace Nock.RedTeam.Batch1680

open Nock.NockVMROM.Thm54.SVCompute

#print axioms chipOf_toCD_layout309
#print axioms rowEnvAtD_toCD
#print axioms rowFacts_toCD
#print axioms layout309_gatesOK
#print axioms layoutVCL
#print axioms lblCAtD_toCD
#print axioms cfgOfTracesD_toCD
#print axioms lblC_stateD
#print axioms c2TreeOfTraces_projD
#print axioms chain_at_atD
#print axioms acc_eq_prefixSum_atD
#print axioms lnPrev_at_atD
#print axioms expCol_eq_prefixExp_atD
#print axioms totalRequestsAt_leD
#print axioms deployed_walkSatD
#print axioms deployed_walkSatD
#print axioms deployed_bfsValidD
#print axioms curOf_eq_curWD
#print axioms Vd_eq_committedD
#print axioms deployed_walkSat_lblCD
#print axioms computePrefix_eqD
#print axioms lblCS_succ_fstD
#print axioms deployed_walkSat_of_D
#print axioms chain_at_at_of_D
#print axioms expCol_eq_prefixExp_at_of_D

/-- The deployed layout's gate premise holds for every datum, by `simp` (`gates309_sub`). -/
example {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] {h : ℕ} (D : ChipData F K h) :
    (layout309 (F := F) (K := K) (h := h)).GatesOK D := layout309_gatesOK D

end Nock.RedTeam.Batch1680
