/-
  Nock/NockVMROM/Thm54/P8Core/SVCompute/EnvTwins.lean

  **The SHARED compute-half twins of `StrategyOfTracesLift` /
  `ExecOfTraces` / `StrategyOfTracesEv` / `StrategyOfTracesR0AC2` / `OptimizedComputeHostileAccumulator`.**
  Each `<name>D` is stated over `(D : ChipData) (L : ChipLayout)`; the honest trace has the layout
  width (`Qh : Fin L.w → F[X]`) and is re-indexed to the family chip's width by `famQ` (the twin of
  `FamilyEnvCore.familyQc`).  The row decode reads `L.serial` (the B0 row carrier) and the base
  cells; nothing reads a Form R, timestamp or memory constant.  Bridges to the live package-typed
  definitions are `rfl` (see `SVCompute/PkgBridges.lean`).
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesEv
import Nock.NockVMROM.Thm54.P8Core.SVCompute.ChipData

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
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.DecodedLambdaEvent

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] {h : ℕ}
  (D : ChipData F K h) (L : ChipLayout F K h)

/-! ## 0. The re-indexing and the generic gather lemmas -/

/-- The honest trace re-indexed to the family chip's width (`FamilyEnvCore.familyQc`). -/
def famQ (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) :
    Fin (chipOf D L c).rap.w → F[X] :=
  fun j => Qh (Fin.cast (chipOf_w D L c) j)

/-- The generic re-indexing at two widths (`familyQc` at an arbitrary equality). -/
def reindexQ {w w' : ℕ} (hw : w' = w) (Qh : Fin w → F[X]) : Fin w' → F[X] :=
  fun j => Qh (Fin.cast hw j)

omit [FiniteDimensional F K] [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] in
/-- `FamilyEnvCore.gather_toSourceEnv_trace_congr` at a basis (twin). -/
theorem gather_toSourceEnv_trace_congrD (b : Module.Basis (Fin 3) F K) {e e' : Env F}
    (ht : e.trace = e'.trace) :
    (gatherCorrectedFinalTypedEnv b e).toSourceEnv.trace =
      (gatherCorrectedFinalTypedEnv b e').toSourceEnv.trace := by
  funext k
  simp only [CorrectedFinalTypedEnv.toSourceEnv, gatherCorrectedFinalTypedEnv, ht]

/-- The traces of `envOfTrace` do not read the width-index of the type (re-indexed family trace). -/
theorem envTrace_famQ (c c' : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X])
    (ω x : F) (ch pb ch' pb' : ℕ → F) :
    (envOfTrace (famQ D L c Qh) ω x ch pb).trace =
      (envOfTrace (famQ D L c' Qh) ω x ch' pb').trace := by
  funext k
  simp only [envOfTrace]
  by_cases hk : k < L.w
  · have h1 : k < (chipOf D L c).rap.w := by rw [chipOf_w]; exact hk
    have h2 : k < (chipOf D L c').rap.w := by rw [chipOf_w]; exact hk
    rw [dif_pos h1, dif_pos h2]
    rfl
  · have h1 : ¬ k < (chipOf D L c).rap.w := by rw [chipOf_w]; exact hk
    have h2 : ¬ k < (chipOf D L c').rap.w := by rw [chipOf_w]; exact hk
    rw [dif_neg h1, dif_neg h2]

/-! ## 1. `rowEnv`, the labels and the label lists (`StrategyOfTracesLift` §B, `ExecOfTraces`) -/

/-- `OptimizedComputeHostileAccumulator.rowEnv` / `StrategyOfTracesLift.rowEnv`, at the datum. -/
abbrev rowEnvHD (Qh : Fin L.w → F[X]) (i : Fin D.N) : CorrectedFinalTypedEnv F K :=
  rowEnvD D Qh i

/-- `StrategyOfTracesLift.typedComputeLabel` (the honest-chip decode of row `i`). -/
def typedComputeLabelD (Qh : Fin L.w → F[X]) (i : Fin D.N) : State × DTcomp K :=
  open scoped Classical in
  let env := decodeSource (rowEnvD D Qh i)
  let st := computeStateOf env
  (st, (inpOf env, pubOfState env st, decOf env))

/-- `StrategyOfTracesLift.typedComputeRows`. -/
def typedComputeRowsD (Qh : Fin L.w → F[X]) : List (State × DTcomp K) :=
  (List.finRange D.N).map (typedComputeLabelD D L Qh)

open scoped Classical in
/-- `StrategyOfTracesLift.typedComputeForest`. -/
def typedComputeForestD (Qh : Fin L.w → F[X]) : List (NTree (State × DTcomp K)) :=
  match rebuildForest computeFanout 1 (typedComputeRowsD D L Qh) with
  | [] => [.node dummyComputeLabel []]
  | t :: ts => t :: ts

open scoped Classical in
/-- `StrategyOfTracesLift.typedComputeTree`. -/
def typedComputeTreeD (Qh : Fin L.w → F[X]) : NTree (State × DTcomp K) :=
  match typedComputeForestD D L Qh with
  | t :: _ => t
  | [] => .node dummyComputeLabel []

/-- The family `𝕂` source environments the wrap reads (`StrategyOfTracesR0.computeEnvsR0`). -/
def computeEnvsR0D (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) :
    Fin D.N → Env K :=
  fun i => (rowEnvAtD D c (famQ D L c Qh) i).toSourceEnv

/-- `ExecOfTraces.lblCAt`: the decoded label of family row `i`. -/
def lblCAtD (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) (i : Fin D.N) :
    State × DTcomp K :=
  let env := rowEnvAtD D c (famQ D L c Qh) i
  let st := computeStateOf (decodeSource env)
  (st, (decodeInputs env, decodePub env st, decodeDec env))

/-- `ExecOfTraces.lblC`: the 1-indexed label (`lblC`'s off-range convention). -/
def lblCD (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) :
    ℕ → State × DTcomp K :=
  fun i =>
    if hi : i - 1 < D.N then lblCAtD D L c Qh ⟨i - 1, hi⟩
    else lblCAtD D L c Qh ⟨0, D.hN⟩

/-- `ExecOfTraces.foC`. -/
def foCD (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) : ℕ → ℕ :=
  fun i => fanoutComp (lblCD D L c Qh i).1

/-- `ExecOfTraces.clabC`. -/
def clabCD (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) (i j : ℕ) :
    Option (State × DTcomp K) :=
  let parent := lblCD D L c Qh i
  if hj : j < foCD D L c Qh i then
    have hj3 : j < 3 :=
      Nat.lt_of_lt_of_le hj ((comp_stateSep (K := K)).fanout_le parent.1)
    let trip := sfTriple parent.2.2.1 ⟨j, hj3⟩
    some (parent.1,
      (parent.2.1,
        { parent.2.2.1 with s := trip.1, f := trip.2.1, e := trip.2.2 },
        parent.2.2.2))
  else
    none

/-- `ExecOfTraces.computeLabelList`. -/
def computeLabelListD (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) :
    List (State × DTcomp K) :=
  (List.finRange D.N).map (lblCAtD D L c Qh)

/-- `ExecOfTraces.computeLabelList_length`. -/
theorem computeLabelListD_length (c : OptimizedProductionChallengeTuple K F)
    (Qh : Fin L.w → F[X]) : (computeLabelListD D L c Qh).length = D.N := by
  simp [computeLabelListD]

/-- `ExecOfTraces.cfgOfTraces`, over the package's base configuration `cfg` (the memory half
`kMem` / `Ksz` / `memRows` is read off `cfg` and `mr`, the memory label count, behind the package
projection; the compute half is the datum's). -/
def cfgOfTracesD (cfg : ExactConfig F K) (hN : D.N = cfg.compRows) (mr : ℕ)
    (hmr : mr = cfg.memRows) (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) :
    ExactConfig F K where
  challenges :=
    { a := c.2.2.1.eqA
      b := c.2.2.1.eqB
      c := c.2.2.1.eqC
      α := alphaM c.1
      z := nprSeed c.1
      β := -(c.2.2.2.interPole)
      γ := c.2.1.1
      lam := c.2.2.2.lambda }
  Ksz := cfg.Ksz
  kMem := cfg.kMem
  orbit := cfg.orbit
  orbit_h_pos := cfg.orbit_h_pos
  compRows := (computeLabelListD D L c Qh).length
  memRows := mr
  compRows_pos := by
    rw [computeLabelListD_length, hN]
    exact cfg.compRows_pos
  memRows_pos := by
    rw [hmr]
    exact cfg.memRows_pos
  compRows_le := by
    rw [computeLabelListD_length, hN]
    exact cfg.compRows_le
  memRows_le := by
    rw [hmr]
    exact cfg.memRows_le
  eDeg := cfg.eDeg
  eDeg_eq_one := cfg.eDeg_eq_one
  compNodes := fun i => cfg.orbit.βcoset * cfg.orbit.ω ^ (i : ℕ)
  compNodes_spec := fun i => rfl
  memNodes := fun i => cfg.orbit.βcoset * cfg.orbit.ω ^ (i : ℕ)
  memNodes_spec := fun i => rfl

theorem cfgOfTracesD_compRows (cfg : ExactConfig F K) (hN : D.N = cfg.compRows) (mr : ℕ)
    (hmr : mr = cfg.memRows) (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) :
    (cfgOfTracesD D L cfg hN mr hmr c Qh).compRows = D.N :=
  computeLabelListD_length D L c Qh

/-! ## 2. The carrier decode (`StrategyOfTracesR0AC2`) -/

/-- `StrategyOfTracesR0AC2.c2AxOf`: the record axis of an exponent on the family source envs. -/
def c2AxOfD (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) : ℕ → ℕ :=
  fun e => certAxisOfEnvs (computeEnvsR0D D L c Qh) e

/-- `StrategyOfTracesR0AC2.c2SAt`: the round-0 carrier of row `i`, read at the layout's serial
column (`302` at `layout309`). -/
def c2SAtD (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) (i : Fin D.N) : ℕ :=
  RecordCarrier.natLift ((computeEnvsR0D D L c Qh i).trace (L.serial : ℕ))

/-- `StrategyOfTracesR0AC2.lblCS`: the label with its carrier attached. -/
def lblCSD (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) :
    ℕ → (State × DTcomp K) × ℕ :=
  fun i =>
    (lblCD D L c Qh i,
      if hi : i - 1 < D.N then c2SAtD D L c Qh ⟨i - 1, hi⟩ else c2SAtD D L c Qh ⟨0, D.hN⟩)

/-- `StrategyOfTracesR0AC2.c2TreeOfTraces`: the S-carrying exec tree. -/
def c2TreeOfTracesD (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) :
    NTree ((State × DTcomp K) × ℕ) :=
  reconTree (foCD D L c Qh) (lblCSD D L c Qh) D.N

/-! ## 3. The inputs record and the coin-invariance lemmas (`StrategyOfTracesEv`) -/

/-- `StrategyOfTracesEv.inpAt`. -/
def inpAtD (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) :
    ComputeTable.Inputs K :=
  inpOf (decodeSource (rowEnvAtD D c (famQ D L c Qh) ⟨0, D.hN⟩))

theorem inpOf_rowEnvAtD (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X])
    (i : Fin D.N) :
    inpOf (decodeSource (rowEnvAtD D c (famQ D L c Qh) i)) = inpAtD D L c Qh := by
  unfold inpAtD
  simp only [inpOf, decodeSource, Env.ofSubst, computeSubst, Expr.eval,
    CorrectedFinalTypedEnv.toSourceEnv, rowEnvAtD, gatherCorrectedFinalTypedEnv, envOfTrace]

theorem lblCAt_inputsD (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X])
    (i : Fin D.N) : (lblCAtD D L c Qh i).2.1 = inpAtD D L c Qh :=
  inpOf_rowEnvAtD D L c Qh i

theorem lblC_inputsD (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X])
    (i : ℕ) : (lblCD D L c Qh i).2.1 = inpAtD D L c Qh := by
  unfold lblCD
  split_ifs <;> exact lblCAt_inputsD D L c Qh _

/-- The round-0 compute envs' traces do not read the tuple. -/
theorem computeEnvsR0_traceD (c c' : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X])
    (i : Fin D.N) :
    (computeEnvsR0D D L c Qh i).trace = (computeEnvsR0D D L c' Qh i).trace := by
  unfold computeEnvsR0D rowEnvAtD
  exact gather_toSourceEnv_trace_congrD D.basis (envTrace_famQ D L c c' Qh _ _ _ _ _ _)

/-- The decoded compute state does not read the tuple. -/
theorem lblC_stateD (c c' : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X])
    (i : ℕ) : (lblCD D L c Qh i).1 = (lblCD D L c' Qh i).1 := by
  unfold lblCD
  split_ifs <;>
  · unfold lblCAtD
    exact computeStateOf_decodeSource_congr (computeEnvsR0_traceD D L c c' Qh _)

/-- The round-0 record carrier `S` does not read the tuple. -/
theorem c2SAt_eqD (c c' : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X])
    (i : Fin D.N) : c2SAtD D L c Qh i = c2SAtD D L c' Qh i := by
  unfold c2SAtD
  rw [computeEnvsR0_traceD D L c c' Qh i]

theorem foC_eqD (c c' : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) :
    foCD D L c Qh = foCD D L c' Qh := by
  funext i
  unfold foCD
  rw [lblC_stateD D L c c' Qh i]

theorem c2AxOf_eqD (c c' : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X]) :
    c2AxOfD D L c Qh = c2AxOfD D L c' Qh := by
  funext e
  exact certAxisOfEnvs_congr (fun i => computeEnvsR0_traceD D L c c' Qh i) e

/-- The `(state, S)` projection of the S-carrying exec tree does not read the tuple. -/
theorem c2TreeOfTraces_projD (c c' : OptimizedProductionChallengeTuple K F)
    (Qh : Fin L.w → F[X]) :
    mapNTree (fun l : (State × DTcomp K) × ℕ => (l.1.1, l.2)) (c2TreeOfTracesD D L c Qh) =
      mapNTree (fun l : (State × DTcomp K) × ℕ => (l.1.1, l.2)) (c2TreeOfTracesD D L c' Qh) := by
  unfold c2TreeOfTracesD reconTree
  rw [mapNTree_buildT', mapNTree_buildT', foC_eqD D L c c' Qh]
  congr 1
  funext j
  unfold lblCSD
  split_ifs
  · rw [lblC_stateD D L c c' Qh j, c2SAt_eqD D L c c' Qh]
  · rw [lblC_stateD D L c c' Qh j, c2SAt_eqD D L c c' Qh]

/-- `ExecOfTraces.lblCAt_eq_rowEnvAt`-shaped: the label's decoded state is the state of the gathered
family row. -/
theorem lblCAtD_fst (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X])
    (i : Fin D.N) :
    (lblCAtD D L c Qh i).1 = computeStateOf (decodeSource (rowEnvAtD D c (famQ D L c Qh) i)) := rfl

/-! ## 4. The accumulator rows (`OptimizedComputeHostileAccumulator`) -/

/-- `OptimizedComputeHostileAccumulator.rows`. -/
abbrev rowsD : ℕ := D.N

/-- `OptimizedComputeHostileAccumulator.firstRow`. -/
abbrev firstRowD : Fin D.N := ⟨0, D.hN⟩

/-- `OptimizedComputeHostileAccumulator.lastRow`. -/
abbrev lastRowD : Fin D.N := ⟨D.N - 1, Nat.sub_lt D.hN (by omega)⟩

/-- **A record view**: how a typed row environment reads its request-slot records (width `m`) and
activity masks.  `rv309` is the deployed width-10 record. -/
structure RecordView (F K : Type) [Field F] [Field K] [Algebra F K] where
  m : ℕ
  record : CorrectedFinalTypedEnv F K → Fin 3 → Fin m → K
  mask : CorrectedFinalTypedEnv F K → Fin 3 → K

/-- The deployed width-10 record and its activity masks. -/
def rv309 : RecordView F K where
  m := 10
  record := OptimizedComputeHostileAccumulator.rowRecord
  mask := OptimizedComputeHostileAccumulator.activeMask

/-- The active-slot records of one row at a record view (`rowRequests`). -/
def RecordView.requests (RV : RecordView F K) (env : CorrectedFinalTypedEnv F K) :
    List (Fin RV.m → K) :=
  (List.finRange 3).filterMap fun j => if RV.mask env j = 1 then some (RV.record env j) else none

/-- `OptimizedComputeHostileAccumulator.hostileRequests`, at the datum and a record view. -/
def hostileRequestsD (RV : RecordView F K) (Qh : Fin L.w → F[X]) : List (Fin RV.m → K) :=
  (List.ofFn fun i : Fin D.N => RV.requests (rowEnvD D Qh i)).flatten

theorem rv309_requests (env : CorrectedFinalTypedEnv F K) :
    (rv309 (F := F) (K := K)).requests env = OptimizedComputeHostileAccumulator.rowRequests env :=
  rfl

end

end Nock.NockVMROM.Thm54.SVCompute
