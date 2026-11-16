/-
  Nock/NockVMROM/Thm54/StrategyOfTracesLift.lean

  **H1.5b Part 2b-i — `strategyOfTraces` / `TracesWalkHyps` lifted below the pinned file**
.

  2b-ii restores the target field `p8 : ∃ h : TracesWalkHyps …, (strategyOfTraces … h).Accepts …`
  in the pinned `OptimizedStrictFullPackage.lean`.  The originals sit ABOVE the pinned file
  (`ExecOfTraces`, `StrategyOfTracesCore`, `StrategyOfTraces`, `DeployedComputeRows`,
  `FamilyComputeRows`, `OptimizedComputeHostileAccumulator`), so the pinned file cannot name them
.  This module restates every constant of their closure that is defined
  in a module importing the pinned file, following 2a's `FamilyEnvCore` pattern:

  * every definition is **re-parameterised over `O : OptimizedStrictNockVMROMPackage F K hOrb`**
    (the package's `optimized` field); the pinned abbrevs `computeChip` / `memoryChip` / `objects`
    are unfolded through local notation, the pinned defs `memorySourceTrace` / `memoryBaseEnv` /
    `memorySourceEnv` are restated here, and the family env layer is `FamilyEnvCore`'s
;
  * the full-package field `stateTagChar` is an **explicit hypothesis** `tag` of the definitions
    that read it (`familyDataOfTraces` and everything built on it);
  * nothing here mentions `OptimizedFullStrictNockVMROMPackage`, and nothing imported here
    imports the pinned file.

  The originals stay; nothing is re-pointed.  `Nock/RedTeam/Batch940Thm54LiftStrategyReceipts.lean`
  proves every lifted name `rfl`-equal to its original at `O := P.optimized`, `tag := P.stateTagChar`
  (`TracesWalkHyps`, an inductive, by a constructor-wise iff; see there).

  Paper: the paper (inverse BFS), `:1413`, `:1450` (Thm 5.4), `:1690` (`sfTriple`),
  `:1728-1742` (`V_comp`), `:2031` (`memCell`), `:2049-2088` (`V_mem`).
-/
import Nock.Walk
import Nock.NockVM
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.FamilyEnvCore
import Nock.NockVMROM.Thm54.ComputeEnvAgreement
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding
import Nock.NockVMROM.Thm54.HostileRecordLists
import Nock.NockVMROM.Thm54.PreZCensusCore
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.ProductionRawVerifier
import Nock.NockVMROM.Thm54.NodeEncoding
import Nock.NockVMROM.Thm54.RawTopologyAIR
import Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
import Nock.NockVMROM.Thm54.PlusIOSegmentedRAP
import Nock.NockVMROM.Thm54.JointCoins
import Nock.Framework.NockInstances
import Nock.GlobalCarryRecognizer
import Mathlib.GroupTheory.OrderOfElement

namespace Nock.NockVMROM.Thm54.StrategyOfTracesLift

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionRawVerifier
open Nock.NockVMROM.Thm54.RawTopologyAIR
open Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.StrategyOfTraces
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

/-! ## The pinned abbrevs, unfolded (notation only; no new constants) -/

set_option quotPrecheck false

/-- `P.computeChip` at `O := P.optimized`. -/
local notation "CC[" O "]" =>
  ProductionNamedComputeRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.compRows_pos
    (OptimizedStrictNockVMROMPackage.computeNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.computeChallenge O)
    (OptimizedStrictNockVMROMPackage.computePublic O) (OptimizedStrictNockVMROMPackage.orbit O)

/-- `P.memoryChip` at `O := P.optimized`. -/
local notation "MC[" O "]" =>
  namedFinalMemoryRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.memoryChallenge O)
    (OptimizedStrictNockVMROMPackage.memoryPublic O) (OptimizedStrictNockVMROMPackage.orbit O)
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem

/-- The named source memory RAP at `O` (the pinned `memorySourceTrace`'s projection data). -/
local notation "NSM[" O "]" =>
  (namedSourceMemoryRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.memoryChallenge O)
    (OptimizedStrictNockVMROMPackage.memoryPublic O) (OptimizedStrictNockVMROMPackage.orbit O)
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem)

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-! ## §A  Package-free helpers (copied verbatim from the modules above the pin)

`DeployedComputeRows` (decoders), `StrategyOfTraces` §0/§1/§3/§4 (dummies, BFS inverse, the noun
join), `StrategyOfTracesCore` (`memExponent`, the label wraps). -/

/-- `DeployedComputeRows.decodeSource`. -/
def decodeSource (env : CorrectedFinalTypedEnv F K) : Env K :=
  Env.ofSubst computeSubst env.toSourceEnv

/-- `DeployedComputeRows.decodeInputs`. -/
def decodeInputs (env : CorrectedFinalTypedEnv F K) : ComputeTable.Inputs K :=
  inpOf (decodeSource env)

/-- `DeployedComputeRows.decodePub`. -/
def decodePub (env : CorrectedFinalTypedEnv F K) (st : State) : ComputeTable.Pub K :=
  pubOfState (decodeSource env) st

/-- `DeployedComputeRows.decodeDec`. -/
def decodeDec (env : CorrectedFinalTypedEnv F K) : ComputeTable.Dec K :=
  decOf (decodeSource env)

/-- `DeployedComputeRows.decodeEx`. -/
def decodeEx (env : CorrectedFinalTypedEnv F K) : ComputeTable.Extra K :=
  exOf (decodeSource env)

open scoped Classical in
/-- `StrategyOfTraces.dummyMemRec`. -/
def dummyMemRec : MemRecSkeleton where
  root := Noun.atom 0
  child := Noun.atom 0
  axis := 0

open scoped Classical in
/-- `StrategyOfTraces.dummyComputeRow`. -/
def dummyComputeRow : ComputeRowSkeleton where
  state := .s0
  subject := Noun.atom 0
  formula := Noun.atom 0
  evaluation := Noun.atom 0
  decomposition := fun _ _ => Noun.atom 0
  subformula := fun i hi _ => False.elim (by
    have : (i : ℕ) < fanoutComp .s0 := hi
    simp [fanoutComp] at this)
  memoryRecord := fun _ _ => dummyMemRec

open scoped Classical in
/-- `StrategyOfTraces.dummyDTmem`. -/
def dummyDTmem : MemoryTable.DTmem K :=
  ({ z := 0, β := 0, γ := 0 },
    { st := .halt
      pt := Cell.zero
      lc := Cell.zero
      rc := Cell.zero
      lcSt := .halt
      rcSt := .halt
      mem := MemRec.zero
      ipre := 0
      icur := 0 })

open scoped Classical in
/-- `StrategyOfTraces.dummyMemoryLabel`. -/
def dummyMemoryLabel : MemoryTable.MState × MemoryTable.DTmem K :=
  (.halt, dummyDTmem)

open scoped Classical in
/-- `StrategyOfTraces.dummyComputeLabel`. -/
def dummyComputeLabel : ComputeTable.State × ComputeTable.DTcomp K :=
  (.s0,
    ({ α := 0, z := 0, a := 0, b := 0, c := 0 },
      { state := .s0
        s := 0
        f := 0
        e := 0
        sf1_s := 0
        sf1_f := 0
        sf1_e := 0
        sf2_s := 0
        sf2_f := 0
        sf2_e := 0
        sf3_s := 0
        sf3_f := 0
        sf3_e := 0
        ln_prev := 0
        ln := 0
        mr1 := MemRec.zero
        mr2 := MemRec.zero
        mr3 := MemRec.zero },
      { f_h := 0, f_t := 0, f_th := 0, f_tt := 0, f_tth := 0, f_ttt := 0 }))

open scoped Classical in
/-- `StrategyOfTraces.groupChildren`. -/
def groupChildren {α : Type} :
    List ℕ → List (NTree α) → List (List (NTree α)) × List (NTree α)
  | [], kids => ([], kids)
  | f :: fs, kids =>
      let mine := kids.take f
      let rest := kids.drop f
      let more := groupChildren fs rest
      (mine :: more.1, more.2)

open scoped Classical in
/-- `StrategyOfTraces.unbfs`. -/
def unbfs {α : Type} (fanout : α → ℕ) :
    ℕ → List α → List α → List (NTree α)
  | 0, _, _ => []
  | _fuel + 1, [], _ => []
  | fuel + 1, level, rest =>
      let nCh := (level.map fanout).sum
      let childLabels := rest.take nCh
      let rest' := rest.drop nCh
      let childTrees := unbfs fanout fuel childLabels rest'
      let grouped := (groupChildren (level.map fanout) childTrees).1
      (level.zip grouped).map fun p => NTree.node p.1 p.2

open scoped Classical in
/-- `StrategyOfTraces.rebuildForest`. -/
def rebuildForest {α : Type} (fanout : α → ℕ) (kRoots : ℕ) (rows : List α) :
    List (NTree α) :=
  unbfs fanout (rows.length + 1) (rows.take kRoots) (rows.drop kRoots)

open scoped Classical in
/-- `StrategyOfTraces.computeStateOf`. -/
def computeStateOf (env : Env K) : State :=
  if env.trace 1 = 1 then .s1
  else if env.trace 2 = 1 then .s2
  else if env.trace 3 = 1 then .s3
  else if env.trace 4 = 1 then .s4
  else if env.trace 5 = 1 then .s5
  else if env.trace 6 = 1 then .s6
  else if env.trace 7 = 1 then .s7
  else if env.trace 8 = 1 then .s8
  else if env.trace 9 = 1 then .s9
  else if env.trace 10 = 1 then .cons
  else .s0

open scoped Classical in
/-- `StrategyOfTraces.memoryPtNoun`. -/
def memoryPtNoun (envK : Env K) : FP K :=
  ⟨envK.trace 0, envK.trace 1, envK.trace 2⟩

open scoped Classical in
/-- `StrategyOfTraces.memoryMemRoot`. -/
def memoryMemRoot (envK : Env K) : FP K :=
  ⟨envK.trace 19, envK.trace 20, envK.trace 21⟩

open scoped Classical in
/-- `StrategyOfTraces.memoryMemChild`. -/
def memoryMemChild (envK : Env K) : FP K :=
  ⟨envK.trace 22, envK.trace 23, envK.trace 24⟩

open scoped Classical in
/-- `StrategyOfTraces.computeFanout`. -/
def computeFanout : (State × DTcomp K) → ℕ
  | (st, _) => fanoutComp st

open scoped Classical in
/-- `StrategyOfTraces.memoryFanout`. -/
def memoryFanout : (MState × DTmem K) → ℕ
  | (st, _) => fanoutMem st

open scoped Classical in
/-- `StrategyOfTraces.nounByFP`. -/
def nounByFP (q : ℕ)
    (forest : List (NTree (MState × DTmem K))) (fp : FP K) : Noun :=
  match (bfsForest forest).find? (fun t => t.label.2.2.pt.noun = fp) with
  | some t => decodeNoun q t
  | none => Noun.atom 0

open scoped Classical in
/-- `StrategyOfTraces.memRecJoin`. -/
def memRecJoin (q : ℕ)
    (forest : List (NTree (MState × DTmem K))) (mr : MemRec K) :
    MemRecSkeleton where
  root := StrategyOfTracesLift.nounByFP q forest mr.root
  child := StrategyOfTracesLift.nounByFP q forest mr.child
  axis := leafAtomOf q mr.axis

open scoped Classical in
/-- `StrategyOfTraces.kidSkel`. -/
def kidSkel (kids : List ComputeRowSkeleton) (i : ℕ) : ComputeRowSkeleton :=
  kids[i]?.getD dummyComputeRow

open scoped Classical in
/-- `StrategyOfTraces.joinNoun`. -/
def joinNoun (q : ℕ) (z : K)
    (forest : List (NTree (MState × DTmem K))) (fp : FP K) : Noun :=
  if fp.size = z ∧ fp.dyck = 0 then
    Noun.atom (leafAtomOf q fp.leaf)
  else
    StrategyOfTracesLift.nounByFP q forest fp

open scoped Classical in
/-- `StrategyOfTraces.nounHead`. -/
def nounHead : Noun → Noun
  | .cell h _ => h
  | n => n

open scoped Classical in
/-- `StrategyOfTraces.nounTail`. -/
def nounTail : Noun → Noun
  | .cell _ t => t
  | n => n

open scoped Classical in
/-- `StrategyOfTraces.joinEvaluation`. -/
def joinEvaluation (q : ℕ)
    (forest : List (NTree (MState × DTmem K)))
    (formula : Noun)
    (row : State × DTcomp K)
    (kids : List ComputeRowSkeleton) : Noun :=
  match row.1 with
  | .cons => .cell (kidSkel kids 0).evaluation (kidSkel kids 1).evaluation
  | .s1 => nounTail formula
  | .s3 => Noun.wut (kidSkel kids 0).evaluation
  | .s4 =>
      match (kidSkel kids 0).evaluation with
      | .atom k => .atom (k + 1)
      | c => c
  | .s5 => Noun.tis (kidSkel kids 0).evaluation (kidSkel kids 1).evaluation
  | .s2 => (kidSkel kids 2).evaluation
  | .s6 | .s7 | .s8 => (kidSkel kids 0).evaluation
  | .s9 => (kidSkel kids 1).evaluation
  | .s0 => StrategyOfTracesLift.nounByFP q forest row.2.2.1.e

open scoped Classical in
/-- `StrategyOfTraces.computeSkeletonRow`. -/
def computeSkeletonRow (q : ℕ)
    (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun)
    (row : State × DTcomp K)
    (kids : List ComputeRowSkeleton) : ComputeRowSkeleton :=
  let st := row.1
  let pub := row.2.2.1
  let dec := row.2.2.2
  let fh := nounHead formula
  let ft := nounTail formula
  let fth := nounHead ft
  let ftt := nounTail ft
  let ftth := nounHead ftt
  let fttt := nounTail ftt
  { state := st
    subject := subj
    formula := formula
    evaluation := joinEvaluation q forest formula row kids
    decomposition := fun slot _ =>
      match slot with
      | .f_h => fh
      | .f_t => ft
      | .f_th => fth
      | .f_tt => ftt
      | .f_tth => ftth
      | .f_ttt => fttt
    subformula := fun i _hi slot =>
      if h : (i : ℕ) < kids.length then
        match slot with
        | .subject => (kids[(i : ℕ)]'h).subject
        | .formula => (kids[(i : ℕ)]'h).formula
        | .result => (kids[(i : ℕ)]'h).evaluation
      else
        Noun.atom 0
    memoryRecord := fun i _ =>
      match st, i.val with
      | _, 0 => ⟨formula, ft, 3⟩
      | .s0, 1 => ⟨subj, joinEvaluation q forest formula row kids, leafAtomOf q dec.f_t.leaf⟩
      | .s2, 1 | .s5, 1 | .s7, 1 | .s8, 1 | .s9, 1 => ⟨ft, fth, 2⟩
      | .s6, 1 => ⟨ft, fth, 2⟩
      | .s6, 2 => ⟨ftt, ftth, 2⟩
      | .s9, 2 =>
          ⟨(kidSkel kids 0).evaluation, (kidSkel kids 1).formula, leafAtomOf q dec.f_th.leaf⟩
      | _, _ => StrategyOfTracesLift.memRecJoin q forest (computeMemRec pub i) }

open scoped Classical in
/-- MIG 4.35: the children of `mapComputeJoinInFuel` at one row, with the recursive call `f` as a parameter.
Non-recursive; split out so the kernel checks the per-opcode match outside the structural recursion (4.35 reports
deep recursion on the inlined form). `mapComputeJoinInFuel_succ` restates the original body. -/
def mapComputeJoinKids (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (f : NTree (State × DTcomp K) → Noun → Noun → NTree ComputeRowSkeleton)
    (row : State × DTcomp K) (ch : List (NTree (State × DTcomp K))) (subj formula : Noun) :
    List (NTree ComputeRowSkeleton) :=
  match row.1, ch with
  | .s0, [] => []
  | .s1, [] => []
  | .cons, [c0, c1] =>
      [f c0 subj (nounHead formula),
       f c1 subj (nounTail formula)]
  | .s3, [c0] =>
      [f c0 subj (nounTail formula)]
  | .s4, [c0] =>
      [f c0 subj (nounTail formula)]
  | .s5, [c0, c1] =>
      [f c0 subj (nounHead (nounTail formula)),
       f c1 subj (nounTail (nounTail formula))]
  | .s2, [c0, c1, c2] =>
      let s0 := f c0 subj
        (nounHead (nounTail formula))
      let s1 := f c1 subj
        (nounTail (nounTail formula))
      [s0, s1, f c2
        s0.label.evaluation s1.label.evaluation]
  | .s6, [c0, c1] =>
      let fth := nounHead (nounTail formula)
      let ftth := nounHead (nounTail (nounTail formula))
      let fttt := nounTail (nounTail (nounTail formula))
      let sCond := f c1 subj fth
      let b :=
        match sCond.label.evaluation with
        | .atom k => k
        | _ => 0
      [f c0 subj
        (if b = 0 then ftth else fttt), sCond]
  | .s7, [c0, c1] =>
      let fth := nounHead (nounTail formula)
      let ftt := nounTail (nounTail formula)
      let sHelp := f c1 subj fth
      [f c0 sHelp.label.evaluation ftt, sHelp]
  | .s8, [c0, c1] =>
      let fth := nounHead (nounTail formula)
      let ftt := nounTail (nounTail formula)
      let sHelp := f c1 subj fth
      [f c0
        (Noun.cell sHelp.label.evaluation subj) ftt, sHelp]
  | .s9, [c0, c1] =>
      let coreF := nounTail (nounTail formula)
      let sCore := f c0 subj coreF
      let arm := StrategyOfTracesLift.joinNoun q row.2.1.z forest row.2.2.1.sf2_f
      [sCore, f c1 sCore.label.evaluation arm]
  | _, ch' =>
      ch'.map fun c => f c subj formula

open scoped Classical in
/-- `StrategyOfTraces.mapComputeJoinInFuel`. -/
def mapComputeJoinInFuel (fuel : ℕ) (q : ℕ)
    (forest : List (NTree (MState × DTmem K)))
    (t : NTree (State × DTcomp K)) (subj formula : Noun) :
    NTree ComputeRowSkeleton :=
  match fuel, t with
  | 0, .node row _ =>
      .node (computeSkeletonRow q forest subj formula row []) []
  | n + 1, .node row ch =>
      let kids : List (NTree ComputeRowSkeleton) :=
        mapComputeJoinKids q forest (fun c s fo => mapComputeJoinInFuel n q forest c s fo) row ch subj formula
      .node (computeSkeletonRow q forest subj formula row (kids.map NTree.label)) kids

attribute [simp] mapComputeJoinKids

open scoped Classical in
/-- MIG 4.35: the successor unfolding of `mapComputeJoinInFuel` through `mapComputeJoinKids` (`rfl`). -/
theorem mapComputeJoinInFuel_succ (n q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (row : State × DTcomp K) (ch : List (NTree (State × DTcomp K))) (subj formula : Noun) :
    mapComputeJoinInFuel (n + 1) q forest (.node row ch) subj formula =
      .node (computeSkeletonRow q forest subj formula row
          ((mapComputeJoinKids q forest (fun c s fo => mapComputeJoinInFuel n q forest c s fo) row ch subj
            formula).map NTree.label))
        (mapComputeJoinKids q forest (fun c s fo => mapComputeJoinInFuel n q forest c s fo) row ch subj formula) :=
  rfl

open scoped Classical in
/-- MIG 4.35: the 4.31 auto-generated equation `mapComputeJoinInFuel.eq_1`, verbatim, at the re-encoded def. -/
theorem mapComputeJoinInFuel_eq_1_old : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (q : ℕ)
  (forest : List (Nock.Walk.NTree (Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K))) (subj formula : Nock.Noun)
  (row : Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)
  (children : List (Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K))),
  mapComputeJoinInFuel 0 q forest (Nock.Walk.NTree.node row children) subj formula =
    Nock.Walk.NTree.node (computeSkeletonRow q forest subj formula row []) [] := by
  intros; rfl

open scoped Classical in
/-- MIG 4.35: the 4.31 auto-generated equation `mapComputeJoinInFuel.eq_2`, verbatim, at the re-encoded def. -/
theorem mapComputeJoinInFuel_eq_2_old : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (q : ℕ)
  (forest : List (Nock.Walk.NTree (Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K))) (subj formula : Nock.Noun)
  (n : ℕ) (row : Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K),
  row.1 = Nock.ComputeTable.State.s0 →
    mapComputeJoinInFuel n.succ q forest (Nock.Walk.NTree.node row []) subj formula =
      Nock.Walk.NTree.node (computeSkeletonRow q forest subj formula row (List.map Nock.Walk.NTree.label [])) [] := by
  intros
  rw [mapComputeJoinInFuel.eq_2]
  unfold mapComputeJoinKids
  split <;> simp_all

open scoped Classical in
/-- MIG 4.35: the 4.31 auto-generated equation `mapComputeJoinInFuel.eq_3`, verbatim, at the re-encoded def. -/
theorem mapComputeJoinInFuel_eq_3_old : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (q : ℕ)
  (forest : List (Nock.Walk.NTree (Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K))) (subj formula : Nock.Noun)
  (n : ℕ) (row : Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K),
  row.1 = Nock.ComputeTable.State.s1 →
    mapComputeJoinInFuel n.succ q forest (Nock.Walk.NTree.node row []) subj formula =
      Nock.Walk.NTree.node (computeSkeletonRow q forest subj formula row (List.map Nock.Walk.NTree.label [])) [] := by
  intros
  rw [mapComputeJoinInFuel.eq_2]
  unfold mapComputeJoinKids
  split <;> simp_all

open scoped Classical in
/-- MIG 4.35: the 4.31 auto-generated equation `mapComputeJoinInFuel.eq_4`, verbatim, at the re-encoded def. -/
theorem mapComputeJoinInFuel_eq_4_old : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (q : ℕ)
  (forest : List (Nock.Walk.NTree (Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K))) (subj formula : Nock.Noun)
  (n : ℕ) (row : Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)
  (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
  row.1 = Nock.ComputeTable.State.cons →
    mapComputeJoinInFuel n.succ q forest (Nock.Walk.NTree.node row [c0, c1]) subj formula =
      Nock.Walk.NTree.node
        (computeSkeletonRow q forest subj formula row
          (List.map Nock.Walk.NTree.label
            [mapComputeJoinInFuel n q forest c0 subj (nounHead formula),
              mapComputeJoinInFuel n q forest c1 subj (nounTail formula)]))
        [mapComputeJoinInFuel n q forest c0 subj (nounHead formula),
          mapComputeJoinInFuel n q forest c1 subj (nounTail formula)] := by
  intros
  rw [mapComputeJoinInFuel.eq_2]
  unfold mapComputeJoinKids
  split <;> simp_all

open scoped Classical in
/-- MIG 4.35: the 4.31 auto-generated equation `mapComputeJoinInFuel.eq_5`, verbatim, at the re-encoded def. -/
theorem mapComputeJoinInFuel_eq_5_old : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (q : ℕ)
  (forest : List (Nock.Walk.NTree (Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K))) (subj formula : Nock.Noun)
  (n : ℕ) (row : Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)
  (c0 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
  row.1 = Nock.ComputeTable.State.s3 →
    mapComputeJoinInFuel n.succ q forest (Nock.Walk.NTree.node row [c0]) subj formula =
      Nock.Walk.NTree.node
        (computeSkeletonRow q forest subj formula row
          (List.map Nock.Walk.NTree.label [mapComputeJoinInFuel n q forest c0 subj (nounTail formula)]))
        [mapComputeJoinInFuel n q forest c0 subj (nounTail formula)] := by
  intros
  rw [mapComputeJoinInFuel.eq_2]
  unfold mapComputeJoinKids
  split <;> simp_all

open scoped Classical in
/-- MIG 4.35: the 4.31 auto-generated equation `mapComputeJoinInFuel.eq_6`, verbatim, at the re-encoded def. -/
theorem mapComputeJoinInFuel_eq_6_old : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (q : ℕ)
  (forest : List (Nock.Walk.NTree (Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K))) (subj formula : Nock.Noun)
  (n : ℕ) (row : Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)
  (c0 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
  row.1 = Nock.ComputeTable.State.s4 →
    mapComputeJoinInFuel n.succ q forest (Nock.Walk.NTree.node row [c0]) subj formula =
      Nock.Walk.NTree.node
        (computeSkeletonRow q forest subj formula row
          (List.map Nock.Walk.NTree.label [mapComputeJoinInFuel n q forest c0 subj (nounTail formula)]))
        [mapComputeJoinInFuel n q forest c0 subj (nounTail formula)] := by
  intros
  rw [mapComputeJoinInFuel.eq_2]
  unfold mapComputeJoinKids
  split <;> simp_all

open scoped Classical in
/-- MIG 4.35: the 4.31 auto-generated equation `mapComputeJoinInFuel.eq_7`, verbatim, at the re-encoded def. -/
theorem mapComputeJoinInFuel_eq_7_old : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (q : ℕ)
  (forest : List (Nock.Walk.NTree (Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K))) (subj formula : Nock.Noun)
  (n : ℕ) (row : Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)
  (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
  row.1 = Nock.ComputeTable.State.s5 →
    mapComputeJoinInFuel n.succ q forest (Nock.Walk.NTree.node row [c0, c1]) subj formula =
      Nock.Walk.NTree.node
        (computeSkeletonRow q forest subj formula row
          (List.map Nock.Walk.NTree.label
            [mapComputeJoinInFuel n q forest c0 subj (nounHead (nounTail formula)),
              mapComputeJoinInFuel n q forest c1 subj (nounTail (nounTail formula))]))
        [mapComputeJoinInFuel n q forest c0 subj (nounHead (nounTail formula)),
          mapComputeJoinInFuel n q forest c1 subj (nounTail (nounTail formula))] := by
  intros
  rw [mapComputeJoinInFuel.eq_2]
  unfold mapComputeJoinKids
  split <;> simp_all

open scoped Classical in
/-- MIG 4.35: the 4.31 auto-generated equation `mapComputeJoinInFuel.eq_8`, verbatim, at the re-encoded def. -/
theorem mapComputeJoinInFuel_eq_8_old : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (q : ℕ)
  (forest : List (Nock.Walk.NTree (Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K))) (subj formula : Nock.Noun)
  (n : ℕ) (row : Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)
  (c0 c1 c2 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
  row.1 = Nock.ComputeTable.State.s2 →
    mapComputeJoinInFuel n.succ q forest (Nock.Walk.NTree.node row [c0, c1, c2]) subj formula =
      Nock.Walk.NTree.node
        (computeSkeletonRow q forest subj formula row
          (List.map Nock.Walk.NTree.label
            (have s0 := mapComputeJoinInFuel n q forest c0 subj (nounHead (nounTail formula));
            have s1 := mapComputeJoinInFuel n q forest c1 subj (nounTail (nounTail formula));
            [s0, s1, mapComputeJoinInFuel n q forest c2 s0.label.evaluation s1.label.evaluation])))
        (have s0 := mapComputeJoinInFuel n q forest c0 subj (nounHead (nounTail formula));
        have s1 := mapComputeJoinInFuel n q forest c1 subj (nounTail (nounTail formula));
        [s0, s1, mapComputeJoinInFuel n q forest c2 s0.label.evaluation s1.label.evaluation]) := by
  intros
  rw [mapComputeJoinInFuel.eq_2]
  unfold mapComputeJoinKids
  split <;> simp_all

open scoped Classical in
/-- MIG 4.35: the 4.31 auto-generated equation `mapComputeJoinInFuel.eq_9`, verbatim, at the re-encoded def. -/
theorem mapComputeJoinInFuel_eq_9_old : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (q : ℕ)
  (forest : List (Nock.Walk.NTree (Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K))) (subj formula : Nock.Noun)
  (n : ℕ) (row : Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)
  (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
  row.1 = Nock.ComputeTable.State.s6 →
    mapComputeJoinInFuel n.succ q forest (Nock.Walk.NTree.node row [c0, c1]) subj formula =
      Nock.Walk.NTree.node
        (computeSkeletonRow q forest subj formula row
          (List.map Nock.Walk.NTree.label
            (let fth := nounHead (nounTail formula);
            have ftth := nounHead (nounTail (nounTail formula));
            have fttt := nounTail (nounTail (nounTail formula));
            let sCond := mapComputeJoinInFuel n q forest c1 subj fth;
            let b :=
              match sCond.label.evaluation with
              | Nock.Noun.atom k => k
              | x => 0;
            [mapComputeJoinInFuel n q forest c0 subj (if b = 0 then ftth else fttt), sCond])))
        (let fth := nounHead (nounTail formula);
        have ftth := nounHead (nounTail (nounTail formula));
        have fttt := nounTail (nounTail (nounTail formula));
        let sCond := mapComputeJoinInFuel n q forest c1 subj fth;
        let b :=
          match sCond.label.evaluation with
          | Nock.Noun.atom k => k
          | x => 0;
        [mapComputeJoinInFuel n q forest c0 subj (if b = 0 then ftth else fttt), sCond]) := by
  intros
  rw [mapComputeJoinInFuel.eq_2]
  unfold mapComputeJoinKids
  split <;> simp_all

open scoped Classical in
/-- MIG 4.35: the 4.31 auto-generated equation `mapComputeJoinInFuel.eq_10`, verbatim, at the re-encoded def. -/
theorem mapComputeJoinInFuel_eq_10_old : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (q : ℕ)
  (forest : List (Nock.Walk.NTree (Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K))) (subj formula : Nock.Noun)
  (n : ℕ) (row : Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)
  (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
  row.1 = Nock.ComputeTable.State.s7 →
    mapComputeJoinInFuel n.succ q forest (Nock.Walk.NTree.node row [c0, c1]) subj formula =
      Nock.Walk.NTree.node
        (computeSkeletonRow q forest subj formula row
          (List.map Nock.Walk.NTree.label
            (have fth := nounHead (nounTail formula);
            have ftt := nounTail (nounTail formula);
            have sHelp := mapComputeJoinInFuel n q forest c1 subj fth;
            [mapComputeJoinInFuel n q forest c0 sHelp.label.evaluation ftt, sHelp])))
        (have fth := nounHead (nounTail formula);
        have ftt := nounTail (nounTail formula);
        have sHelp := mapComputeJoinInFuel n q forest c1 subj fth;
        [mapComputeJoinInFuel n q forest c0 sHelp.label.evaluation ftt, sHelp]) := by
  intros
  rw [mapComputeJoinInFuel.eq_2]
  unfold mapComputeJoinKids
  split <;> simp_all

open scoped Classical in
/-- MIG 4.35: the 4.31 auto-generated equation `mapComputeJoinInFuel.eq_11`, verbatim, at the re-encoded def. -/
theorem mapComputeJoinInFuel_eq_11_old : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (q : ℕ)
  (forest : List (Nock.Walk.NTree (Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K))) (subj formula : Nock.Noun)
  (n : ℕ) (row : Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)
  (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
  row.1 = Nock.ComputeTable.State.s8 →
    mapComputeJoinInFuel n.succ q forest (Nock.Walk.NTree.node row [c0, c1]) subj formula =
      Nock.Walk.NTree.node
        (computeSkeletonRow q forest subj formula row
          (List.map Nock.Walk.NTree.label
            (have fth := nounHead (nounTail formula);
            have ftt := nounTail (nounTail formula);
            have sHelp := mapComputeJoinInFuel n q forest c1 subj fth;
            [mapComputeJoinInFuel n q forest c0 (sHelp.label.evaluation.cell subj) ftt, sHelp])))
        (have fth := nounHead (nounTail formula);
        have ftt := nounTail (nounTail formula);
        have sHelp := mapComputeJoinInFuel n q forest c1 subj fth;
        [mapComputeJoinInFuel n q forest c0 (sHelp.label.evaluation.cell subj) ftt, sHelp]) := by
  intros
  rw [mapComputeJoinInFuel.eq_2]
  unfold mapComputeJoinKids
  split <;> simp_all

open scoped Classical in
/-- MIG 4.35: the 4.31 auto-generated equation `mapComputeJoinInFuel.eq_12`, verbatim, at the re-encoded def. -/
theorem mapComputeJoinInFuel_eq_12_old : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (q : ℕ)
  (forest : List (Nock.Walk.NTree (Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K))) (subj formula : Nock.Noun)
  (n : ℕ) (row : Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)
  (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
  row.1 = Nock.ComputeTable.State.s9 →
    mapComputeJoinInFuel n.succ q forest (Nock.Walk.NTree.node row [c0, c1]) subj formula =
      Nock.Walk.NTree.node
        (computeSkeletonRow q forest subj formula row
          (List.map Nock.Walk.NTree.label
            (have coreF := nounTail (nounTail formula);
            have sCore := mapComputeJoinInFuel n q forest c0 subj coreF;
            have arm := joinNoun q row.2.1.z forest row.2.2.1.sf2_f;
            [sCore, mapComputeJoinInFuel n q forest c1 sCore.label.evaluation arm])))
        (have coreF := nounTail (nounTail formula);
        have sCore := mapComputeJoinInFuel n q forest c0 subj coreF;
        have arm := joinNoun q row.2.1.z forest row.2.2.1.sf2_f;
        [sCore, mapComputeJoinInFuel n q forest c1 sCore.label.evaluation arm]) := by
  intros
  rw [mapComputeJoinInFuel.eq_2]
  unfold mapComputeJoinKids
  split <;> simp_all

open scoped Classical in
/-- MIG 4.35: the 4.31 auto-generated equation `mapComputeJoinInFuel.eq_13`, verbatim, at the re-encoded def. -/
theorem mapComputeJoinInFuel_eq_13_old : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (q : ℕ)
  (forest : List (Nock.Walk.NTree (Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K))) (subj formula : Nock.Noun)
  (n : ℕ) (row : Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)
  (ch : List (Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K))),
  (row.1 = Nock.ComputeTable.State.s0 → ch = [] → False) →
    (row.1 = Nock.ComputeTable.State.s1 → ch = [] → False) →
      (∀ (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
          row.1 = Nock.ComputeTable.State.cons → ch = [c0, c1] → False) →
        (∀ (c0 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
            row.1 = Nock.ComputeTable.State.s3 → ch = [c0] → False) →
          (∀ (c0 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
              row.1 = Nock.ComputeTable.State.s4 → ch = [c0] → False) →
            (∀ (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
                row.1 = Nock.ComputeTable.State.s5 → ch = [c0, c1] → False) →
              (∀ (c0 c1 c2 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
                  row.1 = Nock.ComputeTable.State.s2 → ch = [c0, c1, c2] → False) →
                (∀ (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
                    row.1 = Nock.ComputeTable.State.s6 → ch = [c0, c1] → False) →
                  (∀ (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
                      row.1 = Nock.ComputeTable.State.s7 → ch = [c0, c1] → False) →
                    (∀ (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
                        row.1 = Nock.ComputeTable.State.s8 → ch = [c0, c1] → False) →
                      (∀ (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × Nock.ComputeTable.DTcomp K)),
                          row.1 = Nock.ComputeTable.State.s9 → ch = [c0, c1] → False) →
                        mapComputeJoinInFuel n.succ q forest (Nock.Walk.NTree.node row ch) subj formula =
                          Nock.Walk.NTree.node
                            (computeSkeletonRow q forest subj formula row
                              (List.map Nock.Walk.NTree.label
                                (List.map (fun c => mapComputeJoinInFuel n q forest c subj formula) ch)))
                            (List.map (fun c => mapComputeJoinInFuel n q forest c subj formula) ch) := by
  intros
  rw [mapComputeJoinInFuel.eq_2]
  unfold mapComputeJoinKids
  split <;> simp_all

open scoped Classical in
/-- `StrategyOfTraces.mapComputeJoinIn`. -/
def mapComputeJoinIn (q : ℕ)
    (forest : List (NTree (MState × DTmem K)))
    (t : NTree (State × DTcomp K)) (subj formula : Noun) :
    NTree ComputeRowSkeleton :=
  mapComputeJoinInFuel t.size q forest t subj formula

open scoped Classical in
/-- `StrategyOfTraces.joinFormulaDeep`. -/
def joinFormulaDeep (q : ℕ)
    (forest : List (NTree (MState × DTmem K)))
    (t : NTree (State × DTcomp K)) : Noun :=
  let z := t.label.2.1.z
  let dec := t.label.2.2.2
  match t with
  | .node row ch =>
      match row.1, ch with
      | .cons, [c0, c1] =>
          .cell (joinFormulaDeep q forest c0) (joinFormulaDeep q forest c1)
      | .s0, [] => .cell (.atom 0) (StrategyOfTracesLift.joinNoun q z forest dec.f_t)
      | .s1, [] => .cell (.atom 1) (StrategyOfTracesLift.joinNoun q z forest dec.f_t)
      | .s3, [c0] => .cell (.atom 3) (joinFormulaDeep q forest c0)
      | .s4, [c0] => .cell (.atom 4) (joinFormulaDeep q forest c0)
      | .s5, [c0, c1] =>
          .cell (.atom 5)
            (.cell (joinFormulaDeep q forest c0) (joinFormulaDeep q forest c1))
      | .s2, [c0, c1, c2] =>
          .cell (.atom 2)
            (.cell (joinFormulaDeep q forest c0) (joinFormulaDeep q forest c1))
      | .s6, [c0, c1] =>
          .cell (.atom 6)
            (.cell (joinFormulaDeep q forest c1)
              (.cell (StrategyOfTracesLift.joinNoun q z forest dec.f_tth)
                (StrategyOfTracesLift.joinNoun q z forest dec.f_ttt)))
      | .s7, [c0, c1] =>
          .cell (.atom 7)
            (.cell (joinFormulaDeep q forest c1) (joinFormulaDeep q forest c0))
      | .s8, [c0, c1] =>
          .cell (.atom 8)
            (.cell (joinFormulaDeep q forest c1) (joinFormulaDeep q forest c0))
      | .s9, [c0, c1] =>
          .cell (.atom 9)
            (.cell (.atom (leafAtomOf q dec.f_th.leaf))
              (joinFormulaDeep q forest c0))
      | _, _ =>
          .cell (StrategyOfTracesLift.joinNoun q z forest dec.f_h)
            (StrategyOfTracesLift.joinNoun q z forest dec.f_t)

open scoped Classical in
/-- `StrategyOfTraces.mapComputeJoin`. -/
def mapComputeJoin (q : ℕ)
    (forest : List (NTree (MState × DTmem K)))
    (t : NTree (State × DTcomp K)) : NTree ComputeRowSkeleton :=
  let z := t.label.2.1.z
  let pub := t.label.2.2.1
  mapComputeJoinIn q forest t
    (StrategyOfTracesLift.joinNoun q z forest pub.s)
    (joinFormulaDeep q forest t)

open scoped Classical in
/-- `StrategyOfTraces.configTemplateOf`. -/
def configTemplateOf (cfg : ExactConfig F K) (z : K) : ExactConfigTemplate F K where
  challenges :=
    { a := cfg.challenges.a
      b := cfg.challenges.b
      c := cfg.challenges.c
      z := z
      β := cfg.challenges.β
      γ := cfg.challenges.γ }
  Ksz := cfg.Ksz
  kMem := cfg.kMem
  orbit := cfg.orbit
  orbit_h_pos := cfg.orbit_h_pos
  compRows := cfg.compRows
  memRows := cfg.memRows
  compRows_pos := cfg.compRows_pos
  memRows_pos := cfg.memRows_pos
  compRows_le := cfg.compRows_le
  memRows_le := cfg.memRows_le
  eDeg := cfg.eDeg
  eDeg_eq_one := cfg.eDeg_eq_one
  compNodes := cfg.compNodes
  compNodes_spec := cfg.compNodes_spec
  memNodes := cfg.memNodes
  memNodes_spec := cfg.memNodes_spec

/-- `StrategyOfTracesCore.wrapComputeLabel`. -/
def wrapComputeLabel (row : State × DTcomp K) : ComputeRowTemplate (K := K) where
  timestamp :=
    { state := row.1
      lnPrevExponent := 0
      lnExponent := Nock.Framework.recordCount row.1
      recordExponent := fun i => (i : ℕ) + 1 }
  placeholder := row

/-- `StrategyOfTracesCore.memExponent`. -/
noncomputable def memExponent (α ts : K) : ℕ :=
  if h : ∃ n : ℕ, n < orderOf α ∧ α ^ n = ts then
    Nat.find h
  else 0

/-- `StrategyOfTracesCore.wrapMemoryLabel`. -/
def wrapMemoryLabel (α : K)
    (row : MState × DTmem K) : MemoryRowTemplate (K := K) where
  timestamp :=
    { state := row.1
      recordExponent := StrategyOfTracesLift.memExponent α row.2.2.mem.ts }
  placeholder := row

/-! ## §B  The package layer, over `O` -/

variable (O : OptimizedStrictNockVMROMPackage F K hOrb)

/-- The pinned `OptimizedFullStrictNockVMROMPackage.memorySourceTrace` at `O := P.optimized`. -/
def memorySourceTrace
    (Qm : Fin (MC[O]).rap.w → F[X]) : Fin 182 → F[X] :=
  RAPPadding.projectTrace (NSM[O]).rap
    (RAPPadding.firstRoundExtra (NSM[O]).rap (NSM[O]).rounds_pos
      (RAPPadding.memoryResidualColumns 3)) Qm

/-- The pinned `OptimizedFullStrictNockVMROMPackage.memoryBaseEnv` at `O := P.optimized`. -/
def memoryBaseEnv
    (Qm : Fin (MC[O]).rap.w → F[X])
    (i : Fin O.family.problem.cfg.memRows) : Env F :=
  envOfTrace (memorySourceTrace O Qm) O.orbit.ω
    (O.memoryNodes i) O.memoryChallenge O.memoryPublic

/-- The pinned `OptimizedFullStrictNockVMROMPackage.memorySourceEnv` at `O := P.optimized`. -/
def memorySourceEnv
    (Qm : Fin (MC[O]).rap.w → F[X])
    (i : Fin O.family.problem.cfg.memRows) : Env K :=
  gatherEnv O.basis ((memorySourceTemplate O.basis).col0 3)
    (memoryBaseEnv O Qm i)

/-- `OptimizedComputeHostileAccumulator.rowEnv` at `O := P.optimized`. -/
abbrev rowEnv (Qc : Fin (CC[O]).rap.w → F[X])
    (i : Fin O.family.problem.cfg.compRows) : CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv O.basis
    (envOfTrace Qc O.orbit.ω (O.computeNodes i)
      O.computeChallenge O.computePublic)

/-! ### `StrategyOfTraces` §2–§4 over `O` -/

open scoped Classical in
/-- `StrategyOfTraces.typedComputeLabel`. -/
def typedComputeLabel
    (Qc : Fin (CC[O]).rap.w → F[X])
    (i : Fin O.family.problem.cfg.compRows) :
    State × DTcomp K :=
  let env := StrategyOfTracesLift.decodeSource (rowEnv O Qc i)
  let st := StrategyOfTracesLift.computeStateOf env
  (st, (inpOf env, pubOfState env st, decOf env))

open scoped Classical in
/-- `StrategyOfTraces.typedMemoryLabel`. -/
def typedMemoryLabel
    (Qm : Fin (MC[O]).rap.w → F[X])
    (i : Fin O.family.problem.cfg.memRows) :
    MState × DTmem K :=
  let envF := memoryBaseEnv O Qm i
  let envK := memorySourceEnv O Qm i
  let st := memoryStateOf envF
  let pt : Cell K := ⟨StrategyOfTracesLift.memoryPtNoun envK, 0, 0⟩
  let mem : MemRec K :=
    ⟨StrategyOfTracesLift.memoryMemRoot envK, StrategyOfTracesLift.memoryMemChild envK, 0, 0⟩
  (st,
    (O.objects.cfg.challenges.memoryInputs,
      { st := st
        pt := pt
        lc := Cell.zero
        rc := Cell.zero
        lcSt := .halt
        rcSt := .halt
        mem := mem
        ipre := 0
        icur := 0 }))

open scoped Classical in
/-- `StrategyOfTraces.typedComputeRows`. -/
def typedComputeRows
    (Qc : Fin (CC[O]).rap.w → F[X]) :
    List (State × DTcomp K) :=
  (List.finRange O.family.problem.cfg.compRows).map (typedComputeLabel O Qc)

open scoped Classical in
/-- `StrategyOfTraces.typedMemoryRows`. -/
def typedMemoryRows
    (Qm : Fin (MC[O]).rap.w → F[X]) :
    List (MState × DTmem K) :=
  (List.finRange O.family.problem.cfg.memRows).map (typedMemoryLabel O Qm)

open scoped Classical in
/-- `StrategyOfTraces.typedComputeForest`. -/
def typedComputeForest
    (Qc : Fin (CC[O]).rap.w → F[X]) :
    List (NTree (State × DTcomp K)) :=
  match StrategyOfTracesLift.rebuildForest StrategyOfTracesLift.computeFanout 1
      (typedComputeRows O Qc) with
  | [] => [.node StrategyOfTracesLift.dummyComputeLabel []]
  | t :: ts => t :: ts

open scoped Classical in
/-- `StrategyOfTraces.typedComputeTree`. -/
def typedComputeTree
    (Qc : Fin (CC[O]).rap.w → F[X]) :
    NTree (State × DTcomp K) :=
  match typedComputeForest O Qc with
  | t :: _ => t
  | [] => .node StrategyOfTracesLift.dummyComputeLabel []

open scoped Classical in
/-- `StrategyOfTraces.typedMemoryForest`. -/
def typedMemoryForest
    (Qm : Fin (MC[O]).rap.w → F[X]) :
    List (NTree (MState × DTmem K)) :=
  match StrategyOfTracesLift.rebuildForest StrategyOfTracesLift.memoryFanout
      O.family.problem.cfg.kMem (typedMemoryRows O Qm) with
  | [] => [.node StrategyOfTracesLift.dummyMemoryLabel []]
  | t :: ts => t :: ts

open scoped Classical in
/-- `StrategyOfTraces.computeJoinOf`. -/
def computeJoinOf
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X]) : ComputeJoin where
  computeTree :=
    StrategyOfTracesLift.mapComputeJoin (ringChar K) (typedMemoryForest O Qm)
      (typedComputeTree O Qc)

open scoped Classical in
/-- `StrategyOfTraces.decodedSkeletonOf`. -/
def decodedSkeletonOf
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X]) : SemanticSkeleton :=
  decodedSkeleton (ringChar K) (computeJoinOf O Qc Qm) (typedMemoryForest O Qm)

open scoped Classical in
/-- `StrategyOfTraces.publicClaimOf`. -/
def publicClaimOf
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X]) : P8PublicClaim :=
  (decodedSkeletonOf O Qc Qm).publicClaim

/-! ### `ExecOfTraces` over `O` -/

/-- `ExecOfTraces.lblCAt`. -/
def lblCAt
    (Qc : Fin (CC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin O.family.problem.cfg.compRows) :
    State × DTcomp K :=
  let env := FamilyEnvCore.rowEnvAt O c (FamilyEnvCore.familyQc O c Qc) i
  let st := StrategyOfTracesLift.computeStateOf (StrategyOfTracesLift.decodeSource env)
  (st, (StrategyOfTracesLift.decodeInputs env, StrategyOfTracesLift.decodePub env st,
    StrategyOfTracesLift.decodeDec env))

/-- `ExecOfTraces.lblC`. -/
def lblC
    (Qc : Fin (CC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    ℕ → State × DTcomp K :=
  fun i =>
    if h : i - 1 < O.family.problem.cfg.compRows then
      lblCAt O Qc c ⟨i - 1, h⟩
    else
      lblCAt O Qc c ⟨0, O.family.problem.cfg.compRows_pos⟩

/-- `ExecOfTraces.decodeMemPub`. -/
def decodeMemPub
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin O.family.problem.cfg.memRows) :
    MemoryTable.Pub K :=
  let envF := FamilyEnvCore.memoryBaseEnvAt O c Qm i
  let envK := FamilyEnvCore.memorySourceEnvAt O c Qm i
  let st := memoryStateOf envF
  { st := st
    pt := ⟨StrategyOfTracesLift.memoryPtNoun envK, envK.trace 3, envK.trace 4⟩
    lc := ⟨⟨envK.trace 5, envK.trace 6, envK.trace 7⟩, envK.trace 8, envK.trace 9⟩
    rc := ⟨⟨envK.trace 10, envK.trace 11, envK.trace 12⟩, envK.trace 13, envK.trace 14⟩
    lcSt :=
      match st with
      | .read_root | .verify_child => st
      | _ => .halt
    rcSt := .halt
    mem := ⟨StrategyOfTracesLift.memoryMemRoot envK, StrategyOfTracesLift.memoryMemChild envK,
      envK.trace 25, envK.trace 26⟩
    ipre := envK.trace 27
    icur := envK.trace 28
    ver := decide (envK.trace 39 = 1)
    cprime? := some (envK.trace 57)
    lambda? := some (envK.chal 8) }

/-- `ExecOfTraces.lblMAt`. -/
def lblMAt
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin O.family.problem.cfg.memRows) :
    MState × DTmem K :=
  let st := memoryStateOf (FamilyEnvCore.memoryBaseEnvAt O c Qm i)
  (st, ({ z := nprSeed c.1, β := -(c.2.2.2.interPole), γ := c.2.1.1 },
    decodeMemPub O Qm c i))

/-- `ExecOfTraces.lblM`. -/
def lblM
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    ℕ → MState × DTmem K :=
  fun i =>
    if h : i - 1 < O.family.problem.cfg.memRows then
      lblMAt O Qm c ⟨i - 1, h⟩
    else
      lblMAt O Qm c ⟨0, O.family.problem.cfg.memRows_pos⟩

/-- `ExecOfTraces.foC`. -/
def foC
    (Qc : Fin (CC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    ℕ → ℕ :=
  fun i => fanoutComp (lblC O Qc c i).1

/-- `ExecOfTraces.foM`. -/
def foM
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    ℕ → ℕ :=
  fun i => fanoutMem (lblM O Qm c i).1

/-- `ExecOfTraces.clabC`. -/
def clabC
    (Qc : Fin (CC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i j : ℕ) :
    Option (State × DTcomp K) :=
  let parent := lblC O Qc c i
  if hj : j < foC O Qc c i then
    have hj3 : j < 3 :=
      Nat.lt_of_lt_of_le hj ((comp_stateSep (K := K)).fanout_le parent.1)
    let trip := sfTriple parent.2.2.1 ⟨j, hj3⟩
    some (parent.1,
      (parent.2.1,
        { parent.2.2.1 with s := trip.1, f := trip.2.1, e := trip.2.2 },
        parent.2.2.2))
  else
    none

/-- `ExecOfTraces.clabM`. -/
def clabM
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i j : ℕ) :
    Option (MState × DTmem K) :=
  let parent := lblM O Qm c i
  if hj : j < foM O Qm c i then
    have hj2 : j < 2 :=
      Nat.lt_of_lt_of_le hj ((mem_stateSep (K := K)).fanout_le parent.1)
    let cell := memCell parent ⟨j, hj2⟩
    some (parent.1, (parent.2.1, { parent.2.2 with pt := cell }))
  else
    none

/-- `ExecOfTraces.computeLabelList`. -/
def computeLabelList
    (Qc : Fin (CC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    List (State × DTcomp K) :=
  (List.finRange O.family.problem.cfg.compRows).map (lblCAt O Qc c)

/-- `ExecOfTraces.memoryLabelList`. -/
def memoryLabelList
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    List (MState × DTmem K) :=
  (List.finRange O.family.problem.cfg.memRows).map (lblMAt O Qm c)

/-- `ExecOfTraces.computeLabelList_length`. -/
theorem computeLabelList_length
    (Qc : Fin (CC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (computeLabelList O Qc c).length = O.family.problem.cfg.compRows := by
  simp [computeLabelList]

/-- `ExecOfTraces.memoryLabelList_length`. -/
theorem memoryLabelList_length
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (memoryLabelList O Qm c).length = O.family.problem.cfg.memRows := by
  simp [memoryLabelList]

/-- `ExecOfTraces.cfgOfTraces`. -/
def cfgOfTraces
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
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
  Ksz := O.family.problem.cfg.Ksz
  kMem := O.family.problem.cfg.kMem
  orbit := O.family.problem.cfg.orbit
  orbit_h_pos := O.family.problem.cfg.orbit_h_pos
  compRows := (computeLabelList O Qc c).length
  memRows := (memoryLabelList O Qm c).length
  compRows_pos := by
    rw [computeLabelList_length]
    exact O.family.problem.cfg.compRows_pos
  memRows_pos := by
    rw [memoryLabelList_length]
    exact O.family.problem.cfg.memRows_pos
  compRows_le := by
    rw [computeLabelList_length]
    exact O.family.problem.cfg.compRows_le
  memRows_le := by
    rw [memoryLabelList_length]
    exact O.family.problem.cfg.memRows_le
  eDeg := O.family.problem.cfg.eDeg
  eDeg_eq_one := O.family.problem.cfg.eDeg_eq_one
  compNodes := fun i =>
    O.family.problem.cfg.orbit.βcoset *
      O.family.problem.cfg.orbit.ω ^ (i : ℕ)
  compNodes_spec := fun i => rfl
  memNodes := fun i =>
    O.family.problem.cfg.orbit.βcoset *
      O.family.problem.cfg.orbit.ω ^ (i : ℕ)
  memNodes_spec := fun i => rfl

/-- `ExecOfTraces.cfgOfTraces_compRows`. -/
theorem cfgOfTraces_compRows
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (cfgOfTraces O Qc Qm c).compRows = O.family.problem.cfg.compRows :=
  computeLabelList_length O Qc c

/-- `ExecOfTraces.cfgOfTraces_memRows`. -/
theorem cfgOfTraces_memRows
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (cfgOfTraces O Qc Qm c).memRows = O.family.problem.cfg.memRows :=
  memoryLabelList_length O Qm c

/-- `ExecOfTraces.cfgOfTraces_kMem`. -/
theorem cfgOfTraces_kMem
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (cfgOfTraces O Qc Qm c).kMem = O.family.problem.cfg.kMem :=
  rfl

/-- `ExecOfTraces.TracesWalkHyps` over `O`: the walk-tiling facts needed by
`bfsForest_reconTree` / `bfsForest_reconForest`.  Mentions `Qc` and `Qm`. -/
structure TracesWalkHyps
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : Prop where
  sfCompute :
    Sf (foC O Qc c) O.family.problem.cfg.compRows + 1 =
      O.family.problem.cfg.compRows
  validCompute :
    BFSValid (foC O Qc c) O.family.problem.cfg.compRows
  sfMemory :
    O.family.problem.cfg.kMem +
        Sf (foM O Qm c) O.family.problem.cfg.memRows =
      O.family.problem.cfg.memRows
  validMemory :
    BFSValidF O.family.problem.cfg.kMem (foM O Qm c)
      O.family.problem.cfg.memRows

/-- `ExecOfTraces.family_kMem_pos` (private there), over `O`. -/
theorem family_kMem_pos :
    1 ≤ O.family.problem.cfg.kMem := by
  have hpos : 0 < O.objects.cfg.kMem := O.objects.exec.memoryRootCount_pos
  have hk := congrArg ExactConfig.kMem O.family_cfg
  rw [← hk] at hpos
  exact hpos

/-- `ExecOfTraces.execOfTraces`: compute tree from `Qc`, memory forest from `Qm`. -/
def execOfTraces
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    ExactExecution (cfgOfTraces O Qc Qm c) where
  computeTree :=
    reconTree (foC O Qc c) (lblC O Qc c)
      O.family.problem.cfg.compRows
  memoryForest :=
    reconForest O.family.problem.cfg.kMem (foM O Qm c) (lblM O Qm c)
      O.family.problem.cfg.memRows
  memoryForest_nonempty := by
    have hk := family_kMem_pos O
    intro hempty
    have hlen := congrArg List.length hempty
    simp [reconForest, List.length_map, List.length_range'] at hlen
    exact (Nat.ne_of_gt (Nat.succ_le_iff.mp hk) hlen)
  memory_root_count := by
    simpa [reconForest, List.length_map, List.length_range'] using
      (cfgOfTraces_kMem O Qc Qm c).symm
  compute_bfs_length := by
    rw [bfsForest_reconTree (foC O Qc c) (lblC O Qc c)
      O.family.problem.cfg.compRows h.sfCompute h.validCompute]
    simp [List.length_map, List.length_range']
    exact (cfgOfTraces_compRows O Qc Qm c).symm
  memory_bfs_length := by
    have hk := family_kMem_pos O
    rw [bfsForest_reconForest O.family.problem.cfg.kMem (foM O Qm c)
      (lblM O Qm c) O.family.problem.cfg.memRows hk h.sfMemory
      h.validMemory]
    simp [List.length_map, List.length_range']
    exact (cfgOfTraces_memRows O Qc Qm c).symm

/-! ### `StrategyOfTracesCore` over `O` (and the explicit `tag`) -/

/-- `StrategyOfTracesCore.cfgTemplateOfTraces`. -/
def cfgTemplateOfTraces
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (z : K) :
    ExactConfigTemplate F K :=
  StrategyOfTracesLift.configTemplateOf (cfgOfTraces O Qc Qm c) z

/-- `StrategyOfTracesCore.execTemplateOfTraces`. -/
def execTemplateOfTraces
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c)
    (z : K) :
    ExactExecutionTemplate (cfgTemplateOfTraces O Qc Qm c z) where
  computeTree :=
    mapNTree StrategyOfTracesLift.wrapComputeLabel (execOfTraces O Qc Qm c h).computeTree
  memoryForest :=
    (execOfTraces O Qc Qm c h).memoryForest.map
      (mapNTree (StrategyOfTracesLift.wrapMemoryLabel (alphaM c.1)))
  memoryForest_nonempty := by
    intro hempty
    exact (execOfTraces O Qc Qm c h).memoryForest_nonempty (List.map_eq_nil_iff.mp hempty)
  memory_root_count := by
    simp only [List.length_map, cfgTemplateOfTraces, StrategyOfTracesLift.configTemplateOf]
    exact (execOfTraces O Qc Qm c h).memory_root_count
  compute_bfs_length := by
    have hlen := (execOfTraces O Qc Qm c h).compute_bfs_length
    have hmap :
        (bfsForest
          [mapNTree StrategyOfTracesLift.wrapComputeLabel
            (execOfTraces O Qc Qm c h).computeTree]).length =
        (bfsForest [(execOfTraces O Qc Qm c h).computeTree]).length := by
      rw [show [mapNTree StrategyOfTracesLift.wrapComputeLabel
              (execOfTraces O Qc Qm c h).computeTree] =
            [(execOfTraces O Qc Qm c h).computeTree].map
              (mapNTree StrategyOfTracesLift.wrapComputeLabel) from rfl,
        bfsForest_mapNTree, List.length_map]
    simpa [cfgTemplateOfTraces, StrategyOfTracesLift.configTemplateOf, hmap] using hlen
  memory_bfs_length := by
    have hlen := (execOfTraces O Qc Qm c h).memory_bfs_length
    have hmap :
        (bfsForest
          ((execOfTraces O Qc Qm c h).memoryForest.map
            (mapNTree (StrategyOfTracesLift.wrapMemoryLabel (alphaM c.1))))).length =
        (bfsForest (execOfTraces O Qc Qm c h).memoryForest).length := by
      rw [bfsForest_mapNTree, List.length_map]
    simpa [cfgTemplateOfTraces, StrategyOfTracesLift.configTemplateOf, hmap] using hlen

/-- `StrategyOfTracesCore.timestampOfTraces`. -/
def timestampOfTraces
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K) :=
  DataOnlyTemplateFixedStagedTimestampStrategy.ofRawData
    (publicClaimOf O Qc Qm)
    (fun seed => cfgTemplateOfTraces O Qc Qm c seed.1)
    (fun seed => execTemplateOfTraces O Qc Qm c h seed.1)
    (fun _ => rfl)

/-- `StrategyOfTracesCore.familyDataOfTraces`, with the full-package field `P.stateTagChar` as the
explicit hypothesis `tag`. -/
def familyDataOfTraces
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    AlphaMFamilyData (timestampOfTraces O Qc Qm c h) z hz α lmb where
  compNodeWidth := NodeEncoding.computeNodeWidth
  compNodeEncode := NodeEncoding.computeNodeEncode tag
  memNodeWidth := NodeEncoding.memoryNodeWidth
  memNodeEncode := NodeEncoding.memoryNodeEncode tag
  requests :=
    algebraMap K (IOField K)
      (∑ k : Fin 3,
          O.computePublic (6 + (k : ℕ)) • O.basis k)
  responses :=
    algebraMap K (IOField K)
      ((FamilyEnvCore.memorySourceEnvAt O c Qm
        ⟨O.family.problem.cfg.memRows - 1,
          Nat.pred_lt (Nat.pos_iff_ne_zero.mp
            O.family.problem.cfg.memRows_pos)⟩).trace 44)
  outMem :=
    algebraMap K (IOField K)
      ((FamilyEnvCore.memorySourceEnvAt O c Qm
        ⟨0, O.family.problem.cfg.memRows_pos⟩).trace 28)

/-- `StrategyOfTracesCore.tablesOfTraces`. -/
def tablesOfTraces
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    RawTableArrays (familyDataOfTraces O tag Qc Qm c h z hz α lmb).base where
  compute := fun i =>
    if hj : i.val < O.family.problem.cfg.compRows then
      StrategyOfTracesLift.decodeEx
        (FamilyEnvCore.rowEnvAt O c (FamilyEnvCore.familyQc O c Qc) ⟨i.val, hj⟩)
    else
      StrategyOfTracesLift.decodeEx (FamilyEnvCore.rowEnvAt O c (FamilyEnvCore.familyQc O c Qc)
        ⟨0, O.family.problem.cfg.compRows_pos⟩)
  memory := fun _ => 0

/-- `StrategyOfTracesCore.walksOfTraces`. -/
def walksOfTraces
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    RawWalkArrays K where
  computeLn := fun i => (lblC O Qc c i).2.2.1.ln
  computeCount := fun i => (lblC O Qc c i).2.2.1.ln_prev
  computeAcc := fun _ => 0
  memoryLn := fun i => (lblM O Qm c i).2.2.ipre
  memoryCount := fun i => (lblM O Qm c i).2.2.icur
  memoryAcc := fun _ => 0

/-- `StrategyOfTracesCore.ioOfTraces`. -/
def ioOfTraces
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    RawIOArrays (familyDataOfTraces O tag Qc Qm c h z hz α lmb).base (ringChar K) where
  multiplicity := fun j =>
    let i := j.val % O.family.problem.cfg.memRows
    if hlt : i < O.family.problem.cfg.memRows then
      if (FamilyEnvCore.memoryBaseEnvAt O c Qm ⟨i, hlt⟩).trace 2 = 1 then 1 else 0
    else
      0
  progAcc := fun i =>
    if hlt : i < O.family.problem.cfg.compRows then
      algebraMap K (IOField K)
        ((FamilyEnvCore.rowEnvAt O c (FamilyEnvCore.familyQc O c Qc) ⟨i, hlt⟩).toSourceEnv.trace
          accAfterIndex)
    else
      0
  memAcc := fun i =>
    if hlt : i < O.family.problem.cfg.memRows then
      algebraMap K (IOField K)
        ((FamilyEnvCore.memorySourceEnvAt O c Qm ⟨i, hlt⟩).trace 44)
    else
      0

/-- `StrategyOfTracesCore.afterAlphaMOfTraces`. -/
def afterAlphaMOfTraces
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    AlphaMCommitment (p := ringChar K) (timestampOfTraces O Qc Qm c h) z hz α lmb where
  familyData := familyDataOfTraces O tag Qc Qm c h z hz α lmb
  tables := tablesOfTraces O tag Qc Qm c h z hz α lmb
  io := ioOfTraces O tag Qc Qm c h z hz α lmb

/-- `StrategyOfTracesCore.topologyOfTraces`. -/
def topologyOfTraces
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    RawTopologyArrays (afterAlphaMOfTraces O tag Qc Qm c h z hz α lmb).familyData.base where
  compute :=
    { childPayload := fun i slot =>
        match clabC O Qc c (i.val + 1) slot.val with
        | some child => ⟨child.2.2.1.s, child.2.2.1.f, child.2.2.1.e⟩
        | none => ComputeLinkPayload.zero }
  memory :=
    { childPayload := fun i slot =>
        match clabM O Qm c (i.val + 1) slot.val with
        | some child => child.2.2.pt
        | none => Cell.zero }

/-- `StrategyOfTracesCore.rawVerifierOfTraces`. -/
def rawVerifierOfTraces
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    TemplateRawJointSoundness.Strategy F K (ringChar K) where
  timestamp := timestampOfTraces O Qc Qm c h
  afterAlphaM := afterAlphaMOfTraces O tag Qc Qm c h
  afterCoins := fun _ _ _ => walksOfTraces O Qc Qm c

/-- `StrategyOfTracesCore.verifierOfTraces`. -/
def verifierOfTraces
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K) where
  raw := rawVerifierOfTraces O tag Qc Qm c h
  topologyAfterAlphaM := topologyOfTraces O tag Qc Qm c h

/-- `StrategyOfTracesCore.strategyOfTraces` over `O`, with `tag` explicit: the K-side strategy
built from the traces (not `P.strategy`). -/
def strategyOfTraces
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    ProductionStrategy F K where
  verifier := verifierOfTraces O tag Qc Qm c h
  skeleton := decodedSkeletonOf O Qc Qm
  publicClaim_eq := rfl

end

end Nock.NockVMROM.Thm54.StrategyOfTracesLift
