/-
  Nock/NockVMROM/Thm54/StrategyOfTraces.lean

  **H1.4 — reconstruct the K-side strategy from deployed traces.**

  Hostile plan M2: arrays = evaluations on `H`,
  skeleton = H1.2's `decodedSkeleton`, compute-row nouns from the IO join
  (`ComputeJoin`), paper-`⊥` record halves from the request side
  (`RecordHalfJoin`), typed forest from `Qm` the way `hostileResponses` already
  reads rows (`memorySourceEnv`).

**What this module is.**  The seed-free reconstruction and the H1.2 join.
  `decodedSkeletonOf` is a function of `(P, Qc, Qm)`.  The public claim is the
  compute-tree root of that skeleton (`SemanticSkeleton.publicClaim`).

  **What this module is not.**  A hyp-free `ProductionStrategy` whose
  `Accepts c.1` follows from `DeployedAcceptance` at an arbitrary tuple. `binds` at a seed other than the baked one is a collision
  event, not a theorem of the traces. -/
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.DeployedComputeRows
import Nock.NockVMROM.Thm54.ComputeEnvAgreement
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding
import Nock.NockVMROM.Thm54.HostileRecordLists
import Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly
import Nock.NockVMROM.Thm54.ComputeEnvAgreement
import Nock.GlobalCarryRecognizer
import Nock.NockVMROM.Thm54.PreZCensusCore
import Nock.NockVMROM.Thm54.P8Core.StrategyOfTraces

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.StrategyOfTraces

open scoped Classical Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Framework
open Nock.Reified
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-! ## §0  Dummy rows (underflow of the BFS inverse) -/

def dummyMemRec : MemRecSkeleton where
  root := Noun.atom 0
  child := Noun.atom 0
  axis := 0

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

def dummyComputeTree : NTree ComputeRowSkeleton :=
  .node dummyComputeRow []

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

def dummyMemoryLabel : MemoryTable.MState × MemoryTable.DTmem K :=
  (.halt, dummyDTmem)

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

/-! ## §1  BFS inverse (`bfsForest` is level-order) -/

def groupChildren {α : Type} :
    List ℕ → List (NTree α) → List (List (NTree α)) × List (NTree α)
  | [], kids => ([], kids)
  | f :: fs, kids =>
      let mine := kids.take f
      let rest := kids.drop f
      let more := groupChildren fs rest
      (mine :: more.1, more.2)

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

/-- Rebuild a forest from its BFS labels.  The first `kRoots` labels are the
roots (`ExactConfig.kMem` on memory, `1` on compute).  Not a positional
lookup in the multiset — it is the inverse of `Walk.bfsForest`. -/
def rebuildForest {α : Type} (fanout : α → ℕ) (kRoots : ℕ) (rows : List α) :
    List (NTree α) :=
  unbfs fanout (rows.length + 1) (rows.take kRoots) (rows.drop kRoots)

theorem unbfs_nil_level {α : Type} (fanout : α → ℕ) (fuel : ℕ) (rest : List α) :
    unbfs fanout fuel [] rest = [] := by
  cases fuel <;> rfl

theorem rebuildForest_zero_roots {α : Type} (fanout : α → ℕ) (rows : List α) :
    rebuildForest fanout 0 rows = [] := by
  simp [rebuildForest, unbfs_nil_level]

/-! ## §2  Row decoders (same instruments as `hostileRequests` / `hostileResponses`) -/

variable (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

def typedComputeLabel
    (Qc : Fin P.computeChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    State × DTcomp K :=
  let env := decodeSource (rowEnv P Qc i)
  let st := computeStateOf env
  (st, (inpOf env, pubOfState env st, decOf env))

def typedMemoryLabel
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    MState × DTmem K :=
  let envF := P.memoryBaseEnv Qm i
  let envK := P.memorySourceEnv Qm i
  let st := memoryStateOf envF
  let pt : Cell K := ⟨memoryPtNoun envK, 0, 0⟩
  let mem : MemRec K :=
    ⟨memoryMemRoot envK, memoryMemChild envK, 0, 0⟩
  (st,
    (P.objects.cfg.challenges.memoryInputs,
      { st := st
        pt := pt
        lc := Cell.zero
        rc := Cell.zero
        lcSt := .halt
        rcSt := .halt
        mem := mem
        ipre := 0
        icur := 0 }))

def typedComputeRows
    (Qc : Fin P.computeChip.rap.w → F[X]) :
    List (State × DTcomp K) :=
  (List.finRange P.optimized.family.problem.cfg.compRows).map (typedComputeLabel P Qc)

def typedMemoryRows
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    List (MState × DTmem K) :=
  (List.finRange P.optimized.family.problem.cfg.memRows).map (typedMemoryLabel P Qm)

theorem typedComputeRows_length
    (Qc : Fin P.computeChip.rap.w → F[X]) :
    (typedComputeRows P Qc).length = P.optimized.family.problem.cfg.compRows := by
  simp [typedComputeRows]

theorem typedMemoryRows_length
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (typedMemoryRows P Qm).length = P.optimized.family.problem.cfg.memRows := by
  simp [typedMemoryRows]

/-! ## §3  Typed forest / compute tree from the traces -/

def computeFanout : (State × DTcomp K) → ℕ
  | (st, _) => fanoutComp st

def memoryFanout : (MState × DTmem K) → ℕ
  | (st, _) => fanoutMem st

/-- One compute tree, BFS-inverted from the committed compute rows. -/
def typedComputeForest
    (Qc : Fin P.computeChip.rap.w → F[X]) :
    List (NTree (State × DTcomp K)) :=
  match rebuildForest computeFanout 1 (typedComputeRows P Qc) with
  | [] => [.node dummyComputeLabel []]
  | t :: ts => t :: ts

def typedComputeTree
    (Qc : Fin P.computeChip.rap.w → F[X]) :
    NTree (State × DTcomp K) :=
  match typedComputeForest P Qc with
  | t :: _ => t
  | [] => .node dummyComputeLabel []

/-- Memory forest, BFS-inverted.  Root count is the chip's `kMem`
(the same geometry `memorySourceEnv` already indexes by). -/
def typedMemoryForest
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    List (NTree (MState × DTmem K)) :=
  match rebuildForest memoryFanout P.optimized.family.problem.cfg.kMem
      (typedMemoryRows P Qm) with
  | [] => [.node dummyMemoryLabel []]
  | t :: ts => t :: ts

theorem typedMemoryForest_nonempty
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    typedMemoryForest P Qm ≠ [] := by
  unfold typedMemoryForest
  cases rebuildForest memoryFanout P.optimized.family.problem.cfg.kMem
      (typedMemoryRows P Qm) <;> simp

/-! ## §4  Noun join: fingerprints → `decodeNoun` of the matching memory node -/

def nounByFP (q : ℕ)
    (forest : List (NTree (MState × DTmem K))) (fp : FP K) : Noun :=
  match (bfsForest forest).find? (fun t => t.label.2.2.pt.noun = fp) with
  | some t => decodeNoun q t
  | none => Noun.atom 0

def memRecJoin (q : ℕ)
    (forest : List (NTree (MState × DTmem K))) (mr : MemRec K) :
    MemRecSkeleton where
  root := nounByFP q forest mr.root
  child := nounByFP q forest mr.child
  axis := leafAtomOf q mr.axis

def kidSkel (kids : List ComputeRowSkeleton) (i : ℕ) : ComputeRowSkeleton :=
  kids[i]?.getD dummyComputeRow

/-- Reconstruct an atom-shaped fingerprint without a forest hit.
    Opcode heads (`SVhead`) and 0/1 test bits are this shape. -/
def joinNoun (q : ℕ) (z : K)
    (forest : List (NTree (MState × DTmem K))) (fp : FP K) : Noun :=
  if fp.size = z ∧ fp.dyck = 0 then
    Noun.atom (leafAtomOf q fp.leaf)
  else
    nounByFP q forest fp

/-- Evaluation noun from `V_comp`: child results,
    `FP.cons` / increment / `wut` / `tis`, formula tail (OP1), or a
    served record (`nounByFP` only where `V_comp` emits one — OP0 `e`). -/
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
  | .s0 => nounByFP q forest row.2.2.1.e

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
      | _, _ => memRecJoin q forest (computeMemRec pub i) }

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
      let arm := joinNoun q row.2.1.z forest row.2.2.1.sf2_f
      [sCore, f c1 sCore.label.evaluation arm]
  | _, ch' =>
      ch'.map fun c => f c subj formula

open scoped Classical in
/-- Fuelled join so Lean does not hang on `NTree.size` well-foundedness.
    Call with `fuel = t.size`.  `V_comp` child `(s,f)`:
    formula heads/tails, sibling results for mutated subjects (OP2/7/8/9).
    Helper/condition children are joined first when BFS order is reversed. -/
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

def mapComputeJoinIn (q : ℕ)
    (forest : List (NTree (MState × DTmem K)))
    (t : NTree (State × DTcomp K)) (subj formula : Noun) :
    NTree ComputeRowSkeleton :=
  mapComputeJoinInFuel t.size q forest t subj formula

/-- Formula noun reconstructed from the tree (`V_comp` opcode wrapper +
    child formulas / row decomposition).  Opcode heads are atoms
    (`evalV` pins `f_h = atomFP z op`). -/
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
      | .s0, [] => .cell (.atom 0) (joinNoun q z forest dec.f_t)
      | .s1, [] => .cell (.atom 1) (joinNoun q z forest dec.f_t)
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
              (.cell (joinNoun q z forest dec.f_tth)
                (joinNoun q z forest dec.f_ttt)))
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
          .cell (joinNoun q z forest dec.f_h) (joinNoun q z forest dec.f_t)

/-- Root wrapper: subject from `joinNoun` of the root `s`; formula from
    `joinFormulaDeep` so opcode wrappers match `V_comp`. -/
def mapComputeJoin (q : ℕ)
    (forest : List (NTree (MState × DTmem K)))
    (t : NTree (State × DTcomp K)) : NTree ComputeRowSkeleton :=
  let z := t.label.2.1.z
  let pub := t.label.2.2.1
  mapComputeJoinIn q forest t
    (joinNoun q z forest pub.s)
    (joinFormulaDeep q forest t)

/-- H1.2's `ComputeJoin`: compute-row nouns from served memory-forest nodes. -/
def computeJoinOf
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) : ComputeJoin where
  computeTree :=
    mapComputeJoin (ringChar K) (typedMemoryForest P Qm) (typedComputeTree P Qc)

/-- Paper-`⊥` halves: fill `read_root.mem.child` and
`verify_child.mem.root` from the first matching request record. -/
def recordHalfJoinOf
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) : RecordHalfJoin :=
  let forest := typedMemoryForest P Qm
  let q := ringChar K
  let reqs := P.hostileRequests Qc
  let recRoot (r : Fin 10 → K) : FP K := ⟨r 0, r 1, r 2⟩
  let recChild (r : Fin 10 → K) : FP K := ⟨r 3, r 4, r 5⟩
  let readChild :=
    match (typedMemoryRows P Qm).find? (fun row => row.1 = .read_root) with
    | some row =>
        match reqs.find? (fun r => recRoot r = row.2.2.mem.root) with
        | some r => nounByFP q forest (recChild r)
        | none => Noun.atom 0
    | none => Noun.atom 0
  let verifyRoot :=
    match (typedMemoryRows P Qm).find? (fun row => row.1 = .verify_child) with
    | some row =>
        match reqs.find? (fun r => recChild r = row.2.2.mem.child) with
        | some r => nounByFP q forest (recRoot r)
        | none => Noun.atom 0
    | none => Noun.atom 0
  { readRootChild := readChild
    verifyChildRoot := verifyRoot }

/-- H1.2's `decodedSkeleton` at the reconstructed forest and join. -/
def decodedSkeletonOf
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) : SemanticSkeleton :=
  decodedSkeleton (ringChar K) (computeJoinOf P Qc Qm) (typedMemoryForest P Qm)

/-- The claim the traces name: compute-root nouns of the joined skeleton. -/
def publicClaimOf
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) : P8PublicClaim :=
  (decodedSkeletonOf P Qc Qm).publicClaim

/-- **`same_problem` as a theorem about the built objects.**  The claim the
strategy will carry *is* the public-input nouns read off the traces.  This is
the H1.5 reading: the built
specialization is the one the committed public inputs name — not `P.objects`. -/
theorem same_problem_claim
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    publicClaimOf P Qc Qm = (decodedSkeletonOf P Qc Qm).publicClaim :=
  rfl

theorem decodedSkeleton_computeTree
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (decodedSkeletonOf P Qc Qm).computeTree =
      (computeJoinOf P Qc Qm).computeTree :=
  rfl

theorem computeJoin_root_subject
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (publicClaimOf P Qc Qm).subject =
      (computeJoinOf P Qc Qm).computeTree.label.subject :=
  rfl

/-! ## §5  Chip-geometry template (orbit / `H.card` / `Ksz`)

Copied from the package family — the same geometry `computeBaseEnv` /
`memorySourceEnv` already use.  `a,b,c` stay the package constants
.  The seed argument overwrites `z`. -/

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

theorem configTemplateOf_z (cfg : ExactConfig F K) (z : K) :
    (configTemplateOf cfg z).challenges.z = z :=
  rfl

theorem configTemplateOf_Ksz (cfg : ExactConfig F K) (z : K) :
    (configTemplateOf cfg z).Ksz = cfg.Ksz :=
  rfl

/-- `hKp` at the chip's `Ksz` public. -/
theorem hKp_of_package (z : K) :
    (configTemplateOf P.objects.cfg z).Ksz = P.objects.cfg.Ksz :=
  rfl

/-! ## §6  Walk-hyp inventory (H1.7 left these at `strategyOfTraces`)

`ComputeRowsAccepted` is `Vcomp` on `exec.computeRows`
(`Batch345.computeRowsAccepted_is_Vcomp_on_bfs`).  H1.1 gives `Vcomp` at
decoded compute rows (`deployed_row_vcomp`).  Identifying those rows with
a family's `exec.computeRows` is the remaining discharge — it needs the
family, which needs H1.U before `Accepts` at an arbitrary `c.1` is the
chips' statement. -/

def computeRowsAreVcomp
    (Qc : Fin P.computeChip.rap.w → F[X]) : Prop :=
  ∀ i : Fin P.optimized.family.problem.cfg.compRows,
    DeployedComputeRows.VcompAt (rowEnv P Qc i)

theorem computeRowsAreVcomp_of_sat
    (Qc : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0) :
    computeRowsAreVcomp P Qc :=
  fun i => deployed_row_vcomp P Qc hsat hz0 i

/-- Arrays as evaluations on `H`: one compute extra per active row, read off
the gathered environment.  This is W6 step (a)'s "arrays = evaluations on `H`". -/
def computeExtrasOnH
    (Qc : Fin P.computeChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) : Extra K :=
  decodeEx (rowEnv P Qc i)

/-! ## §7  Data-only bundle (not `ProductionStrategy`)

H1.4b: the reconstruction functions, without `binds` at every seed and
without `Accepts`.  H1.5 inhabits `ProductionStrategy` later. -/

structure StrategyOfTracesData
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) where
  skeleton : SemanticSkeleton
  claim : P8PublicClaim
  publicClaim_eq : skeleton.publicClaim = claim

def strategyOfTracesData
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    StrategyOfTracesData P Qc Qm where
  skeleton := decodedSkeletonOf P Qc Qm
  claim := publicClaimOf P Qc Qm
  publicClaim_eq := rfl

theorem strategyOfTracesData_skeleton
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (strategyOfTracesData P Qc Qm).skeleton = decodedSkeletonOf P Qc Qm :=
  rfl

theorem strategyOfTracesData_claim
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (strategyOfTracesData P Qc Qm).claim = publicClaimOf P Qc Qm :=
  rfl

end

end Nock.NockVMROM.Thm54.StrategyOfTraces

#print axioms Nock.NockVMROM.Thm54.StrategyOfTraces.same_problem_claim
#print axioms Nock.NockVMROM.Thm54.StrategyOfTraces.typedMemoryForest_nonempty
#print axioms Nock.NockVMROM.Thm54.StrategyOfTraces.computeRowsAreVcomp_of_sat
#print axioms Nock.NockVMROM.Thm54.StrategyOfTraces.configTemplateOf_z
#print axioms Nock.NockVMROM.Thm54.StrategyOfTraces.strategyOfTracesData_skeleton
#print axioms Nock.NockVMROM.Thm54.StrategyOfTraces.strategyOfTracesData_claim
