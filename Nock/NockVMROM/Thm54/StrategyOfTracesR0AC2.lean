/-
  Nock/NockVMROM/Thm54/StrategyOfTracesR0AC2.lean

  **H1.5b Part 2b-i/7 — route B's C2 compute tree as a `ComputeRowSkeleton` tree, and the round-0
  strategy whose skeleton carries it**.  Additive: `strategyOfTracesR0A`,
  `strategyOfTracesR0`, `decodedSkeletonOf` and the lifted strategy stay; nothing is re-pointed.

  Route B (Q5) replaces that tree by the C2 skeleton: the root subject
  and formula are the CLAIM's, OP0's evaluation is the served `verify_child` noun of the row's
  request `2` (exponent `S + 2`), OP9's arm the served noun of request `3` (`S + 3`), and the two
  record axes are the round-0 certificate axes of those exponents (`certAxisOfEnvs`, the memory
  wrap's own `axOfRowsR0` read from the compute side). `S3PairEvent.builtJoin` is exactly this join
  in `S3Node` form (state, `S`, subject, formula, evaluation); this module is its
  `ComputeRowSkeleton` twin, the type `SemanticSkeleton.computeTree` has, with the decomposition,
  subformula and record fields `computeSkeletonRow` fills (structurally, as the lifted join).

  * **§A — the join, generic.**  `c2SkeletonRow sv ax st S subj formula kids` is
    `StrategyOfTracesLift.computeSkeletonRow` with `joinEvaluation`'s OP0 case served
    (`sv .verify_child (S + 2)`), the OP0 / OP9 record axes `ax (S + 2)` / `ax (S + 3)`, and the
    inactive record slots `dummyMemRec` (never read: `BindComputeRow` asks `MemRec.zero` there;
    Q2 "drop `memRecJoin`").  `c2JoinFuel st Sof sv ax` is `mapComputeJoinInFuel`'s recursion
    verbatim over any label type with a state and an `S` projection, with OP9's arm served
    (`sv .verify_child (S + 3)`); `c2Join` is it at fuel `t.size`.
  * **§B — the shape.**  `c2JoinFuel_shape`: on `NTree (State × ℕ)`, the projection
    `(state, subject, formula, evaluation)` of the C2 join IS that projection of
    `S3PairEvent.builtJoinFuel`, at every fuel, root subject and formula — so the S3 event's pairs are
    read off exactly this skeleton's rows (`S3PairEvent.rowS3Pairs` reads only those four fields and
    `S`).
  * **§C — over `O`.**  `c2TreeOfTraces O Qc c : NTree ((State × DTcomp K) × ℕ)` is `execOfTraces`'s
    compute tree (`reconTree (foC) (lblC)`) with each row's round-0 carrier `S = natLift (col 302)`
    attached (`c2TreeOfTraces_fst`, `rfl`); `c2ComputeTree` is the C2 join on it at the served lookup
    `servedNounOfEnvs` of the family memory base envs and the certificate axes of the family compute
    source envs (the two env families `StrategyOfTracesR0` reads), rooted at the package claim's
    subject and formula.  `decodedSkeletonC2` carries it with `decodedSkeletonR0A`'s memory forest
; `strategyOfTracesR0AC2` is the
    round-0 strategy chain `verifierGen` at the timestamp strategy `timestampOfTracesC2`, whose claim
    is the C2 skeleton's public claim (`publicClaim_eq := rfl`, as `strategyOfTracesR0`).  Its
    specialized execution and configuration are the round-0 strategy's (`rfl`: `specializedProblem`
    reads `afterSeed` only).

  What changes against `strategyOfTracesR0A`, stated plainly: the verifier's `raw.claim` is
  `(claim.subject, claim.formula, C2 root evaluation)` instead of `publicClaimOf` (the self-read
  root), so `Accepts` (`VerifierChecks T.raw.claim`) and `GenuineTargetAt` (`rootPublicNouns`,
  `evalFByPublic`, `publicClaimHoldsMod`) read the claim's subject and formula and the C2 skeleton;
  `FailureUnion` reads the C2 census.  None of the three transfers by `rfl` from R0A; the memory
  forest and the specialized execution do.

  Paper: the paper (`V_comp`), `:1864-1868` (the OP0 record), `:1879-1882` (the OP9
  record and arm), `:1288-1295` (axes), `:1450` (the claim).
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesR0A
import Nock.NockVMROM.Thm54.S3PairEvent

namespace Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open Nock.NockVMROM.Thm54.S3PairEvent

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false

noncomputable section

/-! ## §A  The C2 join, generic -/

section Join

/-- **The C2 row evaluation**: `StrategyOfTracesLift.joinEvaluation` with OP0's `nounByFP … e`
replaced by the served `verify_child` noun of the row's request `2` (exponent `S + 2`;
`S3PairEvent.builtEvaluation`'s rule, read on `ComputeRowSkeleton` kids). -/
def c2Evaluation (sv : MState → ℕ → Noun) (st : State) (S : ℕ) (formula : Noun)
    (kids : List ComputeRowSkeleton) : Noun :=
  match st with
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
  | .s0 => sv .verify_child (S + 2)

/-- **The C2 skeleton row**: `StrategyOfTracesLift.computeSkeletonRow` with the served OP0
evaluation, the round-0 record axes `ax (S + 2)` (OP0 slot `1`) and `ax (S + 3)` (OP9 slot `2`),
and `dummyMemRec` on the inactive record slots (never read by `BindComputeRow`). -/
def c2SkeletonRow (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (st : State) (S : ℕ)
    (subj formula : Noun) (kids : List ComputeRowSkeleton) : ComputeRowSkeleton :=
  let fh := nounHead formula
  let ft := nounTail formula
  let fth := nounHead ft
  let ftt := nounTail ft
  let ftth := nounHead ftt
  let fttt := nounTail ftt
  { state := st
    subject := subj
    formula := formula
    evaluation := c2Evaluation sv st S formula kids
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
      | .s0, 1 => ⟨subj, c2Evaluation sv st S formula kids, ax (S + 2)⟩
      | .s2, 1 | .s5, 1 | .s7, 1 | .s8, 1 | .s9, 1 => ⟨ft, fth, 2⟩
      | .s6, 1 => ⟨ft, fth, 2⟩
      | .s6, 2 => ⟨ftt, ftth, 2⟩
      | .s9, 2 => ⟨(kidSkel kids 0).evaluation, (kidSkel kids 1).formula, ax (S + 3)⟩
      | _, _ => dummyMemRec }

variable {β : Type}

/-- MIG 4.35: the children of `c2JoinFuel` at one row, with the recursive call `f` as a parameter.
Non-recursive; split out so the kernel checks the per-opcode match outside the structural recursion (4.35 reports
deep recursion on the inlined form). The `c2JoinFuel_eq_k_old` lemmas restate the 4.31 equations. -/
def c2JoinKids (st : β → State) (Sof : β → ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ)
    (f : NTree β → Noun → Noun → NTree ComputeRowSkeleton)
    (row : β) (ch : List (NTree β)) (subj formula : Noun) :
    List (NTree ComputeRowSkeleton) :=
  match st row, ch with
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
      let s0 := f c0 subj (nounHead (nounTail formula))
      let s1 := f c1 subj (nounTail (nounTail formula))
      [s0, s1, f c2 s0.label.evaluation s1.label.evaluation]
  | .s6, [c0, c1] =>
      let fth := nounHead (nounTail formula)
      let ftth := nounHead (nounTail (nounTail formula))
      let fttt := nounTail (nounTail (nounTail formula))
      let sCond := f c1 subj fth
      let b :=
        match sCond.label.evaluation with
        | .atom k => k
        | _ => 0
      [f c0 subj (if b = 0 then ftth else fttt), sCond]
  | .s7, [c0, c1] =>
      let fth := nounHead (nounTail formula)
      let ftt := nounTail (nounTail formula)
      let sHelp := f c1 subj fth
      [f c0 sHelp.label.evaluation ftt, sHelp]
  | .s8, [c0, c1] =>
      let fth := nounHead (nounTail formula)
      let ftt := nounTail (nounTail formula)
      let sHelp := f c1 subj fth
      [f c0 (Noun.cell sHelp.label.evaluation subj) ftt, sHelp]
  | .s9, [c0, c1] =>
      let coreF := nounTail (nounTail formula)
      let sCore := f c0 subj coreF
      let arm := sv .verify_child (Sof row + 3)
      [sCore, f c1 sCore.label.evaluation arm]
  | _, ch' =>
      ch'.map fun c => f c subj formula


/-- **The C2 join at fuel**: `StrategyOfTracesLift.mapComputeJoinInFuel`'s recursion verbatim over
labels with a state projection `st` and a carrier projection `Sof`, with OP9's arm served
(`sv .verify_child (S + 3)`; `S3PairEvent.builtJoinFuel`'s rule). -/
def c2JoinFuel (st : β → State) (Sof : β → ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) :
    ℕ → NTree β → Noun → Noun → NTree ComputeRowSkeleton
  | 0, .node row _, subj, formula =>
      .node (c2SkeletonRow sv ax (st row) (Sof row) subj formula []) []
  | n + 1, .node row ch, subj, formula =>
      let kids : List (NTree ComputeRowSkeleton) :=
        c2JoinKids st Sof sv ax (fun c s fo => c2JoinFuel st Sof sv ax n c s fo) row ch subj formula
      .node (c2SkeletonRow sv ax (st row) (Sof row) subj formula (kids.map NTree.label)) kids

attribute [simp] c2JoinKids

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuel.eq_1`, verbatim, at the re-encoded def. -/
theorem c2JoinFuel_eq_1_old : ∀ {β : Type} (st : β → Nock.ComputeTable.State)
  (Sof : β → ℕ) (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (row : β)
  (children : List (Nock.Walk.NTree β)),
  Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax 0 (Nock.Walk.NTree.node row children) x x_1 =
    Nock.Walk.NTree.node (Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2SkeletonRow sv ax (st row) (Sof row) x x_1 []) [] := by
  intros; rfl

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuel.eq_2`, verbatim, at the re-encoded def. -/
theorem c2JoinFuel_eq_2_old : ∀ {β : Type} (st : β → Nock.ComputeTable.State)
  (Sof : β → ℕ) (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β),
  st row = Nock.ComputeTable.State.s0 →
    Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n.succ (Nock.Walk.NTree.node row []) x x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2SkeletonRow sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label []))
        [] := by
  intros
  rw [c2JoinFuel.eq_2]
  unfold c2JoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuel.eq_3`, verbatim, at the re-encoded def. -/
theorem c2JoinFuel_eq_3_old : ∀ {β : Type} (st : β → Nock.ComputeTable.State)
  (Sof : β → ℕ) (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β),
  st row = Nock.ComputeTable.State.s1 →
    Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n.succ (Nock.Walk.NTree.node row []) x x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2SkeletonRow sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label []))
        [] := by
  intros
  rw [c2JoinFuel.eq_2]
  unfold c2JoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuel.eq_4`, verbatim, at the re-encoded def. -/
theorem c2JoinFuel_eq_4_old : ∀ {β : Type} (st : β → Nock.ComputeTable.State)
  (Sof : β → ℕ) (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 c1 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.cons →
    Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0, c1]) x
        x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2SkeletonRow sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            [Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 x
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead x_1),
              Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c1 x
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1)]))
        [Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 x
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead x_1),
          Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c1 x
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1)] := by
  intros
  rw [c2JoinFuel.eq_2]
  unfold c2JoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuel.eq_5`, verbatim, at the re-encoded def. -/
theorem c2JoinFuel_eq_5_old : ∀ {β : Type} (st : β → Nock.ComputeTable.State)
  (Sof : β → ℕ) (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.s3 →
    Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0]) x x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2SkeletonRow sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            [Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 x
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1)]))
        [Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 x
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1)] := by
  intros
  rw [c2JoinFuel.eq_2]
  unfold c2JoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuel.eq_6`, verbatim, at the re-encoded def. -/
theorem c2JoinFuel_eq_6_old : ∀ {β : Type} (st : β → Nock.ComputeTable.State)
  (Sof : β → ℕ) (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.s4 →
    Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0]) x x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2SkeletonRow sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            [Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 x
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1)]))
        [Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 x
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1)] := by
  intros
  rw [c2JoinFuel.eq_2]
  unfold c2JoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuel.eq_7`, verbatim, at the re-encoded def. -/
theorem c2JoinFuel_eq_7_old : ∀ {β : Type} (st : β → Nock.ComputeTable.State)
  (Sof : β → ℕ) (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 c1 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.s5 →
    Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0, c1]) x
        x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2SkeletonRow sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            [Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 x
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1)),
              Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c1 x
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1))]))
        [Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 x
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1)),
          Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c1 x
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1))] := by
  intros
  rw [c2JoinFuel.eq_2]
  unfold c2JoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuel.eq_8`, verbatim, at the re-encoded def. -/
theorem c2JoinFuel_eq_8_old : ∀ {β : Type} (st : β → Nock.ComputeTable.State)
  (Sof : β → ℕ) (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 c1 c2 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.s2 →
    Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0, c1, c2]) x
        x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2SkeletonRow sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            (have s0 :=
              Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 x
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1));
            have s1 :=
              Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c1 x
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1));
            [s0, s1,
              Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c2 s0.label.evaluation
                s1.label.evaluation])))
        (have s0 :=
          Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 x
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1));
        have s1 :=
          Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c1 x
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1));
        [s0, s1,
          Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c2 s0.label.evaluation
            s1.label.evaluation]) := by
  intros
  rw [c2JoinFuel.eq_2]
  unfold c2JoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuel.eq_9`, verbatim, at the re-encoded def. -/
theorem c2JoinFuel_eq_9_old : ∀ {β : Type} (st : β → Nock.ComputeTable.State)
  (Sof : β → ℕ) (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 c1 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.s6 →
    Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0, c1]) x
        x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2SkeletonRow sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            (let fth :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
            have ftth :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1));
            have fttt :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1));
            let sCond := Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c1 x fth;
            let b :=
              match sCond.label.evaluation with
              | Nock.Noun.atom k => k
              | x => 0;
            [Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 x (if b = 0 then ftth else fttt),
              sCond])))
        (let fth :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
        have ftth :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1));
        have fttt :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1));
        let sCond := Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c1 x fth;
        let b :=
          match sCond.label.evaluation with
          | Nock.Noun.atom k => k
          | x => 0;
        [Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 x (if b = 0 then ftth else fttt),
          sCond]) := by
  intros
  rw [c2JoinFuel.eq_2]
  unfold c2JoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuel.eq_10`, verbatim, at the re-encoded def. -/
theorem c2JoinFuel_eq_10_old : ∀ {β : Type} (st : β → Nock.ComputeTable.State)
  (Sof : β → ℕ) (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 c1 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.s7 →
    Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0, c1]) x
        x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2SkeletonRow sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            (have fth :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
            have ftt :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
            have sHelp := Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c1 x fth;
            [Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 sHelp.label.evaluation ftt,
              sHelp])))
        (have fth :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
        have ftt :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
        have sHelp := Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c1 x fth;
        [Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 sHelp.label.evaluation ftt, sHelp]) := by
  intros
  rw [c2JoinFuel.eq_2]
  unfold c2JoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuel.eq_11`, verbatim, at the re-encoded def. -/
theorem c2JoinFuel_eq_11_old : ∀ {β : Type} (st : β → Nock.ComputeTable.State)
  (Sof : β → ℕ) (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 c1 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.s8 →
    Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0, c1]) x
        x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2SkeletonRow sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            (have fth :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
            have ftt :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
            have sHelp := Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c1 x fth;
            [Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 (sHelp.label.evaluation.cell x)
                ftt,
              sHelp])))
        (have fth :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
        have ftt :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
        have sHelp := Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c1 x fth;
        [Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 (sHelp.label.evaluation.cell x) ftt,
          sHelp]) := by
  intros
  rw [c2JoinFuel.eq_2]
  unfold c2JoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuel.eq_12`, verbatim, at the re-encoded def. -/
theorem c2JoinFuel_eq_12_old : ∀ {β : Type} (st : β → Nock.ComputeTable.State)
  (Sof : β → ℕ) (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (c0 c1 : Nock.Walk.NTree β),
  st row = Nock.ComputeTable.State.s9 →
    Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n.succ (Nock.Walk.NTree.node row [c0, c1]) x
        x_1 =
      Nock.Walk.NTree.node
        (Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2SkeletonRow sv ax (st row) (Sof row) x x_1
          (List.map Nock.Walk.NTree.label
            (have coreF :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
            have sCore := Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 x coreF;
            have arm := sv Nock.MemoryTable.MState.verify_child (Sof row + 3);
            [sCore,
              Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c1 sCore.label.evaluation arm])))
        (have coreF :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail x_1);
        have sCore := Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c0 x coreF;
        have arm := sv Nock.MemoryTable.MState.verify_child (Sof row + 3);
        [sCore, Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c1 sCore.label.evaluation arm]) := by
  intros
  rw [c2JoinFuel.eq_2]
  unfold c2JoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `c2JoinFuel.eq_13`, verbatim, at the re-encoded def. -/
theorem c2JoinFuel_eq_13_old : ∀ {β : Type} (st : β → Nock.ComputeTable.State)
  (Sof : β → ℕ) (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (ax : ℕ → ℕ) (x x_1 : Nock.Noun) (n : ℕ) (row : β)
  (ch : List (Nock.Walk.NTree β)),
  (st row = Nock.ComputeTable.State.s0 → ch = [] → False) →
    (st row = Nock.ComputeTable.State.s1 → ch = [] → False) →
      (∀ (c0 c1 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.cons → ch = [c0, c1] → False) →
        (∀ (c0 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.s3 → ch = [c0] → False) →
          (∀ (c0 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.s4 → ch = [c0] → False) →
            (∀ (c0 c1 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.s5 → ch = [c0, c1] → False) →
              (∀ (c0 c1 c2 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.s2 → ch = [c0, c1, c2] → False) →
                (∀ (c0 c1 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.s6 → ch = [c0, c1] → False) →
                  (∀ (c0 c1 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.s7 → ch = [c0, c1] → False) →
                    (∀ (c0 c1 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.s8 → ch = [c0, c1] → False) →
                      (∀ (c0 c1 : Nock.Walk.NTree β), st row = Nock.ComputeTable.State.s9 → ch = [c0, c1] → False) →
                        Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n.succ
                            (Nock.Walk.NTree.node row ch) x x_1 =
                          Nock.Walk.NTree.node
                            (Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2SkeletonRow sv ax (st row) (Sof row) x x_1
                              (List.map Nock.Walk.NTree.label
                                (List.map
                                  (fun c =>
                                    Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c x x_1)
                                  ch)))
                            (List.map
                              (fun c => Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2.c2JoinFuel st Sof sv ax n c x x_1)
                              ch) := by
  intros
  rw [c2JoinFuel.eq_2]
  unfold c2JoinKids
  split <;> simp_all

/-- The C2 join at fuel `t.size` (as `mapComputeJoinIn` / `builtJoin`). -/
def c2Join (st : β → State) (Sof : β → ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ)
    (t : NTree β) (subj formula : Noun) : NTree ComputeRowSkeleton :=
  c2JoinFuel st Sof sv ax t.size t subj formula

theorem c2JoinFuel_subject (st : β → State) (Sof : β → ℕ) (sv : MState → ℕ → Noun)
    (ax : ℕ → ℕ) (fuel : ℕ) (t : NTree β) (subj formula : Noun) :
    (c2JoinFuel st Sof sv ax fuel t subj formula).label.subject = subj := by
  cases fuel <;> cases t <;> rfl

theorem c2JoinFuel_formula (st : β → State) (Sof : β → ℕ) (sv : MState → ℕ → Noun)
    (ax : ℕ → ℕ) (fuel : ℕ) (t : NTree β) (subj formula : Noun) :
    (c2JoinFuel st Sof sv ax fuel t subj formula).label.formula = formula := by
  cases fuel <;> cases t <;> rfl

theorem c2JoinFuel_state (st : β → State) (Sof : β → ℕ) (sv : MState → ℕ → Noun)
    (ax : ℕ → ℕ) (fuel : ℕ) (t : NTree β) (subj formula : Noun) :
    (c2JoinFuel st Sof sv ax fuel t subj formula).label.state = st t.label := by
  cases fuel <;> cases t <;> rfl

end Join

/-! ## §B  The shape: the C2 join projects to the S3 event's `builtJoin` -/

section Shape

/-- The four fields the S3 census reads, off a skeleton row. -/
def rowTuple (r : ComputeRowSkeleton) : State × Noun × Noun × Noun :=
  (r.state, r.subject, r.formula, r.evaluation)

/-- The same four fields off an `S3Node`. -/
def s3Tuple (n : S3Node) : State × Noun × Noun × Noun :=
  (n.state, n.subject, n.formula, n.evaluation)

theorem kidEval_of_tuple {kids : List ComputeRowSkeleton} {kids' : List S3Node}
    (h : kids.map rowTuple = kids'.map s3Tuple) (i : ℕ) :
    (kidSkel kids i).evaluation = kidEval kids' i := by
  unfold kidSkel kidEval
  have hlen : kids.length = kids'.length := by
    have := congrArg List.length h; simpa using this
  by_cases hi : i < kids.length
  · have hi' : i < kids'.length := hlen ▸ hi
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi']
    simp only [Option.getD_some, Option.map_some]
    have := congrArg (fun l => l[i]?) h
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
      Option.map_some, Option.some.injEq] at this
    exact congrArg (fun p : State × Noun × Noun × Noun => p.2.2.2) this
  · have hi' : ¬ i < kids'.length := hlen ▸ hi
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    rfl

theorem c2SkeletonRow_tuple (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (st : State) (S : ℕ)
    (subj formula : Noun) {kids : List ComputeRowSkeleton} {kids' : List S3Node}
    (h : kids.map rowTuple = kids'.map s3Tuple) :
    rowTuple (c2SkeletonRow sv ax st S subj formula kids) =
      s3Tuple (builtNode sv (st, S) subj formula kids') := by
  simp only [rowTuple, s3Tuple, c2SkeletonRow, builtNode]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
  show c2Evaluation sv st S formula kids = builtEvaluation sv st S formula kids'
  cases st <;> (simp only [c2Evaluation, builtEvaluation, kidEval_of_tuple h]; try rfl)

/-- **The shape theorem.**  The C2 join on the S3 label tree projects, row by row, to the S3
event's `builtJoinFuel`: same tree, same state, subject, formula and evaluation at every node, at
every fuel, root subject and formula. -/
theorem c2JoinFuel_shape (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) :
    ∀ (n : ℕ) (t : NTree (State × ℕ)) (subj formula : Noun),
      mapNTree rowTuple (c2JoinFuel Prod.fst Prod.snd sv ax n t subj formula) =
        mapNTree s3Tuple (builtJoinFuel sv n t subj formula) := by
  intro n
  induction n with
  | zero =>
      intro t subj formula
      cases t with
      | node row ch =>
          simp only [c2JoinFuel, builtJoinFuel, c2JoinKids, builtJoinKids, mapNTree, List.map_nil]
          rw [c2SkeletonRow_tuple sv ax row.1 row.2 subj formula (kids' := []) rfl]
  | succ n ih =>
      intro t subj formula
      cases t with
      | node row ch =>
          -- the label tuple of a joined child, from the IH
          have hlab : ∀ (c : NTree (State × ℕ)) (s f : Noun),
              rowTuple (c2JoinFuel Prod.fst Prod.snd sv ax n c s f).label =
                s3Tuple (builtJoinFuel sv n c s f).label := by
            intro c s f
            have := congrArg NTree.label (ih c s f)
            simpa [mapNTree_label] using this
          have heval : ∀ (c : NTree (State × ℕ)) (s f : Noun),
              (c2JoinFuel Prod.fst Prod.snd sv ax n c s f).label.evaluation =
                (builtJoinFuel sv n c s f).label.evaluation := fun c s f =>
            congrArg (fun p : State × Noun × Noun × Noun => p.2.2.2) (hlab c s f)
          -- the kids' label lists agree, hence the node tuple agrees
          have hnode : ∀ (kids : List (NTree ComputeRowSkeleton)) (kids' : List (NTree S3Node)),
              kids.map (mapNTree rowTuple) = kids'.map (mapNTree s3Tuple) →
              mapNTree rowTuple
                  (NTree.node (c2SkeletonRow sv ax row.1 row.2 subj formula
                    (kids.map NTree.label)) kids) =
                mapNTree s3Tuple
                  (NTree.node (builtNode sv row subj formula (kids'.map NTree.label)) kids') := by
            intro kids kids' hk
            have hlabs : (kids.map NTree.label).map rowTuple =
                (kids'.map NTree.label).map s3Tuple := by
              have := congrArg (List.map NTree.label) hk
              simpa [List.map_map, Function.comp_def, mapNTree_label] using this
            simp only [mapNTree]
            rw [hk, c2SkeletonRow_tuple sv ax row.1 row.2 subj formula hlabs]
          -- case split on the state and the children, exactly as the join does, then unfold
          rcases row with ⟨s, S⟩
          cases s <;> rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, ch'⟩⟩⟩⟩ <;>
            (simp only [c2JoinFuel, builtJoinFuel, c2JoinKids, builtJoinKids]
             refine hnode _ _ ?_
             simp only [List.map_cons, List.map_nil, List.map_map, Function.comp_def, ih, heval]
             try rfl)

end Shape

/-! ## §C  Over `O`: the S-carrying exec tree, the C2 skeleton and the strategy -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

variable (O : OptimizedStrictNockVMROMPackage F K hOrb)

/-- `P.computeChip` at `O := P.optimized` (as in `StrategyOfTracesR0`). -/
local notation "CC[" O "]" =>
  ProductionNamedComputeRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.compRows_pos
    (OptimizedStrictNockVMROMPackage.computeNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.computeChallenge O)
    (OptimizedStrictNockVMROMPackage.computePublic O) (OptimizedStrictNockVMROMPackage.orbit O)

/-- `P.memoryChip` at `O := P.optimized` (as in `StrategyOfTracesR0`). -/
local notation "MC[" O "]" =>
  namedFinalMemoryRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.memoryChallenge O)
    (OptimizedStrictNockVMROMPackage.memoryPublic O) (OptimizedStrictNockVMROMPackage.orbit O)
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem

/-- **The served lookup of the traces**: `PreZComputeCore.Served.servedNounOfEnvs` at the family
memory base envs (`memoryEnvsR0`, round-0 columns `0, 1, 2, 180, 181`), modulus `ringChar K`,
`kMem` roots. -/
def c2ServedOf
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : MState → ℕ → Noun :=
  PreZComputeCore.Served.servedNounOfEnvs K (ringChar K) O.family.problem.cfg.kMem
    (memoryEnvsR0 O Qm c) O.family.problem.cfg.memRows_pos

/-- **The round-0 record axis of an exponent**: the certificate axis the exponent locator assigns to
it on the family compute source envs (`certAxisOfEnvs`; the memory wrap's `axOfRowsR0` reads the
same function at the row's `natLift reqIdx`). -/
def c2AxOf
    (Qc : Fin (CC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : ℕ → ℕ :=
  fun e => certAxisOfEnvs (computeEnvsR0 O Qc c) e

/-- The round-0 carrier `S = natLift (col 302)` of compute row `i`. -/
def c2SAt
    (Qc : Fin (CC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin O.family.problem.cfg.compRows) : ℕ :=
  RecordCarrier.natLift ((computeEnvsR0 O Qc c i).trace 302)

/-- The 1-indexed decoded compute label with its carrier attached (`lblC`'s off-range convention). -/
def lblCS
    (Qc : Fin (CC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    ℕ → (State × DTcomp K) × ℕ :=
  fun i =>
    (lblC O Qc c i,
      if h : i - 1 < O.family.problem.cfg.compRows then c2SAt O Qc c ⟨i - 1, h⟩
      else c2SAt O Qc c ⟨0, O.family.problem.cfg.compRows_pos⟩)

/-- **The S-carrying exec tree**: `execOfTraces`'s compute tree with every row's carrier attached
(`reconTree` of `lblCS` at the same fanouts). -/
def c2TreeOfTraces
    (Qc : Fin (CC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : NTree ((State × DTcomp K) × ℕ) :=
  reconTree (foC O Qc c) (lblCS O Qc c) O.family.problem.cfg.compRows

theorem mapNTree_buildT' {α β : Type*} (f : α → β) (fo : ℕ → ℕ) (lbl : ℕ → α) (h : ℕ) :
    ∀ i, mapNTree f (buildT fo lbl h i) = buildT fo (fun j => f (lbl j)) h i := by
  intro i
  suffices ∀ d i, h - i = d →
      mapNTree f (buildT fo lbl h i) = buildT fo (fun j => f (lbl j)) h i from this (h - i) i rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i hi
    rw [buildT, mapNTree, buildT]
    refine congrArg (NTree.node (f (lbl i))) ?_
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    have hmem : j.1 ∈ childIdxs fo h i := j.property
    have hlt : h - j.1 < d := by
      simp only [childIdxs, List.mem_filter, decide_eq_true_eq] at hmem
      omega
    exact ih (h - j.1) hlt j.1 rfl

/-- The S-carrying tree projects to the exec tree. -/
theorem c2TreeOfTraces_fst
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    mapNTree Prod.fst (c2TreeOfTraces O Qc c) = (execOfTraces O Qc Qm c h).computeTree := by
  unfold c2TreeOfTraces reconTree
  rw [mapNTree_buildT']
  rfl

/-- **The C2 compute tree of the traces**: the C2 join on the S-carrying exec tree, at the served
lookup and the certificate axes of the traces, rooted at the package claim's subject and formula. -/
def c2ComputeTree
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : NTree ComputeRowSkeleton :=
  c2Join (fun l => l.1.1) (fun l => l.2) (c2ServedOf O Qm c) (c2AxOf O Qc c)
    (c2TreeOfTraces O Qc c) O.verifier.raw.claim.subject O.verifier.raw.claim.formula

/-- **The C2 skeleton**: the C2 compute tree with the a-bearing round-0 memory forest
(`decodedSkeletonR0A`'s, verbatim). -/
def decodedSkeletonC2
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) : SemanticSkeleton where
  computeTree := c2ComputeTree O Qc Qm c
  memoryForest := (decodedSkeletonR0A O Qc Qm c h).memoryForest

theorem decodedSkeletonC2_memoryForest
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    (decodedSkeletonC2 O Qc Qm c h).memoryForest = (decodedSkeletonR0A O Qc Qm c h).memoryForest :=
  rfl

theorem decodedSkeletonC2_computeTree
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    (decodedSkeletonC2 O Qc Qm c h).computeTree = c2ComputeTree O Qc Qm c := rfl

/-- The C2 skeleton's public claim: the package claim's subject and formula, the C2 root
evaluation. -/
theorem decodedSkeletonC2_publicClaim_subject
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    (decodedSkeletonC2 O Qc Qm c h).publicClaim.subject = O.verifier.raw.claim.subject := by
  show (c2ComputeTree O Qc Qm c).label.subject = _
  unfold c2ComputeTree c2Join
  exact c2JoinFuel_subject _ _ _ _ _ _ _ _

theorem decodedSkeletonC2_publicClaim_formula
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    (decodedSkeletonC2 O Qc Qm c h).publicClaim.formula = O.verifier.raw.claim.formula := by
  show (c2ComputeTree O Qc Qm c).label.formula = _
  unfold c2ComputeTree c2Join
  exact c2JoinFuel_formula _ _ _ _ _ _ _ _

/-- **The C2 timestamp strategy**: `timestampOfTracesR0` with the C2 skeleton's public claim (the
round-0 execution template verbatim). -/
def timestampOfTracesC2
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K) :=
  DataOnlyTemplateFixedStagedTimestampStrategy.ofRawData
    (decodedSkeletonC2 O Qc Qm c h).publicClaim
    (fun seed => cfgTemplateOfTraces O Qc Qm c seed.1)
    (fun seed => execTemplateOfTracesR0 O Qc Qm c h seed.1)
    (fun _ => rfl)

/-- **The round-0 built strategy with the C2 skeleton**: the generic chain `verifierGen` at
`timestampOfTracesC2`, skeleton `decodedSkeletonC2`.  `publicClaim_eq` is `rfl` (the claim IS the
skeleton's). -/
def strategyOfTracesR0AC2
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    ProductionStrategy F K where
  verifier := verifierGen O (timestampOfTracesC2 O Qc Qm c h) tag Qc Qm c
  skeleton := decodedSkeletonC2 O Qc Qm c h
  publicClaim_eq := rfl

/-! ### Definitional facts -/

theorem strategyOfTracesR0AC2_skeleton
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    (strategyOfTracesR0AC2 O tag Qc Qm c h).skeleton = decodedSkeletonC2 O Qc Qm c h := rfl

/-- The specialized execution is the round-0 strategy's (hence the a-bearing one's):
`specializedProblem` reads `afterSeed` only, which `timestampOfTracesC2` shares with
`timestampOfTracesR0`. -/
theorem specializedExec_C2_eq
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    (strategyOfTracesR0AC2 O tag Qc Qm c h).specializedExec z hz α lmb =
      (strategyOfTracesR0A O tag Qc Qm c h).specializedExec z hz α lmb := rfl

theorem specializedCfg_C2_eq
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    (strategyOfTracesR0AC2 O tag Qc Qm c h).specializedCfg z hz α lmb =
      (strategyOfTracesR0A O tag Qc Qm c h).specializedCfg z hz α lmb := rfl

theorem specializedCfg_C2_z
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    ((strategyOfTracesR0AC2 O tag Qc Qm c h).specializedCfg z hz α lmb).challenges.z = z := rfl

/-- The verifier's claim is the C2 skeleton's public claim (what `Accepts` and `GenuineTargetAt`
read); its subject and formula are the package claim's. -/
theorem strategyOfTracesR0AC2_claim
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    (strategyOfTracesR0AC2 O tag Qc Qm c h).verifier.raw.claim =
      (decodedSkeletonC2 O Qc Qm c h).publicClaim := rfl

end

end Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
