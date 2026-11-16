/-
  Nock/NockVMROM/Thm54/S3PairEvent.lean

  **H1.5b Part 2b-i/3 — the S3 event: the pre-`z` collision census of the route-B built skeleton,
  with a premise-free card lemma**.

  `hbind`'s binding induction on route B needs, at every row, the
  separation `SepSeed z a b` of a few pairs of nouns whose fingerprints the chips only equate:
  the OP5 equality operands (`hfaith`), and under served decomposition the formula / tail
  decompositions (`formulaCons`, `tailCons`, `branchTailCons`; `ComputedWindow.s3_pairs_separated`). This module builds that event, below the pinned file, so 2b-ii can name it:

  * **§1 — the window** `s3Window M Λ = M + max M Λ`.
  * **§2 — the round-0 built skeleton (route B's C2 skeleton).**  The compute tree is rebuilt from the
    round-0 compute columns only: each row's state (selectors `1..10`, `computeStateOf`) and its
    request carrier `S` (column `302`, `natLift`), by the lifted inverse BFS
    (`StrategyOfTracesLift.rebuildForest`, one root).  The noun join `builtJoinFuel` is the lifted
    `StrategyOfTracesLift.mapComputeJoinInFuel` with exactly the route-B C2 substitutions
: the root subject and formula are the CLAIM's (not
    `joinNoun pub.s` / `joinFormulaDeep`); OP0's evaluation is the served `verify_child` noun of the
    row's request `2` (exponent `S + 2`, record slot `1 = ⟨subj, eval, ax⟩`); OP9's arm is the served
    `verify_child` noun of request `3` (exponent `S + 3`, record slot `2 = ⟨core, arm, ax⟩`).  Every
    other noun is the structural join's (heads / tails of the formula, sibling evaluations).  The
    served lookup is an argument `sv : MState → ℕ → Noun`; the event instantiates it at
    `PreZComputeCore.Served.servedNounOfEnvs` (`reqIdx`-located pre-`z` decode, memory base columns
    `0, 1, 2, 180, 181`).  No `nounByFP`, no fingerprint, no `ts`, no coin is read.
  * **§3 — the S3 pairs.**  Per built row, with `f_t`, `f_th`, `f_tth` the served `verify_child`
    nouns of requests `1, 2, 3` (record slots `⟨f, f_t, 3⟩`, `⟨f_t, f_th, 2⟩`, `⟨f_tt, f_tth, 2⟩`):
    `formulaCons = (f, cell (head f) f_t)` at every row; `tailCons = (f_t, cell f_th (tail f_t))` at
    OP2/5/6/7/8/9; `branchTailCons = (tail f_t, cell f_tth (tail (tail f_t)))` at OP6; the operand
    pair `(e₀, e₁)` at OP5.  At most `3` per row (`rowS3Pairs_length_le`); the census is the first
    `N` built rows in BFS order, so `|s3Pairs| ≤ 3N` with no premise (`s3PairsOf_length_le`).
  * **§4 — the event and the card lemma.**  `s3PairEventOfEnvs := liftSeed (pairBadSeeds (s3Window M Λ)
    pairs)` on `JointCoins`, `s3PairEventOf := liftP8Failure` of it on the production tuple, and
    **`s3PairEventOf_card_le : card ≤ |𝕂|¹⁰ · (3N · (2·s3Window M Λ − 1))` at EVERY env tuple, every
    claim, every `Λ`** (rule 8(b): the guard sits inside `pairBadSeeds`).  `s3PairWorkload T Λ` is the
    same numeral at a strategy's skeleton row counts (the `workload` summand 2b-ii adds).

Paper: the paper (collision count `2Λ − 1` per pair, union), `:1054-1076` (Nock steps),
  `:1728-1801` (`V_comp`, the record slots), `:507-509`, `:800-803` (round 0 before `z`).
-/
import Nock.NockVMROM.Thm54.PreZComputeCore
import Nock.NockVMROM.Thm54.StrategyOfTracesLift
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.ProductionP8Containment

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.S3PairEvent

open Nock
open Nock.Walk
open Nock.Reified
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.Framework.Reify

noncomputable section

/-! ## §1  The split window -/

/-- **The S3 window** `M + max M Λ` (served nouns `≤ M`, computed `≤ Λ`, mixed cells `≤ M + max M Λ`;
the leaf-bound probe's `Λ3`).  Verbatim `ComputedWindow.window3`, restated here because
`ComputedWindow` sits above the pinned file (`Batch980.s3Window_eq_window3`, `rfl`). -/
def s3Window (M Λ : ℕ) : ℕ := M + max M Λ

theorem s3Window_le_two_mul {M Λ S : ℕ} (hM : M ≤ S) (hΛ : Λ ≤ S) : s3Window M Λ ≤ 2 * S := by
  unfold s3Window
  have : max M Λ ≤ S := max_le hM hΛ
  omega

/-! ## §2  The round-0 built skeleton (route B's C2 skeleton) -/

/-- One built row: its state, its request carrier `S`, and the join's three nouns. -/
structure S3Node where
  state : State
  S : ℕ
  subject : Noun
  formula : Noun
  evaluation : Noun

/-- The `i`-th kid's evaluation (`atom 0` past the end, as `StrategyOfTracesLift.kidSkel`'s dummy). -/
def kidEval (kids : List S3Node) (i : ℕ) : Noun :=
  (kids[i]?.map S3Node.evaluation).getD (Noun.atom 0)

/-- **The row's evaluation**: `StrategyOfTracesLift.joinEvaluation` with OP0's `nounByFP … e`
replaced by the served `verify_child` noun of the row's request `2` (exponent `S + 2`). -/
def builtEvaluation (sv : MState → ℕ → Noun) (st : State) (S : ℕ) (formula : Noun)
    (kids : List S3Node) : Noun :=
  match st with
  | .cons => .cell (kidEval kids 0) (kidEval kids 1)
  | .s1 => StrategyOfTracesLift.nounTail formula
  | .s3 => Noun.wut (kidEval kids 0)
  | .s4 =>
      match kidEval kids 0 with
      | .atom k => .atom (k + 1)
      | c => c
  | .s5 => Noun.tis (kidEval kids 0) (kidEval kids 1)
  | .s2 => kidEval kids 2
  | .s6 | .s7 | .s8 => kidEval kids 0
  | .s9 => kidEval kids 1
  | .s0 => sv .verify_child (S + 2)

/-- The node a row produces from its inputs and its kids' nodes. -/
def builtNode (sv : MState → ℕ → Noun) (row : State × ℕ) (subj formula : Noun)
    (kids : List S3Node) : S3Node :=
  ⟨row.1, row.2, subj, formula, builtEvaluation sv row.1 row.2 formula kids⟩

/-- MIG 4.35: the children of `builtJoinFuel` at one row, with the recursive call `f` as a parameter.
Non-recursive; split out so the kernel checks the per-opcode match outside the structural recursion (4.35 reports
deep recursion on the inlined form). The `builtJoinFuel_eq_k_old` lemmas restate the 4.31 equations. -/
def builtJoinKids (sv : MState → ℕ → Noun)
    (f : NTree (State × ℕ) → Noun → Noun → NTree S3Node)
    (row : State × ℕ) (ch : List (NTree (State × ℕ))) (subj formula : Noun) :
    List (NTree S3Node) :=
  match row.1, ch with
  | .s0, [] => []
  | .s1, [] => []
  | .cons, [c0, c1] =>
      [f c0 subj (StrategyOfTracesLift.nounHead formula),
       f c1 subj (StrategyOfTracesLift.nounTail formula)]
  | .s3, [c0] =>
      [f c0 subj (StrategyOfTracesLift.nounTail formula)]
  | .s4, [c0] =>
      [f c0 subj (StrategyOfTracesLift.nounTail formula)]
  | .s5, [c0, c1] =>
      [f c0 subj
        (StrategyOfTracesLift.nounHead (StrategyOfTracesLift.nounTail formula)),
       f c1 subj
        (StrategyOfTracesLift.nounTail (StrategyOfTracesLift.nounTail formula))]
  | .s2, [c0, c1, c2] =>
      let s0 := f c0 subj
        (StrategyOfTracesLift.nounHead (StrategyOfTracesLift.nounTail formula))
      let s1 := f c1 subj
        (StrategyOfTracesLift.nounTail (StrategyOfTracesLift.nounTail formula))
      [s0, s1, f c2 s0.label.evaluation s1.label.evaluation]
  | .s6, [c0, c1] =>
      let fth := StrategyOfTracesLift.nounHead (StrategyOfTracesLift.nounTail formula)
      let ftth := StrategyOfTracesLift.nounHead
        (StrategyOfTracesLift.nounTail (StrategyOfTracesLift.nounTail formula))
      let fttt := StrategyOfTracesLift.nounTail
        (StrategyOfTracesLift.nounTail (StrategyOfTracesLift.nounTail formula))
      let sCond := f c1 subj fth
      let b :=
        match sCond.label.evaluation with
        | .atom k => k
        | _ => 0
      [f c0 subj (if b = 0 then ftth else fttt), sCond]
  | .s7, [c0, c1] =>
      let fth := StrategyOfTracesLift.nounHead (StrategyOfTracesLift.nounTail formula)
      let ftt := StrategyOfTracesLift.nounTail (StrategyOfTracesLift.nounTail formula)
      let sHelp := f c1 subj fth
      [f c0 sHelp.label.evaluation ftt, sHelp]
  | .s8, [c0, c1] =>
      let fth := StrategyOfTracesLift.nounHead (StrategyOfTracesLift.nounTail formula)
      let ftt := StrategyOfTracesLift.nounTail (StrategyOfTracesLift.nounTail formula)
      let sHelp := f c1 subj fth
      [f c0 (Noun.cell sHelp.label.evaluation subj) ftt, sHelp]
  | .s9, [c0, c1] =>
      let coreF := StrategyOfTracesLift.nounTail (StrategyOfTracesLift.nounTail formula)
      let sCore := f c0 subj coreF
      let arm := sv .verify_child (row.2 + 3)
      [sCore, f c1 sCore.label.evaluation arm]
  | _, ch' =>
      ch'.map fun c => f c subj formula

/-- **The route-B noun join, at fuel**: `StrategyOfTracesLift.mapComputeJoinInFuel`'s recursion
verbatim (children's inputs from heads / tails of the formula and sibling evaluations, in
evaluation order), with OP9's arm the served `verify_child` noun of request `3` (`S + 3`). -/
def builtJoinFuel (sv : MState → ℕ → Noun) :
    ℕ → NTree (State × ℕ) → Noun → Noun → NTree S3Node
  | 0, .node row _, subj, formula =>
      .node (builtNode sv row subj formula []) []
  | n + 1, .node row ch, subj, formula =>
      let kids : List (NTree S3Node) :=
        builtJoinKids sv (fun c s fo => builtJoinFuel sv n c s fo) row ch subj formula
      .node (builtNode sv row subj formula (kids.map NTree.label)) kids

attribute [simp] builtJoinKids

/-- MIG 4.35: the 4.31 auto-generated equation `builtJoinFuel.eq_1`, verbatim, at the re-encoded def. -/
theorem builtJoinFuel_eq_1_old : ∀ (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (subj formula : Nock.Noun)
  (row : Nock.ComputeTable.State × ℕ) (children : List (Nock.Walk.NTree (Nock.ComputeTable.State × ℕ))),
  builtJoinFuel sv 0 (Nock.Walk.NTree.node row children) subj formula = Nock.Walk.NTree.node (builtNode sv row subj formula []) [] := by
  intros; rfl

/-- MIG 4.35: the 4.31 auto-generated equation `builtJoinFuel.eq_2`, verbatim, at the re-encoded def. -/
theorem builtJoinFuel_eq_2_old : ∀ (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (subj formula : Nock.Noun) (n : ℕ)
  (row : Nock.ComputeTable.State × ℕ),
  row.1 = Nock.ComputeTable.State.s0 →
    builtJoinFuel sv n.succ (Nock.Walk.NTree.node row []) subj formula =
      Nock.Walk.NTree.node (builtNode sv row subj formula (List.map Nock.Walk.NTree.label [])) [] := by
  intros
  rw [builtJoinFuel.eq_2]
  unfold builtJoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `builtJoinFuel.eq_3`, verbatim, at the re-encoded def. -/
theorem builtJoinFuel_eq_3_old : ∀ (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (subj formula : Nock.Noun) (n : ℕ)
  (row : Nock.ComputeTable.State × ℕ),
  row.1 = Nock.ComputeTable.State.s1 →
    builtJoinFuel sv n.succ (Nock.Walk.NTree.node row []) subj formula =
      Nock.Walk.NTree.node (builtNode sv row subj formula (List.map Nock.Walk.NTree.label [])) [] := by
  intros
  rw [builtJoinFuel.eq_2]
  unfold builtJoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `builtJoinFuel.eq_4`, verbatim, at the re-encoded def. -/
theorem builtJoinFuel_eq_4_old : ∀ (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (subj formula : Nock.Noun) (n : ℕ)
  (row : Nock.ComputeTable.State × ℕ) (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
  row.1 = Nock.ComputeTable.State.cons →
    builtJoinFuel sv n.succ (Nock.Walk.NTree.node row [c0, c1]) subj formula =
      Nock.Walk.NTree.node
        (builtNode sv row subj formula
          (List.map Nock.Walk.NTree.label
            [builtJoinFuel sv n c0 subj (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead formula),
              builtJoinFuel sv n c1 subj (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula)]))
        [builtJoinFuel sv n c0 subj (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead formula),
          builtJoinFuel sv n c1 subj (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula)] := by
  intros
  rw [builtJoinFuel.eq_2]
  unfold builtJoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `builtJoinFuel.eq_5`, verbatim, at the re-encoded def. -/
theorem builtJoinFuel_eq_5_old : ∀ (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (subj formula : Nock.Noun) (n : ℕ)
  (row : Nock.ComputeTable.State × ℕ) (c0 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
  row.1 = Nock.ComputeTable.State.s3 →
    builtJoinFuel sv n.succ (Nock.Walk.NTree.node row [c0]) subj formula =
      Nock.Walk.NTree.node
        (builtNode sv row subj formula
          (List.map Nock.Walk.NTree.label
            [builtJoinFuel sv n c0 subj (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula)]))
        [builtJoinFuel sv n c0 subj (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula)] := by
  intros
  rw [builtJoinFuel.eq_2]
  unfold builtJoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `builtJoinFuel.eq_6`, verbatim, at the re-encoded def. -/
theorem builtJoinFuel_eq_6_old : ∀ (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (subj formula : Nock.Noun) (n : ℕ)
  (row : Nock.ComputeTable.State × ℕ) (c0 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
  row.1 = Nock.ComputeTable.State.s4 →
    builtJoinFuel sv n.succ (Nock.Walk.NTree.node row [c0]) subj formula =
      Nock.Walk.NTree.node
        (builtNode sv row subj formula
          (List.map Nock.Walk.NTree.label
            [builtJoinFuel sv n c0 subj (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula)]))
        [builtJoinFuel sv n c0 subj (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula)] := by
  intros
  rw [builtJoinFuel.eq_2]
  unfold builtJoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `builtJoinFuel.eq_7`, verbatim, at the re-encoded def. -/
theorem builtJoinFuel_eq_7_old : ∀ (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (subj formula : Nock.Noun) (n : ℕ)
  (row : Nock.ComputeTable.State × ℕ) (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
  row.1 = Nock.ComputeTable.State.s5 →
    builtJoinFuel sv n.succ (Nock.Walk.NTree.node row [c0, c1]) subj formula =
      Nock.Walk.NTree.node
        (builtNode sv row subj formula
          (List.map Nock.Walk.NTree.label
            [builtJoinFuel sv n c0 subj
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula)),
              builtJoinFuel sv n c1 subj
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula))]))
        [builtJoinFuel sv n c0 subj
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula)),
          builtJoinFuel sv n c1 subj
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula))] := by
  intros
  rw [builtJoinFuel.eq_2]
  unfold builtJoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `builtJoinFuel.eq_8`, verbatim, at the re-encoded def. -/
theorem builtJoinFuel_eq_8_old : ∀ (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (subj formula : Nock.Noun) (n : ℕ)
  (row : Nock.ComputeTable.State × ℕ) (c0 c1 c2 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
  row.1 = Nock.ComputeTable.State.s2 →
    builtJoinFuel sv n.succ (Nock.Walk.NTree.node row [c0, c1, c2]) subj formula =
      Nock.Walk.NTree.node
        (builtNode sv row subj formula
          (List.map Nock.Walk.NTree.label
            (have s0 :=
              builtJoinFuel sv n c0 subj
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula));
            have s1 :=
              builtJoinFuel sv n c1 subj
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula));
            [s0, s1, builtJoinFuel sv n c2 s0.label.evaluation s1.label.evaluation])))
        (have s0 :=
          builtJoinFuel sv n c0 subj
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula));
        have s1 :=
          builtJoinFuel sv n c1 subj
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula));
        [s0, s1, builtJoinFuel sv n c2 s0.label.evaluation s1.label.evaluation]) := by
  intros
  rw [builtJoinFuel.eq_2]
  unfold builtJoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `builtJoinFuel.eq_9`, verbatim, at the re-encoded def. -/
theorem builtJoinFuel_eq_9_old : ∀ (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (subj formula : Nock.Noun) (n : ℕ)
  (row : Nock.ComputeTable.State × ℕ) (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
  row.1 = Nock.ComputeTable.State.s6 →
    builtJoinFuel sv n.succ (Nock.Walk.NTree.node row [c0, c1]) subj formula =
      Nock.Walk.NTree.node
        (builtNode sv row subj formula
          (List.map Nock.Walk.NTree.label
            (let fth :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula);
            have ftth :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula));
            have fttt :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                  (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula));
            let sCond := builtJoinFuel sv n c1 subj fth;
            let b :=
              match sCond.label.evaluation with
              | Nock.Noun.atom k => k
              | subj => 0;
            [builtJoinFuel sv n c0 subj (if b = 0 then ftth else fttt), sCond])))
        (let fth :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula);
        have ftth :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula));
        have fttt :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
            (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
              (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula));
        let sCond := builtJoinFuel sv n c1 subj fth;
        let b :=
          match sCond.label.evaluation with
          | Nock.Noun.atom k => k
          | subj => 0;
        [builtJoinFuel sv n c0 subj (if b = 0 then ftth else fttt), sCond]) := by
  intros
  rw [builtJoinFuel.eq_2]
  unfold builtJoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `builtJoinFuel.eq_10`, verbatim, at the re-encoded def. -/
theorem builtJoinFuel_eq_10_old : ∀ (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (subj formula : Nock.Noun) (n : ℕ)
  (row : Nock.ComputeTable.State × ℕ) (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
  row.1 = Nock.ComputeTable.State.s7 →
    builtJoinFuel sv n.succ (Nock.Walk.NTree.node row [c0, c1]) subj formula =
      Nock.Walk.NTree.node
        (builtNode sv row subj formula
          (List.map Nock.Walk.NTree.label
            (have fth :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula);
            have ftt :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula);
            have sHelp := builtJoinFuel sv n c1 subj fth;
            [builtJoinFuel sv n c0 sHelp.label.evaluation ftt, sHelp])))
        (have fth :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula);
        have ftt :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula);
        have sHelp := builtJoinFuel sv n c1 subj fth;
        [builtJoinFuel sv n c0 sHelp.label.evaluation ftt, sHelp]) := by
  intros
  rw [builtJoinFuel.eq_2]
  unfold builtJoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `builtJoinFuel.eq_11`, verbatim, at the re-encoded def. -/
theorem builtJoinFuel_eq_11_old : ∀ (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (subj formula : Nock.Noun) (n : ℕ)
  (row : Nock.ComputeTable.State × ℕ) (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
  row.1 = Nock.ComputeTable.State.s8 →
    builtJoinFuel sv n.succ (Nock.Walk.NTree.node row [c0, c1]) subj formula =
      Nock.Walk.NTree.node
        (builtNode sv row subj formula
          (List.map Nock.Walk.NTree.label
            (have fth :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula);
            have ftt :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula);
            have sHelp := builtJoinFuel sv n c1 subj fth;
            [builtJoinFuel sv n c0 (sHelp.label.evaluation.cell subj) ftt, sHelp])))
        (have fth :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounHead (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula);
        have ftt :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula);
        have sHelp := builtJoinFuel sv n c1 subj fth;
        [builtJoinFuel sv n c0 (sHelp.label.evaluation.cell subj) ftt, sHelp]) := by
  intros
  rw [builtJoinFuel.eq_2]
  unfold builtJoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `builtJoinFuel.eq_12`, verbatim, at the re-encoded def. -/
theorem builtJoinFuel_eq_12_old : ∀ (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (subj formula : Nock.Noun) (n : ℕ)
  (row : Nock.ComputeTable.State × ℕ) (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
  row.1 = Nock.ComputeTable.State.s9 →
    builtJoinFuel sv n.succ (Nock.Walk.NTree.node row [c0, c1]) subj formula =
      Nock.Walk.NTree.node
        (builtNode sv row subj formula
          (List.map Nock.Walk.NTree.label
            (have coreF :=
              Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail
                (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula);
            have sCore := builtJoinFuel sv n c0 subj coreF;
            have arm := sv Nock.MemoryTable.MState.verify_child (row.2 + 3);
            [sCore, builtJoinFuel sv n c1 sCore.label.evaluation arm])))
        (have coreF :=
          Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail (Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounTail formula);
        have sCore := builtJoinFuel sv n c0 subj coreF;
        have arm := sv Nock.MemoryTable.MState.verify_child (row.2 + 3);
        [sCore, builtJoinFuel sv n c1 sCore.label.evaluation arm]) := by
  intros
  rw [builtJoinFuel.eq_2]
  unfold builtJoinKids
  split <;> simp_all

/-- MIG 4.35: the 4.31 auto-generated equation `builtJoinFuel.eq_13`, verbatim, at the re-encoded def. -/
theorem builtJoinFuel_eq_13_old : ∀ (sv : Nock.MemoryTable.MState → ℕ → Nock.Noun) (subj formula : Nock.Noun) (n : ℕ)
  (row : Nock.ComputeTable.State × ℕ) (ch : List (Nock.Walk.NTree (Nock.ComputeTable.State × ℕ))),
  (row.1 = Nock.ComputeTable.State.s0 → ch = [] → False) →
    (row.1 = Nock.ComputeTable.State.s1 → ch = [] → False) →
      (∀ (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
          row.1 = Nock.ComputeTable.State.cons → ch = [c0, c1] → False) →
        (∀ (c0 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
            row.1 = Nock.ComputeTable.State.s3 → ch = [c0] → False) →
          (∀ (c0 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
              row.1 = Nock.ComputeTable.State.s4 → ch = [c0] → False) →
            (∀ (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
                row.1 = Nock.ComputeTable.State.s5 → ch = [c0, c1] → False) →
              (∀ (c0 c1 c2 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
                  row.1 = Nock.ComputeTable.State.s2 → ch = [c0, c1, c2] → False) →
                (∀ (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
                    row.1 = Nock.ComputeTable.State.s6 → ch = [c0, c1] → False) →
                  (∀ (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
                      row.1 = Nock.ComputeTable.State.s7 → ch = [c0, c1] → False) →
                    (∀ (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
                        row.1 = Nock.ComputeTable.State.s8 → ch = [c0, c1] → False) →
                      (∀ (c0 c1 : Nock.Walk.NTree (Nock.ComputeTable.State × ℕ)),
                          row.1 = Nock.ComputeTable.State.s9 → ch = [c0, c1] → False) →
                        builtJoinFuel sv n.succ (Nock.Walk.NTree.node row ch) subj formula =
                          Nock.Walk.NTree.node
                            (builtNode sv row subj formula
                              (List.map Nock.Walk.NTree.label (List.map (fun c => builtJoinFuel sv n c subj formula) ch)))
                            (List.map (fun c => builtJoinFuel sv n c subj formula) ch) := by
  intros
  rw [builtJoinFuel.eq_2]
  unfold builtJoinKids
  split <;> simp_all


/-- The join at fuel `t.size` (as `StrategyOfTracesLift.mapComputeJoinIn`). -/
def builtJoin (sv : MState → ℕ → Noun) (t : NTree (State × ℕ)) (subj formula : Noun) :
    NTree S3Node :=
  builtJoinFuel sv t.size t subj formula

section Rows

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **A compute row's round-0 label**: its state (selector columns `1..10`, the lifted
`computeStateOf`) and its request carrier `S = natLift (column 302)`. -/
def preCLabel (env : Env F) : State × ℕ :=
  (StrategyOfTracesLift.computeStateOf env, RecordCarrier.natLift (env.trace 302))

/-- The committed compute rows' round-0 labels, in row order. -/
def preCRows {N : ℕ} (envs : Fin N → Env F) : List (State × ℕ) :=
  (List.finRange N).map fun i => preCLabel (envs i)

/-- **The round-0 compute tree**: the lifted inverse BFS at one root over the round-0 labels
(fanout `fanoutComp` of the state), with `StrategyOfTracesLift.typedComputeTree`'s dummy fallback. -/
def builtTreeOfEnvs {N : ℕ} (envs : Fin N → Env F) : NTree (State × ℕ) :=
  match StrategyOfTracesLift.rebuildForest (fun l : State × ℕ => fanoutComp l.1) 1 (preCRows envs) with
  | t :: _ => t
  | [] => .node (.s0, 0) []

end Rows

/-! ## §3  The S3 pairs -/

/-- **The S3 pairs of one built row** (`ComputedWindow.s3_pair_nouns_le_window3`'s list, with the
served decomposition nouns read at the row's own request exponents `S + 1, S + 2, S + 3`). -/
def rowS3Pairs (sv : MState → ℕ → Noun) (u : NTree S3Node) : List (Noun × Noun) :=
  let nd := u.label
  let ft := sv .verify_child (nd.S + 1)
  let fth := sv .verify_child (nd.S + 2)
  let ftth := sv .verify_child (nd.S + 3)
  let formulaCons := (nd.formula, Noun.cell (StrategyOfTracesLift.nounHead nd.formula) ft)
  let tailCons := (ft, Noun.cell fth (StrategyOfTracesLift.nounTail ft))
  let branchTailCons := (StrategyOfTracesLift.nounTail ft,
    Noun.cell ftth (StrategyOfTracesLift.nounTail (StrategyOfTracesLift.nounTail ft)))
  let kids := u.children.map NTree.label
  match nd.state with
  | .s5 => [formulaCons, tailCons, (kidEval kids 0, kidEval kids 1)]
  | .s6 => [formulaCons, tailCons, branchTailCons]
  | .s2 | .s7 | .s8 | .s9 => [formulaCons, tailCons]
  | _ => [formulaCons]

/-- **At most three pairs per row** (the served decomposition's `k ≤ 3`). -/
theorem rowS3Pairs_length_le (sv : MState → ℕ → Noun) (u : NTree S3Node) :
    (rowS3Pairs sv u).length ≤ 3 := by
  unfold rowS3Pairs
  dsimp only
  split <;> simp

/-- **The S3 census of a built tree**: the first `N` built rows in BFS order, each row's pairs. -/
def s3PairsOf (sv : MState → ℕ → Noun) (N : ℕ) (t : NTree S3Node) : List (Noun × Noun) :=
  ((bfsForest [t]).take N).flatMap (rowS3Pairs sv)

/-- **`|s3Pairs| ≤ 3N`, no premise.** -/
theorem s3PairsOf_length_le (sv : MState → ℕ → Noun) (N : ℕ) (t : NTree S3Node) :
    (s3PairsOf sv N t).length ≤ 3 * N := by
  unfold s3PairsOf
  rw [List.length_flatMap]
  have hsum : ∀ l : List (NTree S3Node),
      (l.map fun u => (rowS3Pairs sv u).length).sum ≤ 3 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons u l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have := rowS3Pairs_length_le sv u
        omega
  have htake := List.length_take_le N (bfsForest [t])
  exact (hsum _).trans (by omega)

section OfEnvs

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The S3 pair list at committed envs** (`s3Pairs`): the route-B built skeleton of the round-0
compute labels, rooted at the claim's subject and formula, joined against the `reqIdx`-located
pre-`z` served lookup of the memory base envs. -/
def s3PairsOfEnvs (K : Type) [Field K] [Algebra F K] (q kroots : ℕ) {N M : ℕ}
    (envsC : Fin N → Env F) (envsM : Fin M → Env F) (hM : 0 < M) (claim : P8PublicClaim) :
    List (Noun × Noun) :=
  s3PairsOf (PreZComputeCore.Served.servedNounOfEnvs K q kroots envsM hM) N
    (builtJoin (PreZComputeCore.Served.servedNounOfEnvs K q kroots envsM hM)
      (builtTreeOfEnvs envsC) claim.subject claim.formula)

theorem s3PairsOfEnvs_length_le (K : Type) [Field K] [Algebra F K] (q kroots : ℕ) {N M : ℕ}
    (envsC : Fin N → Env F) (envsM : Fin M → Env F) (hM : 0 < M) (claim : P8PublicClaim) :
    (s3PairsOfEnvs K q kroots envsC envsM hM claim).length ≤ 3 * N :=
  s3PairsOf_length_le _ _ _

/-! ## §4  The event and its card lemma -/

/-- **The S3 event on `JointCoins K`**: the `z`-cylinder over the guarded bad seeds of the S3
census at the window `s3Window M Λ`. -/
def s3PairEventOfEnvs (K : Type) [Field K] [Fintype K] [DecidableEq K] [Algebra F K]
    (q kroots Λ : ℕ) {N M : ℕ} (envsC : Fin N → Env F) (envsM : Fin M → Env F) (hM : 0 < M)
    (claim : P8PublicClaim) : Finset (JointCoins K) :=
  liftSeed (pairBadSeeds (K := K) (s3Window M Λ) (s3PairsOfEnvs K q kroots envsC envsM hM claim))

/-- **Card `≤ 3N · (2·s3Window M Λ − 1) · |𝕂|³` at every env tuple** (rule 8(b): no premise). -/
theorem s3PairEventOfEnvs_card_le (K : Type) [Field K] [Fintype K] [DecidableEq K] [Algebra F K]
    (q kroots Λ : ℕ) {N M : ℕ} (envsC : Fin N → Env F) (envsM : Fin M → Env F) (hM : 0 < M)
    (claim : P8PublicClaim) :
    (s3PairEventOfEnvs K q kroots Λ envsC envsM hM claim).card ≤
      3 * N * (2 * s3Window M Λ - 1) * Fintype.card K ^ 3 := by
  have hB := pairBadSeeds_card_le (K := K) (s3Window M Λ)
    (s3PairsOfEnvs K q kroots envsC envsM hM claim)
  have hL := s3PairsOfEnvs_length_le K q kroots envsC envsM hM claim
  rw [s3PairEventOfEnvs, card_liftSeed]
  exact Nat.mul_le_mul_right _ (hB.trans (Nat.mul_le_mul_right _ hL))

/-- **The S3 event on the production challenge tuple** (`liftP8Failure` of the `JointCoins` event,
the slot 2b-ii adds to `OptimizedHostileProductionFailureEvent`). -/
def s3PairEventOf (K : Type) [Field K] [Fintype K] [DecidableEq K] [Algebra F K]
    (q kroots Λ : ℕ) {N M : ℕ} (envsC : Fin N → Env F) (envsM : Fin M → Env F) (hM : 0 < M)
    (claim : P8PublicClaim) : Finset (OptimizedProductionChallengeTuple K F) :=
  liftP8Failure (F := F) (s3PairEventOfEnvs K q kroots Λ envsC envsM hM claim)

/-- **THE CARD LEMMA: `≤ |𝕂|¹⁰ · (3N · (2·s3Window M Λ − 1))` at EVERY `(envsC, envsM)`, every claim,
every `Λ`, with no premise** (rule 8(b)).  At the committed envs of any `(Qc, Qm)` this is the
bound 2b-ii's slot needs. -/
theorem s3PairEventOf_card_le (K : Type) [Field K] [Fintype K] [DecidableEq K] [Algebra F K]
    (q kroots Λ : ℕ) {N M : ℕ} (envsC : Fin N → Env F) (envsM : Fin M → Env F) (hM : 0 < M)
    (claim : P8PublicClaim) :
    (s3PairEventOf K q kroots Λ envsC envsM hM claim).card ≤
      Fintype.card K ^ 10 * (3 * N * (2 * s3Window M Λ - 1)) := by
  have hB := s3PairEventOfEnvs_card_le K q kroots Λ envsC envsM hM claim
  unfold s3PairEventOf liftP8Failure
  rw [Finset.card_product, Finset.card_univ]
  have hrest :
      Fintype.card ((K × K) × FinalComputeChallengeTuple K × MemoryChallengeTuple K) =
        Fintype.card K ^ 7 := by
    simp only [Fintype.card_prod, card_finalComputeChallengeTuple, card_memoryChallengeTuple]
    ring
  rw [hrest]
  calc _ ≤ 3 * N * (2 * s3Window M Λ - 1) * Fintype.card K ^ 3 * Fintype.card K ^ 7 :=
        Nat.mul_le_mul_right _ hB
    _ = Fintype.card K ^ 10 * (3 * N * (2 * s3Window M Λ - 1)) := by ring

end OfEnvs

/-- **The S3 workload at a strategy** — the numeral 2b-ii adds to `workload` (`s3Work`):
`3·N_T·(2·(M_T + max M_T Λ) − 1)` at the skeleton's compute / memory row counts.  The body is
written out (no `s3Window`), as `ProductionP8Containment.reqPairWorkload`'s is, so a watchlisted
fingerprint of this one name covers it. -/
def s3PairWorkload {F K : Type} [Field F] [Field K] [Algebra F K] [CharP K (ringChar K)]
    (T : ProductionP8Containment.ProductionStrategy F K) (Λ : ℕ) : ℕ :=
  3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length *
    (2 * ((SemanticStrategy.memorySkeletonRows T.skeleton).length +
      max (SemanticStrategy.memorySkeletonRows T.skeleton).length Λ) - 1)

theorem s3PairWorkload_eq {F K : Type} [Field F] [Field K] [Algebra F K] [CharP K (ringChar K)]
    (T : ProductionP8Containment.ProductionStrategy F K) (Λ : ℕ) :
    s3PairWorkload T Λ =
      3 * (SemanticStrategy.computeSkeletonRows T.skeleton).length *
        (2 * s3Window (SemanticStrategy.memorySkeletonRows T.skeleton).length Λ - 1) := rfl

/-! ## §5  The read set: round 0 -/

/-- The compute columns the S3 census reads: the selectors `1..10` and the carrier `S = 302`. -/
def s3CompCols : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 302]

/-- **Every compute column the census reads is B1 round `0`.** -/
theorem s3CompCols_round_zero : ∀ c ∈ s3CompCols, PreZComputeCore.compColRound c = 0 := by
  decide

section ReadSet

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem preCLabel_congr {e e' : Env F} (h : ∀ c ∈ s3CompCols, e.trace c = e'.trace c) :
    preCLabel e = preCLabel e' := by
  have h1 := h 1 (by simp [s3CompCols]); have h2 := h 2 (by simp [s3CompCols])
  have h3 := h 3 (by simp [s3CompCols]); have h4 := h 4 (by simp [s3CompCols])
  have h5 := h 5 (by simp [s3CompCols]); have h6 := h 6 (by simp [s3CompCols])
  have h7 := h 7 (by simp [s3CompCols]); have h8 := h 8 (by simp [s3CompCols])
  have h9 := h 9 (by simp [s3CompCols]); have h10 := h 10 (by simp [s3CompCols])
  have h302 := h 302 (by simp [s3CompCols])
  simp only [preCLabel, StrategyOfTracesLift.computeStateOf, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h302]

theorem builtTreeOfEnvs_congr {N : ℕ} {envs envs' : Fin N → Env F}
    (h : ∀ i, ∀ c ∈ s3CompCols, (envs i).trace c = (envs' i).trace c) :
    builtTreeOfEnvs envs = builtTreeOfEnvs envs' := by
  have hrows : preCRows envs = preCRows envs' := by
    unfold preCRows
    congr 1
    funext i
    exact preCLabel_congr (h i)
  unfold builtTreeOfEnvs
  rw [hrows]


theorem s3PairsOfEnvs_congr (K : Type) [Field K] [Algebra F K] (q kroots : ℕ) {N M : ℕ}
    {envsC envsC' : Fin N → Env F} {envsM envsM' : Fin M → Env F}
    (hC : ∀ i, ∀ c ∈ s3CompCols, (envsC i).trace c = (envsC' i).trace c)
    (hMem : ∀ i, ∀ c ∈ PreZComputeCore.Served.preZMemCols, (envsM i).trace c = (envsM' i).trace c)
    (hM : 0 < M) (claim : P8PublicClaim) :
    s3PairsOfEnvs K q kroots envsC envsM hM claim = s3PairsOfEnvs K q kroots envsC' envsM' hM claim := by
  unfold s3PairsOfEnvs
  rw [builtTreeOfEnvs_congr hC, PreZComputeCore.Served.servedNounOfEnvs_congr K q kroots hMem hM]

theorem s3PairEventOf_congr (K : Type) [Field K] [Fintype K] [DecidableEq K] [Algebra F K]
    (q kroots Λ : ℕ) {N M : ℕ}
    {envsC envsC' : Fin N → Env F} {envsM envsM' : Fin M → Env F}
    (hC : ∀ i, ∀ c ∈ s3CompCols, (envsC i).trace c = (envsC' i).trace c)
    (hMem : ∀ i, ∀ c ∈ PreZComputeCore.Served.preZMemCols, (envsM i).trace c = (envsM' i).trace c)
    (hM : 0 < M) (claim : P8PublicClaim) :
    s3PairEventOf K q kroots Λ envsC envsM hM claim =
      s3PairEventOf K q kroots Λ envsC' envsM' hM claim := by
  unfold s3PairEventOf s3PairEventOfEnvs
  rw [s3PairsOfEnvs_congr K q kroots hC hMem hM claim]

/-- **Round 0 at the committed compute trace**: at `envOfTrace` envs, the S3 event is the same for
every pair of compute column assignments that agree on the B1 round-`0` columns
(`PreZComputeCore.PreZAgreeOnC`). -/
theorem s3PairEventOf_preZ_compute (K : Type) [Field K] [Fintype K] [DecidableEq K] [Algebra F K]
    (q kroots Λ : ℕ) {w N M : ℕ} {Qc Qc' : Fin w → Polynomial F}
    (hag : PreZComputeCore.PreZAgreeOnC Qc Qc') (ω : F) (nodes : Fin N → F) (chal pub : ℕ → F)
    (envsM : Fin M → Env F) (hM : 0 < M) (claim : P8PublicClaim) :
    s3PairEventOf K q kroots Λ (fun i => envOfTrace Qc ω (nodes i) chal pub) envsM hM claim =
      s3PairEventOf K q kroots Λ (fun i => envOfTrace Qc' ω (nodes i) chal pub) envsM hM claim :=
  s3PairEventOf_congr K q kroots Λ
    (fun i c hc => PreZComputeCore.envOfTrace_trace_congr hag ω (nodes i) chal pub
      (s3CompCols_round_zero c hc))
    (fun _ _ _ => rfl) hM claim

end ReadSet

end

end Nock.NockVMROM.Thm54.S3PairEvent
