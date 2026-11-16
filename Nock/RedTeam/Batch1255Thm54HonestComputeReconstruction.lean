import Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderAirLinked
import Nock.NockVMROM.Thm54.ReconTreeSize
import Nock.RedTeam.Batch996Thm54HonestDecodedTreeBFS
import Nock.RedTeam.Batch1250Thm54HonestGoodGenerated
import Nock.RedTeam.Batch997Thm54HonestComputeCertDecode
import Nock.RedTeam.Batch958Thm54HonestComputeTiling
import Nock.RedTeam.Batch773Thm54ExpOfRequestList
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticDataParts
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMem
import Nock.NockVMROM.Thm54.PreZCensusCore
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace
import Nock.RedTeam.Batch959Thm54HonestMemoryTiling
import Nock.NockVMROM.Thm54.StrategyOfTracesR0
import Nock.NockVMROM.Thm54.TraceGen.BFSAssign
import Nock.RedTeam.Batch671Thm54ExponentCarrierHonestFill
import Nock.NockVMROM.Thm54.TraceGen.GenExponentLineNumbers
import Nock.NockVMROM.Thm54.TraceGen.GenRecordExponentBridge
import Nock.NockVMROM.Thm54.TraceGen.GenRequestTargets
import Nock.RedTeam.Batch1061Thm54RepairIIHonestAcceptance
import Nock.RedTeam.Batch1000Thm54HonestLambdaGenerated
import Nock.RedTeam.Batch1173Thm54C2CombinedServedRecords
import Nock.RedTeam.Batch489Thm54FoOfEqFoW
import Nock.RedTeam.Batch940Thm54LiftStrategyReceipts

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1255Thm54HonestComputeReconstruction.lean

* `Gen.builtComputeTree_genPkg` (binders of `Batch1250.hgood_genPkg_of_pair` minus `hpair`):
    `(builtSkeletonEv GP (honestQc …) (honestQm …)).computeTree = GP.strategy.skeleton.computeTree`.
    `Join.J_gen` (the C2 join over the generated tree returns the compiler's rows, given the OP0 / OP9
    served noun and axis), `Gen.treeOfTraces_eq` (the rebuilt S-carrying tree is the BFS-assigned
    generator tree), `Gen.sv_eq` (served lookup = skeleton request target; `Mem.AllLC`,
    `decode_of_LC`), `Gen.ax_row` (decoded cert axis = record axis), `Gen.served_W`.

  * **The MEMORY half of `hS` is NOT proved and is unconfirmed-false**: `decodeMemoryRowAx` fills
    `read_root.mem.child` / `verify_child.mem.root` by `nounByFP` (first BFS node with that
    fingerprint), and `hbad` prices compute-side pairs only. No counterexample at a
    generated program is compiled (§6: unconfirmed); nothing consumes the memory forest of the built
    skeleton in the Ev event.

  -- the paper
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option quotPrecheck false

namespace Nock.RedTeam.Batch1255.Join

open Nock Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.TraceGen

variable (sv : MState → ℕ → Noun) (ax : ℕ → ℕ)

theorem row_s1 (S : ℕ) (subj tail : Noun) :
    c2SkeletonRow sv ax .s1 S subj (.cell (.atom 1) tail) [] =
      genSkelOp1 subj (.cell (.atom 1) tail) tail (.atom 1) := by
  simp only [c2SkeletonRow, c2Evaluation, genSkelOp1, nounHead, nounTail]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t => rfl
    | .f_th | .f_tt | .f_tth | .f_ttt => simp [decActive, hasTailDecomposition] at hact
  · funext i hi slot
    simp [fanoutComp] at hi
  · funext i hi
    have : (i : ℕ) < 1 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · simp at this
    · simp at this

theorem row_s0 (S : ℕ) (subj tail result : Noun) (a : ℕ)
    (hsv : sv .verify_child (S + 2) = result) (hax : ax (S + 2) = a) :
    c2SkeletonRow sv ax .s0 S subj (.cell (.atom 0) tail) [] =
      genSkelOp0 subj (.cell (.atom 0) tail) (.atom 0) tail result a := by
  simp only [c2SkeletonRow, c2Evaluation, genSkelOp0, nounHead, nounTail, hsv, hax]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t => rfl
    | .f_th | .f_tt | .f_tth | .f_ttt => simp [decActive, hasTailDecomposition] at hact
  · funext i hi slot
    simp [fanoutComp] at hi
  · funext i hi
    have : (i : ℕ) < 2 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · rfl
    · simp at this

theorem row_cons (S : ℕ) (subj fh ft : Noun) (k0 k1 : ComputeRowSkeleton)
    (h0s : k0.subject = subj) (h0f : k0.formula = fh)
    (h1s : k1.subject = subj) (h1f : k1.formula = ft) :
    c2SkeletonRow sv ax .cons S subj (.cell fh ft) [k0, k1] =
      genSkelCons subj fh ft k0.evaluation k1.evaluation := by
  simp only [c2SkeletonRow, c2Evaluation, genSkelCons, kidSkel, nounHead, nounTail,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t => rfl
    | .f_th | .f_tt | .f_tth | .f_ttt => simp [decActive, hasTailDecomposition] at hact
  · funext i hi slot
    fin_cases i
    · simp [h0s, h0f]; cases slot <;> rfl
    · simp [h1s, h1f]; cases slot <;> rfl
    · simp [fanoutComp] at hi
  · funext i hi
    have : (i : ℕ) < 1 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · simp at this
    · simp at this

theorem row_s3 (S : ℕ) (subj tail : Noun) (k0 : ComputeRowSkeleton)
    (h0s : k0.subject = subj) (h0f : k0.formula = tail) :
    c2SkeletonRow sv ax .s3 S subj (.cell (.atom 3) tail) [k0] =
      genSkelOp3 subj (.cell (.atom 3) tail) (.atom 3) tail subj tail k0.evaluation
        (Noun.wut k0.evaluation) := by
  simp only [c2SkeletonRow, c2Evaluation, genSkelOp3, kidSkel, nounHead, nounTail,
    List.getElem?_cons_zero, Option.getD]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t => rfl
    | .f_th | .f_tt | .f_tth | .f_ttt => simp [decActive, hasTailDecomposition] at hact
  · funext i hi slot
    have : (i : ℕ) < 1 := by simpa [fanoutComp] using hi
    fin_cases i
    · simp [h0s, h0f]; cases slot <;> rfl
    · simp at this
    · simp at this
  · funext i hi
    have : (i : ℕ) < 1 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · simp at this
    · simp at this

theorem row_s4 (S : ℕ) (subj tail : Noun) (k0 : ComputeRowSkeleton) (k : ℕ)
    (h0s : k0.subject = subj) (h0f : k0.formula = tail) (h0e : k0.evaluation = .atom k) :
    c2SkeletonRow sv ax .s4 S subj (.cell (.atom 4) tail) [k0] =
      genSkelOp4 subj (.cell (.atom 4) tail) (.atom 4) tail subj tail (.atom k)
        (.atom (k + 1)) := by
  simp only [c2SkeletonRow, c2Evaluation, genSkelOp4, kidSkel, nounHead, nounTail,
    List.getElem?_cons_zero, Option.getD, h0e]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t => rfl
    | .f_th | .f_tt | .f_tth | .f_ttt => simp [decActive, hasTailDecomposition] at hact
  · funext i hi slot
    have : (i : ℕ) < 1 := by simpa [fanoutComp] using hi
    fin_cases i
    · simp [h0s, h0f, h0e]; cases slot <;> rfl
    · simp at this
    · simp at this
  · funext i hi
    have : (i : ℕ) < 1 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · simp at this
    · simp at this

theorem row_s5 (S : ℕ) (subj b c : Noun) (k0 k1 : ComputeRowSkeleton)
    (h0s : k0.subject = subj) (h0f : k0.formula = b)
    (h1s : k1.subject = subj) (h1f : k1.formula = c) :
    c2SkeletonRow sv ax .s5 S subj (.cell (.atom 5) (.cell b c)) [k0, k1] =
      genSkelOp5 subj (.cell (.atom 5) (.cell b c)) (.atom 5) (.cell b c) b c
        k0.evaluation k1.evaluation (Noun.tis k0.evaluation k1.evaluation) := by
  simp only [c2SkeletonRow, c2Evaluation, genSkelOp5, kidSkel, nounHead, nounTail,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t | .f_th | .f_tt => rfl
    | .f_tth | .f_ttt => simp [decActive, hasTailDecomposition] at hact
  · funext i hi slot
    fin_cases i
    · simp [h0s, h0f]; cases slot <;> rfl
    · simp [h1s, h1f]; cases slot <;> rfl
    · simp [fanoutComp] at hi
  · funext i hi
    have : (i : ℕ) < 2 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · rfl
    · simp at this

theorem row_s2 (S : ℕ) (subj b c : Noun) (k0 k1 k2 : ComputeRowSkeleton)
    (h0s : k0.subject = subj) (h0f : k0.formula = b)
    (h1s : k1.subject = subj) (h1f : k1.formula = c)
    (h2s : k2.subject = k0.evaluation) (h2f : k2.formula = k1.evaluation) :
    c2SkeletonRow sv ax .s2 S subj (.cell (.atom 2) (.cell b c)) [k0, k1, k2] =
      genSkelOp2 subj (.cell (.atom 2) (.cell b c)) (.atom 2) (.cell b c) b c
        k0.evaluation k1.evaluation k2.evaluation := by
  simp only [c2SkeletonRow, c2Evaluation, genSkelOp2, kidSkel, nounHead, nounTail,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t | .f_th | .f_tt => rfl
    | .f_tth | .f_ttt => simp [decActive, hasTailDecomposition] at hact
  · funext i hi slot
    fin_cases i
    · simp [h0s, h0f]; cases slot <;> rfl
    · simp [h1s, h1f]; cases slot <;> rfl
    · simp [h2s, h2f]; cases slot <;> rfl
  · funext i hi
    have : (i : ℕ) < 2 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · rfl
    · simp at this

theorem row_s7 (S : ℕ) (subj b c : Noun) (k0 k1 : ComputeRowSkeleton)
    (h0s : k0.subject = k1.evaluation) (h0f : k0.formula = c)
    (h1s : k1.subject = subj) (h1f : k1.formula = b) :
    c2SkeletonRow sv ax .s7 S subj (.cell (.atom 7) (.cell b c)) [k0, k1] =
      genSkelOp7 subj (.cell (.atom 7) (.cell b c)) (.atom 7) (.cell b c) b c
        k1.evaluation k0.evaluation := by
  simp only [c2SkeletonRow, c2Evaluation, genSkelOp7, kidSkel, nounHead, nounTail,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t | .f_th | .f_tt => rfl
    | .f_tth | .f_ttt => simp [decActive, hasTailDecomposition] at hact
  · funext i hi slot
    fin_cases i
    · simp [h0s, h0f]; cases slot <;> rfl
    · simp [h1s, h1f]; cases slot <;> rfl
    · simp [fanoutComp] at hi
  · funext i hi
    have : (i : ℕ) < 2 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · rfl
    · simp at this

theorem row_s8 (S : ℕ) (subj b c : Noun) (k0 k1 : ComputeRowSkeleton)
    (h0s : k0.subject = .cell k1.evaluation subj) (h0f : k0.formula = c)
    (h1s : k1.subject = subj) (h1f : k1.formula = b) :
    c2SkeletonRow sv ax .s8 S subj (.cell (.atom 8) (.cell b c)) [k0, k1] =
      genSkelOp8 subj (.cell (.atom 8) (.cell b c)) (.atom 8) (.cell b c) b c
        k1.evaluation k0.evaluation := by
  simp only [c2SkeletonRow, c2Evaluation, genSkelOp8, kidSkel, nounHead, nounTail,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t | .f_th | .f_tt => rfl
    | .f_tth | .f_ttt => simp [decActive, hasTailDecomposition] at hact
  · funext i hi slot
    fin_cases i
    · simp [h0s, h0f]; cases slot <;> rfl
    · simp [h1s, h1f]; cases slot <;> rfl
    · simp [fanoutComp] at hi
  · funext i hi
    have : (i : ℕ) < 2 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · rfl
    · simp at this

theorem row_s9 (S : ℕ) (subj c : Noun) (a : ℕ) (k0 k1 : ComputeRowSkeleton)
    (h0s : k0.subject = subj) (h0f : k0.formula = c)
    (h1s : k1.subject = k0.evaluation)
    (hax : ax (S + 3) = a) :
    c2SkeletonRow sv ax .s9 S subj (.cell (.atom 9) (.cell (.atom a) c)) [k0, k1] =
      genSkelOp9 subj (.cell (.atom 9) (.cell (.atom a) c)) (.atom 9) (.cell (.atom a) c)
        (.atom a) c k0.evaluation k1.formula k1.evaluation a := by
  simp only [c2SkeletonRow, c2Evaluation, genSkelOp9, kidSkel, nounHead, nounTail,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD, hax]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t | .f_th | .f_tt => rfl
    | .f_tth | .f_ttt => simp [decActive, hasTailDecomposition] at hact
  · funext i hi slot
    fin_cases i
    · simp [h0s, h0f]; cases slot <;> rfl
    · simp [h1s]; cases slot <;> rfl
    · simp [fanoutComp] at hi
  · funext i hi
    fin_cases i
    · rfl
    · rfl
    · rfl

theorem row_s6 (S : ℕ) (subj b c d cond : Noun) (k0 k1 : ComputeRowSkeleton)
    (h0s : k0.subject = subj)
    (h1s : k1.subject = subj) (h1f : k1.formula = b) (h1e : k1.evaluation = cond) :
    c2SkeletonRow sv ax .s6 S subj (.cell (.atom 6) (.cell b (.cell c d))) [k0, k1] =
      genSkelOp6 subj (.cell (.atom 6) (.cell b (.cell c d))) (.atom 6) (.cell b (.cell c d)) b
        (.cell c d) c d cond k0.formula k0.evaluation := by
  simp only [c2SkeletonRow, c2Evaluation, genSkelOp6, kidSkel, nounHead, nounTail,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t | .f_th | .f_tt | .f_tth | .f_ttt => rfl
  · funext i hi slot
    fin_cases i
    · simp [h0s]; cases slot <;> rfl
    · simp [h1s, h1f, h1e]; cases slot <;> rfl
    · simp [fanoutComp] at hi
  · funext i hi
    fin_cases i
    · rfl
    · rfl
    · rfl


/-! ## The join induction -/

variable {K : Type} [Field K]

/-- The served-record facts the join reads at an OP0 / OP9 node. -/
def Served (W : NTree (ComputeRowSkeleton × ℕ)) : Prop :=
  ∀ w, InTree W w →
    (∀ h : (1 : ℕ) < Nock.Framework.recordCount w.label.1.state, w.label.1.state = .s0 →
      sv .verify_child (w.label.2 + 2) = (w.label.1.memoryRecord ⟨1, by omega⟩ h).child ∧
      ax (w.label.2 + 2) = (w.label.1.memoryRecord ⟨1, by omega⟩ h).axis) ∧
    (∀ h : (2 : ℕ) < Nock.Framework.recordCount w.label.1.state, w.label.1.state = .s9 →
      sv .verify_child (w.label.2 + 3) = (w.label.1.memoryRecord ⟨2, by omega⟩ h).child ∧
      ax (w.label.2 + 3) = (w.label.1.memoryRecord ⟨2, by omega⟩ h).axis)

variable {sv ax}

theorem Served.child {W c : NTree (ComputeRowSkeleton × ℕ)} (h : Served sv ax W)
    (hc : c ∈ W.children) : Served sv ax c :=
  fun w hw => h w (InTree.sub hc hw)


theorem inv_node {α β : Type*} {W : NTree (α × β)} {a : α} {cs : List (NTree α)}
    (h : mapNTree Prod.fst W = .node a cs) :
    ∃ S ws, W = .node (a, S) ws ∧ ws.map (mapNTree Prod.fst) = cs := by
  obtain ⟨⟨a', S⟩, ws⟩ := W
  simp only [mapNTree, NTree.node.injEq] at h
  obtain ⟨rfl, hws⟩ := h
  exact ⟨S, ws, rfl, hws⟩

theorem kid_facts {fuel : ℕ} {s f : Noun} {p : NTree (GenComputeRow K) × Noun}
    (hp : genComputeSkeleton (K := K) fuel s f = .ok p) {w : NTree (ComputeRowSkeleton × ℕ)}
    (hw : mapNTree Prod.fst w = mapNTree GenComputeRow.skel (airReorder p.1)) :
    w.label.1.subject = s ∧ w.label.1.formula = f ∧ w.label.1.evaluation = p.2 := by
  have hl := congrArg NTree.label hw
  simp only [mapNTree_label, airReorder_label] at hl
  rw [hl]
  exact genComputeSkeleton_root_sfe_pair hp

local notation "J" => c2JoinFuel (fun l : ComputeRowSkeleton × ℕ => l.1.state)
  (fun l : ComputeRowSkeleton × ℕ => l.2) sv ax

theorem size_two {α : Type*} (a : α) (x y : NTree α) :
    (NTree.node a [x, y]).size = 1 + x.size + y.size := by
  simp [NTree.size]; omega

theorem size_one {α : Type*} (a : α) (x : NTree α) :
    (NTree.node a [x]).size = 1 + x.size := by
  simp [NTree.size]

theorem size_three {α : Type*} (a : α) (x y u : NTree α) :
    (NTree.node a [x, y, u]).size = 1 + x.size + y.size + u.size := by
  simp [NTree.size]; omega

theorem J_gen (fuel : ℕ) :
    ∀ {s f : Noun} {p : NTree (GenComputeRow K) × Noun},
      genComputeSkeleton (K := K) fuel s f = .ok p →
      ∀ (W : NTree (ComputeRowSkeleton × ℕ)),
        mapNTree Prod.fst W = mapNTree GenComputeRow.skel (airReorder p.1) →
        Served sv ax W → ∀ m, W.size ≤ m → J m W s f = mapNTree Prod.fst W := by
  induction fuel with
  | zero => intro s f p h; simp [genComputeSkeleton] at h
  | succ n ih =>
    intro subject formula p h W hW hS m hm
    cases formula with
    | atom _ => simp [genComputeSkeleton] at h
    | cell hd tl =>
      cases hd with
      | cell lh lt =>
        cases hL : genComputeSkeleton (K := K) n subject (.cell lh lt) with
        | error _ => simp [genComputeSkeleton, hL] at h
        | ok pL =>
          cases hR : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hL, hR] at h
          | ok pR =>
            simp [genComputeSkeleton, hL, hR] at h
            subst h
            rw [airReorder_no_swap_cons _ _ (airNeedsSwap_skelNode_false_cons _ _ _ _ _ _)] at hW
            simp only [mapNTree, List.map_cons, List.map_nil] at hW
            obtain ⟨S, ws, rfl, hws⟩ := inv_node hW
            rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, ws⟩⟩⟩ <;> simp at hws
            obtain ⟨h0, h1⟩ := hws
            rw [size_two] at hm
            obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
            have e0 := ih hL w0 h0 (hS.child (by simp)) m (by omega)
            have e1 := ih hR w1 h1 (hS.child (by simp)) m (by omega)
            have k0 := kid_facts hL h0
            have k1 := kid_facts hR h1
            simp only [c2JoinFuel, c2JoinKids, skelNode, genSkelCons, nounHead, nounTail]
            rw [e0, e1]
            simp only [mapNTree, List.map_cons, List.map_nil, mapNTree_label]
            congr 1
            rw [row_cons sv ax S subject (.cell lh lt) tl _ _ k0.1 k0.2.1 k1.1 k1.2.1, k0.2.2, k1.2.2]
            rfl
      | atom op =>
        rcases nat_lt_twelve_or_ge op with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hge
        · -- OP0
          cases tl with
          | cell _ _ => simp [genComputeSkeleton] at h
          | atom a =>
            cases hslot : Noun.slot a subject with
            | none => simp [genComputeSkeleton, hslot] at h
            | some res =>
              simp [genComputeSkeleton, hslot] at h
              subst h
              rw [airReorder_leaf] at hW
              simp only [mapNTree, List.map_nil] at hW
              obtain ⟨S, ws, rfl, hws⟩ := inv_node hW
              rcases ws with _ | ⟨w0, ws⟩ <;> simp at hws
              have hroot := (hS _ (InTree.here _)).1 (show (1:ℕ) < Nock.Framework.recordCount State.s0 by decide) rfl
              simp only [skelNode, genSkelOp0] at hroot
              obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp [NTree.size] at hm; omega⟩
              simp only [c2JoinFuel, c2JoinKids, skelNode, genSkelOp0, mapNTree, List.map_nil]
              congr 1
              rw [row_s0 sv ax S subject (.atom a) res a hroot.1 hroot.2]
              rfl
        · -- OP1
          simp [genComputeSkeleton] at h
          subst h
          rw [airReorder_leaf] at hW
          simp only [mapNTree, List.map_nil] at hW
          obtain ⟨S, ws, rfl, hws⟩ := inv_node hW
          rcases ws with _ | ⟨w0, ws⟩ <;> simp at hws
          obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp [NTree.size] at hm; omega⟩
          simp only [c2JoinFuel, c2JoinKids, skelNode, genSkelOp1, mapNTree, List.map_nil]
          congr 1
          rw [row_s1 sv ax S subject tl]
          rfl
        · -- OP2
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                cases hM : genComputeSkeleton (K := K) n pB.2 pC.2 with
                | error _ => simp [genComputeSkeleton, hB, hC, hM] at h
                | ok pM =>
                  simp [genComputeSkeleton, hB, hC, hM] at h
                  subst h
                  rw [airReorder_no_swap_cons _ _ (airNeedsSwap_skelNode_op2 _ _ _ _ _ _ _ _ _ _)] at hW
                  simp only [mapNTree, List.map_cons, List.map_nil] at hW
                  obtain ⟨S, ws, rfl, hws⟩ := inv_node hW
                  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, ws⟩⟩⟩⟩ <;> simp at hws
                  obtain ⟨h0, h1, h2⟩ := hws
                  rw [size_three] at hm
                  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
                  have e0 := ih hB w0 h0 (hS.child (by simp)) m (by omega)
                  have e1 := ih hC w1 h1 (hS.child (by simp)) m (by omega)
                  have e2 := ih hM w2 h2 (hS.child (by simp)) m (by omega)
                  have k0 := kid_facts hB h0
                  have k1 := kid_facts hC h1
                  have k2 := kid_facts hM h2
                  simp only [c2JoinFuel, c2JoinKids, skelNode, genSkelOp2, nounHead, nounTail]
                  rw [e0, e1]
                  simp only [mapNTree_label]
                  rw [k0.2.2, k1.2.2, e2]
                  simp only [mapNTree, List.map_cons, List.map_nil, mapNTree_label]
                  congr 1
                  rw [row_s2 sv ax S subject b c _ _ _ k0.1 k0.2.1 k1.1 k1.2.1
                    (k2.1.trans k0.2.2.symm) (k2.2.1.trans k1.2.2.symm), k0.2.2, k1.2.2, k2.2.2]
                  rfl
        · -- OP3
          cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok pCall =>
            simp [genComputeSkeleton, hcall] at h
            subst h
            rw [airReorder_no_swap_cons _ _ (airNeedsSwap_skelNode_false_op3 _ _ _ _ _ _ _ _ _)] at hW
            simp only [mapNTree, List.map_cons, List.map_nil] at hW
            obtain ⟨S, ws, rfl, hws⟩ := inv_node hW
            rcases ws with _ | ⟨w0, _ | ⟨w1, ws⟩⟩ <;> simp at hws
            rw [size_one] at hm
            obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
            have e0 := ih hcall w0 hws (hS.child (by simp)) m (by omega)
            have k0 := kid_facts hcall hws
            simp only [c2JoinFuel, c2JoinKids, skelNode, genSkelOp3, nounHead, nounTail]
            rw [e0]
            simp only [mapNTree, List.map_cons, List.map_nil, mapNTree_label]
            congr 1
            rw [row_s3 sv ax S subject tl _ k0.1 k0.2.1, k0.2.2]
            rfl
        · -- OP4
          cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok pCall =>
            cases hlus : Noun.lus pCall.2 with
            | none => simp [genComputeSkeleton, hcall, hlus] at h
            | some res =>
              have hk : ∃ k, pCall.2 = .atom k ∧ res = .atom (k + 1) := by
                cases hv : pCall.2 with
                | atom k => rw [hv] at hlus; simp [Noun.lus] at hlus; exact ⟨k, rfl, hlus.symm⟩
                | cell _ _ => rw [hv] at hlus; simp [Noun.lus] at hlus
              obtain ⟨k, hk1, hk2⟩ := hk
              simp [genComputeSkeleton, hcall, hlus] at h
              subst h
              rw [airReorder_no_swap_cons _ _ (airNeedsSwap_skelNode_false_op4 _ _ _ _ _ _ _ _ _)] at hW
              simp only [mapNTree, List.map_cons, List.map_nil] at hW
              obtain ⟨S, ws, rfl, hws⟩ := inv_node hW
              rcases ws with _ | ⟨w0, _ | ⟨w1, ws⟩⟩ <;> simp at hws
              rw [size_one] at hm
              obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              have e0 := ih hcall w0 hws (hS.child (by simp)) m (by omega)
              have k0 := kid_facts hcall hws
              simp only [c2JoinFuel, c2JoinKids, skelNode, genSkelOp4, nounHead, nounTail]
              rw [e0]
              simp only [mapNTree, List.map_cons, List.map_nil, mapNTree_label]
              congr 1
              rw [row_s4 sv ax S subject tl _ k k0.1 k0.2.1 (k0.2.2.trans hk1), hk1, hk2]
              rfl
        · -- OP5
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                subst h
                rw [airReorder_no_swap_cons _ _ (airNeedsSwap_skelNode_false_op5 _ _ _ _ _ _ _ _ _ _)] at hW
                simp only [mapNTree, List.map_cons, List.map_nil] at hW
                obtain ⟨S, ws, rfl, hws⟩ := inv_node hW
                rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, ws⟩⟩⟩ <;> simp at hws
                obtain ⟨h0, h1⟩ := hws
                rw [size_two] at hm
                obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
                have e0 := ih hB w0 h0 (hS.child (by simp)) m (by omega)
                have e1 := ih hC w1 h1 (hS.child (by simp)) m (by omega)
                have k0 := kid_facts hB h0
                have k1 := kid_facts hC h1
                simp only [c2JoinFuel, c2JoinKids, skelNode, genSkelOp5, nounHead, nounTail]
                rw [e0, e1]
                simp only [mapNTree, List.map_cons, List.map_nil, mapNTree_label]
                congr 1
                rw [row_s5 sv ax S subject b c _ _ k0.1 k0.2.1 k1.1 k1.2.1, k0.2.2, k1.2.2]
                rfl
        · -- OP6
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b rest =>
            cases rest with
            | atom _ => simp [genComputeSkeleton] at h
            | cell c d =>
              cases hcond : genComputeSkeleton (K := K) n subject b with
              | error _ => simp [genComputeSkeleton, hcond] at h
              | ok pCond =>
                cases hval : pCond.2 with
                | cell _ _ => simp [genComputeSkeleton, hcond, hval] at h
                | atom condv =>
                  have hbr : ∀ (cv : ℕ) (tk : Noun), (cv = 0 ∧ tk = c) ∨ (cv = 1 ∧ tk = d) →
                      condv = cv →
                      ∀ pT : NTree (GenComputeRow K) × Noun,
                      genComputeSkeleton (K := K) n subject tk = .ok pT →
                      p = (.node (skelNode (genSkelOp6 subject
                        (.cell (.atom 6) (.cell b (.cell c d))) (.atom 6) (.cell b (.cell c d)) b
                        (.cell c d) c d (.atom cv) tk pT.2)
                        [⟨.cell (.atom 6) (.cell b (.cell c d)), .cell b (.cell c d), 3, 0⟩,
                         ⟨.cell b (.cell c d), b, 2, 0⟩, ⟨.cell c d, c, 2, 0⟩]) [pCond.1, pT.1], pT.2) →
                      J m W subject (.cell (.atom 6) (.cell b (.cell c d))) = mapNTree Prod.fst W := by
                    intro cv tk hcvtk hcv pT hT hp
                    subst hp
                    rw [airReorder_swap_cons _ _ (airNeedsSwap_skelNode_op6 _ _ _ _ _ _ _ _ _ _ _ _)] at hW
                    simp only [mapNTree, List.map_cons, List.map_nil, swapPair] at hW
                    obtain ⟨S, ws, rfl, hws⟩ := inv_node hW
                    rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, ws⟩⟩⟩ <;> simp at hws
                    obtain ⟨h0, h1⟩ := hws
                    rw [size_two] at hm
                    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
                    have e1 := ih hcond w1 h1 (hS.child (by simp)) m (by omega)
                    have e0 := ih hT w0 h0 (hS.child (by simp)) m (by omega)
                    have k0 := kid_facts hT h0
                    have k1 := kid_facts hcond h1
                    simp only [hval, hcv] at k1
                    simp only [c2JoinFuel, c2JoinKids, skelNode, genSkelOp6, nounHead, nounTail]
                    simp only [e1]
                    simp only [mapNTree_label, k1.2.2]
                    have htk : (if cv = 0 then c else d) = tk := by
                      rcases hcvtk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
                    simp only [htk]
                    rw [e0]
                    simp only [mapNTree, List.map_cons, List.map_nil, mapNTree_label]
                    congr 1
                    rw [row_s6 sv ax S subject b c d (.atom cv) _ _ k0.1 k1.1 k1.2.1 k1.2.2,
                      k0.2.1, k0.2.2]
                    rfl
                  cases condv with
                  | zero =>
                    cases htaken : genComputeSkeleton (K := K) n subject c with
                    | error _ => simp [genComputeSkeleton, hcond, hval, htaken] at h
                    | ok pTaken =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                      exact hbr 0 c (Or.inl ⟨rfl, rfl⟩) rfl pTaken htaken (by rw [← h])
                  | succ condv =>
                    cases condv with
                    | zero =>
                      cases htaken : genComputeSkeleton (K := K) n subject d with
                      | error _ => simp [genComputeSkeleton, hcond, hval, htaken] at h
                      | ok pTaken =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                        exact hbr 1 d (Or.inr ⟨rfl, rfl⟩) rfl pTaken htaken (by rw [← h])
                    | succ _ =>
                      simp [genComputeSkeleton, hcond, hval] at h
        · -- OP7
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n pB.2 c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                subst h
                rw [airReorder_swap_cons _ _ (airNeedsSwap_skelNode_op7 _ _ _ _ _ _ _ _ _)] at hW
                simp only [mapNTree, List.map_cons, List.map_nil, swapPair] at hW
                obtain ⟨S, ws, rfl, hws⟩ := inv_node hW
                rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, ws⟩⟩⟩ <;> simp at hws
                obtain ⟨h0, h1⟩ := hws
                rw [size_two] at hm
                obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
                have e1 := ih hB w1 h1 (hS.child (by simp)) m (by omega)
                have e0 := ih hC w0 h0 (hS.child (by simp)) m (by omega)
                have k0 := kid_facts hC h0
                have k1 := kid_facts hB h1
                simp only [c2JoinFuel, c2JoinKids, skelNode, genSkelOp7, nounHead, nounTail]
                rw [e1]
                simp only [mapNTree_label, k1.2.2]
                rw [e0]
                simp only [mapNTree, List.map_cons, List.map_nil, mapNTree_label]
                congr 1
                rw [row_s7 sv ax S subject b c _ _ (k0.1.trans k1.2.2.symm) k0.2.1 k1.1 k1.2.1,
                  k0.2.2, k1.2.2]
                rfl
        · -- OP8
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n (.cell pB.2 subject) c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                subst h
                rw [airReorder_swap_cons _ _ (airNeedsSwap_skelNode_op8 _ _ _ _ _ _ _ _ _)] at hW
                simp only [mapNTree, List.map_cons, List.map_nil, swapPair] at hW
                obtain ⟨S, ws, rfl, hws⟩ := inv_node hW
                rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, ws⟩⟩⟩ <;> simp at hws
                obtain ⟨h0, h1⟩ := hws
                rw [size_two] at hm
                obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
                have e1 := ih hB w1 h1 (hS.child (by simp)) m (by omega)
                have e0 := ih hC w0 h0 (hS.child (by simp)) m (by omega)
                have k0 := kid_facts hC h0
                have k1 := kid_facts hB h1
                simp only [c2JoinFuel, c2JoinKids, skelNode, genSkelOp8, nounHead, nounTail]
                rw [e1]
                simp only [mapNTree_label, k1.2.2]
                rw [e0]
                simp only [mapNTree, List.map_cons, List.map_nil, mapNTree_label]
                congr 1
                rw [row_s8 sv ax S subject b c _ _ (by rw [k0.1, k1.2.2]) k0.2.1 k1.1 k1.2.1,
                  k0.2.2, k1.2.2]
                rfl
        · -- OP9
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell axN c =>
            cases axN with
            | cell _ _ => simp [genComputeSkeleton] at h
            | atom a =>
              cases hcore : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hcore] at h
              | ok pCore =>
                cases hslot : Noun.slot a pCore.2 with
                | none => simp [genComputeSkeleton, hcore, hslot] at h
                | some arm =>
                  cases hinv : genComputeSkeleton (K := K) n pCore.2 arm with
                  | error _ => simp [genComputeSkeleton, hcore, hslot, hinv] at h
                  | ok pInv =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                    subst h
                    rw [airReorder_no_swap_cons _ _
                      (airNeedsSwap_skelNode_false_op9 _ _ _ _ _ _ _ _ _ _ _)] at hW
                    simp only [mapNTree, List.map_cons, List.map_nil] at hW
                    obtain ⟨S, ws, rfl, hws⟩ := inv_node hW
                    rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, ws⟩⟩⟩ <;> simp at hws
                    obtain ⟨h0, h1⟩ := hws
                    rw [size_two] at hm
                    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
                    have hroot := (hS _ (InTree.here _)).2 (show (2:ℕ) < Nock.Framework.recordCount State.s9 by decide) rfl
                    simp [skelNode, genSkelOp9, NTree.label] at hroot
                    have e0 := ih hcore w0 h0 (hS.child (by simp)) m (by omega)
                    have e1 := ih hinv w1 h1 (hS.child (by simp)) m (by omega)
                    have k0 := kid_facts hcore h0
                    have k1 := kid_facts hinv h1
                    simp only [c2JoinFuel, c2JoinKids, skelNode, genSkelOp9, nounHead, nounTail]
                    rw [e0]
                    simp only [mapNTree_label, k0.2.2]
                    rw [hroot.1, e1]
                    simp only [mapNTree, List.map_cons, List.map_nil, mapNTree_label]
                    congr 1
                    rw [row_s9 sv ax S subject c a _ _ k0.1 k0.2.1 (k1.1.trans k0.2.2.symm) hroot.2,
                      k0.2.2, k1.2.1, k1.2.2]
                    rfl
        · simp [genComputeSkeleton] at h
        · simp [genComputeSkeleton] at h
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
          simp only [genComputeSkeleton] at h
          split at h <;> first | omega | contradiction

end Nock.RedTeam.Batch1255.Join



set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch1255.Tree

open Nock Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2

theorem buildT_congr {α : Type*} (fo fo' : ℕ → ℕ) (lbl lbl' : ℕ → α) (h : ℕ)
    (hfo : ∀ j, 1 ≤ j → j ≤ h → fo j = fo' j) (hlbl : ∀ j, 1 ≤ j → j ≤ h → lbl j = lbl' j) :
    ∀ i, 1 ≤ i → i ≤ h → buildT fo lbl h i = buildT fo' lbl' h i := by
  intro i
  induction hd : h - i using Nat.strong_induction_on generalizing i with
  | _ d ih =>
    intro hi1 hih
    rw [buildT, buildT]
    have hci : childIdxs fo h i = childIdxs fo' h i := by
      unfold childIdxs firstC
      rw [Nock.RedTeam.Batch996.Sf_congr (fo := fo) (fo' := fo') (k := i - 1)
        (fun j hj1 hj2 => hfo j hj1 (by omega)), hfo i hi1 hih]
    rw [hlbl i hi1 hih]
    congr 1
    have key : ∀ (l : List ℕ) (hl : ∀ j ∈ l, i < j ∧ j ≤ h),
        l.attach.map (fun j => buildT fo lbl h j.1) = l.attach.map (fun j => buildT fo' lbl' h j.1) := by
      intro l hl
      apply List.map_congr_left
      intro j _
      exact ih (h - j.1) (by have := hl j.1 j.2; omega) j.1 rfl (by have := hl j.1 j.2; omega)
        (hl j.1 j.2).2
    have hmem : ∀ j ∈ childIdxs fo h i, i < j ∧ j ≤ h := by
      intro j hj
      simp only [childIdxs, List.mem_filter, decide_eq_true_eq] at hj
      exact hj.2
    have e1 := key (childIdxs fo h i) hmem
    rw [List.attach_map_val (f := fun j => buildT fo lbl h j)] at e1
    rw [List.attach_map_val (f := fun j => buildT fo' lbl' h j)] at e1
    rw [List.attach_map_val (f := fun j => buildT fo lbl h j),
      List.attach_map_val (f := fun j => buildT fo' lbl' h j), ← hci]
    exact e1

theorem buildT_eq_buildTF_one {α : Type*} (fo : ℕ → ℕ) (lbl : ℕ → α) (h : ℕ) :
    ∀ i, buildT fo lbl h i = buildTF 1 fo lbl h i := by
  intro i
  induction hd : h - i using Nat.strong_induction_on generalizing i with
  | _ d ih =>
    rw [buildT, buildTF]
    have hci : childIdxs fo h i = childIdxsF 1 fo h i := by
      unfold childIdxs childIdxsF firstC firstCF
      rfl
    congr 1
    rw [List.attach_map_val (f := fun j => buildT fo lbl h j),
      List.attach_map_val (f := fun j => buildTF 1 fo lbl h j), hci]
    apply List.map_congr_left
    intro j hj
    have : i < j ∧ j ≤ h := by
      simp only [childIdxsF, List.mem_filter, decide_eq_true_eq] at hj
      exact hj.2
    exact ih (h - j) (by omega) j rfl

/-- The BFS round trip of a single tree. -/
theorem buildT_bfs {α : Type*} (t : NTree α) (fb : α) :
    buildT (foCol (bfsForest [t])) (fun i => ((bfsForest [t])[i - 1]?).map NTree.label |>.getD fb)
      (bfsForest [t]).length 1 = t := by
  rw [buildT_eq_buildTF_one]
  have h := exact_reconForest_bfsForest [t] (by simp) fb
  have h1 : reconForest 1 (foCol (bfsForest [t]))
      (fun i => ((bfsForest [t])[i - 1]?).map NTree.label |>.getD fb) (bfsForest [t]).length =
      [buildTF 1 (foCol (bfsForest [t]))
        (fun i => ((bfsForest [t])[i - 1]?).map NTree.label |>.getD fb) (bfsForest [t]).length 1] := by
    simp [reconForest, List.range'_succ, List.range'_zero]
  simp only [List.length_singleton] at h
  rw [h1] at h
  simpa using h

/-- **The C2 join reads its labels only through `(state, S)`.** -/
theorem c2JoinFuel_canon {β : Type} (st : β → State) (Sof : β → ℕ)
    (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) :
    ∀ (n : ℕ) (X : NTree β) (s f : Noun),
      c2JoinFuel st Sof sv ax n X s f =
        c2JoinFuel Prod.fst Prod.snd sv ax n (mapNTree (fun l => (st l, Sof l)) X) s f := by
  intro n
  induction n with
  | zero =>
    intro X s f
    obtain ⟨x, xs⟩ := X
    simp only [c2JoinFuel, mapNTree]
  | succ n ih =>
    intro X s f
    obtain ⟨x, xs⟩ := X
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, xs⟩⟩⟩⟩ <;>
    cases hs : st x <;>
    simp [c2JoinFuel, mapNTree, hs, ih, List.map_map, Function.comp_def]

theorem c2JoinFuel_relabel {β γ : Type} (st : β → State) (Sof : β → ℕ) (st' : γ → State)
    (Sof' : γ → ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (n : ℕ) (X : NTree β) (Y : NTree γ)
    (hXY : mapNTree (fun l => (st l, Sof l)) X = mapNTree (fun l => (st' l, Sof' l)) Y)
    (s f : Noun) :
    c2JoinFuel st Sof sv ax n X s f = c2JoinFuel st' Sof' sv ax n Y s f := by
  rw [c2JoinFuel_canon, c2JoinFuel_canon st', hXY]

end Nock.RedTeam.Batch1255.Tree



set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch1255.Comp

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The decoded state at the canonical trace is the exec row's (any tuple). -/
theorem lblC_state_canon (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    (StrategyOfTracesLift.lblC P.optimized (canonicalComputeTrace P) c (i.val + 1)).1 =
      (P.optimized.family.problem.exec.computePubAt i).state := by
  unfold StrategyOfTracesLift.lblC
  rw [dif_pos (by omega)]
  have hi : (⟨i.val + 1 - 1, by omega⟩ : Fin P.optimized.family.problem.cfg.compRows) = i :=
    Fin.ext (by simp)
  rw [hi]
  show StrategyOfTraces.computeStateOf (DeployedComputeRows.decodeSource _) = _
  rw [Nock.RedTeam.Batch773.computeStateOf_decodeSource]
  rw [← Nock.RedTeam.Batch958.src_rowState_honest P i, Nock.RedTeam.Batch465.rowStateOf_eq_computeStateOf]
  rfl

/-- The canonical carrier column is the honest prefix `S(i)`. -/
theorem c2SAt_canon (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.compRows)
    (hS : OptimizedComputeFinalTrace.honestS P.optimized.family i < ringChar K) :
    c2SAt P.optimized (canonicalComputeTrace P) c i =
      OptimizedComputeFinalTrace.honestS P.optimized.family i := by
  unfold c2SAt
  have h : (StrategyOfTracesR0.computeEnvsR0 P.optimized (canonicalComputeTrace P) c i).trace 302 =
      ((OptimizedComputeFinalTrace.honestS P.optimized.family i : ℕ) : K) := by
    have e1 : (StrategyOfTracesR0.computeEnvsR0 P.optimized (canonicalComputeTrace P) c i).trace =
        (P.computeSourceEnv (canonicalComputeTrace P) i).trace := rfl
    rw [e1, show P.computeSourceEnv (canonicalComputeTrace P) i =
      (OptimizedCanonicalHostileLists.honestRow P i).toSourceEnv from rfl]
    show (CorrectedFinalTypedEnv.toSourceEnv _).trace 302 = _
    simp only [CorrectedFinalTypedEnv.toSourceEnv]
    simp only [show ¬ (302 < 13) by omega, show ¬ (302 < 76) by omega,
      show ¬ (202 ≤ 302 ∧ 302 < 296) by omega, dite_false, if_false,
      show ¬ ((302:ℕ) = 296) by omega, show ¬ ((302:ℕ) = 299) by omega, if_true]
    have := OptimizedComputeCanonicalSatisfaction.canonical_gather_expCol P.optimized.sampled
      P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
      P.optimized.computeNodes_injective P.optimized.basis
      P.optimized.computeChallenge P.optimized.computePublic P.optimized.orbit i
    rw [show (OptimizedCanonicalHostileLists.honestRow P i).expCol = _ from this]
    simp
  rw [h]
  exact RecordCarrier.natLift_natCast hS

end
end Nock.RedTeam.Batch1255.Comp



set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch1255.Mem

open Nock Nock.Walk Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TraceGen

variable {K : Type} [Field K]
variable {lmb : K}

abbrev PL (K : Type) := MemoryRowSkeleton × MState × MState × ComputeTable.FP K

/-- The decoder-visible projection of a generated memory row. -/
def proj (g : GenMemoryRow K) : PL K := (g.skel, g.row.1, g.row.2.2.st, g.row.2.2.pt.noun)

/-- The local structural shape at a node, per skeleton state. -/
def LCs (E : Noun → ComputeTable.FP K) : MState → NTree (PL K) → Prop
  | .halt, v => v.children = [] ∧ ∃ a, v.label.1.parent = .atom a ∧ v.label.2.2.2 = E (.atom a)
  | .decompose, v => ∃ x y, v.children = [x, y] ∧
      v.label.1.parent = .cell x.label.1.parent y.label.1.parent
  | _, v => ∃ x, v.children = [x] ∧ v.label.1.parent = x.label.1.parent

def LCn (E : Noun → ComputeTable.FP K) (v : NTree (PL K)) : Prop :=
  v.label.2.1 = v.label.1.state ∧ v.label.2.2.1 = v.label.1.state ∧ LCs E v.label.1.state v

def AllLC (E : Noun → ComputeTable.FP K) (u : NTree (PL K)) : Prop := ∀ v, InTree u v → LCn E v

theorem AllLC.mk {E : Noun → ComputeTable.FP K} {a : PL K} {cs : List (NTree (PL K))}
    (h : LCn E (.node a cs)) (hc : ∀ c ∈ cs, AllLC E c) : AllLC E (.node a cs) := by
  intro v hv
  cases hv with
  | here => exact h
  | sub hs h' => exact hc _ (by simpa using hs) v h'

theorem walk_LC (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, AllLC E (mapNTree proj (genAnnotatedNounWalk E z lmb n).1) ∧
      (genAnnotatedNounWalk E z lmb n).1.label.skel.parent = n
  | .atom a => by
      refine ⟨?_, rfl⟩
      simp only [genAnnotatedNounWalk, mapNTree, List.map_nil]
      refine AllLC.mk ?_ (by simp)
      refine ⟨rfl, rfl, ?_⟩
      exact ⟨rfl, a, rfl, rfl⟩
  | .cell h t => by
      refine ⟨?_, rfl⟩
      have ih1 := walk_LC E z h
      have ih2 := walk_LC E z t
      simp only [genAnnotatedNounWalk, mapNTree, List.map_cons, List.map_nil]
      refine AllLC.mk ?_ ?_
      · refine ⟨rfl, rfl, ?_⟩
        refine ⟨_, _, rfl, ?_⟩
        simp only [mapNTree_label]
        simp [proj, gMemRow9, memDecomposeSkel, ih1.2, ih2.2]
      · intro c hc
        simp at hc
        rcases hc with rfl | rfl
        · exact ih1.1
        · exact ih2.1

theorem verify_LC (E : Noun → ComputeTable.FP K) (z : K) (root child : Noun) (ax : ℕ) (ts : K)
    (e : ℕ) :
    AllLC E (mapNTree proj (genAnnotatedVerify E z lmb root child ax ts e).1) ∧
      (genAnnotatedVerify E z lmb root child ax ts e).1.label.skel.parent = child := by
  refine ⟨?_, rfl⟩
  have ih := walk_LC (lmb := lmb) E z child
  simp only [genAnnotatedVerify, mapNTree, List.map_cons, List.map_nil]
  refine AllLC.mk ?_ ?_
  · refine ⟨rfl, rfl, ?_⟩
    refine ⟨_, rfl, ?_⟩
    simp only [mapNTree_label]
    simp [proj, gMemRow9, memVerifySkelAx, ih.2]
  · intro c hc
    simp at hc
    subst hc
    exact ih.1

theorem cell_of_slot {a : ℕ} {n x : Noun} (h2 : 2 ≤ a) (h : Noun.slot a n = some x) :
    ∃ hd tl, n = .cell hd tl := by
  cases n with
  | atom k => rw [slot_atom_of_ge_two h2] at h; simp at h
  | cell hd tl => exact ⟨hd, tl, rfl⟩

theorem descent_LC (E : Noun → ComputeTable.FP K) (z : K) (root child : Noun) (recAxis : ℕ)
    (ts : K) (e : ℕ) :
    ∀ remaining current, 1 ≤ remaining → Noun.slot remaining current = some child →
      ∀ u ∈ (genAnnotatedDescent E z lmb root child recAxis ts e current remaining).1,
        AllLC E (mapNTree proj u) ∧ u.label.skel.parent = current := by
  intro remaining
  induction remaining using Nat.strongRecOn with
  | _ n ih =>
    intro current h1 hslot u hu
    have hdesc := hu
    unfold genAnnotatedDescent at hdesc
    split at hdesc
    · rename_i hlt
      have hn : n = 1 := by omega
      subst hn
      simp [Noun.slot] at hslot
      subst hslot
      simp at hdesc
      subst hdesc
      exact verify_LC E z root current recAxis ts e
    · rename_i hge
      have h2 : 2 ≤ n := by omega
      obtain ⟨hd, tl, rfl⟩ := cell_of_slot h2 hslot
      rw [slot_eq_msb hd tl h2] at hslot
      have hr1 : 1 ≤ axisRest n := axisRest_pos h2
      split at hdesc
      · rename_i ht
        simp only [ht, if_true] at hslot
        simp at hdesc
        subst hdesc
        have hlen := genAnnotatedDescent_length (lmb := lmb) E z root child recAxis ts e
          (formulaTail (.cell hd tl)) (axisRest n)
        have ihd := ih (axisRest n) (axisRest_lt h2) tl hr1 hslot
        have hw := walk_LC (lmb := lmb) E z hd
        obtain ⟨w, hw1⟩ : ∃ w, (genAnnotatedDescent E z lmb root child recAxis ts e
            (formulaTail (.cell hd tl)) (axisRest n)).1 = [w] := by
          rcases hh : (genAnnotatedDescent E z lmb root child recAxis ts e
            (formulaTail (.cell hd tl)) (axisRest n)).1 with _ | ⟨w, _ | ⟨w', ws⟩⟩
          · rw [hh] at hlen; simp at hlen
          · exact ⟨w, rfl⟩
          · rw [hh] at hlen; simp at hlen
        have hwd := ihd w (by simp [formulaTail] at hw1 ⊢; rw [hw1]; simp)
        simp only [formulaTail] at hw1
        simp only [formulaHead, formulaTail, hw1]
        refine ⟨?_, rfl⟩
        simp only [mapNTree, List.cons_append, List.nil_append, List.map_cons, List.map_nil]
        refine AllLC.mk ?_ ?_
        · refine ⟨rfl, rfl, ?_⟩
          refine ⟨_, _, rfl, ?_⟩
          simp only [mapNTree_label]
          simp [proj, gMemRow9, memDecomposeSkel, hw.2, hwd.2]
        · intro c hc
          simp at hc
          rcases hc with rfl | rfl
          · exact hw.1
          · exact hwd.1
      · rename_i ht
        have ht' : axisTopBit n = false := Bool.eq_false_iff.mpr ht
        simp only [ht', Bool.false_eq_true, if_false] at hslot
        simp at hdesc
        subst hdesc
        have hlen := genAnnotatedDescent_length (lmb := lmb) E z root child recAxis ts e
          (formulaHead (.cell hd tl)) (axisRest n)
        have ihd := ih (axisRest n) (axisRest_lt h2) hd hr1 hslot
        have hw := walk_LC (lmb := lmb) E z tl
        obtain ⟨w, hw1⟩ : ∃ w, (genAnnotatedDescent E z lmb root child recAxis ts e
            (formulaHead (.cell hd tl)) (axisRest n)).1 = [w] := by
          rcases hh : (genAnnotatedDescent E z lmb root child recAxis ts e
            (formulaHead (.cell hd tl)) (axisRest n)).1 with _ | ⟨w, _ | ⟨w', ws⟩⟩
          · rw [hh] at hlen; simp at hlen
          · exact ⟨w, rfl⟩
          · rw [hh] at hlen; simp at hlen
        have hwd := ihd w (by simp [formulaHead] at hw1 ⊢; rw [hw1]; simp)
        simp only [formulaHead] at hw1
        simp only [formulaHead, formulaTail, hw1]
        refine ⟨?_, rfl⟩
        simp only [mapNTree, List.cons_append, List.nil_append, List.map_cons, List.map_nil]
        refine AllLC.mk ?_ ?_
        · refine ⟨rfl, rfl, ?_⟩
          refine ⟨_, _, rfl, ?_⟩
          simp only [mapNTree_label]
          simp [proj, gMemRow9, memDecomposeSkel, hw.2, hwd.2]
        · intro c hc
          simp at hc
          rcases hc with rfl | rfl
          · exact hwd.1
          · exact hw.1

theorem descentCont_LC (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) (X : Noun) (h1 : cont.length = 1)
    (hcont : ∀ u ∈ cont, AllLC E (mapNTree proj u) ∧ u.label.skel.parent = X) :
    ∀ remaining current, 1 ≤ remaining → Noun.slot remaining current = some X →
      ∀ u ∈ (genAnnotatedDescentCont E z lmb cont contCell contState current remaining).1,
        AllLC E (mapNTree proj u) ∧ u.label.skel.parent = current := by
  intro remaining
  induction remaining using Nat.strongRecOn with
  | _ n ih =>
    intro current hr hslot u hu
    have hdesc := hu
    unfold genAnnotatedDescentCont at hdesc
    split at hdesc
    · rename_i hlt
      have hn : n = 1 := by omega
      subst hn
      simp [Noun.slot] at hslot
      subst hslot
      exact hcont u hdesc
    · rename_i hge
      have h2 : 2 ≤ n := by omega
      obtain ⟨hd, tl, rfl⟩ := cell_of_slot h2 hslot
      rw [slot_eq_msb hd tl h2] at hslot
      have hr1 : 1 ≤ axisRest n := axisRest_pos h2
      split at hdesc
      · rename_i ht
        simp only [ht, if_true] at hslot
        simp at hdesc
        subst hdesc
        have hlen := genAnnotatedDescentCont_length_one (lmb := lmb) E z cont contCell contState
          h1 (formulaTail (.cell hd tl)) (axisRest n)
        have ihd := ih (axisRest n) (axisRest_lt h2) tl hr1 hslot
        have hw := walk_LC (lmb := lmb) E z hd
        obtain ⟨w, hw1⟩ : ∃ w, (genAnnotatedDescentCont E z lmb cont contCell contState
            (formulaTail (.cell hd tl)) (axisRest n)).1 = [w] := by
          rcases hh : (genAnnotatedDescentCont E z lmb cont contCell contState
            (formulaTail (.cell hd tl)) (axisRest n)).1 with _ | ⟨w, _ | ⟨w', ws⟩⟩
          · rw [hh] at hlen; simp at hlen
          · exact ⟨w, rfl⟩
          · rw [hh] at hlen; simp at hlen
        have hwd := ihd w (by simp [formulaTail] at hw1 ⊢; rw [hw1]; simp)
        simp only [formulaTail] at hw1
        simp only [formulaHead, formulaTail, hw1]
        refine ⟨?_, rfl⟩
        simp only [mapNTree, List.cons_append, List.nil_append, List.map_cons, List.map_nil]
        refine AllLC.mk ?_ ?_
        · refine ⟨rfl, rfl, ?_⟩
          refine ⟨_, _, rfl, ?_⟩
          simp only [mapNTree_label]
          simp [proj, gMemRow9, memDecomposeSkel, hw.2, hwd.2]
        · intro c hc
          simp at hc
          rcases hc with rfl | rfl
          · exact hw.1
          · exact hwd.1
      · rename_i ht
        have ht' : axisTopBit n = false := Bool.eq_false_iff.mpr ht
        simp only [ht', Bool.false_eq_true, if_false] at hslot
        simp at hdesc
        subst hdesc
        have hlen := genAnnotatedDescentCont_length_one (lmb := lmb) E z cont contCell contState
          h1 (formulaHead (.cell hd tl)) (axisRest n)
        have ihd := ih (axisRest n) (axisRest_lt h2) hd hr1 hslot
        have hw := walk_LC (lmb := lmb) E z tl
        obtain ⟨w, hw1⟩ : ∃ w, (genAnnotatedDescentCont E z lmb cont contCell contState
            (formulaHead (.cell hd tl)) (axisRest n)).1 = [w] := by
          rcases hh : (genAnnotatedDescentCont E z lmb cont contCell contState
            (formulaHead (.cell hd tl)) (axisRest n)).1 with _ | ⟨w, _ | ⟨w', ws⟩⟩
          · rw [hh] at hlen; simp at hlen
          · exact ⟨w, rfl⟩
          · rw [hh] at hlen; simp at hlen
        have hwd := ihd w (by simp [formulaHead] at hw1 ⊢; rw [hw1]; simp)
        simp only [formulaHead] at hw1
        simp only [formulaHead, formulaTail, hw1]
        refine ⟨?_, rfl⟩
        simp only [mapNTree, List.cons_append, List.nil_append, List.map_cons, List.map_nil]
        refine AllLC.mk ?_ ?_
        · refine ⟨rfl, rfl, ?_⟩
          refine ⟨_, _, rfl, ?_⟩
          simp only [mapNTree_label]
          simp [proj, gMemRow9, memDecomposeSkel, hw.2, hwd.2]
        · intro c hc
          simp at hc
          rcases hc with rfl | rfl
          · exact hwd.1
          · exact hw.1

/-- A record is served: its axis is positive and `slot` reaches its child. -/
def RecOK (r : MemRecordReq) : Prop := Noun.slot r.axis r.root = some r.child

theorem pos_of_RecOK {r : MemRecordReq} (h : RecOK r) : 1 ≤ r.axis := by
  rcases Nat.eq_zero_or_pos r.axis with h0 | h0
  · unfold RecOK at h; rw [h0] at h; simp [Noun.slot] at h
  · exact h0

theorem recordTree_LC (E : Noun → ComputeTable.FP K) (z α : K) (r : MemRecordReq)
    (hr : RecOK r) :
    AllLC E (mapNTree proj (genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp)) := by
  have hlen := genAnnotatedDescent_length (lmb := lmb) E z r.root r.child r.axis
    (α ^ r.recordExp) r.recordExp r.root r.axis
  have hd := descent_LC (lmb := lmb) E z r.root r.child r.axis (α ^ r.recordExp) r.recordExp
    r.axis r.root (pos_of_RecOK hr) hr
  obtain ⟨w, hw1⟩ : ∃ w, (genAnnotatedDescent E z lmb r.root r.child r.axis (α ^ r.recordExp)
      r.recordExp r.root r.axis).1 = [w] := by
    rcases hh : (genAnnotatedDescent E z lmb r.root r.child r.axis (α ^ r.recordExp)
      r.recordExp r.root r.axis).1 with _ | ⟨w, _ | ⟨w', ws⟩⟩
    · rw [hh] at hlen; simp at hlen
    · exact ⟨w, rfl⟩
    · rw [hh] at hlen; simp at hlen
  have hwd := hd w (by rw [hw1]; simp)
  unfold genAnnotatedRecordTree
  simp only [hw1, mapNTree, List.map_cons, List.map_nil]
  refine AllLC.mk ?_ ?_
  · refine ⟨rfl, rfl, ?_⟩
    refine ⟨_, rfl, ?_⟩
    simp only [mapNTree_label]
    simp [proj, gMemRow9, memReadSkelAx, hwd.2]
  · intro c hc
    simp at hc
    subst hc
    exact hwd.1

theorem chainedTree_LC (E : Noun → ComputeTable.FP K) (z α : K) (r1 r2 : MemRecordReq)
    (hchain : r1.child = r2.root) (h1 : RecOK r1) (h2 : RecOK r2)
    (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z α lmb [r1, r2] = some t) :
    AllLC E (mapNTree proj t) := by
  -- the inner continuation: read r2 over verify r1 over the r2 descent
  set V2 := genAnnotatedVerify E z lmb r2.root r2.child r2.axis (α ^ r2.recordExp) r2.recordExp
  have hV2 := verify_LC (lmb := lmb) E z r2.root r2.child r2.axis (α ^ r2.recordExp) r2.recordExp
  set D2 := genAnnotatedDescentCont E z lmb [V2.1] V2.2 .verify_child r2.root r2.axis
  have hD2len : D2.1.length = 1 :=
    genAnnotatedDescentCont_length_one (lmb := lmb) E z [V2.1] V2.2 .verify_child (by simp)
      r2.root r2.axis
  have hD2 := descentCont_LC (lmb := lmb) E z [V2.1] V2.2 .verify_child r2.child (by simp)
    (by intro u hu; simp at hu; subst hu; exact hV2) r2.axis r2.root (pos_of_RecOK h2) h2
  obtain ⟨d2, hd2⟩ : ∃ w, D2.1 = [w] := by
    rcases hh : D2.1 with _ | ⟨w, _ | ⟨w', ws⟩⟩
    · rw [hh] at hD2len; simp at hD2len
    · exact ⟨w, rfl⟩
    · rw [hh] at hD2len; simp at hD2len
  have hd2' := hD2 d2 (by rw [hd2]; simp)
  have hinner : genAnnotatedChainedInner E z α lmb r1 [r2] =
      ([.node (gMemRow9 (memReadSkelAx r2.root r2.child r2.axis) r2.recordExp z
          (annotatedReadPub E r2.root r2.child r2.axis (α ^ r2.recordExp)
            (annotatedVerifyPub E r1.root r1.child r1.axis (α ^ r1.recordExp) D2.2 0 0 lmb).pt
            0 0 lmb))
        [.node (gMemRow9 (memVerifySkelAx r1.root r1.child r1.axis) r1.recordExp z
            (annotatedVerifyPub E r1.root r1.child r1.axis (α ^ r1.recordExp) D2.2 0 0 lmb))
          D2.1]],
       (annotatedReadPub E r2.root r2.child r2.axis (α ^ r2.recordExp)
          (annotatedVerifyPub E r1.root r1.child r1.axis (α ^ r1.recordExp) D2.2 0 0 lmb).pt
          0 0 lmb).pt) := by
    unfold genAnnotatedChainedInner
    simp only [genAnnotatedChainedInner_nil, chainedInnerRootState]
    rfl
  set I := genAnnotatedChainedInner E z α lmb r1 [r2]
  have hIlen : I.1.length = 1 := by rw [hinner]; simp
  have hI : ∀ u ∈ I.1, AllLC E (mapNTree proj u) ∧ u.label.skel.parent = r1.child := by
    intro u hu
    rw [hinner] at hu
    simp at hu
    subst hu
    refine ⟨?_, by simp [gMemRow9, memReadSkelAx, hchain]⟩
    simp only [mapNTree, List.map_cons, List.map_nil, hd2]
    refine AllLC.mk ?_ ?_
    · refine ⟨rfl, rfl, ?_⟩
      refine ⟨_, rfl, ?_⟩
      simp [proj, gMemRow9, memReadSkelAx, memVerifySkelAx, hchain]
    · intro c hc
      simp at hc
      subst hc
      refine AllLC.mk ?_ ?_
      · refine ⟨rfl, rfl, ?_⟩
        refine ⟨_, rfl, ?_⟩
        simp only [mapNTree_label]
        simp [proj, gMemRow9, memVerifySkelAx, hd2'.2, hchain]
      · intro c hc
        simp at hc
        subst hc
        exact hd2'.1
  set D1 := genAnnotatedDescentCont E z lmb I.1 I.2 (chainedInnerRootState [r2]) r1.root r1.axis
  have hD1len : D1.1.length = 1 :=
    genAnnotatedDescentCont_length_one (lmb := lmb) E z I.1 I.2 _ hIlen r1.root r1.axis
  have hD1 := descentCont_LC (lmb := lmb) E z I.1 I.2 (chainedInnerRootState [r2]) r1.child hIlen
    hI r1.axis r1.root (pos_of_RecOK h1) h1
  obtain ⟨d1, hd1⟩ : ∃ w, D1.1 = [w] := by
    rcases hh : D1.1 with _ | ⟨w, _ | ⟨w', ws⟩⟩
    · rw [hh] at hD1len; simp at hD1len
    · exact ⟨w, rfl⟩
    · rw [hh] at hD1len; simp at hD1len
  have hd1' := hD1 d1 (by rw [hd1]; simp)
  have hopen : genAnnotatedChainedTree E z α lmb [r1, r2] =
      some (.node (gMemRow9 (memReadSkelAx r1.root r1.child r1.axis) r1.recordExp z
        (annotatedReadPub E r1.root r1.child r1.axis (α ^ r1.recordExp) D1.2 0 0 lmb)) D1.1) := rfl
  rw [hopen] at ht
  injection ht with ht
  subst ht
  simp only [mapNTree, hd1, List.map_cons, List.map_nil]
  refine AllLC.mk ?_ ?_
  · refine ⟨rfl, rfl, ?_⟩
    refine ⟨_, rfl, ?_⟩
    simp only [mapNTree_label]
    simp [proj, gMemRow9, memReadSkelAx, hd1'.2]
  · intro c hc
    simp at hc
    subst hc
    exact hd1'.1

theorem rowForest_LC (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ rs : List MemRecordReq, (∀ r ∈ rs, RecOK r) →
      ∀ u ∈ genRowMemForest E z α lmb rs, AllLC E (mapNTree proj u)
  | [], _, u, hu => by simp [genRowMemForest] at hu
  | [r], h, u, hu => by
      simp [genRowMemForest_singleton] at hu
      subst hu
      exact recordTree_LC E z α r (h r (by simp))
  | [r1, r2], h, u, hu => by
      rw [genRowMemForest_two_eq] at hu
      by_cases hc : r1.child = r2.root
      · rw [if_pos hc] at hu
        cases hch : genAnnotatedChainedTree E z α lmb [r1, r2] with
        | none => simp [genAnnotatedChainedTree] at hch
        | some t =>
          simp [hch] at hu
          rw [hu]
          exact chainedTree_LC E z α r1 r2 hc (h r1 (by simp)) (h r2 (by simp)) t hch
      · rw [if_neg hc] at hu
        simp at hu
        rcases hu with rfl | rfl
        · exact recordTree_LC E z α r1 (h r1 (by simp))
        · exact recordTree_LC E z α r2 (h r2 (by simp))
  | [r1, r2, r3], h, u, hu => by
      rw [genRowMemForest_three_eq] at hu
      simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact rowForest_LC E z α [r1, r2] (fun r hr => h r (by simp at hr ⊢; tauto)) u hu
      · exact recordTree_LC E z α r3 (h r3 (by simp))
  | r1 :: r2 :: r3 :: r4 :: rest, h, u, hu => by
      unfold genRowMemForest at hu
      simp only [List.mem_map] at hu
      obtain ⟨r, hr, rfl⟩ := hu
      exact recordTree_LC E z α r (h r hr)

/-- A forest tree comes from one compute node's row forest. -/
theorem mem_fromTree (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ (N : ℕ) (t : NTree (GenComputeRow K)), t.size ≤ N →
      ∀ u ∈ genMemForestFromTree E z α lmb t,
        ∃ n, InTree t n ∧ u ∈ genRowMemForest E z α lmb (extractNodeReqs n.label) := by
  intro N
  induction N with
  | zero =>
    intro t ht u hu
    cases t with
    | node g cs => simp [NTree.size] at ht
  | succ N ih =>
    intro t ht u hu
    cases t with
    | node g cs =>
      simp [genMemForestFromTree] at hu
      rcases hu with hu | hu
      · exact ⟨_, InTree.here _, hu⟩
      · have recList : ∀ cs', (∀ c ∈ cs', c ∈ cs) → ∀ u' ∈ genMemForestFromList E z α lmb cs',
            ∃ n, InTree (.node g cs) n ∧ u' ∈ genRowMemForest E z α lmb (extractNodeReqs n.label) := by
          intro cs' hsub u' hu'
          induction cs' generalizing u' with
          | nil => simp [genMemForestFromList] at hu'
          | cons c rest ihcs =>
            simp [genMemForestFromList] at hu'
            rcases hu' with hu' | hu'
            · have hc : c ∈ cs := hsub c (by simp)
              have hsz : c.size ≤ N := by
                have hin : NTree.size c ∈ cs.map NTree.size := List.mem_map.mpr ⟨c, hc, rfl⟩
                have hsum : NTree.size c ≤ (cs.map NTree.size).sum := List.le_sum_of_mem hin
                simp [NTree.size] at ht
                omega
              obtain ⟨n, hn, hun⟩ := ih c hsz u' hu'
              exact ⟨n, InTree.sub (by simpa using hc) hn, hun⟩
            · exact ihcs (fun c' hc' => hsub c' (List.mem_cons_of_mem _ hc')) u' hu'
        exact recList cs (fun _ h => h) u hu

theorem fromTree_LC (E : Noun → ComputeTable.FP K) (z α : K) (t : NTree (GenComputeRow K))
    (hrec : ∀ n, InTree t n → ∀ r ∈ extractNodeReqs n.label, RecOK r) :
    ∀ u ∈ genMemForestFromTree E z α lmb t, AllLC E (mapNTree proj u) := by
  intro u hu
  obtain ⟨n, hn, hun⟩ := mem_fromTree E z α t.size t le_rfl u hu
  exact rowForest_LC E z α _ (hrec n hn) u hun

/-- Threading is invisible to any label projection that ignores the accumulator columns. -/
theorem thread_map (inp : MemoryTable.Inputs K) {β : Type} (f : GenMemoryRow K → β)
    (hf : ∀ g a b, f (setGenAcc g a b) = f g) :
    ∀ acc (forest : List (NTree (GenMemoryRow K))),
      (threadGenForest inp acc forest).map (mapNTree f) = forest.map (mapNTree f) := by
  intro acc forest
  have hrows : ∀ acc gs, (threadGenRows inp acc gs).map f = gs.map f := by
    intro acc gs
    induction gs generalizing acc with
    | nil => rfl
    | cons g gs ih =>
      simp only [threadGenRows, List.map_cons, threadGenRow_snd, hf, ih]
  unfold threadGenForest
  rw [zipBfs_mapNTree, hrows]
  have hlabs : ((bfsForest forest).map NTree.label).map f =
      (bfsForest (forest.map (mapNTree f))).map NTree.label := by
    rw [bfsForest_mapNTree, List.map_map, List.map_map]
    refine List.map_congr_left ?_
    intro t _
    exact (mapNTree_label f t).symm
  rw [hlabs, zipBfs_self]

theorem proj_setGenAcc (g : GenMemoryRow K) (a b : K) : proj (setGenAcc g a b) = proj g := rfl

theorem genMemoryForest_LC (z α : K) (inp : MemoryTable.Inputs K)
    (t : NTree (GenComputeRow K))
    (hrec : ∀ n, InTree (bfsAssign (airReorder t)) n → ∀ r ∈ extractNodeReqs n.label, RecOK r) :
    ∀ u ∈ genMemoryForest z α lmb inp t, AllLC (encC z) (mapNTree proj u) := by
  intro u hu
  have hmap := thread_map inp proj proj_setGenAcc 0
    (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t)))
  have hmem : mapNTree proj u ∈ (genMemoryForest z α lmb inp t).map (mapNTree proj) :=
    List.mem_map.mpr ⟨u, hu, rfl⟩
  unfold genMemoryForest at hmem
  rw [hmap] at hmem
  obtain ⟨u', hu', heq⟩ := List.mem_map.mp hmem
  rw [← heq]
  exact fromTree_LC (encC z) z α _ hrec u' hu'

section PC

variable {F : Type} [Field F] [Algebra F K]

/-- `honestAtomOf`, read off `(st, pt.noun)` only. -/
noncomputable def atomOfStPt (st : MState) (fp : ComputeTable.FP K) : F :=
  letI := Classical.propDecidable
  if h : st = .halt ∧ ∃ a : F, algebraMap F K a = fp.leaf then h.2.choose else 0

theorem honestAtomOf_eq (pub : MemoryTable.Pub K) :
    OptimizedMemoryCanonicalTrace.honestAtomOf (F := F) pub = atomOfStPt pub.st pub.pt.noun := rfl

/-- The pre-`z` label of a projected row. -/
noncomputable def preD (x : PL K) : MState × F := (x.2.2.1, atomOfStPt x.2.2.1 x.2.2.2)

theorem leafAtomOf_natCast {q a : ℕ} (ha : a < q) (hq : q ≤ ringChar K) :
    HostileSkeletonDecoding.leafAtomOf q ((a : ℕ) : K) = a := by
  have hex : ∃ k : ℕ, k < q ∧ (k : K) = (a : K) := ⟨a, ha, rfl⟩
  have h1 := HostileSkeletonDecoding.leafAtomOf_cast hex
  have h2 := HostileSkeletonDecoding.leafAtomOf_lt hex
  exact OptimizedComputeFinalTrace.natCast_inj_of_lt_ringChar (by omega) (by omega) h1

theorem halt_atom (z : K) (q a : ℕ) (ha : a < q) (hq : q ≤ ringChar K) :
    HostileSkeletonDecoding.leafAtomOf q
      (algebraMap F K (atomOfStPt (F := F) .halt (encC z (.atom a)))) = a := by
  have hleaf : (encC z (.atom a)).leaf = algebraMap F K (a : F) := by
    simp [encC, NPR.leafF, Noun.leafList, hornerLE]
  have hex : (MState.halt = .halt ∧ ∃ b : F, algebraMap F K b = (encC z (.atom a)).leaf) :=
    ⟨rfl, ⟨a, hleaf.symm⟩⟩
  unfold atomOfStPt
  rw [dif_pos hex, hex.2.choose_spec, hleaf, map_natCast]
  exact leafAtomOf_natCast ha hq

/-- **Decoding a structurally consistent projected tree returns its parent noun.** -/
theorem decode_of_LC (z : K) (q : ℕ) (hq : q ≤ ringChar K) :
    ∀ v : NTree (PL K), AllLC (encC z) v →
      (∀ w, InTree v w → ∀ a, w.label.1.state = .halt → w.label.1.parent = .atom a → a < q) →
      PreSeedCensus.decodePre K q (mapNTree (preD (F := F)) v) = v.label.1.parent := by
  intro v
  induction v using NTree.rec
    (motive_2 := fun cs => ∀ c ∈ cs, AllLC (encC z) c →
      (∀ w, InTree c w → ∀ a, w.label.1.state = .halt → w.label.1.parent = .atom a → a < q) →
      PreSeedCensus.decodePre K q (mapNTree (preD (F := F)) c) = c.label.1.parent) with
  | node x cs ih =>
    intro hLC hb
    have hroot := hLC _ (InTree.here _)
    obtain ⟨h1, h2, hs⟩ := hroot
    have hch : ∀ c ∈ cs, PreSeedCensus.decodePre K q (mapNTree (preD (F := F)) c) =
        c.label.1.parent := fun c hc =>
      ih c hc (fun w hw => hLC w (InTree.sub (by simpa using hc) hw))
        (fun w hw => hb w (InTree.sub (by simpa using hc) hw))
    simp only [NTree.label] at h1 h2 hs ⊢
    obtain ⟨sk, st, pst, fp⟩ := x
    simp only at h1 h2 hs ⊢
    subst h1; subst h2
    cases hst : sk.state with
    | halt =>
      rw [hst] at hs
      obtain ⟨hnil, a, hpa, hfp⟩ := hs
      simp only [NTree.children, NTree.label] at hnil hpa hfp
      subst hnil
      have ha := hb _ (InTree.here _) a hst hpa
      simp only [mapNTree, List.map_nil, preD, hst, hfp]
      rw [PreSeedCensus.decodePre, hpa, halt_atom z q a ha hq]
    | decompose =>
      rw [hst] at hs
      obtain ⟨l, r, hlr, hp⟩ := hs
      simp only [NTree.children, NTree.label] at hlr hp
      subst hlr
      simp only [mapNTree, List.map_cons, List.map_nil, preD, hst]
      rw [PreSeedCensus.decodePre, hch l (by simp), hch r (by simp)]
      simp only [NTree.label]; exact hp.symm
    | read_root =>
      rw [hst] at hs
      obtain ⟨c, hc, hp⟩ := hs
      simp only [NTree.children, NTree.label] at hc hp
      subst hc
      simp only [mapNTree, List.map_cons, List.map_nil, preD, hst]
      rw [PreSeedCensus.decodePre, hch c (by simp)]
      simp only [NTree.label]; exact hp.symm
    | verify_child =>
      rw [hst] at hs
      obtain ⟨c, hc, hp⟩ := hs
      simp only [NTree.children, NTree.label] at hc hp
      subst hc
      simp only [mapNTree, List.map_cons, List.map_nil, preD, hst]
      rw [PreSeedCensus.decodePre, hch c (by simp)]
      simp only [NTree.label]; exact hp.symm
  | nil => rename_i hc _ _; simp at hc
  | cons c cs ihc ihcs =>
    rename_i d hd hA hB
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact ihc hA hB
    · exact ihcs d hd hA hB

end PC

section Exists

/-- A verify node of exponent `e` somewhere in `u`. -/
def HasVerify (e : ℕ) (u : NTree (GenMemoryRow K)) : Prop :=
  ∃ v, InTree u v ∧ v.label.skel.state = .verify_child ∧ v.label.stamp.recordExponent = e

theorem verify_has (E : Noun → ComputeTable.FP K) (z : K) (root child : Noun) (ax : ℕ) (ts : K)
    (e : ℕ) : HasVerify e (genAnnotatedVerify E z lmb root child ax ts e).1 :=
  ⟨_, InTree.here _, rfl, rfl⟩

theorem HasVerify.lift {e : ℕ} {a : GenMemoryRow K} {cs : List (NTree (GenMemoryRow K))}
    {c : NTree (GenMemoryRow K)} (hc : c ∈ cs) (h : HasVerify e c) : HasVerify e (.node a cs) := by
  obtain ⟨v, hv, h1, h2⟩ := h
  exact ⟨v, InTree.sub (by simpa using hc) hv, h1, h2⟩

theorem descent_has (E : Noun → ComputeTable.FP K) (z : K) (root child : Noun) (recAxis : ℕ)
    (ts : K) (e : ℕ) :
    ∀ remaining current, ∀ u ∈ (genAnnotatedDescent E z lmb root child recAxis ts e current remaining).1,
      HasVerify e u := by
  intro remaining
  induction remaining using Nat.strongRecOn with
  | _ n ih =>
    intro current u hu
    have hdesc := hu
    unfold genAnnotatedDescent at hdesc
    split at hdesc
    · simp at hdesc; subst hdesc; exact verify_has E z root child recAxis ts e
    · rename_i hge
      have h2 : 2 ≤ n := by omega
      have hlen1 := genAnnotatedDescent_length (lmb := lmb) E z root child recAxis ts e
          (formulaTail current) (axisRest n)
      have hlen2 := genAnnotatedDescent_length (lmb := lmb) E z root child recAxis ts e
          (formulaHead current) (axisRest n)
      split at hdesc
      · simp at hdesc; subst hdesc
        obtain ⟨w, hw⟩ : ∃ w, (genAnnotatedDescent E z lmb root child recAxis ts e
            (formulaTail current) (axisRest n)).1 = [w] := by
          rcases hh : (genAnnotatedDescent E z lmb root child recAxis ts e
            (formulaTail current) (axisRest n)).1 with _ | ⟨w, _ | ⟨w', ws⟩⟩
          · rw [hh] at hlen1; simp at hlen1
          · exact ⟨w, rfl⟩
          · rw [hh] at hlen1; simp at hlen1
        have := ih (axisRest n) (axisRest_lt h2) (formulaTail current) w (by rw [hw]; simp)
        simp only [hw]
        exact HasVerify.lift (by simp) this
      · simp at hdesc; subst hdesc
        obtain ⟨w, hw⟩ : ∃ w, (genAnnotatedDescent E z lmb root child recAxis ts e
            (formulaHead current) (axisRest n)).1 = [w] := by
          rcases hh : (genAnnotatedDescent E z lmb root child recAxis ts e
            (formulaHead current) (axisRest n)).1 with _ | ⟨w, _ | ⟨w', ws⟩⟩
          · rw [hh] at hlen2; simp at hlen2
          · exact ⟨w, rfl⟩
          · rw [hh] at hlen2; simp at hlen2
        have := ih (axisRest n) (axisRest_lt h2) (formulaHead current) w (by rw [hw]; simp)
        simp only [hw]
        exact HasVerify.lift (by simp) this

theorem descentCont_has (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) (h1 : cont.length = 1) (Pr : NTree (GenMemoryRow K) → Prop)
    (hlift : ∀ (a : GenMemoryRow K) cs c, c ∈ cs → Pr c → Pr (.node a cs))
    (hcont : ∀ u ∈ cont, Pr u) :
    ∀ remaining current, ∀ u ∈ (genAnnotatedDescentCont E z lmb cont contCell contState
      current remaining).1, Pr u := by
  intro remaining
  induction remaining using Nat.strongRecOn with
  | _ n ih =>
    intro current u hu
    have hdesc := hu
    unfold genAnnotatedDescentCont at hdesc
    split at hdesc
    · exact hcont u hdesc
    · rename_i hge
      have h2 : 2 ≤ n := by omega
      have hlen1 := genAnnotatedDescentCont_length_one (lmb := lmb) E z cont contCell contState
          h1 (formulaTail current) (axisRest n)
      have hlen2 := genAnnotatedDescentCont_length_one (lmb := lmb) E z cont contCell contState
          h1 (formulaHead current) (axisRest n)
      split at hdesc
      · simp at hdesc; subst hdesc
        obtain ⟨w, hw⟩ : ∃ w, (genAnnotatedDescentCont E z lmb cont contCell contState
            (formulaTail current) (axisRest n)).1 = [w] := by
          rcases hh : (genAnnotatedDescentCont E z lmb cont contCell contState
            (formulaTail current) (axisRest n)).1 with _ | ⟨w, _ | ⟨w', ws⟩⟩
          · rw [hh] at hlen1; simp at hlen1
          · exact ⟨w, rfl⟩
          · rw [hh] at hlen1; simp at hlen1
        have := ih (axisRest n) (axisRest_lt h2) (formulaTail current) w (by rw [hw]; simp)
        simp only [hw]
        exact hlift _ _ w (by simp) this
      · simp at hdesc; subst hdesc
        obtain ⟨w, hw⟩ : ∃ w, (genAnnotatedDescentCont E z lmb cont contCell contState
            (formulaHead current) (axisRest n)).1 = [w] := by
          rcases hh : (genAnnotatedDescentCont E z lmb cont contCell contState
            (formulaHead current) (axisRest n)).1 with _ | ⟨w, _ | ⟨w', ws⟩⟩
          · rw [hh] at hlen2; simp at hlen2
          · exact ⟨w, rfl⟩
          · rw [hh] at hlen2; simp at hlen2
        have := ih (axisRest n) (axisRest_lt h2) (formulaHead current) w (by rw [hw]; simp)
        simp only [hw]
        exact hlift _ _ w (by simp) this

theorem recordTree_has (E : Noun → ComputeTable.FP K) (z α : K) (r : MemRecordReq) :
    HasVerify r.recordExp (genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) := by
  have hlen := genAnnotatedDescent_length (lmb := lmb) E z r.root r.child r.axis
    (α ^ r.recordExp) r.recordExp r.root r.axis
  obtain ⟨w, hw1⟩ : ∃ w, (genAnnotatedDescent E z lmb r.root r.child r.axis (α ^ r.recordExp)
      r.recordExp r.root r.axis).1 = [w] := by
    rcases hh : (genAnnotatedDescent E z lmb r.root r.child r.axis (α ^ r.recordExp)
      r.recordExp r.root r.axis).1 with _ | ⟨w, _ | ⟨w', ws⟩⟩
    · rw [hh] at hlen; simp at hlen
    · exact ⟨w, rfl⟩
    · rw [hh] at hlen; simp at hlen
  have := descent_has (lmb := lmb) E z r.root r.child r.axis (α ^ r.recordExp) r.recordExp
    r.axis r.root w (by rw [hw1]; simp)
  unfold genAnnotatedRecordTree
  simp only [hw1]
  exact HasVerify.lift (by simp) this

theorem chainedTree_has (E : Noun → ComputeTable.FP K) (z α : K) (r1 r2 : MemRecordReq)
    (t : NTree (GenMemoryRow K)) (ht : genAnnotatedChainedTree E z α lmb [r1, r2] = some t) :
    HasVerify r1.recordExp t ∧ HasVerify r2.recordExp t := by
  set V2 := genAnnotatedVerify E z lmb r2.root r2.child r2.axis (α ^ r2.recordExp) r2.recordExp
  set D2 := genAnnotatedDescentCont E z lmb [V2.1] V2.2 .verify_child r2.root r2.axis
  have hD2len : D2.1.length = 1 :=
    genAnnotatedDescentCont_length_one (lmb := lmb) E z [V2.1] V2.2 .verify_child (by simp)
      r2.root r2.axis
  obtain ⟨d2, hd2⟩ : ∃ w, D2.1 = [w] := by
    rcases hh : D2.1 with _ | ⟨w, _ | ⟨w', ws⟩⟩
    · rw [hh] at hD2len; simp at hD2len
    · exact ⟨w, rfl⟩
    · rw [hh] at hD2len; simp at hD2len
  have hd2v : HasVerify r2.recordExp d2 :=
    descentCont_has (lmb := lmb) E z [V2.1] V2.2 .verify_child (by simp) (HasVerify r2.recordExp)
      (fun a cs c hc h => HasVerify.lift hc h)
      (by intro u hu; simp at hu; subst hu; exact verify_has E z _ _ _ _ _) r2.axis r2.root d2
      (by rw [hd2]; simp)
  have hinner : genAnnotatedChainedInner E z α lmb r1 [r2] =
      ([.node (gMemRow9 (memReadSkelAx r2.root r2.child r2.axis) r2.recordExp z
          (annotatedReadPub E r2.root r2.child r2.axis (α ^ r2.recordExp)
            (annotatedVerifyPub E r1.root r1.child r1.axis (α ^ r1.recordExp) D2.2 0 0 lmb).pt
            0 0 lmb))
        [.node (gMemRow9 (memVerifySkelAx r1.root r1.child r1.axis) r1.recordExp z
            (annotatedVerifyPub E r1.root r1.child r1.axis (α ^ r1.recordExp) D2.2 0 0 lmb))
          D2.1]],
       (annotatedReadPub E r2.root r2.child r2.axis (α ^ r2.recordExp)
          (annotatedVerifyPub E r1.root r1.child r1.axis (α ^ r1.recordExp) D2.2 0 0 lmb).pt
          0 0 lmb).pt) := by
    unfold genAnnotatedChainedInner
    simp only [genAnnotatedChainedInner_nil, chainedInnerRootState]
    rfl
  set I := genAnnotatedChainedInner E z α lmb r1 [r2]
  have hIlen : I.1.length = 1 := by rw [hinner]; simp
  have hI : ∀ u ∈ I.1, HasVerify r1.recordExp u ∧ HasVerify r2.recordExp u := by
    intro u hu
    rw [hinner] at hu
    simp at hu
    subst hu
    have hvn : HasVerify r1.recordExp (NTree.node (gMemRow9 (memVerifySkelAx r1.root r1.child
        r1.axis) r1.recordExp z (annotatedVerifyPub E r1.root r1.child r1.axis (α ^ r1.recordExp)
        D2.2 0 0 lmb)) D2.1) := ⟨_, InTree.here _, rfl, rfl⟩
    have hvn2 : HasVerify r2.recordExp (NTree.node (gMemRow9 (memVerifySkelAx r1.root r1.child
        r1.axis) r1.recordExp z (annotatedVerifyPub E r1.root r1.child r1.axis (α ^ r1.recordExp)
        D2.2 0 0 lmb)) D2.1) := by
      rw [hd2]; exact HasVerify.lift (c := d2) (by simp) hd2v
    exact ⟨HasVerify.lift (by simp) hvn, HasVerify.lift (by simp) hvn2⟩
  set D1 := genAnnotatedDescentCont E z lmb I.1 I.2 (chainedInnerRootState [r2]) r1.root r1.axis
  have hD1len : D1.1.length = 1 :=
    genAnnotatedDescentCont_length_one (lmb := lmb) E z I.1 I.2 _ hIlen r1.root r1.axis
  obtain ⟨d1, hd1⟩ : ∃ w, D1.1 = [w] := by
    rcases hh : D1.1 with _ | ⟨w, _ | ⟨w', ws⟩⟩
    · rw [hh] at hD1len; simp at hD1len
    · exact ⟨w, rfl⟩
    · rw [hh] at hD1len; simp at hD1len
  have hd1v := descentCont_has (lmb := lmb) E z I.1 I.2 (chainedInnerRootState [r2]) hIlen
      (fun u => HasVerify r1.recordExp u ∧ HasVerify r2.recordExp u)
      (fun a cs c hc h => ⟨HasVerify.lift hc h.1, HasVerify.lift hc h.2⟩) hI r1.axis r1.root d1
      (by rw [hd1]; simp)
  have hopen : genAnnotatedChainedTree E z α lmb [r1, r2] =
      some (.node (gMemRow9 (memReadSkelAx r1.root r1.child r1.axis) r1.recordExp z
        (annotatedReadPub E r1.root r1.child r1.axis (α ^ r1.recordExp) D1.2 0 0 lmb)) D1.1) := rfl
  rw [hopen] at ht
  injection ht with ht
  subst ht
  simp only [hd1]
  exact ⟨HasVerify.lift (by simp) hd1v.1, HasVerify.lift (by simp) hd1v.2⟩

theorem rowForest_has (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ rs : List MemRecordReq, ∀ r ∈ rs,
      ∃ u ∈ genRowMemForest E z α lmb rs, HasVerify r.recordExp u
  | [], r, hr => by simp at hr
  | [r0], r, hr => by
      simp at hr; subst hr
      exact ⟨_, by simp [genRowMemForest_singleton], recordTree_has (lmb := lmb) E z α r⟩
  | [r1, r2], r, hr => by
      rw [genRowMemForest_two_eq]
      by_cases hc : r1.child = r2.root
      · rw [if_pos hc]
        cases hch : genAnnotatedChainedTree E z α lmb [r1, r2] with
        | none => simp [genAnnotatedChainedTree] at hch
        | some t =>
          have h := chainedTree_has (lmb := lmb) E z α r1 r2 t hch
          simp at hr
          rcases hr with rfl | rfl
          · exact ⟨t, by simp, h.1⟩
          · exact ⟨t, by simp, h.2⟩
      · rw [if_neg hc]
        simp at hr
        rcases hr with rfl | rfl
        · exact ⟨_, by simp, recordTree_has (lmb := lmb) E z α r⟩
        · exact ⟨_, by simp, recordTree_has (lmb := lmb) E z α r⟩
  | [r1, r2, r3], r, hr => by
      rw [genRowMemForest_three_eq]
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · obtain ⟨u, hu, h⟩ := rowForest_has E z α [r, r2] r (by simp)
        exact ⟨u, List.mem_append_left _ hu, h⟩
      · obtain ⟨u, hu, h⟩ := rowForest_has E z α [r1, r] r (by simp)
        exact ⟨u, List.mem_append_left _ hu, h⟩
      · exact ⟨_, List.mem_append_right _ (by simp), recordTree_has (lmb := lmb) E z α r⟩
  | r1 :: r2 :: r3 :: r4 :: rest, r, hr => by
      unfold genRowMemForest
      exact ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, recordTree_has (lmb := lmb) E z α r⟩

theorem fromTree_has (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ (T : NTree (GenComputeRow K)) (n : NTree (GenComputeRow K)), InTree T n →
      ∀ r ∈ extractNodeReqs n.label, ∃ u ∈ genMemForestFromTree E z α lmb T,
        HasVerify r.recordExp u := by
  intro T
  induction T using NTree.rec
    (motive_2 := fun cs => ∀ c ∈ cs, ∀ (n : NTree (GenComputeRow K)), InTree c n →
      ∀ r ∈ extractNodeReqs n.label, ∃ u ∈ genMemForestFromList E z α lmb cs,
        HasVerify r.recordExp u) with
  | node g cs ih =>
    intro n hn r hr
    cases hn with
    | here =>
      obtain ⟨u, hu, h⟩ := rowForest_has (lmb := lmb) E z α _ r hr
      exact ⟨u, by simp only [genMemForestFromTree, List.mem_append]; left; exact hu, h⟩
    | sub hs hn' =>
      obtain ⟨u, hu, h⟩ := ih _ (by simpa using hs) n hn' r hr
      exact ⟨u, by simp [genMemForestFromTree]; right; exact hu, h⟩
  | nil => rename_i hc _ _ _ _; simp at hc
  | cons c cs ihc ihcs =>
    rename_i d hd n hn r hr
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · obtain ⟨u, hu, h⟩ := ihc n hn r hr
      exact ⟨u, by simp [genMemForestFromList, hu], h⟩
    · obtain ⟨u, hu, h⟩ := ihcs d hd n hn r hr
      exact ⟨u, by simp [genMemForestFromList]; right; exact hu, h⟩

end Exists

end Nock.RedTeam.Batch1255.Mem



set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch1255.MemPkg

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.Reified

/-- `ExactTraversal.buildTF_bfsForest_get` (private there), re-proved from the public child
position lemma. -/
theorem buildTF_bfs_get {LT : Type*}
    (l : List (NTree LT)) (hl : l ≠ []) (lbl : ℕ → LT)
    (hlbl : ∀ i t, 1 ≤ i → (bfsForest l)[i - 1]? = some t → lbl i = t.label) :
    ∀ {i : ℕ} {t : NTree LT}, 1 ≤ i → (bfsForest l)[i - 1]? = some t →
      buildTF l.length (foCol (bfsForest l)) lbl (bfsForest l).length i = t := by
  intro i t hi ht
  have hih : i ≤ (bfsForest l).length := by
    have := (List.getElem?_eq_some_iff.mp ht).1
    omega
  have hSf : l.length + Sf (foCol (bfsForest l)) (bfsForest l).length = (bfsForest l).length :=
    foCol_Sf_tilingF l hl
  have hvalid : BFSValidF l.length (foCol (bfsForest l)) (bfsForest l).length :=
    foCol_BFSValidF l hl
  generalize hd : (bfsForest l).length + 1 - i = d
  induction d using Nat.strong_induction_on generalizing i t with
  | h d ih =>
      cases t with
      | node a ch =>
          have hfo : foCol (bfsForest l) i = ch.length := by
            unfold foCol; rw [ht]; rfl
          rw [buildTF, NTree.node.injEq]
          constructor
          · simpa using hlbl i (NTree.node a ch) hi ht
          · rw [List.attach_map_val, childIdxsF_eq l.length _ _ hSf hvalid hi hih, hfo]
            apply List.ext_getElem?
            intro j
            by_cases hj : j < ch.length
            · rw [List.getElem?_map, List.getElem?_range' hj, List.getElem?_eq_getElem hj]
              simp only [Nat.one_mul, Option.map_some]
              have hpos := exact_bfsForest_child_pos l hl hi (j := j) (by rw [hfo]; exact hj)
              rw [ht] at hpos
              simp only [Option.bind_some, NTree.children, List.getElem?_eq_getElem hj] at hpos
              have hqh : firstCF l.length (foCol (bfsForest l)) i + j ≤ (bfsForest l).length := by
                have := (List.getElem?_eq_some_iff.mp hpos).1
                omega
              have hqi : 1 ≤ firstCF l.length (foCol (bfsForest l)) i + j := by
                unfold firstCF; omega
              have hlt : (bfsForest l).length + 1 -
                  (firstCF l.length (foCol (bfsForest l)) i + j) < d := by
                have hv := hvalid i hi hih
                unfold firstCF at *
                omega
              rw [ih _ hlt hqi hpos hqh rfl]
            · rw [List.getElem?_map, List.getElem?_eq_none (by simp; omega),
                List.getElem?_eq_none (Nat.le_of_not_lt hj)]
              rfl

theorem buildTF_congr {α : Type*} (kr : ℕ) (fo fo' : ℕ → ℕ) (lbl lbl' : ℕ → α) (h : ℕ)
    (hfo : ∀ j, 1 ≤ j → j ≤ h → fo j = fo' j) (hlbl : ∀ j, 1 ≤ j → j ≤ h → lbl j = lbl' j) :
    ∀ i, 1 ≤ i → i ≤ h → buildTF kr fo lbl h i = buildTF kr fo' lbl' h i := by
  intro i
  induction hd : h - i using Nat.strong_induction_on generalizing i with
  | _ d ih =>
    intro hi1 hih
    rw [buildTF, buildTF]
    have hci : childIdxsF kr fo h i = childIdxsF kr fo' h i := by
      unfold childIdxsF firstCF
      rw [Nock.RedTeam.Batch996.Sf_congr (fo := fo) (fo' := fo') (k := i - 1)
        (fun j hj1 hj2 => hfo j hj1 (by omega)), hfo i hi1 hih]
    rw [hlbl i hi1 hih]
    congr 1
    rw [List.attach_map_val (f := fun j => buildTF kr fo lbl h j),
      List.attach_map_val (f := fun j => buildTF kr fo' lbl' h j), ← hci]
    apply List.map_congr_left
    intro j hj
    have : i < j ∧ j ≤ h := by
      simp only [childIdxsF, List.mem_filter, decide_eq_true_eq] at hj
      exact hj.2
    exact ih (h - j) (by omega) j rfl (by omega) this.2

section Pkg

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)


local notation "MR" => P.optimized.family.problem.cfg.memRows

noncomputable abbrev envsM : Fin MR → Env F :=
  StrategyOfTracesR0.memoryEnvsR0 P.optimized (canonicalMemoryTrace P) c

theorem envsM_trace (i : Fin MR) :
    (envsM P c i).trace = (P.memoryBaseEnv (canonicalMemoryTrace P) i).trace :=
  (OptimizedFailureEventEv.memoryBaseEnv_trace P (canonicalMemoryTrace P) c i).symm

theorem memoryPubAt_bfs (i : Fin MR) (hi : (i : ℕ) < (bfsForest P.optimized.family.problem.exec.memoryForest).length) :
    P.optimized.family.problem.exec.memoryPubAt i = ((bfsForest P.optimized.family.problem.exec.memoryForest)[(i : ℕ)]'hi).label.2.2 := by
  unfold ExactExecution.memoryPubAt ExactExecution.memoryRowAt ExactExecution.memoryRows
  simp [List.get_eq_getElem] <;> rfl

theorem preState_canon (i : Fin MR) :
    PreSeedCensus.preStateOfEnvs (envsM P c) i = (P.optimized.family.problem.exec.memoryPubAt i).st := by
  rw [← Nock.RedTeam.Batch959.memRowState_honest P i]
  unfold PreSeedCensus.preStateOfEnvs StrategyOfTraces.memoryStateOf
    WalkTilingEvents.memRowStateOf
  rw [envsM_trace]

theorem preAtom_canon (i : Fin MR) :
    PreSeedCensus.preAtomOfEnvs (envsM P c) i =
      OptimizedMemoryCanonicalTrace.honestAtomOf (F := F) (P.optimized.family.problem.exec.memoryPubAt i) := by
  unfold PreSeedCensus.preAtomOfEnvs
  rw [envsM_trace, MultiRootOptimizedAcceptance.canonical_memoryBaseEnv]
  exact OptimizedMemoryCanonicalSatisfaction.canonical_physical_atom P.optimized.sampled
    P.optimized.memoryNodes P.optimized.memoryNodes_injective P.optimized.basis
    P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit i

theorem preReqIdx_canon (hM : 0 < MR) (j : ℕ) (hj1 : 1 ≤ j) (hjM : j ≤ MR) :
    PreSeedCensus.preReqIdxOfEnvs (envsM P c) hM j =
      OptimizedMemorySemanticRealization.honestReqIdx P.optimized.family ⟨j - 1, by omega⟩ := by
  unfold PreSeedCensus.preReqIdxOfEnvs
  rw [dif_pos (by omega), envsM_trace, MultiRootOptimizedAcceptance.canonical_memoryBaseEnv]
  exact OptimizedMemoryCanonicalSatisfaction.canonical_physical_reqIdx P.optimized.sampled
    P.optimized.memoryNodes P.optimized.memoryNodes_injective P.optimized.basis
    P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit _

/-- The exec row projection the pre-`z` decoder sees. -/
noncomputable def prjE (row : MState × DTmem K) : MState × F :=
  (row.2.2.st, OptimizedMemoryCanonicalTrace.honestAtomOf (F := F) row.2.2)

/-- **The pre-`z` decoded noun at the canonical memory trace is the decode of the exec forest's
subtree at that BFS position.** -/
theorem preZNoun_canon (hM : 0 < MR) (q : ℕ)
    (htopo : ∀ t ∈ bfsForest P.optimized.family.problem.exec.memoryForest, fanoutMem t.label.2.2.st = t.children.length)
    (j : ℕ) (t : NTree (MState × DTmem K)) (hj : 1 ≤ j)
    (ht : (bfsForest P.optimized.family.problem.exec.memoryForest)[j - 1]? = some t) :
    PreSeedCensus.preZNounOfEnvs K q P.optimized.family.problem.cfg.kMem (envsM P c) hM j =
      PreSeedCensus.decodePre K q (mapNTree (prjE (F := F)) t) := by
  set l := P.optimized.family.problem.exec.memoryForest with hl
  set l' := l.map (mapNTree (prjE (F := F)))
  have hne : l ≠ [] := P.optimized.family.problem.exec.memoryForest_nonempty
  have hne' : l' ≠ [] := by simpa [l'] using hne
  have hbfs : bfsForest l' = (bfsForest l).map (mapNTree (prjE (F := F))) := bfsForest_mapNTree _ _
  have hlenM : (bfsForest l).length = MR := P.optimized.family.problem.exec.memory_bfs_length
  have hlen' : (bfsForest l').length = MR := by rw [hbfs, List.length_map, hlenM]
  have hkr : P.optimized.family.problem.cfg.kMem = l'.length := by
    simp [l', l, P.optimized.family.problem.exec.memory_root_count]
  have hjM : j ≤ MR := by
    have := (List.getElem?_eq_some_iff.mp ht).1; omega
  -- the canonical label function of `l'`
  let lbl' : ℕ → MState × F := fun i => ((bfsForest l')[i - 1]?).map NTree.label |>.getD (MState.halt, 0)
  have hlbl : ∀ i, 1 ≤ i → i ≤ MR →
      PreSeedCensus.preLblOfEnvs (envsM P c) hM i = lbl' i := by
    intro i hi1 hiM
    have hlt : i - 1 < (bfsForest l).length := by omega
    have hpub := memoryPubAt_bfs P ⟨i - 1, by omega⟩ hlt
    unfold PreSeedCensus.preLblOfEnvs
    rw [dif_pos (by omega), preState_canon, preAtom_canon]
    simp only [lbl', hbfs, List.getElem?_map, List.getElem?_eq_getElem hlt, Option.map_some,
      Option.getD_some, mapNTree_label, prjE]
    simp only at hpub
    rw [hpub]
  have hfo : ∀ i, 1 ≤ i → i ≤ MR →
      PreSeedCensus.preFoOfEnvs (envsM P c) hM i = foCol (bfsForest l') i := by
    intro i hi1 hiM
    have hlt : i - 1 < (bfsForest l).length := by omega
    have hpub := memoryPubAt_bfs P ⟨i - 1, by omega⟩ hlt
    unfold PreSeedCensus.preFoOfEnvs PreSeedCensus.preLblOfEnvs foCol
    rw [dif_pos (by omega), preState_canon]
    simp only [hbfs, List.getElem?_map, List.getElem?_eq_getElem hlt, Option.map_some,
      Option.getD_some]
    simp only at hpub
    rw [hpub, htopo _ (List.getElem_mem hlt)]
    cases ((bfsForest l)[i - 1]'hlt) with
    | node a ch => simp [mapNTree]
  unfold PreSeedCensus.preZNounOfEnvs
  have hcongr := buildTF_congr P.optimized.family.problem.cfg.kMem
    (PreSeedCensus.preFoOfEnvs (envsM P c) hM) (foCol (bfsForest l'))
    (PreSeedCensus.preLblOfEnvs (envsM P c) hM) lbl' MR hfo hlbl j hj hjM
  rw [hcongr, hkr, ← hlen']
  have ht' : (bfsForest l')[j - 1]? = some (mapNTree (prjE (F := F)) t) := by
    rw [hbfs, List.getElem?_map, ht]; rfl
  rw [buildTF_bfs_get l' hne' lbl' (fun i t' hi ht'' => by simp [lbl', ht'']) hj ht']

end Pkg

end Nock.RedTeam.Batch1255.MemPkg



set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch1255.Misc

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrategyOfTracesR0

theorem testBit_band {x m : ℕ} (h1 : 2 ^ m ≤ x) (h2 : x < 2 ^ (m + 1)) : x.testBit m = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hd : x / 2 ^ m = 1 := by
    have hp : 0 < 2 ^ m := Nat.two_pow_pos m
    rw [pow_succ] at h2
    have : x / 2 ^ m < 2 := by rw [Nat.div_lt_iff_lt_mul hp]; omega
    have : 1 ≤ x / 2 ^ m := by rw [Nat.le_div_iff_mul_le hp]; omega
    omega
  simp [hd]

/-- **The certificate axis inverts the Form R certificate** of a positive axis. -/
theorem certAxis_formRCert {a : ℕ} (ha : 1 ≤ a) (c : ℕ → Bool)
    (hc : ∀ k, 1 ≤ k → c k = MemoryTable.formRCertBit a (k - 1)) :
    certAxis (MemoryTable.formRCertShift a) c = a := by
  set m := MemoryTable.formRCertShift a with hm
  have hsz : Nat.size a = m + 1 := by
    have : 0 < Nat.size a := Nat.size_pos.mpr ha
    simp [hm, MemoryTable.formRCertShift]; omega
  have ha1 : a < 2 ^ (m + 1) := by rw [← hsz]; exact Nat.lt_size_self a
  have ha2 : 2 ^ m ≤ a := Nat.lt_size.mp (by omega)
  apply Nat.eq_of_testBit_eq
  intro k
  rcases Nat.lt_trichotomy k m with hk | hk | hk
  · rw [testBit_certAxis m c k hk, hc (m - k) (by omega)]
    unfold MemoryTable.formRCertBit
    rw [← hm, if_pos (by omega)]
    congr 1
    omega
  · subst hk
    rw [testBit_band (certAxis_ge _ c) (certAxis_lt _ c), testBit_band ha2 ha1]
  · have h1 : certAxis m c < 2 ^ k :=
      lt_of_lt_of_le (certAxis_lt m c) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : a < 2 ^ k := lt_of_lt_of_le ha1 (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

section Gen

open Nock.NockVMROM.Thm54.TraceGen
variable {K : Type} [Field K]

/-- `bfsAssign` changes only the stamps. -/
theorem mapNTree_skel_bfsAssign (u : NTree (GenComputeRow K)) :
    mapNTree GenComputeRow.skel (bfsAssign u) = mapNTree GenComputeRow.skel u := by
  have hne : [u] ≠ [] := List.cons_ne_nil _ _
  set v := mapNTree GenComputeRow.skel u
  have hbfs : bfsForest [v] = (bfsForest [u]).map (mapNTree GenComputeRow.skel) :=
    bfsForest_mapNTree _ [u]
  have hfo : foCol (bfsForest [v]) = foCol (bfsForest [u]) := by
    funext i
    unfold foCol
    rw [hbfs, List.getElem?_map]
    cases (bfsForest [u])[i - 1]? with
    | none => rfl
    | some w => cases w; simp [mapNTree]
  have hlen : (bfsForest [v]).length = (bfsForest [u]).length := by rw [hbfs, List.length_map]
  unfold bfsAssign
  rw [Nock.NockVMROM.Thm54.ReconTreeSize.mapNTree_buildTF]
  have hrec := exact_reconForest_bfsForest [v] (by simp) u.label.skel
  have h1 : reconForest 1 (foCol (bfsForest [v]))
      (fun i => ((bfsForest [v])[i - 1]?).map NTree.label |>.getD u.label.skel) (bfsForest [v]).length =
      [buildTF 1 (foCol (bfsForest [v]))
        (fun i => ((bfsForest [v])[i - 1]?).map NTree.label |>.getD u.label.skel) (bfsForest [v]).length 1] := by
    simp [reconForest, List.range'_succ, List.range'_zero]
  simp only [List.length_singleton] at hrec
  rw [h1] at hrec
  have hv : buildTF 1 (foCol (bfsForest [v]))
      (fun i => ((bfsForest [v])[i - 1]?).map NTree.label |>.getD u.label.skel) (bfsForest [v]).length 1 = v := by
    simpa using hrec
  conv => rhs; rw [← hv]
  rw [hfo, hlen]
  have hL : 1 ≤ (bfsForest [u]).length := by
    have := bfsForest_singleton_length_pos u; omega
  refine Nock.RedTeam.Batch1255.MemPkg.buildTF_congr 1 _ _ _ _ _ (fun _ _ _ => rfl) ?_ 1 le_rfl hL
  intro j hj1 hjL
  have hlt : j - 1 < (bfsRows u).length := by rw [bfsRows_length]; omega
  have hlt' : j - 1 < (bfsForest [u]).length := by omega
  rw [bfsLabelAt_skel u j hlt, hbfs, List.getElem?_map, List.getElem?_eq_getElem hlt']
  simp [bfsRows, mapNTree_label]

end Gen

theorem inTree_map {α β : Type*} (f : α → β) {u v : NTree α} (h : InTree u v) :
    InTree (mapNTree f u) (mapNTree f v) := by
  induction h with
  | here => exact InTree.here _
  | @sub c s t hs _ ih =>
    refine InTree.sub (s := mapNTree f s) ?_ ih
    cases c with
    | node a cs =>
      simp only [mapNTree, NTree.children] at hs ⊢
      exact List.mem_map.mpr ⟨s, hs, rfl⟩

theorem inTree_of_mem_bfs {α : Type*} {l : List (NTree α)} {v : NTree α}
    (h : v ∈ bfsForest l) : ∃ u ∈ l, InTree u v :=
  (mem_bfsForest l v).mp h

end Nock.RedTeam.Batch1255.Misc



set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch1255.Consumers

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.Framework
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.P8EventEv

noncomputable section

/-- Compute-only projection of a skeleton. -/
def cOnly (S : SemanticSkeleton) : SemanticSkeleton := ⟨S.computeTree, []⟩

theorem combinedSkeletonPairs_cOnly (K : Type) [Field K] (S : SemanticSkeleton) :
    EdgeComparisonCensus.combinedSkeletonPairs K S =
      EdgeComparisonCensus.combinedSkeletonPairs K (cOnly S) := rfl

theorem skeletonSizeWindowNouns_cOnly (S : SemanticSkeleton) :
    SizeWindowCounting.skeletonSizeWindowNouns S =
      SizeWindowCounting.skeletonSizeWindowNouns (cOnly S) := rfl

theorem requestTargets_cOnly (S : SemanticSkeleton) :
    PreSeedCensus.requestTargets S = PreSeedCensus.requestTargets (cOnly S) := rfl

theorem publicClaim_cOnly (S : SemanticSkeleton) : S.publicClaim = (cOnly S).publicClaim := rfl

theorem cOnly_congr {S T : SemanticSkeleton} (h : S.computeTree = T.computeTree) :
    cOnly S = cOnly T := by unfold cOnly; rw [h]

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

theorem guardedCensusEv_badSeeds_congr {S T : SemanticSkeleton} (Λ : ℕ)
    (h : S.computeTree = T.computeTree) :
    (guardedCensusEv K S Λ).badSeeds (K := K) = (guardedCensusEv K T Λ).badSeeds (K := K) := by
  unfold guardedCensusEv
  rw [combinedSkeletonPairs_cOnly K S, combinedSkeletonPairs_cOnly K T, cOnly_congr h]

theorem guardedSizeWindowFailure_congr {S T : SemanticSkeleton} (Λ : ℕ)
    (h : S.computeTree = T.computeTree) :
    guardedSizeWindowFailure (K := K) S Λ = guardedSizeWindowFailure (K := K) T Λ := by
  unfold guardedSizeWindowFailure guardedSizeWindowSeeds
  rw [skeletonSizeWindowNouns_cOnly S, skeletonSizeWindowNouns_cOnly T, cOnly_congr h]

section AnyPackage

variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])

theorem hp8Ev_of_computeTree_eq (c : OptimizedProductionChallengeTuple K F)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hSc : (builtSkeletonEv P Qc Qm).computeTree = P.strategy.skeleton.computeTree)
    (htopo : c.1 ∉ TemplateRawJointSoundness.specializedTopologyFailureEvent
      (builtStrategyEv P Qc Qm).verifier.raw c.2.2.2.lambda)
    (hax : c.1 ∉ envelopeAxisFailureEvent (builtStrategyEv P Qc Qm) c.2.2.2.lambda) :
    c.1 ∉ evFailureUnion (builtStrategyEv P Qc Qm) P.optimized.Λ c.2.2.2.lambda := by
  have h1 := (P.optimizedFailureEvent_good_components Qc Qm c hgood).1
  simp only [ProductionP8Containment.FailureUnion, Finset.mem_union, not_or] at h1
  obtain ⟨⟨⟨⟨hz0, hcol⟩, -⟩, -⟩, hsw⟩ := h1
  have hS' : (builtStrategyEv P Qc Qm).skeleton.computeTree = P.strategy.skeleton.computeTree := hSc
  refine Nock.RedTeam.Batch1250.not_mem_evFailureUnion_of_parts _ _ _ _ ?_ ?_ htopo hax ?_
  · intro h; exact hz0 ((mem_zeroSeedFailureEvent_iff _).2 h)
  · intro h
    apply hcol
    unfold collisionFailureEvent at h ⊢
    rw [mem_liftSeed_iff] at h ⊢
    have heq : (guardedCensusEv K P.strategy.skeleton P.optimized.Λ).badSeeds (K := K) =
        P.optimized.census.census.badSeeds (K := K) :=
      guardedCensusEv_badSeeds_eq P.optimized.census
    rw [guardedCensusEv_badSeeds_congr P.optimized.Λ hS', heq] at h
    exact h
  · intro h
    rw [guardedSizeWindowFailure_congr P.optimized.Λ hS'] at h
    exact hsw (guardedSizeWindowFailure_subset _ _ h)

theorem hpairEv_of_computeTree_eq (c : OptimizedProductionChallengeTuple K F)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hSc : (builtSkeletonEv P Qc Qm).computeTree = P.strategy.skeleton.computeTree) :
    c.1 ∉ reqPairEv P Qc Qm := by
  have h12 := (P.optimizedFailureEvent_good_components Qc Qm c hgood).2.2.2.2.2.2.2.2.2.2.2
  rw [Nock.RedTeam.Batch1250.reqPairEv_eq_pinned_of_targets P Qc Qm (by
    unfold builtRequestTargets
    rw [requestTargets_cOnly, requestTargets_cOnly P.strategy.skeleton, cOnly_congr hSc])]
  exact h12

theorem hrootEv_of_computeTree_eq (c : OptimizedProductionChallengeTuple K F)
    (hSc : (builtSkeletonEv P Qc Qm).computeTree = P.strategy.skeleton.computeTree) :
    c.1 ∉ rootResultEv P Qc Qm := by
  rw [Nock.RedTeam.Batch1250.rootResultEv_eq_empty_of_diag P Qc Qm (by
    rw [publicClaim_cOnly, cOnly_congr hSc, ← publicClaim_cOnly, P.strategy.publicClaim_eq]
    rfl)]
  simp

end AnyPackage
end
end Nock.RedTeam.Batch1255.Consumers

#print axioms Nock.RedTeam.Batch1255.Consumers.hp8Ev_of_computeTree_eq
#print axioms Nock.RedTeam.Batch1255.Consumers.hpairEv_of_computeTree_eq
#print axioms Nock.RedTeam.Batch1255.Consumers.hrootEv_of_computeTree_eq



set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace Nock.RedTeam.Batch1255.Gen

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.Framework
open Nock.Framework.Thm54
open Module
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch906
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.RedTeam.Batch1061 (genPkg gen_honest_accepted)

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

/-! ## §A  At any package -/

section Generated

variable {q Λ : ℕ}
    {z α : K} {hz : z ≠ 0} {htwo : (2 : K) ≠ 0} {a b c : K}
    {chal : ChallengeVector K} {hinp : chal.computeInputs = ⟨α, z, a, b, c⟩}
    {hmi : chal.memoryInputs = memInputs z}
    {Ksz : ℕ} {orbit : OrbitDomain K} {horb : 1 ≤ orbit.h}
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    {h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)}
    {hseed : SeedGood z t}
    {hcoins : ComputeCoinsGeneric z α a b c (airReorder t)}
    {hΛ : 1 ≤ Λ} {hconf : TraceConfined Λ (airReorder t)}
    {hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length}
    {hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h}
    {hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h}
    {B : ℕ} {hB : B ≤ orderOf α}
    {hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B}
    {hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz}
    {hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz}
    {hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q}
    {hq : 11 < q} {hchar : q = ringChar K}
    {haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t))}
    {hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds}
    {hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))}
    {hKszChar : Ksz < ringChar K}
    {hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h}
    {hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h}
    {hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K}





set_option quotPrecheck false in
set_option hygiene false in
local notation "GP" => genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef
  hinterCard hhon hprl hmore hord hordM hrows

set_option quotPrecheck false in
set_option hygiene false in
local notation "EG" => genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
  hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
  haxis hbad hout hKszChar hprogCap hmemCap hfirst

set_option quotPrecheck false in
set_option hygiene false in
local notation "IG" => inputsOfCarrier (EG) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n
  hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon

theorem compRows_eq
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64) :
    (GP).optimized.family.problem.cfg.compRows = (bfsForest [airReorder t]).length := by
  show (bfsForest [genComputeRows z α t]).length = _
  rw [genComputeRows, renderRows_eq_mapNTree, bfsForest_mapNTree_singleton, List.length_map,
    bfsForest_bfsAssign, List.length_map, List.length_range']

theorem bfsRows_genComputeRows (z α : K) (t : NTree (GenComputeRow K)) :
    bfsRows (genComputeRows z α t) =
      (List.range' 1 (bfsForest [airReorder t]).length).map
        (fun j => renderNode z α (bfsLabelAt (airReorder t) j)) := by
  unfold bfsRows
  rw [genComputeRows, renderRows_eq_mapNTree, bfsForest_mapNTree_singleton, List.map_map]
  have h := bfsAssign_bfsForest_labels (airReorder t)
  have : (bfsForest [bfsAssign (airReorder t)]).map (NTree.label ∘ mapNTree (renderNode z α)) =
      ((bfsForest [bfsAssign (airReorder t)]).map NTree.label).map (renderNode z α) := by
    rw [List.map_map]; congr 1; funext x; simp [Function.comp_def, mapNTree_label]
  rw [this, h, List.map_map]
  rfl

theorem pubState_eq
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64)
    (i : Fin (GP).optimized.family.problem.cfg.compRows)
    (hi : (i : ℕ) < (bfsRows (airReorder t)).length) :
    ((GP).optimized.family.problem.exec.computePubAt i).state =
      ((bfsRows (airReorder t))[(i : ℕ)]'hi).skel.state := by
  have hrows : (GP).optimized.family.problem.exec.computeRows =
      (bfsRows (genComputeRows z α t)).map (fun g => setRowCoins a b c g.row) :=
    genExactExecution_computeRows (F := F) chal Ksz orbit horb a b c _ _ hmempos hcomp hmem
  have hL : (i : ℕ) < (bfsForest [airReorder t]).length := by rwa [← bfsRows_length]
  unfold ExactExecution.computePubAt ExactExecution.computeRowAt
  simp only [List.get_eq_getElem, Fin.val_cast]
  simp only [hrows, bfsRows_genComputeRows, List.getElem_map, List.getElem_range']
  rw [setRowCoins_pub, renderNode_pub_state, bfsLabelAt_skel _ _ (by omega)]
  simp only [show 1 + 1 * (i : ℕ) - 1 = (i : ℕ) by omega]

theorem accAt_succ' (u : NTree (GenComputeRow K)) (i : ℕ) (hi : i < (bfsRows u).length) :
    accAt u (i + 1) = accAt u i + Nock.Framework.recordCount ((bfsRows u)[i]'hi).skel.state := by
  simp only [accAt, List.getElem?_eq_getElem hi]

theorem honestS_eq_accAt
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64) :
    ∀ i, i ≤ (GP).optimized.family.problem.cfg.compRows →
      OptimizedComputeFinalTrace.honestS (GP).optimized.family i = accAt (airReorder t) i := by
  intro i
  induction i with
  | zero => intro _; simp [OptimizedComputeFinalTrace.honestS, accAt]
  | succ m ih =>
    intro hm
    have hlt : m < (GP).optimized.family.problem.cfg.compRows := by omega
    have hcr := compRows_eq stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
    have hlt' : m < (bfsRows (airReorder t)).length := by rw [bfsRows_length, ← hcr]; exact hlt
    rw [Nock.RedTeam.Batch997.honestS_succ' (GP) m hlt, ih (by omega), accAt_succ' _ m hlt',
      Nock.RedTeam.Batch671.activeRequestRecords_length_eq_recordCount,
      pubState_eq stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 ⟨m, hlt⟩ hlt']

theorem accAt_le (u : NTree (GenComputeRow K)) : ∀ i, accAt u i ≤ 3 * i := by
  intro i
  induction i with
  | zero => simp [accAt]
  | succ m ih =>
    simp only [accAt]
    split
    · rename_i g _
      have := Nock.Framework.recordCount_le g.skel.state
      simp [Nock.NockVM.mem_record_arity] at this
      omega
    · omega

theorem bfs_fanout_air {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow K)}
    {result : Noun} (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (v : NTree (GenComputeRow K)) (hv : v ∈ bfsForest [airReorder t]) :
    v.children.length = ComputeTable.fanoutComp v.label.skel.state := by
  have hin : InTree (airReorder t) v := by
    obtain ⟨c, hc, hct⟩ := (mem_bfsForest [airReorder t] v).mp hv
    simp only [List.mem_singleton] at hc
    subst hc; exact hct
  exact airReorder_inTree_fanout (fun u hu => genComputeSkeleton_inTree_fanout h u hu) v hin

theorem treeOfTraces_eq
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64) :
    mapNTree (fun l : (ComputeTable.State × ComputeTable.DTcomp K) × ℕ => (l.1.1, l.2))
        (StrategyOfTracesR0AC2.c2TreeOfTraces (GP).optimized (canonicalComputeTrace (GP))
          StrategyOfTracesEv.coinFree) =
      mapNTree (fun g : GenComputeRow K => (g.skel.state, g.stamp.lnPrevExponent))
        (bfsAssign (airReorder t)) := by
  have hcr := compRows_eq stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  set L := (bfsForest [airReorder t]).length with hL
  have hL1 : 1 ≤ L := by have := bfsForest_singleton_length_pos (airReorder t); omega
  unfold StrategyOfTracesR0AC2.c2TreeOfTraces reconTree
  rw [Nock.NockVMROM.Thm54.ReconTreeSize.mapNTree_buildT, Nock.RedTeam.Batch1255.Tree.buildT_eq_buildTF_one]
  unfold bfsAssign
  rw [Nock.NockVMROM.Thm54.ReconTreeSize.mapNTree_buildTF]
  rw [congrArg (fun hh => buildTF 1 _ _ hh 1) hcr]
  refine Nock.RedTeam.Batch1255.MemPkg.buildTF_congr 1 _ _ _ _ L ?_ ?_ 1 le_rfl hL1
  · intro j hj1 hjL
    have hjN : j - 1 < (GP).optimized.family.problem.cfg.compRows := by omega
    have hjr : j - 1 < (bfsRows (airReorder t)).length := by rw [bfsRows_length]; omega
    have hst := Nock.RedTeam.Batch1255.Comp.lblC_state_canon (GP) StrategyOfTracesEv.coinFree ⟨j - 1, hjN⟩
    simp only [show j - 1 + 1 = j by omega] at hst
    unfold StrategyOfTracesLift.foC
    rw [hst, pubState_eq stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 ⟨j - 1, hjN⟩ hjr]
    unfold foCol
    have hjb : j - 1 < (bfsForest [airReorder t]).length := by omega
    rw [List.getElem?_eq_getElem hjb]
    simp only [Option.map_some, Option.getD_some]
    rw [bfs_fanout_air h _ (List.getElem_mem hjb)]
    simp [bfsRows]
  · intro j hj1 hjL
    have hjN : j - 1 < (GP).optimized.family.problem.cfg.compRows := by omega
    have hjr : j - 1 < (bfsRows (airReorder t)).length := by rw [bfsRows_length]; omega
    have hst := Nock.RedTeam.Batch1255.Comp.lblC_state_canon (GP) StrategyOfTracesEv.coinFree ⟨j - 1, hjN⟩
    simp only [show j - 1 + 1 = j by omega] at hst
    have hS := honestS_eq_accAt stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 (j - 1) hjN.le
    have hSlt : OptimizedComputeFinalTrace.honestS (GP).optimized.family (j - 1) < ringChar K := by
      rw [hS]
      have := accAt_le (airReorder t) (j - 1)
      have h3 := hrows.1
      have : (j - 1) < (GP).optimized.family.problem.cfg.compRows := hjN
      have hc : (GP).optimized.family.problem.cfg.compRows =
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
            orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
            haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows := rfl
      omega
    have hSAt := Nock.RedTeam.Batch1255.Comp.c2SAt_canon (GP) StrategyOfTracesEv.coinFree ⟨j - 1, hjN⟩ hSlt
    simp only [StrategyOfTracesR0AC2.lblCS, dif_pos hjN, hst, hSAt, hS,
      pubState_eq stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 ⟨j - 1, hjN⟩ hjr, bfsLabelAt_skel _ _ hjr, bfsLabelAt_stamp _ _ hjr,
      stampOfAcc_lnPrevExponent]

local notation "MF" => genMemoryForest z α chal.lam (memInputs z) t

theorem execMem_bfs
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64) :
    bfsForest (GP).optimized.family.problem.exec.memoryForest =
      (bfsForest (MF)).map (mapNTree (fun g : GenMemoryRow K =>
        SemanticTimestampStrategy.MemoryRowTemplate.encodeRow chal.lam g.row)) := by
  show bfsForest (((MF).map (mapNTree GenMemoryRow.row)).map
    (mapNTree (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow chal.lam))) = _
  rw [bfsForest_mapNTree, bfsForest_mapNTree, List.map_map]
  congr 1
  funext x
  simp [Function.comp_def, Nock.NockVMROM.Thm54.ReconTreeSize.mapNTree_comp]

theorem genMem_LC
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64) :
    ∀ g ∈ bfsForest (MF), Nock.RedTeam.Batch1255.Mem.AllLC (encC z) (mapNTree Nock.RedTeam.Batch1255.Mem.proj g) := by
  intro g hg
  obtain ⟨u, hu, hug⟩ := Nock.RedTeam.Batch1255.Misc.inTree_of_mem_bfs hg
  have hrec : ∀ n, InTree (bfsAssign (airReorder t)) n → ∀ r ∈ extractNodeReqs n.label,
      Nock.RedTeam.Batch1255.Mem.RecOK r := fun n hn r hr =>
    bfsAssign_extract_requests_slot (airReorder t)
      (treeRequestsWF_airReorder (genComputeSkeleton_tree_requests_wf h)) n hn r hr
  have hall := Nock.RedTeam.Batch1255.Mem.genMemoryForest_LC (lmb := chal.lam) z α (memInputs z) t hrec u hu
  exact fun v hv => hall v (InTree_trans (Nock.RedTeam.Batch1255.Misc.inTree_map Nock.RedTeam.Batch1255.Mem.proj hug) hv)

theorem genMem_bound
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64) :
    ∀ g ∈ bfsForest (MF), ∀ w, InTree (mapNTree Nock.RedTeam.Batch1255.Mem.proj g) w → ∀ a,
      w.label.1.state = .halt → w.label.1.parent = .atom a → a < ringChar K := by
  intro g hg w hw a _ hpa
  obtain ⟨u, hu, hug⟩ := Nock.RedTeam.Batch1255.Misc.inTree_of_mem_bfs hg
  obtain ⟨w0, hw0, rfl⟩ := inTree_mapNTree Nock.RedTeam.Batch1255.Mem.proj g w hw
  have hb' := hb.memoryTrees (mapNTree GenMemoryRow.skel u) (List.mem_map.mpr ⟨u, hu, rfl⟩)
    (mapNTree GenMemoryRow.skel w0) (Nock.RedTeam.Batch1255.Misc.inTree_map _ (InTree_trans hug hw0))
  simp only [mapNTree_label] at hb' hpa
  have := hb'.1
  simp only [Nock.RedTeam.Batch1255.Mem.proj] at hpa
  rw [hpa] at this
  simpa [hchar] using this

theorem encodeRow_st_pt (lmb : K) (row : MemoryTable.MState × MemoryTable.DTmem K) :
    (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb row).2.2.st = row.2.2.st ∧
      (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb row).2.2.pt = row.2.2.pt := by
  unfold SemanticTimestampStrategy.MemoryRowTemplate.encodeRow
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem execMem_topo
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64) :
    ∀ x ∈ bfsForest (GP).optimized.family.problem.exec.memoryForest,
      MemoryTable.fanoutMem x.label.2.2.st = x.children.length := by
  intro x hx
  rw [execMem_bfs stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64] at hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
  have hlc := genMem_LC stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 g hg _ (InTree.here _)
  obtain ⟨_, h2, hs⟩ := hlc
  obtain ⟨a, cs⟩ := g
  simp only [mapNTree, mapNTree_label, NTree.children, NTree.label, List.length_map,
    Nock.RedTeam.Batch1255.Mem.proj] at h2 hs ⊢
  rw [(encodeRow_st_pt chal.lam a.row).1, h2]
  cases hst : a.skel.state <;> rw [hst] at hs <;> simp only [Nock.RedTeam.Batch1255.Mem.LCs, NTree.children] at hs
  · obtain ⟨x, y, hxy, -⟩ := hs
    rw [List.map_eq_cons_iff] at hxy
    obtain ⟨x0, rest, rfl, -, hrest⟩ := hxy
    rw [List.map_eq_cons_iff] at hrest
    obtain ⟨y0, rest', rfl, -, hr'⟩ := hrest
    simp at hr'; subst hr'; simp [MemoryTable.fanoutMem]
  · obtain ⟨hnil, -⟩ := hs
    simp at hnil; subst hnil; simp [MemoryTable.fanoutMem]
  · obtain ⟨x, hx, -⟩ := hs
    rw [List.map_eq_cons_iff] at hx
    obtain ⟨x0, rest, rfl, -, hr'⟩ := hx
    simp at hr'; subst hr'; simp [MemoryTable.fanoutMem]
  · obtain ⟨x, hx, -⟩ := hs
    rw [List.map_eq_cons_iff] at hx
    obtain ⟨x0, rest, rfl, -, hr'⟩ := hx
    simp at hr'; subst hr'; simp [MemoryTable.fanoutMem]

theorem decode_row
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64)
    (hM : 0 < (GP).optimized.family.problem.cfg.memRows)
    (i : ℕ) (g : NTree (GenMemoryRow K)) (hg : (bfsForest (MF))[i]? = some g) :
    PreSeedCensus.preZNounOfEnvs K (ringChar K) (GP).optimized.family.problem.cfg.kMem
        (Nock.RedTeam.Batch1255.MemPkg.envsM (GP) StrategyOfTracesEv.coinFree) hM (i + 1) = g.label.skel.parent := by
  have ht : (bfsForest (GP).optimized.family.problem.exec.memoryForest)[i + 1 - 1]? =
      some (mapNTree (fun g : GenMemoryRow K =>
        SemanticTimestampStrategy.MemoryRowTemplate.encodeRow chal.lam g.row) g) := by
    rw [execMem_bfs stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64, show i + 1 - 1 = i by omega, List.getElem?_map, hg]; rfl
  rw [Nock.RedTeam.Batch1255.MemPkg.preZNoun_canon (GP) StrategyOfTracesEv.coinFree hM (ringChar K)
    (execMem_topo stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64) (i + 1) _ (by omega) ht]
  have hfun : (fun x : GenMemoryRow K => Nock.RedTeam.Batch1255.MemPkg.prjE (F := F)
      (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow chal.lam x.row)) =
      (fun x => Nock.RedTeam.Batch1255.Mem.preD (F := F) (Nock.RedTeam.Batch1255.Mem.proj x)) := by
    funext x
    obtain ⟨h1, h2⟩ := encodeRow_st_pt chal.lam x.row
    simp only [Nock.RedTeam.Batch1255.MemPkg.prjE, Nock.RedTeam.Batch1255.Mem.preD, Nock.RedTeam.Batch1255.Mem.proj, h1, h2, Nock.RedTeam.Batch1255.Mem.honestAtomOf_eq]
  rw [Nock.NockVMROM.Thm54.ReconTreeSize.mapNTree_comp, hfun,
    ← Nock.NockVMROM.Thm54.ReconTreeSize.mapNTree_comp]
  have hmem : g ∈ bfsForest (MF) := List.mem_of_getElem? hg
  have := Nock.RedTeam.Batch1255.Mem.decode_of_LC (F := F) z (ringChar K) le_rfl _ (genMem_LC stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 g hmem)
    (genMem_bound stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 g hmem)
  simpa [mapNTree_label, Nock.RedTeam.Batch1255.Mem.proj] using this

theorem preState_row
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64)
    (hM : 0 < (GP).optimized.family.problem.cfg.memRows)
    (i : ℕ) (hi : i < (GP).optimized.family.problem.cfg.memRows) (g : NTree (GenMemoryRow K))
    (hg : (bfsForest (MF))[i]? = some g) :
    (PreSeedCensus.preLblOfEnvs (Nock.RedTeam.Batch1255.MemPkg.envsM (GP) StrategyOfTracesEv.coinFree) hM (i + 1)).1 =
      g.label.skel.state := by
  unfold PreSeedCensus.preLblOfEnvs
  rw [dif_pos (by omega)]
  simp only
  rw [Nock.RedTeam.Batch1255.MemPkg.preState_canon]
  have hlt : i < (bfsForest (GP).optimized.family.problem.exec.memoryForest).length := by
    rw [execMem_bfs stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64, List.length_map]; exact (List.getElem?_eq_some_iff.mp hg).1
  rw [Nock.RedTeam.Batch1255.MemPkg.memoryPubAt_bfs (GP) ⟨i + 1 - 1, by omega⟩ (by simpa using hlt)]
  have hex := execMem_bfs stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hgi : (bfsForest (GP).optimized.family.problem.exec.memoryForest)[i]? =
      some (mapNTree (fun g : GenMemoryRow K =>
        SemanticTimestampStrategy.MemoryRowTemplate.encodeRow chal.lam g.row) g) := by
    rw [hex, List.getElem?_map, hg]; rfl
  have hgi' := (List.getElem?_eq_some_iff.mp hgi).2
  simp only [show i + 1 - 1 = i by omega]
  rw [hgi', mapNTree_label, (encodeRow_st_pt chal.lam g.label.row).1]
  have hlc := genMem_LC stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 g (List.mem_of_getElem? hg) _ (InTree.here _)
  simpa [mapNTree_label, Nock.RedTeam.Batch1255.Mem.proj] using hlc.2.1

theorem pubSt_row
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64)
    (i : ℕ) (hi : i < (GP).optimized.family.problem.cfg.memRows) (g : NTree (GenMemoryRow K))
    (hg : (bfsForest (MF))[i]? = some g) :
    ((GP).optimized.family.problem.exec.memoryPubAt ⟨i, hi⟩).st = g.label.skel.state := by
  have hlt : i < (bfsForest (GP).optimized.family.problem.exec.memoryForest).length := by
    rw [execMem_bfs stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64, List.length_map]; exact (List.getElem?_eq_some_iff.mp hg).1
  rw [Nock.RedTeam.Batch1255.MemPkg.memoryPubAt_bfs (GP) ⟨i, hi⟩ hlt]
  have hgi : (bfsForest (GP).optimized.family.problem.exec.memoryForest)[i]? =
      some (mapNTree (fun g : GenMemoryRow K =>
        SemanticTimestampStrategy.MemoryRowTemplate.encodeRow chal.lam g.row) g) := by
    rw [execMem_bfs stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64, List.getElem?_map, hg]; rfl
  have hgi' := (List.getElem?_eq_some_iff.mp hgi).2
  simp only
  rw [hgi', mapNTree_label, (encodeRow_st_pt chal.lam g.label.row).1]
  have hlc := genMem_LC stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 g (List.mem_of_getElem? hg) _ (InTree.here _)
  simpa [mapNTree_label, Nock.RedTeam.Batch1255.Mem.proj] using hlc.2.1

theorem reqIdx_row
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64)
    (hM : 0 < (GP).optimized.family.problem.cfg.memRows)
    (i : ℕ) (hi : i < (GP).optimized.family.problem.cfg.memRows) (g : NTree (GenMemoryRow K))
    (hg : (bfsForest (MF))[i]? = some g)
    (hlive : g.label.skel.state = .read_root ∨ g.label.skel.state = .verify_child) :
    RecordCarrier.natLift
        (PreSeedCensus.preReqIdxOfEnvs (Nock.RedTeam.Batch1255.MemPkg.envsM (GP) StrategyOfTracesEv.coinFree) hM (i + 1)) =
      g.label.stamp.recordExponent := by
  rw [Nock.RedTeam.Batch1255.MemPkg.preReqIdx_canon (GP) StrategyOfTracesEv.coinFree hM (i + 1) (by omega) (by omega)]
  simp only [show i + 1 - 1 = i by omega]
  unfold OptimizedMemorySemanticRealization.honestReqIdx
  have hzc : chal.z = z := by
    have := congrArg ComputeTable.Inputs.z hinp
    simpa [ChallengeVector.computeInputs] using this
  have hst := pubSt_row stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 i hi g hg
  have hlive' : ((GP).optimized.family.problem.exec.memoryPubAt ⟨i, hi⟩).st = .read_root ∨
      ((GP).optimized.family.problem.exec.memoryPubAt ⟨i, hi⟩).st = .verify_child := by
    rw [hst]; exact hlive
  have hlen : i < (genTimestampSkeleton F (airReorder t)
      (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))
      (genComputeSkeleton_memForest_stampsWellFormed z α h)).memoryRows.length := by
    rw [genTimestampSkeleton_memoryRows, ← genMemoryStamps_threadGenForest (memInputs z) 0]
    unfold genMemoryStamps
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hg).1
  have hRE := GenRecordExponentBridge.generated_reqIdxNat_eq_recordExponent
    (GP).optimized.sampled z α chal hzc Ksz orbit horb a b c h hmempos hcomp hmem
    (horb_of_window hB hwin) rfl rfl ⟨i, hi⟩ hlen hlive'
  have hstamp : ((genTimestampSkeleton F (airReorder t)
      (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))
      (genComputeSkeleton_memForest_stampsWellFormed z α h)).memoryRows[i]'hlen) =
      g.label.stamp := by
    have e1 : (genTimestampSkeleton F (airReorder t)
        (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))
        (genComputeSkeleton_memForest_stampsWellFormed z α h)).memoryRows =
        genMemoryStamps (MF) := by
      rw [genTimestampSkeleton_memoryRows]; unfold genMemoryForest
      rw [genMemoryStamps_threadGenForest]
    have := congrArg (fun l => l[i]?) e1
    rw [List.getElem?_eq_getElem hlen] at this
    unfold genMemoryStamps at this
    rw [List.getElem?_map, hg] at this
    simpa using this
  rw [hRE, hstamp]
  apply RecordCarrier.natLift_natCast
  -- the exponent is below the characteristic
  have hmemS : g.label.stamp ∈ genMemoryStamps
      (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t))) := by
    rw [← genMemoryStamps_threadGenForest (memInputs z) 0]
    exact List.mem_map.mpr ⟨g, List.mem_of_getElem? hg, rfl⟩
  have hle := genMemForestFromTree_stamp_exp_le_totalRecordCount (encC z) z α (airReorder t) hmemS
  rw [← accAt_len_eq_totalRecordCount] at hle
  have h3 := accAt_le (airReorder t) (bfsRows (airReorder t)).length
  have hcr := compRows_eq stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hr := hrows.1
  have hc : (GP).optimized.family.problem.cfg.compRows =
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows := rfl
  rw [bfsRows_length] at h3
  rw [Algebra.ringChar_eq F K]
  omega

theorem memRows_eq
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64) :
    (GP).optimized.family.problem.cfg.memRows = (bfsForest (MF)).length := rfl

/-- The served lookup at the canonical memory trace is the skeleton's request target. -/
theorem sv_eq
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64) (e : ℕ)
    (hex : ∃ (i : ℕ) (g : NTree (GenMemoryRow K)), (bfsForest (MF))[i]? = some g ∧
      g.label.skel.state = MemoryTable.MState.verify_child ∧
      g.label.stamp.recordExponent = e) :
    StrategyOfTracesR0AC2.c2ServedOf (GP).optimized (canonicalMemoryTrace (GP))
        StrategyOfTracesEv.coinFree .verify_child e =
      PreSeedCensus.requestTargets (genComputeSemanticSkeleton (bfsAssign (airReorder t)))
        .verify_child e := by
  have hM : 0 < (GP).optimized.family.problem.cfg.memRows :=
    (GP).optimized.family.problem.cfg.memRows_pos
  have hRT : PreSeedCensus.requestTargets (genSemanticSkeleton (bfsAssign (airReorder t)) (MF)) =
      PreSeedCensus.requestTargets (genComputeSemanticSkeleton (bfsAssign (airReorder t))) :=
    requestTargets_congr (computeSkeletonRows_genSemantic _ _)
  have KC : ∀ j ∈ PreZComputeCore.Served.servedRowsOfEnvs
      (Nock.RedTeam.Batch1255.MemPkg.envsM (GP) StrategyOfTracesEv.coinFree) hM .verify_child e,
      PreSeedCensus.preZNounOfEnvs K (ringChar K) (GP).optimized.family.problem.cfg.kMem
        (Nock.RedTeam.Batch1255.MemPkg.envsM (GP) StrategyOfTracesEv.coinFree) hM j =
      PreSeedCensus.requestTargets (genComputeSemanticSkeleton (bfsAssign (airReorder t)))
        .verify_child e := by
    intro j hj
    rw [PreZComputeCore.Served.servedRowsOfEnvs, List.mem_filter, List.mem_range'] at hj
    obtain ⟨⟨k, hk, rfl⟩, hcond⟩ := hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    obtain ⟨hst, hidx⟩ := hcond
    have hkM : k < (bfsForest (MF)).length := by rw [← memRows_eq stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64]; omega
    have hg : (bfsForest (MF))[k]? = some ((bfsForest (MF))[k]'hkM) :=
      List.getElem?_eq_getElem hkM
    rw [show 1 + 1 * k = k + 1 by omega] at hst hidx ⊢
    have hs1 := preState_row stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 hM k (by omega) _ hg
    rw [hs1] at hst
    have hr1 := reqIdx_row stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 hM k (by omega) _ hg (Or.inr hst)
    rw [hr1] at hidx
    rw [decode_row stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 hM k _ hg, ← hRT, ← hidx, ← hst]
    exact (genMemoryForest_requestTargets z α chal.lam (memInputs z) h _
      (List.getElem_mem hkM) (Or.inr hst)).symm
  obtain ⟨i, g, hg, hgs, hge⟩ := hex
  have hiM : i < (bfsForest (MF)).length := (List.getElem?_eq_some_iff.mp hg).1
  have hmem : i + 1 ∈ PreZComputeCore.Served.servedRowsOfEnvs
      (Nock.RedTeam.Batch1255.MemPkg.envsM (GP) StrategyOfTracesEv.coinFree) hM .verify_child e := by
    rw [PreZComputeCore.Served.servedRowsOfEnvs, List.mem_filter, List.mem_range']
    refine ⟨⟨i, by rw [memRows_eq stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64]; exact hiM, by omega⟩, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · rw [preState_row stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 hM i (by rw [memRows_eq stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64]; exact hiM) g hg, hgs]
    · rw [reqIdx_row stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 hM i (by rw [memRows_eq stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64]; exact hiM) g hg (Or.inr hgs), hge]
  show PreZComputeCore.Served.servedNounOfEnvs K (ringChar K) (GP).optimized.family.problem.cfg.kMem
    (Nock.RedTeam.Batch1255.MemPkg.envsM (GP) StrategyOfTracesEv.coinFree) hM .verify_child e = _
  unfold PreZComputeCore.Served.servedNounOfEnvs
  split
  · rename_i hnil; rw [hnil] at hmem; simp at hmem
  · rename_i j rest hcons
    exact KC j (by rw [hcons]; simp)

theorem stampOfAcc_state' (st : ComputeTable.State) (acc : ℕ) : (stampOfAcc st acc).state = st := by
  cases st <;> rfl

theorem stampOfAcc_recExp (st : ComputeTable.State) (acc k : ℕ) (h3 : k < 3)
    (hk : k < Nock.Framework.recordCount st) :
    (stampOfAcc st acc).recordExponent ⟨k, h3⟩ = acc + k + 1 := by
  cases st <;> simp [stampOfAcc, Nock.Framework.recordCount] at hk ⊢ <;>
    first | omega | (split_ifs <;> omega)

theorem label_of_inTree_bfsAssign (u : NTree (GenComputeRow K)) (v : NTree (GenComputeRow K))
    (hv : InTree (bfsAssign u) v) :
    ∃ j, 1 ≤ j ∧ j ≤ (bfsForest [u]).length ∧ ∃ hj : j - 1 < (bfsRows u).length,
      v.label = bfsLabelAt u j ∧ v.label.skel = ((bfsRows u)[j - 1]'hj).skel ∧
      v.label.stamp = stampOfAcc ((bfsRows u)[j - 1]'hj).skel.state (accAt u (j - 1)) := by
  have hb : v ∈ bfsForest [bfsAssign u] := (mem_bfsForest _ _).mpr ⟨_, List.mem_singleton_self _, hv⟩
  have hl : v.label ∈ (bfsForest [bfsAssign u]).map NTree.label := List.mem_map.mpr ⟨v, hb, rfl⟩
  rw [bfsAssign_bfsForest_labels] at hl
  obtain ⟨j, hj, hjv⟩ := List.mem_map.mp hl
  obtain ⟨k, hk, rfl⟩ := List.mem_range'.mp hj
  have hj' : 1 + 1 * k - 1 < (bfsRows u).length := by rw [bfsRows_length]; omega
  refine ⟨1 + 1 * k, by omega, by omega, hj', hjv.symm, ?_, ?_⟩
  · rw [← hjv, bfsLabelAt_skel u _ hj']
  · rw [← hjv, bfsLabelAt_stamp u _ hj']

theorem verify_exists
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64) (v : NTree (GenComputeRow K)) (hv : InTree (bfsAssign (airReorder t)) v) (k : ℕ)
    (hk : k < Nock.Framework.recordCount v.label.skel.state) :
    ∃ (i : ℕ) (g : NTree (GenMemoryRow K)), (bfsForest (MF))[i]? = some g ∧
      g.label.skel.state = MemoryTable.MState.verify_child ∧
      g.label.stamp.recordExponent = v.label.stamp.lnPrevExponent + k + 1 := by
  have h3 : k < 3 := lt_of_lt_of_le hk (Nock.Framework.recordCount_le _)
  have hmatch := genComputeSkeleton_air_requestsMatch h v hv
  obtain ⟨hk', hreq⟩ := extractNodeReqs_getElem_skel v.label hmatch k h3 hk
  have hr : (extractNodeReqs v.label)[k] ∈ extractNodeReqs v.label := List.getElem_mem hk'
  obtain ⟨j, -, -, hj, -, hsk, hstp⟩ := label_of_inTree_bfsAssign (airReorder t) v hv
  have hexp : ((extractNodeReqs v.label)[k]).recordExp = v.label.stamp.lnPrevExponent + k + 1 := by
    rw [hreq]
    show getRecordExp v.label.stamp k = _
    unfold getRecordExp
    rw [dif_pos h3, hstp, stampOfAcc_recExp _ _ k h3 (by rw [← hsk]; exact hk),
      stampOfAcc_lnPrevExponent]
  obtain ⟨u', hu', w, hw, hws, hwe⟩ :=
    Nock.RedTeam.Batch1255.Mem.fromTree_has (lmb := chal.lam) (encC z) z α (bfsAssign (airReorder t)) v hv _ hr
  have hwb : w ∈ bfsForest (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t))) :=
    (mem_bfsForest _ _).mpr ⟨u', hu', hw⟩
  obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.mp hwb
  let f : GenMemoryRow K → MemoryTable.MState × ℕ := fun g => (g.skel.state, g.stamp.recordExponent)
  have hmap := Nock.RedTeam.Batch1255.Mem.thread_map (memInputs z) f (fun _ _ _ => rfl) 0
    (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))
  have hb := congrArg bfsForest hmap
  rw [bfsForest_mapNTree, bfsForest_mapNTree] at hb
  have hbi := congrArg (fun l => l[i]?) hb
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, hiw] at hbi
  have hMF : genMemoryForest z α chal.lam (memInputs z) t = threadGenForest (memInputs z) 0
      (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t))) := rfl
  rw [hMF]
  have hiM : i < (bfsForest (threadGenForest (memInputs z) 0
      (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t))))).length := by
    have := congrArg List.length hb
    simp only [List.length_map] at this
    omega
  rw [List.getElem?_eq_getElem hiM] at hbi
  simp only [Option.map_some, Option.some.injEq] at hbi
  have hl := congrArg NTree.label hbi
  simp only [mapNTree_label, f, Prod.mk.injEq] at hl
  exact ⟨i, _, List.getElem?_eq_getElem hiM, hl.1.trans hws, hl.2.trans (hwe.trans hexp)⟩

/-- **The skeleton's request target at a row's request exponent is the row's record child.** -/
theorem requestTargets_row (u : NTree (GenComputeRow K)) (v : NTree (GenComputeRow K))
    (hv : InTree (bfsAssign u) v) (k : ℕ) (h3 : k < 3)
    (hk : k < Nock.Framework.recordCount v.label.skel.state) :
    PreSeedCensus.requestTargets (genComputeSemanticSkeleton (bfsAssign u)) .verify_child
        (v.label.stamp.lnPrevExponent + k + 1) =
      (v.label.skel.memoryRecord ⟨k, h3⟩ hk).child := by
  set S0 := genComputeSemanticSkeleton (bfsAssign u) with hS0
  have hnb : v ∈ bfsForest [bfsAssign u] := (mem_bfsForest _ _).mpr ⟨_, List.mem_singleton_self _, hv⟩
  obtain ⟨j, hj, hjn⟩ := List.mem_iff_getElem.mp hnb
  have hrows : computeSkeletonRows S0 = (bfsForest [bfsAssign u]).map (fun n => n.label.skel) :=
    computeSkeletonRows_genCompute _
  have hjr : j < (computeSkeletonRows S0).length := by rw [hrows]; simpa using hj
  have hstamps : bfsStamps (bfsAssign u) = (bfsForest [bfsAssign u]).map (fun n => n.label.stamp) :=
    rfl
  have hjs : j < (bfsStamps (bfsAssign u)).length := by rw [hstamps]; simpa using hj
  have hrow : (computeSkeletonRows S0)[j]'hjr = v.label.skel := by
    simp only [hrows, List.getElem_map, hjn]
  have hstamp : (bfsStamps (bfsAssign u))[j]'hjs = v.label.stamp := by
    simp only [hstamps, List.getElem_map, hjn]
  have hkr : k < Nock.Framework.recordCount ((computeSkeletonRows S0)[j]'hjr).state := by
    rw [hrow]; exact hk
  have hslot := requestList_getElem_slot S0 (bfsStamps (bfsAssign u))
    (bfsAssign_computeTopology u) (bfsAssign_startsAtZero u) (bfsAssign_computeLineChain u)
    (fun s hs => bfsAssign_computeLineAdvance u hs) j hjr k hkr
  have hslot' : (PreSeedCensus.requestList S0)[v.label.stamp.lnPrevExponent + k]? =
      some (v.label.skel.memoryRecord ⟨k, h3⟩ hk) := by
    have := hslot
    simp only [hstamp] at this
    rw [this]
    simp only [hrow]
  simp [PreSeedCensus.requestTargets, hslot']

theorem ax_row
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64) (v : NTree (GenComputeRow K)) (hv : InTree (bfsAssign (airReorder t)) v) (k : ℕ)
    (h3 : k < 3) (hk : k < Nock.Framework.recordCount v.label.skel.state)
    (hact : (k = 1 ∧ v.label.skel.state = .s0) ∨ (k = 2 ∧ v.label.skel.state = .s9)) :
    StrategyOfTracesR0AC2.c2AxOf (GP).optimized (canonicalComputeTrace (GP))
        StrategyOfTracesEv.coinFree (v.label.stamp.lnPrevExponent + k + 1) =
      (v.label.skel.memoryRecord ⟨k, h3⟩ hk).axis := by
  obtain ⟨j, hj1, hjL, hj, hlab, hsk, hstp⟩ := label_of_inTree_bfsAssign (airReorder t) v hv
  have hcr := compRows_eq stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hjN : j - 1 < (GP).optimized.family.problem.cfg.compRows := by omega
  set i : Fin (GP).optimized.family.problem.cfg.compRows := ⟨j - 1, hjN⟩ with hi
  have hS : v.label.stamp.lnPrevExponent = OptimizedComputeFinalTrace.honestS (GP).optimized.family i := by
    rw [hstp, stampOfAcc_lnPrevExponent, honestS_eq_accAt stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 (j - 1) hjN.le]
  have hpst : ((GP).optimized.family.problem.exec.computePubAt i).state = v.label.skel.state := by
    rw [pubState_eq stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 i hj, hsk]
  have hact' : OptimizedComputeFormRDenoms.slotActive (GP).optimized.family i ⟨k, h3⟩ = 1 := by
    rcases hact with ⟨rfl, hs⟩ | ⟨rfl, hs⟩
    · simp [OptimizedComputeFormRDenoms.slotActive, hpst, hs,
        OptimizedComputeSampledTrace.secondRequestMask]
    · simp [OptimizedComputeFormRDenoms.slotActive, hpst, hs,
        OptimizedComputeSampledTrace.thirdRequestMask]
  have G := Nock.RedTeam.Batch993.hgoodFill_generated (F := F) (K := K) stc hK pOrbit hcap n hreq
    hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have dc := Nock.RedTeam.Batch997.decoded_canon (GP) G.hax G.hwidth i ⟨k, h3⟩ hact'
  -- the record binding at this node
  have hOK := genComputeSkeleton_airReorder_computeNodes_OK (p := (t, result)) z α h
  have hnode := hOK _ (Nock.RedTeam.Batch1255.Misc.inTree_map _ (by
    rw [renderRows_eq_mapNTree]; exact Nock.RedTeam.Batch1255.Misc.inTree_map (renderNode z α) hv))
  obtain ⟨-, -, hbind, -⟩ := hnode
  simp only [mapNTree_label, GenComputeRow.node_skel, GenComputeRow.node_row,
    (renderNode_preserves_skel_stamp z α v.label).1] at hbind
  have hrec := hbind.2.2.2.2.2.2.2.2 ⟨k, h3⟩
  rw [dif_pos hk] at hrec
  have hax := hrec.2.2
  -- the pub at row `i` is the rendered row of `v`
  have hrows' : (GP).optimized.family.problem.exec.computeRows =
      (bfsRows (genComputeRows z α t)).map (fun g => setRowCoins a b c g.row) :=
    genExactExecution_computeRows (F := F) chal Ksz orbit horb a b c _ _ hmempos hcomp hmem
  have hpub : (GP).optimized.family.problem.exec.computePubAt i = (renderNode z α v.label).row.2.2.1 := by
    unfold ExactExecution.computePubAt ExactExecution.computeRowAt
    simp only [List.get_eq_getElem, Fin.val_cast]
    simp only [hrows', bfsRows_genComputeRows, List.getElem_map, List.getElem_range', hi]
    rw [setRowCoins_pub, hlab]
    simp only [show 1 + 1 * (j - 1) = j by omega]
  -- the slot record's axis
  have hslot : (OptimizedComputeFormRDenoms.slotRecord (GP).optimized.family i ⟨k, h3⟩).axis =
      (((v.label.skel.memoryRecord ⟨k, h3⟩ hk).axis : ℕ) : K) := by
    rw [← hax]
    rcases hact with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp [OptimizedComputeFormRDenoms.slotRecord, hpub, computeMemRec]
    · simp [OptimizedComputeFormRDenoms.slotRecord, hpub, computeMemRec]
  -- the axis is a positive residue
  have hmatch := genComputeSkeleton_air_requestsMatch h v hv
  obtain ⟨hk', hreq'⟩ := extractNodeReqs_getElem_skel v.label hmatch k h3 hk
  have hr : (extractNodeReqs v.label)[k] ∈ extractNodeReqs v.label := List.getElem_mem hk'
  have hlt : (v.label.skel.memoryRecord ⟨k, h3⟩ hk).axis < ringChar K := by
    have := hfirst v hv _ hr; rw [hreq'] at this; exact this
  have hpos : 1 ≤ (v.label.skel.memoryRecord ⟨k, h3⟩ hk).axis := by
    have hok := bfsAssign_extract_requests_slot (airReorder t)
      (treeRequestsWF_airReorder (genComputeSkeleton_tree_requests_wf h)) v hv _ hr
    have := Nock.RedTeam.Batch1255.Mem.pos_of_RecOK hok
    rw [hreq'] at this; exact this
  have hnat : MemoryTable.nockAxisOf
      (OptimizedComputeFormRDenoms.slotRecord (GP).optimized.family i ⟨k, h3⟩).axis =
      (v.label.skel.memoryRecord ⟨k, h3⟩ hk).axis := by
    rw [hslot]; exact MemoryTable.nockAxisOf_natCast hlt
  unfold StrategyOfTracesR0AC2.c2AxOf
  rw [StrategyOfTracesEv.certAxisOfEnvs_congr (envsC' := Nock.RedTeam.Batch997.envsC (GP))
    (fun i => by unfold StrategyOfTracesR0.computeEnvsR0; rfl)]
  rw [hS]
  unfold StrategyOfTracesR0.certAxisOfEnvs
  rw [dc.1]
  rw [← hnat]
  refine Nock.RedTeam.Batch1255.Misc.certAxis_formRCert (by rw [hnat]; exact hpos) _ ?_
  intro m hm
  exact dc.2 m hm

local notation "WT" => mapNTree (fun g : GenComputeRow K => (g.skel, g.stamp.lnPrevExponent))
  (bfsAssign (airReorder t))

theorem served_W
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64) :
    Nock.RedTeam.Batch1255.Join.Served
      (StrategyOfTracesR0AC2.c2ServedOf (GP).optimized (canonicalMemoryTrace (GP))
        StrategyOfTracesEv.coinFree)
      (StrategyOfTracesR0AC2.c2AxOf (GP).optimized (canonicalComputeTrace (GP))
        StrategyOfTracesEv.coinFree) (WT) := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := inTree_mapNTree _ _ w hw
  simp only [mapNTree_label]
  refine ⟨fun h1 hs => ?_, fun h2 hs => ?_⟩
  · have hsv := sv_eq stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 (v.label.stamp.lnPrevExponent + 1 + 1)
      (verify_exists stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 v hv 1 h1)
    have hrt := requestTargets_row (airReorder t) v hv 1 (by decide) h1
    have hax := ax_row stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 v hv 1 (by decide) h1 (Or.inl ⟨rfl, hs⟩)
    exact ⟨hsv.trans hrt, hax⟩
  · have hsv := sv_eq stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 (v.label.stamp.lnPrevExponent + 2 + 1)
      (verify_exists stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 v hv 2 h2)
    have hrt := requestTargets_row (airReorder t) v hv 2 (by decide) h2
    have hax := ax_row stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 v hv 2 (by decide) h2 (Or.inr ⟨rfl, hs⟩)
    exact ⟨hsv.trans hrt, hax⟩

theorem strategy_computeTree
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64) :
    (GP).strategy.skeleton.computeTree = mapNTree GenComputeRow.skel (bfsAssign (airReorder t)) := by
  show mapNTree ComputeNode.skel (genComputeNodes z α a b c t) = _
  unfold genComputeNodes
  rw [mapNTree_coinNode_skel, mapNTree_node_skel, genComputeRows, renderRows_skel]

/-- **The compute half of `hS`**: at the generated package's honest traces, the C2 compute tree
the event strategy rebuilds is the compiler's committed compute tree. -/
theorem builtComputeTree_genPkg
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64) :
    (builtSkeletonEv (GP) (honestQc (GP) (GP).honestTuple (QcH (GP)))
        (honestQm (GP) (GP).honestTuple (QmH (GP)))).computeTree =
      (GP).strategy.skeleton.computeTree := by
  rw [honestQc_QcH, honestQm_QmH]
  have hW := treeOfTraces_eq stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hXY : mapNTree (fun l : (ComputeTable.State × ComputeTable.DTcomp K) × ℕ => (l.1.1, l.2))
        (StrategyOfTracesR0AC2.c2TreeOfTraces (GP).optimized (canonicalComputeTrace (GP))
          StrategyOfTracesEv.coinFree) =
      mapNTree (fun l : SemanticStrategy.ComputeRowSkeleton × ℕ => (l.1.state, l.2)) (WT) := by
    rw [hW, Nock.NockVMROM.Thm54.ReconTreeSize.mapNTree_comp]
  have hsize : (StrategyOfTracesR0AC2.c2TreeOfTraces (GP).optimized (canonicalComputeTrace (GP))
      StrategyOfTracesEv.coinFree).size = (WT).size := by
    have := congrArg NTree.size hXY
    rwa [Nock.NockVMROM.Thm54.ReconTreeSize.size_mapNTree,
      Nock.NockVMROM.Thm54.ReconTreeSize.size_mapNTree] at this
  have hclaim : (GP).optimized.verifier.raw.claim = ⟨subject, formula, result⟩ :=
    genDataOfProgram_publicClaim (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
      orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
      hbad hout hKszChar hprogCap hmemCap hfirst
  have hfst : mapNTree Prod.fst (WT) = mapNTree GenComputeRow.skel (airReorder (t, result).1) := by
    rw [Nock.NockVMROM.Thm54.ReconTreeSize.mapNTree_comp]
    exact Nock.RedTeam.Batch1255.Misc.mapNTree_skel_bfsAssign (airReorder t)
  show StrategyOfTracesR0AC2.c2ComputeTree (GP).optimized (canonicalComputeTrace (GP))
    (canonicalMemoryTrace (GP)) StrategyOfTracesEv.coinFree = _
  unfold StrategyOfTracesR0AC2.c2ComputeTree StrategyOfTracesR0AC2.c2Join
  rw [Nock.RedTeam.Batch1255.Tree.c2JoinFuel_relabel _ _ (fun l : SemanticStrategy.ComputeRowSkeleton × ℕ => l.1.state)
    (fun l => l.2) _ _ _ _ _ hXY, hclaim, hsize]
  rw [Nock.RedTeam.Batch1255.Join.J_gen fuel h (WT) hfst (served_W stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64) (WT).size le_rfl,
    strategy_computeTree stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64, Nock.NockVMROM.Thm54.ReconTreeSize.mapNTree_comp]

end Generated
end
end Nock.RedTeam.Batch1255.Gen

#print axioms Nock.RedTeam.Batch1255.Gen.builtComputeTree_genPkg


#print axioms Nock.RedTeam.Batch1255.Join.J_gen
#print axioms Nock.RedTeam.Batch1255.Gen.treeOfTraces_eq
#print axioms Nock.RedTeam.Batch1255.Gen.served_W
#print axioms Nock.RedTeam.Batch1255.Gen.sv_eq
#print axioms Nock.RedTeam.Batch1255.Gen.ax_row
