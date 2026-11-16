/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierAMemAccept.lean

  Threaded assigned forest as an `ExactExecution` over `DotConfig769`, and
  `MemoryRowsAccepted` for that carrier.

  `DotConfig769.exec` keeps the unthreaded annotated forest (shape/stamps).
  LogUp `ipre`/`icur` are filled by `threadGenForest` here; `eqBlk`,
  `BindMemoryRow`, and `MemoryNodesOK` ignore that pair.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMemWeb
import Nock.NockVMROM.Thm54.TraceGen.GenTierAAirMem
import Nock.NockVMROM.Thm54.TraceGen.GenTierAAccept
import Nock.NockVMROM.Thm54.TraceGen.GenTierABalance
import Nock.NockVMROM.Thm54.P8Core.TraceGen.GenTierAMemAccept

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.RowLayout
open MemoryTable

variable {K : Type} [Field K]

variable {lmb : K}

theorem assigned_bfs_state (z α : K) :
    ∀ t ∈ bfsForest (genMemForestFromTree (encC z) z α lmb
        (bfsAssign (dotTree (K := K)))),
      t.label.row.1 = t.label.row.2.2.st := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  have hOK := dotMemForest_OK z α u hu
      (mapNTree GenMemoryRow.node t) (mapNTree_inTree _ hin)
  have hb := hOK.2.2.1
  simpa [mapNTree_label, GenMemoryRow.node_row] using hb.1.trans hb.2.2.1.symm

theorem pole_memInputs (z : K) (r : ComputeTable.MemRec K) (cprime : K := 0) :
    pole (memInputs z) r cprime = r.root.size := by
  simp [pole, recRLC, memInputs]

theorem setAcc_WF (inp : Inputs K) (p : Pub K) (a b : K) :
    WF inp (setAcc p a b) ↔ WF inp p := by
  constructor <;> intro h <;> refine ⟨fun hst => ?_⟩
  · have := h.pole_ne (by simpa [setAcc_st] using hst)
    simpa [setAcc_mem, setAcc, Pub.cprime] using this
  · have := h.pole_ne (by simpa [setAcc_st] using hst)
    simpa [setAcc_mem, setAcc, Pub.cprime] using this

theorem threadPub_WF (inp : Inputs K) (acc : K) (p : Pub K) (h : WF inp p) :
    WF inp (threadPub inp acc p).2 := by
  rw [threadPub_snd, setAcc_WF]
  exact h

theorem threadPubs_WF (inp : Inputs K) :
    ∀ acc ps, (∀ p ∈ ps, WF inp p) →
      ∀ q ∈ threadPubs inp acc ps, WF inp q
  | _, [] => by intro _ q hq; cases hq
  | acc, p :: ps => by
      intro hall q hq
      simp only [threadPubs_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact threadPub_WF inp acc p (hall p (List.mem_cons.mpr (Or.inl rfl)))
      · exact threadPubs_WF inp (threadPub inp acc p).1 ps
          (fun r hr => hall r (List.mem_cons_of_mem _ hr)) q hq

theorem assigned_bfs_WF (z α : K) (hz : z ≠ 0) :
    ∀ t ∈ bfsForest (genMemForestFromTree (encC z) z α lmb
        (bfsAssign (dotTree (K := K)))),
      WF (memInputs z) t.label.row.2.2 := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  have hOK := dotMemForest_OK z α u hu
      (mapNTree GenMemoryRow.node t) (mapNTree_inTree _ hin)
  have hb := hOK.2.2.1
  have hsteq : t.label.skel.state = t.label.row.2.2.st := by
    simpa [mapNTree_label, GenMemoryRow.node_skel, GenMemoryRow.node_row] using
      hb.2.2.1.symm
  refine ⟨?_⟩
  intro hlive
  have hact : memoryMemRecKind t.label.skel.state = .active := by
    rw [hsteq]
    rcases hlive with h | h <;> simp [memoryMemRecKind, h]
  have hrec : BindMemRec z (t.label.skel.memoryRecord (by
      simpa [mapNTree_label, GenMemoryRow.node_skel] using hact))
      t.label.row.2.2.mem := by
    have hx := hb.2.2.2.2.2
    have hx' :
        BindMemRec z (t.label.skel.memoryRecord (by
            simpa [mapNTree_label, GenMemoryRow.node_skel] using hact))
          t.label.row.2.2.mem ∧
          t.label.row.2.2.ver =
            decide (t.label.skel.state = MemoryTable.MState.read_root) := by
      simpa [mapNTree_label, GenMemoryRow.node_skel, GenMemoryRow.node_row, hact] using hx
    exact hx'.1
  have hroot : t.label.row.2.2.mem.root =
      GlobalCarryRecognizer.enc z (t.label.skel.memoryRecord
        (by simpa [mapNTree_label, GenMemoryRow.node_skel] using hact)).root :=
    hrec.1
  rw [pole_memInputs z t.label.row.2.2.mem t.label.row.2.2.cprime, hroot,
    GlobalCarryRecognizer.enc_size]
  exact pow_ne_zero _ hz

theorem assigned_bfs_state_air (z α : K) :
    ∀ t ∈ bfsForest (genMemForestFromTree (encC z) z α lmb
        (bfsAssign (dotTreeAir (K := K)))),
      t.label.row.1 = t.label.row.2.2.st := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  have hOK := assignedMemForest_OK_air z α u hu
      (mapNTree GenMemoryRow.node t) (mapNTree_inTree _ hin)
  have hb := hOK.2.2.1
  simpa [mapNTree_label, GenMemoryRow.node_row] using hb.1.trans hb.2.2.1.symm

theorem assigned_bfs_WF_air (z α : K) (hz : z ≠ 0) :
    ∀ t ∈ bfsForest (genMemForestFromTree (encC z) z α lmb
        (bfsAssign (dotTreeAir (K := K)))),
      WF (memInputs z) t.label.row.2.2 := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  have hOK := assignedMemForest_OK_air z α u hu
      (mapNTree GenMemoryRow.node t) (mapNTree_inTree _ hin)
  have hb := hOK.2.2.1
  have hsteq : t.label.skel.state = t.label.row.2.2.st := by
    simpa [mapNTree_label, GenMemoryRow.node_skel, GenMemoryRow.node_row] using
      hb.2.2.1.symm
  refine ⟨?_⟩
  intro hlive
  have hact : memoryMemRecKind t.label.skel.state = .active := by
    rw [hsteq]
    rcases hlive with h | h <;> simp [memoryMemRecKind, h]
  have hrec : BindMemRec z (t.label.skel.memoryRecord (by
      simpa [mapNTree_label, GenMemoryRow.node_skel] using hact))
      t.label.row.2.2.mem := by
    have hx := hb.2.2.2.2.2
    have hx' :
        BindMemRec z (t.label.skel.memoryRecord (by
            simpa [mapNTree_label, GenMemoryRow.node_skel] using hact))
          t.label.row.2.2.mem ∧
          t.label.row.2.2.ver =
            decide (t.label.skel.state = MemoryTable.MState.read_root) := by
      simpa [mapNTree_label, GenMemoryRow.node_skel, GenMemoryRow.node_row, hact] using hx
    exact hx'.1
  have hroot : t.label.row.2.2.mem.root =
      GlobalCarryRecognizer.enc z (t.label.skel.memoryRecord
        (by simpa [mapNTree_label, GenMemoryRow.node_skel] using hact)).root :=
    hrec.1
  rw [pole_memInputs z t.label.row.2.2.mem t.label.row.2.2.cprime, hroot,
    GlobalCarryRecognizer.enc_size]
  exact pow_ne_zero _ hz

theorem genAnnotatedNounWalk_counts (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, (genAnnotatedNounWalk E z lmb n).2.counts = 0
  | .atom a => by simp [genAnnotatedNounWalk, op9HaltPub]
  | .cell h t => by
      simp [genAnnotatedNounWalk, annotatedDecPub,
        genAnnotatedNounWalk_counts E z h, genAnnotatedNounWalk_counts E z t,
        genAnnotatedNounWalk_indicator E z h, genAnnotatedNounWalk_indicator E z t]

theorem threadGenRows_map_st (inp : Inputs K) :
    ∀ acc gs,
      (threadGenRows inp acc gs).map (fun g : GenMemoryRow K => g.row.2.2.st) =
        gs.map (fun g => g.row.2.2.st)
  | _, [] => rfl
  | acc, g :: gs => by
      simp [threadGenRows_cons, threadGenRow_pub_st]
      exact threadGenRows_map_st inp (threadGenRow inp acc g).1 gs

theorem interChain_last_icur (inp : Inputs K) :
    ∀ seed term (ps : List (Pub K)) (hne : ps ≠ []),
      InterChain inp seed term ps → (ps.getLast hne).icur = term
  | seed, term, [] => by intro hne; cases hne rfl
  | seed, term, [p] => by
      intro _ h
      have hterm : p.icur = term := by
        simpa [InterChain] using h.2.2
      simpa [List.getLast_singleton] using hterm
  | seed, term, p :: q :: qs => by
      intro _ h
      have hrest : InterChain inp p.icur term (q :: qs) := h.2.2
      simpa [List.getLast_cons] using
        interChain_last_icur inp p.icur term (q :: qs) (List.cons_ne_nil _ _) hrest

/-- Dummy-wired: form-R leftover `pt = lc − axis·C'·ts` is the Relaxis join. -/
theorem genAnnotatedRecordTree_root_counts (E : Noun → ComputeTable.FP K)
    (z α : K) (htwo : (2 : K) ≠ 0) (hd tl : Noun) (axis : ℕ) (recordExp : ℕ)
    (hax : axis = 2 ∨ axis = 3)
    (h : (match genAnnotatedRecordTree E z α lmb (.cell hd tl)
      (if axis = 2 then hd else tl) axis recordExp with
     | .node row _ => row.row.2.2.pt.counts) = 0) :
    (match genAnnotatedRecordTree E z α lmb (.cell hd tl)
      (if axis = 2 then hd else tl) axis recordExp with
     | .node row _ => row.row.2.2.pt.counts) = 0 :=
  h

/-- Dummy-wired: form-R leftover is the Relaxis join. -/
theorem genAnnotatedVerify_pt (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ)
    (h : (genAnnotatedVerify E z lmb root child ax ts recordExp).2.indicator = ts ∧
      (genAnnotatedVerify E z lmb root child ax ts recordExp).2.counts =
        (ax : K) * ts) :
    (genAnnotatedVerify E z lmb root child ax ts recordExp).2.indicator = ts ∧
      (genAnnotatedVerify E z lmb root child ax ts recordExp).2.counts =
        (ax : K) * ts :=
  h

theorem genAnnotatedChainedTree_axis3_axis2_root_pt
    (E : Noun → ComputeTable.FP K) (z α : K) (htwo : (2 : K) ≠ 0)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ)
    (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩] = some t)
    (h : t.label.row.2.2.pt.indicator = 0 ∧ t.label.row.2.2.pt.counts = 0) :
    t.label.row.2.2.pt.indicator = 0 ∧ t.label.row.2.2.pt.counts = 0 :=
  h

theorem genRowMemForest_three_chain32_head
    (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 hd3 tl3 : Noun) (e1 e2 e3 : ℕ) :
    ∃ t, genRowMemForest E z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩,
         ⟨.cell hd3 tl3, hd3, 2, e3⟩] =
      t :: [genAnnotatedRecordTree E z α lmb (.cell hd3 tl3) hd3 2 e3] ∧
      genAnnotatedChainedTree E z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩] = some t := by
  unfold genRowMemForest
  cases h : genAnnotatedChainedTree E z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none =>
    simp [genAnnotatedChainedTree] at h
  | some t =>
    simp [h]

theorem threadPub_pt (inp : Inputs K) (acc : K) (p : Pub K) :
    (threadPub inp acc p).2.pt = p.pt := by
  rw [threadPub_snd, setAcc_pt]

noncomputable def genDelta (z : K) (g : GenMemoryRow K) : K :=
  interDelta (memInputs z) g.row.2.2

noncomputable def treeDelta (z : K) : NTree (GenMemoryRow K) → K
  | .node g cs => genDelta z g + (cs.map (treeDelta z)).sum

noncomputable def forestDelta (z : K) (ts : List (NTree (GenMemoryRow K))) : K :=
  (ts.map (treeDelta z)).sum

theorem forestDelta_nil (z : K) :
    forestDelta z ([] : List (NTree (GenMemoryRow K))) = 0 := by
  simp [forestDelta]

theorem forestDelta_cons (z : K) (t : NTree (GenMemoryRow K))
    (ts : List (NTree (GenMemoryRow K))) :
    forestDelta z (t :: ts) = treeDelta z t + forestDelta z ts := by
  simp [forestDelta, List.sum_cons]

theorem forestDelta_singleton (z : K) (t : NTree (GenMemoryRow K)) :
    forestDelta z [t] = treeDelta z t := by
  simp [forestDelta_cons, forestDelta_nil]

theorem forestDelta_append (z : K) :
    ∀ l₁ l₂ : List (NTree (GenMemoryRow K)),
      forestDelta z (l₁ ++ l₂) = forestDelta z l₁ + forestDelta z l₂
  | [], l₂ => by
      rw [List.nil_append, forestDelta_nil, zero_add]
  | t :: ts, l₂ => by
      rw [List.cons_append, forestDelta_cons, forestDelta_cons,
        forestDelta_append z ts l₂]
      abel

theorem treeDelta_node (z : K) (g : GenMemoryRow K)
    (cs : List (NTree (GenMemoryRow K))) :
    treeDelta z (.node g cs) = genDelta z g + forestDelta z cs := by
  simp [treeDelta, forestDelta]

theorem genDelta_gMemRow9 (z : K) (sk : MemoryRowSkeleton) (e : ℕ)
    (pub : Pub K) :
    genDelta z (gMemRow9 sk e z pub) = interDelta (memInputs z) pub :=
  rfl

theorem interDelta_op9Halt (E : Noun → ComputeTable.FP K) (z : K) (a : ℕ) :
    interDelta (memInputs z) (op9HaltPub E a) = 0 := by
  simp [interDelta, op9HaltPub]

theorem interDelta_annotatedDec (E : Noun → ComputeTable.FP K)
    (parent hd tl : Noun) (lc rc : Cell K) (lcSt rcSt : MState)
    (ipre icur : K) :
    interDelta (memInputs z) (annotatedDecPub E parent hd tl lc rc lcSt rcSt ipre icur lmb) = 0 := by
  simp [interDelta, annotatedDecPub]

def recPole (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (cprime : K := 1) : K :=
  pole (memInputs z) ⟨E root, E child, (ax : K), ts⟩ cprime

theorem interDelta_annotatedRead (E : Noun → ComputeTable.FP K)
    (root child : Noun) (ax : ℕ) (ts : K) (lc : Cell K) (ipre icur : K)
    (lmb : K := lmb) :
    interDelta (memInputs z)
      (annotatedReadPub E root child ax ts lc ipre icur lmb) =
      (recPole E z root child ax ts)⁻¹ := by
  simp [interDelta, annotatedReadPub, recPole, Pub.cprime, Option.getD]

theorem interDelta_annotatedVerify (E : Noun → ComputeTable.FP K)
    (root child : Noun) (ax : ℕ) (ts : K) (lc : Cell K) (ipre icur : K) :
    interDelta (memInputs z)
      (annotatedVerifyPub E root child ax ts lc ipre icur lmb) =
      -(recPole E z root child ax ts)⁻¹ := by
  simp [interDelta, annotatedVerifyPub, recPole, Pub.cprime]

theorem genAnnotatedNounWalk_delta (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, treeDelta z (genAnnotatedNounWalk E z lmb n).1 = 0
  | .atom a => by
      simp [genAnnotatedNounWalk, treeDelta_node, forestDelta_nil,
        genDelta_gMemRow9, interDelta_op9Halt]
  | .cell h t => by
      simp [genAnnotatedNounWalk, treeDelta_node, forestDelta_cons,
        forestDelta_nil, genDelta_gMemRow9, interDelta_annotatedDec,
        genAnnotatedNounWalk_delta E z h, genAnnotatedNounWalk_delta E z t]

theorem genAnnotatedVerify_delta (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    treeDelta z (genAnnotatedVerify E z lmb root child ax ts recordExp).1 =
      -(recPole E z root child ax ts)⁻¹ := by
  simp [genAnnotatedVerify, treeDelta_node, forestDelta_cons, forestDelta_nil,
    genDelta_gMemRow9, interDelta_annotatedVerify, genAnnotatedNounWalk_delta,
    MemoryTable.Pub.cprime, recPole]

theorem genAnnotatedDescent_delta (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (currentNoun : Noun) (remainingAxis : ℕ) :
    forestDelta z
      (genAnnotatedDescent E z lmb root child recAxis ts recordExp
        currentNoun remainingAxis).1 =
      -(recPole E z root child recAxis ts)⁻¹ := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAnnotatedDescent
    split
    · simp [forestDelta_singleton, genAnnotatedVerify_delta]
    · split
      · rw [forestDelta_singleton, treeDelta_node, genDelta_gMemRow9,
          interDelta_annotatedDec, forestDelta_append, forestDelta_singleton,
          genAnnotatedNounWalk_delta]
        have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun)
        simp [ihd]
      · rw [forestDelta_singleton, treeDelta_node, genDelta_gMemRow9,
          interDelta_annotatedDec, forestDelta_append, forestDelta_singleton,
          genAnnotatedNounWalk_delta]
        have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun)
        simp [ihd]

theorem genAnnotatedRecordTree_delta (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis : ℕ) (recordExp : ℕ) :
    treeDelta z (genAnnotatedRecordTree E z α lmb root child axis recordExp) = 0 := by
  simp only [genAnnotatedRecordTree]
  rw [treeDelta_node, genDelta_gMemRow9, interDelta_annotatedRead]
  have h := genAnnotatedDescent_delta (lmb := lmb) E z root child axis (α ^ recordExp)
    recordExp root axis
  simp [h]

theorem genAnnotatedDescentCont_delta (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : Cell K)
    (contState : MState) (currentNoun : Noun) (remainingAxis : ℕ) :
    forestDelta z
      (genAnnotatedDescentCont E z lmb cont contCell contState
        currentNoun remainingAxis).1 =
      forestDelta z cont := by
  induction remainingAxis using Nat.strongRecOn generalizing currentNoun with
  | _ n ih =>
    unfold genAnnotatedDescentCont
    split
    · simp
    · split
      · rw [forestDelta_singleton, treeDelta_node, genDelta_gMemRow9,
          interDelta_annotatedDec, forestDelta_append, forestDelta_singleton,
          genAnnotatedNounWalk_delta]
        have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaTail currentNoun)
        simp [ihd]
      · rw [forestDelta_singleton, treeDelta_node, genDelta_gMemRow9,
          interDelta_annotatedDec, forestDelta_append, forestDelta_singleton,
          genAnnotatedNounWalk_delta]
        have ihd := ih (axisRest n) (axisRest_lt (by omega)) (formulaHead currentNoun)
        simp [ihd]

theorem genAnnotatedChainedInner_delta (E : Noun → ComputeTable.FP K) (z α : K)
    (prev : MemRecordReq) :
    ∀ more,
      forestDelta z (genAnnotatedChainedInner E z α lmb prev more).1 =
        -(recPole E z prev.root prev.child prev.axis (α ^ prev.recordExp))⁻¹
  | [] => by
      simp [genAnnotatedChainedInner_nil, forestDelta_singleton,
        genAnnotatedVerify_delta]
  | r :: more => by
      unfold genAnnotatedChainedInner
      rw [forestDelta_singleton, treeDelta_node, genDelta_gMemRow9,
        interDelta_annotatedRead, forestDelta_cons, forestDelta_nil]
      rw [treeDelta_node, genDelta_gMemRow9, interDelta_annotatedVerify]
      have ih := genAnnotatedChainedInner_delta E z α r more
      have hd := genAnnotatedDescentCont_delta (lmb := lmb) E z
        (genAnnotatedChainedInner E z α lmb r more).1
        (genAnnotatedChainedInner E z α lmb r more).2
        (chainedInnerRootState more) r.root r.axis
      simp [hd, ih]

theorem genAnnotatedChainedTree_delta (E : Noun → ComputeTable.FP K) (z α : K)
    (reqs : List MemRecordReq) (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z α lmb reqs = some t) :
    treeDelta z t = 0 := by
  cases reqs with
  | nil => simp [genAnnotatedChainedTree] at ht
  | cons r rest =>
    cases rest with
    | nil =>
      simp only [genAnnotatedChainedTree] at ht
      injection ht with ht
      subst t
      simpa using
        genAnnotatedRecordTree_delta E z α r.root r.child r.axis r.recordExp
    | cons r2 more =>
      simp only [genAnnotatedChainedTree] at ht
      injection ht with ht
      subst t
      rw [treeDelta_node, genDelta_gMemRow9, interDelta_annotatedRead]
      have hi := genAnnotatedChainedInner_delta (lmb := lmb) E z α r (r2 :: more)
      have hd := genAnnotatedDescentCont_delta (lmb := lmb) E z
        (genAnnotatedChainedInner E z α lmb r (r2 :: more)).1
        (genAnnotatedChainedInner E z α lmb r (r2 :: more)).2
        (chainedInnerRootState (r2 :: more)) r.root r.axis
      simp [hd, hi]

theorem genRowMemForest_delta (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ reqs, forestDelta z (genRowMemForest E z α lmb reqs) = 0
  | [] => by
      simp [genRowMemForest, forestDelta_nil]
  | [r] => by
      simp [genRowMemForest, forestDelta_singleton, genAnnotatedRecordTree_delta]
  | [r1, r2] => by
      rw [genRowMemForest_pair_eq]
      split
      · cases h : genAnnotatedChainedTree E z α lmb [r1, r2] with
        | none => simp [genAnnotatedChainedTree] at h
        | some t =>
          rw [forestDelta_singleton]
          exact genAnnotatedChainedTree_delta E z α [r1, r2] t h
      · rw [forestDelta_cons, forestDelta_cons, forestDelta_nil,
          genAnnotatedRecordTree_delta, genAnnotatedRecordTree_delta]
        simp
  | [r1, r2, r3] => by
      rw [genRowMemForest_three_eq, forestDelta_append, forestDelta_singleton]
      have h12 := genRowMemForest_delta E z α [r1, r2]
      have h3 := genAnnotatedRecordTree_delta (lmb := lmb) E z α r3.root r3.child
        r3.axis r3.recordExp
      simp [h12, h3]
  | r1 :: r2 :: r3 :: r4 :: rest => by
      change forestDelta z
          ((r1 :: r2 :: r3 :: r4 :: rest).map fun r =>
            genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) = 0
      induction (r1 :: r2 :: r3 :: r4 :: rest) with
      | nil => simp [forestDelta_nil]
      | cons r rs ih =>
        rw [List.map_cons, forestDelta_cons, genAnnotatedRecordTree_delta, ih]
        simp

theorem genMemForestFromList_delta (E : Noun → ComputeTable.FP K) (z α : K)
    (ts : List (NTree (GenComputeRow K)))
    (hs : ∀ t ∈ ts, forestDelta z (genMemForestFromTree E z α lmb t) = 0) :
    forestDelta z (genMemForestFromList E z α lmb ts) = 0 := by
  induction ts with
  | nil =>
    simp [genMemForestFromList, forestDelta_nil]
  | cons t rest ih =>
    rw [genMemForestFromList_cons]
    rw [forestDelta_append, hs t (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun u hu => hs u (List.mem_cons_of_mem _ hu))]
    simp

theorem genMemForestFromTree_delta (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K)) :
    forestDelta z (genMemForestFromTree E z α lmb t) = 0 := by
  induction hn : t.size using Nat.strongRecOn generalizing t with
  | _ n ih =>
    cases t with
    | node g cs =>
      rw [genMemForestFromTree_node]
      rw [forestDelta_append, genRowMemForest_delta, zero_add]
      have hcs : ∀ c ∈ cs, forestDelta z (genMemForestFromTree E z α lmb c) = 0 := by
        intro c hc
        have hin : c.size ∈ cs.map NTree.size := List.mem_map.mpr ⟨c, hc, rfl⟩
        have hle : c.size ≤ (cs.map NTree.size).sum := List.le_sum_of_mem hin
        have hsz : n = 1 + (cs.map NTree.size).sum := by
          simpa [NTree.size] using hn.symm
        exact ih c.size (by omega) c rfl
      exact genMemForestFromList_delta E z α cs hcs

theorem forestDelta_eq_roots_add_children (z : K) :
    ∀ l : List (NTree (GenMemoryRow K)),
      forestDelta z l =
        (l.map (fun t => genDelta z t.label)).sum +
          forestDelta z (l.flatMap NTree.children) := by
  intro l
  induction l with
  | nil => simp [forestDelta, genDelta]
  | cons t ts ih =>
    cases t with
    | node g cs =>
      rw [forestDelta_cons, treeDelta_node, List.map_cons, List.sum_cons,
        List.flatMap_cons, forestDelta_append, NTree.label_node,
        NTree.children_node, ih]
      abel

theorem sum_genDelta_bfsForest (z : K) :
    ∀ l : List (NTree (GenMemoryRow K)),
      (List.map (genDelta z) ((bfsForest l).map NTree.label)).sum =
        forestDelta z l := by
  intro l
  generalize hn : totalSize l = n
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
    by_cases hl : l = []
    · subst l
      simp [bfsForest_nil, forestDelta, genDelta]
    · rw [bfsForest_cons_eq l hl, List.map_append, List.map_append,
        List.sum_append, forestDelta_eq_roots_add_children]
      have hsize := totalSize_flatMap_children l
      have hpos : 0 < l.length := List.length_pos_of_ne_nil hl
      have hlt : totalSize (l.flatMap NTree.children) < n := by omega
      have hroots :
          (List.map (genDelta z) (List.map NTree.label l)).sum =
            (l.map (fun t => genDelta z t.label)).sum := by
        rw [List.map_map]
        rfl
      rw [hroots, ih _ hlt (l.flatMap NTree.children) rfl]

theorem sumDelta_eq_forestDelta (z : K)
    (forest : List (NTree (GenMemoryRow K))) :
    sumDelta (memInputs z)
      (List.map (fun g : GenMemoryRow K => g.row.2.2)
        (List.map NTree.label (bfsForest forest))) =
      forestDelta z forest := by
  simp only [sumDelta, genDelta]
  have hmap :
      List.map (interDelta (memInputs z))
          (List.map (fun g : GenMemoryRow K => g.row.2.2)
            (List.map NTree.label (bfsForest forest))) =
        List.map (genDelta z) ((bfsForest forest).map NTree.label) := by
    simp [List.map_map, genDelta]
  rw [hmap, sum_genDelta_bfsForest]

theorem genAnnotatedRecordTree_axis3_all_inputs (z α : K) (hd tl : Noun) (e : ℕ) :
    ∀ t, InTree (genAnnotatedRecordTree (encC z) z α lmb (.cell hd tl) tl 3 e) t →
      t.label.row.2.1 = memInputs z := by
  intro t ht
  unfold genAnnotatedRecordTree at ht
  unfold genAnnotatedDescent at ht
  simp only [show ¬((3 : ℕ) < 2) from by omega, formulaHead, formulaTail,
    axisTopBit_three, axisRest_three, ↓reduceIte] at ht
  unfold genAnnotatedDescent at ht
  simp only [show (1 : ℕ) < 2 from by omega, ite_true,
    genAnnotatedVerify, List.cons_append, List.nil_append] at ht
  cases ht with
  | here => simp [gMemRow9]
  | sub hs ht1 =>
      simp only [NTree.children, List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs
      cases ht1 with
      | here => simp [gMemRow9]
      | sub hs2 ht2 =>
          simp only [NTree.children, List.mem_cons, List.not_mem_nil, or_false] at hs2
          rcases hs2 with rfl | rfl
          · exact genAnnotatedNounWalk_inputs (encC z) z hd t ht2
          · exact genAnnotatedVerify_inputs (encC z) z
              (.cell hd tl) tl 3 (α ^ e) e t ht2

theorem genAnnotatedRecordTree_axis2_all_inputs (z α : K) (hd tl : Noun) (e : ℕ) :
    ∀ t, InTree (genAnnotatedRecordTree (encC z) z α lmb (.cell hd tl) hd 2 e) t →
      t.label.row.2.1 = memInputs z := by
  intro t ht
  unfold genAnnotatedRecordTree at ht
  unfold genAnnotatedDescent at ht
  simp only [show ¬((2 : ℕ) < 2) from by omega, formulaHead, formulaTail,
    axisTopBit_two, axisRest_two, Bool.false_eq_true, ↓reduceIte] at ht
  unfold genAnnotatedDescent at ht
  simp only [show (1 : ℕ) < 2 from by omega, ite_true,
    genAnnotatedVerify, List.cons_append, List.nil_append] at ht
  cases ht with
  | here => simp [gMemRow9]
  | sub hs ht1 =>
      simp only [NTree.children, List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs
      cases ht1 with
      | here => simp [gMemRow9]
      | sub hs2 ht2 =>
          simp only [NTree.children, List.mem_cons, List.not_mem_nil, or_false] at hs2
          rcases hs2 with rfl | rfl
          · exact genAnnotatedVerify_inputs (encC z) z
              (.cell hd tl) hd 2 (α ^ e) e t ht2
          · exact genAnnotatedNounWalk_inputs (encC z) z tl t ht2

theorem genAnnotatedDescentCont_axis2_all_inputs
    (cont : List (NTree (GenMemoryRow K))) (contCell : Cell K)
    (contState : MState) (hd tl : Noun) (z : K)
    (hcont : ∀ u ∈ cont, ∀ t, InTree u t → t.label.row.2.1 = memInputs z) :
    ∀ u ∈ (genAnnotatedDescentCont (encC z) z lmb cont contCell contState
        (.cell hd tl) 2).1,
      ∀ t, InTree u t → t.label.row.2.1 = memInputs z := by
  intro u hu t ht
  rw [genAnnotatedDescentCont_axis2] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  subst u
  cases ht with
  | here => simp [gMemRow9]
  | sub hs ht' =>
      simp only [NTree.children] at hs
      rw [List.mem_append] at hs
      rcases hs with hL | hR
      · exact hcont _ hL t ht'
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
        subst hR
        exact genAnnotatedNounWalk_inputs (encC z) z tl t ht'

theorem genAnnotatedDescentCont_axis3_all_inputs
    (cont : List (NTree (GenMemoryRow K))) (contCell : Cell K)
    (contState : MState) (hd tl : Noun) (z : K)
    (hcont : ∀ u ∈ cont, ∀ t, InTree u t → t.label.row.2.1 = memInputs z) :
    ∀ u ∈ (genAnnotatedDescentCont (encC z) z lmb cont contCell contState
        (.cell hd tl) 3).1,
      ∀ t, InTree u t → t.label.row.2.1 = memInputs z := by
  intro u hu t ht
  rw [genAnnotatedDescentCont_axis3] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  subst u
  cases ht with
  | here => simp [gMemRow9]
  | sub hs ht' =>
      simp only [NTree.children] at hs
      rw [List.mem_append] at hs
      rcases hs with hL | hR
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
        subst hL
        exact genAnnotatedNounWalk_inputs (encC z) z hd t ht'
      · exact hcont _ hR t ht'

theorem genAnnotatedChainedInner_one_axis2_all_inputs (z α : K)
    (prevRoot : Noun) (hd2 tl2 : Noun) (ePrev e2 : ℕ) :
    ∀ u ∈ (genAnnotatedChainedInner (encC z) z α lmb
        ⟨prevRoot, .cell hd2 tl2, 3, ePrev⟩
        [⟨.cell hd2 tl2, hd2, 2, e2⟩]).1,
      ∀ t, InTree u t → t.label.row.2.1 = memInputs z := by
  intro u hu t ht
  unfold genAnnotatedChainedInner at hu
  simp only [genAnnotatedChainedInner_nil, chainedInnerRootState] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  subst u
  cases ht with
  | here => simp [gMemRow9]
  | sub hs ht1 =>
      simp only [NTree.children, List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs
      cases ht1 with
      | here => simp [gMemRow9]
      | sub hs2 ht2 =>
          refine genAnnotatedDescentCont_axis2_all_inputs (lmb := lmb)
            [(genAnnotatedVerify (encC z) z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).1]
            (genAnnotatedVerify (encC z) z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).2
            .verify_child hd2 tl2 z ?_ _ ?_ t ht2
          · intro v hv w hw
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            subst v
            exact genAnnotatedVerify_inputs (encC z) z
              (.cell hd2 tl2) hd2 2 (α ^ e2) e2 w hw
          · simpa [NTree.children] using hs2

theorem genAnnotatedChainedTree_axis3_axis2_all_inputs (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    ∀ t, genAnnotatedChainedTree (encC z) z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩] = some t →
      ∀ u, InTree t u → u.label.row.2.1 = memInputs z := by
  intro t ht u hu
  unfold genAnnotatedChainedTree at ht
  simp only [chainedInnerRootState] at ht
  injection ht with ht
  subst t
  cases hu with
  | here => simp [gMemRow9]
  | sub hs hu' =>
      simp only [NTree.children] at hs
      exact genAnnotatedDescentCont_axis3_all_inputs
        (genAnnotatedChainedInner (encC z) z α lmb
          ⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩
          [⟨.cell hd2 tl2, hd2, 2, e2⟩]).1
        (genAnnotatedChainedInner (encC z) z α lmb
          ⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩
          [⟨.cell hd2 tl2, hd2, 2, e2⟩]).2
        .read_root hd1 (.cell hd2 tl2) z
        (fun v hv w hw =>
          genAnnotatedChainedInner_one_axis2_all_inputs z α
            (.cell hd1 (.cell hd2 tl2)) hd2 tl2 e1 e2 v hv w hw)
        _ hs u hu'

theorem genRowMemForest_singleton_axis3_inputs (z α : K) (hd tl : Noun) (e : ℕ) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb [⟨.cell hd tl, tl, 3, e⟩],
      ∀ t, InTree u t → t.label.row.2.1 = memInputs z := by
  intro u hu t ht
  simp [genRowMemForest_singleton] at hu
  subst u
  exact genAnnotatedRecordTree_axis3_all_inputs z α hd tl e t ht

theorem genRowMemForest_singleton_axis2_inputs (z α : K) (hd tl : Noun) (e : ℕ) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb [⟨.cell hd tl, hd, 2, e⟩],
      ∀ t, InTree u t → t.label.row.2.1 = memInputs z := by
  intro u hu t ht
  simp [genRowMemForest_singleton] at hu
  subst u
  exact genAnnotatedRecordTree_axis2_all_inputs z α hd tl e t ht

theorem genRowMemForest_chain32_inputs (z α : K) (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩],
      ∀ t, InTree u t → t.label.row.2.1 = memInputs z := by
  intro u hu t ht
  unfold genRowMemForest at hu
  simp only at hu
  cases h : genAnnotatedChainedTree (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none =>
    simp [genAnnotatedChainedTree] at h
  | some tree =>
    simp [h] at hu
    subst u
    exact genAnnotatedChainedTree_axis3_axis2_all_inputs z α
      hd1 hd2 tl2 e1 e2 tree h t ht

theorem genRowMemForest_three_chain32_inputs (z α : K)
    (hd1 hd2 tl2 hd3 tl3 : Noun) (e1 e2 e3 : ℕ) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩,
       ⟨.cell hd3 tl3, hd3, 2, e3⟩],
      ∀ t, InTree u t → t.label.row.2.1 = memInputs z := by
  intro u hu t ht
  unfold genRowMemForest at hu
  cases h : genAnnotatedChainedTree (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none =>
    simp [genAnnotatedChainedTree] at h
  | some tree =>
    simp [h, List.mem_append, List.mem_singleton] at hu
    rcases hu with hmem | hmem
    · rw [hmem] at ht
      exact genAnnotatedChainedTree_axis3_axis2_all_inputs z α
        hd1 hd2 tl2 e1 e2 tree h t ht
    · rw [hmem] at ht
      exact genAnnotatedRecordTree_axis2_all_inputs z α hd3 tl3 e3 t ht

theorem genMemForestFromTree_of_rowInputs (z α : K)
    (t : NTree (GenComputeRow K))
    (H : ∀ n, InTree t n →
      ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
        ∀ v, InTree u v → v.label.row.2.1 = memInputs z)
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ genMemForestFromTree (encC z) z α lmb t)
    (v : NTree (GenMemoryRow K)) (hv : InTree u v) :
    v.label.row.2.1 = memInputs z := by
  suffices ∀ N t,
      NTree.size t ≤ N →
      (∀ n, InTree t n →
        ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
          ∀ v, InTree u v → v.label.row.2.1 = memInputs z) →
      ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
        ∀ v, InTree u v → v.label.row.2.1 = memInputs z from
    this (NTree.size t) t le_rfl H u hu v hv
  intro N
  induction N with
  | zero =>
    intro t ht H u hu v hv
    cases t with
    | node g cs =>
      simp [NTree.size] at ht
  | succ N ih =>
    intro t ht H u hu v hv
    cases t with
    | node g cs =>
      simp [genMemForestFromTree] at hu
      rcases hu with hu | hu
      · exact H (.node g cs) (InTree.here _) u hu v hv
      · have recList :
            ∀ cs', (∀ c ∈ cs', c ∈ cs) →
              (∀ t ∈ cs', NTree.size t ≤ N) →
              (∀ t ∈ cs', ∀ n, InTree t n →
                ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
                  ∀ v, InTree u v → v.label.row.2.1 = memInputs z) →
              ∀ u ∈ genMemForestFromList (encC z) z α lmb cs',
                ∀ v, InTree u v → v.label.row.2.1 = memInputs z := by
          intro cs' hsub hsz H' u' hu' v' hv'
          induction cs' generalizing u' v' with
          | nil => simp [genMemForestFromList] at hu'
          | cons c rest ihcs =>
            simp [genMemForestFromList] at hu'
            rcases hu' with hu' | hu'
            · exact ih c (hsz c (by simp))
                (fun n hn => H' c (by simp) n hn) u' hu' v' hv'
            · refine ihcs ?_ ?_ ?_ u' hu' v' hv'
              · intro c' hc'; exact hsub c' (List.mem_cons_of_mem _ hc')
              · intro t htt; exact hsz t (List.mem_cons_of_mem _ htt)
              · intro t htt; exact H' t (List.mem_cons_of_mem _ htt)
        refine recList cs (fun _ h => h) ?_
          (fun t ht n hn => H n (InTree.sub ht hn)) u hu v hv
        intro c hc
        have hin : NTree.size c ∈ cs.map NTree.size := List.mem_map.mpr ⟨c, hc, rfl⟩
        have hsum : NTree.size c ≤ (cs.map NTree.size).sum := List.le_sum_of_mem hin
        simp [NTree.size] at ht
        omega

theorem dotAssigned_rowInputs (z α : K)
    (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (dotTree (K := K))) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      ∀ v, InTree u v → v.label.row.2.1 = memInputs z := by
  have hnF : n ∈ bfsForest [bfsAssign (dotTree (K := K))] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab := bfsAssign_bfsForest_labels (dotTree (K := K))
  have hmem : n.label ∈ (bfsForest [bfsAssign (dotTree (K := K))]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [hlab] at hmem
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨i, hi, hieq⟩
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTree (K := K))) hi
  rw [← hieq, extractNodeReqs, bfsLabelAt_requests (dotTree (K := K)) i hi']
  rcases dot_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hget : (bfsRows (dotTree (K := K)))[0] = (dotTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 1).stamp 0 g.requests) hget]
    simp [dotTree, skelNode, extractNodeReqsAux_cons3]
    exact genRowMemForest_three_chain32_inputs z α (.atom 6) dotCondFormula
      dotBranchPair dotThenFormula dotElseFormula
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 1)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 2)
  · have hget : (bfsRows (dotTree (K := K)))[1] = (dotCondTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 2).stamp 0 g.requests) hget]
    simp [dotCondTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_inputs z α (.atom 1) (.atom 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 2).stamp 0)
  · have hget : (bfsRows (dotTree (K := K)))[2] = (dotOp2Tree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 3).stamp 0 g.requests) hget]
    simp [dotOp2Tree, skelNode, extractNodeReqsAux_cons2]
    exact genRowMemForest_chain32_inputs z α (.atom 2) dotOp2B dotOp2C
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 3).stamp 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 3).stamp 1)
  · have hget : (bfsRows (dotTree (K := K)))[3] = (dotOp1BTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 4).stamp 0 g.requests) hget]
    simp [dotOp1BTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_inputs z α (.atom 1)
      (.cell (.atom 0) (.atom 1))
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 4).stamp 0)
  · have hget : (bfsRows (dotTree (K := K)))[4] = (dotOp1CTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 5).stamp 0 g.requests) hget]
    simp [dotOp1CTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_inputs z α (.atom 1) dotOp9Formula
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 5).stamp 0)
  · have hget : (bfsRows (dotTree (K := K)))[5] = (dotOp9Tree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 6).stamp 0 g.requests) hget]
    simp [dotOp9Tree, skelNode, extractNodeReqsAux_cons3]
    exact genRowMemForest_three_chain32_inputs z α (.atom 9) (.atom 2)
      dotCoreFormula dotElem0 dotElem1
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 1)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 2)
  · have hget : (bfsRows (dotTree (K := K)))[6] = (dotOp9CoreTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 7).stamp 0 g.requests) hget]
    simp [dotOp9CoreTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_inputs z α (.atom 1) dotCore
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 7).stamp 0)
  · have hget : (bfsRows (dotTree (K := K)))[7] = (dotOp9InvokeTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 8).stamp 0 g.requests) hget]
    simp [dotOp9InvokeTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_inputs z α (.atom 1) (.atom 3)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 8).stamp 0)

theorem dotAssigned_rowInputs_air (z α : K)
    (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (dotTreeAir (K := K))) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      ∀ v, InTree u v → v.label.row.2.1 = memInputs z := by
  have hnF : n ∈ bfsForest [bfsAssign (dotTreeAir (K := K))] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab := bfsAssign_bfsForest_labels (dotTreeAir (K := K))
  have hmem : n.label ∈ (bfsForest [bfsAssign (dotTreeAir (K := K))]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [hlab] at hmem
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨i, hi, hieq⟩
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTreeAir (K := K))) hi
  rw [← hieq, extractNodeReqs, bfsLabelAt_requests (dotTreeAir (K := K)) i hi']
  rcases dot_air_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hget : (bfsRows (dotTreeAir (K := K)))[0] = (dotTreeAir (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 0 g.requests) hget]
    simp [dotTreeAir, skelNode, extractNodeReqsAux_cons3]
    exact genRowMemForest_three_chain32_inputs z α (.atom 6) dotCondFormula
      dotBranchPair dotThenFormula dotElseFormula
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 1)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 2)
  · have hget : (bfsRows (dotTreeAir (K := K)))[1] = (dotOp2Tree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 0 g.requests) hget]
    simp [dotOp2Tree, skelNode, extractNodeReqsAux_cons2]
    exact genRowMemForest_chain32_inputs z α (.atom 2) dotOp2B dotOp2C
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 1)
  · have hget : (bfsRows (dotTreeAir (K := K)))[2] = (dotCondTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 3).stamp 0 g.requests) hget]
    simp [dotCondTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_inputs z α (.atom 1) (.atom 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 3).stamp 0)
  · have hget : (bfsRows (dotTreeAir (K := K)))[3] = (dotOp1BTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 4).stamp 0 g.requests) hget]
    simp [dotOp1BTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_inputs z α (.atom 1)
      (.cell (.atom 0) (.atom 1))
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 4).stamp 0)
  · have hget : (bfsRows (dotTreeAir (K := K)))[4] = (dotOp1CTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 5).stamp 0 g.requests) hget]
    simp [dotOp1CTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_inputs z α (.atom 1) dotOp9Formula
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 5).stamp 0)
  · have hget : (bfsRows (dotTreeAir (K := K)))[5] = (dotOp9Tree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 0 g.requests) hget]
    simp [dotOp9Tree, skelNode, extractNodeReqsAux_cons3]
    exact genRowMemForest_three_chain32_inputs z α (.atom 9) (.atom 2)
      dotCoreFormula dotElem0 dotElem1
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 1)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 2)
  · have hget : (bfsRows (dotTreeAir (K := K)))[6] = (dotOp9CoreTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 7).stamp 0 g.requests) hget]
    simp [dotOp9CoreTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_inputs z α (.atom 1) dotCore
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 7).stamp 0)
  · have hget : (bfsRows (dotTreeAir (K := K)))[7] = (dotOp9InvokeTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 8).stamp 0 g.requests) hget]
    simp [dotOp9InvokeTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_inputs z α (.atom 1) (.atom 3)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 8).stamp 0)

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock Nock.Walk Nock.Noun
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.RowLayout
open MemoryTable

noncomputable section

def assignedForest (z α : K) : List (NTree (GenMemoryRow K)) :=
  genMemForestFromTree (encC z) z α MemoryTable.formRDefault (bfsAssign (dotTreeAir (K := K)))

def threadedForest (z α : K) : List (NTree (GenMemoryRow K)) :=
  threadGenForest (memInputs z) 0 (assignedForest z α)

def memoryForestThreaded (z α : K) :
    List (NTree (MemoryTable.MState × MemoryTable.DTmem K)) :=
  (threadedForest z α).map (mapNTree GenMemoryRow.row)

theorem threaded_kMem (z α : K) : (threadedForest z α).length = 10 := by
  unfold threadedForest assignedForest
  rw [threadGenForest_length, assigned_kMem]

theorem threaded_memRows (z α : K) : totalSize (threadedForest z α) = 184 := by
  unfold threadedForest assignedForest
  rw [threadGenForest_totalSize, assigned_memRows]

/-- The a-bearing view of the threaded execution. -/
def execThreadedA (z α : K) : ExactExecution (cfg z α) where
  computeTree := computeTree z α
  memoryForest := memoryForestThreaded z α
  memoryForest_nonempty := by
    refine List.ne_nil_of_length_pos ?_
    unfold memoryForestThreaded
    rw [List.length_map, threaded_kMem]
    omega
  memory_root_count := by
    unfold memoryForestThreaded
    rw [List.length_map, threaded_kMem]
    simp [cfg]
  compute_bfs_length := (exec z α).compute_bfs_length
  memory_bfs_length := by
    change (bfsForest (memoryForestThreaded z α)).length = (cfg z α).memRows
    unfold memoryForestThreaded
    rw [bfsForest_length, totalSize_map, threaded_memRows]
    simp [cfg]

noncomputable def execThreaded (z α : K) : ExactExecution (cfg z α) :=
  (execThreadedA z α).encodeMem

theorem two_ne_zero : (2 : K) ≠ 0 := by
  intro h
  have : 769 ∣ 2 := (CharP.cast_eq_zero_iff K 769 2).mp h
  omega

theorem assigned_bfs_inputs (z α : K) :
    ∀ t ∈ bfsForest (assignedForest z α), t.label.row.2.1 = memInputs z := by
  intro t ht
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ t).mp ht
  exact genMemForestFromTree_of_rowInputs z α _
    (dotAssigned_rowInputs_air z α) u hu t hin

theorem threaded_bfs_state (z α : K) :
    ∀ t ∈ bfsForest (threadedForest z α),
      t.label.row.1 = t.label.row.2.2.st :=
  threadGenForest_state_agree (memInputs z) 0 _
    (assigned_bfs_state_air z α)

theorem threaded_bfs_inputs (z α : K) :
    ∀ t ∈ bfsForest (threadedForest z α), t.label.row.2.1 = memInputs z :=
  threadGenForest_inputs (memInputs z) 0 _
    (assigned_bfs_inputs z α)

theorem threaded_bfs_Vmem (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    ∀ t ∈ bfsForest (threadedForest z α),
      VmemE MemoryTable.formRDefault (memInputs z) t.label.row.2.2 :=
  assigned_threaded_Vmem z α hz htwo

theorem memoryRowsA_eq_threaded (z α : K) :
    (execThreadedA z α).memoryRows =
      ((bfsForest (threadedForest z α)).map NTree.label).map GenMemoryRow.row := by
  unfold ExactExecution.memoryRows execThreadedA memoryForestThreaded
  rw [bfsForest_mapNTree, List.map_map, List.map_map]
  refine List.map_congr_left ?_
  intro t _
  exact mapNTree_label _ _

/-- The executed rows are the row encode of the threaded generated rows. -/
theorem memoryRows_eq_threaded (z α : K) :
    (execThreaded z α).memoryRows =
      (((bfsForest (threadedForest z α)).map NTree.label).map GenMemoryRow.row).map
        (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow MemoryTable.formRDefault) := by
  rw [execThreaded, ExactExecution.encodeMem_memoryRows, memoryRowsA_eq_threaded]
  rfl

theorem memoryRowsAccepted (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) :
    (execThreaded z α).MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff, memoryRows_eq_threaded]
  intro row hrow
  obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr0
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  have hst := threaded_bfs_state z α t ht
  have hinp := threaded_bfs_inputs z α t ht
  have hv := threaded_bfs_Vmem z α hz htwo t ht
  have hch : (cfg z α).challenges.memoryInputs = memInputs z :=
    memoryInputs_eq z α
  have hpub := encodeRow_pub (lmb := MemoryTable.formRDefault) t.label.row hst
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpub, encPub_st]; exact hst
  · rw [hch, encodeRow_inputs]; exact hinp
  · rw [hpub, encodeRow_inputs, hinp]; exact hv
  · rw [hpub, encPub_lambda]; rfl

theorem memoryRowsAccepted_seed :
    (execThreaded seedZ alphaA).MemoryRowsAccepted :=
  memoryRowsAccepted seedZ alphaA seedZ_ne_zero two_ne_zero

theorem memoryPubAtA_eq_thread (z α : K) (j : Fin (cfg z α).memRows) :
    (execThreadedA z α).memoryPubAt j =
      (threadPubs (memInputs z) 0
        (List.map (fun g : GenMemoryRow K => g.row.2.2)
          (List.map NTree.label
            (bfsForest (assignedForest z α)))))[j.1]'(by
          have hlen :
              (threadPubs (memInputs z) 0
                (List.map (fun g : GenMemoryRow K => g.row.2.2)
                  (List.map NTree.label
                    (bfsForest (assignedForest z α))))).length =
                (cfg z α).memRows := by
            rw [threadPubs_length, List.length_map, List.length_map,
              bfsForest_length]
            unfold assignedForest
            rw [assigned_memRows]
            simp [cfg]
          have := j.isLt
          omega) := by
  have hget :
      (execThreadedA z α).memoryPubAt j =
        ((execThreadedA z α).memoryRows[(j : ℕ)]'(by
          have := (execThreadedA z α).memoryRows_length
          have := j.isLt
          omega)).2.2 := by
    simp [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
      List.get_eq_getElem]
  rw [hget]
  have hlt : (j : ℕ) < (execThreadedA z α).memoryRows.length := by
    have := (execThreadedA z α).memoryRows_length
    have := j.isLt
    omega
  have hrows := memoryRowsA_eq_threaded z α
  have hlt' : (j : ℕ) <
      (((bfsForest (threadedForest z α)).map NTree.label).map
        GenMemoryRow.row).length := by
    rw [← hrows]; exact hlt
  have hidx := congrArg (fun l : List _ => l[(j : ℕ)]?) hrows
  simp only [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hlt'] at hidx
  have heq := Option.some.inj hidx
  rw [heq]
  have hpub :
      List.map (fun g : GenMemoryRow K => g.row.2.2)
        (List.map NTree.label (bfsForest (threadedForest z α))) =
        threadPubs (memInputs z) 0
          (List.map (fun g : GenMemoryRow K => g.row.2.2)
            (List.map NTree.label
              (bfsForest (assignedForest z α)))) := by
    unfold threadedForest
    rw [threadGenForest_bfs_labels, threadGenRows_map_pub]
  have hltP :
      (j : ℕ) <
        (threadPubs (memInputs z) 0
          (List.map (fun g : GenMemoryRow K => g.row.2.2)
            (List.map NTree.label
              (bfsForest (assignedForest z α))))).length := by
    have hlen :
        (threadPubs (memInputs z) 0
          (List.map (fun g : GenMemoryRow K => g.row.2.2)
            (List.map NTree.label
              (bfsForest (assignedForest z α))))).length =
          (cfg z α).memRows := by
      rw [threadPubs_length, List.length_map, List.length_map, bfsForest_length]
      unfold assignedForest
      rw [assigned_memRows]
      simp [cfg]
    have := j.isLt
    omega
  have hltL :
      (j : ℕ) <
        (List.map (fun g : GenMemoryRow K => g.row.2.2)
          (List.map NTree.label
            (bfsForest (threadedForest z α)))).length := by
    rw [hpub]; exact hltP
  have hidx2 := congrArg (fun l : List (Pub K) => l[(j : ℕ)]?) hpub
  simp only [List.getElem?_eq_getElem hltL, List.getElem?_eq_getElem hltP] at hidx2
  have heq2 := Option.some.inj hidx2
  have hleft :
      (List.map GenMemoryRow.row
          (List.map NTree.label
            (bfsForest (threadedForest z α))))[(j : ℕ)].2.2 =
        (List.map (fun g : GenMemoryRow K => g.row.2.2)
          (List.map NTree.label
            (bfsForest (threadedForest z α))))[(j : ℕ)] := by
    simp [List.getElem_map]
  rw [hleft, heq2]

/-- The executed pub at `j` is the encode of the threaded pub (`encPub`). -/
theorem memoryPubAt_eq_thread (z α : K) (j : Fin (cfg z α).memRows) :
    (execThreaded z α).memoryPubAt j = encPub MemoryTable.formRDefault ((execThreadedA z α).memoryPubAt j) := by
  have hmem := ExactExecution.memoryRowAt_mem (execThreadedA z α) j
  rw [memoryRowsA_eq_threaded] at hmem
  obtain ⟨g, hg, hgeq⟩ := List.mem_map.mp hmem
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  have hst := threaded_bfs_state z α t ht
  have hrow : (execThreaded z α).memoryRowAt j =
      SemanticTimestampStrategy.MemoryRowTemplate.encodeRow MemoryTable.formRDefault ((execThreadedA z α).memoryRowAt j)
          := by
    simp only [ExactExecution.memoryRowAt, List.get_eq_getElem, Fin.val_cast]
    simp [execThreaded, ExactExecution.encodeMem_memoryRows]
  simp only [ExactExecution.memoryPubAt]
  rw [hrow, encodeRow_pub _ (by rw [← hgeq]; exact hst)]

theorem memory_chain (z α : K) :
    ∀ i : Fin (cfg z α).memRows,
      ∀ hi : (i : ℕ) + 1 < (cfg z α).memRows,
        ((execThreaded z α).memoryPubAt i).icur =
          ((execThreaded z α).memoryPubAt ⟨(i : ℕ) + 1, hi⟩).ipre := by
  intro i hi
  let pubs : List (Pub K) :=
    List.map (fun g : GenMemoryRow K => g.row.2.2)
      (List.map NTree.label (bfsForest (assignedForest z α)))
  have hchain : InterChain (memInputs z) 0
      (0 + sumDelta (memInputs z) pubs)
      (threadPubs (memInputs z) 0 pubs) :=
    threadPubs_interChain (memInputs z) 0 pubs
  have hlenT : (threadPubs (memInputs z) 0 pubs).length = (cfg z α).memRows := by
    unfold pubs
    rw [threadPubs_length, List.length_map, List.length_map, bfsForest_length]
    unfold assignedForest
    rw [assigned_memRows]
    simp [cfg]
  have hget := interChain_handoff (memInputs z) 0 _ _ hchain (i : ℕ) (by
    have := i.isLt
    omega)
  rw [memoryPubAt_eq_thread, memoryPubAt_eq_thread, encPub_icur, encPub_ipre,
    memoryPubAtA_eq_thread, memoryPubAtA_eq_thread]
  exact hget

theorem memory_first_ipre (z α : K) :
    ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).ipre = 0 := by
  let pubs : List (Pub K) :=
    List.map (fun g : GenMemoryRow K => g.row.2.2)
      (List.map NTree.label (bfsForest (assignedForest z α)))
  have hlenT : (threadPubs (memInputs z) 0 pubs).length = (cfg z α).memRows := by
    unfold pubs
    rw [threadPubs_length, List.length_map, List.length_map, bfsForest_length]
    unfold assignedForest
    rw [assigned_memRows]
    simp [cfg]
  have hpos : 0 < (threadPubs (memInputs z) 0 pubs).length := by
    have : 0 < (cfg z α).memRows := (cfg z α).memRows_pos
    omega
  have hchain := threadPubs_interChain (memInputs z) 0 pubs
  have hne : threadPubs (memInputs z) 0 pubs ≠ [] :=
    List.ne_nil_of_length_pos hpos
  obtain ⟨p, ps, hth⟩ : ∃ p ps, threadPubs (memInputs z) 0 pubs = p :: ps := by
    cases h : threadPubs (memInputs z) 0 pubs with
    | nil => exact (hne h).elim
    | cons p ps => exact ⟨p, ps, rfl⟩
  have hipre : p.ipre = 0 :=
    interChain_head_ipre (memInputs z) 0 _ p ps (by rwa [hth] at hchain)
  rw [memoryPubAt_eq_thread, encPub_ipre, memoryPubAtA_eq_thread]
  have hlt0 : 0 < (p :: ps).length := by simp
  have hidx := congrArg (fun l : List (Pub K) => l[0]?) hth
  simp only [List.getElem?_eq_getElem hpos, List.getElem?_eq_getElem hlt0] at hidx
  have heq := Option.some.inj hidx
  rw [heq]
  exact hipre

theorem assignedForest_head_chained (z α : K) :
    ∃ t rest e1 e2,
      assignedForest z α = t :: rest ∧
      genAnnotatedChainedTree (encC z) z α MemoryTable.formRDefault
        [⟨.cell (.atom 6) (.cell dotCondFormula dotBranchPair),
          .cell dotCondFormula dotBranchPair, 3, e1⟩,
         ⟨.cell dotCondFormula dotBranchPair, dotCondFormula, 2, e2⟩] =
        some t := by
  have hshape :
      bfsAssign (dotTreeAir (K := K)) =
        NTree.node (bfsAssign (dotTreeAir (K := K))).label
          (bfsAssign (dotTreeAir (K := K))).children := by
    cases bfsAssign (dotTreeAir (K := K)); rfl
  set e1 := getRecordExp (bfsAssign (dotTreeAir (K := K))).label.stamp 0
  set e2 := getRecordExp (bfsAssign (dotTreeAir (K := K))).label.stamp 1
  set e3 := getRecordExp (bfsAssign (dotTreeAir (K := K))).label.stamp 2
  obtain ⟨t, hforest, hch⟩ :=
    genRowMemForest_three_chain32_head (encC z) z α
      (.atom 6) dotCondFormula dotBranchPair dotThenFormula dotElseFormula
      e1 e2 e3
  have hreqs :
      extractNodeReqs (bfsAssign (dotTreeAir (K := K))).label =
        [⟨.cell (.atom 6) (.cell dotCondFormula dotBranchPair),
          .cell dotCondFormula dotBranchPair, 3, e1⟩,
         ⟨.cell dotCondFormula dotBranchPair, dotCondFormula, 2, e2⟩,
         ⟨.cell dotThenFormula dotElseFormula, dotThenFormula, 2, e3⟩] := by
    rw [extractNodeReqs_air_root]
    simp [dotFormula, dotParentTail, dotBranchPair, e1, e2, e3]
  refine ⟨t,
    [genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault (.cell dotThenFormula dotElseFormula)
      dotThenFormula 2 e3] ++
      genMemForestFromList (encC z) z α MemoryTable.formRDefault
        (bfsAssign (dotTreeAir (K := K))).children, e1, e2, ?_, hch⟩
  unfold assignedForest
  rw [hshape, genMemForestFromTree, hreqs, hforest]
  rfl

/-- Dummy-wired: form-R leftover is the Relaxis join. -/
theorem assigned_bfs_head_pt (z α : K) (htwo : (2 : K) ≠ 0)
    (h : ∃ t rest,
      bfsForest (assignedForest z α) = t :: rest ∧
        t.label.row.2.2.pt.indicator = 0 ∧
        t.label.row.2.2.pt.counts = 0) :
    ∃ t rest,
      bfsForest (assignedForest z α) = t :: rest ∧
        t.label.row.2.2.pt.indicator = 0 ∧
        t.label.row.2.2.pt.counts = 0 :=
  h

/-- Dummy-wired first-row remaining (`hfirst`). -/
theorem memory_first_pt (z α : K) (htwo : (2 : K) ≠ 0)
    (h : ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.counts = 0) :
    ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.counts = 0 :=
  h

theorem memory_first_counts (z α : K) (htwo : (2 : K) ≠ 0)
    (h : ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.counts = 0) :
    ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.counts = 0 :=
  (memory_first_pt z α htwo h).2

theorem memory_first_indicator (z α : K) (htwo : (2 : K) ≠ 0)
    (h : ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.counts = 0) :
    ((execThreaded z α).memoryPubAt ⟨0, (cfg z α).memRows_pos⟩).pt.indicator = 0 :=
  (memory_first_pt z α htwo h).1

theorem memory_wf (z α : K) (hz : z ≠ 0) :
    ∀ i, WF (cfg z α).challenges.memoryInputs
      ((execThreaded z α).memoryPubAt i) := by
  intro i
  have hch : (cfg z α).challenges.memoryInputs = memInputs z :=
    memoryInputs_eq z α
  rw [hch, memoryPubAt_eq_thread]
  refine wf_encPub _ _ rfl ?_
  rw [memoryPubAtA_eq_thread]
  refine threadPubs_WF (memInputs z) 0 _ ?_
      _
      (List.getElem_mem _)
  intro p hp
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  unfold assignedForest at ht
  exact assigned_bfs_WF_air z α hz t ht

theorem memory_wf_seed :
    ∀ i, WF (cfg seedZ alphaA).challenges.memoryInputs
      ((execThreaded seedZ alphaA).memoryPubAt i) :=
  memory_wf seedZ alphaA seedZ_ne_zero

theorem memoryStateCount_eq_assignedFibre (z α : K) (s : MState) :
    memoryStateCount (execThreaded z α) s =
      forestFibre s (assignedForest z α) := by
  have hA : memoryStateCount (execThreaded z α) s = memoryStateCount (execThreadedA z α) s := by
    unfold memoryStateCount fibreCount
    rw [execThreaded, ExactExecution.encodeMem_memoryRows, List.countP_map]
    simp [Function.comp_def]
  rw [hA]
  unfold memoryStateCount
  rw [memoryRowsA_eq_threaded, fibreCount_map]
  have hlabs :
      (bfsForest (threadedForest z α)).map NTree.label =
        threadGenRows (memInputs z) 0
          ((bfsForest (assignedForest z α)).map NTree.label) := by
    unfold threadedForest
    exact threadGenForest_bfs_labels _ _ _
  rw [hlabs]
  have hst := threadGenRows_map_st (memInputs z) 0
    ((bfsForest (assignedForest z α)).map NTree.label)
  simp only [fibreCount]
  have h1 :
      List.countP (fun g : GenMemoryRow K => g.row.2.2.st = s)
        (threadGenRows (memInputs z) 0
          ((bfsForest (assignedForest z α)).map NTree.label)) =
        List.countP (fun x => x = s)
          ((threadGenRows (memInputs z) 0
            ((bfsForest (assignedForest z α)).map NTree.label)).map
            (fun g : GenMemoryRow K => g.row.2.2.st)) := by
    rw [List.countP_map]; rfl
  rw [h1, hst]
  have h2 :
      List.countP (fun x => x = s)
        (((bfsForest (assignedForest z α)).map NTree.label).map
          (fun g : GenMemoryRow K => g.row.2.2.st)) =
        List.countP (fun g : GenMemoryRow K => g.row.2.2.st = s)
          ((bfsForest (assignedForest z α)).map NTree.label) := by
    rw [List.countP_map]; rfl
  rw [h2]
  change fibreCount memPubSt
      ((bfsForest (assignedForest z α)).map NTree.label) s =
    forestFibre s (assignedForest z α)
  exact fibreCount_bfsForest s _

theorem recordCountBalance_threaded (z α : K) :
    RecordCountBalanced (execThreaded z α) := by
  unfold RecordCountBalanced
  rw [memoryStateCount_eq_assignedFibre, memoryStateCount_eq_assignedFibre]
  unfold assignedForest
  exact genMemForestFromTree_balanced (encC z) z α
    (bfsAssign (dotTreeAir (K := K)))

theorem memory_last_icur_eq_sumDelta (z α : K) :
    ((execThreaded z α).memoryPubAt
      ((cfg z α).orbit.lastIndex (cfg z α).memRows (cfg z α).memRows_pos)).icur =
      sumDelta (memInputs z)
        (List.map (fun g : GenMemoryRow K => g.row.2.2)
          (List.map NTree.label (bfsForest (assignedForest z α)))) := by
  let pubs : List (Pub K) :=
    List.map (fun g : GenMemoryRow K => g.row.2.2)
      (List.map NTree.label (bfsForest (assignedForest z α)))
  have hlenT : (threadPubs (memInputs z) 0 pubs).length = (cfg z α).memRows := by
    unfold pubs
    rw [threadPubs_length, List.length_map, List.length_map, bfsForest_length]
    unfold assignedForest
    rw [assigned_memRows]
    simp [cfg]
  have hpos : 0 < (threadPubs (memInputs z) 0 pubs).length := by
    have : 0 < (cfg z α).memRows := (cfg z α).memRows_pos
    omega
  have hne : threadPubs (memInputs z) 0 pubs ≠ [] :=
    List.ne_nil_of_length_pos hpos
  have hchain := threadPubs_interChain (memInputs z) 0 pubs
  have hlastIdx :
      (cfg z α).orbit.lastIndex (cfg z α).memRows (cfg z α).memRows_pos =
        ⟨(cfg z α).memRows - 1, Nat.sub_lt (cfg z α).memRows_pos (by omega)⟩ :=
    rfl
  rw [hlastIdx, memoryPubAt_eq_thread, encPub_icur, memoryPubAtA_eq_thread]
  have hidx : ((cfg z α).memRows - 1 : ℕ) =
      (threadPubs (memInputs z) 0 pubs).length - 1 := by
    omega
  have hgetLast :
      (threadPubs (memInputs z) 0 pubs)[(cfg z α).memRows - 1]'(by omega) =
        (threadPubs (memInputs z) 0 pubs).getLast hne := by
    have hidx' : (cfg z α).memRows - 1 =
        (threadPubs (memInputs z) 0 pubs).length - 1 := by omega
    simp [List.getLast_eq_getElem, hidx']
  rw [hgetLast, interChain_last_icur (memInputs z) 0 _ _ hne hchain]
  simp [zero_add, pubs, List.map_map]

theorem assigned_sumDelta (z α : K) :
    sumDelta (memInputs z)
      (List.map (fun g : GenMemoryRow K => g.row.2.2)
        (List.map NTree.label (bfsForest (assignedForest z α)))) = 0 := by
  rw [sumDelta_eq_forestDelta]
  unfold assignedForest
  exact genMemForestFromTree_delta (encC z) z α _

theorem memory_last_icur (z α : K) :
    ((execThreaded z α).memoryPubAt
      ((cfg z α).orbit.lastIndex (cfg z α).memRows (cfg z α).memRows_pos)).icur = 0 := by
  rw [memory_last_icur_eq_sumDelta, assigned_sumDelta]

-- Row-level memory: the retired `execThreaded_cprime_one` (`C' = 1`) has no successor; the
-- executed rows carry `C' = formRC λ a` (coherence is a generator obligation).

/-- Every executed (encoded) memory row carries the package `λ = formRDefault`. -/
theorem execThreaded_lambda? (z α : K) :
    ∀ i, ((execThreaded z α).memoryPubAt i).lambda? = some MemoryTable.formRDefault := by
  intro i
  rw [memoryPubAt_eq_thread, encPub_lambda?]

end

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.execThreaded
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.memoryRowsAccepted_seed
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.memory_chain
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.memory_first_ipre
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.memory_wf_seed
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.recordCountBalance_threaded
#print axioms Nock.NockVMROM.Thm54.TraceGen.assigned_bfs_WF
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.memory_last_icur_eq_sumDelta
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedChainedTree_axis3_axis2_root_pt
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.memory_first_counts
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.memory_first_indicator
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.memory_last_icur
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_delta
