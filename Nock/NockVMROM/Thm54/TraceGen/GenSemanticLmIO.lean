/-
  Nock/NockVMROM/Thm54/TraceGen/GenSemanticLmIO.lean

  **The request/response slot correspondence, generically.**

  `SemanticIOPreimage`'s `semantic_lmio` field (`Language.lean:299`) carries the paper's base IO
  relation `L_mIO^{MEM,K}` between the record list the *compute* table requests and
  the record list the *memory* table serves.  Until now it had no generic form: `MatmulConfig65537`
  proved it at its own 401-row trace and `DotConfig769` hand-wrote thirteen request and thirteen
  response records.

  Almost all of the mathematics was already here — it was written for matmul and stated over an
  arbitrary tree, forest, seed and challenge, but it lived inside `namespace MatmulConfig65537`, so
  nothing else could see it.  This module is that material lifted verbatim into
  `Nock.NockVMROM.Thm54.TraceGen`, plus the capstone it was one theorem short of:
  `genTimestampSkeleton_lmio`, for **any** program the generator accepts.

  The three facts the capstone rests on, all now generic:

  * **requests are `Nodup`** — their exponents are `1, 2, …, accAt t |bfsRows t|` by
    `genSemanticRequests_exponents`, i.e. consecutive, hence distinct;
  * **responses and requests have the same slots** — `hasReadRootSlot_memForest` identifies the
    forest's `read_root` slots with the compute rows' extracted requests, and
    `genComputeSkeleton_tree_requests_match` identifies those with the skeleton's
    own memory records;
  * **they have the same length** — the `read_root` fibre of `genMemForestFromTree` counts the
    extracted requests (`genMemForestFromTree_read_fibre`), which the serving identity matches to
    the request slots.

  Equal finite sets plus equal lengths plus `Nodup` on one side gives `Nodup` on the other and a
  `Perm`, which is `L_mIO` with `unique_requests := requests`.

  Two side conditions remain, and both are `nockCompiles` preconditions rather than facts about the
  program: `1 ≤ accAt t |bfsRows t|` (no empty request list — discharged from a nonempty trace) and
  `accAt t |bfsRows t| ≤ Ksz` (the `[K]` window of `Def:L_mIO`).

  -- the paper
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericMemory
import Nock.NockVMROM.Thm54.TraceGen.GenTierABinds
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderChildLink
import Nock.NockVMROM.Thm54.TraceGen.BFSAssign
import Nock.NockVMROM.Thm54.SemanticTimestampStrategy
import Nock.NockVMROM.Thm54.ChainedLanguage

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun Nock.NockVM
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

variable {K : Type} [Field K]

-- Form R `λ` of the generated memory rows (the configuration's `λ`; 28th λ-fix).
variable {lmb : K}

/-! ## Stamp/state agreement from `MemoryNodesOK` -- the paper -/

theorem memoryStampsWellFormed_of_nodesOK {z α : K} :
    ∀ t : NTree (GenMemoryRow K),
      MemoryNodesOK z α (mapNTree GenMemoryRow.node t) →
      memoryStampsWellFormed t := by
  let P := fun t : NTree (GenMemoryRow K) =>
    MemoryNodesOK z α (mapNTree GenMemoryRow.node t) →
      memoryStampsWellFormed t
  intro t
  change P t
  apply NTree.rec (motive_1 := P)
    (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro g ch ih hOK
    rw [memoryStampsWellFormed_iff]
    constructor
    · have hroot :=
        hOK (mapNTree GenMemoryRow.node (.node g ch)) (InTree.here _)
      simpa [mapNTree_label, GenMemoryRow.node] using hroot.2.1
    · intro s hs
      refine ih s hs (MemoryNodesOK.child hOK ?_)
      simpa [mapNTree_children] using List.mem_map.mpr ⟨s, hs, rfl⟩
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

theorem inTree_memoryTimestamp (z α : K)
    {t u : NTree (GenMemoryRow K)}
    (hOK : MemoryNodesOK z α (mapNTree GenMemoryRow.node t))
    (hu : InTree t u) :
    MemoryTimestampSpecializesAt α u.label.stamp u.label.row := by
  have hnode := hOK (mapNTree GenMemoryRow.node u) (mapNTree_inTree _ hu)
  obtain ⟨_, _, _, htime⟩ := hnode
  simpa [mapNTree_label] using htime

theorem memoryTimestamp_of_setGenAcc (α a b : K)
    (g : GenMemoryRow K)
    (h : MemoryTimestampSpecializesAt α g.stamp g.row) :
    MemoryTimestampSpecializesAt α g.stamp (setGenAcc g a b).row := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [setGenAcc_row1] using h1
  · simpa [setGenAcc, setAcc_st] using h2
  · simpa [setGenAcc, setAcc_mem] using h3
  · intro hp
    simpa [setGenAcc, setAcc_mem] using h4 hp

theorem threadGenRows_map_stamp (inp : MemoryTable.Inputs K) :
    ∀ acc gs,
      (threadGenRows inp acc gs).map GenMemoryRow.stamp =
        gs.map GenMemoryRow.stamp
  | _, [] => rfl
  | acc, g :: gs => by
      simp [threadGenRows_cons, threadGenRow_snd, setGenAcc]
      exact threadGenRows_map_stamp inp (threadGenRow inp acc g).1 gs

theorem threadGenRows_timestamp (α : K) (inp : MemoryTable.Inputs K) :
    ∀ acc gs,
      (∀ g ∈ gs, MemoryTimestampSpecializesAt α g.stamp g.row) →
      List.Forall₂ (MemoryTimestampSpecializesAt α)
        (gs.map GenMemoryRow.stamp)
        ((threadGenRows inp acc gs).map GenMemoryRow.row)
  | _, [] => by
      intro
      exact .nil
  | acc, g :: gs => by
      intro h
      refine .cons ?_ ?_
      · rw [threadGenRow_snd]
        exact memoryTimestamp_of_setGenAcc α _ _ g
          (h g (List.mem_cons.mpr (Or.inl rfl)))
      · exact threadGenRows_timestamp α inp (threadGenRow inp acc g).1 gs
          (fun r hr => h r (List.mem_cons_of_mem _ hr))

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.RowLayout

variable {K : Type} [Field K] {F : Type} [Field F] [Algebra F K]
variable {lmb : K}

noncomputable section

/-! ## Timestamp window -- the paper -/

theorem accAt_mono (t : NTree (GenComputeRow K)) :
    ∀ a b, a ≤ b → accAt t a ≤ accAt t b
  | a, _, Nat.le.refl => le_rfl
  | a, _, Nat.le.step h => by
      have ih := accAt_mono t a _ h
      simp only [accAt]
      omega

theorem stampOfAcc_recordExponent_le (st : ComputeTable.State) (acc : ℕ)
    (i : Fin 3) :
    (stampOfAcc st acc).recordExponent i ≤ acc + 3 := by
  cases st <;> simp [stampOfAcc] <;> split_ifs <;> omega

theorem bfsLabelAt_recordExponent_le (t : NTree (GenComputeRow K))
    (i : ℕ) (hi : i - 1 < (bfsRows t).length) (j : Fin 3) :
    (bfsLabelAt t i).stamp.recordExponent j ≤
      accAt t (i - 1) + 3 := by
  rw [bfsLabelAt_stamp t i hi]
  exact stampOfAcc_recordExponent_le _ _ j

theorem genSemanticRequests_exponent_le (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) {slot : CanonicalRecordSlot}
    (h : slot ∈ genSemanticRequests
      (genSemanticSkeleton (bfsAssign t) mf) (bfsStamps (bfsAssign t))) :
    slot.exponent ≤ accAt t (bfsRows t).length + 3 := by
  simp only [genSemanticRequests, List.mem_flatMap] at h
  obtain ⟨pair, hpair, hmem⟩ := h
  have hstamp : pair.2 ∈ bfsStamps (bfsAssign t) := (List.of_mem_zip hpair).2
  rw [bfsStamps_bfsAssign, List.mem_map] at hstamp
  obtain ⟨i, hi, hieq⟩ := hstamp
  have hi' := lt_bfsRows_of_mem_range' hi
  simp only [List.mem_filterMap, List.mem_ofFn] at hmem
  obtain ⟨o, ⟨j, rfl⟩, hsome⟩ := hmem
  by_cases hlt : (j : ℕ) < Nock.Framework.recordCount pair.1.state
  · rw [dif_pos hlt] at hsome
    injection hsome with hslotEq
    subst hslotEq
    have hle := bfsLabelAt_recordExponent_le t i hi' j
    have hiacc : accAt t (i - 1) ≤ accAt t (bfsRows t).length :=
      accAt_mono t _ _ (Nat.le_of_lt hi')
    change pair.2.recordExponent j ≤ _
    rw [← hieq]
    omega
  · rw [dif_neg hlt] at hsome
    cases hsome

theorem semanticRecordAt_exponent (z : K) (slot : CanonicalRecordSlot) :
    (SemanticTimestampSkeleton.semanticRecordAt (F := F) z slot).2.2 =
      slot.exponent :=
  rfl

/-! ## Response timestamp window -- the paper -/

theorem getRecordExp_le (stamp : ComputeTimestampRow) (N i : ℕ)
    (h : ∀ j : Fin 3, stamp.recordExponent j ≤ N) :
    getRecordExp stamp i ≤ N := by
  unfold getRecordExp
  split_ifs with hi
  · exact h ⟨i, hi⟩
  · exact Nat.zero_le N

theorem extractNodeReqsAux_recordExp (stamp : ComputeTimestampRow) (i : ℕ)
    (rs : List (ServiceReq K)) (r : MemRecordReq)
    (hr : r ∈ extractNodeReqsAux stamp i rs) :
    ∃ k, r.recordExp = getRecordExp stamp k := by
  induction rs generalizing i with
  | nil => simp [extractNodeReqsAux] at hr
  | cons _req rs ih =>
    simp [extractNodeReqsAux] at hr
    rcases hr with h | h
    · subst r
      exact ⟨i, rfl⟩
    · exact ih (i + 1) h

theorem extractNodeReqs_recordExp (g : GenComputeRow K) (r : MemRecordReq)
    (hr : r ∈ extractNodeReqs g) :
    ∃ k, r.recordExp = getRecordExp g.stamp k :=
  extractNodeReqsAux_recordExp g.stamp 0 g.requests r hr

theorem inTree_walk_exp_eq_zero (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n t, InTree (genAnnotatedNounWalk E z lmb n).1 t →
      t.label.stamp.recordExponent = 0
  | .atom _a, t, ht => by
      cases ht with
      | here => simp [genAnnotatedNounWalk, NTree.label, gMemRow9]
      | sub hs _ => simp [genAnnotatedNounWalk, NTree.children] at hs
  | .cell h tl, t, ht => by
      cases ht with
      | here => simp [genAnnotatedNounWalk, NTree.label, gMemRow9]
      | sub hs hu =>
        simp [genAnnotatedNounWalk, NTree.children_node, List.mem_cons,
          List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact inTree_walk_exp_eq_zero E z h _ hu
        · exact inTree_walk_exp_eq_zero E z tl _ hu

theorem inTree_verify_exp_le (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ)
    (t : NTree (GenMemoryRow K))
    (ht : InTree (genAnnotatedVerify E z lmb root child ax ts recordExp).1 t) :
    t.label.stamp.recordExponent ≤ recordExp := by
  cases ht with
  | here =>
    simp [genAnnotatedVerify, NTree.label, gMemRow9]
  | sub hs hu =>
    simp [genAnnotatedVerify, NTree.children_node, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    subst hs
    have hz := inTree_walk_exp_eq_zero E z child _ hu
    simp [hz]

theorem inTree_descent_exp_le (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ) :
    ∀ remainingAxis currentNoun u,
      u ∈ (genAnnotatedDescent E z lmb root child recAxis ts recordExp
            currentNoun remainingAxis).1 →
      ∀ t, InTree u t → t.label.stamp.recordExponent ≤ recordExp := by
  intro remainingAxis
  induction remainingAxis using Nat.strongRecOn with
  | ind n ih =>
    intro currentNoun u hu t ht
    unfold genAnnotatedDescent at hu
    split at hu
    · rename_i hlt
      simp [genAnnotatedVerify] at hu
      subst u
      exact inTree_verify_exp_le E z root child recAxis ts recordExp t ht
    · rename_i hge
      split at hu
      · simp at hu
        subst u
        cases ht with
        | here =>
          simp [NTree.label, gMemRow9]
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_cons, List.mem_append] at hs
          rcases hs with rfl | hs
          · have hz := inTree_walk_exp_eq_zero E z (formulaHead currentNoun) _ hu'
            simp [hz]
          · have hrest : axisRest n < n := axisRest_lt (Nat.le_of_not_gt hge)
            exact ih (axisRest n) hrest (formulaTail currentNoun) _ hs t hu'
      · simp at hu
        subst u
        cases ht with
        | here =>
          simp [NTree.label, gMemRow9]
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_cons, List.mem_append,
            List.not_mem_nil, or_false] at hs
          rcases hs with hs | rfl
          · have hrest : axisRest n < n := axisRest_lt (Nat.le_of_not_gt hge)
            exact ih (axisRest n) hrest (formulaHead currentNoun) _ hs t hu'
          · have hz := inTree_walk_exp_eq_zero E z (formulaTail currentNoun) _ hu'
            simp [hz]

theorem inTree_record_exp_le (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis recordExp : ℕ)
    (t : NTree (GenMemoryRow K))
    (ht : InTree (genAnnotatedRecordTree E z α lmb root child axis recordExp) t) :
    t.label.stamp.recordExponent ≤ recordExp := by
  rw [show genAnnotatedRecordTree E z α lmb root child axis recordExp =
        .node (gMemRow9 (memReadSkelAx root child axis) recordExp z
          (annotatedReadPub E root child axis (α ^ recordExp)
            (genAnnotatedDescent E z lmb root child axis (α ^ recordExp)
              recordExp root axis).2 0 0 lmb))
          (genAnnotatedDescent E z lmb root child axis (α ^ recordExp)
            recordExp root axis).1 from rfl] at ht
  cases ht with
  | here =>
    simp [NTree.label, gMemRow9]
  | sub hs hu =>
    exact inTree_descent_exp_le E z root child axis (α ^ recordExp) recordExp
      axis root _ hs t hu

theorem inTree_descentCont_exp_le (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) (N : ℕ)
    (hcont : ∀ u ∈ cont, ∀ t, InTree u t → t.label.stamp.recordExponent ≤ N) :
    ∀ remainingAxis currentNoun u,
      u ∈ (genAnnotatedDescentCont E z lmb cont contCell contState
            currentNoun remainingAxis).1 →
      ∀ t, InTree u t → t.label.stamp.recordExponent ≤ N := by
  intro remainingAxis
  induction remainingAxis using Nat.strongRecOn with
  | ind n ih =>
    intro currentNoun u hu t ht
    unfold genAnnotatedDescentCont at hu
    split at hu
    · exact hcont u hu t ht
    · rename_i hge
      split at hu
      · simp at hu
        subst u
        cases ht with
        | here =>
          simp [NTree.label, gMemRow9]
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_cons, List.mem_append] at hs
          rcases hs with rfl | hs
          · have hz := inTree_walk_exp_eq_zero E z (formulaHead currentNoun) _ hu'
            simp [hz]
          · have hrest : axisRest n < n := axisRest_lt (Nat.le_of_not_gt hge)
            exact ih (axisRest n) hrest (formulaTail currentNoun) _ hs t hu'
      · simp at hu
        subst u
        cases ht with
        | here =>
          simp [NTree.label, gMemRow9]
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_cons, List.mem_append,
            List.not_mem_nil, or_false] at hs
          rcases hs with hs | rfl
          · have hrest : axisRest n < n := axisRest_lt (Nat.le_of_not_gt hge)
            exact ih (axisRest n) hrest (formulaHead currentNoun) _ hs t hu'
          · have hz := inTree_walk_exp_eq_zero E z (formulaTail currentNoun) _ hu'
            simp [hz]

theorem inTree_chainedInner_exp_le (E : Noun → ComputeTable.FP K) (z α : K)
    (prev : MemRecordReq) (N : ℕ) (hp : prev.recordExp ≤ N) :
    ∀ rest,
      (∀ r ∈ rest, r.recordExp ≤ N) →
      ∀ u ∈ (genAnnotatedChainedInner E z α lmb prev rest).1,
        ∀ t, InTree u t → t.label.stamp.recordExponent ≤ N
  | [], _hr, u, hu, t, ht => by
      simp [genAnnotatedChainedInner, genAnnotatedVerify] at hu
      subst u
      have hle := inTree_verify_exp_le E z prev.root prev.child prev.axis
        (α ^ prev.recordExp) prev.recordExp t ht
      exact le_trans hle hp
  | r :: more, hr, u, hu, t, ht => by
      simp [genAnnotatedChainedInner] at hu
      subst u
      cases ht with
      | here =>
        simp [NTree.label, gMemRow9]
        exact hr r (List.mem_cons.mpr (Or.inl rfl))
      | sub hs hu' =>
        simp [NTree.children_node, List.mem_cons, List.not_mem_nil,
          or_false] at hs
        subst hs
        cases hu' with
        | here =>
          simp [NTree.label, gMemRow9]
          exact hp
        | sub hs' hu'' =>
          refine inTree_descentCont_exp_le E z
              (genAnnotatedChainedInner E z α lmb r more).1
              (genAnnotatedChainedInner E z α lmb r more).2
              (chainedInnerRootState more) N ?_ r.axis r.root _ hs' t hu''
          intro v hv s hs
          exact inTree_chainedInner_exp_le E z α r N
            (hr r (List.mem_cons.mpr (Or.inl rfl))) more
            (fun x hx => hr x (List.mem_cons.mpr (Or.inr hx))) v hv s hs

theorem inTree_chainedTree_exp_le (E : Noun → ComputeTable.FP K) (z α : K)
    (reqs : List MemRecordReq) (N : ℕ)
    (h : ∀ r ∈ reqs, r.recordExp ≤ N)
    (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z α lmb reqs = some t)
    (s : NTree (GenMemoryRow K)) (hs : InTree t s) :
    s.label.stamp.recordExponent ≤ N := by
  match reqs with
  | [] => simp [genAnnotatedChainedTree] at ht
  | [r] =>
    simp [genAnnotatedChainedTree] at ht
    subst t
    have hle := inTree_record_exp_le E z α r.root r.child r.axis r.recordExp s hs
    exact le_trans hle (h r (by simp))
  | r :: r2 :: rest =>
    simp [genAnnotatedChainedTree] at ht
    subst t
    cases hs with
    | here =>
      simp [NTree.label, gMemRow9]
      exact h r (by simp)
    | sub hu ht' =>
      refine inTree_descentCont_exp_le E z
          (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).1
          (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).2
          (chainedInnerRootState (r2 :: rest)) N ?_ r.axis r.root _ hu s ht'
      intro v hv w hw
      exact inTree_chainedInner_exp_le E z α r N (h r (by simp)) (r2 :: rest)
        (fun x hx => h x (List.mem_cons.mpr (Or.inr hx))) v hv w hw

theorem inTree_rowMemForest_exp_le (E : Noun → ComputeTable.FP K) (z α : K)
    (N : ℕ) :
    ∀ rs : List MemRecordReq,
      (∀ r ∈ rs, r.recordExp ≤ N) →
      ∀ u ∈ genRowMemForest E z α lmb rs,
        ∀ t, InTree u t → t.label.stamp.recordExponent ≤ N
  | [], _, u, hu, t, _ => by simp [genRowMemForest] at hu
  | [r], h, u, hu, t, ht => by
      simp [genRowMemForest] at hu
      subst u
      have hle := inTree_record_exp_le E z α r.root r.child r.axis r.recordExp t ht
      exact le_trans hle (h r (by simp))
  | [r1, r2], h, u, hu, t, ht => by
      simp only [genRowMemForest] at hu
      by_cases hc : r1.child = r2.root
      · rw [if_pos hc] at hu
        cases hch : genAnnotatedChainedTree E z α lmb [r1, r2] with
        | none =>
          rw [hch] at hu
          simp at hu
          rcases hu with rfl | rfl
          · have hle := inTree_record_exp_le E z α r1.root r1.child r1.axis
              r1.recordExp t ht
            exact le_trans hle (h r1 (by simp))
          · have hle := inTree_record_exp_le E z α r2.root r2.child r2.axis
              r2.recordExp t ht
            exact le_trans hle (h r2 (by simp))
        | some tree =>
          rw [hch] at hu
          simp at hu
          subst u
          exact inTree_chainedTree_exp_le E z α [r1, r2] N h tree hch t ht
      · rw [if_neg hc] at hu
        simp at hu
        rcases hu with rfl | rfl
        · have hle := inTree_record_exp_le E z α r1.root r1.child r1.axis
            r1.recordExp t ht
          exact le_trans hle (h r1 (by simp))
        · have hle := inTree_record_exp_le E z α r2.root r2.child r2.axis
            r2.recordExp t ht
          exact le_trans hle (h r2 (by simp))
  | [r1, r2, r3], h, u, hu, t, ht => by
      rw [genRowMemForest_three_eq] at hu
      simp [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact inTree_rowMemForest_exp_le E z α N [r1, r2]
          (fun r hr => h r (by
            simp at hr
            rcases hr with rfl | rfl <;> simp)) u hu t ht
      · have hle := inTree_record_exp_le E z α r3.root r3.child r3.axis
          r3.recordExp t ht
        exact le_trans hle (h r3 (by simp))
  | r1 :: r2 :: r3 :: r4 :: rest, h, u, hu, t, ht => by
      unfold genRowMemForest at hu
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
      have hle := inTree_record_exp_le E z α r.root r.child r.axis r.recordExp t ht
      exact le_trans hle (h r hr)

theorem genMemForestFromTree_exp_le (E : Noun → ComputeTable.FP K) (z α : K)
    (N : ℕ) (t : NTree (GenComputeRow K))
    (H : ∀ n, InTree t n → ∀ r ∈ extractNodeReqs n.label, r.recordExp ≤ N)
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ genMemForestFromTree E z α lmb t)
    (s : NTree (GenMemoryRow K)) (hs : InTree u s) :
    s.label.stamp.recordExponent ≤ N := by
  suffices ∀ M t,
      NTree.size t ≤ M →
      (∀ n, InTree t n → ∀ r ∈ extractNodeReqs n.label, r.recordExp ≤ N) →
      ∀ u ∈ genMemForestFromTree E z α lmb t,
        ∀ s, InTree u s → s.label.stamp.recordExponent ≤ N from
    this (NTree.size t) t le_rfl H u hu s hs
  intro M
  induction M with
  | zero =>
    intro t ht _H u _hu s _hs
    cases t with
    | node g cs =>
      simp [NTree.size] at ht
  | succ M ih =>
    intro t ht H u hu s hs
    cases t with
    | node g cs =>
      simp [genMemForestFromTree] at hu
      rcases hu with hu | hu
      · exact inTree_rowMemForest_exp_le E z α N (extractNodeReqs g)
          (H (.node g cs) (InTree.here _)) u hu s hs
      · have recList :
            ∀ cs', (∀ c ∈ cs', c ∈ cs) →
              (∀ t ∈ cs', NTree.size t ≤ M) →
              (∀ t ∈ cs', ∀ n, InTree t n →
                ∀ r ∈ extractNodeReqs n.label, r.recordExp ≤ N) →
              ∀ u ∈ genMemForestFromList E z α lmb cs',
                ∀ s, InTree u s → s.label.stamp.recordExponent ≤ N := by
          intro cs' hsub hsz H' u' hu' s' hs'
          induction cs' generalizing u' s' with
          | nil => simp [genMemForestFromList] at hu'
          | cons c rest ihcs =>
            simp [genMemForestFromList] at hu'
            rcases hu' with hu' | hu'
            · exact ih c (hsz c (by simp))
                (fun n hn => H' c (by simp) n hn) u' hu' s' hs'
            · refine ihcs ?_ ?_ ?_ u' hu' s' hs'
              · intro c' hc'; exact hsub c' (List.mem_cons_of_mem _ hc')
              · intro t htt; exact hsz t (List.mem_cons_of_mem _ htt)
              · intro t htt; exact H' t (List.mem_cons_of_mem _ htt)
        refine recList cs (fun _ h => h) ?_
            (fun t htt n hn => H n (InTree.sub htt hn)) u hu s hs
        intro c hc
        have hin : NTree.size c ∈ cs.map NTree.size :=
          List.mem_map.mpr ⟨c, hc, rfl⟩
        have hsum : NTree.size c ≤ (cs.map NTree.size).sum :=
          List.le_sum_of_mem hin
        simp [NTree.size] at ht
        omega

theorem bfsAssign_extract_recordExp_le (t : NTree (GenComputeRow K))
    (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign t) n) (r : MemRecordReq)
    (hr : r ∈ extractNodeReqs n.label) :
    r.recordExp ≤ accAt t (bfsRows t).length + 3 := by
  have hnF : n ∈ bfsForest [bfsAssign t] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hmem : n.label ∈ (bfsForest [bfsAssign t]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [bfsAssign_bfsForest_labels] at hmem
  obtain ⟨i, hi, hieq⟩ := List.mem_map.mp hmem
  have hi' := lt_bfsRows_of_mem_range' hi
  obtain ⟨k, hk⟩ := extractNodeReqs_recordExp n.label r hr
  have hstamp : ∀ j : Fin 3, n.label.stamp.recordExponent j ≤
      accAt t (i - 1) + 3 := by
    intro j
    rw [← hieq]
    exact bfsLabelAt_recordExponent_le t i hi' j
  have hle : r.recordExp ≤ accAt t (i - 1) + 3 := by
    rw [hk]
    exact getRecordExp_le n.label.stamp _ k hstamp
  have hiacc : accAt t (i - 1) ≤ accAt t (bfsRows t).length :=
    accAt_mono t _ _ (Nat.le_of_lt hi')
  omega

/-! ## Request-slot schedule -- the paper -/

theorem zip_map_same {α β γ : Type*} (f : α → β) (g : α → γ) :
    ∀ l : List α, (l.map f).zip (l.map g) = l.map (fun a => (f a, g a))
  | [] => rfl
  | _ :: l => by simp [List.zip_cons_cons, zip_map_same f g l]

theorem ofFn_fin3 {α} (f : Fin 3 → α) : List.ofFn f = [f 0, f 1, f 2] := by
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp

def rowSlots (g : GenComputeRow K) : List CanonicalRecordSlot :=
  (List.ofFn fun i : Fin 3 =>
    if h : (i : ℕ) < Nock.Framework.recordCount g.skel.state then
      some
        ({ record := g.skel.memoryRecord i h
           exponent := g.stamp.recordExponent i } : CanonicalRecordSlot)
    else none).filterMap id

theorem recordCount_eq_123 (s : ComputeTable.State) :
    Nock.Framework.recordCount s = 1 ∨
      Nock.Framework.recordCount s = 2 ∨
        Nock.Framework.recordCount s = 3 := by
  have hpos := Nock.Framework.recordCount_pos s
  have hle := Nock.Framework.recordCount_le s
  simp [Nock.NockVM.mem_record_arity] at hle
  omega

theorem rowSlots_length (g : GenComputeRow K) :
    (rowSlots g).length = Nock.Framework.recordCount g.skel.state := by
  unfold rowSlots
  rw [ofFn_fin3]
  rcases recordCount_eq_123 g.skel.state with hn | hn | hn
  · have h0 : (0 : ℕ) < 1 := Nat.zero_lt_one
    have n1 : ¬ (1 : ℕ) < 1 := Nat.lt_irrefl 1
    have n2 : ¬ (2 : ℕ) < 1 := by omega
    simp [hn, h0, n1, n2]
  · have h0 : (0 : ℕ) < 2 := by omega
    have h1 : (1 : ℕ) < 2 := by omega
    have n2 : ¬ (2 : ℕ) < 2 := Nat.lt_irrefl 2
    simp [hn, h0, h1, n2]
  · have h0 : (0 : ℕ) < 3 := by omega
    have h1 : (1 : ℕ) < 3 := by omega
    have h2 : (2 : ℕ) < 3 := by omega
    simp [hn, h0, h1, h2]

theorem rowSlots_exponents_of (g : GenComputeRow K) {acc : ℕ}
    (hst : g.stamp = stampOfAcc g.skel.state acc) :
    (rowSlots g).map CanonicalRecordSlot.exponent =
      (List.range (Nock.Framework.recordCount g.skel.state)).map
        (fun i => acc + i + 1) := by
  unfold rowSlots
  rw [ofFn_fin3, hst]
  have hexp (i : Fin 3)
      (hi : (i : ℕ) < Nock.Framework.recordCount g.skel.state) :
      (stampOfAcc g.skel.state acc).recordExponent i =
        acc + (i : ℕ) + 1 :=
    stampOfAcc_recordExponent _ _ i hi
  rcases recordCount_eq_123 g.skel.state with hn | hn | hn
  · have h0 : (0 : ℕ) < 1 := Nat.zero_lt_one
    have n1 : ¬ (1 : ℕ) < 1 := Nat.lt_irrefl 1
    have n2 : ¬ (2 : ℕ) < 1 := by omega
    have h0rc : (0 : ℕ) < Nock.Framework.recordCount g.skel.state := by omega
    simp [hn, h0, n1, n2, hexp 0 h0rc, List.range_succ, List.range_zero]
  · have h0 : (0 : ℕ) < 2 := by omega
    have h1 : (1 : ℕ) < 2 := by omega
    have n2 : ¬ (2 : ℕ) < 2 := Nat.lt_irrefl 2
    have h0rc : (0 : ℕ) < Nock.Framework.recordCount g.skel.state := by omega
    have h1rc : (1 : ℕ) < Nock.Framework.recordCount g.skel.state := by omega
    simp [hn, h0, h1, n2, hexp 0 h0rc, hexp 1 h1rc, List.range_succ,
      List.range_zero]
  · have h0 : (0 : ℕ) < 3 := by omega
    have h1 : (1 : ℕ) < 3 := by omega
    have h2 : (2 : ℕ) < 3 := by omega
    have h0rc : (0 : ℕ) < Nock.Framework.recordCount g.skel.state := by omega
    have h1rc : (1 : ℕ) < Nock.Framework.recordCount g.skel.state := by omega
    have h2rc : (2 : ℕ) < Nock.Framework.recordCount g.skel.state := by omega
    simp [hn, h0, h1, h2, hexp 0 h0rc, hexp 1 h1rc, hexp 2 h2rc,
      List.range_succ, List.range_zero]

theorem genSemanticRequests_eq_bfs (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    genSemanticRequests (genSemanticSkeleton (bfsAssign t) mf)
      (bfsStamps (bfsAssign t)) =
      ((List.range' 1 (bfsForest [t]).length).map (bfsLabelAt t)).flatMap
        rowSlots := by
  simp only [genSemanticRequests, rowSlots]
  rw [computeSkeletonRows_genSemantic, computeSkeletonRows_genCompute,
    bfsStamps_bfsAssign]
  have hskel :
      (bfsForest [bfsAssign t]).map (fun n => n.label.skel) =
        (List.range' 1 (bfsForest [t]).length).map
          (fun i => (bfsLabelAt t i).skel) := by
    convert congrArg (List.map (fun g : GenComputeRow K => g.skel))
      (bfsAssign_bfsForest_labels t) using 1 <;>
      (rw [List.map_map]; rfl)
  rw [hskel, zip_map_same]
  have hpair :
      (List.range' 1 (bfsForest [t]).length).map
          (fun i => ((bfsLabelAt t i).skel, (bfsLabelAt t i).stamp)) =
        ((List.range' 1 (bfsForest [t]).length).map (bfsLabelAt t)).map
          (fun g => (g.skel, g.stamp)) := by
    rw [List.map_map]
    rfl
  rw [hpair, List.flatMap_map]
  rfl

theorem range'_eq_succ_range (n : ℕ) :
    List.range' 1 n = (List.range n).map Nat.succ := by
  simp [List.range'_eq_map_range, Nat.add_comm]

theorem prefixSlots_length_exponents (t : NTree (GenComputeRow K)) :
    ∀ k, k ≤ (bfsRows t).length →
      (((List.range k).map (fun j => bfsLabelAt t (j + 1))).flatMap rowSlots).length =
        accAt t k ∧
      (((List.range k).map (fun j => bfsLabelAt t (j + 1))).flatMap
          rowSlots).map CanonicalRecordSlot.exponent =
        (List.range (accAt t k)).map (fun i => i + 1)
  | 0, _ => by
      simp [accAt, List.range_zero]
  | k + 1, hk => by
      have hk' : k < (bfsRows t).length := Nat.lt_of_succ_le hk
      have hih := prefixSlots_length_exponents t k (Nat.le_of_lt hk')
      have hi : k < (bfsRows t).length := hk'
      have hk1 : k + 1 - 1 = k := rfl
      have hst0 := bfsLabelAt_stamp t (k + 1) (by simpa using hi)
      have hskel0 := bfsLabelAt_skel t (k + 1) (by simpa using hi)
      simp [hk1] at hst0 hskel0
      have hst : (bfsLabelAt t (k + 1)).stamp =
          stampOfAcc (bfsLabelAt t (k + 1)).skel.state (accAt t k) := by
        rw [hst0, hskel0]
      have hlen_row := rowSlots_length (bfsLabelAt t (k + 1))
      have hexp := rowSlots_exponents_of (bfsLabelAt t (k + 1)) hst
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      constructor
      · have hacc := accAt_succ_of_lt t k hk'
        rw [List.length_append, hih.1, hlen_row, hskel0, hacc]
      · have hacc := accAt_succ_of_lt t k hk'
        have hfun : (fun i : ℕ => accAt t k + i + 1) =
            (fun i => i + 1) ∘ (fun x => accAt t k + x) := by
          funext i
          simp [Function.comp]
        rw [List.map_append, hih.2, hexp, hskel0, hfun, hacc, List.range_add,
          List.map_append, List.map_map]

theorem genSemanticRequests_length_eq_accAt (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    (genSemanticRequests (genSemanticSkeleton (bfsAssign t) mf)
      (bfsStamps (bfsAssign t))).length =
      accAt t (bfsRows t).length := by
  rw [genSemanticRequests_eq_bfs, range'_eq_succ_range, List.map_map,
    ← bfsRows_length]
  exact (prefixSlots_length_exponents t (bfsRows t).length le_rfl).1

theorem genSemanticRequests_exponents (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    (genSemanticRequests (genSemanticSkeleton (bfsAssign t) mf)
      (bfsStamps (bfsAssign t))).map CanonicalRecordSlot.exponent =
      (List.range (accAt t (bfsRows t).length)).map (fun i => i + 1) := by
  rw [genSemanticRequests_eq_bfs, range'_eq_succ_range, List.map_map,
    ← bfsRows_length]
  exact (prefixSlots_length_exponents t (bfsRows t).length le_rfl).2

theorem accAt_length_pos (t : NTree (GenComputeRow K))
    (h : 0 < (bfsRows t).length) :
    1 ≤ accAt t (bfsRows t).length := by
  have h1 : accAt t 1 ≤ accAt t (bfsRows t).length :=
    accAt_mono t 1 _ (Nat.succ_le_of_lt h)
  have hacc : accAt t 1 =
      Nock.Framework.recordCount (bfsRows t)[0].skel.state := by
    rw [accAt_succ_of_lt t 0 h, accAt]
    omega
  have hpos : 1 ≤ Nock.Framework.recordCount (bfsRows t)[0].skel.state :=
    Nock.Framework.recordCount_pos _
  omega

/-! ## Serving identity: request triples match skeleton memory records -- the paper -/

def requestTriples (g : GenComputeRow K) : List (Noun × Noun × ℕ) :=
  g.requests.map fun r => (r.root, r.child, r.axis)

def recTriple (rec : MemRecSkeleton) : Noun × Noun × ℕ :=
  (rec.root, rec.child, rec.axis)

def memoryTriples (g : GenComputeRow K) : List (Noun × Noun × ℕ) :=
  (List.ofFn fun i : Fin 3 =>
    if h : (i : ℕ) < Nock.Framework.recordCount g.skel.state then
      some (recTriple (g.skel.memoryRecord i h))
    else none).filterMap id

def requestsMatchMemory (g : GenComputeRow K) : Prop :=
  requestTriples g = memoryTriples g

def treeRequestsMatch (t : NTree (GenComputeRow K)) : Prop :=
  ∀ n, InTree t n → requestsMatchMemory n.label

theorem treeRequestsMatch_node (g : GenComputeRow K)
    (cs : List (NTree (GenComputeRow K)))
    (hg : requestsMatchMemory g)
    (hcs : ∀ c ∈ cs, treeRequestsMatch c) :
    treeRequestsMatch (.node g cs) := by
  intro n hn
  cases hn with
  | here => exact hg
  | sub hs hst => exact hcs _ hs n hst

theorem memoryTriples_of_count1 (g : GenComputeRow K)
    (hc : Nock.Framework.recordCount g.skel.state = 1) :
    memoryTriples g = [recTriple (g.skel.memoryRecord 0 (by omega))] := by
  unfold memoryTriples recTriple
  rw [ofFn_fin3]
  simp [hc]

theorem memoryTriples_of_count2 (g : GenComputeRow K)
    (hc : Nock.Framework.recordCount g.skel.state = 2) :
    memoryTriples g =
      [recTriple (g.skel.memoryRecord 0 (by omega)),
       recTriple (g.skel.memoryRecord 1 (by omega))] := by
  unfold memoryTriples recTriple
  rw [ofFn_fin3]
  simp [hc]

theorem memoryTriples_of_count3 (g : GenComputeRow K)
    (hc : Nock.Framework.recordCount g.skel.state = 3) :
    memoryTriples g =
      [recTriple (g.skel.memoryRecord 0 (by omega)),
       recTriple (g.skel.memoryRecord 1 (by omega)),
       recTriple (g.skel.memoryRecord 2 (by omega))] := by
  unfold memoryTriples recTriple
  rw [ofFn_fin3]
  simp [hc]

theorem match_cons (subject leftF rightF leftR rightR : Noun) :
    requestsMatchMemory (K := K)
      (skelNode (genSkelCons subject leftF rightF leftR rightR)
        [⟨.cell leftF rightF, rightF, 3, 0⟩]) := by
  unfold requestsMatchMemory requestTriples
  rw [memoryTriples_of_count1 _ (by simp [skelNode, genSkelCons,
    Nock.Framework.recordCount])]
  simp [skelNode, genSkelCons, recTriple]

theorem match_op1 (subject formula result head : Noun) :
    requestsMatchMemory (K := K)
      (skelNode (genSkelOp1 subject formula result head)
        [⟨formula, result, 3, 0⟩]) := by
  unfold requestsMatchMemory requestTriples
  rw [memoryTriples_of_count1 _ (by simp [skelNode, genSkelOp1,
    Nock.Framework.recordCount])]
  simp [skelNode, genSkelOp1, recTriple]

theorem match_op3 (subject formula head tail callSubject callFormula
    callResult result : Noun) :
    requestsMatchMemory (K := K)
      (skelNode (genSkelOp3 subject formula head tail callSubject callFormula
          callResult result)
        [⟨formula, tail, 3, 0⟩]) := by
  unfold requestsMatchMemory requestTriples
  rw [memoryTriples_of_count1 _ (by simp [skelNode, genSkelOp3,
    Nock.Framework.recordCount])]
  simp [skelNode, genSkelOp3, recTriple]

theorem match_op4 (subject formula head tail callSubject callFormula
    callResult result : Noun) :
    requestsMatchMemory (K := K)
      (skelNode (genSkelOp4 subject formula head tail callSubject callFormula
          callResult result)
        [⟨formula, tail, 3, 0⟩]) := by
  unfold requestsMatchMemory requestTriples
  rw [memoryTriples_of_count1 _ (by simp [skelNode, genSkelOp4,
    Nock.Framework.recordCount])]
  simp [skelNode, genSkelOp4, recTriple]

theorem match_op0 (subject formula head tail result : Noun) (axis : ℕ) :
    requestsMatchMemory (K := K)
      (skelNode (genSkelOp0 subject formula head tail result axis)
        [⟨formula, tail, 3, 0⟩, ⟨subject, result, axis, 0⟩]) := by
  unfold requestsMatchMemory requestTriples
  rw [memoryTriples_of_count2 _ (by simp [skelNode, genSkelOp0,
    Nock.Framework.recordCount])]
  simp [skelNode, genSkelOp0, recTriple]

theorem match_op2 (subject formula head fTail fTh fTt sf1 sf2 result : Noun) :
    requestsMatchMemory (K := K)
      (skelNode (genSkelOp2 subject formula head fTail fTh fTt sf1 sf2 result)
        [⟨formula, fTail, 3, 0⟩, ⟨fTail, fTh, 2, 0⟩]) := by
  unfold requestsMatchMemory requestTriples
  rw [memoryTriples_of_count2 _ (by simp [skelNode, genSkelOp2,
    Nock.Framework.recordCount])]
  simp [skelNode, genSkelOp2, recTriple]

theorem match_op5 (subject formula head fTail fTh fTt sf1 sf2 result : Noun) :
    requestsMatchMemory (K := K)
      (skelNode (genSkelOp5 subject formula head fTail fTh fTt sf1 sf2 result)
        [⟨formula, fTail, 3, 0⟩, ⟨fTail, fTh, 2, 0⟩]) := by
  unfold requestsMatchMemory requestTriples
  rw [memoryTriples_of_count2 _ (by simp [skelNode, genSkelOp5,
    Nock.Framework.recordCount])]
  simp [skelNode, genSkelOp5, recTriple]

theorem match_op7 (subject formula head fTail fTh fTt sb result : Noun) :
    requestsMatchMemory (K := K)
      (skelNode (genSkelOp7 subject formula head fTail fTh fTt sb result)
        [⟨formula, fTail, 3, 0⟩, ⟨fTail, fTh, 2, 0⟩]) := by
  unfold requestsMatchMemory requestTriples
  rw [memoryTriples_of_count2 _ (by simp [skelNode, genSkelOp7,
    Nock.Framework.recordCount])]
  simp [skelNode, genSkelOp7, recTriple]

theorem match_op8 (subject formula head fTail fTh fTt sb result : Noun) :
    requestsMatchMemory (K := K)
      (skelNode (genSkelOp8 subject formula head fTail fTh fTt sb result)
        [⟨formula, fTail, 3, 0⟩, ⟨fTail, fTh, 2, 0⟩]) := by
  unfold requestsMatchMemory requestTriples
  rw [memoryTriples_of_count2 _ (by simp [skelNode, genSkelOp8,
    Nock.Framework.recordCount])]
  simp [skelNode, genSkelOp8, recTriple]

theorem match_op9 (subject formula head fTail fTh fTt core arm result : Noun)
    (axis : ℕ) :
    requestsMatchMemory (K := K)
      (skelNode (genSkelOp9 subject formula head fTail fTh fTt core arm result
          axis)
        [⟨formula, fTail, 3, 0⟩, ⟨fTail, fTh, 2, 0⟩, ⟨core, arm, axis, 0⟩]) := by
  unfold requestsMatchMemory requestTriples
  rw [memoryTriples_of_count3 _ (by simp [skelNode, genSkelOp9,
    Nock.Framework.recordCount])]
  simp [skelNode, genSkelOp9, recTriple]

theorem match_op6 (subject formula head fTail fTh fTt fTth fTtt cond taken
    result : Noun) :
    requestsMatchMemory (K := K)
      (skelNode (genSkelOp6 subject formula head fTail fTh fTt fTth fTtt cond
          taken result)
        [⟨formula, fTail, 3, 0⟩, ⟨fTail, fTh, 2, 0⟩, ⟨fTt, fTth, 2, 0⟩]) := by
  unfold requestsMatchMemory requestTriples
  rw [memoryTriples_of_count3 _ (by simp [skelNode, genSkelOp6,
    Nock.Framework.recordCount])]
  simp [skelNode, genSkelOp6, recTriple]

theorem rowSlots_of_count1 (g : GenComputeRow K)
    (hc : Nock.Framework.recordCount g.skel.state = 1) :
    rowSlots g =
      [{ record := g.skel.memoryRecord 0 (by omega)
         exponent := g.stamp.recordExponent 0 }] := by
  unfold rowSlots
  rw [ofFn_fin3]
  simp [hc]

theorem rowSlots_of_count2 (g : GenComputeRow K)
    (hc : Nock.Framework.recordCount g.skel.state = 2) :
    rowSlots g =
      [{ record := g.skel.memoryRecord 0 (by omega)
         exponent := g.stamp.recordExponent 0 },
       { record := g.skel.memoryRecord 1 (by omega)
         exponent := g.stamp.recordExponent 1 }] := by
  unfold rowSlots
  rw [ofFn_fin3]
  simp [hc]

theorem rowSlots_of_count3 (g : GenComputeRow K)
    (hc : Nock.Framework.recordCount g.skel.state = 3) :
    rowSlots g =
      [{ record := g.skel.memoryRecord 0 (by omega)
         exponent := g.stamp.recordExponent 0 },
       { record := g.skel.memoryRecord 1 (by omega)
         exponent := g.stamp.recordExponent 1 },
       { record := g.skel.memoryRecord 2 (by omega)
         exponent := g.stamp.recordExponent 2 }] := by
  unfold rowSlots
  rw [ofFn_fin3]
  simp [hc]

set_option maxHeartbeats 800000 in
theorem genComputeSkeleton_tree_requests_match :
    ∀ {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow K)} {r : Noun},
      genComputeSkeleton (K := K) fuel subject formula = .ok (t, r) →
      treeRequestsMatch t := by
  intro fuel
  induction fuel with
  | zero =>
    intro subject formula t r h
    simp [genComputeSkeleton] at h
  | succ n ih =>
    intro subject formula t r h
    cases formula with
    | atom _ =>
      simp [genComputeSkeleton] at h
    | cell hd tl =>
      cases hd with
      | cell lh lt =>
        cases hL : genComputeSkeleton (K := K) n subject (.cell lh lt) with
        | error e => simp [genComputeSkeleton, hL] at h
        | ok pr =>
          obtain ⟨lTree, lRes⟩ := pr
          cases hR : genComputeSkeleton (K := K) n subject tl with
          | error e => simp [genComputeSkeleton, hL, hR] at h
          | ok pr =>
            obtain ⟨rTree, rRes⟩ := pr
            simp [genComputeSkeleton, hL, hR] at h
            obtain ⟨ht, _⟩ := h
            subst t
            refine treeRequestsMatch_node _ _ ?_ ?_
            · exact match_cons subject (.cell lh lt) tl lRes rRes
            · intro c hc
              simp at hc
              rcases hc with rfl | rfl
              · exact ih hL
              · exact ih hR
      | atom op =>
        match op with
        | 0 =>
          cases tl with
          | atom ax =>
            cases hs : Noun.slot ax subject with
            | none => simp [genComputeSkeleton, hs] at h
            | some result =>
              simp [genComputeSkeleton, hs] at h
              obtain ⟨ht, _⟩ := h
              subst t
              refine treeRequestsMatch_node _ _ ?_ (by intro c hc; simp at hc)
              exact match_op0 subject (.cell (.atom 0) (.atom ax)) (.atom 0)
                (.atom ax) result ax
          | cell _ _ => simp [genComputeSkeleton] at h
        | 1 =>
          simp [genComputeSkeleton] at h
          obtain ⟨ht, _⟩ := h
          subst t
          refine treeRequestsMatch_node _ _ ?_ (by intro c hc; simp at hc)
          exact match_op1 subject (.cell (.atom 1) tl) tl (.atom 1)
        | 2 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pr =>
              obtain ⟨bTree, sf1⟩ := pr
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error e => simp [genComputeSkeleton, hB, hC] at h
              | ok pr =>
                obtain ⟨cTree, sf2⟩ := pr
                cases hM : genComputeSkeleton (K := K) n sf1 sf2 with
                | error e => simp [genComputeSkeleton, hB, hC, hM] at h
                | ok pr =>
                  obtain ⟨mTree, result⟩ := pr
                  simp [genComputeSkeleton, hB, hC, hM] at h
                  obtain ⟨ht, _⟩ := h
                  subst t
                  refine treeRequestsMatch_node _ _ ?_ ?_
                  · exact match_op2 subject (.cell (.atom 2) (.cell b c)) (.atom 2)
                      (.cell b c) b c sf1 sf2 result
                  · intro ch hc
                    simp at hc
                    rcases hc with rfl | rfl | rfl
                    · exact ih hB
                    · exact ih hC
                    · exact ih hM
        | 3 =>
          cases hC : genComputeSkeleton (K := K) n subject tl with
          | error e => simp [genComputeSkeleton, hC] at h
          | ok pr =>
            obtain ⟨callTree, callResult⟩ := pr
            simp [genComputeSkeleton, hC] at h
            obtain ⟨ht, _⟩ := h
            subst t
            refine treeRequestsMatch_node _ _ ?_ ?_
            · exact match_op3 subject (.cell (.atom 3) tl) (.atom 3) tl subject tl
                callResult (Noun.wut callResult)
            · intro ch hc
              simp at hc
              subst ch
              exact ih hC
        | 4 =>
          cases hC : genComputeSkeleton (K := K) n subject tl with
          | error e => simp [genComputeSkeleton, hC] at h
          | ok pr =>
            obtain ⟨callTree, callResult⟩ := pr
            cases hinc : Noun.lus callResult with
            | none => simp [genComputeSkeleton, hC, hinc] at h
            | some result =>
              simp [genComputeSkeleton, hC, hinc] at h
              obtain ⟨ht, _⟩ := h
              subst t
              refine treeRequestsMatch_node _ _ ?_ ?_
              · exact match_op4 subject (.cell (.atom 4) tl) (.atom 4) tl subject
                  tl callResult result
              · intro ch hc
                simp at hc
                subst ch
                exact ih hC
        | 5 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pr =>
              obtain ⟨bTree, sf1⟩ := pr
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error e => simp [genComputeSkeleton, hB, hC] at h
              | ok pr =>
                obtain ⟨cTree, sf2⟩ := pr
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨ht, _⟩ := h
                subst t
                refine treeRequestsMatch_node _ _ ?_ ?_
                · exact match_op5 subject (.cell (.atom 5) (.cell b c)) (.atom 5)
                    (.cell b c) b c sf1 sf2 (Noun.tis sf1 sf2)
                · intro ch hc
                  simp at hc
                  rcases hc with rfl | rfl
                  · exact ih hB
                  · exact ih hC
        | 6 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b cd =>
            cases cd with
            | atom _ => simp [genComputeSkeleton] at h
            | cell c d =>
              cases hB : genComputeSkeleton (K := K) n subject b with
              | error e => simp [genComputeSkeleton, hB] at h
              | ok pr =>
                obtain ⟨condTree, cond⟩ := pr
                cases cond with
                | cell _ _ => simp [genComputeSkeleton, hB] at h
                | atom cv =>
                  match cv with
                  | 0 =>
                    cases hC : genComputeSkeleton (K := K) n subject c with
                    | error e => simp [genComputeSkeleton, hB, hC] at h
                    | ok pr =>
                      obtain ⟨takenTree, result⟩ := pr
                      simp [genComputeSkeleton, hB, hC] at h
                      obtain ⟨ht, _⟩ := h
                      subst t
                      refine treeRequestsMatch_node _ _ ?_ ?_
                      · exact match_op6 subject
                          (.cell (.atom 6) (.cell b (.cell c d))) (.atom 6)
                          (.cell b (.cell c d)) b (.cell c d) c d (.atom 0) c
                          result
                      · intro ch hc
                        simp at hc
                        rcases hc with rfl | rfl
                        · exact ih hB
                        · exact ih hC
                  | 1 =>
                    cases hD : genComputeSkeleton (K := K) n subject d with
                    | error e => simp [genComputeSkeleton, hB, hD] at h
                    | ok pr =>
                      obtain ⟨takenTree, result⟩ := pr
                      simp [genComputeSkeleton, hB, hD] at h
                      obtain ⟨ht, _⟩ := h
                      subst t
                      refine treeRequestsMatch_node _ _ ?_ ?_
                      · exact match_op6 subject
                          (.cell (.atom 6) (.cell b (.cell c d))) (.atom 6)
                          (.cell b (.cell c d)) b (.cell c d) c d (.atom 1) d
                          result
                      · intro ch hc
                        simp at hc
                        rcases hc with rfl | rfl
                        · exact ih hB
                        · exact ih hD
                  | _ + 2 => simp [genComputeSkeleton, hB] at h
        | 7 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pr =>
              obtain ⟨bTree, sb⟩ := pr
              cases hC : genComputeSkeleton (K := K) n sb c with
              | error e => simp [genComputeSkeleton, hB, hC] at h
              | ok pr =>
                obtain ⟨cTree, result⟩ := pr
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨ht, _⟩ := h
                subst t
                refine treeRequestsMatch_node _ _ ?_ ?_
                · exact match_op7 subject (.cell (.atom 7) (.cell b c)) (.atom 7)
                    (.cell b c) b c sb result
                · intro ch hc
                  simp at hc
                  rcases hc with rfl | rfl
                  · exact ih hB
                  · exact ih hC
        | 8 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pr =>
              obtain ⟨bTree, sb⟩ := pr
              cases hC : genComputeSkeleton (K := K) n (.cell sb subject) c with
              | error e => simp [genComputeSkeleton, hB, hC] at h
              | ok pr =>
                obtain ⟨cTree, result⟩ := pr
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨ht, _⟩ := h
                subst t
                refine treeRequestsMatch_node _ _ ?_ ?_
                · exact match_op8 subject (.cell (.atom 8) (.cell b c)) (.atom 8)
                    (.cell b c) b c sb result
                · intro ch hc
                  simp at hc
                  rcases hc with rfl | rfl
                  · exact ih hB
                  · exact ih hC
        | 9 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell axN c =>
            cases axN with
            | cell _ _ => simp [genComputeSkeleton] at h
            | atom ax =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error e => simp [genComputeSkeleton, hC] at h
              | ok pr =>
                obtain ⟨coreTree, core⟩ := pr
                cases hslot : Noun.slot ax core with
                | none => simp [genComputeSkeleton, hC, hslot] at h
                | some arm =>
                  cases hI : genComputeSkeleton (K := K) n core arm with
                  | error e => simp [genComputeSkeleton, hC, hslot, hI] at h
                  | ok pr =>
                    obtain ⟨invokeTree, result⟩ := pr
                    simp [genComputeSkeleton, hC, hslot, hI] at h
                    obtain ⟨ht, _⟩ := h
                    subst t
                    refine treeRequestsMatch_node _ _ ?_ ?_
                    · exact match_op9 subject
                        (.cell (.atom 9) (.cell (.atom ax) c)) (.atom 9)
                        (.cell (.atom ax) c) (.atom ax) c core arm result ax
                    · intro ch hc
                      simp at hc
                      rcases hc with rfl | rfl
                      · exact ih hC
                      · exact ih hI
        | 10 => simp [genComputeSkeleton] at h
        | 11 => simp [genComputeSkeleton] at h
        | _ + 12 => simp [genComputeSkeleton] at h

def memReqToSlot (r : MemRecordReq) : CanonicalRecordSlot where
  record := ⟨r.root, r.child, r.axis⟩
  exponent := r.recordExp

theorem memoryTriples_length (g : GenComputeRow K) :
    (memoryTriples g).length = Nock.Framework.recordCount g.skel.state := by
  unfold memoryTriples
  rw [ofFn_fin3]
  rcases recordCount_eq_123 g.skel.state with hn | hn | hn
  · have h0 : (0 : ℕ) < 1 := Nat.zero_lt_one
    have n1 : ¬ (1 : ℕ) < 1 := Nat.lt_irrefl 1
    have n2 : ¬ (2 : ℕ) < 1 := by omega
    simp [hn, h0, n1, n2]
  · have h0 : (0 : ℕ) < 2 := by omega
    have h1 : (1 : ℕ) < 2 := by omega
    have n2 : ¬ (2 : ℕ) < 2 := Nat.lt_irrefl 2
    simp [hn, h0, h1, n2]
  · have h0 : (0 : ℕ) < 3 := by omega
    have h1 : (1 : ℕ) < 3 := by omega
    have h2 : (2 : ℕ) < 3 := by omega
    simp [hn, h0, h1, h2]

theorem requestsMatch_length (g : GenComputeRow K)
    (h : requestsMatchMemory g) :
    g.requests.length = Nock.Framework.recordCount g.skel.state := by
  have := congrArg List.length h
  simpa [requestTriples, List.length_map, memoryTriples_length] using this

theorem extract_map_eq_rowSlots (g : GenComputeRow K)
    (h : requestsMatchMemory g) :
    (extractNodeReqs g).map memReqToSlot = rowSlots g := by
  have hlen := requestsMatch_length g h
  rcases recordCount_eq_123 g.skel.state with hn | hn | hn
  · have hreqlen : g.requests.length = 1 := hlen.trans hn
    match hreqs : g.requests with
    | [] =>
      simp [hreqs] at hreqlen
    | r :: r2 :: rest =>
      simp [hreqs] at hreqlen
    | [r] =>
      rw [rowSlots_of_count1 g hn]
      unfold extractNodeReqs memReqToSlot
      simp [hreqs, extractNodeReqsAux, getRecordExp]
      unfold requestsMatchMemory requestTriples at h
      rw [hreqs, memoryTriples_of_count1 g hn] at h
      simp [recTriple] at h
      obtain ⟨hroot, hchild, haxis⟩ := h
      simp [hroot, hchild, haxis]
  · have hreqlen : g.requests.length = 2 := hlen.trans hn
    match hreqs : g.requests with
    | [] => simp [hreqs] at hreqlen
    | [r] => simp [hreqs] at hreqlen
    | r1 :: r2 :: r3 :: rest => simp [hreqs] at hreqlen
    | [r1, r2] =>
      rw [rowSlots_of_count2 g hn]
      unfold extractNodeReqs memReqToSlot
      simp [hreqs, extractNodeReqsAux, getRecordExp]
      unfold requestsMatchMemory requestTriples at h
      rw [hreqs, memoryTriples_of_count2 g hn] at h
      simp [recTriple] at h
      obtain ⟨⟨hroot0, hchild0, haxis0⟩, hroot1, hchild1, haxis1⟩ := h
      simp [hroot0, hchild0, haxis0, hroot1, hchild1, haxis1]
  · have hreqlen : g.requests.length = 3 := hlen.trans hn
    match hreqs : g.requests with
    | [] => simp [hreqs] at hreqlen
    | [r] => simp [hreqs] at hreqlen
    | [r1, r2] => simp [hreqs] at hreqlen
    | r1 :: r2 :: r3 :: r4 :: rest => simp [hreqs] at hreqlen
    | [r1, r2, r3] =>
      rw [rowSlots_of_count3 g hn]
      unfold extractNodeReqs memReqToSlot
      simp [hreqs, extractNodeReqsAux, getRecordExp]
      unfold requestsMatchMemory requestTriples at h
      rw [hreqs, memoryTriples_of_count3 g hn] at h
      simp [recTriple] at h
      obtain ⟨⟨hroot0, hchild0, haxis0⟩, ⟨hroot1, hchild1, haxis1⟩,
        hroot2, hchild2, haxis2⟩ := h
      simp [hroot0, hchild0, haxis0, hroot1, hchild1, haxis1,
        hroot2, hchild2, haxis2]

theorem inTree_walk_ne_read_root (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n t, InTree (genAnnotatedNounWalk E z lmb n).1 t →
      t.label.skel.state ≠ .read_root
  | .atom _a, t, ht => by
      cases ht with
      | here => simp [genAnnotatedNounWalk, NTree.label, gMemRow9, memHaltSkel]
      | sub hs _ => simp [genAnnotatedNounWalk, NTree.children] at hs
  | .cell h tl, t, ht => by
      cases ht with
      | here =>
        simp [genAnnotatedNounWalk, NTree.label, gMemRow9, memDecomposeSkel]
      | sub hs hu =>
        simp [genAnnotatedNounWalk, NTree.children_node, List.mem_cons,
          List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact inTree_walk_ne_read_root E z h _ hu
        · exact inTree_walk_ne_read_root E z tl _ hu

theorem inTree_verify_ne_read_root (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ)
    (t : NTree (GenMemoryRow K))
    (ht : InTree (genAnnotatedVerify E z lmb root child ax ts recordExp).1 t) :
    t.label.skel.state ≠ .read_root := by
  cases ht with
  | here =>
    simp [genAnnotatedVerify, NTree.label, gMemRow9, memVerifySkelAx]
  | sub hs hu =>
    simp [genAnnotatedVerify, NTree.children_node, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    subst hs
    exact inTree_walk_ne_read_root E z child _ hu

theorem inTree_descent_ne_read_root (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ) :
    ∀ remainingAxis currentNoun u,
      u ∈ (genAnnotatedDescent E z lmb root child recAxis ts recordExp
            currentNoun remainingAxis).1 →
      ∀ t, InTree u t → t.label.skel.state ≠ .read_root := by
  intro remainingAxis
  induction remainingAxis using Nat.strongRecOn with
  | ind n ih =>
    intro currentNoun u hu t ht
    unfold genAnnotatedDescent at hu
    split at hu
    · rename_i hlt
      simp [genAnnotatedVerify] at hu
      subst u
      exact inTree_verify_ne_read_root E z root child recAxis ts recordExp t ht
    · rename_i hge
      split at hu
      · simp at hu
        subst u
        cases ht with
        | here =>
          simp [NTree.label, gMemRow9, memDecomposeSkel]
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_cons, List.mem_append] at hs
          rcases hs with rfl | hs
          · exact inTree_walk_ne_read_root E z (formulaHead currentNoun) _ hu'
          · have hrest : axisRest n < n := axisRest_lt (Nat.le_of_not_gt hge)
            exact ih (axisRest n) hrest (formulaTail currentNoun) _ hs t hu'
      · simp at hu
        subst u
        cases ht with
        | here =>
          simp [NTree.label, gMemRow9, memDecomposeSkel]
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_cons, List.mem_append,
            List.not_mem_nil, or_false] at hs
          rcases hs with hs | rfl
          · have hrest : axisRest n < n := axisRest_lt (Nat.le_of_not_gt hge)
            exact ih (axisRest n) hrest (formulaHead currentNoun) _ hs t hu'
          · exact inTree_walk_ne_read_root E z (formulaTail currentNoun) _ hu'

theorem recordTree_root_state (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis recordExp : ℕ) :
    (genAnnotatedRecordTree E z α lmb root child axis recordExp).label.skel.state =
      .read_root := by
  rw [show genAnnotatedRecordTree E z α lmb root child axis recordExp =
        .node (gMemRow9 (memReadSkelAx root child axis) recordExp z
          (annotatedReadPub E root child axis (α ^ recordExp)
            (genAnnotatedDescent E z lmb root child axis (α ^ recordExp)
              recordExp root axis).2 0 0 lmb))
          (genAnnotatedDescent E z lmb root child axis (α ^ recordExp)
            recordExp root axis).1 from rfl]
  simp [NTree.label, gMemRow9, memReadSkelAx]

theorem inTree_record_read_root_eq (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis recordExp : ℕ)
    (t : NTree (GenMemoryRow K))
    (ht : InTree (genAnnotatedRecordTree E z α lmb root child axis recordExp) t)
    (hst : t.label.skel.state = .read_root) :
    t = genAnnotatedRecordTree E z α lmb root child axis recordExp := by
  rw [show genAnnotatedRecordTree E z α lmb root child axis recordExp =
        .node (gMemRow9 (memReadSkelAx root child axis) recordExp z
          (annotatedReadPub E root child axis (α ^ recordExp)
            (genAnnotatedDescent E z lmb root child axis (α ^ recordExp)
              recordExp root axis).2 0 0 lmb))
          (genAnnotatedDescent E z lmb root child axis (α ^ recordExp)
            recordExp root axis).1 from rfl] at ht ⊢
  cases ht with
  | here => rfl
  | sub hs hu =>
    exact (inTree_descent_ne_read_root E z root child axis (α ^ recordExp)
      recordExp axis root _ hs t hu hst).elim

def readRootSlotOf (g : GenMemoryRow K)
    (h : g.skel.state = .read_root) : CanonicalRecordSlot where
  record := g.skel.memoryRecord (by simp [memoryMemRecKind, h])
  exponent := g.stamp.recordExponent

def forestReadRootSlots (forest : List (NTree (GenMemoryRow K))) :
    List CanonicalRecordSlot :=
  (bfsForest forest).filterMap fun n =>
    if h : n.label.skel.state = .read_root then
      some (readRootSlotOf n.label h)
    else none

def HasReadRootSlot (t : NTree (GenMemoryRow K)) (slot : CanonicalRecordSlot) :
    Prop :=
  ∃ n, InTree t n ∧ ∃ h : n.label.skel.state = .read_root,
    slot = readRootSlotOf n.label h

theorem recordTree_slot (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (axis recordExp : ℕ) :
    readRootSlotOf
        (genAnnotatedRecordTree E z α lmb root child axis recordExp).label
        (recordTree_root_state E z α root child axis recordExp) =
      ({ record := ⟨root, child, axis⟩, exponent := recordExp } :
        CanonicalRecordSlot) := by
  simp [readRootSlotOf, genAnnotatedRecordTree, NTree.label, gMemRow9,
    memReadSkelAx]

theorem hasReadRootSlot_recordTree (E : Noun → ComputeTable.FP K) (z α : K)
    (r : MemRecordReq) (slot : CanonicalRecordSlot) :
    HasReadRootSlot
        (genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) slot ↔
      slot = memReqToSlot r := by
  constructor
  · intro ⟨n, ht, hst, hslot⟩
    have hn := inTree_record_read_root_eq E z α r.root r.child r.axis r.recordExp
      n ht hst
    subst n
    have hroot := recordTree_root_state (lmb := lmb) E z α r.root r.child r.axis r.recordExp
    rw [hslot, recordTree_slot]
    rfl
  · intro hslot
    refine ⟨genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp,
      InTree.here _, recordTree_root_state E z α r.root r.child r.axis r.recordExp,
      ?_⟩
    rw [hslot, recordTree_slot]
    rfl

theorem inTree_descentCont_read_root (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState)
    (P : NTree (GenMemoryRow K) → Prop)
    (hcont : ∀ u ∈ cont, ∀ t, InTree u t →
      t.label.skel.state = .read_root → P t) :
    ∀ remainingAxis currentNoun u,
      u ∈ (genAnnotatedDescentCont E z lmb cont contCell contState
            currentNoun remainingAxis).1 →
      ∀ t, InTree u t → t.label.skel.state = .read_root → P t := by
  intro remainingAxis
  induction remainingAxis using Nat.strongRecOn with
  | ind n ih =>
    intro currentNoun u hu t ht hst
    unfold genAnnotatedDescentCont at hu
    split at hu
    · exact hcont u hu t ht hst
    · rename_i hge
      split at hu
      · simp at hu
        subst u
        cases ht with
        | here =>
          simp [NTree.label, gMemRow9, memDecomposeSkel] at hst
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_cons, List.mem_append] at hs
          rcases hs with rfl | hs
          · exact (inTree_walk_ne_read_root E z (formulaHead currentNoun)
              _ hu' hst).elim
          · have hrest : axisRest n < n := axisRest_lt (Nat.le_of_not_gt hge)
            exact ih (axisRest n) hrest (formulaTail currentNoun) _ hs t hu' hst
      · simp at hu
        subst u
        cases ht with
        | here =>
          simp [NTree.label, gMemRow9, memDecomposeSkel] at hst
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_cons, List.mem_append,
            List.not_mem_nil, or_false] at hs
          rcases hs with hs | rfl
          · have hrest : axisRest n < n := axisRest_lt (Nat.le_of_not_gt hge)
            exact ih (axisRest n) hrest (formulaHead currentNoun) _ hs t hu' hst
          · exact (inTree_walk_ne_read_root E z (formulaTail currentNoun)
              _ hu' hst).elim

theorem genSemanticResponses_eq_forestReadRootSlots
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K))) :
    genSemanticResponses (genSemanticSkeleton t mf) (genMemoryStamps mf) =
      forestReadRootSlots mf := by
  unfold genSemanticResponses forestReadRootSlots genMemoryStamps
  rw [memorySkeletonRows_genSemantic, zip_map_same, List.filterMap_map]
  rfl

theorem mem_forestReadRootSlots (forest : List (NTree (GenMemoryRow K)))
    (slot : CanonicalRecordSlot) :
    slot ∈ forestReadRootSlots forest ↔
      ∃ root ∈ forest, HasReadRootSlot root slot := by
  unfold forestReadRootSlots HasReadRootSlot
  constructor
  · intro h
    obtain ⟨n, hn, hsome⟩ := List.mem_filterMap.mp h
    by_cases hst : n.label.skel.state = .read_root
    · rw [dif_pos hst] at hsome
      injection hsome with hslot
      obtain ⟨root, hroot, hin⟩ := (mem_bfsForest forest n).mp hn
      exact ⟨root, hroot, n, hin, hst, hslot.symm⟩
    · rw [dif_neg hst] at hsome
      cases hsome
  · intro ⟨root, hroot, n, hin, hst, hslot⟩
    refine List.mem_filterMap.mpr ⟨n, ?_, ?_⟩
    · exact (mem_bfsForest forest n).mpr ⟨root, hroot, hin⟩
    · rw [dif_pos hst, hslot]

theorem exists_inTree_descentCont (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) :
    ∀ remainingAxis currentNoun u,
      u ∈ cont →
      ∃ v ∈ (genAnnotatedDescentCont E z lmb cont contCell contState
            currentNoun remainingAxis).1,
        InTree v u := by
  intro remainingAxis
  induction remainingAxis using Nat.strongRecOn with
  | ind n ih =>
    intro currentNoun u hu
    unfold genAnnotatedDescentCont
    split
    · exact ⟨u, hu, InTree.here _⟩
    · rename_i hge
      split
      · obtain ⟨v, hv, hin⟩ :=
          ih (axisRest n) (axisRest_lt (Nat.le_of_not_gt hge))
            (formulaTail currentNoun) u hu
        refine ⟨_, List.mem_singleton.mpr rfl, InTree.sub ?_ hin⟩
        simp [NTree.children_node, List.mem_cons, List.mem_append]
        exact Or.inr hv
      · obtain ⟨v, hv, hin⟩ :=
          ih (axisRest n) (axisRest_lt (Nat.le_of_not_gt hge))
            (formulaHead currentNoun) u hu
        refine ⟨_, List.mem_singleton.mpr rfl, InTree.sub ?_ hin⟩
        simp [NTree.children_node, List.mem_cons, List.mem_append,
          List.not_mem_nil, or_false]
        exact Or.inl hv

theorem inTree_descentCont_from_cont (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState)
    (remainingAxis : ℕ) (currentNoun : Noun) (u t : NTree (GenMemoryRow K))
    (hu : u ∈ (genAnnotatedDescentCont E z lmb cont contCell contState
            currentNoun remainingAxis).1)
    (ht : InTree u t) (hst : t.label.skel.state = .read_root) :
    ∃ v ∈ cont, InTree v t :=
  inTree_descentCont_read_root E z cont contCell contState
    (fun t => ∃ v ∈ cont, InTree v t)
    (fun v hv _ ht _ => ⟨v, hv, ht⟩)
    remainingAxis currentNoun u hu t ht hst

theorem readRootSlotOf_memRead (root child : Noun) (ax e : ℕ) (z : K)
    (pub : MemoryTable.Pub K)
    (h : (gMemRow9 (memReadSkelAx root child ax) e z pub).skel.state =
      .read_root) :
    readRootSlotOf (gMemRow9 (memReadSkelAx root child ax) e z pub) h =
      ({ record := ⟨root, child, ax⟩, exponent := e } : CanonicalRecordSlot) := by
  simp [readRootSlotOf, gMemRow9, memReadSkelAx]

theorem hasReadRootSlot_chainedInner (E : Noun → ComputeTable.FP K) (z α : K)
    (prev : MemRecordReq) :
    ∀ rest slot,
      (∃ u ∈ (genAnnotatedChainedInner E z α lmb prev rest).1,
          HasReadRootSlot u slot) ↔
        slot ∈ rest.map memReqToSlot
  | [], slot => by
      constructor
      · intro ⟨u, hu, n, ht, hst, _hslot⟩
        simp [genAnnotatedChainedInner] at hu
        subst u
        exact (inTree_verify_ne_read_root E z prev.root prev.child prev.axis
          (α ^ prev.recordExp) prev.recordExp n ht hst).elim
      · intro h
        simp at h
  | r :: more, slot => by
      constructor
      · intro ⟨u, hu, n, ht, hst, hslot⟩
        simp [genAnnotatedChainedInner] at hu
        subst u
        cases ht with
        | here =>
          subst hslot
          simp [NTree.label, readRootSlotOf_memRead, memReqToSlot]
        | sub hs hu' =>
          simp [NTree.children_node, List.mem_cons, List.not_mem_nil,
            or_false] at hs
          subst hs
          cases hu' with
          | here =>
            simp [NTree.label, gMemRow9, memVerifySkelAx] at hst
          | sub hs' hu'' =>
            obtain ⟨v, hv, hin⟩ :=
              inTree_descentCont_from_cont E z
                (genAnnotatedChainedInner E z α lmb r more).1
                (genAnnotatedChainedInner E z α lmb r more).2
                (chainedInnerRootState more) r.axis r.root _ n hs' hu'' hst
            exact List.mem_cons.mpr (Or.inr
              ((hasReadRootSlot_chainedInner E z α r more slot).1
                ⟨v, hv, n, hin, hst, hslot⟩))
      · intro hslot
        rw [List.map_cons, List.mem_cons] at hslot
        rcases hslot with hslot | hslot
        · subst slot
          refine ⟨_, List.mem_singleton.mpr rfl, _, InTree.here _, ?_, ?_⟩
          · simp [NTree.label, gMemRow9, memReadSkelAx]
          · simp [NTree.label, readRootSlotOf_memRead, memReqToSlot]
        · have him := (hasReadRootSlot_chainedInner E z α r more slot).2 hslot
          obtain ⟨v, hv, n, ht, hst, hseq⟩ := him
          obtain ⟨w, hw, hinw⟩ :=
            exists_inTree_descentCont E z
              (genAnnotatedChainedInner E z α lmb r more).1
              (genAnnotatedChainedInner E z α lmb r more).2
              (chainedInnerRootState more) r.axis r.root v hv
          refine ⟨_, List.mem_singleton.mpr rfl, n, ?_, hst, hseq⟩
          have hverify :
              InTree
                (.node
                  (gMemRow9 (memVerifySkelAx prev.root prev.child prev.axis)
                    prev.recordExp z
                    (annotatedVerifyPub E prev.root prev.child prev.axis
                      (α ^ prev.recordExp)
                      (genAnnotatedDescentCont E z lmb
                          (genAnnotatedChainedInner E z α lmb r more).1
                          (genAnnotatedChainedInner E z α lmb r more).2
                          (chainedInnerRootState more) r.root r.axis).2
                      0 0 lmb))
                  (genAnnotatedDescentCont E z lmb
                    (genAnnotatedChainedInner E z α lmb r more).1
                    (genAnnotatedChainedInner E z α lmb r more).2
                    (chainedInnerRootState more) r.root r.axis).1)
                n :=
            InTree.sub (by simpa [NTree.children_node] using hw)
              (InTree_trans hinw ht)
          exact InTree.sub (by simp [NTree.children_node]) hverify

theorem hasReadRootSlot_chainedTree (E : Noun → ComputeTable.FP K) (z α : K)
    (reqs : List MemRecordReq) (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z α lmb reqs = some t)
    (slot : CanonicalRecordSlot) :
    HasReadRootSlot t slot ↔ slot ∈ reqs.map memReqToSlot := by
  match reqs with
  | [] => simp [genAnnotatedChainedTree] at ht
  | [r] =>
    simp [genAnnotatedChainedTree] at ht
    subst t
    simpa [List.map_cons, List.map_nil] using
      hasReadRootSlot_recordTree E z α r slot
  | r :: r2 :: rest =>
    simp [genAnnotatedChainedTree] at ht
    subst t
    constructor
    · intro ⟨n, htn, hst, hslot⟩
      cases htn with
      | here =>
        subst hslot
        simp [NTree.label, readRootSlotOf_memRead, memReqToSlot]
      | sub hs hu =>
        obtain ⟨v, hv, hin⟩ :=
          inTree_descentCont_from_cont E z
            (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).1
            (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).2
            (chainedInnerRootState (r2 :: rest)) r.axis r.root _ n hs hu hst
        exact List.mem_cons.mpr (Or.inr
          ((hasReadRootSlot_chainedInner E z α r (r2 :: rest) slot).1
            ⟨v, hv, n, hin, hst, hslot⟩))
    · intro hslot
      rw [List.map_cons, List.mem_cons] at hslot
      rcases hslot with hslot | hslot
      · subst slot
        refine ⟨_, InTree.here _, ?_, ?_⟩
        · simp [NTree.label, gMemRow9, memReadSkelAx]
        · simp [NTree.label, readRootSlotOf_memRead, memReqToSlot]
      · have him :=
          (hasReadRootSlot_chainedInner (lmb := lmb) E z α r (r2 :: rest) slot).2 hslot
        obtain ⟨v, hv, n, htn, hst, hseq⟩ := him
        obtain ⟨w, hw, hinw⟩ :=
          exists_inTree_descentCont E z
            (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).1
            (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).2
            (chainedInnerRootState (r2 :: rest)) r.axis r.root v hv
        refine ⟨n, InTree.sub hw (InTree_trans hinw htn), hst, hseq⟩

theorem hasReadRootSlot_rowMemForest (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ reqs slot,
      (∃ u ∈ genRowMemForest E z α lmb reqs, HasReadRootSlot u slot) ↔
        slot ∈ reqs.map memReqToSlot
  | [], slot => by
      constructor
      · intro ⟨u, hu, _⟩
        simp [genRowMemForest] at hu
      · intro h
        simp at h
  | [r], slot => by
      constructor
      · intro ⟨u, hu, hslot⟩
        simp [genRowMemForest] at hu
        subst u
        simpa using (hasReadRootSlot_recordTree E z α r slot).1 hslot
      · intro hslot
        refine ⟨_, List.mem_singleton.mpr rfl, ?_⟩
        exact (hasReadRootSlot_recordTree E z α r slot).2 (by
          simpa [List.map_cons, List.map_nil] using hslot)
  | [r1, r2], slot => by
      constructor
      · intro ⟨u, hu, hslot⟩
        simp only [genRowMemForest] at hu
        by_cases hc : r1.child = r2.root
        · rw [if_pos hc] at hu
          cases hch : genAnnotatedChainedTree E z α lmb [r1, r2] with
          | none =>
            rw [hch] at hu
            simp at hu
            rcases hu with rfl | rfl
            · have := (hasReadRootSlot_recordTree E z α r1 slot).1 hslot
              simp [this]
            · have := (hasReadRootSlot_recordTree E z α r2 slot).1 hslot
              simp [this]
          | some tree =>
            rw [hch] at hu
            simp at hu
            subst u
            exact (hasReadRootSlot_chainedTree E z α [r1, r2] tree hch slot).1 hslot
        · rw [if_neg hc] at hu
          simp at hu
          rcases hu with rfl | rfl
          · have := (hasReadRootSlot_recordTree E z α r1 slot).1 hslot
            simp [this]
          · have := (hasReadRootSlot_recordTree E z α r2 slot).1 hslot
            simp [this]
      · intro hslot
        simp [List.map_cons, List.mem_cons] at hslot
        by_cases hc : r1.child = r2.root
        · cases hch : genAnnotatedChainedTree E z α lmb [r1, r2] with
          | none =>
            simp [genAnnotatedChainedTree] at hch
          | some tree =>
            refine ⟨tree, ?_,
              (hasReadRootSlot_chainedTree E z α [r1, r2] tree hch slot).2 ?_⟩
            · simp [genRowMemForest, hc, hch]
            · simpa [List.map_cons, List.mem_cons] using hslot
        · simp [genRowMemForest, hc]
          rcases hslot with hslot | hslot
          · exact Or.inl ((hasReadRootSlot_recordTree E z α r1 slot).2 hslot)
          · exact Or.inr ((hasReadRootSlot_recordTree E z α r2 slot).2 (by
              simpa [List.map_nil] using hslot))
  | [r1, r2, r3], slot => by
      constructor
      · intro ⟨u, hu, hslot⟩
        rw [genRowMemForest_three_eq] at hu
        simp [List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · have := (hasReadRootSlot_rowMemForest E z α [r1, r2] slot).1 ⟨u, hu, hslot⟩
          simp [List.map_cons, List.mem_cons]
          rcases (by simpa using this :
              slot = memReqToSlot r1 ∨ slot = memReqToSlot r2) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · have := (hasReadRootSlot_recordTree E z α r3 slot).1 hslot
          simp [this]
      · intro hslot
        simp [List.map_cons, List.mem_cons] at hslot
        rw [genRowMemForest_three_eq]
        rcases hslot with hslot | hslot | hslot
        · have := (hasReadRootSlot_rowMemForest E z α [r1, r2] slot).2 (by
            simp [hslot])
          obtain ⟨u, hu, hs⟩ := this
          exact ⟨u, List.mem_append.mpr (Or.inl hu), hs⟩
        · have := (hasReadRootSlot_rowMemForest E z α [r1, r2] slot).2 (by
            simp [hslot])
          obtain ⟨u, hu, hs⟩ := this
          exact ⟨u, List.mem_append.mpr (Or.inl hu), hs⟩
        · refine ⟨_, List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)),
            (hasReadRootSlot_recordTree E z α r3 slot).2 (by
              simpa [List.map_nil] using hslot)⟩
  | r1 :: r2 :: r3 :: r4 :: rest, slot => by
      constructor
      · intro ⟨u, hu, hslot⟩
        unfold genRowMemForest at hu
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
        have := (hasReadRootSlot_recordTree E z α r slot).1 hslot
        exact List.mem_map.mpr ⟨r, hr, this.symm⟩
      · intro hslot
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hslot
        unfold genRowMemForest
        refine ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩,
          (hasReadRootSlot_recordTree E z α r (memReqToSlot r)).2 rfl⟩

theorem hasReadRootSlot_memForest (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K)) (slot : CanonicalRecordSlot) :
    (∃ u ∈ genMemForestFromTree E z α lmb t, HasReadRootSlot u slot) ↔
      ∃ n, InTree t n ∧ slot ∈ (extractNodeReqs n.label).map memReqToSlot := by
  suffices ∀ M t,
      NTree.size t ≤ M →
      ∀ slot,
        (∃ u ∈ genMemForestFromTree E z α lmb t, HasReadRootSlot u slot) ↔
          ∃ n, InTree t n ∧
            slot ∈ (extractNodeReqs n.label).map memReqToSlot from
    this (NTree.size t) t le_rfl slot
  intro M
  induction M with
  | zero =>
    intro t ht slot
    cases t with
    | node g cs =>
      simp [NTree.size] at ht
  | succ M ih =>
    intro t ht slot
    cases t with
    | node g cs =>
      have hcs : ∀ c ∈ cs, NTree.size c ≤ M := by
        intro c hc
        have hin : NTree.size c ∈ cs.map NTree.size :=
          List.mem_map.mpr ⟨c, hc, rfl⟩
        have hsum : NTree.size c ≤ (cs.map NTree.size).sum :=
          List.le_sum_of_mem hin
        simp [NTree.size] at ht
        omega
      have recList :
          ∀ cs', (∀ c ∈ cs', c ∈ cs) →
            ((∃ u ∈ genMemForestFromList E z α lmb cs', HasReadRootSlot u slot) ↔
              ∃ c ∈ cs', ∃ n, InTree c n ∧
                slot ∈ (extractNodeReqs n.label).map memReqToSlot) := by
        intro cs' hsub
        induction cs' with
        | nil =>
          constructor
          · intro ⟨u, hu, _⟩
            simp [genMemForestFromList] at hu
          · intro ⟨c, hc, _⟩
            simp at hc
        | cons c rest ihcs =>
          constructor
          · intro ⟨u, hu, hslot⟩
            simp [genMemForestFromList] at hu
            rcases hu with hu | hu
            · have := (ih c (hcs c (hsub c (by simp))) slot).1 ⟨u, hu, hslot⟩
              obtain ⟨n, hn, hs⟩ := this
              exact ⟨c, List.mem_cons.mpr (Or.inl rfl), n, hn, hs⟩
            · have := (ihcs (fun c' hc' => hsub c' (List.mem_cons.mpr (Or.inr hc')))).1
                ⟨u, hu, hslot⟩
              obtain ⟨c', hc', n, hn, hs⟩ := this
              exact ⟨c', List.mem_cons.mpr (Or.inr hc'), n, hn, hs⟩
          · intro ⟨c', hc', n, hn, hs⟩
            rcases List.mem_cons.mp hc' with hhead | hc'
            · subst c'
              have := (ih c (hcs c (hsub c (List.mem_cons.mpr (Or.inl rfl))))
                slot).2 ⟨n, hn, hs⟩
              obtain ⟨u, hu, hslot⟩ := this
              exact ⟨u, List.mem_append.mpr (Or.inl hu), hslot⟩
            · have := (ihcs (fun c'' hc'' =>
                  hsub c'' (List.mem_cons.mpr (Or.inr hc'')))).2
                ⟨c', hc', n, hn, hs⟩
              obtain ⟨u, hu, hslot⟩ := this
              exact ⟨u, List.mem_append.mpr (Or.inr hu), hslot⟩
      constructor
      · intro ⟨u, hu, hslot⟩
        simp [genMemForestFromTree] at hu
        rcases hu with hu | hu
        · have := (hasReadRootSlot_rowMemForest E z α (extractNodeReqs g)
            slot).1 ⟨u, hu, hslot⟩
          exact ⟨.node g cs, InTree.here _, this⟩
        · have := (recList cs (fun _ h => h)).1 ⟨u, hu, hslot⟩
          obtain ⟨c, hc, n, hn, hs⟩ := this
          exact ⟨n, InTree.sub hc hn, hs⟩
      · intro ⟨n, hn, hs⟩
        cases hn with
        | here =>
          have := (hasReadRootSlot_rowMemForest (lmb := lmb) E z α (extractNodeReqs g)
            slot).2 hs
          obtain ⟨u, hu, hslot⟩ := this
          exact ⟨u, List.mem_append.mpr (Or.inl hu), hslot⟩
        | sub hc hn =>
          have := (recList cs (fun _ h => h)).2 ⟨_, hc, n, hn, hs⟩
          obtain ⟨u, hu, hslot⟩ := this
          exact ⟨u, List.mem_append.mpr (Or.inr hu), hslot⟩

theorem extractNodeReqs_length (g : GenComputeRow K) :
    (extractNodeReqs g).length = g.requests.length := by
  unfold extractNodeReqs
  have aux : ∀ i (rs : List (ServiceReq K)),
      (extractNodeReqsAux g.stamp i rs).length = rs.length := by
    intro i rs
    induction rs generalizing i with
    | nil => rfl
    | cons _ rest ih => simp [extractNodeReqsAux, ih]
  exact aux 0 g.requests

theorem requestsMatchMemory_of_skel_requests {g g' : GenComputeRow K}
    (hs : g.skel = g'.skel) (hr : g.requests = g'.requests) :
    requestsMatchMemory g ↔ requestsMatchMemory g' := by
  unfold requestsMatchMemory requestTriples memoryTriples
  rw [hs, hr]

theorem treeRequestsMatch_bfsAssign (t : NTree (GenComputeRow K))
    (h : treeRequestsMatch t) : treeRequestsMatch (bfsAssign t) := by
  intro n hn
  have hnF : n ∈ bfsForest [bfsAssign t] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab : n.label ∈ (bfsForest [bfsAssign t]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [bfsAssign_bfsForest_labels] at hlab
  obtain ⟨i, hi, hieq⟩ := List.mem_map.mp hlab
  have hi' := lt_bfsRows_of_mem_range' hi
  have horig : requestsMatchMemory (bfsRows t)[i - 1] := by
    have hmem : (bfsRows t)[i - 1] ∈ (bfsForest [t]).map NTree.label := by
      simpa [bfsRows] using List.getElem_mem hi'
    obtain ⟨orig, horigF, horigL⟩ := List.mem_map.mp hmem
    obtain ⟨c, hc, hin⟩ := (mem_bfsForest [t] orig).mp horigF
    simp at hc
    subst c
    rw [← horigL]
    exact h orig hin
  exact (requestsMatchMemory_of_skel_requests
      (by rw [← hieq, bfsLabelAt_skel t i hi'])
      (by rw [← hieq, bfsLabelAt_requests t i hi'])).1 horig

theorem treeRequestsMatch_airReorder {t : NTree (GenComputeRow K)}
    (h : treeRequestsMatch t) : treeRequestsMatch (airReorder t) := by
  intro u hu
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label t u hu
  simpa [hl] using h u0 hu0

theorem genRowMemForest_read_fibre (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ reqs, forestFibre MemoryTable.MState.read_root
        (genRowMemForest E z α lmb reqs) = reqs.length
  | [] => by simp [genRowMemForest, forestFibre]
  | [r] => by
      rw [genRowMemForest_singleton, forestFibre_singleton]
      exact (genAnnotatedRecordTree_fibre E z α r.root r.child r.axis
        r.recordExp).1
  | [r1, r2] => by
      rw [genRowMemForest_pair_eq]
      split
      · cases hch : genAnnotatedChainedTree E z α lmb [r1, r2] with
        | none =>
          simp [genAnnotatedChainedTree] at hch
        | some tree =>
          rw [forestFibre_singleton]
          simpa using
            (genAnnotatedChainedTree_fibre E z α [r1, r2] tree hch).1
      · rw [forestFibre_cons, forestFibre_cons, forestFibre_nil]
        have h1 := (genAnnotatedRecordTree_fibre (lmb := lmb) E z α r1.root r1.child
          r1.axis r1.recordExp).1
        have h2 := (genAnnotatedRecordTree_fibre (lmb := lmb) E z α r2.root r2.child
          r2.axis r2.recordExp).1
        simp [h1, h2]
  | [r1, r2, r3] => by
      rw [genRowMemForest_three_eq, forestFibre_append, forestFibre_singleton]
      have h12 := genRowMemForest_read_fibre E z α [r1, r2]
      have h3 := (genAnnotatedRecordTree_fibre (lmb := lmb) E z α r3.root r3.child
        r3.axis r3.recordExp).1
      simp [h12, h3]
  | r1 :: r2 :: r3 :: r4 :: rest => by
      unfold genRowMemForest
      exact (forestFibre_map_recordTrees E z α
        (r1 :: r2 :: r3 :: r4 :: rest)).1

theorem mem_rowSlots_bfs (t : NTree (GenComputeRow K))
    (slot : CanonicalRecordSlot) :
    slot ∈ ((bfsForest [bfsAssign t]).map NTree.label).flatMap rowSlots ↔
      ∃ n, InTree (bfsAssign t) n ∧ slot ∈ rowSlots n.label := by
  constructor
  · intro h
    obtain ⟨g, hg, hslot⟩ := List.mem_flatMap.mp h
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hg
    obtain ⟨c, hc, hin⟩ := (mem_bfsForest [bfsAssign t] n).mp hn
    simp at hc
    subst c
    exact ⟨n, hin, hslot⟩
  · intro ⟨n, hin, hslot⟩
    refine List.mem_flatMap.mpr ⟨n.label, ?_, hslot⟩
    exact List.mem_map.mpr ⟨n,
      (mem_bfsForest [bfsAssign t] n).mpr ⟨_, List.mem_singleton.mpr rfl, hin⟩,
      rfl⟩

/-! ## Response length / `L_mIO` -- the paper -/

mutual
def extractCount : NTree (GenComputeRow K) → ℕ
  | .node g cs => (extractNodeReqs g).length + extractCountList cs
def extractCountList : List (NTree (GenComputeRow K)) → ℕ
  | [] => 0
  | t :: ts => extractCount t + extractCountList ts
end

theorem extractCount_node (g : GenComputeRow K)
    (cs : List (NTree (GenComputeRow K))) :
    extractCount (.node g cs) =
      (extractNodeReqs g).length + extractCountList cs :=
  rfl

theorem extractCountList_nil :
    extractCountList ([] : List (NTree (GenComputeRow K))) = 0 :=
  rfl

theorem extractCountList_cons (t : NTree (GenComputeRow K))
    (ts : List (NTree (GenComputeRow K))) :
    extractCountList (t :: ts) = extractCount t + extractCountList ts :=
  rfl

theorem extractCount_singleton (t : NTree (GenComputeRow K)) :
    extractCountList [t] = extractCount t := by
  rw [extractCountList_cons, extractCountList_nil, add_zero]

theorem extractCountList_append :
    ∀ l₁ l₂ : List (NTree (GenComputeRow K)),
      extractCountList (l₁ ++ l₂) = extractCountList l₁ + extractCountList l₂
  | [], _ => by
      rw [List.nil_append, extractCountList_nil, zero_add]
  | t :: ts, l₂ => by
      rw [List.cons_append, extractCountList_cons, extractCountList_cons,
        extractCountList_append ts l₂]
      omega

theorem extractCountList_eq_roots_add_children :
    ∀ cs : List (NTree (GenComputeRow K)),
      extractCountList cs =
        (cs.map (fun t => (extractNodeReqs t.label).length)).sum +
          extractCountList (cs.flatMap NTree.children)
  | [] => by simp [extractCountList]
  | t :: ts => by
      cases t with
      | node g ch =>
        rw [extractCountList_cons, extractCount_node, List.map_cons,
          List.sum_cons, List.flatMap_cons, NTree.children_node,
          NTree.label_node, extractCountList_append,
          extractCountList_eq_roots_add_children ts]
        omega

theorem extractCountList_eq_bfs (cs : List (NTree (GenComputeRow K))) :
    extractCountList cs =
      ((bfsForest cs).map
        (fun n => (extractNodeReqs n.label).length)).sum := by
  generalize hn : totalSize cs = n
  induction n using Nat.strong_induction_on generalizing cs with
  | h n ih =>
    by_cases hl : cs = []
    · subst cs
      simp [extractCountList, bfsForest_nil]
    · rw [bfsForest_cons_eq cs hl, List.map_append, List.sum_append]
      have hsize := totalSize_flatMap_children cs
      have hpos : 0 < cs.length := List.length_pos_of_ne_nil hl
      have hlt : totalSize (cs.flatMap NTree.children) < n := by omega
      rw [extractCountList_eq_roots_add_children,
        ih _ hlt (cs.flatMap NTree.children) rfl]

theorem extractCount_eq_bfs (t : NTree (GenComputeRow K)) :
    extractCount t =
      ((bfsForest [t]).map
        (fun n => (extractNodeReqs n.label).length)).sum := by
  rw [← extractCount_singleton, extractCountList_eq_bfs]

theorem genMemForestFromList_read_fibre (E : Noun → ComputeTable.FP K)
    (z α : K) (cs : List (NTree (GenComputeRow K)))
    (hs : ∀ t ∈ cs,
      forestFibre MemoryTable.MState.read_root
        (genMemForestFromTree E z α lmb t) = extractCount t) :
    forestFibre MemoryTable.MState.read_root
      (genMemForestFromList E z α lmb cs) = extractCountList cs := by
  induction cs with
  | nil =>
    simp [genMemForestFromList_nil, forestFibre, extractCountList]
  | cons t rest ih =>
    rw [genMemForestFromList_cons, forestFibre_append, extractCountList_cons]
    have ht : forestFibre MemoryTable.MState.read_root
        (genMemForestFromTree E z α lmb t) = extractCount t :=
      hs t (List.mem_cons.mpr (Or.inl rfl))
    have hrest : forestFibre MemoryTable.MState.read_root
        (genMemForestFromList E z α lmb rest) = extractCountList rest :=
      ih (fun u hu => hs u (List.mem_cons.mpr (Or.inr hu)))
    simp [ht, hrest]

theorem genMemForestFromTree_read_fibre (E : Noun → ComputeTable.FP K)
    (z α : K) (t : NTree (GenComputeRow K)) :
    forestFibre MemoryTable.MState.read_root
      (genMemForestFromTree E z α lmb t) = extractCount t := by
  induction hn : t.size using Nat.strongRecOn generalizing t with
  | _ n ih =>
    cases t with
    | node g cs =>
      rw [genMemForestFromTree_node, forestFibre_append]
      have hrow := genRowMemForest_read_fibre (lmb := lmb) E z α (extractNodeReqs g)
      have hcs : ∀ c ∈ cs,
          forestFibre MemoryTable.MState.read_root
            (genMemForestFromTree E z α lmb c) = extractCount c := by
        intro c hc
        have hin : c.size ∈ cs.map NTree.size :=
          List.mem_map.mpr ⟨c, hc, rfl⟩
        have hle : c.size ≤ (cs.map NTree.size).sum :=
          List.le_sum_of_mem hin
        have hsz : n = 1 + (cs.map NTree.size).sum := by
          simpa [NTree.size] using hn.symm
        exact ih c.size (by omega) c rfl
      have hlist := genMemForestFromList_read_fibre E z α cs hcs
      simp [extractCount_node, hrow, hlist]

theorem extract_length_eq_rowSlots (g : GenComputeRow K)
    (h : requestsMatchMemory g) :
    (extractNodeReqs g).length = (rowSlots g).length := by
  rw [extractNodeReqs_length, requestsMatch_length g h, rowSlots_length]

theorem length_filterMap_dite {α β : Type*} (p : α → Prop) [DecidablePred p]
    (f : ∀ a, p a → β) :
    ∀ l : List α,
      (l.filterMap fun a => if h : p a then some (f a h) else none).length =
        l.countP p
  | [] => rfl
  | a :: l => by
      by_cases hp : p a
      · simp [hp, length_filterMap_dite p f l]
      · simp [hp, length_filterMap_dite p f l]

theorem forestReadRootSlots_length
    (forest : List (NTree (GenMemoryRow K))) :
    (forestReadRootSlots forest).length =
      (bfsForest forest).countP
        (fun n => n.label.skel.state = MemoryTable.MState.read_root) := by
  unfold forestReadRootSlots
  exact length_filterMap_dite _ _ _

theorem countP_eq_of_forall {α : Type*} (p q : α → Bool) :
    ∀ l : List α, (∀ a ∈ l, p a = q a) → l.countP p = l.countP q
  | [], _ => rfl
  | a :: l, h => by
      rw [List.countP_cons, List.countP_cons,
        h a (List.mem_cons.mpr (Or.inl rfl)),
        countP_eq_of_forall p q l
          (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))]

/-! ## `L_mIO` for any accepted program -- the paper

`Def:L_mIO` asks for `k = |requests| ∈ [Ksz]`, a deduplication `unique_requests`
of the requests, and a permutation carrying it to the responses.  A generated trace satisfies it in
the strongest possible way: its requests are already distinct, so `unique_requests := requests` and
the relation collapses to `responses ~ requests` — which is the `L_IO` of the paper, i.e. the
generator is *unique request* in the sense of `Def:unique_request` and
`cor_uni_req_uni_resp` (`:613`) applies to it.

Three facts do the work, and each is about the generator rather than about a fixture:

* requests are distinct because their exponents are `1, 2, …` consecutively
  (`genSemanticRequests_exponents`);
* requests and responses carry the *same slots*, by the serving identity of the paper;
* they have the same *length*, because the `read_root` fibre of the served forest counts the
  extracted requests. -/

/-- Two lists with the same members and the same length are both `Nodup` as soon as one is. -/
theorem nodup_of_setEq_of_length {α : Type*} [DecidableEq α] {l m : List α}
    (hl : l.Nodup) (hmem : ∀ a, a ∈ m ↔ a ∈ l) (hlen : m.length = l.length) : m.Nodup := by
  have hfin : m.toFinset = l.toFinset := by
    ext a
    simp only [List.mem_toFinset]
    exact hmem a
  have hcard : m.toFinset.card = m.length := by
    rw [hfin, List.toFinset_card_of_nodup hl, hlen]
  have hsub : m.dedup.Sublist m := List.dedup_sublist _
  have hlen' : m.dedup.length = m.length := by
    have hnd : m.dedup.Nodup := List.nodup_dedup _
    have hfin' : m.dedup.toFinset = m.toFinset := by
      ext a
      simp [List.mem_toFinset, List.mem_dedup]
    rw [← List.toFinset_card_of_nodup hnd, hfin', hcard]
  exact (List.dedup_eq_self).1 (List.Sublist.eq_of_length hsub hlen')

/-- Every tree has at least one BFS row. -/
theorem bfsRows_length_pos (u : NTree (GenComputeRow K)) : 0 < (bfsRows u).length := by
  have h1 : 1 ≤ u.size := by cases u with | node _ _ => simp [NTree.size]
  rw [bfsRows_length, bfsForest_length,
    show totalSize [u] = u.size by simp [totalSize]]
  omega

/-! ### Membership: requests and responses carry the same slots -/

/-- The request slots of a generated trace, by membership: one per active memory record of each
compute row. -/
theorem genSemanticRequests_mem (u : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) (slot : CanonicalRecordSlot) :
    slot ∈ genSemanticRequests (genSemanticSkeleton (bfsAssign u) mf)
        (bfsStamps (bfsAssign u)) ↔
      ∃ n, InTree (bfsAssign u) n ∧ slot ∈ rowSlots n.label := by
  have hlab :
      (List.range' 1 (bfsForest [u]).length).map (bfsLabelAt u) =
        (bfsForest [bfsAssign u]).map NTree.label :=
    (bfsAssign_bfsForest_labels u).symm
  rw [genSemanticRequests_eq_bfs u mf, hlab]
  exact mem_rowSlots_bfs u slot

/-- **The serving identity, by membership**.  The `read_root` slots the generated
memory forest serves are exactly the memory records the compute rows commit — given only that the
tree's service requests match its skeleton records. -/
theorem genMemForestFromTree_readRoot_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (u : NTree (GenComputeRow K)) (hmatch : treeRequestsMatch (bfsAssign u))
    (slot : CanonicalRecordSlot) :
    slot ∈ forestReadRootSlots (genMemForestFromTree E z α lmb (bfsAssign u)) ↔
      ∃ n, InTree (bfsAssign u) n ∧ slot ∈ rowSlots n.label := by
  rw [mem_forestReadRootSlots, hasReadRootSlot_memForest]
  constructor
  · rintro ⟨n, hn, hs⟩
    exact ⟨n, hn, by rwa [extract_map_eq_rowSlots n.label (hmatch n hn)] at hs⟩
  · rintro ⟨n, hn, hs⟩
    exact ⟨n, hn, by rwa [← extract_map_eq_rowSlots n.label (hmatch n hn)] at hs⟩

/-- Requests and responses of a generated trace carry the same slots. -/
theorem genSemantic_slot_mem (z α : K) (u : NTree (GenComputeRow K))
    (hmatch : treeRequestsMatch (bfsAssign u)) (slot : CanonicalRecordSlot) :
    slot ∈ genSemanticRequests
        (genSemanticSkeleton (bfsAssign u)
          (genMemForestFromTree (encC z) z α lmb (bfsAssign u)))
        (bfsStamps (bfsAssign u)) ↔
      slot ∈ genSemanticResponses
        (genSemanticSkeleton (bfsAssign u)
          (genMemForestFromTree (encC z) z α lmb (bfsAssign u)))
        (genMemoryStamps (genMemForestFromTree (encC z) z α lmb (bfsAssign u))) := by
  rw [genSemanticResponses_eq_forestReadRootSlots, genSemanticRequests_mem,
    genMemForestFromTree_readRoot_mem _ z α u hmatch]

/-! ### Length: the `read_root` fibre counts the requests -/

/-- The request list's length is the total active-slot count of the BFS rows. -/
theorem genSemanticRequests_length_eq_rowSlots_sum (u : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    (genSemanticRequests (genSemanticSkeleton (bfsAssign u) mf)
        (bfsStamps (bfsAssign u))).length =
      ((bfsForest [bfsAssign u]).map (fun n => (rowSlots n.label).length)).sum := by
  have hlab :
      (List.range' 1 (bfsForest [u]).length).map (bfsLabelAt u) =
        (bfsForest [bfsAssign u]).map NTree.label :=
    (bfsAssign_bfsForest_labels u).symm
  rw [genSemanticRequests_eq_bfs u mf, hlab, List.length_flatMap, List.map_map]
  rfl

/-- Under the serving identity the extracted service requests and the committed record slots agree
in number at every row, hence in total. -/
theorem genExtract_sum_eq_rowSlots_sum (u : NTree (GenComputeRow K))
    (hmatch : treeRequestsMatch (bfsAssign u)) :
    ((bfsForest [bfsAssign u]).map
        (fun n => (extractNodeReqs n.label).length)).sum =
      ((bfsForest [bfsAssign u]).map (fun n => (rowSlots n.label).length)).sum := by
  congr 1
  refine List.map_congr_left ?_
  intro n hn
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ n).mp hn
  simp at hc
  subst c
  exact extract_length_eq_rowSlots n.label (hmatch n hin)

/-- The number of response slots is the `read_root` fibre of the served forest, provided the
rendered public state agrees with the skeleton state — which `BindMemoryRow` gives. -/
theorem genMemForestFromTree_readRoot_length (E : Noun → ComputeTable.FP K) (z α : K)
    (u : NTree (GenComputeRow K))
    (hst : ∀ n ∈ bfsForest (genMemForestFromTree E z α lmb (bfsAssign u)),
        memPubSt n.label = n.label.skel.state) :
    (forestReadRootSlots (genMemForestFromTree E z α lmb (bfsAssign u))).length =
      forestFibre MemoryTable.MState.read_root
        (genMemForestFromTree E z α lmb (bfsAssign u)) := by
  rw [forestReadRootSlots_length,
    ← fibreCount_bfsForest MemoryTable.MState.read_root
      (genMemForestFromTree E z α lmb (bfsAssign u))]
  unfold fibreCount
  rw [List.countP_map]
  refine countP_eq_of_forall _ _ _ ?_
  intro n hn
  have heq := hst n hn
  simp [Function.comp, memPubSt] at heq ⊢
  simp only [heq]

/-- **Requests and responses have the same length.** -/
theorem genSemantic_length (z α : K) (u : NTree (GenComputeRow K))
    (hmatch : treeRequestsMatch (bfsAssign u))
    (hst : ∀ n ∈ bfsForest (genMemForestFromTree (encC z) z α lmb (bfsAssign u)),
        memPubSt n.label = n.label.skel.state) :
    (genSemanticResponses
        (genSemanticSkeleton (bfsAssign u)
          (genMemForestFromTree (encC z) z α lmb (bfsAssign u)))
        (genMemoryStamps (genMemForestFromTree (encC z) z α lmb (bfsAssign u)))).length =
      (genSemanticRequests
        (genSemanticSkeleton (bfsAssign u)
          (genMemForestFromTree (encC z) z α lmb (bfsAssign u)))
        (bfsStamps (bfsAssign u))).length := by
  rw [genSemanticResponses_eq_forestReadRootSlots,
    genMemForestFromTree_readRoot_length _ z α u hst,
    genMemForestFromTree_read_fibre, extractCount_eq_bfs,
    genExtract_sum_eq_rowSlots_sum u hmatch,
    genSemanticRequests_length_eq_rowSlots_sum]

/-! ### Distinctness and the permutation -/

/-- Request exponents are `1, 2, …, accAt u |bfsRows u|`, hence distinct. -/
theorem genSemanticRequests_exponent_nodup (u : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    ((genSemanticRequests (genSemanticSkeleton (bfsAssign u) mf)
      (bfsStamps (bfsAssign u))).map CanonicalRecordSlot.exponent).Nodup := by
  rw [genSemanticRequests_exponents u mf]
  exact List.Nodup.map Nat.succ_injective List.nodup_range

/-- Request slots are distinct — the generator is *unique request*. -/
theorem genSemanticRequests_nodup (u : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    (genSemanticRequests (genSemanticSkeleton (bfsAssign u) mf)
      (bfsStamps (bfsAssign u))).Nodup :=
  List.Nodup.of_map CanonicalRecordSlot.exponent
    (genSemanticRequests_exponent_nodup u mf)

/-- Response slots are distinct — *unique response*, derived rather than assumed. -/
theorem genSemanticResponses_nodup (z α : K) (u : NTree (GenComputeRow K))
    (hmatch : treeRequestsMatch (bfsAssign u))
    (hst : ∀ n ∈ bfsForest (genMemForestFromTree (encC z) z α lmb (bfsAssign u)),
        memPubSt n.label = n.label.skel.state) :
    (genSemanticResponses
      (genSemanticSkeleton (bfsAssign u)
        (genMemForestFromTree (encC z) z α lmb (bfsAssign u)))
      (genMemoryStamps (genMemForestFromTree (encC z) z α lmb (bfsAssign u)))).Nodup := by
  refine List.Nodup.of_map CanonicalRecordSlot.exponent ?_
  refine nodup_of_setEq_of_length (genSemanticRequests_exponent_nodup u
    (genMemForestFromTree (encC z) z α lmb (bfsAssign u))) ?_ ?_
  · intro e
    simp only [List.mem_map]
    constructor
    · rintro ⟨s, hs, he⟩
      exact ⟨s, (genSemantic_slot_mem z α u hmatch s).2 hs, he⟩
    · rintro ⟨s, hs, he⟩
      exact ⟨s, (genSemantic_slot_mem z α u hmatch s).1 hs, he⟩
  · simpa [List.length_map] using genSemantic_length z α u hmatch hst

/-- **Responses are a permutation of requests.** -/
theorem genSemantic_slot_perm (z α : K) (u : NTree (GenComputeRow K))
    (hmatch : treeRequestsMatch (bfsAssign u))
    (hst : ∀ n ∈ bfsForest (genMemForestFromTree (encC z) z α lmb (bfsAssign u)),
        memPubSt n.label = n.label.skel.state) :
    (genSemanticResponses
        (genSemanticSkeleton (bfsAssign u)
          (genMemForestFromTree (encC z) z α lmb (bfsAssign u)))
        (genMemoryStamps (genMemForestFromTree (encC z) z α lmb (bfsAssign u)))).Perm
      (genSemanticRequests
        (genSemanticSkeleton (bfsAssign u)
          (genMemForestFromTree (encC z) z α lmb (bfsAssign u)))
        (bfsStamps (bfsAssign u))) :=
  (List.perm_ext_iff_of_nodup
      (genSemanticResponses_nodup z α u hmatch hst)
      (genSemanticRequests_nodup u _)).2
    (fun slot => (genSemantic_slot_mem z α u hmatch slot).symm)

/-! ### At the sampled seed: `nmrMEF` records -/

/-- Slot lists with distinct exponents realize to distinct `nmrMEF` records. -/
theorem semanticRecordsAt_nodup (z : K) (l : List CanonicalRecordSlot)
    (h : (l.map CanonicalRecordSlot.exponent).Nodup) :
    (l.map (SemanticTimestampSkeleton.semanticRecordAt (F := F) z)).Nodup := by
  refine List.Nodup.of_map (fun r : (nmrMEF F K).Rec => r.2.2) ?_
  simpa [List.map_map, Function.comp_def,
    SemanticTimestampSkeleton.semanticRecordAt] using h

/-! ### The two timestamp windows -- the paper

`SemanticIOPreimage` asks for one window `B` holding every request and every response timestamp,
below `orderOf α` so `bridge` stays injective.  Both sides obey the same arithmetic: a slot's
exponent never exceeds the trace's own accumulator plus the at-most-three records of its row.
`genSemanticRequests_exponent_le` is that on the compute side; the memory side follows because the
served forest is restamped from the compute rows' extracted requests. -/

/-- Every stamp in the served forest is within three of the trace's accumulator. -/
theorem genMemForestFromTree_stamp_exp_le (E : Noun → ComputeTable.FP K) (z α : K)
    (u : NTree (GenComputeRow K)) (v : NTree (GenMemoryRow K))
    (hv : v ∈ bfsForest (genMemForestFromTree E z α lmb (bfsAssign u)))
    (s : NTree (GenMemoryRow K)) (hs : InTree v s) :
    s.label.stamp.recordExponent ≤ accAt u (bfsRows u).length + 3 := by
  obtain ⟨root, hroot, hin⟩ := (mem_bfsForest _ v).mp hv
  exact genMemForestFromTree_exp_le E z α _ (bfsAssign u)
    (fun n hn r hr => bfsAssign_extract_recordExp_le u n hn r hr)
    root hroot s (InTree_trans hin hs)

theorem genMemForestFromTree_bfs_stamp_exp_le (E : Noun → ComputeTable.FP K) (z α : K)
    (u : NTree (GenComputeRow K)) (v : NTree (GenMemoryRow K))
    (hv : v ∈ bfsForest (genMemForestFromTree E z α lmb (bfsAssign u))) :
    v.label.stamp.recordExponent ≤ accAt u (bfsRows u).length + 3 :=
  genMemForestFromTree_stamp_exp_le E z α u v hv v (InTree.here _)

/-- Every response slot's exponent is within three of the trace's accumulator. -/
theorem genSemanticResponses_exponent_le (E : Noun → ComputeTable.FP K) (z α : K)
    (u : NTree (GenComputeRow K)) {slot : CanonicalRecordSlot}
    (h : slot ∈ genSemanticResponses
      (genSemanticSkeleton (bfsAssign u) (genMemForestFromTree E z α lmb (bfsAssign u)))
      (genMemoryStamps (genMemForestFromTree E z α lmb (bfsAssign u)))) :
    slot.exponent ≤ accAt u (bfsRows u).length + 3 := by
  simp only [genSemanticResponses, List.mem_filterMap] at h
  obtain ⟨pair, hpair, hsome⟩ := h
  have hstamp : pair.2 ∈ genMemoryStamps (genMemForestFromTree E z α lmb (bfsAssign u)) :=
    (List.of_mem_zip hpair).2
  simp only [genMemoryStamps, List.mem_map] at hstamp
  obtain ⟨n, hn, hneq⟩ := hstamp
  by_cases hst : pair.1.state = MemoryTable.MState.read_root
  · rw [dif_pos hst] at hsome
    injection hsome with hslotEq
    subst hslotEq
    change pair.2.recordExponent ≤ _
    rw [← hneq]
    exact genMemForestFromTree_bfs_stamp_exp_le E z α u n hn
  · rw [dif_neg hst] at hsome
    cases hsome

/-- **`SemanticIOPreimage.requestTimestampBound`, generically.** -/
theorem genSemanticRequestsAt_timestampBound (B : ℕ) (z : K)
    (u : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hB : accAt u (bfsRows u).length + 3 < B) :
    ∀ r ∈ (genSemanticRequests (genSemanticSkeleton (bfsAssign u) mf)
        (bfsStamps (bfsAssign u))).map
          (SemanticTimestampSkeleton.semanticRecordAt (F := F) z), r.2.2 < B := by
  intro r hr
  obtain ⟨slot, hslot, rfl⟩ := List.mem_map.mp hr
  rw [semanticRecordAt_exponent]
  exact Nat.lt_of_le_of_lt (genSemanticRequests_exponent_le u mf hslot) hB

/-- **`SemanticIOPreimage.responseTimestampBound`, generically.** -/
theorem genSemanticResponsesAt_timestampBound (B : ℕ) (z α : K)
    (u : NTree (GenComputeRow K))
    (hB : accAt u (bfsRows u).length + 3 < B) :
    ∀ r ∈ (genSemanticResponses
        (genSemanticSkeleton (bfsAssign u)
          (genMemForestFromTree (encC z) z α lmb (bfsAssign u)))
        (genMemoryStamps (genMemForestFromTree (encC z) z α lmb (bfsAssign u)))).map
          (SemanticTimestampSkeleton.semanticRecordAt (F := F) z), r.2.2 < B := by
  intro r hr
  obtain ⟨slot, hslot, rfl⟩ := List.mem_map.mp hr
  rw [semanticRecordAt_exponent]
  exact Nat.lt_of_le_of_lt
    (genSemanticResponses_exponent_le (encC z) z α u hslot) hB

/-- **Threading does not move the skeleton.**  `genBindsAt_threaded` produces
`BindsAt` at the semantic skeleton of the *threaded* forest, while this module's request and
response lists live at the skeleton of the *unthreaded* one — which is also what
`MatmulConfig65537` commits.  They are the same skeleton: `threadGenForest` rewrites only the
LogUp accumulator columns of `row`, and `genSemanticSkeleton` reads only `skel`.  So the two
halves of `SemanticIOPreimage` compose without a transport. -/
theorem genSemanticSkeleton_threadGenForest (u : NTree (GenComputeRow K))
    (inp : MemoryTable.Inputs K) (acc : K) (mf : List (NTree (GenMemoryRow K))) :
    genSemanticSkeleton u (threadGenForest inp acc mf) = genSemanticSkeleton u mf := by
  unfold genSemanticSkeleton
  congr 1
  exact threadGenForest_map_skel inp acc mf

/-! ### The program-level suppliers -/

/-- The serving identity holds on the AIR-ordered, BFS-assigned tree of any accepted program. -/
theorem genComputeSkeleton_air_requestsMatch
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    treeRequestsMatch (bfsAssign (airReorder t)) :=
  treeRequestsMatch_bfsAssign _
    (treeRequestsMatch_airReorder (genComputeSkeleton_tree_requests_match h))

/-- Memory stamp/state agreement on the generated forest of any accepted program. -/
theorem genComputeSkeleton_memForest_stampsWellFormed (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ root ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t)),
      memoryStampsWellFormed root :=
  fun root hroot =>
    memoryStampsWellFormed_of_nodesOK root
      (genComputeSkeleton_memForest_OK_air z α h root hroot)

/-- Rendered public state agrees with skeleton state at every served row. -/
theorem genComputeSkeleton_memForest_memPubSt (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ n ∈ bfsForest (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t))),
      memPubSt n.label = n.label.skel.state := by
  intro n hn
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ n).mp hn
  exact (inTree_bindMemoryRow z α
    (genComputeSkeleton_memForest_OK_air z α h u hu) hin).2.2.1

/-! ### The capstone -/

/-- **`semantic_lmio` for any program the generator accepts.**

`Def:L_mIO` at bound `Ksz`, between the record list the compute table requests and
the record list the memory table serves, for the trace of *any* accepted program — no fixture, no
fixed field, no fixed seed.

The only side condition is the `[Ksz]` window of the definition itself: the request count must fit.
Positivity is discharged (every trace has a row, and every row commits at least one record), so
`hKsz` is the whole of what is assumed. -/
theorem genSemantic_lmio (Ksz : ℕ) (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz) :
    IO.LmIO Ksz
      ((genSemanticRequests
          (genSemanticSkeleton (bfsAssign (airReorder t))
            (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t))))
          (bfsStamps (bfsAssign (airReorder t)))).map
        (SemanticTimestampSkeleton.semanticRecordAt (F := F) z))
      ((genSemanticResponses
          (genSemanticSkeleton (bfsAssign (airReorder t))
            (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t))))
          (genMemoryStamps
            (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t))))).map
        (SemanticTimestampSkeleton.semanticRecordAt (F := F) z)) := by
  have hmatch := genComputeSkeleton_air_requestsMatch h
  have hst := genComputeSkeleton_memForest_memPubSt (lmb := lmb) z α h
  have hlen := genSemanticRequests_length_eq_accAt (airReorder t)
    (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t)))
  have hpos : 1 ≤ accAt (airReorder t) (bfsRows (airReorder t)).length :=
    accAt_length_pos _ (bfsRows_length_pos _)
  refine ⟨⟨?_, ?_⟩, _, le_rfl, ?_, fun _ => Iff.rfl, ?_⟩
  · rw [List.length_map, hlen]; exact hpos
  · rw [List.length_map, hlen]; exact hKsz
  · exact semanticRecordsAt_nodup z _ (genSemanticRequests_exponent_nodup _ _)
  · exact (genSemantic_slot_perm z α (airReorder t) hmatch hst).map _

/-- Every generated trace requests at least one record, so `L_mIO`'s `1 ≤ |requests|` is
discharged rather than assumed. -/
theorem genSemanticRequests_length_pos (u : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    1 ≤ (genSemanticRequests (genSemanticSkeleton (bfsAssign u) mf)
        (bfsStamps (bfsAssign u))).length := by
  rw [genSemanticRequests_length_eq_accAt u mf]
  exact accAt_length_pos u (bfsRows_length_pos u)

/-- **The generator is *unique request*** (`Def:unique_request`): its request
records are pairwise distinct.  So `cor_uni_req_uni_resp` upgrades the relation
all the way to `L_IO` — the strict sub-language of `L_mIO` (`Lem:MEM_1`) — and the responses are *unique response* as a consequence rather than as an
assumption.  This is the step `Thm:IO_result`'s proof takes "a priori" at the paper. -/
theorem genSemantic_lio (Ksz : ℕ) (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz) :
    IO.LIO Ksz
      ((genSemanticRequests
          (genSemanticSkeleton (bfsAssign (airReorder t))
            (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t))))
          (bfsStamps (bfsAssign (airReorder t)))).map
        (SemanticTimestampSkeleton.semanticRecordAt (F := F) z))
      ((genSemanticResponses
          (genSemanticSkeleton (bfsAssign (airReorder t))
            (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t))))
          (genMemoryStamps
            (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t))))).map
        (SemanticTimestampSkeleton.semanticRecordAt (F := F) z)) :=
  by
  classical
  exact IO.cor_uni_req_uni_resp (R := (nmrMEF F K).Rec) Ksz _ _
    (semanticRecordsAt_nodup z _ (genSemanticRequests_exponent_nodup _ _))
    (genSemantic_lmio (F := F) Ksz z α h hKsz)

/-- The same, phrased at the object `SemanticIOPreimage` consumes: the two semantic lists of
`genTimestampSkeleton`.  `toSemanticIOPreimage` (`SemanticTimestampStrategy.lean:1430`) takes this
as its `semantic_lmio` argument. -/
theorem genTimestampSkeleton_lmio (Ksz : ℕ) (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hwf : ∀ root ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t)),
        memoryStampsWellFormed root)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz) :
    IO.LmIO Ksz
      ((genTimestampSkeleton F (airReorder t)
        (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t)))
        hwf).semanticRequestsAt z)
      ((genTimestampSkeleton F (airReorder t)
        (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t)))
        hwf).semanticResponsesAt z) :=
  genSemantic_lmio (F := F) Ksz z α h hKsz

/-- `genTimestampSkeleton`'s `memoryStampsWellFormed` argument, discharged for any accepted
program: the capstone with no hypothesis about the forest at all. -/
theorem genTimestampSkeleton_lmio' (Ksz : ℕ) (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz) :
    IO.LmIO Ksz
      ((genTimestampSkeleton F (airReorder t)
        (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t)))
        (genComputeSkeleton_memForest_stampsWellFormed z α h)).semanticRequestsAt z)
      ((genTimestampSkeleton F (airReorder t)
        (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t)))
        (genComputeSkeleton_memForest_stampsWellFormed z α h)).semanticResponsesAt z) :=
  genTimestampSkeleton_lmio Ksz z α h _ hKsz

end

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_tree_requests_match
#print axioms Nock.NockVMROM.Thm54.TraceGen.hasReadRootSlot_memForest
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemantic_slot_mem
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemantic_length
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemanticResponses_nodup
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemantic_slot_perm
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemantic_lmio
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemantic_lio
#print axioms Nock.NockVMROM.Thm54.TraceGen.genTimestampSkeleton_lmio
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemanticSkeleton_threadGenForest
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemanticRequestsAt_timestampBound
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemanticResponsesAt_timestampBound
