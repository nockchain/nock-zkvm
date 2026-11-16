/-
  Nock/NockVMROM/Thm54/TraceGen/GenGenericRowFacts.lean

  **`∀`-generic row, tree and threading facts about the generator — relocated here because a
  filename is not evidence of scope.**

  Every declaration in this module is generic: `{K : Type} [Field K]` with no `GaloisField`
  abbrev, no fixed axis, state, seed, program or config, and no hypothesis pinning any of those
  to a value.  Nothing here is about Tier A, and nothing here is about the matmul fixture.

  **Why the module exists.**  These declarations used to live in
  `GenMatmulNodup.lean` (`map_getRecordExp_one/_two/_three`, `renderNode_active_timestamps`,
  `accAt_le_three_mul`) and `GenTierAMemoryTrace.lean` (`mappedRecordTree`, `axisMTree` and its
  `ofNTree` reductions, the `genMemKey` / `genRespKey` threading transports, and
  `axisMTree_threadGenForest` / `servedGen_thread_get`).  Documenting it did not stop the third recurrence, so the declarations were moved.

  * a signature that *reads* generic can hide a fixed value — either in a config namespace's
    `abbrev K := GaloisField p 3`, or in an ordinary hypothesis such as the
    served-walk theory's `haxis : s.axis = 2` (`EQ`, `ES`);
  * and, the inverse, generic theory can sit in a fixture-named file (`FG` §2, `FF`).

  **The filename settles neither direction.**  `#check` the declaration, *and* read every
  hypothesis for a fixed value.  Both were done for every declaration below before it was moved:
  each elaborates at `{K : Type} [Field K]`, and no hypothesis pins a value.

  This is a **relocation, not a refactor**: names, statements and proofs are byte-identical to
  what stood in the two source files, so every existing call site compiles unchanged.  The
  namespace is still `Nock.NockVMROM.Thm54.TraceGen`, so unqualified uses keep resolving.  Both
  source files now import this module.

  What is here, and what each thing is generic in:

  | group | declarations | generic in |
  |---|---|---|
  | mapped trees | `mappedRecordTree`, `axisMTree` | field, encoder, coins, root/child noun, axis, exponent |
  | `ofNTree` reductions | `axisMTree_read_node`, `_verify_node`, `_decompose_node`, `axisMTree_halt_any`, `axisMTree_read_of`, `_verify_of`, `_decompose_of` | field, coin, row data, children |
  | memory-key transport | `genMemKey`, `threadGenRows_map_memKey`, `threadGenForest_map_memKey`, `axisMTree_of_memKey`, `axisMTree_threadGenForest` | field, inputs, accumulator, forest, index |
  | response-key transport | `genRespKey`, `threadGenRows_map_respKey`, `threadGenForest_map_respKey`, `responseRecords_respKey`, `bfs_respKeys_of_map`, `servedGen_of_respKey`, `servedGen_mapped_row`, `servedGen_thread_get` | field, inputs, accumulator, forest, index |
  | rendered timestamps | `map_getRecordExp_one/_two/_three`, `renderNode_active_timestamps`, `accAt_le_three_mul` | field, coins, row — `renderNode_active_timestamps` covers **all eleven states** and carries no hypothesis at all |

  The two threading transports are what `rootTraceOfRecordTree`'s `hax` / `hsrv` arguments need;
  `renderNode_active_timestamps` is the record-timestamp readout across every state.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierASemanticData
import Nock.NockVMROM.Thm54.TraceGen.GenTierATopology
import Nock.NockVMROM.Thm54.TraceGen.GenSound
import Nock.NockVMROM.Thm54.BoundSemanticTrace
import Nock.NockVMROM.Thm54.ServedMemoryTrace
import Nock.NockVMROM.Thm54.AxisSoundness
import Nock.NockVMROM.Thm54.MonolithicRowLayout

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TraceGen

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## Mapped annotated record trees and their axis tree

Relocated from `GenTierAMemoryTrace.lean:42-48`.  Both are `∀`-generic definitions: the encoder
`E`, the coins `z`/`α`, the root and child nouns, the axis and the exponent are all free. -/

noncomputable def mappedRecordTree (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (root child : Noun) (axis e : ℕ) :
    NTree (MState × DTmem K) :=
  mapNTree GenMemoryRow.row (genAnnotatedRecordTree E z α lmb root child axis e)

noncomputable def axisMTree (α : K) (t : NTree (MState × DTmem K)) : MTree K :=
  (ofNTree (timestampExpAt α) t).toMTree

/-! ## Generic `ofNTree` reductions

Relocated from `GenTierAMemoryTrace.lean:273-289,557-591`.  One `axisMTree` equation per memory
state, at arbitrary row data and arbitrary children. -/

theorem axisMTree_read_node (α : K) (d : DTmem K)
    (c : NTree (MState × DTmem K)) :
    axisMTree α (.node (MState.read_root, d) [c]) =
      .read (timestampExp α d.2.mem.ts) (axisMTree α c) := by
  rw [axisMTree, ofNTree_read]; rfl

theorem axisMTree_verify_node (α : K) (d : DTmem K)
    (c : NTree (MState × DTmem K)) :
    axisMTree α (.node (MState.verify_child, d) [c]) =
      .verify (timestampExp α d.2.mem.ts) d.2.mem.axis (axisMTree α c) := by
  rw [axisMTree, ofNTree_verify]; rfl

theorem axisMTree_decompose_node (α : K) (d : DTmem K)
    (l r : NTree (MState × DTmem K)) :
    axisMTree α (.node (MState.decompose, d) [l, r]) =
      .decompose (axisMTree α l) (axisMTree α r) := by
  rw [axisMTree, ofNTree_decompose]; rfl

theorem axisMTree_halt_any (α : K) (d : DTmem K)
    (ch : List (NTree (MState × DTmem K))) :
    axisMTree α (.node (MState.halt, d) ch) = .halt := by
  simp [axisMTree, ofNTree, MemWalk.toMTree]

theorem axisMTree_decompose_of (α : K) (d : DTmem K) :
    ∀ ch : List (NTree (MState × DTmem K)),
      axisMTree α (.node (MState.decompose, d) ch) =
        match ch with
        | [l, r] => .decompose (axisMTree α l) (axisMTree α r)
        | _ => .halt
  | [] => by simp [axisMTree, ofNTree, MemWalk.toMTree]
  | [_] => by simp [axisMTree, ofNTree, MemWalk.toMTree]
  | [l, r] => axisMTree_decompose_node α d l r
  | _ :: _ :: _ :: _ => by simp [axisMTree, ofNTree, MemWalk.toMTree]

theorem axisMTree_read_of (α : K) (d : DTmem K) :
    ∀ ch : List (NTree (MState × DTmem K)),
      axisMTree α (.node (MState.read_root, d) ch) =
        match ch with
        | [c] => .read (timestampExp α d.2.mem.ts) (axisMTree α c)
        | _ => .halt
  | [] => by simp [axisMTree, ofNTree, MemWalk.toMTree]
  | [c] => axisMTree_read_node α d c
  | _ :: _ :: _ => by simp [axisMTree, ofNTree, MemWalk.toMTree]

theorem axisMTree_verify_of (α : K) (d : DTmem K) :
    ∀ ch : List (NTree (MState × DTmem K)),
      axisMTree α (.node (MState.verify_child, d) ch) =
        match ch with
        | [c] => .verify (timestampExp α d.2.mem.ts) d.2.mem.axis (axisMTree α c)
        | _ => .halt
  | [] => by simp [axisMTree, ofNTree, MemWalk.toMTree]
  | [c] => axisMTree_verify_node α d c
  | _ :: _ :: _ => by simp [axisMTree, ofNTree, MemWalk.toMTree]

/-! ## Memory-key threading transport

Relocated from `GenTierAMemoryTrace.lean:531-555,593-736`.  `threadGenForest` rewrites only the
threaded accumulator, so the `(state, mem)` key of every row survives it; `axisMTree` reads only
that key, hence `axisMTree_threadGenForest`.  This is the transport
`rootTraceOfRecordTree`'s `hax` argument needs, at arbitrary `inp`, `acc`, `α`, `forest` and
index. -/

def genMemKey (g : GenMemoryRow K) : MState × ComputeTable.MemRec K :=
  (g.row.1, g.row.2.2.mem)

theorem threadGenRows_map_memKey (inp : MemoryTable.Inputs K) :
    ∀ acc gs,
      (threadGenRows inp acc gs).map genMemKey = gs.map genMemKey
  | _, [] => rfl
  | acc, g :: gs => by
      simp [threadGenRows, threadGenRow_snd, genMemKey, setGenAcc_row1, setGenAcc_mem]
      exact threadGenRows_map_memKey inp (threadGenRow inp acc g).1 gs

theorem threadGenForest_map_memKey (inp : MemoryTable.Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K))) :
    (threadGenForest inp acc forest).map (mapNTree genMemKey) =
      forest.map (mapNTree genMemKey) := by
  unfold threadGenForest
  rw [zipBfs_mapNTree, threadGenRows_map_memKey]
  have hlabs :
      ((bfsForest forest).map NTree.label).map genMemKey =
        (bfsForest (forest.map (mapNTree genMemKey))).map NTree.label := by
    rw [bfsForest_mapNTree, List.map_map, List.map_map]
    refine List.map_congr_left ?_
    intro t _
    exact (mapNTree_label genMemKey t).symm
  rw [hlabs, zipBfs_self]

theorem axisMTree_of_memKey (α : K) (t u : NTree (GenMemoryRow K))
    (h : mapNTree genMemKey t = mapNTree genMemKey u) :
    axisMTree α (mapNTree GenMemoryRow.row t) =
      axisMTree α (mapNTree GenMemoryRow.row u) := by
  let P := fun t : NTree (GenMemoryRow K) =>
    ∀ u, mapNTree genMemKey t = mapNTree genMemKey u →
      axisMTree α (mapNTree GenMemoryRow.row t) =
        axisMTree α (mapNTree GenMemoryRow.row u)
  refine (show P t from ?_) u h
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro lblt cht ih u htu
    cases u with
    | node lblu chu =>
      simp only [mapNTree] at htu
      injection htu with hkey hch
      obtain ⟨hstEq, hmem⟩ := Prod.mk.inj hkey
      cases hst : lblt.row.1 with
      | halt =>
        have hstu : lblu.row.1 = .halt := hstEq.symm.trans hst
        have ht : lblt.row = (.halt, lblt.row.2) := Prod.ext hst rfl
        have hu : lblu.row = (.halt, lblu.row.2) := Prod.ext hstu rfl
        rw [mapNTree, mapNTree, ht, hu, axisMTree_halt_any, axisMTree_halt_any]
      | decompose =>
        have hstu : lblu.row.1 = .decompose := hstEq.symm.trans hst
        have ht : lblt.row = (.decompose, lblt.row.2) := Prod.ext hst rfl
        have hu : lblu.row = (.decompose, lblu.row.2) := Prod.ext hstu rfl
        rw [mapNTree, mapNTree, ht, hu, axisMTree_decompose_of, axisMTree_decompose_of]
        cases cht with
        | nil =>
          cases chu with
          | nil => simp
          | cons _ _ => simp [List.map] at hch
        | cons l1 rest1 =>
          cases rest1 with
          | nil =>
            cases chu with
            | nil => simp [List.map] at hch
            | cons _ rest2 =>
              cases rest2 with
              | nil => simp
              | cons _ _ => simp [List.map] at hch
          | cons r1 tail1 =>
            cases tail1 with
            | nil =>
              cases chu with
              | nil => simp [List.map] at hch
              | cons l2 rest2 =>
                cases rest2 with
                | nil => simp [List.map] at hch
                | cons r2 tail2 =>
                  cases tail2 with
                  | nil =>
                    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hch ⊢
                    obtain ⟨hl, hr⟩ := hch
                    exact congrArg₂ MTree.decompose (ih l1 (by simp) l2 hl)
                      (ih r1 (by simp) r2 hr)
                  | cons _ _ => simp [List.map] at hch
            | cons _ _ =>
              cases chu with
              | nil => simp [List.map] at hch
              | cons _ rest2 =>
                cases rest2 with
                | nil => simp [List.map] at hch
                | cons _ tail2 =>
                  cases tail2 with
                  | nil => simp [List.map] at hch
                  | cons _ _ => simp
      | read_root =>
        have hstu : lblu.row.1 = .read_root := hstEq.symm.trans hst
        have ht : lblt.row = (.read_root, lblt.row.2) := Prod.ext hst rfl
        have hu : lblu.row = (.read_root, lblu.row.2) := Prod.ext hstu rfl
        rw [mapNTree, mapNTree, ht, hu, axisMTree_read_of, axisMTree_read_of]
        cases cht with
        | nil =>
          cases chu with
          | nil => simp
          | cons _ _ => simp [List.map] at hch
        | cons c1 rest1 =>
          cases rest1 with
          | nil =>
            cases chu with
            | nil => simp [List.map] at hch
            | cons c2 rest2 =>
              cases rest2 with
              | nil =>
                simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hch ⊢
                refine congrArg₂ MTree.read ?_ (ih c1 (by simp) c2 hch)
                simp [hmem]
              | cons _ _ => simp [List.map] at hch
          | cons _ _ =>
            cases chu with
            | nil => simp [List.map] at hch
            | cons _ rest2 =>
              cases rest2 with
              | nil => simp [List.map] at hch
              | cons _ _ => simp
      | verify_child =>
        have hstu : lblu.row.1 = .verify_child := hstEq.symm.trans hst
        have ht : lblt.row = (.verify_child, lblt.row.2) := Prod.ext hst rfl
        have hu : lblu.row = (.verify_child, lblu.row.2) := Prod.ext hstu rfl
        rw [mapNTree, mapNTree, ht, hu, axisMTree_verify_of, axisMTree_verify_of]
        cases cht with
        | nil =>
          cases chu with
          | nil => simp
          | cons _ _ => simp [List.map] at hch
        | cons c1 rest1 =>
          cases rest1 with
          | nil =>
            cases chu with
            | nil => simp [List.map] at hch
            | cons c2 rest2 =>
              cases rest2 with
              | nil =>
                simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hch ⊢
                simp [hmem]
                exact ih c1 (by simp) c2 hch
              | cons _ _ => simp [List.map] at hch
          | cons _ _ =>
            cases chu with
            | nil => simp [List.map] at hch
            | cons _ rest2 =>
              cases rest2 with
              | nil => simp [List.map] at hch
              | cons _ _ => simp
  · intro c hc
    simp at hc
  · intro head tail ihHead ihTail c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

theorem axisMTree_threadGenForest (inp : MemoryTable.Inputs K) (acc α : K)
    (forest : List (NTree (GenMemoryRow K))) {i : ℕ} (hi : i < forest.length) :
    axisMTree α (mapNTree GenMemoryRow.row
        ((threadGenForest inp acc forest)[i]'(by rwa [threadGenForest_length]))) =
      axisMTree α (mapNTree GenMemoryRow.row forest[i]) := by
  have heq := threadGenForest_map_memKey inp acc forest
  have hi' : i < ((threadGenForest inp acc forest).map (mapNTree genMemKey)).length := by
    simpa [List.length_map, threadGenForest_length] using hi
  have hkeys := List.getElem_of_eq heq hi'
  simp only [List.getElem_map] at hkeys
  exact axisMTree_of_memKey α _ _ hkeys

/-! ## Response-key threading transport

Relocated from `GenTierAMemoryTrace.lean:744-843`.  The `servedGen` half of the same story: the
`(pub.st, pub.mem, pub.ver)` key survives threading, `responseRecords` reads `ver`/`mem`, hence
`servedGen_thread_get` — the transport `rootTraceOfRecordTree`'s `hsrv` argument needs, at
arbitrary `inp`, `acc`, `forest` and index. -/

def genRespKey (g : GenMemoryRow K) : MState × ComputeTable.MemRec K × Bool :=
  (g.row.2.2.st, g.row.2.2.mem, g.row.2.2.ver)

theorem threadGenRows_map_respKey (inp : MemoryTable.Inputs K) :
    ∀ acc gs,
      (threadGenRows inp acc gs).map genRespKey = gs.map genRespKey
  | _, [] => rfl
  | acc, g :: gs => by
      simp [threadGenRows, threadGenRow_snd, genRespKey,
        setGenAcc_pub_st, setGenAcc_mem, setGenAcc_ver]
      exact threadGenRows_map_respKey inp (threadGenRow inp acc g).1 gs

theorem threadGenForest_map_respKey (inp : MemoryTable.Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K))) :
    (threadGenForest inp acc forest).map (mapNTree genRespKey) =
      forest.map (mapNTree genRespKey) := by
  unfold threadGenForest
  rw [zipBfs_mapNTree, threadGenRows_map_respKey]
  have hlabs :
      ((bfsForest forest).map NTree.label).map genRespKey =
        (bfsForest (forest.map (mapNTree genRespKey))).map NTree.label := by
    rw [bfsForest_mapNTree, List.map_map, List.map_map]
    refine List.map_congr_left ?_
    intro t _
    exact (mapNTree_label genRespKey t).symm
  rw [hlabs, zipBfs_self]

theorem responseRecords_respKey (g : GenMemoryRow K) :
    responseRecords g.row.2.2 =
      match genRespKey g with
      | (_, m, true) => [m]
      | (_, _, false) => [] := by
  simp only [responseRecords, genRespKey]
  cases hv : g.row.2.2.ver <;> simp [hv]

theorem bfs_respKeys_of_map (t : NTree (GenMemoryRow K)) :
    (bfsForest [mapNTree genRespKey t]).map NTree.label =
      (bfsForest [t]).map (genRespKey ∘ NTree.label) := by
  rw [show [mapNTree genRespKey t] = [t].map (mapNTree genRespKey) from rfl]
  rw [bfsForest_mapNTree, List.map_map]
  refine List.map_congr_left ?_
  intro u _
  simp [Function.comp, mapNTree_label]

theorem servedGen_of_respKey (t u : NTree (GenMemoryRow K))
    (h : mapNTree genRespKey t = mapNTree genRespKey u) :
    servedGen [t] = servedGen [u] := by
  have hkeys :
      (bfsForest [t]).map (genRespKey ∘ NTree.label) =
        (bfsForest [u]).map (genRespKey ∘ NTree.label) := by
    rw [← bfs_respKeys_of_map, ← bfs_respKeys_of_map, h]
  rw [servedGen_eq_labels, servedGen_eq_labels]
  have hgs :
      ((bfsForest [t]).map NTree.label).map genRespKey =
        ((bfsForest [u]).map NTree.label).map genRespKey := by
    simpa [List.map_map] using hkeys
  have hflat :
      ∀ gs hs : List (GenMemoryRow K),
        gs.map genRespKey = hs.map genRespKey →
        gs.flatMap (fun g => responseRecords g.row.2.2) =
          hs.flatMap (fun g => responseRecords g.row.2.2) := by
    intro gs
    induction gs with
    | nil =>
      intro hs h
      cases hs <;> simp_all
    | cons g gs ih =>
      intro hs h
      cases hs with
      | nil => simp at h
      | cons h0 hs =>
        simp only [List.map_cons, List.cons.injEq] at h
        obtain ⟨hk, ht⟩ := h
        rw [List.flatMap_cons, List.flatMap_cons, responseRecords_respKey,
          responseRecords_respKey, hk]
        exact congrArg (List.append _) (ih hs ht)
  exact hflat _ _ hgs

theorem servedGen_mapped_row (t : NTree (GenMemoryRow K)) :
    (bfsForest [mapNTree GenMemoryRow.row t]).flatMap
      (fun n => responseRecords n.label.2.2) =
      servedGen [t] := by
  rw [show [mapNTree GenMemoryRow.row t] =
        [t].map (mapNTree GenMemoryRow.row) from rfl]
  rw [bfsForest_mapNTree, List.flatMap_map]
  simp [servedGen, mapNTree_label]

theorem servedGen_thread_get (inp : MemoryTable.Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K))) {i : ℕ} (hi : i < forest.length) :
    servedGen [(threadGenForest inp acc forest)[i]'(by rwa [threadGenForest_length])] =
      servedGen [forest[i]] := by
  have heq := threadGenForest_map_respKey inp acc forest
  have hi' : i < ((threadGenForest inp acc forest).map (mapNTree genRespKey)).length := by
    simpa [List.length_map, threadGenForest_length] using hi
  have hkeys := List.getElem_of_eq heq hi'
  simp only [List.getElem_map] at hkeys
  exact servedGen_of_respKey _ _ hkeys

/-! ## Rendered opcode-active timestamps

Relocated from `GenMatmulNodup.lean:32-105`.  **Nothing here is matmul.**
`renderNode_active_timestamps` carries no hypothesis at all and covers all eleven compute states
(verified: the proof case-splits on `g.skel.state` exhaustively); `accAt_le_three_mul` is the
three-records-per-row bound at an arbitrary compute tree. -/

theorem map_getRecordExp_one (α : K) (stamp : ComputeTimestampRow) :
    (List.range 1).map (fun i => α ^ getRecordExp stamp i) =
      [α ^ stamp.recordExponent 0] := by
  simp [getRecordExp, List.range_succ, List.range_zero]

theorem map_getRecordExp_two (α : K) (stamp : ComputeTimestampRow) :
    (List.range 2).map (fun i => α ^ getRecordExp stamp i) =
      [α ^ stamp.recordExponent 0, α ^ stamp.recordExponent 1] := by
  simp [getRecordExp, List.range_succ, List.range_zero]

theorem map_getRecordExp_three (α : K) (stamp : ComputeTimestampRow) :
    (List.range 3).map (fun i => α ^ getRecordExp stamp i) =
      [α ^ stamp.recordExponent 0, α ^ stamp.recordExponent 1,
        α ^ stamp.recordExponent 2] := by
  simp [getRecordExp, List.range_succ, List.range_zero]

theorem renderNode_active_timestamps (z α : K) (g : GenComputeRow K) :
    (activeRequestRecords (renderNode z α g).row.2.2.1).map (fun r => r.ts) =
      (List.range (Nock.Framework.recordCount g.skel.state)).map
        (fun i => α ^ getRecordExp g.stamp i) := by
  cases hs : g.skel.state
  · rw [renderNode_op0_row z α g hs]
    simp [hs, activeRequestRecords, renderOp0Row, Nock.Framework.recordCount,
      map_getRecordExp_two]
  · rw [renderNode_op1_row z α g hs]
    simp [hs, activeRequestRecords, renderOp1Row, Nock.Framework.recordCount,
      map_getRecordExp_one, getRecordExp]
  · rw [renderNode_op2_row z α g hs]
    simp [hs, activeRequestRecords, renderOp2Row, Nock.Framework.recordCount,
      map_getRecordExp_two]
  · rw [renderNode_op3_row z α g hs]
    simp [hs, activeRequestRecords, renderOp3Row, Nock.Framework.recordCount,
      map_getRecordExp_one, getRecordExp]
  · rw [renderNode_op4_row z α g hs]
    simp [hs, activeRequestRecords, renderOp4Row, Nock.Framework.recordCount,
      map_getRecordExp_one, getRecordExp]
  · rw [renderNode_op5_row z α g hs]
    simp [hs, activeRequestRecords, renderOp5Row, Nock.Framework.recordCount,
      map_getRecordExp_two]
  · rw [renderNode_op6_row z α g hs]
    simp [hs, activeRequestRecords, renderOp6Row, Nock.Framework.recordCount,
      map_getRecordExp_three]
  · rw [renderNode_op7_row z α g hs]
    simp [hs, activeRequestRecords, renderOp7Row, Nock.Framework.recordCount,
      map_getRecordExp_two]
  · rw [renderNode_op8_row z α g hs]
    simp [hs, activeRequestRecords, renderOp8Row, Nock.Framework.recordCount,
      map_getRecordExp_two]
  · rw [renderNode_op9_row z α g hs]
    simp [hs, activeRequestRecords, renderOp9Row, Nock.Framework.recordCount,
      map_getRecordExp_three]
  · rw [renderNode_cons_row z α g hs]
    simp [hs, activeRequestRecords, renderConsRow, Nock.Framework.recordCount,
      map_getRecordExp_one, getRecordExp]

theorem accAt_le_three_mul (t : NTree (GenComputeRow K)) :
    ∀ k, accAt t k ≤ 3 * k
  | 0 => by simp [accAt]
  | k + 1 => by
      have ih := accAt_le_three_mul t k
      change accAt t k +
          (match (bfsRows t)[k]? with
            | some g => Nock.Framework.recordCount g.skel.state
            | none => 0) ≤ 3 * (k + 1)
      cases h? : (bfsRows t)[k]? with
      | none =>
        simp [h?]
        omega
      | some g =>
        simp [h?]
        have hrc : Nock.Framework.recordCount g.skel.state ≤ 3 := by
          simpa [mem_record_arity] using
            Nock.Framework.recordCount_le g.skel.state
        omega

end Nock.NockVMROM.Thm54.TraceGen
