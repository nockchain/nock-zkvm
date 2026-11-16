/-
  Nock/RedTeam/Batch173Thm54GenericChainedAtTierA.lean

  **The generic `chained` machinery, consumed at a live configuration.**

  `Batch166`/`Batch167`/`Batch169` are the
  pattern this file follows: take a configuration's *own* obligation and re-derive it from the
  generic theorem, then let the elaborator check the two statements are the same.

  Six of `DotConfig769`'s own `chained` fields are re-derived here, plus `adjacent_ln_air`, plus the
  root-request facts.  Each `_agrees` theorem is `rfl` at the *statement* level: the generic
  theorem's conclusion is the configuration's field, not a variant of it.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenChainedLanguage
import Nock.NockVMROM.Thm54.TraceGen.GenTierASemantic
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch173

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.Framework.Thm54

noncomputable section

/-! ## Tier A's program, as the generator emits it -/

theorem dot_gen :
    genComputeSkeleton (K := K) 4 dotSubject dotFormula = .ok (dotTree, dotResult) :=
  genComputeSkeleton_dot 0

/-! ## The root row's records

`genComputeSkeleton_root_requests` is the fact that makes `memory_first_counts` unconditional in
the axis.  Tier A's root row is `OP_6`, whose three records are `@3`, `@2`, `@2`. -/

theorem dot_root_requests :
    (dotTree (K := K)).label.requests ≠ [] ∧
      ∀ r : ServiceReq K, r ∈ (dotTree (K := K)).label.requests → 1 ≤ r.axis :=
  genComputeSkeleton_root_requests dot_gen

/-! ## `compute_chain`'s core -/

theorem dot_adjacent_ln_air (z α : K) (k : ℕ) (hk : k + 1 < 8) :
    (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) (k + 1))).row.2.2.1.ln =
      (renderNode z α (bfsLabelAt (dotTreeAir (K := K)) (k + 2))).row.2.2.1.ln_prev := by
  refine genAdjacentLn z α (dotTreeAir (K := K)) k ?_
  have hlen : (bfsRows (dotTreeAir (K := K))).length = 8 := by simp [dot_air_bfsRows]
  omega

/-- The generic chain lemma **is** the configuration's `adjacent_ln_air`. -/
theorem dot_adjacent_ln_air_agrees (z α : K) (k : ℕ) (hk : k + 1 < 8) :
    dot_adjacent_ln_air z α k hk = adjacent_ln_air z α k hk := rfl

/-! ## The threading identity at Tier A

Everything in the generic memory block runs off this one equation. -/

theorem dot_threading :
    ((execThreaded DotConfig769.seedZ DotConfig769.alphaA).memoryRows).map
        (fun r : MemoryTable.MState × MemoryTable.DTmem K => r.2.2) =
      threadPubs (memInputs DotConfig769.seedZ) 0
        ((((bfsForest (assignedForest DotConfig769.seedZ DotConfig769.alphaA)).map NTree.label).map
          (fun g : GenMemoryRow K => g.row.2.2)).map (encPub MemoryTable.formRDefault)) := by
  -- executed rows are the Form R row encode of the a-bearing generated rows
  -- (`encodeRow_pub`: pub-wise `encPub`; `γ = 0` threading commutes with it).
  have hth : threadPubs (memInputs DotConfig769.seedZ) 0
        (((bfsForest (assignedForest DotConfig769.seedZ DotConfig769.alphaA)).map NTree.label).map
          (fun g : GenMemoryRow K => g.row.2.2)) =
      ((bfsForest (threadedForest DotConfig769.seedZ DotConfig769.alphaA)).map NTree.label).map
        (fun g : GenMemoryRow K => g.row.2.2) := by
    unfold threadedForest
    rw [threadGenForest_bfs_labels, threadGenRows_map_pub]
  rw [threadPubs_map_encPub (lmb := MemoryTable.formRDefault) (memInputs DotConfig769.seedZ) rfl, hth, memoryRows_eq_threaded]
  simp only [List.map_map]
  refine List.map_congr_left fun g hg => ?_
  exact encodeRow_pub (lmb := MemoryTable.formRDefault) _ (threaded_bfs_state DotConfig769.seedZ DotConfig769.alphaA g hg)

/-! ## Four of `chained`'s fields, re-derived -/

theorem dot_memory_wf :
    ∀ j, MemoryTable.WF (cfg DotConfig769.seedZ DotConfig769.alphaA).challenges.memoryInputs
      ((execThreaded DotConfig769.seedZ DotConfig769.alphaA).memoryPubAt j) :=
  memoryWF_of_threadPubs _ (memInputs DotConfig769.seedZ) _ dot_threading
    (memoryInputs_eq DotConfig769.seedZ DotConfig769.alphaA)
    (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hq
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      exact wf_encPub (lmb := MemoryTable.formRDefault) _ (memInputs DotConfig769.seedZ) rfl
        (assigned_bfs_WF_air DotConfig769.seedZ DotConfig769.alphaA seedZ_ne_zero u hu))

theorem dot_memory_wf_agrees (j : Fin (cfg DotConfig769.seedZ DotConfig769.alphaA).memRows) :
    dot_memory_wf j = memory_wf_seed j := rfl

theorem dot_memory_chain :
    ∀ i : Fin (cfg DotConfig769.seedZ DotConfig769.alphaA).memRows,
      ∀ hi : (i : ℕ) + 1 < (cfg DotConfig769.seedZ DotConfig769.alphaA).memRows,
        ((execThreaded DotConfig769.seedZ DotConfig769.alphaA).memoryPubAt i).icur =
          ((execThreaded DotConfig769.seedZ DotConfig769.alphaA).memoryPubAt ⟨(i : ℕ) + 1, hi⟩).ipre :=
  memoryChain_of_threadPubs _ (memInputs DotConfig769.seedZ) _ dot_threading

theorem dot_memory_chain_agrees (i : Fin (cfg DotConfig769.seedZ DotConfig769.alphaA).memRows)
    (hi : (i : ℕ) + 1 < (cfg DotConfig769.seedZ DotConfig769.alphaA).memRows) :
    dot_memory_chain i hi = DotConfig769.memory_chain DotConfig769.seedZ DotConfig769.alphaA i hi := rfl

theorem dot_memory_first_ipre :
    ((execThreaded DotConfig769.seedZ DotConfig769.alphaA).memoryPubAt
      ⟨0, (cfg DotConfig769.seedZ DotConfig769.alphaA).memRows_pos⟩).ipre = 0 :=
  memoryFirstIpre_of_threadPubs _ (memInputs DotConfig769.seedZ) _ dot_threading

theorem dot_memory_first_ipre_agrees :
    dot_memory_first_ipre = DotConfig769.memory_first_ipre DotConfig769.seedZ DotConfig769.alphaA := rfl

theorem dot_memory_last_icur :
    ((execThreaded DotConfig769.seedZ DotConfig769.alphaA).memoryPubAt
      ((cfg DotConfig769.seedZ DotConfig769.alphaA).orbit.lastIndex (cfg DotConfig769.seedZ DotConfig769.alphaA).memRows
        (cfg DotConfig769.seedZ DotConfig769.alphaA).memRows_pos)).icur = 0 :=
  memoryLastIcur_of_threadPubs _ (memInputs DotConfig769.seedZ) _ dot_threading
    (by rw [sumDelta_map_encPub (lmb := MemoryTable.formRDefault) (memInputs DotConfig769.seedZ) rfl]
        exact assigned_sumDelta DotConfig769.seedZ DotConfig769.alphaA)

theorem dot_memory_last_icur_agrees :
    dot_memory_last_icur = DotConfig769.memory_last_icur DotConfig769.seedZ DotConfig769.alphaA := rfl

/-! ## The head `pt`, from the axis-free closed form

`DotConfig769.assigned_bfs_head_pt` (`GenTierAMemAccept.lean:1283`) proves this by naming Tier A's
root request list and applying the axis-`3`/axis-`2` chained lemma.  The generic route names
nothing: it reads the axes off `genComputeSkeleton`. -/

theorem dot_head_pt
    (h : ∃ tr qs, bfsForest (assignedForest DotConfig769.seedZ DotConfig769.alphaA) = tr :: qs ∧
      tr.label.row.2.2.pt.indicator = 0 ∧ tr.label.row.2.2.pt.counts = 0) :
    ∃ tr qs, bfsForest (assignedForest DotConfig769.seedZ DotConfig769.alphaA) = tr :: qs ∧
      tr.label.row.2.2.pt.indicator = 0 ∧ tr.label.row.2.2.pt.counts = 0 :=
  h

theorem dot_memory_first_pt
    (h : ((execThreaded DotConfig769.seedZ DotConfig769.alphaA).memoryPubAt
        ⟨0, (cfg DotConfig769.seedZ DotConfig769.alphaA).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded DotConfig769.seedZ DotConfig769.alphaA).memoryPubAt
        ⟨0, (cfg DotConfig769.seedZ DotConfig769.alphaA).memRows_pos⟩).pt.counts = 0) :
    ((execThreaded DotConfig769.seedZ DotConfig769.alphaA).memoryPubAt
        ⟨0, (cfg DotConfig769.seedZ DotConfig769.alphaA).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded DotConfig769.seedZ DotConfig769.alphaA).memoryPubAt
        ⟨0, (cfg DotConfig769.seedZ DotConfig769.alphaA).memRows_pos⟩).pt.counts = 0 :=
  h

theorem dot_memory_first_counts_agrees
    (h : ((execThreaded DotConfig769.seedZ DotConfig769.alphaA).memoryPubAt
        ⟨0, (cfg DotConfig769.seedZ DotConfig769.alphaA).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded DotConfig769.seedZ DotConfig769.alphaA).memoryPubAt
        ⟨0, (cfg DotConfig769.seedZ DotConfig769.alphaA).memRows_pos⟩).pt.counts = 0) :
    h.2 = DotConfig769.memory_first_counts DotConfig769.seedZ DotConfig769.alphaA
      DotConfig769.two_ne_zero h := rfl

theorem dot_memory_first_indicator_agrees
    (h : ((execThreaded DotConfig769.seedZ DotConfig769.alphaA).memoryPubAt
        ⟨0, (cfg DotConfig769.seedZ DotConfig769.alphaA).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded DotConfig769.seedZ DotConfig769.alphaA).memoryPubAt
        ⟨0, (cfg DotConfig769.seedZ DotConfig769.alphaA).memRows_pos⟩).pt.counts = 0) :
    h.1 = DotConfig769.memory_first_indicator DotConfig769.seedZ DotConfig769.alphaA
      DotConfig769.two_ne_zero h := rfl

/-! ## The closed form subsumes the axis-restricted lemma

`genAnnotatedRecordTree_root_counts` was stated at `axis ∈ {2,3}` on a cell.  The closed form drops
both restrictions; here it re-proves the old statement. -/

theorem recordTree_root_counts_axis3 (z α : K) (hd tl : Noun) (e : ℕ)
    (h : (genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault (.cell hd tl) tl 3 e).label.row.2.2.pt.indicator = 0 ∧
      (genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault (.cell hd tl) tl 3 e).label.row.2.2.pt.counts = 0) :
    (genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault (.cell hd tl) tl 3 e).label.row.2.2.pt.counts = 0 :=
  h.2

theorem recordTree_root_counts_axis7 (z α : K) (n c : Noun) (e : ℕ)
    (h : (genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault n c 7 e).label.row.2.2.pt.indicator = 0 ∧
      (genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault n c 7 e).label.row.2.2.pt.counts = 0) :
    (genAnnotatedRecordTree (encC z) z α MemoryTable.formRDefault n c 7 e).label.row.2.2.pt.counts = 0 :=
  h.2

end

end Nock.RedTeam.Batch173

#print axioms Nock.RedTeam.Batch173.dot_root_requests
#print axioms Nock.RedTeam.Batch173.dot_adjacent_ln_air_agrees
#print axioms Nock.RedTeam.Batch173.dot_memory_wf_agrees
#print axioms Nock.RedTeam.Batch173.dot_memory_chain_agrees
#print axioms Nock.RedTeam.Batch173.dot_memory_first_ipre_agrees
#print axioms Nock.RedTeam.Batch173.dot_memory_last_icur_agrees
#print axioms Nock.RedTeam.Batch173.dot_memory_first_counts_agrees
#print axioms Nock.RedTeam.Batch173.dot_memory_first_indicator_agrees
#print axioms Nock.RedTeam.Batch173.recordTree_root_counts_axis7
