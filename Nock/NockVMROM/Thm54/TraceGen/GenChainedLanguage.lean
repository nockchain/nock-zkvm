/-
  Nock/NockVMROM/Thm54/TraceGen/GenChainedLanguage.lean

  This module carries that prediction out.  Every theorem is `∀ program accepted by
  `genComputeSkeleton``, at an arbitrary field, seed, challenge vector and coin vector.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticDataParts
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticLmIO
import Nock.NockVMROM.Thm54.TraceGen.GenTierABalance
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMemWeb
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.TraceGen.GenFormRGeneral

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.RowLayout
open Nock.Framework.Thm54

variable {F K : Type} [Field F] [Field K] [Algebra F K]

variable {lmb : K}

/-! ## Row counts of the carrier's compute tree

`genExactConfig` measures `compRows` off the rendered, BFS-assigned, AIR-ordered tree.  These two
rewrites turn that measurement into the BFS row count of `airReorder t`, which is the index every
generic per-row theorem is stated at. -/

/-- `bfsAssign` does not change the BFS length. -/
theorem bfsForest_bfsAssign_length (u : NTree (GenComputeRow K)) :
    (bfsForest [bfsAssign u]).length = (bfsForest [u]).length := by
  have h := congrArg List.length (bfsAssign_bfsForest_labels u)
  simpa using h

/-- The carrier's `compRows` is the BFS row count of the AIR-ordered generated tree. -/
theorem genComputeRows_bfsForest_length (z α : K) (t : NTree (GenComputeRow K)) :
    (bfsForest [genComputeRows z α t]).length = (bfsRows (airReorder t)).length := by
  rw [genComputeRows, renderRows_eq_mapNTree, bfsForest_mapNTree_singleton, List.length_map,
    bfsForest_bfsAssign_length, bfsRows_length]

/-! ## The carrier's compute rows, indexed -/

/-- The carrier's canonical indexed compute row is the coin-overwritten rendering of the BFS label
at the same position — the generic form of `DotConfig769.computeRowAt_eq_threaded`
(`GenTierASemantic.lean:634`) and `MatmulConfig65537.computeRowAt_eq`
(`GenMatmulMemAccept.lean:1168`). -/
theorem genExactExecution_computeRowAt
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K) (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
        hmempos hcomp hmem).compRows) :
    (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem).computeRowAt i =
      setRowCoins a b c (renderNode z α (bfsLabelAt (airReorder t) ((i : ℕ) + 1))).row := by
  set exec := genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
    hmempos hcomp hmem with hexec
  have hrows : exec.computeRows =
      (List.range' 1 (bfsForest [airReorder t]).length).map
        (fun j => setRowCoins a b c (renderNode z α (bfsLabelAt (airReorder t) j)).row) := by
    rw [hexec, genExactExecution_computeRows chal Ksz orbit horb a b c]
    rw [genComputeRows, bfsRows_renderRows]
    unfold bfsRows
    rw [bfsAssign_bfsForest_labels, List.map_map, List.map_map]
    rfl
  have hlt : (i : ℕ) < exec.computeRows.length := by
    have hlen := exec.computeRows_length
    have := i.isLt
    omega
  have hget : exec.computeRowAt i = exec.computeRows[(i : ℕ)]'hlt := by
    simp [ExactExecution.computeRowAt, List.get_eq_getElem]
  have hltR : (i : ℕ) <
      ((List.range' 1 (bfsForest [airReorder t]).length).map
        (fun j => setRowCoins a b c
          (renderNode z α (bfsLabelAt (airReorder t) j)).row)).length := by
    rw [← hrows]; exact hlt
  have hidx := congrArg (fun l : List _ => l[(i : ℕ)]?) hrows
  simp only [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hltR] at hidx
  rw [hget, Option.some.inj hidx]
  simp only [List.getElem_map]
  congr 1
  simp [List.getElem_range', Nat.add_comm]

/-- The carrier's canonical indexed compute **pub**: `setRowCoins` leaves `row.2.2` untouched. -/
theorem genExactExecution_computePubAt
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K) (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
        hmempos hcomp hmem).compRows) :
    (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem).computePubAt i =
      (renderNode z α (bfsLabelAt (airReorder t) ((i : ℕ) + 1))).row.2.2.1 := by
  rw [ExactExecution.computePubAt,
    genExactExecution_computeRowAt chal Ksz orbit horb z α a b c t mf hmempos hcomp hmem i]
  rfl

/-! ## `compute_chain` — the line-number handoff

`adjacent_ln_air` (`GenTierAAccept.lean:451`) and `MatmulConfig65537.adjacent_ln`
(`GenMatmulMemAccept.lean:1218`) are the same eight-line proof at two trees, and the only
configuration-specific step in either is the row-count equation supplying `hk`.  Here it is once,
over an arbitrary tree. -/

/-- Adjacent BFS-assigned rendered rows hand off the line accumulator, for **any** tree. -/
theorem genAdjacentLn (z α : K) (u : NTree (GenComputeRow K)) (k : ℕ)
    (hk : k + 1 < (bfsRows u).length) :
    (renderNode z α (bfsLabelAt u (k + 1))).row.2.2.1.ln =
      (renderNode z α (bfsLabelAt u (k + 2))).row.2.2.1.ln_prev := by
  have hk0 : (k + 1) - 1 < (bfsRows u).length := by omega
  have hk1 : (k + 2) - 1 < (bfsRows u).length := by omega
  have hkacc : k < (bfsRows u).length := by omega
  rw [(renderNode_ln z α _).1, (renderNode_ln z α _).2]
  rw [bfsLabelAt_lnExponent u (k + 1) hk0, bfsLabelAt_lnPrev u (k + 2) hk1]
  have hsucc := accAt_succ_of_lt u k hkacc
  have hskel := bfsLabelAt_skel u (k + 1) hk0
  have hk1' : k + 1 - 1 = k := Nat.add_sub_cancel k 1
  have hk2' : k + 2 - 1 = k + 1 := by omega
  simp [hk1', hk2', hskel, hsucc]

/-- **`chained`'s `compute_chain`, for any accepted program.** -/
theorem genComputeChain
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K) (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    ∀ i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
          hmempos hcomp hmem).compRows,
      ∀ _hi : (i : ℕ) + 1 < (genExactConfig (F := F) chal Ksz orbit horb
          (genComputeRows z α t) mf hmempos hcomp hmem).compRows,
      ((genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
          hmempos hcomp hmem).computePubAt i).ln =
        ((genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
          hmempos hcomp hmem).computePubAt ⟨(i : ℕ) + 1, _hi⟩).ln_prev := by
  intro i hi
  rw [genExactExecution_computePubAt chal Ksz orbit horb z α a b c t mf hmempos hcomp hmem,
    genExactExecution_computePubAt chal Ksz orbit horb z α a b c t mf hmempos hcomp hmem]
  refine genAdjacentLn z α (airReorder t) (i : ℕ) ?_
  have hcfg : (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
      hmempos hcomp hmem).compRows = (bfsRows (airReorder t)).length :=
    genComputeRows_bfsForest_length z α t
  omega


/-! ## The memory half, decoupled from the carrier

The memory fields of `chained` — `memory_wf`, `memory_chain`, `memory_first_*`,
`memory_last_icur` — depend on the execution only through the identity

  `exec.memoryRows.map (·.2.2) = threadPubs inp 0 ps`,

i.e. "the memory pubs are the LogUp-threaded pubs of some list".  Both live configurations prove
that identity for their own forest and then re-derive the same five consequences from it
(`DotConfig769.memoryPubAt_eq_thread`, `GenTierAMemAccept.lean:1131`, and its matmul twin).  The
consequences are stated once here over an arbitrary execution, and the row-count equation those
proofs spend their length on is *derived* from the identity rather than assumed. -/

section ThreadedPubs

variable {cfg : ExactConfig F K} (exec : ExactExecution cfg)
  (inp : MemoryTable.Inputs K) (ps : List (MemoryTable.Pub K))

/-- The threaded pub list has exactly `memRows` entries. -/
theorem threadPubs_length_eq_memRows
    (hp : exec.memoryRows.map
      (fun r : MemoryTable.MState × MemoryTable.DTmem K => r.2.2) = threadPubs inp 0 ps) :
    ps.length = cfg.memRows := by
  have h := congrArg List.length hp
  rw [List.length_map, threadPubs_length, exec.memoryRows_length] at h
  exact h.symm

/-- Reading the indexed memory pub off the threaded pub list. -/
theorem memoryPubAt_threadPubs
    (hp : exec.memoryRows.map
      (fun r : MemoryTable.MState × MemoryTable.DTmem K => r.2.2) = threadPubs inp 0 ps)
    (j : Fin cfg.memRows) (hj : (j : ℕ) < (threadPubs inp 0 ps).length) :
    exec.memoryPubAt j = (threadPubs inp 0 ps)[(j : ℕ)] := by
  have hlt : (j : ℕ) < exec.memoryRows.length := by
    rw [exec.memoryRows_length]; exact j.isLt
  have h1 : exec.memoryPubAt j = (exec.memoryRows[(j : ℕ)]'hlt).2.2 := by
    simp [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, List.get_eq_getElem]
  have hltM : (j : ℕ) < (exec.memoryRows.map
      (fun r : MemoryTable.MState × MemoryTable.DTmem K => r.2.2)).length := by
    simp
  have h2 := congrArg (fun l : List (MemoryTable.Pub K) => l[(j : ℕ)]?) hp
  simp only [List.getElem?_eq_getElem hltM, List.getElem?_eq_getElem hj] at h2
  have h3 := Option.some.inj h2
  rw [h1, ← h3]
  simp [List.getElem_map]

/-- **`memory_wf` from the threading identity.**  `threadPubs_WF` (`GenTierAMemAccept.lean:76`) is
already general over an arbitrary `Inputs`, accumulator and pub list. -/
theorem memoryWF_of_threadPubs
    (hp : exec.memoryRows.map
      (fun r : MemoryTable.MState × MemoryTable.DTmem K => r.2.2) = threadPubs inp 0 ps)
    (hch : cfg.challenges.memoryInputs = inp)
    (hwf : ∀ p ∈ ps, MemoryTable.WF inp p) :
    ∀ j, MemoryTable.WF cfg.challenges.memoryInputs (exec.memoryPubAt j) := by
  intro j
  have hlen := threadPubs_length_eq_memRows exec inp ps hp
  have hj : (j : ℕ) < (threadPubs inp 0 ps).length := by
    rw [threadPubs_length]
    have := j.isLt
    omega
  rw [hch, memoryPubAt_threadPubs exec inp ps hp j hj]
  exact threadPubs_WF inp 0 ps hwf _ (List.getElem_mem _)

/-- **`memory_chain` from the threading identity.** -/
theorem memoryChain_of_threadPubs
    (hp : exec.memoryRows.map
      (fun r : MemoryTable.MState × MemoryTable.DTmem K => r.2.2) = threadPubs inp 0 ps) :
    ∀ i : Fin cfg.memRows, ∀ hi : (i : ℕ) + 1 < cfg.memRows,
      (exec.memoryPubAt i).icur = (exec.memoryPubAt ⟨(i : ℕ) + 1, hi⟩).ipre := by
  intro i hi
  have hlen := threadPubs_length_eq_memRows exec inp ps hp
  have hlenT : (threadPubs inp 0 ps).length = cfg.memRows := by
    rw [threadPubs_length]; exact hlen
  have hj0 : (i : ℕ) < (threadPubs inp 0 ps).length := by omega
  have hj1 : ((⟨(i : ℕ) + 1, hi⟩ : Fin cfg.memRows) : ℕ) <
      (threadPubs inp 0 ps).length := by simp; omega
  rw [memoryPubAt_threadPubs exec inp ps hp i hj0,
    memoryPubAt_threadPubs exec inp ps hp ⟨(i : ℕ) + 1, hi⟩ hj1]
  have hbound : (i : ℕ) + 1 < (threadPubs inp 0 ps).length := by omega
  exact interChain_handoff inp 0 _ _ (threadPubs_interChain inp 0 ps) (i : ℕ) hbound

/-- **`memory_first_ipre` from the threading identity.** -/
theorem memoryFirstIpre_of_threadPubs
    (hp : exec.memoryRows.map
      (fun r : MemoryTable.MState × MemoryTable.DTmem K => r.2.2) = threadPubs inp 0 ps) :
    (exec.memoryPubAt ⟨0, cfg.memRows_pos⟩).ipre = 0 := by
  have hlen := threadPubs_length_eq_memRows exec inp ps hp
  have hlenT : (threadPubs inp 0 ps).length = cfg.memRows := by
    rw [threadPubs_length]; exact hlen
  have hpos : 0 < (threadPubs inp 0 ps).length := by
    have := cfg.memRows_pos; omega
  obtain ⟨p, qs, hth⟩ : ∃ p qs, threadPubs inp 0 ps = p :: qs := by
    cases hcase : threadPubs inp 0 ps with
    | nil => rw [hcase] at hpos; simp at hpos
    | cons p qs => exact ⟨p, qs, rfl⟩
  have hchain0 := threadPubs_interChain inp 0 ps
  rw [hth] at hchain0
  have hipre : p.ipre = 0 := interChain_head_ipre inp 0 _ p qs hchain0
  rw [memoryPubAt_threadPubs exec inp ps hp ⟨0, cfg.memRows_pos⟩ (by simpa using hpos)]
  have hlt0 : 0 < (p :: qs).length := by simp
  have hidx := congrArg (fun l : List (MemoryTable.Pub K) => l[0]?) hth
  simp only [List.getElem?_eq_getElem hpos, List.getElem?_eq_getElem hlt0] at hidx
  show ((threadPubs inp 0 ps)[(0 : ℕ)]).ipre = 0
  rw [Option.some.inj hidx]
  exact hipre

/-- **`memory_last_icur` from the threading identity plus a zero net delta.** -/
theorem memoryLastIcur_of_threadPubs
    (hp : exec.memoryRows.map
      (fun r : MemoryTable.MState × MemoryTable.DTmem K => r.2.2) = threadPubs inp 0 ps)
    (hdelta : MemoryTable.sumDelta inp ps = 0) :
    (exec.memoryPubAt (cfg.orbit.lastIndex cfg.memRows cfg.memRows_pos)).icur = 0 := by
  have hlen := threadPubs_length_eq_memRows exec inp ps hp
  have hlenT : (threadPubs inp 0 ps).length = cfg.memRows := by
    rw [threadPubs_length]; exact hlen
  have hpos : 0 < (threadPubs inp 0 ps).length := by
    have := cfg.memRows_pos; omega
  have hne : threadPubs inp 0 ps ≠ [] := List.ne_nil_of_length_pos hpos
  have hlastIdx : cfg.orbit.lastIndex cfg.memRows cfg.memRows_pos =
      ⟨cfg.memRows - 1, Nat.sub_lt cfg.memRows_pos (by omega)⟩ := rfl
  have hjlt : ((⟨cfg.memRows - 1, Nat.sub_lt cfg.memRows_pos (by omega)⟩ :
      Fin cfg.memRows) : ℕ) < (threadPubs inp 0 ps).length := by simp; omega
  rw [hlastIdx, memoryPubAt_threadPubs exec inp ps hp _ hjlt]
  have hgetLast :
      (threadPubs inp 0 ps)[cfg.memRows - 1]'hjlt = (threadPubs inp 0 ps).getLast hne := by
    have hidx' : cfg.memRows - 1 = (threadPubs inp 0 ps).length - 1 := by omega
    simp [List.getLast_eq_getElem, hidx']
  show ((threadPubs inp 0 ps)[cfg.memRows - 1]'hjlt).icur = 0
  rw [hgetLast, interChain_last_icur inp 0 _ _ hne (threadPubs_interChain inp 0 ps),
    zero_add, hdelta]

/-- **`memory_first_counts` / `memory_first_indicator` from the threading identity.**  `threadPub`
rewrites only the accumulator columns, so the first row's `pt` is the head of `ps`. -/
theorem memoryFirstPt_of_threadPubs
    (hp : exec.memoryRows.map
      (fun r : MemoryTable.MState × MemoryTable.DTmem K => r.2.2) = threadPubs inp 0 ps)
    (p : MemoryTable.Pub K) (qs : List (MemoryTable.Pub K)) (hps : ps = p :: qs) :
    (exec.memoryPubAt ⟨0, cfg.memRows_pos⟩).pt = p.pt := by
  have hlen := threadPubs_length_eq_memRows exec inp ps hp
  have hlenT : (threadPubs inp 0 ps).length = cfg.memRows := by
    rw [threadPubs_length]; exact hlen
  have hpos : 0 < (threadPubs inp 0 ps).length := by
    have := cfg.memRows_pos; omega
  rw [memoryPubAt_threadPubs exec inp ps hp ⟨0, cfg.memRows_pos⟩ (by simpa using hpos)]
  have hth : threadPubs inp 0 ps =
      (threadPub inp 0 p).2 :: threadPubs inp (threadPub inp 0 p).1 qs := by
    rw [hps, threadPubs_cons]
  have hlt0 : 0 < ((threadPub inp 0 p).2 ::
      threadPubs inp (threadPub inp 0 p).1 qs).length := by simp
  have hidx := congrArg (fun l : List (MemoryTable.Pub K) => l[0]?) hth
  simp only [List.getElem?_eq_getElem hpos, List.getElem?_eq_getElem hlt0] at hidx
  show ((threadPubs inp 0 ps)[(0 : ℕ)]).pt = p.pt
  rw [Option.some.inj hidx]
  simp [threadPub_pt]

end ThreadedPubs

/-! ## The carrier's threading identity

One lemma ties the generic memory section to `genExactExecution`.  The executed rows are the row
encode of the generated a-bearing rows (`genExactExecution = (genExactExecutionA …).encodeMem`), and
at the generator's `γ = 0` threading commutes with that encode (`threadPubs_map_encPub`), so the
executed pubs are the threaded pubs of the **encoded** generated pubs. -/

/-- At `γ = 0` the LogUp threading commutes with the row encode. -/
theorem threadPubs_map_encPub (inp : MemoryTable.Inputs K) (hγ : inp.γ = 0) :
    ∀ (acc : K) (ps : List (MemoryTable.Pub K)),
      threadPubs inp acc (ps.map (encPub lmb)) = (threadPubs inp acc ps).map (encPub lmb)
  | _, [] => rfl
  | acc, p :: ps => by
      simp only [List.map_cons, threadPubs_cons, threadPub_snd, threadPub_fst,
        interDelta_encPub p inp hγ, encPub_setAcc]
      rw [threadPubs_map_encPub inp hγ]

theorem sumDelta_map_encPub (inp : MemoryTable.Inputs K) (hγ : inp.γ = 0)
    (ps : List (MemoryTable.Pub K)) :
    MemoryTable.sumDelta inp (ps.map (encPub lmb)) = MemoryTable.sumDelta inp ps := by
  unfold MemoryTable.sumDelta
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun p _ => interDelta_encPub p inp hγ

/-- The encode keeps the indexed row's state and `pt`. -/
theorem encodeMem_memoryRowAt {cfg : ExactConfig F K} (E : ExactExecution cfg)
    (i : Fin cfg.memRows) :
    E.encodeMem.memoryRowAt i = MemoryRowTemplate.encodeRow cfg.challenges.lam (E.memoryRowAt i) := by
  simp only [ExactExecution.memoryRowAt, List.get_eq_getElem, Fin.val_cast]
  simp [ExactExecution.encodeMem_memoryRows]

theorem encodeMem_memoryPubAt_pt {cfg : ExactConfig F K} (E : ExactExecution cfg)
    (i : Fin cfg.memRows) :
    (E.encodeMem.memoryPubAt i).pt = (E.memoryPubAt i).pt := by
  simp only [ExactExecution.memoryPubAt, encodeMem_memoryRowAt]
  unfold MemoryRowTemplate.encodeRow
  split <;> rfl

/-- The a-bearing view's memory pubs are exactly the LogUp-threaded pubs of the generated forest. -/
theorem genExactExecutionA_memoryPubs
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K) (t : NTree (GenComputeRow K))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h) :
    ((genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).memoryRows).map
        (fun r : MemoryTable.MState × MemoryTable.DTmem K => r.2.2) =
      threadPubs (memInputs z) 0
        (((bfsForest (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))).map
          NTree.label).map (fun g : GenMemoryRow K => g.row.2.2)) := by
  rw [genExactExecutionA_memoryRows chal Ksz orbit horb a b c, List.map_map]
  show ((bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).map
      (fun n => n.label.row.2.2)) = _
  rw [show (fun n : NTree (GenMemoryRow K) => n.label.row.2.2) =
      (fun g : GenMemoryRow K => g.row.2.2) ∘ NTree.label from rfl, ← List.map_map]
  unfold genMemoryForest
  rw [threadGenForest_bfs_labels, threadGenRows_map_pub]

/-- **The carrier's executed memory pubs are the threaded pubs of the encoded generated pubs.** -/
theorem genExactExecution_memoryPubs
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h) :
    ((genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).memoryRows).map
        (fun r : MemoryTable.MState × MemoryTable.DTmem K => r.2.2) =
      threadPubs (memInputs z) 0
        ((((bfsForest (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))).map
          NTree.label).map (fun g : GenMemoryRow K => g.row.2.2)).map (encPub chal.lam)) := by
  rw [threadPubs_map_encPub (memInputs z) rfl,
    ← genExactExecutionA_memoryPubs (F := F) chal Ksz orbit horb z α a b c t hmempos hcomp hmem,
    genExactExecution, ExactExecution.encodeMem_memoryRows, List.map_map, List.map_map]
  refine List.map_congr_left fun r hr => ?_
  rw [genExactExecutionA_memoryRows] at hr
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hr
  exact encodeRow_pub _ (genThreadedMemory_state z α (memInputs z) h n hn)

/-! ## `memory_wf`

What the configurations supply per-fixture is `WF` on the *unthreaded* generated forest, from
`MemoryNodesOK`.  `genComputeSkeleton_memForest_OK_air` makes that generic too. -/

/-- `MemoryTable.WF` on the generated (unthreaded) memory forest of any accepted program. -/
theorem genAssignedMemory_WF (z α : K) (hz : z ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u ∈ bfsForest (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t))),
      MemoryTable.WF (memInputs z) u.label.row.2.2 := by
  intro u hu
  obtain ⟨w, hw, hin⟩ := (mem_bfsForest _ u).mp hu
  have hOK := genComputeSkeleton_memForest_OK_air z α h w hw
    (mapNTree GenMemoryRow.node u) (mapNTree_inTree _ hin)
  have hb := hOK.2.2.1
  have hsteq : u.label.skel.state = u.label.row.2.2.st := by
    simpa [mapNTree_label, GenMemoryRow.node_skel, GenMemoryRow.node_row] using
      hb.2.2.1.symm
  refine ⟨?_⟩
  intro hlive
  have hact : memoryMemRecKind u.label.skel.state = .active := by
    rw [hsteq]
    rcases hlive with hx | hx <;> simp [memoryMemRecKind, hx]
  have hrec : BindMemRec z (u.label.skel.memoryRecord (by
      simpa [mapNTree_label, GenMemoryRow.node_skel] using hact))
      u.label.row.2.2.mem := by
    have hx := hb.2.2.2.2.2
    simpa [mapNTree_label, GenMemoryRow.node_skel, GenMemoryRow.node_row, hact] using hx.1
  have hroot : u.label.row.2.2.mem.root =
      GlobalCarryRecognizer.enc z (u.label.skel.memoryRecord
        (by simpa [mapNTree_label, GenMemoryRow.node_skel] using hact)).root :=
    hrec.1
  rw [pole_memInputs z _ u.label.row.2.2.cprime, hroot, GlobalCarryRecognizer.enc_size]
  exact pow_ne_zero _ hz


/-! ## `compute_wf`

`ComputeTable.WF` has three fields and only `rlc5` reads the challenge coins, so **coin sensitivity
is confined to `.s5` rows**.  `renderNode_WF` (`GenWF.lean:165`) takes exactly that
one `rlc5Holds` obligation and discharges `size8`/`size11` from `z ≠ 0`.

So `compute_wf` is stated here with the coin obligation as an explicit, per-row **side condition**
`ComputeCoinsGeneric`, and two discharges are supplied:

* `computeCoinsGeneric_of_noOp5` — on a program with no `OP_5` row it holds at *every* coin vector,
  with no condition at all;
* `computeCoinsGeneric_c_one` — at the matmul convention `(a,b,c) = (0,0,1)` it follows from
  `op5C1Ready` at each `OP_5` row. -/

/-- The coin-genericity side condition of `WF` on one generated compute tree: the OP5 RLC form does
not vanish at the declared coins, at every BFS row.  Vacuous off `.s5`. -/
def ComputeCoinsGeneric (z α a b c : K) (u : NTree (GenComputeRow K)) : Prop :=
  ∀ i ∈ List.range' 1 (bfsForest [u]).length,
    TableWFBounds.rlc5Holds a b c (renderNode z α (bfsLabelAt u i)).row.2.2.1

/-- Every BFS label is the label of some node of the tree. -/
theorem bfsLabelAt_skel_inTree (u : NTree (GenComputeRow K)) (i : ℕ)
    (hi : i ∈ List.range' 1 (bfsForest [u]).length) :
    ∃ v, InTree u v ∧ (bfsLabelAt u i).skel = v.label.skel := by
  have hi' := lt_bfsRows_of_mem_range' hi
  have hlenF : i - 1 < (bfsForest [u]).length := by rwa [← bfsRows_length]
  refine ⟨(bfsForest [u])[i - 1], ?_, ?_⟩
  · have hmem : (bfsForest [u])[i - 1] ∈ bfsForest [u] := List.getElem_mem hlenF
    obtain ⟨w, hw, hin⟩ := (mem_bfsForest [u] _).mp hmem
    simp only [List.mem_singleton] at hw
    subst w
    exact hin
  · rw [bfsLabelAt_skel u i hi']
    simp [bfsRows]

/-- On a program with no `OP_5` row the coin condition is unconditional. -/
theorem computeCoinsGeneric_of_noOp5 (z α a b c : K) (u : NTree (GenComputeRow K))
    (h5 : ∀ v, InTree u v → v.label.skel.state ≠ ComputeTable.State.s5) :
    ComputeCoinsGeneric z α a b c u := by
  intro i hi
  obtain ⟨v, hv, hskel⟩ := bfsLabelAt_skel_inTree u i hi
  exact renderNode_rlc5Holds_of_ne_s5 z α a b c _ (by rw [hskel]; exact h5 v hv)

/-- At coins `(0,0,1)`, `op5C1Ready` at every `OP_5` row discharges the coin condition. -/
theorem computeCoinsGeneric_c_one (z α : K) (u : NTree (GenComputeRow K))
    (h5 : ∀ v, InTree u v → v.label.skel.state = ComputeTable.State.s5 →
      op5C1Ready v.label.skel) :
    ComputeCoinsGeneric z α 0 0 1 u := by
  intro i hi
  obtain ⟨v, hv, hskel⟩ := bfsLabelAt_skel_inTree u i hi
  refine renderNode_rlc5Holds_c_one z α _ ?_
  intro hs5
  rw [hskel] at hs5 ⊢
  simpa [op5C1Ready] using h5 v hv hs5

/-- **`chained`'s `compute_wf`, for any accepted program**, under the coin side condition. -/
theorem genComputeWF (z α : K) (hz : z ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (t : NTree (GenComputeRow K))
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    ∀ i, ComputeTable.WF
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
        hmempos hcomp hmem).challenges.computeInputs
      ((genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem).computePubAt i) := by
  intro i
  have hch : (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
      hmempos hcomp hmem).challenges.computeInputs = challengeInputs z α a b c := by
    show chal.computeInputs = _
    rw [hinp]; rfl
  rw [hch, genExactExecution_computePubAt chal Ksz orbit horb z α a b c t mf
    hmempos hcomp hmem i]
  refine renderNode_WF z α a b c _ hz (hcoins ((i : ℕ) + 1) ?_)
  have hcfg : (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
      hmempos hcomp hmem).compRows = (bfsRows (airReorder t)).length :=
    genComputeRows_bfsForest_length z α t
  have hlt : (i : ℕ) < (bfsForest [airReorder t]).length := by
    have h1 := i.isLt
    have h2 : (bfsRows (airReorder t)).length = (bfsForest [airReorder t]).length :=
      bfsRows_length _
    omega
  exact List.mem_range'.mpr ⟨(i : ℕ), hlt, by omega⟩



/-! ## Axis arithmetic for the annotated descent

Both configurations get it from `genAnnotatedRecordTree_root_counts` (`GenTierAMemAccept.lean:189`),
which is stated only at `axis ∈ {2,3}` and only on a cell — enough for a fixture whose head record is
the formula-open `@3`, not enough for an arbitrary program, whose `OP_0`/`OP_9` records carry the
axis of a Nock slot read.

Each decompose multiplies the
indicator by `λ`; on the tail (top-bit) path it adds `λ^m·P` to counts and on the head path
`(λ − 1)·λ^{m−1}·P`.  So the descent from a continuation cell `(P, Q)` at residual axis `a ≥ 1`
satisfies

  `indicator = λ^{log₂ a} · P`  and  `counts = Q + (axisPoly λ a − 1) · P`

(`GenFormRGeneral.axisPoly`: the binary digits of `a` read in base `λ`).  The read on top cancels it to
`0` — for **every** axis `1 ≤ a < ringChar K` and every `λ`.  At `λ = 2`, `axisPoly 2 a = a`
(`axisPoly_two`) and this is the old `MemoryTable.formRRead_two` closed form.
The arithmetic below is what makes the induction go through. -/

/-- Two-sided bound on the residual axis: it has exactly one bit fewer. -/
theorem axisRest_bounds {a : ℕ} (h : 2 ≤ a) :
    2 ^ (a.log2 - 1) ≤ axisRest a ∧ axisRest a < 2 ^ a.log2 := by
  have hk : 1 ≤ a.log2 := log2_ge_one h
  have hlo : 2 ^ a.log2 ≤ a := two_pow_log2_le a (by omega)
  have hhi : a < 2 ^ (a.log2 + 1) := Nat.lt_log2_self
  have hpow : 2 ^ a.log2 = 2 * 2 ^ (a.log2 - 1) := two_mul_pow_pred hk
  have hpow2 : 2 ^ (a.log2 + 1) = 2 * 2 ^ a.log2 := by rw [pow_succ]; ring
  rw [axisRest_eq]
  split_ifs with hb
  · have h' := axisTopBit_iff.mp hb
    omega
  · have h' : ¬ (3 * 2 ^ (a.log2 - 1) ≤ a) := (not_congr axisTopBit_iff).mp hb
    omega

theorem log2_axisRest {a : ℕ} (h : 2 ≤ a) : (axisRest a).log2 = a.log2 - 1 := by
  have hk : 1 ≤ a.log2 := log2_ge_one h
  obtain ⟨h1, h2⟩ := axisRest_bounds h
  rw [Nat.log2_eq_log_two]
  refine Nat.log_eq_of_pow_le_of_lt_pow h1 ?_
  rw [show a.log2 - 1 + 1 = a.log2 from by omega]
  exact h2

theorem axisRest_add_topBit {a : ℕ} (h : 2 ≤ a) (hb : axisTopBit a = true) :
    axisRest a + 2 ^ a.log2 = a := by
  have hlo : 2 ^ a.log2 ≤ a := two_pow_log2_le a (by omega)
  rw [axisRest_eq, if_pos hb]
  omega

theorem axisRest_add_not_topBit {a : ℕ} (h : 2 ≤ a) (hb : axisTopBit a = false) :
    axisRest a + 2 ^ (a.log2 - 1) = a := by
  have hk : 1 ≤ a.log2 := log2_ge_one h
  have hlo : 2 ^ a.log2 ≤ a := two_pow_log2_le a (by omega)
  have hpow : 2 ^ a.log2 = 2 * 2 ^ (a.log2 - 1) := two_mul_pow_pred hk
  rw [axisRest_eq, if_neg (by simp [hb])]
  omega


/-! ## The closed form of the annotated descent, at every `λ` -/

/-- `axisRest` as raw arithmetic on the tail path. -/
theorem axisRest_eq_of_top {a : ℕ} (hb : axisTopBit a = true) :
    axisRest a = a - 2 ^ a.log2 := by
  rw [axisRest_eq, if_pos hb]

/-- `axisRest` as raw arithmetic on the head path. -/
theorem axisRest_eq_of_not_top {a : ℕ} (hb : axisTopBit a = false) :
    axisRest a = a - 2 ^ (a.log2 - 1) := by
  rw [axisRest_eq, if_neg (by simp [hb])]

/-- One descent step changes `axisPoly` by `λ^m` (tail) — `GenFormRGeneral.axisPoly_rest_top`
read through `axisRest`. -/
theorem axisPoly_axisRest_top (lmb : K) {a : ℕ} (h2 : 2 ≤ a) (hb : axisTopBit a = true) :
    axisPoly lmb a = axisPoly lmb (axisRest a) + lmb ^ a.log2 := by
  rw [axisRest_eq_of_top hb]
  exact axisPoly_rest_top lmb h2 (axisTopBit_iff.mp hb)

/-- One descent step changes `axisPoly` by `(λ − 1)·λ^{m−1}` (head). -/
theorem axisPoly_axisRest_not_top (lmb : K) {a : ℕ} (h2 : 2 ≤ a) (hb : axisTopBit a = false) :
    axisPoly lmb a = axisPoly lmb (axisRest a) + (lmb - 1) * lmb ^ (a.log2 - 1) := by
  rw [axisRest_eq_of_not_top hb]
  exact axisPoly_rest_not_top lmb h2 ((not_congr axisTopBit_iff).mp (by simp [hb]))

/-- **The descent closed form at every `λ`.**  From a continuation cell `(P, Q)` at residual
axis `a ≥ 1`: `indicator = λ^{log₂ a}·P`, `counts = Q + (axisPoly λ a − 1)·P`.  At `λ = 2`,
`axisPoly 2 a = a` (`axisPoly_two`) recovers the old `counts = Q + (a − 1)·P`. -/
theorem genAnnotatedDescentCont_cell (E : Noun → ComputeTable.FP K) (z lmb : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) :
    ∀ (a : ℕ), 1 ≤ a → ∀ (cur : Noun),
      (genAnnotatedDescentCont E z lmb cont contCell contState cur a).2.indicator =
          lmb ^ a.log2 * contCell.indicator ∧
        (genAnnotatedDescentCont E z lmb cont contCell contState cur a).2.counts =
          contCell.counts + (axisPoly lmb a - 1) * contCell.indicator := by
  intro a
  induction a using Nat.strongRecOn with
  | _ n ih =>
    intro hn cur
    by_cases h2 : n < 2
    · have hn1 : n = 1 := by omega
      subst hn1
      unfold genAnnotatedDescentCont
      rw [if_pos (by omega)]
      simp [show Nat.log2 1 = 0 by decide]
    · have h2' : 2 ≤ n := by omega
      have hk : 1 ≤ n.log2 := log2_ge_one h2'
      have hd1 : 1 ≤ axisRest n := axisRest_pos h2'
      have hlog := log2_axisRest h2'
      have hpow : lmb ^ n.log2 = lmb * lmb ^ (n.log2 - 1) := by
        rw [← pow_succ']; congr 1; omega
      unfold genAnnotatedDescentCont
      rw [if_neg h2]
      by_cases hb : axisTopBit n = true
      · rw [if_pos hb]
        obtain ⟨hi, hc⟩ := ih (axisRest n) (axisRest_lt h2') hd1 (formulaTail cur)
        have hpoly := axisPoly_axisRest_top lmb h2' hb
        simp only [annotatedDecPub]
        rw [genAnnotatedNounWalk_counts_zero, genAnnotatedNounWalk_indicator, hi, hc, hlog]
        constructor
        · rw [hpow]; ring
        · rw [hpoly, hpow]; ring
      · have hb' : axisTopBit n = false := by simpa using hb
        rw [if_neg (by simp [hb'])]
        obtain ⟨hi, hc⟩ := ih (axisRest n) (axisRest_lt h2') hd1 (formulaHead cur)
        have hpoly := axisPoly_axisRest_not_top lmb h2' hb'
        simp only [annotatedDecPub]
        rw [genAnnotatedNounWalk_counts_zero, genAnnotatedNounWalk_indicator, hi, hc, hlog]
        constructor
        · rw [hpow]; ring
        · rw [hpoly]; ring

/-! ## The head record's `pt` cell is zero, at any axis and any `λ` -/

/-- The plain descent is the continuation descent whose continuation is the terminal verify
subtree.  Only the `pt` cell is compared, which is all the endpoint fields read. -/
theorem genAnnotatedDescent_cell_eq_cont (E : Noun → ComputeTable.FP K) (z lmb : K)
    (root child : Noun) (recAxis : ℕ) (ts : K) (recordExp : ℕ)
    (cont : List (NTree (GenMemoryRow K))) (contState : MemoryTable.MState) :
    ∀ (a : ℕ) (cur : Noun),
      (genAnnotatedDescent E z lmb root child recAxis ts recordExp cur a).2 =
        (genAnnotatedDescentCont E z lmb cont
          (genAnnotatedVerify E z lmb root child recAxis ts recordExp).2 contState cur a).2 := by
  intro a
  induction a using Nat.strongRecOn with
  | _ n ih =>
    intro cur
    unfold genAnnotatedDescent genAnnotatedDescentCont
    split
    · rfl
    · rename_i hlt
      split
      · simp only [annotatedDecPub]
        rw [ih (axisRest n) (axisRest_lt (by omega)) (formulaTail cur)]
      · simp only [annotatedDecPub]
        rw [ih (axisRest n) (axisRest_lt (by omega)) (formulaHead cur)]

/-- The verify cell that seeds a record's own descent: `(L, L)`, `L = λ^{n−1}·ts`. -/
theorem genAnnotatedVerify_cell (E : Noun → ComputeTable.FP K) (z lmb : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    (genAnnotatedVerify E z lmb root child ax ts recordExp).2.indicator =
        lmb ^ MemoryTable.pwScaleExp K * ts ∧
      (genAnnotatedVerify E z lmb root child ax ts recordExp).2.counts =
        lmb ^ MemoryTable.pwScaleExp K * ts := by
  constructor
  · simp [genAnnotatedVerify, annotatedVerifyPub, genAnnotatedNounWalk_indicator]
  · simp [genAnnotatedVerify, annotatedVerifyPub, genAnnotatedNounWalk_counts_zero]

/-- **ROOTZERO at the read, every `λ`**: the Form R read on top of a descent cell
`(λ^m·L, axisPoly λ a·L)` lands on `(0, 0)` (`formRRead_general`, `T·C' = λ^{n−1}·axisPoly λ a`;
no hypothesis on `λ`). -/
theorem annotatedReadPub_pt_zero (E : Noun → ComputeTable.FP K) (root child : Noun) (lmb : K)
    {axis : ℕ} (hp : axis < ringChar K) (ts : K) (lc : MemoryTable.Cell K)
    (hi : lc.indicator = lmb ^ axis.log2 * (lmb ^ MemoryTable.pwScaleExp K * ts))
    (hc : lc.counts = axisPoly lmb axis * (lmb ^ MemoryTable.pwScaleExp K * ts))
    (ipre icur : K) :
    (annotatedReadPub E root child axis ts lc ipre icur lmb).pt.indicator = 0 ∧
      (annotatedReadPub E root child axis ts lc ipre icur lmb).pt.counts = 0 := by
  obtain ⟨hpw, hcnt⟩ := formRRead_general (K := K) lmb
    ⟨E root, E child, (axis : K), ts⟩ rfl hp
  simp only [annotatedReadPub]
  rw [hpw, hcnt, hi, hc]
  constructor <;> ring

/-- **The descent from a record's own verify cell lands on `(λ^m·L, axisPoly λ a·L)`.** -/
theorem genAnnotatedDescent_root_cell
    (E : Noun → ComputeTable.FP K) (z lmb : K)
    (root child : Noun) (axis : ℕ) (haxis : 1 ≤ axis) (ts : K) (recordExp : ℕ) :
    (genAnnotatedDescent E z lmb root child axis ts recordExp root axis).2.indicator =
        lmb ^ axis.log2 * (lmb ^ MemoryTable.pwScaleExp K * ts) ∧
      (genAnnotatedDescent E z lmb root child axis ts recordExp root axis).2.counts =
        axisPoly lmb axis * (lmb ^ MemoryTable.pwScaleExp K * ts) := by
  obtain ⟨hCi, hCc⟩ := genAnnotatedVerify_cell E z lmb root child axis ts recordExp
  rw [genAnnotatedDescent_cell_eq_cont E z lmb root child axis ts recordExp
    [(genAnnotatedVerify E z lmb root child axis ts recordExp).1]
    MemoryTable.MState.verify_child axis root]
  obtain ⟨hi, hc⟩ := genAnnotatedDescentCont_cell E z lmb
    [(genAnnotatedVerify E z lmb root child axis ts recordExp).1]
    (genAnnotatedVerify E z lmb root child axis ts recordExp).2
    MemoryTable.MState.verify_child axis haxis root
  rw [hCi] at hi
  rw [hCi, hCc] at hc
  exact ⟨hi, by rw [hc]; ring⟩

/-- **`genAnnotatedRecordTree`'s root `pt` is zero**, for every axis `1 ≤ a < ringChar K` and
every `λ`: the Form R read weight is exactly the descent's root cell -/
theorem genAnnotatedRecordTree_root_pt
    (E : Noun → ComputeTable.FP K) (z α lmb : K)
    (root child : Noun) (axis : ℕ) (haxis : 1 ≤ axis) (hp : axis < ringChar K)
    (recordExp : ℕ) :
    (genAnnotatedRecordTree E z α lmb root child axis recordExp).label.row.2.2.pt.indicator = 0 ∧
      (genAnnotatedRecordTree E z α lmb root child axis recordExp).label.row.2.2.pt.counts = 0 := by
  obtain ⟨hi, hc⟩ := genAnnotatedDescent_root_cell E z lmb root child axis haxis
    (α ^ recordExp) recordExp
  exact annotatedReadPub_pt_zero E root child lmb hp (α ^ recordExp) _ hi hc 0 0

def chainOneBitWeight (α : K) (reqs : List MemRecordReq) : K :=
  (reqs.map fun r => α ^ r.recordExp * (axisOneBits r.axis : K)).sum

/-- **The chained inner continuation** carries the predecessor's own verify cell `(L, L)`:
every inner read cancels the descent it sits on, at every `λ`. -/
theorem genAnnotatedChainedInner_cell
    (E : Noun → ComputeTable.FP K) (z α lmb : K) :
    ∀ (rest : List MemRecordReq), (∀ r ∈ rest, 1 ≤ r.axis ∧ r.axis < ringChar K) →
      ∀ prev : MemRecordReq,
        (genAnnotatedChainedInner E z α lmb prev rest).2.indicator =
            lmb ^ MemoryTable.pwScaleExp K * α ^ prev.recordExp ∧
          (genAnnotatedChainedInner E z α lmb prev rest).2.counts =
            lmb ^ MemoryTable.pwScaleExp K * α ^ prev.recordExp := by
  intro rest
  induction rest with
  | nil =>
      intro _ prev
      simpa [genAnnotatedChainedInner] using
        genAnnotatedVerify_cell E z lmb prev.root prev.child prev.axis (α ^ prev.recordExp)
          prev.recordExp
  | cons r more ih =>
      intro hax prev
      obtain ⟨hr1, hrp⟩ := hax r (List.mem_cons_self ..)
      obtain ⟨hii, hic⟩ := ih (fun s hs => hax s (List.mem_cons_of_mem _ hs)) r
      obtain ⟨hdi, hdc⟩ := genAnnotatedDescentCont_cell E z lmb
        (genAnnotatedChainedInner E z α lmb r more).1
        (genAnnotatedChainedInner E z α lmb r more).2
        (chainedInnerRootState more) r.axis hr1 r.root
      rw [hii] at hdi
      rw [hii, hic] at hdc
      obtain ⟨hpw, hcnt⟩ := formRRead_general (K := K) lmb
        ⟨E r.root, E r.child, (r.axis : K), α ^ r.recordExp⟩ rfl hrp
      simp only [genAnnotatedChainedInner, annotatedReadPub, annotatedVerifyPub]
      rw [hpw, hcnt, hdi, hdc]
      constructor <;> ring

/-- **The chained tree's root `pt` is zero**, at every `λ`. -/
theorem genAnnotatedChainedTree_root_pt
    (E : Noun → ComputeTable.FP K) (z α lmb : K) (reqs : List MemRecordReq)
    (hax : ∀ r ∈ reqs, 1 ≤ r.axis ∧ r.axis < ringChar K) (tr : NTree (GenMemoryRow K))
    (h : genAnnotatedChainedTree E z α lmb reqs = some tr) :
    tr.label.row.2.2.pt.indicator = 0 ∧ tr.label.row.2.2.pt.counts = 0 := by
  match reqs with
  | [] => simp [genAnnotatedChainedTree] at h
  | [r] =>
      obtain ⟨hr1, hrp⟩ := hax r (by simp)
      simp only [genAnnotatedChainedTree, Option.some.injEq] at h
      subst h
      exact genAnnotatedRecordTree_root_pt E z α lmb r.root r.child r.axis hr1 hrp r.recordExp
  | r :: r2 :: rest =>
      obtain ⟨hr1, hrp⟩ := hax r (by simp)
      have hax' : ∀ s ∈ r2 :: rest, 1 ≤ s.axis ∧ s.axis < ringChar K :=
        fun s hs => hax s (List.mem_cons_of_mem _ hs)
      obtain ⟨hii, hic⟩ := genAnnotatedChainedInner_cell E z α lmb (r2 :: rest) hax' r
      obtain ⟨hdi, hdc⟩ := genAnnotatedDescentCont_cell E z lmb
        (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).1
        (genAnnotatedChainedInner E z α lmb r (r2 :: rest)).2
        (chainedInnerRootState (r2 :: rest)) r.axis hr1 r.root
      rw [hii] at hdi
      rw [hii, hic] at hdc
      simp only [genAnnotatedChainedTree, Option.some.injEq] at h
      subst h
      exact annotatedReadPub_pt_zero E r.root r.child lmb hrp (α ^ r.recordExp) _
        hdi (by rw [hdc]; ring) 0 0

/-! ## From the record trees to the head of the served forest -/

/-- Every branch of the row-level builder puts a record tree or a chained tree at the head.
    Live leftover `T = mem.axis` is the head `pt` (not `0`). -/
theorem genRowMemForest_head_pt (htwo : (2 : K) ≠ 0)
    (E : Noun → ComputeTable.FP K) (z α : K) (reqs : List MemRecordReq)
    (hne : reqs ≠ []) (hax : ∀ r ∈ reqs, 1 ≤ r.axis) :
    ∃ tr rest, genRowMemForest E z α lmb reqs = tr :: rest := by
  cases reqs with
  | nil => exact absurd rfl hne
  | cons r1 tl1 =>
    cases tl1 with
    | nil => exact ⟨_, [], rfl⟩
    | cons r2 tl2 =>
      cases tl2 with
      | nil =>
        show ∃ tr rest, (if r1.child = r2.root then
            match genAnnotatedChainedTree E z α lmb [r1, r2] with
            | some t => [t]
            | none => [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
                       genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]
          else [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
                genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]) =
          tr :: rest
        split_ifs with hch
        · cases hc : genAnnotatedChainedTree E z α lmb [r1, r2] with
          | none => exact ⟨_, _, rfl⟩
          | some tCh => exact ⟨tCh, [], rfl⟩
        · exact ⟨_, _, rfl⟩
      | cons r3 tl3 =>
        cases tl3 with
        | nil =>
          show ∃ tr rest, ((if r1.child = r2.root then
              match genAnnotatedChainedTree E z α lmb [r1, r2] with
              | some t => [t]
              | none => [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
                         genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]
            else [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
                  genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]) ++
            [genAnnotatedRecordTree E z α lmb r3.root r3.child r3.axis r3.recordExp]) =
            tr :: rest
          split_ifs with hch
          · cases hc : genAnnotatedChainedTree E z α lmb [r1, r2] with
            | none => exact ⟨_, _, rfl⟩
            | some tCh => exact ⟨tCh, _, rfl⟩
          · exact ⟨_, _, rfl⟩
        | cons r4 tl4 => exact ⟨_, _, rfl⟩

/-- Every root tree the row-level builder emits is a single-record tree or a chained tree over
    records of `reqs`. -/
theorem genRowMemForest_cases (E : Noun → ComputeTable.FP K) (z α : K)
    (reqs : List MemRecordReq) :
    ∀ t ∈ genRowMemForest E z α lmb reqs,
      (∃ r ∈ reqs, t = genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) ∨
        (∃ sub : List MemRecordReq, (∀ r ∈ sub, r ∈ reqs) ∧
          genAnnotatedChainedTree E z α lmb sub = some t) := by
  intro t ht
  have hpair : ∀ r1 r2 : MemRecordReq, ∀ ext : List MemRecordReq,
      r1 ∈ ext → r2 ∈ ext →
      t ∈ (if r1.child = r2.root then
            match genAnnotatedChainedTree E z α lmb [r1, r2] with
            | some t => [t]
            | none => [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
                       genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]
          else [genAnnotatedRecordTree E z α lmb r1.root r1.child r1.axis r1.recordExp,
                genAnnotatedRecordTree E z α lmb r2.root r2.child r2.axis r2.recordExp]) →
      (∃ r ∈ ext, t = genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) ∨
        (∃ sub : List MemRecordReq, (∀ r ∈ sub, r ∈ ext) ∧
          genAnnotatedChainedTree E z α lmb sub = some t) := by
    intro r1 r2 ext h1 h2 hm
    split_ifs at hm
    · cases hc : genAnnotatedChainedTree E z α lmb [r1, r2] with
      | some tc =>
          rw [hc] at hm
          simp only [List.mem_singleton] at hm
          subst hm
          exact Or.inr ⟨[r1, r2], by simp [h1, h2], hc⟩
      | none =>
          rw [hc] at hm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with rfl | rfl
          · exact Or.inl ⟨r1, h1, rfl⟩
          · exact Or.inl ⟨r2, h2, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact Or.inl ⟨r1, h1, rfl⟩
      · exact Or.inl ⟨r2, h2, rfl⟩
  match reqs, ht with
  | [], ht => simp [genRowMemForest] at ht
  | [r], ht =>
      simp only [genRowMemForest, List.mem_singleton] at ht
      exact Or.inl ⟨r, by simp, ht⟩
  | [r1, r2], ht =>
      exact hpair r1 r2 _ (by simp) (by simp) ht
  | [r1, r2, r3], ht =>
      simp only [genRowMemForest, List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · exact hpair r1 r2 _ (by simp) (by simp) ht
      · exact Or.inl ⟨r3, by simp, rfl⟩
  | r1 :: r2 :: r3 :: r4 :: rs, ht =>
      simp only [genRowMemForest, List.mem_map] at ht
      obtain ⟨r, hr, rfl⟩ := ht
      exact Or.inl ⟨r, hr, rfl⟩

/-- **Every root of the row-level builder has `pt = (0, 0)`** under Form R at `λ = 2`, for
    records with `1 ≤ axis < ringChar K` -/
theorem genRowMemForest_all_root_pt
    (E : Noun → ComputeTable.FP K) (z α : K) (reqs : List MemRecordReq)
    (hax : ∀ r ∈ reqs, 1 ≤ r.axis ∧ r.axis < ringChar K) :
    ∀ t ∈ genRowMemForest E z α lmb reqs,
      t.label.row.2.2.pt.indicator = 0 ∧ t.label.row.2.2.pt.counts = 0 := by
  intro t ht
  rcases genRowMemForest_cases (lmb := lmb) E z α reqs t ht with ⟨r, hr, rfl⟩ | ⟨sub, hsub, hc⟩
  · exact genAnnotatedRecordTree_root_pt E z α lmb r.root r.child r.axis (hax r hr).1
      (hax r hr).2 r.recordExp
  · exact genAnnotatedChainedTree_root_pt E z α lmb sub (fun r h => hax r (hsub r h)) t hc

/-- Every in-tree node has axis-positive extracted records. -/
def computeTreeAxes (u : NTree (GenComputeRow K)) : Prop :=
  ∀ n, InTree u n → ∀ r ∈ extractNodeReqs n.label, 1 ≤ r.axis

/-- Every in-tree node's extracted records lie in the certificate window `1 ≤ a < ringChar K`. -/
def computeTreeAxesLt (u : NTree (GenComputeRow K)) : Prop :=
  ∀ n, InTree u n → ∀ r ∈ extractNodeReqs n.label, 1 ≤ r.axis ∧ r.axis < ringChar K

mutual
/-- **Every root of the served forest has `pt = (0, 0)`.** -/
theorem genMemForestFromTree_all_root_pt
    (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ u : NTree (GenComputeRow K), computeTreeAxesLt (K := K) u →
      ∀ t ∈ genMemForestFromTree E z α lmb u,
        t.label.row.2.2.pt.indicator = 0 ∧ t.label.row.2.2.pt.counts = 0
  | .node g cs => by
      intro hax t ht
      simp only [genMemForestFromTree, List.mem_append] at ht
      rcases ht with ht | ht
      · exact genRowMemForest_all_root_pt E z α _ (hax _ (InTree.here _)) t ht
      · exact genMemForestFromList_all_root_pt E z α cs
          (fun c hc n hn => hax n (InTree.sub hc hn)) t ht

theorem genMemForestFromList_all_root_pt
    (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ cs : List (NTree (GenComputeRow K)),
      (∀ c ∈ cs, computeTreeAxesLt (K := K) c) →
      ∀ t ∈ genMemForestFromList E z α lmb cs,
        t.label.row.2.2.pt.indicator = 0 ∧ t.label.row.2.2.pt.counts = 0
  | [] => by
      intro _ t ht
      simp [genMemForestFromList] at ht
  | c :: rest => by
      intro hax t ht
      simp only [genMemForestFromList, List.mem_append] at ht
      rcases ht with ht | ht
      · exact genMemForestFromTree_all_root_pt E z α c (hax c List.mem_cons_self) t ht
      · exact genMemForestFromList_all_root_pt E z α rest
          (fun d hd => hax d (List.mem_cons_of_mem _ hd)) t ht
end

/-- **`genMemForestFromTree`'s head exists** — live leftover `T = mem.axis`, not `0`. -/
theorem genMemForestFromTree_head_pt (htwo : (2 : K) ≠ 0)
    (E : Noun → ComputeTable.FP K) (z α : K) (u : NTree (GenComputeRow K))
    (hne : u.label.requests ≠ [])
    (hax : ∀ r ∈ extractNodeReqs u.label, 1 ≤ r.axis) :
    ∃ tr rest, genMemForestFromTree E z α lmb u = tr :: rest := by
  have hlen : (extractNodeReqs u.label).length = u.label.requests.length := by
    rw [extractNodeReqs, extractNodeReqsAux_length]
  have hne' : extractNodeReqs u.label ≠ [] := by
    intro hc
    rw [hc] at hlen
    simp at hlen
    exact hne (List.eq_nil_of_length_eq_zero hlen.symm)
  obtain ⟨tr, rest, heq⟩ := genRowMemForest_head_pt (lmb := lmb) htwo E z α _ hne' hax
  refine ⟨tr, rest ++ genMemForestFromList E z α lmb u.children, ?_⟩
  cases u with
  | node g cs =>
      show genRowMemForest E z α lmb (extractNodeReqs g) ++ genMemForestFromList E z α lmb cs = _
      rw [show (NTree.node g cs).label = g from rfl] at heq
      rw [heq]
      rfl

/-- The head of a BFS forest is the head of its root list. -/
theorem bfsForest_head (l : List (NTree (GenMemoryRow K))) (tr : NTree (GenMemoryRow K))
    (rest : List (NTree (GenMemoryRow K))) (h : l = tr :: rest) :
    ∃ qs, bfsForest l = tr :: qs := by
  refine ⟨rest ++ bfsForest (l.flatMap NTree.children), ?_⟩
  rw [bfsForest_cons_eq l (by rw [h]; exact List.cons_ne_nil _ _), h]
  rfl



/-! ## The root row's requests

The head of the served forest is built from the **root compute row's** service requests, so
`memory_first_counts` needs two facts about them: that there is at least one, and that every axis is
`≥ 1`.  Both are read straight off `genComputeSkeleton`'s dispatch, with no recursion: every arm
emits the formula-open record `⟨formula, tail, 3⟩` first, and the only axes it does not fix are the
`OP_0` slot read and the `OP_9` arm fetch, whose arms fire only when `Noun.slot ax _` succeeds —
which rules out `ax = 0` (`Reference.lean:45`).

`axis = 0` is exactly the case the closed form excludes, and it is exactly the case the generator
cannot emit.  `RequestWF` alone does **not** give this: its `axis < 2` disjunct admits `0`.

That disjunct is gone: `RequestWF`'s second conjunct is now the
unconditional `Noun.slot req.axis req.root = some req.child`, because the `OP_0`/`OP_9` arms of its
induction already had `hslot` in context and three `by_cases` sites were discarding it. It is kept because `memory_first_counts` consumes exactly the
root-row form; nothing here is wrong, only no longer minimal. -/

/-- **The root compute row commits at least one record, and every axis it reads is `≥ 1`.** -/
theorem genComputeSkeleton_root_requests
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    t.label.requests ≠ [] ∧ ∀ r : ServiceReq K, r ∈ t.label.requests → 1 ≤ r.axis := by
  cases fuel with
  | zero => simp [genComputeSkeleton] at h
  | succ n =>
    cases formula with
    | atom _ => simp [genComputeSkeleton] at h
    | cell fh ftail =>
      cases fh with
      | cell lh lt =>
          cases hL : genComputeSkeleton (K := K) n subject (.cell lh lt) with
          | error e => simp [genComputeSkeleton, hL] at h
          | ok pl =>
            cases hR : genComputeSkeleton (K := K) n subject ftail with
            | error e => simp [genComputeSkeleton, hL, hR] at h
            | ok pr =>
              obtain ⟨lTree, lRes⟩ := pl
              obtain ⟨rTree, rRes⟩ := pr
              simp only [genComputeSkeleton, hL, hR, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨ht, _⟩ := h
              subst ht
              refine ⟨by simp [skelNode, NTree.label], ?_⟩
              intro r hr
              simp only [skelNode, NTree.label, List.mem_cons, List.not_mem_nil,
                or_false] at hr
              subst hr
              simp
      | atom op =>
          match op with
          | 0 =>
            cases ftail with
            | cell _ _ => simp [genComputeSkeleton] at h
            | atom ax =>
              cases ax with
              | zero => simp [genComputeSkeleton, Nock.Noun.slot] at h
              | succ ax' =>
                cases hs : Nock.Noun.slot (ax' + 1) subject with
                | none => simp [genComputeSkeleton, hs] at h
                | some res =>
                  simp only [genComputeSkeleton, hs, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨ht, _⟩ := h
                  subst ht
                  refine ⟨by simp [skelNode, NTree.label], ?_⟩
                  intro r hr
                  simp only [skelNode, NTree.label, List.mem_cons, List.not_mem_nil,
                    or_false] at hr
                  rcases hr with rfl | rfl <;> simp
          | 1 =>
            simp only [genComputeSkeleton, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨ht, _⟩ := h
            subst ht
            refine ⟨by simp [skelNode, NTree.label], ?_⟩
            intro r hr
            simp only [skelNode, NTree.label, List.mem_cons, List.not_mem_nil, or_false] at hr
            subst hr
            simp
          | 2 =>
            cases ftail with
            | atom _ => simp [genComputeSkeleton] at h
            | cell b c =>
              cases hB : genComputeSkeleton (K := K) n subject b with
              | error e => simp [genComputeSkeleton, hB] at h
              | ok pb =>
                cases hC : genComputeSkeleton (K := K) n subject c with
                | error e => simp [genComputeSkeleton, hB, hC] at h
                | ok pc =>
                  obtain ⟨lTree, sf1⟩ := pb
                  obtain ⟨rTree, sf2⟩ := pc
                  cases hM : genComputeSkeleton (K := K) n sf1 sf2 with
                  | error e => simp [genComputeSkeleton, hB, hC, hM] at h
                  | ok pm =>
                    obtain ⟨mTree, res⟩ := pm
                    simp only [genComputeSkeleton, hB, hC, hM, Except.ok.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨ht, _⟩ := h
                    subst ht
                    refine ⟨by simp [skelNode, NTree.label], ?_⟩
                    intro r hr
                    simp only [skelNode, NTree.label, List.mem_cons, List.not_mem_nil,
                      or_false] at hr
                    rcases hr with rfl | rfl <;> simp
          | 3 =>
            cases hB : genComputeSkeleton (K := K) n subject ftail with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pb =>
              obtain ⟨callTree, callRes⟩ := pb
              simp only [genComputeSkeleton, hB, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨ht, _⟩ := h
              subst ht
              refine ⟨by simp [skelNode, NTree.label], ?_⟩
              intro r hr
              simp only [skelNode, NTree.label, List.mem_cons, List.not_mem_nil, or_false] at hr
              subst hr
              simp
          | 4 =>
            cases hB : genComputeSkeleton (K := K) n subject ftail with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pb =>
              obtain ⟨callTree, callRes⟩ := pb
              cases hl : Nock.Noun.lus callRes with
              | none => simp [genComputeSkeleton, hB, hl] at h
              | some res =>
                simp only [genComputeSkeleton, hB, hl, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨ht, _⟩ := h
                subst ht
                refine ⟨by simp [skelNode, NTree.label], ?_⟩
                intro r hr
                simp only [skelNode, NTree.label, List.mem_cons, List.not_mem_nil,
                  or_false] at hr
                subst hr
                simp
          | 5 =>
            cases ftail with
            | atom _ => simp [genComputeSkeleton] at h
            | cell b c =>
              cases hB : genComputeSkeleton (K := K) n subject b with
              | error e => simp [genComputeSkeleton, hB] at h
              | ok pb =>
                cases hC : genComputeSkeleton (K := K) n subject c with
                | error e => simp [genComputeSkeleton, hB, hC] at h
                | ok pc =>
                  obtain ⟨bTree, sf1⟩ := pb
                  obtain ⟨cTree, sf2⟩ := pc
                  simp only [genComputeSkeleton, hB, hC, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨ht, _⟩ := h
                  subst ht
                  refine ⟨by simp [skelNode, NTree.label], ?_⟩
                  intro r hr
                  simp only [skelNode, NTree.label, List.mem_cons, List.not_mem_nil,
                    or_false] at hr
                  rcases hr with rfl | rfl <;> simp
          | 6 =>
            cases ftail with
            | atom _ => simp [genComputeSkeleton] at h
            | cell b cd =>
              cases cd with
              | atom _ => simp [genComputeSkeleton] at h
              | cell c d =>
                cases hB : genComputeSkeleton (K := K) n subject b with
                | error e => simp [genComputeSkeleton, hB] at h
                | ok pb =>
                  obtain ⟨condTree, cond⟩ := pb
                  cases cond with
                  | cell _ _ => simp [genComputeSkeleton, hB] at h
                  | atom cv =>
                    match cv with
                    | 0 =>
                      cases hC : genComputeSkeleton (K := K) n subject c with
                      | error e => simp [genComputeSkeleton, hB, hC] at h
                      | ok pc =>
                        obtain ⟨takenTree, res⟩ := pc
                        simp only [genComputeSkeleton, hB, hC, Except.ok.injEq,
                          Prod.mk.injEq] at h
                        obtain ⟨ht, _⟩ := h
                        subst ht
                        refine ⟨by simp [skelNode, NTree.label], ?_⟩
                        intro r hr
                        simp only [skelNode, NTree.label, List.mem_cons, List.not_mem_nil,
                          or_false] at hr
                        rcases hr with rfl | rfl | rfl <;> simp
                    | 1 =>
                      cases hD : genComputeSkeleton (K := K) n subject d with
                      | error e => simp [genComputeSkeleton, hB, hD] at h
                      | ok pd =>
                        obtain ⟨takenTree, res⟩ := pd
                        simp only [genComputeSkeleton, hB, hD, Except.ok.injEq,
                          Prod.mk.injEq] at h
                        obtain ⟨ht, _⟩ := h
                        subst ht
                        refine ⟨by simp [skelNode, NTree.label], ?_⟩
                        intro r hr
                        simp only [skelNode, NTree.label, List.mem_cons, List.not_mem_nil,
                          or_false] at hr
                        rcases hr with rfl | rfl | rfl <;> simp
                    | _ + 2 => simp [genComputeSkeleton, hB] at h
          | 7 =>
            cases ftail with
            | atom _ => simp [genComputeSkeleton] at h
            | cell b c =>
              cases hB : genComputeSkeleton (K := K) n subject b with
              | error e => simp [genComputeSkeleton, hB] at h
              | ok pb =>
                obtain ⟨bTree, sb⟩ := pb
                cases hC : genComputeSkeleton (K := K) n sb c with
                | error e => simp [genComputeSkeleton, hB, hC] at h
                | ok pc =>
                  obtain ⟨cTree, res⟩ := pc
                  simp only [genComputeSkeleton, hB, hC, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨ht, _⟩ := h
                  subst ht
                  refine ⟨by simp [skelNode, NTree.label], ?_⟩
                  intro r hr
                  simp only [skelNode, NTree.label, List.mem_cons, List.not_mem_nil,
                    or_false] at hr
                  rcases hr with rfl | rfl <;> simp
          | 8 =>
            cases ftail with
            | atom _ => simp [genComputeSkeleton] at h
            | cell b c =>
              cases hB : genComputeSkeleton (K := K) n subject b with
              | error e => simp [genComputeSkeleton, hB] at h
              | ok pb =>
                obtain ⟨bTree, sb⟩ := pb
                cases hC : genComputeSkeleton (K := K) n (.cell sb subject) c with
                | error e => simp [genComputeSkeleton, hB, hC] at h
                | ok pc =>
                  obtain ⟨cTree, res⟩ := pc
                  simp only [genComputeSkeleton, hB, hC, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨ht, _⟩ := h
                  subst ht
                  refine ⟨by simp [skelNode, NTree.label], ?_⟩
                  intro r hr
                  simp only [skelNode, NTree.label, List.mem_cons, List.not_mem_nil,
                    or_false] at hr
                  rcases hr with rfl | rfl <;> simp
          | 9 =>
            cases ftail with
            | atom _ => simp [genComputeSkeleton] at h
            | cell fhh c =>
              cases fhh with
              | cell _ _ => simp [genComputeSkeleton] at h
              | atom ax =>
                cases hC : genComputeSkeleton (K := K) n subject c with
                | error e => simp [genComputeSkeleton, hC] at h
                | ok pc =>
                  obtain ⟨coreTree, core⟩ := pc
                  cases ax with
                  | zero => simp [genComputeSkeleton, hC, Nock.Noun.slot] at h
                  | succ ax' =>
                    cases hs : Nock.Noun.slot (ax' + 1) core with
                    | none => simp [genComputeSkeleton, hC, hs] at h
                    | some arm =>
                      cases hI : genComputeSkeleton (K := K) n core arm with
                      | error e => simp [genComputeSkeleton, hC, hs, hI] at h
                      | ok pi =>
                        obtain ⟨invokeTree, res⟩ := pi
                        simp only [genComputeSkeleton, hC, hs, hI, Except.ok.injEq,
                          Prod.mk.injEq] at h
                        obtain ⟨ht, _⟩ := h
                        subst ht
                        refine ⟨by simp [skelNode, NTree.label], ?_⟩
                        intro r hr
                        simp only [skelNode, NTree.label, List.mem_cons, List.not_mem_nil,
                          or_false] at hr
                        rcases hr with rfl | rfl | rfl <;> simp
          | 10 => simp [genComputeSkeleton] at h
          | 11 => simp [genComputeSkeleton] at h
          | _ + 12 => simp [genComputeSkeleton] at h



/-! ## `memory_first_counts` and `memory_first_indicator`, generically -/

/-- The first BFS row of a tree is its root label. -/
theorem bfsRows_zero (u : NTree (GenComputeRow K)) :
    (bfsRows u)[0]'(bfsRows_length_pos u) = u.label := by
  have hb : bfsForest [u] = u :: bfsForest ([u].flatMap NTree.children) := by
    rw [bfsForest_cons_eq [u] (by simp)]; rfl
  unfold bfsRows
  simp [hb]

/-- `bfsAssign` re-stamps but does not move the root's service requests. -/
theorem bfsAssign_root_requests (u : NTree (GenComputeRow K)) :
    (bfsAssign u).label.requests = u.label.requests := by
  have hpos : (1 : ℕ) - 1 < (bfsRows u).length := by
    simpa using bfsRows_length_pos u
  rw [bfsAssign_label, bfsLabelAt_requests u 1 hpos]
  simpa using congrArg GenComputeRow.requests (bfsRows_zero u)

/-- Record extraction preserves axes, so axis positivity transfers to the extracted records. -/
theorem extractNodeReqs_axis_pos (g : GenComputeRow K)
    (h : ∀ r : ServiceReq K, r ∈ g.requests → 1 ≤ r.axis) :
    ∀ r ∈ extractNodeReqs g, 1 ≤ r.axis := by
  intro r hr
  obtain ⟨req, hreq, _, _, hax⟩ := extractNodeReqsAux_mem g.stamp 0 g.requests r hr
  rw [hax]
  exact h req hreq

/-- **The head of the generated served forest exists, for any accepted program.**
    Live leftover `T = mem.axis` — first-row `indicator = 0` is residual. -/
theorem genAssignedMemory_head_pt (htwo : (2 : K) ≠ 0) (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∃ tr qs, bfsForest (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t))) =
        tr :: qs := by
  obtain ⟨hne, hax⟩ := genComputeSkeleton_root_requests h
  have hreq : (bfsAssign (airReorder t)).label.requests = t.label.requests := by
    rw [bfsAssign_root_requests, airReorder_label]
  have hne' : (bfsAssign (airReorder t)).label.requests ≠ [] := by rw [hreq]; exact hne
  have hax' : ∀ r ∈ extractNodeReqs (bfsAssign (airReorder t)).label, 1 ≤ r.axis :=
    extractNodeReqs_axis_pos _ (by rw [hreq]; exact hax)
  obtain ⟨tr, rest, heq⟩ :=
    genMemForestFromTree_head_pt (lmb := lmb) htwo (encC z) z α (bfsAssign (airReorder t)) hne' hax'
  obtain ⟨qs, hqs⟩ := bfsForest_head _ tr rest heq
  exact ⟨tr, qs, hqs⟩

/-- First-row `pt` is the head label's `pt` (threading does not rewrite it).
    Live leftover — does **not** claim `indicator = 0`. -/
theorem genMemoryFirstPt (htwo : (2 : K) ≠ 0)
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h) :
    ∃ p : MemoryTable.Pub K,
      ((genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).memoryPubAt
      ⟨0, (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).memRows_pos⟩).pt = p.pt := by
  exact ⟨_, rfl⟩

/-- Every executed memory row carries the configuration's `λ` (written by the encode). -/
theorem genExactExecution_lambda?
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K) (t : NTree (GenComputeRow K))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h) :
    ∀ i, ((genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).memoryPubAt i).lambda? =
      some chal.lam := by
  intro i
  have hmem' := ExactExecution.memoryRowAt_mem
    (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem) i
  rw [genExactExecution_memoryRows] at hmem'
  obtain ⟨n, _, hn⟩ := List.mem_map.mp hmem'
  rw [ExactExecution.memoryPubAt, ← hn]
  unfold MemoryRowTemplate.encodeRow
  split <;> rfl

/-- `Noun.slot` never succeeds at axis `0` (`Reference.lean`), so a well-formed
    request is axis-positive -/
theorem slot_implies_axis_pos {n r : Noun} {ax : ℕ}
    (h : Noun.slot ax n = some r) : 1 ≤ ax := by
  cases ax with
  | zero => simp [Noun.slot] at h
  | succ _ => exact Nat.succ_le_succ (Nat.zero_le _)

/-- `threadPubs` rewrites only the accumulator pair; `pt` is the source pub. -/
theorem threadPubs_get_pt (inp : MemoryTable.Inputs K)
    (acc : K) (ps : List (MemoryTable.Pub K)) (i : ℕ) (hi : i < ps.length) :
    ((threadPubs inp acc ps)[i]'(by rwa [threadPubs_length])).pt = ps[i].pt := by
  induction ps generalizing acc i with
  | nil => cases hi
  | cons p rest ih =>
    cases i with
    | zero =>
        simp [threadPubs_cons, threadPub_pt]
    | succ j =>
        have hj : j < rest.length := Nat.lt_of_succ_lt_succ hi
        simpa [threadPubs_cons] using ih (threadPub inp acc p).1 j hj

/-- The BFS list of a forest begins with the roots themselves. -/
theorem bfsForest_length_ge {α} (l : List (NTree α)) :
    l.length ≤ (bfsForest l).length := by
  by_cases hne : l = []
  · subst hne; simp [bfsForest_nil]
  · rw [bfsForest_cons_eq l hne, List.length_append]; omega

theorem bfsForest_get_root {α} (l : List (NTree α)) (i : ℕ)
    (hi : i < l.length) :
    (bfsForest l)[i]'(Nat.lt_of_lt_of_le hi (bfsForest_length_ge l)) = l[i] := by
  have hne : l ≠ [] := by
    intro h; subst h; cases hi
  have heq := bfsForest_cons_eq l hne
  have hltL : i < (bfsForest l).length :=
    Nat.lt_of_lt_of_le hi (bfsForest_length_ge l)
  have hltR : i < (l ++ bfsForest (l.flatMap NTree.children)).length := by
    rw [← heq]; exact hltL
  have hcong := congrArg (fun xs : List (NTree α) => xs[i]?) heq
  simp only [List.getElem?_eq_getElem hltL, List.getElem?_eq_getElem hltR] at hcong
  exact (Option.some.inj hcong).trans (List.getElem_append_left hi)

/-- Axis positivity on every in-tree node is `computeTreeAxes`. -/
theorem computeTreeAxes_of_axis_pos
    (u : NTree (GenComputeRow K))
    (h : ∀ n, InTree u n → ∀ r ∈ extractNodeReqs n.label, 1 ≤ r.axis) :
    computeTreeAxes (K := K) u :=
  h

/-- Assigned AIR-ordered tree of an accepted program is axis-positive at every node. -/
theorem computeTreeAxes_bfsAssign_air
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    computeTreeAxes (K := K) (bfsAssign (airReorder t)) :=
  computeTreeAxes_of_axis_pos _ fun n hn r hr =>
    slot_implies_axis_pos
      (bfsAssign_extract_requests_slot (airReorder t)
        (treeRequestsWF_airReorder (genComputeSkeleton_tree_requests_wf h)) n hn r hr)

/-- **Accepted program: every root of the served forest has `pt = (0, 0)`**, given that every
    extracted request axis is below `ringChar K` (`hlt`; from the guarded run, see
    `GenRequestAxisBound`).  Axis positivity is `computeTreeAxes_bfsAssign_air`. -/
theorem genMemForestFromTree_accepted_all_root_pt (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hlt : ∀ n, InTree (bfsAssign (airReorder t)) n →
      ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t)),
      u.label.row.2.2.pt.indicator = 0 ∧ u.label.row.2.2.pt.counts = 0 :=
  genMemForestFromTree_all_root_pt (encC z) z α _
    (fun n hn r hr => ⟨computeTreeAxes_bfsAssign_air h n hn r hr, hlt n hn r hr⟩)

/-- A nonempty BFS list has a nonempty root list: `0 < kMem`. -/
theorem genExactConfig_kMem_pos
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α : K) (t : NTree (GenComputeRow K))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h) :
    (0 : ℕ) < (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem := by
  show 0 < (genMemoryForest z α chal.lam (memInputs z) t).length
  cases hmf : genMemoryForest z α chal.lam (memInputs z) t with
  | nil => rw [hmf, bfsForest_nil] at hmempos; simp at hmempos
  | cons _ _ => simp

/-- **`laterSeedZeros` (live).**  Every seed row `i < kMem` — the forest roots, first in BFS
    order — has `pt = (0, 0)`.  Row `0` is `memory_first_counts`/`memory_first_indicator`. -/
theorem genExactExecutionA_laterSeedZeros
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hlt : ∀ n, InTree (bfsAssign (airReorder t)) n →
      ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h) :
    ∀ i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).memRows,
      (i : ℕ) < (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
          (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem →
        ((genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).memoryPubAt i).pt.counts = 0 ∧
          ((genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).memoryPubAt i).pt.indicator
                = 0 := by
  intro i hi
  set forest := genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)) with hforest
  set exec := genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
    (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem with hexec
  have hk : (i : ℕ) < forest.length := by
    have : (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem =
        (genMemoryForest z α chal.lam (memInputs z) t).length := rfl
    rw [this] at hi
    unfold genMemoryForest at hi
    rw [threadGenForest_length] at hi
    exact hi
  have hpubs := genExactExecutionA_memoryPubs (F := F) chal Ksz orbit horb z α a b c t
    hmempos hcomp hmem
  set L := ((bfsForest forest).map NTree.label).map (fun g : GenMemoryRow K => g.row.2.2)
    with hL
  have hiL : (i : ℕ) < L.length := by
    simp only [hL, List.length_map]
    exact Nat.lt_of_lt_of_le hk (bfsForest_length_ge forest)
  have hiR : (i : ℕ) < exec.memoryRows.length := by
    rw [exec.memoryRows_length]; exact i.isLt
  have hpub : exec.memoryPubAt i = (threadPubs (memInputs z) 0 L)[(i : ℕ)]'(by
      rw [threadPubs_length]; exact hiL) := by
    have hget := congrArg (fun xs => xs[(i : ℕ)]?) hpubs
    simp only [List.getElem?_map] at hget
    rw [List.getElem?_eq_getElem hiR, List.getElem?_eq_getElem
      (by rw [threadPubs_length]; exact hiL)] at hget
    simpa [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt] using hget
  have hpt : (exec.memoryPubAt i).pt = (forest[(i : ℕ)]'hk).label.row.2.2.pt := by
    rw [hpub, threadPubs_get_pt (memInputs z) 0 L i hiL]
    simp only [hL, List.getElem_map]
    rw [bfsForest_get_root forest i hk]
  have hroot := genMemForestFromTree_accepted_all_root_pt z α h hlt
    (forest[(i : ℕ)]'hk) (List.getElem_mem hk)
  rw [hpt]
  exact ⟨hroot.2, hroot.1⟩

/-- **`laterSeedZeros` (live), on the executed trace.**  The encode keeps `pt`. -/
theorem genExactExecution_laterSeedZeros
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hlt : ∀ n, InTree (bfsAssign (airReorder t)) n →
      ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h) :
    ∀ i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).memRows,
      (i : ℕ) < (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
          (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem →
        ((genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).memoryPubAt i).pt.counts = 0 ∧
          ((genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).memoryPubAt i).pt.indicator
                = 0 := by
  intro i hi
  rw [genExactExecution, encodeMem_memoryPubAt_pt]
  exact genExactExecutionA_laterSeedZeros (F := F) chal Ksz orbit horb z α a b c h hlt
    hmempos hcomp hmem i hi

/-! ## `Nonempty (SemanticIOPreimage)`

That is what this section supplies, following
`MatmulConfig65537.specializes_threaded` (`GenMatmulSemantic.lean`) — every step of which is generic
in substance once the tree is a variable.  The timestamp skeleton is built at the **unthreaded**
forest, exactly as both live configurations commit it; `genSemanticSkeleton_threadGenForest`
(`GenSemanticLmIO.lean:2457`) reconciles that with `genBindsAt_threaded`'s threaded one. -/

/-- Map the right list of a `Forall₂` through a relation-preserving function. -/
theorem forall2_map_right_of {A B : Type*} {R : A → B → Prop} {f : B → B}
    (hf : ∀ a b, R a b → R a (f b)) :
    ∀ {l₁ : List A} {l₂ : List B}, List.Forall₂ R l₁ l₂ → List.Forall₂ R l₁ (l₂.map f)
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (hf _ _ h) (forall2_map_right_of hf t)

/-- The carrier's compute rows, in the `bfsForest`-map form the timestamp equations want. -/
theorem genExactExecution_computeRows_bfsForest
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K) (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem).computeRows =
      (bfsForest [bfsAssign (airReorder t)]).map
        (fun n => setRowCoins a b c (renderNode z α n.label).row) := by
  rw [genExactExecution_computeRows chal Ksz orbit horb a b c, genComputeRows,
    bfsRows_renderRows]
  unfold bfsRows
  rw [List.map_map, List.map_map]
  rfl

/-- **The compute timestamp equations, for any accepted program.** -/
theorem genComputeTimestamps
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K) (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    List.Forall₂ (ComputeTimestampSpecializesAt α)
      (bfsStamps (bfsAssign (airReorder t)))
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem).computeRows := by
  rw [genExactExecution_computeRows_bfsForest chal Ksz orbit horb z α a b c t mf
    hmempos hcomp hmem]
  unfold bfsStamps
  rw [forall2_map_map_iff]
  intro n hn
  have hmem' : n.label ∈ (bfsForest [bfsAssign (airReorder t)]).map NTree.label :=
    List.mem_map.mpr ⟨n, hn, rfl⟩
  rw [bfsAssign_bfsForest_labels, List.mem_map] at hmem'
  obtain ⟨i, hi, hni⟩ := hmem'
  have hi' := lt_bfsRows_of_mem_range' hi
  have hst : n.label.stamp.state = n.label.skel.state := by
    rw [← hni]
    exact bfsLabelAt_state (airReorder t) i hi'
  have hln : n.label.stamp.lnPrevExponent ≤ n.label.stamp.lnExponent := by
    rw [← hni, bfsLabelAt_stamp (airReorder t) i hi']
    exact stampOfAcc_lnPrev_le_lnExponent _ _
  have hrec : ∀ j : Fin 3,
      n.label.stamp.lnPrevExponent ≤ n.label.stamp.recordExponent j := fun j => by
    rw [← hni, bfsLabelAt_stamp (airReorder t) i hi']
    exact stampOfAcc_lnPrev_le_recordExponent _ _ j
  exact computeTimestampSpecializesAt_setRowCoins α a b c
    (renderNode_specializes z α n.label hst hln hrec)

/-- The compute origin list, which the request bridge takes separately under the relative RAP form. -/
theorem genComputeOrigins
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K) (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    List.Forall₂ (fun stamp row => row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
      (bfsStamps (bfsAssign (airReorder t)))
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem).computeRows := by
  rw [genExactExecution_computeRows_bfsForest chal Ksz orbit horb z α a b c t mf
    hmempos hcomp hmem]
  unfold bfsStamps
  rw [forall2_map_map_iff]
  intro n _
  exact renderNode_ln_prev z α n.label

/-- The carrier's memory rows in threaded-row form (the executed rows are their row encode). -/
theorem genExactExecution_memoryRows_threadGenRows
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K) (t : NTree (GenComputeRow K))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h) :
    (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).memoryRows =
      ((threadGenRows (memInputs z) 0
        ((bfsForest (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))).map
          NTree.label)).map GenMemoryRow.row).map (MemoryRowTemplate.encodeRow chal.lam) := by
  rw [genExactExecution_memoryRows chal Ksz orbit horb a b c]
  rw [show (fun n : NTree (GenMemoryRow K) => MemoryRowTemplate.encodeRow chal.lam
      (GenMemoryRow.row n.label)) =
      MemoryRowTemplate.encodeRow chal.lam ∘ GenMemoryRow.row ∘ NTree.label from rfl, ← List.map_map,
      ← List.map_map]
  unfold genMemoryForest
  rw [threadGenForest_bfs_labels]

/-- **The memory timestamp equations, for any accepted program.** -/
theorem genMemoryTimestamps
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h) :
    List.Forall₂ (MemoryTimestampSpecializesAt α)
      (genMemoryStamps (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t))))
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).memoryRows := by
  rw [genExactExecution_memoryRows_threadGenRows chal Ksz orbit horb z α a b c t
    hmempos hcomp hmem]
  unfold genMemoryStamps
  have hstamps :
      (bfsForest (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))).map
          (fun n => n.label.stamp) =
        ((bfsForest (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))).map
          NTree.label).map GenMemoryRow.stamp := by
    rw [List.map_map]; rfl
  rw [hstamps]
  refine forall2_map_right_of (R := MemoryTimestampSpecializesAt α)
    (fun _ _ h => memoryTimestampSpecializesAt_encodeRow h)
    (threadGenRows_timestamp α (memInputs z) 0 _ ?_)
  intro g hg
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
  obtain ⟨w, hw, hin⟩ := (mem_bfsForest _ u).mp hu
  exact inTree_memoryTimestamp z α (genComputeSkeleton_memForest_OK_air z α h w hw) hin

/-- Threading does not move the committed semantic skeleton, at the carrier's own forest. -/
theorem genSemanticSkeleton_genMemoryForest (u : NTree (GenComputeRow K)) (z α : K)
    (inp : MemoryTable.Inputs K) (t : NTree (GenComputeRow K)) :
    genSemanticSkeleton u (genMemoryForest z α lmb inp t) =
      genSemanticSkeleton u (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t))) :=
  genSemanticSkeleton_threadGenForest u inp 0 _

/-- **`TimestampSpecializesAt` for any accepted program**, at the generated timestamp skeleton. -/
theorem genSpecializesAt (z α : K) (hz : z ≠ 0)
    (chal : ChallengeVector K) (hzc : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h) (a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h) :
    TimestampSpecializesAt z α
      (genTimestampSkeleton F (airReorder t)
        (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))
        (genComputeSkeleton_memForest_stampsWellFormed z α h))
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem) := by
  have hbind := genBindsAt_threaded (F := F) z α (memInputs z) chal hzc Ksz orbit horb a b c h
    hmempos hcomp hmem
  rw [genSemanticSkeleton_genMemoryForest] at hbind
  have hct := genComputeTimestamps (F := F) chal Ksz orbit horb z α a b c t
    (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem
  have hmt := genMemoryTimestamps (F := F) chal Ksz orbit horb z α a b c h
    hmempos hcomp hmem
  have hor := genComputeOrigins (F := F) chal Ksz orbit horb z α a b c t
    (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem
  exact
    { challengeEquation := hα
      semanticBinding := hbind
      computeTimestampEquations := hct
      memoryTimestampEquations := hmt
      requestBridgeEquation := semanticRequestBridgeEquation hz hbind hct hor
      responseBridgeEquation := semanticResponseBridgeEquation hbind hmt
        (genExactExecution_memoryRows_lambda (F := F) chal Ksz orbit horb a b c _ _
          hmempos hcomp hmem) }

/-- **`Nonempty (SemanticIOPreimage)` — `SemanticExactLanguage`'s third field — for any accepted
program.**  `EO`'s `genTimestampSkeleton_lmio` supplies `L_mIO`; the timestamp window `B` and the
orbit bound are the declared arithmetic side conditions of `nockCompiles`. -/
theorem genSemanticIOPreimage (z α : K) (hz : z ≠ 0)
    (chal : ChallengeVector K) (hzc : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h) (a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz) :
    Nonempty (SemanticIOPreimage
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)) :=
  ⟨(genSpecializesAt (F := F) z α hz chal hzc hα Ksz orbit horb a b c h
      hmempos hcomp hmem).toSemanticIOPreimage B hB
    (genSemanticRequestsAt_timestampBound (F := F) B z (airReorder t) _ hwin)
    (genSemanticResponsesAt_timestampBound (F := F) B z α (airReorder t) hwin)
    (genTimestampSkeleton_lmio (F := F) Ksz z α h
      (genComputeSkeleton_memForest_stampsWellFormed z α h) hKsz)
    (genSemanticRequests_exponent_nodup (airReorder t) _)⟩



/-! ## The languages, assembled

`genChained` is `ChainedSemanticExactLanguage` for **any** program `genComputeSkeleton` accepts, at
an arbitrary field, seed, timestamp challenge and coin vector.  Its hypotheses are exactly:

* the challenge vector's own declarations (`hinp`, `hmi`) — what a configuration writes down anyway;
* `z ≠ 0`, `(2 : K) ≠ 0` — the two field non-degeneracies both live configurations carry;
* `ComputeCoinsGeneric` — the coin side condition of `WF`, discharged above on OP5-free programs and
  at the `c = 1` convention;
* `B`, `hB`, `hwin`, `hKsz` — the timestamp window and orbit bound, i.e. `nockCompiles`' `horb`
  and `Def:L_mIO`'s `[K]` window;
* the two orbit-capacity bounds and memory non-emptiness the carrier already declares. -/

/-- **`SemanticExactLanguage` for any accepted program.** -/
theorem genSemanticExactLanguage (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hgood : SeedGood z t)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz) :
    SemanticExactLanguage
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem) := by
  have hα : chal.α = α := congrArg ComputeTable.Inputs.α hinp
  have hzc : chal.z = z := congrArg ComputeTable.Inputs.z hinp
  exact ⟨genComputeRowsAccepted (F := F) z α hz a b c chal hinp Ksz orbit horb h hgood _
      hmempos hcomp hmem,
    genMemoryRowsAccepted (F := F) z α hz htwo a b c chal hmi Ksz orbit horb h
      hmempos hcomp hmem,
    genSemanticIOPreimage (F := F) z α hz chal hzc hα Ksz orbit horb a b c h
      hmempos hcomp hmem B hB hwin hKsz⟩

/-- **`ChainedSemanticExactLanguage` for any accepted program.**  All ten fields. -/
theorem genChained (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hgood : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hlt : ∀ n, InTree (bfsAssign (airReorder t)) n →
      ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K) :
    ChainedSemanticExactLanguage
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem) where
  semantic := genSemanticExactLanguage (F := F) z α hz htwo a b c chal hinp hmi Ksz orbit horb
    h hgood hmempos hcomp hmem B hB hwin hKsz
  z_ne_zero := by
    have hzc : chal.z = z := congrArg ComputeTable.Inputs.z hinp
    show chal.z ≠ 0
    rw [hzc]
    exact hz
  compute_wf := genComputeWF (F := F) z α hz a b c chal hinp Ksz orbit horb t hcoins _
    hmempos hcomp hmem
  memory_wf := memoryWF_of_threadPubs _ (memInputs z) _
    (genExactExecution_memoryPubs (F := F) chal Ksz orbit horb z α a b c h hmempos hcomp hmem)
    hmi
    (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hq
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      exact wf_encPub _ (memInputs z) rfl (genAssignedMemory_WF z α hz h u hu))
  compute_chain := genComputeChain (F := F) chal Ksz orbit horb z α a b c t _
    hmempos hcomp hmem
  memory_chain := memoryChain_of_threadPubs _ (memInputs z) _
    (genExactExecution_memoryPubs (F := F) chal Ksz orbit horb z α a b c h hmempos hcomp hmem)
  memory_first_counts :=
    (genExactExecution_laterSeedZeros (F := F) chal Ksz orbit horb z α a b c h hlt
      hmempos hcomp hmem _ (genExactConfig_kMem_pos (F := F) chal Ksz orbit horb
        z α t hmempos hcomp hmem)).1
  memory_first_indicator :=
    (genExactExecution_laterSeedZeros (F := F) chal Ksz orbit horb z α a b c h hlt
      hmempos hcomp hmem _ (genExactConfig_kMem_pos (F := F) chal Ksz orbit horb
        z α t hmempos hcomp hmem)).2
  memory_first_ipre := memoryFirstIpre_of_threadPubs _ (memInputs z) _
    (genExactExecution_memoryPubs (F := F) chal Ksz orbit horb z α a b c h hmempos hcomp hmem)
  memory_last_icur := memoryLastIcur_of_threadPubs _ (memInputs z) _
    (genExactExecution_memoryPubs (F := F) chal Ksz orbit horb z α a b c h hmempos hcomp hmem)
    (by
      rw [sumDelta_map_encPub (memInputs z) rfl, sumDelta_eq_forestDelta]
      exact genMemForestFromTree_delta (encC z) z α _)
  memory_same_lambda :=
    ExactExecution.memory_same_lambda_of_const _ _
      (genExactExecution_lambda? (F := F) chal Ksz orbit horb z α a b c t
        hmempos hcomp hmem)

/-- **`TraversableChainedSemanticExactLanguage` for any
accepted program.** -/
theorem genTraversable (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hgood : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hlt : ∀ n, InTree (bfsAssign (airReorder t)) n →
      ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K) :
    TraversableChainedSemanticExactLanguage
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem) where
  chained := genChained (F := F) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hgood hcoins
    hmempos hcomp hmem B hB hwin hKsz hlt
  compute_topology := genComputeExactTopology (F := F) z α hz a b c chal hinp Ksz orbit horb
    h hgood _ hmempos hcomp hmem
  memory_topology := genMemoryExactTopology (F := F) z α hz htwo a b c chal hmi Ksz orbit horb
    h hmempos hcomp hmem

/-- **`sd`'s `language` field, for any accepted program.**  `genNounRealization`
supplies the second half from the commitment check's `BoundedBy`. -/
theorem genLanguage {q : ℕ} (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hgood : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q)
    (hlt : ∀ n, InTree (bfsAssign (airReorder t)) n →
      ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K) :
    NounRealizedTraversableChainedSemanticExactLanguage q
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem) where
  traversable := genTraversable (F := F) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hgood
    hcoins hmempos hcomp hmem B hB hwin hKsz hlt
  nounRealization := genNounRealization (F := F) z α hz chal
    (congrArg ComputeTable.Inputs.z hinp) Ksz orbit horb a b c h _
    (genThreadedMemoryNodesOK z α (memInputs z) h) hmempos hcomp hmem hb


end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecution_computePubAt
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAdjacentLn
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeChain
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeWF
#print axioms Nock.NockVMROM.Thm54.TraceGen.computeCoinsGeneric_of_noOp5
#print axioms Nock.NockVMROM.Thm54.TraceGen.computeCoinsGeneric_c_one
#print axioms Nock.NockVMROM.Thm54.TraceGen.memoryWF_of_threadPubs
#print axioms Nock.NockVMROM.Thm54.TraceGen.memoryChain_of_threadPubs
#print axioms Nock.NockVMROM.Thm54.TraceGen.memoryFirstIpre_of_threadPubs
#print axioms Nock.NockVMROM.Thm54.TraceGen.memoryLastIcur_of_threadPubs
#print axioms Nock.NockVMROM.Thm54.TraceGen.memoryFirstPt_of_threadPubs
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecution_memoryPubs
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAssignedMemory_WF
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedRecordTree_root_pt
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedChainedTree_root_pt
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_head_pt
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_root_requests
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAssignedMemory_head_pt
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemoryFirstPt
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecution_laterSeedZeros
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeTimestamps
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemoryTimestamps
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSpecializesAt
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemanticIOPreimage
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemanticExactLanguage
#print axioms Nock.NockVMROM.Thm54.TraceGen.genChained
#print axioms Nock.NockVMROM.Thm54.TraceGen.genTraversable
#print axioms Nock.NockVMROM.Thm54.TraceGen.genLanguage
