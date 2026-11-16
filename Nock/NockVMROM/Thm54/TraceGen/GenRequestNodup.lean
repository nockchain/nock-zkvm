/-
  Nock/NockVMROM/Thm54/TraceGen/GenRequestNodup.lean

  **`genBuildable`'s `hnodup`, at the generated carrier.**

  `BuildableNockExecution.requestNodup` (`GenExactExecution.lean:171` consumes it as `hnodup`) is
  `exec.derivedRequestIO.Nodup`, i.e. the encoded compute-request IO column has no repeated entry.
  `derivedRequestIO = rawRequests.map encRec` (`Language.lean:46`) and
  `rawRequests = computeRows.flatMap (activeRequestRecords ·.2.2.1)` (`:33`), so the obligation is
  about the multiset of memory records the compute rows emit.

  **What separates the records is the timestamp, and nothing else has to.**  `encRec`'s eighth
  coordinate is the record timestamp (`encRec_ts`, `AxisBridge.lean:1348`); at a generated carrier
  every active record's timestamp is `α ^ e` with `e` the record's committed exponent
  (`renderNode_active_timestamps`, `GenGenericRowFacts.lean`, all eleven states, no hypothesis),
  and the tree's exponents are exactly `1, 2, …, N` with `N = accAt (airReorder t) …`
  (`genSemanticRequests_exponents`, `GenSemanticLmIO.lean:734`).  Below `orderOf α` those powers are
  distinct, so the timestamp column alone is `Nodup`, and `Nodup` of a projection gives `Nodup` of
  the list.  This is the paper's own reason for the timestamp: the paper — "this timestamp is
  unique and represents the line number of the compute table at which the memory record was
  requested, thus having the closed form `z^i`" — and the paper, where the per-lookup
  uniqueness of each `z^i` is called key.  Read at source.

  **No injectivity of `encC` is used**, and none is available: the record's root
  and child fingerprints are never compared.  Nor is the DFS/BFS permutation bridge of
  `GenMemForestOrder.lean` needed — `rawRequests` is in BFS row order and so is
  `genSemanticRequests`, so the two line up directly and `genForestRecordExps` never enters.  That
  makes this route shorter than the one `FW` used for `timestampPowersNodup`, which had to cross a
  `Perm` because the *forest* is built in DFS order.

  **The premise.**  It is **not**
  additional at the assembly level: `horb_of_window` (`GenServedRoots.lean` §D.1) derives it from
  the `hB`/`hwin` window premise `genSemanticData` already carries (`FU.2` §1).  Note also that
  **no acceptance hypothesis is needed** — `treeRequestsMatch` never appears, because §A relates
  `rowSlots` to `getRecordExp` directly rather than through `extractNodeReqs`.  So the statements
  below hold at an arbitrary `t` and an arbitrary memory forest `mf`.

  §A the per-row exponent readout · §B the whole tree's · §C the request IO's timestamp column and
  its length · §D `hnodup`, and the response-length bound `hresp` reduces to.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericRowFacts
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticDataParts
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.Framework.Thm54

variable {K : Type} [Field K]

/-! ## A. One row's slot exponents are its `getRecordExp` readout

`rowSlots_exponents_of` (`GenSemanticLmIO.lean:627`) says the same thing *after* `stampOfAcc` has
been substituted.  This is the unconditional form: `rowSlots` reads `g.stamp.recordExponent i` at
each active slot and `getRecordExp g.stamp i` is that same projection with the `i < 3` bound
carried, so the two agree at any stamp whatsoever.  No `requestsMatchMemory`, no `bfsAssign`. -/

theorem rowSlots_exponents_eq_getRecordExp (g : GenComputeRow K) :
    (rowSlots g).map CanonicalRecordSlot.exponent =
      (List.range (Nock.Framework.recordCount g.skel.state)).map
        (fun i => getRecordExp g.stamp i) := by
  unfold rowSlots
  rw [ofFn_fin3]
  rcases recordCount_eq_123 g.skel.state with hn | hn | hn
  · have h0 : (0 : ℕ) < 1 := Nat.zero_lt_one
    have n2 : ¬ (2 : ℕ) < 1 := by omega
    simp [hn, h0, n2, getRecordExp, List.range_succ, List.range_zero]
  · have h0 : (0 : ℕ) < 2 := by omega
    have h1 : (1 : ℕ) < 2 := by omega
    simp [hn, h0, h1, getRecordExp, List.range_succ, List.range_zero]
  · have h0 : (0 : ℕ) < 3 := by omega
    have h1 : (1 : ℕ) < 3 := by omega
    have h2 : (2 : ℕ) < 3 := by omega
    simp [hn, h0, h1, h2, getRecordExp, List.range_succ, List.range_zero]

/-! ## B. The whole assigned tree's slot exponents are `1 … N`

`genSemanticRequests_eq_bfs` and `genSemanticRequests_exponents` (`GenSemanticLmIO.lean:658,734`)
already say this; the only work is putting `bfsRows (bfsAssign t)` in the shape they use.  Both are
hypothesis-free, so this is too. -/

theorem bfsRows_rowSlots_exponents (t : NTree (GenComputeRow K)) :
    ((bfsRows (bfsAssign t)).flatMap rowSlots).map CanonicalRecordSlot.exponent =
      (List.range (accAt t (bfsRows t).length)).map (fun i => i + 1) := by
  have hb : bfsRows (bfsAssign t) = (bfsForest [bfsAssign t]).map NTree.label := rfl
  rw [hb, bfsAssign_bfsForest_labels,
    ← genSemanticRequests_eq_bfs t ([] : List (NTree (GenMemoryRow K))),
    genSemanticRequests_exponents t ([] : List (NTree (GenMemoryRow K)))]

/-- The list `1 … N` is `Nodup`, and so are its `α`-powers below `orderOf α`. -/
theorem pow_succ_range_nodup (α : K) (N : ℕ) (horb : N < orderOf α) :
    ((List.range N).map (fun i => α ^ (i + 1))).Nodup := by
  have hinner : ((List.range N).map (fun i => i + 1)).Nodup :=
    List.Nodup.map (fun _ _ h => by omega) List.nodup_range
  have := List.Nodup.map_on (l := (List.range N).map (fun i => i + 1))
    (f := fun e => α ^ e) ?_ hinner
  · simpa [List.map_map, Function.comp_def] using this
  · intro x hx y hy hxy
    simp only [List.mem_map, List.mem_range] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := hy
    exact pow_injOn_Iio_orderOf (Set.mem_Iio.mpr (by omega))
      (Set.mem_Iio.mpr (by omega)) hxy

/-! ## C. The generated carrier's request IO, as a timestamp list

`setRowCoins` rewrites only the two RLC coin columns and leaves `.2.2` alone (`setRowCoins_pub`,
`GenWF.lean:57`), so the execution's rows emit the rendered rows' records verbatim. -/

/-- **One list of generated rows: rendered, coin-overwritten, flattened to a timestamp list.**
The induction is over the row list, and each step is §A plus `renderNode_active_timestamps`. -/
theorem renderedRows_activeRequest_ts (z α a b c : K) (l : List (GenComputeRow K)) :
    ((((l.map (renderNode z α)).map (fun g => setRowCoins a b c g.row)).flatMap
        (fun row => activeRequestRecords row.2.2.1)).map (fun r => r.ts)) =
      ((l.flatMap rowSlots).map CanonicalRecordSlot.exponent).map (fun e => α ^ e) := by
  induction l with
  | nil => simp
  | cons g l ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append, ih]
      congr 1
      have hs : (setRowCoins a b c (renderNode z α g).row).2.2.1
          = (renderNode z α g).row.2.2.1 := rfl
      rw [hs, renderNode_active_timestamps z α g, rowSlots_exponents_eq_getRecordExp g,
        List.map_map]
      simp [Function.comp_def]

section Gen

variable {F : Type} [Field F] [Algebra F K]

/-- **The emitted request records' timestamps are `α^1, …, α^N`**, in BFS row order, at the
generated carrier over an arbitrary compute tree and an arbitrary memory forest.  No acceptance
hypothesis and no orbit hypothesis: this is an identity, not yet a distinctness claim. -/
theorem genExactExecution_rawRequests_ts (z α : K)
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    ((genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem).rawRequests).map (fun r => r.ts) =
      (List.range (accAt (airReorder t) (bfsRows (airReorder t)).length)).map
        (fun i => α ^ (i + 1)) := by
  rw [ExactExecution.rawRequests_eq_computeRows,
    genExactExecution_computeRows chal Ksz orbit horb a b c, genComputeRows,
    bfsRows_renderRows, renderedRows_activeRequest_ts,
    bfsRows_rowSlots_exponents, List.map_map]
  simp [Function.comp_def]

/-- **The request IO column has exactly `N` entries** — the trace's own record count.  So
`genBuildable`'s `hprog` is the stated capacity condition `N + 1 ≤ 2 ^ orbit.h`. -/
theorem genExactExecution_derivedRequestIO_length (z α : K)
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem).derivedRequestIO.length =
      accAt (airReorder t) (bfsRows (airReorder t)).length := by
  have h := congrArg List.length
    (genExactExecution_rawRequests_ts (F := F) z α chal Ksz orbit horb a b c t mf
      hmempos hcomp hmem)
  simpa [ExactExecution.derivedRequestIO] using h

/-! ## D. `hnodup`, and the bound `hresp` reduces to -/

/-- **`requestNodup` at the generated carrier.**  `encRec`'s eighth coordinate is the timestamp
(`encRec_ts`), the timestamp column is `α^1 … α^N`, and those are distinct below `orderOf α`.
`Nodup` of a projection of a list gives `Nodup` of the list, so the encoded IO column is `Nodup`
however the other seven coordinates behave — no fingerprint injectivity is used. -/
theorem genExactExecution_requestNodup (z α : K)
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (a b c : K)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α) :
    (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
      hmempos hcomp hmem).derivedRequestIO.Nodup := by
  set exec := genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
    hmempos hcomp hmem with hexec
  have hts : (exec.rawRequests.map (fun r => r.ts)).Nodup := by
    rw [genExactExecution_rawRequests_ts (F := F) z α chal Ksz orbit horb a b c t mf
      hmempos hcomp hmem]
    exact pow_succ_range_nodup α _ horbα
  have hproj : exec.rawRequests.map (fun r => r.ts) =
      exec.derivedRequestIO.map (fun f => f 7) := by
    rw [ExactExecution.derivedRequestIO, List.map_map]
    exact List.map_congr_left fun r _ => rfl
  rw [hproj] at hts
  exact (List.Nodup.of_map _ hts)

end Gen

/-- A response list contributes at most one record per memory row. -/
theorem length_flatMap_le_of_length_le_one {A B : Type*} (f : A → List B)
    (hf : ∀ a, (f a).length ≤ 1) : ∀ l : List A, (l.flatMap f).length ≤ l.length
  | [] => by simp
  | a :: l => by
      have := length_flatMap_le_of_length_le_one f hf l
      have ha := hf a
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega

/-- `responseRecords` emits a
record only at `read_root` (`MemoryTable.lean:132`), so `genBuildable`'s `hresp` follows from the
stated capacity condition `memRows + 1 ≤ 2 ^ orbit.h` — a strengthening by one of `genExactConfig`'s
own `memRows_le`. -/
theorem derivedResponseIO_length_le {F : Type} [Field F] [Algebra F K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.derivedResponseIO.length ≤ exec.memoryRows.length :=
  -- Row-level memory: the retired `C' = 1` hypothesis is not needed; each `ver` row emits one
  -- encoded record whatever its `C'`.
  ExactExecution.derivedResponseIO_length_le exec

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.rowSlots_exponents_eq_getRecordExp
#print axioms Nock.NockVMROM.Thm54.TraceGen.bfsRows_rowSlots_exponents
#print axioms Nock.NockVMROM.Thm54.TraceGen.pow_succ_range_nodup
#print axioms Nock.NockVMROM.Thm54.TraceGen.renderedRows_activeRequest_ts
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecution_rawRequests_ts
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecution_derivedRequestIO_length
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecution_requestNodup
#print axioms Nock.NockVMROM.Thm54.TraceGen.derivedResponseIO_length_le
