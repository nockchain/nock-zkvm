/-
  Nock/NockVMROM/Thm54/TraceGen/GenServedRequestCoverage.lean

  **The converse of the root classification: every request is served by some built root.**

  `semanticCoverage` (`ServedMemoryTrace.lean:616`) needs the other direction: for a request the
  compute row actually emits, a `Service` **in some root's `services` list**.

  Three steps, and only the middle one is new.

  * `FB`'s `genMemForest_flatMap_read` (`GenMemForestOrder.lean:236`) is a list **equality**
    between the forest's per-root readout and the compute tree's request list, so membership
    transfers in both directions.

  * That root is at *some index*, and `genRoots_spec` at that index names *some* request `r'` of
    *some* node.  Nothing identifies `r'` with the request `r` we started from, and
    `genAnnotatedRecordTree` is not known to be injective (`FI` §5), so the tree equation is not
    enough.

  * `ServiceMatches` then transports the service's `root`/`child`/`axis`/`record` from `r'` to `r`.

  **Scope.**  §A is at an arbitrary compute tree.  §B is at `∀ program accepted by
  `genComputeSkeleton``, arbitrary field, seed, `α`, challenges, coins and memory inputs, under
  `horbα`.  No axis is fixed, no state is fixed, and no configuration is chosen.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenChainedServedGen

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.Framework.Thm54

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## A. The tree's request list, and its exponents as a key

`genForestRecordExps` (`GenMemForestOrder.lean:105`) is already the DFS `flatMap` of the per-node
request exponents; `genForestReqs` is the same walk keeping the requests themselves, so the two are
related by one `List.map`. -/

/-- Every `MemRecordReq` of every node, in the DFS pre-order the memory-forest builder walks. -/
def genForestReqs (t : NTree (GenComputeRow K)) : List MemRecordReq :=
  (dfsTree t).flatMap (fun n => extractNodeReqs n.label)

theorem genForestReqs_map_recordExp (t : NTree (GenComputeRow K)) :
    (genForestReqs t).map MemRecordReq.recordExp = genForestRecordExps t := by
  rw [genForestReqs, genForestRecordExps, List.map_flatMap]

/-- A request of any node of the tree is a request of the tree. -/
theorem mem_genForestReqs (t : NTree (GenComputeRow K))
    {n : NTree (GenComputeRow K)} (hn : InTree t n)
    {r : MemRecordReq} (hr : r ∈ extractNodeReqs n.label) :
    r ∈ genForestReqs t := by
  refine List.mem_flatMap.mpr ⟨n, ?_, hr⟩
  have hmem : n ∈ dfsForest [t] :=
    (mem_dfsForest _ n).mpr ⟨_, List.mem_singleton_self _, hn⟩
  simpa [dfsForest] using hmem

/-- **The record exponent is a key for the whole tree's requests.**

`genForestRecordExps_nodup` (`FB`) says the exponents are `1 … N` without repetition; read through
`List.inj_on_of_nodup_map` that is exactly injectivity of `recordExp` on the request list.  This is
what replaces the injectivity of `genAnnotatedRecordTree` that nothing proves. -/
theorem genForestReqs_recordExp_inj (t : NTree (GenComputeRow K))
    (hmatch : treeRequestsMatch (bfsAssign t))
    {r1 r2 : MemRecordReq}
    (h1 : r1 ∈ genForestReqs (bfsAssign t)) (h2 : r2 ∈ genForestReqs (bfsAssign t))
    (he : r1.recordExp = r2.recordExp) : r1 = r2 := by
  have hnd : ((genForestReqs (bfsAssign t)).map MemRecordReq.recordExp).Nodup := by
    rw [genForestReqs_map_recordExp]
    exact genForestRecordExps_nodup t hmatch
  exact List.inj_on_of_nodup_map hnd h1 h2 he

/-- Two requests of the tree whose timestamps agree inside `α`'s orbit are the same request. -/
theorem genForestReqs_eq_of_pow_eq {α : K} {t : NTree (GenComputeRow K)}
    (hmatch : treeRequestsMatch (bfsAssign t))
    (horb : accAt t (bfsRows t).length < orderOf α)
    {n1 n2 : NTree (GenComputeRow K)} (hn1 : InTree (bfsAssign t) n1)
    (hn2 : InTree (bfsAssign t) n2)
    {r1 r2 : MemRecordReq} (hr1 : r1 ∈ extractNodeReqs n1.label)
    (hr2 : r2 ∈ extractNodeReqs n2.label)
    (hpow : α ^ r1.recordExp = α ^ r2.recordExp) : r1 = r2 := by
  have hb1 : r1.recordExp < orderOf α :=
    extractNodeReqs_recordExp_lt_orderOf α hmatch horb hn1 hr1
  have hb2 : r2.recordExp < orderOf α :=
    extractNodeReqs_recordExp_lt_orderOf α hmatch horb hn2 hr2
  have hexp : r1.recordExp = r2.recordExp :=
    pow_injOn_Iio_orderOf (Set.mem_Iio.mpr hb1) (Set.mem_Iio.mpr hb2) hpow
  exact genForestReqs_recordExp_inj t hmatch
    (mem_genForestReqs _ hn1 hr1) (mem_genForestReqs _ hn2 hr2) hexp

/-! ## B. The served-record readout, and the request-level converse -/

/-- The record a `MemRecordReq` commits: the tuple both root builders install and `FG` §B.2
produces a `Service` at. -/
def reqRecord (E : Noun → ComputeTable.FP K) (α : K) (r : MemRecordReq) :
    ComputeTable.MemRec K :=
  ⟨E r.root, E r.child, (r.axis : K), α ^ r.recordExp⟩

/-- **`FB`'s read-back at the served-record readout.** -/
theorem genMemForest_flatMap_servedGen (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K)) :
    (genMemForestFromTree E z α lmb t).flatMap (fun u => servedGen [u]) =
      (dfsTree t).flatMap (fun n => (extractNodeReqs n.label).map (reqRecord E α)) :=
  genMemForest_flatMap_read E z α (fun u => servedGen [u]) (reqRecord E α)
    (fun r => genAnnotatedRecordTree_servedGen E z α r.root r.child r.axis r.recordExp)
    (fun _ _ _ _ hu => genAnnotatedChainedTree_pair_servedGen E z α _ _ hu) t

/-- **Every request's record is served by some root of the generated forest.**

The direction `ET` §2's classification does not give: it goes from a request to a root, not from a
root to a request.  It is the equality in `genMemForest_flatMap_read` that supplies it. -/
theorem exists_forest_root_serving (E : Noun → ComputeTable.FP K) (z α : K)
    (t : NTree (GenComputeRow K))
    {n : NTree (GenComputeRow K)} (hn : InTree t n)
    {r : MemRecordReq} (hr : r ∈ extractNodeReqs n.label) :
    ∃ j : ℕ, ∃ hj : j < (genMemForestFromTree E z α lmb t).length,
      reqRecord E α r ∈ servedGen [(genMemForestFromTree E z α lmb t)[j]'hj] := by
  have hmemRHS : reqRecord E α r ∈
      (dfsTree t).flatMap (fun m => (extractNodeReqs m.label).map (reqRecord E α)) := by
    refine List.mem_flatMap.mpr ⟨n, ?_, List.mem_map.mpr ⟨r, hr, rfl⟩⟩
    have hmem : n ∈ dfsForest [t] :=
      (mem_dfsForest _ n).mpr ⟨_, List.mem_singleton_self _, hn⟩
    simpa [dfsForest] using hmem
  rw [← genMemForest_flatMap_servedGen E z α t] at hmemRHS
  obtain ⟨u, hu, hru⟩ := List.mem_flatMap.mp hmemRHS
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hu
  exact ⟨j, hj, by rw [hget]; exact hru⟩

/-! ## C. The service, in a built root's `services` list

`exists_forest_root_serving` puts the request's record in *some* root's served list;
`genRoots_spec` says what the root at that index is and which request the classification chose for
it.  §A's exponent key identifies the two requests, and `ServiceMatches` then carries the
service's four coordinates back to the request we started from.

This is the step `FG` §B.2 could not take: it produces a `Service`, and what `semanticCoverage`
needs is a `Service` **that is a member of `(roots i).services`**. -/

section MemRoots

variable {F : Type} [Field F] [Algebra F K]

/-- **A `Service` in a built root's `services` list, at any memory-record request of any node.**

The membership `FG` §B.2 does not give.  `horbα` is the orbit-capacity restriction already carried
by `genRoots` itself (`FI` §1) and it is used twice here: once through `genRoots`, and once to turn
the served record's timestamp back into its exponent -/
theorem exists_service_mem_genRoots (z α a b c : K)
    (chal : ChallengeVector K) (hz : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h)
    {n : NTree (GenComputeRow K)} (hn : InTree (bfsAssign (airReorder t)) n)
    {r : MemRecordReq} (hr : r ∈ extractNodeReqs n.label) :
    ∃ (i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem)
      (s : ServedMemoryTrace.Service
        (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
          (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem)
        (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
          (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem)),
      s ∈ (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
          hmempos hcomp hmem i).services ∧
        ServiceMatches (encC z) α s r := by
  have hmatch : treeRequestsMatch (bfsAssign (airReorder t)) :=
    genComputeSkeleton_air_requestsMatch h
  obtain ⟨j, hj, hru⟩ :=
    exists_forest_root_serving (encC z) z α (bfsAssign (airReorder t)) hn hr
  -- the classified index is the built index
  have hk : j < (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem := by
    have hlen : (genMemoryForest z α chal.lam inp t).length
        = (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t))).length := by
      rw [genMemoryForest_eq_thread, threadGenForest_length]
    have : j < (genMemoryForest z α chal.lam inp t).length := by rw [hlen]; exact hj
    exact this
  refine ⟨⟨j, hk⟩, ?_⟩
  obtain ⟨n', hn', hshape⟩ := genRoots_spec (F := F) z α a b c chal hz hα Ksz orbit horb inp h
    horbα hmempos hcomp hmem ⟨j, hk⟩
  rcases hshape with ⟨r', hr', hu', s, hsm, hsv⟩ | ⟨r1, hr1, r2, hr2, hlink, hne, ht, s1, s2,
      hsm1, hsm2, hsv⟩
  · -- one-record root: its served list is the singleton `[reqRecord … r']`
    have hserved : servedGen [(genMemForestFromTree (encC z) z α chal.lam
        (bfsAssign (airReorder t)))[j]'hj] = [reqRecord (encC z) α r'] := by
      rw [show (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))[j]'hj
          = genAnnotatedRecordTree (encC z) z α chal.lam r'.root r'.child r'.axis r'.recordExp from hu',
        genAnnotatedRecordTree_servedGen]
      rfl
    rw [hserved, List.mem_singleton] at hru
    have hpow : α ^ r.recordExp = α ^ r'.recordExp :=
      congrArg ComputeTable.MemRec.ts hru
    have hreq : r = r' :=
      genForestReqs_eq_of_pow_eq hmatch horbα hn hn' hr hr' hpow
    exact ⟨s, by rw [hsv]; exact List.mem_singleton_self s, hreq ▸ hsm⟩
  · -- chained pair: its served list is `[reqRecord … r1, reqRecord … r2]`
    have hserved : servedGen [(genMemForestFromTree (encC z) z α chal.lam
        (bfsAssign (airReorder t)))[j]'hj]
        = [reqRecord (encC z) α r1, reqRecord (encC z) α r2] := by
      rw [genAnnotatedChainedTree_pair_servedGen (encC z) z α r1 r2 ht]
      rfl
    rw [hserved] at hru
    rcases List.mem_cons.mp hru with heq | hru2
    · have hpow : α ^ r.recordExp = α ^ r1.recordExp :=
        congrArg ComputeTable.MemRec.ts heq
      have hreq : r = r1 :=
        genForestReqs_eq_of_pow_eq hmatch horbα hn hn' hr hr1 hpow
      exact ⟨s1, by rw [hsv]; exact List.mem_cons_self, hreq ▸ hsm1⟩
    · rw [List.mem_singleton] at hru2
      have hpow : α ^ r.recordExp = α ^ r2.recordExp :=
        congrArg ComputeTable.MemRec.ts hru2
      have hreq : r = r2 :=
        genForestReqs_eq_of_pow_eq hmatch horbα hn hn' hr hr2 hpow
      exact ⟨s2, by rw [hsv]; exact List.mem_cons_of_mem _ List.mem_cons_self, hreq ▸ hsm2⟩

end MemRoots

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genForestReqs_map_recordExp
#print axioms Nock.NockVMROM.Thm54.TraceGen.mem_genForestReqs
#print axioms Nock.NockVMROM.Thm54.TraceGen.genForestReqs_recordExp_inj
#print axioms Nock.NockVMROM.Thm54.TraceGen.genForestReqs_eq_of_pow_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemForest_flatMap_servedGen
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_forest_root_serving
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_service_mem_genRoots
