/-
  Nock/NockVMROM/Thm54/TraceGen/GenMemForestOrder.lean

  **The generated memory forest in DFS order, and its timestamp exponents.**

  `ExactServedMemoryTrace.timestampPowersNodup` (`ServedMemoryTrace.lean:610`) is the paper's
  global `z^i` uniqueness across the whole forest (the paper: "this timestamp is unique and
  represents the line number of the compute table at which the memory record was requested, thus
  having the closed form `z^i`"; the paper: "the uniqueness (per memory lookup) … of each
  timestamp `z^i` are key").  Distinctness is *available* — `genSemanticRequests_exponents`
  proves the request exponents are the list `1, 2, …, N`, and
  `genSemanticRequests_exponent_nodup` reads `Nodup` off it — but it is available in
  **BFS row order**, the
  order the walk RAP commits to, while `genMemForestFromTree` builds the memory
  forest by **DFS pre-order** recursion.

  The chain, in order:

  * **A** `genMemForestFromTree` *is* a DFS pre-order `flatMap` — `dfsTree` was defined in
    `Walk.lean` with exactly this recursion shape, so this is a mutual structural induction.
  * **B** one row's extracted `recordExp`s are its `rowSlots` exponents.  This is already in the
    tree: `extract_map_eq_rowSlots` (`GenSemanticLmIO.lean:1253`) under `requestsMatchMemory`.
  * **C** hence the whole forest's record exponents are a **permutation of `1 … N`**, so `Nodup`,
    and every one of them is `≤ N`.  `genForestRecordExps_ne_nil` records that the list is never
    empty, so the `Nodup` is not `Nodup []`.
  * **E** root-by-root accounting: `genRowMemForest`'s five arms read back each row's requests
    exactly once — the chainable pair contributes one root carrying two records, everything else
    one root per record.  Stated over an arbitrary readout `rd` into an arbitrary `B`, because the
    consumer wants it at `B = ℕ` (exponents) and at `B = K` (`z^i` timestamps).
  * **F** the two consumers, `genMemForest_recordExps_nodup` and
    `genMemForest_timestampPowers_nodup`.
  * **G** the `[α ^ e]` / `[α ^ e₁, α ^ e₂]` *shape* `h1`/`h2` assume is the shape the two
    existing builders' `timestampPowers` have: `rootTraceOfRecordTree` has `services := [s]` with
    `s.exponent = timestampExp α (α ^ e)`, and `rootTraceOfChainedPair` has `services := [s1, s2]`;
    `timestampPowers_of_services_singleton` / `_pair` read those off, via `timestampExp_pow_self`.

  **What is a hypothesis and why.**  `treeRequestsMatch (bfsAssign t)` is the tree's existing
  request/record agreement premise (`genComputeSkeleton_air_requestsMatch` supplies it for a
  generated program).  It subsumes `α ≠ 0`, since
  `orderOf (0 : K) = 0` and no natural is below that.

  **Not supplied here.**  `roots : ∀ i : Fin cfg.kMem, RootTrace cfg exec i` for the generated
  carrier does not exist yet, so the `ExactServedMemoryTrace` field itself is not filled.  What is
  filled is everything the field reduces to once `roots` is assembled from the two builders:
  `finRange_flatMap_getElem` converts the field's `(List.finRange cfg.kMem).flatMap (roots · |>.timestampPowers)`
  into `mf.flatMap rd` with `cfg.kMem = mf.length` (`genExactConfig`), and §F closes that.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServedForest
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticLmIO

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.ServedMemoryTrace

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## A. The forest builder is a DFS pre-order `flatMap` -/

mutual
theorem genMemForestFromTree_eq_flatMap (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ t : NTree (GenComputeRow K),
      genMemForestFromTree E z α lmb t =
        (dfsTree t).flatMap (fun n => genRowMemForest E z α lmb (extractNodeReqs n.label))
  | .node g cs => by
      rw [genMemForestFromTree, dfsTree_eq, NTree.children_node, List.flatMap_cons,
        NTree.label_node, genMemForestFromList_eq_flatMap E z α cs]

theorem genMemForestFromList_eq_flatMap (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ cs : List (NTree (GenComputeRow K)),
      genMemForestFromList E z α lmb cs =
        (dfsForest cs).flatMap (fun n => genRowMemForest E z α lmb (extractNodeReqs n.label))
  | [] => by rw [genMemForestFromList, dfsForest_nil, List.flatMap_nil]
  | c :: cs => by
      rw [genMemForestFromList, dfsForest_cons, List.flatMap_append,
        genMemForestFromTree_eq_flatMap E z α c, genMemForestFromList_eq_flatMap E z α cs]
end

/-! ## B. The record exponents of one compute row -/

theorem extractNodeReqs_recordExps_eq_rowSlots (g : GenComputeRow K)
    (h : requestsMatchMemory g) :
    (extractNodeReqs g).map MemRecordReq.recordExp =
      (rowSlots g).map CanonicalRecordSlot.exponent := by
  rw [← extract_map_eq_rowSlots g h, List.map_map]
  rfl

/-! ## C. The whole forest's record exponents -/

def genForestRecordExps (t : NTree (GenComputeRow K)) : List ℕ :=
  (dfsTree t).flatMap (fun n => (extractNodeReqs n.label).map MemRecordReq.recordExp)

theorem genForestRecordExps_bfs (u : NTree (GenComputeRow K))
    (hmatch : treeRequestsMatch u) :
    (genForestRecordExps u).Perm
      ((((bfsForest [u]).map NTree.label).flatMap rowSlots).map
        CanonicalRecordSlot.exponent) := by
  have heq :
      (bfsForest [u]).flatMap
          (fun n => (extractNodeReqs n.label).map MemRecordReq.recordExp) =
        (((bfsForest [u]).map NTree.label).flatMap rowSlots).map
          CanonicalRecordSlot.exponent := by
    rw [List.map_flatMap, List.flatMap_map]
    refine List.flatMap_congr ?_
    intro n hn
    obtain ⟨c, hc, hct⟩ := (mem_bfsForest [u] n).mp hn
    rw [List.mem_singleton] at hc
    subst hc
    exact extractNodeReqs_recordExps_eq_rowSlots _ (hmatch n hct)
  refine (List.Perm.flatMap_right _ (dfsTree_perm_bfsForest u)).trans ?_
  rw [heq]

theorem genForestRecordExps_perm_range (t : NTree (GenComputeRow K))
    (hmatch : treeRequestsMatch (bfsAssign t)) :
    (genForestRecordExps (bfsAssign t)).Perm
      ((List.range (accAt t (bfsRows t).length)).map (fun i => i + 1)) := by
  refine (genForestRecordExps_bfs _ hmatch).trans ?_
  rw [bfsAssign_bfsForest_labels t,
    ← genSemanticRequests_eq_bfs t ([] : List (NTree (GenMemoryRow K))),
    genSemanticRequests_exponents t ([] : List (NTree (GenMemoryRow K)))]

theorem genForestRecordExps_nodup (t : NTree (GenComputeRow K))
    (hmatch : treeRequestsMatch (bfsAssign t)) :
    (genForestRecordExps (bfsAssign t)).Nodup :=
  (genForestRecordExps_perm_range t hmatch).nodup_iff.mpr
    (List.Nodup.map Nat.succ_injective List.nodup_range)

theorem genForestRecordExps_length (t : NTree (GenComputeRow K))
    (hmatch : treeRequestsMatch (bfsAssign t)) :
    (genForestRecordExps (bfsAssign t)).length = accAt t (bfsRows t).length := by
  rw [(genForestRecordExps_perm_range t hmatch).length_eq, List.length_map,
    List.length_range]

/-- **Not vacuous.**  The forest always carries at least one record exponent, so the `Nodup`
above is never `Nodup []`. -/
theorem genForestRecordExps_ne_nil (t : NTree (GenComputeRow K))
    (hmatch : treeRequestsMatch (bfsAssign t)) :
    genForestRecordExps (bfsAssign t) ≠ [] := by
  have hlen := genForestRecordExps_length t hmatch
  have hpos := accAt_length_pos t (bfsRows_length_pos t)
  intro h
  rw [h, List.length_nil] at hlen
  omega

theorem genForestRecordExps_le (t : NTree (GenComputeRow K))
    (hmatch : treeRequestsMatch (bfsAssign t))
    {e : ℕ} (he : e ∈ genForestRecordExps (bfsAssign t)) :
    e ≤ accAt t (bfsRows t).length := by
  have h := (genForestRecordExps_perm_range t hmatch).mem_iff.mp he
  simp only [List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  omega

/-! ## D. Timestamp powers -/

theorem genForestTimestampPowers_nodup (t : NTree (GenComputeRow K)) (α : K)
    (hmatch : treeRequestsMatch (bfsAssign t))
    (horb : accAt t (bfsRows t).length < orderOf α) :
    ((genForestRecordExps (bfsAssign t)).map (fun e => α ^ e)).Nodup := by
  refine List.Nodup.map_on ?_ (genForestRecordExps_nodup t hmatch)
  intro x hx y hy hxy
  exact pow_injOn_Iio_orderOf
    (Set.mem_Iio.mpr (lt_of_le_of_lt (genForestRecordExps_le t hmatch hx) horb))
    (Set.mem_Iio.mpr (lt_of_le_of_lt (genForestRecordExps_le t hmatch hy) horb))
    hxy

/-! ## E. Root-by-root accounting: every request is read off exactly one root

`rd` is whatever per-root readout the consumer uses — the exponent list of a `RootTrace`'s
services, or the `z^i` timestamp list directly.  The two hypotheses say what the two builders of
`GenServedRootTrace` already set: a one-record root reads back its own request, a chained pair
reads back both of its requests, in order.  Nothing else about `rd` is assumed, so the accounting
is stated once and used at `B = ℕ` and at `B = K`. -/

section RootExps

variable {B : Type*}
variable (E : Noun → ComputeTable.FP K) (z α : K)
variable (rd : NTree (GenMemoryRow K) → List B) (val : MemRecordReq → B)

/-- **One compute row's forest reads back exactly that row's requests, in order.**  All five arms
of `genRowMemForest`: the empty row, the single record, the chainable / non-chainable pair, the
three-record row, and the `≥ 4` fallback. -/
theorem genRowMemForest_flatMap_read
    (h1 : ∀ r : MemRecordReq,
      rd (genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) = [val r])
    (h2 : ∀ (r1 r2 : MemRecordReq) (u : NTree (GenMemoryRow K)),
      r1.child = r2.root → genAnnotatedChainedTree E z α lmb [r1, r2] = some u →
        rd u = [val r1, val r2]) :
    ∀ reqs : List MemRecordReq,
      (genRowMemForest E z α lmb reqs).flatMap rd = reqs.map val := by
  have hpair : ∀ r1 r2 : MemRecordReq,
      (genRowMemForest E z α lmb [r1, r2]).flatMap rd = [val r1, val r2] := by
    intro r1 r2
    rw [genRowMemForest]
    by_cases hlink : r1.child = r2.root
    · rw [if_pos hlink]
      cases hc : genAnnotatedChainedTree E z α lmb [r1, r2] with
      | none => simp [h1]
      | some tr => simp [h2 r1 r2 tr hlink hc]
    · rw [if_neg hlink]; simp [h1]
  have htriple : ∀ r1 r2 r3 : MemRecordReq,
      genRowMemForest E z α lmb [r1, r2, r3] =
        genRowMemForest E z α lmb [r1, r2]
          ++ [genAnnotatedRecordTree E z α lmb r3.root r3.child r3.axis r3.recordExp] := by
    intro r1 r2 r3; rfl
  intro reqs
  match reqs with
  | [] => simp [genRowMemForest]
  | [r] => simp [genRowMemForest, h1]
  | [r1, r2] => simpa using hpair r1 r2
  | [r1, r2, r3] =>
      rw [htriple, List.flatMap_append, hpair r1 r2]
      simp [h1]
  | r1 :: r2 :: r3 :: r4 :: rest =>
      rw [genRowMemForest, List.flatMap_map]
      all_goals simp [h1, ← List.map_eq_flatMap]

/-- **The whole generated forest reads back the whole compute tree's requests**, in the DFS
pre-order the builder walks. -/
theorem genMemForest_flatMap_read
    (h1 : ∀ r : MemRecordReq,
      rd (genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) = [val r])
    (h2 : ∀ (r1 r2 : MemRecordReq) (u : NTree (GenMemoryRow K)),
      r1.child = r2.root → genAnnotatedChainedTree E z α lmb [r1, r2] = some u →
        rd u = [val r1, val r2])
    (t : NTree (GenComputeRow K)) :
    (genMemForestFromTree E z α lmb t).flatMap rd =
      (dfsTree t).flatMap (fun n => (extractNodeReqs n.label).map val) := by
  rw [genMemForestFromTree_eq_flatMap, List.flatMap_assoc]
  exact List.flatMap_congr
    (fun n _ => genRowMemForest_flatMap_read E z α rd val h1 h2 (extractNodeReqs n.label))

end RootExps

/-! ## F. The two consumers -/

/-- **Record exponents.**  `rd` reads the raw `recordExp` off each root. -/
theorem genMemForest_recordExps_nodup
    (E : Noun → ComputeTable.FP K) (z α : K)
    (rd : NTree (GenMemoryRow K) → List ℕ)
    (h1 : ∀ r : MemRecordReq,
      rd (genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp) = [r.recordExp])
    (h2 : ∀ (r1 r2 : MemRecordReq) (u : NTree (GenMemoryRow K)),
      r1.child = r2.root → genAnnotatedChainedTree E z α lmb [r1, r2] = some u →
        rd u = [r1.recordExp, r2.recordExp])
    (t : NTree (GenComputeRow K)) (hmatch : treeRequestsMatch (bfsAssign t)) :
    ((genMemForestFromTree E z α lmb (bfsAssign t)).flatMap rd).Nodup := by
  rw [genMemForest_flatMap_read E z α rd MemRecordReq.recordExp h1 h2]
  exact genForestRecordExps_nodup t hmatch

/-- **`timestampPowersNodup`, at the generated forest.**  `rd` reads each root's `z^i` timestamps.  The two hypotheses are the shapes `rootTraceOfRecordTree` and
`rootTraceOfChainedPair` set; `timestampExp_pow_self` converts a `RootTrace`'s
`timestampPowers = exponents.map (α ^ ·)` into this form.

It also
subsumes `α ≠ 0`: `orderOf (0 : K) = 0`, so no natural is below it. -/
theorem genMemForest_timestampPowers_nodup
    (E : Noun → ComputeTable.FP K) (z α : K)
    (rd : NTree (GenMemoryRow K) → List K)
    (h1 : ∀ r : MemRecordReq,
      rd (genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp)
        = [α ^ r.recordExp])
    (h2 : ∀ (r1 r2 : MemRecordReq) (u : NTree (GenMemoryRow K)),
      r1.child = r2.root → genAnnotatedChainedTree E z α lmb [r1, r2] = some u →
        rd u = [α ^ r1.recordExp, α ^ r2.recordExp])
    (t : NTree (GenComputeRow K)) (hmatch : treeRequestsMatch (bfsAssign t))
    (horb : accAt t (bfsRows t).length < orderOf α) :
    ((genMemForestFromTree E z α lmb (bfsAssign t)).flatMap rd).Nodup := by
  have hread := genMemForest_flatMap_read E z α rd (fun r => α ^ r.recordExp) h1 h2 (bfsAssign t)
  have hsplit :
      (dfsTree (bfsAssign t)).flatMap
          (fun n => (extractNodeReqs n.label).map (fun r => α ^ r.recordExp)) =
        (genForestRecordExps (bfsAssign t)).map (fun e => α ^ e) := by
    rw [genForestRecordExps, List.map_flatMap]
    exact List.flatMap_congr (fun n _ => by rw [List.map_map]; rfl)
  rw [hread, hsplit]
  exact genForestTimestampPowers_nodup t α hmatch horb

/-- The bridge from a `RootTrace`'s exponent readout: `timestampPowers` is
`exponents.map (α ^ ·)` and the builders set `exponent = timestampExp α (α ^ e)`, whose `α`-power
is `α ^ e` again. -/
theorem timestampExp_pow_self (α : K) (e : ℕ) :
    α ^ timestampExp α (α ^ e) = α ^ e :=
  (timestampExp_spec (K := K) ⟨e, rfl⟩).symm

/-- **Row-level exponent distinctness at every node**, from the whole tree's `Nodup`.

`RootShape`'s chain disjunct needs `r1.recordExp ≠ r2.recordExp` and the classification takes it as
`NodeExpsNodup`; this supplies it for any accepted program.  `genForestRecordExps` is a DFS
`flatMap`, so each node's block is one of the flatMap's blocks and `nodup_flatMap` projects it. -/
theorem nodeExpsNodup_of_requestsMatch (t : NTree (GenComputeRow K))
    (hmatch : treeRequestsMatch (bfsAssign t)) : NodeExpsNodup (bfsAssign t) := by
  intro n hn
  have h := genForestRecordExps_nodup t hmatch
  rw [genForestRecordExps] at h
  refine (List.nodup_flatMap.1 h).1 n ?_
  have hmem : n ∈ dfsForest [bfsAssign t] :=
    (mem_dfsForest _ n).mpr ⟨_, List.mem_singleton_self _, hn⟩
  simpa [dfsForest] using hmem

/-! ## G. The `RootTrace` readout, and the `Fin cfg.kMem` shape -/

section RootTraceShape

variable {F : Type} [Field F] [Algebra F K]
variable {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}

/-- A one-service root's `timestampPowers` is `[α ^ e]` — the `h1` shape of
`genMemForest_timestampPowers_nodup`.  `rootTraceOfRecordTree` sets `services := [s]` and
`hexp : s.exponent = timestampExp α (α ^ e)`. -/
theorem timestampPowers_of_services_singleton (R : RootTrace cfg exec i)
    (s : Service cfg exec) (e : ℕ) (hs : R.services = [s])
    (hexp : s.exponent = timestampExp cfg.challenges.α (cfg.challenges.α ^ e)) :
    R.timestampPowers = [cfg.challenges.α ^ e] := by
  simp [RootTrace.timestampPowers, RootTrace.exponents, hs, hexp, timestampExp_pow_self]

/-- A chained pair's `timestampPowers` is `[α ^ e₁, α ^ e₂]` — the `h2` shape.
`rootTraceOfChainedPair` sets `services := [s1, s2]`. -/
theorem timestampPowers_of_services_pair (R : RootTrace cfg exec i)
    (s1 s2 : Service cfg exec) (e1 e2 : ℕ) (hs : R.services = [s1, s2])
    (hexp1 : s1.exponent = timestampExp cfg.challenges.α (cfg.challenges.α ^ e1))
    (hexp2 : s2.exponent = timestampExp cfg.challenges.α (cfg.challenges.α ^ e2)) :
    R.timestampPowers = [cfg.challenges.α ^ e1, cfg.challenges.α ^ e2] := by
  simp [RootTrace.timestampPowers, RootTrace.exponents, hs, hexp1, hexp2,
    timestampExp_pow_self]

end RootTraceShape


theorem finRange_flatMap_getElem {A B : Type*} (l : List A) (g : A → List B) :
    ((List.finRange l.length).flatMap fun i => g l[i]) = l.flatMap g := by
  have h : (List.finRange l.length).map (fun i => l[i]) = l := by
    apply List.ext_getElem (by simp)
    intro n h1 h2
    simp
  conv_rhs => rw [← h]
  rw [List.flatMap_map]

end Nock.NockVMROM.Thm54.TraceGen
