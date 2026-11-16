/-
  Nock/NockVMROM/Thm54/TraceGen/GenForestTimestampNodup.lean

  **`ExactServedMemoryTrace.timestampPowersNodup`, filled at the generated carrier.**

  The field (`ServedMemoryTrace.lean:610`) is

  ```
  ((List.finRange cfg.kMem).flatMap (fun i => (roots i).timestampPowers)).Nodup
  ```

  and everything it needs was in the tree; this module is the composition, not new mathematics.

  * `genRoots_timestampPowers` (`GenServedRoots.lean` §C.2/§C.3) pins, per forest index, **which
    tree the root sits at** and the exact `timestampPowers` — `[α ^ e]` at a one-record tree,
    `[α ^ e₁, α ^ e₂]` at a chained pair.
  * so the per-index relation is an **equality**, `(genRoots … i).timestampPowers = servedTs F[i]`,
    not merely a permutation: no `Perm` lifting is used anywhere below, and
    `GenForestIndexRange.lean`'s `perm_flatMap_pointwise` is not needed.
  * `finRange_flatMap_getElem` (`GenMemForestOrder.lean:344`) then turns the field's `Fin cfg.kMem`
    flatMap into `F.flatMap servedTs`, over the *unthreaded* classified forest `F`, because
    `cfg.kMem` counts `threadGenForest inp 0 F` and `threadGenForest_length` says that is `F.length`.

  **Premises.**  **No new premise is introduced here.**
-/
import Nock.NockVMROM.Thm54.TraceGen.GenChainedServedGen

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.Framework.Thm54

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## A. A `Fin n`-indexed flatMap over a list of known length

`finRange_flatMap_getElem` (`GenMemForestOrder.lean:344`) is stated at `n = l.length`; the field's
index type is `Fin cfg.kMem`, and `cfg.kMem` is only *equal* to the forest length, not syntactically
it.  This is that lemma with the length equation carried. -/

/-- `(finRange n).flatMap g = l.flatMap f` whenever `n = l.length` and `g` reads `f` off the
element at each index. -/
theorem finRange_flatMap_of_getElem {A B : Type*} {n : ℕ} (l : List A) (hn : l.length = n)
    (g : Fin n → List B) (f : A → List B)
    (hg : ∀ (i : Fin n) (hi : (i : ℕ) < l.length), g i = f l[(i : ℕ)]) :
    (List.finRange n).flatMap g = l.flatMap f := by
  subst hn
  rw [← finRange_flatMap_getElem l f]
  exact List.flatMap_congr (fun i _ => hg i i.isLt)

/-! ## B. The per-index readout is an equality

Both arms of `genRoots_timestampPowers` name the tree at the index, and §D of
`GenChainedServedGen.lean` computes `servedTs` at exactly those two tree shapes.  So the two lists
agree **on the nose**; nothing here crosses a permutation. -/

section Gen

variable {F : Type} [Field F] [Algebra F K]

/-- **The chosen root's `timestampPowers` is the `servedTs` readout of the tree it sits at.**

An equality, per index. -/
theorem genRoots_timestampPowers_eq_servedTs (z α a b c : K)
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
    (i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem) :
    (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
        hmempos hcomp hmem i).timestampPowers
      = servedTs ((genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))[(i : ℕ)]'
          (genRoot_index_lt (F := F) z α inp t chal Ksz orbit horb hmempos hcomp hmem i)) := by
  rcases genRoots_timestampPowers (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
      hmempos hcomp hmem i with ⟨r, hu, hts⟩ | ⟨r1, r2, ht, hts⟩
  · rw [hts, hu, servedTs_recordTree]
  · rw [hts, servedTs, genAnnotatedChainedTree_pair_servedGen (encC z) z α r1 r2 ht]
    rfl

/-- The config's root count is the *unthreaded* classified forest's length.

`genExactConfig.kMem` is the committed forest's length, and the committed forest is
`threadGenForest inp 0` of the classified one (`genMemoryForest_eq_thread`), which
`threadGenForest_length` says has the same length. -/
theorem genMemForestFromTree_length_eq_kMem (z α : K)
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (inp : MemoryTable.Inputs K) (t : NTree (GenComputeRow K))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h) :
    (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t))).length
      = (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
          (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem := by
  rw [genExactConfig_kMem, genMemoryForest_eq_thread, threadGenForest_length]

/-- **The aggregate readout, as one list over the classified forest.** -/
theorem genRoots_forestTimestampPowers_eq (z α a b c : K)
    (chal : ChallengeVector K) (hz : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h) :
    ((List.finRange (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem).flatMap
      (fun i => (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
        hmempos hcomp hmem i).timestampPowers))
      = (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t))).flatMap servedTs :=
  finRange_flatMap_of_getElem
    (genMemForestFromTree (encC z) z α chal.lam (bfsAssign (airReorder t)))
    (genMemForestFromTree_length_eq_kMem (F := F) z α chal Ksz orbit horb inp t
      hmempos hcomp hmem)
    _ servedTs
    (fun i _ => genRoots_timestampPowers_eq_servedTs (F := F) z α a b c chal hz hα
      Ksz orbit horb inp h horbα hmempos hcomp hmem i)

/-- **`ExactServedMemoryTrace.timestampPowersNodup`, at the generated carrier.**

The paper's global timestamp uniqueness across the whole memory forest, for
any program `genComputeSkeleton` accepts, at the roots `genRoots` builds.

Premises are exactly `genRoots`'s own: the program's acceptance and `horbα`.  Nothing new is
assumed and nothing is left as a residual — this is the field, not a reduction of it. -/
theorem genRoots_timestampPowersNodup (z α a b c : K)
    (chal : ChallengeVector K) (hz : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h) :
    ((List.finRange (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem).flatMap
      (fun i => (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
        hmempos hcomp hmem i).timestampPowers)).Nodup := by
  rw [genRoots_forestTimestampPowers_eq (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
    hmempos hcomp hmem]
  exact genMemForest_servedTs_nodup (encC z) z α (airReorder t)
    (genComputeSkeleton_air_requestsMatch h) horbα

/-! ## C. Non-vacuity of the aggregate list

The `Nodup` is not `Nodup []`, nor is it `Nodup` of a one-element list.  So the `Nodup` is a statement about `N` genuinely distinct field elements, and `N ≥ 1`
always. -/

/-- **The aggregate timestamp list, identified.**  It is `α ^ ·` of the forest's record exponents,
in DFS order.  Everything in this section is read off this one equation. -/
theorem genRoots_forestTimestampPowers_eq_recordExps (z α a b c : K)
    (chal : ChallengeVector K) (hz : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h) :
    ((List.finRange (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem).flatMap
      (fun i => (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
        hmempos hcomp hmem i).timestampPowers))
      = (genForestRecordExps (bfsAssign (airReorder t))).map (fun e => α ^ e) := by
  rw [genRoots_forestTimestampPowers_eq (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
    hmempos hcomp hmem]
  rw [genMemForest_flatMap_read (encC z) z α servedTs (fun r => α ^ r.recordExp)
    (servedTs_recordTree (encC z) z α)
    (fun r1 r2 u hlink hu => servedTs_chainedPair (encC z) z α r1 r2 hlink hu)
    (bfsAssign (airReorder t))]
  rw [genForestRecordExps, List.map_flatMap]
  exact List.flatMap_congr (fun n _ => by rw [List.map_map]; rfl)

/-- **The aggregate timestamp list is `[α ^ 1, …, α ^ N]` up to order**, with `N` the trace's
record count.  This is the strongest non-vacuity statement available: not just "the list is long",
but which field elements it contains. -/
theorem genRoots_forestTimestampPowers_perm_range (z α a b c : K)
    (chal : ChallengeVector K) (hz : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h) :
    ((List.finRange (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem).flatMap
      (fun i => (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
        hmempos hcomp hmem i).timestampPowers)).Perm
      (((List.range (accAt (airReorder t) (bfsRows (airReorder t)).length)).map
        (fun i => i + 1)).map (fun e => α ^ e)) := by
  rw [genRoots_forestTimestampPowers_eq_recordExps (F := F) z α a b c chal hz hα
    Ksz orbit horb inp h horbα hmempos hcomp hmem]
  exact (genForestRecordExps_perm_range (airReorder t)
    (genComputeSkeleton_air_requestsMatch h)).map _

/-- **The aggregate timestamp list has one entry per emitted memory record.**

`accAt … |bfsRows …|` is the trace's record count, so the `Nodup` above is a statement about that
many genuinely distinct field elements. -/
theorem genRoots_forestTimestampPowers_length (z α a b c : K)
    (chal : ChallengeVector K) (hz : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h) :
    ((List.finRange (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem).flatMap
      (fun i => (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
        hmempos hcomp hmem i).timestampPowers)).length
      = accAt (airReorder t) (bfsRows (airReorder t)).length := by
  rw [genRoots_forestTimestampPowers_eq_recordExps (F := F) z α a b c chal hz hα
    Ksz orbit horb inp h horbα hmempos hcomp hmem, List.length_map,
    genForestRecordExps_length _ (genComputeSkeleton_air_requestsMatch h)]

/-- **And it is never empty.**  Every accepted program emits at least one memory record
(`accAt_length_pos`), so the field is not `Nodup []`. -/
theorem genRoots_forestTimestampPowers_ne_nil (z α a b c : K)
    (chal : ChallengeVector K) (hz : chal.z = z) (hα : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h) :
    ((List.finRange (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem).flatMap
      (fun i => (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
        hmempos hcomp hmem i).timestampPowers)) ≠ [] := by
  have hlen := genRoots_forestTimestampPowers_length (F := F) z α a b c chal hz hα
    Ksz orbit horb inp h horbα hmempos hcomp hmem
  have hpos := accAt_length_pos (airReorder t) (bfsRows_length_pos (airReorder t))
  intro hnil
  rw [hnil, List.length_nil] at hlen
  omega

end Gen

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.finRange_flatMap_of_getElem
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRoots_timestampPowers_eq_servedTs
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_length_eq_kMem
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRoots_forestTimestampPowers_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRoots_timestampPowersNodup
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRoots_forestTimestampPowers_eq_recordExps
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRoots_forestTimestampPowers_perm_range
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRoots_forestTimestampPowers_length
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRoots_forestTimestampPowers_ne_nil
