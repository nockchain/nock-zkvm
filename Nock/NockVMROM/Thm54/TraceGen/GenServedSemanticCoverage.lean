/-
  Nock/NockVMROM/Thm54/TraceGen/GenServedSemanticCoverage.lean

  **`ExactServedMemoryTrace.semanticCoverage` at the generated carrier.**

  `FF`'s `semanticCoverage_of_servedSupply` + `servedSupply_of_states`
  (`GenServedCoverage.lean`) cut the field to **two** obligations, one per served state, each
  written out of the skeleton's own projections.  `GenServedRequestCoverage.lean` supplies a
  `Service` **in a built root's `services` list** at any `MemRecordReq` of any node.  This module
  is the join, and it has exactly three moving parts:

  * **the row bridge** (§A) — `skeletonRowAt` reads `computeSkeletonRows` at an index while
    `computeRowAt` reads `computeRows` at the same index, and for a generated carrier both lists
    are `(bfsForest [bfsAssign (airReorder t)]).map …`.  So one BFS node supplies the skeleton row
    *and* the compute row, with no encoding and no injectivity;

  * **the record identity** (§B) — `BindComputeRow`'s memory component realizes the row's `k`-th
    record as `enc z` of the skeleton's `k`-th memory record, and `encC_eq` (`Encode.lean:63`)
    makes `enc` and `encC` the same function, so the row's `k`-th record is literally
    `reqRecord (encC z) α ((extractNodeReqs g)[k])`;

  * **the served slot is a record slot** (§C) — `SkeletonOperationalCore.s0_record` /
    `.s9_record` (`BoundSemanticTrace.lean:28`) say the served lookup's root and child *are* the
    skeleton's memory-record root and child, at slot `1` for `.s0` and slot `2` for `.s9`.  That is
    what makes the served tuple's nouns the request's nouns as **nouns**, which is the step an
    argument routed through fingerprints could not take without seed-dependent injectivity.

  `hcore` is not a new premise: `semanticCoverage_of_servedSupply` already takes
  `hop : ∀ s ∈ computeSkeletonRows S, SkeletonOperationalPremises q z s`, and
  `SkeletonOperationalPremises` extends `SkeletonOperationalCore`, so the caller passes a
  projection of what `ofSkeleton` already required.

  **Scope.**  `∀ program accepted by `genComputeSkeleton``, arbitrary field, seed, `α`,
  challenges, coins.  The only arithmetic side condition is `horbα`, which `genRoots` already
  carries (`FI` §1) and which `FU.2`'s `horb_of_window` derives from the window premise the
  assembly holds anyway.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServedRequestCoverage
import Nock.NockVMROM.Thm54.TraceGen.GenServedCoverage

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.Framework.Thm54

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## A. The row bridge

Both lists the two `…At` readers index are maps of the same BFS flatten, so one node answers for
both. -/

section Bridge

variable {F : Type} [Field F] [Algebra F K]

theorem genExactExecution_computeRows_bfsNodes (z α a b c : K)
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem).computeRows
      = (bfsForest [bfsAssign (airReorder t)]).map
          (fun n => setRowCoins a b c (renderNode z α n.label).row) := by
  rw [genExactExecution_computeRows, genComputeRows, bfsRows_renderRows, bfsRows, List.map_map,
    List.map_map]
  rfl

theorem computeSkeletonRows_bfsNodes (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    computeSkeletonRows (genSemanticSkeleton (bfsAssign (airReorder t)) mf)
      = (bfsForest [bfsAssign (airReorder t)]).map (fun n => n.label.skel) := by
  rw [computeSkeletonRows_genSemantic, computeSkeletonRows_genCompute]

/-- **One BFS node answers for both readers.**  At a generated carrier the skeleton row at index
`row` is that node's `skel` and the compute row at index `row` is that node's rendered row. -/
theorem exists_bfsNode_at_row (z α a b c : K)
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)
    {zz : K}
    (binds : BindsAt zz (genSemanticSkeleton (bfsAssign (airReorder t)) mf)
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
        hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem))
    (row : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
      hmempos hcomp hmem).compRows) :
    ∃ n : NTree (GenComputeRow K), InTree (bfsAssign (airReorder t)) n ∧
      skeletonRowAt (genSemanticSkeleton (bfsAssign (airReorder t)) mf)
          (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
            hmempos hcomp hmem) binds row = n.label.skel ∧
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
          hmempos hcomp hmem).computeRowAt row
        = setRowCoins a b c (renderNode z α n.label).row := by
  set exec := genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
    hmempos hcomp hmem with hexec
  have hrows := genExactExecution_computeRows_bfsNodes (F := F) z α a b c chal Ksz orbit horb
    t mf hmempos hcomp hmem
  have hskels := computeSkeletonRows_bfsNodes (K := K) t mf
  have hlt0 : (row : ℕ) < exec.computeRows.length := by
    rw [exec.computeRows_length]; exact row.isLt
  have hltB : (row : ℕ) < (bfsForest [bfsAssign (airReorder t)]).length := by
    have := hlt0
    rw [hrows, List.length_map] at this
    exact this
  refine ⟨(bfsForest [bfsAssign (airReorder t)])[(row : ℕ)]'hltB, ?_, ?_, ?_⟩
  · exact ((mem_bfsForest _ _).mp (List.getElem_mem hltB)).elim
      (fun c hc => by
        obtain ⟨hc1, hc2⟩ := hc
        rw [List.mem_singleton.mp hc1] at hc2
        exact hc2)
  · have hlt1 : (row : ℕ) <
        (computeSkeletonRows (genSemanticSkeleton (bfsAssign (airReorder t)) mf)).length := by
      rw [hskels, List.length_map]; exact hltB
    have hstep := List.getElem_of_eq hskels hlt1
    rw [List.getElem_map] at hstep
    show (computeSkeletonRows (genSemanticSkeleton (bfsAssign (airReorder t)) mf)).get _ = _
    rw [List.get_eq_getElem]
    exact hstep
  · have hstep := List.getElem_of_eq hrows hlt0
    rw [List.getElem_map] at hstep
    show exec.computeRows.get _ = _
    rw [List.get_eq_getElem]
    exact hstep

end Bridge

/-! ## B. The record identity

The row's `k`-th emitted record is exactly the record its `k`-th `MemRecordReq` commits. -/

/-- `BindComputeRow` at a node of the assigned, AIR-ordered tree of an accepted program.  This is
`ComputeNodesOK`'s per-node component, which `exists_service_of_memRecordReq` takes inline. -/
theorem genBindComputeRow (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    {u : NTree (GenComputeRow K)} (hu : InTree (bfsAssign (airReorder t)) u) :
    BindComputeRow z u.label.skel (renderNode z α u.label).row := by
  have hOK := genComputeSkeleton_airReorder_computeNodes_OK (p := (t, result)) z α h
  have hnode : InTree (mapNTree GenComputeRow.node
      (renderRows z α (bfsAssign (airReorder t))))
      (mapNTree GenComputeRow.node (mapNTree (renderNode z α) u)) := by
    rw [renderRows_eq_mapNTree]
    exact mapNTree_inTree _ (mapNTree_inTree _ hu)
  obtain ⟨-, -, hbind, -⟩ := hOK _ hnode
  rw [mapNTree_label, mapNTree_label] at hbind
  simpa only [GenComputeRow.node_skel, GenComputeRow.node_row, renderNode_op1_skel] using hbind

/-- **The rendered row's `k`-th record, from the skeleton's `k`-th memory record.**
`encC_eq` (`Encode.lean:63`) makes `enc` and `encC` the same function, and
`renderNode_computeMemRec_ts` (`GenServedRoots.lean:174`) supplies the timestamp. -/
theorem renderNode_computeMemRec_eq (z α : K) (g : GenComputeRow K)
    (hbind : BindComputeRow z g.skel (renderNode z α g).row)
    (k : ℕ) (h3 : k < 3) (hc : k < Nock.Framework.recordCount g.skel.state) :
    computeMemRec (renderNode z α g).row.2.2.1 ⟨k, h3⟩
      = ⟨encC z (g.skel.memoryRecord ⟨k, h3⟩ hc).root,
         encC z (g.skel.memoryRecord ⟨k, h3⟩ hc).child,
         ((g.skel.memoryRecord ⟨k, h3⟩ hc).axis : K),
         α ^ getRecordExp g.stamp k⟩ := by
  have hmr := hbind.2.2.2.2.2.2.2.2 ⟨k, h3⟩
  rw [dif_pos hc] at hmr
  have hreal := realizesMemRec_of_bindMemRec hmr
  have hts : (computeMemRec (renderNode z α g).row.2.2.1 ⟨k, h3⟩).ts
      = α ^ getRecordExp g.stamp k := by
    simpa using renderNode_computeMemRec_ts z α g ⟨k, h3⟩ hc
  refine ComputeTable.MemRec.ext ?_ ?_ ?_ ?_
  · exact hreal.root_realizes.trans (encC_eq z _).symm
  · exact hreal.child_realizes.trans (encC_eq z _).symm
  · exact hreal.axis_realizes
  · exact hts

/-- **The `k`-th request of a row, with its four coordinates read off the skeleton.**  §A's
`requests_getElem_triple` and `extractNodeReqs_getElem` (`GenServiceSupply.lean`) combined: the
`k`-th extracted request *is* the skeleton's `k`-th memory record, stamped with the row's `k`-th
record exponent. -/
theorem extractNodeReqs_getElem_skel (g : GenComputeRow K) (hmatch : requestsMatchMemory g)
    (k : ℕ) (h3 : k < 3) (hc : k < Nock.Framework.recordCount g.skel.state) :
    ∃ hk : k < (extractNodeReqs g).length,
      (extractNodeReqs g)[k]'hk =
        { root := (g.skel.memoryRecord ⟨k, h3⟩ hc).root,
          child := (g.skel.memoryRecord ⟨k, h3⟩ hc).child,
          axis := (g.skel.memoryRecord ⟨k, h3⟩ hc).axis,
          recordExp := getRecordExp g.stamp k } := by
  have hlen := requestsMatch_length g hmatch
  have hkq : k < g.requests.length := by rw [hlen]; exact hc
  have hk : k < (extractNodeReqs g).length := by rw [extractNodeReqs_length]; exact hkq
  refine ⟨hk, ?_⟩
  obtain ⟨h3', hc', hroot, hchild, haxis⟩ := requests_getElem_triple g hmatch k hkq
  rw [extractNodeReqs_getElem g k hkq]
  rw [hroot, hchild, haxis]

/-! ## C. The per-slot supply at the generated carrier

One statement covering every record slot of every state; `.s0`'s slot `1` and `.s9`'s slot `2` are
the two `servedTuplesOf` reads. -/

section Slot

variable {F : Type} [Field F] [Algebra F K]

/-- **A `Service` in a built root's `services`, agreeing with the row's `k`-th record slot.**

`exists_service_mem_genRoots` supplies the membership at the *request*; this identifies the
request's four coordinates with the skeleton's `k`-th memory record and the row's `k`-th emitted
record.  Every state and every active slot, no axis fixed -/
theorem genServedRecordSlot (z α a b c : K)
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
    (kf : Fin 3) (hc : (kf : ℕ) < Nock.Framework.recordCount n.label.skel.state) :
    ∃ (i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem).kMem)
      (s : ServedMemoryTrace.Service
        (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
          (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem)
        (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
          (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem)),
      s ∈ (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
          hmempos hcomp hmem i).services ∧
        s.record = computeMemRec (renderNode z α n.label).row.2.2.1 kf ∧
        s.root = (n.label.skel.memoryRecord kf hc).root ∧
        s.child = (n.label.skel.memoryRecord kf hc).child ∧
        s.axis = (n.label.skel.memoryRecord kf hc).axis := by
  have hmatch : requestsMatchMemory n.label :=
    genComputeSkeleton_air_requestsMatch h n hn
  obtain ⟨hk, hreq⟩ := extractNodeReqs_getElem_skel n.label hmatch (kf : ℕ) kf.isLt hc
  have hr : (extractNodeReqs n.label)[(kf : ℕ)]'hk ∈ extractNodeReqs n.label :=
    List.getElem_mem hk
  obtain ⟨i, s, hsmem, hsroot, hschild, hsaxis, -, hsrec⟩ :=
    exists_service_mem_genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
      hmempos hcomp hmem hn hr
  have hbind : BindComputeRow z n.label.skel (renderNode z α n.label).row :=
    genBindComputeRow z α h hn
  have hrowrec := renderNode_computeMemRec_eq z α n.label hbind (kf : ℕ) kf.isLt hc
  refine ⟨i, s, hsmem, ?_, ?_, ?_, ?_⟩
  · rw [hsrec, hrowrec, hreq]
  · rw [hsroot, hreq]
  · rw [hschild, hreq]
  · rw [hsaxis, hreq]

end Slot

/-! ## D. The two served states, and `ServedSupply`

`SkeletonOperationalCore` says the served lookup's root and child *are* the skeleton memory
record's root and child — `s0_record` at slot `1` and `s9_record` at slot `2`.  So the two obligations `servedSupply_of_states` leaves are §C at those
two slots. -/

section Supply

variable {F : Type} [Field F] [Algebra F K]

/-- **`FF`'s `ServedSupply`, discharged at the generated carrier.**

`hcore` is a projection of the `hop` that `ofSkeleton` already requires
(`SkeletonOperationalPremises extends SkeletonOperationalCore`), so this introduces no premise
beyond `horbα` -/
theorem genServedSupply {q Λ : ℕ} (z α a b c : K)
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
    {zz : K}
    (binds : BindsAt zz
      (genSemanticSkeleton (bfsAssign (airReorder t)) (genMemoryForest z α chal.lam inp t))
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem))
    (hcore : ∀ s ∈ computeSkeletonRows
      (genSemanticSkeleton (bfsAssign (airReorder t)) (genMemoryForest z α chal.lam inp t)),
      SkeletonOperationalCore s) :
    ServedSupply (q := q) (Λ := Λ)
      (genSemanticSkeleton (bfsAssign (airReorder t)) (genMemoryForest z α chal.lam inp t))
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem) binds
      (genRoots (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
        hmempos hcomp hmem) := by
  refine servedSupply_of_states _ _ _ _ ?_ ?_
  · -- `.s0`: slot 1, the paper
    intro row hs0
    obtain ⟨n, hn, hskel, hrow⟩ := exists_bfsNode_at_row (F := F) z α a b c chal Ksz orbit horb
      t (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem binds row
    have hcore' : SkeletonOperationalCore n.label.skel := by
      rw [← hskel]
      exact hcore _ (List.get_mem _ _)
    have hstate : n.label.skel.state = .s0 := by rw [← hskel]; exact hs0
    have hc : ((1 : Fin 3) : ℕ) < Nock.Framework.recordCount n.label.skel.state := by
      rw [hstate]; decide
    obtain ⟨hmrroot, hmrchild⟩ := hcore'.s0_record hstate
    obtain ⟨i, s, hsmem, hsrec, hsroot, hschild, hsaxis⟩ :=
      genServedRecordSlot (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
        hmempos hcomp hmem hn (1 : Fin 3) hc
    refine ⟨i, s, hsmem, ?_, ?_, ?_, ?_⟩
    · rw [hsrec, hrow, setRowCoins_pub]
    · rw [hsroot, hskel, hmrroot]
    · rw [hschild, hskel, hmrchild]
    · rw [hsaxis, hskel, P8Census.skeletonMemoryAxis, dif_pos (hskel ▸ hc)]
  · -- `.s9`: slot 2, the paper
    intro row hs9
    obtain ⟨n, hn, hskel, hrow⟩ := exists_bfsNode_at_row (F := F) z α a b c chal Ksz orbit horb
      t (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem binds row
    have hcore' : SkeletonOperationalCore n.label.skel := by
      rw [← hskel]
      exact hcore _ (List.get_mem _ _)
    have hstate : n.label.skel.state = .s9 := by rw [← hskel]; exact hs9
    have hc : ((2 : Fin 3) : ℕ) < Nock.Framework.recordCount n.label.skel.state := by
      rw [hstate]; decide
    obtain ⟨hmrroot, hmrchild⟩ := hcore'.s9_record hstate
    obtain ⟨i, s, hsmem, hsrec, hsroot, hschild, hsaxis⟩ :=
      genServedRecordSlot (F := F) z α a b c chal hz hα Ksz orbit horb inp h horbα
        hmempos hcomp hmem hn (2 : Fin 3) hc
    refine ⟨i, s, hsmem, ?_, ?_, ?_, ?_⟩
    · rw [hsrec, hrow, setRowCoins_pub]
    · rw [hsroot, hskel, hmrroot]
    · rw [hschild, hskel, hmrchild]
    · rw [hsaxis, hskel, P8Census.skeletonMemoryAxis, dif_pos (hskel ▸ hc)]

end Supply

/-! ## E. `semanticCoverage`, at the generated carrier

`genOperationalCore` (`GenSemanticDataParts.lean:85`) supplies `hcore` **unconditionally** at any
accepted program, so §D's hypothesis is discharged and not carried.  What remains in the signature
below is `genRows`' own argument list plus `hα` and `horbα`, both of which `genRoots` already
needs. -/

section Field

variable {F : Type} [Field F] [Algebra F K] [Fintype K] [DecidableEq K]

/-- **`ExactServedMemoryTrace.semanticCoverage` (`ServedMemoryTrace.lean:616`) for the rows
`genSemanticData` commits, with `roots := genRoots`.**

Every served lookup of every compute row of the generated execution is matched — on record, root,
child and axis — by a `Service` that is a **member of some built root's `services` list**. -/
theorem genSemanticCoverage {q Λ : ℕ} (z α : K) (hz : z ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hzc : chal.z = z) (hαc : chal.α = α)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (horbα : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α)
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)))
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))) :
    ∀ row : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).compRows,
      ∀ lookup ∈ (genRows (F := F) z α hz a b c chal hzc Ksz orbit horb h hΛ hconf
          hmempos hcomp hmem hb hq hchar haxis hbad hout row).needs.served,
        ∃ (i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem)
          (s : ServedMemoryTrace.Service
            (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
              (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)
            (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
              (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)),
          s ∈ (genRoots (F := F) z α a b c chal hzc hαc Ksz orbit horb (memInputs z) h horbα
              hmempos hcomp hmem i).services ∧
            s.record = lookup.record ∧ s.root = lookup.root ∧
              s.child = lookup.child ∧ s.axis = lookup.axis :=
  semanticCoverage_of_servedSupply
    (genSemanticSkeleton (bfsAssign (airReorder t)) (genMemoryForest z α chal.lam (memInputs z) t))
    (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)
    (genBindsAt_threaded (F := F) z α (memInputs z) chal hzc Ksz orbit horb a b c h
      hmempos hcomp hmem)
    (genSkeletonP8Census hΛ h hconf _)
    hb
    (genComparisonBounded hb hq hchar haxis)
    hbad
    (genOperationalPremises hchar hz h _ hout)
    (genRoots (F := F) z α a b c chal hzc hαc Ksz orbit horb (memInputs z) h horbα
      hmempos hcomp hmem)
    (genServedSupply (F := F) (q := q) (Λ := Λ) z α a b c chal hzc hαc Ksz orbit horb
      (memInputs z) h horbα hmempos hcomp hmem
      (binds := genBindsAt_threaded (F := F) z α (memInputs z) chal hzc Ksz orbit horb a b c h
        hmempos hcomp hmem)
      (genOperationalCore h _))

end Field

/-! ## F. The same statement at `genSemanticData`'s own `rows`

`genSemanticData.rows` **is** `genRows` (`GenSemanticData.lean:158`), so this is §E read at the
object the assembly will consume — i.e. literally the `semanticCoverage` field's type with
`D := genSemanticData …` and `roots := genRoots …`.  `hα` is `hinp`'s `α` component, exactly as
`genSemanticData` already takes `hzc` to be its `z` component. -/

section AtSemanticData

variable {F : Type} [Field F] [Algebra F K] [Fintype K] [DecidableEq K]

/-- **The `semanticCoverage` field, at `genSemanticData` and `genRoots`.** -/
theorem genSemanticData_semanticCoverage {q Λ : ℕ} (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0)
    (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hseed : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)))
    (hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))) :
    ∀ row : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).compRows,
      ∀ lookup ∈ ((genSemanticData (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hb hq hchar
          haxis hbad hout hfirst).rows row).needs.served,
        ∃ (i : Fin (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem)
          (s : ServedMemoryTrace.Service
            (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
              (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)
            (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
              (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)),
          s ∈ (genRoots (F := F) z α a b c chal (congrArg ComputeTable.Inputs.z hinp)
              (congrArg ComputeTable.Inputs.α hinp) Ksz orbit horb (memInputs z) h
              (horb_of_window hB hwin) hmempos hcomp hmem i).services ∧
            s.record = lookup.record ∧ s.root = lookup.root ∧
              s.child = lookup.child ∧ s.axis = lookup.axis :=
  genSemanticCoverage (F := F) z α hz a b c chal (congrArg ComputeTable.Inputs.z hinp)
    (congrArg ComputeTable.Inputs.α hinp) Ksz orbit horb h (horb_of_window hB hwin)
    hΛ hconf hmempos hcomp hmem hb hq hchar haxis hbad hout

end AtSemanticData

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecution_computeRows_bfsNodes
#print axioms Nock.NockVMROM.Thm54.TraceGen.computeSkeletonRows_bfsNodes
#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_bfsNode_at_row
#print axioms Nock.NockVMROM.Thm54.TraceGen.genBindComputeRow
#print axioms Nock.NockVMROM.Thm54.TraceGen.renderNode_computeMemRec_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.extractNodeReqs_getElem_skel
#print axioms Nock.NockVMROM.Thm54.TraceGen.genServedRecordSlot
#print axioms Nock.NockVMROM.Thm54.TraceGen.genServedSupply
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemanticCoverage
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemanticData_semanticCoverage
