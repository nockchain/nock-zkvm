/-
  Nock/NockVMROM/Thm54/TraceGen/GenSemanticDataParts.lean

  This module does the first list.  Nothing here proves anything new; each theorem names a
  composite that both live configurations were re-deriving, or that nobody had written down.

  `genThreadedMemoryNodesOK` closes that with `MemoryNodesOK_threadGenForest`, which
  `GenGenericMemory.lean:120` already pointed at.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenBindsAt
import Nock.NockVMROM.Thm54.TraceGen.GenTierAHonestData

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.Framework.Thm54

variable {F K : Type} [Field F] [Field K] [Algebra F K]

variable {lmb : K}

/-! ## The threaded memory forest — the `DZ` defect, fixed

`genBindsAt` is usable at a live carrier only if its `MemoryNodesOK` hypothesis is dischargeable on
the **threaded** forest.  It is. -/

/-- The committed memory forest of a generated program: generated, then threaded. -/
noncomputable def genMemoryForest (z α lmb : K) (inp : MemoryTable.Inputs K)
    (t : NTree (GenComputeRow K)) : List (NTree (GenMemoryRow K)) :=
  threadGenForest inp 0 (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t)))

/-- Threading rewrites only `ipre`/`icur` (`setAcc`), so any pub property stable under `setAcc`
survives it, at every BFS label. -/
theorem threadGenRows_pub {P : MemoryTable.Pub K → Prop}
    (hP : ∀ p a b, P p → P (setAcc p a b)) (inp : MemoryTable.Inputs K) :
    ∀ (acc : K) (gs : List (GenMemoryRow K)), (∀ g ∈ gs, P g.row.2.2) →
      ∀ g ∈ threadGenRows inp acc gs, P g.row.2.2
  | _, [], _, g, hg => by cases hg
  | acc, q :: qs, hall, g, hg => by
      rw [threadGenRows_cons] at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · rw [threadGenRow_snd]
        exact hP _ _ _ (hall q List.mem_cons_self)
      · exact threadGenRows_pub hP inp _ qs
          (fun r hr => hall r (List.mem_cons_of_mem _ hr)) g hg

theorem threadGenForest_bfs_pub {P : MemoryTable.Pub K → Prop}
    (hP : ∀ p a b, P p → P (setAcc p a b)) (inp : MemoryTable.Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K)))
    (H : ∀ t ∈ bfsForest forest, P t.label.row.2.2) :
    ∀ t ∈ bfsForest (threadGenForest inp acc forest), P t.label.row.2.2 := by
  intro t ht
  have hlab : t.label ∈ (bfsForest (threadGenForest inp acc forest)).map NTree.label :=
    List.mem_map.mpr ⟨t, ht, rfl⟩
  rw [threadGenForest_bfs_labels] at hlab
  exact threadGenRows_pub hP inp acc _
    (fun g hg => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      exact H u hu)
    t.label hlab

/-- This replaces the retired `C' = 1` invariant: the executed rows are
the row encode of these (`genExactExecution = (genExactExecutionA …).encodeMem`), which writes
`(T, C', λ)`. -/
theorem genMemoryForest_bfs_aBearing (z α : K) (inp : MemoryTable.Inputs K)
    (t : NTree (GenComputeRow K)) :
    ∀ n ∈ bfsForest (genMemoryForest z α lmb inp t),
      n.label.row.2.2.cprime? = none ∧
        (n.label.row.2.2.st ≠ MemoryTable.MState.halt → n.label.row.2.2.lambda = lmb) :=
  threadGenForest_bfs_pub
    (P := fun p => p.cprime? = none ∧ (p.st ≠ MemoryTable.MState.halt → p.lambda = lmb))
    (fun _ _ _ h => h) inp 0 _
    (fun u hu =>
      ⟨forest_bfs_cprime _
          (fun v hv => genMemForestFromTree_allC (encC z) z α lmb (bfsAssign (airReorder t)) v hv)
          u hu,
        forest_bfs_lambda _
          (fun v hv => genMemForestFromTree_allC (encC z) z α lmb (bfsAssign (airReorder t)) v hv)
          u hu⟩)

/-- **`MemoryNodesOK` on the threaded forest**, for any accepted program.

`genComputeSkeleton_memForest_OK_air` gives it on the unthreaded forest and
`MemoryNodesOK_threadGenForest` transports it through the threading — the composition
`GenGenericMemory.lean:120` names in prose and nothing had written down. -/
theorem genThreadedMemoryNodesOK (z α : K) (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u ∈ genMemoryForest z α lmb inp t, MemoryNodesOK z α (mapNTree GenMemoryRow.node u) :=
  MemoryNodesOK_threadGenForest z α inp 0 _
    (genComputeSkeleton_memForest_OK_air z α h)

/-- **`BindsAt` at the forest a configuration actually commits.**  `DZ`'s `genBindsAt` with its
memory hypothesis discharged rather than assumed. -/
theorem genBindsAt_threaded (z α : K) (inp : MemoryTable.Inputs K)
    (chal : ChallengeVector K) (hz : chal.z = z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h) (a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h) :
    BindsAt z (genSemanticSkeleton (bfsAssign (airReorder t)) (genMemoryForest z α chal.lam inp t))
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam inp t) hmempos hcomp hmem) :=
  genBindsAt z α chal hz Ksz orbit horb a b c h _ (genThreadedMemoryNodesOK z α inp h)
    hmempos hcomp hmem

/-! ## `SkeletonOperationalCore` — `ofSkeleton`'s `hop`, core half

Both live configurations' proofs are three lines differing
in the tree name; this is that composite, named once. -/

/-- **`SkeletonOperationalCore` at every committed row of any accepted program.** -/
theorem genOperationalCore
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (mf : List (NTree (GenMemoryRow K))) :
    ∀ s ∈ computeSkeletonRows (genSemanticSkeleton (bfsAssign (airReorder t)) mf),
      SkeletonOperationalCore s :=
  bfsAssign_operationalCore (airReorder t) mf
    (fun g hg => (genComputeSkeleton_bfsRows_census_air h g hg).2.1)
    (fun g hg => (genComputeSkeleton_bfsRows_census_air h g hg).1)

/-! ## `CombinedBoundedBy` — `Data.combinedBounded`, and `ofSkeleton`'s `hcmp`

Its only input beyond `skeletonBounded` is the OP0/OP9 axis-range condition, which the
commitment check does **not** cover — axes are `ℕ`, not committed nouns — so it is carried here as
an explicit hypothesis and is a new declared precondition of `nockCompiles`. -/

/-- The OP0/OP9 axis-range measurement.  Not implied by `CanonicalCommitmentCheck`. -/
def SkeletonAxisRange (q : ℕ) (S : SemanticSkeleton) : Prop :=
  ∀ s ∈ computeSkeletonRows S,
    (s.state = .s0 → P8Census.skeletonMemoryAxis s 1 < q) ∧
      (s.state = .s9 → P8Census.skeletonMemoryAxis s 2 < q)

/-- **`Data.combinedBounded` for any accepted program**, from the commitment check plus the
axis-range measurement. -/
theorem genCombinedBounded {q : ℕ} {t : NTree (GenComputeRow K)}
    {mf : List (NTree (GenMemoryRow K))}
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t)) mf).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t)) mf)) :
    ProductionP8Containment.CombinedBoundedBy K q
      (genSemanticSkeleton (bfsAssign (airReorder t)) mf) :=
  GenericHonestData.combinedBounded_of_skeletonBounded_and_axis_range
    hb hq hchar haxis

/-! ## `ofSkeleton`'s remaining arguments

`EA` listed three: `C`, `hop` and `hgood`.  `C` is a projection; `hop` is now complete; `hgood` is a
counted seed condition **independent of** `GenDyckBadSeed`'s `SeedGood` — a different object built
from different data, not a disjoint *set* of seeds (one `z` may perfectly well fail both) — and is
left to the caller. -/

/-- **`ofSkeleton`'s `C` is a field projection**, not a conversion: `CombinedSkeletonCensus` *is*
a `SkeletonP8Census` paired with an edge census (`EdgeComparisonCensus.lean:165`). -/
theorem genSkeletonP8Census {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hconf : TraceConfined Λ (airReorder t))
    (mf : List (NTree (GenMemoryRow K))) :
    BoundSemanticTrace.SkeletonP8Census K
      (genSemanticSkeleton (bfsAssign (airReorder t)) mf) Λ :=
  (genComputeSkeleton_census_gen hΛ h hconf mf).p8

section SizeWindow

variable [Fintype K] [DecidableEq K]

/-- `SkeletonSizeWindowPremises` at every committed row, from the seed lying outside the counted
failure set.  The bound on that set is `sizeWindowFailureSeeds_card_le`, which consumes
`genComputeSkeleton_sizeWindowBound_gen` — so this is the *second* counted seed condition, and it is
paid for by the same `Λ` measurement as `census`. -/
theorem genSizeWindowPremises {z : K} (hz : z ≠ 0)
    (t : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t)) mf)) :
    ∀ s ∈ computeSkeletonRows (genSemanticSkeleton (bfsAssign (airReorder t)) mf),
      BoundSemanticTrace.SkeletonSizeWindowPremises z s :=
  fun s hs =>
    SizeWindowCounting.windows_of_not_mem_sizeWindowFailureSeeds _ hz hout s hs

theorem genOperationalPremises {q : ℕ} {z : K} (hq : q = ringChar K) (hz : z ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (mf : List (NTree (GenMemoryRow K)))
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t)) mf)) :
    ∀ s ∈ computeSkeletonRows (genSemanticSkeleton (bfsAssign (airReorder t)) mf),
      BoundSemanticTrace.SkeletonOperationalPremises q z s :=
  fun s hs =>
    operationalPremises_of_core_windows hq
      (genOperationalCore h mf s hs)
      (genSizeWindowPremises hz t mf hout s hs)

end SizeWindow

/-! ## `rowAccepted` — `EA` item 3

Unblocked by `EF`: `ComputeRowAccepted` pins `row.2.1 = cfg.challenges.computeInputs`, which a
coin-fixed carrier could not meet for a configuration wanting `c = 1`. -/

/-- The BFS rows of a rendered tree are the rendered BFS rows. -/
theorem bfsRows_renderRows (z α : K) (v : NTree (GenComputeRow K)) :
    bfsRows (renderRows z α v) = (bfsRows v).map (renderNode z α) := by
  rw [renderRows_eq_mapNTree]
  unfold bfsRows
  rw [show [mapNTree (renderNode z α) v] = [v].map (mapNTree (renderNode z α)) from rfl,
    bfsForest_mapNTree, List.map_map, List.map_map]
  exact List.map_congr_left fun t _ => mapNTree_label _ t

/-- **`ComputeRowsAccepted` for any accepted program.**

The three conjuncts: state agreement from `renderNode_state` and `renderNode_pub_state`; the input
vector from `setRowCoins_renderNode_inputs` against the declared challenges; and `V_comp` from the
counted seed condition `SeedGood` (`GenDyckBadSeed`), transported through the coin overwrite by
`Vcomp_setRowCoins`. -/
theorem genComputeRowsAccepted (z α : K) (hz : z ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hgood : SeedGood z t)
    (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
      hmempos hcomp hmem).ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff,
    genExactExecution_computeRows chal Ksz orbit horb a b c]
  intro row hrow
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hrow
  rw [genComputeRows, bfsRows_renderRows] at hg
  obtain ⟨gl, hgl, rfl⟩ := List.mem_map.mp hg
  unfold bfsRows at hgl
  rw [bfsAssign_bfsForest_labels] at hgl
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hgl
  refine ⟨?_, ?_, ?_⟩
  · show (renderNode z α _).row.1 = (renderNode z α _).row.2.2.1.state
    rw [renderNode_state, renderNode_pub_state]
  · have hch : (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf
        hmempos hcomp hmem).challenges = chal := rfl
    rw [hch, hinp]
    exact setRowCoins_renderNode_inputs z α a b c _
  · exact (Vcomp_setRowCoins a b c _).mpr
      (genComputeSkeleton_airReorder_bfsLabelAt_Vcomp_of_seedGood z α hz h hgood hi)

/-- **`rowAccepted` — the `ExactExecutionSemanticData` field**, at every index. -/
theorem genRowAccepted (z α : K) (hz : z ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hgood : SeedGood z t)
    (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    ∀ i, ExactExecution.ComputeRowAccepted
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t) mf hmempos hcomp hmem)
      ((genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem).computeRowAt i) :=
  fun i => ExactExecution.computeRowAt_accepted
    (genComputeRowsAccepted z α hz a b c chal hinp Ksz orbit horb h hgood mf
      hmempos hcomp hmem) i

/-! ## `compute_topology` — `EA` item 5, compute half

`assigned_airReorder_coins_binding` (`GenAirOrderBinding.lean:345`) is stated at
`mapNTree (setRowCoins a b c ∘ GenComputeRow.row ∘ renderNode z α) (bfsAssign (airReorder p.1))`
— i.e. **already at the coin-set tree**, which is exactly the carrier's committed compute tree after
`EF`. The generator track had anticipated the coin parameter; the carrier had not. -/

/-- The carrier's committed compute tree, as the coin-set binding lemma spells it. -/
theorem genExactExecution_computeTree_eq (z α a b c : K) (t : NTree (GenComputeRow K)) :
    mapNTree (fun g : GenComputeRow K => setRowCoins a b c g.row) (genComputeRows z α t) =
      mapNTree ((setRowCoins a b c) ∘ GenComputeRow.row ∘ renderNode z α)
        (bfsAssign (airReorder t)) := by
  rw [genComputeRows, renderRows_eq_mapNTree, mapNTree_comp]
  rfl

/-- **`ComputeExactTopology` for any accepted program.** -/
theorem genComputeExactTopology (z α : K) (hz : z ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hgood : SeedGood z t)
    (mf : List (NTree (GenMemoryRow K)))
    (hmempos : 0 < (bfsForest mf).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h) :
    ComputeExactTopology
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t) mf
        hmempos hcomp hmem) := by
  refine computeExactTopology_of_rowsAccepted_and_binding
    (genComputeRowsAccepted z α hz a b c chal hinp Ksz orbit horb h hgood mf
      hmempos hcomp hmem) ?_
  show ∀ u ∈ bfsForest
      [mapNTree (fun g : GenComputeRow K => setRowCoins a b c g.row) (genComputeRows z α t)],
    RawComputeTopologyBinding u
  rw [genExactExecution_computeTree_eq]
  exact assigned_airReorder_coins_binding (p := (t, result)) z α a b c h

/-! ## Memory-row state agreement, generically

`MemoryRowAccepted` has three parts: state agreement, `inputs = memoryInputs`, and `Vmem`.  The
first falls straight out of `MemoryNodesOK`, which is already generic — the
configurations' `assigned_bfs_state_air` (`GenTierAMemAccept.lean:117`) is six lines and the only
config-specific thing in it is the tree.  The other two are `EH`'s brick and are **not** here. -/

/-- State agreement on the generated (unthreaded) memory forest, from `MemoryNodesOK`. -/
theorem genAssignedMemory_state (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u ∈ bfsForest (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t))),
      u.label.row.1 = u.label.row.2.2.st := by
  intro u hu
  obtain ⟨w, hw, hin⟩ := (mem_bfsForest _ u).mp hu
  have hOK := genComputeSkeleton_memForest_OK_air z α h w hw
    (mapNTree GenMemoryRow.node u) (mapNTree_inTree _ hin)
  have hb := hOK.2.2.1
  simpa [mapNTree_label, GenMemoryRow.node_row] using hb.1.trans hb.2.2.1.symm

/-- The same on the threaded forest a configuration commits. -/
theorem genThreadedMemory_state (z α : K) (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u ∈ bfsForest (genMemoryForest z α lmb inp t),
      u.label.row.1 = u.label.row.2.2.st :=
  threadGenForest_state_agree inp 0 _ (genAssignedMemory_state z α h)

/-! ## `MemoryRowsAccepted`, generically

`EI` predicted two inductions over `genRowMemForest`'s request list.  **They already exist** —
`genRowMemForest_all_inputs` (`GenMatmulMemAccept.lean:221`) and `genRowMemForest_wf_eqBlk`
(`:553`), both quantified over an arbitrary `rs : List MemRecordReq` — so this is composition after
all. -/

/-- Row inputs on the generated (unthreaded) memory forest.

Holds for **any** tree — the acceptance hypothesis is not used, and is kept only so the signature
matches its siblings. -/
theorem genAssignedMemory_inputs (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (_h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u ∈ bfsForest (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t))),
      u.label.row.2.1 = memInputs z := by
  intro u hu
  obtain ⟨w, hw, hin⟩ := (mem_bfsForest _ u).mp hu
  exact genMemForestFromTree_of_rowInputs z α _
    (fun n _ => genRowMemForest_all_inputs (encC z) z α _) w hw u hin

/-- `eqBlk` on the generated forest, from the generator's own request well-formedness. -/
theorem genAssignedMemory_eqBlk (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u ∈ bfsForest (genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t))),
      eqBlkE lmb (memInputs z) u.label.row.2.2 := by
  have hwf : treeRequestsWF (airReorder t) :=
    treeRequestsWF_airReorder (genComputeSkeleton_tree_requests_wf h)
  intro u hu
  obtain ⟨w, hw, hin⟩ := (mem_bfsForest _ u).mp hu
  exact genMemForestFromTree_of_rowEqBlk z α hz htwo _
    (fun n hn => by
      intro x hx y hy
      exact genRowMemForest_wf_eqBlk (lmb := lmb) z α hz htwo _
        (fun r hr =>
          ⟨bfsAssign_extract_requests_wf (airReorder t) hwf n hn r hr,
            Or.inr (bfsAssign_extract_requests_slot (airReorder t) hwf n hn r hr)⟩)
        x hx y hy)
    w hw u hin

theorem genThreadedMemory_inputs (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u ∈ bfsForest (genMemoryForest z α lmb (memInputs z) t),
      u.label.row.2.1 = memInputs z :=
  threadGenForest_inputs (memInputs z) 0 _ (genAssignedMemory_inputs z α h)

theorem genThreadedMemory_Vmem (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u ∈ bfsForest (genMemoryForest z α lmb (memInputs z) t),
      VmemE lmb (memInputs z) u.label.row.2.2 :=
  threadGenForest_Vmem (memInputs z) 0 _ (genAssignedMemory_eqBlk z α hz htwo h)

/-- `memInputs` pins the LogUp pole offset to zero.  Stated so the restriction inside
`genMemoryRowsAccepted`'s hypothesis is a compiled fact rather than a remark. -/
theorem memoryInputs_forces_beta_zero (chal : ChallengeVector K) (z : K)
    (hmi : chal.memoryInputs = memInputs z) : chal.β = 0 := by
  have := congrArg MemoryTable.Inputs.β hmi
  simpa [ChallengeVector.memoryInputs, memInputs] using this

/-- ...and the record-RLC challenge likewise. -/
theorem memoryInputs_forces_gamma_zero (chal : ChallengeVector K) (z : K)
    (hmi : chal.memoryInputs = memInputs z) : chal.γ = 0 := by
  have := congrArg MemoryTable.Inputs.γ hmi
  simpa [ChallengeVector.memoryInputs, memInputs] using this

/-- **`MemoryRowsAccepted` for any accepted program — at memory challenges `(z, 0, 0)`.**

**Scope, which the hypothesis hides.**  `hmi : chal.memoryInputs = memInputs z` looks like a naming
convention but is a *restriction*: `memInputs z = ⟨z, 0, 0⟩` (`Gen.lean:2954`), so it pins
`chal.β = 0` **and** `chal.γ = 0` — see `memoryInputs_forces_beta_zero` /
`_gamma_zero` below, which put that in the build rather than in prose.

This is **not** an artefact of this theorem: the generator bakes `memInputs z` into every memory row
it emits, so any configuration consuming generated memory rows inherits it, and both live ones do.

The compute side is parametric in its coins (`EF`); the memory side is not, and the asymmetry is
visible in the two signatures. Recorded as a carried restriction, not fixed here. -/
theorem genMemoryRowsAccepted (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h) :
    (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff,
    genExactExecution_memoryRows chal Ksz orbit horb a b c]
  intro row hrow
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hrow
  have hst := genThreadedMemory_state z α (memInputs z) h n hn
  have hinp := genThreadedMemory_inputs z α h n hn
  have hv := genThreadedMemory_Vmem z α hz htwo h n hn
  have hch : (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).challenges.memoryInputs
      = memInputs z := by
    show chal.memoryInputs = memInputs z
    exact hmi
  -- The executed row is the row encode of the generated a-bearing row.
  have hpub := encodeRow_pub (lmb := chal.lam) n.label.row hst
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpub, encPub_st]; exact hst
  · rw [hch, encodeRow_inputs]; exact hinp
  · rw [hpub, encodeRow_inputs, hinp]; exact hv
  · rw [hpub, encPub_lambda]; rfl

/-! ## `memory_topology` — `EA` item 5, memory half

Now unblocked: `memoryExactTopology_of_rowsAccepted_and_binding` wanted `MemoryRowsAccepted`, which
`genMemoryRowsAccepted` supplies.  The binding side was already a chain of generic lemmas —
`genRowMemForest_binding` (`GenMatmulTopology.lean:754`, total over the request list),
`genMemForestFromTree_of_rowBinding`, `threadGenForest_bfs_binding`. -/

/-- The row encode keeps the topology binding (it touches neither the state nor the cells). -/
theorem rawMemoryTopologyBinding_encode
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K))
    (h : RawMemoryTopologyBinding t) :
    RawMemoryTopologyBinding (mapNTree (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb) t)
        := by
  have hcell : ∀ (lbl : MemoryTable.MState × MemoryTable.DTmem K) (i : Fin 2),
      MemoryTable.memCell (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb lbl) i =
        MemoryTable.memCell lbl i := by
    intro lbl i
    fin_cases i <;> (unfold SemanticTimestampStrategy.MemoryRowTemplate.encodeRow; split <;> rfl)
  cases t with
  | node lbl cs =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · simpa [mapNTree, NTree.label, NTree.children] using h1
    · intro i hi
      have := h2 i (by
        simpa [mapNTree, NTree.label, SemanticTimestampStrategy.MemoryRowTemplate.encodeRow] using
            hi)
      simp only [mapNTree, NTree.label] at this ⊢
      rw [hcell, ← this]
      simp [NTree.childLabel, NTree.childOpt, List.getElem?_map, Option.map_map,
        Function.comp_def]

theorem genThreadedMemory_binding (z α : K) (inp : MemoryTable.Inputs K)
    (t : NTree (GenComputeRow K)) :
    ∀ u ∈ bfsForest ((genMemoryForest z α lmb inp t).map (mapNTree GenMemoryRow.row)),
      RawMemoryTopologyBinding u :=
  threadGenForest_bfs_binding inp 0 _
    (by
      intro u hu
      rw [bfsForest_mapNTree] at hu
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
      obtain ⟨w, hw, hin⟩ := (mem_bfsForest _ v).mp hv
      exact genMemForestFromTree_of_rowBinding (encC z) z α _
        (fun n _ => genRowMemForest_binding (encC z) z α _) w hw v hin)

/-- The topology binding on the **executed** forest (the row encode of the threaded forest). -/
theorem genThreadedMemory_bindingE (z α : K) (inp : MemoryTable.Inputs K)
    (t : NTree (GenComputeRow K)) :
    ∀ u ∈ bfsForest (((genMemoryForest z α lmb inp t).map (mapNTree GenMemoryRow.row)).map
        (mapNTree (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow lmb))),
      RawMemoryTopologyBinding u := by
  intro u hu
  rw [bfsForest_mapNTree] at hu
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
  exact rawMemoryTopologyBinding_encode v (genThreadedMemory_binding z α inp t v hv)

/-- **`MemoryExactTopology` for any accepted program.** -/
theorem genMemoryExactTopology (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h) :
    MemoryExactTopology
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem) :=
  memoryExactTopology_of_rowsAccepted_and_binding
    (genMemoryRowsAccepted z α hz htwo a b c chal hmi Ksz orbit horb h hmempos hcomp hmem)
    (genThreadedMemory_bindingE z α (memInputs z) t)

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genThreadedMemoryNodesOK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genBindsAt_threaded
#print axioms Nock.NockVMROM.Thm54.TraceGen.genOperationalCore
#print axioms Nock.NockVMROM.Thm54.TraceGen.genCombinedBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkeletonP8Census
#print axioms Nock.NockVMROM.Thm54.TraceGen.genOperationalPremises
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeRowsAccepted
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRowAccepted
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeExactTopology
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAssignedMemory_state
#print axioms Nock.NockVMROM.Thm54.TraceGen.genThreadedMemory_state
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemoryRowsAccepted
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemoryExactTopology
