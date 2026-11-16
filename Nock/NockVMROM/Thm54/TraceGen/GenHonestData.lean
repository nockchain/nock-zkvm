/-
  Nock/NockVMROM/Thm54/TraceGen/GenHonestData.lean

  **`HonestCommitment.Data`'s sixteen fields at the generated carrier, for any accepted program.**

  `genBuildable` (`GenExactExecution.lean:171`) is the generic
  `BuildableNockExecution`; this module builds the honest prover's seed-free commitment
  `Data (genBuildable …)` over it, for **every program `genComputeSkeleton` accepts**.

  **The survey result, stated exactly.**  §G listed eight fields as "already generic" and four as
  per-configuration with generic cores.  Measured against the proofs rather than the signatures:

  * *Twelve* of the sixteen have program-generic suppliers already in the tree.  §G's eight
    (`slotSemantics`, `recordEquations`, `memoryOK`, `census`, `sizeWindowBound`, `skeletonBounded`,
    `computeOK`, `combinedBounded`) plus `compute_rows`, `memory_rows`, `root_line_exponent` and
    `q_eq_ringChar` — the four §G called per-configuration.  Nothing here is new mathematics.
  * The older claim here — that the only supplier was `genCommitment_skeletonBounded`
    (`GenCommitmentBridge.lean:120`), undischarged — was stale.  It costs nothing *new*, because `genSemanticData`
    (`GenSemanticData.lean:119`) already carries the same `hb` — so the `Data` assembly adds no
    premise the carrier's `sd` was not already assuming.
  * `computeOK` is the field §G's list gets wrong in the *pessimistic* direction: it reads as though
    it needed the per-fixture `dotComputeNodesAir_OK`, while
    `genComputeSkeleton_airReorder_computeNodes_OK` (`GenAirOrderBinding.lean:371`) has been
    unconditional-at-any-accepted-program all along, and `computeNodesOK_setRowCoins`
    (`GenBindsAt.lean:87`) carries it across the carrier's coin overwrite.

  **What the premise list is.**  No new premise, no carrier field, no `∀ E`.

  **Scope.**  `∀ program accepted by genComputeSkeleton`, at arbitrary field, seed, `α`, coins and
  challenge vector — subject to `hinp`/`hmi` pinning the challenge vector to the generator's own
  inputs, which for the memory side forces `β = γ = 0` (`memoryInputs_forces_beta_zero`,
  `GenSemanticDataParts.lean`).  It says nothing about executions that are not generated.

  **Not claimed.**  `Inputs`, `buildFullPackage`, the capstone and the mandatory
  `claimedResult = result` conjunct are untouched.  `hnodup` and `hbal` are arguments, not
  discharges: `genBuildable` wants them and only `hbal` is composed (`FF`, `genBuildable_hbal`).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticDataParts

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.Framework.Thm54

variable {F K : Type} [Field F] [Field K] [Algebra F K]

variable {lmb : K}

/-! ## The two committed node objects

`Data` commits node **trees**, not rows: the skeleton, the committed Nat timestamp exponents, and
the execution row.  The generator already emits all three per row (`GenComputeRow`,
`GenMemoryRow`), so both objects are a projection of the carrier's own trees — with one wrinkle on
the compute side.  `genExactExecution`'s compute tree is coin-overwritten
(`setRowCoins a b c`, `EF`), so the committed node must carry the same overwrite or `compute_rows`
is false.  `computeNodesOK_setRowCoins` (`GenBindsAt.lean:87`) is what makes that free. -/

/-- **The committed compute node tree of a generated program.**  Rendered, BFS-assigned,
AIR-ordered, then coin-overwritten to match the carrier's execution row. -/
noncomputable def genComputeNodes (z α a b c : K) (t : NTree (GenComputeRow K)) :
    NTree (ComputeNode K) :=
  mapNTree (fun n : ComputeNode K => { n with row := setRowCoins a b c n.row })
    (mapNTree GenComputeRow.node (genComputeRows z α t))

/-- **The committed memory node forest of a generated program.**  The threaded forest a
configuration actually commits (`genMemoryForest`, `GenSemanticDataParts.lean`). -/
noncomputable def genMemoryNodes (z α lmb : K) (inp : MemoryTable.Inputs K)
    (t : NTree (GenComputeRow K)) : List (NTree (MemoryNode K)) :=
  (genMemoryForest z α lmb inp t).map (mapNTree GenMemoryRow.node)

/-! ## `compute_rows` and `memory_rows` — the identification with the carrier -/

/-- **`Data.compute_rows` at the generated carrier.**  `mapNTree_coinNode_row` does the whole job:
the committed node tree's row projection *is* the carrier's coin-set compute tree. -/
theorem genComputeNodes_rows (z α a b c : K) (t : NTree (GenComputeRow K)) :
    mapNTree ComputeNode.row (genComputeNodes z α a b c t) =
      mapNTree (fun g : GenComputeRow K => setRowCoins a b c g.row) (genComputeRows z α t) :=
  mapNTree_coinNode_row a b c (genComputeRows z α t)

/-- **`Data.memory_rows` at the generated carrier.** -/
theorem genMemoryNodes_rows (z α : K) (inp : MemoryTable.Inputs K)
    (t : NTree (GenComputeRow K)) :
    (genMemoryNodes z α lmb inp t).map (mapNTree MemoryNode.row) =
      (genMemoryForest z α lmb inp t).map (mapNTree GenMemoryRow.row) := by
  rw [genMemoryNodes, List.map_map]
  exact List.map_congr_left fun u _ => mapNTree_memNode_row u

/-! ## `computeOK` and `memoryOK` -/

/-- **`Data.computeOK` for every program the generator accepts.**

`genComputeSkeleton_airReorder_computeNodes_OK` (`GenAirOrderBinding.lean:371`) is unconditional at
any accepted program; `computeNodesOK_setRowCoins` carries it across the coin overwrite.  Neither
`BindComputeRow` nor `ComputeTimestampSpecializesAt` reads a coin column, which is why the second
step is free. -/
theorem genComputeNodes_OK (z α a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ComputeNodesOK z α (genComputeNodes z α a b c t) :=
  computeNodesOK_setRowCoins a b c
    (genComputeSkeleton_airReorder_computeNodes_OK (p := (t, result)) z α h)

/-- **`Data.memoryOK` for every program the generator accepts**, on the threaded forest. -/
theorem genMemoryNodes_OK (z α : K) (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u ∈ genMemoryNodes z α lmb inp t, MemoryNodesOK z α u := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
  exact genThreadedMemoryNodesOK z α inp h v hv

/-! the paper makes the line-number column a *prover* step, so this is a commitment condition and
never something recovered from acceptance.  At the generated carrier it is one equation on the BFS
accumulator: the root sits at 0-based BFS position `0` and `accAt t 0 = 0` by definition
(`BFSAssign.lean:44`).  Nothing about the program enters, and the coin overwrite does not touch the
stamp. -/

/-- **`Data.root_line_exponent` for any generated tree**, unconditionally — no acceptance
hypothesis. -/
theorem genComputeNodes_root_line_exponent (z α a b c : K) (t : NTree (GenComputeRow K)) :
    (genComputeNodes z α a b c t).label.stamp.lnPrevExponent = 0 := by
  have hpos : (1 : ℕ) - 1 < (bfsRows (airReorder t)).length := by
    have := bfsForest_singleton_length_pos (airReorder t)
    simpa [bfsRows] using this
  have hstamp :
      (genComputeNodes z α a b c t).label.stamp = (bfsLabelAt (airReorder t) 1).stamp := by
    simp only [genComputeNodes, genComputeRows, mapNTree_label, renderRows_eq_mapNTree,
      GenComputeRow.node, renderNode_op1_stamp, bfsAssign_label]
  rw [hstamp, bfsLabelAt_lnPrev (airReorder t) 1 hpos]
  rfl

/-- **`Data.root_line_origin` for any generated tree**, unconditionally and at every `α`
(`α = 0` included): the root row's `ln_prev` is `α ^ 0 = 1` (`renderNode_ln_prev`,
`genComputeNodes_root_line_exponent`; `setRowCoins` does not touch `ln_prev`). -/
theorem genComputeNodes_root_line_origin (z α a b c : K) (t : NTree (GenComputeRow K)) :
    (genComputeNodes z α a b c t).label.row.2.2.1.ln_prev = 1 := by
  have hpos : (1 : ℕ) - 1 < (bfsRows (airReorder t)).length := by
    have := bfsForest_singleton_length_pos (airReorder t)
    simpa [bfsRows] using this
  have hrow :
      (genComputeNodes z α a b c t).label.row =
        setRowCoins a b c (renderNode z α (bfsLabelAt (airReorder t) 1)).row := by
    simp only [genComputeNodes, genComputeRows, mapNTree_label, renderRows_eq_mapNTree,
      GenComputeRow.node, bfsAssign_label]
  have hstamp := genComputeNodes_root_line_exponent z α a b c t
  have hstamp' : (bfsLabelAt (airReorder t) 1).stamp.lnPrevExponent = 0 := by
    rw [bfsLabelAt_lnPrev (airReorder t) 1 hpos]; rfl
  rw [hrow]
  show (renderNode z α (bfsLabelAt (airReorder t) 1)).row.2.2.1.ln_prev = 1
  rw [renderNode_ln_prev, hstamp', pow_zero]

/-! ## The committed skeleton is the generator's own skeleton

Every remaining field is a statement about `skeletonOfNodes computeNodes memoryNodes`, while every
generic supplier is stated at `genSemanticSkeleton (bfsAssign (airReorder t)) mf`.  This is the
bridge, and it is the coin-invariance of the skeleton projection plus two `mapNTree` collapses. -/

/-- **The committed skeleton of a generated program is `genSemanticSkeleton`.**  The generic
version of `DotConfig769.skeletonOfNodes_eq` (`GenTierAHonestData.lean:250`), with the
configuration removed and the coin overwrite absorbed. -/
theorem genSkeletonOfNodes_eq (z α a b c : K) (inp : MemoryTable.Inputs K)
    (t : NTree (GenComputeRow K)) :
    skeletonOfNodes (genComputeNodes z α a b c t) (genMemoryNodes z α lmb inp t) =
      genSemanticSkeleton (bfsAssign (airReorder t)) (genMemoryForest z α lmb inp t) := by
  refine congrArg₂ SemanticSkeleton.mk ?_ ?_
  · show mapNTree ComputeNode.skel (genComputeNodes z α a b c t) = _
    rw [genComputeNodes, mapNTree_coinNode_skel]
    exact (genSemanticSkeleton_computeTree (mf := genMemoryForest z α lmb inp t) z α t).symm
  · show (genMemoryNodes z α lmb inp t).map (mapNTree MemoryNode.skel) = _
    rw [genMemoryNodes, List.map_map]
    exact List.map_congr_left fun u _ => mapNTree_memNode_skel u

/-! ## The six seed-free skeleton obligations

Each is the generic supplier transported along `genSkeletonOfNodes_eq`.  `census` and
`sizeWindowBound` consume the leaf-window measurement `hΛ`/`hconf`; `skeletonBounded` is assumed
(`EP.1` — see the module docstring); `combinedBounded` is `skeletonBounded` plus the axis-range
measurement. -/

section Skeleton

variable (z α a b c : K) (inp : MemoryTable.Inputs K)

/-- **`Data.slotSemantics` at the generated carrier**. -/
theorem genData_slotSemantics
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (genComputeNodes z α a b c t) (genMemoryNodes z α lmb inp t)),
      SkeletonSlotSemantics s := by
  rw [genSkeletonOfNodes_eq]
  exact bfsAssign_computeSkeletonRows_slotSemantics (airReorder t) _
    (fun g hg => (genComputeSkeleton_bfsRows_census_air h g hg).1)

/-- **`Data.recordEquations` at the generated carrier**. -/
theorem genData_recordEquations
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (genComputeNodes z α a b c t) (genMemoryNodes z α lmb inp t)),
      SkeletonRecordEquations s := by
  rw [genSkeletonOfNodes_eq]
  exact bfsAssign_computeSkeletonRows_recordEquations (airReorder t) _
    (fun g hg => (genComputeSkeleton_bfsRows_census_air h g hg).2.1)

/-- **`Data.census` at the generated carrier**, from the leaf-window measurement. -/
theorem genData_census {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hconf : TraceConfined Λ (airReorder t)) :
    EdgeComparisonCensus.CombinedSkeletonCensus K
      (skeletonOfNodes (genComputeNodes z α a b c t) (genMemoryNodes z α lmb inp t)) Λ := by
  rw [genSkeletonOfNodes_eq]
  exact genComputeSkeleton_census_gen hΛ h hconf _

/-- **`Data.sizeWindowBound` at the generated carrier**, from the same measurement. -/
theorem genData_sizeWindowBound {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hconf : TraceConfined Λ (airReorder t)) :
    SizeWindowCounting.SizeWindowNounsBoundedBy
      (skeletonOfNodes (genComputeNodes z α a b c t) (genMemoryNodes z α lmb inp t)) Λ := by
  rw [genSkeletonOfNodes_eq]
  exact genComputeSkeleton_sizeWindowBound_gen hΛ h hconf _

/-- **`Data.skeletonBounded` at the generated carrier — a restatement of an assumed premise.**

There is no generic derivation of this: `genCommitment_skeletonBounded`
(`GenCommitmentBridge.lean:120`) wants `CanonicalCommitmentCheck`, which nothing in the tree
discharges at a generated trace.  `hb` is exactly the hypothesis
`genSemanticData` already takes, so assembling `Data` adds nothing. -/
theorem genData_skeletonBounded {q : ℕ} (t : NTree (GenComputeRow K))
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α lmb inp t)).BoundedBy q) :
    (skeletonOfNodes (genComputeNodes z α a b c t) (genMemoryNodes z α lmb inp t)).BoundedBy q := by
  rw [genSkeletonOfNodes_eq]
  exact hb

/-- **`Data.combinedBounded` at the generated carrier**, from `skeletonBounded` plus the OP0/OP9
axis-range measurement. -/
theorem genData_combinedBounded {q : ℕ} (t : NTree (GenComputeRow K))
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α lmb inp t)).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q
      (genSemanticSkeleton (bfsAssign (airReorder t)) (genMemoryForest z α lmb inp t))) :
    ProductionP8Containment.CombinedBoundedBy K q
      (skeletonOfNodes (genComputeNodes z α a b c t) (genMemoryNodes z α lmb inp t)) := by
  rw [genSkeletonOfNodes_eq]
  exact genCombinedBounded hb hq hchar haxis

end Skeleton

/-! ## The carrier's projections

`genBuildable` is a structure literal, so these are `rfl`. -/

section Carrier

variable (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
  (a b c : K) (ct : NTree (GenComputeRow K)) (mf : List (NTree (GenMemoryRow K)))
  (hmempos : 0 < (bfsForest mf).length)
  (hcomp : (bfsForest [ct]).length ≤ 2 ^ orbit.h)
  (hmem : (bfsForest mf).length ≤ 2 ^ orbit.h)

theorem genExactConfig_challenges :
    (genExactConfig (F := F) chal Ksz orbit horb ct mf hmempos hcomp hmem).challenges = chal :=
  rfl

theorem genExactExecution_computeTree :
    (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem).computeTree =
      mapNTree (fun g : GenComputeRow K => setRowCoins a b c g.row) ct :=
  rfl

theorem genExactExecutionA_memoryForest :
    (genExactExecutionA (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem).memoryForest =
      mf.map (mapNTree GenMemoryRow.row) :=
  rfl

/-- The executed memory forest is its row encode. -/
theorem genExactExecution_memoryForest :
    (genExactExecution (F := F) chal Ksz orbit horb a b c ct mf hmempos hcomp hmem).memoryForest =
      (mf.map (mapNTree GenMemoryRow.row)).map
        (mapNTree (SemanticTimestampStrategy.MemoryRowTemplate.encodeRow chal.lam)) :=
  rfl

end Carrier

/-! ## The two challenge-vector projections

`Data.computeOK` / `.memoryOK` are stated at `E.cfg.challenges.z` / `.α`, while every generic
supplier is stated at the seed and timestamp base the generator rendered with.  `hinp` — the
hypothesis `genSemanticData` already carries — identifies them. -/

/-- **`Data.computeOK` at the carrier's own challenge projections.** -/
theorem genData_computeOK (z α a b c : K) (chal : ChallengeVector K)
    (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ComputeNodesOK chal.z chal.α (genComputeNodes z α a b c t) := by
  have hz : chal.z = z := congrArg ComputeTable.Inputs.z hinp
  have hα : chal.α = α := congrArg ComputeTable.Inputs.α hinp
  rw [hz, hα]
  exact genComputeNodes_OK z α a b c h

/-- **`Data.memoryOK` at the carrier's own challenge projections.** -/
theorem genData_memoryOK (z α a b c : K) (chal : ChallengeVector K)
    (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (inp : MemoryTable.Inputs K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u ∈ genMemoryNodes z α chal.lam inp t, MemoryNodesOK chal.z chal.α u := by
  have hz : chal.z = z := congrArg ComputeTable.Inputs.z hinp
  have hα : chal.α = α := congrArg ComputeTable.Inputs.α hinp
  rw [hz, hα]
  exact genMemoryNodes_OK z α inp h

/-! ## `Data` at the generated carrier

Sixteen fields, none assumed as a `Data` field.  Every premise below is one `genSemanticData`
(`GenSemanticData.lean:119`) already takes, so a configuration that can build the carrier's `sd`
can build this commitment with no further measurement:

| field | source | generic? |
|---|---|---|
| `computeNodes`, `memoryNodes` | `genComputeNodes`, `genMemoryNodes` | definitions |
| `compute_rows`, `memory_rows` | `genComputeNodes_rows`, `genMemoryNodes_rows` | ✅ |
| `computeOK` | `genComputeSkeleton_airReorder_computeNodes_OK` + coin transport | ✅ |
| `memoryOK` | `genThreadedMemoryNodesOK` | ✅ |
| `root_line_exponent` | `bfsLabelAt_lnPrev` + `accAt` at `0` | ✅ unconditional |
| `nounSizeBound`, `Λ` | `Λ` | choices |
| `slotSemantics`, `recordEquations` | `genComputeSkeleton_bfsRows_census_air` | ✅ |
| `census`, `sizeWindowBound` | leaf-window measurement `hΛ`/`hconf` | ✅ from the measurement |
| `skeletonBounded` | **`hb`, assumed** — no generic derivation exists (`EP.1`) | ❌ premise |
| `combinedBounded` | `hb` + `haxis` (`SkeletonAxisRange`, also assumed) | ❌ premise-fed |

`hnodup` and `hbal` are arguments of the **carrier**, not of the commitment: `genBuildable` wants
them and this module does not discharge either. -/

/-- **`HonestCommitment.Data` at the generated carrier, for any program the generator accepts.**

The honest prover's seed-free commitment over `genBuildable`.  No field is
fabricated and none is left as a `Data`-level hypothesis; the two premises that are not derived —
`hb` and `haxis` — appear as named arguments, and both are already in `genSemanticData`'s list. -/
noncomputable def genData
    (z α a b c : K) (chal : ChallengeVector K)
    (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (q : ℕ) (hq1 : 1 < q) (Λ : ℕ) (hΛ : 1 ≤ Λ)
    (hconf : TraceConfined Λ (airReorder t))
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q)
    (hq11 : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t)))
    (sd : SemanticTrace.ExactExecutionSemanticData q Λ
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem))
    (mt : ServedMemoryTrace.ExactServedMemoryTrace q Λ
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem) sd
      (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem))
    (hnodup : (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).derivedRequestIO.Nodup)
    (hbal : RowLayout.RecordCountBalanced
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem))
    (hqrc : q ≤ ringChar K) (h2 : (2 : K) ≠ 0) (hKsz : Ksz < ringChar K)
    (hprog : (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).derivedRequestIO.length
        + 1 ≤ 2 ^ orbit.h)
    (hresp : (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).derivedResponseIO.length
        + 1 ≤ 2 ^ orbit.h) :
    Data (genBuildable (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem q hq1 Λ sd mt hnodup hbal
      hqrc h2 hKsz hprog hresp) where
  computeNodes := genComputeNodes z α a b c t
  memoryNodes := genMemoryNodes z α chal.lam (memInputs z) t
  compute_rows := genComputeNodes_rows z α a b c t
  memory_rows := genMemoryNodes_rows z α (memInputs z) t
  computeOK := genData_computeOK z α a b c chal hinp h
  memoryOK := genData_memoryOK z α a b c chal hinp (memInputs z) h
  root_line_exponent := genComputeNodes_root_line_exponent z α a b c t
  root_line_origin := genComputeNodes_root_line_origin z α a b c t
  nounSizeBound := Λ
  Λ := Λ
  slotSemantics := genData_slotSemantics z α a b c (memInputs z) h
  recordEquations := genData_recordEquations z α a b c (memInputs z) h
  census := genData_census z α a b c (memInputs z) hΛ h hconf
  sizeWindowBound := genData_sizeWindowBound z α a b c (memInputs z) hΛ h hconf
  q_eq_ringChar := hchar
  skeletonBounded := genData_skeletonBounded z α a b c (memInputs z) t hb
  combinedBounded := genData_combinedBounded z α a b c (memInputs z) t hb hq11 hchar haxis

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeNodes_rows
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemoryNodes_rows
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeNodes_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemoryNodes_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeNodes_root_line_exponent
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeNodes_root_line_origin
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkeletonOfNodes_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.genData_slotSemantics
#print axioms Nock.NockVMROM.Thm54.TraceGen.genData_recordEquations
#print axioms Nock.NockVMROM.Thm54.TraceGen.genData_census
#print axioms Nock.NockVMROM.Thm54.TraceGen.genData_sizeWindowBound
#print axioms Nock.NockVMROM.Thm54.TraceGen.genData_skeletonBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.genData_combinedBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.genData_computeOK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genData_memoryOK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genData
