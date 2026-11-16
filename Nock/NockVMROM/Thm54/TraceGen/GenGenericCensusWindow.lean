/-
  Nock/NockVMROM/Thm54/TraceGen/GenGenericCensusWindow.lean

  **`Data.census` for every program the generator accepts, from one decidable measurement.**

  `census_of_leafWindow` (`CensusExtraClosure.lean:1592`) is §G's reduction: on any semantic
  skeleton, `1 ≤ Λ` plus `RowCellIdentities` plus `RowLeafWindow` at every committed compute row
  gives `CombinedSkeletonCensus` outright — no seed, no fixture, no carrier field.  Until now the
  reduction was only ever *fed* at written fixture scope (`SizeWindowBoundOp6.named_census`, three
  rows at `Op6Execution`, `Λ = 7`), because neither input was available generically.

  Both now are:

  * `RowCellIdentities` is the fourth conjunct of `NodeCmpKind`, which
    `genComputeSkeleton_inTree_cmpKind_unconditional` (`GenGenericCensus.lean:140`) proves at every
    node of any accepted program with **no** hypothesis.  Transported to the AIR ordering by
    `cmpKind_of_labelsFrom` (`GenAirTransport.lean:59`) — which is what that theorem was for.
  * `RowLeafWindow` is `leafWindow_of_traceConfined` (`GenTraceConfined.lean`) applied to the
    **decidable** `TraceConfined` premise.

  So `census` at an arbitrary generated program reduces to a `Nat` measurement — discharged at a
  concrete program by a row-list equation plus kernel `Nat.ble` reduction, **not** by `decide`, which
  does not reduce at the noncomputable released carriers (`GenTraceConfined`'s docstring says why).
  That measurement is not an artefact of this formalization: it is the
  `λ ≤ Λ` membership condition of `NockVM^Λ` and `FiniteTransitions^Λ`
  (`:1147`), which the paper also assumes rather than derives.

  **Scope, stated exactly.**  This is `∀ program accepted by genComputeSkeleton, ∀ Λ measured to
  confine it`, not `∀ E`.  It discharges **`HonestCommitment.Data.census`** at the
  generated-and-rendered skeleton.  It does **not** discharge
  `GenericHonestData.CensusRecordPremises.census`, which is stated over
  `skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)` at `E.Λ` — a reconstruction off an
  arbitrary `E`; that would additionally need the commitment-to-reconstruction identification.  It
  says nothing about executions that are not generated, and it moves no other premise.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenAirTransport

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.CensusExtraClosure
open Nock.NockVMROM.Thm54.HonestCommitment
open ComputeTable

variable {K : Type} [Field K]

/-! ## `InTree` scope to `bfsRows` scope, for any label predicate -/

/-- Every BFS row is the label of some `InTree` node, so a node-wise property is a row-wise one.
This is the step `genComputeSkeleton_bfsRows_census` performs inline; stated once here because the
window and the cell identities both need it. -/
theorem bfsRows_of_inTree (P : GenComputeRow K → Prop)
    (t : NTree (GenComputeRow K)) (h : ∀ u, InTree t u → P u.label) :
    ∀ g ∈ bfsRows t, P g := by
  intro g hg
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
  obtain ⟨r, hr, hin⟩ := (mem_bfsForest [t] u).mp hu
  simp only [List.mem_singleton] at hr
  subst hr
  exact h u hin

/-! ## The measurement transports along `LabelsFrom`

`RowNounsConfined` reads only the label, so a measurement taken on the generator's raw output is a
measurement on the AIR ordering.  Fixtures can therefore measure whichever tree they have. -/

/-- `TraceConfined` transports to any tree whose labels come from a confined one. -/
theorem traceConfined_of_labelsFrom {Λ : ℕ} {t t' : NTree (GenComputeRow K)}
    (hlab : LabelsFrom t' t) (h : TraceConfined Λ t) : TraceConfined Λ t' :=
  bfsRows_of_inTree _ _ (fun u hu => by
    obtain ⟨u0, hu0, heq⟩ := hlab u hu
    rw [heq]
    exact confined_inTree h hu0)

/-- In particular `airReorder` preserves it, since it only permutes children. -/
theorem traceConfined_airReorder {Λ : ℕ} (t : NTree (GenComputeRow K))
    (h : TraceConfined Λ t) : TraceConfined Λ (airReorder t) :=
  traceConfined_of_labelsFrom (labelsFrom_airReorder t) h

/-! ## The two inputs of §G's reduction, generically -/

/-- **`RowCellIdentities` at every BFS row of any accepted program, AIR-ordered, unconditionally.**

The first consumer of `cmpKind_of_labelsFrom`. -/
theorem genComputeSkeleton_bfsRows_cellIdentities_air
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ g ∈ bfsRows (airReorder t), RowCellIdentities g.skel :=
  bfsRows_of_inTree _ _
    (fun u hu => (cmpKind_of_labelsFrom h (labelsFrom_airReorder t) u hu).2.2.2)

/-- **`RowLeafWindow` at every BFS row of any accepted program, AIR-ordered, from the
measurement.** -/
theorem genComputeSkeleton_bfsRows_leafWindow_air {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hconf : TraceConfined Λ (airReorder t)) :
    ∀ g ∈ bfsRows (airReorder t), RowLeafWindow Λ g.skel :=
  bfsRows_of_inTree _ _ (genComputeSkeleton_leafWindow_air hΛ h hconf)

/-! ## `Data.census`, generically -/

/-- **`Data.census` for every program the generator accepts.**

Exactly the shape the `census` field takes — the rendered, BFS-assigned, AIR-ordered tree with the
memory forest arbitrary — with a single side condition, the decidable measurement.

Previously discharged only at `Op6Execution` / `K3` / `Λ = 7` by a three-row hand proof
(`SizeWindowBoundOp6.named_census`). -/
theorem genComputeSkeleton_census_air (z α : K) {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hconf : TraceConfined Λ (airReorder t))
    (mf : List (NTree (MemoryNode K))) :
    EdgeComparisonCensus.CombinedSkeletonCensus K
      (skeletonOfNodes
        (mapNTree GenComputeRow.node (renderRows z α (bfsAssign (airReorder t)))) mf) Λ := by
  refine census_of_leafWindow (K := K) _ Λ hΛ ?_ ?_ <;>
    rw [computeSkeletonRows_skeletonOfNodes_renderRows z α (bfsAssign (airReorder t)) mf []]
  · exact bfsAssign_computeSkeletonRows_of_bfsRows _ (airReorder t) []
      (genComputeSkeleton_bfsRows_cellIdentities_air h)
  · exact bfsAssign_computeSkeletonRows_of_bfsRows _ (airReorder t) []
      (genComputeSkeleton_bfsRows_leafWindow_air hΛ h hconf)

/-- **`Data.sizeWindowBound` for every program the generator accepts**, from the *same* measurement
that gives `census`.

`§B` of `CensusExtraClosure` recorded that the honest missing object behind `sizeWindowBound` is the
paper's leaf window; `sizeWindowBound_of_leafWindow` makes that a theorem, and this instantiates it
at the generated skeleton.  Previously discharged only at `Op6Execution` / `K3` / `Λ = 7`. -/
theorem genComputeSkeleton_sizeWindowBound_air (z α : K) {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hconf : TraceConfined Λ (airReorder t))
    (mf : List (NTree (MemoryNode K))) :
    SizeWindowCounting.SizeWindowNounsBoundedBy
      (skeletonOfNodes
        (mapNTree GenComputeRow.node (renderRows z α (bfsAssign (airReorder t)))) mf) Λ := by
  refine sizeWindowBound_of_leafWindow _ Λ ?_
  rw [computeSkeletonRows_skeletonOfNodes_renderRows z α (bfsAssign (airReorder t)) mf []]
  exact bfsAssign_computeSkeletonRows_of_bfsRows _ (airReorder t) []
    (genComputeSkeleton_bfsRows_leafWindow_air hΛ h hconf)

/-! ## The `genSemanticSkeleton` spelling

Live configurations build their skeleton as `genSemanticSkeleton (bfsAssign (airReorder t)) mf`
(e.g. `DotConfig769.semanticSkeleton`, `GenTierABinds.lean:565`) rather than through
`skeletonOfNodes`, and transport to `skeletonOfNodes` by a per-config equation.  Both extras are
therefore stated at that spelling too, so a configuration can consume them directly. -/

/-- `Data.census` at the spelling live configurations use. -/
theorem genComputeSkeleton_census_gen {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hconf : TraceConfined Λ (airReorder t))
    (mf : List (NTree (GenMemoryRow K))) :
    EdgeComparisonCensus.CombinedSkeletonCensus K
      (genSemanticSkeleton (bfsAssign (airReorder t)) mf) Λ :=
  census_of_leafWindow _ Λ hΛ
    (bfsAssign_computeSkeletonRows_of_bfsRows _ (airReorder t) mf
      (genComputeSkeleton_bfsRows_cellIdentities_air h))
    (bfsAssign_computeSkeletonRows_of_bfsRows _ (airReorder t) mf
      (genComputeSkeleton_bfsRows_leafWindow_air hΛ h hconf))

/-- `Data.sizeWindowBound` at the same spelling. -/
theorem genComputeSkeleton_sizeWindowBound_gen {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hconf : TraceConfined Λ (airReorder t))
    (mf : List (NTree (GenMemoryRow K))) :
    SizeWindowCounting.SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder t)) mf) Λ :=
  sizeWindowBound_of_leafWindow _ Λ
    (bfsAssign_computeSkeletonRows_of_bfsRows _ (airReorder t) mf
      (genComputeSkeleton_bfsRows_leafWindow_air hΛ h hconf))

/-- **`hwinNouns` from §1's window.**  Every size-window noun is a
`skeletonSubformula` slot (`s3`/`s4` result₀, `s6` result₁), already
bounded by `RowLeafWindow` of a confined generated tree.  No extra
hypothesis -/
theorem sizeWindowNounsBoundedBy_of_traceConfined {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hconf : TraceConfined Λ (airReorder t))
    (mf : List (NTree (GenMemoryRow K))) :
    SizeWindowCounting.SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder t)) mf) Λ :=
  genComputeSkeleton_sizeWindowBound_gen hΛ h hconf mf

/-- F-3: `1 ≤ Λ` is `one_le_of_hΛ_conf`. -/
theorem sizeWindowNounsBoundedBy_of_traceConfined_only {Λ : ℕ}
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hconf : TraceConfined Λ (airReorder t))
    (mf : List (NTree (GenMemoryRow K))) :
    SizeWindowCounting.SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder t)) mf) Λ :=
  sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hconf) h hconf mf

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.bfsRows_of_inTree
#print axioms Nock.NockVMROM.Thm54.TraceGen.traceConfined_airReorder
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_bfsRows_cellIdentities_air
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_bfsRows_leafWindow_air
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_census_air
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_sizeWindowBound_air
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_census_gen
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_sizeWindowBound_gen
#print axioms Nock.NockVMROM.Thm54.TraceGen.sizeWindowNounsBoundedBy_of_traceConfined
#print axioms Nock.NockVMROM.Thm54.TraceGen.sizeWindowNounsBoundedBy_of_traceConfined_only
