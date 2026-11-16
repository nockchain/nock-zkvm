/-
  Nock/NockVMROM/Thm54/TraceGen/GenAirTransport.lean

  **Removing the air / non-air duplication, rather than patching instances of it.**

  Three `_air` variants were added.

  So the fix here is structural rather than another pair of theorems.  `airReorder` only permutes
  children — it keeps every label (`airReorder_label`, `GenAirOrder.lean:73`; per-node
  `inTree_airReorder_label`, `GenAirOrderChildLink.lean:40`).  **Every property that reads only
  `.label` therefore transports across it.**  Stating such a property once against
  `LabelsFrom t' t` covers both orderings, and there is no second theorem to keep in sync.

  `nodeCensus`, `NodeCmpKind` and `RowSeedGood` are all label-only, so all three transport.  What
  does **not** transport this way is anything reading the tree's *shape* — fan-out, child links, the
  BFS index — and those already have their own air results (`airReorder_inTree_fanout`,
  `childLinkAll_airReorder_of_gen`, `genComputeSkeleton_airReorder_computeNodes_OK`).  The
  distinction is the point: label-only obligations need no duplication, shape obligations genuinely
  do.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenRowShape
import Nock.NockVMROM.Thm54.TraceGen.GenConsHead
import Nock.NockVMROM.Thm54.TraceGen.GenGenericCensus
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderChildLink
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulAccept

-- A missing import otherwise becomes a silent type variable rather than an error;
-- that cost real debugging time on this module family.
set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

/-! ## The transport hypothesis

`LabelsFrom`, `labelsFrom_self`, `labelsFrom_airReorder` and `census_of_labelsFrom` now live in
`GenGenericCensus.lean`, above the censuses they subsume, so the AIR census is a corollary of the
transport rather than a second induction.  What remains here is the transport applied to the
predicates defined downstream of that module. -/

/-- The comparison census likewise -- provided for symmetry with `census_of_labelsFrom`; **it has
no consumer yet**, since nothing downstream needs `NodeCmpKind` at the AIR ordering.
Stated here rather than duplicated later.

The comparison census likewise, with no side hypothesis (`NoHead8` being vacuous). -/
theorem cmpKind_of_labelsFrom
    {fuel : ℕ} {subject formula : Noun}
    {t t' : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hlab : LabelsFrom t' t) :
    ∀ u, InTree t' u → NodeCmpKind (K := K) u.label := by
  intro u hu
  obtain ⟨u0, hu0, heq⟩ := hlab u hu
  rw [heq]
  exact genComputeSkeleton_inTree_cmpKind_unconditional h u0 hu0

/-- **`SeedGood` transports**, because `RowSeedGood` reads only the label.  This is what makes the
seed predicate usable at the committed ordering without a second predicate. -/
theorem seedGood_of_labelsFrom {z : K}
    {t t' : NTree (GenComputeRow K)}
    (hgood : SeedGood z t) (hlab : LabelsFrom t' t) :
    SeedGood z t' := by
  intro u hu
  obtain ⟨u0, hu0, heq⟩ := hlab u hu
  rw [heq]
  exact hgood u0 hu0

/-- The AIR-ordered instance, stated for the reader who wants it by name. -/
theorem seedGood_airReorder {z : K} {t : NTree (GenComputeRow K)}
    (hgood : SeedGood z t) : SeedGood z (airReorder t) :=
  seedGood_of_labelsFrom hgood (labelsFrom_airReorder t)

/-! ## The `cons`-head shape hypothesis, discharged

`rowBad_card_le_of_shape` (`DH`) takes the row's shape as a hypothesis, and its `cons` component was
the one open structural step: nothing derived "at a `cons` row the formula head is a cell".
`genComputeSkeleton_inTree_consHead` (`GenConsHead.lean`) now proves it for any accepted program, so
that component is discharged and only the **leaf window** remains — which is the parked `census` /
`RowLeafWindow` premise, a separate obligation. -/

/-- **`rowBad_card_le_of_shape`'s `cons` hypothesis, for a generated row.**

The shape half is proved; the caller supplies only the leaf window. -/
theorem consShape_of_generated (Λ : ℕ)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (u : NTree (GenComputeRow K)) (hu : InTree t u)
    (hwin : ∀ a b, formulaHead u.label.skel.formula = Noun.cell a b →
      (Noun.cell a b).leaves ≤ Λ) :
    u.label.skel.state = State.cons →
      ∃ a b, formulaHead u.label.skel.formula = Noun.cell a b ∧
        (Noun.cell a b).leaves ≤ Λ := by
  intro hst
  obtain ⟨a, b, hab⟩ := genComputeSkeleton_inTree_consHead h u hu hst
  exact ⟨a, b, hab, hwin a b hab⟩

/-! ## `V_comp` at the committed ordering

`genComputeSkeleton_inTree_Vcomp_of_seedGood` is stated at the generator's own tree.  The committed
ordering needs `genComputeSkeleton_airReorder_bfsLabelAt_Vcomp` (`GenMatmulAccept.lean:27`), whose
three hypotheses are over `InTree t` — so `SeedGood z t` supplies them directly and no transport is
needed here. -/

/-- **`V_comp` at every BFS row of the AIR-ordered tree, from one `SeedGood` hypothesis.**

The form a live configuration needs: `DotConfig769` and every other config commit
`bfsAssign (airReorder t)`. -/
theorem genComputeSkeleton_airReorder_bfsLabelAt_Vcomp_of_seedGood (z α : K) (hz : z ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hgood : SeedGood z t)
    {i : ℕ} (hi : i ∈ List.range' 1 (bfsForest [airReorder t]).length) :
    Vcomp (renderNode z α (bfsLabelAt (airReorder t) i)).row.2.1
      (renderNode z α (bfsLabelAt (airReorder t) i)).row.2.2.1
      (renderNode z α (bfsLabelAt (airReorder t) i)).row.2.2.2 :=
  genComputeSkeleton_airReorder_bfsLabelAt_Vcomp z α hz h
    (fun v hv hc => (hgood v hv).1 hc)
    (fun v hv h5 => (hgood v hv).2.1 h5)
    (fun v hv h3 => (hgood v hv).2.2 h3)
    hi

/-! ## The bad-seed count at the committed ordering

`seedBad_card_le` counts over `bfsRows t`.  The committed ordering counts over
`bfsRows (airReorder t)`, and `rowsBad_card_le` applies to any list, so this is the same theorem at
a different list — no new counting argument. -/

/-- The trace-level bad-seed count over the AIR-ordered rows. -/
theorem seedBad_card_le_air [Fintype K] [DecidableEq K] (B : ℕ)
    (t : NTree (GenComputeRow K))
    (hrow : ∀ g ∈ bfsRows (airReorder t),
      (Finset.univ.filter (fun z : K => ¬ RowSeedGood z g)).card ≤ B) :
    (Finset.univ.filter
        (fun z : K => ∃ g ∈ bfsRows (airReorder t), ¬ RowSeedGood z g)).card
      ≤ (bfsRows (airReorder t)).length * B :=
  rowsBad_card_le B (bfsRows (airReorder t)) hrow

/-- A good seed at the AIR ordering, from the AIR-ordered count. -/
theorem seedGood_airReorder_of_not_mem [Fintype K] [DecidableEq K] (z : K)
    (t : NTree (GenComputeRow K))
    (hz : z ∉ Finset.univ.filter
      (fun w : K => ∃ g ∈ bfsRows (airReorder t), ¬ RowSeedGood w g)) :
    SeedGood z (airReorder t) :=
  seedGood_of_not_mem_seedBad z (airReorder t) hz

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.census_of_labelsFrom
#print axioms Nock.NockVMROM.Thm54.TraceGen.cmpKind_of_labelsFrom
#print axioms Nock.NockVMROM.Thm54.TraceGen.seedGood_of_labelsFrom
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_airReorder_bfsLabelAt_Vcomp_of_seedGood
#print axioms Nock.NockVMROM.Thm54.TraceGen.seedBad_card_le_air
#print axioms Nock.NockVMROM.Thm54.TraceGen.consShape_of_generated
