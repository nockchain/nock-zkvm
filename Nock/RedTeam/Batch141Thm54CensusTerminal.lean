import Nock.RedTeam.AO125Thm54CensusWiringRoute
import Nock.NockVMROM.Thm54.DistinctCensusCommitment

/-!
**Nothing here
inhabits a named premise, adds a carrier field, weakens a census predicate, withdraws a theorem, or
ticks a `§J` box.**  `BuildableNockExecution` keeps its fourteen fields, `HonestCommitment.Data` its
sixteen, `ResidualPremises` its four, `CensusRecordPremises` its five, and
`BuildablePackage.CommitmentResidual` its twenty-one.  No statement below is a verdict on the paper
construction, which is not in question at any point.

## §1. `CommitmentResidual` is INHABITED — confirmed, and at the F97 fixture by a production term

`b141_commitmentResidual_inhabited_at_F97`
compiles it here, from the production `def residualD`
(`DistinctCensusCommitment.lean:977-978`), and `b141_F97_inhabitant_is_the_census_fixture` pins that
the inhabitant's committed skeleton is `skelD`, its window is `7`, and the execution is the F97 one
the `census` row is about.  So the wire target is a live structure, not an empty one.

*Precision, recorded because the distinction has been conflated before.*  What is compiled about the
universal form is `b141_generic_residual_forces_q_equality`: a term of type
`∀ E, CommitmentResidual E` yields `∀ E, E.q = ringChar K`.  `BuildableNockExecution` carries only
`q_le_ringChar : q ≤ ringChar K` (`b141_buildable_carries_only_the_inequality`), and that inequality
does not force equality (`b141_le_does_not_force_eq` at the scalar level;
`GenericHonestCommitment.Concrete.f73_strict_q_le_inhabited` at F73's own `ringChar`).  This makes
the universal constructor **unavailable** — nothing in the build produces one, and producing one
would need equality from `≤`.

## §2. A2 is free — confirmed — and it is not the wire the identification needs

`b141_bindsAt_of_commitmentResidual_via_iff` derives the binding through
`RawSemanticAssembly.bindsAt_iff_scan`'s `.mpr`, from `R.shapeMatch`, `R.rowFrame` and `R.scan`
— three *fields* of `CommitmentResidual` (`BuildablePackage.lean:74-82`) — plus
`specializedProblem_seed`.  No hypothesis is added.  `b141_a2_forward` runs the same biconditional's
`.mp`, so both directions are proved and A2 is an equivalence, not a one-way reduction.

That the identification is a different object is compiled twice.
`b141_census_field_is_over_the_reconstruction` extracts the `census` field and shows its object is
`skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)`, while `BindsAt`'s object is
`C.skeleton` against `exec`.  `b141_row_component_does_not_determine_skel` shows the two coordinates
of `ComputeNode` are independent: two nodes with the *same* `row` (hence the same
`mapNTree ComputeNode.row`, which is all `Data.compute_rows` pins) give reconstructions whose rows
are two arbitrary and distinct skeletons.  So nothing that pins only the `row` component — which is
what the binding layer sees — determines the layer `census` is stated over.

## §3. The block's location, and the relocation, under the standing equivalence test

**The relocation claim holds.**

**The standing equivalence test, applied explicitly, and it separates.**
`b141_residual_does_not_imply_check` exhibits a one-row `OP_1` skeleton on which
`RowLeafWindow 1` holds at *every* compute row while `CanonicalCommitmentCheck 97 ⟨·, 1⟩` **fails**.
The mechanism: `decActive st.f_h = true` in every state (`SemanticStrategy.lean:50-51`), so
`commitmentNouns` bounds the `.dec.f_h` noun, and `RowLeafWindow` bounds only the public triple and
the subformula projections — never a `dec` slot.  So the check is **strictly stronger** than the
residual, in the same bound.

Consequence, stated precisely: AD-3's "the check *is* the residual restated" should read **"entails
the residual, strictly"**.  This does not weaken AD-7 — it hardens it.  A route whose new premise
strictly implies the old one cannot be a reduction in any direction; C2 is a rename in the
favourable direction and an *increase* in the other.

## §4. `C.nounSizeBound ≤ E.Λ` — confirmed on both halves

`b141_nounSizeBound_free_on_the_assembly_path` recompiles the `rfl`-chain independently:
`censusAssemblyOf` sets `nounSizeBound := E.Λ` (`GenericHonestData.lean:1772`) and `dataOf` sets
`Λ := E.Λ`, so the two scalars are the same numeral.  The failure at `1` is therefore exactly the untied scalar and not a defect of the witness,
so the obligation is genuine off the assembly path.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch141

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.CensusExtraClosure
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.RawSemanticAssembly
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## §1. `CommitmentResidual` is inhabited -/

section F97Inhabitation

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment

local instance prime97b141 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97b141 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

-- Form R leftover first-row counts (live is `chainOneBitWeight`).
variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD

/-- **Claim 1, first half: `CommitmentResidual` is INHABITED.**  Compiled at the F97 fixture the
`census` row is about, from the production term `DistinctCensusCommitment.residualD`. -/
theorem b141_commitmentResidual_inhabited_at_F97 :
    Nonempty (BuildablePackage.CommitmentResidual (distinctCensusExecution hfirstD)) :=
  ⟨residualD hfirstD⟩

/-- The inhabitant is the F97 one, not a degenerate stand-in: its committed skeleton is `skelD`, its
committed window is `7`, and the execution's atom bound is `97`. -/
theorem b141_F97_inhabitant_is_the_census_fixture :
    (residualD hfirstD).commitment.skeleton = skelD ∧ (residualD hfirstD).Λ = 7 ∧
      (distinctCensusExecution hfirstD).q = 97 ∧ (distinctCensusExecution hfirstD).Λ = 7 :=
  ⟨rfl, rfl, rfl, rfl⟩

end F97Inhabitation

section GenericConstructor

variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- **Claim 1, second half, as far as it is compiled.**  A universal constructor would force the
strict `q` pin at *every* buildable execution. -/
theorem b141_generic_residual_forces_q_equality
    (g : ∀ E : BuildableNockExecution F K, BuildablePackage.CommitmentResidual E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  fun E => (g E).q_eq_ringChar

end GenericConstructor

/-- What a buildable execution actually carries is the *inequality*. -/
theorem b141_buildable_carries_only_the_inequality (E : BuildableNockExecution F K) :
    E.q ≤ ringChar K :=
  E.q_le_ringChar

/-- …and the inequality does not force equality.  Scalar level only: this is the shape of the gap,
not an execution-level counterexample, and the build exhibits no
`E : BuildableNockExecution` with `E.q ≠ ringChar K`.  The F73 instance of the same shape at a real
`ringChar` is `GenericHonestCommitment.Concrete.f73_strict_q_le_inhabited`. -/
theorem b141_le_does_not_force_eq :
    ∃ q n : ℕ, 1 < q ∧ q ≤ n ∧ q ≠ n :=
  ⟨2, 3, by norm_num, by norm_num, by norm_num⟩

/-! ## §2. A2 is free, and is not the wire the identification needs -/

section A2

variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- **Claim 2, first half: A2 is free.**  Derived through the biconditional's `.mpr`, from three
fields the structure already has, with no added hypothesis. -/
theorem b141_bindsAt_of_commitmentResidual_via_iff
    (E : BuildableNockExecution F K) (R : BuildablePackage.CommitmentResidual E)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    BindsAt z R.commitment.skeleton
      (specializedProblem R.verifier.raw.timestamp z hz α lmb).cfg
      (specializedProblem R.verifier.raw.timestamp z hz α lmb).exec :=
  bindsAt_iff_scan.mpr
    ⟨specializedProblem_seed R.verifier.raw.timestamp z hz α lmb,
      R.shapeMatch z hz α lmb, R.rowFrame z hz α lmb, R.scan z hz α lmb⟩

/-- The other direction of the same biconditional, so that "proved biconditional" rests on a use of
both halves in this file. -/
theorem b141_a2_forward {z : K} {C : SkeletonCommitment}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : BindsAt z C.skeleton cfg exec) :
    ExecTreeShapeMatchesAt C exec ∧ RowFrameChecksAt z C exec ∧
      ActiveFingerprintChecksAt z C exec :=
  ⟨(bindsAt_iff_scan.mp h).2.1, (bindsAt_iff_scan.mp h).2.2.1, (bindsAt_iff_scan.mp h).2.2.2⟩

end A2

/-- **Claim 2, second half, part one.**  The `census` field's object is the reconstruction; this is
the exact terminal object the field consumes. -/
theorem b141_census_field_is_over_the_reconstruction
    {E : BuildableNockExecution F K} {P : ResidualPremises E} {M : MemoryRecordPremises E}
    (C : CensusRecordPremises E P M) :
    EdgeComparisonCensus.CombinedSkeletonCensus K
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ :=
  C.census

/-- **Claim 2, second half, part two.**  `ComputeNode`'s `row` and `skel` are independent
coordinates: two nodes with the *same* `row` — hence the same `mapNTree ComputeNode.row`, which is
all `Data.compute_rows` pins — yield reconstructions carrying two arbitrary and distinct row
skeletons.  So the binding layer, which sees `row`, cannot determine the layer `census` is stated
over. -/
theorem b141_row_component_does_not_determine_skel
    (stamp : ComputeTimestampRow) (row : ComputeTable.State × ComputeTable.DTcomp K)
    (s₁ s₂ : ComputeRowSkeleton) :
    (⟨s₁, stamp, row⟩ : ComputeNode K).row = (⟨s₂, stamp, row⟩ : ComputeNode K).row ∧
      mapNTree ComputeNode.row (NTree.node ⟨s₁, stamp, row⟩ []) =
          mapNTree ComputeNode.row (NTree.node ⟨s₂, stamp, row⟩ []) ∧
        (skeletonOfNodes (NTree.node ⟨s₁, stamp, row⟩ [])
            ([] : List (NTree (MemoryNode K)))).computeTree.label = s₁ ∧
          (skeletonOfNodes (NTree.node ⟨s₂, stamp, row⟩ [])
              ([] : List (NTree (MemoryNode K)))).computeTree.label = s₂ := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [skeletonOfNodes, mapNTree]

/-! ## §3. The relocation, and the standing equivalence test -/

theorem b141_rowLeafWindow_of_check {p : ℕ} {C : SkeletonCommitment}
    (h : CanonicalCommitmentCheck p C) (hb : 1 ≤ C.nounSizeBound) :
    ∀ s ∈ computeSkeletonRows C.skeleton, RowLeafWindow C.nounSizeBound s := by
  intro s hs
  have key : ∀ a : ComputeSlotAddress, computeSlotActive s.state a = true →
      (computeSlotNoun s a).leaves ≤ C.nounSizeBound := fun a ha =>
    (h _ (mem_commitmentNouns_compute hs ((mem_activeComputeSlotAddresses_iff _ _).2 ha))).2
  refine ⟨key .subject rfl, key .formula rfl, key .evaluation rfl, ?_⟩
  intro i slot
  by_cases hi : (i : ℕ) < ComputeTable.fanoutComp s.state
  · rw [P8Census.skeletonSubformula, dif_pos hi]
    have hk := key (.sub i slot) (by simp [computeSlotActive, hi])
    rwa [computeSlotNoun_sub_of_active hi slot] at hk
  · rw [P8Census.skeletonSubformula, dif_neg hi]
    simpa [Noun.leaves] using hb

section EquivalenceTest

/-! the paper cite on `bigDecRow` below —
> a row that sets `state :=.s1` and is described as an `OP_1` row — should be read as
> **the paper **.  `.s1` is
> `OP_1` by `ComputeTable.lean:140-150` (`State.toNat.s1 = 1`).
>
> **No mathematical consequence.**  `b141_residual_does_not_imply_check` and its supporting lemmas
> read only `ComputeTable.fanoutComp.s1 = 0` (`NockVM.lean:157-159`),
> `Nock.Framework.recordCount.s1 = 1` (`NockInstances.lean:61-63`) and
> `hasTailDecomposition.s1 = false` (`SemanticStrategy.lean:46-48`) — the last through
> `decActive st.f_h = true`, which holds in **every** state and is what the separation uses.  All
> three re-measured at source.  A claim-hygiene repair, not a proof repair; no statement, name,
> proof or definition in this file changes, and the result is not withdrawn.  It scopes the all-`.atom 0` claim to "public triple and
> subformula projections", which is exactly true, and then states the decomposition slots are a
> two-leaf cell, which is also exactly true. -/

/-- An `OP_1` row whose public triple and subformula projections are all `.atom 0`, and whose
decomposition slots are a two-leaf cell.  `RowLeafWindow` never reads a `dec` slot; the canonical
check does, because `decActive st.f_h = true` in every state. -/
def bigDecRow : ComputeRowSkeleton where
  state := .s1
  subject := .atom 0
  formula := .atom 0
  evaluation := .atom 0
  decomposition := fun _ _ => .cell (.atom 0) (.atom 0)
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩

def bigDecSkeleton : SemanticSkeleton where
  computeTree := .node bigDecRow []
  memoryForest := []

theorem bigDecSkeleton_computeRows :
    computeSkeletonRows bigDecSkeleton = [bigDecRow] := by
  unfold computeSkeletonRows bigDecSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

theorem bigDecRow_dec_noun :
    computeSlotNoun bigDecRow (.dec .f_h) = .cell (.atom 0) (.atom 0) := by
  show P8Census.skeletonDec bigDecRow .f_h = _
  rw [P8Census.skeletonDec, dif_pos (by rfl : decActive bigDecRow.state .f_h = true)]
  rfl

theorem bigDecRow_window : RowLeafWindow 1 bigDecRow := by
  refine ⟨by simp [bigDecRow, Noun.leaves], by simp [bigDecRow, Noun.leaves],
    by simp [bigDecRow, Noun.leaves], ?_⟩
  intro i slot
  rw [P8Census.skeletonSubformula]
  split
  · simp [bigDecRow, Noun.leaves]
  · simp [Noun.leaves]

/-- **The standing equivalence test, in the direction that decides whether C2 is a rename.**  The
residual holds at every compute row of this skeleton while the canonical check **fails** at the same
committed bound.  So `CanonicalCommitmentCheck`'s leaf conjunct is *strictly stronger* than
`RowLeafWindow`, not equal to it: attaching the check relocates the premise upward, never
downward. -/
theorem b141_residual_does_not_imply_check :
    (∀ s ∈ computeSkeletonRows bigDecSkeleton, RowLeafWindow 1 s) ∧
      ¬ CanonicalCommitmentCheck 97 ⟨bigDecSkeleton, 1⟩ := by
  constructor
  · intro s hs
    rw [bigDecSkeleton_computeRows, List.mem_singleton] at hs
    subst hs
    exact bigDecRow_window
  · intro h
    have hrow : bigDecRow ∈ computeSkeletonRows
        (⟨bigDecSkeleton, 1⟩ : SkeletonCommitment).skeleton := by
      show bigDecRow ∈ computeSkeletonRows bigDecSkeleton
      rw [bigDecSkeleton_computeRows]
      exact List.mem_singleton_self _
    have hactive : (ComputeSlotAddress.dec .f_h) ∈
        activeComputeSlotAddresses bigDecRow.state :=
      (mem_activeComputeSlotAddresses_iff _ _).2 rfl
    have := (h _ (mem_commitmentNouns_compute hrow hactive)).2
    rw [bigDecRow_dec_noun] at this
    simp [Noun.leaves] at this

end EquivalenceTest

/-! ## §4. `C.nounSizeBound ≤ E.Λ` -/

section NounSizeBound

variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- **Claim 4, the free half**, recompiled independently. -/
theorem b141_nounSizeBound_free_on_the_assembly_path
    (E : BuildableNockExecution F K) (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (C : CensusRecordPremises E P M)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOfCensus E P M C hln).nounSizeBound = E.Λ ∧
      (dataOfCensus E P M C hln).Λ = E.Λ ∧
        (dataOfCensus E P M C hln).nounSizeBound ≤ (dataOfCensus E P M C hln).Λ :=
  ⟨rfl, rfl, le_rfl⟩

end NounSizeBound

theorem b141_nounSizeBound_is_load_bearing_confirmed :
    CanonicalCommitmentCheck 2 ⟨AO125.wideSkeleton, 2⟩ ∧
      ¬ (∀ s ∈ computeSkeletonRows AO125.wideSkeleton, RowLeafWindow 1 s) :=
  ⟨AO125.wideCommitment_check, AO125.ao125_nounSizeBound_is_load_bearing.2.2⟩

/-- So the failure at `1` is exactly the untied
scalar `C.nounSizeBound ≤ Λ` and not a defect of the witness. -/
theorem b141_wideSkeleton_window_at_its_own_bound :
    ∀ s ∈ computeSkeletonRows AO125.wideSkeleton, RowLeafWindow 2 s := by
  intro s hs
  rw [AO125.wideSkeleton_computeRows, List.mem_singleton] at hs
  subst hs
  refine ⟨by simp [AO125.wideRow, Noun.leaves], by simp [AO125.wideRow, Noun.leaves],
    by simp [AO125.wideRow, Noun.leaves], ?_⟩
  intro i slot
  rw [P8Census.skeletonSubformula]
  split
  · simp [AO125.wideRow, Noun.leaves]
  · simp [Noun.leaves]

/-! ## §5. Nothing moved -/

/-- `CensusRecordPremises` is still five named fields. -/
theorem b141_censusRecordPremises_still_five {E : BuildableNockExecution F K}
    {P : ResidualPremises E} {M : MemoryRecordPremises E}
    (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl

/-- `ResidualPremises` is still four named fields. -/
theorem b141_residualPremises_still_four {E : BuildableNockExecution F K}
    (P : ResidualPremises E) :
    P =
      { axisAtoms := P.axisAtoms
        inactiveDec := P.inactiveDec
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

#print axioms b141_commitmentResidual_inhabited_at_F97
#print axioms b141_F97_inhabitant_is_the_census_fixture
#print axioms b141_generic_residual_forces_q_equality
#print axioms b141_buildable_carries_only_the_inequality
#print axioms b141_le_does_not_force_eq
#print axioms b141_bindsAt_of_commitmentResidual_via_iff
#print axioms b141_a2_forward
#print axioms b141_census_field_is_over_the_reconstruction
#print axioms b141_row_component_does_not_determine_skel
#print axioms b141_rowLeafWindow_of_check
#print axioms bigDecSkeleton_computeRows
#print axioms bigDecRow_dec_noun
#print axioms bigDecRow_window
#print axioms b141_residual_does_not_imply_check
#print axioms b141_nounSizeBound_free_on_the_assembly_path
#print axioms b141_nounSizeBound_is_load_bearing_confirmed
#print axioms b141_wideSkeleton_window_at_its_own_bound
#print axioms b141_censusRecordPremises_still_five
#print axioms b141_residualPremises_still_four

end

end Nock.RedTeam.Batch141
