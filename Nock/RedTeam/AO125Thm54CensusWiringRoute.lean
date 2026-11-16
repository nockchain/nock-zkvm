import Nock.RedTeam.Batch140Thm54CensusReduction
import Nock.NockVMROM.Thm54.BuildablePackage
import Nock.NockVMROM.Thm54.GenericHonestData

/-!
# Is the `census` wiring route AVAILABLE or BLOCKED?

**Nothing here inhabits a named premise, adds a
carrier field, weakens a census predicate, withdraws a theorem, or ticks a `§J` box.**
`BuildableNockExecution` keeps its fourteen fields, `HonestCommitment.Data` its sixteen,
`ResidualPremises` its four, `CensusRecordPremises` its five, and
`BuildablePackage.CommitmentResidual` its twenty-one.  No statement below is a verdict on the paper
construction, which is not in question at any point.

This module measures all three.

## §A. A2 is NOT an open frontier — it is dischargeable from objects already held

`RawSemanticAssembly.bindsAt_iff_scan` is a **proved biconditional**, in both directions, and the
three checks on its right-hand side — `ExecTreeShapeMatchesAt`, `RowFrameChecksAt`,
`ActiveFingerprintChecksAt` — are **already fields** of `BuildablePackage.CommitmentResidual`
(`shapeMatch`, `rowFrame`, `scan`).  `ao125_bindsAt_of_commitmentResidual` compiles the consequence:
every `CommitmentResidual E` yields `SemanticStrategy.BindsAt` at every admissible seed, with no
added hypothesis.

**Status of A2: dischargeable from held objects, and in fact already discharged in production.**

## §B. …and A2 is therefore NOT the wire that (a) needs.

`BindsAt z C.skeleton cfg exec` relates the committed skeleton to the **execution**, through
fingerprints.  The `census` field is over the **reconstruction**
`skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)`, which is a third object, built from `E`
and the premises.  `HonestCommitment.Data.skeleton D` unfolds to
`skeletonOfNodes D.computeNodes D.memoryNodes` (`HonestCommitment.lean:775-776`), and
`commitmentResidualOf` publishes `⟨D.skeleton, D.nounSizeBound⟩`
(`HonestCommitment.lean:985`).  So the identification (a) is exactly

  `D.computeNodes = computeNodesOf E P`  and  `D.memoryNodes = memoryNodesOf E M`,

which `ao125_identification_reduces_to_node_equality` compiles.  **`BindsAt` does not supply it.**
Two realizations of one fingerprint are equal
only under `SepSeed` (`FPRealizationWitness.noun_unique`), and
`GenericHonestCommitment.chooseNoun_uses_existence_only` records that the generic constructor never
applies it.

So (a) is a **noun-uniqueness (`SepSeed`) obligation on the soundness side**, **not** the A2 binding residual.  A2 is closed; this is not.

## §C. Wires (a) and (b) both EVAPORATE at one particular commitment — and that is the trap

`SkeletonCommitment` is a bare pair `⟨skeleton, nounSizeBound⟩` with **no invariant**
(`SkeletonCommitment.lean:39-43`).  Take `C := ⟨reconstruction, E.Λ⟩` — `ao125_reconCommitment` — and:

* the identification (a) is `fun s hs => hs`, and
* the bound (b) is `le_rfl`,

so `ao125_census_of_check_at_reconCommitment` produces the `CensusRecordPremises.census` object
**at its own consumed layer**, from the check plus the paper's `cons` equations and `1 ≤ E.Λ`, with
no identification hypothesis and no scalar hypothesis at all.

**This is not progress, and saying why is the point of the pass.**  The route has moved the residual, not
shrunk it.  What the route promised was a check on data the *prover published*; at
`⟨reconstruction, E.Λ⟩` nothing is published, so the promise is unredeemed.

## §D. `C.nounSizeBound ≤ E.Λ` — free on one path, a genuine obligation in general

`ao125_nounSizeBound_le_Lambda_on_the_dataOfCensus_path` compiles that
`(dataOfCensus E P M C).nounSizeBound ≤ (dataOfCensus E P M C).Λ` holds **by `rfl`-chain**, both
sides being `E.Λ`: `censusAssemblyOf` sets `nounSizeBound := E.Λ` and `dataOf` sets `Λ := E.Λ`.  So
on the honest assembly path the scalar tie is free.

It is **not** free in general, and that is compiled rather than asserted.
`HonestCommitment.Data` carries `nounSizeBound : ℕ` and `Λ : ℕ` as two independent bare scalars with
no field relating them, and `SkeletonCommitment` has no invariant at all.
`ao125_nounSizeBound_is_load_bearing` exhibits a commitment satisfying `CanonicalCommitmentCheck` at
its own bound `2` whose single row **fails** `RowLeafWindow 1`: without `C.nounSizeBound ≤ Λ` the
check says nothing at `Λ`.

**Verdict on (b): derivable on the `dataOfCensus`/`censusAssemblyOf` path, an additional obligation
on any other, including the `commitmentResidualOf D` path for an arbitrary `Data E`.**

## §E. (c) confirmed: the check does not subsume `RowCellIdentities`

`ao125_check_does_not_subsume_rowCellIdentities` exhibits an all-atom `OP_1` skeleton on which
`CanonicalCommitmentCheck 2 ⟨·, 1⟩` holds while `RowCellIdentities` fails at its only row —
`formula_cons` wants `s.formula =.cell (dec.f_h) (dec.f_t)`, a *cell*, and the check bounds each
`dec` slot separately while the census compares the formula against their `cons` cell, whose leaf
count is the sum.

## §F.

The brief asks what it would mean for the route if `CommitmentResidual` were uninhabited.  It is
not.  `ao125_commitmentResidual_inhabited_from_data` compiles that `CommitmentResidual E` is
inhabited whenever `HonestCommitment.Data E` is, and `Data` is inhabited at **three** semantically
distinct executions (`Concrete.data73`, `MultiRootHonestCommitment.dataM`,
`DistinctCensusCommitment.dataD`), among them `DistinctCensusCommitment.residualD`, at the
**F97 fixture the `census` row is about**.

`data73`, `dataM` and `dataD` sit over
`concreteExecution`, `multiRootExecution` and `distinctCensusExecution` — three, not two — and the
build carries **eleven** argument-free `def`s of type `BuildablePackage.CommitmentResidual`
(`BuildablePackage.Concrete.residual73`, `HonestCommitment.Concrete.residual73'`,
`GenericHonestArrays.Concrete.residual73Honest` and `…_of_char`, `MultiRootHonestCommitment.residualM`,
`MultiRootHonestArrays.residualHonestM`, `MultiRootPhaseCorrect.residualHonestP`,
`DistinctCensusCommitment.residualD`, `DistinctCensusHonestArrays.residualHonestD`,
`DistinctCensusPhaseCorrect.residualHonestQ`, and `…_of_char`'s partner), of which
`residual73Honest_of_char = residual73Honest` by `rfl` (`residual73Honest_of_char_eq`), plus the
parametric family `MultiRootNonzeroChallenges.residualHonestN a g`.  Nothing here changes the
verdict: the point was only ever that the structure is not empty.

What is **unavailable — not refuted** is the strictly different **generic constructor**
`∀ E, CommitmentResidual E`: `ao125_no_generic_commitmentResidual_constructor` re-exports that it
would force `∀ E, E.q = ringChar K`, against the strict-`q` **reading** recorded at F73
(`GenericHonestCommitment.Concrete.f73_strict_q_le_inhabited`, a scalar
`∃ q, 1 < q ∧ q ≤ ringChar K73cubic ∧ q ≠ ringChar K73cubic`).  A wire into
`CommitmentResidual` therefore does **not** wire into an empty structure.  It is the *universally
quantified* route that is unavailable, not the pointwise one.

## §G. Verdict

Not at (a) — that wire is free at
`⟨reconstruction, E.Λ⟩` and, at a published commitment, is a `SepSeed` obligation rather than the
already-discharged A2.  Not at (b) — free on the honest assembly path.  Not at (c) — the `cons`
equations are separately available (`distinctCensus_rowCellIdentities` discharges them outright at
F97).  The block is that **`CanonicalCommitmentCheck` is held by nothing**: it is a field of no
structure in the cone, and the only structure it could be attached to is
`BuildablePackage.CommitmentResidual`, which this pass is forbidden to change and does not change.
At the one commitment where it costs nothing to state — `⟨reconstruction, E.Λ⟩` — it is the residual
itself, restated.

`census`'s clean terminal description is in `ao125_census_terminal_description`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.AO125

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.CensusExtraClosure
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.RawSemanticAssembly
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## §A. A2 is dischargeable from a `CommitmentResidual`, with no added hypothesis -/

section A2

variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- **A2's actual status: DISCHARGEABLE, not an open frontier.**  Every `CommitmentResidual E`
already carries `shapeMatch`, `rowFrame` and `scan`, and `bindsAt_of_scan` turns exactly those three
into the binding at every admissible seed.  No hypothesis is added and no field is used that the
structure does not already have. -/
theorem ao125_bindsAt_of_commitmentResidual
    (E : BuildableNockExecution F K) (R : BuildablePackage.CommitmentResidual E)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    BindsAt z R.commitment.skeleton
      (specializedProblem R.verifier.raw.timestamp z hz α lmb).cfg
      (specializedProblem R.verifier.raw.timestamp z hz α lmb).exec :=
  bindsAt_of_scan (specializedProblem_seed R.verifier.raw.timestamp z hz α lmb)
    (R.shapeMatch z hz α lmb) (R.rowFrame z hz α lmb) (R.scan z hz α lmb)

/-- A2 is a **biconditional**, not a one-way reduction: the three checks are exactly the binding.
Re-exported here so the classification rests on a statement in this file. -/
theorem ao125_a2_is_an_equivalence {z : K} {C : SkeletonCommitment}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} :
    BindsAt z C.skeleton cfg exec ↔
      (cfg.challenges.z = z ∧ ExecTreeShapeMatchesAt C exec ∧
        RowFrameChecksAt z C exec ∧ ActiveFingerprintChecksAt z C exec) :=
  bindsAt_iff_scan

end A2

/-! ## §B. What the identification actually is — node equality, not `BindsAt`

This heading and the docstring below say "(a) **is** node equality".  Read
> instead: **(a) REDUCES TO node equality, which is sufficient for wire (a) and strictly stronger
> than the skeleton equality the published commitment actually needs.**  The published commitment
> is the pair `⟨D.skeleton, D.nounSizeBound⟩`, so what it requires is **skeleton** equality, and
> `skeletonOfNodes` (`HonestCommitment.lean:489-492`) forgets `stamp` and `row`: two nodes agreeing
> only on `skel` already give equal reconstructions.  `AD-2`'s own wording — "(a) is a `SepSeed` noun-uniqueness obligation on the soundness
> side, not the A2 binding residual" — is unaffected and remains exact. -/

/-- **The identification (a), reduced to its real content.**  The published commitment's skeleton is
`skeletonOfNodes D.computeNodes D.memoryNodes`; the census layer is
`skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)`.  So (a) is *node equality*, and nothing
about fingerprints or seeds enters.  `BindsAt` does not deliver it: `Data.compute_rows` pins only
the `row` component, while `skeletonOfNodes` reads the `skel` component. -/
theorem ao125_identification_reduces_to_node_equality
    {E : BuildableNockExecution F K} (D : Data E)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (hc : D.computeNodes = computeNodesOf E P)
    (hm : D.memoryNodes = memoryNodesOf E M) :
    D.skeleton = skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M) := by
  unfold Data.skeleton
  rw [hc, hm]

/-- The published commitment of an honest `Data` is literally the pair
`⟨D.skeleton, D.nounSizeBound⟩`, so §B's reduction is the whole of wire (a). -/
theorem ao125_published_commitment_is_the_data_pair
    [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    {E : BuildableNockExecution F K} (D : Data E) :
    (commitmentResidualOfZero D).commitment = ⟨D.skeleton, D.nounSizeBound⟩ :=
  rfl

/-! ## §C. The reconstruction commitment: wires (a) and (b) are free there -/

/-- The `SkeletonCommitment` whose skeleton **is** the reconstruction and whose committed bound
**is** `E.Λ`.  `SkeletonCommitment` carries no invariant, so this is a legal commitment. -/
def ao125_reconCommitment (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E) : SkeletonCommitment :=
  ⟨skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M), E.Λ⟩

theorem ao125_reconCommitment_wires_are_free
    (E : BuildableNockExecution F K) (P : ResidualPremises E) (M : MemoryRecordPremises E) :
    (ao125_reconCommitment E P M).skeleton =
        skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M) ∧
      (ao125_reconCommitment E P M).nounSizeBound = E.Λ ∧
        (ao125_reconCommitment E P M).nounSizeBound ≤ E.Λ :=
  ⟨rfl, rfl, le_rfl⟩

/-- **The census field's exact object, from the check at the reconstruction commitment.**  No
identification hypothesis, no scalar hypothesis: at this commitment they are `rfl` and `le_rfl`.
Only the check, the paper's `cons` equations, and `1 ≤ E.Λ`.

**This is not an inhabitation.**  `CanonicalCommitmentCheck` is a hypothesis, held by no field of
`E`, `P`, `M`, `Data` or `CommitmentResidual`; `censusRecordPremises_still_five_here` is unchanged. -/
theorem ao125_census_of_check_at_reconCommitment {p : ℕ}
    (E : BuildableNockExecution F K) (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (hΛ : 1 ≤ E.Λ)
    (h : CanonicalCommitmentCheck p (ao125_reconCommitment E P M))
    (hc : ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      RowCellIdentities s) :
    EdgeComparisonCensus.CombinedSkeletonCensus K
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ :=
  Batch140.b140_census_of_canonicalCommitmentCheck (K := K) h hΛ hc

/-- **…and why that is a restatement rather than a reduction.**  Nothing has been made
smaller. -/
theorem ao125_check_at_reconCommitment_entails_the_residual {p : ℕ}
    (E : BuildableNockExecution F K) (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (hΛ : 1 ≤ E.Λ)
    (h : CanonicalCommitmentCheck p (ao125_reconCommitment E P M)) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      RowLeafWindow E.Λ s :=
  Batch140.b140_rowLeafWindow_of_canonicalCommitmentCheck h hΛ

/-! ## §D/§E. Two witnesses: the scalar tie is load-bearing, and the check is not the identities

Both the paper cites in this section —
> on `atomRow` and on `wideRow`, each of which sets `state :=.s1` and is described as an `OP_1`
> row — should be read as **the paper **.  `.s1` is `OP_1` by `ComputeTable.lean:140-150`
> (`State.toNat.s1 = 1`).
>
> **No mathematical consequence.**  Neither witness's proofs read the opcode.  They read only
> `ComputeTable.fanoutComp.s1 = 0` (`NockVM.lean:157-159`),
> `Nock.Framework.recordCount.s1 = 1` (`NockInstances.lean:61-63`) and
> `hasTailDecomposition.s1 = false` (`SemanticStrategy.lean:46-48`), all three re-measured at
> source here.  This is a claim-hygiene repair, not a proof repair; no statement, name, proof or
> definition in this file changes. -/

section Witnesses

/-- An `OP_1` row whose every committed noun is `.atom 0`.  `RowCellIdentities.formula_cons` demands
a *cell*, so it fails; the canonical check passes at any positive prime and any `1 ≤ bound`. -/
def atomRow : ComputeRowSkeleton where
  state := .s1
  subject := .atom 0
  formula := .atom 0
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩

/-- An `OP_1` row whose formula is a two-leaf cell and whose `dec` halves are atoms.  It *satisfies*
`RowCellIdentities`, and the canonical check passes at committed bound `2`, while `RowLeafWindow 1`
fails. -/
def wideRow : ComputeRowSkeleton where
  state := .s1
  subject := .atom 0
  formula := .cell (.atom 0) (.atom 0)
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩

def atomSkeleton : SemanticSkeleton where
  computeTree := .node atomRow []
  memoryForest := []

def wideSkeleton : SemanticSkeleton where
  computeTree := .node wideRow []
  memoryForest := []

theorem atomSkeleton_computeRows :
    computeSkeletonRows atomSkeleton = [atomRow] := by
  unfold computeSkeletonRows atomSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

theorem wideSkeleton_computeRows :
    computeSkeletonRows wideSkeleton = [wideRow] := by
  unfold computeSkeletonRows wideSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

theorem atomSkeleton_memoryRows :
    memorySkeletonRows atomSkeleton = [] := by
  simp [memorySkeletonRows, atomSkeleton, bfsForest_nil]

theorem wideSkeleton_memoryRows :
    memorySkeletonRows wideSkeleton = [] := by
  simp [memorySkeletonRows, wideSkeleton, bfsForest_nil]

theorem atomRow_slotNoun (a : ComputeSlotAddress) :
    computeSlotNoun atomRow a = .atom 0 := by
  cases a with
  | subject => rfl
  | formula => rfl
  | evaluation => rfl
  | dec slot =>
      show P8Census.skeletonDec atomRow slot = .atom 0
      unfold P8Census.skeletonDec
      split <;> rfl
  | sub i slot =>
      show P8Census.skeletonSubformula atomRow i slot = .atom 0
      unfold P8Census.skeletonSubformula
      split <;> rfl
  | memRec i slot =>
      show (if h : (i : ℕ) < Nock.Framework.recordCount atomRow.state
        then memRecSkeletonNoun (atomRow.memoryRecord i h) slot else .atom 0) = .atom 0
      split
      · cases slot <;> rfl
      · rfl

theorem wideRow_slotNoun_cases (a : ComputeSlotAddress) :
    computeSlotNoun wideRow a = .atom 0 ∨
      computeSlotNoun wideRow a = .cell (.atom 0) (.atom 0) := by
  cases a with
  | subject => exact Or.inl rfl
  | formula => exact Or.inr rfl
  | evaluation => exact Or.inl rfl
  | dec slot =>
      refine Or.inl ?_
      show P8Census.skeletonDec wideRow slot = .atom 0
      unfold P8Census.skeletonDec
      split <;> rfl
  | sub i slot =>
      refine Or.inl ?_
      show P8Census.skeletonSubformula wideRow i slot = .atom 0
      unfold P8Census.skeletonSubformula
      split <;> rfl
  | memRec i slot =>
      refine Or.inl ?_
      show (if h : (i : ℕ) < Nock.Framework.recordCount wideRow.state
        then memRecSkeletonNoun (wideRow.memoryRecord i h) slot else .atom 0) = .atom 0
      split
      · cases slot <;> rfl
      · rfl

theorem atomCommitment_check : CanonicalCommitmentCheck 2 ⟨atomSkeleton, 1⟩ := by
  intro n hn
  have hzero : n = .atom 0 := by
    unfold commitmentNouns at hn
    rw [List.mem_append] at hn
    rcases hn with hn | hn
    · rw [List.mem_flatMap] at hn
      obtain ⟨s, hs, hns⟩ := hn
      show n = .atom 0
      rw [show (⟨atomSkeleton, 1⟩ : SkeletonCommitment).skeleton = atomSkeleton from rfl,
        atomSkeleton_computeRows, List.mem_singleton] at hs
      subst hs
      unfold commitmentComputeRowNouns at hns
      rw [List.mem_map] at hns
      obtain ⟨a, _, rfl⟩ := hns
      exact atomRow_slotNoun a
    · rw [List.mem_flatMap] at hn
      obtain ⟨s, hs, _⟩ := hn
      rw [show (⟨atomSkeleton, 1⟩ : SkeletonCommitment).skeleton = atomSkeleton from rfl,
        atomSkeleton_memoryRows] at hs
      simp at hs
  subst hzero
  exact ⟨by decide, by decide⟩

theorem wideCommitment_check : CanonicalCommitmentCheck 2 ⟨wideSkeleton, 2⟩ := by
  intro n hn
  unfold commitmentNouns at hn
  rw [List.mem_append] at hn
  rcases hn with hn | hn
  · rw [List.mem_flatMap] at hn
    obtain ⟨s, hs, hns⟩ := hn
    rw [show (⟨wideSkeleton, 2⟩ : SkeletonCommitment).skeleton = wideSkeleton from rfl,
      wideSkeleton_computeRows, List.mem_singleton] at hs
    subst hs
    unfold commitmentComputeRowNouns at hns
    rw [List.mem_map] at hns
    obtain ⟨a, _, rfl⟩ := hns
    rcases wideRow_slotNoun_cases a with h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩
  · rw [List.mem_flatMap] at hn
    obtain ⟨s, hs, _⟩ := hn
    rw [show (⟨wideSkeleton, 2⟩ : SkeletonCommitment).skeleton = wideSkeleton from rfl,
      wideSkeleton_memoryRows] at hs
    simp at hs

/-- **(c) CONFIRMED, with a witness.**  The canonical check holds on an all-atom `OP_1` commitment
while `RowCellIdentities` fails at its only row: `formula_cons` demands
`s.formula =.cell (dec.f_h) (dec.f_t)`, a *cell*, and the check bounds each `dec` slot separately
while the census compares the formula against their `cons` cell, whose leaf count is the sum. -/
theorem ao125_check_does_not_subsume_rowCellIdentities :
    CanonicalCommitmentCheck 2 ⟨atomSkeleton, 1⟩ ∧
      ¬ (∀ s ∈ computeSkeletonRows atomSkeleton, RowCellIdentities s) := by
  refine ⟨atomCommitment_check, ?_⟩
  intro h
  have hrow : atomRow ∈ computeSkeletonRows atomSkeleton := by
    rw [atomSkeleton_computeRows]; exact List.mem_singleton_self _
  have := (h atomRow hrow).formula_cons
  simp [atomRow, P8Census.skeletonDec] at this

/-- **(b) is load-bearing, with a witness.**  A commitment can satisfy `CanonicalCommitmentCheck` at
its *own* committed bound and still fail `RowLeafWindow Λ` at a smaller `Λ`.  So
`C.nounSizeBound ≤ E.Λ` cannot be dropped, and — `SkeletonCommitment` having no invariant and
`Data.nounSizeBound`/`Data.Λ` being two unrelated bare scalars — it is not free in general. -/
theorem ao125_nounSizeBound_is_load_bearing :
    CanonicalCommitmentCheck 2 ⟨wideSkeleton, 2⟩ ∧
      ¬ (⟨wideSkeleton, 2⟩ : SkeletonCommitment).nounSizeBound ≤ 1 ∧
        ¬ (∀ s ∈ computeSkeletonRows wideSkeleton, RowLeafWindow 1 s) := by
  refine ⟨wideCommitment_check, by decide, ?_⟩
  intro h
  have hrow : wideRow ∈ computeSkeletonRows wideSkeleton := by
    rw [wideSkeleton_computeRows]; exact List.mem_singleton_self _
  have := (h wideRow hrow).2.1
  simp [wideRow, Noun.leaves] at this

end Witnesses

/-! ## §D (positive half). The scalar tie IS free on the honest assembly path -/

/-- **(b) on the `dataOfCensus` path: free.**  `censusAssemblyOf` sets `nounSizeBound := E.Λ` and
`dataOf` sets `Λ := E.Λ`, so the two committed scalars are the same natural number by `rfl` and the
inequality is `le_rfl`.  Compare `ao125_nounSizeBound_is_load_bearing`, which shows this is a
property of *that path* and not of the structure. -/
theorem ao125_nounSizeBound_le_Lambda_on_the_dataOfCensus_path
    [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (C : CensusRecordPremises E P M)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOfCensus E P M C hln).nounSizeBound = E.Λ ∧
      (dataOfCensus E P M C hln).Λ = E.Λ ∧
        (dataOfCensus E P M C hln).nounSizeBound ≤ (dataOfCensus E P M C hln).Λ :=
  ⟨rfl, rfl, le_rfl⟩

/-! ## §F. `CommitmentResidual` inhabitation -/

section Inhabitation

variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- **`CommitmentResidual E` is INHABITED whenever `Data E` is.**  `Data` is inhabited at three
semantically distinct executions in this build, so a wire into
`CommitmentResidual` does not wire into an empty structure. -/
theorem ao125_commitmentResidual_inhabited_from_data
    {E : BuildableNockExecution F K} (D : Data E) :
    Nonempty (BuildablePackage.CommitmentResidual E) :=
  ⟨commitmentResidualOfZero D⟩

/-- What *is* unavailable is the strictly different **generic constructor** `∀ E, CommitmentResidual E`,
which would force the strict `q` pin at every buildable execution.  Re-exported so the distinction
between "uninhabited" and "no universal constructor" rests on a statement in this file.
**Unavailable is not refuted** : no `E : BuildableNockExecution` with `E.q ≠ ringChar K` is
exhibited anywhere in the build, so this consequence is not shown false. -/
theorem ao125_no_generic_commitmentResidual_constructor
    (g : ∀ E : BuildableNockExecution F K, BuildablePackage.CommitmentResidual E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  fun E => (g E).q_eq_ringChar

end Inhabitation

/-! ## §G. `census`'s terminal description, and the carrier eta re-checks -/

/-- **The terminal description of the `census` residual, as a compiled statement.**  Object: the
per-row leaf window of `Def[Nock Program]` on the *reconstruction*.  Quantifier: `∀ s ∈
computeSkeletonRows (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M))`, a bounded
quantification over the committed compute rows — **not** over seeds, nouns, or field elements.
Classification: `paperProtocol`, unchanged by this pass.

This theorem states the reduction in the exact shape the terminal description names: the window at
that quantifier, plus the paper's `cons` equations and `1 ≤ E.Λ`, gives the census field.  It is a
conditional, and both hypotheses are hypotheses. -/
theorem ao125_census_terminal_description
    (E : BuildableNockExecution F K) (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (hΛ : 1 ≤ E.Λ)
    (hc : ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      RowCellIdentities s)
    (hw : ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      RowLeafWindow E.Λ s) :
    EdgeComparisonCensus.CombinedSkeletonCensus K
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ :=
  census_of_leafWindow _ _ hΛ hc hw

/-- The five census extras are still five named fields. -/
theorem ao125_censusRecordPremises_still_five {E : BuildableNockExecution F K}
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
theorem ao125_residualPremises_still_four {E : BuildableNockExecution F K}
    (P : ResidualPremises E) :
    P =
      { axisAtoms := P.axisAtoms
        inactiveDec := P.inactiveDec
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

#print axioms ao125_bindsAt_of_commitmentResidual
#print axioms ao125_a2_is_an_equivalence
#print axioms ao125_identification_reduces_to_node_equality
#print axioms ao125_published_commitment_is_the_data_pair
#print axioms ao125_reconCommitment_wires_are_free
#print axioms ao125_census_of_check_at_reconCommitment
#print axioms ao125_check_at_reconCommitment_entails_the_residual
#print axioms atomSkeleton_computeRows
#print axioms wideSkeleton_computeRows
#print axioms atomCommitment_check
#print axioms wideCommitment_check
#print axioms ao125_check_does_not_subsume_rowCellIdentities
#print axioms ao125_nounSizeBound_is_load_bearing
#print axioms ao125_nounSizeBound_le_Lambda_on_the_dataOfCensus_path
#print axioms ao125_commitmentResidual_inhabited_from_data
#print axioms ao125_no_generic_commitmentResidual_constructor
#print axioms ao125_census_terminal_description
#print axioms ao125_censusRecordPremises_still_five
#print axioms ao125_residualPremises_still_four

end

end Nock.RedTeam.AO125
