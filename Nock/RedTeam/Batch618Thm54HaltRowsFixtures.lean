import Nock.RedTeam.Batch72Thm54UniversalOptimizedChips
import Nock.RedTeam.Batch77Thm54UniversalPackage
import Nock.RedTeam.Batch86Thm54DistinctCensusPhaseCorrect
import Nock.NockVMROM.Thm54.MemoryHaltRowsBase

/-!
This file discharges the premise and restores the unconditional shapes.  Lemma file only; no
production declaration changes.

**How the premise is discharged.**  Neither fixture is a `TraceGen` output: the F73
`BuildableConcrete.concreteExecution` and the F97 `DistinctCensusExecution.execD` are hand-built
row lists, so `TraceGen.genMemForestFromTree_halt_leaf_base` (`GenMemAtomFill.lean`) does not
apply to them literally.  Its content — a skeleton `halt` row's parent is an atom and
`enc z (atom k)` has leaf `(k : K)` — reaches them through the committed layer instead:
`haltRowsBase_of_residual` is the `CommitmentResidual` analogue of
`MemoryHaltLeavesHonest.objects_haltRowsBase` (scan + row frame + shape match at the honest seed,
transported along `honest_specialization`).  Both fixtures have a residual
(`BuildablePackage.Concrete.residual73`, `DistinctCensusPhaseCorrect.residualHonestQ`), giving
`f73_haltRowsBase` and `distinctCensus_haltRowsBase`.  (Production already has the F73 instance
row by row, `BuildableChips.Concrete.concrete_haltRowsBase`; `f73_haltRowsBase` is an independent
route to the same proposition.)

**Receipts restored.**

* `Batch77.arbitrary_tuple_chip_path` is generic in `E` but already takes
  `R : CommitmentResidual E`, so the premise is discharged *generically* from `R`:
  `arbitrary_tuple_chip_path_unconditional` is `∀ E` with `hhalt` removed and nothing added.
* `Batch86.alternate_chip_input_is_satisfying_and_writes_two` is an F97 fixture receipt:
  `alternate_chip_input_is_satisfying_and_writes_two_unconditional`.
* `Batch72.same_execution_full_receipt` at the F73 fixture (`I` still arbitrary):
  `same_execution_full_receipt_f73_unconditional`; also its line origin, paired record layout and
  `C'` coherence premises are discharged from the fixture.
* `Batch72.symbolic_multirow_surface` at the F97 distinct-census fixture:
  `symbolic_multirow_surface_distinctCensus_unconditional`.  Not at F73: the receipt requires
  `2 ≤ E.cfg.compRows` and the F73 fixture has one compute row, so an F73 instance would be vacuous.

**What stays conditional, and why.**  `Batch72.symbolic_multirow_surface` and
`Batch72.same_execution_full_receipt` quantify over an arbitrary `E : BuildableNockExecution F K`
with *no* committed layer.  No field of `BuildableNockExecution` states `HaltRowsBase`, and the
only derivations of it in the tree (`haltRowsBase_of_checks`, `objects_haltRowsBase`, the
row-by-row fixture proofs, the generator's `genMemForestFromTree_halt_leaf_base`) all go through a
skeleton binding (`BindMemoryRow`) or a concrete row list — data a bare `E` does not carry.  So the
generic receipts keep `hhalt`; no carrier field is added to `BuildableNockExecution` (out of scope
for a lemma file, and it would change the production structure).
Wherever a `CommitmentResidual E` is in hand the premise is a theorem (`haltRowsBase_of_residual`),
and every package has it (`MemoryHaltLeavesHonest.objects_haltRowsBase`).

Scope: fixture claims are "at F73" / "at F97 distinct census"; only
`haltRowsBase_of_residual` and `arbitrary_tuple_chip_path_unconditional` are generic.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch618

open scoped Classical Polynomial
open Module Polynomial
open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage

noncomputable section

/-! ## A. Generic: a committed layer gives `HaltRowsBase` -/

section Generic

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-- **A `CommitmentResidual` gives `HaltRowsBase`** — the residual analogue of
`MemoryHaltLeavesHonest.objects_haltRowsBase`: the committed scan / row-frame / shape checks at the
honest seed bind every memory row to its skeleton row, and `honest_specialization` identifies that
specialized execution with `E.exec`. -/
theorem haltRowsBase_of_residual {E : BuildableNockExecution F K} (R : CommitmentResidual E) :
    MemoryHaltLeavesHonest.HaltRowsBase (F := F) E.exec := by
  have hrows := MemoryHaltLeavesHonest.haltRowsBase_of_checks (F := F)
    (R.shapeMatch R.honestSeed R.honestSeed_ne R.honestAlpha E.cfg.challenges.lam)
    (R.rowFrame R.honestSeed R.honestSeed_ne R.honestAlpha E.cfg.challenges.lam)
    (R.scan R.honestSeed R.honestSeed_ne R.honestAlpha E.cfg.challenges.lam)
  rw [R.honest_specialization] at hrows
  exact hrows

variable [DecidableEq F]

/-- **`Batch77.arbitrary_tuple_chip_path`, `hhalt` removed, still `∀ E`.**  The receipt already
takes the committed layer `R`, which discharges the premise (`haltRowsBase_of_residual`). -/
theorem arbitrary_tuple_chip_path_unconditional
    (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (c d : FinalComputeChallengeTuple K)
    (hC : E.exec.CprimeCoherent)
    (haxc : FormRAxisBound (sampledAssignment E (I.withComputeChallenges c))
      (I.withComputeChallenges c).basis)
    (haxd : FormRAxisBound (sampledAssignment E (I.withComputeChallenges d))
      (I.withComputeChallenges d).basis)
    (hbasis : FormRBasis I.basis)
    (hwidth : FormRWidth F) :
    ExactFinalChallengeCoordinatesWith I.basis
        (sampledAssignment E (I.withComputeChallenges c)) c
        (computeChallenge E (I.withComputeChallenges c)) ∧
      BuildableTraceSatisfaction
        (buildTopology E (I.withComputeChallenges c))
        (buildTraces E (I.withComputeChallenges c)) ∧
      BuildableTraceSatisfaction
        (buildTopology E (I.withComputeChallenges d))
        (buildTraces E (I.withComputeChallenges d)) :=
  Nock.RedTeam.Batch77.arbitrary_tuple_chip_path E I R hprl hmore hord hordM c d
    hmore hord hordM hC haxc haxd hbasis hwidth (haltRowsBase_of_residual R)

end Generic

/-! ## B. The F73 fixture (`BuildableConcrete.concreteExecution`) -/

section F73

open Nock.NockVMROM.Thm54.ConcreteStrictPackage

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance prime73 : Fact (Nat.Prime 73) := ⟨by norm_num⟩
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- **`HaltRowsBase` at the F73 fixture**, through its committed layer `residual73`. -/
theorem f73_haltRowsBase :
    MemoryHaltLeavesHonest.HaltRowsBase (F := F73) BuildableConcrete.concreteExecution.exec :=
  haltRowsBase_of_residual BuildablePackage.Concrete.residual73

/-- **`Batch72.same_execution_full_receipt` at F73, unconditional in `hhalt`** (and in the line
origin, paired record layout and `C'` coherence, all discharged from the fixture).  The backend
input `I` stays arbitrary. -/
theorem same_execution_full_receipt_f73_unconditional
    (I : Inputs BuildableConcrete.concreteExecution)
    (hmore : BuildableAxisWitness.LaterSeedZeros BuildableConcrete.concreteExecution)
    (hord : 2 ≤ BuildableConcrete.concreteExecution.cfg.compRows →
      BuildableConcrete.concreteExecution.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ BuildableConcrete.concreteExecution.cfg.memRows →
      BuildableConcrete.concreteExecution.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hax : FormRAxisBound (sampledAssignment BuildableConcrete.concreteExecution I) I.basis)
    (hbasis : FormRBasis I.basis)
    (hwidth : FormRWidth F73) :
    let E := BuildableConcrete.concreteExecution
    (sampledAssignment E I).sampled.records.requests = E.exec.derivedRequestIO ∧
      (sampledAssignment E I).sampled.records.responses = E.exec.derivedResponseIO ∧
      (buildTopology E I).rawFamily.problem = ⟨E.cfg, E.exec⟩ ∧
      (buildTopology E I).computeChip =
        ProductionNamedComputeRAP E.cfg.compRows_pos (computeNodes E I) I.basis
          (computeChallenge E I) (computePublic E I) I.orbit ∧
      (buildTopology E I).memoryChip =
        namedFinalMemoryRAP E.cfg.memRows_pos (memoryNodes E I) I.basis
          (memoryChallenge E I) (memoryPublic E I) I.orbit E.cfg.kMem ∧
      (buildTraces E I).compute =
        OptimizedComputeFinalTrace.correctedCanonicalFinalTrace
          (sampledAssignment E I) E.cfg.compRows_pos (computeNodes E I) I.basis
          (computeChallenge E I) (computePublic E I) I.orbit ∧
      (buildTraces E I).memory =
        OptimizedMemoryCanonicalSatisfaction.canonicalFinalMemoryTrace
          (sampledAssignment E I) (memoryNodes E I) I.basis
          (memoryChallenge E I) (memoryPublic E I) I.orbit ∧
      BuildableTraceSatisfaction (buildTopology E I) (buildTraces E I) :=
  Nock.RedTeam.Batch72.same_execution_full_receipt BuildableConcrete.concreteExecution I
    BuildableChips.Concrete.concrete_line_origin BuildableChips.Concrete.concrete_prl
    hmore hord hordM
    (ConcreteStrictPackage.execution_cprimeCoherent ConcreteStrictPackage.honestSeed
      ConcreteStrictPackage.honestAlpha)
    hax hbasis hwidth f73_haltRowsBase

end F73

/-! ## C. The F97 distinct-census fixture (`DistinctCensusExecution.execD`) -/

section F97

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusCommitment
open Nock.NockVMROM.Thm54.DistinctCensusPhaseCorrect
open Nock.NockVMROM.Thm54.DistinctCensusHonestArrays
open Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)

/-- **`HaltRowsBase` at the F97 distinct-census fixture**, through its committed layer
`residualHonestQ`. -/
theorem distinctCensus_haltRowsBase :
    MemoryHaltLeavesHonest.HaltRowsBase (F := F97) (distinctCensusExecution hfirstD).exec :=
  haltRowsBase_of_residual (residualHonestQ hfirstD)

/-- **`Batch86.alternate_chip_input_is_satisfying_and_writes_two`, unconditional in `hhalt`.** -/
theorem alternate_chip_input_is_satisfying_and_writes_two_unconditional
    (hrootAt : ∀ a g : K97cubic,
      (packageQ hfirstD).strategy.RootAxisBoundaryAt
        (nprSeed (coinQ a g)) seedH_ne (alphaM (coinQ a g)))
    (hax : FormRAxisBound
      (sampledAssignment (distinctCensusExecution hfirstD)
        (Nock.RedTeam.Batch86.alternateInputsQ hfirstD))
      (Nock.RedTeam.Batch86.alternateInputsQ hfirstD).basis)
    (hbasis : FormRBasis (Nock.RedTeam.Batch86.alternateInputsQ hfirstD).basis)
    (hwidth : FormRWidth F97) :
    BuildableTraceSatisfaction
        (buildTopology (distinctCensusExecution hfirstD)
          (Nock.RedTeam.Batch86.alternateInputsQ hfirstD))
        (buildTraces (distinctCensusExecution hfirstD)
          (Nock.RedTeam.Batch86.alternateInputsQ hfirstD)) ∧
      computeChallenge (distinctCensusExecution hfirstD)
          (Nock.RedTeam.Batch86.alternateInputsQ hfirstD)
        OptimizedComputeSubstitution.finalScalarChallengeBase = 0 :=
  Nock.RedTeam.Batch86.alternate_chip_input_is_satisfying_and_writes_two hfirstD hrootAt
    hax hbasis hwidth (distinctCensus_haltRowsBase hfirstD)

/-- **`Batch72.symbolic_multirow_surface` at the F97 distinct-census fixture (three compute rows,
so `2 ≤ compRows` holds and the instance is not vacuous), unconditional in `hhalt`.**  The
multi-row, line-origin, record-layout, later-seed and `C'` premises are discharged from the
fixture; the backend input `I` stays arbitrary. -/
theorem symbolic_multirow_surface_distinctCensus_unconditional
    (I : Inputs (distinctCensusExecution hfirstD))
    (hord : 2 ≤ (distinctCensusExecution hfirstD).cfg.compRows →
      (distinctCensusExecution hfirstD).cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ (distinctCensusExecution hfirstD).cfg.memRows →
      (distinctCensusExecution hfirstD).cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hax : FormRAxisBound (sampledAssignment (distinctCensusExecution hfirstD) I) I.basis)
    (hbasis : FormRBasis I.basis)
    (hwidth : FormRWidth F97) :
    Nonempty (BuildableTopology (distinctCensusExecution hfirstD)) ∧
      Nonempty (BuildableTopologyTraces (buildTopology (distinctCensusExecution hfirstD) I)) ∧
      BuildableTraceSatisfaction (buildTopology (distinctCensusExecution hfirstD) I)
        (buildTraces (distinctCensusExecution hfirstD) I) :=
  Nock.RedTeam.Batch72.symbolic_multirow_surface (distinctCensusExecution hfirstD) I
    (by change 2 ≤ 3; norm_num)
    (by
      change (DistinctCensusExecution.execD.computePubAt
        ⟨0, DistinctCensusExecution.cfgD.compRows_pos⟩).ln_prev = 1
      rw [DistinctCensusExecution.computePubAtD_zero]
      rfl)
    DistinctCensusC1.pairedRecordLayout_distinctCensus
    (BuildableAxisWitness.hmore_of_kMem_le_one (distinctCensusExecution hfirstD)
      (by simp [distinctCensusExecution]; decide))
    hord hordM DistinctCensusExecution.execD_cprimeCoherent
    hax hbasis hwidth (distinctCensus_haltRowsBase hfirstD)

end F97

end

end Nock.RedTeam.Batch618

#print axioms Nock.RedTeam.Batch618.haltRowsBase_of_residual
#print axioms Nock.RedTeam.Batch618.arbitrary_tuple_chip_path_unconditional
#print axioms Nock.RedTeam.Batch618.f73_haltRowsBase
#print axioms Nock.RedTeam.Batch618.same_execution_full_receipt_f73_unconditional
#print axioms Nock.RedTeam.Batch618.distinctCensus_haltRowsBase
#print axioms Nock.RedTeam.Batch618.alternate_chip_input_is_satisfying_and_writes_two_unconditional
#print axioms Nock.RedTeam.Batch618.symbolic_multirow_surface_distinctCensus_unconditional
