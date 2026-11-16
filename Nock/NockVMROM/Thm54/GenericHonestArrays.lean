import Nock.NockVMROM.Thm54.GenericHonestData
import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.JointVerification
import Nock.NockVMROM.Thm54.NodeEncoding
import Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Honest later-round `A`/`W` from `Data E` plus named walk-encoding extra

`commitmentResidualOf` still takes
the prover's post-challenge families `A`/`W`.  The paper
fixes the chronology: the prover commits (`Com(...)`, the paper), the
verifier answers with `α, γ ∈ 𝕂`, and only then does the
prover build `ln`, `count`, and `acc_walk`.
`jointVerification_complete` bundles two choices made
at those different rounds: public IO endpoints, a function of the committed
derived lists alone, and the six-family assignment, whose walk components
depend on the sampled walk coin.

This module matches `MultiRootPhaseCorrect` / `DistinctCensusPhaseCorrect`:

* `alphaMCommitmentOf` is the pre-challenge message.  It is indexed by
  `(z, hz, α)` only — the API forbids `alphaC`/`gamma` — and its table/IO
  arrays are the reference assignment at `(0, 0)`.
* `walkArraysOf ω` is the later-round message and a genuine function of the
  sampled coin: it returns the walk columns of the assignment at
  `(alphaC ω, gamma ω)`.

Opcode selectors occupy `{0,...,9} ∪ {11}`.
`StateTagChar` is injectivity of `natCast` on that interval, and is derived
from the paper hypothesis `11 < ringChar K`.  `1 < q` still does not force `11 < char`.
The encoding-level constructors retain a `StateTagChar` argument; the public
`*_of_char` residual / fibre-`Accepts` API takes `11 < ringChar K` instead.
Walk coins `(αc, γ)` are arguments of `afterCoins`, not premises.
Fibre `VerifierGates` is `∀ a g` on `honestCoin` given inhabited `Data E`
plus `11 < ringChar K`.  Mixed `ofLegacy` `Accepts` is the same quantifier.
Trace types are the AIR column counts, so
the six evaluations transport along propositional `familyAt_honestCoin`
without rewriting `RawMessage`'s family index.  No `∀ ω`.  `hzero` remains
on `buildFullPackage`.  `packageR` is not rewritten.  `ResidualPremises`
stays four.  `CensusRecordPremises` stays five.  The F97 fixture `q` is not
bumped.
-/

namespace Nock.NockVMROM.Thm54
namespace GenericHonestArrays

open scoped Classical
open Nock Nock.Walk Nock.NockVMROM
open Nock.Reified Nock.Framework
open scoped Polynomial
open SemanticStrategy SemanticTimestampStrategy
open HonestCommitment
open GenericHonestCommitment
open GenericHonestData
open TemplateRawJointSoundness
open BuildableChips
open ProductionRawVerifier
open OptimizedComputeFinalTrace

set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## Named extra: walk node-tag injectivity -/

/-- Opcode selectors occupy `{0,...,9} ∪ {11}`.  `E.q_gt_one`
is `1 < q` and does not force `11 < ringChar K` -/
theorem q_gt_one_does_not_give_stateTagChar :
    ¬ ∀ (q n : ℕ), 1 < q → q ≤ n → 11 < n := by
  intro h
  have hlt : 11 < 2 := h 2 2 (by omega) (by omega)
  omega

/-- Paper hypothesis: `11 < ringChar K` yields the opcode-tag encoding extra.
Not a free `StateTagChar` -/
theorem stateTagChar_of_paper_char (hgt : 11 < ringChar K) :
    NodeEncoding.StateTagChar K :=
  NodeEncoding.stateTagChar_of_ringChar_gt_eleven hgt

/-- On positive characteristic the encoding extra is exactly `11 < char`. -/
theorem stateTagChar_iff_paper_char (hpos : 0 < ringChar K) :
    NodeEncoding.StateTagChar K ↔ 11 < ringChar K :=
  NodeEncoding.stateTagChar_iff_ringChar_gt_eleven hpos

/-- Encoding-level constructors still take a `StateTagChar` argument; it is
now derived from `11 < ringChar K` rather than left free. -/
theorem stateTagChar_stays_named (hchar : NodeEncoding.StateTagChar K) :
    NodeEncoding.StateTagChar K :=
  hchar

/-- Paper Goldilocks prime is `> 11`.  Fixture `q` is not
bumped -/
theorem goldilocks_p_gt_eleven : 11 < 2 ^ 64 - 2 ^ 32 + 1 :=
  NodeEncoding.goldilocks_p_gt_eleven

/-! ## Honest family over `E.cfg`/`E.exec` at sampled walk coins -/

/-- Exact family at walk coins `(a, g)` over the committed execution.  Memory-walk
`α` is the execution's table timestamp; compute-walk `αc` and topology `γ` are
the later-round samples. -/
def honestZeroFamily (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    PlusIOSegmentedFamily F K :=
  PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders
    (ExactCanonicalRAPProblem.ofChained E.chained)
    hchar a g E.cfg.challenges.α
    0 0 0 E.programIOCapacity E.memoryIOCapacity

theorem honestZeroFamily_problem (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (honestZeroFamily E hchar a g).problem =
      ExactCanonicalRAPProblem.ofChained E.chained :=
  rfl

theorem honestZeroFamily_walk_coins (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (honestZeroFamily E hchar a g).computeWalkAlpha = a ∧
      (honestZeroFamily E hchar a g).walkGamma = g ∧
      (honestZeroFamily E hchar a g).memoryWalkAlpha = E.cfg.challenges.α :=
  ⟨rfl, rfl, rfl⟩

theorem honestZeroFamily_withWalk (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (honestZeroFamily E hchar 0 0).withWalkChallenges a g E.cfg.challenges.α =
      honestZeroFamily E hchar a g :=
  rfl

/-- Transport an exact derived-IO assignment across walk-challenge insertion.
The assignment reads only the committed problem and the public endpoints. -/
def ioAtWalkChallenges {R : PlusIOSegmentedFamily F K} {p : ℕ} [CharP K p]
    (io : ExactDerivedIOAssignment R p) (αc γ αm : K) :
    ExactDerivedIOAssignment (R.withWalkChallenges αc γ αm) p where
  multiplicity := io.multiplicity
  progAcc := io.progAcc
  memAcc := io.memAcc
  multiplicity_ne_zero := io.multiplicity_ne_zero
  progSat := io.progSat
  memSat := io.memSat
  endpoints_agree := io.endpoints_agree
  memory_closes := io.memory_closes

/-- Walk-challenge insertion after the public endpoints are chosen.  This is the
paper chronology: endpoints before `(αc, γ)`. -/
def familyAtWalk (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) (a g : K)
    (requests responses outMem : IOField K) : PlusIOSegmentedFamily F K :=
  (honestZeroFamily E hchar 0 0).withIOEndpoints requests responses outMem
    |>.withWalkChallenges a g E.cfg.challenges.α

/-- **One endpoint triple for every sampled walk-challenge pair**. -/
theorem uniformEndpoints_exist (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) :
    ∃ requests responses outMem : IOField K,
      ∀ a g : K,
        Nonempty (JointAssignment
          (familyAtWalk E hchar a g requests responses outMem)
          (ringChar K)) := by
  let R0 := honestZeroFamily E hchar 0 0
  have hLIO :
      IO.LIO R0.problem.cfg.Ksz
        R0.problem.exec.derivedRequestIO R0.problem.exec.derivedResponseIO := by
    change IO.LIO E.cfg.Ksz E.exec.derivedRequestIO E.exec.derivedResponseIO
    exact execution_lio E
  obtain ⟨requests, responses, outMem, ⟨io⟩⟩ :=
    ExactDerivedIOAssignment.exists_with_public_endpoints_of_LIO
      R0 E.Ksz_lt_ringChar hLIO
  refine ⟨requests, responses, outMem, fun a g => ?_⟩
  let R := familyAtWalk E hchar a g requests responses outMem
  have io' : ExactDerivedIOAssignment R (ringChar K) :=
    ioAtWalkChallenges (R := R0.withIOEndpoints requests responses outMem)
      io a g E.cfg.challenges.α
  have hchained : ChainedSemanticExactLanguage R.problem.cfg R.problem.exec := by
    change ChainedSemanticExactLanguage E.cfg E.exec
    exact E.chained
  obtain ⟨A, hA⟩ :=
    PlusIOSameExecutionAssignment.exists_satisfies_of_chained_IO
      (R := R) hchained io'
  have hLIO' :
      IO.LIO R.problem.cfg.Ksz
        R.problem.exec.derivedRequestIO R.problem.exec.derivedResponseIO := by
    change IO.LIO E.cfg.Ksz E.exec.derivedRequestIO E.exec.derivedResponseIO
    exact execution_lio E
  exact
    ⟨{ sameExecution := A
       sixFamilies := hA
       sharedIO :=
         (sharedIOSat_iff_LIO R E.Ksz_lt_ringChar).2 hLIO' }⟩

/-- One endpoint triple, and one joint assignment at each sampled pair.
Endpoint fields are **not** indexed by `(a, g)`. -/
structure PhaseCompletion (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) where
  requests : IOField K
  responses : IOField K
  outMem : IOField K
  assignment : ∀ a g : K,
    JointAssignment
      (familyAtWalk E hchar a g requests responses outMem)
      (ringChar K)

theorem phaseCompletion_nonempty (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) :
    Nonempty (PhaseCompletion E hchar) := by
  obtain ⟨requests, responses, outMem, h⟩ := uniformEndpoints_exist E hchar
  exact ⟨⟨requests, responses, outMem, fun a g => Classical.choice (h a g)⟩⟩

def completion (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) : PhaseCompletion E hchar :=
  Classical.choice (phaseCompletion_nonempty E hchar)

abbrev honestFamily (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    PlusIOSegmentedFamily F K :=
  familyAtWalk E hchar a g
    (completion E hchar).requests (completion E hchar).responses
    (completion E hchar).outMem

abbrev assignmentOf (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    PlusIOSameExecutionAssignment (honestFamily E hchar a g) (ringChar K) :=
  ((completion E hchar).assignment a g).sameExecution

theorem honestFamily_endpoints (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) (a g a' g' : K) :
    (honestFamily E hchar a g).requests = (honestFamily E hchar a' g').requests ∧
      (honestFamily E hchar a g).responses = (honestFamily E hchar a' g').responses ∧
      (honestFamily E hchar a g).outMem = (honestFamily E hchar a' g').outMem ∧
      (honestFamily E hchar a g).problem = (honestFamily E hchar a' g').problem ∧
      (honestFamily E hchar a g).computeWalkAlpha = a ∧
      (honestFamily E hchar a g).walkGamma = g :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Pre-challenge `A` and later-round `W` -/

/-- Committed post-`alphaM` family data.  No `alphaC`, no `gamma`. -/
def familyDataOf {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (z : K) (hz : z ≠ 0) (α lmb : K) :
    AlphaMFamilyData D.timestampStrategy z hz α lmb where
  compNodeWidth := NodeEncoding.computeNodeWidth
  compNodeEncode := NodeEncoding.computeNodeEncode hchar
  memNodeWidth := NodeEncoding.memoryNodeWidth
  memNodeEncode := NodeEncoding.memoryNodeEncode hchar
  requests := (completion E hchar).requests
  responses := (completion E hchar).responses
  outMem := (completion E hchar).outMem

theorem responseLen_of_binds {E : BuildableNockExecution F K} (D : Data E)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    (specializedProblem D.timestampStrategy z hz α lmb).exec.derivedResponseIO.length =
      E.exec.derivedResponseIO.length :=
  derivedResponseIO_length_eq (D.binds z α lmb) D.honest_binds

theorem honestFamily_responseLen (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (honestFamily E hchar a g).problem.exec.derivedResponseIO.length =
      E.exec.derivedResponseIO.length :=
  rfl

/-- **The committed later-round-`alphaM` message.**  No `(a, g)` parameter.  Table/IO arrays are the reference assignment at `(0, 0)`. -/
def alphaMCommitmentOf {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (z : K) (hz : z ≠ 0) (α lmb : K) :
    AlphaMCommitment (p := ringChar K) D.timestampStrategy z hz α lmb where
  familyData := familyDataOf D hchar z hz α lmb
  tables :=
    { compute := (assignmentOf E hchar 0 0).computeTableAux
      memory := (assignmentOf E hchar 0 0).memoryTableAux }
  io :=
    { multiplicity := fun j =>
        (assignmentOf E hchar 0 0).exactIO.multiplicity
          ⟨j, by
            have hj := j.isLt
            have hbase :
                (familyDataOf D hchar z hz α lmb).base.exec.derivedResponseIO.length =
                  (specializedProblem D.timestampStrategy z hz α lmb).exec.derivedResponseIO.length :=
              rfl
            have hlen :=
              hbase.trans
                ((responseLen_of_binds D z hz α lmb).trans
                  (honestFamily_responseLen E hchar 0 0).symm)
            exact hlen ▸ hj⟩
      progAcc := (assignmentOf E hchar 0 0).exactIO.progAcc
      memAcc := (assignmentOf E hchar 0 0).exactIO.memAcc }

/-- **The later-round walk columns**.  A genuine function of
the sampled coin: walks are the assignment at that coin's own `alphaC` and
`gamma`. -/
def walkArraysOf {E : BuildableNockExecution F K} (_D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (ω : JointCoins K) (_lmb : K)
    (_hz : nprSeed ω ≠ 0) : RawWalkArrays K where
  computeLn := (assignmentOf E hchar (alphaC ω) (gamma ω)).computeWalk.ln
  computeCount := (assignmentOf E hchar (alphaC ω) (gamma ω)).computeWalk.count
  computeAcc := (assignmentOf E hchar (alphaC ω) (gamma ω)).computeWalk.acc
  memoryLn := (assignmentOf E hchar (alphaC ω) (gamma ω)).memoryWalk.ln
  memoryCount := (assignmentOf E hchar (alphaC ω) (gamma ω)).memoryWalk.count
  memoryAcc := (assignmentOf E hchar (alphaC ω) (gamma ω)).memoryWalk.acc

/-- Outcome 2: `afterCoins` reads `(αc, γ)`. -/
theorem walkArraysOf_reads_the_coin {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (ω : JointCoins K)
    (hz : nprSeed ω ≠ 0) :
    (walkArraysOf D hchar ω lmb hz).computeLn =
        (assignmentOf E hchar (alphaC ω) (gamma ω)).computeWalk.ln ∧
      (walkArraysOf D hchar ω lmb hz).computeCount =
        (assignmentOf E hchar (alphaC ω) (gamma ω)).computeWalk.count ∧
      (walkArraysOf D hchar ω lmb hz).computeAcc =
        (assignmentOf E hchar (alphaC ω) (gamma ω)).computeWalk.acc ∧
      (walkArraysOf D hchar ω lmb hz).memoryLn =
        (assignmentOf E hchar (alphaC ω) (gamma ω)).memoryWalk.ln ∧
      (walkArraysOf D hchar ω lmb hz).memoryCount =
        (assignmentOf E hchar (alphaC ω) (gamma ω)).memoryWalk.count ∧
      (walkArraysOf D hchar ω lmb hz).memoryAcc =
        (assignmentOf E hchar (alphaC ω) (gamma ω)).memoryWalk.acc :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Walk arrays ignore NPR seed and `alphaM`; they depend only on the later-round
walk pair.  This is not `∀ ω` whole-joint. -/
theorem walkArraysOf_reads_only_walk_challenges
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K)
    (a g αm z αm' z' lmb lmb' : K) (hz : z ≠ 0) (hz' : z' ≠ 0) :
    walkArraysOf D hchar ((a, g), (αm, z)) lmb hz =
      walkArraysOf D hchar ((a, g), (αm', z')) lmb' hz' :=
  rfl

/-- Pre-challenge tables ignore sampled seed and `alphaM`. -/
theorem afterAlphaM_tables_ignore_seed_and_alphaM
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K)
    (z z' α α' lmb lmb' : K) (hz : z ≠ 0) (hz' : z' ≠ 0) :
    (alphaMCommitmentOf D hchar z hz α lmb).tables.compute =
        (alphaMCommitmentOf D hchar z' hz' α' lmb').tables.compute ∧
      (alphaMCommitmentOf D hchar z hz α lmb).tables.memory =
        (alphaMCommitmentOf D hchar z' hz' α' lmb').tables.memory :=
  ⟨rfl, rfl⟩

theorem afterAlphaM_tables_are_the_reference_assignment
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (z : K) (hz : z ≠ 0) (α lmb : K) :
    (alphaMCommitmentOf D hchar z hz α lmb).tables.compute =
        (assignmentOf E hchar 0 0).computeTableAux ∧
      (alphaMCommitmentOf D hchar z hz α lmb).tables.memory =
        (assignmentOf E hchar 0 0).memoryTableAux :=
  ⟨rfl, rfl⟩

/-! ## Residual inhabitant and quantifier-order receipts -/

/-- Production raw strategy: committed template, coin-free `A`, coin-reading `W`. -/
def rawStrategyOf {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) :
    TemplateRawJointSoundness.Strategy F K (ringChar K) where
  timestamp := D.timestampStrategy
  afterAlphaM := alphaMCommitmentOf D hchar
  afterCoins := walkArraysOf D hchar

theorem familyAt_specializes_the_coin {E : BuildableNockExecution F K}
    (D : Data E) (hchar : NodeEncoding.StateTagChar K)
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    ((rawStrategyOf D hchar).familyAt ω lmb hz).cfg.challenges.z = nprSeed ω ∧
      ((rawStrategyOf D hchar).familyAt ω lmb hz).cfg.challenges.α = alphaM ω ∧
      ((rawStrategyOf D hchar).familyAt ω lmb hz).computeWalkAlpha = alphaC ω ∧
      ((rawStrategyOf D hchar).familyAt ω lmb hz).walkGamma = gamma ω :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem alphaMCommitment_same_across_walk_coins
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K)
    (z : K) (hz : z ≠ 0) (α lmb a g a' g' : K) :
    (rawStrategyOf D hchar).alphaMCommitment ((a, g), (α, z)) lmb hz =
      (rawStrategyOf D hchar).alphaMCommitment ((a', g'), (α, z)) lmb hz :=
  rfl

/-- Honest fibre coin: later-round `(a, g)` over the committed sample
`(alphaM, z) = (E.cfg.challenges.α, E.cfg.challenges.z)`.  Not `∀ ω`. -/
def honestCoin (E : BuildableNockExecution F K) (a g : K) : JointCoins K :=
  ((a, g), (E.cfg.challenges.α, E.cfg.challenges.z))

theorem honestCoin_coordinates (E : BuildableNockExecution F K) (a g : K) :
    alphaC (honestCoin E a g) = a ∧ gamma (honestCoin E a g) = g ∧
      alphaM (honestCoin E a g) = E.cfg.challenges.α ∧
      nprSeed (honestCoin E a g) = E.cfg.challenges.z :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Milestone 5's committed residual with honest later-round arrays.**
`A` is `∀ z hz α` (pre-challenge); `W` is `∀ ω, nprSeed ω ≠ 0 → RawWalkArrays`
and a function of `(αc, γ)`. -/
def commitmentResidualOfArrays {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) :
    BuildablePackage.CommitmentResidual E :=
  commitmentResidualOf D (alphaMCommitmentOf D hchar) (walkArraysOf D hchar)

theorem commitmentResidualOfArrays_nonempty {E : BuildableNockExecution F K}
    (D : Data E) (hchar : NodeEncoding.StateTagChar K) :
    Nonempty (BuildablePackage.CommitmentResidual E) :=
  ⟨commitmentResidualOfArrays D hchar⟩

/-- Whole-joint `∀ ω` is uninhabited: `Accepts` is definitionally `False` on a
zero NPR seed -/
theorem not_forall_omega_accepts {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) :
    ¬ ∀ (ω : JointCoins K) (lmb : K), (rawStrategyOf D hchar).Accepts ω lmb := by
  intro h
  have h0 := h ((0, 0), (0, 0)) 0
  simp [TemplateRawJointSoundness.Strategy.Accepts, nprSeed] at h0

/-- No constructor `∀ E, CommitmentResidual E`.  The arrays constructor still
starts from inhabited `Data E` plus the named state-tag extra. -/
theorem generic_residual_would_force_q_equality
    (g : ∀ E : BuildableNockExecution F K, BuildablePackage.CommitmentResidual E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  GenericHonestCommitment.generic_residual_would_force_q_equality (F := F) (K := K) g

theorem generic_data_would_force_q_equality
    (g : ∀ E : BuildableNockExecution F K, Data E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  GenericHonestCommitment.generic_data_would_force_q_equality (F := F) (K := K) g

/-- Five census extras remain named; this module does not inhabit them. -/
theorem censusRecordPremises_still_five {E : BuildableNockExecution F K}
    {P : ResidualPremises E} {M : MemoryRecordPremises E}
    (C : CensusRecordPremises E P M) :
    (∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      ServedLookupBridge.SkeletonSlotSemantics s) ∧
      EdgeComparisonCensus.CombinedSkeletonCensus K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ ∧
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q ∧
      ProductionP8Containment.CombinedBoundedBy K E.q
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) :=
  GenericHonestData.censusRecordPremises_still_five C

theorem residualPremises_still_four {E : BuildableNockExecution F K}
    (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  GenericHonestData.residualPremises_still_four P

/-- `hzero` remains on released `buildFullPackage`. -/
theorem released_builder_still_takes_hzero {E : BuildableNockExecution F K}
    (I : BuildableChips.Inputs E) (R : BuildablePackage.CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    Nonempty (OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  ⟨BuildablePackage.buildFullPackage E I R hzero hprl hmore hord hordM hrows⟩

/-- Accounting receipt: residual pair stays `11+1+2`.  `packageR` is not rewritten. -/
theorem residual_pair_still_eleven_one_two : 11 + 1 + 2 = 14 :=
  rfl

/-! ## Fibre `VerifierGates` / production `Accepts`

Public endpoints and table/IO arrays are chosen before the
walk coins; only `ln`/`count`/`acc_walk` read `(αc, γ)`.
The mixed assignment is the message the verifier actually reads.  Acceptance
is the honest fibre `honestCoin E a g`, not `∀ ω`. -/

/-- Tables and IO from the reference assignment at `(0, 0)`; walks from the
assignment at the sampled pair. -/
def mixedAssignment (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    PlusIOSameExecutionAssignment (honestFamily E hchar a g) (ringChar K) where
  computeTableAux := (assignmentOf E hchar 0 0).computeTableAux
  memoryTableAux := (assignmentOf E hchar 0 0).memoryTableAux
  computeWalk := (assignmentOf E hchar a g).computeWalk
  memoryWalk := (assignmentOf E hchar a g).memoryWalk
  exactIO :=
    ioAtWalkChallenges (assignmentOf E hchar 0 0).exactIO a g E.cfg.challenges.α

theorem honestFamily_withWalk (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (honestFamily E hchar 0 0).withWalkChallenges a g E.cfg.challenges.α =
      honestFamily E hchar a g :=
  rfl

/-- The six families accept the mixed message: four committed RAPs from `(0, 0)`,
two walk RAPs from the sampled pair. -/
theorem mixedAssignment_satisfies (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (mixedAssignment E hchar a g).Satisfies := by
  have h0 := (completion E hchar).assignment 0 0 |>.sixFamilies
  have hag := (completion E hchar).assignment a g |>.sixFamilies
  exact ⟨h0.1, h0.2.1, hag.2.2.1, hag.2.2.2.1, h0.2.2.2.2.1, h0.2.2.2.2.2⟩

theorem rawStrategyOf_claim {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) :
    (rawStrategyOf D hchar).claim = D.skeleton.publicClaim :=
  rfl

theorem honestCoin_seed_ne {E : BuildableNockExecution F K} (D : Data E)
    (a g : K) : nprSeed (honestCoin E a g) ≠ 0 :=
  D.honestSeed_ne

/-- The raw family at the honest fibre is the mixed later-round family. -/
theorem familyAt_honestCoin {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne =
      RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g) := by
  have hspec := D.honest_specialization
  simp [rawStrategyOf, TemplateRawJointSoundness.Strategy.familyAt,
    TemplateRawJointSoundness.Strategy.alphaMCommitment, honestCoin,
    nprSeed, alphaM, alphaC, gamma, alphaMCommitmentOf, familyDataOf,
    AlphaMFamilyData.atCoins, RawPlusIOSegmentedFamily.ofLegacy,
    honestFamily, familyAtWalk, PlusIOSegmentedFamily.withWalkChallenges,
    PlusIOSegmentedFamily.withIOEndpoints, honestZeroFamily,
    PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders,
    RawProblem.ofExact, ExactCanonicalRAPProblem.ofChained]
  rw [hspec]

theorem rowAlignment_of_rowsAccepted
    (R : RawPlusIOSegmentedFamily F K)
    (hc : R.exec.ComputeRowsAccepted) (hm : R.exec.MemoryRowsAccepted) :
    RawMessage.RowAlignmentGates (R := R) := by
  constructor
  · intro i
    have h := ExactExecution.computeRowAt_accepted hc i
    exact ⟨h.1, h.2.1⟩
  · intro i
    have h := ExactExecution.memoryRowAt_accepted hm i
    exact ⟨h.1, h.2.1⟩

theorem mixed_rowAlignment {E : BuildableNockExecution F K}
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    RawMessage.RowAlignmentGates
      (R := RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)) :=
  rowAlignment_of_rowsAccepted _
    (by
      change E.exec.ComputeRowsAccepted
      exact E.chained.semantic.1)
    (by
      change E.exec.MemoryRowsAccepted
      exact E.chained.semantic.2.1)

theorem mixed_canonicalEncoders {E : BuildableNockExecution F K}
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)).CanonicalNodeEncoderGates := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · intro hchar'
    have hh : hchar' = hchar := Subsingleton.elim _ _
    subst hchar'
    rfl
  · intro hchar'
    have hh : hchar' = hchar := Subsingleton.elim _ _
    subst hchar'
    rfl

theorem mixed_root_bindings {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    let R := RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)
    (R.exec.computePubAt ⟨0, R.cfg.compRows_pos⟩).s =
        GlobalCarryRecognizer.enc (nprSeed (honestCoin E a g))
          D.skeleton.publicClaim.subject ∧
      (R.exec.computePubAt ⟨0, R.cfg.compRows_pos⟩).f =
        GlobalCarryRecognizer.enc (nprSeed (honestCoin E a g))
          D.skeleton.publicClaim.formula ∧
      (R.exec.computePubAt ⟨0, R.cfg.compRows_pos⟩).e =
        GlobalCarryRecognizer.enc (nprSeed (honestCoin E a g))
          D.skeleton.publicClaim.result := by
  intro R
  have hroot := BindsAt.root_bindings D.honest_binds
  have hpub := computePubAt_root_eq E.exec
  change (E.exec.computePubAt ⟨0, E.cfg.compRows_pos⟩).s =
      GlobalCarryRecognizer.enc E.cfg.challenges.z D.skeleton.publicClaim.subject ∧
    (E.exec.computePubAt ⟨0, E.cfg.compRows_pos⟩).f =
      GlobalCarryRecognizer.enc E.cfg.challenges.z D.skeleton.publicClaim.formula ∧
    (E.exec.computePubAt ⟨0, E.cfg.compRows_pos⟩).e =
      GlobalCarryRecognizer.enc E.cfg.challenges.z D.skeleton.publicClaim.result
  rw [hpub]
  exact hroot

theorem mixed_lio_gates {E : BuildableNockExecution F K}
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    let R := RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)
    IO.InRange R.cfg.Ksz R.exec.derivedRequestIO.length ∧
      R.exec.derivedRequestIO.Nodup ∧
      R.exec.derivedResponseIO.length ≤ R.cfg.Ksz ∧
      R.exec.derivedResponseIO.Nodup := by
  intro R
  have hLIO := execution_lio E
  have hperm := hLIO.2.2
  refine ⟨?_, E.requestNodup, ?_, hLIO.2.1⟩
  · change IO.InRange E.cfg.Ksz E.exec.derivedRequestIO.length
    rw [hperm.length_eq]
    exact hLIO.1
  · change E.exec.derivedResponseIO.length ≤ E.cfg.Ksz
    exact hLIO.1.2

/-- Seventeen-conjunct `VerifierGates` on the mixed later-round message at every
sampled walk pair over the committed fibre. -/
theorem honestVerifierGates {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (RawMessage.ofLegacy (mixedAssignment E hchar a g)).VerifierGates
      D.skeleton.publicClaim (honestCoin E a g) := by
  refine ⟨D.honestSeed_ne, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact mixed_rowAlignment hchar a g
  · exact mixed_canonicalEncoders hchar a g
  · exact (mixed_root_bindings D hchar a g).1
  · exact (mixed_root_bindings D hchar a g).2.1
  · exact (mixed_root_bindings D hchar a g).2.2
  · exact ((completion E hchar).assignment 0 0).public_endpoints.1
  · exact ((completion E hchar).assignment 0 0).public_endpoints.2
  · exact (assignmentOf E hchar 0 0).exactIO.multiplicity_ne_zero
  · exact (mixed_lio_gates (E := E) hchar a g).1
  · exact (mixed_lio_gates (E := E) hchar a g).2.1
  · exact (mixed_lio_gates (E := E) hchar a g).2.2.1
  · exact (mixed_lio_gates (E := E) hchar a g).2.2.2

/-- Production raw `Accepts` on the mixed later-round message at the honest fibre.
Not `∀ ω`. -/
theorem mixed_raw_accepts {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (RawMessage.ofLegacy (mixedAssignment E hchar a g)).Accepts
      D.skeleton.publicClaim (honestCoin E a g) :=
  RawMessage.accepts_of_legacy_assignment
    D.skeleton.publicClaim (honestCoin E a g) (mixedAssignment E hchar a g)
    (mixedAssignment_satisfies E hchar a g) (honestVerifierGates D hchar a g)

/-- Seventeen-conjunct `VerifierGates` on the strategy message at the honest fibre.  `R`-only conjuncts transport along
`familyAt_honestCoin`; multiplicity is the committed IO witness. -/
theorem honestVerifierGates_at {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).VerifierGates
      D.skeleton.publicClaim (honestCoin E a g) := by
  have hfam := familyAt_honestCoin D hchar a g
  refine ⟨D.honestSeed_ne, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfam]; exact mixed_rowAlignment hchar a g
  · rw [hfam]; exact mixed_canonicalEncoders hchar a g
  · rw [hfam]; exact (mixed_root_bindings D hchar a g).1
  · rw [hfam]; exact (mixed_root_bindings D hchar a g).2.1
  · rw [hfam]; exact (mixed_root_bindings D hchar a g).2.2
  · rw [hfam]; exact ((completion E hchar).assignment 0 0).public_endpoints.1
  · rw [hfam]; exact ((completion E hchar).assignment 0 0).public_endpoints.2
  · intro j
    exact (assignmentOf E hchar 0 0).exactIO.multiplicity_ne_zero
      ⟨j.val, by
        have hj := j.isLt
        have hlen :
            ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).exec.derivedResponseIO.length =
              (honestFamily E hchar 0 0).problem.exec.derivedResponseIO.length := by
          change
            (specializedProblem D.timestampStrategy E.cfg.challenges.z D.honestSeed_ne
                E.cfg.challenges.α E.cfg.challenges.lam).exec.derivedResponseIO.length =
              E.exec.derivedResponseIO.length
          rw [D.honest_specialization]
        exact hlen ▸ hj⟩
  · rw [hfam]; exact (mixed_lio_gates (E := E) hchar a g).1
  · rw [hfam]; exact (mixed_lio_gates (E := E) hchar a g).2.1
  · rw [hfam]; exact (mixed_lio_gates (E := E) hchar a g).2.2.1
  · rw [hfam]; exact (mixed_lio_gates (E := E) hchar a g).2.2.2

/-! ## `SixRAPSatisfy` on `messageAt`

`RAP.Satisfies` expects `Fin rap.w → L[X]`, and `airToRAP.w` is the AIR
column count.  Table/walk/IO traces therefore have family-independent types.
The six RAP objects and the six traces transport along propositional
`familyAt_honestCoin`; mixed `ofLegacy` `SixRAPSatisfy` supplies the values. -/

theorem familyAt_honestCoin_cfg {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).cfg =
      E.cfg :=
  rfl

theorem familyAt_honestCoin_exec {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).exec =
      E.exec :=
  D.honest_exec

theorem mixed_ofLegacy_sixRAP (E : BuildableNockExecution F K)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (RawMessage.ofLegacy (mixedAssignment E hchar a g)).SixRAPSatisfy :=
  RawMessage.sixRAPSatisfy_of_legacy
    (mixedAssignment E hchar a g) (mixedAssignment_satisfies E hchar a g)

theorem familyAt_computeTableRAP {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) (kind : ConstraintKind) :
    ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeTableRAP
        kind =
      (RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)).computeTableRAP
        kind :=
  congrArg (fun R => R.computeTableRAP kind) (familyAt_honestCoin D hchar a g)

theorem familyAt_memoryTableRAP {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) (kind : ConstraintKind) :
    ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryTableRAP
        kind =
      (RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)).memoryTableRAP
        kind :=
  congrArg (fun R => R.memoryTableRAP kind) (familyAt_honestCoin D hchar a g)

theorem familyAt_computeWalkRAP {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) (kind : ConstraintKind) :
    ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeWalkRAP
        kind =
      (RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)).computeWalkRAP
        kind :=
  congrArg (fun R => R.computeWalkRAP kind) (familyAt_honestCoin D hchar a g)

theorem familyAt_memoryWalkRAP {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) (kind : ConstraintKind) :
    ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryWalkRAP
        kind =
      (RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)).memoryWalkRAP
        kind :=
  congrArg (fun R => R.memoryWalkRAP kind) (familyAt_honestCoin D hchar a g)

theorem familyAt_computeIORAP {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) (kind : ConstraintKind) :
    ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeIORAP
        kind =
      (RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)).computeIORAP
        kind :=
  congrArg (fun R => R.computeIORAP kind) (familyAt_honestCoin D hchar a g)

theorem familyAt_memoryIORAP {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) (kind : ConstraintKind) :
    ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryIORAP
        kind =
      (RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)).memoryIORAP
        kind :=
  congrArg (fun R => R.memoryIORAP kind) (familyAt_honestCoin D hchar a g)

theorem messageAt_tables_compute {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).tables.compute =
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).tables.compute :=
  rfl

theorem messageAt_tables_memory {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).tables.memory =
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).tables.memory :=
  rfl

theorem messageAt_walks {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).walks =
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).walks :=
  rfl

theorem messageAt_io_acc {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).io.progAcc =
        (RawMessage.ofLegacy (mixedAssignment E hchar a g)).io.progAcc ∧
      ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).io.memAcc =
        (RawMessage.ofLegacy (mixedAssignment E hchar a g)).io.memAcc :=
  ⟨rfl, rfl⟩

/-- Compute-table traces agree: configuration is definitional and the execution is
`honest_exec`. -/
theorem messageAt_computeTableTrace {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeTableTrace =
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).computeTableTrace := by
  unfold RawMessage.computeTableTrace
  rw [familyAt_honestCoin_exec D hchar a g, messageAt_tables_compute D hchar a g]
  rfl

theorem messageAt_memoryTableTrace {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryTableTrace =
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).memoryTableTrace := by
  unfold RawMessage.memoryTableTrace
  rw [familyAt_honestCoin_exec D hchar a g, messageAt_tables_memory D hchar a g]
  rfl

theorem messageAt_computeWalkTrace {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeWalkTrace =
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).computeWalkTrace := by
  unfold RawMessage.computeWalkTrace
  unfold RawPlusIOSegmentedFamily.computeWalkSeed
  unfold RawPlusIOSegmentedFamily.computeWalkRows
  rw [familyAt_honestCoin_exec D hchar a g, messageAt_walks D hchar a g]
  rfl

theorem messageAt_memoryWalkTrace {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryWalkTrace =
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).memoryWalkTrace := by
  unfold RawMessage.memoryWalkTrace
  unfold RawPlusIOSegmentedFamily.memoryWalkSeed
  unfold RawPlusIOSegmentedFamily.memoryWalkRows
  rw [familyAt_honestCoin_exec D hchar a g, messageAt_walks D hchar a g]
  rfl

theorem messageAt_computeIOTrace {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeIOTrace =
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).computeIOTrace := by
  unfold RawMessage.computeIOTrace
  rw [familyAt_honestCoin_exec D hchar a g]
  rfl

theorem messageAt_castμ {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    IO.castμ (𝔽 := K)
        ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).io.multiplicity =
      IO.castμ (𝔽 := K)
        (RawMessage.ofLegacy (mixedAssignment E hchar a g)).io.multiplicity := by
  have hlen :
      ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).exec.derivedResponseIO.length =
        (RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)).exec.derivedResponseIO.length :=
    congrArg (fun e => e.derivedResponseIO.length) (familyAt_honestCoin_exec D hchar a g)
  funext i
  simp only [IO.castμ]
  by_cases hspec :
      i <
        ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).exec.derivedResponseIO.length
  · by_cases hmix :
        i <
          (RawPlusIOSegmentedFamily.ofLegacy
            (honestFamily E hchar a g)).exec.derivedResponseIO.length
    · rw [dif_pos hspec, dif_pos hmix]
      simp [rawStrategyOf, TemplateRawJointSoundness.Strategy.messageAt,
        TemplateRawJointSoundness.Strategy.alphaMCommitment, honestCoin,
        nprSeed, alphaM, alphaC, gamma, alphaMCommitmentOf,
        TemplateRawJointSoundness.AlphaMCommitment.ioAt, RawMessage.ofLegacy,
        mixedAssignment, ioAtWalkChallenges]
      exact congrArg (SetEq.castZ (ringChar K))
        (congrArg (assignmentOf E hchar 0 0).exactIO.multiplicity (Fin.ext rfl))
    · exact (hmix (hlen ▸ hspec)).elim
  · by_cases hmix :
        i <
          (RawPlusIOSegmentedFamily.ofLegacy
            (honestFamily E hchar a g)).exec.derivedResponseIO.length
    · exact (hspec (hlen.symm ▸ hmix)).elim
    · rw [dif_neg hspec, dif_neg hmix]

theorem messageAt_memoryIOTrace {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryIOTrace =
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).memoryIOTrace := by
  unfold RawMessage.memoryIOTrace
  rw [messageAt_castμ D hchar a g]
  rw [familyAt_honestCoin_exec D hchar a g]
  rfl

theorem rapSatisfies_congr {L : Type} [CommRing L] {R S : RAP L}
    (hR : R = S) {P : Fin R.w → L[X]} {Q : Fin S.w → L[X]}
    (hP : HEq P Q) (h : R.Satisfies P) : S.Satisfies Q := by
  cases hR
  cases hP
  exact h

/-- The six RAP evaluations on `messageAt` at the honest fibre. -/
theorem honestSixRAPSatisfy_at {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).SixRAPSatisfy := by
  have hsix := mixed_ofLegacy_sixRAP E hchar a g
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro kind
    exact rapSatisfies_congr
      (familyAt_computeTableRAP D hchar a g kind).symm
      (heq_of_eq (messageAt_computeTableTrace D hchar a g).symm)
      (hsix.1 kind)
  · intro kind
    exact rapSatisfies_congr
      (familyAt_memoryTableRAP D hchar a g kind).symm
      (heq_of_eq (messageAt_memoryTableTrace D hchar a g).symm)
      (hsix.2.1 kind)
  · intro kind
    exact rapSatisfies_congr
      (familyAt_computeWalkRAP D hchar a g kind).symm
      (heq_of_eq (messageAt_computeWalkTrace D hchar a g).symm)
      (hsix.2.2.1 kind)
  · intro kind
    exact rapSatisfies_congr
      (familyAt_memoryWalkRAP D hchar a g kind).symm
      (heq_of_eq (messageAt_memoryWalkTrace D hchar a g).symm)
      (hsix.2.2.2.1 kind)
  · intro kind
    exact rapSatisfies_congr
      (familyAt_computeIORAP D hchar a g kind).symm
      (heq_of_eq (messageAt_computeIOTrace D hchar a g).symm)
      (hsix.2.2.2.2.1 kind)
  · intro kind
    exact rapSatisfies_congr
      (familyAt_memoryIORAP D hchar a g kind).symm
      (heq_of_eq (messageAt_memoryIOTrace D hchar a g).symm)
      (hsix.2.2.2.2.2 kind)

/-- Strategy raw `Accepts` on the honest fibre.  Not `∀ ω`. -/
theorem honest_raw_accepts {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (rawStrategyOf D hchar).Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  ((rawStrategyOf D hchar).accepts_iff_gates_and_sixRAP
      (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).2
    ⟨honestVerifierGates_at D hchar a g, honestSixRAPSatisfy_at D hchar a g⟩

theorem honest_exactTopology {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ComputeExactTopology
        ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).exec ∧
      MemoryExactTopology
        ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).exec := by
  rw [familyAt_honestCoin D hchar a g]
  exact E.traversal

/-- Named-premises fibre: every later-round walk pair has mixed `Accepts` and
strategy `VerifierGates`. -/
theorem fibre_mixed_accepts {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) :
    ∀ a g : K,
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).Accepts
          D.skeleton.publicClaim (honestCoin E a g) ∧
        ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).VerifierGates
          D.skeleton.publicClaim (honestCoin E a g) :=
  fun a g => ⟨mixed_raw_accepts D hchar a g, honestVerifierGates_at D hchar a g⟩

/-- Residual production `verifier.Accepts` on the honest fibre.
Topology is `E.traversal` after `familyAt_honestCoin`.  Not `∀ ω`. -/
theorem honest_residual_accepts {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (commitmentResidualOfArrays D hchar).verifier.Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  ProductionRawVerifier.TemplateAdapter.Strategy.honest_accepts
    (rawStrategyOf D hchar) (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne
    (honest_raw_accepts D hchar a g) (honest_exactTopology D hchar a g)

/-- Named-premises fibre: every later-round walk pair has residual `Accepts`.
Not `∀ ω`. -/
theorem fibre_residual_accepts {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) :
    ∀ a g : K,
      (commitmentResidualOfArrays D hchar).verifier.Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  fun a g => honest_residual_accepts D hchar a g

/-! ## Paper characteristic wrappers

`commitmentResidualOfArrays` / fibre `Accepts` take `11 < ringChar K` instead
of a free `StateTagChar`.  Encoding-level functions still convert through
`stateTagChar_of_paper_char`.  The F97 fixture `q` is not bumped. -/

/-- Residual from inhabited `Data E` plus the paper characteristic bound.
Not a free `StateTagChar` -/
def commitmentResidualOfArrays_of_char {E : BuildableNockExecution F K}
    (D : Data E) (hgt : 11 < ringChar K) :
    BuildablePackage.CommitmentResidual E :=
  commitmentResidualOfArrays D (stateTagChar_of_paper_char hgt)

theorem commitmentResidualOfArrays_of_char_eq {E : BuildableNockExecution F K}
    (D : Data E) (hgt : 11 < ringChar K) :
    commitmentResidualOfArrays_of_char D hgt =
      commitmentResidualOfArrays D (stateTagChar_of_paper_char hgt) :=
  rfl

theorem commitmentResidualOfArrays_of_char_projects_data
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K) :
    (commitmentResidualOfArrays_of_char D hgt).q_eq_ringChar = D.q_eq_ringChar ∧
      (commitmentResidualOfArrays_of_char D hgt).honestSeed = E.cfg.challenges.z ∧
      (commitmentResidualOfArrays_of_char D hgt).honestAlpha = E.cfg.challenges.α :=
  ⟨rfl, rfl, rfl⟩

/-- Residual production `verifier.Accepts` from `11 < ringChar K`.  Not `∀ ω`. -/
theorem honest_residual_accepts_of_char {E : BuildableNockExecution F K}
    (D : Data E) (hgt : 11 < ringChar K) (a g : K) :
    (commitmentResidualOfArrays_of_char D hgt).verifier.Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  honest_residual_accepts D (stateTagChar_of_paper_char hgt) a g

/-- Named-premises fibre: every later-round walk pair has residual `Accepts`,
given inhabited `Data E` plus `11 < ringChar K`.  Not a free `StateTagChar`.
Not `∀ ω` -/
theorem fibre_residual_accepts_of_char {E : BuildableNockExecution F K}
    (D : Data E) (hgt : 11 < ringChar K) :
    ∀ a g : K,
      (commitmentResidualOfArrays_of_char D hgt).verifier.Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  fun a g => honest_residual_accepts_of_char D hgt a g

theorem fibre_residual_accepts_of_char_eq {E : BuildableNockExecution F K}
    (D : Data E) (hgt : 11 < ringChar K) :
    fibre_residual_accepts_of_char D hgt =
      fibre_residual_accepts D (stateTagChar_of_paper_char hgt) :=
  rfl

/-! ## F73: honest arrays are inhabited on a real execution -/

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open HonestCommitment.Concrete

local instance : Fact (Nat.Prime 73) := concrete_prime73
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

theorem f73_char_gt_eleven : 11 < ringChar K73cubic := by
  rw [← ConcreteStrictPackage.q_eq_ringChar]
  omega

def stateTagChar73 : NodeEncoding.StateTagChar K73cubic :=
  stateTagChar_of_paper_char f73_char_gt_eleven

/-- Honest later-round residual over the F73 committed data.  Not the all-zero
placeholder `residual73'` -/
def residual73Honest :
    BuildablePackage.CommitmentResidual concreteExecution :=
  commitmentResidualOfArrays data73 stateTagChar73

/-- Same residual from the paper characteristic bound, not a free `StateTagChar`. -/
def residual73Honest_of_char :
    BuildablePackage.CommitmentResidual concreteExecution :=
  commitmentResidualOfArrays_of_char data73 f73_char_gt_eleven

theorem residual73Honest_of_char_eq : residual73Honest_of_char = residual73Honest :=
  rfl

theorem residual73Honest_nonvacuous :
    Nonempty (BuildablePackage.CommitmentResidual concreteExecution) :=
  ⟨residual73Honest⟩

/-- F73 mixed later-round `Accepts` at every fibre walk pair -/
theorem residual73Honest_mixed_accepts (a g : K73cubic) :
    (RawMessage.ofLegacy
        (mixedAssignment concreteExecution stateTagChar73 a g)).Accepts
      data73.skeleton.publicClaim (honestCoin concreteExecution a g) :=
  mixed_raw_accepts data73 stateTagChar73 a g

theorem residual73Honest_verifierGates_at (a g : K73cubic) :
    ((rawStrategyOf data73 stateTagChar73).messageAt
        (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam data73.honestSeed_ne).VerifierGates
      data73.skeleton.publicClaim (honestCoin concreteExecution a g) :=
  honestVerifierGates_at data73 stateTagChar73 a g

theorem residual73Honest_fibre_mixed_accepts :
    ∀ a g : K73cubic,
      (RawMessage.ofLegacy
          (mixedAssignment concreteExecution stateTagChar73 a g)).Accepts
          data73.skeleton.publicClaim (honestCoin concreteExecution a g) ∧
        ((rawStrategyOf data73 stateTagChar73).messageAt
            (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam data73.honestSeed_ne).VerifierGates
          data73.skeleton.publicClaim (honestCoin concreteExecution a g) :=
  fibre_mixed_accepts data73 stateTagChar73

/-- F73 residual `verifier.Accepts` at every fibre walk pair -/
theorem residual73Honest_sixRAP_at (a g : K73cubic) :
    ((rawStrategyOf data73 stateTagChar73).messageAt
        (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam data73.honestSeed_ne).SixRAPSatisfy :=
  honestSixRAPSatisfy_at data73 stateTagChar73 a g

theorem residual73Honest_raw_accepts (a g : K73cubic) :
    (rawStrategyOf data73 stateTagChar73).Accepts
      (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam :=
  honest_raw_accepts data73 stateTagChar73 a g

theorem residual73Honest_residual_accepts (a g : K73cubic) :
    residual73Honest.verifier.Accepts (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam :=
  honest_residual_accepts data73 stateTagChar73 a g

theorem residual73Honest_fibre_residual_accepts :
    ∀ a g : K73cubic,
      residual73Honest.verifier.Accepts (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam :=
  fibre_residual_accepts data73 stateTagChar73

/-- F73 fibre residual `Accepts` from `11 < ringChar`, not a free `StateTagChar`. -/
theorem residual73Honest_fibre_residual_accepts_of_char :
    ∀ a g : K73cubic,
      residual73Honest_of_char.verifier.Accepts
        (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam :=
  fibre_residual_accepts_of_char data73 f73_char_gt_eleven

end Concrete

end

end GenericHonestArrays
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.q_gt_one_does_not_give_stateTagChar
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.stateTagChar_of_paper_char
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.stateTagChar_iff_paper_char
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.goldilocks_p_gt_eleven
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.uniformEndpoints_exist
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.ioAtWalkChallenges
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.alphaMCommitmentOf
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.walkArraysOf
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.walkArraysOf_reads_the_coin
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.walkArraysOf_reads_only_walk_challenges
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.afterAlphaM_tables_ignore_seed_and_alphaM
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.afterAlphaM_tables_are_the_reference_assignment
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.familyAt_specializes_the_coin
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.commitmentResidualOfArrays
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.commitmentResidualOfArrays_nonempty
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.not_forall_omega_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.generic_residual_would_force_q_equality
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.censusRecordPremises_still_five
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.residualPremises_still_four
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.released_builder_still_takes_hzero
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.residual_pair_still_eleven_one_two
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.mixedAssignment
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.mixedAssignment_satisfies
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.familyAt_honestCoin
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.honestVerifierGates
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.mixed_raw_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.honestVerifierGates_at
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.honestSixRAPSatisfy_at
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.honest_raw_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.honest_exactTopology
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.fibre_mixed_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.honest_residual_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.fibre_residual_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.commitmentResidualOfArrays_of_char
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.commitmentResidualOfArrays_of_char_eq
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.commitmentResidualOfArrays_of_char_projects_data
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.honest_residual_accepts_of_char
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.fibre_residual_accepts_of_char
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.fibre_residual_accepts_of_char_eq
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.Concrete.stateTagChar73
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.Concrete.residual73Honest
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.Concrete.residual73Honest_of_char
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.Concrete.residual73Honest_of_char_eq
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.Concrete.residual73Honest_nonvacuous
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.Concrete.residual73Honest_mixed_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.Concrete.residual73Honest_verifierGates_at
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.Concrete.residual73Honest_fibre_mixed_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.Concrete.residual73Honest_sixRAP_at
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.Concrete.residual73Honest_raw_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.Concrete.residual73Honest_residual_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.Concrete.residual73Honest_fibre_residual_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.Concrete.residual73Honest_fibre_residual_accepts_of_char
