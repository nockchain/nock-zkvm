import Nock.NockVMROM.Thm54.GenericHonestArrays
import Nock.RedTeam.Batch104Thm54GenericHonestArrays
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  The seventeen-conjunct `VerifierGates` holds on the mixed
`ofLegacy` message and on strategy `messageAt`, at every later-round pair over
the named fibre `honestCoin`.  Mixed `ofLegacy` `Accepts` holds.  Residual
`verifier.Accepts` is not obtained: it is equivalent on this fibre to raw
`Accepts`, which still needs `SixRAPSatisfy` on `messageAt`.  That connective
is family-indexed (`RAP.Satisfies` takes `Fin rap.w → K[X]`; traces and IO
`Fin` domains read `exec`), and `familyAt_honestCoin` is propositional via
`honest_exec`, not the MultiRoot `rfl`.  Accounting remains `11+1+2`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch105

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.NodeEncoding
open Nock.NockVMROM.Thm54.ProductionRawVerifier
open Nock.Framework

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. `VerifierGates` is exactly 17 conjuncts, none `True` -/

/-- Exhaustive expansion of production `VerifierGates`.  Seventeen conjuncts.
None is the proposition `True` -/
theorem verifierGates_expands_seventeen
    (R : RawPlusIOSegmentedFamily F K) (M : RawMessage R (ringChar K))
    (claim : P8PublicClaim) (ω : JointCoins K) :
    M.VerifierGates claim ω ↔
      nprSeed ω ≠ 0 ∧
        R.cfg.challenges.z = nprSeed ω ∧
        R.computeWalkAlpha = alphaC ω ∧
        R.walkGamma = gamma ω ∧
        R.memoryWalkAlpha = alphaM ω ∧
        RawMessage.RowAlignmentGates (R := R) ∧
        R.CanonicalNodeEncoderGates ∧
        (R.exec.computePubAt ⟨0, R.cfg.compRows_pos⟩).s =
          GlobalCarryRecognizer.enc (nprSeed ω) claim.subject ∧
        (R.exec.computePubAt ⟨0, R.cfg.compRows_pos⟩).f =
          GlobalCarryRecognizer.enc (nprSeed ω) claim.formula ∧
        (R.exec.computePubAt ⟨0, R.cfg.compRows_pos⟩).e =
          GlobalCarryRecognizer.enc (nprSeed ω) claim.result ∧
        R.requests = R.responses ∧
        R.outMem = 0 ∧
        (∀ j, M.io.multiplicity j ≠ 0) ∧
        IO.InRange R.cfg.Ksz R.exec.derivedRequestIO.length ∧
        R.exec.derivedRequestIO.Nodup ∧
        R.exec.derivedResponseIO.length ≤ R.cfg.Ksz ∧
        R.exec.derivedResponseIO.Nodup :=
  Iff.rfl

/-- Row alignment is per-row state/input agreement, not `True`. -/
theorem rowAlignment_expands
    (R : RawPlusIOSegmentedFamily F K) :
    RawMessage.RowAlignmentGates (R := R) ↔
      (∀ i : Fin R.cfg.compRows,
        let row := R.exec.computeRowAt i
        row.1 = row.2.2.1.state ∧
          row.2.1 = R.cfg.challenges.computeInputs) ∧
      (∀ i : Fin R.cfg.memRows,
        let row := R.exec.memoryRowAt i
        row.1 = row.2.2.st ∧
          row.2.1 = R.cfg.challenges.memoryInputs) :=
  Iff.rfl

/-- Canonical encoders are width identities plus `HEq` of the concrete encoders,
not `True` -/
theorem canonicalEncoders_expand
    (R : RawPlusIOSegmentedFamily F K) :
    R.CanonicalNodeEncoderGates ↔
      R.compNodeWidth = NodeEncoding.computeNodeWidth ∧
        (∀ hchar : NodeEncoding.StateTagChar K,
          HEq R.compNodeEncode (NodeEncoding.computeNodeEncode hchar)) ∧
        R.memNodeWidth = NodeEncoding.memoryNodeWidth ∧
        (∀ hchar : NodeEncoding.StateTagChar K,
          HEq R.memNodeEncode (NodeEncoding.memoryNodeEncode hchar)) :=
  Iff.rfl

/-- Coin-alignment gates on the mixed family are the honest-fibre coordinates,
not `True` -/
theorem mixed_coin_alignment_is_honestCoin
    (E : BuildableNockExecution F K) (hchar : NodeEncoding.StateTagChar K)
    (a g : K) :
    let R := RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)
    let ω := honestCoin E a g
    R.cfg.challenges.z = nprSeed ω ∧
      R.computeWalkAlpha = alphaC ω ∧
      R.walkGamma = gamma ω ∧
      R.memoryWalkAlpha = alphaM ω :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Mixed `ofLegacy` carries all seventeen gates -/
theorem mixed_ofLegacy_verifierGates_seventeen
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (RawMessage.ofLegacy (mixedAssignment E hchar a g)).VerifierGates
      D.skeleton.publicClaim (honestCoin E a g) :=
  honestVerifierGates D hchar a g

/-- Strategy `messageAt` carries the same seventeen gates -/
theorem messageAt_verifierGates_seventeen
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).VerifierGates
      D.skeleton.publicClaim (honestCoin E a g) :=
  honestVerifierGates_at D hchar a g

/-- Expanding the mixed witness recovers every named conjunct -/
theorem mixed_ofLegacy_gates_project
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    let M := RawMessage.ofLegacy (mixedAssignment E hchar a g)
    let ω := honestCoin E a g
    nprSeed ω ≠ 0 ∧
      RawMessage.RowAlignmentGates
        (R := RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)) ∧
      (RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)).CanonicalNodeEncoderGates ∧
      (∀ j, M.io.multiplicity j ≠ 0) ∧
      (RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)).requests =
        (RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)).responses ∧
      (RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)).outMem = 0 := by
  have h := (verifierGates_expands_seventeen _ _ _ _).1
    (mixed_ofLegacy_verifierGates_seventeen D hchar a g)
  exact ⟨h.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-! ## B. Mixed `ofLegacy` `Accepts` is compiled; it is not residual `Accepts` -/

/-- Mixed tables/IO come from `(0, 0)`; walks come from `(a, g)`. -/
theorem mixed_tables_are_zero_zero_walks_are_sampled
    (E : BuildableNockExecution F K) (hchar : NodeEncoding.StateTagChar K)
    (a g : K) :
    (mixedAssignment E hchar a g).computeTableAux =
        (assignmentOf E hchar 0 0).computeTableAux ∧
      (mixedAssignment E hchar a g).memoryTableAux =
        (assignmentOf E hchar 0 0).memoryTableAux ∧
      (mixedAssignment E hchar a g).computeWalk =
        (assignmentOf E hchar a g).computeWalk ∧
      (mixedAssignment E hchar a g).memoryWalk =
        (assignmentOf E hchar a g).memoryWalk :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The six mixed families are four committed RAPs at `(0, 0)` and two walk RAPs
at `(a, g)` -/
theorem mixed_six_families_split_rounds
    (E : BuildableNockExecution F K) (hchar : NodeEncoding.StateTagChar K)
    (a g : K) :
    (∀ kind, ((honestFamily E hchar a g).computeTableRAP kind).Satisfies
        (mixedAssignment E hchar a g).computeTableTrace) ∧
      (∀ kind, ((honestFamily E hchar a g).memoryTableRAP kind).Satisfies
        (mixedAssignment E hchar a g).memoryTableTrace) ∧
      (∀ kind, ((honestFamily E hchar a g).computeWalkRAP kind).Satisfies
        (mixedAssignment E hchar a g).computeWalkTrace) ∧
      (∀ kind, ((honestFamily E hchar a g).memoryWalkRAP kind).Satisfies
        (mixedAssignment E hchar a g).memoryWalkTrace) ∧
      (∀ kind, ((honestFamily E hchar a g).computeIORAP kind).Satisfies
        (mixedAssignment E hchar a g).computeIOTrace) ∧
      (∀ kind, ((honestFamily E hchar a g).memoryIORAP kind).Satisfies
        (mixedAssignment E hchar a g).memoryIOTrace) := by
  have h := mixedAssignment_satisfies E hchar a g
  exact (PlusIOSameExecutionAssignment.satisfies_iff_six_families
    (mixedAssignment E hchar a g)).1 h

/-- Mixed `ofLegacy` carries `SixRAPSatisfy`. -/
theorem mixed_ofLegacy_sixRAP
    (E : BuildableNockExecution F K) (hchar : NodeEncoding.StateTagChar K)
    (a g : K) :
    (RawMessage.ofLegacy (mixedAssignment E hchar a g)).SixRAPSatisfy :=
  RawMessage.sixRAPSatisfy_of_legacy
    (mixedAssignment E hchar a g) (mixedAssignment_satisfies E hchar a g)

theorem mixed_ofLegacy_accepts_independently
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (RawMessage.ofLegacy (mixedAssignment E hchar a g)).Accepts
      D.skeleton.publicClaim (honestCoin E a g) :=
  RawMessage.accepts_of_legacy_assignment
    D.skeleton.publicClaim (honestCoin E a g) (mixedAssignment E hchar a g)
    (mixedAssignment_satisfies E hchar a g)
    (mixed_ofLegacy_verifierGates_seventeen D hchar a g)

/-- Mixed acceptance is exactly gates and six RAPs on the `ofLegacy` message. -/
theorem mixed_ofLegacy_accepts_iff_gates_and_sixRAP
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (RawMessage.ofLegacy (mixedAssignment E hchar a g)).Accepts
        D.skeleton.publicClaim (honestCoin E a g) ↔
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).VerifierGates
          D.skeleton.publicClaim (honestCoin E a g) ∧
        (RawMessage.ofLegacy (mixedAssignment E hchar a g)).SixRAPSatisfy :=
  RawMessage.rawAccepts_iff_sixRAP_and_gates _ _ _

/-! ## C. Residual `verifier.Accepts` is not obtained; it needs `messageAt` RAPs -/

/-- The residual verifier is the honest adapter of `rawStrategyOf`. -/
theorem residual_verifier_is_honest_adapter
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) :
    (commitmentResidualOfArrays D hchar).verifier =
      TemplateAdapter.Strategy.honest (rawStrategyOf D hchar) :=
  rfl

theorem residual_verifier_raw_is_rawStrategyOf
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) :
    (commitmentResidualOfArrays D hchar).verifier.raw = rawStrategyOf D hchar :=
  rfl

/-- Raw strategy `Accepts` is gates and `SixRAPSatisfy` on `messageAt`. -/
theorem raw_accepts_iff_messageAt_gates_and_sixRAP
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (rawStrategyOf D hchar).Accepts (honestCoin E a g) E.cfg.challenges.lam ↔
      ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).VerifierGates
          D.skeleton.publicClaim (honestCoin E a g) ∧
        ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).SixRAPSatisfy :=
  (rawStrategyOf D hchar).accepts_iff_gates_and_sixRAP
    (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne

/-- On this fibre, residual production `Accepts` is equivalent to raw `Accepts`.
Topology is already compiled, so the remaining connective is raw `SixRAPSatisfy`. -/
theorem residual_accepts_iff_raw_accepts
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (commitmentResidualOfArrays D hchar).verifier.Accepts (honestCoin E a g) E.cfg.challenges.lam ↔
      (rawStrategyOf D hchar).Accepts (honestCoin E a g) E.cfg.challenges.lam := by
  constructor
  · intro h
    have hraw := TemplateAdapter.Strategy.rawAccepts_of_accepts
      (commitmentResidualOfArrays D hchar).verifier (honestCoin E a g) E.cfg.challenges.lam
      D.honestSeed_ne h
    simpa [residual_verifier_raw_is_rawStrategyOf] using hraw
  · intro h
    simpa [residual_verifier_is_honest_adapter] using
      TemplateAdapter.Strategy.honest_accepts
        (rawStrategyOf D hchar) (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne h
        (honest_exactTopology D hchar a g)

/-- Residual `Accepts` therefore still needs `SixRAPSatisfy` on `messageAt`.
Gates on `messageAt` are not enough -/
theorem residual_accepts_iff_messageAt_sixRAP
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (commitmentResidualOfArrays D hchar).verifier.Accepts (honestCoin E a g) E.cfg.challenges.lam ↔
      ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).SixRAPSatisfy := by
  rw [residual_accepts_iff_raw_accepts, raw_accepts_iff_messageAt_gates_and_sixRAP]
  constructor
  · exact And.right
  · intro hsix
    exact ⟨messageAt_verifierGates_seventeen D hchar a g, hsix⟩

/-- Mixed `ofLegacy` `Accepts` does not supply residual `verifier.Accepts`.
The closed mixed witness lives on a different family index -/
theorem mixed_accepts_is_ofLegacy_not_residual
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (RawMessage.ofLegacy (mixedAssignment E hchar a g)).Accepts
        D.skeleton.publicClaim (honestCoin E a g) ∧
      ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).VerifierGates
        D.skeleton.publicClaim (honestCoin E a g) :=
  fibre_mixed_accepts D hchar a g

/-! ## D. `familyAt_honestCoin` does not rewrite `SixRAPSatisfy` -/

/-- `RAP.Satisfies` is width-indexed: the trace is `Fin rap.w → L[X]`. -/
theorem rap_satisfies_expects_fin_width
    {L : Type} [CommRing L] (R : RAP L) :
    ∀ P : Fin R.w → Polynomial L,
      R.Satisfies P ↔
        ∀ i : Fin R.s, ∀ x ∈ R.H, (R.compose P i).eval x = 0 :=
  fun _ => Iff.rfl

/-- IO RAP domains read `derivedResponseIO.length`, hence `exec`. -/
theorem memoryIOParams_domain_reads_exec
    (R : RawPlusIOSegmentedFamily F K) :
    R.memIOParams.domain =
      fun kind =>
        PlusIOSegmentedFamily.liftFinsetToIO
          (PlusIOSegmentedFamily.ioBaseDomain R.cfg.orbit
            R.exec.derivedResponseIO.length kind) :=
  rfl

/-- Honest configuration at the fibre is definitional; honest execution is not. -/
theorem honest_cfg_is_rfl {E : BuildableNockExecution F K} (D : Data E) :
    (configTemplateOf E E.cfg.challenges.z).specialize E.cfg.challenges.α E.cfg.challenges.lam = E.cfg :=
  Data.honest_cfg D

/-- `familyAt_honestCoin` is the propositional `honest_specialization`, not `rfl`.
The MultiRoot fixture closed residual `Accepts` because its `familyAt` was
definitionally `ofLegacy` -/
theorem familyAt_honestCoin_is_honest_specialization
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne =
      RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g) :=
  familyAt_honestCoin D hchar a g

/-- Mixed `ofLegacy` IO is indexed by the execution's derived-response length. -/
theorem mixed_io_index_is_E_exec_length
    (E : BuildableNockExecution F K) (hchar : NodeEncoding.StateTagChar K)
    (a g : K) :
    (honestFamily E hchar a g).problem.exec.derivedResponseIO.length =
      E.exec.derivedResponseIO.length :=
  honestFamily_responseLen E hchar a g

/-- Strategy `familyAt` IO is indexed by the specialized execution, not by `E.exec`
definitionally -/
theorem familyAt_io_index_is_specialized
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).exec.derivedResponseIO.length =
      (specializedProblem D.timestampStrategy E.cfg.challenges.z D.honestSeed_ne
        E.cfg.challenges.α E.cfg.challenges.lam).exec.derivedResponseIO.length :=
  rfl

/-- The specialized response length equals `E.exec` only by `responseLen_of_binds`. -/
theorem specialized_response_length_eq_E_is_propositional
    {E : BuildableNockExecution F K} (D : Data E) :
    (specializedProblem D.timestampStrategy E.cfg.challenges.z D.honestSeed_ne
        E.cfg.challenges.α E.cfg.challenges.lam).exec.derivedResponseIO.length =
      E.exec.derivedResponseIO.length :=
  responseLen_of_binds D E.cfg.challenges.z D.honestSeed_ne E.cfg.challenges.α E.cfg.challenges.lam

/-- `SixRAPSatisfy` on mixed `ofLegacy` does not inhabit `SixRAPSatisfy` on
`messageAt`: the two messages are indexed by propositionally equal families,
not definitionally equal ones -/
theorem sixRAP_on_mixed_does_not_give_raw_accepts
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (RawMessage.ofLegacy (mixedAssignment E hchar a g)).SixRAPSatisfy ∧
      ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).VerifierGates
        D.skeleton.publicClaim (honestCoin E a g) ∧
      (ComputeExactTopology
          ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).exec ∧
        MemoryExactTopology
          ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).exec) :=
  ⟨mixed_ofLegacy_sixRAP E hchar a g,
    messageAt_verifierGates_seventeen D hchar a g,
    honest_exactTopology D hchar a g⟩

/-! ## E. Named fibre, not whole-joint -/

/-- `honestCoin` is later-round `(a, g)` over the committed sample
`(E.cfg.challenges.α, E.cfg.challenges.z)`.  Not `∀ ω` -/
theorem honestCoin_is_named_fibre
    (E : BuildableNockExecution F K) (a g : K) :
    honestCoin E a g = ((a, g), (E.cfg.challenges.α, E.cfg.challenges.z)) ∧
      alphaC (honestCoin E a g) = a ∧ gamma (honestCoin E a g) = g ∧
      alphaM (honestCoin E a g) = E.cfg.challenges.α ∧
      nprSeed (honestCoin E a g) = E.cfg.challenges.z :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Whole-joint `∀ ω` remains uninhabited on this strategy -/
theorem still_not_forall_omega
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (lmb : K) :
    ¬ ∀ ω : JointCoins K, (rawStrategyOf D hchar).Accepts ω lmb := by
  intro h
  have h0 := h ((0, 0), (0, 0))
  simp [TemplateRawJointSoundness.Strategy.Accepts, nprSeed] at h0

/-! ## F. Named premises and `hzero` remain -/

theorem arrays_constructor_still_takes_data_and_stateTagChar
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) :
    (commitmentResidualOfArrays D hchar).q_eq_ringChar = D.q_eq_ringChar ∧
      NodeEncoding.StateTagChar K :=
  ⟨rfl, hchar⟩

theorem censusRecordPremises_eta_still_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

theorem released_builder_still_takes_hzero
    {E : BuildableNockExecution F K}
    (I : BuildableChips.Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    -- The package carries `rowsBound`.
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    Nonempty
      (OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  GenericHonestArrays.released_builder_still_takes_hzero I R hzero hprl hmore hord hordM hrows hgenF hF

theorem any_universal_residual_still_forces_q_pin
    (g : ∀ E : BuildableNockExecution F K, CommitmentResidual E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  GenericHonestArrays.generic_residual_would_force_q_equality (F := F) (K := K) g

/-! ## G. F73: mixed fibre is inhabited; residual `Accepts` is not claimed -/

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open HonestCommitment.Concrete
open GenericHonestArrays.Concrete

local instance : Fact (Nat.Prime 73) := concrete_prime73
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- Real F73 mixed `ofLegacy` `Accepts` at a concrete walk pair.  Not residual
`verifier.Accepts` -/
theorem residual73_mixed_accepts_nonvacuous :
    (RawMessage.ofLegacy
        (mixedAssignment concreteExecution stateTagChar73 0 1)).Accepts
      data73.skeleton.publicClaim (honestCoin concreteExecution 0 1) :=
  residual73Honest_mixed_accepts 0 1

theorem residual73_messageAt_gates_nonvacuous :
    ((rawStrategyOf data73 stateTagChar73).messageAt
        (honestCoin concreteExecution 0 1) concreteExecution.cfg.challenges.lam data73.honestSeed_ne).VerifierGates
      data73.skeleton.publicClaim (honestCoin concreteExecution 0 1) :=
  residual73Honest_verifierGates_at 0 1

/-- F73 residual `Accepts` is still exactly `messageAt` `SixRAPSatisfy`.
No inhabitant of that connective is supplied -/
theorem residual73_residual_accepts_iff_messageAt_sixRAP (a g : K73cubic) :
    (residual73Honest.verifier.Accepts (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam) ↔
      ((rawStrategyOf data73 stateTagChar73).messageAt
          (honestCoin concreteExecution a g) concreteExecution.cfg.challenges.lam data73.honestSeed_ne).SixRAPSatisfy := by
  simpa [residual73Honest] using
    residual_accepts_iff_messageAt_sixRAP data73 stateTagChar73 a g

theorem residual73_still_rejects_zero_seed :
    ¬ (rawStrategyOf data73 stateTagChar73).Accepts ((0, 0), (0, 0))
      concreteExecution.cfg.challenges.lam := by
  simp [TemplateRawJointSoundness.Strategy.Accepts, nprSeed]

end Concrete

/-! ## H. -/

inductive ReviewedField105
  | structural
  | optimized_chips
  | shared_io
  | perfect_completeness
  | containment
  | walk_bounds
  | p8_fixed_field_soundness
  | p8_fixed_field_bits
  | acceptance_to_target
  | complete_false_acceptance_bound
  | complete_false_acceptance_bits
  | exact_resources
  | row_budgets
  | shared_forest_axis
deriving DecidableEq

def substantiveFields105 : List ReviewedField105 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields105 : List ReviewedField105 := [.structural]

def residualFields105 : List ReviewedField105 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

theorem independent_exact_eleven_one_two_accounting :
    substantiveFields105.length = 11 ∧
      typeSummaryFields105.length = 1 ∧
      residualFields105 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields105.length = 2 ∧
      (substantiveFields105 ++ typeSummaryFields105 ++ residualFields105).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  ⟨optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth, rfl⟩

#print axioms verifierGates_expands_seventeen
#print axioms rowAlignment_expands
#print axioms canonicalEncoders_expand
#print axioms mixed_coin_alignment_is_honestCoin
#print axioms mixed_ofLegacy_verifierGates_seventeen
#print axioms messageAt_verifierGates_seventeen
#print axioms mixed_ofLegacy_gates_project
#print axioms mixed_tables_are_zero_zero_walks_are_sampled
#print axioms mixed_six_families_split_rounds
#print axioms mixed_ofLegacy_sixRAP
#print axioms mixed_ofLegacy_accepts_independently
#print axioms mixed_ofLegacy_accepts_iff_gates_and_sixRAP
#print axioms residual_verifier_is_honest_adapter
#print axioms residual_verifier_raw_is_rawStrategyOf
#print axioms raw_accepts_iff_messageAt_gates_and_sixRAP
#print axioms residual_accepts_iff_raw_accepts
#print axioms residual_accepts_iff_messageAt_sixRAP
#print axioms mixed_accepts_is_ofLegacy_not_residual
#print axioms rap_satisfies_expects_fin_width
#print axioms memoryIOParams_domain_reads_exec
#print axioms honest_cfg_is_rfl
#print axioms familyAt_honestCoin_is_honest_specialization
#print axioms mixed_io_index_is_E_exec_length
#print axioms familyAt_io_index_is_specialized
#print axioms specialized_response_length_eq_E_is_propositional
#print axioms sixRAP_on_mixed_does_not_give_raw_accepts
#print axioms honestCoin_is_named_fibre
#print axioms still_not_forall_omega
#print axioms arrays_constructor_still_takes_data_and_stateTagChar
#print axioms censusRecordPremises_eta_still_five
#print axioms residualPremises_eta_still_four
#print axioms released_builder_still_takes_hzero
#print axioms any_universal_residual_still_forces_q_pin
#print axioms Concrete.residual73_mixed_accepts_nonvacuous
#print axioms Concrete.residual73_messageAt_gates_nonvacuous
#print axioms Concrete.residual73_residual_accepts_iff_messageAt_sixRAP
#print axioms Concrete.residual73_still_rejects_zero_seed
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.honestVerifierGates
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.mixed_raw_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.honestVerifierGates_at
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.fibre_mixed_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.familyAt_honestCoin
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch105
