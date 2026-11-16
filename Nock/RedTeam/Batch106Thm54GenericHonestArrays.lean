import Nock.NockVMROM.Thm54.GenericHonestArrays
import Nock.RedTeam.Batch105Thm54GenericHonestArrays
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  All six `messageAt` RAP evaluations hold
on the named fibre.  Transport is `rapSatisfies_congr` along propositional
family/trace equalities: `airToRAP.w` is the AIR column count, so traces have
family-independent types, and `honest_exec` identifies the specialized IO
lists with `E.exec` (not merely their lengths).  F73 residual `Accepts`
inhabits at two distinct later-round pairs.  Accounting remains `11+1+2`.
No `∀ ω`.  No `∀ E`.  `hzero` remains.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch106

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
open Nock.Reified
open Nock.Framework.Reify

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. Residual `Accepts` is production `VerifierChecks`, not mixed `ofLegacy` -/

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

/-- Production residual `Accepts` is `VerifierChecks` of the honest-adapter message. -/
theorem residual_accepts_is_verifierChecks
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (commitmentResidualOfArrays D hchar).verifier.Accepts (honestCoin E a g) E.cfg.challenges.lam ↔
      ((commitmentResidualOfArrays D hchar).verifier.messageAt
          (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).VerifierChecks
        (commitmentResidualOfArrays D hchar).verifier.raw.claim
        (honestCoin E a g) :=
  ((commitmentResidualOfArrays D hchar).verifier.accepts_iff_production
    (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne)

/-- `VerifierChecks` is gates plus eight RAP families (32 evaluations). -/
theorem verifierChecks_is_eight_families
    (R : RawPlusIOSegmentedFamily F K) (M : Message R (ringChar K))
    (claim : P8PublicClaim) (ω : JointCoins K) :
    M.VerifierChecks claim ω ↔
      M.raw.VerifierGates claim ω ∧
        (∀ kind, (R.computeTableRAP kind).Satisfies M.raw.computeTableTrace) ∧
          (∀ kind, (R.memoryTableRAP kind).Satisfies M.raw.memoryTableTrace) ∧
            (∀ kind, (R.computeWalkRAP kind).Satisfies M.raw.computeWalkTrace) ∧
              (∀ kind, (R.memoryWalkRAP kind).Satisfies M.raw.memoryWalkTrace) ∧
                (∀ kind, (R.computeIORAP kind).Satisfies M.raw.computeIOTrace) ∧
                  (∀ kind, (R.memoryIORAP kind).Satisfies M.raw.memoryIOTrace) ∧
                    (∀ kind, (computeTopologyGenericRAP R kind).Satisfies
                      (computeTopologyTrace R M.topology.compute)) ∧
                      (∀ kind, (memoryTopologyGenericRAP R kind).Satisfies
                        (memoryTopologyTrace R M.topology.memory)) :=
  Message.verifierChecks_iff_eight_segmented_families M claim ω

theorem eight_times_four_evaluations : 8 * 4 = 32 := by decide

/-- Mixed `ofLegacy` `Accepts` is the six-family raw predicate, not residual
`VerifierChecks` -/
theorem mixed_accepts_is_raw_six_not_eight
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (RawMessage.ofLegacy (mixedAssignment E hchar a g)).Accepts
        D.skeleton.publicClaim (honestCoin E a g) ↔
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).VerifierGates
          D.skeleton.publicClaim (honestCoin E a g) ∧
        (RawMessage.ofLegacy (mixedAssignment E hchar a g)).SixRAPSatisfy :=
  RawMessage.rawAccepts_iff_sixRAP_and_gates _ _ _

/-- Independent residual `Accepts` on the fibre.  This is
`commitmentResidualOfArrays.verifier.Accepts`, obtained from raw `Accepts`
plus compiled topology, not by renaming mixed `ofLegacy` `Accepts`. -/
theorem residual_accepts_independently
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (commitmentResidualOfArrays D hchar).verifier.Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  honest_residual_accepts D hchar a g

/-- Expanding residual `Accepts` recovers all eight production families. -/
theorem residual_accepts_expands_eight
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    let T := (commitmentResidualOfArrays D hchar).verifier
    let ω := honestCoin E a g
    T.Accepts ω E.cfg.challenges.lam →
      (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).raw.VerifierGates T.raw.claim ω ∧
        (∀ kind, ((T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne).computeTableRAP kind).Satisfies
          (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).raw.computeTableTrace) ∧
        (∀ kind, ((T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne).memoryTableRAP kind).Satisfies
          (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).raw.memoryTableTrace) ∧
        (∀ kind, ((T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne).computeWalkRAP kind).Satisfies
          (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).raw.computeWalkTrace) ∧
        (∀ kind, ((T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne).memoryWalkRAP kind).Satisfies
          (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).raw.memoryWalkTrace) ∧
        (∀ kind, ((T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne).computeIORAP kind).Satisfies
          (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).raw.computeIOTrace) ∧
        (∀ kind, ((T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne).memoryIORAP kind).Satisfies
          (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).raw.memoryIOTrace) ∧
        (∀ kind, (computeTopologyGenericRAP (T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne) kind).Satisfies
          (computeTopologyTrace (T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne)
            (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).topology.compute)) ∧
        (∀ kind, (memoryTopologyGenericRAP (T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne) kind).Satisfies
          (memoryTopologyTrace (T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne)
            (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).topology.memory)) := by
  intro T ω h
  exact (T.accepts_iff_eight_segmented_families ω E.cfg.challenges.lam D.honestSeed_ne).1 h

/-- All eight families hold on the fibre, including both IO RAPs and both
topology RAPs -/
theorem residual_eight_families_hold
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    let T := (commitmentResidualOfArrays D hchar).verifier
    let ω := honestCoin E a g
    (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).raw.VerifierGates T.raw.claim ω ∧
      (∀ kind, ((T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne).computeTableRAP kind).Satisfies
        (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).raw.computeTableTrace) ∧
      (∀ kind, ((T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne).memoryTableRAP kind).Satisfies
        (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).raw.memoryTableTrace) ∧
      (∀ kind, ((T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne).computeWalkRAP kind).Satisfies
        (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).raw.computeWalkTrace) ∧
      (∀ kind, ((T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne).memoryWalkRAP kind).Satisfies
        (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).raw.memoryWalkTrace) ∧
      (∀ kind, ((T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne).computeIORAP kind).Satisfies
        (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).raw.computeIOTrace) ∧
      (∀ kind, ((T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne).memoryIORAP kind).Satisfies
        (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).raw.memoryIOTrace) ∧
      (∀ kind, (computeTopologyGenericRAP (T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne) kind).Satisfies
        (computeTopologyTrace (T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne)
          (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).topology.compute)) ∧
      (∀ kind, (memoryTopologyGenericRAP (T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne) kind).Satisfies
        (memoryTopologyTrace (T.familyAt ω E.cfg.challenges.lam D.honestSeed_ne)
          (T.messageAt ω E.cfg.challenges.lam D.honestSeed_ne).topology.memory)) :=
  residual_accepts_expands_eight D hchar a g (residual_accepts_independently D hchar a g)

/-! ## B. Transport is 1-1: all six RAPs, IO lists identified by `honest_exec` -/

/-- `RAP.Satisfies` is width-indexed: the trace is `Fin rap.w → L[X]`. -/
theorem rap_satisfies_expects_fin_width
    {L : Type} [CommRing L] (R : RAP L) :
    ∀ P : Fin R.w → Polynomial L,
      R.Satisfies P ↔
        ∀ i : Fin R.s, ∀ x ∈ R.H, (R.compose P i).eval x = 0 :=
  fun _ => Iff.rfl

/-- `airToRAP.w` is the AIR column count, independent of `exec` -/
theorem airToRAP_w_is_numTraceCols
    {L : Type} [Field L] (air : Reified.AIR) (chalVal pubVal : ℕ → L)
    (eDeg hExp : ℕ) (ω β : L) (H : Finset L) (hβ : β ≠ 0) (hh1 : 1 ≤ hExp) :
    (airToRAP air chalVal pubVal eDeg hExp ω β H hβ hh1).w = air.numTraceCols :=
  rfl

/-- `rapSatisfies_congr` is equality cases, not a family-index rewrite. -/
theorem rapSatisfies_congr_is_eq_cases {L : Type} [CommRing L] {R S : RAP L}
    (hR : R = S) {P : Fin R.w → L[X]} {Q : Fin S.w → L[X]}
    (hP : HEq P Q) (h : R.Satisfies P) : S.Satisfies Q :=
  rapSatisfies_congr hR hP h

/-- Specialized execution at the honest sample is the supplied `E.exec`.
This identifies IO lists, not merely their lengths -/
theorem specialized_exec_eq_E
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).exec =
      E.exec :=
  familyAt_honestCoin_exec D hchar a g

/-- Mixed `ofLegacy` execution is the supplied `E.exec` definitionally. -/
theorem mixed_exec_eq_E
    (E : BuildableNockExecution F K) (hchar : NodeEncoding.StateTagChar K)
    (a g : K) :
    (RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)).exec = E.exec :=
  rfl

/-- Request and response lists, not just lengths, agree with `E.exec`. -/
theorem specialized_io_lists_eq_E
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).exec.derivedRequestIO =
        E.exec.derivedRequestIO ∧
      ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).exec.derivedResponseIO =
        E.exec.derivedResponseIO := by
  constructor
  · exact congrArg (fun e => e.derivedRequestIO)
      (specialized_exec_eq_E D hchar a g)
  · exact congrArg (fun e => e.derivedResponseIO)
      (specialized_exec_eq_E D hchar a g)

theorem mixed_io_lists_eq_E
    (E : BuildableNockExecution F K) (hchar : NodeEncoding.StateTagChar K)
    (a g : K) :
    (RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)).exec.derivedRequestIO =
        E.exec.derivedRequestIO ∧
      (RawPlusIOSegmentedFamily.ofLegacy (honestFamily E hchar a g)).exec.derivedResponseIO =
        E.exec.derivedResponseIO :=
  ⟨rfl, rfl⟩

/-- Specialized and mixed IO lists are the same lists -/
theorem specialized_io_lists_eq_mixed
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).exec.derivedRequestIO =
        (RawPlusIOSegmentedFamily.ofLegacy
          (honestFamily E hchar a g)).exec.derivedRequestIO ∧
      ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).exec.derivedResponseIO =
        (RawPlusIOSegmentedFamily.ofLegacy
          (honestFamily E hchar a g)).exec.derivedResponseIO := by
  constructor
  · exact (specialized_io_lists_eq_E D hchar a g).1.trans
      (mixed_io_lists_eq_E E hchar a g).1.symm
  · exact (specialized_io_lists_eq_E D hchar a g).2.trans
      (mixed_io_lists_eq_E E hchar a g).2.symm

/-- Memory-IO RAP domain reads `derivedResponseIO.length` -/
theorem memoryIOParams_domain_reads_exec
    (R : RawPlusIOSegmentedFamily F K) :
    R.memIOParams.domain =
      fun kind =>
        PlusIOSegmentedFamily.liftFinsetToIO
          (PlusIOSegmentedFamily.ioBaseDomain R.cfg.orbit
            R.exec.derivedResponseIO.length kind) :=
  rfl

/-- After `honest_exec`, that domain length is `E.exec`'s response length. -/
theorem specialized_response_length_eq_E
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).exec.derivedResponseIO.length =
      E.exec.derivedResponseIO.length :=
  congrArg (fun e => e.derivedResponseIO.length) (specialized_exec_eq_E D hchar a g)

/-- `SixRAPSatisfy` is exactly the six named RAP families -/
theorem sixRAP_expands_six
    (R : RawPlusIOSegmentedFamily F K) (M : RawMessage R (ringChar K)) :
    M.SixRAPSatisfy ↔
      (∀ kind, (R.computeTableRAP kind).Satisfies M.computeTableTrace) ∧
        (∀ kind, (R.memoryTableRAP kind).Satisfies M.memoryTableTrace) ∧
          (∀ kind, (R.computeWalkRAP kind).Satisfies M.computeWalkTrace) ∧
            (∀ kind, (R.memoryWalkRAP kind).Satisfies M.memoryWalkTrace) ∧
              (∀ kind, (R.computeIORAP kind).Satisfies M.computeIOTrace) ∧
                (∀ kind, (R.memoryIORAP kind).Satisfies M.memoryIOTrace) :=
  Iff.rfl

/-- Independent `SixRAPSatisfy` on strategy `messageAt` -/
theorem messageAt_sixRAP_independently
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).SixRAPSatisfy :=
  honestSixRAPSatisfy_at D hchar a g

/-- All six RAP evaluations on `messageAt`, projected separately. -/
theorem messageAt_all_six_raps
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (∀ kind, (((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeTableRAP
          kind).Satisfies
        ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeTableTrace) ∧
      (∀ kind, (((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryTableRAP
          kind).Satisfies
        ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryTableTrace) ∧
      (∀ kind, (((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeWalkRAP
          kind).Satisfies
        ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeWalkTrace) ∧
      (∀ kind, (((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryWalkRAP
          kind).Satisfies
        ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryWalkTrace) ∧
      (∀ kind, (((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeIORAP
          kind).Satisfies
        ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeIOTrace) ∧
      (∀ kind, (((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryIORAP
          kind).Satisfies
        ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryIOTrace) :=
  (sixRAP_expands_six _ _).1 (messageAt_sixRAP_independently D hchar a g)

/-- Compute-IO RAP evaluation holds on `messageAt` -/
theorem messageAt_computeIORAP_satisfies
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ∀ kind, (((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeIORAP
        kind).Satisfies
      ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeIOTrace :=
  (messageAt_all_six_raps D hchar a g).2.2.2.2.1

/-- Memory-IO RAP evaluation holds on `messageAt` -/
theorem messageAt_memoryIORAP_satisfies
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ∀ kind, (((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryIORAP
        kind).Satisfies
      ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryIOTrace :=
  (messageAt_all_six_raps D hchar a g).2.2.2.2.2

/-- Compute-table traces are propositionally equal, not merely `HEq`. -/
theorem computeTableTrace_is_eq
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeTableTrace =
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).computeTableTrace :=
  messageAt_computeTableTrace D hchar a g

theorem memoryTableTrace_is_eq
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryTableTrace =
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).memoryTableTrace :=
  messageAt_memoryTableTrace D hchar a g

theorem computeWalkTrace_is_eq
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeWalkTrace =
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).computeWalkTrace :=
  messageAt_computeWalkTrace D hchar a g

theorem memoryWalkTrace_is_eq
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryWalkTrace =
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).memoryWalkTrace :=
  messageAt_memoryWalkTrace D hchar a g

/-- Compute-IO traces are `Eq` after identifying `exec` -/
theorem computeIOTrace_is_eq
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeIOTrace =
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).computeIOTrace :=
  messageAt_computeIOTrace D hchar a g

/-- Memory-IO traces are `Eq` after `castμ` and identifying `exec`. -/
theorem memoryIOTrace_is_eq
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryIOTrace =
      (RawMessage.ofLegacy (mixedAssignment E hchar a g)).memoryIOTrace :=
  messageAt_memoryIOTrace D hchar a g

/-- Independent reconstruction of the memory-IO RAP transport: RAP equality,
trace equality, then `rapSatisfies_congr` -/
theorem memoryIORAP_transport_is_congr
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) (kind : ConstraintKind) :
    (((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryIORAP
        kind).Satisfies
      ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).memoryIOTrace :=
  rapSatisfies_congr
    (familyAt_memoryIORAP D hchar a g kind).symm
    (heq_of_eq (memoryIOTrace_is_eq D hchar a g).symm)
    ((mixed_ofLegacy_sixRAP E hchar a g).2.2.2.2.2 kind)

theorem computeIORAP_transport_is_congr
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) (kind : ConstraintKind) :
    (((rawStrategyOf D hchar).familyAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeIORAP
        kind).Satisfies
      ((rawStrategyOf D hchar).messageAt (honestCoin E a g) E.cfg.challenges.lam D.honestSeed_ne).computeIOTrace :=
  rapSatisfies_congr
    (familyAt_computeIORAP D hchar a g kind).symm
    (heq_of_eq (computeIOTrace_is_eq D hchar a g).symm)
    ((mixed_ofLegacy_sixRAP E hchar a g).2.2.2.2.1 kind)

/-- Strategy raw `Accepts` on the fibre -/
theorem raw_accepts_independently
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (a g : K) :
    (rawStrategyOf D hchar).Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  honest_raw_accepts D hchar a g

/-! ## C. Named fibre, not whole-joint -/

theorem honestCoin_is_named_fibre
    (E : BuildableNockExecution F K) (a g : K) :
    honestCoin E a g = ((a, g), (E.cfg.challenges.α, E.cfg.challenges.z)) ∧
      alphaC (honestCoin E a g) = a ∧ gamma (honestCoin E a g) = g ∧
      alphaM (honestCoin E a g) = E.cfg.challenges.α ∧
      nprSeed (honestCoin E a g) = E.cfg.challenges.z :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem still_not_forall_omega
    {E : BuildableNockExecution F K} (D : Data E)
    (hchar : NodeEncoding.StateTagChar K) (lmb : K) :
    ¬ ∀ ω : JointCoins K, (rawStrategyOf D hchar).Accepts ω lmb := by
  intro h
  have h0 := h ((0, 0), (0, 0))
  simp [TemplateRawJointSoundness.Strategy.Accepts, nprSeed] at h0

/-! ## D. Named premises and `hzero` remain -/

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

/-! ## E. F73: residual `Accepts` at two distinct `(a, g)` -/

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open HonestCommitment.Concrete
open GenericHonestArrays.Concrete

local instance : Fact (Nat.Prime 73) := concrete_prime73
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

theorem zero_ne_one_k73 : (0 : K73cubic) ≠ 1 :=
  zero_ne_one

theorem residual73_pairs_distinct :
    honestCoin concreteExecution (0 : K73cubic) 1 ≠
      honestCoin concreteExecution 1 0 := by
  intro h
  injection h with hpair
  injection hpair with ha
  exact zero_ne_one_k73 ha

/-- Real F73 residual production `Accepts` at `(0, 1)` -/
theorem residual73_accepts_at_zero_one :
    residual73Honest.verifier.Accepts (honestCoin concreteExecution 0 1) concreteExecution.cfg.challenges.lam :=
  residual73Honest_residual_accepts 0 1

/-- Real F73 residual production `Accepts` at `(1, 0)` -/
theorem residual73_accepts_at_one_zero :
    residual73Honest.verifier.Accepts (honestCoin concreteExecution 1 0) concreteExecution.cfg.challenges.lam :=
  residual73Honest_residual_accepts 1 0

theorem residual73_sixRAP_at_zero_one :
    ((rawStrategyOf data73 stateTagChar73).messageAt
        (honestCoin concreteExecution 0 1) concreteExecution.cfg.challenges.lam data73.honestSeed_ne).SixRAPSatisfy :=
  residual73Honest_sixRAP_at 0 1

theorem residual73_sixRAP_at_one_zero :
    ((rawStrategyOf data73 stateTagChar73).messageAt
        (honestCoin concreteExecution 1 0) concreteExecution.cfg.challenges.lam data73.honestSeed_ne).SixRAPSatisfy :=
  residual73Honest_sixRAP_at 1 0

theorem residual73_memoryIORAP_at_zero_one :
    ∀ kind, (((rawStrategyOf data73 stateTagChar73).familyAt
          (honestCoin concreteExecution 0 1) concreteExecution.cfg.challenges.lam data73.honestSeed_ne).memoryIORAP
        kind).Satisfies
      ((rawStrategyOf data73 stateTagChar73).messageAt
        (honestCoin concreteExecution 0 1) concreteExecution.cfg.challenges.lam data73.honestSeed_ne).memoryIOTrace :=
  messageAt_memoryIORAP_satisfies data73 stateTagChar73 0 1

theorem residual73_still_rejects_zero_seed :
    ¬ (rawStrategyOf data73 stateTagChar73).Accepts ((0, 0), (0, 0))
      concreteExecution.cfg.challenges.lam := by
  simp [TemplateRawJointSoundness.Strategy.Accepts, nprSeed]

end Concrete

/-! ## F. -/

inductive ReviewedField106
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

def substantiveFields106 : List ReviewedField106 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields106 : List ReviewedField106 := [.structural]

def residualFields106 : List ReviewedField106 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

theorem independent_exact_eleven_one_two_accounting :
    substantiveFields106.length = 11 ∧
      typeSummaryFields106.length = 1 ∧
      residualFields106 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields106.length = 2 ∧
      (substantiveFields106 ++ typeSummaryFields106 ++ residualFields106).Nodup ∧
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

#print axioms residual_verifier_is_honest_adapter
#print axioms residual_verifier_raw_is_rawStrategyOf
#print axioms residual_accepts_is_verifierChecks
#print axioms verifierChecks_is_eight_families
#print axioms eight_times_four_evaluations
#print axioms mixed_accepts_is_raw_six_not_eight
#print axioms residual_accepts_independently
#print axioms residual_accepts_expands_eight
#print axioms residual_eight_families_hold
#print axioms rap_satisfies_expects_fin_width
#print axioms airToRAP_w_is_numTraceCols
#print axioms rapSatisfies_congr_is_eq_cases
#print axioms specialized_exec_eq_E
#print axioms mixed_exec_eq_E
#print axioms specialized_io_lists_eq_E
#print axioms mixed_io_lists_eq_E
#print axioms specialized_io_lists_eq_mixed
#print axioms memoryIOParams_domain_reads_exec
#print axioms specialized_response_length_eq_E
#print axioms sixRAP_expands_six
#print axioms messageAt_sixRAP_independently
#print axioms messageAt_all_six_raps
#print axioms messageAt_computeIORAP_satisfies
#print axioms messageAt_memoryIORAP_satisfies
#print axioms computeTableTrace_is_eq
#print axioms memoryTableTrace_is_eq
#print axioms computeWalkTrace_is_eq
#print axioms memoryWalkTrace_is_eq
#print axioms computeIOTrace_is_eq
#print axioms memoryIOTrace_is_eq
#print axioms memoryIORAP_transport_is_congr
#print axioms computeIORAP_transport_is_congr
#print axioms raw_accepts_independently
#print axioms honestCoin_is_named_fibre
#print axioms still_not_forall_omega
#print axioms arrays_constructor_still_takes_data_and_stateTagChar
#print axioms censusRecordPremises_eta_still_five
#print axioms residualPremises_eta_still_four
#print axioms released_builder_still_takes_hzero
#print axioms any_universal_residual_still_forces_q_pin
#print axioms Concrete.zero_ne_one_k73
#print axioms Concrete.residual73_pairs_distinct
#print axioms Concrete.residual73_accepts_at_zero_one
#print axioms Concrete.residual73_accepts_at_one_zero
#print axioms Concrete.residual73_sixRAP_at_zero_one
#print axioms Concrete.residual73_sixRAP_at_one_zero
#print axioms Concrete.residual73_memoryIORAP_at_zero_one
#print axioms Concrete.residual73_still_rejects_zero_seed
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.honestSixRAPSatisfy_at
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.honest_raw_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.honest_residual_accepts
#print axioms Nock.NockVMROM.Thm54.GenericHonestArrays.fibre_residual_accepts
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch106
