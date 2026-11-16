import Nock.NockVMROM.Thm54.PlusIOTraceEncoding
import Nock.NockVMROM.Thm54.NodeEncoding

/-!
# Same-execution joint verification for the exact Theorem 5.4 family

This is the algebraic S5/S6 layer.  A single `PlusIOSegmentedFamily` fixes one exact problem,
configuration, and execution for both table families, both walk families, and both IO families.
There is no probability statement here.

The concrete widths remain the segmented `102/44`, `1-1*` scope proved by
`PlusIOSegmentedFamily.one_to_one_star_scope`.
-/

namespace Nock.NockVMROM.Thm54

open scoped Classical

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## S5: shared IO on the exact derived lists -/

/-- Algebraic shared-IO satisfiability on exactly the request and response lists derived from
`R.problem.exec`.

The last conjunct is the literal `IOSat` witness and therefore retains the dependent
`Fin R.problem.exec.derivedResponseIO.length → ZMod p` multiplicity.  The preceding facts are the
range and uniqueness side conditions required by the exact `IO.io_result_LIO` biconditional. -/
noncomputable def SharedIOSat (R : PlusIOSegmentedFamily F K)
    (p : ℕ) [CharP K p] : Prop :=
  IO.InRange R.problem.cfg.Ksz R.problem.exec.derivedRequestIO.length ∧
    R.problem.exec.derivedRequestIO.Nodup ∧
    R.problem.exec.derivedResponseIO.length ≤ R.problem.cfg.Ksz ∧
    R.problem.exec.derivedResponseIO.Nodup ∧
    IOSat p R.problem.exec.derivedRequestIO R.problem.exec.derivedResponseIO

/-- **S5 shared IO.**  Under the characteristic bound, algebraic satisfiability on the two exact
derived lists is equivalent to their unique IO matching language. -/
theorem sharedIOSat_iff_LIO
    (R : PlusIOSegmentedFamily F K) {p : ℕ} [CharP K p]
    (hKp : R.problem.cfg.Ksz < p) :
    SharedIOSat R p ↔
      IO.LIO R.problem.cfg.Ksz
        R.problem.exec.derivedRequestIO R.problem.exec.derivedResponseIO := by
  unfold SharedIOSat
  constructor
  · rintro ⟨hKreq, hreqnd, hKresp, hrespnd, hsat⟩
    exact
      (IO.io_result_LIO R.problem.cfg.Ksz hKp
        R.problem.exec.derivedRequestIO R.problem.exec.derivedResponseIO
        hKreq hKresp hreqnd hrespnd).1 hsat
  · intro hLIO
    have hperm := hLIO.2.2
    have hKreq :
        IO.InRange R.problem.cfg.Ksz R.problem.exec.derivedRequestIO.length := by
      rw [hperm.length_eq]
      exact hLIO.1
    have hreqnd : R.problem.exec.derivedRequestIO.Nodup :=
      hperm.nodup_iff.mpr hLIO.2.1
    refine ⟨hKreq, hreqnd, hLIO.1.2, hLIO.2.1, ?_⟩
    exact
      (IO.io_result_LIO R.problem.cfg.Ksz hKp
        R.problem.exec.derivedRequestIO R.problem.exec.derivedResponseIO
        hKreq hLIO.1.2 hreqnd hLIO.2.1).2 hLIO

/-! ## One negative-type-safe joint assignment -/

/-- One proof-carrying joint assignment for one exact family.

`sameExecution` is deliberately reused rather than copying its six witness families.  The public endpoints are the fields
`R.requests`, `R.responses`, and `R.outMem` consumed by `sameExecution.exactIO`. -/
structure JointAssignment (R : PlusIOSegmentedFamily F K)
    (p : ℕ) [CharP K p] where
  sameExecution : PlusIOSameExecutionAssignment R p
  sixFamilies : sameExecution.Satisfies
  sharedIO : SharedIOSat R p

/-- The joint verification problem for characteristic `p` and the exact problem carried by `R`.
Inhabitation means that all six families accept one assignment and S5 holds on that same
execution's exact derived IO lists. -/
def JointVerificationProblem (R : PlusIOSegmentedFamily F K)
    (p : ℕ) [CharP K p] : Prop :=
  Nonempty (JointAssignment R p)

namespace JointAssignment

variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-- The six ordinary family satisfactions stored by a joint assignment, exposed without changing
their common exact-execution index. -/
theorem six_family_satisfaction (A : JointAssignment R p) :
    (∀ kind, (R.computeTableRAP kind).Satisfies A.sameExecution.computeTableTrace) ∧
      (∀ kind, (R.memoryTableRAP kind).Satisfies A.sameExecution.memoryTableTrace) ∧
      (∀ kind, (R.computeWalkRAP kind).Satisfies A.sameExecution.computeWalkTrace) ∧
      (∀ kind, (R.memoryWalkRAP kind).Satisfies A.sameExecution.memoryWalkTrace) ∧
      (∀ kind, (R.computeIORAP kind).Satisfies A.sameExecution.computeIOTrace) ∧
      (∀ kind, (R.memoryIORAP kind).Satisfies A.sameExecution.memoryIOTrace) :=
  (PlusIOSameExecutionAssignment.satisfies_iff_six_families A.sameExecution).1 A.sixFamilies

/-- The public IO endpoints of a joint assignment are the endpoints certified by its exact IO
witness. -/
theorem public_endpoints (A : JointAssignment R p) :
    R.requests = R.responses ∧ R.outMem = 0 :=
  ⟨A.sameExecution.exactIO.endpoints_agree, A.sameExecution.exactIO.memory_closes⟩

end JointAssignment

/-! ## S5: exact two-RAP verification -/

/-- **One exact two-RAP realization**.

The sole witness is one `JointAssignment` for one `PlusIOSegmentedFamily`.  Opening that witness
exposes satisfaction of all six kind-segment families, shared IO on the same execution's derived
lists, and agreement of the public compute/memory endpoints.  This is the segmented `102/44`,
`e = 1` scope; it does not identify these families with the separately named monolithic
`199/196`, `e = 3` chips. -/
def TwoRAPRealization (R : PlusIOSegmentedFamily F K)
    (p : ℕ) [CharP K p] : Prop :=
  ∃ A : JointAssignment R p,
    A.sameExecution.Satisfies ∧
      SharedIOSat R p ∧
      (R.requests = R.responses ∧ R.outMem = 0)

/-- **Universal paper-facing S5 claim.**  Every accepted exact joint verification problem projects
to a two-RAP realization on that very same family and characteristic.  Existence of such a joint
assignment is the separate S6 obligation below. -/
def ExactTwoRAPVerification (F K : Type)
    [Field F] [Field K] [Algebra F K] : Prop :=
  ∀ (R : PlusIOSegmentedFamily F K) (p : ℕ) [CharP K p],
    JointVerificationProblem R p → TwoRAPRealization R p

/-- **S5 exact two-RAP verification** at segmented `102/44`, `e = 1` scope.

The proof only opens the single `JointAssignment` already accepted by
`JointVerificationProblem`; no execution, IO list, family, or endpoint is replaced. -/
theorem exactTwoRAPVerification (F K : Type)
    [Field F] [Field K] [Algebra F K] :
    ExactTwoRAPVerification F K := by
  intro R p _ h
  obtain ⟨A⟩ := h
  exact ⟨A, A.sixFamilies, A.sharedIO, A.public_endpoints⟩

/-! ## S6: constructive combined existence -/

/-- **S6 combined existence.**  A chained exact execution, a semantic IO witness, and the
characteristic bound construct public endpoint values and one joint assignment containing all six
accepting families.

No separate traversal or one-hot premise is needed here: the walk completeness connector operates
on the authoritative BFS tree/forest already stored in this same exact execution. -/
theorem jointVerification_complete
    (R : PlusIOSegmentedFamily F K) {p : ℕ} [CharP K p]
    (hchained :
      ChainedSemanticExactLanguage R.problem.cfg R.problem.exec)
    (w : SemanticIOWitness R.problem.cfg R.problem.exec)
    (hKp : R.problem.cfg.Ksz < p) :
    ∃ requests responses outMem : IOField K,
      JointVerificationProblem
        (R.withIOEndpoints requests responses outMem) p := by
  have hLIO :
      IO.LIO R.problem.cfg.Ksz
        R.problem.exec.derivedRequestIO R.problem.exec.derivedResponseIO :=
    (w.strongExactLanguage_of_semanticExactLanguage hchained.semantic).2.2
  obtain ⟨requests, responses, outMem, ⟨io⟩⟩ :=
    ExactDerivedIOAssignment.exists_with_public_endpoints_of_semanticIOWitness
      R hKp w hchained.semantic
  let R' := R.withIOEndpoints requests responses outMem
  have hchained' :
      ChainedSemanticExactLanguage R'.problem.cfg R'.problem.exec := by
    simpa [R', PlusIOSegmentedFamily.withIOEndpoints] using hchained
  have hKp' : R'.problem.cfg.Ksz < p := by
    simpa [R', PlusIOSegmentedFamily.withIOEndpoints] using hKp
  have hLIO' :
      IO.LIO R'.problem.cfg.Ksz
        R'.problem.exec.derivedRequestIO R'.problem.exec.derivedResponseIO := by
    simpa [R', PlusIOSegmentedFamily.withIOEndpoints] using hLIO
  obtain ⟨A, hA⟩ :=
    PlusIOSameExecutionAssignment.exists_satisfies_of_chained_IO
      (R := R') hchained' io
  refine ⟨requests, responses, outMem, ?_⟩
  exact
    ⟨{ sameExecution := A
       sixFamilies := hA
       sharedIO := (sharedIOSat_iff_LIO R' hKp').2 hLIO' }⟩

/-- Constructor-specialized completeness using the production finite-coordinate node encoders.
The only family-specific premises left explicit are the two exact active-prefix capacities. -/
theorem jointVerification_complete_with_concreteNodeEncoders
    (problem : ExactCanonicalRAPProblem F K)
    (hchar : NodeEncoding.StateTagChar K)
    (computeWalkAlpha walkGamma memoryWalkAlpha : K)
    (progIO_capacity :
      problem.exec.derivedRequestIO.length + 1 ≤ 2 ^ problem.cfg.orbit.h)
    (memIO_capacity :
      problem.exec.derivedResponseIO.length + 1 ≤ 2 ^ problem.cfg.orbit.h)
    {p : ℕ} [CharP K p]
    (hchained : ChainedSemanticExactLanguage problem.cfg problem.exec)
    (w : SemanticIOWitness problem.cfg problem.exec)
    (hKp : problem.cfg.Ksz < p) :
    ∃ requests responses outMem : IOField K,
      JointVerificationProblem
        (PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders
          problem hchar computeWalkAlpha walkGamma memoryWalkAlpha
          requests responses outMem
          progIO_capacity memIO_capacity) p := by
  let R : PlusIOSegmentedFamily F K :=
    PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders
      problem hchar computeWalkAlpha walkGamma memoryWalkAlpha
      0 0 0 progIO_capacity memIO_capacity
  have hchainedR :
      ChainedSemanticExactLanguage R.problem.cfg R.problem.exec := by
    simpa [R, PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders] using hchained
  have wR : SemanticIOWitness R.problem.cfg R.problem.exec := by
    simpa [R, PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders] using w
  have hKpR : R.problem.cfg.Ksz < p := by
    simpa [R, PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders] using hKp
  obtain ⟨requests, responses, outMem, hjoint⟩ :=
    jointVerification_complete R hchainedR wR hKpR
  refine ⟨requests, responses, outMem, ?_⟩
  simpa [R, PlusIOSegmentedFamily.withIOEndpoints,
    PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders] using hjoint

theorem jointVerification_complete_with_concreteNodeEncodersScopedP7
    (problem : ExactCanonicalRAPProblem F K)
    (hchar : NodeEncoding.StateTagChar K)
    (progIO_capacity :
      problem.exec.derivedRequestIO.length + 1 ≤ 2 ^ problem.cfg.orbit.h)
    (memIO_capacity :
      problem.exec.derivedResponseIO.length + 1 ≤ 2 ^ problem.cfg.orbit.h)
    {p : ℕ} [CharP K p]
    (hchained : ChainedSemanticExactLanguage problem.cfg problem.exec)
    (w : SemanticIOWitness problem.cfg problem.exec)
    (hKp : problem.cfg.Ksz < p) :
    ∃ requests responses outMem : IOField K,
      JointVerificationProblem
        (PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncodersScopedP7
          problem hchar requests responses outMem
          progIO_capacity memIO_capacity) p := by
  simpa [PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncodersScopedP7] using
    (jointVerification_complete_with_concreteNodeEncoders
      problem hchar problem.cfg.challenges.α problem.cfg.challenges.γ
      problem.cfg.challenges.α progIO_capacity memIO_capacity hchained w hKp)

/-! ## Paper-facing exact S6 claim -/

/-- **S6 at one exact configuration and execution**.

One chained semantic witness supplies the exact canonical-RAP problem used by all six accepting
families.  The semantic IO witness, concrete finite-coordinate node encoders, two active-prefix
capacities, characteristic, and `Ksz < p` bound then construct one joint assignment with shared IO.
The conclusion remains visibly indexed by the input `cfg` and dependent `exec` through
`ExactCanonicalRAPProblem.ofChained hchained`; it does not bundle independently quantified
compute, memory, walk, or IO subclaims.

This is the segmented `102/44`, `1-1*` +IO scope.  It does not identify these families with the
paper's final monolithic `199/196` chips. -/
noncomputable def CombinedCompletenessAt
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop :=
  ∀ (hchained : ChainedSemanticExactLanguage cfg exec)
    (_w : SemanticIOWitness cfg exec)
    (hchar : NodeEncoding.StateTagChar K)
    (computeWalkAlpha walkGamma memoryWalkAlpha : K)
    (progIO_capacity :
      exec.derivedRequestIO.length + 1 ≤ 2 ^ cfg.orbit.h)
    (memIO_capacity :
      exec.derivedResponseIO.length + 1 ≤ 2 ^ cfg.orbit.h)
    (p : ℕ) [CharP K p],
    cfg.Ksz < p →
      ∃ requests responses outMem : IOField K,
        JointVerificationProblem
          (PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders
            (ExactCanonicalRAPProblem.ofChained hchained)
            hchar computeWalkAlpha walkGamma memoryWalkAlpha
            requests responses outMem progIO_capacity memIO_capacity) p

/-- **Paper-facing exact S6.**  Every exact configuration/execution has the same-object combined
completeness implication described by `CombinedCompletenessAt`. -/
def ExactChainedHasPerfectCompleteness (F K : Type)
    [Field F] [Field K] [Algebra F K] : Prop :=
  ∀ (cfg : ExactConfig F K) (exec : ExactExecution cfg),
    CombinedCompletenessAt cfg exec

/-- **S6 perfect completeness** at segmented +IO scope.

This is a direct specialization of the concrete-node-encoder joint constructor, so its witness
contains all six accepting families and `SharedIOSat` on one exact `cfg`/`exec`. -/
theorem exactChainedHasPerfectCompleteness (F K : Type)
    [Field F] [Field K] [Algebra F K] :
    ExactChainedHasPerfectCompleteness F K := by
  intro cfg exec hchained w hchar computeWalkAlpha walkGamma memoryWalkAlpha
    progIO_capacity memIO_capacity p _ hKp
  exact
    jointVerification_complete_with_concreteNodeEncoders
      (ExactCanonicalRAPProblem.ofChained hchained) hchar
      computeWalkAlpha walkGamma memoryWalkAlpha
      progIO_capacity memIO_capacity hchained w hKp

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.sharedIOSat_iff_LIO
#print axioms Nock.NockVMROM.Thm54.JointAssignment.six_family_satisfaction
#print axioms Nock.NockVMROM.Thm54.JointAssignment.public_endpoints
#print axioms Nock.NockVMROM.Thm54.TwoRAPRealization
#print axioms Nock.NockVMROM.Thm54.ExactTwoRAPVerification
#print axioms Nock.NockVMROM.Thm54.exactTwoRAPVerification
#print axioms Nock.NockVMROM.Thm54.jointVerification_complete
#print axioms Nock.NockVMROM.Thm54.jointVerification_complete_with_concreteNodeEncoders
#print axioms Nock.NockVMROM.Thm54.jointVerification_complete_with_concreteNodeEncodersScopedP7
#print axioms Nock.NockVMROM.Thm54.ExactChainedHasPerfectCompleteness
#print axioms Nock.NockVMROM.Thm54.exactChainedHasPerfectCompleteness

