import Nock.NockVMROM.Thm54.OptimizedMemoryCodec
import Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace
import Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier

/-!
# Same-object optimized memory semantic carrier

This module does not introduce a replacement trace, forest, or record list.  It wraps one existing
`SampledIOSameExecutionAssignment`; its table auxiliary, one `bfsForest` walk, sampled response
records, multiplicities, and exact execution are therefore definitionally the same objects.  The
only additional field is the production axis-structural refinement already checked by
`ProductionAxisStructureVerifier` and inhabited by the concrete strict package.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedMemorySameExecution

open Nock
open Nock.Framework
open OptimizedMemoryCoreInventory
open OptimizedMemoryCodec
open TemplateAxisCounting

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-- Primitive same-execution input needed to construct the optimized memory chip and its
canonical satisfying trace.  It contains only the exact table, one aggregate forest walk, and
sampled response-IO obligations; the later axis conclusions are deliberately absent.

This is the pre-axis compiler boundary for the paper. -/
structure MemoryChipAssignment
    (A : SampledIOSameExecutionAssignment R p) : Prop where
  obligations : A.MemorySampledObligations

/-- One production memory assignment.  Both proof fields are indexed by `A.exact`'s single
`R.problem`; they cannot select another execution or independently quantified forest
. -/
-- Row-level memory: the executed
-- rows carry `(T, C')`, so the axis accounting (structure, root polynomials) is stated on the
-- a-bearing view `execA`, whose row encode is the executed `R.problem.exec` (`exec_encode`).
-- Chips, IO and table cells (`rootPubZero`) stay on `R.problem.exec`.
structure MemoryProductionAssignment
    (A : SampledIOSameExecutionAssignment R p) (execA : ExactExecution R.problem.cfg) :
    Prop where
  obligations : A.MemorySampledObligations
  /-- The executed memory rows are the Form R row encode of the a-bearing view. -/
  exec_encode : R.problem.exec = execA.encodeMem
  axisStructural :
    ExactAxisStructuralRefinement R.problem.cfg execA
  /-- Honest canonical construction supplies the stronger fixed-polynomial boundary.
  This is intentionally distinct from sampled verifier acceptance, which checks only
  evaluation at the sampled challenge and is guarded by the axis root event. -/
  axisRootPolynomial :
    ∀ i : Fin R.problem.cfg.kMem,
      Nock.AxisBatching.MTree.countsP_bin
        (exactAxisTree R.problem.cfg execA i) = 0
  /-- Indicator twin of `axisRootPolynomial` (`indP_bin` identically 0 at every forest root). -/
  axisRootIndicator :
    ∀ i : Fin R.problem.cfg.kMem,
      Nock.AxisBatching.MTree.indP_bin
        (exactAxisTree R.problem.cfg execA i) = 0
  /-- First-row parent accums vanish (`memory_first_*`, `Corr:forest` at the
      chained dummy).  Later form-R forest roots are the remaining Relaxis
      join (`Batch558.cancellingTree_is_remaining_join`): table cells are
      `(1 − axis)·ts` / `(2 − axis)·ts`, not zero.  Chip `rootMask` completeness
      at `0 < i < kMem` is `LaterSeedZeros`, not this field. -/
  rootPubZero :
    ∀ (i : Fin R.problem.cfg.memRows),
      (i : ℕ) = 0 →
        (R.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (R.problem.exec.memoryPubAt i).pt.indicator = 0

namespace MemoryChipAssignment

variable {A : SampledIOSameExecutionAssignment R p}

/-- Every exact memory row belongs to the same accepted memory table. -/
theorem vmemAt (P : MemoryChipAssignment A)
    (i : Fin R.problem.cfg.memRows) :
    MemoryTable.Vmem R.problem.cfg.challenges.memoryInputs
      (R.problem.exec.memoryPubAt i) := by
  have haccept : exactMemoryChainedAccepts R.problem :=
    (exactChainedHasCanonicalRAP2 F K).memory_iff R.problem |>.2
      ⟨A.exact.memoryTableAux, P.obligations.1⟩
  exact haccept.1 i

/-- The primitive memory-chip assignment already carries the one aggregate forest walk. -/
theorem oneForestWalk (P : MemoryChipAssignment A) :
    Nock.Walk.WalkSat
      (Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows)
      (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
      (Nock.Walk.foCol R.memoryWalkRows)
      A.exact.memoryWalk.ln A.exact.memoryWalk.count A.exact.memoryWalk.acc
      R.memoryWalkAlpha R.memoryWalkSeed
      (R.memoryWalkAlpha ^ R.problem.cfg.kMem)
      R.problem.cfg.memRows ∧
    A.exact.memoryWalk.acc R.problem.cfg.memRows = 0 :=
  P.obligations.2.1

end MemoryChipAssignment

def MemoryProductionAssignment.toChipAssignment
    {A : SampledIOSameExecutionAssignment R p} {execA : ExactExecution R.problem.cfg}
    (P : MemoryProductionAssignment A execA) : MemoryChipAssignment A :=
  ⟨P.obligations⟩

instance {A : SampledIOSameExecutionAssignment R p} {execA : ExactExecution R.problem.cfg} :
    CoeOut (MemoryProductionAssignment A execA) (MemoryChipAssignment A) :=
  ⟨MemoryProductionAssignment.toChipAssignment⟩

namespace MemoryProductionAssignment

variable {A : SampledIOSameExecutionAssignment R p} {execA : ExactExecution R.problem.cfg}

/-- Every exact memory row is a genuine one of the four `Vmem` states on this same execution
. -/
theorem vmemAt (P : MemoryProductionAssignment A execA)
    (i : Fin R.problem.cfg.memRows) :
    MemoryTable.Vmem R.problem.cfg.challenges.memoryInputs
      (R.problem.exec.memoryPubAt i) := by
  have haccept : exactMemoryChainedAccepts R.problem :=
    (exactChainedHasCanonicalRAP2 F K).memory_iff R.problem |>.2
      ⟨A.exact.memoryTableAux, P.obligations.1⟩
  exact haccept.1 i

/-- The carried walk is the one aggregate forest walk, with the paper's preloaded
`Σ RLC(root_i) α^i` seed, initial count `α^k`, every local walk row, and terminal zero
. -/
theorem oneForestWalk (P : MemoryProductionAssignment A execA) :
    Nock.Walk.WalkSat
      (Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows)
      (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
      (Nock.Walk.foCol R.memoryWalkRows)
      A.exact.memoryWalk.ln A.exact.memoryWalk.count A.exact.memoryWalk.acc
      R.memoryWalkAlpha R.memoryWalkSeed
      (R.memoryWalkAlpha ^ R.problem.cfg.kMem)
      R.problem.cfg.memRows ∧
    A.exact.memoryWalk.acc R.problem.cfg.memRows = 0 :=
  P.obligations.2.1

theorem memoryWalkRows_eq_one_bfsForest (P : MemoryProductionAssignment A execA) :
    R.memoryWalkRows = Nock.Walk.bfsForest R.problem.exec.memoryForest := by
  rfl

theorem aggregateRootSeed (P : MemoryProductionAssignment A execA) :
    R.memoryWalkSeed =
      (Nock.Walk.nodeListP
        (Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows)
        R.problem.cfg.kMem).eval R.memoryWalkAlpha := by
  rfl

theorem initialAggregateCount (P : MemoryProductionAssignment A execA) :
    R.memoryWalkAlpha ^ R.problem.cfg.kMem =
      R.memoryWalkAlpha ^ R.problem.cfg.kMem := rfl

/-- Per-root NMR ancestry, unique read timestamps, and the ONE global intermediate matching all
refer to the same exact rows used by `vmemAt` and `oneForestWalk`; this is the multi-root connective
omitted only at the paper's prose level.  The intermediate condition
is stated on the aggregate forest multiset, where the paper puts it. -/
theorem axis_timestamp_intermediate_same_object (P : MemoryProductionAssignment A execA) :
    ExactMemoryAncestry R.problem.cfg execA ∧
      (∀ i, ((AxisBridge.readExps
        (exactAxisTree R.problem.cfg execA i)).map
          (fun e => R.problem.cfg.challenges.α ^ e)).Nodup) ∧
      IO.LmIO R.problem.cfg.Ksz
        (forestReadTimestamps R.problem.cfg execA)
        (forestVerifyTimestamps R.problem.cfg execA) :=
  ⟨P.axisStructural.ancestry,
    P.axisStructural.read_timestamps_nodup,
    P.axisStructural.intermediate_matching⟩

/-- Every used read/verify timestamp in one committed root has the paper's carried
axis.  The nesting, multiplicity-one facts, and zero root polynomial all come from
this same production assignment and its exact `Vmem` forest
. -/
theorem axis_eq_relaxis_of_used
    (h2 : (2 : K) ≠ 0) (P : MemoryProductionAssignment A execA)
    (i : Fin R.problem.cfg.kMem) (e : ℕ)
    (hread : e ∈ AxisBridge.readExps
      (exactAxisTree R.problem.cfg execA i))
    (hverify : e ∈ AxisBridge.verifyExps
      (exactAxisTree R.problem.cfg execA i)) :
    Nock.AxisBatching.MTree.vaxis e
        (exactAxisTree R.problem.cfg execA i) =
      Nock.AxisBatching.MTree.Relaxis e
        (exactAxisTree R.problem.cfg execA i) := by
  let t := exactAxisTree R.problem.cfg execA i
  have hrnd : (AxisBridge.readExps t).Nodup :=
    P.axisStructural.readExps_nodup i
  have hvnd : (AxisBridge.verifyExps t).Nodup :=
    P.axisStructural.verifyExps_nodup i
  have hru : ∀ q, Nock.AxisBatching.MTree.readCount q t ≤ 1 :=
    fun q => AxisBridge.readCount_le_one q t hrnd
  have hvu : ∀ q, Nock.AxisBatching.MTree.verifyCount q t ≤ 1 :=
    fun q => AxisBridge.verifyCount_le_one q t hvnd
  have hn : Nock.AxisBatching.MTree.Nested e t :=
    AxisBridge.nested_of_readVerifyNested t (P.axisStructural.ancestry i) e hru hvu
  have hcounts := AxisBridge.used_once_of_unique_ts e t hrnd hvnd hread hverify
  exact Nock.AxisBatching.MTree.axis_batching_sound h2 t
    (P.axisRootPolynomial i) e hn hcounts.1 hcounts.2

/-- Sampled finite-field response IO, with all pole/RLC/log-derivative exclusions, is carried by
the same exact record lists as the table and forest. -/
theorem sampledMemoryIO (P : MemoryProductionAssignment A execA) :
    FiniteIO.FiniteIOAccepts
        A.sampled.records A.sampled.coins A.sampled.witness ∧
      A.sampled.records.responses = R.problem.exec.derivedResponseIO ∧
      A.sampled.coins.pole ∉
        FiniteIO.IOPoleHitEvent A.sampled.records A.sampled.coins.gamma ∧
      A.sampled.coins.gamma ∉
        FiniteIO.IORLCCollisionEvent A.sampled.records ∧
      A.sampled.coins.pole ∉
        FiniteIO.IOLogDerivEvent A.sampled.records A.sampled.coins.gamma :=
  ⟨P.obligations.2.2.1, A.responses_eq, A.poleHitGood,
    A.sampled.gammaGood, A.sampled.poleGood⟩

end MemoryProductionAssignment

namespace Concrete

open ConcreteStrictPackage
open OptimizedComputeSampledTrace.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- H1.W memory walk-label obligations of the five-row F73 fixture: the encoder is the `x^mem`
projection by construction, and each of the five rows' children carry the declared `lc`/`rc`
cells. -/
theorem honest_memoryWalkLabelObligations : honestSampled.MemoryWalkLabelObligations := by
  refine ⟨fun t => rfl, ?_⟩
  intro t ht
  have hex : honestLegacyFamily.problem.exec.memoryForest =
      (exec honestSeed honestAlpha).memoryForest := by
    change (TemplateRawJointSoundness.specializedProblem timestampStrategy honestSeed
      honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.memoryForest = _
    rw [specializedProblem_eq]
  rw [PlusIOSegmentedFamily.memoryWalkRows, hex] at ht
  simp [exec, dummyHaltTree, dummyHaltRow, dummyHaltPub, readTree, decomposeTree, headTree, verifyTree, tailTree, Walk.bfsForest] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [readRow, decomposeRow, headRow, verifyRow, tailRow, readPub, decomposePub, headPub,
      verifyPub, tailPub, MemoryTable.fanoutMem, MemoryTable.childLinkMem, MemoryTable.memCell,
      Walk.NTree.childLabel, Walk.NTree.childOpt, decomposeTree, headTree, verifyTree,
      tailTree, Fin.forall_fin_two]

theorem honest_memory_obligations :
    honestSampled.MemorySampledObligations := by
  apply honestSampled.memorySampledObligations_of_six
  · change honestAssignment.SixConcreteObligations
    exact (honestAssignment.satisfies_iff_six_concrete_obligations).1
      honestCompletion.assignment.sixFamilies
  · exact honest_memoryWalkLabelObligations

/-- The a-bearing view of the concrete honest execution (`specializeA` of the committed
template): the record holds the address. -/
noncomputable abbrev honestExecA : ExactExecution honestLegacyFamily.problem.cfg :=
  (executionTemplate honestSeed).specializeA honestAlpha MemoryTable.formRDefault

theorem honest_exec_encode :
    honestLegacyFamily.problem.exec = honestExecA.encodeMem := by
  change (TemplateRawJointSoundness.specializedProblem timestampStrategy honestSeed
      honestSeed_ne honestAlpha MemoryTable.formRDefault).exec = _
  exact SemanticTimestampStrategy.ExactExecutionTemplate.specialize_eq_encodeMem
    (executionTemplate honestSeed) honestAlpha MemoryTable.formRDefault

theorem honest_axisStructural :
    ExactAxisStructuralRefinement honestLegacyFamily.problem.cfg honestExecA := by
  have hprod :=
    concreteStrictPackage.strategy.productionAxisAccepts_of_accepts
      honestCoins MemoryTable.formRDefault honestSeed_ne production_accepts_honestCoins
  have hstruct :=
    ProductionAxisStructureVerifier.exactAxisStructuralRefinement_of_accepts
      concreteStrictPackage.strategy.verifier honestCoins MemoryTable.formRDefault honestSeed_ne hprod
  exact hstruct

/-- Both fixed template root polynomials of the concrete honest template vanish identically
(root `1`: `(x − 3)/2 · X` at the a-bearing `x = 3`). -/
theorem honest_template_axis_zero (i : Fin (configTemplate honestSeed).kMem) :
    Nock.AxisBatching.MTree.indP_bin
        (templateAxisTree (templateMemoryTreeAt (executionTemplate honestSeed) i)) = 0 ∧
      templateAxisPolynomial (executionTemplate honestSeed) i = 0 := by
  have hk : (configTemplate honestSeed).kMem = 2 := rfl
  fin_cases i
  · simp [Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, TemplateAxisCounting.templateAxisPolynomial,
      TemplateAxisCounting.templateMemoryTreeAt, executionTemplate,
      dummyHaltTemplateTree, dummyHaltRowTemplate,
      TemplateAxisCounting.templateAxisTree, Nock.AxisBatching.MTree.countsP_bin,
      Nock.AxisBatching.MTree.indP_bin]
  · refine ⟨?_, ?_⟩
    · simp [Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, TemplateAxisCounting.templateMemoryTreeAt, executionTemplate,
        readTemplateTree, decomposeTemplateTree, headTemplateTree, verifyTemplateTree,
        tailTemplateTree, readRowTemplate, decomposeRowTemplate, headRowTemplate,
        verifyRowTemplate, tailRowTemplate, TemplateAxisCounting.templateAxisTree,
        Nock.AxisBatching.MTree.indP_bin]
    · simp [Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, TemplateAxisCounting.templateAxisPolynomial,
        TemplateAxisCounting.templateMemoryTreeAt, executionTemplate,
        readTemplateTree, decomposeTemplateTree, headTemplateTree, verifyTemplateTree,
        tailTemplateTree, readRowTemplate, decomposeRowTemplate, headRowTemplate,
        verifyRowTemplate, tailRowTemplate, TemplateAxisCounting.templateAxisTree,
        Nock.AxisBatching.MTree.countsP_bin, Nock.AxisBatching.MTree.indP_bin,
        verifyPubA, verifyPub, requestRecord]
      letI : CharP K73cubic 73 := concrete_char73
      have htwo : (2 : K73cubic) ≠ 0 := by
        exact SetEq.Lcast_ne_zero (p := 73) (by norm_num) (by norm_num)
      have h3 : (Polynomial.C (3 : K73cubic)) = Polynomial.C 2 + 1 := by
        rw [← map_one Polynomial.C, ← map_add]; norm_num
      rw [h3, show (Polynomial.C (2 : K73cubic) + 1) * Polynomial.X - Polynomial.X =
          Polynomial.C 2 * Polynomial.X by ring, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ htwo, map_one, one_mul, sub_self]

theorem honest_axisRootPolynomial :
    ∀ i : Fin honestLegacyFamily.problem.cfg.kMem,
      Nock.AxisBatching.MTree.countsP_bin
        (exactAxisTree honestLegacyFamily.problem.cfg honestExecA i) = 0 := by
  intro i
  change Nock.AxisBatching.MTree.countsP_bin
      (exactAxisTree ((configTemplate honestSeed).specialize honestAlpha MemoryTable.formRDefault)
        ((executionTemplate honestSeed).specializeA honestAlpha MemoryTable.formRDefault) i) = 0
  rw [(specializeA_axis_bin_eq_reindex (executionTemplate honestSeed) honestAlpha i).2,
    (honest_template_axis_zero i).2, reindexPolynomial_zero]

theorem honest_axisRootIndicator :
    ∀ i : Fin honestLegacyFamily.problem.cfg.kMem,
      Nock.AxisBatching.MTree.indP_bin
        (exactAxisTree honestLegacyFamily.problem.cfg honestExecA i) = 0 := by
  intro i
  change Nock.AxisBatching.MTree.indP_bin
      (exactAxisTree ((configTemplate honestSeed).specialize honestAlpha MemoryTable.formRDefault)
        ((executionTemplate honestSeed).specializeA honestAlpha MemoryTable.formRDefault) i) = 0
  rw [(specializeA_axis_bin_eq_reindex (executionTemplate honestSeed) honestAlpha i).1,
    (honest_template_axis_zero i).1, reindexPolynomial_zero]

theorem honest_rootPubZero :
    ∀ (i : Fin honestLegacyFamily.problem.cfg.memRows),
      (i : ℕ) = 0 →
        (honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0 := by
  change ∀ (i : Fin (TemplateRawJointSoundness.specializedProblem
      ConcreteStrictPackage.timestampStrategy honestSeed honestSeed_ne
      honestAlpha MemoryTable.formRDefault).cfg.memRows),
    (i : ℕ) = 0 →
      ((TemplateRawJointSoundness.specializedProblem
        ConcreteStrictPackage.timestampStrategy honestSeed honestSeed_ne
        honestAlpha MemoryTable.formRDefault).exec.memoryPubAt i).pt.counts = 0 ∧
        ((TemplateRawJointSoundness.specializedProblem
          ConcreteStrictPackage.timestampStrategy honestSeed honestSeed_ne
          honestAlpha MemoryTable.formRDefault).exec.memoryPubAt i).pt.indicator = 0
  rw [ConcreteStrictPackage.specializedProblem_eq]
  intro i hi0
  have hidx : i = ⟨0, by
      change 0 < (ConcreteStrictPackage.cfg honestSeed honestAlpha).memRows
      decide⟩ := Fin.ext hi0
  subst hidx
  rw [ConcreteStrictPackage.memoryPubAt73_0]
  exact ⟨rfl, rfl⟩

/-- Served form-R read-root cell at axis `3`, `ts = α = 4`, row-level `(T, C')` at
    `λ = formRDefault = 2` (`scaleL = λ^{n−1}`): indicator `8·scaleL − scaleL·T·4`,
    counts `12·scaleL − T·C'·4`. -/
theorem honest_served_root_not_table_zero :
    (ConcreteStrictPackage.readPub honestSeed honestAlpha).pt.indicator =
        8 * scaleL - scaleL * rowT * 4 ∧
      (ConcreteStrictPackage.readPub honestSeed honestAlpha).pt.counts =
        12 * scaleL - rowT * rowC * 4 := by
  simp [ConcreteStrictPackage.readPub, ConcreteStrictPackage.seedCell]

/-- Concrete `F73 ⊂ K73cubic` inhabitant of the same-object memory production carrier. -/
noncomputable def honestProduction :
    MemoryProductionAssignment honestSampled honestExecA where
  obligations := honest_memory_obligations
  exec_encode := honest_exec_encode
  axisStructural := honest_axisStructural
  axisRootPolynomial := honest_axisRootPolynomial
  axisRootIndicator := honest_axisRootIndicator
  rootPubZero := honest_rootPubZero

theorem honest_same_object_nonvacuous :
    Nonempty (MemoryProductionAssignment honestSampled honestExecA) :=
  ⟨honestProduction⟩

end Concrete
end
end OptimizedMemorySameExecution
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedMemorySameExecution.MemoryProductionAssignment.vmemAt
#print axioms Nock.NockVMROM.Thm54.OptimizedMemorySameExecution.MemoryProductionAssignment.oneForestWalk
#print axioms Nock.NockVMROM.Thm54.OptimizedMemorySameExecution.MemoryProductionAssignment.axis_timestamp_intermediate_same_object
#print axioms Nock.NockVMROM.Thm54.OptimizedMemorySameExecution.MemoryProductionAssignment.axis_eq_relaxis_of_used
#print axioms Nock.NockVMROM.Thm54.OptimizedMemorySameExecution.Concrete.honest_axisRootPolynomial
#print axioms Nock.NockVMROM.Thm54.OptimizedMemorySameExecution.Concrete.honest_served_root_not_table_zero
#print axioms Nock.NockVMROM.Thm54.OptimizedMemorySameExecution.Concrete.honest_same_object_nonvacuous
