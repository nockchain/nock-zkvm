import Nock.NockVMROM.Thm54.BuildableExecution
import Nock.NockVMROM.Thm54.OptimizedStrictFullPackageConcrete
import Nock.NockVMROM.Thm54.RawTopologyAIR
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Data-bearing staged topology output

This module defines the output side of the universal constructor without claiming that the
universal constructor already exists.  `BuildableTopology` contains only data.  RAP satisfaction
is stated separately in `BuildableTraceSatisfaction`.

At this milestone the optimized chips, fixed preprocessing, active domains, coordinate layouts,
canonical IO lists, raw topology payload arrays, topology AIRs, and verifier-generated topology
traces can all be organized without adding proof-premise fields.  Canonical optimized polynomial
traces still require the later sampled-IO/chip constructor, so they live in the separate staged
`BuildableTopologyTraces` record.  The missing generic functions are named explicitly by
`BuildableTopologyConstructor` and `BuildableTopologyTraceConstructor`; neither is assumed.
-/

namespace Nock.NockVMROM.Thm54

open Nock Nock.Framework
open Module StrictExtension
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- Data-only walk/IO family fields, indexed definitionally by one buildable execution.

Unlike `PlusIOSegmentedFamily`, this record contains no injectivity, capacity, table-satisfaction,
walk-satisfaction, or IO-acceptance proof. -/
structure BuildableRawFamily (E : BuildableNockExecution F K) where
  computeWalkAlpha : K
  memoryWalkAlpha : K
  walkGamma : K
  compNodeWidth : ℕ
  compNodeEncode :
    (ComputeTable.State × ComputeTable.DTcomp K) → Fin compNodeWidth → K
  memNodeWidth : ℕ
  memNodeEncode :
    (MemoryTable.MState × MemoryTable.DTmem K) → Fin memNodeWidth → K
  requests : IOField K
  responses : IOField K
  outMem : IOField K

namespace BuildableRawFamily

variable {E : BuildableNockExecution F K}

/-- Reuse the existing data-only family with the input `cfg`/`exec` inserted definitionally. -/
def toRawPlusIOSegmentedFamily (R : BuildableRawFamily E) :
    RawPlusIOSegmentedFamily F K where
  problem := ⟨E.cfg, E.exec⟩
  computeWalkAlpha := R.computeWalkAlpha
  memoryWalkAlpha := R.memoryWalkAlpha
  walkGamma := R.walkGamma
  compNodeWidth := R.compNodeWidth
  compNodeEncode := R.compNodeEncode
  memNodeWidth := R.memNodeWidth
  memNodeEncode := R.memNodeEncode
  requests := R.requests
  responses := R.responses
  outMem := R.outMem

end BuildableRawFamily

/-- Data-bearing staged output for one exact buildable execution.

The optimized chips and their verifier-fixed preprocessing are derived below from these primitive
data.  The topology payload arrays are actual arrays, not topology-validity premises. -/
structure BuildableTopology (E : BuildableNockExecution F K) where
  /-- Data-only family whose problem is definitionally `E.cfg/E.exec`. -/
  raw : BuildableRawFamily E
  /-- Height parameter of the strict cubic base-field orbit. -/
  hOrb : ℕ
  /-- Cubic coordinate basis used by both optimized chips. -/
  basis : Basis (Fin 3) F K
  /-- Strict base-field orbit of exact order `3 * 2^hOrb`. -/
  orbit : StrictOrbitDomain F 3 hOrb
  /-- Active compute interpolation nodes. -/
  computeNodes : Fin E.cfg.compRows → F
  /-- Active memory interpolation nodes. -/
  memoryNodes : Fin E.cfg.memRows → F
  /-- Complete optimized-compute challenge coordinate layout. -/
  computeChallenge : ℕ → F
  /-- Complete optimized-compute public coordinate layout. -/
  computePublic : ℕ → F
  /-- Complete optimized-memory challenge coordinate layout. -/
  memoryChallenge : ℕ → F
  /-- Complete optimized-memory public coordinate layout. -/
  memoryPublic : ℕ → F
  /-- Actual optimized fixed-preprocessing compute chip.  Its correspondence to the metadata is a
  separate correctness proposition, not a constructor premise. -/
  computeChipData : FixedPreprocessingRAP F
  /-- Actual optimized fixed-preprocessing memory chip. -/
  memoryChipData : FixedPreprocessingRAP F
  /-- Actual compute child-payload arrays, three slots per active row. -/
  computeChildPayload :
    Fin E.cfg.compRows → Fin 3 → ComputeLinkPayload K
  /-- Actual memory child-payload arrays, two slots per active row. -/
  memoryChildPayload :
    Fin E.cfg.memRows → Fin 2 → MemoryTable.Cell K

namespace BuildableTopology

variable {E : BuildableNockExecution F K}
variable (T : BuildableTopology E)

/-- The exact data-only topology family, definitionally on the input problem. -/
def rawFamily : RawPlusIOSegmentedFamily F K :=
  T.raw.toRawPlusIOSegmentedFamily

/-- The two actual topology payload arrays. -/
def topologyArrays : RawTopologyArrays T.rawFamily where
  compute := ⟨T.computeChildPayload⟩
  memory := ⟨T.memoryChildPayload⟩

/-- The optimized fixed-preprocessing compute chip (`199/98` in the cubic realization). -/
def computeChip : FixedPreprocessingRAP F :=
  T.computeChipData

/-- The optimized fixed-preprocessing memory chip (`196/104` in the cubic realization). -/
def memoryChip : FixedPreprocessingRAP F :=
  T.memoryChipData

/-- Verifier-fixed compute preprocessing polynomials, exposed as output data. -/
def computePreprocessing : Fin (computeChip T).fixedCount → F[X] :=
  (computeChip T).preprocessing

/-- Verifier-fixed memory preprocessing polynomials, exposed as output data. -/
def memoryPreprocessing : Fin (memoryChip T).fixedCount → F[X] :=
  (memoryChip T).preprocessing

/-- Active compute row domain of the actual optimized chip. -/
def computeDomain : Finset F :=
  (computeChip T).rap.H

/-- Active memory row domain of the actual optimized chip. -/
def memoryDomain : Finset F :=
  (memoryChip T).rap.H

/-- Canonical finite IO lists are functions of the input execution, not caller-selected output. -/
def requestIO : List (Fin 9 → K) :=
  E.exec.derivedRequestIO

/-- Canonical finite response list from the same execution. -/
def responseIO : List (Fin 9 → K) :=
  E.exec.derivedResponseIO

/-- The exportable compute topology AIR syntax. -/
def computeTopologyAIR : Nock.Reified.AIR :=
  RawTopologyAIR.computeAIR

/-- The exportable memory topology AIR syntax. -/
def memoryTopologyAIR : Nock.Reified.AIR :=
  RawTopologyAIR.memoryAIR

/-- Verifier-generated compute topology polynomial trace from the actual payload arrays. -/
def computeTopologyTrace :
    Fin RawTopologyAIR.computeAIR.numTraceCols → K[X] :=
  Nock.NockVMROM.Thm54.computeTopologyTrace T.rawFamily T.topologyArrays.compute

/-- Verifier-generated memory topology polynomial trace from the actual payload arrays. -/
def memoryTopologyTrace :
    Fin RawTopologyAIR.memoryAIR.numTraceCols → K[X] :=
  Nock.NockVMROM.Thm54.memoryTopologyTrace T.rawFamily T.topologyArrays.memory

-- Definitional cfg/exec identity: the output topology family cannot select another problem.
omit [FiniteDimensional F K] in
theorem rawFamily_problem :
    T.rawFamily.problem = ⟨E.cfg, E.exec⟩ :=
  rfl

end BuildableTopology

/-- Staged optimized polynomial traces.  These are data only; satisfaction is separate. -/
structure BuildableTopologyTraces {E : BuildableNockExecution F K}
    (T : BuildableTopology E) where
  compute : Fin (BuildableTopology.computeChip T).rap.w → F[X]
  memory : Fin (BuildableTopology.memoryChip T).rap.w → F[X]

/-- Correctness proposition kept separate from `BuildableTopology` and its trace data. -/
structure BuildableTraceSatisfaction {E : BuildableNockExecution F K}
    (T : BuildableTopology E) (Q : BuildableTopologyTraces T) : Prop where
  compute :
    RAP.SatisfiesWithPreprocessing (BuildableTopology.computeChip T) Q.compute
  memory :
    RAP.SatisfiesWithPreprocessing (BuildableTopology.memoryChip T) Q.memory

/-- The still-missing generic Milestone-2+ topology constructor, named without assuming it. -/
abbrev BuildableTopologyConstructor (F K : Type) [Field F] [Field K] [Algebra F K] :=
  (E : BuildableNockExecution F K) → BuildableTopology E

/-- The still-missing generic canonical-trace constructor over a supplied topology builder. -/
abbrev BuildableTopologyTraceConstructor
    (build : BuildableTopologyConstructor F K) :=
  (E : BuildableNockExecution F K) → BuildableTopologyTraces (build E)

/-! ## Existing F73 fixture through the new API -/

namespace BuildableConcrete

open Module
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open TemplateAxisCounting
open ConcreteStrictPackage
open OptimizedComputeSampledTrace.Concrete
open OptimizedMemoryCanonicalSatisfaction.Concrete
open OptimizedStrictPackage.Concrete
open OptimizedStrictFullPackage.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- The F73 execution satisfies the exact noun-realized, chained, arity-3/2 input language. -/
theorem concreteLanguage :
    NounRealizedTraversableChainedSemanticExactLanguage 73
      (ConcreteStrictPackage.cfg honestSeed honestAlpha)
      (ConcreteStrictPackage.exec honestSeed honestAlpha) := by
  have htop := ConcreteStrictPackage.honest_exactTopology
  let R := RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily
  let P : RawProblem F73 K73cubic :=
    ⟨ConcreteStrictPackage.cfg honestSeed honestAlpha,
      ConcreteStrictPackage.exec honestSeed honestAlpha⟩
  have hp : R.problem = P := ConcreteStrictPackage.honestRawLegacy_problem
  have htransport :
      (ComputeExactTopology R.exec ∧ MemoryExactTopology R.exec) =
        (ComputeExactTopology P.exec ∧ MemoryExactTopology P.exec) :=
    congrArg
      (fun Q : RawProblem F73 K73cubic =>
        ComputeExactTopology Q.exec ∧ MemoryExactTopology Q.exec) hp
  have htop' : ComputeExactTopology P.exec ∧ MemoryExactTopology P.exec :=
    Eq.mp htransport htop
  refine
    { traversable :=
        { chained := ConcreteStrictPackage.honest_chained
          compute_topology := htop'.1
          memory_topology := htop'.2 }
      nounRealization := ?_ }
  exact (ConcreteStrictPackage.bindsAt honestSeed honestAlpha).nounRealization
    honestSeed_ne ConcreteStrictPackage.skeletonBounded

/-- The existing concrete production witness supplies the strengthened row-level semantic CORE.
Only its semantic-row fields are retained here; its separately proved axis conclusions are not
stored in `BuildableNockExecution`. -/
noncomputable def concreteSemanticData :
    SemanticTrace.ExactExecutionSemanticData 73 2
      (ConcreteStrictPackage.cfg honestSeed honestAlpha)
      (ConcreteStrictPackage.exec honestSeed honestAlpha) := by
  have htarget : Nonempty
      (ProductionP8Containment.GenuineWitness concreteStrictPackage.strategy 73 2
        honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault) := by
    simpa [ProductionP8Containment.GenuineTargetAt,
      ConcreteStrictPackage.honestSeed_ne, ConcreteStrictPackage.honestCoins,
      nprSeed, alphaM, proof_irrel_heq] using
        ConcreteStrictPackage.honest_genuineTarget
  let W := Classical.choice htarget
  let P₁ := TemplateRawJointSoundness.specializedProblem
    ConcreteStrictPackage.verifier.raw.timestamp honestSeed honestSeed_ne honestAlpha
    MemoryTable.formRDefault
  let P₂ : RawProblem F73 K73cubic :=
    ⟨ConcreteStrictPackage.cfg honestSeed honestAlpha,
      ConcreteStrictPackage.exec honestSeed honestAlpha⟩
  have hp : P₁ = P₂ :=
    ConcreteStrictPackage.verifier_specializedProblem honestSeed honestSeed_ne honestAlpha
  let LanguageAt := fun P : RawProblem F73 K73cubic =>
    NounRealizedTraversableChainedSemanticExactLanguage 73 P.cfg P.exec
  let DataAt := fun P : RawProblem F73 K73cubic =>
    SemanticTrace.ExactExecutionSemanticData 73 2 P.cfg P.exec
  have language₁ : LanguageAt P₁ :=
    Eq.mp (congrArg LanguageAt hp).symm concreteLanguage
  have rowsAccepted₁ : P₁.exec.ComputeRowsAccepted := by
    change concreteStrictPackage.strategy.specializedExec
      honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault |>.ComputeRowsAccepted
    exact W.computeRowsAccepted
  let data₁ : DataAt P₁ :=
    { language := language₁
      rowAccepted := fun i => ExactExecution.computeRowAt_accepted rowsAccepted₁ i
      rows := fun i => W.canonicalRows i }
  exact Eq.mp (congrArg DataAt hp) data₁

/-- The one concrete OP1 request is nevertheless a genuine Nock slot service: axis `3` selects
the formula tail.  Its read and verify occur in the same supplied memory root. -/
noncomputable def concreteMemoryService :
    ServedMemoryTrace.Service
      (ConcreteStrictPackage.cfg honestSeed honestAlpha)
      (ConcreteStrictPackage.execA honestSeed honestAlpha) where
  exponent := timestampExp honestAlpha honestAlpha
  record := ConcreteStrictPackage.requestRecord honestSeed honestAlpha
  root := ConcreteStrictPackage.formulaNoun
  child := ConcreteStrictPackage.resultNoun
  axis := 3
  request_mem := by
    rw [ExactExecution.rawRequests,
      show (ConcreteStrictPackage.execA honestSeed honestAlpha).computeRows =
        (ConcreteStrictPackage.exec honestSeed honestAlpha).computeRows from rfl,
      (ConcreteStrictPackage.execution_rows _ _).1]
    simp [ConcreteStrictPackage.computeRow, ConcreteStrictPackage.computePub,
      NockVM.activeRequestRecords]
  timestamp := by
    exact timestampExp_spec
      (show TimestampClosedAt honestAlpha honestAlpha from ⟨1, by simp⟩)
  realization := by
    exact
      { root_realizes := by rfl
        child_realizes := by rfl
        axis_realizes := by
          simp [ConcreteStrictPackage.requestRecord] }
  served := by
    simp [ConcreteStrictPackage.formulaNoun, ConcreteStrictPackage.resultNoun,
      Noun.slot]

theorem concreteMemoryTreeAt_dummy :
    (ConcreteStrictPackage.execA honestSeed honestAlpha).memoryTreeAt
      ⟨0, by simp [ConcreteStrictPackage.cfg]⟩ =
      ConcreteStrictPackage.dummyHaltTree honestSeed :=
  rfl

theorem concreteMemoryTreeAt_read :
    (ConcreteStrictPackage.execA honestSeed honestAlpha).memoryTreeAt
      ⟨1, by simp [ConcreteStrictPackage.cfg]⟩ =
      ConcreteStrictPackage.readTreeA honestSeed honestAlpha :=
  rfl

/-- Dummy halt first forest root (`kMem = 2`): a record-free `S_leaf` seed. -/
theorem concreteAxisTree_dummy :
    exactAxisTree
        (ConcreteStrictPackage.cfg honestSeed honestAlpha)
        (ConcreteStrictPackage.execA honestSeed honestAlpha)
        ⟨0, by simp [ConcreteStrictPackage.cfg]⟩ = .halt := by
  rw [exactAxisTree, concreteMemoryTreeAt_dummy]
  simp [ConcreteStrictPackage.dummyHaltTree, ConcreteStrictPackage.dummyHaltRow,
    ConcreteStrictPackage.dummyHaltPub, AxisBridge.ofNTree, AxisBridge.MemWalk.toMTree]

set_option maxRecDepth 300000 in
/-- The five-row `read_root`/`decompose`/`verify_child` tree is forest index 1. -/
theorem concreteAxisTree_read :
    exactAxisTree
        (ConcreteStrictPackage.cfg honestSeed honestAlpha)
        (ConcreteStrictPackage.execA honestSeed honestAlpha)
        ⟨1, by simp [ConcreteStrictPackage.cfg]⟩ =
      .read (timestampExp honestAlpha honestAlpha)
        (.decompose .halt
          (.verify (timestampExp honestAlpha honestAlpha) (3 : K73cubic) .halt)) := by
  rw [exactAxisTree, concreteMemoryTreeAt_read]
  simp [ConcreteStrictPackage.readTreeA, ConcreteStrictPackage.decomposeTreeA,
    ConcreteStrictPackage.headTree, ConcreteStrictPackage.verifyTreeA,
    ConcreteStrictPackage.tailTree, ConcreteStrictPackage.readRowA,
    ConcreteStrictPackage.decomposeRow, ConcreteStrictPackage.headRow,
    ConcreteStrictPackage.verifyRowA, ConcreteStrictPackage.tailRow,
    AxisBridge.ofNTree, AxisBridge.MemWalk.toMTree, ConcreteStrictPackage.readPub,
        ConcreteStrictPackage.readPubA,
    ConcreteStrictPackage.verifyPub, ConcreteStrictPackage.verifyPubA,
        ConcreteStrictPackage.requestRecord,
    ConcreteStrictPackage.cfg, timestampExpAt]

/-- Forest case split: dummy halt at `0`, the OP1 read tree at `1`. -/
theorem concreteAxisTree
    (i : Fin (ConcreteStrictPackage.cfg honestSeed honestAlpha).kMem) :
    exactAxisTree
        (ConcreteStrictPackage.cfg honestSeed honestAlpha)
        (ConcreteStrictPackage.execA honestSeed honestAlpha) i =
      if (i : ℕ) = 0 then .halt
      else
        .read (timestampExp honestAlpha honestAlpha)
          (.decompose .halt
            (.verify (timestampExp honestAlpha honestAlpha) (3 : K73cubic) .halt)) := by
  rcases i with ⟨i, hi⟩
  have hi' : i < 2 := by simpa [ConcreteStrictPackage.cfg] using hi
  interval_cases i
  · simpa using concreteAxisTree_dummy
  · simpa using concreteAxisTree_read

/-- The Nock axis `3` of the concrete service is the single right-descent route. -/
theorem concreteAxisPath : ServedMemoryTrace.axisPath 3 = [true] := by
  rw [ServedMemoryTrace.axisPath_of_two_le (by norm_num)]
  norm_num [ServedMemoryTrace.axisPath_of_lt_two]

/-- Empty service partition of the dummy halt seed. -/
noncomputable def concreteDummyServedRoot :
    ServedMemoryTrace.RootTrace
      (ConcreteStrictPackage.cfg honestSeed honestAlpha)
      (ConcreteStrictPackage.execA honestSeed honestAlpha)
      ⟨0, by simp [ConcreteStrictPackage.cfg]⟩ where
  subject := .atom 0
  services := []
  recordPartition := by
    simp [ServedMemoryTrace.rootResponseRecords, concreteMemoryTreeAt_dummy,
      ConcreteStrictPackage.dummyHaltTree, ConcreteStrictPackage.dummyHaltRow,
      ConcreteStrictPackage.dummyHaltPub, Nock.Walk.bfsForest,
      MemoryTable.responseRecords]
  readPartition := by
    rw [concreteAxisTree_dummy]
    simp [readExps]
  verifyPartition := by
    rw [concreteAxisTree_dummy]
    simp [verifyExps]
  traversal := by
    rw [concreteAxisTree_dummy]
    exact ServedMemoryTrace.ServiceWalk.halt

/-- OP1 read-root partition at forest index 1. -/
noncomputable def concreteReadServedRoot :
    ServedMemoryTrace.RootTrace
      (ConcreteStrictPackage.cfg honestSeed honestAlpha)
      (ConcreteStrictPackage.execA honestSeed honestAlpha)
      ⟨1, by simp [ConcreteStrictPackage.cfg]⟩ where
  subject := ConcreteStrictPackage.formulaNoun
  services := [concreteMemoryService]
  recordPartition := by
    simp [ServedMemoryTrace.rootResponseRecords, concreteMemoryTreeAt_read,
      ConcreteStrictPackage.readTreeA, ConcreteStrictPackage.decomposeTreeA,
      ConcreteStrictPackage.headTree, ConcreteStrictPackage.verifyTreeA,
      ConcreteStrictPackage.tailTree, ConcreteStrictPackage.readRowA,
      ConcreteStrictPackage.decomposeRow, ConcreteStrictPackage.headRow,
      ConcreteStrictPackage.verifyRowA, ConcreteStrictPackage.tailRow,
      Nock.Walk.bfsForest, MemoryTable.responseRecords,
      ConcreteStrictPackage.readPub, ConcreteStrictPackage.readPubA,
          ConcreteStrictPackage.decomposePub,
      ConcreteStrictPackage.headPub, ConcreteStrictPackage.verifyPub,
          ConcreteStrictPackage.verifyPubA,
      ConcreteStrictPackage.tailPub, ConcreteStrictPackage.requestRecord,
      concreteMemoryService]
  readPartition := by
    rw [concreteAxisTree_read]
    simp [concreteMemoryService, readExps]
  verifyPartition := by
    rw [concreteAxisTree_read]
    simp [concreteMemoryService, verifyExps]
  traversal := by
    rw [concreteAxisTree_read]
    refine ServedMemoryTrace.ServiceWalk.read concreteMemoryService (by simp) rfl rfl ?_ ?_
    · rw [show concreteMemoryService.axis = 3 from rfl, concreteAxisPath]
      exact ServedMemoryTrace.VerifyRoute.right (by simp [readCount]) (by simp [verifyCount])
        (ServedMemoryTrace.VerifyRoute.here rfl rfl (by simp [readCount])
          (by simp [verifyCount]))
    · exact ServedMemoryTrace.ServiceWalk.decompose
        ServedMemoryTrace.ServiceWalk.halt
        (ServedMemoryTrace.ServiceWalk.verify ServedMemoryTrace.ServiceWalk.halt)

/-- Concrete root partition: dummy halt at `0`, OP1 read tree at `1`. -/
noncomputable def concreteServedMemoryRoots :
    ∀ i : Fin (ConcreteStrictPackage.cfg honestSeed honestAlpha).kMem,
      ServedMemoryTrace.RootTrace
        (ConcreteStrictPackage.cfg honestSeed honestAlpha)
        (ConcreteStrictPackage.execA honestSeed honestAlpha) i
  | ⟨0, _⟩ => concreteDummyServedRoot
  | ⟨1, _⟩ => concreteReadServedRoot
  | ⟨n + 2, h⟩ =>
      absurd (show n + 2 < 2 by simp only [ConcreteStrictPackage.cfg] at h; exact h)
        (by omega)

theorem concreteServedMemoryRoots_range :
    List.finRange (ConcreteStrictPackage.cfg honestSeed honestAlpha).kMem =
      [⟨0, by simp [ConcreteStrictPackage.cfg]⟩,
        ⟨1, by simp [ConcreteStrictPackage.cfg]⟩] := by
  simp [ConcreteStrictPackage.cfg, List.finRange]

/-- Concrete non-vacuity for the same-execution served-memory CORE.  The terminal OP1 row has no
OP0/OP9 semantic lookup to cover, while its ordinary recursive memory service remains traversed. -/
noncomputable def concreteServedMemoryTrace :
    ServedMemoryTrace.ExactServedMemoryTrace
      73 2
      (ConcreteStrictPackage.cfg honestSeed honestAlpha)
      (ConcreteStrictPackage.exec honestSeed honestAlpha)
      concreteSemanticData
      (ConcreteStrictPackage.execA honestSeed honestAlpha) where
  roots := concreteServedMemoryRoots
  timestampPowersNodup := by
    rw [concreteServedMemoryRoots_range]
    simp [ServedMemoryTrace.RootTrace.timestampPowers,
      ServedMemoryTrace.RootTrace.exponents, concreteServedMemoryRoots,
      concreteDummyServedRoot, concreteReadServedRoot, concreteMemoryService]
  forestIndexRange := by
    have hlen :
        ((List.finRange (ConcreteStrictPackage.cfg honestSeed honestAlpha).kMem).flatMap
          (fun i => (concreteServedMemoryRoots i).timestampPowers)).length = 1 := by
      rw [concreteServedMemoryRoots_range]
      simp [List.flatMap, ServedMemoryTrace.RootTrace.timestampPowers,
        ServedMemoryTrace.RootTrace.exponents, concreteServedMemoryRoots,
        concreteDummyServedRoot, concreteReadServedRoot, concreteMemoryService]
    change IO.InRange (ConcreteStrictPackage.cfg honestSeed honestAlpha).Ksz _
    rw [hlen]
    simp [IO.InRange, ConcreteStrictPackage.cfg]
  semanticCoverage := by
    intro row lookup hlookup
    have hstate :
        ((ConcreteStrictPackage.exec honestSeed honestAlpha).computeRowAt row).1 = .s1 := by
      rcases row with ⟨row, hrow⟩
      have hrow0 : row = 0 := by
        have : row < 1 := by simpa [ConcreteStrictPackage.cfg] using hrow
        omega
      subst row
      norm_num [ExactExecution.computeRowAt, ExactExecution.computeRows,
        ConcreteStrictPackage.exec, Nock.Walk.bfsForest, ConcreteStrictPackage.cfg,
        ConcreteStrictPackage.computeRow]
    have hlen :
        (concreteSemanticData.rows row).needs.served.length = 0 := by
      rw [(concreteSemanticData.rows row).needs.served_count]
      simp [SemanticTrace.requiredServedLookups, hstate]
    rw [List.eq_nil_of_length_eq_zero hlen] at hlookup
    simp at hlookup

/-- Existing concrete exact execution, re-expressed through the minimal input API. -/
def concreteExecution : BuildableNockExecution F73 K73cubic where
  q := 73
  q_gt_one := by norm_num
  Λ := 2
  cfg := ConcreteStrictPackage.cfg honestSeed honestAlpha
  execA := ConcreteStrictPackage.execA honestSeed honestAlpha
  exec := ConcreteStrictPackage.exec honestSeed honestAlpha
  exec_encode := ConcreteStrictPackage.exec_eq_encodeMem honestSeed honestAlpha
  semanticData := concreteSemanticData
  memoryTrace := concreteServedMemoryTrace
  requestNodup := by
    rw [ConcreteStrictPackage.derived_request_singleton]
    simp
  recordCountBalance := ConcreteStrictPackage.recordCountBalance
  q_le_ringChar := by
    rw [← ConcreteStrictPackage.q_eq_ringChar]
  two_ne_zero := by
    intro hk
    have hbase : (2 : F73) ≠ 0 := by decide
    apply hbase
    apply (algebraMap F73 K73cubic).injective
    simpa only [map_ofNat, map_zero] using hk
  Ksz_lt_ringChar := by
    rw [← ConcreteStrictPackage.q_eq_ringChar]
    norm_num [ConcreteStrictPackage.cfg]
  programIOCapacity := by
    rw [ConcreteStrictPackage.derived_request_singleton]
    norm_num [ConcreteStrictPackage.cfg, ConcreteStrictPackage.executionOrbit]
  memoryIOCapacity := by
    rw [ConcreteStrictPackage.derived_response_singleton]
    norm_num [ConcreteStrictPackage.cfg, ConcreteStrictPackage.executionOrbit]

/-- Data-only raw family for the same concrete cfg/exec. -/
def concreteRawFamily : BuildableRawFamily concreteExecution :=
  let R := RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily
  { computeWalkAlpha := R.computeWalkAlpha
    memoryWalkAlpha := R.memoryWalkAlpha
    walkGamma := R.walkGamma
    compNodeWidth := R.compNodeWidth
    compNodeEncode := R.compNodeEncode
    memNodeWidth := R.memNodeWidth
    memNodeEncode := R.memNodeEncode
    requests := R.requests
    responses := R.responses
    outMem := R.outMem }

/-- Existing concrete optimized/topology data, with no optimized package stored in the new API. -/
def concreteTopology : BuildableTopology concreteExecution :=
  let R := concreteRawFamily.toRawPlusIOSegmentedFamily
  let A := honestTopologyArrays R
  { raw := concreteRawFamily
    hOrb := 2
    basis := basis73
    orbit := strictOrbit
    computeNodes := fun _ => 1
    memoryNodes := fun i => strictOrbit.βcoset * strictOrbit.ω ^ (i : ℕ)
    computeChallenge := Nock.RedTeam.Batch62.concreteChallengeCoordinates
    computePublic := Nock.RedTeam.Batch62.concretePublicCoordinates
    memoryChallenge := honestMemoryChalVal
    memoryPublic := honestMemoryPubVal
    computeChipData :=
      OptimizedComputeCorrectedFinal.ProductionNamedComputeRAP
        concreteOptimizedStrictPackage.family.problem.cfg.compRows_pos
        concreteOptimizedStrictPackage.computeNodes
        concreteOptimizedStrictPackage.basis
        concreteOptimizedStrictPackage.computeChallenge
        concreteOptimizedStrictPackage.computePublic
        concreteOptimizedStrictPackage.orbit
    memoryChipData :=
      OptimizedMemoryRAP.namedFinalMemoryRAP
        concreteOptimizedStrictPackage.family.problem.cfg.memRows_pos
        concreteOptimizedStrictPackage.memoryNodes
        concreteOptimizedStrictPackage.basis
        concreteOptimizedStrictPackage.memoryChallenge
        concreteOptimizedStrictPackage.memoryPublic
        concreteOptimizedStrictPackage.orbit
        concreteOptimizedStrictPackage.family.problem.cfg.kMem
    computeChildPayload := A.compute.childPayload
    memoryChildPayload := A.memory.childPayload }

/-- Existing canonical F73 optimized traces through the staged output API. -/
def concreteTraces : BuildableTopologyTraces concreteTopology where
  compute := concreteComputeTrace
  memory := concreteMemoryTrace

-- The old F73 witness also proves the separate trace-correctness proposition.
-- `hmore` is the remaining Relaxis join at form R (`kMem = 2` dummy halt).
set_option maxRecDepth 300000 in
theorem concreteTraceSatisfaction
    (hbasis : OptimizedComputeFinalTrace.FormRBasis basis73)
    (hmore : ∀ i : Fin honestLegacyFamily.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < honestLegacyFamily.problem.cfg.kMem →
        (honestLegacyFamily.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (honestLegacyFamily.problem.exec.memoryPubAt i).pt.indicator = 0) :
    BuildableTraceSatisfaction concreteTopology concreteTraces := by
  have h :=
    OptimizedStrictPackage.Concrete.concrete_source_and_final_satisfaction hbasis hmore
  constructor
  · exact h.1
  · exact h.2

/-- Concrete non-vacuity of both the minimal input and data-bearing output APIs. -/
theorem concrete_nonvacuous :
    Nonempty (BuildableNockExecution F73 K73cubic) ∧
      Nonempty (BuildableTopology concreteExecution) ∧
      Nonempty (BuildableTopologyTraces concreteTopology) :=
  ⟨⟨concreteExecution⟩, ⟨concreteTopology⟩, ⟨concreteTraces⟩⟩

end BuildableConcrete

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.BuildableTopology.rawFamily_problem
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteLanguage
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteSemanticData
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteMemoryService
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteServedMemoryTrace
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteExecution
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteTopology
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concreteTraceSatisfaction
#print axioms Nock.NockVMROM.Thm54.BuildableConcrete.concrete_nonvacuous
