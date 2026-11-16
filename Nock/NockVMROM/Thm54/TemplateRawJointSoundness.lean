import Nock.NockVMROM.Thm54.SemanticTimestampStrategy
import Nock.NockVMROM.Thm54.RawTopologyRAP
import Nock.NockVMROM.Thm54.P8Census

/-!
This module gives the production chronology missing from `RawP8Strategy`:

* the semantic skeleton (and hence its public claim) is fixed before `z`;
* the complete timestamp/configuration/execution template is fixed after nonzero `z`;
* the exact problem, table arrays, IO arrays, and endpoints are fixed after `alphaM`, through an
  API which has no `alphaC` or `gamma` argument;
* the full-coin response contains only `RawWalkArrays`.

The verifier message is still genuinely raw.  No table-WF, RVT, evaluator, target, or semantic
proof is carried by `RawMessage` or tested by `RawAccepts`.
-/

open scoped BigOperators Classical

namespace Nock.NockVMROM.Thm54.TemplateRawJointSoundness

open Nock Nock.Walk
open SemanticTimestampStrategy

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {p : ℕ} [CharP K p]

/-! ## The `(z, alphaM)`-specialized raw problem -/

/-- The exact raw problem generated from the complete seed-fixed carrier by supplying only the
sampled timestamp/memory-walk challenge `alphaM` and the Form R `λ` drawn in the same round. -/
def specializedProblem
    (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) (alphaM lmb : K) : RawProblem F K where
  cfg := (T.afterSeed ⟨z, hz⟩).configTemplate.specialize alphaM lmb
  exec := (T.afterSeed ⟨z, hz⟩).executionTemplate.specialize alphaM lmb

/-- The a-bearing view of the specialized execution (`ExactExecutionTemplate.specializeA`): the
object all axis accounting is stated on. -/
def specializedExecA
    (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) (alphaM lmb : K) : ExactExecution (specializedProblem T z hz alphaM lmb).cfg :=
  (T.afterSeed ⟨z, hz⟩).executionTemplate.specializeA alphaM lmb

@[simp] theorem specializedProblem_tableAlpha
    (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) (alphaM lmb : K) :
    (specializedProblem T z hz alphaM lmb).cfg.challenges.α = alphaM :=
  rfl

@[simp] theorem specializedProblem_tableLam
    (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) (alphaM lmb : K) :
    (specializedProblem T z hz alphaM lmb).cfg.challenges.lam = lmb :=
  rfl

/-- Every memory row of the specialized execution carries the sampled `λ`: the template is
λ-free and `specialize α λ` writes `λ` into every row (`specialize_memory_lambda`).  This is the
former `memoryLambdaUniform` residual, now a theorem of the template chronology. -/
theorem specializedProblem_memoryLambda
    (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) (alphaM lmb : K)
    (i : Fin (specializedProblem T z hz alphaM lmb).cfg.memRows) :
    ((specializedProblem T z hz alphaM lmb).exec.memoryPubAt i).lambda =
      (specializedProblem T z hz alphaM lmb).cfg.challenges.lam :=
  (T.afterSeed ⟨z, hz⟩).executionTemplate.specialize_memory_lambda alphaM lmb _
    ((specializedProblem T z hz alphaM lmb).exec.memoryRowAt_mem i)

@[simp] theorem specializedProblem_seed
    (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) (alphaM lmb : K) :
    (specializedProblem T z hz alphaM lmb).cfg.challenges.z = z := by
  exact (T.afterSeed ⟨z, hz⟩).sampledSeed

/-- Raw family data fixed after `(z, alphaM)`.  There is no `alphaC` or `gamma` in this structure.
The zero placeholders are overwritten only when the public coins are inserted. -/
structure AlphaMFamilyData
    (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) (alphaM lmb : K) where
  compNodeWidth : ℕ
  compNodeEncode :
    (ComputeTable.State × ComputeTable.DTcomp K) → Fin compNodeWidth → K
  memNodeWidth : ℕ
  memNodeEncode :
    (MemoryTable.MState × MemoryTable.DTmem K) → Fin memNodeWidth → K
  requests : IOField K
  responses : IOField K
  outMem : IOField K

namespace AlphaMFamilyData

/-- The committed base.  Its walk placeholders carry no chronology claim; the final family below
sets all sampled coordinates definitionally. -/
def base
    {T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {z : K} {hz : z ≠ 0} {alphaM lmb : K}
    (D : AlphaMFamilyData T z hz alphaM lmb) : RawPlusIOSegmentedFamily F K where
  problem := specializedProblem T z hz alphaM lmb
  computeWalkAlpha := 0
  memoryWalkAlpha := alphaM
  walkGamma := 0
  compNodeWidth := D.compNodeWidth
  compNodeEncode := D.compNodeEncode
  memNodeWidth := D.memNodeWidth
  memNodeEncode := D.memNodeEncode
  requests := D.requests
  responses := D.responses
  outMem := D.outMem

/-- Insert the two coins which were unavailable at the `(z, alphaM)` phase. -/
def atCoins
    {T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {z : K} {hz : z ≠ 0} {alphaM lmb : K}
    (D : AlphaMFamilyData T z hz alphaM lmb) (alphaC gamma : K) :
    RawPlusIOSegmentedFamily F K where
  problem := specializedProblem T z hz alphaM lmb
  computeWalkAlpha := alphaC
  memoryWalkAlpha := alphaM
  walkGamma := gamma
  compNodeWidth := D.compNodeWidth
  compNodeEncode := D.compNodeEncode
  memNodeWidth := D.memNodeWidth
  memNodeEncode := D.memNodeEncode
  requests := D.requests
  responses := D.responses
  outMem := D.outMem

@[simp] theorem atCoins_tableAlpha
    {T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {z : K} {hz : z ≠ 0} {alphaM lmb : K}
    (D : AlphaMFamilyData T z hz alphaM lmb) (alphaC gamma : K) :
    (D.atCoins alphaC gamma).cfg.challenges.α = alphaM :=
  rfl

@[simp] theorem atCoins_computeWalkAlpha
    {T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {z : K} {hz : z ≠ 0} {alphaM lmb : K}
    (D : AlphaMFamilyData T z hz alphaM lmb) (alphaC gamma : K) :
    (D.atCoins alphaC gamma).computeWalkAlpha = alphaC :=
  rfl

@[simp] theorem atCoins_memoryWalkAlpha
    {T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {z : K} {hz : z ≠ 0} {alphaM lmb : K}
    (D : AlphaMFamilyData T z hz alphaM lmb) (alphaC gamma : K) :
    (D.atCoins alphaC gamma).memoryWalkAlpha = alphaM :=
  rfl

@[simp] theorem atCoins_walkGamma
    {T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {z : K} {hz : z ≠ 0} {alphaM lmb : K}
    (D : AlphaMFamilyData T z hz alphaM lmb) (alphaC gamma : K) :
    (D.atCoins alphaC gamma).walkGamma = gamma :=
  rfl

/-- Same `(z, alphaM)` means the complete problem and all non-walk family payloads are identical,
even when both later coins differ. -/
theorem nonSplicing
    {T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {z : K} {hz : z ≠ 0} {alphaM lmb : K}
    (D : AlphaMFamilyData T z hz alphaM lmb)
    (alphaC₁ gamma₁ alphaC₂ gamma₂ : K) :
    (D.atCoins alphaC₁ gamma₁).problem = (D.atCoins alphaC₂ gamma₂).problem ∧
      (D.atCoins alphaC₁ gamma₁).compNodeWidth =
        (D.atCoins alphaC₂ gamma₂).compNodeWidth ∧
      (D.atCoins alphaC₁ gamma₁).compNodeEncode =
        (D.atCoins alphaC₂ gamma₂).compNodeEncode ∧
      (D.atCoins alphaC₁ gamma₁).memNodeWidth =
        (D.atCoins alphaC₂ gamma₂).memNodeWidth ∧
      (D.atCoins alphaC₁ gamma₁).memNodeEncode =
        (D.atCoins alphaC₂ gamma₂).memNodeEncode ∧
      (D.atCoins alphaC₁ gamma₁).requests =
        (D.atCoins alphaC₂ gamma₂).requests ∧
      (D.atCoins alphaC₁ gamma₁).responses =
        (D.atCoins alphaC₂ gamma₂).responses ∧
      (D.atCoins alphaC₁ gamma₁).outMem =
        (D.atCoins alphaC₂ gamma₂).outMem :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end AlphaMFamilyData

/-- Complete data committed after `(z, alphaM)`.  The dependent table and IO arrays are indexed by
the base built above, so they cannot mention `alphaC` or `gamma`. -/
structure AlphaMCommitment
    (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) (alphaM lmb : K) where
  familyData : AlphaMFamilyData T z hz alphaM lmb
  tables : RawTableArrays familyData.base
  io : RawIOArrays familyData.base p

namespace AlphaMCommitment

/-- Transport table arrays to a final family.  Only walk parameters changed. -/
def tablesAt
    {T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {z : K} {hz : z ≠ 0} {alphaM lmb : K}
    (C : AlphaMCommitment (p := p) T z hz alphaM lmb)
    (alphaC gamma : K) : RawTableArrays (C.familyData.atCoins alphaC gamma) where
  compute := C.tables.compute
  memory := C.tables.memory

/-- Transport IO arrays to a final family.  Its problem, execution, and endpoints are unchanged. -/
def ioAt
    {T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {z : K} {hz : z ≠ 0} {alphaM lmb : K}
    (C : AlphaMCommitment (p := p) T z hz alphaM lmb)
    (alphaC gamma : K) : RawIOArrays (C.familyData.atCoins alphaC gamma) p where
  multiplicity := C.io.multiplicity
  progAcc := C.io.progAcc
  memAcc := C.io.memAcc

theorem sameAlphaM_tables
    {T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {z : K} {hz : z ≠ 0} {alphaM lmb : K}
    (C : AlphaMCommitment (p := p) T z hz alphaM lmb)
    (alphaC₁ gamma₁ alphaC₂ gamma₂ : K) :
    (C.tablesAt alphaC₁ gamma₁).compute = (C.tablesAt alphaC₂ gamma₂).compute ∧
      (C.tablesAt alphaC₁ gamma₁).memory = (C.tablesAt alphaC₂ gamma₂).memory :=
  ⟨rfl, rfl⟩

theorem sameAlphaM_io
    {T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {z : K} {hz : z ≠ 0} {alphaM lmb : K}
    (C : AlphaMCommitment (p := p) T z hz alphaM lmb)
    (alphaC₁ gamma₁ alphaC₂ gamma₂ : K) :
    (C.ioAt alphaC₁ gamma₁).multiplicity = (C.ioAt alphaC₂ gamma₂).multiplicity ∧
      (C.ioAt alphaC₁ gamma₁).progAcc = (C.ioAt alphaC₂ gamma₂).progAcc ∧
      (C.ioAt alphaC₁ gamma₁).memAcc = (C.ioAt alphaC₂ gamma₂).memAcc :=
  ⟨rfl, rfl, rfl⟩

end AlphaMCommitment

/-! ## Production strategy and raw acceptance -/

/-- Production raw strategy.  `timestamp.claim` fixes the public claim before `z`;
`timestamp.afterSeed` fixes only raw config/execution templates and the seed equation;
`afterAlphaM` has exactly the API `(z, hz, alphaM)`; `afterCoins` returns only walks. -/
structure Strategy (F K : Type) [Field F] [Field K] [Algebra F K]
    (p : ℕ) [CharP K p] where
  timestamp : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)
  afterAlphaM :
    ∀ (z : K) (hz : z ≠ 0) (alphaM lmb : K),
      AlphaMCommitment (p := p) timestamp z hz alphaM lmb
  afterCoins :
    ∀ (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0), RawWalkArrays K

namespace Strategy

def claim (T : Strategy F K p) : P8PublicClaim :=
  T.timestamp.claim

def alphaMCommitment (T : Strategy F K p)
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    AlphaMCommitment (p := p) T.timestamp (nprSeed ω) hz (alphaM ω) lmb :=
  T.afterAlphaM (nprSeed ω) hz (alphaM ω) lmb

def familyAt (T : Strategy F K p)
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    RawPlusIOSegmentedFamily F K :=
  (T.alphaMCommitment ω lmb hz).familyData.atCoins (alphaC ω) (gamma ω)

def messageAt (T : Strategy F K p)
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    RawMessage (T.familyAt ω lmb hz) p where
  tables := (T.alphaMCommitment ω lmb hz).tablesAt (alphaC ω) (gamma ω)
  walks := T.afterCoins ω lmb hz
  io := (T.alphaMCommitment ω lmb hz).ioAt (alphaC ω) (gamma ω)

/-- Acceptance is exactly raw gates plus six raw RAP evaluations; zero seed rejects. -/
def Accepts (T : Strategy F K p) (ω : JointCoins K) (lmb : K) : Prop :=
  if hz : nprSeed ω ≠ 0 then
    RawAccepts T.claim (T.familyAt ω lmb hz) ω (T.messageAt ω lmb hz)
  else False

theorem accepts_iff_raw
    (T : Strategy F K p) (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    T.Accepts ω lmb ↔
      RawAccepts T.claim (T.familyAt ω lmb hz) ω (T.messageAt ω lmb hz) := by
  simp [Accepts, hz]

theorem accepts_iff_gates_and_sixRAP
    (T : Strategy F K p) (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    T.Accepts ω lmb ↔
      (T.messageAt ω lmb hz).VerifierGates T.claim ω ∧
        (T.messageAt ω lmb hz).SixRAPSatisfy := by
  simp only [Accepts, dif_pos hz, RawAccepts_iff_sixRAP_and_gates]

/-- Fully expanded raw acceptance over the six named segmented families. -/
theorem accepts_iff_six_families
    (T : Strategy F K p) (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    T.Accepts ω lmb ↔
      (T.messageAt ω lmb hz).VerifierGates T.claim ω ∧
      (∀ kind, ((T.familyAt ω lmb hz).computeTableRAP kind).Satisfies
        (T.messageAt ω lmb hz).computeTableTrace) ∧
      (∀ kind, ((T.familyAt ω lmb hz).memoryTableRAP kind).Satisfies
        (T.messageAt ω lmb hz).memoryTableTrace) ∧
      (∀ kind, ((T.familyAt ω lmb hz).computeWalkRAP kind).Satisfies
        (T.messageAt ω lmb hz).computeWalkTrace) ∧
      (∀ kind, ((T.familyAt ω lmb hz).memoryWalkRAP kind).Satisfies
        (T.messageAt ω lmb hz).memoryWalkTrace) ∧
      (∀ kind, ((T.familyAt ω lmb hz).computeIORAP kind).Satisfies
        (T.messageAt ω lmb hz).computeIOTrace) ∧
      (∀ kind, ((T.familyAt ω lmb hz).memoryIORAP kind).Satisfies
        (T.messageAt ω lmb hz).memoryIOTrace) := by
  rw [T.accepts_iff_gates_and_sixRAP ω lmb hz]
  rfl

/-- The sampled family's memory rows all carry its configuration's `λ` (= the sampled `λ`). -/
theorem familyAt_memoryLambda
    (T : Strategy F K p) (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (i : Fin (T.familyAt ω lmb hz).cfg.memRows) :
    ((T.familyAt ω lmb hz).exec.memoryPubAt i).lambda =
      (T.familyAt ω lmb hz).cfg.challenges.lam :=
  specializedProblem_memoryLambda T.timestamp (nprSeed ω) hz (alphaM ω) lmb i

/-- Every sampled coordinate, including the table diagonal, is definitional. -/
theorem sampledCoordinates
    (T : Strategy F K p) (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    (T.familyAt ω lmb hz).cfg.challenges.z = nprSeed ω ∧
      (T.familyAt ω lmb hz).cfg.challenges.α = alphaM ω ∧
      (T.familyAt ω lmb hz).cfg.challenges.lam = lmb ∧
      (T.familyAt ω lmb hz).computeWalkAlpha = alphaC ω ∧
      (T.familyAt ω lmb hz).memoryWalkAlpha = alphaM ω ∧
      (T.familyAt ω lmb hz).walkGamma = gamma ω := by
  exact ⟨specializedProblem_seed _ _ _ _ _, rfl, rfl, rfl, rfl, rfl⟩

/-- Template specialization puts the configured per-root boundary directly at sampled `alphaM`.
No `RawSampledAxisBoundaryResidual` is needed. -/
theorem sampledAxisBoundary
    (T : Strategy F K p) (z : K) (hz : z ≠ 0) (alphaM lmb : K)
    (R : ExactAxisRefinement
      (specializedProblem T.timestamp z hz alphaM lmb).cfg
      (specializedProblem T.timestamp z hz alphaM lmb).exec) :
    ∀ i : Fin (specializedProblem T.timestamp z hz alphaM lmb).cfg.kMem,
      (Nock.AxisBatching.MTree.countsP
        (exactAxisTree
          (specializedProblem T.timestamp z hz alphaM lmb).cfg
          (specializedProblem T.timestamp z hz alphaM lmb).exec i)).eval alphaM = 0 := by
  intro i
  simpa using R.root_accepts i

/-! ## Forward raw-verifier soundness -/

/-- Consequences of raw acceptance.  No well-formedness, RVT, evaluator, or target premise occurs
in this bundle. -/
structure ForwardSoundnessAt
    (T : Strategy F K p) (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) : Prop where
  computeTable :
    (∀ i, ComputeTable.Vcomp
      (T.familyAt ω lmb hz).cfg.challenges.computeInputs
      ((T.familyAt ω lmb hz).exec.computePubAt i)
      ((T.familyAt ω lmb hz).exec.computeDecAt i)) ∧
    (∀ i : Fin (T.familyAt ω lmb hz).cfg.compRows,
      ∀ hi : (i : ℕ) + 1 < (T.familyAt ω lmb hz).cfg.compRows,
      ((T.familyAt ω lmb hz).exec.computePubAt i).ln =
        ((T.familyAt ω lmb hz).exec.computePubAt ⟨(i : ℕ) + 1, hi⟩).ln_prev)
  memoryTable :
    (∀ i, MemoryTable.Vmem
      (T.familyAt ω lmb hz).cfg.challenges.memoryInputs
      ((T.familyAt ω lmb hz).exec.memoryPubAt i)) ∧
    (∀ i : Fin (T.familyAt ω lmb hz).cfg.memRows,
      ∀ hi : (i : ℕ) + 1 < (T.familyAt ω lmb hz).cfg.memRows,
      ((T.familyAt ω lmb hz).exec.memoryPubAt i).icur =
        ((T.familyAt ω lmb hz).exec.memoryPubAt ⟨(i : ℕ) + 1, hi⟩).ipre) ∧
    ((T.familyAt ω lmb hz).exec.memoryPubAt
      ⟨0, (T.familyAt ω lmb hz).cfg.memRows_pos⟩).pt.counts = 0 ∧
    ((T.familyAt ω lmb hz).exec.memoryPubAt
      ⟨0, (T.familyAt ω lmb hz).cfg.memRows_pos⟩).pt.indicator = 0 ∧
    ((T.familyAt ω lmb hz).exec.memoryPubAt
      ⟨0, (T.familyAt ω lmb hz).cfg.memRows_pos⟩).ipre = 0 ∧
    ((T.familyAt ω lmb hz).exec.memoryPubAt
      ((T.familyAt ω lmb hz).cfg.orbit.lastIndex
        (T.familyAt ω lmb hz).cfg.memRows
        (T.familyAt ω lmb hz).cfg.memRows_pos)).icur = 0
  seedNonzero : (T.familyAt ω lmb hz).cfg.challenges.z ≠ 0
  computeWalk : (T.messageAt ω lmb hz).ComputeWalkCertificate
  memoryWalk : (T.messageAt ω lmb hz).MemoryWalkCertificate
  exactIO :
    IO.LIO (T.familyAt ω lmb hz).cfg.Ksz
      (T.familyAt ω lmb hz).exec.derivedRequestIO
      (T.familyAt ω lmb hz).exec.derivedResponseIO

/-- Forward soundness is inherited directly from the raw verifier.  The only external conditions
are the field tag characteristic, characteristic capacity, and the two IO trace capacities. -/
theorem forwardSoundness_of_accepts
    (T : Strategy F K p) (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (hchar : NodeEncoding.StateTagChar K)
    (hKp : (T.familyAt ω lmb hz).cfg.Ksz < p)
    (hProgCap :
      (T.familyAt ω lmb hz).exec.derivedRequestIO.length + 1 ≤
        2 ^ (T.familyAt ω lmb hz).cfg.orbit.h)
    (hMemCap :
      (T.familyAt ω lmb hz).exec.derivedResponseIO.length + 1 ≤
        2 ^ (T.familyAt ω lmb hz).cfg.orbit.h)
    (hlam : ∀ i, ((T.familyAt ω lmb hz).exec.memoryPubAt i).lambda = (T.familyAt ω lmb hz).cfg.challenges.lam)
    (haccept : T.Accepts ω lmb) :
    T.ForwardSoundnessAt ω lmb hz := by
  let M := T.messageAt ω lmb hz
  have hraw : RawAccepts T.claim (T.familyAt ω lmb hz) ω M :=
    (T.accepts_iff_raw ω lmb hz).1 haccept
  have hsix : M.SixRAPSatisfy := hraw.2
  have hcomp := M.computeTable_sound_wfFree hchar hsix.1
  have hmem := M.memoryTable_sound_wfFree hchar hlam hsix.2.1
  exact
    { computeTable := hcomp.1
      memoryTable := hmem.1
      seedNonzero := hcomp.2
      computeWalk := (M.computeWalkRAP_wholeTrace_iff).1 hsix.2.2.1
      memoryWalk := (M.memoryWalkRAP_wholeTrace_iff).1 hsix.2.2.2.1
      exactIO := M.lio_of_accepts hKp hProgCap hMemCap hraw }

/-- Optional production topology gate.  It is still a raw equality check over committed data and
adds no proof-carrying topology field to the message. -/
def AcceptsWithTopology
    (T : Strategy F K p) (ω : JointCoins K) (lmb : K) : Prop :=
  if hz : nprSeed ω ≠ 0 then
    RawAccepts T.claim (T.familyAt ω lmb hz) ω (T.messageAt ω lmb hz) ∧
      TopologyCompressedCheck (T.familyAt ω lmb hz) (gamma ω)
  else False

theorem acceptsWithTopology_iff_raw_checks
    (T : Strategy F K p) (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    T.AcceptsWithTopology ω lmb ↔
      (T.messageAt ω lmb hz).VerifierGates T.claim ω ∧
      (T.messageAt ω lmb hz).SixRAPSatisfy ∧
      TopologyCompressedCheck (T.familyAt ω lmb hz) (gamma ω) := by
  simp only [AcceptsWithTopology, dif_pos hz, RawAccepts_iff_sixRAP_and_gates]
  tauto

end Strategy

/-! ## One fixed pre-seed NPR census -/

/-- Occurrence-preserving pair list from an explicit proof-side semantic skeleton and the raw
pre-seed public claim.  The skeleton is not a field of `Strategy`. -/
def preSeedPairs (T : Strategy F K p) (S : SemanticStrategy.SemanticSkeleton) :
    List (Noun × Noun) :=
  [(S.computeTree.label.subject, T.claim.subject),
    (S.computeTree.label.formula, T.claim.formula),
    (S.computeTree.label.evaluation, T.claim.result)] ++
    (P8Census.skeletonComparisonCensus (K := K) S).map SemanticTrace.ComparisonUse.pair

/-- The sole input needed to turn the fixed pair list into a `ComparisonCensus`. -/
structure PreSeedCensus
    (T : Strategy F K p) (S : SemanticStrategy.SemanticSkeleton) (Λ : ℕ) : Prop where
  leaves_bounded :
    ∀ pair ∈ preSeedPairs T S, pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ

namespace PreSeedCensus

def census {T : Strategy F K p} {S : SemanticStrategy.SemanticSkeleton} {Λ : ℕ}
    (C : PreSeedCensus T S Λ) :
    ComparisonCensus Λ :=
  ComparisonCensus.ofPairList (preSeedPairs T S) C.leaves_bounded

@[simp] theorem census_count
    {T : Strategy F K p} {S : SemanticStrategy.SemanticSkeleton} {Λ : ℕ}
    (C : PreSeedCensus T S Λ) :
    C.census.count = (preSeedPairs T S).length :=
  rfl

theorem census_count_exact
    {T : Strategy F K p} {S : SemanticStrategy.SemanticSkeleton} {Λ : ℕ}
    (C : PreSeedCensus T S Λ) :
    C.census.count =
      3 + (P8Census.skeletonComparisonCensus (K := K) S).length := by
  simp [census, preSeedPairs]
  omega

end PreSeedCensus

/-! ## Regenerated `alphaM`-label counting -/

section Finite

variable [Fintype K] [DecidableEq K]

/-- A strategy-wide family of the exact obligations caused by specializing all memory labels at
the same `alphaM` later used by the memory walk.  `fails z hz alphaM` (at the sampled `λ` the data is indexed by) should be instantiated with
the desired fixed-seed memory-walk failure predicate (with any remaining `gamma` quantified in the
predicate). -/
structure RegeneratedMemoryCountingData
    (T : Strategy F K p) (hchar : NodeEncoding.StateTagChar K) (lmb : K) where
  fails : ∀ z : K, z ≠ 0 → K → Prop
  receipt :
    ∀ (z : K) (hz : z ≠ 0),
      RegeneratedMemoryLabelCountingObligation
        (T.timestamp.afterSeed ⟨z, hz⟩).executionTemplate hchar lmb (fails z hz)

namespace RegeneratedMemoryCountingData

def seedPairs
    {T : Strategy F K p} {hchar : NodeEncoding.StateTagChar K} {lmb : K}
    (D : RegeneratedMemoryCountingData T hchar lmb) : Finset (K × K) :=
  fiberEvent (validSeeds K) fun z =>
    if hz : z ≠ 0 then (D.receipt z hz).badAlphas else ∅

/-- Exact JointCoins contribution.  `alphaC` and `gamma` are unrestricted because the polynomial
receipt has already quantified whatever remains in `fails`; only `(z, alphaM)` is restricted. -/
def failureEvent
    {T : Strategy F K p} {hchar : NodeEncoding.StateTagChar K} {lmb : K}
    (D : RegeneratedMemoryCountingData T hchar lmb) : Finset (JointCoins K) :=
  liftAxisSeedFibers D.seedPairs

@[simp] theorem mem_failureEvent_iff
    {T : Strategy F K p} {hchar : NodeEncoding.StateTagChar K} {lmb : K}
    (D : RegeneratedMemoryCountingData T hchar lmb) (ω : JointCoins K) :
    ω ∈ D.failureEvent ↔
      ∃ hz : nprSeed ω ≠ 0,
        alphaM ω ∈ (D.receipt (nprSeed ω) hz).badAlphas := by
  rw [failureEvent, mem_liftAxisSeedFibers_iff, seedPairs,
    mem_fiberEvent_iff, mem_validSeeds]
  constructor
  · rintro ⟨hz, hmem⟩
    exact ⟨hz, by simpa only [dif_pos hz] using hmem⟩
  · rintro ⟨hz, hmem⟩
    exact ⟨hz, by simpa only [dif_pos hz] using hmem⟩

/-- The receipt's failure predicate is covered by the exact joint event. -/
theorem failure_mem_event
    {T : Strategy F K p} {hchar : NodeEncoding.StateTagChar K} {lmb : K}
    (D : RegeneratedMemoryCountingData T hchar lmb)
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (hfail : D.fails (nprSeed ω) hz (alphaM ω)) :
    ω ∈ D.failureEvent :=
  (D.mem_failureEvent_iff ω).2
    ⟨hz, (D.receipt (nprSeed ω) hz).failure_mem_badAlphas _ hfail⟩

/-- Exact regenerated-memory contribution: a uniform composed degree `d` contributes
`d * |K|^3` on the four-coordinate joint space. -/
theorem failureEvent_card_le
    {T : Strategy F K p} {hchar : NodeEncoding.StateTagChar K} {lmb : K}
    (D : RegeneratedMemoryCountingData T hchar lmb) (workload : ℕ)
    (hwork : ∀ z (hz : z ≠ 0),
      (D.receipt z hz).composedDegreeBound ≤ workload) :
    D.failureEvent.card ≤ workload * Fintype.card K ^ 3 := by
  rw [failureEvent, card_liftAxisSeedFibers]
  have hpairs : D.seedPairs.card ≤ (Fintype.card K - 1) * workload := by
    unfold seedPairs
    simpa only [validSeeds_card] using
      (fiberEvent_card_le (validSeeds K)
        (fun z => if hz : z ≠ 0 then (D.receipt z hz).badAlphas else ∅)
        workload (by
          intro z hzmem
          have hz : z ≠ 0 := (mem_validSeeds z).1 hzmem
          simp only [dif_pos hz]
          exact (D.receipt z hz).badAlphas_card.trans (hwork z hz)))
  calc
    D.seedPairs.card * Fintype.card K ^ 2
        ≤ ((Fintype.card K - 1) * workload) * Fintype.card K ^ 2 :=
      Nat.mul_le_mul_right _ hpairs
    _ ≤ (Fintype.card K * workload) * Fintype.card K ^ 2 := by
      exact Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right workload (Nat.sub_le (Fintype.card K) 1))
    _ = workload * Fintype.card K ^ 3 := by ring

end RegeneratedMemoryCountingData

/-! ## Fixed-after-`alphaM` topology counting -/

/-- Fix `(z, alphaM)` and a bad-`gamma` set, leaving only `alphaC` unrestricted. -/
def fixedZAlphaMGammaEvent (z alphaMValue : K) (badGamma : Finset K) :
    Finset (JointCoins K) :=
  ((Finset.univ : Finset K) ×ˢ badGamma) ×ˢ
    (({alphaMValue} : Finset K) ×ˢ ({z} : Finset K))

@[simp] theorem mem_fixedZAlphaMGammaEvent_iff
    (z alphaMValue : K) (badGamma : Finset K) (ω : JointCoins K) :
    ω ∈ fixedZAlphaMGammaEvent z alphaMValue badGamma ↔
      nprSeed ω = z ∧ alphaM ω = alphaMValue ∧ gamma ω ∈ badGamma := by
  rcases ω with ⟨⟨alphaC, gamma⟩, ⟨alphaM', z'⟩⟩
  simp [fixedZAlphaMGammaEvent, nprSeed, Thm54.alphaM, Thm54.gamma, eq_comm]
  aesop

theorem card_fixedZAlphaMGammaEvent
    (z alphaM : K) (badGamma : Finset K) :
    (fixedZAlphaMGammaEvent z alphaM badGamma).card =
      badGamma.card * Fintype.card K := by
  simp [fixedZAlphaMGammaEvent]
  ring

/-- Honest topology event fibered over both pieces of already-committed data. -/
def specializedTopologyFailureEvent (T : Strategy F K p) (lmb : K) :
    Finset (JointCoins K) :=
  (Finset.univ : Finset (K × K)).biUnion fun za =>
    if hz : za.1 ≠ 0 then
      fixedZAlphaMGammaEvent za.1 za.2
        (topologyBadGammas
          (T.afterAlphaM za.1 hz za.2 lmb).familyData.base)
    else ∅

@[simp] theorem mem_specializedTopologyFailureEvent_iff
    (T : Strategy F K p) (lmb : K) (ω : JointCoins K) :
    ω ∈ specializedTopologyFailureEvent T lmb ↔
      ∃ hz : nprSeed ω ≠ 0,
        gamma ω ∈ topologyBadGammas
          (T.afterAlphaM (nprSeed ω) hz (alphaM ω) lmb).familyData.base := by
  constructor
  · intro h
    rw [specializedTopologyFailureEvent] at h
    obtain ⟨za, _, hza⟩ := Finset.mem_biUnion.mp h
    split at hza
    · rename_i hz
      have hm := (mem_fixedZAlphaMGammaEvent_iff za.1 za.2 _ ω).1 hza
      rcases za with ⟨z, alphaMValue⟩
      rcases hm with ⟨hseed, halpha, hbad⟩
      dsimp at hz hseed halpha hbad ⊢
      subst z
      subst alphaMValue
      refine ⟨hz, ?_⟩
      simpa only [proof_irrel_heq] using hbad
    · simp at hza
  · rintro ⟨hz, hbad⟩
    rw [specializedTopologyFailureEvent]
    apply Finset.mem_biUnion.mpr
    refine ⟨(nprSeed ω, alphaM ω), Finset.mem_univ _, ?_⟩
    rw [dif_pos hz]
    exact (mem_fixedZAlphaMGammaEvent_iff _ _ _ _).2 ⟨rfl, rfl, hbad⟩

theorem specializedTopologyFailureEvent_card_le
    (T : Strategy F K p) (lmb : K) (workload : ℕ)
    (hwork : ∀ z (hz : z ≠ 0) alphaM,
      topologyWorkload (T.afterAlphaM z hz alphaM lmb).familyData.base ≤ workload) :
    (specializedTopologyFailureEvent T lmb).card ≤
      workload * Fintype.card K ^ 3 := by
  calc
    (specializedTopologyFailureEvent T lmb).card ≤
        ∑ za : K × K,
          (if hz : za.1 ≠ 0 then
            fixedZAlphaMGammaEvent za.1 za.2
              (topologyBadGammas
                (T.afterAlphaM za.1 hz za.2 lmb).familyData.base)
          else ∅).card := by
      unfold specializedTopologyFailureEvent
      exact Finset.card_biUnion_le
    _ ≤ ∑ _za : K × K, workload * Fintype.card K := by
      apply Finset.sum_le_sum
      intro za _
      split
      · rename_i hz
        rw [card_fixedZAlphaMGammaEvent]
        exact Nat.mul_le_mul_right _
          ((topologyBadGammas_card_le
            (T.afterAlphaM za.1 hz za.2 lmb).familyData.base).trans
              (hwork za.1 hz za.2))
      · simp
    _ = workload * Fintype.card K ^ 3 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        nsmul_eq_mul]
      simp [pow_succ]
      ring

/-- Topology soundness from the optional raw compressed check, outside its counted event. -/
theorem Strategy.exactTopology_of_acceptsWithTopology
    (T : Strategy F K p) (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (hchar : NodeEncoding.StateTagChar K)
    (hlam : ∀ i, ((T.familyAt ω lmb hz).exec.memoryPubAt i).lambda = (T.familyAt ω lmb hz).cfg.challenges.lam)
    (haccept : T.AcceptsWithTopology ω lmb)
    (hout : ω ∉ specializedTopologyFailureEvent T lmb) :
    ComputeExactTopology (T.familyAt ω lmb hz).exec ∧
      MemoryExactTopology (T.familyAt ω lmb hz).exec := by
  have hparts :
      RawAccepts T.claim (T.familyAt ω lmb hz) ω (T.messageAt ω lmb hz) ∧
        TopologyCompressedCheck (T.familyAt ω lmb hz) (gamma ω) := by
    simpa [Strategy.AcceptsWithTopology, hz] using haccept
  apply (T.messageAt ω lmb hz).exactTopology_of_accepts_and_compressedCheck
    hchar hlam hparts.1 hparts.2
  intro hbad
  apply hout
  apply (mem_specializedTopologyFailureEvent_iff T lmb ω).2
  refine ⟨hz, ?_⟩
  change gamma ω ∈ topologyBadGammas
    (T.afterAlphaM (nprSeed ω) hz (alphaM ω) lmb).familyData.base at hbad
  exact hbad

/-! ## Specialized axis event and semantic target -/

/-- Exact self-specialized axis event.  Unlike the old seed-fixed event, both the problem and the
evaluation point use the same sampled `alphaM`. -/
def specializedAxisFailureEvent (T : Strategy F K p) (lmb : K) :
    Finset (JointCoins K) :=
  Finset.univ.filter fun ω =>
    if hz : nprSeed ω ≠ 0 then
      alphaM ω ∈ axisBadAlphas
        (specializedProblem T.timestamp (nprSeed ω) hz (alphaM ω) lmb).cfg
        (specializedExecA T.timestamp (nprSeed ω) hz (alphaM ω) lmb)
    else False

@[simp] theorem mem_specializedAxisFailureEvent_iff
    (T : Strategy F K p) (lmb : K) (ω : JointCoins K) :
    ω ∈ specializedAxisFailureEvent T lmb ↔
      ∃ hz : nprSeed ω ≠ 0,
        alphaM ω ∈ axisBadAlphas
          (specializedProblem T.timestamp (nprSeed ω) hz (alphaM ω) lmb).cfg
          (specializedExecA T.timestamp (nprSeed ω) hz (alphaM ω) lmb) := by
  simp only [specializedAxisFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  split
  · rename_i hz
    constructor
    · intro h
      exact ⟨hz, h⟩
    · rintro ⟨hz', h⟩
      simpa only [proof_irrel_heq] using h
  · rename_i hz
    constructor
    · intro h
      contradiction
    · rintro ⟨hz', _⟩
      exact (hz hz').elim

/-- Field target on the exact `(z, alphaM)` specialization. -/
def Strategy.FieldTargetAt (T : Strategy F K p) (q : ℕ)
    (ω : JointCoins K) (lmb : K) : Prop :=
  if hz : nprSeed ω ≠ 0 then
    let problem := specializedProblem T.timestamp (nprSeed ω) hz (alphaM ω) lmb
    (∃ Λ : ℕ,
      Nonempty (SemanticTrace.ExactExecutionSemanticData q Λ
        problem.cfg problem.exec)) ∧
      ExactMemoryAxisSemantics problem.cfg
        (specializedExecA T.timestamp (nprSeed ω) hz (alphaM ω) lmb)
  else False

def Strategy.GenuineTargetAt (T : Strategy F K p) (q : ℕ)
    (ω : JointCoins K) (lmb : K) : Prop :=
  T.FieldTargetAt q ω lmb ∧ T.claim.Holds

/-- Production false acceptance uses the raw topology equality check in addition to `RawAccepts`.
Neither target is stored in prover data. -/
def Strategy.FalseAcceptanceSet (T : Strategy F K p) (q : ℕ) (lmb : K) :
    Finset (JointCoins K) :=
  Finset.univ.filter fun ω =>
    T.AcceptsWithTopology ω lmb ∧ ¬ T.GenuineTargetAt q ω lmb

@[simp] theorem Strategy.mem_FalseAcceptanceSet_iff
    (T : Strategy F K p) (q : ℕ) (ω : JointCoins K) :
    ω ∈ T.FalseAcceptanceSet q lmb ↔
      T.AcceptsWithTopology ω lmb ∧ ¬ T.GenuineTargetAt q ω lmb := by
  simp [Strategy.FalseAcceptanceSet]

/-- Exact remaining axis-counting obligation.  The ordinary fixed-polynomial theorem cannot be
silently applied because `exactAxisTree` is itself formed from the `alphaM`-specialized carrier. -/
def SpecializedAxisCountingResidual
    (T : Strategy F K p) (lmb : K) (workload : ℕ) : Prop :=
  (specializedAxisFailureEvent T lmb).card ≤ workload * Fintype.card K ^ 3

/-- Exact remaining compute-walk counting obligation after choosing the concrete event.  Per fixed
`(z, alphaM)` the committed payload is independent of `(alphaC, gamma)` by
`AlphaMFamilyData.nonSplicing`; this residual is only the global event/cardinality assembly. -/
def SpecializedComputeWalkCountingResidual
    (event : Finset (JointCoins K)) (workload : ℕ) : Prop :=
  event.card ≤ workload * Fintype.card K ^ 3

/-- Direct sampled-axis containment.  The diagonal premise required by the generic axis theorem is
definitionally `rfl` here. -/
theorem specializedAxisFailure_of_refinement
    (T : Strategy F K p) (q : ℕ) (ω : JointCoins K) (lmb : K)
    (hz : nprSeed ω ≠ 0)
    (R : ExactAxisRefinement
      (specializedProblem T.timestamp (nprSeed ω) hz (alphaM ω) lmb).cfg
      (specializedExecA T.timestamp (nprSeed ω) hz (alphaM ω) lmb))
    (haccept : T.AcceptsWithTopology ω lmb)
    (hsemantic :
      ∃ Λ : ℕ, Nonempty (SemanticTrace.ExactExecutionSemanticData q Λ
        (specializedProblem T.timestamp (nprSeed ω) hz (alphaM ω) lmb).cfg
        (specializedProblem T.timestamp (nprSeed ω) hz (alphaM ω) lmb).exec))
    (hnotField : ¬ T.FieldTargetAt q ω lmb) :
    ω ∈ specializedAxisFailureEvent T lmb := by
  apply (mem_specializedAxisFailureEvent_iff T lmb ω).2
  refine ⟨hz, ?_⟩
  rw [← mem_AxisFailureSet_iff]
  apply exactAxisRefinement_P8AxisContainment
    (fun ω => T.AcceptsWithTopology ω lmb)
    (∃ Λ : ℕ, Nonempty (SemanticTrace.ExactExecutionSemanticData q Λ
      (specializedProblem T.timestamp (nprSeed ω) hz (alphaM ω) lmb).cfg
      (specializedProblem T.timestamp (nprSeed ω) hz (alphaM ω) lmb).exec))
    (specializedProblem T.timestamp (nprSeed ω) hz (alphaM ω) lmb).cfg
    (specializedExecA T.timestamp (nprSeed ω) hz (alphaM ω) lmb) R
    ω haccept rfl hsemantic
  intro htarget
  apply hnotField
  simpa [Strategy.FieldTargetAt, hz, AxisCumulativeFieldExecutionTarget,
    proof_irrel_heq] using htarget

/-! ## Aggregate exact event and residual containment -/

def ProductionFailureUnion
    (T : Strategy F K p) (lmb : K) (C : ComparisonCensus Λ)
    {hchar : NodeEncoding.StateTagChar K}
    (D : RegeneratedMemoryCountingData T hchar lmb)
    (computeEvent : Finset (JointCoins K)) : Finset (JointCoins K) :=
  (((((zeroSeedFailureEvent ∪ collisionFailureEvent C) ∪
      D.failureEvent) ∪ specializedTopologyFailureEvent T lmb) ∪
      specializedAxisFailureEvent T lmb) ∪ computeEvent)

def productionWorkload
    (collisionCount Λ regeneratedMemory topology axis compute : ℕ) : ℕ :=
  1 + collisionCount * (2 * Λ - 1) + regeneratedMemory + topology + axis + compute

/-- Exact residual: this proposition is exported but no theorem asserts it.  Table and IO events
are absent because accepted table rows and exact `LIO` are deterministic consequences of
`RawAccepts`; adding probabilistic table/IO terms would be unsupported double counting. -/
def FalseAcceptanceContainmentResidual
    (T : Strategy F K p) (q : ℕ) (lmb : K) (C : ComparisonCensus Λ)
    {hchar : NodeEncoding.StateTagChar K}
    (D : RegeneratedMemoryCountingData T hchar lmb)
    (computeEvent : Finset (JointCoins K)) : Prop :=
  T.FalseAcceptanceSet q lmb ⊆ ProductionFailureUnion T lmb C D computeEvent

/-- Aggregate count from exactly the proved/explicit components.  The two premises named
`haxis` and `hcompute` are the remaining specialized cardinality residuals. -/
theorem productionFailureUnion_card_le
    (T : Strategy F K p) (lmb : K) (C : ComparisonCensus Λ)
    {hchar : NodeEncoding.StateTagChar K}
    (D : RegeneratedMemoryCountingData T hchar lmb)
    (computeEvent : Finset (JointCoins K))
    (memoryWorkload topologyWorkloadBound axisWorkload computeWorkload : ℕ)
    (hmemory : D.failureEvent.card ≤
      memoryWorkload * Fintype.card K ^ 3)
    (htopology : (specializedTopologyFailureEvent T lmb).card ≤
      topologyWorkloadBound * Fintype.card K ^ 3)
    (haxis : SpecializedAxisCountingResidual T lmb axisWorkload)
    (hcompute :
      SpecializedComputeWalkCountingResidual computeEvent computeWorkload) :
    (ProductionFailureUnion T lmb C D computeEvent).card ≤
      productionWorkload C.count Λ memoryWorkload topologyWorkloadBound
        axisWorkload computeWorkload * Fintype.card K ^ 3 := by
  let k3 := Fintype.card K ^ 3
  let Z : Finset (JointCoins K) := zeroSeedFailureEvent
  let N : Finset (JointCoins K) := collisionFailureEvent C
  let M := D.failureEvent
  let G := specializedTopologyFailureEvent T lmb
  let A := specializedAxisFailureEvent T lmb
  let W := computeEvent
  have hZ : Z.card ≤ 1 * k3 := by
    simp [Z, k3, zeroSeedFailureEvent_card]
  have hN : N.card ≤ (C.count * (2 * Λ - 1)) * k3 :=
    collisionFailureEvent_card_le C
  have hM : M.card ≤ memoryWorkload * k3 := hmemory
  have hG : G.card ≤ topologyWorkloadBound * k3 := htopology
  have hA : A.card ≤ axisWorkload * k3 := haxis
  have hW : W.card ≤ computeWorkload * k3 := hcompute
  calc
    (ProductionFailureUnion T lmb C D computeEvent).card
        ≤ Z.card + N.card + M.card + G.card + A.card + W.card := by
      simpa [ProductionFailureUnion, Z, N, M, G, A, W] using
        (calc
          (((((Z ∪ N) ∪ M) ∪ G) ∪ A) ∪ W).card
              ≤ ((((Z ∪ N) ∪ M) ∪ G) ∪ A).card + W.card :=
            Finset.card_union_le _ _
          _ ≤ (((Z ∪ N) ∪ M) ∪ G).card + A.card + W.card := by
            exact Nat.add_le_add_right (Finset.card_union_le _ _) _
          _ ≤ ((Z ∪ N) ∪ M).card + G.card + A.card + W.card := by
            exact Nat.add_le_add_right
              (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
          _ ≤ (Z ∪ N).card + M.card + G.card + A.card + W.card := by
            exact Nat.add_le_add_right
              (Nat.add_le_add_right
                (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _
          _ ≤ Z.card + N.card + M.card + G.card + A.card + W.card := by
            exact Nat.add_le_add_right
              (Nat.add_le_add_right
                (Nat.add_le_add_right
                  (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _) _)
    _ ≤ 1 * k3 + (C.count * (2 * Λ - 1)) * k3 +
        memoryWorkload * k3 + topologyWorkloadBound * k3 +
        axisWorkload * k3 + computeWorkload * k3 := by omega
    _ = productionWorkload C.count Λ memoryWorkload topologyWorkloadBound
        axisWorkload computeWorkload * Fintype.card K ^ 3 := by
      simp only [productionWorkload, k3]
      ring

/-- Cardinality-to-probability adapter.  The containment residual remains an explicit premise. -/
theorem falseAcceptance_jointProbability_le
    (T : Strategy F K p) (q : ℕ) (lmb : K) (workload : ℕ)
    (failure : Finset (JointCoins K))
    (hcontain : T.FalseAcceptanceSet q lmb ⊆ failure)
    (hfailure : failure.card ≤ workload * Fintype.card K ^ 3) :
    |jointProbability (T.FalseAcceptanceSet q lmb)| ≤
      (workload : ℝ) / (Fintype.card K : ℝ) := by
  apply jointProbability_le_workload_div_card
  exact (Finset.card_le_card hcontain).trans hfailure

end Finite


/-- Exact factorization required to reuse an existing `RawP8Strategy` without moving any payload
across phases.  The old strategy type does not provide these fields: its problem is fixed before
`alphaM`.  Consequently this is an honest residual interface, not an unconditional conversion. -/
structure LegacyPhaseFactorization
    (timestamp : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (L : RawP8Strategy F K p) where
  claim_eq : timestamp.claim = L.claim
  afterAlphaM :
    ∀ (z : K) (hz : z ≠ 0) (alphaM lmb : K),
      AlphaMCommitment (p := p) timestamp z hz alphaM lmb
  family_eq :
    ∀ (z : K) (hz : z ≠ 0) (alphaM lmb alphaC gamma : K),
      ((afterAlphaM z hz alphaM lmb).familyData.atCoins alphaC gamma) =
        (L.afterSeed z hz).atJointCoins ((alphaC, gamma), (alphaM, z))
  tables_eq :
    ∀ (z : K) (hz : z ≠ 0) (alphaM lmb alphaC gamma : K),
      HEq ((afterAlphaM z hz alphaM lmb).tablesAt alphaC gamma)
        ((L.afterSeed z hz).tablesAt ((alphaC, gamma), (alphaM, z)))
  io_eq :
    ∀ (z : K) (hz : z ≠ 0) (alphaM lmb alphaC gamma : K),
      HEq ((afterAlphaM z hz alphaM lmb).ioAt alphaC gamma)
        ((L.afterSeed z hz).ioAt ((alphaC, gamma), (alphaM, z)))

namespace LegacyPhaseFactorization

def toStrategy
    {timestamp : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {L : RawP8Strategy F K p}
    (P : LegacyPhaseFactorization (p := p) timestamp L) : Strategy F K p where
  timestamp := timestamp
  afterAlphaM := P.afterAlphaM
  afterCoins := fun ω _ hz => L.afterCoins ω hz

theorem familyAt_eq
    {timestamp : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {L : RawP8Strategy F K p}
    (P : LegacyPhaseFactorization (p := p) timestamp L)
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    (P.toStrategy.familyAt ω lmb hz) = L.familyAt ω hz := by
  rcases ω with ⟨⟨alphaCValue, gammaValue⟩, ⟨alphaMValue, z⟩⟩
  simpa [toStrategy, Strategy.familyAt, Strategy.alphaMCommitment,
    RawP8Strategy.familyAt, nprSeed, alphaM, alphaC, gamma] using
    P.family_eq z hz alphaMValue lmb alphaCValue gammaValue

theorem legacy_tableAlpha_eq
    {timestamp : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {L : RawP8Strategy F K p}
    (P : LegacyPhaseFactorization (p := p) timestamp L)
    (z : K) (hz : z ≠ 0) (alphaMValue lmb : K) :
    (L.afterSeed z hz).base.problem.cfg.challenges.α = alphaMValue := by
  have h := congrArg
    (fun R : RawPlusIOSegmentedFamily F K => R.cfg.challenges.α)
    (P.family_eq z hz alphaMValue lmb 0 0)
  simpa using h.symm

/-- The same obstruction for the Form R challenge: a factorization forces the old seed-fixed `λ`
to equal every sampled `λ` (`λ` and `alphaM` are drawn in the same round). -/
theorem legacy_tableLam_eq
    {timestamp : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)}
    {L : RawP8Strategy F K p}
    (P : LegacyPhaseFactorization (p := p) timestamp L)
    (z : K) (hz : z ≠ 0) (alphaMValue lmb : K) :
    (L.afterSeed z hz).base.problem.cfg.challenges.lam = lmb := by
  have h := congrArg
    (fun R : RawPlusIOSegmentedFamily F K => R.cfg.challenges.lam)
    (P.family_eq z hz alphaMValue lmb 0 0)
  exact h.symm

end LegacyPhaseFactorization

end

end Nock.NockVMROM.Thm54.TemplateRawJointSoundness

#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.Strategy.sampledCoordinates
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.AlphaMFamilyData.nonSplicing
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.AlphaMCommitment.sameAlphaM_tables
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.AlphaMCommitment.sameAlphaM_io
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.Strategy.accepts_iff_six_families
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.Strategy.acceptsWithTopology_iff_raw_checks
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.Strategy.sampledAxisBoundary
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.Strategy.forwardSoundness_of_accepts
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.RegeneratedMemoryCountingData.failureEvent_card_le
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.specializedTopologyFailureEvent_card_le
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.specializedAxisFailure_of_refinement
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.productionFailureUnion_card_le
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.falseAcceptance_jointProbability_le
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.LegacyPhaseFactorization.familyAt_eq
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.LegacyPhaseFactorization.legacy_tableAlpha_eq
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.LegacyPhaseFactorization.legacy_tableLam_eq
#print axioms Nock.NockVMROM.Thm54.TemplateRawJointSoundness.specializedProblem_memoryLambda
