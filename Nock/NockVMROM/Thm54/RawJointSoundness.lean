import Nock.NockVMROM.Thm54.RawVerifier

/-!
This module replaces the proof-carrying `P8Strategy` experiment with a genuinely raw prover
interface. The seed commitment and post-coin message contain data only. Table validity, walk
certificates, and IO matching are consequences of `RawAccepts`.

The table timestamp challenge remains part of the seed-fixed `RawProblem`. Merely replacing the
memory-walk challenge by `alphaM` does not change it. The missing sampled-axis boundary is
therefore exported as `RawSampledAxisBoundaryResidual`. A future staged timestamp specialization
may discharge it, but no diagonal is assumed in this raw seed-fixed experiment.
-/

open scoped BigOperators Classical

namespace Nock.NockVMROM.Thm54

open Nock Nock.Walk

set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]

/-! ## Data-only challenge-ordered strategy -/

/-- The public compute row at the root of a raw problem. -/
def rawRootComputePub (problem : RawProblem F K) : ComputeTable.Pub K :=
  problem.exec.computePubAt ⟨0, problem.cfg.compRows_pos⟩

/-- Data fixed after the NPR seed and before the remaining three coins.

`base` fixes the problem, tree labels, node layouts/encoders, IO endpoints, and harmless placeholder
walk parameters. The table arrays and complete IO arrays are indexed by that same base and are
therefore also committed before `alphaC`, `gamma`, and `alphaM`. There are no proof-carrying
assignments, table-WF facts, RAP satisfaction facts, semantic targets, or capacity/injectivity
proofs in this commitment. -/
structure RawP8SeedCommitment (claim : P8PublicClaim) (z : K) (p : ℕ) where
  base : RawPlusIOSegmentedFamily F K
  sampled_seed : base.problem.cfg.challenges.z = z
  tables : RawTableArrays base
  io : RawIOArrays base p
  subject_binding :
    (rawRootComputePub base.problem).s = GlobalCarryRecognizer.enc z claim.subject
  formula_binding :
    (rawRootComputePub base.problem).f = GlobalCarryRecognizer.enc z claim.formula
  result_binding :
    (rawRootComputePub base.problem).e = GlobalCarryRecognizer.enc z claim.result

namespace RawP8SeedCommitment

/-- Insert only the three post-seed walk coins. The problem, encoders, widths, and IO endpoints
are copied definitionally. -/
def atJointCoins {claim : P8PublicClaim} {z : K} {p : ℕ}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p)
    (ω : JointCoins K) : RawPlusIOSegmentedFamily F K where
  problem := C.base.problem
  computeWalkAlpha := alphaC ω
  memoryWalkAlpha := alphaM ω
  walkGamma := gamma ω
  compNodeWidth := C.base.compNodeWidth
  compNodeEncode := C.base.compNodeEncode
  memNodeWidth := C.base.memNodeWidth
  memNodeEncode := C.base.memNodeEncode
  requests := C.base.requests
  responses := C.base.responses
  outMem := C.base.outMem

@[simp] theorem atJointCoins_problem {claim : P8PublicClaim} {z : K} {p : ℕ}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p) (ω : JointCoins K) :
    (C.atJointCoins ω).problem = C.base.problem := rfl

@[simp] theorem atJointCoins_computeWalkAlpha {claim : P8PublicClaim} {z : K} {p : ℕ}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p) (ω : JointCoins K) :
    (C.atJointCoins ω).computeWalkAlpha = alphaC ω := rfl

@[simp] theorem atJointCoins_walkGamma {claim : P8PublicClaim} {z : K} {p : ℕ}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p) (ω : JointCoins K) :
    (C.atJointCoins ω).walkGamma = gamma ω := rfl

@[simp] theorem atJointCoins_memoryWalkAlpha {claim : P8PublicClaim} {z : K} {p : ℕ}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p) (ω : JointCoins K) :
    (C.atJointCoins ω).memoryWalkAlpha = alphaM ω := rfl

/-- Joint-coin insertion does not silently alter the table timestamp challenge. -/
@[simp] theorem atJointCoins_tableAlpha {claim : P8PublicClaim} {z : K} {p : ℕ}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p) (ω : JointCoins K) :
    (C.atJointCoins ω).problem.cfg.challenges.α =
      C.base.problem.cfg.challenges.α := rfl

/-- Every non-walk family coordinate is definitionally the seed commitment. -/
theorem atJointCoins_seedFixed {claim : P8PublicClaim} {z : K} {p : ℕ}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p) (ω : JointCoins K) :
    (C.atJointCoins ω).problem = C.base.problem ∧
      (C.atJointCoins ω).compNodeWidth = C.base.compNodeWidth ∧
      (C.atJointCoins ω).compNodeEncode = C.base.compNodeEncode ∧
      (C.atJointCoins ω).memNodeWidth = C.base.memNodeWidth ∧
      (C.atJointCoins ω).memNodeEncode = C.base.memNodeEncode ∧
      (C.atJointCoins ω).requests = C.base.requests ∧
      (C.atJointCoins ω).responses = C.base.responses ∧
      (C.atJointCoins ω).outMem = C.base.outMem :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The committed table arrays transport definitionally because walk-coin insertion leaves the
problem and table dimensions fixed. -/
def tablesAt {claim : P8PublicClaim} {z : K} {p : ℕ}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p)
    (ω : JointCoins K) : RawTableArrays (C.atJointCoins ω) where
  compute := C.tables.compute
  memory := C.tables.memory

/-- The complete IO prover arrays transport definitionally because the execution and endpoints
remain fixed. -/
def ioAt {claim : P8PublicClaim} {z : K} {p : ℕ}
    (C : RawP8SeedCommitment (F := F) (K := K) claim z p)
    (ω : JointCoins K) : RawIOArrays (C.atJointCoins ω) p where
  multiplicity := C.io.multiplicity
  progAcc := C.io.progAcc
  memAcc := C.io.memAcc

end RawP8SeedCommitment

/-- The entire post-coin prover response: walk arrays and nothing else. -/
abbrev RawP8WalkResponse (K : Type) := RawWalkArrays K

/-- Its only post-coin response is raw walk data. -/
structure RawP8Strategy (F K : Type) [Field F] [Field K] [Algebra F K]
    (p : ℕ) [CharP K p] where
  claim : P8PublicClaim
  afterSeed :
    ∀ z : K, z ≠ 0 → RawP8SeedCommitment (F := F) (K := K) claim z p
  afterCoins :
    ∀ (ω : JointCoins K) (hz : nprSeed ω ≠ 0),
      RawP8WalkResponse K

namespace RawP8Strategy

def familyAt (T : RawP8Strategy F K p)
    (ω : JointCoins K) (hz : nprSeed ω ≠ 0) :
    RawPlusIOSegmentedFamily F K :=
  (T.afterSeed (nprSeed ω) hz).atJointCoins ω

/-- Assemble the verifier message. Only `walks` comes from the post-coin response. -/
def messageAt (T : RawP8Strategy F K p)
    (ω : JointCoins K) (hz : nprSeed ω ≠ 0) :
    RawMessage (T.familyAt ω hz) p where
  tables := (T.afterSeed (nprSeed ω) hz).tablesAt ω
  walks := T.afterCoins ω hz
  io := (T.afterSeed (nprSeed ω) hz).ioAt ω

/-- The table arrays in every sampled message are exactly the seed commitment. -/
@[simp] theorem messageAt_tables
    (T : RawP8Strategy F K p) (ω : JointCoins K)
    (hz : nprSeed ω ≠ 0) :
    (T.messageAt ω hz).tables =
      (T.afterSeed (nprSeed ω) hz).tablesAt ω := rfl

/-- The IO arrays in every sampled message are exactly the seed commitment. -/
@[simp] theorem messageAt_io
    (T : RawP8Strategy F K p) (ω : JointCoins K)
    (hz : nprSeed ω ≠ 0) :
    (T.messageAt ω hz).io =
      (T.afterSeed (nprSeed ω) hz).ioAt ω := rfl

/-- Reusing one seed commitment at two later coins cannot splice either problem. -/
theorem sameSeed_problem
    (T : RawP8Strategy F K p) (z : K) (hz : z ≠ 0)
    (ω₁ ω₂ : JointCoins K) :
    ((T.afterSeed z hz).atJointCoins ω₁).problem =
      ((T.afterSeed z hz).atJointCoins ω₂).problem := rfl

/-- Reusing one seed commitment at two later coins cannot splice either table array. -/
theorem sameSeed_tables
    (T : RawP8Strategy F K p) (z : K) (hz : z ≠ 0)
    (ω₁ ω₂ : JointCoins K) :
    ((T.afterSeed z hz).tablesAt ω₁).compute =
        ((T.afterSeed z hz).tablesAt ω₂).compute ∧
      ((T.afterSeed z hz).tablesAt ω₁).memory =
        ((T.afterSeed z hz).tablesAt ω₂).memory :=
  ⟨rfl, rfl⟩

/-- Reusing one seed commitment at two later coins cannot splice any IO array. -/
theorem sameSeed_io
    (T : RawP8Strategy F K p) (z : K) (hz : z ≠ 0)
    (ω₁ ω₂ : JointCoins K) :
    ((T.afterSeed z hz).ioAt ω₁).multiplicity =
        ((T.afterSeed z hz).ioAt ω₂).multiplicity ∧
      ((T.afterSeed z hz).ioAt ω₁).progAcc =
        ((T.afterSeed z hz).ioAt ω₂).progAcc ∧
      ((T.afterSeed z hz).ioAt ω₁).memAcc =
        ((T.afterSeed z hz).ioAt ω₂).memAcc :=
  ⟨rfl, rfl, rfl⟩

/-- Data-only acceptance. The zero-seed branch rejects. -/
def Accepts (T : RawP8Strategy F K p) (ω : JointCoins K) : Prop :=
  if hz : nprSeed ω ≠ 0 then
    RawAccepts T.claim (T.familyAt ω hz) ω (T.messageAt ω hz)
  else False

theorem not_accepts_zero (T : RawP8Strategy F K p)
    (ω : JointCoins K) (hz : nprSeed ω = 0) :
    ¬ T.Accepts ω := by
  simp [Accepts, hz]

/-- Exact expansion into the explicit verifier gates and all segmented RAP evaluations. -/
theorem accepts_iff_gates_and_sixRAP
    (T : RawP8Strategy F K p) (ω : JointCoins K)
    (hz : nprSeed ω ≠ 0) :
    T.Accepts ω ↔
      (T.messageAt ω hz).VerifierGates T.claim ω ∧
        (T.messageAt ω hz).SixRAPSatisfy := by
  simp only [Accepts, dif_pos hz, RawAccepts_iff_sixRAP_and_gates]

/-- The sampled problem uses `z`, and the three later family parameters use exactly the sampled
`alphaC`, `gamma`, and `alphaM`. -/
theorem sampled_challenges
    (T : RawP8Strategy F K p) (ω : JointCoins K)
    (hz : nprSeed ω ≠ 0) :
    (T.familyAt ω hz).problem.cfg.challenges.z = nprSeed ω ∧
      (T.familyAt ω hz).computeWalkAlpha = alphaC ω ∧
      (T.familyAt ω hz).walkGamma = gamma ω ∧
      (T.familyAt ω hz).memoryWalkAlpha = alphaM ω := by
  exact ⟨(T.afterSeed (nprSeed ω) hz).sampled_seed, rfl, rfl, rfl⟩

/-- Expansion to all six named segmented families. -/
theorem accepts_iff_six_families
    (T : RawP8Strategy F K p) (ω : JointCoins K)
    (hz : nprSeed ω ≠ 0) :
    T.Accepts ω ↔
      (T.messageAt ω hz).VerifierGates T.claim ω ∧
      (∀ kind, ((T.familyAt ω hz).computeTableRAP kind).Satisfies
        (T.messageAt ω hz).computeTableTrace) ∧
      (∀ kind, ((T.familyAt ω hz).memoryTableRAP kind).Satisfies
        (T.messageAt ω hz).memoryTableTrace) ∧
      (∀ kind, ((T.familyAt ω hz).computeWalkRAP kind).Satisfies
        (T.messageAt ω hz).computeWalkTrace) ∧
      (∀ kind, ((T.familyAt ω hz).memoryWalkRAP kind).Satisfies
        (T.messageAt ω hz).memoryWalkTrace) ∧
      (∀ kind, ((T.familyAt ω hz).computeIORAP kind).Satisfies
        (T.messageAt ω hz).computeIOTrace) ∧
      (∀ kind, ((T.familyAt ω hz).memoryIORAP kind).Satisfies
        (T.messageAt ω hz).memoryIOTrace) := by
  rw [T.accepts_iff_gates_and_sixRAP ω hz]
  rfl

/-! ## Raw semantic targets -/

/-- Field-level semantic target on exactly the seed-fixed raw problem. -/
def FieldTargetAt (T : RawP8Strategy F K p) (q : ℕ)
    (ω : JointCoins K) : Prop :=
  if hz : nprSeed ω ≠ 0 then
    let problem := (T.afterSeed (nprSeed ω) hz).base.problem
    (∃ Λ : ℕ,
      Nonempty
        (SemanticTrace.ExactExecutionSemanticData q Λ problem.cfg problem.exec)) ∧
      ExactMemoryAxisSemantics problem.cfg problem.exec
  else False

/-- Genuine target: the field target plus an actual evaluation of the fixed public claim. -/
def GenuineTargetAt (T : RawP8Strategy F K p) (q : ℕ)
    (ω : JointCoins K) : Prop :=
  T.FieldTargetAt q ω ∧ T.claim.Holds

/-- False acceptance is external; neither target is stored in the strategy or message. -/
def FalseAcceptanceSet (T : RawP8Strategy F K p) (q : ℕ) :
    Finset (JointCoins K) :=
  Finset.univ.filter (fun ω => T.Accepts ω ∧ ¬ T.GenuineTargetAt q ω)

@[simp] theorem mem_FalseAcceptanceSet_iff
    (T : RawP8Strategy F K p) (q : ℕ) (ω : JointCoins K) :
    ω ∈ T.FalseAcceptanceSet q ↔ T.Accepts ω ∧ ¬ T.GenuineTargetAt q ω := by
  simp [FalseAcceptanceSet]

/-! ## One forward verifier-soundness bundle -/

/-- Everything currently derivable directly from raw acceptance. Encoder injectivity is absent:
it is not needed for table descent, extraction of the walk certificates, or exact IO matching.
It enters only the later walk-failure cardinality estimates. -/
structure ForwardSoundnessAt
    (T : RawP8Strategy F K p) (ω : JointCoins K)
    (hz : nprSeed ω ≠ 0) : Prop where
  computeTable :
    (∀ i, ComputeTable.Vcomp
      (T.familyAt ω hz).cfg.challenges.computeInputs
      ((T.familyAt ω hz).exec.computePubAt i)
      ((T.familyAt ω hz).exec.computeDecAt i)) ∧
    (∀ i : Fin (T.familyAt ω hz).cfg.compRows,
      ∀ hi : (i : ℕ) + 1 < (T.familyAt ω hz).cfg.compRows,
      ((T.familyAt ω hz).exec.computePubAt i).ln =
        ((T.familyAt ω hz).exec.computePubAt
          ⟨(i : ℕ) + 1, hi⟩).ln_prev)
  memoryTable :
    (∀ i, MemoryTable.Vmem
      (T.familyAt ω hz).cfg.challenges.memoryInputs
      ((T.familyAt ω hz).exec.memoryPubAt i)) ∧
    (∀ i : Fin (T.familyAt ω hz).cfg.memRows,
      ∀ hi : (i : ℕ) + 1 < (T.familyAt ω hz).cfg.memRows,
      ((T.familyAt ω hz).exec.memoryPubAt i).icur =
        ((T.familyAt ω hz).exec.memoryPubAt
          ⟨(i : ℕ) + 1, hi⟩).ipre) ∧
    ((T.familyAt ω hz).exec.memoryPubAt
      ⟨0, (T.familyAt ω hz).cfg.memRows_pos⟩).pt.counts = 0 ∧
    ((T.familyAt ω hz).exec.memoryPubAt
      ⟨0, (T.familyAt ω hz).cfg.memRows_pos⟩).pt.indicator = 0 ∧
    ((T.familyAt ω hz).exec.memoryPubAt
      ⟨0, (T.familyAt ω hz).cfg.memRows_pos⟩).ipre = 0 ∧
    ((T.familyAt ω hz).exec.memoryPubAt
      ((T.familyAt ω hz).cfg.orbit.lastIndex
        (T.familyAt ω hz).cfg.memRows
        (T.familyAt ω hz).cfg.memRows_pos)).icur = 0
  seedNonzero : (T.familyAt ω hz).cfg.challenges.z ≠ 0
  computeWalk : (T.messageAt ω hz).ComputeWalkCertificate
  memoryWalk : (T.messageAt ω hz).MemoryWalkCertificate
  exactIO :
    IO.LIO (T.familyAt ω hz).cfg.Ksz
      (T.familyAt ω hz).exec.derivedRequestIO
      (T.familyAt ω hz).exec.derivedResponseIO

/-- Single forward soundness theorem for an arbitrary raw message.

The exact external assumptions are one state-tag characteristic condition, the two active-prefix
capacities, and `Ksz < p`. No table-WF or encoder-injectivity hypothesis is used. -/
theorem forwardSoundness_of_accepts
    (T : RawP8Strategy F K p) (ω : JointCoins K)
    (hz : nprSeed ω ≠ 0)
    (hchar : NodeEncoding.StateTagChar K)
    (hKp : (T.familyAt ω hz).cfg.Ksz < p)
    (hProgCap :
      (T.familyAt ω hz).exec.derivedRequestIO.length + 1 ≤
        2 ^ (T.familyAt ω hz).cfg.orbit.h)
    (hMemCap :
      (T.familyAt ω hz).exec.derivedResponseIO.length + 1 ≤
        2 ^ (T.familyAt ω hz).cfg.orbit.h)
    (hlam : ∀ i, ((T.familyAt ω hz).exec.memoryPubAt i).lambda = (T.familyAt ω hz).cfg.challenges.lam)
    (haccept : T.Accepts ω) :
    T.ForwardSoundnessAt ω hz := by
  let M := T.messageAt ω hz
  have hraw : RawAccepts T.claim (T.familyAt ω hz) ω M := by
    simpa [Accepts, hz, M] using haccept
  have hsix : M.SixRAPSatisfy := hraw.2
  have hcomp := M.computeTable_sound_wfFree hchar hsix.1
  have hmem := M.memoryTable_sound_wfFree hchar hlam hsix.2.1
  refine
    { computeTable := hcomp.1
      memoryTable := hmem.1
      seedNonzero := hcomp.2
      computeWalk := (M.computeWalkRAP_wholeTrace_iff).1 hsix.2.2.1
      memoryWalk := (M.memoryWalkRAP_wholeTrace_iff).1 hsix.2.2.2.1
      exactIO := M.lio_of_accepts hKp hProgCap hMemCap hraw }

/-! ## Honest sampled-axis boundary -/

/-- Joint-coin instantiation preserves the seed-fixed table timestamp, not `alphaM`. -/
theorem familyAt_preserves_tableAlpha
    (T : RawP8Strategy F K p) (ω : JointCoins K)
    (hz : nprSeed ω ≠ 0) :
    (T.familyAt ω hz).problem.cfg.challenges.α =
      (T.afterSeed (nprSeed ω) hz).base.problem.cfg.challenges.α :=
  rfl

/-- Exact unresolved boundary needed to place a failed axis target in the sampled `alphaM` event.
It is deliberately not a field of raw acceptance. -/
def RawSampledAxisBoundaryResidual (T : RawP8Strategy F K p) : Prop :=
  ∀ (ω : JointCoins K) (hz : nprSeed ω ≠ 0),
    T.Accepts ω →
    let problem := (T.afterSeed (nprSeed ω) hz).base.problem
    ∀ i : Fin problem.cfg.kMem,
      (Nock.AxisBatching.MTree.countsP
        (exactAxisTree problem.cfg problem.exec i)).eval (alphaM ω) = 0

/-! ## Raw fixed-seed failure fibers -/

/-- Compute-walk bad pairs with the raw encoder selected separately in each seed fiber. -/
def rawComputeSeedPairs
    (T : RawP8Strategy F K p)
    (labels : ZLabelFamily K ComputeTable.State (ComputeTable.DTcomp K))
    (fo : ℕ → ℕ) (h : ℕ) : Finset (K × (K × K)) :=
  fiberEvent (validSeeds K) fun z =>
    if hz : z ≠ 0 then
      walkBadFiber (ComputeTable.comp_stateSep (K := K))
        (T.afterSeed z hz).base.compNodeEncode labels fo h z
    else ∅

/-- Lift the compute fiber while leaving `alphaM` unrestricted. -/
def rawComputeWalkFailureEvent
    (T : RawP8Strategy F K p)
    (labels : ZLabelFamily K ComputeTable.State (ComputeTable.DTcomp K))
    (fo : ℕ → ℕ) (h : ℕ) : Finset (JointCoins K) :=
  liftComputeSeedFibers (rawComputeSeedPairs T labels fo h)

/-- Memory-walk bad pairs with the raw encoder selected separately in each seed fiber. -/
def rawMemorySeedPairs
    (T : RawP8Strategy F K p)
    (labels : ZLabelFamily K MemoryTable.MState (MemoryTable.DTmem K))
    (fo : ℕ → ℕ) (kroots h : ℕ) : Finset (K × (K × K)) :=
  fiberEvent (validSeeds K) fun z =>
    if hz : z ≠ 0 then
      walkBadForestFiber (MemoryTable.mem_stateSep (K := K))
        (T.afterSeed z hz).base.memNodeEncode labels fo kroots h z
    else ∅

/-- Lift the memory fiber while leaving `alphaC` unrestricted. -/
def rawMemoryWalkFailureEvent
    (T : RawP8Strategy F K p)
    (labels : ZLabelFamily K MemoryTable.MState (MemoryTable.DTmem K))
    (fo : ℕ → ℕ) (kroots h : ℕ) : Finset (JointCoins K) :=
  liftMemorySeedFibers (rawMemorySeedPairs T labels fo kroots h)

@[simp] theorem mem_rawComputeWalkFailureEvent_iff
    (T : RawP8Strategy F K p)
    (labels : ZLabelFamily K ComputeTable.State (ComputeTable.DTcomp K))
    (fo : ℕ → ℕ) (h : ℕ) (ω : JointCoins K) :
    ω ∈ rawComputeWalkFailureEvent T labels fo h ↔
      ∃ hz : nprSeed ω ≠ 0,
        computeCoins ω ∈
          walkBadFiber (ComputeTable.comp_stateSep (K := K))
            (T.afterSeed (nprSeed ω) hz).base.compNodeEncode
            labels fo h (nprSeed ω) := by
  rw [rawComputeWalkFailureEvent, mem_liftComputeSeedFibers_iff,
    rawComputeSeedPairs, mem_fiberEvent_iff, mem_validSeeds]
  constructor
  · rintro ⟨hz, hmem⟩
    exact ⟨hz, by simpa only [dif_pos hz] using hmem⟩
  · rintro ⟨hz, hmem⟩
    exact ⟨hz, by simpa only [dif_pos hz] using hmem⟩

@[simp] theorem mem_rawMemoryWalkFailureEvent_iff
    (T : RawP8Strategy F K p)
    (labels : ZLabelFamily K MemoryTable.MState (MemoryTable.DTmem K))
    (fo : ℕ → ℕ) (kroots h : ℕ) (ω : JointCoins K) :
    ω ∈ rawMemoryWalkFailureEvent T labels fo kroots h ↔
      ∃ hz : nprSeed ω ≠ 0,
        memoryCoins ω ∈
          walkBadForestFiber (MemoryTable.mem_stateSep (K := K))
            (T.afterSeed (nprSeed ω) hz).base.memNodeEncode
            labels fo kroots h (nprSeed ω) := by
  rw [rawMemoryWalkFailureEvent, mem_liftMemorySeedFibers_iff,
    rawMemorySeedPairs, mem_fiberEvent_iff, mem_validSeeds]
  constructor
  · rintro ⟨hz, hmem⟩
    exact ⟨hz, by simpa only [dif_pos hz] using hmem⟩
  · rintro ⟨hz, hmem⟩
    exact ⟨hz, by simpa only [dif_pos hz] using hmem⟩

private theorem raw_seed_walk_extension_bound
    (eventCard workload : ℕ)
    (hcard :
      eventCard ≤ (Fintype.card K - 1) * (Fintype.card K * workload)) :
    eventCard * Fintype.card K ≤ workload * Fintype.card K ^ 3 := by
  let k := Fintype.card K
  calc
    eventCard * k ≤ ((k - 1) * (k * workload)) * k :=
      Nat.mul_le_mul_right k hcard
    _ ≤ (k * (k * workload)) * k := by
      exact Nat.mul_le_mul_right k
        (Nat.mul_le_mul_right (k * workload) (Nat.sub_le k 1))
    _ = workload * k ^ 3 := by ring

/-- Raw compute-fiber bound. Encoder injectivity appears exactly where the walk collision
theorem requires it, not in acceptance or forward verifier soundness. -/
theorem rawComputeWalkFailureEvent_card_le
    (T : RawP8Strategy F K p)
    (labels : ZLabelFamily K ComputeTable.State (ComputeTable.DTcomp K))
    (fo : ℕ → ℕ) {h workload : ℕ}
    (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h)
    (harity : ∀ i, fo i ≤ 3)
    (hfo : ∀ z i, 1 ≤ i → i ≤ h →
      fo i = (ComputeTable.comp_stateSep (K := K)).fanout (labels.row z i).1)
    (hF : ∀ z i, 1 ≤ i → i ≤ h →
      ComputeTable.Fcomp (labels.row z i)
        (fun j : Fin 3 =>
          if (j : ℕ) < fo i then some (labels.child z i (j + 1)) else none))
    (hEnc : ∀ z (hz : z ≠ 0),
      Function.Injective (T.afterSeed z hz).base.compNodeEncode)
    (hwork : ∀ z (hz : z ≠ 0),
      walkWorkload h (T.afterSeed z hz).base.compNodeWidth ≤ workload) :
    (rawComputeWalkFailureEvent T labels fo h).card ≤
      workload * Fintype.card K ^ 3 := by
  rw [rawComputeWalkFailureEvent, card_liftComputeSeedFibers]
  apply raw_seed_walk_extension_bound
  unfold rawComputeSeedPairs
  simpa only [validSeeds_card] using
    (fiberEvent_card_le (validSeeds K)
      (fun z =>
        if hz : z ≠ 0 then
          walkBadFiber (ComputeTable.comp_stateSep (K := K))
            (T.afterSeed z hz).base.compNodeEncode labels fo h z
        else ∅)
      (Fintype.card K * workload) (by
        intro z hzmem
        have hz : z ≠ 0 := (mem_validSeeds z).1 hzmem
        simp only [dif_pos hz]
        calc
          (walkBadFiber (ComputeTable.comp_stateSep (K := K))
            (T.afterSeed z hz).base.compNodeEncode labels fo h z).card
              ≤ Fintype.card K * h +
                Fintype.card K *
                  (h * ((T.afterSeed z hz).base.compNodeWidth - 1)) :=
            walkBadFiber_card_le (ComputeTable.comp_stateSep (K := K))
              (T.afterSeed z hz).base.compNodeEncode (hEnc z hz)
              labels fo hSf hvalid harity hfo hF z
          _ = Fintype.card K *
              walkWorkload h (T.afterSeed z hz).base.compNodeWidth := by
            simp only [walkWorkload]
            ring
          _ ≤ Fintype.card K * workload :=
            Nat.mul_le_mul_left _ (hwork z hz)))

/-- Raw memory-fiber bound with injectivity localized to the forest collision estimate. -/
theorem rawMemoryWalkFailureEvent_card_le
    (T : RawP8Strategy F K p)
    (labels : ZLabelFamily K MemoryTable.MState (MemoryTable.DTmem K))
    (fo : ℕ → ℕ) {kroots h workload : ℕ}
    (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h)
    (hvalid : BFSValidF kroots fo h) (harity : ∀ i, fo i ≤ 2)
    (hfo : ∀ z i, 1 ≤ i → i ≤ h →
      fo i = (MemoryTable.mem_stateSep (K := K)).fanout (labels.row z i).1)
    (hF : ∀ z i, 1 ≤ i → i ≤ h →
      MemoryTable.Fmem (labels.row z i)
        (fun j : Fin 2 =>
          if (j : ℕ) < fo i then some (labels.child z i (j + 1)) else none))
    (hEnc : ∀ z (hz : z ≠ 0),
      Function.Injective (T.afterSeed z hz).base.memNodeEncode)
    (hwork : ∀ z (hz : z ≠ 0),
      walkWorkload h (T.afterSeed z hz).base.memNodeWidth ≤ workload) :
    (rawMemoryWalkFailureEvent T labels fo kroots h).card ≤
      workload * Fintype.card K ^ 3 := by
  rw [rawMemoryWalkFailureEvent, card_liftMemorySeedFibers]
  apply raw_seed_walk_extension_bound
  unfold rawMemorySeedPairs
  simpa only [validSeeds_card] using
    (fiberEvent_card_le (validSeeds K)
      (fun z =>
        if hz : z ≠ 0 then
          walkBadForestFiber (MemoryTable.mem_stateSep (K := K))
            (T.afterSeed z hz).base.memNodeEncode labels fo kroots h z
        else ∅)
      (Fintype.card K * workload) (by
        intro z hzmem
        have hz : z ≠ 0 := (mem_validSeeds z).1 hzmem
        simp only [dif_pos hz]
        calc
          (walkBadForestFiber (MemoryTable.mem_stateSep (K := K))
            (T.afterSeed z hz).base.memNodeEncode labels fo kroots h z).card
              ≤ Fintype.card K * h +
                Fintype.card K *
                  (h * ((T.afterSeed z hz).base.memNodeWidth - 1)) :=
            walkBadForestFiber_card_le (MemoryTable.mem_stateSep (K := K))
              (T.afterSeed z hz).base.memNodeEncode (hEnc z hz)
              labels fo hk hSf hvalid harity hfo hF z
          _ = Fintype.card K *
              walkWorkload h (T.afterSeed z hz).base.memNodeWidth := by
            simp only [walkWorkload]
            ring
          _ ≤ Fintype.card K * workload :=
            Nat.mul_le_mul_left _ (hwork z hz)))

/-! ## Raw axis fibers and aggregate failure union -/

/-- The exact structural obligations not currently exposed as gates by `RawVerifier`.

These fields are precisely the external hypotheses used by forward soundness and walk
counting. They are deliberately outside `RawAccepts`; when raw structural gates are added to the
verifier, this is the interface they must discharge. -/
structure RawStructuralGateResidual (T : RawP8Strategy F K p) : Prop where
  stateTagChar : NodeEncoding.StateTagChar K
  Ksz_lt_char :
    ∀ z (hz : z ≠ 0), (T.afterSeed z hz).base.cfg.Ksz < p
  progCapacity :
    ∀ z (hz : z ≠ 0),
      (T.afterSeed z hz).base.exec.derivedRequestIO.length + 1 ≤
        2 ^ (T.afterSeed z hz).base.cfg.orbit.h
  memCapacity :
    ∀ z (hz : z ≠ 0),
      (T.afterSeed z hz).base.exec.derivedResponseIO.length + 1 ≤
        2 ^ (T.afterSeed z hz).base.cfg.orbit.h
  computeEncoderInjective :
    ∀ z (hz : z ≠ 0),
      Function.Injective (T.afterSeed z hz).base.compNodeEncode
  memoryEncoderInjective :
    ∀ z (hz : z ≠ 0),
      Function.Injective (T.afterSeed z hz).base.memNodeEncode

/-- Convenience specialization of the forward bundle from the explicitly isolated structural
residual. Encoder injectivity remains unused by this theorem. -/
theorem forwardSoundness_of_accepts_of_structural
    (T : RawP8Strategy F K p) (ω : JointCoins K)
    (hz : nprSeed ω ≠ 0)
    (hs : RawStructuralGateResidual T)
    (hlam : ∀ i, ((T.familyAt ω hz).exec.memoryPubAt i).lambda = (T.familyAt ω hz).cfg.challenges.lam)
    (haccept : T.Accepts ω) :
    T.ForwardSoundnessAt ω hz :=
  T.forwardSoundness_of_accepts ω hz hs.stateTagChar
    (hs.Ksz_lt_char _ hz) (hs.progCapacity _ hz) (hs.memCapacity _ hz) hlam haccept

/-- Seed-indexed exact axis bad pairs. The polynomial is evaluated at sampled `alphaM`, while
the exact tree remains the one fixed in the seed commitment. -/
def rawSeededAxisPairs (T : RawP8Strategy F K p) : Finset (K × K) :=
  fiberEvent (validSeeds K) fun z =>
    if hz : z ≠ 0 then
      let problem := (T.afterSeed z hz).base.problem
      axisBadAlphas problem.cfg problem.exec
    else ∅

def rawSeededAxisFailureEvent (T : RawP8Strategy F K p) :
    Finset (JointCoins K) :=
  liftAxisSeedFibers (rawSeededAxisPairs T)

@[simp] theorem mem_rawSeededAxisFailureEvent_iff
    (T : RawP8Strategy F K p) (ω : JointCoins K) :
    ω ∈ rawSeededAxisFailureEvent T ↔
      ∃ hz : nprSeed ω ≠ 0,
        let problem := (T.afterSeed (nprSeed ω) hz).base.problem
        alphaM ω ∈ axisBadAlphas problem.cfg problem.exec := by
  rw [rawSeededAxisFailureEvent, mem_liftAxisSeedFibers_iff,
    rawSeededAxisPairs, mem_fiberEvent_iff, mem_validSeeds]
  constructor
  · rintro ⟨hz, hmem⟩
    exact ⟨hz, by simpa only [dif_pos hz] using hmem⟩
  · rintro ⟨hz, hmem⟩
    exact ⟨hz, by simpa only [dif_pos hz] using hmem⟩

theorem rawSeededAxisFailureEvent_card_le
    (h2 : (2 : K) ≠ 0)
    (T : RawP8Strategy F K p) (axisWorkload : ℕ)
    (refinement :
      ∀ (z : K) (hz : z ≠ 0),
        let problem := (T.afterSeed z hz).base.problem
        ExactAxisRefinement problem.cfg problem.exec)
    (hwork :
      ∀ (z : K) (hz : z ≠ 0),
        let problem := (T.afterSeed z hz).base.problem
        exactAxisWorkload problem.cfg problem.exec ≤ axisWorkload) :
    (rawSeededAxisFailureEvent T).card ≤
      axisWorkload * Fintype.card K ^ 3 := by
  rw [rawSeededAxisFailureEvent, card_liftAxisSeedFibers]
  have hpairs :
      (rawSeededAxisPairs T).card ≤
        (Fintype.card K - 1) * axisWorkload := by
    unfold rawSeededAxisPairs
    simpa only [validSeeds_card] using
      (fiberEvent_card_le (validSeeds K)
        (fun z =>
          if hz : z ≠ 0 then
            let problem := (T.afterSeed z hz).base.problem
            axisBadAlphas problem.cfg problem.exec
          else ∅)
        axisWorkload (by
          intro z hzmem
          have hz : z ≠ 0 := (mem_validSeeds z).1 hzmem
          simp only [dif_pos hz]
          exact (axisBadAlphas_card_le h2 (refinement z hz)).trans
            (hwork z hz)))
  calc
    (rawSeededAxisPairs T).card * Fintype.card K ^ 2
        ≤ ((Fintype.card K - 1) * axisWorkload) *
            Fintype.card K ^ 2 :=
      Nat.mul_le_mul_right _ hpairs
    _ ≤ (Fintype.card K * axisWorkload) * Fintype.card K ^ 2 := by
      exact Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right axisWorkload
          (Nat.sub_le (Fintype.card K) 1))
    _ = axisWorkload * Fintype.card K ^ 3 := by ring

/-- Five-class raw failure union. This definition does not claim false-acceptance containment. -/
def RawFailureUnion
    (T : RawP8Strategy F K p)
    (computeLabels : ZLabelFamily K ComputeTable.State (ComputeTable.DTcomp K))
    (computeFo : ℕ → ℕ) (computeHeight : ℕ)
    (memoryLabels : ZLabelFamily K MemoryTable.MState (MemoryTable.DTmem K))
    (memoryFo : ℕ → ℕ) (memoryRoots memoryHeight : ℕ)
    (census : ComparisonCensus Λ) : Finset (JointCoins K) :=
  ((((zeroSeedFailureEvent ∪
      rawComputeWalkFailureEvent T computeLabels computeFo computeHeight) ∪
      rawMemoryWalkFailureEvent T memoryLabels memoryFo memoryRoots memoryHeight) ∪
      collisionFailureEvent census) ∪
      rawSeededAxisFailureEvent T)

@[simp] theorem mem_RawFailureUnion_iff
    (T : RawP8Strategy F K p)
    (computeLabels : ZLabelFamily K ComputeTable.State (ComputeTable.DTcomp K))
    (computeFo : ℕ → ℕ) (computeHeight : ℕ)
    (memoryLabels : ZLabelFamily K MemoryTable.MState (MemoryTable.DTmem K))
    (memoryFo : ℕ → ℕ) (memoryRoots memoryHeight : ℕ)
    (census : ComparisonCensus Λ) (ω : JointCoins K) :
    ω ∈ RawFailureUnion T computeLabels computeFo computeHeight
        memoryLabels memoryFo memoryRoots memoryHeight census ↔
      nprSeed ω = 0 ∨
      (∃ hz : nprSeed ω ≠ 0,
        computeCoins ω ∈
          walkBadFiber (ComputeTable.comp_stateSep (K := K))
            (T.afterSeed (nprSeed ω) hz).base.compNodeEncode
            computeLabels computeFo computeHeight (nprSeed ω)) ∨
      (∃ hz : nprSeed ω ≠ 0,
        memoryCoins ω ∈
          walkBadForestFiber (MemoryTable.mem_stateSep (K := K))
            (T.afterSeed (nprSeed ω) hz).base.memNodeEncode
            memoryLabels memoryFo memoryRoots memoryHeight (nprSeed ω)) ∨
      (∃ i : Fin census.count,
        ¬ GlobalCarryRecognizer.SepSeed (nprSeed ω)
          (census.pair i).1 (census.pair i).2) ∨
      (∃ hz : nprSeed ω ≠ 0,
        let problem := (T.afterSeed (nprSeed ω) hz).base.problem
        alphaM ω ∈ axisBadAlphas problem.cfg problem.exec) := by
  simp [RawFailureUnion]

def rawJointWorkload
    (computeWorkload memoryWorkload collisionCount Λ axisWorkload : ℕ) : ℕ :=
  1 + computeWorkload + memoryWorkload +
    collisionCount * (2 * Λ - 1) + axisWorkload

/-- Aggregate cardinality from the two raw walk bounds and the raw axis bound. The zero and NPR
collision terms reuse the existing `JointSoundness` counting lemmas. -/
theorem rawFailureUnion_card_le
    (T : RawP8Strategy F K p)
    (computeLabels : ZLabelFamily K ComputeTable.State (ComputeTable.DTcomp K))
    (computeFo : ℕ → ℕ) (computeHeight computeWorkload : ℕ)
    (memoryLabels : ZLabelFamily K MemoryTable.MState (MemoryTable.DTmem K))
    (memoryFo : ℕ → ℕ) (memoryRoots memoryHeight memoryWorkload : ℕ)
    (census : ComparisonCensus Λ) (axisWorkload : ℕ)
    (hcompute :
      (rawComputeWalkFailureEvent T computeLabels computeFo computeHeight).card ≤
        computeWorkload * Fintype.card K ^ 3)
    (hmemory :
      (rawMemoryWalkFailureEvent T memoryLabels memoryFo memoryRoots memoryHeight).card ≤
        memoryWorkload * Fintype.card K ^ 3)
    (haxis :
      (rawSeededAxisFailureEvent T).card ≤
        axisWorkload * Fintype.card K ^ 3) :
    (RawFailureUnion T computeLabels computeFo computeHeight
      memoryLabels memoryFo memoryRoots memoryHeight census).card ≤
      rawJointWorkload computeWorkload memoryWorkload census.count Λ axisWorkload *
        Fintype.card K ^ 3 := by
  let k3 := Fintype.card K ^ 3
  let Z : Finset (JointCoins K) := zeroSeedFailureEvent
  let C := rawComputeWalkFailureEvent T computeLabels computeFo computeHeight
  let M := rawMemoryWalkFailureEvent T memoryLabels memoryFo memoryRoots memoryHeight
  let N : Finset (JointCoins K) := collisionFailureEvent census
  let A := rawSeededAxisFailureEvent T
  have hZ : Z.card ≤ 1 * k3 := by
    simp [Z, k3, zeroSeedFailureEvent_card]
  have hC : C.card ≤ computeWorkload * k3 := hcompute
  have hM : M.card ≤ memoryWorkload * k3 := hmemory
  have hN : N.card ≤ (census.count * (2 * Λ - 1)) * k3 :=
    collisionFailureEvent_card_le census
  have hA : A.card ≤ axisWorkload * k3 := haxis
  calc
    (RawFailureUnion T computeLabels computeFo computeHeight
      memoryLabels memoryFo memoryRoots memoryHeight census).card
        ≤ Z.card + C.card + M.card + N.card + A.card := by
      simpa [RawFailureUnion, Z, C, M, N, A] using
        (calc
          ((((Z ∪ C) ∪ M) ∪ N) ∪ A).card
              ≤ (((Z ∪ C) ∪ M) ∪ N).card + A.card :=
            Finset.card_union_le _ _
          _ ≤ ((Z ∪ C) ∪ M).card + N.card + A.card := by
            exact Nat.add_le_add_right (Finset.card_union_le _ _) _
          _ ≤ (Z ∪ C).card + M.card + N.card + A.card := by
            exact Nat.add_le_add_right
              (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
          _ ≤ Z.card + C.card + M.card + N.card + A.card := by
            exact Nat.add_le_add_right
              (Nat.add_le_add_right
                (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _)
    _ ≤ 1 * k3 + computeWorkload * k3 + memoryWorkload * k3 +
        (census.count * (2 * Λ - 1)) * k3 + axisWorkload * k3 :=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add hZ hC) hM) hN) hA
    _ = rawJointWorkload computeWorkload memoryWorkload census.count Λ
        axisWorkload * Fintype.card K ^ 3 := by
      simp only [rawJointWorkload, k3]
      ring

/-- Exact remaining production seam. This proposition is exported, but no theorem asserts it. -/
def RawResidualGenuineTargetContainment
    (T : RawP8Strategy F K p) (q : ℕ)
    (computeLabels : ZLabelFamily K ComputeTable.State (ComputeTable.DTcomp K))
    (computeFo : ℕ → ℕ) (computeHeight : ℕ)
    (memoryLabels : ZLabelFamily K MemoryTable.MState (MemoryTable.DTmem K))
    (memoryFo : ℕ → ℕ) (memoryRoots memoryHeight : ℕ)
    (census : ComparisonCensus Λ) : Prop :=
  ∀ ω, T.Accepts ω → ¬ T.GenuineTargetAt q ω →
    ω ∈ RawFailureUnion T computeLabels computeFo computeHeight
      memoryLabels memoryFo memoryRoots memoryHeight census

/-- Generic cardinality-to-probability adapter. Containment remains an explicit premise. -/
theorem rawFalseAcceptance_jointProbability_le
    (T : RawP8Strategy F K p) (q workload : ℕ)
    (failure : Finset (JointCoins K))
    (hcontain : T.FalseAcceptanceSet q ⊆ failure)
    (hfailure : failure.card ≤ workload * Fintype.card K ^ 3) :
    |jointProbability (T.FalseAcceptanceSet q)| ≤
      (workload : ℝ) / (Fintype.card K : ℝ) := by
  apply jointProbability_le_workload_div_card
  exact (Finset.card_le_card hcontain).trans hfailure


/-- Phase-preserving erasure of the proof-carrying experiment. -/
def ofLegacy (T : P8Strategy (F := F) (K := K)) : RawP8Strategy F K p where
  claim := T.claim
  afterSeed z hz :=
    let C := T.afterSeed z hz
    { base := RawPlusIOSegmentedFamily.ofLegacy C.family
      sampled_seed := C.sampled_seed
      tables :=
        { compute := C.computeTableAux
          memory := C.memoryTableAux }
      io :=
        { multiplicity := C.exactIO.multiplicity
          progAcc := C.exactIO.progAcc
          memAcc := C.exactIO.memAcc }
      subject_binding := by
        simpa [rawRootComputePub, exactRootComputePub,
          RawPlusIOSegmentedFamily.ofLegacy, RawProblem.ofExact] using
          C.subject_binding
      formula_binding := by
        simpa [rawRootComputePub, exactRootComputePub,
          RawPlusIOSegmentedFamily.ofLegacy, RawProblem.ofExact] using
          C.formula_binding
      result_binding := by
        simpa [rawRootComputePub, exactRootComputePub,
          RawPlusIOSegmentedFamily.ofLegacy, RawProblem.ofExact] using
          C.result_binding }
  afterCoins ω hz :=
    { computeLn := (T.afterWalk ω hz).computeWalk.ln
      computeCount := (T.afterWalk ω hz).computeWalk.count
      computeAcc := (T.afterWalk ω hz).computeWalk.acc
      memoryLn := (T.afterWalk ω hz).memoryWalk.ln
      memoryCount := (T.afterWalk ω hz).memoryWalk.count
      memoryAcc := (T.afterWalk ω hz).memoryWalk.acc }

theorem messageAt_ofLegacy
    (T : P8Strategy (F := F) (K := K))
    (ω : JointCoins K) (hz : nprSeed ω ≠ 0) :
    (ofLegacy (p := p) T).messageAt ω hz =
      RawMessage.ofLegacy (T.assignmentAt ω hz) := by
  rfl

theorem accepts_ofLegacy
    (T : P8Strategy (F := F) (K := K))
    (ω : JointCoins K) (hz : nprSeed ω ≠ 0)
    (haccept : T.Accepts ω)
    (hgates :
      let A := T.assignmentAt ω hz
      (RawMessage.ofLegacy A).VerifierGates T.claim ω) :
    (ofLegacy (p := p) T).Accepts ω := by
  rw [Accepts, dif_pos hz]
  rw [messageAt_ofLegacy]
  exact RawMessage.accepts_of_legacy_P8 T ω hz haccept hgates

end RawP8Strategy

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.RawP8Strategy.sameSeed_problem
#print axioms Nock.NockVMROM.Thm54.RawP8Strategy.sameSeed_tables
#print axioms Nock.NockVMROM.Thm54.RawP8Strategy.sameSeed_io
#print axioms Nock.NockVMROM.Thm54.RawP8Strategy.accepts_iff_six_families
#print axioms Nock.NockVMROM.Thm54.RawP8Strategy.forwardSoundness_of_accepts
#print axioms Nock.NockVMROM.Thm54.RawP8Strategy.rawComputeWalkFailureEvent_card_le
#print axioms Nock.NockVMROM.Thm54.RawP8Strategy.rawMemoryWalkFailureEvent_card_le
#print axioms Nock.NockVMROM.Thm54.RawP8Strategy.rawSeededAxisFailureEvent_card_le
#print axioms Nock.NockVMROM.Thm54.RawP8Strategy.rawFailureUnion_card_le
#print axioms Nock.NockVMROM.Thm54.RawP8Strategy.rawFalseAcceptance_jointProbability_le
#print axioms Nock.NockVMROM.Thm54.RawP8Strategy.accepts_ofLegacy
