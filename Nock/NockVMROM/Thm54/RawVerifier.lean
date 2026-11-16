import Nock.NockVMROM.Thm54.JointSoundness

/-!
# Raw Theorem 5.4 prover messages and verification

The prover-facing family and message in this file have no `Prop` fields.  In particular they do
not contain table WF, a nonzero seed, IO satisfaction, endpoint proofs, walk certificates, node
encoder injectivity, or active-prefix capacity proofs.  Acceptance consists only of explicit
verifier gates and the 24 segmented `RAP.Satisfies` evaluations.

Table WF is used only by the optional lift back to the legacy proof-carrying family.  Forward
table soundness is WF-free: row-segment satisfaction is evaluated at each committed row, the
free selector is pinned by the AIR under `NodeEncoding.StateTagChar`, and
`ComputeTable.equiv_compute_sound` / `MemoryTable.equiv_mem_sound` finish the descent.
-/

namespace Nock.NockVMROM.Thm54

open Classical
open Nock Framework Framework.Reify Framework.Thm54
open Nock.Reified
open scoped Polynomial

set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {p : ℕ} [CharP K p]

/-! ## Raw problem and family indices -/

/-- The raw problem removes the three proof fields of `ExactCanonicalRAPProblem`.  The structural
orbit and forest-shape invariants already belonging to `ExactConfig` and `ExactExecution` remain
the public statement being verified. -/
structure RawProblem (F K : Type) [Field F] [Field K] [Algebra F K] where
  cfg : ExactConfig F K
  exec : ExactExecution cfg

namespace RawProblem

/-- Assumptions needed only to reconstruct the legacy exact problem and its table biconditionals.
They are not needed by forward raw soundness. -/
def TableCompletenessAssumptions (Q : RawProblem F K) : Prop :=
  Q.cfg.challenges.z ≠ 0 ∧
    (∀ i, ComputeTable.WF Q.cfg.challenges.computeInputs (Q.exec.computePubAt i)) ∧
    (∀ i, MemoryTable.WF Q.cfg.challenges.memoryInputs (Q.exec.memoryPubAt i)) ∧
    (∀ i, (Q.exec.memoryPubAt i).lambda =
      (Q.exec.memoryPubAt ⟨0, Q.cfg.memRows_pos⟩).lambda)

def ofExact (Q : ExactCanonicalRAPProblem F K) : RawProblem F K where
  cfg := Q.cfg
  exec := Q.exec

def toExact (Q : RawProblem F K) (h : Q.TableCompletenessAssumptions) :
    ExactCanonicalRAPProblem F K where
  cfg := Q.cfg
  exec := Q.exec
  z_ne_zero := h.1
  compute_wf := h.2.1
  memory_wf := h.2.2.1
  memory_same_lambda := h.2.2.2

end RawProblem

/-- Data-only analogue of `PlusIOSegmentedFamily`.  Injectivity and capacity are deliberately
soundness hypotheses, not fields. -/
structure RawPlusIOSegmentedFamily (F K : Type) [Field F] [Field K] [Algebra F K] where
  problem : RawProblem F K
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

namespace RawPlusIOSegmentedFamily

variable (R : RawPlusIOSegmentedFamily F K)

abbrev cfg := R.problem.cfg
abbrev exec := R.problem.exec

/-! The raw structure retains the legacy width/encoder fields for source compatibility, but raw
acceptance below binds them extensionally to these production encoders.  `StateTagChar` stays an
external field-family assumption: no proof of it is stored in prover data. -/

/-- Exact binding of the two raw encoder payloads to the production coordinate encoders.  `HEq`
is necessary because each encoder's domain contains its prover-supplied width.  Under the external
`StateTagChar K` hypothesis this is a literal equality to the canonical injective encoder, not a
prover-supplied injectivity certificate. -/
def CanonicalNodeEncoderGates : Prop :=
  R.compNodeWidth = NodeEncoding.computeNodeWidth ∧
    (∀ hchar : NodeEncoding.StateTagChar K,
      HEq R.compNodeEncode (NodeEncoding.computeNodeEncode hchar)) ∧
    R.memNodeWidth = NodeEncoding.memoryNodeWidth ∧
    (∀ hchar : NodeEncoding.StateTagChar K,
      HEq R.memNodeEncode (NodeEncoding.memoryNodeEncode hchar))

def ofLegacy (S : PlusIOSegmentedFamily F K) : RawPlusIOSegmentedFamily F K where
  problem := RawProblem.ofExact S.problem
  computeWalkAlpha := S.computeWalkAlpha
  memoryWalkAlpha := S.memoryWalkAlpha
  walkGamma := S.walkGamma
  compNodeWidth := S.compNodeWidth
  compNodeEncode := S.compNodeEncode
  memNodeWidth := S.memNodeWidth
  memNodeEncode := S.memNodeEncode
  requests := S.requests
  responses := S.responses
  outMem := S.outMem

/-- Optional completeness lift.  Exactly the omitted proof fields are explicit arguments. -/
def toLegacy (hTable : R.problem.TableCompletenessAssumptions)
    (hCompEnc : ∀ a b, R.compNodeEncode a = R.compNodeEncode b →
      ComputeTable.computeLabelOf a = ComputeTable.computeLabelOf b)
    (hMemEnc : ∀ a b, R.memNodeEncode a = R.memNodeEncode b →
      MemoryTable.memoryLabelOf a = MemoryTable.memoryLabelOf b)
    (hProgCap : R.exec.derivedRequestIO.length + 1 ≤ 2 ^ R.cfg.orbit.h)
    (hMemCap : R.exec.derivedResponseIO.length + 1 ≤ 2 ^ R.cfg.orbit.h) :
    PlusIOSegmentedFamily F K where
  problem := R.problem.toExact hTable
  computeWalkAlpha := R.computeWalkAlpha
  memoryWalkAlpha := R.memoryWalkAlpha
  walkGamma := R.walkGamma
  compNodeWidth := R.compNodeWidth
  compNodeEncode := R.compNodeEncode
  compNodeEncode_labelOf := hCompEnc
  memNodeWidth := R.memNodeWidth
  memNodeEncode := R.memNodeEncode
  memNodeEncode_labelOf := hMemEnc
  requests := R.requests
  responses := R.responses
  outMem := R.outMem
  progIO_capacity := hProgCap
  memIO_capacity := hMemCap

@[simp] theorem ofLegacy_toLegacy
    (hTable : R.problem.TableCompletenessAssumptions)
    (hCompEnc : ∀ a b, R.compNodeEncode a = R.compNodeEncode b →
      ComputeTable.computeLabelOf a = ComputeTable.computeLabelOf b)
    (hMemEnc : ∀ a b, R.memNodeEncode a = R.memNodeEncode b →
      MemoryTable.memoryLabelOf a = MemoryTable.memoryLabelOf b)
    (hProgCap : R.exec.derivedRequestIO.length + 1 ≤ 2 ^ R.cfg.orbit.h)
    (hMemCap : R.exec.derivedResponseIO.length + 1 ≤ 2 ^ R.cfg.orbit.h) :
    ofLegacy (R.toLegacy hTable hCompEnc hMemEnc hProgCap hMemCap) = R := by
  cases R
  rfl

def computeNodeVal
    (t : Nock.Walk.NTree (ComputeTable.State × ComputeTable.DTcomp K)) : K :=
  Nock.Walk.rlc R.walkGamma (R.compNodeEncode t.label)

def memoryNodeVal
    (t : Nock.Walk.NTree (MemoryTable.MState × MemoryTable.DTmem K)) : K :=
  Nock.Walk.rlc R.walkGamma (R.memNodeEncode t.label)

def computeWalkRows :
    List (Nock.Walk.NTree (ComputeTable.State × ComputeTable.DTcomp K)) :=
  Nock.Walk.bfsForest [R.exec.computeTree]

def memoryWalkRows :
    List (Nock.Walk.NTree (MemoryTable.MState × MemoryTable.DTmem K)) :=
  Nock.Walk.bfsForest R.exec.memoryForest

def computeWalkSeed : K :=
  Nock.Walk.curCol R.computeNodeVal R.computeWalkRows 1 * R.computeWalkAlpha

noncomputable def memoryWalkSeed : K :=
  (Nock.Walk.nodeListP
    (Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows) R.cfg.kMem).eval
      R.memoryWalkAlpha

def walkChallengeValuation (α : K) : ℕ → K
  | 0 => α
  | _ => 0

def computeWalkPublicValuation : ℕ → K
  | 0 => R.computeWalkAlpha
  | 1 => R.computeWalkSeed
  | _ => 0

noncomputable def memoryWalkPublicValuation : ℕ → K
  | 0 => R.memoryWalkAlpha ^ R.cfg.kMem
  | 1 => R.memoryWalkSeed
  | _ => 0

noncomputable def computeTableParams : SegmentedRAPParams K :=
  SegmentedRAPParams.ofComputeConfig R.cfg (fun _ => 0)

noncomputable def memoryTableParams : SegmentedRAPParams K :=
  SegmentedRAPParams.ofMemoryConfig R.cfg
    (R.exec.memoryPubAt ⟨0, R.cfg.memRows_pos⟩).lambda (fun _ => 0)

noncomputable def computeWalkParams : SegmentedRAPParams K where
  chalVal := walkChallengeValuation R.computeWalkAlpha
  pubVal := R.computeWalkPublicValuation
  eDeg := R.cfg.eDeg
  hExp := R.cfg.orbit.h
  ω := R.cfg.orbit.ω
  βcoset := R.cfg.orbit.βcoset
  domain := R.cfg.computeDomain
  βcoset_ne_zero := R.cfg.orbit.βcoset_ne_zero
  hExp_pos := R.cfg.orbit_h_pos

noncomputable def memoryWalkParams : SegmentedRAPParams K where
  chalVal := walkChallengeValuation R.memoryWalkAlpha
  pubVal := R.memoryWalkPublicValuation
  eDeg := R.cfg.eDeg
  hExp := R.cfg.orbit.h
  ω := R.cfg.orbit.ω
  βcoset := R.cfg.orbit.βcoset
  domain := R.cfg.memoryDomain
  βcoset_ne_zero := R.cfg.orbit.βcoset_ne_zero
  hExp_pos := R.cfg.orbit_h_pos

noncomputable def ioBaseDomain (records : ℕ) : ConstraintKind → Finset K
  | .row => R.cfg.orbit.rowDomain (records + 1)
  | .transition => R.cfg.orbit.transitionDomain (records + 1) (by omega)
  | .boundary => R.cfg.orbit.boundaryDomain
  | .terminal => R.cfg.orbit.terminalDomain (records + 1) (by omega)

noncomputable def liftFinsetToIO
    (_R : RawPlusIOSegmentedFamily F K) (H : Finset K) : Finset (IOField K) :=
  H.image (algebraMap K (IOField K))

noncomputable def progIOParams : SegmentedRAPParams (IOField K) where
  chalVal := fun _ => 0
  pubVal := fun
    | 0 => R.requests
    | _ => 0
  eDeg := R.cfg.eDeg
  hExp := R.cfg.orbit.h
  ω := algebraMap K (IOField K) R.cfg.orbit.ω
  βcoset := algebraMap K (IOField K) R.cfg.orbit.βcoset
  domain := fun kind => PlusIOSegmentedFamily.liftFinsetToIO
    (PlusIOSegmentedFamily.ioBaseDomain R.cfg.orbit
      R.exec.derivedRequestIO.length kind)
  βcoset_ne_zero := by
    intro h
    exact R.cfg.orbit.βcoset_ne_zero
      ((algebraMap K (IOField K)).injective (by simpa using h))
  hExp_pos := R.cfg.orbit_h_pos

noncomputable def memIOParams : SegmentedRAPParams (IOField K) where
  chalVal := fun _ => 0
  pubVal := fun
    | 0 => R.responses
    | 1 => R.outMem
    | _ => 0
  eDeg := R.cfg.eDeg
  hExp := R.cfg.orbit.h
  ω := algebraMap K (IOField K) R.cfg.orbit.ω
  βcoset := algebraMap K (IOField K) R.cfg.orbit.βcoset
  domain := fun kind => PlusIOSegmentedFamily.liftFinsetToIO
    (PlusIOSegmentedFamily.ioBaseDomain R.cfg.orbit
      R.exec.derivedResponseIO.length kind)
  βcoset_ne_zero := by
    intro h
    exact R.cfg.orbit.βcoset_ne_zero
      ((algebraMap K (IOField K)).injective (by simpa using h))
  hExp_pos := R.cfg.orbit_h_pos

noncomputable def computeTableRAP (kind : ConstraintKind) : RAP K :=
  R.computeTableParams.rap Trans.computeAIRchained kind

noncomputable def memoryTableRAP (kind : ConstraintKind) : RAP K :=
  R.memoryTableParams.rap (Trans.memoryAIRchained (K := K)) kind

noncomputable def computeWalkRAP (kind : ConstraintKind) : RAP K :=
  R.computeWalkParams.rap Trans.walkAIR kind

noncomputable def memoryWalkRAP (kind : ConstraintKind) : RAP K :=
  R.memoryWalkParams.rap Trans.walkAIR kind

noncomputable def computeIORAP (kind : ConstraintKind) : RAP (IOField K) :=
  R.progIOParams.rap Trans.ioProgAIR kind

noncomputable def memoryIORAP (kind : ConstraintKind) : RAP (IOField K) :=
  R.memIOParams.rap Trans.ioMemAIR kind

end RawPlusIOSegmentedFamily

/-! ## Raw data and six direct trace encoders -/

structure RawTableArrays (R : RawPlusIOSegmentedFamily F K) where
  compute : Fin R.cfg.compRows → ComputeTable.Extra K
  memory : Fin R.cfg.memRows → K

structure RawWalkArrays (K : Type) where
  computeLn : ℕ → K
  computeCount : ℕ → K
  computeAcc : ℕ → K
  memoryLn : ℕ → K
  memoryCount : ℕ → K
  memoryAcc : ℕ → K

structure RawIOArrays (R : RawPlusIOSegmentedFamily F K) (p : ℕ) where
  multiplicity : Fin R.exec.derivedResponseIO.length → ZMod p
  progAcc : ℕ → IOField K
  memAcc : ℕ → IOField K

/-- The truly raw prover message: every field is data. -/
structure RawMessage (R : RawPlusIOSegmentedFamily F K) (p : ℕ) where
  tables : RawTableArrays R
  walks : RawWalkArrays K
  io : RawIOArrays R p

namespace RawMessage

variable {R : RawPlusIOSegmentedFamily F K}

noncomputable def computeTableTrace (M : RawMessage R p) :
    Fin Trans.computeAIRchained.numTraceCols → K[X] :=
  encodeComputeTrace
    (fun i => computeEnvFull R.cfg.challenges.computeInputs
      (ComputeTable.opSel (R.exec.computePubAt i).state)
      (R.exec.computePubAt i) (R.exec.computeDecAt i) (M.tables.compute i))
    R.cfg.compNodes

noncomputable def memoryTableTrace (M : RawMessage R p) :
    Fin (Trans.memoryAIRchained (K := K)).numTraceCols → K[X] :=
  encodeMemoryTrace
    (fun i => memoryEnvFull R.cfg.challenges.memoryInputs
      (MemoryTable.opSel (R.exec.memoryPubAt i).st)
      (R.exec.memoryPubAt i) (M.tables.memory i))
    R.cfg.memNodes

noncomputable def computeWalkTrace (M : RawMessage R p) :
    Fin Trans.walkAIR.numTraceCols → K[X] :=
  encodeEnvTrace
    (fun i : Fin R.cfg.compRows =>
      Trans.walkRowEnv
        (Nock.Walk.curCol R.computeNodeVal R.computeWalkRows)
        (Nock.Walk.chldCol R.computeNodeVal R.computeWalkRows)
        (Nock.Walk.foCol R.computeWalkRows)
        M.walks.computeLn M.walks.computeCount M.walks.computeAcc
        R.computeWalkAlpha R.computeWalkSeed R.computeWalkAlpha ((i : ℕ) + 1))
    R.cfg.compNodes

noncomputable def memoryWalkTrace (M : RawMessage R p) :
    Fin Trans.walkAIR.numTraceCols → K[X] :=
  encodeEnvTrace
    (fun i : Fin R.cfg.memRows =>
      Trans.walkRowEnv
        (Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows)
        (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
        (Nock.Walk.foCol R.memoryWalkRows)
        M.walks.memoryLn M.walks.memoryCount M.walks.memoryAcc
        R.memoryWalkAlpha R.memoryWalkSeed
        (R.memoryWalkAlpha ^ R.cfg.kMem) ((i : ℕ) + 1))
    R.cfg.memNodes

noncomputable def computeIOTrace (M : RawMessage R p) :
    Fin Trans.ioProgAIR.numTraceCols → (IOField K)[X] :=
  encodeEnvTrace
    (fun i : Fin (R.exec.derivedRequestIO.length + 1) =>
      Trans.ioProgRowEnv
        (fun q => SetEq.RLC (IO.listExt R.exec.derivedRequestIO q))
        M.io.progAcc R.requests i)
    (fun i => algebraMap K (IOField K) (R.cfg.orbit.orbitPoint i))

noncomputable def memoryIOTrace (M : RawMessage R p) :
    Fin Trans.ioMemAIR.numTraceCols → (IOField K)[X] :=
  encodeEnvTrace
    (fun i : Fin (R.exec.derivedResponseIO.length + 1) =>
      Trans.ioMemRowEnv
        (fun q => SetEq.RLC (IO.listExt R.exec.derivedResponseIO q))
        (IO.castμ (𝔽 := K) M.io.multiplicity)
        M.io.memAcc R.responses R.outMem i)
    (fun i => algebraMap K (IOField K) (R.cfg.orbit.orbitPoint i))

/-! ## Raw acceptance -/

/-- Cheap deterministic alignment omitted by the table traces themselves.  Every active derived
BFS row must carry the public state and the unique configured table inputs used by its table AIR. -/
def RowAlignmentGates : Prop :=
  (∀ i : Fin R.cfg.compRows,
    let row := R.exec.computeRowAt i
    row.1 = row.2.2.1.state ∧
      row.2.1 = R.cfg.challenges.computeInputs) ∧
  (∀ i : Fin R.cfg.memRows,
    let row := R.exec.memoryRowAt i
    row.1 = row.2.2.st ∧
      row.2.1 = R.cfg.challenges.memoryInputs)

def VerifierGates (claim : P8PublicClaim) (ω : JointCoins K)
    (M : RawMessage R p) : Prop :=
  nprSeed ω ≠ 0 ∧
    R.cfg.challenges.z = nprSeed ω ∧
    R.computeWalkAlpha = alphaC ω ∧
    R.walkGamma = gamma ω ∧
    R.memoryWalkAlpha = alphaM ω ∧
    RowAlignmentGates (R := R) ∧
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
    R.exec.derivedResponseIO.Nodup

def SixRAPSatisfy (M : RawMessage R p) : Prop :=
  (∀ kind, (R.computeTableRAP kind).Satisfies M.computeTableTrace) ∧
    (∀ kind, (R.memoryTableRAP kind).Satisfies M.memoryTableTrace) ∧
    (∀ kind, (R.computeWalkRAP kind).Satisfies M.computeWalkTrace) ∧
    (∀ kind, (R.memoryWalkRAP kind).Satisfies M.memoryWalkTrace) ∧
    (∀ kind, (R.computeIORAP kind).Satisfies M.computeIOTrace) ∧
    (∀ kind, (R.memoryIORAP kind).Satisfies M.memoryIOTrace)

/-- Exactly the verifier gates and 24 segmented RAP evaluations. -/
def Accepts (claim : P8PublicClaim) (ω : JointCoins K) (M : RawMessage R p) : Prop :=
  M.VerifierGates claim ω ∧ M.SixRAPSatisfy

theorem rawAccepts_iff_sixRAP_and_gates
    (claim : P8PublicClaim) (ω : JointCoins K) (M : RawMessage R p) :
    M.Accepts claim ω ↔ M.VerifierGates claim ω ∧ M.SixRAPSatisfy :=
  Iff.rfl

/-- Raw acceptance binds both encoder payloads to the production encoders under the one permitted
external field-family hypothesis.  No prover-supplied injectivity proof appears in this statement. -/
theorem canonicalNodeEncoders_of_accepts
    {claim : P8PublicClaim} {ω : JointCoins K}
    (M : RawMessage R p) (hchar : NodeEncoding.StateTagChar K)
    (h : M.Accepts claim ω) :
    R.compNodeWidth = NodeEncoding.computeNodeWidth ∧
      HEq R.compNodeEncode (NodeEncoding.computeNodeEncode hchar) ∧
      R.memNodeWidth = NodeEncoding.memoryNodeWidth ∧
      HEq R.memNodeEncode (NodeEncoding.memoryNodeEncode hchar) := by
  rcases h.1 with
    ⟨_, _, _, _, _, _, henc, _, _, _, _, _, _, _, _, _, _⟩
  exact ⟨henc.1, henc.2.1 hchar, henc.2.2.1, henc.2.2.2 hchar⟩

/-! ## WF-free table soundness -/

theorem freeSelectorChar_of_stateTagChar (hchar : NodeEncoding.StateTagChar K) :
    ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1 := by
  intro n hn heq
  apply hchar hn (by norm_num)
  simpa using heq

theorem memoryFreeSelectorChar_of_stateTagChar (hchar : NodeEncoding.StateTagChar K) :
    ∀ n : ℕ, n ≤ 4 → (n : K) = 1 → n = 1 := by
  intro n hn
  exact freeSelectorChar_of_stateTagChar hchar n (by omega)

/-- Forward compute-table soundness.  WF is absent; `z ≠ 0` is extracted from the AIR gate. -/
theorem computeTable_sound_wfFree (M : RawMessage R p)
    (hchar : NodeEncoding.StateTagChar K)
    (hrap : ∀ kind, (R.computeTableRAP kind).Satisfies M.computeTableTrace) :
    ((∀ i, ComputeTable.Vcomp R.cfg.challenges.computeInputs
        (R.exec.computePubAt i) (R.exec.computeDecAt i)) ∧
      ∀ i : Fin R.cfg.compRows, ∀ hi : (i : ℕ) + 1 < R.cfg.compRows,
        (R.exec.computePubAt i).ln =
          (R.exec.computePubAt ⟨(i : ℕ) + 1, hi⟩).ln_prev) ∧
      R.cfg.challenges.z ≠ 0 := by
  let env := fun i : Fin R.cfg.compRows =>
    computeEnvFull R.cfg.challenges.computeInputs
      (ComputeTable.opSel (R.exec.computePubAt i).state)
      (R.exec.computePubAt i) (R.exec.computeDecAt i) (M.tables.compute i)
  have hrowRAP :=
    (computeRowSegment_iff R.cfg M.computeTableTrace).1 (hrap .row)
  have hrows :
      ∀ i, ∀ c ∈ computeAIR.constraints, c.expr.eval (env i) = 0 := by
    apply (satisfies_iff_perRow_env env R.cfg.compNodes R.cfg.compNodes_injective
      R.cfg.challenges.computeValuation R.cfg.eDeg R.cfg.orbit.h
      R.cfg.orbit.ω R.cfg.orbit.βcoset R.cfg.orbit.βcoset_ne_zero
      R.cfg.orbit_h_pos (fun _ => rfl) (fun _ => rfl)).1
    simpa [env, computeTableTrace] using hrowRAP
  have hdecoded : ∀ i,
      ComputeTable.Vcomp R.cfg.challenges.computeInputs
        (R.exec.computePubAt i) (R.exec.computeDecAt i) ∧
      R.cfg.challenges.z ≠ 0 := by
    intro i
    obtain ⟨s, hs, hlocal, hz⟩ :=
      computeAIR_sound_free R.cfg.challenges.computeInputs
        (ComputeTable.opSel (R.exec.computePubAt i).state)
        (R.exec.computePubAt i) (R.exec.computeDecAt i) (M.tables.compute i)
        (freeSelectorChar_of_stateTagChar hchar) (hrows i)
    have hstate : s = (R.exec.computePubAt i).state := by
      by_contra hne
      have he := congrFun hs (R.exec.computePubAt i).state
      simp [ComputeTable.opSel, Ne.symm hne] at he
    subst s
    exact
      ⟨ComputeTable.equiv_compute_sound _ _ _
        ⟨M.tables.compute i, by simpa using hlocal⟩, hz⟩
  refine ⟨⟨fun i => (hdecoded i).1, ?_⟩, (hdecoded ⟨0, R.cfg.compRows_pos⟩).2⟩
  exact (computeTransitionSegment_iff R.cfg R.exec.computePubAt
    R.exec.computeDecAt M.tables.compute).1 (hrap .transition)

/-- Forward memory-table soundness, also WF-free and deriving nonzero seed from the AIR. -/
theorem memoryTable_sound_wfFree (M : RawMessage R p)
    (hchar : NodeEncoding.StateTagChar K)
    (hlam : ∀ i, (R.exec.memoryPubAt i).lambda = R.cfg.challenges.lam)
    (hrap : ∀ kind, (R.memoryTableRAP kind).Satisfies M.memoryTableTrace) :
    ((∀ i, MemoryTable.Vmem R.cfg.challenges.memoryInputs
        (R.exec.memoryPubAt i)) ∧
      (∀ i : Fin R.cfg.memRows, ∀ hi : (i : ℕ) + 1 < R.cfg.memRows,
        (R.exec.memoryPubAt i).icur =
          (R.exec.memoryPubAt ⟨(i : ℕ) + 1, hi⟩).ipre) ∧
      (R.exec.memoryPubAt ⟨0, R.cfg.memRows_pos⟩).pt.counts = 0 ∧
      (R.exec.memoryPubAt ⟨0, R.cfg.memRows_pos⟩).pt.indicator = 0 ∧
      (R.exec.memoryPubAt ⟨0, R.cfg.memRows_pos⟩).ipre = 0 ∧
      (R.exec.memoryPubAt
        (R.cfg.orbit.lastIndex R.cfg.memRows R.cfg.memRows_pos)).icur = 0) ∧
      R.cfg.challenges.z ≠ 0 := by
  let env := fun i : Fin R.cfg.memRows =>
    memoryEnvFull R.cfg.challenges.memoryInputs
      (MemoryTable.opSel (R.exec.memoryPubAt i).st)
      (R.exec.memoryPubAt i) (M.tables.memory i)
  have hrowRAP :=
    (memoryRowSegment_iff R.cfg R.exec.memoryPubAt M.memoryTableTrace).1 (hrap .row)
  have hrows :
      ∀ i, ∀ c ∈ (memoryAIR (K := K)).constraints, c.expr.eval (env i) = 0 := by
    apply (satisfies_iff_perRow_env_mem env R.cfg.memNodes R.cfg.memNodes_injective
      (R.cfg.challenges.memoryChalVal
        (R.exec.memoryPubAt ⟨0, R.cfg.memRows_pos⟩).lambda)
      R.cfg.eDeg R.cfg.orbit.h
      R.cfg.orbit.ω R.cfg.orbit.βcoset R.cfg.orbit.βcoset_ne_zero
      R.cfg.orbit_h_pos
      (by
        intro k
        funext j
        simp [env, memoryEnvFull, ChallengeVector.memoryChalVal,
          ChallengeVector.memoryInputs, hlam k, hlam ⟨0, R.cfg.memRows_pos⟩]
        rfl)
      (fun _ => rfl)).1
    simpa [env, memoryTableTrace] using hrowRAP
  have hdecoded : ∀ i,
      MemoryTable.Vmem R.cfg.challenges.memoryInputs (R.exec.memoryPubAt i) ∧
      R.cfg.challenges.z ≠ 0 := by
    intro i
    obtain ⟨s, hs, hlocal, hz⟩ :=
      memoryAIR_sound_free R.cfg.challenges.memoryInputs
        (MemoryTable.opSel (R.exec.memoryPubAt i).st)
        (R.exec.memoryPubAt i) (M.tables.memory i)
        (memoryFreeSelectorChar_of_stateTagChar hchar) (hrows i)
    have hstate : s = (R.exec.memoryPubAt i).st := by
      by_contra hne
      have he := congrFun hs (R.exec.memoryPubAt i).st
      simp [MemoryTable.opSel, Ne.symm hne] at he
    subst s
    exact
      ⟨MemoryTable.equiv_mem_sound _ _
        ⟨M.tables.memory i, by simpa using hlocal⟩, hz⟩
  have htrans := (memoryTransitionSegment_iff R.cfg R.exec.memoryPubAt
    M.tables.memory).1 (hrap .transition)
  have hboundary := (memoryBoundarySegment_iff R.cfg R.exec.memoryPubAt
    M.tables.memory).1 (hrap .boundary)
  have hterminal := (memoryTerminalSegment_iff R.cfg R.exec.memoryPubAt
    M.tables.memory).1 (hrap .terminal)
  exact ⟨⟨fun i => (hdecoded i).1, htrans, hboundary.1, hboundary.2.1,
    hboundary.2.2, hterminal⟩, (hdecoded ⟨0, R.cfg.memRows_pos⟩).2⟩

/-! ## Canonical row acceptance from raw table soundness and alignment -/

/-- The compute AIR checks the configured inputs and the public/Dec projections.  The deterministic
alignment gate supplies exactly the two fields omitted from that trace, yielding the canonical
`ExactExecution.ComputeRowAccepted` predicate on the authoritative BFS row. -/
theorem computeRowAccepted_of_accepts {claim : P8PublicClaim} {ω : JointCoins K}
    (M : RawMessage R p) (hchar : NodeEncoding.StateTagChar K)
    (h : M.Accepts claim ω) :
    ∀ i : Fin R.cfg.compRows,
      ExactExecution.ComputeRowAccepted R.cfg (R.exec.computeRowAt i) := by
  have htable := M.computeTable_sound_wfFree hchar h.2.1
  rcases h.1 with
    ⟨_, _, _, _, _, halign, _, _, _, _, _, _, _, _, _, _, _⟩
  intro i
  have ha := halign.1 i
  refine ⟨ha.1, ha.2, ?_⟩
  rw [ha.2]
  simpa [ExactExecution.computePubAt, ExactExecution.computeDecAt] using htable.1.1 i

/-- Memory analogue of `computeRowAccepted_of_accepts`. -/
theorem memoryRowAccepted_of_accepts {claim : P8PublicClaim} {ω : JointCoins K}
    (M : RawMessage R p) (hchar : NodeEncoding.StateTagChar K)
    (hlam : ∀ i, (R.exec.memoryPubAt i).lambda = R.cfg.challenges.lam)
    (h : M.Accepts claim ω) :
    ∀ i : Fin R.cfg.memRows,
      ExactExecution.MemoryRowAccepted R.cfg (R.exec.memoryRowAt i) := by
  have htable := M.memoryTable_sound_wfFree hchar hlam h.2.2.1
  rcases h.1 with
    ⟨_, _, _, _, _, halign, _, _, _, _, _, _, _, _, _, _, _⟩
  intro i
  have ha := halign.2 i
  refine ⟨ha.1, ha.2, ?_, hlam i⟩
  rw [ha.2]
  simpa [ExactExecution.memoryPubAt] using htable.1.1 i

/-- Every authoritative compute BFS row satisfies the canonical fixed-row recognizer. -/
theorem computeRowsAccepted_of_accepts {claim : P8PublicClaim} {ω : JointCoins K}
    (M : RawMessage R p) (hchar : NodeEncoding.StateTagChar K)
    (h : M.Accepts claim ω) :
    R.exec.ComputeRowsAccepted := by
  apply (ExactExecution.computeRowsAccepted_iff R.exec).2
  intro row hrow
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hrow
  have hacc := M.computeRowAccepted_of_accepts hchar h
    (Fin.cast R.exec.computeRows_length i)
  rw [R.exec.computeRowAt_cast] at hacc
  rw [← hi]
  exact hacc

/-- Every authoritative memory BFS row satisfies the canonical fixed-row recognizer. -/
theorem memoryRowsAccepted_of_accepts {claim : P8PublicClaim} {ω : JointCoins K}
    (M : RawMessage R p) (hchar : NodeEncoding.StateTagChar K)
    (hlam : ∀ i, (R.exec.memoryPubAt i).lambda = R.cfg.challenges.lam)
    (h : M.Accepts claim ω) :
    R.exec.MemoryRowsAccepted := by
  apply (ExactExecution.memoryRowsAccepted_iff R.exec).2
  intro row hrow
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hrow
  have hacc := M.memoryRowAccepted_of_accepts hchar hlam h
    (Fin.cast R.exec.memoryRows_length i)
  rw [R.exec.memoryRowAt_cast] at hacc
  rw [← hi]
  exact hacc

/-! ## Raw walk and IO soundness -/

def ComputeWalkCertificate (M : RawMessage R p) : Prop :=
  Nock.Walk.WalkSat
    (Nock.Walk.curCol R.computeNodeVal R.computeWalkRows)
    (Nock.Walk.chldCol R.computeNodeVal R.computeWalkRows)
    (Nock.Walk.foCol R.computeWalkRows)
    M.walks.computeLn M.walks.computeCount M.walks.computeAcc
    R.computeWalkAlpha R.computeWalkSeed R.computeWalkAlpha R.cfg.compRows ∧
  M.walks.computeAcc R.cfg.compRows = 0

def MemoryWalkCertificate (M : RawMessage R p) : Prop :=
  Nock.Walk.WalkSat
    (Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows)
    (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
    (Nock.Walk.foCol R.memoryWalkRows)
    M.walks.memoryLn M.walks.memoryCount M.walks.memoryAcc
    R.memoryWalkAlpha R.memoryWalkSeed
    (R.memoryWalkAlpha ^ R.cfg.kMem) R.cfg.memRows ∧
  M.walks.memoryAcc R.cfg.memRows = 0

theorem computeWalkRAP_wholeTrace_iff (M : RawMessage R p) :
    (∀ kind, (R.computeWalkRAP kind).Satisfies M.computeWalkTrace) ↔
      M.ComputeWalkCertificate := by
  have hchal :
      RawPlusIOSegmentedFamily.walkChallengeValuation R.computeWalkAlpha =
        (Trans.walkRowEnv
          (Nock.Walk.curCol R.computeNodeVal R.computeWalkRows)
          (Nock.Walk.chldCol R.computeNodeVal R.computeWalkRows)
          (Nock.Walk.foCol R.computeWalkRows)
          M.walks.computeLn M.walks.computeCount M.walks.computeAcc
          R.computeWalkAlpha R.computeWalkSeed R.computeWalkAlpha 1).chal := by
    funext j
    cases j <;> rfl
  have hpub :
      R.computeWalkPublicValuation =
        (Trans.walkRowEnv
          (Nock.Walk.curCol R.computeNodeVal R.computeWalkRows)
          (Nock.Walk.chldCol R.computeNodeVal R.computeWalkRows)
          (Nock.Walk.foCol R.computeWalkRows)
          M.walks.computeLn M.walks.computeCount M.walks.computeAcc
          R.computeWalkAlpha R.computeWalkSeed R.computeWalkAlpha 1).pub := by
    funext j
    cases j with
    | zero => rfl
    | succ j => cases j <;> rfl
  simp only [RawPlusIOSegmentedFamily.computeWalkRAP,
    RawPlusIOSegmentedFamily.computeWalkParams, SegmentedRAPParams.rap,
    computeWalkTrace, ComputeWalkCertificate]
  rw [hchal, hpub]
  have hg := walkSegmentedRAP_wholeTrace_iff
    R.cfg.orbit R.cfg.compRows_pos R.cfg.compRows_le R.cfg.orbit_h_pos R.cfg.eDeg
    (Nock.Walk.curCol R.computeNodeVal R.computeWalkRows)
    (Nock.Walk.chldCol R.computeNodeVal R.computeWalkRows)
    (Nock.Walk.foCol R.computeWalkRows)
    M.walks.computeLn M.walks.computeCount M.walks.computeAcc
    R.computeWalkAlpha R.computeWalkSeed R.computeWalkAlpha
    R.cfg.compNodes R.cfg.compNodes_injective R.cfg.compNodes_eq_orbitPoint
  constructor
  · intro h
    apply hg.mp
    intro kind
    have hk := h kind
    erw [airToRAP_satisfies_iff] at hk ⊢
    intro x hx c hc
    exact hk x (by cases kind <;> exact hx) c hc
  · intro h kind
    have hk := hg.mpr h kind
    erw [airToRAP_satisfies_iff] at hk ⊢
    intro x hx c hc
    exact hk x (by cases kind <;> exact hx) c hc

theorem memoryWalkRAP_wholeTrace_iff (M : RawMessage R p) :
    (∀ kind, (R.memoryWalkRAP kind).Satisfies M.memoryWalkTrace) ↔
      M.MemoryWalkCertificate := by
  have hchal :
      RawPlusIOSegmentedFamily.walkChallengeValuation R.memoryWalkAlpha =
        (Trans.walkRowEnv
          (Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows)
          (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
          (Nock.Walk.foCol R.memoryWalkRows)
          M.walks.memoryLn M.walks.memoryCount M.walks.memoryAcc
          R.memoryWalkAlpha R.memoryWalkSeed
          (R.memoryWalkAlpha ^ R.cfg.kMem) 1).chal := by
    funext j
    cases j <;> rfl
  have hpub :
      R.memoryWalkPublicValuation =
        (Trans.walkRowEnv
          (Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows)
          (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
          (Nock.Walk.foCol R.memoryWalkRows)
          M.walks.memoryLn M.walks.memoryCount M.walks.memoryAcc
          R.memoryWalkAlpha R.memoryWalkSeed
          (R.memoryWalkAlpha ^ R.cfg.kMem) 1).pub := by
    funext j
    cases j with
    | zero => rfl
    | succ j => cases j <;> rfl
  simp only [RawPlusIOSegmentedFamily.memoryWalkRAP,
    RawPlusIOSegmentedFamily.memoryWalkParams, SegmentedRAPParams.rap,
    memoryWalkTrace, MemoryWalkCertificate]
  rw [hchal, hpub]
  have hg := walkSegmentedRAP_wholeTrace_iff
    R.cfg.orbit R.cfg.memRows_pos R.cfg.memRows_le R.cfg.orbit_h_pos R.cfg.eDeg
    (Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows)
    (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
    (Nock.Walk.foCol R.memoryWalkRows)
    M.walks.memoryLn M.walks.memoryCount M.walks.memoryAcc
    R.memoryWalkAlpha R.memoryWalkSeed (R.memoryWalkAlpha ^ R.cfg.kMem)
    R.cfg.memNodes R.cfg.memNodes_injective R.cfg.memNodes_eq_orbitPoint
  constructor
  · intro h
    apply hg.mp
    intro kind
    have hk := h kind
    erw [airToRAP_satisfies_iff] at hk ⊢
    intro x hx c hc
    exact hk x (by cases kind <;> exact hx) c hc
  · intro h kind
    have hk := hg.mpr h kind
    erw [airToRAP_satisfies_iff] at hk ⊢
    intro x hx c hc
    exact hk x (by cases kind <;> exact hx) c hc

theorem computeIORAP_wholeTrace_iff (M : RawMessage R p)
    (hcap : R.exec.derivedRequestIO.length + 1 ≤ 2 ^ R.cfg.orbit.h) :
    (∀ kind, (R.computeIORAP kind).Satisfies M.computeIOTrace) ↔
      IO.ProgIOSat
        (fun i => SetEq.RLC (IO.listExt R.exec.derivedRequestIO i))
        M.io.progAcc R.requests R.exec.derivedRequestIO.length := by
  let a := fun i => SetEq.RLC (IO.listExt R.exec.derivedRequestIO i)
  let rows := fun i : Fin (R.exec.derivedRequestIO.length + 1) =>
    Trans.ioProgRowEnv a M.io.progAcc R.requests i
  have hchal : R.progIOParams.chalVal = (rows ⟨0, by omega⟩).chal := by
    funext j
    rfl
  have hpub : R.progIOParams.pubVal = (rows ⟨0, by omega⟩).pub := by
    funext j
    cases j <;> rfl
  simp only [RawPlusIOSegmentedFamily.computeIORAP, SegmentedRAPParams.rap,
    computeIOTrace]
  rw [hchal, hpub]
  have hg := ioProgSegmentedRAP_wholeTrace_iff R.cfg.orbit
    R.exec.derivedRequestIO.length hcap R.cfg.orbit_h_pos R.cfg.eDeg
    a M.io.progAcc R.requests
  constructor
  · intro h
    apply hg.mp
    intro kind
    have hk := h kind
    erw [airToRAP_satisfies_iff] at hk ⊢
    exact hk
  · intro h kind
    have hk := hg.mpr h kind
    erw [airToRAP_satisfies_iff] at hk ⊢
    exact hk

theorem memoryIORAP_wholeTrace_iff (M : RawMessage R p)
    (hcap : R.exec.derivedResponseIO.length + 1 ≤ 2 ^ R.cfg.orbit.h) :
    (∀ kind, (R.memoryIORAP kind).Satisfies M.memoryIOTrace) ↔
      IO.MemIOSat
        (fun i => SetEq.RLC (IO.listExt R.exec.derivedResponseIO i))
        (IO.castμ (𝔽 := K) M.io.multiplicity)
        M.io.memAcc R.responses R.outMem R.exec.derivedResponseIO.length := by
  let b := fun i => SetEq.RLC (IO.listExt R.exec.derivedResponseIO i)
  let μ := IO.castμ (𝔽 := K) M.io.multiplicity
  let rows := fun i : Fin (R.exec.derivedResponseIO.length + 1) =>
    Trans.ioMemRowEnv b μ M.io.memAcc R.responses R.outMem i
  have hchal : R.memIOParams.chalVal = (rows ⟨0, by omega⟩).chal := by
    funext j
    rfl
  have hpub : R.memIOParams.pubVal = (rows ⟨0, by omega⟩).pub := by
    funext j
    cases j with
    | zero => rfl
    | succ j => cases j <;> rfl
  simp only [RawPlusIOSegmentedFamily.memoryIORAP, SegmentedRAPParams.rap,
    memoryIOTrace]
  rw [hchal, hpub]
  have hg := ioMemSegmentedRAP_wholeTrace_iff R.cfg.orbit
    R.exec.derivedResponseIO.length hcap R.cfg.orbit_h_pos R.cfg.eDeg
    b μ M.io.memAcc R.responses R.outMem
  constructor
  · intro h
    apply hg.mp
    intro kind
    have hk := h kind
    erw [airToRAP_satisfies_iff] at hk ⊢
    exact hk
  · intro h kind
    have hk := hg.mpr h kind
    erw [airToRAP_satisfies_iff] at hk ⊢
    exact hk

/-- Raw acceptance gives `LIO` with only the characteristic and two capacity conditions added. -/
theorem lio_of_accepts {claim : P8PublicClaim} {ω : JointCoins K}
    (M : RawMessage R p) (hKp : R.cfg.Ksz < p)
    (hProgCap : R.exec.derivedRequestIO.length + 1 ≤ 2 ^ R.cfg.orbit.h)
    (hMemCap : R.exec.derivedResponseIO.length + 1 ≤ 2 ^ R.cfg.orbit.h)
    (h : M.Accepts claim ω) :
    IO.LIO R.cfg.Ksz R.exec.derivedRequestIO R.exec.derivedResponseIO := by
  rcases h.1 with
    ⟨_, _, _, _, _, _, _, _, _, _, hend, hclose, hmul, hKreq, hreqnd, hKresp, hrespnd⟩
  apply (IO.io_result_LIO R.cfg.Ksz hKp R.exec.derivedRequestIO
    R.exec.derivedResponseIO hKreq hKresp hreqnd hrespnd).1
  exact ⟨M.io.multiplicity, M.io.progAcc, M.io.memAcc,
    R.requests, R.responses, R.outMem, hmul,
    (M.computeIORAP_wholeTrace_iff hProgCap).1 h.2.2.2.2.2.1,
    (M.memoryIORAP_wholeTrace_iff hMemCap).1 h.2.2.2.2.2.2,
    hend, hclose⟩

/-! ## Legacy erasure and completeness bridges -/

def ofLegacy {S : PlusIOSegmentedFamily F K}
    (A : PlusIOSameExecutionAssignment S p) :
    RawMessage (RawPlusIOSegmentedFamily.ofLegacy S) p where
  tables := { compute := A.computeTableAux, memory := A.memoryTableAux }
  walks :=
    { computeLn := A.computeWalk.ln
      computeCount := A.computeWalk.count
      computeAcc := A.computeWalk.acc
      memoryLn := A.memoryWalk.ln
      memoryCount := A.memoryWalk.count
      memoryAcc := A.memoryWalk.acc }
  io :=
    { multiplicity := A.exactIO.multiplicity
      progAcc := A.exactIO.progAcc
      memAcc := A.exactIO.memAcc }

@[simp] theorem ofLegacy_computeTableTrace {S : PlusIOSegmentedFamily F K}
    (A : PlusIOSameExecutionAssignment S p) :
    (ofLegacy A).computeTableTrace = A.computeTableTrace := rfl

@[simp] theorem ofLegacy_memoryTableTrace {S : PlusIOSegmentedFamily F K}
    (A : PlusIOSameExecutionAssignment S p) :
    (ofLegacy A).memoryTableTrace = A.memoryTableTrace := rfl

@[simp] theorem ofLegacy_computeWalkTrace {S : PlusIOSegmentedFamily F K}
    (A : PlusIOSameExecutionAssignment S p) :
    (ofLegacy A).computeWalkTrace = A.computeWalkTrace := rfl

@[simp] theorem ofLegacy_memoryWalkTrace {S : PlusIOSegmentedFamily F K}
    (A : PlusIOSameExecutionAssignment S p) :
    (ofLegacy A).memoryWalkTrace = A.memoryWalkTrace := rfl

@[simp] theorem ofLegacy_computeIOTrace {S : PlusIOSegmentedFamily F K}
    (A : PlusIOSameExecutionAssignment S p) :
    (ofLegacy A).computeIOTrace = A.computeIOTrace := rfl

@[simp] theorem ofLegacy_memoryIOTrace {S : PlusIOSegmentedFamily F K}
    (A : PlusIOSameExecutionAssignment S p) :
    (ofLegacy A).memoryIOTrace = A.memoryIOTrace := rfl

theorem sixRAPSatisfy_of_legacy {S : PlusIOSegmentedFamily F K}
    (A : PlusIOSameExecutionAssignment S p) (hA : A.Satisfies) :
    (ofLegacy A).SixRAPSatisfy := by
  have hs := (PlusIOSameExecutionAssignment.satisfies_iff_six_families A).1 hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro kind
    change (S.computeTableRAP kind).Satisfies A.computeTableTrace
    exact hs.1 kind
  · intro kind
    change (S.memoryTableRAP kind).Satisfies A.memoryTableTrace
    exact hs.2.1 kind
  · intro kind
    change (S.computeWalkRAP kind).Satisfies A.computeWalkTrace
    exact hs.2.2.1 kind
  · intro kind
    change (S.memoryWalkRAP kind).Satisfies A.memoryWalkTrace
    exact hs.2.2.2.1 kind
  · intro kind
    change (S.computeIORAP kind).Satisfies A.computeIOTrace
    exact hs.2.2.2.2.1 kind
  · intro kind
    change (S.memoryIORAP kind).Satisfies A.memoryIOTrace
    exact hs.2.2.2.2.2 kind

/-- Lift raw data back to the legacy assignment only after supplying the proof obligations omitted
from the raw family and the IO facts derived from raw RAP acceptance. -/
def toLegacyAssignment (M : RawMessage R p)
    (hTable : R.problem.TableCompletenessAssumptions)
    (hCompEnc : ∀ a b, R.compNodeEncode a = R.compNodeEncode b →
      ComputeTable.computeLabelOf a = ComputeTable.computeLabelOf b)
    (hMemEnc : ∀ a b, R.memNodeEncode a = R.memNodeEncode b →
      MemoryTable.memoryLabelOf a = MemoryTable.memoryLabelOf b)
    (hProgCap : R.exec.derivedRequestIO.length + 1 ≤ 2 ^ R.cfg.orbit.h)
    (hMemCap : R.exec.derivedResponseIO.length + 1 ≤ 2 ^ R.cfg.orbit.h)
    (hprog : ∀ kind, (R.computeIORAP kind).Satisfies M.computeIOTrace)
    (hmem : ∀ kind, (R.memoryIORAP kind).Satisfies M.memoryIOTrace)
    (hmul : ∀ j, M.io.multiplicity j ≠ 0)
    (hend : R.requests = R.responses) (hclose : R.outMem = 0) :
    PlusIOSameExecutionAssignment
      (R.toLegacy hTable hCompEnc hMemEnc hProgCap hMemCap) p where
  computeTableAux := M.tables.compute
  memoryTableAux := M.tables.memory
  computeWalk :=
    { ln := M.walks.computeLn
      count := M.walks.computeCount
      acc := M.walks.computeAcc }
  memoryWalk :=
    { ln := M.walks.memoryLn
      count := M.walks.memoryCount
      acc := M.walks.memoryAcc }
  exactIO :=
    { multiplicity := M.io.multiplicity
      progAcc := M.io.progAcc
      memAcc := M.io.memAcc
      multiplicity_ne_zero := hmul
      progSat := (M.computeIORAP_wholeTrace_iff hProgCap).1 hprog
      memSat := (M.memoryIORAP_wholeTrace_iff hMemCap).1 hmem
      endpoints_agree := hend
      memory_closes := hclose }

/-- The legacy lift forgets back to the original raw message. -/
theorem ofLegacy_toLegacyAssignment (M : RawMessage R p)
    (hTable : R.problem.TableCompletenessAssumptions)
    (hCompEnc : ∀ a b, R.compNodeEncode a = R.compNodeEncode b →
      ComputeTable.computeLabelOf a = ComputeTable.computeLabelOf b)
    (hMemEnc : ∀ a b, R.memNodeEncode a = R.memNodeEncode b →
      MemoryTable.memoryLabelOf a = MemoryTable.memoryLabelOf b)
    (hProgCap : R.exec.derivedRequestIO.length + 1 ≤ 2 ^ R.cfg.orbit.h)
    (hMemCap : R.exec.derivedResponseIO.length + 1 ≤ 2 ^ R.cfg.orbit.h)
    (hprog : ∀ kind, (R.computeIORAP kind).Satisfies M.computeIOTrace)
    (hmem : ∀ kind, (R.memoryIORAP kind).Satisfies M.memoryIOTrace)
    (hmul : ∀ j, M.io.multiplicity j ≠ 0)
    (hend : R.requests = R.responses) (hclose : R.outMem = 0) :
    ofLegacy (M.toLegacyAssignment hTable hCompEnc hMemEnc hProgCap hMemCap
      hprog hmem hmul hend hclose) = M := by
  cases R
  cases M
  rfl

/-- The legacy assignment alone supplies six RAPs.  All verifier gates are listed explicitly. -/
theorem accepts_of_legacy_assignment {S : PlusIOSegmentedFamily F K}
    (claim : P8PublicClaim) (ω : JointCoins K)
    (A : PlusIOSameExecutionAssignment S p) (hA : A.Satisfies)
    (hgates : (ofLegacy A).VerifierGates claim ω) :
    (ofLegacy A).Accepts claim ω :=
  ⟨hgates, sixRAPSatisfy_of_legacy A hA⟩

/-- A legacy P8 acceptance erases to raw acceptance once all current explicit raw gates are
checked. -/
theorem accepts_of_legacy_P8
    [Fintype K] [DecidableEq K]
    (T : P8Strategy (F := F) (K := K)) (ω : JointCoins K)
    (hz : nprSeed ω ≠ 0) (haccept : T.Accepts ω)
    (hgates :
      let A := T.assignmentAt ω hz
      (ofLegacy A).VerifierGates T.claim ω) :
    let S := T.familyAt ω hz
    let A := T.assignmentAt ω hz
    (ofLegacy A).Accepts T.claim ω := by
  let S := T.familyAt ω hz
  let A := T.assignmentAt ω hz
  have hsix := (P8Strategy.accepts_iff_six_families T ω hz).1 haccept
  have hA : A.Satisfies := by
    apply (PlusIOSameExecutionAssignment.satisfies_iff_six_families A).2
    exact ⟨hsix.1, hsix.2.1, hsix.2.2.1, hsix.2.2.2.1,
      hsix.2.2.2.2.1, hsix.2.2.2.2.2.1⟩
  exact ⟨hgates, sixRAPSatisfy_of_legacy A hA⟩

end RawMessage

/-- Public spelling of the truly raw verifier predicate. -/
def RawAccepts (claim : P8PublicClaim) (R : RawPlusIOSegmentedFamily F K)
    (ω : JointCoins K) (M : RawMessage R p) : Prop :=
  M.Accepts claim ω

theorem RawAccepts_iff_sixRAP_and_gates
    (claim : P8PublicClaim) (R : RawPlusIOSegmentedFamily F K)
    (ω : JointCoins K) (M : RawMessage R p) :
    RawAccepts claim R ω M ↔ M.VerifierGates claim ω ∧ M.SixRAPSatisfy :=
  Iff.rfl

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.RawAccepts_iff_sixRAP_and_gates
#print axioms Nock.NockVMROM.Thm54.RawMessage.rawAccepts_iff_sixRAP_and_gates
#print axioms Nock.NockVMROM.Thm54.RawMessage.canonicalNodeEncoders_of_accepts
#print axioms Nock.NockVMROM.Thm54.RawMessage.computeTable_sound_wfFree
#print axioms Nock.NockVMROM.Thm54.RawMessage.memoryTable_sound_wfFree
#print axioms Nock.NockVMROM.Thm54.RawMessage.computeRowAccepted_of_accepts
#print axioms Nock.NockVMROM.Thm54.RawMessage.memoryRowAccepted_of_accepts
#print axioms Nock.NockVMROM.Thm54.RawMessage.computeRowsAccepted_of_accepts
#print axioms Nock.NockVMROM.Thm54.RawMessage.memoryRowsAccepted_of_accepts
#print axioms Nock.NockVMROM.Thm54.RawMessage.computeWalkRAP_wholeTrace_iff
#print axioms Nock.NockVMROM.Thm54.RawMessage.memoryWalkRAP_wholeTrace_iff
#print axioms Nock.NockVMROM.Thm54.RawMessage.computeIORAP_wholeTrace_iff
#print axioms Nock.NockVMROM.Thm54.RawMessage.memoryIORAP_wholeTrace_iff
#print axioms Nock.NockVMROM.Thm54.RawMessage.lio_of_accepts
#print axioms Nock.NockVMROM.Thm54.RawMessage.sixRAPSatisfy_of_legacy
#print axioms Nock.NockVMROM.Thm54.RawMessage.ofLegacy_toLegacyAssignment
#print axioms Nock.NockVMROM.Thm54.RawMessage.accepts_of_legacy_P8
