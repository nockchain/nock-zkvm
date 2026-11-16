import Nock.NockVMROM.Thm54.OptimizedMemorySameExecution
import Nock.WalkInGate

/-!
# Exact source realization for optimized memory

This exposes the actual source equations which the `6/55` folding consumes.  In particular the
row equations are the shipped `(memoryAIR (K := K))` bodies, not a self-named acceptance predicate, and the
walk component is the one aggregate `Corr:forest` recurrence.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedMemorySemanticRealization

open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open OptimizedMemorySameExecution
open OptimizedMemoryCoreInventory
open OptimizedMemoryCodec

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}
variable {A : SampledIOSameExecutionAssignment R p}

/-- Exact memory-table environment for one row of the one same-execution assignment. -/
def exactMemoryRowEnv (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) : Env K :=
  memoryEnvFull R.problem.cfg.challenges.memoryInputs
    (MemoryTable.opSel (R.problem.exec.memoryPubAt i).st)
    (R.problem.exec.memoryPubAt i) (A.exact.memoryTableAux i)

/-- Honest deployed acc: mask form (`Walk.accInGate`).  The assignment's
    `memoryWalk.acc` remains the K-side `WalkSat` seed-form witness. -/
def memoryAccInGate (A : SampledIOSameExecutionAssignment R p) (k : ℕ) : K :=
  Nock.Walk.accInGate
    (Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows)
    (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
    (Nock.Walk.foCol R.memoryWalkRows)
    R.memoryWalkAlpha (R.memoryWalkAlpha ^ R.problem.cfg.kMem)
    R.problem.cfg.kMem k

/-- Exact memory-walk environment for the **deployed** (mask-form) census. -/
def exactMemoryWalkRowEnv (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) : Env K :=
  Trans.walkRowEnvMasked
    (Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows)
    (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
    (Nock.Walk.foCol R.memoryWalkRows)
    A.exact.memoryWalk.ln A.exact.memoryWalk.count
    (memoryAccInGate A)
    R.memoryWalkAlpha 0
    (R.memoryWalkAlpha ^ R.problem.cfg.kMem)
    (Nock.Walk.rootMask (K := K) R.problem.cfg.kMem)
    ((i : ℕ) + 1)

/-- Paper `ver`-selector as a field element. -/
def responseActive (ver : Bool) : K :=
  if ver then 1 else 0

def reqIdxNat (R : PlusIOSegmentedFamily F K) (pub : MemoryTable.Pub K) : ℕ :=
  if pub.st = .read_root ∨ pub.st = .verify_child then
    RecordCarrier.honestExp R.problem.exec.derivedRequestIO (NockVM.encRecC pub.mem pub.cprime)
  else 0

/-- The honest `reqIdx` column value (base field). -/
def honestReqIdx (R : PlusIOSegmentedFamily F K) (i : Fin R.problem.cfg.memRows) : F :=
  ((reqIdxNat R (R.problem.exec.memoryPubAt i) : ℕ) : F)

/-- The honest ten-slot record of a memory row: the nine-slot encode plus `reqIdx`. -/
def rowRecord10 (R : PlusIOSegmentedFamily F K) (i : Fin R.problem.cfg.memRows) : Fin 10 → K :=
  RecordCarrier.withExp
    (NockVM.encRecC (R.problem.exec.memoryPubAt i).mem (R.problem.exec.memoryPubAt i).cprime)
    ((reqIdxNat R (R.problem.exec.memoryPubAt i) : ℕ) : K)

/-- On `read_root` / `verify_child` rows the honest ten-slot record is the honest extension of the
row's record. -/
theorem rowRecord10_of_active (R : PlusIOSegmentedFamily F K) (i : Fin R.problem.cfg.memRows)
    (h : (R.problem.exec.memoryPubAt i).st = .read_root ∨
      (R.problem.exec.memoryPubAt i).st = .verify_child) :
    rowRecord10 R i = RecordCarrier.extRec R.problem.exec.derivedRequestIO
      (NockVM.encRecC (R.problem.exec.memoryPubAt i).mem (R.problem.exec.memoryPubAt i).cprime) := by
  simp [rowRecord10, reqIdxNat, h, RecordCarrier.extRec]

def responseDenominator (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) : K :=
  FiniteIO.compress A.sampled.coins (rowRecord10 R i)

def safeResponseDenominator (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) : K :=
  responseActive (K := K) (R.problem.exec.memoryPubAt i).ver *
      responseDenominator A i +
    (1 - responseActive (K := K) (R.problem.exec.memoryPubAt i).ver)

def responseContribution (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) : K :=
  responseActive (K := K) (R.problem.exec.memoryPubAt i).ver *
    (safeResponseDenominator A i)⁻¹

/-- Position-free scalar prefix accumulator over the exact memory-row stream.  This is a local
structural accumulator, not a lookup or pointer into the memory multiset. -/
def responseAccumulator (A : SampledIOSameExecutionAssignment R p) (n : ℕ) : K :=
  RowLayout.coResidentAcc A.compress10 R.problem.exec.memoryRows n

def firstMaskK (i : Fin R.problem.cfg.memRows) : K :=
  if (i : ℕ) = 0 then 1 else 0

def lastMaskK (i : Fin R.problem.cfg.memRows) : K :=
  if (i : ℕ) + 1 = R.problem.cfg.memRows then 1 else 0

def forestInitResidual (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) : K :=
  firstMaskK (K := K) i *
    Trans.walkAccInitMasked.eval (exactMemoryWalkRowEnv A i)

def sampledMemoryRoleValue (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) : SampledMemoryIORole → K
  | 0 => responseDenominator A i
  | 1 => (safeResponseDenominator A i)⁻¹
  | 2 => responseActive (K := K) (R.problem.exec.memoryPubAt i).ver
  | 3 => A.witness10.terminal
  | 4 => forestInitResidual A i
  | 5 => responseContribution A i
  | 6 => responseAccumulator A i
  | 7 => responseAccumulator A ((i : ℕ) + 1)
  -- The two dead sampled roles `45`/`46` host the declared
  -- child state tags, read by the in-gate child
  -- payload RLCs (`MemoryWalkLabel.childTagHost`).
  | 8 => MemoryTable.memChildStateTagCol R.memoryWalkRows ((i : ℕ) + 1) 0
  | 9 => MemoryTable.memChildStateTagCol R.memoryWalkRows ((i : ℕ) + 1) 1
  | 10 => firstMaskK (K := K) i
  | 11 => lastMaskK (K := K) i
  | 12 => lastMaskK (K := K) i * (R.problem.exec.memoryPubAt i).icur
  | 13 => safeResponseDenominator A i

def firstMask (i : Fin R.problem.cfg.memRows) : F := if (i : ℕ) = 0 then 1 else 0

def lastMask (i : Fin R.problem.cfg.memRows) : F :=
  if (i : ℕ) + 1 = R.problem.cfg.memRows then 1 else 0

/-- Honest ratio-form inverse: `(count − ln)⁻¹` off a tiled last row, else `0`. -/
def walkInvValue (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) : K :=
  let c := A.exact.memoryWalk.count ((i : ℕ) + 1)
  let l := A.exact.memoryWalk.ln ((i : ℕ) + 1)
  if c = l then 0 else (c - l)⁻¹

/-- One exact typed `6/56` source row.  Every value is a projection or local scalar derivative of
the same assignment `A`; in particular no memory-row pointer is introduced. -/
def semanticRowAt (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) : SemanticRow F K where
  state := (R.problem.exec.memoryPubAt i).st
  isFirst := firstMask i
  isLast := lastMask i
  table := fun role =>
    match role with
    | .inr (.inr (.inr r)) =>
        if r = 0 then
          RowLayout.interResidentAcc A.interCompress10 R.problem.exec.memoryRows i.val
        else if r = 1 then
          RowLayout.interResidentAcc A.interCompress10 R.problem.exec.memoryRows (i.val + 1)
        else
          (exactMemoryRowEnv A i).trace (memoryTableSourceColumn role)
    | _ =>
        (exactMemoryRowEnv A i).trace (memoryTableSourceColumn role)
  walk := fun role => (exactMemoryWalkRowEnv A i).trace role
  sampledIO := sampledMemoryRoleValue A i
  selectorMirror := fun role =>
    algebraMap F K (stateSelector (F := F)
      (R.problem.exec.memoryPubAt i).st role)
  walkInv := walkInvValue A i

def encodedRowAt (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) : EncodedRow F K :=
  encode (semanticRowAt A i)

@[simp] theorem decode_encodedRowAt (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) :
    decode (encodedRowAt A i) = semanticRowAt A i :=
  decode_encode _

theorem encodedRowAt_controls (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) :
    AcceptedControls (encodedRowAt A i) := by
  apply encode_controls_accepted
  · by_cases h : (i : ℕ) = 0 <;>
      simp [semanticRowAt, firstMask, h]
  · by_cases h : (i : ℕ) + 1 = R.problem.cfg.memRows <;>
      simp [semanticRowAt, lastMask, h]

/-- Every source `(memoryAIR (K := K))` body vanishes on every exact accepted row. -/
theorem exact_memoryAIR_sources
    (P : MemoryChipAssignment A)
    (hlam : ∀ i, (R.problem.exec.memoryPubAt i).lambda =
      (R.problem.exec.memoryPubAt ⟨0, R.problem.cfg.memRows_pos⟩).lambda) :
    ∀ i, ∀ c ∈ (memoryAIR (K := K)).constraints,
      c.expr.eval (exactMemoryRowEnv A i) = 0 := by
  let env := fun i : Fin R.problem.cfg.memRows => exactMemoryRowEnv A i
  have hrowRAP :=
    (memoryRowSegment_iff R.problem.cfg R.problem.exec.memoryPubAt A.exact.memoryTableTrace).1
      (P.obligations.1 .row)
  have hrows :
      ∀ i, ∀ c ∈ (memoryAIR (K := K)).constraints, c.expr.eval (env i) = 0 := by
    apply (satisfies_iff_perRow_env_mem env R.problem.cfg.memNodes
      R.problem.cfg.memNodes_injective
      (R.problem.cfg.challenges.memoryChalVal
        (R.problem.exec.memoryPubAt ⟨0, R.problem.cfg.memRows_pos⟩).lambda)
      R.problem.cfg.eDeg R.problem.cfg.orbit.h R.problem.cfg.orbit.ω
      R.problem.cfg.orbit.βcoset R.problem.cfg.orbit.βcoset_ne_zero
      R.problem.cfg.orbit_h_pos
      (by
        intro k
        funext j
        simp [env, exactMemoryRowEnv, memoryEnvFull, ChallengeVector.memoryChalVal,
          ChallengeVector.memoryInputs, hlam k]
        rfl)
      (fun _ => rfl)).1
    simpa [env, exactMemoryRowEnv,
      PlusIOSameExecutionAssignment.memoryTableTrace,
      exactCanonicalEncodeMem] using hrowRAP
  exact hrows

/-- Exact cross-row `intermediate` handoff and all four endpoint equations, obtained from the same
table satisfaction proof. -/
theorem exact_intermediate_and_endpoints
    (P : MemoryChipAssignment A) :
    (∀ i : Fin R.problem.cfg.memRows, ∀ hi : (i : ℕ) + 1 < R.problem.cfg.memRows,
      (R.problem.exec.memoryPubAt i).icur =
        (R.problem.exec.memoryPubAt ⟨(i : ℕ) + 1, hi⟩).ipre) ∧
    (R.problem.exec.memoryPubAt ⟨0, R.problem.cfg.memRows_pos⟩).pt.counts = 0 ∧
    (R.problem.exec.memoryPubAt ⟨0, R.problem.cfg.memRows_pos⟩).pt.indicator = 0 ∧
    (R.problem.exec.memoryPubAt ⟨0, R.problem.cfg.memRows_pos⟩).ipre = 0 ∧
    (R.problem.exec.memoryPubAt
      (R.problem.cfg.orbit.lastIndex
        R.problem.cfg.memRows R.problem.cfg.memRows_pos)).icur = 0 := by
  have haccept : exactMemoryChainedAccepts R.problem :=
    (exactChainedHasCanonicalRAP2 F K).memory_iff R.problem |>.2
      ⟨A.exact.memoryTableAux, P.obligations.1⟩
  exact ⟨haccept.2.1, haccept.2.2.1, haccept.2.2.2.1,
    haccept.2.2.2.2.1, haccept.2.2.2.2.2⟩

/-- The exact reified forest-walk source: initial line/count/accumulator, every adjacent
line/count/accumulator recurrence, and terminal zero.  K-side `WalkSat` (seed form). -/
theorem exact_forest_walk_sources
    (P : MemoryChipAssignment A) :
    let cur := Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows
    let chld := Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows
    let fo := Nock.Walk.foCol R.memoryWalkRows
    Trans.WalkGatesSat cur chld fo
      A.exact.memoryWalk.ln A.exact.memoryWalk.count A.exact.memoryWalk.acc
      R.memoryWalkAlpha R.memoryWalkSeed
      (R.memoryWalkAlpha ^ R.problem.cfg.kMem) R.problem.cfg.memRows ∧
    Trans.walkOut.eval
      (Trans.walkRowEnv cur chld fo
        A.exact.memoryWalk.ln A.exact.memoryWalk.count A.exact.memoryWalk.acc
        R.memoryWalkAlpha R.memoryWalkSeed
        (R.memoryWalkAlpha ^ R.problem.cfg.kMem) R.problem.cfg.memRows) = 0 := by
  dsimp only
  refine ⟨(Trans.walkGatesSat_iff_walkSat _ _ _ _ _ _ _ _ _ _).2
    P.oneForestWalk.1, ?_⟩
  exact Trans.reified_walk_out_sound.2 P.oneForestWalk.2

theorem exact_kMem_pos : 1 ≤ R.problem.cfg.kMem :=
  Nat.succ_le_of_lt R.problem.exec.memoryRootCount_pos

theorem exact_kMem_le : R.problem.cfg.kMem ≤ R.problem.cfg.memRows :=
  R.problem.exec.kMem_le_memRows

/-- Deployed acc agrees with the K-side `WalkSat` acc from row `kMem` on
    (`seed = nodeListP kMem` is `memoryWalkSeed`). -/
theorem memoryAccInGate_eq_walkSat_acc
    (P : MemoryChipAssignment A) {k : ℕ}
    (hk1 : 1 ≤ k) (hkh : k ≤ R.problem.cfg.memRows) (hk : R.problem.cfg.kMem ≤ k) :
    memoryAccInGate A k = A.exact.memoryWalk.acc k := by
  have hsat := P.oneForestWalk.1
  have htel := Nock.Walk.acc_telescope hsat k hk1 hkh
  unfold memoryAccInGate
  rw [Nock.Walk.accInGate_of_ge_kMem _ _ _ _ _ hk, htel]
  rfl

theorem memoryAccInGate_last_zero (P : MemoryChipAssignment A) :
    memoryAccInGate A R.problem.cfg.memRows = 0 := by
  rw [memoryAccInGate_eq_walkSat_acc P R.problem.cfg.memRows_pos le_rfl exact_kMem_le]
  exact P.oneForestWalk.2

/-- Hosted census of the deployed mask-form walk (`accInGate` on the physical acc
    column).  Ln/count are the certificate's; acc is mask form. -/
theorem exact_forest_walk_sources_masked
    (P : MemoryChipAssignment A) :
    let cur := Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows
    let chld := Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows
    let fo := Nock.Walk.foCol R.memoryWalkRows
    let rm := Nock.Walk.rootMask (K := K) R.problem.cfg.kMem
    Trans.WalkGatesSatMasked cur chld fo
      A.exact.memoryWalk.ln A.exact.memoryWalk.count (memoryAccInGate A)
      R.memoryWalkAlpha 0
      (R.memoryWalkAlpha ^ R.problem.cfg.kMem) rm R.problem.cfg.memRows := by
  dsimp only
  have hsat := P.oneForestWalk.1
  have hgate := (Trans.walkGatesSat_iff_walkSat _ _ _ _ _ _ _ _ _ _).2 hsat
  refine ⟨hgate.1, ?_, ?_, ?_, ?_⟩
  · rw [Trans.walkLn1_eval_masked]; exact hgate.2.1
  · rw [Trans.walkCount1_eval_masked]; exact hgate.2.2.1
  · refine (Trans.reified_walk_accInitMasked_sound _).2 ?_
    have hacc : memoryAccInGate A 1 =
        (R.memoryWalkAlpha ^ R.problem.cfg.kMem) *
          ∑ i ∈ Finset.Icc 1 1,
            Nock.Walk.childSum
              (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
              (Nock.Walk.foCol R.memoryWalkRows) R.memoryWalkAlpha i := by
      unfold memoryAccInGate
      rw [Nock.Walk.accInGate_of_le_kMem _ _ _ _ _ exact_kMem_pos]
    rw [hacc]
    have hsum : (∑ i ∈ Finset.Icc 1 1,
        Nock.Walk.childSum
          (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
          (Nock.Walk.foCol R.memoryWalkRows) R.memoryWalkAlpha i)
        = Nock.Walk.childSum
            (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
            (Nock.Walk.foCol R.memoryWalkRows) R.memoryWalkAlpha 1 := by
      simp
    rw [hsum]
    exact (Nock.Walk.childSum_scale_init
      (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
      (Nock.Walk.foCol R.memoryWalkRows)
      R.memoryWalkAlpha (R.memoryWalkAlpha ^ R.problem.cfg.kMem)).symm
  · intro i hi hih
    refine ⟨?_, ?_, ?_⟩
    · rw [Trans.walkLnStep_eval_masked]; exact (hgate.2.2.2.2 i hi hih).1
    · rw [Trans.walkCountStep_eval_masked]; exact (hgate.2.2.2.2 i hi hih).2.1
    · refine (Trans.reified_walk_acc_stepMasked_sound _ i).2 ?_
      have hcnt := Nock.Walk.count_closed hsat i hi (Nat.le_of_lt hih)
      have hstep := Nock.Walk.accInGate_accStep
        (Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows)
        (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
        (Nock.Walk.foCol R.memoryWalkRows)
        R.memoryWalkAlpha (R.memoryWalkAlpha ^ R.problem.cfg.kMem)
        R.problem.cfg.kMem i
      have hln := Nock.Walk.ln_closed hsat (i + 1) (by omega) (by omega)
      unfold memoryAccInGate
      rw [hln, hcnt]
      convert hstep using 1 <;> simp [Nock.Walk.deqCoeff]

/-- One conjunction containing the exact table, one forest walk, sampled IO, and axis structure.
Every component is projected from `P`; no independently quantified replacement object occurs. -/
def ExactMemorySourceSemantics {execA : ExactExecution R.problem.cfg}
    (_P : MemoryProductionAssignment A execA) : Prop :=
  (∀ i, ∀ c ∈ (memoryAIR (K := K)).constraints,
      c.expr.eval (exactMemoryRowEnv A i) = 0) ∧
    (let cur := Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows
     let chld := Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows
     let fo := Nock.Walk.foCol R.memoryWalkRows
     Trans.WalkGatesSat cur chld fo
       A.exact.memoryWalk.ln A.exact.memoryWalk.count A.exact.memoryWalk.acc
       R.memoryWalkAlpha R.memoryWalkSeed
       (R.memoryWalkAlpha ^ R.problem.cfg.kMem) R.problem.cfg.memRows ∧
     A.exact.memoryWalk.acc R.problem.cfg.memRows = 0) ∧
    FiniteIO.FiniteIOAccepts
      A.sampled.records A.sampled.coins A.sampled.witness ∧
    -- axis structure on the a-bearing view (row-level executed rows carry `(T, C')`)
    TemplateAxisCounting.ExactAxisStructuralRefinement
      R.problem.cfg execA

theorem exact_source_semantics {execA : ExactExecution R.problem.cfg}
    (P : MemoryProductionAssignment A execA)
    (hlam : ∀ i, (R.problem.exec.memoryPubAt i).lambda =
      (R.problem.exec.memoryPubAt ⟨0, R.problem.cfg.memRows_pos⟩).lambda) :
    ExactMemorySourceSemantics P := by
  refine ⟨exact_memoryAIR_sources P hlam, ?_, P.obligations.2.2.1, P.axisStructural⟩
  exact ⟨(Trans.walkGatesSat_iff_walkSat _ _ _ _ _ _ _ _ _ _).2
    P.oneForestWalk.1, P.oneForestWalk.2⟩

end
end OptimizedMemorySemanticRealization
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization.exact_memoryAIR_sources
#print axioms Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization.exact_forest_walk_sources
#print axioms Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization.exact_source_semantics
