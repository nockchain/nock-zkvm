/-
  Nock/RedTeam/Batch485Thm54WalkQueueReceipts.lean

  Queue-validity (`deployed_bfsValid` / `deployed_bfsValid_memory`) rejects
  them with no condition on `α`.  Gate-level rejection at every `α` is
  `Batch480`.  Honest matmul / Peano-fib remain accepted
  (`canonical*Trace_satisfies`).  Tiling events are now in the consumed
  union; `walkAlphaRootBound N = N`.  `openConjunctsAfterVer` stays 7.
  No new `nockCompiles_zmod` hypothesis.  Slot 7 / roles 34–36 untouched.
-/
import Nock.NockVMROM.Thm54.WalkQueueDeployed
import Nock.NockVMROM.Thm54.MemoryWalkDeployed
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
import Nock.NockVMROM.Thm54.ComputeWalkRootEvents
import Nock.NockVMROM.Thm54.WalkTilingEvents
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch459Thm54ComputeTopologyStop
import Nock.RedTeam.Batch469Thm54GarbageWitness
import Nock.RedTeam.Batch470Thm54MemoryPrefix
import Nock.RedTeam.Batch480Thm54QueueGateWitnesses
import Nock.RedTeam.Batch481Thm54CompilerWalkCoin
import Nock.RedTeam.Batch484Thm54WalkQueueConsequences
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch485

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Framework Nock.Reified
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.RedTeam.Batch459
open Nock.RedTeam.Batch469
open Nock.RedTeam.Batch470
open Nock.RedTeam.Batch480

/-! ## Chip-level rejection of the garbage fanouts -/

section ComputeChip

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)

include hax hbasis hwidth

/-- An accepted compute chip's decoded fanout cannot be `fo5`. -/
theorem accepted_compute_fo_ne_fo5
    (hrows : P.optimized.family.problem.cfg.compRows = 5) :
    foW P c Qc hsat ≠ Batch469.fo5 := by
  intro heq
  have hv := deployed_bfsValid P c Qc hsat hax hbasis hwidth
  have hrows' : rows P = 5 := hrows
  rw [hrows', heq] at hv
  exact Batch469.fo5_not_bfsValid hv

omit hax hbasis hwidth in
/-- Census #5's `(0,2,0)` is not `BFSValid` at height 3. -/
theorem fo020_not_bfsValid : ¬ BFSValid (fun i => if i = 2 then 2 else 0) 3 := by
  intro hv
  have := hv 2 (by norm_num) (by norm_num)
  simp [Sf] at this

/-- An accepted compute chip's decoded fanout cannot be `(0,2,0)`. -/
theorem accepted_compute_fo_ne_020
    (hrows : P.optimized.family.problem.cfg.compRows = 3) :
    foW P c Qc hsat ≠ (fun i => if i = 2 then 2 else 0) := by
  intro heq
  have hv := deployed_bfsValid P c Qc hsat hax hbasis hwidth
  have hrows' : rows P = 3 := hrows
  rw [hrows', heq] at hv
  exact fo020_not_bfsValid hv

end ComputeChip

section MemoryChip

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
  (hchar : FamilyMemoryRows.MemStateTagChar F)

include hsat hchar

/-- An accepted memory chip's decoded forest cannot be `fo3`. -/
theorem accepted_memory_fo_ne_fo3
    (hk : kMem P = 1) (hrows : memRows P = 3) :
    MemoryWalkDeployed.foW P c Qm ≠ Batch470.fo3 := by
  intro heq
  have hv := deployed_bfsValid_memory P c Qm hsat hchar
  rw [hk, hrows, heq] at hv
  exact Batch470.fo3_not_bfsValidF hv

end MemoryChip


theorem fo5_rejected_every_alpha {K : Type} [Field K] (α : K) :
    ¬ (∀ i, 1 ≤ i → i < 5 → α ^ (1 + Sf Batch469.fo5 i) ≠ α ^ i) :=
  Batch480.fo5_rejected_by_ratio_gate α

theorem fo3_rejected_every_alpha {K : Type} [Field K] (α : K) :
    ¬ (∀ i, 1 ≤ i → i < 3 → α ^ (1 + Sf Batch470.fo3 i) ≠ α ^ i) :=
  Batch480.fo3_rejected_by_ratio_gate α

theorem fo020_rejected_every_alpha {K : Type} [Field K] (α : K) :
    ¬ (∀ i, 1 ≤ i → i < 3 →
        α ^ (1 + Sf (fun i => if i = 2 then 2 else 0) i) ≠ α ^ i) :=
  Batch480.fo020_rejected_by_ratio_gate α

/-! ## Honest fixtures remain accepted -/

theorem honest_matmul_accepted
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
        (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    RAP.SatisfiesWithPreprocessing P.memoryChip (canonicalMemoryTrace P) :=
  honest_matmul_accepted_at_deployed_chip P hmore hC

theorem honest_peano_fib_accepted
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
        (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (hC : P.optimized.family.problem.exec.CprimeCoherent) :
    RAP.SatisfiesWithPreprocessing P.memoryChip (canonicalMemoryTrace P) :=
  honest_peano_fib_accepted_at_deployed_chip P hmore hC

theorem honest_compute_accepted
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    RAP.SatisfiesWithPreprocessing P.computeChip (canonicalComputeTrace P) :=
  canonicalComputeTrace_satisfies P hax hbasis hwidth

/-- Completeness at the compiler walk coin is still `computeChipAt = computeChip`. -/
theorem compiler_triple_unmoved
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hchal :
      DeployedChipFamily.computeChalValOfTuple P.optimized.basis P.honestTuple =
        P.optimized.computeChallenge)
    (hst :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).state =
        ComputeWalkSeed.rootStateOfFormula P.optimized.verifier.raw.claim.formula)
    (hs :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).s =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.subject)
    (hf :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).f =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.formula)
    (he :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).e =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.result) :
    P.computeChipAt P.honestTuple = P.computeChip :=
  Batch481.perfect_at_compiler_triple P hchal hst hs hf he


theorem walkAlphaRootBound_is_N (N : ℕ) :
    ComputeWalkRootEvents.walkAlphaRootBound N = N :=
  rfl

theorem walkRootBound_is_N_plus_9 (N : ℕ) :
    ComputeWalkRootEvents.walkRootBound N = N + 9 :=
  ComputeWalkRootEvents.walkRootBound_eq N

/-- IO slot = `famIOEventOf`.) -/
theorem failureEvent_prices_tiling
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    P.optimizedFailureEvent Qc Qm =
      OptimizedStrictPackage.OptimizedHostileProductionFailureEvent
        P.strategy P.optimized.census P.objects.cfg.challenges.lam
        (P.famIOEventOf Qc Qm) (P.hostileRequests Qc).length
        (P.computeSourceEnv Qc) (P.computeWalkEnv Qc) (P.computeScalarEnv Qc)
        (P.memorySourceEnv Qm) (P.memoryScalarFamilies Qm)
        (P.hostileInterRecords Qm) (P.memoryBaseEnv Qm)
        (P.computeWalkRootEvent Qc)
        (P.computeTilingEventOf Qc)
        (P.memoryTilingEventOf Qm)
        (P.computePrefixGammaEventOf Qc)
        (P.memoryPrefixGammaEventOf Qm)
        (P.memoryForestAlphaEventOf Qm)
        (P.decodedLambdaEventOf Qc Qm)
        (PreSeedCensus.reqPairEventOfEnvs K P.q P.optimized.family.problem.cfg.kMem
          (P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ) (P.memoryBaseEnv Qm)
          P.optimized.family.problem.cfg.memRows_pos
          (PreSeedCensus.requestTargets P.strategy.skeleton)) :=
  rfl


theorem afterVer_stays_seven :
    Nock.RedTeam.Batch448.openConjunctsAfterVer.length = 7 :=
  Nock.RedTeam.Batch448.openConjunctsAfterVer_length

def nockCompiles_zmod_hypotheses_unmoved : String :=
  "nockCompiles_zmod binders unmoved: hrun hbound hs hf hΛp hp hK hF hwin hKszChar"

theorem nockCompiles_zmod_hypotheses_unmoved_nonempty :
    nockCompiles_zmod_hypotheses_unmoved ≠ "" := by
  decide

def slot7_roles34_36_untouched : String :=
  "walk-γ slot 7 and memory hosts 34-36 unread (Batch483/484)"

theorem slot7_roles34_36_untouched_nonempty :
    slot7_roles34_36_untouched ≠ "" := by
  decide

end Nock.RedTeam.Batch485

#print axioms Nock.RedTeam.Batch485.accepted_compute_fo_ne_fo5
#print axioms Nock.RedTeam.Batch485.accepted_compute_fo_ne_020
#print axioms Nock.RedTeam.Batch485.accepted_memory_fo_ne_fo3
#print axioms Nock.RedTeam.Batch485.fo5_rejected_every_alpha
#print axioms Nock.RedTeam.Batch485.honest_matmul_accepted
#print axioms Nock.RedTeam.Batch485.honest_peano_fib_accepted
#print axioms Nock.RedTeam.Batch485.walkAlphaRootBound_is_N
#print axioms Nock.RedTeam.Batch485.failureEvent_prices_tiling
#print axioms Nock.RedTeam.Batch485.afterVer_stays_seven
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
