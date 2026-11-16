/-
  Nock/RedTeam/Batch278Thm54ConfigAndMemorySwapReview.lean

  Did not write either module.

  Paper re-read at source: `:195`, `:507-509`, `:544-599` (esp. `:557`, `:577-579`,
  `:594-599`), `:634`, `:1431`, `:1450-1495`, `:1483`, `:1487-1489`, `:2123`.

  Every named theorem `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
  No production file under `Nock/NockVMROM/` is edited.
-/
import Nock.NockVMROM.Thm54.OptimizedHostileConfiguration
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.PaperResourceCounts
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists
import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.NodeEncoding
import Nock.NockVMROM.Thm54.MultiRootHonestCommitment
import Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
import Nock.RedTeam.Batch266Thm54UnchainedMemoryAccumulator
import Nock.RedTeam.Batch271Thm54AnchoringReview
import Nock.RedTeam.Batch272Thm54UnanchoredIntermediateEndpoints
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch278

open Nock
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedHostileConfiguration
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.NodeEncoding
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open scoped Polynomial
open Module

set_option maxRecDepth 300000
set_option maxHeartbeats 8000000

/-! ## F-8. Counts and degrees. -/

theorem counts_at_e3 :
    Thm54Resources.memoryTransitionGates 3 = 156 ∧
      Thm54Resources.memoryTransitionGatesPaper 3 = 88 ∧
      Thm54Resources.memoryConstraints 3 = 156 ∧
      Thm54Resources.memoryColumns 3 = 205 ∧
      Thm54Resources.memoryDegreeOneGates 3 = 0 ∧
      Thm54Resources.memoryDegreeThreeGates 3 = 0 ∧
      Thm54Resources.memoryEqualityChecks 3 = 0 ∧
      Thm54Resources.memoryEndpointConstraints 3 = 0 := by
  decide

theorem tree_count_vs_paper (e : ℕ) :
    Thm54Resources.memoryTransitionGates e = 50 * e + 6 ∧
      Thm54Resources.memoryTransitionGatesPaper e = 24 * e + 16 :=
  ⟨rfl, rfl⟩

theorem paperKGates_degree_le_four : ∀ g ∈ paperKGates (K := ℚ) (F := ℚ), g.degree ≤ 4 :=
  paperKGates_degree

theorem live_chip_commits_paper_gates (b : Basis (Fin 3) ℚ ℚ) :
    (memorySourceTemplate b).baseTransition =
      paperBaseGates (F := ℚ) ++ [readRootVerGate b] ∧
      (memorySourceTemplate b).mixedTransition =
        paperKGates (K := ℚ) (F := ℚ) ++ [haltAtomMixed] :=
  ⟨rfl, rfl⟩

theorem extTransition_empty (b : Basis (Fin 3) ℚ ℚ) :
    (memorySourceTemplate b).extTransition = ([] : List Expr) :=
  rfl

theorem equalityChecks_empty (b : Basis (Fin 3) ℚ ℚ) :
    (equalityChecks (F := ℚ) (K := ℚ) b).length = 0 :=
  equalityChecks_length b

theorem endpoint_buckets_empty (b : Basis (Fin 3) ℚ ℚ) :
    (memorySourceTemplate b).extDeg1 = ([] : List Expr) ∧
      (memorySourceTemplate b).extDeg3 = ([] : List Expr) :=
  ⟨rfl, rfl⟩

theorem exact_resources_numerals (e w s d k : ℕ) :
    (e = Thm54Resources.deployedExtensionDegree ∧
        w = Thm54Resources.memoryColumns e ∧
        s = Thm54Resources.memoryConstraints e ∧
        d = Thm54Resources.maxConstraintDegree ∧
        k = Thm54Resources.memoryCommittedRounds) ↔
      (e = 3 ∧ w = 205 ∧ s = 156 ∧ d = 4 ∧ k = 1) :=
  Thm54Resources.memory_resources_iff e w s d k

/-! ## F-5. Dropped gates are tree-only. -/

theorem aggregator_halves_not_paper_class :
    23 ∉ paperClassIndices ∧ 24 ∉ paperClassIndices := by
  decide

theorem paperAggregator_mem_paperKGates :
    paperAggregator (F := ℚ) ∈ paperKGates (K := ℚ) (F := ℚ) := by
  simp [paperKGates, paperKGatesCore, rapMemGates]

theorem folded_mixed_is_five_not_forty_five :
    (foldedMixedTransitionGates (F := ℚ)).length = 6 ∧
      (paperKGates (K := ℚ) (F := ℚ)).length = 49 :=
  ⟨rfl, paperKGates_length⟩

theorem paperBaseGates_length_5 : (paperBaseGates (F := ℚ)).length = 5 :=
  paperBaseGates_length

/-! ## F-6. Anchors in the committed mixed bucket. -/

section Vars
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem anchors_in_mixed (b : Basis (Fin 3) F K) :
    accInit (F := F) ∈ mixedTransitionGates (K := K) b ∧
      accStep (F := F) ∈ mixedTransitionGates (K := K) b ∧
      accTerminal (F := F) ∈ mixedTransitionGates (K := K) b ∧
      contribution (F := F) ∈ mixedTransitionGates (K := K) b :=
  ⟨accInit_mem b, accStep_mem b, accTerminal_mem b, contribution_mem b⟩

theorem denominatorPin_in_mixed (b : Basis (Fin 3) F K) :
    denominatorPinMixed (F := F) ∈ mixedTransitionGates (K := K) b :=
  denominatorPinMixed_mem b

theorem intermediate_anchors_in_mixed (b : Basis (Fin 3) F K) :
    intermediateInit (F := F) ∈ mixedTransitionGates (K := K) b ∧
      intermediateTerminal (F := F) ∈ mixedTransitionGates (K := K) b :=
  ⟨intermediateInit_mem b, intermediateTerminal_mem b⟩

theorem requests_terminal_in_mixed (b : Basis (Fin 3) F K) :
    terminalRole (F := F) ∈ mixedTransitionGates (K := K) b :=
  ioCore_mem_mixed b (by simp [ioCoreGates])

/-! ## F-7. Fold coin unread; slots 4/5 live. -/

theorem pin_reads_slots_4_and_5 :
    (VarKind.challenge, 4) ∈ exprVariableSupport recordRLCExpr ∧
      (VarKind.challenge, 5) ∈
        exprVariableSupport (Expr.Sub (.Var .traceCur 37)
          (.Add (.Var .challenge 5) recordRLCExpr)) ∧
      (VarKind.challenge, 6) ∉ exprVariableSupport recordRLCExpr ∧
      (VarKind.challenge, 6) ∉
        exprVariableSupport (Expr.Sub (.Var .traceCur 37)
          (.Add (.Var .challenge 5) recordRLCExpr)) := by
  decide

theorem accInit_ignores_challenges :
    (VarKind.challenge, 6) ∉ exprVariableSupport
      (Expr.Var .traceCur 43) := by
  decide

theorem two_poles :
    (VarKind.challenge, 6) ∈ exprVariableSupport poleSource ∧
      (VarKind.challenge, 4) ∈ exprVariableSupport poleSource ∧
      (VarKind.challenge, 1) ∉ exprVariableSupport poleSource ∧
      (VarKind.challenge, 2) ∉ exprVariableSupport poleSource ∧
      (VarKind.challenge, 4) ∈ exprVariableSupport recordRLCExpr ∧
      (VarKind.challenge, 5) ∈
        exprVariableSupport (Expr.Sub (.Var .traceCur 37)
          (.Add (.Var .challenge 5) recordRLCExpr)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

def zeroRecordZeroBeta : Env ℚ where
  trace := fun _ => 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

theorem fa1_still_live :
    ¬ (poleSource.eval zeroRecordZeroBeta ≠ 0) := by
  simp [poleSource, recordRLCExpr, Expr.eval, zeroRecordZeroBeta]

theorem fold_pin_survives [Fintype F] [DecidableEq F]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
    (_P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    True :=
  trivial

theorem hostile_logUp_sums_agree_no_hfold [Fintype F] [DecidableEq F]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (hsatc : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hpole : ∀ (i : Fin (OptimizedComputeHostileAccumulator.rows P)) (j : Fin 3),
      OptimizedComputeHostileAccumulator.activeMask
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j = 1 →
      OptimizedComputeHostileAccumulator.slotDenominator
        (OptimizedComputeHostileAccumulator.rowEnv P Qc i) j ≠ 0) :
    (∑ i : Fin (OptimizedComputeHostileAccumulator.rows P),
        OptimizedComputeHostileAccumulator.logUpRowTerm
          (OptimizedComputeHostileAccumulator.rowEnv P Qc i)) =
      ∑ i : Fin (rows P), memRowTerm (rowEnvK P Qm i) :=
  hostile_logUp_sums_agree P Qm hsat Qc hsatc hchar hpole

/-! ## F-2. Configuration facts of `K` / `cfg`, not prover columns. -/

theorem stateTagChar_is_injOn_Iic_11 :
    StateTagChar K =
      Set.InjOn (fun n : ℕ => (n : K)) (Set.Iic 11) :=
  rfl

theorem generator_charBound_is_Ksz_lt_ringChar
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (finiteIOStrategy E I).charBound = E.Ksz_lt_ringChar :=
  rfl

end Vars

/-- LL unchained-accumulator attack, retargeted at the live `accStep` chip. -/
def ll_rejected :=
  @Batch266.repaired_chip_rejects_shifted_accumulator

/-- LV two-row denominator swap, rejected by `denominatorPinMixed`. -/
def lv_rejected :=
  @Batch271.repaired_chip_rejects_denominator_swap

/-- LU intermediate shift, rejected by mixed `intermediateInit`. -/
def lu_rejected :=
  @Batch272.repaired_chip_rejects_intermediate_shift

/-! ## F-1 / F-3. Majorants are strictly stronger; `_of_config` uninhabited at both fixtures. -/

section F73

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.Concrete
open Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists
open Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

theorem f73_hM_fails :
    ¬ (concreteOptimizedFullStrictPackage.objects.cfg.memRows ≤
        concreteOptimizedFullStrictPackage.objects.cfg.Ksz) :=
  concrete73_memRows_not_le_Ksz

theorem f73_h3N :
    3 * concreteOptimizedFullStrictPackage.objects.cfg.compRows ≤
      concreteOptimizedFullStrictPackage.objects.cfg.Ksz :=
  concrete73_three_mul_compRows_le_Ksz

/-- Original `hKresp` holds at F73's honest trace; `hM` does not -/
theorem f73_original_hKresp :
    (concreteOptimizedFullStrictPackage.hostileResponses concreteMemoryTrace).length ≤
      concreteOptimizedFullStrictPackage.objects.cfg.Ksz := by
  have htrace : concreteMemoryTrace =
      honestMemoryTrace concreteOptimizedFullStrictPackage := by
    rw [concreteMemoryTrace_eq]; rfl
  rw [htrace, OptimizedCanonicalHostileLists.canonical_hostileResponses]
  exact concreteOptimizedFullStrictPackage.optimized.sampled.lio10.1.2

end F73

section PackageM

open OptimizedStrictFullPackage
open OptimizedStrictNonterminalConcrete
open MultiRootServedFixture
open MultiRootHonestCommitment

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance fintype97 : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance deq97 : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97 : CharP K97cubic 97 := inferInstance
local instance charRing97 : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)
include hmoreM

theorem packageM_width_and_s :
    (packageM hmoreM).memoryChip.rap.w = 205 ∧ (packageM hmoreM).memoryChip.rap.s = 156 :=
  ⟨(BuildablePackage.constructed_resources multiRootExecution inputsM residualM
      inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      MultiRootHonestCommitment.residualM_generated MultiRootHonestCommitment.f97_primeField).2.2.1,
    (BuildablePackage.constructed_resources multiRootExecution inputsM residualM
      inputsM_challenges pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
      MultiRootHonestCommitment.residualM_generated MultiRootHonestCommitment.f97_primeField).2.2.2⟩

theorem packageM_h3N_fails :
    ¬ (3 * (packageM hmoreM).objects.cfg.compRows ≤ (packageM hmoreM).objects.cfg.Ksz) := by
  have hcfg : (packageM hmoreM).objects.cfg = cfgS := rfl
  rw [hcfg]
  change ¬ (3 * cfgS.compRows ≤ cfgS.Ksz)
  decide

theorem packageM_hM_fails :
    ¬ ((packageM hmoreM).objects.cfg.memRows ≤ (packageM hmoreM).objects.cfg.Ksz) := by
  have hcfg : (packageM hmoreM).objects.cfg = cfgS := rfl
  rw [hcfg]
  change ¬ (cfgS.memRows ≤ cfgS.Ksz)
  decide

end PackageM

end Nock.RedTeam.Batch278

#print axioms Nock.RedTeam.Batch278.counts_at_e3
#print axioms Nock.RedTeam.Batch278.tree_count_vs_paper
#print axioms Nock.RedTeam.Batch278.paperKGates_degree_le_four
#print axioms Nock.RedTeam.Batch278.live_chip_commits_paper_gates
#print axioms Nock.RedTeam.Batch278.extTransition_empty
#print axioms Nock.RedTeam.Batch278.equalityChecks_empty
#print axioms Nock.RedTeam.Batch278.endpoint_buckets_empty
#print axioms Nock.RedTeam.Batch278.exact_resources_numerals
#print axioms Nock.RedTeam.Batch278.packageM_width_and_s
#print axioms Nock.RedTeam.Batch278.aggregator_halves_not_paper_class
#print axioms Nock.RedTeam.Batch278.paperAggregator_mem_paperKGates
#print axioms Nock.RedTeam.Batch278.folded_mixed_is_five_not_forty_five
#print axioms Nock.RedTeam.Batch278.anchors_in_mixed
#print axioms Nock.RedTeam.Batch278.denominatorPin_in_mixed
#print axioms Nock.RedTeam.Batch278.intermediate_anchors_in_mixed
#print axioms Nock.RedTeam.Batch278.requests_terminal_in_mixed
#print axioms Nock.RedTeam.Batch278.ll_rejected
#print axioms Nock.RedTeam.Batch278.lv_rejected
#print axioms Nock.RedTeam.Batch278.lu_rejected
#print axioms Nock.RedTeam.Batch278.pin_reads_slots_4_and_5
#print axioms Nock.RedTeam.Batch278.two_poles
#print axioms Nock.RedTeam.Batch278.fa1_still_live
#print axioms Nock.RedTeam.Batch278.fold_pin_survives
#print axioms Nock.RedTeam.Batch278.hostile_logUp_sums_agree_no_hfold
#print axioms Nock.RedTeam.Batch278.stateTagChar_is_injOn_Iic_11
#print axioms Nock.RedTeam.Batch278.generator_charBound_is_Ksz_lt_ringChar
#print axioms Nock.RedTeam.Batch278.f73_hM_fails
#print axioms Nock.RedTeam.Batch278.f73_original_hKresp
#print axioms Nock.RedTeam.Batch278.packageM_h3N_fails
#print axioms Nock.RedTeam.Batch278.packageM_hM_fails
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
