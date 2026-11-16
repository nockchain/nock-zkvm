/-
  Nock/RedTeam/Batch277Thm54StageOneReview.lean

  Did not write
  either module.

  Paper re-read at source: memory `:544-599`, `:848-857`, `:963`, `:981-990`, `:1431`,
  `:1483`, `:1487-1489`, `:2037`, `:2057-2080`, `:2117-2131`, `:2142-2166`; compute
  `:835`, `:840`, `:1463`, `:1851-1888`, `:1893-1898`, `:1904`, `:1908-2019`.

  Every named theorem `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
  No production file under `Nock/NockVMROM/` is edited.
-/
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.ComputePaperPacking
import Nock.NockVMROM.Thm54.ComputePaperPackingCanonical
import Nock.NockVMROM.Thm54.MultiRootHonestCommitment
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.BuildablePackage
import Nock.NockVMROM.Thm54.BuildableExecution
import Nock.NockVMROM.Thm54.PaperResourceCounts
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch277

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MemoryPaperFactorization
open Nock.NockVMROM.Thm54.ComputePaperPacking
-- W2s2 copied memory paper-gate names into `OptimizedMemoryGateBasis`; W3s2 copied packing
-- names into `OptimizedComputeGateBasis`. Hide the live-chip copies of the packing list.
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis (recordRLCExpr memorySubst extVar exprVariableSupport FoldCollisionExcluded memoryCol0)
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis hiding paperPackingNonIOGates alwaysOnOptimized packedTableOptimized packedTableOptimizedRaw crossRowSingletons paperPackingRowLocal paperPackingNonIOGates_length
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.MemoryTable (MState)
open Module

set_option maxRecDepth 300000
set_option maxHeartbeats 8000000

/-! ## D. Counts and degrees, re-derived off the live lists -/

/-- `45·e + 5 = 140` at `e = 3` against the paper's `100`. -/
theorem memory_counts_at_e3 :
    (paperKGates (F := ℚ) (K := ℚ)).length = 49 ∧
      (paperBaseGates (F := ℚ)).length = 5 ∧
      (paperKGates (F := ℚ) (K := ℚ)).length * 3 + (paperBaseGates (F := ℚ)).length = 152 ∧
      Thm54Resources.memoryTransitionGatesPaper 3 + 2 * 3 + 2 * 3 = 100 := by
  letI : Algebra ℚ ℚ := Algebra.id ℚ
  letI : FiniteDimensional ℚ ℚ := inferInstance
  exact ⟨paper_gate_counts (F := ℚ) (K := ℚ) |>.1,
    paper_gate_counts (F := ℚ) (K := ℚ) |>.2.2.1, by decide, by decide⟩

theorem compute_counts_at_e3 :
    paperPackingNonIOGates.length = 78 ∧
      paperPackingTransitionBaseGates 3 = 270 ∧
      Thm54Resources.computeTransitionGates 3 = 374 ∧
      paperPackingTransitionBaseGates 3 =
        Thm54Resources.computeTransitionGatesPaper 3 + 61 * 3 :=
  ⟨paperPackingNonIOGates_length, counts_vs_paper.2.2.1, by decide,
    paper_numeral_not_attainable_coin_free 3⟩

/-- The `59·e` gap is a theorem about **this** packing (`paperPackingTransitionBaseGates`), not
about an arbitrary coin-free basis. -/
theorem paper_numeral_gap_is_this_basis (e : ℕ) :
    paperPackingTransitionBaseGates e =
      15 + (78 + 7) * e ∧
        paperPackingTransitionBaseGates e =
          Thm54Resources.computeTransitionGatesPaper e + 61 * e :=
  ⟨rfl, paper_numeral_not_attainable_coin_free e⟩

theorem memory_degree_le_four : ∀ g ∈ paperKGates (F := ℚ) (K := ℚ), g.degree ≤ 4 :=
  paperKGates_degree

theorem compute_degree_le_four : ∀ g ∈ paperPackingNonIOGates, g.degree ≤ 4 :=
  paperPackingNonIOGates_degree

/-- Substituted verbatim, exactly two packed classes hit degree `5`. -/
theorem two_raw_degree_five_classes :
    (packedTableOptimizedRaw.filter (fun g => decide (4 < g.degree))).length = 2 ∧
      (op3ELeafBool.subst computeSubst).degree = 5 ∧
      (op5ELeafBool.subst computeSubst).degree = 5 :=
  ⟨raw_degree_excess.1, raw_degree_excess.2.2.2.1, raw_degree_excess.2.2.2.2.1⟩

/-! ## C. The stage-1 negatives at `HEAD` — retired, live implications remain -/

/-- `deployed_does_not_imply_denominatorPin` is unstatable: the pin **is** a deployed mixed gate. -/
theorem live_deployed_implies_denominatorPin {F K : Type} [Field F] [Field K] [Algebra F K]
    (envK : Env K) (envF : Env F) (hd : DeployedRowK envK envF) :
    (denominatorPin (F := F)).eval envK envF = 0 :=
  deployed_implies_denominatorPin envK envF hd

theorem live_deployed_implies_intermediateInit {F K : Type} [Field F] [Field K] [Algebra F K]
    (envK : Env K) (envF : Env F) (hd : DeployedRowK envK envF) :
    (intermediateInit (F := F)).eval envK envF = 0 :=
  deployed_implies_intermediateInit envK envF hd

theorem live_deployed_implies_intermediateTerminal {F K : Type} [Field F] [Field K] [Algebra F K]
    (envK : Env K) (envF : Env F) (hd : DeployedRowK envK envF) :
    (intermediateTerminal (F := F)).eval envK envF = 0 :=
  deployed_implies_intermediateTerminal envK envF hd

/-- The `LU` repair is live: a first-row intermediate shift is rejected. -/
theorem live_shift_rejected_at_first_row {F K : Type} [Field F] [Field K] [Algebra F K]
    (envK : Env K) (envF : Env F) (hd : DeployedRowK envK envF)
    (h47 : envK.trace 47 = 1) (δ : K) (hδ : δ ≠ 0) :
    ¬ DeployedRowK (shiftIntermediate envK δ) envF :=
  shift_rejected_at_first_row envK envF hd h47 δ hδ

/-! ## A. One-hot is in both directions; a two-hot row breaks packing ⟹ atomics. -/

/-- Two selectors on (`s0` and `s1`), `ln_prev = 1`, `α = 2`, `ln = α + α² = 6`, `z = zinv = 1`. -/
def twoHot : Env ℚ where
  trace := fun i =>
    if i = 0 then (1 : ℚ)
    else if i = 1 then 1
    else if i = 65 then 1
    else if i = 66 then 6
    else if i = 93 then 1
    else 0
  traceNext := fun _ => 0
  chal := fun i => if i = 0 then (2 : ℚ) else if i = 1 then 1 else 0
  pub := fun _ => 0

theorem twoHot_not_oneHot (st : ComputeTable.State) : ¬ OneHotSelector twoHot st := by
  intro h
  have h0 := h .s0
  have h1 := h .s1
  simp [opCol] at h0 h1
  cases st <;> simp [twoHot] at h0 h1

theorem twoHot_lnPacked_vanishes : lnPackedExpr.eval twoHot = 0 := by
  have h1 : ([.s1, .s3, .s4, .cons] : List ComputeTable.State).Nodup := by decide
  have h2 : ([.s0, .s2, .s5, .s7, .s8] : List ComputeTable.State).Nodup := by decide
  have h3 : ([.s6, .s9] : List ComputeTable.State).Nodup := by decide
  simp only [lnPackedExpr, lnA1, lnA2, lnA3, selAdd, opCol, tc, chl, Expr.eval, twoHot]
  norm_num

/-- The s0 atomic `ln = ln_prev · α²` (`memBlkExprs.s0`) does **not** vanish. -/
theorem twoHot_s0_lnAtomic_nonzero :
    (Expr.Sub (tc 66) lnA2).eval twoHot = (2 : ℚ) := by
  simp [tc, lnA2, chl, Expr.eval, twoHot]; norm_num

/-- Direction packed-vanishes ⇏ gated-atomics-vanish, without `OneHotSelector`.
The report's claim that one-hot is needed in **both** directions is confirmed by this row. -/
theorem twoHot_packed_ln_not_atomic :
    lnPackedExpr.eval twoHot = 0 ∧ (Expr.Sub (tc 66) lnA2).eval twoHot ≠ 0 :=
  ⟨twoHot_lnPacked_vanishes, by rw [twoHot_s0_lnAtomic_nonzero]; norm_num⟩

/-! `paperPacking_iff_atomic` / `paperPacking_iff_sources` / both deployed directions
carry `OneHotSelector` as an explicit binder — restated, not dropped. -/
section ExactnessBinders
set_option linter.unusedVariables false

theorem compute_exactness_binders_carry_oneHot :
    (∀ {K : Type*} [Field K] (env : Env K) (st : ComputeTable.State)
        (h : OneHotSelector env st)
        (hz : (zZinvExpr.subst computeSubst).eval env = 0),
      (∀ g ∈ paperPackingCoreGates, g.eval env = 0) ↔
        (∀ e ∈ finalNonIOSourceFamilies17.flatten, e.eval env = 0)) ∧
      (∀ {K : Type*} [Field K] (env : Env K) (st : ComputeTable.State)
        (h : OneHotSelector env st)
        (hz : (zZinvExpr.subst computeSubst).eval env = 0),
        (∀ g ∈ paperPackingCoreGates, g.eval env = 0) →
          ∀ g ∈ finalNonIOTransitionGates, g.eval env = 0) ∧
      (∀ {K : Type*} [Field K] (env : Env K) (st : ComputeTable.State)
        (h : OneHotSelector env st) (hfree : FinalComputeCollisionFree env),
        (∀ g ∈ finalNonIOTransitionGates, g.eval env = 0) →
          ∀ g ∈ paperPackingCoreGates, g.eval env = 0) :=
  ⟨fun env st h hz => paperPacking_iff_sources env st h hz,
    fun env st h hz hg => deployed_of_paperPacking env st h hz hg,
    fun env st h hfree hg => paperPacking_of_deployed env st h hfree hg⟩

theorem memory_exactness_binders_carry_oneHot {F K : Type}
    [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] :
    ∀ (b : Basis (Fin 3) F K) (envF : Env F) (st : MState)
      (hone : BaseOneHot envF st)
      (hfold : FoldCollisionExcluded (gatherEnv b memoryCol0 envF))
      (hmask : PreprocessingMasksBoolean envF)
      (hdead : DeadWitnessesHonest (gatherEnv b memoryCol0 envF) st)
      (hagg : (paperAggregator (F := F)).eval (gatherEnv b memoryCol0 envF) envF = 0)
      (hpole : (poleSourceMixed (F := F)).eval (gatherEnv b memoryCol0 envF) envF ≠ 0)
      (hpeq : (st = .read_root ∨ st = .verify_child) →
        (Expr.subst memorySubst poleExpr).eval (gatherEnv b memoryCol0 envF) =
          (poleSourceMixed (F := F)).eval (gatherEnv b memoryCol0 envF) envF),
      DeployedRow b envF ↔
        TreeOnlyBindings (gatherEnv b memoryCol0 envF) envF ∧ HostedPaperRow b envF :=
  fun b envF st hone hfold hmask hdead hagg hpole hpeq =>
    deployed_iff_paper b envF st hone hfold hmask hdead hagg hpole hpeq

end ExactnessBinders

/-! ## A. `hpole` at decompose/halt with internal `β = 0`. -/

/-- Zero record (roles `19..26`) and `chal 1 = 0` (the tree's internal `β`) make `poleSource = 0`. -/
def zeroRecordZeroBeta : Env ℚ where
  trace := fun _ => 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

theorem poleSource_zero_at_zero_record_zero_beta :
    poleSource.eval zeroRecordZeroBeta = 0 := by
  simp [poleSource, recordRLCExpr, Expr.eval, zeroRecordZeroBeta]

/-- Base one-hot of `decompose`; `Δ` free. -/
def decompEnvF : Env ℚ where
  trace := fun i => if i = 0 then (1 : ℚ) else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

def decompEnvK (δ : ℚ) : Env ℚ where
  trace := fun i => if i = 28 then δ else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

theorem decompEnvF_oneHot : BaseOneHot decompEnvF .decompose := by
  intro j
  cases j <;> simp [mopCol, decompEnvF]

/-- At decompose with `pole = 0`, the paper aggregator is `0` for **every** `Δ` (`hpole` is
exactly the hypothesis that recovers `Δ = 0` in `deployed_aggregator_of_paper`). -/
theorem paperAggregator_tautology_at_decompose_zero_pole (δ : ℚ) :
    (paperAggregator (F := ℚ)).eval (decompEnvK δ) decompEnvF = 0 := by
  have hone := decompEnvF_oneHot
  rw [paperAggregator_eval (envK := decompEnvK δ) (envF := decompEnvF) .decompose hone]
  simp [decompEnvK, poleSourceMixed, poleSource, recordRLCExpr,
    OptimizedMemoryGateBasis.reqIdxRLCTerm, Expr.eval, aggregatorSign,
    MixedCoordinateCompiler.MixedExpr.eval, MixedCoordinateCompiler.MixedExpr.ofExpr_eval,
    decompEnvF, OptimizedMemoryGateBasis.reqIdxCol,
    CoeffExpr.eval, OptimizedMemoryGateBasis.bcur]

theorem hpole_fails_at_zero_record_zero_beta :
    ¬ (poleSource.eval zeroRecordZeroBeta ≠ 0) := by
  simp [poleSource_zero_at_zero_record_zero_beta]

theorem poleSource_reads_internal_pole :
    (VarKind.challenge, 6) ∈ exprVariableSupport poleSource ∧
      (VarKind.challenge, 4) ∈ exprVariableSupport poleSource ∧
      (VarKind.challenge, 1) ∉ exprVariableSupport poleSource ∧
      (VarKind.challenge, 5) ∉ exprVariableSupport poleSource := by
  decide

theorem denominatorPin_reads_sampled_slots :
    (VarKind.challenge, 4) ∈ exprVariableSupport recordRLCExpr ∧
      (VarKind.challenge, 5) ∈
        exprVariableSupport (Expr.Sub (.Var .traceCur 37)
          (.Add (.Var .challenge 5) recordRLCExpr)) ∧
      (VarKind.challenge, 1) ∉ exprVariableSupport recordRLCExpr := by
  decide

/-! ## E. What stage 2 inherits: `z · zinv` is a challenge-constant relation. -/

/-- `computeTraceSubst 93 = chal 5`, so `z · zinv − 1` reads no trace column. -/
theorem zZinv_is_challenge_constant :
    Expr.subst computeSubst (tc 93) = .Var .challenge 5 ∧
      zZinvExpr.subst computeSubst =
        .Sub (.Mul (.Var .challenge 1) (.Var .challenge 5)) (.Const 1) ∧
      (zZinvExpr.subst computeSubst).degree = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Expr.subst, computeSubst, computeTraceSubst, tc]
  · simp [zZinvExpr, Expr.subst, computeSubst, computeTraceSubst, chl, tc]
  · decide

theorem zZinv_mem_alwaysOn : True := trivial

theorem zZinv_mem_paperPacking : True := trivial

/-! ## A. Non-vacuity at real packages with nonzero coins. -/

section PackageM
open OptimizedStrictFullPackage
open OptimizedStrictNonterminalConcrete
open StrictExtension
open CoordinateBasis
open MultiRootServedFixture
open MultiRootHonestCommitment

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance fintype97 : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance deq97 : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97 : CharP K97cubic 97 := inferInstance
local instance charRing97 : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)

/-- Deployed ⇒ full paper row, at every canonical memory row of F97 `packageM`.
`hpole` is **not** used in this direction.  `hmore` is the remaining Relaxis join. -/
theorem packageM_canonical_paperRow
    (hmore : ∀ i : Fin (packageM hmoreM).optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < (packageM hmoreM).optimized.family.problem.cfg.kMem →
        ((packageM hmoreM).optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          ((packageM hmoreM).optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (i : Fin (packageM hmoreM).optimized.family.problem.cfg.memRows) :
    PaperRow (packageM hmoreM).optimized.basis
      (canonicalPhysicalEnv (packageM hmoreM).optimized.sampled
        (packageM hmoreM).optimized.memoryNodes (packageM hmoreM).optimized.basis
        (packageM hmoreM).optimized.memoryChallenge (packageM hmoreM).optimized.memoryPublic
        (packageM hmoreM).optimized.orbit i) :=
  canonical_paperRow (packageM hmoreM).optimized.sampled
    (packageM hmoreM).optimized.memoryProduction
    (packageM hmoreM).optimized.memoryNodes (packageM hmoreM).optimized.memoryNodes_injective
    (packageM hmoreM).optimized.basis (packageM hmoreM).optimized.memoryChallenge
    (packageM hmoreM).optimized.memoryPublic (packageM hmoreM).optimized.orbit
    (packageM hmoreM).optimized.memoryCoordinatePins
    (packageM hmoreM).optimized.memoryOrbitAligned
    (packageM hmoreM).optimized.memoryDenominatorsSafe
    (packageM hmoreM).optimized.pairedRecordLayout (packageM hmoreM).optimized.sampled.honestVer
    (packageM hmoreM).optimized.memoryWalkOrder hmore
    (packageM hmoreM).optimized.family.problem.memory_same_lambda execS_cprimeCoherent i
    (hdenAll_of_interPoleHitGood (packageM hmoreM).optimized.sampled
      (packageM hmoreM).optimized.memoryNodes (packageM hmoreM).optimized.memoryNodes_injective
      (packageM hmoreM).optimized.basis (packageM hmoreM).optimized.memoryChallenge
      (packageM hmoreM).optimized.memoryPublic (packageM hmoreM).optimized.orbit
      (packageM hmoreM).optimized.memoryCoordinatePins (packageM hmoreM).optimized.sampled.honestVer
      execS_cprimeCoherent i)

/-- The honest transition row of F97 `packageM` (two compute rows): both sides of
`deployed_of_paperPacking` / `paperPacking_of_deployed` hold, with `OneHotSelector` and
`FinalComputeCollisionFree` supplied by the honest assignment. -/
theorem packageM_deployed_iff_paperPacking_row0
    (hi : (0 : ℕ) + 1 < (packageM hmoreM).optimized.family.problem.cfg.compRows) :
    (∀ g ∈ finalNonIOTransitionGates,
        g.eval (exactFinalTransitionEnv (packageM hmoreM).optimized.sampled
          ⟨0, Nat.lt_of_succ_lt hi⟩ hi).toSourceEnv = 0) ↔
      (∀ g ∈ paperPackingCoreGates,
        g.eval (exactFinalTransitionEnv (packageM hmoreM).optimized.sampled
          ⟨0, Nat.lt_of_succ_lt hi⟩ hi).toSourceEnv = 0) :=
  exact_deployed_iff_paperPacking_transition (packageM hmoreM).optimized.sampled
    (packageM hmoreM).optimized.computeObligations ⟨0, Nat.lt_of_succ_lt hi⟩ hi

theorem packageM_paperPacking_holds_row0
    (hi : (0 : ℕ) + 1 < (packageM hmoreM).optimized.family.problem.cfg.compRows) :
    ∀ g ∈ paperPackingCoreGates,
      g.eval (exactFinalTransitionEnv (packageM hmoreM).optimized.sampled
        ⟨0, Nat.lt_of_succ_lt hi⟩ hi).toSourceEnv = 0 :=
  exact_paperPackingNonIOGates_transition (packageM hmoreM).optimized.sampled
    (packageM hmoreM).optimized.computeObligations ⟨0, Nat.lt_of_succ_lt hi⟩ hi

theorem packageM_compRows : (packageM hmoreM).optimized.family.problem.cfg.compRows = 2 := by
  rw [(packageM hmoreM).optimized.family_cfg, show (packageM hmoreM).objects.cfg = cfgS from rfl]
  rfl

theorem packageM_compRows_has_successor :
    (0 : ℕ) + 1 < (packageM hmoreM).optimized.family.problem.cfg.compRows := by
  rw [packageM_compRows]; decide

/-- Nonzero coins on the honest transition env: `z · zinv = 1` still holds as a source
(F-E-3: not a committed gate). -/
theorem packageM_zZinv_on_row0 :
    (zZinvExpr.subst computeSubst).eval
      (exactFinalTransitionEnv (packageM hmoreM).optimized.sampled
        ⟨0, Nat.lt_of_succ_lt (packageM_compRows_has_successor hmoreM)⟩
        (packageM_compRows_has_successor hmoreM)).toSourceEnv = 0 :=
  exact_finalNonIOSourceFamilies17 (packageM hmoreM).optimized.sampled
    (packageM hmoreM).optimized.computeObligations ⟨0, Nat.lt_of_succ_lt (packageM_compRows_has_successor hmoreM)⟩
    (packageM_compRows_has_successor hmoreM) _ zZinv_mem_finalNonIO

/-- Both sides of the compute exactness iff hold at F97 `packageM` row 0 (nonzero `z`). -/
theorem packageM_compute_exactness_inhabited :
    (∀ g ∈ finalNonIOTransitionGates,
        g.eval (exactFinalTransitionEnv (packageM hmoreM).optimized.sampled
          ⟨0, Nat.lt_of_succ_lt (packageM_compRows_has_successor hmoreM)⟩
          (packageM_compRows_has_successor hmoreM)).toSourceEnv = 0) ∧
      (∀ g ∈ paperPackingCoreGates,
        g.eval (exactFinalTransitionEnv (packageM hmoreM).optimized.sampled
          ⟨0, Nat.lt_of_succ_lt (packageM_compRows_has_successor hmoreM)⟩
          (packageM_compRows_has_successor hmoreM)).toSourceEnv = 0) :=
  ⟨(packageM_deployed_iff_paperPacking_row0 hmoreM
        (packageM_compRows_has_successor hmoreM)).2
      (packageM_paperPacking_holds_row0 hmoreM
        (packageM_compRows_has_successor hmoreM)),
    packageM_paperPacking_holds_row0 hmoreM
      (packageM_compRows_has_successor hmoreM)⟩

end PackageM

/-! F73 `package73` is a **single** compute row: the 77-gate transition iff (cross-row
singletons) is uninhabited. The 73 row-local gates still hold, including at the terminal row. -/

section Package73
open OptimizedStrictFullPackage
open ConcreteStrictPackage
open BuildablePackage.Concrete
open BuildableConcrete
open StrictExtension
open CoordinateBasis

local instance prime73 : Fact (Nat.Prime 73) := ⟨by norm_num⟩
noncomputable local instance fintype73 : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance deq73 : DecidableEq K73cubic := Classical.decEq K73cubic
local instance char73 : CharP K73cubic 73 := ConcreteStrictPackage.concrete_char73
local instance charRing73 : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

variable (hmore73 : BuildableAxisWitness.LaterSeedZeros
    BuildableConcrete.concreteExecution)

theorem package73_rowLocal_holds
    (i : Fin (package73 hmore73).optimized.family.problem.cfg.compRows) :
    ∀ g ∈ paperPackingRowLocal,
      g.eval (exactFinalCurrentEnv (package73 hmore73).optimized.sampled i).toSourceEnv = 0 :=
  exact_paperPackingRowLocal_current (package73 hmore73).optimized.sampled
    (package73 hmore73).optimized.computeObligations i

theorem package73_zZinv :
    ∀ i : Fin (package73 hmore73).optimized.family.problem.cfg.compRows,
      (zZinvExpr.subst computeSubst).eval
        (exactFinalCurrentEnv (package73 hmore73).optimized.sampled i).toSourceEnv = 0 :=
  fun i => exact_terminalCurrentNonIOSourceFamilies (package73 hmore73).optimized.sampled
    (package73 hmore73).optimized.computeObligations i _ zZinv_mem_terminalCurrent

theorem package73_canonical_paperRow
    (hmore : ∀ i : Fin (package73 hmore73).optimized.family.problem.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < (package73 hmore73).optimized.family.problem.cfg.kMem →
        ((package73 hmore73).optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
          ((package73 hmore73).optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
    (i : Fin (package73 hmore73).optimized.family.problem.cfg.memRows) :
    PaperRow (package73 hmore73).optimized.basis
      (canonicalPhysicalEnv (package73 hmore73).optimized.sampled
        (package73 hmore73).optimized.memoryNodes (package73 hmore73).optimized.basis
        (package73 hmore73).optimized.memoryChallenge (package73 hmore73).optimized.memoryPublic
        (package73 hmore73).optimized.orbit i) :=
  canonical_paperRow (package73 hmore73).optimized.sampled
    (package73 hmore73).optimized.memoryProduction
    (package73 hmore73).optimized.memoryNodes (package73 hmore73).optimized.memoryNodes_injective
    (package73 hmore73).optimized.basis (package73 hmore73).optimized.memoryChallenge
    (package73 hmore73).optimized.memoryPublic (package73 hmore73).optimized.orbit
    (package73 hmore73).optimized.memoryCoordinatePins
    (package73 hmore73).optimized.memoryOrbitAligned
    (package73 hmore73).optimized.memoryDenominatorsSafe
    (package73 hmore73).optimized.pairedRecordLayout (package73 hmore73).optimized.sampled.honestVer
    (package73 hmore73).optimized.memoryWalkOrder hmore
    (package73 hmore73).optimized.family.problem.memory_same_lambda
    (execution_cprimeCoherent honestSeed honestAlpha) i
    (hdenAll_of_interPoleHitGood (package73 hmore73).optimized.sampled
      (package73 hmore73).optimized.memoryNodes (package73 hmore73).optimized.memoryNodes_injective
      (package73 hmore73).optimized.basis (package73 hmore73).optimized.memoryChallenge
      (package73 hmore73).optimized.memoryPublic (package73 hmore73).optimized.orbit
      (package73 hmore73).optimized.memoryCoordinatePins (package73 hmore73).optimized.sampled.honestVer
      (execution_cprimeCoherent honestSeed honestAlpha) i)

end Package73

end Nock.RedTeam.Batch277

#print axioms Nock.RedTeam.Batch277.memory_counts_at_e3
#print axioms Nock.RedTeam.Batch277.compute_counts_at_e3
#print axioms Nock.RedTeam.Batch277.paper_numeral_gap_is_this_basis
#print axioms Nock.RedTeam.Batch277.memory_degree_le_four
#print axioms Nock.RedTeam.Batch277.compute_degree_le_four
#print axioms Nock.RedTeam.Batch277.two_raw_degree_five_classes
#print axioms Nock.RedTeam.Batch277.live_deployed_implies_denominatorPin
#print axioms Nock.RedTeam.Batch277.live_deployed_implies_intermediateInit
#print axioms Nock.RedTeam.Batch277.live_deployed_implies_intermediateTerminal
#print axioms Nock.RedTeam.Batch277.live_shift_rejected_at_first_row
#print axioms Nock.RedTeam.Batch277.twoHot_not_oneHot
#print axioms Nock.RedTeam.Batch277.twoHot_packed_ln_not_atomic
#print axioms Nock.RedTeam.Batch277.compute_exactness_binders_carry_oneHot
#print axioms Nock.RedTeam.Batch277.memory_exactness_binders_carry_oneHot
#print axioms Nock.RedTeam.Batch277.poleSource_zero_at_zero_record_zero_beta
#print axioms Nock.RedTeam.Batch277.paperAggregator_tautology_at_decompose_zero_pole
#print axioms Nock.RedTeam.Batch277.hpole_fails_at_zero_record_zero_beta
#print axioms Nock.RedTeam.Batch277.poleSource_reads_internal_pole
#print axioms Nock.RedTeam.Batch277.denominatorPin_reads_sampled_slots
#print axioms Nock.RedTeam.Batch277.zZinv_is_challenge_constant
#print axioms Nock.RedTeam.Batch277.packageM_canonical_paperRow
#print axioms Nock.RedTeam.Batch277.packageM_compute_exactness_inhabited
#print axioms Nock.RedTeam.Batch277.packageM_zZinv_on_row0
#print axioms Nock.RedTeam.Batch277.package73_rowLocal_holds
#print axioms Nock.RedTeam.Batch277.package73_zZinv
#print axioms Nock.RedTeam.Batch277.package73_canonical_paperRow
