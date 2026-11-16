/-
  Nock/NockVMROM/Thm54/P8Core/MemoryInternalPole.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.MemoryInternalPole`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/MemoryInternalPole.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.P8Core.OptimizedMemoryHostileAccumulator
import Nock.NockVMROM.Thm54.P8Core.PairedRecordCountedEvent
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54

namespace MemoryInternalPole

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open OptimizedMemoryHostileAccumulator
open MemoryPaperFactorization (paper_to_deployed BaseOneHot TreeOnlyBindings
  PreprocessingMasksBoolean DeadWitnessesHonest HostedPaperRow DeployedRow)
open StrictExtension
open OptimizedStrictFullPackage
open OptimizedStrictPackage
open PairedRecordCountedEvent
open Module
open scoped Polynomial

noncomputable section

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable [Fintype F] [Fintype K] [DecidableEq F] [DecidableEq K] [CharP K (ringChar K)]

/-- Sampled `(γ, interPole)` at memory slots `4`/`6`. -/
def chipInterCoins (envK : Env K) : FiniteIO.IOCoins K :=
  ⟨envK.chal 4, envK.chal 6⟩

def rowRecord (envK : Env K) (envF : Env F) : Fin 10 → K :=
  OptimizedMemoryHostileAccumulator.rowRecord envK envF

def rowDelta (envK : Env K) : K := envK.trace 28 - envK.trace 27

theorem poleSource_eq_compress (envK : Env K) (envF : Env F) :
    (poleSourceMixed (F := F)).eval envK envF =
      FiniteIO.compress (chipInterCoins envK) (rowRecord envK envF) := by
  rw [rowRecord, OptimizedMemoryHostileAccumulator.rowRecord_eq_memRowRecord10,
    OptimizedMemoryHostileAccumulator.memRowRecord10, FiniteIO.compress,
    RecordCarrier.rlc_withExp]
  simp [poleSourceMixed, poleSource, recordRLCExpr, reqIdxRLCTerm, reqIdxCol, MixedExpr.eval,
    MixedExpr.ofExpr_eval, Expr.eval, bcur, CoeffExpr.eval, chipInterCoins,
    OptimizedMemoryHostileAccumulator.memRowRecord, Walk.rlc]
  rw [Fin.sum_univ_succ]
  simp [Fin.sum_univ_eight]
  ring

theorem paperAggregator_eval_raw (envK : Env K) (envF : Env F) :
    (paperAggregator (F := F)).eval envK envF =
      (poleSourceMixed (F := F)).eval envK envF * (envK.trace 28 - envK.trace 27) -
        (algebraMap F K (envF.trace 2) - algebraMap F K (envF.trace 3)) := by
  simp [paperAggregator, MixedExpr.eval, MixedExpr.ofExpr_eval, bcur, CoeffExpr.eval]

def AggregatorAt (envK : Env K) (envF : Env F) (pole γ : K) : Prop :=
  (pole + Walk.rlc γ (rowRecord envK envF)) * (envK.trace 28 - envK.trace 27) =
    algebraMap F K (envF.trace 2) - algebraMap F K (envF.trace 3)

theorem aggregatorAt_of_paperAggregator (envK : Env K) (envF : Env F)
    (h : (paperAggregator (F := F)).eval envK envF = 0) :
    AggregatorAt envK envF (chipInterCoins envK).pole (chipInterCoins envK).gamma := by
  have hraw := paperAggregator_eval_raw (F := F) envK envF
  rw [poleSource_eq_compress] at hraw
  simpa [AggregatorAt, FiniteIO.compress, chipInterCoins] using sub_eq_zero.mp (hraw.symm.trans h)

theorem delta_eq_signed_inv (envK : Env K) (envF : Env F) (pole γ : K)
    (hagg : AggregatorAt envK envF pole γ)
    (hden : pole + Walk.rlc γ (rowRecord envK envF) ≠ 0) :
    rowDelta envK =
      (algebraMap F K (envF.trace 2) - algebraMap F K (envF.trace 3)) *
        (pole + Walk.rlc γ (rowRecord envK envF))⁻¹ := by
  have hmul : (pole + Walk.rlc γ (rowRecord envK envF)) * rowDelta envK =
      algebraMap F K (envF.trace 2) - algebraMap F K (envF.trace 3) := by
    simpa [AggregatorAt, rowDelta] using hagg
  exact (eq_mul_inv_iff_mul_eq₀ hden).mpr (by rw [mul_comm]; exact hmul)

def rowReadsOf (envF : Env F) (envK : Env K) : List (Fin 10 → K) :=
  if envF.trace 2 = 1 then [rowRecord envK envF] else []

def rowVerifiesOf (envF : Env F) (envK : Env K) : List (Fin 10 → K) :=
  if envF.trace 3 = 1 then [rowRecord envK envF] else []

theorem rowReadsOf_length_le (envF : Env F) (envK : Env K) :
    (rowReadsOf envF envK).length ≤ 1 := by
  unfold rowReadsOf; split_ifs <;> simp

theorem rowVerifiesOf_length_le (envF : Env F) (envK : Env K) :
    (rowVerifiesOf envF envK).length ≤ 1 := by
  unfold rowVerifiesOf; split_ifs <;> simp

section Deployed

theorem paperAggregator_mem (b : Basis (Fin 3) F K) :
    paperAggregator (F := F) ∈ mixedTransitionGates (K := K) b := by
  simp [mixedTransitionGates, paperKGates, paperKGatesCore, rapMemGates]

variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
variable (Qm : Fin P.memoryChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
include hsat
omit hsat
include hsat
omit hsat

theorem req_denom_ne_of_not_hit {m : ℕ} {records : FiniteIO.PreChallengeRecords K m}
    (coins : FiniteIO.IOCoins K)
    (hhit : coins.pole ∉ FiniteIO.IOPoleHitEvent records coins.gamma) :
    ∀ i, coins.pole + FiniteIO.reqVals records coins.gamma i ≠ 0 := by
  intro i h0
  refine hhit ?_
  simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨records.requests.get i, List.mem_append_left _ (List.get_mem _ _),
    by simpa [FiniteIO.reqVals] using h0⟩

omit hsat in
theorem resp_denom_ne_of_not_hit {m : ℕ} {records : FiniteIO.PreChallengeRecords K m}
    (coins : FiniteIO.IOCoins K)
    (hhit : coins.pole ∉ FiniteIO.IOPoleHitEvent records coins.gamma) :
    ∀ j, coins.pole + FiniteIO.respVals records coins.gamma j ≠ 0 := by
  intro j h0
  refine hhit ?_
  simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨records.responses.get j, List.mem_append_right _ (List.get_mem _ _),
    by simpa [FiniteIO.respVals] using h0⟩

end Deployed

end

end MemoryInternalPole

end Nock.NockVMROM.Thm54
