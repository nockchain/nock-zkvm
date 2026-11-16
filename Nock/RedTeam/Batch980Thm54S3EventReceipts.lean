/-
  Nock/RedTeam/Batch980Thm54S3EventReceipts.lean

  * **§A — `rfl` receipts.**  `s3Window = ComputedWindow.window3` (the window the induction's
    `s3_pairs_separated` consumes); the join's structural helpers are the lifted
    `StrategyOfTracesLift.nounHead` / `nounTail`, which are the originals by `rfl` (re-checked here).
  * **§B — the package instance (rule 10 (i): the placement 2b-ii names, compiled).**
    `s3PairEventOfPkg P Qc Qm` is `S3PairEvent.s3PairEventOf` at `q := P.q`, `kroots := kMem`,
    `Λ := P.optimized.Λ`, the committed base envs `P.computeBaseEnv Qc` / `P.memoryBaseEnv Qm` and the
    claim `P.optimized.verifier.raw.claim`.
  * **§C — the round-0 read set at `(Qc, Qm)`.**  `s3PairEventOfPkg_preZ`: the instance is equal at any
    two compute traces agreeing on the B1 round-0 compute columns (`PreZAgreeOnC`) and any two memory
    traces agreeing on the memory round-0 columns (`PreZAgreeOn (memCC P)`), i.e. it is fixed before
    `z` is drawn.  The column lists are measured: compute `1..10, 302` (all round 0 by `decide`;
    positive control `compColRound 13 = 1`), memory `0, 1, 2, 180, 181` (all `memoryColRound = 0`).
  * **§D — positive controls.**  The per-row pair lists at concrete nodes: OP5 has 3 pairs, its third
    the two kid evaluations; OP6 has 3; OP0 has 1; and the row's carrier `S` IS read (two nodes
    differing only in `S` get different pairs under a served lookup that distinguishes exponents).
-/
import Nock.NockVMROM.Thm54.S3PairEvent
import Nock.NockVMROM.Thm54.ComputedWindow
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.PreSeedCensus
import Nock.NockVMROM.Thm54.DeployedStaging
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch980

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.S3PairEvent

/-! ## §A  `rfl` receipts -/

/-- The S3 window is `ComputedWindow.window3` (the window `s3_pairs_separated` consumes). -/
theorem s3Window_eq_window3 (M Λ : ℕ) : s3Window M Λ = ComputedWindow.window3 M Λ := rfl

theorem nounHead_eq (n : Noun) :
    StrategyOfTracesLift.nounHead n = StrategyOfTraces.nounHead n := rfl

theorem nounTail_eq (n : Noun) :
    StrategyOfTracesLift.nounTail n = StrategyOfTraces.nounTail n := rfl

/-! ## §B  The package instance -/

section Package

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

noncomputable def s3PairEventOfPkg
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  S3PairEvent.s3PairEventOf K P.q P.optimized.family.problem.cfg.kMem P.optimized.Λ
    (P.computeBaseEnv Qc) (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.memRows_pos
    P.optimized.verifier.raw.claim

theorem s3PairEventOfPkg_card_le
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (s3PairEventOfPkg P Qc Qm).card ≤
      Fintype.card K ^ 10 * S3PairEvent.s3PairWorkload P.strategy P.optimized.Λ := by
  have hcfg : P.optimized.family.problem.cfg =
      P.strategy.specializedCfg P.honestSeed P.honestSeed_ne P.honestAlpha
        P.optimized.objects.cfg.challenges.lam := by
    rw [P.optimized.family_cfg]
    exact (congrArg (fun x => x.cfg) P.honest_specialization).symm
  have hN : P.optimized.family.problem.cfg.compRows =
      (SemanticStrategy.computeSkeletonRows P.strategy.skeleton).length := by
    rw [hcfg]
    have h := (P.optimized.strategy_bindsAll P.honestSeed P.honestSeed_ne P.honestAlpha
      P.optimized.objects.cfg.challenges.lam).computeRows.length_eq
    rw [ExactExecution.computeRows_length] at h
    exact h.symm
  have hM : P.optimized.family.problem.cfg.memRows =
      (SemanticStrategy.memorySkeletonRows P.strategy.skeleton).length := by
    rw [hcfg]
    have h := (P.optimized.strategy_bindsAll P.honestSeed P.honestSeed_ne P.honestAlpha
      P.optimized.objects.cfg.challenges.lam).memoryRows.length_eq
    rw [ExactExecution.memoryRows_length] at h
    exact h.symm
  rw [S3PairEvent.s3PairWorkload_eq, ← hN, ← hM]
  exact S3PairEvent.s3PairEventOf_card_le _ _ _ _ _ _ _ _

/-! ## §C  The round-0 read set at `(Qc, Qm)` -/

/-- Positive control of the compute round map: column `13` (`𝕂` role `0`) is round `1`, so the
`decide` in `s3CompCols_round_zero` is not vacuous. -/
theorem compColRound_13 : PreZComputeCore.compColRound 13 = 1 := by decide

/-- The memory columns the served lookup reads are round `0` (`DeployedStaging.memoryColRound`). -/
theorem preZMemCols_round_zero :
    ∀ c ∈ PreZComputeCore.Served.preZMemCols, DeployedStaging.memoryColRound c = 0 := by
  decide

/-- Positive control of the memory round map: column `6` (`𝕂` role `0`) is NOT round `0`. -/
theorem memoryColRound_6_ne_zero : DeployedStaging.memoryColRound 6 ≠ 0 := by decide

/-- **The S3 event at the package is fixed before `z`**: equal at any two compute traces agreeing on
the round-0 compute columns and any two memory traces agreeing on the round-0 memory columns. -/
theorem s3PairEventOfPkg_preZ
    {Qc Qc' : Fin P.computeChip.rap.w → F[X]} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hC : PreZComputeCore.PreZAgreeOnC Qc Qc')
    (hMem : PreSeedCensus.PreZAgreeOn (PreSeedCensus.memCC P) Qm Qm') :
    s3PairEventOfPkg P Qc Qm = s3PairEventOfPkg P Qc' Qm' := by
  unfold s3PairEventOfPkg
  refine S3PairEvent.s3PairEventOf_congr K _ _ _ ?_ ?_ _ _
  · intro i c hc
    exact PreZComputeCore.envOfTrace_trace_congr hC _ _ _ _ (S3PairEvent.s3CompCols_round_zero c hc)
  · intro i c hc
    exact PreSeedCensus.preEnv_trace_congr P hMem i c (preZMemCols_round_zero c hc)

end Package

/-! ## §D  Positive controls on the per-row pairs -/

/-- A served lookup that distinguishes exponents. -/
def svC : MState → ℕ → Noun := fun _ k => Noun.atom k

def nodeAt (st : State) (S : ℕ) (kids : List (NTree S3Node)) : NTree S3Node :=
  .node ⟨st, S, Noun.atom 0, Noun.cell (Noun.atom 5) (Noun.atom 0), Noun.atom 0⟩ kids

def kidE (e : ℕ) : NTree S3Node := .node ⟨.s1, 0, Noun.atom 0, Noun.atom 0, Noun.atom e⟩ []

/-- OP5: three pairs, the third the two kid evaluations (the `hfaith` operands). -/
theorem op5_three_pairs :
    rowS3Pairs svC (nodeAt .s5 0 [kidE 7, kidE 8]) =
      [(Noun.cell (Noun.atom 5) (Noun.atom 0), Noun.cell (Noun.atom 5) (Noun.atom 1)),
       (Noun.atom 1, Noun.cell (Noun.atom 2) (Noun.atom 1)),
       (Noun.atom 7, Noun.atom 8)] := rfl

theorem op6_three_pairs : (rowS3Pairs svC (nodeAt .s6 0 [])).length = 3 := rfl

theorem op0_one_pair : (rowS3Pairs svC (nodeAt .s0 0 [])).length = 1 := rfl

/-- The carrier `S` is read: two OP0 nodes differing only in `S` have different S3 pairs. -/
theorem carrier_is_read : rowS3Pairs svC (nodeAt .s0 0 []) ≠ rowS3Pairs svC (nodeAt .s0 1 []) := by
  decide

end Nock.RedTeam.Batch980

#print axioms Nock.NockVMROM.Thm54.S3PairEvent.s3PairEventOf_card_le
#print axioms Nock.NockVMROM.Thm54.S3PairEvent.s3PairsOfEnvs_congr
#print axioms Nock.NockVMROM.Thm54.S3PairEvent.s3PairEventOf_preZ_compute
#print axioms Nock.RedTeam.Batch980.s3PairEventOfPkg_card_le
#print axioms Nock.RedTeam.Batch980.s3PairEventOfPkg_preZ
#print axioms Nock.RedTeam.Batch980.op5_three_pairs
#print axioms Nock.RedTeam.Batch980.carrier_is_read
