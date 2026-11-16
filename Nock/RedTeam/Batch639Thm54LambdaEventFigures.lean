/-
  Nock/RedTeam/Batch639Thm54LambdaEventFigures.lean

  **Lane `lambda-event` (the THIRTIETH move): R3 (the bit figures at the consumed bound,
  worst case) and R5 composed at the compiler's package.**.

  * **R3.**  The consumed bound after the move prices the λ-event inside `p8Work` (`workload` carries
    `fixedFormRWorkload`, `≤ M·(3N + 130)` at worst case) and `pricedWalkWork` lost the slack
    `M + 3N + 130`.  `RealProgramSoundness.hostile_soundness_formR_at_two_pow_31` (`122`) and
    `…_two_pow_32` (`120`) take `p8Work ≤ p8Majorant R M Λ A + M·(3R + 130)`;
    `hostileSizeWorkFormR_not_lt_cardK_prePair` shows `184 − 2r` is the best this numerator gives.  The
    pre-move figures still hold (the bound got smaller): `figures_without_formR_still_hold`.  `123`
    is untouched (`paper_configuration_123_untouched`, the same theorem as before the move).
  * **The slack is gone** (`pricedWalkWork_no_slack`): `pricedWalkWork N M` is the six walk summands.
  * **R5 composed** (`honest_fixedFormRWorkload_le`): for a production strategy whose timestamp
    strategy is an honest commitment's (`HonestCommitment.Data.timestampStrategy`, the compiler
    route's), `CertInRange` holds at every seed (`Batch638.package_certInRange`), so the numeral
    needs no premise beyond `formRN K = 64` and the row majorants: `fixedFormRWorkload ≤ M·(3N + 130)`.
    (The `rfl` identification with `GenericHonestPackage.packageOf …`'s strategy times out at
    `whnf`; it is carried as `htime`.)
-/
import Nock.RedTeam.Batch638Thm54LambdaEventReceipts

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Nock.RedTeam.Batch639

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.TemplateAxisCounting

noncomputable section

/-! ## R3 -/

/-- **122 bits at `2^31`, worst-case λ-event summand.** -/
theorem figure_122 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_formR_at_two_pow_31 R M Λ A p8Work hR hM hΛ hA
    (hp8.trans (Nat.le_add_right _ _))

/-- **120 bits at `2^32`, worst-case λ-event summand.** -/
theorem figure_120 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ A + M * (3 * R + 130)) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_formR_at_two_pow_32 R M Λ A p8Work hR hM hΛ hA
    (hp8.trans (Nat.le_add_right _ _))

/-- The figure is tight for this numerator: one more bit fails at every `r`. -/
theorem figure_tight (r b : ℕ) (hb : 2 * r + b = 184) :
    ¬ ((453 * (2 ^ r * 2 ^ r) + 404 * 2 ^ r + 28) * 2 ^ (b + 1) < 2 * cardKGold) :=
  hostileSizeWorkFormR_not_lt_cardK_prePair r b hb

/-- The pre-move statements still hold at the consumed bound (it only shrank). -/
theorem figures_without_formR_still_hold (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_for_real_programs_at_two_pow_31 R M Λ A p8Work hR hM hΛ hA hp8

/-- `123` at the paper configuration: the same theorem, untouched by the move. -/
theorem paper_configuration_123_untouched (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 123 :=
  hostile_soundness_at_paper_configuration p8Work ioWork hp8 hio

/-- **The slack `pwAccountingWork' 64 N M` left `pricedWalkWork`.** -/
theorem pricedWalkWork_no_slack (N M : ℕ) :
    pricedWalkWork N M =
      ComputeWalkRootEvents.walkRootBound N +
        WalkTilingEvents.computeTilingBound N +
        WalkTilingEvents.memoryTilingBound M +
        WalkPrefixGammaEvents.computePrefixGammaBound N +
        WalkPrefixGammaEvents.memoryPrefixGammaBound M +
        WalkForestPrefixAlphaEvents.memoryForestAlphaBound M := rfl

/-- The removed slack was the `kMem = 1` instance; the new summand's worst case is `M` copies
(`M·(3N+130) = M + M·(3N+129)` vs `M + 3N + 130`). -/
theorem summand_vs_removed_slack (N M : ℕ) (hM : 1 ≤ M) :
    pwAccountingWork' 64 N M ≤ M * (3 * N + 130) + 1 := by
  simp only [pwAccountingWork']
  nlinarith

/-! ## R5 composed at the generator's package -/

section Package

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [Fintype F]

/-- The honest commitment's strategy publishes `D.executionTemplate z` at seed `z`. -/
theorem timestampStrategy_afterSeed {E : BuildableNockExecution F K}
    (D : HonestCommitment.Data E) (z : K) (hz : z ≠ 0) :
    (D.timestampStrategy.afterSeed ⟨z, hz⟩).executionTemplate = D.executionTemplate z := rfl

/-- **R5 composed:** for any production strategy whose timestamp strategy is an honest
commitment's (the package strategy of the compiler route, `HonestCommitment.Data.timestampStrategy`),
the λ-event summand is `≤ M·(3N + 130)` with no `CertInRange` premise. -/
theorem honest_fixedFormRWorkload_le {E : BuildableNockExecution F K}
    (D : HonestCommitment.Data E) (T : ProductionP8Containment.ProductionStrategy F K)
    (hb : T.BindsAll)
    (htime : T.verifier.raw.timestamp = D.timestampStrategy)
    (hn : formRN K = 64) (N M : ℕ)
    (hN : (SemanticStrategy.computeSkeletonRows T.skeleton).length ≤ N)
    (hM : (SemanticStrategy.memorySkeletonRows T.skeleton).length ≤ M) :
    ProductionP8Containment.fixedFormRWorkload T ≤ M * (3 * N + 130) := by
  refine Batch638.fixedFormRWorkload_le_64 T hb ?_ hn N M hN hM
  intro z hz i
  unfold ProductionAxisStructureVerifier.committedTemplate at ⊢
  revert i
  rw [htime]
  intro i
  exact Batch638.package_certInRange D z i

end Package

end

end Nock.RedTeam.Batch639

#print axioms Nock.RedTeam.Batch639.figure_122
#print axioms Nock.RedTeam.Batch639.figure_120
#print axioms Nock.RedTeam.Batch639.figure_tight
#print axioms Nock.RedTeam.Batch639.figures_without_formR_still_hold
#print axioms Nock.RedTeam.Batch639.paper_configuration_123_untouched
#print axioms Nock.RedTeam.Batch639.pricedWalkWork_no_slack
#print axioms Nock.RedTeam.Batch639.summand_vs_removed_slack
#print axioms Nock.RedTeam.Batch639.timestampStrategy_afterSeed
#print axioms Nock.RedTeam.Batch639.honest_fixedFormRWorkload_le
