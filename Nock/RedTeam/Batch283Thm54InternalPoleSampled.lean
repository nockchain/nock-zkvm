/-
  Nock/RedTeam/Batch283Thm54InternalPoleSampled.lean

  * `MemoryChallengeTuple.interPole` is the seventh `𝕂` coordinate
    (`card_optimizedProductionChallengeTuple = |𝕂|⁷`);
  * slot `6` of `memoryChallengeTargets` is occupied (`I.memoryExtensionFold`);
  * `OptimizedProductionAcceptanceAt.memory_intermediate_pole` pins `chal 6`;
  * the consumed bound prices `interWork = ioFailureUnionBound 8 M M |𝕂|` as
    `interWork/|𝕂|²` (`= (28M²+4M)/|𝕂|`);
  * figures: `123` at the paper configuration (ceilings on `p8Work`/`ioWork`),
    `122` / `120` for real programs at `2^31` / `2^32` rows
    (`2r+b = 184` still; majorant `367S²+102S+4`).

    * at Design A commit, `poleSource` was still `poleExpr.subst memorySubst`;
      it is now `chal 6 + recordRLCExpr` (`poleSource_retargeted`);
    * `liftInterPoleFailure` is ∪-ed into `OptimizedHostileProductionFailureEvent`
      on the rebased branch (`interFailurePairs`).

  Paper at source: the paper (`1 → 2` elements), `:2117-2123`.
-/
import Nock.NockVMROM.Thm54.GoldilocksParameters
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.NockVMROM.Thm54.MemoryInternalPole
import Nock.AIR

namespace Nock.RedTeam.Batch283

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.MemoryInternalPole
open Nock.Reified
open FiniteIO

/-! ## A. Challenge space `|𝕂|⁷` -/

theorem card_is_K_pow_7 (K F : Type) [Fintype K] [Fintype F] :
    Fintype.card (OptimizedProductionChallengeTuple K F) = Fintype.card K ^ 11 :=
  card_optimizedProductionChallengeTuple K F

theorem memory_tuple_card_is_K (K : Type) [Fintype K] :
    Fintype.card (MemoryChallengeTuple K) = Fintype.card K ^ 2 :=
  card_memoryChallengeTuple K

theorem goldilocks_space_is_K_pow_7 :
    Fintype.card (OptimizedProductionChallengeTuple Nock.Field.K Nock.Field.Fp)
      = cardKGold ^ 11 :=
  card_challenge_space

/-! ## B. Bound prices `interWork` -/

theorem interWork_is_ioUnion (M cardK : ℕ) :
    interWork M cardK = ioFailureUnionBound 10 M M cardK :=
  rfl

theorem interWork_inner (M cardK : ℕ) :
    ioFailureUnionBound 10 M M cardK = cardK * (36 * M * M + 4 * M) :=
  ioFailureUnionBound_ten M cardK

theorem bound_three_summands (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureProbabilityBound cardK cardF p8Work ioWork N M
      = ((p8Work +
          OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
          pricedWalkWork N M : ℚ) / cardK
        + (ioWork : ℚ) / cardK ^ 2
        + ((ioFailureUnionBound 10 M M cardK + cardK * M : ℕ) : ℚ) / cardK ^ 2) :=
  optimizedHostileProductionFailureProbabilityBound_byte_identical
    cardK cardF p8Work ioWork N M

theorem card_bound_prices_interWork (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureCardBound cardK cardF p8Work ioWork N M
      = optimizedTrimmedProductionFailureCardBound cardK cardF p8Work ioWork N M
        + cardK ^ 10 * OptimizedHostileTimestamps.timestampCollisionBound (3 * N)
        + cardK ^ 9 * (ioFailureUnionBound 10 M M cardK + cardK * M)
        + cardK ^ 10 * pricedWalkWork N M :=
  rfl

/-! ## C. Figures, computed not quoted -/

theorem paper_config_123 (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31)
      < 1 / (2 : ℚ) ^ 123 :=
  hostile_soundness_at_paper_configuration p8Work ioWork hp8 hio

theorem real_programs_122 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_for_real_programs_at_two_pow_31 R M Λ A p8Work hR hM hΛ hA hp8

theorem real_programs_120 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_for_real_programs_at_two_pow_32 R M Λ A p8Work hR hM hΛ hA hp8

/-! ## D. Remainders, stated so they cannot silently close -/

/-- `poleSource` is the sampled-pole compress at slots `(4, 6)` -/
theorem poleSource_retargeted :
    poleSource = .Add (.Var .challenge 6) recordRLCExpr :=
  rfl

end Nock.RedTeam.Batch283

#print axioms Nock.RedTeam.Batch283.card_is_K_pow_7
#print axioms Nock.RedTeam.Batch283.goldilocks_space_is_K_pow_7
#print axioms Nock.RedTeam.Batch283.bound_three_summands
#print axioms Nock.RedTeam.Batch283.paper_config_123
#print axioms Nock.RedTeam.Batch283.real_programs_122
#print axioms Nock.RedTeam.Batch283.real_programs_120
#print axioms Nock.RedTeam.Batch283.poleSource_retargeted
