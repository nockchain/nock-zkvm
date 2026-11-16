/-
  Nock/RedTeam/Batch258Thm54SoundnessNumberAtBroadProgram.lean

  **A closed soundness number at the eight-state generated program.**

  `TraceGen.GenSoundnessNumber` states the false-acceptance error at a released package with the
  numerator explicit in trace data.  This module evaluates that numerator at ONE program —
  `GenBroadProgram.bpTree`, seventeen rows, eight of the eleven compute states, `Λ = 22`,
  `K = GaloisField 769 3` — reusing `Batch231`/`Batch232`/`Batch256`'s already-discharged
  measurements verbatim, and gets a number:

  | quantity | value | source |
  |---|---|---|
  | `C`, compute skeleton rows | `17` | `Batch256.b256_compRows` via `specializedCfg_compRows` |
  | `M`, memory skeleton rows | `227` | `Batch256.b256_memRows` via `specializedCfg_memRows` |
  | `R`, committed memory roots | `19` | `Batch232.bp_kMem` via `specializedCfg_kMem` |
  | `Λ`, leaf window | `22` | `rfl` at the package |
  | `L`, memory records | `22` | `Batch256.b256_accAt_eq_22` via `accAt_len_eq_totalRecordCount` |

      1 + (3 + 19·17)·(2·22 - 1) + (24·17 + 8·227) + 19·22 + 22·23/2
        = 1 + 14018 + 2224 + 418 + 253 = 16914

  and `|K| = 769³ = 454 756 609`, so

      |jointProbability (FalseAcceptanceSet bpPackage.strategy 769 22)| ≤ 16914 / 454756609

  i.e. below `2^-14` (`b258_falseAcceptance_le_two_pow_neg_14`).  `16914 · 2^15 > 769³`

  The theorem below stays true as stated because
  the union it prices has five summands; the interpretation changes.  On the *generated* route no
  sixth event is needed at all — `hop` is already fully discharged there by
  `TraceGen.genOperationalCore` — so this number is the honest one for `nockCompiles` and `2^-11`
  is the honest one for the arbitrary-skeleton reading.
  (`b258_fifteen_bits_needs_a_sharper_numerator`), so **fourteen bits is what this numerator
  yields at this field** — not a claim that the true error is no smaller, and not a security
  claim about the deployed Goldilocks field, where the same numerator against `p³ ≈ 2^192` would
  leave ~177 bits.

  ## Scope

  Fixture.  Every number here is a measurement of `bpTree` at `p = 769`; none is a statement about
  arbitrary programs or about Goldilocks.  The *generic* statements are in
  `TraceGen/GenSoundnessNumber.lean` (`falseAcceptance_le_of_workload_le`, `∀ P`;
  `generated_falseAcceptance_le_explicit`, generated scope; `program_falseAcceptance_le_explicit`,
  over the program).  What this file adds is that the generic numerator is *finite and small* at a
  real generated trace, which no statement in the tree said before.

  `bpPackage` is `Batch256`'s package (`buildFullPackage` at `commitmentResidualOfZero`), not
  `GenericHonestPackage.packageOf`; the exponent window is therefore taken through the `∀ T`
  bridge `committedExponentWindow_of_maxTemplateRecordExponent` plus the `rfl` identification of
  `committedTemplate bpPackage.strategy.verifier z hz` with `bpData.executionTemplate z` at every
  seed, rather than through `packageOf_committedExponentWindow`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSoundnessNumber
import Nock.RedTeam.Batch256Thm54InputsAtBroadProgram
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000

namespace Nock.RedTeam.Batch258

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam
open Nock.RedTeam.Batch256

abbrev DK := DotConfig769.K
abbrev DF := DotConfig769.F

local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK

noncomputable section




/-! ## 1. The five trace numbers -/

/-- `L = 22`: the generator's accumulator at the end of BFS is the paper's `L`, and `Batch256` measured it. -/
theorem b258_L :
    ForestExponentWindow.totalRecordCount
      (bfsStamps (bfsAssign (airReorder (bpTree (K := DK))))) = 22 := by
  rw [← accAt_len_eq_totalRecordCount]
  exact Batch256.b256_accAt_eq_22

/-- `C = 17` compute skeleton rows.  `specializedCfg_compRows` says the count is challenge-free and
equal to the specialized configuration's `compRows`, which at the honest sample is the carrier's
own. -/
theorem b258_C :
    (SemanticStrategy.computeSkeletonRows bpPackage.strategy.skeleton).length = 17 := by
  have h := specializedCfg_compRows bpPackage.strategy bpPackage.optimized.strategy_bindsAll bpPackage.honestSeed
    bpPackage.honestSeed_ne bpPackage.honestAlpha Batch232.bp_buildable.cfg.challenges.lam
  rw [show bpPackage.strategy.specializedCfg bpPackage.honestSeed bpPackage.honestSeed_ne
      bpPackage.honestAlpha Batch232.bp_buildable.cfg.challenges.lam = Batch232.bp_buildable.cfg from rfl] at h
  rw [← h]
  exact Batch256.b256_compRows

/-- `M = 227` memory skeleton rows. -/
theorem b258_M :
    (SemanticStrategy.memorySkeletonRows bpPackage.strategy.skeleton).length = 227 := by
  have h := specializedCfg_memRows bpPackage.strategy bpPackage.optimized.strategy_bindsAll bpPackage.honestSeed
    bpPackage.honestSeed_ne bpPackage.honestAlpha Batch232.bp_buildable.cfg.challenges.lam
  rw [show bpPackage.strategy.specializedCfg bpPackage.honestSeed bpPackage.honestSeed_ne
      bpPackage.honestAlpha Batch232.bp_buildable.cfg.challenges.lam = Batch232.bp_buildable.cfg from rfl] at h
  rw [← h]
  exact Batch256.b256_memRows

/-- `R = 19` committed memory roots. -/
theorem b258_R : bpPackage.strategy.skeleton.memoryForest.length = 19 := by
  have h := specializedCfg_kMem bpPackage.strategy bpPackage.optimized.strategy_bindsAll bpPackage.honestSeed
    bpPackage.honestSeed_ne bpPackage.honestAlpha Batch232.bp_buildable.cfg.challenges.lam
  rw [show bpPackage.strategy.specializedCfg bpPackage.honestSeed bpPackage.honestSeed_ne
      bpPackage.honestAlpha Batch232.bp_buildable.cfg.challenges.lam = Batch232.bp_buildable.cfg from rfl] at h
  rw [← h]
  exact Batch232.bp_kMem

/-- `Λ = 22` at the assembled package. -/
theorem b258_Λ : bpPackage.optimized.Λ = 22 := rfl

/-! ## 2. The exponent window at this commitment

`GenWorkloadBounds.CommittedExponentWindow` is the object that module names and does not supply.
Here it is supplied at `B = L = 22` from `GenExponentLineNumbers`' generated-path bound, using
`Batch256.b256_committed_memoryNodes` — the commitment's memory node forest *is* the generator's
served forest on `bpTree`. -/

theorem b258_window : CommittedExponentWindow bpPackage.strategy 22 := by
  refine committedExponentWindow_of_maxTemplateRecordExponent bpPackage.strategy 22 ?_
  intro z hz
  rw [show committedTemplate bpPackage.strategy.verifier z hz
      = bpData.executionTemplate z from rfl]
  refine data_maxTemplateRecordExponent_le bpData 22 ?_ z
  intro n hn
  rw [b256_committed_memoryNodes] at hn
  have hn' : n ∈ bfsForest (genMemoryNodes DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
      (memInputs DotConfig769.seedZ) (bpTree (K := DK))) := by
    rw [← b256_committed_memoryNodes]; exact hn
  have h := genMemoryNodes_stamp_exp_le DotConfig769.seedZ DotConfig769.alphaA
    (memInputs DotConfig769.seedZ) (bpTree (K := DK)) n hn'
  rw [b258_L] at h
  exact h

/-! ## 3. The number -/

/-- **The five-class workload at this program is at most `16914`.**  Both challenge-indexed
majorants are gone: the topology one by `fixedTopologyWorkload_eq`, the axis one by the window
above. -/
theorem b258_workload_le :
    workload bpPackage.strategy bpPackage.optimized.Λ
      (fixedTopologyWorkload bpPackage.strategy)
      (fixedAxisWorkload bpPackage.strategy) ≤
        16914 + formRUniformWorkload bpPackage.strategy +
          reqPairWorkload bpPackage.strategy bpPackage.optimized.Λ := by
  -- thirtieth move: `workload` carries a Form R λ-event summand (`formRUniformWorkload` since the
  -- thirty-second, `fixedFormRWorkload` before), which
  -- this receipt does not evaluate; it is carried symbolically
  have h := workload_le_explicit bpPackage.strategy bpPackage.optimized.strategy_bindsAll
    bpPackage.optimized.Λ 22 b258_window
  rw [b258_C, b258_M, b258_R, b258_Λ] at h
  refine h.trans (le_of_eq ?_)
  rw [← sizeWindowRootBound_eq_gauss, b258_Λ]
  omega

/-- **The closed soundness error at the eight-state generated program.**
`16914 / 454756609 ≈ 3.72 · 10^-5`. -/
theorem b258_falseAcceptance_le (lmb : DK) :
    |jointProbability (FalseAcceptanceSet bpPackage.strategy bpPackage.q
        bpPackage.optimized.Λ lmb)| ≤
      ((16914 + formRUniformWorkload bpPackage.strategy +
          reqPairWorkload bpPackage.strategy bpPackage.optimized.Λ : ℕ) : ℝ) / 454756609 := by
  have h := falseAcceptance_le_of_workload_le bpPackage _ lmb
    b258_workload_le
  rw [DotConfig769.card_K] at h
  refine h.trans (le_of_eq ?_)
  norm_num

/-! ## 4. In bits -/

theorem b258_hsupport (hformR : formRUniformWorkload bpPackage.strategy ≤ 10838)
    (hpair : reqPairWorkload bpPackage.strategy bpPackage.optimized.Λ = 0) :
    workload bpPackage.strategy bpPackage.optimized.Λ
        (fixedTopologyWorkload bpPackage.strategy)
        (fixedAxisWorkload bpPackage.strategy) * 2 ^ 14 ≤ Fintype.card DK := by
  rw [DotConfig769.card_K]
  calc
    workload bpPackage.strategy bpPackage.optimized.Λ
        (fixedTopologyWorkload bpPackage.strategy)
        (fixedAxisWorkload bpPackage.strategy) * 2 ^ 14
        ≤ (16914 + 10838) * 2 ^ 14 :=
          Nat.mul_le_mul_right _ (b258_workload_le.trans (by omega))
    _ ≤ 769 ^ 3 := by norm_num

/-- **Fourteen bits at `p = 769`.**  `p8_fixedField_falseAcceptance_le_two_pow_neg` at `b = 14`. -/
theorem b258_falseAcceptance_le_two_pow_neg_14
    (hformR : formRUniformWorkload bpPackage.strategy ≤ 10838)
    (hpair : reqPairWorkload bpPackage.strategy bpPackage.optimized.Λ = 0) (lmb : DK) :
    |jointProbability (FalseAcceptanceSet bpPackage.strategy bpPackage.q
        bpPackage.optimized.Λ lmb)| ≤ 1 / 2 ^ 14 :=
  bpPackage.p8_fixedField_falseAcceptance_le_two_pow_neg lmb 14
    (b258_hsupport hformR hpair)

/-! ### The thirty-second move at this fixture (lane `lambda-consumer-32nd`, FINDING)

The summand is now the trace-uniform `formRUniformWorkload = M·(3N + 67 + (formRN K − 1))`.  At
`p = 769` (`formRN = Nat.size 769 = 10`), `N = 17`, `M = 227` it is exactly `227 · 127 = 28829`, so the
`hformR : … ≤ 10838` premise of the fourteen-bit receipt above is FALSE (the receipt is vacuous after
the move), and the premise-free figure at this fixture is thirteen bits. -/

theorem b258_formRN : FormRAxisEvent.formRN DK = 10 := by
  unfold FormRAxisEvent.formRN
  rw [DotConfig769.ringChar_K]
  decide

theorem b258_formRUniform_eq : formRUniformWorkload bpPackage.strategy = 28829 := by
  unfold formRUniformWorkload
  rw [b258_C, b258_M, b258_formRN]

theorem b258_hformR_false : ¬ (formRUniformWorkload bpPackage.strategy ≤ 10838) := by
  rw [b258_formRUniform_eq]; norm_num

theorem b258_falseAcceptance_le_two_pow_neg_13
    (hpair : reqPairWorkload bpPackage.strategy bpPackage.optimized.Λ ≤ 9769) (lmb : DK) :
    |jointProbability (FalseAcceptanceSet bpPackage.strategy bpPackage.q
        bpPackage.optimized.Λ lmb)| ≤ 1 / 2 ^ 13 :=
  bpPackage.p8_fixedField_falseAcceptance_le_two_pow_neg lmb 13 (by
    rw [DotConfig769.card_K]
    calc
      workload bpPackage.strategy bpPackage.optimized.Λ
          (fixedTopologyWorkload bpPackage.strategy)
          (fixedAxisWorkload bpPackage.strategy) * 2 ^ 13
          ≤ (16914 + 28829 + 9769) * 2 ^ 13 :=
            Nat.mul_le_mul_right _ (b258_workload_le.trans (by rw [b258_formRUniform_eq]; omega))
      _ ≤ 769 ^ 3 := by norm_num)

/-- And fourteen no longer follows from the move's numerator: `(16914 + 28829)·2^14 > 769³`. -/
theorem b258_fourteen_bits_lost_at_the_32nd : ¬ ((16914 + 28829) * 2 ^ 14 ≤ 769 ^ 3) := by norm_num

/-! ### The thirty-third move at this fixture (lane `h13-consume`, FINDING)

`workload` now also carries `reqPairWorkload = M·(2(M ⊔ Λ) − 1)`; at `M = 227`, `Λ = 22` it is
`227 · 453 = 102831`, so the numerator is `16914 + 28829 + 102831 = 148574` and the premise-free
figure at this fixture is **eleven bits** (`148574·2^11 ≤ 769³ < 148574·2^12`).  Fixture scope only:
`p = 769` is not the Goldilocks configuration. -/

theorem b258_reqPair_eq : reqPairWorkload bpPackage.strategy bpPackage.optimized.Λ = 102831 := by
  unfold reqPairWorkload
  rw [b258_M, b258_Λ]
  rfl

theorem b258_hpair13_false : ¬ (reqPairWorkload bpPackage.strategy bpPackage.optimized.Λ ≤ 9769) := by
  rw [b258_reqPair_eq]; norm_num

/-- **Eleven bits at `p = 769`, no premise** (after the thirty-third move). -/
theorem b258_falseAcceptance_le_two_pow_neg_11 (lmb : DK) :
    |jointProbability (FalseAcceptanceSet bpPackage.strategy bpPackage.q
        bpPackage.optimized.Λ lmb)| ≤ 1 / 2 ^ 11 :=
  bpPackage.p8_fixedField_falseAcceptance_le_two_pow_neg lmb 11 (by
    rw [DotConfig769.card_K]
    calc
      workload bpPackage.strategy bpPackage.optimized.Λ
          (fixedTopologyWorkload bpPackage.strategy)
          (fixedAxisWorkload bpPackage.strategy) * 2 ^ 11
          ≤ (16914 + 28829 + 102831) * 2 ^ 11 :=
            Nat.mul_le_mul_right _ (b258_workload_le.trans
              (by rw [b258_formRUniform_eq, b258_reqPair_eq]))
      _ ≤ 769 ^ 3 := by norm_num)

/-- And twelve no longer follows from the move's numerator: `148574·2^12 > 769³`. -/
theorem b258_twelve_bits_lost_at_the_33rd : ¬ ((16914 + 28829 + 102831) * 2 ^ 12 ≤ 769 ^ 3) := by
  norm_num

/-- And fifteen does not follow from *this* numerator: `16914 · 2^15 > 769³`.  That is a statement
about the numerator, not about the true error. -/
theorem b258_fifteen_bits_needs_a_sharper_numerator :
    ¬ (16914 * 2 ^ 15 ≤ 769 ^ 3) := by norm_num

end

end Nock.RedTeam.Batch258

#print axioms Nock.RedTeam.Batch258.b258_L
#print axioms Nock.RedTeam.Batch258.b258_C
#print axioms Nock.RedTeam.Batch258.b258_M
#print axioms Nock.RedTeam.Batch258.b258_R
#print axioms Nock.RedTeam.Batch258.b258_window
#print axioms Nock.RedTeam.Batch258.b258_workload_le
#print axioms Nock.RedTeam.Batch258.b258_falseAcceptance_le
#print axioms Nock.RedTeam.Batch258.b258_falseAcceptance_le_two_pow_neg_14
