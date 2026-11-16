/-
  Nock/RedTeam/Batch909Thm54R4HonestInstance.lean

  Instance: `c = P.honestTuple`, `Qc = QcH P`, `Qm = QmH P`.  Source of each premise
  (all at an arbitrary package `P`, generic in the program, from `HonestFill P`):

  | premise | source |
  |---|---|
  | `hacc : DeployedAcceptanceAt`       | `deployedAcceptance_honest`  |
  | `hio : FamilyIOGood`                | `hio_honest`, `ioGood10` |
  | `hb : CertBitsBoolean`              | `hb_honest`, from `hacc` |
  | `h1 : coord b 1 0 ≠ 0`              | `h1_honest`, `FormRBasis` |
  | `hU : UniqueExponents`              | `UniqueExponentsBridge.uniqueExponents_decoded_pkg` |
  | `hA : CertInRange`                  | `hA_of_acceptance`, `Batch806` |
  | `hrb : rows < ringChar K`           | explicit hypothesis (generator side condition, see below) |
  | `hgood : c ∉ optimizedFailureEvent` | **`HonestEventResidual P`** (below) |

  **`hgood` is the premise with no source theorem in the tree.**  No existing
  fixture proves them either: `MultiRootOptimizedAcceptance.packageP_optimized_outside_failure`
  carries the same nine as hypotheses.  `HonestEventResidual` names exactly those, with each
  field's type read off `notMem_optimizedFailureEvent_of_components`.

  `hrb`: the generator's `hF : 3 * 2^h ∣ p - 1` and `programFit` give it at `nockCompiles` scope,
  but no package field states it (it is the future `rowsBound`).
-/
import Nock.RedTeam.Batch908Thm54R4HonestShiftRange
import Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch909

open scoped Polynomial
open Polynomial
open Nock
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.AxisBatching.MTree
open Nock.RedTeam.Batch575
open Nock.RedTeam.Batch905
open Nock.RedTeam.Batch906
open Nock.RedTeam.Batch907
open Nock.RedTeam.Batch908

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- **The twelve-event residual at the honest instance**, minus the one event `hio` that the
package discharges (`ioGood10`).  Every field is `c ∉ <component of optimizedFailureEvent>` at
`c = P.honestTuple` and the canonical traces, or a side condition of the closed forms that
discharge a component (`alphaNe`, `alphaOrder` for the timestamp event; `interNe`, `interGamma8`,
`inactiveMem`, `inactiveCprime` for the internal-pole pair event). -/
structure HonestEventResidual (P : OptimizedFullStrictNockVMROMPackage F K hOrb) : Prop where
  failureUnion : P.honestTuple.1 ∉ ProductionP8Containment.FailureUnion P.strategy P.optimized.census
    P.objects.cfg.challenges.lam
  walk : P.honestTuple.1 ∉ P.computeWalkRootEvent (canonicalComputeTrace P)
  tileC : P.honestTuple.1 ∉ P.computeTilingEventOf (canonicalComputeTrace P)
  tileM : P.honestTuple.1 ∉ P.memoryTilingEventOf (canonicalMemoryTrace P)
  gammaC : P.honestTuple.1 ∉ P.computePrefixGammaEventOf (canonicalComputeTrace P)
  gammaM : P.honestTuple.1 ∉ P.memoryPrefixGammaEventOf (canonicalMemoryTrace P)
  forestAlpha : P.honestTuple.1 ∉ P.memoryForestAlphaEventOf (canonicalMemoryTrace P)
  lam : P.honestTuple ∉ P.decodedLambdaEventOf (canonicalComputeTrace P) (canonicalMemoryTrace P)
  pair : P.honestTuple.1 ∉ PreSeedCensus.reqPairEventOfEnvs K P.q
    P.optimized.family.problem.cfg.kMem
    (P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ)
    (P.memoryBaseEnv (canonicalMemoryTrace P)) P.optimized.family.problem.cfg.memRows_pos
    (PreSeedCensus.requestTargets P.strategy.skeleton)
  alphaNe : alphaM P.honestTuple.1 ≠ 0
  alphaOrder : 3 * P.optimized.family.problem.cfg.compRows ≤ orderOf (alphaM P.honestTuple.1)
  interNe : P.optimized.sampled.interPole ≠ 0
  interGamma8 : P.optimized.sampled.interPole + P.optimized.sampled.sampled.coins.gamma ^ 8 ≠ 0
  inactiveMem : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
    (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .read_root →
    (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .verify_child →
    (P.optimized.family.problem.exec.memoryPubAt i).mem = ComputeTable.MemRec.zero
  inactiveCprime : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
    (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .read_root →
    (P.optimized.family.problem.exec.memoryPubAt i).st ≠ .verify_child →
    (P.optimized.family.problem.exec.memoryPubAt i).cprime = 1

variable {P : OptimizedFullStrictNockVMROMPackage F K hOrb}

/-- **The 2a IO component at the honest instance**: `honestTuple ∉ famIOEventOf`, i.e.
`FamilyIOGood`  unfolded (`FamilyEnvCore.mem_famIOEventOf_iff`; `QcH` / `QmH` are the
family reindexings of the canonical traces). -/
theorem hioEvent_honest (H : HonestFill P) :
    P.honestTuple ∉ P.famIOEventOf (canonicalComputeTrace P) (canonicalMemoryTrace P) := by
  intro hm
  have h := (FamilyEnvCore.mem_famIOEventOf_iff P.optimized (canonicalComputeTrace P)
    (canonicalMemoryTrace P) P.honestTuple).1 hm
  exact hio_honest H h

/-- **`hgood` at the honest instance, from the residual.** -/
theorem hgood_honest (H : HonestFill P) (R : HonestEventResidual P) :
    P.honestTuple ∉ P.optimizedFailureEvent (honestQc P P.honestTuple (QcH P))
      (honestQm P P.honestTuple (QmH P)) := by
  rw [honestQc_QcH, honestQm_QmH]
  refine P.notMem_optimizedFailureEvent_of_components _ _ _ R.failureUnion ?_ ?_ ?_ R.walk R.tileC R.tileM
    R.gammaC R.gammaM R.forestAlpha R.lam R.pair
  · exact hioEvent_honest H
  · exact OptimizedCanonicalHostileLists.alpha_not_collision_of_orderOf P _ R.alphaNe R.alphaOrder
  · have h := OptimizedCanonicalHostileLists.canonical_inter_not_hostile_failure P R.interNe
      R.interGamma8 R.inactiveMem R.inactiveCprime H.hC
    have hp : P.honestTuple.2.2.2.interPole = P.optimized.sampled.interPole :=
      P.packageInterPole_eq_sampled
    change (P.optimized.sampled.sampled.coins.gamma, P.honestTuple.2.2.2.interPole) ∉ _
    rw [hp]
    exact h

/-- `2 ≤ formRN F` from `FormRWidth`. -/
theorem two_le_formRN (H : HonestFill P) : 2 ≤ OptimizedComputeRangeCertificate.formRN F := by
  have h3 := H.hwidth.2.2
  unfold OptimizedComputeRangeCertificate.formRN
  have : 1 < Nat.size (ringChar F) := Nat.lt_size.mpr (by omega)
  omega

/-- **THE PREMISE SET, JOINTLY, AT THE HONEST INSTANCE**: all of `r4_path_valid_at`'s hypotheses
hold at `(P, P.honestTuple, QcH P, QmH P)`, from `HonestFill P`, the row bound and the event
residual. -/
theorem r4Premises_honest (H : HonestFill P) (R : HonestEventResidual P)
    (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K) :
    R4Premises P P.honestTuple (QcH P) (QmH P) := by
  have hacc := deployedAcceptance_honest H
  have hgood := hgood_honest H R
  have hio := hio_honest H
  have hb := hb_honest H
  have h1 := h1_honest H
  refine ⟨hacc, hgood, hio, hrb, hb, h1, ?_, ?_⟩
  · intro r _
    exact UniqueExponentsBridge.uniqueExponents_decoded_pkg P P.honestTuple (QcH P) (QmH P)
      hacc hgood hio hrb h1 _ r
  · exact hA_of_acceptance P P.honestTuple (QcH P) hacc.compute_satisfies (two_le_formRN H)

/-- **THE INSTANTIATED CONCLUSION** (`r4_path_valid_at` at the honest instance): at the honest
tuple and honest traces, for every decoded root, the read and verify counts balance and every
paired exponent has valid padding and the path equation `V = R ++ bitsOf (m_e) (c_e)`. -/
theorem r4_honest_conclusion (H : HonestFill P) (R : HonestEventResidual P)
    (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K) :
    ∀ r ∈ Finset.Icc 1 P.optimized.family.problem.cfg.kMem,
      let t := DecodedLambdaEvent.decodedMTreeOfEnvs (Batch824.envsKR P P.honestTuple (QmH P))
        (Batch824.envsFR P P.honestTuple (QmH P)) P.optimized.family.problem.cfg.kMem r
      (∀ e, readCount e t = verifyCount e t) ∧
        ∀ e, Paired e t →
          Padding (FormRAxisEvent.formRN K)
              (DecodedLambdaEvent.decodedShift (Batch824.envsCR P P.honestTuple (QcH P)) e)
              (DecodedLambdaEvent.decodedBits (Batch824.envsCR P P.honestTuple (QcH P)) e) ∧
            ∃ q, Batch554.rpaths e t = [q] ∧
              Batch554.vpaths e t =
                [q ++ Batch554.bitsOf
                  (DecodedLambdaEvent.decodedShift (Batch824.envsCR P P.honestTuple (QcH P)) e)
                  (DecodedLambdaEvent.decodedBits (Batch824.envsCR P P.honestTuple (QcH P)) e)] :=
  r4_path_valid_of_premises P P.honestTuple (QcH P) (QmH P) (r4Premises_honest H R hrb)

end

/-! ## The fixture `packageP` does NOT satisfy `HonestFill`

`HonestFill.hchalM` is the premise `h` of the existing `memoryChipAt_honest_of_chalVal`.  So no theorem of
this family (chip equality at the honest tuple) applies at `packageP`; the honest family chip's
satisfaction there would need a read-set argument (the raw slots are unread) that is not in the
tree.  Generated packages carry `memoryScalarChallenge` as a free `Inputs` field, so the same
failure occurs at every one that sets it nonzero. -/

namespace Fixture

open scoped Classical
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete

local instance prime97p' : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97p' : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-- **Compiled counterexample to `HonestFill.hchalM` at the fixture package.** -/
theorem packageP_hchalM_false
    (hmoreM : BuildableAxisWitness.LaterSeedZeros MultiRootServedFixture.multiRootExecution) :
    DeployedChipFamily.memoryChalValOfTuple (packageP hmoreM).optimized.basis
        (packageP hmoreM).honestTuple ≠ (packageP hmoreM).optimized.memoryChallenge := by
  intro h
  have h0 := congrFun h 0
  simp [DeployedChipFamily.memoryChalValOfTuple] at h0
  have h1 : (packageP hmoreM).optimized.memoryChallenge 0 = (1 : F97) := by
    show BuildableChips.memoryChallenge MultiRootServedFixture.multiRootExecution
      MultiRootServedFixture.inputsM 0 = 1
    simp [BuildableChips.memoryChallenge, MultiRootServedFixture.inputsM]
  rw [h1] at h0
  exact absurd h0 (by decide)

end Fixture

end Nock.RedTeam.Batch909

#print axioms Nock.RedTeam.Batch909.hgood_honest
#print axioms Nock.RedTeam.Batch909.r4Premises_honest
#print axioms Nock.RedTeam.Batch909.r4_honest_conclusion
#print axioms Nock.RedTeam.Batch909.Fixture.packageP_hchalM_false
