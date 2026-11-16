/-
  Nock/RedTeam/Batch851Thm54CoinParamCompletenessStop.lean

  Core module: `CoinParamCompleteness.lean`.

  (A) **Compatibility with the existing completeness.**  The existing perfect completeness is the
      instance at `c = honestTuple`: `Batch361.perfect_at_compiler_triple` is chip equality there.
      The pole fibre through `honestTuple` contains `honestTuple` itself (`withPole_honest`).  On
      that fibre the honest fill is accepted at no more than `|responses|` poles
      (`honest_fibre_card_le`).
  `honest_fibre_has_rejected_good_pole`: some pole outside
      the honest IO-pole hit event is rejected.  The only size condition is
      `|requests| + 2·|responses| < |𝕂|`, which holds at every real configuration.
  (C) **Concrete receipt** (𝔽₇): the LogUp sum of two records moves when the pole moves, at two
      poles that hit neither record.
  (E) **Read map**: the IO pole is read at compute slot `8` and memory slot `5` only, while the
      `requests` publics are the same at every tuple.

  Paper: the paper (`requests = acc_prog(h₁)` is the prover's terminal, after the
  `(α, β)` round at `:509`), `:599` (memory seeded "as-is"), `:634`, `:1451`.
-/
import Nock.NockVMROM.Thm54.CoinParamCompleteness
import Nock.RedTeam.Batch361Thm54Completeness
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch851

open scoped Polynomial
open Polynomial
open Nock
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.CoinParamCompleteness

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## (A) Compatibility -/

/-- The honest tuple lies on its own pole fibre. -/
theorem withPole_honest : withPole P.honestTuple P.honestTuple.2.1.2 = P.honestTuple := rfl

/-- The existing perfect completeness, quoted unchanged: at `c = honestTuple` the family compute
chip IS the package chip (`Batch361.perfect_at_compiler_triple`).  Coin-parametric completeness,
had it held, would restrict to exactly this at `c = honestTuple`. -/
theorem existing_instance_at_honestTuple
    (hchal : computeChalValOfTuple P.optimized.basis P.honestTuple =
      P.optimized.computeChallenge)
    (hst : (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).state =
        ComputeWalkSeed.rootStateOfFormula P.optimized.verifier.raw.claim.formula)
    (hs : (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).s =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.subject)
    (hf : (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).f =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.formula)
    (he : (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).e =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.result)
    (hmchal : memoryChalValOfTuple P.optimized.basis P.honestTuple =
      P.optimized.memoryChallenge) :
    P.computeChipAt P.honestTuple = P.computeChip ∧ P.memoryChipAt P.honestTuple = P.memoryChip :=
  ⟨Batch361.perfect_at_compiler_triple P hchal hst hs hf he,
    P.memoryChipAt_honest_of_chalVal hmchal⟩

open Classical in
/-- On the pole fibre through `honestTuple`, any fill whose committed responses do not move
with the pole is accepted at no more than `|responses|` poles. -/
theorem honest_fibre_card_le
    (Qm : ∀ p : K, Fin (P.memoryChipAt (withPole P.honestTuple p)).rap.w → F[X])
    (rs : List (Fin 10 → K))
    (hrs : ∀ p, hostileResponsesAt P (withPole P.honestTuple p) (Qm p) = rs)
    (hnd : (rs.map (Walk.rlc P.honestTuple.2.1.1)).Nodup) (hne : rs ≠ []) :
    (Finset.univ.filter fun p : K =>
        RAP.SatisfiesWithPreprocessing (P.memoryChipAt (withPole P.honestTuple p)) (Qm p)).card ≤
      rs.length :=
  accepted_poles_card_le P P.honestTuple Qm rs hrs hnd hne


/-- Pole-uniform completeness fails on the honest fibre.  Some pole outside
the honest records' IO-pole hit event admits NO two-chip acceptance with the fill's memory
trace. -/
theorem honest_fibre_has_rejected_good_pole
    (Qm : ∀ p : K, Fin (P.memoryChipAt (withPole P.honestTuple p)).rap.w → F[X])
    (R : FiniteIO.PreChallengeRecords K 10)
    (hrs : ∀ p, hostileResponsesAt P (withPole P.honestTuple p) (Qm p) = R.responses)
    (hnd : R.responses.Nodup)
    (hγ : P.honestTuple.2.1.1 ∉ FiniteIO.IORLCCollisionEvent R)
    (hne : R.responses ≠ [])
    (hK : R.requests.length + 2 * R.responses.length < Fintype.card K) :
    ∃ p : K, p ∉ FiniteIO.IOPoleHitEvent R P.honestTuple.2.1.1 ∧
      ∀ Qc : Fin (P.computeChipAt (withPole P.honestTuple p)).rap.w → F[X],
        ¬ DeployedAcceptanceAt P (withPole P.honestTuple p) Qc (Qm p) :=
  exists_good_pole_not_deployed P P.honestTuple Qm R hrs
    (nodup_rlc_of_not_collision R _ hnd hγ) hne hK

/-! ## (C) Concrete receipt -/

/-- 𝔽₇, records `0, 1`, poles `1` and `2` (neither hits a record): the LogUp sums differ. -/
theorem concrete_sum_moves :
    (1 : ZMod 7)⁻¹ + (2 : ZMod 7)⁻¹ ≠ (2 : ZMod 7)⁻¹ + (3 : ZMod 7)⁻¹ :=
  logup_sum_moves_with_pole_F7.1

/-- The algebraic fibre bound is tight in shape: in 𝔽₇, with records `{0, 1}` and target
`1⁻¹ + 2⁻¹`, pole `1` is good and meets the target, so the filtered set is nonempty. -/
theorem concrete_fibre_nonempty :
    (1 : ZMod 7) ∈ (Finset.univ.filter fun p : ZMod 7 =>
      (∀ x ∈ ({0, 1} : Finset (ZMod 7)), p + x ≠ 0) ∧
        ∑ x ∈ ({0, 1} : Finset (ZMod 7)), (p + x)⁻¹ = (1 : ZMod 7)⁻¹ + (2 : ZMod 7)⁻¹) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨by decide, ?_⟩
  rw [Finset.sum_pair (by decide)]
  norm_num

/-! ## (D) Negative control -/

/-- A pole that hits a committed response record: the family memory chip rejects. -/
theorem negative_control (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hhit : c.2.1.2 ∈ FiniteIO.IOPoleHitEvent
      (⟨[], hostileResponsesAt P c Qm⟩ : FiniteIO.PreChallengeRecords K 10) c.2.1.1) :
    ¬ RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm :=
  rejected_of_mem_poleHit_responses P c Qm hhit

/-! ## (E) Read map -/

/-- What moves on the pole fibre: compute slot `8` and memory slot `5`, and nothing else among
the `𝕂` slots.  The `requests` publics do not move (`familyComputePublic_requests`,
`familyMemoryPublic_coin_free`). -/
theorem pole_fibre_read_map (c : OptimizedProductionChallengeTuple K F) (p : K) :
    (∀ q, q ≠ 8 → computeKOfTuple (withPole c p) q = computeKOfTuple c q) ∧
      (∀ q, q ≠ 5 → memoryKOfTuple (withPole c p) q = memoryKOfTuple c q) ∧
      (∀ k : Fin 3, P.familyComputePublic (withPole c p) (6 + (k : ℕ)) =
        P.familyComputePublic c (6 + (k : ℕ))) ∧
      (∀ k : Fin 3, P.familyMemoryPublic (withPole c p) (12 + (k : ℕ)) =
        P.familyMemoryPublic c (12 + (k : ℕ))) := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun k => ?_, fun k => ?_⟩
  · rw [computeKOfTuple_withPole, if_neg hq]
  · rw [memoryKOfTuple_withPole, if_neg hq]
  · exact familyComputePublic_coin_free P _ _ _ (by omega)
  · exact familyMemoryPublic_coin_free P _ _ _ (by omega)

end Nock.RedTeam.Batch851

#print axioms Nock.RedTeam.Batch851.existing_instance_at_honestTuple
#print axioms Nock.RedTeam.Batch851.honest_fibre_card_le
#print axioms Nock.RedTeam.Batch851.honest_fibre_has_rejected_good_pole
#print axioms Nock.RedTeam.Batch851.concrete_sum_moves
#print axioms Nock.RedTeam.Batch851.concrete_fibre_nonempty
#print axioms Nock.RedTeam.Batch851.negative_control
#print axioms Nock.RedTeam.Batch851.pole_fibre_read_map
