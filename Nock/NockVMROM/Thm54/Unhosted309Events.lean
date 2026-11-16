import Nock.NockVMROM.Thm54.Unhosted309Realization
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackageDefs
import Nock.NockVMROM.Thm54.P8Core.RepartitionedStaging
import Nock.NockVMROM.Thm54.BelowDefs.Unhosted309Events
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Summands 5 and 8 at the un-hosted 309 chip: event-level round-locality

* `computeSourceEnv309` — the width-309 decoded committed table;
* `computeWalkRootEvent309` (summand 5) and `computePrefixGammaEventOf309` (summand 8) — the
  deployed events' bodies over that table;
* `computeWalkRootEvent309_congr` / `computePrefixGammaEventOf309_congr` — **both events are
  functions of the `B0 ∪ B1` columns** (`RepartitionedStaging.newComputeColRound ≤ 1`): every
  decoded label, child payload and fanout reads only selectors and `𝕂`-roles `< 58` other than
  `32..35` (`decoder_reads_B01`, decided over the 36 restored sources and 33 tag hosts);
* `summand8_readsOn`, `summand5_alpha_readsOn`, `summand5_gamma_readsOn` — composed with the
  round discipline of a staged prover, the bad sets are `ReadsOn` the coins sampled before their
  own (plus the directly read `γ`, `z`), which is `cylinder_card_le`'s premise.
-/

namespace Nock.NockVMROM.Thm54
namespace Unhosted309

open Nock
open Nock.Reified
open Nock.Framework Reify
open Nock.ComputeTable
open Nock.Walk
open OptimizedComputeSubstitution
open OptimizedComputeCorrectedFinal
open OptimizedStrictFullPackage
open OptimizedStrictPackage
open ComputeWalkRootEvents
open ComputeWalkLabel
open RepartitionedStaging
open RoundFibred
open scoped Polynomial

set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The decoders read only `B0 ∪ B1` source indices -/

section Decoders
variable {K : Type} [Field K]

variable {N : ℕ}

theorem operands_congr {envs envs' : Fin N → Env K}
    (h : ∀ i, rowLabelVec (envs i) = rowLabelVec (envs' i) ∧
      (∀ l, rowChildVec (envs i) l = rowChildVec (envs' i) l) ∧
      rowFanout (envs i) = rowFanout (envs' i)) :
    curOf envs = curOf envs' ∧ chldOf envs = chldOf envs' ∧ foOf envs = foOf envs' := by
  refine ⟨?_, ?_, ?_⟩
  · funext g i; unfold curOf; split_ifs with hi
    · rw [(h _).1]
    · rfl
  · funext g i l; unfold chldOf; split_ifs with hi
    · rw [(h _).2.1]
    · rfl
  · funext i; unfold foOf; split_ifs with hi
    · rw [(h _).2.2]
    · rfl

theorem rootEvent_congr [Fintype K] [DecidableEq K] {envs envs' : Fin N → Env K}
    (u : K → Fin 10 → K) {v v' : Fin 10 → K}
    (h : ∀ i, rowLabelVec (envs i) = rowLabelVec (envs' i) ∧
      (∀ l, rowChildVec (envs i) l = rowChildVec (envs' i) l) ∧
      rowFanout (envs i) = rowFanout (envs' i)) (hv : v = v') :
    rootEvent envs u v = rootEvent envs' u v' := by
  obtain ⟨hc, hl, hf⟩ := operands_congr h
  subst hv
  unfold rootEvent alphaRootEventConsumed alphaRootEvent alphaBadAt
  rw [hc, hl, hf]

theorem prefixGamma_congr [Fintype K] [DecidableEq K] {envs envs' : Fin N → Env K}
    (h : ∀ i, rowLabelVec (envs i) = rowLabelVec (envs' i) ∧
      (∀ l, rowChildVec (envs i) l = rowChildVec (envs' i) l) ∧
      rowFanout (envs i) = rowFanout (envs' i)) :
    WalkPrefixGammaEvents.computePrefixGammaEventOf envs =
      WalkPrefixGammaEvents.computePrefixGammaEventOf envs' := by
  have hV : WalkPrefixGammaEvents.committedComputeV envs =
      WalkPrefixGammaEvents.committedComputeV envs' := by
    funext i; unfold WalkPrefixGammaEvents.committedComputeV; split_ifs
    · rw [(h _).1]
    · rfl
  have hCv : WalkPrefixGammaEvents.committedComputeCv envs =
      WalkPrefixGammaEvents.committedComputeCv envs' := by
    funext i l; unfold WalkPrefixGammaEvents.committedComputeCv; split_ifs
    · rw [(h _).2.1]
    · rfl
  have hfo := (operands_congr h).2.2
  unfold WalkPrefixGammaEvents.computePrefixGammaEventOf
  rw [hV, hCv, hfo]

end Decoders

/-! ## 2. The width-309 committed table and the two events -/

section Package
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

abbrev pkgComputeChipAt309 (c : OptimizedProductionChallengeTuple K F) : FixedPreprocessingRAP F :=
  computeChipAt309 P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
    P.optimized.basis (P.familyComputePublic c) P.optimized.orbit c

def computeBaseEnv309 (Qc : Fin 309 → F[X]) (i : Fin P.optimized.family.problem.cfg.compRows) :
    Env F :=
  envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
    P.optimized.computeChallenge P.optimized.computePublic

/-- The width-309 decoded committed table. -/
def computeSourceEnv309 (Qc : Fin 309 → F[X]) (i : Fin P.optimized.family.problem.cfg.compRows) :
    Env K :=
  (gather309 P.optimized.basis (computeBaseEnv309 P Qc i)).toSourceEnv

def computeWalkRootEvent309 (Qc : Fin 309 → F[X]) : Finset (JointCoins K) :=
  rootEvent (computeSourceEnv309 P Qc)
    (fun z => ComputeWalkSeed.claimLabelVec z P.optimized.verifier.raw.claim)
    (rowLabelVec (computeSourceEnv309 P Qc ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩))

def computePrefixGammaEventOf309 (Qc : Fin 309 → F[X]) : Finset (JointCoins K) :=
  WalkPrefixGammaEvents.computePrefixGammaEventOf (computeSourceEnv309 P Qc)

/-- Two 309 traces agree on every column committed in `B0 ∪ B1`. -/
def AgreeB01 (Qc Qc' : Fin 309 → F[X]) : Prop :=
  ∀ j : Fin 309, newComputeColRound j ≤ 1 → Qc j = Qc' j

theorem source309_agree_good {Qc Qc' : Fin 309 → F[X]} (h : AgreeB01 Qc Qc')
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    ∀ q, goodSrc q = true →
      varVal (computeSourceEnv309 P Qc i) q.1 q.2 = varVal (computeSourceEnv309 P Qc' i) q.1 q.2 := by
  rintro ⟨k, j⟩ hq
  cases k
  · apply src_trace_congr
    intro c hc
    obtain ⟨h309, hr⟩ := physOf_good_round j c hq hc
    simp only [computeBaseEnv309, envOfTrace, dif_pos h309]
    rw [h ⟨c, h309⟩ hr]
  all_goals simp [goodSrc] at hq

/-- **Summand 5 is a function of the `B0 ∪ B1` columns of the 309 trace.** -/
theorem computeWalkRootEvent309_congr {Qc Qc' : Fin 309 → F[X]} (h : AgreeB01 Qc Qc') :
    computeWalkRootEvent309 P Qc = computeWalkRootEvent309 P Qc' := by
  unfold computeWalkRootEvent309
  apply rootEvent_congr
  · intro i; exact decoders_congr_good (source309_agree_good P h i)
  · exact (decoders_congr_good (source309_agree_good P h _)).1

/-- **Summand 8 is a function of the `B0 ∪ B1` columns of the 309 trace.** -/
theorem computePrefixGammaEventOf309_congr {Qc Qc' : Fin 309 → F[X]} (h : AgreeB01 Qc Qc') :
    computePrefixGammaEventOf309 P Qc = computePrefixGammaEventOf309 P Qc' := by
  unfold computePrefixGammaEventOf309
  exact prefixGamma_congr fun i => decoders_congr_good (source309_agree_good P h i)

/-! ## 3. Composed with a staged prover: `ReadsOn` the prior coins (the 12-coin schedule) -/

/-- The repartitioned schedule's `sampledAfter`, as a function on `Fin 12`. -/
def sched12 : Fin 12 → ℕ := ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1]

theorem sched12_eq (j : Fin 12) :
    sched12 j = (repartitionedChronology.sampledAfter j : ℕ) := by
  fin_cases j <;> rfl

/-- A staged compute prover at the repartitioned schedule: each 309 column is a function of the
coins sampled strictly before its block. -/
def StagedCompute (Qc : (Fin 12 → K) → Fin 309 → F[X]) : Prop :=
  ∀ (j : Fin 309) (χ χ' : Fin 12 → K),
    (∀ i, sched12 i < newComputeColRound j → χ i = χ' i) → Qc χ j = Qc χ' j

theorem agree_of_prior {Qc : (Fin 12 → K) → Fin 309 → F[X]} (hst : StagedCompute Qc)
    (i₀ : Fin 12) (h1 : sched12 i₀ = 1) {χ χ' : Fin 12 → K}
    (h : ∀ j ∈ priorCoords sched12 i₀, χ j = χ' j) :
    AgreeB01 (Qc χ) (Qc χ') := by
  intro j hj
  apply hst j χ χ'
  intro i hi
  apply h i
  simp only [priorCoords, Finset.mem_filter, Finset.mem_univ, true_and, h1]
  omega

/-- **Summand 8, composed**: the event (the bad `γ`-set, `γ` = coin `1`, M2) is fixed once the
M1 coins are. -/
theorem summand8_readsOn {Qc : (Fin 12 → K) → Fin 309 → F[X]} (hst : StagedCompute Qc) :
    ReadsOn (C := K) (priorCoords sched12 1)
      (fun χ => computePrefixGammaEventOf309 P (Qc χ)) := by
  intro χ χ' h
  exact computePrefixGammaEventOf309_congr P (agree_of_prior hst 1 rfl h)

/-- **Summand 5, composed**: the root event (bad `αC`-set at the sampled `γ`, `z`, and the bad
`γ`-set at `z`; `αC` = coin `0`, M2) is fixed once the M1 coins are. -/
theorem summand5_readsOn {Qc : (Fin 12 → K) → Fin 309 → F[X]} (hst : StagedCompute Qc) :
    ReadsOn (C := K) (priorCoords sched12 0)
      (fun χ => computeWalkRootEvent309 P (Qc χ)) := by
  intro χ χ' h
  exact computeWalkRootEvent309_congr P (agree_of_prior hst 0 rfl h)

/-- The cylinder premise: neither coin is in its own read set, and both read sets are exactly
the M1 coins `{αM, z, a, b, c, λ}`. -/
theorem summands58_prior :
    priorCoords sched12 1 = {2, 3, 6, 7, 8, 10} ∧ priorCoords sched12 0 = {2, 3, 6, 7, 8, 10} ∧
      (1 : Fin 12) ∉ priorCoords sched12 1 ∧ (0 : Fin 12) ∉ priorCoords sched12 0 := by
  decide

end Package

end

#print axioms Nock.NockVMROM.Thm54.Unhosted309.computeWalkRootEvent309_congr
#print axioms Nock.NockVMROM.Thm54.Unhosted309.computePrefixGammaEventOf309_congr
#print axioms Nock.NockVMROM.Thm54.Unhosted309.summand8_readsOn
#print axioms Nock.NockVMROM.Thm54.Unhosted309.summand5_readsOn

end Unhosted309
end Nock.NockVMROM.Thm54
