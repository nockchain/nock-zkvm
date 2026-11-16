/-
  Nock/RedTeam/Batch961Thm54HonestLambdaPairStop.lean

  **Component 11 (λ).**  `decodedLambdaEventOf` is, per decoded root `r ∈ 1..kMem`, the guarded
  zero set of the decoded Form R polynomial `P_r = decodedRootPoly`; the guard is
  `∃ k ≤ E', coeff k P_r ≠ 0`.  §A: if every honest `P_r` is identically `0`, the honest tuple is
  outside (`lam_of_rootPolys_zero`, the guard fails).  Conversely, at an accepted tuple whose
  envelope vanishes, outside implies `P_r = 0` (`FormRBridge.decodedRootPoly_eq_zero_of_not_bad`,
  given `ExpLe`).  So component 11 IS the polynomial identity `P_r ≡ 0` at the canonical traces.
  By `Batch575.formR_counts_zero_iff` that identity needs, on the decoded honest tree:
  `UniqueExponents`, the shift range, balanced read/verify counts, padding and
  `vpaths = [rpaths ++ bitsOf m c]`.  **The circularity:** the only sources of those in the tree
  are `UniqueExponentsBridge.uniqueExponents_decoded_pkg` (takes the WHOLE
  `hgood : c ∉ optimizedFailureEvent`, though its proof projects only components 1, 3, 4),
  `Batch824.expLe_at` (`hgood` through `ts_window`) and `Batch824.r4_path_valid_at` (`hgood`,
  including component 11 itself).  No generator-side proof of honest path validity of
  `decodedMTreeOfEnvs` at the canonical envs exists (no `rpaths` / `vpaths` / `FormRPathValid`
  lemma in `TraceGen/`).  The bundling of `uniqueExponents_decoded_pkg` is formal (a
  component-wise restatement would remove it); the path-validity dependency is real.

  **Component 12 (`reqPair`).**  §B: the event is `liftSeed (pairBadSeeds Λg pairs)`, so at the
  honest tuple it is exactly `z ∉ pairBadSeeds Λg (reqPairsOfEnvs …)` at the canonical memory base
  envs (`pair_iff`).  The pairs put the decoded node of every memory row against
  `requestTargets S st (natLift reqIdx)`, and on `decompose` rows that target is the constant
  `atom 0` (`requestTargets_decompose`, `rfl`) while the decoded node is a cell: a field-distinct
  pair whose bad seeds need not be empty.  The generator's seed choice avoids `{0}`, the p8
  census (compute-skeleton pairs at window `Λ`) and the size-window seeds only
  (`GoodSeed.romSeed`); its budget `seedBudget` has no `M·(2(M⊔Λ)−1)` term.  So the generated
  package's seed is not shown to avoid these pairs.  Closing it is a change of the generator's
  seed choice (a different generated package, and a larger seed budget), not a lemma.
-/
import Nock.RedTeam.Batch909Thm54R4HonestInstance
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch961

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.Reified

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## A. Component 11 is the polynomial identity `P_r ≡ 0` -/

/-- A root whose decoded polynomial is identically `0` contributes no bad pair. -/
theorem decodedRootBad_eq_empty_of_zero {N M : ℕ} (envsC : Fin N → Env K)
    (envsK : Fin M → Env K) (envsF : Fin M → Env F) (kroots r : ℕ)
    (h0 : decodedRootPoly envsC envsK envsF kroots r = 0) :
    decodedRootBad envsC envsK envsF kroots r = ∅ := by
  unfold decodedRootBad
  rw [if_neg]
  rintro ⟨k, -, hk⟩
  rw [h0] at hk
  exact hk (Polynomial.coeff_zero k)

/-- **Sufficiency**: if every honest decoded root polynomial vanishes identically, the honest
tuple is outside the λ-event. -/
theorem lam_of_rootPolys_zero
    (h0 : ∀ r ∈ Finset.Icc 1 P.optimized.family.problem.cfg.kMem,
      decodedRootPoly (P.computeSourceEnv (canonicalComputeTrace P))
        (P.memorySourceEnv (canonicalMemoryTrace P)) (P.memoryBaseEnv (canonicalMemoryTrace P))
        P.optimized.family.problem.cfg.kMem r = 0) :
    P.honestTuple ∉ P.decodedLambdaEventOf (canonicalComputeTrace P) (canonicalMemoryTrace P) := by
  intro hm
  unfold OptimizedFullStrictNockVMROMPackage.decodedLambdaEventOf decodedLambdaEventOfEnvs at hm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hm
  obtain ⟨r, hr, hbad⟩ := hm
  rw [decodedRootBad_eq_empty_of_zero _ _ _ _ _ (h0 r hr)] at hbad
  exact Finset.notMem_empty _ hbad

/-- **Necessity** (the existing lemma, restated at the honest instance): at a tuple whose decoded
envelope vanishes, being outside root `r`'s set forces `P_r = 0`, given `ExpLe`. -/
theorem rootPoly_zero_of_lam
    (r : ℕ) (hr : r ∈ Finset.Icc 1 P.optimized.family.problem.cfg.kMem)
    (hexp : FormRBridge.ExpLe (decodedEnvelopeDeg P.optimized.family.problem.cfg.compRows)
      (decodedMTreeOfEnvs (P.memorySourceEnv (canonicalMemoryTrace P))
        (P.memoryBaseEnv (canonicalMemoryTrace P)) P.optimized.family.problem.cfg.kMem r))
    (hzero : FormRBridge.biv (alphaM P.honestTuple.1) P.honestTuple.2.2.2.lambda
      (decodedRootPoly (P.computeSourceEnv (canonicalComputeTrace P))
        (P.memorySourceEnv (canonicalMemoryTrace P)) (P.memoryBaseEnv (canonicalMemoryTrace P))
        P.optimized.family.problem.cfg.kMem r) = 0)
    (hout : P.honestTuple ∉
      P.decodedLambdaEventOf (canonicalComputeTrace P) (canonicalMemoryTrace P)) :
    decodedRootPoly (P.computeSourceEnv (canonicalComputeTrace P))
        (P.memorySourceEnv (canonicalMemoryTrace P)) (P.memoryBaseEnv (canonicalMemoryTrace P))
        P.optimized.family.problem.cfg.kMem r = 0 := by
  refine FormRBridge.decodedRootPoly_eq_zero_of_not_bad _ _ _ _ r _ _ hexp hzero ?_
  intro hbad
  apply hout
  unfold OptimizedFullStrictNockVMROMPackage.decodedLambdaEventOf decodedLambdaEventOfEnvs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
  exact ⟨r, hr, hbad⟩

/-! ## B. Component 12 is the honest seed against the route-B pairs -/

theorem pair_iff :
    P.honestTuple.1 ∈ PreSeedCensus.reqPairEventOfEnvs K P.q P.optimized.family.problem.cfg.kMem
        (P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ)
        (P.memoryBaseEnv (canonicalMemoryTrace P)) P.optimized.family.problem.cfg.memRows_pos
        (PreSeedCensus.requestTargets P.strategy.skeleton) ↔
      P.objects.cfg.challenges.z ∈ PreSeedCensus.pairBadSeeds (K := K)
        (P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ)
        (PreSeedCensus.reqPairsOfEnvs K P.q P.optimized.family.problem.cfg.kMem
          (P.memoryBaseEnv (canonicalMemoryTrace P)) P.optimized.family.problem.cfg.memRows_pos
          (PreSeedCensus.requestTargets P.strategy.skeleton)) := by
  unfold PreSeedCensus.reqPairEventOfEnvs
  rw [mem_liftSeed_iff]
  rfl

/-- On a `decompose` row the route-B target is the constant `atom 0`, whatever the exponent. -/
theorem requestTargets_decompose (S : SemanticStrategy.SemanticSkeleton) (k : ℕ) :
    PreSeedCensus.requestTargets S .decompose k = .atom 0 := by
  cases k <;> rfl

end

end Nock.RedTeam.Batch961

#print axioms Nock.RedTeam.Batch961.lam_of_rootPolys_zero
#print axioms Nock.RedTeam.Batch961.rootPoly_zero_of_lam
#print axioms Nock.RedTeam.Batch961.pair_iff
#print axioms Nock.RedTeam.Batch961.requestTargets_decompose
