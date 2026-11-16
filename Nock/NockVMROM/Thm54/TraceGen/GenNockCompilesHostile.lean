/-
  Nock/NockVMROM/Thm54/TraceGen/GenNockCompilesHostile.lean

  M5 finalises it with the user.

  Conjuncts (4) and (5) are about trace pairs FIXED
  BEFORE ALL COINS.  This module does not state or imply `:966`-shaped / interactive soundness at
  the deployed two-message chronology.  Conjunct (5) is on the STRUCTURAL
  `OptimizedFalseAcceptanceSet` (`acc ∧ ¬ Target`); the "wrong result rejected" content is the
  ∀-package theorem `PlacementA.wrong_claim_rejected_evOnly` /
  `HostileSemanticSoundness.wrong_claim_rejected`, not a property of the compiled (true-claim)
  package.

  Conjuncts (4)/(5) are restated at the parallel
  package's twelve-coin tuple, 309 compute trace, `AcceptanceAt309`, `consumedFailureEvent309`,
  `OptimizedProductionGenuineTargetAt309` and `…ProbabilityBound15`; the new conjunct (6) is the
  staged bound at `repartitionedChronology`.  Shape 27/14.  Still nothing about `deployedChronology`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.TraceGen.GoodSeed

open scoped Classical Polynomial
open Polynomial Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage Nock.NockVMROM.Thm54.ProductionP8Containment

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
variable [FiniteDimensional (ZMod p) K]
variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- `nockCompiles_zmod`'s binders
verbatim (27/14: `α αW lmb`, `hwin = programAcc t + 3 < orderOf α ∧ programMemShape αW t ≤ orderOf αW`).
Conclusion: `Stmt ∧ claim ∧ lam ∧ memoryWalkAlpha = αW`, then — spelled out at the program's own nouns,
at the parallel package's twelve-coin tuple —
(4) every trace pair the two chips accept (`PartAStaged.AcceptanceAt309`) at a tuple outside the
    fifteen-summand consumed event computes the program's result (`evalN`; the target's `p8`),
(5) the false-acceptance probability at fixed traces is below the explicit bound
    `ε := optimizedHostileProductionFailureProbabilityBound15 |𝕂| |𝔽| (workloadEv P Λ)
    (ioFailureUnionBound 10 (3N) M |𝕂|) N M`, and
(6) the same `ε` bounds the false-acceptance probability of every STAGED prover strategy at
    `RepartitionedStaging.repartitionedChronology` (B0 fixed, B1 a function of the M1 coins, B2 of
    all twelve); (5) is its constant-strategy corollary.
All three are corollaries of `Stmt` (`acceptance_to_target.p8` + the claim equation;
`complete_false_acceptance_bound`; `staged_false_acceptance_bound`), stated for readability.  Nothing
here states or implies `:966` soundness at `deployedChronology` (see §1 v4). -/
theorem nockCompilesHostile
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy p fuel subject formula)
    (hs : FieldEmbedding.BoundedBy p subject)
    (hf : FieldEmbedding.BoundedBy p formula)
    (hΛp : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) < p)
    (hp : 25 ≤ p)
    (hp64 : p < 2 ^ 64)
    (hK : Module.finrank (ZMod p) K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ p - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α ∧
      programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < p) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (ZMod p) K
      (orbitHeight (programFit α
        (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW
        -- (4) traces accepted by the two chips at a twelve-coin tuple outside the consumed event
        --     compute THIS program's result
        ∧ (∀ (Qc : Fin 309 → (ZMod p)[X])
             (Qm : Fin package.memoryChip.rap.w → (ZMod p)[X])
             (c : PartA12.OptimizedProductionChallengeTuple12 K (ZMod p)),
             PartAStaged.AcceptanceAt309 package Qc Qm c →
             c ∉ PartAStaged.consumedFailureEvent309 package Qc Qm →
             ∃ fuel', Nock.evalN fuel' subject formula = some result)
        -- (5) the fixed-trace false-acceptance probability, ε explicit
        ∧ (∀ (Qc : Fin 309 → (ZMod p)[X])
             (Qm : Fin package.memoryChip.rap.w → (ZMod p)[X]),
             ((Finset.univ.filter fun c =>
                 PartAStaged.AcceptanceAt309 package Qc Qm c ∧
                   ¬ package.OptimizedProductionGenuineTargetAt309 Qc Qm c).card : ℚ) /
                 Fintype.card (PartA12.OptimizedProductionChallengeTuple12 K (ZMod p)) ≤
               PartA12.optimizedHostileProductionFailureProbabilityBound15 (Fintype.card K) (Fintype.card (ZMod p))
                 (OptimizedFailureEventEv.workloadEv package package.optimized.Λ)
                 (FiniteIO.ioFailureUnionBound 10 (3 * package.optimized.family.problem.cfg.compRows)
                   package.optimized.family.problem.cfg.memRows (Fintype.card K))
                 package.optimized.family.problem.cfg.compRows package.optimized.family.problem.cfg.memRows)
        -- (6) the staged false-acceptance probability (H2.3, `repartitionedChronology`), same ε
        ∧ (∀ (Qc : PartA12.OptimizedProductionChallengeTuple12 K (ZMod p) → Fin 309 → (ZMod p)[X])
             (Qm : PartA12.OptimizedProductionChallengeTuple12 K (ZMod p) → Fin package.memoryChip.rap.w → (ZMod p)[X]),
             PartAStaged.StagedTraces12 package Qc Qm →
             ((Finset.univ.filter fun c =>
                 PartAStaged.AcceptanceAt309 package (Qc c) (Qm c) c ∧
                   ¬ package.OptimizedProductionGenuineTargetAt309 (Qc c) (Qm c) c).card : ℚ) /
                 Fintype.card (PartA12.OptimizedProductionChallengeTuple12 K (ZMod p)) ≤
               PartA12.optimizedHostileProductionFailureProbabilityBound15 (Fintype.card K) (Fintype.card (ZMod p))
                 (OptimizedFailureEventEv.workloadEv package package.optimized.Λ)
                 (FiniteIO.ioFailureUnionBound 10 (3 * package.optimized.family.problem.cfg.compRows)
                   package.optimized.family.problem.cfg.memRows (Fintype.card K))
                 package.optimized.family.problem.cfg.compRows package.optimized.family.problem.cfg.memRows) := by
  obtain ⟨P, hS, hclaim, hlam, hmwa⟩ := nockCompiles_zmod α αW lmb hrun hbound hs hf hΛp hp hp64 hK hF hwin hKszChar
  refine ⟨P, hS, hclaim, hlam, hmwa, ?_, ?_, ?_⟩
  · intro Qc Qm c hacc hgood
    obtain ⟨fuel', h⟩ := (hS.acceptance_to_target Qc Qm c hacc hgood).p8
    refine ⟨fuel', ?_⟩
    rw [hclaim] at h
    exact h
  · intro Qc Qm
    exact hS.complete_false_acceptance_bound Qc Qm
  · intro Qc Qm hst
    exact hS.staged_false_acceptance_bound Qc Qm hst

end Nock.NockVMROM.Thm54.TraceGen.GoodSeed

