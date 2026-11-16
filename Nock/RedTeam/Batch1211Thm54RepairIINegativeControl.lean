/-
  Nock/RedTeam/Batch1211Thm54RepairIINegativeControl.lean

  `gen_honest_accepted` needs `hα : alphaM honestTuple = memoryWalkAlpha`, which holds at the
  generated package only because the chain now passes `mwa := α` (repair (ii), §5 "ok sg").  Two
  controls show the receipt genuinely consumes (ii):

  * **Semantic (compiled here).**  At EVERY built package, if the timestamp coin
    `E.cfg.challenges.α` differs from the memory walk coin `I.memoryWalkAlpha`, the canonical
    memory trace is REJECTED by the family memory chip at the honest tuple
    (`mwa_free_memory_rejected`), so `DeployedAcceptanceAt P P.honestTuple (QcH P) (QmH P)` is
    FALSE (`mwa_free_not_accepted`).  The mechanism is the committed boundary gate
    `firstMask · (ln − chal 3)` (`MemoryWalkDeployed.walkLn_row0`) against the canonical trace's
    `ln(row 0) = I.memoryWalkAlpha` (`Batch994.canonical_ln_row0`); this is `Batch994`'s
    `honest_memory_acceptance_forces_walk_alpha`, read contrapositively.  Before (ii) the chain
    passed `mwa := compilerWalkCoin packageOrbit`, and no §1 hypothesis forced it to equal `α`
    (`Batch994.gen_honest_memory_rejected`).
  * **Elaboration (scratch, recorded).**
-/
import Nock.RedTeam.Batch994Thm54HonestMemoryAcceptance
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1211

open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.RedTeam.Batch906

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

/-- **With the memory walk coin free (`≠ α`), the honest memory trace is rejected** by the family
memory chip at the honest tuple, at every built package. -/
theorem mwa_free_memory_rejected (E : BuildableNockExecution F K) (I : Inputs E)
    (R : CommitmentResidual E)
    (hzero : I.computeChallenges =
      (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec) (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hne : E.cfg.challenges.α ≠ I.memoryWalkAlpha) :
    ¬ RAP.SatisfiesWithPreprocessing
      ((buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).memoryChipAt
        (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).honestTuple)
      (QmH (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF)) := fun hsat =>
  hne (Batch994.honest_memory_acceptance_forces_walk_alpha E I R hzero hprl hmore hord hordM
    hrows hgenF hF hsat)

/-- **The negative control for `gen_honest_accepted`:** with `mwa ≠ α`, honest acceptance at both
family chips at the honest tuple FAILS (its memory half is refuted). -/
theorem mwa_free_not_accepted (E : BuildableNockExecution F K) (I : Inputs E)
    (R : CommitmentResidual E)
    (hzero : I.computeChallenges =
      (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec) (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hne : E.cfg.challenges.α ≠ I.memoryWalkAlpha) :
    ¬ DeployedAcceptanceAt (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF)
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).honestTuple
      (QcH (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF))
      (QmH (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF)) := fun hacc =>
  mwa_free_memory_rejected E I R hzero hprl hmore hord hordM hrows hgenF hF hne hacc.memory_satisfies

end Nock.RedTeam.Batch1211

#print axioms Nock.RedTeam.Batch1211.mwa_free_memory_rejected
#print axioms Nock.RedTeam.Batch1211.mwa_free_not_accepted
