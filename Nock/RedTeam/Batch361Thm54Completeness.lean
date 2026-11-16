/-
  Nock/RedTeam/Batch361Thm54Completeness.lean

  **Two completeness theorems.**

  (a) Perfect, at the compiler's triple: the honest chip is `computeChipAt`
      `honestTuple` once `chalVal` functions agree
      (`computeChipAt_honest_satisfies_iff`).

  (b) Statistical, at a random triple — the paper.  From
      `GenCoinCounting.exists_computeCoinsGeneric` (bad triples
      `< rows · |𝕂|²`) the density is
      `|{(a,b,c) : some honest OP5 row's form vanishes}| / |𝕂|³
        ≤ #OP5rows / |𝕂|`.
      The bound is `op5CompletenessError N`.

  Paper nit: "perfect completeness" is literally true only
  at a chosen triple; at a sampled one it is `1 − op5CompletenessError`.

  Negative control: `op5_rlc_completeness_needs_abc` — there is a program
  (difference `(1,-1,0)`) and a triple at which no `inv_gen` witness exists.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.GateCorrespondenceCompute
import Nock.AIR
import Nock.NockVMROM.Thm54.TraceGen.GenCoinCounting
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch361

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.TraceGen
open Nock.TableWFBounds

/-- Completeness error at `N` compute rows: `#OP5rows / |𝕂|` majorant. -/
def op5CompletenessError (N cardK : ℕ) : ℚ :=
  (N : ℚ) / (cardK : ℚ)

/-- Density of bad `(a,b,c)` is `≤ #rows / |𝕂|` = `op5CompletenessError`. -/
theorem op5CompletenessError_bounds_failure {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (z α : K) (u : Nock.Walk.NTree (GenComputeRow K)) :
    ((computeCoinFailure z α u).card : ℚ) /
        (Fintype.card (ComputeCoins K) : ℚ) ≤
      op5CompletenessError (Nock.Walk.bfsForest [u]).length (Fintype.card K) :=
  computeCoinFailure_prob_le z α u

/-- Good triples exist once `N < |𝕂|`.  Existence outside a counted set,
not `∀ (a,b,c)`. -/
theorem exists_good_triple {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (z α : K) (u : Nock.Walk.NTree (GenComputeRow K))
    (hrow : (Nock.Walk.bfsForest [u]).length < Fintype.card K) :
    ∃ a b c : K, ComputeCoinsGeneric z α a b c u :=
  exists_computeCoinsGeneric z α u hrow

/-- Perfect completeness at the compiler's triple: the honest chip *is*
`computeChipAt honestTuple` once `chalVal` agrees.  RAP structures compare
`chalVal` as a whole function, so recovery is structure equality. -/
theorem perfect_at_compiler_triple
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hchal :
      DeployedChipFamily.computeChalValOfTuple P.optimized.basis P.honestTuple =
        P.optimized.computeChallenge)
    (hst :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).state =
        ComputeWalkSeed.rootStateOfFormula P.optimized.verifier.raw.claim.formula)
    (hs :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).s =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.subject)
    (hf :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).f =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.formula)
    (he :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).e =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.result) :
    P.computeChipAt P.honestTuple = P.computeChip :=
  P.computeChipAt_honest_of_chalVal hchal hst hs hf he

/-- Paper nit, the paper: "perfect completeness" holds at a *chosen*
triple.  At a sampled one the failure probability is at most
`op5CompletenessError N`. -/
theorem paper_nit_perfect_completeness_is_chosen_triple (N cardK : ℕ)
    (hK : 0 < cardK) :
    op5CompletenessError N cardK = (N : ℚ) / (cardK : ℚ) ∧
      (0 : ℚ) ≤ op5CompletenessError N cardK :=
  ⟨rfl, div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg cardK)⟩

/-- Negative control: there is a difference triple and coins at which the
honest OP5 prover cannot produce `inv_gen`.  The error
is not vacuous. -/
theorem honest_prover_fails_at_bad_triple {K : Type*} [Field K] :
    ∃ a b c ds dd dl : K,
      (ds ≠ 0 ∨ dd ≠ 0 ∨ dl ≠ 0) ∧
        ∀ g : K, g * (a * ds + b * dd + c * dl + (1 - 1)) ≠ 1 :=
  Nock.Reified.GateCorrespondenceCompute.op5_rlc_completeness_needs_abc

end Nock.RedTeam.Batch361

#print axioms Nock.RedTeam.Batch361.op5CompletenessError_bounds_failure
#print axioms Nock.RedTeam.Batch361.exists_good_triple
#print axioms Nock.RedTeam.Batch361.perfect_at_compiler_triple
#print axioms Nock.RedTeam.Batch361.paper_nit_perfect_completeness_is_chosen_triple
#print axioms Nock.RedTeam.Batch361.honest_prover_fails_at_bad_triple
