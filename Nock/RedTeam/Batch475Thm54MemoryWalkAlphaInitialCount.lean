/-
  Nock/RedTeam/Batch475Thm54MemoryWalkAlphaInitialCount.lean

  Paper, re-read at source: the memory walk is the FOREST recognizer.  Over `k` roots its inputs are
  `(seed, initial_count) = (Σ_{i=1}^k RLC^γ(slt_i) · α^i, α^k)` (`:1006`), with `(α, γ)` the
  verifier's responses — not `Thm:Walk_IOP`'s single-root `(RLC^γ(slt)·α, α)` (`:962`).  The count
  starts at `α^k` because the `k` roots occupy the line indices `α^1..α^k` of the seed, so the
  first discovered child is indexed `α^{k+1}` (`count(1) = initial_count · Σ st · α^fanout`,
  `:813`, read at the forest's `initial_count`).  So the coin's value is `alphaM c.1 ^ kMem` with
  `kMem = cfg.kMem` the (verifier-known) memory root count, at memory publics `6..8`
  (`ExactMemoryCoordinatePins.walkInitialCount`), and the walk's `α` challenge at memory slot
  `3` is `alphaM c.1` (`memoryKOfTuple`).

  No
  memory gate, label or column moved.

  Receipts are at `P.memoryChipAt c` / the family public map; the honest identity is for the
  generic package (no fixture).
-/
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.P8Core.Batch475Thm54MemoryWalkAlphaInitialCount
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch475

open scoped Polynomial
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.CoordinateBasis

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The deployed memory chip at `c` reads `familyMemoryPublic c` as its public valuation. -/
theorem memoryChipAt_reads_family_publics (c : OptimizedProductionChallengeTuple K F) :
    P.memoryChipAt c =
      DeployedChipFamily.memoryChipAt P.optimized.family.problem.cfg.memRows_pos
        P.optimized.memoryNodes P.optimized.basis
        (memoryPublicOfTuple P.optimized.basis P.optimized.verifier.raw.claim
          P.optimized.family.problem.cfg.kMem P.optimized.memoryPublic c)
        P.optimized.orbit c P.optimized.family.problem.cfg.kMem := rfl

/-- The walk-`α` challenge the memory chip reads at slot `3` is the same coin. -/
theorem memory_walkAlpha_is_coin (c : OptimizedProductionChallengeTuple K F) :
    memoryKOfTuple c 3 = alphaM c.1 := rfl

/-- **`initial_count` and the walk-α challenge agree at every tuple**: the forest recognizer's
premise `initial_count = α^k` at the verifier's `α` (`:1006`) holds unconditionally at the
deployed memory chip. -/
theorem memory_forest_premise_holds (c : OptimizedProductionChallengeTuple K F) :
    (∑ k : Fin 3, P.familyMemoryPublic c (6 + 3 * 0 + (k : ℕ)) • P.optimized.basis k) =
      memoryKOfTuple c 3 ^ P.optimized.family.problem.cfg.kMem :=
  memory_initialCount_is_coin P c

/-- Off `6..8` the family memory map is the package map (seed, `requests`, …). -/
theorem memory_family_publics_off_block (c : OptimizedProductionChallengeTuple K F)
    (j : ℕ) (hj : ¬ (6 ≤ j ∧ j < 9)) :
    P.familyMemoryPublic c j = P.optimized.memoryPublic j :=
  memoryPublicOfTuple_eq_pkg _ _ _ _ c j hj

/-- **Honest identity (generic package).**  At the honest tuple, once the memory `chalVal`
agrees, the deployed memory chip IS the package's memory chip — the memory twin of
`computeChipAt_honest_of_chalVal`, now through `familyMemoryPublic_honest_of_chalVal`. -/
theorem memoryChipAt_honest
    (h : memoryChalValOfTuple P.optimized.basis P.honestTuple = P.optimized.memoryChallenge) :
    P.memoryChipAt P.honestTuple = P.memoryChip := by
  simp only [OptimizedFullStrictNockVMROMPackage.memoryChipAt,
    OptimizedFullStrictNockVMROMPackage.memoryChip, DeployedChipFamily.memoryChipAt, h,
    P.familyMemoryPublic_honest_of_chalVal h]

/-- **The move is not vacuous**: at two tuples whose memory coins have different `k`-th powers,
the deployed memory chip's `initial_count` publics differ. -/
theorem memory_initialCount_varies_with_tuple (c c' : OptimizedProductionChallengeTuple K F)
    (hne : alphaM c.1 ^ P.optimized.family.problem.cfg.kMem ≠
      alphaM c'.1 ^ P.optimized.family.problem.cfg.kMem) :
    P.familyMemoryPublic c ≠ P.familyMemoryPublic c' := by
  intro heq
  apply hne
  rw [← memory_initialCount_is_coin P c, ← memory_initialCount_is_coin P c', heq]

end

end Nock.RedTeam.Batch475

#print axioms Nock.RedTeam.Batch475.memoryChipAt_reads_family_publics
#print axioms Nock.RedTeam.Batch475.memory_initialCount_is_coin
#print axioms Nock.RedTeam.Batch475.memory_forest_premise_holds
#print axioms Nock.RedTeam.Batch475.memory_family_publics_off_block
#print axioms Nock.RedTeam.Batch475.memoryChipAt_honest
#print axioms Nock.RedTeam.Batch475.memory_initialCount_varies_with_tuple
