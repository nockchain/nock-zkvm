/-
  Nock/NockVMROM/Thm54/P8Core/Batch475Thm54MemoryWalkAlphaInitialCount.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch475Thm54MemoryWalkAlphaInitialCount`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch475Thm54MemoryWalkAlphaInitialCount.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.FamilyMemoryRows
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

/-- **The memory walk's `initial_count` extension public (base publics `6..8`) is the coin's
`α^k` at every tuple `c`**. -/
theorem memory_initialCount_is_coin (c : OptimizedProductionChallengeTuple K F) :
    (∑ k : Fin 3, P.familyMemoryPublic c (6 + 3 * 0 + (k : ℕ)) • P.optimized.basis k) =
      alphaM c.1 ^ P.optimized.family.problem.cfg.kMem := by
  have hk : ∀ k : Fin 3, P.familyMemoryPublic c (6 + 3 * 0 + (k : ℕ)) =
      coord P.optimized.basis (alphaM c.1 ^ P.optimized.family.problem.cfg.kMem) k := by
    intro k
    simpa using memoryPublicOfTuple_alpha_coord P.optimized.basis
      P.optimized.verifier.raw.claim P.optimized.family.problem.cfg.kMem
      P.optimized.memoryPublic c k
  simp only [hk]
  exact reconstruct_coord P.optimized.basis _

end

end Nock.RedTeam.Batch475
