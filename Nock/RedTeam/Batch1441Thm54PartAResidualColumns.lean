import Nock.NockVMROM.Thm54.OptimizedCanonicalTraces
import Nock.NockVMROM.Thm54.P8Core.PartAOpenItems
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1441Thm54PartAResidualColumns.lean

  **L4's open item (a) — the memory residual
  columns `182..204`.**

  Under L1's map they are round 0 (`PartAOpenItems.residual_round_zero`), so `StagedTraces12`
  makes them constants fixed before every coin.  Perfect completeness at the staged schedule
  therefore needs the honest generator to fill them coin-free.  It does:

  * `canonicalMemoryTrace_residual_zero` (package form): the package's honest memory trace is the
    zero polynomial on every residual column;
  * `PartAOpenItems.canonicalFinalMemoryTrace_residual_zero` / `honest_residual_staged`
    (generator form, below the statement): `0` at every challenge / public vector the generator
    is fed, hence constant along any honest strategy;
  * `honest_residual_free_acceptance`: and the twelve-coin memory chip does not read them
    (`PartAOpenItems.memoryChipAt12_satisfies_residual_free`): replacing the honest trace's residual
    columns by anything leaves acceptance at every twelve-coin tuple unchanged.

  No residual column needs a coin
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1441

open scoped Polynomial
open Nock Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.PartA12

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **(a), package form**: the honest memory trace is `0` on every residual column. -/
theorem canonicalMemoryTrace_residual_zero (j : Fin P.memoryChip.rap.w) (hj : 182 ≤ (j : ℕ)) :
    canonicalMemoryTrace P j = 0 :=
  PartAOpenItems.canonicalFinalMemoryTrace_residual_zero _ _ _ _ _ _ j hj

/-- **(a), acceptance**: any residual fill of the honest memory trace is accepted at exactly the
twelve-coin tuples the honest trace is accepted at. -/
theorem honest_residual_free_acceptance (c : OptimizedProductionChallengeTuple12 K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (hagree : ∀ j : Fin P.memoryChip.rap.w, (j : ℕ) < 182 → Qm j = canonicalMemoryTrace P j) :
    RAP.SatisfiesWithPreprocessing (Pkg12.memoryChipAt12 P c) (Pkg12.familyQm12 P c Qm) ↔
      RAP.SatisfiesWithPreprocessing (Pkg12.memoryChipAt12 P c)
        (Pkg12.familyQm12 P c (canonicalMemoryTrace P)) :=
  PartAOpenItems.memoryChipAt12_satisfies_residual_free P c _ _ hagree

/-- The residual columns are round 0 (control: the column just below, `181`, is round 0 too —
`reqIdx`; the last role column `179` is not). -/
theorem residual_rounds :
    (∀ j : Fin 205, 182 ≤ (j : ℕ) → RepartitionedStaging.newMemoryColRound j = 0) ∧
      RepartitionedStaging.newMemoryColRound 179 ≠ 0 := by
  refine ⟨fun j hj => PartAOpenItems.residual_round_zero j (by omega), by decide⟩

end Nock.RedTeam.Batch1441

#print axioms Nock.RedTeam.Batch1441.canonicalMemoryTrace_residual_zero
#print axioms Nock.RedTeam.Batch1441.honest_residual_free_acceptance
#print axioms Nock.RedTeam.Batch1441.residual_rounds
