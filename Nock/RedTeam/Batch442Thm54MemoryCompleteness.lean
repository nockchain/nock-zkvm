/-
  Nock/RedTeam/Batch442Thm54MemoryCompleteness.lean

  **Completeness, generic and at the fixtures.**

  * `MemoryWalkLabelObligations` (a conjunct of `MemorySampledObligations` since this move) is
    supplied at the generic builder from `E.traversal.2` + row acceptance
    (`BuildableChips.memoryWalkLabelObligations`), not by fixture `rfl`; F73 additionally
    (`OptimizedMemorySameExecution.honest_memoryWalkLabelObligations`).
  * The four in-gate walk gates vanish on every canonical memory row
    (`MemoryWalkLabelCanonical.canonical_inGateWalkGates`), so
    `canonicalFinalMemoryTrace_satisfies` and `canonicalMemoryRealization` keep their statements.
  * `memoryChipAt honestTuple = memoryChip` once `chalVal` agrees
    (`memoryChipAt_honest_of_chalVal`); slot `7` at the honest tuple is the family's `walkGamma`.
-/
import Nock.NockVMROM.Thm54.BuildableChips
import Nock.NockVMROM.Thm54.MemoryWalkLabelCanonical
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch442

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

section Generic

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [Fintype F] [DecidableEq K] [DecidableEq F]
  [FiniteDimensional F K] [CharP K (ringChar K)]

/-- Generic: every buildable execution's sampled assignment meets the walk-label obligations. -/
theorem generic_obligations (E : BuildableNockExecution F K) (I : BuildableChips.Inputs E) :
    (BuildableChips.sampledAssignment E I).MemoryWalkLabelObligations :=
  BuildableChips.memoryWalkLabelObligations E I

/-- The memory chip assignment the generic builder ships carries them (fourth conjunct). -/
theorem generic_chip_assignment_carries
    (E : BuildableNockExecution F K) (I : BuildableChips.Inputs E) :
    (BuildableChips.memoryChipAssignment E I).obligations.2.2.2 =
      BuildableChips.memoryWalkLabelObligations E I := rfl

end Generic

/-! ## F73 -/

section F73

open ConcreteStrictPackage
open OptimizedComputeSampledTrace.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

theorem f73_obligations : honestSampled.MemoryWalkLabelObligations :=
  OptimizedMemorySameExecution.Concrete.honest_memoryWalkLabelObligations

end F73

/-! ## Honest tuple -/

section Honest

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K] [Fintype F]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem honest_slot7 :
    DeployedChipFamily.memoryKOfTuple P.honestTuple 7 = P.optimized.family.walkGamma :=
  P.memoryKOfTuple_honest_walkGamma

theorem chipAt_honest
    (h : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis P.honestTuple =
      P.optimized.memoryChallenge) :
    P.memoryChipAt P.honestTuple = P.memoryChip :=
  P.memoryChipAt_honest_of_chalVal h

end Honest

/-! ## Canonical satisfaction of the in-gate gates (re-export) -/

def CANONICAL_IN_GATE : String :=
  "MemoryWalkLabelCanonical.canonical_inGateWalkGates: all four in-gate walk gates vanish on every canonical row"

end Nock.RedTeam.Batch442

#print axioms Nock.RedTeam.Batch442.generic_obligations
#print axioms Nock.RedTeam.Batch442.f73_obligations
#print axioms Nock.NockVMROM.Thm54.MemoryWalkLabelCanonical.canonical_inGateWalkGates
#print axioms Nock.NockVMROM.Thm54.MemoryPaperFactorization.canonicalFinalMemoryTrace_satisfies
