/-
  Nock/NockVMROM/Thm54/P8Core/DeployedStaging.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.DeployedStaging`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/DeployedStaging.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
import Nock.NockVMROM.Thm54.OptimizedComputeFinal
import Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 200000
open scoped BigOperators Classical

namespace Nock.NockVMROM.Thm54.DeployedStaging

open Nock
open Nock.Framework
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.Staging
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Module

/-- Memory `𝕂`-role → round (roles `0..57`, physical columns `6 + 3r + k`). -/
def memoryRoleRound (r : ℕ) : ℕ :=
  if r ∈ [0, 1, 2, 5, 6, 7, 10, 11, 12, 19, 20, 21, 22, 23, 24, 30] then 1
  else if r ∈ [15, 16, 17, 18, 34, 35, 36, 39, 45, 46, 47, 48, 49, 51, 52, 53, 54, 56] then 0
  else 2

/-- Memory physical column → round. -/
def memoryColRound (c : ℕ) : ℕ :=
  if c < 6 then 0
  else if c = 153 ∨ c = 154 then 0
  else if c < 180 then memoryRoleRound ((c - 6) / 3)
  else 0

/-- **The chronology the deployed chips share**: the eleven coordinates of the landed tuple
(`FormRAxisEvent.landedVec` order), three blocks. -/
def deployedChronology : ChallengeChronology 3 where
  numChallenges := 11
  sampledAfter := ![1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1]

/-- A staged view of a deployed RAP: its own width, a round schedule of that width and the
shared chronology.  The RAP is the deployed one; nothing is a dummy. -/
structure StagedRAPView (F : Type*) [Field F] (rounds : ℕ) (chron : ChallengeChronology rounds)
    where
  rap : RAP F
  width : ℕ
  hw : rap.w = width
  schedule : RoundSchedule width rounds
  /-- The sampled challenges each column's committed values may depend on (as in
  `StagedChip.columnChallenges`). -/
  columnChallenges : Fin width → Finset (Fin chron.numChallenges)
  /-- **Commit before sample** (as in `StagedChip.columns_commit_before_sampling`). -/
  columns_commit_before_sampling :
    ∀ c, ∀ j ∈ columnChallenges c, chron.usableByColumnOf (schedule.roundOf c) j

/-- B1's column → challenge map: a column of round `r` may read exactly the coins sampled before
round `r` (round 0: none; round 1: `z, a, b, c`; round 2: all eleven). -/
def roundChallenges (r : Fin 3) : Finset (Fin deployedChronology.numChallenges) :=
  Finset.univ.filter fun j => ((deployedChronology.sampledAfter j : Fin 3) : ℕ) < (r : ℕ)

theorem roundChallenges_usable (r : Fin 3) :
    ∀ j ∈ roundChallenges r, deployedChronology.usableByColumnOf r j :=
  fun _ hj => (Finset.mem_filter.mp hj).2

def memoryRoundFin (c : Fin 205) : Fin 3 :=
  ⟨memoryColRound c, by unfold memoryColRound memoryRoleRound; split_ifs <;> omega⟩

def memoryBlockWidth : Fin 3 → ℕ := ![85, 48, 72]

set_option maxRecDepth 20000 in
theorem memoryBlockWidth_eq (r : Fin 3) :
    memoryBlockWidth r = (Finset.univ.filter fun c : Fin 205 => memoryRoundFin c = r).card := by
  fin_cases r <;> decide

def deployedMemorySchedule : RoundSchedule 205 3 where
  roundOf := memoryRoundFin
  width := memoryBlockWidth
  width_eq := memoryBlockWidth_eq

section Views

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **B1.**  The staged view of the deployed memory chip, `w = 205`, `s = 156`. -/
noncomputable def deployedMemoryView {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictExtension.StrictOrbitDomain F 3 h) (kMem : ℕ) :
    StagedRAPView F 3 deployedChronology where
  rap := (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap
  width := 205
  hw := (OptimizedMemoryRAP.finalMemoryRAP_fingerprint hn nodes b chalVal pubVal orbit kMem).1
  schedule := deployedMemorySchedule
  columnChallenges := fun c => roundChallenges (memoryRoundFin c)
  columns_commit_before_sampling := fun c => roundChallenges_usable (memoryRoundFin c)

end Views

end Nock.NockVMROM.Thm54.DeployedStaging
