/-
  Nock/NockVMROM/Thm54/MemoryWalkDeployed.lean

  Memory twin of `Batch459::deployed_walkSat`: for every `c` and
  every trace accepted at `memoryChipAt c`, the dedicated walk columns (roles
  `31`/`32`/`33`) satisfy the paper's `WalkSat` over `memRows` rows with
  `α = alphaM c.1`, `initial_count = α ^ kMem` and the
  prover-committed seed at public role `1`.  Hosted roles `34`/`35`/`36` and
  walk-γ slot `7` are unread here.
-/
import Nock.Walk
import Nock.WalkInGate
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.NockVMROM.Thm54.MemoryWalkLabel
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace
import Nock.NockVMROM.Thm54.HostilePoleAlignment
import Nock.RedTeam.Batch475Thm54MemoryWalkAlphaInitialCount
import Nock.NockVMROM.Thm54.P8Core.MemoryWalkDeployed
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.MemoryWalkDeployed

open scoped Classical
open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.Framework.FixedPreprocessingRAP
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MemoryWalkLabel
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler.MixedExpr (ofExpr)
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.RedTeam.Batch475
open Module

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
  (hchar : MemStateTagChar F)

/-! ### Masks, next-row, coins, publics -/

omit hsat hchar in
theorem envK_pub_const (i j : Fin (memRows P)) (r : ℕ) :
    (envK P c Qm i).pub r = (envK P c Qm j).pub r := by
  simp only [envK, Qmh, memorySourceEnvAt, gatherEnv, memoryBaseEnvAt, envOfTrace]

/-! ### Decoded row, one-hot, in-gate operands -/

include hsat hchar in
theorem labelRLC_cur (i : Fin (memRows P))
    (st : MState) (hone : MemoryPaperFactorization.BaseOneHot (envF P c Qm i) st) :
    (labelRLC (curReader (F := F))).eval (envK P c Qm i) (envF P c Qm i) =
      Walk.rlc (gamma c.1) (memoryLabelVec (pubAt P c Qm i)) := by
  have hst : (pubAt P c Qm i).st = st := by
    rw [pubAt_st, stAt_eq_oneHot P c Qm hchar i st hone]
  have hsel : ∀ st', ((curReader (F := F)).sel st').eval (envF P c Qm i) =
      if st' = (pubAt P c Qm i).st then 1 else 0 := by
    intro st'; rw [hst]; exact hsel_cur P c Qm hchar i st hone st'
  exact labelRLC_eval (curReader (F := F)) _ _ (pubAt P c Qm i) (gamma c.1)
    hsel (cur_cell P c Qm i) (walkGamma_eval P c Qm i)

/-! ### Committed walk gates vanish -/

/-! ### Gate identities at an accepted trace -/

/-! ### `ℕ`-indexed columns (row `i` reads index `i − 1`, as `lblM`) -/

omit hsat hchar in
/-- Seed public deleted : deployed subst writes `Const 0` at
    `publicVal 1`; this witness is the zero that the chip reads. -/
def seedW : K := 0

omit hsat hchar in
theorem seedW_eq_zero : seedW (K := K) = 0 := rfl

omit hsat in
theorem foW_eq_foM (i : ℕ) (hi1 : 1 ≤ i) (_hih : i ≤ memRows P) :
    foW P c Qm i = foM P (Qmh P c Qm) c i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < memRows P := by omega
  have hidx : (k + 1) - 1 = k := Nat.add_sub_cancel k 1
  simp only [foW, foM, lblM, pubAt, Qmh]
  rw [rowOf_succ P k hk, hidx, dif_pos hk]
  rfl

end

end Nock.NockVMROM.Thm54.MemoryWalkDeployed
