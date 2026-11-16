/-
  Nock/NockVMROM/Thm54/P8Core/PreSeedCensus.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.PreSeedCensus`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/PreSeedCensus.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.DeployedStaging
import Nock.NockVMROM.Thm54.P8Core.MemoryHaltAtomDecode
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.PreSeedCensus

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedStaging
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.MemoryHaltAtomDecode
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding

noncomputable section

section Production

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The staged view of the package's memory chip (`P.memoryChip` is this view's RAP). -/
abbrev memView : StagedRAPView F 3 deployedChronology :=
  deployedMemoryView P.optimized.family.problem.cfg.memRows_pos P.optimized.memoryNodes
    P.optimized.basis P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit
    P.optimized.family.problem.cfg.kMem

/-- Row `i`'s committed base environment, coin-free (`memoryBaseEnv`: package challenge map). -/
abbrev preEnv (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : Reified.Env F :=
  P.memoryBaseEnv Qm i

/-- Row `i`'s state, decoded from the selector columns `0, 1, 2`. -/
def preState (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : MState :=
  memoryStateOf (preEnv P Qm i)

/-- Row `i`'s committed pre-seed atom (column `atomCol = 180`). -/
def preAtom (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : F :=
  (preEnv P Qm i).trace atomCol

/-- 1-indexed pre-`z` label (state, atom), with `lblM`'s out-of-range convention (row `0`). -/
def preLbl (Qm : Fin P.memoryChip.rap.w → F[X]) (j : ℕ) : MState × F :=
  if hj : j - 1 < P.optimized.family.problem.cfg.memRows then
    (preState P Qm ⟨j - 1, hj⟩, preAtom P Qm ⟨j - 1, hj⟩)
  else
    (preState P Qm ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩,
      preAtom P Qm ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩)

/-- Pre-`z` fanout (`fanoutMem` of the selector state). -/
def preFo (Qm : Fin P.memoryChip.rap.w → F[X]) : ℕ → ℕ :=
  fun j => fanoutMem (preLbl P Qm j).1

end Production

section Production2

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The decoded noun at aggregate-BFS position `i` of the pre-`z` forest. -/
def preZNoun (q : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) (i : ℕ) : Noun :=
  decodePre K q (buildTF P.optimized.family.problem.cfg.kMem (preFo P Qm) (preLbl P Qm)
    P.optimized.family.problem.cfg.memRows i)

end Production2

section Bridge

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem lblM_fst_eq_preLbl (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) (j : ℕ) :
    (lblM P Qm c j).1 = (preLbl P Qm j).1 := by
  unfold lblM preLbl
  split_ifs <;> rfl

theorem foM_eq_preFo (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : foM P Qm c = preFo P Qm := by
  funext j
  simp only [foM, preFo, lblM_fst_eq_preLbl]

/-- **§3: on every accepted memory trace, the decoder's noun at every position of the committed
forest is the pre-`z` noun.** -/
theorem accepted_decode_eq_preZNoun (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm) (q i : ℕ) :
    decodeNoun q (buildTF P.optimized.family.problem.cfg.kMem (foM P (honestQm P c Qm) c)
        (lblM P (honestQm P c Qm) c) P.optimized.family.problem.cfg.memRows i) =
      preZNoun P q (honestQm P c Qm) i := by
  rw [foM_eq_preFo, preZNoun]
  refine decodeNoun_buildTF_eq_decodePre q _ _ _ _ _ (lblM_fst_eq_preLbl P _ c) ?_ i
  intro j hj
  unfold lblM preLbl at *
  split_ifs at hj ⊢ with hlt
  · have hst : (decodeMemPub P (honestQm P c Qm) c ⟨j - 1, hlt⟩).st = .halt := hj
    have := decodeMemPub_halt_leaf_eq_atom P c Qm hsat ⟨j - 1, hlt⟩ hst
    exact congrArg (leafAtomOf q) this
  · have hst : (decodeMemPub P (honestQm P c Qm) c
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).st = .halt := hj
    have := decodeMemPub_halt_leaf_eq_atom P c Qm hsat
      ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩ hst
    exact congrArg (leafAtomOf q) this

end Bridge

end

end Nock.NockVMROM.Thm54.PreSeedCensus
