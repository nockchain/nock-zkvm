/-
  Nock/NockVMROM/Thm54/P8Core/MemoryHaltAtomDecode.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.MemoryHaltAtomDecode`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/MemoryHaltAtomDecode.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.FamilyMemoryRows
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.MemoryHaltAtomDecode

open scoped Polynomial
open Nock
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTraces

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)

/-- **The decoder reads the atom column**: row `i`'s committed pre-seed atom. -/
def memoryAtomAt (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : F :=
  (memoryBaseEnvAt P c Qm i).trace atomCol

theorem haltAtomMixed_mem (b : Module.Basis (Fin 3) F K) :
    haltAtomMixed (F := F) ∈ mixedTransitionGates (F := F) (K := K) b := by
  simp [mixedTransitionGates]

variable (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)

include hsat in
/-- **On every accepted trace, a decoded `halt` row's leaf is the lifted atom column.** -/
theorem decodeMemPub_halt_leaf_eq_atom
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hst : (decodeMemPub P (honestQm P c Qm) c i).st = .halt) :
    (decodeMemPub P (honestQm P c Qm) c i).pt.noun.leaf =
      algebraMap F K (memoryAtomAt P c (honestQm P c Qm) i) := by
  have hgate := mixed_at_family P c Qm hsat i haltAtomMixed
    (haltAtomMixed_mem (F := F) (K := K) P.optimized.basis)
  rw [haltAtomMixed_eval] at hgate
  have hst' : memoryStateOf (memoryBaseEnvAt P c (honestQm P c Qm) i) = .halt := by
    simpa [decodeMemPub] using hst
  have hsel : (memoryBaseEnvAt P c (honestQm P c Qm) i).trace 1 = 1 := by
    unfold memoryStateOf at hst'
    split_ifs at hst' with h0 h1 <;> first | exact h1 | cases hst'
  rw [hsel, map_one, one_mul, sub_eq_zero] at hgate
  simpa [decodeMemPub, memoryPtNoun, memoryAtomAt, atomCol] using hgate

end

end Nock.NockVMROM.Thm54.MemoryHaltAtomDecode
