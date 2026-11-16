/-
  Nock/NockVMROM/Thm54/P8Core/WrapFixesVcomp.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.WrapFixesVcomp`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/WrapFixesVcomp.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.ExecOfTraces
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.WrapFixesVcomp
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.WrapFixesVcomp

open scoped Polynomial
open Polynomial
open Nock
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.Reified
open Nock.Framework
open MonolithicRAP
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {K : Type} [Field K]

noncomputable section

variable {F : Type} [Field F] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem lblCAt_vcomp_of_vcompAt
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.compRows)
    (hv : VcompAt (rowEnvAt P c (familyQc P c Qc) i)) :
    let env := rowEnvAt P c (familyQc P c Qc) i
    let st := computeStateOf (decodeSource env)
    Vcomp (decodeInputs env) (decodePub env st) (decodeDec env) := by
  obtain ⟨st', hone, hV⟩ := hv
  have honeE : OneHotSelector (decodeSource (rowEnvAt P c (familyQc P c Qc) i)) st' :=
    oneHot_ofSubst _ st' hone
  have hst : computeStateOf (decodeSource (rowEnvAt P c (familyQc P c Qc) i)) = st' :=
    computeStateOf_of_oneHot honeE
  simpa [hst] using hV

end

end Nock.NockVMROM.Thm54.WrapFixesVcomp
