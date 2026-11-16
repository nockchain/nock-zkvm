/-
  Nock/NockVMROM/Thm54/P8Core/DeployedComputeRows.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.DeployedComputeRows`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/DeployedComputeRows.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.DeployedComputeRows
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54

namespace DeployedComputeRows

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.Framework
open Nock.Framework.Reify
open OptimizedStrictFullPackage
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeSemanticRealization
open OptimizedComputeCorrectedFinal
open ComputePaperPacking
open Module
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

variable (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Characteristic hypothesis the SV block needs, read off the package
(`StateTagChar` injectivity at the point `1`; `OptimizedHostileConfiguration.hchar_of_stateTagChar`). -/
def pkgHchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1 :=
  fun n hn heq =>
    P.stateTagChar hn (by simp : (1 : ℕ) ≤ 11)
      (heq.trans (Nat.cast_one (R := K)).symm)

end DeployedComputeRows

end Nock.NockVMROM.Thm54
