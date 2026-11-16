/-
  NockvmE2E/Emit/TieCompute.lean

  The `K`-point twin of `accGatesHX_semK` (Compute.lean): the 54 coordinate-level accumulator gates `accGatesHX`
  and the coordinate expansion of the 18 `𝕂` gates `accKGatesHX` agree, gate by gate and in order, when evaluated at an
  arbitrary `K`-algebra point (`evalA`), not only at `F`-environments.  Same proof as the `F`-environment lemma.
-/
import NockvmE2E.Emit.Compute
import NockvmE2E.Emit.TieMixed

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NockvmE2E.Emit

open Nock.Emit Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Module Nock.NockVMROM.Thm54.VclL.Handle.ChipH Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

section SemA
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem evalA_termK_coord (b : Basis (Fin 3) F K) (slots : List (Slot F)) (k : Fin 3) (eA : Env K) :
    evalA eA ((mixedCompile b col0Id (termK slots)) k) = evalA eA ((termCoord slots k)) := by
  induction slots with
  | nil => simp [termK, termCoord, CoeffExpr.sumList, mixedCompile, evalA]
  | cons s l ih =>
    simp only [termK, termCoord, CoeffExpr.sumList, List.foldr_cons] at ih ⊢
    simp [mixedCompile, evalA, ih, col0Id]

theorem accGatesX_semA (b : Basis (Fin 3) F K) (slots : List (Slot F)) (accBase pubBase : ℕ) (eA : Env K) :
    ((accGatesX slots accBase pubBase).map (evalA eA)) =
      (((accKGates slots accBase pubBase).flatMap fun g => List.ofFn (mixedCompile b col0Id g)).map (evalA eA)) := by
  have h0 := evalA_termK_coord b slots 0 eA
  have h1 := evalA_termK_coord b slots 1 eA
  have h2 := evalA_termK_coord b slots 2 eA
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  simp [accGatesX, accKGates, accInitX, accStepX, accTermX, List.range_succ, List.ofFn_succ, mixedCompile,
    evalA, col0Id, cc, h0, h1, h2]

/-- **The compute K-point twin**: `accGatesHX_semK` at a `K`-algebra point. -/
theorem accGatesHX_semA (b : Basis (Fin 3) F K) (eA : Env K) :
    ((accGatesHX (F := F)).map (evalA eA)) =
      (((accKGatesHX (F := F)).flatMap fun g => List.ofFn (mixedCompile b col0Id g)).map (evalA eA)) := by
  simp only [accGatesHX, accKGatesHX, accOf, accKOf, List.flatMap_append, List.map_append,
    accGatesX_semA b _ _ _ eA]

end SemA

end NockvmE2E.Emit

#print axioms NockvmE2E.Emit.accGatesHX_semA
