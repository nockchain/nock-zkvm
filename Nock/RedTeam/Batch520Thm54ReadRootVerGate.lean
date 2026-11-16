/-
  Nock/RedTeam/Batch520Thm54ReadRootVerGate.lean

  Coin-free base gate
  `readRootVerGate`: coordinate-0 expansion of
  `readRootSel · (1 − ver) = 0`.
-/
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.PaperResourceCounts
import Nock.NockVMROM.Thm54.GoldilocksParameters
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.RedTeam.Batch519Thm54CancellationAttack

set_option autoImplicit false

namespace Nock.RedTeam.Batch520

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.Thm54Resources
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis
open Module

/-! ## Committed shape -/

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem readRootVerGate_mem (b : Basis (Fin 3) F K) :
    readRootVerGate b ∈ baseTransitionGates b := by
  simp [baseTransitionGates]

theorem base_length_is_six (b : Basis (Fin 3) F K) :
    (baseTransitionGates b).length = 6 :=
  baseTransitionGates_length b

theorem deployed_s_is_153 :
    memoryTransitionGates 3 = 156 ∧ memoryConstraints 3 = 156 :=
  ⟨memoryTransitionGates_deployed, memoryConstraints_deployed⟩

theorem degree_stays_four :
    maxConstraintDegree = 4 :=
  rfl


/-- Synthetic physical env of an unserved `read_root`: selector column 2
    is `1`, role-39 coord 0 (column 123) is `0`. -/
def unservedReadRootEnv : Env F where
  trace := fun i => if i = 2 then 1 else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

theorem readRootVerGate_eval_unserved (b : Basis (Fin 3) F K) :
    (readRootVerGate b).eval (unservedReadRootEnv (F := F)) =
      coord b (1 : K) (0 : Fin 3) := by
  simp [readRootVerGate, CoeffExpr.eval, bcur, extCoord, unservedReadRootEnv]

/-- Negative control: the unserved `read_root` fails the new gate
    whenever `1` has a nonzero first coordinate (true of every
    production `stdCoordBasis`). -/
theorem unserved_read_root_rejected
    (b : Basis (Fin 3) F K)
    (h1 : coord b (1 : K) (0 : Fin 3) ≠ 0) :
    (readRootVerGate b).eval (unservedReadRootEnv (F := F)) ≠ 0 := by
  rw [readRootVerGate_eval_unserved]
  exact h1


theorem figures_unmoved (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    GoldilocksParameters.goldilocksHostileFailureBound p8Work ioWork
      (2 ^ 31) (2 ^ 31) < 1 / (2 : Rat) ^ 123 :=
  GoldilocksParameters.hostile_soundness_at_paper_configuration
    p8Work ioWork hp8 hio

theorem figures_real_31 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ RealProgramSoundness.p8Majorant R M Λ A) :
    GoldilocksParameters.goldilocksHostileFailureBound p8Work
        (FiniteIO.ioFailureUnionBound 10 (3 * R) M
          (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : Rat) ^ 122 :=
  RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_31
    R M Λ A p8Work hR hM hΛ hA hp8

theorem figures_real_32 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ RealProgramSoundness.p8Majorant R M Λ A) :
    GoldilocksParameters.goldilocksHostileFailureBound p8Work
        (FiniteIO.ioFailureUnionBound 10 (3 * R) M
          (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : Rat) ^ 120 :=
  RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_32
    R M Λ A p8Work hR hM hΛ hA hp8

end Nock.RedTeam.Batch520

#print axioms Nock.RedTeam.Batch520.deployed_s_is_153
#print axioms Nock.RedTeam.Batch520.unserved_read_root_rejected
#print axioms Nock.RedTeam.Batch520.figures_unmoved
