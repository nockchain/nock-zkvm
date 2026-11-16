/-
  Nock/RedTeam/Batch407Thm54SeedBoundaryBodies.lean

  `decide` on these equalities inside `Batch407Thm54SeedBoundaryRapAttack`
  (package73 / K73cubic) did not return after 100 minutes. Same equalities
  here, no F73 fibre. Do not import package73 / K73cubic.
-/
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.MemoryFactorizationScope

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Nock.RedTeam.Batch407Bodies

open Nock.Reified
open Nock.MemoryTable
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.MemoryFactorizationScope

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem body9_halt :
    ((memQuantity (K := K) .halt 9).subst memorySubst) = .Var .traceCur 9 := by
  rfl

theorem body9_decompose :
    ((memQuantity (K := K) .decompose 9).subst memorySubst) = .Const 0 := by
  rfl

theorem body9_read_root :
    ((memQuantity (K := K) .read_root 9).subst memorySubst) = .Const 0 := by
  rfl

theorem body9_verify :
    ((memQuantity (K := K) .verify_child 9).subst memorySubst) = .Const 0 := by
  rfl

theorem body14_halt :
    ((memQuantity (K := K) .halt 14).subst memorySubst) = .Var .traceCur 14 := by
  rfl

theorem body14_decompose :
    ((memQuantity (K := K) .decompose 14).subst memorySubst) = .Const 0 := by
  rfl

theorem body14_read_root :
    ((memQuantity (K := K) .read_root 14).subst memorySubst) = .Var .traceCur 14 := by
  rfl

theorem body14_verify :
    ((memQuantity (K := K) .verify_child 14).subst memorySubst) = .Var .traceCur 14 := by
  rfl

theorem body21_halt :
    ((memQuantity (K := K) .halt 21).subst memorySubst) = .Var .traceCur 25 := by
  rfl

theorem body21_decompose :
    ((memQuantity (K := K) .decompose 21).subst memorySubst) = .Var .traceCur 25 := by
  rfl

theorem body21_read_root :
    ((memQuantity (K := K) .read_root 21).subst memorySubst) = .Const 0 := by
  rfl

theorem body21_verify :
    ((memQuantity (K := K) .verify_child 21).subst memorySubst) = .Const 0 := by
  rfl

theorem body9 (st : MState) :
    ((memQuantity (K := K) st 9).subst memorySubst) = .Const 0 ∨
      ((memQuantity (K := K) st 9).subst memorySubst) = .Var .traceCur 9 := by
  cases st with
  | halt => exact Or.inr body9_halt
  | decompose => exact Or.inl body9_decompose
  | read_root => exact Or.inl body9_read_root
  | verify_child => exact Or.inl body9_verify

theorem body14 (st : MState) :
    ((memQuantity (K := K) st 14).subst memorySubst) = .Const 0 ∨
      ((memQuantity (K := K) st 14).subst memorySubst) = .Var .traceCur 14 := by
  cases st with
  | halt => exact Or.inr body14_halt
  | decompose => exact Or.inl body14_decompose
  | read_root => exact Or.inr body14_read_root
  | verify_child => exact Or.inr body14_verify

theorem body21 (st : MState) :
    ((memQuantity (K := K) st 21).subst memorySubst) = .Const 0 ∨
      ((memQuantity (K := K) st 21).subst memorySubst) = .Var .traceCur 25 := by
  cases st with
  | halt => exact Or.inr body21_halt
  | decompose => exact Or.inr body21_decompose
  | read_root => exact Or.inl body21_read_root
  | verify_child => exact Or.inl body21_verify

end Nock.RedTeam.Batch407Bodies
