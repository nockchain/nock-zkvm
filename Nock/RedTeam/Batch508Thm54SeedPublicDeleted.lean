/-
  Nock/RedTeam/Batch508Thm54SeedPublicDeleted.lean

  `walkSubst` / `walkBoundarySubst`
  write `Const 0` at `publicVal 1`; `walkSeed` pin dropped;
  `exactMemoryWalkRowEnv` seed argument is `0`.  Deployed masked
  init/step never read `pubv 1` (`AIR.lean` `walkAccInitMasked`).
-/
import Nock.AIR
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.RedTeam.Batch448Thm54VerTransfer

set_option autoImplicit false

namespace Nock.RedTeam.Batch508

open Nock.Reified
open Nock.Reified.Trans
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.RedTeam.Batch448

/-- Deployed subst ignores slots 9..11. -/
theorem walkSubst_pub1_is_zero : walkSubst .publicVal 1 = .Const 0 := rfl

theorem walkBoundarySubst_pub1_is_zero : walkBoundarySubst .publicVal 1 = .Const 0 := rfl

/-- Masked init does not mention the seed public (`pubv 1`). -/
theorem walkAccInitMasked_no_seed :
    walkAccInitMasked = .Sub (Reified.tc 2) (.Mul (pubv 0) (Reified.tc 4)) :=
  rfl

theorem openConjunctsAfterVer_still_seven :
    openConjunctsAfterVer.length = 7 :=
  openConjunctsAfterVer_length

end Nock.RedTeam.Batch508

#print axioms Nock.RedTeam.Batch508.walkSubst_pub1_is_zero
#print axioms Nock.RedTeam.Batch508.walkBoundarySubst_pub1_is_zero
#print axioms Nock.RedTeam.Batch508.walkAccInitMasked_no_seed
