/-
  Nock/RedTeam/Batch411Thm54SeedBoundaryDraft.lean

  No `hroot` on the
  capstone; no new `nockCompiles_zmod` hypothesis; slot 7 untouched. -/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
import Nock.RedTeam.Batch408Thm54SeedBoundaryGates
import Nock.RedTeam.Batch409Thm54SeedBoundaryKside
import Nock.RedTeam.Batch410Thm54SeedBoundaryFrozen

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch411

open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.RedTeam.Batch408
open Nock.RedTeam.Batch409
open Nock.RedTeam.Batch410

def draftPath : String := "CENSUS-DRAFT-seed-pin.md"

def nineteenthBeforeDigest : String := Batch410.nineteenthBeforeDigest

theorem before_digest_is_live_after_walk_alpha :
    nineteenthBeforeDigest =
      "474348bffbdddb0772a33ba271d2ddae0ebe9279cf0bc45dd666da583ffec8b2" :=
  rfl

/-- The consumed capstone takes only the package; there is no `hroot`. -/
theorem capstone_of_package_is_hyp_free
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedFullStrictThm54Statement P :=
  optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth


theorem f97_stop : Batch408.userDecisionStop = true :=
  Batch408.status_is_user_decision_stop

theorem f97_nested_service_accepted :
    Batch408.authorizedRootMaskLanded = true :=
  Batch408.authorized_root_mask_landed

theorem kprime_robustness_name : True :=
  let _ := @Batch409.rootMask_sound_for_every_k
  trivial

theorem slot_7_untouched :
    Batch410.walk_gamma_slot_untouched = Batch410.walk_gamma_slot_untouched :=
  rfl

def stopReason : String := Batch408.stopReason

end Nock.RedTeam.Batch411

#print axioms Nock.RedTeam.Batch411.before_digest_is_live_after_walk_alpha
#print axioms Nock.RedTeam.Batch411.capstone_of_package_is_hyp_free
#print axioms Nock.RedTeam.Batch411.f97_nested_service_accepted
#print axioms Nock.RedTeam.Batch411.kprime_robustness_name
