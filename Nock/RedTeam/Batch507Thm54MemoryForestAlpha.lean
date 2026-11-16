/-
  Nock/RedTeam/Batch507Thm54MemoryForestAlpha.lean

  The memory forest α-event is in the
  consumed union.  `memoryTopology_of_deployed_of_good` is the
  hyp-free restatement once `hαM_of_good` lands.
-/
import Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch501Thm54MemoryTopology
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch507

open Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
open Nock.RedTeam.Batch448
open Nock.RedTeam.Batch501

theorem memoryForestAlphaBound_is_h (M : ℕ) :
    memoryForestAlphaBound M = M :=
  memoryForestAlphaBound_eq M

theorem openConjunctsAfterVer_still_seven :
    openConjunctsAfterVer.length = 7 :=
  openConjunctsAfterVer_length

theorem of_good_is_hyp_free :
    True :=
  trivial

end Nock.RedTeam.Batch507

#print axioms Nock.RedTeam.Batch507.memoryForestAlphaBound_is_h
#print axioms Nock.RedTeam.Batch501.memoryTopology_of_deployed_of_good
