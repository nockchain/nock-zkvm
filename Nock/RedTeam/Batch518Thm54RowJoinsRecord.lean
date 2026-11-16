/-
  Nock/RedTeam/Batch518Thm54RowJoinsRecord.lean

  **Record.**

  * `TracesBindsHyps` still a parameter of `strategyOfTraces`.
  * K-level `recordHalfJoin_of_deployed` landed.
  * Compiled STOPs: `decodeMemoryRow_readRoot_child_is_atom0` /
    `RemainingBindMemRec`; `ComputeJoinSoundRemaining`.
  * `bindsDropBlockersAfter` still 3; `TracesBindsHyps` still a parameter.
-/
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch509Thm54WrapSpecialize
import Nock.RedTeam.Batch513Thm54ActiveMemPower
import Nock.RedTeam.Batch517Thm54DropBindsHyps
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding

set_option autoImplicit false

namespace Nock.RedTeam.Batch518

open Nock.RedTeam.Batch448
open Nock.RedTeam.Batch509
open Nock.RedTeam.Batch513
open Nock.RedTeam.Batch517

theorem historical_openConjunctsAfterVer_still_seven :
    openConjunctsAfterVer.length = 7 :=
  openConjunctsAfterVer_length

theorem live_openConjunctsAfterWrap_is_five :
    openConjunctsAfterWrap.length = 5 :=
  openConjunctsAfterWrap_length

theorem live_list_not_empty :
    openConjunctsAfterWrap ≠ [] := by
  decide

theorem tracesBindsHyps_still_present :
    "strategyOfTraces takes TracesBindsHyps" ∈
      Nock.RedTeam.Batch465.CHIP_SFE_REMAINING_BEFORE_H15B :=
  tracesBindsHyps_not_dropped

theorem remainingJoin_is_decode_atom0
    (q : ℕ) {K : Type} [Field K] (data : Nock.MemoryTable.DTmem K)
    (child : Nock.Walk.NTree (Nock.MemoryTable.MState × Nock.MemoryTable.DTmem K)) :
    ((Nock.NockVMROM.Thm54.HostileSkeletonDecoding.decodeMemoryRow (K := K) q
        (.node (.read_root, data) [child])).memoryRecord
      (by simp [Nock.NockVMROM.Thm54.HostileSkeletonDecoding.decodeMemoryRow,
        Nock.NockVMROM.Thm54.HostileSkeletonDecoding.decodeMemoryRowIn_readRoot_state,
        Nock.NockVMROM.Thm54.memoryMemRecKind])).child = Nock.Noun.atom 0 := by
  simp [Nock.NockVMROM.Thm54.HostileSkeletonDecoding.decodeMemoryRow,
    Nock.NockVMROM.Thm54.HostileSkeletonDecoding.decodeMemoryRowIn,
    Nock.NockVMROM.Thm54.HostileSkeletonDecoding.nounByFP,
    Nock.Walk.bfsForest_nil]

end Nock.RedTeam.Batch518

#print axioms Nock.RedTeam.Batch518.historical_openConjunctsAfterVer_still_seven
#print axioms Nock.RedTeam.Batch518.live_openConjunctsAfterWrap_is_five
#print axioms Nock.RedTeam.Batch518.remainingJoin_is_decode_atom0
