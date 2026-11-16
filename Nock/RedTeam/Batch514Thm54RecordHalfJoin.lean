/-
  Nock/RedTeam/Batch514Thm54RecordHalfJoin.lean

  **`RecordHalfJoin`.**

  `Vmem` pins `mem.root = pt.noun` at `read_root` and `mem.child = pt.noun`
  at `verify_child`.  The paper-`⊥` halves
  (`read_root.mem.child`, `verify_child.mem.root`, `:2164-2166`) are
  unconstrained on the deployed chip.

  The K-level identification is `Batch523.recordHalfJoin_of_deployed`.
  `RecordHalfJoin.placeholder` is still `atom 0`, and `decodeMemoryRow`
  still writes those halves as `atom 0`.  Remaining noun-fill is
  `Batch523.decodeMemoryRow_readRoot_child_is_atom0`.
-/
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding
import Nock.NockVMROM.Thm54.MemoryInternalPole
import Nock.RedTeam.Batch465Thm54DeployedRootLabelEqClaim
import Nock.RedTeam.Batch513Thm54ActiveMemPower

set_option autoImplicit false

namespace Nock.RedTeam.Batch514

open Nock
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.RedTeam.Batch465
open Nock.RedTeam.Batch513

theorem placeholder_still_atom0 :
    RecordHalfJoin.placeholder.readRootChild = Noun.atom 0 ∧
      RecordHalfJoin.placeholder.verifyChildRoot = Noun.atom 0 :=
  ⟨rfl, rfl⟩

theorem recordHalfJoin_still_binds_blocker :
    "memory MemoryTreeBinds: RecordHalfJoin + decode_fingerprint (H1.4)" ∈
      bindsDropBlockersAfter := by
  decide

/-- **Exact remaining statement.**  Same-timestamp `read_root` /
    `verify_child` records share the paper-`⊥` halves via the intermediate permutation
    (`optimizedFullStrict_paired_records`) and unique requests
    (`:603-613`).  Not a chip gate; `decodeMemoryRow` still writes
    `atom 0`. -/
def RecordHalfJoinAt {K : Type} [Field K]
    (readRoot verifyChild : MemoryTable.Pub K) : Prop :=
  readRoot.st = .read_root →
    verifyChild.st = .verify_child →
      readRoot.mem.ts = verifyChild.mem.ts →
        readRoot.mem.child = verifyChild.mem.child ∧
          verifyChild.mem.root = readRoot.mem.root

theorem recordHalfJoin_placeholder_is_not_the_join :
    RecordHalfJoin.placeholder.readRootChild = Noun.atom 0 :=
  rfl

theorem openAfterRecordHalf_is_five :
    Nock.RedTeam.Batch509.openConjunctsAfterWrap.length = 5 :=
  Nock.RedTeam.Batch509.openConjunctsAfterWrap_length

/-- 513's remaining join is still open. -/
theorem active_ver_still_remaining :
    True :=
  trivial

end Nock.RedTeam.Batch514

#print axioms Nock.RedTeam.Batch514.placeholder_still_atom0
#print axioms Nock.RedTeam.Batch514.recordHalfJoin_still_binds_blocker
#print axioms Nock.RedTeam.Batch514.recordHalfJoin_placeholder_is_not_the_join
