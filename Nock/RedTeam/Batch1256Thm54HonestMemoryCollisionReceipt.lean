import Nock.NockVMROM.Thm54.HostileSkeletonDecoding
import Nock.NockVMROM.Thm54.TraceGen.Encode
import Mathlib.Data.ZMod.Basic

/-
  Nock/RedTeam/Batch1256Thm54HonestMemoryCollisionReceipt.lean

  Two distinct nouns of equal leaf count and Dyck
  word have equal fingerprints at a concrete seed, so `nounByFP` (first BFS match) can return a
  different noun than the record's.  This is a mechanism, not a counterexample at a generated
  program (unconfirmed, §6)
-/

set_option autoImplicit false

namespace Nock.RedTeam.Batch1256

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.TraceGen

/-- Two distinct nouns with the same leaf count and Dyck word whose fingerprints coincide at the
seed `z = 4` in `ZMod 7` (`2 + 3·4 = 4 + 6·4 = 0`). -/
theorem collision_ZMod7 :
    encC (4 : ZMod 7) (.cell (.atom 2) (.atom 3)) = encC (4 : ZMod 7) (.cell (.atom 4) (.atom 6)) ∧
      (Noun.cell (.atom 2) (.atom 3) : Noun) ≠ .cell (.atom 4) (.atom 6) := by
  refine ⟨?_, by decide⟩
  unfold encC
  congr 1

end Nock.RedTeam.Batch1256

#print axioms Nock.RedTeam.Batch1256.collision_ZMod7
