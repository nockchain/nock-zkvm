/-
  Nock/RedTeam/Batch971Thm54Round0WrapForestCover.lean

  **Lane `2b-round0-wrap`: every decoded `read_root` row's exponent is PAIRED in its
  decoded root tree** (the combinatorial half of `wrapJoin`'s padding step).

  R4's path validity (`Batch824.r4_path_valid_at`) speaks about exponents that are `Paired` in a
  decoded root tree `decodedMTreeOfEnvs … r`.  `wrapJoin` needs the padding of the certificate of
  EVERY `read_root` row's exponent, so it needs: every row lies in some root's reach set
  (`reach_cover`, from the BFS tiling `kroots + Sf fo M = M` and `BFSValidF`), and a `read_root`
  row in the reach set of `r` contributes a read of its exponent to the tree of `r`
  (`readCount_pos_of_reach`).  With `UniqueExponents` and R4's balanced counts that read is
  paired (`paired_of_read_row`).
-/
import Nock.NockVMROM.Thm54.DecodedLambdaEvent
import Nock.NockVMROM.Thm54.P8Core.Batch971Thm54Round0WrapForestCover

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch971

open Nock Nock.Walk Nock.MemoryTable
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.RedTeam.Batch575

section Forest

variable {F K : Type} [Field F] [Field K] [DecidableEq F] {M : ℕ}
variable (envsK : Fin M → Reified.Env K) (envsF : Fin M → Reified.Env F) (kroots : ℕ)

end Forest

end Nock.RedTeam.Batch971

#print axioms Nock.RedTeam.Batch971.reach_cover
#print axioms Nock.RedTeam.Batch971.readCount_pos_of_reach
#print axioms Nock.RedTeam.Batch971.paired_of_read_row
