/-
  Nock/RedTeam/Batch445Thm54KsideVerField.lean

  **`Pub.ver` field receipt.**

  Receipt that `MemoryTable.Pub` carries `ver : Bool` (honest default
  `decide (st = read_root)`), `Vmem` is `verBool ∧ eqBlk ∧ interV`,
  and `decodeMemPub` reads role 39 into `ver`.
-/
import Nock.MemoryTable
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch445

open scoped Polynomial
open Polynomial
open Nock
open Nock.MemoryTable
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage

#check Pub.ver
#check verBool
#check Vmem
#check verBool_holds
#check decodeMemPub

/-- `Vmem` carries booleanity of `ver` as its first conjunct. -/
theorem vmem_carries_verBool {K : Type*} [Field K]
    (inp : Inputs K) (p : Pub K) :
    Vmem inp p → verBool (K := K) p :=
  And.left

/-- Honest structure default: `ver` is the `read_root` indicator. -/
theorem honest_ver_default {K : Type*} (st : MState)
    (pt lc rc : Cell K) (lcSt rcSt : MState) (mem : ComputeTable.MemRec K) (ipre icur : K) :
    ({ st := st, pt := pt, lc := lc, rc := rc, lcSt := lcSt, rcSt := rcSt,
       mem := mem, ipre := ipre, icur := icur } : Pub K).ver =
      decide (st = MState.read_root) :=
  rfl

/-- `verBool` holds for every `Pub` (`ver : Bool`). -/
theorem verBool_always {K : Type*} [Field K] (p : Pub K) :
    verBool (K := K) p :=
  verBool_holds p

/-- Decode reads role 39: `ver = decide (trace 39 = 1)`. -/
theorem decodeMemPub_ver_from_role39
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (decodeMemPub P Qm c i).ver =
      decide ((memorySourceEnvAt P c Qm i).trace 39 = 1) :=
  rfl

end Nock.RedTeam.Batch445

#print axioms Nock.RedTeam.Batch445.vmem_carries_verBool
#print axioms Nock.RedTeam.Batch445.honest_ver_default
#print axioms Nock.RedTeam.Batch445.verBool_always
#print axioms Nock.RedTeam.Batch445.decodeMemPub_ver_from_role39
