import Nock.NockVMROM.Thm54.P8Core.PartAReHost
import Nock.NockVMROM.Thm54.P8Core.PartAReWalkChip
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1451Thm54PartAReHostReWalk.lean

  **R-T steps 3-4 — the re-host of the 309
  compute trace into the deployed layout and the memory re-walk at the timestamp coin.**

  * §A `satisfies303_of_309` (production, `PartAReHost`): acceptance of `Qc` by the un-hosted 309
    chip at a tuple gives acceptance of `reHost P t Qc` by the deployed 303 chip at that tuple.
    Positive control: L2's
    `retargeted_core_sensitive` — the instrument does see the four host-reading walk positions.
  * §B `memory_satisfies_at_alpha` (production, `PartAReWalkChip`): the landed memory chip at
    `forget12 c` (walk coin `α`) accepts `reWalk P Qm c`.
  * §C The re-walk touches only round-2 columns (`reWalk_round2`), so the twelve-coin event's
    round-local summands (L4's `consumedFailureEvent12_roundLocal`) do not see it.

  Scope: `repartitionedChronology` and the parallel package; nothing here states or implies
  `:966` soundness at `deployedChronology`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1451

open Nock Nock.Reified Nock.Walk
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.PartA12
open Nock.NockVMROM.Thm54.PartAStaged
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open scoped Polynomial

section Pkg

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- §A receipt. -/
theorem receipt_satisfies303_of_309 (t : OptimizedProductionChallengeTuple K F) (Qc : Fin 309 → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (Unhosted309.pkgComputeChipAt309 P t) Qc) :
    RAP.SatisfiesWithPreprocessing (P.computeChipAt t)
      (FamilyEnvCore.familyQc P.optimized t (PartAReHost.reHost P t Qc)) :=
  PartAReHost.satisfies303_of_309 P t Qc hsat

/-- §B receipt. -/
theorem receipt_memory_satisfies_at_alpha (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple12 K F) (hacc : AcceptanceAt309 P Qc Qm c)
    (hgood : c ∉ consumedFailureEvent309 P Qc Qm) :
    RAP.SatisfiesWithPreprocessing (P.memoryChipAt (forget12 c))
      (familyQm P (forget12 c) (PartAReWalk.reWalk P Qm c)) :=
  PartAReWalk.memory_satisfies_at_alpha P Qc Qm c hacc hgood

end Pkg

theorem receipt_insensitive_all_buckets : True := by
  have := PartAReHost.insensitive_all_buckets (F := ℚ)
  trivial

/-- §A positive control: the instrument sees exactly the four host-reading walk core positions. -/
theorem control_retargeted_sensitive :
    ((List.finRange 82).filter fun i =>
      (List.finRange 11).any fun s =>
        !Unhosted309.Insensitive (Unhosted309.curSel s) (Unhosted309.diffAt s)
          (Unhosted309.coreSrc i)).map Fin.val = [74, 75, 76, 77] :=
  Unhosted309.retargeted_core_sensitive

/-- §C the re-walk changes only round-2 columns. -/
theorem receipt_reWalk_round2 : ∀ j ∈ (List.range 182).filter (fun j => PartAReWalk.walkPhysB j),
    RepartitionedStaging.newMemoryColRound j = 2 :=
  PartAReWalk.reWalk_round2

end Nock.RedTeam.Batch1451

#print axioms Nock.RedTeam.Batch1451.receipt_satisfies303_of_309
#print axioms Nock.RedTeam.Batch1451.receipt_memory_satisfies_at_alpha
#print axioms Nock.NockVMROM.Thm54.PartAReHost.insensitive_all_buckets
#print axioms Nock.NockVMROM.Thm54.PartAReWalk.mixed_census
#print axioms Nock.NockVMROM.Thm54.PartAReWalk.forest_at_view
#print axioms Nock.NockVMROM.Thm54.PartAReWalk.forestVecBFT_isForestFullBFT
