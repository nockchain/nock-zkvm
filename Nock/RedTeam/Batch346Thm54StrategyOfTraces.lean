/-
  Nock/RedTeam/Batch346Thm54StrategyOfTraces.lean

  **Reconstruction receipts.**  Typed forest from `Qm`,
  `ComputeJoin` / `RecordHalfJoin` from the IO records, claim from the
  joined compute root.  Instrument: definitional identities and list
  lengths off `List.finRange` / `rebuildForest`.

  Lean: `` `StrategyOfTraces.lean::typedMemoryForest` ``,
  `` `::computeJoinOf` ``, `` `::recordHalfJoinOf` ``,
  `` `::publicClaimOf` ``, `` `::same_problem_claim` ``.
-/
import Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch346

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## Reconstruction lengths -/

theorem compute_rows_card
    (Qc : Fin P.computeChip.rap.w → F[X]) :
    (typedComputeRows P Qc).length = P.optimized.family.problem.cfg.compRows :=
  typedComputeRows_length P Qc

theorem memory_rows_card
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (typedMemoryRows P Qm).length = P.optimized.family.problem.cfg.memRows :=
  typedMemoryRows_length P Qm

theorem memory_forest_nonempty
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    typedMemoryForest P Qm ≠ [] :=
  typedMemoryForest_nonempty P Qm

theorem rebuild_zero_roots {α : Type} (fanout : α → ℕ) (rows : List α) :
    rebuildForest fanout 0 rows = [] :=
  rebuildForest_zero_roots fanout rows


theorem join_is_skeleton_compute
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (decodedSkeletonOf P Qc Qm).computeTree =
      (computeJoinOf P Qc Qm).computeTree :=
  decodedSkeleton_computeTree P Qc Qm

theorem claim_is_join_root
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (publicClaimOf P Qc Qm).subject =
      (computeJoinOf P Qc Qm).computeTree.label.subject ∧
    (publicClaimOf P Qc Qm).formula =
      (computeJoinOf P Qc Qm).computeTree.label.formula ∧
    (publicClaimOf P Qc Qm).result =
      (computeJoinOf P Qc Qm).computeTree.label.evaluation :=
  ⟨rfl, rfl, rfl⟩

/-- `RecordHalfJoin` is filled (possibly by `atom 0` when no matching
request exists).  The type is inhabited at every trace pair. -/
theorem recordHalfJoin_inhabited
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) :
    ∃ j : RecordHalfJoin, j = recordHalfJoinOf P Qc Qm :=
  ⟨recordHalfJoinOf P Qc Qm, rfl⟩

/-- Chip `Ksz` is the package public (reuse-map `hKp`). -/
theorem ksz_is_package_public (z : K) :
    (configTemplateOf P.objects.cfg z).Ksz = P.objects.cfg.Ksz :=
  hKp_of_package P z

theorem seed_overwrites_z (z : K) :
    (configTemplateOf P.objects.cfg z).challenges.z = z :=
  configTemplateOf_z P.objects.cfg z

end

end Nock.RedTeam.Batch346

#print axioms Nock.RedTeam.Batch346.compute_rows_card
#print axioms Nock.RedTeam.Batch346.memory_forest_nonempty
#print axioms Nock.RedTeam.Batch346.claim_is_join_root
#print axioms Nock.RedTeam.Batch346.recordHalfJoin_inhabited
#print axioms Nock.RedTeam.Batch346.ksz_is_package_public
