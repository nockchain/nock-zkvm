/-
  Nock/NockVMROM/Thm54/P8Core/Batch1142Thm54C2CombinedCertAxes0.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch1142Thm54C2CombinedCertAxes0`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch1142Thm54C2CombinedCertAxes0.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.ComputedWindow
import Nock.NockVMROM.Thm54.P8Core.FamilyMemoryRows
import Nock.NockVMROM.Thm54.P8Core.OptimizedFailureEventEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace Nock.RedTeam.Batch1142

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.ComputedWindow
open Nock.NockVMROM.Thm54.TraceGen
open Nock.GlobalCarryRecognizer
open Nock.FieldEmbedding
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
set_option quotPrecheck false
/-- The C2 join on the family traces at `c`, rooted at the package claim. -/
local notation "JT" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) (svF P c Qm) (axF P c Qc)
  (treeS P c Qc).size (treeS P c Qc)
  P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula

omit [Fintype F] [DecidableEq F] [CharP K (ringChar K)] [FiniteDimensional F K] in
theorem hΛ1_of_hgen {gfuel : ℕ} {S Fm R : Noun} {G : NTree (GenComputeRow K)} {Λ : ℕ}
    (hgen : genComputeSkeleton (K := K) gfuel S Fm = .ok (G, R))
    (hΛG : programLeafBound (airReorder G) ≤ Λ) : 1 ≤ Λ :=
  (S.one_le_leaves.trans (honestCall_inputs_le (honestCall_root hgen)).1).trans hΛG

/-- `α ≠ 0` is the last component of the 2b-ii event. -/
theorem hα0_of_goodEv (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm)) :
    alphaM c.1 ≠ 0 :=
  (optimizedFailureEventEv_good_components P _ _ c hgoodEv).2.2.2.2.2.2.2.2.2.2.2.2.2

end Nock.RedTeam.Batch1142
