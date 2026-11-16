/-
  Nock/RedTeam/Batch1024Thm54C2BindsAtCoin.lean

  * §A — the compute template's specialization transports `BindComputeRow` / `ComputeTreeBinds`:
    `ComputeRowTemplate.specialize` at `wrapComputeLabel` changes only `inp.α`, `ln_prev`, `ln` and
    the record timestamps, and writes `MemRec.zero` on exactly the inactive record slots
    (`specializeMemRecScaled`), so a skeleton row bound to a decoded row is bound to its
    specialization (`bindComputeRow_specialize`), and tree-wise through `mapNTree`
    (`computeTreeBinds_mapNTree`).  No `V_comp` is needed for this.
  * §C — **the memory re-check**: `decodedSkeletonC2`'s memory forest and the C2 strategy's
    specialized execution are `decodedSkeletonR0A`'s and `strategyOfTracesR0A`'s (`rfl`), so
    `Batch1011.memoryForestBinds_R0A` applies verbatim: `hservedChild` / `hservedRoot` and every
    other memory premise discharge unchanged (C2 touches no `nounByFP` half of the memory decoder).
  * §E — the claim facts: the C2 strategy's verifier claim is the C2 skeleton's public claim, whose
    subject and formula are the package claim's; the a-bearing strategy's is `publicClaimOf` (the
    decoded self-read root).
-/
import Nock.RedTeam.Batch1021Thm54C2JoinAssembly
import Nock.RedTeam.Batch1011Thm54AxisViewBindsAtCoin
import Nock.RedTeam.Batch1013Thm54AxisViewTransfer
import Nock.NockVMROM.Thm54.P8Core.Batch1024Thm54C2BindsAtCoin
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1024

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch1021

noncomputable section

/-! ## §A  Specialization transports the compute binding -/

section Transport

variable {K : Type} [Field K] [DecidableEq K]

/-- The specialized row's state is the template's `stamp.state`, i.e. the label's state. -/
theorem specialize_wrap_fst (α : K) (row : State × DTcomp K) :
    ((StrategyOfTracesLift.wrapComputeLabel row).specialize α).1 = row.1 := rfl

end Transport

/-! ## §B–§E  At the family traces -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)

theorem hcomp_C2_of_ready (hz : nprSeed c.1 ≠ 0) {q : ℕ}
    (hR : C2JoinReady (svF P c Qm) (axF P c Qc) (nprSeed c.1) q (treeS P c Qc)
      P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula) :
    ComputeTreeBinds (nprSeed c.1) (TC P c Qc Qm h).skeleton.computeTree
      ((TC P c Qc Qm h).specializedExec (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeTree := by
  rw [specialized_computeTree_C2]
  exact computeTreeBinds_mapNTree _ (fun s row hb => bindComputeRow_specialize (alphaM c.1) s row hb)
    _ _ _ (Nat.le_refl _)
    (computeTreeBinds_C2_of_ready P.optimized (honestQc P c Qc) (honestQm P c Qm) c h hz hR)

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)

include hacc hgood hax hbasis hwidth

/-- The seed
conjunct is definitional (`specializedCfg_C2_z`), the memory conjunct is `memoryForestBinds_C2`,
the compute conjunct `hcomp_C2_of_ready`, the BFS row conjuncts are derived
(`BindsAt.ofTreeBindings`). -/
theorem bindsAtCoin_C2_of_ready
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x)
    (hα0 : alphaM c.1 ≠ 0) {q : ℕ}
    (hR : C2JoinReady (svF P c Qm) (axF P c Qc) (nprSeed c.1) q (treeS P c Qc)
      P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula) :
    (TC P c Qc Qm h).BindsAtCoin c.1 c.2.2.2.lambda := by
  intro hz
  exact BindsAt.ofTreeBindings rfl (hcomp_C2_of_ready P c Qc Qm h hz hR)
    (memoryForestBinds_C2 P c Qc Qm h hacc hgood hax hbasis hwidth hz hF hα0)

omit hacc hgood hax hbasis hwidth in
/-! ## §E  The claim facts (what does and does not transfer from R0A) -/

/-- The C2 verifier's claim subject and formula are the package claim's. -/
theorem claim_C2_subject :
    (TC P c Qc Qm h).verifier.raw.claim.subject = P.optimized.verifier.raw.claim.subject :=
  decodedSkeletonC2_publicClaim_subject _ _ _ _ _

omit hacc hgood hax hbasis hwidth in
theorem claim_C2_formula :
    (TC P c Qc Qm h).verifier.raw.claim.formula = P.optimized.verifier.raw.claim.formula :=
  decodedSkeletonC2_publicClaim_formula _ _ _ _ _

omit hacc hgood hax hbasis hwidth in
/-- The a-bearing strategy's claim is the decoded self-read root (`publicClaimOf`): what
`Batch1013.accepts_R0A_iff` transfers by `Iff.rfl` is NOT the C2 strategy's `Accepts`. -/
theorem claim_R0A_is_publicClaimOf :
    (Batch1013.TA P c Qc Qm h).verifier.raw.claim =
      publicClaimOf P.optimized (honestQc P c Qc) (honestQm P c Qm) := rfl

omit hacc hgood hax hbasis hwidth in
/-- What does transfer: the specialized execution and configuration (`rfl`). -/
theorem specializedExec_C2_transfer (z : K) (hz : z ≠ 0) (α lmb : K) :
    (TC P c Qc Qm h).specializedExec z hz α lmb =
      (Batch1013.TA P c Qc Qm h).specializedExec z hz α lmb := rfl

end

end Nock.RedTeam.Batch1024

#print axioms Nock.RedTeam.Batch1024.bindComputeRow_specialize
#print axioms Nock.RedTeam.Batch1024.computeTreeBinds_mapNTree
#print axioms Nock.RedTeam.Batch1024.hcomp_C2_of_ready
#print axioms Nock.RedTeam.Batch1024.memoryForestBinds_C2
#print axioms Nock.RedTeam.Batch1024.bindsAtCoin_C2_of_ready
#print axioms Nock.RedTeam.Batch1024.claim_C2_subject
