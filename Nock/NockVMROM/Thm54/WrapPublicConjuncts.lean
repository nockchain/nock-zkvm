/-
  Nock/NockVMROM/Thm54/WrapPublicConjuncts.lean

  `AcceptedContent.public_subject/formula/result` at the
  trace-built strategy.

  Family chips carry `enc(nprSeed c.1, claim)` in unread slots 42..68
  (`DeployedChipFamily.computePublicOfTuple`); the gate-read set stays
  the package map.
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
import Nock.NockVMROM.Thm54.SemanticStrategy
import Nock.NockVMROM.Thm54.TemplateRawJointSoundness
import Nock.GlobalCarryRecognizer
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.WrapPublicConjuncts

open scoped Polynomial
open Polynomial
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.SemanticStrategy
open Module

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- `specializedExec` is `specializedProblem` of the trace timestamp. -/
theorem specializedExec_eq_specializedProblem
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0) :
    (strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda =
      (specializedProblem (timestampOfTraces P Qc Qm c h)
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).exec :=
  rfl

/-- `public_subject` of `AcceptedContent` at the built strategy. -/
theorem specialized_public_subject
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hbinds : (strategyOfTraces P Qc Qm c h).BindsAtCoin c.1 c.2.2.2.lambda)
    (hz : nprSeed c.1 ≠ 0) :
    (((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computePubAt
      ⟨0, ((strategyOfTraces P Qc Qm c h).specializedCfg
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).compRows_pos⟩).s =
      GlobalCarryRecognizer.enc (nprSeed c.1)
        (strategyOfTraces P Qc Qm c h).verifier.raw.claim.subject := by
  have hb := hbinds hz
  have hroot := BindsAt.root_bindings hb
  have hexec := specializedExec_eq_specializedProblem P Qc Qm c h hz
  have hclaim := strategyOfTraces_claim P Qc Qm c h
  have hpub :=
    computePubAt_root_eq
      ((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda)
  rw [hpub, hexec, hclaim]
  exact hroot.1

/-- `public_formula` of `AcceptedContent` at the built strategy. -/
theorem specialized_public_formula
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hbinds : (strategyOfTraces P Qc Qm c h).BindsAtCoin c.1 c.2.2.2.lambda)
    (hz : nprSeed c.1 ≠ 0) :
    (((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computePubAt
      ⟨0, ((strategyOfTraces P Qc Qm c h).specializedCfg
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).compRows_pos⟩).f =
      GlobalCarryRecognizer.enc (nprSeed c.1)
        (strategyOfTraces P Qc Qm c h).verifier.raw.claim.formula := by
  have hb := hbinds hz
  have hroot := BindsAt.root_bindings hb
  have hexec := specializedExec_eq_specializedProblem P Qc Qm c h hz
  have hclaim := strategyOfTraces_claim P Qc Qm c h
  have hpub :=
    computePubAt_root_eq
      ((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda)
  rw [hpub, hexec, hclaim]
  exact hroot.2.1

/-- `public_result` of `AcceptedContent` at the built strategy. -/
theorem specialized_public_result
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hbinds : (strategyOfTraces P Qc Qm c h).BindsAtCoin c.1 c.2.2.2.lambda)
    (hz : nprSeed c.1 ≠ 0) :
    (((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computePubAt
      ⟨0, ((strategyOfTraces P Qc Qm c h).specializedCfg
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).compRows_pos⟩).e =
      GlobalCarryRecognizer.enc (nprSeed c.1)
        (strategyOfTraces P Qc Qm c h).verifier.raw.claim.result := by
  have hb := hbinds hz
  have hroot := BindsAt.root_bindings hb
  have hexec := specializedExec_eq_specializedProblem P Qc Qm c h hz
  have hclaim := strategyOfTraces_claim P Qc Qm c h
  have hpub :=
    computePubAt_root_eq
      ((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda)
  rw [hpub, hexec, hclaim]
  exact hroot.2.2

end

end Nock.NockVMROM.Thm54.WrapPublicConjuncts

#print axioms Nock.NockVMROM.Thm54.WrapPublicConjuncts.specialized_public_subject
#print axioms Nock.NockVMROM.Thm54.WrapPublicConjuncts.specialized_public_formula
#print axioms Nock.NockVMROM.Thm54.WrapPublicConjuncts.specialized_public_result
