import Nock.RedTeam.Batch1310Thm54RootResultNonVacuity
import Nock.NockVMROM.Thm54.P8Core.PlacementAEvOnly
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1330Thm54PlacementAEvOnly.lean

  * Component-map receipts (`P8Core/PlacementABridge.lean`): `comps1_10_pinned` here (the same ten
    props are slots 1–10 of the PINNED `good_components`, reducible `exact`), with
    `PlacementA.comps1_10_literal` (slots 1–10 are literal summands of Ev) and
    `PlacementA.comp0_zeroSeed_of_Ev` (slot 0's only consumed content, `nprSeed ≠ 0`, is Ev's).
  * `HoldsPremisesEvOnly`: `Batch1310.HoldsPremises` with the `c ∉ P.optimizedFailureEvent` conjunct
    DELETED; `holds_of_premises_evOnly` fires `PlacementA.holds_of_traces_evOnly` from it.
  * Non-vacuity: `nonvacuous_zmod_holds_evOnly` / `nonvacuous_zmod_semantic_evOnly`
    (`nockCompiles_zmod`'s binders verbatim, no open premise) at `Batch1310.nonvacuous_zmod_holds`'s
    generated package, honest tuple and honest traces; `hgoodEv` there is QP's
    `Batch1250.hgoodEv_of_pinned` route (inside `Batch1310.nonvacuous_generated_holds`), and
    `evOnly_of_premises` drops `hgood`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace Nock.RedTeam.Batch1330

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.Framework
open Nock.Framework.Thm54
open Module
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch906
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.RedTeam.Batch1061 (genPkg gen_honest_accepted)

noncomputable section

section Components

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])
  (c : OptimizedProductionChallengeTuple K F)

/-- **Slots 1–10 of the PINNED `good_components`** are the same ten props that
`PlacementA.comps1_10_literal` reads off Ev (reducible `exact`: no unfolding). -/
theorem comps1_10_pinned (h : c ∉ P.optimizedFailureEvent Qc Qm) :
      c ∉ P.famIOEventOf Qc Qm ∧
      alphaM c.1 ∉
        OptimizedHostileTimestamps.TimestampCollisionEvent (P.hostileRequests Qc).length ∧
      (c.2.1.1, c.2.2.2.interPole) ∉
        interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) ∧
      c.1 ∉ P.computeWalkRootEvent Qc ∧
      c.1 ∉ P.computeTilingEventOf Qc ∧
      c.1 ∉ P.memoryTilingEventOf Qm ∧
      c.1 ∉ P.computePrefixGammaEventOf Qc ∧
      c.1 ∉ P.memoryPrefixGammaEventOf Qm ∧
      c.1 ∉ P.memoryForestAlphaEventOf Qm ∧
      c ∉ P.decodedLambdaEventOf Qc Qm := by
  have g := P.optimizedFailureEvent_good_components Qc Qm c h
  with_reducible exact ⟨g.2.1, g.2.2.1, g.2.2.2.1, g.2.2.2.2.1, g.2.2.2.2.2.1, g.2.2.2.2.2.2.1,
    g.2.2.2.2.2.2.2.1, g.2.2.2.2.2.2.2.2.1, g.2.2.2.2.2.2.2.2.2.1, g.2.2.2.2.2.2.2.2.2.2.1⟩

end Components

section Holds

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

/-- **The premise list of `holds_of_traces_evOnly`**: `Batch1310.HoldsPremises` minus `hgood`. -/
def HoldsPremisesEvOnly {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X]) (Qm : Fin (P.memoryChipAt c).rap.w → F[X]) : Prop :=
  DeployedAcceptanceAt P c Qc Qm ∧
    c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm) ∧
    FormRAxisBound P.optimized.sampled P.optimized.basis ∧
    FormRBasis P.optimized.basis ∧
    FormRWidth F ∧
    StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c ∧
    (∃ (gfuel : ℕ) (G : NTree (GenComputeRow K)) (R : Noun),
      genComputeSkeleton (K := K) gfuel P.optimized.verifier.raw.claim.subject
        P.optimized.verifier.raw.claim.formula = .ok (G, R) ∧
      programLeafBound (airReorder G) ≤ P.optimized.Λ) ∧
    (∃ (fuel : ℕ) (r : Noun), FieldEmbedding.evalGBy (ringChar K) fuel
      P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula = some r) ∧
    FieldEmbedding.BoundedBy (ringChar K) P.optimized.verifier.raw.claim.subject ∧
    FieldEmbedding.BoundedBy (ringChar K) P.optimized.verifier.raw.claim.formula ∧
    (∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x)

/-- `HoldsPremisesEvOnly` at `P`'s honest tuple and honest traces. -/
def HoldsAtEvOnly {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) : Prop :=
  HoldsPremisesEvOnly P P.honestTuple (QcH P) (QmH P)

theorem evOnly_of_premises {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X]) (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (H : Batch1310.HoldsPremises P c Qc Qm) : HoldsPremisesEvOnly P c Qc Qm :=
  ⟨H.1, H.2.2⟩

/-- **The semantic `p8` from the Ev-only bundle** (`PlacementA.holds_of_traces_evOnly`). -/
theorem holds_of_premises_evOnly {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X]) (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (H : HoldsPremisesEvOnly P c Qc Qm) :
    ∃ fuel, FieldEmbedding.evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
        P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result ∧
      Nock.evalN fuel P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula =
        some P.optimized.verifier.raw.claim.result := by
  obtain ⟨hacc, hgoodEv, hax, hbasis, hwidth, h, ⟨gfuel, G, R, hgen, hΛG⟩, ⟨fuel, r, hG⟩,
    bs, bf, hF⟩ := H
  exact ⟨fuel, PlacementA.holds_of_traces_evOnly P c Qc Qm hacc hgoodEv hax hbasis hwidth h hgen hG
    bs bf hΛG hF⟩

end Holds

section Zmod

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional (ZMod p) K]

open Nock.NockVMROM.Thm54.TraceGen.GoodSeed in
/-- **Non-vacuity of the Ev-only semantic `p8`, §1 spelling, every program, NO open premise**:
`nockCompiles_zmod`'s binders verbatim; the package of `Batch1310.nonvacuous_zmod_holds`
(generated, honest tuple, honest traces; `hgoodEv` there is QP's `hgoodEv_of_pinned` route). -/
theorem nonvacuous_zmod_holds_evOnly
    (α lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy p fuel subject formula)
    (hs : FieldEmbedding.BoundedBy p subject)
    (hf : FieldEmbedding.BoundedBy p formula)
    (hΛp : (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))) < p)
    (hp : 25 ≤ p)
    (hp64 : p < 2 ^ 64)
    (hK : Module.finrank (ZMod p) K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ∣ p - 1)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3 < orderOf α ∧ programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf α)
    (hKszChar : compilerKszOf (0 : K) α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < p) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (ZMod p) K (orbitHeight (programFit α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ HoldsAtEvOnly package := by
  obtain ⟨P, h1, h2, h3, h4⟩ := Batch1310.nonvacuous_zmod_holds α lmb hrun hbound hs hf hΛp hp hp64
    hK hF hwin hKszChar
  exact ⟨P, h1, h2, h3, evOnly_of_premises P _ _ _ h4⟩

open Nock.NockVMROM.Thm54.TraceGen.GoodSeed in
/-- **The Ev-only semantic `p8` fired at the §1 package.** -/
theorem nonvacuous_zmod_semantic_evOnly
    (α lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy p fuel subject formula)
    (hs : FieldEmbedding.BoundedBy p subject)
    (hf : FieldEmbedding.BoundedBy p formula)
    (hΛp : (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))) < p)
    (hp : 25 ≤ p)
    (hp64 : p < 2 ^ 64)
    (hK : Module.finrank (ZMod p) K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ∣ p - 1)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3 < orderOf α ∧ programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf α)
    (hKszChar : compilerKszOf (0 : K) α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < p) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (ZMod p) K (orbitHeight (programFit α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ HoldsAtEvOnly package
        ∧ ∃ fuel', FieldEmbedding.evalGBy (ringChar K) fuel' package.optimized.verifier.raw.claim.subject
            package.optimized.verifier.raw.claim.formula = some package.optimized.verifier.raw.claim.result ∧
          Nock.evalN fuel' package.optimized.verifier.raw.claim.subject
            package.optimized.verifier.raw.claim.formula = some package.optimized.verifier.raw.claim.result := by
  obtain ⟨P, h1, h2, h3, h4⟩ := nonvacuous_zmod_holds_evOnly α lmb hrun hbound hs hf hΛp hp hp64 hK
    hF hwin hKszChar
  exact ⟨P, h1, h2, h3, h4, holds_of_premises_evOnly P _ _ _ h4⟩

end Zmod

end

end Nock.RedTeam.Batch1330

#print axioms Nock.NockVMROM.Thm54.PlacementA.comps1_10_literal
#print axioms Nock.NockVMROM.Thm54.PlacementA.comp0_zeroSeed_of_Ev
#print axioms Nock.NockVMROM.Thm54.PlacementA.good_components_of_Ev
#print axioms Nock.RedTeam.Batch1330.comps1_10_pinned
#print axioms Nock.NockVMROM.Thm54.PlacementA.bindsAtCoin_C2_combined_evOnly
#print axioms Nock.NockVMROM.Thm54.PlacementA.census_window_combined_evOnly
#print axioms Nock.NockVMROM.Thm54.PlacementA.not_mem_FailureUnion_combined_evOnly
#print axioms Nock.NockVMROM.Thm54.PlacementA.rootResult_bridge_evOnly
#print axioms Nock.NockVMROM.Thm54.PlacementA.holds_of_traces_evOnly
#print axioms Nock.NockVMROM.Thm54.PlacementA.holds_exists_evOnly
#print axioms Nock.NockVMROM.Thm54.PlacementA.tracesWalkHyps_of_acc_evOnly
#print axioms Nock.NockVMROM.Thm54.PlacementA.holds_of_acceptance_evOnly
#print axioms Nock.NockVMROM.Thm54.PlacementA.wrong_claim_rejected_evOnly
#print axioms Nock.RedTeam.Batch1330.holds_of_premises_evOnly
#print axioms Nock.RedTeam.Batch1330.nonvacuous_zmod_holds_evOnly
#print axioms Nock.RedTeam.Batch1330.nonvacuous_zmod_semantic_evOnly
