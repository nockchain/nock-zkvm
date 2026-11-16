/-
  Nock/RedTeam/Batch401Thm54ClaimUnbound.lean

  **Claim unbound at the deployed chip.**

  Endpoint
  equality checks read `20..41` (`` `OptimizedComputeFinal.lean::finalEndpointEqualityChecks` ``);
  typed final publics are `< 42`
  (`FinalTypedSupportFits`).

  Finding `claim_unbound_at_deployed_chip`: `DeployedAcceptanceAt` does
  not mention a claim.  Positive control: K-side `VerifierGates` rejects
  a claim whose fingerprint differs at the sampled seed.
-/
import Lean
import Nock.AIR
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.OptimizedComputeFinal
import Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.RawVerifier
import Nock.NockVMROM.Thm54.JointSoundness
import Nock.GlobalCarryRecognizer
import Nock.RedTeam.Batch397Thm54FamilyPublics
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch401

open Lean Meta Elab Command
open scoped Polynomial
open Polynomial
open Nock
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.RedTeam.Batch397
open Module

/-! ## Read-set receipts -/

/-- Re-export: claim slots are disjoint from the gate-read set. -/
theorem claim_slots_disjoint_from_readSet :
    ∀ j ∈ seedDependentSlots, j ∉ computePublicReadSet :=
  Batch397.claim_slots_disjoint_from_readSet

/-- Endpoint banks are `20..30` and `31..41` — inside the gate-read set,
    outside claim slots `42..68`. -/
theorem endpoint_public_banks_in_readSet :
    (∀ i < 11, 20 + i ∈ computePublicReadSet) ∧
      (∀ i < 11, 31 + i ∈ computePublicReadSet) := by
  constructor
  · intro i hi
    simp only [computePublicReadSet, List.mem_append, List.mem_map, List.mem_range]
    refine Or.inr ⟨i, by omega, ?_⟩
    omega
  · intro i hi
    simp only [computePublicReadSet, List.mem_append, List.mem_map, List.mem_range]
    refine Or.inr ⟨11 + i, by omega, ?_⟩
    omega

/-- Typed final AST forbids public indices `≥ 42`, so claim slots cannot
    appear in lowered final gates. -/
theorem finalTyped_publicVal_bound :
    FinalTypedSupportFits (.publicVal 41) ∧
      ¬ FinalTypedSupportFits (.publicVal 42) := by
  decide

/-! ## Finding: claim unbound at DeployedAcceptanceAt -/

/-- `DeployedAcceptanceAt` has no claim argument.  Changing the public claim
    cannot appear in its type; acceptance at fixed `(Qc, Qm, c)` is claim-blind. -/
theorem claim_unbound_at_deployed_chip
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (claim claim' : P8PublicClaim)
    (_hne : claim ≠ claim')
    (h : DeployedAcceptanceAt P c Qc Qm) :
    DeployedAcceptanceAt P c Qc Qm :=
  h

/-- Constant walk: the *type* of `DeployedAcceptanceAt` reaches no claim name. -/
def DEPLOYED_ACC : Name :=
  ``Nock.NockVMROM.Thm54.DeployedAcceptanceAt

def P8_CLAIM : Name :=
  ``Nock.NockVMROM.Thm54.P8PublicClaim

elab "#batch401_acceptance_claim_blind" : command => do
  let env ← getEnv
  let some ci := env.find? DEPLOYED_ACC
    | throwError "DeployedAcceptanceAt missing"
  let tyConsts := ci.type.getUsedConstants
  if tyConsts.contains P8_CLAIM then
    throwError "DeployedAcceptanceAt type reaches P8PublicClaim"
  logInfo m!"Batch401: DeployedAcceptanceAt type is claim-blind \
    ({tyConsts.size} constants)"

#batch401_acceptance_claim_blind

/-! ## K-side positive control -/

private theorem verifierGates_subject_eq
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (R : RawPlusIOSegmentedFamily F K) (M : RawMessage R (ringChar K))
    (claim : P8PublicClaim) (ω : JointCoins K)
    (h : M.VerifierGates claim ω) :
    (R.exec.computePubAt ⟨0, R.cfg.compRows_pos⟩).s =
      GlobalCarryRecognizer.enc (nprSeed ω) claim.subject := by
  unfold RawMessage.VerifierGates at h
  exact h.2.2.2.2.2.2.2.1

private theorem verifierGates_formula_eq
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (R : RawPlusIOSegmentedFamily F K) (M : RawMessage R (ringChar K))
    (claim : P8PublicClaim) (ω : JointCoins K)
    (h : M.VerifierGates claim ω) :
    (R.exec.computePubAt ⟨0, R.cfg.compRows_pos⟩).f =
      GlobalCarryRecognizer.enc (nprSeed ω) claim.formula := by
  unfold RawMessage.VerifierGates at h
  exact h.2.2.2.2.2.2.2.2.1

private theorem verifierGates_result_eq
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (R : RawPlusIOSegmentedFamily F K) (M : RawMessage R (ringChar K))
    (claim : P8PublicClaim) (ω : JointCoins K)
    (h : M.VerifierGates claim ω) :
    (R.exec.computePubAt ⟨0, R.cfg.compRows_pos⟩).e =
      GlobalCarryRecognizer.enc (nprSeed ω) claim.result := by
  unfold RawMessage.VerifierGates at h
  exact h.2.2.2.2.2.2.2.2.2.1

theorem verifierGates_rejects_mismatched_subject
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (R : RawPlusIOSegmentedFamily F K) (M : RawMessage R (ringChar K))
    (claim claim' : P8PublicClaim) (ω : JointCoins K)
    (h : M.VerifierGates claim ω)
    (hne :
      GlobalCarryRecognizer.enc (nprSeed ω) claim.subject ≠
        GlobalCarryRecognizer.enc (nprSeed ω) claim'.subject) :
    ¬ M.VerifierGates claim' ω := by
  intro h'
  have hs := verifierGates_subject_eq R M claim ω h
  have hs' := verifierGates_subject_eq R M claim' ω h'
  exact hne (hs.symm.trans hs')

theorem verifierGates_rejects_mismatched_formula
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (R : RawPlusIOSegmentedFamily F K) (M : RawMessage R (ringChar K))
    (claim claim' : P8PublicClaim) (ω : JointCoins K)
    (h : M.VerifierGates claim ω)
    (hne :
      GlobalCarryRecognizer.enc (nprSeed ω) claim.formula ≠
        GlobalCarryRecognizer.enc (nprSeed ω) claim'.formula) :
    ¬ M.VerifierGates claim' ω := by
  intro h'
  have hf := verifierGates_formula_eq R M claim ω h
  have hf' := verifierGates_formula_eq R M claim' ω h'
  exact hne (hf.symm.trans hf')

theorem verifierGates_rejects_mismatched_result
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (R : RawPlusIOSegmentedFamily F K) (M : RawMessage R (ringChar K))
    (claim claim' : P8PublicClaim) (ω : JointCoins K)
    (h : M.VerifierGates claim ω)
    (hne :
      GlobalCarryRecognizer.enc (nprSeed ω) claim.result ≠
        GlobalCarryRecognizer.enc (nprSeed ω) claim'.result) :
    ¬ M.VerifierGates claim' ω := by
  intro h'
  have he := verifierGates_result_eq R M claim ω h
  have he' := verifierGates_result_eq R M claim' ω h'
  exact hne (he.symm.trans he')

end Nock.RedTeam.Batch401

#print axioms Nock.RedTeam.Batch401.claim_slots_disjoint_from_readSet
#print axioms Nock.RedTeam.Batch401.claim_unbound_at_deployed_chip
#print axioms Nock.RedTeam.Batch401.verifierGates_rejects_mismatched_subject
#print axioms Nock.RedTeam.Batch401.finalTyped_publicVal_bound
