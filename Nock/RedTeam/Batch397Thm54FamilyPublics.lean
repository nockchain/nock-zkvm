/-
  Nock/RedTeam/Batch397Thm54FamilyPublics.lean

  **Family-chip publics read `c`.**

  Measurement: gate-read public slots are `0..8` and `20..41`
  (`DeployedChipFamily.computePublicReadSet`) — walk α/seed, `requests`,
  first/last state one-hots.  None is `enc(z, claim.*)`.

  Claim-slot
  disjointness receipt retained.  Constant walk to `c` for the seed
  scaffold moved to `` `Batch402.computeSeedOfTuple` ``.
-/
import Lean
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.OptimizedComputeFinal
import Nock.NockVMROM.Thm54.JointSoundness
import Nock.RedTeam.Batch265Thm54DeadChallenge36
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch397

open Lean Meta Elab Command
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.RedTeam.Batch265
open Module

/-! ## Classify the gate-read set -/

/-- Seed-independent slots (gate-read): walk, requests, state one-hots. -/
def seedIndependentSlots : List ℕ := computePublicReadSet

def seedDependentSlots : List ℕ :=
  (List.range 27).map (· + claimPublicBase)

theorem seedIndependentSlots_length : seedIndependentSlots.length = 31 :=
  computePublicReadSet_length

theorem seedDependentSlots_length : seedDependentSlots.length = 27 := by
  simp [seedDependentSlots]

theorem claim_slots_disjoint_from_readSet :
    ∀ j ∈ seedDependentSlots, j ∉ computePublicReadSet := by
  intro j hj
  simp only [seedDependentSlots, List.mem_map, List.mem_range] at hj
  obtain ⟨t, ht, rfl⟩ := hj
  intro hrd
  simp only [computePublicReadSet, List.mem_append, List.mem_map, List.mem_range,
    claimPublicBase] at hrd
  rcases hrd with h | ⟨u, hu, heq⟩
  · omega
  · omega

/-- Endpoint equality checks read no challenge slots. -/
theorem finalEndpointEqualityChecks_chalSlots_empty :
    ∀ g ∈ (finalEndpointEqualityChecks (F := Nat)), chalSlots g = [] :=
  finalEndpointEqualityChecks_chalSlots

/-! ## 3 — tuple publics and honest read-set equality -/

theorem computePublicOfTuple_honest_on_readSet
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (claim : P8PublicClaim)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple K F)
    (j : ℕ) (hj : j ∈ computePublicReadSet) (hseed : ¬ j < 6) :
    computePublicOfTuple b claim pkgPub c j = pkgPub j :=
  computePublicOfTuple_eq_pkg_on_readSet b claim pkgPub c j hj hseed

theorem memoryPublicOfTuple_is_pkg
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (claim : P8PublicClaim) (kMem : ℕ)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple K F)
    (j : ℕ) (hj : ¬ (6 ≤ j ∧ j < 9)) :
    memoryPublicOfTuple b claim kMem pkgPub c j = pkgPub j :=
  memoryPublicOfTuple_eq_pkg b claim kMem pkgPub c j hj

theorem computePublicOfTuple_is_pkg
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (claim : P8PublicClaim)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple K F)
    (j : ℕ) (hseed : ¬ j < 6) :
    computePublicOfTuple b claim pkgPub c j = pkgPub j :=
  computePublicOfTuple_eq_pkg_off_seed b claim pkgPub c j hseed

end Nock.RedTeam.Batch397

#print axioms Nock.RedTeam.Batch397.seedIndependentSlots_length
#print axioms Nock.RedTeam.Batch397.claim_slots_disjoint_from_readSet
#print axioms Nock.RedTeam.Batch397.finalEndpointEqualityChecks_chalSlots_empty
#print axioms Nock.RedTeam.Batch397.computePublicOfTuple_is_pkg
