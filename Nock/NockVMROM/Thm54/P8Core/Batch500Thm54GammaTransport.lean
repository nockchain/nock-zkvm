/-
  Nock/NockVMROM/Thm54/P8Core/Batch500Thm54GammaTransport.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch500Thm54GammaTransport`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch500Thm54GammaTransport.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch490Thm54TopologyAssembly
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Nock.RedTeam.Batch500

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.MemoryWalkLabel
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.Framework
open Nock.Framework.Reify
open MonolithicRAP
open Nock.RedTeam.Batch465
open Nock.RedTeam.Batch471
open Nock.RedTeam.Batch489
open Nock.RedTeam.Batch490
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem curValsV_congr_on {n : ℕ} {V V' : ℕ → Fin n → K} {h : ℕ}
    (hV : ∀ i, 1 ≤ i → i ≤ h → V i = V' i) :
    curValsV V h = curValsV V' h := by
  refine List.map_congr_left ?_
  intro i hi
  have hi' : i < h := List.mem_range.mp hi
  exact hV (i + 1) (Nat.succ_le_succ (Nat.zero_le _)) (Nat.succ_le_of_lt hi')

theorem blkValsV_congr_on {n : ℕ} {Cv Cv' : ℕ → ℕ → Fin n → K}
    {fo fo' : ℕ → ℕ} {i : ℕ}
    (hfo : fo i = fo' i)
    (hCv : ∀ l, 1 ≤ l → l ≤ fo i → Cv i l = Cv' i l) :
    blkValsV Cv fo i = blkValsV Cv' fo' i := by
  simp only [blkValsV, hfo]
  refine List.map_congr_left ?_
  intro l hl
  have hl' : l < fo' i := List.mem_range.mp hl
  exact hCv (l + 1) (Nat.succ_le_succ (Nat.zero_le _)) (by
    rw [hfo]; exact Nat.succ_le_of_lt hl')

theorem flatBlksV_congr_on {n : ℕ} {Cv Cv' : ℕ → ℕ → Fin n → K}
    {fo fo' : ℕ → ℕ} {k : ℕ}
    (hfo : ∀ i, 1 ≤ i → i ≤ k → fo i = fo' i)
    (hCv : ∀ i l, 1 ≤ i → i ≤ k → Cv i l = Cv' i l) :
    flatBlksV Cv fo k = flatBlksV Cv' fo' k := by
  induction k with
  | zero => simp [flatBlksV]
  | succ k ih =>
    rw [flatBlksV_succ, flatBlksV_succ, ih]
    · congr 1
      refine blkValsV_congr_on (hfo (k + 1) (by omega) (by omega)) ?_
      intro l h1 h2
      exact hCv (k + 1) l (by omega) (by omega)
    · intro i h1 h2; exact hfo i h1 (le_trans h2 (Nat.le_succ _))
    · intro i l h1 h2; exact hCv i l h1 (le_trans h2 (Nat.le_succ _))

theorem prefixBadGammas_congr_on {n : ℕ}
    {V V' : ℕ → Fin n → K} {Cv Cv' : ℕ → ℕ → Fin n → K}
    {fo fo' : ℕ → ℕ} {h : ℕ}
    (hV : ∀ i, 1 ≤ i → i ≤ h → V i = V' i)
    (hCv : ∀ i l, 1 ≤ i → i ≤ h → Cv i l = Cv' i l)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = fo' i) :
    prefixBadGammas V Cv fo h = prefixBadGammas V' Cv' fo' h := by
  by_cases hz : h = 0
  · subst hz
    simp [prefixBadGammas, curValsV]
  · have hpos : 1 ≤ h := by omega
    unfold prefixBadGammas
    congr 1
    · exact curValsV_congr_on hV
    · have hlists : V 1 :: flatBlksV Cv fo h = V' 1 :: flatBlksV Cv' fo' h := by
        congr 1
        · exact hV 1 le_rfl hpos
        · exact flatBlksV_congr_on hfo hCv
      rw [hlists]

section DeployedVectors

variable {F : Type} [Field F] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
include hsatC

/-- Committed node vector at walk index `i ∈ 1..N` is `Vd i`. -/
theorem Vd_eq_committed (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ rows P) :
    committedComputeV (P.computeSourceEnv Qc₀) i = Vd P c Qc₀ i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < rows P := by omega
  have hpos : 1 ≤ k + 1 ∧ k < rows P := ⟨by omega, hk⟩
  have hpub := pubAt_rowOf P c Qc₀ hsatC (k + 1)
  rw [Batch459.rowOf_succ P k hk] at hpub
  simp only [committedComputeV, Vd, dif_pos hpos, Nat.add_sub_cancel]
  rw [rowLabelVec_family P c Qc₀ hsatC ⟨k, hk⟩, hpub]

/-- Committed child vector at walk index `i ∈ 1..N` is `Cvd i l`. -/
theorem Cvd_eq_committed (i l : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ rows P) :
    committedComputeCv (P.computeSourceEnv Qc₀) i l = Cvd P c Qc₀ hsatC i l := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < rows P := by omega
  have hpos : 1 ≤ k + 1 ∧ k < rows P := ⟨by omega, hk⟩
  have hpub := pubAt_rowOf P c Qc₀ hsatC (k + 1)
  rw [Batch459.rowOf_succ P k hk] at hpub
  simp only [committedComputeCv, Cvd, dif_pos hpos, Nat.add_sub_cancel]
  rw [rowChildVec_family P c Qc₀ hsatC ⟨k, hk⟩]
  simp only [Batch459.rowOf_succ P k hk, hpub]

/-- Committed fanout at walk index `i ∈ 1..N` is `foC i`. -/
theorem foC_eq_committed (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ rows P) :
    foOf (P.computeSourceEnv Qc₀) i = foC P Qc₀ c i := by
  have hfoW := foOf_eq_foW P c Qc₀ hsatC i hi1 hih
  have hAll := foW_eq_foC_all P c Qc₀ hsatC
  rw [hfoW, hAll]

/-- The priced event's `prefixBadGammas` is the topology statement's. -/
theorem prefixBadGammas_Vd_eq_committed :
    prefixBadGammas (committedComputeV (P.computeSourceEnv Qc₀))
        (committedComputeCv (P.computeSourceEnv Qc₀))
        (foOf (P.computeSourceEnv Qc₀)) (rows P) =
      prefixBadGammas (Vd P c Qc₀) (Cvd P c Qc₀ hsatC)
        (foC P Qc₀ c) (rows P) :=
  prefixBadGammas_congr_on
    (fun i h1 h2 => Vd_eq_committed P c Qc₀ hsatC i h1 h2)
    (fun i _l h1 h2 => Cvd_eq_committed P c Qc₀ hsatC i _l h1 h2)
    (fun i h1 h2 => foC_eq_committed P c Qc₀ hsatC i h1 h2)

end DeployedVectors

section PricedGamma

variable {F : Type} [Field F] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hz : nprSeed c.1 ≠ 0)
  (hchar : MemStateTagChar F)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hsatC

/-- Priced `computePrefixGammaEventOf` is `prefixBadGammas` of `Vd`/`Cvd`/`foC`. -/
theorem hγ_of_priced
    (hγC : c.1 ∉ P.computePrefixGammaEventOf Qc₀) :
    gamma c.1 ∉ prefixBadGammas (Vd P c Qc₀) (Cvd P c Qc₀ hsatC)
      (foC P Qc₀ c) (rows P) := by
  have hmem : gamma c.1 ∉
      prefixBadGammas (committedComputeV (P.computeSourceEnv Qc₀))
        (committedComputeCv (P.computeSourceEnv Qc₀))
        (foOf (P.computeSourceEnv Qc₀)) (rows P) :=
    (computePrefixGammaEventOf_eq_prefix (P.computeSourceEnv Qc₀) c.1).mpr.mt hγC
  rwa [prefixBadGammas_Vd_eq_committed P c Qc₀ hsatC] at hmem

include hsatM

/-- `c ∉ optimizedFailureEvent` discharges topology `hγ`. -/
theorem hγ_of_good
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀) :
    gamma c.1 ∉ prefixBadGammas (Vd P c Qc₀) (Cvd P c Qc₀ hsatC)
      (foC P Qc₀ c) (rows P) :=
  hγ_of_priced P c Qc₀ hsatC
    (P.optimizedFailureEvent_good_components Qc₀ Qm₀ c hgood).2.2.2.2.2.2.2.1

include hz hchar
include hax hbasis hwidth

/-- **`ComputeExactTopology` of `execOfTraces` from chips + priced events.**
    No extra `hγ`. -/
theorem computeTopology_of_deployed_of_good
    (hacc : DeployedAcceptanceAt P c (familyQc P c Qc₀) (familyQm P c Qm₀))
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀) :
    ComputeExactTopology (execOfTraces P Qc₀ Qm₀ c
      (tracesWalkHyps_of_deployed P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth hacc hgood)) :=
  computeTopology_of_deployed P c Qc₀ Qm₀ hsatC hsatM hz hchar hax hbasis hwidth hacc hgood
    (hγ_of_good P c Qc₀ Qm₀ hsatC hsatM hgood)

end PricedGamma

end Nock.RedTeam.Batch500
