/-
  Nock/NockVMROM/Thm54/BelowDefs/P8Core/Batch458Thm54StrategyBindsStop.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/P8Core/Batch458Thm54StrategyBindsStop.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.ComputeWalkSeed

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch458

open scoped Polynomial
open Polynomial
open Nock
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.Framework
open MonolithicRAP
open OptimizedComputeHostileAccumulator
open Module

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
variable (c : OptimizedProductionChallengeTuple K F)

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] in
/-- Coordinates `1..9` of `labelVecOfPub = claimLabelVec` are the three `bindFP`s. -/
theorem bindFP_of_labelVec_eq (pub : Pub K) (z : K) (claim : P8PublicClaim)
    (h : labelVecOfPub pub = claimLabelVec z claim) :
    bindFP z claim.subject pub.s ∧ bindFP z claim.formula pub.f ∧
      bindFP z claim.result pub.e := by
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  have h6 := congrFun h 6
  have h7 := congrFun h 7
  have h8 := congrFun h 8
  have h9 := congrFun h 9
  simp only [labelVecOfPub, claimLabelVec] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  refine ⟨?_, ?_, ?_⟩
  · show pub.s = _
    cases hs : pub.s
    rw [hs] at h1 h2 h3
    cases he : GlobalCarryRecognizer.enc z claim.subject
    rw [he] at h1 h2 h3
    simp only at h1 h2 h3
    rw [h1, h2, h3]
  · show pub.f = _
    cases hs : pub.f
    rw [hs] at h4 h5 h6
    cases he : GlobalCarryRecognizer.enc z claim.formula
    rw [he] at h4 h5 h6
    simp only at h4 h5 h6
    rw [h4, h5, h6]
  · show pub.e = _
    cases hs : pub.e
    rw [hs] at h7 h8 h9
    cases he : GlobalCarryRecognizer.enc z claim.result
    rw [he] at h7 h8 h9
    simp only at h7 h8 h9
    rw [h7, h8, h9]

end

end Nock.RedTeam.Batch458
