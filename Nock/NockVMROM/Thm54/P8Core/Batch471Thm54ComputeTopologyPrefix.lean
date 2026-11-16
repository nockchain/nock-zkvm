/-
  Nock/NockVMROM/Thm54/P8Core/Batch471Thm54ComputeTopologyPrefix.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch471Thm54ComputeTopologyPrefix`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch471Thm54ComputeTopologyPrefix.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch459Thm54ComputeTopologyStop
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.Batch471Thm54ComputeTopologyPrefix
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch471

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.Framework
open MonolithicRAP

section ClabC

variable {K : Type} [Field K]

end ClabC

section VecMap

variable {K : Type*} [Field K] {n m : ℕ}

end VecMap

section Generic

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

end Generic

section Deployed

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)

/-- `lblC` carries its own state in its `Pub` (`pubOfState`). -/
theorem lblC_state (i : ℕ) :
    (ExecOfTraces.lblC P Qc₀ c i).2.2.1.state = (ExecOfTraces.lblC P Qc₀ c i).1 := by
  unfold ExecOfTraces.lblC
  split <;> rfl

include hsat
include hax hbasis hwidth

omit hax hbasis hwidth in
theorem stAt_rowOf (i : ℕ) :
    Batch459.stAt P c (familyQc P c Qc₀) hsat (Batch459.rowOf P i) =
      (ExecOfTraces.lblC P Qc₀ c i).1 := by
  by_cases h : i - 1 < P.optimized.family.problem.cfg.compRows
  · simp only [Batch459.rowOf, ExecOfTraces.lblC, dif_pos h]
    rw [ExecOfTraces.lblCAt_eq_rowEnvAt]
    exact (Batch459.stAt_eq_computeStateOf P c (familyQc P c Qc₀) hsat _).symm
  · simp only [Batch459.rowOf, ExecOfTraces.lblC, dif_neg h]
    rw [ExecOfTraces.lblCAt_eq_rowEnvAt]
    exact (Batch459.stAt_eq_computeStateOf P c (familyQc P c Qc₀) hsat _).symm

omit hax hbasis hwidth in
theorem pubAt_rowOf (i : ℕ) :
    Batch459.pubAt P c (familyQc P c Qc₀) hsat (Batch459.rowOf P i) =
      (ExecOfTraces.lblC P Qc₀ c i).2.2.1 := by
  have hst := stAt_rowOf P c Qc₀ hsat i
  by_cases h : i - 1 < P.optimized.family.problem.cfg.compRows
  · simp only [Batch459.rowOf, dif_pos h] at hst ⊢
    simp only [Batch459.pubAt, ExecOfTraces.lblC, dif_pos h, ExecOfTraces.lblCAt]
    simp only [Batch459.rowOf, ExecOfTraces.lblC, dif_pos h, ExecOfTraces.lblCAt] at hst
    rw [hst]
  · simp only [Batch459.rowOf, dif_neg h] at hst ⊢
    simp only [Batch459.pubAt, ExecOfTraces.lblC, dif_neg h, ExecOfTraces.lblCAt]
    simp only [Batch459.rowOf, ExecOfTraces.lblC, dif_neg h, ExecOfTraces.lblCAt] at hst
    rw [hst]

omit hax hbasis hwidth in
/-- The deployed node vectors at the decoded labels. -/
noncomputable def Vd (i : ℕ) : Fin 10 → K := labelVecOfPub (ExecOfTraces.lblC P Qc₀ c i).2.2.1

omit hax hbasis hwidth in
/-- The deployed declared child vectors (hosted tags, Option A). -/
noncomputable def Cvd (i l : ℕ) : Fin 10 → K :=
  childVecN (ExecOfTraces.lblC P Qc₀ c i).2.2.1
    (Batch459.tagsAt P c (familyQc P c Qc₀) hsat (Batch459.rowOf P i)) (l - 1)

omit hax hbasis hwidth in
theorem foW_eq_foC_all :
    Batch459.foW P c (familyQc P c Qc₀) hsat = ExecOfTraces.foC P Qc₀ c := by
  funext i
  simp only [Batch459.foW, ExecOfTraces.foC]
  rw [stAt_rowOf P c Qc₀ hsat i]

/-- **`Batch459::deployed_walkSat` at `lblC` / `foC`, all indices.** -/
theorem deployed_walkSat_lblC :
    WalkSat (fun i => rlc (gamma c.1) (Vd P c Qc₀ i))
      (fun i l => rlc (gamma c.1) (Cvd P c Qc₀ hsat i l)) (ExecOfTraces.foC P Qc₀ c)
      (Batch459.lnW P c (familyQc P c Qc₀)) (Batch459.countW P c (familyQc P c Qc₀))
      (Batch459.accW P c (familyQc P c Qc₀)) (alphaC c.1)
      (seedOfClaim P.optimized.verifier.raw.claim c)
      (alphaC c.1) (rows P) := by
  have hw := Batch459.deployed_walkSat P c (familyQc P c Qc₀) hsat hax hbasis hwidth
  have hcur : Batch459.curW P c (familyQc P c Qc₀) hsat =
      fun i => rlc (gamma c.1) (Vd P c Qc₀ i) := by
    funext i; simp only [Batch459.curW, Vd]; rw [pubAt_rowOf P c Qc₀ hsat i]
  have hch : Batch459.chldW P c (familyQc P c Qc₀) hsat =
      fun i l => rlc (gamma c.1) (Cvd P c Qc₀ hsat i l) := by
    funext i l; simp only [Batch459.chldW, Cvd]; rw [pubAt_rowOf P c Qc₀ hsat i]
  rw [hcur, hch, foW_eq_foC_all P c Qc₀ hsat] at hw
  exact hw

end Deployed

end Nock.RedTeam.Batch471
