/-
  Nock/RedTeam/Batch824Thm54R4Bridge.lean

  Additive; nothing consumes this.

  **Statement (`r4_bridge_at`).**

  2. **the roots** — every decoded root `r ∈ 1..kMem` has `decodedRootPoly … r = 0`
     (root accumulators are `0` by `rootMask`; the envelope is `biv` below `3N + 3`; outside the
     decoded event the guard fails).

  Not at every `(Qc, Qm)`.
-/
import Nock.RedTeam.Batch822Thm54R4BridgeMemory
import Nock.RedTeam.Batch823Thm54R4BridgeCompute
import Nock.RedTeam.Batch521Thm54ReadRootImpliesVer
import Nock.NockVMROM.Thm54.P8Core.Batch824Thm54R4Bridge
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch824

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.FormRBridge
open Nock.RedTeam.Batch575

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

/-! ## A. Package-level facts -/

/-! ## B. Memory row facts at the family chip -/

section Rows

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
include hacc

end Rows

/-! ## C. The IO / certificate facts of the telescope -/

section IO

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hio : FamilyIOGood P c Qc Qm)
  (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K)
include hacc hgood hio hrb

end IO

/-! ## D. Assembly -/

section Assembly

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hio : FamilyIOGood P c Qc Qm)
  (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K)
  (hb : Batch823.CertBitsBoolean P c Qc)
  (h1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)
include hacc hgood hio hrb hb h1

omit hb in
/-- **R4 at the current gates**: `CertBitsBoolean` discharged by `Batch823.certBitsBoolean_of_sat`
(the one place that reads `booleanGates`' current body). -/
theorem r4_bridge_at_current :
    (∀ i (h : 1 ≤ i ∧ i ≤ P.optimized.family.problem.cfg.memRows),
      biv (alphaM c.1) c.2.2.2.lambda
          (formRCounts (FormRAxisEvent.formRN K) (decodedShift (envsCR P c Qc))
            (decodedBits (envsCR P c Qc))
            (decodedMTreeOfEnvs (envsKR P c Qm) (envsFR P c Qm)
              P.optimized.family.problem.cfg.kMem i)) =
        (Batch822.pubR P c (honestQm P c Qm) i).pt.counts) ∧
    (∀ r ∈ Finset.Icc 1 P.optimized.family.problem.cfg.kMem,
      decodedRootPoly (envsCR P c Qc) (envsKR P c Qm) (envsFR P c Qm)
        P.optimized.family.problem.cfg.kMem r = 0) := by
  have hb := Batch823.certBitsBoolean_of_sat P c Qc hacc.compute_satisfies
  have h := r4_bridge_at P c Qc Qm hacc hgood hio hrb hb h1
  exact ⟨fun i hi => (h.1 i hi).2, h.2⟩

end Assembly

end

end Nock.RedTeam.Batch824

#print axioms Nock.RedTeam.Batch824.r4_bridge_at
#print axioms Nock.RedTeam.Batch824.r4_path_valid_at
#print axioms Nock.RedTeam.Batch824.r4_bridge_at_current
