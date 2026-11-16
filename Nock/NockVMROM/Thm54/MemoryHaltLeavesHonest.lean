/-
  Nock/NockVMROM/Thm54/MemoryHaltLeavesHonest.lean

  Every constructed package's memory `halt` rows carry
  a leaf in the image of `𝔽`: the package's skeleton commitment binds every executed memory row
  (`scan` + `rowFrame` + `shapeMatch` give `BindMemoryRow`, `RawSemanticAssembly
.forall₂_bindMemoryRow_of_scan`), a skeleton `halt` row's parent is an atom
  (`MemoryRowSkeleton.haltParent`), and `enc z (atom k)` has leaf `(k : K)`.  The honest specialization (`honest_specialization`) is the package's own
  execution, so `HaltLeavesBase` holds for every package's sampled assignment
  (`package_haltLeavesBase`) — the completeness side condition of the `halt`-row atom gate is a
  theorem, not a hypothesis, wherever a package is in hand.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.MemoryHaltRowsBase
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.RawSemanticAssembly
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The package's own execution has base-field `halt` leaves. -/
theorem objects_haltRowsBase : HaltRowsBase (F := F) P.objects.exec := by
  have hspec := P.honest_specialization
  have hrows := haltRowsBase_of_checks (F := F)
    (P.optimized.shapeMatch P.honestSeed P.honestSeed_ne P.honestAlpha
      P.optimized.objects.cfg.challenges.lam)
    (P.optimized.rowFrame P.honestSeed P.honestSeed_ne P.honestAlpha
      P.optimized.objects.cfg.challenges.lam)
    (P.optimized.scan P.honestSeed P.honestSeed_ne P.honestAlpha
      P.optimized.objects.cfg.challenges.lam)
  rw [hspec] at hrows
  exact hrows

/-- **Every package's memory `halt` rows carry base-field leaves** (the completeness side
condition of the `halt`-row atom gate). -/
theorem package_haltLeavesBase : HaltLeavesBase P.optimized.sampled :=
  haltLeavesBase_of_rows _
    (haltRowsBase_heq P.optimized.family_cfg P.optimized.family_exec (objects_haltRowsBase P))

end

end Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest

#print axioms Nock.NockVMROM.Thm54.MemoryHaltLeavesHonest.package_haltLeavesBase
