/-
  Nock/NockVMROM/Thm54/BelowDefs/TraceGen/GenFormRAxisLambda.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/TraceGen/GenFormRAxisLambda.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericAxisRange

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda

open Classical
open Nock Nock.Walk
open Module
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeCodec
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

section Discharge

theorem renderNode_row_s0 (z α : K) (g : GenComputeRow K) (h : g.skel.state = .s0) :
    (renderNode z α g).row.2.2.1.state = .s0 ∧
      (renderNode z α g).row.2.2.2.f_t = encC z (formulaTail g.skel.formula) := by
  unfold renderNode
  simp only [h]
  exact ⟨rfl, rfl⟩

theorem renderNode_row_s9 (z α : K) (g : GenComputeRow K) (h : g.skel.state = .s9) :
    (renderNode z α g).row.2.2.1.state = .s9 ∧
      (renderNode z α g).row.2.2.2.f_th =
        encC z (formulaHead (formulaTail g.skel.formula)) := by
  unfold renderNode
  simp only [h]
  exact ⟨rfl, rfl⟩

theorem renderNode_row_state (z α : K) (g : GenComputeRow K) :
    (renderNode z α g).row.2.2.1.state = g.skel.state := by
  unfold renderNode
  cases g.skel.state <;> rfl

end Discharge

end

end Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda
