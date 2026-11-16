/-
  Nock/NockVMROM/Thm54/BelowDefs/P8Core/DeployedComputeRows.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/P8Core/DeployedComputeRows.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.OptimizedHostileTimestamps

namespace Nock.NockVMROM.Thm54

namespace DeployedComputeRows

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.Framework
open Nock.Framework.Reify
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeSemanticRealization
open OptimizedComputeCorrectedFinal
open ComputePaperPacking
open Module
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- The eleven booleanities and the one-hot sum vanish at a one-hot selector. -/
theorem svBaseGates_of_oneHot {env : Env K} {st : State}
    (h : OneHotSelector env st) :
    ∀ e ∈ svBaseGates, e.eval env = 0 := by
  intro e he
  simp only [svBaseGates, List.mem_append, List.mem_singleton] at he
  rcases he with hbool | rfl
  · simp only [svBoolExprs, List.mem_map] at hbool
    obtain ⟨t, -, rfl⟩ := hbool
    have ht := h t
    simp only [svBoolExprF, tc, Expr.eval, ht]
    split_ifs <;> ring
  · simp only [svOneHotExprF, tc, Expr.eval, sub_eq_zero]
    have h0 : env.trace 0 = if .s0 = st then 1 else 0 := by simpa [opCol] using h .s0
    have h1 : env.trace 1 = if .s1 = st then 1 else 0 := by simpa [opCol] using h .s1
    have h2 : env.trace 2 = if .s2 = st then 1 else 0 := by simpa [opCol] using h .s2
    have h3 : env.trace 3 = if .s3 = st then 1 else 0 := by simpa [opCol] using h .s3
    have h4 : env.trace 4 = if .s4 = st then 1 else 0 := by simpa [opCol] using h .s4
    have h5 : env.trace 5 = if .s5 = st then 1 else 0 := by simpa [opCol] using h .s5
    have h6 : env.trace 6 = if .s6 = st then 1 else 0 := by simpa [opCol] using h .s6
    have h7 : env.trace 7 = if .s7 = st then 1 else 0 := by simpa [opCol] using h .s7
    have h8 : env.trace 8 = if .s8 = st then 1 else 0 := by simpa [opCol] using h .s8
    have h9 : env.trace 9 = if .s9 = st then 1 else 0 := by simpa [opCol] using h .s9
    have h10 : env.trace 10 = if .cons = st then 1 else 0 := by simpa [opCol] using h .cons
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    cases st <;> simp

theorem alwaysOn_mem_rowLocal {g : _}
    (hg : g ∈ ComputePaperPacking.alwaysOnOptimized) :
    g ∈ ComputePaperPacking.paperPackingRowLocal :=
  List.mem_append.mpr (Or.inr hg)

/-- The original-layout environment decoded from a gathered row. -/
noncomputable def decodeSource (env : CorrectedFinalTypedEnv F K) : Env K :=
  Env.ofSubst computeSubst env.toSourceEnv

noncomputable def decodeInputs (env : CorrectedFinalTypedEnv F K) : Inputs K :=
  inpOf (decodeSource env)

noncomputable def decodePub (env : CorrectedFinalTypedEnv F K) (st : State) : Pub K :=
  pubOfState (decodeSource env) st

noncomputable def decodeDec (env : CorrectedFinalTypedEnv F K) : Dec K :=
  decOf (decodeSource env)

noncomputable def decodeEx (env : CorrectedFinalTypedEnv F K) : Extra K :=
  exOf (decodeSource env)

/-- `V_comp` at the fingerprints a gathered row decodes to. -/
def VcompAt (env : CorrectedFinalTypedEnv F K) : Prop :=
  ∃ st : State, OneHotSelector env.toSourceEnv st ∧
    Vcomp (decodeInputs env) (decodePub env st) (decodeDec env)

end DeployedComputeRows

end Nock.NockVMROM.Thm54
