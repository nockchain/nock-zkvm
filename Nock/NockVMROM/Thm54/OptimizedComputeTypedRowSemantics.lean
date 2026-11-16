import Nock.NockVMROM.Thm54.OptimizedComputeRowSemantics
import Nock.NockVMROM.Thm54.OptimizedComputeTypedLowering

/-! Row-local semantics for the typed 13-base / 58-extension lowering. -/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeTypedRowSemantics

open Nock
open Module
open OptimizedComputeBaseGates
open OptimizedComputeGateBasis
open OptimizedComputeRowSemantics
open OptimizedComputeTypedLowering

noncomputable section

def TypedRowTransitionSat {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (env : TypedEnv F K) : Prop :=
  (∀ g ∈ baseTransitionGates, g.eval (env.toCoeffEnv b) = 0) ∧
    (∀ t ∈ loweredExtTransitionGates, t.eval env = 0)

def TypedCompleteSourceRow {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (env : TypedEnv F K) : Prop :=
  CompleteSourceRow (env.toCoeffEnv b) env.toMixedEnv

/-- Typed row-local satisfaction is exactly the full repaired transition source conjunction. -/
theorem typedRowTransitionSat_iff_completeSource
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (env : TypedEnv F K)
    (hbase : SummaryCollisionFree (env.toCoeffEnv b))
    (hfold : ∀ es ∈ nonIOSourceFamilies17, CollisionFree env.toMixedEnv es) :
    TypedRowTransitionSat b env ↔ TypedCompleteSourceRow b env := by
  rw [TypedRowTransitionSat, TypedCompleteSourceRow,
    loweredExtTransitionGates_eval_iff]
  exact rowTransitionSat_iff_completeSource
    (env.toCoeffEnv b) env.toMixedEnv hbase hfold

theorem typed_malformed_source_rejected
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {e : ℕ} (b : Basis (Fin e) F K) (env : TypedEnv F K)
    (hbase : SummaryCollisionFree (env.toCoeffEnv b))
    (hfold : ∀ es ∈ nonIOSourceFamilies17, CollisionFree env.toMixedEnv es)
    (hbad : ¬ TypedCompleteSourceRow b env) :
    ¬ TypedRowTransitionSat b env := by
  rw [typedRowTransitionSat_iff_completeSource b env hbase hfold]
  exact hbad

#print axioms typedRowTransitionSat_iff_completeSource
#print axioms typed_malformed_source_rejected

end
end OptimizedComputeTypedRowSemantics
end Nock.NockVMROM.Thm54
