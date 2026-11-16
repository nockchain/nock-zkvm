/-
  Nock/RedTeam/Batch339Thm54SelectorTwoRejected.lean

  A selector column set to `2` is rejected by the
  committed booleanity gate `selectorBool k` (the paper, SV2
  `op_j · (1 − op_j) = 0`).  Instrument: `CoeffExpr.eval` of that named
  gate.  Either `compute_satisfies` fails (this file: the gate is nonzero)
  or `deployed_row_one_hot` is false (a column equal to `2` is not one-hot).
-/
import Lean
import Nock.NockVMROM.Thm54.DeployedComputeRows
import Nock.NockVMROM.Thm54.BoundSemanticTrace
import Nock.NockVMROM.Thm54.CoordinateCompiler
import Nock.RedTeam.Batch338Thm54DeployedAcceptance

set_option autoImplicit false

namespace Nock.RedTeam.Batch339

open Lean Meta Elab Command
open Nock
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.CoordinateCompiler

/-! ## The rejecting gate -/

/-- `selectorBool k` is a committed base gate of the compute chip. -/
theorem b339_selectorBool_mem_base (k n : ℕ) (hk : k < 11) :
    selectorBool (F := ℚ) k ∈ finalBaseTransitionGates (F := ℚ) n := by
  simp only [finalBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl ⟨k, hk, rfl⟩

/-- Evaluated value of the booleanity gate at a free environment. -/
theorem b339_selectorBool_eval {F : Type*} [Field F] (k : ℕ) (env : Nock.Reified.Env F) :
    CoeffExpr.eval (selectorBool (F := F) k) env = env.trace k * (1 - env.trace k) := by
  simp [selectorBool, bv, CoeffExpr.eval]

/-- **Negative control.**  If selector column `k` is `2` and `char ≠ 2`, the committed
booleanity gate is `-2 ≠ 0`.  That is the rejecting gate. -/
theorem b339_selector_two_gate_nonzero {F : Type*} [Field F]
    (k : ℕ) (env : Nock.Reified.Env F)
    (h2 : env.trace k = 2) (htwo : (2 : F) ≠ 0) :
    CoeffExpr.eval (selectorBool (F := F) k) env ≠ 0 := by
  rw [b339_selectorBool_eval, h2]
  have : (2 : F) * (1 - 2) = -2 := by ring
  rw [this]
  exact neg_ne_zero.mpr htwo

/-- Concrete witness at `ℚ`: column `0` set to `2` makes `selectorBool 0` equal `-2`. -/
def twoSelEnv : Nock.Reified.Env ℚ where
  trace i := if i = 0 then 2 else 0
  traceNext _ := 0
  chal _ := 0
  pub _ := 0

theorem b339_concrete_selector_two_rejected :
    CoeffExpr.eval (selectorBool (F := ℚ) 0) twoSelEnv = -2 ∧
      CoeffExpr.eval (selectorBool (F := ℚ) 0) twoSelEnv ≠ 0 := by
  constructor
  · simp [b339_selectorBool_eval, twoSelEnv]
    ring
  · exact b339_selector_two_gate_nonzero 0 twoSelEnv (by simp [twoSelEnv]) (by norm_num)

/-- A column equal to `2` is not a one-hot value, so `OneHotSelector` fails. -/
theorem b339_two_not_oneHot {K : Type*} [Field K]
    (env : Nock.Reified.Env K) (st : ComputeTable.State)
    (h2 : env.trace 0 = 2) (htwo : (2 : K) ≠ 0 ∧ (2 : K) ≠ 1) :
    ¬ OneHotSelector env st := by
  intro h
  have h0 := h ComputeTable.State.s0
  change env.trace 0 = (if ComputeTable.State.s0 = st then 1 else 0) at h0
  rw [h2] at h0
  by_cases hst : ComputeTable.State.s0 = st
  · simp [hst] at h0
    exact htwo.2 h0
  · simp [hst] at h0
    exact htwo.1 h0


open Nock.RedTeam.Batch338

/-! `SkeletonOperationalCore`'s field types reach `Noun`. -/
run_cmd do
  let env ← getEnv
  let S : Name := ``Nock.NockVMROM.Thm54.BoundSemanticTrace.SkeletonOperationalCore
  let roots := projNames env S
  unless roots.size == 4 do
    throwError m!"SkeletonOperationalCore field count is {roots.size}, expected 4"
  let r := typeReach env roots
  let noun : Name := ``Nock.Noun
  unless r.contains noun do
    -- try the tree-qualified name
    let alt : Name := `Nock.Tree.Noun
    unless r.contains alt do
      throwError m!"SkeletonOperationalCore type-walk does not reach Noun (reach={r.size})"
  logInfo m!"Batch339 SkeletonOperationalCore typeReach={r.size} Noun PRESENT (H1.2 interface)"

end Nock.RedTeam.Batch339

#print axioms Nock.RedTeam.Batch339.b339_selector_two_gate_nonzero
#print axioms Nock.RedTeam.Batch339.b339_concrete_selector_two_rejected
#print axioms Nock.RedTeam.Batch339.b339_two_not_oneHot
#print axioms Nock.RedTeam.Batch339.b339_selectorBool_mem_base
