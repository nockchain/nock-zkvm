/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestToys.lean

  **The two toys at `computeChipVCLH`'s honest trace**
  (`*[0 [1 0]]` and `*[0 [0 1]]`, as `vcl_completeness_toy` / `_axis1`), over `ZMod 67`.  No hypothesis:
  the run, the atom bound and the first-row publics are discharged.  Plus a discriminating negative
  control (a tampered row fails a real gate).  Additive.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestRun

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk Nock.Reified
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.SemanticStrategy

noncomputable section

instance fact_prime_67 : Fact (Nat.Prime 67) := ⟨by norm_num⟩

abbrev Z67 := ZMod 67

/-- `*[0 [1 0]]`: one OP1 row. -/
def toy1Row : GenComputeRow Z67 :=
  skelNode (genSkelOp1 (.atom 0) (.cell (.atom 1) (.atom 0)) (.atom 0) (.atom 1))
    [⟨.cell (.atom 1) (.atom 0), .atom 0, 3, 0⟩]

/-- `*[0 [0 1]]`: one OP0 row at axis 1. -/
def toy2Row : GenComputeRow Z67 :=
  skelNode (genSkelOp0 (.atom 0) (.cell (.atom 0) (.atom 1)) (.atom 0) (.atom 1) (.atom 0) 1)
    [⟨.cell (.atom 0) (.atom 1), .atom 1, 3, 0⟩, ⟨.atom 0, .atom 0, 1, 0⟩]

theorem toy1_gen : genComputeSkeleton (K := Z67) 2 (.atom 0) (.cell (.atom 1) (.atom 0)) =
    .ok (.node toy1Row [], .atom 0) := by
  simp [genComputeSkeleton, toy1Row]

theorem toy2_gen : genComputeSkeleton (K := Z67) 2 (.atom 0) (.cell (.atom 0) (.atom 1)) =
    .ok (.node toy2Row [], .atom 0) := by
  simp [genComputeSkeleton, toy2Row, Noun.slot]

theorem toy_rows (g : GenComputeRow Z67) : g ∈ bfsRows (airReorder (.node g [])) := by
  simp [airReorder_leaf, bfsRows, bfsForest]

theorem atomsLt_zero : AtomsLt (ringChar Z67) (.atom 0) := by
  intro k hk
  simp [Noun.leafList] at hk
  subst hk
  rw [ZMod.ringChar_zmod_n]; norm_num

/-- The honest rows of the toys, as noun rows. -/
theorem toy1_row : rowOfSkel toy1Row.skel =
    { op := 1, s := .atom 0, f := .cell (.atom 1) (.atom 0), e := .atom 0, fh := .atom 1,
      ft := .atom 0 } := by
  simp [rowOfSkel, toy1Row, skelNode, genSkelOp1, VclL.hdN, VclL.tlN]

theorem toy2_row : rowOfSkel toy2Row.skel =
    { op := 0, s := .atom 0, f := .cell (.atom 0) (.atom 1), e := .atom 0, fh := .atom 0,
      ft := .atom 1 } := by
  simp [rowOfSkel, toy2Row, skelNode, genSkelOp0, VclL.hdN, VclL.tlN]

/-- **Toy 1**: every non-lookup base gate holds on the honest row of `*[0 [1 0]]`. -/
theorem toy1_gates (cells : List Noun) :
    ∀ gate ∈ (arithGates : List (CoeffExpr ℚ)) ++ (eqGates : List (EqG ℚ)).map EqG.gate,
      (mapC (fun q : ℚ => (q : Z67)) gate).eval
        (hEnv cells (rowOfSkel toy1Row.skel) 1 1 (pubVec cells (rowOfSkel toy1Row.skel))) = 0 := by
  refine honest_row_base_gates (t := .node toy1Row []) (by simpa using toy1_gen) (toy_rows _) cells 1 1
    _ ?_ (Or.inr ⟨rfl, rfl, rfl⟩)
  rw [toy1_row]; exact ⟨atomsLt_zero, atomsLt_zero⟩

/-- **Toy 2** (axis 1, `z1 = 1`). -/
theorem toy2_gates (cells : List Noun) :
    ∀ gate ∈ (arithGates : List (CoeffExpr ℚ)) ++ (eqGates : List (EqG ℚ)).map EqG.gate,
      (mapC (fun q : ℚ => (q : Z67)) gate).eval
        (hEnv cells (rowOfSkel toy2Row.skel) 1 1 (pubVec cells (rowOfSkel toy2Row.skel))) = 0 := by
  refine honest_row_base_gates (t := .node toy2Row []) (by simpa using toy2_gen) (toy_rows _) cells 1 1
    _ ?_ (Or.inr ⟨rfl, rfl, rfl⟩)
  rw [toy2_row]; exact ⟨atomsLt_zero, atomsLt_zero⟩

/-! ## Negative control: a tampered row fails a real gate -/

/-- Toy 1 with a wrong result (`e = 5` instead of the formula tail `0`). -/
def toy1Bad : RowN := { rowOfSkel toy1Row.skel with e := .atom 5 }

/-- The OP1 equality gate `e = f_t` evaluates to `5 ≠ 0` on the tampered row. -/
theorem toy1_bad_gate_fails :
    (mapC (fun q : ℚ => (q : Z67)) (EqG.gate (⟨cc 1, hE.v, .col hFt.v⟩ : EqG ℚ))).eval
      (hEnv [] toy1Bad 1 1 (pubVec [] toy1Bad)) ≠ 0 := by
  rw [eval_mapC_cast]
  have : rowOfSkel toy1Row.skel = _ := toy1_row
  simp [toy1Bad, this, evalQ, EqG.gate, Opnd.expr, hEnv, cc, hE, hFt, hd, hn, colVal, cvOne]
  decide

end

end Nock.NockVMROM.Thm54.VclL.Handle
