/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulLeafBound.lean

  **Field-free leaf counts of the 2×2 matmul program text, and the root
  cons fact that makes `SeedGood` non-vacuous.**

  `TraceConfined Λ t` (`GenTraceConfined.lean::TraceConfined`) is
  `∀ g ∈ bfsRows t, RowNounsConfined Λ g` — three `Noun.leaves`
  comparisons per compute row, the generator-side image of
  `λ ≤ Λ` on `FiniteTransitions^Λ` / `NockProgram^Λ`
  (`:1097`).

  This module does **not** discharge `TraceConfined` at the 401-row
  tree.  It records the program-text numbers a combinator induction
  would consume, and that the generated root is `cons` (so `SeedGood`
  is not the vacuous Tier-A predicate).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmul
import Nock.NockVMROM.Thm54.TraceGen.GenLeafWindow
import Nock.NockVMROM.Thm54.CensusExtraClosure

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open ComputeTable

variable {K : Type} [Field K]

/-! ## Program-text leaf counts (no field, no tree walk) -/

theorem op0_leaves (ax : ℕ) : (op0 ax).leaves = 2 := rfl
theorem op1_leaves (n : ℕ) : (op1 n).leaves = 2 := rfl
theorem quote_leaves (n : Noun) : (quote n).leaves = n.leaves + 1 :=
  Nat.add_comm _ _
theorem invokeAxis_leaves (axis : ℕ) : (invokeAxis axis).leaves = 4 := rfl

theorem slam_leaves (batteryF sampleF : Noun) (axis : ℕ) :
    (slam batteryF sampleF axis).leaves =
      batteryF.leaves + sampleF.leaves + 5 := by
  simp [slam, op7, invokeAxis, cell_leaves, atom_leaves]
  omega

theorem addNewSample_leaves : addNewSample.leaves = 8 := by decide

theorem addArm_leaves : addArm.leaves = 23 := by decide

theorem addFromMac_leaves : addFromMac.leaves = 13 := by decide

theorem macNewSample_leaves : macNewSample.leaves = 20 := by decide

theorem macArm_leaves : macArm.leaves = 35 := by decide

theorem mmBattery_leaves : mmBattery.leaves = 58 := by
  rw [mmBattery, cell_leaves, macArm_leaves, addArm_leaves]

theorem invokeMac_leaves (accF nF mF : Noun) :
    (invokeMac accF nF mF).leaves =
      accF.leaves + nF.leaves + mF.leaves + 66 := by
  rw [invokeMac, slam_leaves, quote_leaves, mmBattery_leaves]
  simp [cell_leaves, op1_leaves]
  omega

theorem mac2_leaves (accF nF mF nF' mF' : Noun) :
    (mac2 accF nF mF nF' mF').leaves =
      accF.leaves + nF.leaves + mF.leaves + nF'.leaves + mF'.leaves + 132 := by
  rw [mac2, invokeMac_leaves, invokeMac_leaves]
  omega

theorem mmC00_leaves : mmC00.leaves = 142 := by
  rw [mmC00, mac2_leaves, op1_leaves, op0_leaves, op0_leaves, op0_leaves,
    op0_leaves]

theorem mmC01_leaves : mmC01.leaves = 142 := by
  rw [mmC01, mac2_leaves, op1_leaves, op0_leaves, op0_leaves, op0_leaves,
    op0_leaves]

theorem mmC10_leaves : mmC10.leaves = 142 := by
  rw [mmC10, mac2_leaves, op1_leaves, op0_leaves, op0_leaves, op0_leaves,
    op0_leaves]

theorem mmC11_leaves : mmC11.leaves = 142 := by
  rw [mmC11, mac2_leaves, op1_leaves, op0_leaves, op0_leaves, op0_leaves,
    op0_leaves]

theorem mmFormula_leaves : mmFormula.leaves = 568 := by
  rw [mmFormula, cell_leaves, cell_leaves, cell_leaves,
    mmC00_leaves, mmC01_leaves, mmC10_leaves, mmC11_leaves]

theorem mmC_leaves : mmC.leaves = 4 := rfl

/-- The program text uses OP7 (`slam`) and OP9 (`invokeAxis`).  The SubISA
derivation (`genComputeSkeleton_subISA_traceConfined`) excludes both. -/
theorem mmC00_is_mac2 :
    mmC00 = mac2 (op1 0) (op0 8) (op0 12) (op0 9) (op0 14) :=
  rfl

theorem slam_is_op7 (batteryF sampleF : Noun) (axis : ℕ) :
    slam batteryF sampleF axis =
      .cell (.atom 7) (.cell (.cell batteryF sampleF) (invokeAxis axis)) :=
  rfl

theorem invokeAxis_is_op9 (axis : ℕ) :
    invokeAxis axis =
      .cell (.atom 9) (.cell (.atom axis) (.cell (.atom 0) (.atom 1))) :=
  rfl

/-! ## Autocons roots are `cons` — so `SeedGood` is not vacuous here. -/

/-- An autocons formula emits a `cons`
row.  Field-polymorphic; no `decide`. -/
theorem genComputeSkeleton_autocons_root
    {n : ℕ} {s lh lt rt : Noun}
    {t : NTree (GenComputeRow K)} {r : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) s (.cell (.cell lh lt) rt) =
      .ok (t, r)) :
    t.label.skel.state = .cons := by
  simp only [genComputeSkeleton] at h
  cases hL : genComputeSkeleton (K := K) n s (.cell lh lt) with
  | error _ => simp [hL] at h
  | ok pL =>
    cases hR : genComputeSkeleton (K := K) n s rt with
    | error _ => simp [hL, hR] at h
    | ok pR =>
      simp [hL, hR] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

/-- The generated matmul root is `cons`.  `SeedGood` therefore asks for a
Dyck check on `formulaHead mmFormula`, unlike the vacuous Tier-A case
(`Batch180.dot_seedGood`). -/
theorem mmTree_root_is_cons :
    (mmTree (K := K)).label.skel.state = .cons := by
  have h := mmTree_gen (K := K)
  have hf : mmFormula = .cell (.cell mmC00 mmC01) (.cell mmC10 mmC11) := rfl
  rw [hf] at h
  exact genComputeSkeleton_autocons_root (n := 63) h

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.mmFormula_leaves
#print axioms Nock.NockVMROM.Thm54.TraceGen.mmTree_root_is_cons
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_autocons_root
