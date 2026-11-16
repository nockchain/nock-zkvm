/-
  NockvmE2E/Exec/HSpecGen.lean   (HSpec, ; KERNEL-checked, Mathlib)

  `HSpec` discharged for every instance that passes the setup gates and whose LDE fits the domain (`hN < 2^nD`):
    * `hspec_of_gates`  : `setupGates XX = true → XX.hN < 2^XX.nD → HSpec XX`
    * `hspec_of_shape`  : J-8 (`hN = 2^(k+1)`, `nD = k+7`)
    * `hspec_of_shapeF` : families (J-9 A)
    * `hspec_needs_hD`  : the extra hypothesis is necessary (kernel counterexample, `hN = 2^nD`)
    * `hspec_sat`       : non-vacuity (`toyInstO`)
  The Merkle side is `HSpecTree.fxRagLevels_root`, the algebra is `HSpecAlg.lde_word`.
  No axiom, no `sorry`.
-/
import NockvmE2E.Exec.HSpecAlg
import NockvmE2E.Exec.HSpecTree
import NockvmE2E.Exec.ShapeF

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VF NockvmE2E.Exec.VL

theorem nD_pos_of_gates {XX : ExecInst} (hg : setupGates XX = true) : 1 ≤ XX.nD := by
  simp only [setupGates, Bool.and_eq_true, decide_eq_true_eq] at hg
  omega

theorem fixCols_size_pos (XX : ExecInst) : 1 ≤ (fixCols XX).size := by
  have h : FixCol.zh ∈ fixCols XX := by
    unfold fixCols
    simp
  exact Array.size_pos_iff_exists_mem.mpr ⟨_, h⟩

/-- the LDE words of the fixed columns, as `mkVKData'` computes them -/
def ldeOf (XX : ExecInst) : Array (Array G) :=
  ((fixCols XX).map (fixPoly XX (orbitPts XX))).map fun p => cosetLdeR p XX.nD XX.dGen

theorem root_eq_ldeOf (XX : ExecInst) (Hf : HFn) :
    (mkVKData' XX Hf).vk.root = ((fxRagLevels Hf 0 (fixCols XX).size (2 ^ (XX.nD - 1)) (ldeOf XX))[0]!)[0]! := rfl

/-- **`HSpec` for every gated instance whose LDE fits the domain** -/
theorem hspec_of_gates (XX : ExecInst) (hg : setupGates XX = true) (hD : XX.hN < 2 ^ XX.nD) : HSpec XX := by
  intro Hf
  rw [setup'_of_gates hg]
  refine congrArg some ?_
  have hnD := nD_pos_of_gates hg
  have hW := fixCols_size_pos XX
  have key := fxRagLevels_root Hf (fixCols XX).size (XX.nD - 1) (ldeOf XX)
    (fun r i => specWord XX (fixCols XX)[r]! i) hW (by
      intro r hr i hi
      have hr' : r < (fixCols XX).size := hr
      have hi' : i < 2 ^ XX.nD := by rwa [Nat.sub_add_cancel hnD] at hi
      have hmem : (fixCols XX)[r]! ∈ fixCols XX := by
        rw [getElem!_pos _ r hr']; exact Array.getElem_mem hr'
      unfold ldeOf
      rw [getElem!_pos _ r (by simpa using hr')]
      simp only [Array.getElem_map]
      rw [← getElem!_pos (fixCols XX) r hr']
      exact lde_word XX hg hD _ hmem i hi')
  have hroot : (mkVKData' XX Hf).vk.root = specRoot XX Hf := by
    rw [root_eq_ldeOf]
    refine key.trans ?_
    unfold specRoot
    dsimp only
    refine congrArg (fun F => specTop Hf F (XX.nD - 1) (XX.nD - 1) 1) ?_
    funext g
    unfold specGroup
    dsimp only
    simp only [Nat.zero_mul, Nat.add_zero, Nat.one_mul]
  have e : (mkVKData' XX Hf).vk = ⟨eraseXS XX, fixCols XX, (mkVKData' XX Hf).vk.root⟩ := rfl
  rw [e, hroot]
  rfl

theorem hD_of_shape {XX : ExecInst} (h : J8Shape.j8ShapeOk XX = true) : XX.hN < 2 ^ XX.nD := by
  have h1 := J8Shape.hN_of_shape h
  have h2 : XX.nD = XX.k + 7 := by
    unfold J8Shape.j8ShapeOk at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    tauto
  rw [h1, h2]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem hD_of_shapeF {F : ShapeF.Fam} {XX : ExecInst} (h : ShapeF.shapeOkF F XX = true) : XX.hN < 2 ^ XX.nD := by
  have h1 := ShapeF.hN_of_shapeF h
  have h2 : XX.nD = XX.k + 7 := by
    unfold ShapeF.shapeOkF at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    tauto
  rw [h1, h2]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- J-8: discharged by the shape (`hN = 2^(k+1)`, `nD = k+7`) -/
theorem hspec_of_shape {XX : ExecInst} (hg : setupGates XX = true) (hsh : J8Shape.j8ShapeOk XX = true) : HSpec XX :=
  hspec_of_gates XX hg (hD_of_shape hsh)

/-- families (J-9 A): the same via `shapeOkF` -/
theorem hspec_of_shapeF {F : ShapeF.Fam} {XX : ExecInst} (hg : setupGates XX = true) (hsh : ShapeF.shapeOkF F XX = true) :
    HSpec XX :=
  hspec_of_gates XX hg (hD_of_shapeF hsh)

/-- non-vacuity: `toyInstO` satisfies both hypotheses of `hspec_of_gates` -/
theorem hspec_sat : setupGates toyInstO = true ∧ toyInstO.hN < 2 ^ toyInstO.nD :=
  ⟨toy_setupGates, by decide⟩

theorem hspec_toyInstO : HSpec toyInstO := hspec_of_gates toyInstO hspec_sat.1 hspec_sat.2

/-! ### necessity of `hN < 2^nD` (kernel counterexample) -/

/-- identity "hash": the root is the whole transcript, so root equality = leaf-by-leaf equality -/
def idH : HFn := fun l => l

/-- two tables of `hN_t = 2`, each one kind-1 column (pre coefficients `#[5]`, `#[6]`) + one public column; `nD = 1`, `hN = 2 = 2^nD` -/
def cexInst : ExecInst :=
  { nD := 1, dShift := 7, dGen := dGenOf 1, hN := 2, hGen := dGenOf 32, hShift := 1, r := 2, k := 0, d := 1, l := 1,
    nc := 4, nq := 3, colKind := #[1, 2, 1, 2], blockOf := #[0, 2, 0, 2, 3, 3, 3], pre := #[#[5], #[], #[6], #[]], pubOf := #[1, 3],
    ppt := J8Shape.pptJ8, nCoins := #[1, 1], derived := #[],
    tabs := #[{ hN := 2, col0 := 0, nc := 2, npub := 1, pubBase := 0, chip := J8Shape.toyChip },
              { hN := 2, col0 := 2, nc := 2, npub := 1, pubBase := 1, chip := J8Shape.toyChip }] }

theorem cex_gates : setupGates cexInst = true := by decide +kernel

theorem cex_roots_differ : (mkVKData' cexInst idH).vk.root ≠ (vkSpec cexInst idH).root := by decide +kernel

/-- **`hD` is necessary**: `setupGates` alone does not give `HSpec` (`hN = 2^nD`: `Z_H` has `2^nD + 1` coefficients and the LDE drops the top one) -/
theorem hspec_needs_hD : ∃ XX : ExecInst, setupGates XX = true ∧ XX.hN = 2 ^ XX.nD ∧ ¬ HSpec XX := by
  refine ⟨cexInst, cex_gates, by decide, fun h => ?_⟩
  have h1 := h idH
  rw [setup'_of_gates cex_gates] at h1
  exact cex_roots_differ (congrArg VK.root (Option.some.inj h1))

end NockvmE2E.Exec.V

#print axioms NockvmE2E.Exec.V.hspec_needs_hD
#print axioms NockvmE2E.Exec.V.hspec_of_gates
#print axioms NockvmE2E.Exec.V.hspec_of_shape
#print axioms NockvmE2E.Exec.V.hspec_of_shapeF
#print axioms NockvmE2E.Exec.V.hspec_sat
#print axioms NockvmE2E.Exec.V.hspec_toyInstO
