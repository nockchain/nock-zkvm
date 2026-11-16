import Nock.NockVMROM.Thm54.VclL.Compute.RecReaderQ7
import Nock.NockVMROM.Thm54.VclL.Compute.TowerRecs
import Nock.NockVMROM.Thm54.VclL.Compute.TowerGather

/-!
# GEN-C3 step 1b : the tower instance of `RecReader`

.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.ComputeTable (State FP)
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework
open Nock.NockVMROM.Thm54.RecordCarrier (natLift)
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

section lift
variable {F K K' : Type} [Field F] [Field K] [Algebra F K] [Field K'] [Algebra F K']

/-- `natLift` of a base-field element is the same at any extension of equal characteristic. -/
theorem natLift_algebraMap_eq (h : ringChar K' = ringChar K) (x : F) :
    natLift (algebraMap F K' x) = natLift (algebraMap F K x) := by
  have hiff : ∀ n : ℕ, (n : K') = algebraMap F K' x ↔ (n : K) = algebraMap F K x := by
    intro n
    rw [← map_natCast (algebraMap F K'), ← map_natCast (algebraMap F K),
      (algebraMap F K').injective.eq_iff, (algebraMap F K).injective.eq_iff]
  classical
  unfold natLift
  simp only [h, hiff]

end lift

section tower
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] [Fintype K] [DecidableEq K]
  [DecidableEq (Quad (algebraMap F K δ))] (b : Basis (Fin 3) F K)

theorem recXQ_nine (eK : Env K) (e : Env F) (s : ℕ) (hs : s < 3) :
    recXQ δ eK e s 9 = algebraMap F (Quad (algebraMap F K δ)) (e.trace (xIdxCol s)) := by
  rcases s with _ | _ | _ | s
  · show Q.val δ (qlift F (.var .traceCur fIdxCol)) eK e = _
    rw [qlift_val]; rfl
  · show Q.val δ (qlift F (.var .traceCur (vIdxCol 0))) eK e = _
    rw [qlift_val]; rfl
  · show Q.val δ (qlift F (.var .traceCur (vIdxCol 1))) eK e = _
    rw [qlift_val]; rfl
  · omega

theorem recXQ_ten (eK : Env K) (e : Env F) (s : ℕ) (hs : s < 3) :
    recXQ δ eK e s 10 = if s = 0 then 1 else 0 := by
  rcases s with _ | _ | _ | s
  · show Q.val δ (qconst F 1) eK e = _
    rw [qconst_val]; simp
  · exact Fin.snoc_last (α := fun _ => Quad (algebraMap F K δ)) _ _
  · exact Fin.snoc_last (α := fun _ => Quad (algebraMap F K δ)) _ _
  · omega

theorem recPQ_seven (eK : Env K) (e : Env F) (s : ℕ) (hs : s < 2) :
    recPQ δ eK e s 7 = algebraMap F (Quad (algebraMap F K δ)) (e.trace (pIdxCol s)) := by
  rcases s with _ | _ | s
  · show Q.val δ (qlift F (.var .traceCur (vIdxCol 0))) eK e = _
    rw [qlift_val]; rfl
  · show Q.val δ (qlift F (.var .traceCur (vIdxCol 1))) eK e = _
    rw [qlift_val]; rfl
  · omega

theorem recPQ_six (eK : Env K) (e : Env F) (s : ℕ) (hs : s < 2) :
    recPQ δ eK e s 6 = algebraMap F (Quad (algebraMap F K δ)) (e.trace axCol) := by
  rcases s with _ | _ | s
  · show Q.val δ (qlift F (.var .traceCur axCol)) eK e = _
    rw [qlift_val]; rfl
  · show Q.val δ (qlift F (.var .traceCur axCol)) eK e = _
    rw [qlift_val]; rfl
  · omega

theorem actXQ_one_of_sel (e : Env F) (st : State) (h : SelAt e st)
    (hx : st = .s2 ∨ st = .s5 ∨ st = .s6 ∨ st = .s7 ∨ st = .s8 ∨ st = .s9) :
    actXQ (K := K) δ e 1 = 1 := by
  have ht := selAt_trace h
  simp only [actXQ, selSum_eval, slot1ExportSels, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  rw [ht 2 (by norm_num), ht 5 (by norm_num), ht 6 (by norm_num), ht 7 (by norm_num),
    ht 8 (by norm_num), ht 9 (by norm_num)]
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [selIdx]

/-- **The tower record reader**: `recXQ`/`recPQ`/`actXQ`/`actPQ` at the gathered `𝕂` environment. -/
def towerReader : RecReader (towerGather δ b) K where
  recX11 e := recXQ δ (gatherEnv b e) e
  recP e := recPQ δ (gatherEnv b e) e
  actX := actXQ δ
  actP := actPQ δ
  actX_zero _ := rfl
  actX_one e st h hx := actXQ_one_of_sel δ e st h hx
  actX_two e h := by simp only [actXQ]; rw [selAt_trace h 6 (by norm_num)]; simp [selIdx]
  xroot0 e st := rfl
  xchild0 e := by
    simp only [RV.exportChild, RV.sideOf, recXQ_ten δ _ e 0 (by norm_num), if_true, decide_true]
    rfl
  xroot1 e := rfl
  xchild1 e := by
    simp only [RV.exportChild, RV.sideOf, recXQ_ten δ _ e 1 (by norm_num), show (1 : ℕ) ≠ 0 by decide,
      if_false, zero_ne_one, decide_false, Bool.false_eq_true]
    rfl
  xroot2 e := rfl
  xchild2 e := by
    simp only [RV.exportChild, RV.sideOf, recXQ_ten δ _ e 2 (by norm_num), show (2 : ℕ) ≠ 0 by decide,
      if_false, zero_ne_one, decide_false, Bool.false_eq_true]
    rfl
  xaxis e s hs := by
    simp only [RV.exportAxis, RV.sideOf, recXQ_ten δ _ e s hs]
    by_cases h : s = 0 <;> simp [h]
  xkey e s hs := by
    simp only [RV.exportKey, RV.sideOf, recXQ_nine δ _ e s hs, recXQ_ten δ _ e s hs]
    rw [natLift_algebraMap_eq (ringChar_quad _) (e.trace (xIdxCol s))]
    by_cases h : s = 0 <;> simp [h]
  proot0 e st := rfl
  pchild0 e st st' h hne := by
    rw [NodeRecQ7.decodePub_e_oneHotG _ st st' hne h]; rfl
  proot1 e st := rfl
  pchild1 e st st' h hne := by
    rw [NodeRecQ7.decodePub_sf2f_oneHotG _ st st' hne h]; rfl
  paxis e s hs := by
    simp only [RV.pathAxis, recPQ_six δ _ e s hs]
    exact natLift_algebraMap_eq (ringChar_quad _) _
  pkey e s hs := by
    simp only [RV.pathKey, recPQ_seven δ _ e s hs, recPQ_six δ _ e s hs]
    rw [natLift_algebraMap_eq (ringChar_quad _), natLift_algebraMap_eq (ringChar_quad _)]

end tower

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
