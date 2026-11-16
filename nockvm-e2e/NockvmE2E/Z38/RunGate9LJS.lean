/-
  `verdict9LJVS`: the binding verdict `verdict9LJVB` run at the RECOMPUTED VK root.  `setupData' XI0 Hf` is the function `vk-setup` runs; the vk file's root `rootF`
  must equal the recomputed `D.vk.root`, else REJECT.  A WRAPPER: `verdict9LJVB` and its theorems are unchanged.
  `verdict9LJVS_sound` (kernel): accept implies the unchanged premise of the `_B` headline, `rootF` is the honest root, and the executed online check is
  `verifyOnline'` at the honest VK `(mkVKData' XI0 Hf).vk`.  Not zero-knowledge.
-/
import NockvmE2E.Z38.RunGate9LJB
import NockvmE2E.Exec.VKp

set_option autoImplicit false

namespace NockvmE2E.Z38.RunGate9LJS
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.J9A.RunGate9V NockvmE2E.Z38.RunGate9LJB NockvmE2E.Z38.RunGate9LJ
open Nock.NockVMROM.Thm54 (P8PublicClaim)

/-- `verdict9LJVB` at the RECOMPUTED VK root; the vk file's root must equal it -/
def verdict9LJVS (XI0 : ExecInst) (rootF : Dg5) (H Hf : HFn) (FS FSf : FSFn) (z : List ℕ) (π : FlatProof) (πF : FixProof) :
    Except String P8PublicClaim :=
  match setupData' XI0 Hf with
  | none => .error "setupGates"
  | some D =>
    if D.vk.root != rootF then .error "vk root differs from setup (vk-setup)" else
      verdict9LJVB XI0 D.vk.root H Hf FS FSf z π πF

theorem vkOfRoot_mkVKData' (XX : ExecInst) (Hf : HFn) : vkOfRoot XX (mkVKData' XX Hf).vk.root = (mkVKData' XX Hf).vk := rfl

theorem verdict9LJVS_sound {XI0 : ExecInst} {rootF : Dg5} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof} {πF : FixProof}
    {c : P8PublicClaim} (h : verdict9LJVS XI0 rootF H Hf FS FSf z π πF = .ok c) :
    verdict9LJVB XI0 rootF H Hf FS FSf z π πF = .ok c
    ∧ rootF = (mkVKData' XI0 Hf).vk.root
    ∧ verifyOnline' (mkVKData' XI0 Hf).vk H Hf FS FSf z π πF = true := by
  unfold verdict9LJVS at h
  split at h
  · cases h
  · rename_i D hD
    have hDe : D = mkVKData' XI0 Hf := by
      unfold setupData' at hD
      split at hD
      · cases hD
      · cases hD; rfl
    subst hDe
    by_cases hr : ((mkVKData' XI0 Hf).vk.root != rootF) = true
    · simp [hr] at h
    · have hr' : (mkVKData' XI0 Hf).vk.root = rootF := by simpa using hr
      simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
      rw [hr'] at h
      refine ⟨h, hr'.symm, ?_⟩
      have h3 := (verdict9LJV_sound (verdict9LJVB_sound h).1).2.2.2.2.2
      rw [← hr'] at h3
      exact h3

end NockvmE2E.Z38.RunGate9LJS

#print axioms NockvmE2E.Z38.RunGate9LJS.vkOfRoot_mkVKData'
#print axioms NockvmE2E.Z38.RunGate9LJS.verdict9LJVS_sound
