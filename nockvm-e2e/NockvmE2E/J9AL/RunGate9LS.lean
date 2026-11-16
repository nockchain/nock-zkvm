/-
  `verdict9LVS`: the binding verdict `verdict9LVB` run at the RECOMPUTED VK root.  `setupData' XI0 Hf` is the function `vk-setup` runs; the vk file's root `rootF`
  must equal the recomputed `D.vk.root`, else REJECT.  A WRAPPER: `verdict9LVB` and its theorems are unchanged.
  `verdict9LVS_sound` (kernel): accept implies the unchanged premise of the `_B` headline, `rootF` is the honest root, and the executed online check is
  `verifyOnline'` at the honest VK `(mkVKData' XI0 Hf).vk`.  Not zero-knowledge.
-/
import NockvmE2E.J9AL.RunGate9LB
import NockvmE2E.Exec.VKp

set_option autoImplicit false

namespace NockvmE2E.J9AL.RunGate9LS
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.J9A.RunGate9V NockvmE2E.J9AL.RunGate9LB NockvmE2E.J9A.RunGate9L
open Nock.NockVMROM.Thm54 (P8PublicClaim)

/-- `verdict9LVB` at the RECOMPUTED VK root; the vk file's root must equal it -/
def verdict9LVS (XI0 : ExecInst) (rootF : Dg5) (H Hf : HFn) (FS FSf : FSFn) (z : List ℕ) (π : FlatProof) (πF : FixProof) :
    Except String P8PublicClaim :=
  match setupData' XI0 Hf with
  | none => .error "setupGates"
  | some D =>
    if D.vk.root != rootF then .error "vk root differs from setup (vk-setup)" else
      verdict9LVB XI0 D.vk.root H Hf FS FSf z π πF

theorem vkOfRoot_mkVKData' (XX : ExecInst) (Hf : HFn) : vkOfRoot XX (mkVKData' XX Hf).vk.root = (mkVKData' XX Hf).vk := rfl

theorem verdict9LVS_sound {XI0 : ExecInst} {rootF : Dg5} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof} {πF : FixProof}
    {c : P8PublicClaim} (h : verdict9LVS XI0 rootF H Hf FS FSf z π πF = .ok c) :
    verdict9LVB XI0 rootF H Hf FS FSf z π πF = .ok c
    ∧ rootF = (mkVKData' XI0 Hf).vk.root
    ∧ verifyOnline' (mkVKData' XI0 Hf).vk H Hf FS FSf z π πF = true := by
  unfold verdict9LVS at h
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
      have h3 := (verdict9LV_sound (verdict9LVB_sound h).1).2.2.2.2.2
      rw [← hr'] at h3
      exact h3

end NockvmE2E.J9AL.RunGate9LS

#print axioms NockvmE2E.J9AL.RunGate9LS.vkOfRoot_mkVKData'
#print axioms NockvmE2E.J9AL.RunGate9LS.verdict9LVS_sound
