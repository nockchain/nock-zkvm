/-
  NockvmE2E/J9AL/RunGate9LB.lean   (S1)

  `verdict9LVB`: the online verdict `verdict9LV` behind the binding gate `zBind XI0.pubIn z` (the Fiat-Shamir statement `z` starts with `zHdr pubIn`, Exec/ZBind.lean).
  A WRAPPER: `verdict9LV` and its theorems are unchanged.  `verdict9LVB_sound`: accept implies the verdict accepts, and `z` binds `pubIn`.
  STILL NON-ADAPTIVE as a theorem (the headline `nock_e2e_J9AL_succinct_B` is a corollary); the executed verifier now enforces the binding.  Not zero-knowledge.
-/
import NockvmE2E.J9A.RunGate9L
import NockvmE2E.Exec.ZBind

set_option autoImplicit false

namespace NockvmE2E.J9AL.RunGate9LB
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.J9A.RunGate9L NockvmE2E.Exec.ZBind
open Nock.NockVMROM.Thm54 (P8PublicClaim)

def verdict9LVB (XI0 : ExecInst) (root : Dg5) (H Hf : HFn) (FS FSf : FSFn) (z : List ℕ) (π : FlatProof) (πF : FixProof) :
    Except String P8PublicClaim :=
  if !zBind XI0.pubIn z then .error "z does not bind pubIn (zBind)" else verdict9LV XI0 root H Hf FS FSf z π πF

theorem verdict9LVB_sound {XI0 : ExecInst} {root : Dg5} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof} {πF : FixProof}
    {c : P8PublicClaim} (h : verdict9LVB XI0 root H Hf FS FSf z π πF = .ok c) :
    verdict9LV XI0 root H Hf FS FSf z π πF = .ok c ∧ zBind XI0.pubIn z = true := by
  unfold verdict9LVB at h
  by_cases hb : zBind XI0.pubIn z = true
  · simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    exact ⟨h, hb⟩
  · simp only [Bool.not_eq_true] at hb
    simp [hb] at h

/-- the online verdict `verdict9LVO` behind `zBind pubIn z` on the `pubIn` it checks (S1 follow-up; wrapper, `verdict9LVO` unchanged) -/
def verdict9LVOB (Xs : ExecInst) (root : Dg5) (pubIn : PE.PubIn) (H Hf : HFn) (FS FSf : FSFn) (z : List ℕ) (π : FlatProof) (πF : FixProof) :
    Except String P8PublicClaim :=
  if !zBind pubIn z then .error "z does not bind pubIn (zBind)" else verdict9LVO Xs root pubIn H Hf FS FSf z π πF

theorem verdict9LVOB_sound {Xs : ExecInst} {root : Dg5} {pubIn : PE.PubIn} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof} {πF : FixProof}
    {c : P8PublicClaim} (h : verdict9LVOB Xs root pubIn H Hf FS FSf z π πF = .ok c) :
    verdict9LVO Xs root pubIn H Hf FS FSf z π πF = .ok c ∧ zBind pubIn z = true := by
  unfold verdict9LVOB at h
  by_cases hb : zBind pubIn z = true
  · simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    exact ⟨h, hb⟩
  · simp only [Bool.not_eq_true] at hb
    simp [hb] at h

end NockvmE2E.J9AL.RunGate9LB

#print axioms NockvmE2E.J9AL.RunGate9LB.verdict9LVB_sound
#print axioms NockvmE2E.J9AL.RunGate9LB.verdict9LVOB_sound
