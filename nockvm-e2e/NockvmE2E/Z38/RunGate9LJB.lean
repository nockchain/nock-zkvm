/-
  NockvmE2E/Z38/RunGate9LJB.lean   (S1)

  `verdict9LJVB`: the online verdict `verdict9LJV` behind the binding gate `zBind XI0.pubIn z` (the Fiat-Shamir statement `z` starts with `zHdr pubIn`, Exec/ZBind.lean).
  A WRAPPER: `verdict9LJV` and its theorems are unchanged.  `verdict9LJVB_sound`: accept implies the verdict accepts, and `z` binds `pubIn`.
  STILL NON-ADAPTIVE as a theorem (the headline `nock_e2e_J9ALJ_succinct_B` is a corollary); the executed verifier now enforces the binding.  Not zero-knowledge.
-/
import NockvmE2E.Z38.RunGate9LJ
import NockvmE2E.Exec.ZBind

set_option autoImplicit false

namespace NockvmE2E.Z38.RunGate9LJB
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Z38.RunGate9LJ NockvmE2E.Exec.ZBind
open Nock.NockVMROM.Thm54 (P8PublicClaim)

def verdict9LJVB (XI0 : ExecInst) (root : Dg5) (H Hf : HFn) (FS FSf : FSFn) (z : List ℕ) (π : FlatProof) (πF : FixProof) :
    Except String P8PublicClaim :=
  if !zBind XI0.pubIn z then .error "z does not bind pubIn (zBind)" else verdict9LJV XI0 root H Hf FS FSf z π πF

theorem verdict9LJVB_sound {XI0 : ExecInst} {root : Dg5} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof} {πF : FixProof}
    {c : P8PublicClaim} (h : verdict9LJVB XI0 root H Hf FS FSf z π πF = .ok c) :
    verdict9LJV XI0 root H Hf FS FSf z π πF = .ok c ∧ zBind XI0.pubIn z = true := by
  unfold verdict9LJVB at h
  by_cases hb : zBind XI0.pubIn z = true
  · simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    exact ⟨h, hb⟩
  · simp only [Bool.not_eq_true] at hb
    simp [hb] at h

/-- the online verdict `verdict9LJVO` behind `zBind pubIn z` on the `pubIn` it checks (S1 follow-up; wrapper, `verdict9LJVO` unchanged) -/
def verdict9LJVOB (Xs : ExecInst) (root : Dg5) (pubIn : PE.PubIn) (H Hf : HFn) (FS FSf : FSFn) (z : List ℕ) (π : FlatProof) (πF : FixProof) :
    Except String P8PublicClaim :=
  if !zBind pubIn z then .error "z does not bind pubIn (zBind)" else verdict9LJVO Xs root pubIn H Hf FS FSf z π πF

theorem verdict9LJVOB_sound {Xs : ExecInst} {root : Dg5} {pubIn : PE.PubIn} {H Hf : HFn} {FS FSf : FSFn} {z : List ℕ} {π : FlatProof} {πF : FixProof}
    {c : P8PublicClaim} (h : verdict9LJVOB Xs root pubIn H Hf FS FSf z π πF = .ok c) :
    verdict9LJVO Xs root pubIn H Hf FS FSf z π πF = .ok c ∧ zBind pubIn z = true := by
  unfold verdict9LJVOB at h
  by_cases hb : zBind pubIn z = true
  · simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    exact ⟨h, hb⟩
  · simp only [Bool.not_eq_true] at hb
    simp [hb] at h

end NockvmE2E.Z38.RunGate9LJB

#print axioms NockvmE2E.Z38.RunGate9LJB.verdict9LJVB_sound
#print axioms NockvmE2E.Z38.RunGate9LJB.verdict9LJVOB_sound
