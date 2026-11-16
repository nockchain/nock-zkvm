/-
 conjunct 5 glue lemmas (challenges,...).

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue17` is complete.
-/
import NockvmE2E.Exec.SideGlue16

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideGlue17
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Merkle NockvmE2E.Exec.SideInst
  NockvmE2E.Merkle.Fri NockvmE2E.Exec.SF NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.DomIdx NockvmE2E.Exec.E2EFri
  NockvmE2E.Exec.SideGlue9 NockvmE2E.FriPort NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Merkle.RapFriQ NockvmE2E.Exec.SideGlue13
  NockvmE2E.Exec.E2EResid NockvmE2E.Exec.Inst NockvmE2E.Exec.Emb

/-- the entries `1 .. k+3` of the verifier's challenge array, read by the FS function -/
theorem fixChals_getElem' (vk : VK) (FSf : FSFn) (z ctx : List Nat) (πF : FixProof) (hl : 0 < vk.X.l)
    (hr : vk.X.k ≤ πF.roots.size) (i : ℕ) (hi1 : 1 ≤ i) (ht : i ≤ vk.X.k + 3) :
    (fixChals vk FSf z ctx πF)[i]! =
      FSf (z :: ctx :: ((fixMsgs vk.X.k ctx πF.vF πF.roots πF.pfinal).toList.drop 1).take i)
        (fixNl vk.X.k vk.X.l (i)) := by
  have hsz : (fixMsgs vk.X.k ctx πF.vF πF.roots πF.pfinal).size = vk.X.k + 4 := by
    simp [fixMsgs, Array.size_extract]
    omega
  unfold fixChals
  simp only
  rw [hsz]
  have hlt : i < vk.X.k + 4 := by omega
  have hlt' : i < (Array.map (fun i : ℕ => if fixNl vk.X.k vk.X.l i == 0 then ([] : List Nat) else FSf (z :: ((fixMsgs vk.X.k ctx πF.vF πF.roots πF.pfinal).extract 0 (i + 1)).toList)
        (fixNl vk.X.k vk.X.l i)) (Array.range (vk.X.k + 4))).size := by simp; omega
  rw [getElem!_pos _ (i) hlt']
  simp only [Array.getElem_map, Array.getElem_range]
  have hne : (fixNl vk.X.k vk.X.l (i) == 0) = false := by
    unfold fixNl
    by_cases h1 : i ≤ 2 + vk.X.k
    · simp [h1]; omega
    · have : i = 3 + vk.X.k := by omega
      simp [this]
      omega
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  congr 1
  congr 1
  generalize hM : fixMsgs vk.X.k ctx πF.vF πF.roots πF.pfinal = M at hsz ⊢
  have hM0 : M[0]? = some ctx := by
    rw [← hM]; simp [fixMsgs]
  rcases hMl : M.toList with _ | ⟨a, rest⟩
  · simp at hMl; subst hMl; simp at hsz
  · have ha : a = ctx := by
      have : M[0]? = some a := by
        rw [← Array.getElem?_toList]; simp [hMl]
      rw [hM0] at this; exact (Option.some.inj this).symm
    subst ha
    simp [Array.toList_extract, hMl, List.take_succ_cons]


section Side
variable {n k : ℕ} {ω : SmoothCosetFftDomain n KC} (s : Fin (k + 1) → ℕ+) (l : ℕ) (L : Fri.FriLeaves (ω := ω) s)
  [SampleableType KC] [Inhabited KC] [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (XI : ExecInst) {Statement Salt : Type} (decZ : List ℕ → Statement × Salt) (encZ : Statement × Salt → List ℕ)

/-- **`hch` glue**: the verifier's challenge `t+2` (`alpha_t`, ..., query challenge) is the encoded challenge `t` of the friMask path -/
theorem chal_fix (hz : ∀ x, decZ (encZ x) = x) {Op : Type} [Finite Op] [DecidableEq Op] (ω0 ω' : Op)
    (gk : (kk : Key (SStmt XI × (Statement × Salt)) PUnit (compiledRoundsK DgJ8 Op (SMSg s l L))) → kk.Challenge)
    (vk : VK) (hk : vk.X.k = k) (hl : vk.X.l = l) (hl0 : 0 < l) (FSf : FSFn)
    (hFSf : ∀ x nn, FSf x nn = frOfX s l L XI ω0 (fkOfX s l L XI decZ ω0 x) (gk _) nn)
    (z0 : Statement × Salt) (ctx : List ℕ) (πF : FixProof) (hr : k ≤ πF.roots.size) (t : ℕ) (ht : t < k + 2) :
    (fixChals vk FSf (encZ z0) ctx πF)[t + 2]! =
      (encPathD (compiledRoundsK DgJ8 Op (friMask s 1 l L DgJ8 E2EResid.encK))
        (mDecs dgOf (friMask s 1 l L DgJ8 E2EResid.encK) (dsmC s 1 l L E2EResid.encK) ω0)
        (pathOf (stF XI ctx (((fixMsgs k ctx πF.vF πF.roots πF.pfinal).toList.drop 1).headD []), z0) _ gk
          (decMsgs _ (mDecs dgOf (SMSg s l L) (dsS s l L) ω') ((fixMsgs k ctx πF.vF πF.roots πF.pfinal).toList.drop 1))).2.2).getD t [] := by
  have hr' : vk.X.k ≤ πF.roots.size := by rw [hk]; exact hr
  rw [SideGlue16.fixChals_getElem vk FSf (encZ z0) ctx πF (by rw [hl]; exact hl0) hr' t (by rw [hk]; exact ht)]
  rw [hk, hl, hFSf]
  have hsz : (fixMsgs k ctx πF.vF πF.roots πF.pfinal).size = k + 4 := by
    simp [fixMsgs, Array.size_extract]
    omega
  have hlen : ((fixMsgs k ctx πF.vF πF.roots πF.pfinal).toList.drop 1).length = k + 3 := by
    simp [hsz]
  rw [SideGlue15.chal_side s l L XI decZ encZ hz ω0 ω' gk z0 ctx _ (by omega) t (by omega)]


/-- **`cs` glue**: the verifier's batching challenge (as a `KC` element) is the clear challenge of the compiled side path -/
theorem cs_fix (hz : ∀ x, decZ (encZ x) = x) {Op : Type} [Finite Op] [DecidableEq Op] (ω0 ω' : Op)
    (gk : (kk : Key (SStmt XI × (Statement × Salt)) PUnit (compiledRoundsK DgJ8 Op (SMSg s l L))) → kk.Challenge)
    (vk : VK) (hk : vk.X.k = k) (hl : vk.X.l = l) (hl0 : 0 < l) (FSf : FSFn)
    (hFSf : ∀ x nn, FSf x nn = frOfX s l L XI ω0 (fkOfX s l L XI decZ ω0 x) (gk _) nn)
    (z0 : Statement × Salt) (ctx : List ℕ) (πF : FixProof) (hr : k ≤ πF.roots.size) :
    toKV (VF.K3.ofLimbs (fixChals vk FSf (encZ z0) ctx πF)[1]!) =
      (pathOf (stF XI ctx (((fixMsgs k ctx πF.vF πF.roots πF.pfinal).toList.drop 1).headD []), z0) _ gk
          (decMsgs _ (mDecs dgOf (SMSg s l L) (dsS s l L) ω') ((fixMsgs k ctx πF.vF πF.roots πF.pfinal).toList.drop 1))).2.1 := by
  have hr' : vk.X.k ≤ πF.roots.size := by rw [hk]; exact hr
  rw [fixChals_getElem' vk FSf (encZ z0) ctx πF (by rw [hl]; exact hl0) hr' 1 le_rfl (by omega)]
  rw [hk, hl, hFSf]
  have hsz : (fixMsgs k ctx πF.vF πF.roots πF.pfinal).size = k + 4 := by
    simp [fixMsgs, Array.size_extract]
    omega
  have hlen : ((fixMsgs k ctx πF.vF πF.roots πF.pfinal).toList.drop 1).length = k + 3 := by
    simp [hsz]
  have h := SideGlue.fs_side s l L XI decZ encZ hz ω0 ω' gk z0 ctx ((fixMsgs k ctx πF.vF πF.roots πF.pfinal).toList.drop 1) (by omega) 1 le_rfl (by omega) (fixNl k l 1)
  rw [h]
  exact E2EFinal.hcsC_dsbC _

end Side




end NockvmE2E.Exec.SideGlue17

#print axioms NockvmE2E.Exec.SideGlue17.chal_fix
#print axioms NockvmE2E.Exec.SideGlue17.fixChals_getElem'
#print axioms NockvmE2E.Exec.SideGlue17.cs_fix
