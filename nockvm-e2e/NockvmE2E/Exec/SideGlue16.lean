/-
 conjunct 5, `hch` glue: the verifier's challenge array entry `fixChals[t+2]!` is the encoded challenge `t` of the friMask path.

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue16` is complete.
-/
import NockvmE2E.Exec.SideGlue13
import NockvmE2E.Exec.SideGlue15

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideGlue16
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Merkle NockvmE2E.Exec.SideInst
  NockvmE2E.Merkle.Fri NockvmE2E.Exec.SF NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.DomIdx NockvmE2E.Exec.E2EFri
  NockvmE2E.Exec.SideGlue9 NockvmE2E.FriPort NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Merkle.RapFriQ NockvmE2E.Exec.SideGlue13
  NockvmE2E.Exec.E2EResid NockvmE2E.Exec.Inst NockvmE2E.Exec.Emb

/-- the entries `2 .. k+3` of the verifier's challenge array, read by the FS function -/
theorem fixChals_getElem (vk : VK) (FSf : FSFn) (z ctx : List Nat) (πF : FixProof) (hl : 0 < vk.X.l)
    (hr : vk.X.k ≤ πF.roots.size) (t : ℕ) (ht : t < vk.X.k + 2) :
    (fixChals vk FSf z ctx πF)[t + 2]! =
      FSf (z :: ctx :: ((fixMsgs vk.X.k ctx πF.vF πF.roots πF.pfinal).toList.drop 1).take (t + 2))
        (fixNl vk.X.k vk.X.l (t + 2)) := by
  have hsz : (fixMsgs vk.X.k ctx πF.vF πF.roots πF.pfinal).size = vk.X.k + 4 := by
    simp [fixMsgs, Array.size_extract]
    omega
  unfold fixChals
  simp only
  rw [hsz]
  have hlt : t + 2 < vk.X.k + 4 := by omega
  have hlt' : t + 2 < (Array.map (fun i : ℕ => if fixNl vk.X.k vk.X.l i == 0 then ([] : List Nat) else FSf (z :: ((fixMsgs vk.X.k ctx πF.vF πF.roots πF.pfinal).extract 0 (i + 1)).toList)
        (fixNl vk.X.k vk.X.l i)) (Array.range (vk.X.k + 4))).size := by simp; omega
  rw [getElem!_pos _ (t + 2) hlt']
  simp only [Array.getElem_map, Array.getElem_range]
  have hne : (fixNl vk.X.k vk.X.l (t + 2) == 0) = false := by
    unfold fixNl
    by_cases h1 : t + 2 ≤ 2 + vk.X.k
    · simp [h1]
    · have : t + 2 = 3 + vk.X.k := by omega
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

end NockvmE2E.Exec.SideGlue16

#print axioms NockvmE2E.Exec.SideGlue16.fixChals_getElem
