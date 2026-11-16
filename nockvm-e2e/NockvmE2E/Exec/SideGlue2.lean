/-
 conjuncts 2-4 of `hglue_J8` (canonicity of the opening points, off-domain, canonicity of `vF` and of the true values), for an abstract `vk`.
`hglue_J8` itself is NOT written (conjunct 5 not started).

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue2` is complete.
-/
import NockvmE2E.Exec.SideGlue

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NockvmE2E.Exec.V NockvmE2E.Exec in
/-- the `OffDom` check of an accepting `verifyFix'` -/
theorem verifyFix'_offdom (vk : VK) (Hf : HFn) (FSf : FSFn) (z ctx : List Nat) (zeta : VF.K3) (πF : FixProof)
    (h : verifyFix' vk Hf FSf z ctx zeta πF = .ok ()) :
    ∀ o < vk.X.r, ((openPts vk.X zeta)[o]!.pow (2 ^ vk.X.nD) != VF.K3.ofG (VF.pow vk.X.dShift (2 ^ vk.X.nD))) = true := by
  unfold verifyFix' at h
  simp only [bind_unit_ok, forM_ok, ckE_ok, List.mem_range] at h
  obtain ⟨_, _, _, _, _, _, hoff, _⟩ := h
  exact hoff

open NockvmE2E.Exec.V NockvmE2E.Exec NockvmE2E.Exec.VL in
theorem canon_ppt_of_gates {XI : ExecInst} (hg : setupGates XI = true) : canon3 XI.ppt := by
  have h1 : instCanon XI = true := by
    simp only [setupGates, Bool.and_eq_true] at hg; tauto
  simp only [instCanon, Bool.and_eq_true, Array.all_eq_true] at h1
  exact k3Ok_canon3 _ h1.1.1.2

open NockvmE2E.Exec.V NockvmE2E.Exec NockvmE2E.Exec.VL in
theorem canon3_fixTrue (XI : ExecInst) (hg : setupGates XI = true) (col : FixCol) (x : VF.K3) :
    canon3 (fixTrue XI col x) := by
  obtain ⟨hS, hpre⟩ := canon_of_gates hg
  cases col with
  | pre c =>
    unfold fixTrue VF.K3.hornerG
    exact canon_hornerG _ _ (hpre c)
  | zh => unfold fixTrue zhEval; exact canon3_multFold _ _ _ (VF.K3.one, XI.hShift) canon3_one
  | zout t => unfold fixTrue zoutEval; exact canon3_multFold _ _ _ (VF.K3.one, _) canon3_one

open NockvmE2E.Exec.V NockvmE2E.Exec NockvmE2E.Exec.VL NockvmE2E.Exec.Inst Domain in
theorem offdom_toKV (XI : ExecInst) (hn : XI.nD ≤ 32) (L : DomLink XI hn) (pt : VF.K3)
    (hv : (pt.pow (2 ^ XI.nD) != VF.K3.ofG (VF.pow XI.dShift (2 ^ XI.nD))) = true) (i : Fin (2 ^ XI.nD)) :
    smoothDomain XI.nD hn i ≠ toKV pt := by
  intro h
  have hne : pt.pow (2 ^ XI.nD) ≠ VF.K3.ofG (VF.pow XI.dShift (2 ^ XI.nD)) := by
    intro he
    have h1 : (pt.pow (2 ^ XI.nD) == VF.K3.ofG (VF.pow XI.dShift (2 ^ XI.nD))) = true := (K3_beq_iff _ _).mpr he
    simp [bne, h1] at hv
  apply hne
  apply toKV_inj _ _ (canon3_pow _ _) (canon3_ofG _ (canon_pow _ _))
  rw [toKV_pow, toKV_ofG, psiV_pow, L.dShift_eq, ← h, smoothDomain_pow]

open NockvmE2E.Exec.V NockvmE2E.Exec in
theorem r_ge_two_of_gates {XI : ExecInst} (hg : setupGates XI = true) : 2 ≤ XI.r := by
  simp only [setupGates, Bool.and_eq_true, decide_eq_true_eq] at hg
  omega

namespace NockvmE2E.Exec.SideGlue
open NockvmE2E.Exec.SideInst NockvmE2E.Exec NockvmE2E.Exec.V in
theorem mem_opList_lt (XI : ExecInst) (e : ℕ × ℕ) (he : e ∈ opList XI) : e.2 < max XI.r 1 := by
  obtain ⟨a, b⟩ := e
  have h1 := (mem_opList XI a b).1 he
  have h2 := fixLen_le_max XI (fixCols XI)[a]!
  have := h1.2
  simp only at *
  omega
end NockvmE2E.Exec.SideGlue

open NockvmE2E.Exec.V NockvmE2E.Exec NockvmE2E.Exec.VL NockvmE2E.Exec.SideInst NockvmE2E.Exec.SideOnlineR NockvmE2E.Exec.Inst Domain in
/-- **conjuncts 2-4 of `hglue_J8`** (for abstract `vk` with `vk.cols = fixCols XI`, `vk.X = eraseX XI`) -/
theorem conj234_of_FixFailR (XI : ExecInst) (hg : setupGates XI = true) (hn : XI.nD ≤ 32) (L : DomLink XI hn)
    (vk : VK) (Hf : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof)
    (hc : vk.cols = fixCols XI) (hX : vk.X = eraseX XI)
    (h : FixFailR XI vk Hf FS FSf z π πF) :
    (∀ j, canon3 (ptKX XI (fixCtx π (zetaOf XI FS z π)) j)) ∧
    (∀ j i, smoothDomain XI.nD hn i ≠ toKV (ptKX XI (fixCtx π (zetaOf XI FS z π)) j)) ∧
    (∀ j o', j < (fixCols XI).size → o' < fixLen XI (fixCols XI)[j]! →
      canon3 (πF.vF[j]!)[o']! ∧ canon3 (fixTrue XI (fixCols XI)[j]! ((openPts XI (zetaOf XI FS z π))[o']!))) := by
  obtain ⟨hF, hs, hcan, hctx⟩ := verifyFix'_shape vk Hf FSf z _ _ πF h.1.1
  have hoff := verifyFix'_offdom vk Hf FSf z _ _ πF h.1.1
  rw [hc] at hF hs
  have hζ : canon3 (zetaOf XI FS z π) := by
    have hb : ∀ x ∈ VF.K3.limbs (zetaOf XI FS z π), x < NockvmE2E.Exec.p := by
      intro x hx
      rw [← PN_eq_p]
      have := List.all_eq_true.1 hctx x (by unfold fixCtx; exact List.mem_append_right _ hx)
      simpa [VF.based] using this
    have := canon3_ofLimbs _ hb
    rwa [ofLimbs_limbs] at this
  have hppt := canon_ppt_of_gates hg
  have hr := r_ge_two_of_gates hg
  have hpt : ∀ j, canon3 (ptKX XI (fixCtx π (zetaOf XI FS z π)) j) := by
    intro j; rw [hC2X]; exact E2EW0.openPts_can XI hppt _ hζ _
  refine ⟨hpt, ?_, ?_⟩
  · intro j i
    rw [hC2X]
    refine offdom_toKV XI hn L _ ?_ i
    have hlt : (opIdxX XI j).2 < XI.r := by
      unfold opIdxX
      by_cases hj : j.1 < (opList XI).length
      · have hm := List.getElem_mem hj
        rw [getElem!_pos (opList XI) j.1 hj]
        have := NockvmE2E.Exec.SideGlue.mem_opList_lt XI _ hm
        omega
      · rw [getElem!_neg (opList XI) j.1 hj]; show 0 < XI.r; omega
    have := hoff _ (by rw [hX]; exact hlt)
    rw [hX] at this
    exact this
  · intro j o' hj ho
    refine ⟨?_, canon3_fixTrue XI hg _ _⟩
    have := (Array.all_eq_true_iff_forall_mem.1 hcan) _ (Array.getElem_mem (by omega : j < πF.vF.size))
    have h2 := (Array.all_eq_true_iff_forall_mem.1 this)
    have hlen := hs j (by omega)
    rw [getElem!_pos πF.vF j (by omega)]
    have hfl : fixLen vk.X (fixCols XI)[j]! = fixLen XI (fixCols XI)[j]! := by rw [hX]; rfl
    rw [hfl, getElem!_pos πF.vF j (by omega)] at hlen
    rw [getElem!_pos _ o' (by omega)]
    exact k3Ok_canon3 _ (h2 _ (Array.getElem_mem _))

open NockvmE2E.Exec.V NockvmE2E.Exec in
/-- the first public message of the side proof (`fixMsgs` slot 1, after dropping the statement slot) is the flat `vF` limb list -/
theorem fixMsgs_headD (k : Nat) (ctx : List Nat) (vF : Array (Array VF.K3)) (roots : Array Dg5) (pfinal : Array VF.K3) :
    ((fixMsgs k ctx vF roots pfinal).toList.drop 1).headD [] = vF.toList.flatMap (fun a => a.toList.flatMap VF.K3.limbs) := by
  simp [fixMsgs]

#print axioms verifyFix'_offdom
#print axioms canon3_fixTrue
#print axioms offdom_toKV
#print axioms conj234_of_FixFailR
#print axioms fixMsgs_headD
