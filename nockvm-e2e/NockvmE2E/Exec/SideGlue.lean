/-
 `hglue_J8`.  STARTED ONLY: this file holds the
first list lemma for conjunct 1 (the flat-`vF` readout of `stF`).  `hglue_J8` itself is NOT written.

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue` is complete.
-/
import NockvmE2E.Exec.SideInst
import NockvmE2E.Exec.SideOnlineR

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.SideGlue

/-- reading entry `i` of row `j` out of the flattened rows at offset `3 * (m 0 + .. + m (j-1)) + i` (rows of length `3 * m j`) -/
theorem flatMap_getD : ∀ (rows : List (List ℕ)) (m : ℕ → ℕ),
    (∀ j (h : j < rows.length), rows[j].length = 3 * m j) →
    ∀ j (h : j < rows.length) i, i < 3 * m j →
      (rows.flatMap id).getD (3 * ((List.range j).map m).sum + i) 0 = rows[j].getD i 0
  | [], _, _, j, h, _, _ => absurd h (by simp)
  | r :: rs, m, hlen, 0, h, i, hi => by
      have h0 : r.length = 3 * m 0 := hlen 0 h
      simp only [List.range_zero, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.zero_add, List.flatMap_cons, id]
      rw [List.getD_append _ _ _ _ (by omega)]
      rfl
  | r :: rs, m, hlen, j + 1, h, i, hi => by
      have h0 : r.length = 3 * m 0 := hlen 0 (by simp)
      have hrs : ∀ j' (h' : j' < rs.length), rs[j'].length = 3 * (fun x => m (x + 1)) j' :=
        fun j' h' => hlen (j' + 1) (by simpa using h')
      have ih := flatMap_getD rs (fun x => m (x + 1)) hrs j (by simpa using h) i (by simpa using hi)
      have hs : ((List.range (j + 1)).map m).sum = m 0 + ((List.range j).map (fun x => m (x + 1))).sum := by
        rw [List.range_succ_eq_map]; simp [List.map_map, Function.comp_def]
      rw [hs]
      simp only [List.flatMap_cons, id]
      have : 3 * (m 0 + ((List.range j).map (fun x => m (x + 1))).sum) + i
          = r.length + (3 * ((List.range j).map (fun x => m (x + 1))).sum + i) := by omega
      rw [this, List.getD_append_right _ _ _ _ (by omega)]
      simpa using ih

open NockvmE2E.Exec.SideInst NockvmE2E.Exec in
/-- a canonical `K3` round-trips through its `ZMod p` limb encoding used by `stF`/`decSX` -/
theorem k3_rt (x : VF.K3) (h : VL.canon3 x) :
    VF.K3.ofLimbs (List.ofFn fun c : Fin 3 => ((((VF.K3.limbs x).getD c.1 0 : ℕ) : ZMod NockvmE2E.Exec.p)).val) = x := by
  obtain ⟨c0, c1, c2⟩ := x
  obtain ⟨h0, h1, h2⟩ := h
  simp only [VL.canon] at h0 h1 h2
  have e : ∀ a : UInt64, a.toNat < NockvmE2E.Exec.p →
      UInt64.ofNat (((a.toNat : ℕ) : ZMod NockvmE2E.Exec.p)).val = a := by
    intro a ha
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt ha]
    simp
  simp [VF.K3.ofLimbs, VF.K3.limbs, List.ofFn, Fin.foldr, Fin.foldr.loop]
  exact ⟨e _ h0, e _ h1, e _ h2⟩

open NockvmE2E.Exec.SideInst NockvmE2E.Exec in
/-- reading limb `c` of entry `o` of a flattened `K3` row -/
theorem row_getD (a : Array VF.K3) (o c : ℕ) (ho : o < a.size) (hc : c < 3) :
    (a.toList.flatMap VF.K3.limbs).getD (3 * o + c) 0 = (VF.K3.limbs a[o]).getD c 0 := by
  have h := flatMap_getD (a.toList.map VF.K3.limbs) (fun _ => 1)
    (by intro j hj; simp [VF.K3.limbs]) o (by simpa using ho) c (by omega)
  simp only [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul, Nat.mul_one] at h
  have e : (a.toList.map VF.K3.limbs).flatMap id = a.toList.flatMap VF.K3.limbs := by
    simp [List.flatMap_map]
  rw [e] at h
  rw [h]
  simp

open NockvmE2E.Exec.SideInst NockvmE2E.Exec NockvmE2E.Exec.V in
/-- **conjunct 1, the statement readout**: `decSX (stF ctx (flat vF)) = ⟨[], ctx, vF⟩` -/
theorem decSX_stF (XI : ExecInst) (ctx : List ℕ) (vF : Array (Array VF.K3))
    (hctx : ctx.length ≤ 23) (hb : ∀ x ∈ ctx, x < NockvmE2E.Exec.p)
    (hF : vF.size = (fixCols XI).size)
    (hs : ∀ j (h : j < vF.size), vF[j].size = fixLen XI (fixCols XI)[j]!)
    (hcan : ∀ j (h : j < vF.size) o (h2 : o < vF[j].size), VL.canon3 vF[j][o])
    (hr : ∀ j (h : j < vF.size), fixLen XI (fixCols XI)[j]! ≤ max XI.r 1) :
    decSX XI (stF XI ctx (vF.toList.flatMap (fun a => a.toList.flatMap VF.K3.limbs))) = ⟨[], ctx, vF⟩ := by
  have hrows : ∀ j (h : j < (vF.toList.map (fun a : Array VF.K3 => a.toList.flatMap VF.K3.limbs)).length),
      (vF.toList.map (fun a : Array VF.K3 => a.toList.flatMap VF.K3.limbs))[j].length = 3 * fixLen XI (fixCols XI)[j]! := by
    intro j hj
    have hj' : j < vF.size := by simpa using hj
    simp only [List.getElem_map, Array.getElem_toList]
    have : ∀ (a : Array VF.K3), (a.toList.flatMap VF.K3.limbs).length = 3 * a.size := by
      intro a
      rw [List.length_flatMap]; simp [VF.K3.limbs]
      induction a.toList <;> simp_all [Nat.mul_comm]
    rw [this, hs j hj']
  have hflat : vF.toList.flatMap (fun a => a.toList.flatMap VF.K3.limbs)
      = (vF.toList.map (fun a => a.toList.flatMap VF.K3.limbs)).flatMap id := by
    simp [List.flatMap_map]
  show (⟨[], decCtx (encCtx ctx), _⟩ : SideStmt) = _
  rw [decCtx_encCtx ctx hctx hb]
  congr 1
  apply Array.ext
  · simp [hF]
  · intro j h1 h2
    have hj : j < vF.size := h2
    simp only [Array.getElem_ofFn, Array.size_extract, Array.size_ofFn]
    apply Array.ext
    · simp [Array.size_extract, hs j hj]
      have := hr j hj; omega
    · intro o ho1 ho2
      have ho : o < vF[j].size := ho2
      have hoL : o < fixLen XI (fixCols XI)[j]! := by rw [← hs j hj]; exact ho
      simp only [Array.getElem_extract, Array.getElem_ofFn, Nat.zero_add]
      rw [← k3_rt vF[j][o] (hcan j hj o ho)]
      congr 1
      apply congrArg
      funext c
      unfold stF
      simp only [hoL, if_true]
      congr 2
      have key := flatMap_getD (vF.toList.map (fun a => a.toList.flatMap VF.K3.limbs))
        (fun j => fixLen XI (fixCols XI)[j]!) hrows j (by simpa using hj) (3 * o + c.1) (by have := c.2; omega)
      rw [← hflat] at key
      have e3 : 3 * (offX XI j + o) + c.1 = 3 * ((List.range j).map fun j => fixLen XI (fixCols XI)[j]!).sum + (3 * o + c.1) := by
        unfold offX; omega
      rw [e3, key]
      simp only [List.getElem_map, Array.getElem_toList]
      rw [row_getD _ _ _ ho c.2]

open NockvmE2E.Exec.SideInst NockvmE2E.Exec NockvmE2E.Exec.V in
theorem mem_opList (XI : ExecInst) (j o : ℕ) :
    (j, o) ∈ opList XI ↔ j < (fixCols XI).size ∧ o < fixLen XI (fixCols XI)[j]! := by
  simp [opList]

open NockvmE2E.Exec.SideInst NockvmE2E.Exec NockvmE2E.Exec.V in
/-- the opening list is nonempty as soon as one column has a value -/
theorem opList_length_pos (XI : ExecInst) (j : ℕ) (hj : j < (fixCols XI).size) (h0 : 0 < fixLen XI (fixCols XI)[j]!) :
    0 < (opList XI).length :=
  List.length_pos_of_mem ((mem_opList XI j 0).2 ⟨hj, h0⟩)

open NockvmE2E.Exec.SideInst NockvmE2E.Exec NockvmE2E.Exec.V in
/-- `hC1` of `exec_e2e_J8V'''` for `opIdxX` -/
theorem hC1X (XI : ExecInst) (j : ℕ) (hj : j < (fixCols XI).size) (h0 : 0 < fixLen XI (fixCols XI)[j]!) :
    ∀ j o, j < (fixCols XI).size → o < fixLen XI (fixCols XI)[j]! → ∃ i, opIdxX XI i = (j, o) := by
  intro j' o hj' ho
  have hm := (mem_opList XI j' o).2 ⟨hj', ho⟩
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hm
  have hpos := opList_length_pos XI j hj h0
  refine ⟨⟨i, by unfold mSX; omega⟩, ?_⟩
  unfold opIdxX
  simp [hie.symm, hi]

open NockvmE2E.Exec.SideInst NockvmE2E.Exec NockvmE2E.Exec.V in
/-- `hcol` of `exec_e2e_J8V'''` for `opIdxX` (no side condition: `opIdxX` is `[]!`, and `default.1 = 0` needs `0 < size`, so we assume it for the
out-of-range case only through `hF`) -/
theorem hcolX (XI : ExecInst) (hF : 0 < (fixCols XI).size) (i : Fin (mSX XI + 1)) :
    (opIdxX XI i).1 < (fixCols XI).size := by
  unfold opIdxX
  by_cases h : i.1 < (opList XI).length
  · have hm := List.getElem_mem h
    rw [getElem!_pos (opList XI) i.1 h]
    exact ((mem_opList XI _ _).1 hm).1
  · simp [getElem!_neg, h]; exact hF

end NockvmE2E.Exec.SideGlue

#print axioms NockvmE2E.Exec.SideGlue.flatMap_getD
#print axioms NockvmE2E.Exec.SideGlue.hC1X
#print axioms NockvmE2E.Exec.SideGlue.hcolX
#print axioms NockvmE2E.Exec.SideGlue.row_getD
#print axioms NockvmE2E.Exec.SideGlue.decSX_stF
#print axioms NockvmE2E.Exec.SideGlue.k3_rt

open NockvmE2E.Exec.V NockvmE2E.Exec in
/-- shape and canonicity facts that an accepting `verifyFix'` run guarantees -/
theorem verifyFix'_shape (vk : VK) (Hf : HFn) (FSf : FSFn) (z ctx : List Nat) (zeta : VF.K3) (πF : FixProof)
    (h : verifyFix' vk Hf FSf z ctx zeta πF = .ok ()) :
    πF.vF.size = vk.cols.size ∧ (∀ j, j < vk.cols.size → πF.vF[j]!.size = fixLen vk.X vk.cols[j]!) ∧
      (πF.vF.all (·.all k3Ok) = true) ∧ ctx.all VF.based = true := by
  unfold verifyFix' at h
  simp only [bind_unit_ok, ckE_ok] at h
  obtain ⟨h1, h2, _⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h1 h2
  exact ⟨h1.1.1.1.1.1.1, fun j hj => h1.1.1.1.1.1.2 j hj, h2.1.1.1.1.1.1, List.all_eq_true.2 h2.2⟩

open NockvmE2E.Exec.V NockvmE2E.Exec in
theorem fixLen_le_max (XI : ExecInst) (c : FixCol) : fixLen XI c ≤ max XI.r 1 := by
  cases c <;> simp [fixLen] <;> omega

open NockvmE2E.Exec in
theorem PN_eq_p : VF.PN = NockvmE2E.Exec.p := by
  unfold VF.PN NockvmE2E.Exec.p; norm_num

open NockvmE2E.Exec.V NockvmE2E.Exec NockvmE2E.Exec.SideInst NockvmE2E.Exec.SideOnlineR in
/-- **conjunct 1 of `hglue_J8`**, for an abstract `vk` with `vk.cols = fixCols XI` and the same `fixLen` -/
theorem conj1_of_FixFailR (XI : ExecInst) (vk : VK) (Hf : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof)
    (hc : vk.cols = fixCols XI) (hfl : ∀ c, fixLen vk.X c = fixLen XI c)
    (h : FixFailR XI vk Hf FS FSf z π πF) :
    decSX XI (stF XI (fixCtx π (zetaOf XI FS z π)) (πF.vF.toList.flatMap (fun a => a.toList.flatMap VF.K3.limbs))) =
      ⟨[], fixCtx π (zetaOf XI FS z π), πF.vF⟩ := by
  obtain ⟨hF, hs, hcan, hctx⟩ := verifyFix'_shape vk Hf FSf z _ _ πF h.1.1
  rw [hc] at hF hs
  have hlen := h.roots_len
  apply NockvmE2E.Exec.SideGlue.decSX_stF
  · unfold fixCtx
    rw [List.length_append]
    have h1 : ((π.roots.extract 0 4).toList.flatMap id).length ≤ 20 := by
      rw [List.length_flatMap]
      have : ∀ r ∈ (π.roots.extract 0 4).toList, (id r).length = 5 := fun r hr => hlen r (by
        obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hr)
        simp only [Array.getElem_extract]
        exact Array.getElem_mem _)
      rw [List.map_congr_left this]
      simp [Array.size_extract]
      omega
    have h2 : (VF.K3.limbs (zetaOf XI FS z π)).length = 3 := rfl
    omega
  · intro x hx; rw [← PN_eq_p]; have := List.all_eq_true.1 hctx x hx; simpa [VF.based] using this
  · exact hF
  · intro j hj; have := hs j (by omega); rw [← hfl]; simpa [getElem!_pos, hj] using this
  · intro j hj o ho
    have := (Array.all_eq_true_iff_forall_mem.1 hcan) _ (Array.getElem_mem hj)
    exact k3Ok_canon3 _ ((Array.all_eq_true_iff_forall_mem.1 this) _ (Array.getElem_mem ho))
  · intro j hj; exact fixLen_le_max _ _

#print axioms verifyFix'_shape
#print axioms conj1_of_FixFailR
