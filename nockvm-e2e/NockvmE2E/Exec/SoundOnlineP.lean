/-
  NockvmE2E/Exec/SoundOnlineP.lean   (proof-only, kernel)

  Port of SoundOnline.lean's split lemma to the primed executables of VKp.lean (side hash `Hf` explicit):
  `OnlineOk'`, `FixFail'`, `setup'_some`, `online_to_flat'`, `verifyOnline_split'`.  Same proofs, no random oracle, no assumption on `H`, `Hf`, `FS`, `FSf`.
-/
import NockvmE2E.Exec.SoundOnline
import NockvmE2E.Exec.VKp

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec.VF NockvmE2E.Exec.VL

/-- `verifyOnlineE` accepts, as a proposition (transcribed from `VerifyOnline.lean`; same style as `FlatOk`) -/
def OnlineOk' (vk : VK) (H Hf : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) : Prop :=
  let XI := vk.X
  let nB := 4
  let k := XI.k
  let ncq := XI.nc + XI.nq
  let lay := fixLayout XI vk.cols
  allCanonOnline z π = true ∧
  (π.roots.size == nB + k && π.vals.size == nB + k && π.sibs.size == nB + k) = true ∧
  (π.vT.size == XI.nc && π.vQ.size == XI.nq && π.pfinal.size == XI.d && π.pos.size == XI.l) = true ∧
  (∀ c ∈ List.range XI.nc, (π.vT[c]!.size == vTLen XI c) = true) ∧
  (π.pos.all (· < 2 ^ XI.nD)) = true ∧
  let pfEnc := π.pfinal.toList.flatMap VF.K3.limbs
  let msgs : Array (List Nat) :=
    #[[], π.roots[0]!, π.roots[1]!, π.roots[2]!, π.roots[3]!, deepMsg π.vT π.vQ, [], []] ++ π.roots.extract nB (nB + k) ++ #[pfEnc]
  let nlOf := roundNl XI
  let chals : Array (List Nat) := (Array.range msgs.size).map fun i =>
    if nlOf i == 0 then [] else FS (z :: (msgs.extract 0 (i + 1)).toList) (nlOf i)
  (chals.all (·.all based)) = true ∧
  let coins0 := k3s chals[1]! XI.nCoins[0]!
  let coins1 := k3s chals[2]! XI.nCoins[1]!
  let alpha := VF.K3.ofLimbs chals[3]!
  let zeta := VF.K3.ofLimbs chals[4]!
  let cs := VF.K3.ofLimbs chals[6]!
  let alphas : Array VF.K3 := (Array.range (k + 1)).map fun w => VF.K3.ofLimbs chals[7 + w]!
  let xs : Array Nat := chals[8 + k]!.toArray.map (· % 2 ^ XI.nD)
  (π.pos == xs) = true ∧
  verifyFix' vk Hf FSf z (fixCtx π zeta) zeta πF = .ok () ∧
  let vF := πF.vF
  let half0 := 2 ^ (XI.nD - 1)
  let (W, rank) := blockLayout XI
  let sels : Array (Array Nat) := (Array.range (nB + k)).map fun j => treeSel XI (W.getD j 0) j π.pos
  (∀ j ∈ List.range (nB + k), treeCheck XI H π W half0 sels j = .ok ()) ∧
  let slots : Array VF.K3 := XI.derived.toList.foldl (fun (slots : Array VF.K3) (be : Nat × Nat) => slots.push (VF.K3.pow slots[be.1]! be.2)) (coins0 ++ coins1)
  let zh := (vF[lay.zh]!)[0]!
  let curNxt := curNxtOn XI π vF lay
  (∀ c ∈ XI.pubOf.toList, (decide (c < XI.nc) && XI.colKind[c]! == 2) = true ∧ ((π.vT[c]!)[0]!).isBase = true) ∧
  let pub : Array G := XI.pubOf.map fun c => ((π.vT[c]!)[0]!).c0
  (!zh.isZero) = true ∧
  let lhs := lhsOn XI vF lay curNxt pub slots alpha
  let zN := VF.K3.pow zeta XI.hN
  let qsum := (List.range XI.nq).foldl
    (fun qs j => VF.K3.add qs (VF.K3.mul (VF.K3.mul (VF.K3.pow VF.K3.gen (j % 3)) (VF.K3.pow zN (j / 3))) π.vQ[j]!)) VF.K3.zero
  (lhs == VF.K3.mul zh qsum) = true ∧
  let pts := openPts XI zeta
  let dN := 2 ^ XI.nD
  (∀ pt ∈ pts.toList, (pt.pow dN != VF.K3.ofG (VF.pow XI.dShift dN)) = true) ∧
  XI.pubCheck slots pub = true ∧
  (∀ c ∈ List.range XI.nc, (XI.colKind[c]! != 1 || (List.range XI.r).all (fun o => (π.vT[c]!)[o]! == (vF[lay.pre[c]!]!)[o]!)) = true) ∧
  let ops := openingList XI cs π.vT π.vQ
  let baseAt (c idx : Nat) : G :=
    let b := XI.blockOf[c]!
    let leafPos := (idx % half0) * 2 * W[b]! + (idx / half0) * W[b]! + rank[c]!
    UInt64.ofNat (π.vals[b]!)[lb sels[b]! leafPos]!
  let word0 := deepWord XI pts ops baseAt
  ∀ q ∈ π.pos.toList,
    let g0 := q % half0
    ∃ r, friSteps XI π.vals sels alphas q (List.range' 1 k)
      (foldK3 (word0 g0) (word0 (g0 + half0)) (yAt XI 0 g0) alphas[0]!) g0 = .ok r ∧
    (r.1 == VF.K3.horner π.pfinal (VF.K3.ofG (yAt XI (k + 1) r.2))) = true

theorem verifyOnlineE'_ok_iff (vk : VK) (H Hf : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) :
    verifyOnlineE' vk H Hf FS FSf z π πF = .ok () ↔ OnlineOk' vk H Hf FS FSf z π πF := by
  unfold verifyOnlineE' OnlineOk'
  simp only [bind_unit_ok, forM_ok, ckE_ok]
  simp only [bind_ok, ckE_ok]
  exact Iff.rfl



/-- the side proof's verifier accepts, yet a claimed value `vF[j][o]` differs from the true evaluation of fixed column `j` at opening point `o`
(`pts[o] = openPts X0 ζ [o]`, `ζ` the Fiat-Shamir challenge of the main proof) -/
def FixFail' (X0 : ExecInst) (vk : VK) (Hf : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) : Prop :=
  verifyFix' vk Hf FSf z (fixCtx π (zetaOf X0 FS z π)) (zetaOf X0 FS z π) πF = .ok () ∧
  ∃ j o, j < vk.cols.size ∧ o < fixLen X0 vk.cols[j]! ∧
    (πF.vF[j]!)[o]! ≠ fixTrue X0 vk.cols[j]! ((openPts X0 (zetaOf X0 FS z π))[o]!)


/-- `setup` returns `some vk`: its gates hold, `vk.X` is `X0` with `pre` erased, `vk.cols = fixCols X0` -/
theorem setup'_some {X0 : ExecInst} {Hf : HFn} {vk : VK} (h : setup' X0 Hf = some vk) :
    setupGates X0 = true ∧ vk.X = eraseX X0 ∧ vk.cols = fixCols X0 := by
  unfold setup' setupData' mkVKData' at h
  by_cases hg : setupGates X0 = true
  · simp only [hg, Bool.not_true, Bool.false_eq_true, ite_false, Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨hg, rfl, rfl⟩
  · simp only [Bool.not_eq_true] at hg
    simp [hg] at h


theorem online_to_flat' (X0 : ExecInst) (H Hf : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) (vk : VK)
    (hg : setupGates X0 = true) (hX : vk.X = eraseX X0) (hc : vk.cols = fixCols X0)
    (hon : OnlineOk' vk H Hf FS FSf z π πF) (hnf : ¬ FixFail' X0 vk Hf FS FSf z π πF) : FlatOk X0 H FS z π := by
  have hg' := hg
  simp only [setupGates, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range, and_assoc] at hg'
  obtain ⟨gic, gin, gcs, gbs, gps, gnc, gnd, gnq, gr, ghN, gl, gpar, gtab, gblk⟩ := hg'
  unfold OnlineOk' at hon
  simp only [hX, hc] at hon
  simp only [er_nD, er_k, er_nc, er_nq, er_d, er_l, er_r, er_hN, er_colKind, er_blockOf, er_pubOf, er_nCoins, er_derived, er_tabs, er_dShift, er_treeSel, er_blockLayout, er_deepWord, er_openPts, er_openingList, er_roundNl, er_treeCheck, er_vTLen, er_yAt, er_pubCheck, er_fixLayout, er_curNxtOn, er_lhsOn, friSteps_erase] at hon
  obtain ⟨O1, O2, O3, O4, O5, O6, O7, O8, O9, O10, O11, O12, O13, O14, O15, O16⟩ := hon
  have hCh : ChalCan X0 FS z π := chalCan_of_all X0 FS z π O6
  have hζ : canon3 (zetaOf X0 FS z π) := canon3_zetaOf X0 FS z π hCh
  have hver : verifyFix' vk Hf FSf z (fixCtx π (zetaOf X0 FS z π)) (zetaOf X0 FS z π) πF = .ok () := O8
  have hT : ∀ j, j < (fixCols X0).size → ∀ o, o < fixLen X0 (fixCols X0)[j]! →
      (πF.vF[j]!)[o]! = fixTrue X0 (fixCols X0)[j]! ((openPts X0 (zetaOf X0 FS z π))[o]!) := by
    intro j hj o ho
    by_contra hne
    exact hnf ⟨hver, j, o, by rw [hc]; exact hj, by rw [hc]; exact ho, by rw [hc]; exact hne⟩
  obtain ⟨lay, hlay⟩ : ∃ lay, lay = fixLayout X0 (fixCols X0) := ⟨_, rfl⟩
  rw [← hlay] at O11 O12 O15
  have hp0 : (openPts X0 (zetaOf X0 FS z π))[0]! = zetaOf X0 FS z π := by
    rw [openPts_zero X0 _ (by omega), k3_mul_one _ hζ]
  have hp1 : (openPts X0 (zetaOf X0 FS z π))[1]! = VF.K3.smul X0.hGen (zetaOf X0 FS z π) := by
    rw [openPts_one X0 _ (by omega), k3_mul_smul_one _ _ hζ]
  have hzh : (πF.vF[lay.zh]!)[0]! = zhEval X0 (zetaOf X0 FS z π) := by
    obtain ⟨hlt, hcl⟩ := fixLayout_zh X0 (fixCols X0) (fixCols_zh X0)
    rw [← hlay] at hlt hcl
    have := hT _ hlt 0 (by rw [hcl]; simp [fixLen])
    rw [this, hcl]
    simp only [fixTrue, hp0]
  have hpre : ∀ c, c < X0.nc → X0.colKind[c]! = 1 → ∀ o, o < X0.r →
      (πF.vF[lay.pre[c]!]!)[o]! = VF.K3.hornerG X0.pre[c]! ((openPts X0 (zetaOf X0 FS z π))[o]!) := by
    intro c hc hk o ho
    obtain ⟨hlt, hcl⟩ := fixLayout_pre X0 (fixCols X0) c hc (fixCols_pre X0 c hc hk)
    rw [← hlay] at hlt hcl
    have := hT _ hlt o (by rw [hcl]; simpa [fixLen] using ho)
    rw [this, hcl]
    rfl
  have hmult : ∀ t, t < X0.tabs.size → tabHN X0 t < X0.hN →
      (πF.vF[lay.zout[t]!]!)[0]! = zoutEval X0 (tabHN X0 t) (zetaOf X0 FS z π) := by
    intro t ht hl
    obtain ⟨hlt, hcl⟩ := fixLayout_zout X0 (fixCols X0) t ht (fixCols_zout X0 t ht hl)
    rw [← hlay] at hlt hcl
    have := hT _ hlt 0 (by rw [hcl]; simp [fixLen])
    rw [this, hcl]
    simp only [fixTrue, hp0]
  have hcn := curNxt_eq X0 π πF.vF lay (zetaOf X0 FS z π) (fun c hc hk =>
    ⟨by rw [hpre c hc hk 0 (by omega), hp0], by rw [hpre c hc hk 1 (by omega), hp1]⟩)
  rw [hcn] at O12
  rw [lhs_eq X0 πF.vF lay (zetaOf X0 FS z π) _ _ _ _ hmult] at O12
  rw [hzh] at O11 O12
  unfold FlatOk
  refine ⟨?F1, ?F2, ?F3, gpar, O2, O3, O4, gtab, O5, O6, O7, ?F12, O9, O10, O11, O12, O13, O14, gin, ?F20, O16⟩
  · rw [allCanon_split]; simp [gic, O1]
  · simp [gcs, gbs, gps, gnc]
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]; omega
  · intro c hcr
    simpa using gblk c (List.mem_range.mp hcr)
  · intro c hcr
    exact preOpen_transfer X0 π πF.vF lay _ c
      (fun hk o ho => hpre c (List.mem_range.mp hcr) hk o ho) (O15 c hcr)


/-- **The split lemma.**  If `setup X0 H = some vk` and the online verifier accepts (`π`, side proof `πF`), then the flat verifier
accepts `π` on the instance `X0` (the J-8 chain's `AccF`), or the side proof is a `FixFail`: it passes `verifyFix` while one of its claimed
fixed-column values differs from the true evaluation `fixTrue` at the opening point.  Elementary: no random oracle, no assumption on `H`, `FS`, `FSf`. -/
theorem verifyOnline_split' (X0 : ExecInst) (H Hf : HFn) (FS FSf : FSFn) (z : List Nat) (π : FlatProof) (πF : FixProof) (vk : VK)
    (hvk : setup' X0 Hf = some vk) (hon : verifyOnline' vk H Hf FS FSf z π πF = true) :
    verifyFlat X0 H FS z π = true ∨ FixFail' X0 vk Hf FS FSf z π πF := by
  obtain ⟨hg, hX, hc⟩ := setup'_some hvk
  have hE : verifyOnlineE' vk H Hf FS FSf z π πF = .ok () := by
    unfold verifyOnline' at hon
    cases h : verifyOnlineE' vk H Hf FS FSf z π πF with
    | error _ => simp [h] at hon
    | ok u => cases u; rfl
  by_cases hF : FixFail' X0 vk Hf FS FSf z π πF
  · exact Or.inr hF
  · exact Or.inl ((verifyFlat_iff X0 H FS z π).mpr
      (online_to_flat' X0 H Hf FS FSf z π πF vk hg hX hc ((verifyOnlineE'_ok_iff vk H Hf FS FSf z π πF).mp hE) hF))


#print axioms verifyOnline_split'

end NockvmE2E.Exec.V
