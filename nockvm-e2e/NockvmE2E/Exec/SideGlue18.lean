/-
 conjunct 5 glue lemmas (openings, roots, local check).

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue18` is complete.
-/
import NockvmE2E.Exec.SideGlue16
import NockvmE2E.Exec.SideGlue14

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideGlue18
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Merkle NockvmE2E.Exec.SideInst
  NockvmE2E.Merkle.Fri NockvmE2E.Exec.SF NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.DomIdx NockvmE2E.Exec.E2EFri
  NockvmE2E.Exec.SideGlue9 NockvmE2E.FriPort NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Merkle.RapFriQ NockvmE2E.Exec.SideGlue13
  NockvmE2E.Exec.E2EResid NockvmE2E.Exec.Inst NockvmE2E.Exec.Emb NockvmE2E.Exec.SideGlue NockvmE2E.Exec.SideGlue11 NockvmE2E.Exec.SideGlue12 NockvmE2E.Exec.SideGlue14 NockvmE2E.FriPort.Batched

section Side
variable {n k : ℕ} {ω : SmoothCosetFftDomain n KC} (s : Fin (k + 1) → ℕ+) (l : ℕ) (L : Fri.FriLeaves (ω := ω) s)
  [SampleableType KC] [Inhabited KC] [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (XI : ExecInst) {Statement Salt : Type} (decZ : List ℕ → Statement × Salt) (encZ : Statement × Salt → List ℕ)

/-- the FRI-tree opening of the side proof, read off the adapted proof of `verifyFix'` (tree 0's root is the VK root there, a dummy in `fixAdaptD`) -/
theorem openAllS_eq (vk : VK) (hk : vk.X.k = XI.k) (πF : FixProof) (hr : XI.k ≤ πF.roots.size) :
    openAllS s l L XI πF = openAllOf _ ((flatTrees XI (fixPa vk πF)).drop 4) := by
  unfold openAllS flatTrees
  suffices hl : List.drop 4 (List.map (ftree XI (fixAdaptD XI πF)) (List.range (4 + XI.k))) =
      List.drop 4 (List.map (ftree XI (fixPa vk πF)) (List.range (4 + XI.k))) by rw [hl]
  rw [← List.map_drop, ← List.map_drop]
  refine List.map_congr_left (fun j hj => ?_)
  have hj4 : 4 ≤ j ∧ j < 4 + XI.k := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hj
    simp [List.getElem_drop] at hi ⊢
    omega
  obtain ⟨w, rfl⟩ : ∃ w, j = 4 + w := ⟨j - 4, by omega⟩
  refine ftree_congr _ _ _ _ rfl ?_ ?_ ?_
  · show _ = _
    unfold fixAdaptD fixPa
    rw [hk]
  · show _ = _
    unfold fixAdaptD fixPa
    rw [hk]
  · show (#[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]] ++ πF.roots)[4 + w]! =
      (#[vk.root, [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]] ++ πF.roots)[4 + w]!
    rw [append_getElem _ _ _ rfl (by omega), append_getElem _ _ _ rfl (by omega)]

/-- the roots (as digests) and the opening of the compiled side path -/
theorem pathRoots_side {Op : Type} [Finite Op] [DecidableEq Op] (hk : XI.k = k) (ω' : Op)
    (gk : (kk : Key (SStmt XI × (Statement × Salt)) PUnit (compiledRoundsK DgJ8 Op (SMSg s l L))) → kk.Challenge)
    (z0 : Statement × Salt) (ctx : List ℕ) (πF : FixProof) (hr : πF.roots.size = k) :
    pathRootsK DgJ8 Op (SMSg s l L)
      (pathOf (stF XI ctx (((fixMsgs XI.k ctx πF.vF πF.roots πF.pfinal).toList.drop 1).headD []), z0) _ gk
        (decMsgs _ (mDecs dgOf (SMSg s l L) (dsS s l L) ω') ((fixMsgs XI.k ctx πF.vF πF.roots πF.pfinal).toList.drop 1))) =
      (πF.roots.toList.map dgOf, ω') := by
  subst hk
  have h := pathRootsK_embed dgOf (stF XI ctx (((fixMsgs XI.k ctx πF.vF πF.roots πF.pfinal).toList.drop 1).headD []), z0)
    (SMSg s l L) (dsS s l L) ω' ((fixMsgs XI.k ctx πF.vF πF.roots πF.pfinal).toList.drop 1) gk
  have hsz : (fixMsgs XI.k ctx πF.vF πF.roots πF.pfinal).size = XI.k + 4 := by
    simp [fixMsgs, Array.size_extract]
    omega
  have hlen : ((fixMsgs XI.k ctx πF.vF πF.roots πF.pfinal).toList.drop 1).length = XI.k + 3 := by
    simp [hsz]
  rw [embedMsgs] at h
  rw [h, SideGlue15.merkleMsgs_SMSg s l L dgOf _ (by omega)]
  congr 2
  have : πF.roots.extract 0 XI.k = πF.roots := by
    rw [Array.extract_eq_self_iff]; omega
  simp [fixMsgs, this, List.drop_append, List.take_append, hr]

/-- the query positions of an accepting `verifyFix'` are the reduced FS query challenge -/
theorem verifyFix'_pos (vk : VK) (Hf : HFn) (FSf : FSFn) (z ctx : List Nat) (zeta : VF.K3) (πF : FixProof)
    (h : verifyFix' vk Hf FSf z ctx zeta πF = .ok ()) :
    πF.pos = ((fixChals vk FSf z ctx πF)[3 + vk.X.k]!).toArray.map (· % 2 ^ vk.X.nD) := by
  unfold verifyFix' at h
  simp only [bind_unit_ok, forM_ok, ckE_ok, List.mem_range] at h
  obtain ⟨_, _, _, _, hp, _⟩ := h
  simpa [fixChals, fixMsgs] using hp

/-- the sizes of an accepting `verifyFix'` -/
theorem verifyFix'_sizes (vk : VK) (Hf : HFn) (FSf : FSFn) (z ctx : List Nat) (zeta : VF.K3) (πF : FixProof)
    (h : verifyFix' vk Hf FSf z ctx zeta πF = .ok ()) :
    πF.pfinal.size = vk.X.d ∧ πF.pos.size = vk.X.l ∧ πF.roots.size = vk.X.k ∧ (∀ x ∈ πF.pfinal, canon3 x) := by
  unfold verifyFix' at h
  simp only [bind_unit_ok, forM_ok, ckE_ok, List.mem_range] at h
  obtain ⟨h1, h2, _⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h1 h2
  refine ⟨h1.1.1.1.1.2, h1.1.1.1.2, h1.1.1.2, fun x hx => ?_⟩
  exact k3Ok_canon3 _ ((Array.all_eq_true_iff_forall_mem.1 h2.1.1.1.1.1.2) x hx)

/-- `pw` of a canonical base is canonical -/
theorem canon3_pw (cs : VF.K3) (h : canon3 cs) (i : ℕ) : canon3 (pw cs VF.K3.one i) := by
  induction i with
  | zero => exact canon3_one
  | succ i ih => rw [pw_succ]; exact canon3_mul _ _

/-- the claimed values of an accepting `verifyFix'` are canonical -/
theorem vF_canon (XI : ExecInst) (vk : VK) (Hf : HFn) (FSf : FSFn) (z ctx : List Nat) (zeta : VF.K3) (πF : FixProof)
    (hc : vk.cols = fixCols XI) (hX : vk.X = eraseX XI)
    (h : verifyFix' vk Hf FSf z ctx zeta πF = .ok ()) :
    ∀ j o', j < (fixCols XI).size → o' < fixLen XI (fixCols XI)[j]! → canon3 (πF.vF[j]!)[o']! := by
  obtain ⟨hF, hs, hcan, hctx⟩ := verifyFix'_shape vk Hf FSf z ctx zeta πF h
  rw [hc] at hF hs
  intro j o' hj ho
  have := (Array.all_eq_true_iff_forall_mem.1 hcan) _ (Array.getElem_mem (by omega : j < πF.vF.size))
  have h2 := (Array.all_eq_true_iff_forall_mem.1 this)
  have hlen := hs j (by omega)
  rw [getElem!_pos πF.vF j (by omega)]
  have hfl : fixLen vk.X (fixCols XI)[j]! = fixLen XI (fixCols XI)[j]! := by rw [hX]; rfl
  rw [hfl, getElem!_pos πF.vF j (by omega)] at hlen
  rw [getElem!_pos _ o' (by omega)]
  exact k3Ok_canon3 _ (h2 _ (Array.getElem_mem _))

theorem fixLen_pos (XI : ExecInst) (c : FixCol) (hr : 0 < XI.r) : 0 < fixLen XI c := by
  cases c <;> simp [fixLen] <;> omega

theorem fixCols_size_pos (XI : ExecInst) : 0 < (fixCols XI).size := by
  unfold fixCols
  simp

/-- `VKcoll` negated: every selected tree-0 leaf is honest -/
theorem hhon_of_not_VKcoll (XI : ExecInst) (vk : VK) (Hf : HFn) (FSf : FSFn) (z ctx : List Nat) (zeta : VF.K3) (πF : FixProof)
    (h : verifyFix' vk Hf FSf z ctx zeta πF = .ok ()) (hnc : ¬ VKcoll XI vk Hf πF) :
    ∀ r, r < (treeSel vk.X vk.cols.size 0 πF.pos).size →
      (πF.vals[0]!)[r]! = honestLeaf XI vk.cols.size (2 ^ (vk.X.nD - 1)) (treeSel vk.X vk.cols.size 0 πF.pos)[r]! := by
  intro r hr
  by_contra hne
  apply hnc
  refine ⟨?_, r, hr, hne⟩
  have := verifyFix'_trees vk Hf FSf z ctx zeta πF h 0 (by omega)
  exact this

section W0
variable {S : Type}

set_option maxHeartbeats 2000000 in
/-- **`hW0` for the side proof**: the initial oracle of the combined statement at a queried domain point is the verifier's word 0 -/
theorem hW0_side (XI : ExecInst) (hg : setupGates XI = true) (hn : XI.nD ≤ 32) (L' : DomLink XI hn)
    (hshift : XI.dShift = 7) (hgen : psiV XI.dGen = ((zeta XI.nD : KCˣ) : KC))
    (vk : VK) (Hf : HFn) (FSf : FSFn) (z ctx : List Nat) (zeta : VF.K3) (π : FlatProof) (πF : FixProof)
    (hc : vk.cols = fixCols XI) (hX : vk.X = eraseX XI) (hctx : ctx = fixCtx π zeta)
    (hv : verifyFix' vk Hf FSf z ctx zeta πF = .ok ()) (hnc : ¬ VKcoll XI vk Hf πF)
    (G : CoreDefinitions.Generator S (Fin (mSX XI + 1)) KC) (csS : S) (cs : VF.K3)
    (hG : ∀ i : Fin (mSX XI + 1), G csS i = toKV cs ^ (i : ℕ))
    (hcsdef : cs = fixCs vk FSf z ctx πF) (hcan_cs : canon3 cs) (j : Fin XI.l) (g : ℕ) (hgj : Rd XI.nD (πF.pos[j.1]!) 0 g) :
    ∃ y : ((smoothDomain XI.nD hn).subdomain 0).toFinset, y.val = Yp (homV.ψ XI.dShift) (homV.ψ XI.dGen) 0 g ∧
      initialOracle (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+))
        (combinedStmt (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) (mSX XI) G csS
          (stmtOf (SideCfg.mk (m := mSX XI) XI (opIdxX XI) (ptKX XI)) hn ⟨[], ctx, πF.vF⟩)) y =
        homV.φ (fixWord0 vk FSf z ctx zeta πF g) := by
  have hg1 : g < 2 ^ XI.nD := by simpa using hgj.1
  have hnD : 0 < XI.nD := by have := nD_of_gates XI hg; omega
  let u : Fin (2 ^ (XI.nD - 0)) := ⟨g, by simpa using hg1⟩
  have hy : ((((smoothDomain XI.nD hn).subdomain 0).equivToFinset u).val) = Yp (homV.ψ XI.dShift) (homV.ψ XI.dGen) 0 g := by
    show _ = Yp (psiV XI.dShift) (psiV XI.dGen) 0 g
    rw [psiV_shift XI hshift, hgen]
    exact pt_val XI.nD hn 0 0 hnD rfl u
  have hω : smoothDomain XI.nD hn ⟨g, hg1⟩ = homV.ψ XI.dShift * homV.ψ XI.dGen ^ g := by
    show _ = psiV XI.dShift * psiV XI.dGen ^ g
    rw [psiV_shift XI hshift, hgen, Inst.smoothDomain_apply]
  have hy2 : ((((smoothDomain XI.nD hn).subdomain 0).equivToFinset u).val) = smoothDomain XI.nD hn ⟨g, hg1⟩ := by
    rw [hy, hω]; simp [Yp]
  refine ⟨((smoothDomain XI.nD hn).subdomain 0).equivToFinset u, hy, ?_⟩
  obtain ⟨hlim1, hlim2, hlim3, hlim4, hlim5, hlim6⟩ := verifyFix'_limits vk Hf FSf z ctx zeta πF hv
  have hvals := fixPa_vals_mem vk πF hlim4
  obtain ⟨hF, hs, hcanF, hctxb⟩ := verifyFix'_shape vk Hf FSf z ctx zeta πF hv
  have hζ : canon3 zeta := by
    have hb : ∀ x ∈ VF.K3.limbs zeta, x < NockvmE2E.Exec.p := by
      intro x hx
      rw [← PN_eq_p]
      have := List.all_eq_true.1 hctxb x (by rw [hctx]; unfold fixCtx; exact List.mem_append_right _ hx)
      simpa [VF.based] using this
    have := canon3_ofLimbs _ hb
    rwa [SideInst.ofLimbs_limbs] at this
  have hppt := canon_ppt_of_gates hg
  have hr := r_ge_two_of_gates hg
  have hpos := opList_length_pos XI 0 (fixCols_size_pos XI) (by
    have := fixLen_pos XI (fixCols XI)[0]! (by omega); exact this)
  have hfl : ∀ j, j < (fixCols XI).size → fixLen XI (fixCols XI)[j]! ≤ XI.r + 2 := fun j _ => by
    have := fixLen_le_max XI (fixCols XI)[j]!; omega
  have hpts : openPts vk.X zeta = openPts XI (VF.K3.ofLimbs (ctx.drop (ctx.length - 3))) := by
    rw [hctx, ctx_tail, hX]; rfl
  have hhon := hhon_of_not_VKcoll XI vk Hf FSf z ctx zeta πF hv hnc
  have hn1 : 1 ≤ vk.X.nD := by rw [hX]; exact hnD
  have hF0 : 0 < vk.cols.size := by rw [hc]; exact fixCols_size_pos XI
  have hmem : πF.pos[j.1]! ∈ πF.pos.toList := by
    have hs' : j.1 < πF.pos.size := by
      rw [(verifyFix'_sizes vk Hf FSf z ctx zeta πF hv).2.1, hX]; exact j.2
    rw [getElem!_pos πF.pos j.1 hs']; simp
  have hbase : ∀ c, c < (fixCols XI).size → homV.ψ (fixBaseAt vk πF c g) = honestWord XI (fixCols XI)[c]! ⟨g, hg1⟩ := by
    intro c hcc
    have h1 := baseAt_honest XI vk.X (by rw [hX]; rfl) hn1 vk.cols.size hF0 πF.pos (πF.vals[0]!) hhon c g (by rw [hc]; exact hcc)
      (by rw [hX]; exact hg1) (πF.pos[j.1]!) hmem (by
        have := hgj.2
        rw [hX]; simpa using this.symm)
    show psiV (fixBaseAt vk πF c g) = psiV (specWord XI (fixCols XI)[c]! g)
    congr 1
    have e0 : (fixPa vk πF).vals[0]! = πF.vals[0]! := by unfold fixPa; simp
    have e1 : (fixSels vk πF)[0]! = treeSel vk.X vk.cols.size 0 πF.pos := by unfold fixSels; simp
    unfold fixBaseAt
    rw [e0, e1]
    exact h1
  have hcpos : ∀ p ∈ opList XI, p.1 < (fixCols XI).size ∧ p.2 < fixLen XI (fixCols XI)[p.1]! := fun p hp => by
    have := (mem_opList XI p.1 p.2).1 hp; exact this
  have hops_eq : (fixOps vk.X vk.cols cs πF.vF).toList = (fixOps XI (fixCols XI) cs πF.vF).toList := by
    rw [hc, hX]
    exact (fixOps_toList (eraseX XI) cs πF.vF).trans (fixOps_toList XI cs πF.vF).symm
  have hops_can : ∀ o ∈ (fixOps XI (fixCols XI) cs πF.vF).toList, homV.C o.2.2.1 ∧ homV.C o.2.2.2 ∧ homV.Cg (fixBaseAt vk πF o.1 g) := by
    intro o ho
    rw [fixOps_toList] at ho
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
    obtain ⟨hp1, hp2⟩ := hcpos p hp
    refine ⟨canon3_pw cs hcan_cs _, vF_canon XI vk Hf FSf z ctx zeta πF hc hX hv p.1 p.2 hp1 hp2, ?_⟩
    show canon (fixBaseAt vk πF p.1 g)
    unfold fixBaseAt
    exact canon_ofNat _ (arr_get_lt (a := (fixPa vk πF).vals) hvals 0 _)
  have hpts_can : ∀ q, q < XI.r + 2 → homV.C (openPts vk.X zeta)[q]! := fun q _ => by
    rw [hX]
    show canon3 (openPts XI zeta)[q]!
    exact E2EW0.openPts_can XI hppt zeta hζ q
  have hops := ops_forall2 XI hpos ⟨[], ctx, πF.vF⟩ cs πF.vF rfl hfl (openPts vk.X zeta) hpts (fixBaseAt vk πF) g ⟨g, hg1⟩ rfl
    (fun c hc' => hbase c hc')
  have key := initialOracle_side (SideCfg.mk (m := mSX XI) XI (opIdxX XI) (ptKX XI)) hn ⟨[], ctx, πF.vF⟩ G csS (toKV cs) hG
    (openPts vk.X zeta) (fixOps XI (fixCols XI) cs πF.vF).toList (fixBaseAt vk πF) ⟨g, hg1⟩ _ hy2 hω hops hops_can hpts_can
    (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) (by simp [finRangeTo])
  refine key.trans ?_
  unfold fixWord0
  rw [← hcsdef] at *
  rw [V.deepWord_eq, hops_eq]
  rw [hX]
  rfl
end W0

end Side

end NockvmE2E.Exec.SideGlue18
