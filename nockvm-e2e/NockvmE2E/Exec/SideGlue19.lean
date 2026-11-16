/-
 conjunct 5, the local check (`local_side`).

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue19` is complete.
-/
import NockvmE2E.Exec.SideGlue18

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideGlue19
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Merkle NockvmE2E.Exec.SideInst
  NockvmE2E.Merkle.Fri NockvmE2E.Exec.SF NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.DomIdx NockvmE2E.Exec.E2EFri
  NockvmE2E.Exec.SideGlue9 NockvmE2E.FriPort NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Merkle.RapFriQ NockvmE2E.Exec.SideGlue13
  NockvmE2E.Exec.E2EResid NockvmE2E.Exec.Inst NockvmE2E.Exec.Emb NockvmE2E.Exec.SideGlue NockvmE2E.Exec.SideGlue11 NockvmE2E.Exec.SideGlue12 NockvmE2E.Exec.SideGlue14 NockvmE2E.Exec.SideGlue18 NockvmE2E.Exec.SideGlue7 NockvmE2E.Exec.SideGlue10 NockvmE2E.FriPort.Batched


/-- the challenge samplers of `pSpec` at `eraseX XI` are those at `XI` (`eraseX` only erases `pre`) -/
instance instSampEraseX [SampleableType KC] [Inhabited KC] (XI : ExecInst) {n : ℕ} {ω : SmoothCosetFftDomain n KC}
    (s : Fin (XI.k + 1) → ℕ+)
    [inst : ∀ j, SampleableType ((pSpec XI.k (ω := ω) s XI.l).Challenge j)] :
    ∀ j, SampleableType ((pSpec (eraseX XI).k (ω := ω) s (eraseX XI).l).Challenge j) :=
  inst
instance instSampEraseX2 [SampleableType KC] [Inhabited KC] (XI : ExecInst) (hn : XI.nD ≤ 32) (s : Fin (XI.k + 1) → ℕ+)
    [inst : ∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) s XI.l).Challenge j)] :
    ∀ j, SampleableType ((pSpec (eraseX XI).k (ω := smoothDomain (eraseX XI).nD hn) s (eraseX XI).l).Challenge j) :=
  inst

theorem fixSels_ge4 (vk : VK) (πF : FixProof) (i : ℕ) (hi : i < vk.X.k) :
    (fixSels vk πF)[4 + i]! = treeSel vk.X 0 (4 + i) πF.pos := by
  unfold fixSels
  rw [getElem!_pos _ (4 + i) (by simp; omega)]
  simp only [Array.getElem_map, Array.getElem_range]
  have h1 : ¬ (4 + i == 0) = true := by simp
  have h2 : ¬ (4 + i < 4) := by omega
  simp only [h1, h2, if_false]
  rfl

section Local
variable [SampleableType KC] [Inhabited KC]

/-- the Fiat-Shamir challenge limbs of an accepting `verifyFix'` are canonical -/
theorem verifyFix'_chal_can (vk : VK) (Hf : HFn) (FSf : FSFn) (z ctx : List Nat) (zeta : VF.K3) (πF : FixProof)
    (h : verifyFix' vk Hf FSf z ctx zeta πF = .ok ()) (i : ℕ) : ∀ x ∈ (fixChals vk FSf z ctx πF)[i]!, x < NockvmE2E.Exec.p := by
  unfold verifyFix' at h
  simp only [bind_unit_ok, forM_ok, ckE_ok, List.mem_range] at h
  obtain ⟨_, _, _, h4, _⟩ := h
  have h4' : (fixChals vk FSf z ctx πF).all (·.all VF.based) = true := h4
  by_cases hi : i < (fixChals vk FSf z ctx πF).size
  · rw [getElem!_pos _ i hi]
    intro x hx
    have := List.all_eq_true.1 ((Array.all_eq_true_iff_forall_mem.1 h4') _ (Array.getElem_mem hi)) x hx
    simpa [VF.based, PN_eq_p] using this
  · rw [getElem!_neg _ i hi]
    intro x hx
    exact absurd hx (by simp [default])

/-- `eraseX` does not change the flat trees (`ftree` does not read `pre`) -/
theorem flatTrees_eraseX (XI : ExecInst) (π : FlatProof) : flatTrees (eraseX XI) π = flatTrees XI π := rfl

/-- **`local_side`**: the FRI local check of the compiled side path accepts (the flat data are those of an accepting `verifyFix'`) -/
theorem local_side (XI : ExecInst) (hg : setupGates XI = true) (hn : XI.nD ≤ 32) (L' : DomLink XI hn)
    [∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)]
    (hshift : XI.dShift = 7) (hgen : psiV XI.dGen = ((zeta XI.nD : KCˣ) : KC)) (hd1 : XI.d = 1)
    (hdom : 2 ^ (∑ j, (((fun _ : Fin (XI.k + 1) => (1 : ℕ+)) j : ℕ+) : ℕ)) * (1 : ℕ+).val ≤ 2 ^ XI.nD)
    (vk : VK) (h : NQuery (skelsSide XI) → DgJ8) (FSf : FSFn) (z ctx : List Nat) (zeta : VF.K3) (π : FlatProof) (πF : FixProof)
    (hc : vk.cols = fixCols XI) (hX : vk.X = eraseX XI) (hctx : ctx = fixCtx π zeta)
    (hv : verifyFix' vk (Hof (skelsSide XI) h) FSf z ctx zeta πF = .ok ())
    (hnc : ¬ VKcoll XI vk (Hof (skelsSide XI) h) πF)
    (Op : Type) [Finite Op] [DecidableEq Op]
    (ω0 ω1 : Op)
    (pm : (protocol (compiledRoundsK DgJ8 Op (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 E2EResid.encK))).tree.ExecutionPath)
    (decode : Op → OpenAll DgJ8 (merkleSkels (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 E2EResid.encK)))
    {Gs : Type} [Fintype Gs] [Nonempty Gs] [SampleableType Gs]
    (GG : CoreDefinitions.Generator Gs (Fin (mSX XI + 1)) KC) (csS : Gs)
    (hG : ∀ i : Fin (mSX XI + 1), GG csS i = toKV (fixCs vk FSf z ctx πF) ^ (i : ℕ))
    {Salt : Type} (salt : Salt)
    (hch : ∀ t, t < XI.k + 2 → (encPathD (compiledRoundsK DgJ8 Op (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 E2EResid.encK))
      (mDecs dgOf (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 E2EResid.encK)
        (dsmC (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) E2EResid.encK) ω0) pm).getD t [] =
      (fixChals vk FSf z ctx πF)[t + 2]!)
    (fm : List (List ℕ))
    (hm : pathMsgs _ pm = decMsgs _ (mDecs dgOf (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 E2EResid.encK)
      (dsmC (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) E2EResid.encK) ω1) fm)
    (hlast : fm.getD (XI.k + 1) [] = πF.pfinal.toList.flatMap VF.K3.limbs)
    (hopen : decode (pathRootsK DgJ8 Op (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 E2EResid.encK) pm).2 =
      openAllOf _ ((flatTrees (eraseX XI) (fixPa vk πF)).drop 4)) :
    friLocal (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 E2EResid.encK Op hdom decode
      (combinedStmt (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) (mSX XI) GG csS
        (stmtOf (SideCfg.mk (m := mSX XI) XI (opIdxX XI) (ptKX XI)) hn ⟨[], ctx, πF.vF⟩), salt) pm = true := by
  
  classical
  letI instE1 : ∀ j, SampleableType ((pSpec (eraseX XI).k (ω := smoothDomain (eraseX XI).nD hn) (fun _ : Fin ((eraseX XI).k + 1) => (1 : ℕ+)) (eraseX XI).l).Challenge j) :=
    ‹∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)›
  letI instE2 : ∀ j, SampleableType ((pSpec (eraseX XI).k (ω := smoothDomain XI.nD hn) (fun _ : Fin ((eraseX XI).k + 1) => (1 : ℕ+)) (eraseX XI).l).Challenge j) :=
    ‹∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)›
  letI : ∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain (eraseX XI).nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j) :=
    ‹∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)›
  letI : ∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain (eraseX XI).nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) (eraseX XI).l).Challenge j) :=
    ‹∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)›
  letI : ∀ j, SampleableType ((pSpec (eraseX XI).k (ω := smoothDomain (eraseX XI).nD hn) (fun _ : Fin ((eraseX XI).k + 1) => (1 : ℕ+)) XI.l).Challenge j) :=
    ‹∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)›
  letI : ∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j) :=
    ‹∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)›
  letI : ∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) (eraseX XI).l).Challenge j) :=
    ‹∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)›
  letI : ∀ j, SampleableType ((pSpec (eraseX XI).k (ω := smoothDomain XI.nD hn) (fun _ : Fin ((eraseX XI).k + 1) => (1 : ℕ+)) XI.l).Challenge j) :=
    ‹∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)›
  obtain ⟨hsz_pf, hsz_pos, hsz_roots, hpfc⟩ := verifyFix'_sizes vk _ FSf z ctx zeta πF hv
  obtain ⟨hlim1, hlim2, hlim3, hlim4, hlim5, hlim6⟩ := verifyFix'_limits vk _ FSf z ctx zeta πF hv
  have hk : vk.X.k = XI.k := by rw [hX]; rfl
  have hl : vk.X.l = XI.l := by rw [hX]; rfl
  have hvals := fixPa_vals_mem vk πF hlim4
  have hwalk := verifyFix'_walk vk _ FSf z ctx zeta πF hv
  have htrees := verifyFix'_trees vk _ FSf z ctx zeta πF hv
  have hposeq := verifyFix'_pos vk _ FSf z ctx zeta πF hv
  have hk1 := nD_of_gates XI hg
  have hsels : ∀ i, i < XI.k → (fixSels vk πF)[4 + i]! = treeSel (eraseX XI) 0 (4 + i) πF.pos := fun i hi => by
    rw [fixSels_ge4 vk πF i (by rw [hk]; exact hi), hX]
  have hsel4 : ∀ j, 4 ≤ j → j < 4 + XI.k → (fixSels vk πF)[j]! = (selsOf (eraseX XI) (fixPa vk πF))[j]! := fun j h4 hj => by
    obtain ⟨i, rfl⟩ : ∃ i, j = 4 + i := ⟨j - 4, by omega⟩
    rw [selsOf_ge4 (eraseX XI) (fixPa vk πF) (4 + i) hj h4, hsels i (by omega)]
    rfl
  have hsib : ∀ j, 4 ≤ j → j < 4 + XI.k → ∀ d ∈ (((fixPa vk πF).sibs)[j]!).toList, dgOk d = true := by
    intro j h4 hj
    obtain ⟨w, rfl⟩ : ∃ w, j = 4 + w := ⟨j - 4, by omega⟩
    have e : ((fixPa vk πF).sibs)[4 + w]! = πF.sibs[1 + w]! :=
      adapt_getElem _ _ vk.X.k w rfl (by rw [hk]; omega) (by omega)
    rw [e]
    intro d hd
    refine hlim5 _ ?_ d (Array.mem_toList_iff.mp hd)
    rw [getElem!_pos πF.sibs (1 + w) (by omega)]
    exact Array.getElem_mem _
  have htcs : ∀ j, 4 ≤ j → j < 4 + XI.k →
      treeCheck (eraseX XI) (Hof (skelsSide (eraseX XI)) h) (fixPa vk πF) #[vk.cols.size, 0, 0, 0] (2 ^ ((eraseX XI).nD - 1)) (fixSels vk πF) j = .ok () := by
    intro j h4 hj
    have := htrees j (by omega)
    rw [hX] at this
    exact this
  have hselF := selF_side (eraseX XI) hn 1 (LX XI hn) rfl E2EResid.encK (fixPa vk πF) h _ _ (fixSels vk πF) htcs hsel4 hvals hsib
  have hvalF := valF_side (eraseX XI) hn 1 (LX XI hn) rfl E2EResid.encK E2EResid.encK_ok (fixPa vk πF) h _ _ (fixSels vk πF) htcs hsel4 hvals hsib
  have hopenE : decode (pathRootsK DgJ8 Op (friMask (ω := smoothDomain (eraseX XI).nD hn) (fun _ : Fin ((eraseX XI).k + 1) => (1 : ℕ+)) 1 (eraseX XI).l (LX XI hn) DgJ8 E2EResid.encK) pm).2 =
      openAllOf _ ((flatTrees (eraseX XI) (fixPa vk πF)).drop 4) := hopen
  have hsel4all : ∀ j, 4 ≤ j → (fixSels vk πF)[j]! = (selsOf (eraseX XI) (fixPa vk πF))[j]! := by
    intro j h4
    by_cases hj : j < 4 + XI.k
    · exact hsel4 j h4 hj
    · have e1 : ¬ j < (fixSels vk πF).size := by unfold fixSels; simp [hk]; omega
      have e2 : ¬ j < (selsOf (eraseX XI) (fixPa vk πF)).size := by unfold selsOf; simp; omega
      rw [getElem!_neg (fixSels vk πF) j e1, getElem!_neg (selsOf (eraseX XI) (fixPa vk πF)) j e2]
  have hlv : lvS (fixPa vk πF).vals (fixSels vk πF) = fun i t => homV.φ (friAtV (fixPa vk πF).vals (4 + i) (lb (selsOf (eraseX XI) (fixPa vk πF))[4 + i]! t)) := by
    funext i t
    unfold lvS
    rw [hsel4all (4 + i) (by omega)]
  have hwalk' := hwalk
  rw [hX] at hwalk'
  have hw0 : ∀ i, canon3 (fixWord0 vk FSf z ctx zeta πF i) := fun i => V.canon3_deepWord _ _ _ _ _
  have hszpos : πF.pos.size = XI.l := by rw [hsz_pos, hl]
  have hxs : ∀ j : Fin XI.l, (XsOf (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 E2EResid.encK Op 0 XI.k (by omega) pm.2.2 j).val =
      homV.ψ XI.dShift * homV.ψ XI.dGen ^ πF.pos[j.1]! := by
    intro j
    have L'e : DomLink (eraseX XI) hn := ⟨L'.dShift_eq, L'.dGen_eq⟩
    have h1 := hX_side (eraseX XI) hn L'e 1 (LX XI hn) E2EResid.encK Op dgOf ω0 XI.k 0 (Nat.zero_add _) pm.2.2 j
    have hq : (encPathD _ (mDecs dgOf (friMerkleMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 E2EResid.encK 0 XI.k (Nat.zero_add _))
        (dsFM (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) E2EResid.encK 0 XI.k (Nat.zero_add _)) ω0) pm.2.2).getD XI.k [] =
        (fixChals vk FSf z ctx πF)[3 + XI.k]! := by
      have := hch (XI.k + 1) (by omega)
      rw [show XI.k + 1 + 2 = 3 + XI.k by omega] at this
      exact this
    refine h1.trans ?_
    erw [hq]
    have hj : j.1 < πF.pos.size := by rw [hszpos]; exact j.2
    have hnDv : vk.X.nD = XI.nD := by rw [hX]; rfl
    have hp2 := hposeq
    simp only [hk, hnDv] at hp2
    have hlen : ((fixChals vk FSf z ctx πF)[3 + XI.k]!).length = πF.pos.size := by
      have := congrArg Array.size hp2
      simpa using this.symm
    have hj' : j.1 < ((fixChals vk FSf z ctx πF)[3 + XI.k]!).length := by rw [hlen]; exact hj
    have key : πF.pos[j.1]! = ((fixChals vk FSf z ctx πF)[3 + XI.k]!)[j.1]! % 2 ^ XI.nD := by
      have e := congrArg (fun a => a[j.1]!) hp2
      try simp only at e
      rw [e, getElem!_pos _ j.1 (by simpa using hj'), getElem!_pos ((fixChals vk FSf z ctx πF)[3 + XI.k]!) j.1 hj']
      simp
    rw [key]
    rfl
  have hα : ∀ i : Fin (XI.k + 1), toKV (VF.K3.ofLimbs ((fun i => (fixChals vk FSf z ctx πF)[i - 5]!) (7 + i.val))) = homV.φ (fixAlphas vk FSf z ctx πF)[i.val]! := by
    intro i
    show _ = toKV _
    unfold fixAlphas
    rw [getElem!_pos _ i.val (by simp [hk]; omega)]
    simp only [Array.getElem_map, Array.getElem_range]
    rw [show 7 + i.val - 5 = 2 + i.val by omega]
  have hW0 : ∀ (j : Fin XI.l) g, Rd XI.nD (πF.pos[j.1]!) 0 g →
      ∃ y : ((smoothDomain XI.nD hn).subdomain 0).toFinset, y.val = Yp (homV.ψ XI.dShift) (homV.ψ XI.dGen) 0 g ∧
        initialOracle (fun _ : Fin (XI.k + 1) => (1 : ℕ+))
          (combinedStmt (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) (mSX XI) GG csS
            (stmtOf (SideCfg.mk (m := mSX XI) XI (opIdxX XI) (ptKX XI)) hn ⟨[], ctx, πF.vF⟩)) y =
          homV.φ (Wf (eraseX XI) (fixWord0 vk FSf z ctx zeta πF) (faV (fixPa vk πF).vals (fixSels vk πF)) (fbV (fixPa vk πF).vals (fixSels vk πF)) 0 g) := by
    intro j g hgj
    have hcs : canon3 (fixCs vk FSf z ctx πF) :=
      canon3_ofLimbs _ (verifyFix'_chal_can vk _ FSf z ctx zeta πF hv 1)
    obtain ⟨y, hy, hi⟩ := hW0_side XI hg hn L' hshift hgen vk _ FSf z ctx zeta π πF hc hX hctx hv hnc GG csS (fixCs vk FSf z ctx πF) hG rfl hcs j g hgj
    exact ⟨y, hy, by rw [hi]; simp [Wf]⟩
  exact friLocal_side (eraseX XI) hn 1 hdom (LX XI hn) rfl E2EResid.encK Op decode pm _ πF.pos (fixPa vk πF).vals (fixSels vk πF)
    (fixWord0 vk FSf z ctx zeta πF) (fixAlphas vk FSf z ctx πF) πF.pfinal (fun i => (fixChals vk FSf z ctx πF)[i - 5]!)
    hshift hgen hk1 hszpos hsels hvals hpfc hw0 hwalk' hxs (by convert hselF using 4; rw [hopenE]; exact Iff.rfl) (by convert hvalF using 4; rw [hopenE, hlv]; exact Iff.rfl)
    dgOf ω0 (dsmC (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) E2EResid.encK)
    (fun t ht => by
      show _ = (fixChals vk FSf z ctx πF)[7 + t - 5]!
      rw [show 7 + t - 5 = t + 2 by omega]; exact hch t ht)
    (E2EResid.hcod0_dsmC _ _ _ _ _) (E2EResid.codOK_dsFM _ _ _ _ _ XI.k 0 (Nat.zero_add _))
    (hPdec_side (eraseX XI) hn 1 (LX XI hn) E2EResid.encK Op dgOf ω1 pm fm πF.pfinal (by rw [hsz_pf, hX]; exact hd1) hm hlast)
    hα hW0

end Local

end NockvmE2E.Exec.SideGlue19
