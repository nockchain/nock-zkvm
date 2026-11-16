/-
 conjunct 5, side-mask plumbing: the codec fields of `friLocal_side` at the concrete decoders `dsmC` of the side FRI mask
(`hPdec` from the final-polynomial message).

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue14` is complete.
-/
import NockvmE2E.Exec.SideGlue12

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideGlue14
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Merkle NockvmE2E.Exec.SideInst
  NockvmE2E.Merkle.Fri NockvmE2E.Exec.SF NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.DomIdx NockvmE2E.Exec.E2EFri
  NockvmE2E.Exec.SideGlue9 NockvmE2E.FriPort NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Merkle.RapFriQ NockvmE2E.Exec.E2EResid NockvmE2E.Exec.Inst

/-- **`hPdec` for the side FRI mask**: the final polynomial read off the compiled path `pm` (messages `fm`, decoded by `dsmC`) evaluates as the Horner polynomial of
`pfinal`, given that the last message is `pfinal`'s limbs and `pfinal.size = d` -/
theorem hPdec_side (XI : ExecInst) (hn32 : XI.nD ≤ 32) [SampleableType KC] [Inhabited KC]
    [∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)]
    (d : ℕ+) (L : Fri.FriLeaves (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+))) (enc : KC ↪ DgJ8)
    (Op : Type) [Finite Op] [DecidableEq Op] (dY : List ℕ → DgJ8) (ω0 : Op)
    (pm : (protocol (compiledRoundsK DgJ8 Op (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc))).tree.ExecutionPath)
    (fm : List (List ℕ)) (pfinal : Array VF.K3) (hsz : pfinal.size = d.val)
    (hm : pathMsgs _ pm = decMsgs _ (mDecs dY (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc)
      (dsmC (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L enc) ω0) fm)
    (hlast : fm.getD (XI.k + 1) [] = pfinal.toList.flatMap VF.K3.limbs) (y : KC) :
    (finPolyOf (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc Op 0 XI.k (by omega) pm.2.2).eval y =
      hornerF (fun j => homV.φ pfinal[j]!) pfinal.size y := by
  classical
  have hm' : pathMsgs _ pm = decMsgs _ (mDecs dY (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc)
      (dsmC (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L enc) ω0) fm := hm
  have h1 : pathMsgs _ pm.2.2 = decMsgs _ (mDecs dY _ (dsFM (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L enc 0 XI.k (Nat.zero_add _)) ω0) fm.tail :=
    congrArg Prod.snd hm'
  have hf := finPolyOf_dsFM (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L enc dY ω0 XI.k 0 (Nat.zero_add _) _
    fm.tail h1
  have hlast' : fm.tail.getD XI.k [] = pfinal.toList.flatMap VF.K3.limbs := by
    rw [← hlast]; simp [List.getD_eq_getElem?_getD, List.getElem?_tail]
  rw [hf, hlast', eval_finPolyD, hornerF_sum, length_flat, Array.length_toList]
  have hmin : min (3 * pfinal.size / 3) d.val = pfinal.size := by
    rw [hsz]; omega
  rw [hmin]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have := ofLimbs_flat pfinal.toList j (by simpa using hj')
  rw [this]
  have h3 : pfinal.toList[j]! = pfinal[j]! := by
    simp [getElem!_pos, hj']
  rw [h3]; rfl

theorem xs_last_side (XI : ExecInst) (hn32 : XI.nD ≤ 32) [SampleableType KC] [Inhabited KC]
    [∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)]
    (d : ℕ+) (v : ((friAlt (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l).midRound XI.k (Nat.lt_succ_self XI.k)).Challenge) :
    cast (queryChallenge_type (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l)
      (xp (a := ⟨2 * XI.k + 2, by have := friLength (k := XI.k); omega⟩) (b := (queryChallenge (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).val)
        (Fin.ext (by simp only [queryChallenge_val])) v) = cast (queryE (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l) v :=
  eq_of_heq ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))

/-- **`hxs` for the side FRI mask** (port of `hX_dsFM`): the query points read off the compiled path are `dShift · dGen ^ (encoded query challenge)` -/
theorem hX_side (XI : ExecInst) (hn32 : XI.nD ≤ 32) [SampleableType KC] [Inhabited KC]
    [∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)]
    (hD : DomLink XI hn32) (d : ℕ+) (L : Fri.FriLeaves (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+))) (enc : KC ↪ DgJ8)
    (Op : Type) [Finite Op] [DecidableEq Op] (dY : List ℕ → DgJ8) (ω0 : Op) : (c i : ℕ) → (h : i + c = XI.k) →
    (q : (protocol (compiledRoundsK DgJ8 Op (friMerkleMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc i c h))).tree.ExecutionPath) → (j : Fin XI.l) →
    (XsOf (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc Op i c h q j).val =
      homV.ψ XI.dShift * homV.ψ XI.dGen ^
        (((encPathD _ (mDecs dY _ (dsFM (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L enc i c h) ω0) q).getD c [])[j.1]! % 2 ^ XI.nD)
  | 0, i, h, q, j => by
      have hi : i = XI.k := by omega
      subst hi
      have e1 : (XsOf (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc Op XI.k 0 h q j) =
          (cast (queryE (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l) q.2.1) j := by
        have := xs_last_side XI hn32 d q.2.1
        exact congrFun this j
      have e2 : ((encPathD _ (mDecs dY _ (dsFM (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L enc XI.k 0 h) ω0) q).getD 0 []) =
          (qCodec (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l).encC q.2.1 := rfl
      rw [e1, e2]
      set x := (cast (queryE (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l) q.2.1) j with hx
      have hj : ((qCodec (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l).encC q.2.1)[j.1]! =
          (((smoothDomain XI.nD hn32).subdomain 0).equivToFinset.symm x).val := by
        simp [qCodec, List.getElem!_eq_getElem?_getD, hx]
      rw [hj]
      set idx := ((smoothDomain XI.nD hn32).subdomain 0).equivToFinset.symm x with hidx
      have h1 : x.val = smoothDomain XI.nD hn32 idx := by
        rw [← CosetFftDomainClass.subdomain_0_apply]
        exact (CosetFftDomain.equivToFinset_symm_apply ((smoothDomain XI.nD hn32).subdomain 0) x).symm
      rw [h1, Nat.mod_eq_of_lt (by simpa using idx.2)]
      exact hω_of_domLink XI _ hD idx
  | c + 1, i, h, q, j => hX_side XI hn32 hD d L enc Op dY ω0 c i.succ (by omega) q.2.2 j

/-- **`tree_open_side`**: port of `tree_open` to a tree `j ≥ 4` of an adapted proof whose `treeCheck` passed: the embedded opening is
`⟨selOf .., valsOf .., pr⟩` (selector and values read off the flat tree) -/
theorem tree_open_side (XI : ExecInst) (πa : FlatProof) (skels : List Skeleton)
    (h : NQuery skels → DgJ8) (W : Array ℕ) (half0 : ℕ) (sels : Array (Array ℕ))
    (hlen : skels.length = 4 + XI.k)
    (j : Fin skels.length) (hj4 : 4 ≤ j.1)
    (hsk : skels.get j = skelFlat XI j.1)
    (htc : treeCheck XI (Hof skels h) πa W half0 sels j.1 = .ok ())
    (hsel : sels[j.1]! = (selsOf XI πa)[j.1]!)
    (hlim : ∀ v ∈ πa.vals, ∀ x ∈ v, x < NockvmE2E.Exec.p)
    (hsb : ∀ d ∈ (πa.sibs[j.1]!).toList, dgOk d = true) :
    ∃ pr, mkOpeningD (ftree XI πa j.1) (skels.get j) =
      ⟨selOf (ftree XI πa j.1).isSel (skels.get j) 0,
        valsOf (ftree XI πa j.1).lv (skels.get j) (selOf (ftree XI πa j.1).isSel (skels.get j) 0) 0, pr⟩ := by
  have hjk : j.1 < 4 + XI.k := hlen ▸ j.2
  have hne : ¬ (j.1 < 4 ∧ W[j.1]! = 0) := by omega
  obtain ⟨_, hgo⟩ := treeCheck_root XI (Hof skels h) πa W half0 sels j.1 htc hne
  rw [hsel] at hgo
  have hn4 : ¬ j.1 < 4 := by omega
  have hsp : WfSpec (friSpec (2 ^ (XI.nD - (j.1 - 3)))) ∧ 1 ≤ (friSpec (2 ^ (XI.nD - (j.1 - 3)))).total :=
    ⟨wf_friSpec _, by simp only [friSpec]; exact Nat.two_pow_pos _⟩
  have hcl' : ∀ r, dgOk (if j.1 < 4 then [(πa.vals[j.1]!)[r]!, 0, 0, 0, 0]
      else [(πa.vals[j.1]!)[3 * r]!, (πa.vals[j.1]!)[3 * r + 1]!, (πa.vals[j.1]!)[3 * r + 2]!, 0, 0]) = true := by
    intro r
    have hz : NockvmE2E.Exec.VF.based 0 = true := by
      simp [NockvmE2E.Exec.VF.based, PN_eq]; exact (Fact.out : Nat.Prime NockvmE2E.Exec.p).pos
    simp only [hn4, ite_false]
    simp [dgOk, NockvmE2E.Exec.VF.based, PN_eq, arr_get_lt (a := πa.vals) hlim, hz]
    exact (Fact.out : Nat.Prime NockvmE2E.Exec.p).pos
  have hsk' : skels.get j = skelOf (friSpec (2 ^ (XI.nD - (j.1 - 3)))) (friSpec (2 ^ (XI.nD - (j.1 - 3)))).total
      (friSpec (2 ^ (XI.nD - (j.1 - 3)))).total := by
    rw [hsk]; unfold skelFlat; simp [hn4]
  exact embed_tree_open skels h j _ hsp.1 hsk' hsp.2 _ (selsOf_pw XI πa j.1 hjk) _ _ _ hcl' hsb (by simpa [hn4] using hgo)

/-- the per-tree readout of the value of a selected leaf (port of `open_val`) -/
theorem open_val_side (XI : ExecInst) (πa : FlatProof) (skels : List Skeleton)
    (h : NQuery skels → DgJ8) (W : Array ℕ) (half0 : ℕ) (sels : Array (Array ℕ))
    (hlen : skels.length = 4 + XI.k) (j : Fin skels.length) (hj4 : 4 ≤ j.1)
    (hsk : skels.get j = skelFlat XI j.1)
    (htc : treeCheck XI (Hof skels h) πa W half0 sels j.1 = .ok ())
    (hsel : sels[j.1]! = (selsOf XI πa)[j.1]!)
    (hlim : ∀ v ∈ πa.vals, ∀ x ∈ v, x < NockvmE2E.Exec.p)
    (hsb : ∀ d ∈ (πa.sibs[j.1]!).toList, dgOk d = true)
    (tr : FTree DgJ8) (htr : tr = ftree XI πa j.1) (sk : Skeleton) (hs : sk = skels.get j) :
    ∀ t (ht : (mkOpeningD tr sk).selector.get t = true),
      selectedValueAt (mkOpeningD tr sk).values t ht = tr.lv (leafNum t) := by
  subst htr hs
  obtain ⟨pr, hpr⟩ := tree_open_side XI πa skels h W half0 sels hlen j hj4 hsk htc hsel hlim hsb
  intro t ht
  revert ht
  rw [hpr]
  intro ht
  exact (selectedValueAt_valsOf _ t _ 0 ht).trans (by rw [Nat.zero_add])

/-- **`hselF` for the side proof**: the openings' selectors mark every leaf of the verifier's selection -/
theorem selF_side (XI : ExecInst) (hn32 : XI.nD ≤ 32) [SampleableType KC] [Inhabited KC]
    [∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)]
    (d : ℕ+) (L : Fri.FriLeaves (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+))) (hL : L = LX XI hn32) (enc : KC ↪ DgJ8)
    (πa : FlatProof) (h : NQuery (skelsSide XI) → DgJ8) (W : Array ℕ) (half0 : ℕ) (sels : Array (Array ℕ))
    (htcs : ∀ j, 4 ≤ j → j < 4 + XI.k → treeCheck XI (Hof (skelsSide XI) h) πa W half0 sels j = .ok ())
    (hsels : ∀ j, 4 ≤ j → j < 4 + XI.k → sels[j]! = (selsOf XI πa)[j]!)
    (hlim : ∀ v ∈ πa.vals, ∀ x ∈ v, x < NockvmE2E.Exec.p)
    (hsbs : ∀ j, 4 ≤ j → j < 4 + XI.k → ∀ d ∈ (πa.sibs[j]!).toList, dgOk d = true) :
    SelF (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc (QS sels) 0 XI.k (by omega)
      (openAllOf _ ((flatTrees XI πa).drop 4)) := by
  refine selF_openAll (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L enc (QS sels) XI.k 0 (by omega) _ ?_
  intro b hb _ _ t ht
  have hj : 4 + b < (skelsSide XI).length := by rw [skelsSide_length]; omega
  have h4b : 4 ≤ 4 + b := by omega
  have hltb : 4 + b < 4 + XI.k := by omega
  have hg : ((flatTrees XI πa).drop 4).getD (b - 0) ⟨fun _ => false, fun _ => default, [], default⟩ = ftree XI πa (4 + b) := by
    rw [Nat.sub_zero, ← ftree_getD XI πa (4 + b) (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm 4 b]
  have hsL : L.skel ⟨b, hb⟩ = (skelsSide XI).get ⟨4 + b, hj⟩ := by
    rw [skelsSide_get_fri XI b hb hj]
    subst hL
    simp [LX, friSkel]
  have hsk : (skelsSide XI).get ⟨4 + b, hj⟩ = skelFlat XI (4 + b) := by
    rw [skelsSide_get_fri XI b hb hj]
    simpa using friSkel_eq_skelFlat XI ⟨b, hb⟩
  obtain ⟨pr, hpr⟩ := tree_open_side XI πa (skelsSide XI) h W half0 sels (skelsSide_length XI) ⟨4 + b, hj⟩ (by simp) hsk
    (htcs (4 + b) h4b hltb) (hsels (4 + b) h4b hltb) hlim (hsbs (4 + b) h4b hltb)
  have key : ∀ (s' : Skeleton), s' = (skelsSide XI).get ⟨4 + b, hj⟩ → ∀ (t : SkeletonLeafIndex s'),
      QS sels b (leafNum t) → (mkOpeningD (ftree XI πa (4 + b)) s').selector.get t = true := by
    intro s' hs' t ht
    subst hs'
    rw [hpr]
    show (selOf (ftree XI πa (4 + b)).isSel ((skelsSide XI).get ⟨4 + b, hj⟩) 0).get t = true
    rw [selOf_get]
    have ht' : leafNum t ∈ ((selsOf XI πa)[4 + b]!).toList := by
      have := ht
      unfold QS at this
      rwa [hsels (4 + b) h4b hltb] at this
    have hpw : ((selsOf XI πa)[4 + b]!).toList.Pairwise (· < ·) := selsOf_pw XI πa (4 + b) hltb
    have := (mem_iff_lb _ hpw _).mpr ht'
    simp [ftree, ftreeOf, this]
  rw [hg]
  exact key _ hsL t ht

/-- **`hvalF` for the side proof**: the opened digest at every selected leaf of FRI word `i` is the codec image of the flat leaf value -/
theorem valF_side (XI : ExecInst) (hn32 : XI.nD ≤ 32) [SampleableType KC] [Inhabited KC]
    [∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)]
    (d : ℕ+) (L : Fri.FriLeaves (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+))) (hL : L = LX XI hn32) (enc : KC ↪ DgJ8)
    (hEnc : EncOK enc) (πa : FlatProof) (h : NQuery (skelsSide XI) → DgJ8) (W : Array ℕ) (half0 : ℕ) (sels : Array (Array ℕ))
    (htcs : ∀ j, 4 ≤ j → j < 4 + XI.k → treeCheck XI (Hof (skelsSide XI) h) πa W half0 sels j = .ok ())
    (hsels : ∀ j, 4 ≤ j → j < 4 + XI.k → sels[j]! = (selsOf XI πa)[j]!)
    (hlim : ∀ v ∈ πa.vals, ∀ x ∈ v, x < NockvmE2E.Exec.p)
    (hsbs : ∀ j, 4 ≤ j → j < 4 + XI.k → ∀ d ∈ (πa.sibs[j]!).toList, dgOk d = true) :
    ValF (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc (fun i t => homV.φ (friAtV πa.vals (4 + i) (lb (selsOf XI πa)[4 + i]! t))) 0 XI.k (by omega)
      (openAllOf _ ((flatTrees XI πa).drop 4)) := by
  refine valF_openAll (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L enc _ _ _ _ _ ?_
  intro b hb _ _ o ho t hs
  have hj : 4 + b < (skelsSide XI).length := by rw [skelsSide_length]; omega
  have hget : ((flatTrees XI πa).drop 4).getD (b - 0) ⟨fun _ => false, fun _ => default, [], default⟩ = ftree XI πa (4 + b) := by
    rw [Nat.sub_zero, ← ftree_getD XI πa (4 + b) (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm 4 b]
  have hsL : L.skel ⟨b, hb⟩ = (skelsSide XI).get ⟨4 + b, hj⟩ := by
    rw [skelsSide_get_fri XI b hb hj]
    subst hL
    simp [LX, friSkel]
  have hsk : (skelsSide XI).get ⟨4 + b, hj⟩ = skelFlat XI (4 + b) := by
    rw [skelsSide_get_fri XI b hb hj]
    simpa using friSkel_eq_skelFlat XI ⟨b, hb⟩
  have h4b : 4 ≤ 4 + b := by omega
  have hltb : 4 + b < 4 + XI.k := by omega
  have hv := open_val_side XI πa (skelsSide XI) h W half0 sels (skelsSide_length XI) ⟨4 + b, hj⟩ (by simp) hsk
    (htcs (4 + b) h4b hltb) (hsels (4 + b) h4b hltb) hlim (hsbs (4 + b) h4b hltb) _ hget _ hsL
  subst ho
  rw [hv t hs, hget]
  have hb' : ∀ a r, (πa.vals[a]!)[r]! < NockvmE2E.Exec.p := fun a r => arr_get_lt (a := πa.vals) hlim a r
  have h4' : ¬ 4 + b < 4 := by omega
  show dgOf _ = enc (homV.φ (friAtV πa.vals (4 + b) (lb (selsOf XI πa)[4 + b]! (leafNum t))))
  unfold friAtV
  rw [show homV.φ _ = toKV _ from rfl, hEnc _ _ _ (hb' _ _) (hb' _ _) (hb' _ _)]
  simp [ftree, ftreeOf, h4']

end NockvmE2E.Exec.SideGlue14

#print axioms NockvmE2E.Exec.SideGlue14.hPdec_side
#print axioms NockvmE2E.Exec.SideGlue14.hX_side
#print axioms NockvmE2E.Exec.SideGlue14.tree_open_side
#print axioms NockvmE2E.Exec.SideGlue14.selF_side
#print axioms NockvmE2E.Exec.SideGlue14.valF_side
