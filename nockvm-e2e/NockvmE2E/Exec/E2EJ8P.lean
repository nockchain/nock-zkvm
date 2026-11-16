import NockvmE2E.Exec.E2EFinal
import NockvmE2E.Exec.E2EInstGen
import NockvmE2E.Exec.HdagU
import NockvmE2E.Exec.J8Shape
import NockvmE2E.J8.MinusT
import NockvmE2E.J8.InstJ8W
import NockvmE2E.J8.RVUJ8
import NockvmE2E.J8.TieJ8G
import NockvmE2E.J8.E2E
import NockvmE2E.Exec.J8ShapeX

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.E2EJ8P
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort
  NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EResid NockvmE2E.Exec.E2EW0 NockvmE2E.Exec.E2EFinal
  NockvmE2E.Exec.InstGen
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM NockvmE2E.J8 NockvmE2E.Exec.E2ELR
open NockvmE2E.J8.TieJ8G
open NockvmE2E.J8.InstJ8 (ω0)
open NockvmE2E.J8.InstJ8W (sigmaX tabIdx RJ8 hfree_J8)
open ProximityGap CoreDefinitions NockvmE2E.Succ.Numbers

/-! ## 4. numbers -/

theorem nD_of_shape {XI : ExecInst} (h : J8Shape.j8ShapeOk XI = true) : XI.nD = XI.k + 7 := by
  unfold J8Shape.j8ShapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  tauto

/-- `hrate` -/
theorem hrate_X {XI : ExecInst} (h : J8Shape.j8ShapeOk XI = true) (dF : ℕ+) (hd : dF.val = XI.d) :
    64 * (2 ^ (∑ j : Fin (XI.k + 1), ((fun _ : Fin (XI.k + 1) => (1 : ℕ+)) j).val) * dF.val) ≤ 2 ^ XI.nD := by
  rw [hd, J8Shape.d_of_shape h, nD_of_shape h]
  simp only [PNat.one_coe, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  rw [pow_add 2 XI.k 7, pow_add 2 XI.k 1]; norm_num; omega

theorem hF_X : goldilocks ^ 3 ≤ Fintype.card KC := by
  rw [KC_card]; unfold goldilocks; norm_num

theorem hDg_X : goldilocks ^ 4 ≤ Nat.card DgJ8 := by
  unfold DgJ8
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have : NockvmE2E.Exec.p = 18446744069414584321 := p_eq
  rw [this]; unfold goldilocks; norm_num


theorem hω_smooth (n : ℕ) (hn : n ≤ 32) (i : Fin (2 ^ n)) :
    domEmb (smoothDomain n hn) i ∈ Set.range (algebraMap (ZMod NockvmE2E.Exec.p) KC) := by
  have h : domEmb (smoothDomain n hn) i = smoothDomain n hn i := rfl
  rw [h, smoothDomain_apply, zeta_val]
  exact ⟨7 * (NTT.root n).toZ ^ (i : ℕ), by simp [map_pow]⟩

section Gen
variable {n k : ℕ} (hn : n ≤ 32) (J : RapAirJ (ZMod NockvmE2E.Exec.p) KC) (pr : PubRead J) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
  (hNH : friBound s d ≤ J.H.card) (hpd : ∀ j c, J.pre j = some c → c.natDegree ≤ J.H.card)

theorem hD_X : (deepParamsJ J pr (smoothDomain n hn) (31 / 64) (friBound s d) hNH hpd).D.card ≤ 2 ^ 32 := by
  refine (Finset.card_image_le).trans ?_
  rw [Finset.card_univ, Fintype.card_fin]
  exact Nat.pow_le_pow_right (by norm_num) hn

theorem hH_X : (deepParamsJ J pr (smoothDomain n hn) (31 / 64) (friBound s d) hNH hpd).H.card ≤ 2 ^ 32 := by
  show (HK J).card ≤ _
  rw [card_HK]
  exact J.cap_H.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num))

theorem htoPoly_X (hrate : 64 * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ n) :
    (deepParamsJ J pr (smoothDomain n hn) (31 / 64) (friBound s d) hNH hpd).toPoly =
      udDecodeB (smoothDomain n hn) (31 / 64) (friBound s d) := by
  have hr : 64 * friBound s d ≤ 2 ^ n := hrate
  have hN1 : 0 < friBound s d := by unfold friBound; positivity
  have hN : friBound s d + 1 ≤ 2 ^ n := by omega
  have hδ : (31 / 64 : ℝ≥0) ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb (smoothDomain n hn)) (friBound s d + 1) : Set (Fin (2 ^ n) → KC)) :=
    relUDR_rs_ge _ _ (by rw [Fintype.card_fin]; omega)
  exact tp_eq (smoothDomain n hn) (hω_smooth n hn) hN hδ

end Gen


section Inst
variable (I : Inst) (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub)

/-- the interface domain `H` has `hN` points -/
theorem card_H_JJ : (I.JJ npub tp hcap).H.card = I.XI.hN := by
  rw [hdom_J8 I npub tp hcap]
  exact Finset.card_image_of_injOn (by simpa using hinj_J8 I) |>.trans (Finset.card_range _)

/-- `hNH`: `friBound s1 dF = 2^(k+1) = hN ≤ |H|` (`dF = 1`) -/
theorem hNH_X (dF : ℕ+) (hd : dF.val = I.XI.d) :
    friBound (fun _ : Fin (I.XI.k + 1) => (1 : ℕ+)) dF ≤ (I.JJ npub tp hcap).H.card := by
  rw [card_H_JJ, show friBound (fun _ : Fin (I.XI.k + 1) => (1 : ℕ+)) dF = 2 ^ (I.XI.k + 1) by
    unfold friBound
    rw [hd, J8Shape.d_of_shape I.hsh]
    simp; rfl, J8Shape.hN_of_shape I.hsh]

/-- `hcap`: the cap of `plusJ` at `npub = pubOf.size ≤ 926` (J-8 has 71 public values; this bound is NOT implied by `j8ShapeOk`) -/
theorem hcap_X (hnp : npub ≤ 926) : I.Cap npub := by
  unfold Inst.Cap
  have h1 : Fintype.card I.Jm.ι0 ≤ 1117 := by
    refine le_trans (Fintype.card_subtype_le _) ?_
    exact (InstJ8.card_Ι).le
  have h2 : I.Jm.r = 2 := rfl
  have h3 : I.Jm.d = 4 := rfl
  rw [h2, h3, Fintype.card_fin]
  omega


/-! ### preprocessing degrees -/

theorem natDeg_interp_le {n : ℕ} (nodes : Fin n → ZMod InstJ8.P) (hinj : Function.Injective nodes) (r : Fin n → ZMod InstJ8.P) :
    (Lagrange.interpolate Finset.univ nodes r).natDegree ≤ n := by
  have h := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin n))) (v := nodes) r hinj.injOn
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact Polynomial.natDegree_le_of_degree_le h.le

theorem preOf_deg {R : Nock.Framework.FixedPreprocessingRAP (ZMod InstJ8.P)} {c : Fin R.rap.w} {q : (ZMod InstJ8.P)[X]} {N : ℕ}
    (h : InstJ8.preOf R c = some q) (hall : ∀ j, (R.preprocessing j).natDegree ≤ N) : q.natDegree ≤ N := by
  classical
  unfold InstJ8.preOf at h
  split_ifs at h with hex
  · rw [← Option.some.inj h]; exact hall _


theorem pb_facts (XI : ExecInst) (hsh : J8Shape.j8ShapeOk XI = true) {hpos : InstJ8.PosX XI} {kroots krootsV : ℕ}
    {Rt : ℕ → Nock.Jet.Autogen.Tpl} {regs ids : List ℕ} {idx : ℕ → ℕ} {rk : ℕ → ℕ × ℕ}
    {lay : Fin (InstJ8.hNof XI "jetChipJ8") → Nock.Jet.ChipJ8.PRow} (Pb : Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8.PubJ8 InstJ8.P)
    (hd : Pb = InstJ8.PbOfX XI hsh hpos kroots krootsV Rt regs ids idx rk lay) (hk1 : 1 ≤ XI.hN) :
    (∀ i, Pb.nodes i = ω0 XI ^ (i : ℕ)) ∧ (∀ i, Pb.nodesC i = ω0 XI ^ (i : ℕ)) ∧ (∀ i, Pb.nodesW i = ω0 XI ^ (i : ℕ)) ∧
    (∀ i, Pb.nodesJ i = ω0 XI ^ (i : ℕ)) ∧ (∀ i, Pb.nodesA i = ω0 XI ^ (i : ℕ)) ∧ (∀ i, Pb.nodesV i = ω0 XI ^ (i : ℕ)) ∧
    Pb.n ≤ XI.hN ∧ Pb.nC ≤ XI.hN ∧ Pb.nW ≤ XI.hN ∧ Pb.nJ ≤ XI.hN ∧ Pb.nA ≤ XI.hN ∧ Pb.nV ≤ XI.hN := by
  subst hd
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    InstJ8.hNof_le _ hsh _, InstJ8.hNof_le _ hsh _, InstJ8.hNof_le _ hsh _, InstJ8.hNof_le _ hsh _, InstJ8.hNof_le _ hsh _,
    InstJ8.nV_le _ hsh hk1⟩

set_option maxRecDepth 8000 in
/-- **`hpd`**: every fixed column of `J8` is an interpolant over `n_t ≤ hN` nodes, so has degree `≤ hN = |H|` -/
theorem hpd_X : ∀ j c, (I.JJ npub tp hcap).pre j = some c → c.natDegree ≤ (I.JJ npub tp hcap).H.card := by
  intro j c h
  rw [card_H_JJ]
  rcases j with ⟨jj, hj⟩ | j
  swap
  · have h0 : (none : Option (ZMod NockvmE2E.Exec.p)[X]) = some c := h
    cases h0
  have h' : InstJ8.preJ I.d jj = some c := h
  have hsh := I.hsh
  have hk1 : 1 ≤ I.XI.hN := by rw [J8Shape.hN_of_shape hsh]; exact Nat.one_le_two_pow
  have hd := I.hd
  obtain ⟨e1, e2, e3, e4, e5, e6, n1, n2, n3, n4, n5, n6⟩ := pb_facts I.XI hsh I.d.Pb I.hd hk1
  have hi : ∀ {n : ℕ} (nodes : Fin n → ZMod InstJ8.P), (∀ i, nodes i = ω0 I.XI ^ (i : ℕ)) → n ≤ I.XI.hN →
      Function.Injective nodes := fun nodes e hn a b hab => InstJ8.inj_pows hsh hn (by simpa [e] using hab)
  rcases jj with c | c | c | c | c | c
  · refine (preOf_deg h' ?_).trans n1
    intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ e1 n1) _
  · refine (preOf_deg h' ?_).trans n2
    intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ e2 n2) _
  · refine (preOf_deg h' ?_).trans n3
    intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ e3 n3) _
  · refine (preOf_deg h' ?_).trans n4
    intro j; exact natDeg_interp_le _ (hi _ e4 n4) _
  · refine (preOf_deg h' ?_).trans n5
    intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ e5 n5) _
  · refine (preOf_deg h' ?_).trans n6
    intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ e6 n6) _


/-! ### hpre0 -/

theorem preOf_none {R : Nock.Framework.FixedPreprocessingRAP (ZMod InstJ8.P)} {c : Fin R.rap.w} (S : List ℕ)
    (hS : ∀ j, (R.preprocessingIndex j).val ∈ S) (hc : c.val ∉ S) : InstJ8.preOf R c = none := by
  classical
  unfold InstJ8.preOf
  rw [dite_eq_right_iff]
  intro hex
  exfalso
  obtain ⟨j, hj⟩ := hex
  apply hc
  have := congrArg Fin.val hj
  have e : (R.preprocessingColumn j).val = (R.preprocessingIndex j).val := rfl
  rw [e] at this
  rw [← this]; exact hS j

theorem preJ_none (d : InstJ8.Datum) (s : Fin 6) (c : ℕ) (hc : c < wOf s)
    (hnot : c ∉ (J8Shape.preIdxJ8 (InstJ8.tabId s)).toList) : InstJ8.preJ d (colI s c) = none := by
  fin_cases s
  · have hc' : c % 123 = c := Nat.mod_eq_of_lt hc
    have hnot' : c ∉ (J8Shape.preIdxJ8 "computeChipVCLHX").toList := hnot
    show InstJ8.preOf _ _ = none
    refine preOf_none (J8Shape.preIdxJ8 "computeChipVCLHX").toList ?_ ?_
    · intro j; fin_cases j <;> simp [J8Shape.preIdxJ8] <;> first | exact Or.inl rfl | exact Or.inr rfl
    · simpa [hc'] using hnot'
  · have hc' : c % 242 = c := Nat.mod_eq_of_lt hc
    have hnot' : c ∉ (J8Shape.preIdxJ8 "cellChipHQKW").toList := hnot
    show InstJ8.preOf _ _ = none
    refine preOf_none (J8Shape.preIdxJ8 "cellChipHQKW").toList ?_ ?_
    · intro j; fin_cases j <;> simp [J8Shape.preIdxJ8] <;> first | exact Or.inl rfl | exact Or.inr rfl
    · simpa [hc'] using hnot'
  · have hc' : c % 166 = c := Nat.mod_eq_of_lt hc
    have hnot' : c ∉ (J8Shape.preIdxJ8 "walkChipJ8").toList := hnot
    show InstJ8.preOf _ _ = none
    refine preOf_none (J8Shape.preIdxJ8 "walkChipJ8").toList ?_ ?_
    · intro j; fin_cases j <;> simp [J8Shape.preIdxJ8] <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
    · simpa [hc'] using hnot'
  · have hc' : c % 71 = c := Nat.mod_eq_of_lt hc
    have hnot' : c ∉ (J8Shape.preIdxJ8 "jetChipJ8").toList := hnot
    show InstJ8.preOf _ _ = none
    refine preOf_none (J8Shape.preIdxJ8 "jetChipJ8").toList ?_ ?_
    · intro j; simp [J8Shape.preIdxJ8]; exact j.2
    · simpa [hc'] using hnot'
  · have hc' : c % 349 = c := Nat.mod_eq_of_lt hc
    have hnot' : c ∉ (J8Shape.preIdxJ8 "atomChipHQL").toList := hnot
    show InstJ8.preOf _ _ = none
    refine preOf_none (J8Shape.preIdxJ8 "atomChipHQL").toList ?_ ?_
    · intro j; fin_cases j <;> simp [J8Shape.preIdxJ8] <;> first | exact Or.inl rfl | exact Or.inr rfl
    · simpa [hc'] using hnot'
  · have hc' : c % 166 = c := Nat.mod_eq_of_lt hc
    have hnot' : c ∉ (J8Shape.preIdxJ8 "walkChipHQK").toList := hnot
    show InstJ8.preOf _ _ = none
    refine preOf_none (J8Shape.preIdxJ8 "walkChipHQK").toList ?_ ?_
    · intro j; fin_cases j <;> simp [J8Shape.preIdxJ8] <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
    · simpa [hc'] using hnot'


theorem preKind_of_shape {XI : ExecInst} (h : J8Shape.j8ShapeOk XI = true) :
    ∀ t ∈ XI.tabs.toList, ∀ c < t.nc - t.npub, ((XI.colKind[t.col0 + c]! == 1) == (J8Shape.preIdxJ8 t.chip.id).contains c) = true := by
  have hk : J8Shape.preKindOk XI = true := by
    unfold J8Shape.j8ShapeOk at h
    simp only [Bool.and_eq_true] at h
    tauto
  unfold J8Shape.preKindOk at hk
  intro t ht c hc
  have := (Array.all_eq_true_iff_forall_mem.mp hk) t (Array.mem_def.mpr ht)
  simp only [List.all_eq_true, List.mem_range] at this
  exact this c hc

theorem tabId_tabIdx (a : String) (ha : a ∈ ["computeChipVCLHX", "cellChipHQKW", "walkChipJ8", "atomChipHQL", "walkChipHQK", "jetChipJ8"]) :
    InstJ8.tabId (tabIdx a) = a ∧ J8Shape.wJ8 a = wOf (tabIdx a) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- **`hpre0`**: kind-0 columns are not fixed columns -/
theorem hpre0_X : ∀ (t : Fin I.XI.tabs.size) c, c < I.XI.tabs[t].nc - I.XI.tabs[t].npub →
      I.XI.colKind[I.XI.tabs[t].col0 + c]! = 0 → (I.JJ npub tp hcap).pre (colJ I npub tp hcap t c) = none := by
  intro t c hc hk
  have hsh := I.hsh
  obtain ⟨-, hmem⟩ := ids_of_shape hsh
  have hm : I.XI.tabs[t] ∈ I.XI.tabs.toList := Array.getElem_mem_toList t.2
  have hid := hmem _ hm
  obtain ⟨e1, e2⟩ := tabId_tabIdx _ hid
  have hw := J8Shape.width_of_shape hsh _ hm
  have hpk := preKind_of_shape hsh _ hm c hc
  rw [hk] at hpk
  have hnot : c ∉ (J8Shape.preIdxJ8 (InstJ8.tabId (sigmaX I.XI t))).toList := by
    show c ∉ (J8Shape.preIdxJ8 (InstJ8.tabId (tabIdx I.XI.tabs[t].chip.id))).toList
    rw [e1]
    intro hmem'
    have : (J8Shape.preIdxJ8 I.XI.tabs[t].chip.id).contains c = true := by
      rw [Array.contains_iff_mem]; exact Array.mem_toList_iff.mp hmem'
    rw [this] at hpk
    simp at hpk
  exact preJ_none I.d _ c (by rw [hw] at hc; exact e2 ▸ hc) hnot

end Inst

theorem fold_layout (f : Nat × Nat × Bool → TabInst → Nat × Nat × Bool) (Q : TabInst → Prop)
    (hf1 : ∀ st t, (f st t).1 = st.1 + t.nc) (hf2 : ∀ st t, (f st t).2.1 = st.2.1 + t.npub)
    (hf3 : ∀ st t, (f st t).2.2 = true → st.2.2 = true ∧ t.col0 = st.1 ∧ t.pubBase = st.2.1 ∧ Q t) :
    ∀ (l : List TabInst) (st : Nat × Nat × Bool), (l.foldl f st).2.2 = true →
      st.2.2 = true ∧
      (∀ i (hi : i < l.length), l[i].col0 = st.1 + ((l.take i).map (·.nc)).sum ∧
        l[i].pubBase = st.2.1 + ((l.take i).map (·.npub)).sum ∧ Q l[i]) ∧
      (l.foldl f st).1 = st.1 + (l.map (·.nc)).sum ∧ (l.foldl f st).2.1 = st.2.1 + (l.map (·.npub)).sum := by
  intro l
  induction l with
  | nil => intro st h; exact ⟨h, fun i hi => absurd hi (by simp), by simp, by simp⟩
  | cons t l ih =>
    intro st h
    rw [List.foldl_cons] at h ⊢
    obtain ⟨hok, hl, h1, h2⟩ := ih (f st t) h
    obtain ⟨hst, hc, hb, hq⟩ := hf3 st t hok
    refine ⟨hst, ?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero => simpa [hc, hb] using hq
      | succ i =>
        have := hl i (by simpa using hi)
        rw [hf1, hf2] at this
        simp only [List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
        refine ⟨by omega, by omega, this.2.2⟩
    · rw [h1, hf1]; simp; omega
    · rw [h2, hf2]; simp; omega


/-- **the column layout of a shaped instance** (from `tabsOk`): `col0`/`pubBase` are the running sums of `nc`/`npub`, the tables
partition the `nc` columns and the `pubOf.size` public slots, and `pubOf` sends the `j`-th public of a table to its `j`-th public column -/
theorem layout_of_shape {XI : ExecInst} (h : J8Shape.j8ShapeOk XI = true) :
    (∀ t : Fin XI.tabs.size, XI.tabs[t].col0 = ((XI.tabs.toList.map (·.nc)).take t.1).sum ∧
      XI.tabs[t].pubBase = ((XI.tabs.toList.map (·.npub)).take t.1).sum ∧ XI.tabs[t].npub ≤ XI.tabs[t].nc ∧
      (∀ j < XI.tabs[t].npub, XI.pubOf[XI.tabs[t].pubBase + j]! = XI.tabs[t].col0 + (XI.tabs[t].nc - XI.tabs[t].npub) + j) ∧
      (∀ j < XI.tabs[t].npub, XI.colKind[XI.tabs[t].col0 + (XI.tabs[t].nc - XI.tabs[t].npub) + j]! = 2)) ∧
    (XI.tabs.toList.map (·.nc)).sum = XI.nc ∧ (XI.tabs.toList.map (·.npub)).sum = XI.pubOf.size := by
  have h1 := J8Shape.tabsOk_of_shape h
  unfold V.tabsOk at h1
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  have h2 := h1.1.1.2
  have h3 := h1.1.2
  have h4 := h1.2
  rw [← Array.foldl_toList] at h2 h3 h4
  obtain ⟨-, hl, e1, e2⟩ := fold_layout _ (fun t => t.npub ≤ t.nc ∧ (∀ j < t.npub, XI.pubOf[t.pubBase + j]! = t.col0 + (t.nc - t.npub) + j) ∧
      (∀ j < t.npub, XI.colKind[t.col0 + (t.nc - t.npub) + j]! = 2))
    (fun _ _ => rfl) (fun _ _ => rfl) (by
      intro st t hst
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hst
      refine ⟨by tauto, by tauto, by tauto, by tauto, fun j hj => ?_, fun j hj => ?_⟩
      · have := hst.2 j hj
        simpa using this
      · have hnn : t.npub ≤ t.nc := by tauto
        have hk := hst.1.2 (t.nc - t.npub + j) (by omega)
        rw [if_neg (by omega)] at hk
        simp only [Bool.and_eq_true, beq_iff_eq] at hk
        have e : t.nc - t.npub + j = (t.nc - t.npub) + j := rfl
        rw [← add_assoc] at hk
        exact hk.1) XI.tabs.toList (0, 0, true) h2
  refine ⟨fun t => ?_, by simpa using e1.symm.trans h3, by simpa using e2.symm.trans h4⟩
  have := hl t.1 (by simp)
  simp only [zero_add, List.map_take, Array.getElem_toList] at this ⊢
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩

section Part
open NockvmE2E.J8.TieJ8G (flatIdx_fst_lt flatIdx_snd_lt flatIdx_inv off_inj flatIdx_off)

variable {XI : ExecInst} (hsh : J8Shape.j8ShapeOk XI = true)
include hsh

/-- the columns of the tables partition `[0, nc)` -/
theorem col_decomp (c : ℕ) (hc : c < XI.nc) : ∃ t : Fin XI.tabs.size, ∃ n < XI.tabs[t].nc, c = XI.tabs[t].col0 + n := by
  obtain ⟨hl, hs, -⟩ := layout_of_shape hsh
  have hc' : c < (XI.tabs.toList.map (·.nc)).sum := by rw [hs]; exact hc
  have h1 := flatIdx_fst_lt _ c hc'
  have h2 := flatIdx_snd_lt _ c hc'
  have h3 := flatIdx_inv _ c hc'
  simp only [List.length_map, Array.length_toList] at h1
  refine ⟨⟨_, h1⟩, ?_⟩
  simp only [List.getElem_map] at h2
  refine ⟨_, by simpa using h2, ?_⟩
  have := (hl ⟨_, h1⟩).1
  simp only at this
  rw [this]; exact h3.symm

theorem col_inj (t t' : Fin XI.tabs.size) (n n' : ℕ) (hn : n < XI.tabs[t].nc) (hn' : n' < XI.tabs[t'].nc)
    (h : XI.tabs[t].col0 + n = XI.tabs[t'].col0 + n') : t = t' ∧ n = n' := by
  obtain ⟨hl, hs, -⟩ := layout_of_shape hsh
  have c1 := (hl t).1
  have c2 := (hl t').1
  rw [c1, c2] at h
  have := off_inj (XI.tabs.toList.map (·.nc)) t.1 t'.1 n n' (by simp) (by simp) (by simpa using hn) (by simpa using hn') h
  exact ⟨Fin.ext this.1, this.2⟩

/-- the public slots of the tables partition `[0, pubOf.size)` -/
theorem pub_decomp (s : ℕ) (hs' : s < XI.pubOf.size) : ∃ t : Fin XI.tabs.size, ∃ j < XI.tabs[t].npub, s = XI.tabs[t].pubBase + j := by
  obtain ⟨hl, -, hs⟩ := layout_of_shape hsh
  have hc' : s < (XI.tabs.toList.map (·.npub)).sum := by rw [hs]; exact hs'
  have h1 := flatIdx_fst_lt _ s hc'
  have h2 := flatIdx_snd_lt _ s hc'
  have h3 := flatIdx_inv _ s hc'
  simp only [List.length_map, Array.length_toList] at h1
  refine ⟨⟨_, h1⟩, ?_⟩
  simp only [List.getElem_map] at h2
  refine ⟨_, by simpa using h2, ?_⟩
  have := (hl ⟨_, h1⟩).2.1
  simp only at this
  rw [this]; exact h3.symm

theorem pub_inj (t t' : Fin XI.tabs.size) (j j' : ℕ) (hj : j < XI.tabs[t].npub) (hj' : j' < XI.tabs[t'].npub)
    (h : XI.tabs[t].pubBase + j = XI.tabs[t'].pubBase + j') : t = t' ∧ j = j' := by
  obtain ⟨hl, -, -⟩ := layout_of_shape hsh
  have c1 := (hl t).2.1
  have c2 := (hl t').2.1
  rw [c1, c2] at h
  have := off_inj (XI.tabs.toList.map (·.npub)) t.1 t'.1 j j' (by simp) (by simp) (by simpa using hj) (by simpa using hj') h
  exact ⟨Fin.ext this.1, this.2⟩

end Part


theorem lay_of_shape {XI : ExecInst} (h : J8Shape.j8ShapeOk XI = true) :
    (∀ c < XI.nc, XI.colKind[c]! < 3) ∧ (∀ c < XI.nc, XI.colKind[c]! = 2 → XI.blockOf[c]! = 2) ∧
      (∀ j < XI.nq, XI.blockOf[XI.nc + j]! = 3) := by
  have hl : J8Shape.layoutShapeOk XI = true := by
    unfold J8Shape.j8ShapeOk at h
    simp only [Bool.and_eq_true] at h
    tauto
  unfold J8Shape.layoutShapeOk at hl
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hl
  obtain ⟨⟨-, hc⟩, hq⟩ := hl
  refine ⟨fun c hcn => ?_, fun c hcn hk => ?_, hq⟩
  · have := hc c hcn
    by_cases h2 : XI.colKind[c]! = 2
    · omega
    · by_cases h1 : XI.colKind[c]! = 1
      · omega
      · simp only [h2, h1, if_false, Bool.and_eq_true, beq_iff_eq] at this
        omega
  · have := hc c hcn
    simpa [hk] using this

section CI
open NockvmE2E.J8.InstJ8 (Ι tabΙ Datum J8)

def locΙ : Ι → ℕ
  | Sum.inl c => c.val
  | Sum.inr (Sum.inl c) => c.val
  | Sum.inr (Sum.inr (Sum.inl c)) => c.val
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl c))) => c.val
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c)))) => c.val
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr c)))) => c.val

theorem colI_locΙ (j : Ι) : colI (tabΙ j) (locΙ j) = j := by
  rcases j with c | c | c | c | c | c <;> simp [colI, tabΙ, locΙ, Nat.mod_eq_of_lt c.2]

theorem locΙ_lt (j : Ι) : locΙ j < wOf (tabΙ j) := by
  rcases j with c | c | c | c | c | c <;> exact c.2

theorem locΙ_colI (s : Fin 6) (c : ℕ) (hc : c < wOf s) : locΙ (colI s c) = c := by
  fin_cases s <;> simp [colI, locΙ, wOf] at hc ⊢ <;> omega

variable (I : Inst) (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub)

/-- the instance table of a present column -/
noncomputable def tcol (j : PresentCols (J8 I.d I.hdk) I.R.p) : Fin I.XI.tabs.size := Fin.cast I.hT (I.R.tabC' _ j)

theorem sigma_tcol (j : PresentCols (J8 I.d I.hdk) I.R.p) : sigmaX I.XI (tcol I j) = tabΙ j.1 :=
  (I.hσ _).symm.trans (I.R.σ_tabC' _ j)

theorem tcol_colJ (t : Fin I.XI.tabs.size) (c : ℕ) :
    tcol I ⟨colI (sigmaX I.XI t) c, colI_mem I t c⟩ = t :=
  sigmaX_inj I.XI I.hsh ((sigma_tcol I _).trans (tabΙ_colI _ _))

/-- the flat column of an interface column -/
noncomputable def f0 : PresentCols (J8 I.d I.hdk) I.R.p ⊕ Fin npub → ℕ
  | Sum.inl j => I.XI.tabs[tcol I j].col0 + locΙ j.1
  | Sum.inr s => I.XI.pubOf[s.1]!

theorem w_eq (t : Fin I.XI.tabs.size) : I.XI.tabs[t].nc - I.XI.tabs[t].npub = wOf (sigmaX I.XI t) := by
  obtain ⟨-, hmem⟩ := ids_of_shape I.hsh
  have hm : I.XI.tabs[t] ∈ I.XI.tabs.toList := Array.getElem_mem_toList t.2
  have hw := J8Shape.width_of_shape I.hsh _ hm
  obtain ⟨-, e2⟩ := tabId_tabIdx _ (hmem _ hm)
  rw [hw]; exact e2

theorem f0_lt (hnpub : npub = I.XI.pubOf.size) : ∀ x, f0 I npub x < I.XI.nc := by
  have hcolB := J8Shape.hcolB_of_shape I.hsh
  have lay := layout_of_shape I.hsh
  rintro (j | s)
  · show I.XI.tabs[tcol I j].col0 + locΙ j.1 < _
    have h1 := locΙ_lt j.1
    rw [← sigma_tcol I j, ← w_eq I] at h1
    have h2 : I.XI.tabs[tcol I j].col0 + I.XI.tabs[tcol I j].nc ≤ I.XI.nc := hcolB _ (Array.getElem_mem_toList _)
    have h3 := (lay.1 (tcol I j)).2.2.1
    omega
  · show I.XI.pubOf[s.1]! < _
    obtain ⟨t, j, hj, hs⟩ := pub_decomp I.hsh s.1 (by rw [← hnpub]; exact s.2)
    rw [hs, (lay.1 t).2.2.2.1 j hj]
    have h2 : I.XI.tabs[t].col0 + I.XI.tabs[t].nc ≤ I.XI.nc := hcolB _ (Array.getElem_mem_toList _)
    have h3 := (lay.1 t).2.2.1
    omega


theorem f0_colJ (t : Fin I.XI.tabs.size) (c : ℕ) (hc : c < wOf (sigmaX I.XI t)) :
    f0 I npub (Sum.inl ⟨colI (sigmaX I.XI t) c, colI_mem I t c⟩) = I.XI.tabs[t].col0 + c := by
  have e := congrArg (fun t' : Fin I.XI.tabs.size => I.XI.tabs[t'].col0) (tcol_colJ I t c)
  show I.XI.tabs[tcol I ⟨colI (sigmaX I.XI t) c, colI_mem I t c⟩].col0 + locΙ (colI (sigmaX I.XI t) c) = _
  rw [locΙ_colI _ _ hc]
  exact congrArg (· + c) e

theorem f0_inj (hnpub : npub = I.XI.pubOf.size) : Function.Injective (f0 I npub) := by
  have lay := layout_of_shape I.hsh
  have hsh := I.hsh
  have bnd : ∀ t : Fin I.XI.tabs.size, I.XI.tabs[t].nc - I.XI.tabs[t].npub ≤ I.XI.tabs[t].nc := fun t => Nat.sub_le _ _
  have hloc : ∀ j : PresentCols (J8 I.d I.hdk) I.R.p, locΙ j.1 < I.XI.tabs[tcol I j].nc - I.XI.tabs[tcol I j].npub := fun j => by
    have h1 := locΙ_lt j.1
    rw [← sigma_tcol I j, ← w_eq I] at h1
    exact h1
  rintro (j | s) (j' | s') h
  · obtain ⟨e1, e2⟩ := col_inj hsh (tcol I j) (tcol I j') _ _ (lt_of_lt_of_le (hloc j) (bnd _))
      (lt_of_lt_of_le (hloc j') (bnd _)) h
    congr 1
    apply Subtype.ext
    have a1 := colI_locΙ j.1
    have a2 := colI_locΙ j'.1
    rw [← a1, ← a2, e2, ← sigma_tcol I j, ← sigma_tcol I j', e1]
  · exfalso
    have h' : I.XI.tabs[tcol I j].col0 + locΙ j.1 = I.XI.pubOf[s'.1]! := h
    obtain ⟨t, jj, hj, hs⟩ := pub_decomp hsh s'.1 (by rw [← hnpub]; exact s'.2)
    rw [hs, (lay.1 t).2.2.2.1 jj hj] at h'
    have h3 := (lay.1 t).2.2.1
    obtain ⟨e1, e2⟩ := col_inj hsh (tcol I j) t (locΙ j.1) (I.XI.tabs[t].nc - I.XI.tabs[t].npub + jj) (lt_of_lt_of_le (hloc j) (bnd _)) (by omega) (by rw [h']; omega)
    subst e1
    have := hloc j
    omega
  · exfalso
    have h' : I.XI.pubOf[s.1]! = I.XI.tabs[tcol I j'].col0 + locΙ j'.1 := h
    obtain ⟨t, jj, hj, hs⟩ := pub_decomp hsh s.1 (by rw [← hnpub]; exact s.2)
    rw [hs, (lay.1 t).2.2.2.1 jj hj] at h'
    have h3 := (lay.1 t).2.2.1
    obtain ⟨e1, e2⟩ := col_inj hsh t (tcol I j') (I.XI.tabs[t].nc - I.XI.tabs[t].npub + jj) (locΙ j'.1) (by omega) (lt_of_lt_of_le (hloc j') (bnd _)) (by rw [← h']; omega)
    subst e1
    have := hloc j'
    omega
  · have h' : I.XI.pubOf[s.1]! = I.XI.pubOf[s'.1]! := h
    obtain ⟨t, jj, hj, hs⟩ := pub_decomp hsh s.1 (by rw [← hnpub]; exact s.2)
    obtain ⟨t', jj', hj', hs'⟩ := pub_decomp hsh s'.1 (by rw [← hnpub]; exact s'.2)
    rw [hs, (lay.1 t).2.2.2.1 jj hj, hs', (lay.1 t').2.2.2.1 jj' hj'] at h'
    have h3 := (lay.1 t).2.2.1
    have h3' := (lay.1 t').2.2.1
    obtain ⟨e1, e2⟩ := col_inj hsh t t' (I.XI.tabs[t].nc - I.XI.tabs[t].npub + jj) (I.XI.tabs[t'].nc - I.XI.tabs[t'].npub + jj') (by omega) (by omega) (by omega)
    subst e1
    have : jj = jj' := by omega
    congr 1
    apply Fin.ext
    rw [hs, hs', this]

theorem f0_surj (hnpub : npub = I.XI.pubOf.size) : ∀ c : Fin I.XI.nc, ∃ x, f0 I npub x = c.1 := by
  have lay := layout_of_shape I.hsh
  have hpubB := J8Shape.hpubB_of_shape I.hsh
  intro c
  obtain ⟨t, n, hn, hc⟩ := col_decomp I.hsh c.1 c.2
  have h3 := (lay.1 t).2.2.1
  by_cases hw : n < I.XI.tabs[t].nc - I.XI.tabs[t].npub
  · refine ⟨Sum.inl ⟨colI (sigmaX I.XI t) n, colI_mem I t n⟩, ?_⟩
    rw [f0_colJ I npub t n (by rw [← w_eq]; exact hw), hc]
  · have hb : I.XI.tabs[t].pubBase + (n - (I.XI.tabs[t].nc - I.XI.tabs[t].npub)) < npub := by
      have : I.XI.tabs[t].pubBase + I.XI.tabs[t].npub ≤ I.XI.pubOf.size := hpubB _ (Array.getElem_mem_toList _)
      rw [hnpub]; omega
    refine ⟨Sum.inr ⟨_, hb⟩, ?_⟩
    show I.XI.pubOf[I.XI.tabs[t].pubBase + (n - (I.XI.tabs[t].nc - I.XI.tabs[t].npub))]! = _
    rw [(lay.1 t).2.2.2.1 _ (by omega), hc]
    omega


/-- **the column bijection `cI`** of the final interface (`plusJ ∘ minusT J8`) with the loaded columns -/
noncomputable def cIX (hnpub : npub = I.XI.pubOf.size) : (I.JJ npub tp hcap).ι0 ≃ Fin I.XI.nc :=
  Equiv.ofBijective (fun x : PresentCols (J8 I.d I.hdk) I.R.p ⊕ Fin npub => (⟨f0 I npub x, f0_lt I npub hnpub x⟩ : Fin I.XI.nc))
    ⟨fun a b h => f0_inj I npub hnpub (by simpa using congrArg Fin.val h),
     fun c => by obtain ⟨x, hx⟩ := f0_surj I npub hnpub c; exact ⟨x, Fin.ext hx⟩⟩

/-- `hcI_col` -/
theorem hcI_col_X (hnpub : npub = I.XI.pubOf.size) :
    ∀ (t : Fin I.XI.tabs.size) c, c < I.XI.tabs[t].nc - I.XI.tabs[t].npub →
      ((cIX I npub tp hcap hnpub (colJ I npub tp hcap t c) : Fin I.XI.nc) : ℕ) = I.XI.tabs[t].col0 + c := by
  intro t c hc
  exact f0_colJ I npub t c (by rw [← w_eq]; exact hc)

/-- `hcI_pub` -/
theorem hcI_pub_X (hnpub : npub = I.XI.pubOf.size) :
    ∀ (t : Fin I.XI.tabs.size) s, s < I.XI.tabs[t].npub →
      ((cIX I npub tp hcap hnpub (pubJ I npub tp hcap t s) : Fin I.XI.nc) : ℕ) = I.XI.pubOf[I.XI.tabs[t].pubBase + s]! := by
  intro t s hs
  have hpubB := J8Shape.hpubB_of_shape I.hsh
  have : I.XI.tabs[t].pubBase + I.XI.tabs[t].npub ≤ I.XI.pubOf.size := hpubB _ (Array.getElem_mem_toList _)
  have hlt : I.XI.tabs[t].pubBase + s < npub := by rw [hnpub]; omega
  unfold pubJ
  simp only [hlt, ↓reduceDIte]
  rfl


/-- the flat public array a reader reconstructs from the opened public values (canonical residues) -/
noncomputable def readPub (v : Fin npub → KC) : Array UInt64 :=
  Array.ofFn (fun j : Fin npub => UInt64.ofNat (HdagU.coord0 (v j)).val)

set_option maxRecDepth 20000 in
/-- **the reader `pr`** of the final interface: `plusPR` with `ppt = toKV XI.ppt`, `gen = toKV K3.gen`, and `rd = Mof` of the canonical public array -/
noncomputable def prX : PubRead (I.JJ npub tp hcap) where
  pub := Sum.elim (fun _ => false) (fun _ => true)
  ppt := Sum.elim (fun _ => 0) (fun _ => toKV I.XI.ppt)
  rd v := NockvmE2E.J8.RVUJ8.Mof I.XI.pubLay (readPub npub (fun j => v (Sum.inr j)))
  gen := toKV VF.K3.gen
  hrd v v' h := congrArg (fun w => NockvmE2E.J8.RVUJ8.Mof I.XI.pubLay (readPub npub w)) (funext fun i => h (Sum.inr i) rfl)
  hCpub := by
    intro χ M i p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp (MvPolynomial.vars_rename _ _ (show p ∈ (MvPolynomial.rename (Prod.map Sum.inl id)
      (I.Jm.C χ M i)).vars from hp))
    rfl


theorem loc_lt (j : PresentCols (J8 I.d I.hdk) I.R.p) : locΙ j.1 < I.XI.tabs[tcol I j].nc - I.XI.tabs[tcol I j].npub := by
  have h1 := locΙ_lt j.1
  rw [← sigma_tcol I j, ← w_eq I] at h1
  exact h1

/-- `hpub` -/
theorem hpub_X (hnpub : npub = I.XI.pubOf.size) :
    ∀ c, (prX I npub tp hcap).pub c = true ↔ I.XI.colKind[(cIX I npub tp hcap hnpub c).val]! = 2 := by
  have lay := layout_of_shape I.hsh
  rintro (j | s)
  · show false = true ↔ I.XI.colKind[f0 I npub (Sum.inl j)]! = 2
    simp only [Bool.false_eq_true, false_iff]
    show ¬ I.XI.colKind[I.XI.tabs[tcol I j].col0 + locΙ j.1]! = 2
    have := J8Shape.hkind_of_shape I.hsh (tcol I j) _ (loc_lt I j)
    omega
  · show true = true ↔ I.XI.colKind[I.XI.pubOf[s.1]!]! = 2
    simp only [true_iff]
    obtain ⟨t, jj, hj, hs⟩ := pub_decomp I.hsh s.1 (by rw [← hnpub]; exact s.2)
    rw [hs, (lay.1 t).2.2.2.1 jj hj]
    exact (lay.1 t).2.2.2.2 jj hj

/-- `hppt` -/
theorem hppt_X : ∀ c, (prX I npub tp hcap).pub c = true → (prX I npub tp hcap).ppt c = toKV I.XI.ppt := by
  rintro (j | s) h
  · exact absurd h (by simp [prX])
  · rfl

/-- `hgen` -/
theorem hgen_X : (prX I npub tp hcap).gen = toKV VF.K3.gen := rfl

/-- `hblkq`: the quotient columns are in block 3 -/
theorem hblkq_X (n : ℕ) (hn : n ≤ I.XI.nq) : ∀ q : Fin n, I.XI.blockOf[I.XI.nc + q.val]! = 3 :=
  fun q => (lay_of_shape I.hsh).2.2 q.val (lt_of_lt_of_le q.2 hn)

/-- `hkd` -/
theorem hkd_X : ∀ c < I.XI.nc, I.XI.colKind[c]! < 3 := (lay_of_shape I.hsh).1

/-- the block table of the loaded instance against `J8`'s `colR` (NOT implied by `j8ShapeOk`, which only bounds `blockOf ≤ 2` on kind-0
columns: a new exe conjunct `blockTabOk`,  item); the Bool twin would compare `blockOf[col0 + c]` with the literal `colR` tables -/
def BlockTab : Prop := ∀ (t : Fin I.XI.tabs.size) c, c < I.XI.tabs[t].nc - I.XI.tabs[t].npub →
  I.XI.blockOf[I.XI.tabs[t].col0 + c]! = InstJ8.colR (colI (sigmaX I.XI t) c)

/-- `hblk` from `BlockTab` and the kind-2 block (shape) -/
theorem hblk_X (hnpub : npub = I.XI.pubOf.size) (hBT : BlockTab I) :
    ∀ c, I.XI.blockOf[(cIX I npub tp hcap hnpub c).val]! = (I.JJ npub tp hcap).colRound0 c := by
  have lay := layout_of_shape I.hsh
  have hlay := lay_of_shape I.hsh
  rintro (j | s)
  · show I.XI.blockOf[I.XI.tabs[tcol I j].col0 + locΙ j.1]! = InstJ8.colR j.1
    have hj : colI (sigmaX I.XI (tcol I j)) (locΙ j.1) = j.1 := by
      rw [sigma_tcol I (j : PresentCols (J8 I.d I.hdk) I.R.p)]; exact colI_locΙ _
    have := hBT (tcol I j) (locΙ j.1) (loc_lt I j)
    rw [hj] at this
    exact this
  · show I.XI.blockOf[I.XI.pubOf[s.1]!]! = 2
    obtain ⟨t, jj, hj, hs⟩ := pub_decomp I.hsh s.1 (by rw [← hnpub]; exact s.2)
    rw [hs, (lay.1 t).2.2.2.1 jj hj]
    have hk := (lay.1 t).2.2.2.2 jj hj
    have h2 : I.XI.tabs[t].col0 + I.XI.tabs[t].nc ≤ I.XI.nc := J8Shape.hcolB_of_shape I.hsh _ (Array.getElem_mem_toList _)
    have h3 := (lay.1 t).2.2.1
    exact hlay.2.1 _ (by omega) hk


theorem zv_ofNat_val (z : ZMod NockvmE2E.Exec.p) : zv (UInt64.ofNat z.val) = z := by
  unfold zv
  have h1 : z.val < NockvmE2E.Exec.p := ZMod.val_lt z
  have h2 : NockvmE2E.Exec.p < 2 ^ 64 := by rw [p_eq]; norm_num
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa using lt_trans h1 h2)]
  exact ZMod.natCast_zmod_val z

theorem readPub_get (v : Fin npub → KC) (i : ℕ) (hi : i < npub) :
    zv (readPub npub v)[i]! = HdagU.coord0 (v ⟨i, hi⟩) := by
  have : (readPub npub v)[i]! = UInt64.ofNat (HdagU.coord0 (v ⟨i, hi⟩)).val := by
    unfold readPub
    rw [getElem!_pos _ i (by simpa using hi)]
    simp
  rw [this]; exact zv_ofNat_val _

theorem slOf_get (L : PE.PubLayout) (pub : Array UInt64) (t j : ℕ) (hp : L.present[t]! = true) (hj : j < L.lens[t]!)
    (hb : L.bases[t]! + L.lens[t]! ≤ pub.size) : (SP.slOf L pub t)[j]! = pub[L.bases[t]! + j]! := by
  unfold SP.slOf
  rw [if_pos hp]
  have h1 : j < (pub.extract L.bases[t]! (L.bases[t]! + L.lens[t]!)).size := by
    simp only [Array.size_extract]; omega
  have h2 : L.bases[t]! + j < pub.size := by omega
  rw [getElem!_pos (pub.extract L.bases[t]! (L.bases[t]! + L.lens[t]!)) j h1, getElem!_pos pub _ h2]
  simp

end CI



/-! ### the four extra shape facts from `j8ShapeXOk` -/
section ShapeX
open NockvmE2E.J8.InstJ8W (sigmaX tabIdx)

theorem nq_of_shapeX {XI : ExecInst} (h : J8Shape.j8ShapeXOk XI = true) : XI.nq = 9 := by
  simp only [J8Shape.j8ShapeXOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

theorem npub_of_shapeX {XI : ExecInst} (h : J8Shape.j8ShapeXOk XI = true) : XI.pubOf.size ≤ 926 := by
  simp only [J8Shape.j8ShapeXOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

theorem colRB_eq (a : String) (ha : a ∈ ["computeChipVCLHX", "cellChipHQKW", "walkChipJ8", "atomChipHQL", "walkChipHQK", "jetChipJ8"])
    (c : ℕ) (hc : c < wOf (tabIdx a)) : J8Shape.colRB a c = InstJ8.colR (colI (tabIdx a) c) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [J8Shape.colRB, tabIdx, colI, InstJ8.colR, wOf] at hc ⊢ <;>
    simp [Nat.mod_eq_of_lt hc, Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8.crC, Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8.crM,
      Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8.crW, Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8.crJ,
      Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8.crA]

variable (I : Inst)

/-- **`BlockTab` from `j8ShapeXOk`** -/
theorem blockTab_of_shapeX (h : J8Shape.j8ShapeXOk I.XI = true) : BlockTab I := by
  intro t c hc
  simp only [J8Shape.j8ShapeXOk, Bool.and_eq_true] at h
  have hb := h.1.2
  unfold J8Shape.blockTabOk at hb
  have := (Array.all_eq_true_iff_forall_mem.mp hb) I.XI.tabs[t] (Array.mem_def.mpr (Array.getElem_mem_toList t.2))
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at this
  rw [this c hc]
  obtain ⟨-, hmem⟩ := ids_of_shape I.hsh
  have hm : I.XI.tabs[t] ∈ I.XI.tabs.toList := Array.getElem_mem_toList t.2
  have hid := hmem _ hm
  have := colRB_eq _ hid c (by have := w_eq I t; show c < wOf (sigmaX I.XI t); omega)
  exact this

/-- the loader's public layout matches the loaded tables (`pubCheck`'s `okShape` does not check this) -/
def LayOK : Prop :=
  (∀ t : Fin I.XI.tabs.size, I.XI.pubLay.present[(sigmaX I.XI t).val]! = true ∧
      I.XI.pubLay.bases[(sigmaX I.XI t).val]! = I.XI.tabs[t].pubBase ∧ I.XI.pubLay.lens[(sigmaX I.XI t).val]! = I.XI.tabs[t].npub ∧
      I.XI.tabs[t].npub = PE.tabLens[(sigmaX I.XI t).val]!) ∧
  (∀ s : Fin 6, (∀ t : Fin I.XI.tabs.size, sigmaX I.XI t ≠ s) → I.XI.pubLay.present[s.val]! = false)

theorem tabOfId_tabIdx (a : String) (ha : a ∈ ["computeChipVCLHX", "cellChipHQKW", "walkChipJ8", "atomChipHQL", "walkChipHQK", "jetChipJ8"]) :
    PE.tabOfId a = some (tabIdx a).val := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem layOK_of_shapeX (h : J8Shape.j8ShapeXOk I.XI = true) : LayOK I := by
  simp only [J8Shape.j8ShapeXOk, Bool.and_eq_true] at h
  have hl := h.2
  unfold J8Shape.layOk at hl
  simp only [Bool.and_eq_true, beq_iff_eq] at hl
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hlens⟩, htabs⟩, hany⟩ := hl
  obtain ⟨-, hmem⟩ := ids_of_shape I.hsh
  refine ⟨fun t => ?_, fun s hs => ?_⟩
  · have hm : I.XI.tabs[t] ∈ I.XI.tabs.toList := Array.getElem_mem_toList t.2
    have := (Array.all_eq_true_iff_forall_mem.mp htabs) I.XI.tabs[t] (Array.mem_def.mpr hm)
    rw [tabOfId_tabIdx _ (hmem _ hm)] at this
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    refine ⟨this.1.1, this.1.2, ?_, this.2⟩
    show I.XI.pubLay.lens[(tabIdx I.XI.tabs[t].chip.id).val]! = _
    rw [hlens, this.2]
  · have h1 := (List.all_eq_true.mp hany) s.val (List.mem_range.mpr s.2)
    simp only [beq_iff_eq] at h1
    rw [h1]
    simp only [Array.any_eq_false, Bool.not_eq_true, beq_eq_false_iff_ne, ne_eq]
    intro i hi
    rw [tabOfId_tabIdx _ (hmem _ (Array.getElem_mem_toList hi))]
    intro hh
    exact hs ⟨i, hi⟩ (Fin.ext (Option.some.inj hh))

/-- `hcap` from the shape (`npub = pubOf.size`) -/
theorem hcap_of_shapeX (npub : ℕ) (hnpub : npub = I.XI.pubOf.size) (h : J8Shape.j8ShapeXOk I.XI = true) : I.Cap npub :=
  hcap_X I npub (by rw [hnpub]; exact npub_of_shapeX h)

/-- `hblk` from the shape -/
theorem hblk_of_shapeX (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub) (hnpub : npub = I.XI.pubOf.size)
    (h : J8Shape.j8ShapeXOk I.XI = true) :
    ∀ c, I.XI.blockOf[(cIX I npub tp hcap hnpub c).val]! = (I.JJ npub tp hcap).colRound0 c :=
  hblk_X I npub tp hcap hnpub (blockTab_of_shapeX I h)

end ShapeX

end NockvmE2E.Exec.E2EJ8P

#print axioms NockvmE2E.Exec.E2EJ8P.hpd_X
#print axioms NockvmE2E.Exec.E2EJ8P.htoPoly_X
#print axioms NockvmE2E.Exec.E2EJ8P.hNH_X
#print axioms NockvmE2E.Exec.E2EJ8P.hcap_X
#print axioms NockvmE2E.Exec.E2EJ8P.hpre0_X
#print axioms NockvmE2E.Exec.E2EJ8P.hblk_X
#print axioms NockvmE2E.Exec.E2EJ8P.hpub_X
#print axioms NockvmE2E.Exec.E2EJ8P.hcI_col_X
#print axioms NockvmE2E.Exec.E2EJ8P.hcI_pub_X
#print axioms NockvmE2E.Exec.E2EJ8P.prX
#print axioms NockvmE2E.Exec.E2EJ8P.layout_of_shape
