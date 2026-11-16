/-
the generic end-to-end layer, part 1 (this file): `InstG F J XI`, the
interface pieces `Jm`/`JJ`, the generic regroup `GflatG`, columns `colJG`/`pubJG`, the generic `hdagU_G` (the twin of `TieJ8G.hdagU_J8`
with the tie `htie` a binder), the column bijection `cIG`, the reader `prG`, the numbers, `ofJ8` with its `rfl` probes.
Part 2 is `Exec/E2EGenP.lean` (`exec_e2e_JF`, `exec_e2e_generic`).
`J`, `XI` are PARAMETERS of `InstG`, the table restriction `R` a FIELD (abstract), exactly as `TieJ8G.Inst`; no `ofIface`/`RJ8` in a statement.
-/
import NockvmE2E.Exec.ShapeF
import NockvmE2E.Exec.E2EJ8P

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open Polynomial

namespace NockvmE2E.Exec.E2EGen

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.DagSem NockvmE2E.Exec.E2ELR NockvmE2E.Exec.InstGen
open NockvmE2E.J8 NockvmE2E.Rap NockvmE2E.Deep NockvmE2E.Exec.ShapeF
open NockvmE2E.J8.TieJ8G (sizes nsK sizes_length sizes_get flatIdx_off flatIdx_fst_lt flatIdx_snd_lt flatIdx_inv off_lt off_inj tabX
  gbJ gbJ_cf chalK hslot_gen)
open NockvmE2E.J8.InstJ8 (ω0)
open Fri.Spec Domain
open scoped NNReal

/-! ## 0. numbers and layout over `shapeOkF F` (the twins of E2EJ8P's `*_of_shape`) -/

section ShapeLemmas
variable {F : Fam} {XI : ExecInst}

theorem nD_of_shapeF (h : shapeOkF F XI = true) : XI.nD = XI.k + 7 := by
  unfold shapeOkF at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  tauto

theorem hShift_of_shapeF (h : shapeOkF F XI = true) : XI.hShift = 1 := by
  unfold shapeOkF at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  tauto

/-- `hrate` -/
theorem hrate_F (h : shapeOkF F XI = true) (dF : ℕ+) (hd : dF.val = XI.d) :
    64 * (2 ^ (∑ j : Fin (XI.k + 1), ((fun _ : Fin (XI.k + 1) => (1 : ℕ+)) j).val) * dF.val) ≤ 2 ^ XI.nD := by
  rw [hd, d_of_shapeF h, nD_of_shapeF h]
  simp only [PNat.one_coe, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  rw [pow_add 2 XI.k 7, pow_add 2 XI.k 1]; norm_num; omega

/-- **the column layout of a shaped instance** (from `tabsOk`), over `shapeOkF F` -/
theorem layout_of_shapeF (h : shapeOkF F XI = true) :
    (∀ t : Fin XI.tabs.size, XI.tabs[t].col0 = ((XI.tabs.toList.map (·.nc)).take t.1).sum ∧
      XI.tabs[t].pubBase = ((XI.tabs.toList.map (·.npub)).take t.1).sum ∧ XI.tabs[t].npub ≤ XI.tabs[t].nc ∧
      (∀ j < XI.tabs[t].npub, XI.pubOf[XI.tabs[t].pubBase + j]! = XI.tabs[t].col0 + (XI.tabs[t].nc - XI.tabs[t].npub) + j) ∧
      (∀ j < XI.tabs[t].npub, XI.colKind[XI.tabs[t].col0 + (XI.tabs[t].nc - XI.tabs[t].npub) + j]! = 2)) ∧
    (XI.tabs.toList.map (·.nc)).sum = XI.nc ∧ (XI.tabs.toList.map (·.npub)).sum = XI.pubOf.size := by
  have h1 := tabsOk_of_shapeF h
  unfold V.tabsOk at h1
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  have h2 := h1.1.1.2
  have h3 := h1.1.2
  have h4 := h1.2
  rw [← Array.foldl_toList] at h2 h3 h4
  obtain ⟨-, hl, e1, e2⟩ := E2EJ8P.fold_layout _ (fun t => t.npub ≤ t.nc ∧ (∀ j < t.npub, XI.pubOf[t.pubBase + j]! = t.col0 + (t.nc - t.npub) + j) ∧
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

theorem lay_of_shapeF (h : shapeOkF F XI = true) :
    (∀ c < XI.nc, XI.colKind[c]! < 3) ∧ (∀ c < XI.nc, XI.colKind[c]! = 2 → XI.blockOf[c]! = 2) ∧
      (∀ j < XI.nq, XI.blockOf[XI.nc + j]! = 3) := by
  have hl : J8Shape.layoutShapeOk XI = true := by
    unfold shapeOkF at h
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

theorem col_decompF (h : shapeOkF F XI = true) (c : ℕ) (hc : c < XI.nc) :
    ∃ t : Fin XI.tabs.size, ∃ n < XI.tabs[t].nc, c = XI.tabs[t].col0 + n := by
  obtain ⟨hl, hs, -⟩ := layout_of_shapeF h
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

theorem col_injF (h : shapeOkF F XI = true) (t t' : Fin XI.tabs.size) (n n' : ℕ) (hn : n < XI.tabs[t].nc) (hn' : n' < XI.tabs[t'].nc)
    (he : XI.tabs[t].col0 + n = XI.tabs[t'].col0 + n') : t = t' ∧ n = n' := by
  obtain ⟨hl, hs, -⟩ := layout_of_shapeF h
  have c1 := (hl t).1
  have c2 := (hl t').1
  rw [c1, c2] at he
  have := off_inj (XI.tabs.toList.map (·.nc)) t.1 t'.1 n n' (by simp) (by simp) (by simpa using hn) (by simpa using hn') he
  exact ⟨Fin.ext this.1, this.2⟩

theorem pub_decompF (h : shapeOkF F XI = true) (s : ℕ) (hs' : s < XI.pubOf.size) :
    ∃ t : Fin XI.tabs.size, ∃ j < XI.tabs[t].npub, s = XI.tabs[t].pubBase + j := by
  obtain ⟨hl, -, hs⟩ := layout_of_shapeF h
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

/-- the chip ids of the loaded tables are pairwise distinct and admissible -/
theorem ids_of_shapeF (h : shapeOkF F XI = true) :
    (XI.tabs.toList.map (·.chip.id)).Nodup ∧ ∀ t ∈ XI.tabs.toList, t.chip.id ∈ F.ids := by
  have hm := mandatoryOk_of_shapeF h
  unfold mandatoryOkF at hm
  simp only [Bool.and_eq_true] at hm
  refine ⟨NockvmE2E.J8.TieJ8G.distinctB_nodup _ hm.1.1, fun t ht => ?_⟩
  have := hm.1.2
  simp only [List.all_eq_true] at this
  simpa using this t.chip.id (List.mem_map.mpr ⟨t, ht, rfl⟩)

theorem tabs_le_F (h : shapeOkF F XI = true) : XI.tabs.size ≤ F.ids.length := by
  obtain ⟨hnd, hmem⟩ := ids_of_shapeF h
  have hsub : (XI.tabs.toList.map (·.chip.id)) ⊆ F.ids := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    exact hmem t ht
  have := (hnd.subperm hsub).length_le
  simpa using this

/-- `nsK ≤ 2^20` from the per-chip bound and the number of admissible ids -/
theorem ns_le_F (h : shapeOkF F XI = true) (hF : F.ids.length * 100000 ≤ 2 ^ 20)
    (hsz : ∀ t : Fin XI.tabs.size, XI.tabs[t].chip.cons.size ≤ 100000) : nsK XI ≤ 2 ^ 20 := by
  unfold nsK
  have h6 := tabs_le_F h
  have : (sizes XI).sum ≤ (sizes XI).length • 100000 := by
    apply List.sum_le_card_nsmul
    intro x hx
    unfold sizes at hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    exact hsz ⟨i, by simpa using hi⟩
  rw [sizes_length] at this
  simp only [smul_eq_mul] at this
  have h7 : XI.tabs.size * 100000 ≤ F.ids.length * 100000 := Nat.mul_le_mul_right _ h6
  omega

theorem nq_of_shapeXF (h : shapeXOkF F XI = true) : XI.nq = 9 := by
  simp only [shapeXOkF, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

theorem npub_of_shapeXF (h : shapeXOkF F XI = true) : XI.pubOf.size ≤ F.pubCap := by
  simp only [shapeXOkF, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

theorem hinj_F (h : shapeOkF F XI = true) :
    Set.InjOn (fun i => zv XI.hShift * zv XI.hGen ^ i) (Finset.range XI.hN : Set ℕ) := by
  rw [hShift_of_shapeF h, zv_one]
  intro a ha b hb hab
  simp only [one_mul] at hab
  have ho := orbit_order_of_shapeF h
  have hlt : XI.hN < orderOf (zv XI.hGen) := by
    rw [ho, hN_of_shapeF h, pow_succ]; have := Nat.two_pow_pos XI.k; omega
  have ha' : a < XI.hN := by simpa using ha
  have hb' : b < XI.hN := by simpa using hb
  exact pow_injOn_Iio_orderOf (show a ∈ Set.Iio (orderOf (zv XI.hGen)) from lt_of_lt_of_le ha' hlt.le)
    (show b ∈ Set.Iio (orderOf (zv XI.hGen)) from lt_of_lt_of_le hb' hlt.le) hab

end ShapeLemmas

/-! ## 1. `InstG` -/

/-- **the generic instance bundle**: everything about a chip family `F` over the interface `J` at the loaded instance `XI` that is
not a shape/chip Bool check.  `J`, `XI` are parameters (the statement mentions their fields); the table restriction `R` is a FIELD. -/
structure InstG (F : Fam) (J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC) (XI : ExecInst) where
  hsh : shapeOkF F XI = true
  σ : Fin XI.tabs.size → Fin J.T                                   -- data
  hσinj : Function.Injective σ
  col : Fin J.T → ℕ → J.ι0                                         -- data
  loc : J.ι0 → ℕ                                                   -- data
  w : Fin J.T → ℕ                                                  -- data
  hcolT : ∀ s n, J.tabC (col s n) = s
  hcolL : ∀ j, col (J.tabC j) (loc j) = j
  hlocW : ∀ j, loc j < w (J.tabC j)
  hlocC : ∀ s c, c < w s → loc (col s c) = c
  hw : ∀ t : Fin XI.tabs.size, XI.tabs[t].nc - XI.tabs[t].npub = w (σ t)
  nloc : Fin J.T → ℕ                                               -- data
  dec : Fin J.ns ≃ (Σ s : Fin J.T, Fin (nloc s))                   -- data
  hdec : ∀ i, (dec i).1 = J.tabS i
  rt : Fin J.T → NockvmE2E.J8.TieJ8.Route                          -- data
  hrtN : ∀ s, (rt s).N = nloc s
  R : TabRestr J                                                   -- data, ABSTRACT
  hT : R.T' = XI.tabs.size
  hσR : ∀ t : Fin R.T', R.σ t = σ (Fin.cast hT t)
  hfree : J.AccOn R.q
  hr : J.r = 2
  hd4 : J.d = 4
  hoff : ∀ t (k : Fin J.r), J.off t k = zv XI.hGen ^ (k : ℕ)
  hdom : J.H = (Finset.range XI.hN).image (fun i => zv XI.hShift * zv XI.hGen ^ i)
  hdomt : ∀ t : Fin XI.tabs.size, J.Ht (σ t) = (Finset.range XI.tabs[t].hN).image (fun i => zv XI.hShift * zv XI.hGen ^ i)
  hpdeg : ∀ j c, J.pre j = some c → c.natDegree ≤ XI.hN
  hpreN : ∀ (t : Fin XI.tabs.size) c, c < w (σ t) → c ∉ (F.preIdx XI.tabs[t].chip.id).toList → J.pre (col (σ t) c) = none
  hcolR : ∀ (t : Fin XI.tabs.size) c, c < w (σ t) → F.colR XI.tabs[t].chip.id c = J.colRound0 (col (σ t) c)
  hcapι : (Fintype.card J.ι0 + F.pubCap) * 2 + 9 ≤ 2 ^ 12
  rdM : Array UInt64 → J.Msg                                       -- data

namespace InstG
variable {F : Fam} {J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC} {XI : ExecInst} (IG : InstG F J XI)

/-- `J−`: the present tables of `J` -/
noncomputable def Jm : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC := minusT J IG.R IG.hfree

/-- the cap of `plusJ` -/
def Cap (npub : ℕ) : Prop := (Fintype.card IG.Jm.ι0 + Fintype.card (Fin npub)) * IG.Jm.r + 3 * (IG.Jm.d - 1) ≤ 2 ^ 12

/-- the interface of the final theorem: `plusJ ∘ minusT` -/
noncomputable def JJ (npub : ℕ) (tp : Fin IG.Jm.T) (hcap : IG.Cap npub) :
    RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC := plusJ IG.Jm (Fin npub) tp hcap

end InstG

instance instNeZeroJJG {F : Fam} {J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC} {XI : ExecInst} (IG : InstG F J XI) (npub : ℕ)
    (tp : Fin IG.Jm.T) (hcap : IG.Cap npub) : NeZero (IG.JJ npub tp hcap).r :=
  ⟨by show J.r ≠ 0; rw [IG.hr]; norm_num⟩

/-! ## 2. the generic regroup `GflatG` -/

section Greg
variable {F : Fam} {J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC} {XI : ExecInst} (IG : InstG F J XI)

/-- the table (of the instance) of the `k`-th present constraint -/
noncomputable def tkG (k : Fin IG.R.ns') : Fin XI.tabs.size := Fin.cast IG.hT (IG.R.tabS' k)

/-- the table of `J` of the `k`-th present constraint -/
noncomputable def sOfG (k : Fin IG.R.ns') : Fin J.T := (IG.dec (IG.R.ρ k)).1
/-- its local index -/
noncomputable def lOfG (k : Fin IG.R.ns') : ℕ := ((IG.dec (IG.R.ρ k)).2 : ℕ)
/-- its (DAG gate, coordinate) -/
noncomputable def rOfG (k : Fin IG.R.ns') : ℕ × ℕ := (IG.rt (sOfG IG k)).route (lOfG IG k)

theorem sOfG_eq (k : Fin IG.R.ns') : IG.σ (tkG IG k) = sOfG IG k :=
  (IG.hσR _).symm.trans ((IG.R.hρtab k).trans (IG.hdec _).symm)

theorem lOfG_lt (k : Fin IG.R.ns') : lOfG IG k < IG.nloc (sOfG IG k) := ((IG.dec (IG.R.ρ k)).2).2

theorem rOfG_spec (k : Fin IG.R.ns') :
    (rOfG IG k).1 < (IG.rt (sOfG IG k)).nK ∧ (rOfG IG k).2 < (IG.rt (sOfG IG k)).mult (rOfG IG k).1 ∧
      (IG.rt (sOfG IG k)).jOf (rOfG IG k).1 (rOfG IG k).2 = lOfG IG k :=
  (IG.rt (sOfG IG k)).h1 _ (by rw [IG.hrtN]; exact lOfG_lt IG k)

theorem rOfG_crd_lt (k : Fin IG.R.ns') : (rOfG IG k).2 < 3 :=
  lt_of_lt_of_le (rOfG_spec IG k).2.1 ((IG.rt (sOfG IG k)).hmult _)

/-- the chips' constraint counts are the routes' DAG gate counts -/
def HSzG : Prop := ∀ t : Fin XI.tabs.size, XI.tabs[t].chip.cons.size = (IG.rt (IG.σ t)).nK

theorem rOfG_lt_cons (hsz : HSzG IG) (k : Fin IG.R.ns') : (rOfG IG k).1 < XI.tabs[tkG IG k].chip.cons.size := by
  have h := (rOfG_spec IG k).1
  rw [← sOfG_eq] at h
  rw [hsz]; exact h

theorem grp_ltG (hsz : HSzG IG) (k : Fin IG.R.ns') :
    ((sizes XI).take (tkG IG k).1).sum + (rOfG IG k).1 < nsK XI := by
  have ht : (tkG IG k).1 < (sizes XI).length := by rw [sizes_length]; exact (tkG IG k).2
  exact off_lt (sizes XI) _ _ ht (by rw [sizes_get]; exact rOfG_lt_cons IG hsz k)

theorem dec_ext (a b : Fin J.ns) (h1 : (IG.dec a).1 = (IG.dec b).1) (h2 : ((IG.dec a).2 : ℕ) = (IG.dec b).2) : a = b := by
  have : IG.dec a = IG.dec b := by
    rcases ha : IG.dec a with ⟨s, l⟩
    rcases hb : IG.dec b with ⟨s', l'⟩
    rw [ha, hb] at h1 h2
    simp only at h1 h2
    subst h1
    exact congrArg (Sigma.mk s) (Fin.ext h2)
  exact IG.dec.injective this

/-- **`G`**: the present constraint `k` (table `t'`, DAG gate `ℓ`, coordinate `κ`) goes to the flat DAG gate `off t' + ℓ`
with coordinate `κ` -/
noncomputable def GflatG (hsz : HSzG IG) : NockvmE2E.J8.Regroup IG.R.ns' (nsK XI) where
  grp k := ⟨((sizes XI).take (tkG IG k).1).sum + (rOfG IG k).1, grp_ltG IG hsz k⟩
  crd k := ⟨(rOfG IG k).2, rOfG_crd_lt IG k⟩
  hinj j j' hg hc := by
    have hg' := congrArg Fin.val hg
    have hc' := congrArg Fin.val hc
    simp only at hg' hc'
    have ht : (tkG IG j).1 < (sizes XI).length := by rw [sizes_length]; exact (tkG IG j).2
    have ht' : (tkG IG j').1 < (sizes XI).length := by rw [sizes_length]; exact (tkG IG j').2
    obtain ⟨h1, h2⟩ := off_inj (sizes XI) _ _ _ _ ht ht' (by rw [sizes_get]; exact rOfG_lt_cons IG hsz j)
      (by rw [sizes_get]; exact rOfG_lt_cons IG hsz j') hg'
    have h1' : tkG IG j = tkG IG j' := Fin.ext h1
    have hs : sOfG IG j = sOfG IG j' := by rw [← sOfG_eq, ← sOfG_eq, h1']
    have hr : rOfG IG j = rOfG IG j' := Prod.ext h2 hc'
    have e1 := (rOfG_spec IG j).2.2
    have e2 := (rOfG_spec IG j').2.2
    rw [hs, hr] at e1
    have hl : lOfG IG j = lOfG IG j' := e1.symm.trans e2
    exact IG.R.hρ (dec_ext IG _ _ hs hl)

end Greg

/-! ## 3. columns, publics of the final interface -/

section Cols
variable {F : Fam} {J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC} {XI : ExecInst} (IG : InstG F J XI)
  (npub : ℕ) (tp : Fin IG.Jm.T) (hcap : IG.Cap npub)

theorem colG_mem (t : Fin XI.tabs.size) (c : ℕ) : IG.R.p (IG.col (IG.σ t) c) :=
  (IG.R.hp _).2 ⟨Fin.cast IG.hT.symm t, by
    rw [IG.hσR]; simp only [Fin.cast_cast, Fin.cast_eq_self]; exact (IG.hcolT _ _).symm⟩

/-- the interface column of local column `c` of the instance's table `t` -/
noncomputable def colJG (t : Fin XI.tabs.size) (c : ℕ) : (IG.JJ npub tp hcap).ι0 :=
  Sum.inl ⟨IG.col (IG.σ t) c, colG_mem IG t c⟩

/-- the public column `s` of table `t` (the flat public index `pubBase + s`; a junk column out of range) -/
noncomputable def pubJG (t : Fin XI.tabs.size) (s : ℕ) : (IG.JJ npub tp hcap).ι0 :=
  if h : XI.tabs[t].pubBase + s < npub then Sum.inr ⟨XI.tabs[t].pubBase + s, h⟩ else colJG IG npub tp hcap t 0

/-- `hoff` -/
theorem hoff_G (t : Fin (IG.JJ npub tp hcap).T) (k : Fin (IG.JJ npub tp hcap).r) :
    (IG.JJ npub tp hcap).off t k = zv XI.hGen ^ k.1 := IG.hoff _ k

/-- `hdom` -/
theorem hdom_G : (IG.JJ npub tp hcap).H = (Finset.range XI.hN).image (fun i => zv XI.hShift * zv XI.hGen ^ i) := IG.hdom

/-- `hdomt` (the `tabJ` of the bundle is `Fin.cast`) -/
theorem hdomt_G (t : Fin XI.tabs.size) :
    (IG.JJ npub tp hcap).Ht (Fin.cast IG.hT.symm t) =
      (Finset.range XI.tabs[t].hN).image (fun i => zv XI.hShift * zv XI.hGen ^ i) := by
  show J.Ht (IG.R.σ (Fin.cast IG.hT.symm t)) = _
  rw [IG.hσR, Fin.cast_cast, Fin.cast_eq_self]
  exact IG.hdomt t

theorem htabS_G (hsz : HSzG IG) (j : Fin IG.R.ns') :
    (IG.JJ npub tp hcap).tabS j = Fin.cast IG.hT.symm (tabX XI ((GflatG IG hsz).grp j)) := by
  apply Fin.ext
  have ht : (tkG IG j).1 < (sizes XI).length := by rw [sizes_length]; exact (tkG IG j).2
  have := flatIdx_off (sizes XI) _ _ ht (by rw [sizes_get]; exact rOfG_lt_cons IG hsz j)
  show (IG.R.tabS' j).1 = (flatIdx (sizes XI) _).1
  rw [show ((GflatG IG hsz).grp j).1 = ((sizes XI).take (tkG IG j).1).sum + (rOfG IG j).1 from rfl, this]
  rfl

end Cols

/-- the conclusion of `TieJ8G.htie_J8`, generically (the evaluation-level tie of the regrouped constraints with the chip DAGs) -/
def HtieG {F : Fam} {J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC} {XI : ExecInst} (IG : InstG F J XI) (hsz : HSzG IG)
    (npub : ℕ) (tp : Fin IG.Jm.T) (hcap : IG.Cap npub) (pr : PubRead (IG.JJ npub tp hcap))
    (chalK : Coins (IG.JJ npub tp hcap).Φ0 NockvmE2E.Exec.KC → ℕ → NockvmE2E.Exec.KC) : Prop :=
  ∀ (i : Fin (nsK XI)) (χ : Coins (IG.JJ npub tp hcap).Φ0 NockvmE2E.Exec.KC)
    (v val : (IG.JJ npub tp hcap).ι0 × Fin (IG.JJ npub tp hcap).r → NockvmE2E.Exec.KC),
    ∑ j ∈ Finset.univ.filter (fun j : Fin IG.R.ns' => (GflatG IG hsz).grp j = i),
        gbJ ((GflatG IG hsz).crd j) *
          MvPolynomial.aeval val ((IG.JJ npub tp hcap).C χ (pr.rd (fun c => v (c, 0))) j) =
      (evalDagK XI.tabs[tabX XI i].chip
        ⟨fun c => val (colJG IG npub tp hcap (tabX XI i) c, 0),
         fun c => val (colJG IG npub tp hcap (tabX XI i) c, ⟨1 % (IG.JJ npub tp hcap).r, Nat.mod_lt _ (NeZero.pos _)⟩),
         fun s => HdagU.coord0 (v (pubJG IG npub tp hcap (tabX XI i) s, 0)), chalK χ,
         XI.tabs[tabX XI i].chip.baseCols⟩)[(flatIdx (sizes XI) i.1).2]!

/-! ## 4. the column bijection `cIG`, the reader `prG`, the numbers -/

section CI
variable {F : Fam} {J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC} {XI : ExecInst} (IG : InstG F J XI)
  (npub : ℕ) (tp : Fin IG.Jm.T) (hcap : IG.Cap npub)

/-- the instance table of a present column -/
noncomputable def tcolG (j : PresentCols J IG.R.p) : Fin XI.tabs.size := Fin.cast IG.hT (IG.R.tabC' J j)

theorem sigma_tcolG (j : PresentCols J IG.R.p) : IG.σ (tcolG IG j) = J.tabC j.1 :=
  (IG.hσR _).symm.trans (IG.R.σ_tabC' J j)

theorem tcol_colG (t : Fin XI.tabs.size) (c : ℕ) :
    tcolG IG ⟨IG.col (IG.σ t) c, colG_mem IG t c⟩ = t :=
  IG.hσinj ((sigma_tcolG IG _).trans (IG.hcolT _ _))

/-- the flat column of an interface column -/
noncomputable def f0G : PresentCols J IG.R.p ⊕ Fin npub → ℕ :=
  Sum.elim (fun j => XI.tabs[tcolG IG j].col0 + IG.loc j.1) (fun s => XI.pubOf[s.1]!)

theorem f0G_lt (hnpub : npub = XI.pubOf.size) : ∀ x, f0G IG npub x < XI.nc := by
  have hcolB := hcolB_of_shapeF IG.hsh
  have lay := layout_of_shapeF IG.hsh
  rintro (j | s)
  · show XI.tabs[tcolG IG j].col0 + IG.loc j.1 < _
    have h1 := IG.hlocW j.1
    rw [← sigma_tcolG IG j, ← IG.hw (tcolG IG j)] at h1
    have h2 : XI.tabs[tcolG IG j].col0 + XI.tabs[tcolG IG j].nc ≤ XI.nc := hcolB _ (Array.getElem_mem_toList _)
    have h3 := (lay.1 (tcolG IG j)).2.2.1
    omega
  · show XI.pubOf[s.1]! < _
    obtain ⟨t, j, hj, hs⟩ := pub_decompF IG.hsh s.1 (by rw [← hnpub]; exact s.2)
    rw [hs, (lay.1 t).2.2.2.1 j hj]
    have h2 : XI.tabs[t].col0 + XI.tabs[t].nc ≤ XI.nc := hcolB _ (Array.getElem_mem_toList _)
    have h3 := (lay.1 t).2.2.1
    omega

theorem f0G_colJ (t : Fin XI.tabs.size) (c : ℕ) (hc : c < IG.w (IG.σ t)) :
    f0G IG npub (Sum.inl ⟨IG.col (IG.σ t) c, colG_mem IG t c⟩) = XI.tabs[t].col0 + c := by
  have e := congrArg (fun t' : Fin XI.tabs.size => XI.tabs[t'].col0) (tcol_colG IG t c)
  show XI.tabs[tcolG IG ⟨IG.col (IG.σ t) c, colG_mem IG t c⟩].col0 + IG.loc (IG.col (IG.σ t) c) = _
  rw [IG.hlocC _ _ hc]
  exact congrArg (· + c) e

theorem pub_injF (h : shapeOkF F XI = true) (t t' : Fin XI.tabs.size) (j j' : ℕ) (hj : j < XI.tabs[t].npub) (hj' : j' < XI.tabs[t'].npub)
    (he : XI.tabs[t].pubBase + j = XI.tabs[t'].pubBase + j') : t = t' ∧ j = j' := by
  obtain ⟨hl, -, -⟩ := layout_of_shapeF h
  have c1 := (hl t).2.1
  have c2 := (hl t').2.1
  rw [c1, c2] at he
  have := off_inj (XI.tabs.toList.map (·.npub)) t.1 t'.1 j j' (by simp) (by simp) (by simpa using hj) (by simpa using hj') he
  exact ⟨Fin.ext this.1, this.2⟩

theorem f0G_inj (hnpub : npub = XI.pubOf.size) : Function.Injective (f0G IG npub) := by
  have lay := layout_of_shapeF IG.hsh
  have hsh := IG.hsh
  have bnd : ∀ t : Fin XI.tabs.size, XI.tabs[t].nc - XI.tabs[t].npub ≤ XI.tabs[t].nc := fun t => Nat.sub_le _ _
  have hloc : ∀ j : PresentCols J IG.R.p, IG.loc j.1 < XI.tabs[tcolG IG j].nc - XI.tabs[tcolG IG j].npub := fun j => by
    have h1 := IG.hlocW j.1
    rw [← sigma_tcolG IG j, ← IG.hw (tcolG IG j)] at h1
    exact h1
  rintro (j | s) (j' | s') h
  · obtain ⟨e1, e2⟩ := col_injF hsh (tcolG IG j) (tcolG IG j') _ _ (lt_of_lt_of_le (hloc j) (bnd _))
      (lt_of_lt_of_le (hloc j') (bnd _)) h
    congr 1
    apply Subtype.ext
    have a1 := IG.hcolL j.1
    have a2 := IG.hcolL j'.1
    rw [← a1, ← a2, e2, ← sigma_tcolG IG j, ← sigma_tcolG IG j', e1]
  · exfalso
    have h' : XI.tabs[tcolG IG j].col0 + IG.loc j.1 = XI.pubOf[s'.1]! := h
    obtain ⟨t, jj, hj, hs⟩ := pub_decompF hsh s'.1 (by rw [← hnpub]; exact s'.2)
    rw [hs, (lay.1 t).2.2.2.1 jj hj] at h'
    have h3 := (lay.1 t).2.2.1
    obtain ⟨e1, e2⟩ := col_injF hsh (tcolG IG j) t (IG.loc j.1) (XI.tabs[t].nc - XI.tabs[t].npub + jj) (lt_of_lt_of_le (hloc j) (bnd _)) (by omega) (by rw [h']; omega)
    subst e1
    have := hloc j
    omega
  · exfalso
    have h' : XI.pubOf[s.1]! = XI.tabs[tcolG IG j'].col0 + IG.loc j'.1 := h
    obtain ⟨t, jj, hj, hs⟩ := pub_decompF hsh s.1 (by rw [← hnpub]; exact s.2)
    rw [hs, (lay.1 t).2.2.2.1 jj hj] at h'
    have h3 := (lay.1 t).2.2.1
    obtain ⟨e1, e2⟩ := col_injF hsh t (tcolG IG j') (XI.tabs[t].nc - XI.tabs[t].npub + jj) (IG.loc j'.1) (by omega) (lt_of_lt_of_le (hloc j') (bnd _)) (by rw [← h']; omega)
    subst e1
    have := hloc j'
    omega
  · have h' : XI.pubOf[s.1]! = XI.pubOf[s'.1]! := h
    obtain ⟨t, jj, hj, hs⟩ := pub_decompF hsh s.1 (by rw [← hnpub]; exact s.2)
    obtain ⟨t', jj', hj', hs'⟩ := pub_decompF hsh s'.1 (by rw [← hnpub]; exact s'.2)
    rw [hs, (lay.1 t).2.2.2.1 jj hj, hs', (lay.1 t').2.2.2.1 jj' hj'] at h'
    have h3 := (lay.1 t).2.2.1
    have h3' := (lay.1 t').2.2.1
    obtain ⟨e1, e2⟩ := col_injF hsh t t' (XI.tabs[t].nc - XI.tabs[t].npub + jj) (XI.tabs[t'].nc - XI.tabs[t'].npub + jj') (by omega) (by omega) (by omega)
    subst e1
    have : jj = jj' := by omega
    congr 1
    apply Fin.ext
    rw [hs, hs', this]

theorem f0G_surj (hnpub : npub = XI.pubOf.size) : ∀ c : Fin XI.nc, ∃ x, f0G IG npub x = c.1 := by
  have lay := layout_of_shapeF IG.hsh
  have hpubB := hpubB_of_shapeF IG.hsh
  intro c
  obtain ⟨t, n, hn, hc⟩ := col_decompF IG.hsh c.1 c.2
  have h3 := (lay.1 t).2.2.1
  by_cases hw : n < XI.tabs[t].nc - XI.tabs[t].npub
  · refine ⟨Sum.inl ⟨IG.col (IG.σ t) n, colG_mem IG t n⟩, ?_⟩
    rw [f0G_colJ IG npub t n (by rw [← IG.hw]; exact hw), hc]
  · have hb : XI.tabs[t].pubBase + (n - (XI.tabs[t].nc - XI.tabs[t].npub)) < npub := by
      have : XI.tabs[t].pubBase + XI.tabs[t].npub ≤ XI.pubOf.size := hpubB _ (Array.getElem_mem_toList _)
      rw [hnpub]; omega
    refine ⟨Sum.inr ⟨_, hb⟩, ?_⟩
    show XI.pubOf[XI.tabs[t].pubBase + (n - (XI.tabs[t].nc - XI.tabs[t].npub))]! = _
    rw [(lay.1 t).2.2.2.1 _ (by omega), hc]
    omega

/-- **the column bijection `cI`** of the final interface (`plusJ ∘ minusT J`) with the loaded columns -/
noncomputable def cIG (hnpub : npub = XI.pubOf.size) : (IG.JJ npub tp hcap).ι0 ≃ Fin XI.nc :=
  Equiv.ofBijective (fun x : PresentCols J IG.R.p ⊕ Fin npub => (⟨f0G IG npub x, f0G_lt IG npub hnpub x⟩ : Fin XI.nc))
    ⟨fun a b h => f0G_inj IG npub hnpub (by simpa using congrArg Fin.val h),
     fun c => by obtain ⟨x, hx⟩ := f0G_surj IG npub hnpub c; exact ⟨x, Fin.ext hx⟩⟩

/-- `hcI_col` -/
theorem hcI_col_G (hnpub : npub = XI.pubOf.size) :
    ∀ (t : Fin XI.tabs.size) c, c < XI.tabs[t].nc - XI.tabs[t].npub →
      ((cIG IG npub tp hcap hnpub (colJG IG npub tp hcap t c) : Fin XI.nc) : ℕ) = XI.tabs[t].col0 + c := by
  intro t c hc
  exact f0G_colJ IG npub t c (by rw [← IG.hw]; exact hc)

/-- `hcI_pub` -/
theorem hcI_pub_G (hnpub : npub = XI.pubOf.size) :
    ∀ (t : Fin XI.tabs.size) s, s < XI.tabs[t].npub →
      ((cIG IG npub tp hcap hnpub (pubJG IG npub tp hcap t s) : Fin XI.nc) : ℕ) = XI.pubOf[XI.tabs[t].pubBase + s]! := by
  intro t s hs
  have hpubB := hpubB_of_shapeF IG.hsh
  have : XI.tabs[t].pubBase + XI.tabs[t].npub ≤ XI.pubOf.size := hpubB _ (Array.getElem_mem_toList _)
  have hlt : XI.tabs[t].pubBase + s < npub := by rw [hnpub]; omega
  unfold pubJG
  simp only [hlt, ↓reduceDIte]
  rfl

set_option maxRecDepth 20000 in
/-- **the reader `pr`** of the final interface: `ppt = toKV XI.ppt`, `gen = toKV K3.gen`, `rd = IG.rdM` of the canonical public array -/
noncomputable def prG : PubRead (IG.JJ npub tp hcap) where
  pub := Sum.elim (fun _ => false) (fun _ => true)
  ppt := Sum.elim (fun _ => 0) (fun _ => toKV XI.ppt)
  rd v := IG.rdM (E2EJ8P.readPub npub (fun j => v (Sum.inr j)))
  gen := toKV VF.K3.gen
  hrd v v' h := congrArg (fun w => IG.rdM (E2EJ8P.readPub npub w)) (funext fun i => h (Sum.inr i) rfl)
  hCpub := by
    intro χ M i p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp (MvPolynomial.vars_rename _ _ (show p ∈ (MvPolynomial.rename (Prod.map Sum.inl id)
      (IG.Jm.C χ M i)).vars from hp))
    rfl

theorem loc_ltG (j : PresentCols J IG.R.p) : IG.loc j.1 < XI.tabs[tcolG IG j].nc - XI.tabs[tcolG IG j].npub := by
  have h1 := IG.hlocW j.1
  rw [← sigma_tcolG IG j, ← IG.hw (tcolG IG j)] at h1
  exact h1

/-- `hpub` -/
theorem hpub_G (hnpub : npub = XI.pubOf.size) (cI : (IG.JJ npub tp hcap).ι0 ≃ Fin XI.nc)
    (hv : ∀ x, ((cI x : Fin XI.nc) : ℕ) = f0G IG npub x) :
    ∀ c, (prG IG npub tp hcap).pub c = true ↔ XI.colKind[(cI c).val]! = 2 := by
  have lay := layout_of_shapeF IG.hsh
  rintro (j | s)
  · erw [hv]
    show false = true ↔ XI.colKind[f0G IG npub (Sum.inl j)]! = 2
    simp only [Bool.false_eq_true, false_iff]
    show ¬ XI.colKind[XI.tabs[tcolG IG j].col0 + IG.loc j.1]! = 2
    have := hkind_of_shapeF IG.hsh (tcolG IG j) _ (loc_ltG IG j)
    omega
  · erw [hv]
    show true = true ↔ XI.colKind[XI.pubOf[s.1]!]! = 2
    simp only [true_iff]
    obtain ⟨t, jj, hj, hs⟩ := pub_decompF IG.hsh s.1 (by rw [← hnpub]; exact s.2)
    rw [hs, (lay.1 t).2.2.2.1 jj hj]
    exact (lay.1 t).2.2.2.2 jj hj

/-- `hppt` -/
theorem hppt_G : ∀ c, (prG IG npub tp hcap).pub c = true → (prG IG npub tp hcap).ppt c = toKV XI.ppt := by
  rintro (j | s) h
  · exact absurd h (by simp [prG])
  · rfl

/-- `hgen` -/
theorem hgen_G : (prG IG npub tp hcap).gen = toKV VF.K3.gen := rfl

/-- `hblkq`: the quotient columns are in block 3 -/
theorem hblkq_F (h : shapeOkF F XI = true) (n : ℕ) (hn : n ≤ XI.nq) : ∀ q : Fin n, XI.blockOf[XI.nc + q.val]! = 3 :=
  fun q => (lay_of_shapeF h).2.2 q.val (lt_of_lt_of_le q.2 hn)

/-- `hkd` -/
theorem hkd_F (h : shapeOkF F XI = true) : ∀ c < XI.nc, XI.colKind[c]! < 3 := (lay_of_shapeF h).1

/-- the block table of the loaded instance against `J`'s `colRound0` -/
def BlockTabG : Prop := ∀ (t : Fin XI.tabs.size) c, c < XI.tabs[t].nc - XI.tabs[t].npub →
  XI.blockOf[XI.tabs[t].col0 + c]! = J.colRound0 (IG.col (IG.σ t) c)

theorem blockTab_of_shapeXF (h : shapeXOkF F XI = true) : BlockTabG IG := by
  intro t c hc
  simp only [shapeXOkF, Bool.and_eq_true] at h
  have hb := h.1.2
  unfold blockTabOkF at hb
  have := (Array.all_eq_true_iff_forall_mem.mp hb) XI.tabs[t] (Array.mem_def.mpr (Array.getElem_mem_toList t.2))
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at this
  rw [this c hc]
  exact IG.hcolR t c (by rw [← IG.hw]; exact hc)

/-- `hblk` -/
theorem hblk_G (hnpub : npub = XI.pubOf.size) (hBT : BlockTabG IG) (cI : (IG.JJ npub tp hcap).ι0 ≃ Fin XI.nc)
    (hv : ∀ x, ((cI x : Fin XI.nc) : ℕ) = f0G IG npub x) :
    ∀ c, XI.blockOf[(cI c).val]! = (IG.JJ npub tp hcap).colRound0 c := by
  have lay := layout_of_shapeF IG.hsh
  have hlay := lay_of_shapeF IG.hsh
  rintro (j | s)
  · erw [hv]
    show XI.blockOf[XI.tabs[tcolG IG j].col0 + IG.loc j.1]! = J.colRound0 j.1
    have hj : IG.col (IG.σ (tcolG IG j)) (IG.loc j.1) = j.1 := by
      rw [sigma_tcolG IG j]; exact IG.hcolL _
    have := hBT (tcolG IG j) (IG.loc j.1) (loc_ltG IG j)
    rw [hj] at this
    exact this
  · erw [hv]
    show XI.blockOf[XI.pubOf[s.1]!]! = 2
    obtain ⟨t, jj, hj, hs⟩ := pub_decompF IG.hsh s.1 (by rw [← hnpub]; exact s.2)
    rw [hs, (lay.1 t).2.2.2.1 jj hj]
    have hk := (lay.1 t).2.2.2.2 jj hj
    have h2 : XI.tabs[t].col0 + XI.tabs[t].nc ≤ XI.nc := hcolB_of_shapeF IG.hsh _ (Array.getElem_mem_toList _)
    have h3 := (lay.1 t).2.2.1
    exact hlay.2.1 _ (by omega) hk

theorem hblk_of_shapeXF (hnpub : npub = XI.pubOf.size) (h : shapeXOkF F XI = true) (cI : (IG.JJ npub tp hcap).ι0 ≃ Fin XI.nc)
    (hv : ∀ x, ((cI x : Fin XI.nc) : ℕ) = f0G IG npub x) :
    ∀ c, XI.blockOf[(cI c).val]! = (IG.JJ npub tp hcap).colRound0 c :=
  hblk_G IG npub tp hcap hnpub (blockTab_of_shapeXF IG h) cI hv

/-- any column bijection with the layout of `hcI_col`/`hcI_pub` is `f0G` -/
theorem cI_val_G (hnpub : npub = XI.pubOf.size) (cI : (IG.JJ npub tp hcap).ι0 ≃ Fin XI.nc)
    (hcol : ∀ (t : Fin XI.tabs.size) c, c < XI.tabs[t].nc - XI.tabs[t].npub →
      ((cI (colJG IG npub tp hcap t c) : Fin XI.nc) : ℕ) = XI.tabs[t].col0 + c)
    (hpb : ∀ (t : Fin XI.tabs.size) s, s < XI.tabs[t].npub →
      ((cI (pubJG IG npub tp hcap t s) : Fin XI.nc) : ℕ) = XI.pubOf[XI.tabs[t].pubBase + s]!) :
    ∀ x, ((cI x : Fin XI.nc) : ℕ) = f0G IG npub x := by
  rintro (j | s)
  · have e : colJG IG npub tp hcap (tcolG IG j) (IG.loc j.1) = Sum.inl j := by
      apply congrArg Sum.inl
      apply Subtype.ext
      show IG.col (IG.σ (tcolG IG j)) (IG.loc j.1) = j.1
      rw [sigma_tcolG IG j]; exact IG.hcolL _
    have h := hcol _ _ (loc_ltG IG j)
    rw [e] at h
    exact h
  · obtain ⟨t, jj, hj, hs⟩ := pub_decompF IG.hsh s.1 (by rw [← hnpub]; exact s.2)
    have hlt : XI.tabs[t].pubBase + jj < npub := by rw [← hs]; exact s.2
    have e : pubJG IG npub tp hcap t jj = Sum.inr s := by
      unfold pubJG
      simp only [hlt, ↓reduceDIte]
      exact congrArg Sum.inr (Fin.ext hs.symm)
    have h := hpb t jj hj
    rw [e] at h
    rw [h]
    show _ = XI.pubOf[s.1]!
    rw [hs]

/-- `hpre0`: kind-0 columns are not fixed columns -/
theorem hpre0_G : ∀ (t : Fin XI.tabs.size) c, c < XI.tabs[t].nc - XI.tabs[t].npub →
    XI.colKind[XI.tabs[t].col0 + c]! = 0 → (IG.JJ npub tp hcap).pre (colJG IG npub tp hcap t c) = none := by
  intro t c hc hk
  have hpk := preKindOk_of_shapeF IG.hsh
  unfold preKindOkF at hpk
  have := (Array.all_eq_true_iff_forall_mem.mp hpk) XI.tabs[t] (Array.mem_def.mpr (Array.getElem_mem_toList t.2))
  simp only [List.all_eq_true, List.mem_range] at this
  have hpk' := this c hc
  rw [hk] at hpk'
  have hnot : c ∉ (F.preIdx XI.tabs[t].chip.id).toList := by
    intro hmem'
    have : (F.preIdx XI.tabs[t].chip.id).contains c = true := by
      rw [Array.contains_iff_mem]; exact Array.mem_toList_iff.mp hmem'
    rw [this] at hpk'
    simp at hpk'
  exact IG.hpreN t c (by rw [← IG.hw]; exact hc) hnot

/-- the interface domain `H` has `hN` points -/
theorem card_H_G : (IG.JJ npub tp hcap).H.card = XI.hN := by
  rw [hdom_G IG npub tp hcap]
  exact Finset.card_image_of_injOn (by simpa using hinj_F IG.hsh) |>.trans (Finset.card_range _)

/-- `hNH`: `friBound s1 dF = 2^(k+1) = hN ≤ |H|` (`dF = 1`) -/
theorem hNH_G (dF : ℕ+) (hd : dF.val = XI.d) :
    friBound (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) dF ≤ (IG.JJ npub tp hcap).H.card := by
  rw [card_H_G, show friBound (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) dF = 2 ^ (XI.k + 1) by
    unfold friBound
    rw [hd, d_of_shapeF IG.hsh]
    simp; rfl, hN_of_shapeF IG.hsh]

/-- `hpd` -/
theorem hpd_G : ∀ j c, (IG.JJ npub tp hcap).pre j = some c → c.natDegree ≤ (IG.JJ npub tp hcap).H.card := by
  intro j c h
  rw [card_H_G]
  rcases j with ⟨jj, hj⟩ | j
  · exact IG.hpdeg jj c h
  · have h0 : (none : Option (ZMod NockvmE2E.Exec.p)[X]) = some c := h
    cases h0

/-- `hcap` -/
theorem hcap_G (hnp : npub ≤ F.pubCap) : IG.Cap npub := by
  unfold InstG.Cap
  have h1 : Fintype.card IG.Jm.ι0 ≤ Fintype.card J.ι0 := Fintype.card_subtype_le _
  have h2 : IG.Jm.r = 2 := IG.hr
  have h3 : IG.Jm.d = 4 := IG.hd4
  have h4 := IG.hcapι
  rw [h2, h3, Fintype.card_fin]
  omega

theorem hcap_of_shapeXF (hnpub : npub = XI.pubOf.size) (h : shapeXOkF F XI = true) : IG.Cap npub :=
  hcap_G IG npub (by rw [hnpub]; exact npub_of_shapeXF h)

end CI

/-- `hm12` from the interface cap `cap_m` -/
theorem hm12_G (J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC) {nc m : ℕ} (cI : J.ι0 ≃ Fin nc)
    (hm : m + 1 = nc * J.r + 3 * (J.d - 1)) : m + 1 ≤ 2 ^ 12 := by
  have hc : Fintype.card J.ι0 = nc := by rw [Fintype.card_congr cI, Fintype.card_fin]
  have hcap' := J.cap_m
  rw [hc] at hcap'
  rw [hm]
  exact hcap'


/-! ## 4b. `hdagU_G`: the twin of `TieJ8G.hdagU_J8` with the tie `htie` a binder -/

section HdagUG
open NockvmE2E.Exec.Cover NockvmE2E.Succ NockvmE2E.Deep Fri.Spec Domain
open scoped NNReal
variable {F : Fam} {J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC} {XI : ExecInst} (IG : InstG F J XI)
  (npub : ℕ) (tp : Fin IG.Jm.T) (hcap : IG.Cap npub)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- **`hdagU` at a generic interface**: the `hdagU_of_tie` conclusion for `plusJ ∘ minusT R J` with the regroup `GflatG`; the tie `htie`
(evaluation level, per chip) is a hypothesis; everything else is proved from `shapeOkF`, `IG` and the named layout hypotheses. -/
theorem hdagU_G (hsz : HSzG IG) (hnpub : npub = XI.pubOf.size) (pr : PubRead (IG.JJ npub tp hcap)) {n : ℕ}
    (ω : SmoothCosetFftDomain n KC) (δ : NNReal) (N : ℕ) (hNH : N ≤ (IG.JJ npub tp hcap).H.card)
    (hpd : ∀ j c, (IG.JJ npub tp hcap).pre j = some c → c.natDegree ≤ (IG.JJ npub tp hcap).H.card) {n0 n1 : ℕ}
    (sl0 : {i : Fin (extFrame (IG.JJ npub tp hcap).Φ0 2).n // (extFrame (IG.JJ npub tp hcap).Φ0 2).sampledAfter i = 0} ≃ Fin n0)
    (sl1 : {i : Fin (extFrame (IG.JJ npub tp hcap).Φ0 2).n // (extFrame (IG.JJ npub tp hcap).Φ0 2).sampledAfter i = 1} ≃ Fin n1)
    (hn0 : XI.nCoins[0]! = n0) (hn1 : XI.nCoins[1]! = n1)
    (htie : HtieG IG hsz npub tp hcap pr (chalK (IG.JJ npub tp hcap).Φ0 sl0 sl1))
    (cI : (IG.JJ npub tp hcap).ι0 ≃ Fin XI.nc)
    (hcI_col : ∀ (t : Fin XI.tabs.size) c, c < XI.tabs[t].nc - XI.tabs[t].npub →
      ((cI (colJG IG npub tp hcap t c) : Fin XI.nc) : ℕ) = XI.tabs[t].col0 + c)
    (hcI_pub : ∀ (t : Fin XI.tabs.size) s, s < XI.tabs[t].npub →
      ((cI (pubJG IG npub tp hcap t s) : Fin XI.nc) : ℕ) = XI.pubOf[XI.tabs[t].pubBase + s]!)
    (hpre0 : ∀ (t : Fin XI.tabs.size) c, c < XI.tabs[t].nc - XI.tabs[t].npub →
      XI.colKind[XI.tabs[t].col0 + c]! = 0 → (IG.JJ npub tp hcap).pre (colJG IG npub tp hcap t c) = none)
    (hcur1 : ∀ (t : Fin XI.tabs.size) c, c < XI.tabs[t].nc - XI.tabs[t].npub → XI.colKind[XI.tabs[t].col0 + c]! = 1 →
      (IG.JJ npub tp hcap).pre (colJG IG npub tp hcap t c) = some (((List.range XI.pre[XI.tabs[t].col0 + c]!.size).map fun m =>
        Polynomial.monomial m (zv (XI.pre[XI.tabs[t].col0 + c]!)[m]!)).sum)) :
    ∀ (c0 : Block (extFrame (IG.JJ npub tp hcap).Φ0 2) KC 0) (c1 : Block (extFrame (IG.JJ npub tp hcap).Φ0 2) KC 1)
      (c2 : Block (extFrame (IG.JJ npub tp hcap).Φ0 2) KC 2) (c3 : Block (extFrame (IG.JJ npub tp hcap).Φ0 2) KC 3)
      (ζ : VF.K3) (vT : Array (Array VF.K3)),
      CanonIn (slotsAt XI (blockEnc sl0 c0) (blockEnc sl1 c1)) ζ vT →
      ∀ i : Fin (((deepParamsJ (IG.JJ npub tp hcap) pr ω δ N hNH hpd).regroup (GflatG IG hsz) gbJ)).ns,
        (termsAt XI (slotsAt XI (blockEnc sl0 c0) (blockEnc sl1 c1)) ζ vT)[i.1]? =
          some (((airJ (IG.JJ npub tp hcap) pr ω δ N hNH hpd).regroup (GflatG IG hsz) gbJ).Cv
            (chiOfBlocks c0 c1 c2 c3) (toKV ζ) i (vTOfG XI cI (IG.JJ npub tp hcap).r vT)) := by
  obtain ⟨hread, hcanon, hpreC, hS, hle, hcolB, hpubB, hnpubB, hkind, hr2⟩ := hdagU_shape_of_F IG.hsh
  refine HdagU.hdagU_of_tie (IG.JJ npub tp hcap) pr ω δ N hNH hpd XI (GflatG IG hsz) gbJ (blockEnc sl0) (blockEnc sl1)
    (vTOfG XI cI (IG.JJ npub tp hcap).r) rfl (tabX XI) (fun t => Fin.cast IG.hT.symm t) (htabS_G IG npub tp hcap hsz)
    (fun _ => rfl) (colJG IG npub tp hcap) (pubJG IG npub tp hcap) hread hcanon hpreC hS hle hcolB hpubB hnpubB hkind ?_ hcur1 ?_ hr2 IG.hr
    (fun t k => hoff_G IG npub tp hcap t k) (chalK (IG.JJ npub tp hcap).Φ0 sl0 sl1) ?_ (hdom_G IG npub tp hcap)
    (fun t => hdomt_G IG npub tp hcap t) (hinj_F IG.hsh) htie
  · intro t c hc hk
    refine ⟨hpre0 t c hc hk, fun vT k => ?_⟩
    have e := hcI_col t c hc
    have hk' : XI.colKind[(cI (colJG IG npub tp hcap t c) : ℕ)]! = 0 := by rw [e]; exact hk
    simp only [vTOfG, hk', e]
    rw [if_neg (fun h2 => by have := hk.symm.trans h2; omega)]
  · intro t s vT hs
    have e := hcI_pub t s hs
    simp only [vTOfG]
    rw [e]
    simp
  · intro c0 c1 c2 c3 q hq
    exact hslot_gen _ XI (derived_of_shapeF IG.hsh) hn0 hn1 sl0 sl1 c0 c1 c2 c3 q (by have hc19 := coins19_of_shapeF IG.hsh; subst hn0 hn1; omega)

end HdagUG

/-! ## 5. the J-8 instance `InstG.ofJ8` (vacuity witness: an `Inst` exists exactly when J-8 does) and the `rfl` probes -/

section J8
open NockvmE2E.J8.InstJ8 (J8 hNof)
open NockvmE2E.J8.InstJ8W (sigmaX tabIdx)
open NockvmE2E.J8.TieJ8G (hShift_of_shape HtOf_eq hNof_tab)

set_option maxRecDepth 8000 in
/-- **`hpdeg` at J-8**: every fixed column of `J8` is an interpolant over `n_t ≤ hN` nodes (the body of `E2EJ8P.hpd_X`) -/
theorem hpdeg_J8 (I : NockvmE2E.J8.TieJ8G.Inst) :
    ∀ j c, (J8 I.d I.hdk).pre j = some c → c.natDegree ≤ I.XI.hN := by
  intro j c h
  have h' : NockvmE2E.J8.InstJ8.preJ I.d j = some c := h
  have hsh := I.hsh
  have hk1 : 1 ≤ I.XI.hN := by rw [J8Shape.hN_of_shape hsh]; exact Nat.one_le_two_pow
  obtain ⟨e1, e2, e3, e4, e5, e6, n1, n2, n3, n4, n5, n6⟩ := E2EJ8P.pb_facts I.XI hsh I.d.Pb I.hd hk1
  have hi : ∀ {n : ℕ} (nodes : Fin n → ZMod NockvmE2E.J8.InstJ8.P), (∀ i, nodes i = ω0 I.XI ^ (i : ℕ)) → n ≤ I.XI.hN →
      Function.Injective nodes := fun nodes e hn a b hab => NockvmE2E.J8.InstJ8.inj_pows hsh hn (by simpa [e] using hab)
  rcases j with c | c | c | c | c | c
  · refine (E2EJ8P.preOf_deg h' ?_).trans n1
    intro j; fin_cases j <;> exact E2EJ8P.natDeg_interp_le _ (hi _ e1 n1) _
  · refine (E2EJ8P.preOf_deg h' ?_).trans n2
    intro j; fin_cases j <;> exact E2EJ8P.natDeg_interp_le _ (hi _ e2 n2) _
  · refine (E2EJ8P.preOf_deg h' ?_).trans n3
    intro j; fin_cases j <;> exact E2EJ8P.natDeg_interp_le _ (hi _ e3 n3) _
  · refine (E2EJ8P.preOf_deg h' ?_).trans n4
    intro j; exact E2EJ8P.natDeg_interp_le _ (hi _ e4 n4) _
  · refine (E2EJ8P.preOf_deg h' ?_).trans n5
    intro j; fin_cases j <;> exact E2EJ8P.natDeg_interp_le _ (hi _ e5 n5) _
  · refine (E2EJ8P.preOf_deg h' ?_).trans n6
    intro j; fin_cases j <;> exact E2EJ8P.natDeg_interp_le _ (hi _ e6 n6) _

/-- `hdomt` at J-8 (the body of `TieJ8G.hdomt_J8`, at `σ t` instead of `R.σ (cast t)`) -/
theorem hdomt_J8' (I : NockvmE2E.J8.TieJ8G.Inst) (t : Fin I.XI.tabs.size) :
    (J8 I.d I.hdk).Ht (sigmaX I.XI t) = (Finset.range I.XI.tabs[t].hN).image
      (fun i => zv I.XI.hShift * zv I.XI.hGen ^ i) := by
  have hs : sigmaX I.XI t = 5 → (NockvmE2E.J8.InstJ8.tabOf I.XI "walkChipHQK").isSome = true := by
    intro h5
    have h1 := NockvmE2E.J8.TieJ8G.tabId_sigmaX I.XI I.hsh t
    rw [h5] at h1
    have h2 : I.XI.tabs[t].chip.id = "walkChipHQK" := h1.symm
    rw [h2.symm, NockvmE2E.J8.TieJ8G.find_tab I.XI I.hsh]
    rfl
  show NockvmE2E.J8.InstJ8.HtOf I.d (sigmaX I.XI t) = _
  rw [HtOf_eq I _ hs, hNof_tab I.XI I.hsh, hShift_of_shape I.hsh, zv_one]
  simp only [one_mul]
  rfl

/-- **`InstG.ofJ8`**: the generic instance bundle at the J-8 interface, from a `TieJ8G.Inst` (the vacuity instance of `InstG`) -/
noncomputable def InstG.ofJ8 (I : NockvmE2E.J8.TieJ8G.Inst) : InstG famJ8 (J8 I.d I.hdk) I.XI where
  hsh := I.hsh
  σ := sigmaX I.XI
  hσinj := NockvmE2E.J8.TieJ8G.sigmaX_inj I.XI I.hsh
  col := NockvmE2E.J8.TieJ8G.colI
  loc := E2EJ8P.locΙ
  w := NockvmE2E.J8.TieJ8G.wOf
  hcolT := NockvmE2E.J8.TieJ8G.tabΙ_colI
  hcolL := E2EJ8P.colI_locΙ
  hlocW := E2EJ8P.locΙ_lt
  hlocC := E2EJ8P.locΙ_colI
  hw := E2EJ8P.w_eq I
  nloc := NockvmE2E.J8.InstJ8.sz I.d
  dec := finSigmaFinEquiv.symm
  hdec := fun _ => rfl
  rt := NockvmE2E.J8.TieJ8.rtJ8 I.d
  hrtN := NockvmE2E.J8.TieJ8.rtJ8_N I.d
  R := I.R
  hT := I.hT
  hσR := I.hσ
  hfree := I.hfree
  hr := rfl
  hd4 := rfl
  hoff := fun t k => congrArg (· ^ (k : ℕ)) (NockvmE2E.J8.TieJ8G.omegaOf_eq I t)
  hdom := NockvmE2E.J8.InstJ8.H_J8_eq I.XI I.d I.hdk (hShift_of_shape I.hsh) I.hdN I.hdω
  hdomt := hdomt_J8' I
  hpdeg := hpdeg_J8 I
  hpreN := fun t c hc hnot => by
    have hnot' : c ∉ (J8Shape.preIdxJ8 (NockvmE2E.J8.InstJ8.tabId (sigmaX I.XI t))).toList := by
      rw [NockvmE2E.J8.TieJ8G.tabId_sigmaX I.XI I.hsh t]; exact hnot
    exact E2EJ8P.preJ_none I.d _ c hc hnot'
  hcolR := fun t c hc =>
    E2EJ8P.colRB_eq _ ((NockvmE2E.J8.TieJ8G.ids_of_shape I.hsh).2 _ (Array.getElem_mem_toList t.2)) c hc
  hcapι := by
    show (Fintype.card NockvmE2E.J8.InstJ8.Ι + 926) * 2 + 9 ≤ 2 ^ 12
    rw [NockvmE2E.J8.InstJ8.card_Ι]; norm_num
  rdM := NockvmE2E.J8.RVUJ8.Mof I.XI.pubLay

/-! ### the `rfl` probes: each generic data def agrees with its J-8 text at `ofJ8` -/

section Probes
variable (I : NockvmE2E.J8.TieJ8G.Inst) (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub)

set_option maxRecDepth 50000 in
example (hsz : NockvmE2E.J8.TieJ8G.HSz I) :
    GflatG (InstG.ofJ8 I) hsz = NockvmE2E.J8.TieJ8G.Gflat I hsz := rfl

example (t : Fin I.XI.tabs.size) (c : ℕ) :
    colJG (InstG.ofJ8 I) npub tp hcap t c = NockvmE2E.J8.TieJ8G.colJ I npub tp hcap t c := rfl

example (t : Fin I.XI.tabs.size) (s : ℕ) :
    pubJG (InstG.ofJ8 I) npub tp hcap t s = NockvmE2E.J8.TieJ8G.pubJ I npub tp hcap t s := rfl

example (hnpub : npub = I.XI.pubOf.size) :
    prG (InstG.ofJ8 I) npub tp hcap = E2EJ8P.prX I npub tp hcap := rfl

example (hnpub : npub = I.XI.pubOf.size) (x : PresentCols (J8 I.d I.hdk) I.R.p ⊕ Fin npub) :
    f0G (InstG.ofJ8 I) npub x = E2EJ8P.f0 I npub x := by
  rcases x with j | s <;> rfl

example (hnpub : npub = I.XI.pubOf.size) (x : (I.JJ npub tp hcap).ι0) :
    cIG (InstG.ofJ8 I) npub tp hcap hnpub x = E2EJ8P.cIX I npub tp hcap hnpub x := by
  rcases x with j | s <;> rfl

/-- `cIG = cIX` holds pointwise (hence by `Equiv.ext`); `rfl` at function level does not go through (probe finding), so the generic
theorem takes `cI` as a binder with `hcI_col`/`hcI_pub` and `cI_val_G` instead -/
example (hnpub : npub = I.XI.pubOf.size) :
    cIG (InstG.ofJ8 I) npub tp hcap hnpub = E2EJ8P.cIX I npub tp hcap hnpub :=
  Equiv.ext fun x => by rcases x with j | s <;> rfl

example : (InstG.ofJ8 I).JJ npub tp hcap = I.JJ npub tp hcap := rfl

end Probes

end J8

end NockvmE2E.Exec.E2EGen
