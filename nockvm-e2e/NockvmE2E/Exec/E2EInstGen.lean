/-
  NockvmE2E/Exec/E2EInstGen.lean   

  The generic (no J-8 import) instance half of `exec_e2e_final` for a flat `ExecInst` of J-8 shape:
  * `OpsU` (`opsU_of_layout`): column bijection `cI : ι ≃ Fin nc` (`colNG`), the opening enumeration `eOf`, the rank equivalence `rkP`
    (block-layout counting lemma `layout_count`, `card_block`), the opened-value reader `vTOfG`; the closed form of `openingList`
    (`olInv_fold`) and of `openPts` (`openPts_get`).
  * `da` (`daOf`): M0 unit codec, block 0/1 slot-order codecs (`blockEnc`/`blockDec`), block 2/3 singleton codecs (`singEnc`/`singDec`),
    the `Mfin` parser `finDecG` (`parse_vT`/`parse_vQ` on `deepMsg`); `uniLinksN_of_da` assembles `UniLinksN` with `hdagU`, `hRVU` (Y-half)
    and `hH`, `he`, `hnq`, `hcw` as arguments.
  * `JFacts`: the `deepParamsJ`-specific `single_az`, `hH_J`, `hcw_J`, `pt_J`.
-/
import NockvmE2E.Exec.E2EFinal
import NockvmE2E.Exec.J8Shape
import NockvmE2E.J8.Adapt
import NockvmE2E.J8.Deep
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace NockvmE2E.Exec.InstGen
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL

theorem push_get_lt {α : Type} [Inhabited α] (a : Array α) (x : α) (k : ℕ) (h : k < a.size) : (a.push x)[k]! = a[k]! := by
  rw [getElem!_pos _ k (by simp; omega), getElem!_pos _ k h]
  simp [Array.getElem_push_lt h]

theorem push_get_eq {α : Type} [Inhabited α] (a : Array α) (x : α) : (a.push x)[a.size]! = x := by
  rw [getElem!_pos _ a.size (by simp)]
  simp

theorem pts_fold (zeta : VF.K3) (hG : UInt64) : ∀ n : ℕ,
    ((List.range n).foldl (fun (st : Array VF.K3 × VF.K3) _ => (st.1.push (VF.K3.mul zeta st.2), VF.K3.smul hG st.2)) (#[], VF.K3.one)).1.size = n ∧
    toKV ((List.range n).foldl (fun (st : Array VF.K3 × VF.K3) _ => (st.1.push (VF.K3.mul zeta st.2), VF.K3.smul hG st.2)) (#[], VF.K3.one)).2 = psiV hG ^ n ∧
    ∀ k < n, toKV ((List.range n).foldl (fun (st : Array VF.K3 × VF.K3) _ => (st.1.push (VF.K3.mul zeta st.2), VF.K3.smul hG st.2)) (#[], VF.K3.one)).1[k]! = toKV zeta * psiV hG ^ k := by
  intro n
  induction n with
  | zero => simp [toKV_one]
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    refine ⟨by simp [h1], by rw [toKV_smul, h2, pow_succ, mul_comm], fun k hk => ?_⟩
    by_cases hkn : k < n
    · rw [push_get_lt _ _ _ (by rw [h1]; exact hkn)]; exact h3 k hkn
    · have : k = n := by omega
      subst this
      have := push_get_eq ((List.range k).foldl (fun (st : Array VF.K3 × VF.K3) _ => (st.1.push (VF.K3.mul zeta st.2), VF.K3.smul hG st.2)) (#[], VF.K3.one)).1 (VF.K3.mul zeta ((List.range k).foldl (fun (st : Array VF.K3 × VF.K3) _ => (st.1.push (VF.K3.mul zeta st.2), VF.K3.smul hG st.2)) (#[], VF.K3.one)).2)
      rw [h1] at this
      rw [this, toKV_mul, h2]

theorem openPts_get (XI : ExecInst) (zeta : VF.K3) :
    (∀ k < XI.r, toKV (openPts XI zeta)[k]! = toKV zeta * psiV XI.hGen ^ k) ∧ (openPts XI zeta)[XI.r]! = XI.ppt ∧ (openPts XI zeta)[XI.r + 1]! = zeta := by
  obtain ⟨h1, h2, h3⟩ := pts_fold zeta XI.hGen XI.r
  unfold openPts
  generalize (List.range XI.r).foldl (fun (st : Array VF.K3 × VF.K3) _ => (st.1.push (VF.K3.mul zeta st.2), VF.K3.smul XI.hGen st.2)) (#[], VF.K3.one) = st at h1 h2 h3 ⊢
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · rw [push_get_lt _ _ _ (by simp [h1]; omega), push_get_lt _ _ _ (by rw [h1]; exact hk)]; exact h3 k hk
  · rw [← h1, push_get_lt _ _ _ (by simp), push_get_eq]
  · rw [← h1, show st.1.size + 1 = ((st.1.push XI.ppt).size) by simp, push_get_eq]

/-! ## the opening list in closed form -/

abbrev Entry := ℕ × ℕ × VF.K3 × VF.K3

theorem inner_fold (c : ℕ) (g : ℕ → ℕ) (v : ℕ → VF.K3) (cs : VF.K3) (a : Array Entry) (p : VF.K3) : ∀ n : ℕ,
    ((List.range n).foldl (fun (st : Array Entry × VF.K3) o => (st.1.push (c, g o, st.2, v o), VF.K3.mul st.2 cs)) (a, p)).1.size = a.size + n ∧
    toKV ((List.range n).foldl (fun (st : Array Entry × VF.K3) o => (st.1.push (c, g o, st.2, v o), VF.K3.mul st.2 cs)) (a, p)).2 = toKV p * toKV cs ^ n ∧
    (∀ j < a.size, ((List.range n).foldl (fun (st : Array Entry × VF.K3) o => (st.1.push (c, g o, st.2, v o), VF.K3.mul st.2 cs)) (a, p)).1[j]! = a[j]!) ∧
    ∀ o < n, (((List.range n).foldl (fun (st : Array Entry × VF.K3) o => (st.1.push (c, g o, st.2, v o), VF.K3.mul st.2 cs)) (a, p)).1[a.size + o]!).1 = c ∧
      (((List.range n).foldl (fun (st : Array Entry × VF.K3) o => (st.1.push (c, g o, st.2, v o), VF.K3.mul st.2 cs)) (a, p)).1[a.size + o]!).2.1 = g o ∧
      toKV (((List.range n).foldl (fun (st : Array Entry × VF.K3) o => (st.1.push (c, g o, st.2, v o), VF.K3.mul st.2 cs)) (a, p)).1[a.size + o]!).2.2.1 = toKV p * toKV cs ^ o ∧
      (((List.range n).foldl (fun (st : Array Entry × VF.K3) o => (st.1.push (c, g o, st.2, v o), VF.K3.mul st.2 cs)) (a, p)).1[a.size + o]!).2.2.2 = v o := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize hst : (List.range n).foldl (fun (st : Array Entry × VF.K3) o => (st.1.push (c, g o, st.2, v o), VF.K3.mul st.2 cs)) (a, p) = st at h1 h2 h3 h4 ⊢
    refine ⟨by simp [h1]; omega, by rw [toKV_mul, h2, pow_succ]; ring, fun j hj => ?_, fun o ho => ?_⟩
    · rw [push_get_lt _ _ _ (by rw [h1]; omega), h3 j hj]
    · by_cases hon : o < n
      · rw [push_get_lt _ _ _ (by rw [h1]; omega)]; exact h4 o hon
      · have : o = n := by omega
        subst this
        have e : a.size + o = (st.1).size := by rw [h1]
        rw [e, push_get_eq]
        refine ⟨rfl, rfl, ?_, rfl⟩
        show toKV st.2 = _
        rw [h2]

/-- one column of `openingList` (a copy of the verifier's fold body) -/
def olStep (XI : ExecInst) (cs : VF.K3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3) (st : Array Entry × VF.K3) (c : ℕ) : Array Entry × VF.K3 :=
  match kindG XI c with
  | 0 | 1 => (List.range XI.r).foldl
      (fun (st : Array (ℕ × ℕ × VF.K3 × VF.K3) × VF.K3) o => (st.1.push (c, o, st.2, (vT[c]!)[o]!), VF.K3.mul st.2 cs)) st
  | 2 => (List.range XI.r).foldl
      (fun (st : Array (ℕ × ℕ × VF.K3 × VF.K3) × VF.K3) _ => (st.1.push (c, XI.r, st.2, (vT[c]!)[0]!), VF.K3.mul st.2 cs)) st
  | 3 => (st.1.push (c, XI.r + 1, st.2, vQ[c - XI.nc]!), VF.K3.mul st.2 cs)
  | _ => st

theorem openingList_eq (XI : ExecInst) (cs : VF.K3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3) :
    openingList XI cs vT vQ = ((List.range (XI.nc + XI.nq)).foldl (olStep XI cs vT vQ) (#[], VF.K3.one)).1 := rfl

/-- the closed form of entry `j` of the opening list -/
def EntryOK (XI : ExecInst) (cs : VF.K3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3) (j : ℕ) (e : Entry) : Prop :=
  toKV e.2.2.1 = toKV cs ^ j ∧
  (if j < XI.nc * XI.r then
    e.1 = j / XI.r ∧ e.2.1 = (if XI.colKind[j / XI.r]! = 2 then XI.r else j % XI.r) ∧
      e.2.2.2 = (vT[j / XI.r]!)[if XI.colKind[j / XI.r]! = 2 then 0 else j % XI.r]!
  else e.1 = XI.nc + (j - XI.nc * XI.r) ∧ e.2.1 = XI.r + 1 ∧ e.2.2.2 = vQ[j - XI.nc * XI.r]!)

structure OlInv (XI : ExecInst) (cs : VF.K3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3) (m : ℕ) (st : Array Entry × VF.K3) : Prop where
  s1 : m ≤ XI.nc → st.1.size = m * XI.r
  s2 : XI.nc ≤ m → st.1.size = XI.nc * XI.r + (m - XI.nc)
  c : toKV st.2 = toKV cs ^ st.1.size
  e : ∀ j < st.1.size, EntryOK XI cs vT vQ j st.1[j]!

theorem olInv_fold (XI : ExecInst) [NeZero XI.r] (hkd : ∀ c < XI.nc, XI.colKind[c]! < 3) (cs : VF.K3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3) :
    ∀ m, m ≤ XI.nc + XI.nq → OlInv XI cs vT vQ m ((List.range m).foldl (olStep XI cs vT vQ) (#[], VF.K3.one)) := by
  have hr : 0 < XI.r := Nat.pos_of_ne_zero (NeZero.ne _)
  intro m
  induction m with
  | zero => intro _; exact ⟨fun _ => by simp, fun h => by have : XI.nc = 0 := by omega
                                                          simp [this], by simp [toKV_one], fun j hj => by simp at hj⟩
  | succ m ih =>
    intro hm
    have IH := ih (by omega)
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize hst : (List.range m).foldl (olStep XI cs vT vQ) (#[], VF.K3.one) = st at IH ⊢
    have hkm : kindG XI m = if m < XI.nc then XI.colKind[m]! else 3 := rfl
    by_cases hmn : m < XI.nc
    · have hsz : st.1.size = m * XI.r := IH.s1 hmn.le
      have hk := hkd m hmn
      have hkk : kindG XI m = XI.colKind[m]! := by rw [hkm, if_pos hmn]
      -- generic step for the two inner-fold cases
      have gen : ∀ (g : ℕ → ℕ) (v : ℕ → VF.K3),
          (∀ o < XI.r, g o = (if XI.colKind[m]! = 2 then XI.r else o)) →
          (∀ o < XI.r, v o = (vT[m]!)[if XI.colKind[m]! = 2 then 0 else o]!) →
          OlInv XI cs vT vQ (m + 1) ((List.range XI.r).foldl
            (fun (st : Array Entry × VF.K3) o => (st.1.push (m, g o, st.2, v o), VF.K3.mul st.2 cs)) st) := by
        intro g v hg hv
        obtain ⟨i1, i2, i3, i4⟩ := inner_fold m g v cs st.1 st.2 XI.r
        have hcs : toKV st.2 = toKV cs ^ (m * XI.r) := by rw [IH.c, hsz]
        refine ⟨fun _ => ?_, fun h => ?_, ?_, ?_⟩
        · rw [i1, hsz, Nat.succ_mul]
        · rw [i1, hsz]; have : XI.nc = m + 1 := by omega
          rw [this, Nat.succ_mul]; simp
        · rw [i2, hcs, i1, hsz, ← pow_add]
        · intro j hj
          rw [i1, hsz] at hj
          by_cases hjo : j < m * XI.r
          · rw [i3 j (by rw [hsz]; exact hjo)]
            have := IH.e j (by rw [hsz]; exact hjo)
            exact this
          · obtain ⟨o, ho, rfl⟩ : ∃ o, o < XI.r ∧ j = m * XI.r + o := ⟨j - m * XI.r, by omega, by omega⟩
            obtain ⟨j1, j2, j3, j4⟩ := i4 o ho
            rw [hsz] at j1 j2 j3 j4
            have hdiv : (m * XI.r + o) / XI.r = m := by
              rw [Nat.mul_comm, Nat.mul_add_div hr, Nat.div_eq_of_lt ho]; simp
            have hmod : (m * XI.r + o) % XI.r = o := by
              rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ho]
            have hlt : m * XI.r + o < XI.nc * XI.r := by
              calc m * XI.r + o < m * XI.r + XI.r := by omega
                _ = (m + 1) * XI.r := (Nat.succ_mul _ _).symm
                _ ≤ XI.nc * XI.r := Nat.mul_le_mul_right _ hmn
            unfold EntryOK
            rw [if_pos hlt, hdiv, hmod]
            refine ⟨?_, j1, ?_, ?_⟩
            · rw [j3, hcs, ← pow_add]
            · rw [j2, hg o ho]
            · rw [j4, hv o ho]
      have hk3 : XI.colKind[m]! = 0 ∨ XI.colKind[m]! = 1 ∨ XI.colKind[m]! = 2 := by omega
      unfold olStep
      rw [hkk]
      rcases hk3 with h0 | h1 | h2
      · rw [h0]; exact gen (fun o => o) (fun o => (vT[m]!)[o]!) (fun o _ => by simp [h0]) (fun o _ => by simp [h0])
      · rw [h1]; exact gen (fun o => o) (fun o => (vT[m]!)[o]!) (fun o _ => by simp [h1]) (fun o _ => by simp [h1])
      · rw [h2]; exact gen (fun _ => XI.r) (fun _ => (vT[m]!)[0]!) (fun o _ => by simp [h2]) (fun o _ => by simp [h2])
    · have hsz : st.1.size = XI.nc * XI.r + (m - XI.nc) := IH.s2 (by omega)
      have hkk : kindG XI m = 3 := by rw [hkm, if_neg hmn]
      unfold olStep
      rw [hkk]
      show OlInv XI cs vT vQ (m + 1) (st.1.push (m, XI.r + 1, st.2, vQ[m - XI.nc]!), VF.K3.mul st.2 cs)
      refine ⟨fun h => by omega, fun h => ?_, ?_, ?_⟩
      · simp [hsz]; omega
      · simp only [Array.size_push, toKV_mul, IH.c, pow_succ]
      · intro j hj
        simp only [Array.size_push] at hj
        by_cases hjo : j < st.1.size
        · rw [push_get_lt _ _ _ hjo]; exact IH.e j hjo
        · have : j = st.1.size := by omega
          subst this
          rw [push_get_eq]
          unfold EntryOK
          have hge : ¬ (st.1.size < XI.nc * XI.r) := by omega
          rw [if_neg hge]
          refine ⟨IH.c, ?_, rfl, ?_⟩
          · simp [hsz]; omega
          · simp [hsz]

/-! ## the block layout counts the columns of a block -/

theorem layout_count (XI : ExecInst) (b : ℕ) (hb : b < 4) : ∀ m, m ≤ XI.nc + XI.nq →
    ((List.range m).foldl (layoutStep XI) (Array.replicate 4 0, Array.replicate (XI.nc + XI.nq) 0)).1[b]! =
      ∑ c ∈ Finset.range m, if XI.blockOf[c]! = b then 1 else 0 := by
  intro m
  induction m with
  | zero => intro _; simp [hb]
  | succ m ih =>
    intro hm
    have IH := ih (by omega)
    have hL := LInv_fold XI m (by omega)
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← IH]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize (List.range m).foldl (layoutStep XI) (Array.replicate 4 0, Array.replicate (XI.nc + XI.nq) 0) = st at hL ⊢
    unfold layoutStep
    by_cases hv : XI.blockOf[m]! < 4
    · simp only [hv, ite_true]
      rw [modify_get1 _ _ _ (by rw [hL.s1]; exact hv)]
      by_cases hmb : XI.blockOf[m]! = b
      · simp [hmb]
      · simp [hmb, Ne.symm hmb]
    · have : ¬ (XI.blockOf[m]! = b) := by omega
      simp [hv, this]


/-! ## the flat column bijection, the block rank -/

section Cols
open NockvmE2E.Exec.Cover

variable {ι : Type} [Fintype ι] [DecidableEq ι] {nq : ℕ}

/-- the flat column index of an interface column (trace/public columns by `cI`, quotient chunk `q` at `nc + q`) -/
def colNG (XI : ExecInst) (cI : ι ≃ Fin XI.nc) : ι ⊕ Fin nq → ℕ := Sum.elim (fun c => (cI c).val) (fun q => XI.nc + q.val)

/-- `colNG` as an equivalence onto the `nc + nq` flat columns -/
def eC (XI : ExecInst) (cI : ι ≃ Fin XI.nc) (hnq : XI.nq = nq) : ι ⊕ Fin nq ≃ Fin (XI.nc + XI.nq) :=
  (Equiv.sumCongr cI (finCongr hnq.symm)).trans finSumFinEquiv

theorem eC_val (XI : ExecInst) (cI : ι ≃ Fin XI.nc) (hnq : XI.nq = nq) (x : ι ⊕ Fin nq) :
    ((eC XI cI hnq x : Fin _) : ℕ) = colNG XI cI x := by
  rcases x with c | q <;> simp [eC, colNG]

theorem card_block (XI : ExecInst) (cI : ι ≃ Fin XI.nc) (hnq : XI.nq = nq) (colRound : ι ⊕ Fin nq → ℕ)
    (hcolB : ∀ c, XI.blockOf[colNG XI cI c]! = colRound c) (hlt : ∀ c, colRound c < 4) (b : ℕ) :
    Fintype.card {c : ι ⊕ Fin nq // colRound c = b} = Wb XI b := by
  classical
  by_cases hb : b < 4
  · rw [Fintype.card_congr (Equiv.subtypeEquiv (eC XI cI hnq) (q := fun i : Fin (XI.nc + XI.nq) => XI.blockOf[i.val]! = b)
        (fun c => by rw [eC_val, hcolB])), Fintype.card_subtype, Finset.card_filter]
    have := Fin.sum_univ_eq_sum_range (fun c => if XI.blockOf[c]! = b then 1 else 0) (XI.nc + XI.nq)
    rw [this]
    unfold Wb
    rw [blockLayout_eq, layout_count XI b hb _ le_rfl]
  · have h0 : Wb XI b = 0 := by
      unfold Wb
      rw [getElem!_neg _ b (by rw [blockLayout_size]; exact hb)]; rfl
    rw [h0, Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨c, hc⟩ => by have := hlt c; omega⟩

/-- **the rank equivalence** (`rk` of `OpsU`): a column's rank in its block, bijective onto `Fin (Wb b)` -/
noncomputable def rkOf (XI : ExecInst) (cI : ι ≃ Fin XI.nc) (hnq : XI.nq = nq) (colRound : ι ⊕ Fin nq → ℕ)
    (hcolB : ∀ c, XI.blockOf[colNG XI cI c]! = colRound c) (hlt : ∀ c, colRound c < 4) (b : ℕ) :
    {c : ι ⊕ Fin nq // colRound c = b} ≃ Fin (Wb XI b) := by
  classical
  refine Equiv.ofBijective (fun c => ⟨(blockLayout XI).2[colNG XI cI c.1]!, ?_⟩) ?_
  · have hv : LayoutValid XI (colNG XI cI c.1) := by
      show XI.blockOf[colNG XI cI c.1]! < 4
      rw [hcolB]; exact hlt _
    have := blockLayout_rank_lt XI (colNG XI cI c.1) (by rw [← eC_val XI cI hnq]; exact (eC XI cI hnq c.1).2) hv
    rw [hcolB, c.2] at this
    exact this
  · rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun c c' h => ?_, by rw [card_block XI cI hnq colRound hcolB hlt b]; simp⟩
    have h' : (blockLayout XI).2[colNG XI cI c.1]! = (blockLayout XI).2[colNG XI cI c'.1]! := congrArg Fin.val h
    by_contra hne
    have hne' : colNG XI cI c.1 ≠ colNG XI cI c'.1 := by
      intro he
      apply hne
      apply Subtype.ext
      exact (eC XI cI hnq).injective (Fin.ext (by rw [eC_val, eC_val]; exact he))
    refine blockLayout_rank_inj XI _ _ (by rw [← eC_val XI cI hnq]; exact (eC XI cI hnq c.1).2)
      (by rw [← eC_val XI cI hnq]; exact (eC XI cI hnq c'.1).2) ?_ ?_ ?_ hne' h'
    · show XI.blockOf[colNG XI cI c.1]! < 4
      rw [hcolB]; exact hlt _
    · show XI.blockOf[colNG XI cI c'.1]! < 4
      rw [hcolB]; exact hlt _
    · rw [hcolB, hcolB, c.2, c'.2]

theorem rkOf_val (XI : ExecInst) (cI : ι ≃ Fin XI.nc) (hnq : XI.nq = nq) (colRound : ι ⊕ Fin nq → ℕ)
    (hcolB : ∀ c, XI.blockOf[colNG XI cI c]! = colRound c) (hlt : ∀ c, colRound c < 4) (b : ℕ)
    (c : {c : ι ⊕ Fin nq // colRound c = b}) :
    ((rkOf XI cI hnq colRound hcolB hlt b c : Fin _) : ℕ) = (blockLayout XI).2[colNG XI cI c.1]! := rfl

end Cols

/-! ## `e`: the batched-opening enumeration -/

section EnumE

theorem div_aux (a r k : ℕ) (hk : k < r) : (a * r + k) / r = a := by
  rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hk]; simp

theorem mod_aux (a r k : ℕ) (hk : k < r) : (a * r + k) % r = k := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]

theorem lt_aux (a n r k : ℕ) (ha : a < n) (hk : k < r) : a * r + k < n * r :=
  calc a * r + k < a * r + r := by omega
    _ = (a + 1) * r := (Nat.succ_mul _ _).symm
    _ ≤ n * r := Nat.mul_le_mul_right _ ha

variable {ι : Type} [Fintype ι] [DecidableEq ι] {nq : ℕ}

/-- **`e`**: the `j`-th batched opening is `(c, k)` for `j = c·r + k` (`c` the flat index of the column), then the quotient chunks -/
def eOf (XI : ExecInst) (cI : ι ≃ Fin XI.nc) (r : ℕ) [NeZero r] {m : ℕ} (hm : m + 1 = XI.nc * r + nq) :
    Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin nq where
  toFun j := if h : j.val < XI.nc * r then
      Sum.inl (cI.symm ⟨j.val / r, (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne r))).2 h⟩,
        ⟨j.val % r, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne r))⟩)
    else Sum.inr ⟨j.val - XI.nc * r, by have := j.2; omega⟩
  invFun x := match x with
    | Sum.inl (c, k) => ⟨(cI c).val * r + k.val, by have := lt_aux (cI c).val XI.nc r k.val (cI c).2 k.2; omega⟩
    | Sum.inr q => ⟨XI.nc * r + q.val, by have := q.2; omega⟩
  left_inv j := by
    by_cases h : j.val < XI.nc * r
    · simp only [h, dite_true, Equiv.apply_symm_apply]
      exact Fin.ext (Nat.div_add_mod' _ _)
    · simp only [h, dite_false]
      exact Fin.ext (by simp; omega)
  right_inv x := by
    rcases x with ⟨c, k⟩ | q
    · have hlt := lt_aux (cI c).val XI.nc r k.val (cI c).2 k.2
      simp only [hlt, dite_true]
      have e1 : (⟨((cI c).val * r + k.val) / r, by rw [div_aux _ _ _ k.2]; exact (cI c).2⟩ : Fin XI.nc) = cI c :=
        Fin.ext (div_aux _ _ _ k.2)
      simp only [div_aux _ _ _ k.2, mod_aux _ _ _ k.2]
      simp
    · simp

end EnumE

section OpsGen
open NockvmE2E.Exec.Cover NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Rap NockvmE2E.Exec.E2EW0 NockvmE2E.Exec.E2ELR NockvmE2E.Succ.FriDeep

/-- the opened-value reader: the value of column `c` at offset `k` is `vT[c][k]`, a public (kind 2) column carries a single value `vT[c][0]` -/
noncomputable def vTOfG (XI : ExecInst) {ι : Type} (cI : ι ≃ Fin XI.nc) (r : ℕ) : Array (Array VF.K3) → ι × Fin r → KC :=
  fun vT ck => toKV ((vT[(cI ck.1).val]!)[if XI.colKind[(cI ck.1).val]! = 2 then 0 else ck.2.val]!)

theorem hopsF_gen (XI : ExecInst) {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
    (P : DeepParams Φ KC ι (Fin (2 ^ XI.nD) → ZMod NockvmE2E.Exec.p) colRound) {r : ℕ} [NeZero r] (A : AirShape P r) (hr : r = XI.r)
    (hnq : XI.nq = P.nq) (hkd : ∀ c < XI.nc, XI.colKind[c]! < 3) (cI : ι ≃ Fin XI.nc)
    (hptP : ∀ c k ζ, XI.colKind[(cI c).val]! = 2 → A.pt c k ζ = toKV XI.ppt)
    (hptT : ∀ c (k : Fin r) ζ, XI.colKind[(cI c).val]! ≠ 2 → A.pt c k ζ = ζ * psiV XI.hGen ^ k.val)
    {m : ℕ} (hm : m + 1 = XI.nc * r + P.nq) :
    ∀ (cs ζ : VF.K3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3), VShape XI vT vQ →
    List.Forall₂ (fun (o : ℕ × ℕ × VF.K3 × VF.K3) (j : Fin (m + 1)) =>
      o.2.1 < XI.r + 2 ∧ toKV o.2.2.1 = toKV cs ^ (j : ℕ) ∧
      toKV (openPts XI ζ)[o.2.1]! = Sum.elim (fun ck => A.pt ck.1 ck.2 (toKV ζ)) (fun _ => toKV ζ) (eOf XI cI r hm j) ∧
      toKV o.2.2.2 = Sum.elim (vTOfG XI cI r vT) (fun q => toKV vQ[q.1]!) (eOf XI cI r hm j) ∧
      o.1 = colNG XI cI (Sum.elim (fun ck => Sum.inl ck.1) (fun q => Sum.inr q) (eOf XI cI r hm j)))
      (openingList XI cs vT vQ).toList (List.finRange (m + 1)) := by
  subst hr
  intro cs ζ vT vQ _
  have hr0 : 0 < XI.r := Nat.pos_of_ne_zero (NeZero.ne _)
  have hinv := olInv_fold XI hkd cs vT vQ (XI.nc + XI.nq) le_rfl
  have hsize : (openingList XI cs vT vQ).size = m + 1 := by
    rw [openingList_eq, hinv.s2 (by omega)]; omega
  rw [List.forall₂_iff_get]
  refine ⟨by simp [hsize], fun i h1 h2 => ?_⟩
  have hi : i < m + 1 := by simpa using h2
  have hE := hinv.e i (by rw [← openingList_eq, hsize]; exact hi)
  rw [← openingList_eq] at hE
  have hget : (openingList XI cs vT vQ).toList.get ⟨i, h1⟩ = (openingList XI cs vT vQ)[i]! := by
    rw [getElem!_pos _ i (by rw [hsize]; exact hi)]; simp
  have hfin : (List.finRange (m + 1)).get ⟨i, h2⟩ = ⟨i, hi⟩ := by simp
  rw [hget, hfin]
  obtain ⟨hc, hrest⟩ := hE
  have hpts := openPts_get XI ζ
  generalize (openingList XI cs vT vQ)[i]! = o at hc hrest ⊢
  by_cases h : i < XI.nc * XI.r
  · rw [if_pos h] at hrest
    obtain ⟨ho1, ho2, ho3⟩ := hrest
    have hdiv : i / XI.r < XI.nc := (Nat.div_lt_iff_lt_mul hr0).2 h
    have hmod : i % XI.r < XI.r := Nat.mod_lt _ hr0
    have he : eOf XI cI XI.r hm ⟨i, hi⟩ = Sum.inl (cI.symm ⟨i / XI.r, hdiv⟩, ⟨i % XI.r, hmod⟩) := by
      simp [eOf, h]
    rw [he]
    have hk : XI.colKind[(cI (cI.symm ⟨i / XI.r, hdiv⟩)).val]! = XI.colKind[i / XI.r]! := by simp
    refine ⟨?_, hc, ?_, ?_, ?_⟩
    · rw [ho2]; split_ifs <;> omega
    · show _ = A.pt _ _ _
      rw [ho2]
      by_cases hk2 : XI.colKind[i / XI.r]! = 2
      · rw [if_pos hk2, hptP _ _ _ (by rw [hk]; exact hk2), hpts.2.1]
      · rw [if_neg hk2, hptT _ _ _ (by rw [hk]; exact hk2)]
        exact hpts.1 _ hmod
    · show _ = vTOfG XI cI XI.r vT _
      rw [ho3]; unfold vTOfG; simp
    · show _ = ((cI (cI.symm _)).val)
      rw [ho1]; simp
  · rw [if_neg h] at hrest
    obtain ⟨ho1, ho2, ho3⟩ := hrest
    have he : eOf XI cI XI.r hm ⟨i, hi⟩ = Sum.inr ⟨i - XI.nc * XI.r, by omega⟩ := by
      simp [eOf, h]
    rw [he]
    refine ⟨by rw [ho2]; omega, hc, ?_, ?_, ?_⟩
    · show _ = toKV ζ
      rw [ho2, hpts.2.2]
    · show _ = toKV vQ[i - XI.nc * XI.r]!
      rw [ho3]
    · show _ = XI.nc + (i - XI.nc * XI.r)
      rw [ho1]

section OpsAsm
variable (XI : ExecInst) {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ XI.nD) → ZMod NockvmE2E.Exec.p) colRound)

theorem colB_of (hR : P.R = 2) (cI : ι ≃ Fin XI.nc) (hblk : ∀ c, XI.blockOf[(cI c).val]! = colRound c)
    (hblkq : ∀ q : Fin P.nq, XI.blockOf[XI.nc + q.val]! = 3) : ∀ c, XI.blockOf[colNG XI cI c]! = P.colRoundX c := by
  rintro (c | q)
  · exact hblk c
  · show XI.blockOf[XI.nc + q.val]! = P.R + 1
    rw [hblkq, hR]

theorem colX_lt (hR : P.R = 2) : ∀ c, P.colRoundX c < 4 := by
  rintro (c | q)
  · have := P.hcol c; show colRound c < 4; omega
  · show P.R + 1 < 4; omega

/-- **`rk`**: the rank of a column in its block -/
noncomputable def rkP (hR : P.R = 2) (hnq : XI.nq = P.nq) (cI : ι ≃ Fin XI.nc) (hblk : ∀ c, XI.blockOf[(cI c).val]! = colRound c)
    (hblkq : ∀ q : Fin P.nq, XI.blockOf[XI.nc + q.val]! = 3) : ∀ b, {c : ι ⊕ Fin P.nq // P.colRoundX c = b} ≃ Fin (Wb XI b) :=
  rkOf XI cI hnq P.colRoundX (colB_of XI P hR cI hblk hblkq) (colX_lt XI P hR)

/-- **`opsU_of_layout`**: all five fields of `OpsU` for the flat opening list, from the column bijection `cI` (interface column `c` is flat column
`cI c`; quotient chunk `q` is flat column `nc + q`) and the point/block facts of `A`/`P`. `hblk` is the `hcolB` tie to the emitted rounds (an instance
fact of the datum). Generic in `XI` (no J-8 import). -/
theorem opsU_of_layout (hR : P.R = 2) {r : ℕ} [NeZero r] (A : AirShape P r) (hr : r = XI.r) (hnq : XI.nq = P.nq)
    (hkd : ∀ c < XI.nc, XI.colKind[c]! < 3) (cI : ι ≃ Fin XI.nc)
    (hblk : ∀ c, XI.blockOf[(cI c).val]! = colRound c) (hblkq : ∀ q : Fin P.nq, XI.blockOf[XI.nc + q.val]! = 3)
    (hptP : ∀ c k ζ, XI.colKind[(cI c).val]! = 2 → A.pt c k ζ = toKV XI.ppt)
    (hptT : ∀ c (k : Fin r) ζ, XI.colKind[(cI c).val]! ≠ 2 → A.pt c k ζ = ζ * psiV XI.hGen ^ k.val)
    {m : ℕ} (hm : m + 1 = XI.nc * r + P.nq) :
    OpsU XI P A (eOf XI cI r hm) (vTOfG XI cI r) (colNG XI cI) (rkP XI P hR hnq cI hblk hblkq) toyEncB where
  hopsF := hopsF_gen XI P A hr hnq hkd cI hptP hptT hm
  hcolB := colB_of XI P hR cI hblk hblkq
  hcR := colX_lt XI P hR
  hrkV := fun b c => rkOf_val XI cI hnq P.colRoundX (colB_of XI P hR cI hblk hblkq) (colX_lt XI P hR) b c
  hencB := toy_hencB
end OpsAsm
end OpsGen

/-! ## the decoders `da`: challenge codecs in slot order, the `Mfin` parser -/

section Codecs
open NockvmE2E.Exec.E2EResid NockvmE2E.Rap

/-- a `K3` whose value is `y` (a fixed choice) -/
noncomputable def k3Of (y : KC) : VF.K3 := VF.K3.ofLimbs (Classical.choose (limbs_surj y))

theorem toKV_k3Of (y : KC) : toKV (k3Of y) = y := (Classical.choose_spec (limbs_surj y)).2

theorem canon3_k3Of (y : KC) : canon3 (k3Of y) :=
  canon3_ofLimbs _ (Classical.choose_spec (limbs_surj y)).1

theorem limbs_lt_of_canon3 (x : VF.K3) (h : canon3 x) : ∀ v ∈ VF.K3.limbs x, v < NockvmE2E.Exec.p := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨h1, h2, h3⟩ := h
  intro v hv
  simp only [VF.K3.limbs, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem ofLimbs_limbs' (x : VF.K3) : VF.K3.ofLimbs (VF.K3.limbs x) = x := by
  simpa using ofLimbs_limbs x []

variable {Φ : CoinFrame} {b n : ℕ}

/-- encode a challenge block: the limbs of the coins in slot order (`sl`: coin ↦ slot) -/
noncomputable def blockEnc (sl : {i : Fin Φ.n // Φ.sampledAfter i = b} ≃ Fin n) (c : Block Φ KC b) : List ℕ :=
  (List.finRange n).flatMap (fun s => VF.K3.limbs (k3Of (c (sl.symm s))))

/-- decode a challenge block: coin `i` is the `K3` at slot `sl i` -/
noncomputable def blockDec (sl : {i : Fin Φ.n // Φ.sampledAfter i = b} ≃ Fin n) (l : List ℕ) : Block Φ KC b :=
  fun i => toKV (VF.K3.ofLimbs (l.drop (3 * (sl i).val)))

theorem blockEnc_slot (sl : {i : Fin Φ.n // Φ.sampledAfter i = b} ≃ Fin n) (c : Block Φ KC b) (s : Fin n) :
    toKV (VF.K3.ofLimbs ((blockEnc sl c).drop (3 * s.val))) = c (sl.symm s) := by
  unfold blockEnc
  rw [← List.flatMap_map (g := VF.K3.limbs) (f := fun s => k3Of (c (sl.symm s))) (l := List.finRange n)]
  rw [ofLimbs_flat _ s.val (by simp)]
  simp [toKV_k3Of]

theorem blockDec_enc (sl : {i : Fin Φ.n // Φ.sampledAfter i = b} ≃ Fin n) (c : Block Φ KC b) :
    blockDec sl (blockEnc sl c) = c := by
  funext i
  unfold blockDec
  rw [blockEnc_slot, Equiv.symm_apply_apply]

/-- the codec of a block that holds the single coin `a` -/
noncomputable def singEnc (a : Fin Φ.n) (ha : Φ.sampledAfter a = b) (c : Block Φ KC b) : List ℕ :=
  VF.K3.limbs (k3Of (c ⟨a, ha⟩))

noncomputable def singDec (l : List ℕ) : Block Φ KC b := fun _ => toKV (VF.K3.ofLimbs l)

theorem singDec_enc (a : Fin Φ.n) (ha : Φ.sampledAfter a = b) (hs : ∀ i, Φ.sampledAfter i = b → i = a) (c : Block Φ KC b) :
    singDec (singEnc a ha c) = c := by
  funext i
  have : i = ⟨a, ha⟩ := Subtype.ext (hs i.1 i.2)
  subst this
  simp [singDec, singEnc, ofLimbs_limbs', toKV_k3Of]

theorem singEnc_dec (a : Fin Φ.n) (ha : Φ.sampledAfter a = b) (c : Block Φ KC b) :
    toKV (VF.K3.ofLimbs (singEnc a ha c)) = c ⟨a, ha⟩ := by
  simp [singEnc, ofLimbs_limbs', toKV_k3Of]

end Codecs

/-! ## parsing `deepMsg` -/

section Parse
open NockvmE2E.Exec.E2ELR NockvmE2E.Exec.E2EResid

theorem append_get_left {α : Type} [Inhabited α] (a b : List α) (i : ℕ) (h : i < a.length) : (a ++ b)[i]! = a[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos _ i h]; simp [List.getElem_append_left h]

theorem append_get_right {α : Type} [Inhabited α] (a b : List α) (i : ℕ) : (a ++ b)[a.length + i]! = b[i]! := by
  by_cases h : i < b.length
  · rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ i h]; simp [List.getElem_append_right]
  · rw [getElem!_neg _ _ (by simp; omega), getElem!_neg _ i h]

theorem flat_get {α : Type} [Inhabited α] : ∀ (L : List (List α)) (sz : ℕ → ℕ), (∀ i < L.length, (L[i]!).length = sz i) →
    ∀ c k, c < L.length → k < sz c → L.flatten[((List.range c).map sz).sum + k]! = (L[c]!)[k]!
  | [], _, _, c, k, hc, _ => by simp at hc
  | a :: L, sz, hsz, c, k, hc, hk => by
    have ha : a.length = sz 0 := by simpa using hsz 0 (by simp)
    cases c with
    | zero =>
      simp only [List.range_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatten_cons]
      rw [append_get_left _ _ _ (by omega)]
      rfl
    | succ c =>
      rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map, List.flatten_cons]
      have e : sz 0 + ((List.range c).map (sz ∘ Nat.succ)).sum + k = a.length + (((List.range c).map (sz ∘ Nat.succ)).sum + k) := by
        omega
      rw [e, append_get_right]
      have := flat_get L (sz ∘ Nat.succ) (fun i hi => by simpa using hsz (i + 1) (by simpa using hi)) c k (by simpa using hc) hk
      simpa using this


theorem flat_idx_lt {α : Type} [Inhabited α] : ∀ (L : List (List α)) (sz : ℕ → ℕ), (∀ i < L.length, (L[i]!).length = sz i) →
    ∀ c k, c < L.length → k < sz c → ((List.range c).map sz).sum + k < L.flatten.length
  | [], _, _, c, k, hc, _ => by simp at hc
  | a :: L, sz, hsz, c, k, hc, hk => by
    have ha : a.length = sz 0 := by simpa using hsz 0 (by simp)
    cases c with
    | zero => simp only [List.range_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatten_cons, List.length_append]; omega
    | succ c =>
      rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map, List.flatten_cons, List.length_append]
      have := flat_idx_lt L (sz ∘ Nat.succ) (fun i hi => by simpa using hsz (i + 1) (by simpa using hi)) c k (by simpa using hc) hk
      omega

/-- the offset (in `K3`s) of column `c`'s opened values in the DEEP message -/
def offT (XI : ExecInst) (c : ℕ) : ℕ := ((List.range c).map (vTLen XI)).sum

/-- the DEEP message as a list of `K3` -/
def flatK (vT : Array (Array VF.K3)) (vQ : Array VF.K3) : List VF.K3 := vT.toList.flatMap Array.toList ++ vQ.toList

theorem deepMsg_eq (vT : Array (Array VF.K3)) (vQ : Array VF.K3) : deepMsg vT vQ = (flatK vT vQ).flatMap VF.K3.limbs := by
  simp [deepMsg, flatK, List.flatMap_append, List.flatMap_assoc]

theorem toList_get {α : Type} [Inhabited α] (a : Array α) (i : ℕ) : a.toList[i]! = a[i]! := by
  by_cases h : i < a.size
  · rw [getElem!_pos _ i (by simpa using h), getElem!_pos _ i h]; simp
  · rw [getElem!_neg _ i (by simpa using h), getElem!_neg _ i h]

/-- the two index lemmas, in one: the `K3` list `flatK` read at the offsets -/
theorem flatK_get (XI : ExecInst) (vT : Array (Array VF.K3)) (vQ : Array VF.K3) (hsh : VShape XI vT vQ) :
    (∀ c k, c < XI.nc → k < vTLen XI c → offT XI c + k < (flatK vT vQ).length ∧ (flatK vT vQ)[offT XI c + k]! = (vT[c]!)[k]!) ∧
    (∀ q, q < XI.nq → offT XI XI.nc + q < (flatK vT vQ).length ∧ (flatK vT vQ)[offT XI XI.nc + q]! = vQ[q]!) := by
  obtain ⟨h1, h2, h3⟩ := hsh
  let Lv : List (List VF.K3) := vT.toList.map Array.toList
  let L : List (List VF.K3) := Lv ++ [vQ.toList]
  let sz : ℕ → ℕ := fun i => if i < XI.nc then vTLen XI i else XI.nq
  have hLv : Lv.length = XI.nc := by simp [Lv, h1]
  have hLlen : L.length = XI.nc + 1 := by simp [L, hLv]
  have hflat : L.flatten = flatK vT vQ := by
    simp [L, Lv, flatK, List.flatMap]
  have hLi : ∀ i (hi : i < XI.nc), L[i]! = (vT[i]!).toList := by
    intro i hi
    have hi1 : i < L.length := by omega
    have hi2 : i < Lv.length := by omega
    have hi3 : i < vT.size := by omega
    rw [getElem!_pos _ i hi1, getElem!_pos vT i hi3]
    have : L[i] = Lv[i] := List.getElem_append_left hi2
    rw [this]
    simp [Lv]
  have hLq : L[XI.nc]! = vQ.toList := by
    have hi1 : XI.nc < L.length := by omega
    rw [getElem!_pos L XI.nc hi1]
    have h5 : XI.nc - Lv.length < ([vQ.toList] : List (List VF.K3)).length := by simp [hLv]
    have : L[XI.nc] = ([vQ.toList] : List (List VF.K3))[XI.nc - Lv.length] := List.getElem_append_right (by omega)
    rw [this]; simp [hLv]
  have hsz : ∀ i < L.length, (L[i]!).length = sz i := by
    intro i hi
    by_cases hin : i < XI.nc
    · rw [hLi i hin]
      have := h3 i (List.mem_range.mpr hin)
      simp only [sz, hin, ite_true, Array.length_toList]
      exact this
    · have : i = XI.nc := by omega
      subst this
      rw [hLq]; simp [sz, h2]
  have hoff : ∀ c, c ≤ XI.nc → ((List.range c).map sz).sum = offT XI c := by
    intro c hc
    unfold offT
    congr 1
    apply List.map_congr_left
    intro i hi
    have := List.mem_range.mp hi
    simp only [sz, show i < XI.nc by omega, ite_true]
  refine ⟨fun c k hc hk => ?_, fun q hq => ?_⟩
  · have hk' : k < sz c := by simp only [sz, hc, ite_true]; exact hk
    rw [← hoff c hc.le, ← hflat]
    refine ⟨flat_idx_lt L sz hsz c k (by omega) hk', ?_⟩
    rw [flat_get L sz hsz c k (by omega) hk', hLi c hc]
    exact toList_get _ _
  · have hq' : q < sz XI.nc := by simp [sz, hq]
    rw [← hoff XI.nc le_rfl, ← hflat]
    refine ⟨flat_idx_lt L sz hsz XI.nc q (by omega) hq', ?_⟩
    rw [flat_get L sz hsz XI.nc q (by omega) hq', hLq]
    exact toList_get _ _


theorem parse_vT (XI : ExecInst) (vT : Array (Array VF.K3)) (vQ : Array VF.K3) (hsh : VShape XI vT vQ) (c k : ℕ) (hc : c < XI.nc)
    (hk : k < vTLen XI c) :
    toKV (VF.K3.ofLimbs ((deepMsg vT vQ).drop (3 * (offT XI c + k)))) = toKV ((vT[c]!)[k]!) := by
  obtain ⟨hl, he⟩ := (flatK_get XI vT vQ hsh).1 c k hc hk
  rw [deepMsg_eq, ofLimbs_flat _ _ hl, he]

theorem parse_vQ (XI : ExecInst) (vT : Array (Array VF.K3)) (vQ : Array VF.K3) (hsh : VShape XI vT vQ) (q : ℕ) (hq : q < XI.nq) :
    toKV (VF.K3.ofLimbs ((deepMsg vT vQ).drop (3 * (offT XI XI.nc + q)))) = toKV vQ[q]! := by
  obtain ⟨hl, he⟩ := (flatK_get XI vT vQ hsh).2 q hq
  rw [deepMsg_eq, ofLimbs_flat _ _ hl, he]

/-- the `Mfin` parser of the final message: the opened trace values (a public column carries one value, read for every offset) and the chunk values -/
noncomputable def finDecG (XI : ExecInst) {ι : Type} (cI : ι ≃ Fin XI.nc) (r nq : ℕ) {M0 : Type} (m0 : M0) (l : List ℕ) :
    M0 × (ι × Fin r → KC) × (Fin nq → KC) :=
  (m0, fun ck => toKV (VF.K3.ofLimbs (l.drop (3 * (offT XI (cI ck.1).val + (if XI.colKind[(cI ck.1).val]! = 2 then 0 else ck.2.val))))),
    fun q => toKV (VF.K3.ofLimbs (l.drop (3 * (offT XI XI.nc + q.val)))))

theorem finDecG_vQ (XI : ExecInst) {ι : Type} (cI : ι ≃ Fin XI.nc) (r nq : ℕ) (hnq : XI.nq = nq) {M0 : Type} (m0 : M0)
    (vT : Array (Array VF.K3)) (vQ : Array VF.K3) (hsh : VShape XI vT vQ) (q : Fin nq) :
    (finDecG XI cI r nq m0 (deepMsg vT vQ)).2.2 q = toKV vQ[q.1]! :=
  parse_vQ XI vT vQ hsh q.1 (by have := q.2; omega)

theorem finDecG_vT (XI : ExecInst) {ι : Type} (cI : ι ≃ Fin XI.nc) (r nq : ℕ) (hr : r = XI.r) (hkd : ∀ c < XI.nc, XI.colKind[c]! < 3)
    {M0 : Type} (m0 : M0) (vT : Array (Array VF.K3)) (vQ : Array VF.K3) (hsh : VShape XI vT vQ) :
    (finDecG XI cI r nq m0 (deepMsg vT vQ)).2.1 = vTOfG XI cI r vT := by
  funext ck
  obtain ⟨c, k⟩ := ck
  have hc := (cI c).2
  show toKV _ = toKV _
  have hlen : (if XI.colKind[(cI c).val]! = 2 then 0 else k.val) < vTLen XI (cI c).val := by
    unfold vTLen kindG
    rw [if_pos hc]
    have := hkd _ hc
    have hk := k.2
    by_cases h2 : XI.colKind[(cI c).val]! = 2
    · rw [h2]; simp [h2]
    · have : XI.colKind[(cI c).val]! = 0 ∨ XI.colKind[(cI c).val]! = 1 := by omega
      rcases this with h | h <;> simp [h, h2] <;> omega
  exact parse_vT XI vT vQ hsh _ _ hc hlen

end Parse

/-! ## `hlenU`, `hptsU` -/

section LenPts
open NockvmE2E.Exec.E2ELR NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Rap

theorem termsAt_length (XI : ExecInst) (slots : Array VF.K3) (ζ : VF.K3) (vT : Array (Array VF.K3)) :
    (termsAt XI slots ζ vT).length = (XI.tabs.toList.map (fun t => t.chip.cons.size)).sum := by
  unfold termsAt termsK
  rw [List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro t _
  simp [tabCvAt, evalDag]

theorem openPts_size (XI : ExecInst) (zeta : VF.K3) : (openPts XI zeta).size = XI.r + 2 := by
  obtain ⟨h1, _, _⟩ := pts_fold zeta XI.hGen XI.r
  unfold openPts
  simp [h1]

theorem mem_get {α : Type} [Inhabited α] (a : Array α) (i : ℕ) (h : i < a.size) : a[i]! ∈ a.toList := by
  rw [getElem!_pos a i h]
  exact Array.getElem_mem_toList h


theorem hptsU_gen (XI : ExecInst) {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC] [Inhabited B]
    {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
    (P : DeepParams Φ KC ι (Fin (2 ^ XI.nD) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r) (hr : r = XI.r)
    (cI : ι ≃ Fin XI.nc)
    (hptP : ∀ c k ζ, XI.colKind[(cI c).val]! = 2 → A.pt c k ζ = toKV XI.ppt)
    (hptT : ∀ c (k : Fin r) ζ, XI.colKind[(cI c).val]! ≠ 2 → A.pt c k ζ = ζ * psiV XI.hGen ^ k.val) :
    ∀ (ζ : VF.K3) (ck : ι × Fin r), ∃ pt ∈ (openPts XI ζ).toList, toKV pt = A.pt ck.1 ck.2 (toKV ζ) := by
  subst hr
  intro ζ ⟨c, k⟩
  have hpts := openPts_get XI ζ
  have hsz := openPts_size XI ζ
  by_cases h2 : XI.colKind[(cI c).val]! = 2
  · refine ⟨(openPts XI ζ)[XI.r]!, mem_get _ _ (by omega), ?_⟩
    rw [hpts.2.1, hptP c k _ h2]
  · refine ⟨(openPts XI ζ)[k.val]!, mem_get _ _ (by have := k.2; omega), ?_⟩
    rw [hptT c k _ h2]
    exact hpts.1 k.val k.2

end LenPts

/-! ## `da` and the half of `UniLinksN` -/

section DaSec
open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal
open NockvmE2E.Exec.E2ELR NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Lift NockvmE2E.Lift.Alternating NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.SM
  NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.Emb NockvmE2E.Exec.E2EW0 NockvmE2E.Exec.E2EResid
  NockvmE2E.Exec.E2E NockvmE2E.Merkle NockvmE2E.Merkle.Fri NockvmE2E.FriPort NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain

variable (XI : ExecInst) (hn : XI.nD ≤ 32)

set_option hygiene false in
local notation "ωS" => smoothDomain XI.nD hn
set_option hygiene false in
local notation "s1" => (fun _ : Fin (XI.k + 1) => (1 : ℕ+))

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC] [Inhabited B]
variable [SampleableType KC] [Inhabited KC]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ XI.nD) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ KC ι (Fin (2 ^ XI.nD) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ KC → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ KC → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ XI.nD) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin)
variable (d : ℕ+)
variable [∀ j, SampleableType ((pSpec XI.k (ω := ωS) s1 XI.l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : KC ↪ Dg)
  (md : PointMaskData P.colRoundX (Fin (2 ^ XI.nD)) B Dg) (L : Fri.FriLeaves (ω := ωS) s1)
variable (PR : Array VF.K3 → Array VF.G → Prop)

set_option hygiene false in
local notation "RM" => RapP.rapMask Φ KC md.toRapMaskData (P.statement R0 Rest).M0
  (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I0 I Ifin 4

/-- **`da`**: the decoders of the RAP prefix: `M0` clear (the unit message `m0`), blocks 0/1 the slot-order codecs `sl0`/`sl1`, blocks 2/3 the singleton
codecs of `α`/`ζ`, `Mfin` the DEEP parser `finDecG` (R0's final message `mf`). -/
noncomputable def daOf (cI : ι ≃ Fin XI.nc) {n0 n1 : ℕ} (sl0 : {i : Fin Φ.n // Φ.sampledAfter i = 0} ≃ Fin n0)
    (sl1 : {i : Fin Φ.n // Φ.sampledAfter i = 1} ≃ Fin n1) (hPa : Φ.sampledAfter P.a = 2) (hPz : Φ.sampledAfter P.z = 3)
    (ha1 : ∀ i, Φ.sampledAfter i = 2 → i = P.a) (hz1 : ∀ i, Φ.sampledAfter i = 3 → i = P.z)
    (m0 : (P.statement R0 Rest).M0) (mf : R0.Mfin) : MDec (RM) :=
  (({ encC := fun _ => [], decC := fun _ => (), decC_encC := fun _ => rfl, decM := fun _ => m0 } : RDec (unitRound _ I0)),
    ({ encC := blockEnc sl0, decC := blockDec sl0, decC_encC := blockDec_enc sl0 } : CCodec (colRoundR Φ KC _ P.colRoundX I 0)),
    ({ encC := blockEnc sl1, decC := blockDec sl1, decC_encC := blockDec_enc sl1 } : CCodec (colRoundR Φ KC _ P.colRoundX I 1)),
    ({ encC := singEnc P.a hPa, decC := singDec, decC_encC := singDec_enc P.a hPa ha1 } : CCodec (colRoundR Φ KC _ P.colRoundX I 2)),
    ({ encC := singEnc P.z hPz, decC := singDec, decC_encC := singDec_enc P.z hPz hz1 } : CCodec (colRoundR Φ KC _ P.colRoundX I 3)),
    ({ encC := fun _ => [], decC := fun _ => (), decC_encC := fun _ => rfl, decM := finDecG XI cI r P.nq mf } : RDec (unitRound _ Ifin)), ())


set_option hygiene false in
local notation "BM" => bmask (S := S) s1 d XI.l Dg enc L

/-- **the half of `UniLinksN`, assembled**: with `ds := mdAppend RM BM (daOf ..) db`, the fields `hPa hPz hαC hζC hQU hVT hlenU hptsU` are proved here from the
column bijection `cI`, the slot bijections `sl0`/`sl1`, the singleton facts `ha1`/`hz1` and the point facts `hptP`/`hptT`; the Y-half (`hdagU`, `hRVU`) and the
`P`-specific `hH`, `he`, `hnq`, `hcw` are arguments (see `uniLinksN_J` for the J-8 `P`). -/
theorem uniLinksN_of_da (hR : P.R = 2) (hr : r = XI.r) (hkd : ∀ c < XI.nc, XI.colKind[c]! < 3) (cI : ι ≃ Fin XI.nc)
    {n0 n1 : ℕ} (sl0 : {i : Fin Φ.n // Φ.sampledAfter i = 0} ≃ Fin n0) (sl1 : {i : Fin Φ.n // Φ.sampledAfter i = 1} ≃ Fin n1)
    (ha1 : ∀ i, Φ.sampledAfter i = 2 → i = P.a) (hz1 : ∀ i, Φ.sampledAfter i = 3 → i = P.z)
    (m0 : (P.statement R0 Rest).M0) (mf : R0.Mfin) (dY : List ℕ → Dg) (db : MDec (BM))
    (hptP : ∀ c k ζ, XI.colKind[(cI c).val]! = 2 → A.pt c k ζ = toKV XI.ppt)
    (hptT : ∀ c (k : Fin r) ζ, XI.colKind[(cI c).val]! ≠ 2 → A.pt c k ζ = ζ * psiV XI.hGen ^ k.val)
    (hns : P.ns = (XI.tabs.toList.map (fun t => t.chip.cons.size)).sum) (hnq : XI.nq = P.nq)
    (hdagU : ∀ (c0 : Block Φ KC 0) (c1 : Block Φ KC 1) (c2 : Block Φ KC 2) (c3 : Block Φ KC 3) (ζ : VF.K3) (vT : Array (Array VF.K3)),
      CanonIn (slotsAt XI (blockEnc sl0 c0) (blockEnc sl1 c1)) ζ vT →
      ∀ i : Fin P.ns, (termsAt XI (slotsAt XI (blockEnc sl0 c0) (blockEnc sl1 c1)) ζ vT)[i.1]? =
        some (A.Cv (chiOfBlocks c0 c1 c2 c3) (toKV ζ) i (vTOfG XI cI r vT)))
    (hRVU : ∀ (c0 : Block Φ KC 0) (c1 : Block Φ KC 1) (c2 : Block Φ KC 2) (c3 : Block Φ KC 3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3),
      VShape XI vT vQ →
      PR (slotsAt XI (blockEnc sl0 c0) (blockEnc sl1 c1)) (pubAt XI vT) →
      RestV m0 (finDecG XI cI r P.nq mf (deepMsg vT vQ)) (chiOfBlocks c0 c1 c2 c3))
    (hH : P.H = (Finset.range XI.hN).image (fun i => psiV XI.hShift * psiV XI.hGen ^ i)) (he : P.e = 3)
    (hcw : ∀ j : Fin P.nq, toKV VF.K3.gen ^ (j.1 % 3) = P.cw j) :
    UniLinksN XI hn P A R0 Rest RestV e I0 I Ifin d Dg enc md L PR dY
      (mdAppend (RM) (BM) (daOf XI hn P A R0 Rest RestV e I0 I Ifin Dg md cI sl0 sl1 (P.ha.trans hR) (P.hz.trans (by rw [hR])) ha1 hz1 m0 mf) db)
      (vTOfG XI cI r) where
  hPa := P.ha.trans hR
  hPz := P.hz.trans (by rw [hR])
  hαC := fun c => singEnc_dec P.a (P.ha.trans hR) c
  hζC := fun c => singEnc_dec P.z (P.hz.trans (by rw [hR])) c
  hQU := fun vT vQ hsh j => finDecG_vQ XI cI r P.nq hnq mf vT vQ hsh j
  hVT := fun vT vQ hsh => finDecG_vT XI cI r P.nq hr hkd mf vT vQ hsh
  hlenU := fun slots ζ vT => by rw [termsAt_length, hns]
  hdagU := hdagU
  hptsU := hptsU_gen XI P A hr cI hptP hptT
  hRVU := hRVU
  hH := hH
  he := he
  hnq := hnq
  hcw := hcw

end DaSec

/-! ## the J-8 `P` (`deepParamsJ`): the `P`-specific facts -/

section JFacts
open NockvmE2E.J8 NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Deep Domain
open scoped NNReal

variable (XI : ExecInst) (J : RapAirJ (ZMod NockvmE2E.Exec.p) KC) [NeZero J.r] (pr : PubRead J) {ω : SmoothCosetFftDomain XI.nD KC}
  (δ : ℝ≥0) (N : ℕ) (hNH : N ≤ J.H.card) (hpd : ∀ j c, J.pre j = some c → c.natDegree ≤ J.H.card)

/-- `α` is the only coin of block 2, `ζ` of block 3 (`J.hcoin`: every old coin is sampled before round 2) -/
theorem single_az : (∀ i, (extFrame J.Φ0 2).sampledAfter i = 2 → i = (deepParamsJ J pr ω δ N hNH hpd).a) ∧
    (∀ i, (extFrame J.Φ0 2).sampledAfter i = 3 → i = (deepParamsJ J pr ω δ N hNH hpd).z) := by
  have ha : ((deepParamsJ J pr ω δ N hNH hpd).a : ℕ) = J.Φ0.n := rfl
  have hz : ((deepParamsJ J pr ω δ N hNH hpd).z : ℕ) = J.Φ0.n + 1 := rfl
  constructor
  · intro i hi
    apply Fin.ext
    rw [ha]
    simp only [extFrame] at hi
    split_ifs at hi with h
    · have := J.hcoin ⟨i.val, h⟩; omega
    · omega
  · intro i hi
    apply Fin.ext
    rw [hz]
    simp only [extFrame] at hi
    split_ifs at hi with h
    · have := J.hcoin ⟨i.val, h⟩; omega
    · omega

/-- `P.H` is the verifier's union domain (`hHJ`: the interface's `H` is `{hShift · hGen^i : i < hN}`) -/
theorem hH_J (hHJ : J.H = (Finset.range XI.hN).image (fun i => zv XI.hShift * zv XI.hGen ^ i)) :
    (deepParamsJ J pr ω δ N hNH hpd).H = (Finset.range XI.hN).image (fun i => psiV XI.hShift * psiV XI.hGen ^ i) := by
  show HK J = _
  rw [HK, hHJ, Finset.map_eq_image, Finset.image_image]
  apply Finset.image_congr
  intro i _
  simp [psiV, map_mul, map_pow]

theorem hcw_J (hgen : pr.gen = toKV VF.K3.gen) :
    ∀ j : Fin (deepParamsJ J pr ω δ N hNH hpd).nq, toKV VF.K3.gen ^ (j.1 % 3) = (deepParamsJ J pr ω δ N hNH hpd).cw j := by
  intro j; show _ = pr.gen ^ _; rw [hgen]

/-- the opening points of `airJ`: a public column opens at `ppt`, any other at `ζ · hGen^k` -/
theorem pt_J (cI : J.ι0 ≃ Fin XI.nc)
    (hpub : ∀ c, pr.pub c = true ↔ XI.colKind[(cI c).val]! = 2) (hppt : ∀ c, pr.pub c = true → pr.ppt c = toKV XI.ppt)
    (hoff : ∀ t k, J.off t k = zv XI.hGen ^ (k : ℕ)) :
    (∀ c k ζ, XI.colKind[(cI c).val]! = 2 → (airJ J pr ω δ N hNH hpd).pt c k ζ = toKV XI.ppt) ∧
    (∀ c (k : Fin J.r) ζ, XI.colKind[(cI c).val]! ≠ 2 → (airJ J pr ω δ N hNH hpd).pt c k ζ = ζ * psiV XI.hGen ^ k.val) := by
  constructor
  · intro c k ζ h
    show (if pr.pub c then pr.ppt c else _) = _
    rw [if_pos ((hpub c).2 h), hppt c ((hpub c).2 h)]
  · intro c k ζ h
    have : pr.pub c = false := by
      by_contra hc; exact h ((hpub c).1 (by simpa using hc))
    show (if pr.pub c then pr.ppt c else _) = _
    rw [if_neg (by simp [this]), hoff, map_pow]
    rfl

end JFacts

end NockvmE2E.Exec.InstGen

#print axioms NockvmE2E.Exec.InstGen.opsU_of_layout
#print axioms NockvmE2E.Exec.InstGen.uniLinksN_of_da
#print axioms NockvmE2E.Exec.InstGen.single_az
#print axioms NockvmE2E.Exec.InstGen.hH_J
#print axioms NockvmE2E.Exec.InstGen.pt_J
#print axioms NockvmE2E.Exec.InstGen.olInv_fold
