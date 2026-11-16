/-
  NockvmE2E/Exec/DagSemV.lean   (proof-only)

  Semantics of the verifier chip `VC.verifierChipT` (Exec/VChip.lean; `FlatProver.verifierChip` calls it): evaluated at the verifier's slot vector it
  equals the EMITTED chip evaluated at `chalE` (coin i := slot of coin i; derived slot := re/im of `γ'^power`, `qpow`; else the `.chal 63` fallback).
  C1 `qpow`, C2 `chalE`, C3 `evalDagK_verifierChipT`.  Uses the `KC` interpreter of `Exec/DagSem.lean`.
-/
import NockvmE2E.Exec.DagSem
import NockvmE2E.Exec.VChip
import NockvmE2E.Exec.AuxFill
import NockvmE2E.Exec.SoundPub

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace NockvmE2E.Exec.DagSemV
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.Tr NockvmE2E.Exec.DagSem
open NockvmE2E.Exec.VC NockvmE2E.Exec.Aux

/-! ## array/memo helpers -/
noncomputable def memoFrom (env : KEnv) (init : Array KC) (sh : List Ex) : Array KC :=
  sh.foldl (fun (memo : Array KC) s => memo.push (evKC env memo s)) init

theorem memoK_eq (sh : List Ex) (env : KEnv) : memoK sh env = memoFrom env #[] sh := rfl

theorem memoFrom_append (env : KEnv) (init : Array KC) (a b : List Ex) :
    memoFrom env init (a ++ b) = memoFrom env (memoFrom env init a) b := by
  simp [memoFrom, List.foldl_append]

theorem memoFrom_size (env : KEnv) (sh : List Ex) : ∀ init : Array KC, (memoFrom env init sh).size = init.size + sh.length := by
  induction sh with
  | nil => intro init; simp [memoFrom]
  | cons s sh ih => intro init; simp only [memoFrom, List.foldl_cons] at ih ⊢; rw [ih]; simp; omega

theorem getElem!_append_left (A B : Array KC) (i : ℕ) (h : i < A.size) : (A ++ B)[i]! = A[i]! := by
  simp [getElem!_def, Array.getElem?_append, h]

theorem getElem!_append_right (A B : Array KC) (i : ℕ) : (A ++ B)[i + A.size]! = B[i]! := by
  simp [getElem!_def, Array.getElem?_append]

theorem getElem!_push_lt (A : Array KC) (v : KC) (i : ℕ) (h : i < A.size) : (A.push v)[i]! = A[i]! := by
  simp [getElem!_def, Array.getElem?_push, h, Nat.ne_of_lt h]

/-! ## C1 `qpow`, C2 `chalE` -/
noncomputable def qpow (re im : KC) : ℕ → KC × KC
  | 0 => (1, 0)
  | n + 1 => let q := qpow re im n; (q.1 * re + 7 * (q.2 * im), q.1 * im + q.2 * re)

noncomputable def chalE (ders : Array Der) (coinMeta : Array (Nat × Nat)) (chalV : ℕ → KC) (i : ℕ) : KC :=
  let order : Array Nat := orderOf coinMeta
  match order.findIdx? (· == i) with
  | some q => chalV q
  | none => match ders.find? (·.slot == i) with
    | some d =>
      let g := qpow (chalV ((order.findIdx? (· == d.re)).getD 0)) (chalV ((order.findIdx? (· == d.im)).getD 0)) d.power
      if d.isRe then g.1 else g.2
    | none => chalV 63

/-! ## block lemma -/
noncomputable def qarr (re im : KC) : ℕ → Array KC
  | 0 => #[1, 0]
  | p + 1 => qarr re im p ++ #[(qpow re im (p + 1)).1, (qpow re im (p + 1)).2]

theorem qarr_size (re im : KC) (p : ℕ) : (qarr re im p).size = 2 * p + 2 := by
  induction p with
  | zero => rfl
  | succ p ih => simp [qarr, ih]; omega

theorem qarr_get1 (re im : KC) (p : ℕ) (q : ℕ) (hq : q ≤ p) :
    (qarr re im p)[2 * q]! = (qpow re im q).1 ∧ (qarr re im p)[2 * q + 1]! = (qpow re im q).2 := by
  induction p with
  | zero =>
    have : q = 0 := by omega
    subst this; simp [qarr, qpow, getElem!_def]
  | succ p ih =>
    rcases Nat.lt_or_ge q (p + 1) with h | h
    · have := ih (by omega)
      have hs := qarr_size re im p
      refine ⟨?_, ?_⟩
      · rw [qarr, getElem!_append_left _ _ _ (by omega)]; exact this.1
      · rw [qarr, getElem!_append_left _ _ _ (by omega)]; exact this.2
    · have : q = p + 1 := by omega
      subst this
      have hs := qarr_size re im p
      refine ⟨?_, ?_⟩
      · have := getElem!_append_right (qarr re im p) #[(qpow re im (p + 1)).1, (qpow re im (p + 1)).2] 0
        rw [qarr]; rw [show 2 * (p + 1) = 0 + (qarr re im p).size by omega, this]; rfl
      · have := getElem!_append_right (qarr re im p) #[(qpow re im (p + 1)).1, (qpow re im (p + 1)).2] 1
        rw [qarr]; rw [show 2 * (p + 1) + 1 = 1 + (qarr re im p).size by omega, this]; rfl

theorem psiV_7 : psiV (7 : UInt64) = 7 := NockvmE2E.Exec.SP.psiV_seven
theorem psiV_0 : psiV (0 : UInt64) = 0 := by unfold psiV; rw [zv_zero, map_zero]

theorem dblock_memo (env : KEnv) (rp ip base : ℕ) (mp : ℕ) (M : Array KC) (hM : M.size = base) :
    memoFrom env M (dblock rp ip base mp).toList = M ++ qarr (env.chal rp) (env.chal ip) mp := by
  induction mp with
  | zero => simp [dblock, memoFrom, qarr, evKC, psiV_0, psiV_one]; apply Array.ext'; simp
  | succ p ih =>
    have hd : (dblock rp ip base (p + 1)).toList = (dblock rp ip base p).toList ++
        [.add (.mul (.ref (base + 2 * p)) (.chal rp)) (.mul (.cF 7) (.mul (.ref (base + 2 * p + 1)) (.chal ip))),
         .add (.mul (.ref (base + 2 * p)) (.chal ip)) (.mul (.ref (base + 2 * p + 1)) (.chal rp))] := by
      simp [dblock]
    rw [hd, memoFrom_append, ih]
    have hs := qarr_size (env.chal rp) (env.chal ip) p
    have h1 := qarr_get1 (env.chal rp) (env.chal ip) p p le_rfl
    have g1 : (M ++ qarr (env.chal rp) (env.chal ip) p)[base + 2 * p]! = (qpow (env.chal rp) (env.chal ip) p).1 := by
      rw [show base + 2 * p = 2 * p + M.size by omega, getElem!_append_right]; exact h1.1
    have g2 : (M ++ qarr (env.chal rp) (env.chal ip) p)[base + 2 * p + 1]! = (qpow (env.chal rp) (env.chal ip) p).2 := by
      rw [show base + 2 * p + 1 = (2 * p + 1) + M.size by omega, getElem!_append_right]; exact h1.2
    simp only [memoFrom, List.foldl_cons, List.foldl_nil, evKC]
    rw [getElem!_push_lt _ _ _ (by simp; omega), getElem!_push_lt _ _ _ (by simp; omega), g1, g2, psiV_7]
    rw [qarr]; apply Array.ext'; simp [qpow]

/-! ## the derived-node memo -/
def rpOf (coinMeta : Array (Nat × Nat)) (x : ℕ) : ℕ := ((orderOf coinMeta).findIdx? (· == x)).getD 0

def DInv (ders : Array Der) (coinMeta : Array (Nat × Nat)) (env : KEnv) (st : Array Ex × Array (Nat × Nat × Nat × Nat)) : Prop :=
  ∀ s ∈ st.2.toList, s.2.2.1 + 2 * s.2.2.2 + 2 ≤ st.1.size ∧ s.2.2.2 = mpOf ders s.1 s.2.1 ∧
    ∀ q ≤ s.2.2.2,
      (memoK st.1.toList env)[s.2.2.1 + 2 * q]! = (qpow (env.chal (rpOf coinMeta s.1)) (env.chal (rpOf coinMeta s.2.1)) q).1 ∧
      (memoK st.1.toList env)[s.2.2.1 + 2 * q + 1]! = (qpow (env.chal (rpOf coinMeta s.1)) (env.chal (rpOf coinMeta s.2.1)) q).2

theorem memoK_size (sh : List Ex) (env : KEnv) : (memoK sh env).size = sh.length := by
  rw [memoK_eq, memoFrom_size]; simp

theorem dblock_size (rp ip base mp : ℕ) : (dblock rp ip base mp).size = 2 * mp + 2 := by
  induction mp with
  | zero => rfl
  | succ p ih => simp [dblock, ih]; omega

theorem dnStep_inv (ders : Array Der) (coinMeta : Array (Nat × Nat)) (env : KEnv)
    (st : Array Ex × Array (Nat × Nat × Nat × Nat)) (p : Nat × Nat) (h : DInv ders coinMeta env st) :
    DInv ders coinMeta env (dnStep ders coinMeta st p) := by
  have hmemo : memoK (dnStep ders coinMeta st p).1.toList env =
      memoK st.1.toList env ++ qarr (env.chal (rpOf coinMeta p.1)) (env.chal (rpOf coinMeta p.2)) (mpOf ders p.1 p.2) := by
    simp only [dnStep, Array.toList_append, memoK_eq, memoFrom_append]
    have := dblock_memo env (rpOf coinMeta p.1) (rpOf coinMeta p.2) st.1.size (mpOf ders p.1 p.2) (memoFrom env #[] st.1.toList)
      (by rw [memoFrom_size]; simp)
    exact this
  have hsz : (dnStep ders coinMeta st p).1.size = st.1.size + (2 * mpOf ders p.1 p.2 + 2) := by
    simp [dnStep, dblock_size]
  intro s hs
  rw [hmemo, hsz]
  simp only [dnStep, Array.toList_push, List.mem_append, List.mem_singleton] at hs
  rcases hs with hs | hs
  · obtain ⟨h1, h2, h3⟩ := h s hs
    refine ⟨by omega, h2, fun q hq => ?_⟩
    have := h3 q hq
    have hlt : s.2.2.1 + 2 * q + 1 < (memoK st.1.toList env).size := by rw [memoK_size]; simpa using (by omega : s.2.2.1 + 2 * q + 1 < st.1.size)
    refine ⟨?_, ?_⟩
    · rw [getElem!_append_left _ _ _ (by omega)]; exact this.1
    · rw [getElem!_append_left _ _ _ hlt]; exact this.2
  · subst hs
    refine ⟨by simp; omega, rfl, fun q hq => ?_⟩
    have hq' := qarr_get1 (env.chal (rpOf coinMeta p.1)) (env.chal (rpOf coinMeta p.2)) (mpOf ders p.1 p.2) q hq
    have hM : (memoK st.1.toList env).size = st.1.size := by rw [memoK_size]; simp
    simp only
    refine ⟨?_, ?_⟩
    · rw [show st.1.size + 2 * q = 2 * q + (memoK st.1.toList env).size by omega, getElem!_append_right]; exact hq'.1
    · rw [show st.1.size + 2 * q + 1 = (2 * q + 1) + (memoK st.1.toList env).size by omega, getElem!_append_right]; exact hq'.2

theorem dnFold_inv (ders : Array Der) (coinMeta : Array (Nat × Nat)) (env : KEnv) (l : List (Nat × Nat)) :
    ∀ st, DInv ders coinMeta env st →
      DInv ders coinMeta env (l.foldl (dnStep ders coinMeta) st) ∧
      (∀ s ∈ st.2.toList, s ∈ (l.foldl (dnStep ders coinMeta) st).2.toList) ∧
      ∀ q ∈ l, ∃ s ∈ (l.foldl (dnStep ders coinMeta) st).2.toList, s.1 = q.1 ∧ s.2.1 = q.2 := by
  induction l with
  | nil => intro st h; exact ⟨h, fun s hs => hs, fun q hq => by simp at hq⟩
  | cons p l ih =>
    intro st h
    have h1 := dnStep_inv ders coinMeta env st p h
    obtain ⟨i1, i2, i3⟩ := ih _ h1
    refine ⟨i1, fun s hs => i2 s (by simp [dnStep, hs]), fun q hq => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · obtain ⟨s, hs, _⟩ : ∃ s ∈ (dnStep ders coinMeta st q).2.toList, s.1 = q.1 ∧ s.2.1 = q.2 :=
        ⟨(q.1, q.2, st.1.size, mpOf ders q.1 q.2), by simp [dnStep], rfl, rfl⟩
      exact ⟨s, i2 s hs, by assumption⟩
    · exact i3 q hq

/-! ## pairs / mpOf / dref -/
theorem pairs_cov_aux (L : List Der) : ∀ init : Array (Nat × Nat),
    (∀ x ∈ init.toList, x ∈ (L.foldl (fun (acc : Array (Nat × Nat)) d => if acc.contains (d.re, d.im) then acc else acc.push (d.re, d.im)) init).toList) ∧
    ∀ d ∈ L, (d.re, d.im) ∈ (L.foldl (fun (acc : Array (Nat × Nat)) d => if acc.contains (d.re, d.im) then acc else acc.push (d.re, d.im)) init).toList := by
  induction L with
  | nil => intro init; simp
  | cons e L ih =>
    intro init
    simp only [List.foldl_cons]
    by_cases hc : init.contains (e.re, e.im) = true
    · rw [if_pos hc]
      obtain ⟨i1, i2⟩ := ih init
      refine ⟨i1, fun d hd => ?_⟩
      rcases List.mem_cons.mp hd with rfl | hd
      · exact i1 _ (Array.mem_def.mp (Array.mem_of_contains_eq_true hc))
      · exact i2 d hd
    · rw [if_neg hc]
      obtain ⟨i1, i2⟩ := ih (init.push (e.re, e.im))
      refine ⟨fun x hx => i1 x (by simp [hx]), fun d hd => ?_⟩
      rcases List.mem_cons.mp hd with rfl | hd
      · exact i1 _ (by simp)
      · exact i2 d hd

theorem pairs_cov (ders : Array Der) (d : Der) (hd : d ∈ ders.toList) : (d.re, d.im) ∈ (pairsOf ders).toList := by
  unfold pairsOf
  rw [← Array.foldl_toList]
  exact (pairs_cov_aux ders.toList #[]).2 d hd

theorem mpOf_aux (re im : ℕ) (L : List Der) : ∀ m : ℕ,
    m ≤ L.foldl (fun m d => if d.re == re && d.im == im then max m d.power else m) m ∧
    ∀ d ∈ L, d.re = re → d.im = im → d.power ≤ L.foldl (fun m d => if d.re == re && d.im == im then max m d.power else m) m := by
  induction L with
  | nil => intro m; simp
  | cons e L ih =>
    intro m
    simp only [List.foldl_cons]
    by_cases hc : (e.re == re && e.im == im) = true
    · rw [if_pos hc]
      obtain ⟨i1, i2⟩ := ih (max m e.power)
      refine ⟨le_trans (le_max_left _ _) i1, fun d hd h1 h2 => ?_⟩
      rcases List.mem_cons.mp hd with rfl | hd
      · exact le_trans (le_max_right _ _) i1
      · exact i2 d hd h1 h2
    · rw [if_neg hc]
      obtain ⟨i1, i2⟩ := ih m
      refine ⟨i1, fun d hd h1 h2 => ?_⟩
      rcases List.mem_cons.mp hd with rfl | hd
      · exfalso; apply hc; simp [h1, h2]
      · exact i2 d hd h1 h2

theorem power_le_mpOf (ders : Array Der) (d : Der) (hd : d ∈ ders.toList) : d.power ≤ mpOf ders d.re d.im := by
  unfold mpOf
  rw [← Array.foldl_toList]
  exact (mpOf_aux d.re d.im ders.toList 0).2 d hd rfl rfl

theorem find_cong (L : List Der) (p q : Der → Bool) (h : ∀ d ∈ L, p d = q d) : L.find? p = L.find? q := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [List.find?_cons, h e (by simp)]
    rw [ih (fun d hd => h d (by simp [hd]))]

theorem drefEntry_spec (S : Array (Nat × Nat × Nat × Nat)) (d : Der) (h : ∃ s ∈ S.toList, s.1 = d.re ∧ s.2.1 = d.im) :
    ∃ s ∈ S.toList, s.1 = d.re ∧ s.2.1 = d.im ∧
      drefEntry S d = some (d.slot, s.2.2.1 + 2 * d.power + (if d.isRe then 0 else 1)) := by
  obtain ⟨s, hs, h1, h2⟩ := h
  have hsome : (S.find? (fun s => s.1 == d.re && s.2.1 == d.im)).isSome = true := by
    rw [← Array.find?_toList, List.find?_isSome]
    exact ⟨s, hs, by simp [h1, h2]⟩
  obtain ⟨s0, hs0⟩ := Option.isSome_iff_exists.mp hsome
  have hm : s0 ∈ S.toList := by
    rw [← Array.find?_toList] at hs0; exact List.mem_of_find?_eq_some hs0
  have hp : (s0.1 == d.re && s0.2.1 == d.im) = true := by
    have hs0' : S.toList.find? (fun s => s.1 == d.re && s.2.1 == d.im) = some s0 := by rw [Array.find?_toList]; exact hs0
    exact List.find?_some (p := fun s : Nat × Nat × Nat × Nat => s.1 == d.re && s.2.1 == d.im) hs0'
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨s0, hm, hp.1, hp.2, by simp [drefEntry, hs0]⟩

theorem fOf_eval (ders : Array Der) (coinMeta : Array (Nat × Nat)) (env : KEnv) (M : Array KC) (i : ℕ) :
    evKC env (memoK (dnSeen ders coinMeta).1.toList env ++ M)
        (fOf (orderOf coinMeta) (drefOf ders (dnSeen ders coinMeta).2) i) = chalE ders coinMeta env.chal i := by
  have hDS : dnSeen ders coinMeta = (pairsOf ders).toList.foldl (dnStep ders coinMeta) (#[], #[]) := by
    unfold dnSeen; rw [Array.foldl_toList]
  obtain ⟨hinv, -, hcov⟩ := dnFold_inv ders coinMeta env (pairsOf ders).toList (#[], #[]) (by intro s hs; simp at hs)
  rw [← hDS] at hinv hcov
  generalize dnSeen ders coinMeta = D at hinv hcov ⊢
  have hcov' : ∀ d ∈ ders.toList, ∃ s ∈ D.2.toList, s.1 = d.re ∧ s.2.1 = d.im := fun d hd =>
    hcov (d.re, d.im) (pairs_cov ders d hd)
  have hfind : (drefOf ders D.2).find? (fun x => x.1 == i) = (ders.find? (fun d => d.slot == i)).bind (drefEntry D.2) := by
    unfold drefOf
    rw [← Array.find?_toList, Array.toList_filterMap, List.find?_filterMap, ← Array.find?_toList]
    congr 1
    apply find_cong
    intro d hd
    obtain ⟨s, _, _, _, he⟩ := drefEntry_spec D.2 d (hcov' d hd)
    simp [he]
  unfold fOf chalE
  rcases h : (orderOf coinMeta).findIdx? (· == i) with _ | p
  · simp only [h, hfind]
    rcases hd : ders.find? (fun d => d.slot == i) with _ | d
    · simp [hd, evKC]
    · have hdm : d ∈ ders.toList := by
        rw [← Array.find?_toList] at hd; exact List.mem_of_find?_eq_some hd
      have hds : d.slot = i := by
        have := List.find?_some (show ders.toList.find? (fun d => d.slot == i) = some d by rw [Array.find?_toList]; exact hd)
        simpa using this
      obtain ⟨s, hs, h1, h2, he⟩ := drefEntry_spec D.2 d (hcov' d hdm)
      obtain ⟨hb, hmp, hval⟩ := hinv s hs
      have hmp' : d.power ≤ s.2.2.2 := by rw [hmp, h1, h2]; exact power_le_mpOf ders d hdm
      have hv := hval d.power hmp'
      rw [h1, h2] at hv
      simp only [rpOf] at hv
      have hsz : (memoK D.1.toList env).size = D.1.size := by rw [memoK_size]; simp
      simp only [he, Option.bind_some, hd]
      cases hre : d.isRe
      · simp only [evKC, Bool.false_eq_true, ↓reduceIte]
        rw [getElem!_append_left _ _ _ (by omega)]; exact hv.2
      · simp only [evKC, ↓reduceIte]
        rw [getElem!_append_left _ _ _ (by omega)]; simpa using hv.1
  · simp [h, evKC]

/-! ## C3 -/
theorem evKC_mapExT (env : KEnv) (A M : Array KC) (f : ℕ → Ex) (ch' : ℕ → KC)
    (hf : ∀ i, evKC env (A ++ M) (f i) = ch' i) (e : Ex) :
    evKC env (A ++ M) (mapExT f A.size e) = evKC { env with chal := ch' } M e := by
  induction e with
  | var k i => rcases k with _ | _ | k <;> simp [mapExT, evKC]
  | cF v => simp [mapExT, evKC]
  | add a b iha ihb => simp [mapExT, evKC, iha, ihb]
  | sub a b iha ihb => simp [mapExT, evKC, iha, ihb]
  | mul a b iha ihb => simp [mapExT, evKC, iha, ihb]
  | neg a ih => simp [mapExT, evKC, ih]
  | pow a n ih => simp [mapExT, evKC, ih]
  | extVar k e => rcases k with _ | _ | k <;> simp [mapExT, evKC]
  | chal i => simp only [mapExT, evKC]; exact hf i
  | ref i => simp only [mapExT, evKC]; exact getElem!_append_right A M i

theorem memoFrom_map (env : KEnv) (A : Array KC) (f : ℕ → Ex) (ch' : ℕ → KC)
    (hf : ∀ M, ∀ i, evKC env (A ++ M) (f i) = ch' i) (S : List Ex) :
    ∀ M : Array KC, memoFrom env (A ++ M) (S.map (mapExT f A.size)) = A ++ memoFrom { env with chal := ch' } M S := by
  induction S with
  | nil => intro M; simp [memoFrom]
  | cons s S ih =>
    intro M
    have h1 := evKC_mapExT env A M f ch' (hf M) s
    have h2 : (A ++ M).push (evKC { env with chal := ch' } M s) = A ++ M.push (evKC { env with chal := ch' } M s) := by
      apply Array.ext'; simp
    have e1 : memoFrom env (A ++ M) ((s :: S).map (mapExT f A.size)) =
        memoFrom env ((A ++ M).push (evKC env (A ++ M) (mapExT f A.size s))) (S.map (mapExT f A.size)) := rfl
    have e2 : memoFrom { env with chal := ch' } M (s :: S) =
        memoFrom { env with chal := ch' } (M.push (evKC { env with chal := ch' } M s)) S := rfl
    rw [e1, e2, h1, h2, ih]

theorem evalDagK_verifierChipT (ch : Chip) (ders : Array Der) (coinMeta : Array (Nat × Nat)) (env : KEnv) :
    evalDagK (verifierChipT ch ders coinMeta).1 env = evalDagK ch { env with chal := chalE ders coinMeta env.chal } := by
  set D := dnSeen ders coinMeta with hD
  set A := memoK D.1.toList env with hA
  have hAs : A.size = D.1.size := by rw [hA, memoK_size]; simp
  have hf : ∀ M, ∀ i, evKC env (A ++ M) (fOf (orderOf coinMeta) (drefOf ders D.2) i) = chalE ders coinMeta env.chal i :=
    fun M i => fOf_eval ders coinMeta env M i
  have hmemo : memoK ((verifierChipT ch ders coinMeta).1.shared).toList env =
      A ++ memoK ch.shared.toList { env with chal := chalE ders coinMeta env.chal } := by
    have h0 : (verifierChipT ch ders coinMeta).1.shared = D.1 ++ ch.shared.map (mapExT (fOf (orderOf coinMeta) (drefOf ders D.2)) D.1.size) := rfl
    rw [h0, Array.toList_append, Array.toList_map, memoK_eq, memoFrom_append, ← memoK_eq, ← hA, ← hAs]
    have := memoFrom_map env A (fOf (orderOf coinMeta) (drefOf ders D.2)) (chalE ders coinMeta env.chal) hf ch.shared.toList #[]
    rw [Array.append_empty] at this
    rw [this, memoK_eq]
  unfold evalDagK
  rw [hmemo]
  show Array.map _ (ch.cons.map _) = _
  rw [Array.map_map]
  congr 1
  funext c
  have := evKC_mapExT env A (memoK ch.shared.toList { env with chal := chalE ders coinMeta env.chal })
    (fOf (orderOf coinMeta) (drefOf ders D.2)) (chalE ders coinMeta env.chal) (hf _) c.e
  rw [hAs] at this
  exact this

/-! ## witness: a 1-constraint chip reading coin 0 and derived slot 2 (= re of γ'^2, γ' = (coin 0, coin 1)) -/
def wCh : Chip := ⟨"w", #[], #[⟨0, 0, 1, .add (.chal 0) (.chal 2)⟩], #[], #[], #[], 0, 0⟩
def wDers : Array Der := #[⟨2, 0, 1, 2, true⟩]
def wMeta : Array (Nat × Nat) := #[(0, 0), (1, 0)]

/-- the verifier chip: `[1, 0, γ'^1 (2 nodes), γ'^2 (2 nodes)]` as shared nodes, and the constraint reads `chal 0 + ref 4` -/
theorem wit_shape :
    (verifierChipT wCh wDers wMeta).1.shared.size = 6 ∧
    exEqB (verifierChipT wCh wDers wMeta).1.cons[0]!.e (.add (.chal 0) (.ref 4)) = true := by
  decide +kernel

theorem wit_eval (env : KEnv) :
    (evalDagK (verifierChipT wCh wDers wMeta).1 env)[0]! =
      env.chal 0 + (qpow (env.chal 0) (env.chal 1) 2).1 := by
  rw [evalDagK_verifierChipT]
  have h0 : (VC.orderOf wMeta).findIdx? (· == 0) = some 0 := by decide +kernel
  have h1 : (VC.orderOf wMeta).findIdx? (· == 1) = some 1 := by decide +kernel
  have h2 : (VC.orderOf wMeta).findIdx? (· == 2) = none := by decide +kernel
  have hf : wDers.find? (·.slot == 2) = some ⟨2, 0, 1, 2, true⟩ := by rfl
  simp [evalDagK, wCh, evKC, memoK, chalE, h0, h1, h2, hf]

#print axioms evalDagK_verifierChipT
#print axioms wit_shape
#print axioms wit_eval

end NockvmE2E.Exec.DagSemV
