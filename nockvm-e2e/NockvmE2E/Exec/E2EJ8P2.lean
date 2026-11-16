/-
the public-read plumbing of `exec_e2e_J8`: `RdSpec` for the reader `prX`, the canonicalisation
lemma for `PubJ8P`, `hrd`/`hRVU`, `hχ` and slot canonicity.  Part 1 is `Exec/E2EJ8P.lean`.
-/
import NockvmE2E.Exec.E2EJ8P

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.E2EJ8P2
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.E2EJ8P NockvmE2E.J8.TieJ8G NockvmE2E.J8
open NockvmE2E.J8.InstJ8W (sigmaX tabIdx)

/-! ## 1. `RdSpec` -/

theorem pubsOK_core (L : PE.PubLayout) (arr : Array UInt64) (s : Fin 6) (env : NockvmE2E.Exec.DagSem.KEnv) (b n : ℕ)
    (hp : L.present[s.val]! = true) (hb : L.bases[s.val]! = b) (hl : L.lens[s.val]! = n) (hn : n = PE.tabLens[s.val]!)
    (hco : ∀ j < n, zv arr[b + j]! = env.pub j) (hsz : b + n ≤ arr.size) :
    PubsOK (NockvmE2E.J8.RVUJ8.Mof L arr) env s := by
  have hg : ∀ j < n, zv (SP.slOf L arr s.val)[j]! = env.pub j := fun j hj => by
    rw [slOf_get L arr s.val j hp (by omega) (by omega)]
    rw [hb]; exact hco j hj
  have hpk : ∀ i, 3 * i + 2 < n → SP.pubK (SP.slOf L arr s.val) i = NockvmE2E.Emit.pubK env i := by
    intro i hi
    unfold SP.pubK NockvmE2E.Emit.pubK
    rw [NockvmE2E.Exec.DagSem.toKV_mk, hg _ (by omega), hg _ (by omega), hg _ (by omega)]
  have h33 : ∀ (hs : s.val = 0), n = 33 := fun hs => by rw [hn, hs]; rfl
  fin_cases s
  · intro j hj
    have := hg j (by rw [h33 rfl]; exact hj)
    simp only [InstJ8.xpF, NockvmE2E.J8.RVUJ8.Mof, hj, ↓reduceDIte]
    exact this
  · have h18 : n = 18 := hn.trans rfl
    intro i hi; exact hpk i (by omega)
  · have h18 : n = 24 := hn.trans rfl
    intro i hi; exact hpk i (by omega)
  · have h18 : n = 12 := hn.trans rfl
    intro i hi; exact hpk i (by omega)
  · have h18 : n = 36 := hn.trans rfl
    intro i hi; exact hpk i (by omega)
  · have h18 : n = 24 := hn.trans rfl
    intro i hi; exact hpk i (by omega)

section Rd
variable (I : Inst) (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub)

/-- **`RdSpec`** of the reader `prX` (from `j8ShapeXOk`, which gives the layout `LayOK`) -/
theorem rdSpec_X (hnpub : npub = I.XI.pubOf.size) (hX : J8Shape.j8ShapeXOk I.XI = true) :
    RdSpec I npub tp hcap (prX I npub tp hcap) := by
  intro v t env henv
  obtain ⟨hp, hb, hl, hn⟩ := (layOK_of_shapeX I hX).1 t
  have hpubB := J8Shape.hpubB_of_shape I.hsh
  have hbd : I.XI.tabs[t].pubBase + I.XI.tabs[t].npub ≤ npub := by
    rw [hnpub]; exact hpubB _ (Array.getElem_mem_toList _)
  show PubsOK (NockvmE2E.J8.RVUJ8.Mof I.XI.pubLay (readPub npub (fun j => v (Sum.inr j)))) env (sigmaX I.XI t)
  refine pubsOK_core _ _ _ env _ _ hp hb hl hn ?_ ?_
  · intro j hj
    have hlt : I.XI.tabs[t].pubBase + j < npub := by omega
    rw [readPub_get npub (fun j => v (Sum.inr j)) _ hlt, henv j]
    unfold pubJ
    simp only [hlt, ↓reduceDIte]
  · simp only [readPub, Array.size_ofFn]; exact hbd

end Rd

/-! ## 2. canonicalisation of the public array -/
section Canon

def cf (g : UInt64) : UInt64 := UInt64.ofNat (g.toNat % NockvmE2E.Exec.p)
def canonPub (pub : Array UInt64) : Array UInt64 := pub.map cf

theorem p_lt64 : NockvmE2E.Exec.p < 2 ^ 64 := by rw [p_eq]; norm_num

theorem cf_toNat (g : UInt64) : (cf g).toNat = g.toNat % NockvmE2E.Exec.p := by
  unfold cf
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by rw [p_eq]; norm_num)) p_lt64)]

theorem zv_cf (g : UInt64) : zv (cf g) = zv g := by
  unfold zv; rw [cf_toNat, ZMod.natCast_mod]

theorem cf_zero : cf 0 = 0 := by
  apply UInt64.toNat_inj.mp; rw [cf_toNat]; simp

theorem canon_cf (g : UInt64) : canon (cf g) := by
  unfold canon; rw [cf_toNat]; exact Nat.mod_lt _ (by rw [p_eq]; norm_num)

theorem map_getBang (f : Array UInt64) (j : ℕ) : (f.map cf)[j]! = cf f[j]! := by
  by_cases h : j < f.size
  · rw [getElem!_pos _ j (by simpa using h), getElem!_pos _ j h]; simp
  · rw [getElem!_neg _ j (by simpa using h), getElem!_neg _ j h]
    show (default : UInt64) = cf default
    exact cf_zero.symm

theorem pubK_map (f : Array UInt64) (i : ℕ) : SP.pubK (f.map cf) i = SP.pubK f i := by
  unfold SP.pubK
  rw [NockvmE2E.Exec.DagSem.toKV_mk, NockvmE2E.Exec.DagSem.toKV_mk, map_getBang, map_getBang, map_getBang, zv_cf, zv_cf, zv_cf]

theorem slOf_map (L : PE.PubLayout) (pub : Array UInt64) (t : ℕ) : SP.slOf L (canonPub pub) t = (SP.slOf L pub t).map cf := by
  unfold SP.slOf canonPub
  split_ifs
  · rw [Array.map_extract]
  · rw [Array.map_replicate, cf_zero]

theorem labelOf_map (x : Array UInt64) (j : ℕ) : SP.labelOf (x.map cf) j = SP.labelOf x j % NockvmE2E.Exec.p := by
  unfold SP.labelOf; rw [map_getBang, cf_toNat]

theorem claimVec_canon (e : PE.Fp3) (s : ℕ) (hs : s < 2 ^ 64) (hi lo : ℕ) :
    (SP.recQ (PE.claimVec e s hi lo) : Fin 5 → SP.Q) = SP.recQ (PE.claimVec e (s % NockvmE2E.Exec.p) hi lo) := by
  funext k
  have hz : zv (UInt64.ofNat s) = zv (UInt64.ofNat (s % NockvmE2E.Exec.p)) := by
    unfold zv
    rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by rw [p_eq]; norm_num)) p_lt64),
      ZMod.natCast_mod]
  fin_cases k
  all_goals first | rfl | skip
  all_goals
    simp only [SP.recQ, SP.toQ6, PE.claimVec, PE.K6.base, VF.K3.ofG, VF.K3.zero, List.getD_cons_succ, List.getD_cons_zero,
      Fin.mk_one, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.val_two]
    first | rfl | (simp only [NockvmE2E.Exec.DagSem.toKV_mk, hz])

theorem claimStep (z y : PE.K6) (x : Array UInt64) (c : PE.NounRec) (kind hi lo : ℕ) (hkind : kind < NockvmE2E.Exec.p) (r : List PE.K6)
    (h : (if (decide (c.key > 2) || SP.labelOf x (2 * c.key) != kind) = true then none
        else do
          let e ← PE.enc z y c.noun
          pure (PE.claimVec e (SP.labelOf x (2 * c.key + 1)) hi lo)) = some r) :
    ∃ r', (if (decide (c.key > 2) || SP.labelOf (x.map cf) (2 * c.key) != kind) = true then none
        else do
          let e ← PE.enc z y c.noun
          pure (PE.claimVec e (SP.labelOf (x.map cf) (2 * c.key + 1)) hi lo)) = some r' ∧
      (SP.recQ r : Fin 5 → SP.Q) = SP.recQ r' := by
  split at h
  · simp at h
  · rename_i hc
    simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_or, not_not] at hc
    obtain ⟨hk, hl⟩ := hc
    have hc' : ¬ ((decide (c.key > 2) || SP.labelOf (x.map cf) (2 * c.key) != kind) = true) := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_or, not_not]
      refine ⟨hk, ?_⟩
      rw [labelOf_map, hl]; exact Nat.mod_eq_of_lt hkind
    rw [if_neg hc']
    cases he : PE.enc z y c.noun with
    | none => simp [he] at h
    | some e =>
      simp only [he] at h ⊢
      have h2 : (some (PE.claimVec e (SP.labelOf x (2 * c.key + 1)) hi lo) : Option (List PE.K6)) = some r := h
      have h3 := Option.some.inj h2
      subst h3
      have hs : SP.labelOf x (2 * c.key + 1) < 2 ^ 64 := UInt64.toNat_lt _
      refine ⟨PE.claimVec e (SP.labelOf (x.map cf) (2 * c.key + 1)) hi lo, rfl, ?_⟩
      rw [labelOf_map]
      exact claimVec_canon e _ hs hi lo

theorem claimRecS_canon (z y : PE.K6) (x : Array UInt64) (c : PE.NounRec) (r : List PE.K6)
    (h : SP.claimRecS z y x c = some r) :
    ∃ r', SP.claimRecS z y (x.map cf) c = some r' ∧ (SP.recQ r : Fin 5 → SP.Q) = SP.recQ r' := by
  have hp : (2 : ℕ) < NockvmE2E.Exec.p := by rw [p_eq]; norm_num
  unfold SP.claimRecS at h ⊢
  exact claimStep z y x c _ _ _ (by split_ifs <;> omega) r h

theorem claims_canon (z y : PE.K6) (x : Array UInt64) :
    ∀ (l : List PE.NounRec) (cr : List (List PE.K6)), l.mapM (SP.claimRecS z y x) = some cr →
      ∃ cr', l.mapM (SP.claimRecS z y (x.map cf)) = some cr' ∧
        cr.map (fun r => (SP.recQ r : Fin 5 → SP.Q)) = cr'.map (fun r => (SP.recQ r : Fin 5 → SP.Q))
  | [], cr, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨[], by simp, rfl⟩
  | a :: l, cr, h => by
    rw [List.mapM_cons] at h
    cases h1 : SP.claimRecS z y x a with
    | none => simp [h1] at h
    | some r =>
      cases h2 : l.mapM (SP.claimRecS z y x) with
      | none => simp [h1, h2] at h
      | some rs =>
        rw [h1, h2] at h
        have h' : (some (r :: rs) : Option (List (List PE.K6))) = some cr := h
        have h'' := Option.some.inj h'
        subst h''
        obtain ⟨r', hr', hq⟩ := claimRecS_canon z y x a r h1
        obtain ⟨rs', hrs', hq'⟩ := claims_canon z y x l rs h2
        refine ⟨r' :: rs', ?_, ?_⟩
        · rw [List.mapM_cons, hr', hrs']; rfl
        · simp only [List.map_cons, hq, hq']

theorem pubK_map' (f : Array UInt64) : SP.pubK (f.map cf) = SP.pubK f := funext (pubK_map f)

theorem rhoOf_map (x : Array UInt64) : SP.rhoOf (x.map cf) = SP.rhoOf x := by
  funext i; unfold SP.rhoOf; rw [pubK_map, pubK_map, pubK_map, pubK_map]

theorem rhoSOf_map (x : Array UInt64) : SP.rhoSOf (x.map cf) = SP.rhoSOf x := by
  unfold SP.rhoSOf; rw [pubK_map, pubK_map]

theorem toKV_cf (a b c : UInt64) : toKV (VF.K3.mk (cf a) (cf b) (cf c)) = toKV (VF.K3.mk a b c) := by
  simp only [NockvmE2E.Exec.DagSem.toKV_mk, zv_cf]

theorem psiV_cf (g : UInt64) : psiV (cf g) = psiV g := by unfold psiV; rw [zv_cf]

theorem cf_ofNat (n : ℕ) (hn : n < NockvmE2E.Exec.p) : cf (UInt64.ofNat n) = UInt64.ofNat n := by
  apply UInt64.toNat_inj.mp
  rw [cf_toNat, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (lt_trans hn p_lt64), Nat.mod_eq_of_lt hn]

theorem computeDerived_canon (inp : PE.PubIn) (coins : Array VF.K3) (x : Array UInt64)
    (hat : ∀ a ∈ inp.atoms, a.2 < NockvmE2E.Exec.p) (h : SP.ComputeDerivedP inp coins x) :
    SP.ComputeDerivedP inp coins (x.map cf) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨by simpa using h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_getBang, map_getBang, map_getBang, toKV_cf]; exact h1
  · rw [map_getBang, map_getBang, map_getBang, toKV_cf]
    rw [h2]; congr 2; funext q; rw [map_getBang, psiV_cf]
  · rw [map_getBang, h3, cf_zero]
  · rw [map_getBang, h4, cf_zero]
  · rw [map_getBang, h5, cf_zero]
  · intro a ha
    obtain ⟨ha1, ha2, ha3⟩ := h6 a ha
    refine ⟨ha1, ?_, ?_⟩
    · rw [map_getBang, ha2, cf_zero]
    · rw [map_getBang, ha3, cf_ofNat _ (hat a ha)]

/-- **canonicalisation (finding 1)**: `PubJ8P` is stable under reduction of the public array mod `p`, given the instance atoms are `< p` -/
theorem pubJ8P_canon (inp : PE.PubIn) (L : PE.PubLayout) (slotOf : Array ℕ) (slots : Array VF.K3) (pub : Array UInt64)
    (hat : ∀ a ∈ inp.atoms, a.2 < NockvmE2E.Exec.p) (h : NockvmE2E.Merkle.RapFriQ.PubJ8P inp L slotOf slots pub) :
    NockvmE2E.Merkle.RapFriQ.PubJ8P inp L slotOf slots (canonPub pub) := by
  obtain ⟨⟨cr, pr, h1, h2, h3⟩, hd⟩ := h
  obtain ⟨cr', h1', hq⟩ := claims_canon _ _ _ _ cr h1
  refine ⟨⟨cr', pr, ?_, h2, ?_⟩, ?_⟩
  · rw [slOf_map]; exact h1'
  · rw [slOf_map, slOf_map, slOf_map, slOf_map, slOf_map, slOf_map, rhoOf_map, rhoSOf_map]
    rw [pubK_map', pubK_map', pubK_map', pubK_map', pubK_map', ← hq]
    exact h3
  · rw [slOf_map]; exact computeDerived_canon _ _ _ hat hd

end Canon

/-! ## 3. `hrd` and `hRVU` -/
section Hrd
open NockvmE2E.Exec.InstGen NockvmE2E.Exec.E2ELR
variable (I : Inst) (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub)

theorem ofNat_zvval (g : UInt64) : UInt64.ofNat (zv g).val = cf g := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat', cf_toNat]
  unfold zv
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by rw [p_eq]; norm_num)) p_lt64)]

theorem readPub_eq (hnpub : npub = I.XI.pubOf.size) (hr : (I.JJ npub tp hcap).r = I.XI.r) (hkd : ∀ c < I.XI.nc, I.XI.colKind[c]! < 3)
    {M0 : Type} (m0 : M0) (nq : ℕ) (vT : Array (Array VF.K3)) (vQ : Array VF.K3) (hsh : VShape I.XI vT vQ) :
    readPub npub (fun j => (finDecG I.XI (cIX I npub tp hcap hnpub) (I.JJ npub tp hcap).r nq m0 (deepMsg vT vQ)).2.1 (Sum.inr j, 0))
      = canonPub (pubAt I.XI vT) := by
  rw [finDecG_vT I.XI (cIX I npub tp hcap hnpub) _ nq hr hkd m0 vT vQ hsh]
  apply Array.ext
  · simp [readPub, canonPub, pubAt, hnpub]
  · intro i h1 h2
    have hi : i < npub := by simpa [readPub] using h1
    have : (readPub npub fun j => vTOfG I.XI (cIX I npub tp hcap hnpub) (I.JJ npub tp hcap).r vT (Sum.inr j, 0))[i]'h1 =
        UInt64.ofNat (HdagU.coord0 (vTOfG I.XI (cIX I npub tp hcap hnpub) (I.JJ npub tp hcap).r vT (Sum.inr ⟨i, hi⟩, 0))).val := by
      simp [readPub]
    rw [this]
    simp only [canonPub, pubAt, Array.getElem_map]
    have hp : i < I.XI.pubOf.size := by rw [← hnpub]; exact hi
    have e1 : ((cIX I npub tp hcap hnpub (Sum.inr ⟨i, hi⟩) : Fin I.XI.nc) : ℕ) = I.XI.pubOf[i] := by
      show I.XI.pubOf[i]! = _
      exact getElem!_pos _ i hp
    have e2 : vTOfG I.XI (cIX I npub tp hcap hnpub) (I.JJ npub tp hcap).r vT (Sum.inr ⟨i, hi⟩, 0) =
        toKV ((vT[I.XI.pubOf[i]]!)[0]!) := by
      unfold vTOfG
      simp only [e1]
      simp
    rw [e2, HdagU.coord0_toKV, ofNat_zvval]


/-- **`hrd`** of `hRVU_X_of` (c0..c3 do not occur): a canonical public array `pub` with `PubJ8P` and `pr.rd = Mof L pub`.
The `PubJ8P` premise is at the raw `pubAt vT`; `pub := canonPub (pubAt vT)` (finding 1 of the report). -/
theorem hrd_X (hnpub : npub = I.XI.pubOf.size) (hX : J8Shape.j8ShapeXOk I.XI = true) (hat : ∀ a ∈ I.XI.pubIn.atoms, a.2 < NockvmE2E.Exec.p)
    {M0 : Type} (m0 : M0) (nq : ℕ) (slots : Array VF.K3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3) (hsh : VShape I.XI vT vQ)
    (hP : NockvmE2E.Merkle.RapFriQ.PubJ8P I.XI.pubIn I.XI.pubLay I.XI.slotOf slots (pubAt I.XI vT)) :
    ∃ pub : Array UInt64, (∀ g ∈ pub, canon g) ∧ NockvmE2E.Merkle.RapFriQ.PubJ8P I.XI.pubIn I.XI.pubLay I.XI.slotOf slots pub ∧
      (prX I npub tp hcap).rd (fun c => (finDecG I.XI (cIX I npub tp hcap hnpub) (I.JJ npub tp hcap).r nq m0 (deepMsg vT vQ)).2.1 (c, 0)) =
        NockvmE2E.J8.RVUJ8.Mof I.XI.pubLay pub := by
  refine ⟨canonPub (pubAt I.XI vT), ?_, pubJ8P_canon _ _ _ _ _ hat hP, ?_⟩
  · intro g hg
    obtain ⟨a, -, rfl⟩ := Array.mem_map.mp hg
    exact canon_cf a
  · show NockvmE2E.J8.RVUJ8.Mof I.XI.pubLay (readPub npub (fun j => (finDecG I.XI (cIX I npub tp hcap hnpub) (I.JJ npub tp hcap).r nq m0
      (deepMsg vT vQ)).2.1 (Sum.inr j, 0))) = _
    rw [readPub_eq I npub tp hcap hnpub (J8Shape.r_of_shape I.hsh ▸ rfl) (hkd_X I) m0 nq vT vQ hsh]

end Hrd

/-! ## 4. the coin-slot order: `sl0X`, `sl1X` realise `slotOfJ8`, and `hχ` -/
section Slots
open NockvmE2E.J8.InstJ8 (Φ0)
open NockvmE2E.Exec.E2ELR NockvmE2E.Exec.InstGen NockvmE2E.Lift NockvmE2E.Lift.Alternating NockvmE2E.Rap

theorem slot_tab : ∀ i : Fin Φ0.n, (Φ0.sampledAfter i = 0 → J8Shape.slotOfJ8[i.val]! < 13) ∧
    (Φ0.sampledAfter i = 1 → 13 ≤ J8Shape.slotOfJ8[i.val]! ∧ J8Shape.slotOfJ8[i.val]! < 19) := by decide

theorem slot_inj : ∀ i j : Fin Φ0.n, J8Shape.slotOfJ8[i.val]! = J8Shape.slotOfJ8[j.val]! → i = j := by decide

theorem slot_surj0 : ∀ q : Fin 13, ∃ i : Fin Φ0.n, Φ0.sampledAfter i = 0 ∧ J8Shape.slotOfJ8[i.val]! = q.val := by decide

theorem slot_surj1 : ∀ q : Fin 6, ∃ i : Fin Φ0.n, Φ0.sampledAfter i = 1 ∧ J8Shape.slotOfJ8[i.val]! = 13 + q.val := by decide

theorem lt_of_sa0 (i : Fin (extFrame Φ0 2).n) (h : (extFrame Φ0 2).sampledAfter i < 2) : i.1 < Φ0.n := lt_of_sa Φ0 i h

theorem sa_ext (i : Fin Φ0.n) : (extFrame Φ0 2).sampledAfter (extC Φ0 2 i) = Φ0.sampledAfter i := by
  simp [extFrame, extC, i.2]

noncomputable def sl0X : {i : Fin (extFrame Φ0 2).n // (extFrame Φ0 2).sampledAfter i = 0} ≃ Fin 13 :=
  Equiv.ofBijective
    (fun x => ⟨J8Shape.slotOfJ8[x.1.val]!, by
      have hl := lt_of_sa0 x.1 (by rw [x.2]; norm_num)
      have := (slot_tab ⟨x.1.val, hl⟩).1 (by have := x.2; simpa [extFrame, hl] using this)
      exact this⟩)
    ⟨fun x y h => by
      have hl := lt_of_sa0 x.1 (by rw [x.2]; norm_num)
      have hl' := lt_of_sa0 y.1 (by rw [y.2]; norm_num)
      have := slot_inj ⟨x.1.val, hl⟩ ⟨y.1.val, hl'⟩ (by simpa using congrArg Fin.val h)
      exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val this)),
     fun q => by
      obtain ⟨i, hi, hq⟩ := slot_surj0 q
      refine ⟨⟨extC Φ0 2 i, by rw [sa_ext]; exact hi⟩, Fin.ext ?_⟩
      simpa [extC] using hq⟩

noncomputable def sl1X : {i : Fin (extFrame Φ0 2).n // (extFrame Φ0 2).sampledAfter i = 1} ≃ Fin 6 :=
  Equiv.ofBijective
    (fun x => ⟨J8Shape.slotOfJ8[x.1.val]! - 13, by
      have hl := lt_of_sa0 x.1 (by rw [x.2]; norm_num)
      have : 13 ≤ J8Shape.slotOfJ8[x.1.val]! ∧ J8Shape.slotOfJ8[x.1.val]! < 19 :=
        (slot_tab ⟨x.1.val, hl⟩).2 (by have := x.2; simpa [extFrame, hl] using this)
      omega⟩)
    ⟨fun x y h => by
      have hl := lt_of_sa0 x.1 (by rw [x.2]; norm_num)
      have hl' := lt_of_sa0 y.1 (by rw [y.2]; norm_num)
      have h1 : 13 ≤ J8Shape.slotOfJ8[x.1.val]! ∧ J8Shape.slotOfJ8[x.1.val]! < 19 :=
        (slot_tab ⟨x.1.val, hl⟩).2 (by have := x.2; simpa [extFrame, hl] using this)
      have h2 : 13 ≤ J8Shape.slotOfJ8[y.1.val]! ∧ J8Shape.slotOfJ8[y.1.val]! < 19 :=
        (slot_tab ⟨y.1.val, hl'⟩).2 (by have := y.2; simpa [extFrame, hl'] using this)
      have h3 : J8Shape.slotOfJ8[x.1.val]! - 13 = J8Shape.slotOfJ8[y.1.val]! - 13 := congrArg Fin.val h
      have := slot_inj ⟨x.1.val, hl⟩ ⟨y.1.val, hl'⟩ (show J8Shape.slotOfJ8[x.1.val]! = J8Shape.slotOfJ8[y.1.val]! by omega)
      exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val this)),
     fun q => by
      obtain ⟨i, hi, hq⟩ := slot_surj1 q
      refine ⟨⟨extC Φ0 2 i, by rw [sa_ext]; exact hi⟩, Fin.ext ?_⟩
      simp only [extC]
      omega⟩

theorem sl0X_val (i : Fin Φ0.n) (h : (extFrame Φ0 2).sampledAfter (extC Φ0 2 i) = 0) :
    ((sl0X ⟨extC Φ0 2 i, h⟩ : Fin 13) : ℕ) = J8Shape.slotOfJ8[i.val]! := rfl

theorem sl1X_val (i : Fin Φ0.n) (h : (extFrame Φ0 2).sampledAfter (extC Φ0 2 i) = 1) :
    ((sl1X ⟨extC Φ0 2 i, h⟩ : Fin 6) : ℕ) = J8Shape.slotOfJ8[i.val]! - 13 := rfl


/-- **`hχ`** for the rank-order equivalences: the coin `i` of the audited challenge vector is the verifier's `coinsOf` slot `slotOf[i]` -/
theorem hχ_X (XI : ExecInst) (hsh : J8Shape.j8ShapeOk XI = true)
    (c0 : Block (extFrame Φ0 2) KC 0) (c1 : Block (extFrame Φ0 2) KC 1) (c2 : Block (extFrame Φ0 2) KC 2) (c3 : Block (extFrame Φ0 2) KC 3)
    (i : Fin Φ0.n) :
    restr 2 (chiOfBlocks c0 c1 c2 c3) i =
      toKV (SP.coinsOf (slotsAt XI (blockEnc sl0X c0) (blockEnc sl1X c1)) XI.slotOf)[i.val]! := by
  obtain ⟨hso, hnc⟩ := J8Shape.slotOf_of_shape hsh
  have hn0 : XI.nCoins[0]! = 13 := by rw [hnc]; rfl
  have hn1 : XI.nCoins[1]! = 6 := by rw [hnc]; rfl
  have hi19 : i.val < 19 := i.2
  rw [SP.coinsOf_get _ _ i.val hi19, hso]
  have hq := slot_tab i
  have hcoin := InstJ8.hcoin0 i
  have hor : Φ0.sampledAfter i = 0 ∨ Φ0.sampledAfter i = 1 := by omega
  have hlt19 : J8Shape.slotOfJ8[i.val]! < 13 + 6 := by
    rcases hor with h | h
    · have := (hq.1 h); omega
    · have := (hq.2 h); omega
  have hslot := hslot_gen Φ0 XI (J8Shape.derived_of_shape hsh) hn0 hn1 sl0X sl1X c0 c1 c2 c3 J8Shape.slotOfJ8[i.val]! hlt19
  rw [hslot]
  unfold chalK
  rcases hor with h | h
  · have hlt := hq.1 h
    rw [dif_pos hlt]
    have h0 : (extFrame Φ0 2).sampledAfter (extC Φ0 2 i) = 0 := by rw [sa_ext]; exact h
    have e : sl0X.symm ⟨J8Shape.slotOfJ8[i.val]!, hlt⟩ = ⟨extC Φ0 2 i, h0⟩ :=
      (Equiv.symm_apply_eq _).2 (Fin.ext (sl0X_val i h0)).symm
    congr 1
    apply Fin.ext
    simp only [e, extC]
  · have hge := hq.2 h
    rw [dif_neg (by omega), dif_pos (by omega)]
    have h1 : (extFrame Φ0 2).sampledAfter (extC Φ0 2 i) = 1 := by rw [sa_ext]; exact h
    have e : sl1X.symm ⟨J8Shape.slotOfJ8[i.val]! - 13, by omega⟩ = ⟨extC Φ0 2 i, h1⟩ :=
      (Equiv.symm_apply_eq _).2 (Fin.ext (sl1X_val i h1)).symm
    congr 1
    apply Fin.ext
    simp only [e, extC]

end Slots

/-! ## 5. `hpJ`, `hpV`: absent jet / atom-walk table means `present = false` -/
section Pres
open NockvmE2E.J8.InstJ8W (sigmaX tabIdx)
variable (I : Inst)

theorem present_false_of_hN0 (hX : J8Shape.j8ShapeXOk I.XI = true) (s : Fin 6) (id : String) (hid : InstJ8.tabId s = id)
    (h0 : InstJ8.hNof I.XI id = 0) : I.XI.pubLay.present[s.val]! = false := by
  by_cases hex : ∃ t : Fin I.XI.tabs.size, sigmaX I.XI t = s
  · exfalso
    obtain ⟨t, ht⟩ := hex
    obtain ⟨-, hmem⟩ := ids_of_shape I.hsh
    have hm : I.XI.tabs[t] ∈ I.XI.tabs.toList := Array.getElem_mem_toList t.2
    have e1 := (TieJ8G.tabId_tabIdx _ (hmem _ hm))
    have e2 : I.XI.tabs[t].chip.id = id := by
      have : sigmaX I.XI t = tabIdx I.XI.tabs[t].chip.id := rfl
      rw [this] at ht
      rw [← e1, ht, hid]
    have hsome : (InstJ8.tabOf I.XI id).isSome = true :=
      InstJ8.tabOf_isSome_of_mem _ _ (List.mem_map.mpr ⟨_, hm, e2⟩)
    have := InstJ8.hNof_pos_of_isSome (InstJ8.hN_pos_of_shape I.hsh) id hsome
    omega
  · exact (layOK_of_shapeX I hX).2 s (not_exists.mp hex)

theorem hpJ_X (hX : J8Shape.j8ShapeXOk I.XI = true) : I.d.Pb.nJ = 0 → I.XI.pubLay.present[3]! = false := by
  intro h
  have : I.d.Pb.nJ = InstJ8.hNof I.XI "jetChipJ8" := by rw [I.hd]; rfl
  exact present_false_of_hN0 I hX 3 "jetChipJ8" rfl (by omega)

/-- `hpV`: uses the `NumOK` numerals (a loaded atom-walk table has `krootsV ∈ {1,2}`) -/
theorem hpV_X (hX : J8Shape.j8ShapeXOk I.XI = true) (hnum : ∀ t, NumOK I.d (sigmaX I.XI t)) :
    I.d.Pb.krootsV = 0 → I.XI.pubLay.present[5]! = false := by
  intro h
  by_cases hex : ∃ t : Fin I.XI.tabs.size, sigmaX I.XI t = 5
  · exfalso
    obtain ⟨t, ht⟩ := hex
    have := (hnum t).2 ht
    simp [h] at this
  · exact (layOK_of_shapeX I hX).2 5 (not_exists.mp hex)

end Pres

end NockvmE2E.Exec.E2EJ8P2

#print axioms NockvmE2E.Exec.E2EJ8P2.rdSpec_X
#print axioms NockvmE2E.Exec.E2EJ8P2.pubJ8P_canon
#print axioms NockvmE2E.Exec.E2EJ8P2.hrd_X
#print axioms NockvmE2E.Exec.E2EJ8P2.hχ_X
#print axioms NockvmE2E.Exec.E2EJ8P2.hpJ_X
#print axioms NockvmE2E.Exec.E2EJ8P2.hpV_X
#print axioms NockvmE2E.Exec.E2EJ8P2.sl0X
#print axioms NockvmE2E.Exec.E2EJ8P2.sl1X
