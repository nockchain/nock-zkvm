/-
part 3: the J-9 A public reader (`RdSpec9`) and the J-9 A tie `htie9` (`HtieG` at `InstG.ofJ9A`), from `tieAt9`
through the generic reduction `E2EGenT.htieG_of`.
-/
import NockvmE2E.J9A.GenJ9A
import NockvmE2E.Exec.E2EGenT

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open Polynomial

namespace NockvmE2E.J9A.HtieJ9A

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.E2EGen NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
open NockvmE2E.Exec.E2EGenT NockvmE2E.Exec.DagSem
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.TieJ9A NockvmE2E.J9A.GenJ9A
open NockvmE2E.J8.InstJ8 (P Φ0 ω0)
open NockvmE2E.J8 (RapAirJ TabRestr)
open NockvmE2E.J8.TieJ8 (Route cf KN)
open NockvmE2E.J8.TieJ8G (sizes nsK tabX gbJ chalK)
open NockvmE2E.Exec.E2EJ8P (slOf_get readPub readPub_get)
open NockvmE2E.Rap (Coins)

/-! ## 1. the public message read -/

theorem pubsOK9_core (L : PE.PubLayout) (arr : Array UInt64) (s : Fin 8) (env : KEnv) (b n : ℕ)
    (hp : L.present[s.val]! = true) (hb : L.bases[s.val]! = b) (hl : L.lens[s.val]! = n) (hn : n = tabLens9[s.val]!)
    (hco : ∀ j < n, zv arr[b + j]! = env.pub j) (hsz : b + n ≤ arr.size) :
    PubsOK9 (NockvmE2E.J9A.RVUJ9A.Mof9 L arr) env s := by
  have hg : ∀ j < n, zv (SP.slOf L arr s.val)[j]! = env.pub j := fun j hj => by
    rw [slOf_get L arr s.val j hp (by omega) (by omega)]
    rw [hb]; exact hco j hj
  have hpk : ∀ i, 3 * i + 2 < n → SP.pubK (SP.slOf L arr s.val) i = NockvmE2E.Emit.pubK env i := by
    intro i hi
    unfold SP.pubK NockvmE2E.Emit.pubK
    rw [NockvmE2E.Exec.DagSem.toKV_mk, hg _ (by omega), hg _ (by omega), hg _ (by omega)]
  fin_cases s
  · intro j hj
    have h33 : n = 33 := hn.trans rfl
    have := hg j (by omega)
    simp only [NockvmE2E.J8.InstJ8.xpF, NockvmE2E.J9A.RVUJ9A.Mof9, hj, ↓reduceDIte]
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
  · have h18 : n = 12 := hn.trans rfl
    intro i hi; exact hpk i (by omega)
  · have h18 : n = 6 := hn.trans rfl
    intro i hi; exact hpk i (by omega)

/-- the loader's public layout matches the loaded tables (from `shapeXOkF famJ9A`) -/
theorem layOK9 {XI : ExecInst} (hsh : shapeOkF famJ9A XI = true) (hX : shapeXOkF famJ9A XI = true) (t : Fin XI.tabs.size) :
    XI.pubLay.present[(sigma9 XI t).val]! = true ∧ XI.pubLay.bases[(sigma9 XI t).val]! = XI.tabs[t].pubBase ∧
      XI.pubLay.lens[(sigma9 XI t).val]! = XI.tabs[t].npub ∧ XI.tabs[t].npub = tabLens9[(sigma9 XI t).val]! := by
  simp only [shapeXOkF, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hX
  have hl := hX.2
  unfold layOkF at hl
  simp only [Bool.and_eq_true, beq_iff_eq] at hl
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hlens⟩, htabs⟩, hany⟩ := hl
  obtain ⟨-, hmem⟩ := ids_of_shapeF hsh
  have hm : XI.tabs[t] ∈ XI.tabs.toList := Array.getElem_mem_toList t.2
  have := (Array.all_eq_true_iff_forall_mem.mp htabs) XI.tabs[t] (Array.mem_def.mpr hm)
  have e : famJ9A.tabOf XI.tabs[t].chip.id = some (sigma9 XI t).val := tabOf9_tabIdx9 _ (hmem _ hm)
  rw [e] at this
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  refine ⟨this.1.1, this.1.2, ?_, this.2⟩
  show XI.pubLay.lens[(sigma9 XI t).val]! = _
  rw [hlens, this.2]

/-- **`RdSpec` at J-9 A** -/
theorem rdSpec9 {XI : ExecInst} (hsh : shapeOkF famJ9A XI = true) (hX : shapeXOkF famJ9A XI = true) (d : Datum9A) (hdk : DatumOK9A d)
    (L : Link9 XI d) (R : TabRestr (J9A d hdk)) (hT : R.T' = XI.tabs.size)
    (hσ : ∀ t : Fin R.T', R.σ t = sigma9 XI (Fin.cast hT t)) (hfree : (J9A d hdk).AccOn R.q)
    (npub : ℕ) (hnpub : npub = XI.pubOf.size) (tp) (hcap) :
    ∀ (v : ((InstG.ofJ9A XI hsh d hdk L R hT hσ hfree).JJ npub tp hcap).ι0 → NockvmE2E.Exec.KC) (t : Fin XI.tabs.size) (env : KEnv),
      (∀ s, env.pub s = HdagU.coord0 (v (pubJG (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree) npub tp hcap t s))) →
      PubsOK9 ((prG (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree) npub tp hcap).rd v) env (sigma9 XI t) := by
  intro v t env henv
  obtain ⟨hp, hb, hl, hn⟩ := layOK9 hsh hX t
  have hpubB := hpubB_of_shapeF hsh
  have hbd : XI.tabs[t].pubBase + XI.tabs[t].npub ≤ npub := by
    rw [hnpub]; exact hpubB _ (Array.getElem_mem_toList _)
  show PubsOK9 (NockvmE2E.J9A.RVUJ9A.Mof9 XI.pubLay (readPub npub (fun j => v (Sum.inr j)))) env (sigma9 XI t)
  refine pubsOK9_core _ _ _ env _ _ hp hb hl hn ?_ ?_
  · intro j hj
    have hlt : XI.tabs[t].pubBase + j < npub := by omega
    rw [readPub_get npub (fun j => v (Sum.inr j)) _ hlt, henv j]
    unfold pubJG
    simp only [hlt, ↓reduceDIte]
  · simp only [readPub, Array.size_ofFn]; exact hbd

/-! ## 2. the tie -/

section Tie
variable {XI : ExecInst} (hsh : shapeOkF famJ9A XI = true) (d : Datum9A) (hdk : DatumOK9A d) (L : Link9 XI d)
  (R : TabRestr (J9A d hdk)) (hT : R.T' = XI.tabs.size)
  (hσ : ∀ t : Fin R.T', R.σ t = sigma9 XI (Fin.cast hT t)) (hfree : (J9A d hdk).AccOn R.q)
  (npub : ℕ) (tp : Fin (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree).Jm.T) (hcap : (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree).Cap npub)

instance instNZ9 (d : Datum9A) (hdk : DatumOK9A d) : NeZero (J9A d hdk).r := ⟨by show (2 : ℕ) ≠ 0; norm_num⟩

instance instNZJJ9 : NeZero ((InstG.ofJ9A XI hsh d hdk L R hT hσ hfree).JJ npub tp hcap).r :=
  instNeZeroJJG _ _ _ _

theorem C_dec9 (χ : Coins Φ0 KN) (M : Msg9) (s : Fin 8) (x : Fin (sz9 d s)) :
    (J9A d hdk).C χ M (finSigmaFinEquiv ⟨s, x⟩) = consT9 d χ M s x := by
  show (clJ9A d hdk).Cfun χ M _ = _
  unfold NockvmE2E.J8.IfaceG.CLay.Cfun
  rw [Equiv.symm_apply_apply]
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- **the per-table tie at J-9 A**: `TabTieG` from `tieAt9` (hop 0 and the numerals `NumOK9` of every loaded table, the slot map, the
public reader) -/
theorem tt9 (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ))
    (hnum : ∀ t : Fin XI.tabs.size, NumOK9 d (sigma9 XI t))
    (hop : ∀ t : Fin XI.tabs.size, NockvmE2E.J8.TieJ8.HopZero XI.tabs[t].chip (DOf9 d (sigma9 XI t)) ders cmeta XI.tabs[t].chip.baseCols ∧
      XI.tabs[t].chip.baseCols = bcOf9 (sigma9 XI t))
    (chK : Coins (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree |>.JJ npub tp hcap).Φ0 NockvmE2E.Exec.KC → ℕ → NockvmE2E.Exec.KC)
    (hE : ∀ χ, NockvmE2E.Emit.SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta (chK χ)) (NockvmE2E.J8.TieJ8.χf χ))
    (hrd : ∀ (v : ((InstG.ofJ9A XI hsh d hdk L R hT hσ hfree).JJ npub tp hcap).ι0 → NockvmE2E.Exec.KC) (t : Fin XI.tabs.size) (env : KEnv),
      (∀ s, env.pub s = HdagU.coord0 (v (pubJG (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree) npub tp hcap t s))) →
      PubsOK9 ((prG (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree) npub tp hcap).rd v) env (sigma9 XI t)) :
    TabTieG (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree) npub tp hcap
      (prG (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree) npub tp hcap) chK := by
  intro t' l hl χ v val
  set IG := InstG.ofJ9A XI hsh d hdk L R hT hσ hfree with hIG
  have hT9 := tieAt9 d χ ((prG IG npub tp hcap).rd (fun c => v (c, 0))) (valJ IG npub tp hcap val) ders cmeta
    ⟨fun c => val (colJG IG npub tp hcap t' c, 0),
     fun c => val (colJG IG npub tp hcap t' c, ⟨1 % (IG.JJ npub tp hcap).r, Nat.mod_lt _ (NeZero.pos _)⟩),
     fun s => HdagU.coord0 (v (pubJG IG npub tp hcap t' s, 0)), chK χ, XI.tabs[t'].chip.baseCols⟩
    XI.tabs[t'].chip (sigma9 XI t') (hnum t') (hop t').1 (hop t').2
    (fun n hn => (valJ_apply IG npub tp hcap val (colI9 (sigma9 XI t') n) (colG_mem IG t' n) 0).symm)
    (fun n hn => (valJ_apply IG npub tp hcap val (colI9 (sigma9 XI t') n) (colG_mem IG t' n)
      ⟨1 % (IG.JJ npub tp hcap).r, Nat.mod_lt _ (NeZero.pos _)⟩).symm)
    (hE χ) (hrd (fun c => v (c, 0)) t' _ (fun _ => rfl))
  have hT' := hT9 l hl
  refine Eq.trans (Finset.sum_congr rfl ?_) hT'
  intro k hk
  have hjl : (rt9 d (sigma9 XI t')).jOf l k < sz9 d (sigma9 XI t') := by
    have := ((rt9 d (sigma9 XI t')).h2 l hl k (Finset.mem_range.mp hk)).1
    rwa [rt9_N] at this
  refine congrArg (fun z => cfC k * z) ?_
  refine (dif_pos hjl).trans ?_
  exact (congrArg (MvPolynomial.aeval (R := ZMod NockvmE2E.Exec.p) (valJ IG npub tp hcap val)) (C_dec9 d hdk χ _ (sigma9 XI t') ⟨(rt9 d (sigma9 XI t')).jOf l k, hjl⟩)).trans
    (aeval_consT9_eq d χ _ (valJ IG npub tp hcap val) ⟨sigma9 XI t', ⟨(rt9 d (sigma9 XI t')).jOf l k, hjl⟩⟩)

end Tie

end NockvmE2E.J9A.HtieJ9A

#print axioms NockvmE2E.J9A.HtieJ9A.pubsOK9_core
#print axioms NockvmE2E.J9A.HtieJ9A.layOK9
#print axioms NockvmE2E.J9A.HtieJ9A.rdSpec9
#print axioms NockvmE2E.J9A.HtieJ9A.tt9
