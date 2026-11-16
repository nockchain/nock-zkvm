/-
the J-9 AL public reader (`rdSpec9L`) and the per-table tie `tt9L`
(`TabTieG` at `InstG.ofJ9AL`), from `tieAt9L` (`J9AL/TieJ9AL.lean`) through the generic reduction `E2EGenT.htieG_of` (calls it).
Twin of `J9A/HtieJ9A.lean`.  The ALU's loaded chip reads `aluDers`, the other eight read `jDers` (`dersL`); `tt9L` therefore takes the slot
facts for both tables (`hE` for `jDers`, `hEA`/`hY` for `aluDers`; discharged by `slotOK_X`, `slotOK_XL`, `slotY_X`).
Not zero-knowledge.
-/
import NockvmE2E.J9AL.GenJ9AL
import NockvmE2E.J9A.HtieJ9A
import NockvmE2E.Exec.E2EGenT

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

open Polynomial

namespace NockvmE2E.J9AL.HtieJ9AL

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.E2EGen NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
  NockvmE2E.Exec.J9ALChips
open NockvmE2E.Exec.E2EGenT NockvmE2E.Exec.DagSem
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.TieJ9A NockvmE2E.J9A.GenJ9A NockvmE2E.J9A.HtieJ9A
open NockvmE2E.J9AL.InstJ9AL NockvmE2E.J9AL.TieJ9AL NockvmE2E.J9AL.GenJ9AL NockvmE2E.J9AL.TieAluJ9AL
open NockvmE2E.J8.InstJ8 (P Φ0 ω0)
open NockvmE2E.J8 (RapAirJ TabRestr)
open NockvmE2E.J8.TieJ8 (Route cf KN)
open NockvmE2E.J8.TieJ8G (sizes nsK tabX gbJ chalK)
open NockvmE2E.Exec.E2EJ8P (slOf_get readPub readPub_get)
open NockvmE2E.Rap (Coins)

/-! ## 1. the public message read -/

theorem tabLensAL_old (s : Fin 8) : tabLensAL[(s.castSucc : Fin 9).val]! = tabLens9[s.val]! := by fin_cases s <;> rfl

theorem pubsOK9L_core (L : PE.PubLayout) (arr : Array UInt64) (s : Fin 9) (env : KEnv) (b n : ℕ)
    (hp : L.present[s.val]! = true) (hb : L.bases[s.val]! = b) (hl : L.lens[s.val]! = n) (hn : n = tabLensAL[s.val]!)
    (hco : ∀ j < n, zv arr[b + j]! = env.pub j) (hsz : b + n ≤ arr.size) :
    PubsOK9L (Mof9L L arr) env s := by
  rcases Fin.eq_castSucc_or_eq_last s with ⟨s', rfl⟩ | rfl
  · rw [PubsOK9L_old]
    exact pubsOK9_core L arr s' env b n hp hb hl (hn.trans (tabLensAL_old s')) hco hsz
  · have hp : L.present[8]! = true := hp
    have hb : L.bases[8]! = b := hb
    have hl : L.lens[8]! = n := hl
    have hn : n = tabLensAL[8]! := hn
    have hg : ∀ j < n, zv (SP.slOf L arr 8)[j]! = env.pub j := fun j hj => by
      rw [slOf_get L arr 8 j hp (by omega) (by omega)]
      rw [hb]; exact hco j hj
    have h18 : n = 18 := hn.trans rfl
    intro i hi
    show SP.pubK (SP.slOf L arr 8) i = NockvmE2E.Emit.pubK env i
    unfold SP.pubK NockvmE2E.Emit.pubK
    rw [NockvmE2E.Exec.DagSem.toKV_mk, hg _ (by omega), hg _ (by omega), hg _ (by omega)]

/-- the loader's public layout matches the loaded tables (from `shapeXOkF famJ9AL`) -/
theorem layOK9L {XI : ExecInst} (hsh : shapeOkF famJ9AL XI = true) (hX : shapeXOkF famJ9AL XI = true) (t : Fin XI.tabs.size) :
    XI.pubLay.present[(sigma9L XI t).val]! = true ∧ XI.pubLay.bases[(sigma9L XI t).val]! = XI.tabs[t].pubBase ∧
      XI.pubLay.lens[(sigma9L XI t).val]! = XI.tabs[t].npub ∧ XI.tabs[t].npub = tabLensAL[(sigma9L XI t).val]! := by
  simp only [shapeXOkF, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hX
  have hl := hX.2
  unfold layOkF at hl
  simp only [Bool.and_eq_true, beq_iff_eq] at hl
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hlens⟩, htabs⟩, hany⟩ := hl
  obtain ⟨-, hmem⟩ := ids_of_shapeF hsh
  have hm : XI.tabs[t] ∈ XI.tabs.toList := Array.getElem_mem_toList t.2
  have := (Array.all_eq_true_iff_forall_mem.mp htabs) XI.tabs[t] (Array.mem_def.mpr hm)
  have e : famJ9AL.tabOf XI.tabs[t].chip.id = some (sigma9L XI t).val := tabOf9L_tabIdx9L _ (hmem _ hm)
  rw [e] at this
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  refine ⟨this.1.1, this.1.2, ?_, this.2⟩
  show XI.pubLay.lens[(sigma9L XI t).val]! = _
  rw [hlens, this.2]

/-- **`RdSpec` at J-9 AL** -/
theorem rdSpec9L {XI : ExecInst} (hsh : shapeOkF famJ9AL XI = true) (hX : shapeXOkF famJ9AL XI = true) (d : Datum9AL) (hdk : DatumOK9AL d)
    (L : Link9L XI d) (R : TabRestr (J9AL d hdk)) (hT : R.T' = XI.tabs.size)
    (hσ : ∀ t : Fin R.T', R.σ t = sigma9L XI (Fin.cast hT t)) (hfree : (J9AL d hdk).AccOn R.q)
    (npub : ℕ) (hnpub : npub = XI.pubOf.size) (tp) (hcap) :
    ∀ (v : ((InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree).JJ npub tp hcap).ι0 → NockvmE2E.Exec.KC) (t : Fin XI.tabs.size) (env : KEnv),
      (∀ s, env.pub s = HdagU.coord0 (v (pubJG (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree) npub tp hcap t s))) →
      PubsOK9L ((prG (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree) npub tp hcap).rd v) env (sigma9L XI t) := by
  intro v t env henv
  obtain ⟨hp, hb, hl, hn⟩ := layOK9L hsh hX t
  have hpubB := hpubB_of_shapeF hsh
  have hbd : XI.tabs[t].pubBase + XI.tabs[t].npub ≤ npub := by
    rw [hnpub]; exact hpubB _ (Array.getElem_mem_toList _)
  show PubsOK9L (Mof9L XI.pubLay (readPub npub (fun j => v (Sum.inr j)))) env (sigma9L XI t)
  refine pubsOK9L_core _ _ _ env _ _ hp hb hl hn ?_ ?_
  · intro j hj
    have hlt : XI.tabs[t].pubBase + j < npub := by omega
    rw [readPub_get npub (fun j => v (Sum.inr j)) _ hlt, henv j]
    unfold pubJG
    simp only [hlt, ↓reduceDIte]
  · simp only [readPub, Array.size_ofFn]; exact hbd

/-! ## 2. the tie -/

section Tie
variable {XI : ExecInst} (hsh : shapeOkF famJ9AL XI = true) (d : Datum9AL) (hdk : DatumOK9AL d) (L : Link9L XI d)
  (R : TabRestr (J9AL d hdk)) (hT : R.T' = XI.tabs.size)
  (hσ : ∀ t : Fin R.T', R.σ t = sigma9L XI (Fin.cast hT t)) (hfree : (J9AL d hdk).AccOn R.q)
  (npub : ℕ) (tp : Fin (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree).Jm.T) (hcap : (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree).Cap npub)

instance instNZ9L (d : Datum9AL) (hdk : DatumOK9AL d) : NeZero (J9AL d hdk).r := ⟨by show (2 : ℕ) ≠ 0; norm_num⟩

instance instNZJJ9L : NeZero ((InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree).JJ npub tp hcap).r :=
  instNeZeroJJG _ _ _ _

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 50000 in
theorem C_dec9L (χ : Coins Φ0 KN) (M : Msg9L) (s : Fin 9) (x : Fin (sz9L d s)) :
    (J9AL d hdk).C χ M (finSigmaFinEquiv ⟨s, x⟩) = consT9L d χ M s x := by
  show (clJ9AL d hdk).Cfun χ M _ = _
  unfold NockvmE2E.J8.IfaceG.CLay.Cfun
  rw [Equiv.symm_apply_apply]
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- **the per-table tie at J-9 AL**: `TabTieG` from `tieAt9L` (hop 0 and the numerals `NumOK9L` of every loaded table, the slot maps of
`jDers` and `aluDers`, the public reader) -/
theorem tt9L (cmeta : Array (ℕ × ℕ))
    (hnum : ∀ t : Fin XI.tabs.size, NumOK9L d (sigma9L XI t))
    (hop : ∀ t : Fin XI.tabs.size, NockvmE2E.J8.TieJ8.HopZero XI.tabs[t].chip (DOf9L d (sigma9L XI t)) (dersL (sigma9L XI t)) cmeta
        XI.tabs[t].chip.baseCols ∧ XI.tabs[t].chip.baseCols = bcOf9L (sigma9L XI t))
    (chK : Coins (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree |>.JJ npub tp hcap).Φ0 NockvmE2E.Exec.KC → ℕ → NockvmE2E.Exec.KC)
    (hE : ∀ χ, NockvmE2E.Emit.SlotOK (NockvmE2E.Exec.DagSemV.chalE NockvmE2E.Exec.J8Chips.jDers cmeta (chK χ)) (NockvmE2E.J8.TieJ8.χf χ))
    (hEA : ∀ χ, NockvmE2E.Emit.SlotOK (NockvmE2E.Exec.DagSemV.chalE Nock.Emit.aluDers cmeta (chK χ)) (NockvmE2E.J8.TieJ8.χf χ))
    (hY : ∀ χ, SlotY (NockvmE2E.Exec.DagSemV.chalE Nock.Emit.aluDers cmeta (chK χ)) (NockvmE2E.J8.TieJ8.χf χ))
    (hrd : ∀ (v : ((InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree).JJ npub tp hcap).ι0 → NockvmE2E.Exec.KC) (t : Fin XI.tabs.size) (env : KEnv),
      (∀ s, env.pub s = HdagU.coord0 (v (pubJG (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree) npub tp hcap t s))) →
      PubsOK9L ((prG (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree) npub tp hcap).rd v) env (sigma9L XI t)) :
    TabTieG (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree) npub tp hcap
      (prG (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree) npub tp hcap) chK := by
  intro t' l hl χ v val
  set IG := InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree with hIG
  have hE' : NockvmE2E.Emit.SlotOK (NockvmE2E.Exec.DagSemV.chalE (dersL (sigma9L XI t')) cmeta (chK χ)) (NockvmE2E.J8.TieJ8.χf χ) := by
    by_cases h8 : sigma9L XI t' = 8
    · rw [h8]; exact hEA χ
    · rw [dersL_ne _ h8]; exact hE χ
  have hT9 := tieAt9L d χ ((prG IG npub tp hcap).rd (fun c => v (c, 0))) (valJ IG npub tp hcap val) (dersL (sigma9L XI t')) cmeta
    ⟨fun c => val (colJG IG npub tp hcap t' c, 0),
     fun c => val (colJG IG npub tp hcap t' c, ⟨1 % (IG.JJ npub tp hcap).r, Nat.mod_lt _ (NeZero.pos _)⟩),
     fun s => HdagU.coord0 (v (pubJG IG npub tp hcap t' s, 0)), chK χ, XI.tabs[t'].chip.baseCols⟩
    XI.tabs[t'].chip (sigma9L XI t') (hnum t') (hop t').1 (hop t').2
    (fun n hn => (valJ_apply IG npub tp hcap val (colI9L (sigma9L XI t') n) (colG_mem IG t' n) 0).symm)
    (fun n hn => (valJ_apply IG npub tp hcap val (colI9L (sigma9L XI t') n) (colG_mem IG t' n)
      ⟨1 % (IG.JJ npub tp hcap).r, Nat.mod_lt _ (NeZero.pos _)⟩).symm)
    hE' (fun h8 => by rw [h8]; exact hY χ) (hrd (fun c => v (c, 0)) t' _ (fun _ => rfl))
  have hT' := hT9 l hl
  refine Eq.trans (Finset.sum_congr rfl ?_) hT'
  intro k hk
  have hjl : (rt9L d (sigma9L XI t')).jOf l k < sz9L d (sigma9L XI t') := by
    have := ((rt9L d (sigma9L XI t')).h2 l hl k (Finset.mem_range.mp hk)).1
    rwa [rt9L_N] at this
  refine congrArg (fun z => cfC k * z) ?_
  refine (dif_pos hjl).trans ?_
  exact (congrArg (MvPolynomial.aeval (R := ZMod NockvmE2E.Exec.p) (valJ IG npub tp hcap val))
      (C_dec9L d hdk χ _ (sigma9L XI t') ⟨(rt9L d (sigma9L XI t')).jOf l k, hjl⟩)).trans
    (aeval_consT9L_eq d χ _ (valJ IG npub tp hcap val) ⟨sigma9L XI t', ⟨(rt9L d (sigma9L XI t')).jOf l k, hjl⟩⟩)

end Tie

end NockvmE2E.J9AL.HtieJ9AL

#print axioms NockvmE2E.J9AL.HtieJ9AL.pubsOK9L_core
#print axioms NockvmE2E.J9AL.HtieJ9AL.layOK9L
#print axioms NockvmE2E.J9AL.HtieJ9AL.rdSpec9L
#print axioms NockvmE2E.J9AL.HtieJ9AL.C_dec9L
#print axioms NockvmE2E.J9AL.HtieJ9AL.tt9L
