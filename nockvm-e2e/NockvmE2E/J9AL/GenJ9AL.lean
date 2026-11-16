/-
the J-9 AL twin of `J9A/GenJ9A.lean`: `nJ9AL`, `J9AL`, the table index `tabIdx9L` / `sigma9L`
of a loaded chip, the local column index `loc9IL`, the datum-to-instance link `Link9L`, the facts about `preJ9L`, `colR9L`, widths, and
`InstG.ofJ9AL`, the generic instance bundle at the J-9 AL interface (family `famJ9AL`, nine tables).
Not zero-knowledge.
-/
import NockvmE2E.J9AL.InstJ9AL
import NockvmE2E.J9AL.TieJ9AL
import NockvmE2E.J9A.GenJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.E2EJ9ALIface
import NockvmE2E.Exec.E2EGenG
import NockvmE2E.Exec.J9ALChipsFam

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

open Polynomial

namespace NockvmE2E.J9AL.GenJ9AL

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.E2EGen NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
  NockvmE2E.Exec.J9ALChips
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.TieJ9A NockvmE2E.J9A.GenJ9A
open NockvmE2E.J9AL.InstJ9AL NockvmE2E.J9AL.TieJ9AL
open NockvmE2E.J8.InstJ8 (P Φ0 ω0 preOf)
open NockvmE2E.J8 (RapAirJ TabRestr)
open Nock.TraceGenExe (deltaF powerBasis3)
open NockvmE2E.J8.IfaceG (ofIface)
open NockvmE2E.J8.TieJ8G (rowNodeSet_pows)
open NockvmE2E.J8.IfaceG (CLay NIface)
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL

attribute [local instance] Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9AIface.twinFact
  Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9AIface.twinAlg

/-! ## 0. `nJ9AL`, `J9AL` -/

/-- **`nJ9AL`**: N1-N3 at J-9 AL, the four `E2EJ9ALIface` terms (`hAL` goes into `eps` and `sound` only) -/
noncomputable def nJ9AL (d : Datum9AL) (hd : DatumOK9AL d) :
    NIface (Tr := TrJ9AL (ZMod P)) StJ9AL (MsgJ9AL' P Nock.TraceGenExe.KC deltaF) (AccJ9AL d) (Nock.Jet.HoldsN d.c) where
  list := E2EJ9ALIface.listJ9AL deltaF powerBasis3 d.Pb d.c d.r d.g hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV hd.hnM hd.hreg9P
  eps := E2EJ9ALIface.epsilonOf_listJ9AL deltaF powerBasis3 d.Pb d.c hd.hcK hd.hr hd.hAX hd.hSP hd.hAL hd.hg
    hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV hd.hnM hd.hreg9P
  sound := by
    intro χ M tr h hs
    have := NockvmE2E.J8.InstJ8.charP_KC'
    have := NockvmE2E.J8.InstJ8.charP_KQ'
    exact E2EJ9ALIface.soundJ9AL_pointwise deltaF powerBasis3 d.Pb hd.hRg d.c rfl hd.hr hd.hAX hd.hSP hd.hAL hd.hqM hd.hk hd.hmax hd.hg
      hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV hd.hnM hd.hreg9P χ M tr h hs
  oneRound := by
    intro s hs
    have := E2EJ9ALIface.oneRound_listJ9AL deltaF powerBasis3 d.Pb d.c d.r d.g hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV hd.hnM hd.hreg9P s hs
    exact this

/-- the J-9 AL interface -/
noncomputable def J9AL (d : Datum9AL) (hd : DatumOK9AL d) : RapAirJ (ZMod P) Nock.TraceGenExe.KC :=
  ofIface (clJ9AL d hd) (nJ9AL d hd)

/-! ## 1. table index, local column index -/

/-- the interface table of a chip id (the other ids of the family are never looked up) -/
def tabIdx9L (id : String) : Fin 9 := if id = "aluChipJ9" then 8 else (tabIdx9 id).castSucc

/-- the chip id of an interface table -/
def idOf9L : Fin 9 → String
  | 0 => idOf9 0 | 1 => idOf9 1 | 2 => idOf9 2 | 3 => idOf9 3 | 4 => idOf9 4 | 5 => idOf9 5 | 6 => idOf9 6 | 7 => idOf9 7
  | 8 => "aluChipJ9"

theorem idOf9L_old (s : Fin 8) : idOf9L s.castSucc = idOf9 s := by fin_cases s <;> rfl

def sigma9L (XI : ExecInst) (t : Fin XI.tabs.size) : Fin 9 := tabIdx9L XI.tabs[t].chip.id

theorem tabIdx9L_inj : ∀ a ∈ idsJ9AL, ∀ b ∈ idsJ9AL, tabIdx9L a = tabIdx9L b → a = b := by decide +kernel

theorem idOf9L_tabIdx9L : ∀ a ∈ idsJ9AL, idOf9L (tabIdx9L a) = a := by decide +kernel

theorem tabOf9L_tabIdx9L : ∀ a ∈ idsJ9AL, tabOfAL a = some (tabIdx9L a).val := by decide +kernel

theorem wJ9AL_eq : ∀ a ∈ idsJ9AL, wJ9AL a = wOf9L (tabIdx9L a) := by decide +kernel

theorem sigma9L_inj {XI : ExecInst} (h : shapeOkF famJ9AL XI = true) : Function.Injective (sigma9L XI) := by
  obtain ⟨hnd, hmem⟩ := ids_of_shapeF h
  intro a b hab
  have h1 : XI.tabs[a].chip.id = XI.tabs[b].chip.id :=
    tabIdx9L_inj _ (hmem _ (Array.getElem_mem_toList a.2)) _ (hmem _ (Array.getElem_mem_toList b.2)) hab
  have hnd' : (XI.tabs.toList.map (·.chip.id)).Nodup := hnd
  rw [List.nodup_iff_injective_get] at hnd'
  have := @hnd' ⟨a.1, by simp⟩ ⟨b.1, by simp⟩ (by simpa using h1)
  exact Fin.ext (by simpa using congrArg Fin.val this)

/-- the local index of an interface column -/
def loc9IL : Ι9L → ℕ := Sum.elim loc9I Fin.val

theorem colI9L_loc9IL (j : Ι9L) : colI9L (tabΙ9L j) (loc9IL j) = j := by
  rcases j with j | j
  · show colI9L (tabΙ9 j).castSucc (loc9I j) = Sum.inl j
    rw [colI9L_old, colI9_loc9I]
  · show iL ⟨(j : ℕ) % 196, _⟩ = iL j
    exact congrArg iL (Fin.ext (Nat.mod_eq_of_lt j.2))

theorem loc9IL_lt (j : Ι9L) : loc9IL j < wOf9L (tabΙ9L j) := by
  rcases j with j | j
  · show loc9I j < wOf9L (tabΙ9 j).castSucc
    rw [wOf9L_old]; exact loc9I_lt j
  · exact j.2

theorem loc9IL_colI9L (s : Fin 9) (c : ℕ) (hc : c < wOf9L s) : loc9IL (colI9L s c) = c := by
  rcases Fin.eq_castSucc_or_eq_last s with ⟨s', rfl⟩ | rfl
  · rw [wOf9L_old] at hc
    rw [colI9L_old]
    exact loc9I_colI9 s' c hc
  · show c % 196 = c
    exact Nat.mod_eq_of_lt hc

/-! ## 2. the datum link -/

/-- the number of rows of each table of the datum -/
def Nof9L (d : Datum9AL) : Fin 9 → ℕ
  | 0 => d.Pb.n | 1 => d.Pb.nC | 2 => d.Pb.nW | 3 => d.Pb.nJ | 4 => d.Pb.nA | 5 => d.Pb.nV | 6 => d.Pb.nX | 7 => d.Pb.nS
  | 8 => d.Pb.nL

/-- **[datum] the link of the J-9 AL datum to the loaded instance** (twin of `Link9`): the union domain is the verifier's, every table's row
nodes (the ALU's included) are the powers of the verifier's generator, the table sizes are the loaded tables' `hN`. -/
structure Link9L (XI : ExecInst) (d : Datum9AL) : Prop where
  hdN : d.hN = XI.hN
  hdω : d.ω = zv XI.hGen
  hom : ∀ t, omegaOf9L d t = zv XI.hGen
  nodes0 : ∀ i, d.Pb.nodes i = zv XI.hGen ^ (i : ℕ)
  nodesC : ∀ i, d.Pb.nodesC i = zv XI.hGen ^ (i : ℕ)
  nodesW : ∀ i, d.Pb.nodesW i = zv XI.hGen ^ (i : ℕ)
  nodesJ : ∀ i, d.Pb.nodesJ i = zv XI.hGen ^ (i : ℕ)
  nodesA : ∀ i, d.Pb.nodesA i = zv XI.hGen ^ (i : ℕ)
  nodesV : ∀ i, d.Pb.nodesV i = zv XI.hGen ^ (i : ℕ)
  nodesX : ∀ i, d.Pb.nodesX i = zv XI.hGen ^ (i : ℕ)
  nodesS : ∀ i, d.Pb.nodesS i = zv XI.hGen ^ (i : ℕ)
  nodesL : ∀ i, d.Pb.nodesL i = zv XI.hGen ^ (i : ℕ)
  n_le : ∀ t, Nof9L d t ≤ XI.hN
  n_tab : ∀ t : Fin XI.tabs.size, Nof9L d (sigma9L XI t) = XI.tabs[t].hN

section Link
variable {XI : ExecInst} {d : Datum9AL}

theorem hdom9L (h : shapeOkF famJ9AL XI = true) (L : Link9L XI d) :
    HdomOf9L d = (Finset.range XI.hN).image (fun i => zv XI.hShift * zv XI.hGen ^ i) := by
  rw [hShift_of_shapeF h, zv_one]
  show (Finset.range d.hN).image (fun i => d.ω ^ i) = _
  rw [L.hdN, L.hdω]
  simp only [one_mul]
  rfl

theorem htOf9L_eq (L : Link9L XI d) (t : Fin 9) :
    HtOf9L d t = (Finset.range (Nof9L d t)).image (fun i => zv XI.hGen ^ i) := by
  fin_cases t
  · exact rowNodeSet_pows _ _ L.nodes0
  · exact rowNodeSet_pows _ _ L.nodesC
  · exact rowNodeSet_pows _ _ L.nodesW
  · exact rowNodeSet_pows _ _ L.nodesJ
  · exact rowNodeSet_pows _ _ L.nodesA
  · exact rowNodeSet_pows _ _ L.nodesV
  · exact rowNodeSet_pows _ _ L.nodesX
  · exact rowNodeSet_pows _ _ L.nodesS
  · exact rowNodeSet_pows _ _ L.nodesL

theorem hdomt9L (h : shapeOkF famJ9AL XI = true) (L : Link9L XI d) (t : Fin XI.tabs.size) :
    HtOf9L d (sigma9L XI t) = (Finset.range XI.tabs[t].hN).image (fun i => zv XI.hShift * zv XI.hGen ^ i) := by
  rw [htOf9L_eq L, L.n_tab t, hShift_of_shapeF h, zv_one]
  simp only [one_mul]
  rfl

theorem inj_pows9L (h : shapeOkF famJ9AL XI = true) {n : ℕ} (hn : n ≤ XI.hN) :
    Function.Injective (fun i : Fin n => zv XI.hGen ^ (i : ℕ)) := by
  intro a b hab
  have := hinj_F h (show (a : ℕ) ∈ (Finset.range XI.hN : Set ℕ) by simpa using lt_of_lt_of_le a.2 hn)
    (show (b : ℕ) ∈ (Finset.range XI.hN : Set ℕ) by simpa using lt_of_lt_of_le b.2 hn)
    (by simpa [hShift_of_shapeF h, zv_one] using hab)
  exact Fin.ext this

end Link

/-! ## 3. the fixed columns: degrees and absent columns -/

section Pre
variable {XI : ExecInst} {d : Datum9AL}
open NockvmE2E.Exec.E2EJ8P (natDeg_interp_le preOf_deg preOf_none)

theorem hpdeg9L (h : shapeOkF famJ9AL XI = true) (L : Link9L XI d) (hdk : DatumOK9AL d) :
    ∀ j c, preJ9L d j = some c → c.natDegree ≤ XI.hN := by
  intro j c hj
  have hi : ∀ {n : ℕ} (nodes : Fin n → ZMod P), (∀ i, nodes i = zv XI.hGen ^ (i : ℕ)) → n ≤ XI.hN → Function.Injective nodes :=
    fun nodes e hn a b hab => inj_pows9L h hn (by rw [e a, e b] at hab; exact hab)
  rcases j with c' | c'
  · rcases c' with c' | c' | c' | c' | c' | c' | c' | c'
    · have h' : preJ9 d.toA (Sum.inl c') = some c := hj
      refine (preOf_deg h' ?_).trans (L.n_le 0)
      intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ L.nodes0 (L.n_le 0)) _
    · have h' : preJ9 d.toA (Sum.inr (Sum.inl c')) = some c := hj
      refine (preOf_deg h' ?_).trans (L.n_le 1)
      intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ L.nodesC (L.n_le 1)) _
    · have h' : preJ9 d.toA (Sum.inr (Sum.inr (Sum.inl c'))) = some c := hj
      refine (preOf_deg h' ?_).trans (L.n_le 2)
      intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ L.nodesW (L.n_le 2)) _
    · have h' : preJ9 d.toA (Sum.inr (Sum.inr (Sum.inr (Sum.inl c')))) = some c := hj
      refine (preOf_deg h' ?_).trans (L.n_le 3)
      intro j; exact natDeg_interp_le _ (hi _ L.nodesJ (L.n_le 3)) _
    · have h' : preJ9 d.toA (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c'))))) = some c := hj
      refine (preOf_deg h' ?_).trans (L.n_le 4)
      intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ L.nodesA (L.n_le 4)) _
    · have h' : preJ9 d.toA (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c')))))) = some c := hj
      refine (preOf_deg h' ?_).trans (L.n_le 5)
      intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ L.nodesV (L.n_le 5)) _
    · have h' : preJ9 d.toA (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c'))))))) = some c := hj
      refine (preOf_deg h' ?_).trans (L.n_le 6)
      intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ L.nodesX (L.n_le 6)) _
    · have h' : preJ9 d.toA (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr c'))))))) = some c := hj
      refine (preOf_deg h' ?_).trans (L.n_le 7)
      intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ L.nodesS (L.n_le 7)) _
  · -- the ALU: two Lagrange masks (degree ≤ nL ≤ hN) and the three loaded `preL` columns (`hpreLdeg`)
    refine preOf_deg (N := XI.hN) hj (fun j => ?_)
    show (AluSZChipJ9.preOf _ _ _ j).natDegree ≤ XI.hN
    unfold AluSZChipJ9.preOf
    split_ifs
    · exact (natDeg_interp_le _ (hi _ L.nodesL (L.n_le 8)) _).trans (L.n_le 8)
    · exact (natDeg_interp_le _ (hi _ L.nodesL (L.n_le 8)) _).trans (L.n_le 8)
    · exact (hdk.hpreLdeg _).trans (le_of_eq L.hdN)

end Pre

section Pre2
variable {XI : ExecInst} {d : Datum9AL}
open NockvmE2E.Exec.E2EJ8P (natDeg_interp_le preOf_deg preOf_none)

/-- a column that is not a preprocessed (mask / preg) column of its table has no fixed polynomial -/
theorem preJ9L_none (s : Fin 9) (c : ℕ) (hc : c < wOf9L s) (hnot : c ∉ (preIdxAL (idOf9L s)).toList) :
    preJ9L d (colI9L s c) = none := by
  rcases Fin.eq_castSucc_or_eq_last s with ⟨s', rfl⟩ | rfl
  · rw [wOf9L_old] at hc
    rw [idOf9L_old] at hnot
    have hne : idOf9 s' ≠ "aluChipJ9" := by fin_cases s' <;> decide
    have hnot' : c ∉ (preIdx9 (idOf9 s')).toList := by
      simpa [preIdxAL, show (idOf9 s' == "aluChipJ9") = false by simpa using hne] using hnot
    rw [colI9L_old]
    exact preJ9_none s' c hc hnot'
  · have hc' : c % 196 = c := Nat.mod_eq_of_lt hc
    have hnot' : c ∉ [0, 1, 2, 3, 4] := by simpa [preIdxAL, idOf9L] using hnot
    show preOf _ _ = none
    refine preOf_none [0, 1, 2, 3, 4] ?_ ?_
    · intro j
      have := j.2
      show (j : ℕ) ∈ [0, 1, 2, 3, 4]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      change (j : ℕ) < 5 at this
      omega
    · show (c % 196) ∉ [0, 1, 2, 3, 4]
      rw [hc']; exact hnot'

theorem colR9L_eq (a : String) (ha : a ∈ idsJ9AL) (c : ℕ) (hc : c < wOf9L (tabIdx9L a)) :
    colRAL a c = colR9L (colI9L (tabIdx9L a) c) := by
  by_cases h : a = "aluChipJ9"
  · subst h
    have h8 : tabIdx9L "aluChipJ9" = 8 := by simp [tabIdx9L]
    rw [h8] at hc ⊢
    have hc' : c < 196 := hc
    show _ = crAL ⟨c % 196, _⟩
    simp only [colRAL, crAL, beq_self_eq_true, ite_true, Nat.mod_eq_of_lt hc']
  · have ha' : a ∈ idsJ9A := by
      simp only [idsJ9AL, List.mem_append, List.mem_singleton] at ha
      exact ha.resolve_right h
    have e : tabIdx9L a = (tabIdx9 a).castSucc := by simp [tabIdx9L, h]
    rw [e] at hc ⊢
    rw [wOf9L_old] at hc
    rw [colI9L_old]
    show colRAL a c = colR9 (colI9 (tabIdx9 a) c)
    have : colRAL a c = colR9 a c := by simp [colRAL, h]
    rw [this]
    exact colR9_eq a ha' c hc

theorem w_eq9L (h : shapeOkF famJ9AL XI = true) (t : Fin XI.tabs.size) :
    XI.tabs[t].nc - XI.tabs[t].npub = wOf9L (sigma9L XI t) := by
  obtain ⟨-, hmem⟩ := ids_of_shapeF h
  have hm : XI.tabs[t] ∈ XI.tabs.toList := Array.getElem_mem_toList t.2
  have hw := width_of_shapeF h _ hm
  rw [hw]
  exact wJ9AL_eq _ (hmem _ hm)

end Pre2

/-! ## 4. `InstG.ofJ9AL` -/

/-- **`InstG.ofJ9AL`**: the generic instance bundle at the J-9 AL interface.  `R` (the table restriction) is ABSTRACT, as at J-8 / J-9 A. -/
noncomputable def InstG.ofJ9AL (XI : ExecInst) (hsh : shapeOkF famJ9AL XI = true) (d : Datum9AL) (hdk : DatumOK9AL d) (L : Link9L XI d)
    (R : TabRestr (J9AL d hdk)) (hT : R.T' = XI.tabs.size)
    (hσ : ∀ t : Fin R.T', R.σ t = sigma9L XI (Fin.cast hT t)) (hfree : (J9AL d hdk).AccOn R.q) :
    InstG famJ9AL (J9AL d hdk) XI where
  hsh := hsh
  σ := sigma9L XI
  hσinj := sigma9L_inj hsh
  col := colI9L
  loc := loc9IL
  w := wOf9L
  hcolT := tabΙ9L_colI9L
  hcolL := colI9L_loc9IL
  hlocW := loc9IL_lt
  hlocC := loc9IL_colI9L
  hw := w_eq9L hsh
  nloc := sz9L d
  dec := finSigmaFinEquiv.symm
  hdec := fun _ => rfl
  rt := rt9L d
  hrtN := rt9L_N d
  R := R
  hT := hT
  hσR := hσ
  hfree := hfree
  hr := rfl
  hd4 := rfl
  hoff := fun t k => by
    show omegaOf9L d t ^ (k : ℕ) = _
    rw [L.hom t]
    rfl
  hdom := hdom9L hsh L
  hdomt := hdomt9L hsh L
  hpdeg := hpdeg9L hsh L hdk
  hpreN := fun t c hc hnot => by
    have hid := (ids_of_shapeF hsh).2 _ (Array.getElem_mem_toList t.2)
    refine preJ9L_none (sigma9L XI t) c hc ?_
    show c ∉ (preIdxAL (idOf9L (tabIdx9L XI.tabs[t].chip.id))).toList
    rw [show idOf9L (tabIdx9L XI.tabs[t].chip.id) = XI.tabs[t].chip.id from idOf9L_tabIdx9L _ hid]
    exact hnot
  hcolR := fun t c hc =>
    colR9L_eq _ ((ids_of_shapeF hsh).2 _ (Array.getElem_mem_toList t.2)) c hc
  hcapι := by
    show (Fintype.card Ι9L + famJ9AL.pubCap) * 2 + 9 ≤ 2 ^ 12
    rw [card_Ι9L]; norm_num [famJ9AL]
  rdM := Mof9L XI.pubLay

end NockvmE2E.J9AL.GenJ9AL

#print axioms NockvmE2E.J9AL.GenJ9AL.nJ9AL
#print axioms NockvmE2E.J9AL.GenJ9AL.tabIdx9L_inj
#print axioms NockvmE2E.J9AL.GenJ9AL.idOf9L_tabIdx9L
#print axioms NockvmE2E.J9AL.GenJ9AL.tabOf9L_tabIdx9L
#print axioms NockvmE2E.J9AL.GenJ9AL.wJ9AL_eq
#print axioms NockvmE2E.J9AL.GenJ9AL.sigma9L_inj
#print axioms NockvmE2E.J9AL.GenJ9AL.colI9L_loc9IL
#print axioms NockvmE2E.J9AL.GenJ9AL.loc9IL_colI9L
#print axioms NockvmE2E.J9AL.GenJ9AL.hdom9L
#print axioms NockvmE2E.J9AL.GenJ9AL.htOf9L_eq
#print axioms NockvmE2E.J9AL.GenJ9AL.hdomt9L
#print axioms NockvmE2E.J9AL.GenJ9AL.hpdeg9L
#print axioms NockvmE2E.J9AL.GenJ9AL.preJ9L_none
#print axioms NockvmE2E.J9AL.GenJ9AL.colR9L_eq
#print axioms NockvmE2E.J9AL.GenJ9AL.w_eq9L
#print axioms NockvmE2E.J9AL.GenJ9AL.InstG.ofJ9AL
