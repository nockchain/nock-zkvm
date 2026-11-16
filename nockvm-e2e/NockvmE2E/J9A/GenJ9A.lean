/-
part 2: the J-9 A instance bundle `InstG.ofJ9A` (twin of `E2EGen.InstG.ofJ8` / `TieJ8G.Inst`): the table index `tabIdx9` / `sigma9`
of a loaded chip, the local column index `loc9I`, the datum-to-instance link `Link9` (the J-9 A stand-in for J-8's `hd : d.Pb = PbOfX …`,
which has no J-9 A twin yet), and the facts about `preJ9` (degrees, absent columns), `colR9`, widths.
-/
import NockvmE2E.J9A.InstJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.E2EJ9AIface
import NockvmE2E.J9A.TieJ9A
import NockvmE2E.J9A.RVUJ9A
import NockvmE2E.Exec.E2EGenG
import NockvmE2E.Exec.J9AChipsFam

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open Polynomial

namespace NockvmE2E.J9A.GenJ9A

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.E2EGen NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.TieJ9A
open NockvmE2E.J8.InstJ8 (P Φ0 ω0 preOf)
open NockvmE2E.J8 (RapAirJ TabRestr)
open Nock.TraceGenExe (deltaF powerBasis3)
open NockvmE2E.J8.IfaceG (ofIface)
open NockvmE2E.J8.TieJ8G (rowNodeSet_pows)

/-! ## 0. `nJ9A`, `J9A` -/


open NockvmE2E.J8.IfaceG (CLay NIface)
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A

attribute [local instance] Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9AIface.twinFact
  Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9AIface.twinAlg

/-- **`nJ9A`**: N1-N3 at J-9 A, the four `E2EJ9AIface` terms -/
noncomputable def nJ9A (d : Datum9A) (hd : DatumOK9A d) :
    NIface (Tr := TrJ9A (ZMod P)) StJ9A (MsgJ9A' P Nock.TraceGenExe.KC deltaF) (AccJ9A d) (Nock.Jet.HoldsN d.c) where
  list := E2EJ9AIface.listJ9A deltaF powerBasis3 d.Pb d.c d.r d.g hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV hd.hnM hd.hreg9
  eps := E2EJ9AIface.epsilonOf_listJ9A deltaF powerBasis3 d.Pb d.c hd.hcK hd.hr hd.hAX hd.hSP hd.hg
    hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV hd.hnM hd.hreg9
  sound := by
    intro χ M tr h hs
    have := NockvmE2E.J8.InstJ8.charP_KC'
    have := NockvmE2E.J8.InstJ8.charP_KQ'
    exact E2EJ9AIface.soundJ9A_pointwise deltaF powerBasis3 d.Pb hd.hRg d.c rfl hd.hr hd.hAX hd.hSP hd.hqM hd.hk hd.hmax hd.hg
      hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV hd.hnM hd.hreg9 χ M tr h hs
  oneRound := by
    intro s hs
    have := E2EJ9AIface.oneRound_listJ9A deltaF powerBasis3 d.Pb d.c d.r d.g hd.hLC hd.hLM hd.hLW hd.hLA hd.hLV hd.hnM hd.hreg9 s hs
    exact this

/-- the J-9 A interface -/
noncomputable def J9A (d : Datum9A) (hd : DatumOK9A d) : RapAirJ (ZMod P) Nock.TraceGenExe.KC := ofIface (clJ9A d hd) (nJ9A d hd)


/-! ## 1. table index, local column index -/

/-- the interface table of a chip id (the other ids of the family are never looked up) -/
def tabIdx9 (id : String) : Fin 8 :=
  if id = "computeChipVCLHX9" then 0 else if id = "cellChipHQKW" then 1 else if id = "walkChipJ8" then 2
  else if id = "jetChipJ8" then 3 else if id = "atomChipHQL" then 4 else if id = "walkChipHQK" then 5
  else if id = "axisChipJ9" then 6 else 7

/-- the chip id of an interface table -/
def idOf9 : Fin 8 → String
  | 0 => "computeChipVCLHX9" | 1 => "cellChipHQKW" | 2 => "walkChipJ8" | 3 => "jetChipJ8" | 4 => "atomChipHQL"
  | 5 => "walkChipHQK" | 6 => "axisChipJ9" | 7 => "splitChipJ9"

def sigma9 (XI : ExecInst) (t : Fin XI.tabs.size) : Fin 8 := tabIdx9 XI.tabs[t].chip.id

theorem tabIdx9_inj : ∀ a ∈ idsJ9A, ∀ b ∈ idsJ9A, tabIdx9 a = tabIdx9 b → a = b := by decide +kernel

theorem idOf9_tabIdx9 : ∀ a ∈ idsJ9A, idOf9 (tabIdx9 a) = a := by decide +kernel

theorem tabOf9_tabIdx9 : ∀ a ∈ idsJ9A, tabOf9 a = some (tabIdx9 a).val := by decide +kernel

theorem wJ9A_eq : ∀ a ∈ idsJ9A, wJ9A a = wOf9 (tabIdx9 a) := by decide +kernel

theorem sigma9_inj {XI : ExecInst} (h : shapeOkF famJ9A XI = true) : Function.Injective (sigma9 XI) := by
  obtain ⟨hnd, hmem⟩ := ids_of_shapeF h
  intro a b hab
  have h1 : XI.tabs[a].chip.id = XI.tabs[b].chip.id :=
    tabIdx9_inj _ (hmem _ (Array.getElem_mem_toList a.2)) _ (hmem _ (Array.getElem_mem_toList b.2)) hab
  have hnd' : (XI.tabs.toList.map (·.chip.id)).Nodup := hnd
  rw [List.nodup_iff_injective_get] at hnd'
  have := @hnd' ⟨a.1, by simp⟩ ⟨b.1, by simp⟩ (by simpa using h1)
  exact Fin.ext (by simpa using congrArg Fin.val this)

/-- the local index of an interface column -/
def loc9I : Ι9 → ℕ
  | Sum.inl c => c.val
  | Sum.inr (Sum.inl c) => c.val
  | Sum.inr (Sum.inr (Sum.inl c)) => c.val
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl c))) => c.val
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c)))) => c.val
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c))))) => c.val
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c)))))) => c.val
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr c)))))) => c.val

theorem colI9_loc9I (j : Ι9) : colI9 (tabΙ9 j) (loc9I j) = j := by
  rcases j with c | c | c | c | c | c | c | c <;> simp [colI9, tabΙ9, loc9I, Nat.mod_eq_of_lt c.2] <;> rfl

theorem loc9I_lt (j : Ι9) : loc9I j < wOf9 (tabΙ9 j) := by
  rcases j with c | c | c | c | c | c | c | c <;> exact c.2

theorem loc9I_colI9 (s : Fin 8) (c : ℕ) (hc : c < wOf9 s) : loc9I (colI9 s c) = c := by
  fin_cases s <;> simp [colI9, loc9I, wOf9] at hc ⊢ <;> omega

/-! ## 2. the datum link -/

/-- the number of rows of each table of the datum -/
def Nof9 (d : Datum9A) : Fin 8 → ℕ
  | 0 => d.Pb.n | 1 => d.Pb.nC | 2 => d.Pb.nW | 3 => d.Pb.nJ | 4 => d.Pb.nA | 5 => d.Pb.nV | 6 => d.Pb.nX | 7 => d.Pb.nS

/-- **[datum] the link of the J-9 A datum to the loaded instance** (J-8's `hd : d.Pb = PbOfX XI …` plus `hdN`, `hdω`; a `PbOfX9` is not
defined yet, so the same content is stated as facts): the union domain is the verifier's, every table's row nodes are the powers of the
verifier's generator, the table sizes are the loaded tables' `hN`. -/
structure Link9 (XI : ExecInst) (d : Datum9A) : Prop where
  hdN : d.hN = XI.hN
  hdω : d.ω = zv XI.hGen
  hom : ∀ t, omegaOf9 d t = zv XI.hGen
  nodes0 : ∀ i, d.Pb.nodes i = zv XI.hGen ^ (i : ℕ)
  nodesC : ∀ i, d.Pb.nodesC i = zv XI.hGen ^ (i : ℕ)
  nodesW : ∀ i, d.Pb.nodesW i = zv XI.hGen ^ (i : ℕ)
  nodesJ : ∀ i, d.Pb.nodesJ i = zv XI.hGen ^ (i : ℕ)
  nodesA : ∀ i, d.Pb.nodesA i = zv XI.hGen ^ (i : ℕ)
  nodesV : ∀ i, d.Pb.nodesV i = zv XI.hGen ^ (i : ℕ)
  nodesX : ∀ i, d.Pb.nodesX i = zv XI.hGen ^ (i : ℕ)
  nodesS : ∀ i, d.Pb.nodesS i = zv XI.hGen ^ (i : ℕ)
  n_le : ∀ t, Nof9 d t ≤ XI.hN
  n_tab : ∀ t : Fin XI.tabs.size, Nof9 d (sigma9 XI t) = XI.tabs[t].hN

section Link
variable {XI : ExecInst} {d : Datum9A}

theorem hdom9 (h : shapeOkF famJ9A XI = true) (L : Link9 XI d) :
    HdomOf9 d = (Finset.range XI.hN).image (fun i => zv XI.hShift * zv XI.hGen ^ i) := by
  rw [hShift_of_shapeF h, zv_one]
  unfold HdomOf9
  rw [L.hdN, L.hdω]
  simp only [one_mul]
  rfl

theorem htOf9_eq (L : Link9 XI d) (t : Fin 8) :
    HtOf9 d t = (Finset.range (Nof9 d t)).image (fun i => zv XI.hGen ^ i) := by
  fin_cases t
  · exact rowNodeSet_pows _ _ L.nodes0
  · exact rowNodeSet_pows _ _ L.nodesC
  · exact rowNodeSet_pows _ _ L.nodesW
  · exact rowNodeSet_pows _ _ L.nodesJ
  · exact rowNodeSet_pows _ _ L.nodesA
  · exact rowNodeSet_pows _ _ L.nodesV
  · exact rowNodeSet_pows _ _ L.nodesX
  · exact rowNodeSet_pows _ _ L.nodesS

theorem hdomt9 (h : shapeOkF famJ9A XI = true) (L : Link9 XI d) (t : Fin XI.tabs.size) :
    HtOf9 d (sigma9 XI t) = (Finset.range XI.tabs[t].hN).image (fun i => zv XI.hShift * zv XI.hGen ^ i) := by
  rw [htOf9_eq L, L.n_tab t, hShift_of_shapeF h, zv_one]
  simp only [one_mul]
  rfl

theorem inj_pows9 (h : shapeOkF famJ9A XI = true) {n : ℕ} (hn : n ≤ XI.hN) :
    Function.Injective (fun i : Fin n => zv XI.hGen ^ (i : ℕ)) := by
  intro a b hab
  have := hinj_F h (show (a : ℕ) ∈ (Finset.range XI.hN : Set ℕ) by simpa using lt_of_lt_of_le a.2 hn)
    (show (b : ℕ) ∈ (Finset.range XI.hN : Set ℕ) by simpa using lt_of_lt_of_le b.2 hn)
    (by simpa [hShift_of_shapeF h, zv_one] using hab)
  exact Fin.ext this

end Link

/-! ## 3. the fixed columns: degrees and absent columns -/

section Pre
variable {XI : ExecInst} {d : Datum9A}
open NockvmE2E.Exec.E2EJ8P (natDeg_interp_le preOf_deg preOf_none)

theorem hpdeg9 (h : shapeOkF famJ9A XI = true) (L : Link9 XI d) : ∀ j c, preJ9 d j = some c → c.natDegree ≤ XI.hN := by
  intro j c hj
  have hi : ∀ {n : ℕ} (nodes : Fin n → ZMod P), (∀ i, nodes i = zv XI.hGen ^ (i : ℕ)) → n ≤ XI.hN → Function.Injective nodes :=
    fun nodes e hn a b hab => inj_pows9 h hn (by rw [e a, e b] at hab; exact hab)
  rcases j with c' | c' | c' | c' | c' | c' | c' | c'
  · have h' : preJ9 d (Sum.inl c') = some c := hj
    refine (preOf_deg h' ?_).trans (L.n_le 0)
    intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ L.nodes0 (L.n_le 0)) _
  · have h' : preJ9 d (Sum.inr (Sum.inl c')) = some c := hj
    refine (preOf_deg h' ?_).trans (L.n_le 1)
    intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ L.nodesC (L.n_le 1)) _
  · have h' : preJ9 d (Sum.inr (Sum.inr (Sum.inl c'))) = some c := hj
    refine (preOf_deg h' ?_).trans (L.n_le 2)
    intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ L.nodesW (L.n_le 2)) _
  · have h' : preJ9 d (Sum.inr (Sum.inr (Sum.inr (Sum.inl c')))) = some c := hj
    refine (preOf_deg h' ?_).trans (L.n_le 3)
    intro j; exact natDeg_interp_le _ (hi _ L.nodesJ (L.n_le 3)) _
  · have h' : preJ9 d (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c'))))) = some c := hj
    refine (preOf_deg h' ?_).trans (L.n_le 4)
    intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ L.nodesA (L.n_le 4)) _
  · have h' : preJ9 d (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c')))))) = some c := hj
    refine (preOf_deg h' ?_).trans (L.n_le 5)
    intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ L.nodesV (L.n_le 5)) _
  · have h' : preJ9 d (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c'))))))) = some c := hj
    refine (preOf_deg h' ?_).trans (L.n_le 6)
    intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ L.nodesX (L.n_le 6)) _
  · have h' : preJ9 d (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr c'))))))) = some c := hj
    refine (preOf_deg h' ?_).trans (L.n_le 7)
    intro j; fin_cases j <;> exact natDeg_interp_le _ (hi _ L.nodesS (L.n_le 7)) _

end Pre


section Pre2
variable {XI : ExecInst} {d : Datum9A}
open NockvmE2E.Exec.E2EJ8P (natDeg_interp_le preOf_deg preOf_none)

theorem preIdx9_old (id : String) (h1 : id ≠ "computeChipVCLHX9") (h2 : id ≠ "axisChipJ9") (h3 : id ≠ "splitChipJ9") :
    preIdx9 id = J8Shape.preIdxJ8 id := by
  simp [preIdx9, h1, h2, h3]

/-- a column that is not a preprocessed (mask) column of its table has no fixed polynomial -/
theorem preJ9_none (s : Fin 8) (c : ℕ) (hc : c < wOf9 s) (hnot : c ∉ (preIdx9 (idOf9 s)).toList) :
    preJ9 d (colI9 s c) = none := by
  fin_cases s
  · have hc' : c % 137 = c := Nat.mod_eq_of_lt hc
    have hnot' : c ∉ (preIdx9 "computeChipVCLHX9").toList := hnot
    show preOf _ _ = none
    refine preOf_none (preIdx9 "computeChipVCLHX9").toList ?_ ?_
    · intro j; fin_cases j <;> simp [preIdx9] <;> first | exact Or.inl rfl | exact Or.inr rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
    · simpa [hc'] using hnot'
  · have hc' : c % 242 = c := Nat.mod_eq_of_lt hc
    have hnot' : c ∉ (preIdx9 "cellChipHQKW").toList := hnot
    show preOf _ _ = none
    refine preOf_none (preIdx9 "cellChipHQKW").toList ?_ ?_
    · intro j; fin_cases j <;> simp [preIdx9, J8Shape.preIdxJ8] <;> first | exact Or.inl rfl | exact Or.inr rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
    · simpa [hc'] using hnot'
  · have hc' : c % 166 = c := Nat.mod_eq_of_lt hc
    have hnot' : c ∉ (preIdx9 "walkChipJ8").toList := hnot
    show preOf _ _ = none
    refine preOf_none (preIdx9 "walkChipJ8").toList ?_ ?_
    · intro j; fin_cases j <;> simp [preIdx9, J8Shape.preIdxJ8] <;> first | exact Or.inl rfl | exact Or.inr rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
    · simpa [hc'] using hnot'
  · have hc' : c % 71 = c := Nat.mod_eq_of_lt hc
    have hnot' : c ∉ (preIdx9 "jetChipJ8").toList := hnot
    show preOf _ _ = none
    refine preOf_none (preIdx9 "jetChipJ8").toList ?_ ?_
    · intro j; simp [preIdx9, J8Shape.preIdxJ8]; exact j.2
    · simpa [hc'] using hnot'
  · have hc' : c % 349 = c := Nat.mod_eq_of_lt hc
    have hnot' : c ∉ (preIdx9 "atomChipHQL").toList := hnot
    show preOf _ _ = none
    refine preOf_none (preIdx9 "atomChipHQL").toList ?_ ?_
    · intro j; fin_cases j <;> simp [preIdx9, J8Shape.preIdxJ8] <;> first | exact Or.inl rfl | exact Or.inr rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
    · simpa [hc'] using hnot'
  · have hc' : c % 166 = c := Nat.mod_eq_of_lt hc
    have hnot' : c ∉ (preIdx9 "walkChipHQK").toList := hnot
    show preOf _ _ = none
    refine preOf_none (preIdx9 "walkChipHQK").toList ?_ ?_
    · intro j; fin_cases j <;> simp [preIdx9, J8Shape.preIdxJ8] <;> first | exact Or.inl rfl | exact Or.inr rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
    · simpa [hc'] using hnot'
  · have hc' : c % 52 = c := Nat.mod_eq_of_lt hc
    have hnot' : c ∉ (preIdx9 "axisChipJ9").toList := hnot
    show preOf _ _ = none
    refine preOf_none (preIdx9 "axisChipJ9").toList ?_ ?_
    · intro j; fin_cases j <;> simp [preIdx9] <;> first | exact Or.inl rfl | exact Or.inr rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
    · simpa [hc'] using hnot'
  · have hc' : c % 90 = c := Nat.mod_eq_of_lt hc
    have hnot' : c ∉ (preIdx9 "splitChipJ9").toList := hnot
    show preOf _ _ = none
    refine preOf_none (preIdx9 "splitChipJ9").toList ?_ ?_
    · intro j; fin_cases j <;> simp [preIdx9] <;> first | exact Or.inl rfl | exact Or.inr rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
    · simpa [hc'] using hnot'

open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (crC crM crW crJ crA)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A (crC9 crAX crSP)

theorem colR9_eq (a : String) (ha : a ∈ idsJ9A) (c : ℕ) (hc : c < wOf9 (tabIdx9 a)) :
    NockvmE2E.Exec.J9AChips.colR9 a c = NockvmE2E.J9A.InstJ9A.colR9 (colI9 (tabIdx9 a) c) := by
  simp only [idsJ9A, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [NockvmE2E.Exec.J9AChips.colR9, J8Shape.colRB, tabIdx9, colI9, NockvmE2E.J9A.InstJ9A.colR9, wOf9] at hc ⊢ <;>
    simp [Nat.mod_eq_of_lt hc, crC, crM, crW, crJ, crA, crC9, crAX, crSP]

theorem w_eq9 (h : shapeOkF famJ9A XI = true) (t : Fin XI.tabs.size) :
    XI.tabs[t].nc - XI.tabs[t].npub = wOf9 (sigma9 XI t) := by
  obtain ⟨-, hmem⟩ := ids_of_shapeF h
  have hm : XI.tabs[t] ∈ XI.tabs.toList := Array.getElem_mem_toList t.2
  have hw := width_of_shapeF h _ hm
  rw [hw]
  exact wJ9A_eq _ (hmem _ hm)

end Pre2

/-! ## 5. `InstG.ofJ9A` -/

/-- **`InstG.ofJ9A`**: the generic instance bundle at the J-9 A interface.  `R` (the table restriction) is ABSTRACT, as at J-8. -/
noncomputable def InstG.ofJ9A (XI : ExecInst) (hsh : shapeOkF famJ9A XI = true) (d : Datum9A) (hdk : DatumOK9A d) (L : Link9 XI d)
    (R : TabRestr (J9A d hdk)) (hT : R.T' = XI.tabs.size)
    (hσ : ∀ t : Fin R.T', R.σ t = sigma9 XI (Fin.cast hT t)) (hfree : (J9A d hdk).AccOn R.q) :
    InstG famJ9A (J9A d hdk) XI where
  hsh := hsh
  σ := sigma9 XI
  hσinj := sigma9_inj hsh
  col := colI9
  loc := loc9I
  w := wOf9
  hcolT := tabΙ9_colI9
  hcolL := colI9_loc9I
  hlocW := loc9I_lt
  hlocC := loc9I_colI9
  hw := w_eq9 hsh
  nloc := sz9 d
  dec := finSigmaFinEquiv.symm
  hdec := fun _ => rfl
  rt := rt9 d
  hrtN := rt9_N d
  R := R
  hT := hT
  hσR := hσ
  hfree := hfree
  hr := rfl
  hd4 := rfl
  hoff := fun t k => by
    show omegaOf9 d t ^ (k : ℕ) = _
    rw [L.hom t]
    rfl
  hdom := hdom9 hsh L
  hdomt := hdomt9 hsh L
  hpdeg := hpdeg9 hsh L
  hpreN := fun t c hc hnot => by
    have hid := (ids_of_shapeF hsh).2 _ (Array.getElem_mem_toList t.2)
    refine preJ9_none (sigma9 XI t) c hc ?_
    show c ∉ (preIdx9 (idOf9 (tabIdx9 XI.tabs[t].chip.id))).toList
    rw [show idOf9 (tabIdx9 XI.tabs[t].chip.id) = XI.tabs[t].chip.id from idOf9_tabIdx9 _ hid]
    exact hnot
  hcolR := fun t c hc =>
    colR9_eq _ ((ids_of_shapeF hsh).2 _ (Array.getElem_mem_toList t.2)) c hc
  hcapι := by
    show (Fintype.card Ι9 + 165) * 2 + 9 ≤ 2 ^ 12
    rw [card_Ι9]; norm_num
  rdM := NockvmE2E.J9A.RVUJ9A.Mof9 XI.pubLay

end NockvmE2E.J9A.GenJ9A

#print axioms NockvmE2E.J9A.GenJ9A.sigma9_inj
#print axioms NockvmE2E.J9A.GenJ9A.hdomt9
#print axioms NockvmE2E.J9A.GenJ9A.hpdeg9
#print axioms NockvmE2E.J9A.GenJ9A.preJ9_none
#print axioms NockvmE2E.J9A.GenJ9A.colR9_eq
#print axioms NockvmE2E.J9A.GenJ9A.InstG.ofJ9A
#print axioms NockvmE2E.J9A.GenJ9A.nJ9A
