/-
part 4: the executed mask check over a chip family (`tabMaskF`, `maskOkF`, `numeralOkF`: `MaskOk.maskOk` / `numeralOk` with the
preprocessed-column positions read off `F.preIdx` instead of `preIdxJ8`) and the J-9 A Lagrange bridge `hLagr9_of` (twin of
`MaskBridge.hLagr_of`, eight tables, from `lagr9_*`): a passing check identifies every loaded fixed column with nock's `preJ9`
column.  The jet's registry columns stay TCB.
-/
import NockvmE2E.J9A.GenJ9A
import NockvmE2E.Exec.MaskBridge9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open Polynomial

namespace NockvmE2E.J9A.LagrJ9A

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.E2EGen NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
open NockvmE2E.Exec.MaskOk NockvmE2E.Exec.MaskBridge NockvmE2E.Exec.MaskBridge9
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.TieJ9A NockvmE2E.J9A.GenJ9A
open NockvmE2E.J8.InstJ8 (P Φ0 ω0)
open NockvmE2E.J8 (RapAirJ TabRestr)

/-! ## 1. the executed check over a family -/

/-- `tabMask` with the mask positions of the family `F` -/
def tabMaskF (F : Fam) (XX : ExecInst) (t : TabInst) : Option Nat :=
  if t.chip.id == "jetChipJ8" then some 0 else
  (F.preIdx t.chip.id).toList.zipIdx.foldl (fun acc (c, pos) =>
    match acc, maskCol XX t.hN pos (XX.pre.getD (t.col0 + c) #[]) with
    | some a, some k => some (max a k)
    | _, _ => none) (some 0)

def maskOkF (F : Fam) (XX : ExecInst) : Bool := XX.tabs.all fun t => (tabMaskF F XX t).isSome

def numeralOkF (F : Fam) (XX : ExecInst) : Bool := XX.tabs.all fun t =>
  if t.chip.id == "walkChipJ8" || t.chip.id == "walkChipHQK" then
    (chipNumeralF F t.chip).isSome && chipNumeralF F t.chip == tabMaskF F XX t
  else true

/-- the J-8 check is the family check at `famJ8` -/
theorem tabMaskF_famJ8 : tabMaskF famJ8 = tabMask := rfl
theorem maskOkF_famJ8 : maskOkF famJ8 = maskOk := rfl
theorem numeralOkF_famJ8 : numeralOkF famJ8 = numeralOk := rfl

theorem tabMaskF_eq (F : Fam) (XI : ExecInst) (t : TabInst) (hj : (t.chip.id == "jetChipJ8") = false) :
    tabMaskF F XI t = (F.preIdx t.chip.id).toList.zipIdx.foldl
      (stepF (fun x => maskCol XI t.hN x.2 (XI.pre.getD (t.col0 + x.1) #[]))) (some 0) := by
  unfold tabMaskF
  rw [hj]
  simp only [Bool.false_eq_true, ite_false]
  rfl

theorem tabMaskF_walk (XI : ExecInst) (t : TabInst) (hid : t.chip.id = "walkChipJ8" ∨ t.chip.id = "walkChipHQK") (r : ℕ)
    (h : tabMaskF famJ9A XI t = some r) :
    maskCol XI t.hN 2 (XI.pre.getD (t.col0 + 2) #[]) = some r := by
  have hj : (t.chip.id == "jetChipJ8") = false := by rcases hid with h | h <;> rw [h] <;> decide
  rw [tabMaskF_eq famJ9A XI t hj] at h
  have hl : (famJ9A.preIdx t.chip.id).toList.zipIdx = [(0, 0), (1, 1), (2, 2)] := by
    rcases hid with h | h <;> rw [h] <;> rfl
  rw [hl] at h
  simp only [List.foldl_cons, List.foldl_nil] at h
  cases h0 : maskCol XI t.hN 0 (XI.pre.getD (t.col0 + 0) #[]) with
  | none => simp only [stepF, h0, fold_none] at h; cases h
  | some k0 =>
  cases h1 : maskCol XI t.hN 1 (XI.pre.getD (t.col0 + 1) #[]) with
  | none => simp only [stepF, h0, h1, fold_none] at h; cases h
  | some k1 =>
  cases h2 : maskCol XI t.hN 2 (XI.pre.getD (t.col0 + 2) #[]) with
  | none => simp only [stepF, h0, h1, h2] at h; cases h
  | some k2 =>
    have e0 := maskCol_lt2 XI _ 0 _ (by omega) _ h0
    have e1 := maskCol_lt2 XI _ 1 _ (by omega) _ h1
    subst e0 e1
    simp only [stepF, h0, h1, h2, Nat.max_zero, Nat.zero_max, Option.some.injEq] at h
    rw [← h]

theorem numeral_of_okF (XI : ExecInst) (hn : numeralOkF famJ9A XI = true) (t : TabInst) (ht : t ∈ XI.tabs.toList)
    (hid : t.chip.id = "walkChipJ8" ∨ t.chip.id = "walkChipHQK") :
    (chipNumeralF famJ9A t.chip).isSome = true ∧ chipNumeralF famJ9A t.chip = tabMaskF famJ9A XI t := by
  unfold numeralOkF at hn
  have := (Array.all_eq_true_iff_forall_mem.mp hn) t (Array.mem_def.mpr ht)
  have hw : (t.chip.id == "walkChipJ8" || t.chip.id == "walkChipHQK") = true := by
    rcases hid with h | h <;> rw [h] <;> decide
  simp only [hw, ite_true, Bool.and_eq_true, beq_iff_eq] at this
  exact this

/-! ## 2. the bridge -/

/-- the conclusion of `hcur1` at one column, at the generic interface -/
def LagrAt9 {F : Fam} {J : RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC} {XI : ExecInst} (IG : InstG F J XI) (npub : ℕ)
    (tp : Fin IG.Jm.T) (hcap : IG.Cap npub) (t : Fin XI.tabs.size) (c : ℕ) : Prop :=
  (IG.JJ npub tp hcap).pre (colJG IG npub tp hcap t c) = some
    (((List.range XI.pre[XI.tabs[t].col0 + c]!.size).map fun m =>
      Polynomial.monomial m (zv (XI.pre[XI.tabs[t].col0 + c]!)[m]!)).sum)



section Bridge
variable {XI : ExecInst} (hsh : shapeOkF famJ9A XI = true) (d : Datum9A) (hdk : DatumOK9A d) (L : Link9 XI d)
  (R : TabRestr (J9A d hdk)) (hT : R.T' = XI.tabs.size)
  (hσ : ∀ t : Fin R.T', R.σ t = sigma9 XI (Fin.cast hT t)) (hfree : (J9A d hdk).AccOn R.q)
  (npub : ℕ) (tp : Fin (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree).Jm.T) (hcap : (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree).Cap npub)

/-- the numeral of a table of the datum -/
def numOf9 (d : Datum9A) (s : Fin 8) : ℕ :=
  if s = 2 then d.Pb.kroots else if s = 5 then d.Pb.krootsV else if s = 7 then d.Pb.nA else 0

theorem finish9 (t : Fin XI.tabs.size) (c pos n : ℕ) (nodes : Fin n → ZMod P) (hn0 : 0 < n) (kr k : ℕ)
    (hnodes : ∀ i, nodes i = zv XI.hGen ^ (i : ℕ)) (hnt : n = XI.tabs[t].hN)
    (hmc : maskCol XI XI.tabs[t].hN pos (XI.pre.getD (XI.tabs[t].col0 + c) #[]) = some k) (hk : 2 ≤ pos → kr = k)
    (hpre : preJ9 d (colI9 (sigma9 XI t) c) = some (Msk pos nodes hn0 kr)) :
    LagrAt9 (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree) npub tp hcap t c := by
  have hle : XI.tabs[t].hN ≤ XI.hN := hle_of_shapeF hsh _ (Array.getElem_mem_toList t.2)
  have h1 : (J9A d hdk).pre (colI9 (sigma9 XI t) c) = preJ9 d (colI9 (sigma9 XI t) c) := rfl
  unfold LagrAt9
  show (J9A d hdk).pre (colI9 (sigma9 XI t) c) = _
  rw [h1, hpre, ← polyOfArr_sum]
  congr 1
  exact (polyOfArr_Msk9 XI n (inj_pows9 hsh ((le_of_eq hnt).trans hle)) _ (hpreC_of_shapeF hsh _) pos nodes hn0 hnodes kr k
    (by rw [hnt, pre_getD]; exact hmc) hk).symm

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
theorem hLagr9_of (hmask : maskOkF famJ9A XI = true) (hnum : numeralOkF famJ9A XI = true)
    (hnum0 : ∀ t : Fin XI.tabs.size, (chipNumeralF famJ9A XI.tabs[t].chip).getD 0 = numOf9 d (sigma9 XI t))
    (hjet : ∀ t : Fin XI.tabs.size, XI.tabs[t].chip.id = "jetChipJ8" → ∀ c, c < XI.tabs[t].nc - XI.tabs[t].npub →
      XI.colKind[XI.tabs[t].col0 + c]! = 1 → LagrAt9 (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree) npub tp hcap t c) :
    ∀ (t : Fin XI.tabs.size) c, c < XI.tabs[t].nc - XI.tabs[t].npub → XI.colKind[XI.tabs[t].col0 + c]! = 1 →
      LagrAt9 (InstG.ofJ9A XI hsh d hdk L R hT hσ hfree) npub tp hcap t c := by
  intro t c hc hk
  have hm : XI.tabs[t] ∈ XI.tabs.toList := Array.getElem_mem_toList t.2
  obtain ⟨-, hmem⟩ := ids_of_shapeF hsh
  have hid8 : XI.tabs[t].chip.id ∈ idsJ9A := hmem _ hm
  by_cases hjt : XI.tabs[t].chip.id = "jetChipJ8"
  · exact hjet t hjt c hc hk
  -- the position of `c` among the mask columns
  have hpk : ((XI.colKind[XI.tabs[t].col0 + c]! == 1) == (famJ9A.preIdx XI.tabs[t].chip.id).contains c) = true := by
    have hpk0 := preKindOk_of_shapeF hsh
    unfold preKindOkF at hpk0
    have := (Array.all_eq_true_iff_forall_mem.mp hpk0) XI.tabs[t] (Array.mem_def.mpr hm)
    simp only [List.all_eq_true, List.mem_range] at this
    exact this c hc
  rw [hk] at hpk
  have hcont : (famJ9A.preIdx XI.tabs[t].chip.id).contains c = true := by simpa using hpk
  obtain ⟨pos, hpos⟩ := exists_pos_of_contains _ c
    (List.contains_iff_mem.mpr (Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp hcont)))
  have hj' : (XI.tabs[t].chip.id == "jetChipJ8") = false := by simpa using hjt
  have hsome : (tabMaskF famJ9A XI XI.tabs[t]).isSome = true := by
    unfold maskOkF at hmask
    exact (Array.all_eq_true_iff_forall_mem.mp hmask) _ (Array.mem_def.mpr hm)
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨k, hmc⟩ := fold_some _ _ 0 r (by rw [← tabMaskF_eq famJ9A XI XI.tabs[t] hj']; exact hr) (c, pos) hpos
  have hn_tab := L.n_tab t
  have hsd : sigma9 XI t = tabIdx9 XI.tabs[t].chip.id := rfl
  simp only [idsJ9A, List.mem_cons, List.not_mem_nil, or_false] at hid8
  rcases hid8 with hid | hid | hid | hid | hid | hid | hid | hid
  · -- compute9
    have hs : sigma9 XI t = 0 := by rw [hsd, hid]; rfl
    rw [hid] at hpos
    have hp2 : pos < 2 := by
      have : (preIdx9 "computeChipVCLHX9").toList.zipIdx = [(17, 0), (18, 1)] := by rw [preIdx9_compute]; rfl
      simp only [famJ9A, this] at hpos; simp at hpos; omega
    refine finish9 hsh d hdk L R hT hσ hfree npub tp hcap t c pos d.Pb.n d.Pb.nodes d.Pb.hn 0 k L.nodes0 ?_ hmc
      (fun h => absurd h (by omega)) ?_
    · rw [← hn_tab, hs]; rfl
    · rw [hs]; exact preJ9_s0 d c pos hpos
  · -- cell
    have hs : sigma9 XI t = 1 := by rw [hsd, hid]; rfl
    rw [hid] at hpos
    have hp2 : pos < 2 := by simp [famJ9A, preIdx9, J8Shape.preIdxJ8] at hpos; omega
    refine finish9 hsh d hdk L R hT hσ hfree npub tp hcap t c pos d.Pb.nC d.Pb.nodesC d.Pb.hnC 0 k L.nodesC ?_ hmc
      (fun h => absurd h (by omega)) ?_
    · rw [← hn_tab, hs]; rfl
    · rw [hs]; exact preJ9_s1 d c pos hpos
  · -- walkJ8
    have hs : sigma9 XI t = 2 := by rw [hsd, hid]; rfl
    have hnumt := numeral_of_okF XI hnum _ hm (Or.inl hid)
    have hroot := tabMaskF_walk XI _ (Or.inl hid) r hr
    rw [hid] at hpos
    refine finish9 hsh d hdk L R hT hσ hfree npub tp hcap t c pos d.Pb.nW d.Pb.nodesW d.Pb.hnW d.Pb.kroots k L.nodesW ?_ hmc ?_ ?_
    · rw [← hn_tab, hs]; rfl
    · intro h2
      have hpc : c = 2 ∧ pos = 2 := by simp [famJ9A, preIdx9, J8Shape.preIdxJ8] at hpos; omega
      obtain ⟨rfl, rfl⟩ := hpc
      have hkr : k = r := Option.some.inj (hmc.symm.trans hroot)
      have h0 := hnum0 t
      rw [hs, hnumt.2.trans hr] at h0
      simp [numOf9] at h0
      omega
    · rw [hs]; exact preJ9_s2 d c pos hpos
  · -- atom
    have hs : sigma9 XI t = 4 := by rw [hsd, hid]; rfl
    rw [hid] at hpos
    have hp2 : pos < 2 := by simp [famJ9A, preIdx9, J8Shape.preIdxJ8] at hpos; omega
    refine finish9 hsh d hdk L R hT hσ hfree npub tp hcap t c pos d.Pb.nA d.Pb.nodesA d.Pb.hnA 0 k L.nodesA ?_ hmc
      (fun h => absurd h (by omega)) ?_
    · rw [← hn_tab, hs]; rfl
    · rw [hs]; exact preJ9_s4 d c pos hpos
  · -- walkHQK
    have hs : sigma9 XI t = 5 := by rw [hsd, hid]; rfl
    have hnumt := numeral_of_okF XI hnum _ hm (Or.inr hid)
    have hroot := tabMaskF_walk XI _ (Or.inr hid) r hr
    rw [hid] at hpos
    refine finish9 hsh d hdk L R hT hσ hfree npub tp hcap t c pos d.Pb.nV d.Pb.nodesV d.Pb.hnV d.Pb.krootsV k L.nodesV ?_ hmc ?_ ?_
    · rw [← hn_tab, hs]; rfl
    · intro h2
      have hpc : c = 2 ∧ pos = 2 := by simp [famJ9A, preIdx9, J8Shape.preIdxJ8] at hpos; omega
      obtain ⟨rfl, rfl⟩ := hpc
      have hkr : k = r := Option.some.inj (hmc.symm.trans hroot)
      have h0 := hnum0 t
      rw [hs, hnumt.2.trans hr] at h0
      simp [numOf9] at h0
      omega
    · rw [hs]; exact preJ9_s5 d c pos hpos
  · exact absurd hid hjt
  · -- axis
    have hs : sigma9 XI t = 6 := by rw [hsd, hid]; rfl
    rw [hid] at hpos
    have hp2 : pos < 2 := by
      have : (preIdx9 "axisChipJ9").toList.zipIdx = [(0, 0), (1, 1)] := by rw [preIdx9_axis]; rfl
      simp only [famJ9A, this] at hpos; simp at hpos; omega
    refine finish9 hsh d hdk L R hT hσ hfree npub tp hcap t c pos d.Pb.nX d.Pb.nodesX d.Pb.hnX 0 k L.nodesX ?_ hmc
      (fun h => absurd h (by omega)) ?_
    · rw [← hn_tab, hs]; rfl
    · rw [hs]; exact preJ9_s6 d c pos hpos
  · -- split
    have hs : sigma9 XI t = 7 := by rw [hsd, hid]; rfl
    rw [hid] at hpos
    have hp2 : pos < 2 := by
      have : (preIdx9 "splitChipJ9").toList.zipIdx = [(0, 0), (1, 1)] := by rw [preIdx9_split]; rfl
      simp only [famJ9A, this] at hpos; simp at hpos; omega
    refine finish9 hsh d hdk L R hT hσ hfree npub tp hcap t c pos d.Pb.nS d.Pb.nodesS d.Pb.hnS 0 k L.nodesS ?_ hmc
      (fun h => absurd h (by omega)) ?_
    · rw [← hn_tab, hs]; rfl
    · rw [hs]; exact preJ9_s7 d c pos hpos

end Bridge

end NockvmE2E.J9A.LagrJ9A

#print axioms NockvmE2E.J9A.LagrJ9A.tabMaskF_walk
#print axioms NockvmE2E.J9A.LagrJ9A.finish9
#print axioms NockvmE2E.J9A.LagrJ9A.hLagr9_of
