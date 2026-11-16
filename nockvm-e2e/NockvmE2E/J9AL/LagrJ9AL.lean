/-
`LagrJ9AL`.  §1: `numOf9L` and `PreLLink`.
§2: the J-9 AL Lagrange bridge `hLagr9L_of` (twin of `LagrJ9A.hLagr9_of`, nine tables): the eight old tables as at J-9 A (at `sigma9L` / `preJ9L`, from
`preJ9_s*`), the ALU's columns 0/1 through the mask check `maskOkFL`'s `take 2` and its columns 2..4 through `PreLLink`.
Not zero-knowledge.
-/
import NockvmE2E.J9AL.GenJ9AL
import NockvmE2E.J9A.LagrJ9A
import NockvmE2E.J9A.RunGate9L
import NockvmE2E.Exec.MaskOkK
import NockvmE2E.Exec.MaskBridge9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

open Polynomial

namespace NockvmE2E.J9AL.LagrJ9AL

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.E2EGen NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
open NockvmE2E.Exec.MaskOk NockvmE2E.Exec.MaskBridge NockvmE2E.Exec.MaskBridge9 NockvmE2E.Exec.J9ALChips
open NockvmE2E.Exec.MaskOkK (polyOfArr)
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.TieJ9A NockvmE2E.J9A.GenJ9A NockvmE2E.J9A.LagrJ9A NockvmE2E.J9A.RunGate9L
open NockvmE2E.J9AL.InstJ9AL NockvmE2E.J9AL.TieJ9AL NockvmE2E.J9AL.GenJ9AL
open NockvmE2E.J8.InstJ8 (P Φ0 ω0)
open NockvmE2E.J8 (RapAirJ TabRestr)
open Nock.NockVMROM.Thm54.VclL.Handle

/-! ## 1. interface freeze -/

/-- the numeral of a table of the J-9 AL datum (the ALU table, index 8, has none) -/
def numOf9L (d : Datum9AL) (s : Fin 9) : ℕ :=
  if h : s.val < 8 then NockvmE2E.J9A.LagrJ9A.numOf9 d.toA ⟨s.val, h⟩ else 0

/-- the datum's ALU preprocessed columns are the loaded ones (`pre[col0+2+k]`) -/
def PreLLink (XI : ExecInst) (d : Datum9AL) : Prop :=
  ∀ t : Fin XI.tabs.size, XI.tabs[t].chip.id = "aluChipJ9" → ∀ k : Fin 3,
    d.Pb.preL k = polyOfArr (XI.pre[XI.tabs[t].col0 + 2 + (k : ℕ)]!)

theorem numOf9L_castSucc (d : Datum9AL) (s : Fin 8) : numOf9L d s.castSucc = numOf9 d.toA s := by
  unfold numOf9L
  rw [dif_pos (by simp)]
  rfl

/-! ## 2. the bridge -/

theorem numeral_of_okFL (XI : ExecInst) (hn : numeralOkF famJ9AL XI = true) (t : TabInst) (ht : t ∈ XI.tabs.toList)
    (hid : t.chip.id = "walkChipJ8" ∨ t.chip.id = "walkChipHQK") :
    (chipNumeralF famJ9AL t.chip).isSome = true ∧ chipNumeralF famJ9AL t.chip = tabMaskF famJ9AL XI t := by
  unfold numeralOkF at hn
  have := (Array.all_eq_true_iff_forall_mem.mp hn) t (Array.mem_def.mpr ht)
  have hw : (t.chip.id == "walkChipJ8" || t.chip.id == "walkChipHQK") = true := by
    rcases hid with h | h <;> rw [h] <;> decide
  simp only [hw, ite_true, Bool.and_eq_true, beq_iff_eq] at this
  exact this

/-- off the ALU, the family checks of `famJ9AL` are those of `famJ9A` -/
theorem tabMaskF_AL (XI : ExecInst) (t : TabInst) (h : t.chip.id ≠ "aluChipJ9") :
    tabMaskF famJ9AL XI t = tabMaskF famJ9A XI t := by
  unfold tabMaskF; rw [(famJ9AL_j9a _ h).2.1]

theorem chipNumeralF_AL (c : NockvmE2E.Exec.Tr.Chip) (h : c.id ≠ "aluChipJ9") :
    chipNumeralF famJ9AL c = chipNumeralF famJ9A c := by
  unfold chipNumeralF expectedOfF; rw [(famJ9AL_j9a _ h).2.2.2.2]

theorem tabMaskFL_AL (XI : ExecInst) (t : TabInst) (h : t.chip.id ≠ "aluChipJ9") :
    tabMaskFL famJ9AL XI t = tabMaskF famJ9A XI t := by
  have h' : (t.chip.id == "aluChipJ9") = false := by simpa using h
  unfold tabMaskFL; rw [h', if_neg (by simp), tabMaskF_AL XI t h]

/-- `numeral_of_okFL`, at the family `famJ9A` off the ALU -/
theorem numeral_of_okFL' (XI : ExecInst) (hn : numeralOkF famJ9AL XI = true) (t : TabInst) (ht : t ∈ XI.tabs.toList)
    (hid : t.chip.id = "walkChipJ8" ∨ t.chip.id = "walkChipHQK") :
    (chipNumeralF famJ9A t.chip).isSome = true ∧ chipNumeralF famJ9A t.chip = tabMaskF famJ9A XI t := by
  have hne : t.chip.id ≠ "aluChipJ9" := by rcases hid with h | h <;> rw [h] <;> decide
  have := numeral_of_okFL XI hn t ht hid
  rwa [chipNumeralF_AL _ hne, tabMaskF_AL _ _ hne] at this

section Bridge
variable {XI : ExecInst} (hsh : shapeOkF famJ9AL XI = true) (d : Datum9AL) (hdk : DatumOK9AL d) (L : Link9L XI d)
  (R : TabRestr (J9AL d hdk)) (hT : R.T' = XI.tabs.size)
  (hσ : ∀ t : Fin R.T', R.σ t = sigma9L XI (Fin.cast hT t)) (hfree : (J9AL d hdk).AccOn R.q)
  (npub : ℕ) (tp : Fin (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree).Jm.T) (hcap : (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree).Cap npub)

theorem finish9L (t : Fin XI.tabs.size) (c pos n : ℕ) (nodes : Fin n → ZMod P) (hn0 : 0 < n) (kr k : ℕ)
    (hnodes : ∀ i, nodes i = zv XI.hGen ^ (i : ℕ)) (hnt : n = XI.tabs[t].hN)
    (hmc : maskCol XI XI.tabs[t].hN pos (XI.pre.getD (XI.tabs[t].col0 + c) #[]) = some k) (hk : 2 ≤ pos → kr = k)
    (hpre : preJ9L d (colI9L (sigma9L XI t) c) = some (Msk pos nodes hn0 kr)) :
    LagrAt9 (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree) npub tp hcap t c := by
  have hle : XI.tabs[t].hN ≤ XI.hN := hle_of_shapeF hsh _ (Array.getElem_mem_toList t.2)
  have h1 : (J9AL d hdk).pre (colI9L (sigma9L XI t) c) = preJ9L d (colI9L (sigma9L XI t) c) := rfl
  unfold LagrAt9
  show (J9AL d hdk).pre (colI9L (sigma9L XI t) c) = _
  rw [h1, hpre, ← polyOfArr_sum]
  congr 1
  exact (polyOfArr_Msk9 XI n (inj_pows9L hsh ((le_of_eq hnt).trans hle)) _ (hpreC_of_shapeF hsh _) pos nodes hn0 hnodes kr k
    (by rw [hnt, pre_getD]; exact hmc) hk).symm

/-- the ALU's fixed columns, as `preOf` of the ALU chip -/
theorem preJ9L_alu (c : ℕ) (hc : c < 5) :
    preJ9L d (colI9L 8 c) = some (AluSZChipJ9.preOf d.Pb.hnL d.Pb.nodesL d.Pb.preL ⟨c, hc⟩) := by
  show NockvmE2E.J8.InstJ8.preOf _ _ = _
  rw [NockvmE2E.Exec.MaskBridge.preOf_of_idx _ _ ⟨c, hc⟩ (by show c = c % 196; exact (Nat.mod_eq_of_lt (by omega)).symm)]
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
theorem hLagr9L_of (hmask : maskOkFL famJ9AL XI = true) (hnum : numeralOkF famJ9AL XI = true) (hpreL : PreLLink XI d)
    (hnum0 : ∀ t : Fin XI.tabs.size, (chipNumeralF famJ9AL XI.tabs[t].chip).getD 0 = numOf9L d (sigma9L XI t))
    (hjet : ∀ t : Fin XI.tabs.size, XI.tabs[t].chip.id = "jetChipJ8" → ∀ c, c < XI.tabs[t].nc - XI.tabs[t].npub →
      XI.colKind[XI.tabs[t].col0 + c]! = 1 → LagrAt9 (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree) npub tp hcap t c) :
    ∀ (t : Fin XI.tabs.size) c, c < XI.tabs[t].nc - XI.tabs[t].npub → XI.colKind[XI.tabs[t].col0 + c]! = 1 →
      LagrAt9 (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree) npub tp hcap t c := by
  intro t c hc hk
  have hm : XI.tabs[t] ∈ XI.tabs.toList := Array.getElem_mem_toList t.2
  obtain ⟨-, hmem⟩ := ids_of_shapeF hsh
  have hid8 : XI.tabs[t].chip.id ∈ idsJ9AL := hmem _ hm
  have hsd : sigma9L XI t = tabIdx9L XI.tabs[t].chip.id := rfl
  have hn_tab := L.n_tab t
  -- the position of `c` among the mask columns
  have hpk : ((XI.colKind[XI.tabs[t].col0 + c]! == 1) == (famJ9AL.preIdx XI.tabs[t].chip.id).contains c) = true := by
    have hpk0 := preKindOk_of_shapeF hsh
    unfold preKindOkF at hpk0
    have := (Array.all_eq_true_iff_forall_mem.mp hpk0) XI.tabs[t] (Array.mem_def.mpr hm)
    simp only [List.all_eq_true, List.mem_range] at this
    exact this c hc
  rw [hk] at hpk
  have hcont : (famJ9AL.preIdx XI.tabs[t].chip.id).contains c = true := by simpa using hpk
  obtain ⟨pos, hpos⟩ := exists_pos_of_contains _ c
    (List.contains_iff_mem.mpr (Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp hcont)))
  have hsome : (tabMaskFL famJ9AL XI XI.tabs[t]).isSome = true := by
    unfold maskOkFL at hmask
    exact (Array.all_eq_true_iff_forall_mem.mp hmask) _ (Array.mem_def.mpr hm)
  by_cases halu : XI.tabs[t].chip.id = "aluChipJ9"
  · -- the ALU
    have hs : sigma9L XI t = 8 := by rw [hsd, halu]; rfl
    have hpos' : (c, pos) ∈ (famJ9AL.preIdx "aluChipJ9").toList.zipIdx := by rw [← halu]; exact hpos
    have hpl : (famJ9AL.preIdx "aluChipJ9").toList.zipIdx = [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4)] := by decide
    rw [hpl] at hpos'
    have hcp : c = pos ∧ c < 5 := by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hpos'
      omega
    obtain ⟨rfl, hc5⟩ := hcp
    have hnL : d.Pb.nL = XI.tabs[t].hN := by rw [← hn_tab, hs]; rfl
    by_cases h2 : c < 2
    · -- a mask column
      have hfold : tabMaskFL famJ9AL XI XI.tabs[t] = [(0, 0), (1, 1)].foldl
          (stepF (fun x => maskCol XI XI.tabs[t].hN x.2 (XI.pre.getD (XI.tabs[t].col0 + x.1) #[]))) (some 0) := by
        have h' : (XI.tabs[t].chip.id == "aluChipJ9") = true := by simpa using halu
        unfold tabMaskFL; rw [h', if_pos rfl]
        have : ((famJ9AL.preIdx XI.tabs[t].chip.id).toList.take 2).zipIdx = [(0, 0), (1, 1)] := by rw [halu]; decide
        rw [this]; rfl
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨k, hmc⟩ := fold_some _ _ 0 r (by rw [← hfold]; exact hr) (c, c) (by
        simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]; omega)
      refine finish9L hsh d hdk L R hT hσ hfree npub tp hcap t c c d.Pb.nL d.Pb.nodesL d.Pb.hnL 0 k L.nodesL hnL hmc
        (fun h => absurd h (by omega)) ?_
      rw [hs, preJ9L_alu d c hc5]
      rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> simp [AluSZChipJ9.preOf, Msk]
    · -- the preg columns
      have h1 : (J9AL d hdk).pre (colI9L (sigma9L XI t) c) = preJ9L d (colI9L (sigma9L XI t) c) := rfl
      unfold LagrAt9
      show (J9AL d hdk).pre (colI9L (sigma9L XI t) c) = _
      rw [h1, hs, preJ9L_alu d c hc5]
      have e1 : AluSZChipJ9.preOf d.Pb.hnL d.Pb.nodesL d.Pb.preL ⟨c, hc5⟩ = d.Pb.preL ⟨c - 2, by omega⟩ := by
        simp only [AluSZChipJ9.preOf]
        rw [dif_neg (show ¬ ((⟨c, hc5⟩ : Fin 5) : ℕ) = 0 by simp only [Fin.val_mk]; omega),
          dif_neg (show ¬ ((⟨c, hc5⟩ : Fin 5) : ℕ) = 1 by simp only [Fin.val_mk]; omega)]
      rw [e1, hpreL t halu ⟨c - 2, by omega⟩, ← polyOfArr_sum]
      have e2 : XI.tabs[t].col0 + 2 + (c - 2) = XI.tabs[t].col0 + c := by omega
      rw [e2]
      rfl
  · have hmem' : XI.tabs[t].chip.id ∈ idsJ9A := by
      simp only [idsJ9AL, List.mem_append, List.mem_singleton] at hid8
      exact hid8.resolve_right halu
    have hne := halu
    have eN : chipNumeralF famJ9AL XI.tabs[t].chip = chipNumeralF famJ9A XI.tabs[t].chip := chipNumeralF_AL _ hne
    have hpos : (c, pos) ∈ (famJ9A.preIdx XI.tabs[t].chip.id).toList.zipIdx := by
      rw [← (famJ9AL_j9a _ hne).2.1]; exact hpos
    by_cases hjt : XI.tabs[t].chip.id = "jetChipJ8"
    · exact hjet t hjt c hc hk
    have hj' : (XI.tabs[t].chip.id == "jetChipJ8") = false := by simpa using hjt
    have hsome9 : (tabMaskF famJ9A XI XI.tabs[t]).isSome = true := by rw [← tabMaskFL_AL XI _ hne]; exact hsome
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome9
    obtain ⟨k, hmc⟩ := fold_some _ _ 0 r (by rw [← tabMaskF_eq famJ9A XI XI.tabs[t] hj']; exact hr) (c, pos) hpos
    simp only [idsJ9A, List.mem_cons, List.not_mem_nil, or_false] at hmem'
    rcases hmem' with hid | hid | hid | hid | hid | hid | hid | hid
    · -- compute9
      have hs : sigma9L XI t = 0 := by rw [hsd, hid]; rfl
      rw [hid] at hpos
      have hp2 : pos < 2 := by
        have : (preIdx9 "computeChipVCLHX9").toList.zipIdx = [(17, 0), (18, 1)] := by rw [preIdx9_compute]; rfl
        simp only [famJ9A, this] at hpos; simp at hpos; omega
      refine finish9L hsh d hdk L R hT hσ hfree npub tp hcap t c pos d.Pb.n d.Pb.nodes d.Pb.hn 0 k L.nodes0 ?_ hmc
        (fun h => absurd h (by omega)) ?_
      · rw [← hn_tab, hs]; rfl
      · rw [hs]; exact preJ9_s0 d.toA c pos hpos
    · -- cell
      have hs : sigma9L XI t = 1 := by rw [hsd, hid]; rfl
      rw [hid] at hpos
      have hp2 : pos < 2 := by simp [famJ9A, preIdx9, J8Shape.preIdxJ8] at hpos; omega
      refine finish9L hsh d hdk L R hT hσ hfree npub tp hcap t c pos d.Pb.nC d.Pb.nodesC d.Pb.hnC 0 k L.nodesC ?_ hmc
        (fun h => absurd h (by omega)) ?_
      · rw [← hn_tab, hs]; rfl
      · rw [hs]; exact preJ9_s1 d.toA c pos hpos
    · -- walkJ8
      have hs : sigma9L XI t = 2 := by rw [hsd, hid]; rfl
      have hnumt := numeral_of_okFL' XI hnum _ hm (Or.inl hid)
      have hroot := tabMaskF_walk XI _ (Or.inl hid) r hr
      rw [hid] at hpos
      refine finish9L hsh d hdk L R hT hσ hfree npub tp hcap t c pos d.Pb.nW d.Pb.nodesW d.Pb.hnW d.Pb.kroots k L.nodesW ?_ hmc ?_ ?_
      · rw [← hn_tab, hs]; rfl
      · intro h2
        have hpc : c = 2 ∧ pos = 2 := by simp [famJ9A, preIdx9, J8Shape.preIdxJ8] at hpos; omega
        obtain ⟨rfl, rfl⟩ := hpc
        have hkr : k = r := Option.some.inj (hmc.symm.trans hroot)
        have h0 := hnum0 t
        rw [eN] at h0
        rw [hs, hnumt.2.trans hr] at h0
        simp [numOf9L, numOf9] at h0
        have e1 : d.toA.Pb.kroots = d.Pb.kroots := rfl
        have e2 : d.toA.Pb.krootsV = d.Pb.krootsV := rfl
        omega
      · rw [hs]; exact preJ9_s2 d.toA c pos hpos
    · -- atom
      have hs : sigma9L XI t = 4 := by rw [hsd, hid]; rfl
      rw [hid] at hpos
      have hp2 : pos < 2 := by simp [famJ9A, preIdx9, J8Shape.preIdxJ8] at hpos; omega
      refine finish9L hsh d hdk L R hT hσ hfree npub tp hcap t c pos d.Pb.nA d.Pb.nodesA d.Pb.hnA 0 k L.nodesA ?_ hmc
        (fun h => absurd h (by omega)) ?_
      · rw [← hn_tab, hs]; rfl
      · rw [hs]; exact preJ9_s4 d.toA c pos hpos
    · -- walkHQK
      have hs : sigma9L XI t = 5 := by rw [hsd, hid]; rfl
      have hnumt := numeral_of_okFL' XI hnum _ hm (Or.inr hid)
      have hroot := tabMaskF_walk XI _ (Or.inr hid) r hr
      rw [hid] at hpos
      refine finish9L hsh d hdk L R hT hσ hfree npub tp hcap t c pos d.Pb.nV d.Pb.nodesV d.Pb.hnV d.Pb.krootsV k L.nodesV ?_ hmc ?_ ?_
      · rw [← hn_tab, hs]; rfl
      · intro h2
        have hpc : c = 2 ∧ pos = 2 := by simp [famJ9A, preIdx9, J8Shape.preIdxJ8] at hpos; omega
        obtain ⟨rfl, rfl⟩ := hpc
        have hkr : k = r := Option.some.inj (hmc.symm.trans hroot)
        have h0 := hnum0 t
        rw [eN] at h0
        rw [hs, hnumt.2.trans hr] at h0
        simp [numOf9L, numOf9] at h0
        have e1 : d.toA.Pb.kroots = d.Pb.kroots := rfl
        have e2 : d.toA.Pb.krootsV = d.Pb.krootsV := rfl
        omega
      · rw [hs]; exact preJ9_s5 d.toA c pos hpos
    · exact absurd hid hjt
    · -- axis
      have hs : sigma9L XI t = 6 := by rw [hsd, hid]; rfl
      rw [hid] at hpos
      have hp2 : pos < 2 := by
        have : (preIdx9 "axisChipJ9").toList.zipIdx = [(0, 0), (1, 1)] := by rw [preIdx9_axis]; rfl
        simp only [famJ9A, this] at hpos; simp at hpos; omega
      refine finish9L hsh d hdk L R hT hσ hfree npub tp hcap t c pos d.Pb.nX d.Pb.nodesX d.Pb.hnX 0 k L.nodesX ?_ hmc
        (fun h => absurd h (by omega)) ?_
      · rw [← hn_tab, hs]; rfl
      · rw [hs]; exact preJ9_s6 d.toA c pos hpos
    · -- split
      have hs : sigma9L XI t = 7 := by rw [hsd, hid]; rfl
      rw [hid] at hpos
      have hp2 : pos < 2 := by
        have : (preIdx9 "splitChipJ9").toList.zipIdx = [(0, 0), (1, 1)] := by rw [preIdx9_split]; rfl
        simp only [famJ9A, this] at hpos; simp at hpos; omega
      refine finish9L hsh d hdk L R hT hσ hfree npub tp hcap t c pos d.Pb.nS d.Pb.nodesS d.Pb.hnS 0 k L.nodesS ?_ hmc
        (fun h => absurd h (by omega)) ?_
      · rw [← hn_tab, hs]; rfl
      · rw [hs]; exact preJ9_s7 d.toA c pos hpos

end Bridge

end NockvmE2E.J9AL.LagrJ9AL

#print axioms NockvmE2E.J9AL.LagrJ9AL.numOf9L_castSucc
#print axioms NockvmE2E.J9AL.LagrJ9AL.finish9L
#print axioms NockvmE2E.J9AL.LagrJ9AL.preJ9L_alu
#print axioms NockvmE2E.J9AL.LagrJ9AL.hLagr9L_of
