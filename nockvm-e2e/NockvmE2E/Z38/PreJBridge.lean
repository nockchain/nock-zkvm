/-
  NockvmE2E/Z38/PreJBridge.lean

  `preJLink_of_jetPreOkF`: the executable check `jetPreOkF` gives `PreJLink XI d` (the datum's 18 J fixed columns are the loaded ones).
  Twin of `pregCol_of_pregOkF` / `pregOK_of_pregOkF` (PregJ9AL).  Not zero-knowledge.
-/
import NockvmE2E.Z38.IfaceJ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

open Polynomial

namespace NockvmE2E.Z38.PreJBridge

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.ShapeF NockvmE2E.Exec.MaskOkK NockvmE2E.Exec.MaskBridge NockvmE2E.Exec.MaskBridge9
open NockvmE2E.Exec.MaskOk
open NockvmE2E.Exec.VF (G)
open NockvmE2E.Exec.J8Shape (tabs_all_mem)
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.GenJ9A NockvmE2E.J9A.PbOfX9
open NockvmE2E.J9AL.InstJ9AL NockvmE2E.J9AL.GenJ9AL NockvmE2E.J9AL.PregJ9AL
open NockvmE2E.J9AL.DatX9LOk (P_eq_PN)
open NockvmE2E.Exec.J9ALChips (famJ9AL)
open NockvmE2E.J8.InstJ8 (P tabOf hNof ω0)
open NockvmE2E.Z38.JetPre NockvmE2E.Z38.IfaceJ
open Nock.Jet.ChipJ8 (PRow)

/-- `preColG` is nock's `preCol` on small rows -/
theorem preColG_zv (q : PRow) (c : ℕ) (hc : c < 18) (h11 : c ≠ 11) (h12 : c ≠ 12)
    (hs : q.id < P ∧ q.cid < P ∧ q.nid < P ∧ q.n1 < P ∧ q.n2 < P) :
    zv (preColG q c) = (Nock.Jet.ChipJ8.preCol q c : ZMod P) := by
  have hPN := P_eq_PN
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  by_cases hl : c < 11
  · unfold preColG Nock.Jet.ChipJ8.preCol
    rw [if_pos hl, if_pos hl]
    by_cases hq : q.kd.sel = c
    · rw [if_pos hq, if_pos hq]; exact zv_one
    · rw [if_neg hq, if_neg hq]; exact zv_zero
  · have : c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 ∨ c = 17 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · simp [preColG, Nock.Jet.ChipJ8.preCol, zv_ofNat_lt _ (hPN ▸ h1)]
      rfl
    · simp [preColG, Nock.Jet.ChipJ8.preCol, zv_ofNat_lt _ (hPN ▸ h2)]
      rfl
    · simp [preColG, Nock.Jet.ChipJ8.preCol, zv_ofNat_lt _ (hPN ▸ h3)]
      rfl
    · simp [preColG, Nock.Jet.ChipJ8.preCol, zv_ofNat_lt _ (hPN ▸ h4)]
      rfl
    · simp [preColG, Nock.Jet.ChipJ8.preCol, zv_ofNat_lt _ (hPN ▸ h5)]
      rfl

/-- the list-to-array form of the layout column is the `Array.range` form of `eval_of_pat'` -/
theorem toArray_range (l : List G) (n : ℕ) (hn : l.length = n) :
    l.toArray = (Array.range n).map (fun i => l.getD i 0) := by
  apply Array.ext
  · simp [hn]
  · intro i h1 h2
    simp only [List.size_toArray] at h1
    simp [List.getD_eq_getElem _ _ h1, List.getElem?_eq_getElem h1]

theorem preJLink_of_jetPreOkF (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (hjp : jetPreOkF XI = true)
    (d : Datum9AL) (L : Link9L XI d) (hlay : List.ofFn d.Pb.lay = layJ XI.pubIn)
    (hsm : ∀ q ∈ layJ XI.pubIn, q.id < P ∧ q.cid < P ∧ q.nid < P ∧ q.n1 < P ∧ q.n2 < P) : PreJLink XI d := by
  intro t hid c hc
  have hm : XI.tabs[t] ∈ XI.tabs.toList := Array.getElem_mem_toList t.2
  have hall := tabs_all_mem (XI := XI) (by unfold jetPreOkF at hjp; exact hjp) _ hm
  simp only [hid, beq_self_eq_true, ite_true, Bool.and_eq_true, decide_eq_true_eq] at hall
  obtain ⟨⟨hlen, hmasks⟩, hcols⟩ := hall
  unfold jetLayLenOk at hlen
  simp only [decide_eq_true_eq] at hlen
  have hs : sigma9L XI t = 3 := by
    have hsd : sigma9L XI t = NockvmE2E.J9AL.GenJ9AL.tabIdx9L XI.tabs[t].chip.id := rfl
    rw [hsd, hid]; rfl
  have hn : d.Pb.nJ = XI.tabs[t].hN := by
    have := L.n_tab t
    rw [hs] at this
    exact this
  have hle : XI.tabs[t].hN ≤ XI.hN := hle_of_shapeF h _ hm
  have hn0 : 0 < d.Pb.nJ := by
    rw [hn]; exact hN_pos_of_shapeF h _ hm
  have hinj : Function.Injective (fun i : Fin d.Pb.nJ => zv XI.hGen ^ (i : ℕ)) := inj_pows9L h (hn ▸ hle)
  have hgd : ∀ j, XI.pre.getD (XI.tabs[t].col0 + j) #[] = XI.pre[XI.tabs[t].col0 + j]! := fun j => (pre_getD _ _).symm
  by_cases h11 : c = 11
  · subst h11
    unfold jetMasksOk at hmasks
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hmasks
    obtain ⟨⟨k, hk⟩, -⟩ := hmasks
    have := polyOfArr_Msk9 XI d.Pb.nJ hinj (XI.pre[XI.tabs[t].col0 + 11]!) (hpreC_of_shapeF h _) 0 d.Pb.nodesJ hn0 L.nodesJ 0 k
      (by rw [hn, pre_getD]; exact hk) (fun h => absurd h (by omega))
    have e : Lagrange.interpolate Finset.univ d.Pb.nodesJ (fun i => Nock.Jet.ChipJ8.jetPre d.Pb.lay 11 i) =
        Msk 0 d.Pb.nodesJ hn0 0 := by
      unfold Msk
      rw [if_pos rfl, Nock.Framework.firstRowMask]
      congr 1 <;> (funext i; simp [Nock.Jet.ChipJ8.jetPre])
    exact e.trans this.symm
  by_cases h12 : c = 12
  · subst h12
    unfold jetMasksOk at hmasks
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hmasks
    obtain ⟨-, ⟨k, hk⟩⟩ := hmasks
    have := polyOfArr_Msk9 XI d.Pb.nJ hinj (XI.pre[XI.tabs[t].col0 + 12]!) (hpreC_of_shapeF h _) 1 d.Pb.nodesJ hn0 L.nodesJ 0 k
      (by rw [hn, pre_getD]; exact hk) (fun h => absurd h (by omega))
    have e : Lagrange.interpolate Finset.univ d.Pb.nodesJ (fun i => Nock.Jet.ChipJ8.jetPre d.Pb.lay 12 i) =
        Msk 1 d.Pb.nodesJ hn0 0 := by
      unfold Msk
      rw [if_neg (by omega), if_pos rfl, Nock.Framework.lastRowMask]
      congr 1 <;> (funext i; simp [Nock.Jet.ChipJ8.jetPre, Fin.ext_iff])
    exact e.trans this.symm
  · -- the layout columns
    have hcl := List.all_eq_true.mp hcols c (List.mem_range.mpr hc)
    simp only [Bool.or_eq_true, beq_iff_eq, h11, h12, false_or, jetColOk, Bool.and_eq_true, decide_eq_true_eq] at hcl
    obtain ⟨hsz, hev⟩ := hcl
    rw [hgd c] at hev hsz
    have hlen' : (layJ XI.pubIn).length = XI.tabs[t].hN := hlen
    rw [toArray_range _ _ (by simpa using hlen')] at hev
    have hev' := eval_of_pat' _ XI.hGen (hpreC_of_shapeF h _) XI.tabs[t].hN _ hev
    have hdeg : (polyOfArr (XI.pre[XI.tabs[t].col0 + c]!)).degree < (d.Pb.nJ : WithBot ℕ) := by
      have h0 := degree_polyOfList (XI.pre[XI.tabs[t].col0 + c]!).toList
      have hle2 : (((XI.pre[XI.tabs[t].col0 + c]!).toList.length : ℕ) : WithBot ℕ) ≤ (d.Pb.nJ : WithBot ℕ) := by
        exact_mod_cast (by simpa [hn] using hsz)
      exact lt_of_lt_of_le h0 hle2
    have hv : ∀ i : Fin d.Pb.nJ, (polyOfArr (XI.pre[XI.tabs[t].col0 + c]!)).eval (d.Pb.nodesJ i) =
        Nock.Jet.ChipJ8.jetPre d.Pb.lay c i := by
      intro i
      have hi : (i : ℕ) < XI.tabs[t].hN := hn ▸ i.2
      have hev2 := hev' i hi
      rw [L.nodesJ i]
      refine hev2.trans ?_
      have hil : (i : ℕ) < (layJ XI.pubIn).length := by omega
      have hq : (layJ XI.pubIn)[(i : ℕ)] = d.Pb.lay i := by
        have := List.getElem_of_eq hlay.symm hil
        rw [this]; simp
      simp only [Nock.Jet.ChipJ8.jetPre, if_neg h11, if_neg h12]
      rw [List.getD_eq_getElem _ _ (by simpa using hil), List.getElem_map, hq]
      exact preColG_zv _ c hc h11 h12 (hsm _ (by rw [← hq]; exact List.getElem_mem hil))
    have hinj' : Function.Injective d.Pb.nodesJ := by
      intro a b hab
      exact hinj ((L.nodesJ a).symm.trans (hab.trans (L.nodesJ b)))
    have key := eq_interp d.Pb.nodesJ hinj' _ hdeg _ hv
    exact key.symm

end NockvmE2E.Z38.PreJBridge

#print axioms NockvmE2E.Z38.PreJBridge.preColG_zv
#print axioms NockvmE2E.Z38.PreJBridge.toArray_range
#print axioms NockvmE2E.Z38.PreJBridge.preJLink_of_jetPreOkF
