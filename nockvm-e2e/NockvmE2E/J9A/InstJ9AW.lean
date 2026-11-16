/-
J9A-LINK: the table restriction `RJ9A : TabRestr (J9A d hd)` and `hfree_J9A` (twin of
`J8/InstJ8W.lean`'s `RJ8` / `hfree_J8`).
-/
import NockvmE2E.J9A.PbOfX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.J9A.InstJ9AW

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.GenJ9A NockvmE2E.J9A.PbOfX9
open NockvmE2E.J8.InstJ8 (P tabOf hNof tabOf_isSome_of_mem)
open NockvmE2E.J8.InstJ8W (TabRestr.ofSigma)
open NockvmE2E.J8 (RapAirJ TabRestr)
open Nock.Jet.ChipJ8 (PRow)

/-- **`RJ9A : TabRestr (J9A d hd)`**: the tables of the instance (`T' = XI.tabs.size`, `σ = sigma9 XI`) -/
noncomputable def RJ9A (XI : ExecInst) (d : Datum9A) (hd : DatumOK9A d) : TabRestr (J9A d hd) :=
  TabRestr.ofSigma (J9A d hd) XI.tabs.size (sigma9 XI)

theorem tabIdx9_idOf9 (t : Fin 8) : tabIdx9 (idOf9 t) = t := by
  fin_cases t <;> decide

/-- a J-9 A table whose chip id is a table of the instance is in the range of `sigma9` -/
theorem sigma9_range (XI : ExecInst) (t : Fin 8) (hm : idOf9 t ∈ XI.tabs.toList.map (·.chip.id)) :
    ∃ t' : Fin XI.tabs.size, sigma9 XI t' = t := by
  obtain ⟨tb, htb, hid⟩ := List.mem_map.mp hm
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp htb
  refine ⟨⟨i, (by simpa using hi : i < XI.tabs.size)⟩, ?_⟩
  show tabIdx9 (XI.tabs[i]).chip.id = t
  simp only [Array.getElem_toList] at hid
  rw [hid, tabIdx9_idOf9]

/-- if the table `id` has rows (`hNof ≠ 0`) or is `isSome`, the chip id is a table id of the instance -/
theorem mem_of_hNof_ne {XI : ExecInst} {id : String} (h : hNof XI id ≠ 0) : id ∈ XI.tabs.toList.map (·.chip.id) := by
  unfold hNof tabOf at h
  cases hf : XI.tabs.toList.find? (fun t => t.chip.id == id) with
  | none => simp [hf] at h
  | some t0 =>
    have h1 := List.mem_of_find?_eq_some hf
    have h2 := List.find?_some hf
    simp only [beq_iff_eq] at h2
    exact List.mem_map.mpr ⟨t0, h1, h2⟩

theorem mem_of_isSome {XI : ExecInst} {id : String} (h : (tabOf XI id).isSome = true) :
    id ∈ XI.tabs.toList.map (·.chip.id) := by
  unfold tabOf at h
  cases hf : XI.tabs.toList.find? (fun t => t.chip.id == id) with
  | none => simp [hf] at h
  | some t0 =>
    have h1 := List.mem_of_find?_eq_some hf
    have h2 := List.find?_some hf
    simp only [beq_iff_eq] at h2
    exact List.mem_map.mpr ⟨t0, h1, h2⟩

/-- **the only obligation of `hfree`**: every present table of `PbOfX9` is a table of the instance -/
theorem present9A_q (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → PRow) (d : Datum9A) (hd : d.Pb = PbOfX9 XI h kroots krootsV Rt regs ids idx rk lay)
    (hdk : DatumOK9A d) (t : Fin 8) (ht : present9A d t) : (RJ9A XI d hdk).q t := by
  have hm := mand_mem9 h
  show ∃ t', sigma9 XI t' = t
  refine sigma9_range XI t ?_
  obtain ⟨h3, h5, h6, h7⟩ := ht
  fin_cases t
  · exact hm (idOf9 _) (by simp [famJ9A, idOf9])
  · exact hm (idOf9 _) (by simp [famJ9A, idOf9])
  · exact hm (idOf9 _) (by simp [famJ9A, idOf9])
  · have hJ : d.Pb.nJ ≠ 0 := fun h0 => h3 ⟨rfl, h0⟩
    rw [hd] at hJ
    exact mem_of_hNof_ne (id := "jetChipJ8") hJ
  · exact hm (idOf9 _) (by simp [famJ9A, idOf9])
  · have hV : d.Pb.krootsV ≠ 0 := fun h0 => h5 ⟨rfl, h0⟩
    rw [hd] at hV
    have hV' : (if (tabOf XI "walkChipHQK").isSome then krootsV else 0) ≠ 0 := hV
    by_cases hs : (tabOf XI "walkChipHQK").isSome = true
    · exact mem_of_isSome hs
    · simp [hs] at hV'
  · have hX : d.Pb.axOn = true := by
      by_contra hc
      exact h6 ⟨rfl, by simpa using hc⟩
    rw [hd] at hX
    exact mem_of_isSome (id := "axisChipJ9") hX
  · have hS : d.Pb.spOn = true := by
      by_contra hc
      exact h7 ⟨rfl, by simpa using hc⟩
    rw [hd] at hS
    exact mem_of_isSome (id := "splitChipJ9") hS

/-- **`hfree_J9A`**: `J9A d hd` accepts as soon as the constraints of the instance's tables vanish -/
theorem hfree_J9A (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → PRow) (d : Datum9A) (hd : d.Pb = PbOfX9 XI h kroots krootsV Rt regs ids idx rk lay)
    (hdk : DatumOK9A d) : (J9A d hdk).AccOn (RJ9A XI d hdk).q :=
  RapAirJ.AccOn.mono _ (fun t ht => present9A_q XI h kroots krootsV Rt regs ids idx rk lay d hd hdk t ht)
    (NockvmE2E.J8.IfaceG.accOn_ofIface (clJ9A d hdk) (nJ9A d hdk))

end NockvmE2E.J9A.InstJ9AW

#print axioms NockvmE2E.J9A.InstJ9AW.RJ9A
#print axioms NockvmE2E.J9A.InstJ9AW.present9A_q
#print axioms NockvmE2E.J9A.InstJ9AW.hfree_J9A
