/-
the table restriction `RJ9AL : TabRestr (J9AL d hd)`, `present9L_q`, `hfree_J9AL` (twin of `J9A/InstJ9AW.lean`).
Not zero-knowledge.
-/
import NockvmE2E.J9AL.PbOfX9L
import NockvmE2E.J9A.InstJ9AW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.J9AL.InstJ9ALW

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips NockvmE2E.Exec.J9ALChips
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.GenJ9A NockvmE2E.J9A.PbOfX9
open NockvmE2E.J9AL.InstJ9AL NockvmE2E.J9AL.GenJ9AL NockvmE2E.J9AL.PbOfX9L
open NockvmE2E.J9A.InstJ9AW (mem_of_hNof_ne mem_of_isSome)
open NockvmE2E.J8.InstJ8 (P tabOf hNof tabOf_isSome_of_mem)
open NockvmE2E.J8.InstJ8W (TabRestr.ofSigma)
open NockvmE2E.J8 (RapAirJ TabRestr)
open Nock.Jet.ChipJ8 (PRow)

/-- **`RJ9AL : TabRestr (J9AL d hd)`**: the tables of the instance (`T' = XI.tabs.size`, `σ = sigma9L XI`) -/
noncomputable def RJ9AL (XI : ExecInst) (d : Datum9AL) (hd : DatumOK9AL d) : TabRestr (J9AL d hd) :=
  TabRestr.ofSigma (J9AL d hd) XI.tabs.size (sigma9L XI)

theorem tabIdx9L_idOf9L (t : Fin 9) : tabIdx9L (idOf9L t) = t := by
  fin_cases t <;> decide

theorem sigma9L_range (XI : ExecInst) (t : Fin 9) (hm : idOf9L t ∈ XI.tabs.toList.map (·.chip.id)) :
    ∃ t' : Fin XI.tabs.size, sigma9L XI t' = t := by
  obtain ⟨tb, htb, hid⟩ := List.mem_map.mp hm
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp htb
  refine ⟨⟨i, (by simpa using hi : i < XI.tabs.size)⟩, ?_⟩
  show tabIdx9L (XI.tabs[i]).chip.id = t
  simp only [Array.getElem_toList] at hid
  rw [hid, tabIdx9L_idOf9L]

/-- **the only obligation of `hfree`**: every present table of `PbOfX9L` is a table of the instance -/
theorem present9L_q (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → PRow) (d : Datum9AL) (hd : d.Pb = PbOfX9L XI h kroots krootsV Rt regs ids idx rk lay)
    (hdk : DatumOK9AL d) (t : Fin 9) (ht : present9L d t) : (RJ9AL XI d hdk).q t := by
  have hm := mand_memL h
  show ∃ t', sigma9L XI t' = t
  refine sigma9L_range XI t ?_
  obtain ⟨hp8, hpl⟩ := ht
  fin_cases t
  · exact hm "computeChipVCLHX9" (by simp [famJ9AL])
  · exact hm "cellChipHQKW" (by simp [famJ9AL])
  · exact hm "walkChipJ8" (by simp [famJ9AL])
  · obtain ⟨h3, -, -, -⟩ := hp8 (by decide)
    have hJ : d.Pb.nJ ≠ 0 := fun h0 => h3 ⟨rfl, h0⟩
    rw [hd] at hJ
    exact mem_of_hNof_ne (id := "jetChipJ8") hJ
  · exact hm "atomChipHQL" (by simp [famJ9AL])
  · obtain ⟨-, h5, -, -⟩ := hp8 (by decide)
    have hV : d.Pb.krootsV ≠ 0 := fun h0 => h5 ⟨rfl, h0⟩
    rw [hd] at hV
    have hV' : (if (tabOf XI "walkChipHQK").isSome then krootsV else 0) ≠ 0 := hV
    by_cases hs : (tabOf XI "walkChipHQK").isSome = true
    · exact mem_of_isSome hs
    · simp [hs] at hV'
  · obtain ⟨-, -, h6, -⟩ := hp8 (by decide)
    have hX : d.Pb.axOn = true := by
      by_contra hc
      exact h6 ⟨rfl, show d.Pb.axOn = false by simpa using hc⟩
    rw [hd] at hX
    exact mem_of_isSome (id := "axisChipJ9") hX
  · obtain ⟨-, -, -, h7⟩ := hp8 (by decide)
    have hS : d.Pb.spOn = true := by
      by_contra hc
      exact h7 ⟨rfl, show d.Pb.spOn = false by simpa using hc⟩
    rw [hd] at hS
    exact mem_of_isSome (id := "splitChipJ9") hS
  · have hon : d.Pb.aluOn = true := by
      by_contra hc
      exact hpl ⟨rfl, by simpa using hc⟩
    rw [hd] at hon
    exact mem_of_isSome (id := "aluChipJ9") hon

/-- **`hfree_J9AL`**: `J9AL d hd` accepts as soon as the constraints of the instance's tables vanish -/
theorem hfree_J9AL (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → PRow) (d : Datum9AL) (hd : d.Pb = PbOfX9L XI h kroots krootsV Rt regs ids idx rk lay)
    (hdk : DatumOK9AL d) : (J9AL d hdk).AccOn (RJ9AL XI d hdk).q :=
  RapAirJ.AccOn.mono _ (fun t ht => present9L_q XI h kroots krootsV Rt regs ids idx rk lay d hd hdk t ht)
    (NockvmE2E.J8.IfaceG.accOn_ofIface (clJ9AL d hdk) (nJ9AL d hdk))

end NockvmE2E.J9AL.InstJ9ALW

#print axioms NockvmE2E.J9AL.InstJ9ALW.RJ9AL
#print axioms NockvmE2E.J9AL.InstJ9ALW.present9L_q
#print axioms NockvmE2E.J9AL.InstJ9ALW.hfree_J9AL
