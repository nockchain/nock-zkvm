/-
the table restriction `R: TabRestr (J8 d hd)` and `hfree`.
-/
import NockvmE2E.J8.InstJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.J8.InstJ8W

open NockvmE2E.Rap NockvmE2E.J8 NockvmE2E.J8.InstJ8
open NockvmE2E.Exec.V (ExecInst TabInst)
open NockvmE2E.Exec.J8Shape (j8ShapeOk)
open Nock.Jet.ChipJ8 (PRow)

variable {B K : Type} [Field B] [Field K] [Algebra B K] [Fintype K] [DecidableEq K]

/-- **the table restriction of any `σ : Fin T' → Fin J.T`**: columns / constraints of the tables in the range of `σ`. -/
noncomputable def TabRestr.ofSigma (J : RapAirJ B K) (T' : ℕ) (σ : Fin T' → Fin J.T) : TabRestr J :=
  haveI := Classical.decPred (fun i : Fin J.ns => ∃ t, σ t = J.tabS i)
  { T' := T'
    σ := σ
    p := fun j => ∃ t, σ t = J.tabC j
    dp := Classical.decPred _
    hp := fun _ => Iff.rfl
    ns' := Fintype.card {i : Fin J.ns // ∃ t, σ t = J.tabS i}
    ρ := fun k => ((Fintype.equivFin {i : Fin J.ns // ∃ t, σ t = J.tabS i}).symm k).1
    hρ := fun a b h => (Fintype.equivFin {i : Fin J.ns // ∃ t, σ t = J.tabS i}).symm.injective (Subtype.ext h)
    tabS' := fun k => Classical.choose ((Fintype.equivFin {i : Fin J.ns // ∃ t, σ t = J.tabS i}).symm k).2
    hρtab := fun k => Classical.choose_spec ((Fintype.equivFin {i : Fin J.ns // ∃ t, σ t = J.tabS i}).symm k).2
    hρcov := fun i t h => ⟨Fintype.equivFin {i : Fin J.ns // ∃ t, σ t = J.tabS i} ⟨i, ⟨t, h⟩⟩, by simp⟩ }

theorem TabRestr.ofSigma_q (J : RapAirJ B K) (T' : ℕ) (σ : Fin T' → Fin J.T) (t : Fin J.T) :
    (TabRestr.ofSigma J T' σ).q t ↔ ∃ t', σ t' = t := Iff.rfl

/-- the J-8 flat table index of a chip id -/
def tabIdx (id : String) : Fin 6 :=
  if id == "computeChipVCLHX" then 0 else if id == "cellChipHQKW" then 1 else if id == "walkChipJ8" then 2
  else if id == "jetChipJ8" then 3 else if id == "atomChipHQL" then 4 else 5

theorem tabIdx_tabId (t : Fin 6) : tabIdx (tabId t) = t := by
  fin_cases t <;> decide

/-- the table of the instance `t'` ↦ the J-8 flat table index of its chip -/
def sigmaX (XI : ExecInst) (t : Fin XI.tabs.size) : Fin 6 := tabIdx XI.tabs[t].chip.id

/-- **`R : TabRestr (J8 d hd)`**: the tables of the instance (`T' = XI.tabs.size`) -/
noncomputable def RJ8 (XI : ExecInst) (d : Datum) (hd : DatumOK d) : TabRestr (J8 d hd) :=
  TabRestr.ofSigma (J8 d hd) XI.tabs.size (sigmaX XI)

/-- every J-8-present table is a table of the instance (`present_tab`) -/
theorem presentJ8_q (XI : ExecInst) (hsh : j8ShapeOk XI = true) (hpos : PosX XI) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → PRow) (d : Datum) (hd : d.Pb = PbOfX XI hsh hpos kroots krootsV Rt regs ids idx rk lay)
    (hdk : DatumOK d) (t : Fin 6) (ht : presentJ8 d t) : (RJ8 XI d hdk).q t := by
  have hm := present_tab XI hsh hpos kroots krootsV Rt regs ids idx rk lay d hd t ht
  obtain ⟨tb, htb, hid⟩ := List.mem_map.mp hm
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp htb
  refine ⟨⟨i, (by simpa using hi : i < XI.tabs.size)⟩, ?_⟩
  show tabIdx _ = t
  simp only [Array.getElem_toList] at hid
  show tabIdx (XI.tabs[i]).chip.id = t
  rw [hid, tabIdx_tabId]

/-- **`hfree`**: `J8 d hd` accepts as soon as the constraints of the instance's tables vanish -/
theorem hfree_J8 (XI : ExecInst) (hsh : j8ShapeOk XI = true) (hpos : PosX XI) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → PRow) (d : Datum) (hd : d.Pb = PbOfX XI hsh hpos kroots krootsV Rt regs ids idx rk lay)
    (hdk : DatumOK d) : (J8 d hdk).AccOn (RJ8 XI d hdk).q :=
  RapAirJ.AccOn.mono _ (fun t h => presentJ8_q XI hsh hpos kroots krootsV Rt regs ids idx rk lay d hd hdk t h)
    (accOn_J8 d hdk)

end NockvmE2E.J8.InstJ8W

#print axioms NockvmE2E.J8.InstJ8W.hfree_J8
#print axioms NockvmE2E.J8.InstJ8W.TabRestr.ofSigma
