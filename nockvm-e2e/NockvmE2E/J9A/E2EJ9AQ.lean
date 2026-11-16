/-
part 6: hop 0, the numerals and the constraint-count cap of the eight J-9 A tables from the executed chip check
`chipsOkF famJ9A` (twin of `E2EJ8F.hops_of_chips`): `litTies9` (the 16 literal ties: 12 J-8 from `J8ChipsK_*`, 4 J-9 A from `J9AChipsK_*`)
and `hops9_of_chips`.
-/
import NockvmE2E.J9A.LagrJ9A
import NockvmE2E.Exec.E2EJ8F
import NockvmE2E.Exec.J9AChipsK_compute9
import NockvmE2E.Exec.J9AChipsK_axis
import NockvmE2E.Exec.J9AChipsK_split_1
import NockvmE2E.Exec.J9AChipsK_split_2
import NockvmE2E.Exec.J8ChipsK_walkJ8_3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open Polynomial

namespace NockvmE2E.J9A.E2EJ9AQ

open NockvmE2E.Exec NockvmE2E.Exec.Tr NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J8ChipsK NockvmE2E.Emit Nock.Emit
open NockvmE2E.Exec.V NockvmE2E.Exec.E2EGen NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.TieJ9A NockvmE2E.J9A.GenJ9A NockvmE2E.J9A.LagrJ9A
open NockvmE2E.J8.TieJ8 (HopZero)
open NockvmE2E.Exec.E2EJ8F (chipEqB_baseCols chipEqB_size litTies)
open NockvmE2E.Exec.E2EGenH (LitTiesF)

/-- the emitted spec of a literal -/
def spec9 (id : String) (k : ℕ) : Nock.Emit.TSpec :=
  if id = "computeChipVCLHX9" then computeSpec9 else if id = "axisChipJ9" then axisSpec else if id = "splitChipJ9" then splitSpecAt k
  else if id = "cellChipHQKW" then cellKWSpec else if id = "atomChipHQL" then atomSpec else if id = "jetChipJ8" then jetSpec
  else if id = "walkChipJ8" then walkJ8SpecAt k else if id = "walkChipHQK" then walkAtomSpecAt k else computeSpec

theorem L_c9 : famJ9A.lits "computeChipVCLHX9" = [(0, chipCompute9)] := rfl
theorem L_ax : famJ9A.lits "axisChipJ9" = [(0, chipAxis)] := rfl
theorem L_sp : famJ9A.lits "splitChipJ9" = [(1, chipSplit_1), (2, chipSplit_2)] := rfl
theorem L_c8 : famJ9A.lits "computeChipVCLHX" = [(0, chipCompute)] := rfl
theorem L_ce : famJ9A.lits "cellChipHQKW" = [(0, chipCell)] := rfl
theorem L_at : famJ9A.lits "atomChipHQL" = [(0, chipAtom)] := rfl
theorem L_je : famJ9A.lits "jetChipJ8" = [(0, chipJet)] := rfl
theorem L_wk : famJ9A.lits "walkChipJ8" =
  [(1, chipWalkJ8_1), (9, chipWalkJ8_9), (25, chipWalkJ8_25), (42, chipWalkJ8_42), (48, chipWalkJ8_48), (174, chipWalkJ8_174), (3, chipWalkJ8_3)] := rfl
theorem L_wv : famJ9A.lits "walkChipHQK" = [(1, chipWalkHQK_1), (2, chipWalkHQK_2)] := rfl

theorem litTies9 : LitTiesF famJ9A spec9 := by
  obtain ⟨t1, t2, t3, t4, w1, w9, w25, w42, w48, w174, q1, q2⟩ := litTies
  intro id k lit h
  by_cases e1 : id = "computeChipVCLHX9"
  · subst e1; rw [L_c9] at h; simp only [List.mem_singleton, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨tie_compute9, by decide +kernel⟩
  by_cases e2 : id = "axisChipJ9"
  · subst e2; rw [L_ax] at h; simp only [List.mem_singleton, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨tie_axis, by decide +kernel⟩
  by_cases e3 : id = "splitChipJ9"
  · subst e3; rw [L_sp] at h; simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨tie_split_1, by decide +kernel⟩
    · exact ⟨tie_split_2, by decide +kernel⟩
  by_cases f1 : id = "computeChipVCLHX"
  · subst f1; rw [L_c8] at h; simp only [List.mem_singleton, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simpa [spec9] using t1, by decide +kernel⟩
  by_cases f2 : id = "cellChipHQKW"
  · subst f2; rw [L_ce] at h; simp only [List.mem_singleton, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simpa [spec9] using t2, by decide +kernel⟩
  by_cases f3 : id = "atomChipHQL"
  · subst f3; rw [L_at] at h; simp only [List.mem_singleton, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simpa [spec9] using t3, by decide +kernel⟩
  by_cases f4 : id = "jetChipJ8"
  · subst f4; rw [L_je] at h; simp only [List.mem_singleton, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simpa [spec9] using t4, by decide +kernel⟩
  by_cases f5 : id = "walkChipJ8"
  · subst f5; rw [L_wk] at h; simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨by simpa [spec9] using w1, by decide +kernel⟩
    · exact ⟨by simpa [spec9] using w9, by decide +kernel⟩
    · exact ⟨by simpa [spec9] using w25, by decide +kernel⟩
    · exact ⟨by simpa [spec9] using w42, by decide +kernel⟩
    · exact ⟨by simpa [spec9] using w48, by decide +kernel⟩
    · exact ⟨by simpa [spec9] using w174, by decide +kernel⟩
    · exact ⟨by simpa [spec9] using tie_walkJ8_3, by decide +kernel⟩
  by_cases f6 : id = "walkChipHQK"
  · subst f6; rw [L_wv] at h; simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨by simpa [spec9] using q1, by decide +kernel⟩
    · exact ⟨by simpa [spec9] using q2, by decide +kernel⟩
  have c1 : (id == "computeChipVCLHX") = false := by simpa using f1
  have c2 : (id == "cellChipHQKW") = false := by simpa using f2
  have c3 : (id == "atomChipHQL") = false := by simpa using f3
  have c4 : (id == "jetChipJ8") = false := by simpa using f4
  have c5 : (id == "walkChipJ8") = false := by simpa using f5
  have c6 : (id == "walkChipHQK") = false := by simpa using f6
  have b1 : (id == "computeChipVCLHX9") = false := by simpa using e1
  have b2 : (id == "axisChipJ9") = false := by simpa using e2
  have b3 : (id == "splitChipJ9") = false := by simpa using e3
  simp [famJ9A, lits9, expectedOf, b1, b2, b3, c1, c2, c3, c4, c5, c6] at h

open NockvmE2E.J8

theorem tabIdx9_0 : tabIdx9 "computeChipVCLHX9" = 0 := by decide
theorem tabIdx9_1 : tabIdx9 "cellChipHQKW" = 1 := by decide
theorem tabIdx9_2 : tabIdx9 "walkChipJ8" = 2 := by decide
theorem tabIdx9_3 : tabIdx9 "jetChipJ8" = 3 := by decide
theorem tabIdx9_4 : tabIdx9 "atomChipHQL" = 4 := by decide
theorem tabIdx9_5 : tabIdx9 "walkChipHQK" = 5 := by decide
theorem tabIdx9_6 : tabIdx9 "axisChipJ9" = 6 := by decide
theorem tabIdx9_7 : tabIdx9 "splitChipJ9" = 7 := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- **hop 0, the numerals and the size cap of every loaded table from the executed chip check** -/
theorem hops9_of_chips {XI : ExecInst} (hsh : shapeOkF famJ9A XI = true) (d : Datum9A) (hc : chipsOkF famJ9A XI = true)
    (hnum0 : ∀ t : Fin XI.tabs.size, (chipNumeralF famJ9A XI.tabs[t].chip).getD 0 = numOf9 d (sigma9 XI t)) :
    (∀ t : Fin XI.tabs.size, HopZero XI.tabs[t].chip (DOf9 d (sigma9 XI t)) NockvmE2E.Exec.J8Chips.jDers NockvmE2E.Exec.J8Chips.jMeta
        XI.tabs[t].chip.baseCols ∧ XI.tabs[t].chip.baseCols = bcOf9 (sigma9 XI t)) ∧
      (∀ t : Fin XI.tabs.size, NumOK9 d (sigma9 XI t)) ∧ ∀ t : Fin XI.tabs.size, XI.tabs[t].chip.cons.size ≤ 100000 := by

  have hnum : ∀ t : Fin XI.tabs.size, chipNumeralF famJ9A XI.tabs[t].chip = some (numOf9 d (sigma9 XI t)) := by
    intro t
    have h1 : (chipNumeralF famJ9A XI.tabs[t].chip).isSome = true := by
      unfold chipsOkF at hc
      exact Array.all_eq_true.mp hc t.1 t.2
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h1
    have := hnum0 t
    rw [hk] at this ⊢
    simpa [Option.getD] using congrArg some this
  have no : ∀ s : Fin 8, s ≠ 2 → s ≠ 5 → s ≠ 7 → NumOK9 d s := fun s h2 h5 h7 =>
    ⟨fun h => absurd h h2, fun h => absurd h h5, fun h => absurd h h7⟩
  have key : ∀ t : Fin XI.tabs.size, (HopZero XI.tabs[t].chip (DOf9 d (sigma9 XI t)) NockvmE2E.Exec.J8Chips.jDers NockvmE2E.Exec.J8Chips.jMeta
        XI.tabs[t].chip.baseCols ∧ XI.tabs[t].chip.baseCols = bcOf9 (sigma9 XI t)) ∧
      NumOK9 d (sigma9 XI t) ∧ XI.tabs[t].chip.cons.size ≤ 100000 := by
    intro t
    have hmem : XI.tabs[t].chip.id ∈ idsJ9A := (ids_of_shapeF hsh).2 _ (Array.getElem_mem_toList t.2)
    obtain ⟨lit, hlit, hE⟩ := num_findF famJ9A _ _ (hnum t)
    have hn := hnum t
    have hs : sigma9 XI t = tabIdx9 XI.tabs[t].chip.id := rfl
    generalize XI.tabs[t].chip = c at *
    rw [hs] at hn hlit ⊢
    simp only [idsJ9A, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hid | hid | hid | hid | hid | hid | hid | hid <;> rw [hid] at hlit hn ⊢
    · rw [tabIdx9_0] at hn hlit ⊢
      have hl : lit = chipCompute9 := by
        have h := hlit; unfold expectedOfF at h; rw [L_c9] at h; simp only [List.mem_singleton, Prod.mk.injEq] at h; exact h.2
      subst hl
      refine ⟨⟨(HopsLit.hopZero_of_tie _ _ c tie_compute9 hE), (chipEqB_baseCols c _ hE).trans rfl⟩, no 0 (by decide) (by decide) (by decide), ?_⟩
      rw [chipEqB_size c _ hE]; decide +kernel
    · rw [tabIdx9_1] at hn hlit ⊢
      have hl : lit = chipCell := by
        have h := hlit; unfold expectedOfF at h; rw [L_ce] at h; simp only [List.mem_singleton, Prod.mk.injEq] at h; exact h.2
      subst hl
      refine ⟨⟨(HopsLit.hopZero_of_tie _ _ c litTies.2.1 hE), (chipEqB_baseCols c _ hE).trans rfl⟩, no 1 (by decide) (by decide) (by decide), ?_⟩
      rw [chipEqB_size c _ hE]; decide +kernel
    · rw [tabIdx9_2] at hn hlit ⊢
      unfold expectedOfF at hlit
      rw [L_wk] at hlit
      simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false] at hlit
      simp [numOf9] at hlit
      rcases hlit with ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩
      · refine ⟨⟨?_, (chipEqB_baseCols c _ hE).trans rfl⟩, ⟨fun _ => by rw [hk]; decide, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, ?_⟩
        · show HopZero c (emitDag (walkJ8SpecAt d.Pb.kroots)) _ _ _
          rw [hk]; exact HopsLit.hopZero_of_tie _ _ c litTies.2.2.2.2.1 hE
        · rw [chipEqB_size c _ hE]; decide +kernel
      · refine ⟨⟨?_, (chipEqB_baseCols c _ hE).trans rfl⟩, ⟨fun _ => by rw [hk]; decide, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, ?_⟩
        · show HopZero c (emitDag (walkJ8SpecAt d.Pb.kroots)) _ _ _
          rw [hk]; exact HopsLit.hopZero_of_tie _ _ c litTies.2.2.2.2.2.1 hE
        · rw [chipEqB_size c _ hE]; decide +kernel
      · refine ⟨⟨?_, (chipEqB_baseCols c _ hE).trans rfl⟩, ⟨fun _ => by rw [hk]; decide, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, ?_⟩
        · show HopZero c (emitDag (walkJ8SpecAt d.Pb.kroots)) _ _ _
          rw [hk]; exact HopsLit.hopZero_of_tie _ _ c litTies.2.2.2.2.2.2.1 hE
        · rw [chipEqB_size c _ hE]; decide +kernel
      · refine ⟨⟨?_, (chipEqB_baseCols c _ hE).trans rfl⟩, ⟨fun _ => by rw [hk]; decide, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, ?_⟩
        · show HopZero c (emitDag (walkJ8SpecAt d.Pb.kroots)) _ _ _
          rw [hk]; exact HopsLit.hopZero_of_tie _ _ c litTies.2.2.2.2.2.2.2.1 hE
        · rw [chipEqB_size c _ hE]; decide +kernel
      · refine ⟨⟨?_, (chipEqB_baseCols c _ hE).trans rfl⟩, ⟨fun _ => by rw [hk]; decide, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, ?_⟩
        · show HopZero c (emitDag (walkJ8SpecAt d.Pb.kroots)) _ _ _
          rw [hk]; exact HopsLit.hopZero_of_tie _ _ c litTies.2.2.2.2.2.2.2.2.1 hE
        · rw [chipEqB_size c _ hE]; decide +kernel
      · refine ⟨⟨?_, (chipEqB_baseCols c _ hE).trans rfl⟩, ⟨fun _ => by rw [hk]; decide, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, ?_⟩
        · show HopZero c (emitDag (walkJ8SpecAt d.Pb.kroots)) _ _ _
          rw [hk]; exact HopsLit.hopZero_of_tie _ _ c litTies.2.2.2.2.2.2.2.2.2.1 hE
        · rw [chipEqB_size c _ hE]; decide +kernel
      · refine ⟨⟨?_, (chipEqB_baseCols c _ hE).trans rfl⟩, ⟨fun _ => by rw [hk]; decide, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, ?_⟩
        · show HopZero c (emitDag (walkJ8SpecAt d.Pb.kroots)) _ _ _
          rw [hk]; exact HopsLit.hopZero_of_tie _ _ c tie_walkJ8_3 hE
        · rw [chipEqB_size c _ hE]; decide +kernel
    · rw [tabIdx9_4] at hn hlit ⊢
      have hl : lit = chipAtom := by
        have h := hlit; unfold expectedOfF at h; rw [L_at] at h; simp only [List.mem_singleton, Prod.mk.injEq] at h; exact h.2
      subst hl
      refine ⟨⟨(HopsLit.hopZero_of_tie _ _ c litTies.2.2.1 hE), (chipEqB_baseCols c _ hE).trans rfl⟩, no 4 (by decide) (by decide) (by decide), ?_⟩
      rw [chipEqB_size c _ hE]; decide +kernel
    · rw [tabIdx9_5] at hn hlit ⊢
      unfold expectedOfF at hlit
      rw [L_wv] at hlit
      simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false] at hlit
      simp [numOf9] at hlit
      rcases hlit with ⟨hk, rfl⟩ | ⟨hk, rfl⟩
      · refine ⟨⟨?_, (chipEqB_baseCols c _ hE).trans rfl⟩, ⟨fun h => absurd h (by decide), fun _ => by rw [hk]; decide, fun h => absurd h (by decide)⟩, ?_⟩
        · show HopZero c (emitDag (walkAtomSpecAt d.Pb.krootsV)) _ _ _
          rw [hk]; exact HopsLit.hopZero_of_tie _ _ c litTies.2.2.2.2.2.2.2.2.2.2.1 hE
        · rw [chipEqB_size c _ hE]; decide +kernel
      · refine ⟨⟨?_, (chipEqB_baseCols c _ hE).trans rfl⟩, ⟨fun h => absurd h (by decide), fun _ => by rw [hk]; decide, fun h => absurd h (by decide)⟩, ?_⟩
        · show HopZero c (emitDag (walkAtomSpecAt d.Pb.krootsV)) _ _ _
          rw [hk]; exact HopsLit.hopZero_of_tie _ _ c litTies.2.2.2.2.2.2.2.2.2.2.2 hE
        · rw [chipEqB_size c _ hE]; decide +kernel
    · rw [tabIdx9_3] at hn hlit ⊢
      have hl : lit = chipJet := by
        have h := hlit; unfold expectedOfF at h; rw [L_je] at h; simp only [List.mem_singleton, Prod.mk.injEq] at h; exact h.2
      subst hl
      refine ⟨⟨(HopsLit.hopZero_of_tie _ _ c litTies.2.2.2.1 hE), (chipEqB_baseCols c _ hE).trans rfl⟩, no 3 (by decide) (by decide) (by decide), ?_⟩
      rw [chipEqB_size c _ hE]; decide +kernel
    · rw [tabIdx9_6] at hn hlit ⊢
      have hl : lit = chipAxis := by
        have h := hlit; unfold expectedOfF at h; rw [L_ax] at h; simp only [List.mem_singleton, Prod.mk.injEq] at h; exact h.2
      subst hl
      refine ⟨⟨(HopsLit.hopZero_of_tie _ _ c tie_axis hE), (chipEqB_baseCols c _ hE).trans rfl⟩, no 6 (by decide) (by decide) (by decide), ?_⟩
      rw [chipEqB_size c _ hE]; decide +kernel
    · rw [tabIdx9_7] at hn hlit ⊢
      unfold expectedOfF at hlit
      rw [L_sp] at hlit
      simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false] at hlit
      simp [numOf9] at hlit
      rcases hlit with ⟨hk, rfl⟩ | ⟨hk, rfl⟩
      · refine ⟨⟨?_, (chipEqB_baseCols c _ hE).trans rfl⟩, ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => by rw [hk]; decide⟩, ?_⟩
        · show HopZero c (Nock.Emit.emit_splitAt d.Pb.nA) _ _ _
          rw [hk]; exact HopsLit.hopZero_of_tie _ _ c tie_split_1 hE
        · rw [chipEqB_size c _ hE]; decide +kernel
      · refine ⟨⟨?_, (chipEqB_baseCols c _ hE).trans rfl⟩, ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => by rw [hk]; decide⟩, ?_⟩
        · show HopZero c (Nock.Emit.emit_splitAt d.Pb.nA) _ _ _
          rw [hk]; exact HopsLit.hopZero_of_tie _ _ c tie_split_2 hE
        · rw [chipEqB_size c _ hE]; decide +kernel
  exact ⟨fun t => (key t).1, fun t => (key t).2.1, fun t => (key t).2.2⟩

end NockvmE2E.J9A.E2EJ9AQ

#print axioms NockvmE2E.J9A.E2EJ9AQ.litTies9
#print axioms NockvmE2E.J9A.E2EJ9AQ.hops9_of_chips
