/-
C2 (`E2EJ9ALQ`): hop 0, the numerals and the constraint-count cap of the NINE J-9 AL tables from the
executed chip check `chipsOkF famJ9AL`.  The old eight tables: `hop9_old` (the body of `E2EJ9AQ.hops9_of_chips`' per-table `key`, stated per chip);
the ALU: `hopZero_alu` (twin of `chipEqB_tie` + `hopZero_of_tie`, at `aluDers`, from the split kernel checks `J9ALChipsK_alu_*`).
Not zero-knowledge.
-/
import NockvmE2E.J9A.E2EJ9AQ
import NockvmE2E.J9AL.TieJ9AL
import NockvmE2E.J9AL.GenJ9AL
import NockvmE2E.J9AL.LagrJ9AL
import NockvmE2E.Exec.J9ALChipsK_alu
import NockvmE2E.Exec.J9ALChipsFam

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

open Polynomial

namespace NockvmE2E.J9AL.E2EJ9ALQ

open NockvmE2E.Exec NockvmE2E.Exec.Tr NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J8ChipsK NockvmE2E.Emit Nock.Emit
open NockvmE2E.Exec.V NockvmE2E.Exec.E2EGen NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips NockvmE2E.Exec.J9ALChips
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.TieJ9A NockvmE2E.J9A.GenJ9A NockvmE2E.J9A.LagrJ9A
open NockvmE2E.J9AL.InstJ9AL NockvmE2E.J9AL.TieJ9AL NockvmE2E.J9AL.GenJ9AL NockvmE2E.J9AL.LagrJ9AL
open NockvmE2E.J8.TieJ8 (HopZero)
open NockvmE2E.Exec.E2EJ8F (chipEqB_baseCols chipEqB_size litTies)
open NockvmE2E.J9A.E2EJ9AQ
open NockvmE2E.J8 NockvmE2E.Exec.VC

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- **hop 0, the numeral, `bcOf9` and the size cap of one old (J-9 A) table** (the per-chip body of `hops9_of_chips`) -/
theorem hop9_old (c : NockvmE2E.Exec.Tr.Chip) (hmem : c.id ∈ idsJ9A) (d : Datum9A)
    (hn : chipNumeralF famJ9A c = some (numOf9 d (tabIdx9 c.id))) :
    (HopZero c (DOf9 d (tabIdx9 c.id)) NockvmE2E.Exec.J8Chips.jDers NockvmE2E.Exec.J8Chips.jMeta c.baseCols ∧
      c.baseCols = bcOf9 (tabIdx9 c.id)) ∧ NumOK9 d (tabIdx9 c.id) ∧ c.cons.size ≤ 100000 := by
  obtain ⟨lit, hlit, hE⟩ := num_findF famJ9A _ _ hn
  have no : ∀ s : Fin 8, s ≠ 2 → s ≠ 5 → s ≠ 7 → NumOK9 d s := fun s h2 h5 h7 =>
    ⟨fun h => absurd h h2, fun h => absurd h h5, fun h => absurd h h7⟩
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

/-! ## the ALU: hop 0 at `aluDers` -/

theorem list_eq_of_slices {α : Type} (a b : List α) (hl : a.length = b.length) (hle : b.length ≤ 300)
    (h0 : (a.drop 0).take 60 = (b.drop 0).take 60) (h1 : (a.drop 60).take 60 = (b.drop 60).take 60)
    (h2 : (a.drop 120).take 60 = (b.drop 120).take 60) (h3 : (a.drop 180).take 60 = (b.drop 180).take 60)
    (h4 : (a.drop 240).take 60 = (b.drop 240).take 60) : a = b := by
  have key : ∀ lo i : ℕ, (a.drop lo).take 60 = (b.drop lo).take 60 → lo ≤ i → i < lo + 60 → a[i]? = b[i]? := by
    intro lo i h hlo hi
    have := congrArg (fun l => l[i - lo]?) h
    simp only [List.getElem?_take, List.getElem?_drop, show i - lo < 60 by omega, if_true,
      show lo + (i - lo) = i by omega] at this
    exact this
  apply List.ext_getElem? 
  intro i
  by_cases hi : i < 300
  · by_cases a1 : i < 60
    · exact key 0 i h0 (by omega) (by omega)
    by_cases a2 : i < 120
    · exact key 60 i h1 (by omega) (by omega)
    by_cases a3 : i < 180
    · exact key 120 i h2 (by omega) (by omega)
    by_cases a4 : i < 240
    · exact key 180 i h3 (by omega) (by omega)
    · exact key 240 i h4 (by omega) (by omega)
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem chipAlu_size : chipAlu.cons.size ≤ 300 := by decide +kernel

/-- the kernel ties of `chipAlu` at `aluDers` (assembled from the split checks) -/
theorem tieAlu_spec :
    ∃ c0, chipOfDag (emitDag aluSpec) = some c0 ∧ (verifierChipT c0 aluDers jMeta).1.shared = chipAlu.shared ∧
      (verifierChipT c0 aluDers jMeta).1.cons.map (·.e) = chipAlu.cons.map (·.e) := by
  have hs := J9ALChipsK_alu_shared
  have hl := J9ALChipsK_alu_len
  have h0 := J9ALChipsK_alu_cons0
  have h1 := J9ALChipsK_alu_cons1
  have h2 := J9ALChipsK_alu_cons2
  have h3 := J9ALChipsK_alu_cons3
  have h4 := J9ALChipsK_alu_cons4
  unfold tieSharedAL at hs
  unfold tieLenAL at hl
  unfold tieConsAL at h0 h1 h2 h3 h4
  cases hc : chipOfDag (emitDag aluSpec) with
  | none => simp [hc] at hs
  | some c0 =>
    simp only [hc, beq_iff_eq] at hs hl h0 h1 h2 h3 h4
    have e1 := (exListEqB_iff _ _).1 hs
    have e0 := (exListEqB_iff _ _).1 h0
    have e1' := (exListEqB_iff _ _).1 h1
    have e2 := (exListEqB_iff _ _).1 h2
    have e3 := (exListEqB_iff _ _).1 h3
    have e4 := (exListEqB_iff _ _).1 h4
    refine ⟨c0, rfl, ?_, ?_⟩
    · apply Array.ext'
      simpa [verifierChipT, Array.toList_append, Array.toList_map] using e1
    · apply Array.ext'
      have := list_eq_of_slices _ _ (by simpa using hl) (by simpa using chipAlu_size) e0 e1' e2 e3 e4
      simpa [verifierChipT, Array.toList_map, List.map_map, Function.comp_def] using this

/-- **hop 0 of the ALU**: a loaded chip equal to `chipAlu` is the verifier chip of the emitted `aluSpec` DAG at `aluDers` -/
theorem hopZero_alu (c : NockvmE2E.Exec.Tr.Chip) (h : chipEqB c chipAlu = true) :
    HopZero c emit_alu aluDers jMeta c.baseCols := by
  obtain ⟨c0, hc, hs, hcons⟩ := tieAlu_spec
  obtain ⟨sh, cb, ce, cm, c1, c3, cq, hsh, hcb, hce, hcm, hc1, hc3, hcq, hs0, hc0⟩ := HopsLit.chipOfDag_split _ c0 hc
  refine ⟨{ c0 with baseCols := c.baseCols }, sh, cb, ce, cm, c1, c3, cq, hsh, hcb, hce, hcm, hc1, hc3, hcq, hs0, hc0, ?_, ?_, rfl⟩
  · exact (chipEqB_shared c chipAlu h).trans hs.symm
  · exact (chipEqB_cons_e c chipAlu h).trans hcons.symm

/-! ## the nine tables -/

theorem tabIdx9L_alu : tabIdx9L "aluChipJ9" = 8 := rfl

theorem tabIdx9L_old (id : String) (h : id ≠ "aluChipJ9") : tabIdx9L id = (tabIdx9 id).castSucc := if_neg h

theorem numOf9L_castSucc (d : Datum9AL) (s : Fin 8) : numOf9L d s.castSucc = numOf9 d.toA s := by
  unfold numOf9L
  rw [dif_pos (by simp)]
  rfl

/-- hop 0, the numeral and the size cap of one table of the nine, from its numeral check -/
theorem hop9L_table (c : NockvmE2E.Exec.Tr.Chip) (hmem : c.id ∈ idsJ9AL) (d : Datum9AL)
    (hn : chipNumeralF famJ9AL c = some (numOf9L d (tabIdx9L c.id))) :
    (HopZero c (DOf9L d (tabIdx9L c.id)) (dersL (tabIdx9L c.id)) NockvmE2E.Exec.J8Chips.jMeta c.baseCols ∧
      c.baseCols = bcOf9L (tabIdx9L c.id)) ∧ NumOK9L d (tabIdx9L c.id) ∧ c.cons.size ≤ 100000 := by
  by_cases ha : c.id = "aluChipJ9"
  · obtain ⟨lit, hlit, hE⟩ := num_findF famJ9AL _ _ hn
    rw [ha] at hlit
    have hl : lit = chipAlu := by
      have h := hlit; unfold expectedOfF at h; rw [famJ9AL_alu_lits] at h
      simp only [List.mem_singleton, Prod.mk.injEq] at h; exact h.2
    subst hl
    rw [ha, tabIdx9L_alu, dersL_eight]
    refine ⟨⟨?_, ?_⟩, trivial, ?_⟩
    · exact hopZero_alu c hE
    · exact (chipEqB_baseCols c _ hE).trans rfl
    · rw [chipEqB_size c _ hE]; exact le_trans chipAlu_size (by norm_num)
  · have hmem' : c.id ∈ idsJ9A := by
      simp only [idsJ9AL, List.mem_append, List.mem_singleton] at hmem
      exact hmem.resolve_right ha
    have hlits : (famJ9AL.lits c.id) = famJ9A.lits c.id := (famJ9AL_j9a c.id ha).2.2.2.2
    have hnum : chipNumeralF famJ9A c = some (numOf9 d.toA (tabIdx9 c.id)) := by
      have e : chipNumeralF famJ9AL c = chipNumeralF famJ9A c := by
        unfold chipNumeralF expectedOfF; rw [hlits]
      rw [← e, hn, tabIdx9L_old _ ha, numOf9L_castSucc]
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hop9_old c hmem' d.toA hnum
    rw [tabIdx9L_old _ ha, DOf9L_old, dersL_ne _ (fun h => by have h0 := (tabIdx9 c.id).2; have h' := congrArg Fin.val h; simp at h'; omega), bcOf9L_old, NumOK9L_old]
    exact ⟨⟨h1, h2⟩, h3, h4⟩

/-- **hop 0, the numerals and the size cap of the nine tables** from the executed chip check (twin of `hops9_of_chips`) -/
theorem hops9L_of_chips {XI : ExecInst} (hsh : shapeOkF famJ9AL XI = true) (d : Datum9AL) (hc : chipsOkF famJ9AL XI = true)
    (hnum0 : ∀ t : Fin XI.tabs.size, (chipNumeralF famJ9AL XI.tabs[t].chip).getD 0 = numOf9L d (sigma9L XI t)) :
    (∀ t : Fin XI.tabs.size, HopZero XI.tabs[t].chip (DOf9L d (sigma9L XI t)) (dersL (sigma9L XI t)) NockvmE2E.Exec.J8Chips.jMeta
        XI.tabs[t].chip.baseCols ∧ XI.tabs[t].chip.baseCols = bcOf9L (sigma9L XI t)) ∧
      (∀ t : Fin XI.tabs.size, NumOK9L d (sigma9L XI t)) ∧ ∀ t : Fin XI.tabs.size, XI.tabs[t].chip.cons.size ≤ 100000 := by
  have key : ∀ t : Fin XI.tabs.size, (HopZero XI.tabs[t].chip (DOf9L d (sigma9L XI t)) (dersL (sigma9L XI t))
        NockvmE2E.Exec.J8Chips.jMeta XI.tabs[t].chip.baseCols ∧ XI.tabs[t].chip.baseCols = bcOf9L (sigma9L XI t)) ∧
      NumOK9L d (sigma9L XI t) ∧ XI.tabs[t].chip.cons.size ≤ 100000 := by
    intro t
    have hnum : chipNumeralF famJ9AL XI.tabs[t].chip = some (numOf9L d (sigma9L XI t)) := by
      have h1 : (chipNumeralF famJ9AL XI.tabs[t].chip).isSome = true := by
        unfold chipsOkF at hc
        exact Array.all_eq_true.mp hc t.1 t.2
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h1
      have := hnum0 t
      rw [hk] at this ⊢
      simpa [Option.getD] using congrArg some this
    have hmem : XI.tabs[t].chip.id ∈ idsJ9AL := (ids_of_shapeF hsh).2 _ (Array.getElem_mem_toList t.2)
    have := hop9L_table XI.tabs[t].chip hmem d hnum
    exact this
  exact ⟨fun t => (key t).1, fun t => (key t).2.1, fun t => (key t).2.2⟩

end NockvmE2E.J9AL.E2EJ9ALQ

#print axioms NockvmE2E.J9AL.E2EJ9ALQ.hop9_old
#print axioms NockvmE2E.J9AL.E2EJ9ALQ.hopZero_alu
#print axioms NockvmE2E.J9AL.E2EJ9ALQ.hops9L_of_chips
