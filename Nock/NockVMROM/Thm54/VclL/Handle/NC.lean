/-
  Nock/NockVMROM/Thm54/VclL/Handle/NC.lean

  (a) `nc_dup_serial_op5_eq_accepted` — with the threading gate removed, a cell table with two rows
      at `idx 5` naming `[1 2] ≠ [3 4]` passes every other table check (`RowOK`, `ValidityServed`);
      both export records `(5, …)` are served, the toy trace that decodes both and runs OP5 "=" on
      `(1,5),(1,5)` is accepted, and NO denotation of handles grounds both records (the forgery).
      With the gate in place the table is rejected (`¬ SerialOK`), and on any table meeting
      `SerialOK` two served records with one key are the same record (`served_key_functional`).
  (b) `nc_op5_ne_by_serial_unsound` — an ACCEPTED (`TableAccepts`) honest-shaped table holding
      `[1 2]` at serials `0` and `1`: distinct serial handles, equal denotations.  So "serials
      differ ⇒ nouns differ" is false; OP5 "≠" must not be read off serials.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.Ground

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.NC

open Nock
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle

instance fact67 : Fact (Nat.Prime 67) := ⟨by norm_num⟩

/-- The toy seed. -/
abbrev z67 : ZMod 67 := 2

/-- A rank-1 cell row at serial `i` with two atom children `a b` (fingerprints at the seed). -/
def atomRow (i : ℕ) (a b : ZMod 67) : CellRow 67 (ZMod 67) :=
  let l := FP.atomFP z67 a
  let r := FP.atomFP z67 b
  { b0 := { idx := i, idL := 0, idR := 0, wL := false, wR := false, aL := a, aR := b,
            lo := 1, hi := 0, loL := 0, hiL := 0, loR := 0, hiR := 0, carry := 0, mv := 0, mx := 1 }
    p := FP.cons z67 l r, l := l, r := r }

theorem atomRow_ok (i : ℕ) (a b : ZMod 67) : RowOK z67 (atomRow i a b) where
  cons := rfl
  lo_lt := by simp [atomRow]
  loL_lt := by simp [atomRow]
  loR_lt := by simp [atomRow]
  hi_lt := by simp [atomRow]
  hiL_lt := by simp [atomRow]
  hiR_lt := by simp [atomRow]
  carry_le := by simp [atomRow]
  limbLo := by simp [atomRow]
  limbHi := by simp [atomRow]
  atomL := fun _ => ⟨rfl, rfl, rfl⟩
  atomR := fun _ => ⟨rfl, rfl, rfl⟩

theorem atomRow_served (t : List (CellRow 67 (ZMod 67))) (ht : ∀ c ∈ t, c.b0.wL = false ∧ c.b0.wR = false) :
    ValidityServed t := by
  intro c hc
  obtain ⟨h1, h2⟩ := ht c hc
  exact ⟨fun h => by simp [h1] at h, fun h => by simp [h2] at h⟩

/-! ## (a) Duplicate serials without the gate -/

/-- **The forged table**: two rows at serial `5`, naming `[1 2]` and `[3 4]`. -/
def tDup : List (CellRow 67 (ZMod 67)) := [atomRow 5 1 2, atomRow 5 3 4]

/-- The toy trace: decode both rows' records at serial `5`, then OP5 "=" on `(1,5),(1,5)`. -/
def rowsDup : List ToyRow :=
  [⟨.dec, (true, 5), (false, 1), (false, 2), false⟩,
   ⟨.dec, (true, 5), (false, 3), (false, 4), false⟩,
   ⟨.eqT, (false, 0), (true, 5), (true, 5), true⟩]

/-- A denotation of handles that grounds a list of records (atoms are atoms; every record's key
denotes the cell of its children). -/
def Grounds (N : VHandle → Noun) (xs : List (ℕ × VHandle × VHandle)) : Prop :=
  (∀ v, N (false, v) = .atom v) ∧ ∀ r ∈ xs, N (true, r.1) = .cell (N r.2.1) (N r.2.2)

/-- **NC (a): the duplicate-serial OP5 "=" forgery.** -/
theorem nc_dup_serial_op5_eq_accepted :
    -- every table check except the threading gate passes
    (∀ c ∈ tDup, RowOK z67 c) ∧ ValidityServed tDup ∧
    -- the two rows at serial 5 name different nouns
    (tDup.map (·.b0)).map (fun c => (c.idx, Noun.cell (.atom c.aL.val) (.atom c.aR.val))) =
      [(5, .cell (.atom 1) (.atom 2)), (5, .cell (.atom 3) (.atom 4))] ∧
    Noun.cell (.atom 1) (.atom 2) ≠ Noun.cell (.atom 3) (.atom 4) ∧
    -- the toy trace (two decodes at serial 5, OP5 "=" on (1,5),(1,5)) is accepted
    ToyAccepts (tDup.map (·.b0)) rowsDup ∧
    -- and no denotation grounds both consumed records: the accepted "=" is a forgery
    (¬ ∃ N, Grounds N (toyConsumed rowsDup)) ∧
    -- with the gate in place the table is rejected
    ¬ SerialOK (tDup.map (·.b0)) := by
  refine ⟨?_, atomRow_served _ (by simp [tDup, atomRow]), by decide, by decide, ?_, ?_,
    by unfold SerialOK; decide⟩
  · intro c hc; simp only [tDup, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact atomRow_ok _ _ _
  · refine ⟨?_, ?_⟩
    · intro r hr
      simp only [rowsDup, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [ToyRow.Gates]
    · intro r hr
      simp only [toyConsumed, rowsDup, List.filterMap_cons, ToyRow.consumes, List.filterMap_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., by decide⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by decide⟩
  · rintro ⟨N, hN, hr⟩
    have h1 := hr (5, (false, 1), (false, 2)) (by decide)
    have h2 := hr (5, (false, 3), (false, 4)) (by decide)
    simp only [hN] at h1 h2
    rw [h1] at h2
    simp at h2

/-- **The forged table is rejected by the gate.** -/
theorem dup_table_rejected : ¬ SerialOK (tDup.map (·.b0)) := by
  unfold SerialOK; decide

/-- **With the gate in place, served records with one key are one record** (`serial_functional`):
the conflict of NC (a) cannot arise on any table meeting `SerialOK`. -/
theorem served_key_functional {q : ℕ} {t : List (CellRowB0 q)} (hs : SerialOK t)
    {xs : List (ℕ × VHandle × VHandle)} (hsv : ExportServed t xs) {r r' : ℕ × VHandle × VHandle}
    (hr : r ∈ xs) (hr' : r' ∈ xs) (hk : r.1 = r'.1) : r = r' := by
  obtain ⟨c, hc, rfl⟩ := hsv r hr
  obtain ⟨c', hc', rfl⟩ := hsv r' hr'
  rw [serial_functional hs hc hc' hk]

/-! ## (b) Distinct serials, equal nouns, on an accepted table -/

/-- **An accepted table holding `[1 2]` at serials `0` and `1`.** -/
def tTwin : List (CellRow 67 (ZMod 67)) := [atomRow 0 1 2, atomRow 1 1 2]

theorem tTwin_accepts : TableAccepts z67 tTwin [] where
  serial := by unfold SerialOK; decide
  rows := by
    intro c hc; simp only [tTwin, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact atomRow_ok _ _ _
  served := atomRow_served _ (by simp [tTwin, atomRow])

theorem tTwin_den (i : ℕ) (hi : i < 2) :
    denH (tTwin.map (·.b0)) (true, i) = some (.cell (.atom 1) (.atom 2)) := by
  have hf : fuelChip = (fuelChip - 1) + 1 := by unfold fuelChip; norm_num
  rw [denH_cell, preZNounOfTable, hf]
  interval_cases i <;> rfl

/-- **NC (b): "serials differ ⇒ nouns differ" is false on an accepted table.** -/
theorem nc_op5_ne_by_serial_unsound :
    TableAccepts z67 tTwin [] ∧ ((true, 0) : VHandle) ≠ (true, 1) ∧
      denH (tTwin.map (·.b0)) (true, 0) = denH (tTwin.map (·.b0)) (true, 1) ∧
      denH (tTwin.map (·.b0)) (true, 0) = some (.cell (.atom 1) (.atom 2)) :=
  ⟨tTwin_accepts, by decide, by rw [tTwin_den 0 (by norm_num), tTwin_den 1 (by norm_num)],
    tTwin_den 0 (by norm_num)⟩

end Nock.NockVMROM.Thm54.VclL.Handle.NC
