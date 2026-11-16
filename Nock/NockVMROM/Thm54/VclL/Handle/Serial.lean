/-
  Nock/NockVMROM/Thm54/VclL/Handle/Serial.lean

  * `serial_functional` / `serial_functional_rows` — on a table meeting `SerialOK` (the threading
    gate's consequence), two rows with equal `idx` are the same row;
  * `cellTable_rows_functional` — the same at the chip: an accepted cell table under
    `hnp : n < ringChar F` (= `Checks.hrowsM`, `D < p`), via `cellTable_serial`;
  * `rowByKey` (a lookup BY KEY, `find?` on `idx = i`; no index arithmetic) and
    `getElem?_eq_rowByKey` — the bridge from `decodeB0`'s positional `t[i]?` (`Table.lean`,
    `decodeB0`) to the key lookup under `SerialOK`; `decodeKey`, `decodeB0_eq_decodeKey`;
  * `denH` — `(false, v) ↦ atom v`, `(true, i) ↦ preZNounOfTable t i`;
    `denH_serial_meaning`: `denH (true, i) = some n` iff SOME row with `idx = i` decodes (by key) to
    `n`, and that row is unique.  The statement mentions membership and the `idx` field only.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.RowModel

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock
open Nock.NockVMROM.Thm54.VclL

/-! ## 1. Functional serials -/

section Functional
variable {q : ℕ}

/-- **Functional serials (B0 rows).**  Under `SerialOK`, two rows with equal `idx` are equal. -/
theorem serial_functional {t : List (CellRowB0 q)} (hs : SerialOK t) {c c' : CellRowB0 q}
    (hc : c ∈ t) (hc' : c' ∈ t) (h : c.idx = c'.idx) : c = c' := by
  have h1 := serial_lookup hs hc
  have h2 := serial_lookup hs hc'
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

/-- **Functional serials (full rows, fingerprints included).**  Under `SerialOK` of the round-0
projection, two rows of the table with equal `idx` are the same row. -/
theorem serial_functional_rows {Kfp : Type*} {t : List (CellRow q Kfp)}
    (hs : SerialOK (t.map (·.b0))) {c c' : CellRow q Kfp} (hc : c ∈ t) (hc' : c' ∈ t)
    (h : c.b0.idx = c'.b0.idx) : c = c' := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc'
  have key : ∀ k (hk : k < t.length), (t[k]).b0.idx = k := by
    intro k hk
    have e := congrArg (fun l => l[k]?) hs
    simp only [List.map_map, List.getElem?_map, List.getElem?_eq_getElem hk,
      List.getElem?_range (show k < t.length by simpa using hk), Option.map_some,
      Option.some.injEq, Function.comp_apply, List.length_map] at e
    exact e
  have : i = j := by rw [← key i hi, ← key j hj, h]
  subst this; rfl

end Functional

/-! ## 2. Positionless lookup: `t[i]?` is the lookup by key under `SerialOK` -/

section Key
variable {q : ℕ}

/-- **The row with key `idx = i`** (a search by key; reads no position). -/
def rowByKey (t : List (CellRowB0 q)) (i : ℕ) : Option (CellRowB0 q) := t.find? (fun c => c.idx == i)

theorem rowByKey_spec {t : List (CellRowB0 q)} {i : ℕ} {c : CellRowB0 q}
    (h : rowByKey t i = some c) : c ∈ t ∧ c.idx = i := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

theorem getElem?_eq_rowByKey {t : List (CellRowB0 q)} (hs : SerialOK t) (i : ℕ) :
    t[i]? = rowByKey t i := by
  cases hk : rowByKey t i with
  | some c =>
    obtain ⟨hc, hci⟩ := rowByKey_spec hk
    rw [← hci]; exact serial_lookup hs hc
  | none =>
    rw [rowByKey, List.find?_eq_none] at hk
    rcases Nat.lt_or_ge i t.length with hi | hi
    · exfalso
      have e := congrArg (fun l => l[i]?) hs
      simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
        List.getElem?_range (show i < t.length from hi), Option.map_some,
        Option.some.injEq] at e
      have := hk t[i] (List.getElem_mem hi)
      simp [e] at this
    · exact List.getElem?_eq_none hi

/-- **The decode by key**: `decodeB0` with the positional read replaced by `rowByKey`. -/
def decodeKey (t : List (CellRowB0 q)) : ℕ → ℕ → Option Noun
  | 0, _ => none
  | fuel + 1, i =>
    (rowByKey t i).bind fun c =>
      (if c.wL then decodeKey t fuel c.idL else some (.atom c.aL.val)).bind fun a =>
        (if c.wR then decodeKey t fuel c.idR else some (.atom c.aR.val)).bind fun b =>
          some (.cell a b)

theorem decodeB0_eq_decodeKey {t : List (CellRowB0 q)} (hs : SerialOK t) :
    ∀ f i, decodeB0 t f i = decodeKey t f i
  | 0, _ => rfl
  | f + 1, i => by
    simp only [decodeB0, decodeKey, getElem?_eq_rowByKey hs]
    have ih := decodeB0_eq_decodeKey hs f
    simp only [ih]

/-- The noun one row names, children decoded by key at fuel `f`. -/
def rowNounKey (t : List (CellRowB0 q)) (f : ℕ) (c : CellRowB0 q) : Option Noun :=
  (if c.wL then decodeKey t f c.idL else some (.atom c.aL.val)).bind fun a =>
    (if c.wR then decodeKey t f c.idR else some (.atom c.aR.val)).bind fun b => some (.cell a b)

end Key

/-! ## 3. The handle denotation -/

section Den
variable {q : ℕ}

/-- **A compute handle** `(kind, value)`: `kind = false` an atom with value `v`, `kind = true` the
cell-table serial `i`. -/
abbrev VHandle := Bool × ℕ

def denH (t : List (CellRowB0 q)) : VHandle → Option Noun
  | (false, v) => some (.atom v)
  | (true, i) => preZNounOfTable t i

@[simp] theorem denH_atom (t : List (CellRowB0 q)) (v : ℕ) : denH t (false, v) = some (.atom v) := rfl
@[simp] theorem denH_cell (t : List (CellRowB0 q)) (i : ℕ) :
    denH t (true, i) = preZNounOfTable t i := rfl

/-- **The meaning of a serial handle, positionless.**  Under `SerialOK`, `denH (1, i) = some n`
iff some row of the table with key `idx = i` names `n` (children decoded by key), and any two rows
with key `i` are the same row. -/
theorem denH_serial_meaning {t : List (CellRowB0 q)} (hs : SerialOK t) (i : ℕ) (n : Noun) :
    (denH t (true, i) = some n ↔
      ∃ c ∈ t, c.idx = i ∧ rowNounKey t (fuelChip - 1) c = some n) ∧
    (∀ c ∈ t, ∀ c' ∈ t, c.idx = i → c'.idx = i → c = c') := by
  refine ⟨?_, fun c hc c' hc' h h' => serial_functional hs hc hc' (h.trans h'.symm)⟩
  have hf : fuelChip = (fuelChip - 1) + 1 := by unfold fuelChip; norm_num
  rw [denH_cell, preZNounOfTable, decodeB0_eq_decodeKey hs, hf, decodeKey]
  constructor
  · intro h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, hn⟩ := h
    obtain ⟨hm, hi⟩ := rowByKey_spec hc
    exact ⟨c, hm, hi, hn⟩
  · rintro ⟨c, hm, hi, hn⟩
    rw [Option.bind_eq_some_iff]
    refine ⟨c, ?_, hn⟩
    rw [← getElem?_eq_rowByKey hs, ← hi]
    exact serial_lookup hs hm

end Den

/-! ## 4. At the chip: functional serials on an accepted cell table under `n < p` -/

section Chip
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension
open scoped Polynomial

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))]
  (b : Module.Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

theorem cellTable_rows_functional
    (Q : Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hF : GeneratedField.PrimeFieldElems F)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnp : n < ringChar F)
    {c c' : CellRow (ringChar F) (Quad (algebraMap F K δF))}
    (hc : c ∈ cellTableOf δF b nodes orbit chals pubs Q)
    (hc' : c' ∈ cellTableOf δF b nodes orbit chals pubs Q) (hidx : c.b0.idx = c'.b0.idx) :
    c = c' :=
  serial_functional_rows
    (cellTable_serial δF b hn nodes orbit chals pubs Q hsat hF hbind hinj hadj hnp) hc hc' hidx

end Chip

end Nock.NockVMROM.Thm54.VclL.Handle
