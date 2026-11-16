/-
  Nock/NockVMROM/Thm54/VclL/Handle/Ground.lean

  * `exportRec` — the record a cell row provides on the export lookup, keyed by its serial:
    `(idx, hL, hR)` with child handles `(true, idL)` (a weighted child) or `(false, aL)` (an atom);
  * `ExportServed` — the LogUp existence form (every consumed record is some row's record) and
    `ExportBalanced.served` — derived from the ℕ multiset balance, as `ValidityBalanced.served`;
  * `exportRec_grounded` — **one consumed record is grounded**: from `row_genuine` (T1, the rank μ)
    `denH (1, i) = cell (denH hL) (denH hR)`.  No compute fingerprint is read; the lookup is depth-1;
  * the toy: states `cons | dec | eqT | ret`, rows holding three handles and a bit; `cons`/`dec`
    rows consume one export record, `eqT` rows decide OP5 "=" ONLY by handle equality
    (`bit = true → h1 = h2`); `ToyAccepts`; **`toy_grounding`**: on an accepted cell table and an
    accepted toy trace whose consumed records are served, every row's claim holds on denotations
    (induction along the trace).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.Serial

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock
open Nock.NockVMROM.Thm54.VclL

/-! ## 1. The export record and its lookup -/

section Export
variable {q : ℕ}

/-- The handle of a row's left child: `(true, idL)` if weighted, else the atom `(false, aL)`. -/
def hL (c : CellRowB0 q) : VHandle := (c.wL, if c.wL then c.idL else c.aL.val)
/-- The handle of a row's right child. -/
def hR (c : CellRowB0 q) : VHandle := (c.wR, if c.wR then c.idR else c.aR.val)

/-- **The export record of a cell row**, keyed by its serial: `(idx, hL, hR)`. -/
def exportRec (c : CellRowB0 q) : ℕ × VHandle × VHandle := (c.idx, hL c, hR c)

/-- **LogUp existence form**: every consumed export record is the record of some row. -/
def ExportServed (t : List (CellRowB0 q)) (xs : List (ℕ × VHandle × VHandle)) : Prop :=
  ∀ r ∈ xs, ∃ c ∈ t, r = exportRec c

/-- **The ℕ multiset balance** of the export lookup: the rows' records with multiplicity `mx`
equal the consumed records plus any other consumers `other`. -/
def ExportBalanced (t : List (CellRowB0 q)) (xs other : List (ℕ × VHandle × VHandle)) : Prop :=
  (expand (t.map fun c => (exportRec c, c.mx))).Perm (expand ((xs ++ other).map (·, 1)))

theorem ExportBalanced.served {t : List (CellRowB0 q)} {xs other : List (ℕ × VHandle × VHandle)}
    (h : ExportBalanced t xs other) : ExportServed t xs := by
  intro r hr
  have hmem : r ∈ expand ((xs ++ other).map (·, 1)) := by
    rw [mem_expand]
    exact ⟨(r, 1), List.mem_map.mpr ⟨r, List.mem_append_left _ hr, rfl⟩, one_ne_zero, rfl⟩
  have hp := h.mem_iff.mpr hmem
  rw [mem_expand] at hp
  obtain ⟨kc, hkc, -, hk⟩ := hp
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hkc
  exact ⟨c, hc, hk⟩

/-- **One consumed record is grounded** (depth-1; T1 `row_genuine`, well-founded on μ). -/
theorem exportRec_grounded {Kfp : Type*} [Field Kfp] [Algebra (ZMod q) Kfp] [Fact q.Prime]
    (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0) {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)}
    (h : TableAccepts z t vl) {c : CellRow q Kfp} (hc : c ∈ t) :
    ∃ L R, denH (t.map (·.b0)) (true, c.b0.idx) = some (.cell L R) ∧
      denH (t.map (·.b0)) (hL c.b0) = some L ∧ denH (t.map (·.b0)) (hR c.b0) = some R := by
  obtain ⟨L, R, hd, -, -, -, hLw, hLa, hRw, hRa⟩ := row_genuine hq hz h hc
  refine ⟨L, R, hd, ?_, ?_⟩
  · unfold hL
    cases hw : c.b0.wL
    · simp [denH, hLa hw]
    · simp [denH, hLw hw]
  · unfold hR
    cases hw : c.b0.wR
    · simp [denH, hRa hw]
    · simp [denH, hRw hw]

/-- **Every served record is grounded**: a consumed `(i, hl, hr)` has
`denH (1, i) = cell (denH hl) (denH hr)`. -/
theorem served_grounded {Kfp : Type*} [Field Kfp] [Algebra (ZMod q) Kfp] [Fact q.Prime]
    (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0) {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)}
    (h : TableAccepts z t vl) {xs : List (ℕ × VHandle × VHandle)}
    (hs : ExportServed (t.map (·.b0)) xs) :
    ∀ r ∈ xs, ∃ L R, denH (t.map (·.b0)) (true, r.1) = some (.cell L R) ∧
      denH (t.map (·.b0)) r.2.1 = some L ∧ denH (t.map (·.b0)) r.2.2 = some R := by
  intro r hr
  obtain ⟨c0, hc0, rfl⟩ := hs r hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc0
  exact exportRec_grounded hq hz h hc

end Export

/-! ## 2. The toy compute model -/

/-- Toy states: `cons` builds `h0 = [h1 h2]`, `dec` decodes `h0 = [h1 h2]`, `eqT` is OP5 "=" on
`h1 h2` with output `bit`, `ret` does nothing. -/
inductive ToySt
  | cons | dec | eqT | ret
deriving DecidableEq

/-- A toy compute row: a state, three handles, one bit. -/
structure ToyRow where
  st : ToySt
  h0 : VHandle
  h1 : VHandle
  h2 : VHandle
  bit : Bool
deriving DecidableEq

/-- The export record a row consumes (`cons` / `dec`: the cell `h0` keyed by its serial). -/
def ToyRow.consumes (r : ToyRow) : Option (ℕ × VHandle × VHandle) :=
  match r.st with
  | .cons | .dec => some (r.h0.2, r.h1, r.h2)
  | _ => none

/-- **The toy's local gates**: a `cons`/`dec` row's `h0` is a serial handle (kind bit `1`);
OP5 "=" is decided by handle equality only (`bit = 1 → h1 = h2`; the `≠` direction is NOT read
off serials). -/
def ToyRow.Gates (r : ToyRow) : Prop :=
  (r.st = .cons ∨ r.st = .dec → r.h0.1 = true) ∧ (r.st = .eqT → r.bit = true → r.h1 = r.h2)

/-- The consumed export records of a toy trace. -/
def toyConsumed (rows : List ToyRow) : List (ℕ × VHandle × VHandle) := rows.filterMap ToyRow.consumes

/-- **An accepted toy trace** over a B0 cell table: every row gate, and the export lookup served
(LogUp existence). -/
structure ToyAccepts {q : ℕ} (t : List (CellRowB0 q)) (rows : List ToyRow) : Prop where
  gates : ∀ r ∈ rows, r.Gates
  served : ExportServed t (toyConsumed rows)

/-- **A row's semantic claim on denotations.** -/
def ToyRow.Sem {q : ℕ} (t : List (CellRowB0 q)) (r : ToyRow) : Prop :=
  match r.st with
  | .cons | .dec => ∃ L R, denH t r.h0 = some (.cell L R) ∧ denH t r.h1 = some L ∧ denH t r.h2 = some R
  | .eqT => r.bit = true → denH t r.h1 = denH t r.h2
  | .ret => True

section Toy
variable {q : ℕ} {Kfp : Type*} [Field Kfp] [Algebra (ZMod q) Kfp] [Fact q.Prime]

/-- **The grounding induction (toy).**  On an accepted cell table (T1 at the rank μ) and an
accepted toy trace whose consumed records are served by the table's export lookup, every row's
claim holds on `denH`: built and decoded cells are genuine cells of the denoted children, and an
OP5 "=" accepted on handles holds on nouns.  No compute fingerprint; lookups depth-1. -/
theorem toy_grounding (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0) {t : List (CellRow q Kfp)}
    {vl : List (VKey Kfp)} (h : TableAccepts z t vl) :
    ∀ rows : List ToyRow, ToyAccepts (t.map (·.b0)) rows → ∀ r ∈ rows, r.Sem (t.map (·.b0)) := by
  intro rows
  induction rows with
  | nil => intro _ r hr; simp at hr
  | cons r0 rows ih =>
    intro hacc r hr
    have hacc' : ToyAccepts (t.map (·.b0)) rows :=
      ⟨fun r hr => hacc.gates r (List.mem_cons_of_mem _ hr),
       fun x hx => hacc.served x (by
        unfold toyConsumed at hx ⊢; rw [List.filterMap_cons]; split <;> simp_all)⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · have hg := hacc.gates r (List.mem_cons_self ..)
      have key : r.st = .cons ∨ r.st = .dec →
          ∃ L R, denH (t.map (·.b0)) r.h0 = some (.cell L R) ∧ denH (t.map (·.b0)) r.h1 = some L ∧
            denH (t.map (·.b0)) r.h2 = some R := by
        intro hst
        have hcons : r.consumes = some (r.h0.2, r.h1, r.h2) := by
          rcases hst with h' | h' <;> simp [ToyRow.consumes, h']
        have hmem : (r.h0.2, r.h1, r.h2) ∈ toyConsumed (r :: rows) := by
          unfold toyConsumed; rw [List.filterMap_cons, hcons]; exact List.mem_cons_self ..
        obtain ⟨L, R, h1, h2, h3⟩ := served_grounded hq hz h hacc.served _ hmem
        have hk : r.h0 = (true, r.h0.2) := by
          rw [← hg.1 hst]
        exact ⟨L, R, by rw [hk]; exact h1, h2, h3⟩
      unfold ToyRow.Sem
      cases hs : r.st with
      | cons => exact key (Or.inl hs)
      | dec => exact key (Or.inr hs)
      | eqT => intro hb; rw [hg.2 hs hb]
      | ret => trivial
    · exact ih hacc' r hr

end Toy

end Nock.NockVMROM.Thm54.VclL.Handle
