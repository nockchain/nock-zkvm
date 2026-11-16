/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/LocalVSX9.lean

* `CSt` — the twin's 20 chip states: the 17 J-8 states (`old st`), `s0B`, `s10B`, `s10S`;
    `CSt.sem` — the J-9 A semantic state (`s0B ↦ s0`, `s10B ↦ s10`, `s10S ↦ s10S`).
  * `RowVSX9` — a decoded twin row: its chip state, the twelve J-8 handles (a `RowVSX`) and the routed
    child label `lab = (kLab, vLab)`; `kidsX9` = `ChipHX9.childrenX9`.
  * **`DenOKX9 p D V`** — `DenOKX` plus the kind-3 segment denotation through `V` (`valId`):
    `D (3, 64·i + m) = (V i ≫= segD · m).map atom`, the kind-2 agreement `D (2, i) = atom n → V i = n`
    (discharged at LINK), `V i = n → n ≠ 0`, and the id bound `V i = n → 64·i + 64 ≤ p`
.
  * **`RowSemX09`** — old states: `RowSemX0` on the J-8 handles (no transport of J-8 semantics to a new
    state; A0 Q5); `s0B`: `slot n (D s) = D e` at `D f_t = atom n`; `s10B`: the `s10` edit read at
    `D f_tth = atom n` with the chain root's label `D lab = atom n`; `s10S`: the segment of `valId id`
    at `m ≤ top n` (`D f = segAx n m`, `m = (0, segRd n m)`, `D lab = nxtAx n m`, the pair
    `/[seg s] = D f_tth`, `/[seg e] = D f_ttt`).
  * **`local_stepX9`**, `defined_stepX9`, `roles9_of` and the tree (`RowsOKX9`,
    **`genuineNX9_of_rowsX9`**, **`holdsN_of_rowsVSX9`** — design S8's `holdsN_of_rowsVSX9`): old
    states through C-2's `local_stepX` / `defined_stepX` on the J-8 handles, the three new states here.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
import Nock.Edit.GenuineNX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9

open Nock Nock.Walk Nock.Edit
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputedWindow (FormulaShape op0Axis op9Axis condBit hd tl)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.J9A.NounAx (top segAx segRd nxtAx segD)
open Nock.Jet (Registry HoldsN JetSpec)

/-! ## 1. Chip states, rows, child labels -/

/-- The twin's 20 chip states. -/
inductive CSt
  | old (st : StateX)
  | s0B
  | s10B
  | s10S
deriving DecidableEq, Repr

/-- The semantic state of a chip state. -/
def CSt.sem : CSt → StateX9
  | .old st => StateX9.ofX st
  | .s0B => .s0
  | .s10B => .s10
  | .s10S => .s10S

/-- **A decoded twin row**: chip state, the J-8 handles, the routed child label `(kLab, vLab)`. -/
structure RowVSX9 where
  cs : CSt
  base : RowVSX
  lab : HX

def RowVSX9.trip (r : RowVSX9) : TripX := r.base.trip

/-- **The child labels per chip state** (`ChipHX9.childrenX9`). -/
def kidsX9 (r : RowVSX9) : List TripX :=
  match r.cs with
  | .old _ => kidsX r.base
  | .s0B => []
  | .s10B => [(r.base.s, r.base.fttt, r.base.sf1), (r.base.s, r.base.ftt, r.base.sf2),
      (r.base.sf2, r.lab, r.base.e)]
  | .s10S => [(r.base.s, r.base.m, r.base.e), (r.base.ftth, r.lab, r.base.fttt)]

/-! ## 2. The denotation contract and the row semantics -/

/-- **What `D` satisfies at J-9 A** (`V` is `valId`). -/
structure DenOKX9 (p : ℕ) (D : HX → Option Noun) (V : ℕ → Option ℕ) : Prop where
  base : DenOKX p D
  seg : ∀ i m, m < 64 → D (3, 64 * i + m) = ((V i).bind fun n => segD n m).map Noun.atom
  k2 : ∀ i n, D (2, i) = some (.atom n) → V i = some n
  vpos : ∀ i n, V i = some n → n ≠ 0
  idlt : ∀ i n, V i = some n → 64 * i + 64 ≤ p

section Sem
variable (p : ℕ) (D : HX → Option Noun) (V : ℕ → Option ℕ)

/-- **The J-9 A row semantics on denotations.** -/
def RowSemX09 (R : Registry) (r : RowVSX9) : Prop :=
  match r.cs with
  | .old st => r.base.st = st ∧ RowSemX0 p D R r.base
  | .s0B => Cell3 D r.base.f r.base.fh r.base.ft ∧ r.base.fh = (0, 0) ∧
      ∃ n S E, D r.base.ft = some (.atom n) ∧ D r.base.s = some S ∧ D r.base.e = some E ∧
        Noun.slot n S = some E
  | .s10B => Cell3 D r.base.f r.base.fh r.base.ft ∧ r.base.fh = (0, 10) ∧
      Cell3 D r.base.ft r.base.fth r.base.ftt ∧ Cell3 D r.base.fth r.base.ftth r.base.fttt ∧
      ∃ n, D r.base.ftth = some (.atom n) ∧ D r.lab = some (.atom n) ∧
        ∃ E N, D r.base.e = some E ∧ D r.base.sf1 = some N ∧ Noun.slot n E = some N
  | .s10S => r.base.f.1 ≠ 1 ∧ (D r.base.f ≠ none → ∃ id n m, V id = some n ∧ m ≤ top n ∧
      D r.base.f = some (.atom (segAx n m)) ∧
      r.base.m = (0, segRd n m) ∧ D r.lab = some (.atom (nxtAx n m)) ∧
      ((segRd n m = 1 ∧ r.base.ftth = r.base.s ∧ r.base.fttt = r.base.e) ∨
        ∃ S E X Y, D r.base.s = some S ∧ D r.base.e = some E ∧ D r.base.ftth = some X ∧
          D r.base.fttt = some Y ∧ Noun.slot (segRd n m) S = some X ∧ Noun.slot (segRd n m) E = some Y))

/-- **The kid-kind clause**: every real child position's formula handle is a cell serial. -/
def KidKinds9 (r : RowVSX9) : Prop :=
  ∀ i (h : i < (kidsX9 r).length), chainPosX9 r.cs.sem i = false → ((kidsX9 r)[i]'h).2.1.1 = 1

def RowSemX9 (R : Registry) (r : RowVSX9) : Prop := RowSemX09 p D V R r ∧ KidKinds9 r

/-- The `RowX9` a row denotes. -/
def rx9 (r : RowVSX9) : RowX9 := ⟨r.cs.sem, nd D r.base.s, nd D r.base.f, nd D r.base.e⟩

end Sem

/-! ## 3. Local lemmas -/

section Local
variable {p : ℕ} {D : HX → Option Noun} {V : ℕ → Option ℕ}

/-- A J-8 view of a twin row for C-2's lemmas: the handles, with a PLACEHOLDER state carrying only the
row's chain-ness (C-2's `local_stepX` / `defined_stepX` read a kid's state only through `isChain`).
No J-8 row semantics is claimed of the placeholder. -/
def toV (k : RowVSX9) : RowVSX := { k.base with st := if k.cs.sem.isChain then .s10L else .s0 }

theorem toV_isChain (k : RowVSX9) : (toV k).st.isChain = k.cs.sem.isChain := by
  unfold toV; split <;> simp_all [StateX.isChain]

theorem toV_trip (k : RowVSX9) : (toV k).trip = k.trip := rfl

theorem chainPosX9_ofX (st : StateX) (i : ℕ) : chainPosX9 (StateX9.ofX st) i = chainPosX st i := by
  rcases i with _ | _ | _ | i <;> cases st <;> rfl

theorem formulaShape_ofX (st : StateX) (f : Noun) :
    FormulaShapeX9 (StateX9.ofX st) f ↔ FormulaShapeX st f := by
  cases st <;> exact Iff.rfl

theorem kidInputsNX9_ofX (st : StateX) (s f : Noun) (ks : List RowX9) :
    KidInputsNX9 (StateX9.ofX st) s f ks ↔ KidInputsNX st s f (ks.map strip9) := by
  cases st <;> exact Iff.rfl

theorem rowOutputNX9_ofX (R : Registry) (st : StateX) (s f : Noun) (ks : List RowX9) (e : Noun) :
    RowOutputNX9 R (StateX9.ofX st) s f ks e ↔ RowOutputNX R st s f (ks.map strip9) e := by
  cases st <;> exact Iff.rfl

theorem map_strip_toV (ks : List RowVSX9) :
    ((ks.map toV).map (rx D)).map Nock.Edit.strip = (ks.map (rx9 D)).map strip9 := by
  simp [List.map_map, Function.comp_def, Nock.Edit.strip, strip9, rx, rx9, toV]

theorem cell3_not_atom {a b c : HX} (h : Cell3 D a b c) (n : ℕ) : D a ≠ some (.atom n) := by
  obtain ⟨A, B, ha, -, -⟩ := h
  rw [ha]; simp

/-- **The local step** at J-9 A. -/
theorem local_stepX9 (hD : DenOKX9 p D V) {R : Registry} (r : RowVSX9)
    (hsem : RowSemX09 p D V R r) (ks : List RowVSX9) (hk : ks.map RowVSX9.trip = kidsX9 r)
    (hrole : ∀ i (hi : i < ks.length), (ks[i]'hi).cs.sem.isChain = chainPosX9 r.cs.sem i)
    (hdef : ∀ k ∈ ks, k.cs.sem.isChain = false → D k.base.e ≠ none)
    (hf : r.cs.sem.isChain = true → D r.base.f ≠ none) :
    FormulaShapeX9 r.cs.sem (nd D r.base.f) ∧
      KidInputsNX9 r.cs.sem (nd D r.base.s) (nd D r.base.f) (ks.map (rx9 D)) ∧
      RowOutputNX9 R r.cs.sem (nd D r.base.s) (nd D r.base.f) (ks.map (rx9 D)) (nd D r.base.e) := by
  obtain ⟨cs, b, lab⟩ := r
  cases cs with
  | old st =>
    simp only [RowSemX09] at hsem
    obtain ⟨hst, hsem⟩ := hsem
    have hk' : (ks.map toV).map RowVSX.trip = kidsX b := by
      rw [List.map_map]; exact hk
    have hrole' : ∀ i (hi : i < (ks.map toV).length),
        ((ks.map toV)[i]'hi).st.isChain = chainPosX b.st i := by
      intro i hi
      simp only [List.getElem_map, toV_isChain]
      rw [hrole i (by simpa using hi), hst]
      exact chainPosX9_ofX st i
    have hdef' : ∀ k ∈ ks.map toV, k.st.isChain = false → D k.e ≠ none := by
      intro k hk0 hc
      obtain ⟨k, hk1, rfl⟩ := List.mem_map.mp hk0
      rw [toV_isChain] at hc
      exact hdef k hk1 hc
    have L := local_stepX hD.base b hsem (ks.map toV) hk' hrole' hdef'
    rw [hst] at L
    simp only [CSt.sem]
    refine ⟨(formulaShape_ofX st _).mpr L.1, ?_, ?_⟩
    · rw [kidInputsNX9_ofX, ← map_strip_toV, ← kidInputsNX_strip]; exact L.2.1
    · rw [rowOutputNX9_ofX, ← map_strip_toV, ← rowOutputNX_strip]; exact L.2.2
  | s0B =>
    simp only [RowSemX09] at hsem
    simp only [kidsX9] at hk
    have hks : ks = [] := List.map_eq_nil_iff.mp hk
    subst hks
    obtain ⟨hf3, hfh, n, S, E, hn, hS, hE, hsl⟩ := hsem
    have hF := cell3_of hf3
    rw [hfh, atom_nd hD.base, nd_of hn] at hF
    simp only [CSt.sem, FormulaShapeX9, KidInputsNX9, RowOutputNX9, StateX9.toX, KidInputsNX,
      KidInputsX, RowOutputNX, List.map_nil]
    refine ⟨⟨n, hF⟩, trivial, ?_⟩
    simp only [hF, op0Axis, nd_of hS, nd_of hE]; exact hsl
  | s10B =>
    simp only [RowSemX09] at hsem
    simp only [kidsX9] at hk
    rcases ks with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, ks⟩⟩⟩⟩ <;>
      simp only [List.map_nil, List.map_cons, List.cons.injEq, reduceCtorEq, and_false, false_and,
        List.nil_eq, List.cons_ne_nil, RowVSX9.trip, RowVSX.trip, Prod.mk.injEq, and_true] at hk
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩, ⟨h2s, h2f, h2e⟩⟩ := hk
    obtain ⟨hf3, hfh, ht3, hth3, n, hn, hlab, E, N, hE, hN, hsl⟩ := hsem
    have hF := cell3_of hf3
    have hT := cell3_of ht3
    have hTH := cell3_of hth3
    rw [nd_of hn] at hTH
    rw [hTH] at hT
    rw [hfh, atom_nd hD.base, hT] at hF
    simp only [CSt.sem, FormulaShapeX9, KidInputsNX9, RowOutputNX9, StateX9.toX, KidInputsNX,
      KidInputsX, RowOutputNX, List.map_cons, List.map_nil, rx9, strip9]
    refine ⟨⟨n, _, _, hF⟩, ?_, ?_⟩
    · simp only [hF, h0s, h0f, h1s, h1f, h1e, h2s, h2f, nd_of hlab, op10Axis, hd, tl,
        StrategyOfTraces.nounHead, StrategyOfTraces.nounTail, and_self]
    · simp only [hF, h0e, h2e, op10Axis, and_true, nd_of hE, nd_of hN]; exact hsl
  | s10S =>
    simp only [RowSemX09] at hsem
    simp only [kidsX9] at hk
    rcases ks with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, ks⟩⟩⟩ <;>
      simp only [List.map_nil, List.map_cons, List.cons.injEq, reduceCtorEq, and_false, false_and,
        List.nil_eq, List.cons_ne_nil, RowVSX9.trip, RowVSX.trip, Prod.mk.injEq, and_true] at hk
    obtain ⟨⟨h0s, h0f, h0e⟩, ⟨h1s, h1f, h1e⟩⟩ := hk
    obtain ⟨-, hsem⟩ := hsem
    obtain ⟨id, n, m, hV, hm, hfa, hmh, hlab, hcase⟩ := hsem (hf (by simp [CSt.sem, StateX9.isChain]))
    have hn : n ≠ 0 := hD.vpos id n hV
    simp only [CSt.sem, FormulaShapeX9, KidInputsNX9, RowOutputNX9, List.map_cons, List.map_nil,
      rx9]
    refine ⟨⟨_, nd_of hfa⟩, ?_, ?_⟩
    · refine kidInputsX9_s10S_of_seg hn hm (nd_of hfa) ?_ ?_ ?_
      · simp only [h0f, hmh, atom_nd hD.base]
      · simp only [h1f, nd_of hlab]
      · simp only [h0s]
    · rcases hcase with ⟨h1, hts, hte⟩ | ⟨S, E, X, Y, hS, hE, hX, hY, hsX, hsY⟩
      · refine ⟨by simp only [h0e], nd D b.s, nd D b.e, ?_, ?_, ?_, ?_⟩
        · simp only [h0f, hmh, atom_nd hD.base, chainAxis, h1]; exact slot_one _
        · simp only [h0f, hmh, atom_nd hD.base, chainAxis, h1]; exact slot_one _
        · simp only [h1s, hts]
        · simp only [h1e, hte]
      · refine ⟨by simp only [h0e], X, Y, ?_, ?_, ?_, ?_⟩
        · simp only [h0f, hmh, atom_nd hD.base, chainAxis, nd_of hS]; exact hsX
        · simp only [h0f, hmh, atom_nd hD.base, chainAxis, nd_of hE]; exact hsY
        · simp only [h1s, nd_of hX]
        · simp only [h1e, nd_of hY]

/-- **The per-row definedness step** at J-9 A. -/
theorem defined_stepX9 (hD : DenOKX9 p D V) {R : Registry} (r : RowVSX9)
    (hsem : RowSemX09 p D V R r) (ks : List RowVSX9) (hk : ks.map RowVSX9.trip = kidsX9 r)
    (hrole : ∀ i (hi : i < ks.length), (ks[i]'hi).cs.sem.isChain = chainPosX9 r.cs.sem i)
    (hs : D r.base.s ≠ none)
    (hch : ∀ k ∈ ks, k.cs.sem.isChain = false → D k.base.s ≠ none → D k.base.e ≠ none)
    (hf : r.cs.sem.isChain = true → D r.base.f ≠ none) :
    (∀ k ∈ ks, D k.base.s ≠ none) ∧ (r.cs.sem.isChain = false → D r.base.e ≠ none) := by
  obtain ⟨cs, b, lab⟩ := r
  cases cs with
  | old st =>
    simp only [RowSemX09] at hsem
    obtain ⟨hst, hsem⟩ := hsem
    have hk' : (ks.map toV).map RowVSX.trip = kidsX b := by
      rw [List.map_map]; exact hk
    have hrole' : ∀ i (hi : i < (ks.map toV).length),
        ((ks.map toV)[i]'hi).st.isChain = chainPosX b.st i := by
      intro i hi
      simp only [List.getElem_map, toV_isChain]
      rw [hrole i (by simpa using hi), hst]
      exact chainPosX9_ofX st i
    have hch' : ∀ k ∈ ks.map toV, k.st.isChain = false → D k.s ≠ none → D k.e ≠ none := by
      intro k hk0 hc
      obtain ⟨k, hk1, rfl⟩ := List.mem_map.mp hk0
      rw [toV_isChain] at hc
      exact hch k hk1 hc
    have L := defined_stepX hD.base b hsem (ks.map toV) hk' hrole' hs hch'
    refine ⟨fun k hk => L.1 (toV k) (List.mem_map_of_mem hk), fun hc => L.2 ?_⟩
    rw [hst, ← StateX9.isChain_ofX]; exact hc
  | s0B =>
    simp only [RowSemX09] at hsem
    simp only [kidsX9] at hk
    have hks : ks = [] := List.map_eq_nil_iff.mp hk
    subst hks
    obtain ⟨-, -, n, S, E, -, -, hE, -⟩ := hsem
    exact ⟨by simp, fun _ => ne_none_of hE⟩
  | s10B =>
    simp only [RowSemX09] at hsem
    simp only [kidsX9] at hk
    rcases ks with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, ks⟩⟩⟩⟩ <;>
      simp only [List.map_nil, List.map_cons, List.cons.injEq, reduceCtorEq, and_false, false_and,
        List.nil_eq, List.cons_ne_nil, RowVSX9.trip, RowVSX.trip, Prod.mk.injEq, and_true] at hk
    obtain ⟨⟨h0s, -, -⟩, ⟨h1s, -, h1e⟩, ⟨h2s, -, -⟩⟩ := hk
    obtain ⟨-, -, -, -, n, -, -, E, N, hE, -, -⟩ := hsem
    have e1 := hch k1 (by simp) (by simpa [chainPosX9, CSt.sem] using hrole 1 (by simp))
      (by rw [h1s]; exact hs)
    refine ⟨?_, fun _ => ne_none_of hE⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨h0s ▸ hs, h1s ▸ hs, h2s ▸ h1e ▸ e1⟩
  | s10S =>
    simp only [RowSemX09] at hsem
    simp only [kidsX9] at hk
    rcases ks with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, ks⟩⟩⟩ <;>
      simp only [List.map_nil, List.map_cons, List.cons.injEq, reduceCtorEq, and_false, false_and,
        List.nil_eq, List.cons_ne_nil, RowVSX9.trip, RowVSX.trip, Prod.mk.injEq, and_true] at hk
    obtain ⟨⟨h0s, -, -⟩, ⟨h1s, -, -⟩⟩ := hk
    obtain ⟨-, hsem⟩ := hsem
    obtain ⟨id, n, m, -, -, -, -, -, hcase⟩ := hsem (hf (by simp [CSt.sem, StateX9.isChain]))
    refine ⟨?_, fun h => absurd h (by simp [CSt.sem, StateX9.isChain])⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rcases hcase with ⟨-, hts, -⟩ | ⟨S, E, X, Y, -, -, hX, -⟩
    · exact ⟨h0s ▸ hs, h1s ▸ hts ▸ hs⟩
    · exact ⟨h0s ▸ hs, h1s ▸ ne_none_of hX⟩

/-- A real row's formula never denotes an atom. -/
theorem real_not_atom9 {R : Registry} {k : RowVSX9} (h : RowSemX09 p D V R k)
    (hr : k.cs.sem.isChain = false) (a : ℕ) : D k.base.f ≠ some (.atom a) := by
  obtain ⟨cs, b, lab⟩ := k
  cases cs with
  | old st =>
    simp only [RowSemX09] at h
    obtain ⟨hst, h⟩ := h
    simp only [CSt.sem, StateX9.isChain_ofX] at hr
    rw [← hst] at hr
    cases hs : b.st <;> simp only [RowSemX0, hs] at h <;> simp only [hs, StateX.isChain] at hr <;>
      first | exact absurd hr (by decide) | exact cell3_not_atom h.1 a
  | s0B => simp only [RowSemX09] at h; exact cell3_not_atom h.1 a
  | s10B => simp only [RowSemX09] at h; exact cell3_not_atom h.1 a
  | s10S => exact absurd hr (by simp [CSt.sem, StateX9.isChain])

/-- A chain row's formula handle is not a cell serial. -/
theorem chain_f_ne_one9 {R : Registry} {k : RowVSX9} (h : RowSemX09 p D V R k)
    (hc : k.cs.sem.isChain = true) : k.base.f.1 ≠ 1 := by
  obtain ⟨cs, b, lab⟩ := k
  cases cs with
  | old st =>
    simp only [RowSemX09] at h
    obtain ⟨hst, h⟩ := h
    simp only [CSt.sem, StateX9.isChain_ofX] at hc
    rw [← hst] at hc
    cases hs : b.st <;> simp only [RowSemX0, hs] at h <;> simp only [hs, StateX.isChain] at hc <;>
      first
      | exact absurd hc (by decide)
      | (obtain ⟨a, hf, -⟩ := h; rw [hf]; simp)
      | simp_all
  | s0B => exact absurd hc (by simp [CSt.sem, StateX9.isChain])
  | s10B => exact absurd hc (by simp [CSt.sem, StateX9.isChain])
  | s10S => simp only [RowSemX09] at h; exact h.1

/-- At a chain position the child's formula handle denotes an atom (the row's own formula denoting,
when the row is itself a chain row). -/
theorem chainPos_atom9 (hD : DenOKX9 p D V) {R : Registry} {r : RowVSX9} (h : RowSemX09 p D V R r)
    (hf : r.cs.sem.isChain = true → D r.base.f ≠ none)
    (i : ℕ) (hi : i < (kidsX9 r).length) (hc : chainPosX9 r.cs.sem i = true) :
    ∃ a, D ((kidsX9 r)[i]'hi).2.1 = some (.atom a) := by
  obtain ⟨cs, b, lab⟩ := r
  cases cs with
  | old st =>
    simp only [RowSemX09] at h
    obtain ⟨hst, h⟩ := h
    simp only [CSt.sem, chainPosX9_ofX] at hc
    rw [← hst] at hc
    have hi' : i < (kidsX b).length := by simpa [kidsX9] using hi
    have h0 := chainPos_kind h i hi' hc
    have e : ((kidsX9 ⟨.old st, b, lab⟩)[i]'hi).2.1 = ((kidsX b)[i]'hi').2.1 := rfl
    refine ⟨((kidsX b)[i]'hi').2.1.2, ?_⟩
    rw [e, show ((kidsX b)[i]'hi').2.1 = (0, ((kidsX b)[i]'hi').2.1.2) from Prod.ext h0 rfl]
    exact hD.base.atom _
  | s0B => simp [kidsX9] at hi
  | s10B =>
    simp only [RowSemX09] at h
    obtain ⟨-, -, -, -, n, -, hlab, -⟩ := h
    rcases i with _ | _ | _ | i <;> simp [CSt.sem, chainPosX9] at hc
    exact ⟨n, hlab⟩
  | s10S =>
    simp only [RowSemX09] at h
    obtain ⟨id, n, m, -, -, -, hmh, hlab, -⟩ := h.2 (hf (by simp [CSt.sem, StateX9.isChain]))
    rcases i with _ | _ | i
    · refine ⟨segRd n m, ?_⟩
      simp only [kidsX9, List.getElem_cons_zero, hmh]; exact hD.base.atom _
    · exact ⟨_, hlab⟩
    · simp [kidsX9] at hi

/-- **The roles**: child `i` is a chain row iff `i` is a chain position. -/
theorem roles9_of (hD : DenOKX9 p D V) {R : Registry} {r : RowVSX9} (h : RowSemX09 p D V R r)
    (hf : r.cs.sem.isChain = true → D r.base.f ≠ none)
    (hkk : KidKinds9 r) (ks : List RowVSX9) (hk : ks.map RowVSX9.trip = kidsX9 r)
    (hks : ∀ k ∈ ks, RowSemX09 p D V R k) :
    ∀ i (hi : i < ks.length), (ks[i]'hi).cs.sem.isChain = chainPosX9 r.cs.sem i := by
  intro i hi
  have hlen : ks.length = (kidsX9 r).length := by rw [← hk, List.length_map]
  have hi' : i < (kidsX9 r).length := hlen ▸ hi
  have hfi : (ks[i]'hi).base.f = ((kidsX9 r)[i]'hi').2.1 := by
    have := congrArg (fun l => l[i]?) hk
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
      Option.map_some, Option.some.injEq] at this
    rw [← this]; rfl
  have hki := hks _ (List.getElem_mem hi)
  cases hpos : chainPosX9 r.cs.sem i
  · have h1 := hkk i hi' hpos
    rw [← hfi] at h1
    cases h' : (ks[i]'hi).cs.sem.isChain
    · rfl
    · exact absurd h1 (chain_f_ne_one9 hki h')
  · obtain ⟨a, ha⟩ := chainPos_atom9 hD h hf i hi' hpos
    rw [← hfi] at ha
    cases h' : (ks[i]'hi).cs.sem.isChain
    · exact absurd ha (real_not_atom9 hki h' a)
    · rfl

/-- Chain kids' formulas denote. -/
theorem kidsF_defined9 (hD : DenOKX9 p D V) {R : Registry} {r : RowVSX9} (h : RowSemX09 p D V R r)
    (hf : r.cs.sem.isChain = true → D r.base.f ≠ none)
    (ks : List RowVSX9) (hk : ks.map RowVSX9.trip = kidsX9 r)
    (hrole : ∀ i (hi : i < ks.length), (ks[i]'hi).cs.sem.isChain = chainPosX9 r.cs.sem i) :
    ∀ k ∈ ks, k.cs.sem.isChain = true → D k.base.f ≠ none := by
  intro k hk' hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk'
  have hlen : ks.length = (kidsX9 r).length := by rw [← hk, List.length_map]
  have hi' : i < (kidsX9 r).length := hlen ▸ hi
  have hfi : (ks[i]'hi).base.f = ((kidsX9 r)[i]'hi').2.1 := by
    have := congrArg (fun l => l[i]?) hk
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
      Option.map_some, Option.some.injEq] at this
    rw [← this]; rfl
  obtain ⟨a, ha⟩ := chainPos_atom9 hD h hf i hi' (by rw [← hrole i hi, hc])
  rw [hfi, ha]; simp

end Local

/-! ## 4. The tree -/

section Tree
variable {p : ℕ} {D : HX → Option Noun} {V : ℕ → Option ℕ} {R : Registry} {L : Type}
  (rw : L → RowVSX9)

/-- **The tree hypotheses at J-9 A**: every node satisfies `RowSemX9`, and its children carry
exactly its `kidsX9` labels. -/
structure RowsOKX9 (p : ℕ) (D : HX → Option Noun) (V : ℕ → Option ℕ) (R : Registry) (t : NTree L) :
    Prop where
  sem : ∀ u, InTree t u → RowSemX9 p D V R (rw u.label)
  link : ∀ u, InTree t u → u.children.map (fun c => (rw c.label).trip) = kidsX9 (rw u.label)

theorem RowsOKX9.sub {t : NTree L} (h : RowsOKX9 rw p D V R t) {c : NTree L} (hc : c ∈ t.children) :
    RowsOKX9 rw p D V R c :=
  ⟨fun u hu => h.sem u (InTree.sub hc hu), fun u hu => h.link u (InTree.sub hc hu)⟩

theorem RowsOKX9.kids {t : NTree L} (h : RowsOKX9 rw p D V R t) {u : NTree L} (hu : InTree t u) :
    (u.children.map fun c => rw c.label).map RowVSX9.trip = kidsX9 (rw u.label) := by
  rw [List.map_map]; exact h.link u hu

theorem RowsOKX9.kidSem {t : NTree L} (h : RowsOKX9 rw p D V R t) {u : NTree L} (hu : InTree t u) :
    ∀ k ∈ u.children.map (fun c => rw c.label), RowSemX09 p D V R k := by
  intro k hk
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
  exact (h.sem c (inTree_trans hu (InTree.sub hc (InTree.here _)))).1

theorem RowsOKX9.roles (hD : DenOKX9 p D V) {t : NTree L} (h : RowsOKX9 rw p D V R t) {u : NTree L}
    (hu : InTree t u) (hf : (rw u.label).cs.sem.isChain = true → D (rw u.label).base.f ≠ none) :
    ∀ i (hi : i < (u.children.map fun c => rw c.label).length),
      ((u.children.map fun c => rw c.label)[i]'hi).cs.sem.isChain = chainPosX9 (rw u.label).cs.sem i :=
  roles9_of hD (h.sem u hu).1 hf (h.sem u hu).2 _ (h.kids rw hu) (h.kidSem rw hu)

/-- **Definedness** at J-9 A: from a denoting subject and a REAL root, every node's subject denotes,
every real node's result denotes and every chain node's formula denotes. -/
theorem defined_treeX9 (hD : DenOKX9 p D V) : ∀ t : NTree L, RowsOKX9 rw p D V R t →
    D (rw t.label).base.s ≠ none →
    ((rw t.label).cs.sem.isChain = true → D (rw t.label).base.f ≠ none) → ∀ u, InTree t u →
      D (rw u.label).base.s ≠ none ∧
        ((rw u.label).cs.sem.isChain = false → D (rw u.label).base.e ≠ none) ∧
        ((rw u.label).cs.sem.isChain = true → D (rw u.label).base.f ≠ none)
  | .node l cs, h, hs, hf => by
    have ih : ∀ c ∈ cs, D (rw c.label).base.s ≠ none →
        ((rw c.label).cs.sem.isChain = true → D (rw c.label).base.f ≠ none) → ∀ u, InTree c u →
        D (rw u.label).base.s ≠ none ∧
          ((rw u.label).cs.sem.isChain = false → D (rw u.label).base.e ≠ none) ∧
          ((rw u.label).cs.sem.isChain = true → D (rw u.label).base.f ≠ none) :=
      fun c hc => defined_treeX9 hD c (h.sub rw (by simpa [NTree.children] using hc))
    have hu0 : InTree (NTree.node l cs) (NTree.node l cs) := InTree.here _
    have hrole := h.roles rw hD hu0 hf
    have hkf := kidsF_defined9 hD (h.sem _ hu0).1 hf (cs.map fun c => rw c.label) (h.kids rw hu0) hrole
    have step := defined_stepX9 hD (rw l) (h.sem _ hu0).1 (cs.map fun c => rw c.label)
      (h.kids rw hu0) hrole hs (by
        intro k hk hc hks
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hk
        exact (ih c hc' hks (hkf _ (List.mem_map_of_mem hc')) c (InTree.here _)).2.1 hc) hf
    intro u hu
    cases hu with
    | here => exact ⟨hs, step.2, hf⟩
    | sub hc hu' =>
      exact ih _ hc (step.1 _ (List.mem_map_of_mem hc)) (hkf _ (List.mem_map_of_mem hc)) u hu'

/-- A tree whose every node meets `GenuineNX9`'s local clauses is `GenuineNX9`. -/
theorem genuine9_of_local (g : L → RowX9) : ∀ t : NTree L,
    (∀ u, InTree t u →
      FormulaShapeX9 (g u.label).state (g u.label).formula ∧
      KidInputsNX9 (g u.label).state (g u.label).subject (g u.label).formula
        (u.children.map fun c => g c.label) ∧
      RowOutputNX9 R (g u.label).state (g u.label).subject (g u.label).formula
        (u.children.map fun c => g c.label) (g u.label).evaluation ∧
      ∀ i (hi : i < u.children.length),
        (g (u.children[i]'hi).label).state.isChain = chainPosX9 (g u.label).state i) →
    GenuineNX9 R (mapT g t)
  | .node l cs, h => by
    obtain ⟨hsh, hin, hout, hrole⟩ := h _ (InTree.here _)
    simp only [NTree.label_node, NTree.children_node] at hsh hin hout hrole
    rw [show mapT g (NTree.node l cs) = NTree.node (g l) (cs.map (mapT g)) by simp [mapT]]
    refine GenuineNX9.node hsh ?_ ?_ ?_ ?_
    · simpa [List.map_map, Function.comp_def] using hin
    · simpa [List.map_map, Function.comp_def] using hout
    · intro i hi
      simp only [List.length_map] at hi
      simpa using hrole i hi
    · intro k hk
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
      exact genuine9_of_local g c (fun u hu => h u (InTree.sub (by simpa using hc) hu))

/-- **`GenuineNX9` of the decoded tree.** -/
theorem genuineNX9_of_rowsX9 (hD : DenOKX9 p D V) (t : NTree L) (h : RowsOKX9 rw p D V R t)
    (hs : D (rw t.label).base.s ≠ none) (hreal : (rw t.label).cs.sem.isChain = false) :
    GenuineNX9 R (mapT (fun l => rx9 D (rw l)) t) := by
  refine genuine9_of_local (fun l => rx9 D (rw l)) t (fun u hu => ?_)
  have hk := h.kids rw hu
  have hT := defined_treeX9 rw hD t h hs (fun hc => absurd (hreal ▸ hc) (by decide))
  have hdef : ∀ k ∈ u.children.map (fun c => rw c.label), k.cs.sem.isChain = false →
      D k.base.e ≠ none := by
    intro k hk' hc
    obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hk'
    exact (hT c (inTree_trans hu (InTree.sub hc' (InTree.here _)))).2.1 hc
  have hfu := (hT u hu).2.2
  have key := local_stepX9 hD (rw u.label) (h.sem u hu).1 _ hk (h.roles rw hD hu hfu) hdef hfu
  rw [List.map_map] at key
  refine ⟨key.1, key.2.1, key.2.2, fun i hi => ?_⟩
  have := h.roles rw hD hu hfu i (by simpa using hi)
  simpa [rx9] using this

/-- **Design S8 `holdsN_of_rowsVSX9`**: a twin row tree with `RowsOKX9`, a real root, and root handles
denoting the claim's nouns proves `HoldsN` of the claim, for a faithful registry. -/
theorem holdsN_of_rowsVSX9 (hR : R.Faithful) (hD : DenOKX9 p D V) (t : NTree L)
    (h : RowsOKX9 rw p D V R t) (hreal : (rw t.label).cs.sem.isChain = false) (x : P8PublicClaim)
    (hs : D (rw t.label).base.s = some x.subject) (hf : D (rw t.label).base.f = some x.formula)
    (he : D (rw t.label).base.e = some x.result) : HoldsN x := by
  have hG := genuineNX9_of_rowsX9 rw hD t h (by simp [hs]) hreal
  refine holdsN_of_genuineNX9 hR hG ?_ ?_ ?_ ?_ <;> simp [rx9, hreal, nd_of hs, nd_of hf, nd_of he]

end Tree

end Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9

open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9 in
#print axioms local_stepX9
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9 in
#print axioms defined_stepX9
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9 in
#print axioms roles9_of
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9 in
#print axioms defined_treeX9
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9 in
#print axioms genuineNX9_of_rowsX9
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9 in
#print axioms holdsN_of_rowsVSX9
