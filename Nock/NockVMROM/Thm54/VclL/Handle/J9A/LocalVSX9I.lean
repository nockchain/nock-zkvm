/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/LocalVSX9I.lean

The J-9 B pipeline (`HokJ9G.acceptsJ9_holdsN_finalLG`) consumes the compute half in the implication form
  (`RecOKI` / `RowSemX0I`): the inc and jet providers are proved only as "IF the old handle / subject denotes,
  THEN …".  A J-9 A `finalLG` twin therefore needs the twin tree at the guarded semantics:

  * **`RowSemX09I p D V R r := (PreRow9 D r → RowSemX09 p D V R r) ∧ FShape9 D r`** — old states: RowSemIJ8's
    antecedent `PreRow` on the J-8 handles, and the unguarded state tag + formula shape; new states unguarded.
  * `sem_or` (an `s4` / `s5` / `s11j` row is a real cell-formula row), the role lemmas at the guarded semantics
    (`real_not_atom9I`, `chain_f_ne_one9I`, `chainPos_atom9I`, **`roles9_ofI`**, `kidsF_defined9I`),
    `preRow9_of_kids` (the antecedent from the children's results), **`defined_stepX9I`**.
  * Tree: `RowsOKX9I`, **`defined_treeX9I`**, **`rowsOKX9_of_I`** (every node's antecedent from the definedness;
    then `RowsOKX9`), **`holdsN_of_rowsVSX9I`**.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.LocalVSX9
import Nock.NockVMROM.Thm54.VclL.Handle.RowSemIJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9I

open Nock Nock.Walk Nock.Reified Nock.Edit
open Nock.NockVMROM.Thm54
open Nock.Jet (Registry HoldsN)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemIJ8 (PreRow FShape RowSemX0I preRow_triv preRow_of_kids)

/-! ## 1. The guarded row semantics -/

section Sem
variable (p : ℕ) (D : HX → Option Noun) (V : ℕ → Option ℕ)

/-- The antecedent of a twin row: RowSemIJ8's `PreRow` on an old row; nothing on a new row. -/
def PreRow9 (r : RowVSX9) : Prop :=
  match r.cs with
  | .old _ => PreRow D r.base
  | _ => True

/-- The unguarded part of an old row: its state tag and RowSemIJ8's formula shape. -/
def FShape9 (r : RowVSX9) : Prop :=
  match r.cs with
  | .old st => r.base.st = st ∧ FShape D r.base
  | _ => True

/-- **The guarded J-9 A row semantics.** -/
def RowSemX09I (R : Registry) (r : RowVSX9) : Prop := (PreRow9 D r → RowSemX09 p D V R r) ∧ FShape9 D r

def RowSemX9I (R : Registry) (r : RowVSX9) : Prop := RowSemX09I p D V R r ∧ KidKinds9 r

end Sem

/-! ## 2. Local lemmas -/

section Local
variable {p : ℕ} {D : HX → Option Noun} {V : ℕ → Option ℕ} {R : Registry}

/-- An `s4` / `s5` / `s11j` row (the only guarded states). -/
def Guarded (st : StateX) : Prop := st = .s4 ∨ st = .s5 ∨ st = .s11j

/-- **A guarded row is either unguarded, or an old `s4` / `s5` / `s11j` row with its cell formula.** -/
theorem sem_or {r : RowVSX9} (h : RowSemX09I p D V R r) :
    RowSemX09 p D V R r ∨ ∃ st, r.cs = .old st ∧ r.base.st = st ∧ Guarded st ∧
      Cell3 D r.base.f r.base.fh r.base.ft := by
  obtain ⟨cs, b, lab⟩ := r
  cases cs with
  | old st =>
    obtain ⟨hsem, hst, hsh⟩ := h
    by_cases hg : Guarded st
    · right
      refine ⟨st, rfl, hst, hg, ?_⟩
      simp only at hst
      rcases hg with rfl | rfl | rfl <;> simpa [FShape, hst] using hsh
    · left
      simp only [Guarded, not_or] at hg
      refine hsem ?_
      simp only [PreRow9]
      simp only at hst
      exact preRow_triv (hst ▸ hg.1) (hst ▸ hg.2.1) (hst ▸ hg.2.2)
  | s0B => exact Or.inl (h.1 trivial)
  | s10B => exact Or.inl (h.1 trivial)
  | s10S => exact Or.inl (h.1 trivial)

theorem guarded_not_chain {st : StateX} (hg : Guarded st) : (StateX9.ofX st).isChain = false := by
  rcases hg with rfl | rfl | rfl <;> rfl

theorem guarded_chainPos {st : StateX} (hg : Guarded st) (i : ℕ) : chainPosX9 (StateX9.ofX st) i = false := by
  rw [chainPosX9_ofX]
  rcases hg with rfl | rfl | rfl <;> rcases i with _ | _ | _ | i <;> rfl

theorem real_not_atom9I {k : RowVSX9} (h : RowSemX09I p D V R k)
    (hr : k.cs.sem.isChain = false) (a : ℕ) : D k.base.f ≠ some (.atom a) := by
  rcases sem_or h with h | ⟨st, -, -, -, hc⟩
  · exact real_not_atom9 h hr a
  · exact cell3_not_atom hc a

theorem chain_f_ne_one9I {k : RowVSX9} (h : RowSemX09I p D V R k)
    (hc : k.cs.sem.isChain = true) : k.base.f.1 ≠ 1 := by
  rcases sem_or h with h | ⟨st, hcs, -, hg, -⟩
  · exact chain_f_ne_one9 h hc
  · rw [hcs] at hc; simp only [CSt.sem, guarded_not_chain hg] at hc; exact absurd hc (by decide)

theorem chainPos_atom9I (hD : DenOKX9 p D V) {r : RowVSX9} (h : RowSemX09I p D V R r)
    (hf : r.cs.sem.isChain = true → D r.base.f ≠ none)
    (i : ℕ) (hi : i < (kidsX9 r).length) (hc : chainPosX9 r.cs.sem i = true) :
    ∃ a, D ((kidsX9 r)[i]'hi).2.1 = some (.atom a) := by
  rcases sem_or h with h | ⟨st, hcs, -, hg, -⟩
  · exact chainPos_atom9 hD h hf i hi hc
  · rw [hcs] at hc; simp only [CSt.sem, guarded_chainPos hg] at hc; exact absurd hc (by decide)

/-- **The roles at the guarded semantics.** -/
theorem roles9_ofI (hD : DenOKX9 p D V) {r : RowVSX9} (h : RowSemX09I p D V R r)
    (hf : r.cs.sem.isChain = true → D r.base.f ≠ none)
    (hkk : KidKinds9 r) (ks : List RowVSX9) (hk : ks.map RowVSX9.trip = kidsX9 r)
    (hks : ∀ k ∈ ks, RowSemX09I p D V R k) :
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
    · exact absurd h1 (chain_f_ne_one9I hki h')
  · obtain ⟨a, ha⟩ := chainPos_atom9I hD h hf i hi' hpos
    rw [← hfi] at ha
    cases h' : (ks[i]'hi).cs.sem.isChain
    · exact absurd ha (real_not_atom9I hki h' a)
    · rfl

theorem kidsF_defined9I (hD : DenOKX9 p D V) {r : RowVSX9} (h : RowSemX09I p D V R r)
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
  obtain ⟨a, ha⟩ := chainPos_atom9I hD h hf i hi' (by rw [← hrole i hi, hc])
  rw [hfi, ha]; simp

/-- **The antecedent from the children** (RowSemIJ8's `preRow_of_kids` through the `toV` view). -/
theorem preRow9_of_kids {r : RowVSX9} (hF : FShape9 D r) (ks : List RowVSX9)
    (hk : ks.map RowVSX9.trip = kidsX9 r)
    (hrole : ∀ i (hi : i < ks.length), (ks[i]'hi).cs.sem.isChain = chainPosX9 r.cs.sem i)
    (hs : D r.base.s ≠ none)
    (hch : ∀ k ∈ ks, k.cs.sem.isChain = false → D k.base.s ≠ none → D k.base.e ≠ none) :
    PreRow9 D r := by
  obtain ⟨cs, b, lab⟩ := r
  cases cs with
  | old st =>
    obtain ⟨hst, -⟩ := hF
    simp only at hst
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
    exact preRow_of_kids (ks.map toV) hk' hrole' hs hch'
  | s0B => trivial
  | s10B => trivial
  | s10S => trivial

/-- **`defined_stepX9` at the guarded semantics.** -/
theorem defined_stepX9I (hD : DenOKX9 p D V) (r : RowVSX9)
    (hsem : RowSemX09I p D V R r) (ks : List RowVSX9) (hk : ks.map RowVSX9.trip = kidsX9 r)
    (hrole : ∀ i (hi : i < ks.length), (ks[i]'hi).cs.sem.isChain = chainPosX9 r.cs.sem i)
    (hs : D r.base.s ≠ none)
    (hch : ∀ k ∈ ks, k.cs.sem.isChain = false → D k.base.s ≠ none → D k.base.e ≠ none)
    (hf : r.cs.sem.isChain = true → D r.base.f ≠ none) :
    (∀ k ∈ ks, D k.base.s ≠ none) ∧ (r.cs.sem.isChain = false → D r.base.e ≠ none) :=
  defined_stepX9 hD r (hsem.1 (preRow9_of_kids hsem.2 ks hk hrole hs hch)) ks hk hrole hs hch hf

end Local

/-! ## 3. The tree -/

section Tree
variable {p : ℕ} {D : HX → Option Noun} {V : ℕ → Option ℕ} {R : Registry} {L : Type}
  (rw : L → RowVSX9)

/-- **The tree hypotheses at the guarded semantics.** -/
structure RowsOKX9I (p : ℕ) (D : HX → Option Noun) (V : ℕ → Option ℕ) (R : Registry) (t : NTree L) :
    Prop where
  sem : ∀ u, InTree t u → RowSemX9I p D V R (rw u.label)
  link : ∀ u, InTree t u → u.children.map (fun c => (rw c.label).trip) = kidsX9 (rw u.label)

theorem RowsOKX9I.sub {t : NTree L} (h : RowsOKX9I rw p D V R t) {c : NTree L} (hc : c ∈ t.children) :
    RowsOKX9I rw p D V R c :=
  ⟨fun u hu => h.sem u (InTree.sub hc hu), fun u hu => h.link u (InTree.sub hc hu)⟩

theorem RowsOKX9I.kids {t : NTree L} (h : RowsOKX9I rw p D V R t) {u : NTree L} (hu : InTree t u) :
    (u.children.map fun c => rw c.label).map RowVSX9.trip = kidsX9 (rw u.label) := by
  rw [List.map_map]; exact h.link u hu

theorem RowsOKX9I.kidSem {t : NTree L} (h : RowsOKX9I rw p D V R t) {u : NTree L} (hu : InTree t u) :
    ∀ k ∈ u.children.map (fun c => rw c.label), RowSemX09I p D V R k := by
  intro k hk
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
  exact (h.sem c (inTree_trans hu (InTree.sub hc (InTree.here _)))).1

theorem RowsOKX9I.roles (hD : DenOKX9 p D V) {t : NTree L} (h : RowsOKX9I rw p D V R t) {u : NTree L}
    (hu : InTree t u) (hf : (rw u.label).cs.sem.isChain = true → D (rw u.label).base.f ≠ none) :
    ∀ i (hi : i < (u.children.map fun c => rw c.label).length),
      ((u.children.map fun c => rw c.label)[i]'hi).cs.sem.isChain = chainPosX9 (rw u.label).cs.sem i :=
  roles9_ofI hD (h.sem u hu).1 hf (h.sem u hu).2 _ (h.kids rw hu) (h.kidSem rw hu)

/-- **Definedness at the guarded semantics.** -/
theorem defined_treeX9I (hD : DenOKX9 p D V) : ∀ t : NTree L, RowsOKX9I rw p D V R t →
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
      fun c hc => defined_treeX9I hD c (h.sub rw (by simpa [NTree.children] using hc))
    have hu0 : InTree (NTree.node l cs) (NTree.node l cs) := InTree.here _
    have hrole := h.roles rw hD hu0 hf
    have hkf := kidsF_defined9I hD (h.sem _ hu0).1 hf (cs.map fun c => rw c.label) (h.kids rw hu0) hrole
    have step := defined_stepX9I hD (rw l) (h.sem _ hu0).1 (cs.map fun c => rw c.label)
      (h.kids rw hu0) hrole hs (by
        intro k hk hc hks
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hk
        exact (ih c hc' hks (hkf _ (List.mem_map_of_mem hc')) c (InTree.here _)).2.1 hc) hf
    intro u hu
    cases hu with
    | here => exact ⟨hs, step.2, hf⟩
    | sub hc hu' =>
      exact ih _ hc (step.1 _ (List.mem_map_of_mem hc)) (hkf _ (List.mem_map_of_mem hc)) u hu'

/-- **The guarded tree is a `RowsOKX9` tree** once the root subject denotes and the root is real: every
node's antecedent comes from its children's definedness. -/
theorem rowsOKX9_of_I (hD : DenOKX9 p D V) (t : NTree L) (h : RowsOKX9I rw p D V R t)
    (hs : D (rw t.label).base.s ≠ none) (hreal : (rw t.label).cs.sem.isChain = false) :
    RowsOKX9 rw p D V R t := by
  have hT := defined_treeX9I rw hD t h hs (fun hc => absurd (hreal ▸ hc) (by decide))
  refine ⟨fun u hu => ⟨(h.sem u hu).1.1 ?_, (h.sem u hu).2⟩, h.link⟩
  refine preRow9_of_kids (h.sem u hu).1.2 _ (h.kids rw hu) (h.roles rw hD hu (hT u hu).2.2) (hT u hu).1 ?_
  intro k hk hc _
  obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hk
  exact (hT c (inTree_trans hu (InTree.sub hc' (InTree.here _)))).2.1 hc

/-- **Design S8 at the guarded semantics**: `holdsN_of_rowsVSX9` from `RowsOKX9I`. -/
theorem holdsN_of_rowsVSX9I (hR : R.Faithful) (hD : DenOKX9 p D V) (t : NTree L)
    (h : RowsOKX9I rw p D V R t) (hreal : (rw t.label).cs.sem.isChain = false) (x : P8PublicClaim)
    (hs : D (rw t.label).base.s = some x.subject) (hf : D (rw t.label).base.f = some x.formula)
    (he : D (rw t.label).base.e = some x.result) : HoldsN x :=
  holdsN_of_rowsVSX9 rw hR hD t (rowsOKX9_of_I rw hD t h (by simp [hs]) hreal) hreal x hs hf he

end Tree

end Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9I

open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9I in
#print axioms roles9_ofI
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9I in
#print axioms defined_treeX9I
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9I in
#print axioms rowsOKX9_of_I
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9I in
#print axioms holdsN_of_rowsVSX9I
