/-
  Nock/Edit/GenuineNX9.lean

Kids' labels enter the old-state
    clauses only through `strip9`.
  * **`genuineNX9_to`** — every `GenuineNX9` tree is a `GenuineNX` tree up to labels: an `s10S`
    node is REPLACED by an explicit `s10L … s10T` chain (`chainTree`) built from its `ChainOK`
    (`chainOK_comp` over the two kids), so no J-8 row semantics is transported onto `s10S`.
  * **`genuineNX9_holdsN` / `holdsN_of_genuineNX9`** — a real root proves `HoldsN` (through C-2's
    `genuineNX_holdsN` on the image tree), a chain node `ChainOK`.
-/
import Nock.Edit.GenuineNX
import Nock.Edit.SemanticsX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.Edit

open Nock Nock.Walk Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputedWindow
open Nock.Jet (Registry HoldsN JetSpec)

/-! ## §1 Labels without states -/

/-- A row label with its state forgotten (set to `.s0`). -/
def strip (k : RowX) : RowX := ⟨.s0, k.subject, k.formula, k.evaluation⟩

/-- A J-9 A row label as a J-8 label with its state forgotten. -/
def strip9 (k : RowX9) : RowX := ⟨.s0, k.subject, k.formula, k.evaluation⟩

theorem kidInputsX_strip (st : StateX) (s f : Noun) (ks : List RowX) :
    KidInputsX st s f ks ↔ KidInputsX st s f (ks.map strip) := by
  rcases ks with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> cases st <;>
    simp [KidInputsX, strip]

theorem kidInputsNX_strip (st : StateX) (s f : Noun) (ks : List RowX) :
    KidInputsNX st s f ks ↔ KidInputsNX st s f (ks.map strip) := by
  rcases ks with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> cases st <;>
    simp [KidInputsNX, KidInputsX, strip]

theorem rowOutputNX_strip (R : Registry) (st : StateX) (s f : Noun) (ks : List RowX) (e : Noun) :
    RowOutputNX R st s f ks e ↔ RowOutputNX R st s f (ks.map strip) e := by
  rcases ks with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> cases st <;>
    simp [RowOutputNX, strip]

theorem strip_strip (k : RowX) : strip (strip k) = strip k := rfl

/-! ## §2 The row specs at the J-9 A ISA -/


def KidInputsNX9 : StateX9 → Noun → Noun → List RowX9 → Prop
  | .s10S, s, f, ks => KidInputsX9 .s10S s f ks
  | st, s, f, ks => KidInputsNX st.toX s f (ks.map strip9)

/-- `RowOutputNX` on the old states; on `s10S`: the segment chain `kL` ends at `e`, and the next
segment `kN` runs from `/[seg s]` to `/[seg e]` (`seg := chainAxis kL.formula`). -/
def RowOutputNX9 (R : Registry) : StateX9 → Noun → Noun → List RowX9 → Noun → Prop
  | .s10S, s, _, [kL, kN], e =>
      kL.evaluation = e ∧ ∃ X Y, Noun.slot (chainAxis kL.formula) s = some X ∧
        Noun.slot (chainAxis kL.formula) e = some Y ∧ kN.subject = X ∧ kN.evaluation = Y
  | .s10S, _, _, _, _ => False
  | st, s, f, ks, e => RowOutputNX R st.toX s f (ks.map strip9) e

/-- **A genuine ℕ tree at the J-9 A ISA.** -/
inductive GenuineNX9 (R : Registry) : NTree RowX9 → Prop
  | node {s : RowX9} {kids : List (NTree RowX9)}
      (shape : FormulaShapeX9 s.state s.formula)
      (inputs : KidInputsNX9 s.state s.subject s.formula (kids.map NTree.label))
      (output : RowOutputNX9 R s.state s.subject s.formula (kids.map NTree.label) s.evaluation)
      (roles : ∀ i (h : i < kids.length), (kids[i]'h).label.state.isChain = chainPosX9 s.state i)
      (children : ∀ k ∈ kids, GenuineNX9 R k) :
      GenuineNX9 R (.node s kids)

/-! ## §3 The chain tree of a `ChainOK` -/

/-- **An explicit `s10L … s10T` chain** realising `ChainOK a s e` (`1 ≤ a`). -/
theorem chainTree (R : Registry) : ∀ (a : ℕ) {s e : Noun}, 1 ≤ a → ChainOK a s e →
    ∃ T : NTree RowX, GenuineNX R T ∧ T.label.subject = s ∧ T.label.formula = .atom a ∧
      T.label.evaluation = e ∧ T.label.state.isChain = true
  | a, s, e, ha, hc => by
    rcases Nat.lt_or_ge a 2 with h2 | h2
    · have h1 : a = 1 := by omega
      subst h1
      refine ⟨.node ⟨.s10T, s, .atom 1, e⟩ [], ?_, rfl, rfl, rfl, rfl⟩
      refine GenuineNX.node rfl (by simp [KidInputsNX, KidInputsX]) (by simp [RowOutputNX])
        (fun i h => absurd h (by simp)) (fun k hk => absurd hk (by simp))
    · have hlt : a / 2 < a := Nat.div_lt_self (by omega) (by norm_num)
      obtain ⟨T, hT, hs, hf, he, hch⟩ := chainTree R (a / 2) (by omega) (chainOK_half hc)
      refine ⟨.node ⟨.s10L, s, .atom a, e⟩ [T], ?_, rfl, rfl, rfl, rfl⟩
      have hsib := hc 0 (by simpa using h2)
      simp only [pow_zero, Nat.div_one] at hsib
      refine GenuineNX.node ⟨a, rfl, h2⟩ ?_ ?_ ?_ ?_
      · simp [KidInputsNX, KidInputsX, hs, hf, chainAxis]
      · simpa [RowOutputNX, he, chainAxis] using hsib
      · intro i h
        have hi : i = 0 := by simpa using h
        subst hi; simpa [chainPosX] using hch
      · intro k hk
        simp only [List.mem_singleton] at hk; subst hk; exact hT
  termination_by a => a
  decreasing_by omega

/-! ## §4 Every `GenuineNX9` tree is a `GenuineNX` tree up to labels -/

theorem chainPosX9_old (st : StateX9) (hst : st ≠ .s10S) (i : ℕ) :
    chainPosX9 st i = chainPosX st.toX i := by
  rcases i with _ | _ | _ | i <;> cases st <;> first | rfl | exact absurd rfl hst

theorem formulaShape_old (st : StateX9) (hst : st ≠ .s10S) (f : Noun) :
    FormulaShapeX9 st f ↔ FormulaShapeX st.toX f := by
  cases st <;> first | exact Iff.rfl | exact absurd rfl hst

/-- Choice over a list of kids. -/
theorem list_choice {α β : Type} (P : α → β → Prop) :
    ∀ (l : List α), (∀ a ∈ l, ∃ b, P a b) → ∃ l' : List β, List.Forall₂ P l l'
  | [], _ => ⟨[], .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (List.mem_cons_self ..)
    obtain ⟨l', hl'⟩ := list_choice P l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨b :: l', .cons hb hl'⟩

/-- What the image of a node keeps. -/
def Keeps (T : NTree RowX9) (T' : NTree RowX) : Prop :=
  strip T'.label = strip9 T.label ∧ T'.label.state.isChain = T.label.state.isChain

theorem forall2_map_strip {l : List (NTree RowX9)} {l' : List (NTree RowX)}
    (h : List.Forall₂ (fun T T' => Keeps T T') l l') :
    (l'.map NTree.label).map strip = (l.map NTree.label).map strip9 := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.map_cons, hab.1, ih]

theorem forall2_getElem {α β : Type} {P : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ P l l') : ∀ i (hi : i < l.length) (hi' : i < l'.length), P (l[i]'hi) (l'[i]'hi') := by
  induction h with
  | nil => intro i hi; simp at hi
  | cons hab _ ih =>
    intro i hi hi'
    rcases i with _ | i
    · exact hab
    · exact ih i (by simpa using hi) (by simpa using hi')

/-- **The image theorem**: a genuine J-9 A tree maps to a genuine J-8 tree with the same
`(subject, formula, evaluation)` and the same chain-ness at the root.  Old-state nodes keep their
state; an `s10S` node becomes the explicit chain `chainTree` of its composed `ChainOK`. -/
theorem genuineNX9_to {R : Registry} (hR : R.Faithful) :
    ∀ T : NTree RowX9, GenuineNX9 R T → ∃ T' : NTree RowX, GenuineNX R T' ∧ Keeps T T'
  | .node s kids, .node shape inputs output roles children => by
    have hk : ∀ k ∈ kids, ∃ k', GenuineNX R k' ∧ Keeps k k' := fun k hk' =>
      genuineNX9_to hR k (children k hk')
    obtain ⟨kids', hF⟩ := list_choice (fun k k' => GenuineNX R k' ∧ Keeps k k') kids hk
    have hlen : kids'.length = kids.length := hF.length_eq.symm
    have hK : List.Forall₂ (fun T T' => Keeps T T') kids kids' := hF.imp (fun _ _ h => h.2)
    have hmap := forall2_map_strip hK
    have hgen : ∀ k' ∈ kids', GenuineNX R k' := by
      intro k' hk'
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk'
      exact (forall2_getElem hF i (hlen ▸ hi) hi).1
    have hch : ∀ i (hi : i < kids'.length), (kids'[i]'hi).label.state.isChain =
        (kids[i]'(hlen ▸ hi)).label.state.isChain := fun i hi =>
      (forall2_getElem hF i (hlen ▸ hi) hi).2.2
    by_cases hst : s.state = .s10S
    · -- the segment node: compose the two kids' chains, then rebuild as an explicit chain
      obtain ⟨st, sb, f, e⟩ := s
      simp only at hst; subst hst
      rcases kids with _ | ⟨kL, _ | ⟨kN, _ | ⟨k3, l⟩⟩⟩
      · simp [KidInputsNX9, KidInputsX9] at inputs
      · simp [KidInputsNX9, KidInputsX9] at inputs
      · rcases kids' with _ | ⟨kL', _ | ⟨kN', _ | ⟨_, _⟩⟩⟩
        · simp at hlen
        · simp at hlen
        · have hLg := hgen kL' (by simp)
          have hNg := hgen kN' (by simp)
          have hLc := hch 0 (by simp)
          have hNc := hch 1 (by simp)
          have r0 := roles 0 (by simp)
          have r1 := roles 1 (by simp)
          simp only [List.getElem_cons_zero, List.getElem_cons_succ, chainPosX9] at hLc hNc r0 r1
          simp only [List.map_cons, List.map_nil, List.cons.injEq, strip, strip9, RowX.mk.injEq,
            and_true, true_and] at hmap
          obtain ⟨⟨hLs, hLf, hLe⟩, hNs, hNf, hNe⟩ := hmap
          have cL := genuineNX_chainOK hR hLg (by rw [hLc, r0])
          have cN := genuineNX_chainOK hR hNg (by rw [hNc, r1])
          rw [hLs, hLf, hLe] at cL
          rw [hNs, hNf, hNe] at cN
          simp only [List.map_cons, List.map_nil, KidInputsNX9, KidInputsX9] at inputs
          obtain ⟨hks, m, r, hr, ha1, hax, hNax⟩ := inputs
          simp only [List.map_cons, List.map_nil, RowOutputNX9] at output
          obtain ⟨hke, X, Y, hX, hY, hkNs, hkNe⟩ := output
          obtain ⟨ax, hf⟩ := shape
          simp only at hf
          rw [hks, hke] at cL
          rw [hkNs, hkNe, hNax] at cN
          have hc := chainOK_comp ha1 hr cL hX hY cN
          rw [← hax] at hc
          have h1 : 1 ≤ chainAxis f := by
            rw [hax]; have := Nat.one_le_two_pow (n := m)
            nlinarith
          obtain ⟨T, hT, hTs, hTf, hTe, hTc⟩ := chainTree R (chainAxis f) h1 hc
          refine ⟨T, hT, ?_, ?_⟩
          · show strip T.label = _
            rw [show strip T.label = ⟨.s0, sb, .atom (chainAxis f), e⟩ by simp [strip, hTs, hTf, hTe]]
            simp [strip9, NTree.label, hf, chainAxis]
          · show T.label.state.isChain = StateX9.isChain .s10S
            rw [hTc]; rfl
        · simp at hlen
      · simp [KidInputsNX9, KidInputsX9] at inputs
    · -- an old-state node keeps its state
      refine ⟨.node ⟨s.state.toX, s.subject, s.formula, s.evaluation⟩ kids', ?_, rfl, ?_⟩
      · refine GenuineNX.node ((formulaShape_old _ hst _).mp shape) ?_ ?_ ?_ hgen
        · have hin : KidInputsNX s.state.toX s.subject s.formula ((kids.map NTree.label).map strip9) := by
            cases h : s.state <;> rw [h] at inputs <;> first | exact absurd h hst | exact inputs
          rw [kidInputsNX_strip, hmap]; exact hin
        · have hout : RowOutputNX R s.state.toX s.subject s.formula
              ((kids.map NTree.label).map strip9) s.evaluation := by
            cases h : s.state <;> rw [h] at output <;> first | exact absurd h hst | exact output
          rw [rowOutputNX_strip, hmap]; exact hout
        · intro i hi
          rw [hch i hi, roles i (hlen ▸ hi), chainPosX9_old _ hst]
      · exact StateX9.isChain_toX s.state

/-- **A genuine J-9 A tree with a real root proves `HoldsN`** of its root label. -/
theorem genuineNX9_holdsN {R : Registry} (hR : R.Faithful) {T : NTree RowX9} (hT : GenuineNX9 R T)
    (hreal : T.label.state.isChain = false) :
    HoldsN ⟨T.label.subject, T.label.formula, T.label.evaluation⟩ := by
  obtain ⟨T', hT', hk, hc⟩ := genuineNX9_to hR T hT
  have h := genuineNX_holdsN hR hT' (by rw [hc, hreal])
  simp only [strip, strip9, RowX.mk.injEq, true_and] at hk
  obtain ⟨hs, hf, he⟩ := hk
  rwa [hs, hf, he] at h

/-- A chain node of a genuine J-9 A tree satisfies `ChainOK` at its atom axis. -/
theorem genuineNX9_chainOK {R : Registry} (hR : R.Faithful) {T : NTree RowX9} (hT : GenuineNX9 R T)
    (hchain : T.label.state.isChain = true) :
    ChainOK (chainAxis T.label.formula) T.label.subject T.label.evaluation := by
  obtain ⟨T', hT', hk, hc⟩ := genuineNX9_to hR T hT
  have h := genuineNX_chainOK hR hT' (by rw [hc, hchain])
  simp only [strip, strip9, RowX.mk.injEq, true_and] at hk
  obtain ⟨hs, hf, he⟩ := hk
  rwa [hs, hf, he] at h

/-- **The claim from a genuine J-9 A tree** rooted at it. -/
theorem holdsN_of_genuineNX9 {R : Registry} (hR : R.Faithful) {T : NTree RowX9}
    (hT : GenuineNX9 R T) (hreal : T.label.state.isChain = false) {x : P8PublicClaim}
    (hs : T.label.subject = x.subject) (hf : T.label.formula = x.formula)
    (he : T.label.evaluation = x.result) : HoldsN x := by
  have := genuineNX9_holdsN hR hT hreal
  rw [hs, hf, he] at this; exact this

end Nock.Edit

#print axioms Nock.Edit.chainTree
#print axioms Nock.Edit.genuineNX9_to
#print axioms Nock.Edit.genuineNX9_holdsN
#print axioms Nock.Edit.genuineNX9_chainOK
#print axioms Nock.Edit.holdsN_of_genuineNX9
