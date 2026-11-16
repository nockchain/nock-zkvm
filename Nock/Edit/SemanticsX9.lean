/-
  Nock/Edit/SemanticsX9.lean

  New, additive module:
  `Nock/Edit/SemanticsX.lean` is not edited.

  * `chainOK_comp`: the `ChainOK` twin of `NounSeg.slot_comp`.
-/
import Nock.Edit.SemanticsX
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.NounAx

namespace Nock.Edit

open Nock Nock.Walk Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputedWindow
open Nock.NockVMROM.Thm54.SVGenuineF
open Nock.FieldEmbedding

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- the sibling axis of a composed axis: `(c·2^t + q) xor 1 = c·2^t + (q xor 1)` for `q < 2^t`, `1 ≤ t`. -/
theorem xor_one_comp (c q t : ℕ) (ht : 1 ≤ t) (hq : q < 2 ^ t) :
    (c * 2 ^ t + q) ^^^ 1 = c * 2 ^ t + (q ^^^ 1) ∧ (q ^^^ 1) < 2 ^ t := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  have hp : 2 ^ (u + 1) = 2 * 2 ^ u := by ring
  have hM : c * 2 ^ (u + 1) = 2 * (c * 2 ^ u) := by rw [hp]; ring
  rw [hM, hp] at *
  rw [xor_one_eq, xor_one_eq]
  constructor
  · by_cases h : q % 2 = 0
    · have h' : (2 * (c * 2 ^ u) + q) % 2 = 0 := by omega
      rw [if_pos h, if_pos h']; omega
    · have h' : ¬ (2 * (c * 2 ^ u) + q) % 2 = 0 := by omega
      rw [if_neg h, if_neg h']; omega
  · by_cases h : q % 2 = 0
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

/-- **`chainOK_comp`** (the `ChainOK` twin of `NounSeg.slot_comp`): a segment chain `a` on `s ⇝ e` whose
slots `X = /[a s]`, `Y = /[a e]` carry the rest `2^m + r` composes to the axis `a·2^m + r`. -/
theorem chainOK_comp {a m r : ℕ} {s e X Y : Noun} (ha : 1 ≤ a) (hr : r < 2 ^ m)
    (hc : ChainOK a s e) (hs : Noun.slot a s = some X) (he : Noun.slot a e = some Y)
    (hX : ChainOK (2 ^ m + r) X Y) : ChainOK (a * 2 ^ m + r) s e := by
  intro j hj
  have hm0 : 0 < 2 ^ m := Nat.two_pow_pos m
  rcases Nat.lt_or_ge j m with hjm | hjm
  · -- levels inside the segment
    obtain ⟨t, rfl⟩ : ∃ t, m = j + t := ⟨m - j, by omega⟩
    have ht : 1 ≤ t := by omega
    have hpj : 0 < 2 ^ j := Nat.two_pow_pos j
    have hsplit : 2 ^ (j + t) = 2 ^ j * 2 ^ t := pow_add _ _ _
    have hq : r / 2 ^ j < 2 ^ t := by
      rw [Nat.div_lt_iff_lt_mul hpj]; rw [hsplit] at hr; rwa [mul_comm] at hr
    have d1 : (a * 2 ^ (j + t) + r) / 2 ^ j = a * 2 ^ t + r / 2 ^ j := by
      rw [hsplit, show a * (2 ^ j * 2 ^ t) + r = 2 ^ j * (a * 2 ^ t) + r by ring,
        Nat.mul_add_div hpj]
    have d2 : (2 ^ (j + t) + r) / 2 ^ j = 2 ^ t + r / 2 ^ j := by
      rw [hsplit, show 2 ^ j * 2 ^ t + r = 2 ^ j * 2 ^ t + r from rfl, Nat.mul_add_div hpj]
    rw [d1] at hj ⊢
    have h2t : 2 ≤ 2 ^ t := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
    have hX' := hX j (by rw [d2]; exact le_trans h2t (Nat.le_add_right _ _))
    rw [d2] at hX'
    obtain ⟨x, hx1, hx2⟩ := hX'
    obtain ⟨e1, hlt⟩ := xor_one_comp 1 (r / 2 ^ j) t ht hq
    obtain ⟨e2, -⟩ := xor_one_comp a (r / 2 ^ j) t ht hq
    rw [one_mul] at e1
    rw [e1] at hx1 hx2
    refine ⟨x, ?_, ?_⟩
    · rw [e2, Nock.J9A.NounComp.slot_comp a t _ s ha hlt, hs]; exact hx1
    · rw [e2, Nock.J9A.NounComp.slot_comp a t _ e ha hlt, he]; exact hx2
  · -- levels above the segment: the outer chain
    obtain ⟨i, rfl⟩ : ∃ i, j = m + i := ⟨j - m, by omega⟩
    have d : (a * 2 ^ m + r) / 2 ^ (m + i) = a / 2 ^ i := by
      rw [pow_add, ← Nat.div_div_eq_div_mul, show a * 2 ^ m + r = 2 ^ m * a + r by ring,
        Nat.mul_add_div hm0, Nat.div_eq_of_lt hr, add_zero]
    rw [d] at hj ⊢
    exact hc i hj

/-! ## §A  The extended state set -/

/-- The extended compute states (SPEC §2.1): `OP_0 … OP_9`, `cons`, then the edit states
`s10 / s10L / s10T` and the hint states `s11s / s11d / s11j`. -/
inductive StateX9
  | s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | cons
  | s10 | s10L | s10T | s11s | s11d | s11j
  | s10S
deriving DecidableEq, Repr

namespace StateX9

/-- The released ISA's states inside the extended one. -/
def ofState : State → StateX9
  | .s0 => s0 | .s1 => s1 | .s2 => s2 | .s3 => s3 | .s4 => s4 | .s5 => s5
  | .s6 => s6 | .s7 => s7 | .s8 => s8 | .s9 => s9 | .cons => cons

theorem ofState_injective : Function.Injective ofState := by
  intro a b h; cases a <;> cases b <;> first | rfl | cases h

/-- The chain pseudo-states (atom formula; not an `evalFBy` call). -/
def isChain : StateX9 → Bool
  | s10L | s10T | s10S => true
  | _ => false

theorem isChain_ofState (st : State) : (ofState st).isChain = false := by
  cases st <;> rfl

/-- The E-0 states inside the J-9 A ones. -/
def ofX : StateX → StateX9
  | .s0 => s0 | .s1 => s1 | .s2 => s2 | .s3 => s3 | .s4 => s4 | .s5 => s5
  | .s6 => s6 | .s7 => s7 | .s8 => s8 | .s9 => s9 | .cons => cons
  | .s10 => s10 | .s10L => s10L | .s10T => s10T | .s11s => s11s | .s11d => s11d | .s11j => s11j

/-- The collapse back to E-0 (`s10S`, a chain state, goes to the chain state `s10L`; every consumer of
the collapse reads only `isChain` and the label, never the state itself). -/
def toX : StateX9 → StateX
  | s0 => .s0 | s1 => .s1 | s2 => .s2 | s3 => .s3 | s4 => .s4 | s5 => .s5
  | s6 => .s6 | s7 => .s7 | s8 => .s8 | s9 => .s9 | cons => .cons
  | s10 => .s10 | s10L => .s10L | s10T => .s10T | s11s => .s11s | s11d => .s11d | s11j => .s11j
  | s10S => .s10L

theorem toX_ofX (st : StateX) : toX (ofX st) = st := by cases st <;> rfl

theorem isChain_toX (st : StateX9) : (toX st).isChain = st.isChain := by cases st <;> rfl

theorem isChain_ofX (st : StateX) : (ofX st).isChain = st.isChain := by cases st <;> rfl

end StateX9

/-- Which child positions of a row are chain positions: the chain root of `s10` (position 2)
and the next level of `s10L` (position 0); every other child is a real `evalFBy` call. -/
def chainPosX9 : StateX9 → ℕ → Bool
  | .s10, 2 => true
  | .s10L, 0 => true
  | .s10S, 0 => true
  | .s10S, 1 => true
  | _, _ => false

/-! ## §B  Rows and field genuineness at the extended ISA -/

/-- A compute row's label at the extended ISA. -/
structure RowX9 where
  state : StateX9
  subject : Noun
  formula : Noun
  evaluation : Noun
deriving DecidableEq, Repr

/-- The formula shape of a row (`ComputedWindow.FormulaShape` on the released states). -/
def FormulaShapeX9 : StateX9 → Noun → Prop
  | .s0, f => FormulaShape .s0 f
  | .s1, f => FormulaShape .s1 f
  | .s2, f => FormulaShape .s2 f
  | .s3, f => FormulaShape .s3 f
  | .s4, f => FormulaShape .s4 f
  | .s5, f => FormulaShape .s5 f
  | .s6, f => FormulaShape .s6 f
  | .s7, f => FormulaShape .s7 f
  | .s8, f => FormulaShape .s8 f
  | .s9, f => FormulaShape .s9 f
  | .cons, f => FormulaShape .cons f
  | .s10, f => ∃ ax : ℕ, ∃ c d, f = .cell (.atom 10) (.cell (.cell (.atom ax) c) d)
  | .s10L, f => ∃ ax : ℕ, f = .atom ax ∧ 2 ≤ ax
  | .s10T, f => f = .atom 1
  | .s11s, f => ∃ b : ℕ, ∃ body, f = .cell (.atom 11) (.cell (.atom b) body)
  | .s11d, f => ∃ b clue body, f = .cell (.atom 11) (.cell (.cell b clue) body)
  | .s11j, f => ∃ b clue body, f = .cell (.atom 11) (.cell (.cell b clue) body)
  | .s10S, f => ∃ ax : ℕ, f = .atom ax

/-- The children's inputs (`ComputedWindow.KidInputs` on the released states, same child
order).  `s10`: kids `(s, c, new)`, `(s, d, old)` and the chain root `(old, a, ·)`; `s10L`:
the next level `(old, a/2, ·)`; `s11s`: the body; `s11d`: the clue, then the body. -/
def KidInputsX9 : StateX9 → Noun → Noun → List RowX9 → Prop
  | .s0, _, _, ks => ks = []
  | .s1, _, _, ks => ks = []
  | .cons, s, f, [k0, k1] =>
      k0.subject = s ∧ k0.formula = hd f ∧ k1.subject = s ∧ k1.formula = tl f
  | .s3, s, f, [k0] => k0.subject = s ∧ k0.formula = tl f
  | .s4, s, f, [k0] => k0.subject = s ∧ k0.formula = tl f
  | .s5, s, f, [k0, k1] =>
      k0.subject = s ∧ k0.formula = hd (tl f) ∧ k1.subject = s ∧ k1.formula = tl (tl f)
  | .s2, s, f, [k0, k1, k2] =>
      k0.subject = s ∧ k0.formula = hd (tl f) ∧ k1.subject = s ∧ k1.formula = tl (tl f) ∧
        k2.subject = k0.evaluation ∧ k2.formula = k1.evaluation
  | .s6, s, f, [kT, kC] =>
      kC.subject = s ∧ kC.formula = hd (tl f) ∧ kT.subject = s ∧
        kT.formula = (if condBit kC.evaluation = 0 then hd (tl (tl f)) else tl (tl (tl f)))
  | .s7, s, f, [kM, kH] =>
      kH.subject = s ∧ kH.formula = hd (tl f) ∧ kM.subject = kH.evaluation ∧
        kM.formula = tl (tl f)
  | .s8, s, f, [kM, kH] =>
      kH.subject = s ∧ kH.formula = hd (tl f) ∧ kM.subject = .cell kH.evaluation s ∧
        kM.formula = tl (tl f)
  | .s9, s, f, [kC, kI] =>
      kC.subject = s ∧ kC.formula = tl (tl f) ∧ kI.subject = kC.evaluation ∧
        Noun.slot (op9Axis f) kC.evaluation = some kI.formula
  | .s10, s, f, [kN, kO, kE] =>
      kN.subject = s ∧ kN.formula = tl (hd (tl f)) ∧ kO.subject = s ∧
        kO.formula = tl (tl f) ∧ kE.subject = kO.evaluation ∧ kE.formula = .atom (op10Axis f)
  | .s10L, s, f, [k] => k.subject = s ∧ k.formula = .atom (chainAxis f / 2)
  | .s10T, _, _, ks => ks = []
  | .s10S, s, f, [kL, kN] =>
      kL.subject = s ∧ ∃ m r : ℕ, r < 2 ^ m ∧ 1 ≤ chainAxis kL.formula ∧
        chainAxis f = chainAxis kL.formula * 2 ^ m + r ∧ chainAxis kN.formula = 2 ^ m + r
  | .s11s, s, f, [k] => k.subject = s ∧ k.formula = tl (tl f)
  | .s11d, s, f, [kD, kB] =>
      kD.subject = s ∧ kD.formula = tl (hd (tl f)) ∧ kB.subject = s ∧ kB.formula = tl (tl f)
  | _, _, _, _ => False

/-- The row's evaluation as its opcode's FIELD output (`SVGenuineF.RowOutputF` on the released
states).  `s10`: `slot a e = new` and the chain root ends at `e`; `s10L`: the sibling of `a_k`
agrees between `old` and `e`, and the next level ends at `e`; `s10T`: nothing; `s11s`/`s11d`:
`e` is the body's evaluation (the clue's evaluation is never read — its EXISTENCE is the clue's
definedness). -/
def RowOutputFX9 (q : ℕ) : StateX9 → Noun → Noun → List RowX9 → Noun → Prop
  | .s0, s, f, _, e => Noun.slot (op0Axis f) s = some e
  | .s1, _, f, _, e => e = tl f
  | .cons, _, _, [k0, k1], e => e = .cell k0.evaluation k1.evaluation
  | .s3, _, _, [k0], e => e = Noun.wut k0.evaluation
  | .s4, _, _, [k0], e => lusFBy q k0.evaluation = some e
  | .s5, _, _, [k0, k1], e => e = Noun.tis k0.evaluation k1.evaluation
  | .s2, _, _, [_, _, k2], e => e = k2.evaluation
  | .s6, _, _, [kT, kC], e =>
      (kC.evaluation = .atom 0 ∨ kC.evaluation = .atom 1) ∧ e = kT.evaluation
  | .s7, _, _, [kM, _], e => e = kM.evaluation
  | .s8, _, _, [kM, _], e => e = kM.evaluation
  | .s9, _, _, [_, kI], e => e = kI.evaluation
  | .s10, _, f, [kN, _, kE], e =>
      Noun.slot (op10Axis f) e = some kN.evaluation ∧ kE.evaluation = e
  | .s10L, s, f, [k], e =>
      k.evaluation = e ∧
        ∃ x, Noun.slot (chainAxis f ^^^ 1) s = some x ∧ Noun.slot (chainAxis f ^^^ 1) e = some x
  | .s10T, _, _, [], _ => True
  | .s10S, s, _, [kL, kN], e =>
      kL.evaluation = e ∧ ∃ X Y, Noun.slot (chainAxis kL.formula) s = some X ∧
        Noun.slot (chainAxis kL.formula) e = some Y ∧ kN.subject = X ∧ kN.evaluation = Y
  | .s11s, _, _, [k], e => e = k.evaluation
  | .s11d, _, _, [_, kB], e => e = kB.evaluation
  | _, _, _, _, _ => False

/-- **A field-genuine tree at the extended ISA**: every row obeys its step, and the chain
positions are exactly `chainPosX9`'s. -/
inductive GenuineSkelFX9 (q : ℕ) : NTree RowX9 → Prop
  | node {s : RowX9} {kids : List (NTree RowX9)}
      (shape : FormulaShapeX9 s.state s.formula)
      (inputs : KidInputsX9 s.state s.subject s.formula (kids.map NTree.label))
      (output : RowOutputFX9 q s.state s.subject s.formula (kids.map NTree.label) s.evaluation)
      (roles : ∀ i (h : i < kids.length), (kids[i]'h).label.state.isChain = chainPosX9 s.state i)
      (children : ∀ k ∈ kids, GenuineSkelFX9 q k) :
      GenuineSkelFX9 q (.node s kids)


/-! ## §D  A field-genuine extended tree is a successful `evalFBy` run -/

/-- What a genuine node proves: a chain node its `ChainOK`, a real node its `evalFBy` run. -/
def SemX9 (q : ℕ) (st : StateX9) (n : ℕ) (s f e : Noun) : Prop :=
  if st.isChain then ChainOK (chainAxis f) s e ∧ ∃ a : ℕ, f = .atom a
  else evalFBy q n s f = some e

theorem genuineFX9_root {q : ℕ} {T : NTree RowX9} (hT : GenuineSkelFX9 q T) :
    FormulaShapeX9 T.label.state T.label.formula ∧
      KidInputsX9 T.label.state T.label.subject T.label.formula (T.children.map NTree.label) ∧
      RowOutputFX9 q T.label.state T.label.subject T.label.formula (T.children.map NTree.label)
        T.label.evaluation := by
  cases hT with
  | node shape inputs output _ _ => exact ⟨shape, inputs, output⟩

theorem genuineFX9_child {q : ℕ} {T k : NTree RowX9} (hT : GenuineSkelFX9 q T)
    (hk : k ∈ T.children) : GenuineSkelFX9 q k := by
  cases hT with
  | node _ _ _ _ children => exact children k hk

private theorem semX9_real {q : ℕ} {st : StateX9} {n : ℕ} {s f e : Noun}
    (hst : st.isChain = false) (h : SemX9 q st n s f e) : evalFBy q n s f = some e := by
  simpa [SemX9, hst] using h

private theorem semX9_chain {q : ℕ} {st : StateX9} {n : ℕ} {s f e : Noun}
    (hst : st.isChain = true) (h : SemX9 q st n s f e) : ChainOK (chainAxis f) s e := by
  simp only [SemX9, hst, if_true] at h; exact h.1

theorem genuineFX9_sem {q : ℕ} {T : NTree RowX9} (hT : GenuineSkelFX9 q T) :
    SemX9 q T.label.state T.size T.label.subject T.label.formula T.label.evaluation := by
  induction hT with
  | @node s kids shape inputs output roles children ih =>
    obtain ⟨m, hm, hkm⟩ : ∃ m, (NTree.node s kids).size = m + 1 ∧ ∀ k ∈ kids, k.size ≤ m := by
      refine ⟨(NTree.node s kids).size - 1, ?_, fun k hk => ?_⟩
      · have := size_pos (NTree.node s kids); omega
      · have := size_child_lt (row := s) hk; omega
    have run : ∀ k ∈ kids, k.label.state.isChain = false →
        evalFBy q m k.label.subject k.label.formula = some k.label.evaluation :=
      fun k hk hc => GlobalOpcodeScheduling.evalFBy_mono (hkm k hk) (semX9_real hc (ih k hk))
    have chain : ∀ k ∈ kids, k.label.state.isChain = true →
        ChainOK (chainAxis k.label.formula) k.label.subject k.label.evaluation :=
      fun k hk hc => semX9_chain hc (ih k hk)
    rw [hm]
    simp only [NTree.label]
    cases hst : s.state with
    | s0 =>
      rw [hst] at shape inputs output
      obtain ⟨ax, hf⟩ := shape
      simp only [RowOutputFX9, hf, op0Axis] at output
      simp only [SemX9, StateX9.isChain]
      rw [hf]; simpa [evalFBy] using output
    | s1 =>
      rw [hst] at shape inputs output
      obtain ⟨t, hf⟩ := shape
      simp only [RowOutputFX9, hf, tl, StrategyOfTraces.nounTail] at output
      simp only [SemX9, StateX9.isChain]
      rw [hf, output]; simp [evalFBy]
    | cons =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, d, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsX9] at inputs
      obtain ⟨hs0, hf0, hs1, hf1⟩ := inputs
      simp only [RowOutputFX9, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp) (roles 0 (by simp))
      have r1 := run k1 (by simp) (roles 1 (by simp))
      rw [hs0, hf0, hf] at r0
      rw [hs1, hf1, hf] at r1
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at r0 r1
      simp only [SemX9, StateX9.isChain]
      rw [hf, output]; simp [evalFBy, r0, r1]
    | s3 =>
      rw [hst] at shape inputs output roles
      obtain ⟨t, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, rest⟩⟩ <;> simp only [List.map, KidInputsX9] at inputs
      obtain ⟨hs0, hf0⟩ := inputs
      simp only [RowOutputFX9, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp) (roles 0 (by simp))
      rw [hs0, hf0, hf] at r0
      simp only [tl, StrategyOfTraces.nounTail] at r0
      simp only [SemX9, StateX9.isChain]
      rw [hf, output]; simp [evalFBy, r0]
    | s4 =>
      rw [hst] at shape inputs output roles
      obtain ⟨t, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, rest⟩⟩ <;> simp only [List.map, KidInputsX9] at inputs
      obtain ⟨hs0, hf0⟩ := inputs
      simp only [RowOutputFX9, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp) (roles 0 (by simp))
      rw [hs0, hf0, hf] at r0
      simp only [tl, StrategyOfTraces.nounTail] at r0
      simp only [SemX9, StateX9.isChain]
      rw [hf]; simp [evalFBy, r0, output]
    | s5 =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsX9] at inputs
      obtain ⟨hs0, hf0, hs1, hf1⟩ := inputs
      simp only [RowOutputFX9, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp) (roles 0 (by simp))
      have r1 := run k1 (by simp) (roles 1 (by simp))
      rw [hs0, hf0, hf] at r0
      rw [hs1, hf1, hf] at r1
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at r0 r1
      simp only [SemX9, StateX9.isChain]
      rw [hf, output]; simp [evalFBy, r0, r1]
    | s2 =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, rest⟩⟩⟩⟩ <;>
        simp only [List.map, KidInputsX9] at inputs
      obtain ⟨hs0, hf0, hs1, hf1, hs2, hf2⟩ := inputs
      simp only [RowOutputFX9, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp) (roles 0 (by simp))
      have r1 := run k1 (by simp) (roles 1 (by simp))
      have r2 := run k2 (by simp) (roles 2 (by simp))
      rw [hs0, hf0, hf] at r0
      rw [hs1, hf1, hf] at r1
      rw [hs2, hf2] at r2
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at r0 r1
      simp only [SemX9, StateX9.isChain]
      rw [hf, output]; simp [evalFBy, r0, r1, r2]
    | s6 =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, d, hf⟩ := shape
      rcases kids with _ | ⟨kT, _ | ⟨kC, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsX9] at inputs
      obtain ⟨hsC, hfC, hsT, hfT⟩ := inputs
      simp only [RowOutputFX9, List.map_cons, List.map_nil] at output
      obtain ⟨hb, he⟩ := output
      have rC := run kC (by simp) (roles 1 (by simp))
      have rT := run kT (by simp) (roles 0 (by simp))
      rw [hsC, hfC, hf] at rC
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rC
      rw [hsT, hfT, hf] at rT
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rT
      simp only [SemX9, StateX9.isChain]
      rw [hf, he]
      rcases hb with hb | hb
      · rw [hb] at rC rT; simp [condBit] at rT; simp [evalFBy, rC, rT]
      · rw [hb] at rC rT; simp [condBit] at rT; simp [evalFBy, rC, rT]
    | s7 =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, hf⟩ := shape
      rcases kids with _ | ⟨kM, _ | ⟨kH, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsX9] at inputs
      obtain ⟨hsH, hfH, hsM, hfM⟩ := inputs
      simp only [RowOutputFX9, List.map_cons, List.map_nil] at output
      have rH := run kH (by simp) (roles 1 (by simp))
      have rM := run kM (by simp) (roles 0 (by simp))
      rw [hsH, hfH, hf] at rH
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rH
      rw [hsM, hfM, hf] at rM
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rM
      simp only [SemX9, StateX9.isChain]
      rw [hf, output]; simp [evalFBy, rH, rM]
    | s8 =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, hf⟩ := shape
      rcases kids with _ | ⟨kM, _ | ⟨kH, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsX9] at inputs
      obtain ⟨hsH, hfH, hsM, hfM⟩ := inputs
      simp only [RowOutputFX9, List.map_cons, List.map_nil] at output
      have rH := run kH (by simp) (roles 1 (by simp))
      have rM := run kM (by simp) (roles 0 (by simp))
      rw [hsH, hfH, hf] at rH
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rH
      rw [hsM, hfM, hf] at rM
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rM
      simp only [SemX9, StateX9.isChain]
      rw [hf, output]; simp [evalFBy, rH, rM]
    | s9 =>
      rw [hst] at shape inputs output roles
      obtain ⟨ax, c, hf⟩ := shape
      rcases kids with _ | ⟨kC, _ | ⟨kI, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsX9] at inputs
      obtain ⟨hsC, hfC, hsI, hslot⟩ := inputs
      simp only [RowOutputFX9, List.map_cons, List.map_nil] at output
      have rC := run kC (by simp) (roles 0 (by simp))
      have rI := run kI (by simp) (roles 1 (by simp))
      rw [hsC, hfC, hf] at rC
      simp only [tl, StrategyOfTraces.nounTail] at rC
      rw [hsI] at rI
      rw [hf] at hslot
      simp only [op9Axis] at hslot
      simp only [SemX9, StateX9.isChain]
      rw [hf, output]; simp [evalFBy, rC, hslot, rI]
    | s10 =>
      rw [hst] at shape inputs output roles
      obtain ⟨ax, c, d, hf⟩ := shape
      rcases kids with _ | ⟨kN, _ | ⟨kO, _ | ⟨kE, _ | ⟨k3, rest⟩⟩⟩⟩ <;>
        simp only [List.map, KidInputsX9] at inputs
      obtain ⟨hsN, hfN, hsO, hfO, hsE, hfE⟩ := inputs
      simp only [RowOutputFX9, List.map_cons, List.map_nil] at output
      obtain ⟨hslot, hE⟩ := output
      have rN := run kN (by simp) (roles 0 (by simp))
      have rO := run kO (by simp) (roles 1 (by simp))
      have cE := chain kE (by simp) (roles 2 (by simp))
      rw [hsN, hfN, hf] at rN
      rw [hsO, hfO, hf] at rO
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rN rO
      rw [hfE, hsE, hE, hf] at cE
      simp only [chainAxis, op10Axis] at cE
      rw [hf] at hslot
      simp only [op10Axis] at hslot
      have hed := edit_of_slots cE hslot
      simp only [SemX9, StateX9.isChain]
      rw [hf]; simp [evalFBy, rN, rO, hed]
    | s10L =>
      rw [hst] at shape inputs output roles
      obtain ⟨ax, hf, hax⟩ := shape
      rcases kids with _ | ⟨k, _ | ⟨k1, rest⟩⟩ <;> simp only [List.map, KidInputsX9] at inputs
      obtain ⟨hsk, hfk⟩ := inputs
      simp only [RowOutputFX9, List.map_cons, List.map_nil] at output
      obtain ⟨hke, hsib⟩ := output
      have ck := chain k (by simp) (roles 0 (by simp))
      rw [hfk, hsk, hke, hf] at ck
      simp only [chainAxis] at ck hsib
      rw [hf] at hsib
      simp only [chainAxis] at hsib
      simp only [SemX9, StateX9.isChain, if_true, hf, chainAxis]
      exact ⟨chainOK_step hax hsib ck, ax, rfl⟩
    | s10T =>
      rw [hst] at shape
      rw [shape]
      simp only [SemX9, StateX9.isChain, if_true, chainAxis]
      exact ⟨chainOK_of_lt_two (by norm_num) _ _, 1, rfl⟩
    | s11s =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, body, hf⟩ := shape
      rcases kids with _ | ⟨k, _ | ⟨k1, rest⟩⟩ <;> simp only [List.map, KidInputsX9] at inputs
      obtain ⟨hsk, hfk⟩ := inputs
      simp only [RowOutputFX9, List.map_cons, List.map_nil] at output
      have rk := run k (by simp) (roles 0 (by simp))
      rw [hsk, hfk, hf] at rk
      simp only [tl, StrategyOfTraces.nounTail] at rk
      simp only [SemX9, StateX9.isChain]
      rw [hf, output]; simp [evalFBy, rk]
    | s11d =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, clue, body, hf⟩ := shape
      rcases kids with _ | ⟨kD, _ | ⟨kB, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsX9] at inputs
      obtain ⟨hsD, hfD, hsB, hfB⟩ := inputs
      simp only [RowOutputFX9, List.map_cons, List.map_nil] at output
      have rD := run kD (by simp) (roles 0 (by simp))
      have rB := run kB (by simp) (roles 1 (by simp))
      rw [hsD, hfD, hf] at rD
      rw [hsB, hfB, hf] at rB
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rD rB
      simp only [SemX9, StateX9.isChain]
      rw [hf, output]; simp [evalFBy, rD, rB]
    | s10S =>
      rw [hst] at shape inputs output roles
      obtain ⟨ax, hf⟩ := shape
      rcases kids with _ | ⟨kL, _ | ⟨kN, _ | ⟨k2, rest⟩⟩⟩ <;> simp only [List.map, KidInputsX9] at inputs
      obtain ⟨hsL, m, r, hr, hpos, hA, hAn⟩ := inputs
      simp only [RowOutputFX9, List.map_cons, List.map_nil] at output
      obtain ⟨hLe, X, Y, hX, hY, hNs, hNe⟩ := output
      have cL := chain kL (by simp) (roles 0 (by simp))
      have cN := chain kN (by simp) (roles 1 (by simp))
      rw [hsL, hLe] at cL
      rw [hAn, hNs, hNe] at cN
      simp only [hf, chainAxis] at hA
      simp only [SemX9, StateX9.isChain, if_true, hf, chainAxis]
      exact ⟨hA ▸ chainOK_comp hpos hr cL hX hY cN, ax, rfl⟩
    | s11j =>
      rw [hst] at inputs
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsX9] at inputs

/-- **Field genuineness is a successful field run** (twin of `SVGenuineF.genuineF_evalFBy`): a
field-genuine extended tree with a real root runs under `evalFBy q` at fuel `T.size`. -/
theorem genuineFX9_evalFBy {q : ℕ} {T : NTree RowX9} (hT : GenuineSkelFX9 q T)
    (hreal : T.label.state.isChain = false) :
    evalFBy q T.size T.label.subject T.label.formula = some T.label.evaluation :=
  semX9_real hreal (genuineFX9_sem hT)

/-- A chain node of a field-genuine extended tree satisfies `ChainOK` at its atom axis. -/
theorem genuineFX9_chainOK {q : ℕ} {T : NTree RowX9} (hT : GenuineSkelFX9 q T)
    (hchain : T.label.state.isChain = true) :
    ChainOK (chainAxis T.label.formula) T.label.subject T.label.evaluation :=
  semX9_chain hchain (genuineFX9_sem hT)

/-- **A field-genuine extended tree rooted at the claim proves the claim under `HoldsF`.** -/
theorem holdsF_of_genuineFX9 {q : ℕ} {T : NTree RowX9} (hT : GenuineSkelFX9 q T)
    (hreal : T.label.state.isChain = false) {x : P8PublicClaim}
    (hs : T.label.subject = x.subject) (hf : T.label.formula = x.formula)
    (he : T.label.evaluation = x.result) : HoldsF q x :=
  ⟨T.size, by rw [← hs, ← hf, ← he]; exact genuineFX9_evalFBy hT hreal⟩


/-- **The segment composition at `segAx`**: the limb-`m` segment `segRd n m` composes with the lower segments
`nxtAx n m` to `segAx n m` (`NounAx.segAx_decomp`, `chainOK_comp`). -/
theorem chainOK_segAx {n m : ℕ} (hn : n ≠ 0) (hm : m ≤ Nock.J9A.NounAx.top n)
    {s e X Y : Noun}
    (hc : ChainOK (Nock.J9A.NounAx.segRd n m) s e)
    (hs : Noun.slot (Nock.J9A.NounAx.segRd n m) s = some X)
    (he : Noun.slot (Nock.J9A.NounAx.segRd n m) e = some Y)
    (hX : ChainOK (Nock.J9A.NounAx.nxtAx n m) X Y) :
    ChainOK (Nock.J9A.NounAx.segAx n m) s e := by
  open Nock.J9A.NounAx in
  rw [segAx_decomp n m hm]
  exact chainOK_comp (segRd_pos hn m hm) (nxtAx_lt_pow n m) hc hs he hX

/-- the `s10S` kid-input clause at `segAx`: formulas `segAx n m` / `segRd n m` / `nxtAx n m`. -/
theorem kidInputsX9_s10S_of_seg {n m : ℕ} (hn : n ≠ 0)
    (hm : m ≤ Nock.J9A.NounAx.top n) {s f : Noun} {kL kN : RowX9}
    (hf : f = .atom (Nock.J9A.NounAx.segAx n m))
    (hL : kL.formula = .atom (Nock.J9A.NounAx.segRd n m))
    (hN : kN.formula = .atom (Nock.J9A.NounAx.nxtAx n m))
    (hs : kL.subject = s) : KidInputsX9 .s10S s f [kL, kN] := by
  open Nock.J9A.NounAx in
  refine ⟨hs, 32 * m, n % 2 ^ (32 * m), nxtAx_lt_pow n m, ?_, ?_, ?_⟩
  · simpa [hL, chainAxis] using segRd_pos hn m hm
  · simpa [hf, hL, chainAxis] using segAx_decomp n m hm
  · simp [hN, chainAxis, nxtAx]

end Nock.Edit

#print axioms Nock.Edit.chainOK_comp
#print axioms Nock.Edit.genuineFX9_sem
#print axioms Nock.Edit.holdsF_of_genuineFX9
#print axioms Nock.Edit.chainOK_segAx
#print axioms Nock.Edit.kidInputsX9_s10S_of_seg
