/-
  Nock/Edit/SemanticsX.lean

  **Op 10 is a DECLARED EXTENSION beyond the paper's NockVMROM** (SPEC §1.0): the paper's
  `Def:Nock` defines `OP_10`, the compiled `NockVMROM` removes it.  Any capstone ranging over op-10 programs certifies
  "NockVMROM + edit".  Op 11 is not modelled by the paper; `evalN` / `evalFBy` already have it.

  * **§B `RowX`, `FormulaShapeX`, `KidInputsX`, `RowOutputFX`, `GenuineSkelFX`** — twins of
    `ComputedWindow.FormulaShape/KidInputs` and `SVGenuineF.RowOutputF/GenuineSkelF` with the
    SPEC §1.4 cases.  The chain pseudo-rows carry an ATOM formula; `GenuineSkelFX` carries a
    `roles` field fixing which child positions are chain positions (`chainPosX`: position 2 of
    `s10`, position 0 of `s10L`, nothing else), so a chain row can never stand in for a real
    child (the swapped-state probe of SPEC §8 E-6 at the semantics level).
  * **§C `ChainOK` and `edit_of_slots`** (SPEC §1.3): sibling agreement between `old` and `e`
    along the path plus `slot a e = new` IS `edit a new old = e`.  `edit_of_slots_depth` is the
    SPEC's literal `∀ k < depth(a)` form.
  * **§D `genuineFX_evalFBy`** — a field-genuine extended tree with a real (non-chain) root is
    a successful `evalFBy q` run at fuel `T.size`; chain nodes yield `ChainOK`
    (`genuineFX_chainOK`).  `holdsF_of_genuineFX` closes to `HoldsF`.

  Paper: the paper (Nock), `:1071` (OP_10), `:1531-1534` (field increment).
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1511Thm54SVGenuineF

namespace Nock.Edit

open Nock Nock.Walk Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputedWindow
open Nock.NockVMROM.Thm54.SVGenuineF
open Nock.FieldEmbedding

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## §A  The extended state set -/

/-- The extended compute states (SPEC §2.1): `OP_0 … OP_9`, `cons`, then the edit states
`s10 / s10L / s10T` and the hint states `s11s / s11d / s11j`. -/
inductive StateX
  | s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | cons
  | s10 | s10L | s10T | s11s | s11d | s11j
deriving DecidableEq, Repr

namespace StateX

/-- The released ISA's states inside the extended one. -/
def ofState : State → StateX
  | .s0 => s0 | .s1 => s1 | .s2 => s2 | .s3 => s3 | .s4 => s4 | .s5 => s5
  | .s6 => s6 | .s7 => s7 | .s8 => s8 | .s9 => s9 | .cons => cons

theorem ofState_injective : Function.Injective ofState := by
  intro a b h; cases a <;> cases b <;> first | rfl | cases h

/-- The chain pseudo-states (atom formula; not an `evalFBy` call). -/
def isChain : StateX → Bool
  | s10L | s10T => true
  | _ => false

theorem isChain_ofState (st : State) : (ofState st).isChain = false := by
  cases st <;> rfl

end StateX

/-- Which child positions of a row are chain positions: the chain root of `s10` (position 2)
and the next level of `s10L` (position 0); every other child is a real `evalFBy` call. -/
def chainPosX : StateX → ℕ → Bool
  | .s10, 2 => true
  | .s10L, 0 => true
  | _, _ => false

/-! ## §B  Rows and field genuineness at the extended ISA -/

/-- A compute row's label at the extended ISA. -/
structure RowX where
  state : StateX
  subject : Noun
  formula : Noun
  evaluation : Noun
deriving DecidableEq, Repr

/-- Axis of an OP10 formula `[10 [[ax c] d]]` (`0` off-shape). -/
def op10Axis : Noun → ℕ
  | .cell _ (.cell (.cell (.atom ax) _) _) => ax
  | _ => 0

/-- Axis of a chain pseudo-row's ATOM formula (`0` on a cell). -/
def chainAxis : Noun → ℕ
  | .atom a => a
  | _ => 0

/-- The formula shape of a row (`ComputedWindow.FormulaShape` on the released states). -/
def FormulaShapeX : StateX → Noun → Prop
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

/-- The children's inputs (`ComputedWindow.KidInputs` on the released states, same child
order).  `s10`: kids `(s, c, new)`, `(s, d, old)` and the chain root `(old, a, ·)`; `s10L`:
the next level `(old, a/2, ·)`; `s11s`: the body; `s11d`: the clue, then the body. -/
def KidInputsX : StateX → Noun → Noun → List RowX → Prop
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
  | .s11s, s, f, [k] => k.subject = s ∧ k.formula = tl (tl f)
  | .s11d, s, f, [kD, kB] =>
      kD.subject = s ∧ kD.formula = tl (hd (tl f)) ∧ kB.subject = s ∧ kB.formula = tl (tl f)
  | _, _, _, _ => False

/-- The row's evaluation as its opcode's FIELD output (`SVGenuineF.RowOutputF` on the released
states).  `s10`: `slot a e = new` and the chain root ends at `e`; `s10L`: the sibling of `a_k`
agrees between `old` and `e`, and the next level ends at `e`; `s10T`: nothing; `s11s`/`s11d`:
`e` is the body's evaluation (the clue's evaluation is never read — its EXISTENCE is the clue's
definedness). -/
def RowOutputFX (q : ℕ) : StateX → Noun → Noun → List RowX → Noun → Prop
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
  | .s11s, _, _, [k], e => e = k.evaluation
  | .s11d, _, _, [_, kB], e => e = kB.evaluation
  | _, _, _, _, _ => False

/-- **A field-genuine tree at the extended ISA**: every row obeys its step, and the chain
positions are exactly `chainPosX`'s. -/
inductive GenuineSkelFX (q : ℕ) : NTree RowX → Prop
  | node {s : RowX} {kids : List (NTree RowX)}
      (shape : FormulaShapeX s.state s.formula)
      (inputs : KidInputsX s.state s.subject s.formula (kids.map NTree.label))
      (output : RowOutputFX q s.state s.subject s.formula (kids.map NTree.label) s.evaluation)
      (roles : ∀ i (h : i < kids.length), (kids[i]'h).label.state.isChain = chainPosX s.state i)
      (children : ∀ k ∈ kids, GenuineSkelFX q k) :
      GenuineSkelFX q (.node s kids)

/-! ## §C  `ChainOK` and `edit_of_slots` -/

/-- **The chain invariant** (SPEC §1.4): at every level `a_j = a / 2^j ≥ 2` of the path to `a`,
the sibling `a_j xor 1` is defined in `old` and agrees in `e`. -/
def ChainOK (a : ℕ) (old e : Noun) : Prop :=
  ∀ j, 2 ≤ a / 2 ^ j →
    ∃ x, Noun.slot ((a / 2 ^ j) ^^^ 1) old = some x ∧ Noun.slot ((a / 2 ^ j) ^^^ 1) e = some x

/-- `a xor 1` is `Noun.edit`'s sibling axis. -/
theorem xor_one_eq (a : ℕ) : a ^^^ 1 = if a % 2 = 0 then a + 1 else a - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rcases Nat.even_or_odd' a with ⟨k, rfl | rfl⟩
  · have h0 : (2 * k) % 2 = 0 := by omega
    rw [if_pos h0]
    cases i with
    | zero => simp [Nat.testBit_xor, Nat.testBit_zero]
    | succ i =>
      rw [Nat.testBit_xor, show 2 * k + 1 = 1 + 2 * k by omega, Nat.testBit_succ,
        Nat.testBit_succ, Nat.testBit_succ]
      simp [Nat.mul_add_div, Nat.add_mul_div_left]
  · have h1 : ¬ (2 * k + 1) % 2 = 0 := by omega
    rw [if_neg h1, show 2 * k + 1 - 1 = 2 * k by omega]
    cases i with
    | zero => simp [Nat.testBit_xor, Nat.testBit_zero]
    | succ i =>
      rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      simp [Nat.mul_add_div, Nat.add_mul_div_left]

/-- One `slot` step: below the root, axis `a` reads the `a % 2` side of axis `a / 2`. -/
theorem slot_some_iff {a : ℕ} (ha : 2 ≤ a) (n v : Noun) :
    Noun.slot a n = some v ↔
      ∃ l r, Noun.slot (a / 2) n = some (.cell l r) ∧ v = (if a % 2 = 0 then l else r) := by
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 := ⟨a - 2, by omega⟩
  simp only [Noun.slot]
  cases hs : Noun.slot ((m + 2) / 2) n with
  | none => simp
  | some w =>
    cases w with
    | atom _ => simp
    | cell l r =>
      constructor
      · intro h
        refine ⟨l, r, rfl, ?_⟩
        have := Option.some.inj h
        by_cases hm : (m + 2) % 2 = 0 <;> simp_all
      · rintro ⟨l', r', h, hv⟩
        cases h
        by_cases hm : (m + 2) % 2 = 0 <;> simp_all

/-- The chain invariant one level up. -/
theorem chainOK_half {a : ℕ} {old e : Noun} (h : ChainOK a old e) : ChainOK (a / 2) old e := by
  intro j hj
  have hpow : a / 2 / 2 ^ j = a / 2 ^ (j + 1) := by
    rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
  rw [hpow] at hj ⊢
  exact h (j + 1) hj

/-- A level step: the sibling at `a` plus the invariant one level up. -/
theorem chainOK_step {a : ℕ} {old e : Noun} (_ha : 2 ≤ a)
    (hsib : ∃ x, Noun.slot (a ^^^ 1) old = some x ∧ Noun.slot (a ^^^ 1) e = some x)
    (hup : ChainOK (a / 2) old e) : ChainOK a old e := by
  intro j hj
  cases j with
  | zero => simpa using hsib
  | succ j =>
    have hpow : a / 2 ^ (j + 1) = a / 2 / 2 ^ j := by
      rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
    rw [hpow] at hj ⊢
    exact hup j hj

/-- The terminal: nothing to check at axis `1` (and vacuously at `0`). -/
theorem chainOK_of_lt_two {a : ℕ} (ha : a < 2) (old e : Noun) : ChainOK a old e := by
  intro j hj
  exfalso
  have : a / 2 ^ j ≤ a := Nat.div_le_self _ _
  omega

/-- **`edit_of_slots`** (SPEC §1.3): if every off-spine sibling along the path to `a` is the
same noun in `old` and `e`, and `e` holds `new` at `a`, then `e` IS `#[a new old]`. -/
theorem edit_of_slots {a : ℕ} {new old e : Noun} (hchain : ChainOK a old e)
    (hnew : Noun.slot a e = some new) : Noun.edit a new old = some e := by
  induction a using Nat.strong_induction_on generalizing new with
  | _ a ih =>
    rcases Nat.lt_or_ge a 2 with ha | ha
    · interval_cases a
      · simp [Noun.slot] at hnew
      · simp only [Noun.slot] at hnew
        obtain rfl := Option.some.inj hnew
        simp [Noun.edit]
    · obtain ⟨x, hxo, hxe⟩ := hchain 0 (by simpa using ha)
      simp only [pow_zero, Nat.div_one] at hxo hxe
      rw [xor_one_eq] at hxo hxe
      obtain ⟨l, r, hpar, hv⟩ := (slot_some_iff ha e new).1 hnew
      have hsib2 : 2 ≤ (if a % 2 = 0 then a + 1 else a - 1) := by split <;> omega
      obtain ⟨l', r', hpar', hv'⟩ := (slot_some_iff hsib2 e x).1 hxe
      have hdiv : (if a % 2 = 0 then a + 1 else a - 1) / 2 = a / 2 := by split <;> omega
      rw [hdiv, hpar] at hpar'
      obtain ⟨rfl, rfl⟩ : l = l' ∧ r = r' := by
        have := Option.some.inj hpar'; cases this; exact ⟨rfl, rfl⟩
      -- the paired noun is the parent cell of `e`
      have hpaired : (if a % 2 = 0 then Noun.cell new x else Noun.cell x new) = .cell l r := by
        by_cases hm : a % 2 = 0
        · have hm' : ¬ (a + 1) % 2 = 0 := by omega
          simp only [hm, if_true, hm', if_false] at hv hv' ⊢
          rw [hv, hv']
        · have hm' : (a - 1) % 2 = 0 := by omega
          simp only [hm, if_false, hm', if_true] at hv hv' ⊢
          rw [hv, hv']
      have hrec : Noun.edit (a / 2) (if a % 2 = 0 then Noun.cell new x else Noun.cell x new) old
          = some e := by
        rw [hpaired]
        exact ih (a / 2) (by omega) (chainOK_half hchain) hpar
      obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 := ⟨a - 2, by omega⟩
      simp only [Noun.edit]
      have hsibB : (if ((m + 2) % 2 == 0) = true then m + 2 + 1 else m + 2 - 1)
          = (if (m + 2) % 2 = 0 then m + 2 + 1 else m + 2 - 1) := by
        by_cases hm : (m + 2) % 2 = 0 <;> simp [hm]
      rw [hsibB, hxo]
      simp only
      by_cases hm : (m + 2) % 2 = 0
      · simp only [hm, beq_self_eq_true, if_true] at hrec ⊢; exact hrec
      · have hb : ((m + 2) % 2 == 0) = false := by simpa using hm
        simp only [hm, hb, if_false] at hrec ⊢; exact hrec

/-- `edit_of_slots` in the SPEC's literal form: `∀ k < depth(a)` with `a_k = a / 2^k`,
`sib_k = a_k xor 1`, `depth(a) = ⌊log₂ a⌋`. -/
theorem edit_of_slots_depth {a : ℕ} {new old e : Noun}
    (hsib : ∀ k < Nat.log 2 a, ∃ x, Noun.slot ((a / 2 ^ k) ^^^ 1) old = some x ∧
      Noun.slot ((a / 2 ^ k) ^^^ 1) e = some x)
    (hnew : Noun.slot a e = some new) : Noun.edit a new old = some e := by
  refine edit_of_slots (fun j hj => hsib j ?_) hnew
  have h2 : 2 ^ (j + 1) ≤ a := by
    have := (Nat.le_div_iff_mul_le (Nat.pow_pos (n := j) (by norm_num : 0 < 2))).1 hj
    rw [pow_succ]; linarith
  exact Nat.lt_of_succ_le (Nat.le_log_of_pow_le (by norm_num) h2)

/-! ## §D  A field-genuine extended tree is a successful `evalFBy` run -/

/-- What a genuine node proves: a chain node its `ChainOK`, a real node its `evalFBy` run. -/
def SemX (q : ℕ) (st : StateX) (n : ℕ) (s f e : Noun) : Prop :=
  if st.isChain then ChainOK (chainAxis f) s e ∧ ∃ a : ℕ, f = .atom a
  else evalFBy q n s f = some e

theorem genuineFX_root {q : ℕ} {T : NTree RowX} (hT : GenuineSkelFX q T) :
    FormulaShapeX T.label.state T.label.formula ∧
      KidInputsX T.label.state T.label.subject T.label.formula (T.children.map NTree.label) ∧
      RowOutputFX q T.label.state T.label.subject T.label.formula (T.children.map NTree.label)
        T.label.evaluation := by
  cases hT with
  | node shape inputs output _ _ => exact ⟨shape, inputs, output⟩

theorem genuineFX_child {q : ℕ} {T k : NTree RowX} (hT : GenuineSkelFX q T)
    (hk : k ∈ T.children) : GenuineSkelFX q k := by
  cases hT with
  | node _ _ _ _ children => exact children k hk

private theorem semX_real {q : ℕ} {st : StateX} {n : ℕ} {s f e : Noun}
    (hst : st.isChain = false) (h : SemX q st n s f e) : evalFBy q n s f = some e := by
  simpa [SemX, hst] using h

private theorem semX_chain {q : ℕ} {st : StateX} {n : ℕ} {s f e : Noun}
    (hst : st.isChain = true) (h : SemX q st n s f e) : ChainOK (chainAxis f) s e := by
  simp only [SemX, hst, if_true] at h; exact h.1

theorem genuineFX_sem {q : ℕ} {T : NTree RowX} (hT : GenuineSkelFX q T) :
    SemX q T.label.state T.size T.label.subject T.label.formula T.label.evaluation := by
  induction hT with
  | @node s kids shape inputs output roles children ih =>
    obtain ⟨m, hm, hkm⟩ : ∃ m, (NTree.node s kids).size = m + 1 ∧ ∀ k ∈ kids, k.size ≤ m := by
      refine ⟨(NTree.node s kids).size - 1, ?_, fun k hk => ?_⟩
      · have := size_pos (NTree.node s kids); omega
      · have := size_child_lt (row := s) hk; omega
    have run : ∀ k ∈ kids, k.label.state.isChain = false →
        evalFBy q m k.label.subject k.label.formula = some k.label.evaluation :=
      fun k hk hc => GlobalOpcodeScheduling.evalFBy_mono (hkm k hk) (semX_real hc (ih k hk))
    have chain : ∀ k ∈ kids, k.label.state.isChain = true →
        ChainOK (chainAxis k.label.formula) k.label.subject k.label.evaluation :=
      fun k hk hc => semX_chain hc (ih k hk)
    rw [hm]
    simp only [NTree.label]
    cases hst : s.state with
    | s0 =>
      rw [hst] at shape inputs output
      obtain ⟨ax, hf⟩ := shape
      simp only [RowOutputFX, hf, op0Axis] at output
      simp only [SemX, StateX.isChain]
      rw [hf]; simpa [evalFBy] using output
    | s1 =>
      rw [hst] at shape inputs output
      obtain ⟨t, hf⟩ := shape
      simp only [RowOutputFX, hf, tl, StrategyOfTraces.nounTail] at output
      simp only [SemX, StateX.isChain]
      rw [hf, output]; simp [evalFBy]
    | cons =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, d, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsX] at inputs
      obtain ⟨hs0, hf0, hs1, hf1⟩ := inputs
      simp only [RowOutputFX, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp) (roles 0 (by simp))
      have r1 := run k1 (by simp) (roles 1 (by simp))
      rw [hs0, hf0, hf] at r0
      rw [hs1, hf1, hf] at r1
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at r0 r1
      simp only [SemX, StateX.isChain]
      rw [hf, output]; simp [evalFBy, r0, r1]
    | s3 =>
      rw [hst] at shape inputs output roles
      obtain ⟨t, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, rest⟩⟩ <;> simp only [List.map, KidInputsX] at inputs
      obtain ⟨hs0, hf0⟩ := inputs
      simp only [RowOutputFX, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp) (roles 0 (by simp))
      rw [hs0, hf0, hf] at r0
      simp only [tl, StrategyOfTraces.nounTail] at r0
      simp only [SemX, StateX.isChain]
      rw [hf, output]; simp [evalFBy, r0]
    | s4 =>
      rw [hst] at shape inputs output roles
      obtain ⟨t, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, rest⟩⟩ <;> simp only [List.map, KidInputsX] at inputs
      obtain ⟨hs0, hf0⟩ := inputs
      simp only [RowOutputFX, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp) (roles 0 (by simp))
      rw [hs0, hf0, hf] at r0
      simp only [tl, StrategyOfTraces.nounTail] at r0
      simp only [SemX, StateX.isChain]
      rw [hf]; simp [evalFBy, r0, output]
    | s5 =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsX] at inputs
      obtain ⟨hs0, hf0, hs1, hf1⟩ := inputs
      simp only [RowOutputFX, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp) (roles 0 (by simp))
      have r1 := run k1 (by simp) (roles 1 (by simp))
      rw [hs0, hf0, hf] at r0
      rw [hs1, hf1, hf] at r1
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at r0 r1
      simp only [SemX, StateX.isChain]
      rw [hf, output]; simp [evalFBy, r0, r1]
    | s2 =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, rest⟩⟩⟩⟩ <;>
        simp only [List.map, KidInputsX] at inputs
      obtain ⟨hs0, hf0, hs1, hf1, hs2, hf2⟩ := inputs
      simp only [RowOutputFX, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp) (roles 0 (by simp))
      have r1 := run k1 (by simp) (roles 1 (by simp))
      have r2 := run k2 (by simp) (roles 2 (by simp))
      rw [hs0, hf0, hf] at r0
      rw [hs1, hf1, hf] at r1
      rw [hs2, hf2] at r2
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at r0 r1
      simp only [SemX, StateX.isChain]
      rw [hf, output]; simp [evalFBy, r0, r1, r2]
    | s6 =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, d, hf⟩ := shape
      rcases kids with _ | ⟨kT, _ | ⟨kC, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsX] at inputs
      obtain ⟨hsC, hfC, hsT, hfT⟩ := inputs
      simp only [RowOutputFX, List.map_cons, List.map_nil] at output
      obtain ⟨hb, he⟩ := output
      have rC := run kC (by simp) (roles 1 (by simp))
      have rT := run kT (by simp) (roles 0 (by simp))
      rw [hsC, hfC, hf] at rC
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rC
      rw [hsT, hfT, hf] at rT
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rT
      simp only [SemX, StateX.isChain]
      rw [hf, he]
      rcases hb with hb | hb
      · rw [hb] at rC rT; simp [condBit] at rT; simp [evalFBy, rC, rT]
      · rw [hb] at rC rT; simp [condBit] at rT; simp [evalFBy, rC, rT]
    | s7 =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, hf⟩ := shape
      rcases kids with _ | ⟨kM, _ | ⟨kH, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsX] at inputs
      obtain ⟨hsH, hfH, hsM, hfM⟩ := inputs
      simp only [RowOutputFX, List.map_cons, List.map_nil] at output
      have rH := run kH (by simp) (roles 1 (by simp))
      have rM := run kM (by simp) (roles 0 (by simp))
      rw [hsH, hfH, hf] at rH
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rH
      rw [hsM, hfM, hf] at rM
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rM
      simp only [SemX, StateX.isChain]
      rw [hf, output]; simp [evalFBy, rH, rM]
    | s8 =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, c, hf⟩ := shape
      rcases kids with _ | ⟨kM, _ | ⟨kH, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsX] at inputs
      obtain ⟨hsH, hfH, hsM, hfM⟩ := inputs
      simp only [RowOutputFX, List.map_cons, List.map_nil] at output
      have rH := run kH (by simp) (roles 1 (by simp))
      have rM := run kM (by simp) (roles 0 (by simp))
      rw [hsH, hfH, hf] at rH
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rH
      rw [hsM, hfM, hf] at rM
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rM
      simp only [SemX, StateX.isChain]
      rw [hf, output]; simp [evalFBy, rH, rM]
    | s9 =>
      rw [hst] at shape inputs output roles
      obtain ⟨ax, c, hf⟩ := shape
      rcases kids with _ | ⟨kC, _ | ⟨kI, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsX] at inputs
      obtain ⟨hsC, hfC, hsI, hslot⟩ := inputs
      simp only [RowOutputFX, List.map_cons, List.map_nil] at output
      have rC := run kC (by simp) (roles 0 (by simp))
      have rI := run kI (by simp) (roles 1 (by simp))
      rw [hsC, hfC, hf] at rC
      simp only [tl, StrategyOfTraces.nounTail] at rC
      rw [hsI] at rI
      rw [hf] at hslot
      simp only [op9Axis] at hslot
      simp only [SemX, StateX.isChain]
      rw [hf, output]; simp [evalFBy, rC, hslot, rI]
    | s10 =>
      rw [hst] at shape inputs output roles
      obtain ⟨ax, c, d, hf⟩ := shape
      rcases kids with _ | ⟨kN, _ | ⟨kO, _ | ⟨kE, _ | ⟨k3, rest⟩⟩⟩⟩ <;>
        simp only [List.map, KidInputsX] at inputs
      obtain ⟨hsN, hfN, hsO, hfO, hsE, hfE⟩ := inputs
      simp only [RowOutputFX, List.map_cons, List.map_nil] at output
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
      simp only [SemX, StateX.isChain]
      rw [hf]; simp [evalFBy, rN, rO, hed]
    | s10L =>
      rw [hst] at shape inputs output roles
      obtain ⟨ax, hf, hax⟩ := shape
      rcases kids with _ | ⟨k, _ | ⟨k1, rest⟩⟩ <;> simp only [List.map, KidInputsX] at inputs
      obtain ⟨hsk, hfk⟩ := inputs
      simp only [RowOutputFX, List.map_cons, List.map_nil] at output
      obtain ⟨hke, hsib⟩ := output
      have ck := chain k (by simp) (roles 0 (by simp))
      rw [hfk, hsk, hke, hf] at ck
      simp only [chainAxis] at ck hsib
      rw [hf] at hsib
      simp only [chainAxis] at hsib
      simp only [SemX, StateX.isChain, if_true, hf, chainAxis]
      exact ⟨chainOK_step hax hsib ck, ax, rfl⟩
    | s10T =>
      rw [hst] at shape
      rw [shape]
      simp only [SemX, StateX.isChain, if_true, chainAxis]
      exact ⟨chainOK_of_lt_two (by norm_num) _ _, 1, rfl⟩
    | s11s =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, body, hf⟩ := shape
      rcases kids with _ | ⟨k, _ | ⟨k1, rest⟩⟩ <;> simp only [List.map, KidInputsX] at inputs
      obtain ⟨hsk, hfk⟩ := inputs
      simp only [RowOutputFX, List.map_cons, List.map_nil] at output
      have rk := run k (by simp) (roles 0 (by simp))
      rw [hsk, hfk, hf] at rk
      simp only [tl, StrategyOfTraces.nounTail] at rk
      simp only [SemX, StateX.isChain]
      rw [hf, output]; simp [evalFBy, rk]
    | s11d =>
      rw [hst] at shape inputs output roles
      obtain ⟨b, clue, body, hf⟩ := shape
      rcases kids with _ | ⟨kD, _ | ⟨kB, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsX] at inputs
      obtain ⟨hsD, hfD, hsB, hfB⟩ := inputs
      simp only [RowOutputFX, List.map_cons, List.map_nil] at output
      have rD := run kD (by simp) (roles 0 (by simp))
      have rB := run kB (by simp) (roles 1 (by simp))
      rw [hsD, hfD, hf] at rD
      rw [hsB, hfB, hf] at rB
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rD rB
      simp only [SemX, StateX.isChain]
      rw [hf, output]; simp [evalFBy, rD, rB]
    | s11j =>
      rw [hst] at inputs
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputsX] at inputs

/-- **Field genuineness is a successful field run** (twin of `SVGenuineF.genuineF_evalFBy`): a
field-genuine extended tree with a real root runs under `evalFBy q` at fuel `T.size`. -/
theorem genuineFX_evalFBy {q : ℕ} {T : NTree RowX} (hT : GenuineSkelFX q T)
    (hreal : T.label.state.isChain = false) :
    evalFBy q T.size T.label.subject T.label.formula = some T.label.evaluation :=
  semX_real hreal (genuineFX_sem hT)

/-- A chain node of a field-genuine extended tree satisfies `ChainOK` at its atom axis. -/
theorem genuineFX_chainOK {q : ℕ} {T : NTree RowX} (hT : GenuineSkelFX q T)
    (hchain : T.label.state.isChain = true) :
    ChainOK (chainAxis T.label.formula) T.label.subject T.label.evaluation :=
  semX_chain hchain (genuineFX_sem hT)

/-- **A field-genuine extended tree rooted at the claim proves the claim under `HoldsF`.** -/
theorem holdsF_of_genuineFX {q : ℕ} {T : NTree RowX} (hT : GenuineSkelFX q T)
    (hreal : T.label.state.isChain = false) {x : P8PublicClaim}
    (hs : T.label.subject = x.subject) (hf : T.label.formula = x.formula)
    (he : T.label.evaluation = x.result) : HoldsF q x :=
  ⟨T.size, by rw [← hs, ← hf, ← he]; exact genuineFX_evalFBy hT hreal⟩

end Nock.Edit
