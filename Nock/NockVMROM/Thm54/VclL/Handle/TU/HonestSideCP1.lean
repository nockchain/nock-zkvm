/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/HonestSideCP1.lean

 **Trace uniqueness on the P1 fragment: the honest compute trace satisfies the compute side gates.**

 * E3: on an honest compute row whose state is one of `0, 7, 10, 11, 12, 13`, every round-0 column `c` is `0` when the
 row's state is not in `Act(c)`; each gate of `canonCGates` vanishes at the honest row environment.
 * E2: `(1 − s4·fast)·inv4 = 0` (`fast` and `inv4` are `0` off state `4`).
 * E8: the total activity plus pair flag of each slot is `0` or `1` on these rows, and when it is `0` the honest
 inverse `A·D⁻¹` is `0`; each E8 gate of `canonC2Gates` vanishes.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.SideCompP1
import Nock.NockVMROM.Thm54.VclL.Handle.HonestSlotX
import Nock.V1J8.FillX
import Nock.NockVMROM.Thm54.VclL.Handle.HonestTraceX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.HonestSideCP1

noncomputable section

open Nock Nock.Noun Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1 Nock.NockVMROM.Thm54.VclL.Handle.TU.SideCompP1
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX (hk hv hb hN)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX (stIdx)
open Nock.V1J8.FillX Nock.Walk
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX (rowAtWX)

section Row
variable {F : Type} [Field F] [DecidableEq F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))

/-- The six P1 states. -/
def P1State (st : StateX) : Prop :=
  st = .s0 ∨ st = .s7 ∨ st = .cons ∨ st = .s10 ∨ st = .s10L ∨ st = .s10T

/-- What the honest handle map gives a P1 row: the default noun `0` is `(0, 0)`, no handle is a big atom (the
fragment's atoms are small), and the hosted axis atom `m` has kind `0`. -/
structure P1Hyp (r : RowNX) : Prop where
  h0 : H (.atom 0) = (0, 0)
  nb : ∀ j < 12, (H (hN r j)).1 ≠ 2
  hm : (H r.m).1 = 0

theorem s0_off (s f e a b : Noun) (h0 : H (.atom 0) = (0, 0))
    (ns : (H s).1 ≠ 2) (nf : (H f).1 ≠ 2) (ne : (H e).1 ≠ 2) (na : (H a).1 ≠ 2) (nb : (H b).1 ≠ 2)
    (fst lst : F) :
    ∀ c < 69, stIdx (.s0 : StateX) ∉ actC c →
      colXE H pd ({ st := .s0, s := s, f := f, e := e, fh := a, ft := b } : RowNX) fst lst c = 0 := by
  intro c hc hn
  interval_cases c <;>
    simp_all [colXE, hN, hk, hv, hb, actC, six, stIdx, cZ1E, cVE, cBE, cV2E, cWE, cPrE, cFastE, cInv4E,
      cAx2E, cPr2E, cLE, isPairB]

theorem s7_off (s f e a b c' d x y : Noun) (h0 : H (.atom 0) = (0, 0))
    (ns : (H s).1 ≠ 2) (nf : (H f).1 ≠ 2) (ne : (H e).1 ≠ 2) (na : (H a).1 ≠ 2) (nb : (H b).1 ≠ 2)
    (nc : (H c').1 ≠ 2) (nd : (H d).1 ≠ 2) (nx : (H x).1 ≠ 2) (ny : (H y).1 ≠ 2) (fst lst : F) :
    ∀ c < 69, stIdx (.s7 : StateX) ∉ actC c →
      colXE H pd ({ st := .s7, s := s, f := f, e := e, fh := a, ft := b, fth := c', ftt := d, sf1 := x,
                    sf2 := y } : RowNX) fst lst c = 0 := by
  intro c hc hn
  interval_cases c <;>
    simp_all [colXE, hN, hk, hv, hb, actC, six, stIdx, cZ1E, cVE, cBE, cV2E, cWE, cPrE, cFastE, cInv4E,
      cAx2E, cPr2E, cLE, isPairB]

theorem cons_off (s f e a b x y : Noun) (h0 : H (.atom 0) = (0, 0))
    (ns : (H s).1 ≠ 2) (nf : (H f).1 ≠ 2) (ne : (H e).1 ≠ 2) (na : (H a).1 ≠ 2) (nb : (H b).1 ≠ 2)
    (nx : (H x).1 ≠ 2) (ny : (H y).1 ≠ 2) (fst lst : F) :
    ∀ c < 69, stIdx (.cons : StateX) ∉ actC c →
      colXE H pd ({ st := .cons, s := s, f := f, e := e, fh := a, ft := b, sf1 := x,
                    sf2 := y } : RowNX) fst lst c = 0 := by
  intro c hc hn
  interval_cases c <;>
    simp_all [colXE, hN, hk, hv, hb, actC, six, stIdx, cZ1E, cVE, cBE, cV2E, cWE, cPrE, cFastE, cInv4E,
      cAx2E, cPr2E, cLE, isPairB]

theorem s10_off (s f e a b c' d g g' x y : Noun) (h0 : H (.atom 0) = (0, 0))
    (ns : (H s).1 ≠ 2) (nf : (H f).1 ≠ 2) (ne : (H e).1 ≠ 2) (na : (H a).1 ≠ 2) (nb : (H b).1 ≠ 2)
    (nc : (H c').1 ≠ 2) (nd : (H d).1 ≠ 2) (ng : (H g).1 ≠ 2) (ng' : (H g').1 ≠ 2)
    (nx : (H x).1 ≠ 2) (ny : (H y).1 ≠ 2) (fst lst : F) :
    ∀ c < 69, stIdx (.s10 : StateX) ∉ actC c →
      colXE H pd ({ st := .s10, s := s, f := f, e := e, fh := a, ft := b, fth := c', ftt := d, ftth := g,
                    fttt := g', sf1 := x, sf2 := y } : RowNX) fst lst c = 0 := by
  intro c hc hn
  interval_cases c <;>
    simp_all [colXE, hN, hk, hv, hb, actC, six, stIdx, cZ1E, cVE, cBE, cV2E, cWE, cPrE, cFastE, cInv4E,
      cAx2E, cPr2E, cLE, isPairB]

theorem s10L_off (s f e m g g' : Noun) (h0 : H (.atom 0) = (0, 0))
    (ns : (H s).1 ≠ 2) (nf : (H f).1 ≠ 2) (ne : (H e).1 ≠ 2) (nm : (H m).1 = 0)
    (ng : (H g).1 ≠ 2) (ng' : (H g').1 ≠ 2) (fst lst : F) :
    ∀ c < 69, stIdx (.s10L : StateX) ∉ actC c →
      colXE H pd ({ st := .s10L, s := s, f := f, e := e, sf1 := s, sf2 := e, m := m, ftth := g,
                    fttt := g' } : RowNX) fst lst c = 0 := by
  intro c hc hn
  interval_cases c <;>
    simp_all [colXE, hN, hk, hv, hb, actC, six, stIdx, cZ1E, cVE, cBE, cV2E, cWE, cPrE, cFastE, cInv4E,
      cAx2E, cPr2E, cLE, isPairB]

theorem s10T_off (s f e : Noun) (h0 : H (.atom 0) = (0, 0))
    (ns : (H s).1 ≠ 2) (nf : (H f).1 ≠ 2) (ne : (H e).1 ≠ 2) (fst lst : F) :
    ∀ c < 69, stIdx (.s10T : StateX) ∉ actC c →
      colXE H pd ({ st := .s10T, s := s, f := f, e := e } : RowNX) fst lst c = 0 := by
  intro c hc hn
  interval_cases c <;>
    simp_all [colXE, hN, hk, hv, hb, actC, six, stIdx, cZ1E, cVE, cBE, cV2E, cWE, cPrE, cFastE, cInv4E,
      cAx2E, cPr2E, cLE, isPairB]


theorem rowOfSkelX_st (sk : SkelX) : (rowOfSkelX sk).st = sk.state := by
  unfold rowOfSkelX; cases sk.state <;> rfl

/-- **The extra pin (E3) at the row level.** For the honest row of a generated skeleton whose state is one of the six P1 states, a
round-0 compute column is `0` whenever the state is outside `Act` of that column. -/
theorem e3_off (sk : SkelX) (hs : P1State sk.state) (hy : P1Hyp H (rowOfSkelX sk)) (fst lst : F) :
    ∀ c < 69, stIdx (rowOfSkelX sk).st ∉ actC c → colXE H pd (rowOfSkelX sk) fst lst c = 0 := by
  have nb := hy.nb
  have h0 := hy.h0
  have hm := hy.hm
  rcases hs with h | h | h | h | h | h
  · have hr : rowOfSkelX sk =
      { st := .s0, s := sk.subject, f := sk.formula, e := sk.evaluation,
        fh := hdN sk.formula, ft := tlN sk.formula } := by simp only [rowOfSkelX, h]
    rw [hr] at nb hm ⊢
    exact s0_off H pd _ _ _ _ _ h0 (nb 0 (by norm_num)) (nb 1 (by norm_num)) (nb 2 (by norm_num))
      (nb 5 (by norm_num)) (nb 6 (by norm_num)) fst lst
  · have hr : rowOfSkelX sk =
      { st := .s7, s := sk.subject, f := sk.formula, e := sk.evaluation,
        fh := hdN sk.formula, ft := tlN sk.formula, fth := hdN (tlN sk.formula),
        ftt := tlN (tlN sk.formula), sf1 := kidE sk 0, sf2 := kidE sk 1 } := by simp only [rowOfSkelX, h]
    rw [hr] at nb hm ⊢
    exact s7_off H pd _ _ _ _ _ _ _ _ _ h0 (nb 0 (by norm_num)) (nb 1 (by norm_num)) (nb 2 (by norm_num))
      (nb 5 (by norm_num)) (nb 6 (by norm_num)) (nb 7 (by norm_num)) (nb 8 (by norm_num))
      (nb 3 (by norm_num)) (nb 4 (by norm_num)) fst lst
  · have hr : rowOfSkelX sk =
      { st := .cons, s := sk.subject, f := sk.formula, e := sk.evaluation,
        fh := hdN sk.formula, ft := tlN sk.formula, sf1 := kidE sk 0, sf2 := kidE sk 1 } := by
      simp only [rowOfSkelX, h]
    rw [hr] at nb hm ⊢
    exact cons_off H pd _ _ _ _ _ _ _ h0 (nb 0 (by norm_num)) (nb 1 (by norm_num)) (nb 2 (by norm_num))
      (nb 5 (by norm_num)) (nb 6 (by norm_num)) (nb 3 (by norm_num)) (nb 4 (by norm_num)) fst lst
  · have hr : rowOfSkelX sk =
      { st := .s10, s := sk.subject, f := sk.formula, e := sk.evaluation,
        fh := hdN sk.formula, ft := tlN sk.formula, fth := hdN (tlN sk.formula),
        ftt := tlN (tlN sk.formula), ftth := hdN (hdN (tlN sk.formula)),
        fttt := tlN (hdN (tlN sk.formula)), sf1 := kidE sk 0, sf2 := kidE sk 1 } := by
      simp only [rowOfSkelX, h]
    rw [hr] at nb hm ⊢
    exact s10_off H pd _ _ _ _ _ _ _ _ _ _ _ h0 (nb 0 (by norm_num)) (nb 1 (by norm_num))
      (nb 2 (by norm_num)) (nb 5 (by norm_num)) (nb 6 (by norm_num)) (nb 7 (by norm_num))
      (nb 8 (by norm_num)) (nb 9 (by norm_num)) (nb 10 (by norm_num)) (nb 3 (by norm_num))
      (nb 4 (by norm_num)) fst lst
  · have hr : rowOfSkelX sk =
      { st := .s10L, s := sk.subject, f := sk.formula, e := sk.evaluation,
        sf1 := sk.subject, sf2 := sk.evaluation, m := .atom (chainAxis sk.formula ^^^ 1),
        ftth := sibX (chainAxis sk.formula) sk.subject,
        fttt := sibX (chainAxis sk.formula) sk.evaluation } := by simp only [rowOfSkelX, h]
    rw [hr] at nb hm ⊢
    exact s10L_off H pd _ _ _ _ _ _ h0 (nb 0 (by norm_num)) (nb 1 (by norm_num)) (nb 2 (by norm_num))
      hm (nb 9 (by norm_num)) (nb 10 (by norm_num)) fst lst
  · have hr : rowOfSkelX sk =
      { st := .s10T, s := sk.subject, f := sk.formula, e := sk.evaluation } := by
      simp only [rowOfSkelX, h]
    rw [hr] at nb hm ⊢
    exact s10T_off H pd _ _ _ h0 (nb 0 (by norm_num)) (nb 1 (by norm_num)) (nb 2 (by norm_num)) fst lst

/-- The one-hot columns of an honest row. -/
theorem colXE_onehot (r : RowNX) (fst lst : F) (i : ℕ) (hi : i < 17) :
    colXE H pd r fst lst i = if stIdx r.st = i then 1 else 0 := by
  simp only [colXE, hi, ite_true]

/-- **The extra pin (E2) columns**: `fast` and `inv4` are `0` on the six P1 states. -/
theorem e2_cols (r : RowNX) (hs : P1State r.st) (fst lst : F) :
    colXE H pd r fst lst 61 = 0 ∧ colXE H pd r fst lst 62 = 0 := by
  rcases hs with h | h | h | h | h | h <;> simp [colXE, cFastE, cInv4E, h]

end Row

section Gates
variable {F : Type} [Field F] [DecidableEq F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))

/-- The environment of an honest compute row: its trace holds the round-0 columns. -/
def RowEnv (r : RowNX) (fst lst : F) (eF : Env F) : Prop :=
  ∀ i < 69, eF.trace i = colXE H pd r fst lst i

/-- **The extra pin (E3) and E2 at an honest row**: every gate of `canonCGates` evaluates to `0`. -/
theorem canonCGates_honest (sk : SkelX) (hs : P1State sk.state) (hy : P1Hyp H (rowOfSkelX sk))
    (fst lst : F) (eF : Env F) (hE : RowEnv H pd (rowOfSkelX sk) fst lst eF) :
    ∀ g ∈ canonCGates (F := F), g.eval eF = 0 := by
  have hst : P1State (rowOfSkelX sk).st := by rw [rowOfSkelX_st]; exact hs
  intro g hg
  unfold canonCGates at hg
  rcases List.mem_cons.mp hg with rfl | hg
  · obtain ⟨h61, h62⟩ := e2_cols H pd _ hst fst lst
    simp only [CoeffExpr.eval, cv, notE]
    rw [hE 62 (by norm_num), h62, mul_zero]
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
    have hc69 : c < 69 := List.mem_range.mp hc
    simp only [pinC, CoeffExpr.eval, CoeffExpr.eval_sumList, cv]
    by_cases hmem : stIdx (rowOfSkelX sk).st ∈ actC c
    · have : ((List.filter (fun s => decide (s ∉ actC c)) (List.range 17)).map fun i => eF.trace i).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        obtain ⟨hi17, hna⟩ := List.mem_filter.mp hi
        have hna' : i ∉ actC c := by simpa using hna
        have hi17' : i < 17 := List.mem_range.mp hi17
        rw [hE i (by omega), colXE_onehot H pd _ fst lst i hi17']
        have : stIdx (rowOfSkelX sk).st ≠ i := fun h => hna' (h ▸ hmem)
        simp [this]
      rw [this, zero_mul]
    · rw [hE c hc69, e3_off H pd sk hs hy fst lst c hc69 hmem, mul_zero]

end Gates

section Act
variable {F : Type} [Field F] [DecidableEq F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))

/-- The entries' total activity of a slot at an environment. -/
def entSum (S : SlotX F) (eF : Env F) : F := (CoeffExpr.sumList S.ents EntX.act).eval eF

/-- The pair flag of a slot at an environment (`0` if the slot has no pair). -/
def pairFl (S : SlotX F) (eF : Env F) : F :=
  match S.pair with
  | some (fl, _, _, _) => eF.trace fl
  | none => 0

theorem actTotX_eval (S : SlotX F) (eF : Env F) :
    (actTotX S).eval eF = entSum S eF + pairFl S eF := by
  unfold actTotX entSum pairFl
  rcases hp : S.pair with _ | ⟨fl, a, b, bb⟩ <;> simp [CoeffExpr.eval, cc]

/-- **The extra pin (E8) activity**: on every honest P1 row each slot is either inactive (entries `0`, pair flag `0`) or its total
activity plus pair flag is `1`. -/
theorem slot_act01 (r : RowNX) (hs : P1State r.st) (fst lst : F) (eF : Env F)
    (hE : RowEnv H pd r fst lst eF) :
    ∀ S ∈ (ChipHX.slotsX : List (SlotX F)),
      (entSum S eF = 0 ∧ pairFl S eF = 0) ∨ entSum S eF + pairFl S eF = 1 := by
  have hE' : ∀ i, i < 69 → eF.trace i = colXE H pd r fst lst i := hE
  intro S hS
  simp only [ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl <;>
  rcases hs with h | h | h | h | h | h <;>
  simp [entSum, pairFl, CoeffExpr.eval, CoeffExpr.eval_sumList, EntX.act, selS, notC, cc, kcE, kbE,
    slot0X, slot1X, slot2X, slot3X, opStatesX, l2X, l3X, sS10, sS10L, sS10T, sS11j, consCol, prX, pr2X,
    fastX, z1X, hE', colXE, stIdx, h, cZ1E, cPrE, cPr2E, isPairB, cFastE] <;>
  split_ifs <;> simp <;> assumption

end Act

section E8
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
  (b : Basis (Fin 3) F K) (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

theorem aVal_inactive (S : SlotX F) (eF : Env F) (h1 : entSum S eF = 0) (h2 : pairFl S eF = 0) :
    HonestSlotX.aVal b δ S eF = 0 := by
  unfold HonestSlotX.aVal HonestSlotX.slotAQ
  rw [T0TowerFP.qadd_val, Compute.TowerD.qlift_val]
  have h1' : (CoeffExpr.sumList S.ents EntX.act).eval eF = 0 := h1
  rw [h1', map_zero, zero_add]
  rcases hp : S.pair with _ | ⟨fl, a, b', bb⟩
  · simp [Compute.TowerD.qconst_val]
  · have : eF.trace fl = 0 := by simpa [pairFl, hp] using h2
    rw [T0TowerFP.qmul_val, Compute.TowerD.qlift_val]
    simp [CoeffExpr.eval, cc, this]

theorem inv_limbs_zero (S : SlotX F) (eF : Env F)
    (hinv : HonestSlotX.invAt b δ S eF = HonestSlotX.aVal b δ S eF * (HonestSlotX.dVal b δ S eF)⁻¹)
    (ha : HonestSlotX.aVal b δ S eF = 0) :
    ∀ k < 3, eF.trace (S.inv + k) = 0 ∧ eF.trace (S.invIm + k) = 0 := by
  intro k hk
  rw [ha, zero_mul] at hinv
  unfold HonestSlotX.invAt at hinv
  obtain ⟨h1, h2⟩ := (Quad.mk_eq_zero_iff _ _ _).mp hinv
  have c1 := Compute.LogUp.coord_limbVal b eF.trace S.inv ⟨k, hk⟩
  have c2 := Compute.LogUp.coord_limbVal b eF.trace S.invIm ⟨k, hk⟩
  rw [h1] at c1
  rw [h2] at c2
  simp only [coord, map_zero, Finsupp.coe_zero, Pi.zero_apply] at c1 c2
  exact ⟨c1.symm, c2.symm⟩

/-- **The extra pin (E8) at an honest P1 row**: given the honest inverse limbs `A · D⁻¹`, every E8 gate vanishes. -/
theorem honest_canonC2_e8 (r : RowNX) (hs : P1State r.st) (fst lst : F) (eF : Env F)
    (hE : RowEnv H pd r fst lst eF)
    (hinv : ∀ S ∈ (ChipHX.slotsX : List (SlotX F)),
      HonestSlotX.invAt b δ S eF = HonestSlotX.aVal b δ S eF * (HonestSlotX.dVal b δ S eF)⁻¹) :
    ∀ g ∈ (ChipHX.slotsX (F := F)).flatMap e8Slot, g.eval eF = 0 := by
  intro g hg
  obtain ⟨S, hS, hg⟩ := List.mem_flatMap.mp hg
  have hact := slot_act01 H pd r hs fst lst eF hE S hS
  have key : ∀ k < 3, (1 - (actTotX S).eval eF) * eF.trace (S.inv + k) = 0 ∧
      (1 - (actTotX S).eval eF) * eF.trace (S.invIm + k) = 0 := by
    intro k hk
    rcases hact with ⟨h1, h2⟩ | h
    · obtain ⟨z1, z2⟩ := inv_limbs_zero b δ S eF (hinv S hS) (aVal_inactive b δ S eF h1 h2) k hk
      exact ⟨by rw [z1, mul_zero], by rw [z2, mul_zero]⟩
    · rw [actTotX_eval, h]; simp
  simp only [e8Slot, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · have := (key k (List.mem_range.mp hk)).1
    simpa [CoeffExpr.eval, cc] using this
  · have := (key k (List.mem_range.mp hk)).2
    simpa [CoeffExpr.eval, cc] using this

/-- **The extra pin (E9) at an honest row**: `isLast·wInv` vanishes given `wInv = 0` on the last row (the honest fill). -/
theorem honest_canonC2_e9 (eF : Env F) (h01 : eF.trace lastX = 0 ∨ eF.trace lastX = 1)
    (hw : eF.trace lastX = 1 → ∀ k < 3, eF.trace (wInvX + k) = 0) :
    ∀ g ∈ (e9Gates : List (CoeffExpr F)), g.eval eF = 0 := by
  intro g hg
  simp only [e9Gates, List.mem_map] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  have hk' := List.mem_range.mp hk
  simp only [CoeffExpr.eval, cc]
  rcases h01 with h | h
  · rw [h, zero_mul]
  · rw [hw h k hk', mul_zero]

/-- **`honest_canonC`**: every gate of `canonCGates` vanishes at an honest P1 compute row. -/
theorem honest_canonC (sk : SkelX) (hs : P1State sk.state) (hy : P1Hyp H (rowOfSkelX sk))
    (fst lst : F) (eF : Env F) (hE : RowEnv H pd (rowOfSkelX sk) fst lst eF) :
    ∀ g ∈ canonCGates (F := F), g.eval eF = 0 :=
  canonCGates_honest H pd sk hs hy fst lst eF hE

/-- **`honest_canonC2`**: every gate of `canonC2Gates` vanishes at an honest P1 compute row whose slot inverses
hold `A · D⁻¹` and whose `wInv` is `0` on the last row. -/
theorem honest_canonC2 (r : RowNX) (hs : P1State r.st) (fst lst : F) (eF : Env F)
    (hE : RowEnv H pd r fst lst eF)
    (hinv : ∀ S ∈ (ChipHX.slotsX : List (SlotX F)),
      HonestSlotX.invAt b δ S eF = HonestSlotX.aVal b δ S eF * (HonestSlotX.dVal b δ S eF)⁻¹)
    (h01 : eF.trace lastX = 0 ∨ eF.trace lastX = 1)
    (hw : eF.trace lastX = 1 → ∀ k < 3, eF.trace (wInvX + k) = 0) :
    ∀ g ∈ canonC2Gates (F := F), g.eval eF = 0 := by
  intro g hg
  unfold canonC2Gates at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact honest_canonC2_e8 H pd b δ r hs fst lst eF hE hinv g hg
  · exact honest_canonC2_e9 eF h01 hw g hg

end E8

section Discharge
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
  (b : Basis (Fin 3) F K) (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

open Nock.NockVMROM.Thm54.VclL.HonestTraceX (trX baseT env0 flX llX slotAt trX_base baseT_18
  slot_index dVal_aVal_congr lnW cntW)

/-- The honest environment of chip row `j`: the honest trace `trX` at rows `j` and `j + 1`. -/
def honestEnv (W : List (NTree SkelX)) (chalV pubVal : ℕ → F) (ln cnt acc : ℕ → K) (j : ℕ) : Env F :=
  ⟨trX b δ H pd W chalV pubVal ln cnt acc j, trX b δ H pd W chalV pubVal ln cnt acc (j + 1), chalV, pubVal⟩

theorem honestEnv_rowEnv (W : List (NTree SkelX)) (chalV pubVal : ℕ → F) (ln cnt acc : ℕ → K) (j : ℕ) :
    RowEnv H pd (rowAtWX W (j + 1)) (flX (F := F) j) (llX W j) (honestEnv H pd b δ W chalV pubVal ln cnt acc j) := by
  intro i hi
  show trX b δ H pd W chalV pubVal ln cnt acc j i = _
  rw [trX_base b δ H pd W chalV pubVal ln cnt acc j i hi]
  unfold baseT
  rw [colXE_eq]

theorem honestEnv_hinv (W : List (NTree SkelX)) (chalV pubVal : ℕ → F) (ln cnt acc : ℕ → K) (j : ℕ) :
    ∀ S ∈ (ChipHX.slotsX : List (SlotX F)),
      HonestSlotX.invAt b δ S (honestEnv H pd b δ W chalV pubVal ln cnt acc j) =
        HonestSlotX.aVal b δ S (honestEnv H pd b δ W chalV pubVal ln cnt acc j) *
          (HonestSlotX.dVal b δ S (honestEnv H pd b δ W chalV pubVal ln cnt acc j))⁻¹ := by
  intro S hS
  obtain ⟨sI, hs4, rfl, hinvS, hinvSi⟩ := slot_index hS
  have hcg := dVal_aVal_congr b δ hS (honestEnv H pd b δ W chalV pubVal ln cnt acc j)
    (env0 H pd W chalV pubVal j)
    (fun c hc => by
      show trX b δ H pd W chalV pubVal ln cnt acc j c = _
      rw [trX_base b δ H pd W chalV pubVal ln cnt acc j c hc]; rfl) rfl
  rw [hcg.1, hcg.2]
  unfold HonestSlotX.invAt
  rw [hinvS, hinvSi]
  change Quad.mk _ (Compute.LogUp.limbVal b (trX b δ H pd W chalV pubVal ln cnt acc j) (69 + 6 * sI))
    (Compute.LogUp.limbVal b (trX b δ H pd W chalV pubVal ln cnt acc j) (72 + 6 * sI)) = _
  rw [HonestTraceX.limb_inv b δ H pd W chalV pubVal ln cnt acc j sI hs4,
    HonestTraceX.limb_invIm b δ H pd W chalV pubVal ln cnt acc j sI hs4, Quad.mk_re_im]
  rfl

theorem honestEnv_last (W : List (NTree SkelX)) (chalV pubVal : ℕ → F) (ln cnt acc : ℕ → K) (j : ℕ) :
    (honestEnv H pd b δ W chalV pubVal ln cnt acc j).trace lastX = (if j + 1 = W.length then 1 else 0 : F) := by
  show trX b δ H pd W chalV pubVal ln cnt acc j 18 = _
  rw [trX_base b δ H pd W chalV pubVal ln cnt acc j 18 (by norm_num), baseT_18]

theorem honestEnv_h01 (W : List (NTree SkelX)) (chalV pubVal : ℕ → F) (ln cnt acc : ℕ → K) (j : ℕ) :
    (honestEnv H pd b δ W chalV pubVal ln cnt acc j).trace lastX = 0 ∨
      (honestEnv H pd b δ W chalV pubVal ln cnt acc j).trace lastX = 1 := by
  rw [honestEnv_last]
  by_cases h : j + 1 = W.length <;> simp [h]

/-- **`wInv` is `0` on the last row**: at the last BFS row `cnt = ln` (`Sf + 1 = h`, `foCol_Sf_tiling`). -/
theorem honestEnv_hw (t : NTree SkelX) (chalV pubVal : ℕ → F) (α : K) (acc : ℕ → K) (j : ℕ) :
    (honestEnv H pd b δ (bfsForest [t]) chalV pubVal (lnW α) (cntW (bfsForest [t]) α) acc j).trace lastX = 1 →
      ∀ k < 3, (honestEnv H pd b δ (bfsForest [t]) chalV pubVal (lnW α) (cntW (bfsForest [t]) α) acc j).trace
        (wInvX + k) = 0 := by
  intro hl k hk
  rw [honestEnv_last] at hl
  have hlen : j + 1 = (bfsForest [t]).length := by
    by_contra h
    simp [h] at hl
  have hcl : cntW (bfsForest [t]) α (j + 1) = lnW α (j + 1) := by
    have ht := Walk.foCol_Sf_tiling t
    unfold cntW lnW
    simp only [Compute.TowerD.cntClosed, Compute.TowerD.lnClosed]
    rw [hlen]
    conv_rhs => rw [← ht]
    rw [pow_succ']
  show trX b δ H pd (bfsForest [t]) chalV pubVal (lnW α) (cntW (bfsForest [t]) α) acc j (120 + k) = 0
  unfold trX
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have h1 : (120 + k - 111) / 3 = 3 := by omega
  rw [h1]
  simp [HonestTraceX.walkV, hcl, HonestTraceX.cNA, coord]

/-- **`honest_canonC2'`**: every gate of `canonC2Gates` vanishes at the honest environment of any chip row of a
generated tree's BFS whose compute row is in a P1 state. -/
theorem honest_canonC2' (t : NTree SkelX) (chalV pubVal : ℕ → F) (α : K) (acc : ℕ → K) (j : ℕ)
    (hs : P1State (rowAtWX (bfsForest [t]) (j + 1)).st) :
    ∀ g ∈ canonC2Gates (F := F),
      g.eval (honestEnv H pd b δ (bfsForest [t]) chalV pubVal (lnW α) (cntW (bfsForest [t]) α) acc j) = 0 :=
  honest_canonC2 H pd b δ _ hs _ _ _
    (honestEnv_rowEnv H pd b δ _ chalV pubVal _ _ acc j)
    (honestEnv_hinv H pd b δ _ chalV pubVal _ _ acc j)
    (honestEnv_h01 H pd b δ _ chalV pubVal _ _ acc j)
    (honestEnv_hw H pd b δ t chalV pubVal α acc j)

end Discharge

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.HonestSideCP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.HonestSideCP1.honest_canonC
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.HonestSideCP1.honest_canonC2
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.HonestSideCP1.honest_canonC2'
