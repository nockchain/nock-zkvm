/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/RoundsAtomP1.lean

 **Trace uniqueness on the P1 fragment: the atom table's rounds 1 and 2.**

 The atom table at the pad row carries the round-0 columns `< 205` of the pad (`padA`): the first and last
 row flags are `1`, and the two child kinds are `0`. At a fixed coin outside the events (`z ≠ 0`), two
 traces accepted by `atomChipHQ` with the same round-0 columns have the same `144` round-1 and round-2
 columns, and the same publics `0 .. 11`.

 * §1 cur-row read sets and their congruence (`curM_eval`, `ev_congr_cur`); the `𝕂′` gate shapes.
 * §2 environment level: one trace's gate facts (`atom_r1_facts`) and the equality of two (`atom_r1_eq`,
 `atom_r2_eq`, `atom_env_eq`), field-wise, for any two row environments.
 * §3 the terminal gates: the publics `0 .. 11` are the accumulators' last values (`atom_pubs_eq`).
 * §4 the chip level: rows of an accepted `atomChipHQ` trace, and the equality of all columns at the row nodes
 (`atom_cols_eq`, `atom_pubs_eq_of_chip`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsAtomP1

noncomputable section

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH (gather_chal_T gather_pub_T)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1 (padA)

/-! ## 1. Cur-row read sets -/

section Read
variable {F : Type} [Field F]

/-- A base expression reads only current-row trace columns `< B` (no next row, no coin, no public). -/
def curC (B : ℕ) : CoeffExpr F → Bool
  | .const _ => true
  | .var .traceCur i => decide (i < B)
  | .var .traceNext _ => false
  | .var .challenge _ => false
  | .var .publicVal _ => false
  | .add a b => curC B a && curC B b
  | .sub a b => curC B a && curC B b
  | .mul a b => curC B a && curC B b
  | .neg a => curC B a
  | .pow a _ => curC B a

/-- A mixed expression reads only current-row `𝕂`-roles `< R`, current-row base columns `< B` and coins
(no next row, no public). -/
def curM (R B : ℕ) : MixedExpr F → Bool
  | .Var .traceCur i => decide (i < R)
  | .Var .traceNext _ => false
  | .Var .challenge _ => true
  | .Var .publicVal _ => false
  | .Lift g => curC B g
  | .Scale g u => curC B g && curM R B u
  | .Const _ => true
  | .Add x y => curM R B x && curM R B y
  | .Sub x y => curM R B x && curM R B y
  | .Neg x => curM R B x
  | .Mul x y => curM R B x && curM R B y
  | .Pow x _ => curM R B x

theorem curC_eval {B : ℕ} {g : CoeffExpr F} (hg : curC B g = true) {e e' : Env F}
    (ht : ∀ j < B, e.trace j = e'.trace j) : g.eval e = g.eval e' := by
  induction g with
  | const c => rfl
  | var k i =>
    cases k <;> simp only [curC, decide_eq_true_eq, Bool.false_eq_true] at hg <;>
      simp only [CoeffExpr.eval]
    exact ht i hg
  | add a b iha ihb =>
    simp only [curC, Bool.and_eq_true] at hg
    simp only [CoeffExpr.eval, iha hg.1, ihb hg.2]
  | sub a b iha ihb =>
    simp only [curC, Bool.and_eq_true] at hg
    simp only [CoeffExpr.eval, iha hg.1, ihb hg.2]
  | mul a b iha ihb =>
    simp only [curC, Bool.and_eq_true] at hg
    simp only [CoeffExpr.eval, iha hg.1, ihb hg.2]
  | neg a iha =>
    simp only [curC] at hg
    simp only [CoeffExpr.eval, iha hg]
  | pow a m iha =>
    simp only [curC] at hg
    simp only [CoeffExpr.eval, iha hg]

variable {K : Type} [Field K] [Algebra F K]

theorem curM_eval {R B : ℕ} {g : MixedExpr F} (hg : curM R B g = true) {eK eK' : Env K}
    {eF eF' : Env F} (hKt : ∀ i < R, eK.trace i = eK'.trace i) (hKc : eK.chal = eK'.chal)
    (hFt : ∀ j < B, eF.trace j = eF'.trace j) : g.eval eK eF = g.eval eK' eF' := by
  induction g with
  | Var k i =>
    cases k <;> simp only [curM, decide_eq_true_eq, Bool.false_eq_true] at hg <;> simp only [MixedExpr.eval]
    · exact hKt i hg
    · rw [hKc]
  | Lift g =>
    simp only [curM] at hg
    simp only [MixedExpr.eval, curC_eval hg hFt]
  | Scale g u ih =>
    simp only [curM, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, curC_eval hg.1 hFt, ih hg.2]
  | Const c => rfl
  | Add x y ihx ihy =>
    simp only [curM, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, ihx hg.1, ihy hg.2]
  | Sub x y ihx ihy =>
    simp only [curM, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, ihx hg.1, ihy hg.2]
  | Neg x ih =>
    simp only [curM] at hg
    simp only [MixedExpr.eval, ih hg]
  | Mul x y ihx ihy =>
    simp only [curM, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, ihx hg.1, ihy hg.2]
  | Pow x m ih =>
    simp only [curM] at hg
    simp only [MixedExpr.eval, ih hg]

/-- **A `𝕂′` expression reading only current-row roles `< R`, base columns `< B` and coins is congruent.** -/
theorem ev_congr_cur (δF : F) {R B : ℕ} {e : QE F} (hre : curM R B e.re = true) (him : curM R B e.im = true)
    {eK eK' : Env K} {eF eF' : Env F} (hKt : ∀ i < R, eK.trace i = eK'.trace i) (hKc : eK.chal = eK'.chal)
    (hFt : ∀ j < B, eF.trace j = eF'.trace j) : e.ev δF eK eF = e.ev δF eK' eF' := by
  simp only [QE.ev, curM_eval hre hKt hKc hFt, curM_eval him hKt hKc hFt]

end Read

/-! ## 2. Environment level -/

section Env
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The `𝕂′` value of the `𝕂`-roles `r`, `r + 1`. -/
abbrev qvA (eK : Env K) (r : ℕ) : 𝕂′ := Quad.mk _ (eK.trace r) (eK.trace (r + 1))

/-- The coin `z′ = χ₂ + χ₃√δ`. -/
abbrev zv (eK : Env K) : 𝕂′ := Quad.mk _ (eK.chal 2) (eK.chal 3)

/-- Every `𝕂′` equation of the atom table. -/
def atomAllQ : List (QE F) := Cell.qEqs δF ++ CellHQ.gatesQ δF ++ atomQ δF

variable {eK eK' : Env K} {eF eF' : Env F}

theorem scale1 {c : CoeffExpr F} {a : QE F} (hc : c.eval eF = 1) (h : (QE.scale c a).ev δF eK eF = 0) :
    a.ev δF eK eF = 0 := by
  rw [ev_scale, hc] at h
  simpa [liftQ] using h

theorem gate_inv {r : ℕ} {D : QE F} (h : (QE.sub (QE.mul δF (QE.var r) D) QE.one).ev δF eK eF = 0) :
    qvA δF eK r * D.ev δF eK eF = 1 := by
  rw [ev_sub, ev_mul, ev_var, ev_one, sub_eq_zero] at h
  exact h

theorem inv_pair {r : ℕ} {D D' : 𝕂′} (g : qvA δF eK r * D = 1) (g' : qvA δF eK' r * D' = 1) (h : D = D') :
    qvA δF eK r = qvA δF eK' r := by
  subst h
  exact inv_col_unique (right_ne_zero_of_mul_eq_one g) g g'

theorem gate_first {a : ℕ} {T : QE F} (hF : eF.trace Cell.isF = 1)
    (h : (QE.scale (cv Cell.isF) (QE.sub (QE.var a) T)).ev δF eK eF = 0) :
    qvA δF eK a = T.ev δF eK eF := by
  have := scale1 δF (by simpa [cv, CoeffExpr.eval] using hF) h
  rw [ev_sub, ev_var, sub_eq_zero] at this
  exact this

theorem qv_eq {r : ℕ} (h : qvA δF eK r = qvA δF eK' r) :
    eK.trace r = eK'.trace r ∧ eK.trace (r + 1) = eK'.trace (r + 1) :=
  (Quad.mk_eq_mk_iff _ _ _ _ _).mp h

theorem ev_vTerm : (Cell.vTerm (F := F) true).ev δF eK eF =
    liftQ δF (eF.trace Cell.mv) * qvA δF eK Cell.vProvInv - qvA δF eK Cell.consLInv - qvA δF eK Cell.consRInv := by
  simp only [Cell.vTerm, ite_true, ev_sub, ev_scale, ev_var, cv, CoeffExpr.eval]

theorem ev_xTerm : (Cell.xTerm (F := F) true).ev δF eK eF =
    liftQ δF (eF.trace Cell.mx) * qvA δF eK Cell.xProvInv + liftQ δF (eF.trace Cell.mx1) * qvA δF eK Cell.xProvInv1 := by
  simp only [Cell.xTerm, ite_true, ev_add, ev_scale, ev_var, cv, CoeffExpr.eval]

/-- **One trace's round-1 facts** at a row with both child kinds `0`: the child fingerprints are the atom
fingerprints, and the parent's are determined by `consEqs`. -/
theorem atom_r1_facts (hq : ∀ e ∈ Cell.qEqs δF, e.ev δF eK eF = 0)
    (hwL : eF.trace Cell.wL = 0) (hwR : eF.trace Cell.wR = 0) :
    qvA δF eK Cell.lR = zv δF eK ∧ qvA δF eK (Cell.lR + 2) = 0 ∧
      qvA δF eK (Cell.lR + 4) = liftQ δF (eF.trace Cell.aL) ∧
    qvA δF eK Cell.rR = zv δF eK ∧ qvA δF eK (Cell.rR + 2) = 0 ∧
      qvA δF eK (Cell.rR + 4) = liftQ δF (eF.trace Cell.aR) ∧
    qvA δF eK Cell.pR = qvA δF eK Cell.lR * qvA δF eK Cell.rR ∧
    qvA δF eK (Cell.pR + 4) = qvA δF eK (Cell.lR + 4) + qvA δF eK Cell.lR * qvA δF eK (Cell.rR + 4) ∧
    zv δF eK * qvA δF eK (Cell.pR + 2) =
      zv δF eK * zv δF eK * qvA δF eK (Cell.lR + 2) + qvA δF eK Cell.lR * qvA δF eK Cell.lR +
        zv δF eK * (qvA δF eK Cell.lR * qvA δF eK Cell.lR) * qvA δF eK (Cell.rR + 2) := by
  have hL1 : (notE (cv Cell.wL) : CoeffExpr F).eval eF = 1 := by simp [notE, cv, CoeffExpr.eval, hwL]
  have hR1 : (notE (cv Cell.wR) : CoeffExpr F).eval eF = 1 := by simp [notE, cv, CoeffExpr.eval, hwR]
  have a1 := scale1 δF hL1 (hq (QE.scale (notE (cv Cell.wL)) (QE.sub (QE.var Cell.lR) zQ))
    (by simp [Cell.qEqs, Cell.atomEqs, QFP.var]))
  have a2 := scale1 δF hL1 (hq (QE.scale (notE (cv Cell.wL)) (QE.var (Cell.lR + 2)))
    (by simp [Cell.qEqs, Cell.atomEqs, QFP.var]))
  have a3 := scale1 δF hL1 (hq (QE.scale (notE (cv Cell.wL)) (QE.sub (QE.var (Cell.lR + 4)) (QE.base (cv Cell.aL))))
    (by simp [Cell.qEqs, Cell.atomEqs, QFP.var]))
  have b1 := scale1 δF hR1 (hq (QE.scale (notE (cv Cell.wR)) (QE.sub (QE.var Cell.rR) zQ))
    (by simp [Cell.qEqs, Cell.atomEqs, QFP.var]))
  have b2 := scale1 δF hR1 (hq (QE.scale (notE (cv Cell.wR)) (QE.var (Cell.rR + 2)))
    (by simp [Cell.qEqs, Cell.atomEqs, QFP.var]))
  have b3 := scale1 δF hR1 (hq (QE.scale (notE (cv Cell.wR)) (QE.sub (QE.var (Cell.rR + 4)) (QE.base (cv Cell.aR))))
    (by simp [Cell.qEqs, Cell.atomEqs, QFP.var]))
  have c1 := hq (QE.sub (QE.var Cell.pR) (QE.mul δF (QE.var Cell.lR) (QE.var Cell.rR)))
    (by simp [Cell.qEqs, Cell.consEqs, QFP.var])
  have c2 := hq (QE.sub (QE.var (Cell.pR + 4)) (QE.add (QE.var (Cell.lR + 4))
    (QE.mul δF (QE.var Cell.lR) (QE.var (Cell.rR + 4)))))
    (by simp [Cell.qEqs, Cell.consEqs, QFP.var])
  have c3 := hq (QE.sub (QE.mul δF zQ (QE.var (Cell.pR + 2))) (QE.add (QE.add
    (QE.mul δF (QE.mul δF zQ zQ) (QE.var (Cell.lR + 2))) (QE.mul δF (QE.var Cell.lR) (QE.var Cell.lR)))
    (QE.mul δF (QE.mul δF zQ (QE.mul δF (QE.var Cell.lR) (QE.var Cell.lR))) (QE.var (Cell.rR + 2)))))
    (by simp [Cell.qEqs, Cell.consEqs, QFP.var])
  simp only [ev_sub, ev_var, zQ, ev_chal, ev_base, ev_add, ev_mul, sub_eq_zero] at a1 a2 a3 b1 b2 b3 c1 c2 c3
  refine ⟨a1, a2, a3, b1, b2, b3, c1, c2, ?_⟩
  simpa using c3


/-- **Round 1 is determined.** Two rows with the same round-0 `aL`, `aR`, both child kinds `0`, at one coin
`z′ ≠ 0`, have the same `p`, `l`, `r` fingerprints (roles `0 .. 17`). -/
theorem atom_r1_eq (hq : ∀ e ∈ Cell.qEqs δF, e.ev δF eK eF = 0) (hq' : ∀ e ∈ Cell.qEqs δF, e.ev δF eK' eF' = 0)
    (hwL : eF.trace Cell.wL = 0) (hwR : eF.trace Cell.wR = 0)
    (hwL' : eF'.trace Cell.wL = 0) (hwR' : eF'.trace Cell.wR = 0)
    (haL : eF.trace Cell.aL = eF'.trace Cell.aL) (haR : eF.trace Cell.aR = eF'.trace Cell.aR)
    (hc : eK.chal = eK'.chal) (hz : zv δF eK ≠ 0) :
    ∀ r < 18, eK.trace r = eK'.trace r := by
  obtain ⟨a1, a2, a3, b1, b2, b3, c1, c2, c3⟩ := atom_r1_facts δF hq hwL hwR
  obtain ⟨a1', a2', a3', b1', b2', b3', c1', c2', c3'⟩ := atom_r1_facts δF hq' hwL' hwR'
  have hzz : zv δF eK = zv δF eK' := by simp only [zv, hc]
  have e6 : qvA δF eK Cell.lR = qvA δF eK' Cell.lR := by rw [a1, a1', hzz]
  have e8 : qvA δF eK (Cell.lR + 2) = qvA δF eK' (Cell.lR + 2) := by rw [a2, a2']
  have e10 : qvA δF eK (Cell.lR + 4) = qvA δF eK' (Cell.lR + 4) := by rw [a3, a3', haL]
  have e12 : qvA δF eK Cell.rR = qvA δF eK' Cell.rR := by rw [b1, b1', hzz]
  have e14 : qvA δF eK (Cell.rR + 2) = qvA δF eK' (Cell.rR + 2) := by rw [b2, b2']
  have e16 : qvA δF eK (Cell.rR + 4) = qvA δF eK' (Cell.rR + 4) := by rw [b3, b3', haR]
  have e0 : qvA δF eK Cell.pR = qvA δF eK' Cell.pR := by rw [c1, c1', e6, e12]
  have e4 : qvA δF eK (Cell.pR + 4) = qvA δF eK' (Cell.pR + 4) := by rw [c2, c2', e10, e6, e16]
  have e2 : qvA δF eK (Cell.pR + 2) = qvA δF eK' (Cell.pR + 2) := by
    refine mul_left_cancel₀ hz ?_
    rw [c3, hzz, c3', e6, e8, e14]
  have hp : ∀ m < 9, qvA δF eK (2 * m) = qvA δF eK' (2 * m) := by
    intro m hm
    interval_cases m
    · exact e0
    · exact e2
    · exact e4
    · exact e6
    · exact e8
    · exact e10
    · exact e12
    · exact e14
    · exact e16
  intro r hr
  have h := qv_eq δF (hp (r / 2) (by omega))
  rcases Nat.mod_two_eq_zero_or_one r with h0 | h1
  · have : 2 * (r / 2) = r := by omega
    rw [this] at h
    exact h.1
  · have : 2 * (r / 2) + 1 = r := by omega
    rw [this] at h
    exact h.2


theorem ev_scale_var {c : CoeffExpr F} {r : ℕ} :
    (QE.scale c (QE.var r : QE F)).ev δF eK eF = liftQ δF (c.eval eF) * qvA δF eK r := by
  rw [ev_scale, ev_var]

/-- **Round 2 is determined.** Given equal round-1 roles `< 18`, equal round-0 columns `< 205`, the first and
last row flags `1` and both child kinds `0`, the round-2 roles `18 .. 47` agree. -/
theorem atom_r2_eq (hq : ∀ e ∈ atomAllQ δF, e.ev δF eK eF = 0) (hq' : ∀ e ∈ atomAllQ δF, e.ev δF eK' eF' = 0)
    (hF1 : eF.trace Cell.isF = 1) (hF1' : eF'.trace Cell.isF = 1)
    (hwL : eF.trace Cell.wL = 0) (hwR : eF.trace Cell.wR = 0)
    (hwL' : eF'.trace Cell.wL = 0) (hwR' : eF'.trace Cell.wR = 0)
    (hFt : ∀ j < 205, eF.trace j = eF'.trace j) (hK : ∀ r < 18, eK.trace r = eK'.trace r)
    (hc : eK.chal = eK'.chal) :
    ∀ r, 18 ≤ r → r < 48 → eK.trace r = eK'.trace r := by
  have hL1 : (notE (cv Cell.wL) : CoeffExpr F).eval eF = 1 := by simp [notE, cv, CoeffExpr.eval, hwL]
  have hR1 : (notE (cv Cell.wR) : CoeffExpr F).eval eF = 1 := by simp [notE, cv, CoeffExpr.eval, hwR]
  have hL1' : (notE (cv Cell.wL) : CoeffExpr F).eval eF' = 1 := by simp [notE, cv, CoeffExpr.eval, hwL']
  have hR1' : (notE (cv Cell.wR) : CoeffExpr F).eval eF' = 1 := by simp [notE, cv, CoeffExpr.eval, hwR']
  have mem : ∀ e : QE F, (e ∈ Cell.qEqs δF ∨ e ∈ CellHQ.gatesQ δF ∨ e ∈ atomQ δF) → e ∈ atomAllQ δF := by
    intro e he
    simp only [atomAllQ, List.mem_append]
    tauto
  have cong : ∀ e : QE F, curM 18 205 e.re = true → curM 18 205 e.im = true →
      e.ev δF eK eF = e.ev δF eK' eF' := fun e h1 h2 => ev_congr_cur δF h1 h2 hK hc hFt
  -- inverses
  have inv : ∀ (r : ℕ) (D : QE F), curM 18 205 D.re = true → curM 18 205 D.im = true →
      (QE.sub (QE.mul δF (QE.var r) D) QE.one) ∈ atomAllQ δF → qvA δF eK r = qvA δF eK' r := by
    intro r D h1 h2 hm
    exact inv_pair δF (gate_inv δF (hq _ hm)) (gate_inv δF (hq' _ hm)) (cong D h1 h2)
  have e18 : qvA δF eK Cell.vProvInv = qvA δF eK' Cell.vProvInv :=
    inv _ (den δF Cell.vKeyP) rfl rfl (mem _ (Or.inl (by simp [Cell.qEqs])))
  have e24 : qvA δF eK Cell.xProvInv = qvA δF eK' Cell.xProvInv :=
    inv _ (den δF (Cell.xKeyS 0)) rfl rfl (mem _ (Or.inl (by simp [Cell.qEqs])))
  have e30 : qvA δF eK Cell.xProvInv1 = qvA δF eK' Cell.xProvInv1 :=
    inv _ (den δF (Cell.xKeyS 1)) rfl rfl (mem _ (Or.inl (by simp [Cell.qEqs])))
  have e32 : qvA δF eK CellHQ.invHQ = qvA δF eK' CellHQ.invHQ :=
    inv _ (HQ.denKeyQ δF CellH.keyH) rfl rfl (mem _ (Or.inr (Or.inl (by simp [CellHQ.gatesQ]))))
  have e36 : qvA δF eK mbInv = qvA δF eK' mbInv :=
    inv _ (den δF mbKey) rfl rfl (mem _ (Or.inr (Or.inr (by simp [atomQ]))))
  have e40 : qvA δF eK cInv = qvA δF eK' cInv :=
    inv _ (HQ.denKeyQ δF oldKey) rfl rfl (mem _ (Or.inr (Or.inr (by simp [atomQ]))))
  have e42 : qvA δF eK miInv = qvA δF eK' miInv :=
    inv _ (HQ.denKeyQ δF incKey) rfl rfl (mem _ (Or.inr (Or.inr (by simp [atomQ]))))
  -- the zero inverses
  have z20 : qvA δF eK Cell.consLInv = 0 := by
    have := scale1 δF hL1 (hq _ (mem (QE.scale (notE (cv Cell.wL)) (QE.var Cell.consLInv))
      (Or.inl (by simp [Cell.qEqs]))))
    rwa [ev_var] at this
  have z20' : qvA δF eK' Cell.consLInv = 0 := by
    have := scale1 δF hL1' (hq' _ (mem (QE.scale (notE (cv Cell.wL)) (QE.var Cell.consLInv))
      (Or.inl (by simp [Cell.qEqs]))))
    rwa [ev_var] at this
  have z22 : qvA δF eK Cell.consRInv = 0 := by
    have := scale1 δF hR1 (hq _ (mem (QE.scale (notE (cv Cell.wR)) (QE.var Cell.consRInv))
      (Or.inl (by simp [Cell.qEqs]))))
    rwa [ev_var] at this
  have z22' : qvA δF eK' Cell.consRInv = 0 := by
    have := scale1 δF hR1' (hq' _ (mem (QE.scale (notE (cv Cell.wR)) (QE.var Cell.consRInv))
      (Or.inl (by simp [Cell.qEqs]))))
    rwa [ev_var] at this
  have e20 : qvA δF eK Cell.consLInv = qvA δF eK' Cell.consLInv := by rw [z20, z20']
  have e22 : qvA δF eK Cell.consRInv = qvA δF eK' Cell.consRInv := by rw [z22, z22']
  -- accumulators (one row: `acc = term`)
  have acc : ∀ (a : ℕ) (T : QE F), (QE.scale (cv Cell.isF) (QE.sub (QE.var a) T)) ∈ atomAllQ δF →
      qvA δF eK a = T.ev δF eK eF ∧ qvA δF eK' a = T.ev δF eK' eF' := fun a T hm =>
    ⟨gate_first δF hF1 (hq _ hm), gate_first δF hF1' (hq' _ hm)⟩
  have e26 : qvA δF eK Cell.vAcc = qvA δF eK' Cell.vAcc := by
    obtain ⟨g, g'⟩ := acc Cell.vAcc (Cell.vTerm true) (mem _ (Or.inl (by simp [Cell.qEqs])))
    rw [g, g', ev_vTerm, ev_vTerm, hFt Cell.mv (by decide), e18, e20, e22]
  have e28 : qvA δF eK Cell.xAcc = qvA δF eK' Cell.xAcc := by
    obtain ⟨g, g'⟩ := acc Cell.xAcc (Cell.xTerm true) (mem _ (Or.inl (by simp [Cell.qEqs])))
    rw [g, g', ev_xTerm, ev_xTerm, hFt Cell.mx (by decide), hFt Cell.mx1 (by decide), e24, e30]
  have e34 : qvA δF eK CellHQ.accHQ = qvA δF eK' CellHQ.accHQ := by
    obtain ⟨g, g'⟩ := acc CellHQ.accHQ (QE.scale (cv CellH.mh) (QE.var CellHQ.invHQ))
      (mem _ (Or.inr (Or.inl (by simp [CellHQ.gatesQ]))))
    rw [g, g', ev_scale_var, ev_scale_var, e32]
    simp only [cv, CoeffExpr.eval, hFt CellH.mh (by decide)]
  have e38 : qvA δF eK mbAcc = qvA δF eK' mbAcc := by
    obtain ⟨g, g'⟩ := acc mbAcc (QE.scale (cv mb) (QE.var mbInv)) (mem _ (Or.inr (Or.inr (by simp [atomQ]))))
    rw [g, g', ev_scale_var, ev_scale_var, e36]
    simp only [cv, CoeffExpr.eval, hFt mb (by decide)]
  have e44 : qvA δF eK miAcc = qvA δF eK' miAcc := by
    obtain ⟨g, g'⟩ := acc miAcc (QE.scale (cv mi) (QE.var miInv)) (mem _ (Or.inr (Or.inr (by simp [atomQ]))))
    rw [g, g', ev_scale_var, ev_scale_var, e42]
    simp only [cv, CoeffExpr.eval, hFt mi (by decide)]
  have e46 : qvA δF eK cAcc = qvA δF eK' cAcc := by
    obtain ⟨g, g'⟩ := acc cAcc (QE.scale (cv inc) (QE.var cInv)) (mem _ (Or.inr (Or.inr (by simp [atomQ]))))
    rw [g, g', ev_scale_var, ev_scale_var, e40]
    simp only [cv, CoeffExpr.eval, hFt inc (by decide)]
  have hp : ∀ m, 9 ≤ m → m < 24 → qvA δF eK (2 * m) = qvA δF eK' (2 * m) := by
    intro m h9 h24
    interval_cases m
    · exact e18
    · exact e20
    · exact e22
    · exact e24
    · exact e26
    · exact e28
    · exact e30
    · exact e32
    · exact e34
    · exact e36
    · exact e38
    · exact e40
    · exact e42
    · exact e44
    · exact e46
  intro r h18 h48
  have h := qv_eq δF (hp (r / 2) (by omega) (by omega))
  rcases Nat.mod_two_eq_zero_or_one r with h0 | h1
  · have : 2 * (r / 2) = r := by omega
    rw [this] at h
    exact h.1
  · have : 2 * (r / 2) + 1 = r := by omega
    rw [this] at h
    exact h.2


/-! ## 3. The terminal gates: the publics `0 .. 11` -/

/-- **The publics `0 .. 11` are determined by the roles.** The six terminal gates `isL·(acc − pub)` of the atom
table (validity `0`, export `2`, handle export `4`, external validity `6`, inc record `8`, consume `10`) make each
public pair the accumulator's value at the last row; equal roles give equal publics. -/
theorem atom_pubs_env (hq : ∀ e ∈ atomAllQ δF, e.ev δF eK eF = 0) (hq' : ∀ e ∈ atomAllQ δF, e.ev δF eK' eF' = 0)
    (hL : eF.trace Cell.isL = 1) (hL' : eF'.trace Cell.isL = 1) (hK : ∀ r < 48, eK.trace r = eK'.trace r) :
    ∀ j < 12, eK.pub j = eK'.pub j := by
  have mem : ∀ e : QE F, (e ∈ Cell.qEqs δF ∨ e ∈ CellHQ.gatesQ δF ∨ e ∈ atomQ δF) → e ∈ atomAllQ δF := by
    intro e he
    simp only [atomAllQ, List.mem_append]
    tauto
  have pr : ∀ r j : ℕ, r + 1 < 48 →
      (QE.scale (cv Cell.isL) (QE.sub (QE.var r) (QE.pub j)) : QE F) ∈ atomAllQ δF →
      eK.pub j = eK'.pub j ∧ eK.pub (j + 1) = eK'.pub (j + 1) := by
    intro r j hr hm
    obtain ⟨a, b⟩ := terminal_pub δF eK eF Cell.isL r j hL (hq _ hm)
    obtain ⟨a', b'⟩ := terminal_pub δF eK' eF' Cell.isL r j hL' (hq' _ hm)
    exact ⟨by rw [a, a', hK r (by omega)], by rw [b, b', hK (r + 1) hr]⟩
  have h0 := pr Cell.vAcc 0 (by decide) (mem _ (Or.inl (by simp [Cell.qEqs])))
  have h2 := pr Cell.xAcc 2 (by decide) (mem _ (Or.inl (by simp [Cell.qEqs])))
  have h4 := pr CellHQ.accHQ CellHQ.pubHQ (by decide) (mem _ (Or.inr (Or.inl (by simp [CellHQ.gatesQ]))))
  have h6 := pr mbAcc pubMB (by decide) (mem _ (Or.inr (Or.inr (by simp [atomQ]))))
  have h8 := pr miAcc pubMI (by decide) (mem _ (Or.inr (Or.inr (by simp [atomQ]))))
  have h10 := pr cAcc pubC (by decide) (mem _ (Or.inr (Or.inr (by simp [atomQ]))))
  intro j hj
  interval_cases j
  · exact h0.1
  · exact h0.2
  · exact h2.1
  · exact h2.2
  · exact h4.1
  · exact h4.2
  · exact h6.1
  · exact h6.2
  · exact h8.1
  · exact h8.2
  · exact h10.1
  · exact h10.2

/-- **The whole atom row is determined** (`48` roles), from the round-0 columns and the coin. -/
theorem atom_env_eq (hq : ∀ e ∈ atomAllQ δF, e.ev δF eK eF = 0) (hq' : ∀ e ∈ atomAllQ δF, e.ev δF eK' eF' = 0)
    (hF1 : eF.trace Cell.isF = 1) (hF1' : eF'.trace Cell.isF = 1)
    (hwL : eF.trace Cell.wL = 0) (hwR : eF.trace Cell.wR = 0)
    (hwL' : eF'.trace Cell.wL = 0) (hwR' : eF'.trace Cell.wR = 0)
    (hFt : ∀ j < 205, eF.trace j = eF'.trace j) (hc : eK.chal = eK'.chal) (hz : zv δF eK ≠ 0) :
    ∀ r < 48, eK.trace r = eK'.trace r := by
  have mq : ∀ e ∈ Cell.qEqs δF, e ∈ atomAllQ δF := fun e he => by
    simp only [atomAllQ, List.mem_append]; tauto
  have h1 := atom_r1_eq δF (fun e he => hq e (mq e he)) (fun e he => hq' e (mq e he)) hwL hwR hwL' hwR'
    (hFt _ (by decide)) (hFt _ (by decide)) hc hz
  have h2 := atom_r2_eq δF hq hq' hF1 hF1' hwL hwR hwL' hwR' hFt h1 hc
  intro r hr
  by_cases h : r < 18
  · exact h1 r h
  · exact h2 r (by omega) hr

end Env

/-! ## 4. The chip level -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- Row `i`'s base environment of an atom trace. -/
abbrev aEF {w : ℕ} (Q : Fin w → F[X]) (i : Fin n) : Env F :=
  Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 205 chals) (slotVal b 205 pubs)

/-- Row `i`'s gathered `𝕂` environment of an atom trace. -/
abbrev aEK {w : ℕ} (Q : Fin w → F[X]) (i : Fin n) : Env K :=
  gatherEnv b ((atomTemplateHQ δF).col0 3) (aEF b nodes orbit chals pubs Q i)

/-- **Every `𝕂′` equation of the atom table holds at every row of an accepted trace.** -/
theorem atom_row_gates (Q : Fin (atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    ∀ e ∈ atomAllQ δF, e.ev δF (aEK δF b nodes orbit chals pubs Q i) (aEF b nodes orbit chals pubs Q i) = 0 := by
  have hl := (expandChip_satisfies_iff_language (atomTemplateHQ δF) b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  intro e he
  refine ev_eq_zero_of_gates δF _ _ e fun g hg => hl.2.2.2 g ?_
  simp only [atomAllQ, List.mem_append] at he
  rcases he with (he | he) | he
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, he, hg⟩))
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hg⟩))
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hg⟩)

theorem aEF_trace {w : ℕ} (Q : Fin w → F[X]) (i : Fin n) {j : ℕ} (hj : j < w) :
    (aEF b nodes orbit chals pubs Q i).trace j = (Q ⟨j, hj⟩).eval (nodes i) :=
  envOfTrace_trace Q _ _ _ _ hj

theorem aEK_chal (Q : Fin (atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X]) (i : Fin n) (r : ℕ) :
    (aEK δF b nodes orbit chals pubs Q i).chal r = chals r :=
  gather_chal_T b (atomTemplateHQ δF) 205 (atomTemplateHQ_baseCols δF) _ chals rfl r

theorem aEK_pub (Q : Fin (atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X]) (i : Fin n) (r : ℕ) :
    (aEK δF b nodes orbit chals pubs Q i).pub r = pubs r :=
  gather_pub_T b (atomTemplateHQ δF) 205 (atomTemplateHQ_baseCols δF) _ pubs rfl r

/-- The round-0 pad columns at a row. -/
theorem aEF_pad {A : Fin 349 → F[X]} (hpad : ∀ j : Fin 349, (j : ℕ) < 205 → A j = Polynomial.C (padA j))
    (i : Fin n) {j : ℕ} (hj : j < 205) :
    (aEF b nodes orbit chals pubs
      (fun j => A (Fin.cast (atomChipHQ_width δF b hn nodes orbit chals pubs) j)) i).trace j = padA j := by
  rw [aEF_trace b nodes orbit chals pubs _ i (by rw [atomChipHQ_width]; omega)]
  have := hpad ⟨j, by omega⟩ hj
  simp only [Fin.cast_mk, this, Polynomial.eval_C]

variable {pubs}

/-- **The atom table's round-1 and round-2 columns are determined.** Two traces accepted by `atomChipHQ` (at one
coin, any publics), each carrying the pad row's round-0 columns, with `z′ ≠ 0`, agree on every column at every row
node. -/
theorem atom_cols_eq {pubs' : ℕ → K} {A A' : Fin 349 → F[X]}
    (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies
      (fun j => A (Fin.cast (atomChipHQ_width δF b hn nodes orbit chals pubs) j)))
    (hsat' : (atomChipHQ δF b hn nodes orbit chals pubs').rap.Satisfies
      (fun j => A' (Fin.cast (atomChipHQ_width δF b hn nodes orbit chals pubs') j)))
    (hpad : ∀ j : Fin 349, (j : ℕ) < 205 → A j = Polynomial.C (padA j))
    (hpad' : ∀ j : Fin 349, (j : ℕ) < 205 → A' j = Polynomial.C (padA j))
    (hz : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ≠ 0) :
    ∀ (j : Fin 349) (i : Fin n), (A j).eval (nodes i) = (A' j).eval (nodes i) := by
  intro j i
  set Q := fun j => A (Fin.cast (atomChipHQ_width δF b hn nodes orbit chals pubs) j) with hQ
  set Q' := fun j => A' (Fin.cast (atomChipHQ_width δF b hn nodes orbit chals pubs') j) with hQ'
  have hp := fun j hj => aEF_pad δF b hn nodes orbit chals (pubs := pubs) hpad i (j := j) hj
  have hp' := fun j hj => aEF_pad δF b hn nodes orbit chals (pubs := pubs') hpad' i (j := j) hj
  by_cases hj : (j : ℕ) < 205
  · rw [hpad j hj, hpad' j hj]
  · have hzz : zv δF (aEK δF b nodes orbit chals pubs Q i) ≠ 0 := by
      simp only [zv, aEK_chal]; exact hz
    have hK := atom_env_eq δF (atom_row_gates δF b hn nodes orbit chals pubs Q hsat i)
      (atom_row_gates δF b hn nodes orbit chals pubs' Q' hsat' i)
      (by rw [hp _ (by decide)]; simp [padA, Cell.isF, Cell.isL, Cell.wL, Cell.wR]) (by rw [hp' _ (by decide)]; simp [padA, Cell.isF, Cell.isL, Cell.wL, Cell.wR])
      (by rw [hp _ (by decide)]; simp [padA, Cell.isF, Cell.isL, Cell.wL, Cell.wR]) (by rw [hp _ (by decide)]; simp [padA, Cell.isF, Cell.isL, Cell.wL, Cell.wR])
      (by rw [hp' _ (by decide)]; simp [padA, Cell.isF, Cell.isL, Cell.wL, Cell.wR]) (by rw [hp' _ (by decide)]; simp [padA, Cell.isF, Cell.isL, Cell.wL, Cell.wR])
      (fun j hj => by rw [hp j hj, hp' j hj])
      (by funext r; rw [aEK_chal, aEK_chal]) hzz
    have hr : ((j : ℕ) - 205) / 3 < 48 := by have := j.isLt; omega
    have hk : ((j : ℕ) - 205) % 3 < 3 := Nat.mod_lt _ (by omega)
    have h := trace_cols_eq_of_gather b ((atomTemplateHQ δF).col0 3)
      (aEF b nodes orbit chals pubs Q i) (aEF b nodes orbit chals pubs' Q' i) (((j : ℕ) - 205) / 3)
      (hK _ hr) ⟨((j : ℕ) - 205) % 3, hk⟩
    have hidx : (atomTemplateHQ δF).col0 3 VarKind.traceCur (((j : ℕ) - 205) / 3) + ((j : ℕ) - 205) % 3 = j := by
      simp only [ChipTemplate.col0, atomTemplateHQ_baseCols]
      omega
    simp only [hidx] at h
    rw [aEF_trace b nodes orbit chals pubs Q i (by rw [atomChipHQ_width]; exact j.isLt),
      aEF_trace b nodes orbit chals pubs' Q' i (by rw [atomChipHQ_width]; exact j.isLt)] at h
    exact h

/-- **The atom table's publics `0 .. 11` are determined.** The terminal gates make them the accumulators' last
values, which `atom_cols_eq` shows equal. -/
theorem atom_pubs_eq {pubs' : ℕ → K} {A A' : Fin 349 → F[X]}
    (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies
      (fun j => A (Fin.cast (atomChipHQ_width δF b hn nodes orbit chals pubs) j)))
    (hsat' : (atomChipHQ δF b hn nodes orbit chals pubs').rap.Satisfies
      (fun j => A' (Fin.cast (atomChipHQ_width δF b hn nodes orbit chals pubs') j)))
    (hpad : ∀ j : Fin 349, (j : ℕ) < 205 → A j = Polynomial.C (padA j))
    (hpad' : ∀ j : Fin 349, (j : ℕ) < 205 → A' j = Polynomial.C (padA j))
    (hz : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ≠ 0) :
    ∀ j < 12, pubs j = pubs' j := by
  intro j hj
  set Q := fun j => A (Fin.cast (atomChipHQ_width δF b hn nodes orbit chals pubs) j) with hQ
  set Q' := fun j => A' (Fin.cast (atomChipHQ_width δF b hn nodes orbit chals pubs') j) with hQ'
  let i : Fin n := ⟨0, hn⟩
  have hp := fun j hj => aEF_pad δF b hn nodes orbit chals (pubs := pubs) hpad i (j := j) hj
  have hp' := fun j hj => aEF_pad δF b hn nodes orbit chals (pubs := pubs') hpad' i (j := j) hj
  have hzz : zv δF (aEK δF b nodes orbit chals pubs Q i) ≠ 0 := by
    simp only [zv, aEK_chal]; exact hz
  have hq := atom_row_gates δF b hn nodes orbit chals pubs Q hsat i
  have hq' := atom_row_gates δF b hn nodes orbit chals pubs' Q' hsat' i
  have hK := atom_env_eq δF hq hq'
    (by rw [hp _ (by decide)]; simp [padA, Cell.isF, Cell.isL, Cell.wL, Cell.wR]) (by rw [hp' _ (by decide)]; simp [padA, Cell.isF, Cell.isL, Cell.wL, Cell.wR])
    (by rw [hp _ (by decide)]; simp [padA, Cell.isF, Cell.isL, Cell.wL, Cell.wR]) (by rw [hp _ (by decide)]; simp [padA, Cell.isF, Cell.isL, Cell.wL, Cell.wR])
    (by rw [hp' _ (by decide)]; simp [padA, Cell.isF, Cell.isL, Cell.wL, Cell.wR]) (by rw [hp' _ (by decide)]; simp [padA, Cell.isF, Cell.isL, Cell.wL, Cell.wR])
    (fun j hj => by rw [hp j hj, hp' j hj])
    (by funext r; rw [aEK_chal, aEK_chal]) hzz
  have := atom_pubs_env δF hq hq' (by rw [hp _ (by decide)]; simp [padA, Cell.isF, Cell.isL, Cell.wL, Cell.wR])
    (by rw [hp' _ (by decide)]; simp [padA, Cell.isF, Cell.isL, Cell.wL, Cell.wR]) hK j hj
  rwa [aEK_pub, aEK_pub] at this

end Chip

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsAtomP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsAtomP1.atom_r1_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsAtomP1.atom_r2_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsAtomP1.atom_pubs_env
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsAtomP1.atom_env_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsAtomP1.atom_cols_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsAtomP1.atom_pubs_eq
