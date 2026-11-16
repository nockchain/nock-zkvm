/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/RoundsWalkP1.lean

 **Trace uniqueness on the P1 fragment: the J-8 walk chip's rounds 1 and 2.**

 Two traces accepted by `walkChipJ8` at one coin, with the same round-0 columns (`< 25`) and the same
 fingerprint columns of round 1 (the four `𝕂′` labels `p l r root`, roles `0 .. 23`, fixed by the export
 consume and the path records, not by a gate), agree on every round-2 column: the positional `α`-RLC `ln`, the
 count `cnt`, the accumulator `acc`, the old and handle inverses (each `inv · den = 1`, so `den ≠ 0` comes with
 the gate) and the four `𝕂′` accumulators. The terminal gates fix the walk publics `0 .. 7`.

 * §1 read sets: current-row and current-or-next-row (`curM_eval`, `rdM_eval`); no public is read.
 * §2 row families: the gates of an accepted trace as facts about row environments (`RowFam`), and the
 gate readouts (`ln`, `cnt`, `acc`, inverses, accumulators).
 * §3 determination by roles (`walk_env_eq`): `ln`, `cnt`, `acc`, then the inverses, then the accumulators.
 * §4 the terminal gates (`walk_pubs_env`).
 * §5 the chip level (`walk_cols_eq`, `walk_pubs_eq`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsWalkP1

noncomputable section

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH (gather_chal_T gather_pub_T masks_of gather_next_T)

/-! ## 1. Read sets -/

section Read
variable {F : Type} [Field F]

/-- A base expression reads only trace columns `< B`, current or next row (no coin, no public). -/
def rdC (B : ℕ) : CoeffExpr F → Bool
  | .const _ => true
  | .var .traceCur i => decide (i < B)
  | .var .traceNext i => decide (i < B)
  | .var .challenge _ => false
  | .var .publicVal _ => false
  | .add a b => rdC B a && rdC B b
  | .sub a b => rdC B a && rdC B b
  | .mul a b => rdC B a && rdC B b
  | .neg a => rdC B a
  | .pow a _ => rdC B a

/-- A mixed expression reads only `𝕂`-roles `< R` (current or next row), base columns `< B` and coins; no
public. -/
def rdM (R B : ℕ) : MixedExpr F → Bool
  | .Var .traceCur i => decide (i < R)
  | .Var .traceNext i => decide (i < R)
  | .Var .challenge _ => true
  | .Var .publicVal _ => false
  | .Lift g => rdC B g
  | .Scale g u => rdC B g && rdM R B u
  | .Const _ => true
  | .Add x y => rdM R B x && rdM R B y
  | .Sub x y => rdM R B x && rdM R B y
  | .Neg x => rdM R B x
  | .Mul x y => rdM R B x && rdM R B y
  | .Pow x _ => rdM R B x

/-- The same, current row only. -/
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

theorem rdC_eval {B : ℕ} {g : CoeffExpr F} (hg : rdC B g = true) {e e' : Env F}
    (ht : ∀ j < B, e.trace j = e'.trace j) (hn : ∀ j < B, e.traceNext j = e'.traceNext j) :
    g.eval e = g.eval e' := by
  induction g with
  | const c => rfl
  | var k i =>
    cases k <;> simp only [rdC, decide_eq_true_eq, Bool.false_eq_true] at hg <;> simp only [CoeffExpr.eval]
    · exact ht i hg
    · exact hn i hg
  | add a b iha ihb =>
    simp only [rdC, Bool.and_eq_true] at hg
    simp only [CoeffExpr.eval, iha hg.1, ihb hg.2]
  | sub a b iha ihb =>
    simp only [rdC, Bool.and_eq_true] at hg
    simp only [CoeffExpr.eval, iha hg.1, ihb hg.2]
  | mul a b iha ihb =>
    simp only [rdC, Bool.and_eq_true] at hg
    simp only [CoeffExpr.eval, iha hg.1, ihb hg.2]
  | neg a iha =>
    simp only [rdC] at hg
    simp only [CoeffExpr.eval, iha hg]
  | pow a m iha =>
    simp only [rdC] at hg
    simp only [CoeffExpr.eval, iha hg]

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

theorem rdM_eval {R B : ℕ} {g : MixedExpr F} (hg : rdM R B g = true) {eK eK' : Env K}
    {eF eF' : Env F} (hKt : ∀ i < R, eK.trace i = eK'.trace i)
    (hKn : ∀ i < R, eK.traceNext i = eK'.traceNext i) (hKc : eK.chal = eK'.chal)
    (hFt : ∀ j < B, eF.trace j = eF'.trace j) (hFn : ∀ j < B, eF.traceNext j = eF'.traceNext j) :
    g.eval eK eF = g.eval eK' eF' := by
  induction g with
  | Var k i =>
    cases k <;> simp only [rdM, decide_eq_true_eq, Bool.false_eq_true] at hg <;> simp only [MixedExpr.eval]
    · exact hKt i hg
    · exact hKn i hg
    · rw [hKc]
  | Lift g =>
    simp only [rdM] at hg
    simp only [MixedExpr.eval, rdC_eval hg hFt hFn]
  | Scale g u ih =>
    simp only [rdM, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, rdC_eval hg.1 hFt hFn, ih hg.2]
  | Const c => rfl
  | Add x y ihx ihy =>
    simp only [rdM, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, ihx hg.1, ihy hg.2]
  | Sub x y ihx ihy =>
    simp only [rdM, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, ihx hg.1, ihy hg.2]
  | Neg x ih =>
    simp only [rdM] at hg
    simp only [MixedExpr.eval, ih hg]
  | Mul x y ihx ihy =>
    simp only [rdM, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, ihx hg.1, ihy hg.2]
  | Pow x m ih =>
    simp only [rdM] at hg
    simp only [MixedExpr.eval, ih hg]

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

end Read

/-! ## 2. Row families and gate readouts -/

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The `𝕂′` value of the `𝕂`-roles `r`, `r + 1`. -/
abbrev qvA (eK : Env K) (r : ℕ) : 𝕂′ := Quad.mk _ (eK.trace r) (eK.trace (r + 1))

/-- The `𝕂′` equations of the J-8 walk: the old IO gates and the handle gates. -/
def walkAllQ : List (QE F) := WChip.qEqs δF ++ WalkHQ.gatesQ δF

/-- **The gates of an accepted walk trace as facts about row environments.** Row `i < n` has the `𝕂`
environment `eK i` and the base environment `eF i`; the coins are `ch` at every row; the next-row columns of
row `i` are the columns of row `i + 1`; `isFirst` and `isLast` are the endpoint masks. -/
structure RowFam (kroots n : ℕ) (ch : ℕ → K) (eK : ℕ → Env K) (eF : ℕ → Env F) : Prop where
  gates : ∀ i, i < n → ∀ g ∈ WChip.walkGates (F := F) kroots, g.eval (eK i) (eF i) = 0
  qg : ∀ i, i < n → ∀ e ∈ walkAllQ δF, e.ev δF (eK i) (eF i) = 0
  chal : ∀ i, (eK i).chal = ch
  nextK : ∀ i, i + 1 < n → ∀ r, (eK i).traceNext r = (eK (i + 1)).trace r
  nextF : ∀ i, i + 1 < n → ∀ j, (eF i).traceNext j = (eF (i + 1)).trace j
  isF : ∀ i, i < n → (eF i).trace WChip.isF = if i = 0 then 1 else 0
  isL : ∀ i, i < n → (eF i).trace WChip.isL = if i + 1 = n then 1 else 0

variable {kroots n : ℕ} {ch : ℕ → K} {eK : ℕ → Env K} {eF : ℕ → Env F}

theorem scaleK1 {c : CoeffExpr F} {X : MixedExpr F} {eK : Env K} {eF : Env F} (hc : c.eval eF = 1)
    (h : (MixedExpr.Scale c X).eval eK eF = 0) : X.eval eK eF = 0 := by
  simp only [MixedExpr.eval, hc, map_one, one_mul] at h
  exact h

theorem scale1Q {c : CoeffExpr F} {a : QE F} {eK : Env K} {eF : Env F} (hc : c.eval eF = 1)
    (h : (QE.scale c a).ev δF eK eF = 0) : a.ev δF eK eF = 0 := by
  rw [ev_scale, hc] at h
  simpa [liftQ] using h

theorem RowFam.isF0 (R : RowFam δF kroots n ch eK eF) (hn : 0 < n) :
    (cv WChip.isF : CoeffExpr F).eval (eF 0) = 1 := by
  simp [cv, CoeffExpr.eval, R.isF 0 hn]

theorem RowFam.notL (R : RowFam δF kroots n ch eK eF) {i : ℕ} (hi : i + 1 < n) :
    (notE (cv WChip.isL) : CoeffExpr F).eval (eF i) = 1 := by
  have := R.isL i (by omega)
  simp [notE, cv, CoeffExpr.eval, this, show i + 1 ≠ n by omega]

theorem RowFam.ln0 (R : RowFam δF kroots n ch eK eF) (hn : 0 < n) : (eK 0).trace WChip.lnR = ch 0 := by
  have g := R.gates 0 hn (MixedExpr.Scale (cv WChip.isF) (MixedExpr.Sub (WChip.vC WChip.lnR) WChip.αE))
    (by simp [WChip.walkGates])
  have := scaleK1 (R.isF0 δF hn) g
  simp only [WChip.vC, WChip.αE, MixedExpr.eval, sub_eq_zero, R.chal] at this
  exact this

theorem RowFam.lnS (R : RowFam δF kroots n ch eK eF) {i : ℕ} (hi : i + 1 < n) :
    (eK (i + 1)).trace WChip.lnR = ch 0 * (eK i).trace WChip.lnR := by
  have g := R.gates i (by omega) (MixedExpr.Scale (notE (cv WChip.isL))
    (MixedExpr.Sub (WChip.vN WChip.lnR) (MixedExpr.Mul WChip.αE (WChip.vC WChip.lnR))))
    (by simp [WChip.walkGates])
  have := scaleK1 (R.notL δF hi) g
  simp only [WChip.vC, WChip.vN, WChip.αE, MixedExpr.eval, sub_eq_zero, R.chal, R.nextK i hi] at this
  exact this

theorem RowFam.cnt0 (R : RowFam δF kroots n ch eK eF) (hn : 0 < n) :
    (eK 0).trace WChip.cntR = ch 0 ^ kroots * (WChip.afoW cv).eval (eK 0) (eF 0) := by
  have g := R.gates 0 hn (MixedExpr.Scale (cv WChip.isF) (MixedExpr.Sub (WChip.vC WChip.cntR)
    (MixedExpr.Mul (WChip.αk kroots) (WChip.afoW cv)))) (by simp [WChip.walkGates])
  have := scaleK1 (R.isF0 δF hn) g
  simp only [WChip.vC, WChip.αk, WChip.αE, MixedExpr.eval, sub_eq_zero, R.chal] at this
  exact this

theorem RowFam.cntS (R : RowFam δF kroots n ch eK eF) {i : ℕ} (hi : i + 1 < n) :
    (eK (i + 1)).trace WChip.cntR = (eK i).trace WChip.cntR * (WChip.afoW nv).eval (eK i) (eF i) := by
  have g := R.gates i (by omega) (MixedExpr.Scale (notE (cv WChip.isL))
    (MixedExpr.Sub (WChip.vN WChip.cntR) (MixedExpr.Mul (WChip.vC WChip.cntR) (WChip.afoW nv))))
    (by simp [WChip.walkGates])
  have := scaleK1 (R.notL δF hi) g
  simp only [WChip.vC, WChip.vN, MixedExpr.eval, sub_eq_zero, R.nextK i hi] at this
  exact this

theorem RowFam.acc0 (R : RowFam δF kroots n ch eK eF) (hn : 0 < n) :
    (eK 0).trace WChip.accR = ch 0 ^ kroots * (WChip.ccW .traceCur cv).eval (eK 0) (eF 0) := by
  have g := R.gates 0 hn (MixedExpr.Scale (cv WChip.isF) (MixedExpr.Sub (WChip.vC WChip.accR)
    (MixedExpr.Mul (WChip.αk kroots) (WChip.ccW .traceCur cv)))) (by simp [WChip.walkGates])
  have := scaleK1 (R.isF0 δF hn) g
  simp only [WChip.vC, WChip.αk, WChip.αE, MixedExpr.eval, sub_eq_zero, R.chal] at this
  exact this

theorem RowFam.accS (R : RowFam δF kroots n ch eK eF) {i : ℕ} (hi : i + 1 < n) :
    (eK (i + 1)).trace WChip.accR - (eK i).trace WChip.accR =
      (MixedExpr.Mul (WChip.vC WChip.cntR) (WChip.ccW .traceNext nv) : MixedExpr F).eval (eK i) (eF i) -
      (MixedExpr.Scale (notE (nv WChip.rM)) (MixedExpr.Mul (WChip.vN WChip.lnR)
        (WChip.curW .traceNext nv)) : MixedExpr F).eval (eK i) (eF i) := by
  have g := R.gates i (by omega) (MixedExpr.Scale (notE (cv WChip.isL))
    (MixedExpr.Sub (MixedExpr.Add (MixedExpr.Scale (notE (nv WChip.rM)) (MixedExpr.Mul (WChip.vN WChip.lnR)
      (WChip.curW .traceNext nv))) (MixedExpr.Sub (WChip.vN WChip.accR) (WChip.vC WChip.accR)))
      (MixedExpr.Mul (WChip.vC WChip.cntR) (WChip.ccW .traceNext nv)))) (by simp [WChip.walkGates])
  have := scaleK1 (R.notL δF hi) g
  simp only [MixedExpr.eval, WChip.vC, WChip.vN, R.nextK i hi] at this ⊢
  linear_combination this

theorem RowFam.invQ (R : RowFam δF kroots n ch eK eF) {i : ℕ} (hi : i < n) {r : ℕ} {D : QE F}
    (hm : (QE.sub (QE.mul δF (QE.var r) D) QE.one : QE F) ∈ walkAllQ δF) :
    qvA δF (eK i) r * D.ev δF (eK i) (eF i) = 1 := by
  have h := R.qg i hi _ hm
  rw [ev_sub, ev_mul, ev_var, ev_one, sub_eq_zero] at h
  exact h

theorem RowFam.initQ (R : RowFam δF kroots n ch eK eF) (hn : 0 < n) {a : ℕ} {T : QE F}
    (hm : (QE.scale (cv WChip.isF) (QE.sub (QE.var a) T) : QE F) ∈ walkAllQ δF) :
    qvA δF (eK 0) a = T.ev δF (eK 0) (eF 0) := by
  have h := scale1Q δF (R.isF0 δF hn) (R.qg 0 hn _ hm)
  rw [ev_sub, ev_var, sub_eq_zero] at h
  exact h

theorem RowFam.stepQ (R : RowFam δF kroots n ch eK eF) {i : ℕ} (hi : i + 1 < n) {a : ℕ} {T : QE F}
    (hm : (QE.scale (notE (cv WChip.isL)) (QE.sub (QE.sub (QE.next a) (QE.var a)) T) : QE F) ∈ walkAllQ δF) :
    qvA δF (eK (i + 1)) a - qvA δF (eK i) a = T.ev δF (eK i) (eF i) := by
  have h := scale1Q δF (R.notL δF hi) (R.qg i (by omega) _ hm)
  rw [ev_sub, ev_sub, ev_next, ev_var, sub_eq_zero] at h
  rw [R.nextK i hi, R.nextK i hi] at h
  exact h

theorem RowFam.termQ (R : RowFam δF kroots n ch eK eF) {i : ℕ} (hi : i < n) (hL : i + 1 = n) {a j : ℕ}
    (hm : (QE.scale (cv WChip.isL) (QE.sub (QE.var a) (QE.pub j)) : QE F) ∈ walkAllQ δF) :
    (eK i).pub j = (eK i).trace a ∧ (eK i).pub (j + 1) = (eK i).trace (a + 1) :=
  terminal_pub δF (eK i) (eF i) WChip.isL a j (by simp [R.isL i hi, hL]) (R.qg i hi _ hm)

end Rows

/-! ## 3. Determination by roles -/

section Det
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]
  {kroots n : ℕ} {ch : ℕ → K} {eK eK' : ℕ → Env K} {eF eF' : ℕ → Env F}

theorem ev_congr_cur {R B : ℕ} {e : QE F} (hre : curM R B e.re = true) (him : curM R B e.im = true)
    {eK eK' : Env K} {eF eF' : Env F} (hKt : ∀ i < R, eK.trace i = eK'.trace i) (hKc : eK.chal = eK'.chal)
    (hFt : ∀ j < B, eF.trace j = eF'.trace j) : e.ev δF eK eF = e.ev δF eK' eF' := by
  simp only [QE.ev, curM_eval hre hKt hKc hFt, curM_eval him hKt hKc hFt]

theorem ev_congr_rd {R B : ℕ} {e : QE F} (hre : rdM R B e.re = true) (him : rdM R B e.im = true)
    {eK eK' : Env K} {eF eF' : Env F} (hKt : ∀ i < R, eK.trace i = eK'.trace i)
    (hKn : ∀ i < R, eK.traceNext i = eK'.traceNext i) (hKc : eK.chal = eK'.chal)
    (hFt : ∀ j < B, eF.trace j = eF'.trace j) (hFn : ∀ j < B, eF.traceNext j = eF'.traceNext j) :
    e.ev δF eK eF = e.ev δF eK' eF' := by
  simp only [QE.ev, rdM_eval hre hKt hKn hKc hFt hFn, rdM_eval him hKt hKn hKc hFt hFn]

theorem inv_pair {𝕂' : Type} [Field 𝕂'] {a a' D D' : 𝕂'} (g : a * D = 1) (g' : a' * D' = 1) (h : D = D') :
    a = a' := by
  subst h
  exact inv_col_unique (right_ne_zero_of_mul_eq_one g) g g'

theorem qv_eq {eK eK' : Env K} {r : ℕ} (h : qvA δF eK r = qvA δF eK' r) :
    eK.trace r = eK'.trace r ∧ eK.trace (r + 1) = eK'.trace (r + 1) :=
  (Quad.mk_eq_mk_iff _ _ _ _ _).mp h


/-- The roles `< Rk` of every row agree. -/
def AgK (n : ℕ) (eK eK' : ℕ → Env K) (Rk : ℕ) : Prop := ∀ i, i < n → ∀ r, r < Rk → (eK i).trace r = (eK' i).trace r

theorem AgK.next (R : RowFam δF kroots n ch eK eF) (R' : RowFam δF kroots n ch eK' eF') {Rk : ℕ}
    (ag : AgK n eK eK' Rk) {i : ℕ} (hi : i + 1 < n) : ∀ r < Rk, (eK i).traceNext r = (eK' i).traceNext r := by
  intro r hr
  rw [R.nextK i hi, R'.nextK i hi]
  exact ag (i + 1) hi r hr

/-- The round-0 columns of the next row agree. -/
theorem F0.next (R : RowFam δF kroots n ch eK eF) (R' : RowFam δF kroots n ch eK' eF')
    (h0 : ∀ i, i < n → ∀ j, j < 25 → (eF i).trace j = (eF' i).trace j) {i : ℕ} (hi : i + 1 < n) :
    ∀ j < 25, (eF i).traceNext j = (eF' i).traceNext j := by
  intro j hj
  rw [R.nextF i hi, R'.nextF i hi]
  exact h0 (i + 1) hi j hj

/-- **`ln`, `cnt`, `acc` are determined** (roles `24, 25, 26`): the positional `α`-RLC, the count and the
accumulator, from the round-0 columns and the round-1 labels. -/
theorem walk_lca (R : RowFam δF kroots n ch eK eF) (R' : RowFam δF kroots n ch eK' eF')
    (h0 : ∀ i, i < n → ∀ j, j < 25 → (eF i).trace j = (eF' i).trace j) (h1 : AgK n eK eK' 24) :
    AgK n eK eK' 27 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro i hi; omega
  have hc : ∀ i, (eK i).chal = (eK' i).chal := fun i => (R.chal i).trans (R'.chal i).symm
  -- ln
  have hln : ∀ i, i < n → (eK i).trace WChip.lnR = (eK' i).trace WChip.lnR := by
    refine prod_rec_unique n (fun i => (eK i).trace WChip.lnR) (fun i => (eK' i).trace WChip.lnR)
      (fun _ => ch 0) ?_ ?_ ?_
    · simp only [R.ln0 δF hn, R'.ln0 δF hn]
    · intro i hi
      simp only [R.lnS δF hi, mul_comm]
    · intro i hi
      simp only [R'.lnS δF hi, mul_comm]
  -- cnt
  have hafoN : ∀ i, i + 1 < n → (WChip.afoW nv : MixedExpr F).eval (eK i) (eF i) =
      (WChip.afoW nv : MixedExpr F).eval (eK' i) (eF' i) := fun i hi =>
    rdM_eval (R := 0) (B := 25) rfl (fun r hr => absurd hr (by omega)) (fun r hr => absurd hr (by omega))
      (hc i) (h0 i (by omega)) (F0.next δF R R' h0 hi)
  have hcnt : ∀ i, i < n → (eK i).trace WChip.cntR = (eK' i).trace WChip.cntR := by
    refine prod_rec_unique n (fun i => (eK i).trace WChip.cntR) (fun i => (eK' i).trace WChip.cntR)
      (fun i => (WChip.afoW nv : MixedExpr F).eval (eK i) (eF i)) ?_ ?_ ?_
    · have e : (WChip.afoW cv : MixedExpr F).eval (eK 0) (eF 0) = (WChip.afoW cv : MixedExpr F).eval (eK' 0) (eF' 0) :=
        curM_eval (R := 0) (B := 25) rfl (fun r hr => absurd hr (by omega)) (hc 0) (h0 0 hn)
      simp only [R.cnt0 δF hn, R'.cnt0 δF hn, e]
    · intro i hi
      exact R.cntS δF hi
    · intro i hi
      rw [R'.cntS δF hi, hafoN i hi]
  have ag26 : AgK n eK eK' 26 := by
    intro i hi r hr
    by_cases h : r < 24
    · exact h1 i hi r h
    · by_cases h' : r = 24
      · subst h'; exact hln i hi
      · have : r = 25 := by omega
        subst this; exact hcnt i hi
  -- acc
  have hacc : ∀ i, i < n → (eK i).trace WChip.accR = (eK' i).trace WChip.accR := by
    let X1 : ℕ → K := fun i => (MixedExpr.Mul (WChip.vC WChip.cntR) (WChip.ccW .traceNext nv) : MixedExpr F).eval (eK i) (eF i) -
      (MixedExpr.Scale (notE (nv WChip.rM)) (MixedExpr.Mul (WChip.vN WChip.lnR)
        (WChip.curW .traceNext nv)) : MixedExpr F).eval (eK i) (eF i)
    let X1' : ℕ → K := fun i => (MixedExpr.Mul (WChip.vC WChip.cntR) (WChip.ccW .traceNext nv) : MixedExpr F).eval (eK' i) (eF' i) -
      (MixedExpr.Scale (notE (nv WChip.rM)) (MixedExpr.Mul (WChip.vN WChip.lnR)
        (WChip.curW .traceNext nv)) : MixedExpr F).eval (eK' i) (eF' i)
    let s : ℕ → K := fun i => if i = 0 then ch 0 ^ kroots * (WChip.ccW .traceCur cv : MixedExpr F).eval (eK 0) (eF 0)
      else X1 (i - 1)
    let s' : ℕ → K := fun i => if i = 0 then ch 0 ^ kroots * (WChip.ccW .traceCur cv : MixedExpr F).eval (eK' 0) (eF' 0)
      else X1' (i - 1)
    have hX : ∀ i, i + 1 < n → X1 i = X1' i := by
      intro i hi
      have hKn := AgK.next δF R R' ag26 hi
      have e1 : (MixedExpr.Mul (WChip.vC WChip.cntR) (WChip.ccW .traceNext nv) : MixedExpr F).eval (eK i) (eF i) =
          (MixedExpr.Mul (WChip.vC WChip.cntR) (WChip.ccW .traceNext nv) : MixedExpr F).eval (eK' i) (eF' i) :=
        rdM_eval (R := 26) (B := 25) rfl (ag26 i (by omega)) hKn (hc i) (h0 i (by omega)) (F0.next δF R R' h0 hi)
      have e2 : (MixedExpr.Scale (notE (nv WChip.rM)) (MixedExpr.Mul (WChip.vN WChip.lnR)
          (WChip.curW .traceNext nv)) : MixedExpr F).eval (eK i) (eF i) =
          (MixedExpr.Scale (notE (nv WChip.rM)) (MixedExpr.Mul (WChip.vN WChip.lnR)
          (WChip.curW .traceNext nv)) : MixedExpr F).eval (eK' i) (eF' i) :=
        rdM_eval (R := 26) (B := 25) rfl (ag26 i (by omega)) hKn (hc i) (h0 i (by omega)) (F0.next δF R R' h0 hi)
      simp only [X1, X1', e1, e2]
    have e0 : (WChip.ccW .traceCur cv : MixedExpr F).eval (eK 0) (eF 0) = (WChip.ccW .traceCur cv : MixedExpr F).eval (eK' 0) (eF' 0) :=
      curM_eval (R := 24) (B := 25) rfl (fun r hr => h1 0 hn r hr) (hc 0) (h0 0 hn)
    refine acc_unique n (fun i => (eK i).trace WChip.accR) (fun i => (eK' i).trace WChip.accR) s s'
      ?_ ?_ ?_ ?_ ?_
    · simp only [s, if_true, R.acc0 δF hn]
    · simp only [s', if_true, R'.acc0 δF hn]
    · intro i hi
      by_cases h : i = 0
      · subst h; simp only [s, s', if_true, e0]
      · simp only [s, s', h, if_false]
        exact hX (i - 1) (by omega)
    · intro i hi
      simp only [s, if_neg (show i + 1 ≠ 0 by omega), Nat.add_sub_cancel]
      exact R.accS δF hi
    · intro i hi
      simp only [s', if_neg (show i + 1 ≠ 0 by omega), Nat.add_sub_cancel]
      exact R'.accS δF hi
  intro i hi r hr
  by_cases h : r < 26
  · exact ag26 i hi r h
  · have : r = 26 := by omega
    subst this; exact hacc i hi


/-- **The six inverses of rounds 2 are determined** (roles `27 .. 32` and `37 .. 42`): each gate is
`inv · den = 1`, so `den ≠ 0` and `inv = den⁻¹`, and the denominators read round-1 labels and round-0 columns. -/
theorem walk_invs (R : RowFam δF kroots n ch eK eF) (R' : RowFam δF kroots n ch eK' eF')
    (h0 : ∀ i, i < n → ∀ j, j < 25 → (eF i).trace j = (eF' i).trace j) (ag : AgK n eK eK' 27) :
    ∀ i, i < n → (∀ r, 27 ≤ r → r < 33 → (eK i).trace r = (eK' i).trace r) ∧
      (∀ r, 37 ≤ r → r < 43 → (eK i).trace r = (eK' i).trace r) := by
  have hc : ∀ i, (eK i).chal = (eK' i).chal := fun i => (R.chal i).trans (R'.chal i).symm
  have inv : ∀ (r : ℕ) (D : QE F), curM 24 25 D.re = true → curM 24 25 D.im = true →
      (QE.sub (QE.mul δF (QE.var r) D) QE.one : QE F) ∈ walkAllQ δF → ∀ i, i < n →
      qvA δF (eK i) r = qvA δF (eK' i) r := by
    intro r D h1 h2 hm i hi
    exact inv_pair (R.invQ δF hi hm) (R'.invQ δF hi hm)
      (ev_congr_cur δF h1 h2 (fun r hr => ag i hi r (by omega)) (hc i) (h0 i hi))
  have e27 := inv WChip.xInv (den δF WChip.xKey) rfl rfl (by simp [walkAllQ, WChip.qEqs])
  have e29 := inv WChip.pInvL (den δF WChip.recL) rfl rfl (by simp [walkAllQ, WChip.qEqs])
  have e31 := inv WChip.pInvR (den δF WChip.recR) rfl rfl (by simp [walkAllQ, WChip.qEqs])
  have e37 := inv WalkHQ.hxInvQ (HQ.denKeyQ δF WalkHC.xKeyH) rfl rfl (by simp [walkAllQ, WalkHQ.gatesQ])
  have e39 := inv WalkHQ.hpInvLQ (HQ.denKeyQ δF WalkHC.recLH) rfl rfl (by simp [walkAllQ, WalkHQ.gatesQ])
  have e41 := inv WalkHQ.hpInvRQ (HQ.denKeyQ δF WalkHC.recRH) rfl rfl (by simp [walkAllQ, WalkHQ.gatesQ])
  intro i hi
  refine ⟨fun r h27 h33 => ?_, fun r h37 h43 => ?_⟩
  · have : r = 27 ∨ r = 28 ∨ r = 29 ∨ r = 30 ∨ r = 31 ∨ r = 32 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (qv_eq δF (e27 i hi)).1
    · exact (qv_eq δF (e27 i hi)).2
    · exact (qv_eq δF (e29 i hi)).1
    · exact (qv_eq δF (e29 i hi)).2
    · exact (qv_eq δF (e31 i hi)).1
    · exact (qv_eq δF (e31 i hi)).2
  · have : r = 37 ∨ r = 38 ∨ r = 39 ∨ r = 40 ∨ r = 41 ∨ r = 42 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (qv_eq δF (e37 i hi)).1
    · exact (qv_eq δF (e37 i hi)).2
    · exact (qv_eq δF (e39 i hi)).1
    · exact (qv_eq δF (e39 i hi)).2
    · exact (qv_eq δF (e41 i hi)).1
    · exact (qv_eq δF (e41 i hi)).2


/-- **A `𝕂′` accumulator is determined by its terms**: `acc₀ = Tc₀` and `acc' − acc = Tn` (the gates `isF·(acc − Tc)`
and `(1 − isL)·(acc' − acc − Tn)`), with equal terms on the two traces. -/
theorem accQ_eq (R : RowFam δF kroots n ch eK eF) (R' : RowFam δF kroots n ch eK' eF') {a : ℕ} {Tc Tn : QE F}
    (hinit : (QE.scale (cv WChip.isF) (QE.sub (QE.var a) Tc) : QE F) ∈ walkAllQ δF)
    (hstep : (QE.scale (notE (cv WChip.isL)) (QE.sub (QE.sub (QE.next a) (QE.var a)) Tn) : QE F) ∈ walkAllQ δF)
    (hTc : ∀ i, i < n → i = 0 → Tc.ev δF (eK i) (eF i) = Tc.ev δF (eK' i) (eF' i))
    (hTn : ∀ i, i + 1 < n → Tn.ev δF (eK i) (eF i) = Tn.ev δF (eK' i) (eF' i)) :
    ∀ i, i < n → qvA δF (eK i) a = qvA δF (eK' i) a := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro i hi; omega
  refine acc_unique n (fun i => qvA δF (eK i) a) (fun i => qvA δF (eK' i) a)
    (fun i => if i = 0 then Tc.ev δF (eK 0) (eF 0) else Tn.ev δF (eK (i - 1)) (eF (i - 1)))
    (fun i => if i = 0 then Tc.ev δF (eK' 0) (eF' 0) else Tn.ev δF (eK' (i - 1)) (eF' (i - 1)))
    ?_ ?_ ?_ ?_ ?_
  · simp only [if_true]; exact R.initQ δF hn hinit
  · simp only [if_true]; exact R'.initQ δF hn hinit
  · intro i hi
    by_cases h : i = 0
    · subst h; simp only [if_true]; exact hTc 0 hi rfl
    · simp only [h, if_false]; exact hTn (i - 1) (by omega)
  · intro i hi
    simp only [if_neg (show i + 1 ≠ 0 by omega), Nat.add_sub_cancel]
    exact R.stepQ δF hi hstep
  · intro i hi
    simp only [if_neg (show i + 1 ≠ 0 by omega), Nat.add_sub_cancel]
    exact R'.stepQ δF hi hstep

/-- **The old IO accumulators `xAcc`, `pAcc`** (roles `33 .. 36`). -/
theorem walk_accs_old (R : RowFam δF kroots n ch eK eF) (R' : RowFam δF kroots n ch eK' eF')
    (h0 : ∀ i, i < n → ∀ j, j < 25 → (eF i).trace j = (eF' i).trace j) (ag : AgK n eK eK' 33) :
    ∀ i, i < n → ∀ r, 33 ≤ r → r < 37 → (eK i).trace r = (eK' i).trace r := by
  have hc : ∀ i, (eK i).chal = (eK' i).chal := fun i => (R.chal i).trans (R'.chal i).symm
  have ex : ∀ i, i < n → qvA δF (eK i) WChip.xAcc = qvA δF (eK' i) WChip.xAcc := by
    refine accQ_eq δF R R' (a := WChip.xAcc) (Tc := QE.var WChip.xInv) (Tn := QE.next WChip.xInv)
      (by simp [walkAllQ, WChip.qEqs]) (by simp [walkAllQ, WChip.qEqs]) ?_ ?_
    · intro i hi _
      rw [ev_var, ev_var]
      simp only [qvA, ag i hi WChip.xInv (by decide), ag i hi (WChip.xInv + 1) (by decide)]
    · intro i hi
      rw [ev_next, ev_next, R.nextK i hi, R.nextK i hi, R'.nextK i hi, R'.nextK i hi]
      simp only [ag (i + 1) hi WChip.xInv (by decide), ag (i + 1) hi (WChip.xInv + 1) (by decide)]
  have ep : ∀ i, i < n → qvA δF (eK i) WChip.pAcc = qvA δF (eK' i) WChip.pAcc := by
    refine accQ_eq δF R R' (a := WChip.pAcc) (Tc := WChip.pTerm true) (Tn := WChip.pTerm false)
      (by simp [walkAllQ, WChip.qEqs]) (by simp [walkAllQ, WChip.qEqs]) ?_ ?_
    · intro i hi _
      exact ev_congr_cur δF (R := 33) (B := 25) rfl rfl (fun r hr => ag i hi r hr) (hc i) (h0 i hi)
    · intro i hi
      exact ev_congr_rd δF (R := 33) (B := 25) rfl rfl (fun r hr => ag i (by omega) r hr)
        (AgK.next δF R R' ag hi) (hc i) (h0 i (by omega)) (F0.next δF R R' h0 hi)
  intro i hi r h33 h37
  have : r = 33 ∨ r = 34 ∨ r = 35 ∨ r = 36 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · exact (qv_eq δF (ex i hi)).1
  · exact (qv_eq δF (ex i hi)).2
  · exact (qv_eq δF (ep i hi)).1
  · exact (qv_eq δF (ep i hi)).2

/-- **The handle accumulators `hxAcc`, `hpAcc`** (roles `43 .. 46`). -/
theorem walk_accs_hq (R : RowFam δF kroots n ch eK eF) (R' : RowFam δF kroots n ch eK' eF')
    (h0 : ∀ i, i < n → ∀ j, j < 25 → (eF i).trace j = (eF' i).trace j) (ag : AgK n eK eK' 43) :
    ∀ i, i < n → ∀ r, 43 ≤ r → r < 47 → (eK i).trace r = (eK' i).trace r := by
  have hc : ∀ i, (eK i).chal = (eK' i).chal := fun i => (R.chal i).trans (R'.chal i).symm
  have ex : ∀ i, i < n → qvA δF (eK i) WalkHQ.hxAccQ = qvA δF (eK' i) WalkHQ.hxAccQ := by
    refine accQ_eq δF R R' (a := WalkHQ.hxAccQ) (Tc := QE.var WalkHQ.hxInvQ) (Tn := QE.next WalkHQ.hxInvQ)
      (by simp [walkAllQ, WalkHQ.gatesQ]) (by simp [walkAllQ, WalkHQ.gatesQ]) ?_ ?_
    · intro i hi _
      rw [ev_var, ev_var]
      simp only [qvA, ag i hi WalkHQ.hxInvQ (by decide), ag i hi (WalkHQ.hxInvQ + 1) (by decide)]
    · intro i hi
      rw [ev_next, ev_next, R.nextK i hi, R.nextK i hi, R'.nextK i hi, R'.nextK i hi]
      simp only [ag (i + 1) hi WalkHQ.hxInvQ (by decide), ag (i + 1) hi (WalkHQ.hxInvQ + 1) (by decide)]
  have ep : ∀ i, i < n → qvA δF (eK i) WalkHQ.hpAccQ = qvA δF (eK' i) WalkHQ.hpAccQ := by
    refine accQ_eq δF R R' (a := WalkHQ.hpAccQ) (Tc := WalkHQ.pTermQ true) (Tn := WalkHQ.pTermQ false)
      (by simp [walkAllQ, WalkHQ.gatesQ]) (by simp [walkAllQ, WalkHQ.gatesQ]) ?_ ?_
    · intro i hi _
      exact ev_congr_cur δF (R := 43) (B := 25) rfl rfl (fun r hr => ag i hi r hr) (hc i) (h0 i hi)
    · intro i hi
      exact ev_congr_rd δF (R := 43) (B := 25) rfl rfl (fun r hr => ag i (by omega) r hr)
        (AgK.next δF R R' ag hi) (hc i) (h0 i (by omega)) (F0.next δF R R' h0 hi)
  intro i hi r h43 h47
  have : r = 43 ∨ r = 44 ∨ r = 45 ∨ r = 46 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · exact (qv_eq δF (ex i hi)).1
  · exact (qv_eq δF (ex i hi)).2
  · exact (qv_eq δF (ep i hi)).1
  · exact (qv_eq δF (ep i hi)).2

/-- **The J-8 walk's round-2 roles are determined** (`24 .. 46`), from the round-0 columns and the round-1 labels
(roles `< 24`). -/
theorem walk_env_eq (R : RowFam δF kroots n ch eK eF) (R' : RowFam δF kroots n ch eK' eF')
    (h0 : ∀ i, i < n → ∀ j, j < 25 → (eF i).trace j = (eF' i).trace j) (h1 : AgK n eK eK' 24) :
    AgK n eK eK' 47 := by
  have a27 := walk_lca δF R R' h0 h1
  have inv := walk_invs δF R R' h0 a27
  have a33 : AgK n eK eK' 33 := fun i hi r hr => by
    by_cases h : r < 27
    · exact a27 i hi r h
    · exact (inv i hi).1 r (by omega) hr
  have old := walk_accs_old δF R R' h0 a33
  have a43 : AgK n eK eK' 43 := fun i hi r hr => by
    by_cases h : r < 33
    · exact a33 i hi r h
    · by_cases h' : r < 37
      · exact old i hi r (by omega) h'
      · exact (inv i hi).2 r (by omega) hr
  have hq := walk_accs_hq δF R R' h0 a43
  intro i hi r hr
  by_cases h : r < 43
  · exact a43 i hi r h
  · exact hq i hi r (by omega) hr


/-! ## 4. The terminal gates: the publics `0 .. 7` -/

/-- **The walk publics `0 .. 7` are determined.** The four terminal gates `isL·(acc − pub)` (old export `0`, old
path `2`, handle export `4`, handle path `6`, the last two being `pubXQ`, `pubPQ`) make each public pair the
accumulator's value at the last row; the walk RAP's own gate reads publics `2, 3` as well as `0, 1`. -/
theorem walk_pubs_env (R : RowFam δF kroots n ch eK eF) (R' : RowFam δF kroots n ch eK' eF') (hn : 0 < n)
    (ag : AgK n eK eK' 47) : ∀ j, j < 8 → (eK (n - 1)).pub j = (eK' (n - 1)).pub j := by
  have hl : n - 1 < n := by omega
  have hl2 : n - 1 + 1 = n := by omega
  have p0 := R.termQ δF hl hl2 (a := WChip.xAcc) (j := 0) (by simp [walkAllQ, WChip.qEqs])
  have p0' := R'.termQ δF hl hl2 (a := WChip.xAcc) (j := 0) (by simp [walkAllQ, WChip.qEqs])
  have p2 := R.termQ δF hl hl2 (a := WChip.pAcc) (j := 2) (by simp [walkAllQ, WChip.qEqs])
  have p2' := R'.termQ δF hl hl2 (a := WChip.pAcc) (j := 2) (by simp [walkAllQ, WChip.qEqs])
  have p4 := R.termQ δF hl hl2 (a := WalkHQ.hxAccQ) (j := WalkHQ.pubXQ) (by simp [walkAllQ, WalkHQ.gatesQ])
  have p4' := R'.termQ δF hl hl2 (a := WalkHQ.hxAccQ) (j := WalkHQ.pubXQ) (by simp [walkAllQ, WalkHQ.gatesQ])
  have p6 := R.termQ δF hl hl2 (a := WalkHQ.hpAccQ) (j := WalkHQ.pubPQ) (by simp [walkAllQ, WalkHQ.gatesQ])
  have p6' := R'.termQ δF hl hl2 (a := WalkHQ.hpAccQ) (j := WalkHQ.pubPQ) (by simp [walkAllQ, WalkHQ.gatesQ])
  have g : ∀ r, r < 47 → (eK (n - 1)).trace r = (eK' (n - 1)).trace r := fun r hr => ag _ hl r hr
  intro j hj
  interval_cases j
  · exact p0.1.trans ((g _ (by decide)).trans p0'.1.symm)
  · exact p0.2.trans ((g _ (by decide)).trans p0'.2.symm)
  · exact p2.1.trans ((g _ (by decide)).trans p2'.1.symm)
  · exact p2.2.trans ((g _ (by decide)).trans p2'.2.symm)
  · exact p4.1.trans ((g _ (by decide)).trans p4'.1.symm)
  · exact p4.2.trans ((g _ (by decide)).trans p4'.2.symm)
  · exact p6.1.trans ((g _ (by decide)).trans p6'.1.symm)
  · exact p6.2.trans ((g _ (by decide)).trans p6'.2.symm)


end Det

/-! ## 5. The chip level -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- Row `i` as a `Fin n` (row `0` outside the range). -/
def rowIx (hn : 0 < n) (i : ℕ) : Fin n := if h : i < n then ⟨i, h⟩ else ⟨0, hn⟩

/-- Row `i`'s base environment of a walk trace. -/
abbrev wEF {w : ℕ} (Q : Fin w → F[X]) (i : ℕ) : Env F :=
  Reify.envOfTrace Q orbit.ω (nodes (rowIx hn i)) (slotVal b 25 chals) (slotVal b 25 pubs)

/-- Row `i`'s gathered `𝕂` environment of a walk trace. -/
abbrev wEK {w : ℕ} (Q : Fin w → F[X]) (i : ℕ) : Env K :=
  gatherEnv b ((walkTemplateJ8 δF kroots).col0 3) (wEF b hn nodes orbit chals pubs Q i)

theorem rowIx_val (i : ℕ) (hi : i < n) : (rowIx hn i : ℕ) = i := by simp [rowIx, hi]

theorem wEF_next {w : ℕ} (Q : Fin w → F[X])
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : ℕ) (hi : i + 1 < n) (j : ℕ) :
    (wEF b hn nodes orbit chals pubs Q i).traceNext j = (wEF b hn nodes orbit chals pubs Q (i + 1)).trace j := by
  have hp : (rowIx hn i : ℕ) + 1 < n := by rw [rowIx_val hn i (by omega)]; exact hi
  have h0 := traceNext_eq nodes orbit Q (slotVal b 25 chals) (slotVal b 25 pubs) hadj (rowIx hn i) hp j
  have e : (⟨(rowIx hn i : ℕ) + 1, hp⟩ : Fin n) = rowIx hn (i + 1) :=
    Fin.ext (by
      have h1 := rowIx_val hn i (by omega)
      have h2 := rowIx_val hn (i + 1) hi
      simp only [Fin.val_mk]
      omega)
  rw [e] at h0
  exact h0

/-- **An accepted J-8 walk trace is a row family.** -/
theorem walk_rowFam (Q : Fin (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    RowFam δF kroots n chals (wEK δF kroots b hn nodes orbit chals pubs Q)
      (wEF b hn nodes orbit chals pubs Q) := by
  have hw : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w = 166 :=
    walkChipJ8_width δF kroots b hn nodes orbit chals pubs
  have hl : ∀ i, i < n → _ := fun i hi =>
    (expandChip_satisfies_iff_language (walkTemplateJ8 δF kroots) b _ _ orbit _ Q).mp hsat
      (nodes (rowIx hn i)) (mem_rowNodeSet nodes (rowIx hn i))
  have m0 : Q ⟨0, by rw [hw]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 3; omega⟩
  have m1 : Q ⟨1, by rw [hw]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 3; omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi g hg
    refine (hl i hi).2.2.2 g ?_
    exact List.mem_append_left _ (List.mem_append_left _ hg)
  · intro i hi e he
    refine ev_eq_zero_of_gates δF _ _ e fun g hg => (hl i hi).2.2.2 g ?_
    simp only [walkAllQ, List.mem_append] at he
    rcases he with he | he
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hg⟩))
    · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hg⟩)
  · intro i
    funext r
    exact gather_chal_T b (walkTemplateJ8 δF kroots) 25 (walkTemplateJ8_baseCols δF kroots) _ chals rfl r
  · intro i hi r
    exact gather_next_T b _ _ _ (fun j => wEF_next b hn nodes orbit chals pubs Q hadj i hi j) r
  · intro i hi j
    exact wEF_next b hn nodes orbit chals pubs Q hadj i hi j
  · intro i hi
    have := (masks_of hn nodes orbit Q (by rw [hw]; omega) (by rw [hw]; omega) m0 m1 hinj
      (slotVal b 25 chals) (slotVal b 25 pubs) (rowIx hn i)).1
    simp only [rowIx_val hn i hi] at this
    exact this
  · intro i hi
    have := (masks_of hn nodes orbit Q (by rw [hw]; omega) (by rw [hw]; omega) m0 m1 hinj
      (slotVal b 25 chals) (slotVal b 25 pubs) (rowIx hn i)).2
    simp only [rowIx_val hn i hi] at this
    refine this.trans ?_
    by_cases h : i + 1 = n
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]


theorem wEF_trace {w : ℕ} (Q : Fin w → F[X]) (i : ℕ) {j : ℕ} (hj : j < w) :
    (wEF b hn nodes orbit chals pubs Q i).trace j = (Q ⟨j, hj⟩).eval (nodes (rowIx hn i)) :=
  envOfTrace_trace Q _ _ _ _ hj

theorem rowIx_fin (i : Fin n) : rowIx hn (i : ℕ) = i := Fin.ext (rowIx_val hn i i.isLt)

variable {pubs}

/-- **The J-8 walk's round-1 and round-2 columns are determined.** Two traces accepted by `walkChipJ8` (at one
coin, any publics) with the same round-0 columns and the same round-1 label columns (roles `0 .. 23`, columns
`25 .. 96`) agree on every column at every row node. The label columns are fixed by the export consume and the
path records, not by a gate of the walk. -/
theorem walk_det {pubs' : ℕ → K} {W W' : Fin 166 → F[X]}
    (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies
      (fun j => W (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs) j)))
    (hsat' : (walkChipJ8 δF kroots b hn nodes orbit chals pubs').rap.Satisfies
      (fun j => W' (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs') j)))
    (hbind : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).BindsPreprocessing
      (fun j => W (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs) j)))
    (hbind' : (walkChipJ8 δF kroots b hn nodes orbit chals pubs').BindsPreprocessing
      (fun j => W' (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs') j)))
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (h0 : ∀ j : Fin 166, (j : ℕ) < 25 → W j = W' j)
    (hr1 : ∀ j : Fin 166, 25 ≤ (j : ℕ) → (j : ℕ) < 97 → ∀ i, (W j).eval (nodes i) = (W' j).eval (nodes i)) :
    AgK n (wEK δF kroots b hn nodes orbit chals pubs
        (fun j => W (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs) j)))
      (wEK δF kroots b hn nodes orbit chals pubs'
        (fun j => W' (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs') j))) 47 ∧
    ∀ (j : Fin 166) (i : Fin n), (W j).eval (nodes i) = (W' j).eval (nodes i) := by
  set Q := fun j => W (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs) j) with hQ
  set Q' := fun j => W' (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs') j) with hQ'
  have R := walk_rowFam δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj
  have R' := walk_rowFam δF kroots b hn nodes orbit chals pubs' Q' hsat' hbind' hinj hadj
  have hw : ∀ j, j < 166 → j < (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w := fun j hj => by
    rw [walkChipJ8_width]; exact hj
  have hw' : ∀ j, j < 166 → j < (walkChipJ8 δF kroots b hn nodes orbit chals pubs').rap.w := fun j hj => by
    rw [walkChipJ8_width]; exact hj
  have ev : ∀ (i : ℕ) (j : ℕ) (hj : j < 166),
      (wEF b hn nodes orbit chals pubs Q i).trace j = (W ⟨j, hj⟩).eval (nodes (rowIx hn i)) := fun i j hj => by
    rw [wEF_trace b hn nodes orbit chals pubs Q i (hw j hj)]; rfl
  have ev' : ∀ (i : ℕ) (j : ℕ) (hj : j < 166),
      (wEF b hn nodes orbit chals pubs' Q' i).trace j = (W' ⟨j, hj⟩).eval (nodes (rowIx hn i)) := fun i j hj => by
    rw [wEF_trace b hn nodes orbit chals pubs' Q' i (hw' j hj)]; rfl
  have hF0 : ∀ i, i < n → ∀ j, j < 25 →
      (wEF b hn nodes orbit chals pubs Q i).trace j = (wEF b hn nodes orbit chals pubs' Q' i).trace j := by
    intro i hi j hj
    rw [ev i j (by omega), ev' i j (by omega), h0 ⟨j, by omega⟩ hj]
  have hcol : ∀ (i : ℕ) (hi : i < n) (j : ℕ) (hj : j < 166), 25 ≤ j → j < 97 →
      (wEF b hn nodes orbit chals pubs Q i).trace j = (wEF b hn nodes orbit chals pubs' Q' i).trace j := by
    intro i hi j hj h25 h97
    rw [ev i j hj, ev' i j hj]
    exact hr1 ⟨j, hj⟩ h25 h97 _
  have h1 : AgK n (wEK δF kroots b hn nodes orbit chals pubs Q) (wEK δF kroots b hn nodes orbit chals pubs' Q') 24 := by
    intro i hi r hr
    simp only [wEK, gatherEnv]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hidx : (walkTemplateJ8 δF kroots).col0 3 VarKind.traceCur r + (k : ℕ) < 97 := by
      simp only [ChipTemplate.col0, walkTemplateJ8_baseCols]; have := k.isLt; omega
    have hidx2 : 25 ≤ (walkTemplateJ8 δF kroots).col0 3 VarKind.traceCur r + (k : ℕ) := by
      simp only [ChipTemplate.col0, walkTemplateJ8_baseCols]; omega
    rw [hcol i hi _ (by omega) hidx2 hidx]
  have ag := walk_env_eq δF R R' hF0 h1
  refine ⟨ag, ?_⟩
  intro j i
  by_cases hj : (j : ℕ) < 25
  · rw [h0 j hj]
  · have hr : ((j : ℕ) - 25) / 3 < 47 := by have := j.isLt; omega
    have hk : ((j : ℕ) - 25) % 3 < 3 := Nat.mod_lt _ (by omega)
    have hg := trace_cols_eq_of_gather b ((walkTemplateJ8 δF kroots).col0 3)
      (wEF b hn nodes orbit chals pubs Q i) (wEF b hn nodes orbit chals pubs' Q' i) (((j : ℕ) - 25) / 3)
      (ag i i.isLt _ hr) ⟨((j : ℕ) - 25) % 3, hk⟩
    have hidx : (walkTemplateJ8 δF kroots).col0 3 VarKind.traceCur (((j : ℕ) - 25) / 3) + ((j : ℕ) - 25) % 3 = j := by
      simp only [ChipTemplate.col0, walkTemplateJ8_baseCols]
      omega
    simp only [hidx] at hg
    rw [ev i j j.isLt, ev' i j j.isLt, rowIx_fin hn i] at hg
    exact hg

theorem walk_cols_eq {pubs' : ℕ → K} {W W' : Fin 166 → F[X]}
    (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies
      (fun j => W (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs) j)))
    (hsat' : (walkChipJ8 δF kroots b hn nodes orbit chals pubs').rap.Satisfies
      (fun j => W' (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs') j)))
    (hbind : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).BindsPreprocessing
      (fun j => W (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs) j)))
    (hbind' : (walkChipJ8 δF kroots b hn nodes orbit chals pubs').BindsPreprocessing
      (fun j => W' (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs') j)))
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (h0 : ∀ j : Fin 166, (j : ℕ) < 25 → W j = W' j)
    (hr1 : ∀ j : Fin 166, 25 ≤ (j : ℕ) → (j : ℕ) < 97 → ∀ i, (W j).eval (nodes i) = (W' j).eval (nodes i)) :
    ∀ (j : Fin 166) (i : Fin n), (W j).eval (nodes i) = (W' j).eval (nodes i) :=
  (walk_det δF kroots b hn nodes orbit chals hsat hsat' hbind hbind' hinj hadj h0 hr1).2

/-- **The walk publics `0 .. 7` are determined**: the terminal gates make them the accumulators' last values,
which `walk_det` shows equal (including `2, 3`, read by the walk RAP's own `pAcc` terminal gate). -/
theorem walk_pubs_eq {pubs' : ℕ → K} {W W' : Fin 166 → F[X]}
    (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies
      (fun j => W (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs) j)))
    (hsat' : (walkChipJ8 δF kroots b hn nodes orbit chals pubs').rap.Satisfies
      (fun j => W' (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs') j)))
    (hbind : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).BindsPreprocessing
      (fun j => W (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs) j)))
    (hbind' : (walkChipJ8 δF kroots b hn nodes orbit chals pubs').BindsPreprocessing
      (fun j => W' (Fin.cast (walkChipJ8_width δF kroots b hn nodes orbit chals pubs') j)))
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (h0 : ∀ j : Fin 166, (j : ℕ) < 25 → W j = W' j)
    (hr1 : ∀ j : Fin 166, 25 ≤ (j : ℕ) → (j : ℕ) < 97 → ∀ i, (W j).eval (nodes i) = (W' j).eval (nodes i)) :
    ∀ j, j < 8 → pubs j = pubs' j := by
  intro j hj
  have ag := (walk_det δF kroots b hn nodes orbit chals hsat hsat' hbind hbind' hinj hadj h0 hr1).1
  have R := walk_rowFam δF kroots b hn nodes orbit chals pubs _ hsat hbind hinj hadj
  have R' := walk_rowFam δF kroots b hn nodes orbit chals pubs' _ hsat' hbind' hinj hadj
  have := walk_pubs_env δF R R' hn ag j hj
  rwa [gather_pub_T b (walkTemplateJ8 δF kroots) 25 (walkTemplateJ8_baseCols δF kroots) _ pubs rfl j,
    gather_pub_T b (walkTemplateJ8 δF kroots) 25 (walkTemplateJ8_baseCols δF kroots) _ pubs' rfl j] at this

end Chip

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsWalkP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsWalkP1.walk_lca
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsWalkP1.walk_invs
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsWalkP1.walk_accs_old
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsWalkP1.walk_accs_hq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsWalkP1.walk_env_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsWalkP1.walk_pubs_env
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsWalkP1.walk_rowFam
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsWalkP1.walk_cols_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsWalkP1.walk_pubs_eq
