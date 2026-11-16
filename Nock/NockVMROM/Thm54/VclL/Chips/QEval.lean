/-
  Nock/NockVMROM/Thm54/VclL/Chips/QEval.lean

  A `QE` (`ChipRAP.lean`) is a pair of `𝕂`-valued `MixedExpr`s (Re, Im); its value in
  `𝕂′ = Quad δ`, `δ = algebraMap 𝔽 𝕂 δF`, is `QE.ev e = Quad.mk δ (re.eval) (im.eval)`.  This file
  proves `QE.ev` is a homomorphism for the `QE` combinators (`ev_add`, `ev_sub`, `ev_mul` — the
  `Quad.mk_mul` formula with the `Scale (const δF)` term —, `ev_scale`, `ev_base`, `ev_mk2`,
  `ev_rlc`), and that a `𝕂′` equation whose two `𝕂`-gates vanish has `QE.ev e = 0`
  (`ev_eq_zero_of_gates`, `Quad.mk_eq_zero_iff`).  This is the recombination step of the chip ⇒
  row-model bridge (brief R-V2b (1): "`𝕂′` recombination via `Quad.mk`").
-/
import Nock.NockVMROM.Thm54.VclL.Chips.RowBridge

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] (δF : F)

/-- The `𝕂′` value of a `QE`. -/
def QE.ev (e : QE F) (eK : Env K) (eF : Env F) : Quad (algebraMap F K δF) :=
  Quad.mk _ (e.re.eval eK eF) (e.im.eval eK eF)

/-- The `𝕂′` fingerprint value of a `QFP`. -/
def QFP.ev (x : QFP F) (eK : Env K) (eF : Env F) : ComputeTable.FP (Quad (algebraMap F K δF)) :=
  ⟨x.size.ev δF eK eF, x.dyck.ev δF eK eF, x.leaf.ev δF eK eF⟩

variable (eK : Env K) (eF : Env F)

/-- The `𝕂 → 𝕂′` scalar of a base-field value. -/
abbrev liftQ (g : F) : Quad (algebraMap F K δF) := algebraMap K _ (algebraMap F K g)

theorem ev_add (a b : QE F) : (QE.add a b).ev δF eK eF = a.ev δF eK eF + b.ev δF eK eF := by
  simp only [QE.ev, QE.add, MixedExpr.eval, Quad.mk_add]

theorem ev_sub (a b : QE F) : (QE.sub a b).ev δF eK eF = a.ev δF eK eF - b.ev δF eK eF := by
  simp only [QE.ev, QE.sub, MixedExpr.eval, Quad.mk_sub]

theorem ev_mul (a b : QE F) : (QE.mul δF a b).ev δF eK eF = a.ev δF eK eF * b.ev δF eK eF := by
  simp only [QE.ev, QE.mul, MixedExpr.eval, CoeffExpr.eval, Quad.mk_mul]

theorem ev_scale (g : CoeffExpr F) (a : QE F) :
    (QE.scale g a).ev δF eK eF = liftQ δF (g.eval eF) * a.ev δF eK eF := by
  simp only [QE.ev, QE.scale, MixedExpr.eval, liftQ, Quad.mk_smul]

theorem ev_base (g : CoeffExpr F) : (QE.base g).ev δF eK eF = liftQ δF (g.eval eF) := by
  simp only [QE.ev, QE.base, MixedExpr.eval, Int.cast_zero, Quad.mk_base, liftQ]

theorem ev_mk2 (g h : CoeffExpr F) :
    (QE.mk2 g h).ev δF eK eF = Quad.mk _ (algebraMap F K (g.eval eF)) (algebraMap F K (h.eval eF)) := by
  simp only [QE.ev, QE.mk2, MixedExpr.eval]

theorem ev_one : (QE.one : QE F).ev δF eK eF = 1 := by
  simp only [QE.ev, QE.one, MixedExpr.eval, Int.cast_one, Int.cast_zero, Quad.mk_one']

theorem ev_zero : (QE.zero : QE F).ev δF eK eF = 0 := by
  simp only [QE.ev, QE.zero, MixedExpr.eval, Int.cast_zero, Quad.mk_zero']

theorem ev_var (r : ℕ) : (QE.var r : QE F).ev δF eK eF = Quad.mk _ (eK.trace r) (eK.trace (r + 1)) := by
  simp only [QE.ev, QE.var, MixedExpr.eval]

theorem ev_next (r : ℕ) :
    (QE.next r : QE F).ev δF eK eF = Quad.mk _ (eK.traceNext r) (eK.traceNext (r + 1)) := by
  simp only [QE.ev, QE.next, MixedExpr.eval]

theorem ev_chal (i j : ℕ) : (QE.chal i j : QE F).ev δF eK eF = Quad.mk _ (eK.chal i) (eK.chal j) := by
  simp only [QE.ev, QE.chal, MixedExpr.eval]

theorem ev_pub (i : ℕ) : (QE.pub i : QE F).ev δF eK eF = Quad.mk _ (eK.pub i) (eK.pub (i + 1)) := by
  simp only [QE.ev, QE.pub, MixedExpr.eval]

theorem ev_gpow (i : ℕ) :
    (QE.gpow i : QE F).ev δF eK eF = Quad.mk _ (eK.chal (11 + 2 * i)) (eK.chal (12 + 2 * i)) := by
  simp only [QE.ev, QE.gpow, MixedExpr.eval]

/-- The flat fold `RLC′` term by term (any indexed list). -/
theorem ev_foldr_rlc (L : List (QE F × ℕ)) :
    (L.foldr (fun ei acc => QE.add (QE.mul δF (QE.gpow ei.2) ei.1) acc) QE.zero).ev δF eK eF =
      (L.map fun ei => (QE.gpow ei.2 : QE F).ev δF eK eF * ei.1.ev δF eK eF).sum := by
  induction L with
  | nil => simp [ev_zero]
  | cons a t ih => simp only [List.foldr_cons, ev_add, ev_mul, ih, List.map_cons, List.sum_cons]

/-- **`RLC′` in `𝕂′`**: `Σ γ′ⁱ · eᵢ` over the gathered coin powers. -/
theorem ev_rlc (es : List (QE F)) :
    (QE.rlc δF es).ev δF eK eF =
      (es.zipIdx.map fun ei => (QE.gpow ei.2 : QE F).ev δF eK eF * ei.1.ev δF eK eF).sum :=
  ev_foldr_rlc δF eK eF _

theorem ev_den (es : List (QE F)) :
    (den δF es).ev δF eK eF = (rQ : QE F).ev δF eK eF + (QE.rlc δF es).ev δF eK eF := by
  simp only [den, ev_add]

/-- **A `𝕂′` equation whose two `𝕂`-gates vanish holds in `𝕂′`.** -/
theorem ev_eq_zero_of_gates (e : QE F) (h : ∀ g ∈ e.gates, g.eval eK eF = 0) : e.ev δF eK eF = 0 := by
  have h1 := h e.re (by simp [QE.gates])
  have h2 := h e.im (by simp [QE.gates])
  simp only [QE.ev, h1, h2, Quad.mk_zero']

/-- `QFP` combinators. -/
theorem QFP.ev_var (r : ℕ) : (QFP.var r : QFP F).ev δF eK eF =
    ⟨(QE.var r : QE F).ev δF eK eF, (QE.var (r + 2) : QE F).ev δF eK eF,
      (QE.var (r + 4) : QE F).ev δF eK eF⟩ := rfl

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
