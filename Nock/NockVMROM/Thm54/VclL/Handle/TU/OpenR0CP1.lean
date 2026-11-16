/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/OpenR0CP1.lean

 **Trace uniqueness on the P1 fragment: the open fact `r0C` (round-0 compute columns) from row agreement.**

 * §1 one compute row of an accepted canonical trace (`RowGatesP1`: the base gates, the one-hot state, the E3 zero
 pins). `six_of`: the state is one of `s0, s7, cons, s10, s10L, s10T` (any other state's own selector is an E3
 pinned column). `kb_val`: the big-atom bit of a handle is `k(k−1)/2`, a function of its kind.
 * §2 the per-state gate facts: `pr = sel_{s10L}`, `pr2 = 0`, the head handle `fh`, the axis copy `v` on `s0`/`s10`,
 the `s10L` chain level (`v2 = f.v`, `m.v = ax2`, `sf1 = s`, `sf2 = e`, `ftth = fttt`, `a = 2v + β`, `w`, `ax2`),
 and `half_det`: with the halving range, `a = 2v + β` fixes `v` and `β`.
 * §3 **`row_eq`**: two such rows in the same state, with equal endpoint masks, equal handles on the state's list
 `actH` (the handles no gate fixes from others), equal `z1` on `s0`/`s10`, and the halving range on `s10L`, agree
 on all `69` round-0 columns. `z1_eq_of_v_ne`: `z1` is forced except at axis `1`.
 * §4 **`r0C_of_rows`**: the trace form. Two traces accepted by `computeChipVCLHX` at one layout (`Pb.nodes`,
 `Pb.orbit`) and by the side template `canonC`, with per-row state and `actH` agreement, `z1` agreement at
 axis-`1` rows of `s0`/`s10`, and the halving range on `s10L` rows, satisfy the `r0C` field of `OpenP1`.

 The column `z1` (`19`) at an `s0` row with axis `1` and a cell subject, or an `s10` row with axis `1` and a cell
 edit target, is not fixed by the compute gates alone (`z1 = 0` consumes a path record at axis `1`, and `RecOK`
 holds there). It is fixed by the axis bound `AxOK` of the consumed path records (`z1_one_of_ax`): the walk
 provides only axes `2·pre + b` with `pre ≥ 1` (`WalkKJ8.axOK_p_row`), and every consumed record is provided
 outside the events (`ServedJ8.servedP_of_balancesJ8`). The trace theorems take that bound as `hAx`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.RowBridgeP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1

noncomputable section

open Nock Nock.Reified Nock.Framework Nock.Edit Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1

/-! ## 1. One compute row -/

section Row
variable {p : ℕ} [Fact p.Prime]

/-- **One compute row of an accepted canonical trace** in state `st`: the base gates, the one-hot state, and the
E3 pins (a round-0 column outside `Act` of the state is `0`). -/
structure RowGatesP1 (E : Env (ZMod p)) (st : StateX) : Prop where
  base : BaseHoldsX E
  oh : OneHotAt E (stIdx st)
  e3 : ∀ c < 69, stIdx st ∉ actC c → E.trace c = 0

/-- **The state is one of the six fragment states**: any other state's own selector column has empty `Act`, so its
E3 pin makes it `0`, against the one-hot `1`. -/
theorem six_of {E : Env (ZMod p)} {st : StateX} (G : RowGatesP1 E st) :
    st = .s0 ∨ st = .s7 ∨ st = .cons ∨ st = .s10 ∨ st = .s10L ∨ st = .s10T := by
  have h1 : E.trace (stIdx st) = 1 := oh_one G.oh (stIdx_lt st)
  have key : ∀ c, c < 17 → c ∉ six → stIdx st = c → False := by
    intro c hc hs he
    have h0 := G.e3 c (by omega) (by rw [he]; simp [actC, hc, hs])
    rw [← he, h1] at h0
    exact one_ne_zero h0
  cases st <;> first | exact (key _ (by decide) (by decide) rfl).elim | simp

theorem natCast_ne {a b : ℕ} (ha : a < p) (hb : b < p) (hne : a ≠ b) : (a : ZMod p) ≠ (b : ZMod p) := by
  intro h
  have := congrArg ZMod.val h
  rw [val_nat ha, val_nat hb] at this
  exact hne this

theorem two_ne_zero' (hp : 17 < p) : (2 : ZMod p) ≠ 0 := by
  have := natCast_ne (p := p) (a := 2) (b := 0) (by omega) (by omega) (by decide)
  simpa using this

/-- **The big-atom bit is a function of the kind**: `2·kb = k·(k − 1)` (the `kb` split). -/
theorem kb_val {E : Env (ZMod p)} (hB : BaseHoldsX E) {h : Hd} (hh : h ∈ allHandlesX) :
    2 * E.trace (kbX h) = E.trace h.k * (E.trace h.k - 1) := by
  have s := kind_split hB h hh
  simp only [kcV, kbV] at s
  rcases s with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · have hk : E.trace h.k = 0 := by linear_combination a + 2 * b
    rw [hk, b]; ring
  · have hk : E.trace h.k = 1 := by linear_combination a + 2 * b
    rw [hk, b]; ring
  · have hk : E.trace h.k = 2 := by linear_combination a + 2 * b
    rw [hk, b]; ring

/-- Equal kinds give equal big-atom bits. -/
theorem kb_eq (hp : 17 < p) {E E' : Env (ZMod p)} (hB : BaseHoldsX E) (hB' : BaseHoldsX E') {h : Hd}
    (hh : h ∈ allHandlesX) (hk : E.trace h.k = E'.trace h.k) : E.trace (kbX h) = E'.trace (kbX h) := by
  have e := kb_val hB hh
  have e' := kb_val hB' hh
  rw [hk, ← e'] at e
  exact mul_left_cancel₀ (two_ne_zero' hp) e

/-- Equal decoded handles have equal kind and value columns. -/
theorem cols_of_hdV {E E' : Env (ZMod p)} {h : Hd} (H : hdV E h = hdV E' h) :
    E.trace h.k = E'.trace h.k ∧ E.trace h.v = E'.trace h.v := by
  simp only [hdV, Prod.mk.injEq] at H
  exact ⟨ZMod.val_injective _ H.1, ZMod.val_injective _ H.2⟩

theorem hdV_of_cols {E E' : Env (ZMod p)} {h : Hd} (hk : E.trace h.k = E'.trace h.k)
    (hv : E.trace h.v = E'.trace h.v) : hdV E h = hdV E' h := by
  simp only [hdV, hk, hv]

end Row

/-! ## 2. Per-state gate facts -/

section Facts
variable {p : ℕ} [Fact p.Prime] {E : Env (ZMod p)}

/-- `pr = s10L` off `s5`. -/
theorem pr_eq (hB : BaseHoldsX E) (h5 : E.trace 5 = 0) : E.trace prX = E.trace sS10L := by
  have a := arith_of_base hB (op5G_sub _ (by simp [op5G] : (prGateX : CoeffExpr ℚ) ∈ op5G))
  simp only [prGateX] at a
  gsimp at a
  rw [h5] at a
  linear_combination a

/-- `pr2 = 0` off `s5`. -/
theorem pr2_eq (hB : BaseHoldsX E) (h5 : E.trace 5 = 0) : E.trace pr2X = 0 := by
  have a := arith_of_base hB (op5G_sub _ (by simp [op5G] : (pr2GateX : CoeffExpr ℚ) ∈ op5G))
  simp only [pr2GateX] at a
  gsimp at a
  rw [h5] at a
  linear_combination a

/-- The `s10` head value is the constant `10`. -/
theorem fhv_s10 (hB : BaseHoldsX E) (hOH : OneHotAt E sS10) : E.trace xFh.v = ((10 : ℚ) : ZMod p) := by
  have := eqg hB (svEq_sub _ (by simp [svEq] : (⟨cc sS10, xFh.v, .cst 10⟩ : EqG ℚ) ∈ svEq))
    (by simp only [cc, evalQX]; exact oh_one hOH (by decide))
  simpa [Opnd.expr, evalQX] using this

/-- `s0`: `v = f_t.v`. -/
theorem v_s0 (hB : BaseHoldsX E) (hOH : OneHotAt E 0) : E.trace vX = E.trace xFt.v :=
  eqCol hB (op0Eq_sub _ (by simp [op0Eq] : (⟨cc 0, vX, .col xFt.v⟩ : EqG ℚ) ∈ op0Eq))
    (by simp only [cc, evalQX]; exact oh_one hOH (by decide))

/-- `s10`: `v = f_tth.v`. -/
theorem v_s10 (hB : BaseHoldsX E) (hOH : OneHotAt E sS10) : E.trace vX = E.trace xFtth.v :=
  eqCol hB (s10Eq_sub _ (by simp [s10Eq] : (⟨cc sS10, vX, .col xFtth.v⟩ : EqG ℚ) ∈ s10Eq))
    (by simp only [cc, evalQX]; exact oh_one hOH (by decide))

/-- **The `s10L` chain level.** -/
theorem s10L_facts (hB : BaseHoldsX E) (hOH : OneHotAt E sS10L) :
    E.trace v2X = E.trace xF.v ∧ E.trace xM.v = E.trace ax2X ∧ hdV E xSf1 = hdV E xS ∧
      hdV E xSf2 = hdV E xE ∧ hdV E xFtth = hdV E xFttt ∧
      E.trace v2X = 2 * E.trace vX + E.trace betaX ∧ (E.trace v2X - 1) * E.trace wX = 1 ∧
      E.trace ax2X = E.trace v2X + 1 - 2 * E.trace betaX ∧ (E.trace betaX = 0 ∨ E.trace betaX = 1) := by
  have h12 : E.trace sS10L = 1 := oh_one hOH (by decide)
  have hσ : evalQX (cc (F := ℚ) sS10L) E = 1 := by simp only [cc, evalQX]; exact h12
  have e1 := eqCol hB (s10LEq_sub _ (by simp [s10LEq] : (⟨cc sS10L, v2X, .col xF.v⟩ : EqG ℚ) ∈ s10LEq)) hσ
  have e2 := eqCol hB (s10LEq_sub _ (by simp [s10LEq] : (⟨cc sS10L, xM.v, .col ax2X⟩ : EqG ℚ) ∈ s10LEq)) hσ
  have e3 : hdV E xSf1 = hdV E xS := hdEq hB (σ := cc sS10L)
    (fun g hg => s10LEq_sub _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hg)))) hσ
  have e4 : hdV E xSf2 = hdV E xE := hdEq hB (σ := cc sS10L)
    (fun g hg => s10LEq_sub _ (List.mem_append_left _ (List.mem_append_right _ hg))) hσ
  have e5 : hdV E xFtth = hdV E xFttt := hdEq hB (σ := cc sS10L)
    (fun g hg => s10LEq_sub _ (List.mem_append_right _ hg)) hσ
  have a1 := arith_of_base hB (s10LG_sub _ (by simp [s10LG] :
    (.mul (cc sS10L) (.sub (.sub (cc v2X) (.mul (.const 2) (cc vX))) (cc betaX)) : CoeffExpr ℚ) ∈ s10LG))
  have a2 := arith_of_base hB (s10LG_sub _ (by simp [s10LG] :
    (.mul (cc sS10L) (.sub (.mul (.sub (cc v2X) (.const 1)) (cc wX)) (.const 1)) : CoeffExpr ℚ) ∈ s10LG))
  have a3 := arith_of_base hB (s10LG_sub _ (by simp [s10LG] :
    (.mul (cc sS10L) (.add (.sub (.sub (cc ax2X) (cc v2X)) (.const 1)) (.mul (.const 2) (cc betaX))) :
      CoeffExpr ℚ) ∈ s10LG))
  gsimp at a1; gsimp at a2; gsimp at a3
  rw [h12, one_mul] at a1 a2 a3
  refine ⟨e1, e2, e3, e4, e5, by linear_combination a1, by linear_combination a2, by linear_combination a3,
    col_bool hB (i := betaX) (by simp [oneHotG])⟩

/-- **The halving split is unique**: `a = 2v + β` with `β ∈ {0, 1}` and `2·val v + 1 < p` fixes `v` and `β`. -/
theorem half_det {v β v' β' a : ZMod p} (hv : 2 * v.val + 1 < p) (hv' : 2 * v'.val + 1 < p)
    (hb : β = 0 ∨ β = 1) (hb' : β' = 0 ∨ β' = 1) (h : a = 2 * v + β) (h' : a = 2 * v' + β') :
    v = v' ∧ β = β' := by
  obtain ⟨c, hc1, rfl⟩ : ∃ c : ℕ, c ≤ 1 ∧ β = (c : ZMod p) := by
    rcases hb with rfl | rfl
    · exact ⟨0, by omega, by simp⟩
    · exact ⟨1, le_rfl, by simp⟩
  obtain ⟨c', hc1', rfl⟩ : ∃ c : ℕ, c ≤ 1 ∧ β' = (c : ZMod p) := by
    rcases hb' with rfl | rfl
    · exact ⟨0, by omega, by simp⟩
    · exact ⟨1, le_rfl, by simp⟩
  have e : ((2 * v.val + c : ℕ) : ZMod p) = ((2 * v'.val + c' : ℕ) : ZMod p) := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← h, ← h']
  have := congrArg ZMod.val e
  rw [val_nat (by omega), val_nat (by omega)] at this
  exact ⟨ZMod.val_injective _ (by omega), by congr 1; omega⟩

/-- `z1` on `s0` away from axis `1`: `z1 = 0`. -/
theorem z1_s0 (hB : BaseHoldsX E) (hOH : OneHotAt E 0) (hv : E.trace vX ≠ 1) : E.trace z1X = 0 := by
  have a := arith_of_base hB (op0G_sub _ (by simp [op0G] :
    (prodL [cc 0, cc z1X, .sub (cc vX) (.const 1)] : CoeffExpr ℚ) ∈ op0G))
  gsimp at a
  rw [oh_one hOH (by decide), one_mul] at a
  exact (mul_eq_zero.mp a).resolve_right (fun h => hv (sub_eq_zero.mp h))

/-- `z1` on `s10` away from axis `1`: `z1 = 0`. -/
theorem z1_s10 (hB : BaseHoldsX E) (hOH : OneHotAt E sS10) (hv : E.trace vX ≠ 1) : E.trace z1X = 0 := by
  have a := arith_of_base hB (s10G_sub _ (by simp [s10G] :
    (prodL [cc sS10, cc z1X, .sub (cc vX) (.const 1)] : CoeffExpr ℚ) ∈ s10G))
  gsimp at a
  rw [oh_one hOH (by decide), one_mul] at a
  exact (mul_eq_zero.mp a).resolve_right (fun h => hv (sub_eq_zero.mp h))

/-- **`z1 = 1` at axis `1`** on `s0` / `s10`, when every consumed path record has axis `≥ 2` (`AxOK`, the walk
provides only axes `2·pre + b` with `pre ≥ 1`): `z1 = 0` would make the row consume a path record at axis `v = 1`. -/
theorem z1_one_of_ax (hB : BaseHoldsX E) (hAx : ∀ x ∈ activeX E, ServedJ8.AxOK x) {st : StateX}
    (hOH : OneHotAt E (stIdx st)) (hst : st = .s0 ∨ st = .s10) (hv : E.trace vX = 1) : E.trace z1X = 1 := by
  rcases col_bool hB (i := z1X) (by simp [oneHotG]) with hz | hz
  · exfalso
    rcases hst with rfl | rfl
    · have hm := ent_active hOH (S := slot1X) (by simp [ChipHX.slotsX])
        (x := ⟨[0], notC z1X, walkRecX xS xFt.v xE, .p⟩) (by simp [slot1X]) (by decide) (by decide)
        (by decide) (by simp [notC, cc, evalQX, hz])
      have h := hAx _ hm
      simp only [walkRecX, recOf, walkRec, List.map_cons, List.map_nil, reVal, ServedJ8.AxOK] at h
      have h1 : E.trace xFt.v = 1 := (v_s0 hB hOH).symm.trans hv
      rw [h1, val_one'] at h
      omega
    · have hm := ent_active hOH (S := slot3X) (by simp [ChipHX.slotsX])
        (x := ⟨[sS10], notC z1X, walkRecX xE vX xSf1, .p⟩) (by simp [slot3X]) (by decide) (by decide)
        (by decide) (by simp [notC, cc, evalQX, hz])
      have h := hAx _ hm
      simp only [walkRecX, recOf, walkRec, List.map_cons, List.map_nil, reVal, ServedJ8.AxOK] at h
      rw [hv, val_one'] at h
      omega
  · exact hz

/-- **The `s10L` sibling axis is fixed by the formula value**: two `s10L` rows with the halving range and the same
`f.v` have the same `ax2`. -/
theorem ax2_eq {E E' : Env (ZMod p)} (hB : BaseHoldsX E) (hB' : BaseHoldsX E') (hOH : OneHotAt E sS10L)
    (hOH' : OneHotAt E' sS10L) (hv : HalvingOK E .s10L) (hv' : HalvingOK E' .s10L)
    (hf : E.trace xF.v = E'.trace xF.v) : E.trace ax2X = E'.trace ax2X := by
  obtain ⟨a1, -, -, -, -, a6, -, a8, a9⟩ := s10L_facts hB hOH
  obtain ⟨b1, -, -, -, -, b6, -, b8, b9⟩ := s10L_facts hB' hOH'
  have g22 : E.trace v2X = E'.trace v2X := a1.trans (hf.trans b1.symm)
  obtain ⟨-, g21⟩ := half_det (hv rfl).2 (hv' rfl).2 a9 b9 a6 (by rw [g22]; exact b6)
  rw [a8, b8, g22, g21]

end Facts

/-! ## 3. Two rows in one state -/

/-- **The handles of a state that no gate fixes from other columns** (`Act` handles minus the gate-fixed ones:
`fh` off `cons`, `sf1 sf2 fttt` on `s10L`). -/
def actH : StateX → List Hd
  | .s0 => [xS, xF, xE, xFt]
  | .s7 => [xS, xF, xE, xSf1, xSf2, xFt, xFth, xFtt]
  | .cons => [xS, xF, xE, xSf1, xSf2, xFh, xFt]
  | .s10 => [xS, xF, xE, xSf1, xSf2, xFt, xFth, xFtt, xFtth, xFttt]
  | .s10L => [xS, xF, xE, xFtth]
  | .s10T => [xS, xF, xE]
  | _ => []

section RowEq
variable {p : ℕ} [Fact p.Prime]

/-- `z1` agrees except at axis `1`: the hypothesis `hz1` of `row_eq` is needed only at rows with `v = 1`. -/
theorem z1_eq_of_v_ne {E E' : Env (ZMod p)} {st : StateX} (G : RowGatesP1 E st) (G' : RowGatesP1 E' st)
    (hst : st = .s0 ∨ st = .s10) (hvv : E.trace vX = E'.trace vX) (hv : E.trace vX ≠ 1) :
    E.trace z1X = E'.trace z1X := by
  rcases hst with rfl | rfl
  · rw [z1_s0 G.base G.oh hv, z1_s0 G'.base G'.oh (by rw [← hvv]; exact hv)]
  · rw [z1_s10 G.base G.oh hv, z1_s10 G'.base G'.oh (by rw [← hvv]; exact hv)]

/-- **Two rows in one state agree on all `69` round-0 columns**, given equal endpoint masks, equal `actH` handles,
equal `z1` on `s0`/`s10`, and the halving range on `s10L`. -/
theorem row_eq (hp : 17 < p) {E E' : Env (ZMod p)} {st : StateX} (G : RowGatesP1 E st) (G' : RowGatesP1 E' st)
    (hfl : E.trace firstX = E'.trace firstX) (hll : E.trace lastX = E'.trace lastX)
    (hH : ∀ h ∈ actH st, hdV E h = hdV E' h)
    (hz1 : st = .s0 ∨ st = .s10 → E.trace z1X = E'.trace z1X)
    (hhalf : st = .s10L → HalvingOK E .s10L ∧ HalvingOK E' .s10L) :
    ∀ c < 69, E.trace c = E'.trace c := by
  have hB := G.base
  have hB' := G'.base
  have s6 := six_of G
  have h5 : E.trace 5 = 0 := oh_zero G.oh (by decide) (by rcases s6 with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have h5' : E'.trace 5 = 0 := oh_zero G'.oh (by decide) (by rcases s6 with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have f17 : E.trace 17 = E'.trace 17 := hfl
  have f18 : E.trace 18 = E'.trace 18 := hll
  have f24 : E.trace 24 = E'.trace 24 := by
    have a := pr_eq hB h5
    have a' := pr_eq hB' h5'
    have s := G.oh sS10L (by decide)
    have s' := G'.oh sS10L (by decide)
    exact a.trans (s.trans (s'.symm.trans a'.symm))
  have f64 : E.trace 64 = E'.trace 64 := (pr2_eq hB h5).trans (pr2_eq hB' h5').symm
  have hS := cols_of_hdV (hH xS (by rcases s6 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [actH]))
  have hF := cols_of_hdV (hH xF (by rcases s6 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [actH]))
  have hE := cols_of_hdV (hH xE (by rcases s6 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [actH]))
  have f25 : E.trace 25 = E'.trace 25 := hS.1
  have f26 : E.trace 26 = E'.trace 26 := hS.2
  have f27 : E.trace 27 = E'.trace 27 := hF.1
  have f28 : E.trace 28 = E'.trace 28 := hF.2
  have f29 : E.trace 29 = E'.trace 29 := hE.1
  have f30 : E.trace 30 = E'.trace 30 := hE.2
  have kb : ∀ h ∈ allHandlesX, E.trace h.k = E'.trace h.k → E.trace (kbX h) = E'.trace (kbX h) :=
    fun h hh hk => kb_eq hp hB hB' hh hk
  have mH : ∀ j < 12, hdX j ∈ allHandlesX := fun j hj => List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  have f49 : E.trace 49 = E'.trace 49 := kb xS (mH 0 (by decide)) f25
  have f51 : E.trace 51 = E'.trace 51 := kb xE (mH 2 (by decide)) f29
  -- `fh.k`
  have f35 : E.trace 35 = E'.trace 35 := by
    rcases s6 with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (fh_k0 hB G.oh (by decide)).trans (fh_k0 hB' G'.oh (by decide)).symm
    · exact (fh_k0 hB G.oh (by decide)).trans (fh_k0 hB' G'.oh (by decide)).symm
    · exact (cols_of_hdV (hH xFh (by simp [actH]))).1
    · exact (fh_k0 hB G.oh (by decide)).trans (fh_k0 hB' G'.oh (by decide)).symm
    · exact (fh_k0 hB G.oh (by decide)).trans (fh_k0 hB' G'.oh (by decide)).symm
    · exact (fh_k0 hB G.oh (by decide)).trans (fh_k0 hB' G'.oh (by decide)).symm
  have f54 : E.trace 54 = E'.trace 54 := kb xFh (mH 5 (by decide)) f35
  have off : ∀ c, c < 69 → stIdx st ∉ actC c → E.trace c = E'.trace c := fun c hc hA => by
    rw [G.e3 c hc hA, G'.e3 c hc hA]
  have sel : ∀ c, c < 17 → E.trace c = E'.trace c := fun c hc => by
    rw [G.oh c hc, G'.oh c hc]
  rcases s6 with rfl | rfl | rfl | rfl | rfl | rfl
  · -- s0
    have hFt := cols_of_hdV (hH xFt (by simp [actH]))
    have f37 : E.trace 37 = E'.trace 37 := hFt.1
    have f38 : E.trace 38 = E'.trace 38 := hFt.2
    have f19 : E.trace 19 = E'.trace 19 := hz1 (Or.inl rfl)
    have f20 : E.trace 20 = E'.trace 20 := (v_s0 hB G.oh).trans (f38.trans (v_s0 hB' G'.oh).symm)
    have f36 : E.trace 36 = E'.trace 36 := (fhv_op hB G.oh (by decide)).trans (fhv_op hB' G'.oh (by decide)).symm
    intro c hc
    by_cases hA : stIdx StateX.s0 ∈ actC c
    · interval_cases c <;> first | assumption | exact sel _ (by decide) | exact absurd hA (by decide)
    · exact off c hc hA
  · -- s7
    have hSf1 := cols_of_hdV (hH xSf1 (by simp [actH]))
    have hSf2 := cols_of_hdV (hH xSf2 (by simp [actH]))
    have hFt := cols_of_hdV (hH xFt (by simp [actH]))
    have hFth := cols_of_hdV (hH xFth (by simp [actH]))
    have hFtt := cols_of_hdV (hH xFtt (by simp [actH]))
    have f31 : E.trace 31 = E'.trace 31 := hSf1.1
    have f32 : E.trace 32 = E'.trace 32 := hSf1.2
    have f33 : E.trace 33 = E'.trace 33 := hSf2.1
    have f34 : E.trace 34 = E'.trace 34 := hSf2.2
    have f37 : E.trace 37 = E'.trace 37 := hFt.1
    have f38 : E.trace 38 = E'.trace 38 := hFt.2
    have f39 : E.trace 39 = E'.trace 39 := hFth.1
    have f40 : E.trace 40 = E'.trace 40 := hFth.2
    have f41 : E.trace 41 = E'.trace 41 := hFtt.1
    have f42 : E.trace 42 = E'.trace 42 := hFtt.2
    have f36 : E.trace 36 = E'.trace 36 := (fhv_op hB G.oh (by decide)).trans (fhv_op hB' G'.oh (by decide)).symm
    have f55 : E.trace 55 = E'.trace 55 := kb xFt (mH 6 (by decide)) f37
    have f56 : E.trace 56 = E'.trace 56 := kb xFth (mH 7 (by decide)) f39
    have f57 : E.trace 57 = E'.trace 57 := kb xFtt (mH 8 (by decide)) f41
    intro c hc
    by_cases hA : stIdx StateX.s7 ∈ actC c
    · interval_cases c <;> first | assumption | exact sel _ (by decide) | exact absurd hA (by decide)
    · exact off c hc hA
  · -- cons
    have hSf1 := cols_of_hdV (hH xSf1 (by simp [actH]))
    have hSf2 := cols_of_hdV (hH xSf2 (by simp [actH]))
    have hFh := cols_of_hdV (hH xFh (by simp [actH]))
    have hFt := cols_of_hdV (hH xFt (by simp [actH]))
    have f31 : E.trace 31 = E'.trace 31 := hSf1.1
    have f32 : E.trace 32 = E'.trace 32 := hSf1.2
    have f33 : E.trace 33 = E'.trace 33 := hSf2.1
    have f34 : E.trace 34 = E'.trace 34 := hSf2.2
    have f36 : E.trace 36 = E'.trace 36 := hFh.2
    have f37 : E.trace 37 = E'.trace 37 := hFt.1
    have f38 : E.trace 38 = E'.trace 38 := hFt.2
    have f55 : E.trace 55 = E'.trace 55 := kb xFt (mH 6 (by decide)) f37
    intro c hc
    by_cases hA : stIdx StateX.cons ∈ actC c
    · interval_cases c <;> first | assumption | exact sel _ (by decide) | exact absurd hA (by decide)
    · exact off c hc hA
  · -- s10
    have hSf1 := cols_of_hdV (hH xSf1 (by simp [actH]))
    have hSf2 := cols_of_hdV (hH xSf2 (by simp [actH]))
    have hFt := cols_of_hdV (hH xFt (by simp [actH]))
    have hFth := cols_of_hdV (hH xFth (by simp [actH]))
    have hFtt := cols_of_hdV (hH xFtt (by simp [actH]))
    have hFtth := cols_of_hdV (hH xFtth (by simp [actH]))
    have hFttt := cols_of_hdV (hH xFttt (by simp [actH]))
    have f31 : E.trace 31 = E'.trace 31 := hSf1.1
    have f32 : E.trace 32 = E'.trace 32 := hSf1.2
    have f33 : E.trace 33 = E'.trace 33 := hSf2.1
    have f34 : E.trace 34 = E'.trace 34 := hSf2.2
    have f37 : E.trace 37 = E'.trace 37 := hFt.1
    have f38 : E.trace 38 = E'.trace 38 := hFt.2
    have f39 : E.trace 39 = E'.trace 39 := hFth.1
    have f40 : E.trace 40 = E'.trace 40 := hFth.2
    have f41 : E.trace 41 = E'.trace 41 := hFtt.1
    have f42 : E.trace 42 = E'.trace 42 := hFtt.2
    have f43 : E.trace 43 = E'.trace 43 := hFtth.1
    have f44 : E.trace 44 = E'.trace 44 := hFtth.2
    have f45 : E.trace 45 = E'.trace 45 := hFttt.1
    have f46 : E.trace 46 = E'.trace 46 := hFttt.2
    have f19 : E.trace 19 = E'.trace 19 := hz1 (Or.inr rfl)
    have f20 : E.trace 20 = E'.trace 20 := (v_s10 hB G.oh).trans (f44.trans (v_s10 hB' G'.oh).symm)
    have f36 : E.trace 36 = E'.trace 36 := (fhv_s10 hB G.oh).trans (fhv_s10 hB' G'.oh).symm
    have f55 : E.trace 55 = E'.trace 55 := kb xFt (mH 6 (by decide)) f37
    have f56 : E.trace 56 = E'.trace 56 := kb xFth (mH 7 (by decide)) f39
    have f57 : E.trace 57 = E'.trace 57 := kb xFtt (mH 8 (by decide)) f41
    have f59 : E.trace 59 = E'.trace 59 := kb xFttt (mH 10 (by decide)) f45
    intro c hc
    by_cases hA : stIdx StateX.s10 ∈ actC c
    · interval_cases c <;> first | assumption | exact sel _ (by decide) | exact absurd hA (by decide)
    · exact off c hc hA
  · -- s10L
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := s10L_facts hB G.oh
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := s10L_facts hB' G'.oh
    obtain ⟨hv, hv'⟩ := hhalf rfl
    have hvr := (hv rfl).2
    have hvr' := (hv' rfl).2
    have g22 : E.trace v2X = E'.trace v2X := a1.trans (f28.trans b1.symm)
    obtain ⟨g20, g21⟩ := half_det hvr hvr' a9 b9 a6 (by rw [g22]; exact b6)
    have f20 : E.trace 20 = E'.trace 20 := g20
    have f21 : E.trace 21 = E'.trace 21 := g21
    have f22 : E.trace 22 = E'.trace 22 := g22
    have f23 : E.trace 23 = E'.trace 23 := by
      have b7' : (E.trace v2X - 1) * E'.trace wX = 1 := by rw [g22]; exact b7
      show E.trace wX = E'.trace wX
      linear_combination E'.trace wX * a7 - E.trace wX * b7'
    have f63 : E.trace 63 = E'.trace 63 := by
      show E.trace ax2X = E'.trace ax2X
      rw [a8, b8, g22, g21]
    have f48 : E.trace 48 = E'.trace 48 := a2.trans (f63.trans b2.symm)
    have hS' := hH xS (by simp [actH])
    have hE' := hH xE (by simp [actH])
    have hFtth' := hH xFtth (by simp [actH])
    have hSf1 := cols_of_hdV (a3.trans (hS'.trans b3.symm))
    have hSf2 := cols_of_hdV (a4.trans (hE'.trans b4.symm))
    have hFtth := cols_of_hdV hFtth'
    have hFttt := cols_of_hdV (a5.symm.trans (hFtth'.trans b5))
    have f31 : E.trace 31 = E'.trace 31 := hSf1.1
    have f32 : E.trace 32 = E'.trace 32 := hSf1.2
    have f33 : E.trace 33 = E'.trace 33 := hSf2.1
    have f34 : E.trace 34 = E'.trace 34 := hSf2.2
    have f43 : E.trace 43 = E'.trace 43 := hFtth.1
    have f44 : E.trace 44 = E'.trace 44 := hFtth.2
    have f45 : E.trace 45 = E'.trace 45 := hFttt.1
    have f46 : E.trace 46 = E'.trace 46 := hFttt.2
    intro c hc
    by_cases hA : stIdx StateX.s10L ∈ actC c
    · interval_cases c <;> first | assumption | exact sel _ (by decide) | exact absurd hA (by decide)
    · exact off c hc hA
  · -- s10T
    intro c hc
    by_cases hA : stIdx StateX.s10T ∈ actC c
    · interval_cases c <;> first | assumption | exact sel _ (by decide) | exact absurd hA (by decide)
    · exact off c hc hA

/-- **`row_eq` with `z1` needed only at axis `1`**: away from `v = 1`, `z1` is forced (`z1_eq_of_v_ne`). -/
theorem row_eq' (hp : 17 < p) {E E' : Env (ZMod p)} {st : StateX} (G : RowGatesP1 E st) (G' : RowGatesP1 E' st)
    (hfl : E.trace firstX = E'.trace firstX) (hll : E.trace lastX = E'.trace lastX)
    (hH : ∀ h ∈ actH st, hdV E h = hdV E' h)
    (hz1 : st = .s0 ∨ st = .s10 → E.trace vX = 1 → E.trace z1X = E'.trace z1X)
    (hhalf : st = .s10L → HalvingOK E .s10L ∧ HalvingOK E' .s10L) :
    ∀ c < 69, E.trace c = E'.trace c := by
  refine row_eq hp G G' hfl hll hH (fun hs => ?_) hhalf
  by_cases hv : E.trace vX = 1
  · exact hz1 hs hv
  · refine z1_eq_of_v_ne G G' hs ?_ hv
    rcases hs with rfl | rfl
    · exact (v_s0 G.base G.oh).trans ((cols_of_hdV (hH xFt (by simp [actH]))).2.trans
        (v_s0 G'.base G'.oh).symm)
    · exact (v_s10 G.base G.oh).trans ((cols_of_hdV (hH xFtth (by simp [actH]))).2.trans
        (v_s10 G'.base G'.oh).symm)

/-- **`row_eq` with `z1` from the path records' axis bound** (`AxOK` on every consumed record of both rows). -/
theorem row_eqA (hp : 17 < p) {E E' : Env (ZMod p)} {st : StateX} (G : RowGatesP1 E st) (G' : RowGatesP1 E' st)
    (hfl : E.trace firstX = E'.trace firstX) (hll : E.trace lastX = E'.trace lastX)
    (hH : ∀ h ∈ actH st, hdV E h = hdV E' h)
    (hAx : ∀ x ∈ activeX E, ServedJ8.AxOK x) (hAx' : ∀ x ∈ activeX E', ServedJ8.AxOK x)
    (hhalf : st = .s10L → HalvingOK E .s10L ∧ HalvingOK E' .s10L) :
    ∀ c < 69, E.trace c = E'.trace c := by
  refine row_eq' hp G G' hfl hll hH (fun hs hv => ?_) hhalf
  have hv' : E'.trace vX = 1 := by
    rcases hs with rfl | rfl
    · rw [← (v_s0 G.base G.oh).trans ((cols_of_hdV (hH xFt (by simp [actH]))).2.trans
        (v_s0 G'.base G'.oh).symm)]; exact hv
    · rw [← (v_s10 G.base G.oh).trans ((cols_of_hdV (hH xFtth (by simp [actH]))).2.trans
        (v_s10 G'.base G'.oh).symm)]; exact hv
  rw [z1_one_of_ax G.base hAx G.oh hs hv, z1_one_of_ax G'.base hAx' G'.oh hs hv']

end RowEq

/-! ## 4. The trace form -/

section Trace
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qX)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8 (baseX_of_sat stX stX_spec masksCX)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  (δ : ZMod p) (b : Basis (Fin 3) (ZMod p) K) (Pb : PubJ8 p)

/-- The compute row environment of a trace at row `i`. -/
abbrev envC (tr : TrJ8 (ZMod p)) (chalV pubVal : ℕ → ZMod p) (i : Fin Pb.n) : Env (ZMod p) :=
  Reify.envOfTrace (qX δ b Pb tr chalV pubVal) Pb.orbit.ω (Pb.nodes i) chalV pubVal

theorem envC_trace (tr : TrJ8 (ZMod p)) (chalV pubVal : ℕ → ZMod p) (i : Fin Pb.n) {c : ℕ} (hc : c < 123) :
    (envC δ b Pb tr chalV pubVal i).trace c = (tr.C ⟨c, hc⟩).eval (Pb.nodes i) :=
  envOfTrace_trace (qX δ b Pb tr chalV pubVal) _ _ _ _
    (show c < (computeChipVCLHX Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit).rap.w from hc)

/-- **Every compute row of an accepted canonical trace meets `RowGatesP1`** at its decoded state. -/
theorem rowGates_of (hp : 17 < p) {tr : TrJ8 (ZMod p)} {chalV pubVal : ℕ → ZMod p}
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit)
      (qX δ b Pb tr chalV pubVal))
    (hC : (canonC b Pb).Satisfies (sideCQ tr)) (i : Fin Pb.n) :
    RowGatesP1 (envC δ b Pb tr chalV pubVal i) (stX (envC δ b Pb tr chalV pubVal i)) := by
  have hB : BaseHoldsX (envC δ b Pb tr chalV pubVal i) :=
    baseX_of_sat Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit _ hsat _ (mem_rowNodeSet Pb.nodes i)
  have hOH := stX_spec hB (by rw [ZMod.ringChar_zmod_n]; exact hp)
  refine ⟨hB, hOH, fun c hc hA => ?_⟩
  have hs0 := stIdx_lt (stX (envC δ b Pb tr chalV pubVal i))
  have := compute_offAct_row b Pb tr hC (mem_rowNodeSet Pb.nodes i) hc hs0 hA
    (by rw [← envC_trace δ b Pb tr chalV pubVal i]; simpa using hOH _ hs0)
    (fun s hs hne => by rw [← envC_trace δ b Pb tr chalV pubVal i]; simpa [hne] using hOH s hs)
  rw [envC_trace δ b Pb tr chalV pubVal i (by omega)]
  exact this

/-- **`r0C` from row agreement.** Two traces accepted by `computeChipVCLHX` at the layout `Pb` and by `canonC`,
with, at every row, the same decoded state, equal `actH` handles, the axis bound `AxOK` on every consumed record
(this fixes `z1`), and the halving range on `s10L` rows, agree on the round-0 compute columns at every row node. -/
theorem r0C_of_rows (hp : 17 < p) {tr tr' : TrJ8 (ZMod p)} {chalV pubVal chalV' pubVal' : ℕ → ZMod p}
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit)
      (qX δ b Pb tr chalV pubVal))
    (hsat' : RAP.SatisfiesWithPreprocessing (computeChipVCLHX Pb.hn Pb.nodes b δ chalV' pubVal' Pb.orbit)
      (qX δ b Pb tr' chalV' pubVal'))
    (hinj : Function.Injective Pb.nodes)
    (hC : (canonC b Pb).Satisfies (sideCQ tr)) (hC' : (canonC b Pb).Satisfies (sideCQ tr'))
    (hst : ∀ i, stX (envC δ b Pb tr chalV pubVal i) = stX (envC δ b Pb tr' chalV' pubVal' i))
    (hH : ∀ i, ∀ h ∈ actH (stX (envC δ b Pb tr chalV pubVal i)),
      hdV (envC δ b Pb tr chalV pubVal i) h = hdV (envC δ b Pb tr' chalV' pubVal' i) h)
    (hAx : ∀ i, ∀ x ∈ activeX (envC δ b Pb tr chalV pubVal i), ServedJ8.AxOK x)
    (hAx' : ∀ i, ∀ x ∈ activeX (envC δ b Pb tr' chalV' pubVal' i), ServedJ8.AxOK x)
    (hhalf : ∀ i, stX (envC δ b Pb tr chalV pubVal i) = .s10L →
      HalvingOK (envC δ b Pb tr chalV pubVal i) .s10L ∧ HalvingOK (envC δ b Pb tr' chalV' pubVal' i) .s10L) :
    ∀ j : Fin 123, (j : ℕ) < 69 → ∀ i, (tr.C j).eval (Pb.nodes i) = (tr'.C j).eval (Pb.nodes i) := by
  intro j hj i
  have G := rowGates_of δ b Pb hp hsat hC i
  have G' : RowGatesP1 (envC δ b Pb tr' chalV' pubVal' i) (stX (envC δ b Pb tr chalV pubVal i)) := by
    rw [hst i]; exact rowGates_of δ b Pb hp hsat' hC' i
  have hbind := ((RapWalkJ8.computeChipVCLHX_sat_iff Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit _).mp hsat).1
  have hbind' := ((RapWalkJ8.computeChipVCLHX_sat_iff Pb.hn Pb.nodes b δ chalV' pubVal' Pb.orbit _).mp hsat').1
  have m := masksCX Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit _ hbind hinj i
  have m' := masksCX Pb.hn Pb.nodes b δ chalV' pubVal' Pb.orbit _ hbind' hinj i
  have e := row_eqA hp G G' (m.1.trans m'.1.symm) (m.2.trans m'.2.symm) (hH i) (hAx i) (hAx' i) (hhalf i) j hj
  rwa [envC_trace δ b Pb tr chalV pubVal i (by omega), envC_trace δ b Pb tr' chalV' pubVal' i (by omega)] at e

end Trace

/-! ## 5. From denoted nouns to handles -/

section Nouns
variable {p : ℕ} [Fact p.Prime]

/-- **Serial uniqueness across two denotations**: a cell (kind `1`) or a big atom (kind `2`) has one serial. On
two traces with the same round-0 cell columns and the same atom rows, `D = D'` and this is the distinctness of the
cell table's decoded nouns. -/
def SerialUnique (D D' : HX → Option Noun) : Prop :=
  ∀ k, (k = 1 ∨ k = 2) → ∀ i i' X, D (k, i) = some X → D' (k, i') = some X → i = i'

theorem kind_val {E : Env (ZMod p)} (hp : 17 < p) (hB : BaseHoldsX E) {h : Hd} (hh : h ∈ allHandlesX) :
    (E.trace h.k).val = 0 ∨ (E.trace h.k).val = 1 ∨ (E.trace h.k).val = 2 := by
  have s := kind_split hB h hh
  simp only [kcV, kbV] at s
  rcases s with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · have hk : E.trace h.k = ((0 : ℕ) : ZMod p) := by push_cast; linear_combination a + 2 * b
    left; rw [hk, val_nat (by omega)]
  · have hk : E.trace h.k = ((1 : ℕ) : ZMod p) := by push_cast; linear_combination a + 2 * b
    right; left; rw [hk, val_nat (by omega)]
  · have hk : E.trace h.k = ((2 : ℕ) : ZMod p) := by push_cast; linear_combination a + 2 * b
    right; right; rw [hk, val_nat (by omega)]

/-- **Equal defined denotations give equal handles** (wire kinds `0, 1, 2`; small atoms are `< p`, big atoms
`≥ p`; serial uniqueness for kinds `1, 2`). -/
theorem hdV_eq_of_nd (hp : 17 < p) {D D' : HX → Option Noun} (hD : DenOKX p D) (hD' : DenOKX p D')
    (hU : SerialUnique D D') {E E' : Env (ZMod p)} (hB : BaseHoldsX E) (hB' : BaseHoldsX E') {h : Hd}
    (hh : h ∈ allHandlesX) (hd : D (hdV E h) ≠ none) (hd' : D' (hdV E' h) ≠ none)
    (hn : nd D (hdV E h) = nd D' (hdV E' h)) : hdV E h = hdV E' h := by
  obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp hd
  obtain ⟨X', hX'⟩ := Option.ne_none_iff_exists'.mp hd'
  rw [nd_of hX, nd_of hX'] at hn
  subst hn
  have hk := kind_val hp hB hh
  have hk' := kind_val hp hB' hh
  have hv : (E.trace h.v).val < p := ZMod.val_lt _
  have hv' : (E'.trace h.v).val < p := ZMod.val_lt _
  simp only [hdV] at hX hX' ⊢
  generalize (E.trace h.k).val = k at hk hX ⊢
  generalize (E'.trace h.k).val = k' at hk' hX' ⊢
  generalize (E.trace h.v).val = v at hv hX ⊢
  generalize (E'.trace h.v).val = v' at hv' hX' ⊢
  rcases hk with rfl | rfl | rfl <;> rcases hk' with rfl | rfl | rfl
  · rw [hD.atom] at hX; rw [hD'.atom] at hX'
    rw [← hX'] at hX; cases hX; rfl
  · rw [hD.atom] at hX; obtain ⟨a, c, rfl⟩ := hD'.cell _ _ hX'; cases hX
  · rw [hD.atom] at hX; obtain ⟨n, rfl, hn⟩ := hD'.big _ _ hX'; cases hX; omega
  · rw [hD'.atom] at hX'; obtain ⟨a, c, rfl⟩ := hD.cell _ _ hX; cases hX'
  · rw [hU 1 (Or.inl rfl) v v' X hX hX']
  · obtain ⟨a, c, rfl⟩ := hD.cell _ _ hX; obtain ⟨n, hn, -⟩ := hD'.big _ _ hX'; cases hn
  · rw [hD'.atom] at hX'; obtain ⟨n, rfl, hn⟩ := hD.big _ _ hX; cases hX'; omega
  · obtain ⟨a, c, rfl⟩ := hD'.cell _ _ hX'; obtain ⟨n, hn, -⟩ := hD.big _ _ hX; cases hn
  · rw [hU 2 (Or.inr rfl) v v' X hX hX']

end Nouns

/-! ## 6. From the decode-to-run bridge -/

section Bridge
open Nock.Walk
open Nock.Edit.GenX (P1Frag genX)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemIJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8 (stX)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RowBridgeP1
open Nock.Jet (Registry)
variable {p : ℕ} [Fact p.Prime]

/-- `actH` without the `s10L` row's `f_tth` (the one handle the bridge does not see: its noun is the pair path
record's child). -/
def actHN : StateX → List Hd
  | .s10L => [xS, xF, xE]
  | s => actH s

theorem actH_sub (st : StateX) : ∀ h ∈ actH st, h ∈ allHandlesX := by
  intro h hh
  cases st <;> simp only [actH, List.mem_cons, List.not_mem_nil, or_false] at hh <;>
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact List.mem_map.mpr ⟨_, List.mem_range.mpr (by norm_num), rfl⟩

theorem mem_actHN {st : StateX} {h : Hd} (hh : h ∈ actH st) (hn : ¬ (st = .s10L ∧ h = xFtth)) :
    h ∈ actHN st := by
  cases st <;> try exact hh
  simp only [actH, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl
  · simp [actHN]
  · simp [actHN]
  · simp [actHN]
  · exact absurd ⟨rfl, rfl⟩ hn

/-- **Two decoded rows that agree with one honest row denote the same nouns** at every `actHN` handle (the subject,
formula and evaluation; the locally fixed handles `ActiveX`; the child-triple handles `sf1`, `sf2`). -/
theorem nd_agree {D D' : HX → Option Noun} {E E' : Env (ZMod p)} {st : StateX} {sk : GenX.SkelX}
    (A : RowAgreeX D (rowOfX E st) sk) (A' : RowAgreeX D' (rowOfX E' st) sk) :
    ∀ h ∈ actHN st, nd D (hdV E h) = nd D' (hdV E' h) := by
  obtain ⟨-, s1, f1, e1, K1, a1⟩ := A
  obtain ⟨-, s2, f2, e2, K2, a2⟩ := A'
  have hS : nd D (hdV E xS) = nd D' (hdV E' xS) := s1.trans s2.symm
  have hF : nd D (hdV E xF) = nd D' (hdV E' xF) := f1.trans f2.symm
  have hE : nd D (hdV E xE) = nd D' (hdV E' xE) := e1.trans e2.symm
  have kid : ∀ i (h1 : i < (kidsX (rowOfX E st)).length) (h1' : i < (kidsX (rowOfX E' st)).length)
      (h2 : i < sk.kids.length),
      nd D ((kidsX (rowOfX E st))[i]'h1).1 = nd D' ((kidsX (rowOfX E' st))[i]'h1').1 ∧
        nd D ((kidsX (rowOfX E st))[i]'h1).2.2 = nd D' ((kidsX (rowOfX E' st))[i]'h1').2.2 :=
    fun i h1 h1' h2 => ⟨(K1.2 i h1 h2).1.trans (K2.2 i h1' h2).1.symm,
      (K1.2 i h1 h2).2.2.trans (K2.2 i h1' h2).2.2.symm⟩
  have hlen := K1.1
  intro h hh
  cases st <;> simp only [actHN, actH, List.mem_cons, List.not_mem_nil, or_false] at hh
  · -- s0
    simp only [ActiveX, rowOfX] at a1 a2
    rcases hh with rfl | rfl | rfl | rfl
    · exact hS
    · exact hF
    · exact hE
    · exact a1.2.trans a2.2.symm
  · -- s7
    simp only [ActiveX, rowOfX] at a1 a2
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hS
    · exact hF
    · exact hE
    · exact a1.2.2.2.2.trans a2.2.2.2.2.symm
    · have k0 := kid 0 (by simp [kidsX, rowOfX]) (by simp [kidsX, rowOfX])
        (by rw [← hlen]; simp [kidsX, rowOfX])
      simpa [kidsX, rowOfX] using k0.1
    · exact a1.2.1.trans a2.2.1.symm
    · exact a1.2.2.1.trans a2.2.2.1.symm
    · exact a1.2.2.2.1.trans a2.2.2.2.1.symm
  · -- cons
    simp only [ActiveX, rowOfX] at a1 a2
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hS
    · exact hF
    · exact hE
    · exact a1.2.2.1.trans a2.2.2.1.symm
    · exact a1.2.2.2.trans a2.2.2.2.symm
    · exact a1.1.trans a2.1.symm
    · exact a1.2.1.trans a2.2.1.symm
  · -- s10
    simp only [ActiveX, rowOfX] at a1 a2
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hS
    · exact hF
    · exact hE
    · have k0 := kid 0 (by simp [kidsX, rowOfX]) (by simp [kidsX, rowOfX])
        (by rw [← hlen]; simp [kidsX, rowOfX])
      simpa [kidsX, rowOfX] using k0.2
    · have k1 := kid 1 (by simp [kidsX, rowOfX]) (by simp [kidsX, rowOfX])
        (by rw [← hlen]; simp [kidsX, rowOfX])
      simpa [kidsX, rowOfX] using k1.2
    · exact a1.2.1.trans a2.2.1.symm
    · exact a1.2.2.1.trans a2.2.2.1.symm
    · exact a1.2.2.2.1.trans a2.2.2.2.1.symm
    · exact a1.2.2.2.2.1.trans a2.2.2.2.2.1.symm
    · exact a1.2.2.2.2.2.trans a2.2.2.2.2.2.symm
  · -- s10L
    rcases hh with rfl | rfl | rfl
    · exact hS
    · exact hF
    · exact hE
  · -- s10T
    rcases hh with rfl | rfl | rfl
    · exact hS
    · exact hF
    · exact hE

variable {K : Type} [Field K]

/-- An atom has no subtree at an axis `≥ 2`. -/
theorem slot_atom_ge2 (a : ℕ) (ha : 2 ≤ a) (v : ℕ) : Noun.slot a (.atom v) = none := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega⟩
    rw [Noun.slot.eq_3]
    by_cases h1 : (c + 2) / 2 = 1
    · rw [h1, Noun.slot.eq_2]
    · rw [ih ((c + 2) / 2) (by omega) (by omega)]

theorem two_le_xor_one {a : ℕ} (ha : 2 ≤ a) : 2 ≤ a ^^^ 1 := by
  by_contra hlt
  have hinv : (a ^^^ 1) ^^^ 1 = a := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rcases (show a ^^^ 1 = 0 ∨ a ^^^ 1 = 1 by omega) with h | h <;> rw [h] at hinv <;> simp at hinv <;> omega

/-- **The `s10L` row's `f_tth` is the pair path record's child**: the subject handle is a cell, and
`D(f_tth) = slot ax2 S`. -/
theorem ftth_s10L (hp : 17 < p) {D : HX → Option Noun} (hD : DenOKX p D) {R : Registry} {comb : ℕ → Noun}
    {E : Env (ZMod p)} (hB : BaseHoldsX E) (hOH : OneHotAt E sS10L)
    (hOK : ∀ r ∈ activeX E, RecOKIJ8.RecOKI D R comb r) (hsem : RowSemX0 p D R (rowOfX E .s10L)) :
    ∃ S C, D (hdV E xS) = some S ∧ D (hdV E xFtth) = some C ∧ Noun.slot (E.trace ax2X).val S = some C := by
  obtain ⟨a1, a2, a3, -, -, -, -, -, -⟩ := s10L_facts hB hOH
  have h5 : E.trace 5 = 0 := oh_zero hOH (by decide) (by decide)
  have hpr : E.trace prX = 1 := (pr_eq hB h5).trans (oh_one hOH (by decide))
  have hm := (pair_mem (S := slot2X) (by simp [ChipHX.slotsX]) rfl hpr).1
  obtain ⟨a, -, ha, S, Ev, x, hS, -, hx, -⟩ := hsem
  have hSc : ∃ l r, S = .cell l r := by
    cases S with
    | atom v => rw [slot_atom_ge2 _ (two_le_xor_one ha)] at hx; cases hx
    | cell l r => exact ⟨l, r, rfl⟩
  obtain ⟨l, rr, rfl⟩ := hSc
  have hS' : D (hdV E xS) = some (.cell l rr) := hS
  have hk : E.trace xS.k = 1 := by
    have hkv := kind_val hp hB (h := xS) (List.mem_map.mpr ⟨0, by simp, rfl⟩)
    simp only [hdV] at hS'
    rcases hkv with h0 | h1 | h2
    · rw [h0, hD.atom] at hS'; cases hS'
    · exact ZMod.val_injective _ (h1.trans val_one'.symm)
    · rw [h2] at hS'; obtain ⟨n, hn, -⟩ := hD.big _ _ hS'; cases hn
  have hk1 : E.trace xSf1.k = 1 := by
    have h := congrArg Prod.fst a3
    simp only [hdV] at h
    rw [ZMod.val_injective _ h]; exact hk
  obtain ⟨Rt, C, hRt, hC, hsl⟩ := walk_of_recI hOK hm hk1
  rw [a3, hS'] at hRt
  cases hRt
  exact ⟨_, C, hS', hC, by rw [← a2]; exact hsl⟩

/-- **Row agreement from the bridge.** Two compute traces whose extraction-twin conclusions (`RowsAccXI`, the
forest goal) hold at denotations `D`, `D'`, whose root rows denote the claim's subject and formula, with the claim
formula in the fragment and the generated run `genX R fuel x.subject x.formula = some (tg, r)`, agree row by row:
the same decoded state, equal `actH` handles, and the halving range on `s10L` rows. Remaining inputs: serial
uniqueness `hU` and definedness of the `actH` handles (`hdef`, `hdef'`); the `s10L` row's `f_tth` noun is the pair
path record's child (`ftth_s10L`). -/
theorem rows_of_bridge [CharP K p] (hp : 2 ^ 63 + 1 < p) {R : Registry} (hR : R.Faithful) {n : ℕ} (hn : 1 ≤ n)
    {E E' : ℕ → Env (ZMod p)} {D D' : HX → Option Noun} (hD : DenOKX p D) (hD' : DenOKX p D')
    {comb comb' : ℕ → Noun}
    (A : RowsAccXI n E (fun r => stX (E r)) D R comb)
    (hG : ForestReconGoal (stVS K) (lblOf (rowsWX E (fun r => stX (E r)))) 1 n)
    (A' : RowsAccXI n E' (fun r => stX (E' r)) D' R comb')
    (hG' : ForestReconGoal (stVS K) (lblOf (rowsWX E' (fun r => stX (E' r)))) 1 n)
    (x : P8PublicClaim) (hs : D (hdV (E 0) xS) = some x.subject) (hf : D (hdV (E 0) xF) = some x.formula)
    (hs' : D' (hdV (E' 0) xS) = some x.subject) (hf' : D' (hdV (E' 0) xF) = some x.formula)
    (hfrag : P1Frag x.formula) {fuel : ℕ} {tg : NTree GenX.SkelX} {r : Noun}
    (hg : genX R fuel x.subject x.formula = some (tg, r))
    (hU : SerialUnique D D')
    (hdef : ∀ j < n, ∀ h ∈ actH (stX (E j)), D (hdV (E j) h) ≠ none)
    (hdef' : ∀ j < n, ∀ h ∈ actH (stX (E' j)), D' (hdV (E' j) h) ≠ none) :
    ∀ j < n, stX (E j) = stX (E' j) ∧ (∀ h ∈ actH (stX (E j)), hdV (E j) h = hdV (E' j) h) ∧
      (stX (E j) = .s10L → HalvingOK (E j) .s10L ∧ HalvingOK (E' j) .s10L) := by
  intro j hj
  have hp17 : 17 < p := by omega
  obtain ⟨hl, hrow⟩ := rowBridge (K := K) hp hR hD hn A hG x hs hf hfrag hg
  obtain ⟨hl', hrow'⟩ := rowBridge (K := K) hp hR hD' hn A' hG' x hs' hf' hfrag hg
  have R1 := hrow j (by omega)
  have R2 := hrow' j (by omega)
  have hst : stX (E j) = stX (E' j) := R1.1.trans R2.1.symm
  have R2' : RowAgreeX D' (rowOfX (E' j) (stX (E j))) ((bfsForest [tg])[j]'(by omega)).label := by
    rw [hst]; exact R2
  -- the halving range from the goal's tree
  have half : ∀ {E : ℕ → Env (ZMod p)} {D : HX → Option Noun} {comb : ℕ → Noun},
      RowsAccXI n E (fun r => stX (E r)) D R comb →
      ForestReconGoal (stVS K) (lblOf (rowsWX E (fun r => stX (E r)))) 1 n →
      stX (E j) = .s10L → HalvingOK (E j) .s10L := by
    intro E D comb A hG h10
    obtain ⟨t, hlab, -, hrw, hlink⟩ := goal_tree (K := K) hn hG
    obtain ⟨hlen, hlbl⟩ := bfs_at hlab
    have hjt : j < (bfsForest [t]).length := by omega
    have hnode : InTree t ((bfsForest [t])[j]'hjt) := by
      obtain ⟨c, hc, hcu⟩ := (mem_bfsForest [t] _).mp (List.getElem_mem hjt)
      rw [List.mem_singleton] at hc; subst hc; exact hcu
    have := halving_of_treeI hp A hrw hlink hnode (hlbl j hjt) (by simpa using h10)
    simpa using this
  have hdv : ∀ h ∈ actH (stX (E j)), ¬ (stX (E j) = .s10L ∧ h = xFtth) → hdV (E j) h = hdV (E' j) h :=
    fun h hh hc => hdV_eq_of_nd hp17 hD hD' hU (A.base j hj) (A'.base j hj) (actH_sub _ h hh)
      (hdef j hj h hh) (hdef' j hj h (hst ▸ hh)) (nd_agree R1 R2' h (mem_actHN hh hc))
  refine ⟨hst, fun h hh => ?_, fun h10 => ⟨half A hG h10, half A' hG' (hst ▸ h10)⟩⟩
  by_cases hc : stX (E j) = .s10L ∧ h = xFtth
  swap
  · exact hdv h hh hc
  obtain ⟨h10, rfl⟩ := hc
  have h10' : stX (E' j) = .s10L := hst ▸ h10
  -- the row semantics of both `s10L` rows
  have hO : OneHotAt (E j) sS10L := by
    have := (A.oh j hj : OneHotAt (E j) (stIdx (stX (E j)))); rw [h10] at this; exact this
  have hO' : OneHotAt (E' j) sS10L := by
    have := (A'.oh j hj : OneHotAt (E' j) (stIdx (stX (E' j)))); rw [h10'] at this; exact this
  have hv := half A hG h10
  have hv' := half A' hG' h10'
  have sem := (rowSemXI_of_chip hD hp17 (A.base j hj) .s10L hO (A.served j hj) hv).1.1
    (preRow_triv (by simp [rowOfX]) (by simp [rowOfX]) (by simp [rowOfX]))
  have sem' := (rowSemXI_of_chip hD' hp17 (A'.base j hj) .s10L hO' (A'.served j hj) hv').1.1
    (preRow_triv (by simp [rowOfX]) (by simp [rowOfX]) (by simp [rowOfX]))
  obtain ⟨S, C, hS, hC, hsl⟩ := ftth_s10L hp17 hD (A.base j hj) hO (A.served j hj) sem
  obtain ⟨S', C', hS', hC', hsl'⟩ := ftth_s10L hp17 hD' (A'.base j hj) hO' (A'.served j hj) sem'
  -- the same subject noun and the same sibling axis
  have hmS : xS ∈ actH (stX (E j)) := by rw [h10]; simp [actH]
  have hmF : xF ∈ actH (stX (E j)) := by rw [h10]; simp [actH]
  have hSS : S = S' := by
    have := nd_agree R1 R2' xS (mem_actHN hmS (by rintro ⟨-, h⟩; exact absurd h (by decide)))
    rwa [nd_of hS, nd_of hS'] at this
  have hFF := cols_of_hdV (hdv xF hmF (by rintro ⟨-, h⟩; exact absurd h (by decide)))
  have hax := ax2_eq (A.base j hj) (A'.base j hj) hO hO' hv hv' hFF.2
  rw [hSS, hax, hsl'] at hsl
  cases hsl
  exact hdV_eq_of_nd hp17 hD hD' hU (A.base j hj) (A'.base j hj) (actH_sub _ _ hh)
    (by rw [hC]; simp) (by rw [hC']; simp) (by rw [nd_of hC, nd_of hC'])

end Bridge

/-! ## 7. The open facts `r0C` and `claim` -/

section Final
open Nock.Walk
open Nock.Edit.GenX (P1Frag genX)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemIJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8 (stX)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qX)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.Jet (Registry)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  (δ : ZMod p) (b : Basis (Fin 3) (ZMod p) K) (Pb : PubJ8 p)

theorem envsN_envC (tr : TrJ8 (ZMod p)) (chalV pubVal : ℕ → ZMod p) (i : Fin Pb.n) :
    envsN Pb.hn Pb.nodes chalV pubVal Pb.orbit (qX δ b Pb tr chalV pubVal) i = envC δ b Pb tr chalV pubVal i := by
  simp [envsN, i.isLt]

/-- **`O.r0C` from the extraction twins.** Two traces accepted by `computeChipVCLHX` at the layout `Pb` and by
`canonC`, whose twin conclusions (`RowsAccXI`, the forest goal, at the compute row environments `envsN`) hold at
denotations `D`, `D'`, with root rows denoting the claim's subject and formula, the claim formula in the fragment,
and the generated run `genX R fuel x.subject x.formula = some (tg, r)`, agree on the round-0 compute columns at every
row node, given: serial uniqueness `hU` (the cell-table side), definedness of the `actH` handles (`hdef`, `hdef'`),
and the axis bound `AxOK` on every consumed record (`hAx`, `hAx'`: `ServedJ8.servedP_of_balancesJ8` at the
providers' `WalkKJ8.axOK_p_row`, inside the soundness chain; it fixes `z1` at axis `1`). -/
theorem r0C_of_twins [CharP K p] (hp : 2 ^ 63 + 1 < p) {tr tr' : TrJ8 (ZMod p)}
    {chalV pubVal chalV' pubVal' : ℕ → ZMod p}
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit)
      (qX δ b Pb tr chalV pubVal))
    (hsat' : RAP.SatisfiesWithPreprocessing (computeChipVCLHX Pb.hn Pb.nodes b δ chalV' pubVal' Pb.orbit)
      (qX δ b Pb tr' chalV' pubVal'))
    (hinj : Function.Injective Pb.nodes)
    (hC : (canonC b Pb).Satisfies (sideCQ tr)) (hC' : (canonC b Pb).Satisfies (sideCQ tr'))
    {R : Registry} (hR : R.Faithful) {D D' : HX → Option Noun} (hD : DenOKX p D) (hD' : DenOKX p D')
    {comb comb' : ℕ → Noun}
    (A : RowsAccXI Pb.n (fun r => envsN Pb.hn Pb.nodes chalV pubVal Pb.orbit (qX δ b Pb tr chalV pubVal) r)
      (fun r => stX (envsN Pb.hn Pb.nodes chalV pubVal Pb.orbit (qX δ b Pb tr chalV pubVal) r)) D R comb)
    (hG : ForestReconGoal (stVS K)
      (lblOf (rowsWX (fun r => envsN Pb.hn Pb.nodes chalV pubVal Pb.orbit (qX δ b Pb tr chalV pubVal) r)
        (fun r => stX (envsN Pb.hn Pb.nodes chalV pubVal Pb.orbit (qX δ b Pb tr chalV pubVal) r)))) 1 Pb.n)
    (A' : RowsAccXI Pb.n (fun r => envsN Pb.hn Pb.nodes chalV' pubVal' Pb.orbit (qX δ b Pb tr' chalV' pubVal') r)
      (fun r => stX (envsN Pb.hn Pb.nodes chalV' pubVal' Pb.orbit (qX δ b Pb tr' chalV' pubVal') r)) D' R comb')
    (hG' : ForestReconGoal (stVS K)
      (lblOf (rowsWX (fun r => envsN Pb.hn Pb.nodes chalV' pubVal' Pb.orbit (qX δ b Pb tr' chalV' pubVal') r)
        (fun r => stX (envsN Pb.hn Pb.nodes chalV' pubVal' Pb.orbit (qX δ b Pb tr' chalV' pubVal') r)))) 1 Pb.n)
    (x : P8PublicClaim)
    (hs : D (hdV (envsN Pb.hn Pb.nodes chalV pubVal Pb.orbit (qX δ b Pb tr chalV pubVal) 0) xS) = some x.subject)
    (hf : D (hdV (envsN Pb.hn Pb.nodes chalV pubVal Pb.orbit (qX δ b Pb tr chalV pubVal) 0) xF) = some x.formula)
    (hs' : D' (hdV (envsN Pb.hn Pb.nodes chalV' pubVal' Pb.orbit (qX δ b Pb tr' chalV' pubVal') 0) xS) =
      some x.subject)
    (hf' : D' (hdV (envsN Pb.hn Pb.nodes chalV' pubVal' Pb.orbit (qX δ b Pb tr' chalV' pubVal') 0) xF) =
      some x.formula)
    (hfrag : P1Frag x.formula) {fuel : ℕ} {tg : NTree GenX.SkelX} {r : Noun}
    (hg : genX R fuel x.subject x.formula = some (tg, r))
    (hU : SerialUnique D D')
    (hdef : ∀ i : Fin Pb.n, ∀ h ∈ actH (stX (envC δ b Pb tr chalV pubVal i)),
      D (hdV (envC δ b Pb tr chalV pubVal i) h) ≠ none)
    (hdef' : ∀ i : Fin Pb.n, ∀ h ∈ actH (stX (envC δ b Pb tr' chalV' pubVal' i)),
      D' (hdV (envC δ b Pb tr' chalV' pubVal' i) h) ≠ none)
    (hAx : ∀ i : Fin Pb.n, ∀ x ∈ activeX (envC δ b Pb tr chalV pubVal i), ServedJ8.AxOK x)
    (hAx' : ∀ i : Fin Pb.n, ∀ x ∈ activeX (envC δ b Pb tr' chalV' pubVal' i), ServedJ8.AxOK x):
    ∀ j : Fin 123, (j : ℕ) < 69 → ∀ i, (tr.C j).eval (Pb.nodes i) = (tr'.C j).eval (Pb.nodes i) := by
  have rows := rows_of_bridge (K := K) hp hR Pb.hn hD hD' A hG A' hG' x hs hf hs' hf' hfrag hg hU
    (fun j hj h hh => by
      have := hdef ⟨j, hj⟩ h (by simpa only [← envsN_envC] using hh)
      simpa only [← envsN_envC] using this)
    (fun j hj h hh => by
      have := hdef' ⟨j, hj⟩ h (by simpa only [← envsN_envC] using hh)
      simpa only [← envsN_envC] using this)
  have rows' : ∀ i : Fin Pb.n, _ := fun i => rows i i.isLt
  simp only [envsN_envC] at rows'
  exact r0C_of_rows δ b Pb (by omega) hsat hsat' hinj hC hC' (fun i => (rows' i).1) (fun i => (rows' i).2.1)
    hAx hAx' (fun i => (rows' i).2.2)

open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun isCellN) in
/-- **`O.claim` from serial uniqueness**: the claim cell records denote the claim nouns on both cell tables
(`hcell`, `hcell'`, as `LinkJ8A.hsoundJ8XUA`'s `hcell`), so their serials agree. -/
theorem claim_of_unique {D D' : HX → Option Noun} (hU : SerialUnique D D') {c : P8PublicClaim}
    {m m' : FrameVS.ClaimMsgVS}
    (hcell : ∀ k : Fin 3, isCellN (claimNoun c k) = true → D (1, (m k).1) = some (claimNoun c k))
    (hcell' : ∀ k : Fin 3, isCellN (claimNoun c k) = true → D' (1, (m' k).1) = some (claimNoun c k)) :
    ∀ k, isCellN (claimNoun c k) = true → (m k).1 = (m' k).1 :=
  fun k hk => hU 1 (Or.inl rfl) _ _ _ (hcell k hk) (hcell' k hk)

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.six_of
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.kb_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.s10L_facts
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.half_det
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.z1_eq_of_v_ne
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.row_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.row_eq'
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.rowGates_of
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.r0C_of_rows
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.hdV_eq_of_nd
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.nd_agree
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.rows_of_bridge
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.r0C_of_twins
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.claim_of_unique
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.z1_one_of_ax
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.row_eqA
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1.ftth_s10L
