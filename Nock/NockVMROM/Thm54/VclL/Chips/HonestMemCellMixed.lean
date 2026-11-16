/-
  Nock/NockVMROM/Thm54/VclL/Chips/HonestMemCellMixed.lean

  **The honest cell table's mixed gates.**

  At the honest environment of row `i` of `honestCellQ … vals`, the gathered `𝕂`-environment reads the
  role values of `vals i` (`cellEKh_trace`, `cellEKh_traceNext`), the challenge / public leaves are the
  supplied `chals` / `pubs`, and every `𝕂′` equation of `Cell.qEqs` evaluates (`QE.ev`) to the
  semantic statement recorded in `CellMixedFacts`.  `cell_mixed_gates_hold`: the `44` mixed gates
  vanish, given those facts (the exact converse of `cellRow_gates` / `cell_gates` on the mixed half).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemCell
import Nock.NockVMROM.Thm54.VclL.Chips.Telescope

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.T0Tower
open Module
open scoped Polynomial

noncomputable section

section Env
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (ω : F) (chals pubs : ℕ → K)
  (vals : Fin n → CellVals F (Quad (algebraMap F K δF)))

/-- The base environment of row `i` of the honest cell trace. -/
abbrev cellEFh (i : Fin n) : Env F :=
  Reify.envOfTrace (honestCellQ δF b hn nodes vals) ω (nodes i) (slotVal b 129 chals) (slotVal b 129 pubs)

/-- The gathered `𝕂`-environment of row `i`. -/
abbrev cellEKh (i : Fin n) : Env K :=
  gatherEnv b ((cellTemplate δF).col0 3) (cellEFh δF b hn nodes ω chals pubs vals i)

theorem cell_col0 (r : ℕ) (kind : VarKind) : (cellTemplate δF).col0 3 kind r = 129 + 3 * r := by
  simp [ChipTemplate.col0, cellTemplate_baseCols]

theorem cellEKh_trace (hinj : Function.Injective nodes) (i : Fin n) {r : ℕ} (hr : r < 32) :
    (cellEKh δF b hn nodes ω chals pubs vals i).trace r = roleVal δF (vals i) r := by
  refine gather_trace b _ _ r _ fun k => ?_
  rw [cell_col0, env_trace hn nodes hinj _ ω _ _ i (show 129 + 3 * r + (k : ℕ) < 225 by have := k.isLt; omega)]
  have h1 : (129 + 3 * r + (k : ℕ) - 129) / 3 = r := by have := k.isLt; omega
  have h2 : (129 + 3 * r + (k : ℕ) - 129) % 3 = (k : ℕ) := by have := k.isLt; omega
  have h0 : (129 + 3 * r + (k : ℕ)) ≠ 0 := by omega
  have h1' : (129 + 3 * r + (k : ℕ)) ≠ 1 := by omega
  have h3 : ¬ (129 + 3 * r + (k : ℕ)) < 129 := by omega
  unfold fullCol cellCol
  rw [if_neg h0, if_neg h1', if_neg h3, h1]
  exact congrArg (coord b _) (Fin.ext h2)

theorem cellEKh_traceNext (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) {r : ℕ} (hr : r < 32) :
    (cellEKh δF b hn nodes ω chals pubs vals i).traceNext r = roleVal δF (vals ⟨(i : ℕ) + 1, hi⟩) r := by
  refine gather_traceNext b _ _ r _ fun k => ?_
  rw [cell_col0, env_traceNext hn nodes hinj _ ω _ _ hadj i hi (show 129 + 3 * r + (k : ℕ) < 225 by have := k.isLt; omega)]
  have h1 : (129 + 3 * r + (k : ℕ) - 129) / 3 = r := by have := k.isLt; omega
  have h2 : (129 + 3 * r + (k : ℕ) - 129) % 3 = (k : ℕ) := by have := k.isLt; omega
  have h0 : (129 + 3 * r + (k : ℕ)) ≠ 0 := by omega
  have h1' : (129 + 3 * r + (k : ℕ)) ≠ 1 := by omega
  have h3 : ¬ (129 + 3 * r + (k : ℕ)) < 129 := by omega
  unfold fullCol cellCol
  rw [if_neg h0, if_neg h1', if_neg h3, h1]
  exact congrArg (coord b _) (Fin.ext h2)


theorem cellEKh_ev_var (hinj : Function.Injective nodes) (i : Fin n) {s : ℕ} (hs : s < 16) :
    (QE.var (2 * s) : QE F).ev δF (cellEKh δF b hn nodes ω chals pubs vals i)
        (cellEFh δF b hn nodes ω chals pubs vals i) = (vals i).qslot s := by
  rw [ev_var, cellEKh_trace δF b hn nodes ω chals pubs vals hinj i (by omega),
    cellEKh_trace δF b hn nodes ω chals pubs vals hinj i (show 2 * s + 1 < 32 by omega)]
  have e1 : (2 * s) % 2 = 0 := by omega
  have e2 : (2 * s) / 2 = s := by omega
  have e3 : (2 * s + 1) % 2 ≠ 0 := by omega
  have e4 : (2 * s + 1) / 2 = s := by omega
  simp only [roleVal, e1, e2, e3, e4, if_true, if_false]
  exact Quad.mk_re_im _ _

theorem cellEKh_ev_next (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) {s : ℕ} (hs : s < 16) :
    (QE.next (2 * s) : QE F).ev δF (cellEKh δF b hn nodes ω chals pubs vals i)
        (cellEFh δF b hn nodes ω chals pubs vals i) = (vals ⟨(i : ℕ) + 1, hi⟩).qslot s := by
  rw [ev_next, cellEKh_traceNext δF b hn nodes ω chals pubs vals hinj hadj i hi (by omega),
    cellEKh_traceNext δF b hn nodes ω chals pubs vals hinj hadj i hi (show 2 * s + 1 < 32 by omega)]
  have e1 : (2 * s) % 2 = 0 := by omega
  have e2 : (2 * s) / 2 = s := by omega
  have e3 : (2 * s + 1) % 2 ≠ 0 := by omega
  have e4 : (2 * s + 1) / 2 = s := by omega
  simp only [roleVal, e1, e2, e3, e4, if_true, if_false]
  exact Quad.mk_re_im _ _

end Env


section Facts
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (ω : F) (chals pubs : ℕ → K)
  (vals : Fin n → CellVals F (Quad (algebraMap F K δF)))

/-- The semantic key vectors of a cell row (the `𝕂′` records of the chip's four lookups). -/
def vKeyOf (c : CellVals F (Quad (algebraMap F K δF))) : Fin 5 → Quad (algebraMap F K δF) :=
  ![c.p.size, c.p.dyck, c.p.leaf, Quad.mk _ (algebraMap F K c.lo) (algebraMap F K c.hi),
    liftQ δF c.idx]
def lKeyOf (c : CellVals F (Quad (algebraMap F K δF))) : Fin 5 → Quad (algebraMap F K δF) :=
  ![c.l.size, c.l.dyck, c.l.leaf, Quad.mk _ (algebraMap F K c.loL) (algebraMap F K c.hiL),
    liftQ δF c.idL]
def rKeyOf (c : CellVals F (Quad (algebraMap F K δF))) : Fin 5 → Quad (algebraMap F K δF) :=
  ![c.r.size, c.r.dyck, c.r.leaf, Quad.mk _ (algebraMap F K c.loR) (algebraMap F K c.hiR),
    liftQ δF c.idR]
def xKeyOf (c : CellVals F (Quad (algebraMap F K δF))) (s : F) : Fin 11 → Quad (algebraMap F K δF) :=
  ![c.p.size, c.p.dyck, c.p.leaf, c.l.size, c.l.dyck, c.l.leaf, c.r.size, c.r.dyck, c.r.leaf,
    liftQ δF c.idx, liftQ δF s]

/-- The validity row term `mv·inv_v − inv_L − inv_R` of a row. -/
def vTermOf (c : CellVals F (Quad (algebraMap F K δF))) : Quad (algebraMap F K δF) :=
  liftQ δF c.mv * c.vInv - c.lInv - c.rInv
/-- The export row term `mx·inv₀ + mx1·inv₁`. -/
def xTermOf (c : CellVals F (Quad (algebraMap F K δF))) : Quad (algebraMap F K δF) :=
  liftQ δF c.mx * c.x0Inv + liftQ δF c.mx1 * c.x1Inv

/-- **The semantic content of the `22` `𝕂′` equations at row `i`** (all at the sampled `z`, `ρ`, `γ`
through `FiniteIO.compress`; the accumulators' init / step / terminal). -/
structure CellMixedFacts (γ ρ z : Quad (algebraMap F K δF))
    (vals : Fin n → CellVals F (Quad (algebraMap F K δF))) (i : Fin n) : Prop where
  hz : z ≠ 0
  cons : (vals i).p = ComputeTable.FP.cons z (vals i).l (vals i).r
  atomL : (vals i).wL = 0 → (vals i).l = ComputeTable.FP.atomFP z (liftQ δF (vals i).aL)
  atomR : (vals i).wR = 0 → (vals i).r = ComputeTable.FP.atomFP z (liftQ δF (vals i).aR)
  vInv_den : (vals i).vInv * FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (vals i)) = 1
  lInv_den : (vals i).lInv * FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (lKeyOf δF (vals i)) =
    liftQ δF (vals i).wL
  rInv_den : (vals i).rInv * FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf δF (vals i)) =
    liftQ δF (vals i).wR
  lInv_free : (vals i).wL = 0 → (vals i).lInv = 0
  rInv_free : (vals i).wR = 0 → (vals i).rInv = 0
  x0Inv_den : (vals i).x0Inv * FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (vals i) 0) = 1
  x1Inv_den : (vals i).x1Inv * FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (vals i) 1) = 1
  vAcc_init : (i : ℕ) = 0 → (vals i).vAcc = vTermOf δF (vals i)
  vAcc_step : ∀ hi : (i : ℕ) + 1 < n,
    (vals ⟨(i : ℕ) + 1, hi⟩).vAcc = (vals i).vAcc + vTermOf δF (vals ⟨(i : ℕ) + 1, hi⟩)
  vAcc_term : (i : ℕ) + 1 = n → (vals i).vAcc = Quad.mk _ (pubs 0) (pubs 1)
  xAcc_init : (i : ℕ) = 0 → (vals i).xAcc = xTermOf δF (vals i)
  xAcc_step : ∀ hi : (i : ℕ) + 1 < n,
    (vals ⟨(i : ℕ) + 1, hi⟩).xAcc = (vals i).xAcc + xTermOf δF (vals ⟨(i : ℕ) + 1, hi⟩)
  xAcc_term : (i : ℕ) + 1 = n → (vals i).xAcc = Quad.mk _ (pubs 2) (pubs 3)


theorem cellEKh_chal (i : Fin n) : (cellEKh δF b hn nodes ω chals pubs vals i).chal = chals :=
  funext fun j => gather_chal_cell δF b chals _ rfl j

theorem cellEKh_pub (i : Fin n) (j : ℕ) : (cellEKh δF b hn nodes ω chals pubs vals i).pub j = pubs j :=
  gather_pub_cell δF b pubs _ rfl j

theorem cell_roles (hinj : Function.Injective nodes) (i : Fin n) :
    let eK := cellEKh δF b hn nodes ω chals pubs vals i
    let eF := cellEFh δF b hn nodes ω chals pubs vals i
    (QE.var 0 : QE F).ev δF eK eF = (vals i).p.size ∧ (QE.var 2 : QE F).ev δF eK eF = (vals i).p.dyck ∧
    (QE.var 4 : QE F).ev δF eK eF = (vals i).p.leaf ∧ (QE.var 6 : QE F).ev δF eK eF = (vals i).l.size ∧
    (QE.var 8 : QE F).ev δF eK eF = (vals i).l.dyck ∧ (QE.var 10 : QE F).ev δF eK eF = (vals i).l.leaf ∧
    (QE.var 12 : QE F).ev δF eK eF = (vals i).r.size ∧ (QE.var 14 : QE F).ev δF eK eF = (vals i).r.dyck ∧
    (QE.var 16 : QE F).ev δF eK eF = (vals i).r.leaf ∧ (QE.var 18 : QE F).ev δF eK eF = (vals i).vInv ∧
    (QE.var 20 : QE F).ev δF eK eF = (vals i).lInv ∧ (QE.var 22 : QE F).ev δF eK eF = (vals i).rInv ∧
    (QE.var 24 : QE F).ev δF eK eF = (vals i).x0Inv ∧ (QE.var 26 : QE F).ev δF eK eF = (vals i).vAcc ∧
    (QE.var 28 : QE F).ev δF eK eF = (vals i).xAcc ∧ (QE.var 30 : QE F).ev δF eK eF = (vals i).x1Inv := by
  intro eK eF
  have h := fun (s : ℕ) (hs : s < 16) => cellEKh_ev_var δF b hn nodes ω chals pubs vals hinj i hs
  exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num),
    h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num), h 8 (by norm_num), h 9 (by norm_num),
    h 10 (by norm_num), h 11 (by norm_num), h 12 (by norm_num), h 13 (by norm_num), h 14 (by norm_num),
    h 15 (by norm_num)⟩

theorem cell_roles_next (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    let eK := cellEKh δF b hn nodes ω chals pubs vals i
    let eF := cellEFh δF b hn nodes ω chals pubs vals i
    let v' := vals ⟨(i : ℕ) + 1, hi⟩
    (QE.next 18 : QE F).ev δF eK eF = v'.vInv ∧ (QE.next 20 : QE F).ev δF eK eF = v'.lInv ∧
    (QE.next 22 : QE F).ev δF eK eF = v'.rInv ∧ (QE.next 24 : QE F).ev δF eK eF = v'.x0Inv ∧
    (QE.next 26 : QE F).ev δF eK eF = v'.vAcc ∧ (QE.next 28 : QE F).ev δF eK eF = v'.xAcc ∧
    (QE.next 30 : QE F).ev δF eK eF = v'.x1Inv := by
  intro eK eF v'
  have h := fun (s : ℕ) (hs : s < 16) =>
    cellEKh_ev_next δF b hn nodes ω chals pubs vals hinj hadj i hi hs
  exact ⟨h 9 (by norm_num), h 10 (by norm_num), h 11 (by norm_num), h 12 (by norm_num),
    h 13 (by norm_num), h 14 (by norm_num), h 15 (by norm_num)⟩

/-- The base columns of row `i` and `i + 1` that the mixed gates read. -/
theorem cell_cols (hinj : Function.Injective nodes) (i : Fin n) :
    let eF := cellEFh δF b hn nodes ω chals pubs vals i
    eF.trace 2 = (vals i).idx ∧ eF.trace 3 = (vals i).idL ∧ eF.trace 4 = (vals i).idR ∧
    eF.trace 5 = (vals i).wL ∧ eF.trace 6 = (vals i).wR ∧ eF.trace 7 = (vals i).aL ∧
    eF.trace 8 = (vals i).aR ∧ eF.trace 9 = (vals i).lo ∧ eF.trace 10 = (vals i).hi ∧
    eF.trace 11 = (vals i).loL ∧ eF.trace 12 = (vals i).hiL ∧ eF.trace 13 = (vals i).loR ∧
    eF.trace 14 = (vals i).hiR ∧ eF.trace 16 = (vals i).mv ∧ eF.trace 17 = (vals i).mx ∧
    eF.trace 128 = (vals i).mx1 := by
  intro eF
  have h := fun (j : ℕ) (h2 : 2 ≤ j) (hj : j < 129) =>
    cellEnv_base δF b hn nodes ω (slotVal b 129 chals) (slotVal b 129 pubs) vals hinj i h2 hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [h _ (by norm_num) (by norm_num)]; simp [CellVals.base])

theorem cell_cols_next (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    let eF := cellEFh δF b hn nodes ω chals pubs vals i
    eF.traceNext 16 = (vals ⟨(i : ℕ) + 1, hi⟩).mv ∧ eF.traceNext 17 = (vals ⟨(i : ℕ) + 1, hi⟩).mx ∧
    eF.traceNext 128 = (vals ⟨(i : ℕ) + 1, hi⟩).mx1 := by
  intro eF
  have h := fun (j : ℕ) (h2 : 2 ≤ j) (hj : j < 129) =>
    cellEnv_next_base δF b hn nodes ω (slotVal b 129 chals) (slotVal b 129 pubs) vals hinj hadj i hi h2 hj
  refine ⟨?_, ?_, ?_⟩ <;>
    (rw [h _ (by norm_num) (by norm_num)]; simp [CellVals.base])

/-- The three key vectors of the cell row equal the semantic ones. -/
theorem cell_keyVec_v (hinj : Function.Injective nodes) (i : Fin n) :
    keyVec δF 5 Cell.vKeyP (cellEKh δF b hn nodes ω chals pubs vals i)
      (cellEFh δF b hn nodes ω chals pubs vals i) = vKeyOf δF (vals i) := by
  obtain ⟨p0, p1, p2, -⟩ := cell_roles δF b hn nodes ω chals pubs vals hinj i
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c16, c17, c128⟩ :=
    cell_cols δF b hn nodes ω chals pubs vals hinj i
  funext c
  fin_cases c <;>
    simp [keyVec, Cell.vKeyP, QFP.entries, QFP.var, Cell.pR, vKeyOf, p0, p1, p2, ev_mk2, ev_base,
      CoeffExpr.eval, cv, Cell.lo, Cell.hi, Cell.idx, c2, c9, c10]

theorem cell_keyVec_l (hinj : Function.Injective nodes) (i : Fin n) :
    keyVec δF 5 Cell.vKeyL (cellEKh δF b hn nodes ω chals pubs vals i)
      (cellEFh δF b hn nodes ω chals pubs vals i) = lKeyOf δF (vals i) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, -⟩ := cell_roles δF b hn nodes ω chals pubs vals hinj i
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c16, c17, c128⟩ :=
    cell_cols δF b hn nodes ω chals pubs vals hinj i
  funext c
  fin_cases c <;>
    simp [keyVec, Cell.vKeyL, QFP.entries, QFP.var, Cell.lR, lKeyOf, p3, p4, p5, ev_mk2, ev_base,
      CoeffExpr.eval, cv, Cell.loL, Cell.hiL, Cell.idL, c3, c11, c12]

theorem cell_keyVec_r (hinj : Function.Injective nodes) (i : Fin n) :
    keyVec δF 5 Cell.vKeyR (cellEKh δF b hn nodes ω chals pubs vals i)
      (cellEFh δF b hn nodes ω chals pubs vals i) = rKeyOf δF (vals i) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, -⟩ := cell_roles δF b hn nodes ω chals pubs vals hinj i
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c16, c17, c128⟩ :=
    cell_cols δF b hn nodes ω chals pubs vals hinj i
  funext c
  fin_cases c <;>
    simp [keyVec, Cell.vKeyR, QFP.entries, QFP.var, Cell.rR, rKeyOf, p6, p7, p8, ev_mk2, ev_base,
      CoeffExpr.eval, cv, Cell.loR, Cell.hiR, Cell.idR, c4, c13, c14]

theorem cell_keyVec_x (hinj : Function.Injective nodes) (i : Fin n) (s : F) :
    keyVec δF 11 (Cell.xKeyS s) (cellEKh δF b hn nodes ω chals pubs vals i)
      (cellEFh δF b hn nodes ω chals pubs vals i) = xKeyOf δF (vals i) s := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, -⟩ := cell_roles δF b hn nodes ω chals pubs vals hinj i
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c16, c17, c128⟩ :=
    cell_cols δF b hn nodes ω chals pubs vals hinj i
  funext c
  fin_cases c <;>
    simp [keyVec, Cell.xKeyS, Cell.xKey, QFP.entries, QFP.var, Cell.pR, Cell.lR, Cell.rR, xKeyOf,
      p0, p1, p2, p3, p4, p5, p6, p7, p8, ev_base, CoeffExpr.eval, cv, cst, Cell.idx, c2]

/-- `(1 − w)`-masked equations: the lifted factor vanishes when `w ≠ 0` (boolean `w`). -/
theorem lift_notE_mul (w : F) (hw : w * (w - 1) = 0) (P : Quad (algebraMap F K δF))
    (h : w = 0 → P = 0) : liftQ δF (1 - w) * P = 0 := by
  by_cases h0 : w = 0
  · rw [h h0]; simp
  · have : w = 1 := by
      rcases mul_eq_zero.mp hw with h' | h'
      · exact absurd h' h0
      · linear_combination h'
    simp [this]

variable [DecidableEq F] in
/-- **The `22` `𝕂′` equations hold at the honest environment of row `i`.** -/
theorem cell_qEqs_hold (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hb : CellBaseFacts vals i) (γ ρ z : Quad (algebraMap F K δF))
    (hok : ChalsOK δF chals γ ρ 11) (hz : Quad.mk _ (chals 2) (chals 3) = z)
    (hf : CellMixedFacts δF pubs γ ρ z vals i) :
    ∀ e ∈ Cell.qEqs δF, e.ev δF (cellEKh δF b hn nodes ω chals pubs vals i)
      (cellEFh δF b hn nodes ω chals pubs vals i) = 0 := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15⟩ :=
    cell_roles δF b hn nodes ω chals pubs vals hinj i
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c16, c17, c128⟩ :=
    cell_cols δF b hn nodes ω chals pubs vals hinj i
  set eK := cellEKh δF b hn nodes ω chals pubs vals i with heK
  set eF := cellEFh δF b hn nodes ω chals pubs vals i with heF
  have m0 : eF.trace 0 = if (i : ℕ) = 0 then 1 else 0 :=
    cellEnv_mask0 δF b hn nodes ω (slotVal b 129 chals) (slotVal b 129 pubs) vals hinj i
  have m1 : eF.trace 1 = if i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0 :=
    cellEnv_mask1 δF b hn nodes ω (slotVal b 129 chals) (slotVal b 129 pubs) vals hinj i
  have hzQ : (zQ : QE F).ev δF eK eF = z := by
    rw [zQ, ev_chal, cellEKh_chal]; exact hz
  have hrQ : (rQ : QE F).ev δF eK eF = ρ := by
    rw [rQ, ev_chal, cellEKh_chal]; exact hok.1
  have hch : ChalsOK δF eK.chal γ ρ 11 := by rw [heK, cellEKh_chal]; exact hok
  have dV : (den δF Cell.vKeyP).ev δF eK eF = FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (vals i)) := by
    rw [den_ev_compress' δF Cell.vKeyP (m := 5) rfl _ _ γ ρ (chalsOK_mono δF (by norm_num) hch),
      cell_keyVec_v δF b hn nodes ω chals pubs vals hinj i]
  have dL : (den δF Cell.vKeyL).ev δF eK eF = FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (lKeyOf δF (vals i)) := by
    rw [den_ev_compress' δF Cell.vKeyL (m := 5) rfl _ _ γ ρ (chalsOK_mono δF (by norm_num) hch),
      cell_keyVec_l δF b hn nodes ω chals pubs vals hinj i]
  have dR : (den δF Cell.vKeyR).ev δF eK eF = FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (rKeyOf δF (vals i)) := by
    rw [den_ev_compress' δF Cell.vKeyR (m := 5) rfl _ _ γ ρ (chalsOK_mono δF (by norm_num) hch),
      cell_keyVec_r δF b hn nodes ω chals pubs vals hinj i]
  have dX : ∀ s : F, (den δF (Cell.xKeyS s)).ev δF eK eF =
      FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (vals i) s) := fun s => by
    rw [den_ev_compress' δF (Cell.xKeyS s) (m := 11) rfl _ _ γ ρ hch,
      cell_keyVec_x δF b hn nodes ω chals pubs vals hinj i s]
  have hFirst : (i : ℕ) = 0 → eF.trace 0 = 1 := fun h => by rw [m0, if_pos h]
  have hNFirst : (i : ℕ) ≠ 0 → eF.trace 0 = 0 := fun h => by rw [m0, if_neg h]
  have hiff : i = (⟨n - 1, Nat.sub_lt hn (by omega)⟩ : Fin n) ↔ (i : ℕ) + 1 = n := by
    constructor
    · intro h; rw [h]; simp; omega
    · intro h; apply Fin.ext; simp; omega
  have hLast : (i : ℕ) + 1 = n → eF.trace 1 = 1 := fun h => by rw [m1, if_pos (hiff.mpr h)]
  have hNLast : (i : ℕ) + 1 ≠ n → eF.trace 1 = 0 := fun h => by
    rw [m1, if_neg (fun h' => h (hiff.mp h'))]
  have hvT : (Cell.vTerm true : QE F).ev δF eK eF = vTermOf δF (vals i) := by
    simp only [Cell.vTerm, if_true, ev_sub, ev_scale, CoeffExpr.eval, cv, Cell.mv, Cell.vProvInv,
      Cell.consLInv, Cell.consRInv, c16, p9, p10, p11, vTermOf]
  have hxT : (Cell.xTerm true : QE F).ev δF eK eF = xTermOf δF (vals i) := by
    simp only [Cell.xTerm, if_true, ev_add, ev_scale, CoeffExpr.eval, cv, Cell.mx, Cell.mx1,
      Cell.xProvInv, Cell.xProvInv1, c17, c128, p12, p15, xTermOf]
  have hvTn : ∀ hi : (i : ℕ) + 1 < n,
      (Cell.vTerm false : QE F).ev δF eK eF = vTermOf δF (vals ⟨(i : ℕ) + 1, hi⟩) := fun hi => by
    obtain ⟨q18, q20, q22, -⟩ := cell_roles_next δF b hn nodes ω chals pubs vals hinj hadj i hi
    obtain ⟨d16, -, -⟩ := cell_cols_next δF b hn nodes ω chals pubs vals hinj hadj i hi
    simp only [Cell.vTerm, Bool.false_eq_true, if_false, ev_sub, ev_scale, CoeffExpr.eval, nv,
      Cell.mv, Cell.vProvInv, Cell.consLInv, Cell.consRInv, heK, heF, d16, q18, q20, q22, vTermOf]
  have hxTn : ∀ hi : (i : ℕ) + 1 < n,
      (Cell.xTerm false : QE F).ev δF eK eF = xTermOf δF (vals ⟨(i : ℕ) + 1, hi⟩) := fun hi => by
    obtain ⟨-, -, -, q24, -, -, q30⟩ := cell_roles_next δF b hn nodes ω chals pubs vals hinj hadj i hi
    obtain ⟨-, d17, d128⟩ := cell_cols_next δF b hn nodes ω chals pubs vals hinj hadj i hi
    simp only [Cell.xTerm, Bool.false_eq_true, if_false, ev_add, ev_scale, CoeffExpr.eval, nv,
      Cell.mx, Cell.mx1, Cell.xProvInv, Cell.xProvInv1, heK, heF, d17, d128, q24, q30, xTermOf]
  have hnotE : ∀ j, (notE (cv j) : CoeffExpr F).eval eF = 1 - eF.trace j := fun j => rfl
  intro e he
  simp only [Cell.qEqs, Cell.consEqs, Cell.atomEqs, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with (((rfl | rfl | rfl) | (rfl | rfl | rfl)) | (rfl | rfl | rfl)) |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- cons size
    simp only [QFP.var, Cell.pR, Cell.lR, Cell.rR, Nat.reduceAdd, zero_add, ev_sub, ev_mul, p0, p3, p6]
    have := congrArg ComputeTable.FP.size hf.cons
    simp only [ComputeTable.FP.cons] at this
    exact sub_eq_zero.mpr this
  · -- cons leaf
    simp only [QFP.var, Cell.pR, Cell.lR, Cell.rR, Nat.reduceAdd, zero_add, ev_sub, ev_mul, ev_add, p2, p5, p8, p3]
    have := congrArg ComputeTable.FP.leaf hf.cons
    simp only [ComputeTable.FP.cons] at this
    exact sub_eq_zero.mpr this
  · -- cons dyck
    simp only [QFP.var, Cell.pR, Cell.lR, Cell.rR, Nat.reduceAdd, zero_add, ev_sub, ev_mul, ev_add, hzQ, p1, p4, p7, p3]
    have h := congrArg ComputeTable.FP.dyck hf.cons
    simp only [ComputeTable.FP.cons] at h
    rw [h]
    have hz0 := hf.hz
    field_simp
    ring
  · -- atom L size
    simp only [QFP.var, Cell.lR, Nat.reduceAdd, zero_add, ev_scale, ev_sub, hnotE, Cell.wL, c5, hzQ, p3]
    exact lift_notE_mul δF _ hb.wL_bool _ (fun h0 => by rw [hf.atomL h0]; simp)
  · -- atom L dyck
    simp only [QFP.var, Cell.lR, Nat.reduceAdd, zero_add, ev_scale, hnotE, Cell.wL, c5, p4]
    exact lift_notE_mul δF _ hb.wL_bool _ (fun h0 => by rw [hf.atomL h0]; simp)
  · -- atom L leaf
    simp only [QFP.var, Cell.lR, Nat.reduceAdd, zero_add, ev_scale, ev_sub, ev_base, hnotE, Cell.wL,
      Cell.aL, CoeffExpr.eval, cv, c5, c7, p5]
    exact lift_notE_mul δF _ hb.wL_bool _ (fun h0 => by rw [hf.atomL h0]; simp)
  · -- atom R size
    simp only [QFP.var, Cell.rR, Nat.reduceAdd, zero_add, ev_scale, ev_sub, hnotE, Cell.wR, c6, hzQ, p6]
    exact lift_notE_mul δF _ hb.wR_bool _ (fun h0 => by rw [hf.atomR h0]; simp)
  · -- atom R dyck
    simp only [QFP.var, Cell.rR, Nat.reduceAdd, zero_add, ev_scale, hnotE, Cell.wR, c6, p7]
    exact lift_notE_mul δF _ hb.wR_bool _ (fun h0 => by rw [hf.atomR h0]; simp)
  · -- atom R leaf
    simp only [QFP.var, Cell.rR, Nat.reduceAdd, zero_add, ev_scale, ev_sub, ev_base, hnotE, Cell.wR,
      Cell.aR, CoeffExpr.eval, cv, c6, c8, p8]
    exact lift_notE_mul δF _ hb.wR_bool _ (fun h0 => by rw [hf.atomR h0]; simp)
  · -- vInv
    simp only [ev_sub, ev_mul, ev_one, Cell.vProvInv, p9, dV]
    exact sub_eq_zero.mpr hf.vInv_den
  · -- lInv
    simp only [ev_sub, ev_mul, ev_base, CoeffExpr.eval, cv, Cell.wL, Cell.consLInv, p10, dL, c5]
    exact sub_eq_zero.mpr hf.lInv_den
  · -- rInv
    simp only [ev_sub, ev_mul, ev_base, CoeffExpr.eval, cv, Cell.wR, Cell.consRInv, p11, dR, c6]
    exact sub_eq_zero.mpr hf.rInv_den
  · -- lInv free
    simp only [ev_scale, hnotE, Cell.wL, Cell.consLInv, c5, p10]
    exact lift_notE_mul δF _ hb.wL_bool _ hf.lInv_free
  · -- rInv free
    simp only [ev_scale, hnotE, Cell.wR, Cell.consRInv, c6, p11]
    exact lift_notE_mul δF _ hb.wR_bool _ hf.rInv_free
  · -- x0Inv
    simp only [ev_sub, ev_mul, ev_one, Cell.xProvInv, p12, dX]
    exact sub_eq_zero.mpr hf.x0Inv_den
  · -- x1Inv
    simp only [ev_sub, ev_mul, ev_one, Cell.xProvInv1, p15, dX]
    exact sub_eq_zero.mpr hf.x1Inv_den
  · -- validity accumulator init
    simp only [ev_scale, ev_sub, hvT, CoeffExpr.eval, cv, Cell.isF, Cell.vAcc, p13]
    by_cases h0 : (i : ℕ) = 0
    · rw [hFirst h0]; simp [liftQ, hf.vAcc_init h0]
    · rw [hNFirst h0]; simp [liftQ]
  · -- validity accumulator step
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, hnotE, Cell.isL, hLast hl]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      have q26 : (QE.next 26 : QE F).ev δF eK eF = (vals ⟨(i : ℕ) + 1, hi⟩).vAcc :=
        (cell_roles_next δF b hn nodes ω chals pubs vals hinj hadj i hi).2.2.2.2.1
      simp only [ev_scale, ev_sub, hvTn hi, hnotE, Cell.isL, hNLast hl, Cell.vAcc, q26, p13]
      have := hf.vAcc_step hi
      simp only [liftQ, sub_zero, map_one, one_mul]
      linear_combination this
  · -- validity accumulator terminal
    have hpub : (QE.pub 0 : QE F).ev δF eK eF = Quad.mk _ (pubs 0) (pubs 1) := by
      rw [ev_pub, cellEKh_pub, cellEKh_pub]
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, ev_sub, hpub, CoeffExpr.eval, cv, Cell.isL, hLast hl, Cell.vAcc, p13]
      simp [liftQ, hf.vAcc_term hl]
    · simp only [ev_scale, CoeffExpr.eval, cv, Cell.isL, hNLast hl]; simp [liftQ]
  · -- export accumulator init
    simp only [ev_scale, ev_sub, hxT, CoeffExpr.eval, cv, Cell.isF, Cell.xAcc, p14]
    by_cases h0 : (i : ℕ) = 0
    · rw [hFirst h0]; simp [liftQ, hf.xAcc_init h0]
    · rw [hNFirst h0]; simp [liftQ]
  · -- export accumulator step
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, hnotE, Cell.isL, hLast hl]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      have q28 : (QE.next 28 : QE F).ev δF eK eF = (vals ⟨(i : ℕ) + 1, hi⟩).xAcc :=
        (cell_roles_next δF b hn nodes ω chals pubs vals hinj hadj i hi).2.2.2.2.2.1
      simp only [ev_scale, ev_sub, hxTn hi, hnotE, Cell.isL, hNLast hl, Cell.xAcc, q28, p14]
      have := hf.xAcc_step hi
      simp only [liftQ, sub_zero, map_one, one_mul]
      linear_combination this
  · -- export accumulator terminal
    have hpub : (QE.pub 2 : QE F).ev δF eK eF = Quad.mk _ (pubs 2) (pubs 3) := by
      rw [ev_pub, cellEKh_pub, cellEKh_pub]
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, ev_sub, hpub, CoeffExpr.eval, cv, Cell.isL, hLast hl, Cell.xAcc, p14]
      simp [liftQ, hf.xAcc_term hl]
    · simp only [ev_scale, CoeffExpr.eval, cv, Cell.isL, hNLast hl]; simp [liftQ]

variable [DecidableEq F] in
/-- **The `44` mixed gates of the cell chip vanish at the honest environment of row `i`.** -/
theorem cell_mixed_gates_hold (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hb : CellBaseFacts vals i) (γ ρ z : Quad (algebraMap F K δF))
    (hok : ChalsOK δF chals γ ρ 11) (hz : Quad.mk _ (chals 2) (chals 3) = z)
    (hf : CellMixedFacts δF pubs γ ρ z vals i) :
    ∀ g ∈ Cell.mixedGates δF,
      g.eval (cellEKh δF b hn nodes ω chals pubs vals i) (cellEFh δF b hn nodes ω chals pubs vals i) = 0 := by
  intro g hg
  obtain ⟨e, he, hge⟩ := List.mem_flatMap.mp hg
  have h := cell_qEqs_hold δF b hn nodes ω chals pubs vals hinj hadj i hb γ ρ z hok hz hf e he
  simp only [QE.ev, Quad.mk_eq_zero_iff] at h
  simp only [QE.gates, List.mem_cons, List.not_mem_nil, or_false] at hge
  rcases hge with rfl | rfl
  · exact h.1
  · exact h.2

end Facts

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
