import Nock.NockVMROM.Thm54.VclL.Handle.HonestK8
import Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ

/-!
# J-8b part 2: honest acceptance of `cellChipHQKW` (the cell twin providing the wire key `keyHK`)

The honest trace is built **directly from the original 129-column cell trace** (not from the
`cellChipHQK` trace: its `𝕂′` roles carry the `keyH` inverse), extending `cellChip` by
`mh` (129), `kb` (130, 131), `inv` (132, 133) and the four new `𝕂′` roles with the `keyHK`
denominator. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Nock.NockVMROM.Thm54.VclL.Handle.HonestKW

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK Nock.NockVMROM.Thm54.VclL.Handle.RangeHQ
open Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ Nock.NockVMROM.Thm54.VclL.Handle.HonestK8
open Nock.NockVMROM.Thm54.VclL.Handle.QGates
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The template (restated from `CellTwinKW`) -/

section Gates
variable {F : Type} [Field F] [DecidableEq F]

def gatesQ (δF : F) : List (QE F) :=
  QE.sub (QE.mul δF (QE.var CellHQ.invHQ) (HQ.denKeyQ δF keyHK)) QE.one :: (CellHQ.gatesQ δF).tail

def gates (δF : F) : List (MixedExpr F) := (gatesQ δF).flatMap QE.gates

theorem gates_deg_all (δF : F) : (gates δF).all (fun g => decide (g.degree ≤ 4)) = true := by
  simp [gates, gatesQ, CellHQ.gatesQ, HQ.denKeyQ, HQ.rlcQ, HQ.gpowQ, HQ.gamQ, HQ.rhoQ, keyHK, CellH.valE,
    QE.gates, QE.var, QE.next, QE.chal, QE.pub, QE.base, QE.zero, QE.one, QE.add, QE.sub, QE.mul,
    QE.scale, MixedExpr.degree, CoeffExpr.degree]

theorem mixed_deg (δF : F) : ∀ g ∈ Cell.mixedGates δF ++ gates δF, g.degree ≤ 4 := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact cellMixed_deg δF g hg
  · simpa using List.all_eq_true.mp (gates_deg_all δF) g hg

def cellTemplateHQKW (δF : F) : ChipTemplate F :=
  { CellTwinK.cellTemplateHQK δF with
    mixedTransition := Cell.mixedGates δF ++ gates δF
    mixedTransition_deg := mixed_deg δF }

theorem cellTemplateHQKW_baseCols (δF : F) : (cellTemplateHQKW δF).baseCols = 134 :=
  CellTwinK.cellTemplateHQK_baseCols δF
theorem cellTemplateHQKW_extCols (δF : F) : (cellTemplateHQKW δF).extCols = 36 :=
  CellTwinK.cellTemplateHQK_extCols δF

theorem cellTemplateHQKW_width (δF : F) : (cellTemplateHQKW δF).width 3 = 242 := by
  unfold ChipTemplate.width; rw [cellTemplateHQKW_baseCols, cellTemplateHQKW_extCols]

end Gates

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]

noncomputable def cellChipHQKW (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
    (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    FixedPreprocessingRAP F where
  rap := expandChip (cellTemplateHQKW δF) b (slotVal b 134 chals) (slotVal b 134 pubs) orbit
    (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 134 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

end Chip

/-! ## 2. Congruence of the `keyHK` denominator -/

section Cong
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) (chals : ℕ → K)

theorem keyHK_below134 : ∀ g ∈ (keyHK (F := F)), colsBelow 134 g = true := by
  intro g hg
  simp only [keyHK, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;>
    simp [colsBelow, CellH.valE, cv, notE, Cell.idx, Cell.wL, Cell.wR, Cell.idL, Cell.idR, Cell.aL,
      Cell.aR, kbL, kbR]

theorem gatherW_chal (e : Env F) (hc : e.chal = slotVal b 134 chals) (r : ℕ) :
    (gatherEnv b ((cellTemplateHQKW δF).col0 3) e).chal r = chals r := by
  simp only [gatherEnv, ChipTemplate.col0, hc, cellTemplateHQKW_baseCols]
  exact sum_slotVal b 134 r chals

theorem rlcQW_congr (eK eK' : Env K) (eF eF' : Env F) (hc : eK.chal = eK'.chal)
    (ht : ∀ j < 134, eF.trace j = eF'.trace j) (hn : ∀ j < 134, eF.traceNext j = eF'.traceNext j) :
    ∀ (l : List (CoeffExpr F)), (∀ g ∈ l, colsBelow 134 g = true) → ∀ m,
      (HQ.rlcQ δF m l).ev δF eK eF = (HQ.rlcQ δF m l).ev δF eK' eF'
  | [], _, m => by simp [HQ.rlcQ, ev_zero]
  | g :: r, hl, m => by
      simp only [HQ.rlcQ, ev_add, ev_mul, ev_base, CellTraceHQ.gpowQ_congr δF eK eK' eF eF' hc m,
        colsBelow_eval (hl g (by simp)) ht hn,
        rlcQW_congr eK eK' eF eF' hc ht hn r (fun g' hg' => hl g' (by simp [hg'])) (m + 1)]

theorem denKeyQW_congr (e e' : Env F) (hc : e.chal = slotVal b 134 chals) (hc' : e'.chal = slotVal b 134 chals)
    (ht : ∀ j < 134, e.trace j = e'.trace j) (hn : ∀ j < 134, e.traceNext j = e'.traceNext j) :
    (HQ.denKeyQ δF (keyHK (F := F))).ev δF (gatherEnv b ((cellTemplateHQKW δF).col0 3) e) e =
      (HQ.denKeyQ δF (keyHK (F := F))).ev δF (gatherEnv b ((cellTemplateHQKW δF).col0 3) e') e' := by
  have hcc : (gatherEnv b ((cellTemplateHQKW δF).col0 3) e).chal =
      (gatherEnv b ((cellTemplateHQKW δF).col0 3) e').chal := by
    funext r; rw [gatherW_chal δF b chals e hc, gatherW_chal δF b chals e' hc']
  simp only [HQ.denKeyQ, ev_add, HQ.rhoQ, ev_chal, hcc,
    rlcQW_congr δF _ _ e e' hcc ht hn _ keyHK_below134 0]

end Cong

/-! ## 3. The honest trace -/

section Data
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (mhv kbLv kbRv : Fin n → F)

/-- New columns: `mh` 129, `kb` 130/131, `inv` 132/133, roles `iv` 230..235, `av` 236..241. -/
def newW (iv av : Fin n → Quad (algebraMap F K δF)) : ℕ → Fin n → F := fun j i =>
  if j = 129 then mhv i
  else if j = kbL then kbLv i else if j = kbR then kbRv i
  else if j = invL then (col Cell.loL i + col Cell.hiL i)⁻¹
  else if j = invR then (col Cell.loR i + col Cell.hiR i)⁻¹
  else if 230 ≤ j ∧ j < 233 then coordN b (Quad.re _ (iv i)) (j - 230)
  else if 233 ≤ j ∧ j < 236 then coordN b (Quad.im _ (iv i)) (j - 233)
  else if 236 ≤ j ∧ j < 239 then coordN b (Quad.re _ (av i)) (j - 236)
  else if 239 ≤ j ∧ j < 242 then coordN b (Quad.im _ (av i)) (j - 239) else 0

def colW (iv av : Fin n → Quad (algebraMap F K δF)) : ℕ → Fin n → F :=
  extColF 129 134 ((cellTemplate δF).width 3) col (newW δF b col mhv kbLv kbRv iv av)

def EW (iv av : Fin n → Quad (algebraMap F K δF)) (i : Fin n) : Env F :=
  Reify.envOfTrace (honestQ hn nodes (colW δF b col mhv kbLv kbRv iv av) ((cellTemplateHQKW δF).width 3))
    orbit.ω (nodes i) (slotVal b 134 chals) (slotVal b 134 pubs)

/-- The `keyHK` denominator of row `i` (zero role fill: it reads base columns only). -/
def dRowW (i : Fin n) : Quad (algebraMap F K δF) :=
  (HQ.denKeyQ δF (keyHK (F := F))).ev δF
    (gatherEnv b ((cellTemplateHQKW δF).col0 3)
      (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv (fun _ => 0) (fun _ => 0) i))
    (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv (fun _ => 0) (fun _ => 0) i)

def dNW (j : ℕ) : Quad (algebraMap F K δF) :=
  if hj : j < n then dRowW δF b hn nodes orbit chals pubs col mhv kbLv kbRv ⟨j, hj⟩ else 1

def ivW : Fin n → Quad (algebraMap F K δF) := fun i =>
  (dRowW δF b hn nodes orbit chals pubs col mhv kbLv kbRv i)⁻¹

def avW : Fin n → Quad (algebraMap F K δF) := fun i =>
  ∑ j ∈ Finset.range (i + 1), liftQ δF (CellTraceH.mN mhv j) *
    (dNW δF b hn nodes orbit chals pubs col mhv kbLv kbRv j)⁻¹

/-- **The honest 242-column `cellChipHQKW` trace.** -/
def cellTraceHQKW :=
  honestQ hn nodes (colW δF b col mhv kbLv kbRv (ivW δF b hn nodes orbit chals pubs col mhv kbLv kbRv)
    (avW δF b hn nodes orbit chals pubs col mhv kbLv kbRv)) ((cellTemplateHQKW δF).width 3)

theorem colW_lt134 (iv av iv' av' : Fin n → Quad (algebraMap F K δF)) (j : ℕ) (hj : j < 134) :
    colW δF b col mhv kbLv kbRv iv av j = colW δF b col mhv kbLv kbRv iv' av' j := by
  funext i
  simp only [colW, extColF, newW]
  by_cases h1 : j < 129
  · simp [h1]
  · have h2 : ¬ (230 ≤ j ∧ j < 233) := by omega
    have h3 : ¬ (233 ≤ j ∧ j < 236) := by omega
    have h4 : ¬ (236 ≤ j ∧ j < 239) := by omega
    have h5 : ¬ (239 ≤ j ∧ j < 242) := by omega
    simp [h1, hj, h2, h3, h4, h5]

theorem EW_below (iv av iv' av' : Fin n → Quad (algebraMap F K δF)) (i : Fin n) (j : ℕ) (hj : j < 134) :
    (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i).trace j =
        (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv' av' i).trace j ∧
    (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i).traceNext j =
        (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv' av' i).traceNext j := by
  have hw : j < (cellTemplateHQKW δF).width 3 := by rw [cellTemplateHQKW_width]; omega
  have hq := honestQ_congr hn nodes (colW δF b col mhv kbLv kbRv iv av) (colW δF b col mhv kbLv kbRv iv' av')
    ((cellTemplateHQKW δF).width 3) ⟨j, hw⟩ (colW_lt134 δF b col mhv kbLv kbRv iv av iv' av' j hj)
  simp [EW, Reify.envOfTrace, dif_pos hw, hq]

theorem den_indepW (iv av : Fin n → Quad (algebraMap F K δF)) (i : Fin n) :
    (HQ.denKeyQ δF (keyHK (F := F))).ev δF
      (gatherEnv b ((cellTemplateHQKW δF).col0 3) (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i))
      (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i) =
        dRowW δF b hn nodes orbit chals pubs col mhv kbLv kbRv i :=
  denKeyQW_congr δF b chals _ _ rfl rfl
    (fun j hj => (EW_below δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av (fun _ => 0) (fun _ => 0) i j hj).1)
    (fun j hj => (EW_below δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av (fun _ => 0) (fun _ => 0) i j hj).2)

end Data

/-! ## 4. The four wire-key handle gates at the honest fill -/

section Gates4
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

theorem cellHQW_gates_honest (eK : Env K) (eF : Env F) (N i : ℕ) (hi : i < N)
    (m : ℕ → F) (d : ℕ → Quad (algebraMap F K δF)) (hd0 : d i ≠ 0)
    (hF : eF.trace Cell.isF = if i = 0 then 1 else 0)
    (hL : eF.trace Cell.isL = if i + 1 = N then 1 else 0)
    (hm : eF.trace CellH.mh = m i) (hmn : i + 1 < N → eF.traceNext CellH.mh = m (i + 1))
    (hden : (HQ.denKeyQ δF (keyHK (F := F))).ev δF eK eF = d i)
    (hinv : Quad.mk _ (eK.trace CellHQ.invHQ) (eK.trace (CellHQ.invHQ + 1)) = (d i)⁻¹)
    (hinvn : i + 1 < N → Quad.mk _ (eK.traceNext CellHQ.invHQ) (eK.traceNext (CellHQ.invHQ + 1)) =
      (d (i + 1))⁻¹)
    (hacc : Quad.mk _ (eK.trace CellHQ.accHQ) (eK.trace (CellHQ.accHQ + 1)) =
      ∑ j ∈ Finset.range (i + 1), liftQ δF (m j) * (d j)⁻¹)
    (haccn : i + 1 < N → Quad.mk _ (eK.traceNext CellHQ.accHQ) (eK.traceNext (CellHQ.accHQ + 1)) =
      ∑ j ∈ Finset.range (i + 2), liftQ δF (m j) * (d j)⁻¹)
    (hpub : Quad.mk _ (eK.pub CellHQ.pubHQ) (eK.pub (CellHQ.pubHQ + 1)) =
      ∑ j ∈ Finset.range N, liftQ δF (m j) * (d j)⁻¹) :
    ∀ g ∈ gates δF, g.eval eK eF = 0 := by
  refine flat_gates_of_ev δF _ eK eF fun e he => ?_
  simp only [gatesQ, CellHQ.gatesQ, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [ev_sub, ev_mul, ev_var, hinv, hden, ev_one, inv_mul_cancel₀ hd0, sub_self]
  · rw [ev_scale, ev_sub, ev_var, ev_scale, ev_var, hacc, hinv]
    simp only [cv, CoeffExpr.eval, hF, hm]
    by_cases h0 : i = 0
    · subst h0; simp [liftQ]
    · simp [h0, liftQ]
  · rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var, ev_scale, ev_next]
    simp only [notE, cv, nv, CoeffExpr.eval, hL]
    by_cases hl : i + 1 = N
    · simp [hl, liftQ]
    · have hlt : i + 1 < N := by omega
      rw [haccn hlt, hacc, hinvn hlt, hmn hlt, Finset.sum_range_succ _ (i + 1)]
      simp [hl, liftQ]
  · rw [ev_scale, ev_sub, ev_var, ev_pub, hacc, hpub]
    simp only [cv, CoeffExpr.eval, hL]
    by_cases hl : i + 1 = N
    · subst hl; simp [liftQ]
    · simp [hl, liftQ]

end Gates4

/-! ## 5. The two new gate groups and the acceptance theorem -/

section Main
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (col : ℕ → Fin n → F) (mhv kbLv kbRv : Fin n → F)

theorem fullCol_colW_low (iv av : Fin n → Quad (algebraMap F K δF)) (j : ℕ) (h2 : 2 ≤ j) (h129 : j < 129)
    (i' : Fin n) : fullCol hn (colW δF b col mhv kbLv kbRv iv av) j i' = col j i' := by
  simp only [fullCol, colW, extColF]
  rw [if_neg (by omega), if_neg (by omega), if_pos h129]

theorem fullCol_colW_mid (iv av : Fin n → Quad (algebraMap F K δF)) (j : ℕ) (h1 : 129 ≤ j) (h2 : j < 134)
    (i' : Fin n) : fullCol hn (colW δF b col mhv kbLv kbRv iv av) j i' =
      newW δF b col mhv kbLv kbRv iv av j i' := by
  have h3 : ¬ j < 129 := by omega
  simp [fullCol, colW, extColF, h3, h2, show j ≠ 0 by omega, show j ≠ 1 by omega]

/-- **The five side gates per child** at the honest fill. -/
theorem kindW_gates (hinj : Function.Injective nodes)
    (hL : ∀ i, SideOK (kbLv i) (col Cell.wL i) (col Cell.loL i) (col Cell.hiL i))
    (hR : ∀ i, SideOK (kbRv i) (col Cell.wR i) (col Cell.loR i) (col Cell.hiR i))
    (iv av : Fin n → Quad (algebraMap F K δF)) (i : Fin n) :
    ∀ g ∈ (kindGates (F := F)),
      g.eval (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i) = 0 := by
  have hWK := cellTemplateHQKW_width δF
  have hET : ∀ j, j < 242 → (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i).trace j =
      fullCol hn (colW δF b col mhv kbLv kbRv iv av) j i := fun j hj =>
    env_trace hn nodes hinj _ _ _ _ i (by omega)
  have cL : ∀ j, j ∈ [Cell.wL, Cell.loL, Cell.hiL, Cell.wR, Cell.loR, Cell.hiR] →
      (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i).trace j = col j i := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    have : 2 ≤ j ∧ j < 129 := by
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Cell.wL, Cell.loL, Cell.hiL, Cell.wR, Cell.loR, Cell.hiR]
    rw [hET j (by omega), fullCol_colW_low δF b hn col mhv kbLv kbRv iv av j this.1 this.2]
  have hnewE : ∀ j, 130 ≤ j → j < 134 →
      (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i).trace j =
        newW δF b col mhv kbLv kbRv iv av j i := fun j h1 h2 => by
    rw [hET j (by omega), fullCol_colW_mid δF b hn col mhv kbLv kbRv iv av j (by omega) h2]
  have kL : (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i).trace kbL = kbLv i := by
    rw [hnewE kbL (by simp [kbL]) (by simp [kbL])]; simp [newW, kbL]
  have kR : (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i).trace kbR = kbRv i := by
    rw [hnewE kbR (by simp [kbR]) (by simp [kbR])]; simp [newW, kbL, kbR]
  have iL : (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i).trace invL =
      ((EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i).trace Cell.loL +
        (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i).trace Cell.hiL)⁻¹ := by
    rw [hnewE invL (by simp [invL]) (by simp [invL]), cL Cell.loL (by simp), cL Cell.hiL (by simp)]
    simp [newW, kbL, kbR, invL]
  have iR : (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i).trace invR =
      ((EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i).trace Cell.loR +
        (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i).trace Cell.hiR)⁻¹ := by
    rw [hnewE invR (by simp [invR]) (by simp [invR]), cL Cell.loR (by simp), cL Cell.hiR (by simp)]
    simp [newW, kbL, kbR, invL, invR]
  have sL := sideGates_honest2 kbL invL Cell.wL Cell.loL Cell.hiL _ iL (by
    rw [kL, cL Cell.wL (by simp), cL Cell.loL (by simp), cL Cell.hiL (by simp)]; exact hL i)
  have sR := sideGates_honest2 kbR invR Cell.wR Cell.loR Cell.hiR _ iR (by
    rw [kR, cL Cell.wR (by simp), cL Cell.loR (by simp), cL Cell.hiR (by simp)]; exact hR i)
  intro g hg
  simp only [kindGates, List.mem_append] at hg
  rcases hg with h1 | h1
  · exact sL g h1
  · exact sR g h1

theorem fullCol_colW_ge2 (iv av : Fin n → Quad (algebraMap F K δF)) (j : ℕ) (hj : 2 ≤ j) :
    fullCol hn (colW δF b col mhv kbLv kbRv iv av) j = colW δF b col mhv kbLv kbRv iv av j := by
  funext i'; simp only [fullCol]; split_ifs <;> first | omega | rfl

theorem fullCol_colW_limb (iv av : Fin n → Quad (algebraMap F K δF)) (i' : Fin n) (c : ℕ) (k : Fin 3)
    (h1 : 230 ≤ c) (h2 : c + 3 ≤ 242) (h3 : c % 3 = 2) :
    fullCol hn (colW δF b col mhv kbLv kbRv iv av) (c + k) i' =
      coord b (if c = 230 then Quad.re _ (iv i') else if c = 233 then Quad.im _ (iv i')
        else if c = 236 then Quad.re _ (av i') else Quad.im _ (av i')) k := by
  have hk := k.isLt
  have hW : (cellTemplate δF).width 3 = 225 := CellTraceH.cellTemplate_width δF
  rw [fullCol_colW_ge2 δF b hn col mhv kbLv kbRv iv av _ (by omega)]
  have hc : c = 230 ∨ c = 233 ∨ c = 236 ∨ c = 239 := by omega
  have hcw : colW δF b col mhv kbLv kbRv iv av (c + k) i' =
      newW δF b col mhv kbLv kbRv iv av (c + k) i' := by
    simp only [colW, extColF, hW]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [hcw]
  simp only [newW, kbL, kbR, invL, invR]
  rcases hc with rfl | rfl | rfl | rfl <;>
  · simp only [↓reduceIte, Nat.reduceEqDiff]
    simp (disch := omega) only [if_neg, if_pos]
    exact CellTraceHQ.coordN_shift b _ _ _ k rfl

theorem exportW_gates (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hpole : ∀ i, dRowW δF b hn nodes orbit chals pubs col mhv kbLv kbRv i ≠ 0)
    (hpub : Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (CellTraceH.mN mhv j) * (dNW δF b hn nodes orbit chals pubs col mhv kbLv kbRv j)⁻¹)
    (i : Fin n) :
    ∀ g ∈ gates δF,
      g.eval (gatherEnv b ((cellTemplateHQKW δF).col0 3)
        (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv (ivW δF b hn nodes orbit chals pubs col mhv kbLv kbRv)
          (avW δF b hn nodes orbit chals pubs col mhv kbLv kbRv) i))
        (EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv (ivW δF b hn nodes orbit chals pubs col mhv kbLv kbRv)
          (avW δF b hn nodes orbit chals pubs col mhv kbLv kbRv) i) = 0 := by
  have hWK := cellTemplateHQKW_width δF
  set iv := ivW δF b hn nodes orbit chals pubs col mhv kbLv kbRv with hiv
  set av := avW δF b hn nodes orbit chals pubs col mhv kbLv kbRv with hav
  set e1 := EW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i with he1
  have hET : ∀ j, j < 242 → e1.trace j = fullCol hn (colW δF b col mhv kbLv kbRv iv av) j i := fun j hj =>
    env_trace hn nodes hinj _ _ _ _ i (by omega)
  have hENx : ∀ (hi : (i : ℕ) + 1 < n) j, j < 242 →
      e1.traceNext j = fullCol hn (colW δF b col mhv kbLv kbRv iv av) j ⟨(i : ℕ) + 1, hi⟩ := fun hi j hj =>
    env_traceNext hn nodes hinj _ _ _ _ hadj i hi (by omega)
  have hcol0 : ∀ r k : ℕ, (cellTemplateHQKW δF).col0 3 .traceCur r + k = 134 + 3 * r + k := by
    intro r k; simp only [ChipTemplate.col0, cellTemplateHQKW_baseCols]
  have hcolN : ∀ r k : ℕ, (cellTemplateHQKW δF).col0 3 .traceNext r + k = 134 + 3 * r + k := hcol0
  have hmh : ∀ i' : Fin n, fullCol hn (colW δF b col mhv kbLv kbRv iv av) 129 i' = mhv i' := by
    intro i'
    rw [fullCol_colW_mid δF b hn col mhv kbLv kbRv iv av 129 le_rfl (by omega)]
    simp [newW]
  have hd : ∀ i' : Fin n, dNW δF b hn nodes orbit chals pubs col mhv kbLv kbRv i' =
      dRowW δF b hn nodes orbit chals pubs col mhv kbLv kbRv i' := fun i' => by simp [dNW]
  set eK := gatherEnv b ((cellTemplateHQKW δF).col0 3) e1 with heK
  have hrole : ∀ (r c : ℕ) (v : K), 134 + 3 * r = c → 230 ≤ c → c + 3 ≤ 242 → c % 3 = 2 →
      (∀ k : Fin 3, fullCol hn (colW δF b col mhv kbLv kbRv iv av) (c + k) i = coord b v k) →
      eK.trace r = v := by
    intro r c v hrc h1 h2 _ hv
    refine gather_trace b _ e1 r v fun k => ?_
    rw [hcol0, hrc, hET _ (by have := k.isLt; omega)]; exact hv k
  have hroleN : ∀ (hi : (i : ℕ) + 1 < n) (r c : ℕ) (v : K), 134 + 3 * r = c → 230 ≤ c → c + 3 ≤ 242 →
      c % 3 = 2 → (∀ k : Fin 3, fullCol hn (colW δF b col mhv kbLv kbRv iv av) (c + k)
        ⟨(i : ℕ) + 1, hi⟩ = coord b v k) → eK.traceNext r = v := by
    intro hi r c v hrc h1 h2 _ hv
    refine gather_traceNext b _ e1 r v fun k => ?_
    rw [hcolN, hrc, hENx hi _ (by have := k.isLt; omega)]; exact hv k
  have hinvQ : ∀ (i' : Fin n), iv i' = (dNW δF b hn nodes orbit chals pubs col mhv kbLv kbRv i')⁻¹ :=
    fun i' => by simp [iv, ivW, hd]
  have L := fullCol_colW_limb δF b hn col mhv kbLv kbRv iv av
  refine cellHQW_gates_honest δF eK e1 n i i.isLt
    (CellTraceH.mN mhv) (dNW δF b hn nodes orbit chals pubs col mhv kbLv kbRv) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hd]; exact hpole i
  · show e1.trace 0 = _
    rw [hET 0 (by omega)]; simp [fullCol]
  · show e1.trace 1 = _
    rw [hET 1 (by omega)]
    simp only [fullCol, one_ne_zero, if_false, if_true]
    by_cases hl : (i : ℕ) + 1 = n
    · rw [if_pos hl, if_pos]; exact Fin.ext (by simp; omega)
    · rw [if_neg hl, if_neg]; intro hh; apply hl; have := congrArg Fin.val hh; simp at this; omega
  · show e1.trace 129 = _
    rw [hET 129 (by omega), hmh]; simp [CellTraceH.mN]
  · intro hi; show e1.traceNext 129 = _
    rw [hENx hi 129 (by omega), hmh]; simp [CellTraceH.mN, hi]
  · rw [hd]; exact (den_indepW δF b hn nodes orbit chals pubs col mhv kbLv kbRv iv av i).trans (by simp [dNW])
  · show Quad.mk _ (eK.trace 32) (eK.trace 33) = _
    rw [hrole 32 230 (Quad.re _ (iv i)) (by decide) le_rfl (by omega) (by decide) (fun k => by
        rw [L i 230 k le_rfl (by omega) (by decide)]; try simp),
      hrole 33 233 (Quad.im _ (iv i)) (by decide) (by omega) (by omega) (by decide) (fun k => by
        rw [L i 233 k (by omega) (by omega) (by decide)]; try simp),
      Quad.mk_re_im, hinvQ]
  · intro hi
    show Quad.mk _ (eK.traceNext 32) (eK.traceNext 33) = _
    rw [hroleN hi 32 230 (Quad.re _ (iv ⟨(i : ℕ) + 1, hi⟩)) (by decide) le_rfl (by omega) (by decide) (fun k => by
        rw [L _ 230 k le_rfl (by omega) (by decide)]; try simp),
      hroleN hi 33 233 (Quad.im _ (iv ⟨(i : ℕ) + 1, hi⟩)) (by decide) (by omega) (by omega) (by decide) (fun k => by
        rw [L _ 233 k (by omega) (by omega) (by decide)]; try simp),
      Quad.mk_re_im, hinvQ]
  · show Quad.mk _ (eK.trace 34) (eK.trace 35) = _
    rw [hrole 34 236 (Quad.re _ (av i)) (by decide) (by omega) (by omega) (by decide) (fun k => by
        rw [L i 236 k (by omega) (by omega) (by decide)]; try simp),
      hrole 35 239 (Quad.im _ (av i)) (by decide) (by omega) (by omega) (by decide) (fun k => by
        rw [L i 239 k (by omega) (by omega) (by decide)]; try simp),
      Quad.mk_re_im]
    rfl
  · intro hi
    show Quad.mk _ (eK.traceNext 34) (eK.traceNext 35) = _
    rw [hroleN hi 34 236 (Quad.re _ (av ⟨(i : ℕ) + 1, hi⟩)) (by decide) (by omega) (by omega) (by decide) (fun k => by
        rw [L _ 236 k (by omega) (by omega) (by decide)]; try simp),
      hroleN hi 35 239 (Quad.im _ (av ⟨(i : ℕ) + 1, hi⟩)) (by decide) (by omega) (by omega) (by decide) (fun k => by
        rw [L _ 239 k (by omega) (by omega) (by decide)]; try simp),
      Quad.mk_re_im]
    rfl
  · rw [← hpub]
    congr 1
    · simp only [heK, gatherEnv, ChipTemplate.col0, cellTemplateHQKW_baseCols]
      exact sum_slotVal b 134 CellHQ.pubHQ pubs
    · simp only [heK, gatherEnv, ChipTemplate.col0, cellTemplateHQKW_baseCols]
      exact sum_slotVal b 134 (CellHQ.pubHQ + 1) pubs

/-- **`cellChipHQKW` accepts the honest trace**: from the original honest cell acceptance, the side
conditions per child (`SideOK`), non-vanishing `keyHK` denominators, and the `𝕂′` public equal to the
total. -/
theorem cellChipHQKW_accepts_honest (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hsat0 : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hL : ∀ i, SideOK (kbLv i) (col Cell.wL i) (col Cell.loL i) (col Cell.hiL i))
    (hR : ∀ i, SideOK (kbRv i) (col Cell.wR i) (col Cell.loR i) (col Cell.hiR i))
    (hpole : ∀ i, dRowW δF b hn nodes orbit chals pubs col mhv kbLv kbRv i ≠ 0)
    (hpub : Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) = ∑ j ∈ Finset.range n,
      liftQ δF (CellTraceH.mN mhv j) * (dNW δF b hn nodes orbit chals pubs col mhv kbLv kbRv j)⁻¹) :
    (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies
      (cellTraceHQKW δF b hn nodes orbit chals pubs col mhv kbLv kbRv) := by
  have hR' : (cellTemplate δF).extCols = 32 := cellTemplate_extCols δF
  refine expandChip_extend_honest b orbit (rowNodeSet nodes) chals pubs (cellTemplate δF)
    (cellTemplateHQKW δF) 129 134 (cellTemplate_baseCols δF) (cellTemplateHQKW_baseCols δF) (by omega)
    (by omega) (by rw [hR', cellTemplateHQKW_extCols]; omega)
    (fun g hg => ⟨List.mem_append_left _ hg, cellBase_below g hg⟩)
    (fun g hg => ⟨List.mem_append_left _ hg, by rw [hR']; exact cellMixed_below δF g hg⟩)
    rfl rfl hn nodes col (newW δF b col mhv kbLv kbRv (ivW δF b hn nodes orbit chals pubs col mhv kbLv kbRv)
      (avW δF b hn nodes orbit chals pubs col mhv kbLv kbRv)) hsat0 ?_ ?_
  · intro x hx g hg hg0
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    have hgk : g ∈ kindGates (F := F) := by
      have hg' : g ∈ Cell.baseGates ++ kindGates (F := F) := hg
      rcases List.mem_append.mp hg' with h1 | h1
      · exact absurd h1 hg0
      · exact h1
    exact kindW_gates δF b hn nodes orbit chals pubs col mhv kbLv kbRv hinj hL hR _ _ i g hgk
  · intro x hx g hg hg0
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    have hgm : g ∈ gates δF := by
      have hg' : g ∈ Cell.mixedGates δF ++ gates δF := hg
      rcases List.mem_append.mp hg' with h1 | h1
      · exact absurd h1 hg0
      · exact h1
    exact exportW_gates δF b hn nodes orbit chals pubs col mhv kbLv kbRv hinj hadj hpole hpub i g hgm

end Main

end

end Nock.NockVMROM.Thm54.VclL.Handle.HonestKW
