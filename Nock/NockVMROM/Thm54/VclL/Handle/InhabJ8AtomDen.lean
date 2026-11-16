/-
  Nock/NockVMROM/Thm54/VclL/Handle/InhabJ8AtomDen.lean

  **CLOSED FORMS of the seven denominators of the one-row pad atom
  table** (`InhabJ8AtomChip`).  New module, additive.

  With `γ, ρ` the validity coins (`ChalsOK … γ ρ 11`), `z` the fingerprint seed (`chals 2 / 3`),
  `γH = (chals 33, chals 35)`, `ρH = (chals 34, chals 36)` the handle coins and `zA = (chals 37, chals 38)`:

  * cell validity provide `vKey = (z², z, z, 1, 0)`:            `ρ + z² + γ z + γ² z + γ³`        (`padV_eq`)
  * cell export side `s` `xKey = (z², z, z, z, 0, 0, z, 0, 1, 0, s)`:
                                                   `ρ + z² + γ z + γ² z + γ³ z + γ⁶ z + γ⁸ + s γ¹⁰`  (`padX_eq`)
  * cell handle provide `keyH = (0, 0, 0, 0, 1)`:              `ρH + γH⁴`                        (`padRow_eq`)
  * atom g5 `mbKey = (zA, 0, z, 0, 0)`:                        `ρ + zA + γ² z`                    (`padMB_eq`)
  * atom old-export consume `oldKey = (0, 0, 0, 0, 0)`:        `ρH`                               (`padC_eq`)
  * atom inc `incKey = (2, 0, 2, 0, 4)`:                       `ρH + 2 + 2 γH² + 4 γH⁴`           (`padMI_eq`)
-/
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomChip
import Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomDen

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomCell
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomChip
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomGenJ8
open Module
open scoped Polynomial

noncomputable section

section Env
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h : ℕ} (hn : 0 < 1)
  (nodes : Fin 1 → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (γ ρ z : Quad (algebraMap F K δF)) (i : Fin 1)

/-- The atom pad row environment (zero role fill). -/
abbrev EZp : Env F :=
  HonestA8.EZ δF b hn nodes orbit chals pubs (padC δF b hn nodes orbit chals pubs γ ρ z)
    (newPad (F := F)) i

theorem ezp_trace (j : ℕ) (h2 : 2 ≤ j) (h3 : j < 205) :
    (EZp δF b hn nodes orbit chals pubs γ ρ z i).trace j =
      (if j < 130 then padC δF b hn nodes orbit chals pubs γ ρ z j i else padNew j) := by
  have hWA : (atomTemplateHQ δF).width 3 = 349 := HonestA8.atomTemplateHQ_width δF
  unfold EZp HonestA8.EZ
  rw [env_trace hn nodes (inj1 nodes) _ _ _ _ i (by rw [hWA]; omega : j < (atomTemplateHQ δF).width 3)]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  simp only [fullCol, h0, h1, if_false, HonestA8.colZ, extColF, HonestA8.newZ]
  by_cases hj : j < 130
  · simp [hj]
  · simp only [hj, if_false, h3, if_true, show j < 313 by omega]
    rfl

theorem ezp_zero (j : ℕ) (h2 : 2 ≤ j) (h3 : j < 205) (hj : 130 ≤ j ∨ j = 2)
    (hb : j ≠ bitR) (hi : j ≠ invT) :
    (EZp δF b hn nodes orbit chals pubs γ ρ z i).trace j = 0 := by
  rw [ezp_trace δF b hn nodes orbit chals pubs γ ρ z i j h2 h3]
  rcases hj with hj | rfl
  · rw [if_neg (by omega)]; simp [padNew, hb, hi]
  · simp [padC, CellTraceHQ.colHQ, extColF, padCol, cellCol, CellVals.base, padVals, cellFill, cellFillInv,
      padRow]

theorem gz_chal (r : ℕ) :
    (gatherEnv b ((atomTemplateHQ δF).col0 3) (EZp δF b hn nodes orbit chals pubs γ ρ z i)).chal r = chals r := by
  simp only [gatherEnv, ChipTemplate.col0, atomTemplateHQ_baseCols]
  exact sum_slotVal b 205 r chals

set_option maxRecDepth 20000 in
theorem gz_role (t : ℕ) (ht : t < 32) :
    (gatherEnv b ((atomTemplateHQ δF).col0 3) (EZp δF b hn nodes orbit chals pubs γ ρ z i)).trace t =
      roleVal δF (padVals δF γ ρ z i) t := by
  refine gather_trace b _ _ t _ fun k => ?_
  have hk := k.isLt
  have hcol0 : (atomTemplateHQ δF).col0 3 .traceCur t + k = 205 + 3 * t + k := by
    simp only [ChipTemplate.col0, atomTemplateHQ_baseCols]
  have hWA : (atomTemplateHQ δF).width 3 = 349 := HonestA8.atomTemplateHQ_width δF
  have hW' : (cellTemplateHQ δF).width 3 = 238 := CellTraceHQ.cellTemplateHQ_width δF
  have hW : (cellTemplate δF).width 3 = 225 := CellTraceH.cellTemplate_width δF
  rw [hcol0]
  unfold EZp HonestA8.EZ
  rw [env_trace hn nodes (inj1 nodes) _ _ _ _ i (by rw [hWA]; omega)]
  simp only [fullCol, HonestA8.colZ, extColF, padC, CellTraceHQ.colHQ, padCol, cellCol, hW, hW']
  split_ifs <;> try omega
  rw [show (205 + 3 * t + (k : ℕ) - (205 - 130) - (130 - 129) - 129) / 3 = t by omega]
  congr 1
  exact Fin.ext (by simp; omega)

/-- The pad row's provided-validity `p.leaf` read in the atom row's `𝕂′` roles `4 / 5`. -/
theorem gz_leaf :
    Quad.mk _ ((gatherEnv b ((atomTemplateHQ δF).col0 3) (EZp δF b hn nodes orbit chals pubs γ ρ z i)).trace 4)
      ((gatherEnv b ((atomTemplateHQ δF).col0 3) (EZp δF b hn nodes orbit chals pubs γ ρ z i)).trace 5) = z := by
  rw [gz_role δF b hn nodes orbit chals pubs γ ρ z i 4 (by omega),
    gz_role δF b hn nodes orbit chals pubs γ ρ z i 5 (by omega)]
  simp only [roleVal, show (4 : ℕ) % 2 = 0 from rfl, show (5 : ℕ) % 2 = 1 from rfl, if_true,
    show ((1 : ℕ) = 0) = False from by simp, if_false, show (4 : ℕ) / 2 = 2 from rfl,
    show (5 : ℕ) / 2 = 2 from rfl, Quad.mk_re_im]
  simp [CellVals.qslot, padVals, cellFill, cellFillInv, padRow, ComputeTable.FP.cons, liftQ]

end Env

section MB
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h : ℕ} (hn : 0 < 1)
  (nodes : Fin 1 → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (γ ρ z : Quad (algebraMap F K δF)) (i : Fin 1)

/-- **`padMB_eq`**: the atom g5 denominator of the pad row, `ρ + zA + γ² z`. -/
theorem padMB_eq (hok : ChalsOK δF chals γ ρ 11) :
    HonestA8.dMB δF b hn nodes orbit chals pubs (padC δF b hn nodes orbit chals pubs γ ρ z)
      (newPad (F := F)) i = ρ + Quad.mk _ (chals 37) (chals 38) + γ ^ 2 * z := by
  have hc := gz_chal δF b hn nodes orbit chals pubs γ ρ z i
  have hl := gz_leaf δF b hn nodes orbit chals pubs γ ρ z i
  have h2 := ezp_zero δF b hn nodes orbit chals pubs γ ρ z i 2 le_rfl (by omega) (Or.inr rfl)
    (by decide) (by decide)
  simp only [EZp] at hc hl h2
  have g0 := hok.2 0 (by omega)
  have g1 := hok.2 1 (by omega)
  have g2 := hok.2 2 (by omega)
  have g3 := hok.2 3 (by omega)
  have g4 := hok.2 4 (by omega)
  norm_num at g0 g1 g2 g3 g4
  unfold HonestA8.dMB
  rw [ev_den, ev_rlc]
  simp only [mbKey, zAt, rQ, List.zipIdx, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, ev_chal, ev_gpow, ev_var, ev_zero, ev_base, hc, Cell.pR, Cell.idx]
  simp only [cv, CoeffExpr.eval] at *
  norm_num
  rw [hok.1, g0, g2, hl, h2]
  simp [liftQ]
  ring

/-- **`padC_eq`**: the atom old-export consume denominator of the pad row, `ρH`. -/
theorem padC_eq :
    HonestA8.dC δF b hn nodes orbit chals pubs (padC δF b hn nodes orbit chals pubs γ ρ z)
      (newPad (F := F)) i = Quad.mk _ (chals 34) (chals 36) := by
  have hc := gz_chal δF b hn nodes orbit chals pubs γ ρ z i
  have z200 := ezp_zero δF b hn nodes orbit chals pubs γ ρ z i 200 (by omega) (by omega) (Or.inl (by omega))
    (by decide) (by decide)
  have z201 := ezp_zero δF b hn nodes orbit chals pubs γ ρ z i 201 (by omega) (by omega) (Or.inl (by omega))
    (by decide) (by decide)
  have z202 := ezp_zero δF b hn nodes orbit chals pubs γ ρ z i 202 (by omega) (by omega) (Or.inl (by omega))
    (by decide) (by decide)
  have z203 := ezp_zero δF b hn nodes orbit chals pubs γ ρ z i 203 (by omega) (by omega) (Or.inl (by omega))
    (by decide) (by decide)
  simp only [EZp] at hc z200 z201 z202 z203
  unfold HonestA8.dC
  simp only [HQ.denKeyQ, ev_add, HQ.rhoQ, ev_chal, TeleHQ.rlcQ_ev, hc, oldKey, List.length_cons,
    List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
  simp only [cv, CoeffExpr.eval, idxO, lO, kRO, vRO] at *
  rw [z200, z201, z202, z203]
  simp [liftQ]

/-- **`padMI_eq`**: the atom inc denominator of the pad row, `ρH + 2 + 2 γH² + 4 γH⁴`. -/
theorem padMI_eq :
    HonestA8.dMI δF b hn nodes orbit chals pubs (padC δF b hn nodes orbit chals pubs γ ρ z)
      (newPad (F := F)) i = Quad.mk _ (chals 34) (chals 36) + 2 +
        2 * Quad.mk _ (chals 33) (chals 35) ^ 2 + 4 * Quad.mk _ (chals 33) (chals 35) ^ 4 := by
  have hc := gz_chal δF b hn nodes orbit chals pubs γ ρ z i
  have z2 := ezp_zero δF b hn nodes orbit chals pubs γ ρ z i 2 le_rfl (by omega) (Or.inr rfl)
    (by decide) (by decide)
  have z198 := ezp_zero δF b hn nodes orbit chals pubs γ ρ z i 198 (by omega) (by omega) (Or.inl (by omega))
    (by decide) (by decide)
  have z200 := ezp_zero δF b hn nodes orbit chals pubs γ ρ z i 200 (by omega) (by omega) (Or.inl (by omega))
    (by decide) (by decide)
  simp only [EZp] at hc z2 z198 z200
  unfold HonestA8.dMI
  simp only [HQ.denKeyQ, ev_add, HQ.rhoQ, ev_chal, TeleHQ.rlcQ_ev, hc, incKey, List.length_cons,
    List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
  simp only [cv, notE, CoeffExpr.eval, idxO, conv, Cell.idx, tagInc] at *
  rw [z2, z198, z200]
  simp [liftQ]
  simp only [map_ofNat]
  ring

theorem ec_base (j : ℕ) (h2 : 2 ≤ j) (h3 : j < 129) :
    (CellTraceHQ.E δF b hn nodes orbit chals pubs (padCol δF b γ ρ z) (fun _ => 0) (fun _ => 0) (fun _ => 0)
      i).trace j = (padVals δF γ ρ z i).base j := by
  have hW' : (cellTemplateHQ δF).width 3 = 238 := CellTraceHQ.cellTemplateHQ_width δF
  unfold CellTraceHQ.E
  rw [env_trace hn nodes (inj1 nodes) _ _ _ _ i (by rw [hW']; omega : j < (cellTemplateHQ δF).width 3)]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  simp [fullCol, h0, h1, CellTraceHQ.colHQ, extColF, h3, padCol, cellCol]

/-- **`padRow_eq`**: the cell handle-provide denominator of the pad row, `ρH + γH⁴` (key `(0, 0, 0, 0, 1)`). -/
theorem padRow_eq :
    CellTraceHQ.dRow δF b hn nodes orbit chals pubs (padCol δF b γ ρ z) (fun _ => 0) i =
      Quad.mk _ (chals 34) (chals 36) + Quad.mk _ (chals 33) (chals 35) ^ 4 := by
  have hc := CellTraceHQ.gather_chal δF b chals
    (CellTraceHQ.E δF b hn nodes orbit chals pubs (padCol δF b γ ρ z) (fun _ => 0) (fun _ => 0) (fun _ => 0) i) rfl
  have t2 := ec_base δF b hn nodes orbit chals pubs γ ρ z i 2 le_rfl (by omega)
  have t3 := ec_base δF b hn nodes orbit chals pubs γ ρ z i 3 (by omega) (by omega)
  have t4 := ec_base δF b hn nodes orbit chals pubs γ ρ z i 4 (by omega) (by omega)
  have t5 := ec_base δF b hn nodes orbit chals pubs γ ρ z i 5 (by omega) (by omega)
  have t6 := ec_base δF b hn nodes orbit chals pubs γ ρ z i 6 (by omega) (by omega)
  have t7 := ec_base δF b hn nodes orbit chals pubs γ ρ z i 7 (by omega) (by omega)
  have t8 := ec_base δF b hn nodes orbit chals pubs γ ρ z i 8 (by omega) (by omega)
  simp only [CellVals.base, padVals, cellFill, cellFillInv, padRow] at t2 t3 t4 t5 t6 t7 t8
  norm_num at t2 t3 t4 t5 t6 t7 t8
  unfold CellTraceHQ.dRow
  simp only [HQ.denKeyQ, ev_add, HQ.rhoQ, ev_chal, TeleHQ.rlcQ_ev, hc, CellH.keyH, List.length_cons,
    List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
  simp only [cv, notE, CellH.valE, CoeffExpr.eval, Cell.idx, Cell.wL, Cell.wR, Cell.idL, Cell.idR, Cell.aL,
    Cell.aR] at *
  rw [t2, t3, t4, t5, t6, t7, t8]
  simp [liftQ]

end MB

section IO
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))] (γ ρ z : Quad (algebraMap F K δF))

/-- **`padV_eq`**: the cell validity-provide denominator of the pad row, `ρ + z² + γ z + γ² z + γ³`. -/
theorem padV_eq (hz : z ≠ 0) :
    FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (padRow δF z)) = ρ + z ^ 2 + γ * z + γ ^ 2 * z + γ ^ 3 := by
  simp [FiniteIO.compress, Walk.rlc, Fin.sum_univ_five, vKeyOf, padRow, ComputeTable.FP.cons, liftQ,
    Quad.mk_one']
  field_simp
  ring

/-- **`padX_eq`**: the cell export-provide denominator of side `s` of the pad row,
`ρ + z² + γ z + γ² z + γ³ z + γ⁶ z + γ⁸ + s γ¹⁰`. -/
theorem padX_eq (hz : z ≠ 0) (s : F) :
    FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (padRow δF z) s) =
      ρ + z ^ 2 + γ * z + γ ^ 2 * z + γ ^ 3 * z + γ ^ 6 * z + γ ^ 8 + liftQ δF s * γ ^ 10 := by
  simp [FiniteIO.compress, Walk.rlc, Fin.sum_univ_succ, xKeyOf, padRow, ComputeTable.FP.cons, liftQ]
  field_simp
  ring

end IO

end

end Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomDen
