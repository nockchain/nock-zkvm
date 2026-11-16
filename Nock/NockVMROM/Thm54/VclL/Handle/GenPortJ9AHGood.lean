/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHGood.lean

For `famCellH` (`ComplJ8Of`), `famAH famMB famC famMI` (`ComplJ8OfAtom`; used by `ComplJ9BOf.famsOf`)
  the family LIST at one orbit `o` equals the list at any other orbit `o'` (both with injective row nodes
  `powN o n`, `powN o' n`).  Hence `χ ∉ ev(o) ↔ χ ∉ ev(o')`.

  Reason: each event reads the row environment only through current-row columns (`keyHK`, `keyH`,
  `oldKey`, `incKey`, `mbKey` are all `cv` / chal leaves; no `traceNext`), and the current row at node `i`
  is `fullCol .. j i` (`env_trace`), independent of the orbit.  No family reads `traceNext`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList quadPole ReadsOff)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)

noncomputable section

section Fams
open Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-! ## 1. Current-row reads of a key list -/

/-- A key list whose entries read only current-row columns `< B` gives the same `keyVec5` at two
environments agreeing on the current row below `B` (no `traceNext`, no coin). -/
theorem keyVec5_cur (B : ℕ) (l : List (CoeffExpr (ZMod p)))
    (hl : ∀ c : Fin 5, IOVS.rdOK B (l.getD c (.const 0)) = true) (e e' : Env (ZMod p))
    (ht : ∀ j < B, e.trace j = e'.trace j) :
    ServeH.keyVec5 (K := K) l e = ServeH.keyVec5 l e' := by
  funext c
  simp only [ServeH.keyVec5]
  congr 1
  exact IOVS.eval_congr B _ (hl c) e e' ht

theorem keyHK_cur : ∀ c : Fin 5, IOVS.rdOK 134 ((TwoProviderQ.keyHK (F := ZMod p)).getD c (.const 0)) = true := by
  intro c; fin_cases c <;> rfl

theorem keyH_cur : ∀ c : Fin 5, IOVS.rdOK 130 ((CellH.keyH (F := ZMod p)).getD c (.const 0)) = true := by
  intro c; fin_cases c <;> rfl

theorem oldKey_cur : ∀ c : Fin 5, IOVS.rdOK 205 ((AtomChipHQ.oldKey (F := ZMod p)).getD c (.const 0)) = true := by
  intro c; fin_cases c <;> rfl

theorem incKey_cur : ∀ c : Fin 5, IOVS.rdOK 205 ((AtomChipHQ.incKey (F := ZMod p)).getD c (.const 0)) = true := by
  intro c; fin_cases c <;> rfl

/-! ## 2. Current-row columns at two orbits -/

/-- The cell part's columns `< 184` do not depend on the orbit nor the publics. -/
theorem colAH_orb (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (χ : Coins frameJ8 K) (pubs pubs' : ℕ → K) (k : ℕ) (hk : k < 184) :
    colAH δ b D hA o χ pubs k = colAH δ b D hA o' χ pubs' k :=
  InhabJ8Stage.colHQ_cong δ b _ _ _ _ _ _ _ k hk (fun _ => rfl) (fun _ => rfl)

/-- The atom row environment's current row, columns `< 223`, at two orbits (and two publics). -/
theorem ezA_trace_orb (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.acs.length)) (hinj' : Function.Injective (powN o' D.acs.length))
    (χ : Coins frameJ8 K) (pubs pubs' : ℕ → K) (i : Fin D.acs.length) : ∀ j < 223,
      (ezA δ b D hA o χ pubs i).trace j = (ezA δ b D hA o' χ pubs' i).trace j := by
  intro j hj
  have hw : j < (AtomChipHQ.atomTemplateHQ δ).width 3 := by rw [HonestA8.atomTemplateHQ_width]; omega
  have hW : (cellTemplateHQ δ).width 3 = 238 := CellTraceHQ.cellTemplateHQ_width δ
  have hcol : HonestA8.colZ δ (colAH δ b D hA o χ pubs) (newBA D) j =
      HonestA8.colZ δ (colAH δ b D hA o' χ pubs') (newBA D) j := by
    funext i'
    simp only [HonestA8.colZ, extColF, hW]
    split_ifs with h1 h2 h3
    · rw [colAH_orb δ b D hA o o' χ pubs pubs' j (by omega)]
    · rfl
    · rw [colAH_orb δ b D hA o o' χ pubs pubs' (j - (205 - 130)) (by omega)]
    · rfl
  have e1 : (ezA δ b D hA o χ pubs i).trace j =
      fullCol hA (HonestA8.colZ δ (colAH δ b D hA o χ pubs) (newBA D)) j i :=
    env_trace hA (powN o _) hinj _ o.ω _ _ i hw
  have e2 : (ezA δ b D hA o' χ pubs' i).trace j =
      fullCol hA (HonestA8.colZ δ (colAH δ b D hA o' χ pubs') (newBA D)) j i :=
    env_trace hA (powN o' _) hinj' _ o'.ω _ _ i hw
  rw [e1, e2]
  simp only [fullCol, hcol]

/-- The gathered `𝕂` environment's current-row reads `< 6`, at two orbits. -/
theorem ekA_trace_orb (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.acs.length)) (hinj' : Function.Injective (powN o' D.acs.length))
    (χ : Coins frameJ8 K) (pubs pubs' : ℕ → K) (i : Fin D.acs.length) : ∀ r < 6,
      (ekA δ b D hA o χ pubs i).trace r = (ekA δ b D hA o' χ pubs' i).trace r := by
  intro r hr
  have e := fun k : Fin 3 => ezA_trace_orb δ b D hA o o' hinj hinj' χ pubs pubs' i (205 + 3 * r + k) (by omega)
  simp only [ekA, gatherEnv, ChipTemplate.col0, AtomChipHQ.atomTemplateHQ_baseCols]
  exact Finset.sum_congr rfl fun k _ => by rw [e k]

/-- The coin-free atom cell row environment, current row `< 130`, at two orbits. -/
theorem aE0_trace_orb (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.acs.length)) (hinj' : Function.Injective (powN o' D.acs.length))
    (χ : Coins frameJ8 K) (i : Fin D.acs.length) : ∀ j < 130,
      (aE0 δ b D hA o χ i).trace j = (aE0 δ b D hA o' χ i).trace j := by
  intro j hj
  have hw : j < (cellTemplateHQ δ).width 3 := by rw [CellTraceHQ.cellTemplateHQ_width]; omega
  have e1 : (aE0 δ b D hA o χ i).trace j =
      fullCol hA (CellTraceHQ.colHQ δ b (aCol δ b D χ) (mhvA D) (fun _ => 0) (fun _ => 0)) j i :=
    env_trace hA (powN o _) hinj _ o.ω _ _ i hw
  have e2 : (aE0 δ b D hA o' χ i).trace j =
      fullCol hA (CellTraceHQ.colHQ δ b (aCol δ b D χ) (mhvA D) (fun _ => 0) (fun _ => 0)) j i :=
    env_trace hA (powN o' _) hinj' _ o'.ω _ _ i hw
  rw [e1, e2]

/-- The coin-free cell row environment, current row `< 134`, at two orbits. -/
theorem cEW_trace_orb (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.cells.length)) (hinj' : Function.Injective (powN o' D.cells.length))
    (χ : Coins frameJ8 K) (i : Fin D.cells.length) : ∀ j < 134,
      (cEW δ b D hC o χ i).trace j = (cEW δ b D hC o' χ i).trace j := by
  intro j hj
  have hw : j < (HonestKW.cellTemplateHQKW δ).width 3 := by rw [HonestKW.cellTemplateHQKW_width]; omega
  have e1 : (cEW δ b D hC o χ i).trace j =
      fullCol hC (HonestKW.colW δ b (cCol δ b D χ) (fun i : Fin D.cells.length => (mhF D i : ZMod p))
        (ComplJ8Cell.kbLB (bigOf D) D.cells) (ComplJ8Cell.kbRB (bigOf D) D.cells)
        (fun _ => 0) (fun _ => 0)) j i :=
    env_trace hC (powN o _) hinj _ o.ω _ _ i hw
  have e2 : (cEW δ b D hC o' χ i).trace j =
      fullCol hC (HonestKW.colW δ b (cCol δ b D χ) (fun i : Fin D.cells.length => (mhF D i : ZMod p))
        (ComplJ8Cell.kbLB (bigOf D) D.cells) (ComplJ8Cell.kbRB (bigOf D) D.cells)
        (fun _ => 0) (fun _ => 0)) j i :=
    env_trace hC (powN o' _) hinj' _ o'.ω _ _ i hw
  rw [e1, e2]

/-! ## 3. The five families -/

theorem cellHx_orb (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.cells.length)) (hinj' : Function.Injective (powN o' D.cells.length))
    (j : ℕ) (χ : Coins frameJ8 K) : cellHx δ b D hC o j χ = cellHx δ b D hC o' j χ := by
  unfold cellHx
  by_cases hj : j < D.cells.length
  · rw [dif_pos hj, dif_pos hj, keyVec5_cur 134 _ keyHK_cur (cEW δ b D hC o χ ⟨j, hj⟩)
      (cEW δ b D hC o' χ ⟨j, hj⟩) (cEW_trace_orb δ b D hC o o' hinj hinj' χ ⟨j, hj⟩)]
  · rw [dif_neg hj, dif_neg hj]

theorem aHx_orb (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.acs.length)) (hinj' : Function.Injective (powN o' D.acs.length))
    (j : ℕ) (χ : Coins frameJ8 K) : aHx δ b D hA o j χ = aHx δ b D hA o' j χ := by
  unfold aHx
  by_cases hj : j < D.acs.length
  · rw [dif_pos hj, dif_pos hj, keyVec5_cur 130 _ keyH_cur (aE0 δ b D hA o χ ⟨j, hj⟩)
      (aE0 δ b D hA o' χ ⟨j, hj⟩) (aE0_trace_orb δ b D hA o o' hinj hinj' χ ⟨j, hj⟩)]
  · rw [dif_neg hj, dif_neg hj]

theorem mbX_orb (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.acs.length)) (hinj' : Function.Injective (powN o' D.acs.length))
    (j : ℕ) (χ : Coins frameJ8 K) : mbX δ b D hA o j χ = mbX δ b D hA o' j χ := by
  unfold mbX
  by_cases hj : j < D.acs.length
  · rw [dif_pos hj, dif_pos hj]
    rw [keyVec_mb_congr δ (ekA δ b D hA o χ (pubsAOf δ b D hA o χ) ⟨j, hj⟩)
      (ekA δ b D hA o' χ (pubsAOf δ b D hA o' χ) ⟨j, hj⟩) (ezA δ b D hA o χ (pubsAOf δ b D hA o χ) ⟨j, hj⟩)
      (ezA δ b D hA o' χ (pubsAOf δ b D hA o' χ) ⟨j, hj⟩)
      (by rw [ekA_chal, ekA_chal]) (by rw [ekA_chal, ekA_chal])
      (ekA_trace_orb δ b D hA o o' hinj hinj' χ _ _ ⟨j, hj⟩ 4 (by norm_num))
      (ekA_trace_orb δ b D hA o o' hinj hinj' χ _ _ ⟨j, hj⟩ 5 (by norm_num))
      (ezA_trace_orb δ b D hA o o' hinj hinj' χ _ _ ⟨j, hj⟩ 2 (by norm_num))]
  · rw [dif_neg hj, dif_neg hj]

theorem cX_orb (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.acs.length)) (hinj' : Function.Injective (powN o' D.acs.length))
    (j : ℕ) (χ : Coins frameJ8 K) : cX δ b D hA o j χ = cX δ b D hA o' j χ := by
  unfold cX
  by_cases hj : j < D.acs.length
  · rw [dif_pos hj, dif_pos hj, keyVec5_cur 205 _ oldKey_cur (ezA δ b D hA o χ (pubsAOf δ b D hA o χ) ⟨j, hj⟩)
      (ezA δ b D hA o' χ (pubsAOf δ b D hA o' χ) ⟨j, hj⟩)
      (fun k hk => ezA_trace_orb δ b D hA o o' hinj hinj' χ _ _ ⟨j, hj⟩ k (by omega))]
  · rw [dif_neg hj, dif_neg hj]

theorem miX_orb (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.acs.length)) (hinj' : Function.Injective (powN o' D.acs.length))
    (j : ℕ) (χ : Coins frameJ8 K) : miX δ b D hA o j χ = miX δ b D hA o' j χ := by
  unfold miX
  by_cases hj : j < D.acs.length
  · rw [dif_pos hj, dif_pos hj, keyVec5_cur 205 _ incKey_cur (ezA δ b D hA o χ (pubsAOf δ b D hA o χ) ⟨j, hj⟩)
      (ezA δ b D hA o' χ (pubsAOf δ b D hA o' χ) ⟨j, hj⟩)
      (fun k hk => ezA_trace_orb δ b D hA o o' hinj hinj' χ _ _ ⟨j, hj⟩ k (by omega))]
  · rw [dif_neg hj, dif_neg hj]

/-- **`famCellH` is orbit-invariant** (as a list of bad events). -/
theorem famCellH_orb (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.cells.length)) (hinj' : Function.Injective (powN o' D.cells.length)) :
    famCellH δ b D hC o (K := K) = famCellH δ b D hC o' := by
  unfold famCellH
  refine List.map_congr_left fun j _ => ?_
  rw [show cellHx δ b D hC o j (K := K) = cellHx δ b D hC o' j from
    funext (cellHx_orb δ b D hC o o' hinj hinj' j)]

theorem famAH_orb (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.acs.length)) (hinj' : Function.Injective (powN o' D.acs.length)) :
    famAH δ b D hA o (K := K) = famAH δ b D hA o' := by
  unfold famAH
  refine List.map_congr_left fun j _ => ?_
  rw [show aHx δ b D hA o j (K := K) = aHx δ b D hA o' j from funext (aHx_orb δ b D hA o o' hinj hinj' j)]

theorem famMB_orb (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.acs.length)) (hinj' : Function.Injective (powN o' D.acs.length)) :
    famMB δ b D hA o (K := K) = famMB δ b D hA o' := by
  unfold famMB
  refine List.map_congr_left fun j _ => ?_
  rw [show mbX δ b D hA o j (K := K) = mbX δ b D hA o' j from funext (mbX_orb δ b D hA o o' hinj hinj' j)]

theorem famC_orb (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.acs.length)) (hinj' : Function.Injective (powN o' D.acs.length)) :
    famC δ b D hA o (K := K) = famC δ b D hA o' := by
  unfold famC
  refine List.map_congr_left fun j _ => ?_
  rw [show cX δ b D hA o j (K := K) = cX δ b D hA o' j from funext (cX_orb δ b D hA o o' hinj hinj' j)]

theorem famMI_orb (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.acs.length)) (hinj' : Function.Injective (powN o' D.acs.length)) :
    famMI δ b D hA o (K := K) = famMI δ b D hA o' := by
  unfold famMI
  refine List.map_congr_left fun j _ => ?_
  rw [show miX δ b D hA o j (K := K) = miX δ b D hA o' j from funext (miX_orb δ b D hA o o' hinj hinj' j)]

/-! ## 4. The event statements `χ ∉ ev(o) ↔ χ ∉ ev(o')` -/

theorem famCellH_ev_orb (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.cells.length)) (hinj' : Function.Injective (powN o' D.cells.length))
    (χ : Coins frameJ8 K) :
    (∀ e ∈ famCellH δ b D hC o (K := K), χ ∉ e.ev) ↔ (∀ e ∈ famCellH δ b D hC o' (K := K), χ ∉ e.ev) := by
  rw [famCellH_orb δ b D hC o o' hinj hinj']

theorem famAH_ev_orb (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.acs.length)) (hinj' : Function.Injective (powN o' D.acs.length))
    (χ : Coins frameJ8 K) :
    (∀ e ∈ famAH δ b D hA o (K := K), χ ∉ e.ev) ↔ (∀ e ∈ famAH δ b D hA o' (K := K), χ ∉ e.ev) := by
  rw [famAH_orb δ b D hA o o' hinj hinj']

theorem famMB_ev_orb (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.acs.length)) (hinj' : Function.Injective (powN o' D.acs.length))
    (χ : Coins frameJ8 K) :
    (∀ e ∈ famMB δ b D hA o (K := K), χ ∉ e.ev) ↔ (∀ e ∈ famMB δ b D hA o' (K := K), χ ∉ e.ev) := by
  rw [famMB_orb δ b D hA o o' hinj hinj']

theorem famC_ev_orb (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.acs.length)) (hinj' : Function.Injective (powN o' D.acs.length))
    (χ : Coins frameJ8 K) :
    (∀ e ∈ famC δ b D hA o (K := K), χ ∉ e.ev) ↔ (∀ e ∈ famC δ b D hA o' (K := K), χ ∉ e.ev) := by
  rw [famC_orb δ b D hA o o' hinj hinj']

theorem famMI_ev_orb (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h h' : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o D.acs.length)) (hinj' : Function.Injective (powN o' D.acs.length))
    (χ : Coins frameJ8 K) :
    (∀ e ∈ famMI δ b D hA o (K := K), χ ∉ e.ev) ↔ (∀ e ∈ famMI δ b D hA o' (K := K), χ ∉ e.ev) := by
  rw [famMI_orb δ b D hA o o' hinj hinj']

end Fams

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood in
#print axioms famCellH_orb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood in
#print axioms famAH_orb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood in
#print axioms famMB_orb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood in
#print axioms famC_orb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood in
#print axioms famMI_orb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood in
#print axioms famCellH_ev_orb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood in
#print axioms famAH_ev_orb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood in
#print axioms famMB_ev_orb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood in
#print axioms famC_ev_orb
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGood in
#print axioms famMI_ev_orb
