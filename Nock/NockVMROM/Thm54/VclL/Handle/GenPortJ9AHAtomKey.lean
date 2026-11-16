/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAtomKey.lean

For any `D hA`, any orbit `o` with `hinj : Injective (powN o D.acs.length)`, any `pubs`, any `χ`:
  * `aRow_closed`: the cell part's handle denominator
    `ρH + compress (γH, 0) (liftRec ![i, wL, wL·idL + (1 − wL)·aL, wR, wR·idR + (1 − wR)·aR])`;
  * `dMB_closed`: `ρV + compress (γV, 0) ![zAt (chal 37/38), 0, (aRows i).p.leaf, 0, i]`;
  * `dC_closed`: `ρH + compress (γH, 0) (liftRec ![newBA 200, 0, newBA 201, newBA 202, newBA 203])`;
  * `dMI_closed`: `ρH + compress (γH, 0) (liftRec ![2(1−conv), (1−conv)·idxO − conv, 2, i, 4])`;
  each also with `pubs := fun _ => 0` (`*_pubs0`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomKey

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

section Key
open Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The atom cell part's current row, base columns `2 .. 128`, is the honest cell value's base column. -/
theorem aE0_base (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length))
    (χ : Coins frameJ8 K) (i : Fin D.acs.length) (j : ℕ) (h2 : 2 ≤ j) (h3 : j < 129) :
    (aE0 δ b D hA o χ i).trace j = (aRows δ D χ i).base j := by
  have hW : (cellTemplateHQ δ).width 3 = 238 := CellTraceHQ.cellTemplateHQ_width δ
  unfold aE0 CellTraceHQ.E
  rw [env_trace hA (powN o _) hinj _ _ _ _ i (by rw [hW]; omega)]
  have e0 : j ≠ 0 := by omega
  have e1 : j ≠ 1 := by omega
  simp only [fullCol, e0, e1, if_false, CellTraceHQ.colHQ, extColF, if_neg (show ¬ (j = 129) by omega)]
  rw [if_pos (by omega), aCol, cellCol, if_pos h3]
  rfl

/-- **`aRow_closed`**: the cell part's handle denominator in closed form (any `pubs`). -/
theorem aRow_closed (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length))
    (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    CellTraceHQ.dRow δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (aCol δ b D χ) (mhvA D) i =
      ComplJ8Bad.ρH δ χ + FiniteIO.compress (⟨ComplJ8Bad.γH δ χ, 0⟩ : FiniteIO.IOCoins 𝕂′)
        (BalanceQ.liftRec (K := K) (L := 𝕂′) (fun c : Fin 5 => algebraMap (ZMod p) K
          (![(aRows δ D χ i).idx, (aRows δ D χ i).wL,
             (aRows δ D χ i).wL * (aRows δ D χ i).idL + (1 - (aRows δ D χ i).wL) * (aRows δ D χ i).aL,
             (aRows δ D χ i).wR,
             (aRows δ D χ i).wR * (aRows δ D χ i).idR + (1 - (aRows δ D χ i).wR) * (aRows δ D χ i).aR] c))) := by
  rw [aRow_split]
  congr 1
  simp only [aHx, dif_pos i.isLt, Fin.eta]
  congr 2
  funext c
  simp only [BalanceQ.liftRec, ServeH.keyVec5]
  congr 2
  have t := fun j (h2 : 2 ≤ j) (h3 : j < 129) => aE0_base δ b D hA o hinj χ i j h2 h3
  fin_cases c <;>
    simp [CellH.keyH, CellH.valE, CoeffExpr.eval, cv, notE, Cell.idx, Cell.idL, Cell.idR, Cell.wL, Cell.wR,
      Cell.aL, Cell.aR, CellVals.base, t 2 (by norm_num) (by norm_num), t 3 (by norm_num) (by norm_num),
      t 4 (by norm_num) (by norm_num), t 5 (by norm_num) (by norm_num), t 6 (by norm_num) (by norm_num),
      t 7 (by norm_num) (by norm_num), t 8 (by norm_num) (by norm_num)]

/-- The honest atom cell row's serial is its position. -/
theorem aRows_idx (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) (i : Fin D.acs.length) :
    (aRows δ D χ i).idx = ((i : ℕ) : ZMod p) := by
  simp [aRows, ComplJ8Cell.cellRowsBP, ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowB, cellRow0,
    List.getD_eq_getElem _ _ i.isLt]

/-- The atom row environment's added columns `130 .. 204` are `newBA`. -/
theorem ezA_new (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length))
    (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) (k : ℕ) (h1 : 130 ≤ k) (h2 : k < 205) :
    (ezA δ b D hA o χ pubs i).trace k = newBA D k i := by
  rw [ComplJ8Atom.EZ_trace δ b hA (powN o _) o _ pubs _ _ hinj i k (by omega) h2, if_neg (by omega)]

/-- The atom row environment's serial column is the row position. -/
theorem ezA_idx (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length))
    (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    (ezA δ b D hA o χ pubs i).trace 2 = ((i : ℕ) : ZMod p) := by
  rw [ComplJ8Atom.EZ_trace δ b hA (powN o _) o _ pubs _ _ hinj i 2 le_rfl (by norm_num), if_pos (by norm_num)]
  exact (colAH_fields δ b D hA o χ pubs i).1

/-- **`dMB_closed`**: `dMB = ρV + compress (γV, 0) (zAt, 0, leaf_y, 0, idx)`. -/
theorem dMB_closed (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length))
    (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    HonestA8.dMB δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs) (newBA D) i =
      ρV δ χ + FiniteIO.compress (m := 5) ⟨γV δ χ, 0⟩
        (![Quad.mk _ (chalsAJ8Z δ χ 37) (chalsAJ8Z δ χ 38), 0, (aRows δ D χ i).p.leaf, 0,
           liftQ δ ((i : ℕ) : ZMod p)] : Fin 5 → 𝕂′) := by
  have e4 : Quad.mk _ ((ekA δ b D hA o χ pubs i).trace 4) ((ekA δ b D hA o χ pubs i).trace 5) =
      (aRows δ D χ i).p.leaf := by
    rw [ComplJ8OfBal.ekA_role δ b D hA o hinj χ pubs i 4 (by omega),
      ComplJ8OfBal.ekA_role δ b D hA o hinj χ pubs i 5 (by omega)]
    simp only [roleVal, show (4 : ℕ) % 2 = 0 from rfl, show (5 : ℕ) % 2 = 1 from rfl, if_true,
      show ((1 : ℕ) = 0) = False from by simp, if_false, show (4 : ℕ) / 2 = 2 from rfl,
      show (5 : ℕ) / 2 = 2 from rfl, Quad.mk_re_im]
    rfl
  rw [dMB_eq, ComplJ8OfBal.keyVec_mb, ekA_chal, e4, ezA_idx δ b D hA o hinj χ pubs i]

/-- **`dC_closed`**: `dC = ρH + compress (γH, 0) (idx_o, 0, l_o, kR_o, vR_o)`. -/
theorem dC_closed (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length))
    (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    HonestA8.dC δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs) (newBA D) i =
      ComplJ8Bad.ρH δ χ + FiniteIO.compress (⟨ComplJ8Bad.γH δ χ, 0⟩ : FiniteIO.IOCoins 𝕂′)
        (BalanceQ.liftRec (K := K) (L := 𝕂′) (fun c : Fin 5 => algebraMap (ZMod p) K
          (![newBA D 200 i, 0, newBA D 201 i, newBA D 202 i, newBA D 203 i] c))) := by
  rw [dC_eq]
  congr 2
  funext c
  simp only [BalanceQ.liftRec, ServeH.keyVec5]
  congr 2
  fin_cases c <;>
    simp [AtomChipHQ.oldKey, CoeffExpr.eval, cv, AtomChipHQ.idxO, AtomChipHQ.lO, AtomChipHQ.kRO,
      AtomChipHQ.vRO,
      ezA_new δ b D hA o hinj χ pubs i 200 (by norm_num) (by norm_num),
      ezA_new δ b D hA o hinj χ pubs i 201 (by norm_num) (by norm_num),
      ezA_new δ b D hA o hinj χ pubs i 202 (by norm_num) (by norm_num),
      ezA_new δ b D hA o hinj χ pubs i 203 (by norm_num) (by norm_num)]

/-- **`dMI_closed`**: `dMI = ρH + compress (γH, 0) (2(1−conv), (1−conv)·idx_o − conv, 2, idx, 4)`. -/
theorem dMI_closed (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length))
    (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    HonestA8.dMI δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs) (newBA D) i =
      ComplJ8Bad.ρH δ χ + FiniteIO.compress (⟨ComplJ8Bad.γH δ χ, 0⟩ : FiniteIO.IOCoins 𝕂′)
        (BalanceQ.liftRec (K := K) (L := 𝕂′) (fun c : Fin 5 => algebraMap (ZMod p) K
          (![2 * (1 - newBA D 198 i), (1 - newBA D 198 i) * newBA D 200 i - newBA D 198 i, 2,
             ((i : ℕ) : ZMod p), 4] c))) := by
  rw [dMI_eq]
  congr 2
  funext c
  simp only [BalanceQ.liftRec, ServeH.keyVec5]
  congr 2
  fin_cases c <;>
    simp [AtomChipHQ.incKey, CoeffExpr.eval, cv, notE, AtomChipHQ.conv, AtomChipHQ.idxO, AtomChipHQ.tagInc,
      ezA_new δ b D hA o hinj χ pubs i 198 (by norm_num) (by norm_num),
      ezA_new δ b D hA o hinj χ pubs i 200 (by norm_num) (by norm_num),
      show (ezA δ b D hA o χ pubs i).trace Cell.idx = ((i : ℕ) : ZMod p) from
        ezA_idx δ b D hA o hinj χ pubs i]

/-! ### The same with the publics replaced by `0` (`dMB_pubs0`, `dC_pubs0`, `dMI_pubs0`) -/

theorem dMB_closed_pubs0 (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length))
    (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    HonestA8.dMB δ b hA (powN o _) o (chalsAJ8Z δ χ) (fun _ => 0) (colAH δ b D hA o χ (fun _ => 0)) (newBA D) i =
      ρV δ χ + FiniteIO.compress (m := 5) ⟨γV δ χ, 0⟩
        (![Quad.mk _ (chalsAJ8Z δ χ 37) (chalsAJ8Z δ χ 38), 0, (aRows δ D χ i).p.leaf, 0,
           liftQ δ ((i : ℕ) : ZMod p)] : Fin 5 → 𝕂′) :=
  (dMB_pubs0 δ b D hA o χ pubs i).symm.trans (dMB_closed δ b D hA o hinj χ pubs i)

theorem dC_closed_pubs0 (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length))
    (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    HonestA8.dC δ b hA (powN o _) o (chalsAJ8Z δ χ) (fun _ => 0) (colAH δ b D hA o χ (fun _ => 0)) (newBA D) i =
      ComplJ8Bad.ρH δ χ + FiniteIO.compress (⟨ComplJ8Bad.γH δ χ, 0⟩ : FiniteIO.IOCoins 𝕂′)
        (BalanceQ.liftRec (K := K) (L := 𝕂′) (fun c : Fin 5 => algebraMap (ZMod p) K
          (![newBA D 200 i, 0, newBA D 201 i, newBA D 202 i, newBA D 203 i] c))) :=
  (dC_pubs0 δ b D hA o χ pubs i).symm.trans (dC_closed δ b D hA o hinj χ pubs i)

theorem dMI_closed_pubs0 (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length))
    (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    HonestA8.dMI δ b hA (powN o _) o (chalsAJ8Z δ χ) (fun _ => 0) (colAH δ b D hA o χ (fun _ => 0)) (newBA D) i =
      ComplJ8Bad.ρH δ χ + FiniteIO.compress (⟨ComplJ8Bad.γH δ χ, 0⟩ : FiniteIO.IOCoins 𝕂′)
        (BalanceQ.liftRec (K := K) (L := 𝕂′) (fun c : Fin 5 => algebraMap (ZMod p) K
          (![2 * (1 - newBA D 198 i), (1 - newBA D 198 i) * newBA D 200 i - newBA D 198 i, 2,
             ((i : ℕ) : ZMod p), 4] c))) :=
  (dMI_pubs0 δ b D hA o χ pubs i).symm.trans (dMI_closed δ b D hA o hinj χ pubs i)

theorem aRow_closed_pubs0 (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length))
    (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin D.acs.length) :
    CellTraceHQ.dRow δ b hA (powN o _) o (chalsAJ8Z δ χ) (fun _ => 0) (aCol δ b D χ) (mhvA D) i =
      ComplJ8Bad.ρH δ χ + FiniteIO.compress (⟨ComplJ8Bad.γH δ χ, 0⟩ : FiniteIO.IOCoins 𝕂′)
        (BalanceQ.liftRec (K := K) (L := 𝕂′) (fun c : Fin 5 => algebraMap (ZMod p) K
          (![(aRows δ D χ i).idx, (aRows δ D χ i).wL,
             (aRows δ D χ i).wL * (aRows δ D χ i).idL + (1 - (aRows δ D χ i).wL) * (aRows δ D χ i).aL,
             (aRows δ D χ i).wR,
             (aRows δ D χ i).wR * (aRows δ D χ i).idR + (1 - (aRows δ D χ i).wR) * (aRows δ D χ i).aR] c))) :=
  (dRowHQ_pubs0 δ b hA (powN o _) o (chalsAJ8Z δ χ) pubs (aCol δ b D χ) (mhvA D) i).symm.trans
    (aRow_closed δ b D hA o hinj χ pubs i)

end Key

end

#print axioms aE0_base
#print axioms aRows_idx
#print axioms ezA_new
#print axioms ezA_idx
#print axioms aRow_closed
#print axioms dMB_closed
#print axioms dC_closed
#print axioms dMI_closed
#print axioms aRow_closed_pubs0
#print axioms dMB_closed_pubs0
#print axioms dC_closed_pubs0
#print axioms dMI_closed_pubs0

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomKey
