/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHCellKey.lean

  Stated generically in `p`, `K`, `δ`, `b`
  (instantiate `p := P`, `K := KC`, `δ := deltaF`, `b := powerBasis3`). -/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellKey

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8

noncomputable section

section Key
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K) {n : ℕ} (hn0 : 0 < n) (nodes : Fin n → ZMod p) {h : ℕ}
  (orbit : StrictOrbitDomain (ZMod p) 3 h)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The generic `EW` trace**: the chip environment's row `i` reads `colW` on `2 ≤ j < 242`. -/
theorem EW_trace (hinj : Function.Injective nodes) (chals pubs : ℕ → K) (col : ℕ → Fin n → ZMod p)
    (mhv kbLv kbRv : Fin n → ZMod p) (iv av : Fin n → 𝕂′) (i : Fin n) (j : ℕ) (h2 : 2 ≤ j) (hj : j < 242) :
    (HonestKW.EW δ b hn0 nodes orbit chals pubs col mhv kbLv kbRv iv av i).trace j =
      HonestKW.colW δ b col mhv kbLv kbRv iv av j i := by
  unfold HonestKW.EW
  rw [env_trace hn0 nodes hinj _ _ _ _ i (show j < (HonestKW.cellTemplateHQKW δ).width 3 by
    rw [HonestKW.cellTemplateHQKW_width]; omega)]
  simp [fullCol,show j ≠ 0 by omega, show j ≠ 1 by omega]

/-- **The cell handle denominator in closed form**: no dependence on `nodes`, `orbit`, `pubs`. -/
theorem dRowW_closed (χ : Coins frameJ8 K) (hinj : Function.Injective nodes) (pubs : ℕ → K)
    (V : Fin n → CellVals (ZMod p) 𝕂′) (mhv kbLv kbRv : Fin n → ZMod p) (i : Fin n) :
    HonestKW.dRowW δ b hn0 nodes orbit (chalsMJ8 δ χ) pubs (cellCol δ b V) mhv kbLv kbRv i =
      FiniteIO.compress (⟨ComplJ8Bad.γH δ χ, ComplJ8Bad.ρH δ χ⟩ : FiniteIO.IOCoins 𝕂′)
        (BalanceQ.liftRec (K := K) (L := 𝕂′) (fun c => algebraMap (ZMod p) K
          (![(V i).idx, (V i).wL + kbLv i, (V i).wL * (V i).idL + (1 - (V i).wL) * (V i).aL,
             (V i).wR + kbRv i, (V i).wR * (V i).idR + (1 - (V i).wR) * (V i).aR] c))) := by
  unfold HonestKW.dRowW
  rw [TeleHQ.denKeyQ_ev δ _ _ _ rfl, ComplJ8Of.coinsQ_cell δ b χ _ rfl]
  have hT : ∀ j, 2 ≤ j → j < 242 →
      (HonestKW.EW δ b hn0 nodes orbit (chalsMJ8 δ χ) pubs (cellCol δ b V) mhv kbLv kbRv
        (fun _ => 0) (fun _ => 0) i).trace j =
      HonestKW.colW δ b (cellCol δ b V) mhv kbLv kbRv (fun _ => 0) (fun _ => 0) j i :=
    fun j h2 hj => EW_trace δ b hn0 nodes orbit hinj _ _ _ _ _ _ _ _ i j h2 hj
  congr 1
  funext c
  simp only [BalanceQ.liftRec, ServeH.keyVec5]
  congr 2
  fin_cases c <;>
    simp [TwoProviderQ.keyHK, CellH.valE, CoeffExpr.eval, Cell.idx, Cell.wL, Cell.wR, Cell.idL,
      Cell.idR, Cell.aL, Cell.aR, CellTwinK.kbL, CellTwinK.kbR,
      hT 2 (by norm_num) (by norm_num), hT 3 (by norm_num) (by norm_num), hT 4 (by norm_num) (by norm_num),
      hT 5 (by norm_num) (by norm_num), hT 6 (by norm_num) (by norm_num), hT 7 (by norm_num) (by norm_num),
      hT 8 (by norm_num) (by norm_num), hT 130 (by norm_num) (by norm_num), hT 131 (by norm_num) (by norm_num),
      HonestKW.colW, extColF,HonestKW.newW, cellCol, CellVals.base]

/-- `dNW` for `j < n`. -/
theorem dNW_closed (χ : Coins frameJ8 K) (hinj : Function.Injective nodes) (pubs : ℕ → K)
    (V : Fin n → CellVals (ZMod p) 𝕂′) (mhv kbLv kbRv : Fin n → ZMod p) (j : ℕ) (hj : j < n) :
    HonestKW.dNW δ b hn0 nodes orbit (chalsMJ8 δ χ) pubs (cellCol δ b V) mhv kbLv kbRv j =
      FiniteIO.compress (⟨ComplJ8Bad.γH δ χ, ComplJ8Bad.ρH δ χ⟩ : FiniteIO.IOCoins 𝕂′)
        (BalanceQ.liftRec (K := K) (L := 𝕂′) (fun c => algebraMap (ZMod p) K
          (![(V ⟨j, hj⟩).idx, (V ⟨j, hj⟩).wL + kbLv ⟨j, hj⟩,
             (V ⟨j, hj⟩).wL * (V ⟨j, hj⟩).idL + (1 - (V ⟨j, hj⟩).wL) * (V ⟨j, hj⟩).aL,
             (V ⟨j, hj⟩).wR + kbRv ⟨j, hj⟩,
             (V ⟨j, hj⟩).wR * (V ⟨j, hj⟩).idR + (1 - (V ⟨j, hj⟩).wR) * (V ⟨j, hj⟩).aR] c))) := by
  unfold HonestKW.dNW
  rw [dif_pos hj]
  exact dRowW_closed δ b hn0 nodes orbit χ hinj pubs V mhv kbLv kbRv ⟨j, hj⟩

/-- **No dependence on nodes / orbit / publics.** -/
theorem dRowW_nodes_irrel (χ : Coins frameJ8 K) (nodes' : Fin n → ZMod p) {h' : ℕ}
    (orbit' : StrictOrbitDomain (ZMod p) 3 h') (hinj : Function.Injective nodes)
    (hinj' : Function.Injective nodes') (pubs pubs' : ℕ → K)
    (V : Fin n → CellVals (ZMod p) 𝕂′) (mhv kbLv kbRv : Fin n → ZMod p) (i : Fin n) :
    HonestKW.dRowW δ b hn0 nodes orbit (chalsMJ8 δ χ) pubs (cellCol δ b V) mhv kbLv kbRv i =
      HonestKW.dRowW δ b hn0 nodes' orbit' (chalsMJ8 δ χ) pubs' (cellCol δ b V) mhv kbLv kbRv i := by
  rw [dRowW_closed δ b hn0 nodes orbit χ hinj pubs V mhv kbLv kbRv i,
    dRowW_closed δ b hn0 nodes' orbit' χ hinj' pubs' V mhv kbLv kbRv i]

end Key

#print axioms EW_trace
#print axioms dRowW_closed
#print axioms dNW_closed
#print axioms dRowW_nodes_irrel

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellKey
