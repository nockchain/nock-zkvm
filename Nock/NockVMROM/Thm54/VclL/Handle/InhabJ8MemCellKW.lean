/-
  Nock/NockVMROM/Thm54/VclL/Handle/InhabJ8MemCellKW.lean

  **The honest `cellChipHQKW` (242) trace of THE inhabitant.**  New module, additive.

  * `HonestKW.cellChipHQKW = CellTwinKW.cellChipHQKW` (`rfl`; REPORT-J8B HA's open identification, checked here).
  * `dRowW0`: the `keyHK` denominator of row `i` in closed form, `compress (ρH′, γH′) (lift [i, 0, 0, 0, aR_i])`
    (atom children: kind `0`, value the atom).
  * `trM0` and `cellKW0_sat` / `cellKW0_bind`: the honest trace (kind bits `0`) is accepted with its preprocessing.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemCell
import Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemCell

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.ComputeTable (FP)

noncomputable section

theorem cellChipHQKW_eq {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
    (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    HonestKW.cellChipHQKW δF b hn nodes orbit chals pubs = CellTwinKW.cellChipHQKW δF b hn nodes orbit chals pubs :=
  rfl

section KW
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h : ℕ} (hn : 0 < 2)
  (nodes : Fin 2 → F) (orbit : StrictOrbitDomain F 3 h)

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The handle coins at the memory leaves `33..36`. -/
abbrev hcoins (chals : ℕ → K) : FiniteIO.IOCoins 𝕂′ :=
  ⟨Quad.mk _ (chals 33) (chals 35), Quad.mk _ (chals 34) (chals 36)⟩

/-- The provided wire key of row `j`: `(serial, 0, 0, 0, aR)` (both children small atoms, kind `0`). -/
def kRow (j : ℕ) : Fin 5 → F := ![(j : F), 0, 0, 0, aRv j]

/-- The closed-form `keyHK` denominator of row `j`. -/
def dKW (chals : ℕ → K) (j : ℕ) : 𝕂′ :=
  FiniteIO.compress (hcoins δF chals) (BalanceQ.liftRec (K := K) (L := 𝕂′) fun c => algebraMap F K (kRow j c))

theorem EW_base (chals pubs : ℕ → K) (hinj : Function.Injective nodes) (V : Fin 2 → CellVals F 𝕂′)
    (mhv : Fin 2 → F) (iv av : Fin 2 → 𝕂′) (i : Fin 2) (j : ℕ) (h2 : 2 ≤ j) (hj : j < 129) :
    (HonestKW.EW δF b hn nodes orbit chals pubs (cellCol δF b V) mhv 0 0 iv av i).trace j = (V i).base j := by
  unfold HonestKW.EW
  rw [env_trace hn nodes hinj _ _ _ _ i (show j < (HonestKW.cellTemplateHQKW δF).width 3 by
    rw [HonestKW.cellTemplateHQKW_width]; omega)]
  simp [fullCol, show j ≠ 0 by omega, show j ≠ 1 by omega, HonestKW.colW, extColF, hj, cellCol]

theorem EW_kb (chals pubs : ℕ → K) (hinj : Function.Injective nodes) (V : Fin 2 → CellVals F 𝕂′)
    (mhv : Fin 2 → F) (iv av : Fin 2 → 𝕂′) (i : Fin 2) (j : ℕ) (hj : j = 130 ∨ j = 131) :
    (HonestKW.EW δF b hn nodes orbit chals pubs (cellCol δF b V) mhv 0 0 iv av i).trace j = 0 := by
  unfold HonestKW.EW
  rw [env_trace hn nodes hinj _ _ _ _ i (show j < (HonestKW.cellTemplateHQKW δF).width 3 by
    rw [HonestKW.cellTemplateHQKW_width]; omega)]
  rcases hj with rfl | rfl <;>
    simp [fullCol, HonestKW.colW, extColF, HonestKW.newW, CellTwinK.kbL, CellTwinK.kbR]

theorem dRowW0 (chals pubs : ℕ → K) (hinj : Function.Injective nodes) (γ ρ z : 𝕂′) (mv mx mx1 : ℕ → ℕ)
    (mhv : Fin 2 → F) (i : Fin 2) :
    HonestKW.dRowW δF b hn nodes orbit chals pubs (cellCol δF b (cvals δF γ ρ z mv mx mx1)) mhv 0 0 i =
      dKW δF chals i := by
  unfold HonestKW.dRowW
  rw [TeleHQ.denKeyQ_ev δF _ _ _ rfl]
  have hc : ∀ r, (gatherEnv b ((HonestKW.cellTemplateHQKW δF).col0 3)
      (HonestKW.EW δF b hn nodes orbit chals pubs (cellCol δF b (cvals δF γ ρ z mv mx mx1)) mhv 0 0
        (fun _ => 0) (fun _ => 0) i)).chal r = chals r :=
    fun r => HonestKW.gatherW_chal δF b chals _ rfl r
  have hB := EW_base δF b hn nodes orbit chals pubs hinj (cvals δF γ ρ z mv mx mx1) mhv (fun _ => 0) (fun _ => 0) i
  have hK := EW_kb δF b hn nodes orbit chals pubs hinj (cvals δF γ ρ z mv mx mx1) mhv (fun _ => 0) (fun _ => 0) i
  unfold dKW
  congr 1
  · simp only [TeleHQ.coinsQ, hc]
  · funext c
    simp only [BalanceQ.liftRec, ServeH.keyVec5]
    congr 2
    fin_cases c <;>
      simp [TwoProviderQ.keyHK, CellH.valE, CoeffExpr.eval, kRow, Cell.idx, Cell.wL, Cell.wR, Cell.idL,
        Cell.idR, Cell.aL, Cell.aR,
        hB 2 (by norm_num) (by norm_num), hB 5 (by norm_num) (by norm_num), hB 6 (by norm_num) (by norm_num),
        hB 3 (by norm_num) (by norm_num), hB 4 (by norm_num) (by norm_num), hB 7 (by norm_num) (by norm_num),
        hB 8 (by norm_num) (by norm_num), hK 130 (Or.inl rfl), hK 131 (Or.inr rfl), CellTwinK.kbL, CellTwinK.kbR,
        CellVals.base, cellFill, cellFillInv, crow]

/-- **The honest `cellChipHQKW` trace** (multiplicities `mv mx mx1 mh` per row, kind bits `0`). -/
def trM0 (chals pubs : ℕ → K) (γ ρ z : 𝕂′) (mv mx mx1 mh : ℕ → ℕ) :=
  HonestKW.cellTraceHQKW δF b hn nodes orbit chals pubs (cellCol δF b (cvals δF γ ρ z mv mx mx1))
    (fun i => (mh i : F)) 0 0

theorem cellKW0_sat (chals pubs : ℕ → K) (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin 2) (hi : (i : ℕ) + 1 < 2), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ z : 𝕂′) (mv mx mx1 mh : ℕ → ℕ) (hok : ChalsOK δF chals γ ρ 11)
    (hzc : Quad.mk _ (chals 2) (chals 3) = z) (hz : z ≠ 0)
    (hv : ∀ j < 2, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (crow δF z mv mx mx1 j)) ≠ 0)
    (hx0 : ∀ j < 2, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (crow δF z mv mx mx1 j) 0) ≠ 0)
    (hx1 : ∀ j < 2, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (crow δF z mv mx mx1 j) 1) ≠ 0)
    (hV : vTot δF γ ρ z mv mx mx1 = Quad.mk _ (pubs 0) (pubs 1))
    (hX : xTot δF γ ρ z mv mx mx1 = Quad.mk _ (pubs 2) (pubs 3))
    (hpole : ∀ j < 2, dKW δF chals j ≠ 0)
    (hH : Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) =
      ∑ j ∈ Finset.range 2, liftQ δF (mh j : F) * (dKW δF chals j)⁻¹) :
    (CellTwinKW.cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies
      (trM0 δF b hn nodes orbit chals pubs γ ρ z mv mx mx1 mh) := by
  have hok0 := cellOk0 δF b hn nodes orbit chals pubs hinj hadj γ ρ z mv mx mx1 hok hzc hz hv hx0 hx1 hV hX
  have hs := (cellChipOk_sat δF b hn nodes orbit chals pubs true _ hok0).2.1
  refine HonestKW.cellChipHQKW_accepts_honest δF b hn nodes orbit chals pubs _ _ 0 0 hinj hadj hs
    (fun i => HonestK8.sideOK_zero (Or.inl (by simp [cellCol, CellVals.base, Cell.wL, cellFill, cellFillInv, crow])))
    (fun i => HonestK8.sideOK_zero (Or.inl (by simp [cellCol, CellVals.base, Cell.wR, cellFill, cellFillInv, crow])))
    (fun i => by rw [dRowW0 δF b hn nodes orbit chals pubs hinj]; exact hpole i i.isLt) ?_
  rw [hH]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < 2 := Finset.mem_range.mp hj
  simp only [HonestKW.dNW, CellTraceH.mN, dif_pos hj']
  rw [dRowW0 δF b hn nodes orbit chals pubs hinj]

theorem cellKW0_bind (chals pubs : ℕ → K) (γ ρ z : 𝕂′) (mv mx mx1 mh : ℕ → ℕ) :
    (CellTwinKW.cellChipHQKW δF b hn nodes orbit chals pubs).BindsPreprocessing
      (trM0 δF b hn nodes orbit chals pubs γ ρ z mv mx mx1 mh) := by
  intro j
  fin_cases j
  · exact honestQ_zero hn nodes _ (by rw [HonestKW.cellTemplateHQKW_width]; omega)
  · exact honestQ_one hn nodes _ (by rw [HonestKW.cellTemplateHQKW_width]; omega)

end KW

end

end Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemCell
