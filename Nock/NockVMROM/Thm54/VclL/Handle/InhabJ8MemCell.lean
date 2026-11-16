/-
  Nock/NockVMROM/Thm54/VclL/Handle/InhabJ8MemCell.lean

  **The honest cell rows of THE inhabitant** (`*[[0 0] [0 1]] = [0 0]`).

  Two cell rows: row `0` is `s0 = [0 0]` (serial `0`), row `1` is `f0 = [0 1]` (serial `1`); both children of both
  are small atoms (weights `0`, rank limbs `(lo, hi) = (1, 0)`, kind bits `0`).  The multiplicities (`mv`, `mx`,
  `mx1`, `mh`) are PARAMETERS (`ℕ`-valued per row).

  * `crow`: the committed content of row `j` (`CellVals`), `cellBase0`: the base facts at `n = 2`;
  * `cellOk0`: the `ok`-gated original cell chip accepts the honest trace (`cellOk_sat`), given the IO denominators
    nonzero and the publics `0..3` the two terminals.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemDom
import Nock.NockVMROM.Thm54.VclL.Handle.HonestKW
import Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemAccept

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
open Nock.ComputeTable (FP)

noncomputable section

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The right child atom of row `j` (`s0`: `0`, `f0`: `1`). -/
def aRv (j : ℕ) : F := if j = 1 then 1 else 0

/-- **The committed content of cell row `j`** (round-1/2 slots zero; `cellFill` fills them). -/
def crow (z : 𝕂′) (mv mx mx1 : ℕ → ℕ) (j : ℕ) : CellVals F 𝕂′ where
  idx := (j : F)
  idL := 0
  idR := 0
  wL := 0
  wR := 0
  aL := 0
  aR := aRv j
  lo := 1
  hi := 0
  loL := 0
  hiL := 0
  loR := 0
  hiR := 0
  carry := 0
  mv := (mv j : F)
  mx := (mx j : F)
  mx1 := (mx1 j : F)
  bit := fun k => if k = 0 then 1 else 0
  p := FP.cons z (FP.atomFP z (liftQ δF 0)) (FP.atomFP z (liftQ δF (aRv j)))
  l := FP.atomFP z (liftQ δF 0)
  r := FP.atomFP z (liftQ δF (aRv j))
  vInv := 0
  lInv := 0
  rInv := 0
  x0Inv := 0
  x1Inv := 0
  vAcc := 0
  xAcc := 0

theorem cellBase0 (z : 𝕂′) (mv mx mx1 : ℕ → ℕ) (i : Fin 2) : CellBaseFacts (fun j : Fin 2 => crow δF z mv mx mx1 j) i := by
  refine ⟨fun h => ?_, fun hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k _ => ?_, fun _ => ?_, fun _ => ?_⟩
  · simp [crow, h]
  · have : (i : ℕ) = 0 := by omega
    simp [crow, this]
  · simp [crow]
  · simp [crow]
  · simp [crow]
  · simp [crow]
  · simp [crow]
  · simp only [crow]
    rw [Finset.sum_eq_single 0 (fun k _ hk => by simp [hk]) (fun h => absurd (by simp) h)]
    simp
  · simp only [crow]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    simp
  · simp only [crow]; split_ifs <;> simp
  · simp [crow]
  · simp [crow]

/-! ## The filled rows, the IO terms and the `ok`-gated original acceptance -/

/-- The filled honest rows (`cellFill`: the five inverses and the two accumulators). -/
abbrev cvals (γ ρ z : 𝕂′) (mv mx mx1 : ℕ → ℕ) : Fin 2 → CellVals F 𝕂′ :=
  fun i => cellFill δF γ ρ (crow δF z mv mx mx1) i

/-- The validity terminal `Σ_j vTerm_j`. -/
def vTot (γ ρ z : 𝕂′) (mv mx mx1 : ℕ → ℕ) : 𝕂′ :=
  ∑ k ∈ Finset.range 2, vTermOf δF (cellFillInv δF γ ρ (crow δF z mv mx mx1 k))

/-- The fingerprint-export terminal `Σ_j xTerm_j`. -/
def xTot (γ ρ z : 𝕂′) (mv mx mx1 : ℕ → ℕ) : 𝕂′ :=
  ∑ k ∈ Finset.range 2, xTermOf δF (cellFillInv δF γ ρ (crow δF z mv mx mx1 k))

theorem vTerm_crow (γ ρ z : 𝕂′) (mv mx mx1 : ℕ → ℕ) (k : ℕ) :
    vTermOf δF (cellFillInv δF γ ρ (crow δF z mv mx mx1 k)) =
      liftQ δF (mv k : F) * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (crow δF z mv mx mx1 k)))⁻¹ := by
  simp [vTermOf, cellFillInv, crow, liftQ]

theorem xTerm_crow (γ ρ z : 𝕂′) (mv mx mx1 : ℕ → ℕ) (k : ℕ) :
    xTermOf δF (cellFillInv δF γ ρ (crow δF z mv mx mx1 k)) =
      liftQ δF (mx k : F) * (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (crow δF z mv mx mx1 k) 0))⁻¹ +
      liftQ δF (mx1 k : F) * (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (crow δF z mv mx mx1 k) 1))⁻¹ := by
  simp [xTermOf, cellFillInv, crow]

theorem cellMixed0 (γ ρ z : 𝕂′) (mv mx mx1 : ℕ → ℕ) (pubs : ℕ → K) (hz : z ≠ 0)
    (hv : ∀ j < 2, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (crow δF z mv mx mx1 j)) ≠ 0)
    (hx0 : ∀ j < 2, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (crow δF z mv mx mx1 j) 0) ≠ 0)
    (hx1 : ∀ j < 2, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (crow δF z mv mx mx1 j) 1) ≠ 0)
    (hV : vTot δF γ ρ z mv mx mx1 = Quad.mk _ (pubs 0) (pubs 1))
    (hX : xTot δF γ ρ z mv mx mx1 = Quad.mk _ (pubs 2) (pubs 3)) (i : Fin 2) :
    CellMixedFacts δF pubs γ ρ z (cvals δF γ ρ z mv mx mx1) i :=
  cellFill_facts γ ρ (crow δF z mv mx mx1) z pubs i hz (fun j _ => rfl) (fun j _ _ => rfl)
    (fun j _ _ => rfl) hv (fun j _ h => absurd rfl h) (fun j _ h => absurd rfl h) hx0 hx1 hV hX

section Ok
variable [FiniteDimensional F K] [DecidableEq F] (b : Basis (Fin 3) F K) {h : ℕ} (hn : 0 < 2)
  (nodes : Fin 2 → F) (orbit : StrictOrbitDomain F 3 h)

/-- **The `ok`-gated original cell chip accepts the honest two-row trace.** -/
theorem cellOk0 (chals pubs : ℕ → K) (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin 2) (hi : (i : ℕ) + 1 < 2), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ z : 𝕂′) (mv mx mx1 : ℕ → ℕ) (hok : ChalsOK δF chals γ ρ 11)
    (hzc : Quad.mk _ (chals 2) (chals 3) = z) (hz : z ≠ 0)
    (hv : ∀ j < 2, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (vKeyOf δF (crow δF z mv mx mx1 j)) ≠ 0)
    (hx0 : ∀ j < 2, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (crow δF z mv mx mx1 j) 0) ≠ 0)
    (hx1 : ∀ j < 2, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (xKeyOf δF (crow δF z mv mx mx1 j) 1) ≠ 0)
    (hV : vTot δF γ ρ z mv mx mx1 = Quad.mk _ (pubs 0) (pubs 1))
    (hX : xTot δF γ ρ z mv mx mx1 = Quad.mk _ (pubs 2) (pubs 3)) :
    RAP.SatisfiesWithPreprocessing (cellChipOk δF b hn nodes orbit chals pubs true)
      (fun j => honestQ hn nodes (cellCol δF b (cvals δF γ ρ z mv mx mx1)) 225
        (Fin.cast (cellChipOk_w δF b hn nodes orbit chals pubs true) j)) :=
  cellOk_sat δF b hn nodes orbit chals pubs (cvals δF γ ρ z mv mx mx1) hinj hadj γ ρ z hok hzc
    (fun i => cellBaseFacts_fill δF γ ρ (crow δF z mv mx mx1) i (cellBase0 δF z mv mx mx1 i))
    (fun i => cellMixed0 δF γ ρ z mv mx mx1 pubs hz hv hx0 hx1 hV hX i)

end Ok

end Rows

end

end Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemCell
