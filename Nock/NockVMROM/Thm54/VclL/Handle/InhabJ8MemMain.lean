/-
  Nock/NockVMROM/Thm54/VclL/Handle/InhabJ8MemMain.lean

  **The memory conjuncts of `AcceptsJ8''''` at THE inhabitant**
  (`*[[0 0] [0 1]] = [0 0]`).

  * `withMem Pb0 hdvd`: any `PubJ8` with the memory fields replaced (`nC = 2`, `kroots = nW = 1`, orbits of height
    `1` from `3·2 ∣ p − 1`, nodes `ω^i`).
  * `trMJ` / `trWJ`: the honest cell / walk traces; `pubsC0` / `pubsW0`: their publics (multiplicities `μ`).
  * `memC_*` / `memW_*`: `hsatC hbindC hinjC hadjC hnpC hsatW hbindW hinjW hadjW hkW hknW hkpW`.
  * Closed forms of the terminals; `hfxC0` (the cell ↔ walk fingerprint link).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemWalk
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemMain

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemDom Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemCell
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemWalk

noncomputable section

section Mem
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The memory multiplicities** (cross-chip data): per cell row `j` the validity `mv`, fingerprint exports `mx`
(selector `0`) / `mx1` (selector `1`), handle export `mh`; the walk row's path provides `mL`, `mR`. -/
structure Mults where
  mv : ℕ → ℕ
  mx : ℕ → ℕ
  mx1 : ℕ → ℕ
  mh : ℕ → ℕ
  mL : ℕ
  mR : ℕ

/-- The fingerprint seed `z′ = χ₂ + χ₃√δ`. -/
abbrev zJ (χ : Coins frameJ8 K) : 𝕂′ := Quad.mk _ (χ c2) (χ c3)
/-- The validity IO coins `γ′ = χ₄ + χ₆√δ`, `ρ′ = χ₅ + χ₇√δ`. -/
abbrev γV (χ : Coins frameJ8 K) : 𝕂′ := Quad.mk _ (χ c4) (χ c6)
abbrev ρV (χ : Coins frameJ8 K) : 𝕂′ := Quad.mk _ (χ c5) (χ c7)

/-- The cell validity terminal `Σ_j vTerm_j`. -/
def cvT (χ : Coins frameJ8 K) (μ : Mults) : 𝕂′ := vTot δ (γV δ χ) (ρV δ χ) (zJ δ χ) μ.mv μ.mx μ.mx1
/-- The cell fingerprint-export terminal `Σ_j xTerm_j`. -/
def cxT (χ : Coins frameJ8 K) (μ : Mults) : 𝕂′ := xTot δ (γV δ χ) (ρV δ χ) (zJ δ χ) μ.mv μ.mx μ.mx1
/-- The cell handle-export terminal `Σ_j mh_j / dKW_j`. -/
def chT (χ : Coins frameJ8 K) (μ : Mults) : 𝕂′ :=
  ∑ j ∈ Finset.range 2, liftQ δ (μ.mh j : ZMod p) * (dKW δ (chalsMJ8 δ χ) j)⁻¹
/-- The walk fingerprint-import terminal. -/
def wxT (χ : Coins frameJ8 K) (μ : Mults) : 𝕂′ :=
  wxTot δ (γV δ χ) (ρV δ χ) (chalsMJ8 δ χ 0) (zJ δ χ) μ.mL μ.mR
/-- The walk path-provide terminal. -/
def wpT (χ : Coins frameJ8 K) (μ : Mults) : 𝕂′ :=
  wpTot δ (γV δ χ) (ρV δ χ) (chalsMJ8 δ χ 0) (zJ δ χ) μ.mL μ.mR
/-- The walk handle-import terminal (one row, key `(0,0,0,0,0)`). -/
def whX (χ : Coins frameJ8 K) : 𝕂′ := (hden δ (chalsMJ8 δ χ) 5 vX)⁻¹
/-- The walk handle-provide terminal. -/
def whP (χ : Coins frameJ8 K) (μ : Mults) : 𝕂′ :=
  liftQ δ (μ.mL : ZMod p) * (hden δ (chalsMJ8 δ χ) 4 vPL)⁻¹ +
    liftQ δ (μ.mR : ZMod p) * (hden δ (chalsMJ8 δ χ) 4 vPR)⁻¹

/-- **The cell table's publics**: `0/1` validity, `2/3` fingerprint export, `4/5` handle export. -/
def pubsC0 (χ : Coins frameJ8 K) (μ : Mults) : ℕ → K := fun i =>
  if i = 0 then Quad.re _ (cvT δ χ μ) else if i = 1 then Quad.im _ (cvT δ χ μ)
  else if i = 2 then Quad.re _ (cxT δ χ μ) else if i = 3 then Quad.im _ (cxT δ χ μ)
  else if i = 4 then Quad.re _ (chT δ χ μ) else if i = 5 then Quad.im _ (chT δ χ μ) else 0

/-- **The J-8 walk's publics**: `0/1` fingerprint import, `2/3` path provide, `4/5` handle import, `6/7` handle
provide. -/
def pubsW0 (χ : Coins frameJ8 K) (μ : Mults) : ℕ → K := fun i =>
  if i = 0 then Quad.re _ (wxT δ χ μ) else if i = 1 then Quad.im _ (wxT δ χ μ)
  else if i = 2 then Quad.re _ (wpT δ χ μ) else if i = 3 then Quad.im _ (wpT δ χ μ)
  else if i = 4 then Quad.re _ (whX δ χ) else if i = 5 then Quad.im _ (whX δ χ)
  else if i = 6 then Quad.re _ (whP δ χ μ) else if i = 7 then Quad.im _ (whP δ χ μ) else 0

theorem pubsC0_01 (χ : Coins frameJ8 K) (μ : Mults) :
    Quad.mk _ (pubsC0 δ χ μ 0) (pubsC0 δ χ μ 1) = cvT δ χ μ := by simp [pubsC0, Quad.mk_re_im]
theorem pubsC0_23 (χ : Coins frameJ8 K) (μ : Mults) :
    Quad.mk _ (pubsC0 δ χ μ 2) (pubsC0 δ χ μ 3) = cxT δ χ μ := by simp [pubsC0, Quad.mk_re_im]
theorem pubsC0_H (χ : Coins frameJ8 K) (μ : Mults) :
    Quad.mk _ (pubsC0 δ χ μ CellHQ.pubHQ) (pubsC0 δ χ μ (CellHQ.pubHQ + 1)) = chT δ χ μ := by
  simp [pubsC0, CellHQ.pubHQ, Quad.mk_re_im]
theorem pubsW0_01 (χ : Coins frameJ8 K) (μ : Mults) :
    Quad.mk _ (pubsW0 δ χ μ 0) (pubsW0 δ χ μ 1) = wxT δ χ μ := by simp [pubsW0, Quad.mk_re_im]
theorem pubsW0_23 (χ : Coins frameJ8 K) (μ : Mults) :
    Quad.mk _ (pubsW0 δ χ μ 2) (pubsW0 δ χ μ 3) = wpT δ χ μ := by simp [pubsW0, Quad.mk_re_im]
theorem pubsW0_X (χ : Coins frameJ8 K) (μ : Mults) :
    Quad.mk _ (pubsW0 δ χ μ WalkHQ.pubXQ) (pubsW0 δ χ μ (WalkHQ.pubXQ + 1)) = whX δ χ := by
  simp [pubsW0, WalkHQ.pubXQ, Quad.mk_re_im]
theorem pubsW0_P (χ : Coins frameJ8 K) (μ : Mults) :
    Quad.mk _ (pubsW0 δ χ μ WalkHQ.pubPQ) (pubsW0 δ χ μ (WalkHQ.pubPQ + 1)) = whP δ χ μ := by
  simp [pubsW0, WalkHQ.pubPQ, Quad.mk_re_im]

/-- **The memory fields of the public data**: `Pb0` with the cell / walk domains replaced. -/
def withMem (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) : PubJ8 p :=
  { Pb0 with
    hC := 1
    nC := 2
    hnC := two_pos
    nodesC := nodesM hdvd 2
    orbitC := orbitM hdvd
    kroots := 1
    hW := 1
    nW := 1
    hnW := one_pos
    nodesW := nodesM hdvd 1
    orbitW := orbitM hdvd }

/-- **The honest cell trace** (242). -/
def trMJ (hdvd : 3 * 2 ^ 1 ∣ p - 1) (χ : Coins frameJ8 K) (μ : Mults) : Fin 242 → (ZMod p)[X] :=
  InhabJ8MemCell.trM0 δ b two_pos (nodesM hdvd 2) (orbitM hdvd) (chalsMJ8 δ χ) (pubsC0 δ χ μ)
    (γV δ χ) (ρV δ χ) (zJ δ χ) μ.mv μ.mx μ.mx1 μ.mh

/-- **The honest J-8 walk trace** (166). -/
def trWJ (hdvd : 3 * 2 ^ 1 ∣ p - 1) (χ : Coins frameJ8 K) (μ : Mults) : Fin 166 → (ZMod p)[X] :=
  trW0 δ b one_pos (nodesM hdvd 1) (orbitM hdvd) (chalsMJ8 δ χ) (pubsW0 δ χ μ)
    (γV δ χ) (ρV δ χ) (zJ δ χ) μ.mL μ.mR

/-! ## The twelve memory conjuncts -/

theorem zJ_chals (χ : Coins frameJ8 K) : Quad.mk _ (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) = zJ δ χ := by
  rw [ProbJ8.chalsMJ8_lo δ χ 2 (by norm_num), ProbJ8.chalsMJ8_lo δ χ 3 (by norm_num)]
  congr 1

theorem nodesC_inj (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) :
    Function.Injective (withMem Pb0 hdvd).nodesC := nodesM_inj hdvd 2 (by norm_num)

theorem p_ge (hdvd : 3 * 2 ^ 1 ∣ p - 1) : 7 ≤ p := by
  have hp := (Fact.out : p.Prime).two_le
  obtain ⟨k, hk⟩ := hdvd
  rcases k with _ | k
  · omega
  · omega

/-- `hsatC`. -/
theorem memC_sat (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) (tr : TrJ8 (ZMod p)) (χ : Coins frameJ8 K)
    (μ : Mults) (pubsC : ℕ → K) (htr : tr.M = trMJ δ b hdvd χ μ) (hpc : pubsC = pubsC0 δ χ μ)
    (hz : zJ δ χ ≠ 0)
    (hv : ∀ j < 2, FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (vKeyOf δ (crow δ (zJ δ χ) μ.mv μ.mx μ.mx1 j)) ≠ 0)
    (hx0 : ∀ j < 2, FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩
      (xKeyOf δ (crow δ (zJ δ χ) μ.mv μ.mx μ.mx1 j) 0) ≠ 0)
    (hx1 : ∀ j < 2, FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩
      (xKeyOf δ (crow δ (zJ δ χ) μ.mv μ.mx μ.mx1 j) 1) ≠ 0)
    (hH : ∀ j < 2, dKW δ (chalsMJ8 δ χ) j ≠ 0) :
    (CellTwinKW.cellChipHQKW δ b (withMem Pb0 hdvd).hnC (withMem Pb0 hdvd).nodesC (withMem Pb0 hdvd).orbitC
      (chalsMJ8 δ χ) pubsC).rap.Satisfies (qM δ b (withMem Pb0 hdvd) tr (chalsMJ8 δ χ) pubsC) := by
  subst hpc
  show (CellTwinKW.cellChipHQKW δ b two_pos (nodesM hdvd 2) (orbitM hdvd) (chalsMJ8 δ χ)
    (pubsC0 δ χ μ)).rap.Satisfies tr.M
  rw [htr]
  exact cellKW0_sat δ b two_pos (nodesM hdvd 2) (orbitM hdvd) (chalsMJ8 δ χ) (pubsC0 δ χ μ)
    (nodesM_inj hdvd 2 (by norm_num)) (nodesM_adj hdvd 2) (γV δ χ) (ρV δ χ) (zJ δ χ) μ.mv μ.mx μ.mx1 μ.mh
    (ProbJ8.chalsOK_J8 δ χ) (zJ_chals δ χ) hz hv hx0 hx1
    (pubsC0_01 δ χ μ).symm (pubsC0_23 δ χ μ).symm hH (by rw [pubsC0_H]; rfl)

/-- `hbindC`. -/
theorem memC_bind (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) (tr : TrJ8 (ZMod p)) (χ : Coins frameJ8 K)
    (μ : Mults) (pubsC : ℕ → K) (htr : tr.M = trMJ δ b hdvd χ μ) (hpc : pubsC = pubsC0 δ χ μ) :
    (CellTwinKW.cellChipHQKW δ b (withMem Pb0 hdvd).hnC (withMem Pb0 hdvd).nodesC (withMem Pb0 hdvd).orbitC
      (chalsMJ8 δ χ) pubsC).BindsPreprocessing (qM δ b (withMem Pb0 hdvd) tr (chalsMJ8 δ χ) pubsC) := by
  subst hpc
  show (CellTwinKW.cellChipHQKW δ b two_pos (nodesM hdvd 2) (orbitM hdvd) (chalsMJ8 δ χ)
    (pubsC0 δ χ μ)).BindsPreprocessing tr.M
  rw [htr]
  exact cellKW0_bind δ b two_pos (nodesM hdvd 2) (orbitM hdvd) (chalsMJ8 δ χ) (pubsC0 δ χ μ) (γV δ χ) (ρV δ χ)
    (zJ δ χ) μ.mv μ.mx μ.mx1 μ.mh

/-- `hinjC`. -/
theorem memC_inj (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) : Function.Injective (withMem Pb0 hdvd).nodesC :=
  nodesM_inj hdvd 2 (by norm_num)

/-- `hadjC`. -/
theorem memC_adj (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) :
    ∀ (i : Fin (withMem Pb0 hdvd).nC) (hi : (i : ℕ) + 1 < (withMem Pb0 hdvd).nC),
      (withMem Pb0 hdvd).nodesC ⟨(i : ℕ) + 1, hi⟩ = (withMem Pb0 hdvd).nodesC i * (withMem Pb0 hdvd).orbitC.ω :=
  nodesM_adj hdvd 2

/-- `hnpC`. -/
theorem memC_np (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) : (withMem Pb0 hdvd).nC < ringChar (ZMod p) := by
  rw [ZMod.ringChar_zmod_n]; show 2 < p; have := p_ge hdvd; omega

/-- `hsatW`. -/
theorem memW_sat (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) (tr : TrJ8 (ZMod p)) (χ : Coins frameJ8 K)
    (μ : Mults) (pubsW : ℕ → K) (htr : tr.W = trWJ δ b hdvd χ μ) (hpw : pubsW = pubsW0 δ χ μ)
    (hx : FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (wxKeyV δ (wrow δ (chalsMJ8 δ χ 0) (zJ δ χ) μ.mL μ.mR)) ≠ 0)
    (hL : FiniteIO.compress (m := 8) ⟨γV δ χ, ρV δ χ⟩ (wrecLV δ (wrow δ (chalsMJ8 δ χ 0) (zJ δ χ) μ.mL μ.mR)) ≠ 0)
    (hR : FiniteIO.compress (m := 8) ⟨γV δ χ, ρV δ χ⟩ (wrecRV δ (wrow δ (chalsMJ8 δ χ 0) (zJ δ χ) μ.mL μ.mR)) ≠ 0)
    (hpX : hden δ (chalsMJ8 δ χ) 5 vX ≠ 0) (hpL : hden δ (chalsMJ8 δ χ) 4 vPL ≠ 0)
    (hpR : hden δ (chalsMJ8 δ χ) 4 vPR ≠ 0) :
    (WalkJ8.walkChipJ8 δ (withMem Pb0 hdvd).kroots b (withMem Pb0 hdvd).hnW (withMem Pb0 hdvd).nodesW
      (withMem Pb0 hdvd).orbitW (chalsMJ8 δ χ) pubsW).rap.Satisfies
        (qW δ b (withMem Pb0 hdvd) tr (chalsMJ8 δ χ) pubsW) := by
  subst hpw
  have h := walkJ8_0 δ b one_pos (nodesM hdvd 1) (orbitM hdvd) (chalsMJ8 δ χ) (pubsW0 δ χ μ)
    (GeneratedField.primeFieldElems_zmod p) (nodesM_inj hdvd 1 (by norm_num)) (nodesM_adj hdvd 1)
    (γV δ χ) (ρV δ χ) (zJ δ χ) μ.mL μ.mR (ProbJ8.chalsOK_J8 δ χ) hx hL hR (pubsW0_01 δ χ μ).symm
    (pubsW0_23 δ χ μ).symm hpX hpL hpR (pubsW0_X δ χ μ) (pubsW0_P δ χ μ)
  show (WalkJ8.walkChipJ8 δ 1 b one_pos (nodesM hdvd 1) (orbitM hdvd) (chalsMJ8 δ χ)
    (pubsW0 δ χ μ)).rap.Satisfies (fun j => tr.W (Fin.cast (WalkJ8.walkChipJ8_width δ 1 b one_pos
      (nodesM hdvd 1) (orbitM hdvd) (chalsMJ8 δ χ) (pubsW0 δ χ μ)) j))
  rw [htr]
  exact h.1

/-- `hbindW`. -/
theorem memW_bind (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) (tr : TrJ8 (ZMod p)) (χ : Coins frameJ8 K)
    (μ : Mults) (pubsW : ℕ → K) (htr : tr.W = trWJ δ b hdvd χ μ) (hpw : pubsW = pubsW0 δ χ μ)
    (hx : FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (wxKeyV δ (wrow δ (chalsMJ8 δ χ 0) (zJ δ χ) μ.mL μ.mR)) ≠ 0)
    (hL : FiniteIO.compress (m := 8) ⟨γV δ χ, ρV δ χ⟩ (wrecLV δ (wrow δ (chalsMJ8 δ χ 0) (zJ δ χ) μ.mL μ.mR)) ≠ 0)
    (hR : FiniteIO.compress (m := 8) ⟨γV δ χ, ρV δ χ⟩ (wrecRV δ (wrow δ (chalsMJ8 δ χ 0) (zJ δ χ) μ.mL μ.mR)) ≠ 0)
    (hpX : hden δ (chalsMJ8 δ χ) 5 vX ≠ 0) (hpL : hden δ (chalsMJ8 δ χ) 4 vPL ≠ 0)
    (hpR : hden δ (chalsMJ8 δ χ) 4 vPR ≠ 0) :
    (WalkJ8.walkChipJ8 δ (withMem Pb0 hdvd).kroots b (withMem Pb0 hdvd).hnW (withMem Pb0 hdvd).nodesW
      (withMem Pb0 hdvd).orbitW (chalsMJ8 δ χ) pubsW).BindsPreprocessing
        (qW δ b (withMem Pb0 hdvd) tr (chalsMJ8 δ χ) pubsW) := by
  subst hpw
  have h := walkJ8_0 δ b one_pos (nodesM hdvd 1) (orbitM hdvd) (chalsMJ8 δ χ) (pubsW0 δ χ μ)
    (GeneratedField.primeFieldElems_zmod p) (nodesM_inj hdvd 1 (by norm_num)) (nodesM_adj hdvd 1)
    (γV δ χ) (ρV δ χ) (zJ δ χ) μ.mL μ.mR (ProbJ8.chalsOK_J8 δ χ) hx hL hR (pubsW0_01 δ χ μ).symm
    (pubsW0_23 δ χ μ).symm hpX hpL hpR (pubsW0_X δ χ μ) (pubsW0_P δ χ μ)
  show (WalkJ8.walkChipJ8 δ 1 b one_pos (nodesM hdvd 1) (orbitM hdvd) (chalsMJ8 δ χ)
    (pubsW0 δ χ μ)).BindsPreprocessing (fun j => tr.W (Fin.cast (WalkJ8.walkChipJ8_width δ 1 b one_pos
      (nodesM hdvd 1) (orbitM hdvd) (chalsMJ8 δ χ) (pubsW0 δ χ μ)) j))
  rw [htr]
  exact h.2

/-- `hinjW`. -/
theorem memW_inj (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) : Function.Injective (withMem Pb0 hdvd).nodesW :=
  nodesM_inj hdvd 1 (by norm_num)

/-- `hadjW`. -/
theorem memW_adj (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) :
    ∀ (i : Fin (withMem Pb0 hdvd).nW) (hi : (i : ℕ) + 1 < (withMem Pb0 hdvd).nW),
      (withMem Pb0 hdvd).nodesW ⟨(i : ℕ) + 1, hi⟩ = (withMem Pb0 hdvd).nodesW i * (withMem Pb0 hdvd).orbitW.ω :=
  nodesM_adj hdvd 1

/-- `hkW`. -/
theorem memW_k (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) : 1 ≤ (withMem Pb0 hdvd).kroots := le_rfl

/-- `hknW`. -/
theorem memW_kn (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) :
    (withMem Pb0 hdvd).kroots ≤ (withMem Pb0 hdvd).nW := le_rfl

/-- `hkpW`. -/
theorem memW_kp (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) :
    (withMem Pb0 hdvd).kroots + (withMem Pb0 hdvd).nW < ringChar (ZMod p) := by
  rw [ZMod.ringChar_zmod_n]; show 1 + 1 < p; have := p_ge hdvd; omega

/-! ## The fingerprint link `hfxC` (internal to the two memory chips) -/

theorem xKey_wx (χ : Coins frameJ8 K) (μ : Mults) :
    xKeyOf δ (crow δ (zJ δ χ) μ.mv μ.mx μ.mx1 0) 0 = wxKeyV δ (wrow δ (chalsMJ8 δ χ 0) (zJ δ χ) μ.mL μ.mR) := by
  funext c; fin_cases c <;> rfl

/-- **`hfxC`** at the honest export multiplicities: `s0` exported once at selector `0` (the walk's dummy root
imports it), nothing else exported. -/
theorem hfxC0 (χ : Coins frameJ8 K) (μ : Mults) (hx0 : μ.mx 0 = 1) (hx1 : μ.mx 1 = 0) (hy0 : μ.mx1 0 = 0)
    (hy1 : μ.mx1 1 = 0) :
    pubsC0 δ χ μ 2 = pubsW0 δ χ μ 0 ∧ pubsC0 δ χ μ 3 = pubsW0 δ χ μ 1 := by
  have h : cxT δ χ μ = wxT δ χ μ := by
    simp only [cxT, xTot, Finset.sum_range_succ, Finset.sum_range_zero, xTerm_crow, hx0, hx1, hy0, hy1,
      wxT, wxTot, ← xKey_wx]
    simp [liftQ]
  simp [pubsC0, pubsW0, h]

/-! ## The handle terminals in closed form (coins `γH′ = gamHQ`, `ρH′ = rhoHQ`) -/

theorem hcoins_J8 (χ : Coins frameJ8 K) :
    hcoins δ (chalsMJ8 δ χ) = (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′) :=
  mcoins_J8 δ χ

/-- **Closed form of the cell handle export** (`pubsC 4/5`, read by `hGx`): `Σ_j mh_j / (ρH′ + RLC^{γH′}(j, 0, 0,
0, aR_j))`, `aR = (0, 1)`. -/
theorem chT_closed (χ : Coins frameJ8 K) (μ : Mults) :
    chT δ χ μ = ∑ j ∈ Finset.range 2, liftQ δ (μ.mh j : ZMod p) *
      (FiniteIO.compress (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′)
        (BalanceQ.liftRec (K := K) (L := 𝕂′) fun c => algebraMap (ZMod p) K (kRow j c)))⁻¹ := by
  simp only [chT, dKW, hcoins_J8]

/-- **Closed form of the walk handle import** (`pubsW 4/5`, read by `hGx`): `(ρH′ + RLC^{γH′}(0,0,0,0,0))⁻¹ =
ρH′⁻¹`, the same key as cell row `0` (`s0`). -/
theorem whX_closed (χ : Coins frameJ8 K) :
    whX δ χ = (FiniteIO.compress (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′)
        (BalanceQ.liftRec (K := K) (L := 𝕂′) fun c : Fin 5 => algebraMap (ZMod p) K (vX c)))⁻¹ := by
  simp only [whX, hden, hcoins_J8]

theorem whX_rho (χ : Coins frameJ8 K) : whX δ χ = (rhoHQ δ (toVSQ χ))⁻¹ := by
  rw [whX_closed]
  simp [FiniteIO.compress, Walk.rlc, BalanceQ.liftRec, vX]

theorem dKW0_eq (chals : ℕ → K) : dKW δ chals 0 = hden δ chals 5 vX := by
  unfold dKW hden
  congr 2
  funext c
  fin_cases c <;> simp [kRow, vX, aRv]

/-- **Closed form of the walk handle provide** (`pubsW 6/7`, read by `hGp`): `mL / (ρH′ + RLC(0, 2, 0, 0)) +
mR / (ρH′ + RLC(0, 3, 0, 0))`; `0` at the honest `mL = mR = 0`. -/
theorem whP_closed (χ : Coins frameJ8 K) (μ : Mults) :
    whP δ χ μ = liftQ δ (μ.mL : ZMod p) * (FiniteIO.compress (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′)
        (BalanceQ.liftRec (K := K) (L := 𝕂′) fun c : Fin 4 => algebraMap (ZMod p) K (vPL c)))⁻¹ +
      liftQ δ (μ.mR : ZMod p) * (FiniteIO.compress (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′)
        (BalanceQ.liftRec (K := K) (L := 𝕂′) fun c : Fin 4 => algebraMap (ZMod p) K (vPR c)))⁻¹ := by
  simp only [whP, hden, hcoins_J8]

theorem whP_zero (χ : Coins frameJ8 K) (μ : Mults) (hL : μ.mL = 0) (hR : μ.mR = 0) : whP δ χ μ = 0 := by
  simp [whP, hL, hR, liftQ]

theorem wpT_zero (χ : Coins frameJ8 K) (μ : Mults) (hL : μ.mL = 0) (hR : μ.mR = 0) : wpT δ χ μ = 0 := by
  simp [wpT, wpTot, hL, hR, liftQ]

/-! ## Simple coin conditions discharging every memory denominator hypothesis

If every record entry lies in the base `𝕂 ⊂ 𝕂′` (true when `χ₃ = 0`: then `z′ ∈ 𝕂`, and every fingerprint of a
noun with leaves `0, 1` is in `𝕂`), the RLC coin has zero `√δ`-part and the pole has a nonzero one, then
`compress ≠ 0` (its `√δ`-part is the pole's). -/

/-- `x ∈ 𝕂 ⊂ 𝕂′`. -/
def IsB (x : 𝕂′) : Prop := ∃ a : K, x = algebraMap K 𝕂′ a

theorem isB_alg (a : K) : IsB δ (algebraMap K 𝕂′ a) := ⟨a, rfl⟩
theorem isB_mk0 (a : K) : IsB δ (Quad.mk _ a 0) := ⟨a, Quad.mk_base _ a⟩
theorem isB_liftQ (g : ZMod p) : IsB δ (liftQ (K := K) δ g) := ⟨algebraMap (ZMod p) K g, rfl⟩
theorem isB_zero : IsB δ (0 : 𝕂′) := ⟨0, (map_zero _).symm⟩
theorem isB_add {x y : 𝕂′} (hx : IsB δ x) (hy : IsB δ y) : IsB δ (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨c, rfl⟩ := hy; exact ⟨a + c, (map_add _ _ _).symm⟩
theorem isB_mul {x y : 𝕂′} (hx : IsB δ x) (hy : IsB δ y) : IsB δ (x * y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨c, rfl⟩ := hy; exact ⟨a * c, (map_mul _ _ _).symm⟩
theorem isB_inv {x : 𝕂′} (hx : IsB δ x) : IsB δ x⁻¹ := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨a⁻¹, (map_inv₀ _ _).symm⟩
theorem isB_pow {x : 𝕂′} (hx : IsB δ x) (n : ℕ) : IsB δ (x ^ n) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨a ^ n, (map_pow _ _ _).symm⟩

theorem compress_ne_zero_B {m : ℕ} (γ : 𝕂′) (hγ : IsB δ γ) (r1 r2 : K) (hr : r2 ≠ 0) (v : Fin m → 𝕂′)
    (hv : ∀ c, IsB δ (v c)) : FiniteIO.compress (⟨γ, Quad.mk _ r1 r2⟩ : IOCoins 𝕂′) v ≠ 0 := by
  have hS : IsB δ (Walk.rlc γ v) := by
    unfold Walk.rlc
    exact Finset.sum_induction _ (IsB δ) (fun _ _ => isB_add δ) (isB_zero δ)
      (fun c _ => isB_mul δ (isB_pow δ hγ _) (hv c))
  obtain ⟨S, hS⟩ := hS
  unfold FiniteIO.compress
  rw [hS, ← Quad.mk_base, Quad.mk_add]
  intro h
  exact hr (by simpa using ((Quad.mk_eq_zero_iff _ _ _).mp h).2)

/-- A fingerprint with all three entries in `𝕂`. -/
def FPB (f : FP 𝕂′) : Prop := IsB δ f.size ∧ IsB δ f.dyck ∧ IsB δ f.leaf

theorem fpb_atom {z v : 𝕂′} (hz : IsB δ z) (hv : IsB δ v) : FPB δ (FP.atomFP z v) := ⟨hz, isB_zero δ, hv⟩

theorem fpb_cons {z : 𝕂′} {a c : FP 𝕂′} (hz : IsB δ z) (ha : FPB δ a) (hc : FPB δ c) :
    FPB δ (FP.cons z a c) := by
  obtain ⟨a1, a2, a3⟩ := ha; obtain ⟨c1, c2, c3⟩ := hc
  refine ⟨isB_mul δ a1 c1, ?_, isB_add δ a3 (isB_mul δ a1 c3)⟩
  exact isB_add δ (isB_add δ (isB_mul δ hz a2) (isB_mul δ (isB_mul δ a1 a1) (isB_inv δ hz)))
    (isB_mul δ (isB_mul δ a1 a1) c2)

theorem crow_B {z : 𝕂′} (hz : IsB δ z) (mv mx mx1 : ℕ → ℕ) (j : ℕ) :
    FPB δ (crow δ z mv mx mx1 j).p ∧ FPB δ (crow δ z mv mx mx1 j).l ∧ FPB δ (crow δ z mv mx mx1 j).r := by
  have hl := fpb_atom δ hz (isB_liftQ δ 0)
  have hr := fpb_atom δ hz (isB_liftQ δ (aRv j))
  exact ⟨fpb_cons δ hz hl hr, hl, hr⟩

/-- **The simple coin conditions**: `z′ = χ₂ ≠ 0` real (`χ₃ = 0`), validity RLC coin real (`χ₆ = 0`) and pole
non-real (`χ₇ ≠ 0`); handle RLC coin real (`χ₁₅ = 0`) and pole non-real (`χ₁₆ ≠ 0`). -/
structure SimpleCoins (χ : Coins frameJ8 K) : Prop where
  z_re : χ c2 ≠ 0
  z_im : χ c3 = 0
  g_im : χ c6 = 0
  r_im : χ c7 ≠ 0
  gH_im : toVSQ χ cGamHi = 0
  rH_im : toVSQ χ cRhoHi ≠ 0

section Simple

theorem sc_z {χ : Coins frameJ8 K} (hs : SimpleCoins χ) (μ : Mults) : zJ δ χ ≠ 0 := by
  intro h; exact hs.z_re ((Quad.mk_eq_zero_iff _ _ _).mp h).1

theorem sc_zB {χ : Coins frameJ8 K} (hs : SimpleCoins χ) (μ : Mults) : IsB δ (zJ δ χ) := by rw [zJ, hs.z_im]; exact isB_mk0 δ _

theorem sc_gB {χ : Coins frameJ8 K} (hs : SimpleCoins χ) (μ : Mults) : IsB δ (γV δ χ) := by rw [γV, hs.g_im]; exact isB_mk0 δ _

theorem sc_v {χ : Coins frameJ8 K} (hs : SimpleCoins χ) (μ : Mults) (j : ℕ) : FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩
    (vKeyOf δ (crow δ (zJ δ χ) μ.mv μ.mx μ.mx1 j)) ≠ 0 := by
  obtain ⟨hp, -, -⟩ := crow_B δ (sc_zB δ hs μ) μ.mv μ.mx μ.mx1 j
  refine compress_ne_zero_B δ _ (sc_gB δ hs μ) _ _ hs.r_im _ fun c => ?_
  fin_cases c
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2
  · exact ⟨algebraMap (ZMod p) K 1, by simp [vKeyOf, crow, Quad.mk_base]⟩
  · exact isB_liftQ δ _

theorem sc_x {χ : Coins frameJ8 K} (hs : SimpleCoins χ) (μ : Mults) (j : ℕ) (s : ZMod p) : FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩
    (xKeyOf δ (crow δ (zJ δ χ) μ.mv μ.mx μ.mx1 j) s) ≠ 0 := by
  obtain ⟨hp, hl, hr⟩ := crow_B δ (sc_zB δ hs μ) μ.mv μ.mx μ.mx1 j
  refine compress_ne_zero_B δ _ (sc_gB δ hs μ) _ _ hs.r_im _ fun c => ?_
  fin_cases c
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2
  · exact hl.1
  · exact hl.2.1
  · exact hl.2.2
  · exact hr.1
  · exact hr.2.1
  · exact hr.2.2
  · exact isB_liftQ δ _
  · exact isB_liftQ δ _

theorem sc_w {χ : Coins frameJ8 K} (hs : SimpleCoins χ) (μ : Mults) : FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩
      (wxKeyV δ (wrow δ (chalsMJ8 δ χ 0) (zJ δ χ) μ.mL μ.mR)) ≠ 0 ∧
    FiniteIO.compress (m := 8) ⟨γV δ χ, ρV δ χ⟩ (wrecLV δ (wrow δ (chalsMJ8 δ χ 0) (zJ δ χ) μ.mL μ.mR)) ≠ 0 ∧
    FiniteIO.compress (m := 8) ⟨γV δ χ, ρV δ χ⟩ (wrecRV δ (wrow δ (chalsMJ8 δ χ 0) (zJ δ χ) μ.mL μ.mR)) ≠ 0 := by
  obtain ⟨hp, hl, hr⟩ := crow_B δ (sc_zB δ hs μ) μ.mv μ.mx μ.mx1 0
  refine ⟨?_, ?_, ?_⟩
  · rw [← xKey_wx]; exact sc_x δ hs μ 0 0
  · refine compress_ne_zero_B δ _ (sc_gB δ hs μ) _ _ hs.r_im _ fun c => ?_
    fin_cases c
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2
    · exact hl.1
    · exact hl.2.1
    · exact hl.2.2
    · exact isB_liftQ δ _
    · exact isB_liftQ δ _
  · refine compress_ne_zero_B δ _ (sc_gB δ hs μ) _ _ hs.r_im _ fun c => ?_
    fin_cases c
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2
    · exact hr.1
    · exact hr.2.1
    · exact hr.2.2
    · exact isB_liftQ δ _
    · exact isB_liftQ δ _

theorem sc_h {χ : Coins frameJ8 K} (hs : SimpleCoins χ) (μ : Mults) (m : ℕ) (v : ℕ → ZMod p) : hden δ (chalsMJ8 δ χ) m v ≠ 0 := by
  unfold hden
  rw [hcoins_J8]
  have hg : gamHQ δ (toVSQ χ) = Quad.mk _ (toVSQ χ ⟨11, by decide⟩) 0 := by rw [gamHQ, hs.gH_im]
  rw [hg]
  exact compress_ne_zero_B δ _ (isB_mk0 δ _) _ _ hs.rH_im _ fun c => isB_alg δ _

theorem sc_dKW {χ : Coins frameJ8 K} (hs : SimpleCoins χ) (μ : Mults) (j : ℕ) : dKW δ (chalsMJ8 δ χ) j ≠ 0 := by
  unfold dKW
  rw [hcoins_J8]
  have hg : gamHQ δ (toVSQ χ) = Quad.mk _ (toVSQ χ ⟨11, by decide⟩) 0 := by rw [gamHQ, hs.gH_im]
  rw [hg]
  exact compress_ne_zero_B δ _ (isB_mk0 δ _) _ _ hs.rH_im _ fun c => isB_alg δ _

/-- **`hsatC` under the simple coin conditions** (every denominator discharged). -/
theorem memC_sat_simple {χ : Coins frameJ8 K} (hs : SimpleCoins χ) (μ : Mults) (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) (tr : TrJ8 (ZMod p)) (pubsC : ℕ → K)
    (htr : tr.M = trMJ δ b hdvd χ μ) (hpc : pubsC = pubsC0 δ χ μ) :
    (CellTwinKW.cellChipHQKW δ b (withMem Pb0 hdvd).hnC (withMem Pb0 hdvd).nodesC (withMem Pb0 hdvd).orbitC
      (chalsMJ8 δ χ) pubsC).rap.Satisfies (qM δ b (withMem Pb0 hdvd) tr (chalsMJ8 δ χ) pubsC) :=
  memC_sat δ b Pb0 hdvd tr χ μ pubsC htr hpc (sc_z δ hs μ) (fun j _ => sc_v δ hs μ j)
    (fun j _ => sc_x δ hs μ j 0) (fun j _ => sc_x δ hs μ j 1) (fun j _ => sc_dKW δ hs μ j)

/-- **`hsatW` under the simple coin conditions.** -/
theorem memW_sat_simple {χ : Coins frameJ8 K} (hs : SimpleCoins χ) (μ : Mults) (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) (tr : TrJ8 (ZMod p)) (pubsW : ℕ → K)
    (htr : tr.W = trWJ δ b hdvd χ μ) (hpw : pubsW = pubsW0 δ χ μ) :
    (WalkJ8.walkChipJ8 δ (withMem Pb0 hdvd).kroots b (withMem Pb0 hdvd).hnW (withMem Pb0 hdvd).nodesW
      (withMem Pb0 hdvd).orbitW (chalsMJ8 δ χ) pubsW).rap.Satisfies
        (qW δ b (withMem Pb0 hdvd) tr (chalsMJ8 δ χ) pubsW) :=
  memW_sat δ b Pb0 hdvd tr χ μ pubsW htr hpw (sc_w δ hs μ).1 (sc_w δ hs μ).2.1 (sc_w δ hs μ).2.2
    (sc_h δ hs μ _ _) (sc_h δ hs μ _ _) (sc_h δ hs μ _ _)

/-- **`hbindW` under the simple coin conditions.** -/
theorem memW_bind_simple {χ : Coins frameJ8 K} (hs : SimpleCoins χ) (μ : Mults) (Pb0 : PubJ8 p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) (tr : TrJ8 (ZMod p)) (pubsW : ℕ → K)
    (htr : tr.W = trWJ δ b hdvd χ μ) (hpw : pubsW = pubsW0 δ χ μ) :
    (WalkJ8.walkChipJ8 δ (withMem Pb0 hdvd).kroots b (withMem Pb0 hdvd).hnW (withMem Pb0 hdvd).nodesW
      (withMem Pb0 hdvd).orbitW (chalsMJ8 δ χ) pubsW).BindsPreprocessing
        (qW δ b (withMem Pb0 hdvd) tr (chalsMJ8 δ χ) pubsW) :=
  memW_bind δ b Pb0 hdvd tr χ μ pubsW htr hpw (sc_w δ hs μ).1 (sc_w δ hs μ).2.1 (sc_w δ hs μ).2.2
    (sc_h δ hs μ _ _) (sc_h δ hs μ _ _) (sc_h δ hs μ _ _)

end Simple

/-! ## Closed forms of the terminals -/

section Closed
variable [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- The cell noun of row `j`: row `1` is `f0`, every other row `s0`. -/
def cnoun (j : ℕ) : Noun := if j = 1 then InhabJ8Base.f0 else InhabJ8Base.s0

theorem one_lt_atomsP : 1 < Nock.Atoms.p := by
  rw [show Nock.Atoms.p = Nock.Field.p from rfl, Nock.Field.p_eq]; norm_num

theorem leafVal_zero (y : 𝕂′) : Nock.Atoms.leafVal y 0 = liftQ δ 0 := by
  rw [Nock.Atoms.leafVal_small y (by have := one_lt_atomsP; omega)]; simp [liftQ]

theorem leafVal_one (y : 𝕂′) : Nock.Atoms.leafVal y 1 = liftQ δ 1 := by
  rw [Nock.Atoms.leafVal_small y one_lt_atomsP]; simp [liftQ]

/-- The cell rows' fingerprints ARE the verifier's encoder `E(z, y)` of the row's noun. -/
theorem crow_p (χ : Coins frameJ8 K) (mv mx mx1 : ℕ → ℕ) (j : ℕ) (hj : j < 2) :
    (crow δ (zJ δ χ) mv mx mx1 j).p = encJ8 δ χ (cnoun j) := by
  interval_cases j <;>
    simp [crow, cnoun, InhabJ8Base.s0, InhabJ8Base.f0, EncZYJ8.encZY, aRv, leafVal_zero, leafVal_one]

/-- **The validity key of row `j` is the claim record** `claimVec (E(cnoun j)) j 0 1` (rank `1 = 0·2^62 + 1`). -/
theorem vKey_claim (χ : Coins frameJ8 K) (mv mx mx1 : ℕ → ℕ) (j : ℕ) (hj : j < 2) :
    vKeyOf δ (crow δ (zJ δ χ) mv mx mx1 j) =
      ClaimVS.claimVec δ (encJ8 δ χ (cnoun j)) ((j : ℕ) : ZMod p) ((0 : ℕ) : ZMod p) ((1 : ℕ) : ZMod p) := by
  rw [← crow_p δ χ mv mx mx1 j hj]
  funext c
  fin_cases c <;> simp [vKeyOf, ClaimVS.claimVec, crow, liftQ, Quad.mk_base]

/-- **Closed form of the cell validity terminal** (`pubsC 0/1`): `Σ_j mv_j / compress(γ′, ρ′)(claimVec …)`. -/
theorem cvT_closed (χ : Coins frameJ8 K) (μ : Mults) :
    cvT δ χ μ = ∑ j ∈ Finset.range 2, liftQ δ (μ.mv j : ZMod p) *
      (FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩
        (ClaimVS.claimVec δ (encJ8 δ χ (cnoun j)) ((j : ℕ) : ZMod p) ((0 : ℕ) : ZMod p) ((1 : ℕ) : ZMod p)))⁻¹ := by
  unfold cvT vTot
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [vTerm_crow, vKey_claim δ χ μ.mv μ.mx μ.mx1 j (Finset.mem_range.mp hj)]

/-- **The `hsumC'` identity at the honest validity multiplicities `(2, 1)`**: the verifier's claim records of
`c0` (subject `s0`, formula `f0`, result `s0`, serials from `H0`; no pins) sum to the cell validity terminal.
So `hsumC'` holds iff the atom table's `g5` terminal `(pubsA pubMB, pubsA (pubMB+1))` is `0`. -/
theorem claimSum0 (χ : Coins frameJ8 K) (μ : Mults) (m : ClaimMsgVS)
    (hm : ∀ k, (m k).1 = (H0 p (claimNoun InhabJ8Base.c0 k)).2) (hmv0 : μ.mv 0 = 2) (hmv1 : μ.mv 1 = 1)
    (Pb : PubJ8 p) (hreg : Pb.regs = []) :
    ((AcceptsJ8P.claimRecsJ8 δ χ InhabJ8Base.c0 m ++ AcceptsJ8P.pinRecsJ8 δ Pb χ).map fun r =>
      (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
      Quad.mk _ (pubsC0 δ χ μ 0) (pubsC0 δ χ μ 1) := by
  rw [pubsC0_01, cvT_closed]
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  simp only [claimNoun, InhabJ8Base.c0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.vecHead, Matrix.vecTail, H0_s0, H0_f0] at h0 h1 h2
  simp [AcceptsJ8P.pinRecsJ8, hreg, AcceptsJ8P.claimRecsJ8, AcceptsJ8P.claimCells, List.finRange, claimNoun,
    InhabJ8Base.c0, InhabJ8Base.s0, InhabJ8Base.f0, isCellN, AcceptsJ8P.rkC, Noun.internal, h0, h1, h2, hmv0,
    hmv1, Finset.sum_range_succ, cnoun, liftQ, List.filter, H0]
  ring

end Closed

end Mem

end

end Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemMain
