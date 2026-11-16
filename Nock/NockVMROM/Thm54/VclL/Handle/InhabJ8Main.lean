/-
  Nock/NockVMROM/Thm54/VclL/Handle/InhabJ8Main.lean

* The public data `PbJ` (compute `1` row, cell `2` rows `s0 f0`, J-8 walk `1` dummy root, J `0` rows, atom table
    `1` pad row, atom walk absent), the honest traces `trJ0 χ` (compute `InhabJ8Comp.trC0`, cell `InhabJ8MemMain.trMJ`,
    walk `trWJ`, atom `InhabJ8Atom.trA0`; J and atom-walk columns `0`), the honest message `MJ0 χ` (claim serials from
    the handle map `H0`, `ρ` / `ρS` the compute accumulators, every chip's publics), the multiplicities `μ0`
    (validity `(2, 1)`, fingerprint export `(1, 0)`, handle export `(1, 1)`: the walk root and the compute row).
  * The coin `χ0`: every `√δ`-coordinate `0` except the two LogUp poles' (`χ₇ = χ₁₆ = 1`), every other coin `1`.
    Every honest denominator is then `ρ + (an element of 𝕂)` with `ρ ∉ 𝕂`, hence nonzero (`pole_ne`, `IsB`).
  * The cross-chip balances: `hGx` (compute consumes `f0`'s handle once, the walk root `s0`'s once; the cell table
    provides each once), `hGp` (no path read, `0 = 0`), `hGS` (no service, `0 = 0`), `hsumC'` (`claimSum0`),
    `hbalA'`, `hvalA0`, `hfxC` (`hfxC0`), `hfxA` (`0 = 0`).
  * **`inhabitant`**: `AcceptsJ8V δ b (PbJ hdvd Rt) R0 c0 χ0 (MJ0 δ b χ0) (trJ0 δ b hdvd Rt χ0) rJ0 0`, under
    `B ≤ p` and `3 · 2 ∣ p − 1`; **`inhabitant_goldilocks`**: at `p = Nock.Atoms.p` (both discharged), as
    `∃ Pb χ M tr r g, AcceptsJ8V … ∧ Pb.krootsV = 0 ∧ Pb.nJ = 0 ∧ HoldsN c0`.
  * NOT claimed: that the honest trace map `χ ↦ trJ0 χ` is staged (`StJ8`); the inhabitant is at ONE coin.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Static
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Comp
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemMain
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Atom

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Main

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Static
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemDom
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemMain
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Atom
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)

noncomputable section

/-! ## 1. The public data, the multiplicities, the coin -/

section Data
variable {p : ℕ} [Fact p.Prime]

/-- The public data before the memory fields (`withMem` sets them): compute `1` row, J `0` rows, atom table `1`
row, atom walk absent (`krootsV = 0`, one placeholder row: `PubJ8.hnV`), empty registry. -/
def PbBase (hdvd : 3 * 2 ^ 1 ∣ p - 1) (Rt : ℕ → Nock.Jet.Autogen.Tpl) : PubJ8 p where
  h := 1
  n := 1
  hn := one_pos
  nodes := fun _ => 1
  orbit := orbitM hdvd
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
  orbitW := orbitM hdvd
  hJ := 1
  nJ := 0
  nodesJ := Fin.elim0
  orbitJ := orbitM hdvd
  lay := Fin.elim0
  hA := 1
  nA := 1
  hnA := one_pos
  nodesA := fun _ => 1
  orbitA := orbitM hdvd
  krootsV := 0
  hV := 1
  nV := 1
  hnV := one_pos
  nodesV := fun _ => 1
  orbitV := orbitM hdvd
  Rt := Rt
  regs := []
  ids := []
  idx := fun _ => 0
  rk := fun _ => (0, 0)

/-- **The public data of the inhabitant.** -/
def PbJ (hdvd : 3 * 2 ^ 1 ∣ p - 1) (Rt : ℕ → Nock.Jet.Autogen.Tpl) : PubJ8 p := withMem (PbBase hdvd Rt) hdvd

/-- **The honest multiplicities**: validity `(2, 1)` (the claim's subject and result are `s0`, its formula `f0`),
fingerprint export `s0` once at selector `0` (the walk root), handle export `(1, 1)` (`s0` by the walk root, `f0` by
the compute row), no path provide. -/
def μ0 : Mults where
  mv := fun j => if j = 0 then 2 else 1
  mx := fun j => if j = 0 then 1 else 0
  mx1 := fun _ => 0
  mh := fun _ => 1
  mL := 0
  mR := 0

/-- The row counts (generous; only `BudJ8` reads them). -/
def rJ0 : RowsJ8 where
  N := 10
  D := 10
  W := 10
  Λ := 10
  A := 10
  AW := 10
  J := 10
  mb := 10
  inc := 10
  calls := 10
  heads := 10
  blocks := 10
  rd := 10
  leaves := 10
  maxlen := 10

end Data

section Coin
variable {K : Type} [Field K]

/-- **The coin**: `0` at the `√δ`-coordinates `χ₃ χ₆ χ₁₅ χ₁₈` (of `z′`, `γ′`, `γH′`, `y`), `1` everywhere else (in
particular the poles' `√δ`-coordinates `χ₇ = χ₁₆ = 1`). -/
def χ0 : Coins frameJ8 K := fun i =>
  if (i : ℕ) = 3 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 15 ∨ (i : ℕ) = 18 then 0 else 1

theorem χ0_val (i : Fin frameJ8.n) :
    (χ0 : Coins frameJ8 K) i = if (i : ℕ) = 3 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 15 ∨ (i : ℕ) = 18 then 0 else 1 := rfl

end Coin

/-! ## 2. Traces and message -/

section Tr
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The honest traces** at coin `χ`. -/
def trJ0 (hdvd : 3 * 2 ^ 1 ∣ p - 1) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (χ : Coins frameJ8 K) : TrJ8 (ZMod p) where
  C := InhabJ8Comp.trC0 δ b (H0 p) χ (PbJ hdvd Rt).nodes 123
  M := trMJ δ b hdvd χ μ0
  W := trWJ δ b hdvd χ μ0
  J := fun _ => 0
  A := trA0 δ b (PbJ hdvd Rt).hnA (PbJ hdvd Rt).nodesA (PbJ hdvd Rt).orbitA χ
  V := fun _ => 0

/-- **The honest message** at coin `χ`. -/
def MJ0 (χ : Coins frameJ8 K) : MsgJ8' p K δ where
  m := InhabJ8Comp.mC0 (H0 p)
  ρ := InhabJ8Comp.ρC0 δ b (H0 p) χ
  ρS := InhabJ8Comp.ρSC0 δ b (H0 p) χ
  pubsC := pubsC0 δ χ μ0
  pubsW := pubsW0 δ χ μ0
  pubsJ := fun _ => 0
  pubsA := pubsA0
  pubsV := fun _ => 0

/-! ## 3. Nonvanishing at `χ0` -/

theorem pole_ne (a r : K) (hr : r ≠ 0) (x : 𝕂′) (hx : IsB δ x) : Quad.mk _ a r + x ≠ 0 := by
  obtain ⟨c, rfl⟩ := hx
  rw [← Quad.mk_base, Quad.mk_add]
  intro h
  exact hr (by simpa using ((Quad.mk_eq_zero_iff _ _ _).mp h).2)

theorem isB_two : IsB δ (2 : 𝕂′) := ⟨2, (map_ofNat _ 2).symm⟩
theorem isB_four : IsB δ (4 : 𝕂′) := ⟨4, (map_ofNat _ 4).symm⟩

theorem z0 : zA δ (χ0 : Coins frameJ8 K) = Quad.mk _ 1 0 := by simp [zA, χ0, c2, c3]
theorem γ0 : γA δ (χ0 : Coins frameJ8 K) = Quad.mk _ 1 0 := by simp [γA, χ0, c4, c6]
theorem ρ0 : ρA δ (χ0 : Coins frameJ8 K) = Quad.mk _ 1 1 := by simp [ρA, χ0, c5, c7]
theorem y0 : yA δ (χ0 : Coins frameJ8 K) = Quad.mk _ 1 0 := by simp [yA, χ0, cY1, cY2]
theorem γH0 : gamHQ δ (toVSQ (χ0 : Coins frameJ8 K)) = Quad.mk _ 1 0 := by
  simp [gamHQ, toVSQ, χ0, cGamHi]
theorem ρH0 : rhoHQ δ (toVSQ (χ0 : Coins frameJ8 K)) = Quad.mk _ 1 1 := by
  simp [rhoHQ, toVSQ, χ0, cRhoHi]

theorem isB_m10 : IsB δ (Quad.mk (algebraMap (ZMod p) K δ) (1 : K) 0) := isB_mk0 δ 1

/-- Closes `IsB` goals built from `mk 1 0`, numerals, `+`, `*`, `^`. -/
macro "isb" : tactic => `(tactic| repeat (first
  | exact isB_m10 _ | exact isB_two _ | exact isB_four _
  | apply InhabJ8MemMain.isB_add | apply InhabJ8MemMain.isB_mul | apply InhabJ8MemMain.isB_pow))

theorem coinsA0_hV : ρA δ (χ0 : Coins frameJ8 K) + yA δ (χ0 : Coins frameJ8 K) ^ 2 + γA δ (χ0 : Coins frameJ8 K) * yA δ (χ0 : Coins frameJ8 K) + γA δ (χ0 : Coins frameJ8 K) ^ 2 * yA δ (χ0 : Coins frameJ8 K) + γA δ (χ0 : Coins frameJ8 K) ^ 3 ≠ 0 := by
  rw [γ0, ρ0, y0]
  simp only [add_assoc]
  exact pole_ne δ _ _ one_ne_zero _ (by isb)

theorem coinsA0_hX0 : ρA δ (χ0 : Coins frameJ8 K) + yA δ (χ0 : Coins frameJ8 K) ^ 2 + γA δ (χ0 : Coins frameJ8 K) * yA δ (χ0 : Coins frameJ8 K) + γA δ (χ0 : Coins frameJ8 K) ^ 2 * yA δ (χ0 : Coins frameJ8 K) + γA δ (χ0 : Coins frameJ8 K) ^ 3 * yA δ (χ0 : Coins frameJ8 K) +
    γA δ (χ0 : Coins frameJ8 K) ^ 6 * yA δ (χ0 : Coins frameJ8 K) + γA δ (χ0 : Coins frameJ8 K) ^ 8 ≠ 0 := by
  rw [γ0, ρ0, y0]
  simp only [add_assoc]
  exact pole_ne δ _ _ one_ne_zero _ (by isb)

theorem coinsA0_hX1 : ρA δ (χ0 : Coins frameJ8 K) + yA δ (χ0 : Coins frameJ8 K) ^ 2 + γA δ (χ0 : Coins frameJ8 K) * yA δ (χ0 : Coins frameJ8 K) + γA δ (χ0 : Coins frameJ8 K) ^ 2 * yA δ (χ0 : Coins frameJ8 K) + γA δ (χ0 : Coins frameJ8 K) ^ 3 * yA δ (χ0 : Coins frameJ8 K) +
    γA δ (χ0 : Coins frameJ8 K) ^ 6 * yA δ (χ0 : Coins frameJ8 K) + γA δ (χ0 : Coins frameJ8 K) ^ 8 + γA δ (χ0 : Coins frameJ8 K) ^ 10 ≠ 0 := by
  rw [γ0, ρ0, y0]
  simp only [add_assoc]
  exact pole_ne δ _ _ one_ne_zero _ (by isb)

theorem coinsA0_hH : rhoHQ δ (toVSQ (χ0 : Coins frameJ8 K)) + gamHQ δ (toVSQ (χ0 : Coins frameJ8 K)) ^ 4 ≠ 0 := by
  rw [γH0, ρH0]
  exact pole_ne δ _ _ one_ne_zero _ (by isb)

theorem coinsA0_hMB : ρA δ (χ0 : Coins frameJ8 K) + zA δ (χ0 : Coins frameJ8 K) + γA δ (χ0 : Coins frameJ8 K) ^ 2 * yA δ (χ0 : Coins frameJ8 K) ≠ 0 := by
  rw [γ0, ρ0, y0, z0]
  simp only [add_assoc]
  exact pole_ne δ _ _ one_ne_zero _ (by isb)

theorem coinsA0_hMI : rhoHQ δ (toVSQ (χ0 : Coins frameJ8 K)) + 2 + 2 * gamHQ δ (toVSQ (χ0 : Coins frameJ8 K)) ^ 2 + 4 * gamHQ δ (toVSQ (χ0 : Coins frameJ8 K)) ^ 4 ≠ 0 := by
  rw [γH0, ρH0]
  simp only [add_assoc]
  exact pole_ne δ _ _ one_ne_zero _ (by isb)

theorem coinsA0 : CoinsA δ (χ0 : Coins frameJ8 K) where
  hy := by rw [y0]; intro h; exact one_ne_zero ((Quad.mk_eq_zero_iff _ _ _).mp h).1
  hV := coinsA0_hV δ
  hX0 := coinsA0_hX0 δ
  hX1 := coinsA0_hX1 δ
  hH := coinsA0_hH δ
  hMB := coinsA0_hMB δ
  hC := by rw [ρH0]; intro h; exact one_ne_zero ((Quad.mk_eq_zero_iff _ _ _).mp h).2
  hMI := coinsA0_hMI δ

theorem simple0 : SimpleCoins (χ0 : Coins frameJ8 K) where
  z_re := by simp [χ0, c2]
  z_im := by simp [χ0, c3]
  g_im := by simp [χ0, c6]
  r_im := by simp [χ0, c7]
  gH_im := by simp [χ0, toVSQ, cGamHi]
  rH_im := by simp [χ0, toVSQ, cRhoHi]

theorem hα0 : (χ0 : Coins frameJ8 K) ⟨13, by decide⟩ ≠ 0 := by simp [χ0]

theorem hden0 : compress (⟨gamHQ δ (toVSQ (χ0 : Coins frameJ8 K)), rhoHQ δ (toVSQ (χ0 : Coins frameJ8 K))⟩ : IOCoins 𝕂′)
    (liftRec (L := 𝕂′) (InhabJ8Comp.recF0 (p := p) (K := K) (H0 p))) ≠ 0 := by
  rw [γH0, ρH0]
  exact compress_ne_zero_B δ _ (isB_m10 δ) 1 1 one_ne_zero _ (fun c => isB_alg δ _)

/-! ## 4. The cross-chip balances -/

theorem recF0_kRow : InhabJ8Comp.recF0 (p := p) (K := K) (H0 p) =
    fun c => algebraMap (ZMod p) K (InhabJ8MemCell.kRow (F := ZMod p) 1 c) := by
  funext c
  fin_cases c <;> simp [InhabJ8Comp.recF0, InhabJ8MemCell.kRow, InhabJ8MemCell.aRv, H0_f0]

theorem vX_kRow : (fun c : Fin 5 => algebraMap (ZMod p) K (InhabJ8MemWalk.vX (F := ZMod p) c)) =
    fun c => algebraMap (ZMod p) K (InhabJ8MemCell.kRow (F := ZMod p) 0 c) := by
  funext c
  fin_cases c <;> simp [InhabJ8MemWalk.vX, InhabJ8MemCell.kRow, InhabJ8MemCell.aRv]

theorem hGx0 (hp : 2 ≤ p) (χ : Coins frameJ8 K) :
    InhabJ8Comp.ρC0 δ b (H0 p) χ 3 + (Quad.mk _ (pubsW0 δ χ μ0 WalkHQ.pubXQ) (pubsW0 δ χ μ0 (WalkHQ.pubXQ + 1)) +
      Quad.mk (algebraMap (ZMod p) K δ) (0 : K) 0) =
    Quad.mk _ (pubsC0 δ χ μ0 CellHQ.pubHQ) (pubsC0 δ χ μ0 (CellHQ.pubHQ + 1)) := by
  rw [InhabJ8Comp.ρC0_3 δ b (H0 p) (hdlOK_H0 p) hp χ, pubsW0_X, pubsC0_H, whX_closed, chT_closed,
    Quad.mk_zero', add_zero, recF0_kRow, vX_kRow]
  simp [Finset.sum_range_succ, μ0, Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ]
  ring

theorem hGp0 (χ : Coins frameJ8 K) :
    InhabJ8Comp.ρC0 δ b (H0 p) χ 4 = Quad.mk _ (pubsW0 δ χ μ0 WalkHQ.pubPQ) (pubsW0 δ χ μ0 (WalkHQ.pubPQ + 1)) := by
  rw [InhabJ8Comp.ρC0_4, pubsW0_P, whP_zero δ χ μ0 rfl rfl]

end Tr

/-! ## 5. THE INHABITANT -/

section Main
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

theorem p_ge_B {hB : Nock.Atoms.B ≤ p} : 2 ^ 32 ≤ p := hB

/-- **THE INHABITANT**: the honest run of `*[[0 0] [0 1]] = [0 0]` (no jets, no big atoms) is ACCEPTED by
`AcceptsJ8V` at the coin `χ0`, the J chip and the atom walk absent, the atom table one inert pad row. -/
theorem inhabitant (hB : Nock.Atoms.B ≤ p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    AcceptsJ8V δ b (PbJ hdvd Rt) R0 c0 χ0 (MJ0 δ b χ0) (trJ0 δ b hdvd Rt χ0) rJ0 0 := by
  have hBp : 2 ^ 32 ≤ p := hB
  have hp2 : 2 ≤ p := le_trans (by norm_num) hBp
  have hs := simple0 (K := K)
  have hcA := coinsA0 (K := K) δ
  exact
  { hsatX := InhabJ8Comp.hsatX_c0_qX δ b (H0 p) (hdlOK_H0 p) hB χ0 (hα0 (K := K)) (hden0 δ) (PbJ hdvd Rt)
      (trJ0 δ b hdvd Rt χ0) rfl rfl
    hinjX := fun a c _ => Fin.ext (by
      have h1 : (a : ℕ) < 1 := a.isLt
      have h2 : (c : ℕ) < 1 := c.isLt
      omega)
    hadjX := fun i hi => absurd (show (i : ℕ) + 1 < 1 from hi) (by omega)
    hsatC := memC_sat_simple δ b hs μ0 (PbBase hdvd Rt) hdvd _ _ rfl rfl
    hbindC := memC_bind δ b (PbBase hdvd Rt) hdvd _ χ0 μ0 _ rfl rfl
    hinjC := memC_inj (PbBase hdvd Rt) hdvd
    hadjC := memC_adj (PbBase hdvd Rt) hdvd
    hnpC := memC_np (PbBase hdvd Rt) hdvd
    hsatW := memW_sat_simple δ b hs μ0 (PbBase hdvd Rt) hdvd _ _ rfl rfl
    hbindW := memW_bind_simple δ b hs μ0 (PbBase hdvd Rt) hdvd _ _ rfl rfl
    hinjW := memW_inj (PbBase hdvd Rt) hdvd
    hadjW := memW_adj (PbBase hdvd Rt) hdvd
    hkW := memW_k (PbBase hdvd Rt) hdvd
    hknW := memW_kn (PbBase hdvd Rt) hdvd
    hkpW := memW_kp (PbBase hdvd Rt) hdvd
    hJk := jchip_absent δ b _ _ _ _ _ _ rfl ⟨rfl, rfl, rfl, rfl⟩
    hsatA := hsatA_A0 (PbJ hdvd Rt) rfl _ χ0 rfl hcA _ rfl
    hbindA := hbindA_A0 (PbJ hdvd Rt) _ χ0 rfl _ rfl
    hinjA := hinjA_A0 (PbJ hdvd Rt) rfl
    hadjA := hadjA_A0 (PbJ hdvd Rt) rfl
    hnpA := hnpA_A0 (PbJ hdvd Rt) rfl
    hVk := Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    hGx := hGx0 δ b hp2 χ0
    hGp := hGp0 δ b χ0
    hGS := by
      show InhabJ8Comp.ρSC0 δ b (H0 p) χ0 + _ + _ = _
      rw [InhabJ8Comp.ρSC0_eq]
      simp [PbJ, PbBase, withMem, MJ0, Nock.Jet.PinJ8.pinCons, pubsA0, Quad.mk_zero']
    hlay := hlay0 (PbJ hdvd Rt) rfl rfl rfl
    hsmall := hsmall0 (PbJ hdvd Rt) rfl rfl
    huniq := huniq0 (PbJ hdvd Rt) rfl rfl
    hTpl := regs_vacuous (PbJ hdvd Rt) rfl
    hnd := hnd0 (PbJ hdvd Rt) rfl
    hidx := regs_vacuous (PbJ hdvd Rt) rfl
    hrk := regs_vacuous (PbJ hdvd Rt) rfl
    hlt := regs_vacuous (PbJ hdvd Rt) rfl
    hsumC' := by
      rw [show (MJ0 δ b χ0).m = InhabJ8Comp.mC0 (H0 p) from rfl, show (MJ0 δ b χ0).pubsC = pubsC0 δ χ0 μ0 from rfl,
        show (MJ0 δ b (K := K) χ0).pubsA = pubsA0 from rfl, claimSum0 δ χ0 μ0 (InhabJ8Comp.mC0 (H0 p)) (fun k => rfl) rfl rfl (PbJ hdvd Rt) rfl]
      simp [pubsA0, Quad.mk_zero']
    hbalA' := by simp [MJ0, pubsA0, Quad.mk_zero']
    hvalA0 := hvalA0_A0
    hfxC := hfxC0 δ χ0 μ0 rfl rfl rfl rfl
    hfxA := ⟨rfl, rfl⟩
    hclA := hclA0 p
    hclI := fun k _ => by
      show (H0 p (claimNoun c0 k)).2 < p
      rw [claimNoun_c0]
      split_ifs
      · rw [H0_f0]; omega
      · rw [H0_s0]; omega
    hclR := hclR0 p (by omega)
    hcen := hcen0 (PbJ hdvd Rt) rfl hp2
    hlenC := by show 3 + 0 + 2 * 2 < p; omega
    hlenA := by show 1 + 1 < p; omega
    hcellF := hcellF0
    hnA62 := by show 1 ≤ 2 ^ 62; norm_num
    hbud := hbud0 (PbJ hdvd Rt) rJ0 _ rfl rfl (by simp [PbJ, PbBase, withMem, rJ0])
      (by simp [PbJ, PbBase, withMem, rJ0]) (by simp [PbJ, PbBase, withMem, rJ0])
      (by simp [PbJ, PbBase, withMem, rJ0]) (by simp [PbJ, PbBase, withMem, rJ0])
      (by simp [PbJ, PbBase, withMem, rJ0])
    hbudV := ⟨le_refl _, by simp [PbJ, PbBase, withMem, rJ0], by simp [PbJ, PbBase, withMem, rJ0],
      by simp [PbJ, PbBase, withMem, rJ0]⟩
    hsatL := hsatL_A0 (PbJ hdvd Rt) rfl _ χ0 rfl hcA _ rfl
    hbindL := hbindL_A0 (PbJ hdvd Rt) _ χ0 rfl _ rfl }

/-- **The inhabitant at Goldilocks** (`p = Nock.Atoms.p`; `B ≤ p` and `3 · 2 ∣ p − 1` discharged): there are public
data, a coin, a message, traces, row counts and a budget at which `AcceptsJ8V` holds, with the atom walk ABSENT
(`krootsV = 0`), the J chip ABSENT (`nJ = 0`), and the claim TRUE (`HoldsN c0`). -/
theorem inhabitant_goldilocks (hpG : p = Nock.Atoms.p) (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    ∃ (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (r : RowsJ8) (g : ℕ),
      AcceptsJ8V δ b Pb R0 c0 χ M tr r g ∧ Pb.krootsV = 0 ∧ Pb.nJ = 0 ∧ Pb.regs = [] ∧ Nock.Jet.HoldsN c0 := by
  have hB : Nock.Atoms.B ≤ p := by
    rw [hpG, show Nock.Atoms.B = 2 ^ 32 from rfl, show Nock.Atoms.p = Nock.Field.p from rfl, Nock.Field.p_eq]
    norm_num
  have hdvd : 3 * 2 ^ 1 ∣ p - 1 := by
    rw [hpG, show Nock.Atoms.p = Nock.Field.p from rfl, Nock.Field.p_eq, Nat.dvd_iff_mod_eq_zero]
    norm_num
  exact ⟨PbJ hdvd Rt, χ0, MJ0 δ b χ0, trJ0 δ b hdvd Rt χ0, rJ0, 0, inhabitant δ b hB hdvd Rt, rfl, rfl, rfl,
    ⟨1, evalN0⟩⟩

end Main

end

end Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Main
