/-
  Nock/NockVMROM/Thm54/VclL/Handle/InhabJ8Atom.lean

  **The ATOM-TABLE conjuncts of `AcceptsJ8G.AcceptsJ8''''`
  (`hsatA hbindA hinjA hadjA hnpA hsatL hbindL`) inhabited by the ONE-ROW inert pad table** (`n = nA = 1`, the
  cell `[0 1]`, every multiplicity `0`).

  * `pubsA0 = 0` (all atom-table publics); `trA0 δ b hn nodes orbit χ : Fin 349 → (ZMod p)[X]` the trace
    (`InhabJ8AtomChip.padTraceA` at the atom table's coins `chalsAJ8Z δ χ`, `γ′ = (χ₄, χ₆)`, `ρ′ = (χ₅, χ₇)`,
    fingerprint seed `y = (χ_{Y1}, χ_{Y2})`).
  * **`CoinsA δ χ`**: the eight explicit coin conditions (`y ≠ 0` and seven non-vanishing denominators in closed
    form, `InhabJ8AtomDen`); each says that the pole `ρ′` (resp. `ρH`) avoids ONE value determined by the other
    coins, so it fails on at most `7` pole values (`+ y = 0`) out of `|𝕂′|`.
  * **`hsatL_A0`, `hbindL_A0`, `hsatA_A0`, `hbindA_A0`, `hinjA_A0`, `hadjA_A0`, `hnpA_A0`** at any `Pb` with
    `Pb.nA = 1`, `tr.A = trA0 … Pb.hnA Pb.nodesA Pb.orbitA χ`, `pubs = pubsA0`.
  * closed forms: `pubsA0_terminals` (validity `0/1`, export `2/3`, handle `pubHQ`, `pubMB`, `pubMI`, `pubC` and
    their `+1`: all `0`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomDen
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Atom

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomCell Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomChip
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomDen
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8
open Nock.NockVMROM.Thm54.StrictExtension

noncomputable section

section Atom
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The atom table's publics: all `0`. -/
def pubsA0 : ℕ → K := fun _ => 0

/-- The atom table's validity coins `γ′ = (χ₄, χ₆)`, `ρ′ = (χ₅, χ₇)`, its fingerprint seed `y`, the g5 seed
`zA = (χ₂, χ₃)`. -/
def γA (χ : Coins frameJ8 K) : 𝕂′ := Quad.mk _ (χ c4) (χ c6)
def ρA (χ : Coins frameJ8 K) : 𝕂′ := Quad.mk _ (χ c5) (χ c7)
def yA (χ : Coins frameJ8 K) : 𝕂′ := Quad.mk _ (χ cY1) (χ cY2)
def zA (χ : Coins frameJ8 K) : 𝕂′ := Quad.mk _ (χ c2) (χ c3)

/-- **The coin conditions** of the one-row pad atom table (completeness bad events, all explicit). -/
structure CoinsA (χ : Coins frameJ8 K) : Prop where
  hy : yA δ χ ≠ 0
  hV : ρA δ χ + yA δ χ ^ 2 + γA δ χ * yA δ χ + γA δ χ ^ 2 * yA δ χ + γA δ χ ^ 3 ≠ 0
  hX0 : ρA δ χ + yA δ χ ^ 2 + γA δ χ * yA δ χ + γA δ χ ^ 2 * yA δ χ + γA δ χ ^ 3 * yA δ χ +
    γA δ χ ^ 6 * yA δ χ + γA δ χ ^ 8 ≠ 0
  hX1 : ρA δ χ + yA δ χ ^ 2 + γA δ χ * yA δ χ + γA δ χ ^ 2 * yA δ χ + γA δ χ ^ 3 * yA δ χ +
    γA δ χ ^ 6 * yA δ χ + γA δ χ ^ 8 + γA δ χ ^ 10 ≠ 0
  hH : rhoHQ δ (toVSQ χ) + gamHQ δ (toVSQ χ) ^ 4 ≠ 0
  hMB : ρA δ χ + zA δ χ + γA δ χ ^ 2 * yA δ χ ≠ 0
  hC : rhoHQ δ (toVSQ χ) ≠ 0
  hMI : rhoHQ δ (toVSQ χ) + 2 + 2 * gamHQ δ (toVSQ χ) ^ 2 + 4 * gamHQ δ (toVSQ χ) ^ 4 ≠ 0

/-- **The trace** `trA0 : Fin 349 → (ZMod p)[X]` (as a function of the coins). -/
def trA0 {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) : Fin 349 → (ZMod p)[X] := fun j =>
  padTraceA δ b hn nodes orbit (chalsAJ8Z δ χ) pubsA0 (γA δ χ) (ρA δ χ) (yA δ χ)
    (Fin.cast (AtomChipHQ.atomChipHQ_width δ b hn nodes orbit (chalsAJ8Z δ χ) pubsA0).symm j)

theorem gamH_eq (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 33) (chalsAJ8Z δ χ 35) = gamHQ δ (toVSQ χ) := by
  rw [chalsAJ8Z_agree δ χ 33 (by omega) (by omega), chalsAJ8Z_agree δ χ 35 (by omega) (by omega)]; rfl

theorem rhoH_eq (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 34) (chalsAJ8Z δ χ 36) = rhoHQ δ (toVSQ χ) := by
  rw [chalsAJ8Z_agree δ χ 34 (by omega) (by omega), chalsAJ8Z_agree δ χ 36 (by omega) (by omega)]; rfl

/-- `atomChipHQL` accepts the one-row pad trace at `n = 1`, under `CoinsA`. -/
theorem sat1 {h : ℕ} (hn : 0 < 1) (nodes : Fin 1 → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) (hc : CoinsA δ χ) :
    (atomChipHQL δ b hn nodes orbit (chalsAJ8Z δ χ) pubsA0).rap.Satisfies
      (padTraceL δ b hn nodes orbit (chalsAJ8Z δ χ) pubsA0 (γA δ χ) (ρA δ χ) (yA δ χ)) := by
  have hok : ChalsOK δ (chalsAJ8Z δ χ) (γA δ χ) (ρA δ χ) 11 := chalsAJ8Z_ok δ χ
  have hy := hc.hy
  refine pad_atomChipHQL_sat δ b hn nodes orbit (chalsAJ8Z δ χ) pubsA0 (γA δ χ) (ρA δ χ) (yA δ χ) hok
    (chalsAJ8Z_y δ χ) hy ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · rw [padV_eq δ _ _ _ hy]; exact hc.hV
  · rw [padX_eq δ _ _ _ hy]; simpa [liftQ] using hc.hX0
  · rw [padX_eq δ _ _ _ hy]; simpa [liftQ] using hc.hX1
  · intro i; rw [padRow_eq, rhoH_eq, gamH_eq]; exact hc.hH
  · intro i; rw [padMB_eq _ _ _ _ _ _ _ _ _ _ i hok, chalsAJ8Z_zAt]; exact hc.hMB
  · intro i; rw [padC_eq, rhoH_eq]; exact hc.hC
  · intro i; rw [padMI_eq, rhoH_eq, gamH_eq]; exact hc.hMI

theorem satN {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (hn1 : n = 1) (χ : Coins frameJ8 K) (hc : CoinsA δ χ) :
    (atomChipHQL δ b hn nodes orbit (chalsAJ8Z δ χ) pubsA0).rap.Satisfies
      (padTraceL δ b hn nodes orbit (chalsAJ8Z δ χ) pubsA0 (γA δ χ) (ρA δ χ) (yA δ χ)) := by
  subst hn1
  exact sat1 δ b hn nodes orbit χ hc

/-- The variant view of a table whose atom trace is `trA0` IS the pad trace. -/
theorem qAL_eq (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (χ : Coins frameJ8 K)
    (htr : tr.A = trA0 δ b Pb.hnA Pb.nodesA Pb.orbitA χ) :
    qAL δ b Pb tr (chalsAJ8Z δ χ) pubsA0 =
      padTraceL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) pubsA0 (γA δ χ) (ρA δ χ) (yA δ χ) := by
  funext j
  simp only [qAL, htr, trA0]
  rfl

variable {δ b}

/-- **`hsatL`** (the atom table at the variant chip). -/
theorem hsatL_A0 (Pb : PubJ8 p) (hA : Pb.nA = 1) (tr : TrJ8 (ZMod p)) (χ : Coins frameJ8 K)
    (htr : tr.A = trA0 δ b Pb.hnA Pb.nodesA Pb.orbitA χ) (hc : CoinsA δ χ) (pubs : ℕ → K) (hpub : pubs = pubsA0) :
    (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) pubs).rap.Satisfies
      (qAL δ b Pb tr (chalsAJ8Z δ χ) pubs) := by
  subst hpub
  rw [qAL_eq δ b Pb tr χ htr]
  exact satN δ b Pb.hnA Pb.nodesA Pb.orbitA hA χ hc

/-- **`hbindL`** (no coin condition). -/
theorem hbindL_A0 (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (χ : Coins frameJ8 K)
    (htr : tr.A = trA0 δ b Pb.hnA Pb.nodesA Pb.orbitA χ) (pubs : ℕ → K) (hpub : pubs = pubsA0) :
    (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) pubs).BindsPreprocessing
      (qAL δ b Pb tr (chalsAJ8Z δ χ) pubs) := by
  subst hpub
  rw [qAL_eq δ b Pb tr χ htr]
  intro j
  fin_cases j
  · exact honestQ_zero Pb.hnA Pb.nodesA _ (by norm_num)
  · exact honestQ_one Pb.hnA Pb.nodesA _ (by norm_num)

/-- **`hsatA`**. -/
theorem hsatA_A0 (Pb : PubJ8 p) (hA : Pb.nA = 1) (tr : TrJ8 (ZMod p)) (χ : Coins frameJ8 K)
    (htr : tr.A = trA0 δ b Pb.hnA Pb.nodesA Pb.orbitA χ) (hc : CoinsA δ χ) (pubs : ℕ → K) (hpub : pubs = pubsA0) :
    (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) pubs).rap.Satisfies
      (qA δ b Pb tr (chalsAJ8Z δ χ) pubs) := by
  rw [← qAL_toHQ]
  exact atomChipHQL_sat δ b _ _ _ _ _ _ (hsatL_A0 Pb hA tr χ htr hc pubs hpub)

/-- **`hbindA`**. -/
theorem hbindA_A0 (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (χ : Coins frameJ8 K)
    (htr : tr.A = trA0 δ b Pb.hnA Pb.nodesA Pb.orbitA χ) (pubs : ℕ → K) (hpub : pubs = pubsA0) :
    (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) pubs).BindsPreprocessing
      (qA δ b Pb tr (chalsAJ8Z δ χ) pubs) := by
  rw [← qAL_toHQ]
  exact atomChipHQL_bind δ b _ _ _ _ _ _ (hbindL_A0 Pb tr χ htr pubs hpub)

/-- **`hinjA`**. -/
theorem hinjA_A0 (Pb : PubJ8 p) (hA : Pb.nA = 1) : Function.Injective Pb.nodesA :=
  fun a c _ => Fin.ext (by have := a.isLt; have := c.isLt; omega)

/-- **`hadjA`** (vacuous at one row). -/
theorem hadjA_A0 (Pb : PubJ8 p) (hA : Pb.nA = 1) :
    ∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω :=
  fun i hi => absurd hi (by omega)

/-- **`hnpA`**. -/
theorem hnpA_A0 (Pb : PubJ8 p) (hA : Pb.nA = 1) : Pb.nA < p := by
  rw [hA]; exact (Fact.out : p.Prime).one_lt

/-- **The closed forms of the atom-table publics** read by `hvalA0`, `hfxA`, `hbalA'`, `hGS`, `hsumC'`. -/
theorem pubsA0_terminals :
    (pubsA0 : ℕ → K) 0 = 0 ∧ (pubsA0 : ℕ → K) 1 = 0 ∧ (pubsA0 : ℕ → K) 2 = 0 ∧ (pubsA0 : ℕ → K) 3 = 0 ∧
    (pubsA0 : ℕ → K) CellHQ.pubHQ = 0 ∧ (pubsA0 : ℕ → K) (CellHQ.pubHQ + 1) = 0 ∧
    (pubsA0 : ℕ → K) AtomChipHQ.pubMB = 0 ∧ (pubsA0 : ℕ → K) (AtomChipHQ.pubMB + 1) = 0 ∧
    (pubsA0 : ℕ → K) AtomChipHQ.pubMI = 0 ∧ (pubsA0 : ℕ → K) (AtomChipHQ.pubMI + 1) = 0 ∧
    (pubsA0 : ℕ → K) AtomChipHQ.pubC = 0 ∧ (pubsA0 : ℕ → K) (AtomChipHQ.pubC + 1) = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `hvalA0` at `pubsA0`. -/
theorem hvalA0_A0 : (pubsA0 : ℕ → K) 0 = 0 ∧ (pubsA0 : ℕ → K) 1 = 0 := ⟨rfl, rfl⟩

end Atom

end

end Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Atom
