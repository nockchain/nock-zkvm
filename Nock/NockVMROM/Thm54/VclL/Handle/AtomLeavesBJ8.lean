/-
  Nock/NockVMROM/Thm54/VclL/Handle/AtomLeavesBJ8.lean

  **`AtomLeaves` at `extB p rA` from g4 on the
  exported (`mb`) rows.**  New module, additive.

  * ℕ level: **`B_le_val`** (under g3, `TopNZ`: every denoted limb list has value `≥ B`) and **`big_of_bnd`**
    (a row meeting the boundary condition `wR = 0 → aR = B − 1 ∧ aL ≠ 0` (g4's ℕ reading) denotes a value
    `≥ p`: two limbs `[aL, B − 1]` with `aL ≥ 1` give `≥ B(B − 1) + 1 = p`; three or more give `≥ B²`).
  * Gate level: **`bnd_of_mb`** (g4 `bnd mb` at an `mb = 1` row, read in ℕ), **`topNZ_of_gates`** (g3 on the table
    rows, `atom_g23`; the rows beyond the table by the named `hTout`, the same class as `hB` / `hwRA` / `hrn`).
  * **`extB_mb`**: an exported row's denoted value is big and `extB p rA` reads it (`p ≤ val l`,
    `extB p rA k = atom (val l)`): the two premises P11's `G5J8.atomLeaves_of_rows` asks at `ext = extB p rA`.
  * **`atomLeaves_extB`**: `AtomLeaves E vp (extA r)` with every key's row big ⇒ `AtomLeaves E vp (extB p r)`;
    **`atomLeaves_extB_of_mb`**: the same with "big" from the keys' rows being `mb` rows (g4).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AtomLeavesBJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes Reads atomChipHQ atomGates bnd LimbsBounded)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (TopNZ atom_g23)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ (aEF atom_base)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8 (extA)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB extB_of_denotes extA_some)
open Nock.ComputeTable (FP)
open Nock.Atoms (val B)

noncomputable section

/-! ## 1. ℕ level -/

theorem B_le_val {r : ℕ → ARow} (hT : TopNZ r) {j : ℕ} {l : List ℕ} (h : Denotes r j l) : B ≤ val l := by
  induction h with
  | @top i hw =>
    have h1 := hT i hw
    simp only [val, Nat.ofDigits_cons, Nat.ofDigits_nil, mul_zero, add_zero]
    have : B * 1 ≤ B * (r i).aR := Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr h1)
    omega
  | @step i l' _ _ ih =>
    simp only [val, Nat.ofDigits_cons] at ih ⊢
    have hB1 : 1 ≤ B := by norm_num [B]
    have : B * 1 ≤ B * Nat.ofDigits B l' := Nat.mul_le_mul_left _ (le_trans hB1 ih)
    omega

theorem p_eq : Nock.Atoms.p = B * (B - 1) + 1 := by
  show Nock.Field.p = _
  norm_num [Nock.Field.p, B]

/-- **g4 read in ℕ ⇒ big**: a row with `wR = 0 → aR = B − 1 ∧ aL ≠ 0` denotes a value `≥ p`. -/
theorem big_of_bnd {r : ℕ → ARow} (hT : TopNZ r) {k : ℕ}
    (hk : (r k).wR = 0 → (r k).aR = B - 1 ∧ (r k).aL ≠ 0) {l : List ℕ} (h : Denotes r k l) :
    Nock.Atoms.p ≤ val l := by
  rw [p_eq]
  cases h with
  | top hw =>
    obtain ⟨haR, haL⟩ := hk hw
    simp only [val, Nat.ofDigits_cons, Nat.ofDigits_nil, mul_zero, add_zero, haR]
    omega
  | step hw hd =>
    have h1 := B_le_val hT hd
    simp only [val, Nat.ofDigits_cons] at h1 ⊢
    have h2 : B * B ≤ B * Nat.ofDigits B _ := Nat.mul_le_mul_left _ h1
    have h3 : B * (B - 1) + 1 ≤ B * B := by norm_num [B]
    omega

/-- **`AtomLeaves` passes from `extA` to `extB`** when every key's row is big. -/
theorem atomLeaves_extB {Kfp : Type} [Field Kfp] {E : Noun → FP Kfp} {vp : List (VKey Kfp)} {p : ℕ}
    {r : ℕ → ARow} (hA : AtomLeaves E vp (extA r))
    (hbig : ∀ k ∈ vp, ∀ l, Denotes r k.2.2.2 l → p ≤ val l) : AtomLeaves E vp (extB p r) := by
  intro k hk
  obtain ⟨h1, h2, v, hv, hE⟩ := hA k hk
  obtain ⟨l, hl, hX⟩ := extA_some hv
  have hvl : v = val l := by simpa using hX
  refine ⟨h1, h2, v, ?_, hE⟩
  rw [hvl]; exact extB_of_denotes hl (hbig k hk l hl)

/-! ## 2. Gate level -/

section Gates
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {hA nA : ℕ} {hnA : 0 < nA} {nodesA : Fin nA → ZMod p} {orbitA : StrictOrbitDomain (ZMod p) 3 hA}
  {chalsA pubsA : ℕ → K}
  {QA : Fin (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X]}

local notation "AE" => aEF b nodesA orbitA chalsA pubsA QA

/-- **g4 (`bnd mb`) at an exported row, read in ℕ.** -/
theorem bnd_of_mb (hq : 2 ^ 63 < p) (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    {r : ℕ → ARow} (hR : ∀ k : Fin nA, Reads (AE k) (r k)) (hs : ∀ k : Fin nA, (r k).Small) (k : Fin nA)
    (hmb : (AE k).trace AtomChipHQ.mb = 1) :
    (r k).wR = 0 → (r k).aR = B - 1 ∧ (r k).aL ≠ 0 := by
  intro hw
  have hqF : 2 ^ 63 < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n]; exact hq
  have ce : ∀ {x y : ℕ}, x < 2 ^ 63 → y < 2 ^ 63 → ((x : ℕ) : ZMod p) = y → x = y :=
    fun hx hy e => AtomChipHQ.cast_inj hqF hx hy e
  have hg := atom_base δ b hnA nodesA orbitA chalsA pubsA QA hsat k
  have g := fun x (hx : x ∈ (atomGates : List (CoeffExpr (ZMod p)))) => hg x (List.mem_append_right _ hx)
  have g4a := g _ (by simp [atomGates, bnd] :
    CoeffExpr.mul (.mul (cv AtomChipHQ.mb) (notE (cv Cell.wR))) (.sub (cv Cell.aR) (.const (AtomChipHQ.Bf - 1))) ∈
      (atomGates : List (CoeffExpr (ZMod p))))
  have g4b := g _ (by simp [atomGates, bnd] :
    CoeffExpr.mul (.mul (cv AtomChipHQ.mb) (notE (cv Cell.wR)))
      (.sub (.mul (cv Cell.aL) (cv AtomChipHQ.invB)) (.const 1)) ∈ (atomGates : List (CoeffExpr (ZMod p))))
  simp only [notE, cv, CoeffExpr.eval] at g4a g4b
  have hRk := hR k
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := hs k
  rw [hmb, hRk.wR, hw, Nat.cast_zero, sub_zero, one_mul, one_mul] at g4a g4b
  refine ⟨?_, ?_⟩
  · apply ce (by omega) (by norm_num [B])
    rw [← hRk.aR, sub_eq_zero.mp g4a, AtomChipHQ.Bf_eq, Nat.cast_sub (by norm_num [B]), Nat.cast_one]
  · intro h0
    rw [hRk.aL, h0, Nat.cast_zero, zero_mul, zero_sub] at g4b
    exact one_ne_zero (neg_eq_zero.mp g4b)

/-- **g3 on the table rows** (`atom_g23`), and on the rows beyond the table by `hTout`. -/
theorem topNZ_of_gates (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    {r : ℕ → ARow} (hR : ∀ k : Fin nA, Reads (AE k) (r k))
    (hTout : ∀ j, nA ≤ j → (r j).wR = 0 → (r j).aR ≠ 0) : TopNZ r := by
  intro j hw
  by_cases hj : j < nA
  · have hRk := hR ⟨j, hj⟩
    have g3 := (atom_g23 hsat ⟨j, hj⟩).2
    intro h0
    apply g3
    · rw [hRk.wR]; simp [hw]
    · rw [hRk.aR]; simp [h0]
  · exact hTout j (by omega) hw

/-- **An exported row is big and `extB` reads it.** -/
theorem extB_mb (hq : 2 ^ 63 < p) (hpG : p = Nock.Atoms.p)
    (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    {r : ℕ → ARow} (hR : ∀ k : Fin nA, Reads (AE k) (r k)) (hs : ∀ k : Fin nA, (r k).Small)
    (hT : TopNZ r) (k : Fin nA) (hmb : (AE k).trace AtomChipHQ.mb = 1) {l : List ℕ} (hd : Denotes r k l) :
    p ≤ val l ∧ extB p r k = some (.atom (val l)) := by
  have hb : p ≤ val l := by rw [hpG]; exact big_of_bnd hT (bnd_of_mb hq hsat hR hs k hmb) hd
  exact ⟨hb, extB_of_denotes hd hb⟩

/-- **`AtomLeaves` at `extB p rA` from g4**: every key of `vp` names an exported (`mb`) row. -/
theorem atomLeaves_extB_of_mb {Kfp : Type} [Field Kfp] {E : Noun → FP Kfp} {vp : List (VKey Kfp)}
    (hq : 2 ^ 63 < p) (hpG : p = Nock.Atoms.p)
    (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    {r : ℕ → ARow} (hR : ∀ k : Fin nA, Reads (AE k) (r k)) (hs : ∀ k : Fin nA, (r k).Small)
    (hTout : ∀ j, nA ≤ j → (r j).wR = 0 → (r j).aR ≠ 0)
    (hA : AtomLeaves E vp (extA r))
    (hvpRow : ∀ k ∈ vp, ∃ i : Fin nA, (AE i).trace AtomChipHQ.mb = 1 ∧ k.2.2.2 = i) :
    AtomLeaves E vp (extB p r) := by
  have hT := topNZ_of_gates hsat hR hTout
  refine atomLeaves_extB hA fun k hk l hl => ?_
  obtain ⟨i, hmb, hi⟩ := hvpRow k hk
  rw [hi] at hl
  exact (extB_mb hq hpG hsat hR hs hT i hmb hl).1

end Gates

end

end Nock.NockVMROM.Thm54.VclL.Handle.AtomLeavesBJ8
