/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AChipsOK.lean

Every key denominator of the axis chip (`limbKey`, `pathKey`, `tagKey` per row) and of the split chip (`d2`, `d3`
  per row) is `ρH + x` where `x` is a polynomial in `γH = (χ₁₁, χ₁₅)` with constant (coin-free) coefficients and
  `Re ρH = χ₁₂` (`InhabJ8Good.c12`): a vanishing denominator is a `quadPole` event on coordinate `c12`, weight
  `1/|K|` each.  Axis: `3n` events; split: `2n` events.  The terminal publics are DEFINED as the honest sums.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AAxisRows
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ASplitH
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChipsOK

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AXChipOK SPChipOK)
open Module

noncomputable section

section Gen
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The handle coins at `chalsMJ8` are `(γH, ρH)`** (the memory chips' `κ`). -/
theorem kappa_eq (χ : Coins frameJ8 K) :
    Nock.NockVMROM.Thm54.VclL.Handle.AxisTeleJ9.κ δ (chalsMJ8 δ χ) =
      (⟨γH δ χ, ρH δ χ⟩ : FiniteIO.IOCoins 𝕂′) := by
  have h := mcoins_J8 δ χ
  exact h.trans rfl

theorem chals_pair (χ : Coins frameJ8 K) :
    Quad.mk _ (chalsMJ8 δ χ 33) (chalsMJ8 δ χ 35) = γH δ χ ∧
      Quad.mk _ (chalsMJ8 δ χ 34) (chalsMJ8 δ χ 36) = ρH δ χ := by
  have h := kappa_eq δ χ
  simp only [Nock.NockVMROM.Thm54.VclL.Handle.AxisTeleJ9.κ] at h
  exact ⟨congrArg FiniteIO.IOCoins.gamma h, congrArg FiniteIO.IOCoins.pole h⟩

end Gen

/-! ## 1. The axis chip -/

section Axis
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {n : ℕ} (hn0 : 0 < n) (cs : List (ComplJ9AAxisRows.ChainSpec (ZMod p)))
  (hn : n = (ComplJ9AAxisRows.tableRows cs).length)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The three axis keys. -/
def axKeys : List (List (CoeffExpr (ZMod p))) :=
  [Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.limbKey, Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pathKey,
    Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.tagKey]

/-- The coin-free key vector of row `i`, key `key`. -/
def axKeyVec (key : List (CoeffExpr (ZMod p))) (i : Fin n) : Fin 8 → 𝕂′ :=
  liftRec (K := K) (L := 𝕂′) (Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.keyVecL (K := K) 8 key
    (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.envC hn0 (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn) i (fun _ => 0)))

/-- **The three key denominators of axis row `i`** as functions of the coin. -/
def axDens (i : Fin n) : List (Coins frameJ8 K → 𝕂′) :=
  axKeys.map fun key χ => Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.dKey δ (chalsMJ8 δ χ) hn0
    (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn) key i

/-- All `3n` key vectors. -/
def axVecs : List (Fin 8 → 𝕂′) :=
  (List.finRange n).flatMap fun i => axKeys.map fun key => axKeyVec δ hn0 cs hn key i

/-- **The axis completeness bad events**: one pole event on `χ₁₂` per denominator and row (`3n` events). -/
def famAX : List (BadSpec K) := ioPoles δ InhabJ8Good.c12 (γH δ) (axVecs δ hn0 cs hn)

theorem famAX_OK : ∀ e ∈ famAX δ hn0 cs hn (K := K), e.OK :=
  ioPoles_OK δ _ _ _ (γH_readsOff δ)

theorem famAX_length : (famAX δ hn0 cs hn (K := K)).length = 3 * n := by
  simp [famAX, ioPoles, axVecs, axKeys, List.length_flatMap, Function.comp_def]
  omega

theorem famAX_cost : costL (famAX δ hn0 cs hn (K := K)) = 3 * n := by
  have h : ∀ s ∈ famAX δ hn0 cs hn (K := K), s.cost = 1 := by
    intro s hs
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hs
    rfl
  rw [costL, List.map_congr_left h, List.map_const', List.sum_replicate, famAX_length]
  simp

theorem famAX_good (χ : Coins frameJ8 K) (hχ : ∀ e ∈ famAX δ hn0 cs hn (K := K), χ ∉ e.ev) (i : Fin n) :
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.dKey δ (chalsMJ8 δ χ) hn0 (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn)
      Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.limbKey i ≠ 0 ∧
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.dKey δ (chalsMJ8 δ χ) hn0 (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn)
      Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pathKey i ≠ 0 ∧
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.dKey δ (chalsMJ8 δ χ) hn0 (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn)
      Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.tagKey i ≠ 0 := by
  have hg := ioPoles_good δ InhabJ8Good.c12 (γH δ) (ρH δ) (axVecs δ hn0 cs hn) (ρH_re δ) χ hχ
  have hk : ∀ key ∈ axKeys (p := p), 
      Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.dKey δ (chalsMJ8 δ χ) hn0
        (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn) key i ≠ 0 := by
    intro key hkey
    have := hg (axKeyVec δ hn0 cs hn key i)
      (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨key, hkey, rfl⟩⟩)
    have e := kappa_eq δ χ
    unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.dKey
    rw [e]
    exact this
  refine ⟨hk _ ?_, hk _ ?_, hk _ ?_⟩ <;> simp [axKeys]

/-- The honest service terminal. -/
def axSumS (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ i, ((Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.dKey δ (chalsMJ8 δ χ) hn0 (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn)
      Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.limbKey i)⁻¹ -
    liftQ δ (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.mu i) *
      (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.dKey δ (chalsMJ8 δ χ) hn0 (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn)
        Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.tagKey i)⁻¹)

/-- The honest path terminal. -/
def axSumP (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ i, liftQ δ (1 - ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.z1a i) *
    (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.dKey δ (chalsMJ8 δ χ) hn0 (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn)
      Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pathKey i)⁻¹

/-- **The axis publics**: `pubAXs, pubAXs+1` = Re/Im of the service sum, `pubAXp, pubAXp+1` = Re/Im of the path
sum, `0` elsewhere. -/
def pubsXOf (χ : Coins frameJ8 K) : ℕ → K := fun j =>
  if j = Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXs then Quad.re _ (axSumS δ hn0 cs hn χ)
  else if j = Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXs + 1 then Quad.im _ (axSumS δ hn0 cs hn χ)
  else if j = Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXp then Quad.re _ (axSumP δ hn0 cs hn χ)
  else if j = Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXp + 1 then Quad.im _ (axSumP δ hn0 cs hn χ)
  else 0

theorem pubsXOf_S (χ : Coins frameJ8 K) :
    Quad.mk _ (pubsXOf δ hn0 cs hn χ Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXs)
      (pubsXOf δ hn0 cs hn χ (Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXs + 1)) = axSumS δ hn0 cs hn χ := by
  simp [pubsXOf, Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXs, Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXp,
    Quad.mk_re_im]

theorem pubsXOf_P (χ : Coins frameJ8 K) :
    Quad.mk _ (pubsXOf δ hn0 cs hn χ Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXp)
      (pubsXOf δ hn0 cs hn χ (Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXp + 1)) = axSumP δ hn0 cs hn χ := by
  simp [pubsXOf, Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXs, Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXp,
    Quad.mk_re_im]

/-- **`AXChipOK`, present disjunct, for an honest table of chains** at every coin outside `famAX`. -/
theorem axChipOK_honest {h : ℕ} (hcs : ∀ c ∈ cs, c.OK) (nodes : Fin n → ZMod p)
    (orbit : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnp : n < p) (χ : Coins frameJ8 K) (hχ : ∀ e ∈ famAX δ hn0 cs hn (K := K), χ ∉ e.ev) :
    AXChipOK δ b true hn0 nodes orbit (chalsMJ8 δ χ) (pubsXOf δ hn0 cs hn χ)
      (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.polyAx δ b hn0 nodes orbit (chalsMJ8 δ χ)
        (pubsXOf δ hn0 cs hn χ) (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn)) := by
  have hden := famAX_good δ hn0 cs hn χ hχ
  have hs := Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisRows.axisChipJ9_honest_table (δ := δ) (b := b)
    (nodes := nodes) (orbit := orbit) (chals := chalsMJ8 δ χ) (pubs := pubsXOf δ hn0 cs hn χ) hcs hn0 hn hinj hadj
    hden (pubsXOf_S δ hn0 cs hn χ) (pubsXOf_P δ hn0 cs hn χ)
  exact Or.inl ⟨rfl, hs.1, hs.2, hinj, hadj, hnp⟩

end Axis

/-! ## 2. The split chip -/

section Split
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (nA : ℕ) {n : ℕ} (vS mS : Fin n → ℕ)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The coin-polynomial part of a four-limb record key: `a + γ b + γ² c + γ³ d`. -/
def xKey4 (γ : 𝕂′) (a b c d : ZMod p) : 𝕂′ :=
  liftQ δ a + γ * liftQ δ b + γ ^ 2 * liftQ δ c + γ ^ 3 * liftQ δ d

/-- The pole-free part of `d2` at row `i`, as a function of `γ`. -/
def x2 (i : Fin n) (γ : 𝕂′) : 𝕂′ :=
  xKey4 δ γ ((nA + (i : ℕ) : ℕ) : ZMod p) 2 0 ((vS i % 2 ^ 32 : ℕ) : ZMod p)
/-- The pole-free part of `d3` at row `i`. -/
def x3 (i : Fin n) (γ : 𝕂′) : 𝕂′ :=
  xKey4 δ γ ((nA + (i : ℕ) : ℕ) : ZMod p) 3 0 ((vS i / 2 ^ 32 : ℕ) : ZMod p)

theorem d2_eq (χ : Coins frameJ8 K) (i : Fin n) :
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.d2 δ (chalsMJ8 δ χ) nA vS i = ρH δ χ + x2 δ nA vS i (γH δ χ) := by
  obtain ⟨h1, h2⟩ := chals_pair δ χ
  unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.d2 Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.dKey4
  rw [h1, h2]; rfl

theorem d3_eq (χ : Coins frameJ8 K) (i : Fin n) :
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.d3 δ (chalsMJ8 δ χ) nA vS i = ρH δ χ + x3 δ nA vS i (γH δ χ) := by
  obtain ⟨h1, h2⟩ := chals_pair δ χ
  unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.d3 Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.dKey4
  rw [h1, h2]; rfl

/-- **The two denominators of split row `i`** as functions of the coin. -/
def spDens (i : Fin n) : List (Coins frameJ8 K → 𝕂′) :=
  [fun χ => Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.d2 δ (chalsMJ8 δ χ) nA vS i,
   fun χ => Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.d3 δ (chalsMJ8 δ χ) nA vS i]

/-- The pole-free parts of the two denominators (functions of the coin). -/
def spXs (i : Fin n) : List (Coins frameJ8 K → 𝕂′) :=
  [fun χ => x2 δ nA vS i (γH δ χ), fun χ => x3 δ nA vS i (γH δ χ)]

/-- **The split completeness bad events**: one pole event on `χ₁₂` per denominator and row (`2n` events). -/
def famSP : List (BadSpec K) :=
  (List.finRange n).flatMap fun i => (spXs δ nA vS i (K := K)).map (quadPole δ InhabJ8Good.c12)

theorem famSP_OK : ∀ e ∈ famSP δ nA vS (K := K), e.OK := by
  intro e he
  obtain ⟨i, -, he⟩ := List.mem_flatMap.mp he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  refine quadPole_OK δ _ _ ?_
  simp only [spXs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;>
  · intro χ χ' h
    beta_reduce
    rw [γH_readsOff δ χ χ' h]

theorem famSP_length : (famSP δ nA vS (K := K)).length = 2 * n := by
  simp [famSP, spXs, List.length_flatMap, Function.comp_def]
  omega

theorem famSP_cost : costL (famSP δ nA vS (K := K)) = 2 * n := by
  have h : ∀ s ∈ famSP δ nA vS (K := K), s.cost = 1 := by
    intro s hs
    obtain ⟨i, -, he⟩ := List.mem_flatMap.mp hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    rfl
  rw [costL, List.map_congr_left h, List.map_const', List.sum_replicate, famSP_length]
  simp

theorem famSP_good (χ : Coins frameJ8 K) (hχ : ∀ e ∈ famSP δ nA vS (K := K), χ ∉ e.ev) (i : Fin n) :
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.d2 δ (chalsMJ8 δ χ) nA vS i ≠ 0 ∧
      Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.d3 δ (chalsMJ8 δ χ) nA vS i ≠ 0 := by
  have hm : ∀ x ∈ spXs δ nA vS i (K := K), χ ∉ (quadPole δ InhabJ8Good.c12 x).ev := fun x hx =>
    hχ _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨x, hx, rfl⟩⟩)
  refine ⟨?_, ?_⟩
  · rw [d2_eq]
    exact quadPole_ne δ InhabJ8Good.c12 (fun χ => x2 δ nA vS i (γH δ χ)) χ (ρH δ χ) (ρH_re δ χ)
      (hm _ (by simp [spXs]))
  · rw [d3_eq]
    exact quadPole_ne δ InhabJ8Good.c12 (fun χ => x3 δ nA vS i (γH δ χ)) χ (ρH δ χ) (ρH_re δ χ)
      (hm _ (by simp [spXs]))

/-- The honest split terminal. -/
def spSum (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ i, Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.rowT δ (chalsMJ8 δ χ) nA vS mS i

/-- **The split publics**: `pubSPs, pubSPs+1` = Re/Im of the terminal, `0` elsewhere. -/
def pubsSOf (χ : Coins frameJ8 K) : ℕ → K := fun j =>
  if j = Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9.pubSPs then Quad.re _ (spSum δ nA vS mS χ)
  else if j = Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9.pubSPs + 1 then Quad.im _ (spSum δ nA vS mS χ)
  else 0

theorem pubsSOf_S (χ : Coins frameJ8 K) :
    Quad.mk _ (pubsSOf δ nA vS mS χ Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9.pubSPs)
      (pubsSOf δ nA vS mS χ (Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9.pubSPs + 1)) = spSum δ nA vS mS χ := by
  simp [pubsSOf, Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9.pubSPs, Quad.mk_re_im]

/-- **`SPChipOK`, present disjunct, for honest split values** at every coin outside `famSP`. -/
theorem spChipOK_honest {h : ℕ} (hn0 : 0 < n) (nodes : Fin n → ZMod p)
    (orbit : StrictOrbitDomain (ZMod p) 3 h) (hp : 2 ^ 32 < p) (hv : ∀ i, 2 ^ 32 ≤ vS i ∧ vS i < 2 ^ 64)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnp : n < p) (χ : Coins frameJ8 K) (hχ : ∀ e ∈ famSP δ nA vS (K := K), χ ∉ e.ev) :
    SPChipOK δ b nA true hn0 nodes orbit (chalsMJ8 δ χ) (pubsSOf δ nA vS mS χ)
      (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.polySC δ nA b hn0 nodes orbit (chalsMJ8 δ χ)
        (pubsSOf δ nA vS mS χ) vS mS) := by
  have hd := famSP_good δ nA vS χ hχ
  have hs := Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH.splitChipJ9_honest_sat' δ nA b hn0 nodes orbit
    (chalsMJ8 δ χ) (pubsSOf δ nA vS mS χ) vS mS hp hv hinj hadj (fun i => (hd i).1) (fun i => (hd i).2)
    (pubsSOf_S δ nA vS mS χ)
  exact Or.inl ⟨rfl, hs.1, hs.2, hinj, hadj, hnp⟩

end Split

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChipsOK

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChipsOK
#print axioms kappa_eq
#print axioms chals_pair
#print axioms famAX_OK
#print axioms famAX_length
#print axioms famAX_cost
#print axioms famAX_good
#print axioms pubsXOf_S
#print axioms pubsXOf_P
#print axioms axChipOK_honest
#print axioms d2_eq
#print axioms d3_eq
#print axioms famSP_OK
#print axioms famSP_length
#print axioms famSP_cost
#print axioms famSP_good
#print axioms pubsSOf_S
#print axioms spChipOK_honest
end Axioms
