/-
  Nock/NockVMROM/Thm54/VclL/Handle/EncZYJ8.lean

* §1 **`encZY z y`**: an atom `n` is
    `atomFP z (leafVal y n)` (`A_n(y)` for a big atom, `n` for a small one), a cell is `FP.cons z`.  `encZY_cell`
    (`provOK_x` / `provOK_p`'s `hcons`, `rfl`) and **`inlineAtoms_encZY`** (`hE : InlineAtoms q z E` at
    `q = Atoms.p`, from `leafVal_small`).  `atomLeaves_of_g5`: a provider list whose keys have the g5 shape
    `(⟨z, 0, leafVal y v⟩, 0, 0, idx)` with `ext idx = atom v` is `AtomLeaves (encZY z y)`.
  * §2 the atom walk's vector **`chalsVJ8 := chalsAJ8`**: `hyV_J8` (`chalsV 2, 3 = chalsA 2, 3`), `hchV_J8`
    (leaves `33..36` agree with `chalsMJ8`), `chalsVJ8_walk` (its walk coins, leaves `0, 1`, are `χ₀, χ₁`).
  * §3 **FINDING and the corrected summand #9.**  The atom walk chip
    (`walkChipHQK`) commits its labels (fingerprints at `y`) in ROUND 1 (`baseColsOf = ![25, 0, 0]`,
    `extColsOf = ![0, 24, 23]`; `walkDataOf` reads `walkEnvK`), and reads its walk coins at leaves `0, 1`. At the
    J-8 vectors those leaves are `χ₀, χ₁` (sampled after round 1), the 40th's walk-chain coins. `WeightsJ8`'s #9
    (`atomWalkJ8`) prices the event on `(χ₁₃, χ₁₄)` (sampled after ROUND 0) reading `y` only: the chip's walk
    data then depends on round-1 columns committed after `(χ₁₃, χ₁₄)` are drawn, so `DataJ8.wdA_reads`
    (`ReadsOnC yDep`) is not satisfiable by the chip's readout, and the event is on coins the chip does not use
    (`CorJ8A`'s `houtV` reads `(chalsV 0, chalsV 1)`). The corrected #9 is the 40th's walk-chain shape:
    **`atomWalkJ8C`** on `(χ₀, χ₁)` reading `coinsBelow frameJ8 1` (the round-0 coins, `y` included), SAME
    weight `|𝕂|·15·AW` over `|𝕂|²` (`epsilon_atomWalkJ8C`: `ε` equal to #9's, so `boundJ8P` and the 155 figure
    are unchanged). **`houtV_of_outside`**: outside it, `(chalsVJ8 0, chalsVJ8 1) ∉ walkEvent` (`CorJ8A`'s
    `houtV`). -/
import Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8
open Nock.ComputeTable (FP)
open Nock.Atoms (leafVal leafVal_small)

noncomputable section

/-! ## 1. The bivariate encoder `E(z, y)` -/

section Enc
variable {Kfp : Type} [Field Kfp] [iF : Algebra Nock.Atoms.Fp Kfp] [Fintype Kfp] [DecidableEq Kfp]

/-- **`E(z, y)`**: an atom `n` has fingerprint `(z, 0, leafVal y n)`; a cell is `FP.cons z`. -/
def encZY (z y : Kfp) : Noun → FP Kfp
  | .atom n => FP.atomFP z (leafVal y n)
  | .cell a b => FP.cons z (encZY z y a) (encZY z y b)

theorem encZY_atom (z y : Kfp) (n : ℕ) : encZY z y (.atom n) = FP.atomFP z (leafVal y n) := rfl

/-- `provOK_x` / `provOK_p`'s `hcons`. -/
theorem encZY_cell (z y : Kfp) (a b : Noun) : encZY z y (.cell a b) = FP.cons z (encZY z y a) (encZY z y b) := rfl

/-- **`provOK_x` / `provOK_p`'s `hE`**: on small atoms `E(z, y)` is the inline-atom fingerprint (`leafVal_small`),
at `q = Atoms.p` (any `ZMod q`-algebra structure: ring maps out of `ZMod q` are unique). -/
theorem inlineAtoms_encZY {q : ℕ} [iq : Algebra (ZMod q) Kfp] (hq : q = Nock.Atoms.p) (z y : Kfp) :
    InlineAtoms q z (encZY z y) := by
  subst hq
  have e : iq = iF := Algebra.algebra_ext _ _ fun r =>
    congrArg (fun f : ZMod Nock.Atoms.p →+* Kfp => f r) (RingHom.ext_zmod _ _)
  subst e
  intro a
  show FP.atomFP z (leafVal y a.val) = _
  rw [leafVal_small y (ZMod.val_lt a), ZMod.natCast_zmod_val]

/-- **The g5 shape gives `AtomLeaves (encZY z y)`**: every external key is `(⟨z, 0, leafVal y v⟩, 0, 0, idx)`
with `ext idx = atom v`. -/
theorem atomLeaves_of_g5 (z y : Kfp) {vp : List (VKey Kfp)} {ext : ℕ → Option Noun}
    (h : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧
      ∃ v, ext k.2.2.2 = some (.atom v) ∧ k.1 = FP.atomFP z (leafVal y v)) :
    AtomLeaves (encZY z y) vp ext := by
  intro k hk
  obtain ⟨h1, h2, v, h3, h4⟩ := h k hk
  exact ⟨h1, h2, v, h3, h4⟩

end Enc

/-! ## 2. The atom walk's challenge vector -/

section Vec
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

/-- **The atom walk's challenge vector at `frameJ8`**: the atom table's (`y` at leaves `2, 3`). -/
def chalsVJ8 (χ : Coins frameJ8 K) : ℕ → K := chalsAJ8 δ χ

/-- `CorJ8A`'s `hyV`. -/
theorem hyV_J8 (χ : Coins frameJ8 K) :
    chalsVJ8 δ χ 2 = chalsAJ8 δ χ 2 ∧ chalsVJ8 δ χ 3 = chalsAJ8 δ χ 3 := ⟨rfl, rfl⟩

/-- `FinalJ8`'s `hchV`. -/
theorem hchV_J8 (χ : Coins frameJ8 K) : ∀ j, 33 ≤ j → j ≤ 36 → chalsVJ8 δ χ j = VerJ8.chalsMJ8 δ χ j :=
  chalsAJ8_agree δ χ

/-- The atom walk's walk coins (leaves `0, 1`) are `χ₀, χ₁`. -/
theorem chalsVJ8_walk (χ : Coins frameJ8 K) :
    chalsVJ8 δ χ 0 = χ ⟨0, by decide⟩ ∧ chalsVJ8 δ χ 1 = χ ⟨1, by decide⟩ := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [chalsVJ8, chalsAJ8, if_neg (show (0 : ℕ) ≠ 2 by decide), if_neg (show (0 : ℕ) ≠ 3 by decide),
      if_neg (show (1 : ℕ) ≠ 2 by decide), if_neg (show (1 : ℕ) ≠ 3 by decide)]
    rw [chalsMJ8_lo δ χ _ (by norm_num)]
    simp [FrameVS.chalsVS, Chips.ChipRAP.chalsVCL, CellH.hGam, CellH.hRho, FrameVS.toVCL, toVS, toVSQ]

end Vec

/-! ## 3. The corrected atom-walk summand (#9 on the walk-chain coins) -/

def c0 : Fin frameJ8.n := ⟨0, by decide⟩
def c1 : Fin frameJ8.n := ⟨1, by decide⟩

section Walk
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  (δ : K) [Fact (¬ IsSquare δ)]

/-- `(χ₀, χ₁)` in `𝕂` (the 40th's walk-chain coins). -/
def spec01J8 : IOCoinSpec frameJ8 K K := IOCoinSpec.ofPair frameJ8 K c0 c1

theorem spec01J8_dep_card : (spec01J8 (K := K)).dep.card = 2 := rfl

theorem spec01J8_disj : Disjoint (spec01J8 (K := K)).dep (coinsBelow frameJ8 1) := by
  show Disjoint ({c0, c1} : Finset (Fin frameJ8.n)) (coinsBelow frameJ8 1); decide

/-- `y` is a round-0 coin: it is in the corrected summand's read set. -/
theorem yDep_sub : yDep ⊆ coinsBelow frameJ8 1 := by decide

/-- **The corrected #9** (coins `(χ₀, χ₁)`, reading the round-0 coins, weight `|𝕂|·15·AW`): `walkEvent` at the
atom walk's data. -/
def atomWalkJ8C {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop)
    (wd : Tr → Coins frameJ8 K → WalkVCL.WalkData q (Quad δ)) (AW : ℕ) (hAW : ∀ tr χ, (wd tr χ).h ≤ AW)
    (hreads : ∀ Q, St Q → ReadsOnC frameJ8 (coinsBelow frameJ8 1) (fun χ => wd (Q χ) χ)) :
    BadSummand frameJ8 K Tr St :=
  specSummand (spec01J8 (K := K)) (coinsBelow frameJ8 1) spec01J8_disj St
    (fun tr χ => WalkVCL.walkEvent δ (wd tr χ))
    (Fintype.card K * (15 * AW)) (fun tr χ => WalkVCL.walkEvent_card δ _ (hAW tr χ))
    (fun Q hQ χ χ' h => by simp only [hreads Q hQ χ χ' h])

theorem mem_atomWalkJ8C {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop)
    (wd : Tr → Coins frameJ8 K → WalkVCL.WalkData q (Quad δ)) (AW : ℕ) (hAW hreads) (tr : Tr)
    (χ : Coins frameJ8 K) :
    (atomWalkJ8C δ St wd AW hAW hreads).mem tr χ ↔ (χ c0, χ c1) ∈ WalkVCL.walkEvent δ (wd tr χ) :=
  mem_specSummand _ _ _ _ _ _ _ _ tr χ

/-- **The corrected #9 has #9's `ε`** (`|𝕂|·15·AW / |𝕂|²`): `boundJ8P` and the figure are unchanged. -/
theorem epsilon_atomWalkJ8C {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop)
    (wd : Tr → Coins frameJ8 K → WalkVCL.WalkData q (Quad δ)) (AW : ℕ) (hAW hreads) :
    epsilonOf [atomWalkJ8C δ St wd AW hAW hreads] =
      ((Fintype.card K * (15 * AW) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 2 := by
  erw [atomWalkJ8C, eps_specSummand, spec01J8_dep_card]

/-- The same `ε` as `WeightsJ8.atomWalkJ8` (at any read-set witness for the latter). -/
theorem epsilon_atomWalkJ8C_eq {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop)
    (wd : Tr → Coins frameJ8 K → WalkVCL.WalkData q (Quad δ)) (AW : ℕ) (hAW hreads hreads') :
    epsilonOf [atomWalkJ8C δ St wd AW hAW hreads] = epsilonOf [atomWalkJ8 δ St wd AW hAW hreads'] := by
  rw [epsilon_atomWalkJ8C, atomWalkJ8]
  erw [eps_specSummand, specW_dep_card]

end Walk

section HoutV
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]

/-- **`CorJ8A`'s `houtV`** from the corrected #9: outside it, the atom walk's coins `(chalsVJ8 0, chalsVJ8 1)` are
outside `walkEvent` of its data. -/
theorem houtV_of_outside {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop)
    (wd : Tr → Coins frameJ8 K → WalkVCL.WalkData q (Quad (algebraMap (ZMod p) K δ))) (AW : ℕ) (hAW hreads)
    {tr : Tr} {χ : Coins frameJ8 K}
    (h : ¬ (atomWalkJ8C (algebraMap (ZMod p) K δ) St wd AW hAW hreads).mem tr χ) :
    (chalsVJ8 δ χ 0, chalsVJ8 δ χ 1) ∉ WalkVCL.walkEvent (algebraMap (ZMod p) K δ) (wd tr χ) := by
  rw [(chalsVJ8_walk δ χ).1, (chalsVJ8_walk δ χ).2]
  rwa [mem_atomWalkJ8C] at h

end HoutV

end

end Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8
