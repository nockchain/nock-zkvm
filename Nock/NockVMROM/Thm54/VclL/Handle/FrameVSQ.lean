/-
  Nock/NockVMROM/Thm54/VclL/Handle/FrameVSQ.lean

  Additive: no existing module changed.

  * `frameVSQ` — 17 coins: `frameVS`'s fifteen (`0..10` `frameVCL`, `11 / 12` Re `γH / ρH`, `13 / 14`
    `αW / γW`), then `15 / 16` = Im `γH / ρH`, all four handle coordinates sampled after round 0, exactly
    where `γH, ρH` are sampled today.  `γH′ = χ₁₁ + χ₁₅√δ`, `ρH′ = χ₁₂ + χ₁₆√δ` (as the 39th's IO
    `γ′ = χ₄ + χ₆√δ`).  `toVS` forgets the two Im coins.
  * coin maps: the compute challenge vector `chalVHQ` (limbs `0..11` as `chalVH` at `toVS`, `12..14`
    Im `γH`, `15..17` Im `ρH`, as `ChipHQ` reads them); the memory challenge vector `chalsVSQ` (leaves
    `33 / 34` Re, `35 / 36` Im of `γH / ρH`, as `HQ.gamQ / rhoQ` read them).
  * publics: compute `pubVHQ` (`pubVH` at `toVS` on `0..20`, `21..23 / 24..26` = Im `ρ₃ / ρ₄`); cell
    `pubsCHQ` (`4 / 5` = `ρ₃ + yH′`), walk `pubsWHQ` (`4 / 5` = `yH′`, `6 / 7` = `ρ₄`), `yH′ ∈ 𝕂′`.
  * `GoodCVSQ` = `GoodCVS` WITHOUT `Im ρ₃ = Im ρ₄ = 0` (the handle terminals are full `𝕂′` values now).
  * tables `tableVSQ` (`85`), `shapeVSQ` (`238 / 166`), cores `compCoreVSQ` / `memCoreVSQ` (summands a
    parameter, `Honest := Empty`, as `FrameVS`), and `compute_factsQ` / `cell_factsQ` / `walk_factsQ`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
import Nock.NockVMROM.Thm54.VclL.Handle.MemHQ
import Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
import Nock.Tactic.DeriveFintypeFix

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The frame and the coin maps -/

/-- **The `𝕂′` VS frame**: `frameVS`'s fifteen coins, then Im `γH`, Im `ρH`, sampled after round 0. -/
def frameVSQ : CoinFrame where
  n := 17
  sampledAfter := fun i => ![1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] i

def cGamHi : Fin frameVSQ.n := ⟨15, by decide⟩
def cRhoHi : Fin frameVSQ.n := ⟨16, by decide⟩

theorem lt_frameVSQ (i : Fin frameVS.n) : (i : ℕ) < frameVSQ.n := by
  have := i.isLt; change (i : ℕ) < 15 at this; change (i : ℕ) < 17; omega

/-- The first fifteen coins. -/
def toVS {K : Type} (χ : Coins frameVSQ K) : Coins frameVS K := fun i => χ ⟨i, lt_frameVSQ i⟩

/-- `frameVS`'s round map is `frameVSQ`'s on the first fifteen coins. -/
theorem toVS_sampled (i : Fin frameVS.n) :
    frameVS.sampledAfter i = frameVSQ.sampledAfter ⟨i, lt_frameVSQ i⟩ := by
  fin_cases i <;> rfl

/-- The four `𝕂′` handle coordinates are sampled after round 0, where `γH, ρH` are today. -/
theorem frameVSQ_handle_round0 :
    frameVSQ.sampledAfter ⟨11, by decide⟩ = 0 ∧ frameVSQ.sampledAfter ⟨12, by decide⟩ = 0 ∧
      frameVSQ.sampledAfter cGamHi = 0 ∧ frameVSQ.sampledAfter cRhoHi = 0 := by decide

section Coins
variable {F K : Type} [Field F] [Field K] [Algebra F K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- The `𝕂′` handle coins `γH′ = χ₁₁ + χ₁₅√δ`, `ρH′ = χ₁₂ + χ₁₆√δ`. -/
def gamHQ (χ : Coins frameVSQ K) : Quad (algebraMap F K δF) :=
  Quad.mk _ (χ ⟨11, by decide⟩) (χ cGamHi)
def rhoHQ (χ : Coins frameVSQ K) : Quad (algebraMap F K δF) :=
  Quad.mk _ (χ ⟨12, by decide⟩) (χ cRhoHi)

/-- **The memory challenge vector at VSQ**: leaves `33 / 34` Re, `35 / 36` Im of `γH / ρH`; every
other leaf is `chalsVCL` at the first eleven coins. -/
def chalsVSQ [Fintype K] (χ : Coins frameVSQ K) (j : ℕ) : K :=
  if j = 35 then χ cGamHi else if j = 36 then χ cRhoHi else chalsVS δF (toVS χ) j

/-- The compute's `𝕂` coins by slot: `0 γH`, `1 ρH`, `2 αW`, `3 γW` (Re), `4` Im `γH`, `5` Im `ρH`. -/
def coinHQ (χ : Coins frameVSQ K) (q : ℕ) : K :=
  if q < 4 then coinH (toVS χ) q else if q = 4 then χ cGamHi else χ cRhoHi

/-- **The compute challenge vector** (`𝔽`-limbs `3q .. 3q+2` of `coinHQ q`, `q < 6`). -/
def chalVHQ (b : Basis (Fin 3) F K) (χ : Coins frameVSQ K) : ℕ → F :=
  fun j => if j < 18 then coord b (coinHQ χ (j / 3)) ⟨j % 3, Nat.mod_lt j (by decide)⟩ else 0

theorem chalVHQ_old (b : Basis (Fin 3) F K) (χ : Coins frameVSQ K) (j : ℕ) (hj : j < 12) :
    chalVHQ b χ j = chalVH b (toVS χ) j := by
  have h4 : j / 3 < 4 := by omega
  simp only [chalVHQ, chalVH, coinHQ, if_pos (show j < 18 by omega), if_pos hj, if_pos h4]

end Coins

/-! ## 2. Publics -/

section Pubs
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- **The compute publics at VSQ**: `pubVH` on `0..20`, Im `ρ₃` at `21..23`, Im `ρ₄` at `24..26`. -/
def pubVHQ (b : Basis (Fin 3) F K) (c : P8PublicClaim) (m : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVSQ K) : ℕ → F :=
  fun j =>
    if j < 21 then pubVH δF b c m ρ (toVS χ) j
    else if h1 : j < 24 then coord b (Quad.im _ (ρ 3)) ⟨j - 21, by omega⟩
    else if h2 : j < 27 then coord b (Quad.im _ (ρ 4)) ⟨j - 24, by omega⟩
    else 0

/-- The cell twin's publics: `pubsC` at the fingerprint terminals, `4 / 5` = `ρ₃ + yH′`. -/
def pubsCHQ (ρ : Fin 5 → Quad (algebraMap F K δF)) (y yH : Quad (algebraMap F K δF)) (i : ℕ) : K :=
  if i = 4 then Quad.re _ (ρ 3 + yH) else if i = 5 then Quad.im _ (ρ 3 + yH)
  else pubsC δF (rho3 δF ρ) y i

/-- The walk twin's publics: `pubsP` at the fingerprint terminals, `4 / 5` = `yH′`, `6 / 7` = `ρ₄`. -/
def pubsWHQ (ρ : Fin 5 → Quad (algebraMap F K δF)) (y yH : Quad (algebraMap F K δF)) (i : ℕ) : K :=
  if i = 4 then Quad.re _ yH else if i = 5 then Quad.im _ yH
  else if i = 6 then Quad.re _ (ρ 4) else if i = 7 then Quad.im _ (ρ 4)
  else pubsP δF (rho3 δF ρ) y i

end Pubs

/-! ## 3. Tables and the memory shape -/

/-- The VSQ compute table: width `85`, the `43` handle/control columns in round 0, the rest in 1. -/
def tableVSQ (hC : ℕ) : TableSpec where
  width := ChipHQ.widthHQ
  colRound := fun j => if (j : ℕ) < ChipH.round0W then 0 else 1
  height := hC

/-- The `𝕂′` cell twin's rounds: base `0..129` in 0, round-1 roles `130..183` in 1, the rest in 2. -/
def colRoundCHQ (j : Fin 238) : ℕ := if (j : ℕ) < 130 then 0 else if (j : ℕ) < 184 then 1 else 2

/-- The `𝕂′` walk twin's rounds: base `0..24` in 0, round-1 roles `25..96` in 1, the rest in 2. -/
def colRoundWHQ (j : Fin 166) : ℕ := if (j : ℕ) < 25 then 0 else if (j : ℕ) < 97 then 1 else 2

/-- **The VSQ memory shape**: cell twin `238`, walk twin `166`. -/
abbrev shapeVSQ (hT hP : ℕ) : MemShape := shapeVCL hT hP 238 166 colRoundCHQ colRoundWHQ

def tCQ (hT hP : ℕ) : Fin (shapeVSQ hT hP).k := ⟨0, by show 0 < 2; omega⟩
def tWQ (hT hP : ℕ) : Fin (shapeVSQ hT hP).k := ⟨1, by show 1 < 2; omega⟩

/-! ## 4. The chips -/

section Chips
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr : ℕ) {hC : ℕ}

/-- **What the VSQ compute chip enforces**: `GoodCVS` without the two Im conditions. -/
def GoodCVSQ {S : MemShape} (V : VerifierData F K hC S) (x : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVSQ K) : Prop :=
  V.AdjacentC ∧ Function.Injective V.computeNodes ∧ 2 ^ 63 < ringChar F ∧
    ρ 0 = claimValSum δF V.claim x (toVS χ) ∧ ρ 1 = 0

open Classical in
/-- **The VSQ compute chip**: `computeChipVCLHQ` at `chalVHQ` / `pubVHQ` under `GoodCVSQ`, else rejecting. -/
def chipCVSQ {S : MemShape} (V : VerifierData F K hC S) (x : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVSQ K) : FixedPreprocessingRAP F :=
  if GoodCVSQ δF V x ρ χ then
    ChipHQ.computeChipVCLHQ V.hN V.computeNodes V.basis δF (chalVHQ V.basis χ)
      (pubVHQ δF V.basis V.claim x ρ χ) V.orbitC
  else rejectChipW ChipHQ.widthHQ V.computeNodes V.orbitC

theorem chipCVSQ_width {S : MemShape} (V : VerifierData F K hC S) (x : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVSQ K) :
    (chipCVSQ δF V x ρ χ).rap.w = (tableVSQ hC).width := by
  unfold chipCVSQ; split_ifs <;> rfl

open Classical in
/-- **The VSQ memory chips**: table `0` the `𝕂′` cell twin under `GoodM`, table `1` the `𝕂′` walk
twin under `GoodW kr`, each rejecting otherwise. -/
def chipMVSQ (V : VerifierData F K hC (shapeVSQ hT hP)) (t : Fin (shapeVSQ hT hP).k)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (yy : Quad (algebraMap F K δF) × Quad (algebraMap F K δF))
    (χ : Coins frameVSQ K) : FixedPreprocessingRAP F :=
  if (t : ℕ) = 0 then
    (if GoodM V t then
      cellChipHQ δF V.basis (V.hM t) (V.memNodes t) (V.orbitM t) (chalsVSQ δF χ) (pubsCHQ δF ρ yy.1 yy.2)
    else rejectChipW 238 (V.memNodes t) (V.orbitM t))
  else
    (if GoodW V t kr then
      walkChipHQ δF kr V.basis (V.hM t) (V.memNodes t) (V.orbitM t) (chalsVSQ δF χ) (pubsWHQ δF ρ yy.1 yy.2)
    else rejectChipW 166 (V.memNodes t) (V.orbitM t))

theorem chipMVSQ_width (V : VerifierData F K hC (shapeVSQ hT hP)) (t : Fin (shapeVSQ hT hP).k)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (yy : Quad (algebraMap F K δF) × Quad (algebraMap F K δF))
    (χ : Coins frameVSQ K) :
    (chipMVSQ δF hT hP kr V t ρ yy χ).rap.w = ((shapeVSQ hT hP).table t).width := by
  unfold chipMVSQ
  split_ifs with ht h1 h2
  · rw [cellChipHQ_width]; change _ = (if (t : ℕ) = 0 then (⟨238, colRoundCHQ, hT⟩ : TableSpec) else ⟨166, colRoundWHQ, hP⟩).width; rw [if_pos ht]
  · rw [rejectChipW_w]; change _ = (if (t : ℕ) = 0 then (⟨238, colRoundCHQ, hT⟩ : TableSpec) else ⟨166, colRoundWHQ, hP⟩).width; rw [if_pos ht]
  · rw [walkChipHQ_width]; change _ = (if (t : ℕ) = 0 then (⟨238, colRoundCHQ, hT⟩ : TableSpec) else ⟨166, colRoundWHQ, hP⟩).width; rw [if_neg ht]
  · rw [rejectChipW_w]; change _ = (if (t : ℕ) = 0 then (⟨238, colRoundCHQ, hT⟩ : TableSpec) else ⟨166, colRoundWHQ, hP⟩).width; rw [if_neg ht]

end Chips

/-! ## 5. The cores -/

section Cores
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)

/-- The summand-list type of the VSQ instance. -/
abbrev SummandsVSQ := List (BadSummand frameVSQ K (Traces F (tableVSQ hC) (shapeVSQ hT hP))
  (TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP)))

/-- Compute consumer bounds (as `reqBoundVS`). -/
def reqBoundVSQ (V : VerifierData F K hC (shapeVSQ hT hP)) : Fin 5 → ℕ :=
  ![3, 0, 0, 3 * V.N, 2 * V.N]

/-- Memory-internal consumer bounds (as `internalBoundVS`). -/
def internalBoundVSQ (V : VerifierData F K hC (shapeVSQ hT hP)) : Fin 5 → ℕ :=
  ![2 * V.memRows (tCQ hT hP), V.memRows (tWQ hT hP), 0, V.memRows (tWQ hT hP), 0]

/-- **`CompCoreVSQ`**: the compute core at `chipCVSQ` (`85`); summands a parameter. -/
def compCoreVSQ (sumC : VerifierData F K hC (shapeVSQ hT hP) → ClaimMsgVS → SummandsVSQ (F := F) (K := K) hT hP hC) :
    CompCore F K (Quad (algebraMap F K δF)) frameVSQ hC (shapeVSQ hT hP) (tableVSQ hC) 5 where
  Msg0 := ClaimMsgVS
  chip := fun V x ρ χ => chipCVSQ δF V x ρ χ
  chip_width := fun V x ρ χ => chipCVSQ_width δF V x ρ χ
  reqBound := reqBoundVSQ hT hP hC
  summands := sumC
  Honest := Empty
  honestV := fun H => H.elim
  honestQ := fun H => H.elim
  honestReq := fun H => H.elim
  honest_staged := fun H => H.elim
  honestBad := fun H => H.elim

/-- **`MemCoreVSQ`**: the memory core at `chipMVSQ` (`238 / 166`); summands a parameter. -/
def memCoreVSQ (sumM : VerifierData F K hC (shapeVSQ hT hP) → Unit → SummandsVSQ (F := F) (K := K) hT hP hC) :
    MemCore F K (Quad (algebraMap F K δF)) frameVSQ hC (shapeVSQ hT hP) (tableVSQ hC) 5 where
  Msg0 := Unit
  Msg2 := Quad (algebraMap F K δF) × Quad (algebraMap F K δF)
  chip := fun V t _ ρ yy χ => chipMVSQ δF hT hP kr V t ρ yy χ
  chip_width := fun V t _ ρ yy χ => chipMVSQ_width δF hT hP kr V t ρ yy χ
  internalBound := internalBoundVSQ hT hP hC
  summands := sumM
  Honest := Empty
  honestV := fun H => H.elim
  honestQ := fun H => H.elim
  honestReq := fun H => H.elim
  honest_staged := fun H => H.elim
  honestBad := fun H => H.elim

/-! ## 6. Acceptance at the cores unpacks to the three chips -/

variable {sumC : VerifierData F K hC (shapeVSQ hT hP) → ClaimMsgVS → SummandsVSQ (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVSQ hT hP) → Unit → SummandsVSQ (F := F) (K := K) hT hP hC}

/-- **The compute side of `AcceptsG` at VSQ**: `GoodCVSQ` and `computeChipVCLHQ` acceptance. -/
theorem compute_factsQ (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K)
    (h : AcceptsG V msg χ) :
    GoodCVSQ δF V msg.msg0C (msg.requests χ) χ ∧
      RAP.SatisfiesWithPreprocessing
        (ChipHQ.computeChipVCLHQ V.hN V.computeNodes V.basis δF (chalVHQ V.basis χ)
          (pubVHQ δF V.basis V.claim msg.msg0C (msg.requests χ) χ) V.orbitC)
        (fun j => msg.Qc χ (Fin.cast rfl j)) := by
  classical
  have hc := h.compute
  change RAP.SatisfiesWithPreprocessing (chipCVSQ δF V msg.msg0C (msg.requests χ) χ)
    (fun j => msg.Qc χ (Fin.cast (chipCVSQ_width δF V msg.msg0C (msg.requests χ) χ) j)) at hc
  by_cases hg : GoodCVSQ δF V msg.msg0C (msg.requests χ) χ
  · refine ⟨hg, ?_⟩
    have he : chipCVSQ δF V msg.msg0C (msg.requests χ) χ =
        ChipHQ.computeChipVCLHQ V.hN V.computeNodes V.basis δF (chalVHQ V.basis χ)
          (pubVHQ δF V.basis V.claim msg.msg0C (msg.requests χ) χ) V.orbitC := by
      unfold chipCVSQ; exact if_pos hg
    exact sat_cast_eq he _ rfl _ hc
  · exfalso
    have he : chipCVSQ δF V msg.msg0C (msg.requests χ) χ =
        rejectChipW ChipHQ.widthHQ V.computeNodes V.orbitC := by
      unfold chipCVSQ; exact if_neg hg
    exact not_sat_of_eq_reject _ V.hN V.computeNodes V.orbitC _ he _ _ hc

/-- **The cell side of `AcceptsG` at VSQ**: `GoodM` and `cellChipHQ` acceptance. -/
theorem cell_factsQ (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K)
    (h : AcceptsG V msg χ) :
    GoodM V (tCQ hT hP) ∧ ∃ hw : (cellChipHQ δF V.basis (V.hM (tCQ hT hP)) (V.memNodes (tCQ hT hP))
        (V.orbitM (tCQ hT hP)) (chalsVSQ δF χ) (pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1
          (msg.msg2M χ).2)).rap.w = ((shapeVSQ hT hP).table (tCQ hT hP)).width,
      RAP.SatisfiesWithPreprocessing
        (cellChipHQ δF V.basis (V.hM (tCQ hT hP)) (V.memNodes (tCQ hT hP)) (V.orbitM (tCQ hT hP))
          (chalsVSQ δF χ) (pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2))
        (fun j => msg.Qm χ (tCQ hT hP) (Fin.cast hw j)) := by
  classical
  have hc := h.memory (tCQ hT hP)
  change RAP.SatisfiesWithPreprocessing (chipMVSQ δF hT hP kr V (tCQ hT hP) (msg.requests χ) (msg.msg2M χ) χ)
    (fun j => msg.Qm χ (tCQ hT hP)
      (Fin.cast (chipMVSQ_width δF hT hP kr V (tCQ hT hP) (msg.requests χ) (msg.msg2M χ) χ) j)) at hc
  have h0 : ((tCQ hT hP : Fin (shapeVSQ hT hP).k) : ℕ) = 0 := rfl
  by_cases hg : GoodM V (tCQ hT hP)
  · have he : chipMVSQ δF hT hP kr V (tCQ hT hP) (msg.requests χ) (msg.msg2M χ) χ =
        cellChipHQ δF V.basis (V.hM (tCQ hT hP)) (V.memNodes (tCQ hT hP)) (V.orbitM (tCQ hT hP))
          (chalsVSQ δF χ) (pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) := by
      unfold chipMVSQ; rw [if_pos h0, if_pos hg]
    have hw : (cellChipHQ δF V.basis (V.hM (tCQ hT hP)) (V.memNodes (tCQ hT hP))
        (V.orbitM (tCQ hT hP)) (chalsVSQ δF χ) (pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1
          (msg.msg2M χ).2)).rap.w = ((shapeVSQ hT hP).table (tCQ hT hP)).width := by
      rw [← he]; exact chipMVSQ_width δF hT hP kr V _ _ _ _
    exact ⟨hg, hw, sat_cast_eq he _ hw _ hc⟩
  · exfalso
    have he : chipMVSQ δF hT hP kr V (tCQ hT hP) (msg.requests χ) (msg.msg2M χ) χ =
        rejectChipW 238 (V.memNodes (tCQ hT hP)) (V.orbitM (tCQ hT hP)) := by
      unfold chipMVSQ; rw [if_pos h0, if_neg hg]
    exact not_sat_of_eq_reject _ (V.hM _) (V.memNodes _) (V.orbitM _) _ he _ _ hc

/-- **The walk side of `AcceptsG` at VSQ**: `GoodW kr` and `walkChipHQ` acceptance. -/
theorem walk_factsQ (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K)
    (h : AcceptsG V msg χ) :
    GoodW V (tWQ hT hP) kr ∧ ∃ hw : (walkChipHQ δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP))
        (V.orbitM (tWQ hT hP)) (chalsVSQ δF χ) (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1
          (msg.msg2M χ).2)).rap.w = ((shapeVSQ hT hP).table (tWQ hT hP)).width,
      RAP.SatisfiesWithPreprocessing
        (walkChipHQ δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP)) (V.orbitM (tWQ hT hP))
          (chalsVSQ δF χ) (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2))
        (fun j => msg.Qm χ (tWQ hT hP) (Fin.cast hw j)) := by
  classical
  have hc := h.memory (tWQ hT hP)
  change RAP.SatisfiesWithPreprocessing (chipMVSQ δF hT hP kr V (tWQ hT hP) (msg.requests χ) (msg.msg2M χ) χ)
    (fun j => msg.Qm χ (tWQ hT hP)
      (Fin.cast (chipMVSQ_width δF hT hP kr V (tWQ hT hP) (msg.requests χ) (msg.msg2M χ) χ) j)) at hc
  have h1 : ¬ ((tWQ hT hP : Fin (shapeVSQ hT hP).k) : ℕ) = 0 := Nat.one_ne_zero
  by_cases hg : GoodW V (tWQ hT hP) kr
  · have he : chipMVSQ δF hT hP kr V (tWQ hT hP) (msg.requests χ) (msg.msg2M χ) χ =
        walkChipHQ δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP)) (V.orbitM (tWQ hT hP))
          (chalsVSQ δF χ) (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) := by
      unfold chipMVSQ; rw [if_neg h1, if_pos hg]
    have hw : (walkChipHQ δF kr V.basis (V.hM (tWQ hT hP)) (V.memNodes (tWQ hT hP))
        (V.orbitM (tWQ hT hP)) (chalsVSQ δF χ) (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1
          (msg.msg2M χ).2)).rap.w = ((shapeVSQ hT hP).table (tWQ hT hP)).width := by
      rw [← he]; exact chipMVSQ_width δF hT hP kr V _ _ _ _
    exact ⟨hg, hw, sat_cast_eq he _ hw _ hc⟩
  · exfalso
    have he : chipMVSQ δF hT hP kr V (tWQ hT hP) (msg.requests χ) (msg.msg2M χ) χ =
        rejectChipW 166 (V.memNodes (tWQ hT hP)) (V.orbitM (tWQ hT hP)) := by
      unfold chipMVSQ; rw [if_neg h1, if_neg hg]
    exact not_sat_of_eq_reject _ (V.hM _) (V.memNodes _) (V.orbitM _) _ he _ _ hc

end Cores

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
