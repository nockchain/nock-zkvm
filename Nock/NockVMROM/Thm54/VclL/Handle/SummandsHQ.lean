/-
  Nock/NockVMROM/Thm54/VclL/Handle/SummandsHQ.lean

* `projQ` — a VSQ trace pair read at the VS widths (compute `70 ≤ 85`, cell `232 ≤ 238`, walk
    `151 ≤ 166`, same column indices); `staged_round0Q` / `listsQ_staged`: along a VSQ-staged
    strategy the round-0 record lists `reqX0 / provX0 / reqP0 / provP0` of the projection (at the
    transported datum `toVSV`) are coin-independent.
  * `ioSpecHQ` — the `𝕂′` handle coins `γH′ = χ₁₁ + χ₁₅√δ`, `ρH′ = χ₁₂ + χ₁₆√δ` as an `IOCoinSpec`.
  * `evXQ / evPQ` — the weighted IO failure events of the LIFTED round-0 lists (`liftRec`, the
    entrywise `𝕂 → 𝕂′` lift of `BalanceQ`) on `(γH′, ρH′)`, guarded by the consumer budgets `3N + W` /
    `2N`; cards `≤ ioFUB 5 (3N + W) T |𝕂′|` / `ioFUB 5 (2N) (2W) |𝕂′|`.
  * **`ioSummandHXQ` / `ioSummandHPQ`** — `BadSummand`s on the four coins `{11, 15, 12, 16}`, `dep = ∅`
    (round-0 data); the weights are the two handle numerators of `boundVCLHQ''` (EpsFigVSQ, over
    `|𝕂|⁴`).  `mem_ioSummandHXQ / HPQ`: membership is `(γH′, ρH′) ∈ evXQ / evPQ`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChoiceQ
import Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ
import Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.SummandsHQ

open Nock Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.IOVS Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.ChoiceQ Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The projection to the VS widths -/

section Proj
variable {F : Type} [Field F] (hT hP hC : ℕ)

/-- The VSQ trace pair. -/
abbrev TrVSQ (F : Type) [Field F] (hT hP hC : ℕ) := Traces F (tableVSQ hC) (shapeVSQ hT hP)

theorem widthC_le : (tableVS hC).width ≤ (tableVSQ hC).width := by
  show ChipH.widthH ≤ ChipHQ.widthHQ; decide

theorem widthM_le (t : Fin 2) :
    ((shapeVS hT hP).table t).width ≤ ((shapeVSQ hT hP).table t).width := by
  show (if (t : ℕ) = 0 then (⟨232, colRoundCH, hT⟩ : TableSpec) else ⟨151, colRoundWH, hP⟩).width ≤
    (if (t : ℕ) = 0 then (⟨238, colRoundCHQ, hT⟩ : TableSpec) else ⟨166, colRoundWHQ, hP⟩).width
  split_ifs <;> (show (_ : ℕ) ≤ _; norm_num)

/-- **A VSQ trace pair read at the VS widths** (same column indices). -/
def projQ (tr : TrVSQ F hT hP hC) : TrVS F hT hP hC :=
  (fun j => tr.1 (Fin.castLE (widthC_le hC) j), fun t j => tr.2 t (Fin.castLE (widthM_le hT hP t) j))

variable {K : Type}

/-- Staged VSQ traces agree, across coins, on every round-0 column of the projection. -/
theorem staged_round0Q (Q : Coins frameVSQ K → TrVSQ F hT hP hC)
    (hQ : TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP) Q) (χ χ' : Coins frameVSQ K) :
    (∀ j : Fin (tableVS hC).width, (j : ℕ) < 43 → (projQ hT hP hC (Q χ)).1 j = (projQ hT hP hC (Q χ')).1 j) ∧
      (∀ j : Fin ((shapeVS hT hP).table (tCS hT hP)).width, (j : ℕ) < 130 →
        (projQ hT hP hC (Q χ)).2 (tCS hT hP) j = (projQ hT hP hC (Q χ')).2 (tCS hT hP) j) ∧
      (∀ j : Fin ((shapeVS hT hP).table (tWS hT hP)).width, (j : ℕ) < 25 →
        (projQ hT hP hC (Q χ)).2 (tWS hT hP) j = (projQ hT hP hC (Q χ')).2 (tWS hT hP) j) := by
  refine ⟨fun j hj => hQ.1 _ χ χ' fun i hi => ?_, fun j hj => hQ.2 _ _ χ χ' fun i hi => ?_,
    fun j hj => hQ.2 _ _ χ χ' fun i hi => ?_⟩
  · exfalso
    have : (tableVSQ hC).colRound (Fin.castLE (widthC_le hC) j) = 0 := by
      simp only [tableVSQ, ChipH.round0W, Fin.val_castLE]; exact if_pos (by show (j:ℕ) < 43; omega)
    omega
  · exfalso
    have : ((shapeVSQ hT hP).table (tCS hT hP)).colRound (Fin.castLE (widthM_le hT hP (tCS hT hP)) j) = 0 := by
      change colRoundCHQ _ = 0
      simp only [colRoundCHQ, Fin.val_castLE]; rw [if_pos hj]
    omega
  · exfalso
    have : ((shapeVSQ hT hP).table (tWS hT hP)).colRound (Fin.castLE (widthM_le hT hP (tWS hT hP)) j) = 0 := by
      change colRoundWHQ _ = 0
      simp only [colRoundWHQ, Fin.val_castLE]; rw [if_pos hj]
    omega

variable [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F] [Fintype K] [DecidableEq K]
  [Fintype F]

/-- **The projected round-0 record lists are coin-independent along a VSQ-staged strategy.** -/
theorem listsQ_staged (V : VerifierData F K hC (shapeVSQ hT hP)) (Q : Coins frameVSQ K → TrVSQ F hT hP hC)
    (hQ : TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP) Q) (χ χ' : Coins frameVSQ K) :
    reqX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (Q χ)) =
        reqX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (Q χ')) ∧
      provX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (Q χ)) =
        provX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (Q χ')) ∧
      reqP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (Q χ)) =
        reqP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (Q χ')) ∧
      provP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (Q χ)) =
        provP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC (Q χ')) := by
  obtain ⟨h1, h2, h3⟩ := staged_round0Q hT hP hC Q hQ χ χ'
  set V' := toVSV hT hP hC V
  have hc := compReqs_congr (K := K) V'.computeNodes V'.orbitC (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) _ _ h1
  have hw := walkLists_congr V'.basis (V'.memNodes (tWS hT hP)) (V'.orbitM (tWS hT hP)) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) _ _ h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold reqX0; rw [hc.1, hw.1]
  · unfold provX0
    exact cellProvs_congr V'.basis _ _ _ _ _ _ _ _ h2
  · unfold reqP0; rw [hc.2]
  · unfold provP0; rw [hw.2]

end Proj

/-! ## 2. The `𝕂′` handle coins -/

section Spec
variable {K : Type} [Field K] (δ : K) [Fact (¬ IsSquare δ)]

/-- **The `𝕂′` handle coins** `γH′ = χ₁₁ + χ₁₅√δ`, `ρH′ = χ₁₂ + χ₁₆√δ`. -/
def ioSpecHQ : IOCoinSpec frameVSQ K (Quad δ) :=
  IOCoinSpec.ofExt frameVSQ (Quad.mk δ) (Chips.quadMk_inj δ) (⟨11, by decide⟩, cGamHi)
    (⟨12, by decide⟩, cRhoHi)

theorem ioSpecHQ_pair (χ : Coins frameVSQ K) :
    (ioSpecHQ δ).pair χ = (Quad.mk δ (χ ⟨11, by decide⟩) (χ cGamHi), Quad.mk δ (χ ⟨12, by decide⟩) (χ cRhoHi)) :=
  rfl

end Spec

/-! ## 3. The lifted events and the two summands -/

section Summands
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP hC : ℕ)

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The entrywise `𝕂 → 𝕂′` lift of a consumer list. -/
def liftReqs (l : List (Fin 5 → K)) : List (Fin 5 → 𝕂′) := l.map (liftRec (L := 𝕂′))

/-- The entrywise lift of a weighted provider list. -/
def liftProvs (l : List ((Fin 5 → K) × K)) : List ((Fin 5 → 𝕂′) × 𝕂′) :=
  l.map fun q => (liftRec (L := 𝕂′) q.1, algebraMap K 𝕂′ q.2)

open Classical in
/-- **The `𝕂′` export event** (lifted round-0 lists of the projection; budget `3N + W`). -/
def evXQ (V : VerifierData F K hC (shapeVSQ hT hP)) (tr : TrVSQ F hT hP hC) : Finset (𝕂′ × 𝕂′) :=
  if (reqX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC tr)).length ≤ 3 * V.N + V.memRows (tWS hT hP) then
    IOFailureEventW (liftReqs δF (reqX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC tr)))
      (liftProvs δF (provX0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC tr)))
  else ∅

open Classical in
/-- **The `𝕂′` path event** (budget `2N`). -/
def evPQ (V : VerifierData F K hC (shapeVSQ hT hP)) (tr : TrVSQ F hT hP hC) : Finset (𝕂′ × 𝕂′) :=
  if (reqP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC tr)).length ≤ 2 * V.N then
    IOFailureEventW (liftReqs δF (reqP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC tr)))
      (liftProvs δF (provP0 hT hP hC (toVSV hT hP hC V) (projQ hT hP hC tr)))
  else ∅

theorem evXQ_card (V : VerifierData F K hC (shapeVSQ hT hP)) (tr : TrVSQ F hT hP hC) :
    (evXQ δF hT hP hC V tr).card ≤
      ioFailureUnionBound 5 (3 * V.N + V.memRows (tWS hT hP)) (V.memRows (tCS hT hP)) (Fintype.card 𝕂′) := by
  unfold evXQ
  split_ifs with hl
  · refine (IOFailureEventW_card_le _ _).trans (ioUB_mono _ _ _ _ _ _ ?_ ?_)
    · simpa [liftReqs] using hl
    · simp only [liftProvs, List.length_map]
      exact le_of_eq (provX0_length hT hP hC (toVSV hT hP hC V) (projQ hT hP hC tr))
  · simp

theorem evPQ_card (V : VerifierData F K hC (shapeVSQ hT hP)) (tr : TrVSQ F hT hP hC) :
    (evPQ δF hT hP hC V tr).card ≤
      ioFailureUnionBound 5 (2 * V.N) (2 * V.memRows (tWS hT hP)) (Fintype.card 𝕂′) := by
  unfold evPQ
  split_ifs with hl
  · refine (IOFailureEventW_card_le _ _).trans (ioUB_mono _ _ _ _ _ _ ?_ ?_)
    · simpa [liftReqs] using hl
    · simp only [liftProvs, List.length_map]
      exact le_of_eq (provP0_length hT hP hC (toVSV hT hP hC V) (projQ hT hP hC tr))
  · simp

/-- **The `𝕂′` handle-export IO summand** (coins `{11, 15, 12, 16}`, `dep = ∅`). -/
def ioSummandHXQ (V : VerifierData F K hC (shapeVSQ hT hP)) :
    BadSummand frameVSQ K (TrVSQ F hT hP hC) (TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP)) where
  coins := (ioSpecHQ (algebraMap F K δF)).dep
  dep := ∅
  disj := Finset.disjoint_empty_right _
  badSet tr _ := Finset.univ.filter fun v =>
    (ioSpecHQ (algebraMap F K δF)).pair (extIO (ioSpecHQ (algebraMap F K δF)) v) ∈ evXQ δF hT hP hC V tr
  weight := ioFailureUnionBound 5 (3 * V.N + V.memRows (tWS hT hP)) (V.memRows (tCS hT hP))
    (Fintype.card 𝕂′)
  card_le tr _ := by
    refine le_trans (Finset.card_le_card_of_injOn
      (fun v => (ioSpecHQ (algebraMap F K δF)).pair (extIO (ioSpecHQ (algebraMap F K δF)) v)) ?_ ?_)
      (evXQ_card δF hT hP hC V tr)
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
      exact hv
    · intro v _ v' _ h; exact extIO_inj _ h
  readsOn Q hQ χ χ' _ := by
    obtain ⟨e1, e2, -, -⟩ := listsQ_staged hT hP hC V Q hQ χ χ'
    simp only [evXQ, e1, e2]; rfl

/-- **The `𝕂′` handle-path IO summand** (coins `{11, 15, 12, 16}`, `dep = ∅`). -/
def ioSummandHPQ (V : VerifierData F K hC (shapeVSQ hT hP)) :
    BadSummand frameVSQ K (TrVSQ F hT hP hC) (TracesStaged frameVSQ (tableVSQ hC) (shapeVSQ hT hP)) where
  coins := (ioSpecHQ (algebraMap F K δF)).dep
  dep := ∅
  disj := Finset.disjoint_empty_right _
  badSet tr _ := Finset.univ.filter fun v =>
    (ioSpecHQ (algebraMap F K δF)).pair (extIO (ioSpecHQ (algebraMap F K δF)) v) ∈ evPQ δF hT hP hC V tr
  weight := ioFailureUnionBound 5 (2 * V.N) (2 * V.memRows (tWS hT hP)) (Fintype.card 𝕂′)
  card_le tr _ := by
    refine le_trans (Finset.card_le_card_of_injOn
      (fun v => (ioSpecHQ (algebraMap F K δF)).pair (extIO (ioSpecHQ (algebraMap F K δF)) v)) ?_ ?_)
      (evPQ_card δF hT hP hC V tr)
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
      exact hv
    · intro v _ v' _ h; exact extIO_inj _ h
  readsOn Q hQ χ χ' _ := by
    obtain ⟨-, -, e3, e4⟩ := listsQ_staged hT hP hC V Q hQ χ χ'
    simp only [evPQ, e3, e4]; rfl

theorem mem_ioSummandHXQ (V : VerifierData F K hC (shapeVSQ hT hP)) (tr : TrVSQ F hT hP hC)
    (χ : Coins frameVSQ K) :
    (ioSummandHXQ δF hT hP hC V).mem tr χ ↔ (gamHQ δF χ, rhoHQ δF χ) ∈ evXQ δF hT hP hC V tr := by
  unfold BadSummand.mem
  show (fun i : (ioSpecHQ (algebraMap F K δF)).dep => χ i) ∈
      (Finset.univ.filter fun v : (ioSpecHQ (algebraMap F K δF)).dep → K =>
        (ioSpecHQ (algebraMap F K δF)).pair (extIO (ioSpecHQ (algebraMap F K δF)) v) ∈
          evXQ δF hT hP hC V tr) ↔ _
  rw [Finset.mem_filter, pair_extIO, ioSpecHQ_pair]
  simp [gamHQ, rhoHQ]

theorem mem_ioSummandHPQ (V : VerifierData F K hC (shapeVSQ hT hP)) (tr : TrVSQ F hT hP hC)
    (χ : Coins frameVSQ K) :
    (ioSummandHPQ δF hT hP hC V).mem tr χ ↔ (gamHQ δF χ, rhoHQ δF χ) ∈ evPQ δF hT hP hC V tr := by
  unfold BadSummand.mem
  show (fun i : (ioSpecHQ (algebraMap F K δF)).dep => χ i) ∈
      (Finset.univ.filter fun v : (ioSpecHQ (algebraMap F K δF)).dep → K =>
        (ioSpecHQ (algebraMap F K δF)).pair (extIO (ioSpecHQ (algebraMap F K δF)) v) ∈
          evPQ δF hT hP hC V tr) ↔ _
  rw [Finset.mem_filter, pair_extIO, ioSpecHQ_pair]
  simp [gamHQ, rhoHQ]

/-- The four handle coordinates: the summands' coin count is `4` (so `|𝕂|⁴` in `epsilonOf`). -/
theorem ioSpecHQ_dep_card : (ioSpecHQ (algebraMap F K δF)).dep.card = 4 := by
  show ({⟨11, by decide⟩, cGamHi, ⟨12, by decide⟩, cRhoHi} : Finset (Fin frameVSQ.n)).card = 4
  rfl

end Summands

end

end Nock.NockVMROM.Thm54.VclL.Handle.SummandsHQ
