/-
  Nock/NockVMROM/Thm54/VclL/Handle/ValIOVS.lean

  Additive.

  * `ioSpecVS`: the validity IO coins `(γ′, ρ′) = (χ₄ + χ₆√δ, χ₅ + χ₇√δ)` (`IOCoinSpec.ofExt`, injective
    on `{4, 5, 6, 7}`, the `ioSpecVCLQuad` pattern at `frameVS`).
  * `valReqs` / `valProvs`: the coin-free record lists of the validity lookup read off a trace pair:
    the verifier's claim records `claimRecs` (reading only `χ₂ χ₃` and the claim message) followed by the
    internal consumers `cVInt` of the RESTRICTED cell twin trace, and the providers `cVRec`, with zero
    coins and zero publics (`cVInt_congr` / `cVRec_congr`: the keys read neither, so `pubsCH` does not
    enter).
  * **`valSummand`**: coins `{4, 5, 6, 7}`, `dep = coinsBelow frameVS 1` (round-1 cell columns `< 184`
    and `χ₂ χ₃`), weight `ioFailureUnionBound 5 (3 + 2T) T |𝕂′|` with `T` the cell rows (no guard: the
    consumer count `≤ 3 + 2T` holds at every trace); `valSummand_mass`: weight `/ |𝕂|⁴ =
    ioFailureUnionBound 5 (3 + 2T) T 1 / |𝕂|²`.
  * **`claims_provided_VS'`**: `claims_provided_VS` with its `hio` discharged by `¬ valSummand.mem`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ClaimVS

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimVS
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The IO coins and the restriction -/

section Coins
variable {K : Type} [Field K] (δ : K) [Fact (¬ IsSquare δ)]

/-- **The validity IO coins at VS**: `γ′ = χ₄ + χ₆√δ`, `ρ′ = χ₅ + χ₇√δ`. -/
def ioSpecVS : IOCoinSpec frameVS K (Quad δ) :=
  IOCoinSpec.ofExt frameVS (Quad.mk δ) (quadMk_inj δ) (⟨4, by decide⟩, ⟨6, by decide⟩)
    (⟨5, by decide⟩, ⟨7, by decide⟩)

theorem ioSpecVS_pair (χ : Coins frameVS K) :
    (ioSpecVS δ).pair χ =
      (Quad.mk δ (χ ⟨4, by decide⟩) (χ ⟨6, by decide⟩), Quad.mk δ (χ ⟨5, by decide⟩) (χ ⟨7, by decide⟩)) :=
  rfl

theorem ioSpecVS_dep_card : (ioSpecVS δ).dep.card = 4 := by
  show ({⟨4, by decide⟩, ⟨6, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩} : Finset (Fin frameVS.n)).card = 4
  decide

theorem ioSpecVS_disj : Disjoint (ioSpecVS δ).dep (coinsBelow frameVS 1) := by
  rw [Finset.disjoint_left]
  intro i hi hb
  simp only [coinsBelow, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  have hi' : i ∈ ({⟨4, by decide⟩, ⟨6, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩} :
      Finset (Fin frameVS.n)) := hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi'
  rcases hi' with rfl | rfl | rfl | rfl <;> revert hb <;> decide

end Coins

theorem shift_lt (j : Fin 225) : shiftCol 129 130 j < 232 := by
  have := j.isLt; unfold shiftCol; split_ifs <;> omega

/-- The restriction of a cell twin trace to the original cell chip's `225` columns (as `restrictCell`). -/
def qrC {F : Type} [Field F] (q : Fin 232 → F[X]) : Fin 225 → F[X] :=
  fun j => q ⟨shiftCol 129 130 j, shift_lt j⟩

/-! ## 2. The coin-free record lists and the summand -/

section Summand

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP hC : ℕ)

/-- **Consumers of the validity lookup**: the verifier's claim records, then the restricted cell
twin's internal consumers (zero coins, zero publics). -/
def valReqs (V : VerifierData F K hC (shapeVS hT hP)) (m : ClaimMsgVS) (tr : TrVS F hT hP hC)
    (χ : Coins frameVS K) : List (Fin 5 → Quad (algebraMap F K δF)) :=
  claimRecs δF V.claim m χ ++
    cVInt δF V.basis (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP)) (fun _ => 0) (fun _ => 0)
      (qrC (tr.2 (tCS hT hP)))

/-- **Providers of the validity lookup** (`(vKeyP, mv)` per cell row). -/
def valProvs (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) :
    List ((Fin 5 → Quad (algebraMap F K δF)) × F) :=
  cVRec δF V.basis (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP)) (fun _ => 0) (fun _ => 0)
    (qrC (tr.2 (tCS hT hP)))

theorem cVInt_length_le {h n w : ℕ} (b : Basis (Fin 3) F K) (nodes : Fin n → F)
    (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) (Q : Fin w → F[X]) :
    (cVInt δF b nodes orbit chals pubs Q).length ≤ 2 * n := by
  unfold cVInt
  rw [List.length_flatMap]
  calc _ ≤ ((List.finRange n).map fun _ => 2).sum := List.sum_le_sum fun i _ => by
          rw [List.length_append]
          have h1 : (if (cellEnvF b nodes orbit chals pubs Q i).trace Cell.wL = 1 then
              [keyVec δF 5 Cell.vKeyL (cellEnvK δF b nodes orbit chals pubs Q i)
                (cellEnvF b nodes orbit chals pubs Q i)] else []).length ≤ 1 := by
            split_ifs <;> simp
          have h2 : (if (cellEnvF b nodes orbit chals pubs Q i).trace Cell.wR = 1 then
              [keyVec δF 5 Cell.vKeyR (cellEnvK δF b nodes orbit chals pubs Q i)
                (cellEnvF b nodes orbit chals pubs Q i)] else []).length ≤ 1 := by
            split_ifs <;> simp
          omega
    _ = 2 * n := by simp [mul_comm]

theorem valReqs_length (V : VerifierData F K hC (shapeVS hT hP)) (m : ClaimMsgVS) (tr : TrVS F hT hP hC)
    (χ : Coins frameVS K) :
    (valReqs δF hT hP hC V m tr χ).length ≤ 3 + 2 * V.memRows (tCS hT hP) := by
  unfold valReqs
  rw [List.length_append]
  exact Nat.add_le_add (claimRecs_length_le δF V.claim m χ) (cVInt_length_le δF _ _ _ _ _ _)

theorem valProvs_length (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) :
    (valProvs δF hT hP hC V tr).length = V.memRows (tCS hT hP) := by
  simp [valProvs, cVRec]

/-- The validity IO event of a trace pair at a coin (only the claim records read the coin, `χ₂ χ₃`). -/
def valEv (V : VerifierData F K hC (shapeVS hT hP)) (m : ClaimMsgVS) (tr : TrVS F hT hP hC)
    (χ : Coins frameVS K) : Finset (Quad (algebraMap F K δF) × Quad (algebraMap F K δF)) :=
  FiniteIO.IOFailureEventW (valReqs δF hT hP hC V m tr χ) (liftWts (valProvs δF hT hP hC V tr))

theorem valEv_card (V : VerifierData F K hC (shapeVS hT hP)) (m : ClaimMsgVS) (tr : TrVS F hT hP hC)
    (χ : Coins frameVS K) :
    (valEv δF hT hP hC V m tr χ).card ≤
      FiniteIO.ioFailureUnionBound 5 (3 + 2 * V.memRows (tCS hT hP)) (V.memRows (tCS hT hP))
        (Fintype.card (Quad (algebraMap F K δF))) := by
  unfold valEv
  refine (FiniteIO.IOFailureEventW_card_le _ _).trans (ioUB_mono _ _ _ _ _ _
    (valReqs_length δF hT hP hC V m tr χ) ?_)
  rw [liftWts_length, valProvs_length]

theorem claimRecs_congr (c : P8PublicClaim) (m : ClaimMsgVS) (χ χ' : Coins frameVS K)
    (h2 : χ ⟨2, by decide⟩ = χ' ⟨2, by decide⟩) (h3 : χ ⟨3, by decide⟩ = χ' ⟨3, by decide⟩) :
    claimRecs δF c m χ = claimRecs δF c m χ' := by
  unfold claimRecs claimKey zVS
  rw [h2, h3]

theorem colRound_shift_le (j : Fin 225) (hj : (j : ℕ) < 183) :
    ((shapeVS hT hP).table (tCS hT hP)).colRound ⟨shiftCol 129 130 j, shift_lt j⟩ ≤ 1 := by
  change colRoundCH ⟨shiftCol 129 130 j, shift_lt j⟩ ≤ 1
  simp only [colRoundCH, shiftCol]
  split_ifs <;> omega

/-- Along a staged strategy, the two record lists read only the coins sampled after round 0. -/
theorem valLists_staged (V : VerifierData F K hC (shapeVS hT hP)) (m : ClaimMsgVS)
    (Q : Coins frameVS K → TrVS F hT hP hC)
    (hQ : TracesStaged frameVS (tableVS hC) (shapeVS hT hP) Q) (χ χ' : Coins frameVS K)
    (hdep : ∀ j ∈ coinsBelow frameVS 1, χ j = χ' j) :
    valReqs δF hT hP hC V m (Q χ) χ = valReqs δF hT hP hC V m (Q χ') χ' ∧
      valProvs δF hT hP hC V (Q χ) = valProvs δF hT hP hC V (Q χ') := by
  have hin : ∀ i : Fin frameVS.n, frameVS.sampledAfter i < 1 → χ i = χ' i := fun i hi =>
    hdep i (by simp only [coinsBelow, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi)
  have hcol : ∀ (j : ℕ) (hj : j < 183),
      qrC ((Q χ).2 (tCS hT hP)) ⟨j, by omega⟩ = qrC ((Q χ').2 (tCS hT hP)) ⟨j, by omega⟩ :=
    fun j hj => hQ.2 (tCS hT hP) _ χ χ' fun i hi =>
      hin i (lt_of_lt_of_le hi (colRound_shift_le hT hP ⟨j, by omega⟩ hj))
  refine ⟨?_, ?_⟩
  · unfold valReqs
    rw [claimRecs_congr δF V.claim m χ χ' (hin _ (by decide)) (hin _ (by decide))]
    congr 1
    exact cVInt_congr δF _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) hcol
  · unfold valProvs
    exact cVRec_congr δF _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) hcol

def valSummand (V : VerifierData F K hC (shapeVS hT hP)) (m : ClaimMsgVS) :
    BadSummand frameVS K (TrVS F hT hP hC) (TracesStaged frameVS (tableVS hC) (shapeVS hT hP)) where
  coins := (ioSpecVS (algebraMap F K δF)).dep
  dep := coinsBelow frameVS 1
  disj := ioSpecVS_disj _
  badSet tr χ := Finset.univ.filter fun v =>
    (ioSpecVS (algebraMap F K δF)).pair (extIO (ioSpecVS (algebraMap F K δF)) v) ∈ valEv δF hT hP hC V m tr χ
  weight := FiniteIO.ioFailureUnionBound 5 (3 + 2 * V.memRows (tCS hT hP)) (V.memRows (tCS hT hP))
    (Fintype.card (Quad (algebraMap F K δF)))
  card_le tr χ := by
    refine le_trans (Finset.card_le_card_of_injOn
      (fun v => (ioSpecVS (algebraMap F K δF)).pair (extIO (ioSpecVS (algebraMap F K δF)) v)) ?_ ?_)
      (valEv_card δF hT hP hC V m tr χ)
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
      exact hv
    · intro v _ v' _ h; exact extIO_inj _ h
  readsOn Q hQ χ χ' hdep := by
    obtain ⟨e1, e2⟩ := valLists_staged δF hT hP hC V m Q hQ χ χ' hdep
    show (Finset.univ.filter fun v => _ ∈ valEv δF hT hP hC V m (Q χ) χ) =
      Finset.univ.filter fun v => _ ∈ valEv δF hT hP hC V m (Q χ') χ'
    unfold valEv
    rw [e1, e2]

theorem mem_valSummand (V : VerifierData F K hC (shapeVS hT hP)) (m : ClaimMsgVS) (tr : TrVS F hT hP hC)
    (χ : Coins frameVS K) :
    (valSummand δF hT hP hC V m).mem tr χ ↔
      (Quad.mk (algebraMap F K δF) (χ ⟨4, by decide⟩) (χ ⟨6, by decide⟩),
        Quad.mk (algebraMap F K δF) (χ ⟨5, by decide⟩) (χ ⟨7, by decide⟩)) ∈ valEv δF hT hP hC V m tr χ := by
  unfold BadSummand.mem
  show (fun i : (ioSpecVS (algebraMap F K δF)).dep => χ i) ∈
      (Finset.univ.filter fun v : (ioSpecVS (algebraMap F K δF)).dep → K =>
        (ioSpecVS (algebraMap F K δF)).pair (extIO (ioSpecVS (algebraMap F K δF)) v) ∈
          valEv δF hT hP hC V m tr χ) ↔ _
  rw [Finset.mem_filter, pair_extIO, ioSpecVS_pair]
  simp

/-- **The summand's mass**: `weight / |𝕂|⁴ = ioFailureUnionBound 5 (3 + 2T) T 1 / |𝕂|²`. -/
theorem valSummand_mass (V : VerifierData F K hC (shapeVS hT hP)) (m : ClaimMsgVS) :
    ((valSummand δF hT hP hC V m).weight : ℚ) / (Fintype.card K : ℚ) ^ (valSummand δF hT hP hC V m).coins.card =
      (FiniteIO.ioFailureUnionBound 5 (3 + 2 * V.memRows (tCS hT hP)) (V.memRows (tCS hT hP)) 1 : ℚ) /
        (Fintype.card K : ℚ) ^ 2 := by
  have hc : (Fintype.card K : ℚ) ≠ 0 := by
    have := Fintype.card_pos (α := K); positivity
  show ((FiniteIO.ioFailureUnionBound 5 (3 + 2 * V.memRows (tCS hT hP)) (V.memRows (tCS hT hP))
      (Fintype.card (Quad (algebraMap F K δF))) : ℕ) : ℚ) /
        (Fintype.card K : ℚ) ^ (ioSpecVS (algebraMap F K δF)).dep.card = _
  rw [ioSpecVS_dep_card, quad_card, FiniteIO.ioFUB_mul]
  push_cast
  field_simp

end Summand

/-! ## 3. At VS: the claim records are provided outside the summand -/

section VS

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
  {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

/-- At any coin the coin-free lists ARE the lists `claims_provided_VS` reads. -/
theorem valLists_at (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :
    valReqs δF hT hP hC V msg.msg0C (msg.traces χ) χ =
        claimRecs δF V.claim msg.msg0C χ ++
          cellVInternal δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP))
            (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
            (qCellVS δF hT hP kr hC V msg χ) ∧
      valProvs δF hT hP hC V (msg.traces χ) =
        cellVRecords δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP))
          (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
          (qCellVS δF hT hP kr hC V msg χ) := by
  refine ⟨?_, ?_⟩
  · unfold valReqs
    rw [cVInt_chip]
    exact congrArg (claimRecs δF V.claim msg.msg0C χ ++ ·)
      (cVInt_congr δF _ _ _ _ _ _ _ _ _ (by norm_num) (by rw [cell_w]; norm_num) fun j hj => rfl)
  · unfold valProvs
    rw [cVRec_chip]
    exact cVRec_congr δF _ _ _ _ _ _ _ _ _ (by norm_num) (by rw [cell_w]; norm_num) fun j hj => rfl

/-- `claims_provided_VS` with the validity IO
exclusion priced: outside `valSummand`, every CELL claim noun's record is provided by a row of the
decoded (restricted) cell table. -/
theorem claims_provided_VS' (V : VerifierData F K hC (shapeVS hT hP))
    (hV : V.Checks (fun a => reqBoundVS hT hP hC V a + internalBoundVS hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ)
    (hnot : ¬ (valSummand δF hT hP hC V msg.msg0C).mem (msg.traces χ) χ) :
    ∀ k : Fin 3, isCellN (claimNoun V.claim k) = true →
      ValidityProvided (cellTableOf δF V.basis (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP)) (chalsVS δF χ)
          (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (qCellVS δF hT hP kr hC V msg χ))
        (GlobalCarryRecognizer.enc (zVS δF χ) (claimNoun V.claim k), natOf ((msg.msg0C k).2.1 : F),
          natOf ((msg.msg0C k).2.2 : F), natOf ((msg.msg0C k).1 : F)) := by
  obtain ⟨e1, e2⟩ := valLists_at δF hT hP kr hC V msg χ
  have hio : (Quad.mk (algebraMap F K δF) (χ ⟨4, by decide⟩) (χ ⟨6, by decide⟩),
        Quad.mk (algebraMap F K δF) (χ ⟨5, by decide⟩) (χ ⟨7, by decide⟩)) ∉
      FiniteIO.IOFailureEventW (claimRecs δF V.claim msg.msg0C χ ++
          cellVInternal δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP))
            (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
            (qCellVS δF hT hP kr hC V msg χ))
        (SVFrame.liftWts (cellVRecords δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
          (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
          (qCellVS δF hT hP kr hC V msg χ))) := by
    rw [← e1, ← e2]
    exact fun hm => hnot ((mem_valSummand δF hT hP hC V msg.msg0C (msg.traces χ) χ).mpr hm)
  exact claims_provided_VS δF hT hP kr hC V hV msg χ h hio

end VS

end

end Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS
