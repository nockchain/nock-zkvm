/-
  Nock/NockVMROM/Thm54/VclL/Chips/MemFamilyVCLW.lean

Coordinates unchanged except table `1`: `Φ := frameVCL` (11 coins), `I := ioSpecVCLQuad δ`,
  `Kio := Quad δ`, the record view `RV.recordViewVCL` with the SAME widths `RV.mVCL = 5 / 11 / 8`
  (validity / export / path: the walk emits the path chip's record shape `(root, child, axis,
  rootIdx)`), `Msg0 := Unit`, `Msg2 := Quad δ` (the export terminal `y`).  The shape is
  `shapeVW hT hP = shapeVCL hT hP 225 132 Cell.colRoundT colRoundW` (walk width `132`, rounds
  `21 / 72 / 39`, `LayoutW`).

  * §1 `walkChipOk` (the walk chip with the `ok` gate, `pathChipOk` twin), `walkChipOk_sat`;
    `GoodW V t kr` = `GoodM V t` plus the walk chip's public conditions `1 ≤ kr ≤ memRows t`,
    `kr + memRows t < p` (W2's `records_genuine_of_chip` premises; W4b weakened from `3·memRows t`); `okW`.
  * §2 the chips `vclChipW kr V t x ρ y χ` (table `0` the `ok`-gated cell chip as before, table `1`
    the `ok`-gated walk chip at `kroots = kr`, challenge vector `chalsVCL δF χ` (so the walk coins
    are `χ₀ = αC`, `χ₁ = γ`), publics `pubsP` as the path chip's).
  * §3 the committed records / internal consumers as functions of the table columns alone
    (`vclRespW`: validity and export as before, path = `walkPRecords`, two per walk row;
    `vclInternalW`: validity as before, export = `walkXInternal`, one per walk row), the round-1
    invariance.
  * §4 `vclIoFactsW` (`cellValidityFacts` / `cellExportFactsW` / `walkProviderFacts`),
    `vclIoFactsW_records`, lengths (`D / 2D / 2W`, `2D / W / 0`), `vclInternalW_ne_zero`,
    `vcl_servesW`.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.ExportTelescopeW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The `ok`-gated walk chip and its datum checks -/

section Ok
variable {F : Type} [Field F]

/-- The walk template with the `ok` gate. -/
def walkTemplateOk (δF : F) (kroots : ℕ) (ok : Bool) : ChipTemplate F :=
  { walkTemplate δF kroots with
    baseTransition := WChip.baseGates kroots ++ okGates ok
    baseTransition_deg := by
      intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact walkBase_deg kroots g h
      · exact okGates_deg ok g h }

section Chips
attribute [local irreducible] WChip.baseGates WChip.mixedGates

variable {K : Type} [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) (ok : Bool)

/-- **The walk chip with the `ok` gate.** -/
def walkChipOk : FixedPreprocessingRAP F where
  rap := expandChip (walkTemplateOk δF kroots ok) b (slotVal b 21 chals) (slotVal b 21 pubs) orbit
    (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 3
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 21 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes
    | 2 => rootRowMaskW nodes kroots

theorem walkChipOk_w : (walkChipOk δF kroots b hn nodes orbit chals pubs ok).rap.w = 132 :=
  (walkChip_fingerprint δF kroots b hn nodes orbit chals pubs).1

/-- **An accepted `ok`-gated walk trace has `ok = true` and satisfies the plain walk chip.** -/
theorem walkChipOk_sat (Q : Fin (walkChipOk δF kroots b hn nodes orbit chals pubs ok).rap.w → F[X])
    (hQ : RAP.SatisfiesWithPreprocessing (walkChipOk δF kroots b hn nodes orbit chals pubs ok) Q) :
    ok = true ∧ RAP.SatisfiesWithPreprocessing (walkChip δF kroots b hn nodes orbit chals pubs) Q := by
  have hl := (expandChip_satisfies_iff_language (walkTemplateOk δF kroots ok) b _ _ orbit
    (rowNodeSet nodes) Q).mp hQ.1
  refine ⟨?_, ?_, hQ.2⟩
  · cases ok
    · have := (hl _ (mem_rowNodeSet nodes ⟨0, hn⟩)).1 (.const 1)
        (show (CoeffExpr.const 1 : CoeffExpr F) ∈ WChip.baseGates kroots ++ okGates false from
          List.mem_append_right _ (by simp [okGates]))
      simp [CoeffExpr.eval] at this
    · rfl
  · refine (expandChip_satisfies_iff_language (walkTemplate δF kroots) b _ _ orbit (rowNodeSet nodes)
      Q).mpr fun x hx => ?_
    obtain ⟨h1, h2, h3, h4⟩ := hl x hx
    exact ⟨fun g hg => h1 g (List.mem_append_left _ hg), h2, h3, h4⟩

end Chips

section Datum
variable {K : Type} [Field K] [Algebra F K] {hC : ℕ} {S : MemShape}

/-- **The public conditions the walk table's chip enforces**: `GoodM` and the walk's own
`1 ≤ kr ≤ memRows t`, `kr + memRows t < p` (no queue-counter wrap; W4b: was `3·memRows t < p`,
weakened to what `walk_tiling` uses). -/
def GoodW (V : VerifierData F K hC S) (t : Fin S.k) (kr : ℕ) : Prop :=
  GoodM V t ∧ 1 ≤ kr ∧ kr ≤ V.memRows t ∧ kr + V.memRows t < ringChar F

/-- The `ok` bit of the walk table. -/
def okW (V : VerifierData F K hC S) (t : Fin S.k) (kr : ℕ) : Bool :=
  @decide (GoodW V t kr) (Classical.propDecidable _)

theorem goodW_of_ok {V : VerifierData F K hC S} {t : Fin S.k} {kr : ℕ} (h : okW V t kr = true) :
    GoodW V t kr :=
  @of_decide_eq_true _ (Classical.propDecidable _) h

theorem okW_of_goodW {V : VerifierData F K hC S} {t : Fin S.k} {kr : ℕ} (h : GoodW V t kr) :
    okW V t kr = true :=
  @decide_eq_true _ (Classical.propDecidable _) h

end Datum

end Ok

/-! ## 2. Read sets of the walk keys (decided) -/

section ReadSets
variable {F : Type} [Field F]

theorem qLt_wxKey : qLt 24 21 (WChip.xKey (F := F)) = true := rfl
theorem qLt_wrecL : qLt 24 21 (WChip.recL (F := F)) = true := rfl
theorem qLt_wrecR : qLt 24 21 (WChip.recR (F := F)) = true := rfl

end ReadSets

section Records
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs chals' pubs' : ℕ → K)
  {w w' : ℕ} (Q : Fin w → F[X]) (Q' : Fin w' → F[X])

theorem wPRec_congr (hw : 93 ≤ w) (hw' : 93 ≤ w')
    (hQ : ∀ (j : ℕ) (hj : j < 93), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩) :
    walkPRecords δF kroots b hn nodes orbit chals pubs Q =
      walkPRecords δF kroots b hn nodes orbit chals' pubs' Q' := by
  unfold walkPRecords; congr 1; funext j
  obtain ⟨hF, hK⟩ := walkEnv_congr δF kroots b hn nodes orbit Q Q' hw hw' hQ chals pubs chals' pubs' j
  simp only [walkKey, walkB]
  rw [keyVec_congr δF hK (BF := 21) (fun c hc => hF c (by omega)) 8 _ qLt_wrecL,
    keyVec_congr δF hK (BF := 21) (fun c hc => hF c (by omega)) 8 _ qLt_wrecR,
    hF WChip.mL (by decide), hF WChip.mR (by decide)]

theorem wXInt_congr (hw : 93 ≤ w) (hw' : 93 ≤ w')
    (hQ : ∀ (j : ℕ) (hj : j < 93), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩) :
    walkXInternal δF kroots b hn nodes orbit chals pubs Q =
      walkXInternal δF kroots b hn nodes orbit chals' pubs' Q' := by
  unfold walkXInternal; congr 1; funext j
  obtain ⟨hF, hK⟩ := walkEnv_congr δF kroots b hn nodes orbit Q Q' hw hw' hQ chals pubs chals' pubs' j
  simp only [walkKey]
  rw [keyVec_congr δF hK (BF := 21) (fun c hc => hF c (by omega)) 11 _ qLt_wxKey]

theorem walkPRecords_length :
    (walkPRecords δF kroots b hn nodes orbit chals pubs Q).length ≤ 2 * n := by
  unfold walkPRecords
  have := length_flatMap_le (fun j : ℕ =>
    [(walkKey δF kroots b hn nodes orbit chals pubs Q 8 WChip.recL j,
        walkB b hn nodes orbit chals pubs Q WChip.mL j),
     (walkKey δF kroots b hn nodes orbit chals pubs Q 8 WChip.recR j,
        walkB b hn nodes orbit chals pubs Q WChip.mR j)]) 2 (fun _ => le_refl _) (List.range n)
  simpa using this

theorem walkXInternal_length : (walkXInternal δF kroots b hn nodes orbit chals pubs Q).length = n := by
  simp [walkXInternal]

end Records

/-! ## 3. The family's chips, records and IO fields -/

/-- The walk table's column → round map (`LayoutW`: `21 / 72 / 39`). -/
def colRoundW (j : Fin 132) : ℕ := if (j : ℕ) < 21 then 0 else if (j : ℕ) < 93 then 1 else 2

/-- `colRoundW` is `LayoutW`'s `WalkW.colRound` at the measured width. -/
theorem colRoundW_layout (j : Fin 132) :
    colRoundW j = WalkW.colRound (Fin.cast WalkW.width_eq.symm j) := rfl

section Family
attribute [local irreducible] Cell.baseGates Path.baseGates Cell.mixedGates Path.mixedGates
  WChip.baseGates WChip.mixedGates

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr : ℕ) {hC : ℕ}

/-- **The VCL-L memory shape with the walk table**: cells `225`, walk `132`. -/
abbrev shapeVW : MemShape :=
  shapeVCL hT hP 225 132 Chips.Cell.colRoundT colRoundW

/-- The cell table's index. -/
def tCW : Fin (shapeVW hT hP).k := ⟨0, by show 0 < 2; omega⟩
/-- The walk table's index. -/
def tWW : Fin (shapeVW hT hP).k := ⟨1, by show 1 < 2; omega⟩

variable (ρ : Fin 3 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF))
  (V : VerifierData F K hC (shapeVW hT hP)) (x : Unit) (χ : Coins frameVCL K)
  (Q : ∀ t : Fin (shapeVW hT hP).k, Fin ((shapeVW hT hP).table t).width → F[X])

/-- **The memory chips with the walk**: table `0` the `ok`-gated cell chip, table `1` the
`ok`-gated walk chip (`kroots = kr`), at `V.memNodes t`, `V.basis`, `V.orbitM t`, `chalsVCL δF χ`
and the publics `pubsC` / `pubsP`. -/
def vclChipW (t : Fin (shapeVW hT hP).k) : FixedPreprocessingRAP F :=
  if (t : ℕ) = 0 then
    cellChipOk δF V.basis (V.hM t) (V.memNodes t) (V.orbitM t) (chalsVCL δF χ) (pubsC δF ρ y) (okOf V t)
  else walkChipOk δF kr V.basis (V.hM t) (V.memNodes t) (V.orbitM t) (chalsVCL δF χ) (pubsP δF ρ y)
    (okW V t kr)

theorem vclChipW_width (t : Fin (shapeVW hT hP).k) :
    (vclChipW δF hT hP kr ρ y V χ t).rap.w = ((shapeVW hT hP).table t).width := by
  unfold vclChipW
  split_ifs with ht
  · rw [cellChipOk_w]; unfold shapeVW shapeVCL; dsimp only; rw [if_pos ht]
  · rw [walkChipOk_w]; unfold shapeVW shapeVCL; dsimp only; rw [if_neg ht]

/-- The committed providers per accumulator (B0/B1 columns only; no coin, no public). -/
def vclRespW : ∀ a : Fin 3, List ((Fin (RV.mVCL a) → Quad (algebraMap F K δF)) × F)
  | 0 => cVRec δF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP)) 0 0 (Q (tCW hT hP))
  | 1 => cXRec δF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP)) 0 0 (Q (tCW hT hP))
  | 2 => walkPRecords δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP))
      0 0 (Q (tWW hT hP))

/-- The memory-internal consumers: validity = the weighted child keys, export = every walk row's
consumed key, path = none. -/
def vclInternalW : ∀ a : Fin 3, List (Fin (RV.mVCL a) → Quad (algebraMap F K δF))
  | 0 => cVInt δF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP)) 0 0 (Q (tCW hT hP))
  | 1 => walkXInternal δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP))
      0 0 (Q (tWW hT hP))
  | 2 => []

/-- Provider-row bounds `D / 2D / 2W` (two records per walk row). -/
def vclRespBoundW (V : VerifierData F K hC (shapeVW hT hP)) : Fin 3 → ℕ
  | 0 => V.memRows (tCW hT hP)
  | 1 => 2 * V.memRows (tCW hT hP)
  | 2 => 2 * V.memRows (tWW hT hP)

/-- Internal-consumer bounds `2D / W / 0`. -/
def vclInternalBoundW (V : VerifierData F K hC (shapeVW hT hP)) : Fin 3 → ℕ
  | 0 => 2 * V.memRows (tCW hT hP)
  | 1 => V.memRows (tWW hT hP)
  | 2 => 0

theorem vclInternalW_length (a : Fin 3) :
    (vclInternalW δF hT hP kr V Q a).length ≤ vclInternalBoundW hT hP V a := by
  fin_cases a
  · exact cVInt_length δF _ _ _ _ _ _
  · exact (walkXInternal_length δF _ _ _ _ _ _ _ _).le
  · simp [vclInternalW, vclInternalBoundW]

theorem vclRespW_length (a : Fin 3) :
    (vclRespW δF hT hP kr V Q a).length ≤ vclRespBoundW hT hP V a := by
  fin_cases a
  · exact (cVRec_length δF _ _ _ _ _ _).le
  · exact cXRec_length δF _ _ _ _ _ _
  · exact walkPRecords_length δF _ _ _ _ _ _ _ _

theorem round_cellW (j : ℕ) (hj : j < 183) :
    ((shapeVW hT hP).table (tCW hT hP)).colRound ⟨j, by show j < 225; omega⟩ ≤ 1 := by
  show Chips.Cell.colRoundT ⟨j, _⟩ ≤ 1
  simp only [Chips.Cell.colRoundT, show Chips.Cell.b0CountS = 129 from rfl,
    show Chips.Cell.b1Count = 54 from rfl]
  split_ifs <;> omega

theorem round_walk (j : ℕ) (hj : j < 93) :
    ((shapeVW hT hP).table (tWW hT hP)).colRound ⟨j, by show j < 132; omega⟩ ≤ 1 := by
  show colRoundW ⟨j, _⟩ ≤ 1
  simp only [colRoundW]
  split_ifs <;> omega

theorem round_walk0 (j : ℕ) (hj : j < 21) :
    ((shapeVW hT hP).table (tWW hT hP)).colRound ⟨j, by show j < 132; omega⟩ = 0 := by
  show colRoundW ⟨j, _⟩ = 0
  simp only [colRoundW]
  rw [if_pos hj]

/-- **`respRecords_round`**. -/
theorem vclRespW_round (Q' : ∀ t : Fin (shapeVW hT hP).k, Fin ((shapeVW hT hP).table t).width → F[X])
    (hQ : ∀ t j, ((shapeVW hT hP).table t).colRound j ≤ 1 → Q t j = Q' t j) :
    vclRespW δF hT hP kr V Q = vclRespW δF hT hP kr V Q' := by
  funext a
  fin_cases a
  · exact cVRec_congr δF _ _ _ _ _ _ _ _ _ (show 183 ≤ 225 by omega) (show 183 ≤ 225 by omega)
      fun j hj => hQ _ _ (round_cellW hT hP j hj)
  · exact cXRec_congr δF _ _ _ _ _ _ _ _ _ (show 183 ≤ 225 by omega) (show 183 ≤ 225 by omega)
      fun j hj => hQ _ _ (round_cellW hT hP j hj)
  · exact wPRec_congr δF _ _ _ _ _ _ _ _ _ _ _ (show 93 ≤ 132 by omega) (show 93 ≤ 132 by omega)
      fun j hj => hQ _ _ (round_walk hT hP j hj)

/-- **`internal_round`**. -/
theorem vclInternalW_round (Q' : ∀ t : Fin (shapeVW hT hP).k, Fin ((shapeVW hT hP).table t).width → F[X])
    (hQ : ∀ t j, ((shapeVW hT hP).table t).colRound j ≤ 1 → Q t j = Q' t j) :
    vclInternalW δF hT hP kr V Q = vclInternalW δF hT hP kr V Q' := by
  funext a
  fin_cases a
  · exact cVInt_congr δF _ _ _ _ _ _ _ _ _ (show 183 ≤ 225 by omega) (show 183 ≤ 225 by omega)
      fun j hj => hQ _ _ (round_cellW hT hP j hj)
  · exact wXInt_congr δF _ _ _ _ _ _ _ _ _ _ _ (show 93 ≤ 132 by omega) (show 93 ≤ 132 by omega)
      fun j hj => hQ _ _ (round_walk hT hP j hj)
  · rfl

/-! ### Acceptance of the two chips -/

/-- Table `0`'s chip at its parameters. -/
abbrev cellOkW : FixedPreprocessingRAP F :=
  cellChipOk δF V.basis (V.hM (tCW hT hP)) (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP)) (chalsVCL δF χ)
    (pubsC δF ρ y) (okOf V (tCW hT hP))

/-- Table `1`'s chip at its parameters. -/
abbrev walkOkW : FixedPreprocessingRAP F :=
  walkChipOk δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP))
    (chalsVCL δF χ) (pubsP δF ρ y) (okW V (tWW hT hP) kr)

theorem cellOkW_w' : (cellOkW δF hT hP ρ y V χ).rap.w = ((shapeVW hT hP).table (tCW hT hP)).width := by
  rw [cellChipOk_w]; rfl
theorem walkOkW_w' : (walkOkW δF hT hP kr ρ y V χ).rap.w = ((shapeVW hT hP).table (tWW hT hP)).width := by
  rw [walkChipOk_w]; rfl

/-- The cell trace at the chip's width. -/
def QCW : Fin (cellOkW δF hT hP ρ y V χ).rap.w → F[X] :=
  fun j => Q (tCW hT hP) (Fin.cast (cellOkW_w' δF hT hP ρ y V χ) j)
/-- The walk trace at the chip's width. -/
def QWW : Fin (walkOkW δF hT hP kr ρ y V χ).rap.w → F[X] :=
  fun j => Q (tWW hT hP) (Fin.cast (walkOkW_w' δF hT hP kr ρ y V χ) j)

theorem vclChipW_tC : vclChipW δF hT hP kr ρ y V χ (tCW hT hP) = cellOkW δF hT hP ρ y V χ := by
  unfold vclChipW; exact if_pos rfl
theorem vclChipW_tW : vclChipW δF hT hP kr ρ y V χ (tWW hT hP) = walkOkW δF hT hP kr ρ y V χ := by
  unfold vclChipW; exact if_neg Nat.one_ne_zero

variable {δF hT hP kr ρ y V χ Q} in
/-- **An accepted pair of memory traces**: both datum checks hold and both plain chips are
satisfied. -/
theorem vcl_acceptedW
    (h : ∀ t, RAP.SatisfiesWithPreprocessing (vclChipW δF hT hP kr ρ y V χ t)
      (fun j => Q t (Fin.cast (vclChipW_width δF hT hP kr ρ y V χ t) j))) :
    (GoodM V (tCW hT hP) ∧ RAP.SatisfiesWithPreprocessing
      (cellChip δF V.basis (V.hM (tCW hT hP)) (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP)) (chalsVCL δF χ)
        (pubsC δF ρ y)) (QCW δF hT hP ρ y V χ Q)) ∧
    (GoodW V (tWW hT hP) kr ∧ RAP.SatisfiesWithPreprocessing
      (walkChip δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP))
        (chalsVCL δF χ) (pubsP δF ρ y)) (QWW δF hT hP kr ρ y V χ Q)) := by
  have h0 := sat_transport (vclChipW_tC δF hT hP kr ρ y V χ) (Q (tCW hT hP)) _
    (cellOkW_w' δF hT hP ρ y V χ) (h (tCW hT hP))
  have h1 := sat_transport (vclChipW_tW δF hT hP kr ρ y V χ) (Q (tWW hT hP)) _
    (walkOkW_w' δF hT hP kr ρ y V χ) (h (tWW hT hP))
  obtain ⟨hok0, hs0⟩ := cellChipOk_sat _ _ _ _ _ _ _ _ _ h0
  obtain ⟨hok1, hs1⟩ := walkChipOk_sat _ _ _ _ _ _ _ _ _ _ h1
  exact ⟨⟨goodM_of_ok hok0, hs0⟩, ⟨goodW_of_ok hok1, hs1⟩⟩

/-! ### The chip-typed lists are the family's -/

theorem cellVInternal_eqW :
    cellVInternal δF V.basis (V.hM (tCW hT hP)) (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP))
      (chalsVCL δF χ) (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q) = vclInternalW δF hT hP kr V Q 0 := by
  erw [cVInt_chip]
  exact cVInt_congr δF _ _ _ _ _ _ _ _ _ (by rw [cell_w]; omega)
    (show 183 ≤ 225 by omega) fun j hj => rfl

theorem walkXInternal_eqW :
    walkXInternal δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP))
      (chalsVCL δF χ) (pubsP δF ρ y) (QWW δF hT hP kr ρ y V χ Q) = vclInternalW δF hT hP kr V Q 1 :=
  wXInt_congr δF _ _ _ _ _ _ _ _ _ _ _ (by rw [walkChipOk_w]; omega)
    (show 93 ≤ 132 by omega) fun j hj => rfl

theorem cellVRecords_eqW :
    cellVRecords δF V.basis (V.hM (tCW hT hP)) (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP))
      (chalsVCL δF χ) (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q) = vclRespW δF hT hP kr V Q 0 := by
  erw [cVRec_chip]
  exact cVRec_congr δF _ _ _ _ _ _ _ _ _ (by rw [cell_w]; omega)
    (show 183 ≤ 225 by omega) fun j hj => rfl

theorem cellXRecords_eqW :
    cellXRecords δF V.basis (V.hM (tCW hT hP)) (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP))
      (chalsVCL δF χ) (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q) = vclRespW δF hT hP kr V Q 1 := by
  erw [cXRec_chip]
  exact cXRec_congr δF _ _ _ _ _ _ _ _ _ (by rw [cell_w]; omega)
    (show 183 ≤ 225 by omega) fun j hj => rfl

theorem walkPRecords_eqW :
    walkPRecords δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP))
      (chalsVCL δF χ) (pubsP δF ρ y) (QWW δF hT hP kr ρ y V χ Q) = vclRespW δF hT hP kr V Q 2 :=
  wPRec_congr δF _ _ _ _ _ _ _ _ _ _ _ (by rw [walkChipOk_w]; omega)
    (show 93 ≤ 132 by omega) fun j hj => rfl

/-! ### `ioFacts` -/

variable {δF hT hP kr ρ y V χ Q} in
/-- **`ioFacts`**: the three accumulators' weighted IO facts from an accepted pair (validity
`cellValidityFacts`, export `cellExportFactsW` with the walk as consumer, path
`walkProviderFacts`). -/
def vclIoFactsW
    (h : ∀ t, RAP.SatisfiesWithPreprocessing (vclChipW δF hT hP kr ρ y V χ t)
      (fun j => Q t (Fin.cast (vclChipW_width δF hT hP kr ρ y V χ t) j))) :
    ∀ a : Fin 3, SVFrame.IOFacts F
      (FiniteIO.compress (m := RV.mVCL a) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ))
      (ρ a + ((vclInternalW δF hT hP kr V Q a).map fun r =>
        (FiniteIO.compress (m := RV.mVCL a) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ) r)⁻¹).sum)
  | 0 => IOFacts.recast rfl (by rw [pubsC_01, cellVInternal_eqW]; rfl)
      (cellValidityFacts δF V.basis (V.hM (tCW hT hP)) (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP))
        (chalsVCL δF χ) (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q) (vcl_acceptedW h).1.2.1
        (vcl_acceptedW h).1.2.2 (vcl_acceptedW h).1.1.2.1 (vcl_acceptedW h).1.1.adj _ _
        (chalsVCL_ok δF χ 11))
  | 1 => IOFacts.recast rfl (by erw [walkXInternal_eqW]; rfl)
      (cellExportFactsW δF kr V.basis (V.hM (tCW hT hP)) (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP))
        (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP)) (chalsVCL δF χ) (pubsC δF ρ y)
        (pubsP δF ρ y) (QCW δF hT hP ρ y V χ Q) (QWW δF hT hP kr ρ y V χ Q)
        (vcl_acceptedW h).1.2.1 (vcl_acceptedW h).1.2.2 (vcl_acceptedW h).1.1.2.1 (vcl_acceptedW h).1.1.adj
        (vcl_acceptedW h).2.2.1 (vcl_acceptedW h).2.2.2 (vcl_acceptedW h).2.1.1.2.1
        (vcl_acceptedW h).2.1.1.adj _ _ (chalsVCL_ok δF χ 11) (ρ 1) (by rw [pubsC_23, pubsP_01]))
  | 2 => IOFacts.recast rfl (by rw [pubsP_23]; simp [vclInternalW])
      (walkProviderFacts δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP))
        (chalsVCL δF χ) (pubsP δF ρ y) (QWW δF hT hP kr ρ y V χ Q) (vcl_acceptedW h).2.2.1
        (vcl_acceptedW h).2.2.2 (vcl_acceptedW h).2.1.1.2.1 (vcl_acceptedW h).2.1.1.adj _ _
        (chalsVCL_ok δF χ 11))

variable {δF hT hP kr ρ y V χ Q} in
/-- **`ioFacts_records`**: the IO facts' providers are the committed records `vclRespW`. -/
theorem vclIoFactsW_records
    (h : ∀ t, RAP.SatisfiesWithPreprocessing (vclChipW δF hT hP kr ρ y V χ t)
      (fun j => Q t (Fin.cast (vclChipW_width δF hT hP kr ρ y V χ t) j))) (a : Fin 3) :
    (vclIoFactsW h a).records = vclRespW δF hT hP kr V Q a := by
  fin_cases a
  · exact (IOFacts.recast_records _ _ _).trans (cellVRecords_eqW δF hT hP kr ρ y V χ Q)
  · exact (IOFacts.recast_records _ _ _).trans (cellXRecords_eqW δF hT hP kr ρ y V χ Q)
  · exact (IOFacts.recast_records _ _ _).trans (walkPRecords_eqW δF hT hP kr ρ y V χ Q)

variable {δF hT hP kr ρ y V χ Q} in
/-- **`ioFacts_length`**: provider rows `≤ D / 2D / 2W`. -/
theorem vclIoFactsW_length
    (h : ∀ t, RAP.SatisfiesWithPreprocessing (vclChipW δF hT hP kr ρ y V χ t)
      (fun j => Q t (Fin.cast (vclChipW_width δF hT hP kr ρ y V χ t) j))) (a : Fin 3) :
    (vclIoFactsW h a).records.length ≤ vclRespBoundW hT hP V a := by
  rw [vclIoFactsW_records h a]; exact vclRespW_length δF hT hP kr V Q a

variable {δF hT hP kr ρ y V χ Q} in
theorem walkInternal_ne_zero
    (hsat : (walkChip δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP))
      (chalsVCL δF χ) (pubsP δF ρ y)).rap.Satisfies (QWW δF hT hP kr ρ y V χ Q)) :
    ∀ r ∈ walkXInternal δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP))
      (chalsVCL δF χ) (pubsP δF ρ y) (QWW δF hT hP kr ρ y V χ Q),
      FiniteIO.compress (m := 11) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ) r ≠ 0 := by
  intro r hr
  unfold walkXInternal at hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  have hjn := List.mem_range.mp hj
  have e := walk_compressK δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP))
    (chalsVCL δF χ) (pubsP δF ρ y) (QWW δF hT hP kr ρ y V χ Q) _ _ (chalsVCL_ok δF χ 11) WChip.xKey
    (m := 11) rfl le_rfl j
  exact fun h0 => (walk_xinv δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP))
    (chalsVCL δF χ) (pubsP δF ρ y) (QWW δF hT hP kr ρ y V χ Q) hsat j hjn).1 (e.symm.trans h0)

variable {δF hT hP kr ρ y V χ Q} in
theorem cellInternal_ne_zeroW
    (hsat : (cellChip δF V.basis (V.hM (tCW hT hP)) (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP))
      (chalsVCL δF χ) (pubsC δF ρ y)).rap.Satisfies (QCW δF hT hP ρ y V χ Q)) :
    ∀ r ∈ cellVInternal δF V.basis (V.hM (tCW hT hP)) (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP))
      (chalsVCL δF χ) (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q),
      FiniteIO.compress (m := 5) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ) r ≠ 0 := by
  intro r hr
  erw [cVInt_chip] at hr
  obtain ⟨i, ⟨hw, rfl⟩ | ⟨hw, rfl⟩⟩ := mem_cVInt δF _ _ _ _ _ _ hr
  · obtain ⟨-, ⟨hL, -⟩, -⟩ := cell_inv_facts δF V.basis (V.hM (tCW hT hP)) (V.memNodes (tCW hT hP))
      (V.orbitM (tCW hT hP)) (chalsVCL δF χ) (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q) hsat i
    have e := cell_compress (b := V.basis) (hn := V.hM (tCW hT hP)) (nodes := V.memNodes (tCW hT hP))
      (orbit := V.orbitM (tCW hT hP)) (pubs := pubsC δF ρ y) (Q := QCW δF hT hP ρ y V χ Q) (m := 5)
      _ _ (chalsVCL_ok δF χ 11) Cell.vKeyL rfl (by norm_num) i
    exact fun h0 => hL hw (e.symm.trans h0)
  · obtain ⟨-, -, ⟨hR, -⟩⟩ := cell_inv_facts δF V.basis (V.hM (tCW hT hP)) (V.memNodes (tCW hT hP))
      (V.orbitM (tCW hT hP)) (chalsVCL δF χ) (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q) hsat i
    have e := cell_compress (b := V.basis) (hn := V.hM (tCW hT hP)) (nodes := V.memNodes (tCW hT hP))
      (orbit := V.orbitM (tCW hT hP)) (pubs := pubsC δF ρ y) (Q := QCW δF hT hP ρ y V χ Q) (m := 5)
      _ _ (chalsVCL_ok δF χ 11) Cell.vKeyR rfl (by norm_num) i
    exact fun h0 => hR hw (e.symm.trans h0)

variable {δF hT hP kr ρ y V χ Q} in
/-- **`internal_ne_zero`**. -/
theorem vclInternalW_ne_zero
    (h : ∀ t, RAP.SatisfiesWithPreprocessing (vclChipW δF hT hP kr ρ y V χ t)
      (fun j => Q t (Fin.cast (vclChipW_width δF hT hP kr ρ y V χ t) j))) (a : Fin 3) :
    ∀ r ∈ vclInternalW δF hT hP kr V Q a,
      FiniteIO.compress (m := RV.mVCL a) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ) r ≠ 0 := by
  have hA := vcl_acceptedW h
  match a with
  | 0 =>
    rw [← cellVInternal_eqW δF hT hP kr ρ y V χ Q]
    exact cellInternal_ne_zeroW hA.1.2.1
  | 1 =>
    rw [← walkXInternal_eqW δF hT hP kr ρ y V χ Q]
    exact walkInternal_ne_zero hA.2.2.1
  | 2 => intro r hr; exact absurd hr List.not_mem_nil

variable {δF hT hP kr ρ y V χ Q} in
/-- **`serves`** (`serves_of_weighted_lookup` per accumulator). -/
theorem vcl_servesW [DecidableEq K] [Fintype F]
    (h : ∀ t, RAP.SatisfiesWithPreprocessing (vclChipW δF hT hP kr ρ y V χ t)
      (fun j => Q t (Fin.cast (vclChipW_width δF hT hP kr ρ y V χ t) j)))
    (reqs : ∀ a : Fin 3, List (Fin (RV.mVCL a) → Quad (algebraMap F K δF)))
    (hsum : ∀ a, ((reqs a).map fun r =>
      (FiniteIO.compress (m := RV.mVCL a) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ) r)⁻¹).sum = ρ a)
    (hne : ∀ a, ∀ r ∈ reqs a,
      FiniteIO.compress (m := RV.mVCL a) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ) r ≠ 0)
    (hio : ∀ a, (ioSpecVCLQuad (algebraMap F K δF)).pair χ ∉ FiniteIO.IOFailureEventW
      (reqs a ++ vclInternalW δF hT hP kr V Q a) (liftWts (vclRespW δF hT hP kr V Q a)))
    (hcount : ∀ a, (reqs a ++ vclInternalW δF hT hP kr V Q a).length <
      ringChar (Quad (algebraMap F K δF))) :
    ∀ a, ∀ r ∈ reqs a, r ∈ (vclIoFactsW h a).records.map Prod.fst := by
  intro a
  have hio' : (ioSpecVCLQuad (algebraMap F K δF)).pair χ ∉ FiniteIO.IOFailureEventW
      (reqs a ++ vclInternalW δF hT hP kr V Q a) (liftWts (vclIoFactsW h a).records) := by
    rw [vclIoFactsW_records h a]; exact hio a
  exact serves_of_weighted_lookup (I := ioSpecVCLQuad (algebraMap F K δF)) (m := RV.mVCL)
    (p := ringChar (Quad (algebraMap F K δF))) χ a (reqs a) (vclInternalW δF hT hP kr V Q a) (ρ a)
    (vclIoFactsW h a) (hsum a) (hne a) (vclInternalW_ne_zero h a) hio' (hcount a)

end Family

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
