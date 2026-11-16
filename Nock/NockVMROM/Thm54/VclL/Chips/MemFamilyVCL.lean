/-
  Nock/NockVMROM/Thm54/VclL/Chips/MemFamilyVCL.lean

The memory family's coordinates: `Φ := frameVCL`, `I := ioSpecVCLQuad δ`, `Kio := Quad δ` with
  `δ := algebraMap F K δF`, `S := shapeVCL hT hP 225 112 IOField.Cell.colRoundT IOField.Path.colRoundT`,
  three accumulators `RV.mVCL = 5 / 11 / 8`, `Msg0 := Unit`, `Msg2 := Quad δ` (the export
  terminal `y`).

  * §1 **read sets**: `cLt` / `mLt` (an expression reads only current-row columns below a bound),
    `keyVec_congr` — the record keys read the B0 / B1 columns only, never the coins or publics.
  * §2 the chips `vclChip V t x ρ y χ` (`cellChipOk` / `pathChipOk` at `okOf V t`, challenge vector
    `chalsVCL δF χ`, publics cell `0/1 = ρ 0`, `2/3 = ρ 1 + y`, path `0/1 = y`, `2/3 = ρ 2`),
    `vclChip_width`.
  * §3 the committed records and the internal consumers as functions of the table columns alone
    (`vclResp`, `vclInternal`), their chip-typed forms, and the round-1 invariance
    (`vclResp_round`, `vclInternal_round`).
  * §4 the IO fields: `vclIoFacts` (from `cellChipOk_sat` / `pathChipOk_sat`, `goodM_of_ok`,
    `cellValidityFacts` / `cellExportFacts` / `pathProviderFacts`), `vclIoFacts_records`, the length
    bounds `D / 2D / P` and `2D / P / 0`, `vclInternal_ne_zero`, and `serves`.

  No field here reads `CF.keyOf` or the compute side's `axB0`: the memory IO fields are independent
  of the compute-side exponent indexing.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.ExportTelescope
import Nock.NockVMROM.Thm54.VclL.Chips.IOField
import Nock.NockVMROM.Thm54.VclL.RecordViewVCL
import Nock.NockVMROM.Thm54.P8Core.SVFrame.JointSummands

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
open Nock.NockVMROM.Thm54.VclL.Chips.PathModel
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Read sets -/

/-- A base expression reads only constants and current-row columns `< B`. -/
def cLt {F : Type} (B : ℕ) : CoeffExpr F → Bool
  | .const _ => true
  | .var .traceCur j => decide (j < B)
  | .var _ _ => false
  | .add x y => cLt B x && cLt B y
  | .sub x y => cLt B x && cLt B y
  | .mul x y => cLt B x && cLt B y
  | .neg x => cLt B x
  | .pow x _ => cLt B x

/-- A mixed expression reads only constants, current-row `𝕂` columns `< BK` and current-row base
columns `< BF`. -/
def mLt {F : Type} (BK BF : ℕ) : MixedExpr F → Bool
  | .Var .traceCur r => decide (r < BK)
  | .Var _ _ => false
  | .Lift g => cLt BF g
  | .Scale g u => cLt BF g && mLt BK BF u
  | .Const _ => true
  | .Add x y => mLt BK BF x && mLt BK BF y
  | .Sub x y => mLt BK BF x && mLt BK BF y
  | .Neg x => mLt BK BF x
  | .Mul x y => mLt BK BF x && mLt BK BF y
  | .Pow x _ => mLt BK BF x

theorem cLt_eval {F : Type} [Field F] {B : ℕ} {eF eF' : Env F}
    (h : ∀ j < B, eF.trace j = eF'.trace j) : ∀ g : CoeffExpr F, cLt B g = true → g.eval eF = g.eval eF'
  | .const _, _ => rfl
  | .var .traceCur j, hg => by
    simp only [cLt, decide_eq_true_eq] at hg; simp only [CoeffExpr.eval]; exact h j hg
  | .var .traceNext _, hg => by simp [cLt] at hg
  | .var .challenge _, hg => by simp [cLt] at hg
  | .var .publicVal _, hg => by simp [cLt] at hg
  | .add x y, hg => by
    simp only [cLt, Bool.and_eq_true] at hg
    simp only [CoeffExpr.eval, cLt_eval h x hg.1, cLt_eval h y hg.2]
  | .sub x y, hg => by
    simp only [cLt, Bool.and_eq_true] at hg
    simp only [CoeffExpr.eval, cLt_eval h x hg.1, cLt_eval h y hg.2]
  | .mul x y, hg => by
    simp only [cLt, Bool.and_eq_true] at hg
    simp only [CoeffExpr.eval, cLt_eval h x hg.1, cLt_eval h y hg.2]
  | .neg x, hg => by simp only [cLt] at hg; simp only [CoeffExpr.eval, cLt_eval h x hg]
  | .pow x _, hg => by simp only [cLt] at hg; simp only [CoeffExpr.eval, cLt_eval h x hg]

theorem mLt_eval {F K : Type} [Field F] [Field K] [Algebra F K] {BK BF : ℕ} {eK eK' : Env K}
    {eF eF' : Env F} (hK : ∀ r < BK, eK.trace r = eK'.trace r) (hF : ∀ j < BF, eF.trace j = eF'.trace j) :
    ∀ e : MixedExpr F, mLt BK BF e = true → e.eval eK eF = e.eval eK' eF'
  | .Var .traceCur r, he => by
    simp only [mLt, decide_eq_true_eq] at he; simp only [MixedExpr.eval]; exact hK r he
  | .Var .traceNext _, he => by simp [mLt] at he
  | .Var .challenge _, he => by simp [mLt] at he
  | .Var .publicVal _, he => by simp [mLt] at he
  | .Lift g, he => by simp only [mLt] at he; simp only [MixedExpr.eval, cLt_eval hF g he]
  | .Scale g u, he => by
    simp only [mLt, Bool.and_eq_true] at he
    simp only [MixedExpr.eval, cLt_eval hF g he.1, mLt_eval hK hF u he.2]
  | .Const _, _ => rfl
  | .Add x y, he => by
    simp only [mLt, Bool.and_eq_true] at he
    simp only [MixedExpr.eval, mLt_eval hK hF x he.1, mLt_eval hK hF y he.2]
  | .Sub x y, he => by
    simp only [mLt, Bool.and_eq_true] at he
    simp only [MixedExpr.eval, mLt_eval hK hF x he.1, mLt_eval hK hF y he.2]
  | .Neg x, he => by simp only [mLt] at he; simp only [MixedExpr.eval, mLt_eval hK hF x he]
  | .Mul x y, he => by
    simp only [mLt, Bool.and_eq_true] at he
    simp only [MixedExpr.eval, mLt_eval hK hF x he.1, mLt_eval hK hF y he.2]
  | .Pow x _, he => by simp only [mLt] at he; simp only [MixedExpr.eval, mLt_eval hK hF x he]

/-- A `QE` list reads only current-row columns below the bounds. -/
def qLt {F : Type} (BK BF : ℕ) (es : List (QE F)) : Bool :=
  es.all fun e => mLt BK BF e.re && mLt BK BF e.im

theorem keyVec_congr {F K : Type} [Field F] [Field K] [Algebra F K] (δF : F) {BK BF : ℕ}
    {eK eK' : Env K} {eF eF' : Env F} (hK : ∀ r < BK, eK.trace r = eK'.trace r)
    (hF : ∀ j < BF, eF.trace j = eF'.trace j) (m : ℕ) (es : List (QE F)) (hes : qLt BK BF es = true) :
    keyVec δF m es eK eF = keyVec δF m es eK' eF' := by
  funext c
  simp only [keyVec, QE.ev]
  have hmem : ∀ e : QE F, (e ∈ es ∨ e = QE.zero) → mLt BK BF e.re = true ∧ mLt BK BF e.im = true := by
    rintro e (he | rfl)
    · have := List.all_eq_true.mp hes e he
      simpa only [Bool.and_eq_true] using this
    · exact ⟨rfl, rfl⟩
  have hc : es.getD c QE.zero ∈ es ∨ es.getD c QE.zero = QE.zero := by
    rw [List.getD_eq_getElem?_getD]
    cases hx : es[(c : ℕ)]? with
    | none => right; rfl
    | some x => left; exact List.mem_of_getElem? hx
  obtain ⟨h1, h2⟩ := hmem _ hc
  rw [mLt_eval hK hF _ h1, mLt_eval hK hF _ h2]

/-- The gathered `𝕂` trace at role `r` reads base columns `col0 r + k`, `k < e`. -/
theorem gather_trace_congr {F K : Type} [Field F] [Field K] [Algebra F K] {e : ℕ}
    (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ) {eF eF' : Env F} {BK : ℕ}
    (h : ∀ r < BK, ∀ k < e, eF.trace (col0 .traceCur r + k) = eF'.trace (col0 .traceCur r + k)) :
    ∀ r < BK, (gatherEnv b col0 eF).trace r = (gatherEnv b col0 eF').trace r := by
  intro r hr
  simp only [gatherEnv]
  exact Finset.sum_congr rfl fun k _ => by rw [h r hr k k.isLt]

/-- Two traces agreeing below `B` give environments agreeing below `B` (any coins, any publics). -/
theorem envOfTrace_congr {F : Type} [Field F] {w : ℕ} {P P' : Fin w → F[X]} {B : ℕ} (hB : B ≤ w)
    (h : ∀ (j : ℕ) (hj : j < B), P ⟨j, by omega⟩ = P' ⟨j, by omega⟩) (ω x : F) (c p c' p' : ℕ → F) :
    ∀ j < B, (Reify.envOfTrace P ω x c p).trace j = (Reify.envOfTrace P' ω x c' p').trace j := by
  intro j hj
  rw [envOfTrace_trace P ω x c p (by omega), envOfTrace_trace P' ω x c' p' (by omega), h j hj]

/-- A width cast does not change the environment. -/
theorem envOfTrace_cast {F : Type} [Field F] {w₁ w₂ : ℕ} (hw : w₁ = w₂) (P : Fin w₂ → F[X])
    (ω x : F) (c p : ℕ → F) :
    Reify.envOfTrace (fun j : Fin w₁ => P (Fin.cast hw j)) ω x c p = Reify.envOfTrace P ω x c p := by
  subst hw; rfl

/-! ### The concrete read sets (decided) -/

section ReadSets
variable {F : Type} [Field F]

theorem qLt_vKeyP : qLt 18 129 (Cell.vKeyP (F := F)) = true := rfl
theorem qLt_vKeyL : qLt 18 129 (Cell.vKeyL (F := F)) = true := rfl
theorem qLt_vKeyR : qLt 18 129 (Cell.vKeyR (F := F)) = true := rfl
theorem qLt_xKeyS (s : F) : qLt 18 129 (Cell.xKeyS s) = true := rfl
theorem qLt_pxKey : qLt 24 16 (Path.xKey (F := F)) = true := rfl
theorem qLt_pRec : qLt 24 16 (Path.pRec (F := F)) = true := rfl

end ReadSets

/-- A flat map of short lists is short. -/
theorem length_flatMap_le {α β : Type*} (f : α → List β) (c : ℕ) (hf : ∀ a, (f a).length ≤ c) :
    ∀ l : List α, (l.flatMap f).length ≤ c * l.length
  | [] => by simp
  | a :: t => by
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    have := length_flatMap_le f c hf t
    have := hf a
    omega

/-! ## 2. Row environments agree on the round-≤1 columns -/

section Env
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h)

/-- **Cell row environments read only the first `183` columns for the B0/B1 data** (B0 `< 129`,
the B1 `𝕂` roles `< 18`), whatever the coins and publics and whatever the width. -/
theorem cellEnv_congr {w w' : ℕ} (Q : Fin w → F[X]) (Q' : Fin w' → F[X]) (hw : 183 ≤ w)
    (hw' : 183 ≤ w') (hQ : ∀ (j : ℕ) (hj : j < 183), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩)
    (chals pubs chals' pubs' : ℕ → K) (i : Fin n) :
    (∀ j < 183, (cellEnvF b nodes orbit chals pubs Q i).trace j =
      (cellEnvF b nodes orbit chals' pubs' Q' i).trace j) ∧
    (∀ r < 18, (cellEnvK δF b nodes orbit chals pubs Q i).trace r =
      (cellEnvK δF b nodes orbit chals' pubs' Q' i).trace r) := by
  have hF : ∀ j < 183, (cellEnvF b nodes orbit chals pubs Q i).trace j =
      (cellEnvF b nodes orbit chals' pubs' Q' i).trace j := by
    intro j hj
    rw [envOfTrace_trace Q _ _ _ _ (by omega : j < w), envOfTrace_trace Q' _ _ _ _ (by omega : j < w'),
      hQ j hj]
  refine ⟨hF, ?_⟩
  refine gather_trace_congr b _ (BK := 18) (fun r hr k hk => hF _ ?_)
  simp only [ChipTemplate.col0, cellTemplate_baseCols]; omega

/-- **Path row environments read only the first `88` columns for the B0/B1 data** (B0 `< 16`, the
B1 `𝕂` roles `< 24`). -/
theorem pathEnv_congr {w w' : ℕ} (Q : Fin w → F[X]) (Q' : Fin w' → F[X]) (hw : 88 ≤ w)
    (hw' : 88 ≤ w') (hQ : ∀ (j : ℕ) (hj : j < 88), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩)
    (chals pubs chals' pubs' : ℕ → K) (i : ℕ) :
    (∀ j < 88, (pathEnvF b hn nodes orbit chals pubs Q i).trace j =
      (pathEnvF b hn nodes orbit chals' pubs' Q' i).trace j) ∧
    (∀ r < 24, (pathEnvK δF b hn nodes orbit chals pubs Q i).trace r =
      (pathEnvK δF b hn nodes orbit chals' pubs' Q' i).trace r) := by
  have hF : ∀ j < 88, (pathEnvF b hn nodes orbit chals pubs Q i).trace j =
      (pathEnvF b hn nodes orbit chals' pubs' Q' i).trace j := by
    intro j hj
    unfold pathEnvF
    rw [envOfTrace_trace Q _ _ _ _ (by omega : j < w), envOfTrace_trace Q' _ _ _ _ (by omega : j < w'),
      hQ j hj]
  refine ⟨hF, ?_⟩
  unfold pathEnvK
  refine gather_trace_congr b _ (BK := 24) (fun r hr k hk => hF _ ?_)
  simp only [ChipTemplate.col0, pathTemplate_baseCols]; omega

end Env

/-! ## 3. The records and internal consumers, width-generic -/

section Records
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- Validity providers `(vKeyP, mv)` (= `cellVRecords` at any width). -/
def cVRec {w : ℕ} (Q : Fin w → F[X]) : List ((Fin 5 → Quad (algebraMap F K δF)) × F) :=
  (List.finRange n).map fun i =>
    (keyVec δF 5 Cell.vKeyP (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i),
      (cellEnvF b nodes orbit chals pubs Q i).trace Cell.mv)

/-- Validity internal consumers (= `cellVInternal` at any width). -/
def cVInt {w : ℕ} (Q : Fin w → F[X]) : List (Fin 5 → Quad (algebraMap F K δF)) :=
  (List.finRange n).flatMap fun i =>
    (if (cellEnvF b nodes orbit chals pubs Q i).trace Cell.wL = 1 then
      [keyVec δF 5 Cell.vKeyL (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i)] else []) ++
    (if (cellEnvF b nodes orbit chals pubs Q i).trace Cell.wR = 1 then
      [keyVec δF 5 Cell.vKeyR (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i)] else [])

/-- Export providers, two per cell row (= `cellXRecords` at any width). -/
def cXRec {w : ℕ} (Q : Fin w → F[X]) : List ((Fin 11 → Quad (algebraMap F K δF)) × F) :=
  (List.finRange n).flatMap fun i =>
    [(keyVec δF 11 (Cell.xKeyS 0) (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i),
        (cellEnvF b nodes orbit chals pubs Q i).trace Cell.mx),
     (keyVec δF 11 (Cell.xKeyS 1) (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i),
        (cellEnvF b nodes orbit chals pubs Q i).trace Cell.mx1)]

/-- Export internal consumers, one per path row (= `pathXInternal` at any width). -/
def pXInt {w : ℕ} (Q : Fin w → F[X]) : List (Fin 11 → Quad (algebraMap F K δF)) :=
  (List.range n).map fun j =>
    keyVec δF 11 Path.xKey (pathEnvK δF b hn nodes orbit chals pubs Q j) (pathEnvF b hn nodes orbit chals pubs Q j)

/-- Path providers on the `last` rows (= `pathPRecords` at any width). -/
def pPRec {w : ℕ} (Q : Fin w → F[X]) : List ((Fin 8 → Quad (algebraMap F K δF)) × F) :=
  ((List.range n).filter fun j => (pathEnvF b hn nodes orbit chals pubs Q j).trace Path.last = 1).map fun j =>
    (keyVec δF 8 Path.pRec (pathEnvK δF b hn nodes orbit chals pubs Q j) (pathEnvF b hn nodes orbit chals pubs Q j),
      (pathEnvF b hn nodes orbit chals pubs Q j).trace Path.m)

theorem cVRec_chip (Q : Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X]) :
    cellVRecords δF b hn nodes orbit chals pubs Q = cVRec δF b nodes orbit chals pubs Q := rfl
theorem cVInt_chip (Q : Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X]) :
    cellVInternal δF b hn nodes orbit chals pubs Q = cVInt δF b nodes orbit chals pubs Q := rfl
theorem cXRec_chip (Q : Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X]) :
    cellXRecords δF b hn nodes orbit chals pubs Q = cXRec δF b nodes orbit chals pubs Q := rfl
theorem pXInt_chip (Q : Fin (pathChip δF b hn nodes orbit chals pubs).rap.w → F[X]) :
    pathXInternal δF b hn nodes orbit chals pubs Q = pXInt δF b hn nodes orbit chals pubs Q := rfl
theorem pPRec_chip (Q : Fin (pathChip δF b hn nodes orbit chals pubs).rap.w → F[X]) :
    pathPRecords δF b hn nodes orbit chals pubs Q = pPRec δF b hn nodes orbit chals pubs Q := rfl

variable {w w' : ℕ} (Q : Fin w → F[X]) (Q' : Fin w' → F[X]) (chals' pubs' : ℕ → K)

theorem cVRec_congr (hw : 183 ≤ w) (hw' : 183 ≤ w')
    (hQ : ∀ (j : ℕ) (hj : j < 183), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩) :
    cVRec δF b nodes orbit chals pubs Q = cVRec δF b nodes orbit chals' pubs' Q' := by
  unfold cVRec; congr 1; funext i
  obtain ⟨hF, hK⟩ := cellEnv_congr δF b nodes orbit Q Q' hw hw' hQ chals pubs chals' pubs' i
  rw [keyVec_congr δF hK (BF := 129) (fun j hj => hF j (by omega)) 5 _ qLt_vKeyP,
    hF Cell.mv (by decide)]

theorem cVInt_congr (hw : 183 ≤ w) (hw' : 183 ≤ w')
    (hQ : ∀ (j : ℕ) (hj : j < 183), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩) :
    cVInt δF b nodes orbit chals pubs Q = cVInt δF b nodes orbit chals' pubs' Q' := by
  unfold cVInt; congr 1; funext i
  obtain ⟨hF, hK⟩ := cellEnv_congr δF b nodes orbit Q Q' hw hw' hQ chals pubs chals' pubs' i
  rw [keyVec_congr δF hK (BF := 129) (fun j hj => hF j (by omega)) 5 _ qLt_vKeyL,
    keyVec_congr δF hK (BF := 129) (fun j hj => hF j (by omega)) 5 _ qLt_vKeyR,
    hF Cell.wL (by decide), hF Cell.wR (by decide)]

theorem cXRec_congr (hw : 183 ≤ w) (hw' : 183 ≤ w')
    (hQ : ∀ (j : ℕ) (hj : j < 183), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩) :
    cXRec δF b nodes orbit chals pubs Q = cXRec δF b nodes orbit chals' pubs' Q' := by
  unfold cXRec; congr 1; funext i
  obtain ⟨hF, hK⟩ := cellEnv_congr δF b nodes orbit Q Q' hw hw' hQ chals pubs chals' pubs' i
  rw [keyVec_congr δF hK (BF := 129) (fun j hj => hF j (by omega)) 11 _ (qLt_xKeyS 0),
    keyVec_congr δF hK (BF := 129) (fun j hj => hF j (by omega)) 11 _ (qLt_xKeyS 1),
    hF Cell.mx (by decide), hF Cell.mx1 (by decide)]

theorem pXInt_congr (hw : 88 ≤ w) (hw' : 88 ≤ w')
    (hQ : ∀ (j : ℕ) (hj : j < 88), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩) :
    pXInt δF b hn nodes orbit chals pubs Q = pXInt δF b hn nodes orbit chals' pubs' Q' := by
  unfold pXInt; congr 1; funext j
  obtain ⟨hF, hK⟩ := pathEnv_congr δF b hn nodes orbit Q Q' hw hw' hQ chals pubs chals' pubs' j
  rw [keyVec_congr δF hK (BF := 16) (fun j hj => hF j (by omega)) 11 _ qLt_pxKey]

theorem pPRec_congr (hw : 88 ≤ w) (hw' : 88 ≤ w')
    (hQ : ∀ (j : ℕ) (hj : j < 88), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩) :
    pPRec δF b hn nodes orbit chals pubs Q = pPRec δF b hn nodes orbit chals' pubs' Q' := by
  have hE := fun j => pathEnv_congr δF b hn nodes orbit Q Q' hw hw' hQ chals pubs chals' pubs' j
  unfold pPRec
  rw [List.filter_congr (fun j _ => by rw [(hE j).1 Path.last (by decide)])]
  refine List.map_congr_left fun j _ => ?_
  rw [keyVec_congr δF (hE j).2 (BF := 16) (fun c hc => (hE j).1 c (by omega)) 8 _ qLt_pRec,
    (hE j).1 Path.m (by decide)]

theorem mem_cVInt {r : Fin 5 → Quad (algebraMap F K δF)} (hr : r ∈ cVInt δF b nodes orbit chals pubs Q) :
    ∃ i : Fin n, ((cellEnvF b nodes orbit chals pubs Q i).trace Cell.wL = 1 ∧
        r = keyVec δF 5 Cell.vKeyL (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i)) ∨
      ((cellEnvF b nodes orbit chals pubs Q i).trace Cell.wR = 1 ∧
        r = keyVec δF 5 Cell.vKeyR (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i)) := by
  unfold cVInt at hr
  obtain ⟨i, -, hri⟩ := List.mem_flatMap.mp hr
  refine ⟨i, ?_⟩
  rcases List.mem_append.mp hri with hm | hm
  · left; split_ifs at hm with hw
    · exact ⟨hw, List.mem_singleton.mp hm⟩
    · exact absurd hm List.not_mem_nil
  · right; split_ifs at hm with hw
    · exact ⟨hw, List.mem_singleton.mp hm⟩
    · exact absurd hm List.not_mem_nil

theorem cVRec_length : (cVRec δF b nodes orbit chals pubs Q).length = n := by
  simp [cVRec]
theorem cXRec_length : (cXRec δF b nodes orbit chals pubs Q).length ≤ 2 * n := by
  have := length_flatMap_le (fun i : Fin n =>
    [(keyVec δF 11 (Cell.xKeyS 0) (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i),
        (cellEnvF b nodes orbit chals pubs Q i).trace Cell.mx),
     (keyVec δF 11 (Cell.xKeyS 1) (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i),
        (cellEnvF b nodes orbit chals pubs Q i).trace Cell.mx1)]) 2 (fun _ => le_refl _) (List.finRange n)
  simpa [cXRec] using this
theorem cVInt_length : (cVInt δF b nodes orbit chals pubs Q).length ≤ 2 * n := by
  have := length_flatMap_le (fun i : Fin n =>
    (if (cellEnvF b nodes orbit chals pubs Q i).trace Cell.wL = 1 then
      [keyVec δF 5 Cell.vKeyL (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i)] else []) ++
    (if (cellEnvF b nodes orbit chals pubs Q i).trace Cell.wR = 1 then
      [keyVec δF 5 Cell.vKeyR (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i)] else []))
    2 (fun i => by rw [List.length_append]; split_ifs <;> simp) (List.finRange n)
  simpa [cVInt] using this
theorem pXInt_length : (pXInt δF b hn nodes orbit chals pubs Q).length = n := by
  simp [pXInt]
theorem pPRec_length : (pPRec δF b hn nodes orbit chals pubs Q).length ≤ n := by
  unfold pPRec; rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

end Records

/-! ## 4. The family's IO fields -/

/-- Weighted IO facts transported along equal denominators and terminals (records unchanged). -/
def IOFacts.recast {F Kio : Type} [Field F] [Field Kio] [Algebra F Kio] {m : ℕ}
    {den den' : (Fin m → Kio) → Kio} {ρ ρ' : Kio} (hd : den = den') (hρ : ρ = ρ')
    (M : SVFrame.IOFacts F den ρ) : SVFrame.IOFacts F den' ρ' :=
  hd ▸ hρ ▸ M

theorem IOFacts.recast_records {F Kio : Type} [Field F] [Field Kio] [Algebra F Kio] {m : ℕ}
    {den den' : (Fin m → Kio) → Kio} {ρ ρ' : Kio} (hd : den = den') (hρ : ρ = ρ')
    (M : SVFrame.IOFacts F den ρ) : (IOFacts.recast hd hρ M).records = M.records := by
  subst hd; subst hρ; rfl

theorem sat_transport {F : Type} [Field F] {R R' : FixedPreprocessingRAP F} (hR : R = R') {W : ℕ}
    (Q : Fin W → F[X]) (hw : R.rap.w = W) (hw' : R'.rap.w = W) :
    RAP.SatisfiesWithPreprocessing R (fun j => Q (Fin.cast hw j)) →
      RAP.SatisfiesWithPreprocessing R' (fun j => Q (Fin.cast hw' j)) := by
  subst hR; exact id

section Family
attribute [local irreducible] Cell.baseGates Path.baseGates Cell.mixedGates Path.mixedGates

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP : ℕ) {hC : ℕ}

/-- **The VCL-L memory shape** at the chip widths `225 / 112` and the tower round maps. -/
abbrev shapeV : MemShape :=
  shapeVCL hT hP 225 112 Chips.Cell.colRoundT Chips.Path.colRoundT

/-- The cell table's index. -/
def tC : Fin (shapeV hT hP).k := ⟨0, by show 0 < 2; omega⟩
/-- The path table's index. -/
def tP : Fin (shapeV hT hP).k := ⟨1, by show 1 < 2; omega⟩

/-- The cell publics: `0/1 = ρ_V` (Re/Im), `2/3 = ρ_X + y`. -/
def pubsC (ρ : Fin 3 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF)) (i : ℕ) : K :=
  if i = 0 then Quad.re _ (ρ 0) else if i = 1 then Quad.im _ (ρ 0)
  else if i = 2 then Quad.re _ (ρ 1 + y) else if i = 3 then Quad.im _ (ρ 1 + y) else 0

/-- The path publics: `0/1 = y`, `2/3 = ρ_P`. -/
def pubsP (ρ : Fin 3 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF)) (i : ℕ) : K :=
  if i = 0 then Quad.re _ y else if i = 1 then Quad.im _ y
  else if i = 2 then Quad.re _ (ρ 2) else if i = 3 then Quad.im _ (ρ 2) else 0

variable (ρ : Fin 3 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF))

theorem pubsC_01 : Quad.mk _ (pubsC δF ρ y 0) (pubsC δF ρ y 1) = ρ 0 := by
  simp only [pubsC]; exact Quad.mk_re_im _ _
theorem pubsC_23 : Quad.mk _ (pubsC δF ρ y 2) (pubsC δF ρ y 3) = ρ 1 + y := by
  simp only [pubsC]; exact Quad.mk_re_im _ _
theorem pubsP_01 : Quad.mk _ (pubsP δF ρ y 0) (pubsP δF ρ y 1) = y := by
  simp only [pubsP]; exact Quad.mk_re_im _ _
theorem pubsP_23 : Quad.mk _ (pubsP δF ρ y 2) (pubsP δF ρ y 3) = ρ 2 := by
  simp only [pubsP]; exact Quad.mk_re_im _ _

variable (V : VerifierData F K hC (shapeV hT hP)) (x : Unit) (χ : Coins frameVCL K)
  (Q : ∀ t : Fin (shapeV hT hP).k, Fin ((shapeV hT hP).table t).width → F[X])

/-- **The memory chips of `vclMemFamily`**: table `0` the `ok`-gated cell chip, table `1` the
`ok`-gated path chip, at `V.memNodes t`, `V.basis`, `V.orbitM t`, the challenge vector
`chalsVCL δF χ` and the publics `pubsC` / `pubsP`. -/
def vclChip (t : Fin (shapeV hT hP).k) : FixedPreprocessingRAP F :=
  if (t : ℕ) = 0 then
    cellChipOk δF V.basis (V.hM t) (V.memNodes t) (V.orbitM t) (chalsVCL δF χ) (pubsC δF ρ y) (okOf V t)
  else pathChipOk δF V.basis (V.hM t) (V.memNodes t) (V.orbitM t) (chalsVCL δF χ) (pubsP δF ρ y) (okOf V t)

theorem vclChip_width (t : Fin (shapeV hT hP).k) :
    (vclChip δF hT hP ρ y V χ t).rap.w = ((shapeV hT hP).table t).width := by
  unfold vclChip
  split_ifs with ht
  · rw [cellChipOk_w]; unfold shapeV shapeVCL; dsimp only; rw [if_pos ht]
  · rw [pathChipOk_w]; unfold shapeV shapeVCL; dsimp only; rw [if_neg ht]

/-- The committed providers per accumulator (B0/B1 columns only; no coin, no public). -/
def vclResp : ∀ a : Fin 3, List ((Fin (RV.mVCL a) → Quad (algebraMap F K δF)) × F)
  | 0 => cVRec δF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) 0 0 (Q (tC hT hP))
  | 1 => cXRec δF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) 0 0 (Q (tC hT hP))
  | 2 => pPRec δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP)) 0 0 (Q (tP hT hP))

/-- The memory-internal consumers per accumulator: validity = the weighted child keys, export =
every path row's consumed key, path = none. -/
def vclInternal : ∀ a : Fin 3, List (Fin (RV.mVCL a) → Quad (algebraMap F K δF))
  | 0 => cVInt δF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) 0 0 (Q (tC hT hP))
  | 1 => pXInt δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP)) 0 0 (Q (tP hT hP))
  | 2 => []

/-- Provider-row bounds `D / 2D / P`. -/
def vclRespBound (V : VerifierData F K hC (shapeV hT hP)) : Fin 3 → ℕ
  | 0 => V.memRows (tC hT hP)
  | 1 => 2 * V.memRows (tC hT hP)
  | 2 => V.memRows (tP hT hP)

/-- Internal-consumer bounds `2D / P / 0`. -/
def vclInternalBound (V : VerifierData F K hC (shapeV hT hP)) : Fin 3 → ℕ
  | 0 => 2 * V.memRows (tC hT hP)
  | 1 => V.memRows (tP hT hP)
  | 2 => 0

theorem vclInternal_length (a : Fin 3) :
    (vclInternal δF hT hP V Q a).length ≤ vclInternalBound hT hP V a := by
  fin_cases a
  · exact cVInt_length δF _ _ _ _ _ _
  · exact (pXInt_length δF _ _ _ _ _ _ _).le
  · simp [vclInternal, vclInternalBound]

theorem vclResp_length (a : Fin 3) : (vclResp δF hT hP V Q a).length ≤ vclRespBound hT hP V a := by
  fin_cases a
  · exact (cVRec_length δF _ _ _ _ _ _).le
  · exact cXRec_length δF _ _ _ _ _ _
  · exact pPRec_length δF _ _ _ _ _ _ _

/-- The B0/B1 columns of the two tables are the round-`≤ 1` columns. -/
theorem round_cell (j : ℕ) (hj : j < 183) :
    ((shapeV hT hP).table (tC hT hP)).colRound ⟨j, by show j < 225; omega⟩ ≤ 1 := by
  show Chips.Cell.colRoundT ⟨j, _⟩ ≤ 1
  simp only [Chips.Cell.colRoundT, show Chips.Cell.b0CountS = 129 from rfl,
    show Chips.Cell.b1Count = 54 from rfl]
  split_ifs <;> omega

theorem round_path (j : ℕ) (hj : j < 88) :
    ((shapeV hT hP).table (tP hT hP)).colRound ⟨j, by show j < 112; omega⟩ ≤ 1 := by
  show Chips.Path.colRoundT ⟨j, _⟩ ≤ 1
  simp only [Chips.Path.colRoundT, show Chips.Path.b0Count = 16 from rfl,
    show Chips.Path.b1Count = 72 from rfl]
  split_ifs <;> omega

/-- **`respRecords_round`**: the providers read only round-`≤ 1` columns (and no coin). -/
theorem vclResp_round (Q' : ∀ t : Fin (shapeV hT hP).k, Fin ((shapeV hT hP).table t).width → F[X])
    (hQ : ∀ t j, ((shapeV hT hP).table t).colRound j ≤ 1 → Q t j = Q' t j) :
    vclResp δF hT hP V Q = vclResp δF hT hP V Q' := by
  funext a
  fin_cases a
  · exact cVRec_congr δF _ _ _ _ _ _ _ _ _ (show 183 ≤ 225 by omega) (show 183 ≤ 225 by omega)
      fun j hj => hQ _ _ (round_cell hT hP j hj)
  · exact cXRec_congr δF _ _ _ _ _ _ _ _ _ (show 183 ≤ 225 by omega) (show 183 ≤ 225 by omega)
      fun j hj => hQ _ _ (round_cell hT hP j hj)
  · exact pPRec_congr δF _ _ _ _ _ _ _ _ _ _ (show 88 ≤ 112 by omega) (show 88 ≤ 112 by omega)
      fun j hj => hQ _ _ (round_path hT hP j hj)

/-- **`internal_round`**. -/
theorem vclInternal_round (Q' : ∀ t : Fin (shapeV hT hP).k, Fin ((shapeV hT hP).table t).width → F[X])
    (hQ : ∀ t j, ((shapeV hT hP).table t).colRound j ≤ 1 → Q t j = Q' t j) :
    vclInternal δF hT hP V Q = vclInternal δF hT hP V Q' := by
  funext a
  fin_cases a
  · exact cVInt_congr δF _ _ _ _ _ _ _ _ _ (show 183 ≤ 225 by omega) (show 183 ≤ 225 by omega)
      fun j hj => hQ _ _ (round_cell hT hP j hj)
  · exact pXInt_congr δF _ _ _ _ _ _ _ _ _ _ (show 88 ≤ 112 by omega) (show 88 ≤ 112 by omega)
      fun j hj => hQ _ _ (round_path hT hP j hj)
  · rfl

/-! ### Acceptance of the two chips -/

/-- Table `0`'s chip at its parameters. -/
abbrev cellOk : FixedPreprocessingRAP F :=
  cellChipOk δF V.basis (V.hM (tC hT hP)) (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) (chalsVCL δF χ)
    (pubsC δF ρ y) (okOf V (tC hT hP))

/-- Table `1`'s chip at its parameters. -/
abbrev pathOk : FixedPreprocessingRAP F :=
  pathChipOk δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP)) (chalsVCL δF χ)
    (pubsP δF ρ y) (okOf V (tP hT hP))

theorem cellOk_w' : (cellOk δF hT hP ρ y V χ).rap.w = ((shapeV hT hP).table (tC hT hP)).width := by
  rw [cellChipOk_w]; rfl
theorem pathOk_w' : (pathOk δF hT hP ρ y V χ).rap.w = ((shapeV hT hP).table (tP hT hP)).width := by
  rw [pathChipOk_w]; rfl

/-- The cell trace at the chip's width. -/
def QC : Fin (cellOk δF hT hP ρ y V χ).rap.w → F[X] :=
  fun j => Q (tC hT hP) (Fin.cast (cellOk_w' δF hT hP ρ y V χ) j)
/-- The path trace at the chip's width. -/
def QP : Fin (pathOk δF hT hP ρ y V χ).rap.w → F[X] :=
  fun j => Q (tP hT hP) (Fin.cast (pathOk_w' δF hT hP ρ y V χ) j)

theorem vclChip_tC : vclChip δF hT hP ρ y V χ (tC hT hP) = cellOk δF hT hP ρ y V χ := by
  unfold vclChip; exact if_pos rfl
theorem vclChip_tP : vclChip δF hT hP ρ y V χ (tP hT hP) = pathOk δF hT hP ρ y V χ := by
  unfold vclChip; exact if_neg Nat.one_ne_zero

variable {δF hT hP ρ y V χ Q} in
/-- **An accepted pair of memory traces**: both datum checks hold (`GoodM`) and both plain chips
are satisfied. -/
theorem vcl_accepted
    (h : ∀ t, RAP.SatisfiesWithPreprocessing (vclChip δF hT hP ρ y V χ t)
      (fun j => Q t (Fin.cast (vclChip_width δF hT hP ρ y V χ t) j))) :
    (GoodM V (tC hT hP) ∧ RAP.SatisfiesWithPreprocessing
      (cellChip δF V.basis (V.hM (tC hT hP)) (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) (chalsVCL δF χ)
        (pubsC δF ρ y)) (QC δF hT hP ρ y V χ Q)) ∧
    (GoodM V (tP hT hP) ∧ RAP.SatisfiesWithPreprocessing
      (pathChip δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP)) (chalsVCL δF χ)
        (pubsP δF ρ y)) (QP δF hT hP ρ y V χ Q)) := by
  have h0 := sat_transport (vclChip_tC δF hT hP ρ y V χ) (Q (tC hT hP)) _ (cellOk_w' δF hT hP ρ y V χ)
    (h (tC hT hP))
  have h1 := sat_transport (vclChip_tP δF hT hP ρ y V χ) (Q (tP hT hP)) _ (pathOk_w' δF hT hP ρ y V χ)
    (h (tP hT hP))
  obtain ⟨hok0, hs0⟩ := cellChipOk_sat _ _ _ _ _ _ _ _ _ h0
  obtain ⟨hok1, hs1⟩ := pathChipOk_sat _ _ _ _ _ _ _ _ _ h1
  exact ⟨⟨goodM_of_ok hok0, hs0⟩, ⟨goodM_of_ok hok1, hs1⟩⟩

/-! ### The chip-typed lists are the family's -/

theorem cellVInternal_eq :
    cellVInternal δF V.basis (V.hM (tC hT hP)) (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) (chalsVCL δF χ)
      (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q) = vclInternal δF hT hP V Q 0 := by
  erw [cVInt_chip]
  exact cVInt_congr δF _ _ _ _ _ _ _ _ _ (by rw [cell_w]; omega)
    (show 183 ≤ 225 by omega) fun j hj => rfl

theorem pathXInternal_eq :
    pathXInternal δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP)) (chalsVCL δF χ)
      (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q) = vclInternal δF hT hP V Q 1 := by
  erw [pXInt_chip]
  exact pXInt_congr δF _ _ _ _ _ _ _ _ _ _ (by rw [path_w]; omega)
    (show 88 ≤ 112 by omega) fun j hj => rfl

theorem cellVRecords_eq :
    cellVRecords δF V.basis (V.hM (tC hT hP)) (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) (chalsVCL δF χ)
      (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q) = vclResp δF hT hP V Q 0 := by
  erw [cVRec_chip]
  exact cVRec_congr δF _ _ _ _ _ _ _ _ _ (by rw [cell_w]; omega)
    (show 183 ≤ 225 by omega) fun j hj => rfl

theorem cellXRecords_eq :
    cellXRecords δF V.basis (V.hM (tC hT hP)) (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) (chalsVCL δF χ)
      (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q) = vclResp δF hT hP V Q 1 := by
  erw [cXRec_chip]
  exact cXRec_congr δF _ _ _ _ _ _ _ _ _ (by rw [cell_w]; omega)
    (show 183 ≤ 225 by omega) fun j hj => rfl

theorem pathPRecords_eq :
    pathPRecords δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP)) (chalsVCL δF χ)
      (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q) = vclResp δF hT hP V Q 2 := by
  erw [pPRec_chip]
  exact pPRec_congr δF _ _ _ _ _ _ _ _ _ _ (by rw [path_w]; omega)
    (show 88 ≤ 112 by omega) fun j hj => rfl

/-! ### `ioFacts` -/

variable {δF hT hP ρ y V χ Q} in
/-- **`ioFacts`**: the three accumulators' weighted IO facts from an accepted pair of memory traces
(validity `cellValidityFacts`, export `cellExportFacts`, path `pathProviderFacts`). -/
def vclIoFacts
    (h : ∀ t, RAP.SatisfiesWithPreprocessing (vclChip δF hT hP ρ y V χ t)
      (fun j => Q t (Fin.cast (vclChip_width δF hT hP ρ y V χ t) j))) :
    ∀ a : Fin 3, SVFrame.IOFacts F
      (FiniteIO.compress (m := RV.mVCL a) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ))
      (ρ a + ((vclInternal δF hT hP V Q a).map fun r =>
        (FiniteIO.compress (m := RV.mVCL a) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ) r)⁻¹).sum)
  | 0 => IOFacts.recast rfl (by rw [pubsC_01, cellVInternal_eq]; rfl)
      (cellValidityFacts δF V.basis (V.hM (tC hT hP)) (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP))
        (chalsVCL δF χ) (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q) (vcl_accepted h).1.2.1 (vcl_accepted h).1.2.2
        (vcl_accepted h).1.1.2.1 (vcl_accepted h).1.1.adj _ _ (chalsVCL_ok δF χ 11))
  | 1 => IOFacts.recast rfl (by rw [pathXInternal_eq]; rfl)
      (cellExportFacts δF V.basis (V.hM (tC hT hP)) (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP))
        (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP)) (chalsVCL δF χ) (pubsC δF ρ y)
        (pubsP δF ρ y) (QC δF hT hP ρ y V χ Q) (QP δF hT hP ρ y V χ Q)
        (vcl_accepted h).1.2.1 (vcl_accepted h).1.2.2 (vcl_accepted h).1.1.2.1 (vcl_accepted h).1.1.adj
        (vcl_accepted h).2.2.1 (vcl_accepted h).2.2.2 (vcl_accepted h).2.1.2.1 (vcl_accepted h).2.1.adj
        _ _ (chalsVCL_ok δF χ 11) (ρ 1) (by rw [pubsC_23, pubsP_01]))
  | 2 => IOFacts.recast rfl (by rw [pubsP_23]; simp [vclInternal])
      (pathProviderFacts δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP))
        (chalsVCL δF χ) (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q) (vcl_accepted h).2.2.1 (vcl_accepted h).2.2.2
        (vcl_accepted h).2.1.2.1 (vcl_accepted h).2.1.adj _ _ (chalsVCL_ok δF χ 11))

variable {δF hT hP ρ y V χ Q} in
/-- **`ioFacts_records`**: the IO facts' providers are the committed records `vclResp`. -/
theorem vclIoFacts_records
    (h : ∀ t, RAP.SatisfiesWithPreprocessing (vclChip δF hT hP ρ y V χ t)
      (fun j => Q t (Fin.cast (vclChip_width δF hT hP ρ y V χ t) j))) (a : Fin 3) :
    (vclIoFacts h a).records = vclResp δF hT hP V Q a := by
  fin_cases a
  · exact (IOFacts.recast_records _ _ _).trans (cellVRecords_eq δF hT hP ρ y V χ Q)
  · exact (IOFacts.recast_records _ _ _).trans (cellXRecords_eq δF hT hP ρ y V χ Q)
  · exact (IOFacts.recast_records _ _ _).trans (pathPRecords_eq δF hT hP ρ y V χ Q)

variable {δF hT hP ρ y V χ Q} in
/-- **`ioFacts_length`**: provider rows `≤ D / 2D / P`. -/
theorem vclIoFacts_length
    (h : ∀ t, RAP.SatisfiesWithPreprocessing (vclChip δF hT hP ρ y V χ t)
      (fun j => Q t (Fin.cast (vclChip_width δF hT hP ρ y V χ t) j))) (a : Fin 3) :
    (vclIoFacts h a).records.length ≤ vclRespBound hT hP V a := by
  rw [vclIoFacts_records h a]; exact vclResp_length δF hT hP V Q a

theorem mem_ite_singleton {α : Type*} {p : Prop} [Decidable p] {x r : α}
    (h : r ∈ (if p then [x] else [])) : p ∧ r = x := by
  by_cases hp : p
  · rw [if_pos hp] at h; exact ⟨hp, List.mem_singleton.mp h⟩
  · rw [if_neg hp] at h; exact absurd h List.not_mem_nil

variable {δF hT hP ρ y V χ Q} in
theorem cellInternal_ne_zero
    (hsat : (cellChip δF V.basis (V.hM (tC hT hP)) (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP))
      (chalsVCL δF χ) (pubsC δF ρ y)).rap.Satisfies (QC δF hT hP ρ y V χ Q)) :
    ∀ r ∈ cellVInternal δF V.basis (V.hM (tC hT hP)) (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP))
      (chalsVCL δF χ) (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q),
      FiniteIO.compress (m := 5) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ) r ≠ 0 := by
  intro r hr
  erw [cVInt_chip] at hr
  obtain ⟨i, ⟨hw, rfl⟩ | ⟨hw, rfl⟩⟩ := mem_cVInt δF _ _ _ _ _ _ hr
  · obtain ⟨-, ⟨hL, -⟩, -⟩ := cell_inv_facts δF V.basis (V.hM (tC hT hP)) (V.memNodes (tC hT hP))
      (V.orbitM (tC hT hP)) (chalsVCL δF χ) (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q) hsat i
    have e := cell_compress (b := V.basis) (hn := V.hM (tC hT hP)) (nodes := V.memNodes (tC hT hP))
      (orbit := V.orbitM (tC hT hP)) (pubs := pubsC δF ρ y) (Q := QC δF hT hP ρ y V χ Q) (m := 5)
      _ _ (chalsVCL_ok δF χ 11) Cell.vKeyL rfl (by norm_num) i
    exact fun h0 => hL hw (e.symm.trans h0)
  · obtain ⟨-, -, ⟨hR, -⟩⟩ := cell_inv_facts δF V.basis (V.hM (tC hT hP)) (V.memNodes (tC hT hP))
      (V.orbitM (tC hT hP)) (chalsVCL δF χ) (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q) hsat i
    have e := cell_compress (b := V.basis) (hn := V.hM (tC hT hP)) (nodes := V.memNodes (tC hT hP))
      (orbit := V.orbitM (tC hT hP)) (pubs := pubsC δF ρ y) (Q := QC δF hT hP ρ y V χ Q) (m := 5)
      _ _ (chalsVCL_ok δF χ 11) Cell.vKeyR rfl (by norm_num) i
    exact fun h0 => hR hw (e.symm.trans h0)

variable {δF hT hP ρ y V χ Q} in
theorem pathInternal_ne_zero
    (hsat : (pathChip δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP))
      (chalsVCL δF χ) (pubsP δF ρ y)).rap.Satisfies (QP δF hT hP ρ y V χ Q)) :
    ∀ r ∈ pathXInternal δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP))
      (chalsVCL δF χ) (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q),
      FiniteIO.compress (m := 11) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ) r ≠ 0 := by
  intro r hr
  unfold pathXInternal at hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  have hjn := List.mem_range.mp hj
  have e := path_compress δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP))
    (chalsVCL δF χ) (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q) _ _ (chalsVCL_ok δF χ 11) j hjn
  exact fun h0 => (path_xinv δF V.basis (V.hM (tP hT hP)) (V.memNodes (tP hT hP)) (V.orbitM (tP hT hP))
    (chalsVCL δF χ) (pubsP δF ρ y) (QP δF hT hP ρ y V χ Q) hsat j hjn).1 (e.symm.trans h0)

variable {δF hT hP ρ y V χ Q} in
/-- **`internal_ne_zero`**: every internal consumer's denominator is nonzero (the consumer inverse
gates). -/
theorem vclInternal_ne_zero
    (h : ∀ t, RAP.SatisfiesWithPreprocessing (vclChip δF hT hP ρ y V χ t)
      (fun j => Q t (Fin.cast (vclChip_width δF hT hP ρ y V χ t) j))) (a : Fin 3) :
    ∀ r ∈ vclInternal δF hT hP V Q a,
      FiniteIO.compress (m := RV.mVCL a) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ) r ≠ 0 := by
  have hA := vcl_accepted h
  match a with
  | 0 =>
    rw [← cellVInternal_eq δF hT hP ρ y V χ Q]
    exact cellInternal_ne_zero hA.1.2.1
  | 1 =>
    rw [← pathXInternal_eq δF hT hP ρ y V χ Q]
    exact pathInternal_ne_zero hA.2.2.1
  | 2 => intro r hr; exact absurd hr List.not_mem_nil

variable {δF hT hP ρ y V χ Q} in
/-- **`serves`** (`serves_of_weighted_lookup` per accumulator; `reqCondVCL` is `True`, the summand
exclusion is not used): under the joint weighted IO exclusion and the consumer count, every request
record is a provided record. -/
theorem vcl_serves [DecidableEq K] [Fintype F]
    (h : ∀ t, RAP.SatisfiesWithPreprocessing (vclChip δF hT hP ρ y V χ t)
      (fun j => Q t (Fin.cast (vclChip_width δF hT hP ρ y V χ t) j)))
    (reqs : ∀ a : Fin 3, List (Fin (RV.mVCL a) → Quad (algebraMap F K δF)))
    (hsum : ∀ a, ((reqs a).map fun r =>
      (FiniteIO.compress (m := RV.mVCL a) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ) r)⁻¹).sum = ρ a)
    (hne : ∀ a, ∀ r ∈ reqs a,
      FiniteIO.compress (m := RV.mVCL a) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ) r ≠ 0)
    (hio : ∀ a, (ioSpecVCLQuad (algebraMap F K δF)).pair χ ∉ FiniteIO.IOFailureEventW
      (reqs a ++ vclInternal δF hT hP V Q a) (liftWts (vclResp δF hT hP V Q a)))
    (hcount : ∀ a, (reqs a ++ vclInternal δF hT hP V Q a).length < ringChar (Quad (algebraMap F K δF))) :
    ∀ a, ∀ r ∈ reqs a, r ∈ (vclIoFacts h a).records.map Prod.fst := by
  intro a
  have hio' : (ioSpecVCLQuad (algebraMap F K δF)).pair χ ∉ FiniteIO.IOFailureEventW
      (reqs a ++ vclInternal δF hT hP V Q a) (liftWts (vclIoFacts h a).records) := by
    rw [vclIoFacts_records h a]; exact hio a
  exact serves_of_weighted_lookup (I := ioSpecVCLQuad (algebraMap F K δF)) (m := RV.mVCL)
    (p := ringChar (Quad (algebraMap F K δF))) χ a (reqs a) (vclInternal δF hT hP V Q a) (ρ a)
    (vclIoFacts h a) (hsum a) (hne a) (vclInternal_ne_zero h a) hio' (hcount a)

end Family

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
