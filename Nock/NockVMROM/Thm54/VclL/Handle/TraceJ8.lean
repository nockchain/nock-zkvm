/-
  Nock/NockVMROM/Thm54/VclL/Handle/TraceJ8.lean

  **The J-8 trace type `TrJ8` and its staging `StJ8`, and the
  first readouts from the real traces with their read-set and budget lemmas.**

  * §1 **`TrJ8 F`**: the six chip traces at their fixed widths — compute `computeChipVCLHX` (`123`: round-0 `69`, then
    `54`), cell `cellChipHQKW` (`242`: base `134`, `𝕂`-roles `18 / 18` in rounds `1 / 2`), walk `walkChipJ8` (`166`:
    `25 / 72 / 69`), J `jetChipJ8` (`71`: `29`, then `42`), atom table `atomChipHQ` (`349`: `205 / 54 / 90`), atom walk
    `walkChipHQK` (`166`).  The round of a column is the template's (`ChipTemplate.baseColsOf / extColsOf`: base columns
    first, all in round `0`; then the `𝕂`-roles round by round, `3` coordinates each).  The widths are checked against the
    chips (`widthC_eq` … `widthV_eq`, `rfl`).
  * §3 **the atom walk's data `wdVJ8`** (#9, ruled `atomWalkJ8C`): `walkDataOf` of the restriction `21 → 25` of the
    atom-walk trace (`AtomWalkAW.restrictWalkK`'s map, coins and publics `0`); **`wdVJ8_reads`**: along `StJ8` it reads
    `coinsBelow frameJ8 1` (its columns are of round `≤ 1`); `wdVJ8_h` (`h = n_V`).  `withWalkV`: a `DataJ8C` from a
    `DataJ8` and the real readout.
  * §4 **the walk chain's data `wdWJ8`** (#1, `Data40J8.wdW`) on the J-8 walk trace, and `wdWJ8_reads` along
    `St40 StJ8` at `coinsBelow frameVSQ 1`.
  * §5 **the compute rows `cRowsJ8`** (#1, `Data40J8.cRows`): row `i` is `WalkBridgeJ8.rowsWX` of the coin-free
    row environment and its one-hot state (`stOfEnv`); `rowW_congr` (a row reads only round-0 columns), so
    **`cRowsJ8_const`** along `St40 StJ8`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C
import Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
import Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW
import Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8
import Nock.NockVMROM.Thm54.VclL.Handle.CWalkChipVS
import Nock.NockVMROM.Thm54.VclL.Handle.CensusVS
import Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (walkDataOf walkDataOf_congr cellB0Of cellB0Of_congr)
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP

noncomputable section

/-! ## 1. The trace type and its staging -/

/-- **The six J-8 chip traces** at their fixed widths. -/
structure TrJ8 (F : Type) [Field F] where
  C : Fin 123 → F[X]
  M : Fin 242 → F[X]
  W : Fin 166 → F[X]
  J : Fin 71 → F[X]
  A : Fin 349 → F[X]
  V : Fin 166 → F[X]

/-- Compute: round-0 block `69`, then the coin-dependent block. -/
def crC (j : Fin 123) : ℕ := if (j : ℕ) < 69 then 0 else 1
/-- Cell `HQKW`: base `134`, round-1 roles to `188`, round-2 roles. -/
def crM (j : Fin 242) : ℕ := if (j : ℕ) < 134 then 0 else if (j : ℕ) < 188 then 1 else 2
/-- The two walks (`walkChipJ8`, `walkChipHQK`): base `25`, round-1 roles to `97`, round-2 roles. -/
def crW (j : Fin 166) : ℕ := if (j : ℕ) < 25 then 0 else if (j : ℕ) < 97 then 1 else 2
/-- J: base `29`, round-1 roles. -/
def crJ (j : Fin 71) : ℕ := if (j : ℕ) < 29 then 0 else 1
/-- Atom table: base `205`, round-1 roles to `259`, round-2 roles. -/
def crA (j : Fin 349) : ℕ := if (j : ℕ) < 205 then 0 else if (j : ℕ) < 259 then 1 else 2

/-- **`StJ8`**: every column of every chip is staged at its round. -/
def StJ8 {F K : Type} [Field F] (Q : Coins frameJ8 K → TrJ8 F) : Prop :=
  StagedCols frameJ8 crC (fun χ => (Q χ).C) ∧ StagedCols frameJ8 crM (fun χ => (Q χ).M) ∧
    StagedCols frameJ8 crW (fun χ => (Q χ).W) ∧ StagedCols frameJ8 crJ (fun χ => (Q χ).J) ∧
    StagedCols frameJ8 crA (fun χ => (Q χ).A) ∧ StagedCols frameJ8 crW (fun χ => (Q χ).V)

section Widths
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δ : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

theorem widthC_eq (chalV pubVal : ℕ → F) :
    (ChipHX.computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w = 123 := rfl
theorem widthM_eq : (CellTwinKW.cellChipHQKW δ b hn nodes orbit chals pubs).rap.w = 242 := rfl
theorem widthW_eq (kroots : ℕ) : (WalkJ8.walkChipJ8 δ kroots b hn nodes orbit chals pubs).rap.w = 166 :=
  WalkJ8.walkChipJ8_width δ kroots b hn nodes orbit chals pubs
theorem widthJ_eq (lay : Fin n → Nock.Jet.ChipJ8.PRow) :
    (Nock.Jet.ChipJ8.jetChipJ8 δ b nodes orbit chals pubs lay).rap.w = 71 :=
  Nock.Jet.ChipJ8.jetChipJ8_width δ b nodes orbit chals pubs lay
theorem widthA_eq : (AtomChipHQ.atomChipHQ δ b hn nodes orbit chals pubs).rap.w = 349 :=
  AtomChipHQ.atomChipHQ_width δ b hn nodes orbit chals pubs
theorem widthV_eq (kroots : ℕ) : (CellTwinK.walkChipHQK δ kroots b hn nodes orbit chals pubs).rap.w = 166 :=
  CellTwinK.walkChipHQK_width δ kroots b hn nodes orbit chals pubs

end Widths

/-! ## 2. Staging tools -/

section Stage
variable {K : Type}

/-- A staged column of round `≤ r` agrees at coins agreeing on every coin sampled before round `r`. -/
theorem staged_eq {ι β : Type} {cr : ι → ℕ} {Q : Coins frameJ8 K → ι → β} (hQ : StagedCols frameJ8 cr Q)
    {r : ℕ} {χ χ' : Coins frameJ8 K} (h : ∀ i, frameJ8.sampledAfter i < r → χ i = χ' i) (j : ι) (hj : cr j ≤ r) :
    Q χ j = Q χ' j :=
  hQ j χ χ' fun i hi => h i (lt_of_lt_of_le hi hj)

theorem below_of_mem {χ χ' : Coins frameJ8 K} (h : ∀ i ∈ coinsBelow frameJ8 1, χ i = χ' i) :
    ∀ i, frameJ8.sampledAfter i < 1 → χ i = χ' i := fun i hi =>
  h i (by simp only [coinsBelow, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi)

theorem extY_below {ψ ψ' : Coins frameVSQ K} (y₁ y₂ : K) (h : ∀ i ∈ coinsBelow frameVSQ 1, ψ i = ψ' i) :
    ∀ i, frameJ8.sampledAfter i < 1 → extY ψ y₁ y₂ i = extY ψ' y₁ y₂ i := by
  intro i hi
  unfold extY
  split_ifs with h17
  · refine h _ ?_
    simp only [coinsBelow, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [toVSQ_sampled]; exact hi
  · rfl
  · rfl

end Stage

/-! ## 3. The atom walk's data (#9) -/

theorem shV : ∀ j < 132, shiftCol 21 25 j < 166 := by
  intro j hj; unfold shiftCol; split_ifs <;> omega

theorem shV_round (j : ℕ) (hj : j < 93) : crW ⟨shiftCol 21 25 j, shV j (by omega)⟩ ≤ 1 := by
  simp only [crW, shiftCol]; split_ifs <;> omega

section Walk
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K)

/-- **The atom walk's data of a J-8 trace** (`AtomWalkAW.restrictWalkK`'s restriction, coins and publics `0`). -/
def wdVJ8 (kroots : ℕ) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (tr : TrJ8 F) : WalkVCL.WalkData (ringChar F) (Quad (algebraMap F K δF)) :=
  walkDataOf δF kroots b hn nodes orbit (fun _ => 0) (fun _ => 0) (restrictQ 21 25 shV tr.V)

/-- The same, at any coins and publics (the readout is coin-free). -/
theorem wdVJ8_eq (kroots : ℕ) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (chals pubs : ℕ → K) (tr : TrJ8 F) :
    wdVJ8 δF b kroots hn nodes orbit tr = walkDataOf δF kroots b hn nodes orbit chals pubs (restrictQ 21 25 shV tr.V) :=
  walkDataOf_congr δF kroots b hn nodes orbit _ _ (by norm_num) (by norm_num) (fun _ _ => rfl) _ _ _ _

/-- **Read set of #9**: along `StJ8`, the atom walk's data reads only the round-0 coins. -/
theorem wdVJ8_reads (kroots : ℕ) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (Q : Coins frameJ8 K → TrJ8 F) (hQ : StJ8 Q) :
    ReadsOnC frameJ8 (coinsBelow frameJ8 1) fun χ => wdVJ8 δF b kroots hn nodes orbit (Q χ) := by
  intro χ χ' hχ
  refine walkDataOf_congr δF kroots b hn nodes orbit _ _ (by norm_num) (by norm_num) (fun j hj => ?_) _ _ _ _
  exact staged_eq hQ.2.2.2.2.2 (below_of_mem hχ) _ (shV_round j hj)

theorem wdVJ8_h (kroots : ℕ) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (tr : TrJ8 F) : (wdVJ8 δF b kroots hn nodes orbit tr).h = n := rfl

/-- **The walk chain's data of a J-8 trace** (#1, the J-8 walk `walkChipJ8`, same restriction). -/
def wdWJ8 (kroots : ℕ) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (tr : TrJ8 F) : WalkVCL.WalkData (ringChar F) (Quad (algebraMap F K δF)) :=
  walkDataOf δF kroots b hn nodes orbit (fun _ => 0) (fun _ => 0) (restrictQ 21 25 shV tr.W)

theorem wdWJ8_h (kroots : ℕ) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (tr : TrJ8 F) : (wdWJ8 δF b kroots hn nodes orbit tr).h = n := rfl

theorem wdWJ8_reads (kroots : ℕ) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (Q : Coins frameVSQ K → TrJ8 F) (hQ : St40 (StJ8 (F := F)) Q) :
    ReadsOnC frameVSQ (coinsBelow frameVSQ 1) fun ψ => wdWJ8 δF b kroots hn nodes orbit (Q ψ) := by
  obtain ⟨Q', hQ', y₁, y₂, rfl⟩ := hQ
  intro ψ ψ' hψ
  refine walkDataOf_congr δF kroots b hn nodes orbit _ _ (by norm_num) (by norm_num) (fun j hj => ?_) _ _ _ _
  exact staged_eq hQ'.2.2.1 (extY_below y₁ y₂ hψ) _ (shV_round j hj)

end Walk

/-! ## 3b. A `DataJ8C` from the real atom-walk readout -/

section WithV
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F] [Fintype K]
  [DecidableEq K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K)
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] [Algebra Nock.Atoms.Fp (Quad (algebraMap F K δF))]
  {r : RowsJ8} {P g : ℕ}

/-- **#9 at the real trace**: `R` with the atom walk's data read off the atom-walk trace (`n_V ≤ AW`). -/
def withWalkV (R : DataJ8 (q := ringChar F) (algebraMap F K δF) (TrJ8 F) StJ8 r P) (kroots : ℕ) {h n : ℕ}
    (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (hAW : n ≤ r.AW) :
    DataJ8C (q := ringChar F) (algebraMap F K δF) (TrJ8 F) StJ8 r P g where
  D := R
  wdC tr _ := wdVJ8 δF b kroots hn nodes orbit tr
  wdC_le tr _ := hAW
  wdC_reads Q hQ := wdVJ8_reads δF b kroots hn nodes orbit Q hQ

end WithV

/-! ## 5. The compute rows (#1) -/

section Rows
variable {p : ℕ} [Fact p.Prime]

open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (RowVSX)
open Nock.Edit (StateX)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX (rowOfX stIdx)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8 (rowW rowsWX)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX

/-- The state of a one-hot index (`stIdx`'s inverse; default `s0`). -/
def stOfIdx : ℕ → StateX
  | 0 => .s0 | 1 => .s1 | 2 => .s2 | 3 => .s3 | 4 => .s4 | 5 => .s5 | 6 => .s6 | 7 => .s7 | 8 => .s8
  | 9 => .s9 | 10 => .cons | 11 => .s10 | 12 => .s10L | 13 => .s10T | 14 => .s11s | 15 => .s11d
  | 16 => .s11j | _ => .s0

theorem stOfIdx_stIdx (st : StateX) : stOfIdx (stIdx st) = st := by cases st <;> rfl

/-- The decoded state of a row: its first one-hot selector equal to `1`. -/
def stOfEnv (env : Env (ZMod p)) : StateX :=
  stOfIdx (((List.range 17).find? fun j => decide (env.trace j = 1)).getD 0)

theorem stOfEnv_congr {e e' : Env (ZMod p)} (h : ∀ j < 69, e.trace j = e'.trace j) : stOfEnv e = stOfEnv e' := by
  unfold stOfEnv
  congr 2
  exact Handle.CWalkChipVS.find_congr _ _ _ fun j hj => by
    rw [h j (by have := List.mem_range.mp hj; omega)]

/-- A row decodes from its round-0 columns only. -/
theorem rowW_congr {e e' : Env (ZMod p)} (h : ∀ j < 69, e.trace j = e'.trace j) (st : StateX) :
    rowW e st = rowW e' st := by
  have hd : ∀ hh : ChipH.Hd, hh.k < 69 → hh.v < 69 → hdV e hh = hdV e' hh := by
    intro hh hk hv; simp only [hdV, h _ hk, h _ hv]
  have e0 := hd xS (by decide) (by decide)
  have e1 := hd xF (by decide) (by decide)
  have e2 := hd xE (by decide) (by decide)
  have e3 := hd xSf1 (by decide) (by decide)
  have e4 := hd xSf2 (by decide) (by decide)
  have e5 := hd xFh (by decide) (by decide)
  have e6 := hd xFt (by decide) (by decide)
  have e7 := hd xFth (by decide) (by decide)
  have e8 := hd xFtt (by decide) (by decide)
  have e9 := hd xFtth (by decide) (by decide)
  have e10 := hd xFttt (by decide) (by decide)
  have e11 := hd xM (by decide) (by decide)
  have ev := h vX (by decide)
  cases st <;> simp only [rowW, rowOfX, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, ev]

/-- Row `i`'s coin-free environment on the compute trace (rows past `n` read row `0`). -/
def envCJ8 {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (q : Fin 123 → (ZMod p)[X]) (i : ℕ) : Env (ZMod p) :=
  Framework.Reify.envOfTrace q orbit.ω (if hi : i < n then nodes ⟨i, hi⟩ else nodes ⟨0, hn⟩) (fun _ => 0) (fun _ => 0)

/-- **The compute rows of a J-8 trace** (1-indexed, `rowsWX` of the coin-free environments and their one-hot
states). -/
def cRowsJ8 {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (tr : TrJ8 (ZMod p)) : ℕ → RowVSX :=
  rowsWX (envCJ8 hn nodes orbit tr.C) (fun i => stOfEnv (envCJ8 hn nodes orbit tr.C i))

theorem cRowsJ8_congr {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    {tr tr' : TrJ8 (ZMod p)} (hc : ∀ j : Fin 123, (j : ℕ) < 69 → tr.C j = tr'.C j) :
    cRowsJ8 hn nodes orbit tr = cRowsJ8 hn nodes orbit tr' := by
  have hE : ∀ i, ∀ j < 69, (envCJ8 hn nodes orbit tr.C i).trace j = (envCJ8 hn nodes orbit tr'.C i).trace j :=
    fun i => Handle.IOVS.envOfTrace_congr 69 _ _ hc _ _ _ _ _ _
  funext i
  show rowW _ (stOfEnv _) = rowW _ (stOfEnv _)
  rw [stOfEnv_congr (hE (i - 1)), rowW_congr (hE (i - 1))]

theorem cRowsJ8_const {K : Type} {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
    (orbit : StrictOrbitDomain (ZMod p) 3 h) (Q : Coins frameVSQ K → TrJ8 (ZMod p)) (hQ : St40 (StJ8 (F := ZMod p)) Q)
    (ψ ψ' : Coins frameVSQ K) : cRowsJ8 hn nodes orbit (Q ψ) = cRowsJ8 hn nodes orbit (Q ψ') := by
  obtain ⟨Q', hQ', y₁, y₂, rfl⟩ := hQ
  refine cRowsJ8_congr hn nodes orbit fun j hj => staged_eq hQ'.1 (r := 0) (fun i hi => absurd hi (by omega)) j ?_
  simp only [crC, if_pos hj, le_refl]

end Rows

/-! ## 6. The cell and atom tables' round-0 rows, the census readout -/

section Tables
variable {F : Type} [Field F] [DecidableEq F] [Fintype F]

/-- **The round-0 rows of a cell-layout table** (`cellB0Of` of the coin-free row environments; columns `< 129` are
the original cell chip's in the cell table `HQKW` and in the atom table alike). -/
def rowsB0 {w h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (q : Fin w → F[X]) :
    List (CellRowB0 (ringChar F)) :=
  List.ofFn fun i : Fin n => cellB0Of (Framework.Reify.envOfTrace q orbit.ω (nodes i) (fun _ => 0) (fun _ => 0))

theorem rowsB0_length {w h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (q : Fin w → F[X]) :
    (rowsB0 nodes orbit q).length = n := by simp [rowsB0]

theorem rowsB0_congr {w h n : ℕ} (hw : 129 ≤ w) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    {q q' : Fin w → F[X]} (hq : ∀ (j : ℕ) (hj : j < 129), q ⟨j, by omega⟩ = q' ⟨j, by omega⟩) :
    rowsB0 nodes orbit q = rowsB0 nodes orbit q' := by
  unfold rowsB0
  congr 1
  funext i
  exact cellB0Of_congr (Handle.CensusVS.env_trace_129 q q' hw hw hq orbit _ _ _ _ _)

/-- The cell table's rows (#1's dyck / census, the census readout's `t`). -/
def rowsMJ8 {h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (tr : TrJ8 F) :
    List (CellRowB0 (ringChar F)) := rowsB0 nodes orbit tr.M

/-- The atom table's rows (#8). -/
def rowsAJ8 {h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (tr : TrJ8 F) :
    List (CellRowB0 (ringChar F)) := rowsB0 nodes orbit tr.A

variable {K : Type}

theorem rowsMJ8_const {h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (Q : Coins frameJ8 K → TrJ8 F) (hQ : StJ8 Q) (χ χ' : Coins frameJ8 K) :
    rowsMJ8 nodes orbit (Q χ) = rowsMJ8 nodes orbit (Q χ') :=
  rowsB0_congr (by norm_num) nodes orbit fun j hj =>
    staged_eq hQ.2.1 (r := 0) (fun i hi => absurd hi (by omega)) _ (by simp only [crM]; rw [if_pos (by omega)])

theorem rowsAJ8_const {h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (Q : Coins frameJ8 K → TrJ8 F) (hQ : StJ8 Q) (χ χ' : Coins frameJ8 K) :
    rowsAJ8 nodes orbit (Q χ) = rowsAJ8 nodes orbit (Q χ') :=
  rowsB0_congr (by norm_num) nodes orbit fun j hj =>
    staged_eq hQ.2.2.2.2.1 (r := 0) (fun i hi => absurd hi (by omega)) _ (by simp only [crA]; rw [if_pos (by omega)])

theorem rowsMJ8_const40 {h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (Q : Coins frameVSQ K → TrJ8 F) (hQ : St40 (StJ8 (F := F)) Q) (ψ ψ' : Coins frameVSQ K) :
    rowsMJ8 nodes orbit (Q ψ) = rowsMJ8 nodes orbit (Q ψ') := by
  obtain ⟨Q', hQ', y₁, y₂, rfl⟩ := hQ
  exact rowsMJ8_const nodes orbit Q' hQ' _ _

open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (censusPairs censusList2 censusPairs_length_le)

/-- **The census readout** (P11e's `censusPairs (censusList2 t ext)`) at the cell table's rows and an atom-export
map `ext` read off the trace. -/
def prsJ8 {h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (ext : TrJ8 F → ℕ → Option Noun)
    (tr : TrJ8 F) : List (List ℕ × List ℕ) :=
  censusPairs (censusList2 (rowsMJ8 nodes orbit tr) (ext tr))

theorem prsJ8_le {h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (ext : TrJ8 F → ℕ → Option Noun)
    (hn : n ≤ 2 ^ 31) (tr : TrJ8 F) : (prsJ8 nodes orbit ext tr).length ≤ 2 ^ 66 :=
  censusPairs_length_le _ _ (by rw [rowsMJ8, rowsB0_length]; exact hn)

theorem prsJ8_const {h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (ext : TrJ8 F → ℕ → Option Noun)
    (hext : ∀ Q : Coins frameJ8 K → TrJ8 F, StJ8 Q → ∀ χ χ', ext (Q χ) = ext (Q χ'))
    (Q : Coins frameJ8 K → TrJ8 F) (hQ : StJ8 Q) (χ χ' : Coins frameJ8 K) :
    prsJ8 nodes orbit ext (Q χ) = prsJ8 nodes orbit ext (Q χ') := by
  simp only [prsJ8, rowsMJ8_const nodes orbit Q hQ χ χ', hext Q hQ χ χ']

end Tables

/-! ## 7. The readouts swapped into `Data40J8` / `DataJ8C` -/

section Realize
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δF : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δF))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {r : RowsJ8}

/-- The public layout of the J-8 chips that the readouts need (rows, nodes, orbits, walk roots). -/
structure LayJ8 where
  hC : ℕ
  nC : ℕ
  hnC : 0 < nC
  nodesC : Fin nC → ZMod p
  orbitC : StrictOrbitDomain (ZMod p) 3 hC
  hM : ℕ
  nM : ℕ
  nodesM : Fin nM → ZMod p
  orbitM : StrictOrbitDomain (ZMod p) 3 hM
  hW : ℕ
  nW : ℕ
  hnW : 0 < nW
  nodesW : Fin nW → ZMod p
  orbitW : StrictOrbitDomain (ZMod p) 3 hW
  krootsW : ℕ
  hA : ℕ
  nA : ℕ
  nodesA : Fin nA → ZMod p
  orbitA : StrictOrbitDomain (ZMod p) 3 hA
  hV : ℕ
  nV : ℕ
  hnV : 0 < nV
  nodesV : Fin nV → ZMod p
  orbitV : StrictOrbitDomain (ZMod p) 3 hV
  krootsV : ℕ
  /-- the census skeleton (the claim's nouns, `≤ 3`) -/
  skel : List Noun
  skel_le : skel.length ≤ 3

/-- The layout's row counts within the budgets. -/
structure LayLe (Lay : LayJ8 (p := p)) (r : RowsJ8) : Prop where
  C : Lay.nC ≤ r.N
  M : Lay.nM ≤ r.D
  W : Lay.nW ≤ r.W
  A : Lay.nA ≤ r.A
  V : Lay.nV ≤ r.AW

/-- **#1 at the real traces**: `L` with the compute rows, the cell rows and skeleton and the walk chain's data read
off the J-8 traces (the IO lists stay `L`'s). -/
def realize40 (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δF) (TrJ8 (ZMod p)) StJ8 r)
    (Lay : LayJ8 (p := p)) (hL : LayLe Lay r) :
    Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δF) (TrJ8 (ZMod p)) StJ8 r :=
  { L with
    cRows := cRowsJ8 Lay.hnC Lay.nodesC Lay.orbitC
    cH := fun _ => Lay.nC
    cH_le := fun _ => hL.C
    c_const := fun Q hQ ψ ψ' => ⟨cRowsJ8_const Lay.hnC Lay.nodesC Lay.orbitC Q hQ ψ ψ', rfl⟩
    rowsD := rowsMJ8 Lay.nodesM Lay.orbitM
    skelD := fun _ => Lay.skel
    rowsD_le := fun tr => by rw [rowsMJ8, rowsB0_length]; exact hL.M
    skelD_le := fun _ => Lay.skel_le
    rowsD_const := fun Q hQ ψ ψ' => ⟨rowsMJ8_const40 Lay.nodesM Lay.orbitM Q hQ ψ ψ', rfl⟩
    wdW := fun tr _ => wdWJ8 δF b Lay.krootsW Lay.hnW Lay.nodesW Lay.orbitW tr
    wdW_le := fun _ _ => hL.W
    wdW_reads := fun Q hQ => wdWJ8_reads δF b Lay.krootsW Lay.hnW Lay.nodesW Lay.orbitW Q hQ }

variable [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δF))] {P g : ℕ}

def realizeJ8 (R : DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δF) (TrJ8 (ZMod p)) StJ8 r P)
    (Lay : LayJ8 (p := p)) (hL : LayLe Lay r) (ext : TrJ8 (ZMod p) → ℕ → Option Noun)
    (hext : ∀ Q : Coins frameJ8 K → TrJ8 (ZMod p), StJ8 Q → ∀ χ χ', ext (Q χ) = ext (Q χ'))
    (hP : (P = 2 ^ 66)) (hnM : Lay.nM ≤ 2 ^ 31) :
    DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δF) (TrJ8 (ZMod p)) StJ8 r P g where
  D := { R with
    rowsA := rowsAJ8 Lay.nodesA Lay.orbitA
    skelA := fun _ => Lay.skel
    rowsA_le := fun tr => by rw [rowsAJ8, rowsB0_length]; exact hL.A
    skelA_le := fun _ => Lay.skel_le
    rowsA_const := fun Q hQ χ χ' => ⟨rowsAJ8_const Lay.nodesA Lay.orbitA Q hQ χ χ', rfl⟩
    prs := prsJ8 Lay.nodesM Lay.orbitM ext
    prs_le := fun tr => hP ▸ prsJ8_le Lay.nodesM Lay.orbitM ext hnM tr
    prs_const := prsJ8_const Lay.nodesM Lay.orbitM ext hext }
  wdC tr _ := wdVJ8 δF b Lay.krootsV Lay.hnV Lay.nodesV Lay.orbitV tr
  wdC_le _ _ := hL.V
  wdC_reads Q hQ := wdVJ8_reads δF b Lay.krootsV Lay.hnV Lay.nodesV Lay.orbitV Q hQ

end Realize

end

end Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8
