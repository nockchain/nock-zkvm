import Nock.NockVMROM.Thm54.VclL.Compute.InlineForge

/-!
.

* **Slots** (`slotAcc`): three lookup slots per row.  Slot `0` is the export lookup of the
  formula cell `(f, f_h, f_t, fIdx)` on EVERY row; slot `1` is the `f_t` export
  (`s2 s5 s6 s7 s8 s9`) or the path (`s0`); slot `2` is the `f_tt` export (`s6`) or the core path
  (`s9`) — `s6` and `s9` share slot `2`.  Per state the active slots are exactly the memory
  records (`activeSlots_eq_recordCount`), so `inlineRecordsD := 0`; `kc = 3` (`kc_eq_three`);
  per row at most three export and one path consumer (`exportSlots_le_three`,
  `pathSlots_le_one`), so the export consumer bound is `3N` and the path bound `N`
  (`export_consumer_majorant`, `path_consumer_majorant`).
* **Columns** (`computeChipVCLD`, width `226`): the B0 column `fIdx = 222` (the formula cell's
  serial, round `0`) and slot `0`'s lookup inverse `223..225` (round `1`, a `𝕂` triple: the chip is
  pre-tower).  Slots `1` / `2` use the existing `vIdx₀ / vIdx₁` (`202`, `203`) and inverses
  `214..216` / `217..219`.
* **Gates**: slot `0`: `inv₀ · den₀ − 1 = 0` (degree `2`); slots `1`, `2`: the state-multiplexed
  `inv · den − act = 0` with `den = Σ sel_s · den_kind(s)` and `act = Σ sel_s` over the slot's
  active states (degree `3`): one inverse feeds the export denominator on export rows and the
  path denominator on path rows; the multiplexing reads the one-hot STATE selectors only (no
  positional selector).  `den = pole + Σ_c γ^c · r_c` is `FiniteFieldIO.compress` of the record at
  the IO coins `(γ, pole)` (challenge limbs `γc`, `ρc`, pre-tower `𝕂`).
* **The key clause** (`formula_key_clause`, DESIGN marks it unconfirmed): the slot-0 record's key
  is the `B0Cols`-typed `recKeyFormula` reading column `222`, same shape as `export_key_clause`.
* **The head binding** (`lookup_binds_head_row`): on a decoded row satisfying `V_comp` whose slot-0 record is served as a formula cell
  `[l r]` (`f_h = enc z l`, `f_t = enc z r`), `l = atom op` and the row's `f_t` is the served
  noun's axis-3 child — the inline record is discharged by the lookup.
* (1) Columns `+4`, not
  `≈ +7`: `fIdx` plus ONE `𝕂` inverse triple, because the chip is pre-tower; DESIGN's `+7` counts a
  `𝕂′` inverse (6 limbs), which the tower retype (TI) will make.  (2) Gates `+9`, not `+3`: slot 0's
  triple plus the multiplexed triples of slots 1 / 2, whose inverse columns `214..219` were
  committed but unpinned at `computeChipVCLA`.  Chip `(3, 222, 312, 4, 2) → (3, 226, 321, 4, 2)`.

Paper: `:1728` (`mem_record_1`), `:1850-1852`, `:1893-1898` (state variables), `:1846-1868`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Framework Nock.Reified Module
open Nock.ComputeTable (FP State Vcomp SVhead headAtom)
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.RecordCarrier
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering hiding finalExtCoordIndex
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.MonolithicRAP
open scoped Polynomial

set_option maxRecDepth 300000

noncomputable section

/-! ## 1. The slot assignment (DESIGN §1) -/

/-- The two lookup accumulators of the compute chip. -/
inductive AccVCL
  | export
  | path
  deriving DecidableEq, Repr

/-- **The three multiplexed slots.**  Slot `0` = the formula cell (every row); slot `1` = `f_t`
export / path (`s0`); slot `2` = `f_tt` export (`s6`) / core path (`s9`). -/
def slotAcc : State → Fin 3 → Option AccVCL
  | _, ⟨0, _⟩ => some .export
  | .s0, ⟨1, _⟩ => some .path
  | .s2, ⟨1, _⟩ => some .export
  | .s5, ⟨1, _⟩ => some .export
  | .s6, ⟨1, _⟩ => some .export
  | .s7, ⟨1, _⟩ => some .export
  | .s8, ⟨1, _⟩ => some .export
  | .s9, ⟨1, _⟩ => some .export
  | .s6, ⟨2, _⟩ => some .export
  | .s9, ⟨2, _⟩ => some .path
  | _, _ => none

/-- Active slots of a state. -/
def activeSlots (s : State) : ℕ := ((List.finRange 3).filter fun j => (slotAcc s j).isSome).length

/-- Export / path slots of a state. -/
def exportSlots (s : State) : ℕ :=
  ((List.finRange 3).filter fun j => slotAcc s j = some .export).length
def pathSlots (s : State) : ℕ :=
  ((List.finRange 3).filter fun j => slotAcc s j = some .path).length

/-- **The repaired inline count: zero** (record 0 is a lookup on every row). -/
def inlineRecordsD : State → ℕ := fun _ => 0

/-- **Every memory record is a lookup**: the active slots of a state are its records. -/
theorem activeSlots_eq_recordCount (s : State) :
    activeSlots s = recordCount s ∧ activeSlots s + inlineRecordsD s = recordCount s := by
  cases s <;> decide

/-- `kc = 3`: at most three lookups per row, attained at `s6` and `s9`. -/
theorem kc_eq_three : (∀ s, activeSlots s ≤ 3) ∧ activeSlots .s6 = 3 ∧ activeSlots .s9 = 3 := by
  refine ⟨fun s => ?_, by decide, by decide⟩
  cases s <;> decide

theorem exportSlots_le_three (s : State) : exportSlots s ≤ 3 := by cases s <;> decide
theorem pathSlots_le_one (s : State) : pathSlots s ≤ 1 := by cases s <;> decide

/-- Slot `0` is the formula-cell export at every state (incl. the autocons root). -/
theorem slot0_export (s : State) : slotAcc s 0 = some .export := by cases s <;> rfl

/-- `s6` / `s9` share slot `2` (export at `s6`, path at `s9`); no other state uses it. -/
theorem slot2_shared :
    slotAcc .s6 2 = some .export ∧ slotAcc .s9 2 = some .path ∧
      ∀ s, s ≠ .s6 → s ≠ .s9 → slotAcc s 2 = none := by
  refine ⟨rfl, rfl, fun s h6 h9 => ?_⟩
  cases s <;> first | rfl | exact absurd rfl h6 | exact absurd rfl h9

/-- **The export consumer majorant `3N`.** -/
theorem export_consumer_majorant (rows : List State) :
    (rows.map exportSlots).sum ≤ 3 * rows.length := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := exportSlots_le_three r
    omega

/-- **The path consumer majorant `N`.** -/
theorem path_consumer_majorant (rows : List State) :
    (rows.map pathSlots).sum ≤ rows.length := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := pathSlots_le_one r
    omega

/-! ## 2. Columns and rounds -/

/-- The formula cell's serial: B0 column `222`. -/
def fIdxCol : ℕ := 222
/-- Slot `0`'s lookup inverse: base limbs `223..225` (a `𝕂` triple, round `1`). -/
def inv0Base : ℕ := 223

def vclWidthD : ℕ := 226

/-- The coin-round schedule of `computeChipVCLD`: `colRoundVCL` below `222`, `fIdx` round `0`,
slot `0`'s inverse round `1`. -/
def colRoundVCLD (c : ℕ) : ℕ := if c < 222 then colRoundVCL c else if c = fIdxCol then 0 else 1

theorem colRoundVCLD_fIdx : colRoundVCLD fIdxCol = 0 := by decide
theorem colRoundVCLD_inv0 (k : Fin 3) : colRoundVCLD (inv0Base + k) = 1 := by
  fin_cases k <;> decide

/-- The compute table of the repaired chip. -/
def tableVCLD (h : ℕ) : TableSpec where
  width := vclWidthD
  colRound := fun j => colRoundVCLD j
  height := h

/-- The round-0 columns of `computeChipVCLD`. -/
def IsB0VCLD (c : ℕ) : Prop := IsB0VCL c ∨ c = axCol ∨ c = fIdxCol

instance (c : ℕ) : Decidable (IsB0VCLD c) := by unfold IsB0VCLD axCol fIdxCol; infer_instance

/-- **The compute B0 of the repaired chip, measured**: `IsB0VCL`, the axis `221` and `fIdx = 222`. -/
theorem colRoundVCLD_zero_iff : ∀ c : Fin 226, colRoundVCLD c = 0 ↔ IsB0VCLD c := by
  unfold IsB0VCLD IsB0VCL axCol fIdxCol; decide +kernel

/-! ## 3. Records, denominators and the slot gates -/

/-- A record entry: a `𝕂`-column (three consecutive limbs) or an `𝔽`-column embedded in `𝕂`. -/
inductive Entry
  | k (limb : ℕ)
  | f (col : ℕ)

section entries
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The coordinate vector of an entry. -/
def Entry.vec (b : Basis (Fin 3) F K) : Entry → Fin 3 → CoeffExpr F
  | .k l => fun j => .var .traceCur (l + (j : ℕ))
  | .f c => fun j => .mul (.var .traceCur c) (oneVec b j)

/-- The `𝕂` value of an entry at an `𝔽`-environment. -/
def Entry.val (b : Basis (Fin 3) F K) (envF : Env F) : Entry → K
  | .k l => ∑ j : Fin 3, envF.trace (l + (j : ℕ)) • b j
  | .f c => algebraMap F K (envF.trace c)

theorem Entry.vec_degree (b : Basis (Fin 3) F K) (e : Entry) (j : Fin 3) : (e.vec b j).degree ≤ 1 := by
  cases e <;> simp [Entry.vec, oneVec, CoeffExpr.degree]

/-- A `𝕂`-value given by its limbs has those limbs as coordinates. -/
theorem coord_sum_smul (b : Basis (Fin 3) F K) (c : Fin 3 → F) (j : Fin 3) :
    coord b (∑ i : Fin 3, c i • b i) j = c j := by
  show b.repr _ j = c j
  rw [b.repr_sum_self]

theorem Entry.coord_val [FiniteDimensional F K] (b : Basis (Fin 3) F K) (envF : Env F) (e : Entry)
    (j : Fin 3) : coord b (e.val b envF) j = (e.vec b j).eval envF := by
  cases e with
  | k l => simp only [Entry.val, Entry.vec, CoeffExpr.eval]; exact coord_sum_smul b _ j
  | f c =>
      simp only [Entry.val, Entry.vec, CoeffExpr.eval, oneVec]
      rw [Algebra.algebraMap_eq_smul_one]
      simp [coord, map_smul]

/-- A `𝕂` coin given by three challenge limbs. -/
def chalVec (base : ℕ) : Fin 3 → CoeffExpr F := fun j => .var .challenge (base + (j : ℕ))

def chalVal (b : Basis (Fin 3) F K) (envF : Env F) (base : ℕ) : K :=
  ∑ j : Fin 3, envF.chal (base + (j : ℕ)) • b j

theorem coord_chalVal (b : Basis (Fin 3) F K) (envF : Env F) (base : ℕ) (j : Fin 3) :
    coord b (chalVal b envF base) j = (chalVec base j).eval envF := by
  simp only [chalVal, chalVec, CoeffExpr.eval]; exact coord_sum_smul b _ j

/-- **The compressed denominator** `pole + Σ_c γ^c · r_c` of a width-`m` record, as a coordinate
vector (`FiniteFieldIO.compress` at `IOCoins ⟨γ, pole⟩`). -/
def denVec (b : Basis (Fin 3) F K) (γc ρc : ℕ) {m : ℕ} (r : Fin m → Entry) : Fin 3 → CoeffExpr F :=
  fun k => .add (chalVec ρc k)
    (CoeffExpr.sumList (Finset.univ : Finset (Fin m)).toList fun c =>
      mulVec b (powVec b (chalVec γc) (c : ℕ)) ((r c).vec b) k)

theorem denVec_degree (b : Basis (Fin 3) F K) (γc ρc : ℕ) {m : ℕ} (r : Fin m → Entry) (k : Fin 3) :
    (denVec b γc ρc r k).degree ≤ 1 := by
  simp only [denVec, CoeffExpr.degree]
  refine max_le (by simp [chalVec, CoeffExpr.degree]) ?_
  refine CoeffExpr.degree_sumList_le _ _ _ fun c _ => ?_
  have h := degree_mulVec_le b (powVec b (chalVec γc) (c : ℕ)) ((r c).vec b) 0 1
    (fun i => by
      have := degree_powVec_le b (chalVec (F := F) γc) 0
        (fun i => by simp [chalVec, CoeffExpr.degree]) (c : ℕ) i
      simpa using this)
    (fun i => Entry.vec_degree b (r c) i) k
  simpa using h

/-- The record's `𝕂` values. -/
def recVal (b : Basis (Fin 3) F K) (envF : Env F) {m : ℕ} (r : Fin m → Entry) : Fin m → K :=
  fun c => (r c).val b envF

/-- The IO coins read off the challenge limbs. -/
def coinsAt (b : Basis (Fin 3) F K) (envF : Env F) (γc ρc : ℕ) : FiniteIO.IOCoins K :=
  ⟨chalVal b envF γc, chalVal b envF ρc⟩

theorem coord_compress [FiniteDimensional F K] (b : Basis (Fin 3) F K) (envF : Env F) (γc ρc : ℕ)
    {m : ℕ} (r : Fin m → Entry) (k : Fin 3) :
    coord b (FiniteIO.compress (coinsAt b envF γc ρc) (recVal b envF r)) k =
      (denVec b γc ρc r k).eval envF := by
  simp only [FiniteIO.compress, coinsAt, Walk.rlc, denVec, CoeffExpr.eval, coord_add,
    coord_chalVal, CoeffExpr.eval_sumList, Finset.sum_map_toList, coord_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  exact eval_mulVec b envF _ _ _ _
    (fun i => eval_powVec b envF (chalVec γc) (chalVal b envF γc)
      (fun j => coord_chalVal b envF γc j) (c : ℕ) i)
    (fun i => Entry.coord_val b envF (r c) i) k

end entries

/-- The physical limb base of a `𝕂`-role (`13 + 3·role`; `ftLeafLimb` is role `41`). -/
def roleLimb (role : ℕ) : ℕ := 13 + 3 * role

/-- The three entries of a fingerprint at `𝕂`-roles `R, R+1, R+2` (size, dyck, leaf). -/
def fpEntry (R : ℕ) (j : Fin 3) : Entry := .k (roleLimb (R + (j : ℕ)))

/-- **The export record `(fp p, fp l, fp r, idx)`** (`m_x = 10` over `𝕂`). -/
def exportRec (p l r idx : ℕ) : Fin 10 → Entry :=
  ![fpEntry p 0, fpEntry p 1, fpEntry p 2, fpEntry l 0, fpEntry l 1, fpEntry l 2,
    fpEntry r 0, fpEntry r 1, fpEntry r 2, .f idx]

/-- **The path record `(fp root, fp child, ax, rootIdx)`** (`m_p = 8` over `𝕂`). -/
def pathRec (root child ax idx : ℕ) : Fin 8 → Entry :=
  ![fpEntry root 0, fpEntry root 1, fpEntry root 2, fpEntry child 0, fpEntry child 1,
    fpEntry child 2, .f ax, .f idx]

/-- The `𝕂`-roles of the compute row (source column `− 11`, `ComputeEnvAgreement.pubOfState` /
`decOf`): `s 0`, `f 3`, `e 6`, `sf1_e 15`, `sf2_f 21`, `f_h 36`, `f_t 39`, `f_th 42`, `f_tt 45`,
`f_tth 48`, `f_ttt 51`. -/
def roleS : ℕ := 0
def roleF : ℕ := 3
def roleE : ℕ := 6
def roleSf1E : ℕ := 15
def roleSf2F : ℕ := 21
def roleFh : ℕ := 36
def roleFt : ℕ := 39
def roleFth : ℕ := 42
def roleFtt : ℕ := 45
def roleFtth : ℕ := 48
def roleFttt : ℕ := 51

/-- **Slot 0's record: the formula cell `(f, f_h, f_t, fIdx)`.** -/
def formulaRec : Fin 10 → Entry := exportRec roleF roleFh roleFt fIdxCol
/-- Slot 1, export rows: the cell `f_t = [f_th f_tt]` at `vIdx₀`. -/
def tailRec : Fin 10 → Entry := exportRec roleFt roleFth roleFtt (vIdxCol 0)
/-- Slot 1, `s0`: the path `(s, e, ax, vIdx₀)`. -/
def op0PathRec : Fin 8 → Entry := pathRec roleS roleE axCol (vIdxCol 0)
/-- Slot 2, `s6`: the cell `f_tt = [f_tth f_ttt]` at `vIdx₁`. -/
def ttRec : Fin 10 → Entry := exportRec roleFtt roleFtth roleFttt (vIdxCol 1)
/-- Slot 2, `s9`: the core path `(sf1_e, sf2_f, ax, vIdx₁)`. -/
def op9PathRec : Fin 8 → Entry := pathRec roleSf1E roleSf2F axCol (vIdxCol 1)

section gates
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- A state selector column (`opCol`: `s0..s9 ↦ 0..9`, `cons ↦ 10`). -/
def selVar (i : ℕ) : CoeffExpr F := .var .traceCur i

/-- `Σ_i sel_i` over a list of selector columns. -/
def selSum (l : List ℕ) : CoeffExpr F := CoeffExpr.sumList l selVar

/-- Scale a coordinate vector by a base-field expression. -/
def scaleVec (a : CoeffExpr F) (u : Fin 3 → CoeffExpr F) : Fin 3 → CoeffExpr F :=
  fun k => .mul a (u k)

def addVec (u v : Fin 3 → CoeffExpr F) : Fin 3 → CoeffExpr F := fun k => .add (u k) (v k)

/-- Coordinate `k` of the multiplexed inverse gate `inv · den − act` (`act ∈ 𝔽`). -/
def muxInvCoord (b : Basis (Fin 3) F K) (invBase : ℕ) (act : CoeffExpr F)
    (den : Fin 3 → CoeffExpr F) (k : Fin 3) : CoeffExpr F :=
  .sub (mulVec b (fun j => .var .traceCur (invBase + (j : ℕ))) den k) (.mul act (oneVec b k))

def muxInvGates (b : Basis (Fin 3) F K) (invBase : ℕ) (act : CoeffExpr F)
    (den : Fin 3 → CoeffExpr F) : List (CoeffExpr F) := List.ofFn (muxInvCoord b invBase act den)

/-- **Slot 0's gates**: `inv₀ · den₀ − 1 = 0` at the formula-cell record, every row. -/
def slot0Gates (b : Basis (Fin 3) F K) (γc ρc : ℕ) : List (CoeffExpr F) :=
  lookupInvGates b inv0Base (denVec b γc ρc formulaRec)

/-- The export states of slot 1 (`s2 s5 s6 s7 s8 s9`, selector columns). -/
def slot1ExportSels : List ℕ := [2, 5, 6, 7, 8, 9]

/-- **Slot 1's gates**: `inv₁ · (s0·den_path + Σ s_x·den_export) − (s0 + Σ s_x) = 0`. -/
def slot1Gates (b : Basis (Fin 3) F K) (γc ρc : ℕ) : List (CoeffExpr F) :=
  muxInvGates b (lookupInvBase 0) (selSum (0 :: slot1ExportSels))
    (addVec (scaleVec (selVar 0) (denVec b γc ρc op0PathRec))
      (scaleVec (selSum slot1ExportSels) (denVec b γc ρc tailRec)))

/-- **Slot 2's gates** (`s6` export / `s9` core path share it). -/
def slot2Gates (b : Basis (Fin 3) F K) (γc ρc : ℕ) : List (CoeffExpr F) :=
  muxInvGates b (lookupInvBase 1) (selSum [6, 9])
    (addVec (scaleVec (selVar 6) (denVec b γc ρc ttRec))
      (scaleVec (selVar 9) (denVec b γc ρc op9PathRec)))

/-- All lookup gates of the repaired chip. -/
def lookupGatesD (b : Basis (Fin 3) F K) (γc ρc : ℕ) : List (CoeffExpr F) :=
  slot0Gates b γc ρc ++ slot1Gates b γc ρc ++ slot2Gates b γc ρc

theorem selSum_degree (l : List ℕ) : (selSum (F := F) l).degree ≤ 1 :=
  CoeffExpr.degree_sumList_le _ _ _ fun _ _ => by simp [selVar, CoeffExpr.degree]

theorem muxInvGates_degree (b : Basis (Fin 3) F K) (invBase : ℕ) (act : CoeffExpr F)
    (den : Fin 3 → CoeffExpr F) (dd : ℕ) (hact : act.degree ≤ 1 + dd)
    (hden : ∀ k, (den k).degree ≤ dd) :
    ∀ g ∈ muxInvGates b invBase act den, g.degree ≤ 1 + dd := by
  intro g hg
  simp only [muxInvGates, List.mem_ofFn] at hg
  obtain ⟨k, rfl⟩ := hg
  simp only [muxInvCoord, oneVec, CoeffExpr.degree, add_zero]
  exact max_le (degree_mulVec_le b _ den 1 dd (fun j => by simp [CoeffExpr.degree]) hden k) hact

theorem slot0Gates_degree (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    ∀ g ∈ slot0Gates b γc ρc, g.degree ≤ 2 :=
  lookupInvGates_degree b inv0Base _ 1 (denVec_degree b γc ρc formulaRec)

theorem muxDen_degree (a₁ a₂ : CoeffExpr F) (u v : Fin 3 → CoeffExpr F)
    (h₁ : a₁.degree ≤ 1) (h₂ : a₂.degree ≤ 1) (hu : ∀ k, (u k).degree ≤ 1)
    (hv : ∀ k, (v k).degree ≤ 1) (k : Fin 3) :
    (addVec (scaleVec a₁ u) (scaleVec a₂ v) k).degree ≤ 2 := by
  simp only [addVec, scaleVec, CoeffExpr.degree]
  exact max_le (by have := hu k; omega) (by have := hv k; omega)

theorem slot1Gates_degree (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    ∀ g ∈ slot1Gates b γc ρc, g.degree ≤ 3 :=
  muxInvGates_degree b _ _ _ 2 ((selSum_degree _).trans (by omega))
    (muxDen_degree _ _ _ _ (by simp [selVar, CoeffExpr.degree]) (selSum_degree _)
      (denVec_degree b γc ρc _) (denVec_degree b γc ρc _))

theorem slot2Gates_degree (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    ∀ g ∈ slot2Gates b γc ρc, g.degree ≤ 3 :=
  muxInvGates_degree b _ _ _ 2 ((selSum_degree _).trans (by omega))
    (muxDen_degree _ _ _ _ (by simp [selVar, CoeffExpr.degree]) (by simp [selVar, CoeffExpr.degree])
      (denVec_degree b γc ρc _) (denVec_degree b γc ρc _))

@[simp] theorem muxInvGates_length (b : Basis (Fin 3) F K) (invBase : ℕ) (act : CoeffExpr F)
    (den : Fin 3 → CoeffExpr F) : (muxInvGates b invBase act den).length = 3 := by
  simp [muxInvGates]

theorem lookupGatesD_length (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    (lookupGatesD b γc ρc).length = 9 := by
  simp [lookupGatesD, slot0Gates, slot1Gates, slot2Gates]

theorem lookupGatesD_degree (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    ∀ g ∈ lookupGatesD b γc ρc, g.degree ≤ 3 := by
  intro g hg
  simp only [lookupGatesD, List.mem_append] at hg
  rcases hg with (h | h) | h
  · exact (slot0Gates_degree b γc ρc g h).trans (by omega)
  · exact slot1Gates_degree b γc ρc g h
  · exact slot2Gates_degree b γc ρc g h

end gates

/-! ## 4. Gate soundness: the inverses are the reciprocals of the compressed records -/

section sound
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- The `𝕂` value of an inverse triple. -/
def invVal (b : Basis (Fin 3) F K) (envF : Env F) (base : ℕ) : K := Entry.val b envF (.k base)

theorem coord_invVal (b : Basis (Fin 3) F K) (envF : Env F) (base : ℕ) (j : Fin 3) :
    coord b (invVal b envF base) j = envF.trace (base + (j : ℕ)) := by
  unfold invVal Entry.val; exact coord_sum_smul b _ j

/-- **Slot 0**: on every row where the three gates vanish, `inv₀` is the reciprocal of the
compressed formula-cell record. -/
theorem slot0_sound (b : Basis (Fin 3) F K) (γc ρc : ℕ) (envF : Env F)
    (h : ∀ g ∈ slot0Gates b γc ρc, g.eval envF = 0) :
    invVal b envF inv0Base *
      FiniteIO.compress (coinsAt b envF γc ρc) (recVal b envF formulaRec) = 1 :=
  lookupInvGates_sound b inv0Base _ envF _ _ (fun j => coord_invVal b envF inv0Base j)
    (fun j => coord_compress b envF γc ρc formulaRec j) h

/-- The multiplexed triple: `inv · den = act` as `𝕂` values. -/
theorem muxInvGates_sound (b : Basis (Fin 3) F K) (invBase : ℕ) (act : CoeffExpr F)
    (den : Fin 3 → CoeffExpr F) (envF : Env F) (y : K)
    (hy : ∀ j, coord b y j = (den j).eval envF)
    (h : ∀ g ∈ muxInvGates b invBase act den, g.eval envF = 0) :
    invVal b envF invBase * y = algebraMap F K (act.eval envF) := by
  apply b.repr.injective
  ext k
  have hk := h (muxInvCoord b invBase act den k) ((List.mem_ofFn ..).2 ⟨k, rfl⟩)
  simp only [muxInvCoord, CoeffExpr.eval, sub_eq_zero, oneVec] at hk
  have hm := eval_mulVec b envF (fun j => .var .traceCur (invBase + (j : ℕ))) den
    (invVal b envF invBase) y (fun j => by simpa [CoeffExpr.eval] using coord_invVal b envF invBase j)
    hy k
  have h2 : coord b (invVal b envF invBase * y) k = coord b (algebraMap F K (act.eval envF)) k := by
    rw [hm, hk, Algebra.algebraMap_eq_smul_one]; simp [coord, map_smul]
  simpa [coord] using h2

theorem selSum_eval (l : List ℕ) (envF : Env F) :
    (selSum (F := F) l).eval envF = (l.map envF.trace).sum := by
  simp only [selSum, CoeffExpr.eval_sumList, selVar, CoeffExpr.eval]

/-- The value of a multiplexed denominator when the first selector is on and the second off. -/
theorem coord_mux_left (b : Basis (Fin 3) F K) (envF : Env F) (a₁ a₂ : CoeffExpr F)
    (u v : Fin 3 → CoeffExpr F) (y : K) (hy : ∀ j, coord b y j = (u j).eval envF)
    (h₁ : a₁.eval envF = 1) (h₂ : a₂.eval envF = 0) (j : Fin 3) :
    coord b y j = (addVec (scaleVec a₁ u) (scaleVec a₂ v) j).eval envF := by
  simp [addVec, scaleVec, CoeffExpr.eval, h₁, h₂, hy j]

theorem coord_mux_right (b : Basis (Fin 3) F K) (envF : Env F) (a₁ a₂ : CoeffExpr F)
    (u v : Fin 3 → CoeffExpr F) (y : K) (hy : ∀ j, coord b y j = (v j).eval envF)
    (h₁ : a₁.eval envF = 0) (h₂ : a₂.eval envF = 1) (j : Fin 3) :
    coord b y j = (addVec (scaleVec a₁ u) (scaleVec a₂ v) j).eval envF := by
  simp [addVec, scaleVec, CoeffExpr.eval, h₁, h₂, hy j]

/-- One-hot selector values at a row (`opCol`: `s_k ↦ k`, `cons ↦ 10`). -/
def SelAt (envF : Env F) (s : State) : Prop :=
  ∀ i < 11, envF.trace i = if i = (match s with
    | .s0 => 0 | .s1 => 1 | .s2 => 2 | .s3 => 3 | .s4 => 4 | .s5 => 5 | .s6 => 6 | .s7 => 7
    | .s8 => 8 | .s9 => 9 | .cons => 10) then 1 else 0

/-- **Slot 1 at an `s0` row**: `inv₁` is the reciprocal of the compressed path record. -/
theorem slot1_sound_s0 (b : Basis (Fin 3) F K) (γc ρc : ℕ) (envF : Env F) (hs : SelAt envF .s0)
    (h : ∀ g ∈ slot1Gates b γc ρc, g.eval envF = 0) :
    invVal b envF (lookupInvBase 0) *
      FiniteIO.compress (coinsAt b envF γc ρc) (recVal b envF op0PathRec) = 1 := by
  have hv : ∀ i < 11, envF.trace i = if i = 0 then 1 else 0 := hs
  have hm := muxInvGates_sound b _ _ _ envF _
    (coord_mux_left b envF _ _ _ _ _ (coord_compress b envF γc ρc op0PathRec)
      (by simp [selVar, CoeffExpr.eval, hv 0 (by omega)])
      (by simp [selSum_eval, slot1ExportSels, hv 2 (by omega), hv 5 (by omega), hv 6 (by omega),
            hv 7 (by omega), hv 8 (by omega), hv 9 (by omega)])) h
  rw [hm, selSum_eval]
  simp [slot1ExportSels, hv 0 (by omega), hv 2 (by omega), hv 5 (by omega), hv 6 (by omega),
    hv 7 (by omega), hv 8 (by omega), hv 9 (by omega)]

/-- **Slot 1 at an export row** (`s ∈ {s2, s5, s6, s7, s8, s9}`): `inv₁` is the reciprocal of
the compressed `f_t` cell record. -/
theorem slot1_sound_export (b : Basis (Fin 3) F K) (γc ρc : ℕ) (envF : Env F) (s : State)
    (hs : SelAt envF s) (hx : s = .s2 ∨ s = .s5 ∨ s = .s6 ∨ s = .s7 ∨ s = .s8 ∨ s = .s9)
    (h : ∀ g ∈ slot1Gates b γc ρc, g.eval envF = 0) :
    invVal b envF (lookupInvBase 0) *
      FiniteIO.compress (coinsAt b envF γc ρc) (recVal b envF tailRec) = 1 := by
  have hsum : (selSum (F := F) slot1ExportSels).eval envF = 1 ∧ (selVar (F := F) 0).eval envF = 0 := by
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · have hv := hs
      simp only [SelAt] at hv
      simp [selSum_eval, slot1ExportSels, selVar, CoeffExpr.eval, hv 0 (by omega), hv 2 (by omega),
        hv 5 (by omega), hv 6 (by omega), hv 7 (by omega), hv 8 (by omega), hv 9 (by omega)]
  have hm := muxInvGates_sound b _ _ _ envF _
    (coord_mux_right b envF _ _ _ _ _ (coord_compress b envF γc ρc tailRec) hsum.2 hsum.1) h
  rw [hm]
  have hact : (selSum (F := F) (0 :: slot1ExportSels)).eval envF = 1 := by
    have h1 := hsum.1; have h0 := hsum.2
    simp only [selSum_eval, selVar, CoeffExpr.eval] at h1 h0 ⊢
    simp only [List.map_cons, List.sum_cons]
    rw [h0, zero_add]; exact h1
  rw [hact, map_one]

/-- **Slot 2 at `s6`**: the `f_tt` cell record. -/
theorem slot2_sound_s6 (b : Basis (Fin 3) F K) (γc ρc : ℕ) (envF : Env F) (hs : SelAt envF .s6)
    (h : ∀ g ∈ slot2Gates b γc ρc, g.eval envF = 0) :
    invVal b envF (lookupInvBase 1) *
      FiniteIO.compress (coinsAt b envF γc ρc) (recVal b envF ttRec) = 1 := by
  have hv : ∀ i < 11, envF.trace i = if i = 6 then 1 else 0 := hs
  have hm := muxInvGates_sound b _ _ _ envF _
    (coord_mux_left b envF _ _ _ _ _ (coord_compress b envF γc ρc ttRec)
      (by simp [selVar, CoeffExpr.eval, hv 6 (by omega)])
      (by simp [selVar, CoeffExpr.eval, hv 9 (by omega)])) h
  rw [hm, selSum_eval]
  simp [hv 6 (by omega), hv 9 (by omega)]

/-- **Slot 2 at `s9`**: the core path record. -/
theorem slot2_sound_s9 (b : Basis (Fin 3) F K) (γc ρc : ℕ) (envF : Env F) (hs : SelAt envF .s9)
    (h : ∀ g ∈ slot2Gates b γc ρc, g.eval envF = 0) :
    invVal b envF (lookupInvBase 1) *
      FiniteIO.compress (coinsAt b envF γc ρc) (recVal b envF op9PathRec) = 1 := by
  have hv : ∀ i < 11, envF.trace i = if i = 9 then 1 else 0 := hs
  have hm := muxInvGates_sound b _ _ _ envF _
    (coord_mux_right b envF _ _ _ _ _ (coord_compress b envF γc ρc op9PathRec)
      (by simp [selVar, CoeffExpr.eval, hv 6 (by omega)])
      (by simp [selVar, CoeffExpr.eval, hv 9 (by omega)])) h
  rw [hm, selSum_eval]
  simp [hv 6 (by omega), hv 9 (by omega)]

/-- **Inactive slots are free**: at a row with no active state of slot 2 the gates read
`inv · 0 − 0`, i.e. hold for every inverse (no positional selector is involved). -/
theorem slot2_inactive (b : Basis (Fin 3) F K) (γc ρc : ℕ) (envF : Env F)
    (h6 : envF.trace 6 = 0) (h9 : envF.trace 9 = 0) :
    ∀ g ∈ slot2Gates b γc ρc, g.eval envF = 0 := by
  intro g hg
  simp only [slot2Gates, muxInvGates, List.mem_ofFn] at hg
  obtain ⟨k, rfl⟩ := hg
  simp only [muxInvCoord, CoeffExpr.eval, mulVec, CoeffExpr.eval_sumList, Finset.sum_map_toList,
    addVec, scaleVec, selVar, selSum_eval, h6, h9]
  simp [h6, h9]

end sound

/-! ## 5. The slot-0 record is the decoded formula cell, and its key is B0 -/

section decoded
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- The decoded fingerprint at `𝕂`-role `R` (three `𝕂` roles). -/
def fpAt (b : Basis (Fin 3) F K) (envF : Env F) (R : ℕ) : FP K :=
  ⟨(fpEntry R 0).val b envF, (fpEntry R 1).val b envF, (fpEntry R 2).val b envF⟩

/-- **The slot-0 record is `(f, f_h, f_t, fIdx)`** with `f_h` / `f_t` exactly the deployed
decoder's (`StrategyOfTracesLift.decodeDec`, source columns `47..52`). -/
theorem formulaRec_decoded (b : Basis (Fin 3) F K) (envF : Env F) :
    fpAt b envF roleFh = (StrategyOfTracesLift.decodeDec (gatherCorrectedFinalTypedEnv b envF)).f_h ∧
      fpAt b envF roleFt = (StrategyOfTracesLift.decodeDec (gatherCorrectedFinalTypedEnv b envF)).f_t :=
  ⟨rfl, rfl⟩

theorem formulaRec_val (b : Basis (Fin 3) F K) (envF : Env F) :
    recVal b envF formulaRec =
      ![(fpAt b envF roleF).size, (fpAt b envF roleF).dyck, (fpAt b envF roleF).leaf,
        (fpAt b envF roleFh).size, (fpAt b envF roleFh).dyck, (fpAt b envF roleFh).leaf,
        (fpAt b envF roleFt).size, (fpAt b envF roleFt).dyck, (fpAt b envF roleFt).leaf,
        algebraMap F K (envF.trace fIdxCol)] := by
  funext c; fin_cases c <;> rfl

/-- `fIdx` as a B0 column of the repaired table. -/
def fIdxB0 (h : ℕ) : {c : Fin (tableVCLD h).width // (tableVCLD h).colRound c = 0} :=
  ⟨⟨fIdxCol, by simp only [tableVCLD, vclWidthD, fIdxCol]; omega⟩, colRoundVCLD_fIdx⟩

/-- `RecordView.key` at the slot-0 record: the serial slot `9`, side `false`. -/
def keyOfFormulaRec (r : Fin 10 → K) : KeyVCL := (natLift (r 9), false)

/-- **`recKey` at slot 0**: the B0 column `fIdx`, by type. -/
def recKeyFormula {h : ℕ} (x : F) (bb : B0Cols F (tableVCLD h)) : KeyVCL :=
  (natLift (algebraMap F K ((bb (fIdxB0 h)).eval x)), false)

/-- **The formula key clause is B0** (DESIGN §5 marked it unconfirmed): the slot-0 record's key is
the `B0Cols`-typed `recKeyFormula` of the row, for every trace and node. -/
theorem formula_key_clause {h : ℕ} (b : Basis (Fin 3) F K) (Q : Fin (tableVCLD h).width → F[X])
    (ω x : F) (chal pub : ℕ → F) :
    keyOfFormulaRec (recVal b (Reify.envOfTrace Q ω x chal pub) formulaRec) =
      recKeyFormula (K := K) x (b0 (T := tableVCLD h) Q) := by
  simp only [keyOfFormulaRec, recKeyFormula, recVal, formulaRec, exportRec, b0, fIdxB0,
    Reify.envOfTrace]
  rfl

end decoded

/-! ## 6. -/

section head
variable {K : Type*} [Field K]

open Nock.GlobalCarryRecognizer (enc enc_size enc_atom enc_cons)

/-- A one-leaf noun is an atom. -/
theorem atom_of_leaves_eq_one : ∀ n : Noun, n.leaves = 1 → ∃ a, n = .atom a
  | .atom a, _ => ⟨a, rfl⟩
  | .cell l r, h => by
      have hl := l.one_le_leaves
      have hr := r.one_le_leaves
      simp [Noun.leaves] at h
      omega

/-- **Size `z` means atom, outside the low-order window.** -/
theorem enc_size_eq_seed_imp_atom {z : K} (hz : z ≠ 0) (W : ℕ)
    (hwin : ∀ k, 0 < k → k < W → z ^ k ≠ 1) (n : Noun) (hW : n.leaves ≤ W)
    (h : (enc z n).size = z) : ∃ a, n = .atom a := by
  apply atom_of_leaves_eq_one
  rw [enc_size] at h
  have h1 := n.one_le_leaves
  by_contra hne
  have hk : 0 < n.leaves - 1 := by omega
  apply hwin (n.leaves - 1) hk (by omega)
  have : z ^ n.leaves = z ^ (n.leaves - 1) * z := by
    rw [← pow_succ]; congr 1; omega
  rw [this] at h
  exact mul_right_cancel₀ hz (by simpa using h)

/-- Natural casts below the characteristic are injective. -/
theorem natCast_inj_lt {a c : ℕ} (ha : a < ringChar K) (hc : c < ringChar K)
    (h : (a : K) = (c : K)) : a = c := by
  have := (CharP.natCast_eq_natCast K (ringChar K)).1 h
  unfold Nat.ModEq at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] at this

/-- **The lookup binds the head** (field level): a served head `enc z l` equal to the gated
`atomFP z op` forces `l = atom op`. -/
theorem lookup_binds_head {z : K} (hz : z ≠ 0) (W : ℕ)
    (hwin : ∀ k, 0 < k → k < W → z ^ k ≠ 1) (op : ℕ) (hop : op < ringChar K) (l : Noun)
    (hW : l.leaves ≤ W) (hl : ∀ a, l = .atom a → a < ringChar K)
    (hserved_gate : enc z l = FP.atomFP z (op : K)) : l = .atom op := by
  obtain ⟨a, rfl⟩ := enc_size_eq_seed_imp_atom hz W hwin l hW (by rw [hserved_gate]; rfl)
  rw [enc_atom] at hserved_gate
  have hleaf := congrArg FP.leaf hserved_gate
  simp only [FP.atomFP_leaf] at hleaf
  rw [natCast_inj_lt (hl a rfl) hop hleaf]

/-- `V_comp`'s state gates at a non-`cons` row: `f_h = atomFP z op`. -/
theorem vcomp_f_h {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K}
    {dec : ComputeTable.Dec K} (hV : Vcomp inp pub dec) (hcons : pub.state ≠ State.cons) :
    dec.f_h = FP.atomFP inp.z (pub.state.toNat : K) := by
  have hsv : SVhead inp pub dec := hV.2.2.1
  have hA : headAtom dec inp.z (pub.state.toNat : K) := by simpa [SVhead, hcons] using hsv
  exact FP.ext hA.1 hA.2.1 hA.2.2

/-- **The slot-0 record served as a formula cell**: `f = enc z [l r]`, `f_h = enc z l`,
`f_t = enc z r` (what the export lookup and the cell table's soundness deliver for the record
`(f, f_h, f_t, fIdx)`). -/
def ServedFormulaCell (z : K) (pub : ComputeTable.Pub K) (dec : ComputeTable.Dec K) (l r : Noun) : Prop :=
  pub.f = enc z (.cell l r) ∧ dec.f_h = enc z l ∧ dec.f_t = enc z r

theorem lookup_binds_head_row {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K}
    {dec : ComputeTable.Dec K} (hV : Vcomp inp pub dec) (hcons : pub.state ≠ State.cons)
    (hz : inp.z ≠ 0) (W : ℕ) (hwin : ∀ k, 0 < k → k < W → inp.z ^ k ≠ 1)
    (hop : pub.state.toNat < ringChar K) {l r : Noun} (hW : l.leaves ≤ W)
    (hl : ∀ a, l = .atom a → a < ringChar K) (hsv : ServedFormulaCell inp.z pub dec l r) :
    l = .atom pub.state.toNat ∧
      Noun.slot 3 (.cell l r) = some r ∧ enc inp.z r = dec.f_t := by
  have hh : enc inp.z l = FP.atomFP inp.z (pub.state.toNat : K) := hsv.2.1 ▸ vcomp_f_h hV hcons
  exact ⟨lookup_binds_head hz W hwin _ hop l hW hl hh, by simp [Noun.slot], hsv.2.2.symm⟩

theorem forge_rejected_by_lookup (z : K) (k op : ℕ) (hk : (k : K) ≠ (op : K)) :
    enc z (.atom k) ≠ FP.atomFP z (op : K) := by
  rw [enc_atom]
  intro h
  exact hk (by simpa using congrArg FP.leaf h)

theorem forge_rejected_at_row {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K}
    {dec : ComputeTable.Dec K} (hcons : pub.state ≠ State.cons) (k : ℕ) (t : Noun)
    (hk : (k : K) ≠ (pub.state.toNat : K)) :
    ¬ (Vcomp inp pub dec ∧ ServedFormulaCell inp.z pub dec (.atom k) t) := by
  rintro ⟨hV, hsv⟩
  exact forge_rejected_by_lookup inp.z k _ hk (hsv.2.1 ▸ vcomp_f_h hV hcons)

theorem forged_tail_not_served {z : K} (hz : z ≠ 0) (k op : ℕ) (hk : (k : K) ≠ (op : K))
    (t : Noun) : forgedTail z k op t ≠ enc z t := by
  intro h
  exact (wrong_opcode_inline_forge hz k op hk t).2 ⟨t, by simp [Noun.slot], h.symm⟩

theorem forge_accepted_inline_rejected_lookup {inp : ComputeTable.Inputs K}
    {pub : ComputeTable.Pub K} {dec : ComputeTable.Dec K} (hz : inp.z ≠ 0)
    (hcons : pub.state ≠ State.cons) (k : ℕ) (t : Noun)
    (hk : (k : K) ≠ (pub.state.toNat : K)) :
    FP.cons inp.z (FP.atomFP inp.z (pub.state.toNat : K)) (forgedTail inp.z k pub.state.toNat t) =
        enc inp.z (.cell (.atom k) t) ∧
      ¬ (Vcomp inp pub dec ∧ ServedFormulaCell inp.z pub dec (.atom k) t) ∧
      forgedTail inp.z k pub.state.toNat t ≠ enc inp.z t :=
  ⟨(wrong_opcode_inline_forge hz k _ hk t).1, forge_rejected_at_row hcons k t hk,
    forged_tail_not_served hz k _ hk t⟩

end head

/-! ## 7. The repaired chip `computeChipVCLD` -/

section gatesD
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- **The gates of the repaired chip**: `vclGatesA` (`computeChipVCLA`) and the nine lookup gates. -/
def vclGatesD (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) : List (CoeffExpr F) :=
  vclGatesA n b ++ lookupGatesD b γc ρc

theorem vclGatesD_length (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    (vclGatesD n b γc ρc).length = 321 := by
  simp [vclGatesD, vclGatesA_length, lookupGatesD_length]

theorem vclGatesD_degree (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    ∀ g ∈ vclGatesD n b γc ρc, g.degree ≤ 4 := by
  intro g hg
  simp only [vclGatesD, List.mem_append] at hg
  rcases hg with h | h
  · exact vclGatesA_degree n b g h
  · exact (lookupGatesD_degree b γc ρc g h).trans (by omega)

end gatesD

def vclRAPD {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  { e := 3
    k := 2
    wRAP := ![vclRound0, 18]
    w := vclWidthD
    w_eq := by simp [Fin.sum_univ_two, vclRound0, vclWidthD]
    h := h
    d := 4
    s := (vclGatesD n b γc ρc).length
    ω := orbit.ω
    β := orbit.βcoset
    I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
    C := fun i => coeffToMv chalV pubVal ((vclGatesD n b γc ρc).get i)
    C_vars := fun _i => coeffToMv_vars chalV pubVal _
    C_deg := fun _i => (coeffToMv_totalDegree_le chalV pubVal _).trans
      (vclGatesD_degree n b γc ρc _ (List.get_mem _ _))
    H := H
    β_ne_zero := orbit.βcoset_ne_zero
    I_bound := by
      intro q hq
      have hq2 : q.2 = 0 ∨ q.2 = 1 := by
        have h2 := (Finset.mem_product.mp hq).2
        simpa [Finset.mem_insert, Finset.mem_singleton] using h2
      have hge : 2 ≤ 2 ^ h := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) orbit.h_pos
      rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega }

/-- **`computeChipVCLD`**: `computeChipVCLA` plus `fIdx` (`222`), slot 0's inverse (`223..225`)
and the three slots' lookup-inverse gates (IO coin limbs `γc`, `ρc`). -/
def computeChipVCLD
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) : FixedPreprocessingRAP F where
  rap := vclRAPD (n := n) b γc ρc chalV pubVal orbit (rowNodeSet nodes)
  rounds_pos := by norm_num [vclRAPD]
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨11 + (j : ℕ), by
          have := j.isLt
          change 11 + (j : ℕ) < vclRound0
          simp only [vclRound0]
          omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

theorem computeChipVCLD_sat_iff
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLD hn nodes b γc ρc chalV pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLD hn nodes b γc ρc chalV pubVal orbit) P ↔
      (computeChipVCLD hn nodes b γc ρc chalV pubVal orbit).BindsPreprocessing P ∧
        ∀ x ∈ rowNodeSet nodes, ∀ g ∈ vclGatesD n b γc ρc,
          g.eval (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := by
  have key : ∀ (i : Fin (computeChipVCLD hn nodes b γc ρc chalV pubVal orbit).rap.s) (x : F),
      ((computeChipVCLD hn nodes b γc ρc chalV pubVal orbit).rap.compose P i).eval x =
        ((vclGatesD n b γc ρc).get i).eval (Reify.envOfTrace P orbit.ω x chalV pubVal) := by
    intro i x
    rw [Reify.compose_eval]
    exact eval_coeffToMv P orbit.ω x chalV pubVal _
  constructor
  · rintro ⟨hraw, hfixed⟩
    refine ⟨hfixed, fun x hx g hg => ?_⟩
    obtain ⟨i, hget⟩ := List.mem_iff_get.mp hg
    have hz := hraw i x hx
    rw [key i x] at hz
    rwa [← hget]
  · rintro ⟨hfixed, hall⟩
    refine ⟨?_, hfixed⟩
    intro i x hx
    rw [key i x]
    exact hall x hx _ (List.get_mem _ _)

/-- **The new chip tuple** `(e, w, s, d, k) = (3, 226, 321, 4, 2)` (was `(3, 222, 312, 4, 2)`):
`+4` columns (`fIdx` and one `𝕂` inverse triple; DESIGN's `≈ +7` counts a `𝕂′` inverse, i.e.
after the tower retype), `+9` gates (slot 0's triple and the multiplexed triples of slots 1/2,
whose inverse columns were unpinned at `computeChipVCLA`). -/
theorem vclRAPD_fingerprint
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    let R := vclRAPD (n := n) b γc ρc chalV pubVal orbit H
    R.w = 226 ∧ R.s = 321 ∧ R.d = 4 ∧ R.k = 2 ∧ R.e = 3 ∧ R.wRAP = ![208, 18] :=
  ⟨rfl, vclGatesD_length n b γc ρc, rfl, rfl, rfl, rfl⟩

/-- **Acceptance at the repaired chip gives the slot-0 reciprocal on every row**: the formula
cell is consumed at every row of every accepted trace. -/
theorem computeChipVCLD_slot0
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLD hn nodes b γc ρc chalV pubVal orbit).rap.w → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (computeChipVCLD hn nodes b γc ρc chalV pubVal orbit) P)
    (x : F) (hx : x ∈ rowNodeSet nodes) :
    let envF := Reify.envOfTrace P orbit.ω x chalV pubVal
    invVal b envF inv0Base *
      FiniteIO.compress (coinsAt b envF γc ρc) (recVal b envF formulaRec) = 1 := by
  intro envF
  have hall := ((computeChipVCLD_sat_iff hn nodes b γc ρc chalV pubVal orbit P).1 hP).2 x hx
  exact slot0_sound b γc ρc envF fun g hg =>
    hall g (by simp only [vclGatesD, lookupGatesD, List.mem_append]; exact Or.inr (Or.inl (Or.inl hg)))

end

end VclL.Compute
end Nock.NockVMROM.Thm54
