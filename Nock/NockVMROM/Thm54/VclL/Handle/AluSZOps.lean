/-
  Field: `Fp = ZMod p`, `p` the Goldilocks prime (`Nock.Atoms.ArithSZ`'s lifts live there).

  * §1 `Rows`: a window of ALU rows whose gates vanish (`AluSZRead`'s `RowGates`), next-row reads linked, the last row
    `isLT`, a boolean preg selector, the challenge leaves carrying `y` and `y^t`.  Row facts: booleans, one-hot
    tags / modes / kinds, the slot walk (`Slot`, `slot_of`, `after`, `after_hdr`), block constancy (`const_run`).
  * §2 `AluSZEvent`'s readout `al` of the window (`Readout`), the mirror unrolled along a run (`hornerP_run`, `hpackP_run`)
    and evaluated by the `𝕂′` chains (`chainH`, `chainP`): the mirror = the chip's columns.
  * §3 `ReadOK` (`AluSZRead`'s `fp_read_sound` conclusion), `Ctx` (window, readouts, atom table reading `r`, the atom walk
    faithful to `r` — CARRIED as the field `walk` — and every validity read served), `Lp_ev`, the
    per-row contributions (`D_hdr`, `D_inner`, `D_first`), the `qSum` telescope and **`premise` / `premise_of`:
    the premise of the per-call `outside_arithSZ` from one call block's gates**.
  * §4 slot values (`operand`, `witness`, `qslot1`, `split_val`), **the block shape from the role sequence**
    (`shape_q1`), handle binding (`bind_val`), `HDen` (what a handle denotes) and `HDen.denK`.
  * §5 **`add_sound`, `sub_sound`, `lt_sound`** (the hypothesis `hout` is the conclusion of `outside_arithSZ`).
  * §6 **`out_canonical`**.  §7 `hout_of_event` and **`op_sound`** (add/sub/lt) off `AluSZEvent.arithSZ`.
  * §8 **chip satisfaction ⇒ `RowGates` per row** (`alu_rowGates`) and the window `rowsOf`.
  * §9 `readOK_of_served`: `AluSZRead`'s served read gives `ReadOK`.
  NOT here (this run): `mul`, `div`, `mod` (W-form with views, latches `RL/RO`, the 6-bit length cap, `mQM`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AluSZRead
import Nock.NockVMROM.Thm54.VclL.Handle.AluSZEvent
import Nock.Atoms.ArithSZ
import Nock.Jet.PrimJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluSZOps

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZRead
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (AG CopyG Op)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZEvent (cl onb rowAt laneL laneO laneBits limbPolyQ atomPoly BX hornerP
  packP hpackP Hp HOp Lp Lf RLp ROp D1p D2p blockSum blockRows linkP callPolys hdrs)
open Nock.Atoms (val B Canonical limbPoly natPoly Fp)
open Nock.NockVMROM.Thm54.VclL.Chips.CertBound (bits_sum_nat bool_cases)

noncomputable section

/-! ## 0. Field facts -/

theorem hqFp : 2 ^ 63 < ringChar Fp := by
  rw [ZMod.ringChar_zmod_n]; norm_num [Nock.Atoms.p, Nock.Field.p]

theorem castFp_inj {x y : ℕ} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) (h : (x : Fp) = y) : x = y :=
  AtomChipHQ.cast_inj hqFp hx hy h

theorem two_ne : (2 : Fp) ≠ 0 := by
  intro h
  have := castFp_inj (x := 2) (y := 0) (by norm_num) (by norm_num) (by simpa using h)
  omega

theorem one_ne_negone : (1 : Fp) ≠ -1 := by
  intro h
  have : (2 : Fp) = 0 := by linear_combination h
  exact two_ne this

/-- A boolean field element is `0` or `1`. -/
theorem bool01 {x : Fp} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := bool_cases h

/-! ### One-hot sums of booleans -/

theorem nat_onehot : ∀ (l : List ℕ) (f : ℕ → ℕ) {c : ℕ}, l.Nodup → c ∈ l → f c = 1 → (l.map f).sum = 1 →
    ∀ d ∈ l, d ≠ c → f d = 0
  | [], _, _, _, hc, _, _ => by simp at hc
  | a :: l, f, c, hnd, hc, h1, hs => by
    intro d hd hdc
    simp only [List.map_cons, List.sum_cons] at hs
    rw [List.nodup_cons] at hnd
    by_cases hac : a = c
    · subst hac
      have h0 : (l.map f).sum = 0 := by omega
      rcases List.mem_cons.mp hd with rfl | hd
      · exact absurd rfl hdc
      · exact List.sum_eq_zero_iff.mp h0 _ (List.mem_map.mpr ⟨d, hd, rfl⟩)
    · have hcl : c ∈ l := by
        rcases List.mem_cons.mp hc with h | h
        · exact absurd h.symm hac
        · exact h
      have hle : f c ≤ (l.map f).sum := List.le_sum_of_mem (List.mem_map.mpr ⟨c, hcl, rfl⟩)
      have hfa : f a = 0 := by omega
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hfa
      · exact nat_onehot l f hnd.2 hcl h1 (by omega) d hd hdc

/-- The `0/1` reading of a boolean column. -/
def b01 (e : Env Fp) (j : ℕ) : ℕ := if e.trace j = 1 then 1 else 0

theorem b01_cast {e : Env Fp} {j : ℕ} (h : e.trace j = 0 ∨ e.trace j = 1) : ((b01 e j : ℕ) : Fp) = e.trace j := by
  unfold b01; rcases h with h | h <;> simp [h]

theorem b01_le (e : Env Fp) (j : ℕ) : b01 e j ≤ 1 := by unfold b01; split_ifs <;> omega

theorem sum_b01_le (e : Env Fp) (l : List ℕ) : (l.map (b01 e)).sum ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := b01_le e a; omega

theorem sum_cast_b01 {e : Env Fp} {l : List ℕ} (hb : ∀ j ∈ l, e.trace j = 0 ∨ e.trace j = 1) :
    (((l.map (b01 e)).sum : ℕ) : Fp) = (l.map e.trace).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    rw [b01_cast (hb a List.mem_cons_self), ih fun j hj => hb j (List.mem_cons_of_mem _ hj)]

/-- **One-hot**: booleans whose sum is `0` or `1`, one of them `1` ⇒ the sum is `1` and the others are `0`. -/
theorem onehot {e : Env Fp} {l : List ℕ} (hlen : l.length < 2 ^ 62) (hnd : l.Nodup)
    (hb : ∀ j ∈ l, e.trace j = 0 ∨ e.trace j = 1)
    (hs : (l.map e.trace).sum = 0 ∨ (l.map e.trace).sum = 1) {c : ℕ} (hc : c ∈ l) (h1 : e.trace c = 1) :
    (l.map e.trace).sum = 1 ∧ ∀ d ∈ l, d ≠ c → e.trace d = 0 := by
  have hcast := sum_cast_b01 hb
  have hle := sum_b01_le e l
  have hc1 : b01 e c = 1 := by simp [b01, h1]
  have hge : 1 ≤ (l.map (b01 e)).sum := hc1 ▸ List.le_sum_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hsum : (l.map (b01 e)).sum = 1 := by
    rcases hs with hs | hs
    · rw [hs] at hcast
      have := castFp_inj (x := (l.map (b01 e)).sum) (y := 0) (by omega) (by norm_num) (by simpa using hcast)
      omega
    · rw [hs] at hcast
      exact castFp_inj (by omega) (by norm_num) (by simpa using hcast)
  refine ⟨by rw [← hcast, hsum]; simp, fun d hd hdc => ?_⟩
  have := nat_onehot l (b01 e) hnd hc hc1 hsum d hd hdc
  rw [← b01_cast (hb d hd), this]; simp

/-! ## 1. A window of ALU rows -/

variable {K : Type} [Field K] [Algebra Fp K] {δ : Fp} [Fact (¬ IsSquare (algebraMap Fp K δ))]

local notation "𝕂′" => Quad (algebraMap Fp K δ)

/-- **A window of `n` ALU rows**: row environments with every ALU gate vanishing (`RowGates`, `AluSZRead`), next-row reads
linked, the last row the trace's last (`isLT = 1`), and the challenge leaves carrying the limb coin `y` (leaves
`2 / 3`) and its powers `y^t`, `t ≤ 32` (leaves `40 + 2t / 41 + 2t`; `chalsALJ8_y`, `chalsALJ8_ypow`).  §8 builds
it from chip satisfaction. -/
structure Rows (δ : Fp) (K : Type) [Field K] [Algebra Fp K] where
  n : ℕ
  pos : 0 < n
  eK : ℕ → Env K
  eF : ℕ → Env Fp
  gates : ∀ i < n, RowGates δ (eK i) (eF i)
  nextF : ∀ i, i + 1 < n → ∀ j, (eF i).traceNext j = (eF (i + 1)).trace j
  nextK : ∀ i, i + 1 < n → ∀ j, (eK i).traceNext j = (eK (i + 1)).trace j
  last : (eF (n - 1)).trace isLT = 1
  /-- The last-row mask is 0 off the last row (`masks_of`); the next-row gates are masked by `1 − isLT`. -/
  notLast : ∀ i, i + 1 < n → (eF i).trace isLT = 0
  /-- The preprocessed preg selector is boolean (verifier data, `pre 0`). -/
  spBool : ∀ i < n, (eF i).trace sP = 0 ∨ (eF i).trace sP = 1
  y : Quad (algebraMap Fp K δ)
  chalY : ∀ i < n, Quad.mk (algebraMap Fp K δ) ((eK i).chal 2) ((eK i).chal 3) = y
  chalPow : ∀ i < n, ∀ t ≤ 32,
    Quad.mk (algebraMap Fp K δ) ((eK i).chal (40 + 2 * t)) ((eK i).chal (41 + 2 * t)) = y ^ t

namespace Rows
variable (R : Rows δ K)

/-- Column `j` at row `i`. -/
abbrev v (i j : ℕ) : Fp := (R.eF i).trace j

/-- A `𝕂′` column (roles `r`, `r + 1`) at row `i`. -/
abbrev q (i r : ℕ) : 𝕂′ := (QE.var r : QE Fp).ev δ (R.eK i) (R.eF i)

/-! ### Gate access -/

theorem mem_seq {a : AG Fp} (ha : a ∈ gSeq) : a ∈ baseAG := by simp only [baseAG, List.mem_append]; tauto
theorem mem_coef {a : AG Fp} (ha : a ∈ gCoef) : a ∈ baseAG := by simp only [baseAG, List.mem_append]; tauto
theorem mem_hdr {a : AG Fp} (ha : a ∈ gHdr) : a ∈ baseAG := by simp only [baseAG, List.mem_append]; tauto
theorem mem_const {a : AG Fp} (ha : a ∈ gConst) : a ∈ baseAG := by simp only [baseAG, List.mem_append]; tauto
theorem mem_bind {a : AG Fp} (ha : a ∈ gBind) : a ∈ baseAG := by simp only [baseAG, List.mem_append]; tauto
theorem mem_cap {a : AG Fp} (ha : a ∈ gCap) : a ∈ baseAG := by simp only [baseAG, List.mem_append]; tauto

theorem G {i : ℕ} (hi : i < R.n) {a : AG Fp} (ha : a ∈ baseAG) : a.gate.eval (R.eF i) = 0 :=
  ag_zero (R.gates i hi) ha

theorem Q0 {i : ℕ} (hi : i < R.n) {e : QE Fp} (he : e ∈ aluQ δ) : e.ev δ (R.eK i) (R.eF i) = 0 :=
  qe_zero (R.gates i hi) he

theorem QZ {i : ℕ} (hi : i < R.n) {σ : CoeffExpr Fp} {a b : QE Fp} (he : qz σ a b ∈ aluQ δ)
    (hσ : σ.eval (R.eF i) = 1) : a.ev δ (R.eK i) (R.eF i) = b.ev δ (R.eK i) (R.eF i) :=
  qz_eq (R.gates i hi) he hσ

theorem mem_ident {e : QE Fp} (he : e ∈ identQ δ) : e ∈ aluQ δ := mem_identQ he

/-! ### Booleans -/

theorem boolc {i : ℕ} (hi : i < R.n) {j : ℕ} (hj : (ar (boolE (cv j)) : AG Fp) ∈ baseAG) :
    R.v i j = 0 ∨ R.v i j = 1 := by
  have g := R.G hi hj
  simp only [AG.gate, ar, boolE, cv, CoeffExpr.eval] at g
  exact bool01 g

theorem b_sH {i : ℕ} (hi : i < R.n) : R.v i sH = 0 ∨ R.v i sH = 1 := R.boolc hi (mem_kind (by simp [gKind]))
theorem b_sL {i : ℕ} (hi : i < R.n) : R.v i sL = 0 ∨ R.v i sL = 1 := R.boolc hi (mem_kind (by simp [gKind]))
theorem b_fst {i : ℕ} (hi : i < R.n) : R.v i fst = 0 ∨ R.v i fst = 1 := R.boolc hi (mem_slot (by simp [gSlot]))
theorem b_eos {i : ℕ} (hi : i < R.n) : R.v i eos = 0 ∨ R.v i eos = 1 := R.boolc hi (mem_slot (by simp [gSlot]))
theorem b_lb {i : ℕ} (hi : i < R.n) : R.v i lb = 0 ∨ R.v i lb = 1 := R.boolc hi (mem_hdr (by simp [gHdr]))
theorem b_op {i : ℕ} (hi : i < R.n) {j : ℕ} (hj : j ∈ opCols) : R.v i j = 0 ∨ R.v i j = 1 :=
  R.boolc hi (mem_kind (by
    unfold gKind
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, hj, rfl⟩)))))))
theorem b_role {i : ℕ} (hi : i < R.n) {j : ℕ} (hj : j ∈ roleCols) : R.v i j = 0 ∨ R.v i j = 1 :=
  R.boolc hi (mem_kind (by
    unfold gKind
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, hj, rfl⟩)))))
theorem b_mode {i : ℕ} (hi : i < R.n) {j : ℕ} (hj : j ∈ modeCols) : R.v i j = 0 ∨ R.v i j = 1 :=
  R.boolc hi (mem_kind (by
    unfold gKind
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, hj, rfl⟩))))
theorem b_tag {i : ℕ} (hi : i < R.n) {j : ℕ} (hj : j ∈ roleCols ++ [mQ1, mQM]) : R.v i j = 0 ∨ R.v i j = 1 := by
  rcases List.mem_append.mp hj with h | h
  · exact R.b_role hi h
  · exact R.b_mode hi (by simp [modeCols] at h ⊢; tauto)

/-- The kind sum `sP + sH + sL` is boolean. -/
theorem kind_sum {i : ℕ} (hi : i < R.n) : R.v i sP + R.v i sH + R.v i sL = 0 ∨ R.v i sP + R.v i sH + R.v i sL = 1 := by
  have g := R.G hi (mem_kind (a := ar (boolE (sumC [sP, sH, sL]))) (by simp [gKind]))
  simp only [AG.gate, ar, boolE, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero] at g
  rcases bool01 g with h | h
  · left; linear_combination h
  · right; linear_combination h

/-- **A lane row is not a hdr row.** -/
theorem lane_sH {i : ℕ} (hi : i < R.n) (hL : R.v i sL = 1) : R.v i sH = 0 := by
  have := onehot (e := R.eF i) (l := [sP, sH, sL]) (by simp) (by decide)
    (by intro j hj; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact R.spBool i hi
        · exact R.b_sH hi
        · exact R.b_sL hi)
    (by simpa [add_assoc] using R.kind_sum hi) (c := sL) (by simp) hL
  exact this.2 sH (by simp) (by decide)

theorem hdr_sL {i : ℕ} (hi : i < R.n) (hH : R.v i sH = 1) : R.v i sL = 0 := by
  have := onehot (e := R.eF i) (l := [sP, sH, sL]) (by simp) (by decide)
    (by intro j hj; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact R.spBool i hi
        · exact R.b_sH hi
        · exact R.b_sL hi)
    (by simpa [add_assoc] using R.kind_sum hi) (c := sH) (by simp) hH
  exact this.2 sL (by simp) (by decide)

/-- `isLT·(sH + sL) = 0`: a hdr or lane row is not the last row. -/
theorem not_last {i : ℕ} (hi : i < R.n) (h : R.v i sH = 1 ∨ R.v i sL = 1) : i + 1 < R.n := by
  by_contra hc
  have hi' : i = R.n - 1 := by omega
  have g := R.G hi (mem_kind (a := ar (.mul (cv isLT) (sumC [sH, sL]))) (by simp [gKind]))
  simp only [AG.gate, ar, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero] at g
  have hl : R.v i isLT = 1 := by rw [hi']; exact R.last
  simp only [Rows.v] at hl
  rw [hl, one_mul] at g
  rcases h with h | h
  · have h0 := R.hdr_sL hi h; simp only [Rows.v] at h h0; rw [h, h0] at g; simp at g
  · have h0 := R.lane_sH hi h; simp only [Rows.v] at h h0; rw [h, h0] at g; simp at g

/-- The tag sum `sL = Σ roles + mQ1 + mQM`. -/
theorem tag_sum {i : ℕ} (hi : i < R.n) : R.v i sL = ((roleCols ++ [mQ1, mQM]).map (R.eF i).trace).sum := by
  have g := R.G hi (mem_kind (a := ar (.sub (cv sL) (sumC (roleCols ++ [mQ1, mQM])))) (by simp [gKind]))
  simp only [AG.gate, ar, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv] at g
  have : ((roleCols ++ [mQ1, mQM]).map fun j => (R.eF i).trace j) = (roleCols ++ [mQ1, mQM]).map (R.eF i).trace := rfl
  rw [this] at g
  exact sub_eq_zero.mp g

theorem tags_nodup : (roleCols ++ [mQ1, mQM]).Nodup := by decide

/-- **A tagged row is a lane row, and its tag is one-hot.** -/
theorem tag_onehot {i : ℕ} (hi : i < R.n) {c : ℕ} (hc : c ∈ roleCols ++ [mQ1, mQM]) (h1 : R.v i c = 1) :
    R.v i sL = 1 ∧ ∀ d ∈ roleCols ++ [mQ1, mQM], d ≠ c → R.v i d = 0 := by
  have hs := R.tag_sum hi
  have := onehot (e := R.eF i) (l := roleCols ++ [mQ1, mQM]) (by simp [roleCols]) tags_nodup
    (fun j hj => R.b_tag hi hj) (by rw [← hs]; exact R.b_sL hi) hc h1
  exact ⟨by rw [hs]; exact this.1, this.2⟩

/-- **Modes are one-hot on a lane row.** -/
theorem mode_onehot {i : ℕ} (hi : i < R.n) (hL : R.v i sL = 1) {c : ℕ} (hc : c ∈ modeCols) (h1 : R.v i c = 1) :
    ∀ d ∈ modeCols, d ≠ c → R.v i d = 0 := by
  have hs := modes_sum (R.gates i hi)
  have := onehot (e := R.eF i) (l := modeCols) (by simp [modeCols]) (by decide)
    (fun j hj => R.b_mode hi hj)
    (by right; simp only [modeCols, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rw [← hL]; simp only [Rows.v] at hs ⊢; rw [hs]; ring) hc h1
  exact this.2

/-! ### Slots -/

/-- **A run**: rows `i .. i + m − 1` with `eos` exactly on the last. -/
structure Run (i m : ℕ) : Prop where
  pos : 1 ≤ m
  lt : i + m < R.n
  eos0 : ∀ j, j + 1 < m → R.v (i + j) eos = 0
  eos1 : R.v (i + m - 1) eos = 1

/-- **A slot**: a run of lane rows, `fst` exactly on the first, roles and modes constant. -/
structure Slot (i m : ℕ) : Prop extends R.Run i m where
  lane : ∀ j < m, R.v (i + j) sL = 1
  fst0 : R.v i fst = 1
  fst1 : ∀ j, 1 ≤ j → j < m → R.v (i + j) fst = 0
  same : ∀ j < m, ∀ c ∈ roleCols ++ modeCols, R.v (i + j) c = R.v i c

theorem Run.tail {i m : ℕ} (h : R.Run i m) (hm : 2 ≤ m) : R.Run (i + 1) (m - 1) where
  pos := by omega
  lt := by have := h.lt; omega
  eos0 j hj := by have := h.eos0 (j + 1) (by omega); rwa [show i + (j + 1) = i + 1 + j by omega] at this
  eos1 := by have := h.eos1; rwa [show i + m - 1 = i + 1 + (m - 1) - 1 by omega] at this

/-- Inside a slot (`eos = 0` on a lane row): the next row is a lane row, not `fst`, same roles and modes. -/
theorem inside {i : ℕ} (hi : i < R.n) (hL : R.v i sL = 1) (he : R.v i eos = 0) :
    i + 1 < R.n ∧ R.v (i + 1) sL = 1 ∧ R.v (i + 1) fst = 0 ∧ ∀ c ∈ roleCols ++ modeCols, R.v (i + 1) c = R.v i c := by
  have hn := R.not_last hi (Or.inr hL)
  have g1 := R.G hi (mem_slot (a := ar (prod3 (cv sL) (notE (cv eos)) (notE (nv sL))))
    (by unfold gSlot; exact List.mem_append_left _ (by simp)))
  have g2 := R.G hi (mem_slot (a := ar (prod3 (cv sL) (notE (cv eos)) (nv fst)))
    (by unfold gSlot; exact List.mem_append_left _ (by simp)))
  simp only [AG.gate, ar, prod3, notE, cv, nv, CoeffExpr.eval, R.nextF i hn] at g1 g2
  simp only [Rows.v] at hL he
  rw [hL, he] at g1 g2
  refine ⟨hn, by linear_combination -g1, by linear_combination g2, fun c hc => ?_⟩
  have g3 := R.G hi (mem_slot (a := ar (prod3 (cv sL) (notE (cv eos)) (.sub (nv c) (cv c))))
    (by unfold gSlot; exact List.mem_append_right _ (List.mem_map.mpr ⟨c, hc, rfl⟩)))
  simp only [AG.gate, ar, prod3, notE, cv, nv, CoeffExpr.eval, R.nextF i hn, hL, he] at g3
  linear_combination g3

/-- **The slot walk**: from a lane row, the lane rows continue until an `eos`. -/
theorem walk : ∀ d i, R.n - i = d → i < R.n → R.v i sL = 1 →
    ∃ m, R.Run i m ∧ (∀ j < m, R.v (i + j) sL = 1) ∧ (∀ j, 1 ≤ j → j < m → R.v (i + j) fst = 0) ∧
      ∀ j < m, ∀ c ∈ roleCols ++ modeCols, R.v (i + j) c = R.v i c := by
  intro d
  induction d with
  | zero => intro i hd hi; omega
  | succ d ih =>
    intro i hd hi hL
    have hn := R.not_last hi (Or.inr hL)
    rcases R.b_eos hi with he | he
    · obtain ⟨_, hL1, hf1, hc1⟩ := R.inside hi hL he
      obtain ⟨m, hr, hl, hf, hc⟩ := ih (i + 1) (by omega) hn hL1
      refine ⟨m + 1, ⟨by omega, by have := hr.lt; omega, fun j hj => ?_, ?_⟩, fun j hj => ?_, fun j h1 hj => ?_,
        fun j hj c hcm => ?_⟩
      · rcases j with _ | j
        · simpa using he
        · rw [show i + (j + 1) = i + 1 + j by omega]; exact hr.eos0 j (by omega)
      · rw [show i + (m + 1) - 1 = i + 1 + m - 1 by omega]; exact hr.eos1
      · rcases j with _ | j
        · simpa using hL
        · rw [show i + (j + 1) = i + 1 + j by omega]; exact hl j (by omega)
      · rcases j with _ | j
        · omega
        · rw [show i + (j + 1) = i + 1 + j by omega]
          rcases j with _ | j
          · simpa using hf1
          · exact hf (j + 1) (by omega) (by omega)
      · rcases j with _ | j
        · simp
        · rw [show i + (j + 1) = i + 1 + j by omega, hc j (by omega) c hcm, hc1 c hcm]
    · exact ⟨1, ⟨le_rfl, by omega, fun j hj => by omega, by simpa using he⟩, fun j hj => by
        rw [show j = 0 by omega]; simpa using hL, fun j h1 hj => by omega,
        fun j hj c _ => by rw [show j = 0 by omega]; simp⟩

theorem slot_of {i : ℕ} (hi : i < R.n) (hL : R.v i sL = 1) (hf : R.v i fst = 1) : ∃ m, R.Slot i m := by
  obtain ⟨m, hr, hl, hf1, hc⟩ := R.walk _ i rfl hi hL
  exact ⟨m, { hr with lane := hl, fst0 := hf, fst1 := hf1, same := hc }⟩

/-- The last row of a slot. -/
theorem Slot.lastRow {i m : ℕ} (s : R.Slot i m) : i + m - 1 < R.n ∧ R.v (i + m - 1) eos = 1 ∧
    R.v (i + m - 1) sL = 1 ∧ ∀ c ∈ roleCols ++ modeCols, R.v (i + m - 1) c = R.v i c := by
  have h1 := s.lane (m - 1) (by have := s.pos; omega)
  have h2 := s.same (m - 1) (by have := s.pos; omega)
  rw [show i + (m - 1) = i + m - 1 by have := s.pos; omega] at h1 h2
  exact ⟨by have := s.lt; omega, s.eos1, h1, h2⟩

/-- **After a slot** (`eos·r·σ·(1 − s′)` with `r = σ = 1` at the slot's last row): the next row starts a slot of
tag `s`. -/
theorem after {i m : ℕ} (s : R.Slot i m) {r : ℕ} (hr : r ∈ roleCols ++ modeCols) (hr1 : R.v i r = 1)
    {σ : CoeffExpr Fp} {t : ℕ} (hg : succ r σ t ∈ gSeq) (hσ : σ.eval (R.eF (i + m - 1)) = 1)
    (ht : t ∈ roleCols ++ [mQ1, mQM]) :
    R.v (i + m) t = 1 ∧ R.v (i + m) sL = 1 ∧ R.v (i + m) fst = 1 := by
  obtain ⟨hk, he, hL, hc⟩ := Rows.Slot.lastRow R s
  have hn := R.not_last hk (Or.inr hL)
  have e1 : i + m - 1 + 1 = i + m := by have := s.pos; omega
  have g := R.G hk (mem_seq hg)
  simp only [AG.gate, succ, ar, prod3, notE, cv, nv, CoeffExpr.eval, R.nextF _ hn, hσ, e1] at g
  simp only [Rows.v] at he hc hr1
  rw [he, hc r hr, hr1] at g
  have ht1 : R.v (i + m) t = 1 := by simp only [Rows.v]; linear_combination -g
  have hL' := (R.tag_onehot (by omega) ht ht1).1
  have g2 := R.G hk (mem_slot (a := ar (.mul (.add (cv sH) (cv eos)) (.sub (nv sL) (nv fst))))
    (by unfold gSlot; exact List.mem_append_left _ (by simp)))
  simp only [AG.gate, ar, cv, nv, CoeffExpr.eval, R.nextF _ hn, e1] at g2
  have hs0 := R.lane_sH hk hL
  simp only [Rows.v] at hs0
  rw [hs0, he] at g2
  simp only [Rows.v] at hL'
  refine ⟨ht1, hL', ?_⟩
  simp only [Rows.v]; rw [hL'] at g2; linear_combination -g2

/-- **The hdr's next row starts the `ra` slot.** -/
theorem after_hdr {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) :
    h + 1 < R.n ∧ R.v (h + 1) ra = 1 ∧ R.v (h + 1) sL = 1 ∧ R.v (h + 1) fst = 1 := by
  have hn := R.not_last hh (Or.inl hH)
  have g := R.G hh (mem_slot (a := ar gHdrNotLast) (by unfold gSlot; exact List.mem_append_left _ (by simp)))
  simp only [AG.gate, ar, gHdrNotLast, notE, cv, nv, CoeffExpr.eval, R.nextF _ hn] at g
  simp only [Rows.v] at hH
  rw [hH, one_mul] at g
  have h1 : R.v (h + 1) ra = 1 := by simp only [Rows.v]; linear_combination -g
  have hL := (R.tag_onehot hn (c := ra) (by simp [roleCols]) h1).1
  have g2 := R.G hh (mem_slot (a := ar (.mul (.add (cv sH) (cv eos)) (.sub (nv sL) (nv fst))))
    (by unfold gSlot; exact List.mem_append_left _ (by simp)))
  simp only [AG.gate, ar, cv, nv, CoeffExpr.eval, R.nextF _ hn] at g2
  have he : R.v h eos = 0 := by
    have g3 := R.G hh (mem_slot (a := ar (.mul (cv eos) (notE (cv sL)))) (by simp [gSlot]))
    simp only [AG.gate, ar, notE, cv, CoeffExpr.eval, R.hdr_sL hh hH] at g3
    simp only [Rows.v]; linear_combination g3
  simp only [Rows.v] at he hL
  rw [hH, he, hL] at g2
  exact ⟨hn, h1, hL, by simp only [Rows.v]; linear_combination -g2⟩

/-! ### Block constants -/

/-- The block constants copied along lane rows. -/
def constCols : List ℕ := (opCols ++ [lb, kA, kB, kE]) ++ [vA, vB, vE]

theorem const_step {i : ℕ} (hn : i + 1 < R.n) (hL : R.v (i + 1) sL = 1) :
    ∀ c ∈ constCols, R.v (i + 1) c = R.v i c := by
  have hi : i < R.n := by omega
  intro c hc
  simp only [Rows.v] at hL ⊢
  rcases List.mem_append.mp hc with hc | hc
  · have g := R.G hi (mem_const (a := ar (.mul (.mul (notE (cv isLT)) (nv sL)) (.sub (nv c) (cv c))))
      (by unfold gConst; exact List.mem_append_left _ (List.mem_map.mpr ⟨c, hc, rfl⟩)))
    simp only [AG.gate, ar, cv, nv, notE, CoeffExpr.eval, R.nextF _ hn] at g
    have hlt := R.notLast i hn
    rw [hL, hlt] at g; simpa [sub_eq_zero] using g
  · have g := R.G hi (mem_const (a := AG.cp ⟨.mul (notE (cv isLT)) (nv sL), .nxt c, .cur c⟩)
      (by unfold gConst; exact List.mem_append_right _ (List.mem_map.mpr ⟨c, hc, rfl⟩)))
    simp only [AG.gate, CopyG.gate, Op.expr, cv, nv, notE, CoeffExpr.eval, R.nextF _ hn] at g
    have hlt := R.notLast i hn
    rw [hL, hlt] at g; simpa [sub_eq_zero] using g

/-- **Block constancy**: along lane rows after `h`, the block constants equal `h`'s. -/
theorem const_run {h k : ℕ} (hk : h + k < R.n) (hL : ∀ j, 1 ≤ j → j ≤ k → R.v (h + j) sL = 1) :
    ∀ j ≤ k, ∀ c ∈ constCols, R.v (h + j) c = R.v h c := by
  intro j
  induction j with
  | zero => intro _ c _; rfl
  | succ j ih =>
    intro hj c hc
    rw [← ih (by omega) c hc, show h + (j + 1) = h + j + 1 by omega]
    exact R.const_step (by omega) (by rw [show h + j + 1 = h + (j + 1) by omega]; exact hL _ (by omega) hj) c hc

/-- **A call block**: hdr row `h`, lane rows `h + 1 .. h + k`, then a non-lane row. -/
structure Block (h k : ℕ) : Prop where
  lt : h + k + 1 < R.n
  hdr : R.v h sH = 1
  lane : ∀ j, 1 ≤ j → j ≤ k → R.v (h + j) sL = 1
  stop : R.v (h + k + 1) sL = 0

end Rows

/-! ## 2. The round-0 readout and the polynomial mirror -/

/-- The ALU readout of `AluSZEvent` (`AluSZEvent.ARow`, column ↦ value) at the Goldilocks prime. -/
abbrev ALRow := AluSZEvent.ARow Nock.Atoms.p

/-- **The readout of a window**: `AluSZEvent`'s round-0 rows `al` are the window's base columns. -/
structure Readout (R : Rows δ K) (al : List ALRow) : Prop where
  len : al.length = R.n
  val : ∀ i < R.n, ∀ j, cl al i j = R.v i j

section Mirror
variable {R : Rows δ K} {al : List ALRow} (hal : Readout R al)
include hal

theorem onb_true {i j : ℕ} (hi : i < R.n) (h : R.v i j = 1) : onb al i j = true := by
  simp [onb, hal.val i hi j, h]

theorem onb_false {i j : ℕ} (hi : i < R.n) (h : R.v i j ≠ 1) : onb al i j = false := by
  simp [onb, hal.val i hi j, h]

theorem onb_zero {i j : ℕ} (hi : i < R.n) (h : R.v i j = 0) : onb al i j = false :=
  onb_false hal hi (by rw [h]; exact zero_ne_one)

omit hal in
theorem val_le_one {x : Fp} (h : x = 0 ∨ x = 1) : x.val ≤ 1 := by
  rcases h with rfl | rfl
  · simp
  · exact (ZMod.val_one_eq_one_mod _).trans_le (Nat.mod_le _ _)

/-- The low half `e = Σ_{t<16} 2^t b_t` of a lane (in ℕ). -/
def laneE (al : List ALRow) (i : ℕ) : ℕ := ∑ t ∈ Finset.range 16, 2 ^ t * (cl al i (bt0 + t)).val

omit hal in
theorem laneL_split (al : List ALRow) (i : ℕ) : laneL al i = laneE al i + 2 ^ 16 * laneO al i := by
  unfold laneL laneE laneO
  rw [show (32 : ℕ) = 16 + 16 from rfl, Finset.sum_range_add, Finset.mul_sum]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun t _ => ?_)
  rw [pow_add, show bt0 + (16 + t) = bt0 + 16 + t by omega]; ring

omit hal in
theorem sum_bits_lt (b : ℕ → ℕ) (hb : ∀ t, b t ≤ 1) : ∀ m, ∑ t ∈ Finset.range m, 2 ^ t * b t < 2 ^ m
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have := sum_bits_lt b hb m
    have := hb m
    have : 2 ^ m * b m ≤ 2 ^ m := (Nat.mul_le_mul_left _ this).trans (by rw [mul_one])
    omega

theorem bitv_le {i : ℕ} (hi : i < R.n) {t : ℕ} (ht : t < 32) : (cl al i (bt0 + t)).val ≤ 1 := by
  rw [hal.val i hi]
  exact val_le_one (bool01 (bit_bool (R.gates i hi) ht))

theorem laneL_lt {i : ℕ} (hi : i < R.n) : laneL al i < B := by
  have := sum_bits_lt (fun t => if t < 32 then (cl al i (bt0 + t)).val else 0)
    (fun t => by split_ifs with h; exact bitv_le hal hi h; omega) 32
  rw [Nock.Atoms.B, ← show (∑ t ∈ Finset.range 32, 2 ^ t *
    (if t < 32 then (cl al i (bt0 + t)).val else 0)) = laneL al i from
    Finset.sum_congr rfl fun t ht => by rw [if_pos (Finset.mem_range.mp ht)]]
  exact this

theorem laneO_lt {i : ℕ} (hi : i < R.n) : laneO al i < 2 ^ 16 := by
  have := sum_bits_lt (fun t => if t < 16 then (cl al i (bt0 + 16 + t)).val else 0)
    (fun t => by
      split_ifs with h
      · rw [Nat.add_assoc]; exact bitv_le hal hi (by omega)
      · omega) 16
  rw [← show (∑ t ∈ Finset.range 16, 2 ^ t *
    (if t < 16 then (cl al i (bt0 + 16 + t)).val else 0)) = laneO al i from
    Finset.sum_congr rfl fun t ht => by rw [if_pos (Finset.mem_range.mp ht)]]
  exact this

theorem laneE_lt {i : ℕ} (hi : i < R.n) : laneE al i < 2 ^ 16 := by
  have := sum_bits_lt (fun t => if t < 16 then (cl al i (bt0 + t)).val else 0)
    (fun t => by split_ifs with h; exact bitv_le hal hi (by omega); omega) 16
  rw [← show (∑ t ∈ Finset.range 16, 2 ^ t *
    (if t < 16 then (cl al i (bt0 + t)).val else 0)) = laneE al i from
    Finset.sum_congr rfl fun t ht => by rw [if_pos (Finset.mem_range.mp ht)]]
  exact this

theorem laneBits_le {i : ℕ} (hi : i < R.n) : ∀ x ∈ laneBits al i, x ≤ 1 := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact bitv_le hal hi (List.mem_range.mp ht)

theorem laneBits_length (i : ℕ) : (laneBits al i).length = 32 := by simp [laneBits]

omit hal in
theorem natCast_val_Fp (x : Fp) : ((x.val : ℕ) : Fp) = x := ZMod.natCast_zmod_val x

theorem laneL_cast {i : ℕ} (hi : i < R.n) : ((laneL al i : ℕ) : Fp) = (lE : CoeffExpr Fp).eval (R.eF i) := by
  rw [lE, eval_bitSum, laneL]; push_cast
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [natCast_val_Fp, hal.val i hi]

theorem laneO_cast {i : ℕ} (hi : i < R.n) : ((laneO al i : ℕ) : Fp) = (oE : CoeffExpr Fp).eval (R.eF i) := by
  rw [oE, eval_bitSum, laneO]; push_cast
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [natCast_val_Fp, hal.val i hi]

end Mirror

/-! ### Limb polynomials and lists -/

section Poly

theorem limbPolyQ_nil : limbPolyQ (q := Nock.Atoms.p) [] = 0 := by simp [limbPolyQ, natPoly]

theorem limbPolyQ_cons (a : ℕ) (l : List ℕ) :
    limbPolyQ (q := Nock.Atoms.p) (a :: l) = C (a : Fp) + X * limbPolyQ l := by
  simp [limbPolyQ, natPoly]

theorem natPoly_append (l1 l2 : List ℕ) : natPoly (l1 ++ l2) = natPoly l1 + X ^ l1.length * natPoly l2 := by
  induction l1 with
  | nil => simp [natPoly]
  | cons a l ih => simp only [List.cons_append, natPoly, ih, List.length_cons, pow_succ]; ring

theorem limbPolyQ_append (l1 l2 : List ℕ) :
    limbPolyQ (q := Nock.Atoms.p) (l1 ++ l2) = limbPolyQ l1 + X ^ l1.length * limbPolyQ l2 := by
  simp [limbPolyQ, natPoly_append, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

theorem limbPolyQ_eq (l : List ℕ) : limbPolyQ (q := Nock.Atoms.p) l = limbPoly l := rfl

/-- The lane values of rows `i .. i + m − 1`. -/
def lanes (g : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | i, m + 1 => g i :: lanes g (i + 1) m

theorem lanes_length (g : ℕ → ℕ) : ∀ i m, (lanes g i m).length = m
  | _, 0 => rfl
  | i, m + 1 => by simp [lanes, lanes_length g (i + 1) m]

theorem mem_lanes (g : ℕ → ℕ) : ∀ i m x, x ∈ lanes g i m → ∃ j < m, x = g (i + j)
  | _, 0, _, h => by simp [lanes] at h
  | i, m + 1, x, h => by
    simp only [lanes, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by omega, by simp⟩
    · obtain ⟨j, hj, rfl⟩ := mem_lanes g (i + 1) m x h
      exact ⟨j + 1, by omega, by rw [show i + 1 + j = i + (j + 1) by omega]⟩

theorem lanes_bound (g : ℕ → ℕ) {M i m : ℕ} (h : ∀ j < m, g (i + j) < M) : ∀ x ∈ lanes g i m, x < M := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := mem_lanes g i m x hx
  exact h j hj

/-- `natPoly` of a pointwise `e + c·o` lane list. -/
theorem natPoly_lanes_add (e o : ℕ → ℕ) (c : ℕ) : ∀ i m,
    natPoly (lanes (fun j => e j + c * o j) i m) = natPoly (lanes e i m) + C c * natPoly (lanes o i m)
  | _, 0 => by simp [lanes, natPoly]
  | i, m + 1 => by
    simp only [lanes, natPoly, natPoly_lanes_add e o c (i + 1) m, map_add, map_mul]; ring

theorem limbPolyQ_lanes_add (e o : ℕ → ℕ) (c : ℕ) (i m : ℕ) :
    limbPolyQ (q := Nock.Atoms.p) (lanes (fun j => e j + c * o j) i m) =
      limbPolyQ (lanes e i m) + C (c : Fp) * limbPolyQ (lanes o i m) := by
  simp [limbPolyQ, natPoly_lanes_add, Polynomial.map_add, Polynomial.map_mul]

/-- The packed carries of rows `i .. i + m − 1` (32 per row). -/
def packL (al : List ALRow) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | i, m + 1 => laneBits al i ++ packL al (i + 1) m

theorem mem_packL (al : List ALRow) : ∀ i m x, x ∈ packL al i m → ∃ j < m, x ∈ laneBits al (i + j)
  | _, 0, _, h => by simp [packL] at h
  | i, m + 1, x, h => by
    simp only [packL, List.mem_append] at h
    rcases h with h | h
    · exact ⟨0, by omega, by simpa using h⟩
    · obtain ⟨j, hj, hx⟩ := mem_packL al (i + 1) m x h
      exact ⟨j + 1, by omega, by rwa [show i + (j + 1) = i + 1 + j by omega]⟩

variable {A : Type} [Field A] [Algebra Fp A]

theorem aeval_limbPolyQ (y : A) (l : List ℕ) : aeval y (limbPolyQ (q := Nock.Atoms.p) l) = G5J8.horner y l :=
  G5J8.aeval_limbPoly y l

theorem horner_append (y : A) (l1 l2 : List ℕ) :
    G5J8.horner y (l1 ++ l2) = G5J8.horner y l1 + y ^ l1.length * G5J8.horner y l2 := by
  induction l1 with
  | nil => simp [G5J8.horner]
  | cons a l ih => simp only [List.cons_append, G5J8.horner, ih, List.length_cons, pow_succ]; ring

theorem horner_range (y : A) (g : ℕ → ℕ) : ∀ m,
    G5J8.horner y ((List.range m).map g) = ∑ t ∈ Finset.range m, ((g t : ℕ) : A) * y ^ t
  | 0 => by simp [G5J8.horner]
  | m + 1 => by
    rw [List.range_succ, List.map_append, horner_append, horner_range y g m, Finset.sum_range_succ]
    simp [G5J8.horner, mul_comm]

end Poly

/-! ### Unrolling the mirror along a run -/

section Unroll
variable {R : Rows δ K} {al : List ALRow} (hal : Readout R al)
include hal

theorem hornerP_run (lane : ℕ → ℕ) : ∀ m i f, R.Run i m → m ≤ f →
    hornerP al lane f i = limbPolyQ (lanes lane i m)
  | 0, _, _, r, _ => absurd r.pos (by omega)
  | m + 1, i, f, r, hf => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hi : i < R.n := by have := r.lt; omega
    by_cases hm : m = 0
    · subst hm
      have he : R.v i eos = 1 := by simpa using r.eos1
      simp [hornerP, onb_true hal hi he, lanes, limbPolyQ_cons, limbPolyQ_nil]
    · have he : R.v i eos = 0 := by simpa using r.eos0 0 (by omega)
      have rt := Rows.Run.tail R r (by omega)
      rw [Nat.add_sub_cancel] at rt
      simp only [hornerP, onb_zero hal hi he, Bool.false_eq_true, if_false,
        hornerP_run lane m (i + 1) f' rt (by omega), lanes, limbPolyQ_cons]

theorem hpackP_run : ∀ m i f, R.Run i m → m ≤ f → hpackP al f i = limbPolyQ (packL al i m)
  | 0, _, _, r, _ => absurd r.pos (by omega)
  | m + 1, i, f, r, hf => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hi : i < R.n := by have := r.lt; omega
    by_cases hm : m = 0
    · subst hm
      have he : R.v i eos = 1 := by simpa using r.eos1
      simp [hpackP, onb_true hal hi he, packL, packP]
    · have he : R.v i eos = 0 := by simpa using r.eos0 0 (by omega)
      have rt := Rows.Run.tail R r (by omega)
      rw [Nat.add_sub_cancel] at rt
      simp only [hpackP, onb_zero hal hi he, Bool.false_eq_true, if_false,
        hpackP_run m (i + 1) f' rt (by omega), packL, packP, limbPolyQ_append, laneBits_length hal]

end Unroll

/-! ### The `𝕂′` chains (Horner and packed) evaluate the mirror -/

section Chains
variable [Algebra Fp (Quad (algebraMap Fp K δ))] {R : Rows δ K} {al : List ALRow} (hal : Readout R al)

theorem aeval_C_Fp (y : 𝕂′) (c : Fp) : aeval y (C c) = liftQ δ c := by
  rw [aeval_C]
  exact RingHom.congr_fun (RingHom.ext_zmod (algebraMap Fp 𝕂′) ((algebraMap K 𝕂′).comp (algebraMap Fp K))) c

theorem aeval_natC (y : 𝕂′) (n : ℕ) : aeval y (C ((n : ℕ) : ZMod Nock.Atoms.p)) = ((n : ℕ) : 𝕂′) := by
  simp

theorem liftQ_val (x : Fp) : liftQ (K := K) δ x = ((x.val : ℕ) : 𝕂′) := by
  conv_lhs => rw [← natCast_val_Fp x]
  exact AluSZRead.liftQ_natCast _

include hal

/-- **The Horner chain evaluates the mirror** (`H` / `HO` along a run in a Horner mode). -/
theorem chainH {lane : ℕ → ℕ} {col : ℕ} {ex : CoeffExpr Fp}
    (hstep : qz (.mul hz (notE (cv eos))) (QE.var col) (QE.add (QE.base ex) (QE.mul δ yQ (QE.next col))) ∈ aluQ δ)
    (hend : qz (.mul hz (cv eos)) (QE.var col) (QE.base ex) ∈ aluQ δ)
    (hlane : ∀ i < R.n, ((lane i : ℕ) : Fp) = ex.eval (R.eF i)) :
    ∀ m i f, R.Run i m → (∀ j < m, (hz : CoeffExpr Fp).eval (R.eF (i + j)) = 1) → m ≤ f →
      aeval R.y (hornerP al lane f i) = (QE.var col).ev δ (R.eK i) (R.eF i)
  | 0, _, _, r, _, _ => absurd r.pos (by omega)
  | m + 1, i, f, r, hhz, hf => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hi : i < R.n := by have := r.lt; omega
    have hz0 : (hz : CoeffExpr Fp).eval (R.eF i) = 1 := by simpa using hhz 0 (by omega)
    by_cases hm : m = 0
    · subst hm
      have he : R.v i eos = 1 := by simpa using r.eos1
      have g := R.QZ hi hend (by simp only [CoeffExpr.eval, cv, hz0]; simpa using he)
      rw [ev_base, ← hlane i hi, AluSZRead.liftQ_natCast] at g
      simp only [hornerP, onb_true hal hi he, if_true, aeval_natC]
      exact g.symm
    · have he : R.v i eos = 0 := by simpa using r.eos0 0 (by omega)
      have rt := Rows.Run.tail R r (by omega)
      rw [Nat.add_sub_cancel] at rt
      have hn : i + 1 < R.n := by have := r.lt; omega
      have ih := chainH hstep hend hlane m (i + 1) f' rt
        (fun j hj => by rw [show i + 1 + j = i + (j + 1) by omega]; exact hhz (j + 1) (by omega)) (by omega)
      have g := R.QZ hi hstep (by simp only [CoeffExpr.eval, notE, cv, hz0]; simp only [Rows.v] at he; rw [he]; ring)
      rw [ev_add, ev_base, ev_mul, yQ, ev_chal, R.chalY i hi, ev_next, R.nextK i hn col, R.nextK i hn (col + 1),
        ← hlane i hi, AluSZRead.liftQ_natCast, ← ev_var] at g
      simp only [hornerP, onb_zero hal hi he, Bool.false_eq_true, if_false, map_add, map_mul, aeval_X, aeval_natC, ih]
      exact g.symm

omit hal in
/-- `ev` of a `𝕂′` list sum. -/
theorem ev_sumQ (eK : Env K) (eF : Env Fp) : ∀ l : List (QE Fp),
    (sumQ l).ev δ eK eF = (l.map fun e => e.ev δ eK eF).sum
  | [] => by simp [sumQ, ev_zero]
  | e :: l => by
    simp only [sumQ, List.foldr_cons, List.map_cons, List.sum_cons] at *
    rw [ev_add, ← ev_sumQ eK eF l]; rfl

/-- **One packed row**: `packE` at row `i` is `aeval y (packP al i)`. -/
theorem packE_ev {i : ℕ} (hi : i < R.n) :
    (packE : QE Fp).ev δ (R.eK i) (R.eF i) = aeval R.y (packP al i) := by
  rw [packE, ev_sumQ, List.map_map, list_range_sum]
  rw [packP, aeval_limbPolyQ, laneBits, horner_range]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [Function.comp_apply, ev_scale, ypow, ev_chal, cv, CoeffExpr.eval,
    R.chalPow i hi t (by have := Finset.mem_range.mp ht; omega), hal.val i hi]
  rw [liftQ_val]

/-- **The packed chain evaluates the mirror** (`H` along an `mQ1` run). -/
theorem chainP : ∀ m i f, R.Run i m → (∀ j < m, R.v (i + j) mQ1 = 1) → m ≤ f →
    aeval R.y (hpackP al f i) = (QE.var H).ev δ (R.eK i) (R.eF i)
  | 0, _, _, r, _, _ => absurd r.pos (by omega)
  | m + 1, i, f, r, hq1, hf => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hi : i < R.n := by have := r.lt; omega
    have h1 : R.v i mQ1 = 1 := by simpa using hq1 0 (by omega)
    simp only [Rows.v] at h1
    by_cases hm : m = 0
    · subst hm
      have he : R.v i eos = 1 := by simpa using r.eos1
      have g := R.QZ hi (mem_identQ (e := qz (.mul (cv mQ1) (cv eos)) (QE.var H) packE) (by simp [identQ]))
        (by simp only [CoeffExpr.eval, cv, h1]; simpa using he)
      simp only [hpackP, onb_true hal hi he, if_true]
      rw [g, packE_ev hal hi]
    · have he : R.v i eos = 0 := by simpa using r.eos0 0 (by omega)
      have rt := Rows.Run.tail R r (by omega)
      rw [Nat.add_sub_cancel] at rt
      have hn : i + 1 < R.n := by have := r.lt; omega
      have ih := chainP m (i + 1) f' rt
        (fun j hj => by rw [show i + 1 + j = i + (j + 1) by omega]; exact hq1 (j + 1) (by omega)) (by omega)
      have g := R.QZ hi (mem_identQ (e := qz (.mul (cv mQ1) (notE (cv eos))) (QE.var H)
          (QE.add packE (QE.mul δ (ypow 32) (QE.next H)))) (by simp [identQ]))
        (by simp only [CoeffExpr.eval, notE, cv, h1]; simp only [Rows.v] at he; rw [he]; ring)
      rw [ev_add, ev_mul, ypow, ev_chal, R.chalPow i hi 32 le_rfl, ev_next, R.nextK i hn H,
        R.nextK i hn (H + 1), ← ev_var, packE_ev hal hi] at g
      simp only [hpackP, onb_zero hal hi he, Bool.false_eq_true, if_false, map_add, map_mul, map_pow, aeval_X, ih]
      exact g.symm

end Chains

/-! ## 3. Reads, slots and the per-row mirror -/

/-- **A served validity read, read** (`AluSZRead`'s `fp_read_sound` conclusion, at the ALU's `y`): the key's serial `v`
names a canonical big limb list `l` of the atom table with `L = horner y l`. -/
def ReadOK (y : 𝕂′) (r : ℕ → AtomChipHQ.ARow) (Lv : 𝕂′) (v : ℕ) : Prop :=
  ∃ l : List ℕ, AtomChipHQ.Denotes r v l ∧ Nock.Atoms.p ≤ val l ∧ Canonical l ∧ Lv = G5J8.horner y l ∧
    AtomBigJ8.extB Nock.Atoms.p r v = some (.atom (val l))

/-- **The context of a call**: the window, `AluSZEvent`'s readouts (ALU rows `al`, atom table `t`), the atom table's ℕ
reading `r`, the atom walk faithful to `r` on denoted rows, and every validity read served. -/
structure Ctx (R : Rows δ K) where
  al : List ALRow
  hal : Readout R al
  t : List (CellRowB0 Nock.Atoms.p)
  r : ℕ → AtomChipHQ.ARow
  walk : ∀ v l, AtomChipHQ.Denotes r v l → atomPoly t v = limbPolyQ l
  read : ∀ i < R.n, R.v i aV = 1 → ReadOK R.y r ((QE.var L).ev δ (R.eK i) (R.eF i)) (R.v i sv).val

namespace Ctx
variable [Algebra Fp (Quad (algebraMap Fp K δ))] {R : Rows δ K} (X : Ctx R)

theorem QZne {i : ℕ} (hi : i < R.n) {σ : CoeffExpr Fp} {a b : QE Fp} (he : qz σ a b ∈ aluQ δ)
    (hσ : σ.eval (R.eF i) ≠ 0) : a.ev δ (R.eK i) (R.eF i) = b.ev δ (R.eK i) (R.eF i) := by
  have := R.Q0 hi he
  simp only [qz, ev_scale, ev_sub] at this
  rcases mul_eq_zero.mp this with h | h
  · exact absurd ((map_eq_zero_iff _ (algebraMap Fp K).injective).mp
      ((map_eq_zero_iff (algebraMap K 𝕂′) (algebraMap K 𝕂′).injective).mp h)) hσ
  · exact sub_eq_zero.mp h

/-- Some mode is `1` on a lane row. -/
theorem mode_some {i : ℕ} (hi : i < R.n) (hL : R.v i sL = 1) : ∃ c ∈ modeCols, R.v i c = 1 := by
  by_contra hc
  push_neg at hc
  have hs := modes_sum (R.gates i hi)
  have h0 : ∀ c ∈ modeCols, R.v i c = 0 := fun c hc' => (R.b_mode hi hc').resolve_right (hc c hc')
  simp only [Rows.v] at hL h0
  rw [hL, h0 mR (by simp [modeCols]), h0 mS (by simp [modeCols]), h0 mV (by simp [modeCols]),
    h0 mW (by simp [modeCols]), h0 mQ1 (by simp [modeCols]), h0 mQM (by simp [modeCols])] at hs
  simp at hs

/-- The slot's Horner mode makes `hz = 1` along it. -/
theorem hz_slot {i m : ℕ} (s : R.Slot i m) {md : ℕ} (hmd : md ∈ [mS, mV, mW, mQM]) (h1 : R.v i md = 1) :
    ∀ j < m, (hz : CoeffExpr Fp).eval (R.eF (i + j)) = 1 := by
  intro j hj
  have hl := s.lane j hj
  have hs := s.same j hj md (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmd
    rcases hmd with rfl | rfl | rfl | rfl <;> simp [roleCols, modeCols])
  exact (hz_one hqFp (R.gates (i + j) (by have := s.lt; omega)) hl hmd
    (by simp only [Rows.v] at hs h1 ⊢; rw [hs]; exact h1)).1

theorem Hp_ev {i m : ℕ} (s : R.Slot i m) {md : ℕ} (hmd : md ∈ [mS, mV, mW, mQM]) (h1 : R.v i md = 1) :
    aeval R.y (Hp X.al i) = (QE.var H).ev δ (R.eK i) (R.eF i) :=
  chainH X.hal (mem_identQ (by simp [identQ])) (mem_identQ (by simp [identQ])) (fun i hi => laneL_cast X.hal hi)
    m i _ s.toRun (hz_slot s hmd h1) (by have := s.lt; rw [X.hal.len]; omega)

theorem HOp_ev {i m : ℕ} (s : R.Slot i m) {md : ℕ} (hmd : md ∈ [mS, mV, mW, mQM]) (h1 : R.v i md = 1) :
    aeval R.y (HOp X.al i) = (QE.var HO).ev δ (R.eK i) (R.eF i) :=
  chainH X.hal (mem_identQ (by simp [identQ])) (mem_identQ (by simp [identQ])) (fun i hi => laneO_cast X.hal hi)
    m i _ s.toRun (hz_slot s hmd h1) (by have := s.lt; rw [X.hal.len]; omega)

theorem Hp_poly {i m : ℕ} (s : R.Slot i m) : Hp X.al i = limbPolyQ (lanes (laneL X.al) i m) :=
  hornerP_run X.hal _ m i _ s.toRun (by have := s.lt; rw [X.hal.len]; omega)

theorem HOp_poly {i m : ℕ} (s : R.Slot i m) : HOp X.al i = limbPolyQ (lanes (laneO X.al) i m) :=
  hornerP_run X.hal _ m i _ s.toRun (by have := s.lt; rw [X.hal.len]; omega)

theorem pack_poly {i m : ℕ} (s : R.Slot i m) : hpackP X.al X.al.length i = limbPolyQ (packL X.al i m) :=
  hpackP_run X.hal m i _ s.toRun (by have := s.lt; rw [X.hal.len]; omega)

/-- `ev` of `y − B`. -/
theorem yMB_ev {i : ℕ} (hi : i < R.n) : (yMB : QE Fp).ev δ (R.eK i) (R.eF i) = R.y - 2 ^ 32 := by
  rw [yMB, ev_sub, yQ, ev_chal, R.chalY i hi, ev_base]
  simp [CoeffExpr.eval, Bf, liftQ, map_ofNat]

theorem aeval_BX : aeval R.y (BX : (ZMod Nock.Atoms.p)[X]) = R.y - 2 ^ 32 := by
  simp [BX, map_ofNat]

/-- The mode flags at a lane row with mode `c`. -/
theorem onb_modes {i : ℕ} (hi : i < R.n) (hL : R.v i sL = 1) {c : ℕ} (hc : c ∈ modeCols) (h1 : R.v i c = 1) :
    ∀ d ∈ modeCols, onb X.al i d = decide (d = c) := by
  intro d hd
  by_cases hdc : d = c
  · subst hdc; rw [onb_true X.hal hi h1]; simp
  · rw [onb_zero X.hal hi (R.mode_onehot hi hL hc h1 d hd hdc)]; simp [hdc]

/-- **`L` at a slot's first row is the mirror `Lp`** (every mode; reads served). -/
theorem Lp_ev {i m : ℕ} (s : R.Slot i m) :
    aeval R.y (Lp X.al X.t i) = (QE.var L).ev δ (R.eK i) (R.eF i) ∧
      (R.v i mR = 1 ∨ R.v i mS = 1 ∨ R.v i mV = 1 ∨ R.v i mW = 1 →
        aeval R.y (Lf X.al X.t i) = (QE.var L).ev δ (R.eK i) (R.eF i)) := by
  have hi : i < R.n := by have := s.lt; omega
  have hL := s.lane 0 (by have := s.pos; omega)
  rw [Nat.add_zero] at hL
  have hf := s.fst0
  obtain ⟨c, hc, h1⟩ := mode_some hi hL
  have ob := X.onb_modes hi hL hc h1
  have hcases : c = mR ∨ c = mS ∨ c = mV ∨ c = mW ∨ c = mQ1 ∨ c = mQM := by
    simp only [modeCols, List.mem_cons, List.mem_nil_iff, or_false] at hc; exact hc
  have hm0 : ∀ d ∈ modeCols, d ≠ c → (R.eF i).trace d = 0 := R.mode_onehot hi hL hc h1
  -- the atom read on `mR` / `mV`
  have hread : c = mR ∨ c = mV → aeval R.y (atomPoly X.t (cl X.al i sv).val) = (QE.var L).ev δ (R.eK i) (R.eF i) := by
    intro hcv
    have haV : R.v i aV = 1 := by
      have g := R.G hi (mem_flag (a := ar (.sub (cv aV) (.mul (cv fst) (sumC [mR, mV])))) (by simp [gFlag]))
      simp only [AG.gate, ar, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero] at g
      simp only [Rows.v] at hf h1 ⊢
      rcases hcv with rfl | rfl
      · rw [hf, h1, hm0 mV (by simp [modeCols]) (by decide)] at g; linear_combination g
      · rw [hf, h1, hm0 mR (by simp [modeCols]) (by decide)] at g; linear_combination g
    obtain ⟨l, hl, -, -, hLv, -⟩ := X.read i hi haV
    rw [X.hal.val i hi, X.walk _ l hl, aeval_limbPolyQ, ← hLv]
  -- `L = H` on `mS mV mW`
  have hLH : c = mS ∨ c = mV ∨ c = mW →
      (QE.var L).ev δ (R.eK i) (R.eF i) = (QE.var H).ev δ (R.eK i) (R.eF i) := by
    intro hc'
    refine R.QZ hi (mem_identQ (e := qz (.mul (cv fst) hzV) (QE.var L) (QE.var H)) (by simp [identQ])) ?_
    simp only [hzV, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    simp only [Rows.v] at hf h1 hm0
    rcases hc' with rfl | rfl | rfl
    · rw [hf, h1, hm0 mV (by simp [modeCols]) (by decide), hm0 mW (by simp [modeCols]) (by decide)]; ring
    · rw [hf, h1, hm0 mS (by simp [modeCols]) (by decide), hm0 mW (by simp [modeCols]) (by decide)]; ring
    · rw [hf, h1, hm0 mS (by simp [modeCols]) (by decide), hm0 mV (by simp [modeCols]) (by decide)]; ring
  -- `L = (y − B)·H` on Q blocks
  have hLQ : c = mQ1 ∨ c = mQM →
      (QE.var L).ev δ (R.eK i) (R.eF i) = (R.y - 2 ^ 32) * (QE.var H).ev δ (R.eK i) (R.eF i) := by
    intro hc'
    have g := R.QZ hi (mem_identQ (e := qz (.mul (cv fst) (sumC [mQ1, mQM])) (QE.var L) (QE.mul δ yMB (QE.var H))) (by simp [identQ])) (by
      simp only [sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
      simp only [Rows.v] at hf h1 hm0
      rcases hc' with rfl | rfl
      · rw [hf, h1, hm0 mQM (by simp [modeCols]) (by decide)]; ring
      · rw [hf, h1, hm0 mQ1 (by simp [modeCols]) (by decide)]; ring)
    rw [g, ev_mul, yMB_ev hi]
  have hmd : ∀ {md}, md ∈ [mS, mV, mW, mQM] → c = md → aeval R.y (Hp X.al i) = (QE.var H).ev δ (R.eK i) (R.eF i) :=
    fun hmd hc' => X.Hp_ev s hmd (hc' ▸ h1)
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · have e : Lp X.al X.t i = atomPoly X.t (cl X.al i sv).val := by
      simp [Lp, ob mR (by simp [modeCols])]
        <;> simp [mR, mS, mV, mW, mQ1, mQM]
    have e' : Lf X.al X.t i = atomPoly X.t (cl X.al i sv).val := by
      simp [Lf, ob mR (by simp [modeCols])]
        <;> simp [mR, mS, mV, mW, mQ1, mQM]
    exact ⟨by rw [e]; exact hread (Or.inl rfl), fun _ => by rw [e']; exact hread (Or.inl rfl)⟩
  · have e : Lp X.al X.t i = Hp X.al i := by
      simp [Lp, ob mR (by simp [modeCols]), ob mV (by simp [modeCols]), ob mQ1 (by simp [modeCols]),
        ob mQM (by simp [modeCols]), ob mS (by simp [modeCols])]
        <;> simp [mR, mS, mV, mW, mQ1, mQM]
    have e' : Lf X.al X.t i = Hp X.al i := by
      simp [Lf, ob mR (by simp [modeCols]), ob mV (by simp [modeCols]), ob mS (by simp [modeCols])]
        <;> simp [mR, mS, mV, mW, mQ1, mQM]
    have := hmd (md := mS) (by simp) rfl
    exact ⟨by rw [e, this, hLH (Or.inl rfl)], fun _ => by rw [e', this, hLH (Or.inl rfl)]⟩
  · have e : Lp X.al X.t i = atomPoly X.t (cl X.al i sv).val := by
      simp [Lp, ob mV (by simp [modeCols])]
        <;> simp [mR, mS, mV, mW, mQ1, mQM]
    have e' : Lf X.al X.t i = atomPoly X.t (cl X.al i sv).val := by
      simp [Lf, ob mV (by simp [modeCols])]
        <;> simp [mR, mS, mV, mW, mQ1, mQM]
    exact ⟨by rw [e]; exact hread (Or.inr rfl), fun _ => by rw [e']; exact hread (Or.inr rfl)⟩
  · have e : Lp X.al X.t i = Hp X.al i := by
      simp [Lp, ob mR (by simp [modeCols]), ob mV (by simp [modeCols]), ob mQ1 (by simp [modeCols]),
        ob mQM (by simp [modeCols]), ob mS (by simp [modeCols]), ob mW (by simp [modeCols])]
        <;> simp [mR, mS, mV, mW, mQ1, mQM]
    have e' : Lf X.al X.t i = Hp X.al i := by
      simp [Lf, ob mR (by simp [modeCols]), ob mV (by simp [modeCols]), ob mS (by simp [modeCols]),
        ob mW (by simp [modeCols])]
        <;> simp [mR, mS, mV, mW, mQ1, mQM]
    have := hmd (md := mW) (by simp) rfl
    exact ⟨by rw [e, this, hLH (Or.inr (Or.inr rfl))], fun _ => by rw [e', this, hLH (Or.inr (Or.inr rfl))]⟩
  · have e : Lp X.al X.t i = BX * hpackP X.al X.al.length i := by
      simp [Lp, ob mR (by simp [modeCols]), ob mV (by simp [modeCols]), ob mQ1 (by simp [modeCols])]
        <;> simp [mR, mS, mV, mW, mQ1, mQM]
    have hq1 : ∀ j < m, R.v (i + j) mQ1 = 1 := fun j hj => by
      rw [s.same j hj mQ1 (by simp [modeCols])]; exact h1
    have hP := chainP X.hal m i X.al.length s.toRun hq1 (by have := s.lt; rw [X.hal.len]; omega)
    refine ⟨by rw [e, map_mul, aeval_BX, hP, hLQ (Or.inl rfl)], fun h => ?_⟩
    exfalso
    have hz' := fun d hd hdc => hm0 d hd hdc
    simp only [Rows.v] at h hz' h1
    rcases h with h | h | h | h <;>
      (rw [hz' _ (by simp [modeCols]) (by decide)] at h; exact zero_ne_one h)
  · have e : Lp X.al X.t i = BX * Hp X.al i := by
      simp [Lp, ob mR (by simp [modeCols]), ob mV (by simp [modeCols]), ob mQ1 (by simp [modeCols]),
        ob mQM (by simp [modeCols])]
        <;> simp [mR, mS, mV, mW, mQ1, mQM]
    have := hmd (md := mQM) (by simp) rfl
    refine ⟨by rw [e, map_mul, aeval_BX, this, hLQ (Or.inr rfl)], fun h => ?_⟩
    exfalso
    have hz' := fun d hd hdc => hm0 d hd hdc
    simp only [Rows.v] at h hz' h1
    rcases h with h | h | h | h <;>
      (rw [hz' _ (by simp [modeCols]) (by decide)] at h; exact zero_ne_one h)

/-! ### The contributions `D1`, `D2` row by row -/

theorem D_hdr {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) :
    aeval R.y (D1p X.al X.t h) = (QE.var D1).ev δ (R.eK h) (R.eF h) ∧
      aeval R.y (D2p X.al X.t h) = (QE.var D2).ev δ (R.eK h) (R.eF h) := by
  have o := onb_true X.hal hh hH
  have g1 := R.QZ hh (mem_identQ (e := qz (cv sH) (QE.var D1) (QE.base (.mul (cv oLt) (notE (cv lb)))))
    (by simp [identQ])) (by simp only [CoeffExpr.eval, cv]; exact hH)
  have g2 := R.QZ hh (mem_identQ (e := qz (cv sH) (QE.var D2) (QE.base (sumC [oDiv, oMod]))) (by simp [identQ]))
    (by simp only [CoeffExpr.eval, cv]; exact hH)
  rw [ev_base] at g1 g2
  simp only [D1p, D2p, o, if_true, aeval_C_Fp, X.hal.val h hh, g1, g2]
  simp [CoeffExpr.eval, notE, cv, sumC, CoeffExpr.eval_sumList]

theorem D_inner {i : ℕ} (hi : i < R.n) (hL : R.v i sL = 1) (hf : R.v i fst = 0) :
    D1p X.al X.t i = 0 ∧ D2p X.al X.t i = 0 ∧ (QE.var D1).ev δ (R.eK i) (R.eF i) = 0 ∧
      (QE.var D2).ev δ (R.eK i) (R.eF i) = 0 := by
  have oH := onb_zero X.hal hi (R.lane_sH hi hL)
  have oF := onb_zero X.hal hi hf
  have hσ : (CoeffExpr.mul (cv sL) (notE (cv fst)) : CoeffExpr Fp).eval (R.eF i) = 1 := by
    simp only [CoeffExpr.eval, notE, cv]; simp only [Rows.v] at hL hf; rw [hL, hf]; ring
  have g1 := R.Q0 hi (mem_identQ (e := QE.scale (.mul (cv sL) (notE (cv fst))) (QE.var D1)) (by simp [identQ]))
  have g2 := R.Q0 hi (mem_identQ (e := QE.scale (.mul (cv sL) (notE (cv fst))) (QE.var D2)) (by simp [identQ]))
  rw [ev_scale, hσ] at g1 g2
  simp only [liftQ, map_one, one_mul] at g1 g2
  exact ⟨by simp [D1p, oH, oF], by simp [D2p, oH, oF], g1, g2⟩

/-- **A first row whose `f2` flag is not `1`**: `D1 = cf1·L`, `D2 = cf2·L`, mirrored by `C cf · Lp`. -/
theorem D_first {i m : ℕ} (s : R.Slot i m) (hf2 : R.v i f2 ≠ 1) :
    D1p X.al X.t i = C (R.v i cf1) * Lp X.al X.t i ∧ D2p X.al X.t i = C (R.v i cf2) * Lp X.al X.t i ∧
      aeval R.y (D1p X.al X.t i) = (QE.var D1).ev δ (R.eK i) (R.eF i) ∧
      aeval R.y (D2p X.al X.t i) = (QE.var D2).ev δ (R.eK i) (R.eF i) := by
  have hi : i < R.n := by have := s.lt; omega
  have hL := s.lane 0 (by have := s.pos; omega)
  rw [Nat.add_zero] at hL
  have oH := onb_zero X.hal hi (R.lane_sH hi hL)
  have oF := onb_true X.hal hi s.fst0
  have o2 := onb_false X.hal hi hf2
  have e1 : D1p X.al X.t i = C (R.v i cf1) * Lp X.al X.t i := by
    simp [D1p, oH, oF, o2, X.hal.val i hi]
  have e2 : D2p X.al X.t i = C (R.v i cf2) * Lp X.al X.t i := by
    simp [D2p, oH, oF, X.hal.val i hi]
  have hLp := (X.Lp_ev s).1
  have g1 := QZne hi (mem_identQ (e := qz (.mul (cv fst) (notE (cv f2))) (QE.var D1) (QE.scale (cv cf1) (QE.var L)))
    (by simp [identQ])) (by
      simp only [CoeffExpr.eval, notE, cv]; have := s.fst0; simp only [Rows.v] at this hf2; rw [this, one_mul]
      exact sub_ne_zero.mpr (Ne.symm hf2))
  have g2 := R.QZ hi (mem_identQ (e := qz (cv fst) (QE.var D2) (QE.scale (cv cf2) (QE.var L))) (by simp [identQ]))
    (by simp only [CoeffExpr.eval, cv]; exact s.fst0)
  rw [ev_scale] at g1 g2
  refine ⟨e1, e2, ?_, ?_⟩
  · rw [e1, map_mul, aeval_C_Fp, hLp, g1]; rfl
  · rw [e2, map_mul, aeval_C_Fp, hLp, g2]; rfl

/-! ### The block -/

omit X in
theorem blockSum_eq (al : List ALRow) (D : ℕ → (ZMod Nock.Atoms.p)[X]) : ∀ k f i,
    (∀ j, 1 ≤ j → j ≤ k → onb al (i + j) sL = true) → onb al (i + k + 1) sL = false → k < f →
      blockSum al D f i = ∑ j ∈ Finset.range (k + 1), D (i + j)
  | k, 0, _, _, _, hf => absurd hf (by omega)
  | 0, f + 1, i, _, h0, _ => by simp [blockSum, h0]
  | k + 1, f + 1, i, hl, h0, hf => by
    have h1 : onb al (i + 1) sL = true := by simpa using hl 1 le_rfl (by omega)
    rw [blockSum, if_pos h1, blockSum_eq al D k f (i + 1)
      (fun j hj1 hj2 => by rw [show i + 1 + j = i + (j + 1) by omega]; exact hl _ (by omega) (by omega))
      (by rw [show i + 1 + k + 1 = i + (k + 1) + 1 by omega]; exact h0) (by omega),
      Finset.sum_range_succ' _ (k + 1)]
    simp only [Nat.add_zero]
    rw [add_comm]
    exact congrArg₂ _ (Finset.sum_congr rfl fun j _ => by rw [show i + 1 + j = i + (j + 1) by omega]) rfl

omit X in
theorem blockRows_eq (al : List ALRow) : ∀ k f i,
    (∀ j, 1 ≤ j → j ≤ k → onb al (i + j) sL = true) → onb al (i + k + 1) sL = false → k < f →
      blockRows al f i = (List.range k).map (fun j => i + 1 + j)
  | k, 0, _, _, _, hf => absurd hf (by omega)
  | 0, f + 1, i, _, h0, _ => by simp [blockRows, h0]
  | k + 1, f + 1, i, hl, h0, hf => by
    have h1 : onb al (i + 1) sL = true := by simpa using hl 1 le_rfl (by omega)
    rw [blockRows, if_pos h1, blockRows_eq al k f (i + 1)
      (fun j hj1 hj2 => by rw [show i + 1 + j = i + (j + 1) by omega]; exact hl _ (by omega) (by omega))
      (by rw [show i + 1 + k + 1 = i + (k + 1) + 1 by omega]; exact h0) (by omega), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply]; omega

theorem onbs {h k : ℕ} (b : R.Block h k) :
    (∀ j, 1 ≤ j → j ≤ k → onb X.al (h + j) sL = true) ∧ onb X.al (h + k + 1) sL = false ∧ k < X.al.length := by
  refine ⟨fun j h1 h2 => onb_true X.hal (by have := b.lt; omega) (b.lane j h1 h2),
    onb_zero X.hal b.lt b.stop, by rw [X.hal.len]; have := b.lt; omega⟩

omit X in
theorem tele_aux {M : Type} [AddCommMonoid M] (S f : ℕ → M) (k : ℕ) (h0 : S 0 = f 0)
    (hs : ∀ j < k, S (j + 1) = S j + f (j + 1)) : ∀ j ≤ k, S j = ∑ l ∈ Finset.range (j + 1), f l := by
  intro j
  induction j with
  | zero => intro _; rw [Finset.sum_range_one]; exact h0
  | succ j ih => intro hj; rw [hs j (by omega), ih (by omega), Finset.sum_range_succ _ (j + 1)]

/-- The `qSum` telescope: `S(h + j) = Σ_{l ≤ j} D(h + l)`, and `S = 0` at the block's last row. -/
theorem telescope {h k : ℕ} (b : R.Block h k) {Sc Dc : ℕ}
    (h0 : qz (cv sH) (QE.var Sc) (QE.var Dc) ∈ aluQ δ)
    (hs : qz (.mul (notE (cv isLT)) (nv sL)) (QE.next Sc) (QE.add (QE.var Sc) (QE.next Dc)) ∈ aluQ δ)
    (he : QE.scale (notE (nv sL)) (QE.var Sc) ∈ aluQ δ) :
    ∑ j ∈ Finset.range (k + 1), (QE.var Dc).ev δ (R.eK (h + j)) (R.eF (h + j)) = 0 := by
  have hlt := b.lt
  have e0 : (QE.var Sc).ev δ (R.eK (h + 0)) (R.eF (h + 0)) = (QE.var Dc).ev δ (R.eK (h + 0)) (R.eF (h + 0)) :=
    R.QZ (i := h + 0) (by omega) h0 (by simp only [CoeffExpr.eval, cv]; exact b.hdr)
  have es : ∀ j < k, (QE.var Sc).ev δ (R.eK (h + (j + 1))) (R.eF (h + (j + 1))) =
      (QE.var Sc).ev δ (R.eK (h + j)) (R.eF (h + j)) + (QE.var Dc).ev δ (R.eK (h + (j + 1))) (R.eF (h + (j + 1))) := by
    intro j hj
    have hn : h + j + 1 < R.n := by omega
    have hL := b.lane (j + 1) (by omega) (by omega)
    have g := R.QZ (i := h + j) (by omega) hs (by
      simp only [CoeffExpr.eval, nv, notE, cv, R.nextF _ hn, R.notLast _ hn]
      rw [show h + j + 1 = h + (j + 1) by omega]; simp only [Rows.v] at hL; rw [hL]; ring)
    rw [ev_next, ev_add, ev_next, R.nextK _ hn, R.nextK _ hn, R.nextK _ hn, R.nextK _ hn, ← ev_var, ← ev_var,
      show h + j + 1 = h + (j + 1) by omega] at g
    exact g
  have hS := tele_aux (fun j => (QE.var Sc).ev δ (R.eK (h + j)) (R.eF (h + j)))
    (fun j => (QE.var Dc).ev δ (R.eK (h + j)) (R.eF (h + j))) k e0 es k le_rfl
  rw [← hS]
  have hn : h + k + 1 < R.n := b.lt
  have g := R.Q0 (i := h + k) (by omega) he
  rw [ev_scale] at g
  simp only [CoeffExpr.eval, notE, nv, R.nextF _ hn] at g
  have := b.stop; simp only [Rows.v] at this
  rw [this, sub_zero] at g
  simpa [liftQ] using g

/-- **The premise of `outside_arithSZ` from one call block's gates**: given the per-row mirror
facts, every polynomial of the call vanishes at `y`. -/
theorem premise {h k : ℕ} (b : R.Block h k)
    (hD1 : ∀ j ≤ k, aeval R.y (D1p X.al X.t (h + j)) = (QE.var D1).ev δ (R.eK (h + j)) (R.eF (h + j)))
    (hD2 : ∀ j ≤ k, aeval R.y (D2p X.al X.t (h + j)) = (QE.var D2).ev δ (R.eK (h + j)) (R.eF (h + j)))
    (hlink : ∀ j, 1 ≤ j → j ≤ k → aeval R.y (linkP X.al X.t (h + j)) = 0) :
    ∀ P ∈ callPolys X.al X.t h, aeval R.y P = 0 := by
  obtain ⟨o1, o2, o3⟩ := X.onbs b
  intro P hP
  simp only [callPolys, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_map] at hP
  rcases hP with (rfl | rfl) | ⟨j, hj, rfl⟩
  · rw [blockSum_eq X.al _ k _ h o1 o2 o3, map_sum, Finset.sum_congr rfl fun j hj => hD1 j
      (by have := Finset.mem_range.mp hj; omega)]
    exact telescope b (Sc := S1) (Dc := D1) (by simp [aluQ, identQ]) (by simp [aluQ, identQ]) (by simp [aluQ, identQ])
  · rw [blockSum_eq X.al _ k _ h o1 o2 o3, map_sum, Finset.sum_congr rfl fun j hj => hD2 j
      (by have := Finset.mem_range.mp hj; omega)]
    exact telescope b (Sc := S2) (Dc := D2) (by simp [aluQ, identQ]) (by simp [aluQ, identQ]) (by simp [aluQ, identQ])
  · rw [blockRows_eq X.al k _ h o1 o2 o3] at hj
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hj
    have := hlink (l + 1) (by omega) (by have := List.mem_range.mp hl; omega)
    rwa [show h + 1 + l = h + (l + 1) by omega]

/-- The view link at a lane row vanishes at `y` (`L = H` on `mV` first rows, `L` the read). -/
theorem link_ev {i : ℕ} (hi : i < R.n) (hL : R.v i sL = 1) : aeval R.y (linkP X.al X.t i) = 0 := by
  by_cases hfv : R.v i fst = 1 ∧ R.v i mV = 1
  · obtain ⟨m, s⟩ := R.slot_of hi hL hfv.1
    have hLp := (X.Lp_ev s).2 (Or.inr (Or.inr (Or.inl hfv.2)))
    have hlf : Lf X.al X.t i = atomPoly X.t (cl X.al i sv).val := by
      simp [Lf, onb_true X.hal hi hfv.2]
        <;> simp [mR, mS, mV, mW, mQ1, mQM]
    have e : linkP X.al X.t i = Hp X.al i - atomPoly X.t (cl X.al i sv).val := by
      simp [linkP, onb_true X.hal hi hfv.1, onb_true X.hal hi hfv.2]
    have hH := X.Hp_ev s (md := mV) (by simp) hfv.2
    have hm0 := R.mode_onehot hi hL (c := mV) (by simp [modeCols]) hfv.2
    have hLH := R.QZ hi (mem_identQ (e := qz (.mul (cv fst) hzV) (QE.var L) (QE.var H)) (by simp [identQ])) (by
      simp only [hzV, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      simp only [Rows.v] at hfv hm0
      rw [hfv.1, hfv.2, hm0 mS (by simp [modeCols]) (by decide), hm0 mW (by simp [modeCols]) (by decide)]; ring)
    rw [e, map_sub, hH, ← hlf, hLp, hLH, sub_self]
  · have : (onb X.al i fst && onb X.al i mV) = false := by
      by_cases h1 : R.v i fst = 1
      · rw [onb_false X.hal hi (fun h2 => hfv ⟨h1, h2⟩)]; simp
      · rw [onb_false X.hal hi h1]; simp
    simp [linkP, this]

/-- **The per-row mirror on a block whose rows carry no `f2` flag**, plus the `f2` rows supplied. -/
theorem premise_of {h k : ℕ} (b : R.Block h k)
    (hf2 : ∀ j, 1 ≤ j → j ≤ k → R.v (h + j) fst = 1 → R.v (h + j) f2 = 1 →
      aeval R.y (D1p X.al X.t (h + j)) = (QE.var D1).ev δ (R.eK (h + j)) (R.eF (h + j))) :
    ∀ P ∈ callPolys X.al X.t h, aeval R.y P = 0 := by
  have hh : h < R.n := by have := b.lt; omega
  refine X.premise b (fun j hj => ?_) (fun j hj => ?_) (fun j h1 h2 => X.link_ev (by have := b.lt; omega)
    (b.lane j h1 h2))
  · rcases j with _ | j
    · simpa using (X.D_hdr hh b.hdr).1
    · have hi : h + (j + 1) < R.n := by have := b.lt; omega
      have hL := b.lane (j + 1) (by omega) hj
      rcases R.b_fst hi with hf | hf
      · rw [(X.D_inner hi hL hf).1, (X.D_inner hi hL hf).2.2.1, map_zero]
      · by_cases h2 : R.v (h + (j + 1)) f2 = 1
        · exact hf2 (j + 1) (by omega) hj hf h2
        · obtain ⟨m, s⟩ := R.slot_of hi hL hf
          exact (X.D_first s h2).2.2.1
  · rcases j with _ | j
    · simpa using (X.D_hdr hh b.hdr).2
    · have hi : h + (j + 1) < R.n := by have := b.lt; omega
      have hL := b.lane (j + 1) (by omega) hj
      rcases R.b_fst hi with hf | hf
      · rw [(X.D_inner hi hL hf).2.1, (X.D_inner hi hL hf).2.2.2, map_zero]
      · by_cases h2 : R.v (h + (j + 1)) f2 = 1
        · -- `D2` on an `f2` row is `cf2·L` (no special case)
          obtain ⟨m, s⟩ := R.slot_of hi hL hf
          have oH := onb_zero X.hal hi (R.lane_sH hi hL)
          have oF := onb_true X.hal hi hf
          have g2 := R.QZ hi (mem_identQ (e := qz (cv fst) (QE.var D2) (QE.scale (cv cf2) (QE.var L)))
            (by simp [identQ])) (by simp only [CoeffExpr.eval, cv]; exact hf)
          rw [ev_scale] at g2
          simp only [D2p, oH, oF, Bool.false_eq_true, if_false, if_true, map_mul, aeval_C_Fp, X.hal.val _ hi,
            (X.Lp_ev s).1, g2]
          rfl
        · obtain ⟨m, s⟩ := R.slot_of hi hL hf
          exact (X.D_first s h2).2.2.2

end Ctx

/-! ## 4. Slot values (the polynomial side) -/

namespace Ctx
variable [Algebra Fp (Quad (algebraMap Fp K δ))] {R : Rows δ K} (X : Ctx R)

/-- **`Lp` / `Lf` by mode** (the mirror's branches at a lane row). -/
theorem Lp_mode {i : ℕ} (hi : i < R.n) (hL : R.v i sL = 1) :
    (R.v i mR = 1 ∨ R.v i mV = 1 → Lp X.al X.t i = atomPoly X.t (R.v i sv).val ∧
      Lf X.al X.t i = atomPoly X.t (R.v i sv).val) ∧
    (R.v i mS = 1 ∨ R.v i mW = 1 → Lp X.al X.t i = Hp X.al i ∧ Lf X.al X.t i = Hp X.al i) ∧
    (R.v i mQ1 = 1 → Lp X.al X.t i = BX * hpackP X.al X.al.length i) ∧
    (R.v i mQM = 1 → Lp X.al X.t i = BX * Hp X.al i) := by
  have ob : ∀ {c}, c ∈ modeCols → R.v i c = 1 → ∀ d ∈ modeCols, onb X.al i d = decide (d = c) :=
    fun hc h1 => X.onb_modes hi hL hc h1
  have sv' : cl X.al i sv = R.v i sv := X.hal.val i hi sv
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rcases h with h | h
    · have o := ob (c := mR) (by simp [modeCols]) h
      exact ⟨by simp [Lp, o mR (by simp [modeCols]), sv'], by simp [Lf, o mR (by simp [modeCols]), sv']⟩
    · have o := ob (c := mV) (by simp [modeCols]) h
      exact ⟨by simp [Lp, o mR (by simp [modeCols]), o mV (by simp [modeCols]), sv'] <;> simp [mR, mV],
        by simp [Lf, o mR (by simp [modeCols]), o mV (by simp [modeCols]), sv'] <;> simp [mR, mV]⟩
  · rcases h with h | h
    · have o := ob (c := mS) (by simp [modeCols]) h
      exact ⟨by
          simp [Lp, o mR (by simp [modeCols]), o mV (by simp [modeCols]), o mQ1 (by simp [modeCols]),
            o mQM (by simp [modeCols]), o mS (by simp [modeCols])] <;> simp [mR, mS, mV, mW, mQ1, mQM],
        by simp [Lf, o mR (by simp [modeCols]), o mV (by simp [modeCols]), o mS (by simp [modeCols])]
          <;> simp [mR, mS, mV, mW, mQ1, mQM]⟩
    · have o := ob (c := mW) (by simp [modeCols]) h
      exact ⟨by
          simp [Lp, o mR (by simp [modeCols]), o mV (by simp [modeCols]), o mQ1 (by simp [modeCols]),
            o mQM (by simp [modeCols]), o mS (by simp [modeCols]), o mW (by simp [modeCols])]
            <;> simp [mR, mS, mV, mW, mQ1, mQM],
        by simp [Lf, o mR (by simp [modeCols]), o mV (by simp [modeCols]), o mS (by simp [modeCols]),
            o mW (by simp [modeCols])] <;> simp [mR, mS, mV, mW, mQ1, mQM]⟩
  · have o := ob (c := mQ1) (by simp [modeCols]) h
    simp [Lp, o mR (by simp [modeCols]), o mV (by simp [modeCols]), o mQ1 (by simp [modeCols])]
      <;> simp [mR, mS, mV, mW, mQ1, mQM]
  · have o := ob (c := mQM) (by simp [modeCols]) h
    simp [Lp, o mR (by simp [modeCols]), o mV (by simp [modeCols]), o mQ1 (by simp [modeCols]),
      o mQM (by simp [modeCols])] <;> simp [mR, mS, mV, mW, mQ1, mQM]

/-- **A split slot has length 2** (`gCompat`: `fst·mS·eos = 0`, `fst·mS·(1 − eos′) = 0`). -/
theorem split_len {i m : ℕ} (s : R.Slot i m) (h1 : R.v i mS = 1) : m = 2 := by
  have hi : i < R.n := by have := s.lt; omega
  have hf := s.fst0
  have ge0 := R.G hi (mem_compat (a := ar (prod3 (cv fst) (cv mS) (cv eos))) (by simp [gCompat]))
  simp only [AG.gate, ar, prod3, cv, CoeffExpr.eval] at ge0
  simp only [Rows.v] at hf h1
  rw [hf, h1, one_mul, one_mul] at ge0
  have hm2 : 2 ≤ m := by
    by_contra hc
    have := s.eos1; rw [show i + m - 1 = i by have := s.pos; omega] at this
    simp only [Rows.v] at this; rw [this] at ge0; exact one_ne_zero ge0
  have hn : i + 1 < R.n := by have := s.lt; omega
  have ge1 := R.G hi (mem_compat (a := ar (prod3 (cv fst) (cv mS) (notE (nv eos)))) (by simp [gCompat]))
  simp only [AG.gate, ar, prod3, notE, cv, nv, CoeffExpr.eval, R.nextF _ hn, hf, h1, one_mul] at ge1
  by_contra hc
  have := s.eos0 1 (by omega)
  simp only [Rows.v] at this; rw [this] at ge1; simp at ge1

/-- **A split slot's value** (`AluSZRead`'s `split_sound`): `sv.val = ℓ₀ + B·ℓ₁ < p`. -/
theorem split_val {i m : ℕ} (s : R.Slot i m) (h1 : R.v i mS = 1) :
    (R.v i sv).val = val (lanes (laneL X.al) i m) ∧ val (lanes (laneL X.al) i m) < Nock.Atoms.p := by
  have hm := split_len s h1
  subst hm
  have hi : i < R.n := by have := s.lt; omega
  have hn : i + 1 < R.n := by have := s.lt; omega
  obtain ⟨lo, hi', hlo, hhi, hv, hlt, hc0, hc1, -⟩ := split_sound (p := Nock.Atoms.p) (K := K) (δ := δ) rfl
    (R.eK i) (R.eK (i + 1)) (R.eF i) (R.eF (i + 1)) (R.gates i hi) (R.gates (i + 1) hn) (R.nextF i hn)
    (R.nextK i hn) (R.chalY i hi) (R.chalY (i + 1) hn) s.fst0 h1
  have e0 : laneL X.al i = lo := castFp_inj (by have := laneL_lt X.hal hi; rw [Nock.Atoms.B_eq] at this; omega)
    (by rw [Nock.Atoms.B_eq] at hlo; omega) (by rw [laneL_cast X.hal hi, hc0])
  have e1 : laneL X.al (i + 1) = hi' := castFp_inj (by have := laneL_lt X.hal hn; rw [Nock.Atoms.B_eq] at this; omega)
    (by rw [Nock.Atoms.B_eq] at hhi; omega) (by rw [laneL_cast X.hal hn, hc1])
  have hval : val (lanes (laneL X.al) i 2) = lo + B * hi' := by
    simp [lanes, val, Nat.ofDigits, e0, e1]
  rw [hval]; exact ⟨hv, hlt⟩

/-- **An operand (handle) slot** (`mR mS mV`): its limb list, the mirror's polynomial, and what its handle denotes. -/
theorem operand {i m : ℕ} (s : R.Slot i m) (hm : R.v i mR = 1 ∨ R.v i mS = 1 ∨ R.v i mV = 1) :
    ∃ l : List ℕ, Lp X.al X.t i = limbPolyQ l ∧ Lf X.al X.t i = limbPolyQ l ∧ (∀ x ∈ l, x < B) ∧
      ((R.v i sk = 2 ∧ AtomBigJ8.extB Nock.Atoms.p X.r (R.v i sv).val = some (.atom (val l)) ∧
          Nock.Atoms.p ≤ val l ∧ Canonical l ∧ AtomChipHQ.Denotes X.r (R.v i sv).val l) ∨
        (R.v i sk = 0 ∧ (R.v i sv).val = val l ∧ val l < Nock.Atoms.p)) := by
  have hi : i < R.n := by have := s.lt; omega
  have hL := s.lane 0 (by have := s.pos; omega)
  rw [Nat.add_zero] at hL
  have hf := s.fst0
  have md := X.Lp_mode hi hL
  rcases hm with h1 | h1 | h1
  · -- `mR`
    obtain ⟨e, e'⟩ := md.1 (Or.inl h1)
    have hm0 := R.mode_onehot hi hL (c := mR) (by simp [modeCols]) h1
    have haV : R.v i aV = 1 := by
      have g := R.G hi (mem_flag (a := ar (.sub (cv aV) (.mul (cv fst) (sumC [mR, mV])))) (by simp [gFlag]))
      have h0 := hm0 mV (by simp [modeCols]) (by decide)
      simp only [AG.gate, ar, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero] at g
      simp only [Rows.v] at hf h1 h0 ⊢; rw [hf, h1, h0] at g; linear_combination g
    obtain ⟨l, hl, hbig, hcan, -, hext⟩ := X.read i hi haV
    have hP := X.walk _ l hl
    have hsk : R.v i sk = 2 := by
      have g := R.G hi (Rows.mem_bind (a := ar (.mul (.mul (cv fst) (sumC [mR, mV])) (.sub (cv sk) (.const 2))))
        (by simp [gBind]))
      have h0 := hm0 mV (by simp [modeCols]) (by decide)
      simp only [AG.gate, ar, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero] at g
      simp only [Rows.v] at hf h1 h0 ⊢; rw [hf, h1, h0] at g; linear_combination g
    exact ⟨l, by rw [e, hP], by rw [e', hP], hcan.1, Or.inl ⟨hsk, hext, hbig, hcan, hl⟩⟩
  · -- `mS`
    obtain ⟨e, e'⟩ := md.2.1 (Or.inl h1)
    have hP := X.Hp_poly s
    obtain ⟨hv, hlt⟩ := X.split_val s h1
    have hsk : R.v i sk = 0 := by
      have g1 := R.G hi (mem_flag (a := ar (.sub (cv sf) (.mul (cv fst) (cv mS)))) (by simp [gFlag]))
      have g2 := R.G hi (Rows.mem_bind (a := ar (.mul (cv sf) (cv sk))) (by simp [gBind]))
      simp only [AG.gate, ar, CoeffExpr.eval, cv] at g1 g2
      simp only [Rows.v] at hf h1 ⊢; rw [hf, h1, one_mul] at g1
      rw [show (R.eF i).trace sf = 1 by linear_combination g1, one_mul] at g2; exact g2
    exact ⟨lanes (laneL X.al) i m, by rw [e, hP], by rw [e', hP],
      lanes_bound _ fun j hj => laneL_lt X.hal (by have := s.lt; omega), Or.inr ⟨hsk, hv, hlt⟩⟩
  · -- `mV`
    obtain ⟨e, e'⟩ := md.1 (Or.inr h1)
    have hm0 := R.mode_onehot hi hL (c := mV) (by simp [modeCols]) h1
    have haV : R.v i aV = 1 := by
      have g := R.G hi (mem_flag (a := ar (.sub (cv aV) (.mul (cv fst) (sumC [mR, mV])))) (by simp [gFlag]))
      have h0 := hm0 mR (by simp [modeCols]) (by decide)
      simp only [AG.gate, ar, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero] at g
      simp only [Rows.v] at hf h1 h0 ⊢; rw [hf, h1, h0] at g; linear_combination g
    obtain ⟨l, hl, hbig, hcan, -, hext⟩ := X.read i hi haV
    have hP := X.walk _ l hl
    have hsk : R.v i sk = 2 := by
      have g := R.G hi (Rows.mem_bind (a := ar (.mul (.mul (cv fst) (sumC [mR, mV])) (.sub (cv sk) (.const 2))))
        (by simp [gBind]))
      have h0 := hm0 mR (by simp [modeCols]) (by decide)
      simp only [AG.gate, ar, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero] at g
      simp only [Rows.v] at hf h1 h0 ⊢; rw [hf, h1, h0] at g; linear_combination g
    exact ⟨l, by rw [e, hP], by rw [e', hP], hcan.1, Or.inl ⟨hsk, hext, hbig, hcan, hl⟩⟩

/-- **A witness slot** (`mW`): its lanes. -/
theorem witness {i m : ℕ} (s : R.Slot i m) (h1 : R.v i mW = 1) :
    Lp X.al X.t i = limbPolyQ (lanes (laneL X.al) i m) ∧ Lf X.al X.t i = limbPolyQ (lanes (laneL X.al) i m) ∧
      ∀ x ∈ lanes (laneL X.al) i m, x < B := by
  have hi : i < R.n := by have := s.lt; omega
  have hL := s.lane 0 (by have := s.pos; omega)
  rw [Nat.add_zero] at hL
  obtain ⟨e, e'⟩ := (X.Lp_mode hi hL).2.1 (Or.inr h1)
  exact ⟨by rw [e, X.Hp_poly s], by rw [e', X.Hp_poly s],
    lanes_bound _ fun j hj => laneL_lt X.hal (by have := s.lt; omega)⟩

/-- **A packed `Q` slot** (`mQ1`): `Lp = (Y − B)·Q`, carries `≤ 1`. -/
theorem qslot1 {i m : ℕ} (s : R.Slot i m) (h1 : R.v i mQ1 = 1) :
    Lp X.al X.t i = BX * limbPolyQ (packL X.al i m) ∧ ∀ x ∈ packL X.al i m, x ≤ 1 := by
  have hi : i < R.n := by have := s.lt; omega
  have hL := s.lane 0 (by have := s.pos; omega)
  rw [Nat.add_zero] at hL
  refine ⟨by rw [(X.Lp_mode hi hL).2.2.1 h1, X.pack_poly s], fun x hx => ?_⟩
  obtain ⟨j, hj, hx⟩ := mem_packL X.al i m x hx
  exact laneBits_le X.hal (by have := s.lt; omega) x hx

/-! ### Small helpers for the per-op proofs -/

omit X in
theorem sum_shift {M : Type} [AddCommMonoid M] (D : ℕ → M) (a b c : ℕ) :
    ∑ j ∈ Finset.range (b + c), D (a + j) = ∑ j ∈ Finset.range b, D (a + j) + ∑ j ∈ Finset.range c, D (a + b + j) := by
  rw [Finset.sum_range_add]
  exact congrArg₂ _ rfl (Finset.sum_congr rfl fun j _ => by rw [Nat.add_assoc])

omit X in
theorem sum_head {M : Type} [AddCommMonoid M] (D : ℕ → M) (a k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), D (a + j) = D a + ∑ j ∈ Finset.range k, D (a + 1 + j) := by
  rw [Finset.sum_range_succ', add_comm]
  exact congrArg₂ _ (by simp) (Finset.sum_congr rfl fun j _ => by rw [show a + (j + 1) = a + 1 + j by omega])

/-- **A slot contributes only its first row** (`D = 0` on the inner lane rows). -/
theorem slot_sum {i m : ℕ} (s : R.Slot i m) {i' : ℕ} (he : i' = i) :
    ∑ j ∈ Finset.range m, D1p X.al X.t (i' + j) = D1p X.al X.t i ∧
      ∑ j ∈ Finset.range m, D2p X.al X.t (i' + j) = D2p X.al X.t i := by
  subst he
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := s.pos; omega⟩
  have hz : ∀ j < m', D1p X.al X.t (i' + (j + 1)) = 0 ∧ D2p X.al X.t (i' + (j + 1)) = 0 := by
    intro j hj
    have hi : i' + (j + 1) < R.n := by have := s.lt; omega
    have h := X.D_inner hi (s.lane (j + 1) (by omega)) (s.fst1 (j + 1) (by omega) (by omega))
    exact ⟨h.1, h.2.1⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.add_zero]
  rw [Finset.sum_eq_zero fun j hj => (hz j (Finset.mem_range.mp hj)).1,
    Finset.sum_eq_zero fun j hj => (hz j (Finset.mem_range.mp hj)).2, zero_add, zero_add]
  exact ⟨rfl, rfl⟩

/-- The coefficient gate at a slot's first row: `c = e` where `fst·r·(c − e) = 0`, `r = 1`. -/
theorem coef_val {i m : ℕ} (s : R.Slot i m) {r c : ℕ} {e : CoeffExpr Fp} (hr : R.v i r = 1)
    (hg : coef r c e ∈ gCoef) : R.v i c = e.eval (R.eF i) := by
  have hi : i < R.n := by have := s.lt; omega
  have g := R.G hi (Rows.mem_coef hg)
  have hf := s.fst0
  simp only [AG.gate, coef, ar, prod3, cv, CoeffExpr.eval] at g
  simp only [Rows.v] at hf hr ⊢; rw [hf, hr, one_mul, one_mul] at g; exact sub_eq_zero.mp g

/-- The hdr's op flags are one-hot. -/
theorem ops_hdr {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) {c : ℕ} (hc : c ∈ opCols) (h1 : R.v h c = 1) :
    ∀ d ∈ opCols, d ≠ c → R.v h d = 0 := by
  have g := R.G hh (mem_kind (a := ar (.mul (cv sH) (.sub (sumC opCols) (.const 1)))) (by simp [gKind]))
  simp only [AG.gate, ar, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv] at g
  simp only [Rows.v] at hH; rw [hH, one_mul] at g
  have := onehot (e := R.eF h) (l := opCols) (by simp [opCols]) (by decide) (fun j hj => R.b_op hh hj)
    (Or.inr (sub_eq_zero.mp g)) hc h1
  exact this.2

/-- `C (B : Fp) = −BX + X`. -/
theorem CB_eq : (Polynomial.C (B : Fp) : Fp[X]) = Polynomial.X - BX := by
  unfold BX B; push_cast; ring

/-! ### The block shape from the role sequence -/

omit X in
theorem step {h a i m : ℕ} (hhn : h < R.n) (hia : i = h + 1 + a)
    (hl : ∀ j, 1 ≤ j → j ≤ a → R.v (h + j) sL = 1) (s : R.Slot i m) {r : ℕ} (hr : r ∈ roleCols ++ modeCols)
    (hr1 : R.v i r = 1) {σ : CoeffExpr Fp} {t : ℕ} (hg : succ r σ t ∈ gSeq)
    (hσ : ∀ e : Env Fp, (∀ c ∈ Rows.constCols, e.trace c = R.v h c) → σ.eval e = 1)
    (ht : t ∈ roleCols ++ [mQ1, mQM]) :
    (∀ j, 1 ≤ j → j ≤ a + m → R.v (h + j) sL = 1) ∧ R.v (i + m) t = 1 ∧ ∃ m', R.Slot (i + m) m' := by
  subst hia
  have hl' : ∀ j, 1 ≤ j → j ≤ a + m → R.v (h + j) sL = 1 := by
    intro j h1 h2
    by_cases hj : j ≤ a
    · exact hl j h1 hj
    · have := s.lane (j - 1 - a) (by omega); rwa [show h + 1 + a + (j - 1 - a) = h + j by omega] at this
  have hc := R.const_run (h := h) (k := a + m) (by have := s.lt; omega) hl' (a + m) le_rfl
  have e1 : h + 1 + a + m - 1 = h + (a + m) := by have := s.pos; omega
  obtain ⟨ht1, hL, hf⟩ := R.after s hr hr1 hg (by rw [e1]; exact hσ _ hc) ht
  exact ⟨hl', ht1, R.slot_of (by have := s.lt; omega) hL hf⟩

omit X in
/-- **The 4-slot shapes** (`add sub`: `ra rb rc mQ1`; `lt`: `ra rb rd mQ1`). -/
theorem shape_q1 {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) {x : ℕ} (hx : x ∈ roleCols)
    {σ1 σ2 σ3 : CoeffExpr Fp} (g1 : succ ra σ1 rb ∈ gSeq) (g2 : succ rb σ2 x ∈ gSeq) (g3 : succ x σ3 mQ1 ∈ gSeq)
    (hσ : ∀ e : Env Fp, (∀ c ∈ Rows.constCols, e.trace c = R.v h c) →
      σ1.eval e = 1 ∧ σ2.eval e = 1 ∧ σ3.eval e = 1) :
    ∃ ma mb mc mq, R.Slot (h + 1) ma ∧ R.Slot (h + 1 + ma) mb ∧ R.Slot (h + 1 + ma + mb) mc ∧
      R.Slot (h + 1 + ma + mb + mc) mq ∧ R.v (h + 1) ra = 1 ∧ R.v (h + 1 + ma) rb = 1 ∧
      R.v (h + 1 + ma + mb) x = 1 ∧ R.v (h + 1 + ma + mb + mc) mQ1 = 1 ∧
      R.Block h (ma + mb + mc + mq) ∧ ∀ j ≤ ma + mb + mc + mq, ∀ c ∈ Rows.constCols, R.v (h + j) c = R.v h c := by
  obtain ⟨hn1, hra, hL1, hf1⟩ := R.after_hdr hh hH
  obtain ⟨ma, sa⟩ := R.slot_of hn1 hL1 hf1
  obtain ⟨l1, hrb, mb, sb⟩ := step (a := 0) hh rfl (fun j h1 h2 => by omega) sa (r := ra) (by simp [roleCols]) hra g1
    (fun e he => (hσ e he).1) (by simp [roleCols])
  obtain ⟨l2, hxx, mc, sc⟩ := step (a := ma) hh rfl (fun j h1 h2 => l1 j h1 (by omega)) sb (r := rb)
    (by simp [roleCols]) hrb g2 (fun e he => (hσ e he).2.1) (List.mem_append_left _ hx)
  obtain ⟨l3, hq, mq, sq⟩ := step (a := ma + mb) hh (by omega) (fun j h1 h2 => l2 j h1 h2) sc (r := x)
    (List.mem_append_left _ hx) hxx g3 (fun e he => (hσ e he).2.2) (by simp)
  -- the lanes of the whole block
  have hl : ∀ j, 1 ≤ j → j ≤ ma + mb + mc + mq → R.v (h + j) sL = 1 := by
    intro j h1 h2
    by_cases hj : j ≤ ma + mb + mc
    · exact l3 j h1 hj
    · have := sq.lane (j - 1 - (ma + mb + mc)) (by omega)
      rwa [show h + 1 + ma + mb + mc + (j - 1 - (ma + mb + mc)) = h + j by omega] at this
  -- the terminal `mQ1` block is followed by a non-lane row
  obtain ⟨hk, he, hL, hcq⟩ := Rows.Slot.lastRow R sq
  have hn := R.not_last hk (Or.inr hL)
  have g := R.G hk (Rows.mem_seq (a := ar (prod3 (cv eos) (cv mQ1) (nv sL))) (by simp [gSeq]))
  have hq' := hcq mQ1 (by simp [modeCols])
  simp only [AG.gate, ar, prod3, cv, nv, CoeffExpr.eval, R.nextF _ hn] at g
  simp only [Rows.v] at he hq' hq; rw [he, hq', hq, one_mul, one_mul] at g
  have e1 : h + 1 + ma + mb + mc + mq - 1 + 1 = h + (ma + mb + mc + mq) + 1 := by have := sq.pos; omega
  rw [e1] at g hn
  refine ⟨ma, mb, mc, mq, sa, sb, by simpa using sc, by simpa [Nat.add_assoc] using sq, hra, by simpa using hrb,
    by simpa [Nat.add_assoc] using hxx, by simpa [Nat.add_assoc] using hq,
    ⟨by rw [← Nat.add_assoc] at hn ⊢; omega, hH, hl, by simpa [Nat.add_assoc] using g⟩,
    R.const_run (by omega) hl⟩

/-- The op flags at any row carrying the hdr's constants. -/
theorem op_vals {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) {o : ℕ} (ho : o ∈ opCols) (h1 : R.v h o = 1)
    (e : Env Fp) (he : ∀ c ∈ Rows.constCols, e.trace c = R.v h c) : ∀ c ∈ opCols, e.trace c = if c = o then 1 else 0 := by
  intro c hc
  rw [he c (List.mem_append_left _ (List.mem_append_left _ hc))]
  by_cases hco : c = o
  · subst hco; simpa using h1
  · rw [if_neg hco]; exact ops_hdr hh hH ho h1 c hc hco

/-- The handle binding at a slot's first row (`gBind`). -/
theorem bind_val {i m : ℕ} (s : R.Slot i m) {σ : CoeffExpr Fp} {k v : ℕ} (hσ : σ.eval (R.eF i) = 1)
    (hb : AluSZChipJ9.bind σ k v ⊆ gBind) : R.v i sk = R.v i k ∧ R.v i sv = R.v i v := by
  have hi : i < R.n := by have := s.lt; omega
  have g1 := R.G hi (Rows.mem_bind (a := ar (.mul σ (.sub (cv sk) (cv k)))) (hb (by simp [AluSZChipJ9.bind])))
  have g2 := R.G hi (Rows.mem_bind (a := AG.cp ⟨σ, .cur sv, .cur v⟩) (hb (by simp [AluSZChipJ9.bind])))
  simp only [AG.gate, ar, CopyG.gate, Op.expr, cv, CoeffExpr.eval, hσ, one_mul] at g1 g2
  exact ⟨sub_eq_zero.mp g1, sub_eq_zero.mp g2⟩

/-- **A handle's denotation** (`(k, v)` with `k ∈ {0, 2}`): kind `0` names the small atom `v < p`, kind `2` the
canonical big atom (`≥ p`) of the atom table the serial denotes. -/
def HDen (r : ℕ → AtomChipHQ.ARow) (k v : Fp) (n : ℕ) : Prop :=
  (k = 0 ∧ v.val = n ∧ n < Nock.Atoms.p) ∨
    (k = 2 ∧ AtomBigJ8.extB Nock.Atoms.p r v.val = some (.atom n) ∧ Nock.Atoms.p ≤ n ∧
      ∃ l, Canonical l ∧ val l = n ∧ AtomChipHQ.Denotes r v.val l)

omit X in
/-- **What `HDen` gives the cell table's decoder**: `denK (k, v) = atom n` for every round-0 cell table. -/
theorem HDen.denK {r : ℕ → AtomChipHQ.ARow} {k v : Fp} {n : ℕ} (hd : HDen r k v n) {qc : ℕ}
    (tb : List (CellRowB0 qc)) : denK tb (AtomBigJ8.extB Nock.Atoms.p r) (k.val, v.val) = some (.atom n) := by
  rcases hd with ⟨rfl, hv, -⟩ | ⟨rfl, he, -⟩
  · rw [ZMod.val_zero, hv]; rfl
  · have : (2 : Fp).val = 2 := by
      rw [show (2 : Fp) = ((2 : ℕ) : Fp) by norm_num, ZMod.val_natCast]
      norm_num [Nock.Atoms.p, Nock.Field.p]
    rw [this]; exact he

/-- The operand slot's handle denotes its limb value. -/
theorem operand_den {i m : ℕ} (s : R.Slot i m) (hm : R.v i mR = 1 ∨ R.v i mS = 1 ∨ R.v i mV = 1)
    {kc vc : Fp} (hk : R.v i sk = kc) (hv : R.v i sv = vc) :
    ∃ l : List ℕ, Lp X.al X.t i = limbPolyQ l ∧ Lf X.al X.t i = limbPolyQ l ∧ (∀ x ∈ l, x < B) ∧
      HDen X.r kc vc (val l) := by
  obtain ⟨l, e, e', hb, hd⟩ := X.operand s hm
  refine ⟨l, e, e', hb, ?_⟩
  subst hk hv
  rcases hd with ⟨h2, he, hbig, hcan, hl⟩ | ⟨h0, hv, hlt⟩
  · exact Or.inr ⟨h2, he, hbig, l, hcan, rfl, hl⟩
  · exact Or.inl ⟨h0, hv, hlt⟩

/-! ### Per-op facts shared by the ops -/

/-- The block constants at any row of the block. -/
theorem cst_at {h K : ℕ} (hcst : ∀ j ≤ K, ∀ c ∈ Rows.constCols, R.v (h + j) c = R.v h c) {i : ℕ} (h1 : h ≤ i)
    (h2 : i ≤ h + K) : ∀ c ∈ Rows.constCols, (R.eF i).trace c = R.v h c := by
  have := hcst (i - h) (by omega); rwa [Nat.add_sub_cancel' h1] at this

theorem sel2 {i m : ℕ} (s : R.Slot i m) {r : ℕ} (hr : R.v i r = 1) :
    (CoeffExpr.mul (cv fst) (cv r) : CoeffExpr Fp).eval (R.eF i) = 1 := by
  simp only [CoeffExpr.eval, cv]; simp only [Rows.v] at hr
  rw [show (R.eF i).trace fst = 1 from s.fst0, hr, one_mul]

/-- `f2 = 0` on every row of a non-product block. -/
theorem f2_zero {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) {o : ℕ} (ho : o ∈ opCols) (h1 : R.v h o = 1)
    (hon : o = oAdd ∨ o = oSub ∨ o = oLt) {i : ℕ} (hi : i < R.n)
    (hc : ∀ c ∈ Rows.constCols, (R.eF i).trace c = R.v h c) : R.v i f2 ≠ 1 := by
  have v := op_vals hh hH ho h1 (R.eF i) hc
  have g := R.G hi (mem_flag (a := ar (.sub (cv f2) (prod3 (cv fst) (cv rb) (sumC [oMul, oDiv, oMod]))))
    (by simp [gFlag]))
  simp only [AG.gate, ar, prod3, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, v oMul (by simp [opCols]), v oDiv (by simp [opCols]),
    v oMod (by simp [opCols])] at g
  rcases hon with rfl | rfl | rfl <;> simp [oAdd, oSub, oLt, oMul, oDiv, oMod] at g <;>
    (simp only [Rows.v]; rw [g]; exact zero_ne_one)

/-- An `ra rb rc` slot reads a handle (`mR mS mV`): it is not `mW` (`gCompat`) nor a `Q` block. -/
theorem operand_mode {i m : ℕ} (s : R.Slot i m) {r : ℕ} (hr : r = ra ∨ r = rb ∨ r = rc) (h1 : R.v i r = 1) :
    R.v i mR = 1 ∨ R.v i mS = 1 ∨ R.v i mV = 1 := by
  have hi : i < R.n := by have := s.lt; omega
  have hrt : r ∈ roleCols ++ [mQ1, mQM] := by rcases hr with rfl | rfl | rfl <;> simp [roleCols]
  obtain ⟨hL, h0⟩ := R.tag_onehot hi hrt h1
  replace h0 : ∀ d ∈ roleCols ++ [mQ1, mQM], d ≠ r → (R.eF i).trace d = 0 := h0
  have hq1 := h0 mQ1 (by simp) (by rcases hr with rfl | rfl | rfl <;> decide)
  have hqm := h0 mQM (by simp) (by rcases hr with rfl | rfl | rfl <;> decide)
  have hsum : (R.eF i).trace ra + (R.eF i).trace rb + (R.eF i).trace rc = 1 := by
    rcases hr with rfl | rfl | rfl
    · rw [show (R.eF i).trace ra = 1 from h1, h0 rb (by simp [roleCols]) (by decide),
        h0 rc (by simp [roleCols]) (by decide)]; ring
    · rw [show (R.eF i).trace rb = 1 from h1, h0 ra (by simp [roleCols]) (by decide),
        h0 rc (by simp [roleCols]) (by decide)]; ring
    · rw [show (R.eF i).trace rc = 1 from h1, h0 ra (by simp [roleCols]) (by decide),
        h0 rb (by simp [roleCols]) (by decide)]; ring
  have g := R.G hi (mem_compat (a := ar (.mul (cv mW) (sumC [ra, rb, rc]))) (by simp [gCompat]))
  simp only [AG.gate, ar, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero] at g
  rw [← add_assoc, hsum, mul_one] at g
  obtain ⟨c, hc, hc1⟩ := mode_some hi hL
  simp only [modeCols, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl hc1
  · exact Or.inr (Or.inl hc1)
  · exact Or.inr (Or.inr hc1)
  · simp only [Rows.v] at hc1; rw [hc1] at g; exact absurd g one_ne_zero
  · simp only [Rows.v] at hc1 hq1; rw [hc1] at hq1; exact absurd hq1 one_ne_zero
  · simp only [Rows.v] at hc1 hqm; rw [hc1] at hqm; exact absurd hqm one_ne_zero

/-- A witness role (`rd`, `rs`) is in mode `mW`. -/
theorem witness_mode {i m : ℕ} (s : R.Slot i m) {r : ℕ} (hr : r = rd ∨ r = rs) (h1 : R.v i r = 1) :
    R.v i mW = 1 := by
  have hi : i < R.n := by have := s.lt; omega
  have hrt : r ∈ roleCols ++ [mQ1, mQM] := by rcases hr with rfl | rfl <;> simp [roleCols]
  obtain ⟨-, h0⟩ := R.tag_onehot hi hrt h1
  replace h0 : ∀ d ∈ roleCols ++ [mQ1, mQM], d ≠ r → (R.eF i).trace d = 0 := h0
  have g := R.G hi (mem_compat (a := ar (.mul (sumC [rd, rs]) (notE (cv mW)))) (by simp [gCompat]))
  simp only [AG.gate, ar, notE, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero] at g
  rcases hr with rfl | rfl
  · rw [show (R.eF i).trace rd = 1 from h1, h0 rs (by simp [roleCols]) (by decide), add_zero, one_mul] at g
    simp only [Rows.v]; linear_combination -g
  · rw [show (R.eF i).trace rs = 1 from h1, h0 rd (by simp [roleCols]) (by decide), zero_add, one_mul] at g
    simp only [Rows.v]; linear_combination -g

theorem bind_sub {σ : CoeffExpr Fp} {k v : ℕ} (h : AluSZChipJ9.bind σ k v = AluSZChipJ9.bind σ k v ∧ True)
    (hb : ∀ a ∈ AluSZChipJ9.bind σ k v, a ∈ gBind) : AluSZChipJ9.bind σ k v ⊆ gBind := hb

/-- The `D1p` equation of a 4-slot block (`hdr` + four slot heads). -/
theorem D1_four {h ma mb mc mq : ℕ} (sa : R.Slot (h + 1) ma) (sb : R.Slot (h + 1 + ma) mb)
    (sc : R.Slot (h + 1 + ma + mb) mc) (sq : R.Slot (h + 1 + ma + mb + mc) mq) (bk : R.Block h (ma + mb + mc + mq))
    (hz : ∀ P ∈ callPolys X.al X.t h, P = 0) :
    D1p X.al X.t h + (D1p X.al X.t (h + 1) + D1p X.al X.t (h + 1 + ma) + D1p X.al X.t (h + 1 + ma + mb) +
      D1p X.al X.t (h + 1 + ma + mb + mc)) = 0 := by
  have e1 := hz (blockSum X.al (D1p X.al X.t) X.al.length h) (by simp [callPolys])
  obtain ⟨o1, o2, o3⟩ := X.onbs bk
  rw [blockSum_eq X.al _ _ _ h o1 o2 o3, sum_head, sum_shift _ _ (ma + mb + mc) mq, sum_shift _ _ (ma + mb) mc,
    sum_shift _ _ ma mb, (X.slot_sum sa (i' := h + 1) rfl).1, (X.slot_sum sb (i' := h + 1 + ma) rfl).1,
    (X.slot_sum sc (i' := h + 1 + (ma + mb)) (by omega)).1,
    (X.slot_sum sq (i' := h + 1 + (ma + mb + mc)) (by omega)).1] at e1
  exact e1

/-! ## 5. `op_sound`: add, sub, lt -/

/-- **`add_sound`**: an accepted `add` call block (hdr row `h`, the gates of every row, the served reads, and the
conclusion of `outside_arithSZ` for this call) computes `primSem add` on the decoded handles. -/
theorem add_sound {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) (hop : R.v h oAdd = 1)
    (hout : (∀ P ∈ callPolys X.al X.t h, aeval R.y P = 0) → ∀ P ∈ callPolys X.al X.t h, P = 0) :
    ∃ na nb nc, HDen X.r (R.v h kA) (R.v h vA) na ∧ HDen X.r (R.v h kB) (R.v h vB) nb ∧
      HDen X.r (R.v h kE) (R.v h vE) nc ∧ Nock.Jet.Prim.primSem .add na nb = some nc := by
  have ho : oAdd ∈ opCols := by simp [opCols]
  have V := fun e he => op_vals hh hH ho hop e he
  obtain ⟨ma, mb, mc, mq, sa, sb, sc, sq, ha1, hb1, hc1, hq1, bk, hcst⟩ :=
    shape_q1 (R := R) hh hH (x := rc) (by simp [roleCols]) (σ1 := sumC [oAdd, oSub, oLt, oMul])
      (σ2 := sumC [oAdd, oSub, oMul]) (σ3 := sumC [oAdd, oSub]) (by simp [gSeq]) (by simp [gSeq]) (by simp [gSeq])
      (fun e he => by
        have v := V e he
        simp only [sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, v oAdd (by simp [opCols]), v oSub (by simp [opCols]), v oLt (by simp [opCols]),
          v oMul (by simp [opCols])]
        simp [oAdd, oSub, oLt, oMul])
  have bl := bk.lt
  have := sa.pos; have := sb.pos; have := sc.pos; have := sq.pos
  have C := fun i (h1 : h ≤ i) (h2 : i ≤ h + (ma + mb + mc + mq)) => cst_at hcst h1 h2
  have F2 := fun i (hi : i < R.n) h1 h2 => f2_zero hh hH ho hop (Or.inl rfl) hi (C i h1 h2)
  -- the premise and the event
  have hz := hout (X.premise_of bk fun j h1 h2 hf hf2 => absurd hf2 (F2 _ (by omega) (by omega) (by omega)))
  have e1 := X.D1_four sa sb sc sq bk hz
  -- the contributions
  have d0 : D1p X.al X.t h = 0 := by
    have := V (R.eF h) (fun _ _ => rfl) oLt (by simp [opCols])
    simp [D1p, onb_true X.hal hh hH, X.hal.val h hh, show (R.eF h).trace oLt = 0 by simpa [oLt, oAdd] using this]
  have cv1 : ∀ {i r : ℕ} {e : CoeffExpr Fp} {m : ℕ} (s : R.Slot i m), R.v i r = 1 → coef r cf1 e ∈ gCoef →
      R.v i cf1 = e.eval (R.eF i) := fun s hr hg => coef_val s hr hg
  rw [d0, (X.D_first sa (F2 _ (by omega) (by omega) (by omega))).1,
    (X.D_first sb (F2 _ (by omega) (by omega) (by omega))).1,
    (X.D_first sc (F2 _ (by omega) (by omega) (by omega))).1,
    (X.D_first sq (F2 _ (by omega) (by omega) (by omega))).1] at e1
  have Va := V _ (C (h + 1) (by omega) (by omega))
  have Vb := V _ (C (h + 1 + ma) (by omega) (by omega))
  have Vc := V _ (C (h + 1 + ma + mb) (by omega) (by omega))
  have Vq := V _ (C (h + 1 + ma + mb + mc) (by omega) (by omega))
  rw [cv1 sa ha1 (e := .sub (.sub (.add (.sub (cv oAdd) (cv oSub)) (.mul (cv oLt) sgnLt)) (cv oDiv)) (cv oMod))
      (by simp [gCoef]),
    cv1 sb hb1 (e := .sub (.add (cv oAdd) (cv oSub)) (.mul (cv oLt) sgnLt)) (by simp [gCoef]),
    cv1 sc hc1 (e := .sub (.sub (cv oSub) (cv oAdd)) (cv oMul)) (by simp [gCoef]),
    cv1 sq hq1 (e := sumC [oAdd, oSub, oLt]) (by simp [gCoef])] at e1
  simp only [CoeffExpr.eval, cv, sgnLt, sumC, CoeffExpr.eval_sumList, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Va oAdd (by simp [opCols]), Va oSub (by simp [opCols]), Va oLt (by simp [opCols]),
    Va oDiv (by simp [opCols]), Va oMod (by simp [opCols]), Vb oAdd (by simp [opCols]), Vb oSub (by simp [opCols]),
    Vb oLt (by simp [opCols]), Vc oAdd (by simp [opCols]), Vc oSub (by simp [opCols]), Vc oMul (by simp [opCols]),
    Vq oAdd (by simp [opCols]), Vq oSub (by simp [opCols]), Vq oLt (by simp [opCols])] at e1
  simp only [oAdd, oSub, oLt, oMul, oDiv, oMod] at e1
  norm_num at e1
  -- the slots' values
  have bA : AluSZChipJ9.bind (.mul (cv fst) (cv ra) : CoeffExpr Fp) kA vA ⊆ gBind := fun a ha => by
    unfold gBind; simp only [List.mem_append]; tauto
  have bB : AluSZChipJ9.bind (.mul (cv fst) (cv rb) : CoeffExpr Fp) kB vB ⊆ gBind := fun a ha => by
    unfold gBind; simp only [List.mem_append]; tauto
  have bE : AluSZChipJ9.bind (.mul (cv fst) (cv rc) : CoeffExpr Fp) kE vE ⊆ gBind := fun a ha => by
    unfold gBind; simp only [List.mem_append]; tauto
  have kvA := bind_val sa (σ := .mul (cv fst) (cv ra)) (sel2 sa ha1) bA
  have kvB := bind_val sb (σ := .mul (cv fst) (cv rb)) (sel2 sb hb1) bB
  have kvE := bind_val sc (σ := .mul (cv fst) (cv rc)) (sel2 sc hc1) bE
  obtain ⟨la, ea, -, hla, hda⟩ := X.operand_den sa (operand_mode sa (Or.inl rfl) ha1)
    (kvA.1.trans (C _ (by omega) (by omega) kA (by simp [Rows.constCols])))
    (kvA.2.trans (C _ (by omega) (by omega) vA (by simp [Rows.constCols])))
  obtain ⟨lb, eb, -, hlb, hdb⟩ := X.operand_den sb (operand_mode sb (Or.inr (Or.inl rfl)) hb1)
    (kvB.1.trans (C _ (by omega) (by omega) kB (by simp [Rows.constCols])))
    (kvB.2.trans (C _ (by omega) (by omega) vB (by simp [Rows.constCols])))
  obtain ⟨lc, ec, -, hlc, hdc⟩ := X.operand_den sc (operand_mode sc (Or.inr (Or.inr rfl)) hc1)
    (kvE.1.trans (C _ (by omega) (by omega) kE (by simp [Rows.constCols])))
    (kvE.2.trans (C _ (by omega) (by omega) vE (by simp [Rows.constCols])))
  obtain ⟨eq, hq⟩ := X.qslot1 sq hq1
  rw [ea, eb, ec, eq] at e1
  have hid : limbPoly la + limbPoly lb - limbPoly lc = (Polynomial.C (B : Fp) - Polynomial.X) * limbPoly (packL X.al (h + 1 + ma + mb + mc) mq) := by
    rw [CB_eq]; simp only [← limbPolyQ_eq]; linear_combination e1
  have := Nock.Atoms.add_lift hla hlb hlc hq hid
  exact ⟨val la, val lb, val lc, hda, hdb, hdc, by simp [Nock.Jet.Prim.primSem, this]⟩

/-- **`sub_sound`**: an accepted `sub` call block (hdr row `h`, the gates of every row, the served reads, and the
conclusion of `outside_arithSZ` for this call) computes `primSem sub` on the decoded handles. -/
theorem sub_sound {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) (hop : R.v h oSub = 1)
    (hout : (∀ P ∈ callPolys X.al X.t h, aeval R.y P = 0) → ∀ P ∈ callPolys X.al X.t h, P = 0) :
    ∃ na nb nc, HDen X.r (R.v h kA) (R.v h vA) na ∧ HDen X.r (R.v h kB) (R.v h vB) nb ∧
      HDen X.r (R.v h kE) (R.v h vE) nc ∧ Nock.Jet.Prim.primSem .sub na nb = some nc := by
  have ho : oSub ∈ opCols := by simp [opCols]
  have V := fun e he => op_vals hh hH ho hop e he
  obtain ⟨ma, mb, mc, mq, sa, sb, sc, sq, ha1, hb1, hc1, hq1, bk, hcst⟩ :=
    shape_q1 (R := R) hh hH (x := rc) (by simp [roleCols]) (σ1 := sumC [oAdd, oSub, oLt, oMul])
      (σ2 := sumC [oAdd, oSub, oMul]) (σ3 := sumC [oAdd, oSub]) (by simp [gSeq]) (by simp [gSeq]) (by simp [gSeq])
      (fun e he => by
        have v := V e he
        simp only [sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, v oAdd (by simp [opCols]), v oSub (by simp [opCols]), v oLt (by simp [opCols]),
          v oMul (by simp [opCols])]
        simp [oAdd, oSub, oLt, oMul])
  have bl := bk.lt
  have := sa.pos; have := sb.pos; have := sc.pos; have := sq.pos
  have C := fun i (h1 : h ≤ i) (h2 : i ≤ h + (ma + mb + mc + mq)) => cst_at hcst h1 h2
  have F2 := fun i (hi : i < R.n) h1 h2 => f2_zero hh hH ho hop (Or.inr (Or.inl rfl)) hi (C i h1 h2)
  -- the premise and the event
  have hz := hout (X.premise_of bk fun j h1 h2 hf hf2 => absurd hf2 (F2 _ (by omega) (by omega) (by omega)))
  have e1 := X.D1_four sa sb sc sq bk hz
  -- the contributions
  have d0 : D1p X.al X.t h = 0 := by
    have := V (R.eF h) (fun _ _ => rfl) oLt (by simp [opCols])
    simp [D1p, onb_true X.hal hh hH, X.hal.val h hh, show (R.eF h).trace oLt = 0 by simpa [oLt, oSub] using this]
  have cv1 : ∀ {i r : ℕ} {e : CoeffExpr Fp} {m : ℕ} (s : R.Slot i m), R.v i r = 1 → coef r cf1 e ∈ gCoef →
      R.v i cf1 = e.eval (R.eF i) := fun s hr hg => coef_val s hr hg
  rw [d0, (X.D_first sa (F2 _ (by omega) (by omega) (by omega))).1,
    (X.D_first sb (F2 _ (by omega) (by omega) (by omega))).1,
    (X.D_first sc (F2 _ (by omega) (by omega) (by omega))).1,
    (X.D_first sq (F2 _ (by omega) (by omega) (by omega))).1] at e1
  have Va := V _ (C (h + 1) (by omega) (by omega))
  have Vb := V _ (C (h + 1 + ma) (by omega) (by omega))
  have Vc := V _ (C (h + 1 + ma + mb) (by omega) (by omega))
  have Vq := V _ (C (h + 1 + ma + mb + mc) (by omega) (by omega))
  rw [cv1 sa ha1 (e := .sub (.sub (.add (.sub (cv oAdd) (cv oSub)) (.mul (cv oLt) sgnLt)) (cv oDiv)) (cv oMod))
      (by simp [gCoef]),
    cv1 sb hb1 (e := .sub (.add (cv oAdd) (cv oSub)) (.mul (cv oLt) sgnLt)) (by simp [gCoef]),
    cv1 sc hc1 (e := .sub (.sub (cv oSub) (cv oAdd)) (cv oMul)) (by simp [gCoef]),
    cv1 sq hq1 (e := sumC [oAdd, oSub, oLt]) (by simp [gCoef])] at e1
  simp only [CoeffExpr.eval, cv, sgnLt, sumC, CoeffExpr.eval_sumList, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Va oAdd (by simp [opCols]), Va oSub (by simp [opCols]), Va oLt (by simp [opCols]),
    Va oDiv (by simp [opCols]), Va oMod (by simp [opCols]), Vb oAdd (by simp [opCols]), Vb oSub (by simp [opCols]),
    Vb oLt (by simp [opCols]), Vc oAdd (by simp [opCols]), Vc oSub (by simp [opCols]), Vc oMul (by simp [opCols]),
    Vq oAdd (by simp [opCols]), Vq oSub (by simp [opCols]), Vq oLt (by simp [opCols])] at e1
  simp only [oAdd, oSub, oLt, oMul, oDiv, oMod] at e1
  norm_num at e1
  -- the slots' values
  have bA : AluSZChipJ9.bind (.mul (cv fst) (cv ra) : CoeffExpr Fp) kA vA ⊆ gBind := fun a ha => by
    unfold gBind; simp only [List.mem_append]; tauto
  have bB : AluSZChipJ9.bind (.mul (cv fst) (cv rb) : CoeffExpr Fp) kB vB ⊆ gBind := fun a ha => by
    unfold gBind; simp only [List.mem_append]; tauto
  have bE : AluSZChipJ9.bind (.mul (cv fst) (cv rc) : CoeffExpr Fp) kE vE ⊆ gBind := fun a ha => by
    unfold gBind; simp only [List.mem_append]; tauto
  have kvA := bind_val sa (σ := .mul (cv fst) (cv ra)) (sel2 sa ha1) bA
  have kvB := bind_val sb (σ := .mul (cv fst) (cv rb)) (sel2 sb hb1) bB
  have kvE := bind_val sc (σ := .mul (cv fst) (cv rc)) (sel2 sc hc1) bE
  obtain ⟨la, ea, -, hla, hda⟩ := X.operand_den sa (operand_mode sa (Or.inl rfl) ha1)
    (kvA.1.trans (C _ (by omega) (by omega) kA (by simp [Rows.constCols])))
    (kvA.2.trans (C _ (by omega) (by omega) vA (by simp [Rows.constCols])))
  obtain ⟨lb, eb, -, hlb, hdb⟩ := X.operand_den sb (operand_mode sb (Or.inr (Or.inl rfl)) hb1)
    (kvB.1.trans (C _ (by omega) (by omega) kB (by simp [Rows.constCols])))
    (kvB.2.trans (C _ (by omega) (by omega) vB (by simp [Rows.constCols])))
  obtain ⟨lc, ec, -, hlc, hdc⟩ := X.operand_den sc (operand_mode sc (Or.inr (Or.inr rfl)) hc1)
    (kvE.1.trans (C _ (by omega) (by omega) kE (by simp [Rows.constCols])))
    (kvE.2.trans (C _ (by omega) (by omega) vE (by simp [Rows.constCols])))
  obtain ⟨eq, hq⟩ := X.qslot1 sq hq1
  rw [ea, eb, ec, eq] at e1
  have hid : limbPoly lb + limbPoly lc - limbPoly la = (Polynomial.C (B : Fp) - Polynomial.X) * limbPoly (packL X.al (h + 1 + ma + mb + mc) mq) := by
    rw [CB_eq]; simp only [← limbPolyQ_eq]; linear_combination e1
  obtain ⟨h1, h2, h3⟩ := Nock.Atoms.sub_lift hla hlb hlc hq hid
  exact ⟨val la, val lb, val lc, hda, hdb, hdc, by simp [Nock.Jet.Prim.primSem, h2, h3]⟩

/-- **`lt_sound`**: an accepted `lt` call block (hdr row `h`, the gates of every row, the served reads, and the
conclusion of `outside_arithSZ` for this call) computes `primSem lt` (loobean, `0` = yes, the convention of `Nock.Jet.PrimJ9`) on the decoded handles; the result handle is `(kE, vE) = (0, lb)`. -/
theorem lt_sound {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) (hop : R.v h oLt = 1)
    (hout : (∀ P ∈ callPolys X.al X.t h, aeval R.y P = 0) → ∀ P ∈ callPolys X.al X.t h, P = 0) :
    ∃ na nb nc, HDen X.r (R.v h kA) (R.v h vA) na ∧ HDen X.r (R.v h kB) (R.v h vB) nb ∧
      HDen X.r (R.v h kE) (R.v h vE) nc ∧ Nock.Jet.Prim.primSem .lt na nb = some nc := by
  have ho : oLt ∈ opCols := by simp [opCols]
  have V := fun e he => op_vals hh hH ho hop e he
  obtain ⟨ma, mb, mc, mq, sa, sb, sc, sq, ha1, hb1, hc1, hq1, bk, hcst⟩ :=
    shape_q1 (R := R) hh hH (x := rd) (by simp [roleCols]) (σ1 := sumC [oAdd, oSub, oLt, oMul])
      (σ2 := cv oLt) (σ3 := .const 1) (by simp [gSeq]) (by simp [gSeq]) (by simp [gSeq])
      (fun e he => by
        have v := V e he
        simp only [sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, v oAdd (by simp [opCols]), v oSub (by simp [opCols]), v oLt (by simp [opCols]),
          v oMul (by simp [opCols])]
        simp [oAdd, oSub, oLt, oMul])
  have bl := bk.lt
  have := sa.pos; have := sb.pos; have := sc.pos; have := sq.pos
  have C := fun i (h1 : h ≤ i) (h2 : i ≤ h + (ma + mb + mc + mq)) => cst_at hcst h1 h2
  have F2 := fun i (hi : i < R.n) h1 h2 => f2_zero hh hH ho hop (Or.inr (Or.inr rfl)) hi (C i h1 h2)
  -- the premise and the event
  have hz := hout (X.premise_of bk fun j h1 h2 hf hf2 => absurd hf2 (F2 _ (by omega) (by omega) (by omega)))
  have e1 := X.D1_four sa sb sc sq bk hz
  -- the contributions
  have hL0 : R.v h oLt = 1 := hop
  have d0 : D1p X.al X.t h = Polynomial.C (1 - R.v h lb) := by
    simp [D1p, onb_true X.hal hh hH, X.hal.val h hh, show (R.eF h).trace oLt = 1 from hop]
  have cv1 : ∀ {i r : ℕ} {e : CoeffExpr Fp} {m : ℕ} (s : R.Slot i m), R.v i r = 1 → coef r cf1 e ∈ gCoef →
      R.v i cf1 = e.eval (R.eF i) := fun s hr hg => coef_val s hr hg
  rw [d0, (X.D_first sa (F2 _ (by omega) (by omega) (by omega))).1,
    (X.D_first sb (F2 _ (by omega) (by omega) (by omega))).1,
    (X.D_first sc (F2 _ (by omega) (by omega) (by omega))).1,
    (X.D_first sq (F2 _ (by omega) (by omega) (by omega))).1] at e1
  have Va := V _ (C (h + 1) (by omega) (by omega))
  have Vb := V _ (C (h + 1 + ma) (by omega) (by omega))
  have Vq := V _ (C (h + 1 + ma + mb + mc) (by omega) (by omega))
  have La := C (h + 1) (by omega) (by omega) lb (by simp [Rows.constCols])
  have Lb := C (h + 1 + ma) (by omega) (by omega) lb (by simp [Rows.constCols])
  rw [cv1 sa ha1 (e := .sub (.sub (.add (.sub (cv oAdd) (cv oSub)) (.mul (cv oLt) sgnLt)) (cv oDiv)) (cv oMod))
      (by simp [gCoef]),
    cv1 sb hb1 (e := .sub (.add (cv oAdd) (cv oSub)) (.mul (cv oLt) sgnLt)) (by simp [gCoef]),
    cv1 sc hc1 (e := .const 1) (by simp [gCoef]),
    cv1 sq hq1 (e := sumC [oAdd, oSub, oLt]) (by simp [gCoef])] at e1
  simp only [CoeffExpr.eval, cv, sgnLt, sumC, CoeffExpr.eval_sumList, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Va oAdd (by simp [opCols]), Va oSub (by simp [opCols]), Va oLt (by simp [opCols]),
    Va oDiv (by simp [opCols]), Va oMod (by simp [opCols]), Vb oAdd (by simp [opCols]), Vb oSub (by simp [opCols]),
    Vb oLt (by simp [opCols]), Vq oAdd (by simp [opCols]), Vq oSub (by simp [opCols]), Vq oLt (by simp [opCols]),
    La, Lb] at e1
  simp only [oAdd, oSub, oLt, oMul, oDiv, oMod] at e1
  norm_num at e1
  -- the slots' values
  have bA : AluSZChipJ9.bind (.mul (cv fst) (cv ra) : CoeffExpr Fp) kA vA ⊆ gBind := fun a ha => by
    unfold gBind; simp only [List.mem_append]; tauto
  have bB : AluSZChipJ9.bind (.mul (cv fst) (cv rb) : CoeffExpr Fp) kB vB ⊆ gBind := fun a ha => by
    unfold gBind; simp only [List.mem_append]; tauto
  have kvA := bind_val sa (σ := .mul (cv fst) (cv ra)) (sel2 sa ha1) bA
  have kvB := bind_val sb (σ := .mul (cv fst) (cv rb)) (sel2 sb hb1) bB
  obtain ⟨la, ea, -, hla, hda⟩ := X.operand_den sa (operand_mode sa (Or.inl rfl) ha1)
    (kvA.1.trans (C _ (by omega) (by omega) kA (by simp [Rows.constCols])))
    (kvA.2.trans (C _ (by omega) (by omega) vA (by simp [Rows.constCols])))
  obtain ⟨lb', eb, -, hlb, hdb⟩ := X.operand_den sb (operand_mode sb (Or.inr (Or.inl rfl)) hb1)
    (kvB.1.trans (C _ (by omega) (by omega) kB (by simp [Rows.constCols])))
    (kvB.2.trans (C _ (by omega) (by omega) vB (by simp [Rows.constCols])))
  obtain ⟨ed, -, hld⟩ := X.witness sc (witness_mode sc (Or.inl rfl) hc1)
  obtain ⟨eq, hq⟩ := X.qslot1 sq hq1
  rw [ea, eb, ed, eq] at e1
  -- the result handle `(kE, vE) = (0, lb)` (`gHdr`)
  have gk := R.G hh (Rows.mem_hdr (a := ar (prod3 (cv sH) (cv oLt) (cv kE))) (by simp [gHdr]))
  have gv := R.G hh (Rows.mem_hdr (a := AG.cp ⟨.mul (cv sH) (cv oLt), .cur vE, .cur lb⟩) (by simp [gHdr]))
  simp only [AG.gate, ar, prod3, CopyG.gate, Op.expr, cv, CoeffExpr.eval] at gk gv
  simp only [Rows.v] at hH hL0
  rw [hH, hL0, one_mul, one_mul] at gk gv
  have hvE : R.v h vE = R.v h lb := sub_eq_zero.mp gv
  rcases R.b_lb hh with hl | hl
  · -- yes: `a < b`
    rw [hl] at e1
    simp only [map_zero, map_one, map_ofNat, mul_zero, mul_one, sub_zero, zero_mul] at e1
    have hid : limbPoly la + limbPoly (lanes (laneL X.al) (h + 1 + ma + mb) mc) + 1 - limbPoly lb' =
        (Polynomial.C (B : Fp) - Polynomial.X) * limbPoly (packL X.al (h + 1 + ma + mb + mc) mq) := by
      rw [CB_eq]; simp only [← limbPolyQ_eq]; linear_combination e1
    have := (Nock.Atoms.lt_lift_yes hla hlb hld hq hid).2
    refine ⟨val la, val lb', 0, hda, hdb, Or.inl ⟨gk, by rw [hvE, hl]; simp, by norm_num [Nock.Atoms.p, Nock.Field.p]⟩,
      by simp [Nock.Jet.Prim.primSem, this]⟩
  · -- no: `b ≤ a`
    rw [hl] at e1
    simp only [map_zero, map_one, map_ofNat, mul_zero, mul_one, sub_zero, zero_mul] at e1
    have hid : limbPoly lb' + limbPoly (lanes (laneL X.al) (h + 1 + ma + mb) mc) - limbPoly la =
        (Polynomial.C (B : Fp) - Polynomial.X) * limbPoly (packL X.al (h + 1 + ma + mb + mc) mq) := by
      rw [CB_eq]; simp only [← limbPolyQ_eq]; linear_combination e1
    have := (Nock.Atoms.lt_lift_no hla hlb hld hq hid).2
    refine ⟨val la, val lb', 1, hda, hdb, Or.inl ⟨gk, by rw [hvE, hl]; exact ZMod.val_one _,
      by norm_num [Nock.Atoms.p, Nock.Field.p]⟩, by simp [Nock.Jet.Prim.primSem, not_lt.mpr this]⟩

end Ctx

/-! ## 6. `out_canonical` -/

/-- **`out_canonical`**: a handle `HDen` names is canonical by its kind — kind `0` a value `< p` (the split's
`< p` gate), kind `2` a canonical limb list of value `≥ p` (the atom table's `mb` row, `AluSZRead`). -/
theorem out_canonical {r : ℕ → AtomChipHQ.ARow} {k v : Fp} {n : ℕ} (hd : Ctx.HDen r k v n) :
    (k = 0 ∧ v.val = n ∧ n < Nock.Atoms.p) ∨ (k = 2 ∧ Nock.Atoms.p ≤ n ∧ ∃ l, Canonical l ∧ val l = n) := by
  rcases hd with h | ⟨h2, -, hb, l, hc, hv, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨h2, hb, l, hc, hv⟩

/-! ## 7. `op_sound` off the per-call event (`outside_arithSZ`, `AluSZEvent`) -/

/-- The op flag column of a primitive. -/
def opColOf : Nock.Jet.Prim.PrimOp → ℕ
  | .add => oAdd | .sub => oSub | .lt => oLt | .mul => oMul | .div => oDiv | .mod => oMod | .dec => oAdd

section Event
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 cY1 cY2)
variable [Fintype K] [DecidableEq K] [Algebra Fp (Quad (algebraMap Fp K δ))] {R : Rows δ K}

/-- A hdr row of the window is a call of `AluSZEvent`'s readout. -/
theorem mem_hdrs {al : List ALRow} (hal : Readout R al) {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) :
    h ∈ hdrs al := by
  unfold hdrs
  rw [List.mem_filter]
  exact ⟨List.mem_range.mpr (by rw [hal.len]; exact hh), onb_true hal hh hH⟩

variable {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {alu : Tr → List ALRow}
  {atom : Tr → List (CellRowB0 Nock.Atoms.p)} {C A AL : ℕ} {hC : ∀ tr, (hdrs (alu tr)).length ≤ C}
  {hA : ∀ tr, (atom tr).length ≤ A} {hAL : ∀ tr, (alu tr).length ≤ AL}
  {hc : ∀ Q, St Q → ∀ χ χ', alu (Q χ) = alu (Q χ') ∧ atom (Q χ) = atom (Q χ')}

/-- **The consumed event discharges `hout`**: outside `arithSZ`, at the trace whose readouts are the
context's, the call at hdr row `h` satisfies the hypothesis of the `*_sound` theorems. -/
theorem hout_of_event (X : Ctx R) (tr : Tr) (χ : Coins frameJ8 K) (hal : X.al = alu tr) (ht : X.t = atom tr)
    (hy : R.y = Quad.mk (algebraMap Fp K δ) (χ cY1) (χ cY2))
    (hχ : ¬ (AluSZEvent.arithSZ (algebraMap Fp K δ) St alu atom C A AL hC hA hAL hc).mem tr χ)
    {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) :
    (∀ P ∈ callPolys X.al X.t h, aeval R.y P = 0) → ∀ P ∈ callPolys X.al X.t h, P = 0 := by
  intro h0
  have hm := mem_hdrs X.hal hh hH
  rw [hal] at hm h0 ⊢
  rw [ht] at h0 ⊢
  rw [hy] at h0
  exact AluSZEvent.outside_arithSZ (algebraMap Fp K δ) St alu atom C A AL hC hA hAL hc tr χ hχ hm h0

/-- **`op_sound`** (add, sub, lt): the gates of one call block (`R`), the served reads (`X.read`), the atom walk
(`X.walk`) and the call outside the per-call arithmetic event `arithSZ` give `primSem op (D a) (D b) = some (D c)`
on the hdr's handles `(kA, vA)`, `(kB, vB)`, `(kE, vE)` (`HDen.denK`: `D = denK`). -/
theorem op_sound (X : Ctx R) (op : Nock.Jet.Prim.PrimOp) (hop3 : op = .add ∨ op = .sub ∨ op = .lt)
    {h : ℕ} (hh : h < R.n) (hH : R.v h sH = 1) (hflag : R.v h (opColOf op) = 1)
    (tr : Tr) (χ : Coins frameJ8 K) (hal : X.al = alu tr) (ht : X.t = atom tr)
    (hy : R.y = Quad.mk (algebraMap Fp K δ) (χ cY1) (χ cY2))
    (hχ : ¬ (AluSZEvent.arithSZ (algebraMap Fp K δ) St alu atom C A AL hC hA hAL hc).mem tr χ) :
    ∃ na nb nc, Ctx.HDen X.r (R.v h kA) (R.v h vA) na ∧ Ctx.HDen X.r (R.v h kB) (R.v h vB) nb ∧
      Ctx.HDen X.r (R.v h kE) (R.v h vE) nc ∧ Nock.Jet.Prim.primSem op na nb = some nc := by
  have hout := hout_of_event X tr χ hal ht hy hχ hh hH
  rcases hop3 with rfl | rfl | rfl
  · exact X.add_sound hh hH hflag hout
  · exact X.sub_sound hh hH hflag hout
  · exact X.lt_sound hh hH hflag hout

end Event

/-! ## 8. Chip satisfaction ⇒ a window of `RowGates` rows -/

section Chip
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH (gather_chal_T masks_of gather_next_T)
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] {δ : Fp} [Fact (¬ IsSquare (algebraMap Fp K δ))]
  (b : Basis (Fin 3) Fp K) {hO n : ℕ} (hn : 0 < n) (nodes : Fin n → Fp) (orbit : StrictOrbitDomain Fp 3 hO)
  (chals pubs : ℕ → K) (pre : Fin 3 → Fp[X]) (Q : Fin (aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.w → Fp[X])

/-- Row `i`'s base environment on the ALU chip. -/
abbrev aluEF (i : Fin n) : Env Fp :=
  Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 94 chals) (slotVal b 94 pubs)

/-- Row `i`'s gathered `𝕂` environment on the ALU chip. -/
abbrev aluEK (i : Fin n) : Env K := gatherEnv b ((aluTemplateSZ δ).col0 3) (aluEF b hn nodes orbit chals pubs pre Q i)

/-- **Chip satisfaction ⇒ `RowGates` at every row** (the `atom_base` pattern). -/
theorem alu_rowGates (hsat : (aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.Satisfies Q) (i : Fin n) :
    RowGates δ (aluEK b hn nodes orbit chals pubs pre Q i) (aluEF b hn nodes orbit chals pubs pre Q i) := by
  have hl := (expandChip_satisfies_iff_language (aluTemplateSZ δ) b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  exact ⟨hl.1, hl.2.2.2⟩

theorem alu_width : (aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.w = 196 := rfl

/-- The ℕ-indexed rows (row `0` past the end). -/
def eFn (i : ℕ) : Env Fp :=
  if h : i < n then aluEF b hn nodes orbit chals pubs pre Q ⟨i, h⟩ else aluEF b hn nodes orbit chals pubs pre Q ⟨0, hn⟩

def eKn (i : ℕ) : Env K :=
  if h : i < n then aluEK b hn nodes orbit chals pubs pre Q ⟨i, h⟩ else aluEK b hn nodes orbit chals pubs pre Q ⟨0, hn⟩

theorem eFn_lt {i : ℕ} (h : i < n) : eFn b hn nodes orbit chals pubs pre Q i = aluEF b hn nodes orbit chals pubs pre Q ⟨i, h⟩ := by
  simp [eFn, h]

theorem eKn_lt {i : ℕ} (h : i < n) : eKn b hn nodes orbit chals pubs pre Q i = aluEK b hn nodes orbit chals pubs pre Q ⟨i, h⟩ := by
  simp [eKn, h]

/-- **The window of an accepted ALU chip**: every row's gates (`alu_rowGates`), row adjacency (`hadj`), the
preprocessing masks (`hbind`, `hinj`), a boolean preg selector (`hpre`, verifier data) and the challenge leaves
carrying `y` and `y^t` (`chalsALJ8_y`, `chalsALJ8_ypow` for `chals = chalsALJ8 δ χ`). -/
def rowsOf (hsat : (aluSZChipJ9 δ b hn nodes orbit chals pubs pre).rap.Satisfies Q)
    (hbind : (aluSZChipJ9 δ b hn nodes orbit chals pubs pre).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hpre : ∀ i : Fin n, (pre 0).eval (nodes i) = 0 ∨ (pre 0).eval (nodes i) = 1)
    (y : Quad (algebraMap Fp K δ)) (hy : Quad.mk (algebraMap Fp K δ) (chals 2) (chals 3) = y)
    (hyp : ∀ t ≤ 32, Quad.mk (algebraMap Fp K δ) (chals (40 + 2 * t)) (chals (41 + 2 * t)) = y ^ t) : Rows δ K where
  n := n
  pos := hn
  eK := eKn b hn nodes orbit chals pubs pre Q
  eF := eFn b hn nodes orbit chals pubs pre Q
  gates i hi := by rw [eKn_lt _ _ _ _ _ _ _ _ hi, eFn_lt _ _ _ _ _ _ _ _ hi]; exact alu_rowGates b hn nodes orbit chals pubs pre Q hsat _
  nextF i hi j := by
    rw [eFn_lt _ _ _ _ _ _ _ _ (by omega), eFn_lt _ _ _ _ _ _ _ _ hi]
    exact traceNext_eq nodes orbit Q _ _ hadj ⟨i, by omega⟩ hi j
  nextK i hi j := by
    rw [eKn_lt _ _ _ _ _ _ _ _ (by omega), eKn_lt _ _ _ _ _ _ _ _ hi]
    exact gather_next_T b _ _ _ (traceNext_eq nodes orbit Q _ _ hadj ⟨i, by omega⟩ hi) j
  last := by
    rw [eFn_lt _ _ _ _ _ _ _ _ (by omega)]
    have h0 : Q ⟨0, by rw [alu_width]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 5; omega⟩
    have h1 : Q ⟨1, by rw [alu_width]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 5; omega⟩
    have := (masks_of hn nodes orbit Q _ _ h0 h1 hinj (slotVal b 94 chals) (slotVal b 94 pubs) ⟨n - 1, by omega⟩).2
    simpa [isLT] using this
  notLast i hi := by
    rw [eFn_lt _ _ _ _ _ _ _ _ (by omega)]
    have h0 : Q ⟨0, by rw [alu_width]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 5; omega⟩
    have h1 : Q ⟨1, by rw [alu_width]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 5; omega⟩
    have := (masks_of hn nodes orbit Q _ _ h0 h1 hinj (slotVal b 94 chals) (slotVal b 94 pubs) ⟨i, by omega⟩).2
    rw [if_neg (by simp only []; omega)] at this
    simpa [isLT] using this
  spBool i hi := by
    rw [eFn_lt _ _ _ _ _ _ _ _ hi]
    have h2 : Q ⟨2, by rw [alu_width]; omega⟩ = pre 0 := hbind ⟨2, by show 2 < 5; omega⟩
    show (Reify.envOfTrace Q orbit.ω (nodes ⟨i, hi⟩) (slotVal b 94 chals) (slotVal b 94 pubs)).trace 2 = 0 ∨
      (Reify.envOfTrace Q orbit.ω (nodes ⟨i, hi⟩) (slotVal b 94 chals) (slotVal b 94 pubs)).trace 2 = 1
    rw [envOfTrace_trace Q _ _ _ _ (by rw [alu_width]; omega), h2]
    exact hpre _
  y := y
  chalY i hi := by
    rw [eKn_lt _ _ _ _ _ _ _ _ hi, gather_chal_T b (aluTemplateSZ δ) 94 (aluTemplateSZ_baseCols δ) _ chals rfl,
      gather_chal_T b (aluTemplateSZ δ) 94 (aluTemplateSZ_baseCols δ) _ chals rfl]
    exact hy
  chalPow i hi t ht := by
    rw [eKn_lt _ _ _ _ _ _ _ _ hi, gather_chal_T b (aluTemplateSZ δ) 94 (aluTemplateSZ_baseCols δ) _ chals rfl,
      gather_chal_T b (aluTemplateSZ δ) 94 (aluTemplateSZ_baseCols δ) _ chals rfl]
    exact hyp t ht

end Chip

/-! ## 9. Served reads (`AluSZRead`'s `fp_read_sound`) give `ReadOK` -/

section Served
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes Reads atomChipHQ LimbsBounded)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ (aEF)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)
open Nock.ComputeTable (FP)
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] [DecidableEq K] {δ : Fp}
  [Fact (¬ IsSquare (algebraMap Fp K δ))] {b : Basis (Fin 3) Fp K}
  [Fact (ringChar Fp).Prime] [Algebra (ZMod (ringChar Fp)) K]
  [Algebra (ZMod (ringChar Fp)) (Quad (algebraMap Fp K δ))] [Algebra Fp (Quad (algebraMap Fp K δ))]
  {hA nA : ℕ} {hnA : 0 < nA} {nodesA : Fin nA → Fp} {orbitA : StrictOrbitDomain Fp 3 hA} {chalsA pubsA : ℕ → K}
  {QA : Fin (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → Fp[X]}

/-- **A served ALU validity read is `ReadOK`** (`AluSZRead`'s `fp_read_sound` at the Goldilocks prime; the limb coin of the
atom table is the ALU's `y`). -/
theorem readOK_of_served
    (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbind : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinj : Function.Injective nodesA)
    (hadj : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hnp : nA < Nock.Atoms.p) (hy : Quad.mk (algebraMap Fp K δ) (chalsA 2) (chalsA 3) ≠ 0)
    (hservedA : ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    {r : ℕ → ARow} (hR : ∀ k : Fin nA, Reads (aEF b nodesA orbitA chalsA pubsA QA k) (r k))
    (hs : ∀ k : Fin nA, SmallU (r k)) (hidx : ∀ k : Fin nA, (r k).idx = k) (hB : LimbsBounded r)
    (hwR : ∀ k : Fin nA, (r k).wR ≤ 1) (hTout : ∀ j, nA ≤ j → (r j).wR = 0 → (r j).aR ≠ 0)
    (z : Quad (algebraMap Fp K δ)) (hzAt : Quad.mk (algebraMap Fp K δ) (chalsA 37) (chalsA 38) = z)
    {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) (Quad (algebraMap Fp K δ))] (hqc : 2 ^ 63 < q)
    {zc : Quad (algebraMap Fp K δ)} {t : List (CellRow q (Quad (algebraMap Fp K δ)))}
    (hrows : ∀ c ∈ t, RowOK zc c) {Lv : Quad (algebraMap Fp K δ)} {v : ℕ}
    (hserved : Served2 t (AcceptsJ8P.mbVp δ b nodesA orbitA chalsA pubsA QA) (FP.atomFP z Lv, 0, 0, v))
    {y : Quad (algebraMap Fp K δ)} (hyA : Quad.mk (algebraMap Fp K δ) (chalsA 2) (chalsA 3) = y) :
    ReadOK y r Lv v := by
  have hq : 2 ^ 63 < Nock.Atoms.p := by norm_num [Nock.Atoms.p, Nock.Field.p]
  obtain ⟨l, hl, hbig, hcan, hL, hden, -⟩ := fp_read_sound (p := Nock.Atoms.p) hq rfl hsat hbind hinj hadj hnp hy
    hservedA hR hs hidx hB hwR hTout z hzAt hqc hrows hserved
  exact ⟨l, hl, hbig, hcan, hyA ▸ hL, hden ([] : List (CellRowB0 q))⟩

end Served

/-! ## Axioms (expected: `[propext, Classical.choice, Quot.sound]`) -/

#print axioms Ctx.add_sound
#print axioms Ctx.sub_sound
#print axioms Ctx.lt_sound
#print axioms op_sound
#print axioms out_canonical
#print axioms Ctx.HDen.denK
#print axioms Ctx.premise_of
#print axioms hout_of_event
#print axioms alu_rowGates
#print axioms rowsOf
#print axioms readOK_of_served
#print axioms Ctx.shape_q1

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluSZOps
