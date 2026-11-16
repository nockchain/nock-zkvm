/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/RowSemChipX9.lean

* `activeX9 env` — the records a twin row consumes (`slotsX9`, entries at activity `1`, pairs under an
    active flag).
  * **`RecOK9 D V R comb`** (S5) — what a served, genuine record says: on the `TAG_ax` 8-entry shape
    `(hv, ft.k, ft.v, o.k, o.v, id, 0, 5)` the design's **cond. 4** `TagAxOK`: for every `n` with
    `D ft = atom n`, `V id = n`, `2^32 ≤ n` (every axis chain has ≥ 2 rows: `head·isLast = 0`) and
    `slot n (D (1, hv)) = D o`; on the 4-entry `walkRecA` shape `WalkAOK9` (RecOKA's `WalkAOK` with the
    atom read through `V = valId`); elsewhere `RecOK`.  The obligations are discharged at
    LINK (S1–S4), not here.
  * **`rowSemX9_old`** — old states: `baseHoldsX_of_X9` + `OneHotAt9.newOff` + RecOKAJ8's
    `rowSemX_of_chipA` VERBATIM (no J-8 semantics on a new state; A0 Q5).
  * **`sem_s0B`**, **`sem_s10B`** — the two new real states, from `s0B_row` / `s10B_row` and the served
    records (`hp64 : p ≤ 2^64` for the field route's `top n = 1`).
  * **`sem_s10S`** — the segment pseudo-row, at Goldilocks (`hpG`; `wrap62` at `m = 62`), with the
    limb consume read at `comb := combN`; ℕ helpers `digits_getElem!` (digit `m` = `n / B^m % B`),
    `limb_head`, `limb_nonhead`, `s10S_limb`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.LocalVSX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ChipHX9
import Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8
import Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9

open Nock Nock.Reified Nock.Edit
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (reVal pairRecsX activeX RecOK val_nat val_one' hdV_k0
  hdV_k1 HalvingOK)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8 (RecOKA rowSemX_of_chipA)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8 (PreI preI_off)
open Nock.J9A.NounAx (top segAx segD segRd nxtAx slot_combL_atom top_eq_length segAx_next segAx_top
  nxtAx_zero wrap62)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combN combL)
open Nock.Jet (Registry)

variable {p : ℕ} [Fact p.Prime]

/-! ## 1. Consumed records and the obligation -/

/-- **The records a twin row consumes.** -/
def activeX9 (env : Env (ZMod p)) : List (List ℕ × Bal) :=
  (slotsX9 (F := ℚ)).flatMap fun S =>
    ((S.ents.filter fun x => decide (evalQX x.act env = 1)).map fun x =>
      (x.rcd.map (reVal env), x.bal)) ++ pairRecsX env S

/-- The design's cond. 4 on a `TAG_ax` record. -/
def TagAxOK (D : HX → Option Noun) (V : ℕ → Option ℕ) : List ℕ → Prop
  | [hv, fk, fv, ok, ov, id, 0, 5] => ∀ n, D (fk, fv) = some (.atom n) →
      V id = some n ∧ 2 ^ 32 ≤ n ∧
        ∃ X Y, D (1, hv) = some X ∧ D (ok, ov) = some Y ∧ Noun.slot n X = some Y
  | _ => True

/-- `RecOKA`'s `WalkAOK` with the atom read through `V = valId`. -/
def WalkAOK9 (V : ℕ → Option ℕ) (comb : ℕ → Noun) : List ℕ → Prop
  | [rv, ax, lk, lv] => ∃ n, V rv = some n ∧ (lk = 0 → Noun.slot ax (comb n) = some (.atom lv)) ∧
      (lk = 1 → ∃ a c, Noun.slot ax (comb n) = some (.cell a c))
  | _ => True

/-- The record class: `1` = `TAG_ax` (8 entries, tag `5` last, service), `2` = `walkRecA` (4 entries,
service), `0` = every other shape. -/
def recClass : List ℕ × Bal → ℕ
  | (l, .s) => if l.length = 8 ∧ l.getLast? = some 5 then 1 else if l.length = 4 then 2 else 0
  | _ => 0

/-- **Design S5: `RecOK9`.** -/
def RecOK9 (D : HX → Option Noun) (V : ℕ → Option ℕ) (R : Registry) (comb : ℕ → Noun)
    (r : List ℕ × Bal) : Prop :=
  if recClass r = 1 then TagAxOK D V r.1 else if recClass r = 2 then WalkAOK9 V comb r.1
  else RecOK D R (fun _ _ => (0, 0)) r

/-- **The guarded antecedent**: a class-`0` service record (the inc
key's OLD handle, the jet key's SUBJECT) needs RecOKIJ8's `PreI`; the `TAG_ax` (class `1`, already an implication
on `D ft`) and `walkRecA` (class `2`, read through `V`) records need none. -/
def PreI9 (D : HX → Option Noun) (r : List ℕ × Bal) : Prop := recClass r = 0 → PreI D r

/-- **`RecOK9` in the implication form** (the obligation the guarded pipeline asks LINK for). -/
def RecOK9I (D : HX → Option Noun) (V : ℕ → Option ℕ) (R : Registry) (comb : ℕ → Noun)
    (r : List ℕ × Bal) : Prop :=
  PreI9 D r → RecOK9 D V R comb r

theorem pre9_off {D : HX → Option Noun} {l : List ℕ} {bl : Bal} (h : bl ≠ .s) : PreI9 D (l, bl) :=
  fun _ => preI_off h

theorem pre9_cls {D : HX → Option Noun} {r : List ℕ × Bal} (h : recClass r ≠ 0) : PreI9 D r :=
  fun h0 => absurd h0 h

/-! ## 2. The decoded row and record membership -/

/-- The chip state's one-hot column. -/
def csIdx : CSt → ℕ
  | .old st => stIdx st
  | .s0B => sS0B
  | .s10B => sS10B
  | .s10S => sS10S

/-- **The decoded twin row** (J-8 handles; a new state's `base.st` is a placeholder never read). -/
def rowOfX9 (env : Env (ZMod p)) (cs : CSt) : RowVSX9 :=
  ⟨cs, rowOfX env (match cs with | .old st => st | _ => .s0), hdV env ⟨kLabX, vLabX⟩⟩

section Facts
variable {env : Env (ZMod p)} {D : HX → Option Noun} {V : ℕ → Option ℕ}

theorem ent_mem9 {S : SlotX ℚ} (hS : S ∈ (slotsX9 : List (SlotX ℚ))) {x : EntX ℚ} (hx : x ∈ S.ents)
    (he : evalQX x.act env = 1) : (x.rcd.map (reVal env), x.bal) ∈ activeX9 env :=
  List.mem_flatMap.mpr ⟨S, hS, List.mem_append_left _
    (List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hx, by simp [he]⟩, rfl⟩)⟩

/-- A wire kind decomposes as `kc + 2·kb`. -/
theorem trace_k (h : Hd) : env.trace h.k = kcV env h + 2 * kbV env h := by
  simp only [kcV, kbV]; ring

/-- A cell-kind handle decodes to wire kind `1`. -/
theorem hd_k1 (hB : BaseHoldsX9 env) {h : Hd} (hh : h ∈ allHandlesX) (hne : h ≠ xF)
    (hc : kcV env h = 1) : env.trace h.k = 1 := by
  rcases kind_split9 hB h hh hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hc] at h1; exact absurd h1 one_ne_zero
  · rw [trace_k, h1, h2]; ring
  · rw [hc] at h1; exact absurd h1 one_ne_zero

theorem val_two (hp : 2 < p) : ((2 : ZMod p)).val = 2 := by
  simpa using val_nat (p := p) (n := 2) hp

/-- A non-cell (`kc = 0`) handle that denotes is an atom. -/
theorem atom_of_kc0 (hD : DenOKX9 p D V) (hp : 2 < p) (hB : BaseHoldsX9 env) {h : Hd}
    (hh : h ∈ allHandlesX) (hne : h ≠ xF) (hc : kcV env h = 0) {B : Noun}
    (hBd : D (hdV env h) = some B) : ∃ n, D (hdV env h) = some (.atom n) := by
  rcases kind_split9 hB h hh hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hk : env.trace h.k = 0 := by rw [trace_k, h1, h2]; ring
    rw [hdV_k0 hk]; exact ⟨_, hD.base.atom _⟩
  · rw [hc] at h1; exact absurd h1.symm one_ne_zero
  · have hk : env.trace h.k = 2 := by rw [trace_k, h1, h2]; ring
    have e : hdV env h = (2, (env.trace h.v).val) := by simp [hdV, hk, val_two hp]
    rw [e] at hBd ⊢
    obtain ⟨n, rfl, -⟩ := hD.base.big _ _ hBd
    exact ⟨n, hBd⟩

end Facts

/-! ## 3. Old states: C-2 / J-8 verbatim through the projection -/

section Old
variable {env : Env (ZMod p)} {D : HX → Option Noun} {V : ℕ → Option ℕ} {R : Registry} {comb : ℕ → Noun}

/-- **Design S6, old states**: a twin row one-hot at a J-8 state satisfies `RowSemX9`, by
`baseHoldsX_of_X9` and RecOKAJ8's `rowSemX_of_chipA` verbatim. -/
theorem rowSemX9_old (hD : DenOKX9 p D V) (hp : 17 < p) (hB : BaseHoldsX9 env) (st : StateX)
    (hOH : OneHotAt9 env (stIdx st)) (hOK : ∀ r ∈ activeX env, RecOKA D R comb r)
    (hv : HalvingOK env st) : RowSemX9 p D V R (rowOfX9 env (.old st)) := by
  have hN := hOH.newOff (stIdx_lt st)
  have hB8 := baseHoldsX_of_X9 hB hN
  have hOH8 : OneHotAt env (stIdx st) := fun i hi =>
    hOH i (List.mem_append_left _ (List.mem_range.mpr hi))
  obtain ⟨h0, hk⟩ := rowSemX_of_chipA hD.base hp hB8 st hOH8 hOK hv
  refine ⟨⟨rfl, h0⟩, ?_⟩
  intro i hi hc
  have hc' : chainPosX st i = false := by
    have : chainPosX9 (StateX9.ofX st) i = false := hc
    rwa [chainPosX9_ofX] at this
  exact hk i hi hc'

end Old

/-! ## 4. The new real states -/

section New
variable {env : Env (ZMod p)} {D : HX → Option Noun} {V : ℕ → Option ℕ} {R : Registry} {comb : ℕ → Noun}

theorem fh_zero_kind (hB : BaseHoldsX9 env) (hc : env.trace consCol = 0) : env.trace xFh.k = 0 := by
  have aH := arith_of_base9 hB (g := .sub (cc consCol) (kcE xFh)) (by decide +kernel)
  have aB := arith_of_base9 hB (g := kbE xFh) (by decide +kernel)
  simp only [cc, kcE, kbE, evalQX, Rat.cast_ofNat, hc, zero_sub] at aH aB
  linear_combination -aH + 2 * aB

/-- The cell record of a twin entry. -/
theorem cell9 (hOK : ∀ r ∈ activeX9 env, RecOK9I D V R comb r) {P L Q : Hd}
    (hm : ((cellRecX P L Q).map (reVal env), Bal.x) ∈ activeX9 env) (hk : env.trace P.k = 1) :
    Cell3 D (hdV env P) (hdV env L) (hdV env Q) := by
  have := hOK _ hm (pre9_off (by decide))
  simp only [RecOK9, recClass, cellRecX, recOf, cellRec, List.map_cons, List.map_nil, reVal, RecOK,
    reduceCtorEq, ite_false] at this
  rw [hdV_k1 hk]; exact this

/-- The `TAG_ax` record of a twin entry. -/
theorem tagAx9 (hOK : ∀ r ∈ activeX9 env, RecOK9I D V R comb r) {r ft o : Hd}
    (hm : ((axRecX r ft o).map (reVal env), Bal.s) ∈ activeX9 env) :
    ∀ n, D (hdV env ft) = some (.atom n) → V (env.trace xIdX).val = some n ∧ 2 ^ 32 ≤ n ∧
      ∃ X Y, D (1, (env.trace r.v).val) = some X ∧ D (hdV env o) = some Y ∧ Noun.slot n X = some Y := by
  have := hOK _ hm (pre9_cls (by simp [recClass, axRecX, reVal]))
  simp only [RecOK9, recClass, axRecX, List.map_cons, List.map_nil, reVal, List.length_cons,
    List.length_nil, List.getLast?_cons_cons, List.getLast?_singleton, and_self, ite_true] at this
  exact this

/-- **Design S6, `s0B`**: `f = [0 f_t]` with `D f_t = atom n` and `slot n (D s) = D e`. -/
theorem sem_s0B (hD : DenOKX9 p D V) (hp : 17 < p) (hB : BaseHoldsX9 env)
    (hOH : OneHotAt9 env sS0B) (hOK : ∀ r ∈ activeX9 env, RecOK9I D V R comb r) :
    RowSemX9 p D V R (rowOfX9 env .s0B) := by
  obtain ⟨hfh, hfk, hftc, -, hsc, -, -⟩ := s0B_row hB hOH
  have h1 : env.trace sS0B = 1 := hOH.one (by decide +kernel)
  have h2 : env.trace sS10B = 0 := hOH.zero (by decide +kernel) (by decide)
  have hcons : env.trace consCol = 0 := hOH.zero (by decide +kernel) (by decide)
  have hcell := ent_mem9 (env := env) (S := slot0X9) (by simp [slotsX9])
    (x := ⟨[sS0B, sS10B], .const 1, cellRecX xF xFh xFt, .x⟩) (by simp [slot0X9, extSlot, ents0New])
    (by simp [EntX.act, selS, CoeffExpr.sumList, evalQX, cc, h1, h2])
  have hax := ent_mem9 (env := env) (S := slot1X9) (by simp [slotsX9])
    (x := ⟨[sS0B], .const 1, axRecX xS xFt xE, .s⟩) (by simp [slot1X9, extSlot, ents1New])
    (by simp [EntX.act, selS, CoeffExpr.sumList, evalQX, cc, h1])
  have c3 := cell9 hOK hcell (by simpa [tr] using hfk)
  obtain ⟨A, Bn, -, -, hBd⟩ := c3
  obtain ⟨n, hn⟩ := atom_of_kc0 hD (by omega) hB (h := xFt) (by decide) (by decide) hftc hBd
  obtain ⟨-, -, X, Y, hX, hY, hsl⟩ := tagAx9 hOK hax n hn
  have hsk : env.trace xS.k = 1 := hd_k1 hB (by decide) (by decide) hsc
  refine ⟨?_, fun i hi => by simp [kidsX9, rowOfX9] at hi⟩
  simp only [RowSemX09, rowOfX9, rowOfX]
  refine ⟨cell9 hOK hcell (by simpa [tr] using hfk), ?_, n, X, Y, hn, ?_, hY, hsl⟩
  · rw [hdV_k0 (fh_zero_kind hB hcons)]; simp only [tr] at hfh; rw [hfh]; simp
  · rw [hdV_k1 hsk]; exact hX

/-- `top n = 1` for a two-limb `n < 2^64`. -/
theorem top_two_limb {n : ℕ} (h1 : 2 ^ 32 ≤ n) (h2 : n < 2 ^ 64) : top n = 1 := by
  unfold top
  exact Nat.log_eq_of_pow_le_of_lt_pow (by simpa using h1) (by simpa using h2)

/-- **Design S6, `s10B`**: the `s10` edit read at a big or field axis, and the chain root's label
denotes the same axis atom (kind 2: the handle itself; field axis: `D (3, 64·id + 1)` through `V`). -/
theorem sem_s10B (hD : DenOKX9 p D V) (hp : 17 < p) (hp64 : p ≤ 2 ^ 64) (hB : BaseHoldsX9 env)
    (hOH : OneHotAt9 env sS10B) (hOK : ∀ r ∈ activeX9 env, RecOK9I D V R comb r) :
    RowSemX9 p D V R (rowOfX9 env .s10B) := by
  obtain ⟨hfh, hfk, hftc, hfthc, hftthc, -, hec, httt, htt, hkl, hb1, hb0⟩ := s10B_row hB hOH
  simp only [tr] at hfh hfk httt htt hkl
  have h1 : env.trace sS10B = 1 := hOH.one (by decide +kernel)
  have h0 : env.trace sS0B = 0 := hOH.zero (by decide +kernel) (by decide)
  have hcons : env.trace consCol = 0 := hOH.zero (by decide +kernel) (by decide)
  have hm0 := ent_mem9 (env := env) (S := slot0X9) (by simp [slotsX9])
    (x := ⟨[sS0B, sS10B], .const 1, cellRecX xF xFh xFt, .x⟩) (by simp [slot0X9, extSlot, ents0New])
    (by simp [EntX.act, selS, CoeffExpr.sumList, evalQX, cc, h1, h0])
  have hm1 := ent_mem9 (env := env) (S := slot1X9) (by simp [slotsX9])
    (x := ⟨[sS10B], .const 1, cellRecX xFt xFth xFtt, .x⟩) (by simp [slot1X9, extSlot, ents1New])
    (by simp [EntX.act, selS, CoeffExpr.sumList, evalQX, cc, h1])
  have hm2 := ent_mem9 (env := env) (S := slot2X9) (by simp [slotsX9])
    (x := ⟨[sS10B], .const 1, cellRecX xFth xFtth xFttt, .x⟩) (by simp [slot2X9, extSlot, ents2New])
    (by simp [EntX.act, selS, CoeffExpr.sumList, evalQX, cc, h1])
  have hm3 := ent_mem9 (env := env) (S := slot3X9) (by simp [slotsX9])
    (x := ⟨[sS10B], .const 1, axRecX xE xFtth xSf1, .s⟩) (by simp [slot3X9, extSlot, ents3New])
    (by simp [EntX.act, selS, CoeffExpr.sumList, evalQX, cc, h1])
  have hftk := hd_k1 hB (h := xFt) (by decide) (by decide) hftc
  have hfthk := hd_k1 hB (h := xFth) (by decide) (by decide) hfthc
  have hek := hd_k1 hB (h := xE) (by decide) (by decide) hec
  have c0 := cell9 hOK hm0 hfk
  have c1 := cell9 hOK hm1 hftk
  have c2 := cell9 hOK hm2 hfthk
  obtain ⟨A, Bn, -, hA, -⟩ := c2
  obtain ⟨n, hn⟩ := atom_of_kc0 hD (by omega) hB (h := xFtth) (by decide) (by decide) hftthc hA
  obtain ⟨hV, h32, X, Y, hX, hY, hsl⟩ := tagAx9 hOK hm3 n hn
  -- the routed label denotes the axis atom
  have hlab : D (hdV env ⟨kLabX, vLabX⟩) = some (.atom n) := by
    rcases kind_split9 hB xFtth (by decide) (by decide) with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩
    · -- field axis: `f_tth = (0, v)`, label `(3, 64·id + 1)`
      have hk0 : env.trace xFtth.k = 0 := by rw [trace_k, k1, k2]; ring
      rw [hdV_k0 hk0, hD.base.atom] at hn
      have hnv : (env.trace xFtth.v).val = n := by injection hn with h; exact (Noun.atom.inj h)
      have hvl := hb0 k2
      simp only [tr] at hvl
      have hkl3 : env.trace kLabX = 3 := by rw [hkl, k2]; ring
      have hidb := hD.idlt _ _ hV
      have e3 : ((3 : ZMod p)).val = 3 := by simpa using val_nat (p := p) (n := 3) (by omega)
      have ev : (env.trace vLabX).val = 64 * (env.trace xIdX).val + 1 := by
        rw [hvl, show (64 : ZMod p) * env.trace xIdX + 1 =
          ((64 * (env.trace xIdX).val + 1 : ℕ) : ZMod p) by push_cast; rw [ZMod.natCast_zmod_val]]
        exact val_nat (by omega)
      have hnp : n < 2 ^ 64 := by rw [← hnv]; exact lt_of_lt_of_le (ZMod.val_lt _) hp64
      have ht := top_two_limb h32 hnp
      simp only [hdV, hkl3, e3, ev]
      rw [hD.seg _ 1 (by norm_num), hV]
      simp [segD, ht, segAx]
    · rw [hftthc] at k1; exact absurd k1.symm one_ne_zero
    · -- big axis: the label IS the handle `f_tth`
      have hvl := hb1 k2
      simp only [tr] at hvl
      have hkk : env.trace kLabX = env.trace xFtth.k := by rw [hkl, trace_k, k1, k2]; ring
      have e : hdV env ⟨kLabX, vLabX⟩ = hdV env xFtth := by simp only [hdV, hkk, hvl]
      rw [e]; exact hn
  refine ⟨?_, ?_⟩
  · simp only [RowSemX09, rowOfX9, rowOfX]
    refine ⟨c0, ?_, c1, cell9 hOK hm2 hfthk, n, hn, hlab, X, Y, ?_, hY, hsl⟩
    · rw [hdV_k0 (fh_zero_kind hB hcons), hfh]
      simpa using val_nat (p := p) (n := 10) (by omega)
    · rw [hdV_k1 hek]; exact hX
  · intro i hi hc
    simp only [kidsX9, rowOfX9, rowOfX, List.length_cons, List.length_nil] at hi ⊢
    rcases i with _ | _ | _ | i
    · simp only [List.getElem_cons_zero, hdV, httt, val_one']
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero, hdV, htt, val_one']
    · exact absurd hc (by simp [rowOfX9, CSt.sem, chainPosX9])
    · omega

end New

/-! ## 5. The segment row `s10S` -/

section Seg

/-- **`Nat.digits`' `m`-th entry** (`0` past the end): `digit m = n / b^m % b`. -/
theorem digits_getElem! {b : ℕ} (hb : 1 < b) : ∀ (m n : ℕ), (Nat.digits b n)[m]! = n / b ^ m % b
  | m, 0 => by simp
  | 0, n + 1 => by
      rw [Nat.digits_def' hb (Nat.succ_pos n)]; simp
  | m + 1, n + 1 => by
      rw [Nat.digits_def' hb (Nat.succ_pos n)]
      simp only [List.getElem!_cons_succ]
      rw [digits_getElem! hb m ((n + 1) / b), Nat.div_div_eq_div_mul, pow_succ']

/-- Limb `m` of `n` in base `B = 2^32`. -/
theorem limb_digit (n m : ℕ) : (Nat.digits Nock.Atoms.B n)[m]! = n / 2 ^ (32 * m) % 2 ^ 32 := by
  rw [digits_getElem! (by norm_num [Nock.Atoms.B]) m n]
  simp only [Nock.Atoms.B, ← pow_mul]

theorem digits_len {n : ℕ} (hn : n ≠ 0) : (Nat.digits Nock.Atoms.B n).length = top n + 1 := by
  simpa [Nock.Atoms.limbs] using top_eq_length n hn

/-- **The head limb read** (`hd = 1`): a comb atom at the odd axis `2^{m+1} − 1` is the top limb. -/
theorem limb_head {n m l : ℕ} (hn : n ≠ 0)
    (h : Noun.slot (2 ^ (m + 1) - 1) (combN n) = some (.atom l)) :
    m = top n ∧ l = n / 2 ^ (32 * m) % 2 ^ 32 := by
  have hlen := digits_len hn
  have e1 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  have p1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rcases slot_combL_atom h with ⟨j, -, ha, -⟩ | ⟨hl, ha, hx⟩ | ⟨hL, -, -⟩
  · have e2 : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
    have p2 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    omega
  · have p3 : 1 ≤ 2 ^ (Nat.digits Nock.Atoms.B n).length := Nat.one_le_two_pow
    have hpw : 2 ^ (m + 1) = 2 ^ (Nat.digits Nock.Atoms.B n).length := by omega
    have hm := Nat.pow_right_injective (le_refl 2) hpw
    refine ⟨by omega, ?_⟩
    rw [hx, List.getLast!_eq_getElem!, limb_digit]
    congr 3; omega
  · exact absurd (Nat.digits_eq_nil_iff_eq_zero.mp hL) hn

/-- **The non-head limb read** (`hd = 0`): a comb atom at the even axis `2^{m+2} − 2` is limb
`m < top n`. -/
theorem limb_nonhead {n m l : ℕ} (hn : n ≠ 0)
    (h : Noun.slot (2 ^ (m + 2) - 2) (combN n) = some (.atom l)) :
    m < top n ∧ l = n / 2 ^ (32 * m) % 2 ^ 32 := by
  have hlen := digits_len hn
  have e1 : 2 ^ (m + 2) = 4 * 2 ^ m := by ring
  have p1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rcases slot_combL_atom h with ⟨j, hj, ha, hx⟩ | ⟨hl, ha, -⟩ | ⟨hL, -, -⟩
  · have e2 : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
    have p2 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have hpw : 2 ^ m = 2 ^ j := by omega
    have hm := Nat.pow_right_injective (le_refl 2) hpw
    subst hm
    exact ⟨by omega, by rw [hx, limb_digit]⟩
  · obtain ⟨u, hu⟩ : ∃ u, (Nat.digits Nock.Atoms.B n).length = u + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hl).symm⟩
    rw [hu] at ha
    have e2 : 2 ^ (u + 1) = 2 * 2 ^ u := by ring
    have p2 : 1 ≤ 2 ^ u := Nat.one_le_two_pow
    omega
  · exact absurd (Nat.digits_eq_nil_iff_eq_zero.mp hL) hn

variable {env : Env (ZMod p)} {D : HX → Option Noun} {V : ℕ → Option ℕ} {R : Registry}

/-- The `s10S` row facts over ℕ: the limb consume pins `m ≤ top n`, the segment `m.v = segRd n m`, and a
head row reads the top limb. -/
theorem s10S_limb (hpG : p = Nock.Atoms.p) (hD : DenOKX9 p D V) (hB : BaseHoldsX9 env)
    (hOH : OneHotAt9 env sS10S) (hOK : ∀ r ∈ activeX9 env, RecOK9I D V R combN r) :
    ∃ n m hd : ℕ, V (env.trace xIdX).val = some n ∧ m < 63 ∧ mValV env = (m : ZMod p) ∧
      env.trace zAX * env.trace zBX = (if m = 0 then 1 else 0) ∧ hd ≤ 1 ∧ env.trace hdC = hd ∧
      m ≤ top n ∧ (hd = 1 → m = top n) ∧ (env.trace xM.v).val = segRd n m := by
  have hp63 : 2 ^ 63 < p := by subst hpG; norm_num [Nock.Atoms.p, Nock.Field.p]
  obtain ⟨-, -, -, -, -, -, -, -, -, haxL, hmv, -⟩ := s10S_row hB hOH
  obtain ⟨m, hm63, hmV, hpw, hz⟩ := s10S_seg_nat hB hOH
  have hb := s10S_bits hB
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  obtain ⟨-, -, -, -, -, -, qhd⟩ := hb
  obtain ⟨hd, hhd, ehd⟩ := bool_nat qhd
  have h1 : env.trace sS10S = 1 := hOH.one (by decide +kernel)
  have hlimb := ent_mem9 (env := env) (S := slot3X9) (by simp [slotsX9])
    (x := ⟨[sS10S], .const 1, limbRecX, .s⟩) (by simp [slot3X9, extSlot, ents3New])
    (by simp [EntX.act, selS, CoeffExpr.sumList, evalQX, cc, h1])
  have hw := hOK _ hlimb (pre9_cls (by simp [recClass, limbRecX]))
  simp only [RecOK9, recClass, limbRecX, List.map_cons, List.map_nil, reVal, List.length_cons,
    List.length_nil, WalkAOK9] at hw
  norm_num at hw
  obtain ⟨n, hVn, hsl⟩ := hw
  have hn0 : n ≠ 0 := hD.vpos _ _ hVn
  simp only [tr] at haxL hmv hpw ehd
  refine ⟨n, m, hd, hVn, hm63, hmV, hz, hhd, ehd, ?_⟩
  rcases (by omega : hd = 0 ∨ hd = 1) with rfl | rfl
  · -- non-head: axis `2^{m+2} − 2`
    have eax : env.trace axLX = 2 * 2 ^ (m + 1) - 2 := by
      rw [haxL, ehd, hpw]; push_cast; ring
    rcases (by omega : m ≤ 61 ∨ m = 62) with hm | rfl
    · have hle : 2 ^ (m + 2) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have p2 : 2 ≤ 2 ^ (m + 2) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have ev : (env.trace axLX).val = 2 ^ (m + 2) - 2 := by
        rw [eax, show (2 : ZMod p) * 2 ^ (m + 1) - 2 = ((2 ^ (m + 2) - 2 : ℕ) : ZMod p) by
          rw [Nat.cast_sub p2]; push_cast; ring]
        exact val_nat (by omega)
      rw [ev] at hsl
      obtain ⟨hmt, hl⟩ := limb_nonhead hn0 hsl
      refine ⟨by omega, fun h => absurd h (by norm_num), ?_⟩
      have hlt : (env.trace limbX).val < 2 ^ 32 := by rw [hl]; exact Nat.mod_lt _ (by norm_num)
      have em : env.trace xM.v = (((env.trace limbX).val + 2 ^ 32 : ℕ) : ZMod p) := by
        rw [hmv, ehd]; push_cast; rw [ZMod.natCast_zmod_val]; norm_num
      rw [em, val_nat (by omega)]
      simp only [segRd, show m ≠ top n by omega, ite_false, hl]
    · exfalso
      subst hpG
      refine wrap62 (a := (env.trace axLX).val) (ZMod.val_lt _) ?_ _ _ hsl
      rw [ZMod.natCast_zmod_val, eax]; norm_num
  · -- head: axis `2^{m+1} − 1`
    have p2 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
    have hle : 2 ^ (m + 1) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have ev : (env.trace axLX).val = 2 ^ (m + 1) - 1 := by
      rw [haxL, ehd, hpw, show (((1 : ℕ) : ZMod p)) * (2 ^ (m + 1) - 1) + (1 - ((1 : ℕ) : ZMod p)) *
          (2 * 2 ^ (m + 1) - 2) = ((2 ^ (m + 1) - 1 : ℕ) : ZMod p) by
        rw [Nat.cast_sub p2]; push_cast; ring]
      exact val_nat (by omega)
    rw [ev] at hsl
    obtain ⟨hmt, hl⟩ := limb_head hn0 hsl
    refine ⟨by omega, fun _ => hmt, ?_⟩
    have em : env.trace xM.v = env.trace limbX := by rw [hmv, ehd]; push_cast; ring
    rw [em, hl]
    simp only [segRd, hmt, ite_true, add_zero]

/-- **Design S6, `s10S`** (the segment pseudo-row): the limb consume `(id, axL, 0, l)` through
`slot_combL_atom` (and `wrap62` at `m = 62`, Goldilocks) pins `m ≤ top n` and the segment
`m = (0, segRd n m)`; the label decodes to `segAx n m` (kind 3 exactly through `DenOKX9.idlt`; kind 2 is a
head, `m = top n`, through the guard and `DenOKX9.k2`); the routed child label denotes `nxtAx n m`; the
walk pair (`pr = 1 − z1`, `op5G`'s cell kinds) or, at `z1`, the substitution gives the read. -/
theorem sem_s10S (hpG : p = Nock.Atoms.p) (hD : DenOKX9 p D V) (hB : BaseHoldsX9 env)
    (hOH : OneHotAt9 env sS10S) (hOK : ∀ r ∈ activeX9 env, RecOK9I D V R combN r) :
    RowSemX9 p D V R (rowOfX9 env .s10S) := by
  have hp63 : 2 ^ 63 < p := by subst hpG; norm_num [Nock.Atoms.p, Nock.Field.p]
  obtain ⟨n, m, hd, hVn, hm63, hmV, hz, hhd, ehd, hmt, hhdt, hseg⟩ := s10S_limb hpG hD hB hOH hOK
  obtain ⟨hkb, hdec3, hdec2, -, -, -, -, -, -, -, -, hz1, hmk, hpr, ⟨hs1k, hs1v, hs2k, hs2v⟩, hz1h,
    hkl, hvl⟩ := s10S_row hB hOH
  simp only [tr] at hz1 hmk hpr hs1k hs1v hs2k hs2v hz1h hkl hvl hdec3 hdec2 hz
  have hidlt := hD.idlt _ _ hVn
  obtain ⟨-, fc, -⟩ := kindF9 hB
  have e3 : ((3 : ZMod p)).val = 3 := by simpa using val_nat (p := p) (n := 3) (by omega)
  have hm : hdV env xM = (0, segRd n m) := by simp only [hdV, hmk, ZMod.val_zero, hseg]
  -- the routed child label
  have hlab : D (hdV env ⟨kLabX, vLabX⟩) = some (.atom (nxtAx n m)) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · simp only [ite_true] at hz
      rw [hz] at hkl hvl
      have e : hdV env ⟨kLabX, vLabX⟩ = (0, 1) := by
        simp only [hdV]; rw [hkl, hvl]; simp [val_one']
      rw [e, hD.base.atom, nxtAx_zero]
    · simp only [Nat.pos_iff_ne_zero.mp hm1, ite_false] at hz
      rw [hz] at hkl hvl
      have evF : env.trace vLabX = ((64 * (env.trace xIdX).val + (m - 1) : ℕ) : ZMod p) := by
        rw [hvl, hmV]; push_cast [Nat.cast_sub (show 1 ≤ m by omega)]; rw [ZMod.natCast_zmod_val]; ring
      have e : hdV env ⟨kLabX, vLabX⟩ = (3, 64 * (env.trace xIdX).val + (m - 1)) := by
        simp only [hdV]; rw [evF, val_nat (by omega), hkl]; norm_num [e3]
      rw [e, hD.seg _ _ (by omega), hVn]
      simp only [Option.bind_some, segD, show m - 1 ≤ top n by omega, ite_true, Option.map_some]
      rw [segAx_next n m hmt hm1]
  -- the formula
  have hfk : env.trace xF.k = kcV env xF + 2 := by rw [trace_k, hkb]; ring
  have hf1 : (hdV env xF).1 ≠ 1 := by
    rcases mul_eq_zero.mp fc with hc | hc
    · simp only [hdV]; rw [hfk, hc, zero_add, val_two (by omega)]; norm_num
    · have hc1 : kcV env xF = 1 := by linear_combination hc
      simp only [hdV]; rw [hfk, hc1, show (1 : ZMod p) + 2 = 3 by norm_num, e3]; norm_num
  have hDf : D (hdV env xF) ≠ none → D (hdV env xF) = some (.atom (segAx n m)) := by
    intro hne
    rcases mul_eq_zero.mp fc with hc | hc
    · obtain ⟨hv, hh⟩ := hdec2 hc
      have hd1 : hd = 1 := by
        rcases (by omega : hd = 0 ∨ hd = 1) with rfl | rfl
        · rw [hh] at ehd; simp at ehd
        · rfl
      have hm' := hhdt hd1
      have hk2 : hdV env xF = (2, (env.trace xIdX).val) := by
        simp only [hdV]; rw [hfk, hc, zero_add, val_two (by omega), hv]
      rw [hk2] at hne ⊢
      obtain ⟨X, hX⟩ : ∃ X, D (2, (env.trace xIdX).val) = some X := Option.ne_none_iff_exists'.mp hne
      obtain ⟨n', rfl, -⟩ := hD.base.big _ _ hX
      have h2 := hD.k2 _ _ hX
      rw [hVn] at h2
      cases Option.some.inj h2
      rw [hX, hm', segAx_top]
    · have hc1 : kcV env xF = 1 := by linear_combination hc
      have ev : (env.trace xF.v).val = 64 * (env.trace xIdX).val + m := by
        rw [hdec3 hc1, hmV, show (64 : ZMod p) * env.trace xIdX + (m : ZMod p) =
          ((64 * (env.trace xIdX).val + m : ℕ) : ZMod p) by push_cast; rw [ZMod.natCast_zmod_val]]
        exact val_nat (by omega)
      have hk3 : hdV env xF = (3, 64 * (env.trace xIdX).val + m) := by
        simp only [hdV]; rw [hfk, hc1, show (1 : ZMod p) + 2 = 3 by norm_num, e3, ev]
      rw [hk3, hD.seg _ _ (by omega), hVn]
      simp [segD, hmt]
  -- the pair read
  have hpair : (segRd n m = 1 ∧ hdV env xFtth = hdV env xS ∧ hdV env xFttt = hdV env xE) ∨
      ∃ S E X Y, D (hdV env xS) = some S ∧ D (hdV env xE) = some E ∧ D (hdV env xFtth) = some X ∧
        D (hdV env xFttt) = some Y ∧ Noun.slot (segRd n m) S = some X ∧
          Noun.slot (segRd n m) E = some Y := by
    have qz := arith_of_base9 hB (g := boolG (cc z1X)) (by decide +kernel)
    simp only [boolG, cc, evalQX, Rat.cast_one] at qz
    rcases mul_eq_zero.mp qz with h0 | h0
    · right
      have hpr1 : env.trace prX = 1 := by rw [hpr, h0, sub_zero]
      have gs1 := arith_of_base9 hB (g := .mul (cc prX) (oneMinus (kcE xSf1))) (by decide +kernel)
      have gs2 := arith_of_base9 hB (g := .mul (cc prX) (oneMinus (kcE xSf2))) (by decide +kernel)
      simp only [cc, oneMinus, kcE, kbE, evalQX, Rat.cast_one, Rat.cast_ofNat, hpr1, one_mul] at gs1 gs2
      have kc1 : kcV env xSf1 = 1 := by simp only [kcV]; linear_combination -gs1
      have kc2 : kcV env xSf2 = 1 := by simp only [kcV]; linear_combination -gs2
      have k1 := hd_k1 hB (h := xSf1) (by decide) (by decide) kc1
      have k2 := hd_k1 hB (h := xSf2) (by decide) (by decide) kc2
      have hS : hdV env xS = (1, (env.trace xSf1.v).val) := by
        simp only [hdV]; rw [← hs1k, k1, hs1v, val_one']
      have hE : hdV env xE = (1, (env.trace xSf2.v).val) := by
        simp only [hdV]; rw [← hs2k, k2, hs2v, val_one']
      have hmem : ∀ r ∈ pairRecsX env (slot2X9 (F := ℚ)), r ∈ activeX9 env := fun r hr =>
        List.mem_flatMap.mpr ⟨slot2X9, by simp [slotsX9], List.mem_append_right _ hr⟩
      have hr1 := hOK _ (hmem ((walkRecX xSf1 xM.v xFtth).map (reVal env), .p)
        (by simp [pairRecsX, slot2X9, extSlot, slot2X, hpr1])) (pre9_off (by decide))
      have hr2 := hOK _ (hmem ((walkRecX xSf2 xM.v xFttt).map (reVal env), .p)
        (by simp [pairRecsX, slot2X9, extSlot, slot2X, hpr1])) (pre9_off (by decide))
      simp only [RecOK9, recClass, walkRecX, walkRec, recOf, List.map_cons, List.map_nil, reVal, RecOK,
        reduceCtorEq, ite_false] at hr1 hr2
      obtain ⟨S, X, hS', hX, hsx⟩ := hr1
      obtain ⟨E, Y, hE', hY, hey⟩ := hr2
      rw [hseg] at hsx hey
      exact ⟨S, E, X, Y, by rw [hS]; exact hS', by rw [hE]; exact hE', hX, hY, hsx, hey⟩
    · left
      have hz1v : env.trace z1X = 1 := by linear_combination h0
      obtain ⟨hmv1, -⟩ := hz1 hz1v
      obtain ⟨a1, a2, a3, a4⟩ := hz1h hz1v
      refine ⟨?_, by simp only [hdV, a1, a2], by simp only [hdV, a3, a4]⟩
      rw [← hseg, hmv1, val_one']
  refine ⟨?_, ?_⟩
  · simp only [RowSemX09, rowOfX9, rowOfX]
    exact ⟨hf1, fun hne => ⟨(env.trace xIdX).val, n, m, hVn, hmt, hDf hne, hm, hlab, hpair⟩⟩
  · intro i hi hc
    simp only [kidsX9, rowOfX9, List.length_cons, List.length_nil] at hi
    rcases i with _ | _ | i
    · exact absurd hc (by simp [rowOfX9, CSt.sem, chainPosX9])
    · exact absurd hc (by simp [rowOfX9, CSt.sem, chainPosX9])
    · omega

end Seg

/-! ## 6. LINK bridges: old rows read the J-8 record list -/

section Link
variable {env : Env (ZMod p)}

/-- The `RowSemChipX` record list of one slot. -/
def slotRecs (env : Env (ZMod p)) (S : SlotX ℚ) : List (List ℕ × Bal) :=
  ((S.ents.filter fun x => decide (evalQX x.act env = 1)).map fun x =>
    (x.rcd.map (reVal env), x.bal)) ++ pairRecsX env S

theorem slotRecs_ext (S : SlotX ℚ) (es : List (EntX ℚ)) (ps : List ℕ)
    (hes : ∀ x ∈ es, evalQX x.act env ≠ 1) : slotRecs env (extSlot S es ps) = slotRecs env S := by
  have h0 : es.filter (fun x => decide (evalQX x.act env = 1)) = [] :=
    List.filter_eq_nil_iff.mpr fun x hx => by simpa using hes x hx
  simp only [slotRecs, extSlot, List.filter_append, h0, List.append_nil, pairRecsX]

/-- **LINK bridge (a): on a row with the new states off, the twin consumes exactly the J-8 records.** -/
theorem activeX9_eq (hN : NewOff env) : activeX9 env = activeX env := by
  obtain ⟨h0, h1, h2⟩ := hN
  have e : ∀ x ∈ ([] : List (EntX ℚ)), evalQX x.act env ≠ 1 := by simp
  have e0 : ∀ x ∈ (ents0New : List (EntX ℚ)), evalQX x.act env ≠ 1 := by
    simp [ents0New, EntX.act, selS, CoeffExpr.sumList, evalQX, cc, h0, h1]
  have e1 : ∀ x ∈ (ents1New : List (EntX ℚ)), evalQX x.act env ≠ 1 := by
    simp [ents1New, EntX.act, selS, CoeffExpr.sumList, evalQX, cc, h0, h1]
  have e2 : ∀ x ∈ (ents2New : List (EntX ℚ)), evalQX x.act env ≠ 1 := by
    simp [ents2New, EntX.act, selS, CoeffExpr.sumList, evalQX, cc, h1]
  have e3 : ∀ x ∈ (ents3New : List (EntX ℚ)), evalQX x.act env ≠ 1 := by
    simp [ents3New, EntX.act, selS, CoeffExpr.sumList, evalQX, cc, h1, h2]
  have k : activeX9 env = (slotsX9 (F := ℚ)).flatMap (slotRecs env) := rfl
  have k' : activeX env = (ChipHX.slotsX (F := ℚ)).flatMap (slotRecs env) := rfl
  rw [k, k']
  simp only [slotsX9, ChipHX.slotsX, slot0X9, slot1X9, slot2X9, slot3X9, List.flatMap_cons, List.flatMap_nil,
    slotRecs_ext _ _ _ e0, slotRecs_ext _ _ _ e1, slotRecs_ext _ _ _ e2, slotRecs_ext _ _ _ e3]

/-- The J-8 slots carry no `TAG_ax`-shaped (8 entries, tag `5`) record: their only 8-entry record is the jet
key (tag `3`), and their pairs are 4-entry. -/
theorem slotsX_shape : (ChipHX.slotsX (F := ℚ)).all (fun S =>
    S.ents.all (fun x => x.rcd.length != 8 || x.rcd.getLast? == some (.k 3)) &&
      (match S.pair with | some (_, a, c, _) => a.length != 8 && c.length != 8 | none => true)) = true := by
  decide +kernel

/-- **No old-row record is of class `1`**. -/
theorem recClass_old {r : List ℕ × Bal} (hr : r ∈ activeX env) : recClass r ≠ 1 := by
  have hsh := List.all_eq_true.mp slotsX_shape
  obtain ⟨S, hS, hr⟩ := List.mem_flatMap.mp hr
  have h1 := hsh S hS
  simp only [Bool.and_eq_true] at h1
  obtain ⟨hE, hP⟩ := h1
  have len8 : ∀ (l : List ℕ) (bl : Bal), l.length ≠ 8 → recClass (l, bl) ≠ 1 := by
    intro l bl hl hc
    by_cases hs : bl = .s
    · subst hs
      simp only [recClass] at hc
      split_ifs at hc with h8
      · exact hl h8.1
      · omega
    · have : recClass (l, bl) = 0 := by cases bl <;> simp_all [recClass]
      omega
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    have hx' := List.all_eq_true.mp hE x (List.mem_filter.mp hx).1
    by_cases hl : x.rcd.length = 8
    · simp only [hl, bne_self_eq_false, Bool.false_or, beq_iff_eq] at hx'
      intro hc
      obtain ⟨st, ex, l, bl⟩ := x
      by_cases hs : bl = Bal.s
      · subst hs
        simp only [recClass] at hc
        simp only [List.length_map] at hc
        simp only at hx' hl
        split_ifs at hc with h8
        all_goals first
          | omega
          | (rw [List.getLast?_map, hx'] at h8; simp [reVal] at h8)
      · have : recClass ((l.map (reVal env)), bl) = 0 := by cases bl <;> simp_all [recClass]
        simp only at hc
        rw [this] at hc
        exact absurd hc (by decide)
    · exact len8 _ _ (by simpa using hl)
  · unfold pairRecsX at hr
    cases hp : S.pair with
    | none => simp [hp] at hr
    | some q =>
      obtain ⟨fl, a, c, bl⟩ := q
      simp only [hp, Bool.and_eq_true, bne_iff_ne, ne_eq] at hr hP
      by_cases hf : env.trace fl = 1
      · simp only [hf, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact len8 _ _ (by simpa using hP.1)
        · exact len8 _ _ (by simpa using hP.2)
      · simp [hf] at hr

end Link

end Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9

open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 in
#print axioms rowSemX9_old
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 in
#print axioms sem_s0B
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 in
#print axioms sem_s10B
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 in
#print axioms sem_s10S
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 in
#print axioms activeX9_eq
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 in
#print axioms recClass_old
