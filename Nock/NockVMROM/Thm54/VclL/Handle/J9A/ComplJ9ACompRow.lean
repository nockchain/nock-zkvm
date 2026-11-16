/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ACompRow.lean

* `colX9 H pd idOf l fst lst` — the honest columns of a J-9 A row `l : LX9`:
    - `old`: J-8's `colX` verbatim (it is `0` on every column `≥ 69`, so the fourteen new columns
      `123..136` are `0`; `colX9_old`, `colX9_old_new`; the RAP order of `ComplJ9AComp.emb9` is
      `rapOf9`, `rapOf9_old`);
    - `s0B` / `s10B`: J-8's `colX` on `17..122` with the J-8 one-hot `0..16` cleared, the new selector,
      `xId = idOf n` and (on `s10B`) the chain-root label `(kLab, vLab)`;
    - `s10S`: the segment pseudo-row (formula handle `(2, id)` on the top segment of a big
      `n`, `(3, 64·id + m)` otherwise; the six bits of `m` on `β, fast, l₁.k, l₂.k, m₄, m₅`; `pw1, pw2,
      pw, zA, zB` on `v, v2, w, inv4, ax2`; `hd = [m = top n]`, limb, limb axis, segment `segRd n m`,
      next label `(3(1 − [m=0]), [m=0] + (1 − [m=0])(64·id + m − 1))`).
  * `old_gates`: every twin arithmetic and equality base gate vanishes at an old row with `RowOKX`.
  * `s0B_gates`, `s10B_gates`, `s10S_gates`: the same at the new rows, from `SemN9` and explicit side
    hypotheses.
  Base gates read only the current row (the honest env repeats it as `traceNext`, as `hEnvX` does).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AComp
import Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AGen

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow

open Nock Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle (slot_cell)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc notC selS prodL heq hpub EqG Opnd consCol)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 ChipSt9 SemN9 segRow)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AComp (zeroAt evalQX_zeroAt arith9_class eq9_class)
open Nock.J9A.NounAx (top segAx segRd)

noncomputable section

/-! ## 1. The honest columns -/

/-- Bit `i` of `m`. -/
def bitN (m i : ℕ) : ℕ := m / 2 ^ i % 2

section Cols
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

/-- **`s0B`** (op 0, axis atom `n ≥ 2^62`): J-8's columns `17..122`, J-8 one-hot cleared, `s0B = 1`,
`xId = idOf n`. -/
def colS0B (r : RowNX) (n : ℕ) (fst lst : F) : ℕ → F := fun c =>
  if c < 17 then 0 else if c < 123 then colX H pd r fst lst c
  else if c = 123 then 1 else if c = 126 then (idOf n : F) else 0

/-- **`s10B`** (op 10, axis atom `n ≥ 2^62`): as `s0B`, plus the chain-root label: `(2, f_tth.v)` on a
big axis (`p ≤ n`), `(3, 64·id + 1)` on a field axis. -/
def colS10B (r : RowNX) (n : ℕ) (fst lst : F) : ℕ → F := fun c =>
  if c < 17 then 0 else if c < 123 then colX H pd r fst lst c
  else if c = 124 then 1 else if c = 126 then (idOf n : F)
  else if c = 127 then (if ringChar F ≤ n then 2 else 3)
  else if c = 128 then (if ringChar F ≤ n then hv H r.ftth else ((64 * idOf n + 1 : ℕ) : F))
  else 0

/-- **`s10S`** (segment `m` of the axis `n`; the noun row `r = segRow n m s e`). -/
def colS10S (n m : ℕ) (r : RowNX) (fst lst : F) : ℕ → F := fun c =>
  let b : ℕ → F := fun i => ((bitN m i : ℕ) : F)
  let hd : F := if m = top n then 1 else 0
  let z1 : F := if segRd n m = 1 then 1 else 0
  let pw1 : F := (1 + b 0) * ((1 + 3 * b 1) * (1 + 15 * b 2))
  let pw2 : F := (1 + 255 * b 3) * ((1 + 65535 * b 4) * (1 + 4294967295 * b 5))
  let pw : F := 2 * (pw1 * pw2)
  if c < 17 then 0
  else if c = 19 then z1 else if c = 20 then pw1 else if c = 21 then b 0 else if c = 22 then pw2
  else if c = 23 then pw else if c = 24 then 1 - z1
  else if c = 27 then (if m = top n ∧ ringChar F ≤ n then 2 else 3)
  else if c = 28 then (if m = top n ∧ ringChar F ≤ n then (idOf n : F) else ((64 * idOf n + m : ℕ) : F))
  else if c = 50 then 1
  else if c < 61 then colX H pd r fst lst c
  else if c = 61 then b 1
  else if c = 62 then (1 - b 0) * ((1 - b 1) * (1 - b 2))
  else if c = 63 then (1 - b 3) * ((1 - b 4) * (1 - b 5))
  else if c = 65 then b 2 else if c = 67 then b 3
  else if c < 125 then 0
  else if c = 125 then 1 else if c = 126 then (idOf n : F)
  else if c = 127 then (if m = 0 then 0 else 3)
  else if c = 128 then (if m = 0 then 1 else ((64 * idOf n + (m - 1) : ℕ) : F))
  else if c = 129 then b 4 else if c = 130 then b 5 else if c = 131 then hd
  else if c = 132 then b 0 * (b 1 * b 2) else if c = 133 then b 3 * (b 4 * b 5)
  else if c = 134 then ((n / 2 ^ (32 * m) % 2 ^ 32 : ℕ) : F)
  else if c = 135 then hd * (pw - 1) + (1 - hd) * (2 * pw - 2)
  else if c = 136 then ((segRd n m : ℕ) : F)
  else 0

/-- **The honest round-0 columns of a J-9 A row** (chip numbering `0..136`). -/
def colX9 (l : LX9) (fst lst : F) : ℕ → F :=
  match l.chip with
  | .old => colX H pd l.rn fst lst
  | .s0B => colS0B H pd idOf l.rn l.n fst lst
  | .s10B => colS10B H pd idOf l.rn l.n fst lst
  | .s10S => colS10S H pd idOf l.n l.m l.rn fst lst

/-- The honest base environment (base gates read the current row and the publics). -/
def hEnvX9 (l : LX9) (fst lst : F) (pub : ℕ → F) : Env F :=
  ⟨colX9 H pd idOf l fst lst, colX9 H pd idOf l fst lst, fun _ => 0, pub⟩

/-- The RAP column order of the twin (`ChipHX9RAP.permX9`): RAP column `c` holds chip column
`invPermX9 c`. -/
def invPermX9 (c : ℕ) : ℕ := if c < 69 then c else if c < 83 then c + 54 else c - 14

def rapOf9 (col : ℕ → F) : ℕ → F := fun c => col (invPermX9 c)

end Cols

/-! ## 2. Old rows: the lift -/

section Old
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

theorem colX_ge69 (r : RowNX) (fst lst : F) (c : ℕ) (hc : 69 ≤ c) : colX H pd r fst lst c = 0 := by
  simp only [colX, show ¬ c < 17 by omega, show ¬ c = 17 by omega, show ¬ c = 18 by omega,
    show ¬ c = 19 by omega, show ¬ c = 20 by omega, show ¬ c = 21 by omega, show ¬ c = 22 by omega,
    show ¬ c = 23 by omega, show ¬ c = 24 by omega, show ¬ c < 49 by omega, show ¬ c < 61 by omega,
    show ¬ c = 61 by omega, show ¬ c = 62 by omega, show ¬ c = 63 by omega, show ¬ c = 64 by omega,
    show ¬ c < 69 by omega, if_false]

/-- **Old-row lift**: an old row's twin columns are J-8's `colX`. -/
theorem colX9_old (l : LX9) (fst lst : F) (h : l.chip = .old) :
    colX9 H pd idOf l fst lst = colX H pd l.rn fst lst := by
  simp only [colX9, h]

/-- … and the fourteen new columns are `0`. -/
theorem colX9_old_new (l : LX9) (fst lst : F) (h : l.chip = .old) (c : ℕ) (hc : 123 ≤ c) :
    colX9 H pd idOf l fst lst c = 0 := by
  rw [colX9_old H pd idOf l fst lst h]; exact colX_ge69 H pd l.rn fst lst c (by omega)

theorem permX9_inv (c : ℕ) (hc : c < 137) : invPermX9 (ChipHX9.permX9 c) = c := by
  simp only [invPermX9, ChipHX9.permX9]; split_ifs <;> omega

/-- `rapOf9` reads chip column `c` at RAP column `permX9 c`. -/
theorem rapOf9_perm (col : ℕ → F) (c : ℕ) (hc : c < 137) : rapOf9 col (ChipHX9.permX9 c) = col c := by
  simp only [rapOf9, permX9_inv c hc]

/-- **Old-row lift in the RAP order** (`ComplJ9AComp.emb9`'s convention): RAP `0..68` = J-8 `0..68`,
RAP `69..82` = `0`, RAP `83..136` = J-8 `69..122`. -/
theorem rapOf9_old (l : LX9) (fst lst : F) (h : l.chip = .old) (c : ℕ) :
    rapOf9 (colX9 H pd idOf l fst lst) c =
      if c < 69 then colX H pd l.rn fst lst c else if c < 83 then 0 else colX H pd l.rn fst lst (c - 14) := by
  simp only [rapOf9, invPermX9, colX9_old H pd idOf l fst lst h]
  split_ifs with h1 h2
  · rfl
  · exact colX_ge69 H pd l.rn fst lst _ (by omega)
  · rfl

end Old

/-! ## 3. Twin gates from J-8 gates (arithmetic and equality only) -/

section Twin
variable {F : Type} [Field F]

/-- **The twin's arithmetic and equality gates hold at a row whose columns `≥ 123` are zero and where
J-8's arithmetic and equality gates hold** (the arithmetic / equality half of
`ComplJ9AComp.base9_of_base8`). -/
theorem twin_of_J8 {env : Env F} (hA : ∀ g ∈ (arithGatesX : List (CoeffExpr ℚ)), evalQX g env = 0)
    (hE : ∀ g ∈ (eqGatesX : List (EqG ℚ)), evalQX g.gate env = 0)
    (hz : ∀ c, 123 ≤ c → env.trace c = 0 ∧ env.traceNext c = 0) :
    (∀ g ∈ arithGatesX9, evalQX g env = 0) ∧ (∀ g ∈ (eqGatesX9 : List (EqG ℚ)), evalQX g.gate env = 0) := by
  have hN : NewOff env := ⟨(hz _ (by decide)).1, (hz _ (by decide)).1, (hz _ (by decide)).1⟩
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · have hc := List.all_eq_true.mp arith9_class g hg
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with (hc | hc) | hc
    · exact hA g hc
    · exact evalQX_zeroAt hz g hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · have h := hA (.sub (selS (List.range nStates)) (.const 1)) (by decide +kernel)
        simp only [oneHotSumX9, evalQX, evalQX_selS_zero newStates hN.zero, add_zero]
        simp only [evalQX] at h
        exact h
      · have h := hA (.mul (kcE xF) (kbE xF)) (by decide +kernel)
        simp only [kindRelaxX9, oneMinus, cc, evalQX, hN.2.2, Rat.cast_one, sub_zero, one_mul]
        simp only [evalQX] at h
        exact h
      · have h := hA svXF8 (by decide +kernel)
        simp only [svXFX9, oneMinus, prodL, List.foldr, cc, evalQX, hN.2.2, Rat.cast_one, sub_zero,
          one_mul, zero_mul, add_zero]
        exact h
      · have h := hA prGateX (by decide +kernel)
        simp only [prGateX9, cc, evalQX, hN.2.2, zero_mul, sub_zero]
        exact h
  · have hc := List.all_eq_true.mp eq9_class g hg
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | hc
    · exact hE g hc
    · exact evalQX_zeroAt hz _ hc

end Twin

/-! ## 4. Old rows: every twin arithmetic / equality gate -/

section OldGates
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

/-- **Old rows**: at an old J-9 A row with J-8's `RowOKX`, every arithmetic and equality base gate of the
twin vanishes at the honest environment. -/
theorem old_gates (l : LX9) (fst lst : F) (pub : ℕ → F) (hold : l.chip = .old)
    (hH : HdlOK (ringChar F) H) (hp : 16 ≤ ringChar F) (hok : RowOKX (ringChar F) l.rn)
    (hpair : isPair H l.rn → PairOK (F := F) (pd l.rn)) (hpub : PubOK H l.rn fst pub) :
    (∀ g ∈ arithGatesX9, evalQX g (hEnvX9 H pd idOf l fst lst pub) = 0) ∧
      (∀ g ∈ (eqGatesX9 : List (EqG ℚ)), evalQX g.gate (hEnvX9 H pd idOf l fst lst pub) = 0) := by
  have he : hEnvX9 H pd idOf l fst lst pub = hEnvX H pd l.rn fst lst pub := by
    simp only [hEnvX9, hEnvX, colX9_old H pd idOf l fst lst hold]
  rw [he]
  obtain ⟨hA, hE⟩ := arith_eq_hold H pd l.rn fst lst pub hH hp hok hpair hpub
  exact twin_of_J8 hA hE fun c hc =>
    ⟨colX_ge69 H pd l.rn fst lst c (by omega), colX_ge69 H pd l.rn fst lst c (by omega)⟩

end OldGates

/-! ## 5. -/

/-- A syntactic "this expression is `0` when every column of `Z` is `0`". -/
def zeroOn (Z : List ℕ) : CoeffExpr ℚ → Bool
  | .const c => decide (c = 0)
  | .var .traceCur i => decide (i ∈ Z)
  | .var .traceNext i => decide (i ∈ Z)
  | .var _ _ => false
  | .add a b => zeroOn Z a && zeroOn Z b
  | .sub a b => zeroOn Z a && zeroOn Z b
  | .mul a b => zeroOn Z a || zeroOn Z b
  | .neg a => zeroOn Z a
  | .pow a n => decide (0 < n) && zeroOn Z a

section Zero
variable {F : Type} [Field F]

theorem evalQX_zeroOn (Z : List ℕ) {env : Env F} (hz : ∀ c ∈ Z, env.trace c = 0 ∧ env.traceNext c = 0) :
    ∀ g : CoeffExpr ℚ, zeroOn Z g = true → evalQX g env = 0
  | .const c, h => by simp only [zeroOn, decide_eq_true_eq] at h; simp [evalQX, h]
  | .var .traceCur i, h => by simp only [zeroOn, decide_eq_true_eq] at h; exact (hz i h).1
  | .var .traceNext i, h => by simp only [zeroOn, decide_eq_true_eq] at h; exact (hz i h).2
  | .var .challenge _, h => by simp [zeroOn] at h
  | .var .publicVal _, h => by simp [zeroOn] at h
  | .add a b, h => by
      simp only [zeroOn, Bool.and_eq_true] at h
      simp only [evalQX, evalQX_zeroOn Z hz a h.1, evalQX_zeroOn Z hz b h.2, add_zero]
  | .sub a b, h => by
      simp only [zeroOn, Bool.and_eq_true] at h
      simp only [evalQX, evalQX_zeroOn Z hz a h.1, evalQX_zeroOn Z hz b h.2, sub_zero]
  | .mul a b, h => by
      simp only [zeroOn, Bool.or_eq_true] at h
      rcases h with h | h
      · simp only [evalQX, evalQX_zeroOn Z hz a h, zero_mul]
      · simp only [evalQX, evalQX_zeroOn Z hz b h, mul_zero]
  | .neg a, h => by
      simp only [zeroOn] at h
      simp only [evalQX, evalQX_zeroOn Z hz a h, neg_zero]
  | .pow a n, h => by
      simp only [zeroOn, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [evalQX, evalQX_zeroOn Z hz a h.2]
      exact zero_pow (by omega)

end Zero

/-- Columns `0` on an `s0B` row. -/
def Z0B : List ℕ := List.range 17 ++ [19, 21, 24, 61, 64, 65, 67, 124, 125] ++ List.range' 127 10
/-- Columns `0` on an `s10B` row. -/
def Z10B : List ℕ := List.range 17 ++ [19, 21, 24, 61, 64, 65, 67, 123, 125] ++ List.range' 129 8
/-- Columns `0` on an `s10S` row. -/
def Z10S : List ℕ := List.range 17 ++ [64, 66, 68, 123, 124]

/-- The non-kind arithmetic gates of the twin not killed by `Z0B`. -/
def handA0B : List (CoeffExpr ℚ) :=
  [.sub (cc consCol) (kcE xFh), kbE xFh, oneHotSumX9, kindRelaxX9, svXFX9, boolG (cc sS0B)] ++ s0BG
def handE0B : List (EqG ℚ) := claimEq ++ [⟨cc sS0B, xFh.v, .cst 0⟩]

def handA10B : List (CoeffExpr ℚ) :=
  [.sub (cc consCol) (kcE xFh), kbE xFh, oneHotSumX9, kindRelaxX9, svXFX9, boolG (cc sS10B)] ++ s10BG ++
    kidKindNew
def handE10B : List (EqG ℚ) := claimEq ++ [⟨cc sS10B, xFh.v, .cst 10⟩] ++ s10BEq

def handA10S1 : List (CoeffExpr ℚ) :=
  [boolG (cc z1X), boolG (cc betaX), boolG (cc fastX), boolG (cc xL1.k), boolG (cc xL2.k),
   .sub (cc consCol) (kcE xFh), kbE xFh, .mul (cc prX) (cc xM.k), .mul (cc prX) (oneMinus (kcE xSf1)),
   .mul (cc prX) (oneMinus (kcE xSf2)), oneHotSumX9, kindRelaxX9, svXFX9, prGateX9,
   boolG (cc sS10S), boolG (cc m4X), boolG (cc m5X), boolG (cc hdC), decodeG9]
def handA10S : List (CoeffExpr ℚ) := handA10S1 ++ s10SG
def handE10S : List (EqG ℚ) := claimEq ++ s10SEq

theorem arith_s0B_class : (arithGatesX9.all fun g => zeroOn Z0B g ||
    decide (g ∈ (kindG : List (CoeffExpr ℚ))) || decide (g ∈ handA0B)) = true := by decide +kernel
theorem eq_s0B_class : ((eqGatesX9 : List (EqG ℚ)).all fun g => zeroOn Z0B g.gate ||
    decide (g ∈ handE0B)) = true := by decide +kernel
theorem arith_s10B_class : (arithGatesX9.all fun g => zeroOn Z10B g ||
    decide (g ∈ (kindG : List (CoeffExpr ℚ))) || decide (g ∈ handA10B)) = true := by decide +kernel
theorem eq_s10B_class : ((eqGatesX9 : List (EqG ℚ)).all fun g => zeroOn Z10B g.gate ||
    decide (g ∈ handE10B)) = true := by decide +kernel
theorem arith_s10S_class : (arithGatesX9.all fun g => zeroOn Z10S g ||
    decide (g ∈ (kindG : List (CoeffExpr ℚ))) || decide (g ∈ handA10S)) = true := by decide +kernel
theorem eq_s10S_class : ((eqGatesX9 : List (EqG ℚ)).all fun g => zeroOn Z10S g.gate ||
    decide (g ∈ handE10S)) = true := by decide +kernel

/-- The changed J-8 kind gate `kc(f)·kb(f)` is not a twin gate. -/
theorem kcf_not_mem : (.mul (kcE xF) (kbE xF) : CoeffExpr ℚ) ∉ arithGatesX9 := by decide +kernel

/-! ## 6. Generic assembly for the new rows -/

section Gen
variable {F : Type} [Field F]

/-- The environment of a row's columns (base gates read the current row; `traceNext` repeats it). -/
def mkEnv (col : ℕ → F) (pub : ℕ → F) : Env F := ⟨col, col, fun _ => 0, pub⟩

/-- A handle's `(k, kb)` is a small atom `(0, 0)`, a cell `(1, 0)` or a big atom `(2, 1)`. -/
def KV (k b : F) : Prop := (k = 0 ∧ b = 0) ∨ (k = 1 ∧ b = 0) ∨ (k = 2 ∧ b = 1)

theorem kv_H {H : Noun → ℕ × ℕ} {p : ℕ} (hH : HdlOK p H) (x : Noun) : KV (hk (F := F) H x) (hb H x) := by
  rcases kind3 H hH x with h | h | h <;> simp [KV, hk, hb, h]

/-- **The claim publics**: the first row's `s f e` handle columns. -/
def PubOK9 (col : ℕ → F) (pub : ℕ → F) : Prop :=
  col 17 = 0 ∨ (pub 0 = col 25 ∧ pub 1 = col 26 ∧ pub 2 = col 27 ∧ pub 3 = col 28 ∧ pub 4 = col 29 ∧
    pub 5 = col 30)

theorem claim_hold9 {col pub : ℕ → F} (hpub : PubOK9 col pub) :
    ∀ g ∈ (claimEq : List (EqG ℚ)), evalQX g.gate (mkEnv col pub) = 0 := by
  simp only [claimEq, ChipH.hpub, List.cons_append, List.nil_append, List.forall_mem_cons,
    List.forall_mem_nil, and_true]
  rcases hpub with h0 | ⟨q0, q1, q2, q3, q4, q5⟩
  · simp [EqG.gate, Opnd.expr, evalQX, cc, mkEnv, firstX, h0]
  · simp [EqG.gate, Opnd.expr, evalQX, cc, mkEnv, firstX, xS, xF, xE, hdX, q0, q1, q2, q3, q4, q5]

/-- **The kind gates** at a row whose handles are kinds `0/1/2` (the formula may be the kind-3 label
`(3, ·, kb = 1)`, legal only where the relaxed `kindRelaxX9` replaces `kc(f)·kb(f)`). -/
theorem kind_gates9 {env : Env F}
    (hK : ∀ j < 12, j ≠ 1 → KV (env.trace (25 + 2 * j)) (env.trace (49 + j)))
    (hF : KV (env.trace 27) (env.trace 50) ∨ (env.trace 27 = 3 ∧ env.trace 50 = 1)) :
    ∀ g ∈ (kindG : List (CoeffExpr ℚ)), g ∈ arithGatesX9 → evalQX g env = 0 := by
  intro g hg hg9
  obtain ⟨h, hh, hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hh
  rw [List.mem_range] at hj
  have ek : (hdX j).k = 25 + 2 * j := rfl
  have eb : kbX (hdX j) = 49 + j := kbX_hdX j
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  by_cases hj1 : j = 1
  · subst hj1
    rcases hg with rfl | rfl | rfl
    · rcases hF with (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩) | ⟨a, b⟩ <;>
        simp [boolG, kbE, evalQX, cc, eb, a, b]
    · rcases hF with (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩) | ⟨a, b⟩ <;>
        simp [boolG, kcE, kbE, evalQX, cc, ek, eb, a, b] <;> norm_num
    · exact absurd hg9 kcf_not_mem
  · rcases hK j hj hj1 with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> rcases hg with rfl | rfl | rfl <;>
      simp [boolG, kcE, kbE, evalQX, cc, ek, eb, a, b] <;> norm_num


theorem assemble9 {col pub : ℕ → F} (Z : List ℕ) (hA : List (CoeffExpr ℚ)) (hE : List (EqG ℚ))
    (rA : (arithGatesX9.all fun g => zeroOn Z g ||
      decide (g ∈ (kindG : List (CoeffExpr ℚ))) || decide (g ∈ hA)) = true)
    (rE : ((eqGatesX9 : List (EqG ℚ)).all fun g => zeroOn Z g.gate || decide (g ∈ hE)) = true)
    (hz : ∀ c ∈ Z, col c = 0)
    (hK : ∀ j < 12, j ≠ 1 → KV (col (25 + 2 * j)) (col (49 + j)))
    (hF : KV (col 27) (col 50) ∨ (col 27 = 3 ∧ col 50 = 1))
    (gA : ∀ g ∈ hA, evalQX g (mkEnv col pub) = 0)
    (gE : ∀ g ∈ hE, evalQX g.gate (mkEnv col pub) = 0) :
    (∀ g ∈ arithGatesX9, evalQX g (mkEnv col pub) = 0) ∧
      (∀ g ∈ (eqGatesX9 : List (EqG ℚ)), evalQX g.gate (mkEnv col pub) = 0) := by
  have hz' : ∀ c ∈ Z, (mkEnv col pub).trace c = 0 ∧ (mkEnv col pub).traceNext c = 0 :=
    fun c hc => ⟨hz c hc, hz c hc⟩
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · have hc := List.all_eq_true.mp rA g hg
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with (hc | hc) | hc
    · exact evalQX_zeroOn Z hz' g hc
    · exact kind_gates9 (env := mkEnv col pub) hK hF g hc hg
    · exact gA g hc
  · have hc := List.all_eq_true.mp rE g hg
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | hc
    · exact evalQX_zeroOn Z hz' _ hc
    · exact gE g hc

end Gen

/-! ## 7. `s0B` rows -/

section S0B
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

theorem colS0B_mid (r : RowNX) (n : ℕ) (fst lst : F) (c : ℕ) (h1 : 17 ≤ c) (h2 : c < 123) :
    colS0B H pd idOf r n fst lst c = colX H pd r fst lst c := by
  simp only [colS0B, if_neg (show ¬ c < 17 by omega), if_pos h2]

/-- **`s0B` rows, at the noun level**: J-8's op-0 row facts at an axis atom `n ≥ 2^62`. -/
theorem s0B_gates_core (r : RowNX) (n : ℕ) (fst lst : F) (pub : ℕ → F)
    (hH : HdlOK (ringChar F) H) (hp : 16 ≤ ringChar F)
    (hst : r.st = .s0) (hfh : r.fh = .atom 0) (hf : r.f = .cell r.fh r.ft) (hft : r.ft = .atom n)
    (hn : 2 ≤ n) (hsl : Noun.slot n r.s = some r.e)
    (hpub : PubOK9 (colS0B H pd idOf r n fst lst) pub) :
    (∀ g ∈ arithGatesX9, evalQX g (mkEnv (colS0B H pd idOf r n fst lst) pub) = 0) ∧
      (∀ g ∈ (eqGatesX9 : List (EqG ℚ)), evalQX g.gate (mkEnv (colS0B H pd idOf r n fst lst) pub) = 0) := by
  have e0 : H r.fh = (0, 0) := by rw [hfh]; exact hS_ H hH (by omega)
  have ef : (H r.f).1 = 1 := hC_ H hH (by rw [hf]; rfl)
  have es : (H r.s).1 = 1 := hC_ H hH (slot_cell n r.s r.e hsl (by omega))
  have eft : (H r.ft).1 = 0 ∨ (H r.ft).1 = 2 := by
    rcases kind3 H hH r.ft with h | h | h
    · exact Or.inl h
    · exfalso; have := cell_of_k1 H hH h; rw [hft] at this; simp [Noun.isCell] at this
    · exact Or.inr h
  have n1 : r.ft ≠ .atom 1 := by rw [hft]; intro h; injection h; omega
  refine assemble9 Z0B handA0B handE0B arith_s0B_class eq_s0B_class ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [Z0B, List.mem_append, List.mem_range, List.mem_cons, List.mem_range'] at hc
    rcases hc with ((hc | hc) | hc)
    · simp [colS0B, hc]
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc
      · simp [colS0B, cZ1, hst, n1]
      · simp [colS0B, cB, hst]
      · simp [colS0B, cPr, hst]
      · simp [colS0B, cFast, hst]
      · simp [colS0B, cPr2, isPair, hst]
      · simp [colS0B, cL, isPair, hst]
      · simp [colS0B, cL, isPair, hst]
      · simp [colS0B]
      · simp [colS0B]
      · simp at hc
    · obtain ⟨i, hi, rfl⟩ := hc
      simp only [Nat.one_mul]
      simp only [colS0B, if_neg (show ¬ 127 + i < 17 by omega), if_neg (show ¬ 127 + i < 123 by omega),
        if_neg (show ¬ 127 + i = 123 by omega), if_neg (show ¬ 127 + i = 126 by omega)]
  · intro j hj _
    rw [colS0B_mid H pd idOf r n fst lst _ (by omega) (by omega),
      colS0B_mid H pd idOf r n fst lst _ (by omega) (by omega), colX_k H pd r fst lst j hj,
      colX_kb H pd r fst lst j hj]
    exact kv_H hH _
  · left
    rw [colS0B_mid H pd idOf r n fst lst _ (by omega) (by omega),
      colS0B_mid H pd idOf r n fst lst _ (by omega) (by omega)]
    exact kv_H hH _
  · simp only [handA0B, s0BG, List.cons_append, List.nil_append, List.forall_mem_cons,
      List.forall_mem_nil, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [evalQX, cc, kcE, kbE, mkEnv, consCol, xFh, hdX, kbX, colS0B, hk, hb, e0]
    · simp [evalQX, cc, kbE, mkEnv, xFh, hdX, kbX, colS0B, hb, e0]
    · simp [oneHotSumX9, evalQX, evalQX_sumList, selS, newStates, nStates, List.range_succ, cc, mkEnv,
        colS0B, sS0B, sS10B, sS10S]
    · simp [kindRelaxX9, oneMinus, evalQX, cc, kcE, kbE, mkEnv, xF, hdX, kbX, colS0B, sS10S, hb, ef]
    · simp [svXFX9, svXF8, oneMinus, prodL, evalQX, cc, mkEnv, xF, hdX, colS0B, sS10S, sS10L, sS10T,
        hk, ef]
    · simp [boolG, evalQX, cc, mkEnv, colS0B, sS0B]
    · rcases eft with h | h <;>
        simp [evalQX, cc, kcE, kbE, mkEnv, xFt, hdX, kbX, colS0B, sS0B, hk, hb, h]
    · simp [evalQX, cc, mkEnv, z1X, colS0B, sS0B, cZ1, hst, n1]
    · simp [evalQX, cc, kcE, kbE, oneMinus, mkEnv, xS, hdX, kbX, colS0B, sS0B, hk, hb, es]
  · simp only [handE0B, List.mem_append, List.mem_singleton]
    rintro g (hg | rfl)
    · exact claim_hold9 hpub g hg
    · simp [EqG.gate, Opnd.expr, evalQX, cc, mkEnv, xFh, hdX, colS0B, sS0B, hv, e0]

/-- **`s0B` rows**: at a J-9 A row of chip state `s0B` with `SemN9`, every arithmetic and equality base gate
of the twin vanishes at the honest environment. -/
theorem s0B_gates {R : Nock.Jet.Registry} (l : LX9) (fst lst : F) (pub : ℕ → F) (hchip : l.chip = .s0B)
    (hsem : SemN9 R l) (hH : HdlOK (ringChar F) H) (hp : 16 ≤ ringChar F)
    (hpub : PubOK9 (colX9 H pd idOf l fst lst) pub) :
    (∀ g ∈ arithGatesX9, evalQX g (hEnvX9 H pd idOf l fst lst pub) = 0) ∧
      (∀ g ∈ (eqGatesX9 : List (EqG ℚ)), evalQX g.gate (hEnvX9 H pd idOf l fst lst pub) = 0) := by
  have hc : colX9 H pd idOf l fst lst = colS0B H pd idOf l.rn l.n fst lst := by simp only [colX9, hchip]
  have he : hEnvX9 H pd idOf l fst lst pub = mkEnv (colS0B H pd idOf l.rn l.n fst lst) pub := by
    simp only [hEnvX9, mkEnv, hc]
  rw [he]
  rw [hc] at hpub
  simp only [SemN9, hchip] at hsem
  obtain ⟨hS, hst, hft, hbig⟩ := hsem
  simp only [RowNX.SemN, hst] at hS
  obtain ⟨hfh, hf, ax, hax, hsl⟩ := hS
  rw [hft] at hax
  injection hax with hax
  subst hax
  exact s0B_gates_core H pd idOf l.rn _ fst lst pub hH hp hst hfh hf hft
    (le_trans (by norm_num) hbig) hsl hpub

end S0B

/-! ## 8. `s10B` rows -/

section S10B
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

theorem colS10B_mid (r : RowNX) (n : ℕ) (fst lst : F) (c : ℕ) (h1 : 17 ≤ c) (h2 : c < 123) :
    colS10B H pd idOf r n fst lst c = colX H pd r fst lst c := by
  simp only [colS10B, if_neg (show ¬ c < 17 by omega), if_pos h2]

/-- **`s10B` rows, at the noun level**: J-8's op-10 row facts at an axis atom `n ≥ 2^62`, plus the two
real-child formulas `f_ttt`, `f_tt` being cells (F4's `kidKindNew`; J-8's `RowOKX` carries the same). -/
theorem s10B_gates_core (r : RowNX) (n : ℕ) (fst lst : F) (pub : ℕ → F)
    (hH : HdlOK (ringChar F) H) (hp : 16 ≤ ringChar F)
    (hst : r.st = .s10) (hfh : r.fh = .atom 10) (hf : r.f = .cell r.fh r.ft) (hft : r.ft = .cell r.fth r.ftt)
    (hfth : r.fth = .cell r.ftth r.fttt) (hftth : r.ftth = .atom n) (hn : 2 ≤ n)
    (hed : Noun.edit n r.sf1 r.sf2 = some r.e) (hk1 : r.fttt.isCell = true) (hk2 : r.ftt.isCell = true)
    (hpub : PubOK9 (colS10B H pd idOf r n fst lst) pub) :
    (∀ g ∈ arithGatesX9, evalQX g (mkEnv (colS10B H pd idOf r n fst lst) pub) = 0) ∧
      (∀ g ∈ (eqGatesX9 : List (EqG ℚ)), evalQX g.gate (mkEnv (colS10B H pd idOf r n fst lst) pub) = 0) := by
  have e0 : H r.fh = (0, 10) := by rw [hfh]; exact hS_ H hH (by omega)
  have ef : (H r.f).1 = 1 := hC_ H hH (by rw [hf]; rfl)
  have eft : (H r.ft).1 = 1 := hC_ H hH (by rw [hft]; rfl)
  have efth : (H r.fth).1 = 1 := hC_ H hH (by rw [hfth]; rfl)
  have ee : (H r.e).1 = 1 := hC_ H hH (edit_cell n hed (by omega))
  have ek1 : (H r.fttt).1 = 1 := hC_ H hH hk1
  have ek2 : (H r.ftt).1 = 1 := hC_ H hH hk2
  have n1 : r.ftth ≠ .atom 1 := by rw [hftth]; intro h; injection h; omega
  refine assemble9 Z10B handA10B handE10B arith_s10B_class eq_s10B_class ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [Z10B, List.mem_append, List.mem_range, List.mem_cons, List.mem_range'] at hc
    rcases hc with ((hc | hc) | hc)
    · simp [colS10B, hc]
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc
      · simp [colS10B, cZ1, hst, n1]
      · simp [colS10B, cB, hst]
      · simp [colS10B, cPr, hst]
      · simp [colS10B, cFast, hst]
      · simp [colS10B, cPr2, isPair, hst]
      · simp [colS10B, cL, isPair, hst]
      · simp [colS10B, cL, isPair, hst]
      · simp [colS10B]
      · simp [colS10B]
      · simp at hc
    · obtain ⟨i, hi, rfl⟩ := hc
      simp only [Nat.one_mul]
      simp only [colS10B, if_neg (show ¬ 129 + i < 17 by omega), if_neg (show ¬ 129 + i < 123 by omega),
        if_neg (show ¬ 129 + i = 124 by omega), if_neg (show ¬ 129 + i = 126 by omega),
        if_neg (show ¬ 129 + i = 127 by omega), if_neg (show ¬ 129 + i = 128 by omega)]
  · intro j hj _
    rw [colS10B_mid H pd idOf r n fst lst _ (by omega) (by omega),
      colS10B_mid H pd idOf r n fst lst _ (by omega) (by omega), colX_k H pd r fst lst j hj,
      colX_kb H pd r fst lst j hj]
    exact kv_H hH _
  · left
    rw [colS10B_mid H pd idOf r n fst lst _ (by omega) (by omega),
      colS10B_mid H pd idOf r n fst lst _ (by omega) (by omega)]
    exact kv_H hH _
  · -- the axis atom: a field axis `(0, n)` or a big one `(2, ·)`
    have eA : (ringChar F ≤ n ∧ (H (.atom n)).1 = 2) ∨ (n < ringChar F ∧ H (.atom n) = (0, n)) := by
      by_cases hb : ringChar F ≤ n
      · exact Or.inl ⟨hb, hH.big n hb⟩
      · exact Or.inr ⟨by omega, hH.small n (by omega)⟩
    simp only [handA10B, s10BG, kidKindNew, kidFormsNew, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.forall_mem_cons, List.forall_mem_nil, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [evalQX, cc, kcE, kbE, mkEnv, consCol, xFh, hdX, kbX, colS10B, hk, hb, e0]
    · simp [evalQX, cc, kbE, mkEnv, xFh, hdX, kbX, colS10B, hb, e0]
    · simp [oneHotSumX9, evalQX, evalQX_sumList, selS, newStates, nStates, List.range_succ, cc, mkEnv,
        colS10B, sS0B, sS10B, sS10S]
    · simp [kindRelaxX9, oneMinus, evalQX, cc, kcE, kbE, mkEnv, xF, hdX, kbX, colS10B, sS10S, hb, ef]
    · simp [svXFX9, svXF8, oneMinus, prodL, evalQX, cc, mkEnv, xF, hdX, colS10B, sS10S, sS10L, sS10T,
        hk, ef]
    · simp [boolG, evalQX, cc, mkEnv, colS10B, sS10B]
    · rcases eA with ⟨-, h⟩ | ⟨-, h⟩ <;>
        simp [evalQX, cc, kcE, kbE, mkEnv, xFtth, hdX, kbX, colS10B, sS10B, hk, hb, hftth, h]
    · simp [evalQX, cc, mkEnv, z1X, colS10B, sS10B, cZ1, hst, n1]
    · simp [evalQX, cc, kcE, kbE, oneMinus, mkEnv, xE, hdX, kbX, colS10B, sS10B, hk, hb, ee]
    · simp [evalQX, cc, kcE, kbE, oneMinus, mkEnv, xFt, hdX, kbX, colS10B, sS10B, hk, hb, eft]
    · simp [evalQX, cc, kcE, kbE, oneMinus, mkEnv, xFth, hdX, kbX, colS10B, sS10B, hk, hb, efth]
    · rcases eA with ⟨hb', h⟩ | ⟨hb', h⟩
      · simp [evalQX, cc, kbE, mkEnv, xFtth, hdX, kbX, kLabX, colS10B, sS10B, hb, hftth, h, hb']
        norm_num
      · simp [evalQX, cc, kbE, mkEnv, xFtth, hdX, kbX, kLabX, colS10B, sS10B, hb, hftth, h,
          show ¬ ringChar F ≤ n by omega]
    · rcases eA with ⟨hb', h⟩ | ⟨hb', h⟩
      · simp [prodL, oneMinus, evalQX, cc, kbE, mkEnv, xFtth, hdX, kbX, vLabX, xIdX, colS10B, sS10B, hb,
          hftth, h]
      · simp [prodL, oneMinus, evalQX, cc, kbE, mkEnv, xFtth, hdX, kbX, vLabX, xIdX, colS10B, sS10B, hb,
          hftth, h, show ¬ ringChar F ≤ n by omega]
    · simp [evalQX, cc, kcE, kbE, oneMinus, mkEnv, xFttt, hdX, kbX, colS10B, sS10B, hk, hb, ek1]
    · simp [evalQX, cc, kcE, kbE, oneMinus, mkEnv, xFtt, hdX, kbX, colS10B, sS10B, hk, hb, ek2]
  · simp only [handE10B, s10BEq, List.mem_append, List.mem_singleton]
    rintro g ((hg | rfl) | rfl)
    · exact claim_hold9 hpub g hg
    · simp [EqG.gate, Opnd.expr, evalQX, cc, mkEnv, xFh, hdX, colS10B, sS10B, hv, e0]
    · by_cases hb' : ringChar F ≤ n
      · simp [EqG.gate, Opnd.expr, evalQX, cc, kbE, mkEnv, xFtth, hdX, kbX, vLabX, colS10B, sS10B, hb, hv,
          hftth, hb']
      · simp [EqG.gate, Opnd.expr, evalQX, cc, kbE, mkEnv, xFtth, hdX, kbX, vLabX, colS10B, sS10B, hb, hv,
          hftth, hb', hH.small n (by omega)]

/-- **`s10B` rows**: at a J-9 A row of chip state `s10B` with `SemN9` and its two real-child formulas cells,
every arithmetic and equality base gate of the twin vanishes at the honest environment. -/
theorem s10B_gates {R : Nock.Jet.Registry} (l : LX9) (fst lst : F) (pub : ℕ → F) (hchip : l.chip = .s10B)
    (hsem : SemN9 R l) (hH : HdlOK (ringChar F) H) (hp : 16 ≤ ringChar F)
    (hk1 : l.rn.fttt.isCell = true) (hk2 : l.rn.ftt.isCell = true)
    (hpub : PubOK9 (colX9 H pd idOf l fst lst) pub) :
    (∀ g ∈ arithGatesX9, evalQX g (hEnvX9 H pd idOf l fst lst pub) = 0) ∧
      (∀ g ∈ (eqGatesX9 : List (EqG ℚ)), evalQX g.gate (hEnvX9 H pd idOf l fst lst pub) = 0) := by
  have hc : colX9 H pd idOf l fst lst = colS10B H pd idOf l.rn l.n fst lst := by simp only [colX9, hchip]
  have he : hEnvX9 H pd idOf l fst lst pub = mkEnv (colS10B H pd idOf l.rn l.n fst lst) pub := by
    simp only [hEnvX9, mkEnv, hc]
  rw [he]
  rw [hc] at hpub
  simp only [SemN9, hchip] at hsem
  obtain ⟨hS, hst, hftth, hbig⟩ := hsem
  simp only [RowNX.SemN, hst] at hS
  obtain ⟨hfh, hf, hft, hfth, a, ha, hed⟩ := hS
  rw [hftth] at ha
  injection ha with ha
  subst ha
  exact s10B_gates_core H pd idOf l.rn _ fst lst pub hH hp hst hfh hf hft hfth hftth
    (le_trans (by norm_num) hbig) hed hk1 hk2 hpub

end S10B

/-! ## 9. `s10S` rows -/

/-- The six bits of `m < 64` read `m`. -/
theorem bits_val : ∀ m < 64, m = bitN m 0 + 2 * bitN m 1 + 4 * bitN m 2 + 8 * bitN m 3 + 16 * bitN m 4 +
    32 * bitN m 5 := by decide +kernel

/-- `m < 63`: some bit is `0` (so `aA·aB = 0`). -/
theorem bits_ne63 : ∀ m < 63, bitN m 0 = 0 ∨ bitN m 1 = 0 ∨ bitN m 2 = 0 ∨ bitN m 3 = 0 ∨ bitN m 4 = 0 ∨
    bitN m 5 = 0 := by decide +kernel

/-- `0 < m < 64`: some bit is `1` (so `zA·zB = 0`). -/
theorem bits_nz : ∀ m < 64, m ≠ 0 → bitN m 0 = 1 ∨ bitN m 1 = 1 ∨ bitN m 2 = 1 ∨ bitN m 3 = 1 ∨
    bitN m 4 = 1 ∨ bitN m 5 = 1 := by decide +kernel

theorem bit01 (m i : ℕ) : bitN m i = 0 ∨ bitN m i = 1 := Nat.mod_two_eq_zero_or_one _

theorem bitN_zero (i : ℕ) : bitN 0 i = 0 := by simp [bitN]

/-- `segRd n m = 1` only on the top segment. -/
theorem segRd_one_top {n m : ℕ} (h : segRd n m = 1) : m = top n := by
  by_contra hm
  simp only [segRd, if_neg hm] at h
  omega

open Lean in
macro "ssimp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp [evalQX, cc, kcE, kbE, oneMinus, notC, prodL,
  boolG, mkEnv, colS10S, segRow, hk, hv, hb, xS, xF, xE, xSf1, xSf2, xFh, xM, xFtth, xFttt, hdX, kbX, z1X,
  betaX, fastX, xL1, xL2, consCol, prX, sS10S, sS10L, sS10T, sS0B, sS10B, m4X, m5X, hdC, m0X, m1X, m2X,
  m3X, pw1X, pw2X, pwX, zAX, zBX, aAX, aBX, axLX, ChipHX9.segX, limbX, kLabX, vLabX, xIdX, mValE, vX, v2X,
  wX, inv4X, ax2X, $ts,*])

section S10S
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

theorem colS10S_pass (n m : ℕ) (r : RowNX) (fst lst : F) (c : ℕ) (h1 : 25 ≤ c) (h2 : c < 61)
    (h3 : c ≠ 27) (h4 : c ≠ 28) (h5 : c ≠ 50) :
    colS10S H pd idOf n m r fst lst c = colX H pd r fst lst c := by
  simp only [colS10S, if_neg (show ¬ c < 17 by omega), if_neg (show ¬ c = 19 by omega),
    if_neg (show ¬ c = 20 by omega), if_neg (show ¬ c = 21 by omega), if_neg (show ¬ c = 22 by omega),
    if_neg (show ¬ c = 23 by omega), if_neg (show ¬ c = 24 by omega), if_neg h3, if_neg h4, if_neg h5,
    if_pos h2]

/-- The value of `m` from its six bit columns, in `F`. -/
theorem mval (m : ℕ) (hm : m < 64) :
    ((m : ℕ) : F) = (bitN m 0 : F) + 2 * (bitN m 1 : F) + 4 * (bitN m 2 : F) + 8 * (bitN m 3 : F) +
      16 * (bitN m 4 : F) + 32 * (bitN m 5 : F) := by
  conv_lhs => rw [bits_val m hm]
  push_cast; ring

/-- **The formula handle of an `s10S` row is `H`'s** on the top segment of a big axis, when `idOf n` is the
atom table's serial of `n` (`segAx n (top n) = n`). -/
theorem colS10S_f_top_big (n m : ℕ) (r : RowNX) (fst lst : F) (hmt : m = top n) (hbig : ringChar F ≤ n)
    (hH : HdlOK (ringChar F) H) (hid : (H (.atom n)).2 = idOf n) :
    colS10S H pd idOf n m r fst lst 27 = hk H (.atom (segAx n m)) ∧
      colS10S H pd idOf n m r fst lst 28 = hv H (.atom (segAx n m)) := by
  subst hmt
  rw [Nock.J9A.NounAx.segAx_top]
  constructor
  · simp [colS10S, hbig, hk, hH.big n hbig]
  · simp [colS10S, hbig, hv, hid]

/-- `s10S`'s hand arithmetic gates, part 1 (the J-8 globals, the walk pair, the changed gates, the new
booleans, the decode). -/
theorem s10S_handA1 (n m : ℕ) (s e : Noun) (fst lst : F) (pub : ℕ → F)
    (hH : HdlOK (ringChar F) H) (hq : 2 ^ 63 < ringChar F) (hcap : m < 63)
    (hsl1 : Noun.slot (segRd n m) s = some (ComplJ9AGen.segX n m s))
    (hsl2 : Noun.slot (segRd n m) e = some (ComplJ9AGen.segX n m e)) :
    ∀ g ∈ handA10S1, evalQX g (mkEnv (colS10S H pd idOf n m (segRow n m s e) fst lst) pub) = 0 := by
  have e0 : H (.atom 0) = (0, 0) := hS_ H hH (by omega)
  have eR : H (.atom (segRd n m)) = (0, segRd n m) :=
    hS_ H hH (lt_trans (Nock.J9A.NounAx.segRd_lt n m) (lt_trans (by norm_num) hq))
  have mv := mval (F := F) m (by omega)
  have cS : segRd n m ≠ 1 → (H s).1 = 1 := fun h => hC_ H hH (slot_cell _ s _ hsl1 h)
  have cE : segRd n m ≠ 1 → (H e).1 = 1 := fun h => hC_ H hH (slot_cell _ e _ hsl2 h)
  simp only [handA10S1, List.forall_mem_cons, List.forall_mem_nil, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- booleans
  · by_cases hz : segRd n m = 1 <;> ssimp [hz]
  · rcases bit01 m 0 with h | h <;> ssimp [h]
  · rcases bit01 m 1 with h | h <;> ssimp [h]
  · rcases bit01 m 2 with h | h <;> ssimp [h]
  · rcases bit01 m 3 with h | h <;> ssimp [h]
  -- the decode parent `f_h`, the walk pair
  · ssimp [e0]
  · ssimp [e0]
  · ssimp [eR]
  · by_cases hz : segRd n m = 1
    · ssimp [hz]
    · ssimp [hz, cS hz]
  · by_cases hz : segRd n m = 1
    · ssimp [hz]
    · ssimp [hz, cE hz]
  -- the four changed J-8 gates
  · simp [oneHotSumX9, evalQX, evalQX_sumList, selS, newStates, nStates, List.range_succ, cc, mkEnv,
      colS10S, sS0B, sS10B, sS10S]
  · ssimp [kindRelaxX9]
  · by_cases hk2 : m = top n ∧ ringChar F ≤ n
    · ssimp [svXFX9, svXF8, hk2] <;> norm_num
    · ssimp [svXFX9, svXF8, hk2] <;> norm_num
  · ssimp [prGateX9, prGateX]
  -- new booleans
  · ssimp []
  · rcases bit01 m 4 with h | h <;> ssimp [h]
  · rcases bit01 m 5 with h | h <;> ssimp [h]
  · by_cases hmt : m = top n <;> ssimp [hmt]
  -- the ONE allowlisted decode
  · by_cases hk2 : m = top n ∧ ringChar F ≤ n
    · ssimp [decodeG9, hk2] <;> norm_num
    · ssimp [decodeG9, hk2, mv] <;> ring_nf <;> simp

/-- `s10S`'s own gates `s10SG`. -/
theorem s10S_handA2 (n m : ℕ) (s e : Noun) (fst lst : F) (pub : ℕ → F)
    (hH : HdlOK (ringChar F) H) (hq : 2 ^ 63 < ringChar F) (hcap : m < 63) :
    ∀ g ∈ (s10SG : List (CoeffExpr ℚ)),
      evalQX g (mkEnv (colS10S H pd idOf n m (segRow n m s e) fst lst) pub) = 0 := by
  have eR : H (.atom (segRd n m)) = (0, segRd n m) :=
    hS_ H hH (lt_trans (Nock.J9A.NounAx.segRd_lt n m) (lt_trans (by norm_num) hq))
  have mv := mval (F := F) m (by omega)
  simp only [s10SG, List.forall_mem_cons, List.forall_mem_nil, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ssimp []
  · by_cases hk2 : m = top n ∧ ringChar F ≤ n
    · ssimp [hk2.1]
    · ssimp [hk2] <;> norm_num
  · ssimp []
  · ssimp []
  · ssimp []
  · ssimp []
  · ssimp []
  · rcases bits_ne63 m hcap with h | h | h | h | h | h <;> ssimp [h]
  · ssimp []
  · ssimp []
  · ssimp []
  · by_cases hmt : m = top n
    · ssimp [segRd, hmt]
    · ssimp [segRd, hmt] <;> norm_num
  · by_cases hz : segRd n m = 1
    · ssimp [hz]
    · ssimp [hz]
  · by_cases hz : segRd n m = 1
    · ssimp [hz, segRd_one_top hz]
    · ssimp [hz]
  · ssimp [eR]
  · by_cases hm0 : m = 0
    · subst hm0; ssimp [bitN_zero]
    · rcases bits_nz m (by omega) hm0 with h | h | h | h | h | h <;> ssimp [hm0, h]
  · by_cases hm0 : m = 0
    · subst hm0; ssimp [bitN_zero]
    · have h1 : 1 ≤ m := by omega
      rcases bits_nz m (by omega) hm0 with h | h | h | h | h | h <;>
        ssimp [hm0, h, Nat.cast_sub h1, mv] <;> ring_nf <;> simp

/-- `s10S`'s hand equality gates (the claim publics and `s10SEq`). -/
theorem s10S_handE (n m : ℕ) (s e : Noun) (fst lst : F) (pub : ℕ → F)
    (hH : HdlOK (ringChar F) H) (hq : 2 ^ 63 < ringChar F)
    (hsl1 : Noun.slot (segRd n m) s = some (ComplJ9AGen.segX n m s))
    (hsl2 : Noun.slot (segRd n m) e = some (ComplJ9AGen.segX n m e))
    (hpub : PubOK9 (colS10S H pd idOf n m (segRow n m s e) fst lst) pub) :
    ∀ g ∈ handE10S, evalQX g.gate (mkEnv (colS10S H pd idOf n m (segRow n m s e) fst lst) pub) = 0 := by
  have eR : H (.atom (segRd n m)) = (0, segRd n m) :=
    hS_ H hH (lt_trans (Nock.J9A.NounAx.segRd_lt n m) (lt_trans (by norm_num) hq))
  have zS : segRd n m = 1 → ComplJ9AGen.segX n m s = s := fun h => by
    rw [h] at hsl1; simpa [Noun.slot] using hsl1.symm
  have zE : segRd n m = 1 → ComplJ9AGen.segX n m e = e := fun h => by
    rw [h] at hsl2; simpa [Noun.slot] using hsl2.symm
  simp only [handE10S, s10SEq, heq, List.cons_append, List.nil_append, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro g (hg | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact claim_hold9 hpub g hg
  · by_cases hk2 : m = top n ∧ ringChar F ≤ n
    · ssimp [EqG.gate, Opnd.expr, hk2]
    · ssimp [EqG.gate, Opnd.expr, hk2] <;> norm_num
  · ssimp [EqG.gate, Opnd.expr, eR]
  · ssimp [EqG.gate, Opnd.expr]
  · ssimp [EqG.gate, Opnd.expr]
  · ssimp [EqG.gate, Opnd.expr]
  · ssimp [EqG.gate, Opnd.expr]
  all_goals
    by_cases hz : segRd n m = 1
    · ssimp [EqG.gate, Opnd.expr, hz, zS hz, zE hz]
    · ssimp [EqG.gate, Opnd.expr, hz]

/-- **`s10S` rows, at the noun level**: segment `m < 63` of the axis `n` on `s ⇝ e`, with the two segment
reads defined (`ComplJ9AGen.segX`). -/
theorem s10S_gates_core (n m : ℕ) (s e : Noun) (fst lst : F) (pub : ℕ → F)
    (hH : HdlOK (ringChar F) H) (hq : 2 ^ 63 < ringChar F) (hcap : m < 63)
    (hsl1 : Noun.slot (segRd n m) s = some (ComplJ9AGen.segX n m s))
    (hsl2 : Noun.slot (segRd n m) e = some (ComplJ9AGen.segX n m e))
    (hpub : PubOK9 (colS10S H pd idOf n m (segRow n m s e) fst lst) pub) :
    (∀ g ∈ arithGatesX9, evalQX g (mkEnv (colS10S H pd idOf n m (segRow n m s e) fst lst) pub) = 0) ∧
      (∀ g ∈ (eqGatesX9 : List (EqG ℚ)),
        evalQX g.gate (mkEnv (colS10S H pd idOf n m (segRow n m s e) fst lst) pub) = 0) := by
  refine assemble9 Z10S handA10S handE10S arith_s10S_class eq_s10S_class ?_ ?_ ?_ ?_
    (s10S_handE H pd idOf n m s e fst lst pub hH hq hsl1 hsl2 hpub)
  · intro c hc
    simp only [Z10S, List.mem_append, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | rfl | rfl | rfl | rfl | rfl
    · simp [colS10S, hc]
    all_goals simp [colS10S]
  · intro j hj hj1
    have hodd : 25 + 2 * j ≠ 28 := by omega
    rw [colS10S_pass H pd idOf n m _ fst lst _ (by omega) (by omega) (by omega) hodd (by omega),
      colS10S_pass H pd idOf n m _ fst lst (49 + j) (by omega) (by omega) (by omega) (by omega) (by omega),
      colX_k H pd _ fst lst j hj, colX_kb H pd _ fst lst j hj]
    exact kv_H hH _
  · by_cases hk2 : m = top n ∧ ringChar F ≤ n
    · left; right; right; simp [colS10S, hk2]
    · right; simp [colS10S, hk2]
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact s10S_handA1 H pd idOf n m s e fst lst pub hH hq hcap hsl1 hsl2 g hg
    · exact s10S_handA2 H pd idOf n m s e fst lst pub hH hq hcap g hg

/-- **`s10S` rows**: at a J-9 A row of chip state `s10S` with `SemN9` and segment index `m < 63` (the
cap: `(limbs n).length ≤ 62` gives `m ≤ 61`), every arithmetic and equality base gate of the twin vanishes
at the honest environment. -/
theorem s10S_gates {R : Nock.Jet.Registry} (l : LX9) (fst lst : F) (pub : ℕ → F) (hchip : l.chip = .s10S)
    (hsem : SemN9 R l) (hH : HdlOK (ringChar F) H) (hq : 2 ^ 63 < ringChar F) (hcap : l.m < 63)
    (hpub : PubOK9 (colX9 H pd idOf l fst lst) pub) :
    (∀ g ∈ arithGatesX9, evalQX g (hEnvX9 H pd idOf l fst lst pub) = 0) ∧
      (∀ g ∈ (eqGatesX9 : List (EqG ℚ)), evalQX g.gate (hEnvX9 H pd idOf l fst lst pub) = 0) := by
  simp only [SemN9, hchip] at hsem
  obtain ⟨-, -, hr, -, -, hsl1, hsl2⟩ := hsem
  have hc : colX9 H pd idOf l fst lst =
      colS10S H pd idOf l.n l.m (segRow l.n l.m l.rn.s l.rn.e) fst lst := by
    simp only [colX9, hchip]; rw [← hr]
  have he : hEnvX9 H pd idOf l fst lst pub =
      mkEnv (colS10S H pd idOf l.n l.m (segRow l.n l.m l.rn.s l.rn.e) fst lst) pub := by
    simp only [hEnvX9, mkEnv, hc]
  rw [he]
  rw [hc] at hpub
  have h1 : l.rn.ftth = ComplJ9AGen.segX l.n l.m l.rn.s := by
    rw [hr]; rfl
  have h2 : l.rn.fttt = ComplJ9AGen.segX l.n l.m l.rn.e := by
    rw [hr]; rfl
  rw [h1] at hsl1
  rw [h2] at hsl2
  exact s10S_gates_core H pd idOf l.n l.m l.rn.s l.rn.e fst lst pub hH hq hcap hsl1 hsl2 hpub

end S10S

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow
#print axioms colX9_old
#print axioms colX9_old_new
#print axioms rapOf9_perm
#print axioms rapOf9_old
#print axioms twin_of_J8
#print axioms old_gates
#print axioms arith_s0B_class
#print axioms eq_s0B_class
#print axioms arith_s10B_class
#print axioms eq_s10B_class
#print axioms arith_s10S_class
#print axioms eq_s10S_class
#print axioms kind_gates9
#print axioms assemble9
#print axioms s0B_gates_core
#print axioms s0B_gates
#print axioms s10B_gates_core
#print axioms s10B_gates
#print axioms bits_val
#print axioms bits_ne63
#print axioms bits_nz
#print axioms colS10S_f_top_big
#print axioms s10S_handA1
#print axioms s10S_handA2
#print axioms s10S_handE
#print axioms s10S_gates_core
#print axioms s10S_gates
end Axioms
