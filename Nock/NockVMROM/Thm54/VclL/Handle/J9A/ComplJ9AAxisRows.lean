/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AAxisRows.lean

* `PairOK e`: what an honest axis-chain row (current row of `e`) and its successor (next row of `e`) satisfy,
    stated as field facts, case by case on the booleans (the chip gates G1–G8 read forwards: head / non-head limb axes
    `pw − 1` / `pw − 2`, segment axes `l` / `B + l`, the top-limb-`1` skip, roots, chain continuity, the `pw`
    schedule, the boundaries, the `(0, v)` emission, the emission columns, `mu` only on chain-last rows).
  * **`baseGates_of_pairOK`**: `PairOK e → ∀ g ∈ AxisChipJ9.baseGates, g.eval e = 0`.
  * **`pairOK_last`**: on a table-last row (`isLT = 1`) the next-row facts are vacuous: `PairOK` at EVERY
    next-row valuation from the current-row facts alone (what `ComplJ9AAxisH.axisChipJ9_honest_sat`'s `hgate`
    asks of the last row).
  * `ARow`, `ARow.col`, `ARow.rowEnv`; **`chainRow`**: row `j` of an honest axis chain over the limbs `ls` (head =
    top limb, `pw` from `2^L` halving to `4`, `axK`/`axS` the comb / segment axes, `hin`/`hout` the path handles,
    a field chain's `(0, v)` route); **`chainRow_curOK`** (every chain row), **`chainRow_nextOK`** (inside a chain),
    **`chainRow_nextOK_last`** (a chain-last row before any next chain head).  With `pairOK_last` this discharges
    `ComplJ9AAxisH.axisChipJ9_honest_sat`'s `hgate` for a table of concatenated chains:
  * `ChainSpec` (one chain's parameters) and `ChainSpec.OK` (its side conditions: `≥ 2` limbs, a skipped top read
    keeps the handle, intermediate segment nouns are cells, a field chain has two limbs, its `< p` inverse and its
    value); `tableRows cs` (the chains concatenated), **`tableRows_isChain`**, `tableCol`;
    **`tableRows_hgate`**: EXACTLY `axisChipJ9_honest_sat`'s `hgate` at `col := tableCol (tableRows cs)`;
    **`axisChipJ9_honest_table`**: the axis chip accepts the honest table (`Satisfies ∧ BindsPreprocessing`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AAxisH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisRows

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9

noncomputable section

variable {F : Type} [Field F]

/-- **The current-row facts of an honest axis-chain row** (no next-row read). -/
structure CurOK (e : Env F) : Prop where
  bF : e.trace isFT = 0 ∨ e.trace isFT = 1
  bL : e.trace isLT = 0 ∨ e.trace isLT = 1
  bh : e.trace head = 0 ∨ e.trace head = 1
  bc : e.trace cl = 0 ∨ e.trace cl = 1
  bz : e.trace z1a = 0 ∨ e.trace z1a = 1
  br : e.trace route0 = 0 ∨ e.trace route0 = 1
  axKh : e.trace head = 1 → e.trace axK = e.trace pw - 1
  axKn : e.trace head = 0 → e.trace axK = e.trace pw - 2
  axSh : e.trace head = 1 → e.trace axS = e.trace l
  axSn : e.trace head = 0 → e.trace axS = Bf + e.trace l
  z1 : e.trace z1a = 1 → e.trace head = 1 ∧ e.trace l = 1 ∧ e.trace houtk = e.trace hink ∧
    e.trace houtv = e.trace hinv
  root : e.trace head = 1 → e.trace hinv = e.trace hrv ∧ e.trace hink = 1
  hin1 : e.trace z1a = 0 → e.trace hink = 1
  pw4 : e.trace cl = 1 → e.trace pw = 4
  hcl : e.trace head = 1 → e.trace cl = 0
  last : e.trace isLT = 1 → e.trace cl = 1
  first : e.trace isFT = 1 → e.trace head = 1
  r0h : e.trace r0h = e.trace route0 * e.trace head
  ftk : e.trace ftk = 2 * (1 - e.trace route0)
  ftv : e.trace ftv = e.trace R + e.trace route0 * (e.trace v - e.trace R)
  mu : e.trace cl = 0 → e.trace mu = 0

/-- **The next-row facts of an honest axis-chain row** (only on non-table-last rows). -/
structure NextOK (e : Env F) : Prop where
  cont : e.trace cl = 0 → e.traceNext hink = e.trace houtk ∧ e.traceNext hinv = e.trace houtv ∧
    e.traceNext R = e.trace R ∧ e.traceNext hrv = e.trace hrv ∧ e.traceNext route0 = e.trace route0 ∧
    e.traceNext v = e.trace v ∧ 2 * e.traceNext pw = e.trace pw * (1 + e.trace head)
  bnd1 : e.trace isLT = 0 → e.trace cl = 1 → e.traceNext head = 1
  bnd2 : e.trace isLT = 0 → e.trace cl = 0 → e.traceNext head = 0
  r0 : e.trace r0h = 1 → e.traceNext cl = 1 ∧
    (e.traceNext l = 0 ∨ (e.trace l - (Bf - 1)) * e.trace invg4 = 1) ∧
    e.trace v = e.trace l * Bf + e.traceNext l

/-- `PairOK`: the current-row facts and the next-row facts. -/
structure PairOK (e : Env F) : Prop extends CurOK e, NextOK e

theorem bool_cases {x : F} (h : x = 0 ∨ x = 1) (P : F → Prop) (h0 : P 0) (h1 : P 1) : P x := by
  rcases h with rfl | rfl <;> assumption

/-- **The base gates vanish at an honest row pair.** -/
theorem baseGates_of_pairOK {e : Env F} (H : PairOK e) : ∀ g ∈ (baseGates : List (CoeffExpr F)), g.eval e = 0 := by
  obtain ⟨⟨bF, bL, bh, bc, bz, br, axKh, axKn, axSh, axSn, z1, root, hin1, pw4, hcl, last, first, r0h, ftk, ftv,
    mu⟩, ⟨cont, bnd1, bnd2, r0⟩⟩ := H
  intro g hg
  simp only [baseGates, baseAG, List.map_append, List.mem_append, g1, g2, g3, g4, g5, g6, g6c, g6p, g6b, g7, g8,
    List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ((((((((rfl | rfl | rfl | rfl) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl | rfl | rfl)) |
    (rfl | rfl | rfl)) | ((((rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) | rfl) |
    (rfl | rfl | rfl | rfl))) | (rfl | rfl | rfl | rfl)) | (rfl | rfl | rfl))
  all_goals simp only [AG.gate, CopyG.gate, SelG.gate, Op.expr, gHeadCl, selG8, boolE, notE, cv, nv,
    CoeffExpr.eval]
  -- G1
  · rcases bh with h | h <;> rw [h] <;> ring
  · rcases bc with h | h <;> rw [h] <;> ring
  · rcases bz with h | h <;> rw [h] <;> ring
  · rcases br with h | h <;> rw [h] <;> ring
  -- G2
  · rcases bh with h | h
    · rw [h]; ring
    · rw [h, axKh h]; ring
  · rcases bh with h | h
    · rw [h, axKn h]; ring
    · rw [h]; ring
  -- G3
  · rcases bh with h | h
    · rw [h]; ring
    · rw [h, axSh h]; ring
  · rcases bh with h | h
    · rw [h, axSn h]; ring
    · rw [h]; ring
  -- G4
  · rcases bz with h | h
    · rw [h]; ring
    · rw [h, (z1 h).1]; ring
  · rcases bz with h | h
    · rw [h]; ring
    · rw [h, (z1 h).2.1]; ring
  · rcases bz with h | h
    · rw [h]; ring
    · rw [h, (z1 h).2.2.1]; ring
  · rcases bz with h | h
    · rw [h]; ring
    · rw [h, (z1 h).2.2.2]; ring
  -- G5
  · rcases bh with h | h
    · rw [h]; ring
    · rw [h, (root h).1]; ring
  · rcases bh with h | h
    · rw [h]; ring
    · rw [h, (root h).2]; ring
  · rcases bz with h | h
    · rw [h, hin1 h]; ring
    · rw [h]; ring
  -- G6 continuity
  · rcases bc with h | h
    · rw [h, (cont h).1]; ring
    · rw [h]; ring
  · rcases bc with h | h
    · rw [h, (cont h).2.1]; ring
    · rw [h]; ring
  · rcases bc with h | h
    · rw [h, (cont h).2.2.1]; ring
    · rw [h]; ring
  · rcases bc with h | h
    · rw [h, (cont h).2.2.2.1]; ring
    · rw [h]; ring
  · rcases bc with h | h
    · rw [h, (cont h).2.2.2.2.1]; ring
    · rw [h]; ring
  · rcases bc with h | h
    · rw [h, (cont h).2.2.2.2.2.1]; ring
    · rw [h]; ring
  -- G6 schedule
  · rcases bc with h | h
    · rw [h, (cont h).2.2.2.2.2.2]; ring
    · rw [h]; ring
  · rcases bc with h | h
    · rw [h]; ring
    · rw [h, pw4 h]; ring
  -- head·cl
  · rcases bh with h | h
    · rw [h]; ring
    · rw [h, hcl h]; ring
  -- G6 boundaries
  · rcases bL with hL | hL
    · rcases bc with h | h
      · rw [hL, h]; ring
      · rw [hL, h, bnd1 hL h]; ring
    · rw [hL]; ring
  · rcases bL with hL | hL
    · rcases bc with h | h
      · rw [hL, h, bnd2 hL h]; ring
      · rw [hL, h]; ring
    · rw [hL]; ring
  · rcases bL with hL | hL
    · rw [hL]; ring
    · rw [hL, last hL]; ring
  · rcases bF with hF | hF
    · rw [hF]; ring
    · rw [hF, first hF]; ring
  -- G7
  · rw [r0h]; ring
  · have hr : e.trace AxisChipJ9.r0h = 0 ∨ e.trace AxisChipJ9.r0h = 1 := by
      rw [r0h]; rcases br with h1 | h1 <;> rcases bh with h2 | h2 <;> rw [h1, h2] <;> simp
    rcases hr with h | h
    · rw [h]; ring
    · rw [h, (r0 h).1]; ring
  · have hr : e.trace AxisChipJ9.r0h = 0 ∨ e.trace AxisChipJ9.r0h = 1 := by
      rw [r0h]; rcases br with h1 | h1 <;> rcases bh with h2 | h2 <;> rw [h1, h2] <;> simp
    rcases hr with h | h
    · rw [h]; ring
    · rcases (r0 h).2.1 with h' | h'
      · rw [h, h']; ring
      · rw [h, h']; ring
  · have hr : e.trace AxisChipJ9.r0h = 0 ∨ e.trace AxisChipJ9.r0h = 1 := by
      rw [r0h]; rcases br with h1 | h1 <;> rcases bh with h2 | h2 <;> rw [h1, h2] <;> simp
    rcases hr with h | h
    · rw [h]; ring
    · rw [h, (r0 h).2.2]; ring
  -- G8
  · rw [ftk]; ring
  · rw [ftv]; ring
  · rcases bc with h | h
    · rw [h, mu h]; ring
    · rw [h]; ring

/-- **The table-last row**: `NextOK` holds at every next-row valuation (`isLT = 1` forces `cl = 1`, so every
`(1 − cl)`-guarded fact is vacuous, the boundary facts need `isLT = 0`, and `r0h = route0·head = 0` since a head is
never chain-last). -/
theorem nextOK_last {e : Env F} (H : CurOK e) (hL : e.trace isLT = 1) : NextOK e := by
  have hc : e.trace cl = 1 := H.last hL
  have hh : e.trace head = 0 := by
    rcases H.bh with h | h
    · exact h
    · have := H.hcl h; rw [hc] at this; exact absurd this one_ne_zero
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [hc] at h; exact absurd h one_ne_zero
  · rw [hL] at h; exact absurd h one_ne_zero
  · rw [hL] at h; exact absurd h one_ne_zero
  · rw [H.r0h, hh, mul_zero] at h; exact absurd h zero_ne_one

/-- **`PairOK` on the table-last row from the current-row facts alone.** -/
theorem pairOK_last {e : Env F} (H : CurOK e) (hL : e.trace isLT = 1) : PairOK e := ⟨H, nextOK_last H hL⟩

end

/-! ## 2. The honest chain rows -/

section Chain
variable {F : Type} [Field F]

/-- **One axis-chip row's twenty prover columns** (`2 .. 21`). -/
structure ARow (F : Type) where
  head : F
  cl : F
  z1a : F
  route0 : F
  R : F
  pw : F
  l : F
  axK : F
  axS : F
  hrv : F
  hink : F
  hinv : F
  houtk : F
  houtv : F
  v : F
  invg4 : F
  r0h : F
  ftk : F
  ftv : F
  mu : F

/-- The column function of a row (`0`, `1`: the table masks `fst`, `lst`). -/
def ARow.col (a : ARow F) (fst lst : F) : ℕ → F
  | 0 => fst | 1 => lst | 2 => a.head | 3 => a.cl | 4 => a.z1a | 5 => a.route0 | 6 => a.R | 7 => a.pw
  | 8 => a.l | 9 => a.axK | 10 => a.axS | 11 => a.hrv | 12 => a.hink | 13 => a.hinv | 14 => a.houtk
  | 15 => a.houtv | 16 => a.v | 17 => a.invg4 | 18 => a.r0h | 19 => a.ftk | 20 => a.ftv | 21 => a.mu
  | _ => 0

/-- The environment of a row pair (current `a`, next column function `nxt`). -/
def ARow.rowEnv (a : ARow F) (fst lst : F) (nxt : ℕ → F) : Env F where
  trace := a.col fst lst
  traceNext := nxt
  chal := fun _ => 0
  pub := fun _ => 0

/-- **Row `j` of an axis chain** over the limbs `ls` (little-endian, `L = |ls|`), from the subject handle value
`hrv`, provider id `R`, the route flag (`route0`: a field axis, served by the split chip) with value `vv`, the
path outputs `houts j` (the handle of the noun after row `j`'s segment read), `g4` the inverse for the `< p` gate,
`mu` the consumer count (on the chain-last row).  A top limb `1` is a skipped read: `houts 0 = (1, hrv)` then
(`chainRow_curOK`'s `hz`). -/
def chainRow (ls : List ℕ) (route0 : Bool) (R hrv vv mu : ℕ) (g4 : F) (houts : ℕ → ℕ × ℕ) (j : ℕ) : ARow F :=
  let L := ls.length
  let isH : Bool := j == 0
  let lj : ℕ := ls.getD (L - 1 - j) 0
  let pwj : ℕ := if isH then 2 ^ L else 2 ^ (L + 1 - j)
  let z : Bool := isH && lj == 1
  let hin : ℕ × ℕ := if isH then (1, hrv) else houts (j - 1)
  let hout : ℕ × ℕ := houts j
  { head := if isH then 1 else 0
    cl := if j + 1 = L then 1 else 0
    z1a := if z then 1 else 0
    route0 := if route0 then 1 else 0
    R := (R : F)
    pw := (pwj : F)
    l := (lj : F)
    axK := if isH then (pwj : F) - 1 else (pwj : F) - 2
    axS := if isH then (lj : F) else (2 : F) ^ 32 + (lj : F)
    hrv := (hrv : F)
    hink := (hin.1 : F)
    hinv := (hin.2 : F)
    houtk := (hout.1 : F)
    houtv := (hout.2 : F)
    v := if route0 then (vv : F) else 0
    invg4 := if route0 && isH then g4 else 0
    r0h := if route0 && isH then 1 else 0
    ftk := if route0 then 0 else 2
    ftv := if route0 then (vv : F) else (R : F)
    mu := if j + 1 = L then (mu : F) else 0 }

end Chain

section ChainLemmas
variable {F : Type} [Field F]

@[simp] theorem tr_isFT (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace isFT = f := rfl
@[simp] theorem tr_isLT (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace isLT = l := rfl
@[simp] theorem tr_head (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace head = a.head := rfl
@[simp] theorem tr_cl (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace cl = a.cl := rfl
@[simp] theorem tr_z1a (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace z1a = a.z1a := rfl
@[simp] theorem tr_route0 (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace route0 = a.route0 := rfl
@[simp] theorem tr_R (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace AxisChipJ9.R = a.R := rfl
@[simp] theorem tr_pw (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace pw = a.pw := rfl
@[simp] theorem tr_l (a : ARow F) (f l' : F) (x : ℕ → F) : (a.rowEnv f l' x).trace AxisChipJ9.l = a.l := rfl
@[simp] theorem tr_axK (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace axK = a.axK := rfl
@[simp] theorem tr_axS (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace axS = a.axS := rfl
@[simp] theorem tr_hrv (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace hrv = a.hrv := rfl
@[simp] theorem tr_hink (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace hink = a.hink := rfl
@[simp] theorem tr_hinv (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace hinv = a.hinv := rfl
@[simp] theorem tr_houtk (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace houtk = a.houtk := rfl
@[simp] theorem tr_houtv (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace houtv = a.houtv := rfl
@[simp] theorem tr_v (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace AxisChipJ9.v = a.v := rfl
@[simp] theorem tr_invg4 (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace invg4 = a.invg4 := rfl
@[simp] theorem tr_r0h (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace AxisChipJ9.r0h = a.r0h := rfl
@[simp] theorem tr_ftk (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace ftk = a.ftk := rfl
@[simp] theorem tr_ftv (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace ftv = a.ftv := rfl
@[simp] theorem tr_mu (a : ARow F) (f l : F) (x : ℕ → F) : (a.rowEnv f l x).trace AxisChipJ9.mu = a.mu := rfl
@[simp] theorem trN (a : ARow F) (f l : F) (x : ℕ → F) (c : ℕ) : (a.rowEnv f l x).traceNext c = x c := rfl

@[simp] theorem col_head (a : ARow F) (f l' : F) : a.col f l' head = a.head := rfl
@[simp] theorem col_cl (a : ARow F) (f l' : F) : a.col f l' cl = a.cl := rfl
@[simp] theorem col_route0 (a : ARow F) (f l' : F) : a.col f l' route0 = a.route0 := rfl
@[simp] theorem col_R (a : ARow F) (f l' : F) : a.col f l' AxisChipJ9.R = a.R := rfl
@[simp] theorem col_pw (a : ARow F) (f l' : F) : a.col f l' pw = a.pw := rfl
@[simp] theorem col_l (a : ARow F) (f l' : F) : a.col f l' AxisChipJ9.l = a.l := rfl
@[simp] theorem col_hrv (a : ARow F) (f l' : F) : a.col f l' hrv = a.hrv := rfl
@[simp] theorem col_hink (a : ARow F) (f l' : F) : a.col f l' hink = a.hink := rfl
@[simp] theorem col_hinv (a : ARow F) (f l' : F) : a.col f l' hinv = a.hinv := rfl
@[simp] theorem col_v (a : ARow F) (f l' : F) : a.col f l' AxisChipJ9.v = a.v := rfl

variable (ls : List ℕ) (route0 : Bool) (R hrv vv mu : ℕ) (g4 : F) (houts : ℕ → ℕ × ℕ)

local notation "CR" => chainRow (F := F) ls route0 R hrv vv mu g4 houts

theorem ite01 (c : Prop) [Decidable c] : (if c then (1 : F) else 0) = 0 ∨ (if c then (1 : F) else 0) = 1 := by
  split_ifs <;> simp

/-- **Every chain row meets the current-row facts** (`2 ≤ L`; table masks consistent with the row: a table-first
row is a head, a table-last row is chain-last; a skipped top read keeps the handle; every intermediate segment
noun is a cell). -/
theorem chainRow_curOK (hL : 2 ≤ ls.length) {j : ℕ} (hj : j < ls.length) {fst lst : F}
    (hF : fst = 0 ∨ fst = 1) (hLs : lst = 0 ∨ lst = 1) (hF1 : fst = 1 → j = 0) (hL1 : lst = 1 → j + 1 = ls.length)
    (hz : ls.getD (ls.length - 1) 0 = 1 → houts 0 = (1, hrv))
    (hcell : ∀ k, k + 1 < ls.length → (houts k).1 = 1) (nxt : ℕ → F) :
    CurOK ((CR j).rowEnv fst lst nxt) := by
  have hBf : (Bf : F) = 2 ^ 32 := rfl
  rcases j with _ | k
  · have hne : ¬ (0 + 1 = ls.length) := by omega
    have hz' : ∀ (b : Bool), ((b && true) = b) := fun b => by cases b <;> rfl
    refine ⟨hF, hLs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [tr_isFT, tr_isLT, tr_head, tr_cl, tr_z1a, tr_route0, tr_R, tr_pw, tr_l, tr_axK, tr_axS, tr_hrv,
        tr_hink, tr_hinv, tr_houtk, tr_houtv, tr_v, tr_invg4, tr_r0h, tr_ftk, tr_ftv, tr_mu, chainRow]
    · simp
    · exact ite01 _
    · exact ite01 _
    · cases route0 <;> simp
    · simp
    · simp
    · simp [hBf]
    · simp
    · intro h
      split_ifs at h with hc
      · have h1 : ls.getD (ls.length - 1) 0 = 1 := by simpa using hc
        simp only [Nat.sub_zero]; rw [h1]; simp [hz h1]
      · exact absurd h zero_ne_one
    · simp
    · simp
    · simp [hne]
    · simp [hne]
    · intro h; rcases hLs with h' | h'
      · rw [h'] at h; exact absurd h zero_ne_one
      · exact absurd (hL1 (h' ▸ h)) hne
    · simp
    · cases route0 <;> simp
    · cases route0 <;> simp
    · cases route0 <;> simp
    · simp [hne]
  · have hk0 : k + 1 ≠ 0 := by omega
    refine ⟨hF, hLs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [tr_isFT, tr_isLT, tr_head, tr_cl, tr_z1a, tr_route0, tr_R, tr_pw, tr_l, tr_axK, tr_axS, tr_hrv,
        tr_hink, tr_hinv, tr_houtk, tr_houtv, tr_v, tr_invg4, tr_r0h, tr_ftk, tr_ftv, tr_mu, chainRow]
    · simp
    · exact ite01 _
    · simp
    · cases route0 <;> simp
    · simp
    · simp
    · simp
    · simp [hBf]
    · simp
    · simp
    · intro _; simp [hcell k (by omega)]
    · intro h
      have hk1 : k + 1 + 1 = ls.length := by
        by_contra hc; simp [hc] at h
      have : ls.length + 1 - (k + 1) = 2 := by omega
      simp [this]
    · simp
    · intro h; rcases hLs with h' | h'
      · rw [h'] at h; exact absurd h zero_ne_one
      · simp [hL1 (h' ▸ h)]
    · intro h; rcases hF with h' | h'
      · rw [h'] at h; exact absurd h zero_ne_one
      · exact absurd (hF1 (h' ▸ h)) hk0
    · cases route0 <;> simp
    · cases route0 <;> simp
    · cases route0 <;> simp
    · intro h; simp at h ⊢
      intro h2; exact absurd h2 h

/-- **Inside a chain**: row `j` and row `j + 1` meet the next-row facts (a field chain has two limbs, its `< p`
gate's inverse `g4` and its value `vv = hi·B + lo`). -/
theorem chainRow_nextOK (hL : 2 ≤ ls.length) {j : ℕ} (hj : j + 1 < ls.length) {fst lst fst' lst' : F}
    (h2 : route0 = true → ls.length = 2)
    (hg4 : route0 = true → ls.getD 0 0 = 0 ∨ ((ls.getD 1 0 : F) - (Bf - 1)) * g4 = 1)
    (hvv : route0 = true → (vv : F) = (ls.getD 1 0 : F) * Bf + (ls.getD 0 0 : F)) :
    NextOK ((CR j).rowEnv fst lst ((CR (j + 1)).col fst' lst')) := by
  have hne : ¬ (j + 1 = ls.length) := by omega
  have hBf : (Bf : F) = 2 ^ 32 := rfl
  refine ⟨fun _ => ?_, fun _ h => ?_, fun _ _ => ?_, fun h => ?_⟩
  · simp only [tr_cl, tr_head, tr_houtk, tr_houtv, tr_R, tr_hrv, tr_route0, tr_v, tr_pw, trN, col_hink, col_hinv,
      col_R, col_hrv, col_route0, col_v, col_pw, chainRow]
    refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
    rcases j with _ | k
    · simp; ring
    · have : ls.length + 1 - (k + 1) = (ls.length + 1 - (k + 1 + 1)) + 1 := by omega
      simp only [Nat.add_eq_zero, one_ne_zero, and_false, beq_iff_eq, if_false, Bool.false_eq_true]
      rw [this, pow_succ]; push_cast; ring
  · simp only [tr_cl, chainRow, hne, if_false] at h; exact absurd h zero_ne_one
  · simp [chainRow]
  · simp only [tr_r0h, chainRow] at h
    split_ifs at h with hc
    · simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hr, rfl⟩ := hc
      have hL2 := h2 hr
      simp only [trN, col_cl, col_l, tr_l, tr_v, chainRow, hL2, hr, if_true]
      refine ⟨by simp, ?_, ?_⟩
      · rcases hg4 hr with h0 | h0
        · left; simp only [List.getD_eq_getElem?_getD] at h0; simp [h0]
        · right; simpa using h0
      · simpa using hvv hr
    · exact absurd h zero_ne_one

/-- **Across a chain boundary**: a chain-last row and ANY next row with `head = 1` (the next chain's head) meet the
next-row facts. -/
theorem chainRow_nextOK_last (hL : 2 ≤ ls.length) {fst lst : F} (nxt : ℕ → F) (hnh : nxt head = 1) :
    NextOK ((CR (ls.length - 1)).rowEnv fst lst nxt) := by
  have he : ls.length - 1 + 1 = ls.length := by omega
  have hne : ¬ (ls.length - 1 = 0) := by omega
  refine ⟨fun h => ?_, fun _ _ => by simpa using hnh, fun _ h => ?_, fun h => ?_⟩
  · simp only [tr_cl, chainRow, he, if_true] at h; exact absurd h one_ne_zero
  · simp only [tr_cl, chainRow, he, if_true] at h; exact absurd h one_ne_zero
  · simp only [tr_r0h, chainRow] at h
    split_ifs at h with hc
    · simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact absurd hc.2 hne
    · exact absurd h zero_ne_one

end ChainLemmas

/-! ## 3. The table of concatenated chains: `hgate` of `ComplJ9AAxisH.axisChipJ9_honest_sat` -/

section Table
variable {F : Type} [Field F]

/-- **One honest axis chain** (the parameters of `chainRow`). -/
structure ChainSpec (F : Type) where
  ls : List ℕ
  route0 : Bool
  R : ℕ
  hrv : ℕ
  vv : ℕ
  mu : ℕ
  g4 : F
  houts : ℕ → ℕ × ℕ

/-- Row `j` of a chain. -/
def ChainSpec.row (c : ChainSpec F) (j : ℕ) : ARow F := chainRow c.ls c.route0 c.R c.hrv c.vv c.mu c.g4 c.houts j

/-- The rows of a chain. -/
def ChainSpec.rows (c : ChainSpec F) : List (ARow F) := (List.range c.ls.length).map c.row

/-- **What an honest chain satisfies** (the side conditions of `chainRow_curOK` / `chainRow_nextOK`). -/
structure ChainSpec.OK (c : ChainSpec F) : Prop where
  two : 2 ≤ c.ls.length
  hz : c.ls.getD (c.ls.length - 1) 0 = 1 → c.houts 0 = (1, c.hrv)
  hcell : ∀ k, k + 1 < c.ls.length → (c.houts k).1 = 1
  h2 : c.route0 = true → c.ls.length = 2
  hg4 : c.route0 = true → c.ls.getD 0 0 = 0 ∨ ((c.ls.getD 1 0 : F) - (Bf - 1)) * c.g4 = 1
  hvv : c.route0 = true → (c.vv : F) = (c.ls.getD 1 0 : F) * Bf + (c.ls.getD 0 0 : F)

/-- The row-pair relation of the table. -/
def RelA (x y : ARow F) : Prop := ∀ f l f' l' : F, NextOK (x.rowEnv f l (y.col f' l'))

/-- **The table**: the chains' rows, concatenated. -/
def tableRows : List (ChainSpec F) → List (ARow F)
  | [] => []
  | c :: cs => c.rows ++ tableRows cs

theorem rows_ne_nil {c : ChainSpec F} (hc : c.OK) : c.rows ≠ [] := by
  have := hc.two
  simp only [ChainSpec.rows, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]; omega

theorem rows_head {c : ChainSpec F} (hc : c.OK) : ∀ y ∈ c.rows.head?, y.head = 1 := by
  intro y hy
  have h0 : 0 < c.ls.length := by have := hc.two; omega
  simp only [ChainSpec.rows, List.head?_map, List.head?_range, Option.mem_def] at hy
  rw [if_neg (by omega)] at hy
  simp only [Option.map_some, Option.some.injEq] at hy
  subst hy; simp [ChainSpec.row, chainRow]

theorem rows_last {c : ChainSpec F} (hc : c.OK) : ∀ x ∈ c.rows.getLast?, x = c.row (c.ls.length - 1) := by
  intro x hx
  simp only [ChainSpec.rows, List.getLast?_map, List.getLast?_range, Option.mem_def] at hx
  rw [if_neg (by have := hc.two; omega)] at hx
  simp only [Option.map_some, Option.some.injEq] at hx
  exact hx.symm

theorem rows_isChain {c : ChainSpec F} (hc : c.OK) : List.IsChain RelA c.rows := by
  refine List.isChain_iff_getElem.2 fun i hi => ?_
  simp only [ChainSpec.rows, List.length_map, List.length_range] at hi
  simp only [ChainSpec.rows, List.getElem_map, List.getElem_range]
  intro f l f' l'
  exact chainRow_nextOK c.ls c.route0 c.R c.hrv c.vv c.mu c.g4 c.houts hc.two hi hc.h2 hc.hg4 hc.hvv

theorem tableRows_head {cs : List (ChainSpec F)} (hcs : ∀ c ∈ cs, c.OK) :
    ∀ y ∈ (tableRows cs).head?, y.head = 1 := by
  cases cs with
  | nil => simp [tableRows]
  | cons c cs =>
    intro y hy
    simp only [tableRows, List.head?_append, Option.mem_def] at hy
    have hc := hcs c (List.mem_cons_self ..)
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 (by simpa using rows_ne_nil hc : c.rows.head? ≠ none)
    rw [hz] at hy; simp only [Option.some_or, Option.some.injEq] at hy; subst hy
    exact rows_head hc z hz

theorem tableRows_isChain : ∀ {cs : List (ChainSpec F)}, (∀ c ∈ cs, c.OK) → List.IsChain RelA (tableRows cs)
  | [], _ => by simp [tableRows]
  | c :: cs, hcs => by
    have hc := hcs c (List.mem_cons_self ..)
    have hcs' : ∀ c' ∈ cs, c'.OK := fun c' h => hcs c' (List.mem_cons_of_mem _ h)
    refine List.isChain_append.2 ⟨rows_isChain hc, tableRows_isChain hcs', fun x hx y hy => ?_⟩
    rw [rows_last hc x hx]
    intro f l f' l'
    have hd := tableRows_head hcs' y hy
    exact chainRow_nextOK_last c.ls c.route0 c.R c.hrv c.vv c.mu c.g4 c.houts hc.two _ (by simpa using hd)

theorem mem_tableRows : ∀ {cs : List (ChainSpec F)} {x : ARow F}, x ∈ tableRows cs →
    ∃ c ∈ cs, ∃ j < c.ls.length, x = c.row j
  | [], x, hx => by simp [tableRows] at hx
  | c :: cs, x, hx => by
    simp only [tableRows, List.mem_append] at hx
    rcases hx with hx | hx
    · simp only [ChainSpec.rows, List.mem_map, List.mem_range] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      exact ⟨c, List.mem_cons_self .., j, hj, rfl⟩
    · obtain ⟨c', hc', j, hj, rfl⟩ := mem_tableRows hx
      exact ⟨c', List.mem_cons_of_mem _ hc', j, hj, rfl⟩

theorem tableRows_last : ∀ {cs : List (ChainSpec F)}, (∀ c ∈ cs, c.OK) →
    ∀ x ∈ (tableRows cs).getLast?, x.cl = 1
  | [], _ => by simp [tableRows]
  | c :: cs, hcs => by
    intro x hx
    have hc := hcs c (List.mem_cons_self ..)
    have hcs' : ∀ c' ∈ cs, c'.OK := fun c' h => hcs c' (List.mem_cons_of_mem _ h)
    simp only [tableRows, List.getLast?_append, Option.mem_def] at hx
    cases h : (tableRows cs).getLast? with
    | some z =>
      rw [h] at hx; simp only [Option.some_or, Option.some.injEq] at hx; subst hx
      exact tableRows_last hcs' z h
    | none =>
      rw [h] at hx; simp only [Option.none_or] at hx
      rw [rows_last hc x hx]
      have : c.ls.length - 1 + 1 = c.ls.length := by have := hc.two; omega
      simp [ChainSpec.row, chainRow, this]

end Table

/-! ## 4. `hgate` for the table -/

section Hgate
variable {F : Type} [Field F]

/-- **The table's column function** (`rows[i]`'s columns; the masks `0 / 1` are `fullCol`'s). -/
def tableCol (rows : List (ARow F)) {n : ℕ} (hn0 : 0 < n) (hn : n = rows.length) : ℕ → Fin n → F :=
  fun c i => (rows[i.1]'(hn ▸ i.2)).col (if (i : ℕ) = 0 then 1 else 0)
    (if i = ⟨n - 1, Nat.sub_lt hn0 (by omega)⟩ then 1 else 0) c

theorem fullCol_row (rows : List (ARow F)) {n : ℕ} (hn0 : 0 < n) (hn : n = rows.length) (i : Fin n) (j : ℕ) :
    fullCol hn0 (tableCol rows hn0 hn) j i =
      (rows[i.1]'(hn ▸ i.2)).col (fullCol hn0 (tableCol rows hn0 hn) 0 i) (fullCol hn0 (tableCol rows hn0 hn) 1 i) j := by
  rcases j with _ | _ | j
  · rfl
  · rfl
  · conv_lhs => unfold fullCol
    rw [if_neg (by omega), if_neg (by omega)]
    rfl

/-- **`hgate` of `ComplJ9AAxisH.axisChipJ9_honest_sat` for a table of honest chains.** -/
theorem tableRows_hgate {cs : List (ChainSpec F)} (hcs : ∀ c ∈ cs, c.OK) {n : ℕ} (hn0 : 0 < n)
    (hn : n = (tableRows cs).length) (i : Fin n) (nxt : ℕ → F)
    (hnxt : ∀ hi : (i : ℕ) + 1 < n, ∀ j, nxt j = fullCol hn0 (tableCol (tableRows cs) hn0 hn) j ⟨(i : ℕ) + 1, hi⟩) :
    ∀ g ∈ (AxisChipJ9.baseGates : List (CoeffExpr F)),
      g.eval (ComplJ9AAxisH.envC hn0 (tableCol (tableRows cs) hn0 hn) i nxt) = 0 := by
  set rows := tableRows cs with hrows
  set col := tableCol rows hn0 hn with hcol
  set m0 := fullCol hn0 col 0 i with hm0
  set m1 := fullCol hn0 col 1 i with hm1
  have hi : (i : ℕ) < rows.length := hn ▸ i.2
  have henv : ComplJ9AAxisH.envC hn0 col i nxt = (rows[i.1]'hi).rowEnv m0 m1 nxt := by
    simp only [ComplJ9AAxisH.envC, ARow.rowEnv]
    congr 1
    funext j
    exact fullCol_row rows hn0 hn i j
  rw [henv]
  apply baseGates_of_pairOK
  obtain ⟨c, hc, j, hj, hx⟩ := mem_tableRows (List.getElem_mem hi)
  have hcOK := hcs c hc
  have hm0v : m0 = if (i : ℕ) = 0 then 1 else 0 := rfl
  have hm1v : m1 = if i = ⟨n - 1, Nat.sub_lt hn0 (by omega)⟩ then 1 else 0 := rfl
  have hcur : CurOK ((rows[i.1]'hi).rowEnv m0 m1 nxt) := by
    rw [hx]
    refine chainRow_curOK c.ls c.route0 c.R c.hrv c.vv c.mu c.g4 c.houts hcOK.two hj
      (by rw [hm0v]; split_ifs <;> simp) (by rw [hm1v]; split_ifs <;> simp) (fun h1 => ?_) (fun h1 => ?_)
      hcOK.hz hcOK.hcell nxt
    · rw [hm0v] at h1
      split_ifs at h1 with h0
      · have hhead := tableRows_head hcs (rows[i.1]'hi) (by
          simp only [List.head?_eq_getElem?, Option.mem_def]; simp [h0, hrows])
        rw [hx] at hhead
        by_contra hj0
        simp [ChainSpec.row, chainRow, hj0] at hhead
      · exact absurd h1 zero_ne_one
    · rw [hm1v] at h1
      split_ifs at h1 with h0
      · have hlast := tableRows_last hcs (rows[i.1]'hi) (by
          have hi' : (i : ℕ) = n - 1 := by simpa using congrArg Fin.val h0
          simp only [List.getLast?_eq_getElem?, Option.mem_def]
          rw [List.getElem?_eq_getElem (by omega)]
          simp only [Option.some.injEq]
          congr 1; omega)
        rw [hx] at hlast
        by_contra hj0
        simp [ChainSpec.row, chainRow, hj0] at hlast
      · exact absurd h1 zero_ne_one
  by_cases hlt : (i : ℕ) + 1 < n
  · refine ⟨hcur, ?_⟩
    have hnx : nxt = (rows[(i : ℕ) + 1]'(by omega)).col (fullCol hn0 col 0 ⟨(i : ℕ) + 1, hlt⟩)
        (fullCol hn0 col 1 ⟨(i : ℕ) + 1, hlt⟩) := by
      funext j
      rw [hnxt hlt j]
      exact fullCol_row rows hn0 hn ⟨(i : ℕ) + 1, hlt⟩ j
    rw [hnx]
    exact (tableRows_isChain hcs).getElem (i : ℕ) (by omega) _ _ _ _
  · have hL : ((rows[i.1]'hi).rowEnv m0 m1 nxt).trace isLT = 1 := by
      show m1 = 1
      rw [hm1v, if_pos (Fin.ext (by simp; omega))]
    exact pairOK_last hcur hL

end Hgate

/-! ## 5. The honest axis chip of a table of chains -/

section Honest
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension Module Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) {h n : ℕ}
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- **The honest axis chip of a table of honest chains** (the `AXChipOK` left-disjunct chip conjuncts): from the
chains' side conditions, the orbit facts, no vanishing key denominator (completeness bad events) and the two
terminal publics. -/
theorem axisChipJ9_honest_table {cs : List (ChainSpec F)} (hcs : ∀ c ∈ cs, c.OK) (hn0 : 0 < n)
    (hn : n = (tableRows cs).length) (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hden : ∀ i : Fin n, ComplJ9AAxisH.dKey δ chals hn0 (tableCol (tableRows cs) hn0 hn) AxisChipJ9.limbKey i ≠ 0 ∧
      ComplJ9AAxisH.dKey δ chals hn0 (tableCol (tableRows cs) hn0 hn) AxisChipJ9.pathKey i ≠ 0 ∧
      ComplJ9AAxisH.dKey δ chals hn0 (tableCol (tableRows cs) hn0 hn) AxisChipJ9.tagKey i ≠ 0)
    (hpS : Quad.mk _ (pubs pubAXs) (pubs (pubAXs + 1)) =
      ∑ i, ((ComplJ9AAxisH.dKey δ chals hn0 (tableCol (tableRows cs) hn0 hn) AxisChipJ9.limbKey i)⁻¹ -
        liftQ δ (tableCol (tableRows cs) hn0 hn AxisChipJ9.mu i) *
          (ComplJ9AAxisH.dKey δ chals hn0 (tableCol (tableRows cs) hn0 hn) AxisChipJ9.tagKey i)⁻¹))
    (hpP : Quad.mk _ (pubs pubAXp) (pubs (pubAXp + 1)) =
      ∑ i, liftQ δ (1 - tableCol (tableRows cs) hn0 hn AxisChipJ9.z1a i) *
        (ComplJ9AAxisH.dKey δ chals hn0 (tableCol (tableRows cs) hn0 hn) AxisChipJ9.pathKey i)⁻¹) :
    (axisChipJ9 δ b hn0 nodes orbit chals pubs).rap.Satisfies
        (ComplJ9AAxisH.polyAx δ b hn0 nodes orbit chals pubs (tableCol (tableRows cs) hn0 hn)) ∧
      (axisChipJ9 δ b hn0 nodes orbit chals pubs).BindsPreprocessing
        (ComplJ9AAxisH.polyAx δ b hn0 nodes orbit chals pubs (tableCol (tableRows cs) hn0 hn)) :=
  ComplJ9AAxisH.axisChipJ9_honest_sat δ b hn0 nodes orbit chals pubs _ hinj hadj
    (fun i nxt hnxt => tableRows_hgate hcs hn0 hn i nxt hnxt) hden hpS hpP

end Honest

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisRows

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisRows
#print axioms baseGates_of_pairOK
#print axioms pairOK_last
#print axioms chainRow_curOK
#print axioms chainRow_nextOK
#print axioms chainRow_nextOK_last
#print axioms tableRows_isChain
#print axioms tableRows_hgate
#print axioms axisChipJ9_honest_table
end Axioms
