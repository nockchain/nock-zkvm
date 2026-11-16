/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ChipHX9.lean

  `ChipHX.lean` is NOT edited; everything here is a new name.

  **Layout (APPENDED after J-8's `0..122`; `widthHX9 = 137`, `layoutX9_tiles`).**

  | col | name | use |
  |---|---|---|
  | `123, 124, 125` | `sS0B`, `sS10B`, `sS10S` | new one-hot states (op 0 big/field axis, op 10 big axis, segment pseudo-row) |
  | `126` | `xIdX` | the `TAG_ax` / limb id (`s0B`, `s10B`, `s10S`) |
  | `127, 128` | `kLabX`, `vLabX` | the routed child label `(k, v)` (`s10B`'s chain root, `s10S`'s next segment) |
  | `129, 130` | `m4X`, `m5X` | the two top bits of `s10S`'s 6-bit `m` |
  | `131` | `hdC` | `s10S` head flag |
  | `132, 133` | `aAX`, `aBX` | `m ≠ 63` products |
  | `134` | `limbX` | `s10S`'s limb `l` |
  | `135` | `axLX` | `s10S`'s limb axis |
  | `136` | `segX` | `s10S`'s segment axis (non-serial copy of `m.v`) |

  `s10S` REUSES the global booleans `β, fast, l₁.k, l₂.k` as `m₀..m₃` and the
  atom-only columns `v, v2, w, inv4, ax2` as `pw1, pw2, pw, zA, zB`; every J-8 gate on those columns
  is gated by a J-8 state (zero on an `s10S` row).

  **Changed J-8 gates (only in the twin):** the one-hot sum (20 states), `kindG` on the formula
  handle (`(1 − sS10S)·kc(f)·kb(f)`), `svG`'s formula-kind gate (`(1 − sS10S)·(…) +
  sS10S·(f.k − 2)(f.k − 3)`), `prGateX` (`− sS10S·(1 − z1)`).  Every other J-8 base gate is kept
  verbatim (`arithKeptX9`, `changedJ8_receipt`), so `baseHoldsX_of_X9` reuses every J-8 row lemma
  on old-state rows.

  **F1 (serial-free instrument): exactly ONE allowlisted gate**, the kind-3 label decode
  `sS10S·kc(f)·(f.v − 64·id − m)` (`arithGatesX9_allowlist`).  The kind-2 decode `f.v = id` and the
  `s10B` route `vR = ftth.v` (big axis) are `EqG` entries; the remaining arithmetic sits on non-serial
  columns (`vLab`, `xId`, `segX`).  **F3:** the gate `sS10S·m.k = 0` is ADDED (`s10S_row` (9)).
  **F4:** `kidFormsX9 = kidFormsX ++ [(s10B, f_ttt), (s10B, f_tt)]`.

-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChipHX

namespace Nock.NockVMROM.Thm54
namespace VclL.Handle
namespace ChipHX9

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.Framework

set_option autoImplicit false
set_option linter.unusedSectionVars false

-- Structural equality on gate expressions.
deriving instance DecidableEq for CoeffExpr
deriving instance DecidableEq for Opnd
deriving instance DecidableEq for EqG

noncomputable section

/-! ## 1. Layout -/

def sS0B : ℕ := 123
def sS10B : ℕ := 124
def sS10S : ℕ := 125
def newStates : List ℕ := [sS0B, sS10B, sS10S]
/-- The twin's 20 one-hot states: J-8's `0..16` and the three appended ones. -/
def statesX9 : List ℕ := List.range nStates ++ newStates

def xIdX : ℕ := 126
def kLabX : ℕ := 127
def vLabX : ℕ := 128
def m4X : ℕ := 129
def m5X : ℕ := 130
def hdC : ℕ := 131
def aAX : ℕ := 132
def aBX : ℕ := 133
def limbX : ℕ := 134
def axLX : ℕ := 135
def segX : ℕ := 136

/-- Reused J-8 columns on `s10S` rows. -/
def m0X : ℕ := betaX
def m1X : ℕ := fastX
def m2X : ℕ := xL1.k
def m3X : ℕ := xL2.k
def pw1X : ℕ := vX
def pw2X : ℕ := v2X
def pwX : ℕ := wX
def zAX : ℕ := inv4X
def zBX : ℕ := ax2X

def mBitsX : List ℕ := [m0X, m1X, m2X, m3X, m4X, m5X]

/-- **The twin's width.** -/
def widthHX9 : ℕ := 137

/-- The appended columns tile `123 .. 137`; the twin's states are distinct; the reused `s10S`
columns are J-8 columns and are pairwise distinct. -/
theorem layoutX9_tiles :
    widthHX9 = widthHX + 14 ∧
    [sS0B, sS10B, sS10S, xIdX, kLabX, vLabX, m4X, m5X, hdC, aAX, aBX, limbX, axLX, segX] =
      List.range' widthHX 14 ∧
    statesX9.Nodup ∧ statesX9.length = 20 ∧
    ([m0X, m1X, m2X, m3X, pw1X, pw2X, pwX, zAX, zBX].all fun i => decide (i < widthHX)) = true ∧
    [m0X, m1X, m2X, m3X, pw1X, pw2X, pwX, zAX, zBX].Nodup ∧ mBitsX.Nodup := by
  decide +kernel

/-! ## 2. Gates (generic builders; the template is read at `ℚ`) -/

section Gates
variable {F : Type} [Field F]

/-- `m = Σ 2^i m_i` over the six bits. -/
def mValE : CoeffExpr F :=
  .add (cc m0X) (.add (.mul (.const 2) (cc m1X)) (.add (.mul (.const 4) (cc m2X))
    (.add (.mul (.const 8) (cc m3X)) (.add (.mul (.const 16) (cc m4X)) (.mul (.const 32) (cc m5X))))))

/-! ### The four changed J-8 gates (J-8 gate + terms in the new selectors) -/

/-- J-8's formula-kind gate `f.k − 1 + s10L + s10T` (`svG`'s second entry). -/
def svXF8 : CoeffExpr F := .add (.add (.sub (cc xF.k) (.const 1)) (cc sS10L)) (cc sS10T)

/-- The one-hot sum over 20 states. -/
def oneHotSumX9 : CoeffExpr F := .sub (.add (selS (List.range nStates)) (selS newStates)) (.const 1)

/-- `kindG` on the formula handle, relaxed on `s10S` (a kind-3 formula, `kc = kb = 1`). -/
def kindRelaxX9 : CoeffExpr F := .mul (oneMinus (cc sS10S)) (.mul (kcE xF) (kbE xF))

/-- `svG`'s formula kind: `1` off `s10L/s10T/s10S`; `∈ {2, 3}` on `s10S`. -/
def svXFX9 : CoeffExpr F :=
  .add (.mul (oneMinus (cc sS10S)) svXF8)
    (prodL [cc sS10S, .sub (cc xF.k) (.const 2), .sub (cc xF.k) (.const 3)])

/-- `pr − s5·β·(1 − z1) − s10L − s10S·(1 − z1)`: `s10S` uses `slot2`'s walk pair. -/
def prGateX9 : CoeffExpr F := .sub prGateX (.mul (cc sS10S) (notC z1X))

/-! ### New gates -/

/-- Booleanity of the new one-hot states and the new boolean columns. -/
def newBoolG9 : List (CoeffExpr F) :=
  newStates.map (fun j => boolG (cc j)) ++ [boolG (cc m4X), boolG (cc m5X), boolG (cc hdC)]

/-- **op 0, `s0B`** (big / field axis read): `f_t` is an atom, axis `≠ 1`, the subject is a cell. -/
def s0BG : List (CoeffExpr F) :=
  [.mul (cc sS0B) (kcE xFt), .mul (cc sS0B) (cc z1X), .mul (cc sS0B) (oneMinus (kcE xS))]

/-- **op 10, `s10B`** (big axis): `f_tth` an atom, no `z1`, `e` a cell, the decode parents are
cells (the `l2X` / `l3X` twins), and the routed chain-root label: `kR = 3 − kb(f_tth)` (kind 2 for a
big axis, kind 3 for a field axis); on a field axis `vR = 64·id + 1` (the big-axis case
`vR = f_tth.v` is the `EqG` `s10BEq`, F1). -/
def s10BG : List (CoeffExpr F) :=
  [.mul (cc sS10B) (kcE xFtth), .mul (cc sS10B) (cc z1X), .mul (cc sS10B) (oneMinus (kcE xE)),
   .mul (cc sS10B) (oneMinus (kcE xFt)), .mul (cc sS10B) (oneMinus (kcE xFth)),
   .mul (cc sS10B) (.add (.sub (cc kLabX) (.const 3)) (kbE xFtth)),
   prodL [cc sS10B, oneMinus (kbE xFtth),
     .sub (.sub (cc vLabX) (.mul (.const 64) (cc xIdX))) (.const 1)]]

/-- **op 10, `s10S`** (segment pseudo-row), all serial-free. -/
def s10SG : List (CoeffExpr F) :=
  let S : CoeffExpr F := cc sS10S
  let z : CoeffExpr F := .mul (cc zAX) (cc zBX)
  [.mul S (oneMinus (kbE xF)),
   prodL [S, oneMinus (kcE xF), notC hdC],
   .mul S (.sub (cc pw1X) (prodL [.add (.const 1) (cc m0X), .add (.const 1) (.mul (.const 3) (cc m1X)),
      .add (.const 1) (.mul (.const 15) (cc m2X))])),
   .mul S (.sub (cc pw2X) (prodL [.add (.const 1) (.mul (.const 255) (cc m3X)),
      .add (.const 1) (.mul (.const 65535) (cc m4X)),
      .add (.const 1) (.mul (.const 4294967295) (cc m5X))])),
   .mul S (.sub (cc pwX) (prodL [.const 2, cc pw1X, cc pw2X])),
   .mul S (.sub (cc aAX) (prodL [cc m0X, cc m1X, cc m2X])),
   .mul S (.sub (cc aBX) (prodL [cc m3X, cc m4X, cc m5X])),
   prodL [S, cc aAX, cc aBX],
   .mul S (.sub (cc zAX) (prodL [notC m0X, notC m1X, notC m2X])),
   .mul S (.sub (cc zBX) (prodL [notC m3X, notC m4X, notC m5X])),
   .mul S (.sub (cc axLX) (.add (.mul (cc hdC) (.sub (cc pwX) (.const 1)))
      (.mul (notC hdC) (.sub (.mul (.const 2) (cc pwX)) (.const 2))))),
   .mul S (.sub (cc segX) (.add (cc limbX) (.mul (notC hdC) (.const 4294967296)))),
   prodL [S, cc z1X, .sub (cc segX) (.const 1)],
   prodL [S, cc z1X, notC hdC],
   .mul S (cc xM.k),
   .mul S (.sub (cc kLabX) (.mul (.const 3) (oneMinus z))),
   .mul S (.sub (.sub (cc vLabX) z)
      (.mul (oneMinus z) (.sub (.add (.mul (.const 64) (cc xIdX)) mValE) (.const 1))))]

/-- **The ONE allowlisted gate (F1)**: the kind-3 label decode `f.v = 64·id + m` on `s10S`.  It is
arithmetic on the serial-capable `f.v`; `D (3, ·)` is DEFINED through it. -/
def decodeG9 : CoeffExpr F :=
  prodL [cc sS10S, kcE xF, .sub (.sub (cc xF.v) (.mul (.const 64) (cc xIdX))) mValE]

/-- **F4**: the real-child formula handles of the twin. -/
def kidFormsNew : List (ℕ × Hd) := [(sS10B, xFttt), (sS10B, xFtt)]
def kidFormsX9 : List (ℕ × Hd) := kidFormsX ++ kidFormsNew
def kidKindNew : List (CoeffExpr F) := kidFormsNew.map fun jh => .mul (cc jh.1) (oneMinus (kcE jh.2))

/-! ### Equality tests -/

def svEqNew : List (EqG F) := [⟨cc sS0B, xFh.v, .cst 0⟩, ⟨cc sS10B, xFh.v, .cst 10⟩]
/-- The big-axis route `vR = f_tth.v` as an equality test. -/
def s10BEq : List (EqG F) := [⟨.mul (cc sS10B) (kbE xFtth), vLabX, .col xFtth.v⟩]
/-- The kind-2 decode `f.v = id` and the segment copy `m.v = seg` as equality tests; the pair
substitution `sf1 = s`, `sf2 = e`, and at `z1` `f_tth = s`, `f_ttt = e`. -/
def s10SEq : List (EqG F) :=
  [⟨.mul (cc sS10S) (oneMinus (kcE xF)), xF.v, .col xIdX⟩, ⟨cc sS10S, xM.v, .col segX⟩] ++
  heq (cc sS10S) xSf1 xS ++ heq (cc sS10S) xSf2 xE ++
  heq (.mul (cc sS10S) (cc z1X)) xFtth xS ++ heq (.mul (cc sS10S) (cc z1X)) xFttt xE

def eqGatesX9 : List (EqG F) := eqGatesX ++ svEqNew ++ s10BEq ++ s10SEq

end Gates

/-! ### The twin's arithmetic gate list (read at `ℚ`) -/

/-- The four J-8 gates the twin changes. -/
def changedJ8 : List (CoeffExpr ℚ) :=
  [.sub (selS (List.range nStates)) (.const 1), .mul (kcE xF) (kbE xF), svXF8, prGateX]

/-- The J-8 arithmetic gates kept verbatim. -/
def arithKeptX9 : List (CoeffExpr ℚ) :=
  (arithGatesX (F := ℚ)).filter fun g => decide (g ∉ changedJ8)

/-- The serial-free arithmetic gates. -/
def arithSF9 : List (CoeffExpr ℚ) :=
  arithKeptX9 ++ [oneHotSumX9, kindRelaxX9, svXFX9, prGateX9] ++ newBoolG9 ++ s0BG ++ s10BG ++
    s10SG ++ kidKindNew

/-- **The allowlist (F1): one gate.** -/
def allowlistX9 : List (CoeffExpr ℚ) := [decodeG9]

def arithGatesX9 : List (CoeffExpr ℚ) := arithSF9 ++ allowlistX9


/-- The changed J-8 gates are arithmetic gates of the J-8 chip, and the twin keeps all but four of them. -/
theorem changedJ8_receipt :
    (changedJ8.all fun g => decide (g ∈ (arithGatesX (F := ℚ)))) = true ∧
      arithKeptX9.length + 4 = (arithGatesX (F := ℚ)).length := by
  decide +kernel

/-! ## 3. Records, slots, accumulators -/

section Slots
variable {F : Type} [Field F]

/-- **The `TAG_ax` consume** `(hr.v, ft.k, ft.v, out.k, out.v, id, 0, TAG_ax = 5)` (8 entries, the
tag LAST, as the axis chip's provide). -/
def axRecX (r ft o : Hd) : List RE :=
  [.col r.v, .col ft.k, .col ft.v, .col o.k, .col o.v, .col xIdX, .k 0, .k 5]

/-- **The `s10S` limb consume** `(id, axL, 0, l)`: the `walkRecA` 4-entry shape (comb axis). -/
def limbRecX : List RE := [.col xIdX, .col axLX, .k 0, .col limbX]

/-- A J-8 slot with appended entries / pair states (same inverse, same pair). -/
def extSlot (S : SlotX F) (es : List (EntX F)) (ps : List ℕ) : SlotX F :=
  ⟨S.inv, S.invIm, S.ents ++ es, S.pair, S.pairStates ++ ps⟩

def ents0New : List (EntX F) := [⟨[sS0B, sS10B], .const 1, cellRecX xF xFh xFt, .x⟩]
def ents1New : List (EntX F) :=
  [⟨[sS10B], .const 1, cellRecX xFt xFth xFtt, .x⟩, ⟨[sS0B], .const 1, axRecX xS xFt xE, .s⟩]
def ents2New : List (EntX F) := [⟨[sS10B], .const 1, cellRecX xFth xFtth xFttt, .x⟩]
def ents3New : List (EntX F) :=
  [⟨[sS10B], .const 1, axRecX xE xFtth xSf1, .s⟩, ⟨[sS10S], .const 1, limbRecX, .s⟩]

/-- `slot0`: decode `f` also on `s0B`, `s10B`. -/
def slot0X9 : SlotX F := extSlot slot0X ents0New []
/-- `slot1`: decode `f_t` on `s10B`; **`s0B`'s `TAG_ax` consume on its OWN state** (not a
second state-0 entry, `naive_state0_split_breaks_disjoint`). -/
def slot1X9 : SlotX F := extSlot slot1X ents1New []
/-- `slot2`: decode `f_th` on `s10B`; the walk pair also on `s10S`. -/
def slot2X9 : SlotX F := extSlot slot2X ents2New [sS10S]
/-- `slot3` (`inv3`): `s10B`'s `TAG_ax` consume (replacing `s10`'s path read) and `s10S`'s limb
consume. -/
def slot3X9 : SlotX F := extSlot slot3X ents3New []

def slotsX9 : List (SlotX F) := [slot0X9, slot1X9, slot2X9, slot3X9]

/-- No 5th slot. -/
theorem slotsX9_length : (slotsX9 (F := F)).length = 4 := rfl

end Slots

section Acc
variable {F : Type} [Field F]

def accOf9 (b : Bal) (im : Bool) (accBase pubBase : ℕ) : List (CoeffExpr F) :=
  accGatesX (slotsX9.map fun S => ⟨S.actB b, if im then S.invIm else S.inv⟩) accBase pubBase

/-- The three `𝕂′` accumulators of the twin (same columns and publics as J-8). -/
def accGatesHX9 : List (CoeffExpr F) :=
  accOf9 .x false accXX pubRhoX ++ accOf9 .x true accXXi pubRhoXIm ++
  accOf9 .p false accPX pubRhoP ++ accOf9 .p true accPXi pubRhoPIm ++
  accOf9 .s false accSX pubRhoSX ++ accOf9 .s true accSXi pubRhoSXi

end Acc

/-- **The twin's base gates** (template at `ℚ`). -/
def baseGatesHX9 : List (CoeffExpr ℚ) :=
  arithGatesX9 ++ accGatesHX9 (F := ℚ) ++ (eqGatesX9 (F := ℚ)).map EqG.gate

/-- The twin's slot pairs over `𝕂′`. -/
def slotPairsX9 (F : Type) [Field F] (δ : F) : List (Q F) := (slotsX9 (F := F)).map (slotGateQX F δ)

/-- **Child labels per state** (the J-8 table on `0..16`, extended to the new states). -/
def childrenX9 : ℕ → List (List (Option ℕ))
  | 123 => []
  | 124 => [labX xS xFttt xSf1, labX xS xFtt xSf2,
      [some xSf2.k, some xSf2.v, some kLabX, some vLabX, some xE.k, some xE.v]]
  | 125 => [labX xS xM xE,
      [some xFtth.k, some xFtth.v, some kLabX, some vLabX, some xFttt.k, some xFttt.v]]
  | j => childrenX j

theorem fanoutX9_new :
    ((childrenX9 sS0B).length, (childrenX9 sS10B).length, (childrenX9 sS10S).length) = (0, 3, 2) ∧
    ∀ j ∈ List.range nStates, childrenX9 j = childrenX j := by
  decide +kernel

/-! ## 4. Degree -/

section Degree
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem baseTemplateX9_degree :
    (baseGatesHX9.all fun g => decide (g.degree ≤ 4)) = true := by decide +kernel

theorem act_deg_const1 (x : EntX F) (h : x.extra = .const 1) : x.act.degree ≤ 2 := by
  have hs : (selS (F := F) x.states).degree ≤ 1 :=
    CoeffExpr.degree_sumList_le _ _ _ fun i _ => by simp [cc, CoeffExpr.degree]
  simp only [EntX.act, h, CoeffExpr.degree]
  omega

theorem slotsX9_act_deg : ∀ S ∈ (slotsX9 : List (SlotX F)), ∀ x ∈ S.ents, x.act.degree ≤ 2 := by
  intro S hS x hx
  have old : ∀ S0 ∈ (slotsX : List (SlotX F)), ∀ es ps, S = extSlot S0 es ps →
      (∀ y ∈ es, y.extra = .const 1) → x.act.degree ≤ 2 := by
    intro S0 hS0 es ps hSe hes
    subst hSe
    rcases List.mem_append.mp hx with h | h
    · exact slotsX_act_deg S0 hS0 x h
    · exact act_deg_const1 x (hes x h)
  simp only [slotsX9, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · exact old slot0X (by simp [slotsX]) ents0New [] rfl (by simp [ents0New])
  · exact old slot1X (by simp [slotsX]) ents1New [] rfl (by simp [ents1New])
  · exact old slot2X (by simp [slotsX]) ents2New [sS10S] rfl (by simp [ents2New])
  · exact old slot3X (by simp [slotsX]) ents3New [] rfl (by simp [ents3New])

theorem slotPairsX9_degree (δ : F) : ∀ q ∈ slotPairsX9 F δ, qdeg F q ≤ 4 := by
  intro q hq
  obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hq
  exact slotGateQX_deg δ S (slotsX9_act_deg S hS)

end Degree

/-! ## 5. -/

section Instrument

/-- **Exactly ONE base arithmetic gate of the twin reads a serial-capable column**, and it is
the allowlisted kind-3 decode. -/
theorem arithGatesX9_allowlist :
    (arithGatesX9.filter fun g => !serialFreeX g) = allowlistX9 := by decide +kernel

theorem arithSF9_serialFree : (arithSF9.all serialFreeX) = true := by decide +kernel

theorem allowlistX9_one : allowlistX9.length = 1 ∧ serialFreeX (F := ℚ) decodeG9 = false := by
  decide +kernel

theorem accGatesHX9_serialFree : ((accGatesHX9 (F := ℚ)).all serialFreeX) = true := by decide +kernel

/-- Every equality test of the twin has a serial-free selector (the only serial read is the
difference). -/
theorem eqGatesX9_ok : ((eqGatesX9 (F := ℚ)).all EqG.okX) = true := by decide +kernel

theorem slotPairsX9_keyOK : (slotPairsX9 ℚ 7).all keyOKQX = true := by decide +kernel

/-- **Positive control (F1) 1**: the design's kind-2 decode written as arithmetic,
`sS10S·(1 − kc(f))·(f.v − id)`, IS flagged: hence its `EqG` form. -/
theorem serialFreeX_flags_naive_kind2 :
    serialFreeX (F := ℚ) (prodL [cc sS10S, oneMinus (kcE xF), .sub (cc xF.v) (cc xIdX)]) = false := by
  decide +kernel

/-- **Positive control (F1) 2**: the design's `s10B` route gate
`vR − f_tth.v − (1 − kb)(64·id + 1 − f_tth.v)` IS flagged: hence `s10BEq` + the `kb = 0` gate. -/
theorem serialFreeX_flags_naive_route :
    serialFreeX (F := ℚ) (.mul (cc sS10B) (.sub (.sub (cc vLabX) (cc xFtth.v))
      (.mul (oneMinus (kbE xFtth)) (.sub (.add (.mul (.const 64) (cc xIdX)) (.const 1)) (cc xFtth.v)))))
      = false := by
  decide +kernel

/-- **Positive control (F1) 3**: the design's segment gate on `m.v` directly,
`seg − hd·l − (1 − hd)(B + l)` with `seg := m.v`, IS flagged: hence the copy `segX`. -/
theorem serialFreeX_flags_naive_seg :
    serialFreeX (F := ℚ) (.mul (cc sS10S) (.sub (cc xM.v) (.add (cc limbX)
      (.mul (notC hdC) (.const 4294967296))))) = false := by
  decide +kernel

/-!

`xIdX` is a table row id (atom-table row `< nA` or split id `nA + s`), the class the axis chip
declares serial-capable.  At the twin serial set `serialColsX9 = serialColsX ++ [xIdX]` the
allowlist is the THREE `64·xId + …` gates, ONE injectivity family whose single justification is
`id < nA + nS < 2^57` (`hnAS`), enforced by no gate: ROWSEM derives the id bound on every
`s0B`/`s10B`/`s10S` row from the served service record. -/

def serialColsX9 : List ℕ := serialColsX ++ [xIdX]

/-- Serial-free at the twin serial set. -/
def serialFreeX9 {F : Type} [Field F] (g : CoeffExpr F) : Bool :=
  (colsOf g).all fun i => !serialColsX9.contains i

/-- The `s10B` field-axis route `s10B·(1 − kb(f_tth))·(vLab − 64·xId − 1)` (`s10BG`'s last gate). -/
def routeG9 : CoeffExpr ℚ :=
  prodL [cc sS10B, oneMinus (kbE xFtth), .sub (.sub (cc vLabX) (.mul (.const 64) (cc xIdX))) (.const 1)]

/-- The `s10S` next-segment label `s10S·(vLab − z − (1 − z)(64·xId + m − 1))` (`s10SG`'s last gate). -/
def nextLabG9 : CoeffExpr ℚ :=
  .mul (cc sS10S) (.sub (.sub (cc vLabX) (.mul (cc zAX) (cc zBX)))
    (.mul (oneMinus (.mul (cc zAX) (cc zBX))) (.sub (.add (.mul (.const 64) (cc xIdX)) mValE) (.const 1))))

/-- **The allowlist at the twin serial set: three gates** (the `64·xId` family). -/
def allowlistX9xId : List (CoeffExpr ℚ) := [routeG9, nextLabG9, decodeG9]


/-- The arithmetic gates of the twin that read a serial column are exactly `allowlistX9xId`. -/
theorem arithGatesX9_allowlist_xId :
    (arithGatesX9.filter fun g => !serialFreeX9 g) = allowlistX9xId := by decide +kernel

theorem allowlistX9xId_three : allowlistX9xId.length = 3 ∧
    (allowlistX9xId.all fun g => decide (g ∈ arithGatesX9) && !serialFreeX9 g) = true := by
  decide +kernel

/-- The accumulator gates stay serial-free at the twin serial set. -/
theorem accGatesHX9_serialFree9 : ((accGatesHX9 (F := ℚ)).all serialFreeX9) = true := by decide +kernel

/-- Positive controls re-run at the twin serial set (the three naive forms stay flagged). -/
theorem serialFreeX9_flags_naive :
    serialFreeX9 (F := ℚ) (prodL [cc sS10S, oneMinus (kcE xF), .sub (cc xF.v) (cc xIdX)]) = false ∧
    serialFreeX9 (F := ℚ) (.mul (cc sS10B) (.sub (.sub (cc vLabX) (cc xFtth.v))
      (.mul (oneMinus (kbE xFtth)) (.sub (.add (.mul (.const 64) (cc xIdX)) (.const 1)) (cc xFtth.v)))))
      = false ∧
    serialFreeX9 (F := ℚ) (.mul (cc sS10S) (.sub (cc xM.v) (.add (cc limbX)
      (.mul (notC hdC) (.const 4294967296))))) = false := by
  decide +kernel

end Instrument

/-! ## 6. -/

section ReadSet

def consumesX9 (st : ℕ) : List (List RE × Bal) :=
  (slotsX9 (F := ℚ)).flatMap fun S =>
    ((S.ents.filter fun x => decide (st ∈ x.states)).map fun x => (x.rcd, x.bal)) ++
      (if st ∈ S.pairStates then
        match S.pair with
        | some (_, a, b, bal) => [(a, bal), (b, bal)]
        | none => []
       else [])

/-- One inverse per slot serves at most one entry or one pair (the `s0B` read has its own state). -/
theorem slotsX9_disjoint :
    ((slotsX9 (F := ℚ)).all fun S => ((S.ents.flatMap EntX.states) ++ S.pairStates).Nodup) = true := by
  decide +kernel

/-- **Old states read exactly what they read in J-8.** -/
theorem consumesX9_old : ∀ st ∈ List.range nStates, consumesX9 st = consumesX st := by
  decide +kernel

theorem consumesX9_s0B :
    consumesX9 sS0B = [(cellRecX xF xFh xFt, .x), (axRecX xS xFt xE, .s)] := by decide +kernel

theorem consumesX9_s10B :
    consumesX9 sS10B = [(cellRecX xF xFh xFt, .x), (cellRecX xFt xFth xFtt, .x),
      (cellRecX xFth xFtth xFttt, .x), (axRecX xE xFtth xSf1, .s)] := by decide +kernel

theorem consumesX9_s10S :
    consumesX9 sS10S = [(walkRecX xSf1 xM.v xFtth, .p), (walkRecX xSf2 xM.v xFttt, .p),
      (limbRecX, .s)] := by decide +kernel

/-- **The SERVICE balance of the twin consumes:** `TAG_inc` (op 4 slow), the α pair's two
`walkRecA` (op 5), `TAG_jet` (`s11j`), and the new `TAG_ax` (`s0B`, `s10B`) and limb (`s10S`,
`walkRecA` shape). -/
theorem service_consumers9 :
    (statesX9.flatMap fun st =>
      ((consumesX9 st).filter fun r => decide (r.2 = .s)).map Prod.fst) =
      [incRecX, walkRecAX xFtth xL1, walkRecAX xFttt xL2, jetRecX, axRecX xS xFt xE,
        axRecX xE xFtth xSf1, limbRecX] := by decide +kernel


/-- Negative control: a naive split of the state-0 slot makes the slot's state list non-disjoint (`Nodup` fails). -/
theorem naive_state0_split_breaks_disjoint :
    let naive : SlotX ℚ := extSlot slot1X [⟨[0], .const 1, axRecX xS xFt xE, .s⟩] []
    ((naive.ents.flatMap EntX.states) ++ naive.pairStates).Nodup = False := by
  simp only [eq_iff_iff, iff_false]
  decide +kernel

theorem serviceRecs_shape :
    (axRecX xS xFt xE).length = 8 ∧ (axRecX xS xFt xE).getLast? = some (.k 5) ∧
      limbRecX.length = 4 := by decide +kernel

/-- A list's key polynomial has zero coefficients beyond its length. -/
theorem keyP_coeff_ge {F : Type} [Field F] (l : List F) (n : ℕ) (hn : l.length ≤ n) :
    (keyP l).coeff n = 0 := by
  rw [keyP_coeff]; exact List.getD_eq_default _ _ hn

/-- **Service-key disjointness of the twin (6 pairs, design R4)**: the four service record kinds —
`TAG_inc` (coefficient `4` at `γ⁴`), `TAG_jet` (`3` at `γ⁷`), every 4-entry record (`walkRecA`,
incl. the `s10S` limb consume) and `TAG_ax` (`5` at `γ⁷`) — are pairwise distinct polynomials in
`γ` for ALL row values.  Needs `2, 3, 5 ≠ 0`. -/
theorem serviceKeys_disjoint9 {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h5 : (5 : F) ≠ 0) (f g : ℕ → F) (r : List RE) (hr : r.length = 4) (a b c : Hd) :
    keyP (incRecX.map (RE.ev f)) ≠ keyP (r.map (RE.ev g)) ∧
    keyP (jetRecX.map (RE.ev f)) ≠ keyP (r.map (RE.ev g)) ∧
    keyP (incRecX.map (RE.ev f)) ≠ keyP (jetRecX.map (RE.ev g)) ∧
    keyP ((axRecX a b c).map (RE.ev f)) ≠ keyP (incRecX.map (RE.ev g)) ∧
    keyP ((axRecX a b c).map (RE.ev f)) ≠ keyP (jetRecX.map (RE.ev g)) ∧
    keyP ((axRecX a b c).map (RE.ev f)) ≠ keyP (r.map (RE.ev g)) := by
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hr4 : (r.map (RE.ev g)).length ≤ 4 := by simp [hr]
  have hr7 : (r.map (RE.ev g)).length ≤ 7 := by simp [hr]
  refine ⟨fun h => h4 ?_, fun h => h3 ?_, fun h => h3 ?_, fun h => h5 ?_, fun h => h2 ?_,
    fun h => h5 ?_⟩
  · have := congrArg (fun q => Polynomial.coeff q 4) h
    simp only [keyP_coeff_ge _ 4 hr4] at this
    simpa [keyP_coeff, incRecX, RE.ev] using this
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    simp only [keyP_coeff_ge _ 7 hr7] at this
    simpa [keyP_coeff, jetRecX, RE.ev] using this
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    simpa [keyP_coeff, jetRecX, incRecX, RE.ev] using this.symm
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    simpa [keyP_coeff, axRecX, incRecX, RE.ev] using this
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    simp [keyP_coeff, axRecX, jetRecX, RE.ev] at this
    linear_combination this
  · have := congrArg (fun q => Polynomial.coeff q 7) h
    simp only [keyP_coeff_ge _ 7 hr7] at this
    simpa [keyP_coeff, axRecX, RE.ev] using this

end ReadSet

/-! ## 7. Row level: the twin's base gates, and the projection to J-8 -/

section RowSem
variable {F : Type} [Field F]

/-- The twin's template base gates vanish at a row. -/
def BaseHoldsX9 (env : Env F) : Prop := ∀ g ∈ baseGatesHX9, evalQX g env = 0

theorem arith_of_base9 {env : Env F} (h : BaseHoldsX9 env) {g : CoeffExpr ℚ} (hg : g ∈ arithGatesX9) :
    evalQX g env = 0 :=
  h g (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hg))))

theorem eq_of_base9 {env : Env F} (h : BaseHoldsX9 env) {g : EqG ℚ} (hg : g ∈ eqGatesX9) :
    evalQX g.gate env = 0 :=
  h _ (List.mem_append.mpr (Or.inr (List.mem_map_of_mem hg)))

/-- The three new selectors are off. -/
def NewOff (env : Env F) : Prop :=
  env.trace sS0B = 0 ∧ env.trace sS10B = 0 ∧ env.trace sS10S = 0

theorem NewOff.zero {env : Env F} (hN : NewOff env) : ∀ i ∈ newStates, env.trace i = 0 := by
  intro i hi
  simp only [newStates, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  exacts [hN.1, hN.2.1, hN.2.2]

theorem evalQX_sumList {ι : Type} (l : List ι) (f : ι → CoeffExpr ℚ) (env : Env F) :
    evalQX (CoeffExpr.sumList l f) env = (l.map fun i => evalQX (f i) env).sum := by
  induction l with
  | nil => simp [CoeffExpr.sumList, evalQX]
  | cons a l ih =>
      simp only [CoeffExpr.sumList, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
      simp only [evalQX, ih]

theorem evalQX_selS_zero {env : Env F} (l : List ℕ) (hz : ∀ i ∈ l, env.trace i = 0) :
    evalQX (selS (F := ℚ) l) env = 0 := by
  rw [selS, evalQX_sumList]
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
  simp [cc, evalQX, hz i hi]

theorem act_zero_of_new {env : Env F} (hN : NewOff env) (x : EntX ℚ)
    (hx : ∀ i ∈ x.states, i ∈ newStates) : evalQX x.act env = 0 := by
  simp only [EntX.act, evalQX]
  rw [evalQX_selS_zero _ (fun i hi => hN.zero i (hx i hi)), zero_mul]

theorem hes_of {env : Env F} (hN : NewOff env) (es : List (EntX ℚ))
    (hok : (es.all fun x => x.states.all fun i => decide (i ∈ newStates)) = true) :
    ∀ x ∈ es, evalQX x.act env = 0 := by
  intro x hx
  refine act_zero_of_new hN x fun i hi => ?_
  have h1 := List.all_eq_true.mp hok x hx
  have h2 := List.all_eq_true.mp h1 i hi
  simpa using h2

/-- An extended slot's activity into any balance equals the J-8 slot's when the new entries are off. -/
theorem actB_extSlot {env : Env F} (S : SlotX ℚ) (es : List (EntX ℚ)) (ps : List ℕ)
    (hes : ∀ x ∈ es, evalQX x.act env = 0) (b : Bal) :
    evalQX ((extSlot S es ps).actB b) env = evalQX (S.actB b) env := by
  simp only [SlotX.actB, extSlot, evalQX, List.filter_append]
  rw [evalQX_sumList, evalQX_sumList, List.map_append, List.sum_append]
  have : ((es.filter fun x => decide (x.bal = b)).map fun x => evalQX x.act env).sum = 0 :=
    List.sum_eq_zero fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact hes x (List.mem_filter.mp hx).1
  rw [this, add_zero]

theorem slot0X9_actB {env : Env F} (hN : NewOff env) (b : Bal) :
    evalQX ((slot0X9 (F := ℚ)).actB b) env = evalQX ((slot0X (F := ℚ)).actB b) env :=
  actB_extSlot slot0X ents0New [] (hes_of hN _ (by decide +kernel)) b
theorem slot1X9_actB {env : Env F} (hN : NewOff env) (b : Bal) :
    evalQX ((slot1X9 (F := ℚ)).actB b) env = evalQX ((slot1X (F := ℚ)).actB b) env :=
  actB_extSlot slot1X ents1New [] (hes_of hN _ (by decide +kernel)) b
theorem slot2X9_actB {env : Env F} (hN : NewOff env) (b : Bal) :
    evalQX ((slot2X9 (F := ℚ)).actB b) env = evalQX ((slot2X (F := ℚ)).actB b) env :=
  actB_extSlot slot2X ents2New [sS10S] (hes_of hN _ (by decide +kernel)) b
theorem slot3X9_actB {env : Env F} (hN : NewOff env) (b : Bal) :
    evalQX ((slot3X9 (F := ℚ)).actB b) env = evalQX ((slot3X (F := ℚ)).actB b) env :=
  actB_extSlot slot3X ents3New [] (hes_of hN _ (by decide +kernel)) b

/-- The per-row LogUp term of the twin equals J-8's on a row with the new selectors off. -/
theorem termCoord_twin {env : Env F} (hN : NewOff env) (b : Bal) (im : Bool) (k : ℕ) :
    evalQX (termCoord ((slotsX9 (F := ℚ)).map fun S =>
        (⟨S.actB b, if im then S.invIm else S.inv⟩ : Slot ℚ)) k) env =
      evalQX (termCoord ((slotsX (F := ℚ)).map fun S =>
        (⟨S.actB b, if im then S.invIm else S.inv⟩ : Slot ℚ)) k) env := by
  simp only [termCoord, slotsX9, slotsX, List.map_cons, List.map_nil]
  rw [evalQX_sumList, evalQX_sumList]
  simp only [List.map_cons, List.map_nil, evalQX, slot0X9_actB hN, slot1X9_actB hN, slot2X9_actB hN,
    slot3X9_actB hN]
  rfl

theorem accGatesX_twin {env : Env F} {s1 s2 : List (Slot ℚ)}
    (hT : ∀ k, evalQX (termCoord s2 k) env = evalQX (termCoord s1 k) env) {a p : ℕ}
    {g : CoeffExpr ℚ} (hg : g ∈ accGatesX s1 a p) :
    ∃ g' ∈ accGatesX s2 a p, evalQX g' env = evalQX g env := by
  simp only [accGatesX, List.mem_append, List.mem_map, List.mem_range] at hg
  rcases hg with (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩
  · exact ⟨accInitX a k, List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inl (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))), rfl⟩
  · exact ⟨accStepX s2 a k, List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inr (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))), by simp only [accStepX, evalQX, hT k]⟩
  · exact ⟨accTermX s2 a p k, List.mem_append.mpr (Or.inr
      (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)), by simp only [accTermX, evalQX, hT k]⟩

theorem accHX_twin {env : Env F} (hN : NewOff env) {g : CoeffExpr ℚ} (hg : g ∈ accGatesHX (F := ℚ)) :
    ∃ g' ∈ accGatesHX9 (F := ℚ), evalQX g' env = evalQX g env := by
  have T := fun b im => fun k => termCoord_twin (env := env) hN b im k
  simp only [accGatesHX, List.mem_append] at hg
  simp only [accGatesHX9, List.mem_append]
  rcases hg with ((((h | h) | h) | h) | h) | h
  · obtain ⟨g', h', e⟩ := accGatesX_twin (T .x false) h
    exact ⟨g', Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h')))), e⟩
  · obtain ⟨g', h', e⟩ := accGatesX_twin (T .x true) h
    exact ⟨g', Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h')))), e⟩
  · obtain ⟨g', h', e⟩ := accGatesX_twin (T .p false) h
    exact ⟨g', Or.inl (Or.inl (Or.inl (Or.inr h'))), e⟩
  · obtain ⟨g', h', e⟩ := accGatesX_twin (T .p true) h
    exact ⟨g', Or.inl (Or.inl (Or.inr h')), e⟩
  · obtain ⟨g', h', e⟩ := accGatesX_twin (T .s false) h
    exact ⟨g', Or.inl (Or.inr h'), e⟩
  · obtain ⟨g', h', e⟩ := accGatesX_twin (T .s true) h
    exact ⟨g', Or.inr h', e⟩

theorem kept_mem {g : CoeffExpr ℚ} (hg : g ∈ arithGatesX (F := ℚ)) (hc : g ∉ changedJ8) :
    g ∈ arithGatesX9 := by
  have : g ∈ arithKeptX9 := List.mem_filter.mpr ⟨hg, decide_eq_true hc⟩
  simp only [arithGatesX9, arithSF9, List.mem_append]
  tauto

/-- **The twin projects to J-8**: on a row whose three new selectors are `0`, the
twin's base gates imply every J-8 base gate (kept gates verbatim; the four changed gates and the
accumulators because every new term is a multiple of a new selector).  So every J-8 row lemma
(`s10_row`, `s10L_row`, `kid_cell`, `op4_fast_row`, …) applies verbatim on old-state rows. -/
theorem baseHoldsX_of_X9 {env : Env F} (hB : BaseHoldsX9 env) (hN : NewOff env) : BaseHoldsX env := by
  intro g hg
  simp only [baseGatesHX, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · by_cases hc : g ∈ changedJ8
    · simp only [changedJ8, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · have h := arith_of_base9 hB (g := oneHotSumX9) (by decide +kernel)
        simp only [oneHotSumX9, evalQX] at h ⊢
        rw [evalQX_selS_zero newStates hN.zero, add_zero] at h
        exact h
      · have h := arith_of_base9 hB (g := kindRelaxX9) (by decide +kernel)
        simp only [kindRelaxX9, oneMinus, cc, evalQX, hN.2.2, Rat.cast_one, sub_zero, one_mul] at h
        simp only [evalQX]
        exact h
      · have h := arith_of_base9 hB (g := svXFX9) (by decide +kernel)
        simp only [svXFX9, oneMinus, prodL, List.foldr, cc, evalQX, hN.2.2, Rat.cast_one, sub_zero,
          one_mul, zero_mul, add_zero] at h
        exact h
      · have h := arith_of_base9 hB (g := prGateX9) (by decide +kernel)
        simp only [prGateX9, cc, evalQX, hN.2.2, zero_mul, sub_zero] at h
        exact h
    · exact hB g (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (kept_mem hg hc)))))
  · obtain ⟨g', hg', he⟩ := accHX_twin hN hg
    rw [← he]
    exact hB g' (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hg'))))
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
    exact eq_of_base9 hB (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ he)))

/-! ### Kinds -/

theorem kindKept9 :
    (allHandlesX.all fun h => decide (h = xF) ||
      ([boolG (kbE h), boolG (kcE h), .mul (kcE h) (kbE h)] : List (CoeffExpr ℚ)).all
        fun g => decide (g ∈ arithGatesX9)) = true := by decide +kernel

theorem kindBoolF9 :
    ([boolG (kbE xF), boolG (kcE xF), kindRelaxX9] : List (CoeffExpr ℚ)).all
      (fun g => decide (g ∈ arithGatesX9)) = true := by decide +kernel

/-- **The `kb` split on every handle but the formula** (as J-8's `kind_split`). -/
theorem kind_split9 {env : Env F} (hB : BaseHoldsX9 env) (h : Hd) (hh : h ∈ allHandlesX) (hne : h ≠ xF) :
    (kcV env h = 0 ∧ kbV env h = 0) ∨ (kcV env h = 1 ∧ kbV env h = 0) ∨
      (kcV env h = 0 ∧ kbV env h = 1) := by
  have hm := List.all_eq_true.mp kindKept9 h hh
  simp only [hne, decide_false, Bool.false_or, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, decide_eq_true_eq] at hm
  have h1 := arith_of_base9 hB hm.1
  have h2 := arith_of_base9 hB hm.2.1
  have h3 := arith_of_base9 hB hm.2.2
  simp only [boolG, kbE, kcE, cc, evalQX, Rat.cast_one, Rat.cast_ofNat] at h1 h2 h3
  simp only [kcV, kbV]
  rcases mul_eq_zero.mp h1 with hb | hb <;> rcases mul_eq_zero.mp h2 with hc | hc
  · left; exact ⟨hc, hb⟩
  · right; left; exact ⟨by linear_combination hc, hb⟩
  · right; right; exact ⟨hc, by linear_combination hb⟩
  · exfalso
    have : env.trace (kbX h) = 1 := by linear_combination hb
    have hc' : env.trace h.k - 2 * env.trace (kbX h) = 1 := by linear_combination hc
    rw [hc', this] at h3; simp at h3

/-- **The formula handle**: `kc`, `kb` boolean, and **kind 3 (`kc = kb = 1`) only on `s10S`** (the
relaxation is state-gated, design cond. 7; §5 "a kind-3 formula on a non-`s10S` row"). -/
theorem kindF9 {env : Env F} (hB : BaseHoldsX9 env) :
    kbV env xF * (kbV env xF - 1) = 0 ∧ kcV env xF * (kcV env xF - 1) = 0 ∧
      (kcV env xF = 1 → kbV env xF = 1 → tr env sS10S = 1) := by
  have hm := kindBoolF9
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hm
  have h1 := arith_of_base9 (env := env) hB hm.1
  have h2 := arith_of_base9 (env := env) hB hm.2.1
  have h3 := arith_of_base9 (env := env) hB hm.2.2
  simp only [boolG, kindRelaxX9, oneMinus, kbE, kcE, cc, evalQX, Rat.cast_one, Rat.cast_ofNat] at h1 h2 h3
  simp only [kcV, kbV, tr]
  refine ⟨by linear_combination h1, by linear_combination h2, fun hc hb => ?_⟩
  rw [hc, hb] at h3
  linear_combination -h3

/-- **NC (cond. 7): the UNRELAXED J-8 kind gate rejects every kind-3 formula row.** -/
theorem kind3_rejected_by_J8 {env : Env F} (hc : kcV env xF = 1) (hb : kbV env xF = 1) :
    ¬ BaseHoldsX env := by
  intro hB
  have g := arith_of_base hB (g := .mul (kcE xF) (kbE xF)) (by decide +kernel)
  simp only [kcE, kbE, cc, evalQX, Rat.cast_ofNat] at g
  simp only [kcV, kbV] at hc hb
  rw [hc, hb] at g
  simp at g

/-! ### One-hot -/

/-- The row's one-hot over the twin's 20 states is at `j`. -/
def OneHotAt9 (env : Env F) (j : ℕ) : Prop := ∀ i ∈ statesX9, env.trace i = if i = j then 1 else 0

theorem OneHotAt9.zero {env : Env F} {j : ℕ} (hOH : OneHotAt9 env j) {i : ℕ} (hi : i ∈ statesX9)
    (hne : i ≠ j) : env.trace i = 0 := by
  rw [hOH i hi]; simp [hne]

theorem OneHotAt9.one {env : Env F} {j : ℕ} (hOH : OneHotAt9 env j) (hj : j ∈ statesX9) :
    env.trace j = 1 := by
  rw [hOH j hj]; simp

/-- On an old-state row, the new selectors are off. -/
theorem OneHotAt9.newOff {env : Env F} {j : ℕ} (hOH : OneHotAt9 env j) (hj : j < nStates) :
    NewOff env := by
  refine ⟨hOH.zero (by decide +kernel) ?_, hOH.zero (by decide +kernel) ?_,
    hOH.zero (by decide +kernel) ?_⟩ <;>
  · simp only [sS0B, sS10B, sS10S, nStates] at hj ⊢; omega

/-! ### The new rows -/

/-- **op 0, `s0B`** (big / field axis read): head `0`; `f` a cell; `f_h` the small atom `0`; the axis
`f_t` an atom (small or big); no `z1`; the subject a cell.  Its read is the `TAG_ax` consume
`(s.v, f_t, e, id, 0, 5)` (`consumesX9_s0B`). -/
theorem s0B_row {env : Env F} (hB : BaseHoldsX9 env) (hOH : OneHotAt9 env sS0B) :
    tr env xFh.v = 0 ∧ tr env xF.k = 1 ∧ kcV env xFt = 0 ∧ tr env z1X = 0 ∧ kcV env xS = 1 ∧
      kcV env xFh = 0 ∧ kbV env xFh = 0 := by
  have h1 : env.trace sS0B = 1 := hOH.one (by decide +kernel)
  have h12 : env.trace sS10L = 0 := hOH.zero (by decide +kernel) (by decide)
  have h13 : env.trace sS10T = 0 := hOH.zero (by decide +kernel) (by decide)
  have hS : env.trace sS10S = 0 := hOH.zero (by decide +kernel) (by decide)
  have hc : env.trace consCol = 0 := hOH.zero (by decide +kernel) (by decide)
  have a1 := arith_of_base9 hB (g := .mul (cc sS0B) (kcE xFt)) (by decide +kernel)
  have a2 := arith_of_base9 hB (g := .mul (cc sS0B) (cc z1X)) (by decide +kernel)
  have a3 := arith_of_base9 hB (g := .mul (cc sS0B) (oneMinus (kcE xS))) (by decide +kernel)
  have aF := arith_of_base9 hB (g := svXFX9) (by decide +kernel)
  have aH := arith_of_base9 hB (g := .sub (cc consCol) (kcE xFh)) (by decide +kernel)
  have aB := arith_of_base9 hB (g := kbE xFh) (by decide +kernel)
  have e0 := eq_of_base9 hB (g := ⟨cc sS0B, xFh.v, .cst 0⟩) (by decide +kernel)
  simp only [svXFX9, svXF8, prodL, List.foldr, cc, kcE, kbE, oneMinus, EqG.gate, Opnd.expr, evalQX,
    Rat.cast_one, Rat.cast_ofNat, Rat.cast_zero, h1, h12, h13, hS, hc, one_mul, mul_one, zero_mul,
    sub_zero, add_zero] at a1 a2 a3 aF aH aB e0
  simp only [kcV, kbV, tr]
  refine ⟨e0, by linear_combination aF, a1, a2, by linear_combination -a3, by linear_combination -aH, aB⟩

/-- **op 10, `s10B`** (big axis): head `10`; `f`, `f_t`, `f_th` cells; the axis `f_tth` an atom;
no `z1`; `e` a cell; the two real children's formulas `f_ttt`, `f_tt` are cells (F4); the chain-root
label is `(3 − kb(f_tth), ·)` with value `f_tth.v` on a big axis (kind 2) and `64·id + 1` on a field
axis (kind 3: the design's `(3, 64·xId + 1)`, segment index `m = 1`, the top limb of a 2-limb value).  Its read is the `TAG_ax` consume
`(e.v, f_tth, sf1, id, 0, 5)` (`consumesX9_s10B`). -/
theorem s10B_row {env : Env F} (hB : BaseHoldsX9 env) (hOH : OneHotAt9 env sS10B) :
    tr env xFh.v = 10 ∧ tr env xF.k = 1 ∧ kcV env xFt = 1 ∧ kcV env xFth = 1 ∧ kcV env xFtth = 0 ∧
      tr env z1X = 0 ∧ kcV env xE = 1 ∧ tr env xFttt.k = 1 ∧ tr env xFtt.k = 1 ∧
      tr env kLabX = 3 - kbV env xFtth ∧
      (kbV env xFtth = 1 → tr env vLabX = tr env xFtth.v) ∧
      (kbV env xFtth = 0 → tr env vLabX = 64 * tr env xIdX + 1) := by
  have h1 : env.trace sS10B = 1 := hOH.one (by decide +kernel)
  have h12 : env.trace sS10L = 0 := hOH.zero (by decide +kernel) (by decide)
  have h13 : env.trace sS10T = 0 := hOH.zero (by decide +kernel) (by decide)
  have hS : env.trace sS10S = 0 := hOH.zero (by decide +kernel) (by decide)
  have a1 := arith_of_base9 hB (g := .mul (cc sS10B) (kcE xFtth)) (by decide +kernel)
  have a2 := arith_of_base9 hB (g := .mul (cc sS10B) (cc z1X)) (by decide +kernel)
  have a3 := arith_of_base9 hB (g := .mul (cc sS10B) (oneMinus (kcE xE))) (by decide +kernel)
  have a4 := arith_of_base9 hB (g := .mul (cc sS10B) (oneMinus (kcE xFt))) (by decide +kernel)
  have a5 := arith_of_base9 hB (g := .mul (cc sS10B) (oneMinus (kcE xFth))) (by decide +kernel)
  have a6 := arith_of_base9 hB
    (g := .mul (cc sS10B) (.add (.sub (cc kLabX) (.const 3)) (kbE xFtth))) (by decide +kernel)
  have a7 := arith_of_base9 hB (g := prodL [cc sS10B, oneMinus (kbE xFtth),
     .sub (.sub (cc vLabX) (.mul (.const 64) (cc xIdX))) (.const 1)]) (by decide +kernel)
  have k1 := arith_of_base9 hB (g := .mul (cc sS10B) (oneMinus (kcE xFttt))) (by decide +kernel)
  have k2 := arith_of_base9 hB (g := .mul (cc sS10B) (oneMinus (kcE xFtt))) (by decide +kernel)
  have aF := arith_of_base9 hB (g := svXFX9) (by decide +kernel)
  have e0 := eq_of_base9 hB (g := ⟨cc sS10B, xFh.v, .cst 10⟩) (by decide +kernel)
  have e1 := eq_of_base9 hB (g := ⟨.mul (cc sS10B) (kbE xFtth), vLabX, .col xFtth.v⟩) (by decide +kernel)
  have s1 := kind_split9 hB xFttt (by decide) (by decide)
  have s2 := kind_split9 hB xFtt (by decide) (by decide)
  simp only [svXFX9, svXF8, prodL, List.foldr, cc, kcE, kbE, oneMinus, EqG.gate, Opnd.expr, evalQX,
    Rat.cast_one, Rat.cast_ofNat, h1, h12, h13, hS, one_mul, mul_one, zero_mul, sub_zero,
    add_zero] at a1 a2 a3 a4 a5 a6 a7 k1 k2 aF e0 e1
  simp only [kcV, kbV, tr] at s1 s2 ⊢
  have hk1 : env.trace xFttt.k - 2 * env.trace (kbX xFttt) = 1 := by linear_combination -k1
  have hk2 : env.trace xFtt.k - 2 * env.trace (kbX xFtt) = 1 := by linear_combination -k2
  have hb1 : env.trace (kbX xFttt) = 0 := by
    rcases s1 with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · rw [hk1] at h; exact absurd h one_ne_zero
    · exact h
    · rw [hk1] at h; exact absurd h one_ne_zero
  have hb2 : env.trace (kbX xFtt) = 0 := by
    rcases s2 with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · rw [hk2] at h; exact absurd h one_ne_zero
    · exact h
    · rw [hk2] at h; exact absurd h one_ne_zero
  refine ⟨by linear_combination e0, by linear_combination aF, by linear_combination -a4, by linear_combination -a5, a1, a2,
    by linear_combination -a3, by linear_combination hk1 + 2 * hb1, by linear_combination hk2 + 2 * hb2,
    by linear_combination a6, fun hb => ?_, fun hb => ?_⟩
  · rw [hb, one_mul] at e1; linear_combination e1
  · rw [hb, sub_zero, one_mul] at a7; linear_combination a7

/-- `m = Σ 2^i m_i` at a row. -/
def mValV (env : Env F) : F :=
  tr env m0X + (2 * tr env m1X + (4 * tr env m2X + (8 * tr env m3X + (16 * tr env m4X +
    32 * tr env m5X))))

/-- **`s10S`'s bits** are boolean (`m₀..m₃` by J-8's global booleans on `β, fast, l₁.k, l₂.k`;
`m₄, m₅, hd` by the twin's). -/
theorem s10S_bits {env : Env F} (hB : BaseHoldsX9 env) :
    ∀ i ∈ [m0X, m1X, m2X, m3X, m4X, m5X, hdC], tr env i * (tr env i - 1) = 0 := by
  have hm : ([m0X, m1X, m2X, m3X, m4X, m5X, hdC].all fun i =>
      decide ((boolG (cc i) : CoeffExpr ℚ) ∈ arithGatesX9)) = true := by decide +kernel
  intro i hi
  have g := arith_of_base9 hB (decide_eq_true_eq.mp (List.all_eq_true.mp hm i hi))
  simpa only [boolG, cc, evalQX, Rat.cast_one, tr] using g

/-- **op 10, `s10S`** (the segment pseudo-row, label `(3, 64·id + m)` or a kind-2 head; design
§2.4).  Every conjunct is a gate of the twin read at the row: (1) the formula is kind 2 or 3;
(2) kind 3 decodes `f.v = 64·id + m` (the ONE allowlisted gate); (3) kind 2 is `f.v = id` and a
head; (4)–(6) `pw = 2·pw1·pw2 = 2^{m+1}` (as products; `s10S_seg_nat`); (7) `m ≠ 63`; (8)–(9) `zA`,
`zB`; (10) the limb axis; (11) the segment `m.v = l + (1 − hd)·2^32`; (12) at `z1`: segment `1`,
a head; **(13) F3: `m.k = 0`** (the added gate `s10S·m.k`); (14) the walk pair is on iff not `z1`;
(15) `sf1 = s`, `sf2 = e`; (16) at `z1`: `f_tth = s`, `f_ttt = e`; (17)–(18) the next-segment label. -/
theorem s10S_row {env : Env F} (hB : BaseHoldsX9 env) (hOH : OneHotAt9 env sS10S) :
    kbV env xF = 1 ∧
    (kcV env xF = 1 → tr env xF.v = 64 * tr env xIdX + mValV env) ∧
    (kcV env xF = 0 → tr env xF.v = tr env xIdX ∧ tr env hdC = 1) ∧
    tr env pw1X = (1 + tr env m0X) * ((1 + 3 * tr env m1X) * (1 + 15 * tr env m2X)) ∧
    tr env pw2X = (1 + 255 * tr env m3X) * ((1 + 65535 * tr env m4X) *
      (1 + 4294967295 * tr env m5X)) ∧
    tr env pwX = 2 * (tr env pw1X * tr env pw2X) ∧
    tr env m0X * (tr env m1X * tr env m2X) * (tr env m3X * (tr env m4X * tr env m5X)) = 0 ∧
    tr env zAX = (1 - tr env m0X) * ((1 - tr env m1X) * (1 - tr env m2X)) ∧
    tr env zBX = (1 - tr env m3X) * ((1 - tr env m4X) * (1 - tr env m5X)) ∧
    tr env axLX = tr env hdC * (tr env pwX - 1) + (1 - tr env hdC) * (2 * tr env pwX - 2) ∧
    tr env xM.v = tr env limbX + (1 - tr env hdC) * 4294967296 ∧
    (tr env z1X = 1 → tr env xM.v = 1 ∧ tr env hdC = 1) ∧
    tr env xM.k = 0 ∧
    tr env prX = 1 - tr env z1X ∧
    (tr env xSf1.k = tr env xS.k ∧ tr env xSf1.v = tr env xS.v ∧
      tr env xSf2.k = tr env xE.k ∧ tr env xSf2.v = tr env xE.v) ∧
    (tr env z1X = 1 → tr env xFtth.k = tr env xS.k ∧ tr env xFtth.v = tr env xS.v ∧
      tr env xFttt.k = tr env xE.k ∧ tr env xFttt.v = tr env xE.v) ∧
    tr env kLabX = 3 * (1 - tr env zAX * tr env zBX) ∧
    tr env vLabX = tr env zAX * tr env zBX +
      (1 - tr env zAX * tr env zBX) * (64 * tr env xIdX + mValV env - 1) := by
  have hS : env.trace sS10S = 1 := hOH.one (by decide +kernel)
  have h5 : env.trace 5 = 0 := hOH.zero (by decide +kernel) (by decide)
  have h12 : env.trace sS10L = 0 := hOH.zero (by decide +kernel) (by decide)
  have hG : ∀ g ∈ (s10SG : List (CoeffExpr ℚ)), evalQX g env = 0 := fun g hg =>
    arith_of_base9 hB (by
      have hm : ((s10SG : List (CoeffExpr ℚ)).all fun g => decide (g ∈ arithGatesX9)) = true := by
        decide +kernel
      exact decide_eq_true_eq.mp (List.all_eq_true.mp hm g hg))
  have hE : ∀ g ∈ (s10SEq : List (EqG ℚ)), evalQX g.gate env = 0 := fun g hg =>
    eq_of_base9 hB (by
      have hm : ((s10SEq : List (EqG ℚ)).all fun g => decide (g ∈ eqGatesX9)) = true := by
        decide +kernel
      exact decide_eq_true_eq.mp (List.all_eq_true.mp hm g hg))
  simp only [s10SG, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hG
  simp only [s10SEq, heq, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hE
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17⟩ := hG
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hE
  have gd := arith_of_base9 hB (g := decodeG9) (by decide +kernel)
  have gp := arith_of_base9 hB (g := prGateX9) (by decide +kernel)
  simp only [decodeG9, mValE, prGateX9, prGateX, prodL, List.foldr, cc, notC, kcE, kbE, oneMinus,
    EqG.gate, Opnd.expr, evalQX, Rat.cast_one, Rat.cast_ofNat, hS, h5, h12, one_mul, mul_one,
    zero_mul, sub_zero] at g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 gd gp
  simp only [kcV, kbV, mValV, tr]
  refine ⟨by linear_combination -g1, fun hc => ?_, fun hc => ?_, by linear_combination g3,
    by linear_combination g4, by linear_combination g5, ?_, by linear_combination g9,
    by linear_combination g10, by linear_combination g11, by linear_combination e2 + g12,
    fun hz => ?_, g15, by linear_combination gp,
    ⟨by linear_combination e3, by linear_combination e4, by linear_combination e5,
      by linear_combination e6⟩, fun hz => ?_, by linear_combination g16, by linear_combination g17⟩
  · rw [hc, one_mul] at gd; linear_combination gd
  · rw [hc, sub_zero, one_mul] at e1 g2
    exact ⟨by linear_combination e1, by linear_combination -g2⟩
  · have h6 : env.trace aAX = env.trace m0X * (env.trace m1X * env.trace m2X) := by
      linear_combination g6
    have h7 : env.trace aBX = env.trace m3X * (env.trace m4X * env.trace m5X) := by
      linear_combination g7
    rw [← h6, ← h7]; exact g8
  · rw [hz, one_mul] at g13 g14
    exact ⟨by linear_combination e2 + g13, by linear_combination -g14⟩
  · rw [hz, one_mul] at e7 e8 e9 e10
    exact ⟨by linear_combination e7, by linear_combination e8, by linear_combination e9,
      by linear_combination e10⟩

/-- A boolean field element is the cast of `0` or `1`. -/
theorem bool_nat {x : F} (h : x * (x - 1) = 0) : ∃ b : ℕ, b ≤ 1 ∧ x = b := by
  rcases mul_eq_zero.mp h with h | h
  · exact ⟨0, by omega, by simp [h]⟩
  · exact ⟨1, le_refl _, by simp only [Nat.cast_one]; linear_combination h⟩

theorem pow_bit (c : ℕ) {b : ℕ} (hb : b ≤ 1) : (1 : F) + ((2 ^ c - 1 : ℕ) : F) * b = 2 ^ (c * b) := by
  interval_cases b
  · simp
  · have : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    simp only [Nat.cast_one, mul_one, Nat.cast_sub this, Nat.cast_pow, Nat.cast_ofNat]
    ring

/-- **The `s10S` power of two, over `ℕ`**: the six bits are a natural `m ≤ 62` (so `m ≠ 63`, design
cond. 6 / F5), `pw = 2^{m+1}`, and `zA·zB = [m = 0]` (the next child is the terminal `(0, 1)` exactly
at `m = 0`). -/
theorem s10S_seg_nat {env : Env F} (hB : BaseHoldsX9 env) (hOH : OneHotAt9 env sS10S) :
    ∃ m : ℕ, m < 63 ∧ mValV env = (m : F) ∧ tr env pwX = 2 ^ (m + 1) ∧
      tr env zAX * tr env zBX = (if m = 0 then 1 else 0) := by
  obtain ⟨-, -, -, hp1, hp2, hp, hprod, hzA, hzB, -⟩ := s10S_row hB hOH
  have hb := s10S_bits hB
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  obtain ⟨q0, q1, q2, q3, q4, q5, -⟩ := hb
  obtain ⟨b0, hb0, e0⟩ := bool_nat q0
  obtain ⟨b1, hb1, e1⟩ := bool_nat q1
  obtain ⟨b2, hb2, e2⟩ := bool_nat q2
  obtain ⟨b3, hb3, e3⟩ := bool_nat q3
  obtain ⟨b4, hb4, e4⟩ := bool_nat q4
  obtain ⟨b5, hb5, e5⟩ := bool_nat q5
  simp only [e0, e1, e2, e3, e4, e5] at hp1 hp2 hprod hzA hzB
  refine ⟨b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4 + 32 * b5, ?_, ?_, ?_, ?_⟩
  · by_contra hlt
    have c0 : b0 = 1 := by omega
    have c1 : b1 = 1 := by omega
    have c2 : b2 = 1 := by omega
    have c3 : b3 = 1 := by omega
    have c4 : b4 = 1 := by omega
    have c5 : b5 = 1 := by omega
    subst c0 c1 c2 c3 c4 c5
    norm_num at hprod
  · simp only [mValV, tr, e0, e1, e2, e3, e4, e5]; push_cast; ring
  · have f0 := pow_bit (F := F) 1 hb0
    have f1 := pow_bit (F := F) 2 hb1
    have f2 := pow_bit (F := F) 4 hb2
    have f3 := pow_bit (F := F) 8 hb3
    have f4 := pow_bit (F := F) 16 hb4
    have f5 := pow_bit (F := F) 32 hb5
    norm_num at f0 f1 f2 f3 f4 f5
    rw [hp, hp1, hp2, f0, f1, f2, f3, f4, f5]
    ring
  · rw [hzA, hzB]
    split_ifs with h0
    · have c0 : b0 = 0 := by omega
      have c1 : b1 = 0 := by omega
      have c2 : b2 = 0 := by omega
      have c3 : b3 = 0 := by omega
      have c4 : b4 = 0 := by omega
      have c5 : b5 = 0 := by omega
      subst c0 c1 c2 c3 c4 c5
      norm_num
    · have : b0 = 1 ∨ b1 = 1 ∨ b2 = 1 ∨ b3 = 1 ∨ b4 = 1 ∨ b5 = 1 := by omega
      rcases this with h | h | h | h | h | h <;> subst h <;> simp

/-! ### The cond. 7 negative control, with a concrete row -/

/-- A concrete `s10S` row with a KIND-3 formula `(3, 64·7 + 0)` (segment `m = 0`, head, limb `5`),
subject / target cells `(1, 11)`, `(1, 13)`, the walk pair on. -/
def witListS10S : List (ℕ × ℚ) :=
  [(125, 1), (25, 1), (26, 11), (27, 3), (28, 448), (50, 1), (29, 1), (30, 13), (31, 1), (32, 11),
   (33, 1), (34, 13), (48, 5), (24, 1), (20, 1), (22, 1), (23, 2), (62, 1), (63, 1), (126, 7),
   (128, 1), (131, 1), (134, 5), (135, 1), (136, 5)]

def witS10S : Env ℚ :=
  ⟨fun i => (witListS10S.lookup i).getD 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

theorem witS10S_holds : BaseHoldsX9 witS10S := by
  unfold BaseHoldsX9; decide +kernel

/-- **NC `kidKinds_unrelaxed_rejects_s10S`**:
a concrete `s10S` row with a kind-3 formula satisfies EVERY base gate of the twin (non-vacuity), and
the J-8 base gates (the unrelaxed `kc(f)·kb(f)`) reject it. -/
theorem kidKinds_unrelaxed_rejects_s10S :
    BaseHoldsX9 witS10S ∧ OneHotAt9 witS10S sS10S ∧ kcV witS10S xF = 1 ∧ kbV witS10S xF = 1 ∧
      ¬ BaseHoldsX witS10S := by
  have hc : kcV witS10S xF = 1 := by decide +kernel
  have hb : kbV witS10S xF = 1 := by decide +kernel
  have hOH : OneHotAt9 witS10S sS10S := by unfold OneHotAt9; decide +kernel
  exact ⟨witS10S_holds, hOH, hc, hb, kind3_rejected_by_J8 hc hb⟩

end RowSem

-- AXIOMS-BEGIN
#print axioms layoutX9_tiles
#print axioms changedJ8_receipt
#print axioms slotsX9_length
#print axioms fanoutX9_new
#print axioms baseTemplateX9_degree
#print axioms act_deg_const1
#print axioms slotsX9_act_deg
#print axioms slotPairsX9_degree
#print axioms arithGatesX9_allowlist
#print axioms arithSF9_serialFree
#print axioms allowlistX9_one
#print axioms accGatesHX9_serialFree
#print axioms eqGatesX9_ok
#print axioms slotPairsX9_keyOK
#print axioms serialFreeX_flags_naive_kind2
#print axioms serialFreeX_flags_naive_route
#print axioms serialFreeX_flags_naive_seg
#print axioms arithGatesX9_allowlist_xId
#print axioms allowlistX9xId_three
#print axioms accGatesHX9_serialFree9
#print axioms serialFreeX9_flags_naive
#print axioms slotsX9_disjoint
#print axioms consumesX9_old
#print axioms consumesX9_s0B
#print axioms consumesX9_s10B
#print axioms consumesX9_s10S
#print axioms service_consumers9
#print axioms naive_state0_split_breaks_disjoint
#print axioms serviceRecs_shape
#print axioms keyP_coeff_ge
#print axioms serviceKeys_disjoint9
#print axioms arith_of_base9
#print axioms eq_of_base9
#print axioms NewOff.zero
#print axioms evalQX_sumList
#print axioms evalQX_selS_zero
#print axioms act_zero_of_new
#print axioms hes_of
#print axioms actB_extSlot
#print axioms slot0X9_actB
#print axioms slot1X9_actB
#print axioms slot2X9_actB
#print axioms slot3X9_actB
#print axioms termCoord_twin
#print axioms accGatesX_twin
#print axioms accHX_twin
#print axioms kept_mem
#print axioms baseHoldsX_of_X9
#print axioms kindKept9
#print axioms kindBoolF9
#print axioms kind_split9
#print axioms kindF9
#print axioms kind3_rejected_by_J8
#print axioms OneHotAt9.zero
#print axioms OneHotAt9.one
#print axioms OneHotAt9.newOff
#print axioms s0B_row
#print axioms s10B_row
#print axioms s10S_bits
#print axioms s10S_row
#print axioms bool_nat
#print axioms pow_bit
#print axioms s10S_seg_nat
#print axioms witS10S_holds
#print axioms kidKinds_unrelaxed_rejects_s10S
-- AXIOMS-END

end

end ChipHX9
end VclL.Handle
end Nock.NockVMROM.Thm54
