/-
  Nock/V1J8/FillCell.lean

* `Co` / `coOf`: the five memory `𝕂′` coins of the frame (`z′`, `γ′`, `ρ′`, `γH′`, `ρH′`) as `K6`;
  * `Cell.colZ k mv mx mx1 mh j c`: the example's two cell-KW rows (`s0 = [0 0]`, `f0 = [0 1]`), every one of the 242
    columns, computable (`K6` arithmetic), at multiplicities `mv mx mx1 mh`; `Cell.pubs` the six terminal publics;
  * **`colZ_eq`**: column `c < 242` of row `i` equals the honest builder's column function (`HonestKW.colW` of
    `cellCol (cvals …)`, with `ivW` / `avW`, under `fullCol`) at `𝕂 = KC`, `b = powerBasis3`, `δ = deltaF`, coins
    `toQ` of `k`, given the handle coins of `chals` are `(γH′, ρH′)`;
  * **`cellTrace_eq`**: the Lagrange interpolants of the fill on any injective nodes ARE `InhabJ8MemCell.trM0`, column
    by column; **`cellTrace_eq_frame`**: the same at the frame coins (`coOf χe`, `chals = chalsMJ8 deltaF (toχ χe)`).
-/
import Nock.V1J8.CheckJ8
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemCellKW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.V1J8.FillMem

open Nock Nock.TraceGenExe Nock.Field Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.V1J8.Exe Nock.V1J8.Check

/-! ## 1. Coins and small lifts -/

/-- The five memory `𝕂′` coins. -/
structure Co where
  z : K6
  γ : K6
  ρ : K6
  γH : K6
  ρH : K6

/-- The frame's memory coins at `χe`: `z′ = (χ₂, χ₃)`, `γ′ = (χ₄, χ₆)`, `ρ′ = (χ₅, χ₇)`, `γH′ = (χ₁₁, χ₁₅)`,
`ρH′ = (χ₁₂, χ₁₆)`. -/
def coOf (χe : CoinsE) : Co := ⟨zE χe, γVE χe, ρVE χe, γHE χe, ρHE χe⟩

/-- A natural number as a base element of `𝕂′`. -/
def lq (x : ℕ) : K6 := g6 (natG x)

/-- An executable fingerprint atom `(z, 0, v)`. -/
def atomFPE (z v : K6) : FPE := ⟨z, 0, v⟩

/-! ## 2. The cell-KW fill of the example (rows `s0 = [0 0]`, `f0 = [0 1]`) -/

namespace Cell
variable (k : Co) (mv mx mx1 mh : ℕ → ℕ)

/-- The right child atom of row `j`. -/
def aR (j : ℕ) : ℕ := if j = 1 then 1 else 0
def pE (j : ℕ) : FPE := consE k.z (atomFPE k.z (lq 0)) (atomFPE k.z (lq (aR j)))
def lE : FPE := atomFPE k.z (lq 0)
def rE (j : ℕ) : FPE := atomFPE k.z (lq (aR j))

def vKey (j : ℕ) : Fin 5 → K6 :=
  ![(pE k j).size, (pE k j).dyck, (pE k j).leaf, ⟨g3 (natG 1), g3 (natG 0)⟩, lq j]
def xKey (j s : ℕ) : Fin 11 → K6 :=
  ![(pE k j).size, (pE k j).dyck, (pE k j).leaf, (lE k).size, (lE k).dyck, (lE k).leaf, (rE k j).size,
    (rE k j).dyck, (rE k j).leaf, lq j, lq s]

def vInv (j : ℕ) : K6 := (compressE k.γ k.ρ (vKey k j))⁻¹
def x0Inv (j : ℕ) : K6 := (compressE k.γ k.ρ (xKey k j 0))⁻¹
def x1Inv (j : ℕ) : K6 := (compressE k.γ k.ρ (xKey k j 1))⁻¹
def vTerm (j : ℕ) : K6 := lq (mv j) * vInv k j
def xTerm (j : ℕ) : K6 := lq (mx j) * x0Inv k j + lq (mx1 j) * x1Inv k j
def vAcc (j : ℕ) : K6 := if j = 0 then vTerm k mv 0 else vTerm k mv 0 + vTerm k mv 1
def xAcc (j : ℕ) : K6 := if j = 0 then xTerm k mx mx1 0 else xTerm k mx mx1 0 + xTerm k mx mx1 1

/-- The `𝕂′` slot `s` of row `j` (`CellVals.qslot`). -/
def qslot (j s : ℕ) : K6 :=
  match s with
  | 0 => (pE k j).size | 1 => (pE k j).dyck | 2 => (pE k j).leaf
  | 3 => (lE k).size | 4 => (lE k).dyck | 5 => (lE k).leaf
  | 6 => (rE k j).size | 7 => (rE k j).dyck | 8 => (rE k j).leaf
  | 9 => vInv k j | 10 => 0 | 11 => 0 | 12 => x0Inv k j | 13 => vAcc k mv j | 14 => xAcc k mx mx1 j
  | _ => x1Inv k j

def roleZ (j ρ c : ℕ) : ZMod p :=
  limbZ (if ρ % 2 = 0 then (qslot k mv mx mx1 j (ρ / 2)).re else (qslot k mv mx mx1 j (ρ / 2)).im) c

def baseZ (j c : ℕ) : ZMod p :=
  if c = 2 then (j : ZMod p) else if c = 8 then (aR j : ZMod p) else if c = 9 then 1
  else if c = 16 then (mv j : ZMod p) else if c = 17 then (mx j : ZMod p) else if c = 128 then (mx1 j : ZMod p)
  else if 18 ≤ c ∧ c < 128 then (if c = 18 then 1 else 0) else 0

def dKW (j : ℕ) : K6 := compressE k.γH k.ρH ![lq j, 0, 0, 0, lq (aR j)]
def ivH (j : ℕ) : K6 := (dKW k j)⁻¹
def avH (j : ℕ) : K6 :=
  if j = 0 then lq (mh 0) * ivH k 0 else lq (mh 0) * ivH k 0 + lq (mh 1) * ivH k 1

/-- **Column `c` of cell row `j`** (242 columns). -/
def colZ (j c : ℕ) : ZMod p :=
  if c = 0 then (if j = 0 then 1 else 0) else if c = 1 then (if j = 1 then 1 else 0)
  else if c < 129 then baseZ mv mx mx1 j c
  else if c = 129 then (mh j : ZMod p) else if c < 134 then 0
  else if c < 230 then roleZ k mv mx mx1 j ((c - 134) / 3) ((c - 134) % 3)
  else if c < 233 then limbZ (ivH k j).re (c - 230) else if c < 236 then limbZ (ivH k j).im (c - 233)
  else if c < 239 then limbZ (avH k mh j).re (c - 236) else if c < 242 then limbZ (avH k mh j).im (c - 239)
  else 0

/-- The six terminal publics (`ρ_V`, `ρ_X`, `ρ_H`). -/
def pubs (j : ℕ) : K3 :=
  if j = 0 then (vAcc k mv 1).re else if j = 1 then (vAcc k mv 1).im
  else if j = 2 then (xAcc k mx mx1 1).re else if j = 3 then (xAcc k mx mx1 1).im
  else if j = 4 then (avH k mh 1).re else if j = 5 then (avH k mh 1).im else 0

def cols : ℕ → Fin 2 → ZMod p := fun c i => colZ k mv mx mx1 mh i c

end Cell

/-! ## 3. Bridges: the `K6` objects are the `𝕂′` objects -/

section Bridge
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemCell
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)

theorem toQ_lq (n : ℕ) : K6.toQ (lq n) = liftQ (K := KC) deltaF ((n : ℕ) : ZMod p) := by
  rw [lq, toQ_g6, toZ_natG]; exact IsScalarTower.algebraMap_apply (ZMod p) KC KQ _

theorem toQ_consE (z : K6) (a b : FPE) :
    (consE z a b).toQ = ComputeTable.FP.cons (K6.toQ z) a.toQ b.toQ := by
  simp only [consE, FPE.toQ, ComputeTable.FP.cons, K6.toQ_add, K6.toQ_mul, K6.toQ_inv]

theorem toQ_atomFPE (z v : K6) : (atomFPE z v).toQ = ComputeTable.FP.atomFP (K6.toQ z) (K6.toQ v) := by
  simp only [atomFPE, FPE.toQ, ComputeTable.FP.atomFP, K6.toQ_zero]

theorem coordN_toQ_re (x : K6) (m : ℕ) :
    coordN powerBasis3 (Quad.re _ (K6.toQ x)) m = limbZ x.re (m % 3) := by
  rw [coordN, re_toQ, coord_K]
theorem coordN_toQ_im (x : K6) (m : ℕ) :
    coordN powerBasis3 (Quad.im _ (K6.toQ x)) m = limbZ x.im (m % 3) := by
  rw [coordN, im_toQ, coord_K]

variable (k : Co) (mv mx mx1 mh : ℕ → ℕ)

theorem liftQ_aR (j : ℕ) : liftQ (K := KC) deltaF (((Cell.aR j : ℕ)) : ZMod p) = liftQ deltaF (aRv j) := by
  unfold Cell.aR aRv; split_ifs <;> simp <;> rfl

/-- The committed content of the example's cell row `j` at `K6`-coins `k`. -/
noncomputable abbrev crowQ (j : ℕ) : CellVals (ZMod p) KQ := crow deltaF (K6.toQ k.z) mv mx mx1 j

theorem pE_eq (j : ℕ) : (Cell.pE k j).toQ = (crowQ k mv mx mx1 j).p := by
  rw [Cell.pE, toQ_consE, toQ_atomFPE, toQ_atomFPE, toQ_lq, toQ_lq, liftQ_aR]
  simp [crow]; rfl
theorem lE_eq (j : ℕ) : (Cell.lE k).toQ = (crowQ k mv mx mx1 j).l := by
  rw [Cell.lE, toQ_atomFPE, toQ_lq]; simp [crow]; rfl
theorem rE_eq (j : ℕ) : (Cell.rE k j).toQ = (crowQ k mv mx mx1 j).r := by
  rw [Cell.rE, toQ_atomFPE, toQ_lq, liftQ_aR]; simp [crow]; rfl


/-- The IO coins `(γ′, ρ′)` as `𝕂′`. -/
noncomputable abbrev ioQ : FiniteIO.IOCoins KQ := ⟨K6.toQ k.γ, K6.toQ k.ρ⟩

theorem vInv_eq (j : ℕ) :
    K6.toQ (Cell.vInv k j) = (FiniteIO.compress (m := 5) (ioQ k) (vKeyOf deltaF (crowQ k mv mx mx1 j)))⁻¹ := by
  rw [Cell.vInv, K6.toQ_inv, toQ_compressE]
  congr 2
  funext c
  have hp := pE_eq k mv mx mx1 j
  fin_cases c
  · exact congrArg ComputeTable.FP.size hp
  · exact congrArg ComputeTable.FP.dyck hp
  · exact congrArg ComputeTable.FP.leaf hp
  · simp [Cell.vKey, vKeyOf, crow, toQ_mk, toK_g3, toZ_natG] <;> rfl
  · simp [Cell.vKey, vKeyOf, crow, toQ_lq]

theorem xInv_eq (j s : ℕ) :
    K6.toQ ((compressE k.γ k.ρ (Cell.xKey k j s))⁻¹) =
      (FiniteIO.compress (m := 11) (ioQ k) (xKeyOf deltaF (crowQ k mv mx mx1 j) (s : ZMod p)))⁻¹ := by
  rw [K6.toQ_inv, toQ_compressE]
  congr 2
  funext c
  have hp := pE_eq k mv mx mx1 j
  have hl := lE_eq k mv mx mx1 j
  have hr := rE_eq k mv mx mx1 j
  fin_cases c
  · exact congrArg ComputeTable.FP.size hp
  · exact congrArg ComputeTable.FP.dyck hp
  · exact congrArg ComputeTable.FP.leaf hp
  · exact congrArg ComputeTable.FP.size hl
  · exact congrArg ComputeTable.FP.dyck hl
  · exact congrArg ComputeTable.FP.leaf hl
  · exact congrArg ComputeTable.FP.size hr
  · exact congrArg ComputeTable.FP.dyck hr
  · exact congrArg ComputeTable.FP.leaf hr
  · simp [Cell.xKey, xKeyOf, crow, toQ_lq]
  · simp [Cell.xKey, xKeyOf, crow, toQ_lq]

theorem vTerm_eq (j : ℕ) :
    K6.toQ (Cell.vTerm k mv j) = vTermOf deltaF (cellFillInv deltaF (K6.toQ k.γ) (K6.toQ k.ρ) (crowQ k mv mx mx1 j)) := by
  rw [vTerm_crow, Cell.vTerm, K6.toQ_mul, toQ_lq, vInv_eq k mv mx mx1]

theorem xTerm_eq (j : ℕ) :
    K6.toQ (Cell.xTerm k mx mx1 j) =
      xTermOf deltaF (cellFillInv deltaF (K6.toQ k.γ) (K6.toQ k.ρ) (crowQ k mv mx mx1 j)) := by
  rw [xTerm_crow, Cell.xTerm, K6.toQ_add, K6.toQ_mul, K6.toQ_mul, toQ_lq, toQ_lq, Cell.x0Inv, Cell.x1Inv,
    xInv_eq k mv mx mx1, xInv_eq k mv mx mx1]
  simp only [Nat.cast_zero, Nat.cast_one]

/-- The filled honest rows at `K6`-coins `k`. -/
noncomputable abbrev cvalsQ : Fin 2 → CellVals (ZMod p) KQ :=
  cvals deltaF (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z) mv mx mx1

theorem qslot_eq (i : Fin 2) (s : ℕ) (hs : s < 16) :
    K6.toQ (Cell.qslot k mv mx mx1 i s) = (cvalsQ k mv mx mx1 i).qslot s := by
  have hp := pE_eq k mv mx mx1 i
  have hl := lE_eq k mv mx mx1 i
  have hr := rE_eq k mv mx mx1 i
  have hi : (i : ℕ) < 2 := i.isLt
  interval_cases s
  · exact congrArg ComputeTable.FP.size hp
  · exact congrArg ComputeTable.FP.dyck hp
  · exact congrArg ComputeTable.FP.leaf hp
  · exact congrArg ComputeTable.FP.size hl
  · exact congrArg ComputeTable.FP.dyck hl
  · exact congrArg ComputeTable.FP.leaf hl
  · exact congrArg ComputeTable.FP.size hr
  · exact congrArg ComputeTable.FP.dyck hr
  · exact congrArg ComputeTable.FP.leaf hr
  · exact vInv_eq k mv mx mx1 i
  · show K6.toQ 0 = liftQ deltaF (0 : ZMod p) * _
    rw [K6.toQ_zero, liftQ, map_zero, map_zero, zero_mul]
  · show K6.toQ 0 = liftQ deltaF (0 : ZMod p) * _
    rw [K6.toQ_zero, liftQ, map_zero, map_zero, zero_mul]
  · have := xInv_eq k mv mx mx1 i 0
    rw [Nat.cast_zero] at this
    exact this
  · show K6.toQ (Cell.vAcc k mv i) = ∑ q ∈ Finset.range (i + 1),
      vTermOf deltaF (cellFillInv deltaF (K6.toQ k.γ) (K6.toQ k.ρ) (crowQ k mv mx mx1 q))
    rw [Cell.vAcc]
    rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 by omega) with h | h <;>
      simp only [h, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, if_true, one_ne_zero, if_false,
        K6.toQ_add, vTerm_eq k mv mx mx1]
  · show K6.toQ (Cell.xAcc k mx mx1 i) = ∑ q ∈ Finset.range (i + 1),
      xTermOf deltaF (cellFillInv deltaF (K6.toQ k.γ) (K6.toQ k.ρ) (crowQ k mv mx mx1 q))
    rw [Cell.xAcc]
    rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 by omega) with h | h <;>
      simp only [h, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, if_true, one_ne_zero, if_false,
        K6.toQ_add, xTerm_eq k mv mx mx1]
  · have := xInv_eq k mv mx mx1 i 1
    rw [Nat.cast_one] at this
    exact this

end Bridge

/-! ## 4. The column equality -/

section Col
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemCell
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler

variable (k : Co) (mv mx mx1 mh : ℕ → ℕ)

/-- The honest cell column function (`cellCol` of the filled rows). -/
noncomputable abbrev hcol : ℕ → Fin 2 → ZMod p := cellCol deltaF powerBasis3 (cvalsQ k mv mx mx1)
/-- The handle multiplicities as base-field values. -/
abbrev mhF : Fin 2 → ZMod p := fun i => (mh i : ZMod p)

theorem base_eq (i : Fin 2) (c : ℕ) (h2 : 2 ≤ c) (hc : c < 129) :
    Cell.baseZ mv mx mx1 i c = (crowQ k mv mx mx1 i).base c := by
  rcases (show (2 ≤ c ∧ c < 18) ∨ c = 128 ∨ (18 ≤ c ∧ c < 128) by omega) with hr | hr | hr
  · obtain ⟨_, hr⟩ := hr
    interval_cases c <;> simp [Cell.baseZ, CellVals.base, crow, Cell.aR, aRv]
  · subst hr; simp [Cell.baseZ, CellVals.base, crow]
  · unfold Cell.baseZ CellVals.base
    simp only [if_neg (show c ≠ 2 by omega), if_neg (show c ≠ 3 by omega), if_neg (show c ≠ 4 by omega),
      if_neg (show c ≠ 5 by omega), if_neg (show c ≠ 6 by omega), if_neg (show c ≠ 7 by omega),
      if_neg (show c ≠ 8 by omega), if_neg (show c ≠ 9 by omega), if_neg (show c ≠ 10 by omega),
      if_neg (show c ≠ 11 by omega), if_neg (show c ≠ 12 by omega), if_neg (show c ≠ 13 by omega),
      if_neg (show c ≠ 14 by omega), if_neg (show c ≠ 15 by omega), if_neg (show c ≠ 16 by omega),
      if_neg (show c ≠ 17 by omega), if_neg (show c ≠ 128 by omega), if_pos hr]
    show _ = (if c - 18 = 0 then 1 else 0)
    by_cases e : c = 18
    · rw [if_pos e, if_pos (by omega)]
    · rw [if_neg e, if_neg (by omega)]

variable (hn : 0 < 2) (nodes : Fin 2 → ZMod p) {h : ℕ} (orbit : StrictOrbitDomain (ZMod p) 3 h)
  (chals pubs : ℕ → KC)

theorem dRow_eq (hinj : Function.Injective nodes) (hco : hcoins deltaF chals = ⟨K6.toQ k.γH, K6.toQ k.ρH⟩)
    (i : Fin 2) :
    HonestKW.dRowW deltaF powerBasis3 hn nodes orbit chals pubs (hcol k mv mx mx1) (mhF mh) 0 0 i =
      K6.toQ (Cell.dKW k i) := by
  rw [dRowW0 deltaF powerBasis3 hn nodes orbit chals pubs hinj, InhabJ8MemCell.dKW, hco, Cell.dKW, toQ_compressE]
  congr 1
  funext c
  have z0 : liftQ (K := KC) deltaF (0 : ZMod p) = K6.toQ 0 := by rw [K6.toQ_zero, liftQ, map_zero, map_zero]
  fin_cases c
  · show liftQ (K := KC) deltaF ((i : ℕ) : ZMod p) = K6.toQ (lq i)
    rw [toQ_lq]
  · exact z0
  · exact z0
  · exact z0
  · show liftQ (K := KC) deltaF (aRv i) = K6.toQ (lq (Cell.aR i))
    rw [toQ_lq, liftQ_aR]


theorem ivW_eq (hinj : Function.Injective nodes) (hco : hcoins deltaF chals = ⟨K6.toQ k.γH, K6.toQ k.ρH⟩)
    (i : Fin 2) :
    HonestKW.ivW deltaF powerBasis3 hn nodes orbit chals pubs (hcol k mv mx mx1) (mhF mh) 0 0 i =
      K6.toQ (Cell.ivH k i) := by
  rw [HonestKW.ivW, dRow_eq k mv mx mx1 mh hn nodes orbit chals pubs hinj hco, Cell.ivH, K6.toQ_inv]

theorem avW_eq (hinj : Function.Injective nodes) (hco : hcoins deltaF chals = ⟨K6.toQ k.γH, K6.toQ k.ρH⟩)
    (i : Fin 2) :
    HonestKW.avW deltaF powerBasis3 hn nodes orbit chals pubs (hcol k mv mx mx1) (mhF mh) 0 0 i =
      K6.toQ (Cell.avH k mh i) := by
  have hd := dRow_eq k mv mx mx1 mh hn nodes orbit chals pubs hinj hco
  have d0 : HonestKW.dNW deltaF powerBasis3 hn nodes orbit chals pubs (hcol k mv mx mx1) (mhF mh) 0 0 0 =
      K6.toQ (Cell.dKW k 0) := by
    rw [HonestKW.dNW, dif_pos (by norm_num)]; exact hd ⟨0, by norm_num⟩
  have d1 : HonestKW.dNW deltaF powerBasis3 hn nodes orbit chals pubs (hcol k mv mx mx1) (mhF mh) 0 0 1 =
      K6.toQ (Cell.dKW k 1) := by
    rw [HonestKW.dNW, dif_pos (by norm_num)]; exact hd ⟨1, by norm_num⟩
  have m0 : CellTraceH.mN (mhF mh) 0 = ((mh 0 : ℕ) : ZMod p) := by rw [CellTraceH.mN, dif_pos (by norm_num)]
  have m1 : CellTraceH.mN (mhF mh) 1 = ((mh 1 : ℕ) : ZMod p) := by rw [CellTraceH.mN, dif_pos (by norm_num)]
  rw [HonestKW.avW, Cell.avH]
  fin_cases i
  · simp only [Fin.val_zero, zero_add, Finset.sum_range_one, if_true, d0, m0, K6.toQ_mul, toQ_lq, Cell.ivH,
      K6.toQ_inv]
  · simp only [Fin.val_one, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, one_ne_zero, if_false, d0, d1,
      m0, m1, K6.toQ_add, K6.toQ_mul, toQ_lq, Cell.ivH, K6.toQ_inv]


/-- **Column `c < 242` of the executable fill = the honest builder's column function** (`HonestKW.colW` of
`cellCol (cvals …)` with the honest `ivW` / `avW`, under the row masks `fullCol`). -/
theorem colZ_eq (hinj : Function.Injective nodes) (hco : hcoins deltaF chals = ⟨K6.toQ k.γH, K6.toQ k.ρH⟩)
    (c : ℕ) (hc : c < 242) (i : Fin 2) :
    Cell.colZ k mv mx mx1 mh i c =
      fullCol hn (HonestKW.colW deltaF powerBasis3 (hcol k mv mx mx1) (mhF mh) 0 0
        (HonestKW.ivW deltaF powerBasis3 hn nodes orbit chals pubs (hcol k mv mx mx1) (mhF mh) 0 0)
        (HonestKW.avW deltaF powerBasis3 hn nodes orbit chals pubs (hcol k mv mx mx1) (mhF mh) 0 0)) c i := by
  have hiv := ivW_eq k mv mx mx1 mh hn nodes orbit chals pubs hinj hco i
  have hav := avW_eq k mv mx mx1 mh hn nodes orbit chals pubs hinj hco i
  by_cases h0 : c = 0
  · subst h0; simp [Cell.colZ, fullCol]
  by_cases h1 : c = 1
  · subst h1; fin_cases i <;> simp [Cell.colZ, fullCol]
  simp only [fullCol, if_neg h0, if_neg h1, HonestKW.colW, extColF, CellTraceH.cellTemplate_width, Cell.colZ]
  by_cases hb : c < 129
  · rw [if_pos hb, if_pos hb]
    simp only [hcol, cellCol, if_pos hb]
    exact base_eq k mv mx mx1 i c (by omega) hb
  rw [if_neg hb, if_neg hb]
  by_cases h129 : c = 129
  · subst h129; simp [HonestKW.newW]
  by_cases hk : c < 134
  · rw [if_neg h129, if_pos hk, if_pos hk]
    have hz : ∀ j, 11 ≤ j → j ≤ 14 → hcol k mv mx mx1 j i = 0 := by
      intro j hj1 hj2
      simp only [hcol, cellCol, if_pos (show j < 129 by omega)]
      show (crowQ k mv mx mx1 i).base j = 0
      rw [← base_eq k mv mx mx1 i j (by omega) (by omega)]
      simp only [Cell.baseZ]
      interval_cases j <;> simp
    have h130 : 130 ≤ c := by omega
    interval_cases c
    · simp [HonestKW.newW, CellTwinK.kbL]
    · simp [HonestKW.newW, CellTwinK.kbL, CellTwinK.kbR]
    · simp only [HonestKW.newW, CellTwinK.kbL, CellTwinK.kbR, CellTwinK.invL, Cell.loL, Cell.hiL]
      simp [hz 11 (by norm_num) (by norm_num), hz 12 (by norm_num) (by norm_num)]
    · simp only [HonestKW.newW, CellTwinK.kbL, CellTwinK.kbR, CellTwinK.invL, CellTwinK.invR, Cell.loR, Cell.hiR]
      simp [hz 13 (by norm_num) (by norm_num), hz 14 (by norm_num) (by norm_num)]
  rw [if_neg h129, if_neg hk, if_neg hk]
  by_cases hr : c < 230
  · rw [if_pos hr, if_pos (show c < 225 + (134 - 129) by omega)]
    simp only [hcol, cellCol, if_neg (show ¬ (c - (134 - 129) < 129) by omega)]
    have e1 : c - (134 - 129) - 129 = c - 134 := by omega
    simp only [e1]
    unfold Cell.roleZ roleVal
    rw [← qslot_eq k mv mx mx1 i _ (by omega)]
    split_ifs
    · rw [re_toQ, coord_K]
    · rw [im_toQ, coord_K]
  rw [if_neg hr, if_neg (show ¬ c < 225 + (134 - 129) by omega)]
  simp only [HonestKW.newW, CellTwinK.kbL, CellTwinK.kbR, CellTwinK.invL, CellTwinK.invR,
    if_neg (show c ≠ 129 by omega), if_neg (show c ≠ 130 by omega), if_neg (show c ≠ 131 by omega),
    if_neg (show c ≠ 132 by omega), if_neg (show c ≠ 133 by omega)]
  rw [hiv, hav]
  by_cases a1 : c < 233
  · rw [if_pos a1, if_pos ⟨by omega, a1⟩, coordN_toQ_re, Nat.mod_eq_of_lt (by omega)]
    <;> simp [show c ≠ 130 by omega, show c ≠ 131 by omega, show c ≠ 132 by omega, show c ≠ 133 by omega]
  rw [if_neg a1, if_neg (show ¬ (230 ≤ c ∧ c < 233) by omega)]
  by_cases a2 : c < 236
  · rw [if_pos a2, if_pos ⟨by omega, a2⟩, coordN_toQ_im, Nat.mod_eq_of_lt (by omega)]
    <;> simp [show c ≠ 130 by omega, show c ≠ 131 by omega, show c ≠ 132 by omega, show c ≠ 133 by omega]
  rw [if_neg a2, if_neg (show ¬ (233 ≤ c ∧ c < 236) by omega)]
  by_cases a3 : c < 239
  · rw [if_pos a3, if_pos ⟨by omega, a3⟩, coordN_toQ_re, Nat.mod_eq_of_lt (by omega)]
    <;> simp [show c ≠ 130 by omega, show c ≠ 131 by omega, show c ≠ 132 by omega, show c ≠ 133 by omega]
  rw [if_neg a3, if_neg (show ¬ (236 ≤ c ∧ c < 239) by omega), if_pos hc, if_pos ⟨by omega, hc⟩, coordN_toQ_im, Nat.mod_eq_of_lt (by omega)]
    <;> simp [show c ≠ 130 by omega, show c ≠ 131 by omega, show c ≠ 132 by omega, show c ≠ 133 by omega]


/-- **The executable fill's interpolants ARE the honest `cellChipHQKW` trace `trM0`**, column by column. -/
theorem cellTrace_eq (hinj : Function.Injective nodes) (hco : hcoins deltaF chals = ⟨K6.toQ k.γH, K6.toQ k.ρH⟩)
    (j : Fin ((HonestKW.cellTemplateHQKW deltaF).width 3)) :
    Lagrange.interpolate Finset.univ nodes (fun i => Cell.cols k mv mx mx1 mh j i) =
      trM0 deltaF powerBasis3 hn nodes orbit chals pubs (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z) mv mx mx1 mh j := by
  have hj : (j : ℕ) < 242 := by
    have h1 := j.isLt; have h2 := HonestKW.cellTemplateHQKW_width (F := ZMod p) deltaF; omega
  unfold trM0 HonestKW.cellTraceHQKW honestQ
  congr 1
  funext i
  exact colZ_eq k mv mx mx1 mh hn nodes orbit chals pubs hinj hco j hj i

end Col

/-! ## 5. At the frame coins -/

section Frame
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemCell
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)

theorem hcoins_frame (χe : CoinsE) :
    hcoins deltaF (fun j => K3.toK (chalsMJ8E χe j)) = ⟨K6.toQ (coOf χe).γH, K6.toQ (coOf χe).ρH⟩ := by
  simp only [hcoins, coOf, γHE, ρHE, K6.toQ]
  congr 1

/-- **At the frame coins** (`coOf χe`, the memory challenge vector `chalsMJ8 deltaF (toχ χe)`): the cell chip's
interpolated fill is the honest `trM0`. -/
theorem cellTrace_eq_frame (χe : CoinsE) (mv mx mx1 mh : ℕ → ℕ) (hn : 0 < 2) (nodes : Fin 2 → ZMod p)
    (hinj : Function.Injective nodes) {h : ℕ} (orbit : StrictOrbitDomain (ZMod p) 3 h) (pubs : ℕ → KC)
    (j : Fin ((HonestKW.cellTemplateHQKW deltaF).width 3)) :
    Lagrange.interpolate Finset.univ nodes (fun i => Cell.cols (coOf χe) mv mx mx1 mh j i) =
      trM0 deltaF powerBasis3 hn nodes orbit (VerJ8.chalsMJ8 deltaF (toχ χe)) pubs
        (K6.toQ (γVE χe)) (K6.toQ (ρVE χe)) (K6.toQ (zE χe)) mv mx mx1 mh j := by
  rw [chalsMJ8_eq]
  exact cellTrace_eq (coOf χe) mv mx mx1 mh hn nodes orbit _ pubs hinj (hcoins_frame χe) j


/-- The same for the checker's built trace: the cell chip of an input carrying this fill interpolates to `trM0`
(`mkTr`'s `interpOf`, nodes `ω^i`). -/
theorem interpOf_cell (χe : CoinsE) (mv mx mx1 mh : ℕ → ℕ) (hc : ℕ) (ω : Gold)
    (hinj : Function.Injective (nodesOf ⟨hc, 2, ω, Cell.cols (coOf χe) mv mx mx1 mh⟩)) {h : ℕ}
    (orbit : StrictOrbitDomain (ZMod p) 3 h) (pubs : ℕ → KC) (j : Fin ((HonestKW.cellTemplateHQKW deltaF).width 3)) :
    interpOf ⟨hc, 2, ω, Cell.cols (coOf χe) mv mx mx1 mh⟩ j =
      trM0 deltaF powerBasis3 (by norm_num) (nodesOf ⟨hc, 2, ω, Cell.cols (coOf χe) mv mx mx1 mh⟩) orbit
        (VerJ8.chalsMJ8 deltaF (toχ χe)) pubs (K6.toQ (γVE χe)) (K6.toQ (ρVE χe)) (K6.toQ (zE χe)) mv mx mx1 mh j :=
  cellTrace_eq_frame χe mv mx mx1 mh _ _ hinj orbit pubs j

end Frame

end Nock.V1J8.FillMem
