/-
  Nock/V1J8/FillAtom.lean

* `Atom.colZ k zA c`: the one-row atom table (the pad cell `[0 1]`, every multiplicity `0`), every one of the 349
    columns, computable (`K6`), at coins `k` (whose `z` field is the atom table's fingerprint seed `y`) and the g5
    seed `zA`;
  * **`atomColZ_eq`**: column `c < 349` equals the honest column function (`HonestA8.colA` of
    `InhabJ8AtomChip.padC` and `newPad`, under `fullCol`), given the atom chals carry `γH′ ρH′` at `33..36`, `zA` at
    `37 / 38`, and `ChalsOK` for `(γ′, ρ′)`;
  * **`atomTrace_eq`**: the interpolants ARE `padTraceA`; **`atomTrace_eq_frame`** / **`interpOf_atom`**: at the frame
    coins they ARE `InhabJ8Atom.trA0 deltaF powerBasis3 … (toχ χe)` (seed `y = (χ₁₇, χ₁₈)`, `zA = (χ₂, χ₃)`).
-/
import Nock.V1J8.FillCell
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Atom

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

/-! ## 1. The atom-table fill (the inert pad row `[0 1]`) -/

namespace Atom
variable (k : Co) (zA : K6)

def pE : FPE := consE k.z (atomFPE k.z (lq 0)) (atomFPE k.z (lq 1))
def lE : FPE := atomFPE k.z (lq 0)
def rE : FPE := atomFPE k.z (lq 1)

def vInv : K6 :=
  (compressE k.γ k.ρ (![(pE k).size, (pE k).dyck, (pE k).leaf, ⟨g3 (natG 1), g3 (natG 0)⟩, lq 0] : Fin 5 → K6))⁻¹
def xKey (s : ℕ) : Fin 11 → K6 :=
  ![(pE k).size, (pE k).dyck, (pE k).leaf, (lE k).size, (lE k).dyck, (lE k).leaf, (rE k).size, (rE k).dyck,
    (rE k).leaf, lq 0, lq s]
def x0Inv : K6 := (compressE k.γ k.ρ (xKey k 0))⁻¹
def x1Inv : K6 := (compressE k.γ k.ρ (xKey k 1))⁻¹

def qslot (s : ℕ) : K6 :=
  match s with
  | 0 => (pE k).size | 1 => (pE k).dyck | 2 => (pE k).leaf
  | 3 => (lE k).size | 4 => (lE k).dyck | 5 => (lE k).leaf
  | 6 => (rE k).size | 7 => (rE k).dyck | 8 => (rE k).leaf
  | 9 => vInv k | 12 => x0Inv k | 15 => x1Inv k
  | _ => 0

def roleZ (ρ c : ℕ) : ZMod p := limbZ (if ρ % 2 = 0 then (qslot k (ρ / 2)).re else (qslot k (ρ / 2)).im) c

def dH : K6 := compressE k.γH k.ρH (![0, 0, 0, 0, lq 1] : Fin 5 → K6)
def dMB : K6 := compressE k.γ k.ρ (![zA, 0, (pE k).leaf, 0, 0] : Fin 5 → K6)
def dC : K6 := compressE k.γH k.ρH (![0, 0, 0, 0, 0] : Fin 5 → K6)
def dMI : K6 := compressE k.γH k.ρH (![lq 2, 0, lq 2, 0, lq 4] : Fin 5 → K6)

/-- The atom `𝕂′` roles (Re / Im of `mbInv, mbAcc, cInv, miInv, miAcc, cAcc`; the accumulators `0`). -/
def aRole (t : ℕ) : K3 :=
  if t = 0 then (dMB k zA)⁻¹.re else if t = 1 then (dMB k zA)⁻¹.im else if t = 4 then (dC k)⁻¹.re
  else if t = 5 then (dC k)⁻¹.im else if t = 6 then (dMI k)⁻¹.re else if t = 7 then (dMI k)⁻¹.im else 0

/-- **Column `c` of the pad row** (349 columns). -/
def colZ (c : ℕ) : ZMod p :=
  if c < 2 then 1
  else if c = 8 ∨ c = 9 ∨ c = 18 then 1 else if c < 130 then 0
  else if c = 162 ∨ c = 194 then 1 else if c < 205 then 0
  else if c < 301 then roleZ k ((c - 205) / 3) ((c - 205) % 3)
  else if c < 304 then limbZ (dH k)⁻¹.re (c - 301) else if c < 307 then limbZ (dH k)⁻¹.im (c - 304)
  else if c < 313 then 0
  else if c < 349 then limbZ (aRole k zA ((c - 313) / 3)) ((c - 313) % 3) else 0

def cols : ℕ → Fin 1 → ZMod p := fun c _ => colZ k zA c

end Atom

/-- The atom table's coins at `χe`: fingerprint seed `y = (χ₁₇, χ₁₈)` in the `z` slot. -/
def coOfA (χe : CoinsE) : Co := ⟨yE χe, γVE χe, ρVE χe, γHE χe, ρHE χe⟩

/-! ## 2. Bridges (cell part) -/

section ABridge
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomCell

variable (k : Co) (zA : K6)

noncomputable abbrev padQ : CellVals (ZMod p) KQ := padRow deltaF (K6.toQ k.z)

theorem toQ_lq1 : K6.toQ (lq 1) = liftQ (K := KC) deltaF (1 : ZMod p) := by rw [toQ_lq, Nat.cast_one]
theorem toQ_lq0 : K6.toQ (lq 0) = liftQ (K := KC) deltaF (0 : ZMod p) := by rw [toQ_lq, Nat.cast_zero]

theorem apE_eq : (Atom.pE k).toQ = (padQ k).p := by
  rw [Atom.pE, toQ_consE, toQ_atomFPE, toQ_atomFPE, toQ_lq0, toQ_lq1]; rfl
theorem alE_eq : (Atom.lE k).toQ = (padQ k).l := by
  rw [Atom.lE, toQ_atomFPE, toQ_lq0]; rfl
theorem arE_eq : (Atom.rE k).toQ = (padQ k).r := by
  rw [Atom.rE, toQ_atomFPE, toQ_lq1]; rfl

theorem avInv_eq : K6.toQ (Atom.vInv k) = (FiniteIO.compress (m := 5) (ioQ k) (vKeyOf deltaF (padQ k)))⁻¹ := by
  rw [Atom.vInv, K6.toQ_inv, toQ_compressE]
  congr 2
  funext c
  have hp := apE_eq k
  fin_cases c
  · exact congrArg ComputeTable.FP.size hp
  · exact congrArg ComputeTable.FP.dyck hp
  · exact congrArg ComputeTable.FP.leaf hp
  · simp [vKeyOf, padRow, toQ_mk, toK_g3, toZ_natG] <;> rfl
  · show K6.toQ (lq 0) = liftQ deltaF (0 : ZMod p); exact toQ_lq0

theorem axInv_eq (s : ℕ) :
    K6.toQ ((compressE k.γ k.ρ (Atom.xKey k s))⁻¹) =
      (FiniteIO.compress (m := 11) (ioQ k) (xKeyOf deltaF (padQ k) (s : ZMod p)))⁻¹ := by
  rw [K6.toQ_inv, toQ_compressE]
  congr 2
  funext c
  have hp := apE_eq k
  have hl := alE_eq k
  have hr := arE_eq k
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
  · show K6.toQ (lq 0) = liftQ deltaF (0 : ZMod p); exact toQ_lq0
  · show K6.toQ (lq s) = liftQ deltaF (s : ZMod p); exact toQ_lq s

/-- The filled pad rows at `K6`-coins `k`. -/
noncomputable abbrev padValsQ : Fin 1 → CellVals (ZMod p) KQ :=
  padVals deltaF (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z)

theorem aqslot_eq (i : Fin 1) (s : ℕ) (hs : s < 16) :
    K6.toQ (Atom.qslot k s) = (padValsQ k i).qslot s := by
  have hp := apE_eq k
  have hl := alE_eq k
  have hr := arE_eq k
  have hi : (i : ℕ) = 0 := by omega
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
  · exact avInv_eq k
  · show K6.toQ 0 = liftQ deltaF (0 : ZMod p) * _
    rw [K6.toQ_zero, liftQ, map_zero, map_zero, zero_mul]
  · show K6.toQ 0 = liftQ deltaF (0 : ZMod p) * _
    rw [K6.toQ_zero, liftQ, map_zero, map_zero, zero_mul]
  · have := axInv_eq k 0
    rw [Nat.cast_zero] at this
    exact this
  · show K6.toQ 0 = ∑ q ∈ Finset.range ((i : ℕ) + 1),
      vTermOf deltaF (cellFillInv deltaF (K6.toQ k.γ) (K6.toQ k.ρ) (padQ k))
    rw [hi, Finset.sum_range_one, pad_vTerm, K6.toQ_zero]
  · show K6.toQ 0 = ∑ q ∈ Finset.range ((i : ℕ) + 1),
      xTermOf deltaF (cellFillInv deltaF (K6.toQ k.γ) (K6.toQ k.ρ) (padQ k))
    rw [hi, Finset.sum_range_one, pad_xTerm, K6.toQ_zero]
  · have := axInv_eq k 1
    rw [Nat.cast_one] at this
    exact this

end ABridge

/-! ## 3. The denominators in closed form -/

section ADen
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomCell Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomChip
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8AtomDen
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)

theorem toQ_compressE5 (γ ρ a b c d e : K6) :
    K6.toQ (compressE γ ρ ![a, b, c, d, e]) = K6.toQ ρ + (K6.toQ a + K6.toQ γ * K6.toQ b + K6.toQ γ ^ 2 * K6.toQ c +
      K6.toQ γ ^ 3 * K6.toQ d + K6.toQ γ ^ 4 * K6.toQ e) := by
  rw [toQ_compressE]
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_five]
  simp

theorem toQ_lqN (n : ℕ) : K6.toQ (lq n) = (n : KQ) := by
  rw [toQ_lq, liftQ, map_natCast, map_natCast]

variable (k : Co) (zA : K6) (hn : 0 < 1) (nodes : Fin 1 → ZMod p) {h : ℕ}
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (ch pubs : ℕ → KC) (i : Fin 1)

theorem dH_eq (hG : Quad.mk _ (ch 33) (ch 35) = K6.toQ k.γH) (hR : Quad.mk _ (ch 34) (ch 36) = K6.toQ k.ρH) :
    CellTraceHQ.dRow deltaF powerBasis3 hn nodes orbit ch pubs
      (padCol deltaF powerBasis3 (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z)) (fun _ => 0) i = K6.toQ (Atom.dH k) := by
  rw [padRow_eq, hG, hR, Atom.dH, toQ_compressE5, K6.toQ_zero, toQ_lqN]
  push_cast
  ring

theorem dMB_eq (hok : ChalsOK deltaF ch (K6.toQ k.γ) (K6.toQ k.ρ) 11)
    (hZ : Quad.mk _ (ch 37) (ch 38) = K6.toQ zA) :
    HonestA8.dMB deltaF powerBasis3 hn nodes orbit ch pubs
      (padC deltaF powerBasis3 hn nodes orbit ch pubs (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z)) newPad i =
      K6.toQ (Atom.dMB k zA) := by
  rw [padMB_eq deltaF powerBasis3 hn nodes orbit ch pubs _ _ _ i hok, hZ, Atom.dMB, toQ_compressE5]
  have hl : K6.toQ (Atom.pE k).leaf = K6.toQ k.z := by
    have := congrArg ComputeTable.FP.leaf (apE_eq k)
    rw [show (Atom.pE k).toQ.leaf = K6.toQ (Atom.pE k).leaf from rfl] at this
    rw [this]
    show liftQ deltaF (0 : ZMod p) + K6.toQ k.z * liftQ deltaF (1 : ZMod p) = _
    rw [liftQ, liftQ, map_zero, map_zero, map_one, map_one, zero_add, mul_one]
  rw [hl, K6.toQ_zero]
  ring

theorem dC_eq (hR : Quad.mk _ (ch 34) (ch 36) = K6.toQ k.ρH) :
    HonestA8.dC deltaF powerBasis3 hn nodes orbit ch pubs
      (padC deltaF powerBasis3 hn nodes orbit ch pubs (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z)) newPad i =
      K6.toQ (Atom.dC k) := by
  rw [padC_eq, hR, Atom.dC, toQ_compressE5, K6.toQ_zero]
  ring

theorem dMI_eq (hG : Quad.mk _ (ch 33) (ch 35) = K6.toQ k.γH) (hR : Quad.mk _ (ch 34) (ch 36) = K6.toQ k.ρH) :
    HonestA8.dMI deltaF powerBasis3 hn nodes orbit ch pubs
      (padC deltaF powerBasis3 hn nodes orbit ch pubs (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z)) newPad i =
      K6.toQ (Atom.dMI k) := by
  rw [padMI_eq, hG, hR, Atom.dMI, toQ_compressE5, K6.toQ_zero, toQ_lqN, toQ_lqN]
  push_cast
  ring


theorem limb0 (m : ℕ) : limbZ (0 : K6).re m = 0 := by
  show MemX.limb (0 : K3) m = 0
  unfold MemX.limb; split_ifs <;> exact Gold.toZ_zero

theorem limb0' (m : ℕ) : limbZ (0 : K6).im m = 0 := by
  show MemX.limb (0 : K3) m = 0
  unfold MemX.limb; split_ifs <;> exact Gold.toZ_zero

theorem re0 : Quad.re _ (0 : KQ) = 0 := by rw [← K6.toQ_zero, re_toQ]; exact K3.toK_zero
theorem im0 : Quad.im _ (0 : KQ) = 0 := by rw [← K6.toQ_zero, im_toQ]; exact K3.toK_zero

theorem accPad (j : ℕ) (hj : (AtomGenJ8.padNew j : ZMod p) = 0) (d : Fin 1 → KQ) :
    HonestA8.accOf deltaF (newPad (n := 1) j) d i = 0 := by
  have hi : (i : ℕ) = 0 := by omega
  rw [HonestA8.accOf, hi, zero_add, Finset.sum_range_one, HonestA8.cNat, dif_pos (by norm_num)]
  show liftQ deltaF (AtomGenJ8.padNew j : ZMod p) * _ = 0
  rw [hj, liftQ, map_zero, map_zero, zero_mul]

/-- **The atom `𝕂′` role values**: `K3.toK (aRole t) = roleValA … t i`. -/
theorem aRole_eq (hok : ChalsOK deltaF ch (K6.toQ k.γ) (K6.toQ k.ρ) 11)
    (hG : Quad.mk _ (ch 33) (ch 35) = K6.toQ k.γH) (hR : Quad.mk _ (ch 34) (ch 36) = K6.toQ k.ρH)
    (hZ : Quad.mk _ (ch 37) (ch 38) = K6.toQ zA) (t : ℕ) (ht : t < 12) :
    K3.toK (Atom.aRole k zA t) = HonestA8.roleValA deltaF powerBasis3 hn nodes orbit ch pubs
      (padC deltaF powerBasis3 hn nodes orbit ch pubs (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z)) newPad t i := by
  have hMB := dMB_eq k zA hn nodes orbit ch pubs i hok hZ
  have hC := dC_eq k hn nodes orbit ch pubs i hR
  have hMI := dMI_eq k hn nodes orbit ch pubs i hG hR
  have aMB := accPad i AtomChipHQ.mb (AtomGenJ8.padNew_inert.2.2.1)
  have aC := accPad i AtomChipHQ.inc (AtomGenJ8.padNew_inert.1)
  have aMI := accPad i AtomChipHQ.mi (by simp [AtomGenJ8.padNew, AtomChipHQ.mi, AtomChipHQ.bitR, AtomChipHQ.invT])
  unfold HonestA8.roleValA
  simp only []
  rcases t with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | t
  · rw [if_pos rfl, hMB, ← K6.toQ_inv, re_toQ]; rfl
  · rw [if_neg (by norm_num), if_pos rfl, hMB, ← K6.toQ_inv, im_toQ]; rfl
  · simp only [show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_false, if_true, aMB]
    show K3.toK 0 = _; rw [K3.toK_zero, re0]
  · simp only [show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num, show (3 : ℕ) ≠ 2 by norm_num, if_false, if_true, aMB]
    show K3.toK 0 = _; rw [K3.toK_zero, im0]
  · simp only [show (4 : ℕ) ≠ 0 by norm_num, show (4 : ℕ) ≠ 1 by norm_num, show (4 : ℕ) ≠ 2 by norm_num, show (4 : ℕ) ≠ 3 by norm_num, if_false, if_true, hC]
    show K3.toK ((Atom.dC k)⁻¹.re) = _; rw [← K6.toQ_inv, re_toQ]
  · simp only [show (5 : ℕ) ≠ 0 by norm_num, show (5 : ℕ) ≠ 1 by norm_num, show (5 : ℕ) ≠ 2 by norm_num, show (5 : ℕ) ≠ 3 by norm_num, show (5 : ℕ) ≠ 4 by norm_num, if_false, if_true, hC]
    show K3.toK ((Atom.dC k)⁻¹.im) = _; rw [← K6.toQ_inv, im_toQ]
  · simp only [show (6 : ℕ) ≠ 0 by norm_num, show (6 : ℕ) ≠ 1 by norm_num, show (6 : ℕ) ≠ 2 by norm_num, show (6 : ℕ) ≠ 3 by norm_num, show (6 : ℕ) ≠ 4 by norm_num, show (6 : ℕ) ≠ 5 by norm_num, if_false, if_true, hMI]
    show K3.toK ((Atom.dMI k)⁻¹.re) = _; rw [← K6.toQ_inv, re_toQ]
  · simp only [show (7 : ℕ) ≠ 0 by norm_num, show (7 : ℕ) ≠ 1 by norm_num, show (7 : ℕ) ≠ 2 by norm_num, show (7 : ℕ) ≠ 3 by norm_num, show (7 : ℕ) ≠ 4 by norm_num, show (7 : ℕ) ≠ 5 by norm_num, show (7 : ℕ) ≠ 6 by norm_num, if_false, if_true, hMI]
    show K3.toK ((Atom.dMI k)⁻¹.im) = _; rw [← K6.toQ_inv, im_toQ]
  · simp only [show (8 : ℕ) ≠ 0 by norm_num, show (8 : ℕ) ≠ 1 by norm_num, show (8 : ℕ) ≠ 2 by norm_num, show (8 : ℕ) ≠ 3 by norm_num, show (8 : ℕ) ≠ 4 by norm_num, show (8 : ℕ) ≠ 5 by norm_num, show (8 : ℕ) ≠ 6 by norm_num, show (8 : ℕ) ≠ 7 by norm_num, if_false, if_true, aMI]
    show K3.toK 0 = _; rw [K3.toK_zero, re0]
  · simp only [show (9 : ℕ) ≠ 0 by norm_num, show (9 : ℕ) ≠ 1 by norm_num, show (9 : ℕ) ≠ 2 by norm_num, show (9 : ℕ) ≠ 3 by norm_num, show (9 : ℕ) ≠ 4 by norm_num, show (9 : ℕ) ≠ 5 by norm_num, show (9 : ℕ) ≠ 6 by norm_num, show (9 : ℕ) ≠ 7 by norm_num, show (9 : ℕ) ≠ 8 by norm_num, if_false, if_true, aMI]
    show K3.toK 0 = _; rw [K3.toK_zero, im0]
  · simp only [show (10 : ℕ) ≠ 0 by norm_num, show (10 : ℕ) ≠ 1 by norm_num, show (10 : ℕ) ≠ 2 by norm_num, show (10 : ℕ) ≠ 3 by norm_num, show (10 : ℕ) ≠ 4 by norm_num, show (10 : ℕ) ≠ 5 by norm_num, show (10 : ℕ) ≠ 6 by norm_num, show (10 : ℕ) ≠ 7 by norm_num, show (10 : ℕ) ≠ 8 by norm_num, show (10 : ℕ) ≠ 9 by norm_num, if_false, if_true, aC]
    show K3.toK 0 = _; rw [K3.toK_zero, re0]
  · simp only [show (11 : ℕ) ≠ 0 by norm_num, show (11 : ℕ) ≠ 1 by norm_num, show (11 : ℕ) ≠ 2 by norm_num, show (11 : ℕ) ≠ 3 by norm_num, show (11 : ℕ) ≠ 4 by norm_num, show (11 : ℕ) ≠ 5 by norm_num, show (11 : ℕ) ≠ 6 by norm_num, show (11 : ℕ) ≠ 7 by norm_num, show (11 : ℕ) ≠ 8 by norm_num, show (11 : ℕ) ≠ 9 by norm_num, show (11 : ℕ) ≠ 10 by norm_num, if_false, aC]
    show K3.toK 0 = _; rw [K3.toK_zero, im0]
  · omega


theorem abase_eq (c : ℕ) (h2 : 2 ≤ c) (hc : c < 129) :
    (if c = 8 ∨ c = 9 ∨ c = 18 then (1 : ZMod p) else 0) = (padQ k).base c := by
  rcases (show (2 ≤ c ∧ c < 18) ∨ c = 128 ∨ (18 ≤ c ∧ c < 128) by omega) with hr | hr | hr
  · obtain ⟨_, hr⟩ := hr
    interval_cases c <;> simp [CellVals.base, padRow]
  · subst hr; simp [CellVals.base, padRow]
  · unfold CellVals.base
    simp only [if_neg (show c ≠ 2 by omega), if_neg (show c ≠ 3 by omega), if_neg (show c ≠ 4 by omega),
      if_neg (show c ≠ 5 by omega), if_neg (show c ≠ 6 by omega), if_neg (show c ≠ 7 by omega),
      if_neg (show c ≠ 8 by omega), if_neg (show c ≠ 9 by omega), if_neg (show c ≠ 10 by omega),
      if_neg (show c ≠ 11 by omega), if_neg (show c ≠ 12 by omega), if_neg (show c ≠ 13 by omega),
      if_neg (show c ≠ 14 by omega), if_neg (show c ≠ 15 by omega), if_neg (show c ≠ 16 by omega),
      if_neg (show c ≠ 17 by omega), if_neg (show c ≠ 128 by omega)]
    show _ = (if c - 18 = 0 then 1 else 0)
    by_cases e : c = 18
    · rw [if_pos (Or.inr (Or.inr e)), if_pos (by omega)]
    · rw [if_neg (by omega), if_neg (by omega)]

/-- The honest cell-part columns of the pad row. -/
noncomputable abbrev padCQ : ℕ → Fin 1 → ZMod p :=
  padC deltaF powerBasis3 hn nodes orbit ch pubs (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z)

theorem pc_base (c : ℕ) (hc : c < 129) : padCQ k hn nodes orbit ch pubs c i = (padQ k).base c := by
  simp only [padCQ, padC, CellTraceHQ.colHQ, extColF, if_pos hc, padCol, cellCol]
  rfl

theorem pc_129 : padCQ k hn nodes orbit ch pubs 129 i = 0 := by
  simp [padCQ, padC, CellTraceHQ.colHQ, extColF, CellTraceHQ.new]

theorem pc_role (c : ℕ) (h1 : 130 ≤ c) (h2 : c < 226) :
    padCQ k hn nodes orbit ch pubs c i = Atom.roleZ k ((c - 130) / 3) ((c - 130) % 3) := by
  unfold Atom.roleZ
  simp only [padCQ, padC, CellTraceHQ.colHQ, extColF, if_neg (show ¬ c < 129 by omega),
    if_neg (show ¬ c < 130 by omega), CellTraceH.cellTemplate_width, if_pos (show c < 225 + (130 - 129) by omega),
    padCol, cellCol, if_neg (show ¬ (c - (130 - 129) < 129) by omega)]
  have e1 : c - (130 - 129) - 129 = c - 130 := by omega
  simp only [e1]
  unfold roleVal
  rw [← aqslot_eq k i _ (by omega)]
  split_ifs
  · rw [re_toQ, coord_K]
  · rw [im_toQ, coord_K]

theorem pc_new (c : ℕ) (h1 : 226 ≤ c) (h2 : c < 238) :
    padCQ k hn nodes orbit ch pubs c i = CellTraceHQ.new deltaF powerBasis3 (fun _ => 0)
      (CellTraceHQ.ivF deltaF powerBasis3 hn nodes orbit ch pubs
        (padCol deltaF powerBasis3 (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z)) (fun _ => 0))
      (CellTraceHQ.avF deltaF powerBasis3 hn nodes orbit ch pubs
        (padCol deltaF powerBasis3 (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z)) (fun _ => 0)) c i := by
  simp only [padCQ, padC, CellTraceHQ.colHQ, extColF, if_neg (show ¬ c < 129 by omega),
    if_neg (show ¬ c < 130 by omega), CellTraceH.cellTemplate_width, if_neg (show ¬ c < 225 + (130 - 129) by omega)]

/-- **Column `c < 349` of the executable atom fill = the honest column function** (`HonestA8.colA` of `padC` and
`newPad`, under `fullCol`). -/
theorem atomColZ_eq (hok : ChalsOK deltaF ch (K6.toQ k.γ) (K6.toQ k.ρ) 11)
    (hG : Quad.mk _ (ch 33) (ch 35) = K6.toQ k.γH) (hR : Quad.mk _ (ch 34) (ch 36) = K6.toQ k.ρH)
    (hZ : Quad.mk _ (ch 37) (ch 38) = K6.toQ zA) (c : ℕ) (hc : c < 349) :
    Atom.colZ k zA c = fullCol hn (HonestA8.colA deltaF powerBasis3 hn nodes orbit ch pubs
      (padCQ k hn nodes orbit ch pubs) newPad) c i := by
  have i0 : i = ⟨0, by norm_num⟩ := Fin.ext (by omega)
  by_cases h0 : c = 0
  · subst h0; simp [Atom.colZ, fullCol, i0]
  by_cases h1 : c = 1
  · subst h1; simp [Atom.colZ, fullCol, i0]
  simp only [fullCol, if_neg h0, if_neg h1, HonestA8.colA, extColF, CellTraceHQ.cellTemplateHQ_width]
  simp only [Atom.colZ, if_neg (show ¬ c < 2 by omega)]
  by_cases hb : c < 130
  · rw [if_pos hb, if_pos hb]
    by_cases h129 : c = 129
    · subst h129; rw [pc_129]; simp
    rw [pc_base k hn nodes orbit ch pubs i c (by omega)]
    exact abase_eq k c (by omega) (by omega)
  rw [if_neg hb, if_neg hb]
  by_cases h205 : c < 205
  · rw [if_neg (show ¬ (c = 8 ∨ c = 9 ∨ c = 18) by omega), if_pos h205, if_pos h205]
    simp only [HonestA8.newFull, if_pos (show c < 313 by omega), newPad, AtomGenJ8.padNew, AtomChipHQ.bitR,
      AtomChipHQ.invT]
    split_ifs <;> first | rfl | omega | (simp_all; done) | (split_ifs <;> simp_all; done)
  rw [if_neg (show ¬ (c = 8 ∨ c = 9 ∨ c = 18) by omega), if_neg h205, if_neg h205,
    if_neg (show ¬ (c = 162 ∨ c = 194) by omega)]
  by_cases h313 : c < 313
  · rw [if_pos (show c < 238 + (205 - 130) by omega)]
    by_cases h301 : c < 301
    · rw [if_pos h301, pc_role k hn nodes orbit ch pubs i _ (by omega) (by omega)]
      have e : c - (205 - 130) - 130 = c - 205 := by omega
      rw [e]
      simp only [if_pos (show c < 238 + (205 - 130) by omega)]
    rw [if_neg h301, pc_new k hn nodes orbit ch pubs i _ (by omega) (by omega)]
    have hiv : CellTraceHQ.ivF deltaF powerBasis3 hn nodes orbit ch pubs
        (padCol deltaF powerBasis3 (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z)) (fun _ => 0) i =
          K6.toQ (Atom.dH k)⁻¹ := by
      rw [K6.toQ_inv, ← dH_eq k hn nodes orbit ch pubs i hG hR]; rfl
    have hav : CellTraceHQ.avF deltaF powerBasis3 hn nodes orbit ch pubs
        (padCol deltaF powerBasis3 (K6.toQ k.γ) (K6.toQ k.ρ) (K6.toQ k.z)) (fun _ => 0) i = 0 := by
      rw [CellTraceHQ.avF, i0, Fin.val_mk, zero_add, Finset.sum_range_one, CellTraceH.mN, dif_pos (by norm_num)]
      show liftQ deltaF (0 : ZMod p) * _ = 0
      rw [liftQ, map_zero, map_zero, zero_mul]
    simp only [CellTraceHQ.new, if_neg (show c - (205 - 130) ≠ 129 by omega), hiv, hav]
    by_cases a1 : c < 304
    · rw [if_pos a1, if_pos (show 226 ≤ c - (205 - 130) ∧ c - (205 - 130) < 229 from ⟨by omega, by omega⟩),
        coordN_toQ_re, Nat.mod_eq_of_lt (by omega), show c - (205 - 130) - 226 = c - 301 by omega]
      simp only [if_pos (show c < 238 + (205 - 130) by omega)]
    rw [if_neg a1, if_neg (show ¬ (226 ≤ c - (205 - 130) ∧ c - (205 - 130) < 229) by omega)]
    by_cases a2 : c < 307
    · rw [if_pos a2, if_pos (show 229 ≤ c - (205 - 130) ∧ c - (205 - 130) < 232 from ⟨by omega, by omega⟩),
        coordN_toQ_im, Nat.mod_eq_of_lt (by omega), show c - (205 - 130) - 229 = c - 304 by omega]
      simp only [if_pos (show c < 238 + (205 - 130) by omega)]
    rw [if_neg a2, if_neg (show ¬ (229 ≤ c - (205 - 130) ∧ c - (205 - 130) < 232) by omega), if_pos h313]
    rw [← K6.toQ_zero]
    split_ifs <;> first | omega | rw [coordN_toQ_re, limb0] | rw [coordN_toQ_im, limb0']
  rw [if_neg (show ¬ c < 238 + (205 - 130) by omega), if_neg (show ¬ c < 301 by omega),
    if_neg (show ¬ c < 304 by omega), if_neg (show ¬ c < 307 by omega), if_neg h313, if_pos hc]
  simp only [HonestA8.newFull, if_neg h313]
  rw [← aRole_eq k zA hn nodes orbit ch pubs i hok hG hR hZ _ (by omega), coordN, coord_K]


/-- **The executable atom fill's interpolants ARE the honest pad trace `padTraceA`**, column by column. -/
theorem atomTrace_eq (hok : ChalsOK deltaF ch (K6.toQ k.γ) (K6.toQ k.ρ) 11)
    (hG : Quad.mk _ (ch 33) (ch 35) = K6.toQ k.γH) (hR : Quad.mk _ (ch 34) (ch 36) = K6.toQ k.ρH)
    (hZ : Quad.mk _ (ch 37) (ch 38) = K6.toQ zA) (j : Fin 349) :
    Lagrange.interpolate Finset.univ nodes (fun i => Atom.cols k zA j i) =
      HonestA8.atomTraceHQ deltaF powerBasis3 hn nodes orbit ch pubs (padCQ k hn nodes orbit ch pubs) newPad j := by
  unfold HonestA8.atomTraceHQ honestQ
  congr 1
  funext i
  exact atomColZ_eq k zA hn nodes orbit ch pubs i hok hG hR hZ j j.isLt

end ADen

/-! ## 4. At the frame coins -/

section AFrame
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Atom
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)

/-- **At the frame coins**: the atom fill at `coOfA χe` (seed `y`) and `zA = zE χe` interpolates to the honest
`InhabJ8Atom.trA0 deltaF powerBasis3 … (toχ χe)`. -/
theorem atomTrace_eq_frame (χe : CoinsE) (hn : 0 < 1) (nodes : Fin 1 → ZMod p) {h : ℕ}
    (orbit : StrictOrbitDomain (ZMod p) 3 h) (j : Fin 349) :
    Lagrange.interpolate Finset.univ nodes (fun i => Atom.cols (coOfA χe) (zE χe) j i) =
      trA0 deltaF powerBasis3 hn nodes orbit (toχ χe) j := by
  have hok := ChalsAZJ8.chalsAJ8Z_ok deltaF (toχ χe)
  have hZ := ChalsAZJ8.chalsAJ8Z_zAt deltaF (toχ χe)
  rw [atomTrace_eq (coOfA χe) (zE χe) hn nodes orbit _ pubsA0 hok, trA0]
  · rfl
  · rw [chalsAJ8Z_eq]; rfl
  · rw [chalsAJ8Z_eq]; rfl
  · exact hZ


/-- The same for the checker's `interpOf` (atom chip of the input, nodes `ω^i`). -/
theorem interpOf_atom (χe : CoinsE) (ha : ℕ) (ω : Gold) {h : ℕ} (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (j : Fin 349) :
    interpOf ⟨ha, 1, ω, Atom.cols (coOfA χe) (zE χe)⟩ j =
      trA0 deltaF powerBasis3 (by norm_num) (nodesOf ⟨ha, 1, ω, Atom.cols (coOfA χe) (zE χe)⟩) orbit (toχ χe) j :=
  atomTrace_eq_frame χe _ _ orbit j

end AFrame

end Nock.V1J8.FillMem
