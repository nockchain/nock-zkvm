/-
  Nock/RedTeam/Batch4857Thm54J9ANegChip.lean

  Each attack is a concrete row (or a row pair: current + next) obtained from an HONEST row by overriding a few
  columns; the theorem says that the chip's base-gate list fails at EXACTLY the named gate
  (`failing env = [gate]`, `decide +kernel`), and the honest row has no failing gate (positive control). LABEL: row (base-gate) level, in `ℚ`; bus / record-level rejections are not in this file. Reused, not duplicated: `AxisChipJ9.nc_drop_headCl/padding_rejected`, `ChipHX9.naive_state0_split_breaks_disjoint`,
  `ChipHX9.kidKinds_unrelaxed_rejects_s10S`. -/
import Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9
import Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ChipHX9

set_option autoImplicit false

namespace Nock.RedTeam.Batch4857

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

noncomputable section

/-- Column lookup of an override list (first hit wins), default `0`. -/
def lk (l : List (ℕ × ℚ)) : ℕ → ℚ := fun i => (l.lookup i).getD 0

/-- A two-row environment: current row `c`, next row `n` (override lists). -/
def mkEnv (c n : List (ℕ × ℚ)) : Env ℚ := ⟨lk c, lk n, fun _ => 0, fun _ => 0⟩

/-! ## 1. Axis chip -/

section Axis
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9

/-- `B = 2^32`. -/
def Bq : ℚ := 2 ^ 32

/-- Honest 2-limb chain `(R = 5, hr = 7)`, limbs `l_1 = 3` (head, top) and `l_0 = 2`: row 0. -/
def r0 : List (ℕ × ℚ) :=
  [(isFT, 1), (head, 1), (R, 5), (pw, 4), (l, 3), (axK, 3), (axS, 3), (hrv, 7), (hink, 1), (hinv, 7),
   (houtk, 1), (houtv, 9), (ftk, 2), (ftv, 5)]

/-- Row 1: the chain-last row, provides the tag record (`mu = 1`). -/
def r1 : List (ℕ × ℚ) :=
  [(isLT, 1), (cl, 1), (R, 5), (pw, 4), (l, 2), (axK, 2), (axS, 2 + Bq), (hrv, 7), (hink, 1), (hinv, 9),
   (houtk, 1), (houtv, 0), (ftk, 2), (ftv, 5), (mu, 1)]

/-- The base gates that do not vanish at `e`. -/
def axFail (e : Env ℚ) : List (CoeffExpr ℚ) := (baseGates (F := ℚ)).filter fun g => g.eval e ≠ 0

/-- The gate of a tagged list at an index. -/
def gt (xs : List (AG ℚ)) (i : ℕ) : CoeffExpr ℚ := ((xs.map AG.gate).getD i (.const 0))

/-- **Positive control**: the honest rows fail no base gate. -/
theorem ax_honest0 : axFail (mkEnv r0 r1) = [] := by decide +kernel
theorem ax_honest1 : axFail (mkEnv r1 []) = [] := by decide +kernel

/-- (c) **early stop at `pw = 8`** (chain-last row with a wrong width): `cl·(pw − 4)`. -/
theorem nc_early_stop : axFail (mkEnv ((pw, 8) :: (axK, 6) :: r1) []) = [gt g6p 1] := by decide +kernel

/-- (c) **skipped second row** (`next.pw` not doubled-schedule): `(1−cl)(2·next.pw − pw(1+head))`. -/
theorem nc_skipped_row : axFail (mkEnv r0 ((pw, 2) :: r1)) = [gt g6p 0] := by decide +kernel

/-- `TAG_ax` provided on a non-last row: `(1−cl)·mu`. -/
theorem nc_tag_nonlast : axFail (mkEnv ((mu, 1) :: r0) r1) = [gt g8 2] := by decide +kernel

/-- A chain not starting at the table's first row (`isFirstT` with `head = 0`): `isFT·(1−head)`. -/
theorem nc_chain_not_first :
    axFail (mkEnv ((head, 0) :: (pw, 8) :: (axK, 6) :: (axS, 3 + Bq) :: r0) r1) = [gt g6b 3] := by
  decide +kernel

/-- A partial chain at the table end (`isLastT` with `cl = 0`): `isLT·(1−cl)`. -/
theorem nc_partial_at_end : axFail (mkEnv ((isLT, 1) :: r0) r1) = [gt g6b 2] := by decide +kernel

/-- `z1a` with `l ≠ 1`: `z1a·(l−1)`. -/
theorem nc_z1a_l : axFail (mkEnv ((z1a, 1) :: (houtv, 7) :: r0) ((hinv, 7) :: r1)) = [gt g4 1] := by
  decide +kernel

/-- `z1a` off the head: `z1a·(1−head)`. -/
theorem nc_z1a_offhead :
    axFail (mkEnv ((z1a, 1) :: (l, 1) :: (axS, 1 + Bq) :: (houtv, 9) :: r1) []) = [gt g4 0] := by
  decide +kernel

/-- `hd` lie, head row (axis `pw` instead of `pw − 1`): `head·(axK − pw + 1)`. -/
theorem nc_hd_head : axFail (mkEnv ((axK, 4) :: r0) r1) = [gt g2 0] := by decide +kernel

/-- `hd` lie, non-head row (axis `pw` instead of `pw − 2`): `(1−head)(axK − pw + 2)`. -/
theorem nc_hd_nonhead : axFail (mkEnv ((axK, 4) :: r1) []) = [gt g2 1] := by decide +kernel

/-- Root lie on the head (`hin.v ≠ hr.v`): the `head·(hin.v − hr.v)` copy. -/
theorem nc_root_lie : axFail (mkEnv ((hinv, 8) :: r0) r1) = [gt g5 0] := by decide +kernel

/-- (b) **axis from a different atom** (`R` changes along the chain): `(1−cl)(next.R − R)`. -/
theorem nc_R_change : axFail (mkEnv r0 ((R, 6) :: r1)) = [gt g6c 2] := by decide +kernel

/-- (a) a chain's continuity break (`next.hin.k ≠ hout.k`): `(1−cl)(next.hin.k − hout.k)`. -/
theorem nc_hin_break : axFail (mkEnv r0 ((hink, 0) :: r1)) = [gt g6c 0] := by decide +kernel

/-- The `mb` row `(0, ·)` emission (`route0`, head): the honest limb-pair emission. -/
def e0 : List (ℕ × ℚ) :=
  [(route0, 1), (r0h, 1), (l, Bq - 1), (axS, Bq - 1), (ftk, 0), (ftv, (Bq - 1) * Bq + 1), (v, (Bq - 1) * Bq + 1)]

/-- **`(0, val mod p)` from an `mb` row's two limbs**: with `l = B−1` and `next.l = 1` no `invg4` makes
`r0h·next.l·((l − (B−1))·invg4 − 1)` vanish. -/
theorem nc_mod_p_emission :
    axFail (mkEnv (e0 ++ r0) ((route0, 1) :: (v, (Bq - 1) * Bq + 1) :: (l, 1) :: r1)) = [gt g7 2] := by
  decide +kernel

/-- … and for EVERY value of the `invg4` column. -/
theorem nc_mod_p_emission_all (e : Env ℚ) (h1 : e.trace r0h = 1) (h2 : e.traceNext l = 1)
    (h3 : e.trace l = Bq - 1) : (gt g7 2).eval e ≠ 0 := by
  have : gt g7 2 = .mul (.mul (cv r0h) (nv l)) (.sub (.mul (.sub (cv l) (.const (Bf - 1))) (cv invg4)) (.const 1)) := rfl
  rw [this]
  have hB : (Bf : ℚ) = Bq := rfl
  simp [CoeffExpr.eval, h1, h2, h3, hB]

/-- A 3-limb atom with a `(0, ·)` emission (next row is not chain-last): `r0h·(1 − next.cl)`. -/
theorem nc_three_limb_emission :
    axFail (mkEnv ((route0, 1) :: (r0h, 1) :: (l, 3) :: (axS, 3) :: (ftk, 0) :: (ftv, 3 * Bq + 2) :: (v, 3 * Bq + 2) ::
        (invg4, 1 / (4 - Bq)) :: r0) ((cl, 0) :: (route0, 1) :: (v, 3 * Bq + 2) :: r1)) = [gt g7 1] := by
  decide +kernel

end Axis

/-! ## 2. Split chip -/

section Split
open Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9

/-- The honest split row: `v = 2^32·1 + 0` (`hi = 1`, bit 32 set), `nA = 5`, `id = 5`. -/
def s0 : List (ℕ × ℚ) := [(isFT, 1), (isLT, 1), (sid, 5), (hi, 1), (bit0 + 32, 1), (invHi, 1)]

def spFail (e : Env ℚ) : List (CoeffExpr ℚ) := (baseGates (F := ℚ) 5).filter fun g => g.eval e ≠ 0

theorem sp_honest : spFail (mkEnv s0 []) = [] := by decide +kernel

/-- Id collision (`id` not `nA + s`): `id − pubNA − s`. -/
theorem nc_sp_id : spFail (mkEnv ((sid, 6) :: s0) []) = [(counter (F := ℚ) 5).getD 2 (.const 0)] := by
  decide +kernel

/-- A field axis `< 2^32` through the split (`hi = 0`): `hi·invHi = 1` fails (for any `invHi`). -/
theorem nc_sp_hi_zero : spFail (mkEnv [(isFT, 1), (isLT, 1), (sid, 5)] []) = [hiNZ.getD 0 (.const 0)] := by
  decide +kernel

theorem nc_sp_hi_zero_all (F : Type) [Field F] (e : Env F) (h : e.trace hi = 0) :
    ∃ g ∈ (hiNZ : List (CoeffExpr F)), g.eval e ≠ 0 := by
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  simp [CoeffExpr.eval, h]

/-- A non-boolean bit (`b_1 = 2`, with the limb decode patched): the booleanity gate. -/
theorem nc_sp_bit : spFail (mkEnv ((bit0 + 1, 2) :: (lo, 4) :: s0) []) = [bitBool.getD 1 (.const 0)] := by
  decide +kernel

/-- A limb that disagrees with its bits (`lo = 1`, all `lo` bits 0): the decode. -/
theorem nc_sp_decode : spFail (mkEnv ((lo, 1) :: s0) []) = [decode.getD 1 (.const 0)] := by decide +kernel

/-- The counter does not start at 0: `isFirstT·s`. -/
theorem nc_sp_ctr_start : spFail (mkEnv ((ctr, 3) :: (sid, 8) :: s0) []) = [counter (F := ℚ) 5 |>.getD 0 (.const 0)] := by
  decide +kernel

/-- The counter does not step: `(1 − isLastT)(next.s − s − 1)`. -/
theorem nc_sp_ctr_step : spFail (mkEnv ((isLT, 0) :: s0) s0) = [counter (F := ℚ) 5 |>.getD 1 (.const 0)] := by
  decide +kernel

end Split

/-! ## 3. Compute twin `ChipHX9` -/

section Compute
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9

/-- Rows of the twin as overrides of the existing honest `s10S` witness `witS10S`. -/
def hxEnv (o : List (ℕ × ℚ)) : Env ℚ := ⟨fun i => ((o ++ witListS10S).lookup i).getD 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- The arithmetic gates of the twin that do not vanish. -/
def hxFail (e : Env ℚ) : List (CoeffExpr ℚ) := arithGatesX9.filter fun g => evalQX g e ≠ 0

/-- Positive control (existing witness): no arithmetic gate fails. -/
theorem hx_honest : hxFail (hxEnv []) = [] := by decide +kernel

/-- `s10S` with `m = 63` (the `pw` wrap): the bits, products and labels are made consistent, so only
`s10S·aA·aB` fails. -/
def o63 : List (ℕ × ℚ) :=
  [(m0X, 1), (m1X, 1), (m2X, 1), (m3X, 1), (m4X, 1), (m5X, 1), (aAX, 1), (aBX, 1), (zAX, 0), (zBX, 0),
   (pw1X, 128), (pw2X, 2 ^ 56), (pwX, 2 ^ 64), (xF.v, 511), (axLX, 2 ^ 64 - 1), (kLabX, 3), (vLabX, 510)]

theorem nc_s10S_m63 :
    hxFail (hxEnv o63) = [prodL [cc sS10S, cc aAX, cc aBX]] := by decide +kernel

/-- Early segment termination: a `(0,1)` child claimed at `m = 1` (`zA = zB = 1`, label `(0, 1)`):
the `zA` definition gate `s10S·(zA − Π(1 − m_i))` (the `kN/vN` gates run through `zA·zB`). -/
def oEarly : List (ℕ × ℚ) :=
  [(m0X, 1), (zAX, 1), (zBX, 1), (kLabX, 0), (vLabX, 1), (pw1X, 2), (pw2X, 1), (pwX, 4), (xF.v, 449),
   (axLX, 3), (aAX, 0), (aBX, 0)]

theorem nc_s10S_early_stop :
    hxFail (hxEnv oEarly) = [.mul (cc sS10S) (.sub (cc zAX) (prodL [notC m0X, notC m1X, notC m2X]))] := by
  decide +kernel

/-- A kind-3 label that does not decode (`f.v ≠ 64·id + m`): the allowlisted decode gate. -/
theorem nc_s10S_decode : hxFail (hxEnv [(xF.v, 449)]) = [decodeG9] := by decide +kernel

/-! ### Any-env versions (every field, every row) -/

theorem nc_s0B_axis1 {F : Type} [Field F] {env : Env F} (hs : tr env sS0B = 1) (hz : tr env z1X = 1) :
    ¬ BaseHoldsX9 env := by
  intro hB
  have g := arith_of_base9 hB (g := .mul (cc sS0B) (cc z1X)) (by decide +kernel)
  simp [cc, evalQX, tr, hs, hz] at g

/-- `s10B` with a wrong routed label (`kR ≠ 3 − kb(f_tth)`). -/
theorem nc_s10B_label {F : Type} [Field F] {env : Env F} (hs : tr env sS10B = 1) (hk : tr env kLabX = 0)
    (hb : kbV env xFtth = 0) (h3 : (3 : F) ≠ 0) : ¬ BaseHoldsX9 env := by
  intro hB
  have g := arith_of_base9 hB (g := .mul (cc sS10B) (.add (.sub (cc kLabX) (.const 3)) (kbE xFtth)))
    (by decide +kernel)
  simp only [kbE, cc, evalQX, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero, tr] at g
  simp only [kbV] at hb
  simp only [tr] at hs hk
  rw [hs, hk, hb] at g
  apply h3
  linear_combination -g

/-- `s10S` with `m = 63` (both `aA = aB = 1`): the product `s10S·aA·aB` has value `1`, so the base constraints fail over every field `F`. -/
theorem nc_s10S_aAaB {F : Type} [Field F] {env : Env F} (hs : tr env sS10S = 1) (ha : tr env aAX = 1)
    (hb : tr env aBX = 1) : ¬ BaseHoldsX9 env := by
  intro hB
  have g := arith_of_base9 hB (g := prodL [cc sS10S, cc aAX, cc aBX]) (by decide +kernel)
  simp [prodL, cc, evalQX, tr, hs, ha, hb] at g

/-- A kind-3 formula on a NON-`s10S` row: the (relaxed-only-on-`s10S`) kind gate. -/
theorem nc_kind3_off_s10S {F : Type} [Field F] {env : Env F} (hs : tr env sS10S = 0) (hc : kcV env xF = 1)
    (hb : kbV env xF = 1) : ¬ BaseHoldsX9 env := by
  intro hB
  have g := arith_of_base9 hB (g := kindRelaxX9) (by decide +kernel)
  simp only [kindRelaxX9, oneMinus, kcE, kbE, cc, evalQX, Rat.cast_ofNat, Rat.cast_one, tr] at g
  simp only [kcV, kbV] at hc hb
  have hs' : env.trace sS10S = 0 := hs
  rw [hs', hc, hb] at g
  norm_num at g

/-- `s10S` serving a kind-0 (J-8 chain position) formula: `s10S·(xF.k − 2)(xF.k − 3)`. -/
theorem nc_s10S_kind0 {F : Type} [Field F] {env : Env F} (hs : tr env sS10S = 1) (hk : tr env xF.k = 0)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) : ¬ BaseHoldsX9 env := by
  intro hB
  have g := arith_of_base9 hB (g := svXFX9) (by decide +kernel)
  simp [svXFX9, svXF8, prodL, oneMinus, cc, evalQX, tr, hs, hk] at g
  rcases g with g | g
  · exact h2 g
  · exact h3 g

end Compute

-- AXIOMS-BEGIN
#print axioms ax_honest0
#print axioms ax_honest1
#print axioms nc_early_stop
#print axioms nc_skipped_row
#print axioms nc_tag_nonlast
#print axioms nc_chain_not_first
#print axioms nc_partial_at_end
#print axioms nc_z1a_l
#print axioms nc_z1a_offhead
#print axioms nc_hd_head
#print axioms nc_hd_nonhead
#print axioms nc_root_lie
#print axioms nc_R_change
#print axioms nc_hin_break
#print axioms nc_mod_p_emission
#print axioms nc_mod_p_emission_all
#print axioms nc_three_limb_emission
#print axioms sp_honest
#print axioms nc_sp_id
#print axioms nc_sp_hi_zero
#print axioms nc_sp_hi_zero_all
#print axioms nc_sp_bit
#print axioms nc_sp_decode
#print axioms nc_sp_ctr_start
#print axioms nc_sp_ctr_step
#print axioms hx_honest
#print axioms nc_s10S_m63
#print axioms nc_s10S_early_stop
#print axioms nc_s10S_decode
#print axioms nc_s0B_axis1
#print axioms nc_s10B_label
#print axioms nc_s10S_aAaB
#print axioms nc_kind3_off_s10S
#print axioms nc_s10S_kind0
-- AXIOMS-END

end

end Nock.RedTeam.Batch4857
