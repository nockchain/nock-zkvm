/-
  Nock/V1J8/GenExample.lean

  **The general tracegen on the example IS the example's input.**

  **`genJ8_example : genJ8 R0 1 s0 f0 χ = some (Example.honest χ)`** for every coin vector `χ`: the general J-8
  tracegen (`GenJ8.genJ8`, one pass over `genX`), run on `*[[0 0] [0 1]]`, produces exactly the input the exe checks
  by default (`Example.honest`, whose memory chips are the proved fills B4751-B4753 and whose compute base is
  `FillX.colXE = HonestCompX.colX`, B4750).  The proof goes chip by chip: the run, cell list and handle map (B4755),
  the multiplicities (`mv = (2, 1)`, `mx = (1, 0)`, `mh = (1, 1)`: small closed `decide`s over the one-row run), the
  compute table (`ρ₃` = the consumed record `(1, 0, 0, 0, 1)`, `ρ₄ = ρ_S = 0`, the walk values `(α, α, 0, 0)`), the
  cell table (242 columns × 2 rows, column ranges) and the walk table (166 columns); `K3` / `K6` identities through
  `toK` / `toQ`.
-/
import Nock.V1J8.GenJ8
import Nock.RedTeam.Batch4755Thm54TgJ8Gen

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.V1J8.GenEx

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base (s0 f0 c0 t0 R0 gen0)

theorem k3_ext {a b : K3} (h : K3.toK a = K3.toK b) : a = b := K3.toK_injective h

theorem k6_ext {a b : K6} (h1 : K3.toK a.re = K3.toK b.re) (h2 : K3.toK a.im = K3.toK b.im) : a = b := by
  cases a; cases b; simp only [K6.mk.injEq]; exact ⟨k3_ext h1, k3_ext h2⟩

theorem k6_ext' {a b : K6} (h : K6.toQ a = K6.toQ b) : a = b := by
  refine k6_ext ?_ ?_
  · rw [← Check.re_toQ, ← Check.re_toQ, h]
  · rw [← Check.im_toQ, ← Check.im_toQ, h]

theorem lq0 : lq 0 = 0 := rfl
theorem lq1 : lq 1 = 1 := rfl
theorem natG0 : natG 0 = 0 := rfl
theorem natG1 : natG 1 = 1 := rfl

theorem k6_sub_zero (a : K6) : a - 0 = a := k6_ext' (by rw [K6.toQ_sub, K6.toQ_zero, sub_zero])
theorem k6_zero_add (a : K6) : 0 + a = a := k6_ext' (by rw [K6.toQ_add, K6.toQ_zero, zero_add])
theorem k6_add_zero (a : K6) : a + 0 = a := k6_ext' (by rw [K6.toQ_add, K6.toQ_zero, add_zero])

section Cell
variable (χ : CoinsE)

abbrev cs0 : List Noun := [s0, f0]

theorem pE00 : (cellD (coOf χ) (yE χ) cs0 s0 0).pE = Cell.pE (coOf χ) 0 := by
  simp [cellD, encE, leafE, Cell.pE, atomFPE, Cell.aR, s0, hdN', tlN', lq, show (0 : ℕ) < p by decide]
theorem pE01 : (cellD (coOf χ) (yE χ) cs0 f0 1).pE = Cell.pE (coOf χ) 1 := by
  simp [cellD, encE, leafE, Cell.pE, atomFPE, Cell.aR, f0, hdN', tlN', lq, show (0 : ℕ) < p by decide,
    show (1 : ℕ) < p by decide]

theorem lE0 (n : Noun) (j : ℕ) (hn : n = s0 ∨ n = f0) :
    (cellD (coOf χ) (yE χ) cs0 n j).lE = Cell.lE (coOf χ) := by
  rcases hn with rfl | rfl <;>
  simp [cellD, encE, leafE, Cell.lE, atomFPE, s0, f0, hdN', lq, show (0 : ℕ) < p by decide]
theorem rE00 : (cellD (coOf χ) (yE χ) cs0 s0 0).rE = Cell.rE (coOf χ) 0 := by
  simp [cellD, encE, leafE, Cell.rE, atomFPE, Cell.aR, s0, tlN', lq, show (0 : ℕ) < p by decide]
theorem rE01 : (cellD (coOf χ) (yE χ) cs0 f0 1).rE = Cell.rE (coOf χ) 1 := by
  simp [cellD, encE, leafE, Cell.rE, atomFPE, Cell.aR, f0, tlN', lq, show (1 : ℕ) < p by decide]

theorem internal_s0 : s0.internal = 1 := by decide
theorem internal_f0 : f0.internal = 1 := by decide

theorem vInv00 : (cellD (coOf χ) (yE χ) cs0 s0 0).vInv = Cell.vInv (coOf χ) 0 := by
  have := pE00 χ
  simp only [cellD] at this ⊢
  rw [this, internal_s0]; rfl
theorem vInv01 : (cellD (coOf χ) (yE χ) cs0 f0 1).vInv = Cell.vInv (coOf χ) 1 := by
  have := pE01 χ
  simp only [cellD] at this ⊢
  rw [this, internal_f0]; rfl

theorem x0Inv00 : (cellD (coOf χ) (yE χ) cs0 s0 0).x0Inv = Cell.x0Inv (coOf χ) 0 := by
  have h1 := pE00 χ; have h2 := lE0 χ s0 0 (.inl rfl); have h3 := rE00 χ
  simp only [cellD] at h1 h2 h3 ⊢; rw [h1, h2, h3]; rfl
theorem x0Inv01 : (cellD (coOf χ) (yE χ) cs0 f0 1).x0Inv = Cell.x0Inv (coOf χ) 1 := by
  have h1 := pE01 χ; have h2 := lE0 χ f0 1 (.inr rfl); have h3 := rE01 χ
  simp only [cellD] at h1 h2 h3 ⊢; rw [h1, h2, h3]; rfl
theorem x1Inv00 : (cellD (coOf χ) (yE χ) cs0 s0 0).x1Inv = Cell.x1Inv (coOf χ) 0 := by
  have h1 := pE00 χ; have h2 := lE0 χ s0 0 (.inl rfl); have h3 := rE00 χ
  simp only [cellD] at h1 h2 h3 ⊢; rw [h1, h2, h3]; rfl
theorem x1Inv01 : (cellD (coOf χ) (yE χ) cs0 f0 1).x1Inv = Cell.x1Inv (coOf χ) 1 := by
  have h1 := pE01 χ; have h2 := lE0 χ f0 1 (.inr rfl); have h3 := rE01 χ
  simp only [cellD] at h1 h2 h3 ⊢; rw [h1, h2, h3]; rfl
theorem ivH00 : (cellD (coOf χ) (yE χ) cs0 s0 0).ivH = Cell.ivH (coOf χ) 0 := rfl
theorem ivH01 : (cellD (coOf χ) (yE χ) cs0 f0 1).ivH = Cell.ivH (coOf χ) 1 := rfl

abbrev mv' : Array ℕ := #[2, 1]
abbrev mx' : Array ℕ := #[1, 0]
abbrev mx1' : Array ℕ := Array.replicate 2 0
abbrev mh' : Array ℕ := #[1, 1]

theorem vT00 : vTermD mv' (cellD (coOf χ) (yE χ) cs0 s0 0) = Cell.vTerm (coOf χ) Example.mv 0 := by
  unfold vTermD; rw [show (cellD (coOf χ) (yE χ) cs0 s0 0).lInv = 0 from rfl,
    show (cellD (coOf χ) (yE χ) cs0 s0 0).rInv = 0 from rfl, k6_sub_zero, k6_sub_zero, vInv00]; rfl
theorem vT01 : vTermD mv' (cellD (coOf χ) (yE χ) cs0 f0 1) = Cell.vTerm (coOf χ) Example.mv 1 := by
  unfold vTermD; rw [show (cellD (coOf χ) (yE χ) cs0 f0 1).lInv = 0 from rfl,
    show (cellD (coOf χ) (yE χ) cs0 f0 1).rInv = 0 from rfl, k6_sub_zero, k6_sub_zero, vInv01]; rfl
theorem xT00 : xTermD mx' mx1' (cellD (coOf χ) (yE χ) cs0 s0 0) = Cell.xTerm (coOf χ) Example.mx Example.mx1 0 := by
  unfold xTermD; rw [x0Inv00, x1Inv00]; rfl
theorem xT01 : xTermD mx' mx1' (cellD (coOf χ) (yE χ) cs0 f0 1) = Cell.xTerm (coOf χ) Example.mx Example.mx1 1 := by
  unfold xTermD; rw [x0Inv01, x1Inv01]; rfl

theorem rankBit1 (k : ℕ) (hk : k < 110) : rankBit 1 k = if k = 0 then 1 else 0 := by
  interval_cases k <;> decide

theorem flagT : flag true = 1 := rfl
theorem flagF : flag false = 0 := rfl

abbrev d00 := cellD (coOf χ) (yE χ) cs0 s0 0

theorem hq00 (t : ℕ) : qslotD (d00 χ) (Cell.vAcc (coOf χ) Example.mv 0)
    (Cell.xAcc (coOf χ) Example.mx Example.mx1 0) t = Cell.qslot (coOf χ) Example.mv Example.mx Example.mx1 0 t := by
  match t with
  | 0 => exact congrArg FPE.size (pE00 χ)
  | 1 => exact congrArg FPE.dyck (pE00 χ)
  | 2 => exact congrArg FPE.leaf (pE00 χ)
  | 3 => exact congrArg FPE.size (lE0 χ s0 0 (.inl rfl))
  | 4 => exact congrArg FPE.dyck (lE0 χ s0 0 (.inl rfl))
  | 5 => exact congrArg FPE.leaf (lE0 χ s0 0 (.inl rfl))
  | 6 => exact congrArg FPE.size (rE00 χ)
  | 7 => exact congrArg FPE.dyck (rE00 χ)
  | 8 => exact congrArg FPE.leaf (rE00 χ)
  | 9 => exact vInv00 χ
  | 10 => rfl
  | 11 => rfl
  | 12 => exact x0Inv00 χ
  | 13 => rfl
  | 14 => rfl
  | n + 15 => exact x1Inv00 χ


abbrev LHS0 (c : ℕ) : ZMod P := cellColD 2 mv' mx' mx1' mh' (d00 χ)
      (Cell.vAcc (coOf χ) Example.mv 0) (Cell.xAcc (coOf χ) Example.mx Example.mx1 0) (Cell.avH (coOf χ) Example.mh 0) c
abbrev RHS0 (c : ℕ) : ZMod P := Cell.colZ (coOf χ) Example.mv Example.mx Example.mx1 Example.mh 0 c

theorem colA (c : ℕ) (hc : c < 18) : LHS0 χ c = RHS0 χ c := by
  have hmu : (d00 χ).mu = 1 := internal_s0
  have hj : (d00 χ).j = 0 := rfl
  have hmuL : (d00 χ).muL = 0 := rfl
  have hmuR : (d00 χ).muR = 0 := rfl
  interval_cases c <;> simp [cellColD, Cell.colZ, cellBaseD, Cell.baseZ, flag, hmu, hj, hmuL, hmuR, two62, atomV,
    Cell.aR] <;> rfl

theorem colB (c : ℕ) (h1 : 18 ≤ c) (h2 : c < 128) : LHS0 χ c = RHS0 χ c := by
  have hmu : (d00 χ).mu = 1 := internal_s0
  have hb : rankBit 1 (c - 18) = if c = 18 then 1 else 0 := by
    rw [rankBit1 _ (by omega)]; congr 1; simp; omega
  simp only [LHS0, RHS0, cellColD, Cell.colZ, cellBaseD, Cell.baseZ, hmu, hb,
    show ¬ c = 0 by omega, show ¬ c = 1 by omega, show c < 129 by omega,
    show ¬ c = 2 by omega, show ¬ c = 3 by omega, show ¬ c = 4 by omega, show ¬ c = 5 by omega,
    show ¬ c = 6 by omega, show ¬ c = 7 by omega, show ¬ c = 8 by omega, show ¬ c = 9 by omega,
    show ¬ c = 10 by omega, show ¬ c = 11 by omega, show ¬ c = 12 by omega, show ¬ c = 13 by omega,
    show ¬ c = 14 by omega, show ¬ c = 15 by omega, show ¬ c = 16 by omega, show ¬ c = 17 by omega,
    show ¬ c = 128 by omega, h2, h1, and_self, if_false, if_true]
  split_ifs <;> simp

theorem colC (c : ℕ) (h1 : 128 ≤ c) (h2 : c < 134) : LHS0 χ c = RHS0 χ c := by
  have hmuL : (d00 χ).muL = 0 := rfl
  have hmuR : (d00 χ).muR = 0 := rfl
  have hj : (d00 χ).j = 0 := rfl
  interval_cases c <;> simp [cellColD, Cell.colZ, cellBaseD, Cell.baseZ, hmuL, hmuR, hj, two62] <;> rfl

theorem colD (c : ℕ) (h1 : 134 ≤ c) (h2 : c < 230) : LHS0 χ c = RHS0 χ c := by
  simp only [LHS0, RHS0, cellColD, Cell.colZ, Cell.roleZ, show ¬ c = 0 by omega, show ¬ c = 1 by omega,
    show ¬ c < 129 by omega, show ¬ c = 129 by omega, show ¬ c < 132 by omega, show ¬ c = 132 by omega,
    show ¬ c = 133 by omega, show ¬ c < 134 by omega, h2, if_false, if_true, hq00]

theorem colE' (c : ℕ) (h1 : 230 ≤ c) (h2 : c < 242) : LHS0 χ c = RHS0 χ c := by
  have h7 := ivH00 χ
  simp only [LHS0, RHS0, cellColD, Cell.colZ, show ¬ c = 0 by omega, show ¬ c = 1 by omega,
    show ¬ c < 129 by omega, show ¬ c = 129 by omega, show ¬ c < 132 by omega, show ¬ c = 132 by omega,
    show ¬ c = 133 by omega, show ¬ c < 134 by omega, show ¬ c < 230 by omega, h2, if_false, if_true, h7]

abbrev d01 := cellD (coOf χ) (yE χ) cs0 f0 1

theorem hq01 (t : ℕ) : qslotD (d01 χ) (Cell.vAcc (coOf χ) Example.mv 1)
    (Cell.xAcc (coOf χ) Example.mx Example.mx1 1) t = Cell.qslot (coOf χ) Example.mv Example.mx Example.mx1 1 t := by
  match t with
  | 0 => exact congrArg FPE.size (pE01 χ)
  | 1 => exact congrArg FPE.dyck (pE01 χ)
  | 2 => exact congrArg FPE.leaf (pE01 χ)
  | 3 => exact congrArg FPE.size (lE0 χ f0 1 (.inr rfl))
  | 4 => exact congrArg FPE.dyck (lE0 χ f0 1 (.inr rfl))
  | 5 => exact congrArg FPE.leaf (lE0 χ f0 1 (.inr rfl))
  | 6 => exact congrArg FPE.size (rE01 χ)
  | 7 => exact congrArg FPE.dyck (rE01 χ)
  | 8 => exact congrArg FPE.leaf (rE01 χ)
  | 9 => exact vInv01 χ
  | 10 => rfl
  | 11 => rfl
  | 12 => exact x0Inv01 χ
  | 13 => rfl
  | 14 => rfl
  | n + 15 => exact x1Inv01 χ


abbrev LHS1 (c : ℕ) : ZMod P := cellColD 2 mv' mx' mx1' mh' (d01 χ)
      (Cell.vAcc (coOf χ) Example.mv 1) (Cell.xAcc (coOf χ) Example.mx Example.mx1 1) (Cell.avH (coOf χ) Example.mh 1) c
abbrev RHS1 (c : ℕ) : ZMod P := Cell.colZ (coOf χ) Example.mv Example.mx Example.mx1 Example.mh 1 c

theorem colA1 (c : ℕ) (hc : c < 18) : LHS1 χ c = RHS1 χ c := by
  have hmu : (d01 χ).mu = 1 := internal_f0
  have hj : (d01 χ).j = 1 := rfl
  have hmuL : (d01 χ).muL = 0 := rfl
  have hmuR : (d01 χ).muR = 0 := rfl
  interval_cases c <;> simp [cellColD, Cell.colZ, cellBaseD, Cell.baseZ, flag, hmu, hj, hmuL, hmuR, two62, atomV,
    Cell.aR] <;> rfl

theorem colB1 (c : ℕ) (h1 : 18 ≤ c) (h2 : c < 128) : LHS1 χ c = RHS1 χ c := by
  have hmu : (d01 χ).mu = 1 := internal_f0
  have hb : rankBit 1 (c - 18) = if c = 18 then 1 else 0 := by
    rw [rankBit1 _ (by omega)]; congr 1; simp; omega
  simp only [LHS1, RHS1, cellColD, Cell.colZ, cellBaseD, Cell.baseZ, hmu, hb,
    show ¬ c = 0 by omega, show ¬ c = 1 by omega, show c < 129 by omega,
    show ¬ c = 2 by omega, show ¬ c = 3 by omega, show ¬ c = 4 by omega, show ¬ c = 5 by omega,
    show ¬ c = 6 by omega, show ¬ c = 7 by omega, show ¬ c = 8 by omega, show ¬ c = 9 by omega,
    show ¬ c = 10 by omega, show ¬ c = 11 by omega, show ¬ c = 12 by omega, show ¬ c = 13 by omega,
    show ¬ c = 14 by omega, show ¬ c = 15 by omega, show ¬ c = 16 by omega, show ¬ c = 17 by omega,
    show ¬ c = 128 by omega, h2, h1, and_self, if_false, if_true]
  split_ifs <;> simp

theorem colC1 (c : ℕ) (h1 : 128 ≤ c) (h2 : c < 134) : LHS1 χ c = RHS1 χ c := by
  have hmuL : (d01 χ).muL = 0 := rfl
  have hmuR : (d01 χ).muR = 0 := rfl
  have hj : (d01 χ).j = 1 := rfl
  interval_cases c <;> simp [cellColD, Cell.colZ, cellBaseD, Cell.baseZ, hmuL, hmuR, hj, two62] <;> rfl

theorem colD1 (c : ℕ) (h1 : 134 ≤ c) (h2 : c < 230) : LHS1 χ c = RHS1 χ c := by
  simp only [LHS1, RHS1, cellColD, Cell.colZ, Cell.roleZ, show ¬ c = 0 by omega, show ¬ c = 1 by omega,
    show ¬ c < 129 by omega, show ¬ c = 129 by omega, show ¬ c < 132 by omega, show ¬ c = 132 by omega,
    show ¬ c = 133 by omega, show ¬ c < 134 by omega, h2, if_false, if_true, hq01]

theorem colE1 (c : ℕ) (h1 : 230 ≤ c) (h2 : c < 242) : LHS1 χ c = RHS1 χ c := by
  have h7 := ivH01 χ
  simp only [LHS1, RHS1, cellColD, Cell.colZ, show ¬ c = 0 by omega, show ¬ c = 1 by omega,
    show ¬ c < 129 by omega, show ¬ c = 129 by omega, show ¬ c < 132 by omega, show ¬ c = 132 by omega,
    show ¬ c = 133 by omega, show ¬ c < 134 by omega, show ¬ c < 230 by omega, h2, if_false, if_true, h7]

theorem row0 (c : ℕ) : (if c < 242 then LHS0 χ c else 0) = RHS0 χ c := by
  by_cases h : c < 242
  · rw [if_pos h]
    by_cases a : c < 18; · exact colA χ c a
    by_cases b : c < 128; · exact colB χ c (by omega) b
    by_cases d : c < 134; · exact colC χ c (by omega) d
    by_cases e : c < 230; · exact colD χ c (by omega) e
    exact colE' χ c (by omega) h
  · rw [if_neg h]; simp only [RHS0, Cell.colZ]
    simp only [show ¬ c = 0 by omega, show ¬ c = 1 by omega, show ¬ c < 129 by omega, show ¬ c = 129 by omega,
      show ¬ c < 134 by omega, show ¬ c < 230 by omega, show ¬ c < 233 by omega, show ¬ c < 236 by omega,
      show ¬ c < 239 by omega, h, if_false]

theorem row1 (c : ℕ) : (if c < 242 then LHS1 χ c else 0) = RHS1 χ c := by
  by_cases h : c < 242
  · rw [if_pos h]
    by_cases a : c < 18; · exact colA1 χ c a
    by_cases b : c < 128; · exact colB1 χ c (by omega) b
    by_cases d : c < 134; · exact colC1 χ c (by omega) d
    by_cases e : c < 230; · exact colD1 χ c (by omega) e
    exact colE1 χ c (by omega) h
  · rw [if_neg h]; simp only [RHS1, Cell.colZ]
    simp only [show ¬ c = 0 by omega, show ¬ c = 1 by omega, show ¬ c < 129 by omega, show ¬ c = 129 by omega,
      show ¬ c < 134 by omega, show ¬ c < 230 by omega, show ¬ c < 233 by omega, show ¬ c < 236 by omega,
      show ¬ c < 239 by omega, h, if_false]

theorem ofFn_getD {n : ℕ} (g : Fin n → ZMod P) (c : ℕ) :
    (Array.ofFn g).getD c 0 = if h : c < n then g ⟨c, h⟩ else 0 := by
  by_cases h : c < n
  · rw [dif_pos h]; simp [Array.getD, h]
  · rw [dif_neg h]; simp [Array.getD, h]

theorem rangeMap_getD {α : Type} (n : ℕ) (f : ℕ → Array α) (i : ℕ) (hi : i < n) :
    ((List.range n).map f).toArray.getD i #[] = f i := by
  simp [Array.getD, hi]

theorem cells_ds : (cs0.zipIdx 0).map (fun (x : Noun × ℕ) => cellD (coOf χ) (yE χ) cs0 x.1 x.2) = [d00 χ, d01 χ] := rfl

theorem scan2 (a b : K6) : scanK6 [a, b] = [0 + a, 0 + a + b] := rfl

theorem vAccs0 : scanK6 ([d00 χ, d01 χ].map (vTermD mv')) =
    [Cell.vAcc (coOf χ) Example.mv 0, Cell.vAcc (coOf χ) Example.mv 1] := by
  rw [List.map_cons, List.map_cons, List.map_nil, scan2, vT00, vT01, k6_zero_add]; rfl
theorem xAccs0 : scanK6 ([d00 χ, d01 χ].map (xTermD mx' mx1')) =
    [Cell.xAcc (coOf χ) Example.mx Example.mx1 0, Cell.xAcc (coOf χ) Example.mx Example.mx1 1] := by
  rw [List.map_cons, List.map_cons, List.map_nil, scan2, xT00, xT01, k6_zero_add]; rfl
theorem hAccs0 : scanK6 ([d00 χ, d01 χ].map (hTermD mh')) =
    [Cell.avH (coOf χ) Example.mh 0, Cell.avH (coOf χ) Example.mh 1] := by
  rw [List.map_cons, List.map_cons, List.map_nil, scan2, k6_zero_add]; rfl

theorem cellGen_cols :
    colsOf (cellGen (coOf χ) (yE χ) cs0 mv' mx' mx1' mh').1 2 = Cell.cols (coOf χ) Example.mv Example.mx Example.mx1 Example.mh := by
  funext c i
  have hlen : cs0.length = 2 := rfl
  simp only [colsOf, cellGen, cells_ds, vAccs0, xAccs0, hAccs0, hlen]
  rw [rangeMap_getD _ _ _ i.isLt, ofFn_getD]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.val_zero, List.getD_cons_zero, Fin.val_mk, dite_eq_ite, Cell.cols]
    exact row0 χ c
  · simp only [Fin.mk_one, Fin.val_one, List.getD_cons_succ, List.getD_cons_zero, Fin.val_mk, dite_eq_ite,
      Cell.cols]
    exact row1 χ c

theorem cellGen_pubs :
    (cellGen (coOf χ) (yE χ) cs0 mv' mx' mx1' mh').2 = Cell.pubs (coOf χ) Example.mv Example.mx Example.mx1 Example.mh := by
  funext j
  simp only [cellGen, cells_ds, vAccs0, xAccs0, hAccs0, lastK6, Cell.pubs]
  rfl
end Cell

section Walk
variable (χ : CoinsE)

def w0 : WRow := ⟨s0, s0, 1, 0, false, false, 0, 0⟩
abbrev e0 := walkD (coOf χ) (yE χ) cs0 w0 0
abbrev αW := chalsMJ8E χ 0

theorem wpE : (e0 χ).pE = Walk.pE (coOf χ) := by
  simp [walkD, w0, encE, leafE, Walk.pE, atomFPE, s0, lq, show (0 : ℕ) < p by decide]
theorem wlE : (e0 χ).lE = Walk.lE (coOf χ) := by
  simp [walkD, w0, encE, leafE, Walk.lE, atomFPE, s0, hdN', lq, show (0 : ℕ) < p by decide]
theorem wrE : (e0 χ).rE = Walk.lE (coOf χ) := by
  simp [walkD, w0, encE, leafE, Walk.lE, atomFPE, s0, tlN', lq, show (0 : ℕ) < p by decide]
theorem wroot : (e0 χ).rootE = Walk.pE (coOf χ) := by
  simp [walkD, w0, encE, leafE, Walk.pE, atomFPE, s0, lq, show (0 : ℕ) < p by decide]
theorem wxInv : (e0 χ).xInv = Walk.xInv (coOf χ) := by
  have h1 := wpE χ; have h2 := wlE χ; have h3 := wrE χ
  simp only [walkD] at h1 h2 h3 ⊢; rw [h1, h2, h3]; rfl
theorem wpInvL : (e0 χ).pInvL = Walk.pInvL (coOf χ) := by
  have h1 := wroot χ; have h2 := wlE χ
  simp only [walkD] at h1 h2 ⊢; rw [h1, h2]; rfl
theorem wpInvR : (e0 χ).pInvR = Walk.pInvR (coOf χ) := by
  have h1 := wroot χ; have h2 := wrE χ
  simp only [walkD] at h1 h2 ⊢; rw [h1, h2]; rfl
theorem whX : (e0 χ).hXi = (Walk.hX (coOf χ))⁻¹ := rfl
theorem whPL : (e0 χ).hPLi = (Walk.hPL (coOf χ))⁻¹ := rfl
theorem whPR : (e0 χ).hPRi = (Walk.hPR (coOf χ))⁻¹ := rfl

theorem k3_mul_one (a : K3) : a * CompX.powK a 0 = a := k3_ext (by rw [K3.toK_mul, CompX.toK_powK]; ring)
theorem k3_pow1_mul_pow0 (a : K3) : CompX.powK a 1 * CompX.powK a 0 = a :=
  k3_ext (by rw [K3.toK_mul, CompX.toK_powK, CompX.toK_powK]; ring)
theorem k3_mul_zero (a : K3) : a * 0 = (0 : K3) := k3_ext (by rw [K3.toK_mul, K3.toK_zero, mul_zero])

theorem wfp (s : ℕ) : fpD (e0 χ) s = Walk.fpSlot (coOf χ) s := by
  match s with
  | 0 => exact congrArg FPE.size (wpE χ)
  | 1 => exact congrArg FPE.dyck (wpE χ)
  | 2 => exact congrArg FPE.leaf (wpE χ)
  | 3 => exact congrArg FPE.size (wlE χ)
  | 4 => exact congrArg FPE.dyck (wlE χ)
  | 5 => exact congrArg FPE.leaf (wlE χ)
  | 6 => exact congrArg FPE.size (wrE χ)
  | 7 => exact congrArg FPE.dyck (wrE χ)
  | 8 => exact congrArg FPE.leaf (wrE χ)
  | 9 => exact congrArg FPE.size (wroot χ)
  | 10 => exact congrArg FPE.dyck (wroot χ)
  | n + 11 => exact congrArg FPE.leaf (wroot χ)

theorem wio (s : ℕ) : ioD (e0 χ) (Walk.xInv (coOf χ)) (Walk.pAcc (coOf χ) 0 0) s = Walk.ioSlot (coOf χ) 0 0 s := by
  match s with
  | 0 => exact wxInv χ
  | 1 => exact wpInvL χ
  | 2 => exact wpInvR χ
  | 3 => rfl
  | n + 4 => rfl

theorem whs (s : ℕ) : hsD (e0 χ) (Walk.hX (coOf χ))⁻¹ (Walk.hPA (coOf χ) 0 0) s = Walk.hslot (coOf χ) 0 0 s := by
  match s with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n + 4 => rfl

theorem wrole0 (ρ : ℕ) : wroleD (e0 χ) (αW χ) (αW χ) 0 (Walk.xInv (coOf χ)) (Walk.pAcc (coOf χ) 0 0) ρ =
    Walk.wrole (coOf χ) (αW χ) 0 0 ρ := by
  unfold wroleD Walk.wrole
  split_ifs <;> simp only [wfp, wio]

abbrev WL (c : ℕ) : ZMod P := walkColD (hdl cs0) 1 1 0 (e0 χ) (αW χ) (αW χ) 0 (Walk.xInv (coOf χ))
  (Walk.pAcc (coOf χ) 0 0) (Walk.hX (coOf χ))⁻¹ (Walk.hPA (coOf χ) 0 0) c

theorem wcolA (c : ℕ) (hc : c < 25) : WL χ c = Walk.colZ (coOf χ) (αW χ) 0 0 c := by
  interval_cases c <;> simp [walkColD, Walk.colZ, flag, w0, certB, Nock.NockVMROM.Thm54.VclL.Handle.HonestK8.certB8, Nock.NockVMROM.Thm54.VclL.Handle.HonestK8.top8,
    Nock.NockVMROM.Thm54.VclL.Handle.HonestK8.rem8, walkD, idxN, Gen.hdl, s0, hdN', tlN'] <;> rfl

theorem wcolB (c : ℕ) (h1 : 25 ≤ c) (h2 : c < 136) : WL χ c = Walk.colZ (coOf χ) (αW χ) 0 0 c := by
  simp only [WL, walkColD, Walk.colZ, show ¬ c = 0 by omega, show ¬ c = 1 by omega, show ¬ c = 2 by omega,
    show ¬ c = 3 by omega, show ¬ c = 4 by omega, show ¬ c = 5 by omega, show ¬ c = 6 by omega,
    show ¬ c = 7 by omega, show ¬ c = 8 by omega, show ¬ c = 9 by omega, show ¬ c = 10 by omega,
    show ¬ c = 11 by omega, show ¬ c = 12 by omega, show ¬ c = 13 by omega, show ¬ c = 14 by omega,
    show ¬ c < 21 by omega, show ¬ c = 21 by omega, show ¬ c = 22 by omega, show ¬ c = 23 by omega,
    show ¬ c = 24 by omega, show ¬ c < 3 by omega, show ¬ c < 14 by omega, show ¬ c < 25 by omega, h2,
    if_false, if_true, wrole0]

theorem wcolC (c : ℕ) (h1 : 136 ≤ c) (h2 : c < 166) : WL χ c = Walk.colZ (coOf χ) (αW χ) 0 0 c := by
  simp only [WL, walkColD, Walk.colZ, Walk.hrole, show ¬ c = 0 by omega, show ¬ c = 1 by omega,
    show ¬ c = 2 by omega,
    show ¬ c = 3 by omega, show ¬ c = 4 by omega, show ¬ c = 5 by omega, show ¬ c = 6 by omega,
    show ¬ c = 7 by omega, show ¬ c = 8 by omega, show ¬ c = 9 by omega, show ¬ c = 10 by omega,
    show ¬ c = 11 by omega, show ¬ c = 12 by omega, show ¬ c = 13 by omega, show ¬ c = 14 by omega,
    show ¬ c < 21 by omega, show ¬ c = 21 by omega, show ¬ c = 22 by omega, show ¬ c = 23 by omega,
    show ¬ c = 24 by omega, show ¬ c < 3 by omega, show ¬ c < 14 by omega, show ¬ c < 25 by omega,
    show ¬ c < 136 by omega, h2, if_false, if_true, whs]

theorem wrow (c : ℕ) : (if c < 166 then WL χ c else 0) = Walk.colZ (coOf χ) (αW χ) 0 0 c := by
  by_cases h : c < 166
  · rw [if_pos h]
    by_cases a : c < 25; · exact wcolA χ c a
    by_cases b : c < 136; · exact wcolB χ c (by omega) b
    exact wcolC χ c (by omega) h
  · rw [if_neg h]; simp only [Walk.colZ]
    simp only [show ¬ c < 3 by omega, show ¬ c = 4 by omega, show ¬ c = 10 by omega, show ¬ c = 11 by omega,
      show ¬ c < 14 by omega, show ¬ c < 21 by omega, show ¬ c < 25 by omega, show ¬ c < 136 by omega, h, if_false]

theorem scan1 (a : K6) : scanK6 [a] = [0 + a] := rfl

theorem lca0 (cu : List K3) :
    walkLCA (αW χ) 1 [0] (childSums (αW χ) 1 [0] cu.toArray) cu = [(αW χ, αW χ, 0)] := by
  simp only [walkLCA, childSums, List.foldl_cons, List.foldl_nil, List.range_zero, List.map_nil, List.zip_cons_cons,
    List.zip_nil_left, List.zipIdx_cons, List.zipIdx_nil, ↓reduceIte, List.nil_append, k3_pow1_mul_pow0, k3_mul_zero]

theorem walkGen_cols :
    colsOf (walkGenRows (coOf χ) (yE χ) (αW χ) (chalsMJ8E χ 1) cs0 [w0] 1).1 1 = Walk.cols (coOf χ) (αW χ) 0 0 := by
  funext c i
  have hfo : foW w0 = 0 := rfl
  have hsc : scanN [0] = [0] := rfl
  simp only [colsOf, walkGenRows, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, lca0, scan1,
    k6_zero_add, List.length_cons, List.length_nil, hfo, hsc, List.getD_cons_zero, Nat.zero_add]
  rw [rangeMap_getD _ _ _ i.isLt, ofFn_getD]
  fin_cases i
  simp only [Fin.zero_eta, List.getD_cons_zero, dite_eq_ite, Walk.cols]
  convert wrow χ c using 2
  all_goals rfl

theorem walkGen_pubs :
    (walkGenRows (coOf χ) (yE χ) (αW χ) (chalsMJ8E χ 1) cs0 [w0] 1).2 = Walk.pubs (coOf χ) 0 0 := by
  funext j
  simp only [walkGenRows, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, scan1, k6_zero_add,
    lastK6, Walk.pubs]
  rw [show (List.getLastD [(e0 χ).xInv] 0) = (e0 χ).xInv from rfl, wxInv]
  rfl
end Walk
abbrev b0 : ℕ → ZMod P := baseFn (InhabJ8MemDom.H0 Nock.Field.p) 1 0 InhabJ8Comp.r0

theorem b0_eq : b0 = Example.base0 := rfl
theorem consX0 : consOf b0 .x = [[1, 0, 0, 0, 1]] := by decide
theorem consP0 : consOf b0 .p = [] := by decide
theorem actsS0 : actsOf b0 .s = [0, 0, 0, 0] := by decide

abbrev RnEx : RunX := ⟨t0, s0, [t0], #[InhabJ8Comp.r0]⟩
abbrev clEx : P8PublicClaim := ⟨s0, f0, s0⟩
abbrev H0 := InhabJ8MemDom.H0 Nock.Field.p

theorem bs0 : basesOf H0 RnEx = [b0] := rfl

theorem recTot0 (χ : CoinsE) : recTot 5 χ [[1, 0, 0, 0, 1]] = Example.ρ3E χ := by
  unfold recTot; rw [List.foldr_cons, List.foldr_nil, k6_add_zero]; rfl

theorem rho0 (χ : CoinsE) : rhoOfB χ [b0] = Example.ρE χ := by
  funext i
  simp only [rhoOfB, List.flatMap_cons, List.flatMap_nil, List.append_nil, consX0, consP0, recTot0]
  unfold Example.ρE
  split_ifs <;> rfl

theorem termS0 (iv : Array K6) (i : ℕ) (h1 : 12 ≤ i) (h2 : i < 18) : (termRow b0 iv).getD i 0 = 0 := by
  unfold termRow
  rw [ofFn_getD, dif_pos h2]
  have ha : (accSpecE (i / 3)).1 = .s := by
    have : i / 3 = 4 ∨ i / 3 = 5 := by omega
    rcases this with h | h <;> rw [h] <;> rfl
  simp only [ha, actsS0]
  simp

theorem tot0 (t : Array (ZMod P)) (i : ℕ) (hi : i < 18) :
    (prefixSums 18 [t]).2.getD i 0 = 0 + t.getD i 0 := by
  simp only [prefixSums, List.foldl_cons, List.foldl_nil]
  rw [ofFn_getD, dif_pos hi]
  simp [Array.getD, hi]

theorem rhoS0 (χ : CoinsE) (c : P8PublicClaim) (m : FrameVS.ClaimMsgVS) (ρ : Fin 5 → K6) :
    rhoSOf c m ρ χ [b0] = 0 := by
  simp only [rhoSOf, List.map_cons, List.map_nil, CompX.readK]
  rw [tot0 _ 12 (by decide), tot0 _ 13 (by decide), tot0 _ 14 (by decide), tot0 _ 15 (by decide),
    tot0 _ 16 (by decide), tot0 _ 17 (by decide), termS0 _ 12 (by decide) (by decide),
    termS0 _ 13 (by decide) (by decide), termS0 _ 14 (by decide) (by decide), termS0 _ 15 (by decide) (by decide),
    termS0 _ 16 (by decide) (by decide), termS0 _ 17 (by decide) (by decide), add_zero]
  rfl

theorem k3_inv0 (a : K3) : (a - a)⁻¹ = (0 : K3) :=
  k3_ext (by rw [K3.toK_inv, K3.toK_sub, sub_self, inv_zero, K3.toK_zero])

theorem wv0 (α γ : K3) : walkVals H0 [t0] α γ = [(α, α, 0, 0)] := by
  have hch : t0.children = [] := rfl
  simp only [walkVals, List.foldl_cons, List.foldl_nil, hch, List.length_nil, List.zipIdx_nil, ↓reduceIte,
    List.nil_append, k3_mul_one, k3_mul_zero, k3_inv0]

theorem ofFn_getDK {n : ℕ} (g : Fin n → K6) (c : ℕ) :
    (Array.ofFn g).getD c 0 = if h : c < n then g ⟨c, h⟩ else 0 := by
  by_cases h : c < n
  · rw [dif_pos h]; simp [Array.getD, h]
  · rw [dif_neg h]; simp [Array.getD, h]

theorem acc0 (t : Array (ZMod P)) : (prefixSums 18 [t]).1 = [Array.replicate 18 0] := rfl

abbrev pubEx (χ : CoinsE) : ℕ → ZMod P := pubVJ8E c0 Example.mC (Example.ρE χ) 0 χ

theorem compCol0 (χ : CoinsE) (c : ℕ) (hc : c < 123) :
    compColD b0 (invsOf (envX b0 (pubEx χ) χ)) (Array.replicate 18 0) (χ ⟨13, by decide⟩, χ ⟨13, by decide⟩, 0, 0) c
      = Example.colE (pubEx χ) χ c := by
  unfold compColD Example.colE
  by_cases h1 : c < 69
  · simp only [h1, if_true]; rfl
  by_cases h2 : c < 93
  · simp only [h1, h2, if_true, if_false, invsOf]
    rw [ofFn_getDK, dif_pos (by omega)]
    rfl
  by_cases h3 : c < 111
  · simp only [h1, h2, h3, if_true, if_false]
    simp [Array.getD]
  · simp only [h1, h2, h3, hc, if_true, if_false]
    split_ifs <;> rfl

theorem compTable0 (χ : CoinsE) :
    colsOf (compTable H0 RnEx (pubEx χ) χ [b0]) 1 = Example.colsX χ := by
  funext c i
  fin_cases i
  simp only [colsOf, compTable, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left, acc0, wv0,
    show RnEx.rows.size = 1 from rfl, show RnEx.W = [t0] from rfl]
  rw [rangeMap_getD _ _ 0 (by decide), ofFn_getD]
  simp only [List.getD_cons_zero, Example.colsX]
  by_cases hc : c < 123
  · rw [dif_pos hc]; exact compCol0 χ c hc
  · rw [dif_neg hc]; unfold Example.colE
    simp only [show ¬ c < 69 by omega, show ¬ c < 93 by omega, show ¬ c < 111 by omega, hc, if_false]

/-! ## The assembly -/

abbrev r0 := InhabJ8Comp.r0

theorem run0 : runX R0 1 s0 f0 = some RnEx := Nock.RedTeam.Batch4755.run_example
theorem small0 : smallAtoms #[r0] = true := by decide
theorem nojet0 : noJets #[r0] = true := by decide
theorem cells0 : cellsOfRoots (rootsOf clEx #[r0]) = cs0 := by decide
theorem walk0 : walkGen s0 (pathReads #[r0]) = ([w0], 1) := by decide
theorem mv0 : mvCounts cs0 clEx = mv' := by decide
theorem mx0 : mxCounts cs0 [w0] = mx' := by decide
theorem mh0 : mhCounts cs0 [b0] [w0] = mh' := by decide

theorem compGen_ρ (χ : CoinsE) : (compGen clEx H0 RnEx χ).ρ = Example.ρE χ := rho0 χ
theorem compGen_ρS (χ : CoinsE) : (compGen clEx H0 RnEx χ).ρS = 0 := rhoS0 χ _ _ _
theorem compGen_bases (χ : CoinsE) : (compGen clEx H0 RnEx χ).bases = [b0] := rfl
theorem compGen_size (χ : CoinsE) : (compGen clEx H0 RnEx χ).rows.size = 1 := by
  simp [compGen, compTable]
theorem compGen_cols (χ : CoinsE) : colsOf (compGen clEx H0 RnEx χ).rows 1 = Example.colsX χ := by
  show colsOf (compTable H0 RnEx (pubVJ8E clEx (mOf clEx H0) (rhoOfB χ [b0]) (rhoSOf clEx (mOf clEx H0)
    (rhoOfB χ [b0]) χ [b0]) χ) χ [b0]) 1 = _
  rw [rhoS0, rho0]
  exact compTable0 χ

theorem cellGen_size (χ : CoinsE) : (cellGen (coOf χ) (yE χ) cs0 mv' mx' mx1' mh').1.size = 2 := by
  simp [cellGen]
theorem walkGen_size (χ : CoinsE) :
    (walkGenRows (coOf χ) (yE χ) (αW χ) (chalsMJ8E χ 1) cs0 [w0] 1).1.size = 1 := by
  simp [walkGenRows]

theorem chipOf_eq (tbl : Array (Array (ZMod P))) (n : ℕ) (f : ℕ → Fin n → ZMod P) (hs : tbl.size = n)
    (hc : colsOf tbl n = f) : chipOf tbl = ⟨hOf n, n, ωOf (hOf n), f⟩ := by
  subst hs; subst hc; rfl

theorem hOf1 : hOf 1 = 1 := rfl
theorem hOf2 : hOf 2 = 1 := rfl
theorem ωOf1 : ωOf 1 = Example.ω6g := rfl

/-- **The general J-8 tracegen on the example is the example's input**, at every coin vector. -/
theorem genJ8_example (χ : CoinsE) : genJ8 R0 1 s0 f0 χ = some (Example.honest χ) := by
  simp only [genJ8, run0, small0, nojet0, Bool.and_self, Bool.not_true]
  rw [cells0, Nock.RedTeam.Batch4755.hdl_example]
  simp only [List.headD_cons, Bool.false_eq_true, ↓reduceIte]
  rw [walk0]
  simp only [compGen_bases, mv0, mx0, mh0, show cs0.length = 2 from rfl]
  rw [show Array.replicate 2 0 = mx1' from rfl]
  rw [chipOf_eq _ 1 _ (compGen_size χ) (compGen_cols χ), chipOf_eq _ 2 _ (cellGen_size χ) (cellGen_cols χ),
    chipOf_eq _ 1 _ (walkGen_size χ) (walkGen_cols χ)]
  simp only [cellGen_pubs, walkGen_pubs, compGen_ρ, compGen_ρS, hOf1, hOf2, ωOf1]
  rfl

end Nock.V1J8.GenEx
