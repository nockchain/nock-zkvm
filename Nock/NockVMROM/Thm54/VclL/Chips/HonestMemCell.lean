/-
  Nock/NockVMROM/Thm54/VclL/Chips/HonestMemCell.lean

  **The honest cell-table columns and the base gates.**

  `CellVals F Q` is the committed content of one cell row (`F` scalars, `Q = 𝕂′` fingerprints and
  inverses).  `cellCol δF b vals` lays rows out in the chip's `225` columns (`Layout`: base `0..128`
  = masks, `idx … mx`, the `110` rank bits at `18…127`, `mx1` at `128`; `𝕂`-role `ρ` at columns
  `129 + 3ρ + k` holding the `k`-th coordinate of `roleVal`).  `cell_base_gates_hold`: the `123` base
  gates vanish at the environment of `honestQ … (cellCol …)` given the row-level facts
  `CellBaseFacts` (serial, limbs, booleans, bit decompositions, atom pins) — the exact converse
  of `cellRow_gates`'s base half.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemQ
import Nock.NockVMROM.Thm54.VclL.Chips.QEval

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.T0Tower
open Module
open scoped Polynomial

noncomputable section

/-- **The committed content of one cell row.**  `bit k` is the `k`-th rank bit (`k < 110`:
`0…61` of `lo`, `62…109` of `hi`). -/
structure CellVals (F Q : Type) where
  idx : F
  idL : F
  idR : F
  wL : F
  wR : F
  aL : F
  aR : F
  lo : F
  hi : F
  loL : F
  hiL : F
  loR : F
  hiR : F
  carry : F
  mv : F
  mx : F
  mx1 : F
  bit : ℕ → F
  p : ComputeTable.FP Q
  l : ComputeTable.FP Q
  r : ComputeTable.FP Q
  vInv : Q
  lInv : Q
  rInv : Q
  x0Inv : Q
  x1Inv : Q
  vAcc : Q
  xAcc : Q

namespace CellVals
variable {F Q : Type}

/-- The base-field column `j` (`2 ≤ j < 129`; columns `0`, `1` are the masks). -/
def base (v : CellVals F Q) (j : ℕ) : F :=
  if j = 2 then v.idx else if j = 3 then v.idL else if j = 4 then v.idR
  else if j = 5 then v.wL else if j = 6 then v.wR else if j = 7 then v.aL
  else if j = 8 then v.aR else if j = 9 then v.lo else if j = 10 then v.hi
  else if j = 11 then v.loL else if j = 12 then v.hiL else if j = 13 then v.loR
  else if j = 14 then v.hiR else if j = 15 then v.carry else if j = 16 then v.mv
  else if j = 17 then v.mx else if j = 128 then v.mx1 else v.bit (j - 18)

/-- The `𝕂′`-valued entry of `𝕂′`-slot `s` (`0…8` the fingerprint entries `p l r` as
`size dyck leaf`, `9…15` the B2 values; Re at role `2s`, Im at role `2s + 1`). -/
def qslot (v : CellVals F Q) : ℕ → Q
  | 0 => v.p.size | 1 => v.p.dyck | 2 => v.p.leaf
  | 3 => v.l.size | 4 => v.l.dyck | 5 => v.l.leaf
  | 6 => v.r.size | 7 => v.r.dyck | 8 => v.r.leaf
  | 9 => v.vInv | 10 => v.lInv | 11 => v.rInv | 12 => v.x0Inv | 13 => v.vAcc | 14 => v.xAcc
  | _ => v.x1Inv

end CellVals


section Cols
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K)

/-- The `𝕂`-role `ρ` of a row: Re / Im of the `𝕂′` slot `ρ / 2`. -/
def roleVal (v : CellVals F (Quad (algebraMap F K δF))) (ρ : ℕ) : K :=
  if ρ % 2 = 0 then Quad.re _ (v.qslot (ρ / 2)) else Quad.im _ (v.qslot (ρ / 2))

/-- **The cell table's column function**: base columns `2 … 128` from `CellVals.base`, `𝕂`-role `ρ`
at `129 + 3ρ + k` holding coordinate `k`. -/
def cellCol {n : ℕ} (vals : Fin n → CellVals F (Quad (algebraMap F K δF))) (j : ℕ) (i : Fin n) : F :=
  if j < 129 then (vals i).base j
  else coord b (roleVal δF (vals i) ((j - 129) / 3)) ⟨(j - 129) % 3, Nat.mod_lt _ (by norm_num)⟩

end Cols

section BaseGates
variable {F : Type} [Field F] {Q : Type}

/-- **The row-level facts the `123` base gates encode** (at row `i` of `vals`; `next` is the row
`i + 1` when it exists). -/
structure CellBaseFacts {n : ℕ} (vals : Fin n → CellVals F Q) (i : Fin n) : Prop where
  serial0 : (i : ℕ) = 0 → (vals i).idx = 0
  serialStep : ∀ hi : (i : ℕ) + 1 < n, (vals ⟨(i : ℕ) + 1, hi⟩).idx = (vals i).idx + 1
  limbLo : (vals i).lo + (2 : F) ^ 62 * (vals i).carry = (vals i).loL + (vals i).loR + 1
  limbHi : (vals i).hi = (vals i).hiL + (vals i).hiR + (vals i).carry
  carry_bool : (vals i).carry * ((vals i).carry - 1) = 0
  wL_bool : (vals i).wL * ((vals i).wL - 1) = 0
  wR_bool : (vals i).wR * ((vals i).wR - 1) = 0
  lo_bits : (vals i).lo = ∑ k ∈ Finset.range 62, (2 : F) ^ k * (vals i).bit k
  hi_bits : (vals i).hi = ∑ k ∈ Finset.range 48, (2 : F) ^ k * (vals i).bit (62 + k)
  bit_bool : ∀ k < 110, (vals i).bit k * ((vals i).bit k - 1) = 0
  atomL : (vals i).wL = 0 → (vals i).loL = 0 ∧ (vals i).hiL = 0
  atomR : (vals i).wR = 0 → (vals i).loR = 0 ∧ (vals i).hiR = 0


variable {K : Type} [Field K] [Algebra F K] [Fintype K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (ω : F) (chv pbv : ℕ → F)
  (vals : Fin n → CellVals F (Quad (algebraMap F K δF)))

/-- The honest cell trace. -/
abbrev honestCellQ : Fin 225 → F[X] := honestQ hn nodes (cellCol δF b vals) 225

theorem cellEnv_base (hinj : Function.Injective nodes) (i : Fin n) {j : ℕ} (h2 : 2 ≤ j) (hj : j < 129) :
    (Reify.envOfTrace (honestCellQ δF b hn nodes vals) ω (nodes i) chv pbv).trace j =
      (vals i).base j := by
  rw [env_trace hn nodes hinj _ ω chv pbv i (show j < 225 by omega)]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  simp [fullCol, h0, h1, cellCol, hj]

theorem cellEnv_mask0 (hinj : Function.Injective nodes) (i : Fin n) :
    (Reify.envOfTrace (honestCellQ δF b hn nodes vals) ω (nodes i) chv pbv).trace 0 =
      if (i : ℕ) = 0 then 1 else 0 := by
  rw [env_trace hn nodes hinj _ ω chv pbv i (show 0 < 225 by omega)]
  simp [fullCol]

theorem cellEnv_mask1 (hinj : Function.Injective nodes) (i : Fin n) :
    (Reify.envOfTrace (honestCellQ δF b hn nodes vals) ω (nodes i) chv pbv).trace 1 =
      if i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0 := by
  rw [env_trace hn nodes hinj _ ω chv pbv i (show 1 < 225 by omega)]
  simp [fullCol]

theorem cellEnv_next_base (hinj : Function.Injective nodes) (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω) (i : Fin n) (hi : (i : ℕ) + 1 < n) {j : ℕ} (h2 : 2 ≤ j) (hj : j < 129) :
    (Reify.envOfTrace (honestCellQ δF b hn nodes vals) ω (nodes i) chv pbv).traceNext j =
      (vals ⟨(i : ℕ) + 1, hi⟩).base j := by
  rw [env_traceNext hn nodes hinj _ ω chv pbv hadj i hi (show j < 225 by omega)]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  simp [fullCol, h0, h1, cellCol, hj]

/-- **The `123` base gates vanish at the honest environment of row `i`.** -/
theorem cell_base_gates_hold (hinj : Function.Injective nodes) (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω) (i : Fin n) (hf : CellBaseFacts vals i) :
    ∀ g ∈ Cell.baseGates (F := F),
      g.eval (Reify.envOfTrace (honestCellQ δF b hn nodes vals) ω (nodes i) chv pbv) = 0 := by
  set E := Reify.envOfTrace (honestCellQ δF b hn nodes vals) ω (nodes i) chv pbv with hE
  have hb : ∀ j, 2 ≤ j → j < 129 → E.trace j = (vals i).base j := fun j h2 hj =>
    cellEnv_base δF b hn nodes ω chv pbv vals hinj i h2 hj
  have m0 : E.trace 0 = if (i : ℕ) = 0 then 1 else 0 := cellEnv_mask0 δF b hn nodes ω chv pbv vals hinj i
  have m1 : E.trace 1 = if i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0 := cellEnv_mask1 δF b hn nodes ω chv pbv vals hinj i
  have t2 : E.trace 2 = (vals i).idx := by rw [hb 2 le_rfl (by norm_num)]; simp [CellVals.base]
  have t5 : E.trace 5 = (vals i).wL := by rw [hb 5 (by norm_num) (by norm_num)]; simp [CellVals.base]
  have t6 : E.trace 6 = (vals i).wR := by rw [hb 6 (by norm_num) (by norm_num)]; simp [CellVals.base]
  have t9 : E.trace 9 = (vals i).lo := by rw [hb 9 (by norm_num) (by norm_num)]; simp [CellVals.base]
  have t10 : E.trace 10 = (vals i).hi := by rw [hb 10 (by norm_num) (by norm_num)]; simp [CellVals.base]
  have t11 : E.trace 11 = (vals i).loL := by rw [hb 11 (by norm_num) (by norm_num)]; simp [CellVals.base]
  have t12 : E.trace 12 = (vals i).hiL := by rw [hb 12 (by norm_num) (by norm_num)]; simp [CellVals.base]
  have t13 : E.trace 13 = (vals i).loR := by rw [hb 13 (by norm_num) (by norm_num)]; simp [CellVals.base]
  have t14 : E.trace 14 = (vals i).hiR := by rw [hb 14 (by norm_num) (by norm_num)]; simp [CellVals.base]
  have t15 : E.trace 15 = (vals i).carry := by rw [hb 15 (by norm_num) (by norm_num)]; simp [CellVals.base]
  have tbit : ∀ k, k < 110 → E.trace (18 + k) = (vals i).bit k := fun k hk => by
    rw [hb (18 + k) (by omega) (by omega)]
    simp only [CellVals.base]
    have : ¬ (18 + k = 2 ∨ 18 + k = 3 ∨ 18 + k = 4 ∨ 18 + k = 5 ∨ 18 + k = 6 ∨ 18 + k = 7 ∨
      18 + k = 8 ∨ 18 + k = 9 ∨ 18 + k = 10 ∨ 18 + k = 11 ∨ 18 + k = 12 ∨ 18 + k = 13 ∨
      18 + k = 14 ∨ 18 + k = 15 ∨ 18 + k = 16 ∨ 18 + k = 17 ∨ 18 + k = 128) := by omega
    simp only [not_or] at this
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := this
    simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17]
  have n2 : ∀ hi : (i : ℕ) + 1 < n, E.traceNext 2 = (vals ⟨(i : ℕ) + 1, hi⟩).idx := fun hi => by
    rw [cellEnv_next_base δF b hn nodes ω chv pbv vals hinj hadj i hi le_rfl (by norm_num)]
    simp [CellVals.base]
  intro g hg
  simp only [Cell.baseGates, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hg
  rcases hg with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    ⟨k, hk, rfl⟩
  · -- isF * idx
    simp only [CoeffExpr.eval, cv, Cell.isF, Cell.idx, m0, t2]
    by_cases h0 : (i : ℕ) = 0
    · simp [h0, hf.serial0 h0]
    · simp [h0]
  · -- (1 - isL) * (idx' - idx - 1)
    simp only [CoeffExpr.eval, cv, nv, notE, Cell.isL, Cell.idx, m1, t2]
    by_cases hl : i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩
    · simp [hl]
    · have hi : (i : ℕ) + 1 < n := by
        have : (i : ℕ) ≠ n - 1 := fun h => hl (Fin.ext h)
        omega
      rw [n2 hi, hf.serialStep hi]
      simp [hl]
  · simp only [CoeffExpr.eval, cv, Cell.lo, Cell.carry, Cell.loL, Cell.loR, t9, t15, t11, t13]
    linear_combination hf.limbLo
  · simp only [CoeffExpr.eval, cv, Cell.hi, Cell.hiL, Cell.hiR, Cell.carry, t10, t12, t14, t15]
    linear_combination hf.limbHi
  · simp only [CoeffExpr.eval, cv, Cell.carry, t15]; exact hf.carry_bool
  · simp only [CoeffExpr.eval, cv, Cell.wL, t5]; exact hf.wL_bool
  · simp only [CoeffExpr.eval, cv, Cell.wR, t6]; exact hf.wR_bool
  · simp only [CoeffExpr.eval, cv, Cell.lo, t9, eval_bitSum, Cell.bit0]
    have : ∀ k ∈ Finset.range 62, (2 : F) ^ k * E.trace (18 + k) = (2 : F) ^ k * (vals i).bit k :=
      fun k hk => by rw [tbit k (by have := Finset.mem_range.mp hk; omega)]
    rw [Finset.sum_congr rfl this]
    exact sub_eq_zero.mpr hf.lo_bits
  · simp only [CoeffExpr.eval, cv, Cell.hi, t10, eval_bitSum, Cell.bit0]
    have : ∀ k ∈ Finset.range 48, (2 : F) ^ k * E.trace (18 + 62 + k) = (2 : F) ^ k * (vals i).bit (62 + k) :=
      fun k hk => by
        rw [show 18 + 62 + k = 18 + (62 + k) from by omega,
          tbit (62 + k) (by have := Finset.mem_range.mp hk; omega)]
    rw [Finset.sum_congr rfl this]
    exact sub_eq_zero.mpr hf.hi_bits
  · simp only [CoeffExpr.eval, cv, notE, Cell.wL, Cell.loL, t5, t11]
    by_cases h : (vals i).wL = 0
    · simp [h, (hf.atomL h).1]
    · have : (vals i).wL = 1 := by
        have := hf.wL_bool; rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' h
        · linear_combination h'
      simp [this]
  · simp only [CoeffExpr.eval, cv, notE, Cell.wL, Cell.hiL, t5, t12]
    by_cases h : (vals i).wL = 0
    · simp [h, (hf.atomL h).2]
    · have : (vals i).wL = 1 := by
        have := hf.wL_bool; rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' h
        · linear_combination h'
      simp [this]
  · simp only [CoeffExpr.eval, cv, notE, Cell.wR, Cell.loR, t6, t13]
    by_cases h : (vals i).wR = 0
    · simp [h, (hf.atomR h).1]
    · have : (vals i).wR = 1 := by
        have := hf.wR_bool; rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' h
        · linear_combination h'
      simp [this]
  · simp only [CoeffExpr.eval, cv, notE, Cell.wR, Cell.hiR, t6, t14]
    by_cases h : (vals i).wR = 0
    · simp [h, (hf.atomR h).2]
    · have : (vals i).wR = 1 := by
        have := hf.wR_bool; rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' h
        · linear_combination h'
      simp [this]
  · -- the 110 bit booleanity gates
    simp only [CoeffExpr.eval, cv, Cell.bit0]
    rw [tbit k hk]
    exact hf.bit_bool k hk

end BaseGates

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
