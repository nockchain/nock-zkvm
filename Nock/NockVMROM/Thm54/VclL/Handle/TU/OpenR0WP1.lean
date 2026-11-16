/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/OpenR0WP1.lean

 **Trace uniqueness on the P1 fragment: the walk's derived round-0 columns and its aux columns.**

 Two tuples accepted by `AcceptsCanon2` at one layout, claim and coin. The 25 round-0 walk columns split into
 * the **core** `coreW = [idx, pre, ridx, len, cL, cR, mL, mR, kL, vL, kR, vR]` (`3 4 5 6 7 8 10 11 21 22 23 24`):
 the trie (which node each row is: `pre`, `ridx`, `len`, the child flags), the node's cell serial `idx`, the
 path-record multiplicities and the child handles;
 * the **derived** columns, fixed row by row once the core agrees: the masks `isF isL rM` (preprocessing),
 `e = cL·cR`, the queue counter `q` (by its recurrence from `isF`), `qinv` (`q·qinv = 1` off the last row,
 `isL·qinv = 0` on it), the depth bits `b0 .. b5` (unique with the `y` gadget) and `u = b1·b2`.
 The 32 walk aux columns are fixed by the round-0 columns: the root-order bits `dr` (the binary form of
 `ridx' − ridx − 1` on a consecutive root pair, `0` off it) and `y = b5(1−b2)(1−b3)`.

 * §1 the row facts of a walk trace as a field statement (`WalkRowFacts`) and the uniqueness of the derived
 columns and the aux columns from the core (`rowFacts_unique`; binary forms are unique below `p`,
 `bits_unique`).
 * §2 an accepted trace has the row facts (`walkRowFacts_of`: the walk chip's base gates at every row node, the
 preprocessed masks, the walk side template `canonW`).
 * §3 **`r0W_auxW_of_core`**: equal core columns at every row node give the `OpenP1` fields `r0W` and `auxW`.

 Not derived here: the core columns themselves and the round-1 labels (`OpenP1.r1W`); they are the hypothesis
 `hcore` of §3.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0WP1

noncomputable section

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qW)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.PinsP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsWalkP1 (rowIx rowIx_val)

/-! ## 1. Row facts and the uniqueness of the derived columns -/

/-- The core round-0 walk columns: `idx pre ridx len cL cR mL mR kL vL kR vR`. -/
def coreW : List ℕ := [3, 4, 5, 6, 7, 8, 10, 11, 21, 22, 23, 24]

section Alg
variable {F : Type} [Field F]

theorem bool01 {x : F} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem natCast_inj_lt {p : ℕ} [CharP F p] {x y : ℕ} (hx : x < p) (hy : y < p) (h : (x : F) = (y : F)) :
    x = y := by
  have := (CharP.natCast_eq_natCast F p).mp h
  unfold Nat.ModEq at this
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

/-- **Binary forms are unique below `p`**: two boolean vectors of length `m` (`2^m ≤ p`) with the same weighted
sum agree. -/
theorem bits_unique {p : ℕ} [CharP F p] (b c : ℕ → F) : ∀ m : ℕ, 2 ^ m ≤ p →
    (∀ i < m, b i * (b i - 1) = 0) → (∀ i < m, c i * (c i - 1) = 0) →
    ∑ i ∈ Finset.range m, (2 : F) ^ i * b i = ∑ i ∈ Finset.range m, (2 : F) ^ i * c i →
    ∀ i < m, b i = c i
  | 0, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | m + 1, hp, hb, hc, hs, i, hi => by
    obtain ⟨s, hs1, hs2⟩ := Chips.CertBound.bits_sum_nat b m (fun i hi => hb i (by omega))
    obtain ⟨t, ht1, ht2⟩ := Chips.CertBound.bits_sum_nat c m (fun i hi => hc i (by omega))
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← hs2, ← ht2] at hs
    have hpm : 2 ^ m + 2 ^ m ≤ p := by rw [pow_succ] at hp; omega
    have key : b m = c m ∧ s = t := by
      rcases bool01 (hb m (by omega)) with h1 | h1 <;> rcases bool01 (hc m (by omega)) with h2 | h2 <;>
        rw [h1, h2] at hs
      · refine ⟨by rw [h1, h2], natCast_inj_lt (F := F) (p := p) (by omega) (by omega) ?_⟩
        simpa using hs
      · exfalso
        have e : ((s : ℕ) : F) = ((t + 2 ^ m : ℕ) : F) := by push_cast; simpa using hs
        have := natCast_inj_lt (F := F) (p := p) (by omega) (by omega) e
        omega
      · exfalso
        have e : ((s + 2 ^ m : ℕ) : F) = ((t : ℕ) : F) := by push_cast; simpa using hs
        have := natCast_inj_lt (F := F) (p := p) (by omega) (by omega) e
        omega
      · have e : ((s + 2 ^ m : ℕ) : F) = ((t + 2 ^ m : ℕ) : F) := by push_cast; simpa using hs
        have := natCast_inj_lt (F := F) (p := p) (by omega) (by omega) e
        exact ⟨by rw [h1, h2], by omega⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · refine bits_unique b c m (le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m)) hp)
        (fun i hi => hb i (by omega)) (fun i hi => hc i (by omega)) ?_ i hi
      rw [← hs2, ← ht2, key.2]
    · exact key.1

/-- **The row facts of a walk trace** (`n` rows, `kroots` roots): `v j i` is round-0 column `j` at row `i`,
`a k i` is aux column `k` (`dr` bits `0 .. 30`, `y` at `31`). Columns: `isF 0`, `isL 1`, `rM 2`, `ridx 5`,
`len 6`, `cL 7`, `cR 8`, `e 9`, `q 12`, `qinv 13`, `u 14`, bits `15 .. 20`. -/
structure WalkRowFacts (n kroots : ℕ) (v a : ℕ → ℕ → F) : Prop where
  isF : ∀ i < n, v 0 i = if i = 0 then 1 else 0
  isL : ∀ i < n, v 1 i = if i + 1 = n then 1 else 0
  rM : ∀ i < n, v 2 i = if i < kroots then 1 else 0
  e : ∀ i < n, v 9 i - v 7 i * v 8 i = 0
  u : ∀ i < n, v 14 i - v 16 i * v 17 i = 0
  bits : ∀ i < n, ∀ k < 6, v (15 + k) i * (v (15 + k) i - 1) = 0
  depth : ∀ i < n, v 6 i + (v 15 i + 2 * v 16 i + 4 * v 17 i + 8 * v 18 i + 16 * v 19 i) + 29 * v 20 i = 60
  qF : ∀ i < n, v 0 i * (v 12 i - (kroots : F) - v 7 i - v 8 i + 1) = 0
  qS : ∀ i, i + 1 < n → (1 - v 1 i) * (v 12 (i + 1) - v 12 i - v 7 (i + 1) - v 8 (i + 1) + 1) = 0
  qinv : ∀ i, i + 1 < n → (1 - v 1 i) * (v 12 i * v 13 i - 1) = 0
  qinvL : ∀ i < n, v 1 i * v 13 i = 0
  y1 : ∀ i < n, a 31 i = v 20 i * (1 - v 17 i) * (1 - v 18 i)
  y2 : ∀ i < n, a 31 i * (1 - v 19 i) * (1 - v 15 i * v 16 i) = 0
  drB : ∀ i < n, ∀ k < 31, a k i * (a k i - 1) = 0
  drS : ∀ i, i + 1 < n → (1 - v 1 i) * v 2 i * v 2 (i + 1) *
    (v 5 (i + 1) - v 5 i - 1 - ∑ k ∈ Finset.range 31, (2 : F) ^ k * a k i) = 0
  drZ : ∀ i, i + 1 < n → ∀ k < 31, (1 - (1 - v 1 i) * v 2 i * v 2 (i + 1)) * a k i = 0
  drZL : ∀ i < n, i + 1 = n → ∀ k < 31, a k i = 0

/-- The length column is a natural `≤ 60`. -/
theorem len_nat {n kroots : ℕ} {v a : ℕ → ℕ → F} (R : WalkRowFacts n kroots v a) {i : ℕ} (hi : i < n) : ∃ N : ℕ, N ≤ 60 ∧ v 6 i = (N : F) := by
  have c0 : v 15 i * (v 15 i - 1) = 0 := R.bits i hi 0 (by norm_num)
  have c1 : v 16 i * (v 16 i - 1) = 0 := R.bits i hi 1 (by norm_num)
  have c2 : v 17 i * (v 17 i - 1) = 0 := R.bits i hi 2 (by norm_num)
  have c3 : v 18 i * (v 18 i - 1) = 0 := R.bits i hi 3 (by norm_num)
  have c4 : v 19 i * (v 19 i - 1) = 0 := R.bits i hi 4 (by norm_num)
  have c5 : v 20 i * (v 20 i - 1) = 0 := R.bits i hi 5 (by norm_num)
  obtain ⟨β0, h0, e0⟩ := bit_nat c0
  obtain ⟨β1, h1, e1⟩ := bit_nat c1
  obtain ⟨β2, h2, e2⟩ := bit_nat c2
  obtain ⟨β3, h3, e3⟩ := bit_nat c3
  obtain ⟨β4, h4, e4⟩ := bit_nat c4
  obtain ⟨β5, h5, e5⟩ := bit_nat c5
  have hle : β0 + 2 * β1 + 4 * β2 + 8 * β3 + 16 * β4 + 29 * β5 ≤ 60 := by omega
  refine ⟨60 - (β0 + 2 * β1 + 4 * β2 + 8 * β3 + 16 * β4 + 29 * β5), by omega, ?_⟩
  have d := R.depth i hi
  rw [e0, e1, e2, e3, e4, e5] at d
  push_cast [Nat.cast_sub hle]
  linear_combination d

/-- **The derived round-0 columns and the aux columns are fixed by the core.** Two families with the row facts
(same `n`, `kroots`, `2^32 ≤ p`) agreeing on the core columns agree on every round-0 column `< 25` and on every aux
column `< 32`, at every row. -/
theorem rowFacts_unique {p : ℕ} [CharP F p] (hp : 2 ^ 32 ≤ p) {n kroots : ℕ} {v a v' a' : ℕ → ℕ → F}
    (R : WalkRowFacts n kroots v a) (R' : WalkRowFacts n kroots v' a')
    (hcore : ∀ j ∈ coreW, ∀ i < n, v j i = v' j i) :
    (∀ j < 25, ∀ i < n, v j i = v' j i) ∧ (∀ k < 32, ∀ i < n, a k i = a' k i) := by
  have cL := hcore 7 (by decide)
  have cR := hcore 8 (by decide)
  have hlen := hcore 6 (by decide)
  have hridx := hcore 5 (by decide)
  have h0 : ∀ i < n, v 0 i = v' 0 i := fun i hi => (R.isF i hi).trans (R'.isF i hi).symm
  have h1 : ∀ i < n, v 1 i = v' 1 i := fun i hi => (R.isL i hi).trans (R'.isL i hi).symm
  have h2 : ∀ i < n, v 2 i = v' 2 i := fun i hi => (R.rM i hi).trans (R'.rM i hi).symm
  have he : ∀ i < n, v 9 i = v' 9 i := fun i hi => by
    have x := R.e i hi
    have y := R'.e i hi
    rw [cL i hi, cR i hi] at x
    linear_combination x - y
  -- the depth bits
  have hbits : ∀ i < n, v 15 i = v' 15 i ∧ v 16 i = v' 16 i ∧ v 17 i = v' 17 i ∧ v 18 i = v' 18 i ∧
      v 19 i = v' 19 i ∧ v 20 i = v' 20 i := fun i hi => by
    obtain ⟨N, hN, hNe⟩ := len_nat R hi
    have d' := R'.depth i hi
    rw [← hlen i hi] at d'
    exact depth_bits_unique (p := p) (n := N) (by omega) hNe
      (R.bits i hi 0 (by norm_num)) (R.bits i hi 1 (by norm_num)) (R.bits i hi 2 (by norm_num))
      (R.bits i hi 3 (by norm_num)) (R.bits i hi 4 (by norm_num)) (R.bits i hi 5 (by norm_num))
      (R.depth i hi) (R.y1 i hi) (R.y2 i hi)
      (R'.bits i hi 0 (by norm_num)) (R'.bits i hi 1 (by norm_num)) (R'.bits i hi 2 (by norm_num))
      (R'.bits i hi 3 (by norm_num)) (R'.bits i hi 4 (by norm_num)) (R'.bits i hi 5 (by norm_num))
      d' (R'.y1 i hi) (R'.y2 i hi)
  have hu : ∀ i < n, v 14 i = v' 14 i := fun i hi => by
    have x := R.u i hi
    have y := R'.u i hi
    obtain ⟨-, b1, b2, -⟩ := hbits i hi
    rw [b1, b2] at x
    linear_combination x - y
  -- the queue counter, by its recurrence
  have hq : ∀ i < n, v 12 i = v' 12 i := by
    intro i
    induction i with
    | zero =>
      intro hi
      have x := R.qF 0 hi
      have y := R'.qF 0 hi
      rw [R.isF 0 hi, if_pos rfl, one_mul, cL 0 hi, cR 0 hi] at x
      rw [R'.isF 0 hi, if_pos rfl, one_mul] at y
      linear_combination x - y
    | succ i ih =>
      intro hi
      have x := R.qS i hi
      have y := R'.qS i hi
      rw [R.isL i (by omega), if_neg (by omega), sub_zero, one_mul, ih (by omega), cL (i + 1) hi,
        cR (i + 1) hi] at x
      rw [R'.isL i (by omega), if_neg (by omega), sub_zero, one_mul] at y
      linear_combination x - y
  -- `qinv`
  have hqi : ∀ i < n, v 13 i = v' 13 i := fun i hi => by
    by_cases hL : i + 1 = n
    · have x := R.qinvL i hi
      have y := R'.qinvL i hi
      rw [R.isL i hi, if_pos hL, one_mul] at x
      rw [R'.isL i hi, if_pos hL, one_mul] at y
      rw [x, y]
    · have hi' : i + 1 < n := by omega
      have x := R.qinv i hi'
      have y := R'.qinv i hi'
      rw [R.isL i hi, if_neg hL, sub_zero, one_mul, hq i hi] at x
      rw [R'.isL i hi, if_neg hL, sub_zero, one_mul] at y
      have hq0 : v' 12 i ≠ 0 := by
        intro h0
        rw [h0, zero_mul, zero_sub] at y
        exact one_ne_zero (neg_eq_zero.mp y)
      exact mul_left_cancel₀ hq0 (by linear_combination x - y)
  have r0 : ∀ j < 25, ∀ i < n, v j i = v' j i := by
    intro j hj i hi
    interval_cases j
    · exact h0 i hi
    · exact h1 i hi
    · exact h2 i hi
    · exact hcore 3 (by decide) i hi
    · exact hcore 4 (by decide) i hi
    · exact hcore 5 (by decide) i hi
    · exact hcore 6 (by decide) i hi
    · exact hcore 7 (by decide) i hi
    · exact hcore 8 (by decide) i hi
    · exact he i hi
    · exact hcore 10 (by decide) i hi
    · exact hcore 11 (by decide) i hi
    · exact hq i hi
    · exact hqi i hi
    · exact hu i hi
    · exact (hbits i hi).1
    · exact (hbits i hi).2.1
    · exact (hbits i hi).2.2.1
    · exact (hbits i hi).2.2.2.1
    · exact (hbits i hi).2.2.2.2.1
    · exact (hbits i hi).2.2.2.2.2
    · exact hcore 21 (by decide) i hi
    · exact hcore 22 (by decide) i hi
    · exact hcore 23 (by decide) i hi
    · exact hcore 24 (by decide) i hi
  refine ⟨r0, ?_⟩
  intro k hk i hi
  by_cases hk31 : k < 31
  · by_cases hL : i + 1 = n
    · rw [R.drZL i hi hL k hk31, R'.drZL i hi hL k hk31]
    · have hi' : i + 1 < n := by omega
      have hm : (1 - v 1 i) * v 2 i * v 2 (i + 1) = (1 - v' 1 i) * v' 2 i * v' 2 (i + 1) := by
        rw [h1 i hi, h2 i hi, h2 (i + 1) hi']
      by_cases hm0 : (1 - v 1 i) * v 2 i * v 2 (i + 1) = 0
      · have x := R.drZ i hi' k hk31
        have y := R'.drZ i hi' k hk31
        rw [hm0, sub_zero, one_mul] at x
        rw [← hm, hm0, sub_zero, one_mul] at y
        rw [x, y]
      · have x := R.drS i hi'
        have y := R'.drS i hi'
        rw [← hm] at y
        have x' := (mul_eq_zero.mp x).resolve_left hm0
        have y' := (mul_eq_zero.mp y).resolve_left hm0
        rw [hridx i hi, hridx (i + 1) hi'] at x'
        have hs : ∑ k ∈ Finset.range 31, (2 : F) ^ k * a k i = ∑ k ∈ Finset.range 31, (2 : F) ^ k * a' k i := by
          linear_combination y' - x'
        exact bits_unique (p := p) (fun k => a k i) (fun k => a' k i) 31
          (le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hp)
          (fun k hk => R.drB i hi k hk) (fun k hk => R'.drB i hi k hk) hs k hk31
  · have : k = 31 := by omega
    subst this
    obtain ⟨-, -, b2, b3, -, b5⟩ := hbits i hi
    rw [R.y1 i hi, R'.y1 i hi, b2, b3, b5]

end Alg

/-! ## 2. An accepted trace has the row facts -/

section Glue
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  (δ : ZMod p) (b : Basis (Fin 3) (ZMod p) K) (Pb : PubJ8 p)

/-- Walk row `i`'s base environment (the walk chip's own view). -/
abbrev envB (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K) (i : ℕ) : Env (ZMod p) :=
  Reify.envOfTrace (qW δ b Pb tr chals pubs) Pb.orbitW.ω (Pb.nodesW (rowIx Pb.hnW i)) (slotVal b 25 chals)
    (slotVal b 25 pubs)

/-- Walk row `i`'s environment of the side template `canonW`. -/
abbrev envS (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) (i : ℕ) : Env (ZMod p) :=
  Reify.envOfTrace (sideWQ tr ax) Pb.orbitW.ω (Pb.nodesW (rowIx Pb.hnW i)) (fun _ => 0) (fun _ => 0)

theorem rowIx_mk {i : ℕ} (hi : i < Pb.nW) : rowIx Pb.hnW i = ⟨i, hi⟩ := Fin.ext (rowIx_val Pb.hnW i hi)

theorem envB_eval (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K) {j : ℕ} (hj : j < 166) {i : ℕ} (hi : i < Pb.nW) :
    (envB δ b Pb tr chals pubs i).trace j = (tr.W ⟨j, hj⟩).eval (Pb.nodesW ⟨i, hi⟩) := by
  rw [envOfTrace_trace _ _ _ _ _ (by rw [walkChipJ8_width]; exact hj), rowIx_mk Pb hi]
  rfl

theorem envS_trace (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) (chals pubs : ℕ → K) {j : ℕ} (hj : j < 25) (i : ℕ) :
    (envS Pb tr ax i).trace j = (envB δ b Pb tr chals pubs i).trace j := by
  rw [envW_trace Pb tr ax hj, envOfTrace_trace _ _ _ _ _ (by rw [walkChipJ8_width]; omega)]
  rfl

theorem envS_aux (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) {k : ℕ} (hk : k < 32) {i : ℕ} (hi : i < Pb.nW) :
    (envS Pb tr ax i).trace (25 + k) = (ax.W ⟨k, hk⟩).eval (Pb.nodesW ⟨i, hi⟩) := by
  rw [envOfTrace_trace _ _ _ _ _ (by rw [canonWT_width]; omega), rowIx_mk Pb hi]
  simp only [sideWQ, show ¬ (25 + k < 25) by omega, dif_neg, not_false_eq_true]
  congr 2
  exact Fin.ext (by simp)

theorem nodes_next (hadj : ∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW),
    Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω) {i : ℕ} (hi : i + 1 < Pb.nW) :
    Pb.orbitW.ω * Pb.nodesW (rowIx Pb.hnW i) = Pb.nodesW (rowIx Pb.hnW (i + 1)) := by
  rw [rowIx_mk Pb (by omega : i < Pb.nW), rowIx_mk Pb hi, mul_comm]
  exact (hadj ⟨i, by omega⟩ hi).symm

theorem envB_next (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K)
    (hadj : ∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW),
      Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω) {i : ℕ} (hi : i + 1 < Pb.nW) (j : ℕ) :
    (envB δ b Pb tr chals pubs i).traceNext j = (envB δ b Pb tr chals pubs (i + 1)).trace j := by
  simp only [envB, Reify.envOfTrace, nodes_next Pb hadj hi]

theorem envS_next (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) (chals pubs : ℕ → K)
    (hadj : ∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW),
      Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω) {i : ℕ} (hi : i + 1 < Pb.nW) {j : ℕ} (hj : j < 25) :
    (envS Pb tr ax i).traceNext j = (envB δ b Pb tr chals pubs (i + 1)).trace j := by
  have e : (envS Pb tr ax i).traceNext j = (envS Pb tr ax (i + 1)).trace j := by
    simp only [envS, Reify.envOfTrace, nodes_next Pb hadj hi]
  rw [e, envS_trace δ b Pb tr ax chals pubs hj]

variable [Fintype K] [DecidableEq K] [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)}
  {ax : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ}

/-- **An accepted walk trace with `canonW` has the row facts**, at the base environments of the walk chip and the
side environments of `canonW`. -/
theorem walkRowFacts_of (hA : AcceptsJ8V δ b Pb Rg c χ M tr r g) (hW : (canonW b Pb).Satisfies (sideWQ tr ax)) :
    WalkRowFacts Pb.nW Pb.kroots (fun j i => (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW i).trace j)
      (fun k i => (envS Pb tr ax i).trace (25 + k)) := by
  set chals := chalsMJ8 δ χ
  set pubs := M.pubsW
  set Q := qW δ b Pb tr chals pubs with hQ
  have hw : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals pubs).rap.w = 166 :=
    walkChipJ8_width δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals pubs
  -- the base gates at row `i`
  have hl : ∀ i, ∀ g ∈ (walkTemplateJ8 δ Pb.kroots).baseTransition,
      g.eval (envB δ b Pb tr chals pubs i) = 0 := fun i =>
    ((expandChip_satisfies_iff_language (walkTemplateJ8 δ Pb.kroots) b _ _ Pb.orbitW _ Q).mp hA.hsatW
      (Pb.nodesW (rowIx Pb.hnW i)) (mem_rowNodeSet Pb.nodesW (rowIx Pb.hnW i))).1
  have hB : ∀ g, (g ∈ basePre ∨ g = depthJ8 ∨ g ∈ basePost Pb.kroots) →
      g ∈ (walkTemplateJ8 (F := ZMod p) δ Pb.kroots).baseTransition := by
    intro g hg
    show g ∈ baseGatesJ8 Pb.kroots ++ CellTwinK.baseHK
    simp only [baseGatesJ8, List.mem_append, List.mem_singleton]
    tauto
  -- the side gates at row `i`
  have hs : ∀ i, i < Pb.nW → ∀ g ∈ canonWGates (F := ZMod p), g.eval (envS Pb tr ax i) = 0 := fun i hi =>
    canonW_row b Pb tr ax hW (mem_rowNodeSet Pb.nodesW (rowIx Pb.hnW i))
  -- the masks
  have m0 : Q ⟨0, by rw [hw]; omega⟩ = firstRowMask Pb.nodesW := hA.hbindW ⟨0, by show 0 < 3; omega⟩
  have m1 : Q ⟨1, by rw [hw]; omega⟩ = lastRowMask Pb.hnW Pb.nodesW := hA.hbindW ⟨1, by show 1 < 3; omega⟩
  have m2 : Q ⟨2, by rw [hw]; omega⟩ = rootRowMaskW Pb.nodesW Pb.kroots := hA.hbindW ⟨2, by show 2 < 3; omega⟩
  have hmask : ∀ i, i < Pb.nW → (envB δ b Pb tr chals pubs i).trace 0 = (if i = 0 then 1 else 0) ∧
      (envB δ b Pb tr chals pubs i).trace 1 = (if i + 1 = Pb.nW then 1 else 0) := fun i hi => by
    have := TeleH.masks_of Pb.hnW Pb.nodesW Pb.orbitW Q (by rw [hw]; omega) (by rw [hw]; omega) m0 m1 hA.hinjW
      (slotVal b 25 chals) (slotVal b 25 pubs) (rowIx Pb.hnW i)
    simp only [rowIx_val Pb.hnW i hi] at this
    refine ⟨this.1, this.2.trans ?_⟩
    by_cases h : i + 1 = Pb.nW
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  have hrM : ∀ i, i < Pb.nW → (envB δ b Pb tr chals pubs i).trace 2 = (if i < Pb.kroots then 1 else 0) :=
    fun i hi => by
      rw [envOfTrace_trace _ _ _ _ _ (by rw [hw]; omega)]
      refine (congrArg (Polynomial.eval _) m2).trans ?_
      rw [rootRowMaskW_eval _ _ hA.hinjW, rowIx_val Pb.hnW i hi]
  have hSt : ∀ i {j : ℕ}, j < 25 → (envS Pb tr ax i).trace j = (envB δ b Pb tr chals pubs i).trace j :=
    fun i j hj => envS_trace δ b Pb tr ax chals pubs hj i
  have hSn : ∀ i, i + 1 < Pb.nW → ∀ {j : ℕ}, j < 25 →
      (envS Pb tr ax i).traceNext j = (envB δ b Pb tr chals pubs (i + 1)).trace j :=
    fun i hi j hj => envS_next δ b Pb tr ax chals pubs hA.hadjW hi hj
  have hBn : ∀ i, i + 1 < Pb.nW → ∀ j,
      (envB δ b Pb tr chals pubs i).traceNext j = (envB δ b Pb tr chals pubs (i + 1)).trace j :=
    fun i hi j => envB_next δ b Pb tr chals pubs hA.hadjW hi j
  refine ⟨fun i hi => (hmask i hi).1, fun i hi => (hmask i hi).2, hrM, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · -- e = cL·cR
    intro i hi
    have := hl i _ (hB _ (Or.inl (by simp [basePre])) :
      (.sub (cv WChip.e) (.mul (cv WChip.cL) (cv WChip.cR)) : CoeffExpr (ZMod p)) ∈ _)
    simp only [CoeffExpr.eval] at this
    exact this
  · -- u = b1·b2
    intro i hi
    have := hl i _ (hB _ (Or.inl (by simp [basePre])) :
      (.sub (cv WChip.u) (.mul (WChip.bt 1) (WChip.bt 2)) : CoeffExpr (ZMod p)) ∈ _)
    simp only [CoeffExpr.eval] at this
    exact this
  · -- bit booleanity
    intro i hi k hk
    have hm : (boolE (WChip.bt k) : CoeffExpr (ZMod p)) ∈ basePost Pb.kroots :=
      List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
    have := hl i _ (hB _ (Or.inr (Or.inr hm)))
    simp only [CoeffExpr.eval] at this
    exact this
  · -- the depth certificate
    intro i hi
    have := hl i _ (hB _ (Or.inr (Or.inl rfl)))
    simp only [depthJ8, CoeffExpr.eval, eval_bitSum, Finset.sum_range_succ, Finset.sum_range_zero] at this
    simp only [WChip.len, WChip.bit0] at this
    linear_combination this
  · -- q on the first row
    intro i hi
    have := hl i _ (hB _ (Or.inr (Or.inr (by simp [basePost]))) :
      (.mul (cv WChip.isF) (.add (.sub (.sub (.sub (cv WChip.q) (.const (Pb.kroots : ZMod p))) (cv WChip.cL))
        (cv WChip.cR)) (.const 1)) : CoeffExpr (ZMod p)) ∈ _)
    simp only [CoeffExpr.eval] at this
    exact this
  · -- q recurrence
    intro i hi
    have := hl i _ (hB _ (Or.inr (Or.inr (by simp [basePost]))) :
      (.mul (notE (cv WChip.isL)) (.add (.sub (.sub (.sub (nv WChip.q) (cv WChip.q)) (nv WChip.cL))
        (nv WChip.cR)) (.const 1)) : CoeffExpr (ZMod p)) ∈ _)
    simp only [CoeffExpr.eval, hBn i hi] at this
    exact this
  · -- q·qinv = 1 off the last row
    intro i hi
    have := hl i _ (hB _ (Or.inr (Or.inr (by simp [basePost]))) :
      (.mul (notE (cv WChip.isL)) (.sub (.mul (cv WChip.q) (cv WChip.qinv)) (.const 1)) : CoeffExpr (ZMod p)) ∈ _)
    simp only [CoeffExpr.eval] at this
    exact this
  · -- isL·qinv = 0 (side)
    intro i hi
    have := canonW_qinv _ (hs i hi)
    rw [hSt i (by decide), hSt i (by decide)] at this
    exact this
  · -- y
    intro i hi
    have := (canonW_y _ (hs i hi)).1
    rw [hSt i (j := WChip.bit0 + 5) (by decide), hSt i (j := WChip.bit0 + 2) (by decide),
      hSt i (j := WChip.bit0 + 3) (by decide)] at this
    exact this
  · intro i hi
    have := (canonW_y _ (hs i hi)).2
    rw [hSt i (j := WChip.bit0 + 4) (by decide), hSt i (j := WChip.bit0) (by decide),
      hSt i (j := WChip.bit0 + 1) (by decide)] at this
    exact this
  · -- dr booleanity
    intro i hi k hk
    have := hs i hi (boolE (cv (wA + k)))
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))))
    simp only [CoeffExpr.eval] at this
    exact this
  · -- the root order
    intro i hi
    have := hs i (by omega) (.mul rootPairW (.sub (.sub (.sub (nv WChip.ridx) (cv WChip.ridx)) (.const 1))
      (bitSum wA 31))) (by simp [canonWGates])
    simp only [CoeffExpr.eval, rootPairW, eval_bitSum] at this
    rw [hSt i (by decide), hSt i (by decide), hSt i (by decide), hSn i hi (by decide), hSn i hi (by decide)] at this
    exact this
  · -- dr = 0 off the mask
    intro i hi k hk
    have := hs i (by omega) (.mul (notE rootPairW) (cv (wA + k)))
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))
    simp only [CoeffExpr.eval, rootPairW] at this
    rw [hSt i (by decide), hSt i (by decide), hSn i hi (by decide)] at this
    exact this
  · -- dr = 0 on the last row
    intro i hi hL k hk
    have := hs i hi (.mul (notE rootPairW) (cv (wA + k)))
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))
    simp only [CoeffExpr.eval, rootPairW] at this
    have hL1 : (envB δ b Pb tr chals pubs i).trace WChip.isL = 1 := by
      have := (hmask i hi).2
      rw [if_pos hL] at this
      exact this
    rw [hSt i (j := WChip.isL) (by decide), hL1] at this
    simp only [sub_self, zero_mul, sub_zero, one_mul] at this
    exact this

end Glue

/-! ## 3. `OpenP1.r0W` and `OpenP1.auxW` from the core -/

section Main
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **The walk's round-0 columns (`< 25`) and its 32 aux columns agree at every row node** (`OpenP1.r0W`,
`OpenP1.auxW`), for two tuples accepted by `AcceptsCanon2` at one layout, claim and coin, given that the core
columns `coreW` agree at every row node. -/
theorem r0W_auxW_of_core {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {r : RowsJ8} {g : ℕ} {χ : Coins frameJ8 K}
    {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hcore : ∀ j : Fin 166, (j : ℕ) ∈ coreW → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) :
    (∀ j : Fin 166, (j : ℕ) < 25 → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) ∧
      (∀ j i, (ax.W j).eval (Pb.nodesW i) = (ax'.W j).eval (Pb.nodesW i)) := by
  have R := walkRowFacts_of δ b Pb h.1.1 h.1.2.hW
  have R' := walkRowFacts_of δ b Pb h'.1.1 h'.1.2.hW
  have hp : 2 ^ 32 ≤ p := by
    rw [hpG]
    norm_num [Nock.Atoms.p, Nock.Field.p]
  have hc : ∀ j ∈ coreW, ∀ i < Pb.nW,
      (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW i).trace j = (envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW i).trace j := by
    intro j hj i hi
    have hj25 : j < 166 := by simp only [coreW, List.mem_cons, List.not_mem_nil, or_false] at hj; omega
    rw [envB_eval δ b Pb tr _ _ hj25 hi, envB_eval δ b Pb tr' _ _ hj25 hi]
    exact hcore ⟨j, hj25⟩ hj ⟨i, hi⟩
  obtain ⟨h0, haux⟩ := rowFacts_unique (p := p) hp R R' hc
  refine ⟨fun j hj i => ?_, fun j i => ?_⟩
  · have := h0 j hj i i.isLt
    rwa [envB_eval δ b Pb tr _ _ j.isLt i.isLt, envB_eval δ b Pb tr' _ _ j.isLt i.isLt] at this
  · have := haux j j.isLt i i.isLt
    rwa [envS_aux Pb tr ax j.isLt i.isLt, envS_aux Pb tr' ax' j.isLt i.isLt] at this

end Main

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0WP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0WP1.bits_unique
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0WP1.rowFacts_unique
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0WP1.walkRowFacts_of
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0WP1.r0W_auxW_of_core
