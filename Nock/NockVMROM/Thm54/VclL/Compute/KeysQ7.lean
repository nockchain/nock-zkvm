import Nock.NockVMROM.Thm54.VclL.Compute.ChipQ7S
import Nock.NockVMROM.Thm54.VclL.Compute.HCFTree

/-!
.

* **`recKeyQ7`** (typed on `B0Cols F T`, the frame's `recKey` signature): record `j` of
  a row in state `st` at carrier `S` (the row serial, `S = i`) reads the B0 columns of row `S`:
  `j = 0` → `export (fIdx, true)`; `j = 1` → `path (vIdx₀, axCol)` at `s0`, else `export (vIdx₀, false)`;
  `j = 2` → `path (vIdx₁, axCol)` at `s9`, else `export (vIdx₁, false)`.  Every column read is round 0
  (`fIdx_round0`, `vIdx_round0`, `axCol_round0`: `AxGate.axCol` is round 0 under `colRoundVCLE`).
* **The key clauses, compiled for every trace** (`export_key_clauseQ7`, `path_key_clauseQ7`): the
  record the side chip accumulates (`recX11` / `recP`) has, at `RV.recordViewVCL`, exactly the key
  `recKeyQ7 (b0 Q) st i j`.
* With the arity-1 serial as the carrier, an `s0` row at serial `S + 1` and an `s9` row at serial `S`
  address the same exponent `S + 3`, so `keyOf` must identify their two different path keys:
  `keyOf_forces_collision` (generic), `no_keyOf_at_serial_carrier` (a B0 assignment where no `keyOf`
  exists).  `joinRecordAxis` (`ax (S+2)` / `ax (S+3)`) has the same collision for `axB0`.
* `recKeyQ7` (row-indexed) stays as the reader of row
  `i`; at the doubled label `recKeyQ7' … (2i) j = recKeyQ7 … i j` (`recKeyQ7'_even`), so the compiled
  clauses transfer (`export_key_clauseQ7'`, `path_key_clauseQ7'`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Reified Nock.Framework Nock.Framework.Reify Module Nock.Walk
open Nock.ComputeTable (State)
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.RecordCarrier
open scoped Polynomial

set_option linter.unusedSectionVars false

noncomputable section

theorem fIdx_round0 : colRoundVCLE fIdxCol = 0 := by decide
theorem vIdx_round0 (j : Fin 2) : colRoundVCLE (vIdxCol j) = 0 := by fin_cases j <;> decide
theorem axCol_round0 : colRoundVCLE axCol = 0 := by decide

section keys
variable {F K : Type} [Field F] [Field K] [Algebra F K] {hC : ℕ} {S : MemShape} {T : TableSpec} [WideTable T] {w : ℕ}

/-- The node of row `S` (row `0` off range). -/
def rowNodeQ7 (V : VerifierData F K hC S) (Sr : ℕ) : F :=
  if h : Sr < V.N then V.computeNodes ⟨Sr, h⟩ else 0

/-- A round-0 column of the side chip read at row `S`, lifted to `ℕ` through `K`. -/
def b0NatAt (V : VerifierData F K hC S) (b : B0Cols F T) (c : ℕ) (hc : c < 232)
    (h0 : colRoundVCLE c = 0) (Sr : ℕ) : ℕ :=
  natLift (algebraMap F K ((b (b0ColT c hc h0)).eval (rowNodeQ7 V Sr)))

/-- **`recKeyQ7`**: the key of record `j` of a row in state `st` at serial `S`, from B0 only. -/
def recKeyQ7 (V : VerifierData F K hC S) (b : B0Cols F T) (st : State) (Sr j : ℕ) :
    RV.KeyVCL :=
  match j with
  | 0 => .export (b0NatAt V b fIdxCol (by decide) fIdx_round0 Sr) true
  | 1 => if st = .s0 then
      .path (b0NatAt V b (vIdxCol 0) (by decide) (vIdx_round0 0) Sr)
        (b0NatAt V b axCol (by decide) axCol_round0 Sr)
    else .export (b0NatAt V b (vIdxCol 0) (by decide) (vIdx_round0 0) Sr) false
  | _ => if st = .s9 then
      .path (b0NatAt V b (vIdxCol 1) (by decide) (vIdx_round0 1) Sr)
        (b0NatAt V b axCol (by decide) axCol_round0 Sr)
    else .export (b0NatAt V b (vIdxCol 1) (by decide) (vIdx_round0 1) Sr) false

/-- The raw row env of row `i` (what the accumulators read). -/
def rawEnvQ7 (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X]) (i : Fin V.N) :
    Env F := envOfTrace Q V.orbitC.ω (V.computeNodes i) chalV pubVal

theorem b0NatAt_row (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin T.width → F[X])
    (i : Fin V.N) (c : ℕ) (hc : c < 232) (h0 : colRoundVCLE c = 0) :
    b0NatAt V (b0 (T := T) Q) c hc h0 i =
      natLift (algebraMap F K ((rawEnvQ7 V chalV pubVal Q i).trace c)) := by
  simp [b0NatAt, rowNodeQ7, i.isLt, b0, b0ColT, rawEnvQ7, envOfTrace, hc, show c < T.width from lt_of_lt_of_le hc (WideTable.hw (T := T))]

variable [DecidableEq K] {C : TableSpec} {hC' : ℕ} {S' : MemShape}

/-- **The export key clause** (compiled, every trace, every row): slot `s` of the side chip's export
accumulator has, at `RV.recordViewVCL`, the key `recKeyQ7 (b0 Q) st i s` — at slot 0 for every
state, at slot 1 off `s0`, at slot 2 off `s9`. -/
theorem export_key_clauseQ7 (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin T.width → F[X])
    (i : Fin V.N) (st : State) (s : ℕ) (hs : s = 0 ∨ (s = 1 ∧ st ≠ .s0) ∨ (s = 2 ∧ st ≠ .s9)) :
    (RV.recordViewVCL F K K C S' hC').key 1 (recX11 V.basis (rawEnvQ7 V chalV pubVal Q i) s) =
      recKeyQ7 V (b0 (T := T) Q) st i s := by
  have hk : (RV.recordViewVCL F K K C S' hC').key 1 (recX11 V.basis (rawEnvQ7 V chalV pubVal Q i) s) =
      .export (natLift (recX V.basis (rawEnvQ7 V chalV pubVal Q i) s 9)) (decide (s = 0)) := by
    show RV.exportKey _ = _
    simp only [RV.exportKey, RV.sideOf]
    congr 1
    · have h10 : recX11 V.basis (rawEnvQ7 V chalV pubVal Q i) s 10 = sideVal s := by
        unfold recX11; exact Fin.snoc_last (α := fun _ => K) _ _
      rw [h10]; unfold sideVal; by_cases h : s = 0 <;> simp [h]
  rw [hk]
  rcases hs with rfl | ⟨rfl, hst⟩ | ⟨rfl, hst⟩
  · simp only [recKeyQ7, decide_true]
    rw [b0NatAt_row V chalV pubVal Q i]; rfl
  · simp only [recKeyQ7, if_neg hst]
    rw [b0NatAt_row V chalV pubVal Q i]; rfl
  · simp only [recKeyQ7, if_neg hst]
    rw [b0NatAt_row V chalV pubVal Q i]; rfl

/-- **The path key clause** (compiled, every trace, every row): the `s0` (slot 1) / `s9` (slot 2)
path record has key `path (vIdx, axCol)` = `recKeyQ7 (b0 Q) st i j` — the axis is the B0 `axCol`. -/
theorem path_key_clauseQ7 (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin T.width → F[X])
    (i : Fin V.N) (s : ℕ) (hs : s < 2) :
    (RV.recordViewVCL F K K C S' hC').key 2 (recP V.basis (rawEnvQ7 V chalV pubVal Q i) s) =
      recKeyQ7 V (b0 (T := T) Q) (if s = 0 then .s0 else .s9) i (s + 1) := by
  show RV.pathKey _ = _
  interval_cases s
  · simp only [RV.pathKey, recKeyQ7]
    rw [b0NatAt_row V chalV pubVal Q i, b0NatAt_row V chalV pubVal Q i]; rfl
  · simp only [RV.pathKey, recKeyQ7, show (1 : ℕ) ≠ 0 by decide, if_false]
    rw [b0NatAt_row V chalV pubVal Q i, b0NatAt_row V chalV pubVal Q i]; rfl

/-- **Stride-1 negative control. The carrier collision (generic)**: any `keyOf` meeting the frame's `recKey_s0` / `recKey_s9`
at the serial carrier identifies the `s0` key at serial `S + 1` with the `s9` key at serial `S`. -/
theorem keyOf_forces_collision (V : VerifierData F K hC S) (b : B0Cols F T)
    (keyOf : ℕ → RV.KeyVCL)
    (h0 : ∀ Sr, recKeyQ7 V b .s0 Sr 1 = keyOf (Sr + 2))
    (h9 : ∀ Sr, recKeyQ7 V b .s9 Sr 2 = keyOf (Sr + 3)) (Sr : ℕ) :
    recKeyQ7 V b .s0 (Sr + 1) 1 = recKeyQ7 V b .s9 Sr 2 := by
  rw [h0, h9]

theorem no_keyOf_at_serial_carrier (V : VerifierData F K hC S)
    (hK : 7 < ringChar K) :
    ∃ b : B0Cols F T, ¬ ∃ keyOf : ℕ → RV.KeyVCL,
      (∀ Sr, recKeyQ7 V b .s0 Sr 1 = keyOf (Sr + 2)) ∧ (∀ Sr, recKeyQ7 V b .s9 Sr 2 = keyOf (Sr + 3)) := by
  refine ⟨fun j => if j.1.1 = vIdxCol 0 then Polynomial.C 5
    else if j.1.1 = vIdxCol 1 then Polynomial.C 7 else 0, ?_⟩
  rintro ⟨keyOf, h0, h9⟩
  have hc := keyOf_forces_collision V _ keyOf h0 h9 0
  simp only [recKeyQ7, b0NatAt, b0ColT] at hc
  have h5 : natLift (algebraMap F K (5 : F)) = 5 := by
    rw [show (5 : F) = ((5 : ℕ) : F) by norm_num, map_natCast]; exact natLift_natCast (by omega)
  have h7 : natLift (algebraMap F K (7 : F)) = 7 := by
    rw [show (7 : F) = ((7 : ℕ) : F) by norm_num, map_natCast]; exact natLift_natCast (by omega)
  simp [vIdxCol, Polynomial.eval_C, h5, h7] at hc

end keys

/-! The per-row address set `{S+2, S+3}` under a stride. -/

/-- Stride 1 (the serial itself): the `s0` read of row `i+1` and the `s9` read of row `i` coincide. -/
theorem stride1_collides (i : ℕ) : (i + 1) + 2 = i + 3 := by omega

/-- Stride 2: no `s0` address equals an `s9` address, across any two rows. -/
theorem stride2_disjoint (i j : ℕ) : 2 * i + 2 ≠ 2 * j + 3 := by omega

/-- Stride 2: the two addresses of row `i` are injective in `i` (no cross-row same-slot collision). -/
theorem stride2_inj_s0 (i j : ℕ) (h : 2 * i + 2 = 2 * j + 2) : i = j := by omega
theorem stride2_inj_s9 (i j : ℕ) (h : 2 * i + 3 = 2 * j + 3) : i = j := by omega

theorem stride4_disjoint (i j : ℕ) : 4 * i + 2 ≠ 4 * j + 3 := by omega

/-- Any stride `c ≥ 2` is disjoint: `c·i + 3 = c·j + 2` forces `c ∣ 1`. -/
theorem stride_ge_two_disjoint (c i j : ℕ) (hc : 2 ≤ c) : c * i + 3 ≠ c * j + 2 := by
  intro h
  have hlt : c * i < c * j := by omega
  have hij : i < j := Nat.lt_of_mul_lt_mul_left hlt
  have h1 : c * (j - i) = 1 := by rw [Nat.mul_sub]; omega
  have : c ∣ 1 := ⟨j - i, h1.symm⟩
  have := Nat.le_of_dvd Nat.one_pos this
  omega

/-- Every address `k ≥ 2` is some row's `s0` or `s9` address at stride 2: no gap below `2N+2`. -/
theorem stride2_no_gap (k : ℕ) (hk : 2 ≤ k) : ∃ i, k = 2 * i + 2 ∨ k = 2 * i + 3 := by
  refine ⟨(k - 2) / 2, ?_⟩
  omega

/-! ### The instance: `keyOf` / `axB0` / `recKey` at stride 2 on the compiled columns -/

section keys2
variable {F K : Type} [Field F] [Field K] [Algebra F K] {hC : ℕ} {S : MemShape} {T : TableSpec} [WideTable T] {w : ℕ}

/-- The row an address `k` names (`k = 2i+2` or `2i+3` ↦ `i`). -/
def rowOf (k : ℕ) : ℕ := (k - 2) / 2

theorem rowOf_s0 (i : ℕ) : rowOf (2 * i + 2) = i := by unfold rowOf; omega
theorem rowOf_s9 (i : ℕ) : rowOf (2 * i + 3) = i := by unfold rowOf; omega
theorem par_s0 (i : ℕ) : (2 * i + 2 - 2) % 2 = 0 := by omega
theorem par_s9 (i : ℕ) : (2 * i + 3 - 2) % 2 = 1 := by omega

/-- **`keyOfQ7`** (the frame's `keyOf`, B0-typed): the path key of the row `rowOf k`, slot by parity
(`vIdx₀` at even `k − 2`: the `s0` read; `vIdx₁` at odd: the `s9` arm), axis the row's `axCol`. -/
def keyOfQ7 (V : VerifierData F K hC S) (b : B0Cols F T) (_ : MState) (k : ℕ) :
    RV.KeyVCL :=
  if (k - 2) % 2 = 0 then
    .path (b0NatAt V b (vIdxCol 0) (by decide) (vIdx_round0 0) (rowOf k))
      (b0NatAt V b axCol (by decide) axCol_round0 (rowOf k))
  else
    .path (b0NatAt V b (vIdxCol 1) (by decide) (vIdx_round0 1) (rowOf k))
      (b0NatAt V b axCol (by decide) axCol_round0 (rowOf k))

/-- **`axB0Q7`** (the frame's `axB0`): the `axCol` of the row `rowOf k`. -/
def axB0Q7 (V : VerifierData F K hC S) (b : B0Cols F T) (k : ℕ) : ℕ :=
  b0NatAt V b axCol (by decide) axCol_round0 (rowOf k)

/-- **`recKeyQ7'`** (the frame's `recKey` at the stride-2 carrier `Sr = 2·i`): record 0 is the
formula-cell export of row `Sr/2`; the two PATH records are DEFINED through `keyOfQ7` at `Sr+2` /
`Sr+3` (so the frame's clauses hold at every `Sr`); the non-path slots read row `Sr/2`. -/
def recKeyQ7' (V : VerifierData F K hC S) (b : B0Cols F T) (st : State) (Sr j : ℕ) :
    RV.KeyVCL :=
  match j with
  | 0 => .export (b0NatAt V b fIdxCol (by decide) fIdx_round0 (Sr / 2)) true
  | 1 => if st = .s0 then keyOfQ7 V b MemoryTable.MState.verify_child (Sr + 2)
      else .export (b0NatAt V b (vIdxCol 0) (by decide) (vIdx_round0 0) (Sr / 2)) false
  | _ => if st = .s9 then keyOfQ7 V b MemoryTable.MState.verify_child (Sr + 3)
      else .export (b0NatAt V b (vIdxCol 1) (by decide) (vIdx_round0 1) (Sr / 2)) false

/-- **The frame's `recKey_s0`, for EVERY `S'`** (even or odd, on-shape or not). -/
theorem recKey_s0' (V : VerifierData F K hC S) (b : B0Cols F T) (Sr : ℕ) :
    recKeyQ7' V b .s0 Sr 1 = keyOfQ7 V b MemoryTable.MState.verify_child (Sr + 2) := by
  simp [recKeyQ7']

/-- **The frame's `recKey_s9` (`ExtraPremises.recKey_s9`), for EVERY `S'`.** -/
theorem recKey_s9' (V : VerifierData F K hC S) (b : B0Cols F T) (Sr : ℕ) :
    recKeyQ7' V b .s9 Sr 2 = keyOfQ7 V b MemoryTable.MState.verify_child (Sr + 3) := by
  simp [recKeyQ7']

/-- At the `s0` address of row `i`, `keyOfQ7` is the row's `(vIdx₀, axCol)` path key. -/
theorem keyOfQ7_s0 (V : VerifierData F K hC S) (b : B0Cols F T) (st : MState) (i : ℕ) :
    keyOfQ7 V b st (2 * i + 2) =
      .path (b0NatAt V b (vIdxCol 0) (by decide) (vIdx_round0 0) i)
        (b0NatAt V b axCol (by decide) axCol_round0 i) := by
  simp [keyOfQ7, par_s0, rowOf_s0]

/-- At the `s9` address of row `i`, `keyOfQ7` is the row's `(vIdx₁, axCol)` path key. -/
theorem keyOfQ7_s9 (V : VerifierData F K hC S) (b : B0Cols F T) (st : MState) (i : ℕ) :
    keyOfQ7 V b st (2 * i + 3) =
      .path (b0NatAt V b (vIdxCol 1) (by decide) (vIdx_round0 1) i)
        (b0NatAt V b axCol (by decide) axCol_round0 i) := by
  simp [keyOfQ7, par_s9, rowOf_s9]

/-- `axB0Q7` at both addresses of row `i` is the row's own `axCol` (what `joinRecordAxis` and
`RowFacts.ax0`/`ax9` read at `S+2` / `S+3`). -/
theorem axB0Q7_s0 (V : VerifierData F K hC S) (b : B0Cols F T) (i : ℕ) :
    axB0Q7 V b (2 * i + 2) = b0NatAt V b axCol (by decide) axCol_round0 i := by
  simp [axB0Q7, rowOf_s0]
theorem axB0Q7_s9 (V : VerifierData F K hC S) (b : B0Cols F T) (i : ℕ) :
    axB0Q7 V b (2 * i + 3) = b0NatAt V b axCol (by decide) axCol_round0 i := by
  simp [axB0Q7, rowOf_s9]

theorem recKeyQ7'_even (V : VerifierData F K hC S) (b : B0Cols F T) (st : State)
    (i j : ℕ) : recKeyQ7' V b st (2 * i) j = recKeyQ7 V b st i j := by
  have hdiv : 2 * i / 2 = i := by omega
  rcases j with _ | _ | j
  · simp [recKeyQ7', recKeyQ7, hdiv]
  · simp only [recKeyQ7', recKeyQ7, hdiv, keyOfQ7_s0]
  · simp only [recKeyQ7', recKeyQ7, hdiv, keyOfQ7_s9]

/-- The two path addresses of ONE row are distinct keys only when the row's two `vIdx` differ —
irrelevant: an `s0` row has no record 2 and an `s9` row no path record 1 (`recordCount`). What
matters is that no `keyOf` identity is FORCED across rows: the `keyOf_forces_collision`
hypothesis pair is now satisfied by `keyOfQ7` itself, at every `Sr` (see `recKey_s0'`, `recKey_s9'`). -/
theorem no_forced_collision (V : VerifierData F K hC S) (b : B0Cols F T) :
    ∃ keyOf : ℕ → RV.KeyVCL,
      (∀ Sr, recKeyQ7' V b .s0 Sr 1 = keyOf (Sr + 2)) ∧ (∀ Sr, recKeyQ7' V b .s9 Sr 2 = keyOf (Sr + 3)) :=
  ⟨keyOfQ7 V b MemoryTable.MState.verify_child, recKey_s0' V b, recKey_s9' V b⟩

variable [DecidableEq K] {C : TableSpec} {hC' : ℕ} {S' : MemShape}

/-- **The export key clause transfers to the doubled label** (`export_key_clauseQ7`). -/
theorem export_key_clauseQ7' (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin T.width → F[X])
    (i : Fin V.N) (st : State) (s : ℕ) (hs : s = 0 ∨ (s = 1 ∧ st ≠ .s0) ∨ (s = 2 ∧ st ≠ .s9)) :
    (RV.recordViewVCL F K K C S' hC').key 1 (recX11 V.basis (rawEnvQ7 V chalV pubVal Q i) s) =
      recKeyQ7' V (b0 (T := T) Q) st (2 * i) s := by
  rw [recKeyQ7'_even]; exact export_key_clauseQ7 V chalV pubVal Q i st s hs

/-- **The path key clause transfers to the doubled label** (`path_key_clauseQ7`). -/
theorem path_key_clauseQ7' (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin T.width → F[X])
    (i : Fin V.N) (s : ℕ) (hs : s < 2) :
    (RV.recordViewVCL F K K C S' hC').key 2 (recP V.basis (rawEnvQ7 V chalV pubVal Q i) s) =
      recKeyQ7' V (b0 (T := T) Q) (if s = 0 then .s0 else .s9) (2 * i) (s + 1) := by
  rw [recKeyQ7'_even]; exact path_key_clauseQ7 V chalV pubVal Q i s hs

end keys2


end

end VclL.Compute
end Nock.NockVMROM.Thm54
