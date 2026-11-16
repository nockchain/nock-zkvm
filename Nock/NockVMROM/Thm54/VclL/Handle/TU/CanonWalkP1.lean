/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/CanonWalkP1.lean

 **Completeness of the walk side gates `canonW`.**

 * §1 row level: `HonestW t n kr` (last-row mask, root mask `[i < kr]`, consecutive root serials strictly
 increasing with gaps below `2^31`, `qinv = 0` on the last row, certificate bits `certB8 L` with `L ≤ 60`);
 the honest aux `auxWH` (the bits of `ridx' − ridx − 1` on consecutive root rows, `0` elsewhere; the depth aux
 `y = b5(1−b2)(1−b3)`); `honest_gatesW`: every `canonW` gate vanishes at the honest aux.
 * §2 the side RAP: `canonW_of_honest` at the canonical layout.
 * §3 root order: reads sorted by root serial (`cells.idxOf`) give `walkRoots` strictly increasing in serial
 (`walkRoots_strict`).
 * §4 the honest J-8 walk trace columns (`certUp (wColHQBE …) lenB`) form an `HonestW` table (`honestW_cols`);
 `canonW_walkTr`: the honest walk trace at the canonical nodes satisfies `canonW` with aux `auxWH`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.J8GenClosed

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonWalkP1

open Nock Nock.Reified Nock.Framework Polynomial Module
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1 (bitZ bitZ_bool sum_bitZ bitSum_eval val_natCast_lt)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestK8 (certB8 certB8_le)

noncomputable section

/-! ## 1. Row level -/

section Rows
variable {p : ℕ} [Fact p.Prime]

/-- The gap between consecutive root serials at row `i`, minus one. -/
def drW (t : ℕ → ℕ → ZMod p) (i : ℕ) : ℕ := (t (i + 1) WChip.ridx).val - (t i WChip.ridx).val - 1

/-- **The honest walk aux** (column `c < 32` of row `i`): the bits of `drW` on a consecutive root pair
(`i + 1 < kr`), `0` elsewhere; at `c = 31` the depth aux `y = b5(1−b2)(1−b3)`. -/
def auxWH (t : ℕ → ℕ → ZMod p) (kr i c : ℕ) : ZMod p :=
  if c < 31 then (if i + 1 < kr then bitZ (drW t i) c else 0)
  else t i (WChip.bit0 + 5) * (1 - t i (WChip.bit0 + 2)) * (1 - t i (WChip.bit0 + 3))

/-- The honest walk side row: base columns `0..24`, then the `32` aux values, then `0`. -/
def fullW (t : ℕ → ℕ → ZMod p) (kr i j : ℕ) : ZMod p :=
  if j < 25 then t i j else if j < 57 then auxWH t kr i (j - 25) else 0

/-- **The hypotheses on an honest walk table** (`n` rows, `kr` roots). -/
structure HonestW (t : ℕ → ℕ → ZMod p) (n kr : ℕ) : Prop where
  kr_le : kr ≤ n
  isL : ∀ i < n, t i WChip.isL = if i + 1 = n then 1 else 0
  rM : ∀ i < n, t i WChip.rM = if i < kr then 1 else 0
  ridx : ∀ i, i + 1 < kr → (t i WChip.ridx).val < (t (i + 1) WChip.ridx).val ∧
    (t (i + 1) WChip.ridx).val - (t i WChip.ridx).val - 1 < 2 ^ 31
  qinv : ∀ i < n, i + 1 = n → t i WChip.qinv = 0
  bits : ∀ i < n, ∃ L ≤ 60, ∀ k < 6, t i (WChip.bit0 + k) = ((certB8 L k : ℕ) : ZMod p)

theorem fullW_base {t : ℕ → ℕ → ZMod p} {kr i j : ℕ} (hj : j < 25) : fullW t kr i j = t i j := by
  unfold fullW; exact ite_eq_left hj

theorem fullW_aux {t : ℕ → ℕ → ZMod p} {kr i c : ℕ} (hc : c < 32) : fullW t kr i (25 + c) = auxWH t kr i c := by
  unfold fullW
  rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

/-- The depth-certificate gate `y(1 − b4)(1 − b0 b1)` vanishes at every honest certificate (`L ≤ 60`). -/
theorem cert8_gate : ∀ L < 61, certB8 L 5 * (1 - certB8 L 2) * (1 - certB8 L 3) * (1 - certB8 L 4) *
    (1 - certB8 L 0 * certB8 L 1) = 0 := by decide +kernel

theorem cert8_gate_cast (L : ℕ) (hL : L ≤ 60) :
    ((certB8 L 5 : ℕ) : ZMod p) * (1 - ((certB8 L 2 : ℕ) : ZMod p)) * (1 - ((certB8 L 3 : ℕ) : ZMod p)) *
      (1 - ((certB8 L 4 : ℕ) : ZMod p)) * (1 - ((certB8 L 0 : ℕ) : ZMod p) * ((certB8 L 1 : ℕ) : ZMod p)) = 0 := by
  have h := cert8_gate L (by omega)
  have b0 := certB8_le L 0
  have b1 := certB8_le L 1
  have b2 := certB8_le L 2
  have b3 := certB8_le L 3
  have b4 := certB8_le L 4
  have h01 : certB8 L 0 * certB8 L 1 ≤ 1 := (Nat.mul_le_mul b0 b1).trans (by norm_num)
  have := congrArg (fun x : ℕ => (x : ZMod p)) h
  simp only [Nat.cast_mul, Nat.cast_sub b2, Nat.cast_sub b3, Nat.cast_sub b4, Nat.cast_sub h01, Nat.cast_one,
    Nat.cast_zero] at this
  exact this

/-- **Completeness of the walk side gates**: at every row of an honest walk table, with the next row read as the
honest next row (any value on the last row), every `canonW` gate vanishes at the honest aux. -/
theorem honest_gatesW {t : ℕ → ℕ → ZMod p} {n kr i : ℕ} (H : HonestW t n kr) (hi : i < n)
    (nx ch pu : ℕ → ZMod p) (hnx : i + 1 < n → nx = fullW t kr (i + 1)) :
    ∀ g ∈ canonWGates (F := ZMod p), g.eval ⟨fullW t kr i, nx, ch, pu⟩ = 0 := by
  -- the mask `(1 − isL)·rM·rM'`
  have hm : (1 - fullW t kr i WChip.isL) * fullW t kr i WChip.rM * nx WChip.rM =
      if i + 1 < kr then 1 else 0 := by
    rw [fullW_base (by decide), fullW_base (by decide), H.isL i hi, H.rM i hi]
    by_cases h1 : i + 1 < kr
    · have hn1 : i + 1 < n := lt_of_lt_of_le h1 H.kr_le
      rw [hnx hn1, fullW_base (by decide), H.rM (i + 1) hn1]
      simp [show ¬ i + 1 = n by omega, show i < kr by omega, h1]
    · by_cases hl : i + 1 = n
      · simp [hl, h1, H.kr_le]
      · rw [hnx (by omega), fullW_base (by decide), H.rM (i + 1) (by omega)]
        simp [h1]
  have hdr : ∀ c < 31, fullW t kr i (wA + c) = if i + 1 < kr then bitZ (drW t i) c else 0 := fun c hc => by
    rw [show wA + c = 25 + c from rfl, fullW_aux (by omega)]
    unfold auxWH; rw [ite_eq_left hc]
  have hbit : ∀ k < 6, fullW t kr i (WChip.bit0 + k) = t i (WChip.bit0 + k) := fun k hk =>
    fullW_base (by simp only [WChip.bit0]; omega)
  unfold canonWGates
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false]
  rintro g ((((⟨c, hc, rfl⟩ | rfl) | ⟨c, hc, rfl⟩) | (rfl | rfl | rfl)))
  · -- booleanity of the gap bits
    simp only [CoeffExpr.eval, cv, boolE]
    rw [hdr c hc]
    split_ifs
    · rcases bitZ_bool (p := p) (drW t i) c with h | h <;> rw [h] <;> ring
    · ring
  · -- the root order gate
    simp only [CoeffExpr.eval, cv, nv, notE, rootPairW, bitSum_eval]
    rw [hm]
    by_cases h1 : i + 1 < kr
    · rw [ite_eq_left h1, one_mul]
      have hn1 : i + 1 < n := lt_of_lt_of_le h1 H.kr_le
      obtain ⟨hlt, hlt31⟩ := H.ridx i h1
      rw [Finset.sum_congr rfl fun c hc => by rw [hdr c (Finset.mem_range.mp hc), ite_eq_left h1], sum_bitZ,
        Nat.mod_eq_of_lt (show drW t i < 2 ^ 31 from hlt31), hnx hn1, fullW_base (by decide),
        fullW_base (by decide)]
      unfold drW
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast
      simp only [ZMod.natCast_zmod_val]
      ring
    · rw [ite_eq_right h1, zero_mul]
  · -- the gap bits vanish off the mask
    simp only [CoeffExpr.eval, cv, nv, notE, rootPairW]
    rw [hm, hdr c hc]
    by_cases h1 : i + 1 < kr
    · rw [ite_eq_left h1]; ring
    · rw [ite_eq_right h1, ite_eq_right h1]; ring
  · -- `isL · qinv`
    simp only [CoeffExpr.eval, cv]
    rw [fullW_base (by decide), fullW_base (by decide), H.isL i hi]
    by_cases hl : i + 1 = n
    · rw [H.qinv i hi hl]; ring
    · rw [ite_eq_right hl]; ring
  · -- the depth aux definition
    simp only [CoeffExpr.eval, cv, notE, WChip.bt]
    rw [show wy = 25 + 31 from rfl, fullW_aux (by omega), hbit 5 (by omega), hbit 2 (by omega),
      hbit 3 (by omega)]
    unfold auxWH; rw [ite_eq_right (by omega)]; ring
  · -- the depth certificate gate
    simp only [CoeffExpr.eval, cv, notE, WChip.bt]
    rw [show wy = 25 + 31 from rfl, fullW_aux (by omega), hbit 4 (by omega), hbit 0 (by omega),
      hbit 1 (by omega)]
    unfold auxWH; rw [ite_eq_right (by omega)]
    obtain ⟨L, hL, hb⟩ := H.bits i hi
    rw [hb 5 (by omega), hb 2 (by omega), hb 3 (by omega), hb 4 (by omega), hb 0 (by omega), hb 1 (by omega)]
    exact cert8_gate_cast L hL

end Rows


/-! ## 2. The side RAP -/

section Bridge
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]

/-- The row values of the walk side trace at the nodes `ω^i`. -/
def vW (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) (ω : ZMod p) (i j : ℕ) : ZMod p :=
  (Reify.envOfTrace (sideWQ tr ax) ω (ω ^ i) (fun _ => 0) (fun _ => 0)).trace j

theorem envOfTrace_vW (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) (ω : ZMod p) (i : ℕ) :
    Reify.envOfTrace (sideWQ tr ax) ω (ω ^ i) (fun _ => 0) (fun _ => 0) =
      ⟨vW tr ax ω i, vW tr ax ω (i + 1), fun _ => 0, fun _ => 0⟩ := by
  rw [show vW tr ax ω (i + 1) = fun j =>
      (Reify.envOfTrace (sideWQ tr ax) ω (ω * ω ^ i) (fun _ => 0) (fun _ => 0)).trace j by
    funext j; simp only [vW, pow_succ']]
  rfl

theorem vW_base (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) (ω : ZMod p) (i : ℕ) {j : ℕ} (hj : j < 25) :
    vW tr ax ω i j = (tr.W ⟨j, by omega⟩).eval (ω ^ i) := by
  have hw : j < (canonWT (F := ZMod p)).width 3 := by rw [canonWT_width]; omega
  unfold vW Reify.envOfTrace
  simp only [hw, ↓reduceDIte]
  unfold sideWQ
  simp only [hj, ↓reduceDIte]

theorem vW_aux (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) (ω : ZMod p) (i : ℕ) {c : ℕ} (hc : c < 32) :
    vW tr ax ω i (25 + c) = (ax.W ⟨c, hc⟩).eval (ω ^ i) := by
  have hw : 25 + c < (canonWT (F := ZMod p)).width 3 := by rw [canonWT_width]; omega
  have hn : ¬ (25 + c < 25) := by omega
  unfold vW Reify.envOfTrace
  simp only [hw, ↓reduceDIte]
  unfold sideWQ
  simp only [hn, ↓reduceDIte]
  exact congrArg (fun k => (ax.W k).eval (ω ^ i)) (Fin.ext (by simp))

theorem vW_out (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) (ω : ZMod p) (i : ℕ) {j : ℕ} (hj : 57 ≤ j) :
    vW tr ax ω i j = 0 := by
  have hw : ¬ j < (canonWT (F := ZMod p)).width 3 := by rw [canonWT_width]; omega
  unfold vW Reify.envOfTrace; simp only [hw, ↓reduceDIte]

/-- **The honest side trace satisfies `canonW`**: if, at the canonical layout, the walk side trace's row values
are the honest side rows `fullW t kr` of an honest walk table, `canonW` is satisfied. -/
theorem canonW_of_honest (b : Basis (Fin 3) (ZMod p) K) {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1}
    {c : P8PublicClaim} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)} {t : ℕ → ℕ → ZMod p} {kr : ℕ}
    (H : HonestW t (canonPb hpG sz c).nW kr)
    (hrow : ∀ i < (canonPb hpG sz c).nW, vW tr ax (canonPb hpG sz c).orbitW.ω i = fullW t kr i) :
    (canonW b (canonPb hpG sz c)).Satisfies (sideWQ tr ax) := by
  refine (expandChip_satisfies_iff_language canonWT b (fun _ => 0) (fun _ => 0) (canonPb hpG sz c).orbitW
    (rowNodeSet (canonPb hpG sz c).nodesW) (sideWQ tr ax)).mpr fun x hx => ?_
  obtain ⟨⟨i, hi⟩, rfl⟩ := (mem_rowNodeSet_iff _ x).mp hx
  have hx' : (canonPb hpG sz c).nodesW ⟨i, hi⟩ = (canonPb hpG sz c).orbitW.ω ^ i := rfl
  have hE : Reify.envOfTrace (sideWQ tr ax) (canonPb hpG sz c).orbitW.ω ((canonPb hpG sz c).orbitW.ω ^ i)
      (fun _ => 0) (fun _ => 0) =
      ⟨fullW t kr i, vW tr ax (canonPb hpG sz c).orbitW.ω (i + 1), fun _ => 0, fun _ => 0⟩ := by
    rw [envOfTrace_vW, hrow i hi]
  refine ⟨fun g hg => ?_, fun g hg => absurd hg List.not_mem_nil, fun g hg => absurd hg List.not_mem_nil,
    fun g hg => absurd hg List.not_mem_nil⟩
  rw [hx']
  exact (congrArg (CoeffExpr.eval g) hE).trans
    (honest_gatesW H hi _ (fun _ => 0) (fun _ => 0) (fun h1 => hrow (i + 1) h1) g hg)

end Bridge

/-! ## 3. Root order -/

section Roots
open Nock.NockVMROM.Thm54.VclL.GenWalk

/-- **Reads sorted by root serial give strictly increasing root serials**: `walkRoots` (the deduplicated
path-kind read roots) is strictly increasing in `cells.idxOf` when the path-kind roots are non-decreasing in it and
every root is a cell of `cells`. -/
theorem walkRoots_strict (cells : List Noun) (reads : List (Noun × ℕ))
    (hsort : ((pathKind reads).map Prod.fst).Pairwise fun a b => cells.idxOf a ≤ cells.idxOf b)
    (hmem : ∀ r ∈ walkRoots reads, r ∈ cells) :
    (walkRoots reads).Pairwise fun a b => cells.idxOf a < cells.idxOf b := by
  have hle : (walkRoots reads).Pairwise fun a b => cells.idxOf a ≤ cells.idxOf b :=
    hsort.sublist (List.dedup_sublist _)
  have hnd : (walkRoots reads).Nodup := List.nodup_dedup _
  refine (hle.and hnd).imp_of_mem fun {a b} ha hb h => ?_
  rcases Nat.lt_or_ge (cells.idxOf a) (cells.idxOf b) with h1 | h1
  · exact h1
  · exfalso
    apply h.2
    have he : cells.idxOf a = cells.idxOf b := le_antisymm h.1 h1
    have ia := List.idxOf_lt_length_iff.mpr (hmem a ha)
    have ib := List.idxOf_lt_length_iff.mpr (hmem b hb)
    rw [← List.getElem_idxOf ia, ← List.getElem_idxOf ib]
    simp only [he]

/-- The root of walk row `i < kr` is the `i`-th read root. -/
theorem wTrie_root (cells : List Noun) (reads : List (Noun × ℕ)) (hne : walkRoots reads ≠ []) {i : ℕ}
    (hi : i < krW cells reads) :
    ∃ hiR : i < (walkRoots reads).length, (wTrie cells reads i).label.root = (walkRoots reads)[i] := by
  have hsplit := Nock.Walk.bfsForest_eq_append_flatMap _ (walkForest_ne_nil cells reads)
  have hF : walkForest cells reads = (walkRoots reads).map fun r => trie r r [] (targetsOf reads r) := by
    unfold walkForest; rw [ite_eq_right hne]
  have hil : i < (walkForest cells reads).length := hi
  have hiR : i < (walkRoots reads).length := by rw [hF, List.length_map] at hil; exact hil
  refine ⟨hiR, ?_⟩
  have hw : wTrie cells reads i = (walkForest cells reads)[i] := by
    unfold wTrie walkRows
    rw [List.getD_eq_getElem?_getD, hsplit, List.getElem?_append_left hil, List.getElem?_eq_getElem hil]
    rfl
  rw [hw]
  simp only [hF, List.getElem_map]
  exact (trie_label _ _ _ _).2.2

/-- **Consecutive root rows have strictly increasing root serials** (gaps below `cells.length`). -/
theorem root_serial_lt (cells : List Noun) (reads : List (Noun × ℕ))
    (hsort : ((pathKind reads).map Prod.fst).Pairwise fun a b => cells.idxOf a ≤ cells.idxOf b)
    (hmem : ∀ r ∈ walkRoots reads, r ∈ cells) {i : ℕ} (hi : i + 1 < krW cells reads) :
    cells.idxOf (wTrie cells reads i).label.root < cells.idxOf (wTrie cells reads (i + 1)).label.root ∧
      cells.idxOf (wTrie cells reads (i + 1)).label.root < cells.length := by
  by_cases hne : walkRoots reads = []
  · exfalso
    have : krW cells reads = 1 := by unfold krW walkForest; rw [ite_eq_left hne]; rfl
    omega
  obtain ⟨h0, e0⟩ := wTrie_root cells reads hne (i := i) (by omega)
  obtain ⟨h1, e1⟩ := wTrie_root cells reads hne hi
  rw [e0, e1]
  refine ⟨List.pairwise_iff_getElem.mp (walkRoots_strict cells reads hsort hmem) _ _ h0 h1 (by omega), ?_⟩
  exact List.idxOf_lt_length_iff.mpr (hmem _ (List.getElem_mem h1))

end Roots


/-! ## 4. The honest walk trace columns -/

section Cols
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.GenWalk
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)

/-- The row values of a column function (`0` past the table). -/
def rowsW {n : ℕ} (hn : 0 < n) (colF : ℕ → Fin n → ZMod p) : ℕ → ℕ → ZMod p := fun i j =>
  if h : i < n then fullCol hn colF j ⟨i, h⟩ else 0

/-- **The honest J-8 walk column function** (`walkTrWE`'s columns). -/
abbrev colWH {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
    (orbit : StrictExtension.StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
    (E : Noun → Nock.ComputeTable.FP (Quad (algebraMap (ZMod p) K δ))) (γ ρ : Quad (algebraMap (ZMod p) K δ))
    (cells : List Noun) (reads : List (Noun × ℕ)) (kLv vLv kRv vRv : Fin n → ZMod p) : ℕ → Fin n → ZMod p :=
  HonestK8.certUp (ComplJ8Enc.wColHQBE δ b hn nodes orbit chals pubs E γ ρ cells reads kLv vLv kRv vRv)
    (ComplJ8Walk.lenB cells reads)

variable {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {orbit : StrictExtension.StrictOrbitDomain (ZMod p) 3 h}
  {chals pubs : ℕ → K} {E : Noun → Nock.ComputeTable.FP (Quad (algebraMap (ZMod p) K δ))}
  {γ ρ : Quad (algebraMap (ZMod p) K δ)} {cells : List Noun} {reads : List (Noun × ℕ)}
  {kLv vLv kRv vRv : Fin n → ZMod p}

theorem colWH_named {j : ℕ} (h2 : 2 ≤ j) (hj : j < 14) (i : Fin n) :
    fullCol hn (colWH δ b hn nodes orbit chals pubs E γ ρ cells reads kLv vLv kRv vRv) j i =
      WalkVals.named (ComplJ8Enc.walkRow0E δ E cells reads (chals 0) (chals 1) i) (krW cells reads) i j := by
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  have h14 : ¬ (14 ≤ j ∧ j < 21) := by omega
  have h21 : j < 21 := by omega
  have h15 : j < 15 := by omega
  have h14' : ¬ 14 ≤ j := by omega
  simp only [fullCol, h0, h1, ↓reduceIte, colWH, HonestK8.certUp, h14', false_and, ComplJ8Enc.wColHQBE,
    WalkTraceHQ.colHQ, extColF, h21, ComplJ8Enc.wColBE, walkCol, WalkVals.base, h15]
  rfl

theorem colWH_bit {k : ℕ} (hk : k < 6) (i : Fin n) :
    fullCol hn (colWH δ b hn nodes orbit chals pubs E γ ρ cells reads kLv vLv kRv vRv) (WChip.bit0 + k) i =
      ((certB8 (ComplJ8Walk.lenB cells reads i) k : ℕ) : ZMod p) := by
  have h0 : WChip.bit0 + k ≠ 0 := by simp only [WChip.bit0]; omega
  have h1 : WChip.bit0 + k ≠ 1 := by simp only [WChip.bit0]; omega
  have h14 : 14 ≤ WChip.bit0 + k ∧ WChip.bit0 + k < 21 := by simp only [WChip.bit0]; omega
  simp only [fullCol, h0, h1, ↓reduceIte, colWH, HonestK8.certUp, h14, and_self, HonestK8.fixVal8]
  have h14' : WChip.bit0 + k ≠ 14 := by simp only [WChip.bit0]; omega
  rw [ite_eq_right h14']
  congr 3
  simp only [WChip.bit0]; omega

/-- **The honest walk trace rows form an `HonestW` table**, given reads whose path-kind roots are sorted by list
position and are cells of the list, fewer than `min p (2^31 + 1)` cells, and every row of depth `≤ 60`. -/
theorem honestW_cols (hN : n = (walkRows cells reads).length)
    (hsort : ((pathKind reads).map Prod.fst).Pairwise fun a b => cells.idxOf a ≤ cells.idxOf b)
    (hmem : ∀ r ∈ walkRoots reads, r ∈ cells) (hlenp : cells.length < p) (h31 : cells.length ≤ 2 ^ 31)
    (hle : ∀ i < n, (wTrie cells reads i).label.bits.length ≤ 60) :
    HonestW (rowsW hn (colWH δ b hn nodes orbit chals pubs E γ ρ cells reads kLv vLv kRv vRv)) n
      (krW cells reads) := by
  have hnamed : ∀ i (hi : i < n) j, 2 ≤ j → j < 14 →
      rowsW hn (colWH δ b hn nodes orbit chals pubs E γ ρ cells reads kLv vLv kRv vRv) i j =
        WalkVals.named (ComplJ8Enc.walkRow0E δ E cells reads (chals 0) (chals 1) i) (krW cells reads) i j :=
    fun i hi j h2 hj => by simp only [rowsW, hi, ↓reduceDIte]; exact colWH_named δ b h2 hj ⟨i, hi⟩
  refine ⟨hN ▸ krW_le_rows cells reads, fun i hi => ?_, fun i hi => ?_, fun i hi1 => ?_, fun i hi hl => ?_,
    fun i hi => ?_⟩
  · simp only [rowsW, hi, ↓reduceDIte, fullCol, WChip.isL, one_ne_zero, ↓reduceIte, Fin.ext_iff]
    by_cases hl : i + 1 = n
    · rw [ite_eq_left (by omega), ite_eq_left hl]
    · rw [ite_eq_right (by omega), ite_eq_right hl]
  · rw [show WChip.rM = 2 from rfl, hnamed i hi 2 (by decide) (by decide)]; rfl
  · have hkr := hN ▸ krW_le_rows cells reads
    rw [show WChip.ridx = 5 from rfl, hnamed i (by omega) 5 (by decide) (by decide),
      hnamed (i + 1) (by omega) 5 (by decide) (by decide)]
    simp only [WalkVals.named, ComplJ8Enc.walkRow0E]
    obtain ⟨hlt, hl1⟩ := root_serial_lt cells reads hsort hmem hi1
    rw [val_natCast_lt (by omega), val_natCast_lt (by omega)]
    exact ⟨hlt, by omega⟩
  · rw [show WChip.qinv = 13 from rfl, hnamed i hi 13 (by decide) (by decide)]
    simp only [WalkVals.named, ComplJ8Enc.walkRow0E]
    have hq := (walkRows_queue cells reads).2.1
    rw [hl, hN, hq]; simp
  · refine ⟨(wTrie cells reads i).label.bits.length, hle i hi, fun k hk => ?_⟩
    simp only [rowsW, hi, ↓reduceDIte]
    exact colWH_bit δ b hk ⟨i, hi⟩


/-- **The extra pin (E10) at the honest walk**: with no path-kind read, the single dummy walk row points at cell row `0`
(`idx = cells.idxOf (cells.headD _) = 0` for a non-empty cell list, whatever its order). -/
theorem dummy_idx_zero (hn : 0 < n) (hne : walkRoots reads = []) (hcs : cells ≠ []) :
    rowsW hn (colWH δ b hn nodes orbit chals pubs E γ ρ cells reads kLv vLv kRv vRv) 0 WChip.idx = 0 := by
  rw [show WChip.idx = 3 from rfl]
  simp only [rowsW, hn, ↓reduceDIte]
  rw [colWH_named δ b (by decide) (by decide) ⟨0, hn⟩]
  simp only [WalkVals.named, ComplJ8Enc.walkRow0E]
  have hw : wTrie cells reads 0 = trie (cells.headD (.atom 0)) (cells.headD (.atom 0)) [] [] := by
    have hsplit := Nock.Walk.bfsForest_eq_append_flatMap _ (walkForest_ne_nil cells reads)
    have hF : walkForest cells reads = [trie (cells.headD (.atom 0)) (cells.headD (.atom 0)) [] []] := by
      unfold walkForest; rw [ite_eq_left hne]
    unfold wTrie walkRows
    rw [hsplit, hF]; rfl
  rw [hw, (trie_label _ _ _ _).1]
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hcs
  simp

end Cols

/-! ## 5. At the canonical layout -/

section Canon
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.GenWalk
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]

/-- The nodes `i ↦ ω^i` of an `n`-row table. -/
def nodesN (ω : ZMod p) (n : ℕ) : Fin n → ZMod p := fun i => ω ^ (i : ℕ)

/-- **The honest walk aux interpolants**: aux column `c` interpolates `auxWH t kr · c` at the nodes. -/
def auxWOf {n : ℕ} (nodes : Fin n → ZMod p) (t : ℕ → ℕ → ZMod p) (kr : ℕ) : Fin 32 → (ZMod p)[X] :=
  fun c => Lagrange.interpolate Finset.univ nodes (fun i => auxWH t kr i c)

/-- The canonical layout's walk nodes are distinct. -/
theorem nodesW_inj (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (c : P8PublicClaim) :
    Function.Injective (nodesN (canonPb hpG sz c).orbitW.ω (canonPb hpG sz c).nW) := by
  intro a a' h
  have hord : orderOf (canonPb hpG sz c).orbitW.ω = 3 * 2 ^ (sz c).ht := (canonPb hpG sz c).orbitW.order_ω
  have hfit := (sz c).fit_ht
  have hn : (sz c).nW ≤ 2 ^ (sz c).ht := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hfit
  have ha : (a : ℕ) < (sz c).nW := a.isLt
  have ha' : (a' : ℕ) < (sz c).nW := a'.isLt
  exact Fin.ext (pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hord]; omega)
    (by rw [Set.mem_Iio, hord]; omega) h)

/-- **`canonW` at an honest column function**: the walk trace interpolates `fullCol colF` at the canonical
nodes, the aux interpolates `auxWH`, and the row values form an `HonestW` table. -/
theorem canonW_of_cols (b : Basis (Fin 3) (ZMod p) K) {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1}
    {c : P8PublicClaim} {n kr : ℕ} (hn : 0 < n) (hnW : (canonPb hpG sz c).nW = n) (colF : ℕ → Fin n → ZMod p)
    {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (hW : ∀ j, tr.W j = honestQ hn (nodesN (canonPb hpG sz c).orbitW.ω n) colF 166 j)
    (hax : ax.W = auxWOf (nodesN (canonPb hpG sz c).orbitW.ω n) (rowsW hn colF) kr)
    (H : HonestW (rowsW hn colF) n kr) :
    (canonW b (canonPb hpG sz c)).Satisfies (sideWQ tr ax) := by
  subst hnW
  refine canonW_of_honest b H fun i hi => ?_
  have hinj := nodesW_inj hpG sz c
  funext j
  by_cases hj : j < 25
  · rw [vW_base _ _ _ _ hj, hW, fullW_base hj]
    have := honestQ_eval hn (nodesN _ _) hinj colF (w := 166) ⟨j, by omega⟩ ⟨i, hi⟩
    simp only [nodesN] at this
    rw [this]; simp [rowsW, hi]
  · by_cases hj2 : j < 57
    · obtain ⟨c', rfl⟩ : ∃ c', j = 25 + c' := ⟨j - 25, by omega⟩
      have hc : c' < 32 := by omega
      rw [vW_aux _ _ _ _ hc, fullW_aux hc, hax]
      exact Lagrange.eval_interpolate_at_node (fun k : Fin _ => auxWH (rowsW hn colF) kr k c') hinj.injOn
        (Finset.mem_univ (⟨i, hi⟩ : Fin _))
    · rw [vW_out _ _ _ _ (by omega)]; unfold fullW; simp [hj, hj2]

/-- **The honest J-8 walk trace at the canonical layout satisfies `canonW` with aux `auxWH`** (`walkTrWE` at the
canonical walk nodes; reads with path-kind roots sorted by list position and in the cell list, the row-depth
bound `≤ 60`, fewer than `min p (2^31 + 1)` cells). -/
theorem canonW_walkTr [Fintype K] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
    (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
    (b : Basis (Fin 3) (ZMod p) K) (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (c : P8PublicClaim)
    (chalsF pubsF : SVFrame.Coins FrameJ8.frameJ8 K → ℕ → K)
    (γF ρF : SVFrame.Coins FrameJ8.frameJ8 K → Quad (algebraMap (ZMod p) K δ))
    (EF : SVFrame.Coins FrameJ8.frameJ8 K → Noun → Nock.ComputeTable.FP (Quad (algebraMap (ZMod p) K δ)))
    (cells : List Noun) (reads : List (Noun × ℕ)) {n : ℕ} (hn : 0 < n) (kLv vLv kRv vRv : Fin n → ZMod p)
    (χ : SVFrame.Coins FrameJ8.frameJ8 K)
    (hN : n = (walkRows cells reads).length) (hnW : (canonPb hpG sz c).nW = n)
    (hsort : ((pathKind reads).map Prod.fst).Pairwise fun a b => cells.idxOf a ≤ cells.idxOf b)
    (hmem : ∀ r ∈ walkRoots reads, r ∈ cells) (hlenp : cells.length < p) (h31 : cells.length ≤ 2 ^ 31)
    (hle : ∀ i < n, (wTrie cells reads i).label.bits.length ≤ 60)
    {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (htr : tr.W = ComplJ8Enc.walkTrWE δ b hn (nodesN (canonPb hpG sz c).orbitW.ω n) (canonPb hpG sz c).orbitW
      chalsF pubsF γF ρF EF cells reads kLv vLv kRv vRv χ)
    (hax : ax.W = auxWOf (nodesN (canonPb hpG sz c).orbitW.ω n)
      (rowsW hn (colWH δ b hn (nodesN (canonPb hpG sz c).orbitW.ω n) (canonPb hpG sz c).orbitW (chalsF χ)
        (pubsF χ) (EF χ) (γF χ) (ρF χ) cells reads kLv vLv kRv vRv)) (krW cells reads)) :
    (canonW b (canonPb hpG sz c)).Satisfies (sideWQ tr ax) :=
  canonW_of_cols b hn hnW _ (fun j => by rw [htr]; rfl) hax
    (honestW_cols δ b hN hsort hmem hlenp h31 hle)

/-- **(D) for honest interpolated columns**: every `honestQ` column over `n` distinct nodes has degree `< n`. -/
theorem honestQ_degree_lt {n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (hinj : Function.Injective nodes)
    (col : ℕ → Fin n → ZMod p) {w : ℕ} (j : Fin w) : (honestQ hn nodes col w j).degree < (n : WithBot ℕ) := by
  have := Lagrange.degree_interpolate_lt (s := Finset.univ) (fullCol hn col j) hinj.injOn
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact this

/-- **(D) for the honest aux columns**: degree `< n`. -/
theorem auxWOf_degree_lt {n : ℕ} (nodes : Fin n → ZMod p) (hinj : Function.Injective nodes) (t : ℕ → ℕ → ZMod p) (kr : ℕ) (c : Fin 32) :
    (auxWOf nodes t kr c).degree < (n : WithBot ℕ) := by
  have := Lagrange.degree_interpolate_lt (s := Finset.univ) (fun i : Fin n => auxWH t kr i c) hinj.injOn
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact this


/-- **The extra pin (E10) at the canonical trace**: with no path-kind read, the walk trace's `idx` column vanishes at the first
canonical walk node. -/
theorem canon_dummy_idx [Fintype K] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
    (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
    (b : Basis (Fin 3) (ZMod p) K) (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (c : P8PublicClaim)
    (chalsF pubsF : SVFrame.Coins FrameJ8.frameJ8 K → ℕ → K)
    (γF ρF : SVFrame.Coins FrameJ8.frameJ8 K → Quad (algebraMap (ZMod p) K δ))
    (EF : SVFrame.Coins FrameJ8.frameJ8 K → Noun → Nock.ComputeTable.FP (Quad (algebraMap (ZMod p) K δ)))
    (cells : List Noun) (reads : List (Noun × ℕ)) {n : ℕ} (hn : 0 < n) (kLv vLv kRv vRv : Fin n → ZMod p)
    (χ : SVFrame.Coins FrameJ8.frameJ8 K) (hnW : (canonPb hpG sz c).nW = n)
    (hne : walkRoots reads = []) (hcs : cells ≠ []) {tr : TrJ8 (ZMod p)}
    (htr : tr.W = ComplJ8Enc.walkTrWE δ b hn (nodesN (canonPb hpG sz c).orbitW.ω n) (canonPb hpG sz c).orbitW
      chalsF pubsF γF ρF EF cells reads kLv vLv kRv vRv χ) :
    (tr.W ⟨WChip.idx, by decide⟩).eval ((canonPb hpG sz c).nodesW ⟨0, hnW ▸ hn⟩) = 0 := by
  have hinj : Function.Injective (nodesN (canonPb hpG sz c).orbitW.ω n) := by
    have := nodesW_inj hpG sz c; subst hnW; exact this
  have h0 : (canonPb hpG sz c).nodesW ⟨0, hnW ▸ hn⟩ = nodesN (canonPb hpG sz c).orbitW.ω n ⟨0, hn⟩ := by
    simp [nodesN, canonPb, canonPbOf, nodesG]
  rw [h0, htr]
  have := honestQ_eval hn (nodesN (canonPb hpG sz c).orbitW.ω n) hinj
    (colWH δ b hn (nodesN (canonPb hpG sz c).orbitW.ω n) (canonPb hpG sz c).orbitW (chalsF χ) (pubsF χ) (EF χ)
      (γF χ) (ρF χ) cells reads kLv vLv kRv vRv) (w := 166) ⟨WChip.idx, by decide⟩ ⟨0, hn⟩
  refine this.trans ?_
  have hd := dummy_idx_zero δ b (nodes := nodesN (canonPb hpG sz c).orbitW.ω n) (orbit := (canonPb hpG sz c).orbitW)
    (chals := chalsF χ) (pubs := pubsF χ) (E := EF χ) (γ := γF χ) (ρ := ρF χ) (kLv := kLv) (vLv := vLv)
    (kRv := kRv) (vRv := vRv) hn hne hcs
  simpa [rowsW, hn] using hd

end Canon

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonWalkP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonWalkP1.honest_gatesW
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonWalkP1.canonW_of_honest
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonWalkP1.walkRoots_strict
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonWalkP1.root_serial_lt
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonWalkP1.honestW_cols
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonWalkP1.canonW_of_cols
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonWalkP1.canonW_walkTr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonWalkP1.auxWOf_degree_lt
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonWalkP1.honestQ_degree_lt
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonWalkP1.dummy_idx_zero
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonWalkP1.canon_dummy_idx
