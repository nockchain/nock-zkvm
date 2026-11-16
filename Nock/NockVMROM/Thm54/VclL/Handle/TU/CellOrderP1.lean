/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/CellOrderP1.lean

 **The cell row order of `canonM`: soundness of the sort gadget, distinct nouns, set ⇒ list.** It reads the side gates `canonMGates` of `StatementP1` and the cell table's base gates
 `Cell.baseGates`.

 Setting: a table of row values `v : ℕ → ℕ → ZMod p` (row `i`, column `j`; the side trace's columns: the `134`
 cell base columns, then the `200` aux columns at `SideM.A = 134`), with `n` rows. `envAt v i` is the gate
 environment of row `i` (current row `v i`, next row `v (i+1)`). `TableM v n` collects the hypotheses: every
 side gate and every cell base gate vanishes at every row, and the two mask columns are `[i = 0]`, `[i = n−1]`.

 * §1 `LexLt` (strict lexicographic order on 8-component natural keys), `eq_of_pairwise_of_mem_iff` (two lists,
 pairwise in an asymmetric relation, with the same members, are equal).
 * §2–§4 evaluation of the side gates (`MRow`) and the cell base gates (`CellFacts`); `step_field`: the one-hot
 / first-difference / `bitSum d 62` argument at one row.
 * §5 `keyNat t k` (the natural value of key component `k` at row values `t`); `TableM.step`: adjacent rows
 (outside the last) have `LexLt` keys; `TableM.sorted`, `TableM.keys_pairwise` (the row-key list is
 `Pairwise LexLt`), `TableM.idx_row` (`idx = i`), `TableM.keys_ne`.
 * §6 `limbs_canon`: the limbs of `x = w·id + (1−w)·a` are canonical, `(h, l) = (x.val / 2^32, x.val % 2^32)`
 (Goldilocks; the inverse-or-zero column forces `h = 2^32 − 1 ⇒ l = 0`).
 * §7 nouns: `nCells`, the table-independent noun order `nlt` (rank first, then the children, atoms before
 cells, atoms by value), its asymmetry, transitivity and trichotomy; `sortKey` (merge sort by `nlt`) with
 `sortKey_perm`, `sortKey_pairwise`.
 * §8 `NounLink` (each row's noun is a cell whose children are an atom read from the atom column or the noun of
 the row whose serial the side carries, with that row's rank); `TableM.rank_eq_cells`;
 **`TableM.nouns_sorted`**: the nouns of a sorted linked table are strictly increasing in `nlt`
 (by induction on the noun: child serials are compared first); hence distinct (`nouns_inj`).
 * §9 set ⇒ list: two such tables with the same noun SET have the same noun LIST (`nouns_eq_of_set`), and then
 the same `idx, idL, idR, wL, wR, aL, aR, lo, hi` row by row (`rows_eq_of_set`); provider records that carry
 `idx` in some coordinate are pairwise distinct across rows (`records_nodup`).
 * §10 the bridge from `(canonM b Pb).Satisfies (sideMQ tr ax)` at `Pb = canonPb …` to the row-local gates, and
 the transfer of the cell base gates from any environment that agrees on the first `129` columns.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1

open Nock Nock.Reified Nock.Framework Polynomial Module
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)

noncomputable section

/-! ## 1. The lexicographic key order and set ⇒ list -/

/-- **Strict lexicographic order** on 8-component natural keys. -/
def LexLt (a b : ℕ → ℕ) : Prop := ∃ k < 8, (∀ j < k, a j = b j) ∧ a k < b k

theorem LexLt.irrefl (a : ℕ → ℕ) : ¬ LexLt a a := fun ⟨_, _, _, h⟩ => lt_irrefl _ h

theorem LexLt.trans {a b c : ℕ → ℕ} (h1 : LexLt a b) (h2 : LexLt b c) : LexLt a c := by
  obtain ⟨k, hk8, hk, hlt⟩ := h1
  obtain ⟨m, hm8, hm, hlt'⟩ := h2
  rcases lt_trichotomy k m with h | rfl | h
  · exact ⟨k, hk8, fun j hj => (hk j hj).trans (hm j (hj.trans h)), hlt.trans_eq (hm k h)⟩
  · exact ⟨k, hk8, fun j hj => (hk j hj).trans (hm j hj), hlt.trans hlt'⟩
  · exact ⟨m, hm8, fun j hj => (hk j (hj.trans h)).trans (hm j hj), (hk m h).trans_lt hlt'⟩

theorem LexLt.asymm {a b : ℕ → ℕ} (h1 : LexLt a b) (h2 : LexLt b a) : False :=
  LexLt.irrefl a (h1.trans h2)

theorem LexLt.ne {a b : ℕ → ℕ} (h : LexLt a b) : a ≠ b := by
  rintro rfl; exact LexLt.irrefl a h

/-- The first differing component, case by case. -/
theorem LexLt.cases {a b : ℕ → ℕ} (h : LexLt a b) :
    a 0 < b 0 ∨ (a 0 = b 0 ∧ (a 1 < b 1 ∨ (a 1 = b 1 ∧
      ((a 2 < b 2 ∨ (a 2 = b 2 ∧ (a 3 < b 3 ∨ (a 3 = b 3 ∧ a 4 < b 4)))) ∨
       ((a 2 = b 2 ∧ a 3 = b 3 ∧ a 4 = b 4) ∧
        (a 5 < b 5 ∨ (a 5 = b 5 ∧ (a 6 < b 6 ∨ (a 6 = b 6 ∧ a 7 < b 7))))))))) := by
  obtain ⟨k, hk8, hk, hlt⟩ := h
  interval_cases k
  · exact Or.inl hlt
  · exact Or.inr ⟨hk 0 (by norm_num), Or.inl hlt⟩
  · exact Or.inr ⟨hk 0 (by norm_num), Or.inr ⟨hk 1 (by norm_num), Or.inl (Or.inl hlt)⟩⟩
  · exact Or.inr ⟨hk 0 (by norm_num), Or.inr ⟨hk 1 (by norm_num),
      Or.inl (Or.inr ⟨hk 2 (by norm_num), Or.inl hlt⟩)⟩⟩
  · exact Or.inr ⟨hk 0 (by norm_num), Or.inr ⟨hk 1 (by norm_num),
      Or.inl (Or.inr ⟨hk 2 (by norm_num), Or.inr ⟨hk 3 (by norm_num), hlt⟩⟩)⟩⟩
  · exact Or.inr ⟨hk 0 (by norm_num), Or.inr ⟨hk 1 (by norm_num), Or.inr
      ⟨⟨hk 2 (by norm_num), hk 3 (by norm_num), hk 4 (by norm_num)⟩, Or.inl hlt⟩⟩⟩
  · exact Or.inr ⟨hk 0 (by norm_num), Or.inr ⟨hk 1 (by norm_num), Or.inr
      ⟨⟨hk 2 (by norm_num), hk 3 (by norm_num), hk 4 (by norm_num)⟩,
        Or.inr ⟨hk 5 (by norm_num), Or.inl hlt⟩⟩⟩⟩
  · exact Or.inr ⟨hk 0 (by norm_num), Or.inr ⟨hk 1 (by norm_num), Or.inr
      ⟨⟨hk 2 (by norm_num), hk 3 (by norm_num), hk 4 (by norm_num)⟩,
        Or.inr ⟨hk 5 (by norm_num), Or.inr ⟨hk 6 (by norm_num), hlt⟩⟩⟩⟩⟩

/-- **Set ⇒ list**: two lists that are pairwise in an asymmetric relation and have the same members are equal. -/
theorem eq_of_pairwise_of_mem_iff {α : Type*} (R : α → α → Prop) (hasymm : ∀ a b, R a b → R b a → False) :
    ∀ (l l' : List α), l.Pairwise R → l'.Pairwise R → (∀ x, x ∈ l ↔ x ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr (by simp)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).mp (by simp)) (by simp)
  | a :: l, b :: l', hp, hp', h => by
    have hirr : ∀ x, ¬ R x x := fun x hx => hasymm x x hx hx
    rw [List.pairwise_cons] at hp hp'
    have hab : a = b := by
      rcases List.mem_cons.mp ((h a).mp (by simp)) with hab | hab
      · exact hab
      · rcases List.mem_cons.mp ((h b).mpr (by simp)) with hba | hba
        · exact hba.symm
        · exact (hasymm a b (hp.1 b hba) (hp'.1 a hab)).elim
    subst hab
    congr 1
    refine eq_of_pairwise_of_mem_iff R hasymm l l' hp.2 hp'.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with rfl | hx'
      · exact (hirr _ (hp.1 _ hx)).elim
      · exact hx'
    · rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with rfl | hx'
      · exact (hirr _ (hp'.1 _ hx)).elim
      · exact hx'

/-- A list that is pairwise in an irreflexive relation has no duplicates. -/
theorem nodup_of_pairwise {α : Type*} {R : α → α → Prop} (hirr : ∀ a, ¬ R a a) {l : List α}
    (h : l.Pairwise R) : l.Nodup :=
  h.imp fun {a b} hab => by rintro rfl; exact hirr a hab

/-- `i ↦ f i` over `range n` is pairwise in `R` when `R (f i) (f j)` for all `i < j < n`. -/
theorem pairwise_range_map {α : Type*} {R : α → α → Prop} {n : ℕ} (f : ℕ → α)
    (h : ∀ i j, i < j → j < n → R (f i) (f j)) : ((List.range n).map f).Pairwise R := by
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp_of_mem fun {a b} _ hb hab => h a b hab (List.mem_range.mp hb)

/-! ## 2. Evaluation helpers -/

section Eval
variable {F : Type} [Field F]

/-- The gate environment of row `i` of the row values `v`. -/
def envAt (v : ℕ → ℕ → F) (i : ℕ) : Env F := ⟨v i, v (i + 1), fun _ => 0, fun _ => 0⟩

theorem eval_sumList_range (n : ℕ) (f : ℕ → CoeffExpr F) (e : Env F) :
    (CoeffExpr.sumList (List.range n) f).eval e = ∑ k ∈ Finset.range n, (f k).eval e := by
  rw [CoeffExpr.eval_sumList]
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem bitSum_eval (base n : ℕ) (e : Env F) :
    (bitSum base n : CoeffExpr F).eval e = ∑ i ∈ Finset.range n, (2 : F) ^ i * e.trace (base + i) := by
  unfold bitSum; rw [eval_sumList_range]; rfl

theorem bitSumN_eval (base n : ℕ) (e : Env F) :
    (bitSumN base n : CoeffExpr F).eval e = ∑ i ∈ Finset.range n, (2 : F) ^ i * e.traceNext (base + i) := by
  unfold bitSumN; rw [eval_sumList_range]; rfl

theorem bool_of {x : F} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- The value of key component `k` at the row values `t`. -/
def kF (t : ℕ → F) (k : ℕ) : F := (keyC k).eval ⟨t, fun _ => 0, fun _ => 0, fun _ => 0⟩

theorem bitSum_eval_congr (base n : ℕ) {e e' : Env F} (h : e.trace = e'.trace) :
    (bitSum base n : CoeffExpr F).eval e = (bitSum base n : CoeffExpr F).eval e' := by
  rw [bitSum_eval, bitSum_eval, h]

/-- The current-row key reads only the current row. -/
theorem keyC_eval (e : Env F) (k : ℕ) : (keyC k).eval e = kF e.trace k := by
  unfold kF
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => exact bitSum_eval_congr _ _ rfl
  | 4 => exact bitSum_eval_congr _ _ rfl
  | 5 => rfl
  | 6 => exact bitSum_eval_congr _ _ rfl
  | k + 7 => exact bitSum_eval_congr _ _ rfl

/-- The next-row key is the key of the next row. -/
theorem keyN_eval (e : Env F) (k : ℕ) : (keyN k).eval e = kF e.traceNext k := by
  unfold kF
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => show (bitSumN _ 32).eval e = (bitSum _ 32).eval _; rw [bitSumN_eval, bitSum_eval]
  | 4 => show (bitSumN _ 32).eval e = (bitSum _ 32).eval _; rw [bitSumN_eval, bitSum_eval]
  | 5 => rfl
  | 6 => show (bitSumN _ 32).eval e = (bitSum _ 32).eval _; rw [bitSumN_eval, bitSum_eval]
  | k + 7 => show (bitSumN _ 32).eval e = (bitSum _ 32).eval _; rw [bitSumN_eval, bitSum_eval]

/-- The child value `x = w·id + (1−w)·a` of one side. -/
def xF (t : ℕ → F) (w id a : ℕ) : F := t w * t id + (1 - t w) * t a

end Eval

/-! ## 3. Bits, one-hot -/

section Bits
variable {p : ℕ} [Fact p.Prime]

theorem bits_cast (x : ℕ → ZMod p) (n : ℕ) (hb : ∀ i < n, x i = 0 ∨ x i = 1) :
    ∃ m : ℕ, m < 2 ^ n ∧ ∑ i ∈ Finset.range n, (2 : ZMod p) ^ i * x i = (m : ZMod p) := by
  induction n with
  | zero => exact ⟨0, by norm_num, by simp⟩
  | succ n ih =>
    obtain ⟨m, hm, he⟩ := ih fun i hi => hb i (by omega)
    rw [Finset.sum_range_succ, he]
    rcases hb n (by omega) with h | h
    · exact ⟨m, by rw [pow_succ]; omega, by rw [h]; simp⟩
    · exact ⟨m + 2 ^ n, by rw [pow_succ]; omega, by rw [h]; push_cast; ring⟩

theorem val_natCast_lt {m : ℕ} (h : m < p) : (m : ZMod p).val = m := ZMod.val_cast_of_lt h

theorem natCast_inj_lt {a b : ℕ} (h : (a : ZMod p) = b) (ha : a < p) (hb : b < p) : a = b := by
  rw [← val_natCast_lt ha, ← val_natCast_lt hb, h]

theorem bool_val {x : ZMod p} (h : x = 0 ∨ x = 1) : x.val ≤ 1 := by
  rcases h with rfl | rfl
  · simp
  · rw [ZMod.val_one]

theorem nat_onehot (f : ℕ → ℕ) : ∀ n, (∀ k < n, f k ≤ 1) → ∑ k ∈ Finset.range n, f k = 1 →
    ∃ k0 < n, f k0 = 1 ∧ ∀ k < n, k ≠ k0 → f k = 0
  | 0, _, h => by simp at h
  | n + 1, hb, h => by
    rw [Finset.sum_range_succ] at h
    have hn := hb n (by omega)
    by_cases hfn : f n = 1
    · refine ⟨n, by omega, hfn, fun k hk hne => ?_⟩
      have h0 : ∑ k ∈ Finset.range n, f k = 0 := by omega
      exact (Finset.sum_eq_zero_iff.mp h0) k (Finset.mem_range.mpr (by omega))
    · obtain ⟨k0, hk0, h1, h2⟩ := nat_onehot f n (fun k hk => hb k (by omega)) (by omega)
      refine ⟨k0, by omega, h1, fun k hk hne => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact h2 k hk hne
      · omega

/-- **One-hot**: eight booleans summing to `1` (in `ZMod p`, `p > 8`) are the indicator of one index. -/
theorem onehot (s : ℕ → ZMod p) (hb : ∀ k < 8, s k = 0 ∨ s k = 1) (hsum : ∑ k ∈ Finset.range 8, s k = 1)
    (hp : 8 < p) : ∃ k0 < 8, ∀ k < 8, s k = if k = k0 then 1 else 0 := by
  have hcast : ∀ k, s k = ((s k).val : ZMod p) := fun k => (ZMod.natCast_zmod_val _).symm
  have hle : ∀ k < 8, (s k).val ≤ 1 := fun k hk => bool_val (hb k hk)
  have hS : ∑ k ∈ Finset.range 8, (s k).val = 1 := by
    have h1 : ((∑ k ∈ Finset.range 8, (s k).val : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      push_cast; rw [← hsum]; exact Finset.sum_congr rfl fun k _ => (hcast k).symm
    have hlt : ∑ k ∈ Finset.range 8, (s k).val ≤ 8 := by
      calc ∑ k ∈ Finset.range 8, (s k).val ≤ ∑ _k ∈ Finset.range 8, 1 :=
            Finset.sum_le_sum fun k hk => hle k (Finset.mem_range.mp hk)
        _ = 8 := by simp
    exact natCast_inj_lt h1 (by omega) (by omega)
  obtain ⟨k0, hk0, h1, h0⟩ := nat_onehot (fun k => (s k).val) 8 hle hS
  refine ⟨k0, hk0, fun k hk => ?_⟩
  split_ifs with hkk
  · subst hkk; rw [hcast k, h1]; simp
  · rw [hcast k, h0 k hk hkk]; simp

theorem sum_indicator {F : Type} [Field F] (k0 : ℕ) :
    ∀ l : List ℕ, l.Nodup → (l.map fun k => if k = k0 then (1 : F) else 0).sum = if k0 ∈ l then 1 else 0
  | [], _ => by simp
  | a :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.sum_cons, sum_indicator k0 l hl.2]
    by_cases ha : a = k0
    · subst ha; simp [hl.1]
    · by_cases hk : k0 ∈ l
      · simp [ha, hk]
      · have : k0 ∉ a :: l := by simp [hk, Ne.symm ha]
        simp [ha, hk, this]

end Bits

/-! ## 4. The side gates and the cell base gates, evaluated -/

section Rows
variable {F : Type} [Field F]

open SideM in
/-- `canonMGates` as its eight parts. -/
theorem canonMGates_parts : canonMGates (F := F) =
    ((((((((List.range 128).map fun i => boolE (cv (A + i))) ++
      ((List.range 70).map fun i => boolE (cv (A + 130 + i)))) ++
      sideM Cell.wL Cell.idL Cell.aL CellTwinK.kbL CellTwinK.invL (bLh 0) (bLl 0) tL) ++
      sideM Cell.wR Cell.idR Cell.aR CellTwinK.kbR CellTwinK.invR (bRh 0) (bRl 0) tR) ++
      [ .mul (notE (cv Cell.isL)) (.sub (CoeffExpr.sumList (List.range 8) fun k => cv (s k)) (.const 1)),
        .mul (notE (cv Cell.isL)) (.sub (.sub (CoeffExpr.sumList (List.range 8) fun k =>
          .mul (cv (s k)) (.sub (keyN k) (keyC k))) (.const 1)) (bitSum (d 0) 62)) ]) ++
      ((List.range 7).map fun j => .mul (.mul (notE (cv Cell.isL))
        (CoeffExpr.sumList ((List.range 8).filter fun k => decide (j < k)) fun k => cv (s k)))
          (.sub (keyN j) (keyC j)))) ++
      ((List.range 8).map fun k => .mul (cv Cell.isL) (cv (s k)))) ++
      ((List.range 62).map fun i => .mul (cv Cell.isL) (cv (d i))) := rfl

/-- **The side gates of `canonM` at one row, evaluated.** -/
structure MRow (e : Env F) : Prop where
  limb : ∀ i < 128, e.trace (SideM.A + i) = 0 ∨ e.trace (SideM.A + i) = 1
  sd : ∀ i < 70, e.trace (SideM.A + 130 + i) = 0 ∨ e.trace (SideM.A + 130 + i) = 1
  sideL : ∀ g ∈ sideM (F := F) Cell.wL Cell.idL Cell.aL CellTwinK.kbL CellTwinK.invL (SideM.bLh 0)
    (SideM.bLl 0) SideM.tL, g.eval e = 0
  sideR : ∀ g ∈ sideM (F := F) Cell.wR Cell.idR Cell.aR CellTwinK.kbR CellTwinK.invR (SideM.bRh 0)
    (SideM.bRl 0) SideM.tR, g.eval e = 0
  hot : (1 - e.trace Cell.isL) * (∑ k ∈ Finset.range 8, e.trace (SideM.s k) - 1) = 0
  dif : (1 - e.trace Cell.isL) * (∑ k ∈ Finset.range 8, e.trace (SideM.s k) * (kF e.traceNext k - kF e.trace k)
    - 1 - ∑ i ∈ Finset.range 62, (2 : F) ^ i * e.trace (SideM.d 0 + i)) = 0
  first : ∀ j < 7, (1 - e.trace Cell.isL) *
    (((List.range 8).filter fun k => decide (j < k)).map fun k => e.trace (SideM.s k)).sum *
      (kF e.traceNext j - kF e.trace j) = 0
  lastS : ∀ k < 8, e.trace Cell.isL * e.trace (SideM.s k) = 0
  lastD : ∀ i < 62, e.trace Cell.isL * e.trace (SideM.d i) = 0

theorem mrow_of {e : Env F} (h : ∀ g ∈ canonMGates (F := F), g.eval e = 0) : MRow e := by
  rw [canonMGates_parts] at h
  simp only [List.mem_append, or_imp, forall_and] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at h5
  obtain ⟨g1, g2⟩ := h5
  simp only [CoeffExpr.eval, cv, notE, eval_sumList_range] at g1
  simp only [CoeffExpr.eval, cv, notE, eval_sumList_range, keyN_eval, keyC_eval, bitSum_eval] at g2
  refine ⟨fun i hi => bool_of ?_, fun i hi => bool_of ?_, h3, h4, g1, g2, fun j hj => ?_, fun k hk => ?_,
    fun i hi => ?_⟩
  · have := h1 _ (List.mem_map_of_mem (List.mem_range.mpr hi))
    simpa only [CoeffExpr.eval, cv, boolE] using this
  · have := h2 _ (List.mem_map_of_mem (List.mem_range.mpr hi))
    simpa only [CoeffExpr.eval, cv, boolE] using this
  · have := h6 _ (List.mem_map_of_mem (List.mem_range.mpr hj))
    simpa only [CoeffExpr.eval, cv, notE, CoeffExpr.eval_sumList, keyN_eval, keyC_eval] using this
  · have := h7 _ (List.mem_map_of_mem (List.mem_range.mpr hk))
    simpa only [CoeffExpr.eval, cv] using this
  · have := h8 _ (List.mem_map_of_mem (List.mem_range.mpr hi))
    simpa only [CoeffExpr.eval, cv] using this

/-- **The cell table's base gates at one row, evaluated** (`Cell.baseGates`). -/
structure CellFacts (e : Env F) : Prop where
  serial0 : e.trace Cell.isF * e.trace Cell.idx = 0
  serialS : (1 - e.trace Cell.isL) * (e.traceNext Cell.idx - e.trace Cell.idx - 1) = 0
  rkLo : e.trace Cell.lo + 2 ^ 62 * e.trace Cell.carry - (e.trace Cell.loL + e.trace Cell.loR + 1) = 0
  rkHi : e.trace Cell.hi - (e.trace Cell.hiL + e.trace Cell.hiR + e.trace Cell.carry) = 0
  carry : e.trace Cell.carry = 0 ∨ e.trace Cell.carry = 1
  wL : e.trace Cell.wL = 0 ∨ e.trace Cell.wL = 1
  wR : e.trace Cell.wR = 0 ∨ e.trace Cell.wR = 1
  loBits : e.trace Cell.lo - ∑ i ∈ Finset.range 62, (2 : F) ^ i * e.trace (Cell.bit0 + i) = 0
  hiBits : e.trace Cell.hi - ∑ i ∈ Finset.range 48, (2 : F) ^ i * e.trace (Cell.bit0 + 62 + i) = 0
  aLlo : (1 - e.trace Cell.wL) * e.trace Cell.loL = 0
  aLhi : (1 - e.trace Cell.wL) * e.trace Cell.hiL = 0
  aRlo : (1 - e.trace Cell.wR) * e.trace Cell.loR = 0
  aRhi : (1 - e.trace Cell.wR) * e.trace Cell.hiR = 0
  bits : ∀ i < 110, e.trace (Cell.bit0 + i) = 0 ∨ e.trace (Cell.bit0 + i) = 1

theorem cellFacts_of {e : Env F} (h : ∀ g ∈ Cell.baseGates (F := F), g.eval e = 0) : CellFacts e := by
  simp only [Cell.baseGates, List.mem_append, or_imp, forall_and, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq] at h
  obtain ⟨⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩, hb⟩ := h
  simp only [CoeffExpr.eval, cv, nv, notE, boolE, bitSum_eval] at g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13
  refine ⟨g1, g2, g3, g4, bool_of g5, bool_of g6, bool_of g7, g8, g9, g10, g11, g12, g13, fun i hi => bool_of ?_⟩
  have := hb _ (List.mem_map_of_mem (List.mem_range.mpr hi))
  simpa only [CoeffExpr.eval, cv, boolE] using this

end Rows

/-! ## 5. The gadget at one row; the sorted table -/

section Step
variable {p : ℕ} [Fact p.Prime]

/-- **The sort gadget at one row** (outside the last): the one-hot `s` picks a component `k0`; every earlier
component agrees with the next row's, and component `k0` grows by `1 + D`, `D < 2^62` the `62` difference bits. -/
theorem step_field {e : Env (ZMod p)} (hp : 8 < p) (hm : MRow e) (hL : e.trace Cell.isL = 0) :
    ∃ k0 < 8, (∀ j < k0, kF e.traceNext j = kF e.trace j) ∧
      ∃ m : ℕ, m < 2 ^ 62 ∧ kF e.traceNext k0 = kF e.trace k0 + 1 + (m : ZMod p) := by
  have hot := hm.hot
  rw [hL, sub_zero, one_mul, sub_eq_zero] at hot
  obtain ⟨k0, hk0, hs⟩ := onehot (fun k => e.trace (SideM.s k)) (fun k hk => hm.sd k (by omega)) hot hp
  obtain ⟨m, hm62, hD⟩ := bits_cast (fun i => e.trace (SideM.d 0 + i)) 62 (fun i hi => by
    have e1 : SideM.d 0 + i = SideM.A + 130 + (8 + i) := by simp only [SideM.d]; omega
    rw [e1]; exact hm.sd (8 + i) (by omega))
  refine ⟨k0, hk0, fun j hj => ?_, m, hm62, ?_⟩
  · have hf := hm.first j (by omega)
    rw [hL, sub_zero, one_mul] at hf
    have hmap : (((List.range 8).filter fun k => decide (j < k)).map fun k => e.trace (SideM.s k)) =
        (((List.range 8).filter fun k => decide (j < k)).map fun k => if k = k0 then (1 : ZMod p) else 0) := by
      refine List.map_congr_left fun k hk => ?_
      exact hs k (List.mem_range.mp (List.mem_filter.mp hk).1)
    have hmem : k0 ∈ (List.range 8).filter fun k => decide (j < k) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hk0, by simp [hj]⟩
    rw [hmap, sum_indicator k0 _ (List.nodup_range.filter _)] at hf
    simp only [hmem, ite_true, one_mul, sub_eq_zero] at hf
    exact hf
  · have hdif := hm.dif
    rw [hL, sub_zero, one_mul] at hdif
    have hterm : ∀ k ∈ Finset.range 8, e.trace (SideM.s k) * (kF e.traceNext k - kF e.trace k) =
        if k0 = k then kF e.traceNext k - kF e.trace k else 0 := fun k hk => by
      rw [hs k (Finset.mem_range.mp hk)]
      by_cases h : k = k0
      · subst h; simp
      · simp [h, Ne.symm h]
    have hk0' : k0 ∈ Finset.range 8 := Finset.mem_range.mpr hk0
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq, hD] at hdif
    simp only [hk0', ite_true] at hdif
    linear_combination hdif

end Step

/-! ## 6. Ranges, the sorted table, canonical limbs -/

section Table
variable {p : ℕ} [Fact p.Prime]

/-- The Goldilocks prime as a numeral. -/
theorem pG : Nock.Atoms.p = 18446744069414584321 := by norm_num [Nock.Atoms.p, Nock.Field.p]

theorem bitSum32 {e : Env (ZMod p)} (b : ℕ) (hb : ∀ i < 32, e.trace (b + i) = 0 ∨ e.trace (b + i) = 1) :
    ∃ m : ℕ, m < 2 ^ 32 ∧ (bitSum b 32 : CoeffExpr (ZMod p)).eval e = (m : ZMod p) := by
  rw [bitSum_eval]; exact bits_cast _ 32 hb

theorem CellFacts.lo_lt {e : Env (ZMod p)} (hc : CellFacts e) (hp : 2 ^ 62 < p) :
    (e.trace Cell.lo).val < 2 ^ 62 := by
  obtain ⟨m, hm, he⟩ := bits_cast (fun i => e.trace (Cell.bit0 + i)) 62 (fun i hi => hc.bits i (by omega))
  rw [sub_eq_zero.mp hc.loBits, he, val_natCast_lt (by omega)]; exact hm

theorem CellFacts.hi_lt {e : Env (ZMod p)} (hc : CellFacts e) (hp : 2 ^ 62 < p) :
    (e.trace Cell.hi).val < 2 ^ 62 := by
  obtain ⟨m, hm, he⟩ := bits_cast (fun i => e.trace (Cell.bit0 + 62 + i)) 48 (fun i hi => by
    rw [Nat.add_assoc]; exact hc.bits (62 + i) (by omega))
  rw [sub_eq_zero.mp hc.hiBits, he, val_natCast_lt (by omega)]; omega

/-- The natural value of key component `k` at the row values `t`. -/
def keyNat (t : ℕ → ZMod p) : ℕ → ℕ := fun k => (kF t k).val

theorem limbL_bits {t : ℕ → ZMod p} (hb : ∀ i < 128, t (SideM.A + i) = 0 ∨ t (SideM.A + i) = 1) (c : ℕ)
    (hc : c < 4) : ∀ i < 32, t (SideM.A + 32 * c + i) = 0 ∨ t (SideM.A + 32 * c + i) = 1 := fun i hi => by
  rw [Nat.add_assoc]; exact hb _ (by omega)

/-- Every key component of a row is below `2^62`. -/
theorem kF_val_lt {t : ℕ → ZMod p} (hp : 2 ^ 63 < p) (hb : ∀ i < 128, t (SideM.A + i) = 0 ∨ t (SideM.A + i) = 1)
    (hhi : (t Cell.hi).val < 2 ^ 62) (hlo : (t Cell.lo).val < 2 ^ 62) (hwL : t Cell.wL = 0 ∨ t Cell.wL = 1)
    (hwR : t Cell.wR = 0 ∨ t Cell.wR = 1) : ∀ k < 8, (kF t k).val < 2 ^ 62 := by
  have hlimb : ∀ c < 4, ∃ m : ℕ, m < 2 ^ 32 ∧ (bitSum (SideM.A + 32 * c) 32 : CoeffExpr (ZMod p)).eval
      ⟨t, fun _ => 0, fun _ => 0, fun _ => 0⟩ = (m : ZMod p) := fun c hc =>
    bitSum32 (e := ⟨t, fun _ => 0, fun _ => 0, fun _ => 0⟩) _ (limbL_bits hb c hc)
  have hl : ∀ c < 4, ((bitSum (SideM.A + 32 * c) 32 : CoeffExpr (ZMod p)).eval
      ⟨t, fun _ => 0, fun _ => 0, fun _ => 0⟩).val < 2 ^ 62 := fun c hc => by
    obtain ⟨m, hm, he⟩ := hlimb c hc
    rw [he, val_natCast_lt (by omega)]; omega
  intro k hk
  interval_cases k
  · exact hhi
  · exact hlo
  · exact (bool_val hwL).trans_lt (by norm_num)
  · exact hl 0 (by norm_num)
  · exact hl 1 (by norm_num)
  · exact (bool_val hwR).trans_lt (by norm_num)
  · exact hl 2 (by norm_num)
  · exact hl 3 (by norm_num)

/-- **The hypotheses on a cell table with its side columns** (`n` rows of values `v`): the side gates and the
cell base gates at every row, and the two endpoint masks. -/
structure TableM (v : ℕ → ℕ → ZMod p) (n : ℕ) : Prop where
  hM : ∀ i < n, ∀ g ∈ canonMGates (F := ZMod p), g.eval (envAt v i) = 0
  hC : ∀ i < n, ∀ g ∈ Cell.baseGates (F := ZMod p), g.eval (envAt v i) = 0
  isF : ∀ i < n, v i Cell.isF = if i = 0 then 1 else 0
  isL : ∀ i < n, v i Cell.isL = if i + 1 = n then 1 else 0

variable {v : ℕ → ℕ → ZMod p} {n : ℕ}

theorem TableM.mrow (T : TableM v n) {i : ℕ} (hi : i < n) : MRow (envAt v i) := mrow_of (T.hM i hi)
theorem TableM.cell (T : TableM v n) {i : ℕ} (hi : i < n) : CellFacts (envAt v i) := cellFacts_of (T.hC i hi)

theorem TableM.kF_lt (T : TableM v n) (hp : 2 ^ 63 < p) {i : ℕ} (hi : i < n) :
    ∀ k < 8, (kF (v i) k).val < 2 ^ 62 :=
  kF_val_lt hp (T.mrow hi).limb ((T.cell hi).hi_lt (by omega)) ((T.cell hi).lo_lt (by omega)) (T.cell hi).wL
    (T.cell hi).wR

/-- **Adjacent rows** (outside the last) have strictly increasing keys. -/
theorem TableM.step (T : TableM v n) (hp : 2 ^ 63 < p) {i : ℕ} (hi : i + 1 < n) :
    LexLt (keyNat (v i)) (keyNat (v (i + 1))) := by
  have hL : (envAt v i).trace Cell.isL = 0 := by
    show v i Cell.isL = 0
    rw [T.isL i (by omega)]; simp only [show i + 1 ≠ n by omega, ite_false]
  obtain ⟨k0, hk0, heq, m, hm62, hstep⟩ := step_field (by omega) (T.mrow (by omega)) hL
  have hlt := T.kF_lt hp (i := i) (by omega) k0 hk0
  refine ⟨k0, hk0, fun j hj => ?_, ?_⟩
  · show (kF (v i) j).val = (kF (v (i + 1)) j).val
    exact congrArg ZMod.val (heq j hj).symm
  · show (kF (v i) k0).val < (kF (v (i + 1)) k0).val
    have h' : kF (v (i + 1)) k0 = (((kF (v i) k0).val + 1 + m : ℕ) : ZMod p) := by
      have h2 : kF (v (i + 1)) k0 = kF (v i) k0 + 1 + (m : ZMod p) := hstep
      rw [h2]; push_cast; rw [ZMod.natCast_zmod_val]
    rw [h', val_natCast_lt (by omega)]; omega

/-- **The row keys are strictly increasing** (`i < j < n`). -/
theorem TableM.sorted (T : TableM v n) (hp : 2 ^ 63 < p) :
    ∀ i j, i < j → j < n → LexLt (keyNat (v i)) (keyNat (v j)) := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | rfl
    · exact (ih h (by omega)).trans (T.step hp hj)
    · exact T.step hp hj

/-- **The row-key list is `Pairwise LexLt`.** -/
theorem TableM.keys_pairwise (T : TableM v n) (hp : 2 ^ 63 < p) :
    ((List.range n).map fun i => keyNat (v i)).Pairwise LexLt :=
  pairwise_range_map _ (T.sorted hp)

theorem TableM.keys_ne (T : TableM v n) (hp : 2 ^ 63 < p) {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    keyNat (v i) ≠ keyNat (v j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact (T.sorted hp i j h hj).ne
  · exact (T.sorted hp j i h hi).ne.symm

/-- **`idx` is the row number.** -/
theorem TableM.idx_row (T : TableM v n) : ∀ i < n, v i Cell.idx = (i : ZMod p) := by
  intro i hi
  induction i with
  | zero =>
    have h0 := (T.cell hi).serial0
    change v 0 Cell.isF * v 0 Cell.idx = 0 at h0
    rw [T.isF 0 hi] at h0
    simpa using h0
  | succ i ih =>
    have hs := (T.cell (i := i) (by omega)).serialS
    change (1 - v i Cell.isL) * (v (i + 1) Cell.idx - v i Cell.idx - 1) = 0 at hs
    rw [T.isL i (by omega), ih (by omega)] at hs
    simp only [show i + 1 ≠ n by omega, ite_false, sub_zero, one_mul] at hs
    push_cast; linear_combination hs

theorem TableM.idx_inj (T : TableM v n) (hnp : n ≤ p) {i j : ℕ} (hi : i < n) (hj : j < n)
    (h : v i Cell.idx = v j Cell.idx) : i = j := by
  rw [T.idx_row i hi, T.idx_row j hj] at h
  exact natCast_inj_lt h (by omega) (by omega)

/-- **Canonical limbs of one side** (Goldilocks): the side gates force `x = 2^32·h + l` with `h, l < 2^32` and
`h = 2^32 − 1 ⇒ l = 0`, so `(h, l) = (x.val / 2^32, x.val % 2^32)`; also the two child-kind pins. -/
theorem side_canon (hpG : p = Nock.Atoms.p) {e : Env (ZMod p)} {w id a kb inv h l t : ℕ}
    (hS : ∀ g ∈ sideM (F := ZMod p) w id a kb inv h l t, g.eval e = 0)
    (hh : ∀ i < 32, e.trace (h + i) = 0 ∨ e.trace (h + i) = 1)
    (hl : ∀ i < 32, e.trace (l + i) = 0 ∨ e.trace (l + i) = 1) :
    ((bitSum h 32 : CoeffExpr (ZMod p)).eval e).val = (xF e.trace w id a).val / 2 ^ 32 ∧
    ((bitSum l 32 : CoeffExpr (ZMod p)).eval e).val = (xF e.trace w id a).val % 2 ^ 32 ∧
    (1 - e.trace w) * e.trace id = 0 ∧ e.trace w * e.trace a = 0 := by
  have hpv : p = 18446744069414584321 := hpG.trans pG
  simp only [sideM, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hS
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hS
  obtain ⟨mh, hmh, eh⟩ := bitSum32 h hh
  obtain ⟨ml, hml, el⟩ := bitSum32 l hl
  simp only [CoeffExpr.eval, cv, notE, eh, el] at g1 g4 g5 g6
  have h32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have hml0 : mh = 2 ^ 32 - 1 → ml = 0 := by
    intro hmax
    have hc : ((2 ^ 32 - 1 : ℕ) : ZMod p) = 2 ^ 32 - 1 := by
      rw [Nat.cast_sub (by norm_num)]; push_cast; ring
    have hz : (mh : ZMod p) - (2 ^ 32 - 1) = 0 := by rw [hmax, hc]; ring
    rw [hz, zero_mul, sub_zero, one_mul] at g4
    exact natCast_inj_lt (b := 0) (by simpa using g4) (by omega) (by omega)
  have hbound : 2 ^ 32 * mh + ml < p := by
    by_cases hmax : mh = 2 ^ 32 - 1
    · rw [hml0 hmax, hmax, hpv]; norm_num
    · rw [h32] at hmh hml hmax ⊢; omega
  have hx : xF e.trace w id a = ((2 ^ 32 * mh + ml : ℕ) : ZMod p) := by
    unfold xF; push_cast; linear_combination g1
  rw [eh, el, hx, val_natCast_lt (m := mh) (by omega), val_natCast_lt (m := ml) (by omega),
    val_natCast_lt hbound]
  refine ⟨?_, ?_, g5, g6⟩ <;> rw [h32] at hmh hml ⊢ <;> omega

/-- **Canonical limbs at a row** (both sides; key components `3, 4` and `6, 7`). -/
theorem limbs_canon (hpG : p = Nock.Atoms.p) {e : Env (ZMod p)} (hm : MRow e) :
    (kF e.trace 3).val = (xF e.trace Cell.wL Cell.idL Cell.aL).val / 2 ^ 32 ∧
    (kF e.trace 4).val = (xF e.trace Cell.wL Cell.idL Cell.aL).val % 2 ^ 32 ∧
    (kF e.trace 6).val = (xF e.trace Cell.wR Cell.idR Cell.aR).val / 2 ^ 32 ∧
    (kF e.trace 7).val = (xF e.trace Cell.wR Cell.idR Cell.aR).val % 2 ^ 32 ∧
    (1 - e.trace Cell.wL) * e.trace Cell.idL = 0 ∧ e.trace Cell.wL * e.trace Cell.aL = 0 ∧
    (1 - e.trace Cell.wR) * e.trace Cell.idR = 0 ∧ e.trace Cell.wR * e.trace Cell.aR = 0 := by
  have hb : ∀ c < 4, ∀ i < 32, e.trace (SideM.A + 32 * c + i) = 0 ∨ e.trace (SideM.A + 32 * c + i) = 1 :=
    limbL_bits hm.limb
  obtain ⟨l1, l2, l3, l4⟩ := side_canon hpG hm.sideL (hb 0 (by norm_num)) (hb 1 (by norm_num))
  obtain ⟨r1, r2, r3, r4⟩ := side_canon hpG hm.sideR (hb 2 (by norm_num)) (hb 3 (by norm_num))
  rw [← keyC_eval, ← keyC_eval, ← keyC_eval, ← keyC_eval]
  exact ⟨l1, l2, r1, r2, l3, l4, r3, r4⟩

end Table

/-! ## 7. The noun order and `sortKey` -/

section Nouns

/-- The number of cells (internal nodes) of a noun: the rank the cell table records. -/
def nCells : Noun → ℕ
  | .atom _ => 0
  | .cell a b => nCells a + nCells b + 1

/-- The noun order as a Boolean (see `nlt`). -/
def nltB : Noun → Noun → Bool
  | .atom x, .atom y => decide (x < y)
  | .atom _, .cell _ _ => true
  | .cell _ _, .atom _ => false
  | .cell a b, .cell a' b' =>
      decide (nCells a + nCells b < nCells a' + nCells b') ||
        (decide (nCells a + nCells b = nCells a' + nCells b') && (nltB a a' || (decide (a = a') && nltB b b')))

/-- **The table-independent noun order** the cell sort realises: atoms by value, atoms before cells, cells by
rank (`nCells`) first, then the left child, then the right child. -/
def nlt (a b : Noun) : Prop := nltB a b = true

theorem nlt_atom_atom {x y : ℕ} : nlt (.atom x) (.atom y) ↔ x < y := by simp [nlt, nltB]
theorem nlt_atom_cell {x : ℕ} {a b : Noun} : nlt (.atom x) (.cell a b) := by simp [nlt, nltB]
theorem not_nlt_cell_atom {x : ℕ} {a b : Noun} : ¬ nlt (.cell a b) (.atom x) := by simp [nlt, nltB]

theorem nlt_cell {a b a' b' : Noun} : nlt (.cell a b) (.cell a' b') ↔
    nCells a + nCells b < nCells a' + nCells b' ∨
      (nCells a + nCells b = nCells a' + nCells b' ∧ (nlt a a' ∨ (a = a' ∧ nlt b b'))) := by
  simp only [nlt, nltB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]

theorem nlt_asymm : ∀ (a b : Noun), nlt a b → nlt b a → False
  | .atom x, .atom y, h1, h2 => by rw [nlt_atom_atom] at h1 h2; omega
  | .atom _, .cell _ _, _, h2 => not_nlt_cell_atom h2
  | .cell _ _, .atom _, h1, _ => not_nlt_cell_atom h1
  | .cell a b, .cell a' b', h1, h2 => by
    rw [nlt_cell] at h1 h2
    rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
    · omega
    · omega
    · omega
    · rcases h1 with h1 | ⟨h3, h1⟩ <;> rcases h2 with h2 | ⟨h4, h2⟩
      · exact nlt_asymm a a' h1 h2
      · rw [h4] at h1; exact nlt_asymm a a h1 h1
      · rw [← h3] at h2; exact nlt_asymm a a h2 h2
      · exact nlt_asymm b b' h1 h2

theorem nlt_irrefl (a : Noun) : ¬ nlt a a := fun h => nlt_asymm a a h h

theorem nlt_trans : ∀ (a b c : Noun), nlt a b → nlt b c → nlt a c
  | .atom x, .atom y, .atom z, h1, h2 => by rw [nlt_atom_atom] at h1 h2 ⊢; omega
  | .atom _, _, .cell _ _, _, _ => nlt_atom_cell
  | .atom _, .cell _ _, .atom _, _, h2 => (not_nlt_cell_atom h2).elim
  | .cell _ _, .atom _, _, h1, _ => (not_nlt_cell_atom h1).elim
  | .cell _ _, .cell _ _, .atom _, _, h2 => (not_nlt_cell_atom h2).elim
  | .cell a1 a2, .cell b1 b2, .cell c1 c2, h1, h2 => by
    rw [nlt_cell] at h1 h2 ⊢
    rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
    · left; omega
    · left; omega
    · left; omega
    · right; refine ⟨by omega, ?_⟩
      rcases h1 with h1 | ⟨h3, h1⟩ <;> rcases h2 with h2 | ⟨h4, h2⟩
      · exact Or.inl (nlt_trans a1 b1 c1 h1 h2)
      · subst h4; exact Or.inl h1
      · subst h3; exact Or.inl h2
      · subst h3; subst h4; exact Or.inr ⟨rfl, nlt_trans a2 b2 c2 h1 h2⟩

theorem nlt_trichotomy : ∀ (a b : Noun), nlt a b ∨ a = b ∨ nlt b a
  | .atom x, .atom y => by
    rcases lt_trichotomy x y with h | rfl | h
    · exact Or.inl (nlt_atom_atom.mpr h)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (nlt_atom_atom.mpr h))
  | .atom _, .cell _ _ => Or.inl nlt_atom_cell
  | .cell _ _, .atom _ => Or.inr (Or.inr nlt_atom_cell)
  | .cell a b, .cell a' b' => by
    rcases lt_trichotomy (nCells a + nCells b) (nCells a' + nCells b') with h | h | h
    · exact Or.inl (nlt_cell.mpr (Or.inl h))
    · rcases nlt_trichotomy a a' with h1 | rfl | h1
      · exact Or.inl (nlt_cell.mpr (Or.inr ⟨h, Or.inl h1⟩))
      · rcases nlt_trichotomy b b' with h2 | rfl | h2
        · exact Or.inl (nlt_cell.mpr (Or.inr ⟨h, Or.inr ⟨rfl, h2⟩⟩))
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (nlt_cell.mpr (Or.inr ⟨h.symm, Or.inr ⟨rfl, h2⟩⟩)))
      · exact Or.inr (Or.inr (nlt_cell.mpr (Or.inr ⟨h.symm, Or.inl h1⟩)))
    · exact Or.inr (Or.inr (nlt_cell.mpr (Or.inl h)))

/-- The non-strict comparison the merge sort uses. -/
def nle (a b : Noun) : Bool := !nltB b a

theorem nle_iff {a b : Noun} : nle a b = true ↔ ¬ nlt b a := by simp [nle, nlt]

theorem nle_trans (a b c : Noun) (hab : nle a b = true) (hbc : nle b c = true) : nle a c = true := by
  rw [nle_iff] at hab hbc ⊢
  intro hca
  rcases nlt_trichotomy a b with h | rfl | h
  · exact hbc (nlt_trans c a b hca h)
  · exact hbc hca
  · exact hab h

theorem nle_total (a b : Noun) : (nle a b || nle b a) = true := by
  rw [Bool.or_eq_true, nle_iff, nle_iff]
  by_contra h
  push Not at h
  exact nlt_asymm a b h.2 h.1

/-- **`sortKey`**: the cells listed in the noun order (merge sort by `nlt`). -/
def sortKey (l : List Noun) : List Noun := l.mergeSort nle

theorem sortKey_perm (l : List Noun) : (sortKey l).Perm l := List.mergeSort_perm l nle

/-- **A duplicate-free list, sorted by `sortKey`, is strictly increasing in `nlt`.** -/
theorem sortKey_pairwise {l : List Noun} (hl : l.Nodup) : (sortKey l).Pairwise nlt := by
  have hs : (sortKey l).Pairwise fun a b => nle a b = true := List.pairwise_mergeSort nle_trans nle_total l
  have hnd : (sortKey l).Pairwise (· ≠ ·) := (sortKey_perm l).nodup_iff.mpr hl
  refine (hs.and hnd).imp fun {a b} h => ?_
  rcases nlt_trichotomy a b with h1 | h1 | h1
  · exact h1
  · exact (h.2 h1).elim
  · exact ((nle_iff.mp h.1) h1).elim

end Nouns

/-! ## 8. The noun link and the sorted nouns -/

section Link
variable {p : ℕ} [Fact p.Prime]

/-- **One child side of row `i`**: an atom child read from the atom column (`w = 0`), or (`w = 1`) the noun of
the row `c` whose serial the side carries, with that row's rank `(lo, hi)`. -/
def SideLink (v : ℕ → ℕ → ZMod p) (n : ℕ) (N : ℕ → Noun) (i w id a lo hi : ℕ) (X : Noun) : Prop :=
  (v i w = 0 ∧ X = .atom (v i a).val) ∨
    (v i w = 1 ∧ ∃ c < n, v c Cell.idx = v i id ∧ N c = X ∧ v c Cell.lo = v i lo ∧ v c Cell.hi = v i hi)

/-- **The noun link** of a table (to be supplied from the validity balance): every row's noun `N i` is a cell
whose two children are linked as `SideLink` says. -/
structure NounLink (v : ℕ → ℕ → ZMod p) (n : ℕ) (N : ℕ → Noun) : Prop where
  link : ∀ i < n, ∃ A B, N i = .cell A B ∧ SideLink v n N i Cell.wL Cell.idL Cell.aL Cell.loL Cell.hiL A ∧
    SideLink v n N i Cell.wR Cell.idR Cell.aR Cell.loR Cell.hiR B

/-- The rank `hi·2^62 + lo` of a row. -/
def rk (t : ℕ → ZMod p) : ℕ := (t Cell.hi).val * 2 ^ 62 + (t Cell.lo).val

theorem two62 : (2 : ℕ) ^ 62 = 4611686018427387904 := by norm_num
theorem two63 : (2 : ℕ) ^ 63 = 9223372036854775808 := by norm_num
theorem two32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num

theorem divmod_lt {a b : ℕ} (h : a / 2 ^ 32 < b / 2 ^ 32 ∨ (a / 2 ^ 32 = b / 2 ^ 32 ∧ a % 2 ^ 32 < b % 2 ^ 32)) :
    a < b := by rw [two32] at h; omega

theorem divmod_eq {a b : ℕ} (h1 : a / 2 ^ 32 = b / 2 ^ 32) (h2 : a % 2 ^ 32 = b % 2 ^ 32) : a = b := by
  rw [two32] at h1 h2; omega

/-- **The rank recurrence** `rk = rk_L + rk_R + 1` from the rank gates, the bit decompositions and the child
ranks' ranges (no wrap-around below `2^63 < p`). -/
theorem rank_rec (hp : 2 ^ 63 < p) {e : Env (ZMod p)} (hc : CellFacts e)
    (hLlo : (e.trace Cell.loL).val < 2 ^ 62) (hLhi : (e.trace Cell.hiL).val < 2 ^ 62)
    (hRlo : (e.trace Cell.loR).val < 2 ^ 62) (hRhi : (e.trace Cell.hiR).val < 2 ^ 62) :
    rk e.trace = ((e.trace Cell.hiL).val * 2 ^ 62 + (e.trace Cell.loL).val) +
      ((e.trace Cell.hiR).val * 2 ^ 62 + (e.trace Cell.loR).val) + 1 := by
  have hlo := hc.lo_lt (by omega)
  have hhi := hc.hi_lt (by omega)
  have hcv := bool_val hc.carry
  have h1 : (((e.trace Cell.lo).val + 2 ^ 62 * (e.trace Cell.carry).val : ℕ) : ZMod p) =
      (((e.trace Cell.loL).val + (e.trace Cell.loR).val + 1 : ℕ) : ZMod p) := by
    push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination hc.rkLo
  have h2 : (((e.trace Cell.hi).val : ℕ) : ZMod p) =
      (((e.trace Cell.hiL).val + (e.trace Cell.hiR).val + (e.trace Cell.carry).val : ℕ) : ZMod p) := by
    push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination hc.rkHi
  rw [two63] at hp
  rw [two62] at hlo hhi hLlo hLhi hRlo hRhi h1
  have n1 := natCast_inj_lt h1 (by omega) (by omega)
  have n2 := natCast_inj_lt h2 (by omega) (by omega)
  unfold rk; rw [two62]; omega

variable {v : ℕ → ℕ → ZMod p} {n : ℕ} {N : ℕ → Noun}

theorem TableM.lo_lt (T : TableM v n) (hp : 2 ^ 63 < p) {i : ℕ} (hi : i < n) : (v i Cell.lo).val < 2 ^ 62 :=
  (T.cell hi).lo_lt (by omega)
theorem TableM.hi_lt (T : TableM v n) (hp : 2 ^ 63 < p) {i : ℕ} (hi : i < n) : (v i Cell.hi).val < 2 ^ 62 :=
  (T.cell hi).hi_lt (by omega)

/-- The child value of a linked side: the atom (`w = 0`) or the serial of the child row (`w = 1`). -/
theorem side_xF {i w id a lo hi : ℕ} {X : Noun} (hs : SideLink v n N i w id a lo hi X) :
    (v i w = 0 ∧ xF (v i) w id a = v i a ∧ X = .atom (v i a).val) ∨
      (v i w = 1 ∧ ∃ c < n, xF (v i) w id a = v c Cell.idx ∧ N c = X ∧ v c Cell.lo = v i lo ∧
        v c Cell.hi = v i hi) := by
  rcases hs with ⟨hw, hX⟩ | ⟨hw, c, hc, hid, hN, hlo, hhi⟩
  · exact Or.inl ⟨hw, by simp [xF, hw], hX⟩
  · exact Or.inr ⟨hw, c, hc, by simp [xF, hw, hid], hN, hlo, hhi⟩

/-- The rank of a linked side. -/
theorem TableM.side_rank (T : TableM v n) (hp : 2 ^ 63 < p) {i w id a lo hi : ℕ} {X : Noun}
    (hatom : v i w = 0 → v i lo = 0 ∧ v i hi = 0) (hs : SideLink v n N i w id a lo hi X)
    (ih : ∀ c < n, N c = X → rk (v c) = nCells X) :
    (v i lo).val < 2 ^ 62 ∧ (v i hi).val < 2 ^ 62 ∧ (v i hi).val * 2 ^ 62 + (v i lo).val = nCells X := by
  rcases hs with ⟨hw, hX⟩ | ⟨hw, c, hc, hid, hN, hlo, hhi⟩
  · obtain ⟨h1, h2⟩ := hatom hw
    rw [h1, h2, hX]; simp [nCells]
  · rw [← hlo, ← hhi]
    exact ⟨T.lo_lt hp hc, T.hi_lt hp hc, ih c hc hN⟩

/-- **The rank of every row is the number of cells of its noun.** -/
theorem TableM.rank_eq_cells (T : TableM v n) (L : NounLink v n N) (hp : 2 ^ 63 < p) :
    ∀ m : Noun, ∀ i < n, N i = m → rk (v i) = nCells m := by
  intro m
  induction m with
  | atom x =>
    intro i hi hN
    obtain ⟨A, B, hNi, -, -⟩ := L.link i hi
    rw [hNi] at hN; cases hN
  | cell A B ihA ihB =>
    intro i hi hN
    obtain ⟨A', B', hNi, hl, hr⟩ := L.link i hi
    rw [hNi] at hN
    injection hN with hA hB
    subst hA; subst hB
    have hc := T.cell hi
    have hatomL : v i Cell.wL = 0 → v i Cell.loL = 0 ∧ v i Cell.hiL = 0 := fun hw => by
      have h1 := hc.aLlo; have h2 := hc.aLhi
      change (1 - v i Cell.wL) * v i Cell.loL = 0 at h1
      change (1 - v i Cell.wL) * v i Cell.hiL = 0 at h2
      rw [hw, sub_zero, one_mul] at h1 h2; exact ⟨h1, h2⟩
    have hatomR : v i Cell.wR = 0 → v i Cell.loR = 0 ∧ v i Cell.hiR = 0 := fun hw => by
      have h1 := hc.aRlo; have h2 := hc.aRhi
      change (1 - v i Cell.wR) * v i Cell.loR = 0 at h1
      change (1 - v i Cell.wR) * v i Cell.hiR = 0 at h2
      rw [hw, sub_zero, one_mul] at h1 h2; exact ⟨h1, h2⟩
    obtain ⟨l1, l2, l3⟩ := T.side_rank hp hatomL hl ihA
    obtain ⟨r1, r2, r3⟩ := T.side_rank hp hatomR hr ihB
    have := rank_rec hp hc l1 l2 r1 r2
    change rk (v i) = _ at this
    rw [this]; simp only [nCells]; rw [← l3, ← r3]; rfl

/-- A linked side compared: if the side's `(w, x)` is lexicographically smaller at row `i` than at row `j`, the
child nouns are `nlt`-ordered (the cell case is the induction hypothesis at the child rows). -/
theorem TableM.side_lt (T : TableM v n) (L : NounLink v n N) (hnp : n ≤ p) {i j w id a lo hi : ℕ}
    {X Y : Noun} (hsi : SideLink v n N i w id a lo hi X) (hsj : SideLink v n N j w id a lo hi Y)
    (hlt : (v i w).val < (v j w).val ∨
      ((v i w).val = (v j w).val ∧ (xF (v i) w id a).val < (xF (v j) w id a).val))
    (ih : ∀ c c', c < c' → c' < n → N c = X → nlt X (N c')) : nlt X Y := by
  rcases side_xF hsi with ⟨wi, xi, hX⟩ | ⟨wi, c, hc, xi, hX, -⟩ <;>
    rcases side_xF hsj with ⟨wj, xj, hY⟩ | ⟨wj, c', hc', xj, hY, -⟩
  · rw [wi, wj, xi, xj] at hlt
    rw [hX, hY, nlt_atom_atom]
    simpa using hlt
  · obtain ⟨A, B, hN, -, -⟩ := L.link c' hc'
    rw [hX, ← hY, hN]; exact nlt_atom_cell
  · rw [wi, wj, ZMod.val_one, ZMod.val_zero] at hlt; omega
  · rw [xi, xj, T.idx_row c hc, T.idx_row c' hc', val_natCast_lt (by omega), val_natCast_lt (by omega),
      wi, wj] at hlt
    have hcc : c < c' := by omega
    rw [← hY]; exact ih c c' hcc hc' hX

/-- A linked side with equal `(w, x)` at rows `i` and `j` has equal child nouns. -/
theorem TableM.side_eq (T : TableM v n) (hnp : n ≤ p) {i j w id a lo hi : ℕ}
    {X Y : Noun} (hsi : SideLink v n N i w id a lo hi X) (hsj : SideLink v n N j w id a lo hi Y)
    (hw : v i w = v j w) (hx : xF (v i) w id a = xF (v j) w id a) : X = Y := by
  rcases side_xF hsi with ⟨wi, xi, hX⟩ | ⟨wi, c, hc, xi, hX, -⟩ <;>
    rcases side_xF hsj with ⟨wj, xj, hY⟩ | ⟨wj, c', hc', xj, hY, -⟩
  · rw [hX, hY, ← xi, ← xj, hx]
  · rw [wi, wj] at hw; exact (zero_ne_one hw).elim
  · rw [wi, wj] at hw; exact (one_ne_zero hw).elim
  · rw [xi, xj] at hx
    rw [← hX, ← hY, T.idx_inj hnp hc hc' hx]

theorem TableM.limbs (T : TableM v n) (hpG : p = Nock.Atoms.p) {i : ℕ} (hi : i < n) :
    (kF (v i) 3).val = (xF (v i) Cell.wL Cell.idL Cell.aL).val / 2 ^ 32 ∧
    (kF (v i) 4).val = (xF (v i) Cell.wL Cell.idL Cell.aL).val % 2 ^ 32 ∧
    (kF (v i) 6).val = (xF (v i) Cell.wR Cell.idR Cell.aR).val / 2 ^ 32 ∧
    (kF (v i) 7).val = (xF (v i) Cell.wR Cell.idR Cell.aR).val % 2 ^ 32 ∧
    (1 - v i Cell.wL) * v i Cell.idL = 0 ∧ v i Cell.wL * v i Cell.aL = 0 ∧
    (1 - v i Cell.wR) * v i Cell.idR = 0 ∧ v i Cell.wR * v i Cell.aR = 0 :=
  limbs_canon hpG (T.mrow hi)

theorem hp63_of (hpG : p = Nock.Atoms.p) : 2 ^ 63 < p := by rw [hpG, pG]; norm_num

/-- **Strict ⇒ sorted nouns**: in a table satisfying `canonM` and the cell base gates, with the noun link, the
row nouns are strictly increasing in `nlt`. Induction on the noun: the first differing key component is the
rank (`nCells`), or a side's kind, or a side's value (an atom value, or a child serial = a smaller row, where the
induction hypothesis applies). -/
theorem TableM.nouns_sorted (T : TableM v n) (L : NounLink v n N) (hpG : p = Nock.Atoms.p) (hnp : n ≤ p) :
    ∀ i j, i < j → j < n → nlt (N i) (N j) := by
  have hp := hp63_of hpG
  suffices H : ∀ m : Noun, ∀ i j, i < j → j < n → N i = m → nlt m (N j) from
    fun i j hij hj => H (N i) i j hij hj rfl
  intro m
  induction m with
  | atom x =>
    intro i j hij hj hN
    obtain ⟨A, B, hNi, -, -⟩ := L.link i (by omega)
    rw [hNi] at hN; cases hN
  | cell A B ihA ihB =>
    intro i j hij hj hN
    have hi : i < n := by omega
    obtain ⟨A', B', hNi, hli, hri⟩ := L.link i hi
    have hNi' := hNi
    rw [hN] at hNi'
    injection hNi' with hA hB
    subst hA; subst hB
    obtain ⟨A2, B2, hNj, hlj, hrj⟩ := L.link j hj
    have hRi := T.rank_eq_cells L hp _ i hi hNi
    have hRj := T.rank_eq_cells L hp _ j hj hNj
    simp only [nCells, rk] at hRi hRj
    have hloi := T.lo_lt hp hi
    have hloj := T.lo_lt hp hj
    obtain ⟨c3i, c4i, c6i, c7i, -⟩ := T.limbs hpG hi
    obtain ⟨c3j, c4j, c6j, c7j, -⟩ := T.limbs hpG hj
    have hlex := (T.sorted hp i j hij hj).cases
    rw [hNj, nlt_cell]
    simp only [keyNat] at hlex
    change (v i Cell.hi).val < (v j Cell.hi).val ∨ ((v i Cell.hi).val = (v j Cell.hi).val ∧
      ((v i Cell.lo).val < (v j Cell.lo).val ∨ ((v i Cell.lo).val = (v j Cell.lo).val ∧
      (((v i Cell.wL).val < (v j Cell.wL).val ∨ ((v i Cell.wL).val = (v j Cell.wL).val ∧
        ((kF (v i) 3).val < (kF (v j) 3).val ∨ ((kF (v i) 3).val = (kF (v j) 3).val ∧
          (kF (v i) 4).val < (kF (v j) 4).val)))) ∨
       (((v i Cell.wL).val = (v j Cell.wL).val ∧ (kF (v i) 3).val = (kF (v j) 3).val ∧
          (kF (v i) 4).val = (kF (v j) 4).val) ∧
        ((v i Cell.wR).val < (v j Cell.wR).val ∨ ((v i Cell.wR).val = (v j Cell.wR).val ∧
          ((kF (v i) 6).val < (kF (v j) 6).val ∨ ((kF (v i) 6).val = (kF (v j) 6).val ∧
            (kF (v i) 7).val < (kF (v j) 7).val))))))))) at hlex
    rw [c3i, c4i, c6i, c7i, c3j, c4j, c6j, c7j] at hlex
    rw [two62] at hloi hloj hRi hRj
    rcases hlex with h0 | ⟨e0, h1 | ⟨e1, hrest⟩⟩
    · left; nlinarith
    · left; omega
    · right
      refine ⟨by omega, ?_⟩
      rcases hrest with hL | ⟨⟨e2, e3, e4⟩, hR⟩
      · refine Or.inl (T.side_lt L hnp hli hlj ?_ ihA)
        rcases hL with h | ⟨h, h'⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, divmod_lt h'⟩
      · have hw : v i Cell.wL = v j Cell.wL := ZMod.val_injective p e2
        have hx : xF (v i) Cell.wL Cell.idL Cell.aL = xF (v j) Cell.wL Cell.idL Cell.aL :=
          ZMod.val_injective p (divmod_eq e3 e4)
        refine Or.inr ⟨T.side_eq hnp hli hlj hw hx, T.side_lt L hnp hri hrj ?_ ihB⟩
        rcases hR with h | ⟨h, h'⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, divmod_lt h'⟩

end Link

/-! ## 9. Set ⇒ list -/

section SetList
variable {p : ℕ} [Fact p.Prime] {v v' : ℕ → ℕ → ZMod p} {n n' : ℕ} {N N' : ℕ → Noun}

/-- **The noun list of a sorted linked table is `Pairwise nlt`.** -/
theorem TableM.nouns_pairwise (T : TableM v n) (L : NounLink v n N) (hpG : p = Nock.Atoms.p) (hnp : n ≤ p) :
    ((List.range n).map N).Pairwise nlt :=
  pairwise_range_map N (T.nouns_sorted L hpG hnp)

/-- **Distinct rows carry distinct nouns.** -/
theorem TableM.nouns_inj (T : TableM v n) (L : NounLink v n N) (hpG : p = Nock.Atoms.p) (hnp : n ≤ p)
    {i j : ℕ} (hi : i < n) (hj : j < n) (h : N i = N j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact nlt_irrefl (N j) (h ▸ T.nouns_sorted L hpG hnp i j hlt hj)
  · exact nlt_irrefl (N i) (h ▸ T.nouns_sorted L hpG hnp j i hlt hi)

theorem mem_range_map_iff {α : Type*} (f : ℕ → α) (n : ℕ) (x : α) :
    x ∈ (List.range n).map f ↔ ∃ i < n, f i = x := by
  simp [List.mem_map, List.mem_range]

/-- **Set ⇒ list**: two sorted linked tables with the same noun SET have the same noun LIST. -/
theorem nouns_eq_of_set (T : TableM v n) (L : NounLink v n N) (T' : TableM v' n') (L' : NounLink v' n' N')
    (hpG : p = Nock.Atoms.p) (hnp : n ≤ p) (hnp' : n' ≤ p)
    (hset : ∀ m, (∃ i < n, N i = m) ↔ (∃ j < n', N' j = m)) : n = n' ∧ ∀ i < n, N i = N' i := by
  have hl := eq_of_pairwise_of_mem_iff nlt nlt_asymm _ _ (T.nouns_pairwise L hpG hnp)
    (T'.nouns_pairwise L' hpG hnp') fun x => by rw [mem_range_map_iff, mem_range_map_iff]; exact hset x
  have hn : n = n' := by simpa using congrArg List.length hl
  refine ⟨hn, fun i hi => ?_⟩
  have := congrArg (fun l => l[i]?) hl
  simpa [List.getElem?_map, hi, hn ▸ hi] using this

/-- The side columns from `(w, x)`: `id = w·x`, `a = (1 − w)·x` (the child-kind pins). -/
theorem id_a_of {F : Type} [Field F] {w id a : F} (hw : w = 0 ∨ w = 1) (h1 : (1 - w) * id = 0) (h2 : w * a = 0) :
    id = w * (w * id + (1 - w) * a) ∧ a = (1 - w) * (w * id + (1 - w) * a) := by
  rcases hw with rfl | rfl
  · simp at h1; simp [h1]
  · simp at h2; simp [h2]

/-- A linked side agrees between two tables with the same nouns row by row. -/
theorem side_agree (T : TableM v n) (L : NounLink v n N) (T' : TableM v' n) (hpG : p = Nock.Atoms.p)
    (hnp : n ≤ p) (hN : ∀ i < n, N i = N' i) {i w id a lo hi : ℕ} {X : Noun}
    (hs : SideLink v n N i w id a lo hi X) (hs' : SideLink v' n N' i w id a lo hi X) :
    v i w = v' i w ∧ xF (v i) w id a = xF (v' i) w id a := by
  rcases side_xF hs with ⟨wi, xi, hX⟩ | ⟨wi, c, hc, xi, hX, -⟩ <;>
    rcases side_xF hs' with ⟨wj, xj, hY⟩ | ⟨wj, c', hc', xj, hY, -⟩
  · rw [hX] at hY
    injection hY with hval
    refine ⟨wi.trans wj.symm, ?_⟩
    rw [xi, xj]; exact ZMod.val_injective p hval
  · obtain ⟨A, B, hN', -, -⟩ := (L.link c' hc')
    rw [hN c' hc'] at hN'
    rw [hX, hN'] at hY; cases hY
  · obtain ⟨A, B, hNc, -, -⟩ := L.link c hc
    rw [hNc] at hX; rw [← hX] at hY; cases hY
  · have hcc : c = c' := T.nouns_inj L hpG hnp hc hc' (by rw [hX, hN c' hc', hY])
    subst hcc
    refine ⟨wi.trans wj.symm, ?_⟩
    rw [xi, xj, T.idx_row c hc, T'.idx_row c hc]

/-- **Equal rows**: two sorted linked tables with the same noun SET agree, row by row, on `idx`, the child kinds
`wL wR`, the child serials `idL idR`, the atom columns `aL aR`, and the rank limbs `lo hi`. -/
theorem rows_eq_of_set (T : TableM v n) (L : NounLink v n N) (T' : TableM v' n') (L' : NounLink v' n' N')
    (hpG : p = Nock.Atoms.p) (hnp : n ≤ p) (hnp' : n' ≤ p)
    (hset : ∀ m, (∃ i < n, N i = m) ↔ (∃ j < n', N' j = m)) :
    n = n' ∧ ∀ i < n, N i = N' i ∧ v i Cell.idx = v' i Cell.idx ∧
      v i Cell.wL = v' i Cell.wL ∧ v i Cell.idL = v' i Cell.idL ∧ v i Cell.aL = v' i Cell.aL ∧
      v i Cell.wR = v' i Cell.wR ∧ v i Cell.idR = v' i Cell.idR ∧ v i Cell.aR = v' i Cell.aR ∧
      v i Cell.lo = v' i Cell.lo ∧ v i Cell.hi = v' i Cell.hi := by
  obtain ⟨hn, hN⟩ := nouns_eq_of_set T L T' L' hpG hnp hnp' hset
  subst hn
  have hp := hp63_of hpG
  refine ⟨rfl, fun i hi => ?_⟩
  obtain ⟨A, B, hNi, hl, hr⟩ := L.link i hi
  obtain ⟨A', B', hNi', hl', hr'⟩ := L'.link i hi
  rw [← hN i hi, hNi] at hNi'
  injection hNi' with hA hB
  subst hA; subst hB
  obtain ⟨wl, xl⟩ := side_agree T L T' hpG hnp hN hl hl'
  obtain ⟨wr, xr⟩ := side_agree T L T' hpG hnp hN hr hr'
  obtain ⟨-, -, -, -, l1, l2, r1, r2⟩ := T.limbs hpG hi
  obtain ⟨-, -, -, -, l1', l2', r1', r2'⟩ := T'.limbs hpG hi
  have iaL := id_a_of (w := v i Cell.wL) (T.cell hi).wL l1 l2
  have iaL' := id_a_of (w := v' i Cell.wL) (T'.cell hi).wL l1' l2'
  have iaR := id_a_of (w := v i Cell.wR) (T.cell hi).wR r1 r2
  have iaR' := id_a_of (w := v' i Cell.wR) (T'.cell hi).wR r1' r2'
  simp only [xF] at xl xr
  have hR := T.rank_eq_cells L hp _ i hi rfl
  have hR' := T'.rank_eq_cells L' hp _ i hi rfl
  rw [hN i hi] at hR
  have hlo := T.lo_lt hp hi
  have hlo' := T'.lo_lt hp hi
  unfold rk at hR hR'
  rw [two62] at hR hR' hlo hlo'
  have hhi : (v i Cell.hi).val = (v' i Cell.hi).val := by omega
  have hlo2 : (v i Cell.lo).val = (v' i Cell.lo).val := by omega
  refine ⟨hN i hi, by rw [T.idx_row i hi, T'.idx_row i hi], wl, ?_, ?_, wr, ?_, ?_,
    ZMod.val_injective p hlo2, ZMod.val_injective p hhi⟩
  · rw [iaL.1, iaL'.1, xl, wl]
  · rw [iaL.2, iaL'.2, xl, wl]
  · rw [iaR.1, iaR'.1, xr, wr]
  · rw [iaR.2, iaR'.2, xr, wr]

/-- **Provider records are pairwise distinct across rows** whenever they carry (an injective image of) the row's
`idx` in some coordinate: the validity key `vKeyP`, the export keys and `keyH` all do. -/
theorem TableM.records_inj {m : ℕ} {Lt : Type*} (T : TableM v n) (hnp : n ≤ p) (rec : ℕ → Fin m → Lt)
    (c : Fin m) (φ : ZMod p → Lt) (hφ : Function.Injective φ) (hrec : ∀ i < n, rec i c = φ (v i Cell.idx))
    {i j : ℕ} (hi : i < n) (hj : j < n) (h : rec i = rec j) : i = j := by
  have := congrFun h c
  rw [hrec i hi, hrec j hj] at this
  exact T.idx_inj hnp hi hj (hφ this)

theorem TableM.records_nodup {m : ℕ} {Lt : Type*} (T : TableM v n) (hnp : n ≤ p) (rec : ℕ → Fin m → Lt)
    (c : Fin m) (φ : ZMod p → Lt) (hφ : Function.Injective φ) (hrec : ∀ i < n, rec i c = φ (v i Cell.idx)) :
    ((List.range n).map rec).Nodup :=
  (List.nodup_range).map_on fun x hx y hy h =>
    T.records_inj hnp rec c φ hφ hrec (List.mem_range.mp hx) (List.mem_range.mp hy) h

end SetList

/-! ## 10. From the side RAP to the row-local gates -/

section Bridge
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]

/-- The row values of the cell side trace at the nodes `ω^i`. -/
def vM (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) (ω : ZMod p) (i j : ℕ) : ZMod p :=
  (Reify.envOfTrace (sideMQ tr ax) ω (ω ^ i) (fun _ => 0) (fun _ => 0)).trace j

theorem envOfTrace_vM (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) (ω : ZMod p) (i : ℕ) :
    Reify.envOfTrace (sideMQ tr ax) ω (ω ^ i) (fun _ => 0) (fun _ => 0) = envAt (vM tr ax ω) i := by
  unfold envAt
  rw [show vM tr ax ω (i + 1) = fun j =>
      (Reify.envOfTrace (sideMQ tr ax) ω (ω * ω ^ i) (fun _ => 0) (fun _ => 0)).trace j by
    funext j; simp only [vM, pow_succ']]
  rfl

theorem vM_base (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) (ω : ZMod p) (i : ℕ) {j : ℕ} (hj : j < 134) :
    vM tr ax ω i j = (tr.M ⟨j, by omega⟩).eval (ω ^ i) := by
  have hw : j < (canonMT (F := ZMod p)).width 3 := by rw [canonMT_width]; omega
  unfold vM Reify.envOfTrace
  simp only [hw, ↓reduceDIte]
  unfold sideMQ
  simp only [hj, ↓reduceDIte]

theorem vM_aux (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p)) (ω : ZMod p) (i : ℕ) {c : ℕ} (hc : c < 200) :
    vM tr ax ω i (SideM.A + c) = (ax.M ⟨c, hc⟩).eval (ω ^ i) := by
  have hw : SideM.A + c < (canonMT (F := ZMod p)).width 3 := by rw [canonMT_width]; simp only [SideM.A]; omega
  have hn : ¬ (SideM.A + c < 134) := by simp only [SideM.A]; omega
  unfold vM Reify.envOfTrace
  simp only [hw, ↓reduceDIte]
  unfold sideMQ
  simp only [hn, ↓reduceDIte]
  exact congrArg (fun k => (ax.M k).eval (ω ^ i)) (Fin.ext (by simp only [SideM.A]; omega))

theorem mem_rows {n : ℕ} (nodes : Fin n → ZMod p) (i : Fin n) : nodes i ∈ rowNodeSet nodes :=
  mem_rowNodeSet nodes i

/-- **The side RAP gives the row-local gates**: at the canonical layout, `canonM`'s satisfaction is every side
gate vanishing at every row of the row values `vM`. -/
theorem rows_of_canonM (b : Basis (Fin 3) (ZMod p) K) {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1}
    {c : P8PublicClaim} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (hM : (canonM b (canonPb hpG sz c)).Satisfies (sideMQ tr ax)) :
    ∀ i < (canonPb hpG sz c).nC, ∀ g ∈ canonMGates (F := ZMod p),
      g.eval (envAt (vM tr ax (canonPb hpG sz c).orbitC.ω) i) = 0 := by
  intro i hi g hg
  have hl := (expandChip_satisfies_iff_language canonMT b (fun _ => 0) (fun _ => 0) (canonPb hpG sz c).orbitC
    (rowNodeSet (canonPb hpG sz c).nodesC) (sideMQ tr ax)).mp hM ((canonPb hpG sz c).nodesC ⟨i, hi⟩)
    (mem_rows _ _)
  have h1 := hl.1 g hg
  rw [show (canonPb hpG sz c).nodesC ⟨i, hi⟩ = (canonPb hpG sz c).orbitC.ω ^ i from rfl] at h1
  convert h1 using 2
  exact (envOfTrace_vM _ _ _ _).symm

/-- **Transfer of the cell base gates** from any environment agreeing on the first `129` columns. -/
theorem cellBase_transfer {F : Type} [Field F] {e e' : Env F} (ht : ∀ j < 129, e.trace j = e'.trace j)
    (hn : ∀ j < 129, e.traceNext j = e'.traceNext j) (h : ∀ g ∈ Cell.baseGates (F := F), g.eval e' = 0) :
    ∀ g ∈ Cell.baseGates (F := F), g.eval e = 0 :=
  fun g hg => (colsBelow_eval (cellBase_below g hg) ht hn).trans (h g hg)

end Bridge

/-! ## 11. Completeness: the honest aux witnesses -/

section Honest
variable {p : ℕ} [Fact p.Prime]

/-- Bit `k` of `m`, in `ZMod p`. -/
def bitZ (m k : ℕ) : ZMod p := ((m / 2 ^ k % 2 : ℕ) : ZMod p)

theorem bitZ_bool (m k : ℕ) : bitZ (p := p) m k = 0 ∨ bitZ (p := p) m k = 1 := by
  unfold bitZ
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ k) with h | h <;> rw [h] <;> simp

theorem sum_bitZ (m : ℕ) : ∀ n, ∑ k ∈ Finset.range n, (2 : ZMod p) ^ k * bitZ m k = ((m % 2 ^ n : ℕ) : ZMod p)
  | 0 => by simp [Nat.mod_one]
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_bitZ m n, Nat.mod_pow_succ, bitZ]; push_cast; ring

/-- The child value of one side, as a natural number. -/
def xv (r : ℕ → ZMod p) (w id a : ℕ) : ℕ := (xF r w id a).val

/-- **The honest key** of base row values `r`: `(hi, lo, wL, xL / 2^32, xL % 2^32, wR, xR / 2^32, xR % 2^32)`. -/
def keyH (r : ℕ → ZMod p) (k : ℕ) : ℕ :=
  match k with
  | 0 => (r Cell.hi).val
  | 1 => (r Cell.lo).val
  | 2 => (r Cell.wL).val
  | 3 => xv r Cell.wL Cell.idL Cell.aL / 2 ^ 32
  | 4 => xv r Cell.wL Cell.idL Cell.aL % 2 ^ 32
  | 5 => (r Cell.wR).val
  | 6 => xv r Cell.wR Cell.idR Cell.aR / 2 ^ 32
  | _ => xv r Cell.wR Cell.idR Cell.aR % 2 ^ 32

/-- The first differing component of two keys (`8` if none below `8`). -/
def firstDiff (a b : ℕ → ℕ) : ℕ :=
  Nat.find (⟨8, Or.inl rfl⟩ : ∃ k, k = 8 ∨ (k < 8 ∧ a k ≠ b k))

theorem firstDiff_spec {a b : ℕ → ℕ} (h : LexLt a b) :
    firstDiff a b < 8 ∧ (∀ j < firstDiff a b, a j = b j) ∧ a (firstDiff a b) < b (firstDiff a b) := by
  obtain ⟨k, hk8, hk, hlt⟩ := h
  have hle : firstDiff a b ≤ k := Nat.find_min' _ (Or.inr ⟨hk8, hlt.ne⟩)
  have heq : ∀ j < firstDiff a b, a j = b j := fun j hj => by
    have h1 := Nat.find_min (⟨8, Or.inl rfl⟩ : ∃ k, k = 8 ∨ (k < 8 ∧ a k ≠ b k)) (m := j) hj
    push Not at h1
    exact h1.2 (by omega)
  have hs : firstDiff a b = 8 ∨ (firstDiff a b < 8 ∧ a (firstDiff a b) ≠ b (firstDiff a b)) :=
    Nat.find_spec (⟨8, Or.inl rfl⟩ : ∃ k, k = 8 ∨ (k < 8 ∧ a k ≠ b k))
  have hk0 : firstDiff a b = k := by
    rcases Nat.lt_or_ge (firstDiff a b) k with h1 | h1
    · rcases hs with h2 | ⟨-, h2⟩
      · omega
      · exact (h2 (hk _ h1)).elim
    · omega
  refine ⟨by omega, heq, ?_⟩
  rw [hk0]; exact hlt

/-- **The honest aux values** of row `i` (aux column `c < 200`) of the base rows `t` (`n` rows): the four limb
bit blocks, the two inverse-or-zero columns, then (outside the last row) the one-hot at the first differing key
component and the bits of the difference minus one; `0` on the last row. -/
def auxH (t : ℕ → ℕ → ZMod p) (n i c : ℕ) : ZMod p :=
  if c < 32 then bitZ (xv (t i) Cell.wL Cell.idL Cell.aL / 2 ^ 32) c
  else if c < 64 then bitZ (xv (t i) Cell.wL Cell.idL Cell.aL % 2 ^ 32) (c - 32)
  else if c < 96 then bitZ (xv (t i) Cell.wR Cell.idR Cell.aR / 2 ^ 32) (c - 64)
  else if c < 128 then bitZ (xv (t i) Cell.wR Cell.idR Cell.aR % 2 ^ 32) (c - 96)
  else if c = 128 then (((xv (t i) Cell.wL Cell.idL Cell.aL / 2 ^ 32 : ℕ) : ZMod p) - (2 ^ 32 - 1))⁻¹
  else if c = 129 then (((xv (t i) Cell.wR Cell.idR Cell.aR / 2 ^ 32 : ℕ) : ZMod p) - (2 ^ 32 - 1))⁻¹
  else if i + 1 = n then 0
  else if c < 138 then (if c - 130 = firstDiff (keyH (t i)) (keyH (t (i + 1))) then 1 else 0)
  else bitZ (keyH (t (i + 1)) (firstDiff (keyH (t i)) (keyH (t (i + 1)))) -
    keyH (t i) (firstDiff (keyH (t i)) (keyH (t (i + 1)))) - 1) (c - 138)

/-- **The honest side row** `i`: the base columns, then the `200` aux values, then `0`. -/
def fullH (t : ℕ → ℕ → ZMod p) (n i j : ℕ) : ZMod p :=
  if j < 134 then t i j else if j < 334 then auxH t n i (j - 134) else 0

variable {t : ℕ → ℕ → ZMod p} {n i : ℕ}

theorem fullH_base {j : ℕ} (hj : j < 134) : fullH t n i j = t i j := by
  unfold fullH; exact ite_eq_left hj

theorem fullH_aux {c : ℕ} (hc : c < 200) : fullH t n i (SideM.A + c) = auxH t n i c := by
  unfold fullH
  rw [ite_eq_right (by simp only [SideM.A]; omega), ite_eq_left (by simp only [SideM.A]; omega)]
  exact congrArg (auxH t n i) (by simp only [SideM.A]; omega)

theorem xF_fullH {w id a : ℕ} (hw : w < 134) (hid : id < 134) (ha : a < 134) :
    xF (fullH t n i) w id a = xF (t i) w id a := by
  simp only [xF, fullH_base hw, fullH_base hid, fullH_base ha]

theorem auxH_bool {c : ℕ} (hc : c < 128 ∨ (130 ≤ c ∧ c < 200)) : auxH t n i c = 0 ∨ auxH t n i c = 1 := by
  unfold auxH
  split_ifs <;> first | exact bitZ_bool _ _ | (left; rfl) | (right; rfl) | omega

theorem auxH_hL {m : ℕ} (hm : m < 32) : auxH t n i m = bitZ (xv (t i) Cell.wL Cell.idL Cell.aL / 2 ^ 32) m := by
  unfold auxH; exact ite_eq_left hm

theorem auxH_lL {m : ℕ} (hm : m < 32) :
    auxH t n i (32 + m) = bitZ (xv (t i) Cell.wL Cell.idL Cell.aL % 2 ^ 32) m := by
  unfold auxH; rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem auxH_hR {m : ℕ} (hm : m < 32) :
    auxH t n i (64 + m) = bitZ (xv (t i) Cell.wR Cell.idR Cell.aR / 2 ^ 32) m := by
  unfold auxH; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem auxH_lR {m : ℕ} (hm : m < 32) :
    auxH t n i (96 + m) = bitZ (xv (t i) Cell.wR Cell.idR Cell.aR % 2 ^ 32) m := by
  unfold auxH
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
    Nat.add_sub_cancel_left]

theorem auxH_t (side : ℕ) (hs : side < 2) :
    auxH t n i (128 + side) = ((((if side = 0 then xv (t i) Cell.wL Cell.idL Cell.aL
      else xv (t i) Cell.wR Cell.idR Cell.aR) / 2 ^ 32 : ℕ) : ZMod p) - (2 ^ 32 - 1))⁻¹ := by
  unfold auxH
  interval_cases side
  · simp
  · simp

theorem auxH_last (hl : i + 1 = n) {c : ℕ} (hc : 130 ≤ c) : auxH t n i c = 0 := by
  unfold auxH
  simp only [show ¬ c < 32 by omega, show ¬ c < 64 by omega, show ¬ c < 96 by omega, show ¬ c < 128 by omega,
    show c ≠ 128 by omega, show c ≠ 129 by omega, hl, ite_true, ite_false]

theorem auxH_s (hl : ¬ i + 1 = n) {k : ℕ} (hk : k < 8) :
    auxH t n i (130 + k) = if k = firstDiff (keyH (t i)) (keyH (t (i + 1))) then 1 else 0 := by
  unfold auxH
  simp only [show ¬ 130 + k < 32 by omega, show ¬ 130 + k < 64 by omega, show ¬ 130 + k < 96 by omega,
    show ¬ 130 + k < 128 by omega, show 130 + k ≠ 128 by omega, show 130 + k ≠ 129 by omega, hl,
    show 130 + k < 138 by omega, show 130 + k - 130 = k by omega, ite_true, ite_false]

theorem auxH_d (hl : ¬ i + 1 = n) {m : ℕ} (hm : m < 62) :
    auxH t n i (138 + m) = bitZ (keyH (t (i + 1)) (firstDiff (keyH (t i)) (keyH (t (i + 1)))) -
      keyH (t i) (firstDiff (keyH (t i)) (keyH (t (i + 1)))) - 1) m := by
  unfold auxH
  simp only [show ¬ 138 + m < 32 by omega, show ¬ 138 + m < 64 by omega, show ¬ 138 + m < 96 by omega,
    show ¬ 138 + m < 128 by omega, show 138 + m ≠ 128 by omega, show 138 + m ≠ 129 by omega, hl,
    show ¬ 138 + m < 138 by omega, show 138 + m - 138 = m by omega, ite_false]

theorem xv_lt (hpG : p = Nock.Atoms.p) (r : ℕ → ZMod p) (w id a : ℕ) : xv r w id a < 2 ^ 64 := by
  have := ZMod.val_lt (xF r w id a)
  have hpv := hpG.trans pG
  unfold xv; omega

/-- A limb block of the honest row sums to its limb. -/
theorem limb_sum {e : Env (ZMod p)} {base M : ℕ} (hb : ∀ m < 32, e.trace (base + m) = bitZ M m)
    (hM : M < 2 ^ 32) : (bitSum base 32 : CoeffExpr (ZMod p)).eval e = (M : ZMod p) := by
  rw [bitSum_eval, Finset.sum_congr rfl fun m hm => by rw [hb m (Finset.mem_range.mp hm)], sum_bitZ,
    Nat.mod_eq_of_lt hM]

theorem fullH_hL {m : ℕ} (hm : m < 32) :
    fullH t n i (SideM.bLh 0 + m) = bitZ (xv (t i) Cell.wL Cell.idL Cell.aL / 2 ^ 32) m := by
  rw [show SideM.bLh 0 + m = SideM.A + m by unfold SideM.bLh; omega, fullH_aux (by omega), auxH_hL hm]

theorem fullH_lL {m : ℕ} (hm : m < 32) :
    fullH t n i (SideM.bLl 0 + m) = bitZ (xv (t i) Cell.wL Cell.idL Cell.aL % 2 ^ 32) m := by
  rw [show SideM.bLl 0 + m = SideM.A + (32 + m) by unfold SideM.bLl; omega, fullH_aux (by omega), auxH_lL hm]

theorem fullH_hR {m : ℕ} (hm : m < 32) :
    fullH t n i (SideM.bRh 0 + m) = bitZ (xv (t i) Cell.wR Cell.idR Cell.aR / 2 ^ 32) m := by
  rw [show SideM.bRh 0 + m = SideM.A + (64 + m) by unfold SideM.bRh; omega, fullH_aux (by omega), auxH_hR hm]

theorem fullH_lR {m : ℕ} (hm : m < 32) :
    fullH t n i (SideM.bRl 0 + m) = bitZ (xv (t i) Cell.wR Cell.idR Cell.aR % 2 ^ 32) m := by
  rw [show SideM.bRl 0 + m = SideM.A + (96 + m) by unfold SideM.bRl; omega, fullH_aux (by omega), auxH_lR hm]

/-- **The honest key components**: `kF` of the honest side row is the honest key, cast. -/
theorem kF_fullH (hpG : p = Nock.Atoms.p) {k : ℕ} (hk : k < 8) :
    kF (fullH t n i) k = ((keyH (t i) k : ℕ) : ZMod p) := by
  have h64 := xv_lt hpG (t i) Cell.wL Cell.idL Cell.aL
  have h64' := xv_lt hpG (t i) Cell.wR Cell.idR Cell.aR
  rw [show (2 : ℕ) ^ 64 = 18446744073709551616 by norm_num] at h64 h64'
  interval_cases k
  · show fullH t n i Cell.hi = _; rw [fullH_base (by decide)]; exact (ZMod.natCast_zmod_val _).symm
  · show fullH t n i Cell.lo = _; rw [fullH_base (by decide)]; exact (ZMod.natCast_zmod_val _).symm
  · show fullH t n i Cell.wL = _; rw [fullH_base (by decide)]; exact (ZMod.natCast_zmod_val _).symm
  · exact limb_sum (e := ⟨fullH t n i, fun _ => 0, fun _ => 0, fun _ => 0⟩)
      (M := xv (t i) Cell.wL Cell.idL Cell.aL / 2 ^ 32) (fun m hm => fullH_hL hm)
      (by rw [two32]; omega)
  · exact limb_sum (e := ⟨fullH t n i, fun _ => 0, fun _ => 0, fun _ => 0⟩)
      (M := xv (t i) Cell.wL Cell.idL Cell.aL % 2 ^ 32) (fun m hm => fullH_lL hm)
      (Nat.mod_lt _ (by norm_num))
  · show fullH t n i Cell.wR = _; rw [fullH_base (by decide)]; exact (ZMod.natCast_zmod_val _).symm
  · exact limb_sum (e := ⟨fullH t n i, fun _ => 0, fun _ => 0, fun _ => 0⟩)
      (M := xv (t i) Cell.wR Cell.idR Cell.aR / 2 ^ 32) (fun m hm => fullH_hR hm)
      (by rw [two32]; omega)
  · exact limb_sum (e := ⟨fullH t n i, fun _ => 0, fun _ => 0, fun _ => 0⟩)
      (M := xv (t i) Cell.wR Cell.idR Cell.aR % 2 ^ 32) (fun m hm => fullH_lR hm)
      (Nat.mod_lt _ (by norm_num))

/-- **The side gates of one side hold at the honest values** (limb bits of `x`, the inverse-or-zero of
`h − (2^32 − 1)`, and the honest child-kind / rank-inverse pins). -/
theorem sideM_honest (hpG : p = Nock.Atoms.p) {e : Env (ZMod p)} {w id a kb inv h l tc : ℕ}
    (h1 : (1 - e.trace w) * e.trace id = 0) (h2 : e.trace w * e.trace a = 0)
    (h3 : (1 - e.trace w + e.trace w * e.trace kb) * e.trace inv = 0)
    (hh : ∀ k < 32, e.trace (h + k) = bitZ ((xF e.trace w id a).val / 2 ^ 32) k)
    (hl : ∀ k < 32, e.trace (l + k) = bitZ ((xF e.trace w id a).val % 2 ^ 32) k)
    (ht : e.trace tc = ((((xF e.trace w id a).val / 2 ^ 32 : ℕ) : ZMod p) - (2 ^ 32 - 1))⁻¹) :
    ∀ g ∈ sideM (F := ZMod p) w id a kb inv h l tc, g.eval e = 0 := by
  have hpv : p = 18446744069414584321 := hpG.trans pG
  have hxp : (xF e.trace w id a).val < p := ZMod.val_lt _
  have eH := limb_sum (e := e) hh (by rw [two32]; omega)
  have eL := limb_sum (e := e) hl (Nat.mod_lt _ (by norm_num))
  have hX : (xF e.trace w id a) = (((xF e.trace w id a).val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val _).symm
  have hsplit : (((xF e.trace w id a).val : ℕ) : ZMod p) =
      2 ^ 32 * (((xF e.trace w id a).val / 2 ^ 32 : ℕ) : ZMod p) + (((xF e.trace w id a).val % 2 ^ 32 : ℕ) : ZMod p) := by
    conv_lhs => rw [← Nat.div_add_mod (xF e.trace w id a).val (2 ^ 32)]
    push_cast; ring
  simp only [sideM, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  simp only [CoeffExpr.eval, cv, notE, eH, eL, ht]
  refine ⟨?_, ?_, ?_, ?_, h1, h2, h3⟩
  · have hX' : e.trace w * e.trace id + (1 - e.trace w) * e.trace a = (((xF e.trace w id a).val : ℕ) : ZMod p) :=
      hX
    linear_combination hX' + hsplit
  · by_cases hz : (((xF e.trace w id a).val / 2 ^ 32 : ℕ) : ZMod p) - (2 ^ 32 - 1) = 0
    · rw [hz]; ring
    · rw [mul_inv_cancel₀ hz]; ring
  · by_cases hz : (((xF e.trace w id a).val / 2 ^ 32 : ℕ) : ZMod p) - (2 ^ 32 - 1) = 0
    · rw [hz]; ring
    · rw [mul_inv_cancel₀ hz]; ring
  · by_cases hz : (((xF e.trace w id a).val / 2 ^ 32 : ℕ) : ZMod p) - (2 ^ 32 - 1) = 0
    · have hc : ((2 ^ 32 - 1 : ℕ) : ZMod p) = 2 ^ 32 - 1 := by
        rw [Nat.cast_sub (by norm_num)]; push_cast; ring
      have h' : (((xF e.trace w id a).val / 2 ^ 32 : ℕ) : ZMod p) = ((2 ^ 32 - 1 : ℕ) : ZMod p) := by
        rw [hc]; linear_combination hz
      have hq := natCast_inj_lt h' (by omega) (by rw [two32]; omega)
      have h0 : (xF e.trace w id a).val % 2 ^ 32 = 0 := by rw [two32] at hq ⊢; omega
      rw [h0]; simp
    · rw [mul_inv_cancel₀ hz]; ring

/-- Every honest key component is below `2^62`. -/
theorem keyH_lt (hpG : p = Nock.Atoms.p) {r : ℕ → ZMod p} (hwL : r Cell.wL = 0 ∨ r Cell.wL = 1)
    (hwR : r Cell.wR = 0 ∨ r Cell.wR = 1) (hhi : (r Cell.hi).val < 2 ^ 62) (hlo : (r Cell.lo).val < 2 ^ 62) :
    ∀ k < 8, keyH r k < 2 ^ 62 := by
  have h1 := xv_lt hpG r Cell.wL Cell.idL Cell.aL
  have h2 := xv_lt hpG r Cell.wR Cell.idR Cell.aR
  have b1 := bool_val hwL
  have b2 := bool_val hwR
  rw [show (2 : ℕ) ^ 64 = 18446744073709551616 by norm_num] at h1 h2
  intro k hk
  interval_cases k
  · exact hhi
  · exact hlo
  · show (r Cell.wL).val < _; rw [two62]; omega
  · show xv r Cell.wL Cell.idL Cell.aL / 2 ^ 32 < _; rw [two62, two32]; omega
  · show xv r Cell.wL Cell.idL Cell.aL % 2 ^ 32 < _; rw [two62, two32]; omega
  · show (r Cell.wR).val < _; rw [two62]; omega
  · show xv r Cell.wR Cell.idR Cell.aR / 2 ^ 32 < _; rw [two62, two32]; omega
  · show xv r Cell.wR Cell.idR Cell.aR % 2 ^ 32 < _; rw [two62, two32]; omega

/-- **The hypotheses on an honest cell table** (base rows `t`, `n` rows): the last-row mask, boolean child
kinds, the honest child-kind / rank-inverse pins, ranks below `2^62`, and strictly increasing honest keys. -/
structure HonestM (t : ℕ → ℕ → ZMod p) (n : ℕ) : Prop where
  isL : ∀ i < n, t i Cell.isL = if i + 1 = n then 1 else 0
  wL : ∀ i < n, t i Cell.wL = 0 ∨ t i Cell.wL = 1
  wR : ∀ i < n, t i Cell.wR = 0 ∨ t i Cell.wR = 1
  hi : ∀ i < n, (t i Cell.hi).val < 2 ^ 62
  lo : ∀ i < n, (t i Cell.lo).val < 2 ^ 62
  pinL : ∀ i < n, (1 - t i Cell.wL) * t i Cell.idL = 0 ∧ t i Cell.wL * t i Cell.aL = 0 ∧
    (1 - t i Cell.wL + t i Cell.wL * t i CellTwinK.kbL) * t i CellTwinK.invL = 0
  pinR : ∀ i < n, (1 - t i Cell.wR) * t i Cell.idR = 0 ∧ t i Cell.wR * t i Cell.aR = 0 ∧
    (1 - t i Cell.wR + t i Cell.wR * t i CellTwinK.kbR) * t i CellTwinK.invR = 0
  sorted : ∀ i, i + 1 < n → LexLt (keyH (t i)) (keyH (t (i + 1)))

/-- **Completeness of the sort gadget**: at every row of an honest sorted table, with the next row read as the
honest next row (any value on the last row), every side gate of `canonM` vanishes at the honest aux witnesses. -/
theorem honest_gates (hpG : p = Nock.Atoms.p) (H : HonestM t n) (hi : i < n) (nx ch pu : ℕ → ZMod p)
    (hnx : i + 1 < n → nx = fullH t n (i + 1)) :
    ∀ g ∈ canonMGates (F := ZMod p), g.eval ⟨fullH t n i, nx, ch, pu⟩ = 0 := by
  have hisL : fullH t n i Cell.isL = if i + 1 = n then 1 else 0 := by
    rw [fullH_base (by decide)]; exact H.isL i hi
  have hbs : ∀ c < 70, fullH t n i (SideM.A + 130 + c) = 0 ∨ fullH t n i (SideM.A + 130 + c) = 1 :=
    fun c hc => by rw [Nat.add_assoc, fullH_aux (by omega)]; exact auxH_bool (Or.inr ⟨by omega, by omega⟩)
  have hsL : ∀ k < 8, fullH t n i (SideM.s k) = if i + 1 = n then 0 else
      (if k = firstDiff (keyH (t i)) (keyH (t (i + 1))) then 1 else 0) := fun k hk => by
    rw [show SideM.s k = SideM.A + (130 + k) by unfold SideM.s; omega, fullH_aux (by omega)]
    by_cases hl : i + 1 = n
    · rw [auxH_last hl (by omega), ite_eq_left hl]
    · rw [auxH_s hl hk, ite_eq_right hl]
  have hdL : ∀ m < 62, fullH t n i (SideM.d m) = if i + 1 = n then 0 else
      bitZ (keyH (t (i + 1)) (firstDiff (keyH (t i)) (keyH (t (i + 1)))) -
        keyH (t i) (firstDiff (keyH (t i)) (keyH (t (i + 1)))) - 1) m := fun m hm => by
    rw [show SideM.d m = SideM.A + (138 + m) by unfold SideM.d; omega, fullH_aux (by omega)]
    by_cases hl : i + 1 = n
    · rw [auxH_last hl (by omega), ite_eq_left hl]
    · rw [auxH_d hl hm, ite_eq_right hl]
  have hck : ∀ k < 8, kF (fullH t n i) k = ((keyH (t i) k : ℕ) : ZMod p) := fun k hk => kF_fullH hpG hk
  have hs1 : ¬ i + 1 = n → ∀ k ∈ Finset.range 8, fullH t n i (SideM.s k) =
      if firstDiff (keyH (t i)) (keyH (t (i + 1))) = k then 1 else 0 := fun hl k hk => by
    rw [hsL k (Finset.mem_range.mp hk), ite_eq_right hl]
    by_cases h : k = firstDiff (keyH (t i)) (keyH (t (i + 1)))
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  have hhot : ¬ i + 1 = n → ∑ k ∈ Finset.range 8, fullH t n i (SideM.s k) - 1 = 0 := fun hl => by
    obtain ⟨hk8, -, -⟩ := firstDiff_spec (H.sorted i (by omega))
    rw [Finset.sum_congr rfl (hs1 hl), Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr hk8), sub_self]
  have hdif : ¬ i + 1 = n → ∑ k ∈ Finset.range 8, fullH t n i (SideM.s k) * (kF nx k - kF (fullH t n i) k) - 1 -
      ∑ m ∈ Finset.range 62, (2 : ZMod p) ^ m * fullH t n i (SideM.d 0 + m) = 0 := fun hl => by
    have hi1 : i + 1 < n := by omega
    obtain ⟨hk8, -, hklt⟩ := firstDiff_spec (H.sorted i hi1)
    set k0 := firstDiff (keyH (t i)) (keyH (t (i + 1))) with hk0def
    have hK' := keyH_lt hpG (H.wL (i + 1) hi1) (H.wR (i + 1) hi1) (H.hi (i + 1) hi1) (H.lo (i + 1) hi1) k0 hk8
    have hterm : ∀ k ∈ Finset.range 8, fullH t n i (SideM.s k) * (kF nx k - kF (fullH t n i) k) =
        if k0 = k then kF nx k - kF (fullH t n i) k else 0 := fun k hk => by
      rw [hs1 hl k hk]; split_ifs <;> ring
    have hdsum : ∑ m ∈ Finset.range 62, (2 : ZMod p) ^ m * fullH t n i (SideM.d 0 + m) =
        ((keyH (t (i + 1)) k0 - keyH (t i) k0 - 1 : ℕ) : ZMod p) := by
      rw [Finset.sum_congr rfl fun m hm => by
          rw [show SideM.d 0 + m = SideM.d m by unfold SideM.d; omega, hdL m (Finset.mem_range.mp hm),
            ite_eq_right hl],
        sum_bitZ, Nat.mod_eq_of_lt (by omega)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr hk8), hdsum,
      hnx hi1, kF_fullH hpG hk8, hck k0 hk8, Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast; ring
  have hfirst : ¬ i + 1 = n → ∀ j < 7, (List.map (fun k => fullH t n i (SideM.s k))
      (List.filter (fun k => decide (j < k)) (List.range 8))).sum * (kF nx j - kF (fullH t n i) j) = 0 :=
      fun hl j hj => by
    have hi1 : i + 1 < n := by omega
    obtain ⟨hk8, hkeq, -⟩ := firstDiff_spec (H.sorted i hi1)
    set k0 := firstDiff (keyH (t i)) (keyH (t (i + 1))) with hk0def
    by_cases hjk : j < k0
    · rw [hnx hi1, kF_fullH hpG (by omega), hck j (by omega), hkeq j hjk, sub_self, mul_zero]
    · have hmap : (List.map (fun k => fullH t n i (SideM.s k)) (List.filter (fun k => decide (j < k)) (List.range 8))) =
          (List.map (fun k => if k = k0 then (1 : ZMod p) else 0)
            (List.filter (fun k => decide (j < k)) (List.range 8))) := by
        refine List.map_congr_left fun k hk => ?_
        have hk' := List.mem_range.mp (List.mem_filter.mp hk).1
        rw [hs1 hl k (Finset.mem_range.mpr hk')]
        by_cases h : k = k0
        · rw [ite_eq_left h, ite_eq_left h.symm]
        · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
      have hnm : k0 ∉ (List.filter (fun k => decide (j < k)) (List.range 8)) := by
        intro hm; have := (List.mem_filter.mp hm).2; simp at this; omega
      rw [hmap, sum_indicator k0 _ (List.nodup_range.filter _), ite_eq_right hnm, zero_mul]
  rw [canonMGates_parts]
  simp only [List.mem_append, or_imp, forall_and]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro g hg
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
    rw [List.mem_range] at hc
    simp only [CoeffExpr.eval, cv, boolE]
    rw [fullH_aux (by omega)]
    rcases auxH_bool (t := t) (n := n) (i := i) (Or.inl hc) with h | h <;> rw [h] <;> ring
  · intro g hg
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
    rw [List.mem_range] at hc
    simp only [CoeffExpr.eval, cv, boolE]
    rcases hbs c hc with h | h <;> rw [h] <;> ring
  · obtain ⟨p1, p2, p3⟩ := H.pinL i hi
    have hx := xF_fullH (t := t) (n := n) (i := i) (w := Cell.wL) (id := Cell.idL) (a := Cell.aL)
      (by decide) (by decide) (by decide)
    refine sideM_honest hpG (e := ⟨fullH t n i, nx, ch, pu⟩) ?_ ?_ ?_ (fun k hk => ?_) (fun k hk => ?_) ?_
    · simp only [fullH_base (show Cell.wL < 134 by decide), fullH_base (show Cell.idL < 134 by decide)]
      exact p1
    · simp only [fullH_base (show Cell.wL < 134 by decide), fullH_base (show Cell.aL < 134 by decide)]
      exact p2
    · simp only [fullH_base (show Cell.wL < 134 by decide),
        fullH_base (show CellTwinK.kbL < 134 by decide),
        fullH_base (show CellTwinK.invL < 134 by decide)]
      exact p3
    · show fullH t n i (SideM.bLh 0 + k) = _
      rw [hx, fullH_hL hk]; rfl
    · show fullH t n i (SideM.bLl 0 + k) = _
      rw [hx, fullH_lL hk]; rfl
    · show fullH t n i SideM.tL = _
      rw [hx, show SideM.tL = SideM.A + (128 + 0) by simp only [SideM.tL], fullH_aux (by norm_num),
        auxH_t 0 (by norm_num)]
      rfl
  · obtain ⟨p1, p2, p3⟩ := H.pinR i hi
    have hx := xF_fullH (t := t) (n := n) (i := i) (w := Cell.wR) (id := Cell.idR) (a := Cell.aR)
      (by decide) (by decide) (by decide)
    refine sideM_honest hpG (e := ⟨fullH t n i, nx, ch, pu⟩) ?_ ?_ ?_ (fun k hk => ?_) (fun k hk => ?_) ?_
    · simp only [fullH_base (show Cell.wR < 134 by decide), fullH_base (show Cell.idR < 134 by decide)]
      exact p1
    · simp only [fullH_base (show Cell.wR < 134 by decide), fullH_base (show Cell.aR < 134 by decide)]
      exact p2
    · simp only [fullH_base (show Cell.wR < 134 by decide),
        fullH_base (show CellTwinK.kbR < 134 by decide),
        fullH_base (show CellTwinK.invR < 134 by decide)]
      exact p3
    · show fullH t n i (SideM.bRh 0 + k) = _
      rw [hx, fullH_hR hk]; rfl
    · show fullH t n i (SideM.bRl 0 + k) = _
      rw [hx, fullH_lR hk]; rfl
    · show fullH t n i SideM.tR = _
      rw [hx, show SideM.tR = SideM.A + (128 + 1) by simp only [SideM.tR], fullH_aux (by norm_num),
        auxH_t 1 (by norm_num)]
      rfl
  · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    simp only [CoeffExpr.eval, cv, notE, eval_sumList_range, keyN_eval, keyC_eval, bitSum_eval]
    rw [hisL]
    by_cases hl : i + 1 = n
    · rw [ite_eq_left hl]; simp
    · rw [ite_eq_right hl, sub_zero, one_mul, one_mul]
      exact ⟨hhot hl, hdif hl⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
    rw [List.mem_range] at hj
    simp only [CoeffExpr.eval, cv, notE, CoeffExpr.eval_sumList, keyN_eval, keyC_eval]
    rw [hisL]
    by_cases hl : i + 1 = n
    · rw [ite_eq_left hl]; simp
    · rw [ite_eq_right hl, sub_zero, one_mul]
      exact hfirst hl j hj
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
    rw [List.mem_range] at hk
    simp only [CoeffExpr.eval, cv]
    rw [hisL, hsL k hk]
    by_cases hl : i + 1 = n
    · simp [hl]
    · simp [hl]
  · intro g hg
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hg
    rw [List.mem_range] at hm
    simp only [CoeffExpr.eval, cv]
    rw [hisL, hdL m hm]
    by_cases hl : i + 1 = n
    · simp [hl]
    · simp [hl]

end Honest

/-! ## 12. Completeness at the side RAP -/

section HonestRAP
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]

/-- **The honest side trace satisfies `canonM`**: if, at the canonical layout, the side trace's row values are
the honest side rows `fullH t` of an honest sorted table, then `canonM` is satisfied. -/
theorem canonM_of_honest (b : Basis (Fin 3) (ZMod p) K) {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1}
    {c : P8PublicClaim} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)} {t : ℕ → ℕ → ZMod p}
    (H : HonestM t (canonPb hpG sz c).nC)
    (hrow : ∀ i < (canonPb hpG sz c).nC,
      vM tr ax (canonPb hpG sz c).orbitC.ω i = fullH t (canonPb hpG sz c).nC i) :
    (canonM b (canonPb hpG sz c)).Satisfies (sideMQ tr ax) := by
  refine (expandChip_satisfies_iff_language canonMT b (fun _ => 0) (fun _ => 0) (canonPb hpG sz c).orbitC
    (rowNodeSet (canonPb hpG sz c).nodesC) (sideMQ tr ax)).mpr fun x hx => ?_
  obtain ⟨⟨i, hi⟩, rfl⟩ := (mem_rowNodeSet_iff _ x).mp hx
  have hx' : (canonPb hpG sz c).nodesC ⟨i, hi⟩ = (canonPb hpG sz c).orbitC.ω ^ i := rfl
  have henv : envAt (vM tr ax (canonPb hpG sz c).orbitC.ω) i =
      ⟨fullH t (canonPb hpG sz c).nC i, vM tr ax (canonPb hpG sz c).orbitC.ω (i + 1), fun _ => 0, fun _ => 0⟩ := by
    unfold envAt; rw [hrow i hi]
  have hE : Reify.envOfTrace (sideMQ tr ax) (canonPb hpG sz c).orbitC.ω ((canonPb hpG sz c).orbitC.ω ^ i)
      (fun _ => 0) (fun _ => 0) =
      ⟨fullH t (canonPb hpG sz c).nC i, vM tr ax (canonPb hpG sz c).orbitC.ω (i + 1), fun _ => 0, fun _ => 0⟩ :=
    (envOfTrace_vM _ _ _ _).trans henv
  refine ⟨fun g hg => ?_, fun g hg => absurd hg List.not_mem_nil, fun g hg => absurd hg List.not_mem_nil,
    fun g hg => absurd hg List.not_mem_nil⟩
  rw [hx']
  exact (congrArg (CoeffExpr.eval g) hE).trans
    (honest_gates hpG H hi (vM tr ax (canonPb hpG sz c).orbitC.ω (i + 1)) (fun _ => 0) (fun _ => 0)
      (fun h1 => hrow (i + 1) h1) g hg)

end HonestRAP

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.LexLt.trans
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.eq_of_pairwise_of_mem_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.step_field
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.TableM.step
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.TableM.sorted
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.TableM.keys_pairwise
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.TableM.idx_row
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.limbs_canon
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.nlt_asymm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.nlt_trans
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.nlt_trichotomy
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.sortKey_pairwise
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.TableM.rank_eq_cells
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.TableM.nouns_sorted
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.TableM.nouns_inj
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.nouns_eq_of_set
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.rows_eq_of_set
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.TableM.records_nodup
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.rows_of_canonM
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.cellBase_transfer
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.honest_gates
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1.canonM_of_honest
