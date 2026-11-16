/-
  Nock/NockVMROM/Thm54/VclL/Chips/HonestMemPath.lean

  **The honest path chip's columns and gates.**
  The twin of `HonestMemCell` / `HonestMemCellMixed`:

  * `PathVals F Q`: the committed content of one path row (`16` base columns `2…15`, `𝕂′` slots
    `0…15` = `root p l r` fingerprints and `xConsInv pProvInv xAcc pAcc`);
  * `pathCol`, `honestPathQ` (the `112`-column interpolated trace), the environment lemmas;
  * `path_base_gates_hold` (the `20` base gates, given `PathBaseFacts`);
  * `path_qEqs_hold` / `path_mixed_gates_hold` (the `17` `𝕂′` equations / `34` mixed gates, given
    `PathMixedFacts`).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemCellMixed

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

/-- **The committed content of one path row.** -/
structure PathVals (F Q : Type) where
  side : F
  first : F
  last : F
  len : F
  acc : F
  m : F
  cellIdx : F
  rootIdx : F
  bit : ℕ → F
  root : ComputeTable.FP Q
  p : ComputeTable.FP Q
  l : ComputeTable.FP Q
  r : ComputeTable.FP Q
  xConsInv : Q
  pProvInv : Q
  xAcc : Q
  pAcc : Q

namespace PathVals
variable {F Q : Type}

/-- The base-field column `j` (`2 ≤ j < 16`; columns `0`, `1` are the masks). -/
def base (v : PathVals F Q) (j : ℕ) : F :=
  if j = 2 then v.side else if j = 3 then v.first else if j = 4 then v.last
  else if j = 5 then v.len else if j = 6 then v.acc else if j = 7 then v.m
  else if j = 8 then v.cellIdx else if j = 9 then v.rootIdx else v.bit (j - 10)

/-- The `𝕂′` slot `s` (`root p l r` at `0 / 3 / 6 / 9`, then `xConsInv pProvInv xAcc pAcc`). -/
def qslot (v : PathVals F Q) : ℕ → Q
  | 0 => v.root.size | 1 => v.root.dyck | 2 => v.root.leaf
  | 3 => v.p.size | 4 => v.p.dyck | 5 => v.p.leaf
  | 6 => v.l.size | 7 => v.l.dyck | 8 => v.l.leaf
  | 9 => v.r.size | 10 => v.r.dyck | 11 => v.r.leaf
  | 12 => v.xConsInv | 13 => v.pProvInv | 14 => v.xAcc | _ => v.pAcc

end PathVals

section Cols
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K)

def proleVal (v : PathVals F (Quad (algebraMap F K δF))) (ρ : ℕ) : K :=
  if ρ % 2 = 0 then Quad.re _ (v.qslot (ρ / 2)) else Quad.im _ (v.qslot (ρ / 2))

/-- **The path chip's column function**: base columns `2 … 15`, `𝕂`-role `ρ` at `16 + 3ρ + k`. -/
def pathCol {n : ℕ} (vals : Fin n → PathVals F (Quad (algebraMap F K δF))) (j : ℕ) (i : Fin n) : F :=
  if j < 16 then (vals i).base j
  else coord b (proleVal δF (vals i) ((j - 16) / 3)) ⟨(j - 16) % 3, Nat.mod_lt _ (by norm_num)⟩

end Cols

section Env
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (ω : F) (chals pubs : ℕ → K)
  (vals : Fin n → PathVals F (Quad (algebraMap F K δF)))

/-- The honest path trace. -/
abbrev honestPathQ : Fin 112 → F[X] := honestQ hn nodes (pathCol δF b vals) 112

abbrev pathEFh (i : Fin n) : Env F :=
  Reify.envOfTrace (honestPathQ δF b hn nodes vals) ω (nodes i) (slotVal b 16 chals) (slotVal b 16 pubs)

abbrev pathEKh (i : Fin n) : Env K :=
  gatherEnv b ((pathTemplate δF).col0 3) (pathEFh δF b hn nodes ω chals pubs vals i)

theorem pathEFh_base (hinj : Function.Injective nodes) (i : Fin n) {j : ℕ} (h2 : 2 ≤ j) (hj : j < 16) :
    (pathEFh δF b hn nodes ω chals pubs vals i).trace j = (vals i).base j := by
  rw [env_trace hn nodes hinj _ ω _ _ i (show j < 112 by omega)]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  unfold fullCol pathCol
  rw [if_neg h0, if_neg h1, if_pos hj]

theorem pathEFh_next_base (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) {j : ℕ} (h2 : 2 ≤ j) (hj : j < 16) :
    (pathEFh δF b hn nodes ω chals pubs vals i).traceNext j = (vals ⟨(i : ℕ) + 1, hi⟩).base j := by
  rw [env_traceNext hn nodes hinj _ ω _ _ hadj i hi (show j < 112 by omega)]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  unfold fullCol pathCol
  rw [if_neg h0, if_neg h1, if_pos hj]

theorem pathEFh_mask0 (hinj : Function.Injective nodes) (i : Fin n) :
    (pathEFh δF b hn nodes ω chals pubs vals i).trace 0 = if (i : ℕ) = 0 then 1 else 0 := by
  rw [env_trace hn nodes hinj _ ω _ _ i (show 0 < 112 by omega)]
  simp [fullCol]

theorem pathEFh_mask1 (hinj : Function.Injective nodes) (i : Fin n) :
    (pathEFh δF b hn nodes ω chals pubs vals i).trace 1 =
      if i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0 := by
  rw [env_trace hn nodes hinj _ ω _ _ i (show 1 < 112 by omega)]
  simp [fullCol]

theorem path_col0 (r : ℕ) (kind : VarKind) : (pathTemplate δF).col0 3 kind r = 16 + 3 * r := by
  simp [ChipTemplate.col0, pathTemplate_baseCols]

theorem pathEKh_trace (hinj : Function.Injective nodes) (i : Fin n) {r : ℕ} (hr : r < 32) :
    (pathEKh δF b hn nodes ω chals pubs vals i).trace r = proleVal δF (vals i) r := by
  refine gather_trace b _ _ r _ fun k => ?_
  rw [path_col0, env_trace hn nodes hinj _ ω _ _ i (show 16 + 3 * r + (k : ℕ) < 112 by have := k.isLt; omega)]
  have h1 : (16 + 3 * r + (k : ℕ) - 16) / 3 = r := by have := k.isLt; omega
  have h2 : (16 + 3 * r + (k : ℕ) - 16) % 3 = (k : ℕ) := by have := k.isLt; omega
  have h0 : (16 + 3 * r + (k : ℕ)) ≠ 0 := by omega
  have h1' : (16 + 3 * r + (k : ℕ)) ≠ 1 := by omega
  have h3 : ¬ (16 + 3 * r + (k : ℕ)) < 16 := by omega
  unfold fullCol pathCol
  rw [if_neg h0, if_neg h1', if_neg h3, h1]
  exact congrArg (coord b _) (Fin.ext h2)

theorem pathEKh_traceNext (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) {r : ℕ} (hr : r < 32) :
    (pathEKh δF b hn nodes ω chals pubs vals i).traceNext r = proleVal δF (vals ⟨(i : ℕ) + 1, hi⟩) r := by
  refine gather_traceNext b _ _ r _ fun k => ?_
  rw [path_col0, env_traceNext hn nodes hinj _ ω _ _ hadj i hi
    (show 16 + 3 * r + (k : ℕ) < 112 by have := k.isLt; omega)]
  have h1 : (16 + 3 * r + (k : ℕ) - 16) / 3 = r := by have := k.isLt; omega
  have h2 : (16 + 3 * r + (k : ℕ) - 16) % 3 = (k : ℕ) := by have := k.isLt; omega
  have h0 : (16 + 3 * r + (k : ℕ)) ≠ 0 := by omega
  have h1' : (16 + 3 * r + (k : ℕ)) ≠ 1 := by omega
  have h3 : ¬ (16 + 3 * r + (k : ℕ)) < 16 := by omega
  unfold fullCol pathCol
  rw [if_neg h0, if_neg h1', if_neg h3, h1]
  exact congrArg (coord b _) (Fin.ext h2)

theorem pathEKh_ev_var (hinj : Function.Injective nodes) (i : Fin n) {s : ℕ} (hs : s < 16) :
    (QE.var (2 * s) : QE F).ev δF (pathEKh δF b hn nodes ω chals pubs vals i)
        (pathEFh δF b hn nodes ω chals pubs vals i) = (vals i).qslot s := by
  rw [ev_var, pathEKh_trace δF b hn nodes ω chals pubs vals hinj i (by omega),
    pathEKh_trace δF b hn nodes ω chals pubs vals hinj i (show 2 * s + 1 < 32 by omega)]
  have e1 : (2 * s) % 2 = 0 := by omega
  have e2 : (2 * s) / 2 = s := by omega
  have e3 : (2 * s + 1) % 2 ≠ 0 := by omega
  have e4 : (2 * s + 1) / 2 = s := by omega
  simp only [proleVal, e1, e2, e3, e4, if_true, if_false]
  exact Quad.mk_re_im _ _

theorem pathEKh_ev_next (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) {s : ℕ} (hs : s < 16) :
    (QE.next (2 * s) : QE F).ev δF (pathEKh δF b hn nodes ω chals pubs vals i)
        (pathEFh δF b hn nodes ω chals pubs vals i) = (vals ⟨(i : ℕ) + 1, hi⟩).qslot s := by
  rw [ev_next, pathEKh_traceNext δF b hn nodes ω chals pubs vals hinj hadj i hi (by omega),
    pathEKh_traceNext δF b hn nodes ω chals pubs vals hinj hadj i hi (show 2 * s + 1 < 32 by omega)]
  have e1 : (2 * s) % 2 = 0 := by omega
  have e2 : (2 * s) / 2 = s := by omega
  have e3 : (2 * s + 1) % 2 ≠ 0 := by omega
  have e4 : (2 * s + 1) / 2 = s := by omega
  simp only [proleVal, e1, e2, e3, e4, if_true, if_false]
  exact Quad.mk_re_im _ _

theorem pathEKh_chal (i : Fin n) : (pathEKh δF b hn nodes ω chals pubs vals i).chal = chals :=
  funext fun j => gather_chal_path δF b chals _ rfl j

theorem pathEKh_pub (i : Fin n) (j : ℕ) : (pathEKh δF b hn nodes ω chals pubs vals i).pub j = pubs j :=
  gather_pub_path δF b pubs _ rfl j

end Env

section BaseGates
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (ω : F) (chals pubs : ℕ → K)
  (vals : Fin n → PathVals F (Quad (algebraMap F K δF)))

/-- **The row-level facts the `20` path base gates encode** (at row `i`; the masks are resolved:
`first0` is the `isFirst` gate, `lastL` the `isLast` gate, the `…Next` / `…Step` ones are the
`(1 − isLast)` gates at a row with a successor). -/
structure PathBaseFacts {F Q : Type} [Field F] {n : ℕ} (vals : Fin n → PathVals F Q) (i : Fin n) : Prop where
  side_bool : (vals i).side * ((vals i).side - 1) = 0
  first_bool : (vals i).first * ((vals i).first - 1) = 0
  last_bool : (vals i).last * ((vals i).last - 1) = 0
  first0 : (i : ℕ) = 0 → (vals i).first = 1
  lastL : (i : ℕ) + 1 = n → (vals i).last = 1
  firstNext : ∀ hi : (i : ℕ) + 1 < n, (vals ⟨(i : ℕ) + 1, hi⟩).first = (vals i).last
  len_first : (vals i).first * ((vals i).len - 1) = 0
  len_step : ∀ hi : (i : ℕ) + 1 < n,
    (1 - (vals i).last) * (((vals ⟨(i : ℕ) + 1, hi⟩).len - (vals i).len) - 1) = 0
  acc_first : (vals i).first * (((vals i).acc - 2) - (vals i).side) = 0
  acc_step : ∀ hi : (i : ℕ) + 1 < n,
    (1 - (vals i).last) * (((vals ⟨(i : ℕ) + 1, hi⟩).acc - 2 * (vals i).acc) -
      (vals ⟨(i : ℕ) + 1, hi⟩).side) = 0
  root_first : (vals i).first * ((vals i).rootIdx - (vals i).cellIdx) = 0
  root_step : ∀ hi : (i : ℕ) + 1 < n,
    (1 - (vals i).last) * ((vals ⟨(i : ℕ) + 1, hi⟩).rootIdx - (vals i).rootIdx) = 0
  cert : (vals i).last * (((vals i).len + ∑ k ∈ Finset.range 6, (2 : F) ^ k * (vals i).bit k) - 62) = 0
  m_mask : (1 - (vals i).last) * (vals i).m = 0
  bit_bool : ∀ k < 6, (vals i).bit k * ((vals i).bit k - 1) = 0

/-- **The `20` path base gates vanish at the honest environment of row `i`.** -/
theorem path_base_gates_hold (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hf : PathBaseFacts vals i) :
    ∀ g ∈ Path.baseGates (F := F),
      g.eval (pathEFh δF b hn nodes ω chals pubs vals i) = 0 := by
  have hb : ∀ j, 2 ≤ j → j < 16 → (pathEFh δF b hn nodes ω chals pubs vals i).trace j = (vals i).base j :=
    fun j h2 hj => pathEFh_base δF b hn nodes ω chals pubs vals hinj i h2 hj
  have hbn : ∀ hi : (i : ℕ) + 1 < n, ∀ j, 2 ≤ j → j < 16 →
      (pathEFh δF b hn nodes ω chals pubs vals i).traceNext j = (vals ⟨(i : ℕ) + 1, hi⟩).base j :=
    fun hi j h2 hj => pathEFh_next_base δF b hn nodes ω chals pubs vals hinj hadj i hi h2 hj
  have m0 := pathEFh_mask0 δF b hn nodes ω chals pubs vals hinj i
  have m1 := pathEFh_mask1 δF b hn nodes ω chals pubs vals hinj i
  set E := pathEFh δF b hn nodes ω chals pubs vals i with hE
  have t2 : E.trace 2 = (vals i).side := by rw [hb 2 le_rfl (by norm_num)]; simp [PathVals.base]
  have t3 : E.trace 3 = (vals i).first := by rw [hb 3 (by norm_num) (by norm_num)]; simp [PathVals.base]
  have t4 : E.trace 4 = (vals i).last := by rw [hb 4 (by norm_num) (by norm_num)]; simp [PathVals.base]
  have t5 : E.trace 5 = (vals i).len := by rw [hb 5 (by norm_num) (by norm_num)]; simp [PathVals.base]
  have t6 : E.trace 6 = (vals i).acc := by rw [hb 6 (by norm_num) (by norm_num)]; simp [PathVals.base]
  have t7 : E.trace 7 = (vals i).m := by rw [hb 7 (by norm_num) (by norm_num)]; simp [PathVals.base]
  have t8 : E.trace 8 = (vals i).cellIdx := by rw [hb 8 (by norm_num) (by norm_num)]; simp [PathVals.base]
  have t9 : E.trace 9 = (vals i).rootIdx := by rw [hb 9 (by norm_num) (by norm_num)]; simp [PathVals.base]
  have tbit : ∀ k, k < 6 → E.trace (10 + k) = (vals i).bit k := fun k hk => by
    rw [hb (10 + k) (by omega) (by omega)]
    simp only [PathVals.base]
    have : ¬ (10 + k = 2 ∨ 10 + k = 3 ∨ 10 + k = 4 ∨ 10 + k = 5 ∨ 10 + k = 6 ∨ 10 + k = 7 ∨
      10 + k = 8 ∨ 10 + k = 9) := by omega
    simp only [not_or] at this
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := this
    simp [a1, a2, a3, a4, a5, a6, a7, a8]
  have hiff : i = (⟨n - 1, Nat.sub_lt hn (by omega)⟩ : Fin n) ↔ (i : ℕ) + 1 = n := by
    constructor
    · intro h; rw [h]; simp; omega
    · intro h; apply Fin.ext; simp; omega
  intro g hg
  simp only [Path.baseGates, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hg
  rcases hg with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    ⟨k, hk, rfl⟩
  · simp only [CoeffExpr.eval, cv, Path.side, t2]; exact hf.side_bool
  · simp only [CoeffExpr.eval, cv, Path.first, t3]; exact hf.first_bool
  · simp only [CoeffExpr.eval, cv, Path.last, t4]; exact hf.last_bool
  · -- isF * (first - 1)
    simp only [CoeffExpr.eval, cv, Path.isF, Path.first, t3, m0]
    by_cases h0 : (i : ℕ) = 0
    · simp [h0, hf.first0 h0]
    · simp [h0]
  · -- isL * (last - 1)
    simp only [CoeffExpr.eval, cv, Path.isL, Path.last, t4, m1]
    by_cases hl : (i : ℕ) + 1 = n
    · rw [if_pos (hiff.mpr hl), hf.lastL hl]; simp
    · rw [if_neg (fun h => hl (hiff.mp h))]; simp
  · -- (1 - isL) * (first' - last)
    simp only [CoeffExpr.eval, cv, nv, notE, Path.isL, Path.first, Path.last, t4, m1]
    by_cases hl : (i : ℕ) + 1 = n
    · simp [hiff.mpr hl]
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      rw [hbn hi 3 (by norm_num) (by norm_num)]
      simp only [PathVals.base]
      simp [fun h => hl (hiff.mp h), hf.firstNext hi]
  · simp only [CoeffExpr.eval, cv, Path.first, Path.len, t3, t5]; exact hf.len_first
  · -- (1 - last) * (len' - len - 1)
    simp only [CoeffExpr.eval, cv, nv, notE, Path.last, Path.len, t4, t5]
    by_cases hl : (i : ℕ) + 1 = n
    · rw [hf.lastL hl]; simp
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      rw [hbn hi 5 (by norm_num) (by norm_num)]
      simp only [PathVals.base]
      simpa using hf.len_step hi
  · simp only [CoeffExpr.eval, cv, Path.first, Path.acc, Path.side, t3, t6, t2]; exact hf.acc_first
  · -- (1 - last) * (acc' - 2 acc - side')
    simp only [CoeffExpr.eval, cv, nv, notE, Path.last, Path.acc, Path.side, t4, t6]
    by_cases hl : (i : ℕ) + 1 = n
    · rw [hf.lastL hl]; simp
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      rw [hbn hi 6 (by norm_num) (by norm_num), hbn hi 2 (by norm_num) (by norm_num)]
      simp only [PathVals.base]
      simpa using hf.acc_step hi
  · simp only [CoeffExpr.eval, cv, Path.first, Path.rootIdx, Path.cellIdx, t3, t9, t8]; exact hf.root_first
  · simp only [CoeffExpr.eval, cv, nv, notE, Path.last, Path.rootIdx, t4, t9]
    by_cases hl : (i : ℕ) + 1 = n
    · rw [hf.lastL hl]; simp
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      rw [hbn hi 9 (by norm_num) (by norm_num)]
      simp only [PathVals.base]
      simpa using hf.root_step hi
  · -- cert
    simp only [CoeffExpr.eval, cv, Path.last, Path.len, Path.bit0, eval_bitSum, t4, t5]
    have : ∀ k ∈ Finset.range 6, (2 : F) ^ k * E.trace (10 + k) = (2 : F) ^ k * (vals i).bit k :=
      fun k hk => by rw [tbit k (Finset.mem_range.mp hk)]
    rw [Finset.sum_congr rfl this]
    exact hf.cert
  · simp only [CoeffExpr.eval, cv, notE, Path.last, Path.m, t4, t7]; exact hf.m_mask
  · simp only [CoeffExpr.eval, cv, Path.bit0]
    rw [tbit k hk]
    exact hf.bit_bool k hk

end BaseGates

section Mixed
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (ω : F) (chals pubs : ℕ → K)
  (vals : Fin n → PathVals F (Quad (algebraMap F K δF)))

/-- The edge's child `l + side·(r − l)` as a `𝕂′` fingerprint. -/
def childOf (c : PathVals F (Quad (algebraMap F K δF))) : ComputeTable.FP (Quad (algebraMap F K δF)) :=
  ⟨c.l.size + liftQ δF c.side * (c.r.size - c.l.size), c.l.dyck + liftQ δF c.side * (c.r.dyck - c.l.dyck),
    c.l.leaf + liftQ δF c.side * (c.r.leaf - c.l.leaf)⟩

/-- The consumed export record `(p, l, r, cellIdx, side)` of a path row. -/
def pxKeyOf (c : PathVals F (Quad (algebraMap F K δF))) : Fin 11 → Quad (algebraMap F K δF) :=
  ![c.p.size, c.p.dyck, c.p.leaf, c.l.size, c.l.dyck, c.l.leaf, c.r.size, c.r.dyck, c.r.leaf,
    liftQ δF c.cellIdx, liftQ δF c.side]

/-- The provided path record `(root, child, acc, rootIdx)`. -/
def pRecOf (c : PathVals F (Quad (algebraMap F K δF))) : Fin 8 → Quad (algebraMap F K δF) :=
  ![c.root.size, c.root.dyck, c.root.leaf, (childOf δF c).size, (childOf δF c).dyck,
    (childOf δF c).leaf, liftQ δF c.acc, liftQ δF c.rootIdx]

/-- **The semantic content of the `17` path `𝕂′` equations at row `i`.** -/
structure PathMixedFacts (γ ρ : Quad (algebraMap F K δF))
    (vals : Fin n → PathVals F (Quad (algebraMap F K δF))) (i : Fin n) : Prop where
  root_first : (vals i).first = 1 → (vals i).root = (vals i).p
  root_step : ∀ hi : (i : ℕ) + 1 < n, (vals i).last = 0 → (vals ⟨(i : ℕ) + 1, hi⟩).root = (vals i).root
  p_step : ∀ hi : (i : ℕ) + 1 < n, (vals i).last = 0 → (vals ⟨(i : ℕ) + 1, hi⟩).p = childOf δF (vals i)
  xCons_den : (vals i).xConsInv * FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (pxKeyOf δF (vals i)) = 1
  pProv_den : (vals i).last = 1 →
    (vals i).pProvInv * FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (pRecOf δF (vals i)) = 1
  xAcc_init : (i : ℕ) = 0 → (vals i).xAcc = (vals i).xConsInv
  xAcc_step : ∀ hi : (i : ℕ) + 1 < n,
    (vals ⟨(i : ℕ) + 1, hi⟩).xAcc = (vals i).xAcc + (vals ⟨(i : ℕ) + 1, hi⟩).xConsInv
  xAcc_term : (i : ℕ) + 1 = n → (vals i).xAcc = Quad.mk _ (pubs 0) (pubs 1)
  pAcc_init : (i : ℕ) = 0 → (vals i).pAcc = liftQ δF (vals i).m * (vals i).pProvInv
  pAcc_step : ∀ hi : (i : ℕ) + 1 < n,
    (vals ⟨(i : ℕ) + 1, hi⟩).pAcc =
      (vals i).pAcc + liftQ δF (vals ⟨(i : ℕ) + 1, hi⟩).m * (vals ⟨(i : ℕ) + 1, hi⟩).pProvInv
  pAcc_term : (i : ℕ) + 1 = n → (vals i).pAcc = Quad.mk _ (pubs 2) (pubs 3)

theorem path_roles (hinj : Function.Injective nodes) (i : Fin n) :
    let eK := pathEKh δF b hn nodes ω chals pubs vals i
    let eF := pathEFh δF b hn nodes ω chals pubs vals i
    (QE.var 0 : QE F).ev δF eK eF = (vals i).root.size ∧ (QE.var 2 : QE F).ev δF eK eF = (vals i).root.dyck ∧
    (QE.var 4 : QE F).ev δF eK eF = (vals i).root.leaf ∧ (QE.var 6 : QE F).ev δF eK eF = (vals i).p.size ∧
    (QE.var 8 : QE F).ev δF eK eF = (vals i).p.dyck ∧ (QE.var 10 : QE F).ev δF eK eF = (vals i).p.leaf ∧
    (QE.var 12 : QE F).ev δF eK eF = (vals i).l.size ∧ (QE.var 14 : QE F).ev δF eK eF = (vals i).l.dyck ∧
    (QE.var 16 : QE F).ev δF eK eF = (vals i).l.leaf ∧ (QE.var 18 : QE F).ev δF eK eF = (vals i).r.size ∧
    (QE.var 20 : QE F).ev δF eK eF = (vals i).r.dyck ∧ (QE.var 22 : QE F).ev δF eK eF = (vals i).r.leaf ∧
    (QE.var 24 : QE F).ev δF eK eF = (vals i).xConsInv ∧ (QE.var 26 : QE F).ev δF eK eF = (vals i).pProvInv ∧
    (QE.var 28 : QE F).ev δF eK eF = (vals i).xAcc ∧ (QE.var 30 : QE F).ev δF eK eF = (vals i).pAcc := by
  intro eK eF
  have h := fun (s : ℕ) (hs : s < 16) => pathEKh_ev_var δF b hn nodes ω chals pubs vals hinj i hs
  exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num),
    h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num), h 8 (by norm_num), h 9 (by norm_num),
    h 10 (by norm_num), h 11 (by norm_num), h 12 (by norm_num), h 13 (by norm_num), h 14 (by norm_num),
    h 15 (by norm_num)⟩

theorem path_roles_next (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    let eK := pathEKh δF b hn nodes ω chals pubs vals i
    let eF := pathEFh δF b hn nodes ω chals pubs vals i
    let v' := vals ⟨(i : ℕ) + 1, hi⟩
    (QE.next 0 : QE F).ev δF eK eF = v'.root.size ∧ (QE.next 2 : QE F).ev δF eK eF = v'.root.dyck ∧
    (QE.next 4 : QE F).ev δF eK eF = v'.root.leaf ∧ (QE.next 6 : QE F).ev δF eK eF = v'.p.size ∧
    (QE.next 8 : QE F).ev δF eK eF = v'.p.dyck ∧ (QE.next 10 : QE F).ev δF eK eF = v'.p.leaf ∧
    (QE.next 24 : QE F).ev δF eK eF = v'.xConsInv ∧ (QE.next 26 : QE F).ev δF eK eF = v'.pProvInv ∧
    (QE.next 28 : QE F).ev δF eK eF = v'.xAcc ∧ (QE.next 30 : QE F).ev δF eK eF = v'.pAcc := by
  intro eK eF v'
  have h := fun (s : ℕ) (hs : s < 16) =>
    pathEKh_ev_next δF b hn nodes ω chals pubs vals hinj hadj i hi hs
  exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num),
    h 5 (by norm_num), h 12 (by norm_num), h 13 (by norm_num), h 14 (by norm_num), h 15 (by norm_num)⟩

theorem path_cols (hinj : Function.Injective nodes) (i : Fin n) :
    let eF := pathEFh δF b hn nodes ω chals pubs vals i
    eF.trace 2 = (vals i).side ∧ eF.trace 3 = (vals i).first ∧ eF.trace 4 = (vals i).last ∧
    eF.trace 5 = (vals i).len ∧ eF.trace 6 = (vals i).acc ∧ eF.trace 7 = (vals i).m ∧
    eF.trace 8 = (vals i).cellIdx ∧ eF.trace 9 = (vals i).rootIdx := by
  intro eF
  have h := fun (j : ℕ) (h2 : 2 ≤ j) (hj : j < 16) =>
    pathEFh_base δF b hn nodes ω chals pubs vals hinj i h2 hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [h _ (by norm_num) (by norm_num)]; simp [PathVals.base])

theorem path_cols_next (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    let eF := pathEFh δF b hn nodes ω chals pubs vals i
    eF.traceNext 7 = (vals ⟨(i : ℕ) + 1, hi⟩).m := by
  intro eF
  rw [pathEFh_next_base δF b hn nodes ω chals pubs vals hinj hadj i hi (by norm_num) (by norm_num)]
  simp [PathVals.base]

theorem path_keyVec_x (hinj : Function.Injective nodes) (i : Fin n) :
    keyVec δF 11 Path.xKey (pathEKh δF b hn nodes ω chals pubs vals i)
      (pathEFh δF b hn nodes ω chals pubs vals i) = pxKeyOf δF (vals i) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, -⟩ :=
    path_roles δF b hn nodes ω chals pubs vals hinj i
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9⟩ := path_cols δF b hn nodes ω chals pubs vals hinj i
  funext c
  fin_cases c <;>
    simp [keyVec, Path.xKey, QFP.entries, QFP.var, Path.pR, Path.lR, Path.rR, pxKeyOf,
      p3, p4, p5, p6, p7, p8, p9, p10, p11, ev_base, CoeffExpr.eval, cv, Path.cellIdx, Path.side, c8, c2]

theorem path_keyVec_p (hinj : Function.Injective nodes) (i : Fin n) :
    keyVec δF 8 Path.pRec (pathEKh δF b hn nodes ω chals pubs vals i)
      (pathEFh δF b hn nodes ω chals pubs vals i) = pRecOf δF (vals i) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, -⟩ :=
    path_roles δF b hn nodes ω chals pubs vals hinj i
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9⟩ := path_cols δF b hn nodes ω chals pubs vals hinj i
  funext c
  fin_cases c <;>
    simp [keyVec, Path.pRec, Path.child, QFP.entries, QFP.var, QFP.add, QFP.scale, QFP.sub,
      Path.rootR, Path.lR, Path.rR, pRecOf, childOf,
      p0, p1, p2, p6, p7, p8, p9, p10, p11, ev_add, ev_sub, ev_scale, ev_base, CoeffExpr.eval, cv,
      Path.acc, Path.rootIdx, Path.side, c6, c9, c2]

theorem lift_mul_bool (w : F) (hw : w * (w - 1) = 0) (P : Quad (algebraMap F K δF))
    (h : w = 1 → P = 0) : liftQ δF w * P = 0 := by
  rcases mul_eq_zero.mp hw with h' | h'
  · simp [h']
  · have hw1 : w = 1 := by linear_combination h'
    rw [h hw1]; simp

variable [DecidableEq F] in
/-- **The `17` path `𝕂′` equations hold at the honest environment of row `i`.** -/
theorem path_qEqs_hold (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hb : PathBaseFacts vals i) (γ ρ : Quad (algebraMap F K δF))
    (hok : ChalsOK δF chals γ ρ 11)
    (hf : PathMixedFacts δF pubs γ ρ vals i) :
    ∀ e ∈ Path.qEqs δF, e.ev δF (pathEKh δF b hn nodes ω chals pubs vals i)
      (pathEFh δF b hn nodes ω chals pubs vals i) = 0 := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15⟩ :=
    path_roles δF b hn nodes ω chals pubs vals hinj i
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9⟩ := path_cols δF b hn nodes ω chals pubs vals hinj i
  set eK := pathEKh δF b hn nodes ω chals pubs vals i with heK
  set eF := pathEFh δF b hn nodes ω chals pubs vals i with heF
  have m0 : eF.trace 0 = if (i : ℕ) = 0 then 1 else 0 :=
    pathEFh_mask0 δF b hn nodes ω chals pubs vals hinj i
  have m1 : eF.trace 1 = if i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0 :=
    pathEFh_mask1 δF b hn nodes ω chals pubs vals hinj i
  have hch : ChalsOK δF eK.chal γ ρ 11 := by rw [heK, pathEKh_chal]; exact hok
  have dX : (den δF Path.xKey).ev δF eK eF = FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (pxKeyOf δF (vals i)) := by
    rw [den_ev_compress' δF Path.xKey (m := 11) rfl _ _ γ ρ hch,
      path_keyVec_x δF b hn nodes ω chals pubs vals hinj i]
  have dP : (den δF Path.pRec).ev δF eK eF = FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (pRecOf δF (vals i)) := by
    rw [den_ev_compress' δF Path.pRec (m := 8) rfl _ _ γ ρ (chalsOK_mono δF (by norm_num) hch),
      path_keyVec_p δF b hn nodes ω chals pubs vals hinj i]
  have hFirst : (i : ℕ) = 0 → eF.trace 0 = 1 := fun h => by rw [m0, if_pos h]
  have hNFirst : (i : ℕ) ≠ 0 → eF.trace 0 = 0 := fun h => by rw [m0, if_neg h]
  have hiff : i = (⟨n - 1, Nat.sub_lt hn (by omega)⟩ : Fin n) ↔ (i : ℕ) + 1 = n := by
    constructor
    · intro h; rw [h]; simp; omega
    · intro h; apply Fin.ext; simp; omega
  have hLast : (i : ℕ) + 1 = n → eF.trace 1 = 1 := fun h => by rw [m1, if_pos (hiff.mpr h)]
  have hNLast : (i : ℕ) + 1 ≠ n → eF.trace 1 = 0 := fun h => by
    rw [m1, if_neg (fun h' => h (hiff.mp h'))]
  have hnotE : ∀ j, (notE (cv j) : CoeffExpr F).eval eF = 1 - eF.trace j := fun j => rfl
  have hpub0 : (QE.pub 0 : QE F).ev δF eK eF = Quad.mk _ (pubs 0) (pubs 1) := by
    rw [ev_pub, pathEKh_pub, pathEKh_pub]
  have hpub2 : (QE.pub 2 : QE F).ev δF eK eF = Quad.mk _ (pubs 2) (pubs 3) := by
    rw [ev_pub, pathEKh_pub, pathEKh_pub]
  intro e he
  simp only [Path.qEqs, QFP.entries, QFP.scale, QFP.sub, QFP.var, QFP.next, Path.rootR, Path.pR,
    Path.lR, Path.rR, Path.child, QFP.add, Nat.reduceAdd, zero_add, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · simp only [ev_scale, ev_sub, CoeffExpr.eval, cv, Path.first, c3, p0, p3]
    exact lift_mul_bool δF _ hb.first_bool _ (fun h => by rw [hf.root_first h]; simp)
  · simp only [ev_scale, ev_sub, CoeffExpr.eval, cv, Path.first, c3, p1, p4]
    exact lift_mul_bool δF _ hb.first_bool _ (fun h => by rw [hf.root_first h]; simp)
  · simp only [ev_scale, ev_sub, CoeffExpr.eval, cv, Path.first, c3, p2, p5]
    exact lift_mul_bool δF _ hb.first_bool _ (fun h => by rw [hf.root_first h]; simp)
  · -- root step size
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, hnotE, Path.last, c4, hb.lastL hl]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      obtain ⟨q0, q2, q4, -⟩ := path_roles_next δF b hn nodes ω chals pubs vals hinj hadj i hi
      rw [← heK, ← heF] at q0 q2 q4
      simp only [ev_scale, ev_sub, hnotE, Path.last, c4, q0, p0]
      exact lift_notE_mul δF _ hb.last_bool _ (fun h0 => by rw [hf.root_step hi h0]; simp)
  · -- root step dyck
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, hnotE, Path.last, c4, hb.lastL hl]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      obtain ⟨q0, q2, q4, -⟩ := path_roles_next δF b hn nodes ω chals pubs vals hinj hadj i hi
      rw [← heK, ← heF] at q0 q2 q4
      simp only [ev_scale, ev_sub, hnotE, Path.last, c4, q2, p1]
      exact lift_notE_mul δF _ hb.last_bool _ (fun h0 => by rw [hf.root_step hi h0]; simp)
  · -- root step leaf
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, hnotE, Path.last, c4, hb.lastL hl]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      obtain ⟨q0, q2, q4, -⟩ := path_roles_next δF b hn nodes ω chals pubs vals hinj hadj i hi
      rw [← heK, ← heF] at q0 q2 q4
      simp only [ev_scale, ev_sub, hnotE, Path.last, c4, q4, p2]
      exact lift_notE_mul δF _ hb.last_bool _ (fun h0 => by rw [hf.root_step hi h0]; simp)
  · -- p step size
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, hnotE, Path.last, c4, hb.lastL hl]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      obtain ⟨-, -, -, q6, q8, q10, -⟩ := path_roles_next δF b hn nodes ω chals pubs vals hinj hadj i hi
      rw [← heK, ← heF] at q6 q8 q10
      simp only [ev_scale, ev_sub, ev_add, hnotE, Path.last, Path.side, CoeffExpr.eval, cv, c4, c2, q6,
        p6, p9]
      exact lift_notE_mul δF _ hb.last_bool _ (fun h0 => by rw [hf.p_step hi h0]; simp [childOf])
  · -- p step dyck
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, hnotE, Path.last, c4, hb.lastL hl]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      obtain ⟨-, -, -, q6, q8, q10, -⟩ := path_roles_next δF b hn nodes ω chals pubs vals hinj hadj i hi
      rw [← heK, ← heF] at q6 q8 q10
      simp only [ev_scale, ev_sub, ev_add, hnotE, Path.last, Path.side, CoeffExpr.eval, cv, c4, c2, q8,
        p7, p10]
      exact lift_notE_mul δF _ hb.last_bool _ (fun h0 => by rw [hf.p_step hi h0]; simp [childOf])
  · -- p step leaf
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, hnotE, Path.last, c4, hb.lastL hl]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      obtain ⟨-, -, -, q6, q8, q10, -⟩ := path_roles_next δF b hn nodes ω chals pubs vals hinj hadj i hi
      rw [← heK, ← heF] at q6 q8 q10
      simp only [ev_scale, ev_sub, ev_add, hnotE, Path.last, Path.side, CoeffExpr.eval, cv, c4, c2, q10,
        p8, p11]
      exact lift_notE_mul δF _ hb.last_bool _ (fun h0 => by rw [hf.p_step hi h0]; simp [childOf])
  · -- xCons inverse
    simp only [ev_sub, ev_mul, ev_one, Path.xConsInv, p12, dX]
    exact sub_eq_zero.mpr hf.xCons_den
  · -- pProv inverse
    simp only [ev_scale, ev_sub, ev_mul, ev_one, CoeffExpr.eval, cv, Path.last, c4, Path.pProvInv, p13, dP]
    exact lift_mul_bool δF _ hb.last_bool _ (fun h => sub_eq_zero.mpr (hf.pProv_den h))
  · -- xAcc init
    simp only [ev_scale, ev_sub, CoeffExpr.eval, cv, Path.isF, Path.xAcc, Path.xConsInv, p14, p12]
    by_cases h0 : (i : ℕ) = 0
    · rw [hFirst h0]; simp [liftQ, hf.xAcc_init h0]
    · rw [hNFirst h0]; simp [liftQ]
  · -- xAcc step
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, hnotE, Path.isL, hLast hl]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      obtain ⟨-, -, -, -, -, -, q24, -, q28, -⟩ := path_roles_next δF b hn nodes ω chals pubs vals hinj hadj i hi
      rw [← heK, ← heF] at q24 q28
      simp only [ev_scale, ev_sub, hnotE, Path.isL, hNLast hl, Path.xAcc, Path.xConsInv, q24, q28, p14]
      have := hf.xAcc_step hi
      simp only [liftQ, sub_zero, map_one, one_mul]
      linear_combination this
  · -- xAcc terminal
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, ev_sub, hpub0, CoeffExpr.eval, cv, Path.isL, hLast hl, Path.xAcc, p14]
      simp [liftQ, hf.xAcc_term hl]
    · simp only [ev_scale, CoeffExpr.eval, cv, Path.isL, hNLast hl]; simp [liftQ]
  · -- pAcc init
    simp only [ev_scale, ev_sub, CoeffExpr.eval, cv, Path.isF, Path.pAcc, Path.pProvInv, Path.m, c7, p15, p13]
    by_cases h0 : (i : ℕ) = 0
    · rw [hFirst h0]; simp [liftQ, hf.pAcc_init h0]
    · rw [hNFirst h0]; simp [liftQ]
  · -- pAcc step
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, hnotE, Path.isL, hLast hl]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by have := i.isLt; omega
      obtain ⟨-, -, -, -, -, -, -, q26, -, q30⟩ := path_roles_next δF b hn nodes ω chals pubs vals hinj hadj i hi
      rw [← heK, ← heF] at q26 q30
      have d7 := path_cols_next δF b hn nodes ω chals pubs vals hinj hadj i hi
      rw [← heF] at d7
      simp only [ev_scale, ev_sub, hnotE, Path.isL, hNLast hl, Path.pAcc, Path.pProvInv, Path.m, nv,
        CoeffExpr.eval, d7, q26, q30, p15]
      have := hf.pAcc_step hi
      simp only [liftQ, sub_zero, map_one, one_mul]
      linear_combination this
  · -- pAcc terminal
    by_cases hl : (i : ℕ) + 1 = n
    · simp only [ev_scale, ev_sub, hpub2, CoeffExpr.eval, cv, Path.isL, hLast hl, Path.pAcc, p15]
      simp [liftQ, hf.pAcc_term hl]
    · simp only [ev_scale, CoeffExpr.eval, cv, Path.isL, hNLast hl]; simp [liftQ]

variable [DecidableEq F] in
/-- **The `34` mixed gates of the path chip vanish at the honest environment of row `i`.** -/
theorem path_mixed_gates_hold (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * ω)
    (i : Fin n) (hb : PathBaseFacts vals i) (γ ρ : Quad (algebraMap F K δF))
    (hok : ChalsOK δF chals γ ρ 11) (hf : PathMixedFacts δF pubs γ ρ vals i) :
    ∀ g ∈ Path.mixedGates δF,
      g.eval (pathEKh δF b hn nodes ω chals pubs vals i) (pathEFh δF b hn nodes ω chals pubs vals i) = 0 := by
  intro g hg
  obtain ⟨e, he, hge⟩ := List.mem_flatMap.mp hg
  have h := path_qEqs_hold δF b hn nodes ω chals pubs vals hinj hadj i hb γ ρ hok hf e he
  simp only [QE.ev, Quad.mk_eq_zero_iff] at h
  simp only [QE.gates, List.mem_cons, List.not_mem_nil, or_false] at hge
  rcases hge with rfl | rfl
  · exact h.1
  · exact h.2

end Mixed

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
