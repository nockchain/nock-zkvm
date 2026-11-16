/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalPAx.lean

* `segReads_eq`: `segReads n m s` as an indexed list (`curG` = the noun before segment `m - j`).
  * `chainP_sum`: one honest chain `chainOf H _ _ n _ X` (`n ≥ 2^32`) pays, row by row with activity `1 − z1a`,
    exactly `Σ Tw` over `(segReads n (top n) X).filter (2 ≤ ·.2)` (the head row with top limb `1` is the only
    skipped row, and it is the only segment read of axis `< 2`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AChipsOK
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AChainsRun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalPAx

noncomputable section

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun
open Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData
open Nock.J9A.NounAx (top segRd segRd_pos top_eq_length)

/-! ## 1. The segment reads as an indexed list -/

/-- The noun before row `j` of a chain from segment `m` down (`curG 0 = s`). -/
def curG (n m : ℕ) (s : Noun) : ℕ → Noun
  | 0 => s
  | j + 1 => segX n (m - j) (curG n m s j)

theorem curG_shift (n m : ℕ) (s : Noun) : ∀ j, curG n (m + 1) s (j + 1) = curG n m (segX n (m + 1) s) j
  | 0 => by simp [curG]
  | j + 1 => by
    rw [curG, curG_shift n m s j, curG]
    congr 1
    omega

theorem segReads_eq (n : ℕ) : ∀ (m : ℕ) (s : Noun),
    ComplJ9AData.segReads n m s = (List.range (m + 1)).map fun j => (curG n m s j, segRd n (m - j))
  | 0, s => by simp [ComplJ9AData.segReads, curG]
  | m + 1, s => by
    rw [ComplJ9AData.segReads, segReads_eq n m]
    conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine congrArg₂ _ rfl (List.map_congr_left fun j _ => ?_)
    simp only [Function.comp_apply, curG_shift]
    congr 2
    omega

theorem segN_curG (n : ℕ) (X : Noun) : ∀ j, segN n X j = curG n (top n) X (j + 1)
  | 0 => rfl
  | j + 1 => by
    show segX n (top n - (j + 1)) (segN n X j) = segX n (top n - (j + 1)) (curG n (top n) X (j + 1))
    rw [segN_curG n X j]

theorem curN_curG (n : ℕ) (X : Noun) : ∀ j, curN n X j = curG n (top n) X j
  | 0 => rfl
  | j + 1 => segN_curG n X j

theorem sum_filter_map {α M : Type} [AddCommMonoid M] (P : α → Prop) [DecidablePred P] (g : α → M) :
    ∀ l : List α, ((l.filter P).map g).sum = (l.map fun x => if P x then g x else 0).sum
  | [] => rfl
  | x :: l => by
    by_cases h : P x <;> simp [List.filter_cons, h, sum_filter_map P g l]

/-! ## 2. One chain -/

theorem top_limb (n : ℕ) (hn : n ≠ 0) :
    (Nock.Atoms.limbs n).getD ((Nock.Atoms.limbs n).length - 1 - 0) 0 = segRd n (top n - 0) := by
  rw [limbs_getD, top_eq_length n hn]
  simp [segRd]

theorem mid_limb (n j : ℕ) (hn : n ≠ 0) (hj0 : j ≠ 0) (hj : j < top n + 1) :
    2 ^ 32 + (Nock.Atoms.limbs n).getD ((Nock.Atoms.limbs n).length - 1 - j) 0 = segRd n (top n - j) := by
  rw [limbs_getD, top_eq_length n hn, Nat.add_sub_cancel]
  simp only [segRd]
  rw [if_neg (by omega), Nat.add_comm]

section Rows
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ) (route0 : Bool) (R n mu : ℕ) (X : Noun)

theorem row_hinv (j : ℕ) :
    ((chainOf (F := F) H route0 R n mu X).row j).hinv = (((H (curG n (top n) X j)).2 : ℕ) : F) := by
  rcases j with _ | k
  · rfl
  · show (((H (segN n X k)).2 : ℕ) : F) = _
    rw [segN_curG]

theorem row_hout (j : ℕ) :
    ((chainOf (F := F) H route0 R n mu X).row j).houtk =
        (((H (segX n (top n - j) (curG n (top n) X j))).1 : ℕ) : F) ∧
      ((chainOf (F := F) H route0 R n mu X).row j).houtv =
        (((H (segX n (top n - j) (curG n (top n) X j))).2 : ℕ) : F) := by
  have e : segN n X j = segX n (top n - j) (curG n (top n) X j) := by rw [segN_curG]; rfl
  exact ⟨by show (((H (segN n X j)).1 : ℕ) : F) = _; rw [e],
    by show (((H (segN n X j)).2 : ℕ) : F) = _; rw [e]⟩

theorem row_ax (hn : 2 ^ 32 ≤ n) (j : ℕ) (hj : j < top n + 1) :
    ((chainOf (F := F) H route0 R n mu X).row j).axS = ((segRd n (top n - j) : ℕ) : F) ∧
      ((chainOf (F := F) H route0 R n mu X).row j).z1a = if segRd n (top n - j) = 1 then 1 else 0 := by
  have hn0 : n ≠ 0 := by omega
  rcases j with _ | k
  · have htl := top_limb n hn0
    simp only [ComplJ9AAxisRows.ChainSpec.row, ComplJ9AAxisRows.chainRow, chainOf]
    simp only [htl]
    simp
  · have hml := mid_limb n (k + 1) hn0 (by omega) hj
    have h2 : segRd n (top n - (k + 1)) ≠ 1 := by omega
    simp only [ComplJ9AAxisRows.ChainSpec.row, ComplJ9AAxisRows.chainRow, chainOf]
    rw [← hml]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, beq_iff_eq, Bool.false_and, Bool.false_eq_true,
      if_false, decide_false]
    push_cast
    refine ⟨by norm_num, ?_⟩
    simp only [Bool.false_and, Bool.false_eq_true, if_false]
    rw [if_neg (by omega)]

end Rows

section Chain
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The path weight of a read at handle map `H`**: `1 / (ρH + recDenP((H root).2, axis, H(/[axis] root)))`. -/
def Tw (H : Noun → ℕ × ℕ) (χ : Coins frameJ8 K) (x : Noun × ℕ) : 𝕂′ :=
  (ρH δ χ + recDenP 0 (γH δ χ) ((((H x.1).2 : ℕ) : ZMod p), ((x.2 : ℕ) : ZMod p),
    ((((H ((Noun.slot x.2 x.1).getD (.atom 0))).1 : ℕ) : ZMod p),
      (((H ((Noun.slot x.2 x.1).getD (.atom 0))).2 : ℕ) : ZMod p))))⁻¹

/-- The path term of one axis row (activity `1 − z1a`, key `(hinv, axS, houtk, houtv)`). -/
def rowP (χ : Coins frameJ8 K) (a : ComplJ9AAxisRows.ARow (ZMod p)) : 𝕂′ :=
  liftQ δ (1 - a.z1a) * (ρH δ χ + recDenP 0 (γH δ χ) (a.hinv, a.axS, (a.houtk, a.houtv)))⁻¹

theorem rowP_chain (H : Noun → ℕ × ℕ) (route0 : Bool) (R n mu : ℕ) (X : Noun) (hn : 2 ^ 32 ≤ n)
    (χ : Coins frameJ8 K) (j : ℕ) (hj : j < top n + 1) :
    rowP δ χ ((chainOf (F := ZMod p) H route0 R n mu X).row j) =
      if 2 ≤ segRd n (top n - j) then Tw δ H χ (curG n (top n) X j, segRd n (top n - j)) else 0 := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨hax, hz⟩ := row_ax (F := ZMod p) H route0 R n mu X hn j hj
  obtain ⟨hk, hv⟩ := row_hout (F := ZMod p) H route0 R n mu X j
  have hpos := segRd_pos hn0 (top n - j) (by omega)
  unfold rowP
  rw [hz, hax, row_hinv, hk, hv]
  by_cases h1 : segRd n (top n - j) = 1
  · have h2 : ¬ (2 ≤ segRd n (top n - j)) := by omega
    simp [h1, h2]
  · have h2 : 2 ≤ segRd n (top n - j) := by omega
    simp [h1, h2, Tw, ComplJ9AGen.segX, liftQ, map_one, one_mul]

/-- **One honest chain's path total** is the walk-weight sum over its segment reads of axis `≥ 2`. -/
theorem chainP_sum (H : Noun → ℕ × ℕ) (route0 : Bool) (R n mu : ℕ) (X : Noun) (hn : 2 ^ 32 ≤ n)
    (χ : Coins frameJ8 K) :
    ((chainOf (F := ZMod p) H route0 R n mu X).rows.map (rowP δ χ)).sum =
      (((ComplJ9AData.segReads n (top n) X).filter fun q => 2 ≤ q.2).map (Tw δ H χ)).sum := by
  have hn0 : n ≠ 0 := by omega
  have hL := top_eq_length n hn0
  rw [sum_filter_map, segReads_eq, List.map_map, ComplJ9AAxisRows.ChainSpec.rows, List.map_map]
  have hls : (chainOf (F := ZMod p) H route0 R n mu X).ls.length = top n + 1 := hL
  rw [hls]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  exact rowP_chain δ H route0 R n mu X hn χ j (List.mem_range.mp hj)

end Chain

/-! ## 3. The table -/

section Table
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The path key denominator of an axis row** is `ρH + recDenP(hinv, axS, (houtk, houtv))` of the row. -/
theorem dKey_path {n : ℕ} (hn0 : 0 < n) (rows : List (ComplJ9AAxisRows.ARow (ZMod p)))
    (hn : n = rows.length) (χ : Coins frameJ8 K) (i : Fin n) :
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.dKey δ (chalsMJ8 δ χ) hn0
        (ComplJ9AAxisRows.tableCol rows hn0 hn) Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pathKey i =
      ρH δ χ + recDenP 0 (γH δ χ) ((rows[i.1]'(hn ▸ i.2)).hinv, (rows[i.1]'(hn ▸ i.2)).axS,
        ((rows[i.1]'(hn ▸ i.2)).houtk, (rows[i.1]'(hn ▸ i.2)).houtv)) := by
  have h10 : fullCol hn0 (ComplJ9AAxisRows.tableCol rows hn0 hn) 10 i = (rows[i.1]'(hn ▸ i.2)).axS := by
    rw [ComplJ9AAxisRows.fullCol_row]; rfl
  have h13 : fullCol hn0 (ComplJ9AAxisRows.tableCol rows hn0 hn) 13 i = (rows[i.1]'(hn ▸ i.2)).hinv := by
    rw [ComplJ9AAxisRows.fullCol_row]; rfl
  have h14 : fullCol hn0 (ComplJ9AAxisRows.tableCol rows hn0 hn) 14 i = (rows[i.1]'(hn ▸ i.2)).houtk := by
    rw [ComplJ9AAxisRows.fullCol_row]; rfl
  have h15 : fullCol hn0 (ComplJ9AAxisRows.tableCol rows hn0 hn) 15 i = (rows[i.1]'(hn ▸ i.2)).houtv := by
    rw [ComplJ9AAxisRows.fullCol_row]; rfl
  unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.dKey
  rw [ComplJ9AChipsOK.kappa_eq]
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_eight, BalanceQ.liftRec,
    Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.keyVecL, Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pathKey,
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.envC, recDenP,
    Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.hinv, Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.axS,
    Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.houtk, Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.houtv]
  simp [cv, CoeffExpr.eval, h10, h13, h14, h15, ComplJ9AAxisRows.ARow.col, IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]

/-- **`axSumP` is the row sum of `rowP`** over the table rows. -/
theorem axSumP_rows {n : ℕ} (hn0 : 0 < n) (cs : List (ComplJ9AAxisRows.ChainSpec (ZMod p)))
    (hn : n = (ComplJ9AAxisRows.tableRows cs).length) (χ : Coins frameJ8 K) :
    ComplJ9AChipsOK.axSumP δ hn0 cs hn χ = ((ComplJ9AAxisRows.tableRows cs).map (rowP δ χ)).sum := by
  unfold ComplJ9AChipsOK.axSumP
  simp_rw [dKey_path δ hn0 _ hn χ]
  subst hn
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

theorem tableRows_sum {M : Type} [AddCommMonoid M] (f : ComplJ9AAxisRows.ARow (ZMod p) → M) :
    ∀ cs : List (ComplJ9AAxisRows.ChainSpec (ZMod p)),
      ((ComplJ9AAxisRows.tableRows cs).map f).sum = (cs.map fun c => (c.rows.map f).sum).sum
  | [] => rfl
  | c :: cs => by
    simp only [ComplJ9AAxisRows.tableRows, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      tableRows_sum f cs]

theorem keys_sum (nA : ℕ) (H : Noun → ℕ × ℕ) (rows : Array LX9) (χ : Coins frameJ8 K) :
    ∀ L : List (Noun × ℕ), (∀ k ∈ L, 2 ^ 32 ≤ k.2) →
      (L.map fun k => ((chainOf (F := ZMod p) H (decide (k.2 < p))
          (idOf9 p nA H (fieldAx9 p rows) k.2) k.2 (muOf9 rows k) k.1).rows.map (rowP δ χ)).sum).sum =
        (((L.flatMap fun k => ComplJ9AData.segReads k.2 (top k.2) k.1).filter fun q => 2 ≤ q.2).map
          (Tw δ H χ)).sum
  | [], _ => rfl
  | k :: L, hL => by
    rw [List.map_cons, List.sum_cons, chainP_sum δ H _ _ k.2 _ k.1 (hL k (List.mem_cons_self ..)) χ,
      keys_sum nA H rows χ L (fun k' hk' => hL k' (List.mem_cons_of_mem _ hk')),
      List.flatMap_cons, List.filter_append, List.map_append, List.sum_append]

/-- **The axis chip's honest path total at the C1 table** (one chain per distinct key) is the walk-weight
sum over `axChainReadsK9` — each element of `axChainReadsK9` is consumed exactly once. -/
theorem axSumP_eq (nA : ℕ) (H : Noun → ℕ × ℕ) (rows : Array LX9)
    (hbig : ∀ k ∈ axKeys9 rows, 2 ^ 32 ≤ k.2) {n : ℕ} (hn0 : 0 < n)
    (hn : n = (ComplJ9AAxisRows.tableRows (axChains9 p nA H rows)).length) (χ : Coins frameJ8 K) :
    ComplJ9AChipsOK.axSumP δ hn0 (axChains9 p nA H rows) hn χ =
      ((axChainReadsK9 rows).map (Tw δ H χ)).sum := by
  rw [axSumP_rows, tableRows_sum, axChains9, List.map_map]
  exact keys_sum δ nA H rows χ _ hbig

/-- The run form: on a generated run every key's axis is `≥ 2^62` (`axKeys9_read`). -/
theorem axSumP_eq_run {R : Nock.Jet.Registry} {fuel : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R fuel s f = some (t, r)) (nA : ℕ) (H : Noun → ℕ × ℕ) {n : ℕ} (hn0 : 0 < n)
    (hn : n = (ComplJ9AAxisRows.tableRows (axChains9 p nA H (rowsOfT9 t))).length) (χ : Coins frameJ8 K) :
    ComplJ9AChipsOK.axSumP δ hn0 (axChains9 p nA H (rowsOfT9 t)) hn χ =
      ((axChainReadsK9 (rowsOfT9 t)).map (Tw δ H χ)).sum :=
  axSumP_eq δ nA H _ (fun k hk => le_trans (by norm_num) (axKeys9_read h hk).1) hn0 hn χ

#print axioms chainP_sum
#print axioms dKey_path
#print axioms axSumP_rows
#print axioms axSumP_eq
#print axioms axSumP_eq_run

end Table

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalPAx
