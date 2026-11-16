/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalSAx.lean

`axSumS = Σ_i (1/dKey limbKey_i − mu_i/dKey tagKey_i)` (`ComplJ9AChipsOK.axSumS`).  Here:
  * `dKey_limb` / `dKey_tag`: the two key denominators of a table row, as functions of the row's fields.
  * `axSumS_rows`: `axSumS` is the row sum of `rowLw − mu · tagW`.
  * `limbRecs R n`: the limb consume records `(R, axK, 0, l)` of an `n`-axis chain IN `limbAxes` ORDER (top limb at
    `2^L − 1`, limb `i < L − 1` at `2^(i+2) − 2`) — the common currency of the three limb parties (chain consumes,
    `s10S` consumes, split / atom-walk provides).  **`chainL_sum`**: one chain's limb consumes total `limbRecs`.
  * **`chainT_sum`**: one chain's tag provides total `mu · tagW` at its last row (mu sits on the chain-last row only).

  * **`axSumS_eq`**: at the C1 table `axChains9`, `axSumS = Σ_keys Σ_{limbRecs} 1/den − Σ_{consumer rows} tagW(key)`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalPAx

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSAx

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

/-! ## 1. Multiplicity (generic) -/

/-- **The weighted multiplicity identity**: over a duplicate-free key list containing every key, summing
`count k • w k` is summing `w` once per keyed element. -/
theorem sum_count_smul {α β M : Type} [DecidableEq α] [AddCommMonoid M] (f : β → Option α) (D : List α)
    (hD : D.Nodup) (w : α → M) :
    ∀ L : List β, (∀ l ∈ L, ∀ k, f l = some k → k ∈ D) →
      (D.map fun k => (L.filter fun l => f l = some k).length • w k).sum = ((L.filterMap f).map w).sum := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons l L ih =>
    intro hL
    have ih' := ih (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl'))
    have key : ∀ k : α, ((l :: L).filter fun l => f l = some k).length • w k =
        (if f l = some k then w k else 0) + (L.filter fun l => f l = some k).length • w k := by
      intro k
      by_cases hk : f l = some k
      · simp [List.filter_cons, hk, add_smul, add_comm]
      · simp [List.filter_cons, hk]
    simp only [key]
    rw [List.sum_map_add, ih']
    cases hfl : f l with
    | none =>
      have h0 : (D.map fun k => if (none : Option α) = some k then w k else 0).sum = 0 :=
        List.sum_eq_zero fun x hx => by
          obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
          simp
      rw [h0, zero_add, List.filterMap_cons_none hfl]
    | some a =>
      have haD : a ∈ D := hL l (List.mem_cons_self ..) a hfl
      have hone : (D.map fun k => if some a = some k then w k else 0).sum = w a := by
        clear hL ih ih' key
        induction D with
        | nil => simp at haD
        | cons k D ihD =>
          rw [List.nodup_cons] at hD
          simp only [List.map_cons, List.sum_cons, Option.some.injEq]
          by_cases hak : a = k
          · subst hak
            have : (D.map fun k => if a = k then w k else 0).sum = 0 := by
              refine List.sum_eq_zero fun x hx => ?_
              obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hx
              have : a ≠ k' := fun h => hD.1 (h ▸ hk')
              simp [this]
            simp [this]
          · have hk' : a ∈ D := by
              rcases List.mem_cons.mp haD with h | h
              · exact absurd h hak
              · exact h
            have := ihD hD.2 hk'
            simp only [Option.some.injEq] at this
            simp [hak, this]
      rw [hone]
      simp [List.filterMap_cons, hfl]

theorem sum_map_sub' {α M : Type} [AddCommGroup M] (f g : α → M) :
    ∀ l : List α, (l.map fun x => f x - g x).sum = (l.map f).sum - (l.map g).sum
  | [] => by simp
  | x :: l => by
    simp only [List.map_cons, List.sum_cons, sum_map_sub' f g l]
    abel

/-- **`sum_muOf9_smul`**: `Σ_{k ∈ axKeys9} muOf9 k • w k` is `w` summed once per
`s0B` / `s10B` consumer row (at the row's key). -/
theorem sum_muOf9_smul {M : Type} [AddCommMonoid M] (rows : Array LX9) (w : Noun × ℕ → M) :
    ((axKeys9 rows).map fun k => muOf9 rows k • w k).sum = ((rows.toList.filterMap axKey9).map w).sum :=
  sum_count_smul axKey9 (axKeys9 rows) (axKeys9_nodup rows) w rows.toList
    (fun l hl k hk => mem_axKeys9.2 ⟨l, hl, hk⟩)

/-! ## 2. The row weights and the key denominators -/

section Weights
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The limb weight of a record `(R, axK, 0, l)`. -/
def limbW (χ : Coins frameJ8 K) (q : ZMod p × ZMod p × (ZMod p × ZMod p)) : 𝕂′ :=
  (ρH δ χ + recDenP 0 (γH δ χ) q)⁻¹

/-- The limb consume record of an axis row. -/
def limbRecRow (a : ComplJ9AAxisRows.ARow (ZMod p)) : ZMod p × ZMod p × (ZMod p × ZMod p) := (a.R, a.axK, (0, a.l))

/-- The `TAG_ax` provide vector of an axis row `(hr.v, ftk, ftv, hout.k, hout.v, R, 0, 5)`. -/
def tagVec (a : ComplJ9AAxisRows.ARow (ZMod p)) : Fin 8 → K := fun c =>
  algebraMap (ZMod p) K (![a.hrv, a.ftk, a.ftv, a.houtk, a.houtv, a.R, 0,
    ((Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.tagAx : ℕ) : ZMod p)] c)

/-- The tag weight of an 8-entry record vector at the handle coins `(γH, ρH)`. -/
def tagW (χ : Coins frameJ8 K) (v : Fin 8 → K) : 𝕂′ :=
  (FiniteIO.compress (⟨γH δ χ, ρH δ χ⟩ : FiniteIO.IOCoins 𝕂′) (BalanceQ.liftRec (K := K) (L := 𝕂′) v))⁻¹

/-- The service term of one axis row. -/
def rowS (χ : Coins frameJ8 K) (a : ComplJ9AAxisRows.ARow (ZMod p)) : 𝕂′ :=
  limbW δ χ (limbRecRow a) - liftQ δ a.mu * tagW δ χ (tagVec a)

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

theorem dKey_limb {n : ℕ} (hn0 : 0 < n) (rows : List (ComplJ9AAxisRows.ARow (ZMod p)))
    (hn : n = rows.length) (χ : Coins frameJ8 K) (i : Fin n) :
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.dKey δ (chalsMJ8 δ χ) hn0
        (ComplJ9AAxisRows.tableCol rows hn0 hn) Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.limbKey i =
      ρH δ χ + recDenP 0 (γH δ χ) (limbRecRow (rows[i.1]'(hn ▸ i.2))) := by
  have h6 : fullCol hn0 (ComplJ9AAxisRows.tableCol rows hn0 hn) 6 i = (rows[i.1]'(hn ▸ i.2)).R := by
    rw [ComplJ9AAxisRows.fullCol_row]; rfl
  have h8 : fullCol hn0 (ComplJ9AAxisRows.tableCol rows hn0 hn) 8 i = (rows[i.1]'(hn ▸ i.2)).l := by
    rw [ComplJ9AAxisRows.fullCol_row]; rfl
  have h9 : fullCol hn0 (ComplJ9AAxisRows.tableCol rows hn0 hn) 9 i = (rows[i.1]'(hn ▸ i.2)).axK := by
    rw [ComplJ9AAxisRows.fullCol_row]; rfl
  unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.dKey
  rw [ComplJ9AChipsOK.kappa_eq]
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_eight, BalanceQ.liftRec,
    Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.keyVecL, Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.limbKey,
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.envC, recDenP, limbRecRow,
    Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.R, Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.axK,
    Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.l]
  simp [cv, CoeffExpr.eval, h6, h8, h9, ComplJ9AAxisRows.ARow.col, IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]

theorem dKey_tag {n : ℕ} (hn0 : 0 < n) (rows : List (ComplJ9AAxisRows.ARow (ZMod p)))
    (hn : n = rows.length) (χ : Coins frameJ8 K) (i : Fin n) :
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.dKey δ (chalsMJ8 δ χ) hn0
        (ComplJ9AAxisRows.tableCol rows hn0 hn) Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.tagKey i =
      FiniteIO.compress (⟨γH δ χ, ρH δ χ⟩ : FiniteIO.IOCoins 𝕂′)
        (BalanceQ.liftRec (K := K) (L := 𝕂′) (tagVec (rows[i.1]'(hn ▸ i.2)))) := by
  have hc : ∀ j, 2 ≤ j → fullCol hn0 (ComplJ9AAxisRows.tableCol rows hn0 hn) j i =
      (rows[i.1]'(hn ▸ i.2)).col (fullCol hn0 (ComplJ9AAxisRows.tableCol rows hn0 hn) 0 i)
        (fullCol hn0 (ComplJ9AAxisRows.tableCol rows hn0 hn) 1 i) j := fun j _ => by
    rw [ComplJ9AAxisRows.fullCol_row]
  unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.dKey
  rw [ComplJ9AChipsOK.kappa_eq]
  congr 2
  funext c
  fin_cases c <;>
    simp [tagVec, Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.keyVecL,
      Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.tagKey, Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH.envC,
      cv, CoeffExpr.eval, hc, ComplJ9AAxisRows.ARow.col,
      Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.hrv, Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.ftk,
      Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.ftv, Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.houtk,
      Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.houtv, Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.R]

/-- **`axSumS` is the row sum of `rowS`** over the table rows. -/
theorem axSumS_rows {n : ℕ} (hn0 : 0 < n) (cs : List (ComplJ9AAxisRows.ChainSpec (ZMod p)))
    (hn : n = (ComplJ9AAxisRows.tableRows cs).length) (χ : Coins frameJ8 K) :
    ComplJ9AChipsOK.axSumS δ hn0 cs hn χ = ((ComplJ9AAxisRows.tableRows cs).map (rowS δ χ)).sum := by
  unfold ComplJ9AChipsOK.axSumS
  simp_rw [dKey_limb δ hn0 _ hn χ, dKey_tag δ hn0 _ hn χ]
  subst hn
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

end Weights

/-! ## 3. One chain -/

section Chain
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The limb consume records of an `n`-axis chain with id `R`, in `limbAxes` order**: the top limb at
`2^L − 1`, then limb `i < L − 1` at `2^(i+2) − 2` (`L = top n + 1`). -/
def limbRecs (R n : ℕ) : List (ZMod p × ZMod p × (ZMod p × ZMod p)) :=
  ((R : ZMod p), ((2 ^ (top n + 1) : ℕ) : ZMod p) - 1, (0, ((n / 2 ^ (32 * top n) % 2 ^ 32 : ℕ) : ZMod p))) ::
    (List.range (top n)).map fun i =>
      ((R : ZMod p), ((2 ^ (i + 2) : ℕ) : ZMod p) - 2, (0, ((n / 2 ^ (32 * i) % 2 ^ 32 : ℕ) : ZMod p)))

theorem list_range_sum {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∀ m, ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_range_sum f m, Finset.sum_range_succ]
    simp

/-- The limb record of the head row of a chain. -/
theorem limbRec_row0 (H : Noun → ℕ × ℕ) (route0 : Bool) (R n mu : ℕ) (X : Noun) (hn : n ≠ 0) :
    limbRecRow ((chainOf (F := ZMod p) H route0 R n mu X).row 0) =
      ((R : ZMod p), ((2 ^ (top n + 1) : ℕ) : ZMod p) - 1,
        (0, ((n / 2 ^ (32 * top n) % 2 ^ 32 : ℕ) : ZMod p))) := by
  have hL := top_eq_length n hn
  simp only [limbRecRow, ComplJ9AAxisRows.ChainSpec.row, ComplJ9AAxisRows.chainRow, chainOf,
    beq_self_eq_true, if_true, hL, Nat.sub_zero, limbs_getD, Nat.add_sub_cancel]

/-- The limb record of chain row `j + 1`. -/
theorem limbRec_rowS (H : Noun → ℕ × ℕ) (route0 : Bool) (R n mu : ℕ) (X : Noun) (hn : n ≠ 0) (j : ℕ)
    (hj : j < top n) :
    limbRecRow ((chainOf (F := ZMod p) H route0 R n mu X).row (j + 1)) =
      ((R : ZMod p), ((2 ^ (top n + 1 - j) : ℕ) : ZMod p) - 2,
        (0, ((n / 2 ^ (32 * (top n - 1 - j)) % 2 ^ 32 : ℕ) : ZMod p))) := by
  have hL := top_eq_length n hn
  have hb : (j + 1 == 0) = false := by simp
  have e1 : top n + 1 + 1 - (j + 1) = top n + 1 - j := by omega
  have e2 : top n + 1 - 1 - (j + 1) = top n - 1 - j := by omega
  simp only [limbRecRow, ComplJ9AAxisRows.ChainSpec.row, ComplJ9AAxisRows.chainRow, chainOf,
    hb, Bool.false_eq_true, if_false, hL, limbs_getD, e1, e2]

/-- **`chainL_sum`: one chain's limb consumes total its `limbRecs`.** -/
theorem chainL_sum (H : Noun → ℕ × ℕ) (route0 : Bool) (R n mu : ℕ) (X : Noun) (hn : n ≠ 0)
    (χ : Coins frameJ8 K) :
    ((chainOf (F := ZMod p) H route0 R n mu X).rows.map fun a => limbW δ χ (limbRecRow a)).sum =
      ((limbRecs R n).map (limbW δ χ)).sum := by
  have hL := top_eq_length n hn
  have hls : (chainOf (F := ZMod p) H route0 R n mu X).ls.length = top n + 1 := hL
  rw [ComplJ9AAxisRows.ChainSpec.rows, hls, List.map_map, List.range_succ_eq_map, List.map_cons, List.sum_cons,
    limbRecs, List.map_cons, List.sum_cons, List.map_map]
  refine congrArg₂ (· + ·) ?_ ?_
  · simp only [Function.comp_apply, limbRec_row0 H route0 R n mu X hn]
  · rw [list_range_sum, List.map_map, list_range_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    simp only [Function.comp_apply]
    rw [limbRec_rowS H route0 R n mu X hn (top n - 1 - j) (by omega)]
    have e1 : top n + 1 - (top n - 1 - j) = j + 2 := by omega
    have e2 : top n - 1 - (top n - 1 - j) = j := by omega
    rw [e1, e2]

/-- An 8-entry `TAG_ax` record `(hr.v, ft.k, ft.v, out.k, out.v, id, 0, 5)`. -/
def tagRec (hr ftk ftv ok ov R : ZMod p) : Fin 8 → K := fun c =>
  algebraMap (ZMod p) K (![hr, ftk, ftv, ok, ov, R, 0,
    ((Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.tagAx : ℕ) : ZMod p)] c)

theorem row_mu (H : Noun → ℕ × ℕ) (route0 : Bool) (R n mu : ℕ) (X : Noun) (j : ℕ) :
    ((chainOf (F := ZMod p) H route0 R n mu X).row j).mu =
      if j + 1 = (Nock.Atoms.limbs n).length then (mu : ZMod p) else 0 := rfl

/-- **The tag vector of a chain's last row** (the only row with a nonzero `mu`): subject handle value, the axis
atom's handle `(0, n)` (field, `route0`) or `(2, R)` (big), the noun after the last segment, the id. -/
theorem tagVec_last (H : Noun → ℕ × ℕ) (route0 : Bool) (R n mu : ℕ) (X : Noun) :
    tagVec (K := K) ((chainOf (F := ZMod p) H route0 R n mu X).row (top n)) =
      tagRec (((H X).2 : ℕ) : ZMod p) (if route0 then 0 else 2) (if route0 then (n : ZMod p) else (R : ZMod p))
        (((H (segN n X (top n))).1 : ℕ) : ZMod p) (((H (segN n X (top n))).2 : ℕ) : ZMod p) (R : ZMod p) := by
  funext c
  fin_cases c <;> simp [tagVec, tagRec, ComplJ9AAxisRows.ChainSpec.row, ComplJ9AAxisRows.chainRow, chainOf]

/-- **`chainT_sum`: one chain's tag provides total `mu · tagW` at its last row.** -/
theorem chainT_sum (H : Noun → ℕ × ℕ) (route0 : Bool) (R n mu : ℕ) (X : Noun) (hn : n ≠ 0)
    (χ : Coins frameJ8 K) :
    ((chainOf (F := ZMod p) H route0 R n mu X).rows.map fun a => liftQ δ a.mu * tagW δ χ (tagVec a)).sum =
      liftQ δ (mu : ZMod p) * tagW δ χ (tagVec ((chainOf (F := ZMod p) H route0 R n mu X).row (top n))) := by
  have hL := top_eq_length n hn
  have hls : (chainOf (F := ZMod p) H route0 R n mu X).ls.length = top n + 1 := hL
  rw [ComplJ9AAxisRows.ChainSpec.rows, hls, List.range_succ]
  simp only [List.map_append, List.sum_append, List.map_map, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  have h0 : ((List.range (top n)).map ((fun a => liftQ δ a.mu * tagW δ χ (tagVec a)) ∘
      (chainOf (F := ZMod p) H route0 R n mu X).row)).sum = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hj' := List.mem_range.mp hj
    simp only [Function.comp_apply, row_mu, hL, if_neg (show j + 1 ≠ top n + 1 by omega)]
    simp [liftQ]
  rw [h0, zero_add]
  simp [row_mu, hL]

/-- One chain's service total: limb consumes minus tag provides. -/
theorem chainS_sum (H : Noun → ℕ × ℕ) (route0 : Bool) (R n mu : ℕ) (X : Noun) (hn : n ≠ 0)
    (χ : Coins frameJ8 K) :
    ((chainOf (F := ZMod p) H route0 R n mu X).rows.map (rowS δ χ)).sum =
      ((limbRecs R n).map (limbW δ χ)).sum -
        liftQ δ (mu : ZMod p) * tagW δ χ (tagVec ((chainOf (F := ZMod p) H route0 R n mu X).row (top n))) := by
  unfold rowS
  rw [sum_map_sub', chainL_sum δ H route0 R n mu X hn χ, chainT_sum δ H route0 R n mu X hn χ]

/-- **`limbRecs` of a field axis** (`2^32 ≤ v < 2^64`, two limbs): exactly the split chip's two provided records
`(R, 3, 0, hi)`, `(R, 2, 0, lo)` (`ComplJ9ASplitH.d3` / `d2` at `R = nA + i`). -/
theorem limbRecs_field (R v : ℕ) (h1 : 2 ^ 32 ≤ v) (h2 : v < 2 ^ 64) :
    limbRecs (p := p) R v = [((R : ZMod p), 3, (0, ((v / 2 ^ 32 : ℕ) : ZMod p))),
      ((R : ZMod p), 2, (0, ((v % 2 ^ 32 : ℕ) : ZMod p)))] := by
  have ht : top v = 1 := by
    unfold top
    exact Nat.log_eq_of_pow_le_of_lt_pow (by simpa using h1) (by norm_num; omega)
  have hhi : v / 2 ^ 32 % 2 ^ 32 = v / 2 ^ 32 := Nat.mod_eq_of_lt (by omega)
  simp only [limbRecs, ht, List.range_one, List.map_cons, List.map_nil, Nat.mul_one, Nat.mul_zero, pow_zero,
    Nat.div_one, hhi]
  norm_num

end Chain

/-! ## 4. The table at the C1 chains -/

section Table
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The tag weight of a key `(X, n)`** at the C1 chain of that key (`tagVec_last`). -/
def tagKW (nA : ℕ) (H : Noun → ℕ × ℕ) (rows : Array LX9) (χ : Coins frameJ8 K) (k : Noun × ℕ) : 𝕂′ :=
  tagW δ χ (tagVec (K := K) ((chainOf (F := ZMod p) H (decide (k.2 < p)) (idOf9 p nA H (fieldAx9 p rows) k.2) k.2
    (muOf9 rows k) k.1).row (top k.2)))

theorem liftQ_nat (m : ℕ) (x : 𝕂′) : liftQ δ ((m : ℕ) : ZMod p) * x = m • x := by
  rw [nsmul_eq_mul]; simp [liftQ]

/-- **C3 axis half: `axSumS` at the C1 table** = the chains' limb consumes (per distinct key, `limbRecs`) minus
the tag provides, which are `tagKW` once per `s0B` / `s10B` consumer row (`sum_muOf9_smul`). -/
theorem axSumS_eq (nA : ℕ) (H : Noun → ℕ × ℕ) (rows : Array LX9)
    (hnz : ∀ k ∈ axKeys9 rows, k.2 ≠ 0) {n : ℕ} (hn0 : 0 < n)
    (hn : n = (ComplJ9AAxisRows.tableRows (axChains9 p nA H rows)).length) (χ : Coins frameJ8 K) :
    ComplJ9AChipsOK.axSumS δ hn0 (axChains9 p nA H rows) hn χ =
      ((axKeys9 rows).map fun k => ((limbRecs (idOf9 p nA H (fieldAx9 p rows) k.2) k.2).map (limbW δ χ)).sum).sum -
        ((rows.toList.filterMap axKey9).map (tagKW δ nA H rows χ)).sum := by
  rw [axSumS_rows, ComplJ9ABalPAx.tableRows_sum, axChains9, List.map_map, ← sum_muOf9_smul, ← sum_map_sub']
  refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
  simp only [Function.comp_apply]
  rw [chainS_sum δ H _ _ k.2 _ k.1 (hnz k hk) χ, liftQ_nat]
  rfl

/-- The run form: every key's axis is `≥ 2^62` (`axKeys9_read`). -/
theorem axSumS_eq_run {R : Nock.Jet.Registry} {fuel : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R fuel s f = some (t, r)) (nA : ℕ) (H : Noun → ℕ × ℕ) {n : ℕ} (hn0 : 0 < n)
    (hn : n = (ComplJ9AAxisRows.tableRows (axChains9 p nA H (rowsOfT9 t))).length) (χ : Coins frameJ8 K) :
    ComplJ9AChipsOK.axSumS δ hn0 (axChains9 p nA H (rowsOfT9 t)) hn χ =
      ((axKeys9 (rowsOfT9 t)).map fun k =>
          ((limbRecs (idOf9 p nA H (fieldAx9 p (rowsOfT9 t)) k.2) k.2).map (limbW δ χ)).sum).sum -
        (((rowsOfT9 t).toList.filterMap axKey9).map (tagKW δ nA H (rowsOfT9 t) χ)).sum :=
  axSumS_eq δ nA H _ (fun k hk => by have := (axKeys9_read h hk).1; positivity) hn0 hn χ

end Table

section Axioms
#print axioms sum_count_smul
#print axioms sum_muOf9_smul
#print axioms dKey_limb
#print axioms dKey_tag
#print axioms axSumS_rows
#print axioms limbRec_row0
#print axioms limbRec_rowS
#print axioms chainL_sum
#print axioms limbRecs_field
#print axioms tagVec_last
#print axioms chainT_sum
#print axioms chainS_sum
#print axioms axSumS_eq
#print axioms axSumS_eq_run
end Axioms

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSAx
