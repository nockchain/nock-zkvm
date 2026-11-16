/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AChips.lean

  `Nock.V1J9A.GenAxE.axGenE` / `Nock.V1J9A.GenSpE.spGenE` (executable, `K6`) equal, column by column, the honest
  `ComplJ9AAxisH.colAx` / `ComplJ9ASplitH.colS` (at `KC`, `deltaF`, `powerBasis3`, `chalsMJ8 deltaF (toχ χe)`);
  their publics, through `K3.toK`, are `ComplJ9AChipsOK.pubsXOf` / `pubsSOf`. -/
import Nock.V1J9A.GenAxE
import Nock.V1J9A.GenSpE
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AChipsOK
import Nock.V1J8.FillCell

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J9A
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (liftQ)

/-! ## 1. Generic bridges -/

theorem toQ_zq (x : ZMod p) : K6.toQ (GenAxE.zq x) = liftQ (K := KC) deltaF x := by
  unfold GenAxE.zq
  rw [toQ_g6, Gold.toZ_ofZ]
  exact IsScalarTower.algebraMap_apply (ZMod p) KC KQ _

theorem toQ_γHE (χe : CoinsE) : K6.toQ (γHE χe) = ComplJ8Bad.γH deltaF (toχ χe) := rfl
theorem toQ_ρHE (χe : CoinsE) : K6.toQ (ρHE χe) = ComplJ8Bad.ρH deltaF (toχ χe) := rfl

/-- `inclSums l` is the tail of `scanl (+) 0 l`. -/
theorem inclSums_eq (l : List K6) : GenAxE.inclSums l = (List.scanl (· + ·) 0 l).tail := by
  have key : ∀ (l : List K6) (a : K6) (acc : List K6),
      (l.foldl (fun (s : K6 × List K6) x => let a := s.1 + x; (a, a :: s.2)) (a, acc)).2 =
        (List.scanl (· + ·) a l).tail.reverse ++ acc := by
    intro l
    induction l with
    | nil => intro a acc; simp
    | cons x l ih =>
      intro a acc
      rw [List.foldl_cons, ih, List.scanl_cons, List.tail_cons]
      cases l <;> simp [List.scanl]
  unfold GenAxE.inclSums
  rw [key]; simp

theorem inclSums_length (l : List K6) : (GenAxE.inclSums l).length = l.length := by
  rw [inclSums_eq]; simp

theorem toQ_scanl_getD : ∀ (l : List K6) (a : K6) (i : ℕ), i < l.length →
    K6.toQ ((List.scanl (· + ·) a l).getD (i + 1) 0) =
      K6.toQ a + ∑ j ∈ Finset.range (i + 1), K6.toQ (l.getD j 0)
  | [], a, i, h => by simp at h
  | x :: t, a, 0, _ => by
    rw [List.scanl_cons, List.getD_cons_succ]
    cases t <;> simp [List.scanl_cons, K6.toQ_add]
  | x :: t, a, j + 1, h => by
    have ih := toQ_scanl_getD t (a + x) j (by simpa using h)
    rw [List.scanl_cons, List.getD_cons_succ, ih, K6.toQ_add]
    rw [Finset.sum_range_succ' _ (j + 1)]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    abel

theorem toQ_inclSums_getD (l : List K6) (i : ℕ) (hi : i < l.length) :
    K6.toQ ((GenAxE.inclSums l).getD i 0) = ∑ j ∈ Finset.range (i + 1), K6.toQ (l.getD j 0) := by
  rw [inclSums_eq]
  have := toQ_scanl_getD l 0 i hi
  rw [K6.toQ_zero, zero_add] at this
  rw [← this]
  have e : ∀ L : List K6, L.tail.getD i 0 = L.getD (i + 1) 0 := by
    intro L; cases L <;> simp
  rw [e]

/-! ## 2. The axis chip -/

section Axis
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisRows (ARow tableRows tableCol)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH
variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

theorem mask_irrel (a : ARow (ZMod p)) (f l f' l' : ZMod p) (c : ℕ) (hc : 2 ≤ c) :
    a.col f l c = a.col f' l' c := by
  match c, hc with
  | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl
  | 8, _ => rfl | 9, _ => rfl | 10, _ => rfl | 11, _ => rfl | 12, _ => rfl | 13, _ => rfl
  | 14, _ => rfl | 15, _ => rfl | 16, _ => rfl | 17, _ => rfl | 18, _ => rfl | 19, _ => rfl
  | 20, _ => rfl | 21, _ => rfl
  | c + 22, _ => rfl

theorem fullCol_eq_colAt (rows : List (ARow (ZMod p))) {n : ℕ} (hn0 : 0 < n) (hn : n = rows.length)
    (j : ℕ) (i : Fin n) :
    Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.fullCol hn0 (tableCol rows hn0 hn) j i = GenAxE.colAt rows i j := by
  have hi : (i : ℕ) < rows.length := hn ▸ i.2
  unfold GenAxE.colAt
  rw [List.getElem?_eq_getElem hi]
  simp only
  rcases j with _ | _ | j
  · unfold Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.fullCol; simp [ARow.col]
  · unfold Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.fullCol
    simp only [ARow.col, if_neg (show (0 + 1 : ℕ) ≠ 0 by omega), if_true]
    have : (i = ⟨n - 1, Nat.sub_lt hn0 (by omega)⟩) ↔ (i : ℕ) + 1 = rows.length := by
      constructor
      · intro h; rw [h]; simp; omega
      · intro h; exact Fin.ext (by simp; omega)
    simp only [this]
  · unfold Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.fullCol
    rw [if_neg (by omega), if_neg (by omega)]
    unfold tableCol
    exact mask_irrel _ _ _ _ _ _ (by omega)

theorem envE_eq (rows : List (ARow (ZMod p))) {n : ℕ} (hn0 : 0 < n) (hn : n = rows.length) (i : Fin n) :
    GenAxE.envE rows i = envC hn0 (tableCol rows hn0 hn) i (fun _ => 0) := by
  unfold GenAxE.envE envC
  congr 1
  funext j
  exact (fullCol_eq_colAt rows hn0 hn j i).symm

theorem toQ_dKeyE (χe : CoinsE) (rows : List (ARow (ZMod p))) {n : ℕ} (hn0 : 0 < n) (hn : n = rows.length)
    (key : List (Nock.NockVMROM.Thm54.CoordinateCompiler.CoeffExpr (ZMod p))) (i : Fin n) :
    K6.toQ (GenAxE.dKeyE χe rows key i) =
      dKey deltaF (VerJ8.chalsMJ8 deltaF (toχ χe)) hn0 (tableCol rows hn0 hn) key i := by
  unfold GenAxE.dKeyE dKey
  rw [toQ_compressE, ComplJ9AChipsOK.kappa_eq, toQ_γHE, toQ_ρHE, envE_eq rows hn0 hn i]
  congr 1
  funext c
  rw [toQ_zq]
  rfl

theorem tableCol_eq_colAt (rows : List (ARow (ZMod p))) {n : ℕ} (hn0 : 0 < n) (hn : n = rows.length)
    (j : ℕ) (hj : 2 ≤ j) (i : Fin n) : tableCol rows hn0 hn j i = GenAxE.colAt rows i j := by
  rw [← fullCol_eq_colAt rows hn0 hn j i]
  unfold fullCol
  rw [if_neg (by omega), if_neg (by omega)]

theorem toQ_sRowE (χe : CoinsE) (rows : List (ARow (ZMod p))) {n : ℕ} (hn0 : 0 < n) (hn : n = rows.length)
    (i : Fin n) :
    K6.toQ (GenAxE.sRowE χe rows i) = sRow deltaF (VerJ8.chalsMJ8 deltaF (toχ χe)) hn0 (tableCol rows hn0 hn) i := by
  unfold GenAxE.sRowE sRow
  rw [K6.toQ_sub, K6.toQ_mul, K6.toQ_inv, K6.toQ_inv, toQ_dKeyE χe rows hn0 hn, toQ_dKeyE χe rows hn0 hn,
    toQ_zq, tableCol_eq_colAt rows hn0 hn _ (by decide)]

theorem toQ_pRowE (χe : CoinsE) (rows : List (ARow (ZMod p))) {n : ℕ} (hn0 : 0 < n) (hn : n = rows.length)
    (i : Fin n) :
    K6.toQ (GenAxE.pRowE χe rows i) = pRow deltaF (VerJ8.chalsMJ8 deltaF (toχ χe)) hn0 (tableCol rows hn0 hn) i := by
  unfold GenAxE.pRowE pRow
  rw [K6.toQ_mul, K6.toQ_inv, toQ_dKeyE χe rows hn0 hn, toQ_zq, tableCol_eq_colAt rows hn0 hn _ (by decide)]

theorem toQ_accS (χe : CoinsE) (rows : List (ARow (ZMod p))) {n : ℕ} (hn0 : 0 < n) (hn : n = rows.length)
    (i : Fin n) :
    K6.toQ ((GenAxE.inclSums ((List.range rows.length).map (GenAxE.sRowE χe rows))).getD i 0) =
      accSN deltaF (VerJ8.chalsMJ8 deltaF (toχ χe)) hn0 (tableCol rows hn0 hn) i := by
  rw [toQ_inclSums_getD _ _ (by simp; omega)]
  unfold accSN
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < n := by have := Finset.mem_range.mp hj; have := i.2; omega
  rw [sN, dif_pos hj', ← toQ_sRowE χe rows hn0 hn ⟨j, hj'⟩]
  simp [List.getD_eq_getElem?_getD, hn ▸ hj']

theorem toQ_accP (χe : CoinsE) (rows : List (ARow (ZMod p))) {n : ℕ} (hn0 : 0 < n) (hn : n = rows.length)
    (i : Fin n) :
    K6.toQ ((GenAxE.inclSums ((List.range rows.length).map (GenAxE.pRowE χe rows))).getD i 0) =
      accPN deltaF (VerJ8.chalsMJ8 deltaF (toχ χe)) hn0 (tableCol rows hn0 hn) i := by
  rw [toQ_inclSums_getD _ _ (by simp; omega)]
  unfold accPN
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < n := by have := Finset.mem_range.mp hj; have := i.2; omega
  rw [pN, dif_pos hj', ← toQ_pRowE χe rows hn0 hn ⟨j, hj'⟩]
  simp [List.getD_eq_getElem?_getD, hn ▸ hj']

theorem getD_flatMap_chunk {α β : Type} (g : α → List β) (m : ℕ) (hg : ∀ a, (g a).length = m) (d : α) (e : β) :
    ∀ (L : List α) (r k : ℕ), k < m → r < L.length → (L.flatMap g).getD (m * r + k) e = (g (L.getD r d)).getD k e
  | [], r, k, _, h => by simp at h
  | a :: t, 0, k, hk, _ => by
    rw [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getD_append _ _ _ _ (by rw [hg]; exact hk)]
    rfl
  | a :: t, r + 1, k, hk, h => by
    rw [List.flatMap_cons, show m * (r + 1) + k = (g a).length + (m * r + k) by rw [hg]; ring,
      List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      getD_flatMap_chunk g m hg d e t r k hk (by simpa using h), List.getD_cons_succ]

theorem getD_roleLimbs (q : List K6) (r k : ℕ) (hk : k < 3) (hr : r < 2 * q.length) :
    (GenAxE.roleLimbs q).getD (3 * r + k) 0 =
      limbZ (if r % 2 = 0 then (q.getD (r / 2) 0).re else (q.getD (r / 2) 0).im) k := by
  unfold GenAxE.roleLimbs
  have hlen : (q.flatMap fun a => [a.re, a.im]).length = 2 * q.length := by
    simp [List.length_flatMap]; omega
  rw [getD_flatMap_chunk (fun k : K3 => [k.c0.toZ, k.c1.toZ, k.c2.toZ]) 3 (fun _ => rfl) 0 0 _ r k hk
    (by omega)]
  have h2 := getD_flatMap_chunk (fun a : K6 => [a.re, a.im]) 2 (fun _ => rfl) 0 0 q (r / 2) (r % 2)
    (Nat.mod_lt _ (by norm_num)) (by omega)
  rw [show 2 * (r / 2) + r % 2 = r by omega] at h2
  rw [h2]
  rcases Nat.mod_two_eq_zero_or_one r with h | h
  · rw [if_pos h, h]
    interval_cases k <;> simp [limbZ, MemX.limb]
  · rw [if_neg (by omega), h]
    interval_cases k <;> simp [limbZ, MemX.limb]

theorem tableCol_eq_fullCol (rows : List (ARow (ZMod p))) {n : ℕ} (hn0 : 0 < n) (hn : n = rows.length)
    (j : ℕ) (i : Fin n) : tableCol rows hn0 hn j i = GenAxE.colAt rows i j := by
  by_cases hj : 2 ≤ j
  · exact tableCol_eq_colAt rows hn0 hn j hj i
  · rw [← fullCol_eq_colAt rows hn0 hn j i]
    unfold fullCol tableCol
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · simp [ARow.col]
    · simp [ARow.col]

theorem coordN_toK' (x : K3) (m : ℕ) : coordN powerBasis3 (K3.toK x) m = limbZ x (m % 3) := by
  rw [coordN, coord_K _ _ (Nat.mod_lt _ (by norm_num))]

/-- The five `𝕂′` columns of row `i`, executable. -/
def qL (χe : CoinsE) (rows : List (ARow (ZMod p))) (i : ℕ) : List K6 :=
  [(GenAxE.dKeyE χe rows AxisChipJ9.limbKey i)⁻¹, (GenAxE.dKeyE χe rows AxisChipJ9.pathKey i)⁻¹,
    (GenAxE.dKeyE χe rows AxisChipJ9.tagKey i)⁻¹,
    (GenAxE.inclSums ((List.range rows.length).map (GenAxE.sRowE χe rows))).getD i 0,
    (GenAxE.inclSums ((List.range rows.length).map (GenAxE.pRowE χe rows))).getD i 0]

theorem qvRows_getD (χe : CoinsE) (rows : List (ARow (ZMod p))) (i : ℕ) (hi : i < rows.length) :
    (GenAxE.qvRows χe rows).getD i [] = qL χe rows i := by
  simp [GenAxE.qvRows, qL, List.getD_eq_getElem?_getD, hi]

theorem toQ_qv (χe : CoinsE) (rows : List (ARow (ZMod p))) {n : ℕ} (hn0 : 0 < n) (hn : n = rows.length)
    (s : ℕ) (hs : s < 5) (i : Fin n) :
    qv deltaF (VerJ8.chalsMJ8 deltaF (toχ χe)) hn0 (tableCol rows hn0 hn) s i =
      K6.toQ ((qL χe rows i).getD s 0) := by
  interval_cases s
  · simp [qv, qL, K6.toQ_inv, toQ_dKeyE χe rows hn0 hn] <;> rfl
  · simp [qv, qL, K6.toQ_inv, toQ_dKeyE χe rows hn0 hn] <;> rfl
  · simp [qv, qL, K6.toQ_inv, toQ_dKeyE χe rows hn0 hn] <;> rfl
  · simp only [qv, qL, List.getD_cons_succ, List.getD_cons_zero]
    exact (toQ_accS χe rows hn0 hn i).symm
  · simp only [qv, qL, List.getD_cons_succ, List.getD_cons_zero]
    exact (toQ_accP χe rows hn0 hn i).symm

/-- **L2 (axis): the executable axis table is `colAx`**, every row `i < n`, every column `c < 52`. -/
theorem axGenE_cols (χe : CoinsE) (cs : List (ComplJ9AAxisRows.ChainSpec (ZMod p))) {n : ℕ} (hn0 : 0 < n)
    (hn : n = (ComplJ9AAxisRows.tableRows cs).length) (i : Fin n) (c : ℕ) (hc : c < 52) :
    ((GenAxE.axGenE χe cs).1.getD i #[]).getD c 0 =
      colAx deltaF powerBasis3 (VerJ8.chalsMJ8 deltaF (toχ χe)) hn0 (tableCol (ComplJ9AAxisRows.tableRows cs) hn0 hn) c i := by
  have hi : (i : ℕ) < (ComplJ9AAxisRows.tableRows cs).length := hn ▸ i.2
  have hrow : (GenAxE.axGenE χe cs).1.getD i #[] =
      ((List.range 22).map (GenAxE.colAt (ComplJ9AAxisRows.tableRows cs) i) ++
        GenAxE.roleLimbs (qL χe (ComplJ9AAxisRows.tableRows cs) i)).toArray := by
    have hq : (GenAxE.qvRows χe (ComplJ9AAxisRows.tableRows cs))[(i : ℕ)]? =
        some (qL χe (ComplJ9AAxisRows.tableRows cs) i) := by
      simp [GenAxE.qvRows, qL, hi]
    have hz : ((List.range (ComplJ9AAxisRows.tableRows cs).length).zip
        (GenAxE.qvRows χe (ComplJ9AAxisRows.tableRows cs)))[(i : ℕ)]? =
        some ((i : ℕ), qL χe (ComplJ9AAxisRows.tableRows cs) i) :=
      List.getElem?_zip_eq_some.mpr ⟨by simp [hi], hq⟩
    simp [GenAxE.axGenE, GenAxE.axRows, Array.getD_eq_getD_getElem?, hz]
  rw [hrow]
  unfold colAx
  by_cases h22 : c < 22
  · rw [if_pos h22, tableCol_eq_fullCol _ hn0 hn]
    simp [Array.getD_eq_getD_getElem?, List.getElem?_append_left, h22]
  · rw [if_neg h22]
    have hr : (c - 22) / 3 < 2 * (qL χe (ComplJ9AAxisRows.tableRows cs) i).length := by simp [qL]; omega
    have hlen : (List.map (GenAxE.colAt (ComplJ9AAxisRows.tableRows cs) i) (List.range 22)).length = 22 := by simp
    have e1 : ((List.map (GenAxE.colAt (ComplJ9AAxisRows.tableRows cs) i) (List.range 22) ++
        GenAxE.roleLimbs (qL χe (ComplJ9AAxisRows.tableRows cs) i)).toArray).getD c 0 =
        (GenAxE.roleLimbs (qL χe (ComplJ9AAxisRows.tableRows cs) i)).getD (c - 22) 0 := by
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_append_right (by omega), hlen]
      simp [List.getD_eq_getElem?_getD]
    rw [e1, show c - 22 = 3 * ((c - 22) / 3) + (c - 22) % 3 by omega,
      getD_roleLimbs _ _ _ (Nat.mod_lt _ (by norm_num)) hr]
    have hs : (c - 22) / 3 / 2 < 5 := by omega
    rw [show 3 * ((c - 22) / 3) + (c - 22) % 3 = c - 22 by omega]
    unfold roleV
    rw [toQ_qv χe _ hn0 hn _ hs i]
    split_ifs
    · rw [re_toQ, coordN_toK']
    · rw [im_toQ, coordN_toK']

/-! ### Axis publics -/

theorem toQ_foldl_add (f : ℕ → K6) : ∀ (n : ℕ) (a : K6),
    K6.toQ (((List.range n).map f).foldl (· + ·) a) = K6.toQ a + ∑ i ∈ Finset.range n, K6.toQ (f i)
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, K6.toQ_add]
    rw [toQ_foldl_add f n a, Finset.sum_range_succ]; abel

theorem toQ_foldl_zero (f : ℕ → K6) (n : ℕ) :
    K6.toQ (((List.range n).map f).foldl (· + ·) 0) = ∑ i ∈ Finset.range n, K6.toQ (f i) := by
  rw [toQ_foldl_add, K6.toQ_zero, zero_add]

theorem pubsXE_eq (χe : CoinsE) (cs : List (ComplJ9AAxisRows.ChainSpec (ZMod p))) {n : ℕ} (hn0 : 0 < n)
    (hn : n = (ComplJ9AAxisRows.tableRows cs).length) (j : ℕ) :
    K3.toK (GenAxE.pubsXE χe (ComplJ9AAxisRows.tableRows cs) j) =
      ComplJ9AChipsOK.pubsXOf deltaF hn0 cs hn (toχ χe) j := by
  have hS : K6.toQ (((List.range (ComplJ9AAxisRows.tableRows cs).length).map
      (GenAxE.sRowE χe (ComplJ9AAxisRows.tableRows cs))).foldl (· + ·) 0) =
      ComplJ9AChipsOK.axSumS deltaF hn0 cs hn (toχ χe) := by
    rw [toQ_foldl_zero, ComplJ9AChipsOK.axSumS, ← hn, ← Fin.sum_univ_eq_sum_range
      (fun i => K6.toQ (GenAxE.sRowE χe (ComplJ9AAxisRows.tableRows cs) i)) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := toQ_sRowE χe (ComplJ9AAxisRows.tableRows cs) hn0 hn i
    rw [this]; rfl
  have hP : K6.toQ (((List.range (ComplJ9AAxisRows.tableRows cs).length).map
      (GenAxE.pRowE χe (ComplJ9AAxisRows.tableRows cs))).foldl (· + ·) 0) =
      ComplJ9AChipsOK.axSumP deltaF hn0 cs hn (toχ χe) := by
    rw [toQ_foldl_zero, ComplJ9AChipsOK.axSumP, ← hn, ← Fin.sum_univ_eq_sum_range
      (fun i => K6.toQ (GenAxE.pRowE χe (ComplJ9AAxisRows.tableRows cs) i)) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := toQ_pRowE χe (ComplJ9AAxisRows.tableRows cs) hn0 hn i
    rw [this]; rfl
  unfold GenAxE.pubsXE ComplJ9AChipsOK.pubsXOf AxisChipJ9.pubAXs AxisChipJ9.pubAXp
  by_cases h0 : j = 0
  · subst h0; simp only [if_true]; rw [← re_toQ, hS]
  by_cases h1 : j = 1
  · subst h1; simp only [if_neg (by omega : ¬ (1 = 0)), if_true, if_neg h0]; rw [← im_toQ, hS]
  by_cases h2 : j = 2
  · subst h2; simp only [if_neg (by omega : ¬ (2 = 0)), if_neg (by omega : ¬ (2 = 1)), if_true]
    rw [← re_toQ, hP]
  by_cases h3 : j = 3
  · subst h3; simp only [if_neg (by omega : ¬ (3 = 0)), if_neg (by omega : ¬ (3 = 1)),
      if_neg (by omega : ¬ (3 = 2)), if_true]
    rw [← im_toQ, hP]
  · simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg (by omega : ¬ (j = 0 + 1)),
      if_neg (by omega : ¬ (j = 2 + 1))]
    exact K3.toK_zero

end Axis

/-! ## 3. The split chip -/

section Split
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ASplitH
variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

theorem scanK6_eq (l : List K6) : Gen.scanK6 l =(List.scanl (· + ·) 0 l).tail := by
  have key : ∀ (l : List K6) (a : K6) (pre : List K6),
      (l.foldl (fun (st : List K6 × K6) x => (st.1 ++ [st.2 + x], st.2 + x)) (pre, a)).1 =
        pre ++ (List.scanl (· + ·) a l).tail := by
    intro l
    induction l with
    | nil => intro a pre; simp
    | cons x l ih =>
      intro a pre
      rw [List.foldl_cons, ih, List.scanl_cons, List.tail_cons]
      cases l <;> simp [List.scanl]
  unfold Gen.scanK6
  rw [key]; simp

theorem scanK6_length (l : List K6) : (Gen.scanK6 l).length = l.length := by
  rw [scanK6_eq]; simp

theorem toQ_scanK6_getD (l : List K6) (i : ℕ) (hi : i < l.length) :
    K6.toQ ((Gen.scanK6 l).getD i 0) = ∑ j ∈ Finset.range (i + 1), K6.toQ (l.getD j 0) := by
  rw [← toQ_inclSums_getD l i hi, scanK6_eq, inclSums_eq]

theorem toQ_dKeySE (χe : CoinsE) (id tag limb : ℕ) :
    K6.toQ (GenSpE.dKeyE χe id tag limb) =
      dKey4 deltaF (VerJ8.chalsMJ8 deltaF (toχ χe)) (id : ZMod p) (tag : ZMod p) 0 (limb : ZMod p) := by
  obtain ⟨h1, h2⟩ := ComplJ9AChipsOK.chals_pair deltaF (toχ χe)
  unfold GenSpE.dKeyE dKey4
  rw [toQ_compressE, toQ_γHE, toQ_ρHE, h1, h2]
  unfold FiniteIO.compress Walk.rlc
  have hz : liftQ (K := KC) deltaF (0 : ZMod p) = 0 := by
    simp [liftQ]; exact RingHom.map_zero _
  simp [Fin.sum_univ_four, FillMem.toQ_lq, K6.toQ_zero, hz, add_assoc]
  erw [mul_zero, add_zero]
  exact congrArg (HAdd.hAdd _) (add_assoc _ _ _).symm

theorem toQ_d2E (χe : CoinsE) (nA v i : ℕ) :
    K6.toQ (GenSpE.d2E χe nA v i) =
      dKey4 deltaF (VerJ8.chalsMJ8 deltaF (toχ χe)) ((nA + i : ℕ) : ZMod p) 2 0 ((v % 2 ^ 32 : ℕ) : ZMod p) := by
  unfold GenSpE.d2E; rw [toQ_dKeySE]; simp

theorem toQ_d3E (χe : CoinsE) (nA v i : ℕ) :
    K6.toQ (GenSpE.d3E χe nA v i) =
      dKey4 deltaF (VerJ8.chalsMJ8 deltaF (toχ χe)) ((nA + i : ℕ) : ZMod p) 3 0 ((v / 2 ^ 32 : ℕ) : ZMod p) := by
  unfold GenSpE.d3E; rw [toQ_dKeySE]; simp

variable (χe : CoinsE) (nA : ℕ) (vS mS : List ℕ)

theorem toQ_rowTE {n : ℕ} (hn : n = vS.length) (i : Fin n) :
    K6.toQ (GenSpE.rowTE χe nA (vS.getD i 0) (mS.getD i 0) i) =
      rowT deltaF (VerJ8.chalsMJ8 deltaF (toχ χe)) nA (fun i : Fin n => vS.getD i 0) (fun i : Fin n => mS.getD i 0) i := by
  unfold GenSpE.rowTE rowT
  rw [K6.toQ_mul, K6.toQ_add, K6.toQ_inv, K6.toQ_inv, toQ_d2E, toQ_d3E, FillMem.toQ_lq]
  rfl

theorem toQ_accSE {n : ℕ} (hn : n = vS.length) (i : Fin n) :
    K6.toQ ((GenSpE.accSE χe nA vS mS).getD i 0) =
      accS deltaF nA (VerJ8.chalsMJ8 deltaF (toχ χe)) (fun i : Fin n => vS.getD i 0) (fun i : Fin n => mS.getD i 0) i := by
  unfold GenSpE.accSE
  rw [toQ_scanK6_getD _ _ (by simp; omega)]
  unfold accS
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < n := by have := Finset.mem_range.mp hj; have := i.2; omega
  rw [tN, dif_pos hj', ← toQ_rowTE χe nA vS mS hn ⟨j, hj'⟩]
  simp [List.getD_eq_getElem?_getD, hn ▸ hj']

theorem coordN_toK'' (x : K3) (m : ℕ) : coordN powerBasis3 (K3.toK x) m = limbZ x (m % 3) := coordN_toK' x m

theorem spGenE_cols {n : ℕ} (hn : n = vS.length) (i : Fin n) (c : ℕ) (hc : c < 90) :
    ((GenSpE.spGenE χe nA vS mS).1.getD i #[]).getD c 0 =
      colS deltaF nA powerBasis3 (VerJ8.chalsMJ8 deltaF (toχ χe)) (fun i : Fin n => vS.getD i 0)
        (fun i : Fin n => mS.getD i 0) c i := by
  have hi : (i : ℕ) < vS.length := hn ▸ i.2
  unfold GenSpE.spGenE
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]
  simp only [Array.getElem?_ofFn]
  rw [dif_pos hc]
  unfold colS
  by_cases h72 : c < 72
  · simp only [if_pos h72]
    unfold GenSpE.baseSE baseS GenSpE.bitE bitV
    simp only [← hn]
    rfl
  · simp only [if_neg h72]
    have hq : ∀ s, s < 3 → qv deltaF nA (VerJ8.chalsMJ8 deltaF (toχ χe)) (fun i : Fin n => vS.getD i 0)
        (fun i : Fin n => mS.getD i 0) s i =
        K6.toQ ([(GenSpE.d2E χe nA (vS.getD i 0) i)⁻¹, (GenSpE.d3E χe nA (vS.getD i 0) i)⁻¹,
          (GenSpE.accSE χe nA vS mS).getD i 0].getD s 0) := by
      intro s hs
      interval_cases s
      · simp only [qv, List.getD_cons_zero, K6.toQ_inv, toQ_d2E]; rfl
      · simp only [qv, List.getD_cons_succ, List.getD_cons_zero, K6.toQ_inv, toQ_d3E]; rfl
      · simp only [qv, List.getD_cons_succ, List.getD_cons_zero]
        exact (toQ_accSE χe nA vS mS hn i).symm
    unfold roleV
    split_ifs with hm
    · rw [Option.getD_some, hq _ (by omega), re_toQ, coordN_toK'']
    · rw [Option.getD_some, hq _ (by omega), im_toQ, coordN_toK'']

theorem toQ_lastAcc {n : ℕ} (hn : n = vS.length) (hn0 : 0 < n) :
    K6.toQ (Gen.lastK6 (GenSpE.accSE χe nA vS mS)) =
      ComplJ9AChipsOK.spSum deltaF nA (fun i : Fin n => vS.getD i 0) (fun i : Fin n => mS.getD i 0) (toχ χe) := by
  have hlen : (GenSpE.accSE χe nA vS mS).length = n := by simp [GenSpE.accSE, scanK6_length, hn]
  have hl : Gen.lastK6 (GenSpE.accSE χe nA vS mS) = (GenSpE.accSE χe nA vS mS).getD (n - 1) 0 := by
    unfold Gen.lastK6
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hlen]
    simp [List.getD_eq_getElem?_getD]
  rw [hl, toQ_accSE χe nA vS mS hn ⟨n - 1, by omega⟩]
  unfold ComplJ9AChipsOK.spSum
  exact accS_last _ _ _ _ _ hn0

theorem pubsSE_eq {n : ℕ} (hn : n = vS.length) (hn0 : 0 < n) (j : ℕ) :
    K3.toK ((GenSpE.spGenE χe nA vS mS).2 j) =
      ComplJ9AChipsOK.pubsSOf deltaF nA (fun i : Fin n => vS.getD i 0) (fun i : Fin n => mS.getD i 0) (toχ χe) j := by
  have hT := toQ_lastAcc χe nA vS mS hn hn0
  unfold GenSpE.spGenE ComplJ9AChipsOK.pubsSOf SplitChipJ9.pubSPs
  by_cases h0 : j = 0
  · subst h0; simp only [if_true]; rw [← hT, re_toQ]
  by_cases h1 : j = 1
  · subst h1; simp only [if_neg (by omega : ¬ (1 = 0)), if_true, if_neg h0]; rw [← hT, im_toQ]
  · simp only [if_neg h0, if_neg h1, if_neg (by omega : ¬ (j = 0 + 1))]
    exact K3.toK_zero

end Split

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips
#print axioms axGenE_cols
#print axioms pubsXE_eq
#print axioms spGenE_cols
#print axioms pubsSE_eq
end Axioms

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AChips
