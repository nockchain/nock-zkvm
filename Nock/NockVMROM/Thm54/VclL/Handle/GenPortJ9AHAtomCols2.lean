/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAtomCols2.lean

  The second group of atom-chip columns of the executable data.

  * `atomGenE_size`, `dsE_getD`, `atomGenE_entry` (table access, `roles` irrelevant below `313`);
  * `ivH_eq`, `ha_eq`, `va_eq`, `xa_eq`, `qslot_eqA` (the per-row `𝕂′` values);
  * `atomGenE_cols_lo`.

  Statement note: `qslot_eqA` is against the honest FILLED row `ComplJ8Cell.valsBP … i` (the row `aCol` reads),
  not the unfilled `aRows i` (whose inverse slots are `0`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRow
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomCols1
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomKey

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRow
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomCols1
open Nock.NockVMROM.Thm54.CoordinateBasis

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomCols2

/-! ## 1. Scans (copied from `GenPortJ9AChips`, which imports `AcceptsJ9A`) -/

theorem scanK6_eq (l : List K6) : Gen.scanK6 l = (List.scanl (· + ·) 0 l).tail := by
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

theorem toQ_scanK6_getD (l : List K6) (i : ℕ) (hi : i < l.length) :
    K6.toQ ((Gen.scanK6 l).getD i 0) = ∑ j ∈ Finset.range (i + 1), K6.toQ (l.getD j 0) := by
  rw [scanK6_eq]
  have := toQ_scanl_getD l 0 i hi
  rw [K6.toQ_zero, zero_add] at this
  rw [← this]
  have e : ∀ L : List K6, L.tail.getD i 0 = L.getD (i + 1) 0 := by
    intro L; cases L <;> simp
  rw [e]

/-! ## 2. Table access -/

theorem toArray_getD {α : Type} (L : List α) (d : α) (i : ℕ) (hi : i < L.length) :
    L.toArray.getD i d = L[i] := by
  simp [Array.getD_eq_getD_getElem?, hi]

theorem ofFn_getD {α : Type} {n : ℕ} (g : Fin n → α) (c : ℕ) (hc : c < n) (d : α) :
    (Array.ofFn g).getD c d = g ⟨c, hc⟩ := by
  simp [Array.getD_eq_getD_getElem?, hc]

/-- The per-row data list of `atomGenE`. -/
abbrev dsL (pt : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) : List CellD :=
  (acsL.zipIdx 0).map fun (n, j) => cellDE pt (coOfA χe) (yE χe) acsL n j

abbrev mhArr (acsL : List Noun) (info : Array AInfo) (mhA : Array ℕ) : Array ℕ :=
  (Array.range acsL.length).map fun j => mhA.getD j 0 + (info.getD j AInfo.z).mhx

theorem dsL_length (pt : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) : (dsL pt χe acsL).length = acsL.length := by
  simp [dsL]

theorem dsE_getD (pt : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) (i : ℕ) (hi : i < acsL.length) (d : CellD) :
    (dsL pt χe acsL).getD i d = cellDE pt (coOfA χe) (yE χe) acsL acsL[i] i := by
  simp [dsL, List.getD_eq_getElem?_getD, hi]

theorem dsE_map_getD (pt : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) (g : CellD → K6) (i : ℕ)
    (hi : i < acsL.length) :
    ((dsL pt χe acsL).map g).getD i 0 = g (cellDE pt (coOfA χe) (yE χe) acsL acsL[i] i) := by
  simp [dsL, List.getD_eq_getElem?_getD, hi]

theorem atomGenE_size (pt : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) (info : Array AInfo) (mb mxA mhA : Array ℕ) :
    (atomGenE pt χe acsL info mb mxA mhA).1.size = acsL.length := by
  simp [atomGenE]

theorem infoRange_getD (info : Array AInfo) (D i : ℕ) (hi : i < D) :
    ((List.range D).map fun j => info.getD j AInfo.z).getD i AInfo.z = info.getD i AInfo.z := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- **`atomGenE_entry`**: entry `(i, c)` of the executable table is `atomColD` at row `i`'s data (some `roles`). -/
theorem atomGenE_entry (pt : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) (info : Array AInfo) (mb mxA mhA : Array ℕ)
    (i : ℕ) (hi : i < acsL.length) (c : ℕ) (hc : c < 349) :
    ∃ roles : ℕ → K3,
      ((atomGenE pt χe acsL info mb mxA mhA).1.getD i #[]).getD c 0 =
        atomColD acsL.length (mvE acsL pt) mxA (Array.replicate acsL.length 0) (mhArr acsL info mhA) (mb.getD i 0)
          (cellDE pt (coOfA χe) (yE χe) acsL acsL[i] i)
          ((Gen.scanK6 ((dsL pt χe acsL).map (vTermD (mvE acsL pt)))).getD i 0)
          ((Gen.scanK6 ((dsL pt χe acsL).map (xTermD mxA (Array.replicate acsL.length 0)))).getD i 0)
          ((Gen.scanK6 ((dsL pt χe acsL).map (hTermD (mhArr acsL info mhA)))).getD i 0)
          (info.getD i AInfo.z) roles c := by
  unfold atomGenE
  dsimp only
  rw [toArray_getD _ _ i (by simp [hi])]
  simp only [List.getElem_map, List.getElem_range]
  rw [ofFn_getD _ c hc]
  rw [dsE_getD pt χe acsL i hi, infoRange_getD info acsL.length i hi]
  exact ⟨_, rfl⟩

/-! ## 2b. Column ranges of `cellColD` (no `simp` over the whole `if` chain) -/

theorem cellColD_role (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (va xa ha : K6) (c : ℕ)
    (h1 : 134 ≤ c) (h2 : c < 230) :
    cellColD D mv mx mx1 mh d va xa ha c =
      limbZ (if ((c - 134) / 3) % 2 = 0 then (qslotD d va xa (((c - 134) / 3) / 2)).re
        else (qslotD d va xa (((c - 134) / 3) / 2)).im) ((c - 134) % 3) := by
  unfold cellColD
  rw [if_neg (show c ≠ 0 by omega), if_neg (show c ≠ 1 by omega), if_neg (show ¬ c < 129 by omega),
    if_neg (show c ≠ 129 by omega), if_neg (show ¬ c < 132 by omega), if_neg (show c ≠ 132 by omega),
    if_neg (show c ≠ 133 by omega), if_pos h2]

theorem cellColD_iv (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (va xa ha : K6) (c : ℕ)
    (h1 : 230 ≤ c) (h2 : c < 242) :
    cellColD D mv mx mx1 mh d va xa ha c =
      if c < 233 then limbZ d.ivH.re (c - 230) else if c < 236 then limbZ d.ivH.im (c - 233)
      else if c < 239 then limbZ ha.re (c - 236) else limbZ ha.im (c - 239) := by
  unfold cellColD
  rw [if_neg (show c ≠ 0 by omega), if_neg (show c ≠ 1 by omega), if_neg (show ¬ c < 129 by omega),
    if_neg (show c ≠ 129 by omega), if_neg (show ¬ c < 132 by omega), if_neg (show c ≠ 132 by omega),
    if_neg (show c ≠ 133 by omega), if_neg (show ¬ c < 230 by omega)]

theorem atomColD_role (D : ℕ) (mv mx mx1 mh : Array ℕ) (mb : ℕ) (d : CellD) (va xa ha : K6) (ai : AInfo)
    (roles : ℕ → K3) (c : ℕ) (h1 : 205 ≤ c) (h2 : c < 301) :
    atomColD D mv mx mx1 mh mb d va xa ha ai roles c = cellColD D mv mx mx1 mh d va xa ha (c - 205 + 134) := by
  unfold atomColD
  dsimp only
  rw [if_neg (show ¬ c < 130 by omega), if_neg (show ¬ c < 162 by omega), if_neg (show ¬ c < 194 by omega),
    if_neg (show c ≠ 194 by omega), if_neg (show c ≠ 195 by omega), if_neg (show c ≠ 196 by omega),
    if_neg (show c ≠ 197 by omega), if_neg (show c ≠ 198 by omega), if_neg (show c ≠ 199 by omega),
    if_neg (show c ≠ 200 by omega), if_neg (show c ≠ 201 by omega), if_neg (show c ≠ 202 by omega),
    if_neg (show c ≠ 203 by omega), if_neg (show c ≠ 204 by omega), if_pos h2]

theorem atomColD_iv (D : ℕ) (mv mx mx1 mh : Array ℕ) (mb : ℕ) (d : CellD) (va xa ha : K6) (ai : AInfo)
    (roles : ℕ → K3) (c : ℕ) (h1 : 301 ≤ c) (h2 : c < 313) :
    atomColD D mv mx mx1 mh mb d va xa ha ai roles c = cellColD D mv mx mx1 mh d va xa ha (c - 301 + 230) := by
  unfold atomColD
  dsimp only
  rw [if_neg (show ¬ c < 130 by omega), if_neg (show ¬ c < 162 by omega), if_neg (show ¬ c < 194 by omega),
    if_neg (show c ≠ 194 by omega), if_neg (show c ≠ 195 by omega), if_neg (show c ≠ 196 by omega),
    if_neg (show c ≠ 197 by omega), if_neg (show c ≠ 198 by omega), if_neg (show c ≠ 199 by omega),
    if_neg (show c ≠ 200 by omega), if_neg (show c ≠ 201 by omega), if_neg (show c ≠ 202 by omega),
    if_neg (show c ≠ 203 by omega), if_neg (show c ≠ 204 by omega), if_neg (show ¬ c < 301 by omega),
    if_pos h2]

/-! ## 3. The honest row -/

section Honest
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [instFR : Fact (ringChar (ZMod P)).Prime] [instAR : Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
  (D : ComplJ8Data.J8Data P Rg fuel s f r)

/-- The honest filled atom cell rows (what `aCol` reads). -/
noncomputable abbrev aVals (χe : CoinsE) (i : Fin D.acs.length) : CellVals (ZMod P) KQ :=
  ComplJ8Cell.valsBP deltaF (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe))
    (ComplJ8Of.zA deltaF (toχ χe)) (fun _ => none) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D) (fun _ => 0)
    (ComplJ8Of.ptA D) i

theorem coins_hz (χe : CoinsE) : K6.toQ (coOfA χe).z = ComplJ8Of.zA deltaF (toχ χe) := toQ_yE_zA χe
theorem coins_hγ (χe : CoinsE) : K6.toQ (coOfA χe).γ = ComplJ8Of.γV deltaF (toχ χe) := toQ_γVE χe
theorem coins_hρ (χe : CoinsE) : K6.toQ (coOfA χe).ρ = ComplJ8Of.ρV deltaF (toχ χe) := toQ_ρVE χe

variable (hacs : D.acs = ComplJ8Data.acsP P D.bigs D.dupP)
  (hg : ComplJ8Atom.GenHyp D.bigs D.dupP D.rows D.mb)

include hacs hg in
theorem row_atomRow (k : ℕ) (hk : k < D.acs.length) : AtomRow D.acs[k] :=
  atomRow_of_acs D.bigs D.dupP hg.big _ (hacs ▸ List.getElem_mem hk)

noncomputable abbrev aRowP (χe : CoinsE) (k : ℕ) : CellVals (ZMod P) KQ :=
  ComplJ8Cell.cellRowsBP deltaF (ComplJ8Of.zA deltaF (toχ χe)) (fun _ => none) D.acs (ComplJ8Of.mvA D)
    (ComplJ8Of.mxAF D) (fun _ => 0) (ComplJ8Of.ptA D) k

theorem aVals_eq (χe : CoinsE) (k : ℕ) (hk : k < D.acs.length) :
    ComplJ8Cell.cellRowsBP deltaF (ComplJ8Of.zA deltaF (toχ χe)) (fun _ => none) D.acs (ComplJ8Of.mvA D)
      (ComplJ8Of.mxAF D) (fun _ => 0) (ComplJ8Of.ptA D) k =
    RB (ComplJ8Of.zA deltaF (toχ χe)) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D) (ComplJ8Of.ptA D) D.acs[k] k :=
  ComplJ8Cell.cellRowsBP_getElem _ _ _ _ _ _ _ hk

include hacs hg in
theorem toQ_vTermD_D (χe : CoinsE) (k : ℕ) (hk : k < D.acs.length) :
    K6.toQ (vTermD (mvE D.acs (ComplJ8Data.ptrP P D.acs D.rows))
        (cellDE (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs D.acs[k] k)) =
      vTermOf deltaF (cellFillInv deltaF (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe))
        (ComplJ8Cell.cellRowsBP deltaF (ComplJ8Of.zA deltaF (toχ χe)) (fun _ => none) D.acs (ComplJ8Of.mvA D)
          (ComplJ8Of.mxAF D) (fun _ => 0) (ComplJ8Of.ptA D) k)) := by
  rw [aVals_eq D χe k hk]
  exact toQ_vTermD _ _ _ _ _ _ _ _ _ _ _ (coins_hz χe) (coins_hγ χe) (coins_hρ χe) (row_atomRow D hacs hg k hk) _
    (mvE_getD_mvA D hk)

include hacs hg in
theorem toQ_xTermD_D (χe : CoinsE) (k : ℕ) (hk : k < D.acs.length) :
    K6.toQ (xTermD D.mxA (Array.replicate D.acs.length 0)
        (cellDE (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs D.acs[k] k)) =
      xTermOf deltaF (cellFillInv deltaF (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe))
        (ComplJ8Cell.cellRowsBP deltaF (ComplJ8Of.zA deltaF (toχ χe)) (fun _ => none) D.acs (ComplJ8Of.mvA D)
          (ComplJ8Of.mxAF D) (fun _ => 0) (ComplJ8Of.ptA D) k)) := by
  rw [aVals_eq D χe k hk]
  exact toQ_xTermD _ _ _ _ _ _ _ _ _ _ _ (coins_hz χe) (coins_hγ χe) (coins_hρ χe) (row_atomRow D hacs hg k hk) _ _
    rfl (replicate_getD _ _)

include hacs hg in
/-- The `v` accumulator. -/
theorem va_eq (χe : CoinsE) (i : Fin D.acs.length) :
    K6.toQ ((Gen.scanK6 ((dsL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs).map
      (vTermD (mvE D.acs (ComplJ8Data.ptrP P D.acs D.rows))))).getD i 0) = (aVals D χe i).vAcc := by
  rw [toQ_scanK6_getD _ _ (by simp [dsL_length])]
  show _ = ∑ k ∈ Finset.range ((i : ℕ) + 1), vTermOf deltaF (cellFillInv deltaF _ _ (ComplJ8Cell.cellRowsBP _ _ _ _ _ _ _ _ k))
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < D.acs.length := by have := Finset.mem_range.mp hk; have := i.2; omega
  rw [dsE_map_getD _ _ _ _ k hk']
  exact toQ_vTermD_D D hacs hg χe k hk'

include hacs hg in
/-- The `x` accumulator. -/
theorem xa_eq (χe : CoinsE) (i : Fin D.acs.length) :
    K6.toQ ((Gen.scanK6 ((dsL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs).map
      (xTermD D.mxA (Array.replicate D.acs.length 0)))).getD i 0) = (aVals D χe i).xAcc := by
  rw [toQ_scanK6_getD _ _ (by simp [dsL_length])]
  show _ = ∑ k ∈ Finset.range ((i : ℕ) + 1), xTermOf deltaF (cellFillInv deltaF _ _ (ComplJ8Cell.cellRowsBP _ _ _ _ _ _ _ _ k))
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < D.acs.length := by have := Finset.mem_range.mp hk; have := i.2; omega
  rw [dsE_map_getD _ _ _ _ k hk']
  exact toQ_xTermD_D D hacs hg χe k hk'

include hacs hg in
/-- **`qslot_eqA`**: the executable `𝕂′` slots of row `i` are the honest filled row's. -/
theorem qslot_eqA (χe : CoinsE) (i : Fin D.acs.length) (s : ℕ) (hs : s < 16) :
    K6.toQ (qslotD (cellDE (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs D.acs[i] i)
      ((Gen.scanK6 ((dsL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs).map
        (vTermD (mvE D.acs (ComplJ8Data.ptrP P D.acs D.rows))))).getD i 0)
      ((Gen.scanK6 ((dsL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs).map
        (xTermD D.mxA (Array.replicate D.acs.length 0)))).getD i 0) s) = (aVals D χe i).qslot s := by
  have hn := row_atomRow D hacs hg i i.2
  have hz := coins_hz χe
  have hγ := coins_hγ χe
  have hρ := coins_hρ χe
  have pE := toQ_pE_d (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D)
    D.acs[(i : ℕ)] i _ hz (row_atomRow D hacs hg i i.2)
  have lE := toQ_lE_d (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D)
    D.acs[(i : ℕ)] i _ hz (row_atomRow D hacs hg i i.2)
  have rE := toQ_rE_d (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D)
    D.acs[(i : ℕ)] i _ hz (row_atomRow D hacs hg i i.2)
  have hv := toQ_vInv (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D)
    D.acs[(i : ℕ)] i _ _ _ hz hγ hρ (row_atomRow D hacs hg i i.2)
  have hl := toQ_lInv (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D)
    D.acs[(i : ℕ)] i _ _ _ hz hγ hρ (row_atomRow D hacs hg i i.2)
  have hr := toQ_rInv (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D)
    D.acs[(i : ℕ)] i _ _ _ hz hγ hρ (row_atomRow D hacs hg i i.2)
  have h0 := toQ_x0Inv (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D)
    D.acs[(i : ℕ)] i _ _ _ hz hγ hρ (row_atomRow D hacs hg i i.2)
  have h1 := toQ_x1Inv (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D)
    D.acs[(i : ℕ)] i _ _ _ hz hγ hρ (row_atomRow D hacs hg i i.2)
  have e : aRowP D χe i =
      RB (ComplJ8Of.zA deltaF (toχ χe)) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D) (ComplJ8Of.ptA D)
        D.acs[(i : ℕ)] i := aVals_eq D χe i i.2
  have hva := va_eq D hacs hg χe i
  have hxa := xa_eq D hacs hg χe i
  have hP := congrArg ComputeTable.FP.size pE
  have hP2 := congrArg ComputeTable.FP.dyck pE
  have hP3 := congrArg ComputeTable.FP.leaf pE
  have hL := congrArg ComputeTable.FP.size lE
  have hL2 := congrArg ComputeTable.FP.dyck lE
  have hL3 := congrArg ComputeTable.FP.leaf lE
  have hR := congrArg ComputeTable.FP.size rE
  have hR2 := congrArg ComputeTable.FP.dyck rE
  have hR3 := congrArg ComputeTable.FP.leaf rE
  interval_cases s
  · show _ = (aRowP D χe i).p.size
    rw [e]; exact hP
  · show _ = (aRowP D χe i).p.dyck
    rw [e]; exact hP2
  · show _ = (aRowP D χe i).p.leaf
    rw [e]; exact hP3
  · show _ = (aRowP D χe i).l.size
    rw [e]; exact hL
  · show _ = (aRowP D χe i).l.dyck
    rw [e]; exact hL2
  · show _ = (aRowP D χe i).l.leaf
    rw [e]; exact hL3
  · show _ = (aRowP D χe i).r.size
    rw [e]; exact hR
  · show _ = (aRowP D χe i).r.dyck
    rw [e]; exact hR2
  · show _ = (aRowP D χe i).r.leaf
    rw [e]; exact hR3
  · show _ = (cellFillInv deltaF _ _ (aRowP D χe i)).vInv
    rw [e]; exact hv
  · show _ = (cellFillInv deltaF _ _ (aRowP D χe i)).lInv
    rw [e]; exact hl
  · show _ = (cellFillInv deltaF _ _ (aRowP D χe i)).rInv
    rw [e]; exact hr
  · show _ = (cellFillInv deltaF _ _ (aRowP D χe i)).x0Inv
    rw [e]; exact h0
  · exact hva
  · exact hxa
  · show _ = (cellFillInv deltaF _ _ (aRowP D χe i)).x1Inv
    rw [e]; exact h1

/-! ## 4. `ivH` and the handle accumulator -/

theorem cellDE_ivH_cell (pt : Noun → ℕ) (k : Co) (y : K6) (cs : List Noun) (n : Noun) (j : ℕ)
    (hr : (tlN' n).isCell = true) : (cellDE pt k y cs n j).ivH =
    (compressE k.γH k.ρH ![lq j, (Gen.hK (Gen.hdl cs) (hdN' n)).1, (Gen.hK (Gen.hdl cs) (hdN' n)).2, lq 1, lq (pt n)])⁻¹ := by
  unfold cellDE; dsimp only; rw [if_pos hr]; rfl

theorem cellDE_ivH_atom (pt : Noun → ℕ) (k : Co) (y : K6) (cs : List Noun) (n : Noun) (j : ℕ)
    (hr : (tlN' n).isCell = false) : (cellDE pt k y cs n j).ivH =
    (compressE k.γH k.ρH ![lq j, (Gen.hK (Gen.hdl cs) (hdN' n)).1, (Gen.hK (Gen.hdl cs) (hdN' n)).2,
      (Gen.hK (Gen.hdl cs) (tlN' n)).1, (Gen.hK (Gen.hdl cs) (tlN' n)).2])⁻¹ := by
  unfold cellDE; dsimp only; rw [if_neg (by simp [hr])]; rfl

theorem toQ_compressH (γ ρ : K6) (v : Fin 5 → K6) (w : Fin 5 → KQ) (hw : ∀ c, K6.toQ (v c) = w c) :
    K6.toQ (compressE γ ρ v) = K6.toQ ρ + FiniteIO.compress (m := 5) (⟨K6.toQ γ, 0⟩ : FiniteIO.IOCoins KQ) w := by
  rw [toQ_compressE]
  have : (fun c => K6.toQ (v c)) = w := funext hw
  rw [this]; simp [FiniteIO.compress]

theorem toQ_compressH' (γ ρ : K6) (γ' ρ' : KQ) (hγ : K6.toQ γ = γ') (hρ : K6.toQ ρ = ρ') (v : Fin 5 → K6)
    (w : Fin 5 → KQ) (hw : ∀ c, K6.toQ (v c) = w c) :
    K6.toQ (compressE γ ρ v) = ρ' + FiniteIO.compress (m := 5) (⟨γ', 0⟩ : FiniteIO.IOCoins KQ) w := by
  rw [← hγ, ← hρ]; exact toQ_compressH γ ρ v w hw

theorem hK_atom (cs : List Noun) {v : ℕ} (h : v < P) : Gen.hK (Gen.hdl cs) (.atom v) = (lq 0, lq v) := by
  unfold Gen.hK; rw [hdl_small cs h]

include hacs hg instFR instAR in
/-- **`ivH_eq`**: the executable handle inverse of row `i` is the honest `ivF`. -/
theorem ivH_eq (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (pubs : ℕ → KC) (i : Fin D.acs.length) :
    K6.toQ (cellDE (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs D.acs[(i : ℕ)] i).ivH =
      CellTraceHQ.ivF deltaF powerBasis3 hA (ComplJ8Of.powN o _) o (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) pubs
        (ComplJ8Of.aCol deltaF powerBasis3 D (toχ χe)) (ComplJ8Of.mhvA D) i := by
  have hn := row_atomRow D hacs hg i i.2
  obtain ⟨a, t, he, ha, ht⟩ := hn.shape
  have hRow : ComplJ8Of.aRows deltaF D (toχ χe) i =
      RB (ComplJ8Of.zA deltaF (toχ χe)) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D) (ComplJ8Of.ptA D)
        D.acs[(i : ℕ)] i := aVals_eq D χe i i.2
  have hH : hdN' D.acs[(i : ℕ)] = .atom a := by rw [he]; rfl
  have hT : tlN' D.acs[(i : ℕ)] = t := by rw [he]; rfl
  have hKa : Gen.hK (Gen.hdl D.acs) (hdN' D.acs[(i : ℕ)]) = (lq 0, lq a) := by rw [hH]; exact hK_atom _ ha
  have e1 : K6.toQ (coOfA χe).γH = ComplJ8Bad.γH deltaF (toχ χe) := toQ_γHE χe
  have e2 : K6.toQ (coOfA χe).ρH = ComplJ8Bad.ρH deltaF (toχ χe) := toQ_ρHE χe
  have hidx := RB_idx (ComplJ8Of.zA deltaF (toχ χe)) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D)
    (ComplJ8Of.ptA D) D.acs[(i : ℕ)] i
  have hwL := RB_wL (ComplJ8Of.zA deltaF (toχ χe)) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D)
    (ComplJ8Of.ptA D) D.acs[(i : ℕ)] i hn
  have haL := RB_aL (ComplJ8Of.zA deltaF (toχ χe)) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D)
    (ComplJ8Of.ptA D) D.acs[(i : ℕ)] i hn
  unfold CellTraceHQ.ivF
  rw [GenPortJ9AHAtomKey.aRow_closed deltaF powerBasis3 D hA o hinj (toχ χe) pubs i, hRow]
  by_cases hr : (tlN' D.acs[(i : ℕ)]).isCell = true
  · have hwR := RB_wR_cell (ComplJ8Of.zA deltaF (toχ χe)) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D)
      (ComplJ8Of.ptA D) D.acs[(i : ℕ)] i hr
    have hid := RB_idR_cell (ComplJ8Of.zA deltaF (toχ χe)) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D)
      (ComplJ8Of.ptA D) D.acs[(i : ℕ)] i hr
    rw [cellDE_ivH_cell _ _ _ _ _ _ hr, K6.toQ_inv]
    refine congrArg Inv.inv ?_
    refine toQ_compressH' _ _ _ _ e1 e2 _ _ ?_
    intro c
    fin_cases c
    · show K6.toQ (lq _) = algebraMap KC KQ (algebraMap (ZMod P) KC _)
      rw [toQ_lq, hidx]; rfl
    · show K6.toQ (Gen.hK (Gen.hdl D.acs) (hdN' D.acs[(i : ℕ)])).1 = _
      rw [hKa]
      show K6.toQ (lq 0) = algebraMap KC KQ (algebraMap (ZMod P) KC _)
      rw [toQ_lq, hwL]; simp [liftQ]; rfl
    · show K6.toQ (Gen.hK (Gen.hdl D.acs) (hdN' D.acs[(i : ℕ)])).2 = _
      rw [hKa]
      show K6.toQ (lq a) = algebraMap KC KQ (algebraMap (ZMod P) KC _)
      rw [toQ_lq, hwL, haL]; simp [liftQ, hH, atomV]; rfl
    · show K6.toQ (lq 1) = algebraMap KC KQ (algebraMap (ZMod P) KC _)
      rw [toQ_lq, hwR]; simp [liftQ]; rfl
    · show K6.toQ (lq _) = algebraMap KC KQ (algebraMap (ZMod P) KC _)
      rw [toQ_lq, hwR, hid]; simp [liftQ]; rfl
  · have hrf : (tlN' D.acs[(i : ℕ)]).isCell = false := by simpa using hr
    have hr' := hrf
    rw [hT] at hr'
    cases t with
    | cell x y => simp [Noun.isCell] at hr'
    | atom v =>
      have hv : v < P := ht
      have hKt : Gen.hK (Gen.hdl D.acs) (tlN' D.acs[(i : ℕ)]) = (lq 0, lq v) := by
        rw [hT]; exact hK_atom _ hv
      have hwR := RB_wR_atom (ComplJ8Of.zA deltaF (toχ χe)) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D)
        (ComplJ8Of.ptA D) D.acs[(i : ℕ)] i hrf
      have haR := RB_aR (ComplJ8Of.zA deltaF (toχ χe)) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D)
        (ComplJ8Of.ptA D) D.acs[(i : ℕ)] i hn
      rw [cellDE_ivH_atom _ _ _ _ _ _ hrf, K6.toQ_inv]
      refine congrArg Inv.inv ?_
      refine toQ_compressH' _ _ _ _ e1 e2 _ _ ?_
      intro c
      fin_cases c
      · show K6.toQ (lq _) = algebraMap KC KQ (algebraMap (ZMod P) KC _)
        rw [toQ_lq, hidx]; rfl
      · show K6.toQ (Gen.hK (Gen.hdl D.acs) (hdN' D.acs[(i : ℕ)])).1 = _
        rw [hKa]
        show K6.toQ (lq 0) = algebraMap KC KQ (algebraMap (ZMod P) KC _)
        rw [toQ_lq, hwL]; simp [liftQ]; rfl
      · show K6.toQ (Gen.hK (Gen.hdl D.acs) (hdN' D.acs[(i : ℕ)])).2 = _
        rw [hKa]
        show K6.toQ (lq a) = algebraMap KC KQ (algebraMap (ZMod P) KC _)
        rw [toQ_lq, hwL, haL]; simp [liftQ, hH, atomV]; rfl
      · show K6.toQ (Gen.hK (Gen.hdl D.acs) (tlN' D.acs[(i : ℕ)])).1 = _
        rw [hKt]
        show K6.toQ (lq 0) = algebraMap KC KQ (algebraMap (ZMod P) KC _)
        rw [toQ_lq, hwR]; simp [liftQ]; rfl
      · rw [hKt]
        show K6.toQ (lq v) = algebraMap KC KQ (algebraMap (ZMod P) KC _)
        rw [toQ_lq, hwR, haR]; simp [liftQ, hT, atomV]; rfl

include hacs hg instFR instAR in
/-- **`ha_eq`**: the executable handle accumulator of row `i` is the honest `avF`. -/
theorem ha_eq (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (pubs : ℕ → KC) (i : Fin D.acs.length) :
    K6.toQ ((Gen.scanK6 ((dsL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs).map
      (hTermD (mhArr D.acs D.info D.mhA)))).getD i 0) =
      CellTraceHQ.avF deltaF powerBasis3 hA (ComplJ8Of.powN o _) o (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) pubs
        (ComplJ8Of.aCol deltaF powerBasis3 D (toχ χe)) (ComplJ8Of.mhvA D) i := by
  rw [toQ_scanK6_getD _ _ (by simp [dsL_length])]
  unfold CellTraceHQ.avF
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < D.acs.length := by have := Finset.mem_range.mp hk; have := i.2; omega
  rw [dsE_map_getD _ _ _ _ k hk', toQ_hTermD _ _ _ _ _ _ _ (ComplJ8Of.mhAF D k) (mh_getD D hk'),
    ivH_eq D hacs hg χe hA o hinj pubs ⟨k, hk'⟩]
  have hm : CellTraceH.mN (ComplJ8Of.mhvA D) k = (ComplJ8Of.mhAF D k : ZMod P) := by
    simp [CellTraceH.mN, hk', ComplJ8Of.mhvA]
  rw [hm]
  simp [CellTraceHQ.dN, hk', CellTraceHQ.ivF]
  try rfl

include hacs hg instFR instAR in
/-- **`atomGenE_cols_lo`**: columns `0 .. 312` of the executable atom table are the honest `fullCol` of
`HonestA8.colA` at any orbit with injective `powN`. -/
theorem atomGenE_cols_lo (hinfo : D.info = ComplJ8Data.infoOfP P D.acs D.rows) (χe : CoinsE)
    (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (i : Fin D.acs.length) (c : ℕ) (hc : c < 313) :
    ((atomGenE (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs D.info D.mb D.mxA D.mhA).1.getD i #[]).getD c 0 =
      fullCol hA (HonestA8.colA deltaF powerBasis3 hA (ComplJ8Of.powN o _) o (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
        (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe))
        (ComplJ8Of.colAH deltaF powerBasis3 D hA o (toχ χe) (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe)))
        (ComplJ8Of.newBA D)) c i := by
  obtain ⟨roles, he⟩ := atomGenE_entry (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs D.info D.mb D.mxA D.mhA i i.2 c
    (by omega)
  rw [he]
  have hd := cellDE_j (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs D.acs[(i : ℕ)] i
  by_cases h0 : c = 0
  · subst h0
    simp only [fullCol, if_pos rfl]
    unfold atomColD; rw [if_pos (by norm_num)]; unfold cellColD; rw [if_pos rfl, hd]
    by_cases hi0 : (i : ℕ) = 0 <;> simp [flag, hi0]
  by_cases h1 : c = 1
  · subst h1
    simp only [fullCol, if_neg (show (1 : ℕ) ≠ 0 by norm_num), if_pos rfl]
    unfold atomColD; rw [if_pos (by norm_num)]; unfold cellColD; rw [if_neg (by norm_num), if_pos rfl, hd]
    have hfi : (i = ⟨D.acs.length - 1, Nat.sub_lt hA (by omega)⟩) ↔ ((i : ℕ) + 1 = D.acs.length) := by
      rw [Fin.ext_iff]; simp; omega
    simp only [hfi]
    by_cases hl : (i : ℕ) + 1 = D.acs.length <;> simp [flag, hl]
  simp only [fullCol, if_neg h0, if_neg h1, HonestA8.colA, extColF, CellTraceHQ.cellTemplateHQ_width]
  by_cases hb : c < 130
  · rw [if_pos hb]
    by_cases h129 : c = 129
    · subst h129
      refine (atom129 D χe i _ _ _ _ roles).trans ?_
      simp [ComplJ8Of.colAH, CellTraceHQ.colHQ, extColF, CellTraceHQ.new]
    · have hc129 : c < 129 := by omega
      refine (atomBase_eq D hacs hg χe (ComplJ8Of.zA deltaF (toχ χe)) i _ _ _ _ _ roles c (by omega) hc129).trans ?_
      simp only [ComplJ8Of.colAH, CellTraceHQ.colHQ, extColF, if_pos hc129, if_pos hb, ComplJ8Of.aCol, cellCol]
      rfl
  rw [if_neg hb]
  by_cases h205 : c < 205
  · rw [if_pos h205]
    refine (atomNew_eq D hacs hinfo hg χe i _ _ _ _ roles c (by omega) h205).trans ?_
    unfold HonestA8.newFull
    rw [if_pos hc]
  rw [if_neg h205, if_pos (show c < 238 + (205 - 130) by omega)]
  by_cases h301 : c < 301
  · rw [atomColD_role _ _ _ _ _ _ _ _ _ _ _ _ c (by omega) h301,
      cellColD_role _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
    simp only [ComplJ8Of.colAH, CellTraceHQ.colHQ, extColF, CellTraceH.cellTemplate_width,
      if_neg (show ¬ c - (205 - 130) < 129 by omega), if_neg (show ¬ c - (205 - 130) < 130 by omega),
      if_pos (show c - (205 - 130) < 225 + (130 - 129) by omega), ComplJ8Of.aCol, cellCol,
      if_neg (show ¬ c - (205 - 130) - (130 - 129) < 129 by omega)]
    have e1 : c - (205 - 130) - (130 - 129) - 129 = c - 205 := by omega
    have e2 : c - 205 + 134 - 134 = c - 205 := by omega
    simp only [e1, e2]
    unfold roleVal
    have hq := qslot_eqA D hacs hg χe i ((c - 205) / 3 / 2) (by omega)
    rw [← hq]
    split_ifs
    · rw [re_toQ, coord_K]; rfl
    · rw [im_toQ, coord_K]; rfl
  · rw [atomColD_iv _ _ _ _ _ _ _ _ _ _ _ _ c (by omega) hc]
    simp only [ComplJ8Of.colAH, CellTraceHQ.colHQ, extColF, CellTraceH.cellTemplate_width,
      if_neg (show ¬ c - (205 - 130) < 129 by omega), if_neg (show ¬ c - (205 - 130) < 130 by omega),
      if_neg (show ¬ c - (205 - 130) < 225 + (130 - 129) by omega)]
    rw [cellColD_iv _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
    have hiv := ivH_eq D hacs hg χe hA o hinj (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe)) i
    have hha := ha_eq D hacs hg χe hA o hinj (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe)) i
    simp only [CellTraceHQ.new, if_neg (show c - (205 - 130) ≠ 129 by omega)]
    by_cases a1 : c < 304
    · rw [if_pos (show c - 301 + 230 < 233 by omega),
        if_pos (show 226 ≤ c - (205 - 130) ∧ c - (205 - 130) < 229 from ⟨by omega, by omega⟩),
        ← hiv, coordN_toQ_re, Nat.mod_eq_of_lt (by omega), show c - (205 - 130) - 226 = c - 301 by omega,
        show c - 301 + 230 - 230 = c - 301 by omega]
      try rfl
    by_cases a2 : c < 307
    · rw [if_neg (show ¬ c - 301 + 230 < 233 by omega), if_pos (show c - 301 + 230 < 236 by omega),
        if_neg (show ¬ (226 ≤ c - (205 - 130) ∧ c - (205 - 130) < 229) by omega),
        if_pos (show 229 ≤ c - (205 - 130) ∧ c - (205 - 130) < 232 from ⟨by omega, by omega⟩),
        ← hiv, coordN_toQ_im, Nat.mod_eq_of_lt (by omega), show c - (205 - 130) - 229 = c - 304 by omega,
        show c - 301 + 230 - 233 = c - 304 by omega]
    by_cases a3 : c < 310
    · rw [if_neg (show ¬ c - 301 + 230 < 233 by omega), if_neg (show ¬ c - 301 + 230 < 236 by omega),
        if_pos (show c - 301 + 230 < 239 by omega),
        if_neg (show ¬ (226 ≤ c - (205 - 130) ∧ c - (205 - 130) < 229) by omega),
        if_neg (show ¬ (229 ≤ c - (205 - 130) ∧ c - (205 - 130) < 232) by omega),
        if_pos (show 232 ≤ c - (205 - 130) ∧ c - (205 - 130) < 235 from ⟨by omega, by omega⟩),
        ← hha, coordN_toQ_re, Nat.mod_eq_of_lt (by omega), show c - (205 - 130) - 232 = c - 307 by omega,
        show c - 301 + 230 - 236 = c - 307 by omega]
    · rw [if_neg (show ¬ c - 301 + 230 < 233 by omega), if_neg (show ¬ c - 301 + 230 < 236 by omega),
        if_neg (show ¬ c - 301 + 230 < 239 by omega),
        if_neg (show ¬ (226 ≤ c - (205 - 130) ∧ c - (205 - 130) < 229) by omega),
        if_neg (show ¬ (229 ≤ c - (205 - 130) ∧ c - (205 - 130) < 232) by omega),
        if_neg (show ¬ (232 ≤ c - (205 - 130) ∧ c - (205 - 130) < 235) by omega),
        if_pos (show 235 ≤ c - (205 - 130) ∧ c - (205 - 130) < 238 from ⟨by omega, by omega⟩),
        ← hha, coordN_toQ_im, Nat.mod_eq_of_lt (by omega), show c - (205 - 130) - 235 = c - 310 by omega,
        show c - 301 + 230 - 239 = c - 310 by omega]

end Honest

#print axioms scanK6_eq
#print axioms toQ_scanK6_getD
#print axioms atomGenE_size
#print axioms dsE_getD
#print axioms atomGenE_entry
#print axioms qslot_eqA
#print axioms ivH_eq
#print axioms ha_eq
#print axioms va_eq
#print axioms xa_eq
#print axioms atomGenE_cols_lo

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomCols2
