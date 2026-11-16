/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHAluE.lean

  **Honest link, part 2: the executable ALU chip is accepted** (`ALChipOK`, present
  branch) at the verifier parameters `mkPbAL I hv` of an abstract input `I : InJ9AL` whose ALU chip is the
  executable `aluGenE` table (`hL`, `hpL`).
  * §1 the coin: `K6.toQ (yE χe) = yOf δ (toχ χe)`;
  * §2 the executable rows: `aluGenE`'s table row `i < N` is `colsE ++ roleLimbs rolesE` (`aluGenE_getD`);
  * §3 the columns: every column `c < 196`, row `i < N` of the executable table is the honest
    `fullCol (colAL (tbE …) (r2AL …))` (`aluGenE_cols`), N = `3·2^h` (no extra padding argument: rows past the
    honest table are `padRow` / `QRow.zero` on both sides, by `getD`);
  * §4 the publics: `pubALv/s/x` are `Σ_{i : Fin N} tV/tS/tX` (`aluGenE_pubV/S/X`);
  * §5 (e) `preL`: the verifier's `pregCol` interpolant is `preLOf` of the honest table (`preL_eq_preLOf`);
  * §6 (f) `alChipOK_exec`: `ALChipOK … true …` at the executable chip.

  Design calls : (i) the ALU orbit must be FULL, `I.AL.n = 3·2^{I.AL.h}` (`hfull`): the ALU's next-row gates
  are unguarded and the executable trace is the plain interpolant, so the last row's successor must be row `0`
  (`AluTraceFix.fixAt` is then the identity); the generator's own orbit is full (`N = 3·2^{hOf n0}`); an
  `OrbAdmL` for L4 must keep it so.  (ii) The pole hypothesis is the honest `hden` at `n = N` (from `famAL` at `N`
  by `AluPoles.hden_of_famAL`); the record's `famAL` is at `aluLen + 1` rows (risk 2), bridged in L4.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAlu
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSatRun
import Nock.V1J9AL.CheckJ9ALIff
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrb
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAlu
open Nock.V1J9AL.GenAluE
open Nock.Jet.Prim (PrimOp)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (chalsALJ8)
open Polynomial
open Nock.V1J8.Check
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (fullCol honestQ)

noncomputable section

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-! ## 1. The limb coin -/

theorem toQ_yE_yOf (χe : CoinsE) : K6.toQ (yE χe) = AluPoles.yOf deltaF (toχ χe) := by
  rw [AluPoles.yOf, ← ChalsAZJ8.chalsAJ8Z_y deltaF (toχ χe)]
  rfl

/-! ## 2. The executable rows -/

section Rows

/-- The executable row count. -/
abbrev NE (pregs : List (BRow (ZMod p))) (cls : List CallL) : ℕ :=
  3 * 2 ^ Nock.V1J8.Gen.hOf (aluRowsB p pregs cls).length

/-- The executable LogUp lane of row `i`. -/
abbrev lrE (χe : CoinsE) (pregs : List (BRow (ZMod p))) (cls : List CallL) (i : ℕ) :
    K6 × K6 × K6 × K6 × K6 × K6 × K6 × K6 :=
  laneRow χe (rbE pregs cls i) (rqE χe pregs cls i)

/-- The executable lane, as `aluGenE`'s `lr`. -/
abbrev lrL (χe : CoinsE) (pregs : List (BRow (ZMod p))) (cls : List CallL) :
    List (K6 × K6 × K6 × K6 × K6 × K6 × K6 × K6) :=
  (List.range (NE pregs cls)).map fun i => lrE χe pregs cls i

/-- The three executable prefix-sum columns. -/
abbrev accVE (χe : CoinsE) (pregs : List (BRow (ZMod p))) (cls : List CallL) : List K6 :=
  Nock.V1J9A.GenAxE.inclSums ((lrL χe pregs cls).map fun x => x.1)
abbrev accSE (χe : CoinsE) (pregs : List (BRow (ZMod p))) (cls : List CallL) : List K6 :=
  Nock.V1J9A.GenAxE.inclSums ((lrL χe pregs cls).map fun x => x.2.1)
abbrev accXE (χe : CoinsE) (pregs : List (BRow (ZMod p))) (cls : List CallL) : List K6 :=
  Nock.V1J9A.GenAxE.inclSums ((lrL χe pregs cls).map fun x => x.2.2.1)

/-- `aluGenE`'s row function (base columns, then the role limbs). -/
def rowF (χe : CoinsE) (pregs : List (BRow (ZMod p))) (cls : List CallL) :
    ℕ × (K6 × K6 × K6 × K6 × K6 × K6 × K6 × K6) → Array (ZMod p) := fun (i, x) =>
  let b := rbE pregs cls i
  let cols94 := (List.range 94).map fun j =>
    if j = 0 then (if i = 0 then (1 : ZMod p) else 0)
    else if j = 1 then (if i + 1 = NE pregs cls then (1 : ZMod p) else 0)
    else b.col j
  let q := rqE χe pregs cls i
  let roles : List K6 := [q.H, q.HO, q.L, q.D1, q.D2, q.S1, q.S2, q.RL, q.RO, x.2.2.2.1, x.2.2.2.2.1,
    x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, (accVE χe pregs cls).getD i 0, (accSE χe pregs cls).getD i 0,
    (accXE χe pregs cls).getD i 0]
  (cols94 ++ Nock.V1J9A.GenAxE.roleLimbs roles).toArray

theorem aluGenE_fst (χe : CoinsE) (cs : List Noun) (Hm : Noun → ℕ × ℕ) (ps : List (ℕ × PrimOp)) (ids : List ℕ)
    (pc : List (ℕ × Noun × Noun)) :
    (aluGenE χe cs Hm ps ids pc).1 =
      ((List.range (NE (pregsOf cs ps ids) (callsLOf cs Hm ps pc))).zip
        (lrL χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc))).toArray.map
        (rowF χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc)) := rfl

/-- The base columns of row `i`. -/
def colsE (pregs : List (BRow (ZMod p))) (cls : List CallL) (i : ℕ) : List (ZMod p) :=
  (List.range 94).map fun j =>
    if j = 0 then (if i = 0 then (1 : ZMod p) else 0)
    else if j = 1 then (if i + 1 = NE pregs cls then (1 : ZMod p) else 0)
    else (rbE pregs cls i).col j

/-- The seventeen `K6` roles of row `i`. -/
def rolesE (χe : CoinsE) (pregs : List (BRow (ZMod p))) (cls : List CallL) (i : ℕ) : List K6 :=
  rolesQ (rqE χe pregs cls i) ++
    [(lrE χe pregs cls i).2.2.2.1, (lrE χe pregs cls i).2.2.2.2.1, (lrE χe pregs cls i).2.2.2.2.2.1,
      (lrE χe pregs cls i).2.2.2.2.2.2.1, (lrE χe pregs cls i).2.2.2.2.2.2.2, (accVE χe pregs cls).getD i 0,
      (accSE χe pregs cls).getD i 0, (accXE χe pregs cls).getD i 0]

theorem rowF_eq (χe : CoinsE) (pregs : List (BRow (ZMod p))) (cls : List CallL) (i : ℕ) :
    rowF χe pregs cls (i, lrE χe pregs cls i) =
      (colsE pregs cls i ++ Nock.V1J9A.GenAxE.roleLimbs (rolesE χe pregs cls i)).toArray := rfl

theorem aluGenE_size (χe : CoinsE) (cs : List Noun) (Hm : Noun → ℕ × ℕ) (ps : List (ℕ × PrimOp)) (ids : List ℕ)
    (pc : List (ℕ × Noun × Noun)) :
    (aluGenE χe cs Hm ps ids pc).1.size = NE (pregsOf cs ps ids) (callsLOf cs Hm ps pc) := by
  rw [aluGenE_fst]
  simp [List.length_zip]

theorem aluGenE_getD (χe : CoinsE) (cs : List Noun) (Hm : Noun → ℕ × ℕ) (ps : List (ℕ × PrimOp)) (ids : List ℕ)
    (pc : List (ℕ × Noun × Noun)) (i : ℕ) (hi : i < NE (pregsOf cs ps ids) (callsLOf cs Hm ps pc)) :
    (aluGenE χe cs Hm ps ids pc).1.getD i #[] =
      (colsE (pregsOf cs ps ids) (callsLOf cs Hm ps pc) i ++
        Nock.V1J9A.GenAxE.roleLimbs (rolesE χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc) i)).toArray := by
  rw [aluGenE_fst, ← rowF_eq]
  have hz : ((List.range (NE (pregsOf cs ps ids) (callsLOf cs Hm ps pc))).zip
      (lrL χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc)))[i]? =
      some (i, lrE χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc) i) :=
    List.getElem?_zip_eq_some.mpr ⟨by simp [hi], by simp [hi]⟩
  simp [Array.getD_eq_getD_getElem?, hz]

end Rows

/-! ## 3. The columns -/

section Cols

variable (χe : CoinsE) (pregs : List (BRow (ZMod p))) (cls : List CallL)

local notation "TB" => tbE (yE χe) pregs cls
local notation "CH" => chalsALJ8 deltaF (toχ χe)

theorem NE_pos : 0 < NE pregs cls := by positivity

/-- The honest round-2 `𝕂′` value `s` of row `i` is `toQ` of the executable role `9 + s`. -/
theorem qv2_eq (s : ℕ) (hs : s < 8) (i : ℕ) (hi : i < NE pregs cls) :
    qv2 (n := NE pregs cls) deltaF CH TB s ⟨i, hi⟩ = K6.toQ ((rolesE χe pregs cls i).getD (9 + s) 0) := by
  have hT : ∀ (g : K6 × K6 × K6 × K6 × K6 × K6 × K6 × K6 → K6) (t : Fin (NE pregs cls) → KQ)
      (ht : ∀ j (hj : j < NE pregs cls), K6.toQ (g (lrE χe pregs cls j)) = t ⟨j, hj⟩),
      K6.toQ ((Nock.V1J9A.GenAxE.inclSums ((lrL χe pregs cls).map g)).getD i 0) = accN t i := by
    intro g t ht
    rw [List.map_map]
    exact toQ_incl_accN (fun j => g (lrE χe pregs cls j)) t ht i hi
  have hR : (rolesE χe pregs cls i).getD (9 + 5) 0 = (accVE χe pregs cls).getD i 0 ∧
      (rolesE χe pregs cls i).getD (9 + 6) 0 = (accSE χe pregs cls).getD i 0 ∧
      (rolesE χe pregs cls i).getD (9 + 7) 0 = (accXE χe pregs cls).getD i 0 := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [rolesE, rolesQ, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
  interval_cases s
  · exact (toQ_invV_at χe pregs cls i hi).symm
  · exact (toQ_invR_at χe pregs cls i hi).symm
  · exact (toQ_invO_at χe pregs cls i hi).symm
  · exact (toQ_invJ_at χe pregs cls i hi).symm
  · exact (toQ_invX_at χe pregs cls i hi).symm
  · show accN (tV (n := NE pregs cls) deltaF CH TB) i = _
    rw [show (rolesE χe pregs cls i).getD (9 + 5) 0 = (accVE χe pregs cls).getD i 0 from hR.1]
    exact (hT (fun x => x.1) (tV (n := NE pregs cls) deltaF CH TB)
      fun j hj => toQ_tV_at χe pregs cls j hj).symm
  · show accN (tS (n := NE pregs cls) deltaF CH TB) i = _
    rw [show (rolesE χe pregs cls i).getD (9 + 6) 0 = (accSE χe pregs cls).getD i 0 from hR.2.1]
    exact (hT (fun x => x.2.1) (tS (n := NE pregs cls) deltaF CH TB)
      fun j hj => toQ_tS_at χe pregs cls j hj).symm
  · show accN (tX (n := NE pregs cls) deltaF CH TB) i = _
    rw [show (rolesE χe pregs cls i).getD (9 + 7) 0 = (accXE χe pregs cls).getD i 0 from hR.2.2]
    exact (hT (fun x => x.2.2.1) (tX (n := NE pregs cls) deltaF CH TB)
      fun j hj => toQ_tX_at χe pregs cls j hj).symm

/-- The honest `𝕂`-role `r < 34` of row `i` is the `K3.toK` lift of the executable role's `Re` / `Im`. -/
theorem roleK_eq (r : ℕ) (hr : r < 34) (i : ℕ) (hi : i < NE pregs cls) :
    roleK deltaF TB (r2AL (n := NE pregs cls) deltaF CH TB) r ⟨i, hi⟩ =
      K3.toK (if r % 2 = 0 then ((rolesE χe pregs cls i).getD (r / 2) 0).re
        else ((rolesE χe pregs cls i).getD (r / 2) 0).im) := by
  unfold roleK
  by_cases h18 : r < 18
  · rw [if_pos h18, rowAt_tbE_snd, kvec_qQ _ r h18]
    have e : (rolesE χe pregs cls i).getD (r / 2) 0 = (rolesQ (rqE χe pregs cls i)).getD (r / 2) 0 := by
      unfold rolesE
      rw [List.getD_append _ _ _ _ (by simp [rolesQ]; omega)]
    rw [e]
    split_ifs <;> rfl
  · rw [if_neg h18]
    unfold r2AL
    have e : r / 2 = 9 + (r - 18) / 2 := by omega
    rw [qv2_eq χe pregs cls _ (by omega) i hi, e]
    split_ifs
    · exact re_toQ _
    · exact im_toQ _

/-- **The executable ALU table is the honest column function**, every column `c < 196`, every row `i < N`. -/
theorem cols_eq (i : ℕ) (hi : i < NE pregs cls) (c : ℕ) (hc : c < 196) :
    (colsE pregs cls i ++ Nock.V1J9A.GenAxE.roleLimbs (rolesE χe pregs cls i)).toArray.getD c 0 =
      fullCol (NE_pos pregs cls) (colAL deltaF powerBasis3 TB (r2AL (n := NE pregs cls) deltaF CH TB)) c ⟨i, hi⟩ := by
  have hlen : (colsE pregs cls i).length = 94 := by simp [colsE]
  by_cases h94 : c < 94
  · rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_append_left (by omega)]
    simp only [colsE, List.getElem?_map, List.getElem?_range h94, Option.map_some, Option.getD_some]
    unfold fullCol
    by_cases h0 : c = 0
    · simp [h0]
    by_cases h1 : c = 1
    · subst h1
      simp only [if_neg (show (1 : ℕ) ≠ 0 by omega), if_true]
      by_cases hl : i + 1 = NE pregs cls
      · rw [if_pos hl, if_pos (Fin.ext (by simp; omega))]
      · rw [if_neg hl, if_neg (fun h => hl (by have := congrArg Fin.val h; simp at this; omega))]
    · rw [if_neg h0, if_neg h1, if_neg h0, if_neg h1, colAL, if_pos h94, rowAt_tbE_fst]
      rfl
  · rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_append_right (by omega), hlen]
    have e1 : c - 94 = 3 * ((c - 94) / 3) + (c - 94) % 3 := by omega
    have hr : (c - 94) / 3 < 2 * (rolesE χe pregs cls i).length := by simp [rolesE, rolesQ]; omega
    have hg := GenPortJ9AChips.getD_roleLimbs (rolesE χe pregs cls i) ((c - 94) / 3) ((c - 94) % 3)
      (Nat.mod_lt _ (by norm_num)) hr
    rw [← e1] at hg
    rw [← List.getD_eq_getElem?_getD, hg]
    unfold fullCol
    rw [if_neg (show c ≠ 0 by omega), if_neg (show c ≠ 1 by omega), colAL, if_neg h94,
      roleK_eq χe pregs cls _ (by omega) i hi, GenPortJ9AChips.coordN_toK']

/-- `cols_eq` at any row count `n = N`. -/
theorem cols_eq' {n : ℕ} (hn0 : 0 < n) (hnE : n = NE pregs cls) (i : Fin n) (c : ℕ) (hc : c < 196) :
    (colsE pregs cls i ++ Nock.V1J9A.GenAxE.roleLimbs (rolesE χe pregs cls i)).toArray.getD c 0 =
      fullCol hn0 (colAL deltaF powerBasis3 TB (r2AL (n := n) deltaF CH TB)) c i := by
  subst hnE
  exact cols_eq χe pregs cls i i.2 c hc

end Cols

/-! ## 4. The publics -/

section Pubs

/-- The executable sum of one lane term over the padded rows. -/
abbrev sumE (χe : CoinsE) (pregs : List (BRow (ZMod p))) (cls : List CallL)
    (g : K6 × K6 × K6 × K6 × K6 × K6 × K6 × K6 → K6) : K6 :=
  ((lrL χe pregs cls).map g).foldl (· + ·) 0

theorem aluGenE_snd (χe : CoinsE) (cs : List Noun) (Hm : Noun → ℕ × ℕ) (ps : List (ℕ × PrimOp)) (ids : List ℕ)
    (pc : List (ℕ × Noun × Noun)) :
    (aluGenE χe cs Hm ps ids pc).2 = fun j =>
      if j = 0 then (sumE χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc) fun x => x.1).re
      else if j = 1 then (sumE χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc) fun x => x.1).im
      else if j = 2 then (sumE χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc) fun x => x.2.1).re
      else if j = 3 then (sumE χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc) fun x => x.2.1).im
      else if j = 4 then (sumE χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc) fun x => x.2.2.1).re
      else if j = 5 then (sumE χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc) fun x => x.2.2.1).im
      else 0 := rfl

variable (χe : CoinsE) (pregs : List (BRow (ZMod p))) (cls : List CallL)

local notation "TB" => tbE (yE χe) pregs cls
local notation "CH" => chalsALJ8 deltaF (toχ χe)

theorem toQ_sumE {n : ℕ} (hnE : n = NE pregs cls) (g : K6 × K6 × K6 × K6 × K6 × K6 × K6 × K6 → K6)
    (t : Fin n → KQ) (ht : ∀ j (hj : j < n), K6.toQ (g (lrE χe pregs cls j)) = t ⟨j, hj⟩) :
    K6.toQ (sumE χe pregs cls g) = ∑ i : Fin n, t i := by
  subst hnE
  rw [sumE, List.map_map]
  exact toQ_foldl_sum (fun j => g (lrE χe pregs cls j)) t ht

theorem sumV_eq {n : ℕ} (hnE : n = NE pregs cls) :
    K6.toQ (sumE χe pregs cls fun x => x.1) = ∑ i : Fin n, tV (n := n) deltaF CH TB i :=
  toQ_sumE χe pregs cls hnE _ _ fun j hj => toQ_tV_at χe pregs cls j hj

theorem sumS_eq {n : ℕ} (hnE : n = NE pregs cls) :
    K6.toQ (sumE χe pregs cls fun x => x.2.1) = ∑ i : Fin n, tS (n := n) deltaF CH TB i :=
  toQ_sumE χe pregs cls hnE _ _ fun j hj => toQ_tS_at χe pregs cls j hj

theorem sumX_eq {n : ℕ} (hnE : n = NE pregs cls) :
    K6.toQ (sumE χe pregs cls fun x => x.2.2.1) = ∑ i : Fin n, tX (n := n) deltaF CH TB i :=
  toQ_sumE χe pregs cls hnE _ _ fun j hj => toQ_tX_at χe pregs cls j hj

end Pubs

/-! ## 5. (e) The preprocessing -/

section Pre

/-- Row `i`'s preg columns of the honest table are the verifier's `pregCol` layout. -/
theorem col_pregCol {n : ℕ} (nodes : Fin n → ZMod p) (hinj : Function.Injective nodes) (y : KQ)
    (ps : List (ℕ × PrimOp)) (vcOf mOf : ℕ → ℕ) (cls : List CallL) (hnoDec : ∀ q ∈ ps, q.2 ≠ .dec)
    (hlen : (tblP (K := KC) deltaF p y (AluSatPreg.pregsP ps vcOf mOf) cls).length ≤ n) (k : Fin 3) (i : Fin n) :
    (rowAt (K := KC) deltaF (tblP (K := KC) deltaF p y (AluSatPreg.pregsP ps vcOf mOf) cls) i).1.col ((k : ℕ) + 2) =
      Nock.V1J9AL.CheckJ9AL.pregCol ps (k : ℕ) (i : ℕ) := by
  have hP := (AluSatPreg.pregOK_tblP deltaF nodes hinj p y ps vcOf mOf cls hnoDec hlen).2 i
  rw [← AluSatPreg.preLOf_eval deltaF nodes hinj _ k i]
  match k with
  | 0 => rw [hP.1]; simp [Nock.V1J9AL.CheckJ9AL.pregCol]
  | 1 => rw [hP.2.1]; simp [Nock.V1J9AL.CheckJ9AL.pregCol]
  | 2 => rw [hP.2.2]; simp [Nock.V1J9AL.CheckJ9AL.pregCol]

/-- **(e) The verifier's preprocessing is the honest `preLOf`.** -/
theorem preL_eq_preLOf {n : ℕ} (nodes : Fin n → ZMod p) (hinj : Function.Injective nodes) (y : KQ)
    (ps : List (ℕ × PrimOp)) (vcOf mOf : ℕ → ℕ) (cls : List CallL) (hnoDec : ∀ q ∈ ps, q.2 ≠ .dec)
    (hlen : (tblP (K := KC) deltaF p y (AluSatPreg.pregsP ps vcOf mOf) cls).length ≤ n) :
    (fun k : Fin 3 => Lagrange.interpolate Finset.univ nodes
        (fun i => Nock.V1J9AL.CheckJ9AL.pregCol ps (k : ℕ) (i : ℕ))) =
      AluSatPreg.preLOf deltaF nodes (tblP (K := KC) deltaF p y (AluSatPreg.pregsP ps vcOf mOf) cls) := by
  funext k
  unfold AluSatPreg.preLOf
  congr 1
  funext i
  exact (col_pregCol nodes hinj y ps vcOf mOf cls hnoDec hlen k i).symm

end Pre

/-! ## 5b. Risk 2: the pole family past the table is a repeat of its last row -/

section Poles

/-- **`famAL` at any row count `n` is good once it is good at `m`**, when every row from `m − 1` on is row `m − 1`
(the padding rows repeat the last row; their poles are row `m − 1`'s). -/
theorem famAL_good_of_le
    (T : KQ → List (BRow (ZMod p) × QRow KQ)) {m : ℕ} (hm : 0 < m)
    (hrow : ∀ y i, m - 1 ≤ i → rowAt (K := KC) deltaF (T y) i = rowAt (K := KC) deltaF (T y) (m - 1))
    (χ : SVFrame.Coins FrameJ8.frameJ8 KC) (hg : ∀ e ∈ AluPoles.famAL deltaF T m, χ ∉ e.ev) (n : ℕ) :
    ∀ e ∈ AluPoles.famAL deltaF T n, χ ∉ e.ev := by
  intro e he
  obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
  by_cases him : i < m
  · exact hg e (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr him, he⟩)
  · have hV : AluPoles.xV deltaF T i = AluPoles.xV deltaF T (m - 1) := by
      funext χ'
      unfold AluPoles.xV eKM eFM
      rw [hrow _ i (by omega)]
    have hH : ∀ l, AluPoles.xH deltaF T l i = AluPoles.xH deltaF T l (m - 1) := by
      intro l
      funext χ'
      unfold AluPoles.xH eFM
      rw [hrow _ i (by omega)]
    refine hg e (List.mem_flatMap.mpr ⟨m - 1, List.mem_range.mpr (by omega), ?_⟩)
    rw [hV] at he
    simp only [hH] at he
    exact he

/-- `hrow` for the honest table at its own length (its last row is the padding row). -/
theorem rowAt_tblP_last (pregs : List (BRow (ZMod p))) (cls : List CallL) (y : KQ) (i : ℕ)
    (hi : (tblP (K := KC) deltaF p y pregs cls).length - 1 ≤ i) :
    rowAt (K := KC) deltaF (tblP (K := KC) deltaF p y pregs cls) i =
      rowAt (K := KC) deltaF (tblP (K := KC) deltaF p y pregs cls) ((tblP (K := KC) deltaF p y pregs cls).length - 1) := by
  have hpad : ∀ j, (tblP (K := KC) deltaF p y pregs cls).length - 1 ≤ j →
      rowAt (K := KC) deltaF (tblP (K := KC) deltaF p y pregs cls) j = (padRow, QRow.zero) := by
    intro j hj
    unfold rowAt tblP at *
    rw [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < (pregs.map (fun r => (r, (QRow.zero : QRow KQ))) ++
        cls.flatMap (zipB (K := KC) deltaF p y)).length + 1
    · rw [List.getD_append_right _ _ _ _ (by omega)]
      rw [show j - (pregs.map (fun r => (r, (QRow.zero : QRow KQ))) ++
        cls.flatMap (zipB (K := KC) deltaF p y)).length = 0 by omega]
      rfl
    · rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton] at hlt ⊢; omega)]
  rw [hpad i hi, hpad _ le_rfl]

end Poles

/-! ## 6. (f) The executable ALU chip is accepted -/

section Chip

open Nock.V1J8.Gen (chipOf hOf)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb reorb)

variable [iA : Algebra Nock.Atoms.Fp KQ]

/-- The honest ALU table at the run's coin and the honest preg rows. -/
abbrev tbH (χe : CoinsE) (ps : List (ℕ × PrimOp)) (vcOf mOf : ℕ → ℕ) (cls : List CallL) :
    List (BRow (ZMod p) × QRow KQ) :=
  tblP (K := KC) deltaF p (AluPoles.yOf deltaF (toχ χe)) (AluSatPreg.pregsP ps vcOf mOf) cls

theorem chipOf_aluGenE_n (χe : CoinsE) (cs : List Noun) (Hm : Noun → ℕ × ℕ) (ps : List (ℕ × PrimOp))
    (ids : List ℕ) (pc : List (ℕ × Noun × Noun)) (O : Orb) :
    (reorb (chipOf (aluGenE χe cs Hm ps ids pc).1) O).n = NE (pregsOf cs ps ids) (callsLOf cs Hm ps pc) :=
  aluGenE_size χe cs Hm ps ids pc

/-- On a full orbit (`n = 3·2^h`) the last node's successor is node `0`. -/
theorem zNodes_xLast (q : ChipIn) (ho : OrbOK q) (hn0 : 0 < q.n) (hfull : q.n = 3 * 2 ^ q.h) :
    (AluTraceFix.zNodes (nodesOf q)).eval (xLast hn0 (nodesOf q) (mkOrbit q ho)) = 0 := by
  have hx : xLast hn0 (nodesOf q) (mkOrbit q ho) = nodesOf q ⟨0, hn0⟩ := by
    unfold xLast
    rw [nodesOf_eq, nodesOf_eq]
    show q.ω.toZ * q.ω.toZ ^ (q.n - 1) = q.ω.toZ ^ 0
    rw [← pow_succ', show q.n - 1 + 1 = q.n by omega, hfull, ← ho.ord, pow_orderOf_eq_one, pow_zero]
  rw [hx]
  exact AluTraceFix.zNodes_eval_node _ _

/-- **(f) core: the executable ALU chip at a full admissible orbit `O` is accepted** (present branch). -/
theorem alChipOK_exec (χe : CoinsE) (cs : List Noun) (Hm : Noun → ℕ × ℕ) (ps : List (ℕ × PrimOp)) (ids : List ℕ)
    (pc : List (ℕ × Noun × Noun)) (vcOf mOf : ℕ → ℕ)
    (hpreg : (pregsOf cs ps ids : List (BRow (ZMod p))) = AluSatPreg.pregsP ps vcOf mOf)
    (hnoDec : ∀ q ∈ ps, q.2 ≠ .dec)
    (hblk : ∀ cl ∈ callsLOf cs Hm ps pc, BlockBaseSat (F := ZMod p) p cl ∧ BlockIdentSat (K := KC) deltaF p cl)
    (hsz : (aluRowsB p (pregsOf cs ps ids : List (BRow (ZMod p))) (callsLOf cs Hm ps pc)).length ≤ 2 ^ 31)
    (q : ChipIn) (O : Orb) (hqc : q = reorb (chipOf (aluGenE χe cs Hm ps ids pc).1) O) (ho : OrbOK q)
    (hn0 : 0 < q.n) (hfull : q.n = 3 * 2 ^ q.h)
    (hgood : ∀ e ∈ AluPoles.famAL deltaF
        (fun y => tblP (K := KC) deltaF p y (AluSatPreg.pregsP ps vcOf mOf) (callsLOf cs Hm ps pc)) q.n,
      toχ χe ∉ e.ev)
    (on : Bool) (hon : on = true) (prs : List (ℕ × PrimOp)) (hprs : prs = ps)
    (chals pubs : ℕ → KC) (hch : chals = chalsALJ8 deltaF (toχ χe))
    (hpub : pubs = fun j => K3.toK ((aluGenE χe cs Hm ps ids pc).2 j))
    (pre : Fin 3 → (ZMod p)[X])
    (hpre : ∀ k : Fin 3, pre k =
      Lagrange.interpolate Finset.univ (nodesOf q) (fun i => Nock.V1J9AL.CheckJ9AL.pregCol ps (k : ℕ) (i : ℕ)))
    (P : Fin (AluSZChipJ9.aluSZChipJ9 deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) chals pubs pre).rap.w →
      (ZMod p)[X])
    (hP : ∀ j, P j = interpOf q (j : ℕ)) :
    AcceptsJ9AL.ALChipOK deltaF powerBasis3 on prs hn0 (nodesOf q) (mkOrbit q ho) pre chals pubs P := by
  rw [hon, hprs]
  subst hch hpub
  have hTB : tbE (yE χe) (pregsOf cs ps ids) (callsLOf cs Hm ps pc) = tbH χe ps vcOf mOf (callsLOf cs Hm ps pc) := by
    show tblP (K := KC) deltaF p (K6.toQ (yE χe)) (pregsOf cs ps ids) (callsLOf cs Hm ps pc) = _
    rw [toQ_yE_yOf, hpreg]
  have hnE : q.n = NE (pregsOf cs ps ids) (callsLOf cs Hm ps pc) := by
    rw [hqc]; exact chipOf_aluGenE_n χe cs Hm ps ids pc O
  have hspec := GenPortJ9AHOrb.hOf_spec _ hsz
  have hlen : (tbH χe ps vcOf mOf (callsLOf cs Hm ps pc)).length ≤ q.n := by
    rw [← hTB, tbE_length, hnE]; exact hspec.2.1
  have hnp : q.n < p := by
    have h1 : q.n ≤ 3 * 2 ^ 32 := by
      rw [hnE]; exact Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by norm_num) hspec.2.2)
    have h2 : (3 * 2 ^ 32 : ℕ) < p := by norm_num [Nock.Field.p]
    omega
  have hinj : Function.Injective (nodesOf q) := GenPortJ9AHOrb.nodesOf_inj q ho (by omega)
  have hadj : ∀ (i : Fin q.n) (hi : (i : ℕ) + 1 < q.n),
      nodesOf q ⟨(i : ℕ) + 1, hi⟩ = nodesOf q i * (mkOrbit q ho).ω := by
    intro i hi
    rw [GenPortJ9AHOrb.nodesOf_adj q i hi, mul_comm]; rfl
  -- the columns
  have hcol : ∀ (c : ℕ) (i : Fin q.n), c < 196 →
      q.cols c i = fullCol hn0 (colAL deltaF powerBasis3 (tbH χe ps vcOf mOf (callsLOf cs Hm ps pc))
        (r2AL (n := q.n) deltaF (chalsALJ8 deltaF (toχ χe)) (tbH χe ps vcOf mOf (callsLOf cs Hm ps pc)))) c i := by
    intro c i hc
    have hi : (i : ℕ) < NE (pregsOf cs ps ids) (callsLOf cs Hm ps pc) := hnE ▸ i.2
    have e1 : q.cols c i = ((aluGenE χe cs Hm ps ids pc).1.getD i #[]).getD c 0 := by subst hqc; rfl
    rw [e1, aluGenE_getD χe cs Hm ps ids pc i hi, cols_eq' χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc) hn0 hnE i c hc, hTB]
  -- the preprocessing
  have hpre' : pre = AluSatPreg.preLOf deltaF (nodesOf q) (tbH χe ps vcOf mOf (callsLOf cs Hm ps pc)) := by
    rw [← preL_eq_preLOf (nodesOf q) hinj _ ps vcOf mOf (callsLOf cs Hm ps pc) hnoDec hlen]
    exact funext hpre
  subst hpre'
  -- the trace
  have hPe : P = polyAL deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho) (chalsALJ8 deltaF (toχ χe))
      (fun j => K3.toK ((aluGenE χe cs Hm ps ids pc).2 j)) (AluSatPreg.preLOf deltaF (nodesOf q) (tbH χe ps vcOf mOf (callsLOf cs Hm ps pc))) (tbH χe ps vcOf mOf (callsLOf cs Hm ps pc))
      (r2AL deltaF (chalsALJ8 deltaF (toχ χe)) (tbH χe ps vcOf mOf (callsLOf cs Hm ps pc))) := by
    funext j
    have hj : (j : ℕ) < 196 := j.2
    rw [hP j]
    unfold polyAL
    split_ifs with h1 h2
    · unfold AluSatPreg.preLOf interpOf
      congr 1
      funext i
      rw [hcol j i hj]
      simp only [fullCol, if_neg (show (j : ℕ) ≠ 0 by omega), if_neg (show (j : ℕ) ≠ 1 by omega), colAL,
        if_pos (show (j : ℕ) < 94 by omega), show (j : ℕ) - 2 + 2 = j by omega]
    · unfold AluTraceFix.fixAt
      rw [if_pos (zNodes_xLast q ho hn0 hfull)]
      unfold honestQ interpOf
      congr 1
      funext i
      exact hcol j i hj
    · unfold honestQ interpOf
      congr 1
      funext i
      exact hcol j i hj
  rw [hPe]
  -- the publics
  have hV := sumV_eq χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc) hnE
  have hS := sumS_eq χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc) hnE
  have hX := sumX_eq χe (pregsOf cs ps ids) (callsLOf cs Hm ps pc) hnE
  rw [hTB] at hV hS hX
  have hgood' := AluPoles.hden_of_famAL deltaF
    (fun y => tblP (K := KC) deltaF p y (AluSatPreg.pregsP ps vcOf mOf) (callsLOf cs Hm ps pc)) (toχ χe) hgood
  obtain ⟨hs, hb, hpg⟩ := AluSatPreg.aluSZChipJ9_honest_sat_preg deltaF powerBasis3 hn0 (nodesOf q) (mkOrbit q ho)
    (chalsALJ8 deltaF (toχ χe)) (fun j => K3.toK ((aluGenE χe cs Hm ps ids pc).2 j)) p
    (AluPoles.yOf deltaF (toχ χe)) ps vcOf mOf (callsLOf cs Hm ps pc) hnoDec hblk
    (AluSZChipJ9.chalsALJ8_y deltaF (toχ χe))
    (fun t ht => AluSZChipJ9.chalsALJ8_ypow deltaF (toχ χe) t ht) hinj hadj hlen hgood'
    (by rw [← hV, aluGenE_snd]; rfl) (by rw [← hS, aluGenE_snd]; rfl) (by rw [← hX, aluGenE_snd]; rfl)
  exact Or.inl ⟨rfl, hs, hb, hinj, hadj, hnp, hpg⟩

theorem hOf_go_eq (n k : ℕ) (hk : n ≤ 3 * 2 ^ k) : ∀ (f h : ℕ), h ≤ k → k - h < f →
    (∀ h', h ≤ h' → h' < k → ¬ n ≤ 3 * 2 ^ h') → hOf.go n f h = k
  | 0, h, _, hf, _ => absurd hf (Nat.not_lt_zero _)
  | f + 1, h, hhk, hf, hmin => by
    unfold hOf.go
    by_cases hn : n ≤ 3 * 2 ^ h
    · rw [if_pos hn]
      by_contra hne
      exact hmin h le_rfl (by omega) hn
    · rw [if_neg hn]
      have hne : h ≠ k := fun e => hn (e ▸ hk)
      exact hOf_go_eq n k hk f (h + 1) (by omega) (by omega) fun h' h1 h2 => hmin h' (by omega) h2

/-- `hOf (3·2^k) = k` for `1 ≤ k ≤ 64`. -/
theorem hOf_three_pow (k : ℕ) (h1 : 1 ≤ k) (h64 : k ≤ 64) : hOf (3 * 2 ^ k) = k := by
  unfold hOf
  refine hOf_go_eq _ k le_rfl 64 1 h1 (by omega) fun h' _ h2 hle => ?_
  have : 2 ^ h' < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) h2
  omega

/-- **The generator's ALU chip is on a full orbit** (`n = 3·2^h`), so `hfull` holds at its own orbit. -/
theorem chipOf_aluGenE_full (χe : CoinsE) (cs : List Noun) (Hm : Noun → ℕ × ℕ) (ps : List (ℕ × PrimOp))
    (ids : List ℕ) (pc : List (ℕ × Noun × Noun))
    (hsz : (aluRowsB p (pregsOf cs ps ids : List (BRow (ZMod p))) (callsLOf cs Hm ps pc)).length ≤ 2 ^ 31) :
    (chipOf (aluGenE χe cs Hm ps ids pc).1).n = 3 * 2 ^ (chipOf (aluGenE χe cs Hm ps ids pc).1).h := by
  have hspec := GenPortJ9AHOrb.hOf_spec _ hsz
  show (aluGenE χe cs Hm ps ids pc).1.size = 3 * 2 ^ hOf (aluGenE χe cs Hm ps ids pc).1.size
  rw [aluGenE_size, NE, hOf_three_pow _ hspec.1 (by omega)]

/-- **(f) `alE_at`: the `hALk` field of `AcceptsJ9AL` at `mkPbAL I hv`**, for an abstract input `I` whose ALU chip is
the executable table at some orbit `O` (`hL`: the `withOrbL` shape `reorb (chipOf T) O`; `O` = the table's own orbit
gives `I.AL = chipOf T`), whose ALU publics are the executable ones (`hpL`), present (`hon`), with primitive table
`ps` (`hpr`) and coins `χe` (`hχ`); the orbit is full (`hfull`). -/
theorem alE_at (I : Nock.V1J9AL.CheckJ9AL.InJ9AL) (hv : Nock.V1J9AL.CheckJ9ALIff.ValidJ9AL I)
    (χe : CoinsE) (cs : List Noun) (Hm : Noun → ℕ × ℕ) (ps : List (ℕ × PrimOp)) (ids : List ℕ)
    (pc : List (ℕ × Noun × Noun)) (vcOf mOf : ℕ → ℕ)
    (hpreg : (pregsOf cs ps ids : List (BRow (ZMod p))) = AluSatPreg.pregsP ps vcOf mOf)
    (hnoDec : ∀ q ∈ ps, q.2 ≠ .dec)
    (hblk : ∀ cl ∈ callsLOf cs Hm ps pc, BlockBaseSat (F := ZMod p) p cl ∧ BlockIdentSat (K := KC) deltaF p cl)
    (hsz : (aluRowsB p (pregsOf cs ps ids : List (BRow (ZMod p))) (callsLOf cs Hm ps pc)).length ≤ 2 ^ 31)
    (O : Orb) (hL : I.AL = reorb (chipOf (aluGenE χe cs Hm ps ids pc).1) O)
    (hpL : I.pubsL = (aluGenE χe cs Hm ps ids pc).2)
    (hon : I.aluOn = true) (hpr : I.prims = ps) (hχ : I.χ = χe)
    (hfull : I.AL.n = 3 * 2 ^ I.AL.h)
    (hgood : ∀ e ∈ AluPoles.famAL deltaF
        (fun y => tblP (K := KC) deltaF p y (AluSatPreg.pregsP ps vcOf mOf) (callsLOf cs Hm ps pc)) I.AL.n,
      toχ χe ∉ e.ev) :
    AcceptsJ9AL.ALChipOK deltaF powerBasis3 (Nock.V1J9AL.CheckJ9ALIff.mkPbAL I hv).aluOn
      (Nock.V1J9AL.CheckJ9ALIff.mkPbAL I hv).prims (Nock.V1J9AL.CheckJ9ALIff.mkPbAL I hv).hnL
      (Nock.V1J9AL.CheckJ9ALIff.mkPbAL I hv).nodesL (Nock.V1J9AL.CheckJ9ALIff.mkPbAL I hv).orbitL
      (Nock.V1J9AL.CheckJ9ALIff.mkPbAL I hv).preL (chalsALJ8 deltaF (toχ I.χ)) I.toMsgL.pubsL
      (RealIOJ9AL.qAL deltaF powerBasis3 (Nock.V1J9AL.CheckJ9ALIff.mkPbAL I hv) I.toTrL
        (chalsALJ8 deltaF (toχ I.χ)) I.toMsgL.pubsL) :=
  alChipOK_exec χe cs Hm ps ids pc vcOf mOf hpreg hnoDec hblk hsz I.AL O hL hv.oAL hv.nL hfull hgood
    I.aluOn hon I.prims hpr _ _ (by rw [hχ]) (by funext j; show K3.toK (I.pubsL j) = _; rw [hpL])
    _ (fun k => by show Lagrange.interpolate _ _ _ = _; rw [hpr]) _ (fun j => rfl)

end Chip

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE
