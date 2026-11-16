/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAtom.lean

  The atom chip's honest columns for the executable data.

  * `toQ_zq`, `lastK6_scan`, list-access lemmas;
  * `newBA_info` (the info columns of `newBA D` are the executable `AInfo` fields);
  * `dMB_bridge`, `dC_bridge`, `dMI_bridge` (exec denominators = honest ones, via their closed forms);
  * `iMB_eq`, `aMB_eq`, ... (inverses and accumulators);
  * `role_eq`, `atomGenE_cols`, `atomGenE_pubs`, `interp_cast`.

  Statement note: `atomGenE_cols` carries the `GenHyp` hypothesis `hg` (needed by `atomNew_eq`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRow
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomCols1
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomKey
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomCols2

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
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomCols2
open Nock.NockVMROM.Thm54.CoordinateBasis

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtom

/-! ## 1. Generic bridges -/

theorem toQ_zq (x : ZMod P) : K6.toQ (Gen.zq x) = liftQ (K := KC) deltaF x := by
  unfold Gen.zq
  rw [toQ_g6, Gold.toZ_ofZ]
  exact IsScalarTower.algebraMap_apply (ZMod P) KC KQ _

theorem lastK6_eq (L : List K6) : lastK6 L = L.getD (L.length - 1) 0 := by
  unfold lastK6
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

/-- The last prefix sum is the whole sum. -/
theorem lastK6_scan (L : List K6) (hL : L ≠ []) :
    K6.toQ (lastK6 (Gen.scanK6 L)) = ∑ k ∈ Finset.range L.length, K6.toQ (L.getD k 0) := by
  have hlen : (Gen.scanK6 L).length = L.length := scanK6_length L
  have hpos : 0 < L.length := List.length_pos_of_ne_nil hL
  rw [lastK6_eq, hlen, toQ_scanK6_getD L (L.length - 1) (by omega), Nat.sub_add_cancel hpos]

theorem zipIdx_map_getD {α : Type} (L : List α) (f : α × ℕ → K6) (j : ℕ) (hj : j < L.length) :
    ((L.zipIdx 0).map f).getD j 0 = f (L[j], j) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem zip_map_getD {α β : Type} (L : List α) (M : List β) (f : α × β → K6) (j : ℕ)
    (hj : j < L.length) (hj' : j < M.length) :
    ((L.zip M).map f).getD j 0 = f (L[j], M[j]) := by
  rw [List.getD_eq_getElem _ _ (by simp [hj, hj'])]
  simp

theorem toQ_el (v : K6) (x : ZMod P) (h : K6.toQ v = liftQ (K := KC) deltaF x) :
    K6.toQ v = algebraMap KC KQ (algebraMap (ZMod P) KC x) := h

/-! ## 2. The executable role lists -/

abbrev aisL (info : Array AInfo) (n : ℕ) : List AInfo := (List.range n).map fun j => info.getD j AInfo.z

abbrev iMBL (pt : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) : List K6 :=
  (dsL pt χe acsL).map fun d => (dMBA (coOfA χe) (zE χe) d)⁻¹

abbrev iCL (info : Array AInfo) (n : ℕ) (χe : CoinsE) : List K6 :=
  (aisL info n).map fun ai => (dCA (coOfA χe) ai)⁻¹

abbrev iMIL (info : Array AInfo) (n : ℕ) (χe : CoinsE) : List K6 :=
  ((aisL info n).zipIdx 0).map fun (ai, j) => (dMIA (coOfA χe) ai j)⁻¹

abbrev aMBL (pt : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) (mb : Array ℕ) : List K6 :=
  Gen.scanK6 (((iMBL pt χe acsL).zipIdx 0).map fun (v, j) => lq (mb.getD j 0) * v)

abbrev aCL (χe : CoinsE) (info : Array AInfo) (n : ℕ) : List K6 :=
  Gen.scanK6 (((iCL info n χe).zip (aisL info n)).map fun (v, ai) => (if ai.inc then 1 else 0) * v)

abbrev aMIL (χe : CoinsE) (info : Array AInfo) (n : ℕ) : List K6 :=
  Gen.scanK6 (((iMIL info n χe).zip (aisL info n)).map fun (v, ai) => lq ai.mi * v)

/-- The six `𝕂′` role values of row `j` (`iMB, aMB, iC, iMI, aMI, aC`). -/
def r6E (pt : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) (info : Array AInfo) (mb : Array ℕ) (j : ℕ) :
    List K6 :=
  [(iMBL pt χe acsL).getD j 0, (aMBL pt χe acsL mb).getD j 0, (iCL info acsL.length χe).getD j 0,
    (iMIL info acsL.length χe).getD j 0, (aMIL χe info acsL.length).getD j 0,
    (aCL χe info acsL.length).getD j 0]

def rolesE (pt : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) (info : Array AInfo) (mb : Array ℕ) (j : ℕ) :
    ℕ → K3 :=
  fun t => let v := (r6E pt χe acsL info mb j).getD (t / 2) 0; if t % 2 = 0 then v.re else v.im

/-- The six terminals `v, x, h, mb, mi, c`. -/
def pubsL (pt : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) (info : Array AInfo) (mb mxA mhA : Array ℕ) :
    List K6 :=
  [lastK6 (Gen.scanK6 ((dsL pt χe acsL).map (vTermD (mvE acsL pt)))),
    lastK6 (Gen.scanK6 ((dsL pt χe acsL).map (xTermD mxA (Array.replicate acsL.length 0)))),
    lastK6 (Gen.scanK6 ((dsL pt χe acsL).map (hTermD (mhArr acsL info mhA)))),
    lastK6 (aMBL pt χe acsL mb), lastK6 (aMIL χe info acsL.length), lastK6 (aCL χe info acsL.length)]

/-- The twelve publics as limbs of the six terminals. -/
def pubsE (pt : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) (info : Array AInfo) (mb mxA mhA : Array ℕ) :
    ℕ → K3 := fun j =>
  if j < 12 then
    (if j % 2 = 0 then ((pubsL pt χe acsL info mb mxA mhA).getD (j / 2) 0).re
      else ((pubsL pt χe acsL info mb mxA mhA).getD (j / 2) 0).im)
  else 0

theorem atomGenE_pubs_eq (pt : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) (info : Array AInfo)
    (mb mxA mhA : Array ℕ) : (atomGenE pt χe acsL info mb mxA mhA).2 = pubsE pt χe acsL info mb mxA mhA := by
  funext j
  unfold pubsE
  by_cases hj : j < 12
  · rw [if_pos hj]
    interval_cases j <;> rfl
  · rw [if_neg hj]
    unfold atomGenE
    dsimp only
    rw [if_neg (show j ≠ 0 by omega), if_neg (show j ≠ 1 by omega), if_neg (show j ≠ 2 by omega),
      if_neg (show j ≠ 3 by omega), if_neg (show j ≠ 4 by omega), if_neg (show j ≠ 5 by omega),
      if_neg (show j ≠ 6 by omega), if_neg (show j ≠ 7 by omega), if_neg (show j ≠ 8 by omega),
      if_neg (show j ≠ 9 by omega), if_neg (show j ≠ 10 by omega), if_neg (show j ≠ 11 by omega)]

theorem atomGenE_entry' (pt : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) (info : Array AInfo)
    (mb mxA mhA : Array ℕ) (i : ℕ) (hi : i < acsL.length) (c : ℕ) (hc : c < 349) :
    ((atomGenE pt χe acsL info mb mxA mhA).1.getD i #[]).getD c 0 =
      atomColD acsL.length (mvE acsL pt) mxA (Array.replicate acsL.length 0) (mhArr acsL info mhA) (mb.getD i 0)
        (cellDE pt (coOfA χe) (yE χe) acsL acsL[i] i)
        ((Gen.scanK6 ((dsL pt χe acsL).map (vTermD (mvE acsL pt)))).getD i 0)
        ((Gen.scanK6 ((dsL pt χe acsL).map (xTermD mxA (Array.replicate acsL.length 0)))).getD i 0)
        ((Gen.scanK6 ((dsL pt χe acsL).map (hTermD (mhArr acsL info mhA)))).getD i 0)
        (info.getD i AInfo.z) (rolesE pt χe acsL info mb i) c := by
  unfold atomGenE
  dsimp only
  rw [toArray_getD _ _ i (by simp [hi])]
  simp only [List.getElem_map, List.getElem_range]
  rw [ofFn_getD _ c hc]
  rw [dsE_getD pt χe acsL i hi, infoRange_getD info acsL.length i hi]
  rfl

theorem atomColD_roles (D : ℕ) (mv mx mx1 mh : Array ℕ) (mb : ℕ) (d : CellD) (va xa ha : K6) (ai : AInfo)
    (roles : ℕ → K3) (c : ℕ) (h1 : 313 ≤ c) (h2 : c < 349) :
    atomColD D mv mx mx1 mh mb d va xa ha ai roles c = limbZ (roles ((c - 313) / 3)) ((c - 313) % 3) := by
  unfold atomColD
  dsimp only
  rw [if_neg (show ¬ c < 130 by omega), if_neg (show ¬ c < 162 by omega), if_neg (show ¬ c < 194 by omega),
    if_neg (show c ≠ 194 by omega), if_neg (show c ≠ 195 by omega), if_neg (show c ≠ 196 by omega),
    if_neg (show c ≠ 197 by omega), if_neg (show c ≠ 198 by omega), if_neg (show c ≠ 199 by omega),
    if_neg (show c ≠ 200 by omega), if_neg (show c ≠ 201 by omega), if_neg (show c ≠ 202 by omega),
    if_neg (show c ≠ 203 by omega), if_neg (show c ≠ 204 by omega), if_neg (show ¬ c < 301 by omega),
    if_neg (show ¬ c < 313 by omega), if_pos h2]

/-! ## 3. Exec denominators against the honest ones -/

section Pre
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [instFR : Fact (ringChar (ZMod P)).Prime] [instAR : Algebra (ZMod (ringChar (ZMod P))) KC]

theorem liftQ_zero' : liftQ (K := KC) deltaF (0 : ZMod P) = 0 := by
  unfold liftQ; rw [map_zero, map_zero]

theorem liftQ_one' : liftQ (K := KC) deltaF (1 : ZMod P) = 1 := by
  unfold liftQ; rw [map_one, map_one]

theorem toQ_incMul (b : Bool) (x : K6) :
    K6.toQ ((if b = true then (1 : K6) else 0) * x) = liftQ (K := KC) deltaF (flag b) * K6.toQ x := by
  rw [K6.toQ_mul]
  cases b
  · simp only [flag, Bool.false_eq_true, ite_false]
    rw [K6.toQ_zero, liftQ_zero']
  · simp only [flag, ite_true]
    rw [K6.toQ_one, liftQ_one']

include instFR instAR in
theorem toQ_dCA (k : Co) (ai : AInfo) (γ ρ : KQ) (hγ : K6.toQ k.γH = γ) (hρ : K6.toQ k.ρH = ρ) :
    K6.toQ (dCA k ai) = ρ + FiniteIO.compress (m := 5) (⟨γ, 0⟩ : FiniteIO.IOCoins KQ)
      (BalanceQ.liftRec (K := KC) (L := KQ) (fun c : Fin 5 => algebraMap (ZMod P) KC
        (![((ai.idxO : ℕ) : ZMod P), 0, ((ai.lO : ℕ) : ZMod P), ((ai.kRO : ℕ) : ZMod P),
          ((ai.vRO : ℕ) : ZMod P)] c))) := by
  unfold dCA
  refine toQ_compressH' _ _ _ _ hγ hρ _ _ ?_
  intro c
  fin_cases c
  · exact toQ_lq _
  · show K6.toQ 0 = liftQ (K := KC) deltaF (0 : ZMod P)
    rw [K6.toQ_zero, liftQ_zero']
  · exact toQ_lq _
  · exact toQ_lq _
  · exact toQ_lq _

theorem toQ_dMIA (k : Co) (ai : AInfo) (j : ℕ) (γ ρ : KQ) (hγ : K6.toQ k.γH = γ) (hρ : K6.toQ k.ρH = ρ) :
    K6.toQ (dMIA k ai j) = ρ + FiniteIO.compress (m := 5) (⟨γ, 0⟩ : FiniteIO.IOCoins KQ)
      (BalanceQ.liftRec (K := KC) (L := KQ) (fun c : Fin 5 => algebraMap (ZMod P) KC
        (![2 * (1 - flag ai.conv), (1 - flag ai.conv) * ((ai.idxO : ℕ) : ZMod P) - flag ai.conv, 2,
          ((j : ℕ) : ZMod P), 4] c))) := by
  unfold dMIA
  by_cases hc : ai.conv = true
  · simp only [if_pos hc]
    refine toQ_compressH' _ _ _ _ hγ hρ _ _ ?_
    intro c
    fin_cases c
    · show K6.toQ 0 = liftQ (K := KC) deltaF (2 * (1 - flag ai.conv))
      have h0 : (2 * (1 - flag ai.conv) : ZMod P) = 0 := by simp [hc, flag]
      rw [h0, liftQ_zero', K6.toQ_zero]
    · show K6.toQ (Gen.zq (-1)) = liftQ (K := KC) deltaF _
      rw [toQ_zq]; simp [hc, flag]
    · show K6.toQ (lq 2) = liftQ (K := KC) deltaF _
      rw [toQ_lq]; simp
    · exact toQ_lq _
    · show K6.toQ (lq 4) = liftQ (K := KC) deltaF _
      rw [toQ_lq]; simp
  · have hc' : ai.conv = false := by simpa using hc
    simp only [if_neg hc]
    refine toQ_compressH' _ _ _ _ hγ hρ _ _ ?_
    intro c
    fin_cases c
    · show K6.toQ (lq 2) = liftQ (K := KC) deltaF _
      rw [toQ_lq]; simp [hc', flag]
    · show K6.toQ (lq ai.idxO) = liftQ (K := KC) deltaF _
      rw [toQ_lq]; simp [hc', flag]
    · show K6.toQ (lq 2) = liftQ (K := KC) deltaF _
      rw [toQ_lq]; simp
    · exact toQ_lq _
    · show K6.toQ (lq 4) = liftQ (K := KC) deltaF _
      rw [toQ_lq]; simp

section Honest
variable {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
  (D : ComplJ8Data.J8Data P Rg fuel s f r)
  (hacs : D.acs = ComplJ8Data.acsP P D.bigs D.dupP)
  (hinfo : D.info = ComplJ8Data.infoOfP P D.acs D.rows)
  (hg : ComplJ8Atom.GenHyp D.bigs D.dupP D.rows D.mb)

include hacs hinfo hg in
/-- The info columns of `newBA D` are the executable `AInfo` fields. -/
theorem newBA_info (χe : CoinsE) (i : Fin D.acs.length) :
    ComplJ8Of.newBA D 196 i = ((D.mb.getD i 0 : ℕ) : ZMod P) ∧
    ComplJ8Of.newBA D 197 i = flag (D.info.getD i AInfo.z).inc ∧
    ComplJ8Of.newBA D 198 i = flag (D.info.getD i AInfo.z).conv ∧
    ComplJ8Of.newBA D 200 i = (((D.info.getD i AInfo.z).idxO : ℕ) : ZMod P) ∧
    ComplJ8Of.newBA D 201 i = (((D.info.getD i AInfo.z).lO : ℕ) : ZMod P) ∧
    ComplJ8Of.newBA D 202 i = (((D.info.getD i AInfo.z).kRO : ℕ) : ZMod P) ∧
    ComplJ8Of.newBA D 203 i = (((D.info.getD i AInfo.z).vRO : ℕ) : ZMod P) ∧
    ComplJ8Of.newBA D 204 i = (((D.info.getD i AInfo.z).mi : ℕ) : ZMod P) := by
  have key : ∀ c, 196 ≤ c → c < 205 → ∀ roles : ℕ → K3,
      ComplJ8Of.newBA D c i = atomColD D.acs.length (mvE D.acs (ComplJ8Data.ptrP P D.acs D.rows)) D.mxA
        (Array.replicate D.acs.length 0) #[] (D.mb.getD i 0)
        (cellDE (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs D.acs[i] i) 0 0 0
        (D.info.getD i AInfo.z) roles c := fun c h1 h2 roles =>
    (atomNew_eq D hacs hinfo hg χe i #[] 0 0 0 roles c (by omega) h2).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (key 196 (by norm_num) (by norm_num) (fun _ => 0)).trans ?_
    unfold atomColD; simp
  · refine (key 197 (by norm_num) (by norm_num) (fun _ => 0)).trans ?_
    unfold atomColD; simp
  · refine (key 198 (by norm_num) (by norm_num) (fun _ => 0)).trans ?_
    unfold atomColD; simp
  · refine (key 200 (by norm_num) (by norm_num) (fun _ => 0)).trans ?_
    unfold atomColD; simp
  · refine (key 201 (by norm_num) (by norm_num) (fun _ => 0)).trans ?_
    unfold atomColD; simp
  · refine (key 202 (by norm_num) (by norm_num) (fun _ => 0)).trans ?_
    unfold atomColD; simp
  · refine (key 203 (by norm_num) (by norm_num) (fun _ => 0)).trans ?_
    unfold atomColD; simp
  · refine (key 204 (by norm_num) (by norm_num) (fun _ => 0)).trans ?_
    unfold atomColD; simp

/-! ### Honest values -/

noncomputable abbrev PAh (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h) :
    ℕ → KC := ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe)

noncomputable abbrev hMB (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h) :
    Fin D.acs.length → KQ :=
  HonestA8.dMB deltaF powerBasis3 hA (ComplJ8Of.powN o _) o (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
    (PAh D χe hA o) (ComplJ8Of.colAH deltaF powerBasis3 D hA o (toχ χe) (PAh D χe hA o)) (ComplJ8Of.newBA D)

noncomputable abbrev hCC (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h) :
    Fin D.acs.length → KQ :=
  HonestA8.dC deltaF powerBasis3 hA (ComplJ8Of.powN o _) o (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
    (PAh D χe hA o) (ComplJ8Of.colAH deltaF powerBasis3 D hA o (toχ χe) (PAh D χe hA o)) (ComplJ8Of.newBA D)

noncomputable abbrev hMI (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h) :
    Fin D.acs.length → KQ :=
  HonestA8.dMI deltaF powerBasis3 hA (ComplJ8Of.powN o _) o (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
    (PAh D χe hA o) (ComplJ8Of.colAH deltaF powerBasis3 D hA o (toχ χe) (PAh D χe hA o)) (ComplJ8Of.newBA D)

/-- The honest six role values. -/
noncomputable def r6H (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (i : Fin D.acs.length) : List KQ :=
  [(hMB D χe hA o i)⁻¹, HonestA8.accOf deltaF (ComplJ8Of.newBA D AtomChipHQ.mb) (hMB D χe hA o) i,
    (hCC D χe hA o i)⁻¹, (hMI D χe hA o i)⁻¹,
    HonestA8.accOf deltaF (ComplJ8Of.newBA D AtomChipHQ.mi) (hMI D χe hA o) i,
    HonestA8.accOf deltaF (ComplJ8Of.newBA D AtomChipHQ.inc) (hCC D χe hA o) i]

theorem roleValA_r6 (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (i : Fin D.acs.length) (t : ℕ) (ht : t < 12) :
    HonestA8.roleValA deltaF powerBasis3 hA (ComplJ8Of.powN o _) o (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
      (PAh D χe hA o) (ComplJ8Of.colAH deltaF powerBasis3 D hA o (toχ χe) (PAh D χe hA o))
      (ComplJ8Of.newBA D) t i =
    if t % 2 = 0 then Quad.re _ ((r6H D χe hA o i).getD (t / 2) 0) else Quad.im _ ((r6H D χe hA o i).getD (t / 2) 0) := by
  unfold HonestA8.roleValA r6H
  interval_cases t <;> (simp [List.getD]; try rfl)

/-! ### Denominator bridges -/

include hacs hg in
theorem dMB_bridge (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (i : Fin D.acs.length) :
    K6.toQ (dMBA (coOfA χe) (zE χe)
      (cellDE (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs D.acs[(i : ℕ)] i)) = hMB D χe hA o i := by
  have hn := row_atomRow D hacs hg i i.2
  have hRow : ComplJ8Of.aRows deltaF D (toχ χe) i =
      RB (ComplJ8Of.zA deltaF (toχ χe)) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D) (ComplJ8Of.ptA D)
        D.acs[(i : ℕ)] i := aVals_eq D χe i i.2
  have pE := toQ_pE_d (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs (ComplJ8Of.mvA D)
    (ComplJ8Of.mxAF D) D.acs[(i : ℕ)] i _ (coins_hz χe) hn
  have hP3 := congrArg ComputeTable.FP.leaf pE
  show _ = HonestA8.dMB deltaF powerBasis3 hA (ComplJ8Of.powN o _) o (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
    (PAh D χe hA o) (ComplJ8Of.colAH deltaF powerBasis3 D hA o (toχ χe) (PAh D χe hA o)) (ComplJ8Of.newBA D) i
  rw [GenPortJ9AHAtomKey.dMB_closed deltaF powerBasis3 D hA o hinj (toχ χe) (PAh D χe hA o) i, hRow]
  unfold dMBA
  refine toQ_compressH' _ _ _ _ (coins_hγ χe) (coins_hρ χe) _ _ ?_
  intro c
  fin_cases c
  · show K6.toQ (zE χe) = _
    exact (zAt_zE χe).symm
  · show K6.toQ 0 = _
    rw [K6.toQ_zero]; rfl
  · show K6.toQ (cellDE (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs D.acs[(i : ℕ)] i).pE.leaf = _
    exact hP3
  · show K6.toQ 0 = _
    rw [K6.toQ_zero]; rfl
  · show K6.toQ (lq (cellDE (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs D.acs[(i : ℕ)] i).j) = _
    rw [cellDE_j, toQ_lq]; rfl

include hacs hinfo hg in
theorem dC_bridge (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (i : Fin D.acs.length) :
    K6.toQ (dCA (coOfA χe) (D.info.getD i AInfo.z)) = hCC D χe hA o i := by
  obtain ⟨-, -, -, h200, h201, h202, h203, -⟩ := newBA_info D hacs hinfo hg χe i
  show _ = HonestA8.dC deltaF powerBasis3 hA (ComplJ8Of.powN o _) o (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
    (PAh D χe hA o) (ComplJ8Of.colAH deltaF powerBasis3 D hA o (toχ χe) (PAh D χe hA o)) (ComplJ8Of.newBA D) i
  rw [GenPortJ9AHAtomKey.dC_closed deltaF powerBasis3 D hA o hinj (toχ χe) (PAh D χe hA o) i,
    h200, h201, h202, h203]
  exact toQ_dCA _ _ _ _ (toQ_γHE χe) (toQ_ρHE χe)

include hacs hinfo hg in
theorem dMI_bridge (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (i : Fin D.acs.length) :
    K6.toQ (dMIA (coOfA χe) (D.info.getD i AInfo.z) i) = hMI D χe hA o i := by
  obtain ⟨-, -, h198, h200, -, -, -, -⟩ := newBA_info D hacs hinfo hg χe i
  show _ = HonestA8.dMI deltaF powerBasis3 hA (ComplJ8Of.powN o _) o (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
    (PAh D χe hA o) (ComplJ8Of.colAH deltaF powerBasis3 D hA o (toχ χe) (PAh D χe hA o)) (ComplJ8Of.newBA D) i
  rw [GenPortJ9AHAtomKey.dMI_closed deltaF powerBasis3 D hA o hinj (toχ χe) (PAh D χe hA o) i,
    h198, h200]
  exact toQ_dMIA _ _ _ _ _ (toQ_γHE χe) (toQ_ρHE χe)

/-! ### Inverses, terms and accumulators -/

theorem iMBL_getD (χe : CoinsE) (j : ℕ) (hj : j < D.acs.length) :
    (iMBL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs).getD j 0 =
      (dMBA (coOfA χe) (zE χe)
        (cellDE (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs D.acs[j] j))⁻¹ :=
  dsE_map_getD _ χe D.acs _ j hj

theorem aisL_map_getD (g : AInfo → K6) (j : ℕ) (hj : j < D.acs.length) :
    ((aisL D.info D.acs.length).map g).getD j 0 = g (D.info.getD j AInfo.z) := by
  simp [aisL, List.getD_eq_getElem?_getD, hj]

include hacs hinfo hg in
theorem iMB_eq (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (i : Fin D.acs.length) :
    K6.toQ ((iMBL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs).getD i 0) = (hMB D χe hA o i)⁻¹ := by
  rw [iMBL_getD D χe i i.2, K6.toQ_inv, dMB_bridge D hacs hg χe hA o hinj i]

include hacs hinfo hg in
theorem iC_eq (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (i : Fin D.acs.length) :
    K6.toQ ((iCL D.info D.acs.length χe).getD i 0) = (hCC D χe hA o i)⁻¹ := by
  rw [aisL_map_getD D _ i i.2, K6.toQ_inv, dC_bridge D hacs hinfo hg χe hA o hinj i]

include hacs hinfo hg in
theorem iMI_eq (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (i : Fin D.acs.length) :
    K6.toQ ((iMIL D.info D.acs.length χe).getD i 0) = (hMI D χe hA o i)⁻¹ := by
  have hl : i.1 < (aisL D.info D.acs.length).length := by simpa [aisL] using i.2
  show K6.toQ ((((aisL D.info D.acs.length).zipIdx 0).map fun (ai, j) => (dMIA (coOfA χe) ai j)⁻¹).getD i 0) = _
  rw [zipIdx_map_getD _ _ i hl]
  simp only [aisL, List.getElem_map, List.getElem_range]
  rw [K6.toQ_inv, dMI_bridge D hacs hinfo hg χe hA o hinj i]

include hacs hinfo hg in
/-- The `mb` term of row `k`. -/
theorem termMB (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (k : ℕ) (hk : k < D.acs.length) :
    K6.toQ ((((iMBL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs).zipIdx 0).map
        fun (v, j) => lq (D.mb.getD j 0) * v).getD k 0) =
      liftQ (K := KC) deltaF (HonestA8.cNat k (ComplJ8Of.newBA D AtomChipHQ.mb)) *
        (HonestA8.dNat deltaF (hMB D χe hA o) k)⁻¹ := by
  have hl : k < (iMBL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs).length := by simpa [dsL_length] using hk
  rw [zipIdx_map_getD _ _ k hl]
  show K6.toQ (lq (D.mb.getD k 0) * (iMBL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs)[k]) = _
  have hI : K6.toQ ((iMBL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs).getD k 0) = (hMB D χe hA o ⟨k, hk⟩)⁻¹ :=
    iMB_eq D hacs hinfo hg χe hA o hinj ⟨k, hk⟩
  rw [← List.getD_eq_getElem _ 0 hl, K6.toQ_mul, toQ_lq, hI]
  unfold HonestA8.cNat HonestA8.dNat
  rw [dif_pos hk, dif_pos hk]
  have h196 : ComplJ8Of.newBA D AtomChipHQ.mb ⟨k, hk⟩ = ((D.mb.getD k 0 : ℕ) : ZMod P) :=
    (newBA_info D hacs hinfo hg χe ⟨k, hk⟩).1
  rw [h196]

include hacs hinfo hg in
theorem termC (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (k : ℕ) (hk : k < D.acs.length) :
    K6.toQ ((((iCL D.info D.acs.length χe).zip (aisL D.info D.acs.length)).map
        fun (v, ai) => (if ai.inc then 1 else 0) * v).getD k 0) =
      liftQ (K := KC) deltaF (HonestA8.cNat k (ComplJ8Of.newBA D AtomChipHQ.inc)) *
        (HonestA8.dNat deltaF (hCC D χe hA o) k)⁻¹ := by
  have hl : k < (iCL D.info D.acs.length χe).length := by simpa using hk
  have hl' : k < (aisL D.info D.acs.length).length := by simpa using hk
  rw [zip_map_getD _ _ _ k hl hl']
  have e1 : (iCL D.info D.acs.length χe)[k] = (iCL D.info D.acs.length χe).getD k 0 :=
    (List.getD_eq_getElem _ 0 hl).symm
  have e2 : (aisL D.info D.acs.length)[k] = D.info.getD k AInfo.z := by
    simp [aisL]
  show K6.toQ ((if (aisL D.info D.acs.length)[k].inc then 1 else 0) * (iCL D.info D.acs.length χe)[k]) = _
  have hI : K6.toQ ((iCL D.info D.acs.length χe).getD k 0) = (hCC D χe hA o ⟨k, hk⟩)⁻¹ :=
    iC_eq D hacs hinfo hg χe hA o hinj ⟨k, hk⟩
  rw [e1, e2, toQ_incMul, hI]
  unfold HonestA8.cNat HonestA8.dNat
  rw [dif_pos hk, dif_pos hk]
  have h197 : ComplJ8Of.newBA D AtomChipHQ.inc ⟨k, hk⟩ = flag (D.info.getD k AInfo.z).inc :=
    (newBA_info D hacs hinfo hg χe ⟨k, hk⟩).2.1
  rw [h197]

include hacs hinfo hg in
theorem termMI (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (k : ℕ) (hk : k < D.acs.length) :
    K6.toQ ((((iMIL D.info D.acs.length χe).zip (aisL D.info D.acs.length)).map
        fun (v, ai) => lq ai.mi * v).getD k 0) =
      liftQ (K := KC) deltaF (HonestA8.cNat k (ComplJ8Of.newBA D AtomChipHQ.mi)) *
        (HonestA8.dNat deltaF (hMI D χe hA o) k)⁻¹ := by
  have hl : k < (iMIL D.info D.acs.length χe).length := by simpa using hk
  have hl' : k < (aisL D.info D.acs.length).length := by simpa using hk
  rw [zip_map_getD _ _ _ k hl hl']
  have e1 : (iMIL D.info D.acs.length χe)[k] = (iMIL D.info D.acs.length χe).getD k 0 :=
    (List.getD_eq_getElem _ 0 hl).symm
  have e2 : (aisL D.info D.acs.length)[k] = D.info.getD k AInfo.z := by
    simp [aisL]
  show K6.toQ (lq (aisL D.info D.acs.length)[k].mi * (iMIL D.info D.acs.length χe)[k]) = _
  have hI : K6.toQ ((iMIL D.info D.acs.length χe).getD k 0) = (hMI D χe hA o ⟨k, hk⟩)⁻¹ :=
    iMI_eq D hacs hinfo hg χe hA o hinj ⟨k, hk⟩
  rw [e1, e2, K6.toQ_mul, hI, toQ_lq]
  unfold HonestA8.cNat HonestA8.dNat
  rw [dif_pos hk, dif_pos hk]
  have h204 : ComplJ8Of.newBA D AtomChipHQ.mi ⟨k, hk⟩ = (((D.info.getD k AInfo.z).mi : ℕ) : ZMod P) :=
    (newBA_info D hacs hinfo hg χe ⟨k, hk⟩).2.2.2.2.2.2.2
  rw [h204]

include hacs hinfo hg in
theorem aMB_eq (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (i : Fin D.acs.length) :
    K6.toQ ((aMBL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs D.mb).getD i 0) =
      HonestA8.accOf deltaF (ComplJ8Of.newBA D AtomChipHQ.mb) (hMB D χe hA o) i := by
  unfold aMBL
  rw [toQ_scanK6_getD _ _ (by simp [dsL_length])]
  unfold HonestA8.accOf
  refine Finset.sum_congr (by simp [dsL_length]) fun k hk => ?_
  have hk' : k < D.acs.length := by have := Finset.mem_range.mp hk; have := i.2; omega
  exact termMB D hacs hinfo hg χe hA o hinj k hk'

include hacs hinfo hg in
theorem aC_eq (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (i : Fin D.acs.length) :
    K6.toQ ((aCL χe D.info D.acs.length).getD i 0) =
      HonestA8.accOf deltaF (ComplJ8Of.newBA D AtomChipHQ.inc) (hCC D χe hA o) i := by
  unfold aCL
  rw [toQ_scanK6_getD _ _ (by simp)]
  unfold HonestA8.accOf
  refine Finset.sum_congr (by simp) fun k hk => ?_
  have hk' : k < D.acs.length := by have := Finset.mem_range.mp hk; have := i.2; omega
  exact termC D hacs hinfo hg χe hA o hinj k hk'

include hacs hinfo hg in
theorem aMI_eq (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (i : Fin D.acs.length) :
    K6.toQ ((aMIL χe D.info D.acs.length).getD i 0) =
      HonestA8.accOf deltaF (ComplJ8Of.newBA D AtomChipHQ.mi) (hMI D χe hA o) i := by
  unfold aMIL
  rw [toQ_scanK6_getD _ _ (by simp)]
  unfold HonestA8.accOf
  refine Finset.sum_congr (by simp) fun k hk => ?_
  have hk' : k < D.acs.length := by have := Finset.mem_range.mp hk; have := i.2; omega
  exact termMI D hacs hinfo hg χe hA o hinj k hk'

/-! ## 4. Roles -/

include hacs hinfo hg in
theorem r6_toQ (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (i : Fin D.acs.length) (s : ℕ) (hs : s < 6) :
    K6.toQ ((r6E (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs D.info D.mb i).getD s 0) =
      (r6H D χe hA o i).getD s 0 := by
  interval_cases s
  · exact iMB_eq D hacs hinfo hg χe hA o hinj i
  · exact aMB_eq D hacs hinfo hg χe hA o hinj i
  · exact iC_eq D hacs hinfo hg χe hA o hinj i
  · exact iMI_eq D hacs hinfo hg χe hA o hinj i
  · exact aMI_eq D hacs hinfo hg χe hA o hinj i
  · exact aC_eq D hacs hinfo hg χe hA o hinj i

include hacs hinfo hg in
/-- **`role_eq`**: the executable `𝕂`-role limbs of row `i` are the honest `roleValA`. -/
theorem role_eq (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (i : Fin D.acs.length) (t : ℕ) (ht : t < 12) :
    K3.toK (rolesE (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs D.info D.mb i t) =
      HonestA8.roleValA deltaF powerBasis3 hA (ComplJ8Of.powN o _) o (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
        (PAh D χe hA o) (ComplJ8Of.colAH deltaF powerBasis3 D hA o (toχ χe) (PAh D χe hA o))
        (ComplJ8Of.newBA D) t i := by
  rw [roleValA_r6 D χe hA o i t ht]
  have hq := r6_toQ D hacs hinfo hg χe hA o hinj i (t / 2) (by omega)
  unfold rolesE
  dsimp only
  by_cases hp : t % 2 = 0
  · rw [if_pos hp, if_pos hp, ← hq, re_toQ]
  · rw [if_neg hp, if_neg hp, ← hq, im_toQ]

include hacs hinfo hg instFR instAR in
/-- **`atomGenE_cols`**: all `349` columns of the executable atom table are the honest `fullCol`. -/
theorem atomGenE_cols (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (i : Fin D.acs.length) (c : ℕ) (hc : c < 349) :
    ((atomGenE (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs D.info D.mb D.mxA D.mhA).1.getD i #[]).getD c 0 =
      fullCol hA (HonestA8.colA deltaF powerBasis3 hA (ComplJ8Of.powN o _) o (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe))
        (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe))
        (ComplJ8Of.colAH deltaF powerBasis3 D hA o (toχ χe) (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe)))
        (ComplJ8Of.newBA D)) c i := by
  by_cases hlo : c < 313
  · exact atomGenE_cols_lo D hacs hg hinfo χe hA o hinj i c hlo
  rw [atomGenE_entry' (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs D.info D.mb D.mxA D.mhA i i.2 c hc,
    atomColD_roles _ _ _ _ _ _ _ _ _ _ _ _ c (by omega) hc]
  have h0 : c ≠ 0 := by omega
  have h1 : c ≠ 1 := by omega
  simp only [fullCol, if_neg h0, if_neg h1, HonestA8.colA, extColF, CellTraceHQ.cellTemplateHQ_width]
  rw [if_neg (show ¬ c < 130 by omega), if_neg (show ¬ c < 205 by omega),
    if_neg (show ¬ c < 238 + (205 - 130) by omega)]
  unfold HonestA8.newFull
  rw [if_neg hlo]
  have hr := role_eq D hacs hinfo hg χe hA o hinj i ((c - 313) / 3) (by omega)
  rw [← hr]
  exact (coord_K _ ((c - 313) % 3) (Nat.mod_lt _ (by norm_num))).symm

/-! ## 5. Publics -/

include hacs hinfo hg instFR instAR in
/-- **`atomGenE_pubs`**: the executable publics are the honest `pubsAOf` (through `K3.toK`). -/
theorem atomGenE_pubs (χe : CoinsE) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o D.acs.length)) (j : ℕ) :
    K3.toK ((atomGenE (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs D.info D.mb D.mxA D.mhA).2 j) =
      ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe) j := by
  rw [atomGenE_pubs_eq]
  obtain ⟨tV, tX, tH, tMB, tC, tMI⟩ := ComplJ8OfAtom.atomTerms deltaF powerBasis3 D hA o (toχ χe)
  have hne : D.acs ≠ [] := List.ne_nil_of_length_pos hA
  have hD1 : D.acs.length - 1 + 1 = D.acs.length := Nat.sub_add_cancel hA
  -- the terminals
  have eV : K6.toQ (lastK6 (Gen.scanK6 ((dsL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs).map
      (vTermD (mvE D.acs (ComplJ8Data.ptrP P D.acs D.rows)))))) =
      Quad.mk _ (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe) 0)
        (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe) 1) := by
    rw [← tV, lastK6_scan _ (by simpa [dsL] using hne)]
    refine Finset.sum_congr (by simp [dsL_length]) fun k hk => ?_
    have hk' : k < D.acs.length := Finset.mem_range.mp hk
    rw [dsE_map_getD _ _ _ _ k (by simpa [dsL_length] using hk')]
    exact toQ_vTermD_D D hacs hg χe k hk'
  have eX : K6.toQ (lastK6 (Gen.scanK6 ((dsL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs).map
      (xTermD D.mxA (Array.replicate D.acs.length 0))))) =
      Quad.mk _ (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe) 2)
        (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe) 3) := by
    rw [← tX, lastK6_scan _ (by simpa [dsL] using hne)]
    refine Finset.sum_congr (by simp [dsL_length]) fun k hk => ?_
    have hk' : k < D.acs.length := Finset.mem_range.mp hk
    rw [dsE_map_getD _ _ _ _ k (by simpa [dsL_length] using hk')]
    exact toQ_xTermD_D D hacs hg χe k hk'
  have eH : K6.toQ (lastK6 (Gen.scanK6 ((dsL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs).map
      (hTermD (mhArr D.acs D.info D.mhA))))) =
      Quad.mk _ (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe) CellHQ.pubHQ)
        (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe) (CellHQ.pubHQ + 1)) := by
    rw [tH]
    have hl : (Gen.scanK6 ((dsL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs).map
        (hTermD (mhArr D.acs D.info D.mhA)))).length = D.acs.length := by
      rw [scanK6_length]; simp [dsL_length]
    rw [lastK6_eq, hl]
    have := ha_eq D hacs hg χe hA o hinj (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe))
      ⟨D.acs.length - 1, by omega⟩
    refine this.trans ?_
    unfold CellTraceHQ.avF
    simp only [Fin.val_mk, hD1]
  have eMB : K6.toQ (lastK6 (aMBL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs D.mb)) =
      Quad.mk _ (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe) AtomChipHQ.pubMB)
        (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe) (AtomChipHQ.pubMB + 1)) := by
    rw [tMB]
    unfold aMBL
    rw [lastK6_scan _ (by simpa [dsL] using hne)]
    refine Finset.sum_congr (by simp [dsL_length]) fun k hk => ?_
    exact termMB D hacs hinfo hg χe hA o hinj k (by simpa [dsL_length] using Finset.mem_range.mp hk)
  have eC : K6.toQ (lastK6 (aCL χe D.info D.acs.length)) =
      Quad.mk _ (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe) AtomChipHQ.pubC)
        (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe) (AtomChipHQ.pubC + 1)) := by
    rw [tC]
    unfold aCL
    rw [lastK6_scan _ (by simpa using hne)]
    refine Finset.sum_congr (by simp) fun k hk => ?_
    exact termC D hacs hinfo hg χe hA o hinj k (Finset.mem_range.mp hk |> fun x => by simpa using x)
  have eMI : K6.toQ (lastK6 (aMIL χe D.info D.acs.length)) =
      Quad.mk _ (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe) AtomChipHQ.pubMI)
        (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe) (AtomChipHQ.pubMI + 1)) := by
    rw [tMI]
    unfold aMIL
    rw [lastK6_scan _ (by simpa using hne)]
    refine Finset.sum_congr (by simp) fun k hk => ?_
    exact termMI D hacs hinfo hg χe hA o hinj k (Finset.mem_range.mp hk |> fun x => by simpa using x)
  have hl : ∀ s, s < 6 → K6.toQ ((pubsL (ComplJ8Data.ptrP P D.acs D.rows) χe D.acs D.info D.mb D.mxA D.mhA).getD s 0) =
      Quad.mk _ (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe) (2 * s))
        (ComplJ8Of.pubsAOf deltaF powerBasis3 D hA o (toχ χe) (2 * s + 1)) := by
    intro s hs
    interval_cases s
    · exact eV
    · exact eX
    · exact eH
    · exact eMB
    · exact eMI
    · exact eC
  unfold pubsE
  by_cases hj : j < 12
  · rw [if_pos hj]
    have hs := hl (j / 2) (by omega)
    by_cases hp : j % 2 = 0
    · rw [if_pos hp, ← re_toQ, hs, Quad.re_mk]
      congr 1; omega
    · rw [if_neg hp, ← im_toQ, hs, Quad.im_mk]
      congr 1; omega
  · rw [if_neg hj, K3.toK_zero]
    unfold ComplJ8Of.pubsAOf
    dsimp only
    rw [if_neg (show ¬ j < 6 by omega), if_neg (show ¬ j < 8 by omega), if_neg (show ¬ j < 10 by omega),
      if_neg (show ¬ j < 12 by omega)]

end Honest

end Pre

/-! ## 6. Interpolant cast -/

theorem interp_cast {m n : ℕ} (e : m = n) (nodes g : Fin n → ZMod P) :
    Lagrange.interpolate Finset.univ (fun i : Fin m => nodes (Fin.cast e i)) (fun i : Fin m => g (Fin.cast e i)) =
      Lagrange.interpolate Finset.univ nodes g := by
  subst e
  rfl

#print axioms toQ_zq
#print axioms lastK6_scan
#print axioms newBA_info
#print axioms dMB_bridge
#print axioms dC_bridge
#print axioms dMI_bridge
#print axioms role_eq
#print axioms atomGenE_cols
#print axioms atomGenE_pubs
#print axioms interp_cast

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtom
