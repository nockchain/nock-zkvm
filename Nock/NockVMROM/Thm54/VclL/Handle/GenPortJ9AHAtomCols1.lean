/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAtomCols1.lean

  The first group of atom-chip columns of the executable data. -/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRow

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRow

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomCols1

/-! ## 1. Fields of `cellDE` -/

section Fields
variable (pt : Noun → ℕ) (k : Co) (y : K6) (cs : List Noun) (n : Noun) (j : ℕ)

theorem cellDE_l' : (cellDE pt k y cs n j).l = hdN' n := by
  unfold cellDE; dsimp only; split <;> rfl
theorem cellDE_r' : (cellDE pt k y cs n j).r = tlN' n := by
  unfold cellDE; dsimp only; split <;> rfl
theorem cellDE_mu : (cellDE pt k y cs n j).mu = n.internal := by
  unfold cellDE; dsimp only; split <;> rfl
theorem cellDE_muL : (cellDE pt k y cs n j).muL = (hdN' n).internal := by
  unfold cellDE; dsimp only; split <;> rfl
theorem cellDE_muR : (cellDE pt k y cs n j).muR = (tlN' n).internal := by
  unfold cellDE; dsimp only; split <;> rfl
theorem cellDE_idL (hl : (hdN' n).isCell = false) : (cellDE pt k y cs n j).idL = 0 := by
  unfold cellDE; dsimp only; split <;> simp [cellD, hl]
theorem cellDE_idR_cell (hr : (tlN' n).isCell = true) : (cellDE pt k y cs n j).idR = pt n := by
  unfold cellDE; dsimp only; rw [if_pos hr]
theorem cellDE_idR_atom (hr : (tlN' n).isCell = false) : (cellDE pt k y cs n j).idR = 0 := by
  unfold cellDE; dsimp only; split <;> simp_all [cellD]

end Fields

/-! ## 2. Base columns `2 .. 128` -/

theorem getD_rep (m j : ℕ) : (Array.replicate m 0).getD j 0 = 0 := replicate_getD m j

section Base
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]

/-- The rank bits `18 .. 127`. -/
theorem rankBit_col (mu k : ℕ) :
    (((Nock.V1J8.Gen.rankBit mu k : ℕ)) : ZMod P) =
      Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.rankBit (F := ZMod P) mu k := by
  unfold Nock.V1J8.Gen.rankBit Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.rankBit two62
  split_ifs <;> simp

section RBMore
variable (z : KQ) (cs : List Noun) (mv mx : ℕ → ℕ) (pt : Noun → ℕ) (n : Noun) (j : ℕ)

theorem RB_loL : (RB z cs mv mx pt n j).loL = (((hdN' n).internal % 2 ^ 62 : ℕ) : ZMod P) := by
  rw [hdN'_eq]; rfl
theorem RB_hiL : (RB z cs mv mx pt n j).hiL = (((hdN' n).internal / 2 ^ 62 : ℕ) : ZMod P) := by
  rw [hdN'_eq]; rfl
theorem RB_carry : (RB z cs mv mx pt n j).carry =
    ((((hdN' n).internal % 2 ^ 62 + (tlN' n).internal % 2 ^ 62 + 1) / 2 ^ 62 : ℕ) : ZMod P) := by
  rw [hdN'_eq, tlN'_eq]; rfl
theorem RB_idL (hn : AtomRow n) : (RB z cs mv mx pt n j).idL = 0 := by
  obtain ⟨a, t, rfl, ha, ht⟩ := hn.shape
  simp [RB, ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowB, ComplJ8Cell.idOf, hdN, Noun.isCell]
theorem RB_aL (hn : AtomRow n) : (RB z cs mv mx pt n j).aL = ((atomV (hdN' n) : ℕ) : ZMod P) := by
  obtain ⟨a, t, rfl, ha, ht⟩ := hn.shape
  simp [RB, ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowB, ComplJ8Cell.aOf, ComplJ8Cell.isBig, hdN, hdN', atomV]
theorem RB_aR (hn : AtomRow n) : (RB z cs mv mx pt n j).aR = ((atomV (tlN' n) : ℕ) : ZMod P) := by
  obtain ⟨a, t, rfl, ha, ht⟩ := hn.shape
  cases t <;>
    simp [RB, ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowB, ComplJ8Cell.aOf, ComplJ8Cell.isBig, tlN, tlN', atomV,
      Noun.isCell]
theorem RB_idR_atom (hr : (tlN' n).isCell = false) : (RB z cs mv mx pt n j).idR = 0 := by
  have : (tlN n).isCell = false := by rw [← tlN'_eq]; exact hr
  simp [RB, ComplJ8Cell.cellRowBP, ComplJ8Cell.idRP, ComplJ8Cell.idOf, this]
end RBMore

/-- **`atomBase_RB`**: the executable base columns of an atom-table row against the honest `CellVals.base`. -/
theorem atomBase_RB (pt : Noun → ℕ) (k : Co) (y : K6) (cs : List Noun) (mv mx : ℕ → ℕ) (n : Noun) (j : ℕ)
    (z : KQ) (hn : AtomRow n) (mvX mxX mx1X : Array ℕ) (hmv : mvX.getD j 0 = mv j) (hmx : mxX.getD j 0 = mx j)
    (hmx1 : mx1X.getD j 0 = 0) (c : ℕ) (h2 : 2 ≤ c) (hc : c < 129) :
    cellBaseD mvX mxX mx1X (cellDE pt k y cs n j) c = (RB z cs mv mx pt n j).base c := by
  have hl : (hdN' n).isCell = false := by
    obtain ⟨a, t, rfl, -, -⟩ := hn.shape; rfl
  rcases (show (2 ≤ c ∧ c < 18) ∨ c = 128 ∨ (18 ≤ c ∧ c < 128) by omega) with hr | hr | hr
  · obtain ⟨_, hr⟩ := hr
    have hmv' : ((mvX.getD j 0 : ℕ) : ZMod P) = (mv j : ZMod P) := by rw [hmv]
    have hmx' : ((mxX.getD j 0 : ℕ) : ZMod P) = (mx j : ZMod P) := by rw [hmx]
    have hLo := RB_lo z cs mv mx pt n j
    have hHi := RB_hi z cs mv mx pt n j
    have hLoL := RB_loL z cs mv mx pt n j
    have hHiL := RB_hiL z cs mv mx pt n j
    have hLoR := RB_loR z cs mv mx pt n j
    have hHiR := RB_hiR z cs mv mx pt n j
    have hCar := RB_carry z cs mv mx pt n j
    have hIdL := RB_idL z cs mv mx pt n j hn
    have hAL := RB_aL z cs mv mx pt n j hn
    have hAR := RB_aR z cs mv mx pt n j hn
    have hWL := RB_wL z cs mv mx pt n j hn
    have hIx := RB_idx z cs mv mx pt n j
    have hMv := RB_mv z cs mv mx pt n j
    have hMx := RB_mx z cs mv mx pt n j
    have e0 := cellDE_idL pt k y cs n j hl
    unfold cellBaseD
    simp only [cellDE_j, cellDE_l', cellDE_r', cellDE_mu, cellDE_muL, cellDE_muR, e0]
    by_cases hrc : (tlN' n).isCell = true
    · have e1 := cellDE_idR_cell pt k y cs n j hrc
      have hID := RB_idR_cell z cs mv mx pt n j hrc
      have hWR := RB_wR_cell z cs mv mx pt n j hrc
      interval_cases c <;>
        simp [CellVals.base, flag, hl, hrc, e1, hID, hWR, hWL, hIdL, hAL, hAR, hLo, hHi, hLoL, hHiL, hLoR, hHiR,
          hCar, hIx, hMv, hMx, hmv, hmx, two62]
    · have hrc' : (tlN' n).isCell = false := by simpa using hrc
      have e1 := cellDE_idR_atom pt k y cs n j hrc'
      have hID := RB_idR_atom z cs mv mx pt n j hrc'
      have hWR := RB_wR_atom z cs mv mx pt n j hrc'
      interval_cases c <;>
        simp [CellVals.base, flag, hl, hrc', e1, hID, hWR, hWL, hIdL, hAL, hAR, hLo, hHi, hLoL, hHiL, hLoR, hHiR,
          hCar, hIx, hMv, hMx, hmv, hmx, two62]
  · subst hr
    show ((mx1X.getD (cellDE pt k y cs n j).j 0 : ℕ) : ZMod P) = _
    rw [cellDE_j, hmx1]
    show _ = ((0 : ℕ) : ZMod P)
    rfl
  · obtain ⟨h18, h128⟩ := hr
    unfold cellBaseD
    simp only [cellDE_mu]
    simp only [if_neg (show c ≠ 2 by omega), if_neg (show c ≠ 3 by omega), if_neg (show c ≠ 4 by omega),
      if_neg (show c ≠ 5 by omega), if_neg (show c ≠ 6 by omega), if_neg (show c ≠ 7 by omega),
      if_neg (show c ≠ 8 by omega), if_neg (show c ≠ 9 by omega), if_neg (show c ≠ 10 by omega),
      if_neg (show c ≠ 11 by omega), if_neg (show c ≠ 12 by omega), if_neg (show c ≠ 13 by omega),
      if_neg (show c ≠ 14 by omega), if_neg (show c ≠ 15 by omega), if_neg (show c ≠ 16 by omega),
      if_neg (show c ≠ 17 by omega), if_neg (show c ≠ 128 by omega), if_pos h128, cellDE_j, CellVals.base]
    exact rankBit_col _ _

end Base

/-! ## 3. Generic `D`-free statements (the table `acsL`, `info`, `mb`) -/

section Core
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]

theorem bitZ_eq (n i : ℕ) : bitZ n i = ComplJ8Atom.bitF (F := ZMod P) n i := rfl

theorem flag_nat (b : Bool) : flag b = ((if b = true then 1 else 0 : ℕ) : ZMod P) := by
  cases b <;> simp [flag]

theorem atomV_aR (r : Noun) : (if r.isCell then 0 else atomV r) = atomV r := by
  cases r <;> simp [Noun.isCell, atomV]

/-- **`atomBase_core`**: columns `2 .. 128` of the executable atom row `i`. -/
theorem atomBase_core (acsL : List Noun) (bigs : List ℕ) (dupP : Bool) (hbigs : ∀ a ∈ bigs, P ≤ a)
    (hacs : acsL = ComplJ8Data.acsP P bigs dupP) (mvX mxX mx1X : Array ℕ) (mv mx : ℕ → ℕ)
    (pt : Noun → ℕ) (k : Co) (y : K6) (z : KQ) (i : ℕ) (hi : i < acsL.length)
    (hmv : mvX.getD i 0 = mv i) (hmx : mxX.getD i 0 = mx i) (hmx1 : mx1X.getD i 0 = 0)
    (mh : Array ℕ) (va xa ha : K6) (c : ℕ) (h2 : 2 ≤ c) (hc : c < 129) :
    cellColD acsL.length mvX mxX mx1X mh (cellDE pt k y acsL acsL[i] i) va xa ha c =
      (RB z acsL mv mx pt acsL[i] i).base c := by
  have hn : AtomRow acsL[i] := atomRow_of_acs bigs dupP hbigs _ (hacs ▸ List.getElem_mem hi)
  unfold cellColD
  rw [if_neg (show c ≠ 0 by omega), if_neg (show c ≠ 1 by omega), if_pos hc]
  exact atomBase_RB pt k y acsL mv mx _ i z hn mvX mxX mx1X hmv hmx hmx1 c h2 hc

/-- Column `129`: the handle multiplicity. -/
theorem atom129_core (acsL : List Noun) (pt : Noun → ℕ) (k : Co) (y : K6) (n : Noun) (i : ℕ) (m : ℕ)
    (mvX mxX mx1X mh : Array ℕ) (va xa ha : K6) (hmh : mh.getD i 0 = m) :
    cellColD acsL.length mvX mxX mx1X mh (cellDE pt k y acsL n i) va xa ha 129 = (m : ZMod P) := by
  unfold cellColD
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl, cellDE_j, hmh]

/-- **`atomNew_core`**: columns `130 .. 204` of the executable atom row `i` (the bits, inverses, `mb`, `info`
fields) against `ComplJ8Atom.newOf` at the honest table. -/
theorem atomNew_core (bigs : List ℕ) (dupP : Bool) (rows : Array Nock.Edit.GenX.RowNX) (mb : Array ℕ)
    (hg : ComplJ8Atom.GenHyp bigs dupP rows mb) (acsL : List Noun) (info : Array AInfo)
    (hacs : acsL = ComplJ8Data.acsP P bigs dupP) (hinfo : info = ComplJ8Data.infoOfP P acsL rows)
    (pt : Noun → ℕ) (k : Co) (y : K6) (i : Fin acsL.length) (Dn : ℕ) (mvX mxX mx1X mh : Array ℕ)
    (va xa ha : K6) (roles : ℕ → K3) (c : ℕ) (h1 : 130 ≤ c) (h2 : c < 205) :
    atomColD Dn mvX mxX mx1X mh (mb.getD i 0) (cellDE pt k y acsL acsL[i] i) va xa ha
        (info.getD i AInfo.z) roles c =
      ComplJ8Atom.newOf (F := ZMod P) (n := acsL.length)
        (ComplJ8Atom.tabOf acsL info mb rows).row c i := by
  have hi : (i : ℕ) < acsL.length := i.2
  subst hinfo
  have hr := ComplJ8Atom.row_info bigs dupP rows mb hg i
  have hc := ComplJ8Atom.row_cell bigs dupP rows mb hg (ComplJ8Data.infoOfP P acsL rows) i
    (by subst hacs; exact hi)
  subst hacs
  dsimp only at hr hc
  obtain ⟨hinc, hconv, hcout, hidxO, hlO, hkRO, hvRO, hmi, hmb⟩ := hr
  obtain ⟨-, haL, haR, hwL, hwR, -⟩ := hc
  have hlE := cellDE_l' pt k y (ComplJ8Data.acsP P bigs dupP) (ComplJ8Data.acsP P bigs dupP)[(i : ℕ)] i
  have hrE := cellDE_r' pt k y (ComplJ8Data.acsP P bigs dupP) (ComplJ8Data.acsP P bigs dupP)[(i : ℕ)] i
  simp only [atomColD, ComplJ8Atom.newOf, hlE, hrE]
  rw [atomV_aR]
  have hrc := atomV_aR (tlN' (ComplJ8Data.acsP P bigs dupP)[(i : ℕ)])
  by_cases hrcell : (tlN' (ComplJ8Data.acsP P bigs dupP)[(i : ℕ)]).isCell = true
  · interval_cases c <;>
      simp [cellDE_l', cellDE_r', bitZ_eq, flag_nat, haL, haR, hwR, hrcell, hinc, hconv, hcout, hidxO, hlO, hkRO, hvRO, hmi, hmb]
  · have hrcell' : (tlN' (ComplJ8Data.acsP P bigs dupP)[(i : ℕ)]).isCell = false := by simpa using hrcell
    interval_cases c <;>
      simp [cellDE_l', cellDE_r', bitZ_eq, flag_nat, haL, haR, hwR, hrcell', hinc, hconv, hcout, hidxO, hlO, hkRO, hvRO, hmi, hmb]

end Core

/-! ## 4. At the generic data `D` -/

section DData
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
  (D : ComplJ8Data.J8Data P Rg fuel s f r)
  (hacs : D.acs = ComplJ8Data.acsP P D.bigs D.dupP) (hinfo : D.info = ComplJ8Data.infoOfP P D.acs D.rows)
  (hg : ComplJ8Atom.GenHyp D.bigs D.dupP D.rows D.mb)

include hacs hg in
/-- **`atomBase_eq`**: columns `2 .. 128` of the executable atom row `i` are the honest `base` columns of
`ComplJ8Of.aRows` (here at an arbitrary coin `z`: the base columns do not depend on it). -/
theorem atomBase_eq (χe : CoinsE) (z : KQ) (i : Fin D.acs.length)
    (mh : Array ℕ) (va xa ha : K6) (ai : AInfo) (roles : ℕ → K3) (c : ℕ) (h2 : 2 ≤ c) (hc : c < 129) :
    atomColD D.acs.length (mvE D.acs (ComplJ8Data.ptrP P D.acs D.rows)) D.mxA
        (Array.replicate D.acs.length 0) mh (D.mb.getD i 0)
        (cellDE (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs D.acs[i] i) va xa ha ai roles c =
      (ComplJ8Cell.cellRowsBP deltaF z (fun _ => none) D.acs (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D)
        (fun _ => 0) (ComplJ8Data.ptrP P D.acs D.rows) i).base c := by
  have hlt : (i : ℕ) < D.acs.length := i.2
  rw [ComplJ8Cell.cellRowsBP_getElem _ _ _ _ _ _ _ hlt]
  have h := atomBase_core D.acs D.bigs D.dupP hg.big hacs (mvE D.acs (ComplJ8Data.ptrP P D.acs D.rows)) D.mxA
    (Array.replicate D.acs.length 0) (ComplJ8Of.mvA D) (ComplJ8Of.mxAF D) (ComplJ8Data.ptrP P D.acs D.rows)
    (coOfA χe) (yE χe) z i hlt (mvE_getD_mvA D hlt) rfl (replicate_getD _ _) mh va xa ha c h2 hc
  unfold atomColD
  rw [if_pos (show c < 130 by omega)]
  exact h

/-- **`atom129`**: column `129` is `mhvA D i`. -/
theorem atom129 (χe : CoinsE) (i : Fin D.acs.length) (va xa ha : K6) (ai : AInfo) (roles : ℕ → K3) :
    atomColD D.acs.length (mvE D.acs (ComplJ8Data.ptrP P D.acs D.rows)) D.mxA
        (Array.replicate D.acs.length 0)
        ((Array.range D.acs.length).map fun j => D.mhA.getD j 0 + (D.info.getD j AInfo.z).mhx) (D.mb.getD i 0)
        (cellDE (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs D.acs[i] i) va xa ha ai roles 129 =
      ComplJ8Of.mhvA D i := by
  unfold atomColD
  rw [if_pos (show 129 < 130 by omega)]
  rw [atom129_core D.acs _ _ _ _ i (ComplJ8Of.mhAF D i) _ _ _ _ va xa ha (mh_getD D i.2)]

include hacs hinfo hg in
/-- **`atomNew_eq`**: columns `130 .. 204` of the executable atom row `i` are `newBA D`. -/
theorem atomNew_eq (χe : CoinsE) (i : Fin D.acs.length) (mh : Array ℕ) (va xa ha : K6) (roles : ℕ → K3)
    (c : ℕ) (h1 : 130 ≤ c) (h2 : c < 205) :
    atomColD D.acs.length (mvE D.acs (ComplJ8Data.ptrP P D.acs D.rows)) D.mxA
        (Array.replicate D.acs.length 0) mh (D.mb.getD i 0)
        (cellDE (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) D.acs D.acs[i] i) va xa ha
        (D.info.getD i AInfo.z) roles c = ComplJ8Of.newBA D c i :=
  atomNew_core D.bigs D.dupP D.rows D.mb hg D.acs D.info hacs hinfo _ (coOfA χe) (yE χe) i _ _ _ _ mh va xa ha
    roles c h1 h2

end DData

#print axioms atomBase_RB
#print axioms atomBase_core
#print axioms atom129_core
#print axioms atomNew_core
#print axioms atomBase_eq
#print axioms atom129
#print axioms atomNew_eq

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomCols1
