/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHComp.lean

* `chipOf_n`: `(chipOf tbl).n = tbl.size`;
  * `interpOf_chipOf_compGenX9`: for the generator's compute table `compGenX9 …`, column `d < 137` of
    `interpOf (chipOf rows)` is `polyX9` at the nodes `nodesOf (chipOf rows)` (generic in `c H pd idOf W χe`);
  * `compGenX9_size`: `(compGenX9 …).rows.size = W.length`;
  * `recJ9AX_X`, `recJ9AX_X_n`: `(recJ9AX …).X = chipOf (compGenX9 …).rows` and `.n = N9 t`;
  * `recJ9AX_hdp`: `genJ9AX`'s `H pd idOf` are `j9aDataOf`'s / `idOfA`;
  * **`recJ9AX_toTr_C`**: `(recJ9AX …).toTr.C d = polyX9 … (nodesOf I.X) 137 d` at the honest data.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRun
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCoin

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 rowsOfT9 genX9T)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (W9 N9 N9_def idOfA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData (fieldAx9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains (idOf9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ)
open Nock.V1J9A.GenCompX9
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD (lnClosed cntClosed)
open Nock.NockVMROM.Thm54.VclL.HonestSatX9 (accW9)
open Nock.NockVMROM.Thm54.VclL.HonestTraceX9 (polyX9)
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.GenJ9AX

theorem chipOf_n (tbl : Array (Array (ZMod P))) : (chipOf tbl).n = tbl.size := rfl

theorem compGenX9_size (c : P8PublicClaim) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
    (idOf : ℕ → ℕ) (W : List (NTree LX9)) (χe : CoinsE) :
    (compGenX9 c H pd idOf W χe).rows.size = W.length := by
  rw [compGenX9_rows]
  simp [compTable9]

/-- **`interpOf (chipOf rows)` is `polyX9`** (generic in the data). -/
theorem interpOf_chipOf_compGenX9
    [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
    (c : P8PublicClaim) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (χe : CoinsE) (d : Fin 137) :
    interpOf (chipOf (compGenX9 c H pd idOf W χe).rows) d =
      polyX9 powerBasis3 deltaF H pd idOf W (Example.chalE χe) (pubFinal9 c H pd idOf W χe)
        (lnClosed (K3.toK (χe ⟨13, by decide⟩)))
        (cntClosed (Walk.foCol W) (K3.toK (χe ⟨13, by decide⟩)) (K3.toK (χe ⟨13, by decide⟩)))
        (accW9 (fun u => K3.toK (nodeV9E H pd idOf (χe ⟨14, by decide⟩) u)) W (K3.toK (χe ⟨13, by decide⟩)))
        (nodesOf (chipOf (compGenX9 c H pd idOf W χe).rows)) 137 d := by
  unfold interpOf polyX9
  congr 1
  funext i
  have hi : (i : ℕ) < W.length := by
    have h : (i : ℕ) < (chipOf (compGenX9 c H pd idOf W χe).rows).n := i.2
    exact lt_of_lt_of_eq h ((chipOf_n _).trans (compGenX9_size c H pd idOf W χe))
  exact compGenX9_eq_closed c H pd idOf W χe hi d.2

/-! ## The record -/

/-- The record's compute chip. -/
theorem recJ9AX_X (s f : Noun) (χe : CoinsE) (t : NTree SkelX) (r : Noun) :
    let c : P8PublicClaim := ⟨s, f, r⟩
    let acsL := GenPortJ9.acsRun s f r t
    let cs := cellsOfRoots (rootsOf c (ComplJ8Data.rowsOfT t))
    let H := hdlB cs acsL
    let pt := ptrE acsL (stopEdges (ComplJ8Data.rowsOfT t))
    let pd := HonestPairX.pdX (sxE pt)
    let fx := fieldAx9 P (rowsOfT9 t)
    let idOf := idOf9 P acsL.length H fx
    (recJ9AX s f χe t r).X = chipOf (compGenX9 c H pd idOf (W9 t) χe).rows := rfl

theorem recJ9AX_X_n (s f : Noun) (χe : CoinsE) (t : NTree SkelX) (r : Noun) :
    (recJ9AX s f χe t r).X.n = N9 t := by
  rw [recJ9AX_X, chipOf_n, compGenX9_size, N9_def]

/-- `genJ9AX`'s `H pd idOf` are the honest data's. -/
theorem recJ9AX_hdp {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
    (hnc : callsOf (ComplJ8Data.rowsOfT t) = []) :
    let c : P8PublicClaim := ⟨s, f, r⟩
    let acsL := GenPortJ9.acsRun s f r t
    let cs := cellsOfRoots (rootsOf c (ComplJ8Data.rowsOfT t))
    let H := hdlB cs acsL
    let pt := ptrE acsL (stopEdges (ComplJ8Data.rowsOfT t))
    let pd := HonestPairX.pdX (sxE pt)
    let fx := fieldAx9 P (rowsOfT9 t)
    let idOf := idOf9 P acsL.length H fx
    H = (j9aDataOf P Rg Rt hgen).H ∧ pd = (j9aDataOf P Rg Rt hgen).pd ∧
      idOf = idOfA (p := P) Rt hgen := by
  obtain ⟨-, hcs, hacs⟩ := ComplJ9BClosed.genJ9A_data Rt hgen rfl hnc
  have hacs' : GenPortJ9.acsRun s f r t = (ComplJ8Data.j8DataOf P Rg Rt hgen).acs := hacs
  have hH : hdlB (cellsOfRoots (rootsOf ⟨s, f, r⟩ (ComplJ8Data.rowsOfT t))) (GenPortJ9.acsRun s f r t) =
      (ComplJ8Data.j8DataOf P Rg Rt hgen).H := by
    rw [GenPortJ9A.hdlB_eq_hdlP, hcs, hacs']; rfl
  obtain ⟨-, -, hpd⟩ := GenPortJ9.genJ9A_pointer_data Rt hgen rfl hnc
  dsimp only
  refine ⟨hH, hpd, ?_⟩
  show idOf9 P _ _ _ = idOf9 P _ _ _
  rw [hH, hacs']
  rfl

theorem interp_aux [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
    (c : P8PublicClaim) (DH : Noun → ℕ × ℕ) (Dpd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idA : ℕ → ℕ)
    (t' : NTree SkelX) (χe : CoinsE)
    (d : Fin 137) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (hH : H = DH) (hpd : pd = Dpd) (hid : idOf = idA) (X : ChipIn) (hI : X =
      chipOf (compGenX9 c H pd idOf (W9 t') χe).rows) :
    interpOf X d =
      polyX9 powerBasis3 deltaF DH Dpd idA (W9 t') (Example.chalE χe)
        (pubFinal9 c DH Dpd idA (W9 t') χe)
        (lnClosed (K3.toK (χe ⟨13, by decide⟩)))
        (cntClosed (Walk.foCol (W9 t')) (K3.toK (χe ⟨13, by decide⟩)) (K3.toK (χe ⟨13, by decide⟩)))
        (accW9 (fun u => K3.toK (nodeV9E DH Dpd idA (χe ⟨14, by decide⟩) u)) (W9 t')
          (K3.toK (χe ⟨13, by decide⟩)))
        (nodesOf X) 137 d := by
  subst hH hpd hid hI
  exact interpOf_chipOf_compGenX9 _ _ _ _ _ χe d

/-- **A1**: the executable compute chip's trace polynomials are the honest `polyX9`, at the exec nodes. -/
theorem recJ9AX_toTr_C [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
    {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
    (hnc : callsOf (ComplJ8Data.rowsOfT t) = []) (χe : CoinsE) (d : Fin 137) :
    (recJ9AX s f χe t r).toTr.C d =
      polyX9 powerBasis3 deltaF (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd (idOfA (p := P) Rt hgen)
        (W9 t) (Example.chalE χe) (pubFinal9 ⟨s, f, r⟩ (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
          (idOfA (p := P) Rt hgen) (W9 t) χe)
        (lnClosed (K3.toK (χe ⟨13, by decide⟩)))
        (cntClosed (Walk.foCol (W9 t)) (K3.toK (χe ⟨13, by decide⟩)) (K3.toK (χe ⟨13, by decide⟩)))
        (accW9 (fun u => K3.toK (nodeV9E (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
          (idOfA (p := P) Rt hgen) (χe ⟨14, by decide⟩) u)) (W9 t) (K3.toK (χe ⟨13, by decide⟩)))
        (nodesOf (recJ9AX s f χe t r).X) 137 d := by
  obtain ⟨hH, hpd, hid⟩ := recJ9AX_hdp Rt hgen hnc
  exact interp_aux ⟨s, f, r⟩ (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd (idOfA (p := P) Rt hgen)
    t χe d _ _ _ hH hpd hid _ (recJ9AX_X s f χe t r)

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp.chipOf_n
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp.compGenX9_size
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp.interpOf_chipOf_compGenX9
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp.recJ9AX_X
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp.recJ9AX_X_n
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp.recJ9AX_hdp
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp.interp_aux
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHComp.recJ9AX_toTr_C
