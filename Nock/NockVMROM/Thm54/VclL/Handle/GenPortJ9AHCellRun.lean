/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHCellRun.lean

  The cell chip at the executable record, via the projections `GenPortJ9AHProj.recX_C/recX_M_pubsC` (never unfolds `recJ9AX`):

  * data equalities of the let-terms with `j9aDataOf`'s fields;
  * `recJ9AX_C`, `recJ9AX_pubsC`;
  * **`genJ9AX_cell_n`**, **`genJ9AX_cell_cols`**, **`genJ9AX_cell_pubs`**, **`genJ9AX_cell_interp`** (corrected form:
    `cellTrME` at the executable nodes, any orbit / publics).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCell
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellRun

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellRow
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCell
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf cellsA_pos)
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.V1J9A Nock.V1J9A.GenJ9AX

section Run
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hnc : callsOf (ComplJ8Data.rowsOfT t) = [])
include hnc

/-! ## 1. Data equalities -/

theorem cs_eq (χe : CoinsE) :
    csJ s f χe (RnOf t r) = (j9aDataOf P Rg Rt hgen).cells :=
  (ComplJ9BClosed.genJ9A_data Rt hgen rfl hnc).2.1

theorem acs_eq (χe : CoinsE) :
    acsLJ s f χe (RnOf t r) = (j9aDataOf P Rg Rt hgen).acs :=
  (ComplJ9BClosed.genJ9A_data Rt hgen rfl hnc).2.2

theorem mv_eq (χe : CoinsE) :
    mvJ s f χe (RnOf t r) = (j9aDataOf P Rg Rt hgen).mv := by
  have key : ∀ (m : Array ℕ) (idx : ℕ → ℕ),
      mvPins m (((callsOf (ComplJ8Data.rowsOfT t)).map Prod.fst).dedup) idx = m := by
    intro m idx
    rw [hnc]; rfl
  show mvCounts (csJ s f χe (RnOf t r)) ⟨s, f, r⟩ = mvPins _ _ _
  rw [key]
  exact congrArg (fun cs => mvCounts cs ⟨s, f, r⟩) (cs_eq Rt hgen hnc χe)

theorem mx_mh_eq (χe : CoinsE) :
    mxJ s f χe (RnOf t r) = (j9aDataOf P Rg Rt hgen).mx ∧
      mhJ s f χe (RnOf t r) = (j9aDataOf P Rg Rt hgen).mh := by
  have h := GenPortJ9A.genJ9AX_data (p := P) Rt hgen rfl hnc χe
  dsimp only at h
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem hcs_DA (χe : CoinsE) : ∀ c ∈ (j9aDataOf P Rg Rt hgen).cells, c.isCell = true := by
  rw [← cs_eq Rt hgen hnc χe]
  exact fun c hc => (ComplJ8Walk.cellsOfRoots_mem _ c hc).1

theorem hcl_DA (χe : CoinsE) : ComplJ8Data.ClP (j9aDataOf P Rg Rt hgen).cells [] := by
  rw [← cs_eq Rt hgen hnc χe]
  exact ComplJ8Data.cells_closed _

/-- The executable cell table and publics are `cellGenB` at `DA`'s data. -/
theorem cRPJ_eq (χe : CoinsE) :
    cRPJ s f χe (RnOf t r) =
      cellGenB (coOf χe) (yE χe) (hdlB (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs)
        (bigIdOf (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells
        (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx
        (Array.replicate (j9aDataOf P Rg Rt hgen).cells.length 0) (j9aDataOf P Rg Rt hgen).mh := by
  obtain ⟨hmx, hmh⟩ := mx_mh_eq Rt hgen hnc χe
  unfold cRPJ kJ mx1J HJ
  rw [mv_eq Rt hgen hnc χe, hmx, hmh, cs_eq Rt hgen hnc χe, acs_eq Rt hgen hnc χe]

theorem recJ9AX_C (χe : CoinsE) :
    (recJ9AX s f χe t r).C =
      chipOf (cellGenB (coOf χe) (yE χe) (hdlB (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs)
        (bigIdOf (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells
        (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx
        (Array.replicate (j9aDataOf P Rg Rt hgen).cells.length 0) (j9aDataOf P Rg Rt hgen).mh).1 := by
  rw [recX_C, cRPJ_eq Rt hgen hnc χe]

theorem recJ9AX_pubsC (χe : CoinsE) :
    (recJ9AX s f χe t r).M.pubsC =
      (cellGenB (coOf χe) (yE χe) (hdlB (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs)
        (bigIdOf (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells
        (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx
        (Array.replicate (j9aDataOf P Rg Rt hgen).cells.length 0) (j9aDataOf P Rg Rt hgen).mh).2 := by
  rw [recX_M_pubsC, cRPJ_eq Rt hgen hnc χe]

/-! ## 2. The final statements -/

theorem genJ9AX_cell_n (χe : CoinsE) :
    (recJ9AX s f χe t r).C.n = (j9aDataOf P Rg Rt hgen).cells.length := by
  rw [recJ9AX_C Rt hgen hnc χe]
  exact cellGenB_size _ _ _ _ _ _ _ _ _

theorem genJ9AX_cell_cols (χe : CoinsE) (i : Fin (recJ9AX s f χe t r).C.n) (c : ℕ) (hc : c < 242)
    (nodes : Fin (j9aDataOf P Rg Rt hgen).cells.length → ZMod P) (hinj : Function.Injective nodes) {h : ℕ}
    (orbit : StrictOrbitDomain (ZMod P) 3 h) (pubs : ℕ → KC) :
    (recJ9AX s f χe t r).C.cols c i =
      fullCol (cellsA_pos Rt hgen)
        (HonestKW.colW deltaF powerBasis3
          (cellCol deltaF powerBasis3 (VB χe (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs
            (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx))
          (mhv (j9aDataOf P Rg Rt hgen).mh)
          (ComplJ8Cell.kbLB (ComplJ8Data.bigIdOfP P (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells)
          (ComplJ8Cell.kbRB (ComplJ8Data.bigIdOfP P (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells)
          (HonestKW.ivW deltaF powerBasis3 (cellsA_pos Rt hgen) nodes orbit (chalsMJ8 deltaF (toχ χe)) pubs
            (cellCol deltaF powerBasis3 (VB χe (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs
              (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx))
            (mhv (j9aDataOf P Rg Rt hgen).mh)
            (ComplJ8Cell.kbLB (ComplJ8Data.bigIdOfP P (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells)
            (ComplJ8Cell.kbRB (ComplJ8Data.bigIdOfP P (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells))
          (HonestKW.avW deltaF powerBasis3 (cellsA_pos Rt hgen) nodes orbit (chalsMJ8 deltaF (toχ χe)) pubs
            (cellCol deltaF powerBasis3 (VB χe (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs
              (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx))
            (mhv (j9aDataOf P Rg Rt hgen).mh)
            (ComplJ8Cell.kbLB (ComplJ8Data.bigIdOfP P (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells)
            (ComplJ8Cell.kbRB (ComplJ8Data.bigIdOfP P (j9aDataOf P Rg Rt hgen).acs) (j9aDataOf P Rg Rt hgen).cells)))
        c (Fin.cast (genJ9AX_cell_n Rt hgen hnc χe) i) := by
  have hcg := cellGenB_cols χe (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs
    (hcs_DA Rt hgen hnc χe) (hcl_DA Rt hgen hnc χe) (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx
    (j9aDataOf P Rg Rt hgen).mh (cellsA_pos Rt hgen) rfl nodes hinj orbit pubs
    (Fin.cast (genJ9AX_cell_n Rt hgen hnc χe) i) c hc
  rw [← hcg]
  show (((cRPJ s f χe (RnOf t r)).1.getD (i : ℕ) #[]).getD c 0) = _
  rw [cRPJ_eq Rt hgen hnc χe]
  rfl

theorem genJ9AX_cell_pubs (χe : CoinsE) (hF : ComplJ8Of.DvdOK (j9aDataOf P Rg Rt hgen)) (j : ℕ) :
    K3.toK ((recJ9AX s f χe t r).M.pubsC j) =
      ComplJ8Of.pubsCOf deltaF powerBasis3 (j9aDataOf P Rg Rt hgen) (cellsA_pos Rt hgen)
        (ComplJ8Of.orbJ8 (j9aDataOf P Rg Rt hgen) hF) (toχ χe) j := by
  rw [recJ9AX_pubsC Rt hgen hnc χe]
  have hmem : (j9aDataOf P Rg Rt hgen).cells.length ∈ ComplJ8Of.sizesJ8 (j9aDataOf P Rg Rt hgen) := by
    simp [ComplJ8Of.sizesJ8]
  have hinj : Function.Injective (ComplJ8Of.powN (ComplJ8Of.orbJ8 (j9aDataOf P Rg Rt hgen) hF)
      (j9aDataOf P Rg Rt hgen).cells.length) :=
    (ComplJ8Of.powN_ok _ (ComplJ8Of.le_two_pow_ht _ hmem)).1
  exact cellGenB_pubs χe (j9aDataOf P Rg Rt hgen).cells (j9aDataOf P Rg Rt hgen).acs
    (hcs_DA Rt hgen hnc χe) (hcl_DA Rt hgen hnc χe) (j9aDataOf P Rg Rt hgen).mv (j9aDataOf P Rg Rt hgen).mx
    (j9aDataOf P Rg Rt hgen).mh (j9aDataOf P Rg Rt hgen) rfl rfl rfl rfl rfl (cellsA_pos Rt hgen)
    (ComplJ8Of.orbJ8 (j9aDataOf P Rg Rt hgen) hF) hinj j

theorem genJ9AX_cell_interp (χe : CoinsE) (hinj : Function.Injective (nodesOf (recJ9AX s f χe t r).C)) {h : ℕ}
    (orbit : StrictOrbitDomain (ZMod P) 3 h) (pubsF : Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC → ℕ → KC) (j : ℕ) (hj : j < 242) :
    interpOf (recJ9AX s f χe t r).C j =
      ComplJ8Enc.cellTrME deltaF powerBasis3 (cellsA_pos Rt hgen)
        (fun i => nodesOf (recJ9AX s f χe t r).C (Fin.cast (genJ9AX_cell_n Rt hgen hnc χe).symm i))
        orbit (chalsMJ8 deltaF) pubsF (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.zJ deltaF)
        (ComplJ8Of.encR deltaF) (ComplJ8Of.bigOf (j9aDataOf P Rg Rt hgen)) (j9aDataOf P Rg Rt hgen).cells
        (ComplJ8Of.mvF (j9aDataOf P Rg Rt hgen)) (ComplJ8Of.mxF (j9aDataOf P Rg Rt hgen)) (fun _ => 0)
        (ComplJ8Of.mhF (j9aDataOf P Rg Rt hgen)) (toχ χe) ⟨j, hj⟩ := by
  have hn := genJ9AX_cell_n Rt hgen hnc χe
  unfold interpOf
  rw [interp_cast hn]
  unfold ComplJ8Enc.cellTrME honestQ
  refine congrArg (Lagrange.interpolate Finset.univ (nodesOf (recJ9AX s f χe t r).C ∘ Fin.cast hn.symm)) ?_
  funext i'
  exact genJ9AX_cell_cols Rt hgen hnc χe (Fin.cast hn.symm i') j hj
    (fun i => nodesOf (recJ9AX s f χe t r).C (Fin.cast hn.symm i))
    (hinj.comp (Fin.cast_injective _)) orbit (pubsF (toχ χe))

end Run

#print axioms cs_eq
#print axioms acs_eq
#print axioms mv_eq
#print axioms mx_mh_eq
#print axioms hcs_DA
#print axioms hcl_DA
#print axioms cRPJ_eq
#print axioms recJ9AX_C
#print axioms recJ9AX_pubsC
#print axioms genJ9AX_cell_n
#print axioms genJ9AX_cell_cols
#print axioms genJ9AX_cell_pubs
#print axioms genJ9AX_cell_interp

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellRun
