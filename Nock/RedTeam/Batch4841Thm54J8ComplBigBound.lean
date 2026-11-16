/-
  Nock/RedTeam/Batch4841Thm54J8ComplBigBound.lean
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8BigBound
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of

set_option autoImplicit false

namespace Nock.RedTeam.Batch4841

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.V1J8.Gen (combOf lastIdxOf idxOf idxN)
open Nock.Atoms (B limbs)

variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Nock.Jet.Autogen.Tpl} {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

include hgen in
theorem bigBound_complJ8 (hpG : p = Nock.Atoms.p) (hop5 : ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : ComplJ8Of.Rows31 (j8DataOf p Rg Rt hgen)) :
    let D := j8DataOf p Rg Rt hgen
    (∀ a ∈ D.bigs, p ≤ a ∧ a < p + D.rows.size ∧ limbs a = [a + 1 - p, B - 1]) ∧
      (D.dupP && decide (Noun.cell (.atom 0) (combPP p) ∈ ComplJ8Atom.spineL D.bigs)) = false ∧
      D.acs.Nodup ∧ List.count (combPP p) D.acs ≤ 1 ∧
      lastIdxOf D.acs (combPP p) = idxOf D.acs (combPP p) ∧
      (combPP p ∈ D.acs → lastIdxOf D.acs (combPP p) = List.idxOf (combPP p) D.acs) ∧
      rIAP p D.acs = idxN D.acs ∧
      (∀ n ∈ D.acs, idxOf D.acs n = List.idxOf n D.acs) ∧
      ∀ a, rootIdxP p D.acs a = idxOf D.acs (combOf (limbs a)) := by
  have hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31 := by
    have h := h31 (bfsForest [(j8DataOf p Rg Rt hgen).t]).length (by simp [ComplJ8Of.sizesJ8])
    rw [ComplJ8BigBound.data_rows hgen]
    simpa [rowsOfT, j8DataOf] using h
  exact ComplJ8BigBound.bigBound_single hgen hpG (hclA 0) (hclA 1) hRt hop5 hN

#print axioms ComplJ8BigBound.bnd_slot
#print axioms ComplJ8BigBound.bnd_edit
#print axioms ComplJ8BigBound.chain_bnd
#print axioms ComplJ8BigBound.bnd_semS
#print axioms ComplJ8BigBound.bnd_honestRows
#print axioms ComplJ8BigBound.gen_bnd
#print axioms ComplJ8BigBound.bigs_lt
#print axioms ComplJ8BigBound.limbs_two
#print axioms ComplJ8BigBound.spineL_shape
#print axioms ComplJ8BigBound.acsP_two
#print axioms ComplJ8BigBound.acsP_nodup
#print axioms ComplJ8BigBound.lastIdxOf_eq_idxOf
#print axioms ComplJ8BigBound.single_p
#print axioms ComplJ8BigBound.bigBound_single
#print axioms bigBound_complJ8

end Nock.RedTeam.Batch4841
