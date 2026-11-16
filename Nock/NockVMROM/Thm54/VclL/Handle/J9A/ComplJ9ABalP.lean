/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalP.lean

`hGpA`: `ρ 4 + (axis path public) = (walk handle provide)`, for every good coin.  Assembly:
  * `ρ 4` is `Σ Wp` over `walkReadsX9` (`ComplJ9ABalPC.rho4_total`);
  * the axis path public is `axSumP` (present) or `0` (absent), and `axSumP = Σ Tw = Σ Wp` over `axChainReadsK9`
    (`axSumP_eq_run`, `Tw_eq_Wp`);
  * the walk provide is `Σ Wp` over `readsA = walkReadsX9 ++ axChainReadsK9` (`walkA_run`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalPC
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalPW
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalPAx

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalP

noncomputable section

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (rowsOfT9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A WalkDepthOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (BRun9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf readsA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG (Wp)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalPAx (Tw)
open Nock.Jet.Autogen (Tpl)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}

set_option maxHeartbeats 4000000 in
/-- **`hGp` at the J-9 A run**: the compute path public plus the axis path public is the cell walk's handle provide,
at every good coin (present and absent axis chip). -/
theorem hGpA (hgen : genX Rg.R fuel s f = some (t, r)) (hpG : p = Nock.Atoms.p)
    (h31A : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))
    (hax9 : ProgAxOK9A p t) (hop5 : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8.ProgOp5OK p t)
    (hlen : (j9aDataOf p Rg Rt hgen).cells.length < p)
    (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t)) (χ : Coins frameJ8 K)
    (hχ : (BRun9A δ b Rt hgen hpG h31A).Good χ) :
    ((BRun9A δ b Rt hgen hpG h31A).M χ).ρ 4 +
        Quad.mk (algebraMap (ZMod p) K δ)
          (((BRun9A δ b Rt hgen hpG h31A).M χ).pubsX Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXp)
          (((BRun9A δ b Rt hgen hpG h31A).M χ).pubsX (Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXp + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) (((BRun9A δ b Rt hgen hpG h31A).M χ).pubsW WalkHQ.pubPQ)
        (((BRun9A δ b Rt hgen hpG h31A).M χ).pubsW (WalkHQ.pubPQ + 1)) := by
  have hp62 : 2 ^ 62 < p := lt_trans (by norm_num) (ComplJ9AChains.hp63_of_G hpG)
  rw [ComplJ9ABalPC.rho4_total δ b Rt hgen hpG h31A hax9 hop5 hlen hwalk9 χ hχ,
    ComplJ9ABalPW.walkA_run δ b Rt hgen hpG h31A hlen hp62 hwalk9 χ,
    ComplJ9ADataRec.j9aDataOf_reads]
  have hX : Quad.mk (algebraMap (ZMod p) K δ)
      (((BRun9A δ b Rt hgen hpG h31A).M χ).pubsX Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXp)
      (((BRun9A δ b Rt hgen hpG h31A).M χ).pubsX (Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXp + 1)) =
      ((Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun.axChainReadsK9 (rowsOfT9 t)).map
        (Tw δ (j9aDataOf p Rg Rt hgen).H χ)).sum := by
    show Quad.mk _ (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.pubsXA δ Rt hgen χ _)
      (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.pubsXA δ Rt hgen χ _) = _
    unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.pubsXA
    by_cases h : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.axOnA t = true
    · rw [dif_pos h, ComplJ9AChipsOK.pubsXOf_P]
      exact ComplJ9ABalPAx.axSumP_eq_run δ hgen _ _ _ _ χ
    · rw [dif_neg h]
      have hk : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun.axKeys9 (rowsOfT9 t) = [] := by
        simpa [Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.axOnA] using h
      have hn : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun.axChainReadsK9 (rowsOfT9 t) = [] := by
        simp [Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun.axChainReadsK9, hk]
      rw [hn]
      simp [Quad.mk_zero']
  rw [hX]
  unfold readsA
  rw [List.map_append, List.sum_append, add_right_inj]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  exact ComplJ9ABalPW.Tw_eq_Wp δ Rt hgen hlen hp62 hwalk9 χ x
    (by rw [ComplJ9ADataRec.j9aDataOf_reads]; exact List.mem_append_right _ hx)

end

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle
#print axioms hGpA
#print axioms ComplJ9ABalPW.Tw_eq_Wp
#print axioms ComplJ9ABalPW.walkA_run
#print axioms ComplJ9ABalPC.rho4_total
end Axioms

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalP
