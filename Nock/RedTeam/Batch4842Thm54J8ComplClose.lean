/-
  Nock/RedTeam/Batch4842Thm54J8ComplClose.lean

  **J-8 general completeness: non-vacuity of `ComplJ8Closed.complJ8_closed`.**  At the toy run `*[[0 0] [0 1]]`
  (Goldilocks, `K = KC`, `δ = deltaF`, `b = powerBasis3`, the empty registry, template table
  `fun _ => matmulT 1`, unused) every binder `hpG hax hop5 hclA hleaf hwalk hwalkA hRt hregAx h31` is a closed
  lemma below, and `complJ8_closed_toy_figure` concludes `ε_c < 2^-120` and an accepting coin with no
  hypothesis.  Axioms std3. -/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
import Nock.Jet.AutogenMatmul
import Nock.TraceGenExe.K6
import Nock.TraceGenExe.PowerBasis

set_option autoImplicit false

namespace Nock.RedTeam.Batch4842

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf gen0E rows0)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.TraceGenExe (KC deltaF powerBasis3)

noncomputable section

/-! ## 1. The toy run's data and binders -/

abbrev RtT : ℕ → Nock.Jet.Autogen.Tpl := fun _ => Nock.Jet.Autogen.matmulT 1

abbrev DT := j8DataOf Nock.Field.p Nock.Jet.VerifiedRegistry.empty RtT gen0E

theorem hcalls : Nock.V1J8.Gen.callsOf #[InhabJ8Comp.r0] = [] := by decide

theorem inTree_t0 (u : NTree SkelX) (h : InTree InhabJ8Base.t0 u) : u = InhabJ8Base.t0 := by
  cases h with
  | here => rfl
  | sub hs _ => simp [InhabJ8Base.t0, mkX] at hs

theorem calls_T : DT.calls = [] := by
  show Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT InhabJ8Base.t0) = []
  rw [rows0]; exact hcalls

theorem reads_T : DT.reads = [] := by
  show Nock.V1J8.Gen.pathReads (ComplJ8Data.rowsOfT InhabJ8Base.t0) = []
  rw [rows0]; decide

theorem hleaf_T : ComplJ8Walk.RootsLeafOK DT.roots := by
  show ∀ r ∈ Nock.V1J8.Gen.rootsOf _ (ComplJ8Data.rowsOfT InhabJ8Base.t0) ++ _, _
  rw [rows0]
  simp only [ComplJ8Data.jNounsP, hcalls]
  decide

theorem hwalk_T : ComplJ8Walk.WalkDepthOK DT.reads := by
  rw [reads_T]; intro r hr; simp [VclL.pathReads] at hr

theorem preads_T : DT.preads = [] := by
  show ComplJ8Data.pairReadsP _ _ (ComplJ8Data.rowsOfT InhabJ8Base.t0) = []
  rw [rows0]
  simp [ComplJ8Data.pairReadsP, InhabJ8Comp.r0, Nock.V1J8.FillX.isPairB]

theorem hwalkA_T : ComplJ8Walk.WalkDepthOK DT.preads := by
  rw [preads_T]; intro r hr; simp [VclL.pathReads] at hr

theorem jrows_T : DT.jrows = [] := by
  show ComplJ8Data.mvFixP _ (Nock.Jet.ChipJ8.honestJ8G _ _ (List.map Prod.fst DT.calls).dedup DT.calls) _ = []
  rw [calls_T]; rfl

theorem bigs_T : DT.bigs = [] := by
  show ComplJ8Data.bigsP _ _ (ComplJ8Data.rowsOfT InhabJ8Base.t0) = []
  rw [rows0]
  simp only [ComplJ8Data.jNounsP, hcalls]
  unfold ComplJ8Data.bigsP
  rw [show List.filter _ _ = [] by decide]
  simp

theorem acs_T : DT.acs.length ≤ 2 := by
  show (ComplJ8Data.acsP _ DT.bigs _).length ≤ 2
  rw [bigs_T]
  simp [ComplJ8Data.acsP]
  decide

theorem h31_T : Rows31 DT := by
  intro x hx
  simp only [sizesJ8, nVOf, preads_T, if_true, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hW : (VclL.GenWalk.walkRows DT.cells DT.reads).length ≤ 2 ^ 31 := by
    rw [reads_T]
    have := VclL.GenWalk.walkRows_length_le DT.cells []
    simp [VclL.pathReads] at this
    omega
  have hB : (bfsForest [DT.t]).length = 1 := by
    show (bfsForest [InhabJ8Base.t0]).length = 1
    rw [InhabJ8Comp.bfs0]; rfl
  have hC : DT.cells.length = 2 := by rw [(ComplJ8Data.toy_cells_H RtT).1]; rfl
  have hA := acs_T
  have hJ : DT.jrows.length = 0 := by rw [jrows_T]; rfl
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem hax_T : ComplJ8.ProgAxOK Nock.Field.p InhabJ8Base.t0 := by
  intro u hu
  rw [inTree_t0 u hu]
  show ComplJ8.AxRowX _ InhabJ8Comp.r0
  intro ax hax
  simp [InhabJ8Comp.r0] at hax
  subst hax; decide

theorem hop5_T : ComplJ8.ProgOp5OK Nock.Field.p InhabJ8Base.t0 := by
  intro u hu
  rw [inTree_t0 u hu]
  intro h; simp [InhabJ8Comp.row0, InhabJ8Comp.r0] at h

theorem called_T : ∀ id, id ∉ ComplJ8Jet.CalledIds InhabJ8Base.t0 := by
  rintro id ⟨u, hu, hst, -⟩
  rw [inTree_t0 u hu] at hst
  simp [InhabJ8Comp.row0, InhabJ8Comp.r0] at hst

theorem hclA_T : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ InhabJ8Base.s0 InhabJ8Base.f0 InhabJ8Base.s0) k).leafList,
    v < Nock.Field.p := by
  decide

instance factRC : Fact (ringChar (ZMod Nock.Field.p)).Prime := ⟨by rw [ZMod.ringChar_zmod_n]; exact Fact.out⟩
instance charPKC : CharP Nock.TraceGenExe.KC (ringChar (ZMod Nock.Field.p)) := by
  rw [ZMod.ringChar_zmod_n]; exact charP_of_injective_algebraMap (algebraMap (ZMod Nock.Field.p) Nock.TraceGenExe.KC).injective _
noncomputable instance algRC : Algebra (ZMod (ringChar (ZMod Nock.Field.p))) Nock.TraceGenExe.KC := ZMod.algebra _ _


/-! ## 2. `complJ8_closed` at the toy -/

/-- The toy's honest record (every family). -/
abbrev BT := ComplJ8Closed.BRunA deltaF powerBasis3 RtT gen0E rfl h31_T

open Classical in
/-- **`complJ8_closed` at `*[[0 0] [0 1]]`, every binder discharged.** -/
theorem complJ8_closed_toy :
    (∀ χ, BT.Good χ → AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 BT.Pb Nock.Jet.VerifiedRegistry.empty.R
      (ComplJ8.cJ InhabJ8Base.s0 InhabJ8Base.f0 InhabJ8Base.s0) χ (BT.M χ) (BT.tr χ) BT.rows BT.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 KC => ¬ BT.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 KC) ≤ BT.epsC) ∧
    StJ8 BT.tr ∧ Nock.Jet.HoldsN (ComplJ8.cJ InhabJ8Base.s0 InhabJ8Base.f0 InhabJ8Base.s0) ∧
    (Fintype.card KC = VclL.Events.cK →
      BT.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 BT.Pb Nock.Jet.VerifiedRegistry.empty.R
        (ComplJ8.cJ InhabJ8Base.s0 InhabJ8Base.f0 InhabJ8Base.s0) χ (BT.M χ) (BT.tr χ) BT.rows BT.g) :=
  ComplJ8Closed.complJ8_closed deltaF powerBasis3 RtT gen0E rfl hax_T hop5_T hclA_T hleaf_T hwalk_T hwalkA_T
    (fun id h => absurd h (called_T id)) (fun id h => absurd h (called_T id)) h31_T

theorem card_KC : Fintype.card KC = VclL.Events.cK := by
  rw [Nock.TraceGenExe.KC_card, Nock.NockVMROM.Thm54.VclL.Events.cK_eq]

/-- **The figure at the toy, hypothesis-free**: `ε_c < 2^-120` and an accepting coin. -/
theorem complJ8_closed_toy_figure :
    BT.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 BT.Pb Nock.Jet.VerifiedRegistry.empty.R
        (ComplJ8.cJ InhabJ8Base.s0 InhabJ8Base.f0 InhabJ8Base.s0) χ (BT.M χ) (BT.tr χ) BT.rows BT.g :=
  complJ8_closed_toy.2.2.2.2 card_KC

end

end Nock.RedTeam.Batch4842

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed.complJ8_closed
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed.openJ8_closed
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed.obligations_of_fams
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed.famsAll_facts
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed.good_mono
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed.goodA
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of.obligations_of_run
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of.honestJ8Of
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of.complJ8
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of.famsOf_facts
#print axioms Nock.RedTeam.Batch4842.complJ8_closed_toy
#print axioms Nock.RedTeam.Batch4842.complJ8_closed_toy_figure
