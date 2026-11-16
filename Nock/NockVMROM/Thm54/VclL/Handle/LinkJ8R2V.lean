/-
  Nock/NockVMROM/Thm54/VclL/Handle/LinkJ8R2V.lean

  * **`hXV_of_io`**: on an `AcceptsJ8` trace, with the check **pubsA(2,3) = pubsV(0,1)** (a hypothesis here; lane
    R1 adds it to `AcceptsJ8'`) and the validity pair outside `IOFailureEventW` of the atom walk's consumed keys
    against the atom table's export records (at the trace's views), `KeysExported (atomT …) (walkDataOf …).X`.
    The count `n_V < p` is `AcceptsJ8.hkpV`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R2V

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.WalkVCL (KeysExported)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (restrictWalkK walkChipHQK_restrict_sat walkChipHQK_restrict_bind)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (restrictAtomCell atomChipHQ_restrict_cell_sat
  atomChipHQ_restrict_bind)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_ok)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 shV)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (c4 c5 c6 c7)

noncomputable section

section Link
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The atom walk's consumed export keys at the trace's view (the list `walk_keys_exported` reads). -/
abbrev vxReqsAt (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    List (Fin 11 → 𝕂′) :=
  walkXInternal δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
    (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
      (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV))

/-- The atom table's export records at the trace's view. -/
abbrev vxProvsAt (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    List ((Fin 11 → 𝕂′) × ZMod p) :=
  cellXRecords δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
    (restrictAtomCell δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
      (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA))

/-- **`LinkJ8.hXV` from the export lookup**: on an `AcceptsJ8` trace, with the terminal check
`pubsA(2,3) = pubsV(0,1)` and the validity pair outside the IO failure event of the atom walk's keys against the
atom table's export records, every key the atom walk consumes is a row of the decoded atom table. -/
theorem hXV_of_io [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr)
    (hAV : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA 2) (M.pubsA 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV 0) (M.pubsV 1))
    (hout : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (vxReqsAt δ b Pb χ M tr) (liftWts (vxProvsAt δ b Pb χ M tr))) :
    KeysExported (atomT δ b Pb χ M tr)
      (walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
          (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV))).X := by
  have hsatC := atomChipHQ_restrict_cell_sat δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA _ hacc.hsatA
  have hbindC := atomChipHQ_restrict_bind δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA _ hacc.hbindA
  have hsatP := walkChipHQK_restrict_sat δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV _
    hacc.hsatV
  have hbindP := walkChipHQK_restrict_bind δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV _
    hacc.hbindV
  have hcnt : (vxReqsAt δ b Pb χ M tr).length < p := by
    rw [vxReqsAt, walkXInternal_length]
    have h := hacc.hkpV
    rw [ZMod.ringChar_zmod_n] at h
    omega
  exact walk_keys_exported δ Pb.krootsV b Pb.hnA Pb.nodesA Pb.orbitA Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ)
    M.pubsA M.pubsV _ _ hsatC hbindC hacc.hinjA hacc.hadjA hsatP hbindP hacc.hinjV hacc.hadjV _ _
    (chalsAJ8_ok δ χ) 0 (by rw [zero_add]; exact hAV) (p := p) [] (by simp) (by simp)
    (fun hc => hout (mem_IOFailureEventW_iff.mpr (Or.inl hc)))
    (fun hc => hout (mem_IOFailureEventW_iff.mpr (Or.inr (Or.inr hc)))) hcnt

theorem vxReqsJ8_view (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    vxReqsJ8 δ b Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV tr = vxReqsAt δ b Pb χ M tr :=
  wXInt_congr δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV _ _ _ _ _ _ (by norm_num) (by rw [walk_w]; norm_num)
    fun j hj => congrArg tr.V (Fin.ext rfl)

theorem vxProvsJ8_view (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    vxProvsJ8 δ b Pb.nodesA Pb.orbitA tr = liftWts (vxProvsAt δ b Pb χ M tr) := by
  have hw : 183 ≤ (cellChip δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA).rap.w := by
    rw [cell_w]; norm_num
  have e := cXRec_congr δ b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) (restrictQ 129 205 shA tr.A)
    (restrictAtomCell δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA))
    (chalsAJ8 δ χ) M.pubsA (by norm_num) hw fun j hj => congrArg tr.A (Fin.ext rfl)
  rw [vxProvsJ8, e]
  rfl

variable {r : RowsJ8} {P g : ℕ}

theorem hXV_of_outsideX [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr)
    (X : DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (hX : ∀ s ∈ allJ8X X, ¬ s.mem tr χ)
    (hrq : X.vxReqs tr χ = vxReqsJ8 δ b Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV tr)
    (hpv : X.vxProvs tr χ = vxProvsJ8 δ b Pb.nodesA Pb.orbitA tr)
    (hbV : Pb.nV ≤ r.AW) (hbA : Pb.nA ≤ r.A)
    (hAV : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA 2) (M.pubsA 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV 0) (M.pubsV 1)) :
    KeysExported (atomT δ b Pb χ M tr)
      (walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
          (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV))).X := by
  have h1 : (X.vxReqs tr χ).length ≤ r.AW := by
    rw [hrq, vxReqsJ8_length]; exact hbV
  have h2 : (X.vxProvs tr χ).length ≤ 2 * r.A := by
    rw [hpv]; exact (vxProvsJ8_length δ b Pb.nodesA Pb.orbitA tr).trans (by omega)
  have hout := afx_out_of_outsideX X hX h1 h2
  rw [hrq, hpv, vxReqsJ8_view δ b Pb χ M tr, vxProvsJ8_view δ b Pb χ M tr] at hout
  exact hXV_of_io δ b Pb c χ M tr hacc hAV hout

/-- **`LinkJ8.hXV` at the real readout** `withFpxV R …` (the readout equations are `rfl`). -/
theorem hXV_withFpxV [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr)
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (hX : ∀ s ∈ allJ8X (withFpxV δ b R Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA), ¬ s.mem tr χ)
    (hbV : Pb.nV ≤ r.AW) (hbA : Pb.nA ≤ r.A)
    (hAV : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA 2) (M.pubsA 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV 0) (M.pubsV 1)) :
    KeysExported (atomT δ b Pb χ M tr)
      (walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
          (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV))).X :=
  hXV_of_outsideX δ b Pb c χ M tr hacc _ hX rfl rfl hbV hbA hAV

end Link

end

end Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R2V
