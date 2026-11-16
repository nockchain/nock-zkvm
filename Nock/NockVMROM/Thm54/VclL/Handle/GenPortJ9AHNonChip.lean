/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHNonChip.lean

-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Static

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHNonChip

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.Jet.PinJ8 (pinCons)
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8

noncomputable section

section Accept
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The 29 non-chip fields of `AcceptsJ9A`**, each with exactly its type there. -/
structure NonChipJ9A (Pb : PubJ9A p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ9A' p K δ) : Prop where
  hnpC : Pb.nC < ringChar (ZMod p)
  hkW : 1 ≤ Pb.kroots
  hknW : Pb.kroots ≤ Pb.nW
  hkpW : Pb.kroots + Pb.nW < ringChar (ZMod p)
  hnpA : Pb.nA < p
  hGx : M.ρ 3 + (Quad.mk _ (M.pubsW WalkHQ.pubXQ) (M.pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (M.pubsJ 2) (M.pubsJ 3)) =
    Quad.mk _ (M.pubsC CellHQ.pubHQ) (M.pubsC (CellHQ.pubHQ + 1))
  hGp : M.ρ 4 + Quad.mk _ (M.pubsX AxisChipJ9.pubAXp) (M.pubsX (AxisChipJ9.pubAXp + 1)) =
    Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1))
  hGS : M.ρS + ((pinCons (p := p) (K := K) Pb.regs Pb.idx).map fun r =>
      (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (M.pubsJ 0) (M.pubsJ 1) +
      Quad.mk _ (M.pubsX AxisChipJ9.pubAXs) (M.pubsX (AxisChipJ9.pubAXs + 1)) =
    Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1)) +
      Quad.mk _ (M.pubsS SplitChipJ9.pubSPs) (M.pubsS (SplitChipJ9.pubSPs + 1))
  hlay : List.ofFn Pb.lay = layoutJ8 Pb.Rt Pb.regs Pb.ids
  hsmall : ∀ q ∈ layoutJ8 Pb.Rt Pb.regs Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p
  huniq : ((layoutJ8 Pb.Rt Pb.regs Pb.ids).filterMap tvKey).Nodup
  hTpl : ∀ i ∈ Pb.regs, Rg i = some ⟨(Pb.Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Pb.Rt i)⟩ ∧
    axPosB (Pb.Rt i) = true ∧ (Pb.Rt i).WellTyped p
  hnd : Pb.regs.Nodup
  hidx : ∀ id ∈ Pb.regs, Pb.idx id < p
  hrk : ∀ id ∈ Pb.regs, Pb.rk id ≠ (0, 0)
  hlt : ∀ id ∈ Pb.regs, (Pb.rk id).1 < ringChar (ZMod p) ∧ (Pb.rk id).2 < ringChar (ZMod p) ∧
    Pb.idx id < ringChar (ZMod p)
  hsumC' : ((claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb.toPubJ8 χ).map fun r => (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 0) (M.pubsC 1) + Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubMB) (M.pubsA (AtomChipHQ.pubMB + 1))
  hbalA' : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV WalkHQ.pubXQ) (M.pubsV (WalkHQ.pubXQ + 1))
  hvalA0 : M.pubsA 0 = 0 ∧ M.pubsA 1 = 0
  hfxC : M.pubsC 2 = M.pubsW 0 ∧ M.pubsC 3 = M.pubsW 1
  hfxA : M.pubsA 2 = M.pubsV 0 ∧ M.pubsA 3 = M.pubsV 1
  hclI : ∀ k : Fin 3, (isCellN (claimNoun c k) = true ∨ isBigN p (claimNoun c k) = true) → (M.m k).1 < p
  hclR : ∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < p
  hcen' : ∀ x ∈ censusGJ9 Pb.toPubJ8 c, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ Pb.nA + 2
  hlenC : 3 + Pb.regs.length + 2 * Pb.nC < p
  hlenA : Pb.nA + Pb.nV < p
  hcellF : isCellN c.formula = true
  hnAS : Pb.nA + Pb.nS < 2 ^ 57
  hlenX : Pb.nX + Pb.n < p ∧ 2 * Pb.nS < p

/-- The non-chip fields are projections of `AcceptsJ9A`. -/
theorem nonChip_of_accepts {Pb : PubJ9A p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9A' p K δ} {tr : TrJ9A (ZMod p)} {r : RowsJ9A} {g : ℕ}
    (h : AcceptsJ9A δ b Pb Rg c χ M tr r g) : NonChipJ9A δ b Pb Rg c χ M where
  hnpC := h.hnpC
  hkW := h.hkW
  hknW := h.hknW
  hkpW := h.hkpW
  hnpA := h.hnpA
  hGx := h.hGx
  hGp := h.hGp
  hGS := h.hGS
  hlay := h.hlay
  hsmall := h.hsmall
  huniq := h.huniq
  hTpl := h.hTpl
  hnd := h.hnd
  hidx := h.hidx
  hrk := h.hrk
  hlt := h.hlt
  hsumC' := h.hsumC'
  hbalA' := h.hbalA'
  hvalA0 := h.hvalA0
  hfxC := h.hfxC
  hfxA := h.hfxA
  hclI := h.hclI
  hclR := h.hclR
  hcen' := h.hcen'
  hlenC := h.hlenC
  hlenA := h.hlenA
  hcellF := h.hcellF
  hnAS := h.hnAS
  hlenX := h.hlenX

/-- **The registry-free conjuncts** at `regs = ids = []`, `nJ = 0`. -/
theorem regFree (Pb : PubJ9A p) (hreg : Pb.regs = []) (hids : Pb.ids = []) (hnJ : Pb.nJ = 0)
    (Rg : Nock.Jet.Registry) :
    List.ofFn Pb.lay = layoutJ8 Pb.Rt Pb.regs Pb.ids ∧
    (∀ q ∈ layoutJ8 Pb.Rt Pb.regs Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) ∧
    ((layoutJ8 Pb.Rt Pb.regs Pb.ids).filterMap tvKey).Nodup ∧
    (∀ i ∈ Pb.regs, Rg i = some ⟨(Pb.Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Pb.Rt i)⟩ ∧
      axPosB (Pb.Rt i) = true ∧ (Pb.Rt i).WellTyped p) ∧
    Pb.regs.Nodup ∧ (∀ id ∈ Pb.regs, Pb.idx id < p) ∧ (∀ id ∈ Pb.regs, Pb.rk id ≠ (0, 0)) ∧
    (∀ id ∈ Pb.regs, (Pb.rk id).1 < ringChar (ZMod p) ∧ (Pb.rk id).2 < ringChar (ZMod p) ∧
      Pb.idx id < ringChar (ZMod p)) :=
  ⟨InhabJ8Static.hlay0 Pb.toPubJ8 hreg hids hnJ, InhabJ8Static.hsmall0 Pb.toPubJ8 hreg hids,
    InhabJ8Static.huniq0 Pb.toPubJ8 hreg hids, InhabJ8Static.regs_vacuous Pb.toPubJ8 hreg,
    InhabJ8Static.hnd0 Pb.toPubJ8 hreg, InhabJ8Static.regs_vacuous Pb.toPubJ8 hreg,
    InhabJ8Static.regs_vacuous Pb.toPubJ8 hreg, InhabJ8Static.regs_vacuous Pb.toPubJ8 hreg⟩

theorem pinRecs_nil (Pb : PubJ9A p) (χ : Coins frameJ8 K) (hreg : Pb.regs = []) :
    pinRecsJ8 δ Pb.toPubJ8 χ = [] := by
  unfold pinRecsJ8; rw [hreg]; rfl

theorem pinCons_nil (Pb : PubJ9A p) (hreg : Pb.regs = []) :
    pinCons (p := p) (K := K) Pb.regs Pb.idx = [] := by
  rw [hreg]; rfl

theorem census_nil (Pb : PubJ9A p) (c : P8PublicClaim) (hreg : Pb.regs = []) :
    censusGJ9 Pb.toPubJ8 c = (claimCells c).map (claimNoun c) ++ (claimBigs p c).map (claimNoun c) := by
  unfold censusGJ9 censusG; rw [hreg]; rfl

/-- **Transport of the non-chip conjuncts** from `(Pb', M')` to `(Pb, M)` when the sizes and the message fields
agree and both registries are empty. -/
theorem nonChip_transport {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {Pb Pb' : PubJ9A p} {M M' : MsgJ9A' p K δ} (H : NonChipJ9A δ b Pb' Rg c χ M')
    (hn : Pb.n = Pb'.n) (hnC : Pb.nC = Pb'.nC) (hnW : Pb.nW = Pb'.nW) (hkr : Pb.kroots = Pb'.kroots)
    (hnA : Pb.nA = Pb'.nA) (hnV : Pb.nV = Pb'.nV) (hnX : Pb.nX = Pb'.nX) (hnS : Pb.nS = Pb'.nS)
    (hreg : Pb.regs = []) (hreg' : Pb'.regs = []) (hids : Pb.ids = []) (hnJ : Pb.nJ = 0)
    (hm : M.m = M'.m) (hρ : M.ρ = M'.ρ) (hρS : M.ρS = M'.ρS) (hC : M.pubsC = M'.pubsC) (hW : M.pubsW = M'.pubsW)
    (hJ : M.pubsJ = M'.pubsJ) (hA : M.pubsA = M'.pubsA) (hV : M.pubsV = M'.pubsV) (hX : M.pubsX = M'.pubsX)
    (hS : M.pubsS = M'.pubsS) : NonChipJ9A δ b Pb Rg c χ M := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := regFree Pb hreg hids hnJ Rg
  have hlen : Pb.regs.length = Pb'.regs.length := by rw [hreg, hreg']
  refine
    { hnpC := ?_, hkW := ?_, hknW := ?_, hkpW := ?_, hnpA := ?_, hGx := ?_, hGp := ?_, hGS := ?_,
      hlay := e1, hsmall := e2, huniq := e3, hTpl := e4, hnd := e5, hidx := e6, hrk := e7, hlt := e8,
      hsumC' := ?_, hbalA' := ?_, hvalA0 := ?_, hfxC := ?_, hfxA := ?_, hclI := ?_, hclR := H.hclR,
      hcen' := ?_, hlenC := ?_, hlenA := ?_, hcellF := H.hcellF, hnAS := ?_, hlenX := ?_ }
  · rw [hnC]; exact H.hnpC
  · rw [hkr]; exact H.hkW
  · rw [hkr, hnW]; exact H.hknW
  · rw [hkr, hnW]; exact H.hkpW
  · rw [hnA]; exact H.hnpA
  · rw [hρ, hW, hJ, hC]; exact H.hGx
  · rw [hρ, hX, hW]; exact H.hGp
  · have h := H.hGS
    rw [pinCons_nil Pb' hreg'] at h
    rw [pinCons_nil Pb hreg, hρS, hJ, hX, hA, hV, hS]
    exact h
  · have h := H.hsumC'
    rw [pinRecs_nil δ Pb' χ hreg'] at h
    rw [pinRecs_nil δ Pb χ hreg, hm, hC, hA]
    exact h
  · rw [hA, hV]; exact H.hbalA'
  · rw [hA]; exact H.hvalA0
  · rw [hC, hW]; exact H.hfxC
  · rw [hA, hV]; exact H.hfxA
  · rw [hm]; exact H.hclI
  · have h := H.hcen'
    rw [census_nil Pb' c hreg'] at h
    rw [census_nil Pb c hreg, hnA]
    exact h
  · rw [hlen, hnC]; exact H.hlenC
  · rw [hnA, hnV]; exact H.hlenA
  · rw [hnA, hnS]; exact H.hnAS
  · rw [hnX, hn, hnS]; exact H.hlenX

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHNonChip

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHNonChip.nonChip_of_accepts
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHNonChip.regFree
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHNonChip.pinRecs_nil
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHNonChip.pinCons_nil
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHNonChip.census_nil
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHNonChip.nonChip_transport
