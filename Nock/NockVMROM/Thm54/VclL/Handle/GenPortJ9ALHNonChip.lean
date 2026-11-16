/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHNonChip.lean

  **the non-chip conjuncts of `AcceptsJ9AL`, generic transport (twin of `GenPortJ9AHNonChip`).**  Everything is over
  VARIABLES `Pb Pb' M M'`: hypotheses are `rw`-ed, no concrete record is unfolded.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHNonChip
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Static

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHNonChip

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
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8

noncomputable section

section Accept
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The non-chip fields of `AcceptsJ9AL`** (the `NonChipJ9A` fields at their AL types, plus the AL additions). -/
structure NonChipJ9AL (Pb : PubJ9AL p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ9AL' p K δ) : Prop where
  hnpC : Pb.nC < ringChar (ZMod p)
  hkW : 1 ≤ Pb.kroots
  hknW : Pb.kroots ≤ Pb.nW
  hkpW : Pb.kroots + Pb.nW < ringChar (ZMod p)
  hnpA : Pb.nA < p
  hGx : M.ρ 3 + (Quad.mk _ (M.pubsW WalkHQ.pubXQ) (M.pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (M.pubsJ 2) (M.pubsJ 3) +
      Quad.mk _ (M.pubsL AluSZChipJ9.pubALx) (M.pubsL (AluSZChipJ9.pubALx + 1))) =
    Quad.mk _ (M.pubsC CellHQ.pubHQ) (M.pubsC (CellHQ.pubHQ + 1))
  hGp : M.ρ 4 + Quad.mk _ (M.pubsX AxisChipJ9.pubAXp) (M.pubsX (AxisChipJ9.pubAXp + 1)) =
    Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1))
  hGS : M.ρS + ((pinCons (p := p) (K := K) Pb.regs Pb.idx).map fun r =>
      (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum +
      ((pinRgP (p := p) (K := K) Pb).map fun r =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum +
      ((pinOpP (p := p) (K := K) Pb).map fun r =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (M.pubsJ 0) (M.pubsJ 1) +
      Quad.mk _ (M.pubsX AxisChipJ9.pubAXs) (M.pubsX (AxisChipJ9.pubAXs + 1)) +
      Quad.mk _ (M.pubsL AluSZChipJ9.pubALs) (M.pubsL (AluSZChipJ9.pubALs + 1)) =
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
  hsumC' : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsL AluSZChipJ9.pubALv) (M.pubsL (AluSZChipJ9.pubALv + 1)) +
    ((claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb.toPubJ8 χ ++ pinRecsP δ Pb χ).map fun r => (FiniteIO.compress (m := 5)
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
  hcen' : ∀ x ∈ censusGJ9 Pb.toPubJ8 c ++ censusP Pb, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ Pb.nA + 2
  hlenC : 3 + Pb.regs.length + 2 * Pb.nC < p
  hlenA : Pb.nA + Pb.nV < p
  hcellF : isCellN c.formula = true
  hnAS : Pb.nA + Pb.nS < 2 ^ 57
  hlenX : Pb.nX + Pb.n < p ∧ 2 * Pb.nS < p
  hPrim : ∀ q ∈ Pb.prims, Rg q.1 = some (Nock.Jet.Prim.primSpec q.2)
  hdisjP : ∀ q ∈ Pb.prims, q.1 ∉ Pb.regs
  hlenL : Pb.nL + Pb.n < p ∧ ∀ q ∈ Pb.prims, q.1 < p ∧ Pb.idxP q.1 < p
  hndP : (Pb.prims.map Prod.fst).Nodup
  hrkP : ∀ q ∈ Pb.prims, Pb.rkP q.1 ≠ (0, 0)
  hltP : ∀ q ∈ Pb.prims, (Pb.rkP q.1).1 < ringChar (ZMod p) ∧ (Pb.rkP q.1).2 < ringChar (ZMod p) ∧
    Pb.idxP q.1 < ringChar (ZMod p)
  hlenCP : 3 + Pb.regs.length + Pb.prims.length + Pb.nL + 2 * Pb.nC < p

/-- The non-chip fields are projections of `AcceptsJ9AL` (`hlenL` drops its `nL ≤ r.AL` conjunct, which is a budget
fact). -/
theorem nonChip_of_acceptsL {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {r : RowsJ9AL} {g : ℕ}
    (h : AcceptsJ9AL δ b Pb Rg c χ M tr r g) : NonChipJ9AL δ b Pb Rg c χ M where
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
  hPrim := h.hPrim
  hdisjP := h.hdisjP
  hlenL := ⟨h.hlenL.1, h.hlenL.2.2⟩
  hndP := h.hndP
  hrkP := h.hrkP
  hltP := h.hltP
  hlenCP := h.hlenCP

theorem pinRgP_congr (Pb Pb' : PubJ9AL p) (hpr : Pb.prims = Pb'.prims) (hix : Pb.idxP = Pb'.idxP) :
    pinRgP (p := p) (K := K) Pb = pinRgP (p := p) (K := K) Pb' := by
  unfold pinRgP; rw [hpr, hix]

theorem pinOpP_congr (Pb Pb' : PubJ9AL p) (hpr : Pb.prims = Pb'.prims) :
    pinOpP (p := p) (K := K) Pb = pinOpP (p := p) (K := K) Pb' := by
  unfold pinOpP; rw [hpr]

theorem pinRecsP_congr (Pb Pb' : PubJ9AL p) (χ : Coins frameJ8 K) (hpr : Pb.prims = Pb'.prims)
    (hix : Pb.idxP = Pb'.idxP) (hrk : Pb.rkP = Pb'.rkP) : pinRecsP δ Pb χ = pinRecsP δ Pb' χ := by
  unfold pinRecsP; rw [hpr, hix, hrk]

theorem censusP_congr (Pb Pb' : PubJ9AL p) (hpr : Pb.prims = Pb'.prims) : censusP Pb = censusP Pb' := by
  unfold censusP; rw [hpr]

/-- **Transport of the non-chip conjuncts** from `(Pb', M')` to `(Pb, M)`: sizes and message fields agree, both
J-chip registries are empty, and the primitive data (`prims`, `idxP`, `rkP`, `nL`) agree (the primitive table is
carried over, not assumed empty). -/
theorem nonChip_transportL {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {Pb Pb' : PubJ9AL p} {M M' : MsgJ9AL' p K δ} (H : NonChipJ9AL δ b Pb' Rg c χ M')
    (hn : Pb.n = Pb'.n) (hnC : Pb.nC = Pb'.nC) (hnW : Pb.nW = Pb'.nW) (hkr : Pb.kroots = Pb'.kroots)
    (hnA : Pb.nA = Pb'.nA) (hnV : Pb.nV = Pb'.nV) (hnX : Pb.nX = Pb'.nX) (hnS : Pb.nS = Pb'.nS)
    (hnL : Pb.nL = Pb'.nL)
    (hreg : Pb.regs = []) (hreg' : Pb'.regs = []) (hids : Pb.ids = []) (hnJ : Pb.nJ = 0)
    (hpr : Pb.prims = Pb'.prims) (hix : Pb.idxP = Pb'.idxP) (hrk : Pb.rkP = Pb'.rkP)
    (hm : M.m = M'.m) (hρ : M.ρ = M'.ρ) (hρS : M.ρS = M'.ρS) (hC : M.pubsC = M'.pubsC) (hW : M.pubsW = M'.pubsW)
    (hJ : M.pubsJ = M'.pubsJ) (hA : M.pubsA = M'.pubsA) (hV : M.pubsV = M'.pubsV) (hX : M.pubsX = M'.pubsX)
    (hS : M.pubsS = M'.pubsS) (hL : M.pubsL = M'.pubsL) : NonChipJ9AL δ b Pb Rg c χ M := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ :=
    GenPortJ9AHNonChip.regFree Pb.toPubJ9A hreg hids hnJ Rg
  have hlen : Pb.regs.length = Pb'.regs.length := by rw [hreg, hreg']
  have pRg := pinRgP_congr (p := p) (K := K) Pb Pb' hpr hix
  have pOp := pinOpP_congr (p := p) (K := K) Pb Pb' hpr
  have pRP := pinRecsP_congr δ Pb Pb' χ hpr hix hrk
  have cP := censusP_congr Pb Pb' hpr
  refine
    { hnpC := ?_, hkW := ?_, hknW := ?_, hkpW := ?_, hnpA := ?_, hGx := ?_, hGp := ?_, hGS := ?_,
      hlay := e1, hsmall := e2, huniq := e3, hTpl := e4, hnd := e5, hidx := e6, hrk := e7, hlt := e8,
      hsumC' := ?_, hbalA' := ?_, hvalA0 := ?_, hfxC := ?_, hfxA := ?_, hclI := ?_, hclR := H.hclR,
      hcen' := ?_, hlenC := ?_, hlenA := ?_, hcellF := H.hcellF, hnAS := ?_, hlenX := ?_,
      hPrim := ?_, hdisjP := ?_, hlenL := ?_, hndP := ?_, hrkP := ?_, hltP := ?_, hlenCP := ?_ }
  · rw [hnC]; exact H.hnpC
  · rw [hkr]; exact H.hkW
  · rw [hkr, hnW]; exact H.hknW
  · rw [hkr, hnW]; exact H.hkpW
  · rw [hnA]; exact H.hnpA
  · rw [hρ, hW, hJ, hC, hL]; exact H.hGx
  · rw [hρ, hX, hW]; exact H.hGp
  · have h := H.hGS
    rw [GenPortJ9AHNonChip.pinCons_nil Pb'.toPubJ9A hreg'] at h
    rw [GenPortJ9AHNonChip.pinCons_nil Pb.toPubJ9A hreg, pRg, pOp, hρS, hJ, hX, hA, hV, hS, hL]
    exact h
  · have h := H.hsumC'
    rw [GenPortJ9AHNonChip.pinRecs_nil δ Pb'.toPubJ9A χ hreg'] at h
    rw [GenPortJ9AHNonChip.pinRecs_nil δ Pb.toPubJ9A χ hreg, pRP, hm, hC, hA, hL]
    exact h
  · rw [hA, hV]; exact H.hbalA'
  · rw [hA]; exact H.hvalA0
  · rw [hC, hW]; exact H.hfxC
  · rw [hA, hV]; exact H.hfxA
  · rw [hm]; exact H.hclI
  · have h := H.hcen'
    rw [GenPortJ9AHNonChip.census_nil Pb'.toPubJ9A c hreg', cP.symm] at h
    rw [GenPortJ9AHNonChip.census_nil Pb.toPubJ9A c hreg, hnA]
    exact h
  · rw [hlen, hnC]; exact H.hlenC
  · rw [hnA, hnV]; exact H.hlenA
  · rw [hnA, hnS]; exact H.hnAS
  · rw [hnX, hn, hnS]; exact H.hlenX
  · rw [hpr]; exact H.hPrim
  · intro q _; rw [hreg]; simp
  · rw [hnL, hn, hpr, hix]; exact H.hlenL
  · rw [hpr]; exact H.hndP
  · rw [hpr, hrk]; exact H.hrkP
  · rw [hpr, hrk, hix]; exact H.hltP
  · rw [hlen, hnL, hnC, hpr]; exact H.hlenCP

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHNonChip

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHNonChip.nonChip_of_acceptsL
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHNonChip.nonChip_transportL
