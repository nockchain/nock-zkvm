/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHLink.lean

  **Honest link, part 1: the generic pieces.**

  * §1 `ovlJ_*`: the overlay fields of `GenPortJ9ALHJRun.ovlJ` over a VARIABLE source record (cheap for the kernel),
    and their instances `IL_*` at `recJ9ALXJ`;
  * §2 `nonChip_transportJL`: the J-9 AL non-chip conjuncts transported with J-registered ids (the twin of
    `GenPortJ9AHMsgJ.nonChip_transportJ`, plus the primitive data; the ALU's row count `nL` is NOT transported, its two
    length facts are inputs, and the ALU publics are transported at the three `Quad.mk` terminals only);
  * §3 `sum_fin_stable`, `sumV_stable`/`sumS_stable`/`sumX_stable`: a row-local ALU terminal over `n` rows does not
    depend on `n ≥ |tb|` (the padding row contributes `0`);
  * §4 `lengthsX`: `hlenL`'s `nL + n < p` and `hlenCP` for an ALU chip of up to `2^34` rows (`lengths_L` stops at
    `2^31`; the generator's ALU chip has `3·2^h` rows, which can exceed `2^31`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHMsgJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHNonChip
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHAluE

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHLink

/-! ## 1. The overlay fields -/

section Ovl
open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHJRun (ovlJ)

variable (I : InJ9A) (pC pJ pA : ℕ → K3) (r : Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.RowsJ8) (g : ℕ) (C J A : ChipIn)
  (lay : Fin J.n → Nock.Jet.ChipJ8.PRow) (regs ids : List ℕ) (rAX rSP : ℕ)

theorem ovlJ_C : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).C = C := rfl
theorem ovlJ_J : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).J = J := rfl
theorem ovlJ_A : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).A = A := rfl
theorem ovlJ_pubsC : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).M.pubsC = pC := rfl
theorem ovlJ_pubsJ : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).M.pubsJ = pJ := rfl
theorem ovlJ_pubsA : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).M.pubsA = pA := rfl
theorem ovlJ_r : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).r = r := rfl
theorem ovlJ_g : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).g = g := rfl
theorem ovlJ_regs : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).regs = regs := rfl
theorem ovlJ_ids : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).ids = ids := rfl
theorem ovlJ_rAX : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).rAX = rAX := rfl
theorem ovlJ_rSP : (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).rSP = rSP := rfl
theorem ovlJ_lay : List.ofFn (ovlJ I pC pJ pA r g C J A lay regs ids rAX rSP).lay = List.ofFn lay := rfl
/-! Message congruences over VARIABLE records (the kernel never compares two concrete messages). -/
theorem toMsg_m_congr {I₁ I₂ : InJ9A} (h : I₁.M.m = I₂.M.m) : I₁.toMsg.m = I₂.toMsg.m := h
theorem toMsg_rho_congr {I₁ I₂ : InJ9A} (h : I₁.M.ρ = I₂.M.ρ) : I₁.toMsg.ρ = I₂.toMsg.ρ := by
  show (fun i => K6.toQ (I₁.M.ρ i)) = fun i => K6.toQ (I₂.M.ρ i)
  rw [h]
theorem toMsg_rhoS_congr {I₁ I₂ : InJ9A} (h : I₁.M.ρS = I₂.M.ρS) : I₁.toMsg.ρS = I₂.toMsg.ρS := by
  show K6.toQ I₁.M.ρS = K6.toQ I₂.M.ρS
  rw [h]
theorem toMsg_pubsW_congr {I₁ I₂ : InJ9A} (h : I₁.M.pubsW = I₂.M.pubsW) : I₁.toMsg.pubsW = I₂.toMsg.pubsW := by
  show (fun i => K3.toK (I₁.M.pubsW i)) = fun i => K3.toK (I₂.M.pubsW i)
  rw [h]
theorem toMsg_pubsV_congr {I₁ I₂ : InJ9A} (h : I₁.M.pubsV = I₂.M.pubsV) : I₁.toMsg.pubsV = I₂.toMsg.pubsV := by
  show (fun i => K3.toK (I₁.M.pubsV i)) = fun i => K3.toK (I₂.M.pubsV i)
  rw [h]
theorem toMsg_pubsX_congr {I₁ I₂ : InJ9A} (h : I₁.pubsX = I₂.pubsX) : I₁.toMsg.pubsX = I₂.toMsg.pubsX := by
  show (fun i => K3.toK (I₁.pubsX i)) = fun i => K3.toK (I₂.pubsX i)
  rw [h]
theorem toMsg_pubsS_congr {I₁ I₂ : InJ9A} (h : I₁.pubsS = I₂.pubsS) : I₁.toMsg.pubsS = I₂.toMsg.pubsS := by
  show (fun i => K3.toK (I₁.pubsS i)) = fun i => K3.toK (I₂.pubsS i)
  rw [h]

end Ovl

section ILrec
open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.V1J9AL.CheckJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHJRun
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj (RnOf)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHJRun
open Nock.Jet.Prim (PrimOp)

variable (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (s f : Noun) (χe : CoinsE)
  (t : Nock.Walk.NTree Nock.Edit.GenX.SkelX) (r : Noun)

local notation "IL" => recJ9ALXJ Rt prims s f χe t r
local notation "RN" => RnOf t r

theorem IL_C : (IL).toInJ9A.C = chipOf (cRPLK Rt prims s f χe RN).1 := ovlJ_C _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem IL_A : (IL).toInJ9A.A = chipOf (aRPLK Rt prims s f χe RN).1 := ovlJ_A _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem IL_J : (IL).toInJ9A.J = ⟨hOf (layLK Rt prims s f χe RN).length, (layLK Rt prims s f χe RN).length,
    ωOf (hOf (layLK Rt prims s f χe RN).length),
    colsOf (jgLK Rt prims s f χe RN).1 (layLK Rt prims s f χe RN).length⟩ := ovlJ_J _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem IL_pubsC : (IL).toInJ9A.M.pubsC = (cRPLK Rt prims s f χe RN).2 := ovlJ_pubsC _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem IL_pubsJ : (IL).toInJ9A.M.pubsJ = (jgLK Rt prims s f χe RN).2 := ovlJ_pubsJ _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem IL_pubsA : (IL).toInJ9A.M.pubsA = (aRPLK Rt prims s f χe RN).2 := ovlJ_pubsA _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem IL_r : (IL).toInJ9A.r = budget (mLK Rt prims s f χe RN) := ovlJ_r _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem IL_g : (IL).toInJ9A.g = (regsJLK Rt prims s f χe RN).length := ovlJ_g _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem IL_regs : (IL).toInJ9A.regs = regsJLK Rt prims s f χe RN := ovlJ_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem IL_ids : (IL).toInJ9A.ids = idsJLK Rt prims s f χe RN := ovlJ_ids _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem IL_rAX : (IL).toInJ9A.rAX = BLK Rt prims s f χe RN := ovlJ_rAX _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem IL_rSP : (IL).toInJ9A.rSP = BLK Rt prims s f χe RN := ovlJ_rSP _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem IL_toMsg_m : (IL).toInJ9A.toMsg.m = (recJ9AXJ Rt s f χe t r).toMsg.m :=
  toMsg_m_congr (GenPortJ9ALHJRun.ovlJ_m _ _ _ _ _ _ _ _ _ _ _ _ _ _)
theorem IL_toMsg_rho : (IL).toInJ9A.toMsg.ρ = (recJ9AXJ Rt s f χe t r).toMsg.ρ :=
  toMsg_rho_congr (GenPortJ9ALHJRun.ovlJ_rho _ _ _ _ _ _ _ _ _ _ _ _ _ _)
theorem IL_toMsg_rhoS : (IL).toInJ9A.toMsg.ρS = (recJ9AXJ Rt s f χe t r).toMsg.ρS :=
  toMsg_rhoS_congr (GenPortJ9ALHJRun.ovlJ_rhoS _ _ _ _ _ _ _ _ _ _ _ _ _ _)
theorem IL_toMsg_pubsW : (IL).toInJ9A.toMsg.pubsW = (recJ9AXJ Rt s f χe t r).toMsg.pubsW :=
  toMsg_pubsW_congr (GenPortJ9ALHJRun.ovlJ_pubsW _ _ _ _ _ _ _ _ _ _ _ _ _ _)
theorem IL_toMsg_pubsV : (IL).toInJ9A.toMsg.pubsV = (recJ9AXJ Rt s f χe t r).toMsg.pubsV :=
  toMsg_pubsV_congr (GenPortJ9ALHJRun.ovlJ_pubsV _ _ _ _ _ _ _ _ _ _ _ _ _ _)
theorem IL_toMsg_pubsX : (IL).toInJ9A.toMsg.pubsX = (recJ9AXJ Rt s f χe t r).toMsg.pubsX :=
  toMsg_pubsX_congr (GenPortJ9ALHJRun.ovlJ_pubsX _ _ _ _ _ _ _ _ _ _ _ _ _ _)
theorem IL_toMsg_pubsS : (IL).toInJ9A.toMsg.pubsS = (recJ9AXJ Rt s f χe t r).toMsg.pubsS :=
  toMsg_pubsS_congr (GenPortJ9ALHJRun.ovlJ_pubsS _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem IL_AL : (IL).AL = chipOf (lRPLK Rt prims s f χe RN).1 := rfl
theorem IL_pubsL : (IL).pubsL = (lRPLK Rt prims s f χe RN).2 := rfl
theorem IL_aluOn : (IL).aluOn = aluOnLK Rt prims s f χe RN := rfl
theorem IL_prims : (IL).prims = if aluOnLK Rt prims s f χe RN then psCLK Rt prims s f χe RN else [] := rfl
theorem IL_idxP : (IL).idxP = ComplJ9ALData.idxPOf (csK Rt s f χe RN) prims := rfl
theorem IL_rkP : (IL).rkP = ComplJ9ALData.rkPOf prims := rfl
theorem IL_rAL : (IL).rAL = BLK Rt prims s f χe RN := rfl

end ILrec

/-! ## 2. Transport of the non-chip conjuncts, with J-registered ids -/

section Transport
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
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHNonChip

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **Transport of the J-9 AL non-chip conjuncts at jets** from `(Pb', M')` to `(Pb, M)`: the J-9 A sizes, the
registry fields (`regs ids idx rk Rt`, the layout list), the primitive data (`prims idxP rkP`) and the message fields
agree; the ALU publics agree at the three terminals; the ALU row count is free (its two length facts are inputs). -/
theorem nonChip_transportJL {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {Pb Pb' : PubJ9AL p} {M M' : MsgJ9AL' p K δ} (H : NonChipJ9AL δ b Pb' Rg c χ M')
    (hn : Pb.n = Pb'.n) (hnC : Pb.nC = Pb'.nC) (hnW : Pb.nW = Pb'.nW) (hkr : Pb.kroots = Pb'.kroots)
    (hnA : Pb.nA = Pb'.nA) (hnV : Pb.nV = Pb'.nV) (hnX : Pb.nX = Pb'.nX) (hnS : Pb.nS = Pb'.nS)
    (hreg : Pb.regs = Pb'.regs) (hids : Pb.ids = Pb'.ids) (hidxE : Pb.idx = Pb'.idx)
    (hrkE : Pb.rk = Pb'.rk) (hRtE : Pb.Rt = Pb'.Rt) (hlayE : List.ofFn Pb.lay = List.ofFn Pb'.lay)
    (hpr : Pb.prims = Pb'.prims) (hix : Pb.idxP = Pb'.idxP) (hrkP : Pb.rkP = Pb'.rkP)
    (hlenL1 : Pb.nL + Pb.n < p) (hlenCP : 3 + Pb.regs.length + Pb.prims.length + Pb.nL + 2 * Pb.nC < p)
    (hm : M.m = M'.m) (hρ : M.ρ = M'.ρ) (hρS : M.ρS = M'.ρS) (hC : M.pubsC = M'.pubsC) (hW : M.pubsW = M'.pubsW)
    (hJ : M.pubsJ = M'.pubsJ) (hA : M.pubsA = M'.pubsA) (hV : M.pubsV = M'.pubsV) (hX : M.pubsX = M'.pubsX)
    (hS : M.pubsS = M'.pubsS)
    (hLv : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsL AluSZChipJ9.pubALv) (M.pubsL (AluSZChipJ9.pubALv + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) (M'.pubsL AluSZChipJ9.pubALv) (M'.pubsL (AluSZChipJ9.pubALv + 1)))
    (hLs : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsL AluSZChipJ9.pubALs) (M.pubsL (AluSZChipJ9.pubALs + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) (M'.pubsL AluSZChipJ9.pubALs) (M'.pubsL (AluSZChipJ9.pubALs + 1)))
    (hLx : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsL AluSZChipJ9.pubALx) (M.pubsL (AluSZChipJ9.pubALx + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) (M'.pubsL AluSZChipJ9.pubALx) (M'.pubsL (AluSZChipJ9.pubALx + 1))) :
    NonChipJ9AL δ b Pb Rg c χ M := by
  have hpr8 : pinRecsJ8 δ Pb.toPubJ8 χ = pinRecsJ8 δ Pb'.toPubJ8 χ := by
    unfold pinRecsJ8; rw [hreg, hidxE, hrkE, hRtE]
  have hcen : censusGJ9 Pb.toPubJ8 c = censusGJ9 Pb'.toPubJ8 c := by
    unfold censusGJ9 censusG; rw [hreg, hRtE]
  have pRg := pinRgP_congr (p := p) (K := K) Pb Pb' hpr hix
  have pOp := pinOpP_congr (p := p) (K := K) Pb Pb' hpr
  have pRP := pinRecsP_congr δ Pb Pb' χ hpr hix hrkP
  have cP := censusP_congr Pb Pb' hpr
  exact
    { hnpC := by rw [hnC]; exact H.hnpC
      hkW := by rw [hkr]; exact H.hkW
      hknW := by rw [hkr, hnW]; exact H.hknW
      hkpW := by rw [hkr, hnW]; exact H.hkpW
      hnpA := by rw [hnA]; exact H.hnpA
      hGx := by rw [hρ, hW, hJ, hC, hLx]; exact H.hGx
      hGp := by rw [hρ, hX, hW]; exact H.hGp
      hGS := by rw [hreg, hidxE, pRg, pOp, hρS, hJ, hX, hA, hV, hS, hLs]; exact H.hGS
      hlay := by rw [hlayE, hRtE, hreg, hids]; exact H.hlay
      hsmall := by rw [hRtE, hreg, hids]; exact H.hsmall
      huniq := by rw [hRtE, hreg, hids]; exact H.huniq
      hTpl := by rw [hreg, hRtE]; exact H.hTpl
      hnd := by rw [hreg]; exact H.hnd
      hidx := by rw [hreg, hidxE]; exact H.hidx
      hrk := by rw [hreg, hrkE]; exact H.hrk
      hlt := by rw [hreg, hrkE, hidxE]; exact H.hlt
      hsumC' := by rw [hpr8, pRP, hm, hC, hA, hLv]; exact H.hsumC'
      hbalA' := by rw [hA, hV]; exact H.hbalA'
      hvalA0 := by rw [hA]; exact H.hvalA0
      hfxC := by rw [hC, hW]; exact H.hfxC
      hfxA := by rw [hA, hV]; exact H.hfxA
      hclI := by rw [hm]; exact H.hclI
      hclR := H.hclR
      hcen' := by rw [hcen, cP, hnA]; exact H.hcen'
      hlenC := by rw [hreg, hnC]; exact H.hlenC
      hlenA := by rw [hnA, hnV]; exact H.hlenA
      hcellF := H.hcellF
      hnAS := by rw [hnA, hnS]; exact H.hnAS
      hlenX := by rw [hnX, hn, hnS]; exact H.hlenX
      hPrim := by rw [hpr]; exact H.hPrim
      hdisjP := by rw [hpr, hreg]; exact H.hdisjP
      hlenL := ⟨hlenL1, by rw [hpr, hix]; exact H.hlenL.2⟩
      hndP := by rw [hpr]; exact H.hndP
      hrkP := by rw [hpr, hrkP]; exact H.hrkP
      hltP := by rw [hpr, hrkP, hix]; exact H.hltP
      hlenCP := hlenCP }

end Transport

/-! ## 3. Row-local ALU terminals do not depend on the row count past the table -/

section Sums
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows

theorem sum_fin_stable {M : Type} [AddCommMonoid M] (f : ℕ → M) (L n m : ℕ) (hn : L ≤ n) (hm : L ≤ m)
    (hz : ∀ i, L ≤ i → f i = 0) : ∑ i : Fin n, f i = ∑ i : Fin m, f i := by
  rw [Fin.sum_univ_eq_sum_range f n, Fin.sum_univ_eq_sum_range f m]
  have key : ∀ k, L ≤ k → ∑ i ∈ Finset.range k, f i = ∑ i ∈ Finset.range L, f i := by
    intro k hk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    have h0 : ∑ x ∈ Finset.range d, f (L + x) = 0 := Finset.sum_eq_zero (fun x _ => hz (L + x) (by omega))
    rw [Finset.sum_range_add, h0, add_zero]
  rw [key n hn, key m hm]

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]
  (chals : ℕ → K) (tb : List (BRow F × QRow (Quad (algebraMap F K δ))))

theorem rowAt_past {i : ℕ} (hi : tb.length ≤ i) : rowAt δ tb i = (padRow, QRow.zero) := by
  unfold rowAt; exact List.getD_eq_default _ _ hi

theorem sumV_stable {n m : ℕ} (hn : tb.length ≤ n) (hm : tb.length ≤ m) :
    ∑ i : Fin n, tV (n := n) δ chals tb i = ∑ i : Fin m, tV (n := m) δ chals tb i :=
  sum_fin_stable (fun i => Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ δ (rowAt δ tb i).1.aV * (dV δ chals tb i)⁻¹)
    tb.length n m hn hm (fun i hi => by
      rw [rowAt_past δ tb hi]; simp only [padRow, BRow.zero, Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ, map_zero, zero_mul])

theorem sumS_stable {n m : ℕ} (hn : tb.length ≤ n) (hm : tb.length ≤ m) :
    ∑ i : Fin n, tS (n := n) δ chals tb i = ∑ i : Fin m, tS (n := m) δ chals tb i :=
  sum_fin_stable (fun i =>
      Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ δ (wSv δ tb i) * (dR δ chals tb i)⁻¹ +
        Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ δ (wSv δ tb i) * (dO δ chals tb i)⁻¹ -
        Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ δ ((rowAt δ tb i).1.sH * (rowAt δ tb i).1.mJ) * (dJ δ chals tb i)⁻¹)
    tb.length n m hn hm (fun i hi => by
      simp only [wSv]; rw [rowAt_past δ tb hi]; simp only [padRow, BRow.zero, Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ, map_zero, zero_mul, mul_zero, sub_zero, add_zero])

theorem sumX_stable {n m : ℕ} (hn : tb.length ≤ n) (hm : tb.length ≤ m) :
    ∑ i : Fin n, tX (n := n) δ chals tb i = ∑ i : Fin m, tX (n := m) δ chals tb i :=
  sum_fin_stable (fun i => Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ δ (rowAt δ tb i).1.sH * (dX δ chals tb i)⁻¹)
    tb.length n m hn hm (fun i hi => by
      rw [rowAt_past δ tb hi]; simp only [padRow, BRow.zero, Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ, map_zero, zero_mul])

/-- On the padding-only table every row-local terminal vanishes. -/
theorem sumV_pad {n : ℕ} :
    ∑ i : Fin n, tV (n := n) δ chals [(padRow, QRow.zero)] i = 0 := by
  have h := sum_fin_stable (fun i => Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ δ
    (rowAt δ [((padRow : BRow F), (QRow.zero : QRow (Quad (algebraMap F K δ))))] i).1.aV *
      (dV δ chals [(padRow, QRow.zero)] i)⁻¹) 0 n 0 (Nat.zero_le _) le_rfl (fun i _ => by
    have hr : rowAt δ [((padRow : BRow F), (QRow.zero : QRow (Quad (algebraMap F K δ))))] i = (padRow, QRow.zero) := by
      unfold rowAt; rcases i with _ | i <;> rfl
    rw [hr]; simp only [padRow, BRow.zero, Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ, map_zero, zero_mul])
  exact h.trans (by simp)

theorem sumS_pad {n : ℕ} :
    ∑ i : Fin n, tS (n := n) δ chals [(padRow, QRow.zero)] i = 0 := by
  have h := sum_fin_stable (fun i =>
      Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ δ (wSv δ [((padRow : BRow F), (QRow.zero : QRow (Quad (algebraMap F K δ))))] i) *
          (dR δ chals [(padRow, QRow.zero)] i)⁻¹ +
        Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ δ (wSv δ [((padRow : BRow F), (QRow.zero : QRow (Quad (algebraMap F K δ))))] i) *
          (dO δ chals [(padRow, QRow.zero)] i)⁻¹ -
        Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ δ
          ((rowAt δ [((padRow : BRow F), (QRow.zero : QRow (Quad (algebraMap F K δ))))] i).1.sH *
            (rowAt δ [((padRow : BRow F), (QRow.zero : QRow (Quad (algebraMap F K δ))))] i).1.mJ) *
          (dJ δ chals [(padRow, QRow.zero)] i)⁻¹) 0 n 0 (Nat.zero_le _) le_rfl (fun i _ => by
    have hr : rowAt δ [((padRow : BRow F), (QRow.zero : QRow (Quad (algebraMap F K δ))))] i = (padRow, QRow.zero) := by
      unfold rowAt; rcases i with _ | i <;> rfl
    simp only [wSv]; rw [hr]; simp only [padRow, BRow.zero, Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ, map_zero, zero_mul, mul_zero, sub_zero, add_zero])
  exact h.trans (by simp)

theorem sumX_pad {n : ℕ} :
    ∑ i : Fin n, tX (n := n) δ chals [(padRow, QRow.zero)] i = 0 := by
  have h := sum_fin_stable (fun i => Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ δ
    (rowAt δ [((padRow : BRow F), (QRow.zero : QRow (Quad (algebraMap F K δ))))] i).1.sH *
      (dX δ chals [(padRow, QRow.zero)] i)⁻¹) 0 n 0 (Nat.zero_le _) le_rfl (fun i _ => by
    have hr : rowAt δ [((padRow : BRow F), (QRow.zero : QRow (Quad (algebraMap F K δ))))] i = (padRow, QRow.zero) := by
      unfold rowAt; rcases i with _ | i <;> rfl
    rw [hr]; simp only [padRow, BRow.zero, Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.liftQ, map_zero, zero_mul])
  exact h.trans (by simp)

end Sums

/-! ## 4. The two length facts for an ALU chip of up to `2^34` rows -/

section Lengths
open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data rowsOfT)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (N9)
open Nock.V1J8.Gen (callsOf)
open Nock.Jet.Prim (PrimOp)

variable {p : ℕ} [Fact p.Prime] [Fact (ringChar (ZMod p)).Prime]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (prims : List (ℕ × PrimOp))

/-- **`lengthsX`**: `nL + n < p` and `hlenCP` at the overlay data, for any ALU row count `nL ≤ 2^34`. -/
theorem lengthsX (hpG : p = Nock.Atoms.p)
    (h31 : ComplJ9ARun.Rows31A (ComplJ9ALData.j9alDataOf p Rg Rt prims hgen))
    (hnd : (prims.map Prod.fst).Nodup) (nL : ℕ) (hnL : nL ≤ 2 ^ 34) :
    nL + N9 t < p ∧
    3 + (ComplJ9ALData.j9alDataOf p Rg Rt prims hgen).regs.length +
      (ComplJ9ALData.primsC prims ((J8Data.calls (j9aDataOf p Rg Rt hgen)).map Prod.fst)).length + nL +
      2 * (ComplJ9ALData.j9alDataOf p Rg Rt prims hgen).cells.length < p := by
  have hp63 := ComplJ9AChains.hp63_of_G hpG
  have e34 : (2 : ℕ) ^ 34 < 2 ^ 60 := by norm_num
  have e31 : (2 : ℕ) ^ 31 < 2 ^ 60 := by norm_num
  have e60 : (2 : ℕ) ^ 60 * 8 = 2 ^ 63 := by norm_num
  have hN : N9 t ≤ 2 ^ 31 := h31 _ (ComplJ9ALStatic.memL_N9 Rt hgen prims)
  have hC : (ComplJ9ALData.j9alDataOf p Rg Rt prims hgen).cells.length ≤ 2 ^ 31 :=
    h31 _ (ComplJ9ALStatic.memL_cells Rt hgen prims)
  have hbfs : (Nock.Walk.bfsForest [t]).length ≤ 2 ^ 31 := h31 _ (ComplJ9ALStatic.memL_bfs Rt hgen prims)
  have hreg : (ComplJ9ALData.j9alDataOf p Rg Rt prims hgen).regs.length ≤ 2 ^ 31 :=
    (ComplJ9ALStatic.regsL_len Rt hgen prims).trans hbfs
  have hps : (ComplJ9ALData.primsC prims ((J8Data.calls (j9aDataOf p Rg Rt hgen)).map Prod.fst)).length ≤ 2 ^ 31 := by
    have hsub : ((ComplJ9ALData.primsC prims ((J8Data.calls (j9aDataOf p Rg Rt hgen)).map Prod.fst)).map
        Prod.fst).Sublist (prims.map Prod.fst) := List.Sublist.map Prod.fst List.filter_sublist
    have hnd' := hnd.sublist hsub
    have hsub2 : (ComplJ9ALData.primsC prims ((J8Data.calls (j9aDataOf p Rg Rt hgen)).map Prod.fst)).map Prod.fst ⊆
        (J8Data.calls (j9aDataOf p Rg Rt hgen)).map Prod.fst := by
      intro i hi
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
      simp only [ComplJ9ALData.primsC, List.mem_filter, decide_eq_true_eq] at hq
      exact hq.2
    have h1 := (hnd'.subperm hsub2).length_le
    rw [List.length_map, List.length_map] at h1
    have h2 : (J8Data.calls (j9aDataOf p Rg Rt hgen)).length ≤ (Nock.Walk.bfsForest [t]).length := by
      show (callsOf (rowsOfT t)).length ≤ _
      unfold callsOf rowsOfT
      exact (List.length_filterMap_le _ _).trans (by simp)
    omega
  constructor <;> omega

end Lengths

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHLink
