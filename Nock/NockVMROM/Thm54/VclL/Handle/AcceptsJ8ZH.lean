/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8ZH.lean

  **`hHXW` at `AcceptsJ8Z`.**  New module, additive.  Verbatim twins
  (hypothesis `AcceptsJ8Z`; the proofs read compute / cell / J-8 walk / J fields only) of
  `LinkJ8Q1H.walkX_served / hHXW_of_accepts`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1H

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZH

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec liftRec_inj)
open Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW restrictHQKWCell cellB0Of_hqkw
  cellChipHQKW_width)
open Nock.NockVMROM.Thm54.VclL.Handle.ProvXJ8 (exportRecK_lt)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8 bitFix bitFix_off)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8 (childHOfK)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal computeChipVCLHX nStates)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf compReqsX compReqsX_sum)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (BalJ8 reqsJ8 liftP den_prov_ne_of_out)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.Jet.FibreJ8 (effP)
open Nock.ComputeTable (FP)

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1H
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8

noncomputable section

section Accepts
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **Every J-8 walk read is a cell-table provided key** on an accepted trace, outside the compute's handle IO
events at the real lists (`s` at the effective providers), with the `x` count `< p`. -/
theorem walkX_servedZ [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8Z δ b Pb Rg c χ M tr)
    (hp : 64 ≤ p)
    (hx : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .x) (liftP (provsJ8 δ b Pb χ M tr .x)))
    (hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .p) (liftP (provsJ8 δ b Pb χ M tr .p)))
    (hs : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .s) (effP (liftP (provsJ8 δ b Pb χ M tr .s))))
    (hcx : (reqsOf δ b Pb c χ M tr .x).length < p) :
    ∀ j : Fin Pb.nW, ServeH.keyVec5 (K := K) WalkHC.xKeyH
        (wEF b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) j) ∈
      (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)).map
        Prod.fst := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hF := GeneratedField.primeFieldElems_zmod p
  have B : TeleCQX.BCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) :=
    ⟨by rw [hrc]; show 17 < p; omega, hacc.hsatX, hacc.hinjX, hacc.hadjX⟩
  have hcv := VerJ8.coinsCV_J8 δ b χ
  have hG := (VerJ8.goodCJ8_iff (δ := δ) (b := b) c M.m M.ρ M.ρS χ M.pubsC M.pubsW M.pubsJ M.ρS 0).2
    ⟨hacc.hGx, hacc.hGp, add_zero _⟩
  have he := BalXJ8.extX_sumQ δ b (coinsCV b δ (chalVJ8 b χ)) Pb.kroots Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ)
    M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) hacc.hsatW hacc.hbindW hF (by rw [hrc]; exact hp)
    hacc.hinjW hacc.hadjW ((VerJ8.mcoins_J8 δ χ).trans hcv.symm)
    Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)
    hacc.hsatJ hacc.hbindJ hacc.hinjJ hacc.hnJ hacc.hadjJ ((VerJ8.coinsJX_J8 δ χ).trans hcv.symm)
  have hpr := BalXJ8.provsX_sumQ δ b (coinsCV b δ (chalVJ8 b χ)) Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) hacc.hsatC hacc.hbindC hacc.hinjC hacc.hadjC
    ((VerJ8.mcoins_J8 δ χ).trans hcv.symm)
  have hbx : ServedJ8.rhoX (b := b) (δ := δ) (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) .x +
      ((extJ8 δ b Pb c χ M tr .x).map fun r => (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum =
      ((provsJ8 δ b Pb χ M tr .x).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) q.1))⁻¹).sum := by
    show _ + ((ServeH.walkXReqs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) ++
      Nock.Jet.RapJetJ8.jRd b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)).map
        _).sum = ((cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)).map
          _).sum
    convert hG .x using 2 <;> first | exact he | exact hpr
  have hne : ∀ bl, ∀ r ∈ compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
      (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
      (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) bl,
      compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r) ≠ 0 := by
    intro bl r hr
    cases bl with
    | s => exact TeleC.den_ne_of_out _ _ _ _ hs _ (List.mem_map_of_mem (List.mem_append_left _ hr))
    | x => exact TeleC.den_ne_of_out _ _ _ _ hx _ (List.mem_map_of_mem (List.mem_append_left _ hr))
    | p => exact TeleC.den_ne_of_out _ _ _ _ hpp _ (List.mem_map_of_mem (List.mem_append_left _ hr))
  have hserved : ∀ r ∈ reqsOf δ b Pb c χ M tr .x, r ∈ (liftP (provsJ8 δ b Pb χ M tr .x)).map Prod.fst := by
    refine ServeH.served_of_balance (p := p) _ _ _ _ (TeleC.den_ne_of_out _ _ _ _ hx)
      (den_prov_ne_of_out _ _ _ _ hx) ?_ hcx hx
    have h1 := compReqsX_sum B hne .x
    have h2 := hbx
    unfold reqsOf reqsJ8 liftP
    rw [List.map_map, List.map_append, List.sum_append, List.map_map]
    simp only [Function.comp_def] at h1 ⊢
    rw [h1]
    exact h2
  intro j
  have hc : ServeH.keyVec5 (K := K) WalkHC.xKeyH
      (wEF b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) j) ∈
      extJ8 δ b Pb c χ M tr .x :=
    List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange j))
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (hserved _ (List.mem_map_of_mem (List.mem_append_right _ hc)))
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨q0, hq0, liftRec_inj hqe⟩

/-- **`LinkJ8.hHXW` (L4)** on an accepted trace outside the compute's handle IO events at the real lists. -/
theorem hHXW_of_acceptsZ [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8Z δ b Pb Rg c χ M tr)
    (hp : 64 ≤ p)
    (hx : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .x) (liftP (provsJ8 δ b Pb χ M tr .x)))
    (hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .p) (liftP (provsJ8 δ b Pb χ M tr .p)))
    (hs : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .s) (effP (liftP (provsJ8 δ b Pb χ M tr .s))))
    (hcx : (reqsOf δ b Pb c χ M tr .x).length < p) :
    ∀ j < Pb.nW, ∃ c' ∈ cellT δ b Pb χ M tr,
      (natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j).trace WChip.idx),
        WalkKJ8.childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) false,
        WalkKJ8.childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) true) = exportRecK c'.b0 :=
  hHXW_of_served δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC Pb.kroots Pb.hnW Pb.nodesW Pb.orbitW
    (chalsMJ8 δ χ) M.pubsW (by omega) _ hacc.hsatC _
    (walkX_servedZ δ b Pb c χ M tr hacc hp hx hpp hs hcx)

end Accepts

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZH
