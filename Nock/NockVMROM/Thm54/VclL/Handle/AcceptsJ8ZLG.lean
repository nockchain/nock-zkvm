/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8ZLG.lean

  **`AcceptsJ8ZL` restated over `AcceptsJ8G.AcceptsJ8ZG`** (the J chip present
  or absent).  The proofs read no J-chip conjunct; text verbatim
  otherwise.  New module, additive.  The original header follows.
-/
/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8ZL.lean

  **The compute-side derivations at `AcceptsJ8Z`.**  New module, additive.
  Verbatim twins (hypothesis `AcceptsJ8Z` in place of `AcceptsJ8`; the proofs read compute / cell / walk / J fields
  only, whose names and types are unchanged) of `LinkJ8Q3.xctxJ8 / row0_claim / hseedJ8 / hrealJ8` and
  `AcceptsJ8P.row0_hd`: `xctxJ8Z`, `row0_claimZ`, **`hseedJ8Z`**, **`hrealJ8Z`**, `row0_hdZ`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZLG

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G (AcceptsJ8ZG)

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
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Reads)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8 (AWSeedsOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.FibreJ8 (effP)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (compReqsX)
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.CorJ8F (denJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree chalsOK_J8)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY encZY_cell inlineAtoms_encZY)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC outside40C outside_sumJ8_D)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 wchain_out v0 v1)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8 (OutJ8 outJ8_of_outside chalsMJ8_z)
open Nock.Atoms (lenL)

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q3
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (pubVJ8_label)

noncomputable section

section Root
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

/-- The compute context `XCtx` of an accepted trace (as inside `hsoundJ8`). -/
theorem xctxJ8Z (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p) (hacc : AcceptsJ8ZG δ b Pb Rg c χ M tr) :
    XCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ))
      (limbVal b (chalVJ8 b χ) chalAlphaW) (limbVal b (chalVJ8 b χ) chalGammaW)
      (limbVal b (pubVJ8 δ b c M.m M.ρ M.ρS χ) pubSeed) :=
  ⟨hp, hacc.hsatX, hacc.hinjX, hacc.hadjX, rfl, rfl, pubVJ8_IC δ b c M.m M.ρ M.ρS χ, rfl,
    pubVJ8_out δ b c M.m M.ρ M.ρS χ⟩

/-- **Row 0's claim handles are the claim publics** (`claimEq` under `isFirst`). -/
theorem row0_claimZ (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p) (hacc : AcceptsJ8ZG δ b Pb Rg c χ M tr) :
    (envX δ b Pb c χ M tr 0).trace xS.k = pubVJ8 δ b c M.m M.ρ M.ρS χ 0 ∧
    (envX δ b Pb c χ M tr 0).trace xS.v = pubVJ8 δ b c M.m M.ρ M.ρS χ 1 ∧
    (envX δ b Pb c χ M tr 0).trace xF.k = pubVJ8 δ b c M.m M.ρ M.ρS χ 2 ∧
    (envX δ b Pb c χ M tr 0).trace xF.v = pubVJ8 δ b c M.m M.ρ M.ρS χ 3 ∧
    (envX δ b Pb c χ M tr 0).trace xE.k = pubVJ8 δ b c M.m M.ρ M.ρS χ 4 ∧
    (envX δ b Pb c χ M tr 0).trace xE.v = pubVJ8 δ b c M.m M.ρ M.ρS χ 5 := by
  have XC := xctxJ8Z δ b Pb Rg c χ M tr hp hacc
  have hB := RapWalkJ8.baseE XC Pb.hn
  have hF : (envX δ b Pb c χ M tr 0).trace firstX = 1 := by
    have := (RapWalkJ8.walkRowsX_of_sat XC).first 0 Pb.hn
    simpa using this
  have key : ∀ (x y : ℕ), (⟨cc firstX, x, .pub y⟩ : EqG ℚ) ∈ (claimEq (F := ℚ)) →
      (envX δ b Pb c χ M tr 0).trace x = pubVJ8 δ b c M.m M.ρ M.ρS χ y := by
    intro x y hg
    have h := RowSemChipX.eqg hB (List.mem_append_right _ hg) (by simpa [evalQX, cc] using hF)
    simpa [Opnd.expr, evalQX, RapWalkJ8.pubE XC 0] using h
  exact ⟨key _ _ (by simp [claimEq, hpub]), key _ _ (by simp [claimEq, hpub]),
    key _ _ (by simp [claimEq, hpub]), key _ _ (by simp [claimEq, hpub]),
    key _ _ (by simp [claimEq, hpub]), key _ _ (by simp [claimEq, hpub])⟩

theorem trip_rowOfXZ (env : Env (ZMod p)) (st : Nock.Edit.StateX) :
    (rowOfX env st).trip = (hdV env xS, hdV env xF, hdV env xE) := rfl

/-- **L8 `hseed`, discharged**: the seed public is the walk seed of row 0's label. -/
theorem hseedJ8Z (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p) (hacc : AcceptsJ8ZG δ b Pb Rg c χ M tr) :
    limbVal b (pubVJ8 δ b c M.m M.ρ M.ρS χ) pubSeed =
      Walk.rlc (limbVal b (chalVJ8 b χ) chalGammaW) (encT (K := K)
        (rowW (envX δ b Pb c χ M tr 0) (stX (envX δ b Pb c χ M tr 0))).trip) *
          limbVal b (chalVJ8 b χ) chalAlphaW := by
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := row0_claimZ δ b Pb Rg c χ M tr hp hacc
  rw [limbVal_pubVJ8_low δ b c M.m M.ρ M.ρS χ _ (by simp [pubSeed]),
    limbVal_pubVHQ_low δ b c M.m M.ρ _ _ (by simp [pubSeed]), FrameVS.limb_pubVH_seed,
    Lift40J8.limb_gammaW_J8, Lift40J8.limb_alphaW_J8, rowW_trip, trip_rowOfXZ]
  have hA : toVS (toVSQ χ) cAlphaW = χ c13 := rfl
  have hG : toVS (toVSQ χ) cGamW = χ c14 := rfl
  simp only [encT, encH, hdV, WalkBridgeJ8.alg_val, p0, p1, p2, p3, p4, p5]
  simp [pubVJ8, pubVHQ, pubVH, seedVS, labelF, hvalF, List.zipIdx, Walk.rlc, Fin.sum_univ_succ, hA, hG]
  ring

/-- **L8 `hreal`, discharged at a cell formula**: row 0's formula handle has kind `1`, and a chain state's
formula handle has kind `0` (`s10L_row`, `s10T_row`). -/
theorem hrealJ8Z (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p) (hacc : AcceptsJ8ZG δ b Pb Rg c χ M tr)
    (hfc : isCellN c.formula = true) :
    (stX (envX δ b Pb c χ M tr 0)).isChain = false := by
  obtain ⟨-, -, p2, -, -, -⟩ := row0_claimZ δ b Pb Rg c χ M tr hp hacc
  have XC := xctxJ8Z δ b Pb Rg c χ M tr hp hacc
  have hB := RapWalkJ8.baseE XC Pb.hn
  have hoh := RapWalkJ8.ohE XC Pb.hn
  have hk1 : (envX δ b Pb c χ M tr 0).trace xF.k = 1 := by
    rw [p2]
    obtain ⟨f, hf⟩ : ∃ l r, c.formula = .cell l r := by
      cases h : c.formula with
      | atom v => rw [h] at hfc; simp [isCellN] at hfc
      | cell l r => exact ⟨l, r, rfl⟩
    obtain ⟨r, hf⟩ := hf
    simp [pubVJ8, pubVHQ, pubVH, labelF, hvalF, claimH, claimNoun, claimHandle, hf]
  have h10 : (1 : ZMod p) ≠ 0 := one_ne_zero
  cases hst : stX (envX δ b Pb c χ M tr 0)
  all_goals (try rfl)
  all_goals rw [hst] at hoh
  · have := s10L_row hB (RowSemChipX.oh_one hoh (by decide)) (RowSemChipX.oh_zero hoh (by decide) (by decide))
      (RowSemChipX.oh_zero hoh (by decide) (by decide))
    exact absurd (hk1.symm.trans this.1) h10
  · have := s10T_row hB (RowSemChipX.oh_one hoh (by decide)) (RowSemChipX.oh_zero hoh (by decide) (by decide))
    exact absurd (hk1.symm.trans this.1) h10


/-- **Row 0's claim handles, as handles**: kind and value of claim noun `k` (`hdV` of `xS / xF / xE`). -/
theorem row0_hdZ (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p) (hacc : AcceptsJ8ZG δ b Pb Rg c χ M tr) :
    ∀ k : Fin 3, hdV (envX δ b Pb c χ M tr 0) (![xS, xF, xE] k) =
      (((if (claimH c M.m k).1 then 1 else 0 : ZMod p)).val, (((claimH c M.m k).2 : ℕ) : ZMod p).val) := by
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := row0_claimZ δ b Pb Rg c χ M tr hp hacc
  intro k
  have L := fun j (hj : j < 6) => pubVJ8_label δ b c M.m M.ρ M.ρS χ j hj
  fin_cases k
  · simp [hdV]; rw [p0, p1, L 0 (by norm_num), L 1 (by norm_num)]; simp [labelF, hvalF]; try rfl
  · simp [hdV]; rw [p2, p3, L 2 (by norm_num), L 3 (by norm_num)]; simp [labelF, hvalF]; try rfl
  · simp [hdV]; rw [p4, p5, L 4 (by norm_num), L 5 (by norm_num)]; simp [labelF, hvalF]; try rfl

end Root

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZLG
