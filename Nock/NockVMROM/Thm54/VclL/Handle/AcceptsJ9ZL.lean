/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9ZL.lean

  **The compute side of an accepted J-9 trace** (atom walk absent; generic lemmas are
  layout-free).  New module, additive.
  * `envX9`: the compute environments at `pubVJ9`; `envX9_trace` (the trace is the J-8 one), so `stX`, `hdV`,
    `rowW`, `rowsWX` and the compute requests are the J-8 readouts (`stX_of_trace`, `rowsWX_envX9`, `reqs9_eq`).
  * `row0_pub` (any public vector, from `XCtx` alone), `row0_hd9` (row 0's handles are `claimKH`'s), `hseedJ9`,
    `hrealJ9` (a cell formula).
  * the `AcceptsJ9ZA` twins of the J-8 helpers that read `hsatX`: `compLenZA9`, `budX/P/S_ofZA9`, `hcount_ofZA9`,
    `rdWC_realize40Z9` / `linkJ8_L2Z9`, `walkX_servedZ9` / `hHXW_of_acceptsZ9`, and `hXW_of_ioA9` (no `hsatX`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9Z

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9ZL

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
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.CorJ8F (denJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree chalsOK_J8 chalsAJ8_ok)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY encZY_cell inlineAtoms_encZY)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC outside40C outside_sumJ8_D)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 wchain_out v0 v1)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8 (OutJ8 outJ8_of_outside chalsMJ8_z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.Atoms (lenL)
open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayLe realize40 realizeJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3
open Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8 (valReader)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (rowsMJ8 rowsB0 crA)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (censusList2)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z atomTZ)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_of_ne chalsAJ8Z_ok chalsAJ8Z_agree)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R4 (RR4 LL4 hHXV_ofZ)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ)
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun claimH isCellN)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crA crM crW crC staged_eq below_of_mem shV)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (mbXs claimCells claimRecsJ8 pinRecsJ8 rkC MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_zAt)
open Nock.NockVMROM.Thm54.VclL.Handle.RealVJ8
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R4
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R5
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (xS xF xE)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (envCJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP (toMsgJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 St40 sum40 fpx_out v4 v5 v6 v7)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (extY_below shV_round)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (compReqsX)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9Z
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8 (toMsgJ8ZA provsJ8A)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZLA (trip_rowOfXZ)

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G (AcceptsJ8ZG)

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8 bitFix bitFix_off)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayJ8 LayLe realize40 wdWJ8 cRowsJ8 envCJ8 stOfEnv
  stOfIdx stOfIdx_stIdx rowW_congr shV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX (stIdx)
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8 (stX stX_spec baseX_of_sat)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8 (rowW rowsWX)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8

open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8 (AcceptsJ8ZA provsJ8A)


open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G (AcceptsJ8ZG)

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

open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8 (AcceptsJ8ZA provsJ8A)


noncomputable section

/-! ## 1. Trace-only readouts -/

section Congr
variable {F : Type} [Field F]

theorem stX_of_trace {e e' : Env F} (h : e.trace = e'.trace) : stX e = stX e' := by
  have hfun : OneHotAt e = OneHotAt e' := funext fun j => by simp only [OneHotAt, h]
  unfold stX
  rw [hfun]

end Congr

section Gen
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chalV pv : ℕ → ZMod p}
  {P : Fin (computeChipVCLHX hn nodes b δ chalV pv orbit).rap.w → (ZMod p)[X]}

/-- **Row 0's claim handles are the publics `0..5`**, for ANY compute public vector (from `XCtx` alone; the proof
of `AcceptsJ8ZLA.row0_claimZ`). -/
theorem row0_pub {α γ seed : K} (XC : XCtx hn nodes b δ chalV pv orbit P α γ seed) :
    (envsN hn nodes chalV pv orbit P 0).trace xS.k = pv 0 ∧
    (envsN hn nodes chalV pv orbit P 0).trace xS.v = pv 1 ∧
    (envsN hn nodes chalV pv orbit P 0).trace xF.k = pv 2 ∧
    (envsN hn nodes chalV pv orbit P 0).trace xF.v = pv 3 ∧
    (envsN hn nodes chalV pv orbit P 0).trace xE.k = pv 4 ∧
    (envsN hn nodes chalV pv orbit P 0).trace xE.v = pv 5 := by
  have hB := RapWalkJ8.baseE XC hn
  have hF : (envsN hn nodes chalV pv orbit P 0).trace firstX = 1 := by
    have := (RapWalkJ8.walkRowsX_of_sat XC).first 0 hn
    simpa using this
  have key : ∀ (x y : ℕ), (⟨cc firstX, x, .pub y⟩ : EqG ℚ) ∈ (claimEq (F := ℚ)) →
      (envsN hn nodes chalV pv orbit P 0).trace x = pv y := by
    intro x y hg
    have h := RowSemChipX.eqg hB (List.mem_append_right _ hg) (by simpa [evalQX, cc] using hF)
    simpa [Opnd.expr, evalQX, RapWalkJ8.pubE XC 0] using h
  exact ⟨key _ _ (by simp [claimEq, hpub]), key _ _ (by simp [claimEq, hpub]),
    key _ _ (by simp [claimEq, hpub]), key _ _ (by simp [claimEq, hpub]),
    key _ _ (by simp [claimEq, hpub]), key _ _ (by simp [claimEq, hpub])⟩

end Gen

section Env
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

/-- The compute environments of the trace at `pubVJ9`. -/
abbrev envX9 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (i : ℕ) : Env (ZMod p) :=
  envsN Pb.hn Pb.nodes (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit
    (qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) i

theorem envX9_trace (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (i : ℕ) : (envX9 δ b Pb c χ M tr i).trace = (envX δ b Pb c χ M tr i).trace := by
  simp only [envX9, envX, TeleC.envsN]
  split_ifs <;> rfl

theorem hdV_envX9 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (i : ℕ) (hh : ChipH.Hd) : hdV (envX9 δ b Pb c χ M tr i) hh = hdV (envX δ b Pb c χ M tr i) hh := by
  simp only [hdV, envX9_trace]

theorem rowsWX_envX9 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) :
    rowsWX (fun i => envX9 δ b Pb c χ M tr i) (fun i => stX (envX9 δ b Pb c χ M tr i)) =
      rowsWX (fun i => envX δ b Pb c χ M tr i) (fun i => stX (envX δ b Pb c χ M tr i)) := by
  funext i
  simp only [rowsWX]
  rw [stX_of_trace (envX9_trace δ b Pb c χ M tr (i - 1)),
    TraceJ8.rowW_congr (fun j _ => congrFun (envX9_trace δ b Pb c χ M tr (i - 1)) j)]

/-- The compute requests do not read the publics. -/
theorem reqs9_eq (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (ext : (bl : Bal) → List (Fin (mOf bl) → K)) (bl : Bal) :
    reqsJ8 (hn := Pb.hn) (nodes := Pb.nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ9 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
        (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) ext bl =
      reqsJ8 (hn := Pb.hn) (nodes := Pb.nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
        (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) ext bl := by
  unfold reqsJ8
  rw [ReadIOJ8.compReqsX_congr (K := K) (qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ))
    (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) (fun _ _ _ _ => rfl) bl]

theorem compReqs9_eq (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (bl : Bal) :
    compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ9 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
        (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) bl =
      compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
        (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) bl :=
  ReadIOJ8.compReqsX_congr (K := K) (qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ))
    (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) (fun _ _ _ _ => rfl) bl

end Env

/-! ## 2. Row 0 at `pubVJ9` -/

section Root
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

/-- The compute context at `pubVJ9`. -/
theorem xctxJ9 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (hp : 17 < p)
    (hsatX : RAP.SatisfiesWithPreprocessing (computeChipVCLHX Pb.hn Pb.nodes b δ (chalVJ8 b χ)
      (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit) (qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)))
    (hinjX : Function.Injective Pb.nodes)
    (hadjX : ∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω) :
    XCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ))
      (limbVal b (chalVJ8 b χ) chalAlphaW) (limbVal b (chalVJ8 b χ) chalGammaW)
      (limbVal b (pubVJ9 δ b c M.m M.ρ M.ρS χ) pubSeed) :=
  ⟨hp, hsatX, hinjX, hadjX, rfl, rfl, pubVJ9_IC δ b c M.m M.ρ M.ρS χ, rfl, pubVJ9_out δ b c M.m M.ρ M.ρS χ⟩

variable {δ b}

/-- **Row 0's claim handles at `pubVJ9`**: kind and value of `claimKH` (`hdV` of `xS / xF / xE`). -/
theorem row0_hd9 {Pb : PubJ8 p} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8 p K δ} {tr : TrJ8 (ZMod p)}
    {α γ seed : K} (XC : XCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) α γ seed) :
    ∀ k : Fin 3, hdV (envX9 δ b Pb c χ M tr 0) (![xS, xF, xE] k) =
      ((((claimHJ9 p c M.m k).1 : ℕ) : ZMod p).val, (((claimHJ9 p c M.m k).2 : ℕ) : ZMod p).val) := by
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := row0_pub XC
  have L := fun j (hj : j < 6) => pubVJ9_label δ b c M.m M.ρ M.ρS χ j hj
  intro k
  fin_cases k
  · simp [hdV]; rw [p0, p1, L 0 (by norm_num), L 1 (by norm_num)]; simp [labelJ9]
  · simp [hdV]; rw [p2, p3, L 2 (by norm_num), L 3 (by norm_num)]; simp [labelJ9]
  · simp [hdV]; rw [p4, p5, L 4 (by norm_num), L 5 (by norm_num)]; simp [labelJ9]

/-- **`hseed` at `pubVJ9`**: the seed public is the walk seed of row 0's label. -/
theorem hseedJ9 {Pb : PubJ8 p} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8 p K δ} {tr : TrJ8 (ZMod p)}
    {α γ seed : K} (XC : XCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) α γ seed) :
    limbVal b (pubVJ9 δ b c M.m M.ρ M.ρS χ) pubSeed =
      Walk.rlc (limbVal b (chalVJ8 b χ) chalGammaW) (encT (K := K)
        (rowW (envX9 δ b Pb c χ M tr 0) (stX (envX9 δ b Pb c χ M tr 0))).trip) *
          limbVal b (chalVJ8 b χ) chalAlphaW := by
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := row0_pub XC
  rw [limb_pubVJ9_seed, Lift40J8.limb_gammaW_J8, Lift40J8.limb_alphaW_J8, rowW_trip, trip_rowOfXZ]
  have hA : toVS (toVSQ χ) cAlphaW = χ c13 := rfl
  have hG : toVS (toVSQ χ) cGamW = χ c14 := rfl
  simp only [encT, encH, hdV, WalkBridgeJ8.alg_val, p0, p1, p2, p3, p4, p5]
  simp [pubVJ9, seedJ9, labelJ9, List.zipIdx, Walk.rlc, Fin.sum_univ_succ, hA, hG]
  ring

/-- **`hreal` at `pubVJ9`, at a cell formula**. -/
theorem hrealJ9 {Pb : PubJ8 p} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8 p K δ} {tr : TrJ8 (ZMod p)}
    {α γ seed : K} (XC : XCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) α γ seed)
    (hfc : isCellN c.formula = true) :
    (stX (envX9 δ b Pb c χ M tr 0)).isChain = false := by
  obtain ⟨-, -, p2, -, -, -⟩ := row0_pub XC
  have hB := RapWalkJ8.baseE XC Pb.hn
  have hoh := RapWalkJ8.ohE XC Pb.hn
  have hk1 : (envX9 δ b Pb c χ M tr 0).trace xF.k = 1 := by
    rw [p2]
    obtain ⟨f, hf⟩ : ∃ l r, c.formula = .cell l r := by
      cases h : c.formula with
      | atom v => rw [h] at hfc; simp [isCellN] at hfc
      | cell l r => exact ⟨l, r, rfl⟩
    obtain ⟨r, hf⟩ := hf
    simp [pubVJ9, labelJ9, claimHJ9, claimKH, claimNoun, hf]
  have h10 : (1 : ZMod p) ≠ 0 := one_ne_zero
  cases hst : stX (envX9 δ b Pb c χ M tr 0)
  all_goals (try rfl)
  all_goals rw [hst] at hoh
  · have := s10L_row hB (RowSemChipX.oh_one hoh (by decide)) (RowSemChipX.oh_zero hoh (by decide) (by decide))
      (RowSemChipX.oh_zero hoh (by decide) (by decide))
    exact absurd (hk1.symm.trans this.1) h10
  · have := s10T_row hB (RowSemChipX.oh_one hoh (by decide)) (RowSemChipX.oh_zero hoh (by decide) (by decide))
    exact absurd (hk1.symm.trans this.1) h10

end Root

/-! ## 3. The `AcceptsJ9ZA` twins of the helpers -/
section Budgets9
open Nock.Jet.ChipJ8 (entsX ents0T ents1T ents2T ents3)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

variable {Rg : Nock.Jet.Registry} {r : RowsJ8} {g : ℕ}

theorem compLenZA9 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZA δ b Pb Rg c χ M tr) (hp : 17 < p) (bl : Bal) :
    (compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
        (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) bl).length ≤ ReadIOJ8.capB bl * Pb.n :=
  (compReqs9_eq δ b Pb c χ M tr bl) ▸
    ReadIOJ8.compReqsX_length_le hacc.hsatX (by rw [ZMod.ringChar_zmod_n]; exact hp) bl

theorem budX_ofZA9 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZA δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g) :
    (reqsOf δ b Pb c χ M tr .x).length ≤ 3 * r.N + r.W + r.rd ∧
      (liftP (δ := δ) (provsJ8 δ b Pb χ M tr .x)).length ≤ r.D := by
  refine ⟨?_, ?_⟩
  · rw [reqsOf_length]
    have h1 := compLenZA9 δ b Pb c χ M tr hacc hp .x
    have h2 : (extJ8 δ b Pb c χ M tr .x).length = Pb.nW + jCount entsX Pb.lay := by
      simp only [extJ8, byBal]
      erw [List.length_append, walkXReqs_length, jRd_length]
    simp only [ReadIOJ8.capB] at h1
    have := hB.x1
    omega
  · simp only [liftP, List.length_map]
    show (cellProvsW b Pb.nodesC Pb.orbitC _ _ _).length ≤ r.D
    simp only [cellProvsW, List.length_map, List.length_finRange]
    exact hB.x2

theorem budP_ofZA9 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZA δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g) :
    (reqsOf δ b Pb c χ M tr .p).length ≤ 2 * r.N ∧
      (liftP (δ := δ) (provsJ8 δ b Pb χ M tr .p)).length ≤ 2 * r.W := by
  refine ⟨?_, ?_⟩
  · rw [reqsOf_length]
    have h1 := compLenZA9 δ b Pb c χ M tr hacc hp .p
    have h2 : (extJ8 δ b Pb c χ M tr .p).length = 0 := rfl
    simp only [ReadIOJ8.capB] at h1
    have := hB.p1
    omega
  · simp only [liftP, List.length_map]
    show (ServeH.walkPProvs b Pb.nodesW Pb.orbitW _ _ _).length ≤ 2 * r.W
    rw [walkPProvs_length]; have := hB.p2; omega

/-- **`budS`** at `RR4A` (no atom-walk provider). -/
theorem budS_ofZA9 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZA δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g) :
    (reqsOf δ b Pb c χ M tr .s).length ≤ r.N + 2 * r.J + g ∧
      (effP (liftP (δ := δ) (provsJ8A δ b Pb χ M tr .s))).length ≤ r.calls + r.heads + r.blocks + r.J := by
  refine ⟨?_, ?_⟩
  · rw [reqsOf_length]
    have h1 := compLenZA9 δ b Pb c χ M tr hacc hp .s
    have h2 : (extJ8 δ b Pb c χ M tr .s).length =
        Pb.regs.length + (jCount ents0T Pb.lay + jCount ents1T Pb.lay) := by
      simp only [extJ8, byBal]
      erw [List.length_append, jCons_length]
      erw [List.length_map]
    simp only [ReadIOJ8.capB] at h1
    have := hB.s1
    omega
  · refine (List.length_filter_le _ _).trans ?_
    simp only [liftP, List.length_map]
    show (_ ++ pad8 _).length ≤ _
    simp only [List.length_append, pad8, List.length_map, jProv_length]
    have := AcceptsJ8ZBG.atomIncProvs_length_leZ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
      (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
    have := hB.s2
    omega

theorem hcount_ofZA9 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZA δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g)
    (hcap : 3 * r.N + r.W + r.rd < p ∧ 2 * r.N < p ∧ r.N + 2 * r.J + g < p) :
    ∀ bl, (reqsOf δ b Pb c χ M tr bl).length < p := by
  intro bl
  cases bl
  · exact lt_of_le_of_lt (budX_ofZA9 δ b Pb c χ M tr hacc hp hB).1 hcap.1
  · exact lt_of_le_of_lt (budP_ofZA9 δ b Pb c χ M tr hacc hp hB).1 hcap.2.1
  · exact lt_of_le_of_lt (budS_ofZA9 δ b Pb c χ M tr hacc hp hB).1 hcap.2.2

end Budgets9

section Twins
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {Rg : Nock.Jet.Registry}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

/-- **`LinkJ8.rdWC` (L2)** at `L := realize40 L0 (layPb Pb …) hL`: on a trace whose compute chip is accepted
(`AcceptsJ8.hsatX`), over `17 < p`, the compute rows `cRowsJ8` (coin-free environments, `stOfEnv`) are
`rowsWX` of the `frameJ8` environments `envX` and their one-hot states `stX`, and `cH = n`. -/
theorem rdWC_realize40Z9 (Pb : PubJ8 p) (skel : List Noun) (hs : skel.length ≤ 3)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hL : LayLe (layPb Pb skel hs) r) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZA δ b Pb Rg c χ M tr) (hp : 17 < p) :
    (realize40 δ b L0 (layPb Pb skel hs) hL).cRows tr =
        rowsWX (fun i => envX δ b Pb c χ M tr i) (fun i => stX (envX δ b Pb c χ M tr i)) ∧
      (realize40 δ b L0 (layPb Pb skel hs) hL).cH tr = Pb.n := by
  refine ⟨?_, rfl⟩
  show cRowsJ8 Pb.hn Pb.nodes Pb.orbit tr = _
  funext i
  show rowW (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C (i - 1)) (stOfEnv (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C (i - 1))) =
    rowW (envX δ b Pb c χ M tr (i - 1)) (stX (envX δ b Pb c χ M tr (i - 1)))
  generalize i - 1 = k
  have htr : (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C k).trace = (envX9 δ b Pb c χ M tr k).trace := by
    simp only [envCJ8, envX9, TeleC.envsN]
    split_ifs <;> rfl
  have htr' : (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C k).trace = (envX δ b Pb c χ M tr k).trace :=
    htr.trans (envX9_trace δ b Pb c χ M tr k)
  have hB : BaseHoldsX (envX9 δ b Pb c χ M tr k) := by
    simp only [envX9, TeleC.envsN]
    split_ifs
    · exact baseX_of_sat Pb.hn Pb.nodes b δ _ _ Pb.orbit _ hacc.hsatX _ (mem_rowNodeSet _ _)
    · exact baseX_of_sat Pb.hn Pb.nodes b δ _ _ Pb.orbit _ hacc.hsatX _ (mem_rowNodeSet _ _)
  have hc : nStates < ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n]; exact hp
  have hoh := stX_spec hB hc
  have hoh' : OneHotAt (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C k) (stIdx (stX (envX9 δ b Pb c χ M tr k))) :=
    fun j hj => by rw [congrFun htr j]; exact hoh j hj
  rw [stOfEnv_of_oneHot hoh', stX_of_trace (envX9_trace δ b Pb c χ M tr k),
    TraceJ8.rowW_congr (fun j _ => congrFun htr' j)]

/-- **L2 of `LinkJ8`, both fields**, at `L := realize40 L0 (layPb Pb …) hL`. -/
theorem linkJ8_L2Z9 (Pb : PubJ8 p) (skel : List Noun) (hs : skel.length ≤ 3)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hL : LayLe (layPb Pb skel hs) r) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZA δ b Pb Rg c χ M tr) (hp : 17 < p) :
    ((realize40 δ b L0 (layPb Pb skel hs) hL).cRows tr =
        rowsWX (fun i => envX δ b Pb c χ M tr i) (fun i => stX (envX δ b Pb c χ M tr i)) ∧
      (realize40 δ b L0 (layPb Pb skel hs) hL).cH tr = Pb.n) ∧
    (realize40 δ b L0 (layPb Pb skel hs) hL).wdW tr (toVSQ χ) =
      walkDataOf δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW))) :=
  ⟨rdWC_realize40Z9 δ b Pb skel hs L0 hL c χ M tr hacc hp, rdWW_realize40 δ b Pb skel hs L0 hL χ M tr⟩


/-- **Every J-8 walk read is a cell-table provided key** on an accepted trace, outside the compute's handle IO
events at the real lists (`s` at the effective providers), with the `x` count `< p`. -/
theorem walkX_servedZ9 [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZA δ b Pb Rg c χ M tr)
    (hp : 64 ≤ p)
    (hx : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .x) (liftP (provsJ8 δ b Pb χ M tr .x)))
    (hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .p) (liftP (provsJ8 δ b Pb χ M tr .p)))
    (hs : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .s) (effP (liftP (provsJ8A δ b Pb χ M tr .s))))
    (hcx : (reqsOf δ b Pb c χ M tr .x).length < p) :
    ∀ j : Fin Pb.nW, ServeH.keyVec5 (K := K) WalkHC.xKeyH
        (wEF b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) j) ∈
      (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)).map
        Prod.fst := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hF := GeneratedField.primeFieldElems_zmod p
  have B : TeleCQX.BCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) :=
    ⟨by rw [hrc]; show 17 < p; omega, hacc.hsatX, hacc.hinjX, hacc.hadjX⟩
  have hcv := VerJ8.coinsCV_J8 δ b χ
  have hG := (VerJ8.goodCJ8_iff (δ := δ) (b := b) c M.m M.ρ M.ρS χ M.pubsC M.pubsW M.pubsJ M.ρS 0).2
    ⟨hacc.hGx, hacc.hGp, add_zero _⟩
  have he := JGenJ8.extX_sumQG δ b (coinsCV b δ (chalVJ8 b χ)) Pb.kroots Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ)
    M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) hacc.hsatW hacc.hbindW hF (by rw [hrc]; exact hp)
    hacc.hinjW hacc.hadjW ((VerJ8.mcoins_J8 δ χ).trans hcv.symm)
    Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)
    hacc.hJk ((VerJ8.coinsJX_J8 δ χ).trans hcv.symm)
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
      (pubVal := pubVJ9 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
      (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) bl,
      compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r) ≠ 0 := by
    intro bl r hr
    rw [compReqs9_eq δ b Pb c χ M tr bl] at hr
    cases bl with
    | s => exact TeleC.den_ne_of_out _ _ _ _ hs _ (List.mem_map_of_mem (List.mem_append_left _ hr))
    | x => exact TeleC.den_ne_of_out _ _ _ _ hx _ (List.mem_map_of_mem (List.mem_append_left _ hr))
    | p => exact TeleC.den_ne_of_out _ _ _ _ hpp _ (List.mem_map_of_mem (List.mem_append_left _ hr))
  have hserved : ∀ r ∈ reqsOf δ b Pb c χ M tr .x, r ∈ (liftP (provsJ8 δ b Pb χ M tr .x)).map Prod.fst := by
    refine ServeH.served_of_balance (p := p) _ _ _ _ (TeleC.den_ne_of_out _ _ _ _ hx)
      (den_prov_ne_of_out _ _ _ _ hx) ?_ hcx hx
    have h1 := compReqsX_sum B hne .x
    rw [compReqs9_eq δ b Pb c χ M tr .x] at h1
    change _ = ServedJ8.rhoX (K := K) (b := b) (δ := δ) (pubVal := pubVJ9 δ b c M.m M.ρ M.ρS χ) .x at h1
    rw [rhoX_pubVJ9 δ b c M.m M.ρ M.ρS χ .x] at h1
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
theorem hHXW_of_acceptsZ9 [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZA δ b Pb Rg c χ M tr)
    (hp : 64 ≤ p)
    (hx : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .x) (liftP (provsJ8 δ b Pb χ M tr .x)))
    (hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .p) (liftP (provsJ8 δ b Pb χ M tr .p)))
    (hs : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .s) (effP (liftP (provsJ8A δ b Pb χ M tr .s))))
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
    (walkX_servedZ9 δ b Pb c χ M tr hacc hp hx hpp hs hcx)


/-- **`LinkJ8.hXW` from the fingerprint-export lookup** (the class of `LinkJ8R2V.hXV_of_io`): on an `AcceptsJ8Z`
trace, with `pubsC(2,3) = pubsW(0,1)` and the validity pair outside the IO failure event of the J-8 walk's keys
(at the `bitFix` view) against the cell table's export records, every key the J-8 walk consumes is a decoded cell
row. -/
theorem hXW_of_ioA9 [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ9ZA δ b Pb Rg c χ M tr) (hp : 64 ≤ p)
    (hWC : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 2) (M.pubsC 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsW 0) (M.pubsW 1))
    (hout : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr) (fxProvsJ8 δ b Pb.nodesC Pb.orbitC tr)) :
    WalkVCL.KeysExported (cellT δ b Pb χ M tr)
      (walkDataOf δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (AtomWalkAW.restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)))).X := by
  have hF := GeneratedField.primeFieldElems_zmod p
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp64 : 64 ≤ ringChar (ZMod p) := by rw [hrc]; exact hp
  have hsatC := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _
    hacc.hsatC
  have hbindC := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _
    hacc.hbindC
  have hsatP := AtomWalkAW.walkChipHQK_restrict_sat δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _
    (WalkJ8.walkChipJ8_bitFix_sat δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _ hF hp64 hacc.hsatW)
  have hbindP := AtomWalkAW.walkChipHQK_restrict_bind δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ)
    M.pubsW _ (WalkJ8.walkChipJ8_bitFix_bind δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _
      hacc.hbindW)
  have hrq : walkXInternal δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (AtomWalkAW.restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW))) = fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr :=
    wXInt_bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW _ _ _ _ tr.W
  have hpv : liftWts (cellXRecords δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))) = fxProvsJ8 δ b Pb.nodesC Pb.orbitC tr := by
    have hw : 183 ≤ (cellChip δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.w := by
      rw [cell_w]; norm_num
    rw [cXRec_chip]
    exact congrArg liftWts
      (cXRec_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ hw (by norm_num) fun j hj => congrArg tr.M (Fin.ext rfl))
  rw [← hrq, ← hpv] at hout
  have hcnt : (walkXInternal δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (AtomWalkAW.restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)))).length < p := by
    rw [walkXInternal_length]
    have h := hacc.hkpW
    rw [hrc] at h
    omega
  exact walk_keys_exported δ Pb.kroots b Pb.hnC Pb.nodesC Pb.orbitC Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ)
    M.pubsC M.pubsW _ _ hsatC hbindC hacc.hinjC hacc.hadjC hsatP hbindP hacc.hinjW hacc.hadjW _ _
    (ProbJ8.chalsOK_J8 δ χ) 0 (by rw [zero_add]; exact hWC) (p := p) [] (by simp) (by simp)
    (fun hc => hout (mem_IOFailureEventW_iff.mpr (Or.inl hc)))
    (fun hc => hout (mem_IOFailureEventW_iff.mpr (Or.inr (Or.inr hc)))) (by simpa using hcnt)


end Twins

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9ZL
