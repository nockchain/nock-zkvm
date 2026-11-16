/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8ZS.lean

  **`hseedsV` at `chalsAJ8Z`.**  New module, additive.  Twins of
  `LinkJ8Q1S.rowsAJ8_eq_atomT / hseedsV_of_outside` at `atomTZ` (the round-0 rows read no coin; `chalsAJ8Z_y`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1S

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZS

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C outside_sumJ8_D)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_y)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayLe realizeJ8 rowsAJ8 rowsB0)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8 (AWSeedsOK)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1S
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8

noncomputable section

section Seeds
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

/-- **The atom table's round-0 readout is the decoded table's `b0`** (any coins, any messages). -/
theorem rowsAJ8_eq_atomTZ (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    rowsAJ8 Pb.nodesA Pb.orbitA tr = (atomTZ δ b Pb χ M tr).map (·.b0) := by
  unfold rowsAJ8 rowsB0 atomTZ cellTableOf
  rw [List.map_ofFn]
  congr 1

/-- **`LinkJ8.hseedsV`** outside the #8 group, at a data whose `rowsA` reads the trace's atom table. -/
theorem hseedsV_of_outsideZ (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (hout : ∀ s ∈ allJ8C R, ¬ s.mem tr χ)
    (hrA : R.D.rowsA tr = (atomTZ δ b Pb χ M tr).map (·.b0)) (hΛ : fuelChip ≤ r.Λ) :
    AWSeedsOK δ (Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 2) (chalsAJ8Z δ χ 3)) (atomTZ δ b Pb χ M tr) := by
  have hs := outside_sumJ8_D R hout .atomCensus (by decide) (by decide) (by decide)
  simp only [sumJ8, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hs
  obtain ⟨hd, hc, -⟩ := hs
  rw [chalsAJ8Z_y]
  refine ⟨fun hm => hc ?_, fun hm => hd ?_⟩
  · rw [atomCensusJ8, tableCensusSummand_mem_iff, hrA]
    rw [tableBadSeeds, PreSeedCensus.mem_pairBadSeeds_iff] at hm ⊢
    obtain ⟨pr, hpr, h1, h2, hsep⟩ := hm
    refine ⟨pr, ?_, h1.trans hΛ, h2.trans hΛ, hsep⟩
    rw [censusNouns, List.append_nil] at hpr
    exact Handle.CensusVS.allPairs_append_mem _ _ hpr
  · rw [atomDyckJ8, cellDyckRootSummand, towerSeedSummand_mem_iff, hrA]
    exact hm

end Seeds

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZS
