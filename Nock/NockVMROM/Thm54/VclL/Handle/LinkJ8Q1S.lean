/-
  Nock/NockVMROM/Thm54/VclL/Handle/LinkJ8Q1S.lean

  **`LinkJ8.hseedsV` (L6, the atom walk's two table-side
  seed events).**

  * **`rowsAJ8_eq_atomT`**: the atom table's round-0 readout `TraceJ8.rowsAJ8` (coin-free environments of the raw
    atom trace) is the `b0` projection of `AcceptsJ8.atomT` (the decoded restricted atom table), at any coins
    and messages (columns `< 129`, below the restriction's shift `129 → 205`).
  * **`hseedsV_of_outside`**: outside the J-8 list's #8 group (`atomDyckJ8`, `atomCensusJ8`), when the data's
    `rowsA` reads the trace's atom table (`hrA`) and `fuelChip ≤ Λ` (the census corner), `AWSeedsOK` holds at
    the atom walk's limb coin `(chalsAJ8 2, chalsAJ8 3) = y`: the dyck-root event is the same set; the
    census event at `(Λ, skelA)` contains the one at `(fuelChip, [])` (more pairs, looser leaf guard).
  * **`hseedsV_realizeJ8`**: the same at `R := realizeJ8 R0 (layPb Pb …) …` (its `rowsA` IS `rowsAJ8`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1S

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

noncomputable section

section Seeds
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

/-- **The atom table's round-0 readout is the decoded table's `b0`** (any coins, any messages). -/
theorem rowsAJ8_eq_atomT (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    rowsAJ8 Pb.nodesA Pb.orbitA tr = (atomT δ b Pb χ M tr).map (·.b0) := by
  unfold rowsAJ8 rowsB0 atomT cellTableOf
  rw [List.map_ofFn]
  congr 1

/-- **`LinkJ8.hseedsV`** outside the #8 group, at a data whose `rowsA` reads the trace's atom table. -/
theorem hseedsV_of_outside (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (hout : ∀ s ∈ allJ8C R, ¬ s.mem tr χ)
    (hrA : R.D.rowsA tr = (atomT δ b Pb χ M tr).map (·.b0)) (hΛ : fuelChip ≤ r.Λ) :
    AWSeedsOK δ (Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8 δ χ 2) (chalsAJ8 δ χ 3)) (atomT δ b Pb χ M tr) := by
  have hs := outside_sumJ8_D R hout .atomCensus (by decide) (by decide) (by decide)
  simp only [sumJ8, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hs
  obtain ⟨hd, hc, -⟩ := hs
  rw [chalsAJ8_y]
  refine ⟨fun hm => hc ?_, fun hm => hd ?_⟩
  · rw [atomCensusJ8, tableCensusSummand_mem_iff, hrA]
    rw [tableBadSeeds, PreSeedCensus.mem_pairBadSeeds_iff] at hm ⊢
    obtain ⟨pr, hpr, h1, h2, hsep⟩ := hm
    refine ⟨pr, ?_, h1.trans hΛ, h2.trans hΛ, hsep⟩
    rw [censusNouns, List.append_nil] at hpr
    exact Handle.CensusVS.allPairs_append_mem _ _ hpr
  · rw [atomDyckJ8, cellDyckRootSummand, towerSeedSummand_mem_iff, hrA]
    exact hm

/-- **`LinkJ8.hseedsV` at the realized data** `withLiftC (realizeJ8 R0 (layPb Pb …) …) L` (the shape of
`probJ8_final`'s `R`, with `realizeJ8` in place of `withWalkV`): its `rowsA` is `rowsAJ8`. -/
theorem hseedsV_realizeJ8
    (R0 : DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L : Lift40J8.Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (Pb : PubJ8 p) (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (ext : TrJ8 (ZMod p) → ℕ → Option Noun)
    (hext : ∀ Q : Coins frameJ8 K → TrJ8 (ZMod p), StJ8 Q → ∀ χ χ', ext (Q χ) = ext (Q χ'))
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (hout : ∀ s ∈ allJ8C (ListJ8C.withLiftC (realizeJ8 (g := g) δ b R0 (layPb Pb skel hs) hL ext hext hP hnM) L),
      ¬ s.mem tr χ)
    (hΛ : fuelChip ≤ r.Λ) :
    AWSeedsOK δ (Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8 δ χ 2) (chalsAJ8 δ χ 3)) (atomT δ b Pb χ M tr) :=
  hseedsV_of_outside δ b _ Pb χ M tr hout (rowsAJ8_eq_atomT δ b Pb χ M tr) hΛ

end Seeds

end

end Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1S
