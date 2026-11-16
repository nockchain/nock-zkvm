/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8ZWG.lean

  **`AcceptsJ8ZW` restated over `AcceptsJ8G.AcceptsJ8ZG`** (the J chip present
  or absent).  The proofs read no J-chip conjunct; text verbatim
  otherwise.  New module, additive.  The original header follows.
-/
/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8ZW.lean

  **`rdWC` at `AcceptsJ8Z`.**  New module, additive.  Verbatim twins
  (hypothesis `AcceptsJ8Z`; the proofs read `hsatX` only) of `LinkJ8Q1.rdWC_realize40 / linkJ8_L2`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZWG

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

noncomputable section

section Read
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {r : RowsJ8}

variable [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]


/-- **`LinkJ8.rdWC` (L2)** at `L := realize40 L0 (layPb Pb …) hL`: on a trace whose compute chip is accepted
(`AcceptsJ8.hsatX`), over `17 < p`, the compute rows `cRowsJ8` (coin-free environments, `stOfEnv`) are
`rowsWX` of the `frameJ8` environments `envX` and their one-hot states `stX`, and `cH = n`. -/
theorem rdWC_realize40Z (Pb : PubJ8 p) (skel : List Noun) (hs : skel.length ≤ 3)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hL : LayLe (layPb Pb skel hs) r) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8ZG δ b Pb Rg c χ M tr) (hp : 17 < p) :
    (realize40 δ b L0 (layPb Pb skel hs) hL).cRows tr =
        rowsWX (fun i => envX δ b Pb c χ M tr i) (fun i => stX (envX δ b Pb c χ M tr i)) ∧
      (realize40 δ b L0 (layPb Pb skel hs) hL).cH tr = Pb.n := by
  refine ⟨?_, rfl⟩
  show cRowsJ8 Pb.hn Pb.nodes Pb.orbit tr = _
  funext i
  show rowW (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C (i - 1)) (stOfEnv (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C (i - 1))) =
    rowW (envX δ b Pb c χ M tr (i - 1)) (stX (envX δ b Pb c χ M tr (i - 1)))
  generalize i - 1 = k
  have htr : (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C k).trace = (envX δ b Pb c χ M tr k).trace := by
    simp only [envCJ8, envX, TeleC.envsN]
    split_ifs <;> rfl
  have hB : BaseHoldsX (envX δ b Pb c χ M tr k) := by
    simp only [envX, TeleC.envsN]
    split_ifs
    · exact baseX_of_sat Pb.hn Pb.nodes b δ _ _ Pb.orbit _ hacc.hsatX _ (mem_rowNodeSet _ _)
    · exact baseX_of_sat Pb.hn Pb.nodes b δ _ _ Pb.orbit _ hacc.hsatX _ (mem_rowNodeSet _ _)
  have hc : nStates < ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n]; exact hp
  have hoh := stX_spec hB hc
  have hoh' : OneHotAt (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C k) (stIdx (stX (envX δ b Pb c χ M tr k))) :=
    fun j hj => by rw [congrFun htr j]; exact hoh j hj
  rw [stOfEnv_of_oneHot hoh', rowW_congr (fun j _ => congrFun htr j)]

/-- **L2 of `LinkJ8`, both fields**, at `L := realize40 L0 (layPb Pb …) hL`. -/
theorem linkJ8_L2Z (Pb : PubJ8 p) (skel : List Noun) (hs : skel.length ≤ 3)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hL : LayLe (layPb Pb skel hs) r) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8ZG δ b Pb Rg c χ M tr) (hp : 17 < p) :
    ((realize40 δ b L0 (layPb Pb skel hs) hL).cRows tr =
        rowsWX (fun i => envX δ b Pb c χ M tr i) (fun i => stX (envX δ b Pb c χ M tr i)) ∧
      (realize40 δ b L0 (layPb Pb skel hs) hL).cH tr = Pb.n) ∧
    (realize40 δ b L0 (layPb Pb skel hs) hL).wdW tr (toVSQ χ) =
      walkDataOf δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW))) :=
  ⟨rdWC_realize40Z δ b Pb skel hs L0 hL c χ M tr hacc hp, rdWW_realize40 δ b Pb skel hs L0 hL χ M tr⟩

end Read

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZWG
