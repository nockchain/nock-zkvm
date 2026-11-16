/-
  Nock/NockVMROM/Thm54/VclL/Handle/AbsentVJ8.lean

  * §1 **`provsJ8A`**: `AcceptsJ8.provsJ8` with the `s` providers `jProv ++ pad8 atomIncProvs` (no atom-walk
    record; `.x` / `.p` are `provsJ8`'s, by `rfl`); its coin-free form `provsTA` (`provsJ8A_s_eq`), staged
    (`provsTA_congr`).  **`axReqsJ8A`**: #4's requests = the atom table's consumed old-node keys only.
  * §2 **`RR4A`**: `LinkJ8R4.RR4` with exactly two lists replaced — #6 `svProvs := effP (liftP provsTA)` and #4
    `axReqs := axReqsJ8A` (requests `svReqs` / providers `axProvs` and every other readout, budget and read set are
    `RR4`'s).  The read sets are proved (`sv_reads` `∅`, `ax_reads` `yDep`), so the events are priced by the same
    generic summands at the same budgets.  `rdS_A`, `rdAX_A`: the readouts at an accepted trace.
  * §3 **`toMsgJ8ZA`** (`toMsgJ8Z` with `wreqs := []`), **`AcceptsJ8ZA`** (`AcceptsJ8G.AcceptsJ8ZG` without the seven
    atom-walk conjuncts, plus `hV0`), **`acceptsJ8ZA_of_V`**: `AcceptsJ8V` at `krootsV = 0` gives `AcceptsJ8ZA` at
    `toMsgJ8ZA` (the export balance `hbalA` with no walk term from `hbalA'` and `pubsV pubXQ = 0`).
  * §4 the budget twins `budX_ofZA` / `budP_ofZA` / `budS_ofZA` (at `provsJ8A`) / `hcount_ofZA`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8

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
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (xS xF xE)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (envCJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP (toMsgJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 St40 sum40 fpx_out v4 v5 v6 v7)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (extY_below shV_round)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (crJ)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (compReqsX)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (yDep)

noncomputable section

/-! ## 1. The V-free lists -/

section Lists
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The handle-balance providers with the atom walk ABSENT**: `provsJ8` with the `s` providers the J chip's and
the atom table's inc heads only. -/
def provsJ8A (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    (bl : Bal) → List ((Fin (mOf bl) → K) × K) :=
  byBal (β := fun bl => List ((Fin (mOf bl) → K) × K))
    (provsJ8 δ b Pb χ M tr .x) (provsJ8 δ b Pb χ M tr .p)
    (jProv b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ) ++
      pad8 (atomIncProvs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)))

/-- The `s` providers with the atom walk absent, coin-free. -/
def provsTA (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) : List ((Fin (mOf .s) → K) × K) :=
  jProv b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay tr.J ++
    pad8 (atomIncProvs b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A)

/-- **`provsJ8A.s` is coin-free**: at every coin and message it is `provsTA`. -/
theorem provsJ8A_s_eq (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    provsJ8A δ b Pb χ M tr .s = provsTA b Pb tr := by
  show _ ++ pad8 _ = _ ++ pad8 _
  rw [(ReadIOJ8.jLists_congr b Pb.nodesJ Pb.orbitJ Pb.orbitJ _ _ (fun _ => (0 : K)) (fun _ => 0)
      (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ) tr.J Pb.lay (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega) (by norm_num) (fun _ _ _ _ => rfl)).2.2,
    ReadIOJ8.atomIncProvs_congr b Pb.nodesA Pb.orbitA Pb.orbitA _ _ (fun _ => (0 : K)) (fun _ => 0)
      (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) tr.A (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega) (by norm_num) (fun _ _ _ _ => rfl)]

/-- **#4's requests with the atom walk ABSENT**: the atom table's consumed old-node keys only, lifted. -/
def axReqsJ8A (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) : List (Fin 5 → 𝕂′) :=
  (AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A).map (liftRec (K := K) (L := 𝕂′))

/-- **#4 (absent) at the chip view.** -/
theorem rdAXA_view (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (chalsA pubsA : ℕ → K) :
    axReqsJ8A δ b Pb tr = (AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA chalsA pubsA
      (qA δ b Pb tr chalsA pubsA)).map (liftRec (K := K) (L := 𝕂′)) := by
  unfold axReqsJ8A
  rw [RealAJ8.atomCReqs_congr b Pb.nodesA Pb.orbitA Pb.orbitA _ _ chalsA pubsA tr.A (qA δ b Pb tr chalsA pubsA)
    (by norm_num) (by rw [AtomChipHQ.atomChipHQ_width]; norm_num) (fun c h1 h2 _ => rfl)]

theorem axReqsJ8A_length (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) : (axReqsJ8A δ b Pb tr).length ≤ Pb.nA := by
  unfold axReqsJ8A
  rw [List.length_map]
  unfold AtomServedQ.atomCReqs
  refine (AcceptsJ8P.length_flatMap_le _ _ 1 fun i => ?_).trans (by simp)
  split_ifs <;> simp

end Lists

/-! ### Staging -/

section Stage
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem provsTA_congr {tr tr' : TrJ8 (ZMod p)} (h : Agree0 tr tr') (Pb : PubJ8 p) :
    provsTA b Pb tr = provsTA b Pb tr' := by
  have hJ := ReadIOJ8.jLists_congr b Pb.nodesJ Pb.orbitJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0)
    (fun _ => (0 : K)) (fun _ => 0) tr.J tr'.J Pb.lay (by norm_num) (by norm_num)
    (fun c h1 h2 hc => h.J ⟨c, h1⟩ (by simp [crJ, hc]))
  unfold provsTA
  rw [hJ.2.2, ReadIOJ8.atomIncProvs_congr b Pb.nodesA Pb.orbitA Pb.orbitA _ _ (fun _ => (0 : K))
    (fun _ => 0) tr.A tr'.A (by norm_num) (by norm_num) (fun c h1 h2 hc => h.A ⟨c, h1⟩ (by simp [crA, hc]))]

theorem axA_congr (Pb : PubJ8 p) {tr tr' : TrJ8 (ZMod p)} (h : Agree0 tr tr') :
    axReqsJ8A δ b Pb tr = axReqsJ8A δ b Pb tr' := by
  have hA : ∀ (c : ℕ) (h1 : c < 349) (h2 : c < 349), c < 205 → tr.A ⟨c, h1⟩ = tr'.A ⟨c, h2⟩ :=
    fun c h1 h2 hc => h.A ⟨c, h1⟩ (by simp only [crA]; split_ifs <;> omega)
  unfold axReqsJ8A
  rw [RealAJ8.atomCReqs_congr b Pb.nodesA Pb.orbitA Pb.orbitA _ _ _ _ tr.A tr'.A (by norm_num) (by norm_num) hA]

theorem axJ8A_reads (Pb : PubJ8 p) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q) :
    ReadsOnC frameJ8 yDep fun χ => (axReqsJ8A δ b Pb (Q χ), RealAJ8.axProvsJ8 δ b Pb (Q χ)) := by
  intro χ χ' _
  have h := agree0_of_staged hQ χ χ'
  show (_, _) = (_, _)
  rw [axA_congr δ b Pb h, (RealAJ8.ax_congr δ b Pb h).2]

end Stage

/-! ## 2. The V-free real data `RR4A` -/

section Real
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`RR4A`**: `LinkJ8R4.RR4` with the #6 providers `svProvs := effP (liftP provsTA)` and the #4
requests `axReqs := axReqsJ8A`.  Every other
field, budget and read set is `RR4`'s. -/
def RR4A (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (Pb : PubJ8 p) (c : P8PublicClaim) (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31) :
    DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g :=
  { RR4 δ b (g := g) R0 Pb c skel hs hL hP hnM hreg with
    D := { (RR4 δ b (g := g) R0 Pb c skel hs hL hP hnM hreg).D with
      svReqs := fun tr _ => reqsT δ b Pb tr .s
      svProvs := fun tr _ => effP (liftP (provsTA b Pb tr))
      sv_reads := fun Q hQ χ χ' _ => by
        have h := agree0_of_staged hQ χ χ'
        simp only [reqsT_congr δ b h Pb, provsTA_congr b h Pb]
      axReqs := fun tr _ => axReqsJ8A δ b Pb tr
      axProvs := fun tr _ => RealAJ8.axProvsJ8 δ b Pb tr
      ax_reads := fun Q hQ => axJ8A_reads δ b Pb Q hQ } }

/-- **#6 at `RR4A`**: the requests are `reqsOf.s`, the providers the effective `provsJ8A.s`. -/
theorem rdS_A (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (Pb : PubJ8 p) (c : P8PublicClaim) (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    (RR4A δ b (g := g) R0 Pb c skel hs hL hP hnM hreg).D.svReqs tr χ = reqsOf δ b Pb c χ M tr .s ∧
      (RR4A δ b (g := g) R0 Pb c skel hs hL hP hnM hreg).D.svProvs tr χ =
        effP (liftP (provsJ8A δ b Pb χ M tr .s)) :=
  ⟨(reqsOf_eq δ b Pb c χ M tr .s).symm, by rw [provsJ8A_s_eq]; rfl⟩

/-- **#4 at `RR4A`**, at any atom vector / publics. -/
theorem rdAX_A (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (Pb : PubJ8 p) (c : P8PublicClaim) (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    (χ : Coins frameJ8 K) (tr : TrJ8 (ZMod p)) (chalsA pubsA : ℕ → K) :
    (RR4A δ b (g := g) R0 Pb c skel hs hL hP hnM hreg).D.axReqs tr χ =
      (AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA chalsA pubsA (qA δ b Pb tr chalsA pubsA)).map
        (liftRec (K := K) (L := 𝕂′)) ∧
    (RR4A δ b (g := g) R0 Pb c skel hs hL hP hnM hreg).D.axProvs tr χ = AtomServedQ.liftProvs δ
      (AtomServedQ.atomProvs b Pb.nodesA Pb.orbitA chalsA pubsA (qA δ b Pb tr chalsA pubsA)) :=
  ⟨rdAXA_view δ b Pb tr chalsA pubsA, (RealAJ8.rdAX_view δ b Pb tr chalsA pubsA chalsA pubsA).2⟩

end Real

/-! ## 3. The absent message and predicate -/

section Accept
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`toMsgJ8ZA`**: `toMsgJ8Z` with no atom-walk handle read (`wreqs := []`). -/
def toMsgJ8ZA (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) :
    MsgJ8 p K δ :=
  { toMsgJ8Z δ b Pb c χ M tr with wreqs := [] }

/-- **`AcceptsJ8ZA`**: `AcceptsJ8G.AcceptsJ8ZG` with the seven atom-walk conjuncts removed and the atom walk's two
`s` publics `0` (`hV0`).  Every other field verbatim. -/
structure AcceptsJ8ZA (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) : Prop where
  -- compute
  hsatX : RAP.SatisfiesWithPreprocessing (computeChipVCLHX Pb.hn Pb.nodes b δ (chalVJ8 b χ)
    (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit) (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ))
  hinjX : Function.Injective Pb.nodes
  hadjX : ∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω
  -- the cell table
  hsatC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.Satisfies
    (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)
  hbindC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).BindsPreprocessing
    (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)
  hinjC : Function.Injective Pb.nodesC
  hadjC : ∀ (i : Fin Pb.nC) (hi : (i : ℕ) + 1 < Pb.nC), Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesC i * Pb.orbitC.ω
  hnpC : Pb.nC < ringChar (ZMod p)
  -- the J-8 walk
  hsatW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).rap.Satisfies
    (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)
  hbindW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).BindsPreprocessing
    (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)
  hinjW : Function.Injective Pb.nodesW
  hadjW : ∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW), Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω
  hkW : 1 ≤ Pb.kroots
  hknW : Pb.kroots ≤ Pb.nW
  hkpW : Pb.kroots + Pb.nW < ringChar (ZMod p)
  hJk : JGenJ8.JChipOK δ b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)
  -- the atom table
  hsatA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
    (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  hbindA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
    (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  hinjA : Function.Injective Pb.nodesA
  hadjA : ∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω
  hnpA : Pb.nA < p
  -- the public balance equations
  hGx : M.ρ 3 + (Quad.mk _ (M.pubsW WalkHQ.pubXQ) (M.pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (M.pubsJ 2) (M.pubsJ 3)) =
    Quad.mk _ (M.pubsC CellHQ.pubHQ) (M.pubsC (CellHQ.pubHQ + 1))
  hGp : M.ρ 4 = Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1))
  hGS : M.ρS + ((pinCons (p := p) (K := K) Pb.regs Pb.idx).map fun r =>
      (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (M.pubsJ 0) (M.pubsJ 1) =
    Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1))
  hsumC : (M.reqsC.map fun r => (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
    Quad.mk _ (M.pubsC 0) (M.pubsC 1) + (M.xsC.map fun x => x.2 * (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x.1)⁻¹).sum
  hxneC : ∀ x ∈ M.xsC, FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x.1 ≠ 0
  hbalA : Quad.mk _ (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
    Quad.mk _ (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
      ((M.wreqs.map (liftRec (K := K) (L := 𝕂′))).map fun r =>
        (compress (AtomServedQ.acoins δ (chalsAJ8Z δ χ)) r)⁻¹).sum
  -- the cell validity's external keys
  hxC : ∀ x ∈ M.xsC, ∃ k ∈ M.vp, x.1 = ClaimVS.claimVec δ k.1 (k.2.2.2 : ZMod p) (k.2.1 : ZMod p) (k.2.2.1 : ZMod p)
  hvp0 : ∀ k ∈ M.vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar (ZMod p)
  -- the J chip's public checks and the registry pin
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
  hpinC : ∀ id ∈ Pb.regs, ClaimVS.claimVec δ
    (encZY (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))
      (Nock.Jet.Autogen.compile p (Pb.Rt id))) (Pb.idx id : ZMod p)
    ((Pb.rk id).1 : ZMod p) ((Pb.rk id).2 : ZMod p) ∈ M.reqsC
  -- the atom walk ABSENT: its two `s` publics are `0`
  hV0 : M.pubsV WalkHQ.pubPQ = 0 ∧ M.pubsV (WalkHQ.pubPQ + 1) = 0

variable {δ b}

/-- **`AcceptsJ8V` at `krootsV = 0` ⇒ `AcceptsJ8ZA` at `toMsgJ8ZA`.** -/
theorem acceptsJ8ZA_of_V {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsJ8V.AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (h0 : Pb.krootsV = 0) : AcceptsJ8ZA δ b Pb Rg c χ (toMsgJ8ZA δ b Pb c χ M tr) tr :=
  have hz := (AcceptsJ8V.aw_absent_iff δ b h0).1 h.hVk
  { hsatX := h.hsatX
    hinjX := h.hinjX
    hadjX := h.hadjX
    hsatC := h.hsatC
    hbindC := h.hbindC
    hinjC := h.hinjC
    hadjC := h.hadjC
    hnpC := h.hnpC
    hsatW := h.hsatW
    hbindW := h.hbindW
    hinjW := h.hinjW
    hadjW := h.hadjW
    hkW := h.hkW
    hknW := h.hknW
    hkpW := h.hkpW
    hJk := h.hJk
    hsatA := h.hsatA
    hbindA := h.hbindA
    hinjA := h.hinjA
    hadjA := h.hadjA
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
    hsumC := by
      show _ = _ + ((mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _).map _).sum
      rw [mbXs_sum δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ h.hsatA h.hbindA h.hinjA h.hadjA _ _
        (chalsAJ8Z_ok δ χ)]
      exact h.hsumC'
    hxneC := mbXs_den δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ h.hsatA _ _ (chalsAJ8Z_ok δ χ)
    hbalA := by
      show Quad.mk _ (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
        Quad.mk _ (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
          (((([] : List (Fin 5 → K))).map (liftRec (K := K) (L := 𝕂′))).map fun r =>
            (compress (AtomServedQ.acoins δ (chalsAJ8Z δ χ)) r)⁻¹).sum
      have hb := h.hbalA'
      rw [hz.2.2.1, hz.2.2.2.1, Quad.mk_zero', add_zero] at hb
      simpa using hb
    hxC := mbXs_claimVec δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _
    hvp0 := fun k hk => by
      obtain ⟨h1, h2, h3⟩ := mbVp_small δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ k hk
      exact ⟨h1, h2, by rw [ZMod.ringChar_zmod_n]; exact h3⟩
    hpinC := fun id hid => List.mem_append_right _ (List.mem_map.mpr ⟨id, hid, rfl⟩)
    hV0 := ⟨hz.2.2.2.2.1, hz.2.2.2.2.2⟩ }

end Accept

/-! ## 4. The budget twins at `AcceptsJ8ZA` -/

section Budgets
open Nock.Jet.ChipJ8 (entsX ents0T ents1T ents2T ents3)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

variable {Rg : Nock.Jet.Registry} {r : RowsJ8} {g : ℕ}

theorem compLenZA (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8ZA δ b Pb Rg c χ M tr) (hp : 17 < p) (bl : Bal) :
    (compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
        (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) bl).length ≤ ReadIOJ8.capB bl * Pb.n :=
  ReadIOJ8.compReqsX_length_le hacc.hsatX (by rw [ZMod.ringChar_zmod_n]; exact hp) bl

theorem budX_ofZA (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8ZA δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g) :
    (reqsOf δ b Pb c χ M tr .x).length ≤ 3 * r.N + r.W + r.rd ∧
      (liftP (δ := δ) (provsJ8 δ b Pb χ M tr .x)).length ≤ r.D := by
  refine ⟨?_, ?_⟩
  · rw [reqsOf_length]
    have h1 := compLenZA δ b Pb c χ M tr hacc hp .x
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

theorem budP_ofZA (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8ZA δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g) :
    (reqsOf δ b Pb c χ M tr .p).length ≤ 2 * r.N ∧
      (liftP (δ := δ) (provsJ8 δ b Pb χ M tr .p)).length ≤ 2 * r.W := by
  refine ⟨?_, ?_⟩
  · rw [reqsOf_length]
    have h1 := compLenZA δ b Pb c χ M tr hacc hp .p
    have h2 : (extJ8 δ b Pb c χ M tr .p).length = 0 := rfl
    simp only [ReadIOJ8.capB] at h1
    have := hB.p1
    omega
  · simp only [liftP, List.length_map]
    show (ServeH.walkPProvs b Pb.nodesW Pb.orbitW _ _ _).length ≤ 2 * r.W
    rw [walkPProvs_length]; have := hB.p2; omega

/-- **`budS`** at `RR4A` (no atom-walk provider). -/
theorem budS_ofZA (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8ZA δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g) :
    (reqsOf δ b Pb c χ M tr .s).length ≤ r.N + 2 * r.J + g ∧
      (effP (liftP (δ := δ) (provsJ8A δ b Pb χ M tr .s))).length ≤ r.calls + r.heads + r.blocks + r.J := by
  refine ⟨?_, ?_⟩
  · rw [reqsOf_length]
    have h1 := compLenZA δ b Pb c χ M tr hacc hp .s
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

theorem hcount_ofZA (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8ZA δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g)
    (hcap : 3 * r.N + r.W + r.rd < p ∧ 2 * r.N < p ∧ r.N + 2 * r.J + g < p) :
    ∀ bl, (reqsOf δ b Pb c χ M tr bl).length < p := by
  intro bl
  cases bl
  · exact lt_of_le_of_lt (budX_ofZA δ b Pb c χ M tr hacc hp hB).1 hcap.1
  · exact lt_of_le_of_lt (budP_ofZA δ b Pb c χ M tr hacc hp hB).1 hcap.2.1
  · exact lt_of_le_of_lt (budS_ofZA δ b Pb c χ M tr hacc hp hB).1 hcap.2.2

end Budgets

end

end Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8
