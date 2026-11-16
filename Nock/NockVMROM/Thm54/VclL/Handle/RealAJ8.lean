/-
  Nock/NockVMROM/Thm54/VclL/Handle/RealAJ8.lean

  **The atom table's validity (#3) and export (#4) readouts read off the
  trace.**

  * #3 **`avReqsJ8` / `avProvsJ8`**: the atom table's validity internal consumers / providers (`cVInt` / `cVRec` of
    the restriction `129 → 205` of the atom trace, coins and publics `0`: the validity keys read no coin), read set
    `coinsBelow frameJ8 1` (`avJ8_reads`: round-`≤ 1` columns only); **`rdAV_view`**: at ANY atom vector and
    publics they ARE R3b's `cellVInternal` / `liftWts cellVRecords` of `restrictAtomCell` of the chip view.
  * #4 **`axReqsJ8` / `axProvsJ8`**: the atom table's consumed old-node keys (`atomCReqs`) with the atom walk's
    handle reads (`walkXReqs`), and the atom table's export providers (`atomProvs`), lifted; round-0 columns only,
    no coin (`atomCReqs_congr`, `atomProvs_congr`); read set `yDep` (`axJ8_reads`, along `StJ8`);
    **`rdAX_view`** at any vector / publics.
  * **`realA R`**: `R` with #3 and #4 read off the trace; the lengths `≤ 2 nA`, `nA`, `nA + nV`, `nA`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.RealAJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crA crW staged_eq below_of_mem shV)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (shA shA_round)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8 (Agree0 agree0_of_staged)
open Nock.NockVMROM.Thm54.VclL.Handle.IOVS (rdOK)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)

noncomputable section

/-! ## 1. Congruences of the #4 lists (round-0 columns `< 205`, no coin, no public) -/

section Cong
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (b : Basis (Fin 3) (ZMod p) K)
  {h h' n w w' : ℕ} (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
  (orbit' : StrictOrbitDomain (ZMod p) 3 h') (chals pubs chals' pubs' : ℕ → K)
  (Q : Fin w → (ZMod p)[X]) (Q' : Fin w' → (ZMod p)[X])

theorem oldKey_read : ∀ g ∈ (AtomChipHQ.oldKey : List (CoeffExpr (ZMod p))), rdOK 205 g = true := by
  simp [AtomChipHQ.oldKey, rdOK, Chips.ChipRAP.cv]; decide

theorem keyH_read : ∀ g ∈ (CellH.keyH : List (CoeffExpr (ZMod p))), rdOK 205 g = true := by
  simp [CellH.keyH, CellH.valE, Chips.ChipRAP.notE, rdOK, Chips.ChipRAP.cv]; decide

theorem atomCReqs_congr (hB : 205 ≤ w) (hB' : 205 ≤ w')
    (hQ : ∀ (c : ℕ) (h1 : c < w) (h2 : c < w'), c < 205 → Q ⟨c, h1⟩ = Q' ⟨c, h2⟩) :
    AtomServedQ.atomCReqs b nodes orbit chals pubs Q = AtomServedQ.atomCReqs b nodes orbit' chals' pubs' Q' := by
  unfold AtomServedQ.atomCReqs
  refine congrArg List.flatten (List.map_congr_left fun i _ => ?_)
  have he := DescentVSQ.envOfTrace_congrW 205 Q Q' hB hB' hQ orbit.ω orbit'.ω (nodes i)
    (Chips.ChipRAP.slotVal b 205 chals) (Chips.ChipRAP.slotVal b 205 pubs) (Chips.ChipRAP.slotVal b 205 chals')
    (Chips.ChipRAP.slotVal b 205 pubs')
  rw [IOVS.keyVec5_congr 205 _ oldKey_read _ _ he, he AtomChipHQ.inc (by decide)]

theorem atomProvs_congr (hB : 205 ≤ w) (hB' : 205 ≤ w')
    (hQ : ∀ (c : ℕ) (h1 : c < w) (h2 : c < w'), c < 205 → Q ⟨c, h1⟩ = Q' ⟨c, h2⟩) :
    AtomServedQ.atomProvs b nodes orbit chals pubs Q = AtomServedQ.atomProvs b nodes orbit' chals' pubs' Q' := by
  unfold AtomServedQ.atomProvs
  refine List.map_congr_left fun i _ => ?_
  have he := DescentVSQ.envOfTrace_congrW 205 Q Q' hB hB' hQ orbit.ω orbit'.ω (nodes i)
    (Chips.ChipRAP.slotVal b 205 chals) (Chips.ChipRAP.slotVal b 205 pubs) (Chips.ChipRAP.slotVal b 205 chals')
    (Chips.ChipRAP.slotVal b 205 pubs')
  rw [IOVS.keyVec5_congr 205 _ keyH_read _ _ he, he CellH.mh (by decide)]

end Cong

/-! ## 2. The readouts -/

section Real
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **#3's requests on a J-8 trace**: the atom table's validity internal consumers (coins and publics `0`). -/
def avReqsJ8 (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) : List (Fin 5 → 𝕂′) :=
  cVInt δ b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) (restrictQ 129 205 shA tr.A)

/-- **#3's providers on a J-8 trace**: the atom table's validity providers, weights lifted. -/
def avProvsJ8 (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) : List ((Fin 5 → 𝕂′) × 𝕂′) :=
  liftWts (cVRec δ b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) (restrictQ 129 205 shA tr.A))

theorem avJ8_reads (Pb : PubJ8 p) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q) :
    ReadsOnC frameJ8 (coinsBelow frameJ8 1) fun χ => (avReqsJ8 δ b Pb (Q χ), avProvsJ8 δ b Pb (Q χ)) := by
  intro χ χ' hχ
  refine Prod.ext ?_ ?_
  · refine cVInt_congr δ b Pb.nodesA Pb.orbitA _ _ _ _ _ _ (by norm_num) (by norm_num) fun j hj => ?_
    exact staged_eq hQ.2.2.2.2.1 (below_of_mem hχ) _ (shA_round j hj)
  · show liftWts _ = liftWts _
    congr 1
    refine cVRec_congr δ b Pb.nodesA Pb.orbitA _ _ _ _ _ _ (by norm_num) (by norm_num) fun j hj => ?_
    exact staged_eq hQ.2.2.2.2.1 (below_of_mem hχ) _ (shA_round j hj)

/-- **#3 at the chip view**: at any atom vector and publics, the readout IS R3b's `rdAV` pair. -/
theorem rdAV_view (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K) :
    avReqsJ8 δ b Pb tr = cellVInternal δ b Pb.hnA Pb.nodesA Pb.orbitA chals pubs
        (AtomChipHQ.restrictAtomCell δ b Pb.hnA Pb.nodesA Pb.orbitA chals pubs (qA δ b Pb tr chals pubs)) ∧
      avProvsJ8 δ b Pb tr = liftWts (cellVRecords δ b Pb.hnA Pb.nodesA Pb.orbitA chals pubs
        (AtomChipHQ.restrictAtomCell δ b Pb.hnA Pb.nodesA Pb.orbitA chals pubs (qA δ b Pb tr chals pubs))) := by
  have hw : 183 ≤ (cellChip δ b Pb.hnA Pb.nodesA Pb.orbitA chals pubs).rap.w := by rw [cell_w]; norm_num
  refine ⟨?_, ?_⟩
  · rw [cVInt_chip]
    exact cVInt_congr δ b Pb.nodesA Pb.orbitA _ _ _ _ _ _ (by norm_num) hw fun j hj => congrArg tr.A (Fin.ext rfl)
  · rw [cVRec_chip]
    exact congrArg liftWts
      (cVRec_congr δ b Pb.nodesA Pb.orbitA _ _ _ _ _ _ (by norm_num) hw fun j hj => congrArg tr.A (Fin.ext rfl))

theorem avReqsJ8_length (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) : (avReqsJ8 δ b Pb tr).length ≤ 2 * Pb.nA :=
  cVInt_length δ b _ _ _ _ _

theorem avProvsJ8_length (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) : (avProvsJ8 δ b Pb tr).length = Pb.nA := by
  rw [avProvsJ8, liftWts_length]; exact cVRec_length δ b _ _ _ _ _

/-- **#4's requests on a J-8 trace**: the atom table's consumed old-node keys and the atom walk's handle reads,
lifted (round-0 columns, no coin, no public). -/
def axReqsJ8 (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) : List (Fin 5 → 𝕂′) :=
  (AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A ++
    ServeH.walkXReqs b Pb.nodesV Pb.orbitV (fun _ => (0 : K)) (fun _ => 0) tr.V).map (liftRec (K := K) (L := 𝕂′))

/-- **#4's providers on a J-8 trace**: the atom table's export providers, lifted. -/
def axProvsJ8 (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) : List ((Fin 5 → 𝕂′) × 𝕂′) :=
  AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A)

theorem ax_congr (Pb : PubJ8 p) {tr tr' : TrJ8 (ZMod p)} (h : Agree0 tr tr') :
    axReqsJ8 δ b Pb tr = axReqsJ8 δ b Pb tr' ∧ axProvsJ8 δ b Pb tr = axProvsJ8 δ b Pb tr' := by
  have hA : ∀ (c : ℕ) (h1 : c < 349) (h2 : c < 349), c < 205 → tr.A ⟨c, h1⟩ = tr'.A ⟨c, h2⟩ :=
    fun c h1 h2 hc => h.A ⟨c, h1⟩ (by simp only [crA]; split_ifs <;> omega)
  have hV : ∀ (c : ℕ) (h1 : c < 166) (h2 : c < 166), c < 25 → tr.V ⟨c, h1⟩ = tr'.V ⟨c, h2⟩ :=
    fun c h1 h2 hc => h.V ⟨c, h1⟩ (by simp only [crW]; split_ifs <;> omega)
  refine ⟨?_, ?_⟩
  · unfold axReqsJ8
    rw [atomCReqs_congr b Pb.nodesA Pb.orbitA Pb.orbitA _ _ _ _ tr.A tr'.A (by norm_num) (by norm_num) hA,
      (DescentVSQ.walkLists_congrW b Pb.nodesV Pb.orbitV Pb.orbitV _ _ (fun _ => (0 : K)) (fun _ => 0) tr.V tr'.V
        (by norm_num) (by norm_num) hV).1]
  · unfold axProvsJ8
    rw [atomProvs_congr b Pb.nodesA Pb.orbitA Pb.orbitA _ _ _ _ tr.A tr'.A (by norm_num) (by norm_num) hA]

theorem axJ8_reads (Pb : PubJ8 p) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q) :
    ReadsOnC frameJ8 yDep fun χ => (axReqsJ8 δ b Pb (Q χ), axProvsJ8 δ b Pb (Q χ)) := by
  intro χ χ' _
  have h := ax_congr δ b Pb (agree0_of_staged hQ χ χ')
  show (_, _) = (_, _)
  rw [h.1, h.2]

/-- **#4 at the chip view**: at any atom vector / publics, the readout is `houtA`'s pair of lists. -/
theorem rdAX_view (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (chalsA pubsA chalsV pubsV : ℕ → K) :
    axReqsJ8 δ b Pb tr = (AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA chalsA pubsA (qA δ b Pb tr chalsA pubsA) ++
      ServeH.walkXReqs b Pb.nodesV Pb.orbitV chalsV pubsV (qV δ b Pb tr chalsV pubsV)).map
        (liftRec (K := K) (L := 𝕂′)) ∧
    axProvsJ8 δ b Pb tr = AtomServedQ.liftProvs δ
      (AtomServedQ.atomProvs b Pb.nodesA Pb.orbitA chalsA pubsA (qA δ b Pb tr chalsA pubsA)) := by
  refine ⟨?_, ?_⟩
  · unfold axReqsJ8
    rw [atomCReqs_congr b Pb.nodesA Pb.orbitA Pb.orbitA _ _ chalsA pubsA tr.A (qA δ b Pb tr chalsA pubsA)
      (by norm_num) (by rw [AtomChipHQ.atomChipHQ_width]; norm_num) (fun c h1 h2 _ => rfl),
      (DescentVSQ.walkLists_congrW b Pb.nodesV Pb.orbitV Pb.orbitV _ _ chalsV pubsV tr.V (qV δ b Pb tr chalsV pubsV)
        (by norm_num) (by rw [CellTwinK.walkChipHQK_width]; norm_num) (fun c h1 h2 _ => rfl)).1]
  · unfold axProvsJ8
    rw [atomProvs_congr b Pb.nodesA Pb.orbitA Pb.orbitA _ _ chalsA pubsA tr.A (qA δ b Pb tr chalsA pubsA)
      (by norm_num) (by rw [AtomChipHQ.atomChipHQ_width]; norm_num) (fun c h1 h2 _ => rfl)]

theorem axReqsJ8_length (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) : (axReqsJ8 δ b Pb tr).length ≤ Pb.nA + Pb.nV := by
  unfold axReqsJ8
  rw [List.length_map, List.length_append, RealIOJ8.walkXReqs_length]
  have : (AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A).length ≤ Pb.nA := by
    unfold AtomServedQ.atomCReqs
    refine (AcceptsJ8P.length_flatMap_le _ _ 1 fun i => ?_).trans (by simp)
    split_ifs <;> simp
  omega

theorem axProvsJ8_length (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) : (axProvsJ8 δ b Pb tr).length = Pb.nA := by
  simp [axProvsJ8, AtomServedQ.atomProvs]

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))] {r : RowsJ8} {P g : ℕ}

/-- **`R` with the atom validity (#3) and atom export (#4) lists read off the trace.** -/
def realA (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (Pb : PubJ8 p) : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g :=
  { R with
    D := { R.D with
      avReqs := fun tr _ => avReqsJ8 δ b Pb tr
      avProvs := fun tr _ => avProvsJ8 δ b Pb tr
      av_reads := fun Q hQ => avJ8_reads δ b Pb Q hQ
      axReqs := fun tr _ => axReqsJ8 δ b Pb tr
      axProvs := fun tr _ => axProvsJ8 δ b Pb tr
      ax_reads := fun Q hQ => axJ8_reads δ b Pb Q hQ } }

end Real

end

end Nock.NockVMROM.Thm54.VclL.Handle.RealAJ8
