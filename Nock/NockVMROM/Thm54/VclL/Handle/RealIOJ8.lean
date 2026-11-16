/-
  Nock/NockVMROM/Thm54/VclL/Handle/RealIOJ8.lean

  **The handle-balance IO lists of `R` / `L` read off the trace.**

  * §1 the coin-free lists of a J-8 trace: `reqsT Pb tr bl` (the compute requests of balance `bl` with the
    externals) and `provsT Pb tr bl` (the providers), at coins and publics `0`; **`reqsOf_eq` / `provsJ8_eq`**: at
    EVERY coin `χ` and message `M` they ARE `LinkJ8`'s `reqsOf δ b Pb c χ M tr bl` / `provsJ8 δ b Pb χ M tr bl`
    (`ReadIOJ8`: no list reads a coin or a public).
  * §3 **`realIO R Pb`** (the `DataJ8C` with `cx` / `sv` read off the trace) and **`real40 L Pb`** (the `Data40J8`
    with `p` read off the trace), with their `dep = ∅` read sets proved.
  * §4 **`rdX` / `rdS` / `rdP` of `LinkJ8X'`** at `realIO` / `real40`: equalities at every `χ`, `M`, `tr`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ReadIOJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf compReqsX)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crC crM crW crJ crA staged_eq)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8)
open Nock.Jet.ChipJ8 (jetChipJ8)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.FibreJ8 (effP)

noncomputable section

/-! ## 1. The coin-free lists of a trace -/

section Lists
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The externals of the three handle balances, coin-free. -/
def extT (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) : (bl : Bal) → List (Fin (mOf bl) → K) :=
  byBal (β := fun bl => List (Fin (mOf bl) → K))
    (ServeH.walkXReqs b Pb.nodesW Pb.orbitW (fun _ => (0 : K)) (fun _ => 0) tr.W ++
      jRd b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay tr.J)
    []
    (pinCons (p := p) (K := K) Pb.regs Pb.idx ++
      jCons b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay tr.J)

/-- The providers of the three handle balances, coin-free. -/
def provsT (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) : (bl : Bal) → List ((Fin (mOf bl) → K) × K) :=
  byBal (β := fun bl => List ((Fin (mOf bl) → K) × K))
    (cellProvsW b Pb.nodesC Pb.orbitC (fun _ => (0 : K)) (fun _ => 0) tr.M)
    (ServeH.walkPProvs b Pb.nodesW Pb.orbitW (fun _ => (0 : K)) (fun _ => 0) tr.W)
    (jProv b Pb.nodesJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0) Pb.lay tr.J ++
      (pad8 (atomIncProvs b Pb.nodesA Pb.orbitA (fun _ => (0 : K)) (fun _ => 0) tr.A) ++
        pad8 (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (fun _ => (0 : K)) (fun _ => 0) tr.V)))

/-- **The requests of balance `bl`, coin-free**: the compute's (at coins / publics `0`) and the externals, lifted. -/
def reqsT (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (bl : Bal) : List (Fin (mOf bl) → 𝕂′) :=
  reqsJ8 (hn := Pb.hn) (nodes := Pb.nodes) (b := b) (δ := δ) (chalV := fun _ => 0) (pubVal := fun _ => 0)
    (orbit := Pb.orbit) (P := qX δ b Pb tr (fun _ => 0) (fun _ => 0)) (extT b Pb tr) bl

theorem extJ8_eq (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (bl : Bal) : extJ8 δ b Pb c χ M tr bl = extT b Pb tr bl := by
  cases bl
  · show _ ++ _ = _ ++ _
    rw [(DescentVSQ.walkLists_congrW b Pb.nodesW Pb.orbitW Pb.orbitW _ _ (fun _ => (0 : K)) (fun _ => 0)
      (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) tr.W (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega) (by norm_num) (fun _ _ _ _ => rfl)).1,
      (ReadIOJ8.jLists_congr b Pb.nodesJ Pb.orbitJ Pb.orbitJ _ _ (fun _ => (0 : K)) (fun _ => 0)
      (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ) tr.J Pb.lay (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega) (by norm_num) (fun _ _ _ _ => rfl)).1]
  · rfl
  · show _ ++ _ = _ ++ _
    rw [(ReadIOJ8.jLists_congr b Pb.nodesJ Pb.orbitJ Pb.orbitJ _ _ (fun _ => (0 : K)) (fun _ => 0)
      (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ) tr.J Pb.lay (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega) (by norm_num) (fun _ _ _ _ => rfl)).2.1]

/-- **`reqsOf` is coin-free**: at every coin and message it is the trace's `reqsT`. -/
theorem reqsOf_eq (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (bl : Bal) : reqsOf δ b Pb c χ M tr bl = reqsT δ b Pb tr bl := by
  unfold reqsOf reqsT reqsJ8
  rw [extJ8_eq δ b Pb c χ M tr bl,
    ReadIOJ8.compReqsX_congr (K := K) (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ))
      (qX δ b Pb tr (fun _ => 0) (fun _ => 0)) (fun _ _ _ _ => rfl) bl]

/-- **`provsJ8` is coin-free**: at every coin and message it is the trace's `provsT`. -/
theorem provsJ8_eq (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (bl : Bal) :
    provsJ8 δ b Pb χ M tr bl = provsT b Pb tr bl := by
  cases bl
  · exact ReadIOJ8.cellProvsW_congr b Pb.nodesC Pb.orbitC Pb.orbitC _ _ (fun _ => (0 : K)) (fun _ => 0)
      (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) tr.M (by rw [TraceJ8.widthM_eq]; omega) (by norm_num)
      (fun _ _ _ _ => rfl)
  · exact (DescentVSQ.walkLists_congrW b Pb.nodesW Pb.orbitW Pb.orbitW _ _ (fun _ => (0 : K)) (fun _ => 0)
      (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) tr.W (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega) (by norm_num)
      (fun _ _ _ _ => rfl)).2
  · show _ ++ (pad8 _ ++ pad8 _) = _ ++ (pad8 _ ++ pad8 _)
    rw [(ReadIOJ8.jLists_congr b Pb.nodesJ Pb.orbitJ Pb.orbitJ _ _ (fun _ => (0 : K)) (fun _ => 0)
        (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ) tr.J Pb.lay (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega) (by norm_num) (fun _ _ _ _ => rfl)).2.2,
      ReadIOJ8.atomIncProvs_congr b Pb.nodesA Pb.orbitA Pb.orbitA _ _ (fun _ => (0 : K)) (fun _ => 0)
        (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA) tr.A (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega) (by norm_num) (fun _ _ _ _ => rfl),
      (DescentVSQ.walkLists_congrW b Pb.nodesV Pb.orbitV Pb.orbitV _ _ (fun _ => (0 : K)) (fun _ => 0)
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV) tr.V (by simp only [TraceJ8.widthW_eq, TraceJ8.widthJ_eq, TraceJ8.widthA_eq, TraceJ8.widthV_eq, TraceJ8.widthM_eq]; omega) (by norm_num) (fun _ _ _ _ => rfl)).2]

end Lists

/-! ## 2. Staging: the lists read round-0 columns only -/

section Stage
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

/-- Two J-8 traces agreeing on every round-0 column of every chip. -/
structure Agree0 (tr tr' : TrJ8 (ZMod p)) : Prop where
  C : ∀ j : Fin 123, crC j = 0 → tr.C j = tr'.C j
  M : ∀ j : Fin 242, crM j = 0 → tr.M j = tr'.M j
  W : ∀ j : Fin 166, crW j = 0 → tr.W j = tr'.W j
  J : ∀ j : Fin 71, crJ j = 0 → tr.J j = tr'.J j
  A : ∀ j : Fin 349, crA j = 0 → tr.A j = tr'.A j
  V : ∀ j : Fin 166, crW j = 0 → tr.V j = tr'.V j

/-- Along `StJ8`, the traces at any two coins agree on round-0 columns. -/
theorem agree0_of_staged {Q : Coins frameJ8 K → TrJ8 (ZMod p)} (hQ : StJ8 Q) (χ χ' : Coins frameJ8 K) :
    Agree0 (Q χ) (Q χ') where
  C j hj := staged_eq hQ.1 (r := 0) (fun i hi => absurd hi (by omega)) j hj.le
  M j hj := staged_eq hQ.2.1 (r := 0) (fun i hi => absurd hi (by omega)) j hj.le
  W j hj := staged_eq hQ.2.2.1 (r := 0) (fun i hi => absurd hi (by omega)) j hj.le
  J j hj := staged_eq hQ.2.2.2.1 (r := 0) (fun i hi => absurd hi (by omega)) j hj.le
  A j hj := staged_eq hQ.2.2.2.2.1 (r := 0) (fun i hi => absurd hi (by omega)) j hj.le
  V j hj := staged_eq hQ.2.2.2.2.2 (r := 0) (fun i hi => absurd hi (by omega)) j hj.le

variable {tr tr' : TrJ8 (ZMod p)} (h : Agree0 tr tr')
include h

theorem extT_congr (Pb : PubJ8 p) (bl : Bal) : extT b Pb tr bl = extT b Pb tr' bl := by
  have hW := DescentVSQ.walkLists_congrW b Pb.nodesW Pb.orbitW Pb.orbitW (fun _ => (0 : K)) (fun _ => 0)
    (fun _ => (0 : K)) (fun _ => 0) tr.W tr'.W (by norm_num) (by norm_num)
    (fun c h1 h2 hc => h.W ⟨c, h1⟩ (by simp [crW, hc]))
  have hJ := ReadIOJ8.jLists_congr b Pb.nodesJ Pb.orbitJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0)
    (fun _ => (0 : K)) (fun _ => 0) tr.J tr'.J Pb.lay (by norm_num) (by norm_num)
    (fun c h1 h2 hc => h.J ⟨c, h1⟩ (by simp [crJ, hc]))
  cases bl
  · show _ ++ _ = _ ++ _; rw [hW.1, hJ.1]
  · rfl
  · show _ ++ _ = _ ++ _; rw [hJ.2.1]

theorem reqsT_congr (Pb : PubJ8 p) (bl : Bal) : reqsT δ b Pb tr bl = reqsT δ b Pb tr' bl := by
  unfold reqsT reqsJ8
  rw [extT_congr b h Pb bl,
    ReadIOJ8.compReqsX_congr (K := K) (qX δ b Pb tr (fun _ => 0) (fun _ => 0))
      (qX δ b Pb tr' (fun _ => 0) (fun _ => 0)) (fun c h1 h2 hc => h.C ⟨c, h1⟩ (by simp [crC, hc])) bl]

theorem provsT_congr (Pb : PubJ8 p) (bl : Bal) : provsT b Pb tr bl = provsT b Pb tr' bl := by
  have hW := DescentVSQ.walkLists_congrW b Pb.nodesW Pb.orbitW Pb.orbitW (fun _ => (0 : K)) (fun _ => 0)
    (fun _ => (0 : K)) (fun _ => 0) tr.W tr'.W (by norm_num) (by norm_num)
    (fun c h1 h2 hc => h.W ⟨c, h1⟩ (by simp [crW, hc]))
  have hV := DescentVSQ.walkLists_congrW b Pb.nodesV Pb.orbitV Pb.orbitV (fun _ => (0 : K)) (fun _ => 0)
    (fun _ => (0 : K)) (fun _ => 0) tr.V tr'.V (by norm_num) (by norm_num)
    (fun c h1 h2 hc => h.V ⟨c, h1⟩ (by simp [crW, hc]))
  have hJ := ReadIOJ8.jLists_congr b Pb.nodesJ Pb.orbitJ Pb.orbitJ (fun _ => (0 : K)) (fun _ => 0)
    (fun _ => (0 : K)) (fun _ => 0) tr.J tr'.J Pb.lay (by norm_num) (by norm_num)
    (fun c h1 h2 hc => h.J ⟨c, h1⟩ (by simp [crJ, hc]))
  cases bl
  · exact ReadIOJ8.cellProvsW_congr b Pb.nodesC Pb.orbitC Pb.orbitC _ _ _ _ tr.M tr'.M (by norm_num) (by norm_num)
      (fun c h1 h2 hc => h.M ⟨c, h1⟩ (by simp [crM, hc]))
  · exact hW.2
  · show _ ++ (pad8 _ ++ pad8 _) = _ ++ (pad8 _ ++ pad8 _)
    rw [hJ.2.2, hV.2, ReadIOJ8.atomIncProvs_congr b Pb.nodesA Pb.orbitA Pb.orbitA _ _ (fun _ => (0 : K))
      (fun _ => 0) tr.A tr'.A (by norm_num) (by norm_num) (fun c h1 h2 hc => h.A ⟨c, h1⟩ (by simp [crA, hc]))]

end Stage

/-! ## 3. `realIO` / `real40` -/

section Real
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`R` with the cell-export (#5) and service (#6) lists read off the trace** (coin-free, `dep = ∅`). -/
def realIO (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (Pb : PubJ8 p) : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g :=
  { R with
    D := { R.D with
      cxReqs := fun tr _ => reqsT δ b Pb tr .x
      cxProvs := fun tr _ => liftP (provsT b Pb tr .x)
      cx_reads := fun Q hQ χ χ' _ => by
        have h := agree0_of_staged hQ χ χ'
        simp only [reqsT_congr δ b h Pb, provsT_congr b h Pb]
      svReqs := fun tr _ => reqsT δ b Pb tr .s
      svProvs := fun tr _ => effP (liftP (provsT b Pb tr .s))
      sv_reads := fun Q hQ χ χ' _ => by
        have h := agree0_of_staged hQ χ χ'
        simp only [reqsT_congr δ b h Pb, provsT_congr b h Pb] } }

def real40 (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (Pb : PubJ8 p) : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r :=
  { L with
    pReqs := fun tr _ => reqsT δ b Pb tr .p
    pProvs := fun tr _ => liftP (provsT b Pb tr .p)
    p_reads := fun Q hQ ψ ψ' _ => by
      obtain ⟨Q', hQ', y₁, y₂, rfl⟩ := hQ
      have h := agree0_of_staged hQ' (extY ψ y₁ y₂) (extY ψ' y₁ y₂)
      simp only [reqsT_congr δ b h Pb, provsT_congr b h Pb] }

/-! ## 4. The readouts `rdX` / `rdS` / `rdP` -/

theorem rdX_realIO (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    (realIO δ b R Pb).D.cxReqs tr χ = reqsOf δ b Pb c χ M tr .x ∧
      (realIO δ b R Pb).D.cxProvs tr χ = liftP (provsJ8 δ b Pb χ M tr .x) :=
  ⟨(reqsOf_eq δ b Pb c χ M tr .x).symm, by rw [provsJ8_eq δ b Pb χ M tr .x]; rfl⟩

theorem rdS_realIO (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    (realIO δ b R Pb).D.svReqs tr χ = reqsOf δ b Pb c χ M tr .s ∧
      (realIO δ b R Pb).D.svProvs tr χ = effP (liftP (provsJ8 δ b Pb χ M tr .s)) :=
  ⟨(reqsOf_eq δ b Pb c χ M tr .s).symm, by rw [provsJ8_eq δ b Pb χ M tr .s]; rfl⟩

theorem rdP_real40 (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    (real40 δ b L Pb).pReqs tr (toVSQ χ) = reqsOf δ b Pb c χ M tr .p ∧
      (real40 δ b L Pb).pProvs tr (toVSQ χ) = liftP (provsJ8 δ b Pb χ M tr .p) :=
  ⟨(reqsOf_eq δ b Pb c χ M tr .p).symm, by rw [provsJ8_eq δ b Pb χ M tr .p]; rfl⟩

end Real

/-! ## 5. The budgets and the counts -/

section Bud
open Nock.Jet.ChipJ8 (keysOf entsX ents0T ents1T ents2T ents3 Kd KE PRow)

/-- The number of keys the J rows of a public layout put in the slots `es` (public, verifier-computed). -/
def jCount (es : List (Kd × List KE)) {n : ℕ} (lay : Fin n → PRow) : ℕ :=
  ((List.finRange n).map fun i => (es.filter fun e => e.1 == (lay i).kd).length).sum

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (b : Basis (Fin 3) (ZMod p) K)
  {h n w : ℕ} (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (lay : Fin n → PRow) (Q : Fin w → (ZMod p)[X])

theorem length_flatMap_finRange {β : Type*} (f : Fin n → List β) :
    ((List.finRange n).flatMap f).length = ((List.finRange n).map fun i => (f i).length).sum := by
  rw [List.length_flatMap]

theorem jRd_length : (jRd b nodes orbit chals pubs lay Q).length = jCount entsX lay := by
  unfold jRd jCount
  rw [length_flatMap_finRange]
  simp [keysOf, Nock.Jet.RapJetJ8.rowJ]

theorem jCons_length :
    (jCons b nodes orbit chals pubs lay Q).length = jCount ents0T lay + jCount ents1T lay := by
  unfold jCons jCount
  rw [length_flatMap_finRange, ← List.sum_map_add]
  simp [keysOf, Nock.Jet.RapJetJ8.consKT, Nock.Jet.RapJetJ8.rowJ]

theorem jProv_length :
    (jProv b nodes orbit chals pubs lay Q).length = jCount ents2T lay + jCount ents3 lay := by
  unfold jProv jCount
  rw [length_flatMap_finRange, ← List.sum_map_add]
  simp [keysOf, Nock.Jet.RapJetJ8.provKT, Nock.Jet.RapJetJ8.rowJ]

end Bud

/-! ## 6. `budX` / `budP` / `budS` / `hcount` from public budget checks -/

section Budgets
open Nock.Jet.ChipJ8 (entsX ents0T ents1T ents2T ents3)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **The public budget checks** of the three handle balances: the frame's row parameters cover the public row
counts (`2·n ≤ N`: an `s5` row consumes two service records, `ReadIOJ8.capB`). -/
structure BudJ8 (Pb : PubJ8 p) (r : RowsJ8) (g : ℕ) : Prop where
  x1 : 3 * Pb.n + Pb.nW + jCount entsX Pb.lay ≤ 3 * r.N + r.W + r.rd
  x2 : Pb.nC ≤ r.D
  p1 : Pb.n ≤ r.N
  p2 : Pb.nW ≤ r.W
  s1 : 2 * Pb.n + Pb.regs.length + (jCount ents0T Pb.lay + jCount ents1T Pb.lay) ≤ r.N + 2 * r.J + g
  s2 : jCount ents2T Pb.lay + jCount ents3 Pb.lay + Pb.nA + 2 * Pb.nV ≤ r.calls + r.heads + r.blocks + r.J

theorem walkXReqs_length {F K' : Type} [Field F] [Field K'] [Algebra F K'] (b' : Basis (Fin 3) F K')
    {h n w : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K') (Q : Fin w → F[X]) :
    (ServeH.walkXReqs b' nodes orbit chals pubs Q).length = n := by simp [ServeH.walkXReqs]

theorem walkPProvs_length {F K' : Type} [Field F] [Field K'] [Algebra F K'] (b' : Basis (Fin 3) F K')
    {h n w : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K') (Q : Fin w → F[X]) :
    (ServeH.walkPProvs b' nodes orbit chals pubs Q).length = 2 * n := by
  simp [ServeH.walkPProvs, List.length_flatMap, mul_comm]

theorem reqsOf_length (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (bl : Bal) :
    (reqsOf δ b Pb c χ M tr bl).length =
      (compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
        (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) bl).length +
      (extJ8 δ b Pb c χ M tr bl).length := by
  simp [reqsOf, reqsJ8]

variable {Rg : Nock.Jet.Registry} {r : RowsJ8} {g : ℕ}

theorem compLen (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr) (hp : 17 < p) (bl : Bal) :
    (compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
        (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) bl).length ≤ ReadIOJ8.capB bl * Pb.n :=
  ReadIOJ8.compReqsX_length_le hacc.hsatX (by rw [ZMod.ringChar_zmod_n]; exact hp) bl

/-- **`budX`** at `realIO`. -/
theorem budX_of (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g) :
    (reqsOf δ b Pb c χ M tr .x).length ≤ 3 * r.N + r.W + r.rd ∧
      (liftP (δ := δ) (provsJ8 δ b Pb χ M tr .x)).length ≤ r.D := by
  refine ⟨?_, ?_⟩
  · rw [reqsOf_length]
    have h1 := compLen δ b Pb c χ M tr hacc hp .x
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

/-- **`budP`** at `real40`. -/
theorem budP_of (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g) :
    (reqsOf δ b Pb c χ M tr .p).length ≤ 2 * r.N ∧
      (liftP (δ := δ) (provsJ8 δ b Pb χ M tr .p)).length ≤ 2 * r.W := by
  refine ⟨?_, ?_⟩
  · rw [reqsOf_length]
    have h1 := compLen δ b Pb c χ M tr hacc hp .p
    have h2 : (extJ8 δ b Pb c χ M tr .p).length = 0 := rfl
    simp only [ReadIOJ8.capB] at h1
    have := hB.p1
    omega
  · simp only [liftP, List.length_map]
    show (ServeH.walkPProvs b Pb.nodesW Pb.orbitW _ _ _).length ≤ 2 * r.W
    rw [walkPProvs_length]; have := hB.p2; omega

theorem atomIncProvs_length_le {F K' : Type} [Field F] [Field K'] [Algebra F K'] [DecidableEq F]
    (b' : Basis (Fin 3) F K') {h n w : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (chals pubs : ℕ → K') (Q : Fin w → F[X]) : (atomIncProvs b' nodes orbit chals pubs Q).length ≤ n := by
  unfold atomIncProvs
  exact (AcceptsJ8P.length_flatMap_ite_le _ _ _).trans (by simp)

/-- **`budS`** at `realIO`. -/
theorem budS_of (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g) :
    (reqsOf δ b Pb c χ M tr .s).length ≤ r.N + 2 * r.J + g ∧
      (effP (liftP (δ := δ) (provsJ8 δ b Pb χ M tr .s))).length ≤ r.calls + r.heads + r.blocks + r.J := by
  refine ⟨?_, ?_⟩
  · rw [reqsOf_length]
    have h1 := compLen δ b Pb c χ M tr hacc hp .s
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
    show (_ ++ (pad8 _ ++ pad8 _)).length ≤ _
    simp only [List.length_append, pad8, List.length_map, jProv_length, walkPProvs_length]
    have := atomIncProvs_length_le b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA)
    have := hB.s2
    omega

/-- **`hcount`** from the budgets and the frame's caps below `p`. -/
theorem hcount_of (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr) (hp : 17 < p) (hB : BudJ8 Pb r g)
    (hcap : 3 * r.N + r.W + r.rd < p ∧ 2 * r.N < p ∧ r.N + 2 * r.J + g < p) :
    ∀ bl, (reqsOf δ b Pb c χ M tr bl).length < p := by
  intro bl
  cases bl
  · exact lt_of_le_of_lt (budX_of δ b Pb c χ M tr hacc hp hB).1 hcap.1
  · exact lt_of_le_of_lt (budP_of δ b Pb c χ M tr hacc hp hB).1 hcap.2.1
  · exact lt_of_le_of_lt (budS_of δ b Pb c χ M tr hacc hp hB).1 hcap.2.2

/-- The caps hold at every row parameter below the census corner, `g ≤ 2^31`, Goldilocks. -/
theorem hcap_corner {r : RowsJ8} (hr : RowsLe r EncInjJ8.cornerC) (hg : g ≤ 2 ^ 31) (hpG : p = Nock.Atoms.p) :
    3 * r.N + r.W + r.rd < p ∧ 2 * r.N < p ∧ r.N + 2 * r.J + g < p := by
  obtain ⟨hN, -, hW, -, -, -, hJ, -, -, -, -, -, hrd, -, -⟩ := hr
  simp only [EncInjJ8.cornerC, corner31] at hN hW hJ hrd
  subst hpG
  simp only [Nock.Atoms.p, Nock.Field.p]
  refine ⟨by omega, by omega, by omega⟩

end Budgets

end

end Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8
