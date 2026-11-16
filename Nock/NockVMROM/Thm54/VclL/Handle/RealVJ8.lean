/-
  Nock/NockVMROM/Thm54/VclL/Handle/RealVJ8.lean

* `mbXs_congr`: the atom table's exported validity keys read only the leaves `37 / 38` of the atom vector and the
    columns `< 259` (round `≤ 1`); no other coin, no public.
  * **`valReqsJ8 Pb c`**: the claim's cell records with the serials READ from compute row 0 (`claimRecsT`), the
    registry pin records (verifier), the cell table's validity internal consumers (`cVInt` of the restriction
    `129 → 134`); **`valProvsJ8 Pb`**: the cell table's validity providers and the atom table's `mb` rows at
    `chalsAJ8Z` (leaves `37 / 38` = `z`).  **`valJ8_reads`**: read set `coinsBelow frameJ8 1`.
  * **`rdV_view`**: on an `AcceptsJ8''` trace, the readout IS `LinkJ8X''.rdV`'s pair at `toMsgJ8Z` (the claim
    serials by `row0_hdZ`); `valJ8_length`.
  * #1.5 **`fxReqsJ8` / `fxProvsJ8`** (on `frameVSQ` coins): the J-8 walk's consumed export keys (`walkXInternal`
    of the restriction `21 → 25` of the J-8 walk trace) and the cell table's export records (`cXRec` of the
    restriction `129 → 134`), lifted; `fxJ8_reads` along the 40th's view.
  * **`realV R Pb c`** (#2 on `R`), **`realFx L Pb`** (#1.5 on `L`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RealAJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.RealVJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun claimH isCellN)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crA crM crW crC staged_eq below_of_mem shV)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (mbXs claimCells claimRecsJ8 pinRecsJ8 rkC MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_zAt)

noncomputable section

/-! ## 1. `mbXs` reads leaves `37 / 38` and the columns `< 259` -/

section MB
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δF : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δF))]
  (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ} (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)

theorem mbXs_congr {w w' : ℕ} (chals pubs chals' pubs' : ℕ → K) (Q : Fin w → (ZMod p)[X]) (Q' : Fin w' → (ZMod p)[X])
    (hw : 259 ≤ w) (hw' : 259 ≤ w') (hQ : ∀ (j : ℕ) (hj : j < 259), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩)
    (h37 : chals 37 = chals' 37) (h38 : chals 38 = chals' 38) :
    mbXs δF b nodes orbit chals pubs Q = mbXs δF b nodes orbit chals' pubs' Q' := by
  unfold mbXs
  congr 1; funext i
  have hF : ∀ j < 259, (AtomServedQ.aEF b nodes orbit chals pubs Q i).trace j =
      (AtomServedQ.aEF b nodes orbit chals' pubs' Q' i).trace j := by
    intro j hj
    simp only [AtomServedQ.aEF]
    rw [envOfTrace_trace Q _ _ _ _ (by omega : j < w), envOfTrace_trace Q' _ _ _ _ (by omega : j < w'), hQ j hj]
  have hK : ∀ r < 18, (AtomServedQ.aEK δF b nodes orbit chals pubs Q i).trace r =
      (AtomServedQ.aEK δF b nodes orbit chals' pubs' Q' i).trace r := by
    refine gather_trace_congr b _ (BK := 18) (fun r hr k hk => hF _ ?_)
    simp only [ChipTemplate.col0, AtomChipHQ.atomTemplateHQ_baseCols]; omega
  have hc : ∀ j, (AtomServedQ.aEK δF b nodes orbit chals pubs Q i).chal j = chals j :=
    TeleH.gather_chal_T b (AtomChipHQ.atomTemplateHQ δF) 205 (AtomChipHQ.atomTemplateHQ_baseCols δF) _ chals rfl
  have hc' : ∀ j, (AtomServedQ.aEK δF b nodes orbit chals' pubs' Q' i).chal j = chals' j :=
    TeleH.gather_chal_T b (AtomChipHQ.atomTemplateHQ δF) 205 (AtomChipHQ.atomTemplateHQ_baseCols δF) _ chals' rfl
  have hkey : keyVec δF 5 AtomChipHQ.mbKey (AtomServedQ.aEK δF b nodes orbit chals pubs Q i)
      (AtomServedQ.aEF b nodes orbit chals pubs Q i) =
      keyVec δF 5 AtomChipHQ.mbKey (AtomServedQ.aEK δF b nodes orbit chals' pubs' Q' i)
        (AtomServedQ.aEF b nodes orbit chals' pubs' Q' i) := by
    funext c
    fin_cases c
    · simp only [keyVec, AtomChipHQ.mbKey, AtomChipHQ.zAt]
      simp only [Fin.zero_eta, Fin.isValue, Fin.val_zero, List.getD_cons_zero, ev_chal, hc, hc', h37, h38]
    · rfl
    · simp only [keyVec, AtomChipHQ.mbKey]
      simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Fin.val_two, List.getD_cons_succ,
        List.getD_cons_zero, ev_var, hK (Cell.pR + 4) (by simp [Cell.pR]), hK (Cell.pR + 4 + 1) (by simp [Cell.pR])]
    · rfl
    · simp only [keyVec, AtomChipHQ.mbKey]
      simp only [Fin.reduceFinMk, Fin.isValue, List.getD_cons_succ, List.getD_cons_zero, ev_base,
        CoeffExpr.eval, cv, hF Cell.idx (by decide)]
  rw [hkey, hF AtomChipHQ.mb (by decide)]

end MB

/-! ## 2. The cell validity readout (#2) -/

theorem shM : ∀ j < 225, shiftCol 129 134 j < 242 := by
  intro j hj; unfold shiftCol; split_ifs <;> omega

theorem shM_round (j : ℕ) (hj : j < 183) : crM ⟨shiftCol 129 134 j, shM j (by omega)⟩ ≤ 1 := by
  simp only [crM, shiftCol]; split_ifs <;> omega

section Val
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (xS xF xE)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (envCJ8)

/-- **The claim's cell records, the serials READ from compute row 0** (round-0 compute columns, no message). -/
def claimRecsT (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (tr : TrJ8 (ZMod p)) :
    List (Fin 5 → 𝕂′) :=
  (claimCells c).map fun k => ClaimVS.claimVec δ (encJ8 δ χ (claimNoun c k))
    ((envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C 0).trace (![xS, xF, xE] k).v)
    ((rkC (claimNoun c k)).1 : ZMod p) ((rkC (claimNoun c k)).2 : ZMod p)

/-- **#2's requests on a J-8 trace**: claim records (serials off row 0), registry pins, the cell table's validity
internal consumers. -/
def valReqsJ8 (Pb : PubJ8 p) (c : P8PublicClaim) (tr : TrJ8 (ZMod p)) (χ : Coins frameJ8 K) : List (Fin 5 → 𝕂′) :=
  (claimRecsT δ Pb c χ tr ++ pinRecsJ8 δ Pb χ) ++
    cVInt δ b Pb.nodesC Pb.orbitC (fun _ => (0 : K)) (fun _ => 0) (restrictQ 129 134 shM tr.M)

/-- **#2's providers on a J-8 trace**: the cell table's validity providers (lifted) and the atom table's exported
keys read from its `mb` rows at `chalsAJ8Z`. -/
def valProvsJ8 (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (χ : Coins frameJ8 K) : List ((Fin 5 → 𝕂′) × 𝕂′) :=
  liftWts (cVRec δ b Pb.nodesC Pb.orbitC (fun _ => (0 : K)) (fun _ => 0) (restrictQ 129 134 shM tr.M)) ++
    mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) (fun _ => 0) tr.A

theorem encJ8_congr {χ χ' : Coins frameJ8 K} (h : ∀ i ∈ coinsBelow frameJ8 1, χ i = χ' i) :
    encJ8 δ χ = encJ8 δ χ' := by
  have hm : ∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → i ∈ coinsBelow frameJ8 1 := fun i hi => by
    simp only [coinsBelow, Finset.mem_filter, Finset.mem_univ, true_and, hi]; norm_num
  simp only [encJ8, h c2 (hm _ (by decide)), h c3 (hm _ (by decide)), h cY1 (hm _ (by decide)),
    h cY2 (hm _ (by decide))]

theorem valJ8_reads (Pb : PubJ8 p) (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q) :
    ReadsOnC frameJ8 (coinsBelow frameJ8 1) fun χ => (valReqsJ8 δ b Pb c (Q χ) χ, valProvsJ8 δ b Pb (Q χ) χ) := by
  intro χ χ' hχ
  have hE := encJ8_congr δ hχ
  have hm : ∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → i ∈ coinsBelow frameJ8 1 := fun i hi => by
    simp only [coinsBelow, Finset.mem_filter, Finset.mem_univ, true_and, hi]; norm_num
  refine Prod.ext ?_ ?_
  · show (claimRecsT δ Pb c χ (Q χ) ++ pinRecsJ8 δ Pb χ) ++ _ = (claimRecsT δ Pb c χ' (Q χ') ++ pinRecsJ8 δ Pb χ') ++ _
    have h1 : claimRecsT δ Pb c χ (Q χ) = claimRecsT δ Pb c χ' (Q χ') := by
      unfold claimRecsT
      refine List.map_congr_left fun k _ => ?_
      have ht : (envCJ8 Pb.hn Pb.nodes Pb.orbit (Q χ).C 0).trace (![xS, xF, xE] k).v =
          (envCJ8 Pb.hn Pb.nodes Pb.orbit (Q χ').C 0).trace (![xS, xF, xE] k).v := by
        have hk : (![xS, xF, xE] k).v < 69 := by fin_cases k <;> decide
        simp only [envCJ8]
        rw [envOfTrace_trace _ _ _ _ _ (by omega : (![xS, xF, xE] k).v < 123),
          envOfTrace_trace _ _ _ _ _ (by omega : (![xS, xF, xE] k).v < 123),
          staged_eq hQ.1 (r := 0) (fun i hi => absurd hi (by omega)) _ (by simp only [crC, if_pos hk, le_refl])]
      rw [hE, ht]
    have h2 : pinRecsJ8 δ Pb χ = pinRecsJ8 δ Pb χ' := by unfold pinRecsJ8; rw [hE]
    rw [h1, h2]
    congr 1
    refine cVInt_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ (by norm_num) (by norm_num) fun j hj => ?_
    exact staged_eq hQ.2.1 (below_of_mem hχ) _ (shM_round j hj)
  · show liftWts _ ++ _ = liftWts _ ++ _
    congr 1
    · congr 1
      refine cVRec_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ (by norm_num) (by norm_num) fun j hj => ?_
      exact staged_eq hQ.2.1 (below_of_mem hχ) _ (shM_round j hj)
    · refine mbXs_congr δ b Pb.nodesA Pb.orbitA _ _ _ _ _ _ (by norm_num) (by norm_num) (fun j hj => ?_) ?_ ?_
      · exact staged_eq hQ.2.2.2.2.1 (below_of_mem hχ) _ (by simp only [crA]; split_ifs <;> omega)
      · simp only [chalsAJ8Z, if_pos rfl]; exact hχ c2 (hm _ (by decide))
      · simp only [chalsAJ8Z, if_neg (show (38 : ℕ) ≠ 37 by decide), if_pos rfl]; exact hχ c3 (hm _ (by decide))

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP (toMsgJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)

/-- **The claim serials off row 0** (on an `AcceptsJ8Z` trace, `row0_hdZ`): the readout's claim records are
`toMsgJ8Z`'s. -/
theorem claimRecsT_eq (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p)
    (hacc : AcceptsJ8Z δ b Pb Rg c χ (toMsgJ8Z δ b Pb c χ M tr) tr) :
    claimRecsT δ Pb c χ tr = claimRecsJ8 δ χ c M.m := by
  unfold claimRecsT claimRecsJ8
  refine List.map_congr_left fun k hk => ?_
  have hc : isCellN (claimNoun c k) = true := (List.mem_filter.mp hk).2
  have hd := AcceptsJ8ZL.row0_hdZ δ b Pb Rg c χ (toMsgJ8Z δ b Pb c χ M tr) tr hp hacc k
  have htr : (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C 0).trace =
      (envX δ b Pb c χ (toMsgJ8Z δ b Pb c χ M tr) tr 0).trace := by
    simp only [envCJ8, envX, TeleC.envsN]
    split_ifs <;> rfl
  have h2 := congrArg Prod.snd hd
  simp only [hdV] at h2
  have hv := ZMod.val_injective p h2
  have hm : (toMsgJ8Z δ b Pb c χ M tr).m = M.m := rfl
  rw [htr, hv, hm]
  congr 2
  unfold claimH
  cases hx : claimNoun c k with
  | atom v => rw [hx] at hc; simp [isCellN] at hc
  | cell a b' => rfl

/-- **#2 at an accepted trace**: the readout IS `LinkJ8X''.rdV`'s pair at `toMsgJ8Z`. -/
theorem rdV_view (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p)
    (hacc : AcceptsJ8Z δ b Pb Rg c χ (toMsgJ8Z δ b Pb c χ M tr) tr) :
    valReqsJ8 δ b Pb c tr χ = (toMsgJ8Z δ b Pb c χ M tr).reqsC ++
      cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) (toMsgJ8Z δ b Pb c χ M tr).pubsC
        (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) (toMsgJ8Z δ b Pb c χ M tr).pubsC
          (qM δ b Pb tr (chalsMJ8 δ χ) (toMsgJ8Z δ b Pb c χ M tr).pubsC)) ∧
    valProvsJ8 δ b Pb tr χ = SVFrame.liftWts (cellVRecords δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
      (toMsgJ8Z δ b Pb c χ M tr).pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) (toMsgJ8Z δ b Pb c χ M tr).pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) (toMsgJ8Z δ b Pb c χ M tr).pubsC))) ++ (toMsgJ8Z δ b Pb c χ M tr).xsC := by
  have hw : 183 ≤ (cellChip δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.w := by
    rw [cell_w]; norm_num
  refine ⟨?_, ?_⟩
  · show (claimRecsT δ Pb c χ tr ++ pinRecsJ8 δ Pb χ) ++ _ = (claimRecsJ8 δ χ c M.m ++ pinRecsJ8 δ Pb χ) ++ _
    rw [claimRecsT_eq δ b Pb Rg c χ M tr hp hacc, cVInt_chip]
    refine congrArg ((claimRecsJ8 δ χ c M.m ++ pinRecsJ8 δ Pb χ) ++ ·) ?_
    exact cVInt_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ (by norm_num) hw fun j hj => congrArg tr.M (Fin.ext rfl)
  · show liftWts _ ++ mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) (fun _ => 0) tr.A =
      liftWts _ ++ mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
    rw [cVRec_chip]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · exact congrArg liftWts
        (cVRec_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ (by norm_num) hw fun j hj => congrArg tr.M (Fin.ext rfl))
    · exact mbXs_congr δ b Pb.nodesA Pb.orbitA _ _ _ _ _ _ (by norm_num)
        (by rw [AtomChipHQ.atomChipHQ_width]; norm_num) (fun j hj => rfl) rfl rfl

theorem claimRecsT_length (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (tr : TrJ8 (ZMod p)) :
    (claimRecsT δ Pb c χ tr).length ≤ 3 := by
  simp only [claimRecsT, claimCells, List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

/-- **`budV` at the readout**: `≤ 3 + |regs| + 2 nC` requests, `≤ nC + nA` providers. -/
theorem valJ8_length (Pb : PubJ8 p) (c : P8PublicClaim) (tr : TrJ8 (ZMod p)) (χ : Coins frameJ8 K) :
    (valReqsJ8 δ b Pb c tr χ).length ≤ 3 + Pb.regs.length + 2 * Pb.nC ∧
      (valProvsJ8 δ b Pb tr χ).length ≤ Pb.nC + Pb.nA := by
  refine ⟨?_, ?_⟩
  · unfold valReqsJ8
    have h1 := claimRecsT_length δ Pb c χ tr
    have h2 := cVInt_length δ b Pb.nodesC Pb.orbitC (fun _ => (0 : K)) (fun _ => 0) (restrictQ 129 134 shM tr.M)
    simp only [List.length_append, pinRecsJ8, List.length_map]
    omega
  · unfold valProvsJ8
    have h1 := cVRec_length δ b Pb.nodesC Pb.orbitC (fun _ => (0 : K)) (fun _ => 0) (restrictQ 129 134 shM tr.M)
    have h2 : (mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) (fun _ => (0 : K)) tr.A).length ≤ Pb.nA := by
      unfold mbXs
      exact (AcceptsJ8P.length_flatMap_ite_le _ _ _).trans (by simp)
    rw [List.length_append, liftWts_length, h1]
    omega

variable {r : RowsJ8} {P g : ℕ}

/-- **`R` with the cell validity (#2) lists read off the trace.** -/
def realV (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (Pb : PubJ8 p) (c : P8PublicClaim) :
    DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g :=
  { R with
    D := { R.D with
      valReqs := fun tr χ => valReqsJ8 δ b Pb c tr χ
      valProvs := fun tr χ => valProvsJ8 δ b Pb tr χ
      val_reads := fun Q hQ => valJ8_reads δ b Pb c Q hQ } }

end Val

/-! ## 3. The J-8 walk's fingerprint-export readout (#1.5) and `hXW` -/

section Fx
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h)

/-- **The walk's consumed export keys read only the columns `< 93` outside the certificate block `14..20`.** -/
theorem wXInt_congr_off {w w' : ℕ} (Q : Fin w → F[X]) (Q' : Fin w' → F[X]) (hw : 93 ≤ w)
    (hw' : 93 ≤ w') (hQ : ∀ (j : ℕ) (hj : j < 93), (j < 14 ∨ 21 ≤ j) → Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩)
    (chals pubs chals' pubs' : ℕ → K) :
    walkXInternal δF kroots b hn nodes orbit chals pubs Q = walkXInternal δF kroots b hn nodes orbit chals' pubs' Q' := by
  unfold walkXInternal; congr 1; funext j
  have hF : ∀ c < 93, (c < 14 ∨ 21 ≤ c) → (Chips.ChipRAP.walkEnvF b hn nodes orbit chals pubs Q j).trace c =
      (Chips.ChipRAP.walkEnvF b hn nodes orbit chals' pubs' Q' j).trace c := by
    intro c hc hoff
    unfold Chips.ChipRAP.walkEnvF
    rw [envOfTrace_trace Q _ _ _ _ (by omega : c < w), envOfTrace_trace Q' _ _ _ _ (by omega : c < w'),
      hQ c hc hoff]
  have hK : ∀ r < 24, (Chips.ChipRAP.walkEnvK δF kroots b hn nodes orbit chals pubs Q j).trace r =
      (Chips.ChipRAP.walkEnvK δF kroots b hn nodes orbit chals' pubs' Q' j).trace r := by
    unfold Chips.ChipRAP.walkEnvK
    refine gather_trace_congr b _ (BK := 24) (fun r hr k hk => hF _ ?_ ?_)
    · simp only [ChipTemplate.col0, walkTemplate_baseCols]; omega
    · simp only [ChipTemplate.col0, walkTemplate_baseCols]; omega
  simp only [walkKey]
  rw [keyVec_congr δF hK (BF := 14) (fun c hc => hF c (by omega) (Or.inl hc)) 11 _ (by rfl : qLt 24 14 WChip.xKey = true)]

/-- `bitFix` is invisible to the walk's consumed export keys. -/
theorem wXInt_bitFix (chals pubs chals' pubs' : ℕ → K) (W : Fin 166 → F[X]) :
    walkXInternal δF kroots b hn nodes orbit chals' pubs'
        (AtomWalkAW.restrictWalkK δF kroots b hn nodes orbit chals pubs (WalkJ8.bitFix δF kroots b hn nodes orbit chals pubs
          (fun j => W (Fin.cast (WalkJ8.walkChipJ8_width δF kroots b hn nodes orbit chals pubs) j)))) =
      walkXInternal δF kroots b hn nodes orbit (fun _ => 0) (fun _ => 0) (Handle.restrictQ 21 25 shV W) := by
  refine wXInt_congr_off δF kroots b hn nodes orbit _ _
    (by rw [walk_w δF kroots b hn nodes orbit chals pubs]; norm_num) (by norm_num) (fun j hj hoff => ?_) _ _ _ _
  simp only [AtomWalkAW.restrictWalkK, Handle.restrictQ]
  erw [WalkJ8.bitFix_off]
  · rfl
  · simp only [Handle.shiftCol]; split_ifs <;> omega

/-- **#1.5's requests on a J-8 trace**: the J-8 walk's consumed export keys (restriction `21 → 25`). -/
def fxReqsJ8 (tr : TraceJ8.TrJ8 F) : List (Fin 11 → Quad (algebraMap F K δF)) :=
  walkXInternal δF kroots b hn nodes orbit (fun _ => 0) (fun _ => 0) (Handle.restrictQ 21 25 shV tr.W)

end Fx

section FxP
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ}
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)

/-- **#1.5's providers on a J-8 trace**: the cell table's export records (restriction `129 → 134`), lifted. -/
def fxProvsJ8 (tr : TraceJ8.TrJ8 F) : List ((Fin 11 → Quad (algebraMap F K δF)) × Quad (algebraMap F K δF)) :=
  liftWts (cXRec δF b nodes orbit (fun _ => (0 : K)) (fun _ => 0) (Handle.restrictQ 129 134 shM tr.M))

end FxP

section FxR
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))] {r : RowsJ8}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 St40 sum40 fpx_out v4 v5 v6 v7)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (extY_below shV_round)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z)

/-- **Read set of #1.5** along the 40th's view: round-`≤ 1` columns only. -/
theorem fxJ8_reads (Pb : PubJ8 p) (Q : Coins frameVSQ K → TrJ8 (ZMod p)) (hQ : St40 (StJ8 (F := ZMod p)) Q) :
    ReadsOnC frameVSQ (coinsBelow frameVSQ 1) fun ψ =>
      (fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (Q ψ), fxProvsJ8 δ b Pb.nodesC Pb.orbitC (Q ψ)) := by
  obtain ⟨Q', hQ', y₁, y₂, rfl⟩ := hQ
  intro ψ ψ' hψ
  refine Prod.ext ?_ ?_
  · refine wXInt_congr δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW _ _ _ _ _ _ (by norm_num) (by norm_num)
      fun j hj => ?_
    exact staged_eq hQ'.2.2.1 (extY_below y₁ y₂ hψ) _ (shV_round j hj)
  · exact congrArg liftWts (cXRec_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ (by norm_num) (by norm_num)
      fun j hj => staged_eq hQ'.2.1 (extY_below y₁ y₂ hψ) _ (shM_round j hj))

/-- **`L` with the J-8 walk's fingerprint-export lists (#1.5) read off the trace.** -/
def realFx (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r) (Pb : PubJ8 p) :
    Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r :=
  { L with
    fxReqs := fun tr _ => fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr
    fxProvs := fun tr _ => fxProvsJ8 δ b Pb.nodesC Pb.orbitC tr
    fx_reads := fun Q hQ => fxJ8_reads δ b Pb Q hQ }

/-- **`LinkJ8.hXW` from the fingerprint-export lookup** (the class of `LinkJ8R2V.hXV_of_io`): on an `AcceptsJ8Z`
trace, with `pubsC(2,3) = pubsW(0,1)` and the validity pair outside the IO failure event of the J-8 walk's keys
(at the `bitFix` view) against the cell table's export records, every key the J-8 walk consumes is a decoded cell
row. -/
theorem hXW_of_io [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8Z δ b Pb Rg c χ M tr) (hp : 64 ≤ p)
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

end FxR

end

end Nock.NockVMROM.Thm54.VclL.Handle.RealVJ8
