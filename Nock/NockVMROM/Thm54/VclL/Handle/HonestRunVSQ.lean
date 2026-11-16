/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestRunVSQ.lean

  Additive: a NEW module.

  * `cell_dRowQ_vals` / `walk_dRowQ_vals` (field-generic in the row values), `cellRow0_key`;
  * `coinsCV_VSQ` / `chalsVSQ_gam` / `chalsVSQ_rho`: every chip reads the same `𝕂′` coins `(γH′, ρH′)`;
  * identifications 1–3 at `𝕂′`: `cell_dRowQ_eq_recDen`, `walk_dRowQ_honest` (`recDen′ / recDenP′` of
    `expKey`, `recLH`, `recRH` at `(ρH′, γH′)`);
  * `accSumXQ_eq` / `accSumPQ_eq`, `yHVSQ`, and the three twin terminals `hpubCQ_honest`, `hpubXQ_honest`,
    `hpubPQ_honest` (through the field-generic `export_total_link2_inv` and `compute_walk_balance` at
    `L := 𝕂′`);
  * `rhoVSQ` / `msgVSQ`: the honest VSQ message of a run (`compPolyQ`, `cellTraceHQ`, `walkTraceHQ`,
    `ρ₃′ = accSumXQ`, `ρ₄′ = accSumPQ`, round-2 message `(yTot, yH′)`);
  * **`honest_accepted_VSQ_run`**: `AcceptsG (vsqOf H.V) (msgVSQ …) χ` outside the honest bad events
    (`HonestBadFreeVSQ`, the `𝕂′` compute `NotBadRow`, the walk coin order).  This acceptance is the
    positive control of `rhoVSQ`, `yHVSQ` and `msgVSQ`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestAccVSQ
import Nock.NockVMROM.Thm54.VclL.Handle.HonestVS
import Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Module
open scoped Polynomial

noncomputable section

section CellGenericQ
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (vals : Fin n → CellVals F (Quad (algebraMap F K δF)))

theorem cellEQ_trace (hinj : Function.Injective nodes) (mhv : Fin n → F)
    (iv av : Fin n → Quad (algebraMap F K δF)) (i : Fin n) {j : ℕ} (h2 : 2 ≤ j) (hj : j < 129) :
    (CellTraceHQ.E δF b hn nodes orbit chals pubs (cellCol δF b vals) mhv iv av i).trace j =
      (vals i).base j := by
  have hw : j < (cellTemplateHQ δF).width 3 := by
    rw [CellTraceHQ.cellTemplateHQ_width]; omega
  unfold CellTraceHQ.E
  rw [env_trace hn nodes hinj _ _ _ _ i hw]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  simp [fullCol, CellTraceHQ.colHQ, extColF, cellCol, h0, h1, hj, show j < 129 from hj]

/-- **The `𝕂′` cell twin's handle denominator at a row, from the row's committed values.** -/
theorem cell_dRowQ_vals (hinj : Function.Injective nodes) (mhv : Fin n → F) (i : Fin n) :
    CellTraceHQ.dRow δF b hn nodes orbit chals pubs (cellCol δF b vals) mhv i =
      recDen (Quad.mk _ (chals 34) (chals 36)) (Quad.mk _ (chals 33) (chals 35))
        ((vals i).idx, ((vals i).wL, (vals i).wL * (vals i).idL + (1 - (vals i).wL) * (vals i).aL),
          ((vals i).wR, (vals i).wR * (vals i).idR + (1 - (vals i).wR) * (vals i).aR)) := by
  unfold CellTraceHQ.dRow
  rw [TeleHQ.denKeyQ_ev δF _ _ _ (by simp [CellH.keyH])]
  have hg := CellTraceHQ.gather_chal δF b chals
    (CellTraceHQ.E δF b hn nodes orbit chals pubs (cellCol δF b vals) mhv (fun _ => 0) (fun _ => 0) i) rfl
  simp only [TeleHQ.coinsQ, hg]
  have t := fun j (h2 : 2 ≤ j) (hj : j < 129) =>
    cellEQ_trace δF b hn nodes orbit chals pubs vals hinj mhv (fun _ => 0) (fun _ => 0) i h2 hj
  simp only [compress, Walk.rlc, Fin.sum_univ_five, BalanceQ.liftRec, ServeH.keyVec5, CellH.keyH, CellH.valE,
    List.getD_cons_zero, List.getD_cons_succ, CoeffExpr.eval, Cell.idx, Cell.wL, Cell.wR, Cell.idL, Cell.idR,
    Cell.aL, Cell.aR, recDen]
  simp only [show ((0 : Fin 5) : ℕ) = 0 from rfl, show ((1 : Fin 5) : ℕ) = 1 from rfl,
    show ((2 : Fin 5) : ℕ) = 2 from rfl, show ((3 : Fin 5) : ℕ) = 3 from rfl, show ((4 : Fin 5) : ℕ) = 4 from rfl,
    List.getD_cons_zero, List.getD_cons_succ, cv, notE, CoeffExpr.eval]
  rw [t 2 (by omega) (by omega), t 5 (by omega) (by omega), t 3 (by omega) (by omega),
    t 7 (by omega) (by omega), t 6 (by omega) (by omega), t 4 (by omega) (by omega), t 8 (by omega) (by omega)]
  simp only [CellVals.base]
  simp only [← IsScalarTower.algebraMap_apply]
  norm_num
  ring

end CellGenericQ

section WalkGenericQ
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kr : ℕ)
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (vals : Fin n → WalkVals F K (Quad (algebraMap F K δF))) (kLv vLv kRv vRv : Fin n → F)

theorem walkEQ_trace (hinj : Function.Injective nodes) (R : WalkTraceH.Roles n (Quad (algebraMap F K δF)))
    (i : Fin n) {j : ℕ} (h2 : 2 ≤ j) (hj : j < 25) :
    (WalkTraceHQ.E δF kr b hn nodes orbit chals pubs (walkCol δF b kr vals) kLv vLv kRv vRv R i).trace j =
      if j < 21 then (vals i).base kr i j else if j = 21 then kLv i else if j = 22 then vLv i
      else if j = 23 then kRv i else vRv i := by
  have hw : j < (walkTemplateHQ δF kr).width 3 := by rw [WalkTraceHQ.walkTemplateHQ_width]; omega
  unfold WalkTraceHQ.E
  rw [env_trace hn nodes hinj _ _ _ _ i hw]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  by_cases h21 : j < 21
  · simp [fullCol, WalkTraceHQ.colHQ, extColF, walkCol, h0, h1, h21]
  · have : j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp [fullCol, WalkTraceHQ.colHQ, extColF, WalkTraceHQ.new]

/-- **The `𝕂′` walk twin's denominators at a row, from the row's committed values.** -/
theorem walk_dRowQ_vals (hinj : Function.Injective nodes) (i : Fin n) :
    WalkTraceHQ.dRow δF kr b hn nodes orbit chals pubs WalkHC.xKeyH (walkCol δF b kr vals) kLv vLv kRv vRv i =
      recDen (Quad.mk _ (chals 34) (chals 36)) (Quad.mk _ (chals 33) (chals 35))
        ((vals i).idx, (kLv i, vLv i), (kRv i, vRv i)) ∧
    WalkTraceHQ.dRow δF kr b hn nodes orbit chals pubs WalkHC.recLH (walkCol δF b kr vals) kLv vLv kRv vRv i =
      recDenP (Quad.mk _ (chals 34) (chals 36)) (Quad.mk _ (chals 33) (chals 35))
        ((vals i).ridx, 2 * (vals i).pre, (kLv i, vLv i)) ∧
    WalkTraceHQ.dRow δF kr b hn nodes orbit chals pubs WalkHC.recRH (walkCol δF b kr vals) kLv vLv kRv vRv i =
      recDenP (Quad.mk _ (chals 34) (chals 36)) (Quad.mk _ (chals 33) (chals 35))
        ((vals i).ridx, 2 * (vals i).pre + 1, (kRv i, vRv i)) := by
  have t := fun j (h2 : 2 ≤ j) (hj : j < 25) =>
    walkEQ_trace δF kr b hn nodes orbit chals pubs vals kLv vLv kRv vRv hinj (WalkTraceHQ.zeroR (K := K) δF) i h2 hj
  have t3 := t 3 (by omega) (by omega)
  have t4 := t 4 (by omega) (by omega)
  have t5 := t 5 (by omega) (by omega)
  have t21 := t 21 (by omega) (by omega)
  have t22 := t 22 (by omega) (by omega)
  have t23 := t 23 (by omega) (by omega)
  have t24 := t 24 (by omega) (by omega)
  norm_num [WalkVals.base, WalkVals.named] at t3 t4 t5
  norm_num at t21 t22 t23 t24
  have hg := WalkTraceHQ.gather_chal δF kr b chals
    (WalkTraceHQ.E δF kr b hn nodes orbit chals pubs (walkCol δF b kr vals) kLv vLv kRv vRv
      (WalkTraceHQ.zeroR (K := K) δF) i) rfl
  refine ⟨?_, ?_, ?_⟩ <;>
  · unfold WalkTraceHQ.dRow WalkTraceHQ.denAt
    simp only [HQ.denKeyQ, ev_add, HQ.rhoQ, ev_chal, TeleHQ.rlcQ_ev, hg, WalkHC.xKeyH, WalkHC.recLH, WalkHC.recRH,
      List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero,
      List.getD_cons_zero, List.getD_cons_succ, CoeffExpr.eval, cv, WChip.idx, WChip.pre, WChip.ridx,
      WalkHC.kL, WalkHC.vL, WalkHC.kR, WalkHC.vR, t3, t4, t5, t21, t22, t23, t24, recDen, recDenP]
    simp only [← IsScalarTower.algebraMap_apply]
    try simp only [map_add, map_mul, map_one, map_ofNat]
    ring

end WalkGenericQ

/-! ## The `𝕂′` coins as read by the three chips -/

section CoinsQ
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) (χ : Coins frameVSQ K)

theorem limb_chalVHQ (q : ℕ) (hq : q < 6) :
    limbVal b (chalVHQ b χ) (3 * q) = coinHQ χ q := by
  refine limbVal_eq_of_coords b _ _ _ fun k => ?_
  have hk := k.isLt
  simp only [chalVHQ]
  rw [if_pos (by omega)]
  have e1 : (3 * q + (k : ℕ)) / 3 = q := by omega
  congr 1
  · rw [e1]
  · apply Fin.ext; simp; omega

/-- **The compute chip's `𝕂′` handle coins are `(γH′, ρH′)`.** -/
theorem coinsCV_VSQ : TeleCQ.coinsCV b δF (chalVHQ b χ) = ⟨gamHQ δF χ, rhoHQ δF χ⟩ := by
  have h0 := limb_chalVHQ b χ 0 (by omega)
  have h1 := limb_chalVHQ b χ 1 (by omega)
  have h4 := limb_chalVHQ b χ 4 (by omega)
  have h5 := limb_chalVHQ b χ 5 (by omega)
  simp only [TeleCQ.coinsCV, ChipH.chalGammaL, ChipH.chalRhoL, ChipHQ.chalGammaIm, ChipHQ.chalRhoIm]
  simp only [Nat.mul_zero, Nat.mul_one, show 3 * 4 = 12 from rfl, show 3 * 5 = 15 from rfl] at h0 h1 h4 h5
  rw [h0, h1, h4, h5]
  rfl

/-- **The memory chips' `𝕂′` handle coins are `(γH′, ρH′)`.** -/
theorem chalsVSQ_gam : Quad.mk (algebraMap F K δF) (chalsVSQ δF χ 33) (chalsVSQ δF χ 35) = gamHQ δF χ := rfl
theorem chalsVSQ_rho : Quad.mk (algebraMap F K δF) (chalsVSQ δF χ 34) (chalsVSQ δF χ 36) = rhoHQ δF χ := rfl

end CoinsQ

/-! ## The honest identifications and terminals at `𝕂′` -/

section KeyF
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

/-- The generated cell row's export key is `expKey` of its noun (field-free form of `cellRow0_den`). -/
theorem cellRow0_key (z : Quad (algebraMap F K δF)) (cells vcs xs0 xs1 : List Noun) (n : Noun) :
    ((cellRow0 δF z cells vcs xs0 xs1 n).idx, ((cellRow0 δF z cells vcs xs0 xs1 n).wL,
        (cellRow0 δF z cells vcs xs0 xs1 n).wL * (cellRow0 δF z cells vcs xs0 xs1 n).idL +
          (1 - (cellRow0 δF z cells vcs xs0 xs1 n).wL) * (cellRow0 δF z cells vcs xs0 xs1 n).aL),
      ((cellRow0 δF z cells vcs xs0 xs1 n).wR,
        (cellRow0 δF z cells vcs xs0 xs1 n).wR * (cellRow0 δF z cells vcs xs0 xs1 n).idR +
          (1 - (cellRow0 δF z cells vcs xs0 xs1 n).wR) * (cellRow0 δF z cells vcs xs0 xs1 n).aR)) =
      expKey (F := F) cells n := by
  unfold expKey
  simp only [cellRow0]
  generalize hdN n = a
  generalize tlN n = c
  cases a <;> cases c <;> simp [Noun.isCell, hdl]

end KeyF

section HonestQ
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ}
  (H : HonestVCLW (K := K) δF hT hP hC kr)

/-- **Identification 1 at `𝕂′`**: the `𝕂′` cell twin's row denominator is `recDen ρH′ γH′` of the export key. -/
theorem cell_dRowQ_eq_recDen (bs : List Noun) (χ : Coins frameVSQ K) (pubs : ℕ → K)
    (mhv : Fin (H.V.memRows (tCW hT hP)) → F) (i : Fin (H.V.memRows (tCW hT hP))) :
    CellTraceHQ.dRow δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP))
        (chalsVSQ δF χ) pubs (cellColB H bs (toVCL (toVS χ))) mhv i =
      recDen (rhoHQ δF χ) (gamHQ δF χ) (expKey (F := F) H.d.cells (H.d.cells.getD i (.atom 0))) := by
  unfold cellColB
  rw [cell_dRowQ_vals δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP))
    (chalsVSQ δF χ) pubs _ (H.hinj _) mhv i, chalsVSQ_gam, chalsVSQ_rho]
  exact congrArg _ (cellRow0_key δF (zC (toVCL (toVS χ))) H.d.cells (vcsOf H.d.cells bs) (xs0W H.d)
    (xs1W H.d) (H.d.cells.getD i (.atom 0)))

/-- **Identifications 2 and 3 at `𝕂′`.** -/
theorem walk_dRowQ_honest (χ : Coins frameVSQ K) (pubs : ℕ → K) (i : Fin (H.V.memRows (tWW hT hP))) :
    WalkTraceHQ.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP))
        (chalsVSQ δF χ) pubs WalkHC.xKeyH (walkColVS H (toVS χ)) (kLvH H) (vLvH H) (kRvH H) (vRvH H) i =
      recDen (rhoHQ δF χ) (gamHQ δF χ) (expKey (F := F) H.d.cells (wLbl H i).node) ∧
    WalkTraceHQ.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP))
        (chalsVSQ δF χ) pubs WalkHC.recLH (walkColVS H (toVS χ)) (kLvH H) (vLvH H) (kRvH H) (vRvH H) i =
      recDenP (rhoHQ δF χ) (gamHQ δF χ) (Handle.recLH (F := F) H.d.cells (wLbl H i)) ∧
    WalkTraceHQ.dRow δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP))
        (chalsVSQ δF χ) pubs WalkHC.recRH (walkColVS H (toVS χ)) (kLvH H) (vLvH H) (kRvH H) (vRvH H) i =
      recDenP (rhoHQ δF χ) (gamHQ δF χ) (Handle.recRH (F := F) H.d.cells (wLbl H i)) := by
  obtain ⟨e1, e2, e3⟩ := walk_dRowQ_vals δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
    (H.V.orbitM (tWW hT hP)) (chalsVSQ δF χ) pubs (fun i' => H.wVals (toVCL (toVS χ)) i')
    (kLvH H) (vLvH H) (kRvH H) (vRvH H) (H.hinj _) i
  obtain ⟨w1, w2, w3⟩ := walkVals_idx H (toVS χ) i
  refine ⟨?_, ?_, ?_⟩
  · unfold walkColVS; rw [e1, chalsVSQ_gam, chalsVSQ_rho, w1]
    simp only [expKey, kLvH, vLvH, kRvH, vRvH]
  · unfold walkColVS; rw [e2, chalsVSQ_gam, chalsVSQ_rho, w2, w3]
    simp only [Handle.recLH, kLvH, vLvH]
    push_cast; ring_nf
  · unfold walkColVS; rw [e3, chalsVSQ_gam, chalsVSQ_rho, w2, w3]
    simp only [Handle.recRH, kRvH, vRvH]
    push_cast; ring_nf

end HonestQ

section SumsQ
variable {Kg : Type} [Field Kg]
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

/-- **`ρ₃′` is the consumed export total over the run's rows, at `𝕂′`.** -/
theorem accSumXQ_eq (b : Basis (Fin 3) F K) (cells : List Noun) (chalV : ℕ → F) (t : NTree (GenComputeRow Kg)) :
    HonestCompQ.accSumXQ δF b cells (wRows (bfsForest [airReorder t])) chalV (bfsForest [airReorder t]).length =
      (((bfsRows (airReorder t)).flatMap fun g =>
          (exportEntries (rowOfSkelH g.skel)).map (entryRec (F := F) cells)).map fun k =>
        (recDen (TeleCQ.coinsCV b δF chalV).pole (TeleCQ.coinsCV b δF chalV).gamma k)⁻¹).sum := by
  unfold HonestCompQ.accSumXQ
  refine (sum_wRows (bfsForest [airReorder t]) (fun r => ((exportEntries r).map fun x =>
    (recDen (TeleCQ.coinsCV b δF chalV).pole (TeleCQ.coinsCV b δF chalV).gamma
      (entryRec (F := F) cells x))⁻¹).sum)).trans ?_
  rw [FrameVS.sum_flatMap_map, bfsRows, List.map_map]
  congr 1
  refine List.map_congr_left fun u _ => ?_
  simp [List.map_map, Function.comp_def]

/-- **`ρ₄′` is the consumed path total over the run's rows, at `𝕂′`.** -/
theorem accSumPQ_eq (b : Basis (Fin 3) F K) (cells : List Noun) (chalV : ℕ → F) (t : NTree (GenComputeRow Kg)) :
    HonestCompQ.accSumPQ δF b cells (wRows (bfsForest [airReorder t])) chalV (bfsForest [airReorder t]).length =
      ((consEntriesAll (bfsRows (airReorder t))).map fun x =>
        (recDenP (TeleCQ.coinsCV b δF chalV).pole (TeleCQ.coinsCV b δF chalV).gamma
          (entRecP (F := F) cells x))⁻¹).sum := by
  unfold HonestCompQ.accSumPQ consEntriesAll
  refine (sum_wRows (bfsForest [airReorder t]) (fun r => ((consEntries (hn r)).map fun x =>
    (recDenP (TeleCQ.coinsCV b δF chalV).pole (TeleCQ.coinsCV b δF chalV).gamma
      (entRecP (F := F) cells x))⁻¹).sum)).trans ?_
  rw [FrameVS.sum_flatMap_map, bfsRows, List.map_map]
  rfl

end SumsQ

section TermQ
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ}
  (H : HonestVCLW (K := K) δF hT hP hC kr)

/-- **The honest walk export-consume total at `𝕂′`** `yH′ = Σ_j 1 / recDen′ (expKey node_j)`. -/
def yHVSQ (χ : Coins frameVSQ K) : Quad (algebraMap F K δF) :=
  ∑ j ∈ Finset.range (H.V.memRows (tWW hT hP)),
    (recDen (rhoHQ δF χ) (gamHQ δF χ) (expKey (F := F) H.d.cells (wLbl H j).node))⁻¹

/-- **`hpubX` at `𝕂′`.** -/
theorem hpubXQ_honest (χ : Coins frameVSQ K) (ρ : Fin 5 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF)) :
    yHVSQ H χ = ∑ j ∈ Finset.range (H.V.memRows (tWW hT hP)),
      (WalkTraceHQ.dN δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
        (H.V.orbitM (tWW hT hP)) (chalsVSQ δF χ) (pubsWHQ δF ρ y (yHVSQ H χ)) (walkColVS H (toVS χ))
        (kLvH H) (vLvH H) (kRvH H) (vRvH H) WalkHC.xKeyH j)⁻¹ := by
  unfold yHVSQ
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  simp only [WalkTraceHQ.dN, dif_pos hj']
  rw [(walk_dRowQ_honest H χ _ ⟨j, hj'⟩).1]

/-- **`hpubP` at `𝕂′`**, given the compute path terminal `ρ₄ = accSumPQ`. -/
theorem hpubPQ_honest (χ : Coins frameVSQ K) (ρ : Fin 5 → Quad (algebraMap F K δF))
    (y yH : Quad (algebraMap F K δF)) {t : NTree (GenComputeRow Kg)}
    (hd : H.d = demandH2 (bfsRows (airReorder t)))
    (hsem : ∀ g ∈ bfsRows (airReorder t), (rowOfSkel g.skel).Sem)
    (hρ4 : ρ 4 = HonestCompQ.accSumPQ δF H.V.basis H.d.cells (wRows (bfsForest [airReorder t]))
      (chalVHQ H.V.basis χ) (bfsForest [airReorder t]).length) :
    ρ 4 = ∑ j ∈ Finset.range (H.V.memRows (tWW hT hP)),
      (liftQ δF (WalkTraceH.cN j (walkColVS H (toVS χ) WChip.mL)) *
          (WalkTraceHQ.dN δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
            (H.V.orbitM (tWW hT hP)) (chalsVSQ δF χ) (pubsWHQ δF ρ y yH) (walkColVS H (toVS χ))
            (kLvH H) (vLvH H) (kRvH H) (vRvH H) WalkHC.recLH j)⁻¹ +
        liftQ δF (WalkTraceH.cN j (walkColVS H (toVS χ) WChip.mR)) *
          (WalkTraceHQ.dN δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
            (H.V.orbitM (tWW hT hP)) (chalsVSQ δF χ) (pubsWHQ δF ρ y yH) (walkColVS H (toVS χ))
            (kLvH H) (vLvH H) (kRvH H) (vRvH H) WalkHC.recRH j)⁻¹) := by
  rw [hρ4, accSumPQ_eq, coinsCV_VSQ]
  have hcw := compute_walk_balance (F := F) (fun k => (recDenP (rhoHQ δF χ) (gamHQ δF χ) k)⁻¹) H.d.cells
    (bfsRows (airReorder t)) hsem
  have hpre : walkReadsH (bfsRows (airReorder t)) = H.d.preads := by rw [hd]; rfl
  rw [hcw, hpre, ← sum_walkRows H (fun w => provH (fun k => (recDenP (rhoHQ δF χ) (gamHQ δF χ) k)⁻¹) H.d.cells w)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  obtain ⟨-, eL, eR⟩ := walk_dRowQ_honest H χ (pubsWHQ δF ρ y yH) ⟨j, hj'⟩
  simp only [WalkTraceHQ.dN, WalkTraceH.cN, dif_pos hj', eL, eR, provH, nsmul_eq_mul]
  have hmL : walkColVS H (toVS χ) WChip.mL ⟨j, hj'⟩ = (((wLbl H j).mL : ℕ) : F) := rfl
  have hmR : walkColVS H (toVS χ) WChip.mR ⟨j, hj'⟩ = (((wLbl H j).mR : ℕ) : F) := rfl
  rw [hmL, hmR]
  simp [liftQ]

/-- **`hpubC` at `𝕂′`**, given the compute export terminal `ρ₃ = accSumXQ`. -/
theorem hpubCQ_honest (χ : Coins frameVSQ K) (ρ : Fin 5 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF))
    (bs : List Noun) {t : NTree (GenComputeRow Kg)} (hd : H.d = demandH2 (bfsRows (airReorder t)))
    (hsem : ∀ g ∈ bfsRows (airReorder t), (rowOfSkel g.skel).Sem)
    (hpk : ∀ g ∈ bfsRows (airReorder t), PKS g)
    (hlen : H.d.cells.length < ringChar F)
    (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome)
    (hρ3 : ρ 3 = HonestCompQ.accSumXQ δF H.V.basis H.d.cells (wRows (bfsForest [airReorder t]))
      (chalVHQ H.V.basis χ) (bfsForest [airReorder t]).length) :
    ρ 3 + yHVSQ H χ = ∑ j ∈ Finset.range (H.V.memRows (tCW hT hP)),
      liftQ δF (CellTraceH.mN (mhvH H (bfsRows (airReorder t))) j) *
        (CellTraceHQ.dN δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP))
          (chalsVSQ δF χ) (pubsCHQ δF ρ y (yHVSQ H χ)) (cellColB H bs (toVCL (toVS χ)))
          (mhvH H (bfsRows (airReorder t))) j)⁻¹ := by
  set rows := bfsRows (airReorder t) with hrows
  have hcells : (demandH2 rows).cells = H.d.cells := by rw [hd]
  have hpreads : (demandH2 rows).preads = H.d.preads := by rw [hd]
  have hY : yHVSQ H χ = ((walkConsH2 (F := F) rows).map fun k => (recDen (rhoHQ δF χ) (gamHQ δF χ) k)⁻¹).sum := by
    unfold yHVSQ walkConsH2
    rw [sum_walkRows H (fun w => (recDen (rhoHQ δF χ) (gamHQ δF χ) (expKey (F := F) H.d.cells w.node))⁻¹),
      hcells, hpreads, List.map_map]
    rfl
  have hX : ρ 3 = ((consumedH2 (F := F) rows).map fun k => (recDen (rhoHQ δF χ) (gamHQ δF χ) k)⁻¹).sum := by
    rw [hρ3, accSumXQ_eq, coinsCV_VSQ]
    unfold consumedH2
    rw [hcells]
  have hwn : ∀ w ∈ walkRows (demandH2 rows).cells (demandH2 rows).preads, w.label.node ∈ (demandH2 rows).cells := by
    rw [hcells, hpreads]; exact H.walkRows_node_mem hslot
  have hlink := export_total_link2_inv (F := F) rows hsem hpk (by rw [hcells]; exact hlen) hwn
    (rhoHQ δF χ) (gamHQ δF χ)
  rw [hX, hY, hlink, hcells, ← sum_range_getD H.d.cells (.atom 0), ← H.hC0]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  simp only [CellTraceH.mN, CellTraceHQ.dN, dif_pos hj', mhvH]
  rw [cell_dRowQ_eq_recDen H bs χ _ _ ⟨j, hj'⟩]
  simp [liftQ]

end TermQ

/-! ## The honest VSQ messages of a run and their acceptance -/

section MsgQ
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ} (H : HonestVCLW (K := K) δF hT hP hC kr) (t : NTree (GenComputeRow Kg))

def rhoVSQ (χ : Coins frameVSQ K) : Fin 5 → Quad (algebraMap F K δF) :=
  ![vTotB H (claimBinds H.V.claim) (toVCL (toVS χ)),
    H.xTot (toVCL (toVS χ)) - H.yTot (toVCL (toVS χ)), H.pTot (toVCL (toVS χ)),
    HonestCompQ.accSumXQ δF H.V.basis H.d.cells (wRows (fW t)) (chalVHQ H.V.basis χ) (fW t).length,
    HonestCompQ.accSumPQ δF H.V.basis H.d.cells (wRows (fW t)) (chalVHQ H.V.basis χ) (fW t).length]

/-- The honest `𝕂′` compute trace. -/
def qcVSQ (x : ClaimMsgVS) (χ : Coins frameVSQ K) : Fin (tableVSQ hC).width → F[X] :=
  HonestCompQ.compPolyQ δF H.V.basis H.d.cells (wRows (fW t)) (fW t).length (chalVHQ H.V.basis χ)
    (pubVHQ δF H.V.basis H.V.claim x (rhoVSQ H t χ) χ)
    (wkLn ((toVS χ) cAlphaW)) (wkCnt (fW t) ((toVS χ) cAlphaW))
    (wkAcc (F := F) (fW t) ((toVS χ) cAlphaW) ((toVS χ) cGamW) H.d.cells) H.V.computeNodes (tableVSQ hC).width

/-- The honest `𝕂′` cell twin trace. -/
def qCellVSQ (χ : Coins frameVSQ K) :=
  CellTraceHQ.cellTraceHQ δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP))
    (chalsVSQ δF χ) (pubsCHQ δF (rhoVSQ H t χ) (H.yTot (toVCL (toVS χ))) (yHVSQ H χ))
    (cellColB H (claimBinds H.V.claim) (toVCL (toVS χ))) (mhvH H (bfsRows (airReorder t)))

/-- The honest `𝕂′` walk twin trace. -/
def qWalkVSQ (χ : Coins frameVSQ K) :=
  WalkTraceHQ.walkTraceHQ δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP))
    (chalsVSQ δF χ) (pubsWHQ δF (rhoVSQ H t χ) (H.yTot (toVCL (toVS χ))) (yHVSQ H χ)) (walkColVS H (toVS χ))
    (kLvH H) (vLvH H) (kRvH H) (vRvH H)

theorem width_VSQ_cell (tt : Fin (shapeVSQ hT hP).k) (h : (tt : ℕ) = 0) :
    ((shapeVSQ hT hP).table tt).width = (cellTemplateHQ δF).width 3 := by
  rw [CellTraceHQ.cellTemplateHQ_width]
  change (if (tt : ℕ) = 0 then (⟨238, colRoundCHQ, hT⟩ : TableSpec) else ⟨166, colRoundWHQ, hP⟩).width = 238
  rw [if_pos h]

theorem width_VSQ_walk (tt : Fin (shapeVSQ hT hP).k) (h : ¬ (tt : ℕ) = 0) :
    ((shapeVSQ hT hP).table tt).width = (walkTemplateHQ δF kr).width 3 := by
  rw [WalkTraceHQ.walkTemplateHQ_width]
  change (if (tt : ℕ) = 0 then (⟨238, colRoundCHQ, hT⟩ : TableSpec) else ⟨166, colRoundWHQ, hP⟩).width = 166
  rw [if_neg h]

/-- **The honest VSQ messages of a run** (claim message `x`). -/
def msgVSQ {sumC : VerifierData F K hC (shapeVSQ hT hP) → ClaimMsgVS → SummandsVSQ (F := F) (K := K) hT hP hC}
    {sumM : VerifierData F K hC (shapeVSQ hT hP) → Unit → SummandsVSQ (F := F) (K := K) hT hP hC}
    (x : ClaimMsgVS) : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM) where
  Qc := qcVSQ H t x
  Qm := fun χ tt j =>
    if h : (tt : ℕ) = 0 then qCellVSQ H t χ (Fin.cast (width_VSQ_cell (δF := δF) tt h) j)
    else qWalkVSQ H t χ (Fin.cast (width_VSQ_walk (δF := δF) (kr := kr) tt h) j)
  msg0C := x
  msg0M := ()
  requests := rhoVSQ H t
  msg2M := fun χ => (H.yTot (toVCL (toVS χ)), yHVSQ H χ)

/-- **`honest_accepted_VSQ_run`: the honest VSQ run is accepted at `frameVSQ` outside the honest bad events.**
Hypotheses as `honest_accepted_VS_run`, with the bad events at `frameVSQ` (`HonestBadFreeVSQ`, the `𝕂′`
compute `NotBadRow`, the walk coin order). -/
theorem honest_accepted_VSQ_run
    {sumC : VerifierData F K hC (shapeVSQ hT hP) → ClaimMsgVS → SummandsVSQ (F := F) (K := K) hT hP hC}
    {sumM : VerifierData F K hC (shapeVSQ hT hP) → Unit → SummandsVSQ (F := F) (K := K) hT hP hC}
    {fuel : ℕ} {subject formula : Noun} {result : Noun}
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (hd : H.d = demandH2 (bfsRows (airReorder t)))
    (x : ClaimMsgVS) (hm : HonestClaimMsgFull H.d.cells H.V.claim x)
    (hN : (vsqOf H.V).N = (bfsForest [airReorder t]).length)
    (hinj : Function.Injective (vsOf H.V).computeNodes) (hadj : (vsOf H.V).AdjacentC)
    (hroot : (rowAtW (bfsForest [airReorder t]) 1).s = H.V.claim.subject ∧
      (rowAtW (bfsForest [airReorder t]) 1).f = H.V.claim.formula ∧
      (rowAtW (bfsForest [airReorder t]) 1).e = H.V.claim.result)
    (hbs : ∀ b ∈ (claimBinds H.V.claim).flatMap selfCell, b ∈ H.d.cells)
    (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome) (hreads : H.d.reads = [])
    (hat : ∀ g ∈ bfsRows (airReorder t),
      AtomsLt (ringChar F) (rowOfSkelH g.skel).sf1 ∧ AtomsLt (ringChar F) (rowOfSkelH g.skel).sf2)
    (χ : Coins frameVSQ K)
    (hbf : HonestBadFreeVSQ H (claimBinds H.V.claim) χ (rhoVSQ H t χ) (H.yTot (toVCL (toVS χ))) (yHVSQ H χ)
      (mhvH H (bfsRows (airReorder t))) (kLvH H) (vLvH H) (kRvH H) (vRvH H))
    (hnb : ∀ r < (vsqOf H.V).N, NotBadRow (HonestCompQ.eCQ δF H.V.basis (chalVHQ H.V.basis χ))
      (baseEnvC H.d.cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length
        (chalVHQ H.V.basis χ) (pubVHQ δF H.V.basis H.V.claim x (rhoVSQ H t χ) χ) r))
    (hord : (bfsForest [airReorder t]).length ≤ orderOf ((toVS χ) cAlphaW)) :
    AcceptsG (vsqOf H.V) (msgVSQ (sumC := sumC) (sumM := sumM) H t x) χ := by
  have hsem := run_rows_sem hrun
  have hpk := run_rows_pks hrun
  have hρ3 : rhoVSQ H t χ 3 = HonestCompQ.accSumXQ δF H.V.basis H.d.cells (wRows (bfsForest [airReorder t]))
      (chalVHQ H.V.basis χ) (bfsForest [airReorder t]).length := rfl
  have hρ4 : rhoVSQ H t χ 4 = HonestCompQ.accSumPQ δF H.V.basis H.d.cells (wRows (bfsForest [airReorder t]))
      (chalVHQ H.V.basis χ) (bfsForest [airReorder t]).length := rfl
  refine honest_accepted_VSQ H (msgVSQ H t x) χ (rhoVSQ H t χ) (H.yTot (toVCL (toVS χ))) (yHVSQ H χ)
    (mhvH H (bfsRows (airReorder t))) (kLvH H) (vLvH H) (kRvH H) (vRvH H) rfl rfl
    (fun j => ?_) (fun j => ?_) hbf rfl ?_ rfl rfl (kLvH_bool H) (kRvH_bool H)
    (hpubCQ_honest H χ _ _ _ hd hsem hpk (cells_len_lt H) hslot hρ3)
    (hpubXQ_honest H χ _ _)
    (hpubPQ_honest H χ _ _ _ hd hsem hρ4)
    hslot hreads hadj hinj hbs hm hrun hN hroot hord (by rw [hN]; exact hρ3) (by rw [hN]; exact hρ4) hat hnb rfl
  · simp only [msgVSQ]; exact dif_pos rfl
  · simp only [msgVSQ]; exact dif_neg Nat.one_ne_zero
  · show H.xTot (toVCL (toVS χ)) - H.yTot (toVCL (toVS χ)) + H.yTot (toVCL (toVS χ)) = H.xTot (toVCL (toVS χ))
    exact sub_add_cancel _ _

end MsgQ

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
